open Gillian.Gil_syntax
open Array_utils.Infix

exception MemoryError of string

let mem_error p = Fmt.kstr (fun s -> raise (MemoryError s)) p

module TreeBlock = struct
  type t = { ty : Ty.t; content : tree_content }

  and tree_content =
    | Scalar of Literal.t
    | Fields of t array
    | Array of t array
    | Enum of { discr : int; fields : t array }
    | ThinPtr of string * Projections.t
    | FatPtr of string * Projections.t * int
    | Uninit

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Ty.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Scalar s -> Literal.pp ft s
    | Fields v -> (parens (Fmt.array ~sep:Fmt.comma pp)) ft v
    | Enum { discr; fields } ->
        pf ft "%a[%a]" int discr (Fmt.array ~sep:comma pp) fields
    | ThinPtr (loc, proj) -> pf ft "Ptr(%s, %a)" loc Projections.pp proj
    | FatPtr (loc, proj, meta) ->
        pf ft "FatPtr(%s, %a | %d)" loc Projections.pp proj meta
    | Array v -> (brackets (Fmt.array ~sep:comma pp)) ft v
    | Uninit -> Fmt.string ft "UNINIT"

  let rec to_rust_value ~tyenv ({ content; ty } as t) =
    match content with
    | Scalar s -> (
        match (ty, s) with
        | Scalar (Uint _ | Int _ | Char), _ -> s
        | Scalar Bool, Bool b -> if b then Int Z.one else Int Z.zero
        | _ -> Fmt.failwith "Malformed tree: %a" pp t)
    | Fields v | Array v ->
        let tuple = Array.map (to_rust_value ~tyenv) v |> Array.to_list in
        if Tyenv.is_struct ~tyenv ty then
          LList [ String (Ty.name_exn ty); LList tuple ]
        else LList tuple
    | Enum { discr; fields } ->
        let fields = Array.map (to_rust_value ~tyenv) fields |> Array.to_list in
        let data = Literal.LList [ Int (Z.of_int discr); LList fields ] in
        LList [ String (Ty.name_exn ty); data ]
    | ThinPtr (loc, proj) ->
        LList [ Loc loc; LList (Projections.to_lit_list proj) ]
    | FatPtr (loc, proj, meta) ->
        LList
          [
            LList [ Loc loc; LList (Projections.to_lit_list proj) ];
            Int (Z.of_int meta);
          ]
    | Uninit -> mem_error "Attempting to read uninitialized value"

  let rec of_rust_struct_value ~tyenv ~ty ~fields_tys fields =
    let content =
      List.map2 (fun (_, t) v -> of_rust_value ~tyenv ~ty:t v) fields_tys fields
    in
    let content = Fields (Array.of_list content) in
    { ty; content }

  and of_rust_enum_value ~tyenv ~ty ~variants_tys data =
    match data with
    | [ Literal.Int variant_idx; LList fields ] ->
        let vidx = Z.to_int variant_idx in
        let _, tys = List.nth variants_tys vidx in
        let fields =
          List.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) tys fields
          |> Array.of_list
        in
        let content = Enum { discr = vidx; fields } in
        { ty; content }
    | _ -> failwith "Invalid enum value!"

  and of_rust_value ~tyenv ~ty v =
    match (ty, v) with
    | Ty.Scalar (Uint _ | Int _), Literal.Int _ -> { ty; content = Scalar v }
    | Ty.Scalar Bool, Literal.Int i ->
        if Z.equal i Z.one then { ty; content = Scalar (Bool true) }
        else if Z.equal i Z.zero then { ty; content = Scalar (Bool false) }
        else Fmt.failwith "Invalid boolean: %a" Z.pp_print i
    | Scalar Bool, Bool _ -> { ty; content = Scalar v }
    | Tuple ts, LList tup ->
        let content =
          List.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) ts tup
        in
        let content = Fields (Array.of_list content) in
        { ty; content }
    | Adt name, LList [ String x; LList data ] when String.equal name x -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields_tys) ->
            of_rust_struct_value ~tyenv ~ty ~fields_tys data
        | Enum variants_tys -> of_rust_enum_value ~tyenv ~ty ~variants_tys data)
    | Ref { ty = Slice _; _ }, LList [ LList [ Loc loc; LList proj ]; Int i ] ->
        let content = FatPtr (loc, Projections.of_lit_list proj, Z.to_int i) in
        { ty; content }
    | Ref _, LList [ Loc loc; LList proj ] ->
        let content = ThinPtr (loc, Projections.of_lit_list proj) in
        { ty; content }
    | Array { length; ty = ty' }, LList l
      when List.compare_length_with l length == 0 ->
        let mem_array =
          List.map (of_rust_value ~tyenv ~ty:ty') l |> Array.of_list
        in
        { ty; content = Array mem_array }
    | _ -> Fmt.failwith "Type error: %a is not of type %a" Literal.pp v Ty.pp ty

  let rec uninitialized ~tyenv ty =
    match ty with
    | Ty.Tuple v ->
        let tuple = List.map (uninitialized ~tyenv) v |> Array.of_list in
        { ty; content = Fields tuple }
    | Adt name -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            let tuple =
              List.map (fun (_, t) -> uninitialized ~tyenv t) fields
              |> Array.of_list
            in
            { ty; content = Fields tuple }
        | Enum _ -> { ty; content = Uninit })
    | Array { length; ty = ty' } ->
        let uninit_field _ = uninitialized ~tyenv ty' in
        let content = Array.init length uninit_field in
        { ty; content = Array content }
    | Scalar _ | Ref _ -> { ty; content = Uninit }
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"

  let rec find_path ~tyenv ~update ~return t (path : Partial_layout.access list)
      =
    let rec_call = find_path ~tyenv ~update ~return in
    let replace_vec c v =
      match c with
      | Fields _ -> Fields v
      | Array _ -> Array v
      | Enum { discr; _ } -> Enum { discr; fields = v }
      | _ -> failwith "impossible"
    in
    match (path, t) with
    | [], block ->
        let new_block = update block in
        let ret_value = return block in
        (ret_value, new_block)
    | { index; index_type = _; against; variant } :: r, { ty; content }
      when Ty.equal against ty -> (
        match (content, variant) with
        | (Fields vec | Array vec), None ->
            let e = Result.ok_or vec.%[index] "Index out of bounds" in
            let v, sub_block = rec_call e r in
            let new_block = Result.get_ok (vec.%[index] <- sub_block) in
            (v, { ty; content = replace_vec content new_block })
        | Enum { fields = vec; discr }, Some discr' when discr = discr' ->
            let e = Result.ok_or vec.%[index] "Index out of bounds" in
            let v, sub_block = rec_call e r in
            let new_block = Result.get_ok (vec.%[index] <- sub_block) in
            (v, { ty; content = replace_vec content new_block })
        | _ -> failwith "Invalid node")
    | _ -> failwith "Type mismatch"

  let get_forest ~tyenv t proj size ty copy =
    let open Partial_layout in
    let start_address =
      { block_type = t.ty; route = proj; address_type = Ty.slice_elements ty }
    in
    let context = context_from_env tyenv in
    let start_accesses = resolve_address ~tyenv ~context start_address in
    let start, array_accesses =
      match start_accesses with
      | { index; _ } :: r -> (index, List.rev r)
      | _ -> failwith "wrong slice pointer"
    in
    let update block =
      if copy then block
      else
        match block.content with
        | Array vec ->
            {
              content =
                Array
                  (Result.ok_or
                     (Array_utils.override_range vec ~start ~size (fun _ ->
                          uninitialized ~tyenv ty))
                     "Invalid slice range");
              ty;
            }
        | _ -> failwith "Not an array"
    in
    let return block =
      match block.content with
      | Array vec ->
          Array_utils.sublist_map ~start ~size ~f:(to_rust_value ~tyenv) vec
      | _ -> failwith "Not an array"
    in
    find_path ~tyenv ~update ~return t array_accesses

  let set_forest ~tyenv t proj size ty values =
    assert (List.length values = size);
    let open Partial_layout in
    let start_address =
      { block_type = t.ty; route = proj; address_type = Ty.slice_elements ty }
    in
    let context = context_from_env tyenv in
    let start_accesses = resolve_address ~tyenv ~context start_address in
    let start, array_accesses =
      match start_accesses with
      | { index; _ } :: r -> (index, List.rev r)
      | _ -> failwith "wrong slice pointer"
    in
    let return _ = () in
    let update block =
      match (block.content, block.ty) with
      | Array vec, Ty.Array { ty = ty'; _ } ->
          assert (Ty.equal ty ty');
          {
            content =
              Array
                (Result.ok_or
                   (Array_utils.override_range_with_list vec ~start
                      ~f:(of_rust_value ~tyenv ~ty) values)
                   "Invalid slice range");
            ty;
          }
      | _ -> failwith "Not an array"
    in
    let _, new_block = find_path ~tyenv ~return ~update t array_accesses in
    new_block

  let find_proj ~tyenv ~update ~return ~ty t proj =
    let open Partial_layout in
    let address = { block_type = t.ty; route = proj; address_type = ty } in
    let context = context_from_env tyenv in
    Logging.normal (fun m ->
        m "Finding address: %a" (Fmt.Dump.list Projections.pp_elem) proj);
    Logging.normal (fun m ->
        m "PL for %a: %a" Ty.pp t.ty pp_partial_layout
          (context.partial_layouts t.ty));
    let accesses = resolve_address ~tyenv ~context address |> List.rev in
    Logging.normal (fun m ->
        m "Accessess: %a" (Fmt.Dump.list pp_access) accesses);
    find_path ~tyenv ~update ~return t accesses

  let get_proj ~tyenv t proj ty copy =
    let update block = if copy then block else uninitialized ~tyenv ty in
    let return = to_rust_value ~tyenv in
    find_proj ~tyenv ~update ~return ~ty t proj

  let set_proj ~tyenv t proj ty value =
    let return _ = () in
    let update _block = of_rust_value ~tyenv ~ty value in
    let _, new_block = find_proj ~tyenv ~ty ~return ~update t proj in
    new_block

  let get_discr ~tyenv t proj enum_typ =
    let return { content; _ } =
      match content with
      | Enum t -> t.discr
      | _ -> Fmt.failwith "Cannot get the discriminant of %a" pp_content content
    in
    let update block = block in
    let discr, _ = find_proj ~tyenv ~return ~update ~ty:enum_typ t proj in
    discr

  let deinit ~tyenv t proj ty =
    let return _ = () in
    let update _block = uninitialized ~tyenv ty in
    let _, new_block = find_proj ~tyenv ~ty ~return ~update t proj in
    new_block
end

type t = (string, TreeBlock.t) Hashtbl.t

let alloc ~tyenv (heap : t) ty =
  let loc = Gillian.Utils.Generators.fresh_loc () in
  let new_block = TreeBlock.uninitialized ~tyenv ty in
  Hashtbl.replace heap loc new_block;
  (loc, heap)

let load ~tyenv (mem : t) loc proj ty copy =
  let block = Hashtbl.find mem loc in
  let v, new_block = TreeBlock.get_proj ~tyenv block proj ty copy in
  Hashtbl.replace mem loc new_block;
  (v, mem)

let load_slice ~tyenv (mem : t) loc proj size ty copy =
  let block = Hashtbl.find mem loc in
  let vs, new_block = TreeBlock.get_forest ~tyenv block proj size ty copy in
  Hashtbl.replace mem loc new_block;
  (vs, mem)

let store_slice ~tyenv (mem : t) loc proj size ty values =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.set_forest ~tyenv block proj size ty values in
  Hashtbl.replace mem loc new_block;
  mem

let store ~tyenv (mem : t) loc proj ty value =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.set_proj ~tyenv block proj ty value in
  Hashtbl.replace mem loc new_block;
  mem

let deinit ~tyenv (mem : t) loc proj ty =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.deinit ~tyenv block proj ty in
  Hashtbl.replace mem loc new_block;
  mem

let free (mem : t) loc ty =
  let block = Hashtbl.find mem loc in
  let () =
    if Ty.equal block.ty ty then Hashtbl.remove mem loc
    else
      Fmt.failwith "Incompatible types for free: %a and %a" Ty.pp block.ty Ty.pp
        ty
  in
  mem

let load_discr (mem : t) loc proj enum_typ =
  let block = Hashtbl.find mem loc in
  let discr = TreeBlock.get_discr block proj enum_typ in
  discr

let empty () : t = Hashtbl.create 1
let copy x = Hashtbl.copy x

let pp : t Fmt.t =
  let open Fmt in
  hashtbl ~sep:(any "@\n") (parens (pair ~sep:(any "-> ") string TreeBlock.pp))
