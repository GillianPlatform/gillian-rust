open Gillian.Gil_syntax
open Vec

module TreeBlock = struct
  type t = { ty : Rust_types.t; content : tree_content }

  and tree_content =
    | Scalar  of Literal.t
    | Fields  of t vec
    | Array   of t vec
    | Enum    of { discr : int; fields : t vec }
    | ThinPtr of string * Projections.t
    | FatPtr  of string * Projections.t * int
    | Uninit

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Rust_types.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Scalar s                 -> Literal.pp ft s
    | Fields v                 -> (parens (Vec.pp ~sep:Fmt.comma pp)) ft v
    | Enum { discr; fields }   ->
        pf ft "%a[%a]" int discr (Vec.pp ~sep:comma pp) fields
    | ThinPtr (loc, proj)      -> pf ft "Ptr(%s, %a)" loc Projections.pp proj
    | FatPtr (loc, proj, meta) ->
        pf ft "FatPtr(%s, %a | %d)" loc Projections.pp proj meta
    | Array v                  -> (brackets (Vec.pp ~sep:comma pp)) ft v
    | Uninit                   -> Fmt.string ft "UNINIT"

  let rec to_rust_value ~genv ({ content; ty } as t) =
    match content with
    | Scalar s                 -> (
        match (ty, s) with
        | Scalar (Uint _ | Int _ | Char), _ -> s
        | Scalar Bool, Bool b -> if b then Int Z.one else Int Z.zero
        | _ -> Fmt.failwith "Malformed tree: %a" pp t)
    | Fields v | Array v       -> (
        let tuple = Vec.map (to_rust_value ~genv) v |> Vec.to_list in
        match C_global_env.resolve_named ~genv ty with
        | Struct _ -> LList [ String (Rust_types.name_exn ty); LList tuple ]
        | _        -> LList tuple)
    | Enum { discr; fields }   ->
        let fields = Vec.map (to_rust_value ~genv) fields |> Vec.to_list in
        let data = Literal.LList [ Int (Z.of_int discr); LList fields ] in
        LList [ String (Rust_types.name_exn ty); data ]
    | ThinPtr (loc, proj)      ->
        LList [ Loc loc; LList (Projections.to_lit_list proj) ]
    | FatPtr (loc, proj, meta) ->
        LList
          [
            LList [ Loc loc; LList (Projections.to_lit_list proj) ];
            Int (Z.of_int meta);
          ]
    | Uninit                   ->
        Fmt.failwith "Cannot serialize Uninit or partially uninit values"

  let rec of_rust_struct_value ~genv ~ty ~fields_tys fields =
    let content =
      List.map2 (fun (_, t) v -> of_rust_value ~genv ~ty:t v) fields_tys fields
    in
    let content = Fields (Vec.of_list content) in
    { ty; content }

  and of_rust_enum_value ~genv ~ty ~variants_tys data =
    match data with
    | [ Literal.Int variant_idx; LList fields ] ->
        let vidx = Z.to_int variant_idx in
        let _, tys = List.nth variants_tys vidx in
        let fields =
          List.map2 (fun t v -> of_rust_value ~genv ~ty:t v) tys fields
          |> Vec.of_list
        in
        let content = Enum { discr = vidx; fields } in
        { ty; content }
    | _ -> failwith "Invalid enum value!"

  and of_rust_value ~genv ~ty v =
    match (ty, v) with
    | Rust_types.Scalar (Uint _ | Int _), Literal.Int _ ->
        { ty; content = Scalar v }
    | Rust_types.Scalar Bool, Literal.Int i ->
        if Z.equal i Z.one then { ty; content = Scalar (Bool true) }
        else if Z.equal i Z.zero then { ty; content = Scalar (Bool false) }
        else Fmt.failwith "Invalid boolean: %a" Z.pp_print i
    | Scalar Bool, Bool _ -> { ty; content = Scalar v }
    | Tuple ts, LList tup ->
        let content =
          List.map2 (fun t v -> of_rust_value ~genv ~ty:t v) ts tup
        in
        let content = Fields (Vec.of_list content) in
        { ty; content }
    | Named a, LList [ String x; LList data ] when String.equal a x -> (
        match C_global_env.resolve_named ~genv ty with
        | Struct fields_tys -> of_rust_struct_value ~genv ~ty ~fields_tys data
        | Enum variants_tys -> of_rust_enum_value ~genv ~ty ~variants_tys data
        | _                 ->
            failwith "Deserializing a Named type that is not a struct or enum")
    | Ref { ty = Slice _; _ }, LList [ LList [ Loc loc; LList proj ]; Int i ] ->
        let content = FatPtr (loc, Projections.of_lit_list proj, Z.to_int i) in
        { ty; content }
    | Ref _, LList [ Loc loc; LList proj ] ->
        let content = ThinPtr (loc, Projections.of_lit_list proj) in
        { ty; content }
    | Array { length; ty = ty' }, LList l
      when List.compare_length_with l length == 0 ->
        let mem_array =
          List.map (of_rust_value ~genv ~ty:ty') l |> Vec.of_list
        in
        { ty; content = Array mem_array }
    | _ ->
        Fmt.failwith "Type error: %a is not of type %a" Literal.pp v
          Rust_types.pp ty

  let rec uninitialized ~genv ty =
    match ty with
    | Rust_types.Tuple v         ->
        let tuple = List.map (uninitialized ~genv) v |> Vec.of_list in
        { ty; content = Fields tuple }
    | Named a                    ->
        let uninit_a = uninitialized ~genv (C_global_env.get_type genv a) in
        { uninit_a with ty }
    | Struct fields              ->
        let tuple =
          List.map (fun (_, t) -> uninitialized ~genv t) fields |> Vec.of_list
        in
        { ty; content = Fields tuple }
    | Array { length; ty = ty' } ->
        let uninit_field _ = uninitialized ~genv ty' in
        let content = Vec.init length uninit_field in
        { ty; content = Array content }
    | Enum _ | Scalar _ | Ref _  -> { ty; content = Uninit }
    | Slice _                    -> Fmt.failwith "Cannot initialize unsized type"

  module Proj_result = struct
    type t = Whole_node of t | Index_on of t vec * int

    let resolve = function
      | Whole_node t    -> t
      | Index_on (t, i) -> Result.get_ok t.%[i]
  end

  let rec find_proj ~genv ~update ~return t proj =
    let rec_call = find_proj ~genv ~update ~return in
    match (proj, t) with
    | [], block ->
        let new_block = update block in
        let ret_value = return block in
        (ret_value, new_block)
    | Projections.Index i :: r, { content = Array vec; ty = ty' } ->
        let e = Result.ok_or vec.%[i] "Index out of bound" in
        let v, sub_block = rec_call e r in
        let new_block = Result.get_ok (vec.%[i] <- sub_block) in
        (v, { ty = ty'; content = Array new_block })
    | Projections.Field p :: r, { content = Fields vec; ty = ty' } ->
        let e = Result.ok_or vec.%[p] "Projection out of bound" in
        let v, sub_block = rec_call e r in
        let new_block = Result.get_ok (vec.%[p] <- sub_block) in
        (v, { ty = ty'; content = Fields new_block })
    | Projections.Field p :: r, { content = Enum { discr; fields }; ty = ty' }
      ->
        let e = Result.ok_or fields.%[p] "Projection out of enum bound" in
        let v, sub_block = rec_call e r in
        let new_fields = Result.get_ok (fields.%[p] <- sub_block) in
        (v, { ty = ty'; content = Enum { discr; fields = new_fields } })
    | Downcast p :: r, { content = Enum { discr; _ }; _ } when discr = p ->
        rec_call t r
    | Cast _ :: r, t -> rec_call t r
    | _ -> Fmt.failwith "Invalid projection %a on %a" Projections.pp proj pp t

  let get_forest ~genv t proj size ty copy =
    let start, proj = Projections.slice_start proj in
    let update block =
      if Rust_types.is_slice_of ty block.ty then
        if copy then block
        else
          match block.content with
          | Array vec ->
              {
                content =
                  Array
                    (Result.ok_or
                       (Vec.override_range vec ~start ~size (fun _ ->
                            uninitialized ~genv ty))
                       "Invalid slice range");
                ty;
              }
          | _         -> failwith "Not an array"
      else failwith "Not a subslice"
    in
    let return block =
      match block.content with
      | Array vec -> sublist_map ~start ~size ~f:(to_rust_value ~genv) vec
      | _         -> failwith "Not an array"
    in
    find_proj ~genv ~update ~return t proj

  let set_forest ~genv t proj size ty values =
    assert (List.length values = size);
    let start, proj = Projections.slice_start proj in
    let return _ = () in
    let update block =
      if Rust_types.is_slice_of ty block.ty then
        match (block.content, block.ty) with
        | Array vec, Rust_types.Array { ty; _ } ->
            {
              content =
                Array
                  (Result.ok_or
                     (Vec.override_range_with_list vec ~start
                        ~f:(of_rust_value ~genv ~ty) values)
                     "Invalid slice range");
              ty;
            }
        | _ -> failwith "Not an array"
      else failwith "Not a subslice"
    in
    let _, new_block = find_proj ~genv ~return ~update t proj in
    new_block

  let get_proj ~genv t proj ty copy =
    let update block =
      (* Subtype seems unnecessary *)
      if C_global_env.subtypes ~genv block.ty ty then
        if copy then block else uninitialized ~genv ty
      else
        Fmt.failwith "[get_proj] Invalid type: expected %a got %a" Rust_types.pp
          block.ty Rust_types.pp ty
    in

    let return = to_rust_value ~genv in
    find_proj ~genv ~update ~return t proj

  let set_proj ~genv t proj ty value =
    let return _ = () in
    let update block =
      if C_global_env.subtypes ~genv ty block.ty then
        of_rust_value ~genv ~ty value
      else
        Fmt.failwith "[set_proj] Invalid type: expected %a got %a "
          Rust_types.pp block.ty Rust_types.pp ty
    in
    let _, new_block = find_proj ~genv ~return ~update t proj in
    new_block

  let get_discr ~genv t proj =
    let return { content; _ } =
      match content with
      | Enum t -> t.discr
      | _      -> Fmt.failwith "Cannot get the discriminant of %a" pp_content
                    content
    in
    let update block = block in
    let discr, _ = find_proj ~genv ~return ~update t proj in
    discr
end

type t = (string, TreeBlock.t) Hashtbl.t

let alloc ~genv (heap : t) ty =
  let loc = Gillian.Utils.Generators.fresh_loc () in
  let new_block = TreeBlock.uninitialized ~genv ty in
  Hashtbl.replace heap loc new_block;
  (loc, heap)

let load ~genv (mem : t) loc proj ty copy =
  let block = Hashtbl.find mem loc in
  let v, new_block = TreeBlock.get_proj ~genv block proj ty copy in
  Hashtbl.replace mem loc new_block;
  (v, mem)

let load_slice ~genv (mem : t) loc proj size ty copy =
  let block = Hashtbl.find mem loc in
  let vs, new_block = TreeBlock.get_forest ~genv block proj size ty copy in
  Hashtbl.replace mem loc new_block;
  (vs, mem)

let store_slice ~genv (mem : t) loc proj size ty values =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.set_forest ~genv block proj size ty values in
  Hashtbl.replace mem loc new_block;
  mem

let store ~genv (mem : t) loc proj ty value =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.set_proj ~genv block proj ty value in
  Hashtbl.replace mem loc new_block;
  mem

let free ~genv (mem : t) loc ty =
  let block = Hashtbl.find mem loc in
  let () =
    if C_global_env.subtypes ~genv block.ty ty then Hashtbl.remove mem loc
    else
      Fmt.failwith "Incompatible types for free: %a and %a" Rust_types.pp
        block.ty Rust_types.pp ty
  in
  mem

let load_discr (mem : t) loc proj =
  let block = Hashtbl.find mem loc in
  let discr = TreeBlock.get_discr block proj in
  discr

let empty () : t = Hashtbl.create 1
let copy x = Hashtbl.copy x

let pp : t Fmt.t =
  let open Fmt in
  hashtbl ~sep:(any "@\n") (parens (pair ~sep:(any "-> ") string TreeBlock.pp))
