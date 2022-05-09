open Gillian.Gil_syntax
open Vec

module TreeBlock = struct
  type t = { ty : Rust_types.t; content : tree_content }

  and tree_content =
    | Scalar of Literal.t
    | Fields of t vec
    | Array  of t vec
    | Enum   of { discr : int option; downcast_and_fields : (int * t vec) option }
    | Ptr    of string * Projections.t
    | Uninit

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Rust_types.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Scalar s -> Literal.pp ft s
    | Fields v -> (parens (Vec.pp ~sep:Fmt.comma pp)) ft v
    | Enum { discr; downcast_and_fields } ->
        pf ft "%a[%a]"
          (option ~none:(any "U") int)
          discr
          (option ~none:(any "U")
          @@ pair ~sep:nop int (parens @@ Vec.pp ~sep:comma pp))
          downcast_and_fields
    | Ptr (loc, proj) -> pf ft "Ptr(%s, %a)" loc Projections.pp proj
    | Array v -> (brackets (Vec.pp ~sep:comma pp)) ft v
    | Uninit -> Fmt.string ft "UNINIT"

  let rec to_rust_value ~genv { content; ty } =
    match content with
    | Scalar s -> s
    | Fields v | Array v ->
        let tuple = Vec.map (to_rust_value ~genv) v |> Vec.to_list in
        LList tuple
    | Enum { discr = Some discr; downcast_and_fields = Some (dcast, fields) }
      when discr == dcast ->
        let fields = Vec.map (to_rust_value ~genv) fields |> Vec.to_list in
        LList
          [ Int (Z.of_int discr); LList [ Int (Z.of_int dcast); LList fields ] ]
    | Enum { discr = Some discr; downcast_and_fields = None }
      when Rust_types.no_fields_for_downcast
             (C_global_env.resolve_named ~genv ty)
             discr ->
        LList [ Int (Z.of_int discr) ]
    | Enum _ -> Fmt.failwith "Cannot serialize inconsistent enum"
    | Ptr (loc, proj) -> LList [ Loc loc; LList (Projections.to_lit_list proj) ]
    | Uninit ->
        Fmt.failwith "Cannot serialize Uninit or partially uninit values"

  let rec of_rust_value ~genv ~ty v =
    match (ty, v) with
    | Rust_types.Scalar (Uint _ | Int _), Literal.Int _ ->
        { ty; content = Scalar v }
    | Scalar Bool, Bool _ -> { ty; content = Scalar v }
    | Tuple ts, LList tup ->
        let content =
          List.map2 (fun t v -> of_rust_value ~genv ~ty:t v) ts tup
        in
        let content = Fields (Vec.of_list content) in
        { ty; content }
    | Struct fs, LList tup ->
        let content =
          List.map2 (fun (_, t) v -> of_rust_value ~genv ~ty:t v) fs tup
        in
        let content = Fields (Vec.of_list content) in
        { ty; content }
    | Named a, v ->
        let ty = C_global_env.get_type genv a in
        of_rust_value ~genv ~ty v
    | Enum v_tys, LList [ Int discr; LList [ Int downcast; LList fields ] ] ->
        let _, tys = List.nth v_tys (Z.to_int discr) in
        let fields =
          List.map2 (fun t v -> of_rust_value ~genv ~ty:t v) tys fields
          |> Vec.of_list
        in
        let content =
          Enum
            {
              discr = Some (Z.to_int discr);
              downcast_and_fields = Some (Z.to_int downcast, fields);
            }
        in
        { ty; content }
    | Enum _, LList [ Int discr ] ->
        let content =
          Enum { discr = Some (Z.to_int discr); downcast_and_fields = None }
        in
        { ty; content }
    | Ref _, LList [ Loc loc; LList proj ] ->
        let content = Ptr (loc, Projections.of_lit_list proj) in
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

  let rec find_proj ~genv ~update ~return t proj =
    let rec_call = find_proj ~genv ~update ~return in
    match (proj, t) with
    | [], block ->
        let new_block = update block in
        let ret_value = return block in
        (ret_value, new_block)
    | Projections.Field p :: r, { content; ty = ty' } -> (
        match content with
        | Scalar s ->
            Fmt.failwith "Invalid projection on scalar: %d on %a" p Literal.pp s
        | Ptr _ ->
            Fmt.failwith "Invalid projection on pointer: %d on %a" p pp_content
              content
        | Array _ -> Fmt.failwith "Invalid projection on array: field"
        | Fields vec -> (
            match vec.%[p] with
            | Ok e    ->
                let v, sub_block = rec_call e r in
                let new_block = Result.get_ok (vec.%[p] <- sub_block) in
                (v, { ty = ty'; content = Fields new_block })
            | Error _ -> Fmt.failwith "Projection out of bound")
        | Enum { discr; downcast_and_fields = Some (d, fields) } -> (
            match fields.%[p] with
            | Ok e    ->
                let v, sub_block = rec_call e r in
                let new_fields = Result.get_ok (fields.%[p] <- sub_block) in
                ( v,
                  {
                    ty = ty';
                    content =
                      Enum { discr; downcast_and_fields = Some (d, new_fields) };
                  } )
            | Error _ -> Fmt.failwith "Projection out of enum bound")
        | Enum { downcast_and_fields = None; _ } ->
            Fmt.failwith "Cannot get field of uninit Enum"
        | Uninit -> Fmt.failwith "Uninit use")
    | Downcast p :: r, { ty; content } -> (
        match C_global_env.resolve_named ~genv ty with
        | Rust_types.Enum pats -> (
            match content with
            | Uninit ->
                let downcast_fields =
                  snd (List.nth pats p)
                  |> List.map (uninitialized ~genv)
                  |> Vec.of_list
                in
                let new_content =
                  Enum
                    {
                      discr = None;
                      downcast_and_fields = Some (p, downcast_fields);
                    }
                in
                rec_call { ty; content = new_content } r
            | Enum _ -> rec_call { ty; content } r
            | _      -> Fmt.failwith "Incorrect variant")
        | _                    -> Fmt.failwith "Cannot downcast on %a"
                                    Rust_types.pp ty)

  let get_proj ~genv t proj ty copy =
    let update block =
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
      | Enum { discr = Some discr; _ } -> discr
      | _ -> Fmt.failwith "Cannot get the discriminant of %a" pp_content content
    in
    let update block = block in
    let discr, _ = find_proj ~genv ~return ~update t proj in
    discr

  let set_discr ~genv t proj discr =
    let update { content; ty } =
      match content with
      | Uninit ->
          {
            ty;
            content = Enum { discr = Some discr; downcast_and_fields = None };
          }
      | Enum { downcast_and_fields; _ } ->
          let content = Enum { discr = Some discr; downcast_and_fields } in
          { ty; content }
      | _ -> Fmt.failwith "Invalid content for set_discr: %a" pp_content content
    in
    let return _ = () in
    let (), new_block = find_proj ~genv ~update ~return t proj in
    new_block
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

let store_discr ~genv (mem : t) loc proj discr =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.set_discr ~genv block proj discr in
  Hashtbl.replace mem loc new_block;
  mem

let empty () : t = Hashtbl.create 1
let copy x = Hashtbl.copy x
let pp : t Fmt.t = Fmt.Dump.hashtbl Fmt.string TreeBlock.pp
