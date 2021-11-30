open Gillian.Gil_syntax
open Vec

module TreeBlock = struct
  type t = { ty : Rust_types.t; content : tree_content }

  and tree_content =
    | Scalar of Literal.t
    | Fields of t vec
    | Enum   of int * t vec
    | Uninit

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Rust_types.pp ty

  and pp_content fmt = function
    | Scalar s             -> Literal.pp fmt s
    | Fields v             -> (Fmt.parens (Vec.pp ~sep:Fmt.comma pp)) fmt v
    | Enum (discr, fields) ->
        Fmt.pf fmt "%d%a" discr (Fmt.parens (Vec.pp ~sep:Fmt.comma pp)) fields
    | Uninit               -> Fmt.string fmt "UNINIT"

  let rec to_rust_value { content; _ } =
    match content with
    | Scalar s             -> s
    | Fields v             ->
        let tuple = Vec.map to_rust_value v |> Vec.to_list in
        LList tuple
    | Enum (discr, fields) ->
        let fields = Vec.map to_rust_value fields |> Vec.to_list in
        LList [ Int discr; LList fields ]
    | Uninit               -> Fmt.failwith "Cannot serialize Uninit value"

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
    | Enum v_tys, LList [ Int discr; LList fields ] ->
        let _, tys = List.nth v_tys discr in
        let fields =
          List.map2 (fun t v -> of_rust_value ~genv ~ty:t v) tys fields
          |> Vec.of_list
        in
        let content = Enum (discr, fields) in
        { ty; content }
    | _ ->
        Fmt.failwith "Type error: %a is not of type %a" Literal.pp v
          Rust_types.pp ty

  let rec uninitialized ~genv ty =
    match ty with
    | Rust_types.Scalar _ -> { ty; content = Uninit }
    | Tuple v             ->
        let tuple = List.map (uninitialized ~genv) v |> Vec.of_list in
        { ty; content = Fields tuple }
    | Named a             ->
        let uninit_a = uninitialized ~genv (C_global_env.get_type genv a) in
        { uninit_a with ty }
    | Struct fields       ->
        let tuple =
          List.map (fun (_, t) -> uninitialized ~genv t) fields |> Vec.of_list
        in
        { ty; content = Fields tuple }
    | Enum _              -> { ty; content = Uninit }

  let rec find_proj ~update ~return t proj =
    match (proj, t) with
    | [], block ->
        let new_block = update block in
        let ret_value = return block in
        (ret_value, new_block)
    | Projections.Field p :: r, { content; ty = ty' } -> (
        match content with
        | Scalar s   ->
            Fmt.failwith "Invalid projection on scalar: %d on %a" p Literal.pp s
        | Fields vec -> (
            match vec.%[p] with
            | Ok e    ->
                let v, sub_block = find_proj ~update ~return e r in
                let new_block = Result.get_ok (vec.%[p] <- sub_block) in
                (v, { ty = ty'; content = Fields new_block })
            | Error _ -> Fmt.failwith "Projection out of bound")
        | Enum _     -> Fmt.failwith "Can't handle proj on enum yet"
        | Uninit     -> Fmt.failwith "Uninit use")

  let get_proj ~genv t proj ty copy =
    let update block =
      if C_global_env.type_equal ~genv ty block.ty then
        if copy then block else uninitialized ~genv ty
      else
        Fmt.failwith "Invalid type: %a and %a" Rust_types.pp ty Rust_types.pp
          block.ty
    in
    let return = to_rust_value in
    find_proj ~update ~return t proj

  let set_proj ~genv t proj ty value =
    let return _ = () in
    let update block =
      if C_global_env.type_equal ~genv ty block.ty then
        of_rust_value ~genv ~ty value
      else
        Fmt.failwith "Invalid type: %a and %a " Rust_types.pp ty Rust_types.pp
          block.ty
    in
    let _, new_block = find_proj ~return ~update t proj in
    new_block

  let get_discr t proj =
    let return { content; _ } =
      match content with
      | Enum (discr, _) -> discr
      | _               -> Fmt.failwith "Cannot get the discriminant of %a"
                             pp_content content
    in
    let update block = block in
    let discr, _ = find_proj ~return ~update t proj in
    discr

  let set_discr ~genv t proj discr =
    let rec resolve_variant_fields ty =
      match ty with
      | Rust_types.Enum variants -> snd (List.nth variants discr)
      | Named e                  -> resolve_variant_fields
                                    @@ C_global_env.get_type genv e
      | _                        -> Fmt.failwith
                                      "Invalid type for set_discr: %a"
                                      Rust_types.pp ty
    in
    let update { content; ty } =
      match content with
      | Enum (_, _) | Uninit ->
          let fields_tys = resolve_variant_fields ty in
          let uninit_fields = List.map (uninitialized ~genv) fields_tys in
          let content = Enum (discr, Vec.of_list uninit_fields) in
          { ty; content }
      | _                    -> Fmt.failwith "Invalid content for set_discr: %a"
                                  pp_content content
    in
    let return _ = () in
    let (), new_block = find_proj ~update ~return t proj in
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
