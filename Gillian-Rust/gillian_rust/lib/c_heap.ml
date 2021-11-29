open Gillian.Gil_syntax
open Vec

module TreeBlock = struct
  type t = { ty : Rust_types.t; content : tree_content }

  and tree_content = Scalar of Literal.t | Fields of t vec | Uninit

  let rec to_rust_value { content; _ } =
    match content with
    | Scalar s -> s
    | Fields v ->
        let tuple = Vec.map to_rust_value v |> Vec.to_list in
        LList tuple
    | Uninit   -> Fmt.failwith "Cannot serialize Uninit value"

  let rec of_rust_value ~ty v =
    match (ty, v) with
    | Rust_types.Scalar (Uint _ | Int _), Literal.Int _ ->
        { ty; content = Scalar v }
    | Scalar Bool, Bool _ -> { ty; content = Scalar v }
    | Tuple ts, LList tup ->
        let content = List.map2 (fun t v -> of_rust_value ~ty:t v) ts tup in
        let content = Fields (Vec.of_list content) in
        { ty; content }
    | _ ->
        Fmt.failwith "Type error : %a is not of type %a" Literal.pp v
          Rust_types.pp ty

  let rec uninitialized ty =
    match ty with
    | Rust_types.Scalar _ -> { ty; content = Uninit }
    | Tuple v             ->
        let tuple = List.map uninitialized v |> Vec.of_list in
        { ty; content = Fields tuple }

  let rec get_proj t proj ty copy =
    match (proj, t) with
    | [], { ty = ty'; _ } ->
        if ty = ty' then
          let new_block = if copy then t else uninitialized ty in
          (to_rust_value t, new_block)
        else
          Fmt.failwith "Invalid type: %a and %a" Rust_types.pp ty Rust_types.pp
            ty'
    | Projections.Field p :: r, { content; ty = ty' } -> (
        match content with
        | Scalar s   ->
            Fmt.failwith "Invalid projection on scalar: %d on %a" p Literal.pp s
        | Fields vec -> (
            match vec.%[p] with
            | Ok e    ->
                let v, sub_block = get_proj e r ty copy in
                let new_block = Result.get_ok (vec.%[p] <- sub_block) in
                (v, { ty = ty'; content = Fields new_block })
            | Error _ -> Fmt.failwith "Projection out of bound")
        | Uninit     -> Fmt.failwith "Uninit use")

  let rec set_proj t proj ty value =
    match (proj, t) with
    | [], { ty = ty'; _ } ->
        if ty = ty' then of_rust_value ~ty value
        else
          Fmt.failwith "Invalid type: %a and %a" Rust_types.pp ty Rust_types.pp
            ty'
    | Projections.Field p :: r, { content; ty = ty' } -> (
        match content with
        | Scalar s ->
            Fmt.failwith "Invalid projection on scalar: %d on %a" p Literal.pp s
        | Fields vec -> (
            match vec.%[p] with
            | Ok e    ->
                let on_proj = set_proj e r ty value in
                let new_vec = Result.get_ok (vec.%[p] <- on_proj) in
                { ty = ty'; content = Fields new_vec }
            | Error _ -> Fmt.failwith "Projection out of bound")
        (* Well that one is plain wrong, we can actually assign, if the type is right *)
        | Uninit -> Fmt.failwith "Uninit use")

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Rust_types.pp ty

  and pp_content fmt = function
    | Scalar s -> Literal.pp fmt s
    | Fields v -> (Fmt.parens (Vec.pp ~sep:Fmt.comma pp)) fmt v
    | Uninit   -> Fmt.string fmt "UNINIT"
end

type t = (string, TreeBlock.t) Hashtbl.t

let alloc mem ty =
  let loc = Gillian.Utils.Generators.fresh_loc () in
  let new_block = TreeBlock.uninitialized ty in
  Hashtbl.replace mem loc new_block;
  (loc, mem)

let load (mem : t) loc proj ty copy =
  let block = Hashtbl.find mem loc in
  let v, new_block = TreeBlock.get_proj block proj ty copy in
  Hashtbl.replace mem loc new_block;
  (v, mem)

let store (mem : t) loc proj ty value =
  let block = Hashtbl.find mem loc in
  let new_block = TreeBlock.set_proj block proj ty value in
  Hashtbl.replace mem loc new_block;
  mem

let empty () : t = Hashtbl.create 1

let pp : t Fmt.t = Fmt.Dump.hashtbl Fmt.string TreeBlock.pp
