open Gillian.Gil_syntax

module BaseValues = struct
  type t = Literal.t * Rust_types.t

  let of_lit_and_ty lit ty = (lit, ty)

  let pp = Fmt.parens (Fmt.pair ~sep:(Fmt.any " :@ ") Literal.pp Rust_types.pp)
end

module TreeBlock = struct
  type t = BaseValue of BaseValues.t | Moved of Rust_types.t

  let get_proj t proj ty copy =
    match (proj, t) with
    | [], BaseValue (bv, ty') when ty = ty' ->
        let new_block = if copy then t else Moved ty in
        (bv, new_block)
    | [], BaseValue (_, ty') ->
        Fmt.failwith "Types are not matching! %a and %a" Rust_types.pp ty
          Rust_types.pp ty'
    | [], Moved _ -> Fmt.failwith "That memory was moved!!"
    | _ -> Fmt.failwith "Invalid projection %a" Projections.pp proj

  let set_proj t proj ty v =
    match (proj, t) with
    | [], (BaseValue (_, ty') | Moved ty') when ty = ty' ->
        let new_bv = BaseValues.of_lit_and_ty v ty in
        BaseValue new_bv
    | _ -> Fmt.failwith "Invalid projection %a" Projections.pp proj

  let uninitialized ty = BaseValue (Rust_types.uninitialized_value ty, ty)

  let pp fmt = function
    | BaseValue v -> BaseValues.pp fmt v
    | Moved ty    -> Fmt.pf fmt "MOVED: %a" Rust_types.pp ty
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
