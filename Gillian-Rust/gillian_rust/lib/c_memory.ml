open Gillian.Concrete
open Gillian.Gil_syntax

type vt = Values.t

type st = Subst.t

type err_t = unit

type fix_t = unit

type t = C_heap.t

type action_ret = ASucc of (t * vt list) | AFail of err_t list

(* Utils *)

let wrong_args act args =
  Fmt.failwith "Invalid call to %s: %a" act (Fmt.Dump.list Literal.pp) args

(* Basic memory things *)

let init () = C_heap.empty ()

(* Actions *)

let execute_alloc mem args =
  match args with
  | [ ty ] ->
      let rust_ty = Rust_types.of_lit ty in
      let new_loc, new_mem = C_heap.alloc mem rust_ty in
      let ret = [ Literal.Loc new_loc; Literal.LList [] ] in
      ASucc (new_mem, ret)
  | _      -> wrong_args "alloc" args

let execute_load mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; ty; Literal.Bool copy ] ->
      let rust_ty = Rust_types.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let ret, new_mem = C_heap.load mem loc proj rust_ty copy in
      ASucc (new_mem, [ ret ])
  | _ -> wrong_args "load" args

let execute_store mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; ty; value ] ->
      let rust_ty = Rust_types.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let new_mem = C_heap.store mem loc proj rust_ty value in
      ASucc (new_mem, [])
  | _ -> wrong_args "store" args

let execute_action act_name mem args =
  match Actions.of_name act_name with
  | Alloc -> execute_alloc mem args
  | Load  -> execute_load mem args
  | Store -> execute_store mem args

let copy x = x

let pp = C_heap.pp

let pp_err _ _ = failwith "Not implemented yet!"

(* SYMBOLIC STUFF -- never instantiated *)
let ga_to_setter _ga = failwith "Not implemented yet!"

let ga_to_deleter _ga = failwith "Not implemented yet!"

let ga_to_getter _ga = failwith "Not implemented yet!"

let ga_loc_indexes _ = failwith "Not implemented yet!"

let is_overlapping_asrt _ = failwith "Not implemented yet!"

let substitution_in_place _ _ = ()

let fresh_val _ = failwith "Not implemented yet!"

let clean_up _ = failwith "Not implemented yet!"

let lvars _ = failwith "Not implemented yet!"

let assertions ?to_keep:_ _ = failwith "Not implemented yet!"
