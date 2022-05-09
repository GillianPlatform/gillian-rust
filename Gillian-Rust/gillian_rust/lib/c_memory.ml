open Gillian.Concrete
open Gillian.Gil_syntax

type vt = Values.t
type st = Subst.t
type err_t = unit
type fix_t = unit
type t = { genv : C_global_env.t; heap : C_heap.t }
type action_ret = ASucc of (t * vt list) | AFail of err_t list

(* Utils *)

let wrong_args act args =
  Fmt.failwith "Invalid call to %s: %a" act (Fmt.Dump.list Literal.pp) args

(* Basic memory things *)

let init () = { genv = C_global_env.empty (); heap = C_heap.empty () }

(* Actions *)

let execute_alloc mem args =
  match args with
  | [ ty ] ->
      let rust_ty = Rust_types.of_lit ty in
      let new_loc, new_heap = C_heap.alloc ~genv:mem.genv mem.heap rust_ty in
      let ret = [ Literal.Loc new_loc; Literal.LList [] ] in
      ASucc ({ mem with heap = new_heap }, ret)
  | _      -> wrong_args "alloc" args

let execute_load mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; ty; Literal.Bool copy ] ->
      let rust_ty = Rust_types.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let ret, new_heap =
        C_heap.load ~genv:mem.genv mem.heap loc proj rust_ty copy
      in
      ASucc ({ mem with heap = new_heap }, [ ret ])
  | _ -> wrong_args "load" args

let execute_store mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty; value ] ->
      let rust_ty = Rust_types.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let new_heap =
        C_heap.store ~genv:mem.genv mem.heap loc proj rust_ty value
      in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "store" args

let execute_free mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty ] ->
      let () =
        match proj with
        | [] -> ()
        | _  -> Fmt.failwith "Invalid free: (%s, %a)" loc Literal.pp (LList proj)
      in
      let rust_ty = Rust_types.of_lit ty in
      let new_heap = C_heap.free ~genv:mem.genv mem.heap loc rust_ty in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "free" args

let execute_genv_decl_type mem args =
  match args with
  | [ Literal.String name; decl ] ->
      C_global_env.declare_struct mem.genv name decl;
      ASucc (mem, [])
  | _ -> wrong_args "execute_genv_decl_type" args

let execute_load_discr mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj ] ->
      let proj = Projections.of_lit_list proj in
      let discr = C_heap.load_discr ~genv:mem.genv mem.heap loc proj in
      ASucc (mem, [ Int (Z.of_int discr) ])
  | _ -> wrong_args "execute_load_discr" args

let execute_store_discr mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; Int discr ] ->
      let proj = Projections.of_lit_list proj in
      let new_heap =
        C_heap.store_discr ~genv:mem.genv mem.heap loc proj (Z.to_int discr)
      in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "execute_store_discr" args

let execute_action act_name mem args =
  match Actions.of_name act_name with
  | Alloc          -> execute_alloc mem args
  | Load           -> execute_load mem args
  | Store          -> execute_store mem args
  | Free           -> execute_free mem args
  | Genv_decl_type -> execute_genv_decl_type mem args
  | LoadDiscr      -> execute_load_discr mem args
  | StoreDiscr     -> execute_store_discr mem args

let copy { heap; genv } =
  { heap = C_heap.copy heap; genv = C_global_env.copy genv }

let pp =
  Fmt.braces
  @@ Fmt.record ~sep:Fmt.semi
       [
         Fmt.field "genv" (fun x -> x.genv) C_global_env.pp;
         Fmt.field "heap" (fun x -> x.heap) C_heap.pp;
       ]

let pp_err _ _ = failwith "Not implemented yet!"

(* SYMBOLIC STUFF -- never instantiated *)
let ga_to_setter _ga = failwith "Not implemented yet!"
let ga_to_deleter _ga = failwith "Not implemented yet!"
let ga_to_getter _ga = failwith "Not implemented yet!"
let is_overlapping_asrt _ = failwith "Not implemented yet!"
let substitution_in_place _ _ = ()
let fresh_val _ = failwith "Not implemented yet!"
let clean_up ?keep:_ _ = failwith "Not implemented yet!"
let lvars _ = failwith "Not implemented yet!"
let assertions ?to_keep:_ _ = failwith "Not implemented yet!"
