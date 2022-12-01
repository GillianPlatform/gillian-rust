open Gillian.Concrete
open Gillian.Gil_syntax

type init_data = Tyenv.t
type vt = Values.t
type st = Subst.t
type err_t = string [@@deriving show]
type t = { tyenv : Tyenv.t; heap : C_heap.t }
type action_ret = ASucc of (t * vt list) | AFail of err_t list

(* Utils *)

let wrong_args act args =
  Fmt.failwith "Invalid call to %s: %a" act (Fmt.Dump.list Literal.pp) args

(* Basic memory things *)

let init tyenv = { tyenv; heap = C_heap.empty () }

(* Actions *)

let execute_alloc mem args =
  match args with
  | [ ty ] ->
      let rust_ty = Ty.of_lit ty in
      let new_loc, new_heap = C_heap.alloc ~tyenv:mem.tyenv mem.heap rust_ty in
      let ret = [ Literal.Loc new_loc; Literal.LList [] ] in
      ASucc ({ mem with heap = new_heap }, ret)
  | _ -> wrong_args "alloc" args

let execute_load_value mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; ty; Literal.Bool copy ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let ret, new_heap =
        C_heap.load ~tyenv:mem.tyenv mem.heap loc proj rust_ty copy
      in
      ASucc ({ mem with heap = new_heap }, [ ret ])
  | _ -> wrong_args "load_value" args

let execute_load_slice mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; Int size; ty; Literal.Bool copy ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let size = Z.to_int size in
      let ret, new_heap =
        C_heap.load_slice ~tyenv:mem.tyenv mem.heap loc proj size rust_ty copy
      in
      ASucc ({ mem with heap = new_heap }, [ LList ret ])
  | _ -> wrong_args "load_slice" args

let execute_store_value mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty; value ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let new_heap =
        C_heap.store ~tyenv:mem.tyenv mem.heap loc proj rust_ty value
      in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "store_value" args

let execute_store_slice mem args =
  match args with
  | [ Literal.Loc loc; LList proj; Int size; ty; LList values ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let size = Z.to_int size in
      let new_heap =
        C_heap.store_slice ~tyenv:mem.tyenv mem.heap loc proj size rust_ty
          values
      in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "store_slice" args

let execute_deinit mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let new_heap = C_heap.deinit ~tyenv:mem.tyenv mem.heap loc proj rust_ty in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "execute_deinit" args

let execute_free mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty ] ->
      let () =
        match proj with
        | [] -> ()
        | _ -> Fmt.failwith "Invalid free: (%s, %a)" loc Literal.pp (LList proj)
      in
      let rust_ty = Ty.of_lit ty in
      let new_heap = C_heap.free mem.heap loc rust_ty in
      ASucc ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "free" args

let execute_load_discr mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; enum_typ ] ->
      let enum_typ = Ty.of_lit enum_typ in
      let proj = Projections.of_lit_list proj in
      let discr =
        C_heap.load_discr ~tyenv:mem.tyenv mem.heap loc proj enum_typ
      in
      ASucc (mem, [ Int (Z.of_int discr) ])
  | _ -> wrong_args "execute_load_discr" args

let protect f mem args =
  try f mem args with C_heap.MemoryError s -> AFail [ s ]
  [@@inline]

let execute_action act_name mem args =
  match Actions.of_name act_name with
  | Alloc -> protect execute_alloc mem args
  | Load_value -> protect execute_load_value mem args
  | Store_value -> protect execute_store_value mem args
  | Load_slice -> protect execute_load_slice mem args
  | Store_slice -> protect execute_store_slice mem args
  | Deinit -> protect execute_deinit mem args
  | Free -> protect execute_free mem args
  | Load_discr -> protect execute_load_discr mem args
  | Get_value | Set_value | Rem_value | Get_freed | Set_freed | Rem_freed ->
      failwith "Core Predicates used in concrete execution"

let copy { heap; tyenv } = { heap = C_heap.copy heap; tyenv }
(* We don't need to copy tyenv, because it's immutable *)

let pp =
  Fmt.braces
  @@ Fmt.record ~sep:Fmt.semi
       [
         Fmt.field "tyenv" (fun x -> x.tyenv) Tyenv.pp;
         Fmt.field "heap" (fun x -> x.heap) C_heap.pp;
       ]

let pp_err _ _ = failwith "Not implemented yet!"
