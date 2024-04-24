open Gillian.Concrete
open Gillian.Gil_syntax

type init_data = Tyenv.t
type vt = Values.t
type st = Subst.t
type err_t = string [@@deriving show]
type t = { tyenv : Tyenv.t; heap : Heap.t }
type action_ret = (t * vt list, err_t) result

(* Utils *)

let wrong_args act args =
  Fmt.failwith "Invalid call to %s: %a" act (Fmt.Dump.list Literal.pp) args

(* Basic memory things *)

let init tyenv = { tyenv; heap = Heap.empty () }

(* Actions *)

let execute_alloc mem args =
  match args with
  | [ ty ] ->
      let rust_ty = Ty.of_lit ty in
      let new_loc, new_heap = Heap.alloc ~tyenv:mem.tyenv mem.heap rust_ty in
      let ret = [ Literal.Loc new_loc; Literal.LList [] ] in
      Ok ({ mem with heap = new_heap }, ret)
  | _ -> wrong_args "alloc" args

let execute_load_value mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; ty; Literal.Bool copy ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let ret, new_heap =
        Heap.load ~tyenv:mem.tyenv mem.heap loc proj rust_ty copy
      in
      Ok ({ mem with heap = new_heap }, [ ret ])
  | _ -> wrong_args "load_value" args

let execute_store_value mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty; value ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let new_heap =
        Heap.store ~tyenv:mem.tyenv mem.heap loc proj rust_ty value
      in
      Ok ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "store_value" args

let execute_deinit mem args =
  match args with
  | [ Literal.Loc loc; LList proj; ty ] ->
      let rust_ty = Ty.of_lit ty in
      let proj = Projections.of_lit_list proj in
      let new_heap = Heap.deinit ~tyenv:mem.tyenv mem.heap loc proj rust_ty in
      Ok ({ mem with heap = new_heap }, [])
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
      let new_heap = Heap.free mem.heap loc rust_ty in
      Ok ({ mem with heap = new_heap }, [])
  | _ -> wrong_args "free" args

let execute_load_discr mem args =
  match args with
  | [ Literal.Loc loc; Literal.LList proj; enum_typ ] ->
      let enum_typ = Ty.of_lit enum_typ in
      let proj = Projections.of_lit_list proj in
      let discr = Heap.load_discr ~tyenv:mem.tyenv mem.heap loc proj enum_typ in
      Ok (mem, [ Literal.Int (Z.of_int discr) ])
  | _ -> wrong_args "execute_load_discr" args

let protect f mem args = try f mem args with Heap.MemoryError s -> Error s
[@@inline]

let execute_action act_name mem args =
  match Actions.of_name act_name with
  | Alloc -> protect execute_alloc mem args
  | Load_value -> protect execute_load_value mem args
  | Store_value -> protect execute_store_value mem args
  | Deinit -> protect execute_deinit mem args
  | Free -> protect execute_free mem args
  | Load_discr -> protect execute_load_discr mem args
  | Pcy_resolve
  | Pcy_alloc
  | Pcy_assign
  | Size_of
  | Is_zst
  | Ty_is_unsized
  | Copy_nonoverlapping ->
      Fmt.failwith "%s yet implemented in concrete execution" act_name

let copy { heap; tyenv } = { heap = Heap.copy heap; tyenv }
(* We don't need to copy tyenv, because it's immutable *)

let pp =
  Fmt.braces
  @@ Fmt.record ~sep:Fmt.semi
       [
         Fmt.field "tyenv" (fun x -> x.tyenv) Tyenv.pp;
         Fmt.field "heap" (fun x -> x.heap) Heap.pp;
       ]

let pp_err _ _ = failwith "Not implemented yet!"
