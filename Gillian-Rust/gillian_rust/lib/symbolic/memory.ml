open Gillian.Symbolic
open Gillian.Monadic
open Gillian.Gil_syntax
module DR = Delayed_result
module Actions = Common.Actions

type init_data = Common.Tyenv.t
type vt = Values.t
type st = Subst.t
type c_fix_t = unit
type err_t = Err.t [@@deriving yojson, show]
type t = { tyenv : Common.Tyenv.t; mem : Heap.t } [@@deriving yojson]
type action_ret = Success of (t * vt list) | Failure of err_t

let resolve_or_create_loc_name (lvar_loc : Expr.t) : string Delayed.t =
  let open Delayed.Syntax in
  let* loc_name = Delayed.resolve_loc lvar_loc in
  match loc_name with
  | None ->
      let new_loc_name = ALoc.alloc () in
      let learned = [ Formula.Eq (ALoc new_loc_name, lvar_loc) ] in
      Logging.verbose (fun fmt ->
          fmt "Couldn't resolve loc %a, created %s" Expr.pp lvar_loc
            new_loc_name);
      Delayed.return ~learned new_loc_name
  | Some l ->
      Logging.verbose (fun fmt -> fmt "Resolved %a as %s" Expr.pp lvar_loc l);
      Delayed.return l

let projections_of_expr (e : Expr.t) : Projections.t Delayed.t =
  let open Delayed.Syntax in
  Logging.verbose (fun m -> m "Resolving projections %a@?" Expr.pp e);
  let+ e = Delayed.reduce e in
  Logging.verbose (fun m -> m "Reduced projections to %a@?" Expr.pp e);
  Projections.of_expr e

let resolve_loc_result loc =
  Delayed_result.of_do ~none:(Err.Invalid_loc loc) (Delayed.resolve_loc loc)

let init tyenv = { tyenv; mem = Heap.empty }
let clear t = { t with mem = Heap.empty }
let make_branch ~tyenv ~mem ?(rets = []) () = ({ mem; tyenv }, rets)

let execute_alloc ~tyenv mem args =
  match args with
  | [ ty ] ->
      let ty = Ty.of_expr ty in
      let loc, new_mem = Heap.alloc ~tyenv mem ty in
      DR.ok
        (make_branch ~tyenv ~mem:new_mem ~rets:[ Expr.ALoc loc; EList [] ] ())
  | _ -> Fmt.failwith "Invalid arguments for alloc"

let execute_store ~tyenv mem args =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ new_mem = Heap.store ~tyenv mem loc proj ty value in
      make_branch ~tyenv ~mem:new_mem ()
  | _ -> Fmt.failwith "Invalid arguments for store"

let execute_load ~tyenv mem args =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; proj; ty; Expr.Lit (Bool copy) ] ->
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ value, new_mem = Heap.load ~tyenv mem loc proj ty copy in
      make_branch ~tyenv ~mem:new_mem ~rets:[ value ] ()
  | _ -> Fmt.failwith "Invalid arguments for load"

let execute_load_discr ~tyenv mem args =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; proj; enum_typ ] ->
      let enum_typ = Ty.of_expr enum_typ in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ discr = Heap.load_discr ~tyenv mem loc proj enum_typ in
      make_branch ~tyenv ~mem ~rets:[ discr ] ()
  | _ -> Fmt.failwith "Invalid arguments for load_discr"

let execute_free ~tyenv mem args =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; proj; ty ] ->
      let** () =
        Delayed.branch_on
          (Formula.Eq (proj, EList []))
          ~then_:(fun () -> DR.ok ())
          ~else_:(fun () -> DR.error (Err.Invalid_free_pointer (loc, proj)))
      in
      let** loc = resolve_loc_result loc in
      let ty = Ty.of_expr ty in
      let++ new_mem = Heap.free mem loc ty in
      make_branch ~tyenv ~mem:new_mem ()
  | _ -> Fmt.failwith "Invalid arguments for free"

let execute_get_value ~tyenv mem args =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; proj_exp; ty_exp ] ->
      let ty = Ty.of_expr ty_exp in
      let** loc_name = resolve_loc_result loc in
      let* proj = projections_of_expr proj_exp in
      let++ value = Heap.get_value ~tyenv mem loc_name proj ty in
      make_branch ~tyenv ~mem
        ~rets:[ Expr.loc_from_loc_name loc_name; proj_exp; ty_exp; value ]
        ()
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let execute_set_value ~tyenv mem args =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = projections_of_expr proj in
      let++ new_mem = Heap.set_value ~tyenv mem loc_name proj ty value in
      make_branch ~tyenv ~mem:new_mem ()
  | _ -> Fmt.failwith "Invalid arguments for set_value"

let execute_rem_value ~tyenv mem args =
  match args with
  | [ loc; _proj_exp; _ty_exp ] ->
      let loc_name =
        match loc with
        | Expr.ALoc loc | Lit (Loc loc) -> loc
        | _ -> failwith "unreachable"
      in
      let mem = Heap.rem_value mem loc_name in
      DR.ok (make_branch ~tyenv ~mem ())
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let ga_to_setter str = Actions.ga_to_setter_str str
let ga_to_getter str = Actions.ga_to_getter_str str
let ga_to_deleter str = Actions.ga_to_deleter_str str
let is_overlapping_asrt _ = false
let copy t = t
let pp ft t = Heap.pp ft t.mem
let pp_by_need _ _ = failwith "pp_by_need: Not yet implemented"
let get_print_info _ _ = failwith "get_print_info: Not yet implemented"

let substitution_in_place s mem =
  Delayed.return
  @@ { mem with mem = Heap.substitution ~tyenv:mem.tyenv mem.mem s }

let fresh_val _ = failwith "fresh_val: Not yet implemented"
let clean_up ?keep:_ _ = failwith "clean_up: Not yet implemented"
let lvars _ = failwith "lvars: Not yet implemented"
let alocs _ = failwith "alocs: Not yet implemented"
let assertions ?to_keep:_ { mem; tyenv } = Heap.assertions ~tyenv mem

let mem_constraints _ =
  Logging.normal (fun m -> m "WARNING: MEM_CONSTRAINTS\n@?");
  []

let pp_c_fix _ _ = failwith "pp_c_fix: Not yet implemented"
let pp_err ft t = Err.pp ft t

let get_failing_constraint _ =
  failwith "get_failing_constraints: Not yet implemented"

let get_fixes ?simple_fix:_ _ _ _ = failwith "get_fixes: Not yet implemented"
let apply_fix _ _ _ _ = failwith "apply_fix: Not yet implemented"
let get_recovery_vals _ e = Err.recovery_vals e

let lift_res res =
  match res with
  | Ok a -> Success a
  | Error e -> Failure e

let pp_branch fmt branch =
  let _, values = branch in
  Fmt.pf fmt "Returns: %a@.(Ignoring heap)" (Fmt.Dump.list Expr.pp) values

let lift_dr_and_log res =
  let pp_res = Fmt.Dump.result ~ok:pp_branch ~error:pp_err in
  Delayed.map res (fun res ->
      Logging.verbose (fun fmt -> fmt "Resulting in: %a" pp_res res);
      lift_res res)

let execute_action ~action_name mem args =
  Logging.verbose (fun fmt ->
      fmt "Executing action %s with params %a" action_name
        (Fmt.Dump.list Expr.pp) args);
  Logging.tmi (fun fmt -> fmt "Current heap : %a" pp mem);
  let { tyenv; mem } = mem in
  let action = Actions.of_name action_name in
  let a_ret =
    match action with
    | Alloc -> execute_alloc ~tyenv mem args
    | Load_value -> execute_load ~tyenv mem args
    | Store_value -> execute_store ~tyenv mem args
    | Load_discr -> execute_load_discr ~tyenv mem args
    | Free -> execute_free ~tyenv mem args
    | Get_value -> execute_get_value ~tyenv mem args
    | Set_value -> execute_set_value ~tyenv mem args
    | Rem_value -> execute_rem_value ~tyenv mem args
    | _ -> Fmt.failwith "unhandled action: %s" (Actions.to_name action)
  in
  lift_dr_and_log a_ret
