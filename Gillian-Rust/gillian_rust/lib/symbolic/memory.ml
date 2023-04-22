open Gillian.Symbolic
open Gillian.Monadic
open Gillian.Gil_syntax
module DR = Delayed_result
module Actions = Common.Actions
open DR.Syntax
open Delayed.Syntax

type init_data = Common.Tyenv.t
type vt = Values.t
type st = Subst.t
type c_fix_t = unit
type err_t = Err.t [@@deriving yojson, show]

type t = {
  tyenv : Common.Tyenv.t;
  pcies : Prophecies.t;
  heap : Heap.t;
  lfts : Lft_ctx.t;
}
[@@deriving yojson]

type action_ret = (t * vt list, err_t) result

let resolve_pcy_var (e : Expr.t) : Expr.t Delayed.t = Delayed.reduce e

let resolve_or_create_loc_name (lvar_loc : Expr.t) : string Delayed.t =
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
  let+ e = Delayed.reduce e in
  Projections.of_expr e

let resolve_loc_result loc =
  Delayed_result.of_do ~none:(Err.Invalid_loc loc) (Delayed.resolve_loc loc)

let init tyenv =
  { tyenv; heap = Heap.empty; lfts = Lft_ctx.empty; pcies = Prophecies.empty }

let clear t = { t with heap = Heap.empty; lfts = Lft_ctx.empty }
let make_branch ~mem ?(rets = []) () = (mem, rets)

let execute_alloc mem args =
  let { heap; tyenv; lfts } = mem in
  match args with
  | [ ty ] ->
      let ty = Ty.of_expr ty in
      let loc, new_heap = Heap.alloc ~tyenv heap ty in
      DR.ok
        (make_branch
           ~mem:{ mem with heap = new_heap }
           ~rets:[ Expr.ALoc loc; EList [] ]
           ())
  | _ -> Fmt.failwith "Invalid arguments for alloc"

let execute_store mem args =
  let { heap; tyenv; lfts } = mem in
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ new_heap = Heap.store ~tyenv heap loc proj ty value in
      make_branch ~mem:{ mem with heap = new_heap } ()
  | _ -> Fmt.failwith "Invalid arguments for store"

let execute_load mem args =
  let { heap; tyenv; lfts } = mem in
  match args with
  | [ loc; proj; ty; Expr.Lit (Bool copy) ] ->
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ value, new_heap = Heap.load ~tyenv heap loc proj ty copy in
      make_branch ~mem:{ mem with heap = new_heap } ~rets:[ value ] ()
  | _ -> Fmt.failwith "Invalid arguments for load"

let execute_load_discr mem args =
  match args with
  | [ loc; proj; enum_typ ] ->
      let enum_typ = Ty.of_expr enum_typ in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ discr =
        Heap.load_discr ~tyenv:mem.tyenv mem.heap loc proj enum_typ
      in
      make_branch ~mem ~rets:[ discr ] ()
  | _ -> Fmt.failwith "Invalid arguments for load_discr"

let execute_free mem args =
  let { heap; tyenv; lfts } = mem in
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
      let++ new_heap = Heap.free heap loc ty in
      make_branch ~mem:{ mem with heap = new_heap } ()
  | _ -> Fmt.failwith "Invalid arguments for free"

let execute_get_value mem args =
  let { heap; tyenv; lfts } = mem in
  match args with
  | [ loc; proj_exp; ty_exp ] ->
      let ty = Ty.of_expr ty_exp in
      let** loc_name = resolve_loc_result loc in
      let* proj = projections_of_expr proj_exp in
      let++ value = Heap.get_value ~tyenv heap loc_name proj ty in
      make_branch ~mem
        ~rets:[ Expr.loc_from_loc_name loc_name; proj_exp; ty_exp; value ]
        ()
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let execute_set_value mem args =
  let { heap; tyenv; lfts } = mem in
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = projections_of_expr proj in
      let++ new_heap = Heap.set_value ~tyenv heap loc_name proj ty value in
      make_branch ~mem:{ mem with heap = new_heap } ()
  | _ -> Fmt.failwith "Invalid arguments for set_value"

let execute_rem_value mem args =
  match args with
  | [ loc; _proj_exp; _ty_exp ] ->
      let loc_name =
        match loc with
        | Expr.ALoc loc | Lit (Loc loc) -> loc
        | _ -> failwith "unreachable"
      in
      let new_heap = Heap.rem_value mem.heap loc_name in
      DR.ok (make_branch ~mem:{ mem with heap = new_heap } ())
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let ga_to_setter str = Actions.ga_to_setter_str str
let ga_to_getter str = Actions.ga_to_getter_str str
let ga_to_deleter str = Actions.ga_to_deleter_str str
let is_overlapping_asrt _ = false
let copy t = t

let pp ft t =
  Fmt.pf ft "@[<v 2>Heap:@,%a@]@ @[<v 2>Lifetimes:@,%a@]@ %a" Heap.pp t.heap
    Lft_ctx.pp t.lfts Prophecies.pp t.pcies

let pp_by_need _ _ = failwith "pp_by_need: Not yet implemented"
let get_print_info _ _ = failwith "get_print_info: Not yet implemented"
let fresh_val _ = failwith "fresh_val: Not yet implemented"
let clean_up ?keep:_ _ = failwith "clean_up: Not yet implemented"
let lvars _ = failwith "lvars: Not yet implemented"
let alocs _ = failwith "alocs: Not yet implemented"

let assertions ?to_keep:_ { heap; tyenv; lfts } =
  Lft_ctx.assertions lfts @ Heap.assertions ~tyenv heap

let mem_constraints _ =
  Logging.normal (fun m -> m "WARNING: MEM_CONSTRAINTS\n@?");
  []

let pp_c_fix _ _ = failwith "pp_c_fix: Not yet implemented"
let pp_err ft t = Err.pp ft t

let get_failing_constraint _ =
  failwith "get_failing_constraints: Not yet implemented"

let get_fixes ?simple_fix:_ _ _ _ = failwith "get_fixes: Not yet implemented"
let apply_fix _ _ _ _ = failwith "apply_fix: Not yet implemented"
let get_recovery_tactic _ e = Err.recovery_tactic e

let execute_get_lft mem args =
  let open Gillian.Utils.Syntaxes.Result in
  match args with
  | [ lft_expr ] ->
      let lft = Lft.of_expr lft_expr in
      let res =
        let+ res = Lft_ctx.get mem.lfts lft in
        make_branch ~mem ~rets:[ lft_expr; Expr.bool res ] ()
      in
      Delayed.return res
  | _ -> Fmt.failwith "Invalid arguments for get_alive_lft"

let execute_set_lft mem args =
  let open Gillian.Utils.Syntaxes.Result in
  match args with
  | [ lft; Expr.Lit (Bool status) ] ->
      let lft = Lft.of_expr lft in
      let ret =
        let+ lfts = Lft_ctx.produce mem.lfts lft status in
        make_branch ~mem:{ mem with lfts } ()
      in
      Delayed.return ret
  | _ -> Fmt.failwith "Invalid arguments for new_lft"

let execute_rem_lft mem args =
  match args with
  | [ lft ] ->
      let lft = Lft.of_expr lft in
      let new_lfts = Lft_ctx.remove mem.lfts lft in
      DR.ok (make_branch ~mem:{ mem with lfts = new_lfts } ())
  | _ -> Fmt.failwith "Invalid arguments for rem_alive_lft"

let execute_get_value_observer mem args =
  let { heap; pcies; tyenv; lfts } = mem in
  match args with
  | [ pcy_id; proj_exp; ty_exp ] ->
      let** pcy_id = resolve_loc_result pcy_id in
      let ty = Ty.of_expr ty_exp in
      let* proj = projections_of_expr proj_exp in
      let++ value = Prophecies.get_value_obs ~tyenv pcies pcy_id proj ty in
      make_branch ~mem ~rets:[ Expr.ALoc pcy_id; proj_exp; ty_exp; value ] ()
  | _ -> Fmt.failwith "Invalid arguments for get_value_observer"

let execute_set_value_observer mem args =
  let { pcies; tyenv } = mem in
  match args with
  | [ pcy_id; proj; ty; value ] ->
      let* pcy_id = resolve_or_create_loc_name pcy_id in
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let++ new_pcies =
        Prophecies.set_value_obs ~tyenv pcies pcy_id proj ty value
      in
      make_branch ~mem:{ mem with pcies = new_pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for set_value_observer"

let execute_rem_value_observer mem args =
  match args with
  | [ Expr.ALoc pcy_id; proj_exp; ty_exp ] ->
      let* proj = projections_of_expr proj_exp in
      let ty = Ty.of_expr ty_exp in
      let++ new_pcies =
        Prophecies.rem_value_obs ~tyenv:mem.tyenv mem.pcies pcy_id proj ty
      in
      make_branch ~mem:{ mem with pcies = new_pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let execute_get_pcy_controller mem args =
  let { heap; pcies; tyenv; lfts } = mem in
  match args with
  | [ pcy_id; proj_exp; ty_exp ] ->
      let** pcy_id = resolve_loc_result pcy_id in
      let ty = Ty.of_expr ty_exp in
      let* proj = projections_of_expr proj_exp in
      let++ value = Prophecies.get_controller ~tyenv pcies pcy_id proj ty in
      make_branch ~mem ~rets:[ Expr.ALoc pcy_id; proj_exp; ty_exp; value ] ()
  | _ -> Fmt.failwith "Invalid arguments for get_pcy_controller"

let execute_set_pcy_controller mem args =
  let { pcies; tyenv } = mem in
  match args with
  | [ pcy_id; proj; ty; value ] ->
      let* pcy_id = resolve_or_create_loc_name pcy_id in
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let++ new_pcies =
        Prophecies.set_controller ~tyenv pcies pcy_id proj ty value
      in
      make_branch ~mem:{ mem with pcies = new_pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for set_pcy_controller"

let execute_rem_pcy_controller mem args =
  match args with
  | [ Expr.ALoc pcy_id; proj_exp; ty_exp ] ->
      let* proj = projections_of_expr proj_exp in
      let ty = Ty.of_expr ty_exp in
      let++ new_pcies =
        Prophecies.rem_controller ~tyenv:mem.tyenv mem.pcies pcy_id proj ty
      in
      make_branch ~mem:{ mem with pcies = new_pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let execute_pcy_resolve mem args =
  match args with
  | [ pcy_id; proj_exp; ty ] ->
      let ty = Ty.of_expr ty in
      let** pcy_id = resolve_loc_result pcy_id in
      let* proj = projections_of_expr proj_exp in
      let++ new_pcies =
        Prophecies.resolve ~tyenv:mem.tyenv mem.pcies pcy_id proj ty
      in
      make_branch ~mem:{ mem with pcies = new_pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for pcy_resolve"

let execute_pcy_assign mem args =
  let { pcies; tyenv; lfts } = mem in
  match args with
  | [ pcy_id; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let** pcy_id = resolve_loc_result pcy_id in
      let++ new_pcies = Prophecies.assign ~tyenv pcies pcy_id proj ty value in
      make_branch ~mem:{ mem with pcies = new_pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for store"

let execute_pcy_alloc mem args =
  match args with
  | [ ty ] ->
      let ty = Ty.of_expr ty in
      let ret, pcies = Prophecies.alloc ~tyenv:mem.tyenv mem.pcies ty in
      DR.ok @@ make_branch ~mem:{ mem with pcies } ~rets:ret ()
  | _ -> Fmt.failwith "Invalid arguments for pcy_alloc"

let execut_get_pcy_value mem args =
  match args with
  | [ pcy_id; proj_expr; ty_expr ] ->
      let* proj = projections_of_expr proj_expr in
      let++ pcy_id = resolve_loc_result pcy_id in
      let ty = Ty.of_expr ty_expr in
      let ret, new_pcies =
        Prophecies.get_value ~tyenv:mem.tyenv mem.pcies pcy_id proj ty
      in
      make_branch
        ~mem:{ mem with pcies = new_pcies }
        ~rets:[ Expr.LVar pcy_id; proj_expr; ty_expr; ret ]
        ()
  | _ -> Fmt.failwith "Invalid arguments for pcy_get_value"

let execute_set_pcy_value mem args =
  match args with
  | [ pcy_id; proj_expr; ty_expr; value ] ->
      let* pcy_id = resolve_or_create_loc_name pcy_id in
      let* proj = projections_of_expr proj_expr in
      let ty = Ty.of_expr ty_expr in
      let++ pcies =
        Prophecies.set_value ~tyenv:mem.tyenv mem.pcies pcy_id proj ty value
      in
      make_branch ~mem:{ mem with pcies } ()
  | _ -> Fmt.failwith "Invalid arguments for pcy_set_value"

let execute_rem_pcy_value mem args_ = DR.ok (make_branch ~mem ())

let pp_branch fmt branch =
  let _, values = branch in
  Fmt.pf fmt "Returns: %a@.(Ignoring heap)" (Fmt.Dump.list Expr.pp) values

let filter_errors dr =
  Delayed.bind dr (fun res ->
      match res with
      | Ok _ -> Delayed.return res
      | Error err ->
          Logging.tmi (fun m -> m "Filtering error branch: %a" Err.pp err);
          Delayed.vanish ())

let execute_action ~action_name mem args =
  Logging.verbose (fun fmt ->
      fmt "Executing action %s with params %a" action_name
        (Fmt.Dump.list Expr.pp) args);
  Logging.tmi (fun fmt -> fmt "Current heap : %a" pp mem);
  let action = Actions.of_name action_name in
  let+ res =
    match action with
    | Alloc -> execute_alloc mem args
    | Load_value -> execute_load mem args
    | Store_value -> execute_store mem args
    | Load_discr -> execute_load_discr mem args
    | Free -> execute_free mem args
    | Pcy_alloc -> execute_pcy_alloc mem args
    | Pcy_resolve -> execute_pcy_resolve mem args
    | Pcy_assign -> execute_pcy_assign mem args
    | Get_value -> execute_get_value mem args
    | Set_value ->
        (* Producers cannot fail, so we filter all errors and constrain the paths *)
        execute_set_value mem args |> filter_errors
    | Rem_value -> execute_rem_value mem args
    | Get_lft -> execute_get_lft mem args
    | Set_lft -> execute_set_lft mem args |> filter_errors
    | Rem_lft -> execute_rem_lft mem args
    | Get_value_observer -> execute_get_value_observer mem args
    | Set_value_observer -> execute_set_value_observer mem args
    | Rem_value_observer -> execute_rem_value_observer mem args
    | Get_pcy_controller -> execute_get_pcy_controller mem args
    | Set_pcy_controller -> execute_set_pcy_controller mem args
    | Rem_pcy_controller -> execute_rem_pcy_controller mem args
    | Get_pcy_value -> execut_get_pcy_value mem args
    | Set_pcy_value -> execute_set_pcy_value mem args
    | Rem_pcy_value -> execute_rem_pcy_value mem args
    | _ -> Fmt.failwith "unhandled action: %s" (Actions.to_name action)
  in
  Logging.verbose (fun fmt ->
      fmt "Resulting in: %a" (Fmt.Dump.result ~ok:pp_branch ~error:pp_err) res);
  res

let get_oks dr =
  Delayed.bind dr (fun res ->
      match res with
      | Ok x -> Delayed.return x
      | Error err ->
          Logging.tmi (fun m -> m "Filtering error branch: %a" Err.pp err);
          Delayed.vanish ())

let substitution_in_place s mem =
  let* heap = Heap.substitution ~tyenv:mem.tyenv mem.heap s |> get_oks in
  let+ pcies =
    Prophecies.substitution ~tyenv:mem.tyenv mem.pcies s |> get_oks
  in
  { mem with heap; pcies; lfts = Lft_ctx.substitution s mem.lfts }
