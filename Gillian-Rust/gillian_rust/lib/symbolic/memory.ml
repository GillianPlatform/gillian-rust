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
  obs_ctx : Obs_ctx.t;
}
[@@deriving yojson]

type action_ret = (t * vt list, err_t) result

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
  {
    tyenv;
    heap = Heap.empty;
    lfts = Lft_ctx.empty;
    pcies = Prophecies.empty;
    obs_ctx = Obs_ctx.empty;
  }

let sure_is_nonempty { heap; lfts; pcies; _ } =
  Heap.sure_is_nonempty heap
  || (not @@ Lft_ctx.is_empty lfts)
  || Prophecies.sure_is_nonempty pcies

let get_init_data { tyenv; _ } = tyenv
let clear t = { t with heap = Heap.empty; lfts = Lft_ctx.empty }
let make_branch ~mem ?(rets = []) () = (mem, rets)

let execute_alloc mem args =
  let { heap; tyenv; _ } = mem in
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
  let { heap; tyenv; _ } = mem in
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let** loc = resolve_loc_result loc in
      let++ new_heap = Heap.store ~tyenv heap loc proj ty value in
      make_branch ~mem:{ mem with heap = new_heap } ()
  | _ -> Fmt.failwith "Invalid arguments for store"

let execute_load mem args =
  let { heap; tyenv; _ } = mem in
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
  let { heap; _ } = mem in
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

let execute_cons_value mem args =
  let { heap; tyenv; _ } = mem in
  match args with
  | [ loc; proj_exp; ty_exp ] ->
      let ty = Ty.of_expr ty_exp in
      let** loc_name = resolve_loc_result loc in
      let* proj = projections_of_expr proj_exp in
      let++ value, heap = Heap.cons_value ~tyenv heap loc_name proj ty in
      make_branch ~mem:{ mem with heap } ~rets:[ value ] ()
  | _ -> Fmt.failwith "Invalid arguments for get_value"

let execute_prod_value mem args =
  let { heap; tyenv; _ } = mem in
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = projections_of_expr proj in
      let+ new_heap = Heap.prod_value ~tyenv heap loc_name proj ty value in
      { mem with heap = new_heap }
  | _ -> Fmt.failwith "Invalid arguments for set_value"

let formula_of_expr_exn expr =
  match Formula.lift_logic_expr expr with
  | Some (f, _) -> f
  | None -> failwith "Invalid formula in observation"

let execute_cons_observation mem args =
  match args with
  | [ formula_expr ] ->
      let formula = formula_of_expr_exn formula_expr in
      let++ () = Obs_ctx.cons_observation mem.obs_ctx formula in
      make_branch ~mem ()
  | _ -> Fmt.failwith "Invalid arguments for get_observation"

let execute_prod_observation mem args =
  match args with
  | [ formula ] ->
      let formula = formula_of_expr_exn formula in
      let+ new_obs = Obs_ctx.prod_observation mem.obs_ctx formula in
      { mem with obs_ctx = new_obs }
  | _ -> Fmt.failwith "Invalid arguments for set_observation"

(* Observations are persistent *)
let is_overlapping_asrt _ = false
let copy t = t

let pp ft t =
  Fmt.pf ft "@[<v 2>Heap:@,%a@]@ @[<v 2>Lifetimes:@,%a@]@ %a" Heap.pp t.heap
    Lft_ctx.pp t.lfts Prophecies.pp t.pcies

let pp_by_need _ _ = failwith "pp_by_need: Not yet implemented"
let get_print_info _ _ = failwith "get_print_info: Not yet implemented"
let clean_up ?keep:_ _ = failwith "clean_up: Not yet implemented"

let lvars t =
  let open Utils.Containers in
  Prophecies.lvars t.pcies
  |> SS.union (Heap.lvars t.heap)
  |> SS.union (Lft_ctx.lvars t.lfts)
  |> SS.union (Obs_ctx.lvars t.obs_ctx)

let alocs _ = failwith "alocs: Not yet implemented"

let assertions ?to_keep:_ { heap; tyenv; lfts; pcies; obs_ctx } =
  Obs_ctx.assertions obs_ctx
  @ Prophecies.assertions ~tyenv pcies
  @ Lft_ctx.assertions lfts
  @ Heap.assertions ~tyenv heap

let mem_constraints _ =
  Logging.normal (fun m -> m "WARNING: MEM_CONSTRAINTS\n@?");
  []

let pp_c_fix _ _ = failwith "pp_c_fix: Not yet implemented"
let pp_err ft t = Err.pp ft t

let get_failing_constraint _ =
  failwith "get_failing_constraints: Not yet implemented"

let get_fixes _ _ _ = failwith "get_fixes: Not yet implemented"
let apply_fix _ _ = failwith "apply_fix: Not yet implemented"
let get_recovery_tactic _ e = Err.recovery_tactic e

let execute_cons_lft mem args =
  let open Gillian.Utils.Syntaxes.Result in
  match args with
  | [ lft_expr ] ->
      let branch =
        let lft = Lft.of_expr lft_expr in
        let+ res, lfts = Lft_ctx.cons mem.lfts lft in
        make_branch ~mem:{ mem with lfts } ~rets:[ Expr.bool res ] ()
      in
      Delayed.return branch
  | _ -> Fmt.failwith "Invalid arguments for get_alive_lft"

let execute_prod_lft mem args =
  match args with
  | [ lft; Expr.Lit (Bool status) ] -> (
      let lft = Lft.of_expr lft in
      match Lft_ctx.produce mem.lfts lft status with
      | Some lfts -> Delayed.return { mem with lfts }
      | None -> Delayed.vanish ())
  | _ -> Fmt.failwith "Invalid arguments for new_lft"

let execute_cons_value_observer mem args =
  let { pcies; tyenv; _ } = mem in
  match args with
  | [ pcy_id; proj_exp; ty_exp ] ->
      let** pcy_id = resolve_loc_result pcy_id in
      let ty = Ty.of_expr ty_exp in
      let* proj = projections_of_expr proj_exp in
      let++ value, pcies =
        Prophecies.cons_value_obs ~tyenv pcies pcy_id proj ty
      in
      make_branch ~mem:{ mem with pcies } ~rets:[ value ] ()
  | _ -> Fmt.failwith "Invalid arguments for get_value_observer"

let execute_prod_value_observer mem args =
  let { pcies; tyenv; _ } = mem in
  match args with
  | [ pcy_id; proj; ty; value ] ->
      let* pcy_id = resolve_or_create_loc_name pcy_id in
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let+ new_pcies =
        Prophecies.prod_value_obs ~tyenv pcies pcy_id proj ty value
      in
      { mem with pcies = new_pcies }
  | _ -> Fmt.failwith "Invalid arguments for set_value_observer"

let execute_cons_pcy_controller mem args =
  let { pcies; tyenv; _ } = mem in
  match args with
  | [ pcy_id; proj_exp; ty_exp ] ->
      let** pcy_id = resolve_loc_result pcy_id in
      let ty = Ty.of_expr ty_exp in
      let* proj = projections_of_expr proj_exp in
      let++ value, pcies =
        Prophecies.cons_controller ~tyenv pcies pcy_id proj ty
      in
      make_branch ~mem:{ mem with pcies } ~rets:[ value ] ()
  | _ -> Fmt.failwith "Invalid arguments for get_pcy_controller"

let execute_prod_pcy_controller mem args =
  let { pcies; tyenv; _ } = mem in
  match args with
  | [ pcy_id; proj; ty; value ] ->
      let* pcy_id = resolve_or_create_loc_name pcy_id in
      let ty = Ty.of_expr ty in
      let* proj = projections_of_expr proj in
      let+ new_pcies =
        Prophecies.prod_controller ~tyenv pcies pcy_id proj ty value
      in
      { mem with pcies = new_pcies }
  | _ -> Fmt.failwith "Invalid arguments for set_pcy_controller"

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
  let { pcies; tyenv; _ } = mem in
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

let execute_cons_pcy_value mem args =
  match args with
  | [ pcy_id; proj_expr; ty_expr ] ->
      let* proj = projections_of_expr proj_expr in
      let++ pcy_id = resolve_loc_result pcy_id in
      let ty = Ty.of_expr ty_expr in
      let ret, new_pcies =
        Prophecies.cons_value ~tyenv:mem.tyenv mem.pcies pcy_id proj ty
      in
      make_branch ~mem:{ mem with pcies = new_pcies } ~rets:[ ret ] ()
  | _ -> Fmt.failwith "Invalid arguments for pcy_get_value"

let execute_prod_pcy_value mem args =
  match args with
  | [ pcy_id; proj_expr; ty_expr; value ] ->
      let* pcy_id = resolve_or_create_loc_name pcy_id in
      let* proj = projections_of_expr proj_expr in
      let ty = Ty.of_expr ty_expr in
      let+ pcies =
        Prophecies.prod_value ~tyenv:mem.tyenv mem.pcies pcy_id proj ty value
      in
      { mem with pcies }
  | _ -> Fmt.failwith "Invalid arguments for pcy_set_value"

let pp_branch fmt branch =
  let _, values = branch in
  Fmt.pf fmt "Returns: %a@.(Ignoring heap)" (Fmt.Dump.list Expr.pp) values

let consume ~core_pred mem args =
  Logging.verbose (fun m -> m "Executing consumer for %s" core_pred);
  let+ res =
    let core_pred = Actions.cp_of_name core_pred in
    match core_pred with
    | Value -> execute_cons_value mem args
    | Lft -> execute_cons_lft mem args
    | Pcy_value -> execute_cons_pcy_value mem args
    | Pcy_controller -> execute_cons_pcy_controller mem args
    | Value_observer -> execute_cons_value_observer mem args
    | Observation -> execute_cons_observation mem args
    | Freed -> Fmt.failwith "Unimplemented: Consume Freed"
  in
  Logging.verbose (fun m ->
      m "Resulting in: %a" (Fmt.Dump.result ~ok:pp_branch ~error:Err.pp) res);
  res

let produce ~core_pred mem args =
  Logging.verbose (fun m -> m "Executing producer for %s" core_pred);
  let+ res =
    let core_pred = Actions.cp_of_name core_pred in
    match core_pred with
    | Value -> execute_prod_value mem args
    | Lft -> execute_prod_lft mem args
    | Pcy_value -> execute_prod_pcy_value mem args
    | Pcy_controller -> execute_prod_pcy_controller mem args
    | Value_observer -> execute_prod_value_observer mem args
    | Observation -> execute_prod_observation mem args
    | Freed -> Fmt.failwith "Unimplemented: Produce Freed"
  in
  Logging.verbose (fun m -> m "Resulting in: %a" pp res);
  res

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

let can_fix = function
  | Err.MissingBlock _
  | Missing_pcy _
  | Missing_lifetime _
  | Missing_proj _
  | Missing_observation _
  | Invalid_loc _ -> true
  | _ -> false

let split_partially_missing_value ~tyenv ins _loc missing_proj =
  let iloc, iproj, _ity =
    match ins with
    | [ iloc; iproj; ity ] -> (iloc, iproj, ity)
    | _ -> failwith "Invalid insertions for split_partially_missing_value"
  in
  let iproj = Projections.of_expr iproj in
  let rest = Projections.split_extension iproj missing_proj in
  (* For now we also only handle structure/tuple fields.
     It doesn't mean we can't handle more, we just implement by need.
     We'll very probably need Index for Vec! *)
  let op_on_ty =
    match rest with
    | [ Field (_, ty) ] -> ty
    | _ ->
        failwith "Unhandled (yet): more than one op or not a field in splitting"
  in
  let fields = Ty.fields ~tyenv op_on_ty in
  let new_ins =
    List.mapi
      (fun i field ->
        let proj =
          Projections.add_ops iproj [ Field (i, op_on_ty) ]
          |> Projections.to_expr
        in
        [ iloc; proj; Ty.to_expr field ])
      fields
  in
  let learn_out =
    Expr.EList
      (List.init (List.length fields) (fun i -> Expr.PVar (Fmt.str "%d:0" i)))
  in
  (new_ins, [ learn_out ])

let split_further mem core_pred ins (err : Err.t) =
  match (Actions.cp_of_name core_pred, err) with
  | Value, Missing_proj (loc, missing_proj, Partially) ->
      (* We tried consuming a tree when we had some of it but not all,
         this is precisely what we are trying to signal. *)
      let res =
        split_partially_missing_value ~tyenv:mem.tyenv ins loc missing_proj
      in
      Logging.verbose (fun m ->
          m "SUCCESSFULY SPLIT:@\nNEW INS: %a@\nNEW OUTs: %a"
            Fmt.(Dump.list @@ Dump.list Expr.pp)
            (fst res)
            Fmt.(Dump.list Expr.pp)
            (snd res));
      Some (split_partially_missing_value ~tyenv:mem.tyenv ins loc missing_proj)
  | _ -> None
