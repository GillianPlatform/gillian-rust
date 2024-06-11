open Monadic
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
open Heap
open Gil_syntax
open Delayed_utils

type prophecy = {
  value : Expr.t;
  observer : Expr.t option;
  controller : Expr.t option;
}

let prophecy_lvars prophecy =
  let open Utils.Containers in
  Expr.lvars prophecy.value
  |> SS.union (Option.fold ~none:SS.empty ~some:Expr.lvars prophecy.observer)
  |> SS.union (Option.fold ~none:SS.empty ~some:Expr.lvars prophecy.controller)

let pp_prophecy =
  let open Fmt in
  Fmt.braces
  @@ record ~sep:semi
       [
         field "value" (fun x -> x.value) Expr.pp;
         field "observer" (fun x -> x.observer) (Fmt.Dump.option Expr.pp);
         field "controller" (fun x -> x.controller) (Fmt.Dump.option Expr.pp);
       ]

type t = prophecy MemMap.t

let sure_is_nonempty =
  MemMap.exists (fun _ { observer; controller; _ } ->
      Option.is_some observer || Option.is_some controller)

let assertions (pcies : t) =
  let cps loc pcy =
    (* Location and ty are uniform *)
    let loc = Expr.loc_from_loc_name loc in
    (* The future value of the prophecy variable *)
    let value =
      let cp = Actions.cp_to_name Pcy_value in
      Asrt.GA (cp, [ loc ], [ pcy.value ])
    in
    let controller =
      match pcy.controller with
      | None -> []
      | Some v ->
          let cp = Actions.cp_to_name Pcy_controller in
          [ Asrt.GA (cp, [ loc ], [ v ]) ]
    in
    let observer =
      match pcy.observer with
      | None -> []
      | Some v ->
          let cp = Actions.cp_to_name Value_observer in
          [ Asrt.GA (cp, [ loc ], [ v ]) ]
    in
    value :: (controller @ observer)
  in
  MemMap.fold (fun loc pcy acc -> cps loc pcy @ acc) pcies []

let lvars t =
  let open Utils.Containers in
  MemMap.fold (fun _ pcy acc -> SS.union acc (prophecy_lvars pcy)) t SS.empty

let empty = MemMap.empty
let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let merge old_proph new_proph =
  let open Formula.Infix in
  let value_eq = old_proph.value #== new_proph.value in
  let controller =
    if Option.is_some new_proph.controller then new_proph.controller
    else old_proph.controller
  in
  let observer =
    if Option.is_some new_proph.observer then new_proph.observer
    else old_proph.observer
  in
  let ct_obs_eq =
    match (controller, observer) with
    | Some c, Some o -> [ c #== o ]
    | _ -> []
  in
  let learned = value_eq :: ct_obs_eq in
  DR.ok ~learned { value = new_proph.value; observer; controller }

let with_observer_block pcy_id pcy_env f =
  let open DR.Syntax in
  match MemMap.find_opt pcy_id pcy_env with
  | Some pcy ->
      let++ value, new_observer = f pcy.observer in
      let new_pcymap =
        MemMap.add pcy_id { pcy with observer = new_observer } pcy_env
      in
      (value, new_pcymap)
  | None -> DR.error (Err.Missing_pcy pcy_id)

let with_controller_block pcy_id pcy_env f =
  let open DR.Syntax in
  match MemMap.find_opt pcy_id pcy_env with
  | Some pcy ->
      let++ value, new_controller = f pcy.controller in
      let new_pcymap =
        MemMap.add pcy_id { pcy with controller = new_controller } pcy_env
      in
      (value, new_pcymap)
  | None -> DR.error (Err.Missing_pcy pcy_id)

let cons_value_obs pcy_env pcy_var =
  with_observer_block pcy_var pcy_env @@ function
  | Some obs -> DR.ok (obs, None)
  | None -> DR.error (Err.Missing_observer pcy_var)

let prod_value_obs pcy_env pcy_id obs_value =
  let+ new_block =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { observer = Some _; _ } -> Delayed.vanish ()
    | Some { value; observer = None; controller = Some ctl } ->
        let learned = [ Formula.Infix.( #== ) obs_value ctl ] in
        Delayed.return ~learned
          { value; observer = Some obs_value; controller = Some ctl }
    | Some { value; observer = None; controller = None } ->
        Delayed.return { value; observer = Some obs_value; controller = None }
    | None ->
        Delayed.return
          {
            value = Expr.LVar (LVar.alloc ());
            observer = Some obs_value;
            controller = None;
          }
  in
  MemMap.add pcy_id new_block pcy_env

let cons_controller pcy_env pcy_var =
  with_controller_block pcy_var pcy_env @@ function
  | Some ctl -> DR.ok (ctl, None)
  | None -> DR.error (Err.Missing_controller pcy_var)

let prod_controller pcy_env pcy_id ctl_value =
  let+ new_block =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { controller = Some _; _ } -> Delayed.vanish ()
    | Some { value; observer = Some obs_value; controller = None } ->
        let learned = [ Formula.Infix.( #== ) obs_value ctl_value ] in
        Delayed.return ~learned
          { value; observer = Some obs_value; controller = Some ctl_value }
    | Some { value; observer = None; controller = None } ->
        Delayed.return { value; controller = Some ctl_value; observer = None }
    | None ->
        Delayed.return
          {
            value = Expr.LVar (LVar.alloc ());
            controller = Some ctl_value;
            observer = None;
          }
  in
  MemMap.add pcy_id new_block pcy_env

let cons_value pcy_env pcy_id =
  match MemMap.find_opt pcy_id pcy_env with
  | Some { value; _ } -> (value, pcy_env)
  | None ->
      let value = Expr.LVar (LVar.alloc ()) in
      ( value,
        MemMap.add pcy_id { value; observer = None; controller = None } pcy_env
      )

let prod_value pcy_env pcy_id new_value =
  match MemMap.find_opt pcy_id pcy_env with
  | Some pcy ->
      Delayed.return
        ~learned:[ Formula.Infix.( #== ) pcy.value new_value ]
        pcy_env
  | None ->
      let block = { value = new_value; observer = None; controller = None } in
      Delayed.return (MemMap.add pcy_id block pcy_env)

let resolve obs_ctx pcy_env pcy_var =
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { controller = None; _ } -> DR.error (Err.Missing_controller pcy_var)
  | Some { observer = None; _ } -> DR.error (Err.Missing_observer pcy_var)
  | Some { value; controller = Some ctl; observer = Some _obs } ->
      (* Learning equality with controller is sufficient,
         since controller must already be equal to observer *)
      let* obs_ctx =
        Obs_ctx.prod_observation obs_ctx (Formula.Infix.( #== ) value ctl)
      in
      let new_pcies =
        MemMap.add pcy_var { value; controller = None; observer = None } pcy_env
      in
      DR.ok (new_pcies, obs_ctx)

let assign pcy_env pcy_var assigned =
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { controller = None; _ } -> DR.error (Err.Missing_controller pcy_var)
  | Some { observer = None; _ } -> DR.error (Err.Missing_observer pcy_var)
  | Some { value; controller = Some _; observer = Some _ } ->
      (* We need both and need to write in both the controller and observer at once *)
      let new_pcies =
        MemMap.add pcy_var
          { value; controller = Some assigned; observer = Some assigned }
          pcy_env
      in
      DR.ok new_pcies

let alloc pcy_env =
  let pcy_id = ALoc.alloc () in
  let pcy_value = Expr.LVar (LVar.alloc ()) in
  let obs_ctl_value = Expr.LVar (LVar.alloc ()) in
  let block =
    {
      value = pcy_value;
      observer = Some obs_ctl_value;
      controller = Some obs_ctl_value;
    }
  in
  let updated_env = MemMap.add pcy_id block pcy_env in
  (Expr.ALoc pcy_id, updated_env)

let pp ft t =
  let open Fmt in
  pf ft "@[<v 2>Prophecies:@,%a@]"
    (iter_bindings MemMap.iter (pair ~sep:(any " -> ") string pp_prophecy))
    t

let substitution pcy_env subst =
  let open Gillian.Symbolic in
  if Subst.is_empty subst then DR.ok pcy_env
  else
    let loc_subst =
      Subst.fold subst
        (fun l r acc ->
          match l with
          | ALoc loc | Lit (Loc loc) -> (loc, r) :: acc
          | _ -> acc)
        []
    in
    let subst_expr = Subst.subst_in_expr subst ~partial:true in
    let values_substed =
      MemMap.map
        (fun block ->
          let value = subst_expr block.value in
          let controller = Option.map subst_expr block.controller in
          let observer = Option.map subst_expr block.observer in
          { value; controller; observer })
        pcy_env
    in
    List.fold_left
      (fun acc (old_loc, new_loc) ->
        let** acc = acc in
        let new_loc =
          match new_loc with
          | Expr.Lit (Loc loc) | ALoc loc -> loc
          | _ ->
              Fmt.failwith
                "substitution failed, for location, target isn't a location"
        in
        match (MemMap.find_opt old_loc acc, MemMap.find_opt new_loc acc) with
        | None, None | None, Some _ -> DR.ok acc
        | Some prophecy, None ->
            MemMap.remove old_loc acc |> MemMap.add new_loc prophecy |> DR.ok
        | Some old_prophecy, Some new_prophecy ->
            let++ merged = merge old_prophecy new_prophecy in
            MemMap.remove old_loc acc |> MemMap.add new_loc merged)
      (DR.ok values_substed) loc_subst
