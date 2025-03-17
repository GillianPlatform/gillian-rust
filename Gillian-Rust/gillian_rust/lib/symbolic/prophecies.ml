open Monadic
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
open Heap
open Gil_syntax
open Delayed_utils

type prophecy = {
  value : Expr.t;
  obs_ctl : Expr.t;
  observer : bool;
  controller : bool;
}

let prophecy_lvars prophecy =
  let open Utils.Containers in
  SS.union (Expr.lvars prophecy.obs_ctl) (Expr.lvars prophecy.value)

let pp_prophecy =
  let open Fmt in
  Fmt.braces
  @@ record ~sep:semi
       [
         field "value" (fun x -> x.value) Expr.pp;
         field "obs_ctl" (fun x -> x.obs_ctl) Expr.pp;
         field "observer" (fun x -> x.observer) Fmt.bool;
         field "controller" (fun x -> x.controller) Fmt.bool;
       ]

type t = prophecy MemMap.t

let sure_is_nonempty =
  MemMap.exists (fun _ { observer; controller; _ } -> observer || controller)

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
      | false -> []
      | true ->
          let cp = Actions.cp_to_name Pcy_controller in
          [ Asrt.GA (cp, [ loc ], [ pcy.obs_ctl ]) ]
    in
    let observer =
      match pcy.observer with
      | false -> []
      | true ->
          let cp = Actions.cp_to_name Value_observer in
          [ Asrt.GA (cp, [ loc ], [ pcy.obs_ctl ]) ]
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

let cons_value_obs pcy_env pcy_var =
  match MemMap.find_opt pcy_var pcy_env with
  | Some ({ observer = true; obs_ctl; _ } as pcy) ->
      (* We consume the pcy *)
      let new_pcy_env =
        MemMap.add pcy_var { pcy with observer = false } pcy_env
      in
      DR.ok (obs_ctl, new_pcy_env)
  | Some { observer = false; _ } -> DR.error (Err.Missing_observer pcy_var)
  | None -> DR.error (Err.Missing_pcy pcy_var)

let prod_value_obs pcy_env pcy_id obs_value =
  let+ new_block =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { observer = true; _ } -> Delayed.vanish () (* Duplicated resource *)
    | Some { value; obs_ctl; observer = false; controller = true } ->
        (* We already have a controller, we learn equality *)
        let learned = [ Formula.Infix.( #== ) obs_value obs_ctl ] in
        Delayed.return ~learned
          { value; observer = true; controller = true; obs_ctl }
    | Some { value; observer = false; controller = false; obs_ctl = _ } ->
        (* We have neither the controller nor the observer, the obs_ctl value is irrelevant *)
        Delayed.return
          { value; observer = true; controller = false; obs_ctl = obs_value }
    | None ->
        Delayed.return
          {
            value = Expr.LVar (LVar.alloc ());
            obs_ctl = obs_value;
            observer = true;
            controller = false;
          }
  in
  MemMap.add pcy_id new_block pcy_env

let cons_controller pcy_env pcy_var =
  match MemMap.find_opt pcy_var pcy_env with
  | Some ({ controller = true; obs_ctl; _ } as pcy) ->
      (* We consume the pcy *)
      let new_pcy_env =
        MemMap.add pcy_var { pcy with controller = false } pcy_env
      in
      DR.ok (obs_ctl, new_pcy_env)
  | Some { controller = false; _ } -> DR.error (Err.Missing_controller pcy_var)
  | None -> DR.error (Err.Missing_pcy pcy_var)

let prod_controller pcy_env pcy_id ctl_value =
  let+ new_block =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { controller = true; _ } ->
        Delayed.vanish () (* Duplicated resource *)
    | Some { value; obs_ctl; observer = true; controller = false } ->
        (* We already have an observer, we learn equality *)
        let learned = [ Formula.Infix.( #== ) ctl_value obs_ctl ] in
        Delayed.return ~learned
          { value; observer = true; controller = true; obs_ctl }
    | Some { value; observer = false; controller = false; obs_ctl = _ } ->
        (* We have neither the controller nor the observer, the obs_ctl value is irrelevant *)
        Delayed.return
          { value; observer = false; controller = true; obs_ctl = ctl_value }
    | None ->
        Delayed.return
          {
            value = Expr.LVar (LVar.alloc ());
            obs_ctl = ctl_value;
            observer = false;
            controller = true;
          }
  in
  MemMap.add pcy_id new_block pcy_env

let cons_value pcy_env pcy_id =
  (* The value is persistent information, it doesn't get consumed *)
  match MemMap.find_opt pcy_id pcy_env with
  | Some { value; _ } -> (value, pcy_env)
  | None ->
      (* If not there, we simply create it, and now we know its value. *)
      let value = Expr.LVar (LVar.alloc ()) in
      ( value,
        MemMap.add pcy_id
          {
            value;
            observer = false;
            controller = false;
            obs_ctl = Expr.Lit Null;
            (* The obs_ctl we assign is irrelevant, since we have neither observer nor controller *)
          }
          pcy_env )

let prod_value pcy_env pcy_id new_value =
  match MemMap.find_opt pcy_id pcy_env with
  | Some pcy ->
      (* `value` is a function, so if we already know its value, we now that whatever we have is equal *)
      Delayed.return
        ~learned:[ Formula.Infix.( #== ) pcy.value new_value ]
        pcy_env
  | None ->
      (* The obs_ctl we assign is irrelevant, since we have neither observer nor controller *)
      let block =
        {
          value = new_value;
          observer = false;
          controller = false;
          obs_ctl = Expr.Lit Null;
        }
      in
      Delayed.return (MemMap.add pcy_id block pcy_env)

let assign pcy_env pcy_var assigned =
  (* In order to assign an obs_ctl value, we need *both* the controller and observer at the same time. *)
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { controller = false; _ } -> DR.error (Err.Missing_controller pcy_var)
  | Some { observer = false; _ } -> DR.error (Err.Missing_observer pcy_var)
  | Some ({ controller = true; observer = true; _ } as pcy) ->
      let new_pcies =
        MemMap.add pcy_var { pcy with obs_ctl = assigned } pcy_env
      in
      DR.ok new_pcies

let alloc pcy_env =
  let pcy_id = ALoc.alloc () in
  let value = Expr.LVar (LVar.alloc ()) in
  let obs_ctl = Expr.LVar (LVar.alloc ()) in
  let block = { value; obs_ctl; observer = true; controller = true } in
  let updated_env = MemMap.add pcy_id block pcy_env in
  (Expr.ALoc pcy_id, updated_env)

let pp ft t =
  let open Fmt in
  pf ft "@[<v 2>Prophecies:@,%a@]"
    (iter_bindings MemMap.iter (pair ~sep:(any " -> ") string pp_prophecy))
    t

let merge old_proph new_proph =
  let open Formula.Infix in
  let value_eq = old_proph.value #== new_proph.value in
  let controller = new_proph.controller || old_proph.controller in
  let observer = new_proph.observer || old_proph.observer in
  let obs_ctl, ctl_obs_eq =
    match
      ( old_proph.controller || old_proph.observer,
        new_proph.controller || new_proph.observer )
    with
    | true, true ->
        (* Both obs_ctl are relevant *)
        let ctl_obs_eq = [ old_proph.obs_ctl #== new_proph.obs_ctl ] in
        (new_proph.obs_ctl, ctl_obs_eq)
    | true, false ->
        (* Only old obs_ctl is relevant *)
        (old_proph.obs_ctl, [])
    | false, true ->
        (* Only new obs_ctl is relevant *)
        (new_proph.obs_ctl, [])
    | false, false ->
        (* Both obs_ctl are irrelevant *)
        (Expr.Lit Null, [])
  in
  let learned = value_eq :: ctl_obs_eq in
  DR.ok ~learned { value = new_proph.value; obs_ctl; observer; controller }

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
          let obs_ctl = subst_expr block.obs_ctl in
          let controller = block.controller in
          let observer = block.observer in
          { value; obs_ctl; controller; observer })
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
