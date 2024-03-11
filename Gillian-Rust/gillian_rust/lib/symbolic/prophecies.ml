open Monadic
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
open Heap
open Gil_syntax
open Delayed_utils

(* TODO: massively simplify! *)

type prophecy = {
  value : Expr.t;
  observer : TreeBlock.outer;
  controller : TreeBlock.outer;
}

let prophecy_lvars prophecy =
  let open Utils.Containers in
  Expr.lvars prophecy.value
  |> SS.union (TreeBlock.outer_lvars prophecy.observer)
  |> SS.union (TreeBlock.outer_lvars prophecy.controller)

let pp_prophecy =
  let open Fmt in
  Fmt.braces
  @@ record ~sep:semi
       [
         field "value" (fun x -> x.value) Expr.pp;
         field "observer" (fun x -> x.observer) TreeBlock.pp_outer;
         field "controller" (fun x -> x.controller) TreeBlock.pp_outer;
       ]

type t = prophecy MemMap.t

let sure_is_nonempty =
  MemMap.exists (fun _ { observer; controller; _ } ->
      (not @@ TreeBlock.outer_is_empty observer)
      || (not @@ TreeBlock.outer_is_empty controller))

let assertions ~tyenv:_ (pcies : t) =
  let cps loc pcy =
    (* Location and ty are uniform *)
    let loc = Expr.loc_from_loc_name loc in
    let ty = Ty.to_expr pcy.controller.root.ty in
    (* The future value of the prophecy variable *)
    let value =
      let cp = Actions.cp_to_name Pcy_value in
      Asrt.GA (cp, [ loc; Expr.EList []; ty ], [ pcy.value ])
    in
    (* Contructor for controller and observer which share logic *)
    let build_obs_ctrl cp (outer : TreeBlock.outer) =
      if TreeBlock.totally_missing outer.root then None
      else if TreeBlock.partially_missing outer.root then
        failwith "Prophecy controller/observers should not be partially missing"
      else
        let value = TreeBlock.to_rust_value_exn outer.root in
        let offset = outer.offset in
        Some (Asrt.GA (cp, [ loc; offset; ty ], [ value ]))
    in
    let controller =
      let cp = Actions.cp_to_name Pcy_controller in
      build_obs_ctrl cp pcy.controller
    in
    let observer =
      let cp = Actions.cp_to_name Value_observer in
      build_obs_ctrl cp pcy.observer
    in
    (value, controller, observer)
  in
  MemMap.fold
    (fun loc pcy acc ->
      let value, controller, observer = cps loc pcy in
      (value :: Option.to_list controller) @ Option.to_list observer @ acc)
    pcies []

let lvars t =
  let open Utils.Containers in
  MemMap.fold (fun _ pcy acc -> SS.union acc (prophecy_lvars pcy)) t SS.empty

let empty = MemMap.empty
let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let merge old_proph new_proph =
  let value_eq = Formula.Infix.( #== ) old_proph.value new_proph.value in
  let* observer = TreeBlock.merge_outer old_proph.observer new_proph.observer in
  let* controller =
    TreeBlock.merge_outer old_proph.controller new_proph.controller
  in
  let ct_obs_eq = TreeBlock.outer_equality_constraint observer controller in
  let learned = value_eq :: ct_obs_eq in
  DR.ok ~learned { value = old_proph.value; observer; controller }

let with_observer_block pcy_id pcy_env f =
  let open DR.Syntax in
  match MemMap.find_opt pcy_id pcy_env with
  | Some pcy ->
      let++ (value, new_observer), lk = f pcy.observer in
      let new_pcymap =
        MemMap.add pcy_id { pcy with observer = new_observer } pcy_env
      in
      (value, new_pcymap, lk)
  | None -> DR.error (Err.Missing_pcy pcy_id)

let with_controller_block pcy_id pcy_env f =
  let open DR.Syntax in
  match MemMap.find_opt pcy_id pcy_env with
  | Some pcy ->
      let++ (value, new_controller), lk = f pcy.controller in
      let new_pcymap =
        MemMap.add pcy_id { pcy with controller = new_controller } pcy_env
      in
      (value, new_pcymap, lk)
  | None -> DR.error (Err.Missing_pcy pcy_id)

let cons_value_obs ~tyenv ~lk pcy_env pcy_var proj ty =
  with_observer_block pcy_var pcy_env @@ fun observer ->
  TreeBlock.cons_proj ~loc:pcy_var ~tyenv ~lk observer proj ty

let prod_value_obs ~tyenv ~lk pcy_env pcy_id (proj : Projections.t) ty obs_value
    =
  let missing_root () =
    TreeBlock.outer_missing
      ~offset:(Option.value ~default:(Expr.EList []) proj.base)
      ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let value, observer, controller =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { value; observer; controller } -> (value, observer, controller)
    | None -> (Expr.LVar (LVar.alloc ()), missing_root (), missing_root ())
  in
  let* observer, lk =
    TreeBlock.prod_proj ~tyenv ~lk observer proj ty obs_value
  in
  Delayed.return
    ~learned:(TreeBlock.outer_equality_constraint observer controller)
    (MemMap.add pcy_id { value; observer; controller } pcy_env, lk)

let cons_controller ~tyenv ~lk pcy_env pcy_var proj ty =
  with_controller_block pcy_var pcy_env @@ fun controller ->
  (* FIXME: This might not raise the right error.
     We need to pass what kind of error should be created.
     Of course, this is still sound, but risk triggering the wrong automations. *)
  TreeBlock.cons_proj ~loc:pcy_var ~tyenv ~lk controller proj ty

let prod_controller
    ~tyenv
    ~lk
    pcy_env
    pcy_id
    (proj : Projections.t)
    ty
    ctrl_value =
  let missing_root () =
    TreeBlock.outer_missing
      ~offset:(Option.value ~default:(Expr.EList []) proj.base)
      ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let value, observer, controller =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { value; observer; controller } -> (value, observer, controller)
    | None -> (Expr.LVar (LVar.alloc ()), missing_root (), missing_root ())
  in
  let* controller, lk =
    TreeBlock.prod_proj ~tyenv ~lk controller proj ty ctrl_value
  in
  Delayed.return
    ~learned:(TreeBlock.outer_equality_constraint observer controller)
    (MemMap.add pcy_id { value; observer; controller } pcy_env, lk)

let proj_on_var pcy_var (proj : Projections.t) =
  let () =
    match proj.base with
    | Some _ -> failwith "projections on prophecies have to be None"
    | None -> ()
  in
  let apply_op e = function
    | Projections.Field (i, _) -> Expr.list_nth e i
    | Index (i, _, _) -> Expr.list_nth_e e i
    | VField (i, _, _) -> Expr.list_nth (Expr.list_nth e 0) i
    | _ ->
        failwith
          "proj_on_var: projections on variables have to be field or index \
           access"
  in
  List.fold_left apply_op pcy_var proj.from_base

let cons_value ~tyenv pcy_env pcy_id (proj : Projections.t) ty =
  (* Value is persistent, consuming doesn't remove from the map *)
  let missing_root () =
    TreeBlock.outer_missing
      ~offset:(Option.value ~default:(Expr.EList []) proj.base)
      ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  match MemMap.find_opt pcy_id pcy_env with
  | Some { value; _ } -> (value, pcy_env)
  | None ->
      let value = Expr.LVar (LVar.alloc ()) in
      let controller = missing_root () in
      let observer = missing_root () in
      let projected_value = proj_on_var value proj in
      ( projected_value,
        MemMap.add pcy_id { value; observer; controller } pcy_env )

let prod_value ~tyenv pcy_env pcy_id (proj : Projections.t) ty new_value =
  let missing_root () =
    TreeBlock.outer_missing
      ~offset:(Option.value ~default:(Expr.EList []) proj.base)
      ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let value, observer, controller =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { value; observer; controller } -> (value, observer, controller)
    | None -> (Expr.LVar (LVar.alloc ()), missing_root (), missing_root ())
  in
  let learned =
    let open Formula.Infix in
    [ (proj_on_var value proj) #== new_value ]
  in
  Delayed.return ~learned
    (MemMap.add pcy_id { value; observer; controller } pcy_env)

let resolve ~tyenv ~lk pcy_env pcy_var (proj : Projections.t) ty =
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { value; controller; observer } ->
      let open TreeBlock in
      (* Reading from the controller is a way of ensuring we have the part we require.
         An invariant is that the values of the controller and the resolver have to coincide *)
      let** (current_value, _), lk =
        load_proj ~loc:pcy_var ~tyenv ~lk controller proj ty true
      in
      let** (_, observer), lk =
        cons_proj ~loc:pcy_var ~tyenv ~lk observer proj ty
      in
      let learned =
        let open Formula.Infix in
        [ (proj_on_var value proj) #== current_value ]
      in
      let new_pcies =
        MemMap.add pcy_var { value; controller; observer } pcy_env
      in
      DR.ok ~learned (new_pcies, lk)

let assign ~tyenv ~lk pcy_env pcy_var (proj : Projections.t) ty assigned =
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { value; controller; observer } ->
      let open TreeBlock in
      (* We need both and need to write in both the controller and observer at once *)
      let** controller, lk =
        store_proj ~loc:pcy_var ~tyenv ~lk controller proj ty assigned
      in
      let** observer, lk =
        store_proj ~loc:pcy_var ~tyenv ~lk observer proj ty assigned
      in
      let new_pcies =
        MemMap.add pcy_var { value; controller; observer } pcy_env
      in
      DR.ok (new_pcies, lk)

let alloc ~tyenv pcy_env ty =
  let pcy_id = ALoc.alloc () in
  let value = Expr.LVar (LVar.alloc ()) in
  let new_block =
    let current_value = Expr.LVar (LVar.alloc ()) in
    let controller =
      TreeBlock.outer_symbolic ~tyenv ~offset:(Expr.EList []) ty current_value
    in
    let observer = controller in
    { controller; observer; value }
  in
  let updated_env = MemMap.add pcy_id new_block pcy_env in
  ([ Expr.ALoc pcy_id; Expr.EList [] ], updated_env)

let pp ft t =
  let open Fmt in
  pf ft "@[<v 2>Prophecies:@,%a@]"
    (iter_bindings MemMap.iter (pair ~sep:(any " -> ") string pp_prophecy))
    t

let substitution ~tyenv pcy_env subst =
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
    let** new_mapping =
      MemMap.to_seq pcy_env |> List.of_seq
      |> DR_list.map (fun (pcy_id, block) ->
             let value = subst_expr block.value in
             let** controller =
               TreeBlock.outer_substitution ~tyenv ~subst_expr block.controller
             in
             let++ observer =
               TreeBlock.outer_substitution ~tyenv ~subst_expr block.observer
             in
             (pcy_id, { value; controller; observer }))
    in
    let tree_substed = List.to_seq new_mapping |> MemMap.of_seq in
    List.fold_left
      (fun acc (old_loc, new_loc) ->
        let** acc in
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
      (DR.ok tree_substed) loc_subst
