open Monadic
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
open Heap
open Gil_syntax
open Delayed_utils

type prophecy = {
  value : Expr.t;
  observer : TreeBlock.outer;
  controller : TreeBlock.outer;
}

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

let empty = MemMap.empty
let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

(* let MemMap.find_opt  pcy_var pcy_env =
   match MemMap.find_opt pcy_var pcy_env with
   | Some b -> Delayed.return @@ Some (pcy_var, b)
   | None ->
       let rec delayed_find to_find seq =
         match seq () with
         | Seq.Nil -> Delayed.return None
         | Seq.Cons ((key, value), seq) ->
             if%ent Formula.Infix.( #== ) to_find key then
               Delayed.return (Some (key, value))
             else delayed_find to_find seq
       in
       delayed_find pcy_var (MemMap.to_seq pcy_env) *)

let observer_block pcy_id pcy_env =
  match MemMap.find_opt pcy_id pcy_env with
  | Some { observer; _ } -> DR.ok observer
  | _ -> DR.error (Err.Missing_pcy pcy_id)

let controller_block pcy_id pcy_env =
  match MemMap.find_opt pcy_id pcy_env with
  | Some { controller; _ } -> DR.ok controller
  | _ -> DR.error (Err.Missing_pcy pcy_id)

let get_value_obs ~tyenv pcy_env pcy_var proj ty =
  let** observer = observer_block pcy_var pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv observer proj ty false in
  value

let set_value_obs ~tyenv pcy_env pcy_id (proj : Projections.t) ty obs_value =
  let missing_root () =
    TreeBlock.outer_missing ~offset:proj.base ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let value, observer, controller =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { value; observer; controller } -> (value, observer, controller)
    | None -> (Expr.LVar (LVar.alloc ()), missing_root (), missing_root ())
  in
  let** observer = TreeBlock.set_proj ~tyenv observer proj ty obs_value in
  DR.ok
    ~learned:(TreeBlock.outer_equality_constraint observer controller)
    (MemMap.add pcy_id { value; observer; controller } pcy_env)

let rem_value_obs ~tyenv pcy_env pcy_var proj ty =
  (* We must find it, because we returned it through the getter *)
  match MemMap.find_opt pcy_var pcy_env with
  | Some { value; observer; controller } ->
      let++ observer = TreeBlock.rem_proj ~tyenv observer proj ty in
      MemMap.add pcy_var { value; observer; controller } pcy_env
  | None -> failwith "rem_observer: observer is None"

let get_controller ~tyenv pcy_env pcy_var proj ty =
  let** controller = controller_block pcy_var pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv controller proj ty false in
  value

let set_controller ~tyenv pcy_env pcy_id (proj : Projections.t) ty ctrl_value =
  let missing_root () =
    TreeBlock.outer_missing ~offset:proj.base ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let value, observer, controller =
    match MemMap.find_opt pcy_id pcy_env with
    | Some { value; observer; controller } -> (value, observer, controller)
    | None -> (Expr.LVar (LVar.alloc ()), missing_root (), missing_root ())
  in
  let** controller = TreeBlock.set_proj ~tyenv controller proj ty ctrl_value in
  DR.ok
    ~learned:(TreeBlock.outer_equality_constraint observer controller)
    (MemMap.add pcy_id { value; observer; controller } pcy_env)

let rem_controller ~tyenv pcy_env pcy_id proj ty =
  match MemMap.find_opt pcy_id pcy_env with
  | Some { value; observer; controller } ->
      let++ controller = TreeBlock.rem_proj ~tyenv controller proj ty in
      MemMap.add pcy_id { value; observer; controller } pcy_env
  | None -> failwith "rem_observer: observer is None"

let proj_on_var pcy_var (proj : Projections.t) =
  let () =
    match proj.base with
    | Some _ -> failwith "projections on prophecies have to be None"
    | None -> ()
  in
  let apply_op e = function
    | Projections.Field (i, _) | Index (i, _, _) -> Expr.list_nth e i
    | VField (i, _, _) -> Expr.list_nth (Expr.list_nth e 0) i
    | _ ->
        failwith
          "proj_on_var: projections on variables have to be field or index \
           access"
  in
  List.fold_left apply_op pcy_var proj.from_base

let get_value ~tyenv pcy_env pcy_id (proj : Projections.t) ty =
  let missing_root () =
    TreeBlock.outer_missing ~offset:proj.base ~tyenv
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

let set_value ~tyenv pcy_env pcy_id (proj : Projections.t) ty new_value =
  let missing_root () =
    TreeBlock.outer_missing ~offset:proj.base ~tyenv
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
  DR.ok ~learned (MemMap.add pcy_id { value; observer; controller } pcy_env)

let resolve ~tyenv pcy_env pcy_var (proj : Projections.t) ty =
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { value; controller; observer } ->
      let open TreeBlock in
      (* Reading from the controller is a way of ensuring we have the part we require.
         An invariant is that the values of the controller and the resolver have to coincide *)
      let** current_value, _ = get_proj ~tyenv controller proj ty true in
      let** observer = rem_proj ~tyenv observer proj ty in
      let learned =
        let open Formula.Infix in
        [ (proj_on_var value proj) #== current_value ]
      in
      let new_pcies =
        MemMap.add pcy_var { value; controller; observer } pcy_env
      in
      DR.ok ~learned new_pcies

let assign ~tyenv pcy_env pcy_var (proj : Projections.t) ty value =
  match MemMap.find_opt pcy_var pcy_env with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some { value; controller; observer } ->
      let open TreeBlock in
      (* We need both and need to write in both the controller and observer at once *)
      let** controller = store_proj ~tyenv controller proj ty value in
      let** observer = store_proj ~tyenv observer proj ty value in
      let new_pcies =
        MemMap.add pcy_var { value; controller; observer } pcy_env
      in
      DR.ok new_pcies

let alloc ~tyenv pcy_env ty =
  let pcy_id = ALoc.alloc () in
  let value = Expr.LVar (LVar.alloc ()) in
  let new_block =
    let current_value = Expr.LVar (LVar.alloc ()) in
    let controller =
      TreeBlock.outer_symbolic ~tyenv ~offset:None ty current_value
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
  let non_loc = function
    | Expr.ALoc _ | Lit (Loc _) -> false
    | _ -> true
  in
  let () =
    if not (Expr.Set.is_empty (Subst.domain subst (Some non_loc))) then
      Fmt.pr "WARNING: SUBSTITUTION WITH LOCATIONS NO HANDLED\n@?"
  in
  let subst_expr = Subst.subst_in_expr subst ~partial:true in
  let++ new_mapping =
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
  List.to_seq new_mapping |> MemMap.of_seq
