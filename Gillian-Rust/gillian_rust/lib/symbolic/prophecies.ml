open Monadic
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
open Heap
open Gil_syntax
open Delayed_utils
module PcyMap = Expr.Map

type block = { observer : TreeBlock.outer; controller : TreeBlock.outer }

let pp_block =
  let open Fmt in
  Fmt.braces
  @@ record ~sep:semi
       [
         field "observer" (fun x -> x.observer) TreeBlock.pp_outer;
         field "controller" (fun x -> x.controller) TreeBlock.pp_outer;
       ]

type t = block PcyMap.t

let empty = PcyMap.empty
let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let find_opt pcy_var pcy_env =
  match PcyMap.find_opt pcy_var pcy_env with
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
      delayed_find pcy_var (PcyMap.to_seq pcy_env)

let observer_block pcy_var pcy_env =
  let* kv = find_opt pcy_var pcy_env in
  match kv with
  | Some (k, { observer; _ }) -> DR.ok (k, observer)
  | _ -> DR.error (Err.Missing_pcy pcy_var)

let controller_block pcy_var pcy_env =
  let* kv = find_opt pcy_var pcy_env in
  match kv with
  | Some (k, { controller; _ }) -> DR.ok (k, controller)
  | _ -> DR.error (Err.Missing_pcy pcy_var)

let get_value_obs ~tyenv pcy_env pcy_var proj ty =
  let** k, observer = observer_block pcy_var pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv observer proj ty false in
  (k, value)

let set_value_obs ~tyenv pcy_env pcy_var (proj : Projections.t) ty value =
  let missing_root () =
    TreeBlock.outer_missing ~offset:proj.base ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let* pcy_var, observer, controller =
    let+ kv = find_opt pcy_var pcy_env in
    match kv with
    | Some (k, { observer; controller }) -> (k, observer, controller)
    | None -> (pcy_var, missing_root (), missing_root ())
  in
  let** observer = TreeBlock.set_proj ~tyenv observer proj ty value in
  DR.ok
    ~learned:(TreeBlock.outer_equality_constraint observer controller)
    (PcyMap.add pcy_var { observer; controller } pcy_env)

let rem_value_obs ~tyenv pcy_env pcy_var proj ty =
  (* We must find it, because we returned it through the getter *)
  match PcyMap.find_opt pcy_var pcy_env with
  | Some { observer; controller } ->
      let++ observer = TreeBlock.rem_proj ~tyenv observer proj ty in
      if
        TreeBlock.outer_is_empty controller && TreeBlock.outer_is_empty observer
      then PcyMap.remove pcy_var pcy_env
      else PcyMap.add pcy_var { observer; controller } pcy_env
  | None -> failwith "rem_observer: observer is None"

let get_controller ~tyenv pcy_env pcy_var proj ty =
  let** k, controller = controller_block pcy_var pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv controller proj ty false in
  (k, value)

let set_controller ~tyenv pcy_env pcy_var (proj : Projections.t) ty value =
  let missing_root () =
    TreeBlock.outer_missing ~offset:proj.base ~tyenv
      (Projections.base_ty ~leaf_ty:ty proj)
  in
  let* pcy_var, observer, controller =
    let+ kv = find_opt pcy_var pcy_env in
    match kv with
    | Some (k, { observer; controller }) -> (k, observer, controller)
    | None -> (pcy_var, missing_root (), missing_root ())
  in
  let** controller = TreeBlock.set_proj ~tyenv controller proj ty value in
  DR.ok
    ~learned:(TreeBlock.outer_equality_constraint observer controller)
    (PcyMap.add pcy_var { observer; controller } pcy_env)

let rem_controller ~tyenv pcy_env pcy_var proj ty =
  match PcyMap.find_opt pcy_var pcy_env with
  | Some { observer; controller } ->
      let++ controller = TreeBlock.rem_proj ~tyenv controller proj ty in
      if
        TreeBlock.outer_is_empty controller && TreeBlock.outer_is_empty observer
      then PcyMap.remove pcy_var pcy_env
      else PcyMap.add pcy_var { observer; controller } pcy_env
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

let resolve ~tyenv pcy_env pcy_var (proj : Projections.t) ty =
  let* kv = find_opt pcy_var pcy_env in
  match kv with
  | None -> DR.error (Err.Missing_pcy pcy_var)
  | Some (pcy_var, { controller; observer }) ->
      let open TreeBlock in
      (* Reading from the controller is a way of ensuring we have the part we require.
         An invariant is that the values of the controller and the resolver have to coincide *)
      let** value, _ = get_proj ~tyenv controller proj ty true in
      let** observer = rem_proj ~tyenv observer proj ty in
      let learned =
        let open Formula.Infix in
        [ (proj_on_var pcy_var proj) #== value ]
      in
      let new_pcies = PcyMap.add pcy_var { controller; observer } pcy_env in
      DR.ok ~learned new_pcies

let alloc ~tyenv pcy_env ty =
  let new_lvar = Expr.LVar (LVar.alloc ()) in
  let new_block =
    let current_value = Expr.LVar (LVar.alloc ()) in
    let controller =
      TreeBlock.outer_symbolic ~tyenv ~offset:None ty current_value
    in
    let observer = controller in
    { controller; observer }
  in
  let updated_env = PcyMap.add new_lvar new_block pcy_env in
  ([ new_lvar; Expr.EList [] ], updated_env)

let pp ft t =
  let open Fmt in
  pf ft "@[<v 2>Prophecies:@,%a@]"
    (iter_bindings PcyMap.iter (pair ~sep:(any " -> ") Expr.pp pp_block))
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
    PcyMap.to_seq pcy_env |> List.of_seq
    |> DR_list.map (fun (pcy_var, block) ->
           let** controller =
             TreeBlock.outer_substitution ~tyenv ~subst_expr block.controller
           in
           let++ observer =
             TreeBlock.outer_substitution ~tyenv ~subst_expr block.observer
           in
           (pcy_var, { controller; observer }))
  in
  List.to_seq new_mapping |> PcyMap.of_seq
