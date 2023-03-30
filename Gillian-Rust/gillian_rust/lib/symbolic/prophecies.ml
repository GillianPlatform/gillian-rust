open Monadic
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
open Heap
open Gil_syntax
open Delayed_utils

type block = {
  observer : TreeBlock.outer option;
  controller : TreeBlock.outer option;
}

let pp_block =
  let open Fmt in
  Fmt.braces
  @@ record ~sep:semi
       [
         field "observer" (fun x -> x.observer) (Dump.option TreeBlock.pp_outer);
         field "controller"
           (fun x -> x.controller)
           (Dump.option TreeBlock.pp_outer);
       ]

type t = block MemMap.t

let empty = MemMap.empty
let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let observer_block pcy_var pcy_env =
  match MemMap.find_opt pcy_var pcy_env with
  | Some { observer = Some observer; _ } -> DR.ok observer
  | _ -> DR.error (Err.MissingBlock pcy_var)

let set_observer ~tyenv pcy_var observer env =
  let++ block =
    match MemMap.find_opt pcy_var env with
    | Some ({ controller = Some controller } as block) ->
        DR.ok
          ~learned:
            [ TreeBlock.outer_equality_constraint ~tyenv controller observer ]
          { block with observer = Some observer }
    | Some { controller = None; _ } | None ->
        DR.ok { observer = Some observer; controller = None }
  in
  MemMap.add pcy_var block env

let rem_observer pcy_var env =
  match MemMap.find_opt pcy_var env with
  | Some { observer = Some _; controller = None } -> MemMap.remove pcy_var env
  | Some ({ observer = Some _; controller = Some _ } as block) ->
      MemMap.add pcy_var { block with observer = None } env
  | None | Some { observer = None; _ } ->
      failwith "rem_observer: observer is None"

let controller_block pcy_var pcy_env =
  match MemMap.find_opt pcy_var pcy_env with
  | Some { controller = Some controller; _ } -> DR.ok controller
  | _ -> DR.error (Err.MissingBlock pcy_var)

let set_controller ~tyenv pcy_var controller env =
  let++ block =
    match MemMap.find_opt pcy_var env with
    | Some ({ observer = Some observer; _ } as block) ->
        DR.ok
          ~learned:
            [ TreeBlock.outer_equality_constraint ~tyenv observer controller ]
          { block with controller = Some controller }
    | Some { observer = None; _ } | None ->
        DR.ok { controller = Some controller; observer = None }
  in
  MemMap.add pcy_var block env

let rem_controller pcy_var env =
  match MemMap.find_opt pcy_var env with
  | Some { controller = Some _; observer = None } -> MemMap.remove pcy_var env
  | Some ({ controller = Some _; observer = Some _ } as block) ->
      MemMap.add pcy_var { block with controller = None } env
  | None | Some { controller = None; _ } ->
      failwith "rem_controller: controller is None"

let get_value_obs ~tyenv pcy_env pcy_var proj ty =
  let** observer = observer_block pcy_var pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv observer proj ty false in
  value

let set_value_obs ~tyenv pcy_env pcy_var (proj : Projections.t) ty value =
  let** () =
    match proj.from_base with
    | [] -> DR.ok ()
    | _ ->
        DR.error
          (Err.Unhandled
             "set_value_obs: from_base not empty, can't handle partial trees \
              yet")
  in
  let** new_block =
    TreeBlock.outer_of_rust_value ~offset:proj.base ~tyenv ~ty value
  in
  set_observer ~tyenv pcy_var new_block pcy_env

let rem_value_obs ~tyenv pcy_env pcy_var = rem_observer pcy_var pcy_env

let get_controller ~tyenv pcy_env pcy_var proj ty =
  let** controller = controller_block pcy_var pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv controller proj ty false in
  value

let set_controller ~tyenv pcy_env pcy_var (proj : Projections.t) ty value =
  let** () =
    match proj.from_base with
    | [] -> DR.ok ()
    | _ ->
        DR.error
          (Err.Unhandled
             "set_controller: from_base not empty, can't handle partial trees \
              yet")
  in
  let** new_block =
    TreeBlock.outer_of_rust_value ~offset:proj.base ~tyenv ~ty value
  in
  set_controller ~tyenv pcy_var new_block pcy_env

let rem_controller ~tyenv pcy_env pcy_var = rem_controller pcy_var pcy_env

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
  List.fold_left apply_op (Expr.LVar pcy_var) proj.from_base

let resolve ~tyenv pcy_env pcy_var (proj : Projections.t) ty =
  match MemMap.find_opt pcy_var pcy_env with
  | None | Some { controller = None; _ } | Some { observer = None; _ } ->
      DR.error (Err.MissingBlock pcy_var)
  | Some
      ({ controller = Some controller; observer = Some observer } as
      before_consume) ->
      let open TreeBlock in
      let consume_proj ~tyenv t proj =
        let update block = { ty = block.ty; content = Missing } in
        let return_and_update t = DR.ok (to_rust_value ~tyenv t, update t) in
        find_proj ~tyenv ~return_and_update ~ty t proj
      in
      let** value, observer = consume_proj ~tyenv observer proj in
      let learned =
        let open Formula.Infix in
        [ (proj_on_var pcy_var proj) #== value ]
      in
      let new_pcies =
        MemMap.add pcy_var
          { before_consume with observer = Some observer }
          pcy_env
      in
      DR.ok ~learned new_pcies

let pp ft t =
  let open Fmt in
  pf ft "@[<v 2>Prophecies:@,%a@]"
    (iter_bindings MemMap.iter (pair ~sep:(any " -> ") string pp_block))
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
    |> DR_list.map (fun (pcy_var, block) ->
           let** controller =
             DR_option.map
               (TreeBlock.outer_substitution ~tyenv ~subst_expr)
               block.controller
           in
           let++ observer =
             DR_option.map
               (TreeBlock.outer_substitution ~tyenv ~subst_expr)
               block.observer
           in
           (pcy_var, { controller; observer }))
  in
  List.to_seq new_mapping |> MemMap.of_seq