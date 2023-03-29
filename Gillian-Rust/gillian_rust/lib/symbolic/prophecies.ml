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

let observer_block loc pcy_env =
  match MemMap.find_opt loc pcy_env with
  | Some { observer = Some observer; _ } -> DR.ok observer
  | _ -> DR.error (Err.MissingBlock loc)

let set_observer ~tyenv loc observer env =
  let++ block =
    match MemMap.find_opt loc env with
    | Some ({ controller = Some controller } as block) ->
        DR.ok
          ~learned:
            [ TreeBlock.outer_equality_constraint ~tyenv controller observer ]
          { block with observer = Some observer }
    | Some { controller = None; _ } | None ->
        DR.ok { observer = Some observer; controller = None }
  in
  MemMap.add loc block env

let rem_observer loc env =
  match MemMap.find_opt loc env with
  | Some { observer = Some _; controller = None } -> MemMap.remove loc env
  | Some ({ observer = Some _; controller = Some _ } as block) ->
      MemMap.add loc { block with observer = None } env
  | None | Some { observer = None; _ } ->
      failwith "rem_observer: observer is None"

let controller_block loc pcy_env =
  match MemMap.find_opt loc pcy_env with
  | Some { controller = Some controller; _ } -> DR.ok controller
  | _ -> DR.error (Err.MissingBlock loc)

let set_controller ~tyenv loc controller env =
  let++ block =
    match MemMap.find_opt loc env with
    | Some ({ observer = Some observer; _ } as block) ->
        DR.ok
          ~learned:
            [ TreeBlock.outer_equality_constraint ~tyenv observer controller ]
          { block with controller = Some controller }
    | Some { observer = None; _ } | None ->
        DR.ok { controller = Some controller; observer = None }
  in
  MemMap.add loc block env

let rem_controller loc env =
  match MemMap.find_opt loc env with
  | Some { controller = Some _; observer = None } -> MemMap.remove loc env
  | Some ({ controller = Some _; observer = Some _ } as block) ->
      MemMap.add loc { block with controller = None } env
  | None | Some { controller = None; _ } ->
      failwith "rem_controller: controller is None"

let get_value_obs ~tyenv pcy_env loc proj ty =
  let** observer = observer_block loc pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv observer proj ty false in
  value

let set_value_obs ~tyenv pcy_env loc (proj : Projections.t) ty value =
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
  set_observer ~tyenv loc new_block pcy_env

let rem_value_obs ~tyenv pcy_env loc = rem_observer loc pcy_env

let get_controller ~tyenv pcy_env loc proj ty =
  let** controller = controller_block loc pcy_env in
  let++ value, _ = TreeBlock.get_proj ~tyenv controller proj ty false in
  value

let set_controller ~tyenv pcy_env loc (proj : Projections.t) ty value =
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
  set_controller ~tyenv loc new_block pcy_env

let rem_controller ~tyenv pcy_env loc = rem_controller loc pcy_env

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
    |> DR_list.map (fun (loc, block) ->
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
           (loc, { controller; observer }))
  in
  List.to_seq new_mapping |> MemMap.of_seq
