open Gillian.Gil_syntax
module Recovery_tactic = Gillian.General.Recovery_tactic

type t =
  | Too_symbolic of Expr.t
  | Use_after_free of string
  | Invalid_type of Ty.t * Ty.t
  | Invalid_list_op
  | Invalid_loc of Expr.t
  | Invalid_pcy_var of Expr.t
  | Invalid_free_pointer of Expr.t * Expr.t
  | Invalid_value of Ty.t * Expr.t
  | LogicError of string (* "outs" don't match. e.g. we expect missing and it's not missing. *)
  | Uninitialised_access of string * Projections.t
  | Unhandled of string
  | MissingBlock of string
  | Missing_pcy of string
  | Missing_lifetime of Lft.t
  | Missing_proj of (string * Projections.t * Qty.t) (* Something could be only partially missing *)
  | Missing_observation of Formula.t
  | Double_kill_lifetime of Lft.t
  | Wrong_lifetime_status of Lft.t
  | Unsat_observation of Formula.t
[@@deriving yojson, show]

let recovery_tactic =
  let open Recovery_tactic in
  function
  | Too_symbolic e | Invalid_loc e | Invalid_value (_, e) -> try_unfold [ e ]
  | Missing_lifetime e -> try_fold [ Lft.to_expr e ]
  | MissingBlock l | Missing_pcy l -> try_unfold [ Expr.loc_from_loc_name l ]
  | Invalid_free_pointer (loc, proj) -> try_unfold [ loc; proj ]
  | Missing_observation f -> (
      match Formula.to_expr f with
      | Some e -> try_unfold [ e ]
      | None -> Recovery_tactic.none)
  | Missing_proj (loc, proj, _) ->
      try_unfold [ Expr.loc_from_loc_name loc; Projections.to_expr proj ]
  | LogicError _
  | Invalid_type _
  | Invalid_list_op
  | Unhandled _
  | Invalid_pcy_var _
  | Use_after_free _
  | Double_kill_lifetime _
  | Wrong_lifetime_status _
  | Unsat_observation _
  | Uninitialised_access _ -> Recovery_tactic.none

let pp ft =
  let open Fmt in
  function
  | LogicError s -> pf ft "Logic error: %s" s
  | Too_symbolic e ->
      pf ft "Expression needs to be concretized further: %a" Expr.pp e
  | Use_after_free s -> pf ft "Use after free: %s" s
  | MissingBlock s -> pf ft "MissingBlock: %s" s
  | Missing_pcy s -> pf ft "Missing prophecy: %s" s
  | Missing_proj (loc, proj, qty) ->
      pf ft "%a missing projections at location %s: %a" Qty.pp qty loc
        Projections.pp proj
  | Invalid_type (t1, t2) -> pf ft "Invalid type: %a != %a" Ty.pp t1 Ty.pp t2
  | Invalid_list_op -> pf ft "Invalid list operation"
  | Invalid_loc e -> pf ft "Invalid location: %a" Expr.pp e
  | Invalid_pcy_var e -> pf ft "Invalid prophecy variable: %a" Expr.pp e
  | Invalid_free_pointer (loc, proj) ->
      pf ft "Invalid free pointer: (%a, %a)" Expr.pp loc Expr.pp proj
  | Missing_lifetime e -> pf ft "Missing lifetime: %a" Lft.pp e
  | Missing_observation f -> pf ft "Missing observation: %a" Formula.pp f
  | Double_kill_lifetime e -> pf ft "Double kill lifetime: %a" Lft.pp e
  | Wrong_lifetime_status e -> pf ft "Wrong lifetime status: %a" Lft.pp e
  | Unhandled s -> pf ft "Unhandled: %s" s
  | Invalid_value (t, e) ->
      pf ft "Invalid value for type %a: %a" Ty.pp t Expr.pp e
  | Unsat_observation f -> pf ft "Unsat observation: %a" Formula.pp f
  | Uninitialised_access (loc, proj) ->
      pf ft "Uninitialized memory access at: (%s, %a)" loc Projections.pp proj

module Conversion_error = struct
  (** Conversion error when converting trees to Rust values *)

  type reason = Uninit | Missing
  type t = reason * Projections.op list

  let lift ~loc ~proj (reason, additional_proj) =
    let total_proj = Projections.add_ops proj additional_proj in
    let qty =
      match additional_proj with
      | [] -> Qty.Totally
      | _ -> Partially
    in
    match reason with
    | Uninit -> Uninitialised_access (loc, total_proj)
    | Missing -> Missing_proj (loc, total_proj, qty)
end
