open Gillian.Gil_syntax

type t =
  | Too_symbolic of Expr.t
  | Use_after_free of string
  | Invalid_type of Ty.t * Ty.t
  | Invalid_list_op
  | Invalid_loc of Expr.t
  | Invalid_pcy_var of Expr.t
  | Invalid_free_pointer of Expr.t * Expr.t
  | Invalid_value of Ty.t * Expr.t
  | Unhandled of string
  | MissingBlock of string
  | Missing_lifetime of Lft.t
  | Double_kill_lifetime of Lft.t
  | Wrong_lifetime_status of Lft.t
[@@deriving yojson, show]

let recovery_vals = function
  | Too_symbolic e | Invalid_loc e -> [ e ]
  | Missing_lifetime e | Double_kill_lifetime e | Wrong_lifetime_status e ->
      [ Lft.to_expr e ]
  | Use_after_free l | MissingBlock l -> [ Expr.loc_from_loc_name l ]
  | Invalid_value (_, e) -> [ e ]
  | Invalid_free_pointer (loc, proj) -> [ loc; proj ]
  | Invalid_type _ | Invalid_list_op | Unhandled _ | Invalid_pcy_var _ -> []

let pp ft =
  let open Fmt in
  function
  | Too_symbolic e ->
      pf ft "Expression needs to be concretized further: %a" Expr.pp e
  | Use_after_free s -> pf ft "Use after free: %s" s
  | MissingBlock s -> pf ft "MissingBlock: %s" s
  | Invalid_type (t1, t2) -> pf ft "Invalid type: %a != %a" Ty.pp t1 Ty.pp t2
  | Invalid_list_op -> pf ft "Invalid list operation"
  | Invalid_loc e -> pf ft "Invalid location: %a" Expr.pp e
  | Invalid_pcy_var e -> pf ft "Invalid prophecy variable: %a" Expr.pp e
  | Invalid_free_pointer (loc, proj) ->
      pf ft "Invalid free pointer: (%a, %a)" Expr.pp loc Expr.pp proj
  | Missing_lifetime e -> pf ft "Missing lifetime: %a" Lft.pp e
  | Double_kill_lifetime e -> pf ft "Double kill lifetime: %a" Lft.pp e
  | Wrong_lifetime_status e -> pf ft "Wrong lifetime status: %a" Lft.pp e
  | Unhandled s -> pf ft "Unhandled: %s" s
  | Invalid_value (t, e) ->
      pf ft "Invalid value for type %a: %a" Ty.pp t Expr.pp e
