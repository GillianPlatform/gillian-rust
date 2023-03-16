open Gillian.Gil_syntax

type t =
  | Too_symbolic of Expr.t
  | Use_after_free of string
  | Invalid_type of Ty.t * Ty.t
  | Invalid_list_op
  | Invalid_loc of Expr.t
  | Invalid_free_pointer of Expr.t * Expr.t
  | Missing_block of string
  | Missing_lifetime of Lft.t
  | Double_kill_lifetime of Lft.t
  | Wrong_lifetime_status of Lft.t
  | Cannot_access of string
  | Unhandled of string
[@@deriving yojson, show]

let recovery_vals = function
  | Too_symbolic e | Invalid_loc e -> [ e ]
  | Use_after_free l | Missing_block l -> [ Expr.loc_from_loc_name l ]
  | Missing_lifetime l -> [ Lft.to_expr l ]
  | Invalid_free_pointer (loc, proj) -> [ loc; proj ]
  | Invalid_type _
  | Invalid_list_op
  | Unhandled _
  | Double_kill_lifetime _
  | Wrong_lifetime_status _
  | Cannot_access _ -> []

let pp ft =
  let open Fmt in
  function
  | Too_symbolic e ->
      pf ft "Expression needs to be concretized further: %a" Expr.pp e
  | Use_after_free s -> pf ft "Use after free: %s" s
  | Missing_block s -> pf ft "Missing_block: %s" s
  | Missing_lifetime l -> pf ft "Missing_lifetime: %a" Lft.pp l
  | Double_kill_lifetime l -> pf ft "Lifetime was killed twice: %a" Lft.pp l
  | Wrong_lifetime_status l -> pf ft "Lifetime %a has the wrong status" Lft.pp l
  | Invalid_type (t1, t2) -> pf ft "Invalid type: %a != %a" Ty.pp t1 Ty.pp t2
  | Invalid_list_op -> pf ft "Invalid list operation"
  | Invalid_loc e -> pf ft "Invalid location: %a" Expr.pp e
  | Cannot_access l -> pf ft "Cannot access block: %s" l
  | Invalid_free_pointer (loc, proj) ->
      pf ft "Invalid free pointer: (%a, %a)" Expr.pp loc Expr.pp proj
  | Unhandled s -> pf ft "Unhandled: %s" s
