open Gillian.Gil_syntax

type t =
  | Too_symbolic of Expr.t
  | Use_after_free of string
  | Invalid_type of Ty.t * Ty.t
  | Invalid_list_op
  | Invalid_loc of Expr.t
  | Invalid_free_pointer of Expr.t * Expr.t
  | Unhandled of string
  | MissingBlock of string
[@@deriving yojson]

let recovery_vals = function
  | Too_symbolic e | Invalid_loc e -> [ e ]
  | Use_after_free l | MissingBlock l -> [ Expr.loc_from_loc_name l ]
  | Invalid_free_pointer (loc, proj) -> [ loc; proj ]
  | Invalid_type _ | Invalid_list_op | Unhandled _ -> []

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
  | Invalid_free_pointer (loc, proj) ->
      pf ft "Invalid free pointer: (%a, %a)" Expr.pp loc Expr.pp proj
  | Unhandled s -> pf ft "Unhandled: %s" s
