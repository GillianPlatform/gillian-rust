open Gillian.Gil_syntax

type t =
  | Too_symbolic of Expr.t
  | Use_after_free of string
  | Invalid_type of Ty.t * Ty.t
  | Invalid_list_op
  | Invalid_loc of Expr.t
  | Unhandled of string
[@@deriving yojson]

let recovery_vals = function
  | Too_symbolic e | Invalid_loc e -> [ e ]
  | Use_after_free l -> [ Expr.loc_from_loc_name l ]
  | Invalid_type _ | Invalid_list_op | Unhandled _ -> []

let pp ft =
  let open Fmt in
  function
  | Too_symbolic e ->
      pf ft "Expression needs to be concretized further: %a" Expr.pp e
  | Use_after_free s -> pf ft "Use after free: %s" s
  | Invalid_type (t1, t2) -> pf ft "Invalid type: %a != %a" Ty.pp t1 Ty.pp t2
  | Invalid_list_op -> pf ft "Invalid list operation"
  | Invalid_loc e -> pf ft "Invalid location: %a" Expr.pp e
  | Unhandled s -> pf ft "Unhandled: %s" s
