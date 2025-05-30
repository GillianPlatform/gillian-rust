open Gil_syntax
open Monadic

type t = Expr.t [@@deriving yojson]

let equal = Expr.equal
let pp = Expr.pp
let compare = compare

let fresh () =
  let lvar = LVar.alloc () in
  let lft = Expr.LVar lvar in
  Delayed.return ~learned_types:[ (lvar, Type.SetType) ] lft

let of_expr t = t
let to_expr t = t
let ( <=% ) lft_a lft_b = Formula.SetSub (lft_a, lft_b)
let substitution ~subst_expr lft = subst_expr lft
let lvars = Expr.lvars
