open Gil_syntax

type t [@@deriving yojson, ord]

val pp : Format.formatter -> t -> unit
val of_expr : Expr.t -> t
val to_expr : t -> Expr.t
val ( <=% ) : t -> t -> Formula.t
val substitution : subst_expr:(Expr.t -> Expr.t) -> t -> t
