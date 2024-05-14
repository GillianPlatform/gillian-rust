open Gil_syntax
open Monadic

type t [@@deriving yojson, ord, eq]

val pp : Format.formatter -> t -> unit
val fresh : unit -> t Delayed.t
val of_expr : Expr.t -> t
val to_expr : t -> Expr.t
val ( <=% ) : t -> t -> Formula.t
val substitution : subst_expr:(Expr.t -> Expr.t) -> t -> t
val lvars : t -> Utils.Containers.SS.t
