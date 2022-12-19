(** In Gillian-Rust, we use symbolic values to denote potentially polymorphic types.
    In our execution, types are simply passed around as values, which means we can pass
    polymorphic types as function inputs. *)

open Gillian.Gil_syntax

type t = C of Ty.t | S of Expr.t [@@deriving yojson]

let pp fmt = function
  | C ty -> Ty.pp fmt ty
  | S e -> Expr.pp fmt e