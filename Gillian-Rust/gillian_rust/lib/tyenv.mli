open Gillian.Gil_syntax

type t

val empty : unit -> t
val copy : t -> t
val declared : t -> (string, Ty.Adt_def.t) Hashtbl.t
val adt_def : genv:t -> string -> Ty.Adt_def.t
val is_struct : genv:t -> Ty.t -> bool
val declare_struct : t -> string -> Literal.t -> unit
val declare : t -> string -> Ty.Adt_def.t -> unit
val pp : t Fmt.t
