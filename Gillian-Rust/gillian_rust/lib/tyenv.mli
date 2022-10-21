open Gillian.Gil_syntax

type t

val empty : unit -> t
val copy : t -> t
val declared : t -> (string, Rust_types.adt_def) Hashtbl.t
val adt_def : genv:t -> string -> Rust_types.adt_def
val is_struct : genv:t -> Rust_types.t -> bool
val declare_struct : t -> string -> Literal.t -> unit
val declare : t -> string -> Rust_types.adt_def -> unit
val pp : t Fmt.t
