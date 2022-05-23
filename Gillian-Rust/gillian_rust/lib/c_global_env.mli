open Gillian.Gil_syntax

type t

val empty : unit -> t
val copy : t -> t
val get_type : t -> string -> Rust_types.t
val declared : t -> (string, Rust_types.t) Hashtbl.t
val subtypes : genv:t -> Rust_types.t -> Rust_types.t -> bool
val resolve_named : genv:t -> Rust_types.t -> Rust_types.t
val declare_struct : t -> string -> Literal.t -> unit
val pp : t Fmt.t
