open Gillian.Gil_syntax

type t

val empty : unit -> t

val copy : t -> t

val get_type : t -> string -> Rust_types.t

val type_equal : genv:t -> Rust_types.t -> Rust_types.t -> bool

val declare_struct : t -> string -> Literal.t -> unit

val pp : t Fmt.t
