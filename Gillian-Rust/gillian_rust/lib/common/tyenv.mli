type t [@@deriving yojson]

val set_current : t -> unit
val get_current : unit -> t

val adt_def : string -> Ty.Adt_def.t
val is_struct : Ty.t -> bool
val pp : t Fmt.t
val of_declaration_list : (string * Ty.Adt_def.t) list -> t
val leak : t -> (string, Ty.Adt_def.t) Hashtbl.t
