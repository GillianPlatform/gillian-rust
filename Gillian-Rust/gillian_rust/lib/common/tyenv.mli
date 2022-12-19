type t [@@deriving yojson]

val adt_def : tyenv:t -> string -> Ty.Adt_def.t
val is_struct : tyenv:t -> Ty.t -> bool
val pp : t Fmt.t
val of_declaration_list : (string * Ty.Adt_def.t) list -> t
val leak : t -> (string, Ty.Adt_def.t) Hashtbl.t
