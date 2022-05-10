type t = Alloc | Load | Store | Free | LoadDiscr | Genv_decl_type

let of_name = function
  | "mem_alloc"      -> Alloc
  | "mem_load"       -> Load
  | "mem_store"      -> Store
  | "mem_free"       -> Free
  | "mem_load_discr" -> LoadDiscr
  | "genv_decl_type" -> Genv_decl_type
  | "genv_" | _      -> failwith "incorrect compilation: unkown action"
