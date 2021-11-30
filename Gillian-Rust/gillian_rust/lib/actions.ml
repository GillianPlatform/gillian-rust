type t = Alloc | Load | Store | LoadDiscr | StoreDiscr | Genv_decl_type

let of_name = function
  | "mem_alloc"       -> Alloc
  | "mem_load"        -> Load
  | "mem_store"       -> Store
  | "mem_load_discr"  -> LoadDiscr
  | "mem_store_discr" -> StoreDiscr
  | "genv_decl_type"  -> Genv_decl_type
  | "genv_" | _       -> failwith "incorrect compilation: unkown action"
