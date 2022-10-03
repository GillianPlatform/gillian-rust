type t =
  | Alloc
  | Load_value
  | Store_value
  | Load_slice
  | Store_slice
  | Deinit
  | Free
  | LoadDiscr
  | Genv_decl_type

let of_name = function
  | "mem_alloc" -> Alloc
  | "mem_load_value" -> Load_value
  | "mem_store_value" -> Store_value
  | "mem_load_slice" -> Load_slice
  | "mem_store_slice" -> Store_slice
  | "mem_deinit" -> Deinit
  | "mem_free" -> Free
  | "mem_load_discr" -> LoadDiscr
  | "genv_decl_type" -> Genv_decl_type
  | "genv_" | _ -> failwith "incorrect compilation: unkown action"
