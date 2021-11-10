type t = Alloc | Load | Store

let of_name = function
  | "mem_alloc" -> Alloc
  | "mem_load"  -> Load
  | "mem_store" -> Store
  | _           -> failwith "incorrect compilation: unkown action"
