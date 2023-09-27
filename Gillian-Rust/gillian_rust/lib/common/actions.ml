type t =
  (* Memory *)
  | Alloc
  | Load_value
  | Store_value
  | Load_slice
  | Store_slice
  | Deinit
  | Free
  | Load_discr
  (* Prophecies *)
  | Pcy_alloc
  | Pcy_assign
  | Pcy_resolve

type core_predicate =
  | Value
  | Freed
  | Lft
  | Value_observer
  | Pcy_controller
  | Pcy_value
  | Observation

let of_name = function
  | "alloc" -> Alloc
  | "load_value" -> Load_value
  | "store_value" -> Store_value
  | "load_slice" -> Load_slice
  | "store_slice" -> Store_slice
  | "deinit" -> Deinit
  | "free" -> Free
  | "load_discr" -> Load_discr
  | "pcy_alloc" -> Pcy_alloc
  | "pcy_assign" -> Pcy_assign
  | "pcy_resolve" -> Pcy_resolve
  | _ -> failwith "incorrect compilation: unknown action"

let to_name = function
  | Alloc -> "alloc"
  | Load_value -> "load_value"
  | Store_value -> "store_value"
  | Load_slice -> "load_slice"
  | Store_slice -> "store_slice"
  | Deinit -> "deinit"
  | Free -> "free"
  | Load_discr -> "load_discr"
  | Pcy_alloc -> "pcy_alloc"
  | Pcy_assign -> "pcy_assign"
  | Pcy_resolve -> "pcy_resolve"

let cp_to_name = function
  | Value -> "value"
  | Freed -> "freed"
  | Lft -> "lft"
  | Value_observer -> "value_observer"
  | Pcy_controller -> "pcy_controller"
  | Pcy_value -> "pcy_value"
  | Observation -> "observation"

let cp_of_name = function
  | "value" -> Value
  | "freed" -> Freed
  | "lft" -> Lft
  | "value_observer" -> Value_observer
  | "pcy_controller" -> Pcy_controller
  | "pcy_value" -> Pcy_value
  | "observation" -> Observation
  | _ -> failwith "incorrect compilation: unknown core predicate"
