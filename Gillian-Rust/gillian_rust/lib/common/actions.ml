type t =
  | Alloc
  | Load_value
  | Store_value
  | Load_slice
  | Store_slice
  | Deinit
  | Free
  | Load_discr
  (* Core predicate manipulation *)
  | Get_value
  | Set_value
  | Rem_value
  | Get_freed
  | Set_freed
  | Rem_freed

type core_predicate = Value | Freed

let ga_to_getter = function
  | Value -> Get_value
  | Freed -> Get_freed

let ga_to_setter = function
  | Value -> Set_value
  | Freed -> Set_freed

let ga_to_deleter = function
  | Value -> Rem_value
  | Freed -> Rem_freed

let of_name = function
  | "alloc" -> Alloc
  | "load_value" -> Load_value
  | "store_value" -> Store_value
  | "load_slice" -> Load_slice
  | "store_slice" -> Store_slice
  | "deinit" -> Deinit
  | "free" -> Free
  | "load_discr" -> Load_discr
  | "get_value" -> Get_value
  | "set_value" -> Set_value
  | "rem_value" -> Rem_value
  | "get_freed" -> Get_freed
  | "set_freed" -> Set_freed
  | "rem_freed" -> Rem_freed
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
  | Get_value -> "get_value"
  | Set_value -> "set_value"
  | Rem_value -> "rem_value"
  | Get_freed -> "get_freed"
  | Set_freed -> "set_freed"
  | Rem_freed -> "rem_freed"

let cp_to_name = function
  | Value -> "value"
  | Freed -> "freed"

let cp_of_name = function
  | "value" -> Value
  | "freed" -> Freed
  | _ -> failwith "incorrect compilation: unknown core predicate"

let ga_to_getter_str str = str |> cp_of_name |> ga_to_getter |> to_name
let ga_to_setter_str str = str |> cp_of_name |> ga_to_setter |> to_name
let ga_to_deleter_str str = str |> cp_of_name |> ga_to_deleter |> to_name
