type t =
  | Alloc
  | Load_value
  | Store_value
  | Load_slice
  | Store_slice
  | Deinit
  | Free
  | Load_discr
  | New_lft
  | End_lft
  (* Core predicate manipulation *)
  | Get_value
  | Set_value
  | Rem_value
  | Get_pcy_value
  | Set_pcy_value
  | Rem_pcy_value
  | Get_alive_lft
  | Set_alive_lft
  | Rem_alive_lft
  | Get_freed
  | Set_freed
  | Rem_freed

type core_predicate = Value | Pcy_value | Freed | Alive_lft

let ga_to_getter = function
  | Value -> Get_value
  | Pcy_value -> Get_pcy_value
  | Freed -> Get_freed
  | Alive_lft -> Get_alive_lft

let ga_to_setter = function
  | Value -> Set_value
  | Pcy_value -> Set_pcy_value
  | Freed -> Set_freed
  | Alive_lft -> Set_alive_lft

let ga_to_deleter = function
  | Value -> Rem_value
  | Pcy_value -> Rem_pcy_value
  | Freed -> Rem_freed
  | Alive_lft -> Rem_alive_lft

let of_name = function
  | "alloc" -> Alloc
  | "load_value" -> Load_value
  | "store_value" -> Store_value
  | "load_slice" -> Load_slice
  | "store_slice" -> Store_slice
  | "deinit" -> Deinit
  | "free" -> Free
  | "load_discr" -> Load_discr
  | "new_lft" -> New_lft
  | "end_lft" -> End_lft
  | "get_value" -> Get_value
  | "set_value" -> Set_value
  | "rem_value" -> Rem_value
  | "get_pcy_value" -> Get_pcy_value
  | "set_pcy_value" -> Set_pcy_value
  | "rem_pcy_value" -> Rem_pcy_value
  | "get_alive_lft" -> Get_alive_lft
  | "set_alive_lft" -> Set_alive_lft
  | "rem_alive_lft" -> Rem_alive_lft
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
  | New_lft -> "new_lft"
  | End_lft -> "end_lft"
  | Get_value -> "get_value"
  | Set_value -> "set_value"
  | Rem_value -> "rem_value"
  | Get_pcy_value -> "get_pcy_value"
  | Set_pcy_value -> "set_pcy_value"
  | Rem_pcy_value -> "rem_pcy_value"
  | Get_freed -> "get_freed"
  | Set_freed -> "set_freed"
  | Rem_freed -> "rem_freed"
  | Get_alive_lft -> "get_alive_lft"
  | Set_alive_lft -> "set_alive_lft"
  | Rem_alive_lft -> "rem_alive_lft"

let cp_to_name = function
  | Value -> "value"
  | Pcy_value -> "pcy_value"
  | Freed -> "freed"
  | Alive_lft -> "alive_lft"

let cp_of_name = function
  | "value" -> Value
  | "pcy_value" -> Pcy_value
  | "freed" -> Freed
  | "alive_lft" -> Alive_lft
  | _ -> failwith "incorrect compilation: unknown core predicate"

let ga_to_getter_str str = str |> cp_of_name |> ga_to_getter |> to_name
let ga_to_setter_str str = str |> cp_of_name |> ga_to_setter |> to_name
let ga_to_deleter_str str = str |> cp_of_name |> ga_to_deleter |> to_name
