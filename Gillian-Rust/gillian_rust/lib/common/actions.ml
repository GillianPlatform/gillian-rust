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
  (* Core predicate manipulation: memory *)
  | Get_value
  | Set_value
  | Rem_value
  | Get_freed
  | Set_freed
  | Rem_freed
  | Get_lft
  | Set_lft
  | Rem_lft
  (* Core predicate manipulation: prophecies*)
  | Get_value_observer
  | Set_value_observer
  | Rem_value_observer
  | Get_pcy_controller
  | Set_pcy_controller
  | Rem_pcy_controller
  | Get_pcy_value
  | Set_pcy_value
  | Rem_pcy_value

type core_predicate =
  | Value
  | Freed
  | Lft
  | Value_observer
  | Pcy_controller
  | Pcy_value

let ga_to_getter = function
  | Value -> Get_value
  | Freed -> Get_freed
  | Lft -> Get_lft
  | Value_observer -> Get_value_observer
  | Pcy_controller -> Get_pcy_controller
  | Pcy_value -> Get_pcy_value

let ga_to_setter = function
  | Value -> Set_value
  | Freed -> Set_freed
  | Lft -> Set_lft
  | Value_observer -> Set_value_observer
  | Pcy_controller -> Set_pcy_controller
  | Pcy_value -> Set_pcy_value

let ga_to_deleter = function
  | Value -> Rem_value
  | Freed -> Rem_freed
  | Lft -> Rem_lft
  | Value_observer -> Rem_value_observer
  | Pcy_controller -> Rem_pcy_controller
  | Pcy_value -> Rem_pcy_value

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
  | "get_value" -> Get_value
  | "set_value" -> Set_value
  | "rem_value" -> Rem_value
  | "get_freed" -> Get_freed
  | "set_freed" -> Set_freed
  | "rem_freed" -> Rem_freed
  | "get_lft" -> Get_lft
  | "set_lft" -> Set_lft
  | "rem_lft" -> Rem_lft
  | "get_value_observer" -> Get_value_observer
  | "set_value_observer" -> Set_value_observer
  | "rem_value_observer" -> Rem_value_observer
  | "get_pcy_controller" -> Get_pcy_controller
  | "set_pcy_controller" -> Set_pcy_controller
  | "rem_pcy_controller" -> Rem_pcy_controller
  | "get_pcy_value" -> Get_pcy_value
  | "set_pcy_value" -> Set_pcy_value
  | "rem_pcy_value" -> Rem_pcy_value
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
  | Get_value -> "get_value"
  | Set_value -> "set_value"
  | Rem_value -> "rem_value"
  | Get_freed -> "get_freed"
  | Set_freed -> "set_freed"
  | Rem_freed -> "rem_freed"
  | Get_lft -> "get_lft"
  | Set_lft -> "set_lft"
  | Rem_lft -> "rem_lft"
  | Get_value_observer -> "get_value_observer"
  | Set_value_observer -> "set_value_observer"
  | Rem_value_observer -> "rem_value_observer"
  | Get_pcy_controller -> "get_pcy_controller"
  | Set_pcy_controller -> "set_pcy_controller"
  | Rem_pcy_controller -> "rem_pcy_controller"
  | Get_pcy_value -> "get_pcy_value"
  | Set_pcy_value -> "set_pcy_value"
  | Rem_pcy_value -> "rem_pcy_value"

let cp_to_name = function
  | Value -> "value"
  | Freed -> "freed"
  | Lft -> "lft"
  | Value_observer -> "value_observer"
  | Pcy_controller -> "pcy_controller"
  | Pcy_value -> "pcy_value"

let cp_of_name = function
  | "value" -> Value
  | "freed" -> Freed
  | "lft" -> Lft
  | "value_observer" -> Value_observer
  | "pcy_controller" -> Pcy_controller
  | "pcy_value" -> Pcy_value
  | _ -> failwith "incorrect compilation: unknown core predicate"

let ga_to_getter_str str = str |> cp_of_name |> ga_to_getter |> to_name
let ga_to_setter_str str = str |> cp_of_name |> ga_to_setter |> to_name
let ga_to_deleter_str str = str |> cp_of_name |> ga_to_deleter |> to_name
