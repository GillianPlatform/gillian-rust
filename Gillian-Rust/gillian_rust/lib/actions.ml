type t =
  | Alloc
  | Load_value
  | Store_value
  | Load_slice
  | Store_slice
  | Deinit
  | Free
  | LoadDiscr
  (* Core predicate manipulation *)
  | Get_value
  | Set_value
  | Rem_value

type core_predicate = Value

let ga_to_getter = function
  | Value -> Get_value

let ga_to_setter = function
  | Value -> Set_value

let ga_to_deleter = function
  | Value -> Rem_value

let of_name = function
  | "alloc" -> Alloc
  | "load_value" -> Load_value
  | "store_value" -> Store_value
  | "load_slice" -> Load_slice
  | "store_slice" -> Store_slice
  | "deinit" -> Deinit
  | "free" -> Free
  | "load_discr" -> LoadDiscr
  | "get_value" -> Get_value
  | "set_value" -> Set_value
  | "rem_value" -> Rem_value
  | _ -> failwith "incorrect compilation: unknown action"

let to_name = function
  | Alloc -> "alloc"
  | Load_value -> "load_value"
  | Store_value -> "store_value"
  | Load_slice -> "load_slice"
  | Store_slice -> "store_slice"
  | Deinit -> "deinit"
  | Free -> "free"
  | LoadDiscr -> "load_discr"
  | Get_value -> "get_value"
  | Set_value -> "set_value"
  | Rem_value -> "rem_value"

let cp_to_name = function
  | Value -> "value"

let cp_of_name = function
  | "value" -> Value
  | _ -> failwith "incorrect compilation: unknown core predicate"

let ga_to_getter_str str = str |> cp_of_name |> ga_to_getter |> to_name
let ga_to_setter_str str = str |> cp_of_name |> ga_to_setter |> to_name
let ga_to_deleter_str str = str |> cp_of_name |> ga_to_deleter |> to_name
