type t =
  (* Memory *)
  | Alloc
  | Load_value
  | Store_value
  | Copy_nonoverlapping
  | Deinit
  | Free
  | Load_discr
  (* Lifetime things *)
  | New_lft
  | Kill_lft
  (* Size things *)
  | Size_of
  (* | Is_zst *)
  (* We can optimise this without computing param sizes in most cases *)
  | Ty_is_unsized
  (* Prophecies *)
  | Pcy_alloc
  | Pcy_assign
  (* Observations *)
  | Check_obs_sat

type core_predicate =
  | Value
  | Uninit
  | Maybe_uninit
  | Many_maybe_uninits
  | Freed
  | Ty_size
  | Lft
  | Value_observer
  | Pcy_controller
  | Pcy_value
  | Observation

let of_name = function
  | "alloc" -> Alloc
  | "load_value" -> Load_value
  | "store_value" -> Store_value
  | "copy_nonoverlapping" -> Copy_nonoverlapping
  | "deinit" -> Deinit
  | "free" -> Free
  | "new_lft" -> New_lft
  | "kill_lft" -> Kill_lft
  | "size_of" -> Size_of
  (* | "is_zst" -> Is_zst *)
  | "ty_is_unsized" -> Ty_is_unsized
  | "load_discr" -> Load_discr
  | "pcy_alloc" -> Pcy_alloc
  | "pcy_assign" -> Pcy_assign
  | "check_obs_sat" -> Check_obs_sat
  | _ -> failwith "incorrect compilation: unknown action"

let to_name = function
  | Alloc -> "alloc"
  | Load_value -> "load_value"
  | Store_value -> "store_value"
  | Copy_nonoverlapping -> "copy_nonoverlapping"
  | Deinit -> "deinit"
  | Free -> "free"
  | New_lft -> "new_lft"
  | Kill_lft -> "kill_lft"
  | Size_of -> "size_of"
  (* | Is_zst -> "is_zst" *)
  | Ty_is_unsized -> "ty_is_unsized"
  | Load_discr -> "load_discr"
  | Pcy_alloc -> "pcy_alloc"
  | Pcy_assign -> "pcy_assign"
  | Check_obs_sat -> "check_obs_sat"

let cp_to_name = function
  | Value -> "value"
  | Uninit -> "uninit"
  | Maybe_uninit -> "maybe_uninit"
  | Many_maybe_uninits -> "many_maybe_uninits"
  | Freed -> "freed"
  | Ty_size -> "ty_size"
  | Lft -> "lft"
  | Value_observer -> "value_observer"
  | Pcy_controller -> "pcy_controller"
  | Pcy_value -> "pcy_value"
  | Observation -> "observation"

let cp_of_name = function
  | "value" -> Value
  | "uninit" -> Uninit
  | "maybe_uninit" -> Maybe_uninit
  | "many_maybe_uninits" -> Many_maybe_uninits
  | "freed" -> Freed
  | "ty_size" -> Ty_size
  | "lft" -> Lft
  | "value_observer" -> Value_observer
  | "pcy_controller" -> Pcy_controller
  | "pcy_value" -> Pcy_value
  | "observation" -> Observation
  | cp -> Fmt.failwith "incorrect compilation: unknown core predicate: %s" cp
