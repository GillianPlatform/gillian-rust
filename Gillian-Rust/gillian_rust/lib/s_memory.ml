open Gillian.Symbolic
open Gillian.Gil_syntax

type vt = Values.t
type st = Subst.t
type i_fix_t = unit
type c_fix_t = unit
type err_t = unit [@@deriving yojson]
type t = unit [@@deriving yojson]

type action_ret =
  | ASucc of (t * vt list * Formula.t list * (string * Type.t) list) list
  | AFail of err_t list

let init () = ()
let execute_action ?unification:_ _action _mem _pfs _gamma _args = AFail []
let ga_to_setter _ = failwith "Not yet implemented"
let ga_to_getter _ = failwith "Not yet implemented"
let ga_to_deleter _ = failwith "Not yet implemented"
let is_overlapping_asrt _ = failwith "Not yet implemented"
let copy t = t
let pp _ _ = failwith "Not yet implemented"
let pp_by_need _ _ = failwith "Not yet implemented"
let get_print_info _ _ = failwith "Not yet implemented"
let substitution_in_place ~pfs:_ ~gamma:_ _ _ = failwith "Not yet implemented"
let fresh_val _ = failwith "Not yet implemented"
let clean_up ?keep:_ _ = failwith "Not yet implemented"
let lvars _ = failwith "Not yet implemented"
let alocs _ = failwith "Not yet implemented"
let assertions ?to_keep:_ _ = failwith "Not yet implemented"
let mem_constraints _ = failwith "Not yet implemented"
let pp_i_fix _ _ = failwith "Not yet implemented"
let pp_c_fix _ _ = failwith "Not yet implemented"
let get_recovery_vals _ _ = failwith "Not yet implemented"
let pp_err _ _ = failwith "Not yet implemented"
let get_failing_constraint _ = failwith "Not yet implemented"
let get_fixes ?simple_fix:_ _ _ _ = failwith "Not yet implemented"
let apply_fix _ _ _ _ = failwith "Not yet implemented"
