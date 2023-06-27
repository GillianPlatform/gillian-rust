open Gil_syntax
open Gillian.Monadic
module DR = Delayed_result

type t = Formula.t list [@@deriving yojson]

let empty = []

let get_observation (t : t) (obs : Formula.t) : (unit, Err.t) DR.t =
  let open Delayed.Syntax in
  let* valid_entailment = Delayed.entails t obs in
  if valid_entailment then DR.ok ()
  else
    let error = Err.Missing_observation obs in
    DR.error error

let set_observation (t : t) (obs : Formula.t) : (t, Err.t) DR.t =
  let open Delayed.Syntax in
  let* is_sat = Delayed.check_sat (Formula.conjunct (obs :: t)) in
  if is_sat then DR.ok (obs :: t) else DR.error (Err.Unsat_observation obs)
