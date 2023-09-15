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

let assertions (t : t) =
  let cp = Common.Actions.cp_to_name Observation in
  let of_formula f =
    let exp = Formula.to_expr f |> Option.get in
    Asrt.GA (cp, [ exp ], [])
  in
  List.map of_formula t

let lvars (t : t) =
  let open Utils.Containers in
  List.fold_left (fun acc f -> SS.union acc (Formula.lvars f)) SS.empty t
