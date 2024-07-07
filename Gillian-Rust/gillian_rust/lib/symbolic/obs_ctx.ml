open Gil_syntax
open Gillian.Monadic
module DR = Delayed_result

type t = Formula.t list [@@deriving yojson]

let empty = []

let cons_observation (t : t) (obs : Formula.t) : (unit, Err.t) DR.t =
  let open Delayed.Syntax in
  let* valid_entailment = Delayed.entails t obs in
  if valid_entailment then DR.ok ()
  else
    let error = Err.Missing_observation obs in
    DR.error error

let prod_observation (t : t) (obs : Formula.t) : t Delayed.t =
  let open Delayed.Syntax in
  let* obs = Delayed.reduce_formula obs in
  let* is_sat = Delayed.check_sat (Formula.conjunct (obs :: t)) in
  if is_sat then
    let obs = Formula.split_conjunct_formulae obs in
    Delayed.return (obs @ t)
  else Delayed.vanish ()

let check_sat (t : t) : unit Delayed.t =
  let open Delayed.Syntax in
  let* is_sat = Delayed.check_sat (Formula.conjunct t) in
  if is_sat then Delayed.return () else Delayed.vanish ()

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

let substitution s lk =
  let subst_formula =
    Gillian.Symbolic.Subst.substitute_formula s ~partial:true
  in
  List.map subst_formula lk

let pp ft o = (Fmt.list ~sep:(Fmt.any "@\n") Formula.pp) ft o
