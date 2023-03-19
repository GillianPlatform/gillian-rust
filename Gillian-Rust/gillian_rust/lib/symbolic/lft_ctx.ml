open Gillian.Utils.Prelude
module LftMap = Map.Make (Lft)

type t = bool LftMap.t [@@deriving yojson]

let set_alive t loc = LftMap.add loc true t

let kill t loc =
  match LftMap.find_opt loc t with
  | None -> Error (Err.Missing_lifetime loc)
  | Some false -> Error (Err.Double_kill_lifetime loc)
  | Some true -> Ok (LftMap.add loc false t)

let check_status ~expected t loc =
  match LftMap.find_opt loc t with
  | None -> Error (Err.Missing_lifetime loc)
  | Some actual ->
      if actual = expected then Ok () else Error (Wrong_lifetime_status loc)

let check_alive t loc = check_status ~expected:true t loc
let check_dead t loc = check_status ~expected:false t loc
let remove t loc = LftMap.remove loc t
let empty = LftMap.empty

let assertions t =
  let asrt (lft, status) =
    let alive_cp = Common.Actions.cp_to_name Alive_lft in
    if status then Gil_syntax.Asrt.GA (alive_cp, [ Lft.to_expr lft ], [])
    else failwith "not implemented: dead lfts"
  in
  LftMap.to_seq t |> Seq.map asrt |> List.of_seq