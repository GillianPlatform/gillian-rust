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