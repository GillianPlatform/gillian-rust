open Gillian.Utils.Prelude
module DR = Monadic.Delayed_result
module LftMap = Map.Make (Lft)

type t = bool LftMap.t [@@deriving yojson]

let is_empty = LftMap.for_all (fun _ b -> not b)

let pp ft t =
  (Fmt.iter_bindings LftMap.iter (fun ft (x, y) ->
       Fmt.pf ft "%a: %b" Lft.pp x y))
    ft t

let cons t lft =
  match LftMap.find_opt lft t with
  | None -> Error (Err.Missing_lifetime lft)
  | Some true -> Ok (true, LftMap.remove lft t)
  | Some false -> Ok (false, t)

let produce t lft status =
  match (LftMap.find_opt lft t, status) with
  | None, status -> Some (LftMap.add lft status t)
  | Some false, false -> Some t (* <lft>(#l, false) is pure *)
  | Some _, _ -> None

let new_lft t =
  let open Monadic.Delayed.Syntax in
  let+ lft = Lft.fresh () in
  (lft, LftMap.add lft true t)

let kill t loc =
  match LftMap.find_opt loc t with
  | None -> DR.error (Err.Missing_lifetime loc)
  | Some false -> DR.error (Err.Double_kill_lifetime loc)
  | Some true -> DR.ok (LftMap.add loc false t)

let check_status ~expected t loc =
  match LftMap.find_opt loc t with
  | None -> Error (Err.Missing_lifetime loc)
  | Some actual ->
      if actual = expected then Ok () else Error (Wrong_lifetime_status loc)

let check_alive t loc = check_status ~expected:true t loc
let check_dead t loc = check_status ~expected:false t loc
let empty = LftMap.empty

let assertions t =
  let cp = Common.Actions.cp_to_name Lft in
  let asrt (lft, status) =
    Gil_syntax.Asrt.GA (cp, [ Lft.to_expr lft ], [ Gil_syntax.Expr.bool status ])
  in
  LftMap.to_seq t |> Seq.map asrt |> List.of_seq

let substitution subst t =
  let subst_expr = Gillian.Symbolic.Subst.subst_in_expr subst ~partial:true in
  LftMap.to_seq t
  |> Seq.map (fun (x, y) -> (Lft.substitution ~subst_expr x, y))
  |> LftMap.of_seq

let lvars t =
  LftMap.fold (fun lft _ acc -> SS.union acc (Lft.lvars lft)) t SS.empty
