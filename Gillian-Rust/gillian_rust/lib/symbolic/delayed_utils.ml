module DR = Gillian.Monadic.Delayed_result
open DR.Syntax

module DR_list = struct
  let rec map f l =
    match l with
    | [] -> DR.ok []
    | a :: r ->
        let** a = f a in
        let++ r = map f r in
        a :: r

  let rec map_with_lk ~lk f l =
    match l with
    | [] -> DR.ok ([], lk)
    | a :: r ->
        let** a, lk = f ~lk a in
        let++ r, lk = map_with_lk ~lk f r in
        (a :: r, lk)

  let rec map2 f la lb =
    match (la, lb) with
    | [], [] -> DR.ok []
    | a :: ra, b :: rb ->
        let** a = f a b in
        let++ r = map2 f ra rb in
        a :: r
    | _ -> failwith "dr_list_map_2: lists have different lengths"

  let override_range_with_list
      (lst : 'a list)
      ~(start : int)
      ~(f : 'b -> ('a, 'e) DR.t)
      (overrides : 'b list) : ('a list, 'e) DR.t =
    let rec override ovds lst =
      match (ovds, lst) with
      | [], lst -> DR.ok lst
      | o :: ovds, _ :: lst ->
          let** o = f o in
          let++ r = override ovds lst in
          o :: r
      | _, [] -> raise (Invalid_argument "set_nth: range outside bounds")
    in
    let rec find_start_and_override acc lst start =
      match (start, lst) with
      | 0, _ ->
          let++ lst = override overrides lst in
          List.rev_append acc lst
      | n, x :: r -> find_start_and_override (x :: acc) r (n - 1)
      | _, [] -> raise (Invalid_argument "set_nth: start outside bounds")
    in
    try find_start_and_override [] lst start
    with Invalid_argument _ -> DR.error Err.Invalid_list_op
end

module DR_option = struct
  let map f = function
    | None -> DR.ok None
    | Some x ->
        let++ x = f x in
        Some x
end
