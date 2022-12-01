open S_err

let set_nth lst idx value =
  let rec aux lst idx =
    match (idx, lst) with
    | 0, _ :: r -> value :: r
    | n, x :: r -> x :: aux r (n - 1)
    | _, [] ->
        raise
          (Invalid_argument "List_utils.set_nth: index greater than list length")
  in
  if idx < 0 then raise (Invalid_argument "List_utils.set_nth: negative index")
  else aux lst idx

module Infix = struct
  let ( .%[] ) lst idx =
    try Ok (List.nth lst idx) with Invalid_argument _ -> Error Invalid_list_op

  let ( .%[]<- ) lst idx value =
    try Ok (set_nth lst idx value)
    with Invalid_argument _ -> Error Invalid_list_op
end

let override_range lst ~start ~size update =
  let rec override lst size =
    if size > 0 then
      match lst with
      | [] -> raise (Invalid_argument "set_nth: range outside bounds")
      | x :: r -> update x :: override r (size - 1)
    else lst
  in
  let rec find_start_and_override lst start =
    match (start, lst) with
    | 0, _ -> override lst size
    | n, x :: r -> x :: find_start_and_override r (n - 1)
    | _, [] -> raise (Invalid_argument "set_nth: start outside bounds")
  in
  try Ok (find_start_and_override lst start)
  with Invalid_argument _ -> Error Invalid_list_op

let override_range_with_list lst ~start ~f overrides =
  let rec override ovds lst =
    match (ovds, lst) with
    | [], lst -> lst
    | o :: ovds, _ :: lst -> f o :: override ovds lst
    | _, [] -> raise (Invalid_argument "set_nth: range outside bounds")
  in
  let rec find_start_and_override lst start =
    match (start, lst) with
    | 0, _ -> override overrides lst
    | n, x :: r -> x :: find_start_and_override r (n - 1)
    | _, [] -> raise (Invalid_argument "set_nth: start outside bounds")
  in
  try Ok (find_start_and_override lst start)
  with Invalid_argument _ -> Error Invalid_list_op

let sublist_map ~start ~size ~f lst =
  List.to_seq lst |> Seq.drop start |> Seq.take size |> Seq.map f |> List.of_seq
