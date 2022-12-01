module Infix = struct
  let ( .%[] ) arr idx =
    try Ok (Array.get arr idx) with Invalid_argument _ -> Error ()

  let ( .%[]<- ) vec idx value =
    try
      Ok
        (let copy = Array.copy vec in
         Array.set copy idx value;
         copy)
    with Invalid_argument _ -> Error ()
end

let override_range vec ~start ~size update =
  try
    Ok
      (let copy = Array.copy vec in
       for i = start to start + size - 1 do
         copy.(i) <- update copy.(i)
       done;
       copy)
  with Invalid_argument _ -> Error ()

let override_range_with_list vec ~start ~f list =
  let rec aux v idx = function
    | [] -> ()
    | x :: r ->
        v.(idx) <- f x;
        aux v (idx + 1) r
  in
  try
    Ok
      (let copy = Array.copy vec in
       aux copy start list;
       copy)
  with Invalid_argument _ -> Error ()

let sublist_map ~start ~size ~f vec =
  let rec aux idx acc =
    if idx < start then acc else aux (idx - 1) (f vec.(idx) :: acc)
  in
  aux (start + size - 1) []
