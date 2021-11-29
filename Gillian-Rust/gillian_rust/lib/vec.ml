type 'a vec = 'a array

let ( .%[] ) vec idx =
  try Ok (Array.get vec idx) with Invalid_argument _ -> Error ()

let ( .%[]<- ) vec idx value =
  try
    Ok
      (let copy = Array.copy vec in
       Array.unsafe_set copy idx value;
       copy)
  with Invalid_argument _ -> Error ()

let map = Array.map

let fold_left = Array.fold_left

let of_list l = Array.of_list l

let to_list l = Array.to_list l

let pp = Fmt.array