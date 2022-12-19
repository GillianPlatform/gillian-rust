include Stdlib.Result

let ok_or x msg =
  match x with
  | Ok x -> x
  | Error _ -> failwith msg
