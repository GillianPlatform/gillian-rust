include Stdlib.Option
include Gillian.Utils.Option_utils

let get_or ~msg x =
  match x with
  | Some x -> x
  | None -> failwith msg
