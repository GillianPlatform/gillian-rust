include Stdlib.Result
include Gillian.Utils.Result_utils

let ok_or ~msg x =
  match x with
  | Ok x -> x
  | Error _ -> failwith msg

module Syntax = Gillian.Utils.Syntaxes.Result