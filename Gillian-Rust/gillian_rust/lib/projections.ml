open Gillian.Gil_syntax

type elem = Field of int

let pp_elem fmt = function Field i -> Fmt.int fmt i

type t = elem list

let elem_of_lit = function
  | Literal.Int i -> Field i
  | l             -> Fmt.failwith "invalid projection element %a" Literal.pp l

let of_lit_list lst : t = List.map elem_of_lit lst

let pp = Fmt.Dump.list pp_elem
