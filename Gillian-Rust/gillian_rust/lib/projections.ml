open Gillian.Gil_syntax

type elem = Field of int | Downcast of int

let pp_elem fmt = function
  | Field i    -> Fmt.int fmt i
  | Downcast i -> Fmt.pf fmt "as(%d)" i

type t = elem list

let elem_of_lit : Literal.t -> elem = function
  | LList [ String "f"; Int i ] -> Field i
  | LList [ String "d"; Int i ] -> Downcast i
  | l -> Fmt.failwith "invalid projection element %a" Literal.pp l

let of_lit_list lst : t = List.map elem_of_lit lst

let lit_of_elem : elem -> Literal.t = function
  | Field i    -> LList [ String "f"; Int i ]
  | Downcast i -> LList [ String "d"; Int i ]

let to_lit_list t : Literal.t list = List.map lit_of_elem t

let pp = Fmt.Dump.list pp_elem
