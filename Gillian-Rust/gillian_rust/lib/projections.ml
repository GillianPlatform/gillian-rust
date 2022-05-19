open Gillian.Gil_syntax

type arith_kind = Wrapping | Classic

type elem =
  | Field    of int
  | Downcast of int
  | Index    of int
  | Cast     of Rust_types.t
  | Plus     of arith_kind * int

let pp_elem fmt =
  let str_ak = function Wrapping -> "w" | Classic -> "" in
  function
  | Field i     -> Fmt.int fmt i
  | Downcast i  -> Fmt.pf fmt "as_v(%d)" i
  | Index i     -> Fmt.pf fmt "[%d]" i
  | Cast ty     -> Fmt.pf fmt ">:%a" Rust_types.pp ty
  | Plus (k, i) -> Fmt.pf fmt "+%s(%d)" (str_ak k) i

type t = elem list

let elem_of_lit : Literal.t -> elem = function
  | LList [ String "f"; Int i ] -> Field (Z.to_int i)
  | LList [ String "d"; Int i ] -> Downcast (Z.to_int i)
  | LList [ String "i"; Int i ] -> Index (Z.to_int i)
  | LList [ String "c"; ty ] -> Cast (Rust_types.of_lit ty)
  | LList [ String "+"; Bool b; Int i ] ->
      Plus ((if b then Wrapping else Classic), Z.to_int i)
  | l -> Fmt.failwith "invalid projection element %a" Literal.pp l

let of_lit_list lst : t = List.map elem_of_lit lst

let lit_of_elem : elem -> Literal.t = function
  | Field i     -> LList [ String "f"; Int (Z.of_int i) ]
  | Downcast i  -> LList [ String "d"; Int (Z.of_int i) ]
  | Cast ty     -> LList [ String "c"; Rust_types.to_lit ty ]
  | Index i     -> LList [ String "i"; Int (Z.of_int i) ]
  | Plus (k, i) ->
      let wrapping = match k with Wrapping -> true | Classic -> false in
      LList [ String "+"; Bool wrapping; Int (Z.of_int i) ]

let to_lit_list t : Literal.t list = List.map lit_of_elem t
let pp = Fmt.Dump.list pp_elem

module Tree_path_or_whatever_you_want_to_call_it = struct
  type t
end

let resolve ~(genv : C_global_env.t) (p : t) :
    Tree_path_or_whatever_you_want_to_call_it.t =
  failwith "to implement"

let reduce ~(genv : C_global_env.t) (p : t) : t = failwith "to implement"

(** Takes a projection, and returns the index at the start of the slice,
    as well as the modified projection without the indexing done  *)
let rec slice_start = function
  | []          -> failwith "invalid slice pointer"
  | [ Index i ] -> (i, [])
  | x :: r      ->
      let i, r = slice_start r in
      (i, x :: r)
