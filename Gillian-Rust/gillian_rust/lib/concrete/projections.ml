open Gillian.Gil_syntax
(* module Partial_layout = Partial_layout *)

type arith_kind = Wrap | Overflow [@@deriving show, eq]

type op =
  | VField of int * Ty.t * int
  | Field of int * Ty.t
  | Downcast of int * Ty.t
  | Index of int * Ty.t * int
  | Cast of Ty.t * Ty.t
  | Plus of arith_kind * int * Ty.t
  | UPlus of arith_kind * int
[@@deriving show, eq]

let pp_elem fmt =
  let str_ak = function
    | Wrap -> "w"
    | Overflow -> ""
  in
  function
  | Field (i, ty) -> Fmt.pf fmt ".%d<%a>" i Ty.pp ty
  | VField (i, ty, vidx) -> Fmt.pf fmt ".%d<%a.%d>" i Ty.pp ty vidx
  | Downcast (i, ty) -> Fmt.pf fmt "<%a>as_v(%d)" Ty.pp ty i
  | Index (i, ty, sz) -> Fmt.pf fmt "[%d]<[%a; %d]>" i Ty.pp ty sz
  | Cast (from_ty, into_ty) -> Fmt.pf fmt "%a>%a" Ty.pp from_ty Ty.pp into_ty
  | Plus (k, i, ty) -> Fmt.pf fmt "+%s(%d)<%a>" (str_ak k) i Ty.pp ty
  | UPlus (k, i) -> Fmt.pf fmt "u+%s(%d)" (str_ak k) i

type t = op list

let op_of_lit : Literal.t -> op = function
  | LList [ String "f"; Int i; ty ] -> Field (Z.to_int i, Ty.of_lit ty)
  | LList [ String "vf"; Int i; ty; Int idx ] ->
      VField (Z.to_int i, Ty.of_lit ty, Z.to_int idx)
  | LList [ String "d"; Int i; ty ] -> Downcast (Z.to_int i, Ty.of_lit ty)
  | LList [ String "i"; Int i; ty; Int sz ] ->
      Index (Z.to_int i, Ty.of_lit ty, Z.to_int sz)
  | LList [ String "c"; ty_from; ty_into ] ->
      Cast (Ty.of_lit ty_from, Ty.of_lit ty_into)
  | LList [ String "+"; Bool b; Int i; ty ] ->
      Plus ((if b then Wrap else Overflow), Z.to_int i, Ty.of_lit ty)
  | l -> Fmt.failwith "invalid projection element %a" Literal.pp l

let of_lit_list lst : t = List.map op_of_lit lst

let lit_of_elem : op -> Literal.t =
  let is_wrap = function
    | Wrap -> Literal.Bool true
    | Overflow -> Bool false
  in
  function
  | Field (i, ty) -> LList [ String "f"; Int (Z.of_int i); Ty.to_lit ty ]
  | VField (i, ty, idx) ->
      LList [ String "vf"; Int (Z.of_int i); Ty.to_lit ty; Int (Z.of_int idx) ]
  | Downcast (i, ty) -> LList [ String "d"; Int (Z.of_int i); Ty.to_lit ty ]
  | Cast (from_ty, into_ty) ->
      LList [ String "c"; Ty.to_lit from_ty; Ty.to_lit into_ty ]
  | Index (i, ty, sz) ->
      LList [ String "i"; Int (Z.of_int i); Ty.to_lit ty; Int (Z.of_int sz) ]
  | Plus (k, i, ty) ->
      LList [ String "+"; is_wrap k; Int (Z.of_int i); Ty.to_lit ty ]
  | UPlus (k, i) -> LList [ String "u+"; is_wrap k; Int (Z.of_int i) ]

let to_lit_list t : Literal.t list = List.map lit_of_elem t
let pp = Fmt.Dump.list pp_elem
