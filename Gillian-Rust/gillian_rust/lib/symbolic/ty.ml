(** In Gillian-Rust, we use symbolic values to denote potentially polymorphic types.
    In our execution, types are simply passed around as values, which means we can pass
    polymorphic types as function inputs. *)

open Gillian.Gil_syntax
module Cty = Common.Ty

type int_ty = Cty.int_ty = Isize | I8 | I16 | I32 | I64 | I128
[@@deriving eq, yojson]

type uint_ty = Cty.uint_ty = Usize | U8 | U16 | U32 | U64 | U128
[@@deriving eq, yojson]

type scalar_ty = Cty.scalar_ty = Bool | Char | Int of int_ty | Uint of uint_ty
[@@deriving eq, yojson]

let scalar_ty_to_string = Cty.scalar_ty_of_string
let scalar_ty_of_string = Cty.scalar_ty_of_yojson
let pp_scalar = Cty.pp_scalar

type t =
  | Scalar of scalar_ty
  | Tuple of t list
  | Adt of (string * t list)
      (** This will have to be looked up in the global environment,
        For example List<u32> is Adt("List", [ u32 ] *)
  | Ref of { mut : bool; ty : t }
  | Array of { length : int; ty : t }
  | Slice of t
  | Unresolved of Expr.t
      (** A parameter in an ADT def, should be substituted before used *)
[@@deriving yojson, eq]
(* FIXME: type equality cannot be decided syntactically in theory. It has to be decided by SAT.
   But it requires a lot of changes in Projections and Partial_layout that I'm not ready to make yet. *)

let rec subst_params ~(subst : t list) t =
  match t with
  | Cty.Param i -> List.nth subst i
  | Cty.Scalar s -> Scalar s
  | Tuple l -> Tuple (List.map (subst_params ~subst) l)
  | Array { length; ty } -> Array { length; ty = subst_params ~subst ty }
  | Slice t -> Slice (subst_params ~subst t)
  | Ref { mut; ty } -> Ref { mut; ty = subst_params ~subst ty }
  | Adt (name, l) -> Adt (name, List.map (subst_params ~subst) l)

let rec of_lit = function
  | Literal.String str_ty ->
      Scalar
        (match str_ty with
        | "isize" -> Int Isize
        | "i8" -> Int I8
        | "i16" -> Int I16
        | "i32" -> Int I32
        | "i64" -> Int I64
        | "i128" -> Int I128
        | "usize" -> Uint Usize
        | "u8" -> Uint U8
        | "u16" -> Uint U16
        | "u32" -> Uint U32
        | "u64" -> Uint U64
        | "u128" -> Uint U128
        | "bool" -> Bool
        | "char" -> Char
        | _ -> Fmt.failwith "Incorrect scalar type \"%s\"" str_ty)
  | LList [ String "tuple"; LList l ] -> Tuple (List.map of_lit l)
  | LList [ String "adt"; String name; LList l ] ->
      let args = List.map of_lit l in
      Adt (name, args)
  | LList [ String "ref"; Bool mut; ty ] -> Ref { mut; ty = of_lit ty }
  | LList [ String "array"; ty; Int i ] ->
      Array { length = Z.to_int i; ty = of_lit ty }
  | LList [ String "slice"; ty ] -> Slice (of_lit ty)
  | lit -> Fmt.failwith "Incorrect type %a" Literal.pp lit

let rec of_expr : Expr.t -> t = function
  | Lit lit -> of_lit lit
  | EList [ Expr.Lit (String "tuple"); l ] -> Tuple (list_of_list_expr l)
  | EList [ Expr.Lit (String "adt"); Expr.Lit (String name); l ] ->
      Adt (name, list_of_list_expr l)
  | EList [ Expr.Lit (String "ref"); Expr.Lit (Bool mut); ty ] ->
      Ref { mut; ty = of_expr ty }
  | EList [ Expr.Lit (String "array"); ty; Expr.Lit (Int i) ] ->
      Array { length = Z.to_int i; ty = of_expr ty }
  | EList [ Expr.Lit (String "slice"); ty ] -> Slice (of_expr ty)
  | e -> Unresolved e

and list_of_list_expr = function
  | Expr.EList l -> List.map of_expr l
  | Lit (LList l) -> List.map of_lit l
  | _ -> Fmt.failwith "Incorrect type list"

let rec to_expr = function
  | Scalar s ->
      Expr.Lit
        (Literal.String
           (match s with
           | Int Isize -> "isize"
           | Int I8 -> "i8"
           | Int I16 -> "i16"
           | Int I32 -> "i32"
           | Int I64 -> "i64"
           | Int I128 -> "i128"
           | Uint Usize -> "usize"
           | Uint U8 -> "u8"
           | Uint U16 -> "u16"
           | Uint U32 -> "u32"
           | Uint U64 -> "u64"
           | Uint U128 -> "u128"
           | Bool -> "bool"
           | Char -> "char"))
  | Tuple fls -> EList [ Lit (String "tuple"); EList (List.map to_expr fls) ]
  | Adt (x, a) ->
      let args = List.map to_expr a in
      EList [ Lit (String "adt"); Lit (String x); EList args ]
  | Ref { mut; ty } -> EList [ Lit (String "ref"); Lit (Bool mut); to_expr ty ]
  | Array { length; ty } ->
      EList [ Lit (String "array"); to_expr ty; Lit (Int (Z.of_int length)) ]
  | Slice ty -> EList [ Lit (String "slice"); to_expr ty ]
  | Unresolved e -> e

let rec pp ft t =
  let open Fmt in
  match t with
  | Scalar s -> pp_scalar ft s
  | Tuple t ->
      let pp_tuple = parens (list ~sep:comma pp) in
      pp_tuple ft t
  | Adt (s, args) -> pf ft "%s<%a>" s (list ~sep:comma pp) args
  | Ref { mut; ty } -> Fmt.pf ft "&%s%a" (if mut then "mut " else "") pp ty
  | Array { length; ty } -> Fmt.pf ft "[%a; %d]" pp ty length
  | Slice ty -> Fmt.pf ft "[%a]" pp ty
  | Unresolved e -> Fmt.pf ft "%a" Expr.pp e

let rec substitution ~subst_expr t =
  let rec_call = substitution ~subst_expr in
  match t with
  | Scalar _ -> t
  | Tuple t -> Tuple (List.map rec_call t)
  | Adt (name, l) -> Adt (name, List.map rec_call l)
  | Ref { mut; ty } -> Ref { mut; ty = rec_call ty }
  | Array { length; ty } -> Array { length; ty = rec_call ty }
  | Slice t -> Slice (rec_call t)
  | Unresolved e -> Unresolved (subst_expr e)

let slice_elements = function
  | Slice t -> t
  | _ -> failwith "not a slice type"