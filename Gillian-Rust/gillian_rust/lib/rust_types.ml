open Gillian.Gil_syntax

type int_t = Isize | I8 | I16 | I32 | I64 | I128

type uint_t = Usize | U8 | U16 | U32 | U64 | U128

type t = Unit | Bool | Char | Int of int_t | Uint of uint_t

let of_lit = function
  | Literal.String str_ty -> (
      match str_ty with
      | "isize" -> Int Isize
      | "i8"    -> Int I8
      | "i16"   -> Int I16
      | "i32"   -> Int I32
      | "i64"   -> Int I64
      | "i128"  -> Int I128
      | "u8"    -> Uint U8
      | "u16"   -> Uint U16
      | "u32"   -> Uint U32
      | "u64"   -> Uint U64
      | "u128"  -> Uint U128
      | "()"    -> Unit
      | _       -> Fmt.failwith "Incorrect type \"%s\"" str_ty)
  | lit                   -> Fmt.failwith "Incorrect type %a" Literal.pp lit

let of_expr = function
  | Expr.Lit lit -> of_lit lit
  | other        -> Fmt.failwith "Incorrect type %a" Expr.pp other

let uninitialized_value = function
  | Unit -> Literal.Empty
  | Bool | Char | Int _ | Uint _ -> Undefined

let pp fmt t =
  Fmt.string fmt
    (match t with
    | Unit       -> "()"
    | Bool       -> "Bool"
    | Char       -> "Char"
    | Int Isize  -> "isize"
    | Int I8     -> "i8"
    | Int I16    -> "i16"
    | Int I32    -> "i32"
    | Int I64    -> "i64"
    | Int I128   -> "i128"
    | Uint Usize -> "usize"
    | Uint U8    -> "u8"
    | Uint U16   -> "u16"
    | Uint U32   -> "u32"
    | Uint U64   -> "u64"
    | Uint U128  -> "u128")
