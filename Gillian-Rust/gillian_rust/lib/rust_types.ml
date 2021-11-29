open Gillian.Gil_syntax

type int_t = Isize | I8 | I16 | I32 | I64 | I128

type uint_t = Usize | U8 | U16 | U32 | U64 | U128

type scalar_t = Unit | Bool | Char | Int of int_t | Uint of uint_t

type t = Scalar of scalar_t | Tuple of t list

let rec of_lit = function
  | Literal.String str_ty ->
      Scalar
        (match str_ty with
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
  | LList [ String "tuple"; LList l ] -> Tuple (List.map of_lit l)
  (* | Literal.LList  *)
  | lit -> Fmt.failwith "Incorrect type %a" Literal.pp lit

let of_expr = function
  | Expr.Lit lit -> of_lit lit
  | other        -> Fmt.failwith "Incorrect type %a" Expr.pp other

let pp_scalar fmt t =
  let str = Fmt.string fmt in
  match t with
  | Unit       -> str "()"
  | Bool       -> str "bool"
  | Char       -> str "char"
  | Int Isize  -> str "isize"
  | Int I8     -> str "i8"
  | Int I16    -> str "i16"
  | Int I32    -> str "i32"
  | Int I64    -> str "i64"
  | Int I128   -> str "i128"
  | Uint Usize -> str "usize"
  | Uint U8    -> str "u8"
  | Uint U16   -> str "u16"
  | Uint U32   -> str "u32"
  | Uint U64   -> str "u64"
  | Uint U128  -> str "u128"

let rec pp fmt t =
  match t with
  | Scalar s -> pp_scalar fmt s
  | Tuple t  ->
      let pp_tuple =
        let open Fmt in
        parens (list ~sep:comma pp)
      in
      pp_tuple fmt t