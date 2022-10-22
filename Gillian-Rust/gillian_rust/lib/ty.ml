open Gillian.Gil_syntax

type int_ty = Isize | I8 | I16 | I32 | I64 | I128 [@@deriving eq]
type uint_ty = Usize | U8 | U16 | U32 | U64 | U128 [@@deriving eq]
type scalar_ty = Bool | Char | Int of int_ty | Uint of uint_ty [@@deriving eq]
type repr = ReprC | ReprRust [@@deriving eq, yojson]

let scalar_ty_to_string = function
  | Bool -> "bool"
  | Char -> "char"
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

let scalar_ty_of_string = function
  | "bool" -> Ok Bool
  | "char" -> Ok Char
  | "isize" -> Ok (Int Isize)
  | "i8" -> Ok (Int I8)
  | "i16" -> Ok (Int I16)
  | "i32" -> Ok (Int I32)
  | "i64" -> Ok (Int I64)
  | "i128" -> Ok (Int I128)
  | "usize" -> Ok (Uint Usize)
  | "u8" -> Ok (Uint U8)
  | "u16" -> Ok (Uint U16)
  | "u32" -> Ok (Uint U32)
  | "u64" -> Ok (Uint U64)
  | "u128" -> Ok (Uint U128)
  | s -> Fmt.error "invalid scalar type string: %s" s

let scalar_ty_of_yojson = function
  | `String s -> scalar_ty_of_string s
  | js ->
      Fmt.failwith "invalid scalar type json: %a"
        (Yojson.Safe.pretty_print ~std:true)
        js

let scalar_ty_to_yojson s = `String (scalar_ty_to_string s)

type t =
  | Scalar of scalar_ty
  | Tuple of t list
  | Adt of string
      (** This will have to be looked up in the global environment *)
  | Ref of { mut : bool; ty : t }
  | Array of { length : int; ty : t }
  | Slice of t
[@@deriving eq, yojson]

let name_exn = function
  | Adt s -> s
  | _ -> raise (Invalid_argument "Not a valid name!")

let is_slice_of a b =
  match (a, b) with
  | Slice t1, Array { ty = t2; _ } -> equal t1 t2
  | _ -> false

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
  | LList [ String "adt"; String name ] -> Adt name
  | LList [ String "ref"; Bool mut; ty ] -> Ref { mut; ty = of_lit ty }
  | LList [ String "array"; ty; Int i ] ->
      Array { length = Z.to_int i; ty = of_lit ty }
  | LList [ String "slice"; ty ] -> Slice (of_lit ty)
  | lit -> Fmt.failwith "Incorrect type %a" Literal.pp lit

let rec to_lit = function
  | Scalar s ->
      Literal.String
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
        | Char -> "char")
  | Tuple fls -> LList [ String "tuple"; LList (List.map to_lit fls) ]
  | Adt x -> LList [ String "adt"; String x ]
  | Ref { mut; ty } -> LList [ String "ref"; Bool mut; to_lit ty ]
  | Array { length; ty } ->
      LList [ String "array"; to_lit ty; Int (Z.of_int length) ]
  | Slice t -> LList [ String "slice"; to_lit t ]

let pp_scalar fmt t =
  let str = Fmt.string fmt in
  match t with
  | Bool -> str "bool"
  | Char -> str "char"
  | Int Isize -> str "isize"
  | Int I8 -> str "i8"
  | Int I16 -> str "i16"
  | Int I32 -> str "i32"
  | Int I64 -> str "i64"
  | Int I128 -> str "i128"
  | Uint Usize -> str "usize"
  | Uint U8 -> str "u8"
  | Uint U16 -> str "u16"
  | Uint U32 -> str "u32"
  | Uint U64 -> str "u64"
  | Uint U128 -> str "u128"

let rec pp ft t =
  let open Fmt in
  match t with
  | Scalar s -> pp_scalar ft s
  | Tuple t ->
      let pp_tuple = parens (list ~sep:comma pp) in
      pp_tuple ft t
  | Adt s -> string ft s
  | Ref { mut; ty } -> Fmt.pf ft "&%s%a" (if mut then "mut " else "") pp ty
  | Array { length; ty } -> Fmt.pf ft "[%a; %d]" pp ty length
  | Slice ty -> Fmt.pf ft "[%a]" pp ty

module Adt_def = struct
  type ty = t [@@deriving yojson]
  (* Necessary because ppx_deriving_yojson doesn't work for [nonrec] things. *)

  type t =
    | Enum of (string * ty list) list
        (** Each variant has a name and the type of the list of fields.
        Maybe I should add the name of each field for each variant? *)
    | Struct of repr * (string * ty) list
  [@@deriving yojson]

  let no_fields_for_downcast ty d =
    match ty with
    | Enum l -> (
        match snd (List.nth l d) with
        | [] -> true
        | _ -> false)
    | _ -> Fmt.failwith "[no_fields_for_downcast] Not an enum!"

  let pp ft t =
    let open Fmt in
    match t with
    | Struct (repr, f) ->
        let pp_repr ft = function
          | ReprC -> pf ft "#[repr(C)] "
          | ReprRust -> pf ft "#[repr(Rust)] "
        in
        let pp_struct =
          braces (list ~sep:comma (pair ~sep:(Fmt.any ": ") Fmt.string pp))
        in
        (pair ~sep:nop pp_repr pp_struct) ft (repr, f)
    | Enum v ->
        let pp_variant ftt (name, tys) =
          pf ftt "| %s%a" name (parens (list ~sep:comma pp)) tys
        in
        (list ~sep:sp pp_variant) ft v
end

let slice_elements = function
  | Slice t -> t
  | _ -> failwith "not a slice type"
