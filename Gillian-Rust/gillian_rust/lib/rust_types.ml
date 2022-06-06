open Gillian.Gil_syntax

type int_t = Isize | I8 | I16 | I32 | I64 | I128 [@@deriving eq]
type uint_t = Usize | U8 | U16 | U32 | U64 | U128 [@@deriving eq]
type scalar_t = Bool | Char | Int of int_t | Uint of uint_t [@@deriving eq]
type repr_t = ReprC | ReprRust [@@deriving eq]

type t =
  | Scalar of scalar_t
  | Tuple of t list
  | Struct of repr_t * (string * t) list
  | Enum of (string * t list) list
      (** Each variant has a name and the type of the list of fields.
          Maybe I should add the name of each field for each variant? *)
  | Named of string
      (** This will have to be looked up in the global environment *)
  | Ref of { mut : bool; ty : t }
  | Array of { length : int; ty : t }
  | Slice of t
[@@deriving eq]

let name_exn = function
  | Named s -> s
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
  | LList [ String "adt"; String name ] -> Named name
  | LList [ String "struct"; LList l; repr ] ->
      let parse_field = function
        | Literal.LList [ String field_name; ty ] -> (field_name, of_lit ty)
        | _ -> failwith "Invalid struct field"
      in
      let parse_repr = function
        | Literal.String "c" -> ReprC
        | Literal.String "rust" -> ReprRust
        | _ -> failwith "invalid repr for struct"
      in
      Struct (parse_repr repr, List.map parse_field l)
  | LList [ String "variant"; LList l ] ->
      let parse_variant = function
        | Literal.LList [ String variant_name; LList tys ] ->
            (variant_name, List.map of_lit tys)
        | _ -> failwith "Invalid enum field"
      in
      Enum (List.map parse_variant l)
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
  | Named x -> LList [ String "adt"; String x ]
  | Struct (_, fields) ->
      let make_field (field_name, ty) =
        Literal.LList [ String field_name; to_lit ty ]
      in
      LList [ String "struct"; LList (List.map make_field fields) ]
  | Enum variants ->
      let make_variant (vname, tys) =
        Literal.LList [ String vname; LList (List.map to_lit tys) ]
      in
      LList [ String "variant"; LList (List.map make_variant variants) ]
  | Ref { mut; ty } -> LList [ String "ref"; Bool mut; to_lit ty ]
  | Array { length; ty } ->
      LList [ String "array"; to_lit ty; Int (Z.of_int length) ]
  | Slice t -> LList [ String "slice"; to_lit t ]

let no_fields_for_downcast ty d =
  match ty with
  | Enum l -> (
      match snd (List.nth l d) with
      | [] -> true
      | _ -> false)
  | _ -> Fmt.failwith "[no_fields_for_downcast] Not an enum!"

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
  | Named s -> string ft s
  | Ref { mut; ty } -> Fmt.pf ft "&%s%a" (if mut then "mut " else "") pp ty
  | Array { length; ty } -> Fmt.pf ft "[%a; %d]" pp ty length
  | Slice ty -> Fmt.pf ft "[%a]" pp ty

let slice_elements = function
  | Slice t -> t
  | _ -> failwith "not a slice type"
