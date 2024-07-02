(** In Gillian-Rust, we use symbolic values to denote potentially polymorphic types.
    In our execution, types are simply passed around as values, which means we can pass
    polymorphic types as function inputs. *)

open Gillian.Gil_syntax
module Cty = Common.Ty

type int_ty = Cty.int_ty = Isize | I8 | I16 | I32 | I64 | I128
[@@deriving eq, yojson, ord]

type uint_ty = Cty.uint_ty = Usize | U8 | U16 | U32 | U64 | U128
[@@deriving eq, yojson, ord]

type scalar_ty = Cty.scalar_ty = Bool | Char | Int of int_ty | Uint of uint_ty
[@@deriving eq, yojson, ord]

let size_of_scalar = function
  | Bool | Int I8 | Uint U8 -> 1
  | Int I16 | Uint U16 -> 2
  | Int I32 | Uint U32 | Char -> 4
  | Int I64 | Uint U64 -> 8
  | Int I128 | Uint U128 -> 16
  | Int Isize | Uint Usize -> 8
(* Should be made parametric at some point *)

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
  | Ptr of { mut : bool; ty : t }
  | Array of { length : Expr.t; ty : t }
  | Slice of t
  | Str (* More or less slice of char I guess *)
  | Unresolved of Expr.t
      (** A parameter in an ADT def, should be substituted before used *)
[@@deriving yojson, eq, ord]
(* FIXME: type equality cannot be decided syntactically in theory. It has to be decided by SAT.
   But it requires a lot of changes in Projections and Partial_layout that I'm not ready to make yet.
   However, as it is right now, nothing is unsound, simply less complete. *)

let rec lvars =
  let open Gillian.Utils.Containers in
  function
  | Unresolved expr -> Expr.lvars expr
  | Scalar _ | Str -> SS.empty
  | Tuple l -> List.fold_left (fun acc t -> SS.union acc (lvars t)) SS.empty l
  | Adt (_, l) ->
      List.fold_left (fun acc t -> SS.union acc (lvars t)) SS.empty l
  | Array { length; ty } -> SS.union (Expr.lvars length) (lvars ty)
  | Ref { ty; _ } | Ptr { ty; _ } | Slice ty -> lvars ty

let rec sem_equal a b =
  let open Formula.Infix in
  match (a, b) with
  | Scalar a, Scalar b -> Cty.equal_scalar_ty a b |> Formula.of_bool
  | Tuple a, Tuple b ->
      List.fold_left2
        (fun acc tyl tyr -> acc #&& (sem_equal tyl tyr))
        Formula.True a b
  | Adt (name_a, args_a), Adt (name_b, args_b) ->
      (String.equal name_a name_b |> Formula.of_bool)
      #&& (List.fold_left2
             (fun acc tyl tyr -> acc #&& (sem_equal tyl tyr))
             Formula.True args_a args_b)
  | Ref { mut = mut_a; ty = ty_a }, Ref { mut = mut_b; ty = ty_b }
  | Ptr { mut = mut_a; ty = ty_a }, Ptr { mut = mut_b; ty = ty_b } ->
      (mut_a = mut_b |> Formula.of_bool) #&& (sem_equal ty_a ty_b)
  | ( Array { length = length_a; ty = ty_a },
      Array { length = length_b; ty = ty_b } ) ->
      length_a #== length_b #&& (sem_equal ty_a ty_b)
  | Slice a, Slice b -> sem_equal a b
  | Unresolved left, Unresolved right -> left #== right
  | Str, Str -> Formula.True
  | _ -> Formula.False

let syntactic_equal = equal

let rec subst_params ~(subst : t list) t =
  match t with
  | Cty.Param i -> List.nth subst i
  | Cty.Scalar s -> Scalar s
  | Tuple l -> Tuple (List.map (subst_params ~subst) l)
  | Array { length; ty } ->
      Array { length = Expr.int length; ty = subst_params ~subst ty }
  | Slice t -> Slice (subst_params ~subst t)
  | Ref { mut; ty } -> Ref { mut; ty = subst_params ~subst ty }
  | Ptr { mut; ty } -> Ptr { mut; ty = subst_params ~subst ty }
  | Adt (name, l) -> Adt (name, List.map (subst_params ~subst) l)

let rec of_lit = function
  | Literal.String "str" -> Str
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
  | LList [ String "ptr"; Bool mut; ty ] -> Ptr { mut; ty = of_lit ty }
  | LList [ String "array"; ty; length ] ->
      Array { length = Lit length; ty = of_lit ty }
  | LList [ String "slice"; ty ] -> Slice (of_lit ty)
  | lit -> Fmt.failwith "Incorrect type %a" Literal.pp lit

let rec of_expr : Expr.t -> t = function
  | Lit lit -> of_lit lit
  | EList [ Expr.Lit (String "tuple"); l ] -> Tuple (list_of_list_expr l)
  | EList [ Expr.Lit (String "adt"); Expr.Lit (String name); l ] ->
      Adt (name, list_of_list_expr l)
  | EList [ Expr.Lit (String "ref"); Expr.Lit (Bool mut); ty ] ->
      Ref { mut; ty = of_expr ty }
  | EList [ Expr.Lit (String "ptr"); Expr.Lit (Bool mut); ty ] ->
      Ptr { mut; ty = of_expr ty }
  | EList [ Expr.Lit (String "array"); ty; length ] ->
      Array { length; ty = of_expr ty }
  | EList [ Expr.Lit (String "slice"); ty ] -> Slice (of_expr ty)
  | e -> Unresolved e

and list_of_list_expr = function
  | Expr.EList l -> List.map of_expr l
  | Lit (LList l) -> List.map of_lit l
  | _ -> Fmt.failwith "Incorrect type list"

let rec to_expr = function
  | Scalar s ->
      Expr.string
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
  | Tuple fls -> EList [ Lit (String "tuple"); EList (List.map to_expr fls) ]
  | Adt (x, a) ->
      let args = List.map to_expr a in
      EList [ Lit (String "adt"); Lit (String x); EList args ]
  | Ref { mut; ty } -> EList [ Lit (String "ref"); Lit (Bool mut); to_expr ty ]
  | Ptr { mut; ty } -> EList [ Lit (String "ptr"); Lit (Bool mut); to_expr ty ]
  | Array { length; ty } -> EList [ Lit (String "array"); to_expr ty; length ]
  | Slice ty -> EList [ Lit (String "slice"); to_expr ty ]
  | Str -> Expr.string "str"
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
  | Ptr { mut; ty } -> Fmt.pf ft "*%s %a" (if mut then "mut" else "const") pp ty
  | Array { length; ty } -> Fmt.pf ft "[%a ; %a]" pp ty Expr.pp length
  | Slice ty -> Fmt.pf ft "[%a]" pp ty
  | Str -> Fmt.string ft "str"
  | Unresolved e -> Fmt.pf ft "%a" Expr.pp e

let rec substitution ~subst_expr t =
  let rec_call = substitution ~subst_expr in
  match t with
  | Scalar _ | Str -> t
  | Tuple t -> Tuple (List.map rec_call t)
  | Adt (name, l) -> Adt (name, List.map rec_call l)
  | Ref { mut; ty } -> Ref { mut; ty = rec_call ty }
  | Ptr { mut; ty } -> Ptr { mut; ty = rec_call ty }
  | Array { length; ty } ->
      Array { length = subst_expr length; ty = rec_call ty }
  | Slice t -> Slice (rec_call t)
  | Unresolved e -> Unresolved (subst_expr e)

let array ty length = Array { length; ty }

let is_array_of ~array_ty ~inner_ty =
  match array_ty with
  | Array { ty; _ } -> equal ty inner_ty
  | _ -> false

let slice_elements = function
  | Slice t -> t
  | _ -> failwith "not a slice type"

let fields ~tyenv ty =
  match ty with
  | Adt (name, subst) -> (
      match Common.Tyenv.adt_def ~tyenv name with
      | Struct (_, fields) ->
          List.map (fun (_, cty) -> subst_params ~subst cty) fields
      | _ -> Fmt.failwith "Not a structure: %a" pp ty)
  | Tuple tys -> tys
  | _ -> Fmt.failwith "Not a structure or tuple %a" pp ty

let variant_fields ~tyenv ~idx ty =
  match ty with
  | Adt (name, subst) -> (
      match Common.Tyenv.adt_def ~tyenv name with
      | Enum variants ->
          let _, fields = List.nth variants idx in
          List.map (subst_params ~subst) fields
      | _ -> Fmt.failwith "Not an enum: %a" pp ty)
  | _ -> Fmt.failwith "Not an enum: %a" pp ty

let array_inner ty =
  match ty with
  | Array { ty; _ } -> ty
  | _ -> Fmt.failwith "array_inner: %a is not an array" pp ty

let array_components ty =
  match ty with
  | Array { ty; length } -> (ty, length)
  | _ -> Fmt.failwith "array_components: %a is not an array" pp ty
