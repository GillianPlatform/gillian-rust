open Gillian.Gil_syntax
(* module Partial_layout = Partial_layout *)

type arith_kind = Wrap | Overflow [@@deriving show]

type op =
  | VField of int * Ty.t * int
  | Field of int * Ty.t
  | Index of int * Ty.t * int
  | Cast of Ty.t * Ty.t
  | Plus of arith_kind * int * Ty.t
  | UPlus of arith_kind * int
[@@deriving show]

let pp_elem fmt =
  let str_ak = function
    | Wrap -> "w"
    | Overflow -> ""
  in
  function
  | Field (i, ty) -> Fmt.pf fmt ".%d<%a>" i Ty.pp ty
  | VField (i, ty, vidx) -> Fmt.pf fmt ".%d<%a.%d>" i Ty.pp ty vidx
  | Index (i, ty, sz) -> Fmt.pf fmt "[%d]<[%a; %d]>" i Ty.pp ty sz
  | Cast (from_ty, into_ty) -> Fmt.pf fmt "%a>%a" Ty.pp from_ty Ty.pp into_ty
  | Plus (k, i, ty) -> Fmt.pf fmt "+%s(%d)<%a>" (str_ak k) i Ty.pp ty
  | UPlus (k, i) -> Fmt.pf fmt "u+%s(%d)" (str_ak k) i

type t = { base : Expr.t option; from_base : op list }

let root = { base = None; from_base = [] }

let op_of_lit : Literal.t -> op = function
  | LList [ String "f"; Int i; ty ] -> Field (Z.to_int i, Ty.of_lit ty)
  | LList [ String "vf"; Int i; ty; Int idx ] ->
      VField (Z.to_int i, Ty.of_lit ty, Z.to_int idx)
  | LList [ String "i"; Int i; ty; Int sz ] ->
      Index (Z.to_int i, Ty.of_lit ty, Z.to_int sz)
  | LList [ String "c"; ty_from; ty_into ] ->
      Cast (Ty.of_lit ty_from, Ty.of_lit ty_into)
  | LList [ String "+"; Bool b; Int i; ty ] ->
      Plus ((if b then Wrap else Overflow), Z.to_int i, Ty.of_lit ty)
  | l -> Fmt.failwith "invalid projection literal element %a" Literal.pp l

let op_of_expr : Expr.t -> op = function
  | Lit lit -> op_of_lit lit
  | EList [ Lit (String "f"); Lit (Int i); ty ] ->
      Field (Z.to_int i, Ty.of_expr ty)
  | EList [ Lit (String "vf"); Lit (Int i); ty; Lit (Int idx) ] ->
      VField (Z.to_int i, Ty.of_expr ty, Z.to_int idx)
  | EList [ Lit (String "i"); Lit (Int i); ty; Lit (Int sz) ] ->
      Index (Z.to_int i, Ty.of_expr ty, Z.to_int sz)
  | EList [ Lit (String "c"); ty_from; ty_into ] ->
      Cast (Ty.of_expr ty_from, Ty.of_expr ty_into)
  | EList [ Lit (String "+"); Lit (Bool b); Lit (Int i); ty ] ->
      Plus ((if b then Wrap else Overflow), Z.to_int i, Ty.of_expr ty)
  | e -> Fmt.failwith "invalid projection expression element %a" Expr.pp e

let of_lit_list lst : t = { base = None; from_base = List.map op_of_lit lst }

let expr_of_elem : op -> Expr.t =
  let is_wrap = function
    | Wrap -> Expr.Lit (Bool true)
    | Overflow -> Expr.Lit (Bool false)
  in
  function
  | Field (i, ty) ->
      EList [ Lit (String "f"); Lit (Int (Z.of_int i)); Ty.to_expr ty ]
  | VField (i, ty, idx) ->
      EList
        [
          Lit (String "vf");
          Lit (Int (Z.of_int i));
          Ty.to_expr ty;
          Lit (Int (Z.of_int idx));
        ]
  | Index (i, ty, sz) ->
      EList
        [
          Lit (String "i");
          Lit (Int (Z.of_int i));
          Ty.to_expr ty;
          Lit (Int (Z.of_int sz));
        ]
  | Cast (from_ty, into_ty) ->
      EList [ Lit (String "c"); Ty.to_expr from_ty; Ty.to_expr into_ty ]
  | Plus (k, i, ty) ->
      EList
        [ Lit (String "+"); is_wrap k; Lit (Int (Z.of_int i)); Ty.to_expr ty ]
  | UPlus (k, i) ->
      EList [ Lit (String "u+"); is_wrap k; Lit (Int (Z.of_int i)) ]

let to_expr_list t : Expr.t list = List.map expr_of_elem t

let substitution_in_op ~subst_expr (op : op) =
  match op with
  | Field (i, ty) -> Field (i, Ty.substitution ~subst_expr ty)
  | VField (i, ty, idx) -> VField (i, Ty.substitution ~subst_expr ty, idx)
  | Index (i, ty, sz) -> Index (i, Ty.substitution ~subst_expr ty, sz)
  | Cast (from_ty, into_ty) ->
      Cast
        ( Ty.substitution ~subst_expr from_ty,
          Ty.substitution ~subst_expr into_ty )
  | Plus (k, i, ty) -> Plus (k, i, Ty.substitution ~subst_expr ty)
  | UPlus (k, i) -> UPlus (k, i)

let substitution ~subst_expr { base; from_base } =
  {
    base = Option.map subst_expr base;
    from_base = List.map (substitution_in_op ~subst_expr) from_base;
  }

let to_expr { base; from_base } =
  let from_base = Expr.EList (List.map expr_of_elem from_base) in
  match base with
  | None -> from_base
  | Some b -> Expr.list_cat b from_base

let of_expr (expr : Expr.t) : t =
  match expr with
  | EList l -> { base = None; from_base = List.map op_of_expr l }
  | Lit (LList l) -> { base = None; from_base = List.map op_of_lit l }
  | NOp (LstCat, [ b; EList l ]) ->
      { base = Some b; from_base = List.map op_of_expr l }
  | e ->
      Logging.verbose (fun m ->
          m "of_expr is assigning everything to base %a" Expr.pp e);
      { base = Some e; from_base = [] }

let pp_from_base ft from_base = (Fmt.Dump.list pp_elem) ft from_base

let pp ft t =
  let pp_base ft = function
    | None -> ()
    | Some b ->
        Expr.pp ft b;
        Fmt.string ft " ++ "
  in
  pp_base ft t.base;
  pp_from_base ft t.from_base
