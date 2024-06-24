open Gillian.Gil_syntax
(* module Partial_layout = Partial_layout *)

type arith_kind = Wrap | Overflow [@@deriving show, yojson, eq]

type op =
  | VField of int * Ty.t * int
  | Field of int * Ty.t
  | Index of Expr.t * Ty.t * int
  | Plus of arith_kind * Expr.t * Ty.t
  | UPlus of arith_kind * Expr.t
[@@deriving yojson, eq]

let variant = function
  | VField (i, _, _) -> Some i
  | _ -> None

let pp_op fmt =
  let str_ak = function
    | Wrap -> "w"
    | Overflow -> ""
  in
  function
  | Field (i, ty) -> Fmt.pf fmt ".%d<%a>" i Ty.pp ty
  | VField (i, ty, vidx) -> Fmt.pf fmt ".%d<%a.%d>" i Ty.pp ty vidx
  | Index (i, ty, sz) -> Fmt.pf fmt "[%a]<[%a; %d]>" Expr.pp i Ty.pp ty sz
  | Plus (k, i, ty) -> Fmt.pf fmt "+%s(%a)<%a>" (str_ak k) Expr.pp i Ty.pp ty
  | UPlus (k, i) -> Fmt.pf fmt "u+%s(%a)" (str_ak k) Expr.pp i

type path = op list [@@deriving yojson, eq]

let pp_path = Fmt.Dump.list pp_op

type t = { base : Expr.t option; from_base : path } [@@deriving yojson]

let root = { base = None; from_base = [] }

(** Returns the type at the base, if possible to find *)
let rec base_ty ~(leaf_ty : Ty.t) (path : path) =
  match path with
  | [] -> leaf_ty
  | (Field (_, ty) | VField (_, ty, _) | Index (_, ty, _)) :: _ -> ty
  | Plus (_akind, ofs, ty) :: r -> (
      let next_ty = base_ty ~leaf_ty r in
      if Ty.equal next_ty ty then
        Array { ty; length = Expr.(Infix.(ofs + one_i)) }
      else
        match next_ty with
        | Array { ty = ty'; length } when Ty.equal ty ty' ->
            Array { ty; length = Expr.Infix.(length + ofs) }
        | _ ->
            Fmt.failwith "cannot figure out base_ty:@\nleaf_ty: %a@\npath: %a"
              Ty.pp leaf_ty pp_path path)
  | UPlus _ :: _ -> failwith "reduced to uplus too early"

let op_of_lit : Literal.t -> op = function
  | LList [ String "f"; Int i; ty ] -> Field (Z.to_int i, Ty.of_lit ty)
  | LList [ String "vf"; Int i; ty; Int idx ] ->
      VField (Z.to_int i, Ty.of_lit ty, Z.to_int idx)
  | LList [ String "i"; (Int _ as i); ty; Int sz ] ->
      Index (Expr.Lit i, Ty.of_lit ty, Z.to_int sz)
  | LList [ String "+"; Bool b; (Int _ as i); ty ] ->
      Plus ((if b then Wrap else Overflow), Expr.Lit i, Ty.of_lit ty)
  | l -> Fmt.failwith "invalid projection literal element %a" Literal.pp l

let op_of_expr : Expr.t -> op = function
  | Lit lit -> op_of_lit lit
  | EList [ Lit (String "f"); Lit (Int i); ty ] ->
      Field (Z.to_int i, Ty.of_expr ty)
  | EList [ Lit (String "vf"); Lit (Int i); ty; Lit (Int idx) ] ->
      VField (Z.to_int i, Ty.of_expr ty, Z.to_int idx)
  | EList [ Lit (String "i"); i; ty; Lit (Int sz) ] ->
      Index (i, Ty.of_expr ty, Z.to_int sz)
  | EList [ Lit (String "+"); Lit (Bool b); i; ty ] ->
      Plus ((if b then Wrap else Overflow), i, Ty.of_expr ty)
  | e -> Fmt.failwith "invalid projection expression element %a" Expr.pp e

let of_lit_list lst : t = { base = None; from_base = List.map op_of_lit lst }
let add_ops proj ops = { proj with from_base = proj.from_base @ ops }

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
      EList [ Lit (String "i"); i; Ty.to_expr ty; Expr.int sz ]
  | Plus (k, i, ty) -> EList [ Lit (String "+"); is_wrap k; i; Ty.to_expr ty ]
  | UPlus (k, i) -> EList [ Lit (String "u+"); is_wrap k; i ]

let to_expr_list t : Expr.t list = List.map expr_of_elem t

let substitution_in_op ~subst_expr (op : op) =
  match op with
  | Field (i, ty) -> Field (i, Ty.substitution ~subst_expr ty)
  | VField (i, ty, idx) -> VField (i, Ty.substitution ~subst_expr ty, idx)
  | Index (i, ty, sz) -> Index (i, Ty.substitution ~subst_expr ty, sz)
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

let pp ft t =
  let pp_base ft = function
    | None -> ()
    | Some b ->
        Expr.pp ft b;
        Fmt.string ft " ++ "
  in
  pp_base ft t.base;
  pp_path ft t.from_base

(** Takes two projections of the form
   P and P.ex and returns (P, ex) *)
let split_extension base with_ext =
  if not @@ (Option.equal Expr.equal) base.base with_ext.base then
    failwith "Invalid call to split_extension";
  let rec aux base with_ext =
    match (base, with_ext) with
    | _, [] -> failwith "No extension!"
    | [], rest -> rest
    | x :: br, y :: rr ->
        if equal_op x y then aux br rr else failwith "Incompatible projections!"
  in
  let rest = aux base.from_base with_ext.from_base in
  rest

module Reduction = struct
  let rec reduce_op_list lst =
    let open Expr.Infix in
    match lst with
    | UPlus (k, i) :: UPlus (k', i') :: tl when k == k' ->
        reduce_op_list (UPlus (k, i + i') :: tl)
    | Plus (k, i, ty) :: Plus (k', i', ty') :: tl
      when k == k' && Ty.equal ty ty' ->
        reduce_op_list (Plus (k, i + i', ty) :: tl)
    | Plus (_, i, _) :: tl when Expr.is_concrete_zero_i i -> reduce_op_list tl
    | UPlus (_, i) :: tl when Expr.is_concrete_zero_i i -> reduce_op_list tl
    | hd :: tl -> hd :: reduce_op_list tl
    | [] -> []

  let reduce { base; from_base } =
    let from_base = reduce_op_list from_base in
    { base; from_base }
end
