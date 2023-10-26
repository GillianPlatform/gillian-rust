open Gillian.Utils.Prelude
open Gillian.Gil_syntax
module DR = Gillian.Monadic.Delayed_result
module Delayed = Gillian.Monadic.Delayed

type knowledge = { size : Expr.t (* align: Expr.t; *) } [@@deriving yojson]

let pp_knowledge ft (ty, k) =
  Fmt.pf ft "SIZE OF %a IS %a" Expr.pp ty Expr.pp k.size

let knowledge_lvars { size } = Expr.lvars size

module Map = Map.Make (Expr)

type t = knowledge Map.t [@@deriving yojson]

let pp = Fmt.iter_bindings Map.iter pp_knowledge
let none = Map.empty

let assertions t =
  let cp = Common.Actions.cp_to_name Ty_size in
  let asrts (ty, knowledge) =
    Seq.return (Gil_syntax.Asrt.GA (cp, [ ty ], [ knowledge.size ]))
  in
  Map.to_seq t |> Seq.concat_map asrts |> List.of_seq

let consume_ty_size ~lk ty =
  match Map.find_opt ty lk with
  | Some { size } -> Delayed.return (size, lk)
  | None ->
      let size = Expr.LVar (LVar.alloc ()) in
      let learned =
        let open Formula.Infix in
        let gt_0 = Expr.zero_i #<= size in
        let is_int = (Expr.typeof size) #== (Expr.type_ IntType) in
        [ gt_0; is_int ]
      in
      Delayed.return ~learned (size, Map.add ty { size } lk)

let produce_ty_size ~lk ty new_size =
  let open Formula.Infix in
  match Map.find_opt ty lk with
  | Some { size } ->
      let learned = [ size #== new_size ] in
      Delayed.return ~learned lk
  | None ->
      let learned = [ (Expr.typeof new_size) #== (Expr.type_ IntType) ] in
      Delayed.return ~learned (Map.add ty { size = new_size } lk)

let size_of ~lk ty = consume_ty_size ~lk ty

let is_zst ~lk ~tyenv ty =
  (* [None] means it can't be a zst.
     Otherwise, it's a list of conditions:
     [Left e] means e must be a zst, [Right e] means e must be zero
  *)
  let rec zst_condition (ty : Ty.t) : (Expr.t, Expr.t) Either.t list Option.t =
    let open Syntaxes.Option in
    match ty with
    | Scalar _ | Ref _ | Ptr _ -> None
    | Tuple fields ->
        List.fold_left
          (fun acc ty ->
            let* acc in
            let+ ty = zst_condition ty in
            ty @ acc)
          (Some []) fields
    | SymArray { length; ty } -> (
        match length with
        | Expr.Lit (Int z) when Z.equal z Z.zero -> Some []
        | _ ->
            let+ for_ty = zst_condition ty in
            Either.Right length :: for_ty)
    | Array { length; ty } -> (
        match length with
        | 0 -> Some []
        | _ -> zst_condition ty)
    | Adt (name, subst) -> (
        let adt = Common.Tyenv.adt_def ~tyenv name in
        match adt with
        | Struct (_, fields) ->
            List.fold_left
              (fun acc (_, ty) ->
                let* acc in
                let+ for_ty = zst_condition (Ty.subst_params ~subst ty) in
                for_ty @ acc)
              (Some []) fields
        | Enum variants ->
            List.fold_left
              (fun acc (_vname, fields) ->
                List.fold_left
                  (fun acc ty ->
                    let* acc in
                    let+ for_ty = zst_condition (Ty.subst_params ~subst ty) in
                    for_ty @ acc)
                  acc fields)
              (Some []) variants)
    | Slice _ -> failwith "checking if unsized type is zst?"
    | Unresolved e -> Some [ Either.Left e ]
  in
  match zst_condition ty with
  | None -> Delayed.return (Formula.False, lk)
  | Some l ->
      let open Delayed.Syntax in
      List.fold_left
        (fun acc e ->
          let open Formula.Infix in
          let* b, lk = acc in
          match e with
          | Either.Left e ->
              let+ e, lk = size_of ~lk e in
              (b #&& (e #== Expr.zero_i), lk)
          | Right e -> Delayed.return (b #&& (e #== Expr.zero_i), lk))
        (Delayed.return (Formula.True, lk))
        l

let lvars lk =
  Map.fold
    (fun ty k acc ->
      knowledge_lvars k |> SS.union (Expr.lvars ty) |> SS.union acc)
    lk SS.empty

let substitution subst lk =
  let subst_expr = Gillian.Symbolic.Subst.subst_in_expr subst ~partial:true in
  Map.to_seq lk
  |> Seq.map (fun (x, y) -> (subst_expr x, { size = subst_expr y.size }))
  |> Map.of_seq
