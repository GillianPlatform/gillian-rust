open Gillian.Utils.Prelude
open Gillian.Gil_syntax
module DR = Gillian.Monadic.Delayed_result
module Delayed = Gillian.Monadic.Delayed
open Delayed.Syntax

type knowledge = { size : Expr.t (* align: Expr.t; *) } [@@deriving yojson]

let pp_knowledge ft (ty, k) =
  Fmt.pf ft "SIZE OF %a IS %a" Ty.pp ty Expr.pp k.size

let knowledge_lvars { size } = Expr.lvars size

module Map = Map.Make (Ty)

type t = knowledge Map.t [@@deriving yojson]

let pp = Fmt.iter_bindings Map.iter pp_knowledge
let none = Map.empty

let assertions t =
  let cp = Common.Actions.cp_to_name Ty_size in
  let asrts (ty, knowledge) =
    Seq.return (Gil_syntax.Asrt.GA (cp, [ Ty.to_expr ty ], [ knowledge.size ]))
  in
  Map.to_seq t |> Seq.concat_map asrts |> List.of_seq

let rec size_of ~lk ty =
  match ty with
  | Ty.Scalar ty -> Delayed.return (Expr.int (Ty.size_of_scalar ty), lk)
  | Ref { ty = Slice _; _ } | Ptr { ty = Slice _; _ } ->
      Delayed.return (Expr.int (Ty.size_of_scalar (Uint Usize) * 2), lk)
  | Ref _ | Ptr _ ->
      Delayed.return (Expr.int (Ty.size_of_scalar (Uint Usize)), lk)
  | Unresolved _ -> (
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
          Delayed.return ~learned (size, Map.add ty { size } lk))
  | Array { length; ty } ->
      let+ size_ty, lk = size_of ~lk ty in
      (Expr.Infix.(size_ty * length), lk)
  | _ -> Fmt.failwith "size_of: not implemented for %a yet" Ty.pp ty

let reinterpret_offset ~lk ~from_ty ~to_ty ofs =
  if Ty.equal from_ty to_ty then Delayed.return (ofs, lk)
  else
    let* size_from, lk = size_of ~lk from_ty in
    let+ size_to, lk = size_of ~lk to_ty in
    (Expr.Infix.(ofs * size_from / size_to), lk)

let length_as_array_of ~lk ~of_ty ty =
  match ty with
  | Ty.Array { length; ty } when Ty.equal ty of_ty -> Delayed.return (length, lk)
  | ty ->
      let* size_array, lk = size_of ~lk ty in
      let+ size_conv, lk = size_of ~lk of_ty in
      (Expr.Infix.(size_array / size_conv), lk)

let compare_sizes ~lk comp ty_a ty_b =
  let* size_a, lk = size_of ~lk ty_a in
  let+ size_b, lk = size_of ~lk ty_b in
  (comp size_a size_b, lk)

let size_equal ~lk ty_a ty_b =
  if Ty.equal ty_a ty_b then Delayed.return (Formula.True, lk)
  else compare_sizes ~lk Formula.Infix.( #== ) ty_a ty_b

let produce_ty_size ~lk ty new_size =
  let open Formula.Infix in
  (match ty with
  | Ty.Unresolved _ -> ()
  | _ -> failwith "produce_ty_size for resolved type!");
  match Map.find_opt ty lk with
  | Some { size } ->
      let learned = [ size #== new_size ] in
      Delayed.return ~learned lk
  | None ->
      let learned = [ (Expr.typeof new_size) #== (Expr.type_ IntType) ] in
      Delayed.return ~learned (Map.add ty { size = new_size } lk)

let consume_ty_size ~lk ty = size_of ~lk ty

let rec is_zst ~lk ~tyenv ty =
  let+ ret, lk =
    let open Formula.Infix in
    let return_true lk = Delayed.return (Formula.True, lk) in
    let return_false lk = Delayed.return (Formula.False, lk) in
    let rec all ~lk ?(acc = Formula.True) tys =
      match tys () with
      | Seq.Nil -> Delayed.return (acc, lk)
      | Seq.Cons (ty, tys) -> (
          match acc with
          | Formula.False -> return_false lk
          | _ ->
              let* cond, lk = is_zst ~lk ~tyenv ty in
              let acc = acc #&& cond in
              all ~lk ~acc tys)
    in
    match ty with
    | Ty.Scalar _ | Ref _ | Ptr _ -> return_false lk
    | Tuple fields ->
        let fields = List.to_seq fields in
        all ~lk fields
    | Array { length; ty } -> (
        match length with
        | Expr.Lit (Int z) when Z.equal z Z.zero -> return_true lk
        | _ ->
            let+ for_ty, lk = is_zst ~lk ~tyenv ty in
            (for_ty #|| (length #== Expr.zero_i), lk))
    | Adt (name, subst) -> (
        let adt = Common.Tyenv.adt_def ~tyenv name in
        match adt with
        | Struct (_, fields) ->
            let fields =
              List.to_seq fields
              |> Seq.map (fun (_, ty) -> Ty.subst_params ~subst ty)
            in
            all ~lk fields
        | Enum variants -> (
            match variants with
            | [ (_, variant_fields) ] ->
                let fields =
                  List.to_seq variant_fields |> Seq.map (Ty.subst_params ~subst)
                in
                all ~lk fields
            | _ ->
                return_false lk
                (* more than 1 variant means we have to store at least the discriminant *)
            ))
    | Slice _ -> failwith "checking if unsized type is zst?"
    | ty_param ->
        let+ e, lk = size_of ~lk ty_param in
        (e #== Expr.zero_i, lk)
  in
  Logging.verbose (fun m -> m "IS ZST?? %a: %a" Ty.pp ty Formula.pp ret);
  (ret, lk)

let lvars lk =
  Map.fold
    (fun ty k acc ->
      knowledge_lvars k |> SS.union (Ty.lvars ty) |> SS.union acc)
    lk SS.empty

let substitution subst lk =
  let subst_expr = Gillian.Symbolic.Subst.subst_in_expr subst ~partial:true in
  Map.to_seq lk
  |> Seq.map (fun (x, y) ->
         (Ty.substitution ~subst_expr x, { size = subst_expr y.size }))
  |> Map.of_seq
