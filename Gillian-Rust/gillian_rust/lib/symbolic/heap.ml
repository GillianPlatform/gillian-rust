open Gillian.Gil_syntax
open List_utils.Infix
open Gillian.Monadic
open Err
module DR = Delayed_result
module LK = Layout_knowledge
open DR.Syntax
open Delayed.Syntax
module Tyenv = Common.Tyenv
module Actions = Common.Actions
open Delayed_utils
open Aloc_utils

module TypePreds = struct
  let ( .%[] ) e idx = Expr.list_nth e idx

  open Formula.Infix

  let ( >- ) e ty = (Expr.typeof e) #== (Expr.type_ ty)

  let valid_thin_ptr e =
    (Expr.list_length e) #== (Expr.int 2)
    #&& (e.%[0] >- ObjectType)
    #&& (e.%[1] >- ListType)

  let valid_fat_ptr e =
    (Expr.list_length e) #== (Expr.int 2)
    #&& (valid_thin_ptr e.%[0])
    #&& (e.%[1] >- IntType)

  let valid_thin_mut_ref_pcy e =
    (Expr.list_length e) #== (Expr.int 2) #&& (valid_thin_ptr e.%[0])

  let valid_fat_mut_ref_pcy e =
    (Expr.list_length e) #== (Expr.int 2) #&& (valid_fat_ptr e.%[0])

  let valid scalar_ty e =
    match scalar_ty with
    | Ty.Scalar (Uint _ | Int _) -> e >- IntType
    | Scalar Bool -> e >- BooleanType
    | Ref { ty = Slice _ | Str; mut = true } ->
        if !Common.R_config.prophecy_mode then valid_fat_mut_ref_pcy e
        else valid_fat_ptr e
    | Ref { mut = true; ty = _ } ->
        if !Common.R_config.prophecy_mode then valid_thin_mut_ref_pcy e
        else valid_thin_ptr e
    | Ref { mut = false; ty = Slice _ | Str } -> valid_fat_ptr e
    | Ref { mut = false; ty = _ } -> valid_thin_ptr e
    | Ptr { ty = Slice _ | Str; _ } -> valid_fat_ptr e
    | Ptr _ -> valid_thin_ptr e
    | Scalar Char -> True
    | _ ->
        Fmt.failwith "Not a leaf type, can't express validity: %a of type %a"
          Expr.pp e Ty.pp scalar_ty

  let empty_array ty =
    match ty with
    | Ty.Array { length; _ } -> Formula.Infix.(length #== (Expr.int 0))
    | _ -> False

  (* let valid_zst_value ~tyenv ty e = e #== (Ty.value_of_zst ~tyenv ty) *)
end

module Symb_opt = struct
  open Formula.Infix

  let is_some e = (Expr.list_nth e 0) #== (Expr.int 1)
  let is_none e = e #== (Expr.EList [ Expr.int 0; Expr.EList [] ])
  let access_some_value e = Expr.list_nth (Expr.list_nth e 1) 0
  let some e = Expr.EList [ Expr.int 1; Expr.EList [ e ] ]

  type t = Some of Expr.t | None | Symb of Expr.t

  let of_expr t =
    match%ent t with
    | is_some -> Delayed.return @@ Some (access_some_value t)
    | is_none -> Delayed.return None
    | _ -> Delayed.return @@ Symb t

  let none_e = Expr.EList [ Expr.int 0; Expr.EList [] ]

  (* There is no uninitialized memory for a zst *)
  (* let zst_value_maybe_uninit ~tyenv ty =
       let zstv = Ty.value_of_zst ~tyenv ty in
       some zstv

     let valid_zst_maybe_uninit ~tyenv ty e =
       e #== (zst_value_maybe_uninit ~tyenv ty)

     let zst_array_maybe_uninit ~tyenv ty length =
       let zstv = Ty.value_of_zst ~tyenv ty in
       let some_zstv = some zstv in
       Expr.list_repeat some_zstv length

     let valid_zst_array_maybe_uninit ~tyenv ty length e =
       e #== (zst_array_maybe_uninit ~tyenv ty length) *)

  let to_expr t =
    match t with
    | Some e -> Expr.EList [ Expr.int 1; Expr.EList [ e ] ]
    | None -> none_e
    | Symb e -> e

  let is_all_none ?size e =
    let size =
      match size with
      | Some size -> size
      | None -> Expr.list_length e
    in
    let i = "#i" in
    let pi = Expr.LVar i in
    Formula.ForAll
      ( [ (i, Some IntType) ],
        Expr.zero_i #<= pi #&& (pi #< size) #=> (is_none (Expr.list_nth_e e pi))
      )

  let all_none size = Expr.list_repeat none_e size
end

let too_symbolic e =
  Delayed.map (Delayed.reduce e) (fun e -> Error (Too_symbolic e))

let rec lift_lit = function
  | Literal.LList l -> Expr.EList (List.map lift_lit l)
  | x -> Lit x

module Range = struct
  open Formula.Infix

  type t = Expr.t * Expr.t

  let pp fmt (a, b) = Fmt.pf fmt "@[<h>[%a..%a[@]" Expr.pp a Expr.pp b
  let is_equal (la, ha) (lb, hb) = la #== lb #&& (ha #== hb)
  let is_inside (la, ha) (lb, hb) = lb #<= la #&& (ha #<= hb)
  let size (a, b) = Expr.Infix.(a - b)
  let split_at (l, h) x = ((l, x), (x, h))
  let offset ~by (l, h) = (Expr.Infix.(l + by), Expr.Infix.(h + by))
  let substitute ~subst_expr (l, h) = (subst_expr l, subst_expr h)

  let reduce (a, b) =
    let* a = Delayed.reduce a in
    let+ b = Delayed.reduce b in
    (a, b)

  let point_strictly_inside x (l, h) =
    let open Formula.Infix in
    l #< x #&& (x #< h)

  let reinterpret ~lk ~from_ty ~to_ty (a, b) =
    if Ty.equal from_ty to_ty then Delayed.return ((a, b), lk)
    else
      let* from_size, lk = Layout_knowledge.size_of ~lk from_ty in
      let* to_size, lk = Layout_knowledge.size_of ~lk to_ty in
      let a' = Expr.Infix.(a * from_size / to_size) in
      let b' = Expr.Infix.(b * from_size / to_size) in
      let+ new_range = reduce (a', b') in
      (new_range, lk)

  let lvars (a, b) =
    Gillian.Utils.Containers.SS.union (Expr.lvars a) (Expr.lvars b)

  let as_array_ty ~index_ty (a, b) = Ty.array index_ty Expr.Infix.(b - a)
end

module TreeBlock = struct
  type t =
    | Structural of structural
    | Laid_out_root of laid_out
        (** The laid-out root will contain a tree that starts at offset 0.
          The interpretation is that the values are "at the path of the root" + "offset of its nodes" *)

  and structural = { ty : Ty.t; content : structural_content }

  and structural_content =
    | Fields of t list
    | Enum of { discr : int; fields : t list }
    | Array of t list
    | Uninit
    | Missing
    | Symbolic of Expr.t
        (** Something that cannot be given further structure,
            either because it's already a scalar, or because
            we want to be lazy in its concretization. *)
    | SymbolicMaybeUninit of Expr.t
        (** The expr should be a "Rust value" (encoded a as a GIL expr),
            which has type [Option<T>].
            If the value is None, then it's the equivalent of an [Uninit] node
            If the value is [Some x] then it's the equivalent of a [Symbolic x] node. *)
    | ManySymbolicMaybeUninit of Expr.t
        (** Same as above, except that the expression is of type Seq<Option<T>>, were each element
            of the sequence behaves as above.  *)

  and laid_out = {
    structural : structural option;
        (** [None] means we need to look at the children *)
    range : Range.t;
    index_ty : Ty.t;
    children : (laid_out * laid_out) option;
  }

  type outer = { offset : Expr.t; root : t }

  let rec map_lc_ranges ~f lc =
    let children =
      Option.map
        (fun (left, right) -> (map_lc_ranges ~f left, map_lc_ranges ~f right))
        lc.children
    in
    let range = f lc.range in
    { lc with children; range }

  let offset_laid_out ~by lc =
    if Expr.is_concrete_zero_i by then lc
    else map_lc_ranges ~f:(Range.offset ~by) lc

  (** [reinterpret_lc_ranges ~lk ~to_ty lc] all nodes in the the tree of [lc] and changes
        its indexing type to [to_ty]. *)
  let rec reinterpret_lc_ranges ~lk ~to_ty lc =
    let* range, lk =
      Range.reinterpret ~lk ~from_ty:lc.index_ty ~to_ty lc.range
    in
    let+ children, lk =
      match lc.children with
      | None -> Delayed.return (None, lk)
      | Some (left, right) ->
          let* left, lk = reinterpret_lc_ranges ~lk ~to_ty left in
          let+ right, lk = reinterpret_lc_ranges ~lk ~to_ty right in
          (Some (left, right), lk)
    in
    ({ lc with range; children }, lk)

  let rec lvars =
    let open Gillian.Utils.Containers in
    let lvars_structural_content = function
      | Fields l | Array l | Enum { fields = l; _ } ->
          List.fold_left (fun acc t -> SS.union acc (lvars t)) SS.empty l
      | SymbolicMaybeUninit e | Symbolic e | ManySymbolicMaybeUninit e ->
          Expr.lvars e
      | Uninit | Missing -> SS.empty
    in
    let lvars_structural { ty; content } =
      Ty.lvars ty |> SS.union (lvars_structural_content content)
    in
    let rec lvars_laid_out { structural; range; children; index_ty } =
      let lvars_children =
        match children with
        | None -> SS.empty
        | Some (left, right) ->
            SS.union (lvars_laid_out left) (lvars_laid_out right)
      in
      Range.lvars range |> SS.union lvars_children
      |> SS.union (Ty.lvars index_ty)
      |> SS.union (Option.fold ~none:SS.empty ~some:lvars_structural structural)
    in
    function
    | Structural structural -> lvars_structural structural
    | Laid_out_root lc -> lvars_laid_out lc

  let outer_lvars outer =
    let open Utils.Containers in
    SS.union (lvars outer.root) (Expr.lvars outer.offset)

  let rec missing_qty t : Qty.t option =
    match t with
    | Structural { content = Missing; _ } -> Some Totally
    | Laid_out_root { structural = None; children; _ } -> (
        let left, right = Option.get_or ~msg:"Lazy without children" children in
        let left_qty = missing_qty (Laid_out_root left) in
        let right_qty = missing_qty (Laid_out_root right) in
        match (left_qty, right_qty) with
        | Some Totally, Some Totally -> Some Totally
        | Some _, _ | _, Some _ -> Some Partially
        | _ -> None)
    | Laid_out_root { structural = Some structural; _ } ->
        missing_qty (Structural structural)
    | Structural
        { content = Array fields | Fields fields | Enum { fields; _ }; ty = _ }
      -> (
        let qtys = List.map missing_qty fields in
        Logging.verbose (fun m ->
            m "qtys: %a" (Fmt.Dump.list (Fmt.Dump.option Qty.pp)) qtys);
        match qtys with
        | [] -> None
        | _ ->
            if
              List.for_all
                (function
                  | Some Qty.Totally -> true
                  | _ -> false)
                qtys
            then Some Totally
            else if List.exists Option.is_some qtys then Some Partially
            else None)
    | Structural
        {
          content =
            ( Symbolic _
            | Uninit
            | ManySymbolicMaybeUninit _
            | SymbolicMaybeUninit _ );
          ty = _;
        } -> None

  let totally_missing t =
    match missing_qty t with
    | Some Totally -> true
    | _ -> false

  let outer_is_empty outer = totally_missing outer.root
  let missing ty = Structural { ty; content = Missing }
  let symbolic ~ty e = Structural { ty; content = Symbolic e }

  let rec pp fmt = function
    | Structural structural -> pp_structural fmt structural
    | Laid_out_root lc -> pp_laid_out fmt lc

  and pp_structural ft { ty; content } =
    Fmt.pf ft "(%a) : %a" pp_structural_content content Ty.pp ty

  and pp_structural_content ft =
    let open Fmt in
    function
    | Fields v -> (Fmt.braces (list ~sep:comma pp)) ft v
    | Array v -> (Fmt.brackets (list ~sep:comma pp)) ft v
    | Enum { discr; fields } ->
        pf ft "%a{%a}" int discr (list ~sep:comma pp) fields
    | Symbolic e -> Expr.pp ft e
    | SymbolicMaybeUninit e -> pf ft "¿ %a ?" Expr.pp e
    | ManySymbolicMaybeUninit e -> pf ft "*¿ %a ?*" Expr.pp e
    | Uninit -> string ft "UNINIT"
    | Missing -> string ft "MISSING"

  and pp_laid_out ft { structural; range; children; index_ty } =
    let open Fmt in
    pf ft "INDEXED BY %a <== %a = %a" Ty.pp index_ty Range.pp range
      (Dump.option pp_structural)
      structural;
    match children with
    | None -> ()
    | Some (left, right) ->
        pf ft "WITH CHILDREN:@ @[<v 2>%a@ %a]" pp_laid_out left pp_laid_out
          right

  let block_size_equal_ty_size ~block ~ty ~lk =
    let+ result =
      Logging.verbose (fun m ->
          m "block_size_equal_ty_size:@\nblock: %a@\nty: %a" pp block Ty.pp ty);
      match block with
      | Structural { ty = ty'; _ } -> LK.size_equal ~lk ty ty'
      | Laid_out_root { index_ty; range; _ } ->
          LK.size_equal ~lk ty (Range.as_array_ty ~index_ty range)
    in
    Logging.verbose (fun m ->
        m "block_size_equal_ty_size returns: %a" Formula.pp (fst result));
    result

  let block_size_equal ~lk block_a block_b =
    match (block_a, block_b) with
    | Structural { ty; _ }, block_b ->
        block_size_equal_ty_size ~lk ~block:block_b ~ty
    | block_a, Structural { ty; _ } ->
        block_size_equal_ty_size ~lk ~block:block_a ~ty
    | ( Laid_out_root { index_ty; range; _ },
        Laid_out_root { index_ty = index_ty'; range = range'; _ } ) ->
        LK.size_equal ~lk
          (Range.as_array_ty ~index_ty range)
          (Range.as_array_ty ~index_ty:index_ty' range')

  let structural_ty_opt = function
    | Structural { ty; _ } -> Some ty
    | _ -> None

  let pp_outer ft t =
    let open Fmt in
    pf ft "@[<v 2>[OFFSET: %a] %a @]" Expr.pp t.offset pp t.root

  let rec to_rust_value ~tyenv ?(current_proj = []) ~ty:expected_ty block ~lk :
      (Expr.t * LK.t, Err.Conversion_error.t) DR.t =
    Logging.verbose (fun m ->
        m "TO_RUST_VALUE:\nBlock: %a\nExpected ty: %a" pp block Ty.pp
          expected_ty);
    let rec all ~lk acc ptvs =
      match ptvs () with
      | Seq.Nil -> DR.ok (List.rev acc, lk)
      | Seq.Cons ((proj, ty, x), rest) ->
          let** x, lk =
            to_rust_value ~tyenv ~current_proj:(proj :: current_proj) ~ty x ~lk
          in
          all ~lk (x :: acc) rest
    in
    let rec of_structural ~lk ~expected_ty ~current_proj { ty; content } =
      if Ty.is_array_of ~array_ty:expected_ty ~inner_ty:ty then
        let++ v, lk =
          of_structural ~current_proj ~expected_ty:ty ~lk { ty; content }
        in
        (Expr.EList [ v ], lk)
      else if not (Ty.equal expected_ty ty) then
        Fmt.failwith
          "To implement: casting in to_rust_value. Should be fairly rare case; \
           though happends in pointer transmutation: I have %a and am looking \
           for something of type %a."
          pp block Ty.pp expected_ty
      else
        match content with
        | Fields v ->
            let ptvs =
              let tys = List.to_seq (Ty.fields ~tyenv ty) in
              let vs = List.to_seq v in
              let zipped = Seq.zip tys vs in
              Seq.mapi
                (fun i (ty', v) -> (Projections.Field (i, ty), ty', v))
                zipped
            in
            let++ fields, lk = all ~lk [] ptvs in
            (Expr.EList fields, lk)
        | Array v ->
            let total_size = List.length v in
            let inner_ty = Ty.array_inner ty in
            let ptvs =
              List.to_seq v
              |> Seq.mapi (fun i v ->
                     ( Projections.Index (Expr.int i, ty, total_size),
                       inner_ty,
                       v ))
            in
            let++ elements, lk = all ~lk [] ptvs in
            (Expr.EList elements, lk)
        | Enum { discr; fields } ->
            let ptvs =
              let tys = List.to_seq (Ty.variant_fields ~tyenv ~idx:discr ty) in
              let vs = List.to_seq fields in
              let zipped = Seq.zip tys vs in
              Seq.mapi
                (fun i (ty', v) ->
                  ( Projections.VField
                      { variant_idx = discr; enum_ty = ty; field_idx = i },
                    ty',
                    v ))
                zipped
            in
            let++ fields, lk = all ~lk [] ptvs in
            (Expr.EList [ Expr.int discr; EList fields ], lk)
        | Symbolic e -> DR.ok (e, lk)
        | SymbolicMaybeUninit e ->
            if%ent Symb_opt.is_some e then DR.ok (e, lk)
            else DR.error Err.Conversion_error.(Uninit, List.rev current_proj)
        | ManySymbolicMaybeUninit _e ->
            failwith
              "ManySymbolicMaybeUninit not implemented yet. It will be a forall"
        | Uninit -> DR.error Err.Conversion_error.(Uninit, List.rev current_proj)
        | Missing ->
            DR.error Err.Conversion_error.(Missing, List.rev current_proj)
    in
    let rec of_lc ~lk ~expected_ty ~current_proj lc =
      match (lc.structural, lc.children) with
      | Some structural, _ ->
          of_structural ~current_proj ~expected_ty ~lk structural
      | None, Some (left, right) -> (
          match expected_ty with
          | Ty.Array { ty = inner_ty; length = _ } ->
              let sub_lc ~lk lc =
                let* expected_ty, lk =
                  let+ length, lk =
                    LK.length_as_array_of ~lk ~of_ty:inner_ty
                      (Ty.array lc.index_ty
                         Expr.Infix.(snd lc.range - fst lc.range))
                  in
                  (Ty.array inner_ty length, lk)
                in
                of_lc ~lk ~expected_ty ~current_proj lc
              in
              let** left, lk = sub_lc ~lk left in
              let++ right, lk = sub_lc ~lk right in
              (Expr.list_cat left right, lk)
          | ty ->
              Fmt.failwith
                "Trying to recompose a value from children, but it is not an \
                 array, it is %a"
                Ty.pp ty)
      | None, None -> Fmt.failwith "malformed tree: lazy with no children"
    in
    match block with
    | Laid_out_root lc -> of_lc ~lk ~expected_ty ~current_proj lc
    | Structural structural ->
        of_structural ~lk ~expected_ty ~current_proj structural

  exception Tree_not_a_value

  (* Converts to a value only if there is no doubt that it can be done. *)
  let rec to_rust_value_exn t =
    match t with
    | Laid_out_root { structural = Some structural; _ } ->
        to_rust_value_exn (Structural structural)
    | Laid_out_root { structural = None; _ } ->
        Fmt.failwith "to_rust_value_exn: laid_out with None structural"
    | Structural { ty; content } -> (
        match content with
        | Fields elements | Array elements ->
            let elements =
              List.map to_rust_value_exn elements |> List.map fst
            in
            (Expr.EList elements, ty)
        | Enum { discr; fields } ->
            let fields = List.map to_rust_value_exn fields |> List.map fst in
            (Expr.EList [ Expr.int discr; EList fields ], ty)
        | Symbolic e -> (e, ty)
        | Uninit | Missing | ManySymbolicMaybeUninit _ | SymbolicMaybeUninit _
          -> raise Tree_not_a_value)

  let to_rust_value_opt_no_reasoning t =
    try Some (to_rust_value_exn t) with Tree_not_a_value -> None

  let to_rust_maybe_uninit ~tyenv ~lk ~loc ~proj ~ty:expected_ty t =
    match t with
    | Structural { content = Uninit; _ } ->
        let result = Symb_opt.to_expr None in
        DR.ok (result, lk)
    | Structural { content = SymbolicMaybeUninit s; ty }
      when Ty.equal expected_ty ty -> DR.ok (s, lk)
    | Structural { content = ManySymbolicMaybeUninit s; ty }
      when Ty.is_array_of ~array_ty:ty ~inner_ty:expected_ty ->
        DR.ok (Expr.list_nth s 0, lk)
    | _ ->
        let++ v, lk =
          let result = to_rust_value ~tyenv ~ty:expected_ty ~lk t in
          DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
        in
        (Symb_opt.some v, lk)

  let to_rust_many_maybe_uninits
      ~tyenv
      ~lk
      ~loc
      ~proj
      ~ty:expected_inner_ty
      ~size
      (t : t) =
    let rec all ~lk f acc l =
      match l with
      | [] -> DR.ok (List.rev acc, lk)
      | x :: r ->
          let** x, lk = f ~lk x in
          all ~lk f (x :: acc) r
    in
    let of_structural ~lk { ty = node_ty; content } =
      match content with
      | Uninit -> DR.ok (Symb_opt.all_none size, lk)
      | ManySymbolicMaybeUninit s
        when Ty.is_array_of ~array_ty:node_ty ~inner_ty:expected_inner_ty ->
          DR.ok (s, lk)
      | Symbolic s when Ty.equal expected_inner_ty node_ty ->
          DR.ok (Expr.EList [ Symb_opt.some s ], lk)
      | SymbolicMaybeUninit s when Ty.equal expected_inner_ty node_ty ->
          DR.ok (Expr.EList [ s ], lk)
      | Array l
        when Ty.is_array_of ~array_ty:node_ty ~inner_ty:expected_inner_ty ->
          let++ l, lk =
            all ~lk
              (fun ~lk x ->
                to_rust_maybe_uninit ~tyenv ~loc ~proj ~ty:expected_inner_ty ~lk
                  x)
              [] l
          in
          (Expr.EList l, lk)
      | _ ->
          Fmt.failwith "obtained the following for many_maybe_uninit: %a"
            pp_structural { ty = node_ty; content }
    in
    let rec of_laid_out ~lk { structural; range = _; children; index_ty = _ } =
      match structural with
      | Some s -> of_structural ~lk s
      | None ->
          let left, right =
            Option.get_or ~msg:"malformed: lazy without chidlren" children
          in
          let** left, lk = of_laid_out ~lk left in
          let++ right, lk = of_laid_out ~lk right in
          (Expr.list_cat left right, lk)
    in
    match t with
    | Structural s -> of_structural ~lk s
    | Laid_out_root lc -> of_laid_out ~lk lc

  let assertions ~loc ~base_offset block =
    let value_cp = Actions.cp_to_name Value in
    let uninit_cp = Actions.cp_to_name Uninit in
    let maybe_uninit_cp = Actions.cp_to_name Maybe_uninit in
    let many_maybe_uninit_cp = Actions.cp_to_name Many_maybe_uninits in
    let rec aux ~current_proj block =
      let ins ty =
        let proj =
          Projections.to_expr
            { base = base_offset; from_base = List.rev current_proj }
        in
        let ty = Ty.to_expr ty in
        [ loc; proj; ty ]
      in
      match to_rust_value_opt_no_reasoning block with
      | Some (value, ty) -> Seq.return (Asrt.GA (value_cp, ins ty, [ value ]))
      | None -> (
          match block with
          | Laid_out_root { structural; children; range; index_ty } -> (
              match (structural, children) with
              | Some structural, None ->
                  let current_proj =
                    Projections.Reduction.reduce_op_list
                      (current_proj @ [ Plus (Overflow, fst range, index_ty) ])
                  in
                  aux ~current_proj (Structural structural)
              | _, Some (left, right) ->
                  Seq.append
                    (aux ~current_proj (Laid_out_root left))
                    (aux ~current_proj (Laid_out_root right))
              | None, None ->
                  Fmt.failwith "malformed tree! Lazy without children")
          | Structural { content = Uninit; ty } ->
              Seq.return (Asrt.GA (uninit_cp, ins ty, []))
          | Structural { content = SymbolicMaybeUninit s; ty } ->
              Seq.return (Asrt.GA (maybe_uninit_cp, ins ty, [ s ]))
          | Structural { content = ManySymbolicMaybeUninit s; ty } ->
              Seq.return (Asrt.GA (many_maybe_uninit_cp, ins ty, [ s ]))
          | Structural { content = Missing; _ } -> Seq.empty
          | Structural { content = Fields v; ty } ->
              let proj i = Projections.Field (i, ty) in
              List.to_seq v
              |> Seq.mapi (fun i f ->
                     aux ~current_proj:(proj i :: current_proj) f)
              |> Seq.concat
          | Structural { content = Array v; ty } ->
              let total_size = List.length v in
              let proj i = Projections.Index (Expr.int i, ty, total_size) in
              List.to_seq v
              |> Seq.mapi (fun i f ->
                     aux ~current_proj:(proj i :: current_proj) f)
              |> Seq.concat
          | Structural { content = Enum _; _ } ->
              failwith
                "Trying to derive assertion for incomplete enum: to implement!"
          | _ -> Fmt.failwith "unreachable: %a to assertion" pp block)
    in
    aux ~current_proj:[] block

  let outer_assertions ~loc block =
    assertions ~loc ~base_offset:(Some block.offset) block.root

  let uninitialized ~tyenv:_ ty = Structural { ty; content = Uninit }

  let rec of_rust_struct_value
      ~tyenv
      ~ty
      ~subst
      ~fields_tys
      (fields : Expr.t list) =
    let++ content =
      DR_list.map2
        (fun (_, t) v -> of_rust_value ~tyenv ~ty:(Ty.subst_params ~subst t) v)
        fields_tys fields
    in
    Structural { ty; content = Fields content }

  and of_rust_enum_value ~tyenv ~ty ~subst ~variants_tys (data : Expr.t list) =
    Logging.verbose (fun m ->
        m "of_rust_enum_value %a for %a" (Fmt.Dump.list Expr.pp) data Ty.pp ty);
    match data with
    | [ Lit (Int variant_idx); EList fields ] ->
        let vidx = Z.to_int variant_idx in
        let _, tys = List.nth variants_tys vidx in
        Logging.verbose (fun m -> m "fields: %a" (Fmt.Dump.list Ty.Cty.pp) tys);
        let++ fields =
          DR_list.map2
            (fun t v -> of_rust_value ~tyenv ~ty:(Ty.subst_params ~subst t) v)
            tys fields
        in
        Structural { ty; content = Enum { discr = vidx; fields } }
    | _ ->
        Fmt.failwith "Invalid enum value for type %a: %a" Ty.pp ty
          (Fmt.list Expr.pp) data

  and of_rust_value ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    match (ty, e) with
    | (Ty.Scalar _ | Ptr _ | Ref _), e ->
        Logging.tmi (fun m -> m "valid: %a for %a" Expr.pp e Ty.pp ty);
        if%sat TypePreds.valid ty e then
          DR.ok (Structural { ty; content = Symbolic e })
        else DR.error (Err.Invalid_value (ty, e))
        (* This is a failsafe, should compilation be correct,
           the RHS should be unreachable. *)
    | Tuple _, Lit (LList data) ->
        let content = List.map lift_lit data in
        of_rust_value ~tyenv ~ty (EList content)
    | Tuple ts, EList tup ->
        let++ content =
          DR_list.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) ts tup
        in
        Structural { ty; content = Fields content }
    | Adt _, Lit (LList content) ->
        let content = List.map lift_lit content in
        of_rust_value ~tyenv ~ty (EList content)
    | Adt (name, subst), EList data -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields_tys) ->
            of_rust_struct_value ~tyenv ~ty ~subst ~fields_tys data
        | Enum variants_tys ->
            of_rust_enum_value ~tyenv ~ty ~subst ~variants_tys data)
    | Array { length = Expr.Lit (Int length); ty = ty' }, EList l
      when Z.equal (Z.of_int (List.length l)) length ->
        let++ mem_array = DR_list.map (of_rust_value ~tyenv ~ty:ty') l in
        Structural { ty; content = Array mem_array }
    | _, s -> DR.ok (Structural { ty; content = Symbolic s })

  let of_rust_maybe_uninit ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    let* maybe_value = Symb_opt.of_expr e in
    match maybe_value with
    | None -> DR.ok (uninitialized ~tyenv ty)
    | Some value -> of_rust_value ~tyenv ~ty value
    | Symb e -> DR.ok (Structural { content = SymbolicMaybeUninit e; ty })

  let of_rust_many_maybe_uninit ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    let* e = Delayed.reduce e in
    match (e, ty) with
    | Expr.EList l, Ty.Array { ty = inner_ty; _ } ->
        let++ elements =
          DR_list.map (of_rust_maybe_uninit ~tyenv ~ty:inner_ty) l
        in
        Structural { content = Array elements; ty }
    | _ -> DR.ok (Structural { content = ManySymbolicMaybeUninit e; ty })

  let outer_missing ~offset ~tyenv:_ ty =
    let root = missing ty in
    { offset; root }

  let outer_symbolic ~offset ~tyenv:_ ty e =
    let root = symbolic ~ty e in
    { offset; root }

  let uninitialized_outer ~tyenv ty =
    let root = uninitialized ~tyenv ty in
    { offset = Expr.EList []; root }

  let semi_concretize ~tyenv ~variant ty expr =
    (* FIXME: this assumes the values are initialized? Not entirely sure...
       I think we `Symbolic` means "initialized and symbolic!" *)
    Logging.tmi (fun m ->
        m "semi_concretize %a with ty %a and variant: %a" Expr.pp expr Ty.pp ty
          (Fmt.Dump.option Fmt.int) variant);
    let open Formula.Infix in
    let is_list v = (Expr.typeof v) #== (Expr.type_ ListType) in
    let has_length i l = (Expr.list_length l) #== i in
    match ty with
    | Ty.Tuple v ->
        if%ent (is_list expr) #&& (has_length (Expr.int (List.length v)) expr)
        then
          let values =
            List.init (List.length v) (fun i -> Expr.list_nth expr i)
          in
          let fields =
            List.map2
              (fun ty e -> Structural { content = Symbolic e; ty })
              v values
          in
          DR.ok (Structural { ty; content = Fields fields })
        else too_symbolic expr
          (* FIXME: This is probably not the right error? *)
    | Array { length = Expr.Lit (Int length_i) as length; ty = ty' }
      when Z.(length_i < of_int 1000) ->
        if%sat (is_list expr) #&& (has_length length expr) then
          let values =
            List.init (Z.to_int length_i) (fun i -> Expr.list_nth expr i)
          in
          let fields =
            List.map
              (fun e -> Structural { content = Symbolic e; ty = ty' })
              values
          in
          DR.ok (Structural { ty; content = Array fields })
        else too_symbolic expr
    | Array _ -> failwith "semi-concretizing arrays of symbolic size: implement"
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            if%sat
              (is_list expr)
              #&& (has_length (Expr.int (List.length fields)) expr)
            then
              let values =
                List.init (List.length fields) (fun i -> Expr.list_nth expr i)
              in
              let fields =
                List.map2
                  (fun (_, ty) e ->
                    Structural
                      { content = Symbolic e; ty = Ty.subst_params ~subst ty })
                  fields values
              in
              DR.ok (Structural { ty; content = Fields fields })
            else too_symbolic expr
        | Enum variants ->
            (* This should only be called with a variant context *)
            let variant_idx = Option.get variant in
            let variant = List.nth variants variant_idx in
            let th_variant_idx = Expr.list_nth expr 0 in
            let th_fields = Expr.list_nth expr 1 in
            let number_fields = List.length (snd variant) in
            if%sat
              (* Value should have shape:
                 [ idx, [field_0, ..., field_n] ] *)
              (is_list expr)
              #&& (has_length (Expr.int 2) expr)
              #&& (th_variant_idx #== (Expr.int variant_idx))
              #&& (is_list th_fields)
              #&& (has_length (Expr.int number_fields) th_fields)
            then
              let values =
                List.init number_fields (fun i -> Expr.list_nth th_fields i)
              in
              let fields =
                List.map2
                  (fun ty e ->
                    Structural
                      { content = Symbolic e; ty = Ty.subst_params ~subst ty })
                  (snd variant) values
              in
              DR.ok
                (Structural
                   { ty; content = Enum { discr = variant_idx; fields } })
            else too_symbolic expr)
    | Scalar _ | Ref _ | Ptr _ ->
        failwith
          "I shouldn't ever need to concretize a scalar or something opaque"
    | Slice _ | Str -> Fmt.failwith "Cannot initialize unsized type"
    | Unresolved e ->
        Fmt.failwith
          "Unresolved should have been resolved before getting to \
           `semi_concretize`: %a"
          Expr.pp e

  let structural_missing ~tyenv (ty : Ty.t) =
    match ty with
    | Array { length = Expr.Lit (Int length_i); ty = ty' }
      when Z.(length_i < of_int 1000) ->
        let missing_child = missing ty' in
        Structural
          {
            ty;
            content =
              Array (List.init (Z.to_int length_i) (fun _ -> missing_child));
          }
    | Array _ -> failwith "structural_mising arrays: implement"
    | Tuple fields ->
        Structural
          { ty; content = Fields (List.map (fun ty -> missing ty) fields) }
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            let missing_fields =
              List.map
                (fun (_, cty) ->
                  let ty = Ty.subst_params ~subst cty in
                  missing ty)
                fields
            in
            Structural { ty; content = Fields missing_fields }
        | Enum _ as def ->
            Fmt.failwith "Unhandled: structural missing for Enum %a"
              Common.Ty.Adt_def.pp def)
    | Scalar _ | Ref _ | Ptr _ | Unresolved _ | Slice _ | Str ->
        Fmt.failwith "structural missing called on a leaf or unsized: %a" Ty.pp
          ty

  let extract_range_structural ~lk ~index_ty ~range structural =
    Logging.verbose (fun m ->
        m
          "extract_range_structural:@\n\
           index_ty: %a@\n\
           range: %a@\n\
           structural: %a" Ty.pp index_ty Range.pp range pp_structural
          structural);
    let children_from_split split =
      match split with
      | `Two ((left, left_range), (right, right_range)) ->
          let left =
            {
              structural = Some left;
              range = left_range;
              children = None;
              index_ty;
            }
          in
          let right =
            {
              structural = Some right;
              range = right_range;
              children = None;
              index_ty;
            }
          in
          (left, right)
      | `Three ((left, left_range), (mid, mid_range), (right, right_range)) ->
          let left_left =
            {
              structural = Some left;
              range = left_range;
              children = None;
              index_ty;
            }
          in
          let left_right =
            {
              structural = Some mid;
              range = mid_range;
              children = None;
              index_ty;
            }
          in
          let left =
            {
              structural = None;
              range = (fst left_range, snd mid_range);
              children = Some (left_left, left_right);
              index_ty;
            }
          in
          let right =
            {
              structural = Some right;
              range = right_range;
              children = None;
              index_ty;
            }
          in
          (left, right)
    in
    let root_of_children (left, right) =
      let root =
        {
          structural = Some structural;
          (* From the outer function *)
          range = (fst left.range, snd right.range);
          index_ty = left.index_ty;
          children = Some (left, right);
        }
      in
      Laid_out_root root
    in
    let* end_as_index, lk =
      Layout_knowledge.length_as_array_of ~lk ~of_ty:index_ty structural.ty
    in
    match structural.content with
    | Fields _ | Enum _ ->
        Fmt.failwith
          "Cannot split fields or enum: don't know their layouts, probably a \
           bug in the verified program. (or an unsupported usage of #[repr] on \
           enum)"
    | Array l -> (
        let values_ty = Ty.array_inner structural.ty in
        (* We reinterpret the range using the type of the array, so we can use it to have precise indexes *)
        let* range_v, lk =
          Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:values_ty range
        in
        let as_array_of_values_ty ~lk range =
          let+ length, lk =
            LK.length_as_array_of ~lk ~of_ty:values_ty
              (Range.as_array_ty ~index_ty range)
          in
          (Ty.array values_ty length, lk)
        in
        match range_v with
        | Expr.Lit (Int start), Expr.Lit (Int end_) ->
            (* We have a concrete range, we can extract a precise split *)
            let range_v = Z.(to_int start, to_int end_) in
            let+ split, lk =
              match List_utils.extract_range ~range:range_v l with
              | `Left (left, right) ->
                  (* We use the index_ty provided to us,
                     so we use the range before conversion to the value type*)
                  let left_range = (Expr.zero_i, snd range) in
                  let right_range = (snd range, end_as_index) in
                  let* left_ty, lk = as_array_of_values_ty ~lk left_range in
                  let+ right_ty, lk = as_array_of_values_ty ~lk right_range in
                  ( `Two
                      ( ({ content = Array left; ty = left_ty }, left_range),
                        ({ content = Array right; ty = right_ty }, right_range)
                      ),
                    lk )
              | `Right (left, right) ->
                  let left_range = (Expr.zero_i, fst range) in
                  let right_range = (fst range, snd range) in
                  let* left_ty, lk = as_array_of_values_ty ~lk left_range in
                  let+ right_ty, lk = as_array_of_values_ty ~lk right_range in
                  ( `Two
                      ( ({ content = Array left; ty = left_ty }, left_range),
                        ({ content = Array right; ty = right_ty }, right_range)
                      ),
                    lk )
              | `Three (left, mid, right) ->
                  let left_range = (Expr.zero_i, fst range) in
                  let right_range = (snd range, end_as_index) in
                  let* left_ty, lk = as_array_of_values_ty ~lk left_range in
                  let* mid_ty, lk = as_array_of_values_ty ~lk range in
                  let+ right_ty, lk = as_array_of_values_ty ~lk right_range in
                  ( `Three
                      ( ({ content = Array left; ty = left_ty }, left_range),
                        ({ content = Array mid; ty = mid_ty }, range),
                        ({ content = Array right; ty = right_ty }, right_range)
                      ),
                    lk )
            in
            let root = children_from_split split |> root_of_children in
            (root, lk)
        | _range ->
            Fmt.failwith
              "to implement: extracting a symbolic length from a concrete array"
        )
    | Uninit | Missing ->
        (* FIXME: the structural is wrong, I need to fix the type so that it has the right size! *)
        let+ split =
          if%sat Formula.Infix.((fst range) #== Expr.zero_i) then
            let left_range = (Expr.zero_i, snd range) in
            let right_range = (snd range, end_as_index) in
            let left_ty = Range.as_array_ty ~index_ty left_range in
            let right_ty = Range.as_array_ty ~index_ty right_range in
            Delayed.return
              (`Two
                ( ({ structural with ty = left_ty }, left_range),
                  ({ structural with ty = right_ty }, right_range) ))
          else
            if%sat Formula.Infix.((snd range) #== end_as_index) then
              let left_range = (Expr.zero_i, fst range) in
              Delayed.return
                (`Two ((structural, left_range), (structural, range)))
            else
              let left_range = (Expr.zero_i, fst range) in
              let right_range = (snd range, end_as_index) in
              Delayed.return
                (`Three
                  ( (structural, left_range),
                    (structural, range),
                    (structural, right_range) ))
        in
        let root = children_from_split split |> root_of_children in
        (root, lk)
    | ManySymbolicMaybeUninit e ->
        let value_ty, length = Ty.array_components structural.ty in
        let+ split, lk =
          if%sat Formula.Infix.((fst range) #== Expr.zero_i) then
            let+ left_size, lk =
              LK.reinterpret_offset ~lk ~from_ty:index_ty ~to_ty:value_ty
                (snd range)
            in
            let left_list =
              Expr.list_sub ~lst:e ~start:Expr.zero_i ~size:left_size
            in
            let left_ty = Ty.array value_ty left_size in
            let left_range = (Expr.zero_i, snd range) in
            let right_list =
              Expr.list_sub ~lst:e ~start:left_size
                ~size:Expr.Infix.(length - left_size)
            in
            let right_range = (snd range, end_as_index) in
            let right_ty = Ty.array value_ty Expr.Infix.(length - left_size) in
            let split =
              `Two
                ( ( { content = ManySymbolicMaybeUninit left_list; ty = left_ty },
                    left_range ),
                  ( {
                      content = ManySymbolicMaybeUninit right_list;
                      ty = right_ty;
                    },
                    right_range ) )
            in
            (split, lk)
          else
            if%sat Formula.Infix.((snd range) #== end_as_index) then
              let+ left_size, lk =
                LK.reinterpret_offset ~lk ~from_ty:index_ty ~to_ty:value_ty
                  (fst range)
              in
              let left_list =
                Expr.list_sub ~lst:e ~start:Expr.zero_i ~size:left_size
              in
              let left_ty = Ty.array value_ty left_size in
              let left_range = (Expr.zero_i, fst range) in
              let right_size = Expr.Infix.(length - left_size) in
              let right_list =
                Expr.list_sub ~lst:e ~start:left_size ~size:right_size
              in
              let right_ty = Ty.array value_ty right_size in
              let right_range = (fst range, end_as_index) in
              let split =
                `Two
                  ( ( {
                        content = ManySymbolicMaybeUninit left_list;
                        ty = left_ty;
                      },
                      left_range ),
                    ( {
                        content = ManySymbolicMaybeUninit right_list;
                        ty = right_ty;
                      },
                      right_range ) )
              in
              (split, lk)
            else
              let+ (left_end, mid_end), lk =
                Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:value_ty range
              in
              let left_list =
                Expr.list_sub ~lst:e ~start:Expr.zero_i ~size:left_end
              in
              let left_ty = Ty.array value_ty left_end in
              let left_range = (Expr.zero_i, fst range) in
              let mid_size = Expr.Infix.(mid_end - left_end) in
              let mid_list =
                Expr.list_sub ~lst:e ~start:left_end ~size:mid_size
              in
              let mid_ty = Ty.array value_ty mid_size in
              let right_size = Expr.Infix.(length - mid_end) in
              let right_list =
                Expr.list_sub ~lst:e ~start:left_end ~size:right_size
              in
              let right_ty = Ty.array value_ty right_size in
              let right_range = (snd range, end_as_index) in
              let split =
                `Three
                  ( ( {
                        content = ManySymbolicMaybeUninit left_list;
                        ty = left_ty;
                      },
                      left_range ),
                    ( { content = ManySymbolicMaybeUninit mid_list; ty = mid_ty },
                      range ),
                    ( {
                        content = ManySymbolicMaybeUninit right_list;
                        ty = right_ty;
                      },
                      right_range ) )
              in
              (split, lk)
        in
        let root = children_from_split split |> root_of_children in
        (root, lk)
    | _ ->
        Fmt.failwith "Not implemented yet: extracting range from structural %a"
          pp_structural structural

  let laid_out_of_children left right =
    if not (Ty.equal left.index_ty right.index_ty) then
      Fmt.failwith
        "laid_out_of_children: need to reinterpreted sub-ranges.\n\
         Left: %a\n\
         Right: %a" pp_laid_out left pp_laid_out right;
    let range = (fst left.range, snd right.range) in
    let index_ty = left.index_ty in
    let children = Some (left, right) in
    { structural = None; range; children; index_ty }

  let rec extract ~lk ~range ~index_ty laid_out =
    let* range, lk =
      Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:laid_out.index_ty range
    in
    let index_ty = laid_out.index_ty in
    if%sat Range.is_equal range laid_out.range then
      Delayed.return ((laid_out, None), lk)
    else
      let left, right = Option.get laid_out.children in
      let* range_as_left, lk =
        Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:left.index_ty range
      in
      if%sat Range.is_inside range_as_left left.range then
        let+ (extracted, new_left), lk =
          extract ~lk ~range:range_as_left ~index_ty:left.index_ty left
        in
        let new_self =
          match new_left with
          | Some left -> laid_out_of_children left extracted
          | None -> extracted
        in
        ((extracted, Some new_self), lk)
      else
        let* range_as_right, lk =
          Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:right.index_ty range
        in
        let+ (extracted, new_right), lk =
          extract ~lk ~range:range_as_right ~index_ty:right.index_ty right
        in
        let new_self =
          match new_right with
          | Some right -> laid_out_of_children extracted right
          | None -> extracted
        in
        ((extracted, Some new_self), lk)

  let rec add_to_the_left lc addition : laid_out =
    match lc.children with
    | None -> laid_out_of_children addition lc
    | Some (left, right) ->
        let new_left = add_to_the_left left addition in
        laid_out_of_children new_left right

  let rec add_to_the_right lc addition : laid_out =
    match lc.children with
    | None -> laid_out_of_children lc addition
    | Some (left, right) ->
        let new_right = add_to_the_right right addition in
        laid_out_of_children left new_right

  (** Extract range from a given structural node.
    The range is given in the index type, is relative to the current structure.
    It must be the case that the range is STRICTLY contained in the current structure, i.e.
    [range.length * size_of::<index_ty>() < size_of::<node_ty>()].
    [index_ty] is the index that corresponds to the [range],
    while [node_ty] is the type of the [structural].
    The range must also be relative to the beginning of the structural object.
    The result is a full object of type [t], with a laid-out content starting at range 0.
  *)
  let as_laid_out_child ~lk ~range ~index_ty t =
    match t with
    | Laid_out_root root' ->
        let+ root, lk = reinterpret_lc_ranges ~lk ~to_ty:index_ty root' in
        let child = offset_laid_out ~by:(fst range) root in
        (child, lk)
    | Structural structural ->
        Delayed.return
          ( { structural = Some structural; range; children = None; index_ty },
            lk )

  (** [range] must be according to [lc.index_ty] *)

  let rec extract_laid_out_and_apply :
        'a.
        lk:LK.t ->
        return_and_update:(t -> lk:LK.t -> (('a * t) * LK.t, Err.t) DR.t) ->
        range:Range.t ->
        index_ty:Ty.t ->
        laid_out ->
        (('a * laid_out) * LK.t, Err.t) DR.t =
   fun ~lk ~(return_and_update : t -> lk:LK.t -> (('a * t) * LK.t, Err.t) DR.t)
       ~range ~index_ty lc ->
    let* range, lk =
      Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:lc.index_ty range
    in
    let index_ty = lc.index_ty in
    Logging.verbose (fun m -> m "Inside extract_laid_out_and_apply");
    Logging.verbose (fun m ->
        m "Range we're looking for, using index type %a: %a, range we're in: %a"
          Ty.pp index_ty Range.pp range Range.pp lc.range);
    Logging.verbose (fun m -> m "LC: %a" pp_laid_out lc);
    if%sat Range.is_equal range lc.range then (
      Logging.verbose (fun m -> m "Range is equal");
      let () = Logging.tmi (fun m -> m "Range is equal") in
      let offset = fst range in
      (* we return a relative lc *)
      let this_tree =
        let lc_absolute = offset_laid_out ~by:Expr.Infix.(~-offset) lc in
        Laid_out_root lc_absolute
      in
      let** (value, new_tree), lk = return_and_update ~lk this_tree in
      Logging.verbose (fun m ->
          m "calling as_laid_out_child on %a with range: %a index_ty: %a" pp
            new_tree Range.pp range Ty.pp lc.index_ty);
      let+ lc, lk = as_laid_out_child ~lk ~range ~index_ty new_tree in
      Logging.verbose (fun m -> m "Obtained %a" pp_laid_out lc);
      Ok ((value, lc), lk))
    else
      match (lc.structural, lc.children) with
      | Some structural, None ->
          let () =
            Logging.tmi (fun m ->
                m "Leaf!!! Structural = %a" pp_structural structural)
          in
          let rel_range =
            Range.offset ~by:Expr.Infix.(~-(fst lc.range)) range
          in
          (* leaf, we try splitting further *)
          let* new_node, lk =
            extract_range_structural ~lk ~index_ty:lc.index_ty ~range:rel_range
              structural
          in
          let** (value, new_tree), lk =
            extract_and_apply ~lk ~return_and_update ~index_ty ~range:rel_range
              new_node
          in
          let+ lc, lk =
            as_laid_out_child ~lk ~range:lc.range ~index_ty new_tree
          in
          Ok ((value, lc), lk)
      | _, Some (left, right) ->
          Logging.verbose (fun m -> m "Range is not equal going to children");
          if
            not
              (Ty.equal lc.index_ty left.index_ty
              && Ty.equal lc.index_ty right.index_ty)
          then
            Fmt.failwith
              "extract_laid_out_and_apply: need to reinterpreted \
               sub-ranges.This index ty: %a\n\
               Right: %a\n\
               Left: %a" Ty.pp lc.index_ty pp_laid_out left pp_laid_out right;
          if%sat Range.is_inside range left.range then (
            Logging.verbose (fun m -> m "Inside of left");
            let++ (value, left), lk =
              extract_laid_out_and_apply ~lk ~return_and_update ~index_ty ~range
                left
            in
            let new_lc = laid_out_of_children left right in
            ((value, new_lc), lk))
          else
            if%sat Range.is_inside range right.range then (
              Logging.verbose (fun m -> m "Inside of right");
              let++ (value, right), lk =
                extract_laid_out_and_apply ~lk ~return_and_update ~range
                  ~index_ty right
              in
              let new_lc = laid_out_of_children left right in
              ((value, new_lc), lk))
            else
              (* We now that [this_low <= low < mid < high <= this_high ]
                 Remember that left.range = (this_low, mid) and right.range = (mid, this_high) *)
              let _this_low, this_high = lc.range in
              let low, high = range in
              let _, mid = left.range in
              let dont_update t ~lk = DR.ok (((), t), lk) in
              if%sat
                (* High range is already good *)
                Formula.Infix.(high #== this_high)
              then
                (* Rearrange left*)
                let low_range = (low, mid) in
                let** (_, left), lk =
                  extract_laid_out_and_apply ~lk ~return_and_update:dont_update
                    ~range:low_range ~index_ty left
                in
                let* (extracted, left_opt), lk =
                  extract ~lk left ~index_ty ~range:low_range
                in
                let right = add_to_the_left right extracted in
                let new_self =
                  laid_out_of_children (Option.get left_opt) right
                in
                extract_laid_out_and_apply ~lk ~return_and_update ~range
                  ~index_ty new_self
              else
                (* Rearrange right *)
                let upper_range = (mid, high) in
                let** (_, right), lk =
                  extract_laid_out_and_apply ~lk ~return_and_update:dont_update
                    ~range:upper_range ~index_ty right
                in
                let* (extracted, right_opt), lk =
                  extract ~lk ~range:upper_range ~index_ty right
                in
                let left = add_to_the_right left extracted in
                let new_self =
                  laid_out_of_children left (Option.get right_opt)
                in
                extract_laid_out_and_apply ~lk ~return_and_update ~range
                  ~index_ty new_self
      | _ -> failwith "Malformed: lazy without children"

  (** This applies [return_and_update] on the range given index by [index_ty] within the block [t] *)
  and extract_and_apply ~return_and_update ~range ~index_ty t ~lk =
    Logging.verbose (fun m -> m "extract_and_apply: %a" pp t);
    let* eq, lk =
      block_size_equal_ty_size ~lk ~block:t
        ~ty:(Range.as_array_ty ~index_ty range)
    in
    if%sat eq then return_and_update ~lk t
    else
      match t with
      | Structural s ->
          let* new_node, lk = extract_range_structural ~lk ~index_ty ~range s in
          extract_and_apply ~lk ~return_and_update ~range ~index_ty new_node
      | Laid_out_root lc ->
          let* range_as_in_lc, lk =
            Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:lc.index_ty range
          in
          let++ (value, lc), lk =
            extract_laid_out_and_apply ~lk ~return_and_update ~index_ty
              ~range:range_as_in_lc lc
          in
          ((value, Laid_out_root lc), lk)

  let extend_on_right_if_needed ~can_extend ~range ~index_ty t ~lk =
    Logging.verbose (fun m ->
        m "Extending on the right! Can extend: %b" can_extend);
    let* (_, current_high), lk =
      match t with
      | Structural { ty = Ty.Array { length; ty = ty' }; _ } ->
          Range.reinterpret ~lk ~from_ty:ty' ~to_ty:index_ty
            (Expr.zero_i, length)
      | Structural { ty; _ } when Ty.equal ty index_ty ->
          Delayed.return ((Expr.zero_i, Expr.one_i), lk)
      | Laid_out_root { index_ty = from_ty; range; _ } ->
          Range.reinterpret ~lk ~from_ty ~to_ty:index_ty range
      | _ ->
          Fmt.failwith
            "Extending non-array or non-laid-out:@\n\
             RANGE: %a@\n\
             INDEX_TY: %a@\n\
             BLOCK: %a" Range.pp range Ty.pp index_ty pp t
    in
    if%sat Formula.Infix.((snd range) #<= current_high) then
      Delayed.return (t, lk)
    else
      let () =
        if not can_extend then
          Fmt.failwith "need to extend but can't. Probably a bug in the program"
      in
      match t with
      | Structural s ->
          let left_child =
            {
              structural = Some s;
              range = (Expr.zero_i, current_high);
              children = None;
              index_ty;
            }
          in
          let right_child =
            let range_right = (current_high, snd range) in
            {
              structural =
                Some
                  {
                    content = Missing;
                    ty = Range.as_array_ty ~index_ty range_right;
                  };
              range = range_right;
              children = None;
              index_ty;
            }
          in
          let lc =
            {
              structural = None;
              range = (Expr.zero_i, snd range);
              children = Some (left_child, right_child);
              index_ty;
            }
          in
          Delayed.return (Laid_out_root lc, lk)
      | _ ->
          Fmt.failwith
            "extend on the right for layed out content: not implemented %a, \
             range: %a, index_ty: %a"
            pp t Range.pp range Ty.pp index_ty

  let rec frame_slice
      ~tyenv
      ~lk
      ~can_extend
      ~return_and_update
      ~ty
      ?(current_offset = Expr.zero_i)
      (t : t)
      (path : Projections.op list)
      size =
    (* For now we implement only a few cases we'll need more as we do more case studies and proofs.
       The casts surely come with more general rules. *)
    match path with
    | [] ->
        if%ent Formula.Infix.(Expr.zero_i #<= current_offset) then
          let range = (current_offset, Expr.Infix.(current_offset + size)) in
          let* t, lk =
            (* Extending on the left would require working on the outer level.
               This is not implemented yet. *)
            extend_on_right_if_needed ~lk ~range ~can_extend ~index_ty:ty t
          in
          extract_and_apply ~lk ~return_and_update ~range ~index_ty:ty t
        else
          Fmt.failwith "negative offset in array in frame_slice : %a" Expr.pp
            current_offset
    | Plus (_, ofs, ofs_ty) :: rest ->
        let* ofs, lk =
          LK.reinterpret_offset ~lk ~from_ty:ofs_ty ~to_ty:ty ofs
        in
        frame_slice ~can_extend:true ~tyenv ~lk ~return_and_update ~ty
          ~current_offset:Expr.Infix.(current_offset + ofs)
          t rest size
    | _ ->
        Fmt.failwith
          "Unimplemented case for frame_slice: path: %a, t: ==%a==, \
           expected_ty: %a, size: %a"
          Projections.pp_path path pp t Ty.pp ty Expr.pp size

  let frame_path
      ~tyenv
      ~(return_and_update : t -> lk:LK.t -> (('a * t) * LK.t, Err.t) DR.t)
      ~ty:expected_ty
      t
      path
      ~lk =
    match expected_ty with
    | Ty.Array { length; ty } ->
        (* This should be done way later actually, after properly resolving the other projs *)
        if%sat Formula.Infix.(length #== Expr.zero_i) then
          return_and_update ~lk
            (Structural { ty = expected_ty; content = Array [] })
        else
          frame_slice ~can_extend:true ~tyenv ~lk ~return_and_update ~ty t path
            length
    | _ ->
        let rec aux t (path : Projections.path) ~lk =
          match (path, t) with
          | [], _ ->
              let* eq, lk =
                block_size_equal_ty_size ~lk ~block:t ~ty:expected_ty
              in
              if%ent eq then return_and_update t ~lk
              else
                (* This is the case where we're accessing the first offset of
                   a slice without casting the pointer *)
                let return_and_update' t ~lk = aux t [] ~lk in
                frame_slice ~tyenv ~lk ~can_extend:false
                  ~return_and_update:return_and_update' ~ty:expected_ty
                  ~current_offset:Expr.zero_i t [] Expr.one_i
          | Field (i, ty) :: rest, Structural { content = Fields vec; ty = ty' }
            when Ty.equal ty ty' ->
              let e = Result.ok_or vec.%[i] ~msg:"Index out of bounds" in
              let** (v, sub_block), lk = aux ~lk e rest in
              let++ new_fields = Delayed.return (vec.%[i] <- sub_block) in
              ((v, Structural { ty; content = Fields new_fields }), lk)
          | ( VField { field_idx; enum_ty; variant_idx } :: rest,
              Structural { content = Enum { discr; fields }; ty = ty' } )
            when Ty.equal enum_ty ty' && discr == variant_idx ->
              let e =
                Result.ok_or fields.%[field_idx] ~msg:"Index out of bounds"
              in
              let** (v, sub_block), lk = aux ~lk e rest in
              let++ new_fields =
                Delayed.return (fields.%[field_idx] <- sub_block)
              in
              let block =
                Structural
                  {
                    ty = enum_ty;
                    content = Enum { discr; fields = new_fields };
                  }
              in
              ((v, block), lk)
          | Plus (_, i, ty') :: rest, _ ->
              let return_and_update' t ~lk =
                (* TODO: I need to pass the lk too here, but I'll do this when I make the right monad transformer *)
                aux ~lk t rest
              in
              frame_slice ~tyenv ~lk ~can_extend:false
                ~return_and_update:return_and_update' ~ty:ty' ~current_offset:i
                t [] Expr.one_i
          | (op :: _ as path), Structural { content = Symbolic s; ty } ->
              let variant = Projections.variant op in
              let** this_block = semi_concretize ~tyenv ~variant ty s in
              aux ~lk this_block path
          | _ :: _, Structural { content = Missing; ty } ->
              let this_block = structural_missing ~tyenv ty in
              aux ~lk this_block path
          | _ ->
              Fmt.failwith "Couldn't resolve path: (block: %a, path: %a)" pp t
                (Fmt.Dump.list Projections.pp_op)
                path
        in
        aux ~lk t path

  let frame_slice_outer
      ~tyenv
      ~return_and_update
      ~lk
      ~ty
      (outer : outer)
      (proj : Projections.t)
      size =
    Logging.tmi (fun m ->
        m "Currently in the following block: %a" pp_outer outer);
    let* () =
      let base_equals =
        Formula.Infix.( #== )
          (Option.value ~default:(Expr.EList []) proj.base)
          outer.offset
      in
      if%ent base_equals then Delayed.return ()
      else failwith "Trees need to be extended?"
    in
    let t = outer.root in
    Logging.verbose (fun m ->
        m "Before path reduction: %a" Projections.pp_path proj.from_base);
    let path = Projections.Reduction.reduce_op_list proj.from_base in
    Logging.verbose (fun m ->
        m "After path reduction: %a" Projections.pp_path path);
    let++ (ret, root), lk =
      frame_slice ~can_extend:true ~ty ~lk ~tyenv ~return_and_update t path size
    in
    ((ret, { outer with root }), lk)

  let frame_proj
      ~tyenv
      ~(return_and_update : t -> lk:LK.t -> (('a * t) * LK.t, Err.t) DR.t)
      ~ty
      (outer : outer)
      (proj : Projections.t)
      ~lk =
    Logging.tmi (fun m ->
        m "Currently in the following block: %a" pp_outer outer);
    let* () =
      let base_equals =
        Formula.Infix.( #== )
          (Option.value ~default:(Expr.EList []) proj.base)
          outer.offset
      in
      if%ent base_equals then Delayed.return ()
      else
        Fmt.failwith
          "Trees need to be extended? proj.base: %a, outer.offset: %a"
          (Fmt.Dump.option Expr.pp) proj.base Expr.pp outer.offset
    in
    let t = outer.root in
    Logging.verbose (fun m ->
        m "Before path reduction: %a" Projections.pp_path proj.from_base);
    let path = Projections.Reduction.reduce_op_list proj.from_base in
    Logging.verbose (fun m ->
        m "After path reduction: %a" Projections.pp_path path);
    let++ (ret, root), lk =
      frame_path ~tyenv ~lk ~return_and_update ~ty t path
    in
    ((ret, { outer with root }), lk)

  let copy_nonoverlapping
      ~tyenv
      from_block
      from_proj
      to_block
      to_proj
      ty
      size
      ~lk =
    if%ent Formula.Infix.(size #== Expr.zero_i) then DR.ok (to_block, lk)
    else
      let () =
        Logging.verbose (fun m ->
            m "copy_nonoverlapping: about to load copy from the 'from' block")
      in
      let** (copy, _), lk =
        frame_slice_outer ~tyenv ~lk
          ~return_and_update:(fun t ~lk -> DR.ok ((t, t), lk))
          ~ty from_block from_proj size
      in
      Logging.verbose (fun m ->
          m "copy_nonoverlapping: about to write copy to the 'to' block");
      let return_and_update _t ~lk = DR.ok (((), copy), lk) in
      let++ ((), mem), lk =
        frame_slice_outer ~lk ~tyenv ~return_and_update ~ty to_block to_proj
          size
      in
      (mem, lk)

  let load_proj ~loc ~tyenv t proj ty copy =
    let return_and_update t ~lk =
      let++ value, lk =
        let result = to_rust_value ~lk ~tyenv ~ty t in
        DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
      in
      let updated =
        if copy then t
        else
          let new_ty = Option.value ~default:ty (structural_ty_opt t) in
          uninitialized ~tyenv new_ty
      in
      ((value, updated), lk)
    in
    frame_proj ~tyenv ~return_and_update ~ty t proj

  let cons_proj ~loc ~tyenv ~lk t proj ty =
    let return_and_update t ~lk =
      let++ value, lk =
        let result = to_rust_value ~tyenv ~lk ~ty t in
        DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
      in
      let new_ty = Option.value ~default:ty (structural_ty_opt t) in
      ((value, missing new_ty), lk)
    in
    frame_proj ~tyenv ~lk ~return_and_update ~ty t proj

  let prod_proj ~tyenv ~lk t proj ty value =
    let* new_block =
      let return_and_update block ~lk =
        match missing_qty block with
        | Some Totally ->
            let open DR.Syntax in
            let++ value = of_rust_value ~tyenv ~ty value in
            (((), value), lk)
        | _ -> Delayed.vanish ()
        (* Duplicated resources *)
      in
      let++ (_, new_block), lk =
        frame_proj ~tyenv ~ty ~lk ~return_and_update t proj
      in
      (new_block, lk)
    in
    match new_block with
    | Ok (x, lk) -> Delayed.return (x, lk)
    | Error _ -> Delayed.vanish ()

  let replace_proj ~lk ~tyenv ~ty outer proj new_block =
    let return_and_update block ~lk =
      let* eq, lk = block_size_equal ~lk block new_block in
      if%ent eq then DR.ok (((), new_block), lk)
      else failwith "Could not replace projection, types do not match"
    in
    let++ (_, new_block), _ =
      frame_proj ~tyenv ~ty ~lk:LK.none ~return_and_update outer proj
    in
    (new_block, lk)

  let cons_uninit ~loc:_ ~tyenv t proj ty =
    let return_and_update t ~lk =
      let error () =
        Fmt.kstr (fun s -> DR.error (Err.LogicError s)) "Not uninit: %a" pp t
      in
      match t with
      | Structural { content = Uninit; ty } -> DR.ok (((), missing ty), lk)
      | Structural { content = SymbolicMaybeUninit s; ty } ->
          if%ent Symb_opt.is_none s then DR.ok (((), missing ty), lk)
          else error ()
      | Structural { content = ManySymbolicMaybeUninit s; ty } ->
          if%ent Symb_opt.is_all_none s then DR.ok (((), missing ty), lk)
          else error ()
      | _ -> error ()
    in
    frame_proj ~tyenv ~return_and_update ~ty t proj

  let prod_uninit ~loc:_ ~tyenv t proj ty ~lk =
    let open DR.Syntax in
    let* result =
      let return_and_update block ~lk =
        match missing_qty block with
        | Some Totally ->
            let value = uninitialized ~tyenv ty in
            DR.ok (((), value), lk)
        | _ -> Delayed.vanish ()
        (* Duplicated resource *)
      in
      let++ (_, new_block), lk =
        frame_proj ~tyenv ~ty ~return_and_update ~lk t proj
      in
      (new_block, lk)
    in
    match result with
    | Ok (x, lk) -> Delayed.return (x, lk)
    | Error _ -> Delayed.vanish ()

  let cons_maybe_uninit ~loc ~lk ~tyenv t proj ty =
    let return_and_update t ~lk =
      match missing_qty t with
      | Some qty -> DR.error (Err.Missing_proj (loc, proj, qty))
      | None ->
          let++ value, lk = to_rust_maybe_uninit ~tyenv ~lk ~loc ~proj ~ty t in
          let new_ty = Option.value ~default:ty (structural_ty_opt t) in
          ((value, missing new_ty), lk)
    in
    frame_proj ~tyenv ~lk ~return_and_update ~ty t proj

  let prod_maybe_uninit ~loc:_ ~lk ~tyenv t proj ty maybe_value =
    let* result =
      let return_and_update block ~lk =
        match missing_qty block with
        | Some Totally -> (
            let* maybe_value = Symb_opt.of_expr maybe_value in
            match maybe_value with
            | None ->
                let value = uninitialized ~tyenv ty in
                DR.ok (((), value), lk)
            | Some value ->
                let++ value = of_rust_value ~tyenv ~ty value in
                (((), value), lk)
            | Symb e ->
                DR.ok
                  (((), Structural { content = SymbolicMaybeUninit e; ty }), lk)
            )
        | _ -> Delayed.vanish ()
        (* Duplicated resource *)
      in
      let++ (_, new_block), lk =
        frame_proj ~tyenv ~lk ~ty ~return_and_update t proj
      in
      (new_block, lk)
    in
    match result with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let cons_many_maybe_uninits ~loc ~tyenv ~lk t proj ty size =
    let return_and_update t ~lk =
      match missing_qty t with
      | Some qty -> DR.error (Missing_proj (loc, proj, qty))
      | None ->
          let++ value, lk =
            to_rust_many_maybe_uninits ~tyenv ~lk ~loc ~proj ~ty ~size t
          in
          let new_ty = Option.value ~default:ty (structural_ty_opt t) in
          ((value, missing new_ty), lk)
    in
    frame_slice_outer ~tyenv ~lk ~ty ~return_and_update t proj size

  let prod_many_maybe_uninits ~loc:_ ~tyenv ~lk t proj ty size maybe_values =
    let* result =
      let return_and_update t ~lk =
        match missing_qty t with
        | Some Totally ->
            let content = ManySymbolicMaybeUninit maybe_values in
            let ty = Ty.array ty size in
            DR.ok (((), Structural { ty; content }), lk)
        | _ -> Delayed.vanish ()
      in
      let++ (_, new_block), lk =
        frame_slice_outer ~tyenv ~lk ~ty ~return_and_update t proj size
      in
      (new_block, lk)
    in
    match result with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let store_proj ~loc ~tyenv ~lk t proj ty value =
    let return_and_update block ~lk =
      match missing_qty block with
      | Some qty -> DR.error (Err.Missing_proj (loc, proj, qty))
      | None ->
          let++ block = of_rust_value ~tyenv ~ty value in
          (((), block), lk)
    in
    let++ (_, new_block), lk =
      frame_proj ~tyenv ~lk ~ty ~return_and_update t proj
    in
    (new_block, lk)

  let get_discr ~tyenv ~lk t proj enum_typ =
    let return_and_update (block : t) ~lk =
      match block with
      | Structural { content = Enum enum; ty } when Ty.equal enum_typ ty ->
          DR.ok ((Expr.int enum.discr, block), lk)
      | Structural { content = Symbolic expr; ty } when Ty.equal enum_typ ty ->
          let open Formula.Infix in
          if%sat
            (Expr.typeof expr) #== (Expr.type_ ListType)
            #&& ((Expr.list_length expr) #== (Expr.int 2))
          then DR.ok ((Expr.list_nth expr 0, block), lk)
          else too_symbolic expr
      | _ ->
          Logging.verbose (fun m -> m "get_discr error: %a" pp block);
          DR.error Invalid_enum
    in
    let++ (discr, _), lk =
      frame_proj ~tyenv ~lk ~return_and_update ~ty:enum_typ t proj
    in
    (discr, lk)

  let deinit ~tyenv ~lk t proj ty =
    let return_and_update _block ~lk =
      DR.ok (((), uninitialized ~tyenv ty), lk)
    in
    let++ (_, new_block), lk =
      frame_proj ~tyenv ~lk ~ty ~return_and_update t proj
    in
    (new_block, lk)

  let rec substitution ~tyenv ~subst_expr (t : t) =
    let substitution = substitution ~tyenv ~subst_expr in
    let get_structural = function
      | Structural s -> s
      | _ -> raise (Invalid_argument "get_structural")
    in
    let rec substitute_structural { ty; content } =
      let ty = Ty.substitution ~subst_expr ty in
      match content with
      | Symbolic e ->
          let new_e = subst_expr e in
          if Expr.equal new_e e then DR.ok { ty; content = Symbolic e }
          else
            let++ s = of_rust_value ~tyenv ~ty new_e in
            get_structural s
      | SymbolicMaybeUninit e ->
          let new_e = subst_expr e in
          if Expr.equal new_e e then
            DR.ok { ty; content = SymbolicMaybeUninit e }
          else
            let++ new_tree = of_rust_maybe_uninit ~tyenv ~ty new_e in
            get_structural new_tree
      | ManySymbolicMaybeUninit e ->
          let new_e = subst_expr e in
          if Expr.equal new_e e then
            DR.ok { ty; content = ManySymbolicMaybeUninit e }
          else
            let++ new_tree = of_rust_many_maybe_uninit ~tyenv ~ty new_e in
            get_structural new_tree
      | Array lst ->
          let++ lst = DR_list.map substitution lst in
          { ty; content = Array lst }
      | Fields lst ->
          let++ lst = DR_list.map substitution lst in
          { ty; content = Fields lst }
      | Enum { fields; discr } ->
          let++ fields = DR_list.map substitution fields in
          { ty; content = Enum { fields; discr } }
      | Uninit | Missing -> DR.ok { ty; content }
    and substitute_laid_out { structural; children; range; index_ty } =
      let range = Range.substitute ~subst_expr range in
      let index_ty = Ty.substitution ~subst_expr index_ty in
      let** structural =
        match structural with
        | None -> DR.ok None
        | Some s ->
            let++ s = substitute_structural s in
            Some s
      in
      let++ children =
        match children with
        | Some (left, right) ->
            let** left = substitute_laid_out left in
            let++ right = substitute_laid_out right in
            Some (left, right)
        | None -> DR.ok None
      in
      { structural; children; range; index_ty }
    in
    match t with
    | Structural s ->
        let++ s = substitute_structural s in
        Structural s
    | Laid_out_root lc ->
        let++ lc = substitute_laid_out lc in
        Laid_out_root lc

  let outer_substitution ~tyenv ~lk ~subst_expr t =
    let** root = substitution ~tyenv ~subst_expr t.root in
    let* offset = Delayed.reduce (subst_expr t.offset) in
    let new_proj = Projections.of_expr offset in
    let offset = Option.value ~default:(Expr.EList []) new_proj.base in
    if List.is_empty new_proj.from_base then DR.ok ({ offset; root }, lk)
    else
      match root with
      | Structural { ty; _ } ->
          let ty = Ty.substitution ~subst_expr ty in
          let new_root =
            outer_missing ~offset ~tyenv
              (Projections.base_ty ~leaf_ty:ty new_proj.from_base)
          in
          replace_proj ~lk ~tyenv ~ty new_root new_proj root
      | _ ->
          let offset = Projections.to_expr new_proj in
          DR.ok ({ offset; root }, lk)

  let merge_outer (o1 : outer) (o2 : outer) =
    let+ () =
      let eq = Formula.Infix.( #== ) o1.offset o2.offset in
      if%ent eq then Delayed.return ()
      else
        failwith "Not handled yet: merging outer blocks with different offsets"
    in
    match (o1.root, o2.root) with
    | Structural { content = Missing; _ }, _ -> o2
    | _, Structural { content = Missing; _ } -> o1
    | _ ->
        failwith
          "Not handled yet: merging outer blocks with non-Missing root on both \
           side"
end

module MemMap = Map.Make (String)

type block = T of TreeBlock.outer | Freed
type t = block MemMap.t

let block_lvars = function
  | Freed -> Utils.Containers.SS.empty
  | T outer -> TreeBlock.outer_lvars outer

let lvars t =
  let open Utils.Containers in
  MemMap.fold (fun _ block acc -> SS.union acc (block_lvars block)) t SS.empty

let find_not_freed loc mem =
  let block = MemMap.find_opt loc mem in
  match block with
  | Some (T t) -> DR.ok t
  | Some Freed -> DR.error (Use_after_free loc)
  | None -> DR.error (MissingBlock loc)

let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let alloc ~tyenv (heap : t) ty =
  let loc = ALoc.alloc () in
  let new_block = TreeBlock.uninitialized_outer ~tyenv ty in
  let new_heap = MemMap.add loc (T new_block) heap in
  (loc, new_heap)

let load ~tyenv ~lk (mem : t) loc proj ty copy =
  if%sat TypePreds.empty_array ty then
    let value = Expr.EList [] in
    DR.ok ((value, mem), lk)
  else (
    (* let* is_zst, lk = LK.is_zst ~lk ~tyenv ty in
       if%sat is_zst then
         let value = Ty.value_of_zst ~tyenv ty in
         DR.ok ((value, mem), lk)
       else*)
    Logging.tmi (fun m -> m "Found block: %s" loc);
    let** block = find_not_freed loc mem in
    let++ (v, new_block), lk =
      TreeBlock.load_proj ~lk ~loc ~tyenv block proj ty copy
    in
    let new_mem = MemMap.add loc (T new_block) mem in
    ((v, new_mem), lk))

let store ~tyenv ~lk (mem : t) loc proj ty value =
  if%sat TypePreds.empty_array ty then DR.ok (mem, lk)
  else
    (* let* is_zst, lk = LK.is_zst ~lk ~tyenv ty in
       if%sat is_zst then DR.ok (mem, lk)
       else *)
    let** block = find_not_freed loc mem in
    let++ new_block, lk =
      TreeBlock.store_proj ~loc ~tyenv ~lk block proj ty value
    in
    (MemMap.add loc (T new_block) mem, lk)

let copy_nonoverlapping
    ~tyenv
    ~lk
    mem
    ~from:(from_loc, from_proj)
    ~to_:(to_loc, to_proj)
    ty
    size =
  if String.equal from_loc to_loc then
    failwith
      "copy_nonoverlapping: from and to are the same location, to implement. \
       Trivial but no time"
  else
    if%sat Formula.Infix.(size #== Expr.zero_i) then DR.ok (mem, lk)
    else
      let** from_block = find_not_freed from_loc mem in
      let** to_block = find_not_freed to_loc mem in
      let++ new_to_block, lk =
        TreeBlock.copy_nonoverlapping ~tyenv ~lk from_block from_proj to_block
          to_proj ty size
      in
      (MemMap.add to_loc (T new_to_block) mem, lk)

let cons_value ~tyenv ~lk (mem : t) loc proj ty =
  if%sat TypePreds.empty_array ty then
    let value = Expr.EList [] in
    DR.ok ((value, mem), lk)
  else
    (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
       if%ent is_zst then
         let value = Ty.value_of_zst ~tyenv ty in
         DR.ok ((value, mem), lk)
       else *)
    let** block = find_not_freed loc mem in
    let++ (value, outer), lk =
      TreeBlock.cons_proj ~loc ~tyenv ~lk block proj ty
    in
    let new_heap =
      if TreeBlock.outer_is_empty outer then MemMap.remove loc mem
      else MemMap.add loc (T outer) mem
    in
    ((value, new_heap), lk)

let prod_value ~tyenv ~lk (mem : t) loc (proj : Projections.t) ty value =
  if%sat TypePreds.empty_array ty then
    Delayed.return ~learned:[ Formula.Infix.(value #== (EList [])) ] (mem, lk)
  else
    (* TODO: is_zst will be true for empty arrays anyway,
       so I'll be able to remove the above. *)
    (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
       if%sat is_zst then
         Delayed.return
           ~learned:[ TypePreds.valid_zst_value ~tyenv ty value ]
           (mem, lk)
       else *)
    let () =
      Logging.tmi (fun m -> m "Producing with proj: %a" Projections.pp proj)
    in
    let root =
      match MemMap.find_opt loc mem with
      | Some (T root) -> root
      | Some Freed -> failwith "use after free"
      | None ->
          TreeBlock.outer_missing
            ~offset:(Option.value ~default:(Expr.EList []) proj.base)
            ~tyenv
            (Projections.base_ty ~leaf_ty:ty proj.from_base)
    in
    let+ new_block, lk = TreeBlock.prod_proj ~tyenv ~lk root proj ty value in
    (MemMap.add loc (T new_block) mem, lk)

let cons_uninit ~tyenv ~lk (mem : t) loc proj ty =
  (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
     if%sat is_zst then DR.ok (mem, lk)
     else *)
  if%sat TypePreds.empty_array ty then DR.ok (mem, lk)
  else
    let** block = find_not_freed loc mem in
    let++ ((), outer), lk =
      TreeBlock.cons_uninit ~loc ~tyenv ~lk block proj ty
    in
    let new_heap =
      if TreeBlock.outer_is_empty outer then MemMap.remove loc mem
      else MemMap.add loc (T outer) mem
    in
    (new_heap, lk)

let prod_uninit ~tyenv ~lk (mem : t) loc (proj : Projections.t) ty =
  (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
     if%sat is_zst then Delayed.return (mem, lk)
     else *)
  if%sat TypePreds.empty_array ty then Delayed.return (mem, lk)
  else
    let root =
      match MemMap.find_opt loc mem with
      | Some (T root) -> root
      | Some Freed -> failwith "use after free"
      | None ->
          TreeBlock.outer_missing
            ~offset:(Option.value ~default:(Expr.EList []) proj.base)
            ~tyenv
            (Projections.base_ty ~leaf_ty:ty proj.from_base)
    in
    let+ new_block, lk = TreeBlock.prod_uninit ~loc ~tyenv ~lk root proj ty in
    (MemMap.add loc (T new_block) mem, lk)

let cons_maybe_uninit ~tyenv ~lk (mem : t) loc proj ty =
  (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
     if%ent is_zst then
       let value = Symb_opt.zst_value_maybe_uninit ~tyenv ty in
       DR.ok (value, mem, lk)
     else *)
  if%sat TypePreds.empty_array ty then
    let value = Symb_opt.some (Expr.EList []) in
    DR.ok (value, mem, lk)
  else
    let** block = find_not_freed loc mem in
    let++ (value, outer), lk =
      TreeBlock.cons_maybe_uninit ~loc ~tyenv ~lk block proj ty
    in
    let new_heap =
      if TreeBlock.outer_is_empty outer then MemMap.remove loc mem
      else MemMap.add loc (T outer) mem
    in
    (value, new_heap, lk)

let prod_maybe_uninit
    ~tyenv
    ~lk
    (mem : t)
    loc
    (proj : Projections.t)
    ty
    maybe_value =
  (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
     if%sat is_zst then
       Delayed.return
         ~learned:[ Symb_opt.valid_zst_maybe_uninit ~tyenv ty maybe_value ]
         (mem, lk)
     else *)
  if%sat TypePreds.empty_array ty then
    Delayed.return
      ~learned:
        [ Formula.Infix.(maybe_value #== (Symb_opt.some (Expr.EList []))) ]
      (mem, lk)
  else
    let root =
      match MemMap.find_opt loc mem with
      | Some (T root) -> root
      | Some Freed -> failwith "use after free"
      | None ->
          TreeBlock.outer_missing
            ~offset:(Option.value ~default:(Expr.EList []) proj.base)
            ~tyenv
            (Projections.base_ty ~leaf_ty:ty proj.from_base)
    in
    let+ new_block, lk =
      TreeBlock.prod_maybe_uninit ~loc ~tyenv ~lk root proj ty maybe_value
    in
    (MemMap.add loc (T new_block) mem, lk)

let cons_many_maybe_uninits ~tyenv ~lk (mem : t) loc proj ty size =
  if%sat Formula.Infix.(size #== Expr.zero_i) then DR.ok (Expr.EList [], mem, lk)
  else
    (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
       if%ent is_zst then
         let value = Symb_opt.zst_array_maybe_uninit ~tyenv ty size in
         DR.ok (value, mem, lk)
       else *)
    let** block = find_not_freed loc mem in
    let++ (value, outer), lk =
      TreeBlock.cons_many_maybe_uninits ~loc ~tyenv ~lk block proj ty size
    in
    let new_heap =
      if TreeBlock.outer_is_empty outer then MemMap.remove loc mem
      else MemMap.add loc (T outer) mem
    in
    (value, new_heap, lk)

let prod_many_maybe_uninits
    ~tyenv
    ~lk
    (mem : t)
    loc
    (proj : Projections.t)
    ty
    size
    maybe_values =
  if%sat Formula.Infix.(size #== Expr.zero_i) then
    Delayed.return
      ~learned:[ Formula.Infix.(maybe_values #== (Expr.EList [])) ]
      (mem, lk)
  else
    (* let* is_zst, lk = LK.is_zst ~tyenv ~lk ty in
       if%sat is_zst then
         Delayed.return
           ~learned:
             [ Symb_opt.valid_zst_array_maybe_uninit ~tyenv ty size maybe_values ]
           (mem, lk)
       else *)
    let root =
      match MemMap.find_opt loc mem with
      | Some (T root) -> root
      | Some Freed -> failwith "use after free"
      | None ->
          TreeBlock.outer_missing
            ~offset:(Option.value ~default:(Expr.EList []) proj.base)
            ~tyenv
            (Projections.base_ty ~leaf_ty:(Ty.array ty size) proj.from_base)
    in
    let+ new_block, lk =
      TreeBlock.prod_many_maybe_uninits ~loc ~tyenv ~lk root proj ty size
        maybe_values
    in
    (MemMap.add loc (T new_block) mem, lk)

let deinit ~tyenv ~lk (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ new_block, lk = TreeBlock.deinit ~tyenv ~lk block proj ty in
  (MemMap.add loc (T new_block) mem, lk)

let free ~lk (mem : t) loc ty =
  let** block = find_not_freed loc mem in
  (* TODO: implement freeability properly *)
  (*
  let base_is_empty =
    let open Formula.Infix in
    block.offset #== (Expr.EList [])
  in
  if%ent base_is_empty then *)
  let* eq, lk = TreeBlock.block_size_equal_ty_size ~lk ~block:block.root ~ty in
  if%ent eq then DR.ok (MemMap.add loc Freed mem, lk) else DR.error Invalid_free
(* else Fmt.failwith "Not freeable!" *)

let load_discr ~tyenv ~lk (mem : t) loc proj enum_typ =
  let** block = find_not_freed loc mem in
  TreeBlock.get_discr ~tyenv ~lk block proj enum_typ

let block_assertions ~loc block =
  match block with
  | T block -> TreeBlock.outer_assertions ~loc block
  | Freed ->
      let cp = Actions.cp_to_name Freed in
      Seq.return (Asrt.GA (cp, [ loc ], []))

let assertions ~tyenv:_ (mem : t) =
  let one_block (loc, block) =
    block_assertions ~loc:(Expr.loc_from_loc_name loc) block
  in
  MemMap.to_seq mem |> Seq.flat_map one_block |> List.of_seq

let empty : t = MemMap.empty

let pp_block ft = function
  | Freed -> Fmt.pf ft "FREED"
  | T t -> TreeBlock.pp_outer ft t

let pp : t Fmt.t =
  let open Fmt in
  iter_bindings ~sep:(any "@\n") MemMap.iter
    (parens (pair ~sep:(any "-> ") string pp_block))

let sure_is_nonempty =
  MemMap.exists (fun _ block ->
      match block with
      | Freed -> true
      | T outer -> not (TreeBlock.outer_is_empty outer))

(****** Producers, we put entire stuff here so we can use in subst *****)

let execute_prod_value ~tyenv ~lk heap args =
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = Projections.of_expr_reduce proj in
      prod_value ~tyenv ~lk heap loc_name proj ty value
  | _ -> Fmt.failwith "Invalid arguments for prod_value"

let execute_prod_uninit ~tyenv ~lk heap args =
  match args with
  | [ loc; proj; ty ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = Projections.of_expr_reduce proj in
      prod_uninit ~tyenv ~lk heap loc_name proj ty
  | _ -> Fmt.failwith "Invalid arguments for prod_uninit"

let execute_prod_maybe_uninit ~tyenv ~lk heap args =
  match args with
  | [ loc; proj; ty; value ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = Projections.of_expr_reduce proj in
      prod_maybe_uninit ~tyenv ~lk heap loc_name proj ty value
  | _ -> Fmt.failwith "Invalid arguments for prod_maybe_uninit"

let execute_prod_many_maybe_uninits ~tyenv ~lk heap args =
  match args with
  | [ loc; proj; ty; size; maybe_values ] ->
      let ty = Ty.of_expr ty in
      let* loc_name = resolve_or_create_loc_name loc in
      let* proj = Projections.of_expr_reduce proj in
      prod_many_maybe_uninits ~tyenv ~lk heap loc_name proj ty size maybe_values
  | _ -> Fmt.failwith "Invalid arguments for prod_many_maybe_uninits"

(****** Things to do with susbtitution! *******)
let produce_heap_cp ~core_pred =
  match Actions.cp_of_name core_pred with
  | Value -> execute_prod_value
  | Uninit -> execute_prod_uninit
  | Maybe_uninit -> execute_prod_maybe_uninit
  | Many_maybe_uninits -> execute_prod_many_maybe_uninits
  | Freed -> Fmt.failwith "Produce freed not implemented yet"
  | Ty_size | Lft | Value_observer | Pcy_controller | Pcy_value | Observation ->
      Fmt.failwith "Not a heap core predicate"

let substitution ~tyenv ~lk heap subst =
  let open Gillian.Symbolic in
  if Subst.is_empty subst then DR.ok (heap, lk)
  else
    let loc_subst =
      Subst.fold subst
        (fun l r acc ->
          match l with
          | ALoc loc | Lit (Loc loc) -> (loc, r) :: acc
          | _ -> acc)
        []
    in
    let subst_expr = Subst.subst_in_expr subst ~partial:true in
    let** new_mapping, lk =
      MemMap.to_seq heap |> List.of_seq
      |> DR_list.map_with_lk ~lk (fun ~lk (loc, block) ->
             let++ block, lk =
               match block with
               | Freed -> DR.ok (Freed, lk)
               | T block ->
                   let++ block, lk =
                     TreeBlock.outer_substitution ~lk ~tyenv ~subst_expr block
                   in
                   (T block, lk)
             in
             ((loc, block), lk))
    in
    let map_with_tree_subst = List.to_seq new_mapping |> MemMap.of_seq in
    DR_list.fold_with_lk ~lk
      (fun ~lk current_map (old_loc, new_loc) ->
        Logging.verbose (fun m ->
            m "About to merge locs: %s -> %a" old_loc Expr.pp new_loc);
        let new_loc =
          match new_loc with
          | Lit (Loc loc) | ALoc loc -> loc
          | _ ->
              Fmt.failwith
                "substitution failed, for location, target isn't a location"
        in
        match
          ( MemMap.find_opt old_loc current_map,
            MemMap.find_opt new_loc current_map )
        with
        | None, None | None, Some _ -> DR.ok (current_map, lk)
        | Some tree, None ->
            let new_map =
              MemMap.remove old_loc current_map |> MemMap.add new_loc tree
            in
            DR.ok (new_map, lk)
        | Some tree_left, Some _ ->
            (* Merging trees is... difficult
               So we transform one into assertions and then produce in the other *)
            Logging.verbose (fun m -> m "Actualling merging two trees");
            let map_without_left = MemMap.remove old_loc current_map in
            let left_cps =
              (* We create assertions but locating the content at the new loc *)
              block_assertions ~loc:(Expr.loc_from_loc_name new_loc) tree_left
              |> (Seq.map @@ function
                  | Asrt.GA (cp, ins, outs) -> (cp, ins @ outs)
                  | _ -> failwith "Assertions are not core predicates ??")
              |> List.of_seq
            in
            let+ result =
              Delayed_list.fold_with_lk ~lk
                (fun ~lk map (cp, args) ->
                  produce_heap_cp ~core_pred:cp ~tyenv ~lk map args)
                map_without_left left_cps
            in
            Ok result)
      map_with_tree_subst loc_subst
