open Gillian.Gil_syntax
open List_utils.Infix
open Gillian.Monadic
open Err
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
module Tyenv = Common.Tyenv
module Actions = Common.Actions
open Delayed_utils

exception NotConcrete of string

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
    | Ref { ty = Slice _; mut = true } ->
        if !Common.R_config.prophecy_mode then valid_fat_mut_ref_pcy e
        else valid_fat_ptr e
    | Ref { mut = true; ty = _ } ->
        if !Common.R_config.prophecy_mode then valid_thin_mut_ref_pcy e
        else valid_thin_ptr e
    | Ref { mut = false; ty = Slice _ } -> valid_fat_ptr e
    | Ref { mut = false; ty = _ } -> valid_thin_ptr e
    | Ptr { ty = Slice _; _ } -> valid_fat_ptr e
    | Ptr _ -> valid_thin_ptr e
    | Scalar Char -> True
    | _ ->
        Fmt.failwith "Not a leaf type, can't express validity: %a of type %a"
          Expr.pp e Ty.pp scalar_ty
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

  let new_expr_list_all_none size =
    let e = Expr.LVar (LVar.alloc ()) in
    let learned = [ (Expr.list_length e) #== size; is_all_none ~size e ] in
    Delayed.return ~learned e
end

let too_symbolic e =
  Delayed.map (Delayed.reduce e) (fun e -> Error (Too_symbolic e))

let not_concrete msgf = Fmt.kstr (fun s -> raise (NotConcrete s)) msgf

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
end

module TreeBlock = struct
  type t = { ty : Ty.t; content : tree_content }

  and tree_content =
    | Structural of structural_content
    | Layed_out_root of layed_out_content * Ty.t

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
            which has type Option<T>.
            If the value is None, then it's the equivalent of an [Uninit] node
            If the value is [Some x] then it's the equivalent of a [Symbolic x] node. *)
    | ManySymbolicMaybeUninit of Expr.t
        (** Same as above, except that the expression is of type Seq<Option<T>>, were each element
            of the sequence behaves as above.  *)

  and layed_out_content = {
    structural : structural_content option;
    (* None means we need to look at the children *)
    range : Range.t;
    children : (layed_out_content * Ty.t) list option;
  }

  type outer = { offset : Expr.t; root : t }

  let rec map_lc_ranges ~f lc =
    let children =
      Option.map
        (List.map (fun (l, ty) -> (map_lc_ranges ~f l, ty)))
        lc.children
    in
    let range = f lc.range in
    { lc with children; range }

  let lossless_flatten t =
    match t.content with
    | Layed_out_root ({ structural = Some structural; children = None; _ }, _)
      -> { content = Structural structural; ty = t.ty }
    | _ -> t

  let offset_layed_out ~by lc =
    if Expr.is_concrete_zero_i by then lc
    else map_lc_ranges ~f:(Range.offset ~by) lc

  let rec reinterpret_lc_ranges ~lk ~from_ty ~to_ty lc =
    let rec aux ~lk acc children =
      match children with
      | [] -> Delayed.return (List.rev acc, lk)
      | (child, ty) :: rest ->
          let* child, lk = reinterpret_lc_ranges ~lk ~from_ty ~to_ty child in
          aux ~lk ((child, ty) :: acc) rest
    in
    let* range, lk = Range.reinterpret ~lk ~from_ty ~to_ty lc.range in
    let+ children, lk =
      match lc.children with
      | None -> Delayed.return (None, lk)
      | Some children ->
          let+ children, lk = aux ~lk [] children in
          (Some children, lk)
    in
    ({ lc with range; children }, lk)

  (* let offset_block ~by lc =


     let make_relative block =
       match block.content with
       | Structural _ -> (block, Fun.id)
       | Layed_out_root (lc, ty) ->
         let offset = fst lc.range in
         let lc = offset_layed_out ~by lc in
         ({ ty; content = Layed_out_root (lc, ty) }, Range.offset ~by, ty) *)

  let rec lvars { content; ty } =
    let open Gillian.Utils.Containers in
    let rec lvars_layed_out { structural; range; children } =
      let lvars_children =
        Option.fold ~none:SS.empty
          ~some:(fun l ->
            List.fold_left
              (fun acc (l, ty) ->
                SS.union acc (lvars_layed_out l) |> SS.union (Ty.lvars ty))
              SS.empty l)
          children
      in
      Range.lvars range |> SS.union lvars_children
      |> SS.union (Option.fold ~none:SS.empty ~some:lvars_structural structural)
    and lvars_structural = function
      | Fields l | Array l | Enum { fields = l; _ } ->
          List.fold_left (fun acc t -> SS.union acc (lvars t)) SS.empty l
      | SymbolicMaybeUninit e | Symbolic e | ManySymbolicMaybeUninit e ->
          Expr.lvars e
      | Uninit | Missing -> SS.empty
    in
    let lvars_content = function
      | Structural structure -> lvars_structural structure
      | Layed_out_root (root, ty) ->
          Ty.lvars ty |> SS.union (lvars_layed_out root)
    in
    SS.union (Ty.lvars ty) (lvars_content content)

  let outer_lvars outer =
    let open Utils.Containers in
    SS.union (lvars outer.root) (Expr.lvars outer.offset)

  let rec is_empty block =
    match block.content with
    | Structural Missing -> true
    | Structural (Fields fields | Array fields) -> List.for_all is_empty fields
    | _ -> false
  (* Supposedly, Lazy can never be empty. *)

  let outer_is_empty outer = is_empty outer.root

  let rec missing_qty t : Qty.t option =
    match t.content with
    | Structural Missing -> Some Totally
    | Layed_out_root ({ structural = None; children; _ }, index_ty) ->
        let qtys =
          Option.get_or ~msg:"Lazy without children" children
          |> List.map (fun (l, ty) ->
                 missing_qty { content = Layed_out_root (l, index_ty); ty })
        in

        (* an empty list would return true on the following forall *)
        (match qtys with
        | [] -> Fmt.failwith "0 children??"
        | _ -> ());
        if
          List.for_all
            (function
              | Some Qty.Totally -> true
              | _ -> false)
            qtys
        then Some Totally
        else if List.exists Option.is_some qtys then Some Partially
        else None
    | Layed_out_root ({ structural = Some structural; _ }, _) ->
        missing_qty { ty = t.ty; content = Structural structural }
    | Structural (Array fields | Fields fields | Enum { fields; _ }) -> (
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
        (Symbolic _ | Uninit | ManySymbolicMaybeUninit _ | SymbolicMaybeUninit _)
      -> None

  let totally_missing t =
    match missing_qty t with
    | Some Totally -> true
    | _ -> false

  let rec partially_missing t =
    match t.content with
    | Structural Missing -> true
    | Structural (Array fields | Fields fields | Enum { fields; _ }) ->
        List.exists partially_missing fields
    | Structural
        (Symbolic _ | Uninit | ManySymbolicMaybeUninit _ | SymbolicMaybeUninit _)
    | Layed_out_root _ -> false

  let missing ty = { ty; content = Structural Missing }

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a : %a" pp_content content Ty.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Structural s -> pp_structural ft s
    | Layed_out_root (root, ty) ->
        pf ft "INDEX BY %a <== %a" Ty.pp ty pp_layed_out root

  and pp_structural ft =
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

  and pp_layed_out ft { structural; range; children } =
    let open Fmt in
    pf ft "%a = %a" Range.pp range (Dump.option pp_structural) structural;
    match children with
    | None -> ()
    | Some children ->
        pf ft "  WITH CHILDREN:@ @[<v>%a@]"
          (list ~sep:(any "@\n") (Dump.pair pp_layed_out Ty.pp))
          children

  let pp_outer ft t =
    let open Fmt in
    pf ft "@[<v 2>[OFFSET: %a] %a @]" Expr.pp t.offset pp t.root

  let to_rust_value ?(current_proj = []) ~ty block :
      (Expr.t, Err.Conversion_error.t) DR.t =
    let () =
      if not (Ty.equal ty block.ty) then
        Fmt.failwith
          "To implement: casting in to_rust_value. Should be fairly rare case; \
           though happends in pointer transmutation."
    in
    let rec map_with_proj ~proj vec =
      let++ _, vec =
        List.fold_left
          (fun acc f ->
            let** i, acc = acc in
            let++ f = aux ~current_proj:(proj i :: current_proj) f in
            (i + 1, f :: acc))
          (DR.ok (0, []))
          vec
      in
      List.rev vec
    and aux ~current_proj { content; ty } :
        (Expr.t, Err.Conversion_error.t) DR.t =
      match content with
      | Layed_out_root ({ structural = Some structural; _ }, _) ->
          aux ~current_proj { content = Structural structural; ty }
      | Layed_out_root ({ structural = None; _ }, _) ->
          failwith "Reconstructing value from children not implemented yet"
      | Structural structural -> (
          match structural with
          | Fields v ->
              let proj i = Projections.Field (i, ty) in
              let++ fields = map_with_proj ~proj v in
              Expr.EList fields
          | Array v ->
              let total_size = List.length v in
              let proj i = Projections.Index (Expr.int i, ty, total_size) in
              let++ elements = map_with_proj ~proj v in
              Expr.EList elements
          | Enum { discr; fields } ->
              let proj i = Projections.VField (discr, ty, i) in
              let++ fields = map_with_proj ~proj fields in
              Expr.EList [ Expr.int discr; EList fields ]
          | Symbolic e -> DR.ok e
          | SymbolicMaybeUninit e ->
              if%ent Symb_opt.is_some e then DR.ok e
              else DR.error Err.Conversion_error.(Uninit, List.rev current_proj)
          | ManySymbolicMaybeUninit _e ->
              failwith
                "ManySymbolicMaybeUninit not implemented yet. It will be a \
                 forall"
          | Uninit ->
              DR.error Err.Conversion_error.(Uninit, List.rev current_proj)
          | Missing ->
              DR.error Err.Conversion_error.(Missing, List.rev current_proj))
    in
    aux ~current_proj block

  exception Tree_not_a_value

  (* Converts to a value only if there is no doubt that it can be done. *)
  let rec to_rust_value_exn t =
    match t.content with
    | Layed_out_root ({ structural = Some structural; _ }, _) ->
        to_rust_value_exn { content = Structural structural; ty = t.ty }
    | Layed_out_root ({ structural = None; _ }, _) ->
        Fmt.failwith "to_rust_value_exn: layed_out with None structural"
    | Structural structural -> (
        match structural with
        | Fields elements | Array elements ->
            let elements = List.map to_rust_value_exn elements in
            Expr.EList elements
        | Enum { discr; fields } ->
            let fields = List.map to_rust_value_exn fields in
            Expr.EList [ Expr.int discr; EList fields ]
        | Symbolic e -> e
        | Uninit | Missing | ManySymbolicMaybeUninit _ | SymbolicMaybeUninit _
          -> raise Tree_not_a_value)

  let to_rust_value_opt_no_reasoning t =
    try Some (to_rust_value_exn t) with Tree_not_a_value -> None

  let to_rust_maybe_uninit ~loc ~proj ~ty t =
    match t.content with
    | Structural Uninit ->
        let result = Symb_opt.to_expr None in
        DR.ok (result, missing t.ty)
    | Structural (SymbolicMaybeUninit s) when Ty.equal ty t.ty ->
        DR.ok (s, missing t.ty)
    | Structural (ManySymbolicMaybeUninit s)
      when Ty.is_array_of ~array_ty:t.ty ~inner_ty:ty ->
        DR.ok (Expr.list_nth s 0, missing t.ty)
    | _ ->
        let++ v =
          let result = to_rust_value ~ty t in
          DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
        in
        (Symb_opt.some v, missing t.ty)

  let to_rust_many_maybe_uninits ~ty ~size t =
    let of_structural ~node_ty = function
      | Uninit ->
          let+ result = Symb_opt.new_expr_list_all_none size in
          Ok result
      | ManySymbolicMaybeUninit s
        when Ty.is_array_of ~array_ty:node_ty ~inner_ty:ty -> DR.ok s
      | Symbolic s when Ty.equal ty node_ty ->
          DR.ok (Expr.EList [ Symb_opt.some s ])
      | SymbolicMaybeUninit s when Ty.equal ty node_ty ->
          DR.ok (Expr.EList [ s ])
      | _ -> Fmt.failwith "obtained %a for many_maybe_uninits" pp t
    in
    let rec of_layed_out ~node_ty { structural; range = _; children } =
      match structural with
      | Some s -> of_structural ~node_ty s
      | None ->
          let children =
            Option.get_or ~msg:"malformed: lazy without chidlren" children
          in
          let++ children =
            DR_list.map (fun (l, ty) -> of_layed_out ~node_ty:ty l) children
          in
          Expr.NOp (LstCat, children)
    in
    match t.content with
    | Structural s -> of_structural ~node_ty:t.ty s
    | Layed_out_root (lc, _) -> of_layed_out ~node_ty:t.ty lc

  let assertions ~loc ~base_offset block =
    let value_cp = Actions.cp_to_name Value in
    let uninit_cp = Actions.cp_to_name Uninit in
    let maybe_uninit_cp = Actions.cp_to_name Maybe_uninit in
    let many_maybe_uninit_cp = Actions.cp_to_name Many_maybe_uninits in
    let rec aux ~current_proj ({ content; ty } as block) =
      let ins ty =
        let proj =
          Projections.to_expr
            { base = base_offset; from_base = List.rev current_proj }
        in
        let ty = Ty.to_expr ty in
        [ loc; proj; ty ]
      in
      match to_rust_value_opt_no_reasoning block with
      | Some value -> Seq.return (Asrt.GA (value_cp, ins ty, [ value ]))
      | None -> (
          match content with
          | Layed_out_root ({ structural; children; range }, index_ty) -> (
              match (structural, children) with
              | Some structural, None ->
                  let current_proj =
                    Projections.Reduction.reduce_op_list
                      (current_proj @ [ Plus (Overflow, fst range, index_ty) ])
                  in
                  aux ~current_proj { content = Structural structural; ty }
              | _, Some children ->
                  List.to_seq children
                  |> Seq.concat_map (fun (k, ty) ->
                         aux ~current_proj
                           { content = Layed_out_root (k, index_ty); ty })
              | None, None ->
                  Fmt.failwith "malformed tree! Lazy without children")
          | Structural Uninit -> Seq.return (Asrt.GA (uninit_cp, ins ty, []))
          | Structural (SymbolicMaybeUninit s) ->
              Seq.return (Asrt.GA (maybe_uninit_cp, ins ty, [ s ]))
          | Structural (ManySymbolicMaybeUninit s) ->
              Seq.return (Asrt.GA (many_maybe_uninit_cp, ins ty, [ s ]))
          | Structural Missing -> Seq.empty
          | Structural (Fields v) ->
              let proj i = Projections.Field (i, ty) in
              List.to_seq v
              |> Seq.mapi (fun i f ->
                     aux ~current_proj:(proj i :: current_proj) f)
              |> Seq.concat
          | Structural (Array v) ->
              let total_size = List.length v in
              let proj i = Projections.Index (Expr.int i, ty, total_size) in
              List.to_seq v
              |> Seq.mapi (fun i f ->
                     aux ~current_proj:(proj i :: current_proj) f)
              |> Seq.concat
          | Structural (Enum _) ->
              failwith
                "Trying to derive assertion for incomplete enum: to implement!"
          | _ -> Fmt.failwith "unreachable: %a to assertion" pp block)
    in
    aux ~current_proj:[] block

  let outer_assertions ~loc block =
    assertions ~loc ~base_offset:(Some block.offset) block.root

  let uninitialized ~tyenv:_ ty = { ty; content = Structural Uninit }

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
    let content = Structural (Fields content) in
    { ty; content }

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
        let content = Structural (Enum { discr = vidx; fields }) in
        { ty; content }
    | _ ->
        Fmt.failwith "Invalid enum value for type %a: %a" Ty.pp ty
          (Fmt.list Expr.pp) data

  and of_rust_value ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    match (ty, e) with
    | (Ty.Scalar _ | Ptr _ | Ref _), e ->
        Logging.tmi (fun m -> m "valid: %a for %a" Expr.pp e Ty.pp ty);
        if%sat TypePreds.valid ty e then
          DR.ok { ty; content = Structural (Symbolic e) }
        else DR.error (Err.Invalid_value (ty, e))
    | Tuple _, Lit (LList data) ->
        let content = List.map lift_lit data in
        of_rust_value ~tyenv ~ty (EList content)
    | Tuple ts, EList tup ->
        let++ content =
          DR_list.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) ts tup
        in
        let content = Structural (Fields content) in
        { ty; content }
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
      when List.compare_length_with l (Z.to_int length) == 0 ->
        let++ mem_array = DR_list.map (of_rust_value ~tyenv ~ty:ty') l in
        { ty; content = Structural (Array mem_array) }
    | _, s -> DR.ok { ty; content = Structural (Symbolic s) }

  let of_rust_maybe_uninit ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    let* maybe_value = Symb_opt.of_expr e in
    match maybe_value with
    | None -> DR.ok (uninitialized ~tyenv ty)
    | Some value -> of_rust_value ~tyenv ~ty value
    | Symb e -> DR.ok { content = Structural (SymbolicMaybeUninit e); ty }

  let of_rust_many_maybe_uninit ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    let* e = Delayed.reduce e in
    match (e, ty) with
    | Expr.EList l, Ty.Array { ty; _ } ->
        let++ elements = DR_list.map (of_rust_maybe_uninit ~tyenv ~ty) l in
        { content = Structural (Array elements); ty }
    | _ -> DR.ok { content = Structural (ManySymbolicMaybeUninit e); ty }

  let outer_missing ~offset ~tyenv:_ ty =
    let root = { ty; content = Structural Missing } in
    { offset; root }

  let outer_symbolic ~offset ~tyenv:_ ty e =
    let root = { ty; content = Structural (Symbolic e) } in
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
              (fun ty e -> { content = Structural (Symbolic e); ty })
              v values
          in
          DR.ok { ty; content = Structural (Fields fields) }
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
              (fun e -> { content = Structural (Symbolic e); ty = ty' })
              values
          in
          DR.ok { ty; content = Structural (Array fields) }
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
                    {
                      content = Structural (Symbolic e);
                      ty = Ty.subst_params ~subst ty;
                    })
                  fields values
              in
              DR.ok { ty; content = Structural (Fields fields) }
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
                    {
                      content = Structural (Symbolic e);
                      ty = Ty.subst_params ~subst ty;
                    })
                  (snd variant) values
              in
              DR.ok
                {
                  ty;
                  content = Structural (Enum { discr = variant_idx; fields });
                }
            else too_symbolic expr)
    | Scalar _ | Ref _ | Ptr _ ->
        failwith
          "I shouldn't ever need to concretize a scalar or something opaque"
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"
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
        {
          ty;
          content =
            Structural
              (Array (List.init (Z.to_int length_i) (fun _ -> missing_child)));
        }
    | Array _ -> failwith "structural_mising arrays: implement"
    | Tuple fields ->
        {
          ty;
          content = Structural (Fields (List.map (fun ty -> missing ty) fields));
        }
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
            { ty; content = Structural (Fields missing_fields) }
        | Enum _ as def ->
            Fmt.failwith "Unhandled: structural missing for Enum %a"
              Common.Ty.Adt_def.pp def)
    | Scalar _ | Ref _ | Ptr _ | Unresolved _ | Slice _ ->
        Fmt.failwith "structural missing called on a leaf or unsized: %a" Ty.pp
          ty

  let cast_array
      ~lk
      ~from:(ty_from, length_from)
      ~to_:(ty_to, length_to)
      content =
    let open Formula.Infix in
    match content with
    | Structural Uninit | Structural Missing ->
        let* size_from, lk = Layout_knowledge.size_of ~lk ty_from in
        let* size_to, lk = Layout_knowledge.size_of ~lk ty_to in
        let new_length = Expr.Infix.(length_from * size_from / size_to) in
        if%ent new_length #== length_to then Delayed.return (content, lk)
        else failwith "Not implement: sub-sym-array of uninit after cast"
    | _ ->
        Fmt.failwith
          "Cannot convert anything else than missing or uninit. Tried to \
           convert from [%a;%a] to [%a;%a] : %a"
          Ty.pp ty_from Expr.pp length_from Ty.pp ty_to Expr.pp length_to
          pp_content content

  (* Extract range from a given structural node.
     The range is given in the index type, is relative to the current structure.
     It must be the case that the range is STRICTLY contained in the current structure, i.e.
     [range.length * size_of::<index_ty>() < size_of::<node_ty>()]
  *)
  let extract_range_structural ~lk ~index_ty ~range ~node_ty structural =
    let* end_as_index, lk =
      Layout_knowledge.length_as_array_of ~lk ~of_ty:index_ty node_ty
    in
    match structural with
    | Fields _ | Enum _ ->
        Fmt.failwith
          "Cannot split fields or enum: don't know their layouts, probably a \
           bug in the verified program. (or an unsupported usage of #[repr] on \
           enum)"
    | Array l -> (
        let values_ty =
          match node_ty with
          | Ty.Array { ty; _ } -> ty
          | _ -> failwith "Malformed: Array doesn't have array type?"
        in
        let* range_v, lk =
          Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:values_ty range
        in
        match range_v with
        | Expr.Lit (Int start), Expr.Lit (Int end_) -> (
            let range_v = Z.(to_int start, to_int end_) in
            match List_utils.extract_range ~range:range_v l with
            | `Left (left, right) ->
                let left_child =
                  ( {
                      structural = Some (Array left);
                      range = (Expr.zero_i, snd range);
                      children = None;
                    },
                    Ty.array values_ty (Expr.int (snd range_v)) )
                in
                let right_child =
                  ( {
                      structural = Some (Array right);
                      range = (snd range, end_as_index);
                      children = None;
                    },
                    Ty.array values_ty (Expr.int (List.length right)) )
                in
                let lc =
                  {
                    structural = Some structural;
                    children = Some [ left_child; right_child ];
                    range = (Expr.zero_i, end_as_index);
                  }
                in
                let node =
                  { content = Layed_out_root (lc, index_ty); ty = node_ty }
                in
                Delayed.return (node, lk)
            | `Right (left, right) ->
                let left_child =
                  ( {
                      structural = Some (Array left);
                      range = (Expr.zero_i, fst range);
                      children = None;
                    },
                    Ty.array values_ty (Expr.int (fst range_v)) )
                in
                let right_child =
                  ( {
                      structural = Some (Array right);
                      range = (fst range, snd range);
                      children = None;
                    },
                    Ty.array values_ty (Expr.int (List.length right)) )
                in
                let lc =
                  {
                    structural = Some structural;
                    children = Some [ left_child; right_child ];
                    range = (Expr.zero_i, end_as_index);
                  }
                in
                let node =
                  { content = Layed_out_root (lc, index_ty); ty = node_ty }
                in
                Delayed.return (node, lk)
            | `Three (left, mid, right) ->
                let left_child =
                  ( {
                      structural = Some (Array left);
                      range = (Expr.zero_i, fst range);
                      children = None;
                    },
                    Ty.array values_ty (Expr.int (fst range_v)) )
                in
                let middle_child =
                  ( { structural = Some (Array mid); range; children = None },
                    Ty.array values_ty (Expr.int (snd range_v - fst range_v)) )
                in
                let right_child =
                  ( {
                      structural = Some (Array right);
                      range = (snd range, end_as_index);
                      children = None;
                    },
                    Ty.array values_ty (Expr.int (List.length right)) )
                in
                let lc =
                  {
                    structural = Some structural;
                    children = Some [ left_child; middle_child; right_child ];
                    range = (Expr.zero_i, end_as_index);
                  }
                in
                let node =
                  { content = Layed_out_root (lc, index_ty); ty = node_ty }
                in
                Delayed.return (node, lk))
        | _range ->
            Fmt.failwith
              "to implement: extracting a symbolic length from a concrete array"
        )
    | Uninit | Missing ->
        if%sat Formula.Infix.((fst range) #== Expr.zero_i) then
          let left_child =
            ( {
                structural = Some structural;
                range = (Expr.zero_i, snd range);
                children = None;
              },
              Ty.array index_ty (snd range) )
          in
          let right_child =
            ( {
                structural = Some structural;
                range = (snd range, end_as_index);
                children = None;
              },
              Ty.array index_ty Expr.Infix.(end_as_index - snd range) )
          in
          let lc =
            {
              structural = Some structural;
              range = (Expr.zero_i, end_as_index);
              children = Some [ left_child; right_child ];
            }
          in
          let node =
            { content = Layed_out_root (lc, index_ty); ty = node_ty }
          in
          Delayed.return (node, lk)
        else
          if%sat Formula.Infix.((snd range) #== end_as_index) then
            let left_child =
              ( {
                  structural = Some structural;
                  range = (Expr.zero_i, fst range);
                  children = None;
                },
                Ty.array index_ty (fst range) )
            in
            let right_child =
              ( { structural = Some structural; range; children = None },
                Ty.array index_ty Expr.Infix.(end_as_index - fst range) )
            in
            let lc =
              {
                structural = Some structural;
                range = (Expr.zero_i, end_as_index);
                children = Some [ left_child; right_child ];
              }
            in
            let node =
              { content = Layed_out_root (lc, index_ty); ty = node_ty }
            in
            Delayed.return (node, lk)
          else
            let left_child =
              ( {
                  structural = Some structural;
                  range = (Expr.zero_i, fst range);
                  children = None;
                },
                Ty.array index_ty (fst range) )
            in
            let mid_child =
              ( { structural = Some structural; range; children = None },
                Ty.array index_ty Expr.Infix.(snd range - fst range) )
            in
            let right_child =
              ( {
                  structural = Some structural;
                  range = (snd range, end_as_index);
                  children = None;
                },
                Ty.array index_ty Expr.Infix.(end_as_index - snd range) )
            in
            let lc =
              {
                structural = Some structural;
                range = (Expr.zero_i, end_as_index);
                children = Some [ left_child; mid_child; right_child ];
              }
            in
            let node =
              { content = Layed_out_root (lc, index_ty); ty = node_ty }
            in
            Delayed.return (node, lk)
    | structural ->
        Fmt.failwith "Not implemented yet: extracting range from structural %a"
          pp_structural structural

  let as_layed_out_child ~lk ~range ~index_ty t =
    match t.content with
    | Layed_out_root (root', index_ty') ->
        let+ root, lk =
          reinterpret_lc_ranges ~lk ~from_ty:index_ty' ~to_ty:index_ty root'
        in
        let child = offset_layed_out ~by:(fst range) root in
        ((child, t.ty), lk)
    | Structural structural ->
        Delayed.return
          (({ structural = Some structural; range; children = None }, t.ty), lk)

  let rec extract_layed_out_and_apply
      ~lk
      ~return_and_update
      ~range
      ~index_ty
      ~node_ty
      lc =
    Logging.tmi (fun m -> m "Inside extract_layed_out_and_apply");
    Logging.tmi (fun m ->
        m "Range we're looking for: %a, range we're in: %a" Range.pp range
          Range.pp lc.range);
    if%sat Range.is_equal range lc.range then
      let () = Logging.tmi (fun m -> m "Range is equal") in
      let offset = fst range in
      (* we retrun a relative lc *)
      let this_tree =
        let lc_absolute = offset_layed_out ~by:Expr.Infix.(~-offset) lc in
        { content = Layed_out_root (lc_absolute, index_ty); ty = node_ty }
        |> lossless_flatten
      in
      let** value, new_tree = return_and_update this_tree in
      let+ lc, lk = as_layed_out_child ~lk ~range:lc.range ~index_ty new_tree in
      Ok (value, lc, lk)
    else
      match (lc.structural, lc.children) with
      | Some structural, None ->
          let () =
            Logging.tmi (fun m ->
                m "Leaf!!! Structural = %a" pp_structural structural)
          in

          (* leaf, we try splitting further *)
          let* new_node, lk =
            extract_range_structural ~lk ~index_ty ~range ~node_ty structural
          in
          Logging.tmi (fun m -> m "NEW NODE: %a" pp new_node);
          let** value, new_tree, lk =
            extract_and_apply ~lk ~return_and_update ~range ~index_ty new_node
          in
          let+ lc, lk =
            as_layed_out_child ~lk ~range:lc.range ~index_ty new_tree
          in
          Ok (value, lc, lk)
      | _, Some children ->
          let () =
            Logging.verbose (fun m -> m "Children: %d!!" (List.length children))
          in

          let rec aux ~lk passed children =
            match children with
            | [] ->
                failwith
                  "Not included in any child! Need some kind of regrouping"
            | (child, child_ty) :: rest ->
                if%sat Range.is_inside range child.range then
                  let++ value, child, lk =
                    extract_layed_out_and_apply ~lk ~return_and_update ~range
                      ~index_ty ~node_ty:child_ty child
                  in
                  (value, List.rev_append passed (child :: rest), lk)
                else aux ~lk ((child, child_ty) :: passed) rest
          in
          let++ value, children, lk = aux ~lk [] children in
          ( value,
            ( { structural = None; children = Some children; range = lc.range },
              node_ty ),
            lk )
      | _ -> failwith "Malformed: lazy without children"

  (* This applies [return_and_update] on the range given index by [index_ty] *)
  and extract_and_apply ~lk ~return_and_update ~range ~index_ty t =
    match t.content with
    | Structural s ->
        let* new_node, lk =
          extract_range_structural ~lk ~index_ty ~range ~node_ty:t.ty s
        in
        extract_and_apply ~lk ~return_and_update ~range ~index_ty new_node
    | Layed_out_root (lc, index_ty') ->
        let* range', lk =
          Range.reinterpret ~lk ~from_ty:index_ty ~to_ty:index_ty' range
        in
        let++ value, (lc, ty), lk =
          extract_layed_out_and_apply ~lk ~return_and_update ~range:range'
            ~index_ty:index_ty' ~node_ty:t.ty lc
        in
        let new_tree =
          { content = Layed_out_root (lc, index_ty'); ty } |> lossless_flatten
        in
        (value, new_tree, lk)

  let rec find_slice
      ~tyenv
      ~lk
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
          let* eq, lk =
            Layout_knowledge.size_equal ~lk t.ty (Ty.array ty size)
          in
          if%ent Formula.Infix.(eq #&& (current_offset #== Expr.zero_i)) then
            let++ value, new_slice = return_and_update t in
            (value, new_slice, lk)
          else
            let* less, lk =
              Layout_knowledge.compare_sizes ~lk Formula.Infix.( #< )
                (Ty.array ty size) t.ty
            in

            if%ent less then
              extract_and_apply ~lk ~return_and_update
                ~range:(current_offset, Expr.Infix.(current_offset + size))
                ~index_ty:ty t
            else
              Fmt.failwith
                "Complex transmutation: a slice which captures several fields \
                 of a structure possibly. Will implement by need."
        else
          Fmt.failwith "negative offset in array in find_slice : %a" Expr.pp
            current_offset
    | Plus (_, ofs, ofs_ty) :: rest ->
        let* ofs, lk =
          Layout_knowledge.reinterpret_offset ~lk ~from_ty:ofs_ty ~to_ty:ty ofs
        in
        find_slice ~tyenv ~lk ~return_and_update ~ty
          ~current_offset:Expr.Infix.(current_offset + ofs)
          t rest size
    | _ ->
        Fmt.failwith
          "Unimplemented case for find_slice: path: %a, t: ==%a==, \
           expected_ty: %a, size: %a"
          Projections.pp_path path pp t Ty.pp ty Expr.pp size

  let find_path ~tyenv ~lk ~return_and_update ~ty:expected_ty t path :
      ('a * t * Layout_knowledge.t, Err.t) DR.t =
    match expected_ty with
    | Ty.Array { length; ty } ->
        (* This should be done way later actually, after properly resolving the other projs *)
        find_slice ~tyenv ~lk ~return_and_update ~ty t path length
    | _ ->
        let rec aux t (path : Projections.path) =
          match (path, t.content, t.ty) with
          | [], _, _ ->
              let* eq, lk = Layout_knowledge.size_equal ~lk t.ty expected_ty in
              if%ent eq then
                let++ value, block = return_and_update t in
                (value, block, lk)
              else
                failwith
                  "Not implemented: find_path division. It should be a very \
                   rare case though."
          | Field (i, ty) :: rest, Structural (Fields vec), ty'
            when Ty.equal ty ty' ->
              let e = Result.ok_or vec.%[i] ~msg:"Index out of bounds" in
              let** v, sub_block, lk = aux e rest in
              let++ new_fields = Delayed.return (vec.%[i] <- sub_block) in
              (v, { ty; content = Structural (Fields new_fields) }, lk)
          | ( VField (i, ty, vidx) :: rest,
              Structural (Enum { discr; fields }),
              ty' )
            when Ty.equal ty ty' && discr == vidx ->
              let e = Result.ok_or fields.%[i] ~msg:"Index out of bounds" in
              let** v, sub_block, lk = aux e rest in
              let++ new_fields = Delayed.return (fields.%[i] <- sub_block) in
              ( v,
                {
                  ty;
                  content = Structural (Enum { discr; fields = new_fields });
                },
                lk )
          | (op :: _ as path), Structural (Symbolic s), ty ->
              let variant = Projections.variant op in
              let** this_block = semi_concretize ~tyenv ~variant ty s in
              aux this_block path
          | _ :: _, Structural Missing, ty ->
              Logging.tmi (fun m ->
                  m "Structural missing: %a"
                    (Fmt.Dump.list Projections.pp_op)
                    path);
              let this_block = structural_missing ~tyenv ty in
              aux this_block path
          | _ ->
              Fmt.failwith "Couldn't resolve path: (content: %a, path: %a)"
                pp_content t.content
                (Fmt.Dump.list Projections.pp_op)
                path
        in
        aux t path

  let find_slice_outer
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
    let++ ret, root, lk =
      find_slice ~ty ~lk ~tyenv ~return_and_update t path size
    in
    (ret, { outer with root }, lk)

  let find_proj
      ~tyenv
      ~lk
      ~return_and_update
      ~ty
      (outer : outer)
      (proj : Projections.t) =
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
    let++ ret, root, lk = find_path ~tyenv ~lk ~return_and_update ~ty t path in
    (ret, { outer with root }, lk)

  let copy_nonoverlapping
      ~tyenv
      ~lk
      from_block
      from_proj
      to_block
      to_proj
      ty
      size =
    Logging.verbose (fun m ->
        m "copy_nonoverlapping: about to load copy from the 'from' block");
    let** copy, _, lk =
      find_slice_outer ~tyenv ~lk
        ~return_and_update:(fun t -> DR.ok (t, t))
        ~ty from_block from_proj size
    in
    Logging.verbose (fun m ->
        m "copy_nonoverlapping: about to write copy to the 'to' block");
    let return_and_update _t = DR.ok ((), copy) in
    let++ (), mem, lk =
      find_slice_outer ~tyenv ~return_and_update ~ty ~lk to_block to_proj size
    in
    (mem, lk)

  let load_proj ~loc ~tyenv t proj ty copy =
    let update block = if copy then block else uninitialized ~tyenv ty in
    let return_and_update t =
      let++ value =
        let result = to_rust_value ~ty t in
        DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
      in
      (value, update t)
    in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let cons_proj ~loc ~tyenv t proj ty =
    let return_and_update t =
      let++ value =
        let result = to_rust_value ~ty t in
        DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
      in
      (value, missing t.ty)
    in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let prod_proj ~tyenv ~lk t proj ty value =
    let* new_block =
      let return_and_update block =
        match missing_qty block with
        | Some Totally ->
            let++ value = of_rust_value ~tyenv ~ty value in
            ((), value)
        | _ -> Delayed.vanish ()
        (* Duplicated resources *)
      in
      let++ _, new_block, lk =
        find_proj ~tyenv ~lk ~ty ~return_and_update t proj
      in
      (new_block, lk)
    in
    match new_block with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let cons_uninit ~loc:_ ~tyenv t proj ty =
    let return_and_update t =
      let error () =
        Fmt.kstr (fun s -> DR.error (Err.LogicError s)) "Not uninit: %a" pp t
      in
      match t.content with
      | Structural Uninit -> DR.ok ((), missing t.ty)
      | Structural (SymbolicMaybeUninit s) ->
          if%ent Symb_opt.is_none s then DR.ok ((), missing t.ty) else error ()
      | Structural (ManySymbolicMaybeUninit s) ->
          if%ent Symb_opt.is_all_none s then DR.ok ((), missing t.ty)
          else error ()
      | _ -> error ()
    in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let prod_uninit ~loc:_ ~lk ~tyenv t proj ty =
    let* result =
      let return_and_update block =
        match missing_qty block with
        | Some Totally ->
            let value = uninitialized ~tyenv ty in
            DR.ok ((), value)
        | _ -> Delayed.vanish ()
        (* Duplicated resource *)
      in
      let++ _, new_block, lk =
        find_proj ~tyenv ~lk ~ty ~return_and_update t proj
      in
      (new_block, lk)
    in
    match result with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let cons_maybe_uninit ~loc ~lk ~tyenv t proj ty =
    let return_and_update t =
      match missing_qty t with
      | Some qty -> DR.error (Err.Missing_proj (loc, proj, qty))
      | None -> (
          match t.content with
          | Structural Uninit ->
              let result = Symb_opt.to_expr None in
              DR.ok (result, missing t.ty)
          | Structural (SymbolicMaybeUninit s) when Ty.equal ty t.ty ->
              DR.ok (s, missing t.ty)
          | Structural (ManySymbolicMaybeUninit s)
            when Ty.is_array_of ~array_ty:t.ty ~inner_ty:ty ->
              DR.ok (Expr.list_nth s 0, missing t.ty)
          | _ ->
              let++ v =
                let result = to_rust_value ~ty t in
                DR.map_error result (Err.Conversion_error.lift ~loc ~proj)
              in
              (Symb_opt.some v, missing t.ty))
    in
    find_proj ~tyenv ~lk ~return_and_update ~ty t proj

  let prod_maybe_uninit ~loc:_ ~lk ~tyenv t proj ty maybe_value =
    let* result =
      let return_and_update block =
        match missing_qty block with
        | Some Totally -> (
            let* maybe_value = Symb_opt.of_expr maybe_value in
            match maybe_value with
            | None ->
                let value = uninitialized ~tyenv ty in
                DR.ok ((), value)
            | Some value ->
                let++ value = of_rust_value ~tyenv ~ty value in
                ((), value)
            | Symb e ->
                DR.ok ((), { content = Structural (SymbolicMaybeUninit e); ty })
            )
        | _ -> Delayed.vanish ()
        (* Duplicated resource *)
      in
      let++ _, new_block, lk =
        find_proj ~tyenv ~lk ~ty ~return_and_update t proj
      in
      (new_block, lk)
    in
    match result with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let cons_many_maybe_uninits ~loc ~tyenv ~lk t proj ty size =
    let return_and_update t =
      match missing_qty t with
      | Some qty -> DR.error (Missing_proj (loc, proj, qty))
      | None ->
          let++ value = to_rust_many_maybe_uninits ~ty ~size t in
          (value, missing t.ty)
    in
    find_slice_outer ~tyenv ~lk ~ty ~return_and_update t proj size

  let prod_many_maybe_uninits ~loc:_ ~tyenv ~lk t proj ty size maybe_values =
    let* result =
      let return_and_update t =
        match missing_qty t with
        | Some Totally ->
            let content = Structural (ManySymbolicMaybeUninit maybe_values) in
            let ty = Ty.array ty size in
            DR.ok ((), { ty; content })
        | _ -> Delayed.vanish ()
      in
      let++ _, new_block, lk =
        find_slice_outer ~tyenv ~lk ~ty ~return_and_update t proj size
      in
      (new_block, lk)
    in
    match result with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let store_proj ~loc ~tyenv ~lk t proj ty value =
    let return_and_update block =
      match missing_qty block with
      | Some qty -> DR.error (Err.Missing_proj (loc, proj, qty))
      | None ->
          let++ value = of_rust_value ~tyenv ~ty value in
          ((), value)
    in
    let++ _, new_block, lk =
      find_proj ~tyenv ~lk ~ty ~return_and_update t proj
    in
    (new_block, lk)

  let get_discr ~tyenv ~lk t proj enum_typ =
    let return_and_update block =
      let** () =
        if Ty.equal block.ty enum_typ then DR.ok ()
        else DR.error (Invalid_type (block.ty, enum_typ))
      in
      match block.content with
      | Structural (Enum t) -> DR.ok (Expr.int t.discr, block)
      | Structural (Symbolic expr) ->
          let open Formula.Infix in
          if%sat
            (Expr.typeof expr) #== (Expr.type_ ListType)
            #&& ((Expr.list_length expr) #== (Expr.int 2))
          then DR.ok (Expr.list_nth expr 0, block)
          else too_symbolic expr
      | _ -> DR.error (Invalid_type (block.ty, enum_typ))
    in
    let++ discr, _, lk =
      find_proj ~tyenv ~lk ~return_and_update ~ty:enum_typ t proj
    in
    (discr, lk)

  let deinit ~tyenv ~lk t proj ty =
    let return_and_update _block = DR.ok ((), uninitialized ~tyenv ty) in
    let++ _, new_block, lk =
      find_proj ~tyenv ~lk ~ty ~return_and_update t proj
    in
    (new_block, lk)

  let rec equality_constraints t1 t2 =
    (* Using to_rust_value_exn is over-approximate, but this is only used in the context of prophecies,
       which may never be uninit.
       At some point, I should probably rework prophecies to just be values and not trees anyway 🤷‍♂️ *)
    let ( #== ) = Formula.Infix.( #== ) in
    match (t1.content, t2.content) with
    | Structural Missing, _ | _, Structural Missing -> []
    | Structural (Symbolic e1), Structural (Symbolic e2) -> [ e1 #== e2 ]
    | Structural (Fields f1), Structural (Fields f2) ->
        List_utils.concat_map_2 equality_constraints f1 f2
    | Structural (Array f1), Structural (Array f2) ->
        List_utils.concat_map_2 equality_constraints f1 f2
    | Structural (Enum _), Structural (Enum _) ->
        let to_value = to_rust_value_exn in
        (* Sub parts of enum cannot be missing *)
        [ (to_value t1) #== (to_value t2) ]
    | Structural (Symbolic e), content | content, Structural (Symbolic e) ->
        let content = to_rust_value_exn { ty = t1.ty; content } in
        [ content #== e ]
    | _ -> Fmt.failwith "cannot learn equality of %a and %a" pp t1 pp t2

  let substitution ~tyenv ~subst_expr t =
    let get_structural { content; _ } =
      match content with
      | Structural s -> s
      | _ -> raise (Invalid_argument "get_structural")
    in
    let rec substitute_structural ~ty t =
      match t with
      | Symbolic e ->
          let new_e = subst_expr e in
          if Expr.equal new_e e then DR.ok t
          else
            let++ new_tree = of_rust_value ~tyenv ~ty new_e in
            get_structural new_tree
      | SymbolicMaybeUninit e ->
          let new_e = subst_expr e in
          if Expr.equal new_e e then DR.ok t
          else
            let++ new_tree = of_rust_maybe_uninit ~tyenv ~ty new_e in
            get_structural new_tree
      | ManySymbolicMaybeUninit e ->
          let new_e = subst_expr e in
          if Expr.equal new_e e then DR.ok t
          else
            let++ new_tree = of_rust_many_maybe_uninit ~tyenv ~ty new_e in
            get_structural new_tree
      | Array lst ->
          let++ lst = DR_list.map substitution lst in
          Array lst
      | Fields lst ->
          let++ lst = DR_list.map substitution lst in
          Fields lst
      | Enum { fields; discr } ->
          let++ fields = DR_list.map substitution fields in
          Enum { fields; discr }
      | Uninit | Missing -> DR.ok t
    and substitute_layed_out ~ty { structural; children; range } =
      let range = Range.substitute ~subst_expr range in
      let** structural =
        match structural with
        | None -> DR.ok None
        | Some s ->
            let++ s = substitute_structural ~ty s in
            Some s
      in
      let++ children =
        match children with
        | Some children ->
            let++ children =
              DR_list.map
                (fun (l, ty) ->
                  let ty = Ty.substitution ~subst_expr ty in
                  let++ l = substitute_layed_out ~ty l in
                  (l, ty))
                children
            in
            Some children
        | None -> DR.ok None
      in
      { structural; children; range }
    and substitution { content; ty } =
      let ty = Ty.substitution ~subst_expr ty in
      match content with
      | Structural s ->
          let++ s = substitute_structural ~ty s in
          { ty; content = Structural s }
      | Layed_out_root (lc, index_ty) ->
          let index_ty = Ty.substitution ~subst_expr index_ty in
          let++ lc = substitute_layed_out ~ty lc in
          let content = Layed_out_root (lc, index_ty) in
          { content; ty }
    in
    substitution t

  let outer_substitution ~tyenv ~subst_expr t =
    let** root = substitution ~tyenv ~subst_expr t.root in
    let+ offset = Delayed.reduce (subst_expr t.offset) in
    Ok { offset; root }

  let outer_equality_constraint (o1 : outer) (o2 : outer) =
    if not (Expr.equal o1.offset o2.offset) then
      failwith "Cannot learn equality of two blocks of different offsets";
    if not (Ty.equal o1.root.ty o2.root.ty) then
      failwith "Cannot learn equality of two blocks of different types";
    equality_constraints o1.root o2.root

  let merge_outer (o1 : outer) (o2 : outer) =
    let+ () =
      let eq = Formula.Infix.( #== ) o1.offset o2.offset in
      if%ent eq then Delayed.return ()
      else
        failwith "Not handled yet: merging outer blocks with different offsets"
    in
    match (o1.root, o2.root) with
    | { content = Structural Missing; _ }, _ -> o2
    | _, { content = Structural Missing; _ } -> o1
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
  Logging.tmi (fun m -> m "Found block: %s" loc);
  let** block = find_not_freed loc mem in
  let++ v, new_block, lk =
    TreeBlock.load_proj ~loc ~tyenv ~lk block proj ty copy
  in
  let new_mem = MemMap.add loc (T new_block) mem in
  (v, new_mem, lk)

let store ~tyenv ~lk (mem : t) loc proj ty value =
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
  let** block = find_not_freed loc mem in
  let++ value, outer, lk = TreeBlock.cons_proj ~loc ~tyenv ~lk block proj ty in
  (value, MemMap.add loc (T outer) mem, lk)

let prod_value ~tyenv ~lk (mem : t) loc (proj : Projections.t) ty value =
  let root =
    match MemMap.find_opt loc mem with
    | Some (T root) -> root
    | Some Freed -> failwith "use after free"
    | None ->
        TreeBlock.outer_missing
          ~offset:(Option.value ~default:(Expr.EList []) proj.base)
          ~tyenv
          (Projections.base_ty ~leaf_ty:ty proj)
  in
  let+ new_block, lk = TreeBlock.prod_proj ~tyenv ~lk root proj ty value in
  (MemMap.add loc (T new_block) mem, lk)

let cons_uninit ~tyenv ~lk (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ (), outer, lk = TreeBlock.cons_uninit ~loc ~tyenv ~lk block proj ty in
  (MemMap.add loc (T outer) mem, lk)

let prod_uninit ~tyenv ~lk (mem : t) loc (proj : Projections.t) ty =
  let root =
    match MemMap.find_opt loc mem with
    | Some (T root) -> root
    | Some Freed -> failwith "use after free"
    | None ->
        TreeBlock.outer_missing
          ~offset:(Option.value ~default:(Expr.EList []) proj.base)
          ~tyenv
          (Projections.base_ty ~leaf_ty:ty proj)
  in
  let+ new_block, lk = TreeBlock.prod_uninit ~loc ~tyenv ~lk root proj ty in
  (MemMap.add loc (T new_block) mem, lk)

let cons_maybe_uninit ~tyenv ~lk (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ value, outer, lk =
    TreeBlock.cons_maybe_uninit ~loc ~tyenv ~lk block proj ty
  in
  (value, MemMap.add loc (T outer) mem, lk)

let prod_maybe_uninit
    ~tyenv
    ~lk
    (mem : t)
    loc
    (proj : Projections.t)
    ty
    maybe_value =
  let root =
    match MemMap.find_opt loc mem with
    | Some (T root) -> root
    | Some Freed -> failwith "use after free"
    | None ->
        TreeBlock.outer_missing
          ~offset:(Option.value ~default:(Expr.EList []) proj.base)
          ~tyenv
          (Projections.base_ty ~leaf_ty:ty proj)
  in
  let+ new_block, lk =
    TreeBlock.prod_maybe_uninit ~loc ~tyenv ~lk root proj ty maybe_value
  in
  (MemMap.add loc (T new_block) mem, lk)

let cons_many_maybe_uninits ~tyenv ~lk (mem : t) loc proj ty size =
  if%sat Formula.Infix.(size #== Expr.zero_i) then DR.ok (Expr.EList [], mem, lk)
  else
    let** block = find_not_freed loc mem in
    let++ value, outer, lk =
      TreeBlock.cons_many_maybe_uninits ~loc ~tyenv ~lk block proj ty size
    in
    (value, MemMap.add loc (T outer) mem, lk)

let prod_many_maybe_uninits
    ~tyenv
    ~lk
    (mem : t)
    loc
    (proj : Projections.t)
    ty
    size
    maybe_values =
  if%sat Formula.Infix.(size #== Expr.zero_i) then Delayed.return (mem, lk)
  else
    let root =
      match MemMap.find_opt loc mem with
      | Some (T root) -> root
      | Some Freed -> failwith "use after free"
      | None ->
          TreeBlock.outer_missing
            ~offset:(Option.value ~default:(Expr.EList []) proj.base)
            ~tyenv
            (Projections.base_ty ~leaf_ty:(Ty.array ty size) proj)
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
  if Ty.equal block.root.ty ty then DR.ok (MemMap.add loc Freed mem, lk)
  else
    let* size_left, lk = Layout_knowledge.size_of ~lk block.root.ty in
    let* size_right, lk = Layout_knowledge.size_of ~lk ty in
    if%ent Formula.Infix.(size_left #== size_right) then
      DR.ok (MemMap.add loc Freed mem, lk)
    else DR.error (Invalid_type (ty, block.root.ty))
(* else Fmt.failwith "Not freeable!" *)

let load_discr ~tyenv ~lk (mem : t) loc proj enum_typ =
  let** block = find_not_freed loc mem in
  TreeBlock.get_discr ~tyenv ~lk block proj enum_typ

let assertions ~tyenv:_ (mem : t) =
  let value (loc, block) =
    let loc = Expr.loc_from_loc_name loc in
    match block with
    | T block -> TreeBlock.outer_assertions ~loc block
    | Freed ->
        let cp = Actions.cp_to_name Freed in
        Seq.return (Asrt.GA (cp, [ loc ], []))
  in
  MemMap.to_seq mem |> Seq.flat_map value |> List.of_seq

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

let substitution ~tyenv heap subst =
  let open Gillian.Symbolic in
  if Subst.is_empty subst then DR.ok heap
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
    let++ new_mapping =
      MemMap.to_seq heap |> List.of_seq
      |> DR_list.map (fun (loc, block) ->
             let++ block =
               match block with
               | Freed -> DR.ok Freed
               | T block ->
                   let++ block =
                     TreeBlock.outer_substitution ~tyenv ~subst_expr block
                   in
                   T block
             in
             (loc, block))
    in
    let tree_substed = List.to_seq new_mapping |> MemMap.of_seq in
    List.fold_left
      (fun acc (old_loc, new_loc) ->
        Logging.verbose (fun m ->
            m "About to merge locs: %s -> %a" old_loc Expr.pp new_loc);
        let new_loc =
          match new_loc with
          | Lit (Loc loc) | ALoc loc -> loc
          | _ ->
              Fmt.failwith
                "substitution failed, for location, target isn't a location"
        in
        match (MemMap.find_opt old_loc acc, MemMap.find_opt new_loc acc) with
        | None, None | None, Some _ -> acc
        | Some tree, None ->
            MemMap.remove old_loc acc |> MemMap.add new_loc tree
        | Some tree_left, Some tree_right ->
            Fmt.failwith "Can't merge trees yet @\nLEFT: %a@\nRIGHT:%a" pp_block
              tree_left pp_block tree_right)
      tree_substed loc_subst
