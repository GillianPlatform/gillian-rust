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

(* We let the monadic abstraction leak to avoid rewriting
   the entirety of the Partial_layout engine *)
(* let resolve_address ~tyenv ~context address =
   let+ pc = Delayed.leak_pc_copy () in
   Partial_layout.resolve_address_debug_access_error ~pc ~tyenv ~context address
   |> List.rev *)

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

let too_symbolic e =
  Delayed.map (Delayed.reduce e) (fun e -> Error (Too_symbolic e))

let not_concrete msgf = Fmt.kstr (fun s -> raise (NotConcrete s)) msgf

let rec lift_lit = function
  | Literal.LList l -> Expr.EList (List.map lift_lit l)
  | x -> Lit x

let rec concretize_expr expr =
  match expr with
  | Expr.Lit lit -> lit
  | EList l -> LList (List.map concretize_expr l)
  | BinOp (((EList _ | Lit (LList _)) as l), LstNth, Lit (Int i)) ->
      let i = Z.to_int i in
      concretize_expr (Expr.list_nth l i)
  | _ -> not_concrete "concretize: %a" Expr.pp expr

let concretize_proj expr =
  let lit_list =
    match concretize_expr expr with
    | LList l -> l
    | _ -> not_concrete "concretize_proj, not a list: %a" Expr.pp expr
  in
  Projections.of_lit_list lit_list

let concretiz_proj_opt e =
  try Some (concretize_proj e) with NotConcrete _ -> None

exception MemoryError of string

let mem_error p = Fmt.kstr (fun s -> raise (MemoryError s)) p

module TreeBlock = struct
  type t = { ty : Ty.t; content : tree_content }

  and tree_content =
    | Symbolic of Expr.t
    | Leaf of Expr.t
    | Fields of t list
    | Array of t list
    | Enum of { discr : int; fields : t list }
    | Uninit
    | Missing

  type outer = { offset : Expr.t; root : t }

  let rec lvars t =
    let open Utils.Containers in
    SS.union (Ty.lvars t.ty)
    @@
    match t.content with
    | Uninit | Missing -> SS.empty
    | Symbolic e | Leaf e -> Expr.lvars e
    | Fields l | Array l | Enum { fields = l; _ } ->
        List.fold_left (fun acc t -> SS.union acc (lvars t)) SS.empty l

  let outer_lvars outer =
    let open Utils.Containers in
    SS.union (lvars outer.root) (Expr.lvars outer.offset)

  let rec is_empty block =
    match block.content with
    | Missing -> true
    | Fields fields | Array fields -> List.for_all is_empty fields
    | _ -> false

  let outer_is_empty outer = is_empty outer.root

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Ty.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Leaf e -> Expr.pp ft e
    | Fields v -> (parens (Fmt.list ~sep:Fmt.comma pp)) ft v
    | Enum { discr; fields } ->
        pf ft "%a[%a]" int discr (Fmt.list ~sep:comma pp) fields
    | Array v -> (brackets (Fmt.list ~sep:comma pp)) ft v
    | Symbolic s -> Expr.pp ft s
    | Uninit -> Fmt.string ft "UNINIT"
    | Missing -> Fmt.string ft "MISSING"

  let pp_outer ft t =
    let open Fmt in
    pf ft "@[<v 2>[OFFSET: %a] %a @]" Expr.pp t.offset pp t.root

  let to_rust_value ?(current_proj = []) block :
      (Expr.t, Err.Conversion_error.t) Result.t =
    let rec aux ~current_proj ({ content; ty } as t) :
        (Expr.t, Err.Conversion_error.t) Result.t =
      let open Result.Syntax in
      match content with
      | Leaf s -> (
          match ty with
          | Scalar (Uint _ | Int _ | Char | Bool) | Ptr _ | Ref _ -> Ok s
          | _ -> Fmt.failwith "Malformed tree: %a" pp t)
      | Fields v ->
          let proj i = Projections.Field (i, ty) in
          let+ tuple =
            List.mapi
              (fun i f -> aux ~current_proj:(proj i :: current_proj) f)
              v
            |> Result.all
          in
          Expr.EList tuple
      | Array v ->
          let total_size = List.length v in
          let proj i = Projections.Index (i, ty, total_size) in
          let+ tuple =
            List.mapi
              (fun i f ->
                aux ~current_proj:(proj (Expr.int i) :: current_proj) f)
              v
            |> Result.all
          in
          Expr.EList tuple
      | Enum { discr; fields } ->
          let+ fields = List.map (aux ~current_proj) fields |> Result.all in
          Expr.EList [ Expr.int discr; EList fields ]
      | Symbolic s -> Ok s
      | Uninit -> Error (Uninit, List.rev current_proj)
      | Missing -> Error (Missing, List.rev current_proj)
    in
    aux ~current_proj block

  let to_rust_value_exn ~msg t = to_rust_value t |> Result.ok_or ~msg

  let rec complete_and_init block =
    match block.content with
    | Missing | Uninit -> false
    | Symbolic _ | Leaf _ -> true
    | Fields v | Array v | Enum { fields = v; _ } ->
        List.for_all complete_and_init v

  let assertions ~loc ~base_offset block =
    let value_cp = Actions.cp_to_name Value in
    let uninit_cp = Actions.cp_to_name Uninit in
    let many_uninits_cp = Actions.cp_to_name Many_uninits in
    let rec aux ~current_proj ({ content; ty } as block) =
      let ins ty =
        let proj =
          Projections.to_expr
            { base = base_offset; from_base = List.rev current_proj }
        in
        let ty = Ty.to_expr ty in
        [ loc; proj; ty ]
      in
      if complete_and_init block then
        let value =
          to_rust_value_exn
            ~msg:(__FUNCTION__ ^ ": Complete and init but to_rust_value failed?")
            block
        in
        Seq.return (Asrt.GA (value_cp, ins ty, [ value ]))
      else
        match content with
        | Uninit -> (
            match ty with
            | Array { length; ty } ->
                Seq.return
                  (Asrt.GA (many_uninits_cp, ins ty @ [ Expr.int length ], []))
            | SymArray { length; ty } ->
                Seq.return (Asrt.GA (many_uninits_cp, ins ty @ [ length ], []))
            | _ -> Seq.return (Asrt.GA (uninit_cp, ins ty, [])))
        | Missing -> Seq.empty
        | Fields v ->
            let proj i = Projections.Field (i, ty) in
            List.to_seq v
            |> Seq.mapi (fun i f ->
                   aux ~current_proj:(proj i :: current_proj) f)
            |> Seq.concat
        | Array v ->
            let total_size = List.length v in
            let proj i = Projections.Index (Expr.int i, ty, total_size) in
            List.to_seq v
            |> Seq.mapi (fun i f ->
                   aux ~current_proj:(proj i :: current_proj) f)
            |> Seq.concat
        | Enum _ ->
            failwith
              "Trying to derive assertion for incomplete enum: to implement!"
        | Symbolic _ | Leaf _ -> failwith "unreachable"
    in

    aux ~current_proj:[] block

  let outer_assertions ~loc block =
    assertions ~loc ~base_offset:(Some block.offset) block.root

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
    let content = Fields content in
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
        let content = Enum { discr = vidx; fields } in
        { ty; content }
    | _ ->
        Fmt.failwith "Invalid enum value for type %a: %a" Ty.pp ty
          (Fmt.list Expr.pp) data

  and of_rust_value ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    match (ty, e) with
    | (Ty.Scalar (Uint _ | Int _ | Bool) | Ptr _ | Ref _), e ->
        Logging.tmi (fun m -> m "valid: %a for %a" Expr.pp e Ty.pp ty);
        if%sat TypePreds.valid ty e then DR.ok { ty; content = Leaf e }
        else DR.error (Err.Invalid_value (ty, e))
    | Tuple _, Lit (LList data) ->
        let content = List.map lift_lit data in
        of_rust_value ~tyenv ~ty (EList content)
    | Tuple ts, EList tup ->
        let++ content =
          DR_list.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) ts tup
        in
        let content = Fields content in
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
    | Array { length; ty = ty' }, EList l
      when List.compare_length_with l length == 0 ->
        let++ mem_array = DR_list.map (of_rust_value ~tyenv ~ty:ty') l in
        { ty; content = Array mem_array }
    | _, s -> DR.ok { ty; content = Symbolic s }

  let outer_missing ~offset ~tyenv:_ ty =
    let root = { ty; content = Missing } in
    { offset; root }

  let outer_symbolic ~offset ~tyenv:_ ty e =
    let root = { ty; content = Symbolic e } in
    { offset; root }

  let rec uninitialized ~tyenv ty =
    match ty with
    | Ty.Tuple v ->
        let tuple = List.map (uninitialized ~tyenv) v in
        { ty; content = Fields tuple }
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            let tuple =
              List.map
                (fun (_, t) -> uninitialized ~tyenv (Ty.subst_params ~subst t))
                fields
            in

            { ty; content = Fields tuple }
        | Enum _ -> { ty; content = Uninit })
    | Array { length; ty = ty' } ->
        let uninit_field _ = uninitialized ~tyenv ty' in
        let content = List.init length uninit_field in
        { ty; content = Array content }
    | Scalar _ | Ref _ | Ptr _ | Unresolved _ | SymArray _ ->
        { ty; content = Uninit }
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"

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
    let has_length i l = (Expr.list_length l) #== (Expr.int i) in
    match ty with
    | Ty.Tuple v ->
        if%ent (is_list expr) #&& (has_length (List.length v) expr) then
          let values =
            List.init (List.length v) (fun i -> Expr.list_nth expr i)
          in
          let fields =
            List.map2 (fun ty e -> { content = Symbolic e; ty }) v values
          in
          DR.ok { ty; content = Fields fields }
        else too_symbolic expr
          (* FIXME: This is probably not the right error? *)
    | Array { length; ty = ty' } ->
        if%sat (is_list expr) #&& (has_length length expr) then
          let values = List.init length (fun i -> Expr.list_nth expr i) in
          let fields =
            List.map (fun e -> { content = Symbolic e; ty = ty' }) values
          in
          DR.ok { ty; content = Array fields }
        else too_symbolic expr
    | SymArray { length = _; ty = _ } ->
        failwith "Implement: Sym_array semi_concretize"
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            if%sat (is_list expr) #&& (has_length (List.length fields) expr)
            then
              let values =
                List.init (List.length fields) (fun i -> Expr.list_nth expr i)
              in
              let fields =
                List.map2
                  (fun (_, ty) e ->
                    { content = Symbolic e; ty = Ty.subst_params ~subst ty })
                  fields values
              in
              DR.ok { ty; content = Fields fields }
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
              (is_list expr) #&& (has_length 2 expr)
              #&& (th_variant_idx #== (Expr.int variant_idx))
              #&& (is_list th_fields)
              #&& (has_length number_fields th_fields)
            then
              let values =
                List.init number_fields (fun i -> Expr.list_nth th_fields i)
              in
              let fields =
                List.map2
                  (fun ty e ->
                    { content = Symbolic e; ty = Ty.subst_params ~subst ty })
                  (snd variant) values
              in
              DR.ok { ty; content = Enum { discr = variant_idx; fields } }
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

  let rec partially_missing t =
    match t.content with
    | Missing -> true
    | Array fields | Fields fields | Enum { fields; _ } ->
        List.exists partially_missing fields
    | Symbolic _ | Uninit | Leaf _ -> false

  let rec missing_qty t =
    match t.content with
    | Missing -> Some Err.Totally
    | Array fields | Fields fields | Enum { fields; _ } ->
        if List.exists (fun f -> Option.is_some (missing_qty f)) fields then
          Some Partially
        else None
    | Symbolic _ | Uninit | Leaf _ -> None

  let totally_missing t =
    match t.content with
    | Missing -> true
    | _ -> false

  let missing ty = { ty; content = Missing }

  let structural_missing ~tyenv (ty : Ty.t) =
    match ty with
    | Array { length; ty = cty } ->
        let missing_child = { ty = cty; content = Missing } in
        { ty; content = Array (List.init length (fun _ -> missing_child)) }
    | Tuple fields ->
        {
          ty;
          content =
            Fields (List.map (fun ty -> { content = Missing; ty }) fields);
        }
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            let missing_fields =
              List.map
                (fun (_, cty) ->
                  let ty = Ty.subst_params ~subst cty in
                  { ty; content = Missing })
                fields
            in
            { ty; content = Fields missing_fields }
        | Enum _ as def ->
            Fmt.failwith "Unhandled: structural missing for Enum %a"
              Common.Ty.Adt_def.pp def)
    | SymArray _ -> failwith "structural missing: Sym_array, to implement"
    | Scalar _ | Ref _ | Ptr _ | Unresolved _ | Slice _ ->
        Fmt.failwith "structural missing called on a leaf or unsized: %a" Ty.pp
          ty

  let rec find_path
      ~tyenv
      ~return_and_update
      ~ty:expected_ty
      t
      (path : Projections.op list) : ('a * t, Err.t) DR.t =
    let rec_call = find_path ~ty:expected_ty ~tyenv ~return_and_update in
    match (path, t.content, t.ty) with
    | [], _, _ ->
        if not (Ty.equal t.ty expected_ty) then
          failwith "mismatch in type! need to implement casting";
        return_and_update t
    | Field (i, ty) :: rest, Fields vec, ty' when Ty.equal ty ty' ->
        let e = Result.ok_or vec.%[i] ~msg:"Index out of bounds" in
        let** v, sub_block = rec_call e rest in
        let++ new_fields = Delayed.return (vec.%[i] <- sub_block) in
        (v, { ty; content = Fields new_fields })
    | VField (i, ty, vidx) :: rest, Enum { discr; fields }, ty'
      when Ty.equal ty ty' && discr == vidx ->
        let e = Result.ok_or fields.%[i] ~msg:"Index out of bounds" in
        let** v, sub_block = rec_call e rest in
        let++ new_fields = Delayed.return (fields.%[i] <- sub_block) in
        (v, { ty; content = Enum { discr; fields = new_fields } })
    | (op :: _ as path), Symbolic s, ty ->
        let variant = Projections.variant op in
        let** this_block = semi_concretize ~tyenv ~variant ty s in
        rec_call this_block path
    | _ :: _, Missing, ty ->
        Logging.tmi (fun m ->
            m "Structural missing: %a" (Fmt.Dump.list Projections.pp_op) path);
        let this_block = structural_missing ~tyenv ty in
        rec_call this_block path
    | _ ->
        Fmt.failwith "Couldn't resolve path: (content: %a, path: %a)" pp_content
          t.content
          (Fmt.Dump.list Projections.pp_op)
          path

  let find_slice
      ~tyenv:_
      ~lk (* The lk should probably be hidden in a state monad *)
      ~return_and_update
      ~ty
      (t : t)
      (path : Projections.op list)
      size =
    let open Formula.Infix in
    (* For now we implement only a few cases we'll need more as we do more case studies and proofs *)
    match (path, t.content, t.ty) with
    | [], Missing, Array { ty = ty'; length } when Ty.equal ty ty' ->
        if%ent (Expr.int length) #== size then
          let++ value, new_slice = return_and_update t in
          (value, new_slice, lk)
        else failwith "Not implemented: sub-array of missing"
    | [], Missing, SymArray { ty = ty'; length } when Ty.equal ty ty' ->
        if%ent length #== size then
          let++ value, new_slice = return_and_update t in
          (value, new_slice, lk)
        else failwith "Not implement: sub-sym-array of missing"
    | [ Cast (_ty_from, ty_to) ], Uninit, SymArray { ty = ty'; length }
      when Ty.equal ty' ty_to && Ty.equal ty_to ty ->
        if%ent length #== size then
          let++ value, new_slice = return_and_update t in
          (value, new_slice, lk)
        else failwith "Not implement: sub-sym-array of uninit after cast"
    | [ Cast (ty_from, ty_to) ], Uninit, SymArray { ty = ty'; length }
      when Ty.equal ty_from ty' && Ty.equal ty_to ty ->
        let* size_from, lk = Layout_knowledge.size_of ~lk ty_from in
        let* size_to, lk = Layout_knowledge.size_of ~lk ty_to in
        let length = Expr.Infix.(length * size_from / size_to) in
        if%ent length #== size then
          let++ value, new_slice = return_and_update t in
          (value, new_slice, lk)
        else failwith "Not implement: sub-sym-array of uninit after cast"
    | path, content, ty ->
        Fmt.failwith "Unimplemented case for find_slice: %a, %a, %a, %a"
          Projections.pp_path path pp_content content Ty.pp ty Expr.pp size

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
    let++ ret, root = find_path ~tyenv ~return_and_update ~ty t path in
    (ret, { outer with root })

  let load_proj ~loc ~tyenv t proj ty copy =
    let open Result.Syntax in
    let update block = if copy then block else uninitialized ~tyenv ty in
    let return_and_update t =
      let result =
        let+ value =
          to_rust_value t
          |> Result.map_error (Err.Conversion_error.lift ~loc ~proj)
        in
        (value, update t)
      in
      DR.of_result result
    in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let cons_proj ~loc ~tyenv t proj ty =
    let open Result.Syntax in
    let return_and_update t =
      let result =
        let+ value =
          to_rust_value t
          |> Result.map_error (Err.Conversion_error.lift ~loc ~proj)
        in
        (value, missing t.ty)
      in
      DR.of_result result
    in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let prod_proj ~tyenv t proj ty value =
    let* new_block =
      let return_and_update block =
        match missing_qty block with
        | Some Totally ->
            let++ value = of_rust_value ~tyenv ~ty value in
            ((), value)
        | _ -> Delayed.vanish ()
        (* Duplicated resources *)
      in
      let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
      new_block
    in
    match new_block with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let cons_uninit ~loc:_ ~tyenv t proj ty =
    let return_and_update t =
      match t.content with
      | Uninit -> DR.ok ((), missing t.ty)
      | _ -> DR.error (Err.LogicError "Not uninit")
    in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let prod_uninit ~loc:_ ~tyenv t proj ty =
    let* new_block =
      let return_and_update block =
        match missing_qty block with
        | Some Totally ->
            let value = uninitialized ~tyenv ty in
            DR.ok ((), value)
        | _ -> Delayed.vanish ()
        (* Duplicated resource *)
      in
      let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
      new_block
    in
    match new_block with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let cons_many_uninits ~loc:_ ~tyenv t proj ty size =
    let return_and_update t =
      match t.content with
      | Uninit -> DR.ok ((), missing t.ty)
      | _ -> DR.error (Err.LogicError "Not uninit")
    in
    find_slice_outer ~tyenv ~return_and_update ~ty t proj size

  let prod_many_uninits ~loc:_ ~lk ~tyenv t proj ty size =
    let* new_block =
      let return_and_update block =
        match missing_qty block with
        | Some Totally ->
            let value = uninitialized ~tyenv (Ty.array_of_size size ty) in
            DR.ok ((), value)
        | _ -> Delayed.vanish ()
        (* Duplicated resource *)
      in
      let++ _, new_block, lk =
        find_slice_outer ~ty ~lk ~tyenv ~return_and_update t proj size
      in
      (new_block, lk)
    in
    match new_block with
    | Ok x -> Delayed.return x
    | Error _ -> Delayed.vanish ()

  let store_proj ~loc ~tyenv t proj ty value =
    let return_and_update block =
      match missing_qty block with
      | Some qty -> DR.error (Err.Missing_proj (loc, proj, qty))
      | None ->
          let++ value = of_rust_value ~tyenv ~ty value in
          ((), value)
    in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let get_discr ~tyenv t proj enum_typ =
    let return_and_update block =
      match block.content with
      | Enum t -> DR.ok (Expr.int t.discr, block)
      | Symbolic expr ->
          let open Formula.Infix in
          if%sat
            (Expr.typeof expr) #== (Expr.type_ ListType)
            #&& ((Expr.list_length expr) #== (Expr.int 2))
          then DR.ok (Expr.list_nth expr 0, block)
          else too_symbolic expr
      | _ -> DR.error (Invalid_type (block.ty, enum_typ))
    in
    let++ discr, _ = find_proj ~tyenv ~return_and_update ~ty:enum_typ t proj in
    discr

  let deinit ~tyenv t proj ty =
    let return_and_update _block = DR.ok ((), uninitialized ~tyenv ty) in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let rec equality_constraints t1 t2 =
    let ( #== ) = Formula.Infix.( #== ) in
    match (t1.content, t2.content) with
    | Missing, _ | _, Missing -> []
    | (Symbolic e1 | Leaf e1), (Symbolic e2 | Leaf e2) -> [ e1 #== e2 ]
    | Fields f1, Fields f2 -> List_utils.concat_map_2 equality_constraints f1 f2
    | Array f1, Array f2 -> List_utils.concat_map_2 equality_constraints f1 f2
    | Enum _, Enum _ ->
        let to_value =
          to_rust_value_exn ~msg:"Equality constraint: Malformed enums!!"
        in
        (* Sub parts of enum cannot be missing *)
        [ (to_value t1) #== (to_value t2) ]
    | Symbolic e, content | content, Symbolic e -> (
        match to_rust_value { ty = t1.ty; content } with
        | Ok value -> [ value #== e ]
        | Error _ -> Fmt.failwith "Need to semi-concretize things to learn")
    | _ -> Fmt.failwith "cannot learn equality of %a and %a" pp t1 pp t2

  let substitution ~tyenv ~subst_expr t =
    let rec substitute_content ~ty t =
      match t with
      | Leaf e ->
          let e = subst_expr e in
          DR.ok ~learned:[ TypePreds.valid ty e ] (Leaf e)
      | Array lst ->
          let++ lst = DR_list.map substitution lst in
          Array lst
      | Fields lst ->
          let++ lst = DR_list.map substitution lst in
          Fields lst
      | Enum { fields; discr } ->
          let++ fields = DR_list.map substitution fields in
          Enum { fields; discr }
      | Symbolic s ->
          let new_s = subst_expr s in
          if new_s == s then DR.ok t
          else
            let++ value = of_rust_value ~tyenv ~ty new_s in
            value.content
      | Uninit | Missing -> DR.ok t
    and substitution { content; ty } =
      let ty = Ty.substitution ~subst_expr ty in
      let++ content = substitute_content ~ty content in
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
    | { content = Missing; _ }, _ -> o2
    | _, { content = Missing; _ } -> o1
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

let alloc_raw ~tyenv (heap : t) length =
  let loc = ALoc.alloc () in
  let ty = Ty.SymArray { length; ty = Scalar (Uint U8) } in
  let new_block = TreeBlock.uninitialized_outer ~tyenv ty in
  let new_heap = MemMap.add loc (T new_block) heap in
  (loc, new_heap)

let load ~tyenv (mem : t) loc proj ty copy =
  Logging.tmi (fun m -> m "Found block: %s" loc);
  let** block = find_not_freed loc mem in
  let++ v, new_block = TreeBlock.load_proj ~loc ~tyenv block proj ty copy in
  let new_mem = MemMap.add loc (T new_block) mem in
  (v, new_mem)

let store ~tyenv (mem : t) loc proj ty value =
  let** block = find_not_freed loc mem in
  let++ new_block = TreeBlock.store_proj ~loc ~tyenv block proj ty value in
  MemMap.add loc (T new_block) mem

let cons_value ~tyenv (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ value, outer = TreeBlock.cons_proj ~loc ~tyenv block proj ty in
  (value, MemMap.add loc (T outer) mem)

let prod_value ~tyenv (mem : t) loc (proj : Projections.t) ty value =
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
  let+ new_block = TreeBlock.prod_proj ~tyenv root proj ty value in
  MemMap.add loc (T new_block) mem

let cons_uninit ~tyenv (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ (), outer = TreeBlock.cons_uninit ~loc ~tyenv block proj ty in
  MemMap.add loc (T outer) mem

let prod_uninit ~tyenv (mem : t) loc (proj : Projections.t) ty =
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
  let+ new_block = TreeBlock.prod_uninit ~loc ~tyenv root proj ty in
  MemMap.add loc (T new_block) mem

let cons_many_uninits ~lk ~tyenv (mem : t) loc proj ty size =
  let** block = find_not_freed loc mem in
  let++ (), outer, lk =
    TreeBlock.cons_many_uninits ~loc ~lk ~tyenv block proj ty size
  in
  (MemMap.add loc (T outer) mem, lk)

let prod_many_uninits ~lk ~tyenv (mem : t) loc (proj : Projections.t) ty size =
  let root =
    match MemMap.find_opt loc mem with
    | Some (T root) -> root
    | Some Freed -> failwith "use after free"
    | None ->
        TreeBlock.outer_missing
          ~offset:(Option.value ~default:(Expr.EList []) proj.base)
          ~tyenv
          (Projections.base_ty_slice ~leaf_ty:ty proj size)
  in
  let+ new_block, lk =
    TreeBlock.prod_many_uninits ~loc ~lk ~tyenv root proj ty size
  in
  (MemMap.add loc (T new_block) mem, lk)

let deinit ~tyenv (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ new_block = TreeBlock.deinit ~tyenv block proj ty in
  MemMap.add loc (T new_block) mem

let free (mem : t) loc ty =
  let** block = find_not_freed loc mem in
  let base_is_not_empty =
    let open Formula.Infix in
    fnot block.offset #== (Expr.EList [])
  in
  if%sat base_is_not_empty then DR.error (MissingBlock loc)
  else if not (Ty.equal block.root.ty ty) then
    DR.error (Invalid_type (ty, block.root.ty))
  else DR.ok (MemMap.add loc Freed mem)

let load_discr ~tyenv (mem : t) loc proj enum_typ =
  let** block = find_not_freed loc mem in
  TreeBlock.get_discr ~tyenv block proj enum_typ

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
