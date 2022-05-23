open Projections

type variant_idx = int
type size = int

module Partial_align = struct
  type t = ExactlyPow2 of int | AtLeastPow2 of int

  let max a a' = match a, a' with
    | ExactlyPow2 a, ExactlyPow2 a' -> ExactlyPow2 (max a a')
    | AtLeastPow2 a, AtLeastPow2 a' | ExactlyPow2 a, AtLeastPow2 a' | AtLeastPow2 a, ExactlyPow2 a' -> AtLeastPow2 (max a a')

  let maximum = Seq.fold_left max (ExactlyPow2 0)
end

module Partial_size = struct
  type t = Exactly of size | AtLeast of size

  let map f = function
    | Exactly size -> Exactly (f size)
    | AtLeast size -> AtLeast (f size)

  let from_alignment : Partial_align.t -> t = function
    | ExactlyPow2 n -> Exactly (Int.shift_left 1 n)
    | AtLeastPow2 n -> AtLeast (Int.shift_left 1 n)
  
  let add sz sz' = match sz, sz' with
    | Exactly sz, Exactly sz' -> Exactly (sz + sz')
    | AtLeast sz, AtLeast sz' | Exactly sz, AtLeast sz' | AtLeast sz, Exactly sz' -> AtLeast (sz + sz')

  let sum = Seq.fold_left add (Exactly 0)
end

type align = { pow2 : int }
type wrapping_range = { start : int; finish : int }
type base_integer = I8 | I16 | I32 | I64 | I128
type primative = Int of base_integer * bool | F32 | F64 | Pointer
type scalar = { primative : primative; valid_range : wrapping_range }

type offset =
  | Bytes     of size
  | FromIndex of int * size
  | FromCount of Rust_types.t * int * size

type fields_shape =
  | Primative
  | Union     of int
  | Array     of Partial_size.t * int
  (* offset array includes the offset of the end *)
  | Arbitrary of offset array

type variants =
  | Single   of variant_idx
  | Multiple of { tag : scalar option; variants : partial_layout array }

and partial_layout = {
  fields : fields_shape;
  variant : variants;
  align : Partial_align.t;
  size : Partial_size.t;
}

type context = {
  partial_layouts : Rust_types.t -> partial_layout;
  members : Rust_types.t -> Rust_types.t array;
}

let rec contextualise (context : context) (route : op list) : op list =
  match route with
  | Plus (w, i, t) :: rs -> (
      match (context.partial_layouts t).size with
      | Exactly sz -> UPlus (w, sz * i) :: contextualise context rs
      | _          -> Plus (w, i, t) :: contextualise context rs)
  | Index (i, t, n) :: rs when i < n ->
      Cast (Rust_types.Array { length = n; ty = t }, t)
      :: contextualise context rs
  | Field (i, t) :: rs -> (
      let t' = (context.members t).(i) and rs' = contextualise context rs in
      match (context.partial_layouts t).fields with
      | Arbitrary os -> (
          match os.(i) with
          | Bytes n                -> Cast (t, t')
                                      :: UPlus (Overflow, n)
                                      :: rs'
          | FromIndex (i', n)      ->
              Field (i', t)
              :: Cast ((context.members t).(i'), t')
              :: UPlus (Overflow, n)
              :: rs'
          | FromCount (t'', n, n') ->
              Cast (t, t'')
              :: Plus (Overflow, n, t'')
              :: Cast (t'', t')
              :: UPlus (Overflow, n')
              :: rs')
      | _            -> Field (i, t) :: contextualise context rs)
  | r :: rs -> r :: contextualise context rs
  | [] -> []

let rec cons_all ys xs =
  match ys with y :: ys' -> cons_all ys' (y :: xs) | [] -> xs

let reorder : op list -> op list =
  let rec reorder' upluss rs =
    match rs with
    | (UPlus (_, _) as r) :: rs -> reorder' (r :: upluss) rs
    | (Cast (_, _) as r) :: rs  -> r :: reorder' upluss rs
    | r :: rs                   -> cons_all upluss (r :: reorder' upluss rs)
    | []                        -> []
  in
  reorder' []

let rec simplify : op list -> op list = function
  (* We have to handle 0s/Identity casts removed from the next element, since they could lead to two elements being next to each other and simplifying *)
  | r :: Plus (_, 0, _) :: rs -> simplify (r :: rs)
  | r :: UPlus (_, 0) :: rs -> simplify (r :: rs)
  | r :: Cast (t, t') :: rs when t = t' -> simplify (r :: rs)
  | Plus (Wrap, i, t) :: Plus (Wrap, i', t') :: rs when t = t' ->
      simplify (Plus (Wrap, i + i', t) :: rs)
  | UPlus (Wrap, i) :: UPlus (Wrap, i') :: rs ->
      simplify (UPlus (Wrap, i + i') :: rs)
  | Plus (Overflow, i, t) :: Plus (Overflow, i', t') :: rs
    when i * i' > 0 && t = t' ->
      simplify (Plus (Overflow, i + i, t) :: rs)
  | UPlus (Overflow, i) :: UPlus (Overflow, i') :: rs when i * i' > 0 ->
      simplify (UPlus (Overflow, i + i) :: rs)
  | Cast (t, t'') :: Cast (t''', t') :: rs when t'' = t''' ->
      simplify (Cast (t, t') :: rs)
  (* We also have to handle 0s if they're at the front, from other rules or as the last element *)
  | Plus (_, 0, _) :: rs -> simplify rs
  | UPlus (_, 0) :: rs -> simplify rs
  | Cast (t, t') :: rs when t = t' -> simplify rs
  | r :: rs -> r :: simplify rs
  | [] -> []

let reduce context rs = simplify @@ reorder @@ contextualise context rs

type address = {
  block : int;
  block_type : Rust_types.t;
  route : op list;
  address_type : Rust_types.t;
}

type access = { index : int; index_type : Rust_types.t; against : Rust_types.t }

let distance_to_next_field (partial_layout : partial_layout) (a : int) =
  match partial_layout.fields with
  | Arbitrary offsets when a >= 0 && a + 1 < Array.length offsets -> (
      match (offsets.(a), offsets.(a + 1)) with
      | Bytes n, Bytes n' -> Some (Bytes (n' - n ))
      | FromIndex (n, b), FromIndex (n', b') when n = n' ->
          Some (Bytes (b' - b))
      | FromCount (t, n, b), FromCount (t', n', b') when t = t' ->
          let b'' = b' - b in
          Some (if n' == n then Bytes b'' else FromCount (t, n' - n, b''))
      | _, _ -> None)
  | _ -> None

exception
  AccessError of access list * op list * Rust_types.t * int option * string

module UpTreeDirection = struct
  type t = Curr | Fwd

  let magnitude = function Curr -> 0 | Fwd -> 1
end

module DownTreeDirection = struct
  type t = Bkwd | Curr

  let from_int i = if i < 0 then Bkwd else Curr
  let magnitude = function Bkwd -> -1 | Curr -> 0
end

(* Divide rounding towards -signum(m) * inf *)
let div' (n : int) (m : int) = (n / m) - if n * m < 0 then 1 else 0

let mod' (n : int) (m : int) =
  let res = n mod m in
  if res < 0 then res + m else res

let signum (n : int) = if n < 0 then -1 else if n = 0 then 0 else 1

let rec resolve (context : context) (accesses : access list) (ty : Rust_types.t)
    (rs : op list) (index : int option) : access list =
  let access_error message =
    raise (AccessError (accesses, rs, ty, index, message))
  and ix =
    if Option.is_some index then index
    else
      match (context.partial_layouts ty).fields with
      | Arbitrary offsets when offsets.(0) = Bytes 0 -> Some 0
      | _ -> None
  and accesses' index index_type =
    { index; index_type; against = ty } :: accesses
  in
  let down_tree_cast (dir : DownTreeDirection.t) =
    match ix with
    | Some ix ->
        let ix' = ix + DownTreeDirection.magnitude dir in
        let ix'_type = (context.members ty).(ix') in
        let casted_ix =
          match dir with
          | DownTreeDirection.Bkwd -> Array.length (context.members ix'_type)
          | DownTreeDirection.Curr -> 0
        in
        resolve context (accesses' ix' ix'_type) ix'_type rs (Some casted_ix)
    | None    -> access_error "Can't down-tree cast from no known index"
  in
  let rec up_tree_cast dir accesses' rs' =
    match accesses' with
    (* We're not checking whether the type cast to is meant to have indices, but this should be fine as it won't be able to progress once there *)
    | { index; index_type = _; against } :: as' ->
        let max_ix = Array.length (context.members against)
        and ix' = index + UpTreeDirection.magnitude dir in
        if ix' <= max_ix then resolve context as' against rs' (Some ix')
        else up_tree_cast dir as' rs'
    | [] ->
        access_error "Could not up tree cast from beyond top of access stack"
  in

  match (rs, ix) with
  | Field (i, t) :: rs', None when t = ty ->
      let t' = (context.members t).(i) in
      resolve context (accesses' i t') t rs' None
  (* TODO handle invalid indices etc. *)
  | Field (i, t) :: rs', Some 0 when t = ty ->
      resolve context accesses ty rs' (Some i)
  | Index (i, t, n) :: rs', Some ix
    when i < n && Rust_types.Array { length = n; ty = t } = ty ->
      resolve context accesses ty rs' (Some (i + ix))
  | Downcast (i, t) :: rs', None when t = ty ->
      let t' = (context.members t).(i) in
      resolve context (accesses' i t') t rs' None
  | Cast (_, _) :: rs', ix -> resolve context accesses ty rs' ix
  | Plus (_, 0, _) :: _, _ ->
      access_error "Invalid +^t 0 should not exist at resolution stage"
  | Plus (w, i, t) :: rs', Some ix -> (
      let i' = i + ix
      and modify_plus_eliminating_zero new_i =
        if new_i = 0 then rs' else Plus (w, new_i, t) :: rs'
      and partial_layout = context.partial_layouts ty in
      match ty with
      | Rust_types.Array { ty = tElem; length = n } when tElem = t ->
          if i' < 0 then
            up_tree_cast UpTreeDirection.Curr accesses
              (modify_plus_eliminating_zero i')
          else if i' < n then resolve context accesses ty rs' (Some (i' - n))
          else
            up_tree_cast UpTreeDirection.Fwd accesses
              (modify_plus_eliminating_zero i')
      | Rust_types.Named _ -> (
          let moving_over_field, next_i, next_ix =
            if i < 0 then (ix - 1, i + 1, ix - 1) else (ix, i - 1, ix + 1)
          and members = context.members ty in
          if i < 0 && ix = 0 then
            (* We can up-tree cast directly since we're at field ix 0 *)
            up_tree_cast UpTreeDirection.Curr accesses rs
          else
            match distance_to_next_field partial_layout moving_over_field with
            | Some (FromCount (t', _, 0)) when t' = t ->
                (if next_ix = Array.length members then
                 up_tree_cast UpTreeDirection.Fwd accesses
                else fun rs'' ->
                  resolve context accesses ty rs'' @@ Some next_ix)
                  (modify_plus_eliminating_zero next_i)
            | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | _ -> down_tree_cast (DownTreeDirection.from_int i))
  | UPlus (_, 0) :: _, _ ->
      access_error "Invalid +^U 0 should not exist at resolution stage"
  | UPlus (w, i) :: rs', Some ix -> (
      let modify_uplus_eliminating_zero new_i =
        if new_i = 0 then rs' else UPlus (w, new_i) :: rs'
      and partial_layout = context.partial_layouts ty in
      match ty with
      | Rust_types.Array { ty = tElem; length = n } -> (
          match (context.partial_layouts tElem).size with
          | Exactly size ->
              let ix' = ix + div' i size and rem = mod' i size in
              if ix' < 0 then
                up_tree_cast UpTreeDirection.Curr accesses
                @@ modify_uplus_eliminating_zero
                @@ ((ix * size) + i)
                (* We must only handle cases where we can make progress at this level, otherwise down_tree_cast *)
              else if ix' = ix then
                down_tree_cast (DownTreeDirection.from_int i)
              else if ix' < n then
                resolve context accesses ty
                  (modify_uplus_eliminating_zero rem)
                  (Some ix')
              else
                up_tree_cast UpTreeDirection.Fwd accesses
                @@ modify_uplus_eliminating_zero
                @@ (i - ((n - ix) * size))
          | _                -> down_tree_cast (DownTreeDirection.from_int i))
      | Rust_types.Named _ -> (
          let moving_over_field, next_ix =
            if i < 0 then (ix - 1, ix - 1) else (ix, ix + 1)
          and members = context.members ty in
          if i < 0 && ix = 0 then
            (* We can up-tree cast directly since we're at field ix 0 *)
            up_tree_cast UpTreeDirection.Curr accesses rs
          else
            match distance_to_next_field partial_layout moving_over_field with
            | Some (Bytes size) when size >= abs i ->
                (if next_ix = Array.length members then
                 up_tree_cast UpTreeDirection.Fwd accesses
                else fun rs'' ->
                  resolve context accesses ty rs'' @@ Some next_ix)
                  (modify_uplus_eliminating_zero (i - (signum i * size)))
            | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | _ -> down_tree_cast (DownTreeDirection.from_int i))
  | _ :: _, Some _ -> down_tree_cast DownTreeDirection.Curr
  | _ :: _, _ -> access_error "Stuck handling next op"
  | [], Some ix when ix > 0 ->
      accesses' ix (context.members ty).(ix)
      (* There's a lot of "crash" cases instead of nicely handled errors, context.members here should instead fail nicely if it's not a struct *)
  | [], _ -> accesses

let rec zero_offset_types (context : context) (ty : Rust_types.t) : Rust_types.t list =
  let sub_tree_types () = ty :: zero_offset_types context (context.members ty).(0) in
  match (context.partial_layouts ty).fields with
    | Arbitrary offsets when offsets.(0) = Bytes 0 -> sub_tree_types ()
    | Array (_, _) -> sub_tree_types ()
    | _ -> [ty]

let resolve_address (context : context) (address : address) : access list =
  let accesses = resolve context [] address.block_type address.route None in
  let result_type = function
    | a :: _ -> a.index_type
    | _ -> address.block_type in
  let r_t_accesses = result_type accesses
  in if r_t_accesses = address.address_type then
    accesses
  else
    let z_o_types = zero_offset_types context r_t_accesses in
    let rec make_pairs_until_fst pred = function
      | x :: ((x' :: _) as xs) when not @@ pred x -> (x, x') :: make_pairs_until_fst pred xs
      | _ -> [] in
    let z_o_conversions = make_pairs_until_fst (fun ty -> ty = address.address_type) z_o_types in 
    let as_z_o = List.map (function (index_type, against) -> { index = 0; index_type; against }) z_o_conversions in
    let as' = cons_all as_z_o accesses in
    if result_type as' = address.address_type then 
      as' else raise (AccessError (as', [], result_type as', Some 0, "Could not resolve to correct address type"))

    (* We return align not size as it's easier to convert this to a size than the reverse *)
let align_scalar_t : Rust_types.scalar_t -> Partial_align.t = function
  | Rust_types.Bool -> ExactlyPow2 0
  | Rust_types.Char -> ExactlyPow2 2
  | Rust_types.Int Rust_types.Isize -> AtLeastPow2 0
  | Rust_types.Int Rust_types.I8 -> ExactlyPow2 0
  | Rust_types.Int Rust_types.I16 -> ExactlyPow2 1
  | Rust_types.Int Rust_types.I32 -> ExactlyPow2 2
  | Rust_types.Int Rust_types.I64 -> ExactlyPow2 3
  | Rust_types.Int Rust_types.I128 -> ExactlyPow2 4
  | Rust_types.Uint Rust_types.Usize -> AtLeastPow2 0
  | Rust_types.Uint Rust_types.U8 -> ExactlyPow2 0
  | Rust_types.Uint Rust_types.U16 -> ExactlyPow2 1
  | Rust_types.Uint Rust_types.U32 -> ExactlyPow2 2
  | Rust_types.Uint Rust_types.U64 -> ExactlyPow2 3
  | Rust_types.Uint Rust_types.U128 -> ExactlyPow2 4

let align pow offset =
  let modulus = Int.shift_left 1 pow in
  let r = Int.rem offset modulus in
  match r with
    | 0 -> offset
    | _ -> offset - r + modulus

let next_offset (ix, curr_offset) ((ty, pl), (ty_next, pl_next)) = 
  let ix' = ix + 1 in (ix',
  match curr_offset, pl.size, pl_next.align with
  | Bytes b, Exactly sz, ExactlyPow2 pow -> Bytes (align pow @@ b + sz)
  | Bytes 0, _, ExactlyPow2 0 -> FromCount (ty, 1, 0)
  | Bytes 0, _, _ when ty = ty_next -> FromCount (ty, 1, 0)
  | FromCount (ty', n, b), Exactly sz, ExactlyPow2 pow -> FromCount (ty', n, align pow @@ b + sz)
  | FromCount (ty', n, 0), _, ExactlyPow2 0 when ty = ty' -> FromCount(ty', n + 1, 0)
  | FromCount (ty', n, 0), _, _ when ty = ty' && ty' = ty_next -> FromCount(ty', n + 1, 0)
  | FromIndex (ix_from, b), Exactly sz, ExactlyPow2 pow -> FromIndex (ix_from, align pow @@ b + sz)
  | _ -> FromIndex (ix', 0)
  )

let u8 = Rust_types.Scalar (Rust_types.Uint Rust_types.U8)
let u8_pl = {
  fields = Primative;
  variant = Single 0;
  align = align_scalar_t (Rust_types.Uint Rust_types.U8);
  size = Partial_size.from_alignment @@ align_scalar_t @@ Rust_types.Uint Rust_types.U8
}

let offsets_from_tys_and_pls (tys : Rust_types.t Seq.t) (pls : partial_layout Seq.t) : offset array =
  let end_offset = (u8, u8_pl) in
  let tys_pls = Seq.zip tys pls in
  Array.of_seq @@ 
    Seq.cons (Bytes 0) @@ 
    Seq.map (fun (_, o) -> o) @@ 
    Seq.scan next_offset (0, Bytes 0) @@
    Seq.zip (tys_pls) (Seq.append (Seq.drop 1 tys_pls) @@ List.to_seq [end_offset])


let rec partial_layout_of (genv : C_global_env.t) (known : (string, partial_layout) Hashtbl.t) : Rust_types.t -> partial_layout = function
  | Rust_types.Named n -> (match Hashtbl.find_opt known n with
    | Some layout -> layout
    | None ->
      let partial_layout = partial_layout_of genv known (C_global_env.get_type genv n) in
      Hashtbl.add known n partial_layout;
      partial_layout
  )
  | Rust_types.Array {length; ty} -> 
    let pl_ty = partial_layout_of genv known ty in
    {
      fields = Array(pl_ty.size, length);
      variant = Single 0;
      align = pl_ty.align;
      size = Partial_size.map (fun x -> x * length) pl_ty.size
    }
  | Rust_types.Scalar scalar_t ->
    let align = align_scalar_t scalar_t in
    {
      fields = Primative;
      variant = Single 0;
      align = align;
      size = Partial_size.from_alignment align
    }
  | Rust_types.Tuple ts ->
    let ts_seq = List.to_seq ts in
    let pls = Seq.map (fun t -> partial_layout_of genv known t) ts_seq in
    let align = Partial_align.maximum @@ Seq.map (fun pl -> pl.align) pls in
    let offsets = offsets_from_tys_and_pls ts_seq pls in
    let size = match offsets.(Array.length offsets - 1) with
      | Bytes n -> Partial_size.Exactly n
      | _ -> Partial_size.sum @@ Seq.map (fun pl -> pl.size) pls in
    {
      fields = Arbitrary offsets;
      variant = Single 0;
      align = align;
      size = size
    }
  | Rust_types.Struct (Rust_types.ReprC, fs) ->
    let ts = Seq.map (fun (_, t) -> t) @@ List.to_seq fs in
    let pls = Seq.map (partial_layout_of genv known) ts in
    let align = Partial_align.maximum @@ Seq.map (fun pl -> pl.align) pls in
    let offsets = offsets_from_tys_and_pls ts pls in
    let size = match offsets.(Array.length offsets - 1) with
      | Bytes n -> Partial_size.Exactly n
      | _ -> Partial_size.sum @@ Seq.map (fun pl -> pl.size) pls in
    {
      fields = Arbitrary offsets;
      variant = Single 0;
      align = align;
      size = size
    }
  | Rust_types.Struct (Rust_types.ReprRust, fs) ->
    let offsets = Array.init (List.length fs) (fun i -> FromIndex (i, 0)) in
    {
      fields = Arbitrary offsets;
      variant = Single 0;
      align = AtLeastPow2 0;
      size = AtLeast 0
    }
  | Rust_types.Enum (variants) ->
    (* Check how RustC actually uses Enum offsets (not variant offsets). We're not using this so it's fine *)
    let offsets = [||] in
    {
      fields = Arbitrary offsets;
      variant = Multiple {
        tag = None; (* No tag type since we're not handling ReprC enums yet *)
        variants = Array.of_seq @@ Seq.map (fun (_, fs) -> partial_layout_of genv known @@ Rust_types.Tuple fs) @@ List.to_seq variants
      };
      align = AtLeastPow2 0;
      size = AtLeast 0;
    }
  | Rust_types.Ref { mut = _; ty = _ } -> (* We could gain more information if we deduced it was an unsized type, however, this is fine without it since we use bounds not exact sizes *)
      {
        fields = Primative;
        variant = Single 0;
        align = AtLeastPow2 0;
        size = AtLeast 1
      }
  | Rust_types.Slice _ -> (* Is this a slice or slice reference; assumed slice reference *)
      {
        fields = Primative;
        variant = Single 0;
        align = AtLeastPow2 0;
        size = AtLeast 2
      }

let partial_layouts_from_env (genv : C_global_env.t) : Rust_types.t -> partial_layout =
  let partial_layouts = Hashtbl.create (Hashtbl.length (C_global_env.declared genv)) in
  partial_layout_of genv partial_layouts
