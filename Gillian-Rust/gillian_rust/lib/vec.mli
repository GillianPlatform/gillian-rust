type 'a vec

val make : int -> 'a -> 'a vec
val init : int -> (int -> 'a) -> 'a vec
val ( .%[] ) : 'a vec -> int -> ('a, unit) Result.t
val ( .%[]<- ) : 'a vec -> int -> 'a -> ('a vec, unit) Result.t

val override_range :
  'a vec -> start:int -> size:int -> ('a -> 'a) -> ('a vec, unit) Result.t
(** Returns a new vector, where [size] elements, starting from [start], have been overriden using the [update] function *)

val override_range_with_list :
  'a vec -> start:int -> f:('b -> 'a) -> 'b list -> ('a vec, unit) Result.t

val sublist_map : start:int -> size:int -> f:('a -> 'b) -> 'a vec -> 'b list
val map : ('a -> 'b) -> 'a vec -> 'b vec
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b vec -> 'a
val of_list : 'a list -> 'a vec
val to_list : 'a vec -> 'a list
val pp : ?sep:unit Fmt.t -> 'a Fmt.t -> 'a vec Fmt.t
