type 'a vec

val ( .%[] ) : 'a vec -> int -> ('a, unit) Result.t

val ( .%[]<- ) : 'a vec -> int -> 'a -> ('a vec, unit) Result.t

val map : ('a -> 'b) -> 'a vec -> 'b vec

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b vec -> 'a

val of_list : 'a list -> 'a vec

val to_list : 'a vec -> 'a list

val pp : ?sep:unit Fmt.t -> 'a Fmt.t -> 'a vec Fmt.t
