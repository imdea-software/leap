type ('a,'b) t

val create : int -> ('a,'b) t
val clear : ('a,'b) t -> unit
val copy : ('a,'b) t -> ('a,'b) t

val add : ('a,'b) t -> 'a -> 'b -> unit
val mem : ('a, 'b) t -> 'a -> bool
val dom : ('a,'b) t -> 'a list
val codom : ('a,'b) t -> 'b list
val find_id : ('a, 'b) t -> 'a -> 'b
val find_dom : ('a, 'b) t -> 'b -> 'a list
val dom_size : ('a,'b) t  -> int
val codom_size : ('a,'b) t  -> int

val unify_id : ('a,'b) t -> 'b -> 'b -> unit

val iter : ('a -> 'b -> unit) -> ('a,'b) t -> unit
val fold : ('a -> 'b -> 'c -> 'c) -> ('a,'b) t -> 'c -> 'c
