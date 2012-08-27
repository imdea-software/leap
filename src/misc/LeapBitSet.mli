
type 'a t
(** The type of bit vectors of fixed length *)

val empty : int -> 'a t
(** [create n] creates a new empty bit vector of size [n] *)

val copy : 'a t -> 'a t
(** [copy v] return a copy of vector [v] *)

val add : ('a -> int) -> 'a t -> 'a -> unit
(** [add f v a] adds to vector [v] element [a]. To map a position for
    such element, function [f] is used *)

val union : 'a t -> 'a t -> 'a t
(** [union v w] returns the union between [v] and [w] *)

val intersect : 'a t -> 'a t -> 'a t
(** [intersect v w] returns the intersection between [v] and [w] *)

val complement : 'a t -> 'a t
(** [complement v] returns the complementary of vector [v] *)

val disjoint : 'a t -> 'a t -> bool
(** [disjoint v w] determines whether the intersection between [v]
    and [w] is empty *)

val to_str : 'a t -> string
(** [to_str v] returns a string representation of vector [v] *)
