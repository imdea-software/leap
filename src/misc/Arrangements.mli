
(** The type of an arrangement *)
type 'a t

(** The type of arrangements tree *)
type 'a arrtree

(** [empty ()] returns an empty arrangement *)
val empty : unit -> 'a t

(** [add_eq arr a b] inserts an equality between [a] and [b] into the
    arrangement [arr] *)
val add_eq : 'a t -> 'a -> 'a -> unit

(** [add_ineq arr a b] inserts an inequality between [a] and [b] into the
    arrangement [arr] *)
val add_ineq : 'a t -> 'a -> 'a -> unit

(** [add_order arr a b] inserts an order relation between [a] and [b] into the
    arrangement [arr] *)
val add_order : 'a t -> 'a -> 'a -> unit

(** [to_str arr] returns a string with the equalities, inequalities and order
    relation within the arrangement *)
val to_str : 'a t -> ('a -> string) -> string

val gen_arrtrees : 'a t -> 'a arrtree list


