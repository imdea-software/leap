
(** The type of an arrangement *)
type 'a t

(** The type of arrangements tree *)
type 'a arrtree = Node of 'a list * 'a arrtree list

(** [empty ()] returns an empty arrangement *)
val empty : unit -> 'a t

(** [add_elem arr a] insert a single element in the arrangement [arr]
    without any restriction *)
val add_elem : 'a t -> 'a -> unit

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

(** [gen_arrtrees arr] returns a list with all possible arrangement trees
    that can be generated from [arr] *)
val gen_arrtrees : 'a t -> 'a arrtree list

(** [arrtree_to_set tree] returns a set with all possible branches in [tree] *)
val arrtree_to_set : 'a arrtree -> ('a list list) LeapGenericSet.t

(** [gen_arrs arr] returns a set of list containing all possible arrangements.
    Each list represents a decreasing ordering of equivalences classes
    according to arrangement [arr]. Each equivalence class is represented as
    a list of elements *)
val gen_arrs : 'a t -> ('a list list) LeapGenericSet.t

(** [arrtree_set_to_str f s] generates a string representing all possible
    arrangements is set [s] using function [f] to represent each element *)
val arrtree_set_to_str : ('a -> string) -> ('a list list) LeapGenericSet.t ->
                         string

(** [arrtree_to_str f tree] returns a string representing [tree], using
    function [f] to represent each element *)
val arrtree_to_str : ('a -> string) -> 'a arrtree -> string
