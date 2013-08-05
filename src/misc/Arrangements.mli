
(** The type of an arrangement *)
type 'a t

(** The type of arrangements tree *)
type 'a arrtree = Node of 'a list * 'a arrtree list

(** [empty stc] returns an empty arrangement. [stc] sets strict mode. If strict
    mode is enabled, then elements of the domain must be declared before
    they can be part of a relation. If no strict mode is enabled, then
    relations can add elements to the domain if they have not been previously
    added. *)
val empty : bool -> 'a t

(** [equal arr1 arr2] returns [true] if arrangements [arr1] and [arr2]
    contains the same information *)
val equal : 'a t -> 'a t -> bool

(** [copy arr] returns a duplicate of arrangement [arr] *)
val copy : 'a t -> 'a t

(** [clear arr] clears all information contained into [arr] *)
val clear : 'a t -> unit

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
    arrangement [arr]. Same result as invoking [add_less arr a b] *)
val add_order : 'a t -> 'a -> 'a -> unit

(** [add_less arr a b] inserts an order relation between [a] and [b] into the
    arrangement [arr], stating that [a] is strictly lower than [b] *)
val add_less : 'a t -> 'a -> 'a -> unit

(** [add_greater arr a b] inserts an order relation between [a] and [b] into the
    arrangement [arr], stating that [a] is strictly greater than [b] *)
val add_greater : 'a t -> 'a -> 'a -> unit

(** [add_lesseq arr a b] inserts an order relation between [a] and [b] into the
    arrangement [arr], stating that [a] is lower or equal than [b] *)
val add_lesseq : 'a t -> 'a -> 'a -> unit

(** [add_greatereq arr a b] inserts an order relation between [a] and [b] into the
    arrangement [arr], stating that [a] is greater or equal than [b] *)
val add_greatereq : 'a t -> 'a -> 'a -> unit

(** [add_followed_by arr a b] adds to arrangement [arr] the information that
    element [a] should be immediately followed by element [b] *)
val add_followed_by : 'a t -> 'a -> 'a -> unit

(** [set_minimum arr a] forces [a] to be the minimum element in arrangement
    [arr] *)
val set_minimum : 'a t -> 'a -> unit

(** [to_str arr] returns a string with the equalities, inequalities and order
    relation within the arrangement *)
val to_str : 'a t -> ('a -> string) -> string

(** [gen_arrtrees arr] returns a list with all possible arrangement trees
    that can be generated from [arr] *)
val gen_arrtrees : ('a -> string) -> 'a t -> 'a arrtree list

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



val test : 'a t -> ('a -> string) -> unit
