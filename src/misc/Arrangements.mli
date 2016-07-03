

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

(** [get_domain arr] returns the domain of elements of the arrangement *)
val get_domain : 'a t -> 'a LeapGenericSet.t

(** [get_eqs arr] returns set of equalities declared inside the
    arrangement. *)
val get_eqs : 'a t -> ('a * 'a) LeapGenericSet.t

(** [get_ineqs arr] returns set of inequalities declared inside the
    arrangement. *)
val get_ineqs : 'a t -> ('a * 'a) LeapGenericSet.t

(** [get_order arr] returns a hash table containing the order relation
    between elements inside the arrangement. An entry ([a],[b]) in the hash
    table states that element [a] is strictly lower than element [b]. *)
val get_order : 'a t -> ('a, 'a) Hashtbl.t

(** [get_succ arr] returns a hash table describing the relation "successor
    of" between elements contained in the arrangement. An entry ([a],[b]) in
    the hash table states that element [b] is the immediate successor of
    element [a] in arrangement [arr]. *)
val get_succ : 'a t -> ('a, 'a) Hashtbl.t

(** [get_leq arr] returns the list of pairs of elements related by the
    "lower or equal" relation. A pair ([a],[b]) in the returned list states
    that "element [a] is lower than or equal to element [b]". *)
val get_leq : 'a t -> ('a * 'a) list

(** [get_minimum arr] returns the element from arrangement [arr] which
    is marked as the minimum element in [arr]. *)
val get_minimum : 'a t -> 'a option

(** [equal arr1 arr2] returns [true] if arrangements [arr1] and [arr2]
    contains the same information *)
val equal : 'a t -> 'a t -> bool

(** [copy arr] returns a duplicate of arrangement [arr] *)
val copy : 'a t -> 'a t

(** [convert f arr] converts the elements in arrangement [arr] into a new
    arrangement using function [f] to perform the conversion. *)
val convert : ('a -> 'b) -> 'a t -> 'b t

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

(** [do_not_consider arr a] indicates arrangement [arr] to not consider any relation
 *  involving element [a] *)
val do_not_consider : 'a t -> 'a -> unit

(** [set_minimum arr a] forces [a] to be the minimum element in arrangement
    [arr] *)
val set_minimum : 'a t -> 'a -> unit

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



val test : 'a t -> ('a -> string) -> unit
