
(* The type of generic sets *)
type 'a t


(** [empty ()] creates a new empty set *)
val empty : unit -> 'a t

(** [clear s] removes all elements stored in [s] *)
val clear : 'a t -> unit

(** [equal s1 s2] returns [true] if sets [s1] and [s2] contains the
    same elements *)
val equal : 'a t -> 'a t -> bool

(** [copy s] returns a new copy of set [s] *)
val copy : 'a t -> 'a t

(** [add s a] adds to set [s] element [a] *)
val add : 'a t -> 'a -> unit

(** [remove s a] removes element [a] from set [s] *)
val remove : 'a t -> 'a -> unit

(** [singleton a] creates a new set containing just [a] *)
val singleton : 'a -> 'a t

(** [size s] returns the number of elements in set [s] *)
val size : 'a t -> int

(** [mem s a] returns [true] if element [a] is in set [s]. Otherwise [false] *)
val mem : 'a t -> 'a -> bool

(** [subseteq s r] returns [true] if all elements in [s] are contained into [r].
    Otherwise it returns [false] *)
val subseteq : 'a t -> 'a t -> bool

(** [iter f s] applies [f] in turn to all elements of [s] *)
val iter : ('a -> unit) -> 'a t -> unit

(** [fold f s init] computes [(f eN ... (f e1 init)...)], where [e1 ... eN] are
    the elements in set [s] *)
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(** [union s1 s2] returns the set resulting from the union of [s1] and [s2] *)
val union : 'a t -> 'a t -> 'a t

(** [inter s1 s2] returns the set resulting from the intersection between
    [s1] and [s2] *)
val inter : 'a t -> 'a t -> 'a t

(** [from_list xs] generates a new set from the elements in list [xs] *)
val from_list : 'a list -> 'a t

(** [to_list s] generates a list containing all elements in [s] *)
val to_list : 'a t -> 'a list

(** [exists f s] determines whether there exists an element in [s] for which
    function [f] returns [true] *)
val exists : ('a -> bool) -> 'a t -> bool

(** [for_all f s] determines whether for all element in [s], function [f]
    returns [true] *)
val for_all : ('a -> bool) -> 'a t -> bool

(** [copy_without s ss] returns a set that is a copy of set [s], but excluding
    all elements from any of the sets in [ss] *)
val copy_without : 'a t -> 'a t list -> 'a t

(** [to_str f s] returns a string representing set [s], using function [f]
    to represent each element *)
val to_str : ('a -> string) -> 'a t -> string
