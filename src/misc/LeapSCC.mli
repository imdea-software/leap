
(** [scc g] returns a list with all strongly connected components in [g] *)
val scc : ('a,'a LeapGenericSet.t) Hashtbl.t -> 'a list list

(** [has_cycles g] determines whether there are cycles in [g] *)
val has_cycles : ('a,'a LeapGenericSet.t) Hashtbl.t -> bool
