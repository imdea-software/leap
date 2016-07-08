
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)



(** The type of a partition *)
type 'a t

(** The type of equivalence classes identifier *)
type id = int

(** The type of equalities and inequalities *)
type 'a eqs = Eq of ('a * 'a) | Ineq of ('a * 'a)

(** Inconsistent inequality between two elements was found
    after an equality between them *)
exception Inconsistent_inequality


val empty : unit -> 'a t
(** [empty] returns an empty partition *)

val copy : 'a t -> 'a t
(** [copy p] returns a copy of partition [p] *)

val id : 'a t -> 'a -> id
(** [id p a] returns the identifier of the equivalence class where [a]
    belongs in [p]. Raises [Not_found] if [a] is not in [p] *)

val elems : 'a t -> id -> 'a list
(** [elems p i] returns the list of elements in [p] belonging to
    equivalence class identified with [i] *)

val size : 'a t -> int
(** [size p] returns the number of equivalence classes in partition [p] *)

val elems_with : 'a t -> 'a -> 'a list
(** [elems_with p a] returns the list of elements in [p] belonging to
    the same equivalence class as [a] *)

val add_new : 'a t -> 'a -> id
(** [add_new p a] add to partition [p] a new equivalence class containing only
    element [a]. It returns the identifier of the new created equivalence
    class *)

val add_to : 'a t -> 'a ->  id -> id
(** [add_to p a i] adds to partition [p] element [a] in the equivalence
    class identified with [i]. If [a] was already present in [p], then
    the equivalence class of [a] is unified to the one identified
    with [i]. If [i] is a identifier that has not been defined in [p],
    then [a] is added in an independent equivalence class. The function
    returns the identifier of the equivalence class where [a] was finally
    inserted *)

val add_new_class : 'a t -> 'a list -> id
(** [add_new_class p cs] adds into partition [p] all elements in [cs] as
    a completely new equivalence class. It returns the equivalence class
    identifier of the created class. If the list is empty, no equivalence
    class is created and -1 is returned. *)

val add_with : 'a t -> 'a -> 'a -> id
(** [add_with p a b] adds in partition [p], the element [a] in the same
    equivalence class as [b]. If [a] was already in [p], then both equivalence
    classes are unified. If [b] is not in [p], then a new equivalence class is
    created for [a]. The function returns the identifier of the equivalence
    class where [a] was finally inserted *)

val add_eq : 'a t -> 'a -> 'a -> unit
(** [add_eq p a b] adds to partition [p] an equality between elements [a] and
    [b]. Equivalence classes are created and/or unified id required *)


val singleton : 'a -> 'a t
(** [singleton a] returns a new partition with a single equivalence class
    containing the single element [a] *)

val keys : 'a t -> id list
(** [keys p] returns the list of equivalence class identifiers defined in
    [p] *)

val to_list : 'a t -> 'a list list
(** [to_list p] returns a list representations of all equivalence classes
    in partition [p] *)

val gen_init_partitions : 'a list -> 'a eqs list -> 'a t
(** [gen_init_partitions d as] generates the initial partition of equivalence
    classes considering only elements in domain [d] and the list of assumptions
    [as] *)

val gen_partitions : 'a list -> 'a eqs list -> ('a t) list
(** [gen_partitions d as] generates all possible partitions of equivalence
    classes using elements in domain [d] and starting from the list of
    assumptions [as] *)

val eqs_to_str :  ('a -> string) -> 'a eqs -> string
(** [eqs_to_str f eq] returns a string representing the equality or inequality
    described by [eq] using function [f] to find a string representation of
    elements in such relation *)


val assumptions_to_str : ('a -> string) -> 'a eqs list -> string
(** [assumptions_to_str f eqs] returns a string representing the equalities and
    inequalities in list [eqs] using function [f] to represent the elements in
    the relation *)


val to_str : ('a -> string) -> 'a t -> string
(** [to_str p f] returns a string representation of partition [p],
    using function [f] to represent the elements *)
