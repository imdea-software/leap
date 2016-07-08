
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


(** Computation of model sizes. *)

(** All possible sorts for which its domain size can be consulted *)
type dom_t =
  | Int
  | Level
  | Elem
  | Addr
  | Tid


(** The type of a model size record *)
type t

(** [create ()] returns a new empty model size *)
val create : unit -> t

(** [create_with xs] returns a new model size containing as many elements
 *  in each domain as specified by the list given as argument *)
val create_with : (dom_t * int) list -> t

(** [get ms d] returns the size of the domain of sort [d] for the
 *  model size [ms] *)
val get : t -> dom_t -> int

(** [set ms d i] sets [i] as the number of elements within the domain [d]
 *  in model [ms] *) 
val set : t -> dom_t -> int -> unit

(** [add ms d i] adds [i] elements to the domain [d] in model [ms] *)
val add : t -> dom_t -> int -> unit

(** [incr ms d] increments in 1 the number of elements in the domain [d]
 *  for model [ms] *)
val incr : t -> dom_t -> unit

(** [max ms d i] checks whether the current value in [ms] for domain [d]
 *  is greater than [i]. If so, it leaves [ms] unchanged, otherwise it
 *  sets[i] as the new size for domain [d] *)
val max : t -> dom_t -> int -> unit

(** [max_of ms1 ms2] adds to [ms1] the information contained into [ms2].
 *  At the end, each domain in [ms1] contains the higher value for such
 *  domain initially stored in [ms1] or [ms2] *)
val max_of : t -> t -> unit

(** [to_str ms] returns a string representing the model *)
val to_str : t -> string
