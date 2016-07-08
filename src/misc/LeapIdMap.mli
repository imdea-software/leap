
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


type ('a,'b) t

val create : int -> ('a,'b) t
val is_empty : ('a,'b) t -> bool
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
val union : ('a,'b) t -> ('a, 'b) t -> ('a, 'b) t
