
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


(***********************************************************************)
(*                                                                     *)
(* Type definitions                                                    *)
(*                                                                     *)
(* @authors Julian Samborski-Forlese                                   *)
(* @version 0.1.0                                                      *)
(* @since 2011/08/15                                                   *)
(*                                                                     *)
(***********************************************************************)
type ('a,'b) table

val create : unit -> ('a,'b) table
val copy : ('a,'b) table -> ('a,'b) table
val insert : ('a,'b) table -> 'a * 'b -> 'b option
val find : ('a,'b) table -> 'a -> 'b option
val remove : ('a,'b) table -> 'a -> 'b option
val replace : ('a,'b) table -> 'a*'b -> 'b option
val find_value : ('a,'b) table -> ('b -> bool) -> 'a option
val map : ('b -> 'c) -> ('a,'b) table -> ('a,'c) table
val fold : ('a -> 'b -> 'c -> 'c) -> ('a,'b) table -> 'c -> 'c
val apply : ('a -> 'b -> unit) -> ('a,'b) table -> unit
val merge : ('b->'b->'b) -> ('a,'b) table -> ('a,'b) table -> ('a,'b) table
val insert_table : ('a, 'b) table -> ('a, 'b) table -> ('a, 'b) table
val insert_list : ('a, 'b) table -> ('a * 'b) list -> ('a, 'b) table
val remove_list : ('a, 'b) table -> 'a list -> ('a,'b) table
val to_list : ('a, 'b) table -> ('a * 'b) list 
val from_list : ('a * 'b) list -> ('a, 'b) table
val filter : ('b -> bool) -> ('a, 'b) table -> ('a, 'b) table
val key_filter : ('a -> bool) -> ('a, 'b) table -> ('a, 'b) table
val keys : ('a, 'b) table -> 'a list
val values : ('a, 'b) table -> 'b list
val length : ('a, 'b) table -> int
