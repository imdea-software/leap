
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



module type PoolType =
  sig
    type t
    val compare : t -> t -> int
  end

module type S =
  sig
    type elt
    type t

    val empty : t
    val tag   : t -> elt -> int
  end

module Make(PType: PoolType) =
  struct
    type elt = PType.t
    type t = (elt, int) Hashtbl.t

    let empty : t =
      Hashtbl.create 30

    let tag (p:t) (e:elt) : int =
      if Hashtbl.mem p e then
        Hashtbl.find p e
      else
        let c = Hashtbl.length p in
        let _ = Hashtbl.add p e c in
          c
  end
