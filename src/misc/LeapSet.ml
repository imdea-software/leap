
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


(******************************************************************************)
(* @file LeapSet.mli                                                          *)
(* Custom definition of Sets                                                  *)
(*                                                                            *)
(******************************************************************************)


module T = RoundedTable

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module type S =
  sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val max_elt: t -> elt
    val choose: t -> elt
    val split: elt -> t -> t * bool * t
  end

module Make(Ord: OrderedType) = Set.Make(Ord)

module MakeImperative(Ord : OrderedType) = Set.Make(Ord)

module MakeImperative2(Ord : OrderedType) = struct
  type elt = Ord.t
    
  type t = Empty | Set of (elt,bool) T.table
  
  let wrap_tbl t = if T.length t = 0 then Empty else Set t
    
  (** Set operations *)
  let empty = Empty
  
  let is_empty s = s = Empty
  
  let mem x s = match s with
    | Empty -> false
    | Set t -> (match T.find t x with
      | None -> false
      | Some _ -> true)
  
  let add x s = match s with
    | Empty -> let t = T.create () in ignore(T.insert t (x,true)); Set t
    | Set t -> let t' = (*T.copy*) t in ignore(T.insert t' (x,true)); Set t'
    
  let singleton x = 
    let t = T.create () in ignore(T.insert t (x,true)); Set t
    
  let remove x s = match s with
    | Empty -> Empty
    | Set t -> wrap_tbl (T.key_filter (fun k -> not(k=x)) t)
  
  let union s s' = match s,s' with
    | Empty, _ -> s'
    | _, Empty -> s
    | Set t, Set t' -> 
        let st, st' = if T.length t < T.length t' 
          then T.copy t, t' else T.copy t',t in
        wrap_tbl (T.insert_table st st')
    
  let inter s s' = match s,s' with
    | Empty, _ -> Empty
    | _, Empty -> Empty
    | Set t, Set t' -> 
        let st, st' = if T.length t < T.length t' 
          then t, t' else t',t in
        wrap_tbl (T.key_filter (fun x -> mem x (Set st')) st)
    
  let diff s s' = match s,s' with
    | Empty, _ -> Empty
    | _, Empty -> s
    | Set t, Set t' -> 
        wrap_tbl (T.key_filter (fun x -> not (mem x (Set t'))) t)
    
  let compare = Pervasives.compare
     
  let equal s s' = (s = s')
  
  let subset s s' = match s,s' with
    | Empty, _ -> true
    | _, Empty -> false
    | Set t, Set t' -> 
        if T.length t > T.length t' then false
        else T.length (T.key_filter (fun x -> mem x (Set t')) t) = T.length t
      
  let iter f s = match s with
    | Empty -> ()
    | Set t -> T.apply (fun x _ -> f x) t
  
  let fold f s z = match s with
    | Empty -> z
    | Set t -> T.fold (fun x _ -> f x) t z
  
  exception FalseForall
  let for_all f s = match s with
    | Empty -> true
    | Set t -> try
        T.apply (fun x _ -> if not (f x) then raise(FalseForall) else ()) t;
        true with _ -> false
    
  exception TrueExists
  let exists f s = match s with
    | Empty -> false
    | Set t -> try
        T.apply (fun x _ -> if f x then raise(TrueExists) else ()) t;
        false with _ -> true
        
  let filter f s = match s with
    | Empty -> Empty
    | Set t -> wrap_tbl (T.key_filter f t)
  
  let partition f s = match s with
    | Empty -> (Empty,Empty)
    | Set t -> let st,st' = T.create (), T.create () in
        T.apply (fun x _ -> 
          ignore (if f x then T.insert st (x,true) 
            else T.insert st' (x,true))) t; 
        (wrap_tbl st, wrap_tbl st')
        
  let cardinal = function
    | Empty -> 0
    | Set t -> T.length t
  
  let elements = function
    | Empty -> []
    | Set t -> T.keys t
  
  exception Elt of elt
  exception InternalError of string*int
  let choose = function
    | Empty -> raise(Not_found)
    | Set t -> let xs = try T.fold (fun x _ xs -> raise(Elt x)) t []
                        with Elt x -> [x] in
        let xs = try T.fold (fun x _ xs -> raise(Elt x)) t []
                 with Elt x -> [x] in
        match xs with
          | []   -> raise(InternalError(__file__,__line__))
          | x::l -> x
  
  let min_elt s = match s with
    | Empty -> raise(Not_found)
    | Set t -> let min = choose s in
        T.fold (fun x _ m -> if Ord.compare x m < 0 then x else m) t min
        
  let max_elt s = match s with
    | Empty -> raise(Not_found)
    | Set t -> let min = choose s in
        T.fold (fun x _ m -> if Ord.compare x m > 0 then x else m) t min
        
  let split x s = match s with
    | Empty -> (Empty, false, Empty)
    | Set t -> 
        let lt,geq = partition (fun y -> Ord.compare y x < 0) s in
        match geq with
          | Empty -> lt, false, Empty
          | Set t' -> (match T.remove t' x with
            | None   -> lt, false, Set t'
            | Some _ -> lt, true, Set t')  
end
