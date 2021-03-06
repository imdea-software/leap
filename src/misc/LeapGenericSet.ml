
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



(* The type of generic sets *)
type 'a t = {
              elems : ('a, unit) Hashtbl.t;
              counter : int ref;
            }

(* Special set operation *)
let empty () : 'a t =
  {
   elems = Hashtbl.create 10;
   counter = ref 0;
  }


let equal (s1:'a t) (s2:'a t) : bool =
  if s1.counter <> s2.counter then
    false
  else begin
    try
      Hashtbl.iter (fun x _ -> ignore (Hashtbl.find s2.elems x)) s1.elems;
      true
    with Not_found -> false
  end


let clear (s:'a t) : unit =
  Hashtbl.clear s.elems;
  s.counter := 0


let copy (s:'a t) : 'a t =
  {
    elems = Hashtbl.copy s.elems;
    counter = ref !(s.counter);
  }


let add (s:'a t) (a:'a) : unit =
  if not (Hashtbl.mem s.elems a) then
    begin
      incr s.counter; Hashtbl.add s.elems a ()
    end


let remove (s:'a t) (a:'a) : unit =
  if Hashtbl.mem s.elems a then
    begin
      decr s.counter; Hashtbl.remove s.elems a
    end


let singleton (a:'a) : 'a t =
  let s = empty () in
  let _ = add s a in
    s


let size (s:'a t) : int =
  !(s.counter)


let mem (s:'a t) (a:'a) : bool =
  Hashtbl.mem s.elems a


let iter (f:'a -> unit) (s:'a t) : unit =
  Hashtbl.iter (fun e _ -> f e) s.elems


let fold (f:'a -> 'b -> 'b) (s:'a t) (init:'b) : 'b =
  Hashtbl.fold (fun e _ tmp -> f e tmp) s.elems init


let union (s:'a t) (r:'a t) : 'a t =
  if s.counter < r.counter then
    let s_new = copy r in
    let _ = iter (add s_new) s in
      s_new
  else
    let s_new = copy s in
    let _ = iter (add s_new) r in
      s_new


let inter (s:'a t) (r:'a t) : 'a t =
  let s_new = empty () in
  if s.counter < r.counter then
    let _ = iter (fun e -> if mem r e then add s_new e) s in
      s_new
  else
    let _ = iter (fun e -> if mem s e then add s_new e) r in
      s_new


let diff (s:'a t) (r:'a t) : 'a t =
  let s_new = empty () in
  iter (fun e -> if not (mem r e) then add s_new e) s;
  s_new


let from_list (xs:'a list) : 'a t =
  let s = empty () in
  let _ =  List.iter (fun e -> add s e) xs in
    s


let to_list (s:'a t) : 'a list =
  fold (fun e xs -> e :: xs) s []


let exists (f:'a -> bool) (s:'a t) : bool =
  List.exists f (to_list s)


let for_all (f:'a -> bool) (s:'a t) : bool =
  List.for_all f (to_list s)


let subseteq (s:'a t) (r:'a t) : bool =
  for_all (mem r) s


let copy_without (s:'a t) (ss:'a t list) : 'a t =
  let s_new = empty () in
  let _ = iter (fun e ->
            if not (List.exists (fun x -> mem x e) ss) then
              add s_new e
          ) s in
    s_new


let to_str (f:'a -> string) (s:'a t) : string =
  "{" ^(String.concat ";" (fold (fun e xs -> (f e)::xs) s []))^ "}"
