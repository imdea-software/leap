
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



module H = Hashtbl


type ('a,'b) t =
  {
    mutable map : ('a, 'b) H.t ;
    mutable rev : ('b, 'a list) H.t ;
  }


let create (n:int) : ('a, 'b) t =
  {
    map = H.create n;
    rev = H.create n;
  }


let is_empty (idmap:('a,'b)t) : bool =
  H.length idmap.map = 0 && H.length idmap.rev = 0


let clear (idmap:('a,'b)t) : unit =
  let _ = H.clear idmap.map in
  let _ = H.clear idmap.rev
  in
    ()

let copy (idmap:('a,'b)t) : ('a,'b) t =
  {
    map = H.copy idmap.map ;
    rev = H.copy idmap.rev ;
  }


let add (idmap:('a,'b)t) (a:'a) (b:'b) : unit =
  if H.mem idmap.map a then
    begin
      let old_b = H.find idmap.map a
      in
        H.replace idmap.map a b;
        H.replace idmap.rev old_b
                  (List.filter (fun x -> x<>a) (H.find idmap.rev old_b));
        H.replace idmap.rev b (a::(H.find idmap.rev b))
    end
  else
    let _ = H.replace idmap.map a b in
    let old_dom = try
                    H.find idmap.rev b
                  with _ -> [] in
    let _ = H.replace idmap.rev b (a::old_dom)
    in
      ()


let mem (idmap:('a, 'b)t) (a:'a) : bool =
  H.mem idmap.map a


let dom (idmap:('a,'b)t) : 'a list =
  H.fold (fun a _ xs -> a :: xs) idmap.map []


let codom (idmap:('a,'b)t) : 'b list =
  H.fold (fun b _ xs -> b :: xs) idmap.rev []


let find_id (idmap:('a, 'b)t) (a:'a) : 'b =
  H.find idmap.map a


let find_dom (idmap:('a,'b)t) (b:'b) : 'a list =
  H.find idmap.rev b


let dom_size (idmap:('a,'b)t) : int =
  H.length idmap.map


let codom_size (idmap:('a,'b)t) : int =
  H.length idmap.rev


let unify_id (idmap:('a,'b)t) (old_b:'b) (new_b:'b) : unit =
  if (old_b <> new_b) then
    if H.mem idmap.rev old_b then begin
      let to_modify = H.find idmap.rev old_b in
      List.iter (fun x -> H.replace idmap.map x new_b) to_modify;
      H.replace idmap.rev new_b ((H.find idmap.rev new_b) @ to_modify);
      H.remove idmap.rev old_b
    end


let iter (f:('a -> 'b -> unit)) (idmap:('a,'b)t) : unit =
  H.iter f idmap.map


let fold (f:('a -> 'b -> 'c -> 'c)) (idmap:('a,'b)t) (init:'c) : 'c =
  H.fold f idmap.map init


let union (idmap1:('a,'b)t) (idmap2:('a,'b)t) : ('a,'b) t =
  let res_idmap = copy idmap1 in
  iter (add res_idmap) idmap2;
  res_idmap

