
module H = Hashtbl


type ('a,'b) t =
  {
    mutable map : ('a, 'b) H.t ;
    mutable rev : ('b, 'a list) H.t ;
  }


let create (n:int) : ('a, 'b) t =
  {
    map = H.create 10;
    rev = H.create 10;
  }


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
  if H.mem idmap.rev old_b then
    let to_modify = H.find idmap.rev old_b in
    let _ = List.iter (fun x -> H.replace idmap.map x new_b) to_modify
    in
      ()
  else
    ()


let iter (f:('a -> 'b -> unit)) (idmap:('a,'b)t) : unit =
  H.iter f idmap.map


let fold (f:('a -> 'b -> 'c -> 'c)) (idmap:('a,'b)t) (init:'c) : 'c =
  H.fold f idmap.map init
