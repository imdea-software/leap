(******************************************************************************)
(* @file RoundedTypes                                                         *)
(* Type definitons                                                            *)
(*                                                                            *)
(* @authors Julian Samborski-Forlese                                          *)
(* @version 0.1.0                                                             *)
(* @since 2011/08/15                                                          *)
(*                                                                            *)
(******************************************************************************)
module H = Hashtbl

type ('a, 'b) table = ('a, 'b) H.t
  
let create () = H.create 100

let copy t = H.copy t
  (*let t' = create () in
  H.iter (fun x -> H.add t' x) t; t'*)
  
let insert t (x,y) = 
  try let y' = H.find t x in Some y' 
  with Not_found -> H.add t x y; None
    
let find t x = 
  try let y = H.find t x in Some y
  with Not_found -> None

let remove t x = 
  try let y = H.find t x in H.remove t x; Some y
  with Not_found -> None

let replace t (x,y) = 
  try let y' = H.find t x in H.replace t x y; Some y'
  with Not_found -> H.replace t x y; None
  
let find_value t p =
  let found = ref None in
  H.iter (fun x y -> 
    match !found with
      | None -> if p y then found := Some x
      | Some _ -> ()) t;
  !found

let map f t =
  let t' = create() in
  H.iter (fun x y -> H.add t' x (f y)) t;t'

let fold = H.fold

let apply f t = H.iter f t

let merge f t t' =
  let mrg t1 t2 =
    H.iter (fun x y -> try
      let y' = H.find t2 x in
      H.replace t2 x (f y y')
      with Not_found -> H.add t2 x y) t1 in
   if H.length t <= H.length t' then (mrg t t'; t') 
   else (mrg t' t; t)

let insert_table t t' =
  H.iter (fun x y -> ignore (insert t (x,y))) t'; t
    
let insert_list t l = 
  List.iter (fun (x,y) -> ignore (insert t (x,y))) l; t

let remove_list t l =
  List.iter (fun x -> try H.remove t x with _ -> ()) l; t

let to_list t =
  H.fold (fun x y l -> (x,y) :: l ) t []

let from_list l =
  let t = create() in insert_list t l

let filter p t = 
  let t' = create() in
  H.iter (fun x y -> if p y then H.add t' x y) t;
  t'

let key_filter p t =
  let t' = create() in
  H.iter (fun x y -> if p x then H.add t' x y) t;
  t'
    
let keys t =
  H.fold (fun x y l -> x :: l) t []

let values t =
  H.fold (fun x y l -> y :: l) t []

let length = H.length

