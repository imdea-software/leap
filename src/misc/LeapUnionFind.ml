
module GenSet = LeapGenericSet


(** The type of union-find *)
type 'a t = {
              map : ('a, int) LeapIdMap.t;
              id : int ref;
            }


type id = int

exception Not_in_domain


(* Union-find operations *)

let empty () : 'a t =
  {
    map = LeapIdMap.create 16;
    id = ref 0;
  }


let copy (t:'a t) : 'a t =
  {
    map = LeapIdMap.copy t.map;
    id = ref !(t.id);
  }


let id (t:'a t) (a:'a) : id =
  LeapIdMap.find_id t.map a


let size (t:'a t) : int =
  !(t.id)


let elems (t:'a t) (i:id) : 'a list =
  LeapIdMap.find_dom t.map i


let keys (t:'a t) : id list =
  LeapIdMap.codom t.map


let to_str (f_str:'a -> string) (t:'a t) : string =
  let buf = Buffer.create 256 in
  let t_keys = keys t in
  let _ = List.iter (fun i ->
    Buffer.add_string
      buf ("["^ (String.concat "," (List.map f_str (elems t i))) ^
           "]")
    ) t_keys
  in
    Buffer.contents buf


let elems_with (t:'a t) (a:'a) : 'a list =
  try
    let a_id = LeapIdMap.find_id t.map a in
      LeapIdMap.find_dom t.map a_id
  with _ -> []


let add_new (t:'a t) (a:'a) : id =
  if LeapIdMap.mem t.map a then
    LeapIdMap.find_id t.map a
  else begin
    incr t.id;
    LeapIdMap.add t.map a !(t.id);
    !(t.id)
  end


  (********* Auxiliary functions *********)

let add_to (t:'a t) (a:'a) (i:id) : id =
  try
    let a_id = LeapIdMap.find_id t.map a in
    LeapIdMap.unify_id t.map i a_id;
      a_id
  with _ ->
    if i <= !(t.id) then
      (LeapIdMap.add t.map a i; i)
    else
      add_new t a


let add_with (t:'a t) (a:'a) (b:'a) : id =
  try
    let b_i = LeapIdMap.find_id t.map b in
      add_to t a b_i
  with _ -> add_new t a


let add_new_class (t:'a t) (cs:'a list)  : id =
  match cs with
  | []    -> -1
  | x::xs -> let i = add_new t x in
             let _ = List.iter (fun e -> ignore (add_to t e i)) xs in
               i

  (********* Auxiliary functions *********)

let union (t:'a t) (a:'a) (b:'a) : unit =
  match (LeapIdMap.mem t.map a, LeapIdMap.mem t.map b) with
  | (false, false) -> let a_id = add_new t a in
                        ignore (add_to t b a_id)
  | (true , false) -> ignore (add_with t b a)
  | (false, true ) -> ignore (add_with t a b)
  | (true , true ) -> let a_id = id t a in
                      let b_id = id t b in
                        LeapIdMap.unify_id t.map a_id b_id


let find (t:'a t) (a:'a) : id =
  try
    LeapIdMap.find_id t.map a
  with _ -> raise(Not_in_domain)


let to_list (t:'a t) : 'a list list =
  let ks = keys t in
  List.fold_left (fun xs i ->
    (elems t i) :: xs
  ) [] ks


let from_list (xs:'a list list) : 'a t =
  let t = empty() in
  List.iter (fun cs ->
    ignore (add_new_class t cs)
  ) xs;
  t


let gen_sets (t:'a t) : 'a GenSet.t list=
  List.fold_left (fun xs i ->
    (GenSet.from_list (LeapIdMap.find_dom t.map i)) :: xs
  ) [] (LeapIdMap.codom t.map)

