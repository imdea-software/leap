open LeapLib


type 'a set_t = {
                  elems : ('a, unit) Hashtbl.t;
                  counter : int ref;
                }


type 'a ineq_table_t = ('a, 'a set_t) Hashtbl.t


(** The type of a partition *)
type 'a t = {
              eq_classes : ('a, int) LeapIdMap.t;
              ineqs : (int, 'a LeapBitSet.t * 'a LeapBitSet.t) Hashtbl.t;
              id : int ref;
            }


type id = int


type 'a eqs = Eq of ('a * 'a) | Ineq of ('a * 'a)


exception Not_in_domain
exception Inconsistent_inequality


(* A set for the keys identifying each equivalence class *)
module IntSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = int
  end )

(* Special set operation *)
let set_new () : 'a set_t =
  {
   elems = Hashtbl.create 10;
   counter = ref 0;
  }


let set_add (s:'a set_t) (a:'a) : unit =
  if not (Hashtbl.mem s.elems a) then
    begin
      incr s.counter; Hashtbl.add s.elems a ()
    end


let set_singleton (a:'a) : 'a set_t =
  let s = set_new () in
  let _ = set_add s a in
    s


let set_size (s:'a set_t) : int =
  !(s.counter)


let set_in (s:'a set_t) (a:'a) : bool =
  Hashtbl.mem s.elems a


let set_iter (f:'a -> unit) (s:'a set_t) : unit =
  Hashtbl.iter (fun e _ -> f e) s.elems


let set_union (s:'a set_t) (r:'a set_t) : 'a set_t =
  if s.counter < r.counter then
    let _ = set_iter (set_add r) s in
    let _ = r.counter := Hashtbl.length s.elems in
      r
  else
    let _ = set_iter (set_add s) r in
    let _ = s.counter := Hashtbl.length r.elems in
      s


let set_copy_without (s:'a set_t) (ss:'a set_t list) : 'a set_t =
  let s_new = set_new () in
  let _ = set_iter (fun e ->
            if not (List.exists (fun x -> set_in x e) ss) then
              set_add s_new e
          ) s in
    s_new


let gen_set (xs:'a list) : 'a set_t =
  let s = set_new () in
  let _ =  List.iter (fun e -> set_add s e) xs in
    s


let gen_set_from_pairs (xs:('a*'a) list) : 'a set_t =
  let s = set_new () in
  let _ = List.iter (fun (e1,e2) -> set_add s e1; set_add s e2) xs in
    s


(* Partition operations *)

let empty () : 'a t =
  {
    eq_classes = LeapIdMap.create 10;
    id = ref 0;
    ineqs = Hashtbl.create 10;
  }

let copy (p:'a t) : 'a t =
  {
    eq_classes = LeapIdMap.copy p.eq_classes;
    id = ref !(p.id);
    ineqs = Hashtbl.copy p.ineqs;
  }


let id (p:'a t) (a:'a) : id =
  LeapIdMap.find_id p.eq_classes a


let elems (p:'a t) (i:id) : 'a list =
  LeapIdMap.find_dom p.eq_classes i


let size (p:'a t) : int =
  !(p.id)


let elems_with (p:'a t) (a:'a) : 'a list =
  try
    let a_id = LeapIdMap.find_id p.eq_classes a in
      LeapIdMap.find_dom p.eq_classes a_id
  with _ -> []


let add_new (p:'a t) (a:'a) : id =
  let _ = incr p.id in
  let _ = LeapIdMap.add p.eq_classes a !(p.id) in
    !(p.id)


let add_to (p:'a t) (a:'a) (i:id) : id =
  try
    let a_id = LeapIdMap.find_id p.eq_classes a in
    let _ = LeapIdMap.unify_id p.eq_classes i a_id in
      a_id
  with _ ->
    if i <= !(p.id) then
      let _ = LeapIdMap.add p.eq_classes a i in i
    else
      add_new p a

(** [add_class_to_plus p xs fr en i] adds to partition [p] all elements in
    list [xs] inside the equivalence class identified with [i]. It also adds
    the bitset [fr] as members of the equivalence class and [en] as the bitset
    denoting the elements to which they keep inequalities. It does not perform
    any verification, and thus, assumes that the given equivalence class
    identifier [i] is a valid one *)
let add_class_to_plus (p:'a t) (xs:'a list)
                      (fr:'a LeapBitSet.t) (en:'a LeapBitSet.t) (i:id) : unit =
  begin
    assert (i <= !(p.id));
    List.iter (fun e -> LeapIdMap.add p.eq_classes e i) xs;
    Hashtbl.replace p.ineqs i (fr,en)
  end


let add_new_class (p:'a t) (cs:'a list)  : id =
  match cs with
  | []    -> -1
  | x::xs -> let i = add_new p x in
             let _ = List.iter (fun e -> ignore (add_to p e i)) xs in
               i


let add_new_class_plus (p:'a t) (cs:'a list) (fr:'a LeapBitSet.t) (en:'a LeapBitSet.t) : id =
  let i = add_new_class p cs in
  let _ = if (i <> -1) then
            Hashtbl.replace p.ineqs i (fr,en) in
    i


let add_with (p:'a t) (a:'a) (b:'a) : id =
  try
    let b_i = LeapIdMap.find_id p.eq_classes b in
    let _ = add_to p a b_i in
      b_i
  with _ -> add_new p a


let add_eq (p:'a t) (a:'a) (b:'a) : unit =
  match (LeapIdMap.mem p.eq_classes a, LeapIdMap.mem p.eq_classes b) with
  | (false, false) -> let a_id = add_new p a in
                        ignore (add_to p b a_id)
  | (true , false) -> ignore (add_with p b a)
  | (false, true ) -> ignore (add_with p a b)
  | (true , true ) -> let a_id = id p a in
                      let b_id = id p b in
                        LeapIdMap.unify_id p.eq_classes a_id b_id


let singleton (a:'a) : 'a t =
  let emp = empty () in
  let _ = add_new emp a in
    emp


let keys (p:'a t) : id list =
  LeapIdMap.codom p.eq_classes


let get_bitsets (p:'a t) (i:id) : ('a LeapBitSet.t * 'a LeapBitSet.t) option =
  try
    Some (Hashtbl.find p.ineqs i)
  with _ -> None


let to_list (p:'a t) : 'a list list =
  let ks = keys p in
  List.fold_left (fun xs i ->
    (elems p i) :: xs
  ) [] ks


let to_full_list (p:'a t) : ('a list * 'a LeapBitSet.t * 'a LeapBitSet.t) list =
  let ks = keys p in
  List.fold_left (fun xs k ->
    match (get_bitsets p k) with
    | None -> (elems p k, LeapBitSet.empty 1, LeapBitSet.empty 1) :: xs
    | Some (fr,en) -> (elems p k, fr, en) :: xs
  ) [] ks


let from_list (xs:'a list list) : 'a t =
  let p = empty() in
  let _ = List.iter (fun cs ->
            ignore (add_new_class p cs)
          ) xs in
    p

(*
let rec gen_eq_classes (xs:'a list) : ('a t) list =
  match xs with
  | []    -> []
  | y::[] -> let p = singleton y in [p]
  | y::ys -> let p_list = gen_eq_classes ys
             in
               List.fold_left (fun zs p ->
                 let ks = keys p in
                 let xs' = List.map (fun i ->
                             let p' = copy p in
                             let _ = add_to p' y i in
                               p'
                           ) ks in
                 let p_extra = copy p in
                 let _ = add_new p_extra y
                 in
                   (p_extra :: xs') @ zs
               ) [] p_list
*)

let load_ineq_tbl (dom:'a list) (p:'a t) (tbl:'a ineq_table_t) : unit =
  (* I create a map for elements in the domain *)
  let dom_size = List.length dom in
  let id_map = Hashtbl.create dom_size in
  let counter = ref 0 in
  let _ = List.iter (fun e ->
            Hashtbl.replace id_map e (!counter); incr counter
          ) dom in
  (* Label with bitsets all equivalence classes in the initial partition *)
  let ks = keys p in
  List.iter (fun k ->
    let ds = elems p k in
    let friends = LeapBitSet.empty dom_size in
    let enemies = LeapBitSet.empty dom_size in
    List.iter (fun e ->
      let _ = LeapBitSet.add (Hashtbl.find id_map) friends e in
      (* The EC may not have inequalities, so no set may be returned *)
      try
        let ineq_set = Hashtbl.find tbl e in
        set_iter (fun i->LeapBitSet.add (Hashtbl.find id_map) enemies i) ineq_set
      with _ -> ()
    ) ds;
    if not (LeapBitSet.disjoint friends enemies) then
      raise Inconsistent_inequality;
      Hashtbl.replace p.ineqs k (friends, enemies)
  ) ks


let rec gen_eq_classes (xs:('a list * 'a LeapBitSet.t * 'a LeapBitSet.t) list) : ('a t) list =
  match xs with
  | []          -> []
  | (c,f,e)::[] -> let p = empty () in
                   let _ = add_new_class_plus p c f e in
                     [p]
  | (c,f,e)::cs -> let p_list = gen_eq_classes cs
                   in
                     List.fold_left (fun zs p ->
                       let ks = keys p in
                       let xs' = List.fold_left (fun xs k ->
                                   match get_bitsets p k with
                                   | None ->
                                       let p' = copy p in
                                       let _ = add_class_to_plus p' c f e in
                                         p' :: xs
                                   | Some (k_fr,k_en) ->
                                       if LeapBitSet.disjoint k_fr e then
                                         let p' = copy p in
                                         let new_fr = LeapBitSet.union k_fr f in
                                         let new_en = LeapBitSet.union k_en e in
                                         let _ = add_class_to_plus p' c new_fr new_en k in
                                           p' :: xs
                                       else
                                         xs
                                 ) [] ks in
                       let p_extra = copy p in
                       let _ = add_new_class_plus p_extra c f e
                       in
                         (p_extra :: xs') @ zs
                     ) [] p_list


let check_in_dom (s:'a set_t) (a:'a) : unit =
  if not (set_in s a) then
    raise (Not_in_domain)


let check_inconsistent (a:'a) (b:'a) : unit =
  if a = b then
    raise (Inconsistent_inequality)


let check_no_ineq (tbl: 'a ineq_table_t) (a:'a) (b:'a) : unit =
  try
    let s = Hashtbl.find tbl a in
    if set_in s b then
      raise Inconsistent_inequality
  with _ -> ()


let load_ineq_info (tbl:'a ineq_table_t) (a:'a) (b:'a) : unit =
  try
    let s = Hashtbl.find tbl a in
    let _ = set_add s b in
      Hashtbl.replace tbl a s
  with _ -> Hashtbl.add tbl a (set_singleton b)


let gen_init_partitions (dom:'a list) (assumptions:'a eqs list) : 'a t  =
  let _ = LeapDebug.debug "entering gen_init_partitions...\n" in
  let domSet = gen_set dom in
  (* Split the list of equalities and inequalities *)
  let e_set = set_new () in
  let ineqTbl = Hashtbl.create 100 in
  let (eq,ineq) = List.fold_left (fun (es,is) e ->
                    match e with
                    | Eq (a,b)   -> let _ = check_in_dom domSet a in
                                    let _ = check_in_dom domSet b in
                                    let _ = set_add e_set a in
                                    let _ = set_add e_set b in
                                      ((a,b)::es,is)
                    | Ineq (a,b) -> let _ = check_in_dom domSet a in
                                    let _ = check_in_dom domSet b in
                                    let _ = check_inconsistent a b in
                                    let _ = load_ineq_info ineqTbl a b in
                                    let _ = load_ineq_info ineqTbl b a in
                                      (es,(a,b)::is)
                  ) ([],[]) assumptions in
  (* We create the initial partition with all equalities *)
  let part = empty () in
  let _ = List.iter (fun (a,b) -> add_eq part a b) eq in
  (* We add all remaining domain elements to the initial partition *)
  let rem_set = set_copy_without domSet [e_set] in
  let _ = set_iter (fun e -> ignore(add_new part e)) rem_set in
  (* We load the inequality information *)
  let _ = load_ineq_tbl dom part ineqTbl in
  (* We have the initial partition *)
  let _ = LeapDebug.debug "exiting gen_init_partitions...\n" in
    part


let gen_partitions (dom:'a list) (assumptions:'a eqs list) : ('a t) list =
  let _ = LeapDebug.debug "entering gen_partitions...\n" in
  let part = gen_init_partitions dom assumptions in
  let init_class_list = to_full_list part in
  let ps = gen_eq_classes init_class_list in
  let _ = LeapDebug.debug "exiting gen_partitions...\n" in
    ps


let to_str (p:'a t) (f_str:'a -> string) : string =
  let buf = Buffer.create 256 in
  let p_keys = keys p in
  let _ = List.iter (fun i ->
    Buffer.add_string buf ("["^ (String.concat "," (List.map f_str (elems p i)) ) ^"]")
  ) p_keys
  in
    Buffer.contents buf
