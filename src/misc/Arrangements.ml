open LeapLib

module GenSet = LeapGenericSet

(** The type of an arrangement *)
type 'a t = {
              strict            : bool;
              dom               : 'a GenSet.t;
              mutable minimum   : 'a option;
              eqs               : ('a * 'a) GenSet.t;
              ineqs             : ('a * 'a) GenSet.t;
              order             : ('a, 'a) Hashtbl.t;
              succ              : ('a, 'a) Hashtbl.t;
              mutable leq_order : ('a * 'a) list;
            }

type eqclass_order_t = (int,int GenSet.t) Hashtbl.t


(** The type of arrangements tree *)
type 'a arrtree = Node of 'a list * 'a arrtree list

type 'a aux_arrtree = AuxNode of ('a list * bool * 'a aux_arrtree list)

let empty (stc:bool) : 'a t =
  {
    strict = stc;
    dom = GenSet.empty ();
    minimum = None;
    eqs = GenSet.empty ();
    ineqs = GenSet.empty ();
    order = Hashtbl.create 10;
    succ = Hashtbl.create 10;
    leq_order = [];
  }

(* Test equality between arrangements *)
let equal (arr1:'a t) (arr2:'a t) : bool =
  arr1.strict = arr2.strict &&
  GenSet.equal arr1.dom arr2.dom &&
  arr1.minimum = arr2.minimum &&
  GenSet.equal arr1.eqs arr2.eqs &&
  GenSet.equal arr1.ineqs arr2.ineqs &&
  arr1.order = arr2.order &&
  arr1.succ = arr2.succ &&
  List.for_all (fun e -> List.mem e arr2.leq_order) arr1.leq_order &&
  List.for_all (fun e -> List.mem e arr1.leq_order) arr2.leq_order


let copy (arr:'a t) : 'a t =
  {
    strict = arr.strict;
    dom = GenSet.copy arr.dom;
    minimum = arr.minimum;
    eqs = GenSet.copy arr.eqs;
    ineqs = GenSet.copy arr.ineqs;
    order = Hashtbl.copy arr.order;
    succ = Hashtbl.copy arr.succ;
    leq_order = arr.leq_order;
  }


let clear (arr:'a t) : unit =
  GenSet.clear arr.dom;
  arr.minimum <- None;
  GenSet.clear arr.eqs;
  GenSet.clear arr.ineqs;
  Hashtbl.clear arr.order;
  Hashtbl.clear arr.succ;
  arr.leq_order <- []


let add_elem (arr:'a t) (a:'a) : unit =
  GenSet.add arr.dom a


let proceed (arr:'a t) (a:'a) (b:'a) : bool =
  (not arr.strict) || (GenSet.mem arr.dom a && GenSet.mem arr.dom b)


let add_eq (arr:'a t) (a:'a) (b:'a) : unit =
  if proceed arr a b then
    begin
      if not (GenSet.mem arr.eqs (a,b) || GenSet.mem arr.eqs (b,a)) then
        begin
          GenSet.add arr.dom a;
          GenSet.add arr.dom b;
          GenSet.add arr.eqs (a,b)
        end
    end


let add_ineq (arr:'a t) (a:'a) (b:'a) : unit =
  if proceed arr a b then
    begin
      if not (GenSet.mem arr.eqs (a,b) || GenSet.mem arr.eqs (b,a)) then
        begin
          GenSet.add arr.dom a;
          GenSet.add arr.dom b;
          GenSet.add arr.ineqs (a,b)
        end
    end


let add_order (arr:'a t) (a:'a) (b:'a) : unit =
  if proceed arr a b then
    begin
      if not (List.mem b (Hashtbl.find_all arr.order a)) then
        begin
          GenSet.add arr.dom a;
          GenSet.add arr.dom b;
          Hashtbl.add arr.order a b
        end
    end


let add_less (arr:'a t) (a:'a) (b:'a) : unit =
  add_order arr a b


let add_greater (arr:'a t) (a:'a) (b:'a) : unit =
  add_less arr b a


let add_lesseq (arr:'a t) (a:'a) (b:'a) : unit =
  arr.leq_order <- (a,b) :: arr.leq_order


let add_greatereq (arr:'a t) (a:'a) (b:'a) : unit =
  add_lesseq arr b a


let add_followed_by (arr:'a t) (a:'a) (b:'a) : unit =
  if proceed arr a b then
    begin
      if not (List.mem b (Hashtbl.find_all arr.succ a)) then
        begin
          GenSet.add arr.dom a;
          GenSet.add arr.dom b;
          add_less arr a b;
          Hashtbl.add arr.succ a b
        end
    end



let set_minimum (arr:'a t) (a:'a) : unit =
  arr.minimum <- Some a


let rec inject_leq_info (arr:'a t) : ('a t) list =
  let leq_order = arr.leq_order in
  let arr = copy arr in
  arr.leq_order <- [];
  List.fold_left (fun arrs (a,b) ->
    List.fold_left (fun ys ar ->
      let ar1 = copy ar in
      let ar2 = copy ar in
      add_order ar1 a b;
      add_eq ar2 a b;
      ar1 :: ar2 :: ys
    ) [] arrs
  ) [arr] leq_order


let to_str (arr:'a t) (f:'a -> string) : string =
  let dom_list = GenSet.fold (fun e xs -> (f e) :: xs) arr.dom [] in
  let eq_list = GenSet.fold (fun (a,b) xs -> ((f a) ^"="^ (f b)) :: xs) arr.eqs [] in
  let ineq_list = GenSet.fold (fun (a,b) xs -> ((f a) ^"!="^ (f b)) :: xs) arr.ineqs [] in
  let order_list = Hashtbl.fold (fun a b xs -> ((f a) ^"<"^ (f b)) :: xs) arr.order [] in
  let leq_order_list = List.fold_left (fun xs (a,b) -> ((f a) ^"<="^ (f b)) :: xs) [] arr.leq_order in
  let succ_list = Hashtbl.fold (fun a b xs -> ((f a) ^"->"^ (f b)) :: xs) arr.succ [] in
  "Domain : {" ^ (String.concat ";" dom_list) ^ "}\n" ^
  "Minimum: " ^ (Option.map_default f "" arr.minimum) ^ "\n" ^
  "Eqs    : {" ^ (String.concat ";" eq_list) ^ "}\n" ^
  "Ineqs  : {" ^ (String.concat ";" ineq_list) ^ "}\n" ^
  "Order  : {" ^ (String.concat ";" order_list) ^ "}\n" ^
  "<=     : {" ^ (String.concat ";" leq_order_list) ^ "}\n" ^
  "succ   : {" ^ (String.concat ";" succ_list) ^ "}"


let to_id_order (arr:'a t) (p:'a Partition.t) : eqclass_order_t =
  let eqclass_order : eqclass_order_t = Hashtbl.create 10 in
  let eqs = Partition.to_list p in
  List.iter (fun ec ->
    let ec_id = Partition.id p (List.hd ec) in
    let ord_set = List.fold_left (fun s e ->
                    try
                      List.iter (fun x ->
                        GenSet.add s (Partition.id p x)
                      ) (Hashtbl.find_all arr.order e);
                      s
(*                      GenSet.add s (Partition.id p (Hashtbl.find arr.order e));s *)
                    with _ -> s
                  ) (GenSet.empty()) ec in
    Hashtbl.add eqclass_order ec_id ord_set
  ) eqs;
  eqclass_order


let well_defined_order (arr:'a t) (p:'a Partition.t) : bool =
  not (LeapSCC.has_cycles (to_id_order arr p))


let prune_incomplete_tree (t:'a aux_arrtree) : 'a arrtree option =
  let rec f_aux (AuxNode (e,b,xs):'a aux_arrtree) : ('a arrtree * bool) =
    match xs with
    | [] -> (Node (e,[]), b)
    | _  -> begin
              let xs'= List.fold_left (fun ys (t,c) ->
                         if c then t::ys else ys
                       ) [] (List.map f_aux xs) in
              match xs' with
              | [] -> (Node (e,[]) , false)
              | _  -> (Node (e,xs'), true )
            end
  in
  match f_aux t with
  | (new_t, true ) -> Some new_t
  | (_    , false) -> None


let rec build_cand_tree (graph:eqclass_order_t)
                        (follows:(int, int) Hashtbl.t)
                        (initial_elems:int GenSet.t)
                        (all_elems:int GenSet.t)
                        (p:'a Partition.t) : 'a arrtree list =
  let rec build_aux (avail:int GenSet.t) (all_avail:int GenSet.t) : 'a aux_arrtree list =
    GenSet.fold (fun id xs ->
      let codom = try Hashtbl.find graph id with _ -> GenSet.empty () in
      if (GenSet.mem avail id && GenSet.inter codom all_avail = (GenSet.empty ())) then
        begin
          let all_avail' = GenSet.copy all_avail in
          GenSet.remove all_avail' id;
          let avail' = match Hashtbl.find_all follows id with
                       | [] -> all_avail'
                       | ys -> GenSet.inter all_avail' (GenSet.from_list ys) in
          AuxNode (Partition.elems p id, GenSet.size avail' = 0, build_aux avail' all_avail') :: xs
        end
      else
        xs
    ) all_avail []
  in
    List.fold_left (fun xs t ->
      match prune_incomplete_tree t with
      | Some tr -> tr :: xs
      | None -> xs
    ) [] (build_aux initial_elems all_elems)


let gen_arrtrees (arr:'a t) : 'a arrtree list =
  let process_arr (arr:'a t) : 'a arrtree list =
    let append_eq ((a,b):'a * 'a) (xs:'a Partition.eqs list) =
      Partition.Eq (a,b)::xs in
    let append_ineq ((a,b):'a * 'a) (xs:'a Partition.eqs list) =
      Partition.Ineq (a,b)::xs in
    let eq_list = GenSet.fold append_eq arr.eqs [] in
    let ineq_list = GenSet.fold append_ineq arr.ineqs [] in
    let order_list = Hashtbl.fold (fun a b xs -> append_ineq (a,b) xs) arr.order [] in
    let ps = try
               Partition.gen_partitions (GenSet.to_list arr.dom)
                                        (eq_list @ ineq_list @ order_list)
             with
               Partition.Inconsistent_inequality -> [] in
    let cands = List.fold_left (fun xs p ->
                  let id_order = to_id_order arr p in
                  if not (LeapSCC.has_cycles id_order) then
                    (p,id_order) :: xs
                  else xs
                ) [] ps in
  (*
    List.iter (fun (p,_) ->
        Printf.printf "Well defined: %b\n%s\n\n" (well_defined_order arr p)
                                                 (Partition.to_str f p)
    ) cands;
  *)
    List.fold_left (fun xs (p,id_graph) ->
      let all_avail = (GenSet.from_list (Partition.keys p)) in
      let prev_ids = Hashtbl.create (Hashtbl.length arr.succ) in
      let have_successor = GenSet.empty() in
      Hashtbl.iter (fun a b ->
        let a_id = Partition.id p a in
        let b_id = Partition.id p b in
        Hashtbl.add prev_ids b_id a_id;
        GenSet.add have_successor a_id
      ) arr.succ;
      let initial_avail = GenSet.diff all_avail have_successor in
      (build_cand_tree id_graph prev_ids initial_avail all_avail p) @ xs
    ) [] cands
  in
  let updated_arr = copy arr in
  let _ = match arr.minimum with
          | None -> ()
          | Some m -> GenSet.iter (fun e -> if m <> e then add_lesseq updated_arr m e else ()) arr.dom in
  List.fold_left (fun xs a -> (process_arr a) @ xs) [] (inject_leq_info updated_arr)


let rec arrtree_to_set (tree:'a arrtree) : ('a list list) GenSet.t =
  let Node(e,xs) = tree in
  match xs with
  | [] -> GenSet.singleton [e]
  | _  -> let s = List.fold_left (fun set t -> GenSet.union set (arrtree_to_set t)) (GenSet.empty ()) xs in
          GenSet.fold (fun es res -> GenSet.add res (e::es); res) s (GenSet.empty ())


let gen_arrs (arr:'a t) : ('a list list) GenSet.t =
  List.fold_left (fun s t ->
    let ts = arrtree_to_set t in
    GenSet.union s ts
  ) (GenSet.empty ()) (gen_arrtrees arr)


let arrtree_set_to_str (f:'a -> string) (s:('a list list) GenSet.t) : string =
  String.concat "\n"
    (GenSet.fold (fun es xs -> ("{" ^(String.concat ";" (List.map (fun ec -> "[" ^(String.concat "," (List.map f ec))^ "]") es))^ "}") :: xs) s [])


let rec arrtree_to_str (f:'a -> string) (tree:'a arrtree) : string =
  let Node(e,xs) = tree in
  "{(" ^ (String.concat "," (List.map f e))^ "):[" ^
    (String.concat ";" (List.map (arrtree_to_str f) xs))^ "]}"

let test (arr:'a t) (f:'a -> string) : unit =
  Printf.printf "Original arrangement:\n%s\n\n" (to_str arr f);
  let arr_list = inject_leq_info arr in
  print_endline "List information";
  List.iter (fun a -> print_endline (to_str a f)) arr_list

