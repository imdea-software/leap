
module GenSet = LeapGenericSet

(** The type of an arrangement *)
type 'a t = {
              dom   : 'a GenSet.t;
              eqs   : ('a, 'a) Hashtbl.t;
              ineqs : ('a, 'a) Hashtbl.t;
              order : ('a, 'a) Hashtbl.t;
            }

type eqclass_order_t = (int,int GenSet.t) Hashtbl.t


(** The type of arrangements tree *)
type 'a arrtree = Node of 'a list * 'a arrtree list

let empty () : 'a t =
  {
    dom = GenSet.empty ();
    eqs = Hashtbl.create 10;
    ineqs = Hashtbl.create 10;
    order = Hashtbl.create 10;
  }


let add_elem (arr:'a t) (a:'a) : unit =
  GenSet.add arr.dom a


let add_eq (arr:'a t) (a:'a) (b:'a) : unit =
  GenSet.add arr.dom a;
  GenSet.add arr.dom b;
  Hashtbl.add arr.eqs a b


let add_ineq (arr:'a t) (a:'a) (b:'a) : unit =
  GenSet.add arr.dom a;
  GenSet.add arr.dom b;
  Hashtbl.add arr.ineqs a b


let add_order (arr:'a t) (a:'a) (b:'a) : unit =
  GenSet.add arr.dom a;
  GenSet.add arr.dom b;
  Hashtbl.add arr.order a b


let to_str (arr:'a t) (f:'a -> string) : string =
  let dom_list = GenSet.fold (fun e xs -> (f e) :: xs) arr.dom [] in
  let eq_list = Hashtbl.fold (fun a b xs -> ((f a) ^"="^ (f b)) :: xs) arr.eqs 
  [] in
  let ineq_list = Hashtbl.fold (fun a b xs -> ((f a) ^"!="^ (f b)) :: xs) arr.ineqs [] in
  let order_list = Hashtbl.fold (fun a b xs -> ((f a) ^"<"^ (f b)) :: xs) arr.order [] in
  "{" ^ (String.concat ";" dom_list) ^ "}\n" ^
  "{" ^ (String.concat ";" eq_list) ^ "}\n" ^
  "{" ^ (String.concat ";" ineq_list) ^ "}\n" ^
  "{" ^ (String.concat ";" order_list) ^ "}\n"


let to_id_order (arr:'a t) (p:'a Partition.t) : eqclass_order_t =
  let eqclass_order : eqclass_order_t = Hashtbl.create 10 in
  let eqs = Partition.to_list p in
  List.iter (fun ec ->
    let ec_id = Partition.id p (List.hd ec) in
    let ord_set = List.fold_left (fun s e ->
                    try
                      GenSet.add s (Partition.id p (Hashtbl.find arr.order e));s
                    with _ -> s
                  ) (GenSet.empty()) ec in
    Hashtbl.add eqclass_order ec_id ord_set
  ) eqs;
  eqclass_order


let well_defined_order (arr:'a t) (p:'a Partition.t) : bool =
  not (LeapSCC.has_cycles (to_id_order arr p))


let rec build_cand_tree (graph:eqclass_order_t)
                        (avail:int GenSet.t)
                        (p:'a Partition.t) : 'a arrtree list =
  GenSet.fold (fun id xs ->
    let codom = try Hashtbl.find graph id with _ -> GenSet.empty () in
    if GenSet.inter codom avail <> (GenSet.empty ()) then
      let avail' = GenSet.copy avail in
      GenSet.remove avail' id;
      Node (Partition.elems p id, build_cand_tree graph avail' p) :: xs
    else
      xs
  ) avail []


let gen_arrtrees (arr:'a t) (f:'a -> string) : 'a arrtree list =
  let append_eq (a:'a) (b:'a) (xs:'a Partition.eqs list) =
    Partition.Eq (a,b)::xs in
  let append_ineq (a:'a) (b:'a) (xs:'a Partition.eqs list) =
    Partition.Ineq(a,b) :: xs in
  let eq_list = Hashtbl.fold append_eq arr.eqs [] in
  let ineq_list = Hashtbl.fold append_ineq arr.ineqs [] in
  let order_list = Hashtbl.fold append_ineq arr.order [] in
  let ps = Partition.gen_partitions (GenSet.to_list arr.dom)
                                    (eq_list @ ineq_list @ order_list) in
  let cands = List.fold_left (fun xs p ->
                let id_order = to_id_order arr p in
                if not (LeapSCC.has_cycles id_order) then
                  (p,id_order) :: xs
                else xs
              ) [] ps in
  List.iter (fun (p,_) ->
      Printf.printf "Well defined: %b\n%s\n\n" (well_defined_order arr p)
                                               (Partition.to_str f p)
  ) cands;
  List.fold_left (fun xs (p,id_graph) ->
    (build_cand_tree id_graph (GenSet.from_list (Partition.keys p)) p) @ xs
  ) [] cands


let rec arrtree_to_str (f:'a -> string) (tree:'a arrtree) : string =
  let Node(e,xs) = tree in
  "{(" ^ (String.concat "," (List.map f e))^ "):[" ^
    (String.concat ";" (List.map (arrtree_to_str f) xs))^ "]}"
  

