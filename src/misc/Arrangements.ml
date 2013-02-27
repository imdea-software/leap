
module GenSet = LeapGenericSet

(** The type of an arrangement *)
type 'a t = {
              eqs   : ('a, 'a) Hashtbl.t;
              ineqs : ('a, 'a) Hashtbl.t;
              order : ('a, 'a) Hashtbl.t;
            }

(** The type of arrangements tree *)
type 'a arrtree = Node of 'a * 'a arrtree list

let empty () : 'a t =
  {
    eqs = Hashtbl.create 10;
    ineqs = Hashtbl.create 10;
    order = Hashtbl.create 10;
  }


let add_eq (arr:'a t) (a:'a) (b:'a) : unit =
  Hashtbl.add arr.eqs a b


let add_ineq (arr:'a t) (a:'a) (b:'a) : unit =
  Hashtbl.add arr.ineqs a b


let add_order (arr:'a t) (a:'a) (b:'a) : unit =
  Hashtbl.add arr.order a b


let to_str (arr:'a t) (f:'a -> string) : string =
  let eq_list = Hashtbl.fold (fun a b xs -> ((f a) ^"="^ (f b)) :: xs) arr.eqs [] in
  let ineq_list = Hashtbl.fold (fun a b xs -> ((f a) ^"!="^ (f b)) :: xs) arr.ineqs [] in
  let order_list = Hashtbl.fold (fun a b xs -> ((f a) ^"<"^ (f b)) :: xs) arr.order [] in
  "{" ^ (String.concat ";" eq_list) ^ "}\n" ^
  "{" ^ (String.concat ";" ineq_list) ^ "}\n" ^
  "{" ^ (String.concat ";" order_list) ^ "}\n"


let gen_arrtrees (arr:'a t) : 'a arrtree list =
  let dom_set = GenSet.empty () in
  let add_elem (tbl:('a,'a) Hashtbl.t) : unit =
    Hashtbl.iter (fun a b -> GenSet.add dom_set a;
                             GenSet.add dom_set b) tbl in
  add_elem arr.eqs;
  add_elem arr.ineqs;
  add_elem arr.order;
  let eq_list = Hashtbl.fold (fun a b xs ->
                  Partition.Eq (a,b) :: xs
                ) arr.eqs [] in
  let ineq_list = Hashtbl.fold (fun a b xs ->
                    Partition.Ineq (a,b) :: xs
                  ) arr.ineqs [] in
  let order_list = Hashtbl.fold (fun a b xs ->
                     Partition.Ineq (a,b) :: xs
                   ) arr.order [] in
  let ps = Partition.gen_partitions (GenSet.to_list dom_set)
                                    (eq_list @ ineq_list @ order_list) in
  []
