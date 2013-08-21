open LeapLib
open TllExpression

module Expr     = TllExpression
module VarIdSet = TllExpression.VarIdSet
module ASet     = TllExpression.AtomSet


type model_size =
    { 
      num_elems : int ; 
      num_tids : int ;
      num_addrs : int ;
    }


type union_info = (ASet.t * ASet.t * ASet.t)



let options : Smp.cutoff_options_t ref = ref (Smp.opt_empty())


(* model_size functions *)
let model_size_to_str ms =
  "num_elems  = " ^ (string_of_int ms.num_elems)  ^ "\n" ^
  "num_tids  = " ^ (string_of_int ms.num_tids)  ^ "\n" ^
  "num_addrs  = " ^ (string_of_int ms.num_addrs)  ^ "\n"


(* union_info functions *)

let new_union_count = (ASet.empty, ASet.empty, ASet.empty)


let union_count_elem (u:union_info) (a:Expr.atom) : union_info =
  let (e_set, t_set, a_set) = u
  in
    (ASet.add a e_set, t_set, a_set)


let union_count_tid (u:union_info) (a:Expr.atom) : union_info =
  let (e_set, t_set, a_set) = u
  in
    (e_set, ASet.add a t_set, a_set)


let union_count_addr (u:union_info) (a:Expr.atom) : union_info =
  let (e_set, t_set, a_set) = u
  in
    (e_set, t_set, ASet.add a a_set)


let union_model_size (u:union_info) : model_size =
  let (e_set, t_set, a_set) = u in
  {
    num_elems = ASet.cardinal e_set;
    num_tids = ASet.cardinal t_set;
    num_addrs = ASet.cardinal a_set;
  }


(* calculates the cut_off *)
let cut_off_normalized (expr:conjunctive_formula) : model_size =
  let vars = Expr.get_varset_from_conj expr in
  let vars_tid_set = varset_of_sort vars Tid in
  let vars_tid = VarSet.cardinal vars_tid_set in
  let vars_addr_set = varset_of_sort vars Addr in
  let vars_addr = VarSet.cardinal vars_addr_set in

  let vars_mem_set = if (Smp.forget_primed_mem !options &&
                          not (Smp.group_vars !options)) then
                       VarSet.filter (fun v -> not (Expr.var_is_primed v))
                         (varset_of_sort vars Mem)
                     else
                       varset_of_sort vars Mem in

  let vars_mem = VarSet.cardinal vars_mem_set in

  Printf.printf "VAR ADDRS: %i\n" vars_addr;
  Printf.printf "VAR TIDS: %i\n" vars_tid;
  Printf.printf "VAR MEMS: %i\n" vars_mem;


  (* ALE: I need the "2" for next0, firstlocked0.... *)
  (* ALE: No need to add null and NoThread in the counter, as they are added
          separately as an special address and tid respectively *)

  let numaddr = if Smp.group_vars !options then
                  let _ = LeapDebug.debug "cut_off_normalized, \
                                           group_vars is enabled.\n" in
                  (* We create all possible "next" access to mem variables *)
                  let all_addr_terms = Expr.termset_of_sort
                                        (Expr.get_termset_from_conjformula expr)
                                          Expr.Addr in
                  let voc = TermSet.fold (fun ta set ->
                              List.fold_left (fun s t ->
                                ThreadSet.add t s
                              ) set (Expr.voc_term ta)
                            ) all_addr_terms ThreadSet.empty in

                  let vs = VarSet.elements vars_addr_set in
                  let ts = ThreadSet.elements voc in
                  let (global,local) = List.partition Expr.is_global_var vs in
                  let local_param = List.fold_left (fun xs v ->
                                      (List.map (fun t ->
                                        Expr.var_set_param (Expr.Local t) v
                                      ) ts) @ xs
                                    ) [] local in
                  let nexts = VarSet.fold (fun m ys ->
                                ys @ List.map (fun a ->
                                       Expr.Next(Expr.CellAt
                                         (Expr.VarMem m, Expr.VarAddr a))
                                     ) (global @ local_param)
                              ) vars_mem_set [] in
                  let to_addr xs = List.map (fun v -> Expr.VarAddr v) xs in
                  let all_vars = Expr.Null :: (to_addr global) @
                                 (to_addr local_param) @ nexts in

                  let (eq,ineq) = Expr.get_addrs_eqs_conj expr in
                  let _ = LeapDebug.debug "cut_off_normalized expression:\n%s\n"
                            (Expr.conjunctive_formula_to_str expr) in
                  let assumps = List.map (fun (x,y) -> Partition.Eq (x,y)) eq @
                                List.map (fun (x,y) -> Partition.Ineq (x,y)) ineq in
 
                  let _ = LeapDebug.debug "group_vars domain:\n%s\n"
                            (String.concat "," $
                              List.map Expr.addr_to_str all_vars) in
                  let _ = LeapDebug.debug "group_vars assumptions:\n%s\n"
                            (String.concat "," $
                              List.map (fun e ->
                                match e with
                                | Partition.Eq (a,b) ->
                                    Expr.addr_to_str a ^ "=" ^ Expr.addr_to_str b
                                | Partition.Ineq (a,b) ->
                                    Expr.addr_to_str a ^ "<>" ^ Expr.addr_to_str b
                              ) assumps) in
                  
                  try
                    let part = Partition.gen_init_partitions all_vars assumps in
                    let n_addrs = min (vars_addr + vars_mem * vars_addr)
                                      (Partition.size part) in
                    
                    let _ = LeapDebug.debug
                              "cut_off_normalized, partition size: %i\n" n_addrs in
                    ref n_addrs
                  with
                    | Partition.Inconsistent_inequality ->
                        (LeapDebug.debug "cut_off_normalized: Inconsistent_inequality";
                         ref (List.length all_vars))
                    | e ->
                        (LeapDebug.debug "cut_off_normalized: exception"; raise(e))
                else
                  ref (vars_addr + vars_mem * vars_addr) in

  let vars_elem = VarSet.cardinal (varset_of_sort vars Elem) in

  let numtid = ref (vars_tid) in
  let numelem = ref (vars_elem + vars_mem * vars_addr) in
(*
  let numaddr = ref (2+(VarSet.cardinal varaddr) * tid_num) in
  let numtid = ref (2+(VarSet.cardinal vartid) * tid_num) in
  let numelem = ref (2+(VarSet.cardinal varelem) * tid_num) in
*)
  let process_ineq (x,y) =
    match x with
    | VarT _     -> ()                      (* nothing, y must be a VarT as well *)
    | SetT _     -> numaddr := !numaddr + 1 (* the witness of s1 != s2 *)
    | ElemT _    -> ()
    | TidT _    -> ()
    | AddrT _    -> ()                      (* no need to look for firstlock, every  firstlock has a var *)
    | CellT _    -> ()
    | SetThT _   -> numtid := !numtid + 1   (* the witness of st1 != st2 *)
    | SetElemT _ -> numelem := !numelem + 1 (* the witness of se1 != se2 *)
    | PathT _    -> numaddr := !numaddr + 2 (* the witnesses of p1 != p2 *)
    | MemT _     -> ()
    | IntT _     -> ()
    | VarUpdate _-> () in                (* ALE: Not sure if OK *)
  let process (lit:literal) =
    match lit with
    | Atom(InEq(x,y)) -> process_ineq(x,y)
    | Atom(_) -> ()
    | NegAtom a ->
        begin
          match a with
          | Append _       -> numaddr := !numaddr + 2 (* witness of either p1 intersect p2, or (p1;p2) is different from p3 *)
          | Reach _        -> numaddr := !numaddr + 2 (* witness of p1!=p2 *)
          | OrderList _    -> numelem := !numelem + 2 (* witnesses for not ordered list *)
          | In _           -> ()
          | SubsetEq _     -> numaddr := !numaddr + 1 (* witness of s1 \not\sub s2 *)
          | InTh _         -> ()
          | SubsetEqTh _   -> numtid := !numtid + 1 (* witness of st1 \not\sub st2 *)
          | InElem _       -> ()
          | SubsetEqElem _ -> numelem := !numelem + 1 (* witness of se1 \not\sub se2 *)
          | Less _         -> ()
          | LessEq _       -> ()
          | Greater _      -> ()
          | GreaterEq _    -> ()
          | LessElem _     -> () (* Not sure *)
          | GreaterElem _  -> () (* Not sure *)
          | Eq(x,y)        -> process_ineq (x,y)
          | InEq _         -> ()
          | BoolVar _      -> ()
          | PC _           -> ()
          | PCUpdate _     -> ()
          | PCRange _      -> ()
        end
  in
    match expr with
    | TrueConj  -> { num_addrs = 1 ; num_tids = 1 ; num_elems = 1 }
    | FalseConj -> { num_addrs = 1 ; num_tids = 1 ; num_elems = 1 }
    | Conj l    -> let _ = List.iter process l in
                   (*let _ = numtid := !numtid + vars_mem * !numaddr in
                   let _ = numelem := !numelem + vars_mem * !numaddr in*)
                   {
                     num_addrs = !numaddr ; (* null is accounted for      *)
                     num_tids  = !numtid  ; (* NotThread is accounted for *)
                     num_elems = !numelem ;
                   }


let compute_max_cut_off (conj_list:conjunctive_formula list) : model_size =
  List.fold_left (fun s e ->
    let e_cut_off = cut_off_normalized e
                    
    in
      {
        num_elems = max s.num_elems e_cut_off.num_elems;
        num_tids = max s.num_tids e_cut_off.num_tids;
        num_addrs = max s.num_addrs e_cut_off.num_addrs;
      }
  ) {num_elems=0; num_tids=0; num_addrs=0} conj_list


(* I must also count the equalities!!! *)

let union_eq_cutoff (info:union_info) ((x,y):(Expr.term * Expr.term)) : union_info =
  match x with
    VarT _      -> info (* nothing, y must be a VarT as well *)
  | SetT _      -> union_count_addr info (Expr.Eq(x,y)) (* the witness of s1 != s2 *)
  | ElemT _     -> info
  | TidT _     -> info
  | AddrT _     -> info (* no need to look for firstlock, every firstlock has a var *)
  | CellT _     -> info
  | SetThT _    -> union_count_tid info (Expr.Eq(x,y)) (* the witness of st1 != st2 *)
  | SetElemT _  -> union_count_elem info (Expr.Eq(x,y)) (* the witness of se1 != se2 *)
  | PathT _     -> union_count_addr info (Expr.Eq(x,y)) (* the witnesses of p1 != p2 *)
  | MemT _      -> info
  | IntT _      -> info
  | VarUpdate _ -> info (* ALE: Not sure if OK *)


let union_ineq_cutoff (info:union_info) ((x,y):(Expr.term * Expr.term)) : union_info =
  match x with
    VarT _      -> info (* nothing, y must be a VarT as well *)
  | SetT _      -> union_count_addr info (Expr.InEq(x,y)) (* the witness of s1 != s2 *)
  | ElemT _     -> info
  | TidT _     -> info
  | AddrT _     -> info (* no need to look for firstlock, every firstlock has a var *)
  | CellT _     -> info
  | SetThT _    -> union_count_tid info (Expr.InEq(x,y)) (* the witness of st1 != st2 *)
  | SetElemT _  -> union_count_elem info (Expr.InEq(x,y)) (* the witness of se1 != se2 *)
  | PathT _     -> union_count_addr info (Expr.InEq(x,y)) (* the witnesses of p1 != p2 *)
  | MemT _      -> info
  | IntT _      -> info
  | VarUpdate _ -> info (* ALE: Not sure if OK *)


let union_atom_cutoff (info:union_info) (a:Expr.atom) : union_info =
  match a with
    Append _       -> union_count_addr info a
  | Reach _        -> union_count_addr info a
  | OrderList _    -> union_count_elem info a
  | In      _      -> info
  | SubsetEq _     -> union_count_addr info a
  | InTh _         -> info
  | SubsetEqTh _   -> union_count_tid info a
  | InElem _       -> info
  | SubsetEqElem _ -> union_count_elem info a
  | Less _         -> info
  | LessEq _       -> info
  | Greater _      -> info
  | GreaterEq _    -> info
  | LessElem _     -> union_count_elem info a
  | GreaterElem _  -> union_count_elem info a
  | Eq e           -> union_eq_cutoff info e
  | InEq e         -> union_ineq_cutoff info e
  | BoolVar _      -> info
  | PC _           -> info
  | PCUpdate _     -> info
  | PCRange _      -> info


let union_literal_cutoff (info:union_info) (l:Expr.literal) : union_info =
  match l with
    Atom a    -> union_atom_cutoff info a
  | NegAtom a -> union_atom_cutoff info a


let rec union_formula_cutoff (info:union_info) (phi:Expr.formula) : union_info =
  match phi with
    Literal l       -> union_literal_cutoff info l
  | True            -> info
  | False           -> info
  | And (f1,f2)     -> union_formula_cutoff (union_formula_cutoff info f1) f2
  | Or (f1,f2)      -> union_formula_cutoff (union_formula_cutoff info f1) f2
  | Not f           -> union_formula_cutoff info f
  | Implies (f1,f2) -> union_formula_cutoff (union_formula_cutoff info f1) f2
  | Iff (f1,f2)     -> union_formula_cutoff (union_formula_cutoff info f2) f2


(* Union SMP *)
let compute_max_cut_off_with_union (phi:formula) : model_size =
  let vars = Expr.get_varset_from_formula phi in
  let vartid_num  = VarSet.cardinal (Expr.varset_of_sort vars Tid) in
  let varaddr_num = VarSet.cardinal (Expr.varset_of_sort vars Addr) in
  let varelem_num = VarSet.cardinal (Expr.varset_of_sort vars Elem) in
  let varmem_num  = VarSet.cardinal (Expr.varset_of_sort vars Mem) in
  let info = union_model_size (union_formula_cutoff new_union_count phi) in
  let num_addrs = 1 +                         (* null               *)
                  varaddr_num +               (* Address variables  *)
                  varaddr_num * varmem_num +  (* Cell next pointers *)
                  info.num_addrs              (* Special literals   *) in
  let num_tids = 1 +                          (* No thread          *)
                 vartid_num +                 (* Tid variables     *)
                 varmem_num * num_addrs       (* Cell locks         *) in
  let num_elems = varelem_num +               (* Elem variables     *)
                  varmem_num * num_addrs      (* Cell data          *)
  in
    {
      num_addrs = num_addrs; num_tids = num_tids; num_elems = num_elems;
(*
      num_elems = 2 + (varelem_num + info.num_elems) * vartid_num;
      num_tids = 2 + (vartid_num + info.num_tids) * vartid_num;
      num_addrs = 2 + (varaddr_num + (2 * info.num_addrs)) * vartid_num;
*)
    }


(* Pruning SMP *)
let prune_eq (x:term) (y:term) : (term * term) option =
  match x with
      VarT _      -> None (* nothing, y must be a VarT as well *)
    | SetT _      -> Some (x,y) (* the witness of s1 != s2 *)
    | ElemT _     -> Some (x,y)
    | TidT _     -> Some (x,y)
    | AddrT _     -> Some (x,y) (* For mem[a].next literals *)
    | CellT _     -> None
    | SetThT _    -> Some (x,y) (* the witness of st1 != st2 *)
    | SetElemT _  -> Some (x,y) (* the witness of se1 != se2 *)
    | PathT _     -> Some (x,y) (* the witnesses of p1 != p2 *)
    | MemT _      -> Some (x,y)
    | IntT _      -> None
    | VarUpdate _ -> assert(false) (* ALE: Not sure if OK *)


let prune_atom (a:atom) : atom option =
  match a with
    Append _       -> Some a
  | Reach _        -> Some a
  | OrderList _    -> Some a
  | In _           -> None
  | SubsetEq _     -> Some a
  | InTh _         -> None
  | SubsetEqTh _   -> Some a
  | InElem _       -> None
  | SubsetEqElem _ -> Some a
  | Less _         -> None
  | LessEq _       -> None
  | Greater _      -> None
  | GreaterEq _    -> None
  | LessElem _     -> Some a
  | GreaterElem _  -> Some a
  | Eq (x,y)       -> Option.lift (fun (x',y') -> Eq (x',y')) (prune_eq x y)
  | InEq (x,y)     -> Option.lift (fun (x',y') -> InEq (x',y')) (prune_eq x y)
  | BoolVar _      -> None
  | PC _           -> None
  | PCUpdate _     -> None
  | PCRange _      -> None


let prune_literal (lit:literal) : literal option =
  match lit with
    Atom a    -> Option.lift (fun a' -> Atom a') (prune_atom a)
  | NegAtom a -> Option.lift (fun a' -> NegAtom a') (prune_atom a)


let rec prune_formula (phi:formula) : formula option =
  match phi with
    Literal lit     -> Option.lift (fun l -> Literal l) (prune_literal lit)
  | True            -> None
  | False           -> None
  | And (f1,f2)     -> begin
                         match (prune_formula f1, prune_formula f2) with
                           (Some f1', Some f2') -> Some (And (f1',f2'))
                         | (Some f1', None    ) -> Some f1'
                         | (None    , Some f2') -> Some f2'
                         | (None    , None    ) -> None
                       end
  | Or (f1,f2)      -> begin
                         match (prune_formula f1, prune_formula f2) with
                           (Some f1', Some f2') -> Some (Or (f1',f2'))
                         | (Some f1', None    ) -> Some f1'
                         | (None    , Some f2') -> Some f2'
                         | (None    , None    ) -> None
                       end
  | Not (f)         -> Option.lift (fun f'-> Not f') (prune_formula f)
  | Implies (f1,f2) -> prune_formula (Or (Not f1, f2))
  | Iff (f1,f2)     -> prune_formula (And (Implies (f1,f2), Implies (f2,f1)))
    


let compute_max_cut_off_with_pruning (phi:formula) : model_size =
  Printf.printf "Original formula: %s\n" (Expr.formula_to_str phi);
  let pruned_phi = Option.default True (prune_formula (Expr.nnf phi)) in
  Printf.printf "Pruned formula: %s\n" (Expr.formula_to_str pruned_phi);
  let dnf_phi = Expr.dnf pruned_phi in
  let new_dnf = List.map Expr.cleanup_dup dnf_phi in
  List.iter (fun xs -> Printf.printf "DNF Formula: %s\n" (Expr.conjunctive_formula_to_str xs)) new_dnf;
    compute_max_cut_off (new_dnf)


let cut_off (strat:Smp.cutoff_strategy_t)
            (opt:Smp.cutoff_options_t)
            (f:formula) : model_size =
(*  LOG "Strategy: %s\n" (Smp.strategy_to_str strat) LEVEL DEBUG; *)
  options := opt;
  match strat with
  | Smp.Dnf     -> compute_max_cut_off (Expr.dnf f)
  | Smp.Union   -> compute_max_cut_off_with_union f
  | Smp.Pruning -> compute_max_cut_off_with_pruning f
