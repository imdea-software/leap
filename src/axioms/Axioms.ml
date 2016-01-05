
module Expr = Expression
module GSet = LeapGenericSet

exception Duplicated_special_case
exception Unsupported_axiom of string

type case_tbl_t = (Expr.pc_t, Tag.f_tag list) Hashtbl.t

type rule_t = Tag.f_tag  *  (* Invariant                     *)
              case_tbl_t    (* Special cases                 *)

type case_t = Expr.pc_t * Tag.f_tag list

type t = (Tag.f_tag, case_tbl_t) Hashtbl.t

type v_info_t =  { v_sort : Expr.sort;
                   v_term : Expr.TermSet.t;}

type var_subst_tbl_t = (Expr.V.t, v_info_t) Hashtbl.t

type axiom_case_t = { vars : var_subst_tbl_t;
                      premises : (Expr.literal * bool) GSet.t;
                      result: Expr.formula; }
type axiom_tbl_t = (Tag.f_tag, axiom_case_t list) Hashtbl.t


let empty_axioms () : t =
  Hashtbl.create 0


let new_axioms (rs:rule_t list) : t =
  let tbl = Hashtbl.create (List.length rs) in
  List.iter (fun (inv, cases) ->
    Hashtbl.add tbl inv cases
  ) rs;
  tbl


let split_formula (phi:Expr.formula) (var_tbl:System.var_table_t) : axiom_case_t list =
  let var_subst_tbl = Hashtbl.create (System.num_of_vars var_tbl) in

  List.iter (fun v ->
    let v_info = { v_sort = System.find_var_type var_tbl (Expr.V.id v);
                   v_term = Expr.TermSet.empty; } in
    Hashtbl.add var_subst_tbl v v_info
  ) (System.get_variable_list var_tbl);
  let ax_conj = Formula.to_conj_list phi in
  List.map (fun conj ->
    print_endline ("CONJ: " ^ (Expr.formula_to_str conj));
    match conj with
    | Formula.Literal lit ->
        begin
          { vars = Hashtbl.copy var_subst_tbl;
            premises = GSet.singleton (lit,false);
            result = Formula.True; }
        end
    | Formula.Implies (ante, conseq) ->
        begin
          print_endline ("ANTE: " ^ (Expr.formula_to_str ante));
          let prems = Formula.to_conj_literals (Formula.nnf ante) in
          print_endline "Done";
          let prem_set = GSet.empty () in
          List.iter (fun p -> GSet.add prem_set (p,false)) prems;
          { vars = Hashtbl.copy var_subst_tbl;
            premises = prem_set;
            result = conseq; }
        end
    | Formula.And _ ->
        begin
          print_endline ("CONJ: " ^ (Expr.formula_to_str conj));
          let prems = Formula.to_conj_literals (Formula.nnf conj) in
          print_endline "Done";
          let prem_set = GSet.empty () in
          List.iter (fun p -> GSet.add prem_set (p,false)) prems;
          { vars = Hashtbl.copy var_subst_tbl;
            premises = prem_set;
            result = Formula.True; }
        end
    | _ -> raise (Unsupported_axiom (Expr.formula_to_str phi))
  ) ax_conj


let new_axiom_table (ax_tags:Tag.tag_table) : axiom_tbl_t =
  print_endline ("AXIOM TAG SIZE: " ^ (string_of_int (Tag.tag_table_size ax_tags)));
  let tbl = Hashtbl.create (Tag.tag_table_size ax_tags) in
  Tag.tag_table_iter ax_tags (fun t (t_phi,info) ->
    let cases = split_formula t_phi (Tag.info_params info) in
    Hashtbl.add tbl t cases
  );
  tbl


let reset_axiom_cases (cases:axiom_case_t list) : axiom_case_t list =
  List.map (fun c ->
    let reseted_prems = GSet.empty () in
    GSet.iter (fun (phi,_) ->
      GSet.add reseted_prems (phi,false)
    ) c.premises;
    Hashtbl.iter (fun v info ->
      Hashtbl.replace c.vars v {v_sort = info.v_sort;
                                v_term = Expr.TermSet.empty; }
    ) c.vars;
    { vars = c.vars;
      premises = reseted_prems;
      result = c.result;}
  ) cases


let reset_axiom_table (tbl:axiom_tbl_t) : unit =
  Hashtbl.iter (fun t cases ->
    Hashtbl.replace tbl t (reset_axiom_cases cases)
  ) tbl


let reset_axiom (tbl:axiom_tbl_t) (ax_tag:Tag.f_tag) : unit =
  if Hashtbl.mem tbl ax_tag then
    Hashtbl.replace tbl ax_tag (reset_axiom_cases (Hashtbl.find tbl ax_tag))
  else
    ()


let new_rule (inv:Tag.f_tag) (cases:case_t list) : rule_t =
  let tbl = Hashtbl.create 10 in
  let _ = List.iter (fun (pc,tags) ->
            if Hashtbl.mem tbl pc then
              begin
                Interface.Err.msg "Special case already defined" "";
                raise(Duplicated_special_case)
              end
            else
              Hashtbl.add tbl pc tags
          ) cases
  in
    (inv, tbl)


let new_case (pc:Expr.pc_t) (xs:Tag.f_tag list) : case_t =
  (pc,xs)


(* Begin pretty printers *)
let axiom_table_to_str (tbl:axiom_tbl_t) : string =
  Hashtbl.fold (fun t cases str ->
    str ^ "-----------\nAXIOM: " ^ (Tag.tag_id t) ^ "\n" ^
    "Cases:\n" ^
    (String.concat "\n"
      (List.map (fun c ->
          let v_str = Hashtbl.fold (fun v info str ->
                        str ^ (Expr.V.id v) ^ "; "
                      ) c.vars "" in
          let prem_str = GSet.fold (fun (l,b) str ->
                           (Expr.literal_to_str l) ^ "[" ^ (if b then "X" else " ") ^ "];"
                         ) c.premises "" in
          let res_str = Expr.formula_to_str c.result in
          "Vars: " ^ v_str ^ "\n" ^
          "Premises: " ^ prem_str ^ "\n" ^
          "Result: " ^ res_str ^ "\n"
        ) cases
      )
    )
  )tbl ""


(* End pretty printers *)


let lookup (ax:t) (inv:Tag.f_tag) (pc:Expr.pc_t) : Tag.f_tag list =
  try
    Hashtbl.find (Hashtbl.find ax inv) pc
  with _ -> []


 
(* Apply axiom on formula *)


let apply (tbl:axiom_tbl_t) (phi:Expr.formula) (ax_tag:Tag.f_tag) : Expr.formula =
  let find_matching_case (case:axiom_case_t) (l:Expr.literal) : axiom_case_t =
    let (@@) (xs,b1) (ys,b2) =
      if (b1 && b2) then
        (xs @ ys, true)
      else
        ([], false) in

    let rec match_var (v:Expr.V.t) (s:Expr.sort) (t:Expr.term) :
        ((Expr.V.t * Expr.term) list * bool) =
      try
        let info = Hashtbl.find case.vars v in
        if info.v_sort == s then
          ([v,t], true)
        else
          ([], false)
      with _ -> ([], false)

    and match_lit (pl:Expr.literal) (l:Expr.literal) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pl,l) with
      | (Formula.Atom a1, Formula.Atom a2)
      | (Formula.NegAtom a1, Formula.NegAtom a2) -> match_atom a1 a2
      | _ -> ([], false)

    and match_term (pt:Expr.term) (t:Expr.term) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pt,t) with
      | (Expr.VarT v, _) ->
          match_var v (Expr.term_sort t) t
      | (Expr.SetT (s1), Expr.SetT (s2)) ->
          (match_set s1 s2)
      | (Expr.ElemT (e1), Expr.ElemT (e2)) ->
          (match_elem e1 e2)
      | (Expr.TidT (t1), Expr.TidT (t2)) ->
          (match_tid t1 t2)
      | (Expr.AddrT (a1), Expr.AddrT (a2)) ->
          (match_addr a1 a2)
      | (Expr.CellT (c1), Expr.CellT (c2)) ->
          (match_cell c1 c2)
      | (Expr.SetThT (s1), Expr.SetThT (s2)) ->
          (match_settid s1 s2)
      | (Expr.SetIntT (s1), Expr.SetIntT (s2)) ->
          (match_setint s1 s2)
      | (Expr.SetElemT (s1), Expr.SetElemT (s2)) ->
          (match_setelem s1 s2)
      | (Expr.SetPairT (s1), Expr.SetPairT (s2)) ->
          (match_setpair s1 s2)
      | (Expr.PathT (p1), Expr.PathT (p2)) ->
          (match_path p1 p2)
      | (Expr.MemT (m1), Expr.MemT (m2)) ->
          (match_mem m1 m2)
      | (Expr.IntT (i1), Expr.IntT (i2)) ->
          (match_int i1 i2)
      | (Expr.PairT (p1), Expr.PairT (p2)) ->
          (match_pair p1 p2)
      | (Expr.ArrayT (arr1), Expr.ArrayT (arr2)) ->
          (match_array arr1 arr2)
      | (Expr.AddrArrayT (arr1), Expr.AddrArrayT (arr2)) ->
          (match_addrarray arr1 arr2)
      | (Expr.TidArrayT (arr1), Expr.TidArrayT (arr2)) ->
          (match_tidarray arr1 arr2)
      | (Expr.BucketArrayT (arr1), Expr.BucketArrayT (arr2)) ->
          (match_bucketarray arr1 arr2)
      | (Expr.MarkT (m1), Expr.MarkT (m2)) ->
          (match_mark m1 m2)
      | (Expr.BucketT (b1), Expr.BucketT (b2)) ->
          (match_bucket b1 b2)
      | (Expr.LockT (l1), Expr.LockT (l2)) ->
          (match_lock l1 l2)
      | (Expr.LockArrayT (x1), Expr.LockArrayT (x2)) ->
          (match_lockarray x1 x2)
      | _ -> ([], false)

    and match_atom (pa:Expr.atom) (a:Expr.atom) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.Append(p1,p2,p3),Expr.Append(q1,q2,q3)) ->
          (match_path p1 q1) @@ (match_path p2 q2) @@ (match_path p3 q3)
      | (Expr.Reach(h1,f1,t1,p1), Expr.Reach(h2,f2,t2,p2)) ->
          (match_mem h1 h2) @@ (match_addr f1 f2) @@
          (match_addr t1 t2) @@ (match_path p1 p2)
      | (Expr.ReachAt(h1,f1,t1,l1,p1), Expr.ReachAt(h2,f2,t2,l2,p2)) ->
          (match_mem h1 h2) @@ (match_addr f1 f2) @@
          (match_addr t1 t2) @@ (match_int l1 l2) @@ (match_path p1 p2)
      | (Expr.OrderList(h1,f1,t1), Expr.OrderList(h2,f2,t2)) ->
          (match_mem h1 h2) @@ (match_addr f1 f2) @@
          (match_addr t1 t2)
      | (Expr.Skiplist(h1,s1,l1,f1,t1,e1), Expr.Skiplist(h2,s2,l2,f2,t2,e2)) ->
          (match_mem h1 h2) @@ (match_set s1 s2) @@
          (match_int l1 l2) @@ (match_addr f1 f2) @@
          (match_addr t1 t2) @@ (match_setelem e1 e2)
      | (Expr.In(a1,s1), Expr.In(a2,s2)) ->
          (match_addr a1 a2) @@ (match_set s1 s2)
      | (Expr.SubsetEq(s1,r1), Expr.SubsetEq(s2,r2)) ->
          (match_set s1 s2) @@ (match_set r1 r2)
      | (Expr.InTh(t1,s1), Expr.InTh(t2,s2)) ->
          (match_tid t1 t2) @@ (match_settid s1 s2)
      | (Expr.SubsetEqTh(s1,r1), Expr.SubsetEqTh(s2,r2)) ->
          (match_settid s1 s2) @@ (match_settid r1 r2)
      | (Expr.InInt(i1,s1), Expr.InInt(i2,s2)) ->
          (match_int i1 i2) @@ (match_setint s1 s2)
      | (Expr.SubsetEqInt(s1,r1), Expr.SubsetEqInt(s2,r2)) ->
          (match_setint s1 s2) @@ (match_setint r1 r2)
      | (Expr.InElem(e1,s1), Expr.InElem(e2,s2)) ->
          (match_elem e1 e2) @@ (match_setelem s1 s2)
      | (Expr.SubsetEqElem(s1,r1), Expr.SubsetEqElem(s2,r2)) ->
          (match_setelem s1 s2) @@ (match_setelem r1 r2)
      | (Expr.InPair(p1,s1), Expr.InPair(p2,s2)) ->
          (match_pair p1 p2) @@ (match_setpair s1 s2)
      | (Expr.SubsetEqPair(s1,r1), Expr.SubsetEqPair(s2,r2)) ->
          (match_setpair s1 s2) @@ (match_setpair r1 r2)
      | (Expr.InTidPair(t1,s1), Expr.InTidPair(t2,s2)) ->
          (match_tid t1 t2) @@ (match_setpair s1 s2)
      | (Expr.InIntPair(i1,s1), Expr.InIntPair(i2,s2)) ->
          (match_int i1 i2) @@ (match_setpair s1 s2)
      | (Expr.Less(i1,j1), Expr.Less(i2,j2)) ->
          (match_int i1 i2) @@ (match_int j1 j2)
      | (Expr.Greater(i1,j1), Expr.Greater(i2,j2)) ->
          (match_int i1 i2) @@ (match_int j1 j2)
      | (Expr.LessEq(i1,j1), Expr.LessEq(i2,j2)) ->
          (match_int i1 i2) @@ (match_int j1 j2)
      | (Expr.GreaterEq(i1,j1), Expr.GreaterEq(i2,j2)) ->
          (match_int i1 i2) @@ (match_int j1 j2)
      | (Expr.LessTid(t1,u1), Expr.LessTid(t2,u2)) ->
          (match_tid t1 t2) @@ (match_tid u1 u2)
      | (Expr.LessElem(e1,e2), Expr.LessElem(f1,f2)) ->
          (match_elem e1 e2) @@ (match_elem f1 f2)
      | (Expr.GreaterElem(e1,e2), Expr.GreaterElem(f1,f2)) ->
          (match_elem e1 e2) @@ (match_elem f1 f2)
      | (Expr.Eq(t1,u1), Expr.Eq(t2,u2)) ->
          (match_term t1 t2) @@ (match_term u1 u2)
      | (Expr.InEq(t1,u1), Expr.InEq(t2,u2)) ->
          (match_term t1 t2) @@ (match_term u1 u2)
      | (Expr.UniqueInt(s1), Expr.UniqueInt(s2)) ->
          (match_setpair s1 s2)
      | (Expr.UniqueTid(s1), Expr.UniqueTid(s2)) ->
          (match_setpair s1 s2)
      | (Expr.BoolVar(v1), Expr.BoolVar(v2)) ->
          ([], true)
      | (Expr.BoolArrayRd(arr1,t1), Expr.BoolArrayRd(arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.PC(_), Expr.PC(_))
      | (Expr.PCUpdate(_), Expr.PCUpdate(_))
      | (Expr.PCRange(_), Expr.PCRange(_)) -> ([], true)
      | _ -> ([], false)

    and match_array (pa:Expr.arrays) (a:Expr.arrays) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.VarArray (v), _) -> match_var v Expr.Array (Expr.ArrayT a)
      | (Expr.ArrayUp(arr1,t1,e1), Expr.ArrayUp(arr2,t2,e2)) ->
          ([], false)
      | _ -> ([], false)

    and match_addrarray (pa:Expr.addrarr) (a:Expr.addrarr) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.VarAddrArray (v), _) -> match_var v Expr.AddrArray (Expr.AddrArrayT a)
      | (Expr.AddrArrayUp(arr1,i1,a1), Expr.AddrArrayUp(arr2,i2,a2)) ->
          (match_addrarray arr1 arr2) @@ (match_int i1 i2) @@
          (match_addr a1 a2)
      | (Expr.CellArr(c1), Expr.CellArr(c2)) ->
          (match_cell c1 c2)
      | _ -> ([], false)

    and match_tidarray (pa:Expr.tidarr) (a:Expr.tidarr) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.VarTidArray (v), _) -> match_var v Expr.TidArray (Expr.TidArrayT a)
      | (Expr.TidArrayUp(arr1,i1,t1), Expr.TidArrayUp(arr2,i2,t2)) ->
          (match_tidarray arr1 arr2) @@ (match_int i1 i2) @@
          (match_tid t1 t2)
      | (Expr.CellTids(c1), Expr.CellTids(c2)) ->
          (match_cell c1 c2)
      | _ -> ([], false)

    and match_bucketarray (pa:Expr.bucketarr) (a:Expr.bucketarr) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.VarBucketArray (v), _) -> match_var v Expr.BucketArray (Expr.BucketArrayT a)
      | (Expr.BucketArrayUp(arr1,i1,b1), Expr.BucketArrayUp(arr2,i2,b2)) ->
          (match_bucketarray arr1 arr2) @@ (match_int i1 i2) @@
          (match_bucket b1 b2)
      | _ -> ([], false)

    and match_int (pi:Expr.integer) (i:Expr.integer) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pi,i) with
      | (Expr.VarInt (v), _) -> match_var v Expr.Int (Expr.IntT i)
      | (Expr.IntVal (x1), Expr.IntVal (x2)) -> ([], x1 == x2)
      | (Expr.IntNeg (x1), Expr.IntNeg (x2)) ->
          (match_int x1 x2)
      | (Expr.IntAdd (x1,y1), Expr.IntAdd (x2,y2)) ->
          (match_int x1 x2) @@ (match_int y1 y2)
      | (Expr.IntSub (x1,y1), Expr.IntSub (x2,y2)) ->
          (match_int x1 x2) @@ (match_int y1 y2)
      | (Expr.IntMul (x1,y1), Expr.IntMul (x2,y2)) ->
          (match_int x1 x2) @@ (match_int y1 y2)
      | (Expr.IntDiv (x1,y1), Expr.IntDiv (x2,y2)) ->
          (match_int x1 x2) @@ (match_int y1 y2)
      | (Expr.IntMod (x1,y1), Expr.IntMod (x2,y2)) ->
          (match_int x1 x2) @@ (match_int y1 y2)
      | (Expr.IntArrayRd (arr1,t1), Expr.IntArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.IntSetMin (s1), Expr.IntSetMin (s2)) ->
          (match_setint s1 s2)
      | (Expr.IntSetMax (s1), Expr.IntSetMax (s2)) ->
          (match_setint s1 s2)
      | (Expr.CellMax (c1), Expr.CellMax (c2)) ->
          (match_cell c1 c2)
      | (Expr.HavocLevel, Expr.HavocLevel) -> ([], true)
      | (Expr.HashCode (e1), Expr.HashCode (e2)) ->
          (match_elem e1 e2)
      | (Expr.PairInt (p1), Expr.PairInt (p2)) ->
          (match_pair p1 p2)
      | _ -> ([], false)

    and match_pair (pp:Expr.pair) (p:Expr.pair) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pp,p) with
      | (Expr.VarPair (v), _) -> match_var v Expr.Pair (Expr.PairT p)
      | (Expr.IntTidPair (i1,t1), Expr.IntTidPair (i2,t2)) ->
          (match_int i1 i2) @@ (match_tid t1 t2)
      | (Expr.SetPairMin (s1), Expr.SetPairMin (s2)) ->
          (match_setpair s1 s2)
      | (Expr.SetPairMax (s1), Expr.SetPairMax (s2)) ->
          (match_setpair s1 s2)
      | (Expr.PairArrayRd (arr1,t1), Expr.PairArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | _ -> ([], false)

    and match_set (ps:Expr.set) (s:Expr.set) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (ps,s) with
      | (Expr.VarSet (v), _) -> match_var v Expr.Set (Expr.SetT s)
      | (Expr.EmptySet, Expr.EmptySet) -> ([], true)
      | (Expr.Singl (a1), Expr.Singl (a2)) ->
          (match_addr a1 a2)
      | (Expr.Union (s1,r1), Expr.Union (s2,r2)) ->
          (match_set s1 s2) @@ (match_set r1 r2)
      | (Expr.Intr (s1,r1), Expr.Intr (s2,r2)) ->
          (match_set s1 s2) @@ (match_set r1 r2)
      | (Expr.Setdiff (s1,r1), Expr.Setdiff (s2,r2)) ->
          (match_set s1 s2) @@ (match_set r1 r2)
      | (Expr.PathToSet (p1), Expr.PathToSet (p2)) ->
          (match_path p1 p2)
      | (Expr.AddrToSet (m1,a1), Expr.AddrToSet (m2,a2)) ->
          (match_mem m1 m2) @@ (match_addr a1 a2)
      | (Expr.AddrToSetAt (m1,a1,i1), Expr.AddrToSetAt (m2,a2,i2)) ->
          (match_mem m1 m2) @@ (match_addr a1 a2) @@
          (match_int i1 i2)
      | (Expr.SetArrayRd (arr1,t1), Expr.SetArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.BucketRegion (b1), Expr.BucketRegion (b2)) ->
          (match_bucket b1 b2)
      | _ -> ([], false)

    and match_tid (pt:Expr.tid) (t:Expr.tid) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pt,t) with
      | (Expr.VarTh (v), _) -> match_var v Expr.Tid (Expr.TidT t)
      | (Expr.NoTid, Expr.NoTid) -> ([], true)
      | (Expr.CellLockId (c1), Expr.CellLockId (c2)) ->
          (match_cell c1 c2)
      | (Expr.CellLockIdAt (c1,i1), Expr.CellLockIdAt (c2,i2)) ->
          (match_cell c1 c2) @@ (match_int i1 i2)
      | (Expr.TidArrayRd (arr1,t1), Expr.TidArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.TidArrRd (arr1,i1), Expr.TidArrRd (arr2,i2)) ->
          (match_tidarray arr1 arr2) @@ (match_int i1 i2)
      | (Expr.PairTid (p1), Expr.PairTid (p2)) ->
          (match_pair p1 p2)
      | (Expr.BucketTid (b1), Expr.BucketTid (b2)) ->
          (match_bucket b1 b2)
      | (Expr.LockId (l1), Expr.LockId (l2)) ->
          (match_lock l1 l2)
      | _ -> ([], false)

    and match_lock (pl:Expr.lock) (l:Expr.lock) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pl,l) with
      | (Expr.VarLock (v), _) -> match_var v Expr.Lock (Expr.LockT l)
      | (Expr.LLock (l1,t1), Expr.LLock (l2,t2)) ->
          (match_lock l1 l2) @@ (match_tid t1 t2)
      | (Expr.LUnlock (l1), Expr.LUnlock (l2)) ->
          (match_lock l1 l2)
      | (Expr.LockArrRd (arr1,i1), Expr.LockArrRd (arr2,i2)) ->
          (match_lockarray arr1 arr2) @@ (match_int i1 i2)
      | _ -> ([], false)

    and match_lockarray (pa:Expr.lockarr) (a:Expr.lockarr) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.VarLockArray (v), _) -> match_var v Expr.LockArray (Expr.LockArrayT a)
      | (Expr.LockArrayUp (arr1,i1,l1), Expr.LockArrayUp (arr2,i2,l2)) ->
          (match_lockarray arr1 arr2) @@ (match_int i1 i2) @@
          (match_lock l1 l2)
      | _ -> ([], false)

    and match_elem (pe:Expr.elem) (e:Expr.elem) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pe,e) with
      | (Expr.VarElem (v), _) -> match_var v Expr.Elem (Expr.ElemT e)
      | (Expr.CellData (c1), Expr.CellData (c2)) ->
          (match_cell c1 c2)
      | (Expr.ElemArrayRd (arr1,t1), Expr.ElemArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.HavocListElem, Expr.HavocListElem) -> ([], true)
      | (Expr.HavocSkiplistElem, Expr.HavocSkiplistElem) -> ([], true)
      | (Expr.LowestElem, Expr.LowestElem) -> ([], true)
      | (Expr.HighestElem, Expr.HighestElem) -> ([], true)
      | _ -> ([], false)

    and match_addr (pa:Expr.addr) (a:Expr.addr) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pa,a) with
      | (Expr.VarAddr (v), _) -> match_var v Expr.Addr (Expr.AddrT a)
      | (Expr.Null, Expr.Null) -> ([], true)
      | (Expr.Next (c1), Expr.Next(c2)) ->
          (match_cell c1 c2)
      | (Expr.NextAt (c1,i1), Expr.NextAt(c2,i2)) ->
          (match_cell c1 c2) @@ (match_int i1 i2)
      | (Expr.ArrAt (c1,i1), Expr.ArrAt(c2,i2)) ->
          (match_cell c1 c2) @@ (match_int i1 i2)
      | (Expr.FirstLocked (m1,p1), Expr.FirstLocked(m2,p2)) ->
          (match_mem m1 m2) @@ (match_path p1 p2)
      | (Expr.FirstLockedAt (m1,p1,i1), Expr.FirstLockedAt(m2,p2,i2)) ->
          (match_mem m1 m2) @@ (match_path p1 p2) @@
          (match_int i1 i2)
      | (Expr.LastLocked (m1,p1), Expr.LastLocked(m2,p2)) ->
          (match_mem m1 m2) @@ (match_path p1 p2)
      | (Expr.AddrArrayRd (arr1,t1), Expr.AddrArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.AddrArrRd (arr1,i1), Expr.AddrArrRd (arr2,i2)) ->
          (match_addrarray arr1 arr2) @@ (match_int i1 i2)
      | (Expr.BucketInit (b1), Expr.BucketInit (b2)) ->
          (match_bucket b1 b2)
      | (Expr.BucketEnd (b1), Expr.BucketEnd (b2)) ->
          (match_bucket b1 b2)
      | _ -> ([], false)

    and match_cell (pc:Expr.cell) (c:Expr.cell) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pc,c) with
      | (Expr.VarCell (v), _) -> match_var v Expr.Cell (Expr.CellT c)
      | (Expr.Error, Expr.Error) -> ([], true)
      | (Expr.MkCell (e1,a1,t1), Expr.MkCell (e2,a2,t2)) ->
          (match_elem e1 e2) @@ (match_addr a1 a2) @@
          (match_tid t1 t2)
      | (Expr.MkCellMark (e1,a1,t1,m1), Expr.MkCellMark(e2,a2,t2,m2)) ->
          (match_elem e1 e2) @@ (match_addr a1 a2) @@
          (match_tid t1 t2) @@ (match_mark m1 m2)
      | (Expr.MkSLKCell (e1,a1,t1), Expr.MkSLKCell(e2,a2,t2)) ->
          (match_elem e1 e2) @@
          (List.fold_left2 (fun res x1 x2 ->
             (match_addr x1 x2) @@ res
           ) ([], true) a1 a2) @@
          (List.fold_left2 (fun res x1 x2 ->
             (match_tid x1 x2) @@ res
           ) ([], true) t1 t2)
      | (Expr.MkSLCell (e1,a1,t1,i1), Expr.MkSLCell (e2,a2,t2,i2)) ->
          (match_elem e1 e2) @@ (match_addrarray a1 a2) @@
          (match_tidarray t1 t2) @@ (match_int i1 i2)
      | (Expr.CellLock (c1,t1), Expr.CellLock (c2,t2)) ->
          (match_cell c1 c2) @@ (match_tid t1 t2)
      | (Expr.CellLockAt (c1,i1,t1), Expr.CellLockAt (c2,i2,t2)) ->
          (match_cell c1 c2) @@ (match_int i1 i2) @@
          (match_tid t1 t2)
      | (Expr.CellUnlock (c1), Expr.CellUnlock (c2)) ->
          (match_cell c1 c2)
      | (Expr.CellUnlockAt (c1,i1), Expr.CellUnlockAt (c2,i2)) ->
          (match_cell c1 c2) @@ (match_int i1 i2)
      | (Expr.CellAt (h1,a1), Expr.CellAt (h2,a2)) ->
          (match_mem h1 h2) @@ (match_addr a1 a2)
      | (Expr.CellArrayRd (arr1,t1), Expr.CellArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.UpdCellAddr (c1,i1,a1), Expr.UpdCellAddr (c2,i2,a2)) ->
          (match_cell c1 c2) @@ (match_int i1 i2) @@
          (match_addr a1 a2)
      | _ -> ([], false)

    and match_mark (pm:Expr.mark) (m:Expr.mark) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pm,m) with
      | (Expr.VarMark (v), _) -> match_var v Expr.Mark (Expr.MarkT m)
      | (Expr.MarkTrue, Expr.MarkTrue) -> ([], true)
      | (Expr.MarkFalse, Expr.MarkFalse) -> ([], true)
      | (Expr.Marked (c1), Expr.Marked (c2)) ->
          (match_cell c1 c2)
      | _ -> ([], false)

    and match_bucket (pb:Expr.bucket) (b:Expr.bucket) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pb,b) with
      | (Expr.VarBucket (v), _) -> match_var v Expr.Bucket (Expr.BucketT b)
      | (Expr.MkBucket (a1,b1,s1,t1), Expr.MkBucket (a2,b2,s2,t2)) ->
          (match_addr a1 a2) @@ (match_addr b1 b2) @@
          (match_set s1 s2) @@ (match_tid t1 t2)
      | (Expr.BucketArrRd (arr1,i1), Expr.BucketArrRd (arr2,i2)) ->
          (match_bucketarray arr1 arr2) @@ (match_int i1 i2)
      | _ -> ([], false)

    and match_settid (ps:Expr.setth) (s:Expr.setth) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (ps,s) with
      | (Expr.VarSetTh (v), _) -> match_var v Expr.SetTh (Expr.SetThT s)
      | (Expr.EmptySetTh, Expr.EmptySetTh) -> ([], true)
      | (Expr.SinglTh (t1), Expr.SinglTh (t2)) ->
          (match_tid t1 t2)
      | (Expr.UnionTh (s1,r1), Expr.UnionTh (s2,r2)) ->
          (match_settid s1 s2) @@ (match_settid r1 r2)
      | (Expr.IntrTh (s1,r1), Expr.IntrTh (s2,r2)) ->
          (match_settid s1 s2) @@ (match_settid r1 r2)
      | (Expr.SetdiffTh (s1,r1), Expr.SetdiffTh (s2,r2)) ->
          (match_settid s1 s2) @@ (match_settid r1 r2)
      | (Expr.SetThArrayRd (arr1,t1), Expr.SetThArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | (Expr.LockSet (h1,p1), Expr.LockSet (h2,p2)) ->
          (match_mem h1 h2) @@ (match_path p1 p2)
      | _ -> ([], false)

    and match_setint (ps:Expr.setint) (s:Expr.setint) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (ps,s) with
      | (Expr.VarSetInt (v), _) -> match_var v Expr.SetInt (Expr.SetIntT s)
      | (Expr.EmptySetInt, Expr.EmptySetInt) -> ([], true)
      | (Expr.SinglInt (i1), Expr.SinglInt (i2)) ->
          (match_int i1 i2)
      | (Expr.UnionInt (s1,r1), Expr.UnionInt (s2,r2)) ->
          (match_setint s1 s2) @@ (match_setint r1 r2)
      | (Expr.IntrInt (s1,r1), Expr.IntrInt (s2,r2)) ->
          (match_setint s1 s2) @@ (match_setint r1 r2)
      | (Expr.SetdiffInt (s1,r1), Expr.SetdiffInt (s2,r2)) ->
          (match_setint s1 s2) @@ (match_setint r1 r2)
      | (Expr.SetLower (s1,i1), Expr.SetLower (s2,i2)) ->
          (match_setint s1 s2) @@ (match_int i1 i2)
      | (Expr.SetIntArrayRd (arr1,t1), Expr.SetIntArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | _ -> ([], false)


    and match_setelem (ps:Expr.setelem) (s:Expr.setelem) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (ps,s) with
      | (Expr.VarSetElem (v), _) -> match_var v Expr.SetElem (Expr.SetElemT s)
      | (Expr.EmptySetElem, Expr.EmptySetElem) -> ([], true)
      | (Expr.SinglElem (e1), Expr.SinglElem (e2)) ->
          (match_elem e1 e2)
      | (Expr.UnionElem (s1,r1), Expr.UnionElem (s2,r2)) ->
          (match_setelem s1 s2) @@ (match_setelem r1 r2)
      | (Expr.IntrElem (s1,r1), Expr.IntrElem (s2,r2)) ->
          (match_setelem s1 s2) @@ (match_setelem r1 r2)
      | (Expr.SetdiffElem (s1,r1), Expr.SetdiffElem (s2,r2)) ->
          (match_setelem s1 s2) @@ (match_setelem r1 r2)
      | (Expr.SetToElems (s1,h1), Expr.SetToElems (s2,h2)) ->
          (match_set s1 s2) @@ (match_mem h1 h2)
      | (Expr.SetElemArrayRd (arr1,t1), Expr.SetElemArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | _ -> ([], false)


    and match_setpair (ps:Expr.setpair) (s:Expr.setpair) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (ps,s) with
      | (Expr.VarSetPair (v), _) -> match_var v Expr.SetPair (Expr.SetPairT s)
      | (Expr.EmptySetPair, Expr.EmptySetPair) -> ([], true)
      | (Expr.SinglPair (p1), Expr.SinglPair (p2)) ->
          (match_pair p1 p2)
      | (Expr.UnionPair (s1,r1), Expr.UnionPair (s2,r2)) ->
          (match_setpair s1 s2) @@ (match_setpair r1 r2)
      | (Expr.IntrPair (s1,r1), Expr.IntrPair (s2,r2)) ->
          (match_setpair s1 s2) @@ (match_setpair r1 r2)
      | (Expr.SetdiffPair (s1,r1), Expr.SetdiffPair (s2,r2)) ->
          (match_setpair s1 s2) @@ (match_setpair r1 r2)
      | (Expr.LowerPair (s1,i1), Expr.LowerPair (s2,i2)) ->
          (match_setpair s1 s2) @@ (match_int i1 i2)
      | (Expr.SetPairArrayRd (arr1,t1), Expr.SetPairArrayRd (arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | _ -> ([], false)

    and match_path (pp:Expr.path) (p:Expr.path) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pp,p) with
      | (Expr.VarPath (v), _) -> match_var v Expr.Path (Expr.PathT p)
      | (Expr.Epsilon, Expr.Epsilon) -> ([], true)
      | (Expr.SimplePath (a1), Expr.SimplePath (a2)) ->
          (match_addr a1 a2)
      | (Expr.GetPath (h1,a1,b1), Expr.GetPath (h2,a2,b2)) ->
          (match_mem h1 h2) @@ (match_addr a1 a2) @@
          (match_addr b1 b2)
      | (Expr.GetPathAt (h1,a1,b1,i1), Expr.GetPathAt (h2,a2,b2,i2)) ->
          (match_mem h1 h2) @@ (match_addr a1 a2) @@
          (match_addr b1 b2) @@ (match_int i1 i2)
      | (Expr.PathArrayRd(arr1,t1), Expr.PathArrayRd(arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | _ -> ([], false)

    and match_mem (pm:Expr.mem) (m:Expr.mem) :
        ((Expr.V.t * Expr.term) list * bool) =
      match (pm,m) with
      | (Expr.VarMem (v), _) -> match_var v Expr.Mem (Expr.MemT m)
      | (Expr.Update(h1,a1,c1), Expr.Update(h2,a2,c2)) ->
          (match_mem h1 h2) @@ (match_addr a1 a2) @@
          (match_cell c1 c2)
      | (Expr.MemArrayRd(arr1,t1), Expr.MemArrayRd(arr2,t2)) ->
          (match_array arr1 arr2) @@ (match_tid t1 t2)
      | _ -> ([], false) in

    let prems' = GSet.empty () in
    GSet.iter (fun (pl,b) ->
      if b then
        ()
      else
        begin
          let (assigns, res) = match_lit pl l in
          GSet.add prems' (pl, res);
          List.iter (fun (v,t) ->
            let v_info = Hashtbl.find case.vars v in
            Hashtbl.replace case.vars v { v_sort = v_info.v_sort;
                                          v_term = Expr.TermSet.add t v_info.v_term; }
          ) assigns
        end
      (* If l matches any literal in the premises:
        + Check if c.vars.v_sort matches the sort of the variable in the
          literal.
        + Add the term to which is equal to c.v_term set.
        + Set c.premises of the literal to true.
       *)
    ) case.premises;
    { vars = case.vars;
      premises = prems';
      result = case.result; } in

  let apply_case (cs:axiom_case_t list) : Expr.formula =
    (* Traverse the cases and apply conversion if possible (if case flag is true).
     * Use variable assignment from the tuple to replace variables in the resulting
     * formula.) *)
    let phi_list = List.fold_left (fun xs c ->
                     if GSet.for_all (fun (_,b) -> b) c.premises then
                       begin
                         let subst_list =
                           Hashtbl.fold (fun v info ys ->
                             (v, Expr.TermSet.choose info.v_term) :: ys
                           ) c.vars [] in
                         let v_subst = Expr.new_var_term_subst subst_list in
                         (Expr.subst_var_term v_subst c.result) :: xs
                       end
                     else
                       xs
                   ) [] cs in
    Formula.conj_list phi_list in


  (* Updates the cases, setting which rules can be applied according to
   * the received list of literals *)
  let apply_if_possible (cases:axiom_case_t list) (ls:Expr.literal list) : Expr.formula =
    let cases' = List.fold_left (fun cs l ->
                   List.map (fun c ->
                     find_matching_case c l
                   ) cs
                 ) cases ls in
    (* If for some case all premises are true, then apply the case *)
    apply_case cases' in

  try
    let ax_cases = Hashtbl.find tbl ax_tag in
    let phi_conj = Formula.to_conj_list phi in
    let get_lits f = Formula.to_conj_literals (Formula.nnf f) in
    let phi' =
          Formula.conj_list (
            List.map (fun conj ->
              let phi' = match conj with
                         | Formula.Literal lit ->
                             begin
                               apply_if_possible ax_cases [lit]
                             end
                         | Formula.Implies (ante,conseq) ->
                             begin
                               let ante_lits = get_lits ante in
                               let conseq_lits = get_lits conseq in
                                 phi
                             end
                         | Formula.And _ ->
                             begin
                               let lits = get_lits conj in
                                 phi
                             end
                         | _ -> phi in
              phi'
            ) phi_conj
          ) in
    reset_axiom tbl ax_tag;
    phi'
  with _ -> phi
