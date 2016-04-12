open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module HM       = ThmExpression
module TLL      = TllExpression
module E        = Expression
module F        = Formula

let solver_impl = ref ""

let use_quantifier = ref false

let choose (s:string) : unit =
  solver_impl := s

let comp_model : bool ref = ref false

let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()

(*
let tll_sort_map = ref (GM.new_sort_map())
let tll_model = ref (GM.new_model())
*)

let this_call_tbl : DP.call_tbl_t = DP.new_call_tbl()

module TllSol = (val TllSolver.choose !solver_impl : TllSolver.S)


(* The tables containing thread identifiers, locks and buckets variables
   representing arrays *)
let tidarr_tbl : (HM.tidarr, TLL.tid list) Hashtbl.t =
  Hashtbl.create 8

let lockarr_tbl : (HM.lockarr, TLL.tid list) Hashtbl.t =
  Hashtbl.create 8

let bucketarr_tbl : (HM.bucketarr, (TLL.addr * TLL.addr * TLL.set * TLL.tid) list) Hashtbl.t =
  Hashtbl.create 8


let tid_thm_to_tll (t:HM.tid) : TLL.tid =
  TllInterface.tid_to_tll_tid(ThmInterface.tid_to_expr_tid t)

let term_thm_to_term (t:HM.term) : TLL.term =
  TllInterface.term_to_tll_term(ThmInterface.term_to_expr_term t)

let set_thm_to_tll (s:HM.set) : TLL.set =
  TllInterface.set_to_tll_set(ThmInterface.set_to_expr_set s)

let elem_thm_to_tll (e:HM.elem) : TLL.elem =
  TllInterface.elem_to_tll_elem(ThmInterface.elem_to_expr_elem e)

let addr_thm_to_tll (a:HM.addr) : TLL.addr =
  TllInterface.addr_to_tll_addr(ThmInterface.addr_to_expr_addr a)

let cell_thm_to_tll (c:HM.cell) : TLL.cell =
  TllInterface.cell_to_tll_cell(ThmInterface.cell_to_expr_cell c)

let setth_thm_to_tll (s:HM.setth) : TLL.setth =
  TllInterface.setth_to_tll_setth(ThmInterface.setth_to_expr_setth s)

let setelem_thm_to_tll (s:HM.setelem) : TLL.setelem =
  TllInterface.setelem_to_tll_setelem(ThmInterface.setelem_to_expr_setelem s)

let path_thm_to_tll (p:HM.path) : TLL.path =
  TllInterface.path_to_tll_path(ThmInterface.path_to_expr_path p)

let mem_thm_to_tll (m:HM.mem) : TLL.mem =
  TllInterface.mem_to_tll_mem(ThmInterface.mem_to_expr_mem m)

let int_thm_to_tll (i:HM.integer) : TLL.integer =
  TllInterface.int_to_tll_int(ThmInterface.int_to_expr_int i)


let construct_fresh_name (v:HM.V.t) : string =
  let id_str = HM.V.id v in
  let pr_str = if HM.V.is_primed v then "_prime" else "" in
  let th_str = match HM.V.parameter v with
               | HM.V.Shared -> ""
               | HM.V.Local t -> "_" ^ (HM.V.to_str t) in
  let p_str = match HM.V.scope v with
              | HM.V.GlobalScope -> ""
              | HM.V.Scope p -> p ^ "_" in
  p_str ^ id_str ^ th_str ^ pr_str


let build_conv_var (id:string) (s:TLL.sort) : TLL.V.t =
  TLL.build_var id s false TLL.V.Shared TLL.V.GlobalScope ~fresh:true


let fresh_lock_var (v:HM.V.t) : TLL.V.t =
  let new_id = (construct_fresh_name v) ^ "__fresh" in
  let v_fresh = build_conv_var new_id TLL.Tid in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let fresh_bucket_init_var (v:HM.V.t) : TLL.V.t =
  let new_id = (construct_fresh_name v) ^ "__binit" in
  let v_fresh = build_conv_var new_id TLL.Addr in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let fresh_bucket_end_var (v:HM.V.t) : TLL.V.t =
  let new_id = (construct_fresh_name v) ^ "__bend" in
  let v_fresh = build_conv_var new_id TLL.Addr in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let fresh_bucket_reg_var (v:HM.V.t) : TLL.V.t =
  let new_id = (construct_fresh_name v) ^ "__breg" in
  let v_fresh = build_conv_var new_id TLL.Set in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let fresh_bucket_tid_var (v:HM.V.t) : TLL.V.t =
  let new_id = (construct_fresh_name v) ^ "__btid" in
  let v_fresh = build_conv_var new_id TLL.Tid in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let expand_array_to_var (v:HM.V.t)
                        (s:TLL.sort)
                        (n:int) : TLL.V.t =
  let new_id = (construct_fresh_name v) ^ "__" ^ (string_of_int n) in
  let v_fresh = build_conv_var new_id s in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let expand_bucketarray_to_var (v:HM.V.t)
                              (n:int) : (TLL.V.t * TLL.V.t * TLL.V.t * TLL.V.t) =
  let nStr = string_of_int n in
  let new_v_init = (construct_fresh_name v) ^ "__binit__" ^ nStr in
  let new_v_end = (construct_fresh_name v) ^ "__bend__" ^ nStr in
  let new_v_reg = (construct_fresh_name v) ^ "__breg__" ^ nStr in
  let new_v_tid = (construct_fresh_name v) ^ "__btid__" ^ nStr in
  let v_init_fresh = build_conv_var new_v_init TLL.Addr in
  let v_end_fresh  = build_conv_var new_v_end  TLL.Addr in
  let v_reg_fresh  = build_conv_var new_v_reg  TLL.Set  in
  let v_tid_fresh  = build_conv_var new_v_tid  TLL.Tid  in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_v_init;
  verbl _LONG_INFO "FRESH VAR: %s\n" new_v_end;
  verbl _LONG_INFO "FRESH VAR: %s\n" new_v_reg;
  verbl _LONG_INFO "FRESH VAR: %s\n" new_v_tid;
  (v_init_fresh, v_end_fresh, v_reg_fresh, v_tid_fresh)



let gen_tid_list (levels:int) (tt:HM.tidarr) : TLL.tid list =
  let xs = ref [] in
  for n = levels downto 0 do
    let v = match tt with
            | HM.VarTidArray v ->
                TLL.VarTh (expand_array_to_var v TLL.Tid n)
            | _ -> TLL.NoTid in
    xs := v::(!xs)
  done;
  verbl _LONG_INFO "**** THM Solver, generated thread id list for %s: [%s]\n"
          (HM.tidarr_to_str tt)
          (String.concat ";" (List.map TLL.tid_to_str !xs));
  !xs


let gen_lock_list (levels:int) (ll:HM.lockarr) : TLL.tid list =
  let xs = ref [] in
  for n = levels downto 0 do
    let v = match ll with
            | HM.VarLockArray v ->
                TLL.VarTh (expand_array_to_var v TLL.Tid n)
            | _ -> TLL.NoTid in
    xs := v::(!xs)
  done;
  verbl _LONG_INFO "**** THM Solver, generated thread id list for %s: [%s]\n"
          (HM.lockarr_to_str ll)
          (String.concat ";" (List.map TLL.tid_to_str !xs));
  !xs


let gen_bucket_list (levels:int) (bb:HM.bucketarr) :
    (TLL.addr * TLL.addr * TLL.set * TLL.tid) list =
  let xs = ref [] in
  for n = levels downto 0 do
    let vs = match bb with
             | HM.VarBucketArray v ->
                 begin
                   let (a,e,s,t) = expand_bucketarray_to_var v n in
                   (TLL.VarAddr a, TLL.VarAddr e, TLL.VarSet s, TLL.VarTh t)
                 end
             | _ -> (TLL.Null, TLL.Null, TLL.EmptySet, TLL.NoTid) in
    xs := vs::(!xs)
  done;
  verbl _LONG_INFO "**** THM Solver, generated bucket id list for %s: [%s]\n"
          (HM.bucketarr_to_str bb)
          (String.concat ";" (List.map (fun (a,e,s,t) ->
                                (TLL.addr_to_str a) ^ "," ^
                                (TLL.addr_to_str e) ^ "," ^
                                (TLL.set_to_str  s) ^ "," ^
                                (TLL.tid_to_str  t)
                              ) !xs));
  !xs


let get_tid_list (levels:int) (tt:HM.tidarr) : TLL.tid list =
  try
    Hashtbl.find tidarr_tbl tt
  with _ -> begin
    let tt' = gen_tid_list levels tt in
    Hashtbl.add tidarr_tbl tt tt'; tt'
  end


let get_lock_list (levels:int) (ll:HM.lockarr) : TLL.tid list =
  try
    Hashtbl.find lockarr_tbl ll
  with _ -> begin
    let ll' = gen_lock_list levels ll in
    Hashtbl.add lockarr_tbl ll ll'; ll'
  end


let get_bucket_list (levels:int) (bb:HM.bucketarr) :
    (TLL.addr * TLL.addr * TLL.set * TLL.tid) list =
  try
    Hashtbl.find bucketarr_tbl bb
  with _ -> begin
    let bb' = gen_bucket_list levels bb in
    Hashtbl.add bucketarr_tbl bb bb'; bb'
  end


let find_position (levels:int)
                  (alpha_opt:E.integer list list option)
                  (k:HM.integer) : int =
  match alpha_opt with
  | None -> 0
  | Some alpha ->
      begin
        let k_id = match k with
                   | HM.VarInt v -> HM.V.id v
                   | _ -> "" in
        let (i,found) =
          List.fold_left (fun (i,b) xs ->
            match (i,b) with
            | (_,true)  -> (i,b)
            | (_,false) -> begin
                             if List.exists (fun j ->
                                 match j with
                                 | E.VarInt v -> (E.V.id v) == k_id
                                 | _ -> false) xs then
                               (i,true)
                             else
                               (i+1,false)
                           end
          ) (0,false) alpha in
        if found then i else 0
      end


(***********************************)
(**                               **)
(**  Translation from THM to TLL  **)
(**                               **)
(***********************************)

let rec trans_literal (alpha_r:E.integer list list option)
                      (levels:int)
                      (l:HM.literal) : TLL.formula =
  verbl _LONG_INFO "**** THM Solver. Literal to be translated: %s\n"
    (HM.literal_to_str l);
  match l with
  (* A != B (thread identifiers) *)
  | F.NegAtom(HM.Eq(HM.TidArrayT(HM.VarTidArray _ as tt),
               HM.TidArrayT(HM.VarTidArray _ as uu)))
  | F.Atom(HM.InEq(HM.TidArrayT(HM.VarTidArray _ as tt),
              HM.TidArrayT(HM.VarTidArray _ as uu))) ->
      let tt' = get_tid_list levels tt in
      let uu' = get_tid_list levels uu in
      let xs = ref [] in
      for i = 0 to levels do
        xs := (TLL.ineq_tid (List.nth tt' i) (List.nth uu' i)) :: (!xs)
      done;
      (* I need one witness for array difference *)
      TLL.tid_mark_smp_interesting (List.hd tt') true;
      F.disj_list (!xs)
  (* t = A[i] *)
  | F.Atom(HM.Eq(HM.TidT t, HM.TidT (HM.TidArrRd (tt,i))))
  | F.Atom(HM.Eq(HM.TidT (HM.TidArrRd (tt,i)), HM.TidT t))
  | F.NegAtom(HM.InEq(HM.TidT t, HM.TidT (HM.TidArrRd (tt,i))))
  | F.NegAtom(HM.InEq(HM.TidT (HM.TidArrRd (tt,i)), HM.TidT t)) ->
      let t' = tid_thm_to_tll t in
      let tt' = get_tid_list levels tt in
      let i' = int_thm_to_tll i in
      let xs = ref [] in
      for n = 0 to levels do
        let n' = TLL.IntVal n in
        xs := (F.Implies
                (TLL.eq_int i' n',
                 TLL.eq_tid t' (List.nth tt' n))) :: (!xs)
      done;
      TLL.tid_mark_smp_interesting t' true;
      F.conj_list (!xs)
  (* t != A[i] *)
  | F.NegAtom(HM.Eq(HM.TidT t, HM.TidT (HM.TidArrRd (tt,i))))
  | F.NegAtom(HM.Eq(HM.TidT (HM.TidArrRd (tt,i)), HM.TidT t))
  | F.Atom(HM.InEq(HM.TidT t, HM.TidT (HM.TidArrRd (tt,i))))
  | F.Atom(HM.InEq(HM.TidT (HM.TidArrRd (tt,i)), HM.TidT t)) ->
      F.Not (trans_literal alpha_r levels (F.Atom(HM.Eq(HM.TidT t, HM.TidT (HM.TidArrRd (tt,i))))))
  (* U = T {l <- t} *)
  | F.Atom(HM.Eq(HM.TidArrayT uu, HM.TidArrayT (HM.TidArrayUp(tt,i,t))))
  | F.Atom(HM.Eq(HM.TidArrayT (HM.TidArrayUp(tt,i,t)), HM.TidArrayT uu))
  | F.NegAtom(HM.InEq(HM.TidArrayT uu, HM.TidArrayT (HM.TidArrayUp(tt,i,t))))
  | F.NegAtom(HM.InEq(HM.TidArrayT (HM.TidArrayUp(tt,i,t)), HM.TidArrayT uu)) ->
      let t' = tid_thm_to_tll t in
      let i' = int_thm_to_tll i in
      let tt' = get_tid_list levels tt in
      let uu' = get_tid_list levels uu in
      let xs = ref [] in
      for n = 0 to levels do
        let n' = TLL.IntVal n in
        xs := (F.Implies
                (TLL.eq_int i' n',
                 TLL.eq_tid t' (List.nth uu' n))) ::
              (F.Implies
                (TLL.ineq_int i' n',
                 TLL.eq_tid (List.nth tt' n) (List.nth uu' n))) ::
              (!xs)
      done;
      TLL.tid_mark_smp_interesting t' true;
      F.conj_list (!xs)
  (* U != T {l <- t} *)
  | F.NegAtom(HM.Eq(HM.TidArrayT uu, HM.TidArrayT (HM.TidArrayUp(tt,i,t))))
  | F.NegAtom(HM.Eq(HM.TidArrayT (HM.TidArrayUp(tt,i,t)), HM.TidArrayT uu))
  | F.Atom(HM.InEq(HM.TidArrayT uu, HM.TidArrayT (HM.TidArrayUp(tt,i,t))))
  | F.Atom(HM.InEq(HM.TidArrayT (HM.TidArrayUp(tt,i,t)), HM.TidArrayT uu)) ->
      F.Not (trans_literal alpha_r levels (F.Atom(HM.Eq(HM.TidArrayT uu, HM.TidArrayT (HM.TidArrayUp(tt,i,t))))))
  (* l = mklock(t) *)
  | F.Atom(HM.Eq(HM.LockT(HM.VarLock l), HM.LockT(HM.MkLock(t))))
  | F.Atom(HM.Eq(HM.LockT(HM.MkLock(t)), HM.LockT(HM.VarLock l)))
  | F.NegAtom(HM.InEq(HM.LockT(HM.VarLock l), HM.LockT(HM.MkLock(t))))
  | F.NegAtom(HM.InEq(HM.LockT(HM.MkLock(t)), HM.LockT(HM.VarLock l))) ->
      let t' = tid_thm_to_tll t in
      TLL.eq_tid (TLL.VarTh (fresh_lock_var l)) t'
  (* L != M (locks) *)
  | F.NegAtom(HM.Eq(HM.LockArrayT(HM.VarLockArray _ as ll),
                    HM.LockArrayT(HM.VarLockArray _ as mm)))
  | F.Atom(HM.InEq(HM.LockArrayT(HM.VarLockArray _ as ll),
                   HM.LockArrayT(HM.VarLockArray _ as mm))) ->
      let ll' = get_lock_list levels ll in
      let mm' = get_lock_list levels mm in
      let xs = ref [] in
      for i = 0 to levels do
        xs := (TLL.ineq_tid (List.nth ll' i) (List.nth mm' i)) :: (!xs)
      done;
      (* I need one witness for array difference *)
      TLL.tid_mark_smp_interesting (List.hd ll') true;
      F.disj_list (!xs)
  (* l = L[i] *)
  | F.Atom(HM.Eq(HM.LockT(HM.VarLock l), HM.LockT (HM.LockArrRd (ll,i))))
  | F.Atom(HM.Eq(HM.LockT (HM.LockArrRd (ll,i)), HM.LockT(HM.VarLock l)))
  | F.NegAtom(HM.InEq(HM.LockT(HM.VarLock l), HM.LockT (HM.LockArrRd (ll,i))))
  | F.NegAtom(HM.InEq(HM.LockT (HM.LockArrRd (ll,i)), HM.LockT(HM.VarLock l))) ->
      let l_fresh = TLL.VarTh (fresh_lock_var l) in
      let ll' = get_lock_list levels ll in
      let i' = int_thm_to_tll i in
      let xs = ref [] in
      for n = 0 to levels do
        let n' = TLL.IntVal n in
        xs := (F.Implies
                (TLL.eq_int i' n',
                 TLL.eq_tid l_fresh (List.nth ll' n))) :: (!xs)
      done;
      TLL.tid_mark_smp_interesting l_fresh true;
      F.conj_list (!xs)
  (* l != L[i] *)
  | F.NegAtom(HM.Eq(HM.LockT l, HM.LockT (HM.LockArrRd (ll,i))))
  | F.NegAtom(HM.Eq(HM.LockT (HM.LockArrRd (ll,i)), HM.LockT l))
  | F.Atom(HM.InEq(HM.LockT l, HM.LockT (HM.LockArrRd (ll,i))))
  | F.Atom(HM.InEq(HM.LockT (HM.LockArrRd (ll,i)), HM.LockT l)) ->
      F.Not (trans_literal alpha_r levels (F.Atom(HM.Eq(HM.LockT l, HM.LockT (HM.LockArrRd (ll,i))))))
  (* M = L {i <- l} *)
  | F.Atom(HM.Eq(HM.LockArrayT mm, HM.LockArrayT (HM.LockArrayUp(ll,i,(HM.VarLock l)))))
  | F.Atom(HM.Eq(HM.LockArrayT (HM.LockArrayUp(ll,i,(HM.VarLock l))), HM.LockArrayT mm))
  | F.NegAtom(HM.InEq(HM.LockArrayT mm, HM.LockArrayT (HM.LockArrayUp(ll,i,(HM.VarLock l)))))
  | F.NegAtom(HM.InEq(HM.LockArrayT (HM.LockArrayUp(ll,i,(HM.VarLock l))), HM.LockArrayT mm)) ->
      let l_fresh = TLL.VarTh (fresh_lock_var l) in
      let i' = int_thm_to_tll i in
      let ll' = get_lock_list levels ll in
      let mm' = get_lock_list levels mm in
      let xs = ref [] in
      for n = 0 to levels do
        let n' = TLL.IntVal n in
        xs := (F.Implies
                (TLL.eq_int i' n',
                 TLL.eq_tid l_fresh (List.nth mm' n))) ::
              (F.Implies
                (TLL.ineq_int i' n',
                 TLL.eq_tid (List.nth ll' n) (List.nth mm' n))) ::
              (!xs)
      done;
      TLL.tid_mark_smp_interesting l_fresh true;
      F.conj_list (!xs)
  (* U != T {l <- t} *)
  | F.NegAtom(HM.Eq(HM.LockArrayT mm, HM.LockArrayT (HM.LockArrayUp(ll,i,l))))
  | F.NegAtom(HM.Eq(HM.LockArrayT (HM.LockArrayUp(ll,i,l)), HM.LockArrayT mm))
  | F.Atom(HM.InEq(HM.LockArrayT mm, HM.LockArrayT (HM.LockArrayUp(ll,i,l))))
  | F.Atom(HM.InEq(HM.LockArrayT (HM.LockArrayUp(ll,i,l)), HM.LockArrayT mm)) ->
      F.Not (trans_literal alpha_r levels (F.Atom(HM.Eq(HM.LockArrayT mm, HM.LockArrayT (HM.LockArrayUp(ll,i,l))))))
  (* b = mkbucket(a,e,s,t) *)
  | F.Atom(HM.Eq(HM.BucketT(HM.VarBucket b), HM.BucketT(HM.MkBucket(a,e,s,t))))
  | F.Atom(HM.Eq(HM.BucketT(HM.MkBucket(a,e,s,t)), HM.BucketT(HM.VarBucket b)))
  | F.NegAtom(HM.InEq(HM.BucketT(HM.VarBucket b), HM.BucketT(HM.MkBucket(a,e,s,t))))
  | F.NegAtom(HM.InEq(HM.BucketT(HM.MkBucket(a,e,s,t)), HM.BucketT(HM.VarBucket b))) ->
      print_endline "TRANSLATING A MKBUCKET";
      let b_init = fresh_bucket_init_var b in
      let b_end = fresh_bucket_end_var b in
      let b_reg = fresh_bucket_reg_var b in
      let b_tid = fresh_bucket_tid_var b in
      let a' = addr_thm_to_tll a in
      let e' = addr_thm_to_tll e in
      let s' = set_thm_to_tll s in
      let t' = tid_thm_to_tll t in
      F.conj_list [TLL.eq_addr (TLL.VarAddr b_init) a';
                   TLL.eq_addr (TLL.VarAddr b_end ) e';
                   TLL.eq_set  (TLL.VarSet  b_reg ) s';
                   TLL.eq_tid  (TLL.VarTh   b_tid ) t']
  (* b1 = b2 *)
  | F.Atom(HM.Eq(HM.BucketT(HM.VarBucket b1), HM.BucketT(HM.VarBucket b2)))
  | F.NegAtom(HM.InEq(HM.BucketT(HM.VarBucket b1), HM.BucketT(HM.VarBucket b2))) ->
      print_endline "TRANSLATING EQUALITY BETWEEN BUCKETS";
      let b1_init = fresh_bucket_init_var b1 in
      let b1_end = fresh_bucket_end_var b1 in
      let b1_reg = fresh_bucket_reg_var b1 in
      let b1_tid = fresh_bucket_tid_var b1 in
      let b2_init = fresh_bucket_init_var b2 in
      let b2_end = fresh_bucket_end_var b2 in
      let b2_reg = fresh_bucket_reg_var b2 in
      let b2_tid = fresh_bucket_tid_var b2 in
      F.conj_list [TLL.eq_addr (TLL.VarAddr b1_init) (TLL.VarAddr b2_init);
                   TLL.eq_addr (TLL.VarAddr b1_end ) (TLL.VarAddr b2_end);
                   TLL.eq_set  (TLL.VarSet  b1_reg ) (TLL.VarSet b2_reg);
                   TLL.eq_tid  (TLL.VarTh   b1_tid ) (TLL.VarTh b2_tid)]
  (* b1 != b2 *)
  | F.Atom(HM.InEq(HM.BucketT(HM.VarBucket b1), HM.BucketT(HM.VarBucket b2)))
  | F.NegAtom(HM.Eq(HM.BucketT(HM.VarBucket b1), HM.BucketT(HM.VarBucket b2))) ->
      print_endline "TRANSLATING INEQUALITY BETWEEN BUCKETS";
      let b1_init = fresh_bucket_init_var b1 in
      let b1_end = fresh_bucket_end_var b1 in
      let b1_reg = fresh_bucket_reg_var b1 in
      let b1_tid = fresh_bucket_tid_var b1 in
      let b2_init = fresh_bucket_init_var b2 in
      let b2_end = fresh_bucket_end_var b2 in
      let b2_reg = fresh_bucket_reg_var b2 in
      let b2_tid = fresh_bucket_tid_var b2 in
      F.disj_list [TLL.ineq_addr (TLL.VarAddr b1_init) (TLL.VarAddr b2_init);
                   TLL.ineq_addr (TLL.VarAddr b1_end ) (TLL.VarAddr b2_end);
                   TLL.ineq_set  (TLL.VarSet  b1_reg ) (TLL.VarSet b2_reg);
                   TLL.ineq_tid  (TLL.VarTh   b1_tid ) (TLL.VarTh b2_tid)]
  (* A != B (buckets) *)
  | F.NegAtom(HM.Eq(HM.BucketArrayT(HM.VarBucketArray _ as bb),
                    HM.BucketArrayT(HM.VarBucketArray _ as cc)))
  | F.Atom(HM.InEq(HM.BucketArrayT(HM.VarBucketArray _ as bb),
                   HM.BucketArrayT(HM.VarBucketArray _ as cc))) ->
      let bb' = get_bucket_list levels bb in
      let cc' = get_bucket_list levels cc in
      let xs = ref [] in
      for i = 0 to levels do
        let (a1,e1,s1,t1) = List.nth bb' i in
        let (a2,e2,s2,t2) = List.nth cc' i in
        xs := [TLL.ineq_addr a1 a2; TLL.ineq_addr e1 e2;
               TLL.ineq_set  s1 s2; TLL.ineq_tid  t1 t2] @ (!xs)
      done;
      (* I need one witness for array difference *)
      let (a,e,s,t) = List.hd bb' in
      TLL.addr_mark_smp_interesting a true;
      TLL.addr_mark_smp_interesting e true;
      TLL.tid_mark_smp_interesting t true;
      F.disj_list (!xs)
  (* b = A[i] *)
  | F.Atom(HM.Eq(HM.BucketT(HM.VarBucket b), HM.BucketT (HM.BucketArrRd (bb,i))))
  | F.Atom(HM.Eq(HM.BucketT (HM.BucketArrRd (bb,i)), HM.BucketT(HM.VarBucket b)))
  | F.NegAtom(HM.InEq(HM.BucketT(HM.VarBucket b), HM.BucketT (HM.BucketArrRd (bb,i))))
  | F.NegAtom(HM.InEq(HM.BucketT (HM.BucketArrRd (bb,i)), HM.BucketT(HM.VarBucket b))) ->
      let a_fresh = TLL.VarAddr (fresh_bucket_init_var b) in
      let e_fresh = TLL.VarAddr (fresh_bucket_end_var b) in
      let s_fresh = TLL.VarSet  (fresh_bucket_reg_var b) in
      let t_fresh = TLL.VarTh   (fresh_bucket_tid_var b) in
      let bb' = get_bucket_list levels bb in
      let i' = int_thm_to_tll i in
      let xs = ref [] in
      for n = 0 to levels do
        let n' = TLL.IntVal n in
        let (a,e,s,t) = List.nth bb' n in
        xs := (F.Implies
                (TLL.eq_int i' n',
                 F.conj_list [TLL.eq_addr a_fresh a; TLL.eq_addr e_fresh e;
                              TLL.eq_set  s_fresh s; TLL.eq_tid  t_fresh t])) :: (!xs)
      done;
      TLL.addr_mark_smp_interesting a_fresh true;
      TLL.addr_mark_smp_interesting e_fresh true;
      TLL.tid_mark_smp_interesting t_fresh true;
      F.conj_list (!xs)
  (* b != A[i] *)
  | F.NegAtom(HM.Eq(HM.BucketT b, HM.BucketT (HM.BucketArrRd (bb,i))))
  | F.NegAtom(HM.Eq(HM.BucketT (HM.BucketArrRd (bb,i)), HM.BucketT b))
  | F.Atom(HM.InEq(HM.BucketT b, HM.BucketT (HM.BucketArrRd (bb,i))))
  | F.Atom(HM.InEq(HM.BucketT (HM.BucketArrRd (bb,i)), HM.BucketT b)) ->
      F.Not (trans_literal alpha_r levels (F.Atom(HM.Eq(HM.BucketT b, HM.BucketT (HM.BucketArrRd (bb,i))))))
  (* C = B {i <- b} *)
  | F.Atom(HM.Eq(HM.BucketArrayT cc, HM.BucketArrayT (HM.BucketArrayUp(bb,i,(HM.VarBucket b)))))
  | F.Atom(HM.Eq(HM.BucketArrayT (HM.BucketArrayUp(bb,i,(HM.VarBucket b))), HM.BucketArrayT cc))
  | F.NegAtom(HM.InEq(HM.BucketArrayT cc, HM.BucketArrayT (HM.BucketArrayUp(bb,i,(HM.VarBucket b)))))
  | F.NegAtom(HM.InEq(HM.BucketArrayT (HM.BucketArrayUp(bb,i,(HM.VarBucket b))), HM.BucketArrayT cc)) ->
      let a_fresh = TLL.VarAddr (fresh_bucket_init_var b) in
      let e_fresh = TLL.VarAddr (fresh_bucket_end_var  b) in
      let s_fresh = TLL.VarSet  (fresh_bucket_reg_var  b) in
      let t_fresh = TLL.VarTh   (fresh_bucket_tid_var  b) in
      let i' = int_thm_to_tll i in
      let bb' = get_bucket_list levels bb in
      let cc' = get_bucket_list levels cc in
      let xs = ref [] in
      for n = 0 to levels do
        let n' = TLL.IntVal n in
        let (ab,eb,sb,tb) = List.nth bb' n in
        let (ac,ec,sc,tc) = List.nth cc' n in
        xs := (F.Implies
                (TLL.eq_int i' n',
                 F.conj_list [TLL.eq_addr a_fresh ac; TLL.eq_addr e_fresh ec;
                              TLL.eq_set  s_fresh sc; TLL.eq_tid  t_fresh tc])) ::
              (F.Implies
                (TLL.ineq_int i' n',
                 F.conj_list [TLL.eq_addr ab ac; TLL.eq_addr eb ec;
                              TLL.eq_set  sb sc; TLL.eq_tid  tb tc])) ::
              (!xs)
      done;
      TLL.addr_mark_smp_interesting a_fresh true;
      TLL.addr_mark_smp_interesting e_fresh true;
      TLL.tid_mark_smp_interesting t_fresh true;
      F.conj_list (!xs)
  (* C != B {i <- b} *)
  | F.NegAtom(HM.Eq(HM.BucketArrayT cc, HM.BucketArrayT (HM.BucketArrayUp(bb,i,b))))
  | F.NegAtom(HM.Eq(HM.BucketArrayT (HM.BucketArrayUp(bb,i,b)), HM.BucketArrayT cc))
  | F.Atom(HM.InEq(HM.BucketArrayT cc, HM.BucketArrayT (HM.BucketArrayUp(bb,i,b))))
  | F.Atom(HM.InEq(HM.BucketArrayT (HM.BucketArrayUp(bb,i,b)), HM.BucketArrayT cc)) ->
      F.Not (trans_literal alpha_r levels (F.Atom(HM.Eq(HM.BucketArrayT cc, HM.BucketArrayT (HM.BucketArrayUp(bb,i,b))))))


  (* hashmap(m,s,se,B,k) *)
  | F.Atom(HM.Hashmap(m,s,se,bb,k)) ->
      let m' = mem_thm_to_tll m in
      let s' = set_thm_to_tll s in
      let se' = setelem_thm_to_tll se in
      let bb' = get_bucket_list levels bb in
      let k' = find_position levels alpha_r k in

      let (a0,e0,s0,t0) = List.nth bb' 0 in

      let vreg_union = List.fold_left (fun u i ->
        let (a,e,s,t) = List.nth bb' i in
          TLL.Union (s,u)
      ) s0 (LeapLib.rangeList 1 k') in
      let eq_s = TLL.eq_set s' vreg_union in
      let eq_setelem = TLL.eq_setelem se' (TLL.SetToElems (s',m')) in

      let list_conj_f (a:TLL.addr) (e:TLL.addr) (s:TLL.set) : TLL.formula =
        F.conj_list [TLL.in_addr TLL.Null s;
                     TLL.eq_set s (TLL.AddrToSet(m',a));
                     TLL.in_addr e s;
                     TLL.eq_addr (TLL.Next(TLL.CellAt(m',e))) TLL.Null] in


      let list_conj = List.fold_left (fun c i ->
        let (a,e,s,t) = List.nth bb' i in
        F.And (list_conj_f a e s, c)
      ) (list_conj_f a0 e0 s0) (LeapLib.rangeList 1 k') in


      let disjoint = ref [] in
      for i = 0 to k' do
        let (_,_,si,_) = List.nth bb' i in
        for j = i+1 to k' do
          let (_,_,sj,_) = List.nth bb' j in
            disjoint := (TLL.eq_set (TLL.Intr(si,sj)) TLL.EmptySet) :: (!disjoint)
        done
      done;

      F.conj_list ([eq_s; eq_setelem; list_conj] @ (!disjoint))

  (* ~ hashmap(m,s,se,bb,k) *)
  | F.NegAtom(HM.Hashmap(m,s,se,bb,k)) ->
      let m' = mem_thm_to_tll m in
      let s' = set_thm_to_tll s in
      let se' = setelem_thm_to_tll se in
      let bb' = get_bucket_list levels bb in
      let k' = find_position levels alpha_r k in

      let (a0,e0,s0,t0) = List.nth bb' 0 in

      let vreg_union = List.fold_left (fun u i ->
        let (a,e,s,t) = List.nth bb' i in
          TLL.Union (s,u)
      ) s0 (LeapLib.rangeList 0 k') in

      let ineq_s = TLL.ineq_set s' vreg_union in
      let ineq_setelem = TLL.ineq_setelem se' (TLL.SetToElems (s',m')) in

      let list_disj_f (a:TLL.addr) (e:TLL.addr) (s:TLL.set) : TLL.formula =
        F.disj_list [F.Not (TLL.in_addr TLL.Null s);
                     TLL.ineq_set s (TLL.AddrToSet(m',a));
                     F.Not (TLL.in_addr e s);
                     TLL.ineq_addr (TLL.Next(TLL.CellAt(m',e))) TLL.Null] in

      let list_disj = List.fold_left (fun d i ->
        let (a,e,s,t) = List.nth bb' i in
        F.Or (list_disj_f a e s, d)
      ) (list_disj_f a0 e0 s0) (LeapLib.rangeList 1 k') in

      let disjoint = ref [] in
      for i = 0 to k' do
        let (_,_,si,_) = List.nth bb' i in
        for j = i+1 to k' do
          let (_,_,sj,_) = List.nth bb' j in
            disjoint := (TLL.ineq_set (TLL.Intr(si,sj)) TLL.EmptySet) :: (!disjoint)
        done
      done;

      F.disj_list ([ineq_s; ineq_setelem; list_disj] @ (!disjoint))


  | F.Atom a -> TllInterface.formula_to_tll_formula(
                  ThmInterface.formula_to_expr_formula (Formula.atom_to_formula a))
  | F.NegAtom a -> TllInterface.formula_to_tll_formula(
                     ThmInterface.formula_to_expr_formula (Formula.negatom_to_formula a))



let to_tll (alpha_r:E.integer list list option)
           (levels:int)
           (thm_ls:HM.literal list) : TLL.formula =
  Log.print "ThmSolver. Formula to translate into TLL"
    (String.concat "\n" (List.map HM.literal_to_str thm_ls));
  Hashtbl.clear tidarr_tbl;
  let tll_ps = List.map (trans_literal alpha_r levels) thm_ls in
  let tll_phi = F.conj_list tll_ps in
  Log.print "ThmSolver. Obtained formula in TLL" (TLL.formula_to_str tll_phi);
  tll_phi


(*******************************************)
(*  MACHINERY FOR CHECKING SATISFIABILITY  *)
(*******************************************)


let try_sat_with_presburger_arithmetic (phi:HM.formula) : Sat.t =
  DP.add_dp_calls this_call_tbl DP.Num 1;
  NumSolver.try_sat (ThmInterface.formula_to_expr_formula phi)



(***************************************************)
(**                                               **)
(**  Module instantiation for Arrangement Solver  **)
(**                                               **)
(***************************************************)

let check_thm (levels:int)
              (lines:int)
              (co:Smp.cutoff_strategy_t)
              (arrg_sat_table:(E.integer list list, Sat.t) Hashtbl.t)
              (cf:E.conjunctive_formula)
              (alpha_r:E.integer list list option) : Sat.t =
  match cf with
  | F.TrueConj -> Sat.Sat
  | F.FalseConj -> Sat.Unsat
  | F.Conj ls -> begin
      (* The formula passed to this function does not
       * contains any constant integer value, as this
       * function is called by the arrangements solver when
       * analyzing the NC formula. Hence, I can (and need
       * to) bound the integer variables to the number of
       * available levels in the small model. *)
      let intVars = E.varset_of_sort_from_conj cf E.Int in
      let boundFunc (v:E.V.t) = [F.Atom (E.LessEq (E.IntVal 0, E.VarInt v));
                                 F.Atom (E.Less (E.VarInt v, E.IntVal levels))] in
      let intBoundFormula = E.V.VarSet.fold (fun v cs ->
                              (boundFunc v) @ cs
                            ) intVars [] in
      let fullConj = intBoundFormula @ ls in 
      assert(levels > 0);
      let phi_tll = to_tll alpha_r (levels-1)
                      (List.map ThmInterface.literal_to_thm_literal fullConj) in
      TllSol.compute_model (!comp_model);
      let res = TllSol.check_sat lines co !use_quantifier phi_tll in
      DP.add_dp_calls this_call_tbl DP.Tll 1;
      (*
      tll_sort_map := TllSol.sort_map ();
      tll_model := TllSol.get_model ();
      *)
      if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
        if Sat.is_sat res then print_string "S" else print_string "X";
      let _ = match alpha_r with
              | None -> ()
              | Some a -> Hashtbl.add arrg_sat_table a res in
      res
    end



(*******************************************)
(*  MACHINERY FOR CHECKING SATISFIABILITY  *)
(*******************************************)


module ArrangementSolverOpt =
  struct
    let check_sp_dp = check_thm;
  end

module ArrSol = ArrangementSolver.Make(ArrangementSolverOpt)



let check_sat_plus_info (lines : int)
                        (co : Smp.cutoff_strategy_t)
                        (use_q:bool)
                        (phi : HM.formula) : (Sat.t * int * DP.call_tbl_t) =
    Log.print_ocaml "entering thmsolver check_sat";
    DP.clear_call_tbl this_call_tbl;
    use_quantifier := use_q;
    Log.print "THM Solver formula to check satisfiability" (HM.formula_to_str phi);

    match phi with
    | F.Not(F.Implies(_,F.True)) -> (Sat.Unsat, 1, this_call_tbl)
    | F.Not (F.Implies(F.False, _)) -> (Sat.Unsat, 1, this_call_tbl)
    | F.Implies(F.False, _) -> (Sat.Sat, 1, this_call_tbl)
    | F.Implies(_, F.True) -> (Sat.Sat, 1, this_call_tbl)
    | _ -> let answer =
             try
               ArrSol.try_sat_with_pa
                 (ThmInterface.formula_to_expr_formula phi)
             with _ -> begin
               (* STEP 1: Normalize the formula *)
               (* ERASE *)
               Log.print "THM Solver formula" (HM.formula_to_str phi);
               print_endline "FORMULA TO NORMALIZE:";
               print_endline (HM.formula_to_str phi);
               let phi_norm = HM.normalize phi in
               print_endline "NORMALIZED FORMULA:";
               print_endline (HM.formula_to_str phi_norm);
               (* ERASE *)
               Log.print "THM Solver normalized formula" (HM.formula_to_str phi_norm);
               (* STEP 2: DNF of the normalized formula *)
               let phi_dnf = F.dnf phi_norm in
               (* If any of the conjunctions in DNF is SAT, then phi is sat *)
               if List.exists (fun psi ->
                    Sat.is_sat (ArrSol.dnf_sat lines co
                      (ThmInterface.conj_formula_to_expr_conj_formula psi))
                  ) phi_dnf then
                 Sat.Sat
               else
                 Sat.Unsat
            end in
            (answer, 1, this_call_tbl)


let check_sat (lines : int)
              (co : Smp.cutoff_strategy_t)
              (use_q:bool)
              (phi : HM.formula) : Sat.t =
  let (s,_,_) = check_sat_plus_info lines co use_q phi in s


let check_valid_plus_info (prog_lines:int)
                          (co:Smp.cutoff_strategy_t)
                          (use_q:bool)
                          (phi:HM.formula) : (Valid.t * int * DP.call_tbl_t) =
  let (s,thm_count,tll_count) = check_sat_plus_info prog_lines co use_q
                                    (F.Not phi) in
  (Response.sat_to_valid s, thm_count, tll_count)


let check_valid (prog_lines:int)
                (co:Smp.cutoff_strategy_t)
                (use_q:bool)
                (phi:HM.formula) : Valid.t =
  Response.sat_to_valid (check_sat prog_lines co use_q (F.Not phi))


let compute_model (b:bool) : unit =
  comp_model := b


let model_to_str () : string =
  TllSol.model_to_str()


let print_model () : unit =
  TllSol.print_model()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
