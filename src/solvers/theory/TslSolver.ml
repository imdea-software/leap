
open LeapLib
open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module SL       = TSLExpression
module SLInterf = TSLInterface
(*module type SLK = TSLKExpression.S *)

type alpha_pair_t = (SL.integer list * SL.integer option)

exception UnexpectedLiteral of string


let solver_impl = ref ""


let choose (s:string) : unit =
  solver_impl := s


let comp_model : bool ref = ref false
(* Should we compute a model in case of courter example? *)

let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
(* The structure where we store the options for cutoff *)


(* Intermediate model information between TSL solver interface and
   TSLK solver interface *)
let tslk_sort_map = ref (GM.new_sort_map())
let tslk_model = ref (GM.new_model())


let arr_table = Hashtbl.create 10


let this_call_tbl : DP.call_tbl_t = DP.new_call_tbl()



let gen_fresh_int_var (vs:SL.VarSet.t) : SL.variable =
  let rec find (n:int) : SL.variable =
    let v_cand_id = "fresh_int_" ^ (string_of_int n) in
    let v_cand = SL.build_var v_cand_id SL.Int false SL.Shared SL.GlobalScope
      in
      if SL.VarSet.mem v_cand vs then find (n+1) else v_cand
  in
    find 0



module TranslateTsl (SLK : TSLKExpression.S) =
  struct

    module SLKInterf = TSLKInterface.Make(SLK)


    (* The tables containing addresses and thread identifiers variables
       representing arrays *)
    let addrarr_tbl : (SL.addrarr, SLK.addr list) Hashtbl.t =
      Hashtbl.create 10
    let tidarr_tbl : (SL.tidarr, SLK.tid list) Hashtbl.t =
      Hashtbl.create 10


    let tid_tsl_to_tslk (t:SL.tid) : SLK.tid =
      SLKInterf.tid_to_tslk_tid(SLInterf.tid_to_expr_tid t)

    let term_tsl_to_term (t:SL.term) : SLK.term =
      SLKInterf.term_to_tslk_term(SLInterf.term_to_expr_term t)

    let set_tsl_to_tslk (s:SL.set) : SLK.set =
      SLKInterf.set_to_tslk_set(SLInterf.set_to_expr_set s)

    let elem_tsl_to_tslk (e:SL.elem) : SLK.elem =
      SLKInterf.elem_to_tslk_elem(SLInterf.elem_to_expr_elem e)

    let addr_tsl_to_tslk (a:SL.addr) : SLK.addr =
      SLKInterf.addr_to_tslk_addr(SLInterf.addr_to_expr_addr a)

    let cell_tsl_to_tslk (c:SL.cell) : SLK.cell =
      SLKInterf.cell_to_tslk_cell(SLInterf.cell_to_expr_cell c)

    let setth_tsl_to_tslk (s:SL.setth) : SLK.setth =
      SLKInterf.setth_to_tslk_setth(SLInterf.setth_to_expr_setth s)

    let setelem_tsl_to_tslk (s:SL.setelem) : SLK.setelem =
      SLKInterf.setelem_to_tslk_setelem(SLInterf.setelem_to_expr_setelem s)

    let path_tsl_to_tslk (p:SL.path) : SLK.path =
      SLKInterf.path_to_tslk_path(SLInterf.path_to_expr_path p)

    let mem_tsl_to_tslk (m:SL.mem) : SLK.mem =
      SLKInterf.mem_to_tslk_mem(SLInterf.mem_to_expr_mem m)

    let int_tsl_to_tslk (i:SL.integer) : SLK.level =
      SLKInterf.int_to_tslk_level(SLInterf.int_to_expr_int i)

    let literal_tsl_to_tslk (l:SL.literal) : SLK.literal =
      SLKInterf.literal_to_tslk_literal(SLInterf.literal_to_expr_literal l)


    let expand_array_to_var (v:SL.variable)
                            (s:SLK.sort)
                            (n:int) : SLK.variable =
      let id_str = SL.var_id v in
      let pr_str = if SL.var_is_primed v then "_prime" else "" in
      let th_str = match SL.var_parameter v with
                   | SL.Shared -> ""
                   | SL.Local tid -> "_" ^ (SL.tid_to_str tid) in
      let p_str = match SL.var_scope v with
                  | SL.GlobalScope -> ""
                  | SL.Scope p -> p ^ "_" in
      let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
      let v_fresh = SLK.build_var new_id s false SLK.Shared SLK.GlobalScope in
      verb "FRESH VAR: %s\n" new_id;
      SLK.variable_mark_fresh v_fresh true;
      v_fresh


    let gen_addr_list (aa:SL.addrarr) : SLK.addr list =
      let xs = ref [] in
      for n = (SLK.k - 1) downto 0 do
        let v = match aa with
                | SL.VarAddrArray v ->
                    SLK.VarAddr (expand_array_to_var v SLK.Addr n)
                | SL.CellArr c ->
                    let l = SLK.LevelVal n in
                    SLK.NextAt(cell_tsl_to_tslk c, l)
                | _ -> SLK.Null in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated address list for %s: [%s]\n"
              (SL.addrarr_to_str aa)
              (String.concat ";" (List.map SLK.addr_to_str !xs));
      !xs


    let gen_tid_list (tt:SL.tidarr) : SLK.tid list =
      let xs = ref [] in
      for n = (SLK.k - 1) downto 0 do
        let v = match tt with
                | SL.VarTidArray v ->
                    SLK.VarTh (expand_array_to_var v SLK.Tid n)
                | SL.CellTids c ->
                    let l = SLK.LevelVal n in
                    SLK.CellLockIdAt(cell_tsl_to_tslk c, l)
                | _ -> SLK.NoTid in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated thread id list for %s: [%s]\n"
              (SL.tidarr_to_str tt)
              (String.concat ";" (List.map SLK.tid_to_str !xs));
      !xs



    let get_addr_list (aa:SL.addrarr) : SLK.addr list =
      try
        Hashtbl.find addrarr_tbl aa
      with _ -> begin
        let aa' = gen_addr_list aa in
        Hashtbl.add addrarr_tbl aa aa'; aa'
      end


    let get_tid_list (tt:SL.tidarr) : SLK.tid list =
      try
        Hashtbl.find tidarr_tbl tt
      with _ -> begin
        let tt' = gen_tid_list tt in
        Hashtbl.add tidarr_tbl tt tt'; tt'
      end


    let rec trans_literal (l:SL.literal) : SLK.formula =
      verb "**** TSL Solver. Literal to be translated: %s\n"
            (SL.literal_to_str l);
      match l with
      (* c = mkcell(e,k,A,l) *)
      | SL.Atom(SL.Eq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.Atom(SL.Eq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c)))
      | SL.NegAtom(SL.InEq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.NegAtom(SL.InEq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c))) ->
          let c' = cell_tsl_to_tslk (SL.VarCell c) in
          let e' = elem_tsl_to_tslk e in
          let aa' = get_addr_list aa in
          let tt' = get_tid_list tt in
            SLK.eq_cell (c') (SLK.MkCell(e',aa',tt'))
      (* c != mkcell(e,k,A,l) *)
      | SL.NegAtom(SL.Eq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.NegAtom(SL.Eq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c)))
      | SL.Atom(SL.InEq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | SL.Atom(SL.InEq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c))) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.CellT(SL.VarCell c), SL.CellT(SL.MkCell(e,aa,tt,i))))))
      (* a = c.arr[l] *)
      | SL.Atom(SL.Eq(SL.AddrT a, SL.AddrT(SL.AddrArrRd(SL.CellArr c,l))))
      | SL.Atom(SL.Eq(SL.AddrT(SL.AddrArrRd(SL.CellArr c,l)), SL.AddrT a))
      | SL.NegAtom(SL.InEq(SL.AddrT a, SL.AddrT(SL.AddrArrRd(SL.CellArr c,l))))
      | SL.NegAtom(SL.InEq(SL.AddrT(SL.AddrArrRd(SL.CellArr c,l)), SL.AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          SLK.addr_mark_smp_interesting a' true;
          SLK.eq_addr a' (SLK.NextAt(c',l'))
      (* t = c.tids[l] *)
      | SL.Atom(SL.Eq(SL.TidT t, SL.TidT(SL.TidArrRd(SL.CellTids c,l))))
      | SL.Atom(SL.Eq(SL.TidT(SL.TidArrRd(SL.CellTids c,l)), SL.TidT t))
      | SL.NegAtom(SL.InEq(SL.TidT t, SL.TidT(SL.TidArrRd(SL.CellTids c,l))))
      | SL.NegAtom(SL.InEq(SL.TidT(SL.TidArrRd(SL.CellTids c,l)), SL.TidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          SLK.tid_mark_smp_interesting t' true;
          SLK.eq_tid t' (SLK.CellLockIdAt(c',l'))
      (* A != B (addresses) *)
      | SL.NegAtom(SL.Eq(SL.AddrArrayT(SL.VarAddrArray _ as aa),
                   SL.AddrArrayT(SL.VarAddrArray _ as bb)))
      | SL.Atom(SL.InEq(SL.AddrArrayT(SL.VarAddrArray _ as aa),
                  SL.AddrArrayT(SL.VarAddrArray _ as bb))) ->
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for i = 0 to (SLK.k - 1) do
            xs := (SLK.ineq_addr (List.nth aa' i) (List.nth bb' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          SLK.addr_mark_smp_interesting (List.hd aa') true;
          SLK.disj_list (!xs)
      (* A != B (thread identifiers) *)
      | SL.NegAtom(SL.Eq(SL.TidArrayT(SL.VarTidArray _ as tt),
                   SL.TidArrayT(SL.VarTidArray _ as uu)))
      | SL.Atom(SL.InEq(SL.TidArrayT(SL.VarTidArray _ as tt),
                  SL.TidArrayT(SL.VarTidArray _ as uu))) ->
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for i = 0 to (SLK.k - 1) do
            xs := (SLK.ineq_tid (List.nth tt' i) (List.nth uu' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          SLK.tid_mark_smp_interesting (List.hd tt') true;
          SLK.disj_list (!xs)
      (* a = A[i] *)
      | SL.Atom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.Atom(SL.Eq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a))
      | SL.NegAtom(SL.InEq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.NegAtom(SL.InEq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let aa' = get_addr_list aa in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          SLK.conj_list (!xs)
      (* a != A[i] *)
      | SL.NegAtom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.NegAtom(SL.Eq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a))
      | SL.Atom(SL.InEq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | SL.Atom(SL.InEq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))))
      (* t = A[i] *)
      | SL.Atom(SL.Eq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | SL.Atom(SL.Eq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t))
      | SL.NegAtom(SL.InEq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | SL.NegAtom(SL.InEq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let tt' = get_tid_list tt in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_tid t' (List.nth tt' n))) :: (!xs)
          done;
          SLK.tid_mark_smp_interesting t' true;
          SLK.conj_list (!xs)
      (* t != A[i] *)
      | SL.NegAtom(SL.Eq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | SL.NegAtom(SL.Eq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t))
      | SL.Atom(SL.InEq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | SL.Atom(SL.InEq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))))
      (* B = A {l <- a} *)
      | SL.Atom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.Atom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb))
      | SL.NegAtom(SL.InEq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.NegAtom(SL.InEq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb)) ->
          let a' = addr_tsl_to_tslk a in
          let i' = int_tsl_to_tslk i in
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth bb' n))) ::
                  (SLK.Implies
                    (SLK.ineq_level i' n',
                     SLK.eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                  (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          SLK.conj_list (!xs)
      (* B != A {l <- a} *)
      | SL.NegAtom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.NegAtom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb))
      | SL.Atom(SL.InEq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | SL.Atom(SL.InEq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))))
      (* U = T {l <- t} *)
      | SL.Atom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.Atom(SL.Eq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu))
      | SL.NegAtom(SL.InEq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.NegAtom(SL.InEq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu)) ->
          let t' = tid_tsl_to_tslk t in
          let i' = int_tsl_to_tslk i in
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_tid t' (List.nth uu' n))) ::
                  (SLK.Implies
                    (SLK.ineq_level i' n',
                     SLK.eq_tid (List.nth tt' n) (List.nth uu' n))) ::
                  (!xs)
          done;
          SLK.tid_mark_smp_interesting t' true;
          SLK.conj_list (!xs)
      (* U != T {l <- t} *)
      | SL.NegAtom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.NegAtom(SL.Eq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu))
      | SL.Atom(SL.InEq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | SL.Atom(SL.InEq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu)) ->
          SLK.Not (trans_literal (SL.Atom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))))
      (* Skiplist (m,s,l,s1,s2) *)
      | SL.Atom(SL.Skiplist(m,s,l,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in
          let xs = ref
                    [SLK.Literal(SLK.Atom(
                      SLK.OrderList(m',a1',a2')));
                     SLK.eq_set
                      (s')
(*                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in *)
                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in
(*
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0),
                                          SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in
*)
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := SLK.Implies
                    (SLK.lesseq_level n' l',
                     SLK.And (SLK.atomlit 
                                  (SLK.In(a2',SLK.AddrToSet(m',a1',n'))),
                                  SLK.eq_addr (SLK.NextAt(SLK.CellAt(m',a2'),n'))
                                                   SLK.Null)) :: (!xs);
          done;
          for n = 0 to (SLK.k - 2) do
            let n' = SLK.LevelVal n in
            xs := SLK.Implies
                    (SLK.less_level n' l',
                     SLK.subseteq
(*
                       (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                       (SLK.AddrToSet(m',a1',n'))) :: (!xs)
*)
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelSucc n')))
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',n')))) :: (!xs)
(*
                       (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelSucc n'), SLK.AddrToSet(m',a2',SLK.LevelSucc n')))
                       (SLK.Setdiff (SLK.AddrToSet(m',a1',n'), SLK.AddrToSet(m',a2',n')))) :: (!xs)
*)

          done;
          SLK.addr_mark_smp_interesting a1' true;
          SLK.addr_mark_smp_interesting a2' true;
          SLK.conj_list (!xs)
      (* ~ Skiplist(m,s,l,a1,a2) *)
      | SL.NegAtom(SL.Skiplist(m,s,l,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in


          let xs = ref
                    [SLK.Literal(SLK.NegAtom(
                      SLK.OrderList(m',a1',a2')));
                     SLK.ineq_set
                      (s')
(*                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in *)
                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in
(*                      (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0), SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in *)
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := SLK.And
                    (SLK.lesseq_level n' l',
                     SLK.Or (SLK.Not (SLK.atomlit (SLK.In (a2', SLK.AddrToSet(m',a1',n')))),
                                 SLK.ineq_addr (SLK.NextAt(SLK.CellAt(m',a2'),n'))
                                                    SLK.Null)) :: (!xs)
          done;
          for n = 0 to (SLK.k - 2) do
            let n' = SLK.LevelVal n in
            xs := SLK.And
                    (SLK.less_level n' l',
                     SLK.Not
                      (SLK.subseteq
(*
                        (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                        (SLK.AddrToSet(m',a1',n')))) :: (!xs)
*)

                        (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelSucc n')))
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',n'))))) :: (!xs)

(*
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelSucc n'), SLK.AddrToSet(m',a2',SLK.LevelSucc n')))
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',n'), SLK.AddrToSet(m',a2',n'))))) :: (!xs)
*)
          done;
          SLK.addr_mark_smp_interesting a1' true;
          SLK.addr_mark_smp_interesting a2' true;
          SLK.disj_list (!xs)
      | _ -> SLK.Literal (literal_tsl_to_tslk l)


    let to_tslk (tsl_ls:SL.literal list) : SLK.formula =
      Log.print "TslSolver. Formula to translate into TSLK"
        (String.concat "\n" (List.map SL.literal_to_str tsl_ls));
      Hashtbl.clear addrarr_tbl;
      Hashtbl.clear tidarr_tbl;
      let tslk_ps = List.map trans_literal tsl_ls in
      let tslk_phi = SLK.conj_list tslk_ps in
      Log.print "TslSolver. Obtained formula in TSLK" (SLK.formula_to_str tslk_phi);
      tslk_phi
  end


(*******************************************)
(*  MACHINERY FOR CHECKING SATISFIABILITY  *)
(*******************************************)




let try_sat_with_presburger_arithmetic (phi:SL.formula) : bool =
(*
  print_endline ("Trying to convert formula:\n" ^SL.formula_to_str phi^ "\n");
  let phi_expr = SLInterf.formula_to_expr_formula phi in
  print_endline ("Translation to Expr formula:\n" ^Expression.formula_to_str phi_expr^ "\n");
  let phi_num = NumInterface.formula_to_int_formula phi_expr in
  print_endline ("Translation to Num formula:\n" ^NumExpression.formula_to_str phi_num^ "\n");
*)
  DP.add_dp_calls this_call_tbl DP.Num 1;
  let numSolv_id = BackendSolvers.Yices.identifier in
  let module NumSol = (val NumSolver.choose numSolv_id : NumSolver.S) in
  let phi_num = NumInterface.formula_to_int_formula
                  (SLInterf.formula_to_expr_formula phi)
  in
    NumSol.is_sat phi_num


let split_into_pa_nc (cf:SL.conjunctive_formula)
      : SL.conjunctive_formula *
        SL.conjunctive_formula *
        SL.conjunctive_formula =
  let conj (ls:SL.literal list) : SL.conjunctive_formula =
    match ls with
    | [] -> SL.TrueConj
    | _ -> SL.Conj ls
  in
  match cf with
  | SL.TrueConj  -> (SL.TrueConj,  SL.TrueConj,  SL.TrueConj)
  | SL.FalseConj -> (SL.FalseConj, SL.FalseConj, SL.FalseConj)
  | SL.Conj cf   ->
      let (pa,panc,nc) =
        List.fold_left (fun (pas,pancs,ncs) l ->
          match l with
          (* l = q *)
          | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.IntVal _)))
          | SL.Atom(SL.Eq(SL.IntT(SL.IntVal _),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.IntVal _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.IntVal _),SL.IntT(SL.VarInt _))) -> (l::pas,pancs,ncs)
            (* l1 = l2 *)
          | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
            (* l1 != l2 *)
          | SL.Atom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
            (* l1 = l2 + q *)
          | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.VarInt _, SL.IntVal _))))
          | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.IntVal _, SL.VarInt _))))
          | SL.Atom(SL.Eq(SL.IntT(SL.IntAdd(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | SL.Atom(SL.Eq(SL.IntT(SL.IntAdd(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.VarInt _, SL.IntVal _))))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.IntVal _, SL.VarInt _))))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.IntAdd(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.IntAdd(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
            (* l1 = l2 - q *)
          | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.VarInt _, SL.IntVal _))))
          | SL.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.IntVal _, SL.VarInt _))))
          | SL.Atom(SL.Eq(SL.IntT(SL.IntSub(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | SL.Atom(SL.Eq(SL.IntT(SL.IntSub(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.VarInt _, SL.IntVal _))))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.IntVal _, SL.VarInt _))))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.IntSub(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | SL.NegAtom(SL.InEq(SL.IntT(SL.IntSub(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
            (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
          | SL.Atom(SL.Less(SL.VarInt _,SL.VarInt _))
          | SL.Atom(SL.Greater(SL.VarInt _,SL.VarInt _))
          | SL.NegAtom(SL.LessEq(SL.VarInt _,SL.VarInt _))
          | SL.NegAtom(SL.GreaterEq(SL.VarInt _,SL.VarInt _))
            (* But l1 <= l2 literals appear, as well as they are not compared to constants *)
          | SL.Atom(SL.LessEq(SL.VarInt _,SL.VarInt _))
          | SL.Atom(SL.GreaterEq(SL.VarInt _,SL.VarInt _))
          | SL.NegAtom(SL.Less(SL.VarInt _,SL.VarInt _))
          | SL.NegAtom(SL.Greater(SL.VarInt _,SL.VarInt _)) -> (pas,l::pancs,ncs)
            (* Cases that should not appear at this point after normalization *)
          | SL.Atom(SL.Less(SL.IntVal _,_))          | SL.Atom(SL.Less(_,SL.IntVal _))
          | SL.Atom(SL.Greater(SL.IntVal _,_))       | SL.Atom(SL.Greater(_,SL.IntVal _))
          | SL.NegAtom(SL.LessEq(SL.IntVal _,_))     | SL.NegAtom(SL.LessEq(_,SL.IntVal _))
          | SL.NegAtom(SL.GreaterEq(SL.IntVal _,_))  | SL.NegAtom(SL.GreaterEq(_,SL.IntVal _))
          | SL.Atom(SL.LessEq(SL.IntVal _,_))        | SL.Atom(SL.LessEq(_,SL.IntVal _))
          | SL.Atom(SL.GreaterEq(SL.IntVal _,_))     | SL.Atom(SL.GreaterEq(_,SL.IntVal _))
          | SL.NegAtom(SL.Less(SL.IntVal _,_))       | SL.NegAtom(SL.Less(_,SL.IntVal _))
          | SL.NegAtom(SL.Greater(SL.IntVal _,_))    | SL.NegAtom(SL.Greater(_,SL.IntVal _)) ->
              assert false
            (* Remaining cases *)
          | _ -> (pas,pancs,l::ncs)
        ) ([],[],[]) cf
      in
        (conj pa, conj panc, conj nc)



let guess_arrangements (cf:SL.conjunctive_formula) : (SL.integer list list) 
  GenSet.t =
  let arr = Arr.empty true in
    match cf with
    | SL.FalseConj -> GenSet.empty ()
    | SL.TrueConj  -> GenSet.empty ()
    | SL.Conj ls   -> begin
                            let level_vars = SL.varset_instances_of_sort_from_conj cf (SL.Int) in
                             verb "**** TSL Solver: variables for arrangement...\n{ %s }\n"
                                    (SL.VarSet.fold (fun v str ->
                                      str ^ SL.variable_to_str v ^ "; "
                                    ) level_vars "");
                            SL.VarSet.iter (fun v -> Arr.add_elem arr (SL.VarInt v)) level_vars;
                            List.iter (fun l ->
                              match l with
                              | SL.Atom(SL.Less(i1,i2)) -> Arr.add_less arr i1 i2
                              | SL.Atom(SL.Greater(i1,i2)) -> Arr.add_greater arr i1 i2
                              | SL.Atom(SL.LessEq(i1,i2)) -> Arr.add_lesseq arr i1 i2
                              | SL.Atom(SL.GreaterEq(i1,i2)) -> Arr.add_greatereq arr i1 i2
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                              | SL.Atom(SL.Eq(SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                  if i = 1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                  else if i = -1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntSub(SL.VarInt v2,SL.IntVal i))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntSub(SL.IntVal i,SL.VarInt v2))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.IntSub(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                              | SL.Atom(SL.Eq(SL.IntT (SL.IntSub(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                  if i = 1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i = -1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                  else if i > 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i)))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2)))))
                              | SL.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                              | SL.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                  let v1 = SL.var_set_param (SL.Local th) varr in
                                  if i = 1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                  else if i = -1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.VarInt v2,SL.IntVal i)))))
                              | SL.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.IntVal i,SL.VarInt v2)))))
                              | SL.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                              | SL.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                  let v1 = SL.var_set_param (SL.Local th) varr in
                                  if i = 1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i = -1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                  else if i > 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.Atom(SL.Eq(SL.IntT(SL.VarInt v),SL.IntT(SL.IntVal 0)))
                              | SL.Atom(SL.Eq(SL.IntT(SL.IntVal 0),SL.IntT(SL.VarInt v))) ->
                                  Arr.set_minimum arr (SL.VarInt v)
                              | SL.Atom(SL.Eq(SL.IntT i1,SL.IntT i2)) -> Arr.add_eq arr i1 i2
                              | SL.Atom(SL.InEq(SL.IntT i1,SL.IntT i2)) -> Arr.add_ineq arr i1 i2
                              | SL.NegAtom(SL.Less(i1,i2)) -> Arr.add_greatereq arr i1 i2
                              | SL.NegAtom(SL.Greater(i1,i2)) -> Arr.add_lesseq arr i1 i2
                              | SL.NegAtom(SL.LessEq(i1,i2)) -> Arr.add_greater arr i1 i2
                              | SL.NegAtom(SL.GreaterEq(i1,i2)) -> Arr.add_less arr i1 i2
                              | SL.NegAtom(SL.Eq(SL.IntT i1,SL.IntT i2)) -> Arr.add_ineq arr i1 i2
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i))))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2))))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                  if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i)))))
                              | SL.NegAtom(SL.InEq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2)))))
                              | SL.NegAtom(SL.InEq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                              | SL.NegAtom(SL.InEq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                  let v1 = SL.var_set_param (SL.Local th) varr in
                                  if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                  else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                  else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                              | SL.NegAtom(SL.InEq(SL.IntT(SL.VarInt v),SL.IntT(SL.IntVal 0)))
                              | SL.NegAtom(SL.InEq(SL.IntT(SL.IntVal 0),SL.IntT(SL.VarInt v))) ->
                                  Arr.set_minimum arr (SL.VarInt v)
                              | SL.NegAtom(SL.InEq(SL.IntT i1,SL.IntT i2)) -> Arr.add_eq arr i1 i2
                              | _ -> ()
                            ) ls;
                            Log.print "TSL Solver known information for arrangements"
                                  (Arr.to_str arr SL.int_to_str);
                            let arrgs = try
                                          Hashtbl.find arr_table arr
                                        with
                                          _ -> begin
                                                 let a = Arr.gen_arrs arr in
                                                 Hashtbl.add arr_table arr a;
                                                 a
                                               end
                            in
                            verb "**** TSL Solver: generated %i arrangements\n" (GenSet.size arrgs);
                            arrgs
                          end


let alpha_to_conjunctive_formula (alpha:SL.integer list list)
    : SL.conjunctive_formula =
  let rec cons_eq_class (is:SL.integer list) : SL.literal list =
    match is with
    | i1::i2::xs -> SL.Atom(SL.Eq(SL.IntT i1, SL.IntT i2)) :: cons_eq_class (i2::xs)
    | _          -> []
  in
  let rec cons_ords (arr:SL.integer list list) : SL.literal list =
    match arr with
    | xs::ys::zs -> SL.Atom(SL.Less(List.hd ys,
                              List.hd xs)) :: cons_ords (ys::zs)
    | _          -> []
  in
  let eqs = List.fold_left (fun ys eq_c ->
              (cons_eq_class eq_c) @ ys
            ) [] alpha in
  let ords = cons_ords alpha in
    (SL.Conj (eqs @ ords))


let pumping (cf:SL.conjunctive_formula) : unit =
  match cf with
  | SL.TrueConj  -> ()
  | SL.FalseConj -> ()
  | SL.Conj ls   -> begin
                      let no_arr_updates = ref true in
                      List.iter (fun l ->
                        match l with
                        (* A = B{l <- a} *)
                        | SL.Atom(SL.Eq(_,SL.AddrArrayT(SL.AddrArrayUp(_,i,_))))
                        | SL.Atom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(_,i,_)),_))
                        | SL.NegAtom(SL.InEq(_,SL.AddrArrayT(SL.AddrArrayUp(_,i,_))))
                        | SL.NegAtom(SL.InEq(SL.AddrArrayT(SL.AddrArrayUp(_,i,_)),_)) ->
                            assert (!no_arr_updates); no_arr_updates := false
                        | _ -> ()
                      ) ls
                    end


let relevant_levels (cf:SL.conjunctive_formula) : SL.integer GenSet.t =
  let relevant_set = GenSet.empty() in
  match cf with
  | SL.TrueConj  -> relevant_set
  | SL.FalseConj -> relevant_set
  | SL.Conj ls   -> begin
                      SL.TermSet.iter (fun t ->
                        match t with
                          (* r = addr2set(m,a,l) *)
                        | SL.SetT (SL.AddrToSet(_,_,i))
                          (* p = getp(m,a1,a2,l) *)
                        | SL.PathT (SL.GetPath(_,_,_,i))
                          (* A = B{l <- a} *)
                        | SL.AddrArrayT (SL.AddrArrayUp(_,i,_))
                          (* A = B{l <- t} *)
                        | SL.TidArrayT (SL.TidArrayUp(_,i,_))
                          (* a = A[i] *)
                        | SL.AddrT (SL.AddrArrRd(_,i))
                          (* t = A[i] *)
                        | SL.TidT (SL.TidArrRd(_,i)) -> GenSet.add relevant_set i
                          (* Remaining cases *)
                        | _ -> ()
                      ) (SL.termset_from_conj cf);
                      relevant_set
                    end


let propagate_levels (alpha_pairs:alpha_pair_t list)
                     (panc:SL.conjunctive_formula)
                     (nc:SL.conjunctive_formula)
      : (SL.conjunctive_formula * (* Updated panc         *)
         SL.conjunctive_formula * (* Updated nc           *)
         alpha_pair_t list) =     (* Updated alpha_pairs    *)
  (* A couple of auxiliary functions *)
  (* Given an integer and a alpha_pair_t list, returns the alpha_pair_t list
     section from the eqclass where i was found in decreasing order *)
  let rec keep_lower_or_equals (i:SL.integer) (ps:alpha_pair_t list) : alpha_pair_t list =
    match ps with
    | [] -> []
    | (eqc,_)::xs -> if List.mem i eqc then ps else keep_lower_or_equals i xs in
  let rec find_highest_lower_bound (i:SL.integer) (ps:alpha_pair_t list) : SL.integer option =
    match ps with
    | [] -> None
    | (_,r)::xs -> if r = None then find_highest_lower_bound i xs else r in
  let filter_non_relevant (cf:SL.conjunctive_formula)
                          (relset:SL.integer GenSet.t) : SL.conjunctive_formula =
    match cf with
    | SL.TrueConj  -> SL.TrueConj
    | SL.FalseConj -> SL.FalseConj
    | SL.Conj ls   -> begin
                        SL.Conj (List.fold_left (fun xs lit ->
                          let v_set = SL.varset_of_sort_from_literal lit SL.Int in
                          if SL.VarSet.for_all (fun v -> GenSet.mem relset (SL.VarInt v)) v_set then
                            lit :: xs
                          else
                            xs
                        ) [] ls)
                      end in

  (* Main function body *)
  let add_zero = ref false in
  let elems_to_zero = ref [] in
  let replacements = Hashtbl.create 10 in
  let alpha_relevant = GenSet.empty() in
  List.iter (fun (eqclass,r) ->
    match r with
    | None   -> ()
    | Some l -> GenSet.add alpha_relevant l;
                List.iter (fun e ->
                  Hashtbl.add replacements (SL.IntT e) (SL.IntT l)
                ) eqclass
  ) alpha_pairs;
  let propagate_levels_in_conj_formula (cf:SL.conjunctive_formula) : SL.conjunctive_formula =
    match cf with
    | SL.TrueConj -> SL.TrueConj
    | SL.FalseConj -> SL.FalseConj
    | SL.Conj ls -> begin
                      let result =
                        SL.Conj (List.map (fun lit ->
                          begin
                            match lit with
                            | SL.Atom(SL.Skiplist(_,_,l,_,_))
                            | SL.Atom(SL.Eq(_,SL.CellT(SL.MkCell(_,_,_,l))))
                            | SL.Atom(SL.Eq(SL.CellT(SL.MkCell(_,_,_,l)),_))
                            | SL.NegAtom(SL.InEq(_,SL.CellT(SL.MkCell(_,_,_,l))))
                            | SL.NegAtom(SL.InEq(SL.CellT(SL.MkCell(_,_,_,l)),_)) ->
                                if not (Hashtbl.mem replacements (SL.IntT l)) then
                                  let lowers = keep_lower_or_equals l alpha_pairs in
                                  let lower_l = match find_highest_lower_bound l lowers with
                                                | None   -> (add_zero := true;
                                                             Log.print "Padding" "adding zero as relevant";
                                                             Log.print "Padding" ("Integer " ^(SL.int_to_str l)^ " will be mapped to zero");
                                                             elems_to_zero := l :: !elems_to_zero;
                                                             SL.IntVal 0)
                                                | Some i -> i in
                                  Hashtbl.add replacements (SL.IntT l) (SL.IntT lower_l)
                            | _ -> ()
                          end;
                          SL.replace_terms_literal replacements lit
                        ) ls) in
                        Log.print "Elements to be mapped to zero" (String.concat ";" (List.map SL.int_to_str !elems_to_zero));
                        result
                      end in
  let new_panc = filter_non_relevant (propagate_levels_in_conj_formula panc) alpha_relevant in
  let new_nc = propagate_levels_in_conj_formula nc in
  let alpha_pairs_with_zero = if !add_zero then
                                alpha_pairs @ [(!elems_to_zero, Some (SL.IntVal 0))]
                              else
                                alpha_pairs
  in
    (new_panc, new_nc, alpha_pairs_with_zero)



let update_arrangement (alpha:SL.integer list list) (rel_set:SL.integer GenSet.t)
      : (SL.integer list * SL.integer option) list =
  List.map (fun eqclass ->
    let r = match List.filter (GenSet.mem rel_set) eqclass with
            | [] -> None
            | x::xs -> Some x in
    (eqclass,r)
  ) alpha


let dnf_sat (lines:int) (co:Smp.cutoff_strategy_t) (cf:SL.conjunctive_formula) : bool =
  Log.print_ocaml "entering TSLSolver dnf_sat";
  Log.print "TSLSolver dnf_sat conjunctive formula" (SL.conjunctive_formula_to_str cf);
  let arrg_sat_table : (SL.integer list list, bool) Hashtbl.t = Hashtbl.create 10 in

  let check_pa (cf:SL.conjunctive_formula) : bool =
    match cf with
    | SL.TrueConj  -> (verb "**** check_pa: true\n"; true)
    | SL.FalseConj -> (verb "**** check_pa: false\n"; false)
    | SL.Conj ls   -> (try_sat_with_presburger_arithmetic
                        (SL.from_conjformula_to_formula cf)) in

  (* Main verification function *)
  let check (pa:SL.conjunctive_formula)
            (panc:SL.conjunctive_formula)
            (nc:SL.conjunctive_formula)
            (alpha:SL.integer list list) : bool =
    Log.print_ocaml "entering TSLSolver check";
    Log.print "PA formula" (SL.conjunctive_formula_to_str pa);
    Log.print "PANC formula" (SL.conjunctive_formula_to_str panc);
    Log.print "NC formula" (SL.conjunctive_formula_to_str nc);
    Log.print "Alpha arrangement" (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map SL.int_to_str xs)) ^ "]") alpha));

    Pervasives.flush (Pervasives.stdout);
    let alpha_phi = alpha_to_conjunctive_formula alpha in
    let pa_sat = check_pa (SL.combine_conj_formula (SL.combine_conj_formula pa panc) alpha_phi) in
    (* TODO: Some arrangements are invalid, as I am not considering literals of the
             form "l2 = l1 + 1" to enforce that l2 should be in the immediately consecutive
             equivalence class of l1
    assert pa_sat;
    *)
    if pa_sat then begin
      (* We have an arrangement candidate *)
      pumping nc;
      let rel_set = relevant_levels nc in
      Log.print "Relevant levels" (GenSet.to_str SL.int_to_str rel_set);

      let alpha_pairs = update_arrangement alpha rel_set in
      let (panc_r, nc_r, alpha_pairs_r) = propagate_levels alpha_pairs panc nc in

      let alpha_pairs_str =
        String.concat ";" (List.map (fun (xs,mi) ->
          (String.concat "," (List.map SL.int_to_str xs)) ^":"^ (match mi with
                                                                 | Some i -> SL.int_to_str i
                                                                 | None -> "None")
        ) alpha_pairs_r) in
      Log.print "ALPHA_PAIRS_R" alpha_pairs_str;

      Log.print "PANC_R" (SL.conjunctive_formula_to_str panc_r);
      Log.print "NC_R" (SL.conjunctive_formula_to_str nc_r);

      let alpha_r = List.rev (List.fold_left (fun xs (eqclass,r) ->
                                match r with
                                | None -> xs
                                | Some relev -> [relev] :: xs
                              ) [] alpha_pairs_r) in

      (* Assertions only *)
      let alpha_relev = GenSet.empty () in
      List.iter (fun eqclass ->
        List.iter (fun e -> GenSet.add alpha_relev e) eqclass
      ) alpha_r;

      let rel_set_plus_zero = GenSet.copy rel_set in
      GenSet.add rel_set_plus_zero (SL.IntVal 0);
      assert (GenSet.subseteq alpha_relev rel_set_plus_zero);
      let panc_r_level_vars = SL.varset_of_sort_from_conj panc_r SL.Int in
      let nc_r_level_vars = SL.varset_of_sort_from_conj nc_r SL.Int in

      Log.print "Alpha relevant" (GenSet.to_str SL.int_to_str alpha_relev);

      if not (SL.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) panc_r_level_vars) then begin
        print_endline ("PANC_R_LEVEL_VARS: " ^ (String.concat ";" (List.map SL.variable_to_str (SL.VarSet.elements panc_r_level_vars))));
        print_endline ("ALPHA_RELEV: " ^ (GenSet.to_str SL.int_to_str alpha_relev));
        print_endline ("PANC_R: " ^ (SL.conjunctive_formula_to_str panc_r));
        print_endline ("ALPHA: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map SL.int_to_str xs)) ^ "]") alpha)));
        print_endline ("PA: " ^ (SL.conjunctive_formula_to_str pa));
        print_endline ("PANC: " ^ (SL.conjunctive_formula_to_str panc));
        print_endline ("NC: " ^ (SL.conjunctive_formula_to_str nc))
      end;

      assert (SL.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) panc_r_level_vars);
      if not (SL.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) nc_r_level_vars) then begin
        print_endline ("NC_R_LEVEL_VARS: " ^ (String.concat ";" (List.map SL.variable_to_str (SL.VarSet.elements nc_r_level_vars))));
        print_endline ("ALPHA_RELEV: " ^ (GenSet.to_str SL.int_to_str alpha_relev));
        print_endline ("NC_R: " ^ (SL.conjunctive_formula_to_str nc_r));
        print_endline ("ALPHA: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map SL.int_to_str xs)) ^ "]") alpha)));
        print_endline ("PA: " ^ (SL.conjunctive_formula_to_str pa));
        print_endline ("PANC: " ^ (SL.conjunctive_formula_to_str panc));
        print_endline ("NC: " ^ (SL.conjunctive_formula_to_str nc))
      end;
      assert (SL.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) nc_r_level_vars);
      List.iter (fun xs -> assert (List.length xs = 1)) alpha_r;
      (* Assertions only *)

      try
        let res = Hashtbl.find arrg_sat_table alpha_r in
        print_string (if res then "$" else "#");
        res
      with Not_found -> begin
        let alpha_r_formula = alpha_to_conjunctive_formula alpha_r in
        let final_formula = List.fold_left SL.combine_conj_formula alpha_r_formula [panc_r;nc_r] in
        match final_formula with
        | SL.TrueConj  -> (print_string "T"; Hashtbl.add arrg_sat_table alpha_r true; true)
        | SL.FalseConj -> (print_string "F"; Hashtbl.add arrg_sat_table alpha_r false; false)
        | SL.Conj ls   -> begin
                            let k = List.length alpha_r in
                            let module TslkSol = (val TslkSolver.choose !solver_impl k
                                           : TslkSolver.S) in
                            TslkSol.compute_model (!comp_model);
                            let module Trans = TranslateTsl (TslkSol.TslkExp) in
                            let phi_tslk = Trans.to_tslk ls in
                            let res = TslkSol.is_sat lines co phi_tslk in
                            DP.add_dp_calls this_call_tbl (DP.Tslk k) 1;
                            tslk_sort_map := TslkSol.get_sort_map ();
                            tslk_model := TslkSol.get_model ();
                            if res then print_string "S" else print_string "X";
                            Hashtbl.add arrg_sat_table alpha_r res;
                            res
                          end
      end
    end else begin
      (* For this arrangement is UNSAT. Return UNSAT. *)
      print_string ".";
      false
    end in


  (* Main body *)
  let (pa,panc,nc) = split_into_pa_nc cf in
  (* We clear the table of previously guessed arrangements *)
  Hashtbl.clear arr_table;
  (* Generate arrangements *)
  assert (Hashtbl.length arrg_sat_table = 0);
  let answer =
    (* If no interesting information in NC formula, then we just check PA and PANC *)
    if nc = SL.TrueConj || nc = SL.FalseConj then begin
      try_sat_with_presburger_arithmetic (SL.from_conjformula_to_formula
                                          (SL.combine_conj_formula pa panc))
    end else begin
      let arrgs = guess_arrangements (SL.combine_conj_formula_list [pa; panc; nc]) in
      (* Verify if some arrangement makes the formula satisfiable *)
      GenSet.exists (fun alpha -> check pa panc nc alpha) arrgs
    end in
  answer


(*******************************************)
(*  MACHINERY FOR CHECKING SATISFIABILITY  *)
(*******************************************)



let is_sat_plus_info (lines : int)
           (co : Smp.cutoff_strategy_t)
           (phi : SL.formula) : (bool * int * DP.call_tbl_t) =
    Log.print_ocaml "entering tslsolver is_sat";
    DP.clear_call_tbl this_call_tbl;
    Log.print "TSL Solver formula to check satisfiability" (SL.formula_to_str phi);

    match phi with
    | SL.Not(SL.Implies(_,SL.True)) -> (false, 1, this_call_tbl)
    | SL.Not (SL.Implies(SL.False, _)) -> (false, 1, this_call_tbl)
    | SL.Implies(SL.False, _) -> (true, 1, this_call_tbl)
    | SL.Implies(_, SL.True) -> (true, 1, this_call_tbl)
    | _ -> let answer =
             try
                try_sat_with_presburger_arithmetic phi
             with _ -> begin
               (* STEP 1: Normalize the formula *)
               (* ERASE *)
               print_endline ("PHI: " ^ (SL.formula_to_str phi));
               let phi_norm = SL.normalize phi in
               (* ERASE *)
               print_endline ("NORM PHI: " ^ (SL.formula_to_str phi_norm));
               Log.print "TSL Solver normalized formula" (SL.formula_to_str phi_norm);
               (* STEP 2: DNF of the normalized formula *)
               let phi_dnf = SL.dnf phi_norm in
               (* If any of the conjunctions in DNF is SAT, then phi is sat *)
               let answer = List.exists (fun psi -> dnf_sat lines co psi) phi_dnf
               in
               answer
            end in
            (answer, 1, this_call_tbl)


let is_sat (lines : int)
           (co : Smp.cutoff_strategy_t)
           (phi : SL.formula) : bool =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = is_sat_plus_info lines co phi in s


let is_valid_plus_info (prog_lines:int)
                       (co:Smp.cutoff_strategy_t)
                       (phi:SL.formula) : (bool * int * DP.call_tbl_t) =
  let (s,tsl_count,tslk_count) = is_sat_plus_info prog_lines co
                                   (SL.Not phi) in
    (not s, tsl_count, tslk_count)


let is_valid (prog_lines:int)
             (co:Smp.cutoff_strategy_t)
             (phi:SL.formula) : bool =
  not (is_sat prog_lines co (SL.Not phi))


let compute_model (b:bool) : unit =
  comp_model := b
    (* Should I enable which solver? *)
    (* Solver.compute_model b *)
    (* Perhaps I should only set the flag and set activate the compute_model
       on the Solver when it is about to be called in is_sat *)


let model_to_str () : string =
  let model = !tslk_model in
  let sort_map = !tslk_sort_map in
  let thid_str = GM.search_type_to_str model sort_map GM.tid_s in
  let pc_str   = GM.search_type_to_str model sort_map GM.loc_s in
  let addr_str = GM.search_type_to_str model sort_map GM.addr_s in
  let elem_str = GM.search_type_to_str model sort_map GM.elem_s in
  let cell_str = GM.search_type_to_str model sort_map GM.cell_s in
  let path_str = GM.search_type_to_str model sort_map GM.path_s in
  let level_str = GM.search_type_to_str model sort_map GM.level_s in
  (* Special description for sets *)
  let set_str = GM.search_sets_to_str model sort_map GM.set_s in
  let setth_str = GM.search_sets_to_str model sort_map GM.setth_s in
  let setelem_str = GM.search_sets_to_str model sort_map GM.setelem_s in
  (* Special description for sets *)
  let heap_str = GM.search_type_to_str model sort_map GM.heap_s
  in
    "\nThreads:\n" ^ thid_str ^
    "\nProgram counters:\n" ^ pc_str ^
    "\nAddresses:\n" ^ addr_str ^
    "\nElements:\n" ^ elem_str ^
    "\nCells:\n" ^ cell_str ^
    "\nPaths:\n" ^ path_str ^
    "\nLevels:\n" ^ level_str ^
    "\nSets:\n" ^ set_str ^
    "\nSets of tids:\n" ^ setth_str ^
    "\nSets of elements:\n" ^ setelem_str ^
    "\nHeap:\n" ^ heap_str


let print_model () : unit =
  if !comp_model && (!tslk_model <> GM.new_model()) then
    print_endline (model_to_str())
  else
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
