
open LeapLib
open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module SL       = TSLExpression
module SLInterf = TSLInterface
(*module type SLK = TSLKExpression.S *)



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
                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in
(*                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in *)
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
                       (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                       (SLK.AddrToSet(m',a1',n'))) :: (!xs)
(*
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelSucc n')))
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',n')))) :: (!xs)*)
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
                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in
(*                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in *)
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
                        (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                        (SLK.AddrToSet(m',a1',n')))) :: (!xs)

(*
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelSucc n')))
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',n'))))) :: (!xs)
*)
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
      verbstr (Interface.Msg.info "TSL CONJUNCTIVE FORMULA TO TRANSLATE"
        (String.concat "\n" (List.map SL.literal_to_str tsl_ls)));
      Hashtbl.clear addrarr_tbl;
      Hashtbl.clear tidarr_tbl;
      let tslk_ps = List.map trans_literal tsl_ls in
      let tslk_phi = SLK.conj_list tslk_ps in
      verbstr (Interface.Msg.info "OBTAINED TSLK TRANSLATED FORMULA"
        (SLK.formula_to_str tslk_phi));
      tslk_phi
  end



let is_sat_plus_info (lines : int)
           (co : Smp.cutoff_strategy_t)
           (phi : SL.formula) : (bool * int * (DP.t, int) Hashtbl.t) =
    print_endline "HERE";
    (false, 0, Hashtbl.create 10)


let is_sat (lines : int)
           (co : Smp.cutoff_strategy_t)
           (phi : SL.formula) : bool =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = is_sat_plus_info lines co phi in s


let is_valid_plus_info (prog_lines:int)
                       (co:Smp.cutoff_strategy_t)
                       (phi:SL.formula) : (bool * int * (DP.t, int) Hashtbl.t) =
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
  if !comp_model then
    print_endline (model_to_str())
  else
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
