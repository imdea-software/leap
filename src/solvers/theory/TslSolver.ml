open LeapLib
open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module SL       = TSLExpression
module SLInterf = TSLInterface
module F = Formula
(*module type SLK = TSLKExpression.S *)

type alpha_pair_t = (SL.integer list * SL.integer option)

exception UnexpectedLiteral of string


let solver_impl = ref ""

let use_quantifier = ref false


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



let gen_fresh_int_var (vs:SL.V.VarSet.t) : SL.V.t =
  let rec find (n:int) : SL.V.t =
    let v_cand_id = "fresh_int_" ^ (string_of_int n) in
    let v_cand = SL.build_var v_cand_id SL.Int false SL.V.Shared SL.V.GlobalScope
      in
      if SL.V.VarSet.mem v_cand vs then find (n+1) else v_cand
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
(*
    let literal_tsl_to_tslk (l:SL.literal) : SLK.literal =
      SLKInterf.literal_to_tslk_literal(SLInterf.literal_to_expr_literal l)
*)


    let expand_array_to_var (v:SL.V.t)
                            (s:SLK.sort)
                            (n:int) : SLK.V.t =
      let id_str = SL.V.id v in
      let pr_str = if SL.V.is_primed v then "_prime" else "" in
      let th_str = match SL.V.parameter v with
                   | SL.V.Shared -> ""
                   | SL.V.Local t -> "_" ^ (SL.V.to_str t) in
      let p_str = match SL.V.scope v with
                  | SL.V.GlobalScope -> ""
                  | SL.V.Scope p -> p ^ "_" in
      let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
      let v_fresh = SLK.build_var new_id s false SLK.V.Shared SLK.V.GlobalScope ~fresh:true in
      verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
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
      verbl _LONG_INFO "**** TSL Solver, generated address list for %s: [%s]\n"
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
      verbl _LONG_INFO "**** TSL Solver, generated thread id list for %s: [%s]\n"
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
      verbl _LONG_INFO "**** TSL Solver. Literal to be translated: %s\n"
            (SL.literal_to_str l);
      match l with
      (* c = mkcell(e,k,A,l) *)
      | F.Atom(SL.Eq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,_))))
      | F.Atom(SL.Eq(SL.CellT(SL.MkCell(e,aa,tt,_)),SL.CellT (SL.VarCell c)))
      | F.NegAtom(SL.InEq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,_))))
      | F.NegAtom(SL.InEq(SL.CellT(SL.MkCell(e,aa,tt,_)),SL.CellT (SL.VarCell c))) ->
          let c' = cell_tsl_to_tslk (SL.VarCell c) in
          let e' = elem_tsl_to_tslk e in
          let aa' = get_addr_list aa in
          let tt' = get_tid_list tt in
            SLK.eq_cell (c') (SLK.MkCell(e',aa',tt'))
      (* c != mkcell(e,k,A,l) *)
      | F.NegAtom(SL.Eq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | F.NegAtom(SL.Eq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c)))
      | F.Atom(SL.InEq(SL.CellT (SL.VarCell c),SL.CellT(SL.MkCell(e,aa,tt,i))))
      | F.Atom(SL.InEq(SL.CellT(SL.MkCell(e,aa,tt,i)),SL.CellT (SL.VarCell c))) ->
          F.Not (trans_literal (F.Atom(SL.Eq(SL.CellT(SL.VarCell c), SL.CellT(SL.MkCell(e,aa,tt,i))))))
      (* a = c.arr[l] *)
      | F.Atom(SL.Eq(SL.AddrT a, SL.AddrT(SL.AddrArrRd(SL.CellArr c,l))))
      | F.Atom(SL.Eq(SL.AddrT(SL.AddrArrRd(SL.CellArr c,l)), SL.AddrT a))
      | F.NegAtom(SL.InEq(SL.AddrT a, SL.AddrT(SL.AddrArrRd(SL.CellArr c,l))))
      | F.NegAtom(SL.InEq(SL.AddrT(SL.AddrArrRd(SL.CellArr c,l)), SL.AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          SLK.addr_mark_smp_interesting a' true;
          SLK.eq_addr a' (SLK.NextAt(c',l'))
      (* t = c.tids[l] *)
      | F.Atom(SL.Eq(SL.TidT t, SL.TidT(SL.TidArrRd(SL.CellTids c,l))))
      | F.Atom(SL.Eq(SL.TidT(SL.TidArrRd(SL.CellTids c,l)), SL.TidT t))
      | F.NegAtom(SL.InEq(SL.TidT t, SL.TidT(SL.TidArrRd(SL.CellTids c,l))))
      | F.NegAtom(SL.InEq(SL.TidT(SL.TidArrRd(SL.CellTids c,l)), SL.TidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          SLK.tid_mark_smp_interesting t' true;
          SLK.eq_tid t' (SLK.CellLockIdAt(c',l'))
      (* A != B (addresses) *)
      | F.NegAtom(SL.Eq(SL.AddrArrayT(SL.VarAddrArray _ as aa),
                   SL.AddrArrayT(SL.VarAddrArray _ as bb)))
      | F.Atom(SL.InEq(SL.AddrArrayT(SL.VarAddrArray _ as aa),
                  SL.AddrArrayT(SL.VarAddrArray _ as bb))) ->
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for i = 0 to (SLK.k - 1) do
            xs := (SLK.ineq_addr (List.nth aa' i) (List.nth bb' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          SLK.addr_mark_smp_interesting (List.hd aa') true;
          F.disj_list (!xs)
      (* A != B (thread identifiers) *)
      | F.NegAtom(SL.Eq(SL.TidArrayT(SL.VarTidArray _ as tt),
                   SL.TidArrayT(SL.VarTidArray _ as uu)))
      | F.Atom(SL.InEq(SL.TidArrayT(SL.VarTidArray _ as tt),
                  SL.TidArrayT(SL.VarTidArray _ as uu))) ->
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for i = 0 to (SLK.k - 1) do
            xs := (SLK.ineq_tid (List.nth tt' i) (List.nth uu' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          SLK.tid_mark_smp_interesting (List.hd tt') true;
          F.disj_list (!xs)
      (* a = A[i] *)
      | F.Atom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | F.Atom(SL.Eq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a))
      | F.NegAtom(SL.InEq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | F.NegAtom(SL.InEq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let aa' = get_addr_list aa in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (F.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          F.conj_list (!xs)
      (* a != A[i] *)
      | F.NegAtom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | F.NegAtom(SL.Eq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a))
      | F.Atom(SL.InEq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))
      | F.Atom(SL.InEq(SL.AddrT (SL.AddrArrRd (aa,i)), SL.AddrT a)) ->
          F.Not (trans_literal (F.Atom(SL.Eq(SL.AddrT a, SL.AddrT (SL.AddrArrRd (aa,i))))))
      (* t = A[i] *)
      | F.Atom(SL.Eq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | F.Atom(SL.Eq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t))
      | F.NegAtom(SL.InEq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | F.NegAtom(SL.InEq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let tt' = get_tid_list tt in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (F.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_tid t' (List.nth tt' n))) :: (!xs)
          done;
          SLK.tid_mark_smp_interesting t' true;
          F.conj_list (!xs)
      (* t != A[i] *)
      | F.NegAtom(SL.Eq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | F.NegAtom(SL.Eq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t))
      | F.Atom(SL.InEq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))
      | F.Atom(SL.InEq(SL.TidT (SL.TidArrRd (tt,i)), SL.TidT t)) ->
          F.Not (trans_literal (F.Atom(SL.Eq(SL.TidT t, SL.TidT (SL.TidArrRd (tt,i))))))
      (* B = A {l <- a} *)
      | F.Atom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | F.Atom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb))
      | F.NegAtom(SL.InEq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | F.NegAtom(SL.InEq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb)) ->
          let a' = addr_tsl_to_tslk a in
          let i' = int_tsl_to_tslk i in
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (F.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth bb' n))) ::
                  (F.Implies
                    (SLK.ineq_level i' n',
                     SLK.eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                  (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          F.conj_list (!xs)
      (* B != A {l <- a} *)
      | F.NegAtom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | F.NegAtom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb))
      | F.Atom(SL.InEq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))
      | F.Atom(SL.InEq(SL.AddrArrayT (SL.AddrArrayUp(aa,i,a)), SL.AddrArrayT bb)) ->
          F.Not (trans_literal (F.Atom(SL.Eq(SL.AddrArrayT bb, SL.AddrArrayT (SL.AddrArrayUp(aa,i,a))))))
      (* U = T {l <- t} *)
      | F.Atom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | F.Atom(SL.Eq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu))
      | F.NegAtom(SL.InEq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | F.NegAtom(SL.InEq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu)) ->
          let t' = tid_tsl_to_tslk t in
          let i' = int_tsl_to_tslk i in
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (F.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_tid t' (List.nth uu' n))) ::
                  (F.Implies
                    (SLK.ineq_level i' n',
                     SLK.eq_tid (List.nth tt' n) (List.nth uu' n))) ::
                  (!xs)
          done;
          SLK.tid_mark_smp_interesting t' true;
          F.conj_list (!xs)
      (* U != T {l <- t} *)
      | F.NegAtom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | F.NegAtom(SL.Eq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu))
      | F.Atom(SL.InEq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))
      | F.Atom(SL.InEq(SL.TidArrayT (SL.TidArrayUp(tt,i,t)), SL.TidArrayT uu)) ->
          F.Not (trans_literal (F.Atom(SL.Eq(SL.TidArrayT uu, SL.TidArrayT (SL.TidArrayUp(tt,i,t))))))
      (* Skiplist (m,s,l,s1,s2) *)
      | F.Atom(SL.Skiplist(m,s,l,a1,a2,es)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in
          let es' = setelem_tsl_to_tslk es in
          let xs = ref
                    [F.atom_to_formula(
                      SLK.OrderList(m',a1',a2'));
                     SLK.eq_setelem es' (SLK.SetToElems(s',m'));
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
            xs := F.Implies
                    (SLK.lesseq_level n' l',
                     F.And (SLK.atomlit 
                                  (SLK.In(a2',SLK.AddrToSet(m',a1',n'))),
                                  SLK.eq_addr (SLK.NextAt(SLK.CellAt(m',a2'),n'))
                                                   SLK.Null)) :: (!xs);
          done;
          for n = 0 to (SLK.k - 2) do
            let n' = SLK.LevelVal n in
            xs := F.Implies
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
          F.conj_list (!xs)
      (* ~ Skiplist(m,s,l,a1,a2) *)
      | F.NegAtom(SL.Skiplist(m,s,l,a1,a2,es)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in
          let es' = setelem_tsl_to_tslk es in


          let xs = ref
                    [F.negatom_to_formula(
                      SLK.OrderList(m',a1',a2'));
                     SLK.ineq_setelem es' (SLK.SetToElems(s',m'));
                     SLK.ineq_set
                      (s')
(*                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in *)
                      (SLK.PathToSet(SLK.GetPathAt(m',a1',a2',SLK.LevelVal 0)))] in
(*                      (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0), SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in *)
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := F.And
                    (SLK.lesseq_level n' l',
                     F.Or (F.Not (F.atom_to_formula (SLK.In (a2', SLK.AddrToSet(m',a1',n')))),
                                 SLK.ineq_addr (SLK.NextAt(SLK.CellAt(m',a2'),n'))
                                                    SLK.Null)) :: (!xs)
          done;
          for n = 0 to (SLK.k - 2) do
            let n' = SLK.LevelVal n in
            xs := F.And
                    (SLK.less_level n' l',
                     F.Not
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
          F.disj_list (!xs)
      | F.Atom a -> SLKInterf.formula_to_tslk_formula(
                       SLInterf.formula_to_expr_formula (Formula.atom_to_formula a))
      | F.NegAtom a -> SLKInterf.formula_to_tslk_formula(
                          SLInterf.formula_to_expr_formula (Formula.negatom_to_formula a))


    let to_tslk (tsl_ls:SL.literal list) : SLK.formula =
      Log.print "TslSolver. Formula to translate into TSLK"
        (String.concat "\n" (List.map SL.literal_to_str tsl_ls));
      Hashtbl.clear addrarr_tbl;
      Hashtbl.clear tidarr_tbl;
      let tslk_ps = List.map trans_literal tsl_ls in
      let tslk_phi = F.conj_list tslk_ps in
      Log.print "TslSolver. Obtained formula in TSLK" (SLK.formula_to_str tslk_phi);
      tslk_phi
  end


(*******************************************)
(*  MACHINERY FOR CHECKING SATISFIABILITY  *)
(*******************************************)




let try_sat_with_presburger_arithmetic (phi:SL.formula) : Sat.t =
  DP.add_dp_calls this_call_tbl DP.Num 1;
  let numSolv_id = BackendSolvers.Yices.identifier in
  let module NumSol = (val NumSolver.choose numSolv_id : NumSolver.S) in
  let phi_num = NumInterface.formula_to_int_formula
                  (SLInterf.formula_to_expr_formula phi)
  in
    NumSol.check_sat phi_num


let split_into_pa_nc (cf:SL.conjunctive_formula)
      : SL.conjunctive_formula *
        SL.conjunctive_formula *
        SL.conjunctive_formula =
  let conj (ls:SL.literal list) : SL.conjunctive_formula =
    match ls with
    | [] -> F.TrueConj
    | _ -> F.Conj ls
  in
  match cf with
  | F.TrueConj  -> (F.TrueConj,  F.TrueConj,  F.TrueConj)
  | F.FalseConj -> (F.FalseConj, F.FalseConj, F.FalseConj)
  | F.Conj cf   ->
      let (pa,panc,nc) =
        List.fold_left (fun (pas,pancs,ncs) l ->
          match l with
          (* l = q *)
          | F.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.IntVal _)))
          | F.Atom(SL.Eq(SL.IntT(SL.IntVal _),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.IntVal _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.IntVal _),SL.IntT(SL.VarInt _))) -> (l::pas,pancs,ncs)
            (* l1 = l2 *)
          | F.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
            (* l1 != l2 *)
          | F.Atom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT(SL.VarInt _)))
            (* l1 = l2 + q *)
          | F.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.VarInt _, SL.IntVal _))))
          | F.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.IntVal _, SL.VarInt _))))
          | F.Atom(SL.Eq(SL.IntT(SL.IntAdd(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | F.Atom(SL.Eq(SL.IntT(SL.IntAdd(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.VarInt _, SL.IntVal _))))
          | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntAdd (SL.IntVal _, SL.VarInt _))))
          | F.NegAtom(SL.InEq(SL.IntT(SL.IntAdd(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.IntAdd(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
            (* l1 = l2 - q *)
          | F.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.VarInt _, SL.IntVal _))))
          | F.Atom(SL.Eq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.IntVal _, SL.VarInt _))))
          | F.Atom(SL.Eq(SL.IntT(SL.IntSub(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | F.Atom(SL.Eq(SL.IntT(SL.IntSub(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.VarInt _, SL.IntVal _))))
          | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt _),SL.IntT (SL.IntSub (SL.IntVal _, SL.VarInt _))))
          | F.NegAtom(SL.InEq(SL.IntT(SL.IntSub(SL.VarInt _,SL.IntVal _)),SL.IntT(SL.VarInt _)))
          | F.NegAtom(SL.InEq(SL.IntT(SL.IntSub(SL.IntVal _,SL.VarInt _)),SL.IntT(SL.VarInt _)))
            (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
          | F.Atom(SL.Less(SL.VarInt _,SL.VarInt _))
          | F.Atom(SL.Greater(SL.VarInt _,SL.VarInt _))
          | F.NegAtom(SL.LessEq(SL.VarInt _,SL.VarInt _))
          | F.NegAtom(SL.GreaterEq(SL.VarInt _,SL.VarInt _))
            (* But l1 <= l2 literals appear, as well as they are not compared to constants *)
          | F.Atom(SL.LessEq(SL.VarInt _,SL.VarInt _))
          | F.Atom(SL.GreaterEq(SL.VarInt _,SL.VarInt _))
          | F.NegAtom(SL.Less(SL.VarInt _,SL.VarInt _))
          | F.NegAtom(SL.Greater(SL.VarInt _,SL.VarInt _)) -> (pas,l::pancs,ncs)
            (* Cases that should not appear at this point after normalization *)
          | F.Atom(SL.Less(SL.IntVal _,_))          | F.Atom(SL.Less(_,SL.IntVal _))
          | F.Atom(SL.Greater(SL.IntVal _,_))       | F.Atom(SL.Greater(_,SL.IntVal _))
          | F.NegAtom(SL.LessEq(SL.IntVal _,_))     | F.NegAtom(SL.LessEq(_,SL.IntVal _))
          | F.NegAtom(SL.GreaterEq(SL.IntVal _,_))  | F.NegAtom(SL.GreaterEq(_,SL.IntVal _))
          | F.Atom(SL.LessEq(SL.IntVal _,_))        | F.Atom(SL.LessEq(_,SL.IntVal _))
          | F.Atom(SL.GreaterEq(SL.IntVal _,_))     | F.Atom(SL.GreaterEq(_,SL.IntVal _))
          | F.NegAtom(SL.Less(SL.IntVal _,_))       | F.NegAtom(SL.Less(_,SL.IntVal _))
          | F.NegAtom(SL.Greater(SL.IntVal _,_))    | F.NegAtom(SL.Greater(_,SL.IntVal _)) ->
              assert false
            (* Remaining cases *)
          | _ -> (pas,pancs,l::ncs)
        ) ([],[],[]) cf
      in
        (conj pa, conj panc, conj nc)



let guess_arrangements (cf:SL.conjunctive_formula) : (SL.integer list list) GenSet.t option =
  let arr = Arr.empty true in
    match cf with
    | F.FalseConj -> Some (GenSet.empty ())
    | F.TrueConj  -> Some (GenSet.empty ())
    | F.Conj ls   -> begin
                        let level_vars = SL.varset_instances_of_sort_from_conj cf (SL.Int) in
                        if SL.V.VarSet.cardinal level_vars = 0 then
                          None
                        else begin
                          verbl _LONG_INFO "**** TSL Solver: variables for arrangement...\n{ %s }\n"
                                  (SL.V.VarSet.fold (fun v str ->
                                    str ^ SL.V.to_str v ^ "; "
                                  ) level_vars "");
                          SL.V.VarSet.iter (fun v -> Arr.add_elem arr (SL.VarInt v)) level_vars;
                          List.iter (fun l ->
                            match l with
                            | F.Atom(SL.Less(i1,i2)) -> Arr.add_less arr i1 i2
                            | F.Atom(SL.Greater(i1,i2)) -> Arr.add_greater arr i1 i2
                            | F.Atom(SL.LessEq(i1,i2)) -> Arr.add_lesseq arr i1 i2
                            | F.Atom(SL.GreaterEq(i1,i2)) -> Arr.add_greatereq arr i1 i2
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i))))
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2))))
                            | F.Atom(SL.Eq(SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                            | F.Atom(SL.Eq(SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                if i = 1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                else if i = -1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntSub(SL.VarInt v2,SL.IntVal i))))
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntSub(SL.IntVal i,SL.VarInt v2))))
                            | F.Atom(SL.Eq(SL.IntT (SL.IntSub(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                            | F.Atom(SL.Eq(SL.IntT (SL.IntSub(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                if i = 1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i = -1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                else if i > 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i < 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i)))))
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2)))))
                            | F.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                            | F.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                let v1 = SL.V.set_param varr (SL.V.Local (SL.voc_to_var th)) in
                                if i = 1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                else if i = -1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.VarInt v2,SL.IntVal i)))))
                            | F.Atom(SL.Eq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.IntVal i,SL.VarInt v2)))))
                            | F.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                            | F.Atom(SL.Eq(SL.VarUpdate(_,th,SL.IntT(SL.IntSub(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                let v1 = SL.V.set_param varr (SL.V.Local (SL.voc_to_var th)) in
                                if i = 1 then Arr.add_followed_by arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i = -1 then Arr.add_followed_by arr (SL.VarInt v2) (SL.VarInt v1)
                                else if i > 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i < 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                            | F.Atom(SL.Eq(SL.IntT(SL.VarInt v),SL.IntT(SL.IntVal 0)))
                            | F.Atom(SL.Eq(SL.IntT(SL.IntVal 0),SL.IntT(SL.VarInt v))) ->
                                Arr.set_minimum arr (SL.VarInt v)
                            | F.Atom(SL.Eq(SL.IntT i1,SL.IntT i2)) -> Arr.add_eq arr i1 i2
                            | F.Atom(SL.InEq(SL.IntT i1,SL.IntT i2)) -> Arr.add_ineq arr i1 i2
                            | F.NegAtom(SL.Less(i1,i2)) -> Arr.add_greatereq arr i1 i2
                            | F.NegAtom(SL.Greater(i1,i2)) -> Arr.add_lesseq arr i1 i2
                            | F.NegAtom(SL.LessEq(i1,i2)) -> Arr.add_greater arr i1 i2
                            | F.NegAtom(SL.GreaterEq(i1,i2)) -> Arr.add_less arr i1 i2
                            | F.NegAtom(SL.Eq(SL.IntT i1,SL.IntT i2)) -> Arr.add_ineq arr i1 i2
                            | F.NegAtom(SL.InEq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i))))
                            | F.NegAtom(SL.InEq(SL.IntT (SL.VarInt v1),SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2))))
                            | F.NegAtom(SL.InEq(SL.IntT (SL.IntAdd(SL.VarInt v2,SL.IntVal i)),SL.IntT (SL.VarInt v1)))
                            | F.NegAtom(SL.InEq(SL.IntT (SL.IntAdd(SL.IntVal i,SL.VarInt v2)),SL.IntT (SL.VarInt v1))) ->
                                if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                            | F.NegAtom(SL.InEq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i)))))
                            | F.NegAtom(SL.InEq(SL.IntT (SL.VarInt varr),SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2)))))
                            | F.NegAtom(SL.InEq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.VarInt v2,SL.IntVal i))),SL.IntT (SL.VarInt varr)))
                            | F.NegAtom(SL.InEq(SL.VarUpdate(_,th,SL.IntT(SL.IntAdd(SL.IntVal i,SL.VarInt v2))),SL.IntT (SL.VarInt varr))) ->
                                let v1 = SL.V.set_param varr (SL.V.Local (SL.voc_to_var th)) in
                                if i > 0 then Arr.add_greater arr (SL.VarInt v1) (SL.VarInt v2)
                                else if i < 0 then Arr.add_less arr (SL.VarInt v1) (SL.VarInt v2)
                                else Arr.add_eq arr (SL.VarInt v1) (SL.VarInt v2)
                            | F.NegAtom(SL.InEq(SL.IntT(SL.VarInt v),SL.IntT(SL.IntVal 0)))
                            | F.NegAtom(SL.InEq(SL.IntT(SL.IntVal 0),SL.IntT(SL.VarInt v))) ->
                                Arr.set_minimum arr (SL.VarInt v)
                            | F.NegAtom(SL.InEq(SL.IntT i1,SL.IntT i2)) -> Arr.add_eq arr i1 i2
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
                          verbl _LONG_INFO "**** TSL Solver: generated %i arrangements\n" (GenSet.size arrgs);
                          Some arrgs
                        end
                      end


let alpha_to_conjunctive_formula (alpha:SL.integer list list)
    : SL.conjunctive_formula =
  let rec cons_eq_class (is:SL.integer list) : SL.literal list =
    match is with
    | i1::i2::xs -> F.Atom(SL.Eq(SL.IntT i1, SL.IntT i2)) :: cons_eq_class (i2::xs)
    | _          -> []
  in
  let rec cons_ords (arr:SL.integer list list) : SL.literal list =
    match arr with
    | xs::ys::zs -> F.Atom(SL.Less(List.hd ys,
                              List.hd xs)) :: cons_ords (ys::zs)
    | _          -> []
  in
  let eqs = List.fold_left (fun ys eq_c ->
              (cons_eq_class eq_c) @ ys
            ) [] alpha in
  let ords = cons_ords alpha in
    (F.Conj (eqs @ ords))


let pumping (cf:SL.conjunctive_formula) : unit =
  match cf with
  | F.TrueConj  -> ()
  | F.FalseConj -> ()
  | F.Conj ls   -> begin
                      let no_arr_updates = ref true in
                      List.iter (fun l ->
                        match l with
                        (* A = B{l <- a} *)
                        | F.Atom(SL.Eq(_,SL.AddrArrayT(SL.AddrArrayUp(_,_,_))))
                        | F.Atom(SL.Eq(SL.AddrArrayT (SL.AddrArrayUp(_,_,_)),_))
                        | F.NegAtom(SL.InEq(_,SL.AddrArrayT(SL.AddrArrayUp(_,_,_))))
                        | F.NegAtom(SL.InEq(SL.AddrArrayT(SL.AddrArrayUp(_,_,_)),_)) ->
                            assert (!no_arr_updates); no_arr_updates := false
                        | _ -> ()
                      ) ls
                    end


let relevant_levels (cf:SL.conjunctive_formula) : SL.integer GenSet.t =
  let relevant_set = GenSet.empty() in
  match cf with
  | F.TrueConj  -> relevant_set
  | F.FalseConj -> relevant_set
  | F.Conj ls   -> begin
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
                      List.iter (fun l ->
                        match l with
                          (* reach(m,a,b,i,p) *)
                        | F.Atom (SL.Reach(_,_,_,i,_))
                        | F.NegAtom (SL.Reach(_,_,_,i,_)) -> GenSet.add relevant_set i
                          (* Remaining cases *)
                        | _ -> ()
                      ) ls;
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
    | F.TrueConj  -> F.TrueConj
    | F.FalseConj -> F.FalseConj
    | F.Conj ls   -> begin
                        F.Conj (List.fold_left (fun xs lit ->
                          let v_set = SL.varset_of_sort_from_literal lit SL.Int in
                          if SL.V.VarSet.for_all (fun v -> GenSet.mem relset (SL.VarInt v)) v_set then
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
    | F.TrueConj -> F.TrueConj
    | F.FalseConj -> F.FalseConj
    | F.Conj ls -> begin
                      let result =
                        F.Conj (List.map (fun lit ->
                          begin
                            match lit with
                            | F.Atom(SL.Skiplist(_,_,l,_,_,_))
                            | F.Atom(SL.Eq(_,SL.CellT(SL.MkCell(_,_,_,l))))
                            | F.Atom(SL.Eq(SL.CellT(SL.MkCell(_,_,_,l)),_))
                            | F.NegAtom(SL.InEq(_,SL.CellT(SL.MkCell(_,_,_,l))))
                            | F.NegAtom(SL.InEq(SL.CellT(SL.MkCell(_,_,_,l)),_)) ->
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
            | x::_ -> Some x in
    (eqclass,r)
  ) alpha


let dnf_sat (lines:int) (co:Smp.cutoff_strategy_t) (cf:SL.conjunctive_formula) : Sat.t =
  Log.print_ocaml "entering TSLSolver dnf_sat";
  Log.print "TSLSolver dnf_sat conjunctive formula" (SL.conjunctive_formula_to_str cf);
  let arrg_sat_table : (SL.integer list list, Sat.t) Hashtbl.t = Hashtbl.create 10 in

  let check_pa (cf:SL.conjunctive_formula) : Sat.t =
    match cf with
    | F.TrueConj  -> (verbl _LONG_INFO "**** check_pa: true\n"; Sat.Sat)
    | F.FalseConj -> (verbl _LONG_INFO "**** check_pa: false\n"; Sat.Unsat)
    | F.Conj _    -> (try_sat_with_presburger_arithmetic
                        (F.conjunctive_to_formula cf)) in


  let check_tslk (k:int)
                 (cf:SL.conjunctive_formula)
                 (alpha_r:SL.integer list list option) : Sat.t =
    match cf with
    | F.TrueConj -> Sat.Sat
    | F.FalseConj -> Sat.Unsat
    | F.Conj ls -> begin
                      let module TslkSol = (val TslkSolver.choose !solver_impl k
                                     : TslkSolver.S) in
                      TslkSol.compute_model (!comp_model);
                      let module Trans = TranslateTsl (TslkSol.TslkExp) in
                      let phi_tslk = Trans.to_tslk ls in
                      let res = TslkSol.check_sat lines co !use_quantifier phi_tslk in
                      DP.add_dp_calls this_call_tbl (DP.Tslk k) 1;
                      tslk_sort_map := TslkSol.get_sort_map ();
                      tslk_model := TslkSol.get_model ();
                      if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
                        if Sat.is_sat res then print_string "S" else print_string "X";
                      let _ = match alpha_r with
                              | None -> ()
                              | Some a -> Hashtbl.add arrg_sat_table a res in
                      res
                    end in


  (* Main verification function *)
  let check (pa:SL.conjunctive_formula)
            (panc:SL.conjunctive_formula)
            (nc:SL.conjunctive_formula)
            (alpha:SL.integer list list) : Sat.t =
    Log.print_ocaml "entering TSLSolver check";
    Log.print "PA formula" (SL.conjunctive_formula_to_str pa);
    Log.print "PANC formula" (SL.conjunctive_formula_to_str panc);
    Log.print "NC formula" (SL.conjunctive_formula_to_str nc);
    Log.print "Alpha arrangement" (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map SL.int_to_str xs)) ^ "]") alpha));

    Pervasives.flush (Pervasives.stdout);
    let alpha_phi = alpha_to_conjunctive_formula alpha in
    let pa_sat = check_pa (F.combine_conjunctive (F.combine_conjunctive pa panc) alpha_phi) in
    (* TODO: Some arrangements are invalid, as I am not considering literals of the
             form "l2 = l1 + 1" to enforce that l2 should be in the immediately consecutive
             equivalence class of l1
    assert pa_sat;
    *)
    if Sat.is_sat pa_sat then begin
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

      let alpha_r = List.rev (List.fold_left (fun xs (_,r) ->
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

      if not (SL.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) panc_r_level_vars) then begin
        print_endline ("PANC_R_LEVEL_VARS: " ^ (String.concat ";" (List.map SL.V.to_str (SL.V.VarSet.elements panc_r_level_vars))));
        print_endline ("ALPHA_RELEV: " ^ (GenSet.to_str SL.int_to_str alpha_relev));
        print_endline ("PANC_R: " ^ (SL.conjunctive_formula_to_str panc_r));
        print_endline ("ALPHA: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map SL.int_to_str xs)) ^ "]") alpha)));
        print_endline ("PA: " ^ (SL.conjunctive_formula_to_str pa));
        print_endline ("PANC: " ^ (SL.conjunctive_formula_to_str panc));
        print_endline ("NC: " ^ (SL.conjunctive_formula_to_str nc))
      end;

      assert (SL.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) panc_r_level_vars);
      if not (SL.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) nc_r_level_vars) then begin
        print_endline ("NC_R_LEVEL_VARS: " ^ (String.concat ";" (List.map SL.V.to_str (SL.V.VarSet.elements nc_r_level_vars))));
        print_endline ("ALPHA_RELEV: " ^ (GenSet.to_str SL.int_to_str alpha_relev));
        print_endline ("NC_R: " ^ (SL.conjunctive_formula_to_str nc_r));
        print_endline ("ALPHA: " ^ (String.concat ";" (List.map (fun xs -> "[" ^ (String.concat ";" (List.map SL.int_to_str xs)) ^ "]") alpha)));
        print_endline ("PA: " ^ (SL.conjunctive_formula_to_str pa));
        print_endline ("PANC: " ^ (SL.conjunctive_formula_to_str panc));
        print_endline ("NC: " ^ (SL.conjunctive_formula_to_str nc))
      end;
      assert (SL.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (SL.VarInt v)) nc_r_level_vars);

      (* Assertions only *)

      try
        let res = Hashtbl.find arrg_sat_table alpha_r in
        if (LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO)) then
          print_string (if Sat.is_sat res then "$" else "#");
        res
      with Not_found -> begin
        let alpha_r_formula = alpha_to_conjunctive_formula alpha_r in
        let final_formula = List.fold_left F.combine_conjunctive alpha_r_formula [panc_r;nc_r] in
        match final_formula with
        | F.TrueConj  -> (Hashtbl.add arrg_sat_table alpha_r Sat.Sat; Sat.Sat)
        | F.FalseConj -> (Hashtbl.add arrg_sat_table alpha_r Sat.Unsat; Sat.Unsat)
        | F.Conj _    -> check_tslk (List.length alpha_r) final_formula (Some alpha_r)
      end
    end else begin
      (* For this arrangement is UNSAT. Return UNSAT. *)
      if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
        print_string ".";
      Sat.Unsat
    end in


  (* Main body *)
  let (pa,panc,nc) = split_into_pa_nc cf in
  (* We clear the table of previously guessed arrangements *)
  Hashtbl.clear arr_table;
  (* Generate arrangements *)
  assert (Hashtbl.length arrg_sat_table = 0);
  let answer =
    (* If no interesting information in NC formula, then we just check PA and PANC *)
    if nc = F.TrueConj || nc = F.FalseConj then begin
      try_sat_with_presburger_arithmetic (F.conjunctive_to_formula
                                          (F.combine_conjunctive pa panc))
    end else begin
      let arrgs_opt = guess_arrangements (F.combine_conjunctive_list [pa; panc; nc]) in
      (* Verify if some arrangement makes the formula satisfiable *)
      match arrgs_opt with
      | None -> check_tslk 1 nc None
      | Some arrgs -> if GenSet.exists (fun alpha -> Sat.is_sat (check pa panc nc alpha)) arrgs then
                        Sat.Sat
                      else
                        Sat.Unsat
    end in
  answer


(*******************************************)
(*  MACHINERY FOR CHECKING SATISFIABILITY  *)
(*******************************************)



let check_sat_plus_info (lines : int)
           (co : Smp.cutoff_strategy_t)
           (use_q:bool)
           (phi : SL.formula) : (Sat.t * int * DP.call_tbl_t) =
    Log.print_ocaml "entering tslsolver check_sat";
    DP.clear_call_tbl this_call_tbl;
    use_quantifier := use_q;
    Log.print "TSL Solver formula to check satisfiability" (SL.formula_to_str phi);

    match phi with
    | F.Not(F.Implies(_,F.True)) -> (Sat.Unsat, 1, this_call_tbl)
    | F.Not (F.Implies(F.False, _)) -> (Sat.Unsat, 1, this_call_tbl)
    | F.Implies(F.False, _) -> (Sat.Sat, 1, this_call_tbl)
    | F.Implies(_, F.True) -> (Sat.Sat, 1, this_call_tbl)
    | _ -> let answer =
             try
                try_sat_with_presburger_arithmetic phi
             with _ -> begin
               (* STEP 1: Normalize the formula *)
               (* ERASE *)
               Log.print "TSL Solver formula" (SL.formula_to_str phi);
               let phi_norm = SL.normalize phi in
               (* ERASE *)
               Log.print "TSL Solver normalized formula" (SL.formula_to_str phi_norm);
               (* STEP 2: DNF of the normalized formula *)
               let phi_dnf = F.dnf phi_norm in
               (* If any of the conjunctions in DNF is SAT, then phi is sat *)
               if List.exists (fun psi -> Sat.is_sat (dnf_sat lines co psi)) phi_dnf then
                 Sat.Sat
               else
                 Sat.Unsat
            end in
            (answer, 1, this_call_tbl)


let check_sat (lines : int)
           (co : Smp.cutoff_strategy_t)
           (use_q:bool)
           (phi : SL.formula) : Sat.t =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = check_sat_plus_info lines co use_q phi in s


let check_valid_plus_info (prog_lines:int)
                          (co:Smp.cutoff_strategy_t)
                          (use_q:bool)
                          (phi:SL.formula) : (Valid.t * int * DP.call_tbl_t) =
  let (s,tsl_count,tslk_count) = check_sat_plus_info prog_lines co use_q
                                    (F.Not phi) in
  (Response.sat_to_valid s, tsl_count, tslk_count)


let check_valid (prog_lines:int)
                (co:Smp.cutoff_strategy_t)
                (use_q:bool)
                (phi:SL.formula) : Valid.t =
  Response.sat_to_valid (check_sat prog_lines co use_q (F.Not phi))


let compute_model (b:bool) : unit =
  comp_model := b
    (* Should I enable which solver? *)
    (* Solver.compute_model b *)
    (* Perhaps I should only set the flag and set activate the compute_model
       on the Solver when it is about to be called in check_sat *)


let model_to_str () : string =
  let model = !tslk_model in
  let sort_map = GM.sm_union !tslk_sort_map (GM.get_aux_sort_map model) in
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
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
