
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


open LeapVerbose

module GenSet   = LeapGenericSet
module GM       = GenericModel
module SL       = TSLExpression
module SLInterf = TSLInterface
module E        = Expression
module F        = Formula
module SolOpt   = SolverOptions

type alpha_pair_t = (SL.integer list * SL.integer option)


let solver_impl = ref ""

let use_quantifier = ref false


let choose (s:string) : unit =
  solver_impl := s


(* Should we compute a model in case of courter example? *)
let comp_model : bool ref = ref false

(* The structure where we store the options for cutoff *)
let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()


(* Intermediate model information between TSL solver interface and
   TSLK solver interface *)
let tslk_sort_map = ref (GM.new_sort_map())
let tslk_model = ref (GM.new_model())


let arr_table = Hashtbl.create 8
(* Table containing arrangement satisfiability *)
let alpha_sat_table : (SL.conjunctive_formula, Sat.t) Hashtbl.t = Hashtbl.create 8


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
      Hashtbl.create 8
    let tidarr_tbl : (SL.tidarr, SLK.tid list) Hashtbl.t =
      Hashtbl.create 8

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
                      SLK.OrderList(m',a1',SLK.Null));
                     SLK.eq_setelem es' (SLK.SetToElems(s',m'));
                     SLK.eq_set
                      (s')
                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in
                      (* Old implementation
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',SLK.Null,SLK.LevelVal 0)))] in
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0),
                                          SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in *)
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
                       (* Old implementation
                         (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                         (SLK.AddrToSet(m',a1',n'))) :: (!xs) *)
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',SLK.Null,SLK.LevelSucc n')))
                       (SLK.PathToSet(SLK.GetPathAt(m',a1',SLK.Null,n')))) :: (!xs)
                       (* Old implementation
                         (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelSucc n'), SLK.AddrToSet(m',a2',SLK.LevelSucc n')))
                         (SLK.Setdiff (SLK.AddrToSet(m',a1',n'), SLK.AddrToSet(m',a2',n')))) :: (!xs) *)
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
                      SLK.OrderList(m',a1',SLK.Null));
                     SLK.ineq_setelem es' (SLK.SetToElems(s',m'));
                     SLK.ineq_set
                      (s')
                      (SLK.AddrToSet(m',a1',SLK.LevelVal 0))] in
                      (* Old implementation
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',SLK.Null,SLK.LevelVal 0)))] in
                        (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelVal 0), SLK.AddrToSet(m',a2',SLK.LevelVal 0)))] in *)
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
                        (* Old implementation
                          (SLK.AddrToSet(m',a1',SLK.LevelSucc n'))
                          (SLK.AddrToSet(m',a1',n')))) :: (!xs) *)
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',SLK.Null,SLK.LevelSucc n')))
                        (SLK.PathToSet(SLK.GetPathAt(m',a1',SLK.Null,n'))))) :: (!xs)
                        (* Old implementation
                          (SLK.Setdiff (SLK.AddrToSet(m',a1',SLK.LevelSucc n'), SLK.AddrToSet(m',a2',SLK.LevelSucc n')))
                          (SLK.Setdiff (SLK.AddrToSet(m',a1',n'), SLK.AddrToSet(m',a2',n'))))) :: (!xs) *)
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
  NumSolver.try_sat (SLInterf.formula_to_expr_formula phi)



(***************************************************)
(**                                               **)
(**  Module instantiation for Arrangement Solver  **)
(**                                               **)
(***************************************************)

let check_tslk (opt:SolOpt.t)
               (k:int)
               (arrg_sat_table:(E.integer list list, Sat.t) Hashtbl.t)
               (cf:E.conjunctive_formula)
               (alpha_r:E.integer list list option) : Sat.t =
  match cf with
  | F.TrueConj -> Sat.Sat
  | F.FalseConj -> Sat.Unsat
  | F.Conj ls -> begin
                    let module TslkSol = (val TslkSolver.choose !solver_impl k
                                   : TslkSolver.S) in
                    TslkSol.compute_model (!comp_model);
                    let module Trans = TranslateTsl (TslkSol.TslkExp) in
                    let phi_tslk = Trans.to_tslk
                                    (List.map TSLInterface.literal_to_tsl_literal ls) in
                    let res = TslkSol.check_sat opt phi_tslk in
                    DP.add_dp_calls this_call_tbl (DP.Tslk k) 1;
                    tslk_sort_map := TslkSol.get_sort_map ();
                    tslk_model := TslkSol.get_model ();
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
    let check_sp_dp = check_tslk;
  end

module ArrSol = ArrangementSolver.Make(ArrangementSolverOpt)


let check_sat_plus_info (opt:SolOpt.t)
                        (phi : SL.formula) : (Sat.t * int * DP.call_tbl_t) =
    Log.print_ocaml "entering tslsolver check_sat";
    DP.clear_call_tbl this_call_tbl;
    use_quantifier := (SolOpt.use_quantifiers opt);
    Log.print "TSL Solver formula to check satisfiability" (SL.formula_to_str phi);

    match phi with
    | F.Not(F.Implies(_,F.True)) -> (Sat.Unsat, 1, this_call_tbl)
    | F.Not (F.Implies(F.False, _)) -> (Sat.Unsat, 1, this_call_tbl)
    | F.Implies(F.False, _) -> (Sat.Sat, 1, this_call_tbl)
    | F.Implies(_, F.True) -> (Sat.Sat, 1, this_call_tbl)
    | _ -> let answer =
             try
                ArrSol.try_sat_with_pa
                  (TSLInterface.formula_to_expr_formula phi)
             with _ -> begin
               (* STEP 1: Normalize the formula *)
               Log.print "TSL Solver formula" (SL.formula_to_str phi);
               let phi_norm = SL.normalize phi in
               Log.print "TSL Solver normalized formula" (SL.formula_to_str phi_norm);
               (* STEP 2: DNF of the normalized formula *)
               let phi_dnf = F.dnf phi_norm in
               (* If any of the conjunctions in DNF is SAT, then phi is sat *)
               if List.exists
                    (fun psi ->
                      Sat.is_sat (ArrSol.dnf_sat opt
                                   (TSLInterface.conj_formula_to_expr_conj_formula psi))
                    ) phi_dnf then
                 Sat.Sat
               else
                 Sat.Unsat
            end in
            (answer, 1, this_call_tbl)


let check_sat (opt:SolOpt.t) (phi : SL.formula) : Sat.t =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = check_sat_plus_info opt phi in s


let check_valid_plus_info (opt:SolOpt.t)
                          (phi:SL.formula) : (Valid.t * int * DP.call_tbl_t) =
  let (s,tsl_count,tslk_count) = check_sat_plus_info opt (F.Not phi) in
  (Response.sat_to_valid s, tsl_count, tslk_count)


let check_valid (opt:SolOpt.t) (phi:SL.formula) : Valid.t =
  Response.sat_to_valid (check_sat opt (F.Not phi))


let compute_model (b:bool) : unit =
  comp_model := b
    (* Should I enable which solver? *)
    (* Solver.compute_model b *)
    (* ALE: Perhaps I should only set the flag and set activate the compute_model
       on the Solver when it is about to be called in check_sat *)


let model_to_str () : string =
  let model = !tslk_model in
  let sort_map = GM.sm_union !tslk_sort_map (GM.get_aux_sort_map model) in
  let thid_str = GM.search_type_to_str model sort_map GM.tid_s in
  let int_str  = GM.search_type_to_str model sort_map GM.int_s in
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
    "\nIntegers:\n" ^ int_str ^
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
  if !comp_model && (not (GM.is_empty_model !tslk_model)) then
    print_endline (model_to_str())
  else
    ()


let get_sort_map () : GM.sort_map_t =
  !tslk_sort_map


let get_model () : GM.t =
  !tslk_model


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
