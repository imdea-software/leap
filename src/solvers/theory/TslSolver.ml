
open TSLExpression
open LeapLib
open LeapVerbose

module Arr = Arrangements
module GenSet = LeapGenericSet
module GM = GenericModel
module TslExp = TSLExpression
module type TslkExp = TSLKExpression.S


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


let gen_fresh_int_var (vs:TslExp.VarSet.t) : TslExp.variable =
  let rec find (n:int) : TslExp.variable =
    let v_cand_id = "fresh_int_" ^ (string_of_int n) in
    let v_cand = TslExp.build_var v_cand_id TslExp.Int false None None in
      if TslExp.VarSet.mem v_cand vs then find (n+1) else v_cand
  in
    find 0


let sanitize (cf:TslExp.conjunctive_formula) : TslExp.conjunctive_formula =
  let find_candidates (ls:TslExp.literal list)
        : (TslExp.VarSet.t * TslExp.VarSet.t)  =
    List.fold_left (fun (cs,ss) l ->
      match l with
      | Atom(Eq(_,CellT(MkCell(_,AddrArrayUp(_,VarInt v1,_),TidArrayUp(_,VarInt v2,_),_)))) ->
          (TslExp.VarSet.add v1 (TslExp.VarSet.add v2 cs), ss)
      | Atom(Eq(_,AddrArrayT(AddrArrayUp(_,VarInt v,_))))
      | Atom(Eq(AddrArrayT(AddrArrayUp(_,VarInt v,_)),_))
      | Atom(Eq(_,TidArrayT(TidArrayUp(_,VarInt v,_))))
      | Atom(Eq(TidArrayT(TidArrayUp(_,VarInt v,_)),_))
      | Atom(Eq(_,CellT(MkCell(_,AddrArrayUp(_,VarInt v,_),_,_))))
      | Atom(Eq(_,CellT(MkCell(_,_,TidArrayUp(_,VarInt v,_),_)))) ->
        (TslExp.VarSet.add v cs, ss)
      | Atom(Eq(IntT(VarInt _), IntT(IntAdd (VarInt v, IntVal 1))))
      | Atom(Eq(IntT(IntAdd (VarInt v, IntVal 1)), IntT (VarInt _))) ->
        (cs, TslExp.VarSet.add v ss)
      | _ -> (cs, ss)
    ) (TslExp.VarSet.empty, TslExp.VarSet.empty) ls
  in
  let fresh_vargen = TslExp.new_fresh_gen_from_conjformula cf in
  match cf with
  | TslExp.FalseConj -> cf
  | TslExp.TrueConj  -> cf
  | TslExp.Conj ls   -> let (cs,ss) = find_candidates ls in
                        let needs_sanit = TslExp.VarSet.diff cs ss in
                        let ls' = TslExp.VarSet.fold (fun v xs ->
                                    let v_new = VarInt (TslExp.gen_fresh_var fresh_vargen TslExp.Int) in
                                    (Atom(Eq(IntT v_new, IntT(IntAdd(VarInt v, IntVal 1))))) :: ls
                                  ) needs_sanit ls
                        in
                          TslExp.Conj ls'


let guess_arrangements_by_brute_force (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula list =
  LOG "Entering guess_arrangements..." LEVEL TRACE;
  let rec cons_var_eq_class (vs:TslExp.variable list) : TslExp.literal list =
    match vs with
    | v1::v2::xs -> Atom(Eq(IntT (VarInt v1), IntT (VarInt v2))) :: cons_var_eq_class (v2::xs)
    | _          -> []
  in
  let rec cons_var_ords (arr:TslExp.variable list list) : TslExp.literal list =
    match arr with
    | xs::ys::zs -> Atom(Less(VarInt(List.hd xs),
                              VarInt(List.hd ys))) :: cons_var_ords (ys::zs)
    | _          -> []
  in
  match cf with
  | TslExp.FalseConj -> []
  | TslExp.TrueConj  -> []
  | TslExp.Conj ls   -> verb "**** TSL Solver. Computing level vars from: %s\n"
                              (TslExp.conjunctive_formula_to_str cf);
                        let level_vars = TslExp.varset_of_sort_from_conj cf TslExp.Int in
                        verb "**** TSL Solver. Extracted level vars: %s\n"
                              (String.concat ", " $
                                TslExp.VarSet.fold (fun v xs ->
                                  (TslExp.variable_to_str v) :: xs
                                ) level_vars []);
                        verb "**** TSL Solver. Computing partitions...\n";
                        let parts = Partition.gen_partitions
                                      (TslExp.VarSet.elements level_vars) [] in
                        verb "**** TSL Solver. Computing equalities...\n";
                        let eqs = List.fold_left (fun xs p ->
                                    (Partition.to_list p) :: xs
                                  ) [] parts in
                        verb "**** TSL Solver. Level vars: %i\n"
                              (TslExp.VarSet.cardinal level_vars);
                        verb "**** TSL Solver. Computing arrangements...\n";
                        let arrgs = List.fold_left (fun xs eq_c ->
                                      (LeapLib.comb eq_c (List.length eq_c)) @ xs
                                    ) [] eqs in
                        verb "**** TSL Solver. Computing level arrangements...\n";
                        let lv_arrs = List.fold_left (fun xs arr ->
                                        let eqs = List.fold_left (fun ys eq_c ->
                                                    (cons_var_eq_class eq_c) @ ys
                                                  ) [] arr in
                                        let ords = cons_var_ords arr
                                        in
                                          (TslExp.Conj (eqs @ ords)) :: xs
                                      ) [] arrgs
                        in
                          lv_arrs


let guess_arrangements (cf:TslExp.conjunctive_formula)
      : (TslExp.conjunctive_formula * int) list =
  let rec cons_eq_class (is:TslExp.integer list) : TslExp.literal list =
    match is with
    | i1::i2::xs -> Atom(Eq(IntT i1, IntT i2)) :: cons_eq_class (i2::xs)
    | _          -> []
  in
  let rec cons_ords (arr:TslExp.integer list list) : TslExp.literal list =
    match arr with
    | xs::ys::zs -> Atom(Less(List.hd ys,
                              List.hd xs)) :: cons_ords (ys::zs)
    | _          -> []
  in
  let arr = Arr.empty true in
    match cf with
    | TslExp.FalseConj -> []
    | TslExp.TrueConj  -> []
    | TslExp.Conj ls   -> begin
                            let level_vars = TslExp.varset_instances_of_sort_from_conj cf (TslExp.Int) in
                             verb "**** TSL Solver: variables for arrangement...\n{ %s }\n"
                                    (TslExp.VarSet.fold (fun v str ->
                                      str ^ TslExp.variable_to_str v ^ "; "
                                    ) level_vars "");
(*
                            let level_vars = TslExp.VarSet.fold (fun v s ->
                                               TslExp.VarSet.add (TslExp.unlocalize_variable v) s
                                             ) original_vars TslExp.VarSet.empty in
*)
                            TslExp.VarSet.iter (fun v -> Arr.add_elem arr (TslExp.VarInt v)) level_vars;
                            List.iter (fun l ->
                              match l with
                              | Atom(Less(i1,i2)) -> Arr.add_less arr i1 i2
                              | Atom(Greater(i1,i2)) -> Arr.add_greater arr i1 i2
                              | Atom(LessEq(i1,i2)) -> Arr.add_lesseq arr i1 i2
                              | Atom(GreaterEq(i1,i2)) -> Arr.add_greatereq arr i1 i2
                              | Atom(Eq(IntT (VarInt v1),IntT (IntAdd(VarInt v2,IntVal 1))))
                              | Atom(Eq(IntT (VarInt v1),IntT (IntAdd(IntVal 1,VarInt v2))))
                              | Atom(Eq(IntT (IntAdd(VarInt v2,IntVal 1)),IntT (VarInt v1)))
                              | Atom(Eq(IntT (IntAdd(IntVal 1,VarInt v2)),IntT (VarInt v1))) ->
                                  Arr.add_greater arr (VarInt v1) (VarInt v2)
                              | Atom(Eq(IntT(VarInt v),IntT(IntVal 0)))
                              | Atom(Eq(IntT(IntVal 0),IntT(VarInt v))) ->
                                  Arr.set_minimum arr (VarInt v)
                              | Atom(Eq(IntT i1,IntT i2)) -> Arr.add_eq arr i1 i2
                              | Atom(InEq(IntT i1,IntT i2)) -> Arr.add_ineq arr i1 i2
                              | NegAtom(Less(i1,i2)) -> Arr.add_greatereq arr i1 i2
                              | NegAtom(Greater(i1,i2)) -> Arr.add_lesseq arr i1 i2
                              | NegAtom(LessEq(i1,i2)) -> Arr.add_greater arr i1 i2
                              | NegAtom(GreaterEq(i1,i2)) -> Arr.add_less arr i1 i2
                              | NegAtom(Eq(IntT i1,IntT i2)) -> Arr.add_ineq arr i1 i2
                              | NegAtom(InEq(IntT (VarInt v1),IntT (IntAdd(VarInt v2,IntVal 1))))
                              | NegAtom(InEq(IntT (VarInt v1),IntT (IntAdd(IntVal 1,VarInt v2))))
                              | NegAtom(InEq(IntT (IntAdd(VarInt v2,IntVal 1)),IntT (VarInt v1)))
                              | NegAtom(InEq(IntT (IntAdd(IntVal 1,VarInt v2)),IntT (VarInt v1))) ->
                                  Arr.add_greater arr (VarInt v1) (VarInt v2)
                              | NegAtom(InEq(IntT(VarInt v),IntT(IntVal 0)))
                              | NegAtom(InEq(IntT(IntVal 0),IntT(VarInt v))) ->
                                  Arr.set_minimum arr (VarInt v)
                              | NegAtom(InEq(IntT i1,IntT i2)) -> Arr.add_eq arr i1 i2
                              | _ -> ()
                            ) ls;
                            verb "**** TSL Solver: known information for arrangments:\n%s\n"
                                  (Arr.to_str arr TslExp.int_to_str);
                            let arrgs = GenSet.fold (fun s_elem xs ->
(*
                                    print_endline ("KNOWN INFORMATION:\n" ^
                                          (Arr.to_str arr TslExp.int_to_str));
                                          print_endline "PROC ARRANGEMENT:";
                                          print_endline (String.concat ";"
                                            (List.map (fun es -> "[" ^
                                              (String.concat "," (List.map TslExp.int_to_str es)) ^ "]"
                                            ) s_elem));
*)
                                          let eqs = List.fold_left (fun ys eq_c ->
                                                      (cons_eq_class eq_c) @ ys
                                                    ) [] s_elem in
                                          let ords = cons_ords s_elem in
(*
                                          print_endline "GENERATED LITEREAL";
                                          print_endline (TslExp.conjunctive_formula_to_str (TslExp.Conj (eqs @ ords)));
*)
                                            (TslExp.Conj (eqs @ ords),List.length s_elem) :: xs
                                        ) (Arr.gen_arrs arr) [] in
                            verb "**** TSL Solver: generated %i arragements\n" (List.length arrgs);
                            arrgs
                          end


let split (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula * TslExp.conjunctive_formula =
  match cf with
  | TslExp.TrueConj  -> (TslExp.TrueConj,  TslExp.TrueConj)
  | TslExp.FalseConj -> (TslExp.FalseConj, TslExp.FalseConj)
  | TslExp.Conj cf   ->
      let (pa,nc) = List.fold_left (fun (pas,ncs) l ->
                      match l with
                        (* l = q *)
                      | Atom(Eq(IntT(VarInt _),IntT(IntVal _)))
                      | Atom(Eq(IntT(IntVal _),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(VarInt _),IntT(IntVal _)))
                      | NegAtom(InEq(IntT(IntVal _),IntT(VarInt _))) -> (l::pas,ncs)
                        (* l1 = l2 *)
                      | Atom(InEq(IntT(VarInt _),IntT(VarInt _)))
                      | NegAtom(Eq(IntT(VarInt _),IntT(VarInt _)))
                        (* l1 = l2 + 1*)
                      | Atom(Eq(IntT(VarInt _),IntT (IntAdd (VarInt _, IntVal 1))))
                      | Atom(Eq(IntT(VarInt _),IntT (IntAdd (IntVal 1, VarInt _))))
                      | Atom(Eq(IntT(IntAdd(VarInt _,IntVal 1)),IntT(VarInt _)))
                      | Atom(Eq(IntT(IntAdd(IntVal 1,VarInt _)),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(VarInt _),IntT (IntAdd (VarInt _, IntVal 1))))
                      | NegAtom(InEq(IntT(VarInt _),IntT (IntAdd (IntVal 1, VarInt _))))
                      | NegAtom(InEq(IntT(IntAdd(VarInt _,IntVal 1)),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(IntAdd(IntVal 1,VarInt _)),IntT(VarInt _)))
                        (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
                      | Atom(Less(VarInt _,VarInt _))
                      | Atom(Greater(VarInt _,VarInt _))
                      | NegAtom(LessEq(VarInt _,VarInt _))
                      | NegAtom(GreaterEq(VarInt _,VarInt _))
                        (* But l1 <= l2 literals appear, as well as they are not compared to constants *)
                      | Atom(LessEq(VarInt _,VarInt _))
                      | Atom(GreaterEq(VarInt _,VarInt _))
                      | NegAtom(Less(VarInt _,VarInt _))
                      | NegAtom(Greater(VarInt _,VarInt _)) -> (l::pas,l::ncs)
                        (* Cases that should not appear at this point after normalization *)
                      | Atom(Less(IntVal _,_))          | Atom(Less(_,IntVal _))
                      | Atom(Greater(IntVal _,_))       | Atom(Greater(_,IntVal _))
                      | NegAtom(LessEq(IntVal _,_))     | NegAtom(LessEq(_,IntVal _))
                      | NegAtom(GreaterEq(IntVal _,_))  | NegAtom(GreaterEq(_,IntVal _))
                      | Atom(LessEq(IntVal _,_))        | Atom(LessEq(_,IntVal _))
                      | Atom(GreaterEq(IntVal _,_))     | Atom(GreaterEq(_,IntVal _))
                      | NegAtom(Less(IntVal _,_))       | NegAtom(Less(_,IntVal _))
                      | NegAtom(Greater(IntVal _,_))    | NegAtom(Greater(_,IntVal _)) ->
                          assert false
                        (* Remaining cases *)
                      | _ -> (pas,l::ncs)
                    ) ([],[]) cf
      in
        (TslExp.Conj pa, TslExp.Conj nc)


module TranslateTsl (TslkExp : TSLKExpression.S) =
  struct

    module TslkInterf = TSLKInterface.Make(TslkExp)


    (* The tables containing addresses and thread identifiers variables
       representing arrays *)
    let addrarr_tbl : (TslExp.addrarr, TslkExp.addr list) Hashtbl.t =
      Hashtbl.create 10
    let tidarr_tbl : (TslExp.tidarr, TslkExp.tid list) Hashtbl.t =
      Hashtbl.create 10


    let tid_tsl_to_tslk (t:TslExp.tid) : TslkExp.tid =
      TslkInterf.tid_to_tslk_tid(TSLInterface.tid_to_expr_tid t)

    let term_tsl_to_term (t:TslExp.term) : TslkExp.term =
      TslkInterf.term_to_tslk_term(TSLInterface.term_to_expr_term t)

    let set_tsl_to_tslk (s:TslExp.set) : TslkExp.set =
      TslkInterf.set_to_tslk_set(TSLInterface.set_to_expr_set s)

    let elem_tsl_to_tslk (e:TslExp.elem) : TslkExp.elem =
      TslkInterf.elem_to_tslk_elem(TSLInterface.elem_to_expr_elem e)

    let addr_tsl_to_tslk (a:TslExp.addr) : TslkExp.addr =
      TslkInterf.addr_to_tslk_addr(TSLInterface.addr_to_expr_addr a)

    let cell_tsl_to_tslk (c:TslExp.cell) : TslkExp.cell =
      TslkInterf.cell_to_tslk_cell(TSLInterface.cell_to_expr_cell c)

    let setth_tsl_to_tslk (s:TslExp.setth) : TslkExp.setth =
      TslkInterf.setth_to_tslk_setth(TSLInterface.setth_to_expr_setth s)

    let setelem_tsl_to_tslk (s:TslExp.setelem) : TslkExp.setelem =
      TslkInterf.setelem_to_tslk_setelem(TSLInterface.setelem_to_expr_setelem s)

    let path_tsl_to_tslk (p:TslExp.path) : TslkExp.path =
      TslkInterf.path_to_tslk_path(TSLInterface.path_to_expr_path p)

    let mem_tsl_to_tslk (m:TslExp.mem) : TslkExp.mem =
      TslkInterf.mem_to_tslk_mem(TSLInterface.mem_to_expr_mem m)

    let int_tsl_to_tslk (i:TslExp.integer) : TslkExp.level =
      TslkInterf.int_to_tslk_level(TSLInterface.int_to_expr_int i)

    let literal_tsl_to_tslk (l:TslExp.literal) : TslkExp.literal =
      TslkInterf.literal_to_tslk_literal(TSLInterface.literal_to_expr_literal l)


    let expand_array_to_var (v:TslExp.variable)
                            (s:TslkExp.sort)
                            (n:int) : TslkExp.variable =
      let id_str = TslExp.var_id v in
      let pr_str = if TslExp.is_primed_var v then "_prime" else "" in
      let th_str = match TslExp.var_th v with
                   | None -> ""
                   | Some tid -> "_" ^ (TslExp.tid_to_str tid) in
      let p_str = match TslExp.var_owner v with
                  | None -> ""
                  | Some p -> p ^ "_" in
      let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
      let v_fresh = TslkExp.build_var new_id s false None None in
      Printf.printf "FRESH VAR: %s\n" new_id;
      TslkExp.variable_mark_fresh v_fresh true;
      v_fresh


    let gen_addr_list (aa:TslExp.addrarr) : TslkExp.addr list =
      let xs = ref [] in
      for n = (TslkExp.k - 1) downto 0 do
        let v = match aa with
                | TslExp.VarAddrArray v ->
                    TslkExp.VarAddr (expand_array_to_var v TslkExp.Addr n)
                | TslExp.CellArr c ->
                    let l = TslkExp.LevelVal n in
                    TslkExp.NextAt(cell_tsl_to_tslk c, l)
                | _ -> TslkExp.Null in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated address list for %s: [%s]\n"
              (TslExp.addrarr_to_str aa)
              (String.concat ";" (List.map TslkExp.addr_to_str !xs));
      !xs


    let gen_tid_list (tt:TslExp.tidarr) : TslkExp.tid list =
      let xs = ref [] in
      for n = (TslkExp.k - 1) downto 0 do
        let v = match tt with
                | TslExp.VarTidArray v ->
                    TslkExp.VarTh (expand_array_to_var v TslkExp.Thid n)
                | TslExp.CellTids c ->
                    let l = TslkExp.LevelVal n in
                    TslkExp.CellLockIdAt(cell_tsl_to_tslk c, l)
                | _ -> TslkExp.NoThid in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated thread id list for %s: [%s]\n"
              (TslExp.tidarr_to_str tt)
              (String.concat ";" (List.map TslkExp.tid_to_str !xs));
      !xs



    let get_addr_list (aa:TslExp.addrarr) : TslkExp.addr list =
      try
        Hashtbl.find addrarr_tbl aa
      with _ -> begin
        let aa' = gen_addr_list aa in
        Hashtbl.add addrarr_tbl aa aa'; aa'
      end


    let get_tid_list (tt:TslExp.tidarr) : TslkExp.tid list =
      try
        Hashtbl.find tidarr_tbl tt
      with _ -> begin
        let tt' = gen_tid_list tt in
        Hashtbl.add tidarr_tbl tt tt'; tt'
      end


    let rec trans_literal (l:TslExp.literal) : TslkExp.formula =
      verb "**** TSL Solver. Literal to be translated: %s\n"
            (TslExp.literal_to_str l);
      match l with
      (* c = mkcell(e,k,A,l) *)
      | Atom(Eq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | Atom(Eq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c)))
      | NegAtom(InEq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | NegAtom(InEq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c))) ->
          let c' = cell_tsl_to_tslk (VarCell c) in
          let e' = elem_tsl_to_tslk e in
          let aa' = get_addr_list aa in
          let tt' = get_tid_list tt in
            TslkExp.eq_cell (c') (TslkExp.MkCell(e',aa',tt'))
      (* c != mkcell(e,k,A,l) *)
      | NegAtom(Eq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | NegAtom(Eq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c)))
      | Atom(InEq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | Atom(InEq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c))) ->
          TslkExp.Not (trans_literal (Atom(Eq(CellT(VarCell c), CellT(MkCell(e,aa,tt,i))))))
      (* a = c.arr[l] *)
      | Atom(Eq(AddrT a, AddrT(AddrArrRd(CellArr c,l))))
      | Atom(Eq(AddrT(AddrArrRd(CellArr c,l)), AddrT a))
      | NegAtom(InEq(AddrT a, AddrT(AddrArrRd(CellArr c,l))))
      | NegAtom(InEq(AddrT(AddrArrRd(CellArr c,l)), AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          TslkExp.addr_mark_smp_interesting a' true;
          TslkExp.eq_addr a' (TslkExp.NextAt(c',l'))
      (* t = c.tids[l] *)
      | Atom(Eq(ThidT t, ThidT(ThidArrRd(CellTids c,l))))
      | Atom(Eq(ThidT(ThidArrRd(CellTids c,l)), ThidT t))
      | NegAtom(InEq(ThidT t, ThidT(ThidArrRd(CellTids c,l))))
      | NegAtom(InEq(ThidT(ThidArrRd(CellTids c,l)), ThidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let c' = cell_tsl_to_tslk c in
          let l' = int_tsl_to_tslk l in
          TslkExp.tid_mark_smp_interesting t' true;
          TslkExp.eq_tid t' (TslkExp.CellLockIdAt(c',l'))
      (* A != B (addresses) *)
      | NegAtom(Eq(AddrArrayT(VarAddrArray _ as aa),
                   AddrArrayT(VarAddrArray _ as bb)))
      | Atom(InEq(AddrArrayT(VarAddrArray _ as aa),
                  AddrArrayT(VarAddrArray _ as bb))) ->
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for i = 0 to (TslkExp.k - 1) do
            xs := (TslkExp.ineq_addr (List.nth aa' i) (List.nth bb' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          TslkExp.addr_mark_smp_interesting (List.hd aa') true;
          TslkExp.disj_list (!xs)
      (* A != B (thread identifiers) *)
      | NegAtom(Eq(TidArrayT(VarTidArray _ as tt),
                   TidArrayT(VarTidArray _ as uu)))
      | Atom(InEq(TidArrayT(VarTidArray _ as tt),
                  TidArrayT(VarTidArray _ as uu))) ->
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for i = 0 to (TslkExp.k - 1) do
            xs := (TslkExp.ineq_tid (List.nth tt' i) (List.nth uu' i)) :: (!xs)
          done;
          (* I need one witness for array difference *)
          TslkExp.tid_mark_smp_interesting (List.hd tt') true;
          TslkExp.disj_list (!xs)
      (* a = A[i] *)
      | Atom(Eq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | Atom(Eq(AddrT (AddrArrRd (aa,i)), AddrT a))
      | NegAtom(InEq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | NegAtom(InEq(AddrT (AddrArrRd (aa,i)), AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let aa' = get_addr_list aa in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          TslkExp.addr_mark_smp_interesting a' true;
          TslkExp.conj_list (!xs)
      (* a != A[i] *)
      | NegAtom(Eq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | NegAtom(Eq(AddrT (AddrArrRd (aa,i)), AddrT a))
      | Atom(InEq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | Atom(InEq(AddrT (AddrArrRd (aa,i)), AddrT a)) ->
          TslkExp.Not (trans_literal (Atom(Eq(AddrT a, AddrT (AddrArrRd (aa,i))))))
      (* t = A[i] *)
      | Atom(Eq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | Atom(Eq(ThidT (ThidArrRd (tt,i)), ThidT t))
      | NegAtom(InEq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | NegAtom(InEq(ThidT (ThidArrRd (tt,i)), ThidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let tt' = get_tid_list tt in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_tid t' (List.nth tt' n))) :: (!xs)
          done;
          TslkExp.tid_mark_smp_interesting t' true;
          TslkExp.conj_list (!xs)
      (* t != A[i] *)
      | NegAtom(Eq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | NegAtom(Eq(ThidT (ThidArrRd (tt,i)), ThidT t))
      | Atom(InEq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | Atom(InEq(ThidT (ThidArrRd (tt,i)), ThidT t)) ->
          TslkExp.Not (trans_literal (Atom(Eq(ThidT t, ThidT (ThidArrRd (tt,i))))))
      (* B = A {l <- a} *)
      | Atom(Eq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | Atom(Eq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb))
      | NegAtom(InEq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | NegAtom(InEq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb)) ->
          let a' = addr_tsl_to_tslk a in
          let i' = int_tsl_to_tslk i in
          let aa' = get_addr_list aa in
          let bb' = get_addr_list bb in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_addr a' (List.nth bb' n))) ::
                  (TslkExp.Implies
                    (TslkExp.ineq_level i' n',
                     TslkExp.eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                  (!xs)
          done;
          TslkExp.addr_mark_smp_interesting a' true;
          TslkExp.conj_list (!xs)
      (* B != A {l <- a} *)
      | NegAtom(Eq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | NegAtom(Eq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb))
      | Atom(InEq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | Atom(InEq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb)) ->
          TslkExp.Not (trans_literal (Atom(Eq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))))
      (* U = T {l <- t} *)
      | Atom(Eq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | Atom(Eq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu))
      | NegAtom(InEq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | NegAtom(InEq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu)) ->
          let t' = tid_tsl_to_tslk t in
          let i' = int_tsl_to_tslk i in
          let tt' = get_tid_list tt in
          let uu' = get_tid_list uu in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_tid t' (List.nth uu' n))) ::
                  (TslkExp.Implies
                    (TslkExp.ineq_level i' n',
                     TslkExp.eq_tid (List.nth tt' n) (List.nth uu' n))) ::
                  (!xs)
          done;
          TslkExp.tid_mark_smp_interesting t' true;
          TslkExp.conj_list (!xs)
      (* U != T {l <- t} *)
      | NegAtom(Eq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | NegAtom(Eq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu))
      | Atom(InEq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | Atom(InEq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu)) ->
          TslkExp.Not (trans_literal (Atom(Eq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))))
      (* Skiplist (m,s,l,s1,s2) *)
      | Atom(Skiplist(m,s,l,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in
          let xs = ref
                    [TslkExp.Literal(TslkExp.Atom(
                      TslkExp.OrderList(m',a1',a2')));
                     TslkExp.eq_set
                      (s')
                      (TslkExp.AddrToSet(m',a1',TslkExp.LevelVal 0))] in
(*                      (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelVal 0)))] in *)
(*
                        (TslkExp.Setdiff (TslkExp.AddrToSet(m',a1',TslkExp.LevelVal 0),
                                          TslkExp.AddrToSet(m',a2',TslkExp.LevelVal 0)))] in
*)
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := TslkExp.Implies
                    (TslkExp.lesseq_level n' l',
                     TslkExp.And (TslkExp.atomlit (TslkExp.In(a2',TslkExp.AddrToSet(m',a1',n'))),
                                  TslkExp.eq_addr (TslkExp.NextAt(TslkExp.CellAt(m',a2'),n'))
                                                   TslkExp.Null)) :: (!xs);
          done;
          for n = 0 to (TslkExp.k - 2) do
            let n' = TslkExp.LevelVal n in
            xs := TslkExp.Implies
                    (TslkExp.less_level n' l',
                     TslkExp.subseteq
                       (TslkExp.AddrToSet(m',a1',TslkExp.LevelSucc n'))
                       (TslkExp.AddrToSet(m',a1',n'))) :: (!xs)
(*
                       (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelSucc n')))
                       (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',n')))) :: (!xs)*)
(*
                       (TslkExp.Setdiff (TslkExp.AddrToSet(m',a1',TslkExp.LevelSucc n'), TslkExp.AddrToSet(m',a2',TslkExp.LevelSucc n')))
                       (TslkExp.Setdiff (TslkExp.AddrToSet(m',a1',n'), TslkExp.AddrToSet(m',a2',n')))) :: (!xs)
*)

          done;
          TslkExp.addr_mark_smp_interesting a1' true;
          TslkExp.addr_mark_smp_interesting a2' true;
          TslkExp.conj_list (!xs)
      (* ~ Skiplist(m,s,l,a1,a2) *)
      | NegAtom(Skiplist(m,s,l,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let l' = int_tsl_to_tslk l in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in


          let xs = ref
                    [TslkExp.Literal(TslkExp.NegAtom(
                      TslkExp.OrderList(m',a1',a2')));
                     TslkExp.ineq_set
                      (s')
                      (TslkExp.AddrToSet(m',a1',TslkExp.LevelVal 0))] in
(*                      (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelVal 0)))] in *)
(*                      (TslkExp.Setdiff (TslkExp.AddrToSet(m',a1',TslkExp.LevelVal 0), TslkExp.AddrToSet(m',a2',TslkExp.LevelVal 0)))] in *)
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := TslkExp.And
                    (TslkExp.lesseq_level n' l',
                     TslkExp.Or (TslkExp.Not (TslkExp.atomlit (TslkExp.In (a2', TslkExp.AddrToSet(m',a1',n')))),
                                 TslkExp.ineq_addr (TslkExp.NextAt(TslkExp.CellAt(m',a2'),n'))
                                                    TslkExp.Null)) :: (!xs)
          done;
          for n = 0 to (TslkExp.k - 2) do
            let n' = TslkExp.LevelVal n in
            xs := TslkExp.And
                    (TslkExp.less_level n' l',
                     TslkExp.Not
                      (TslkExp.subseteq
                        (TslkExp.AddrToSet(m',a1',TslkExp.LevelSucc n'))
                        (TslkExp.AddrToSet(m',a1',n')))) :: (!xs)

(*
                        (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelSucc n')))
                        (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',n'))))) :: (!xs)
*)
(*
                        (TslkExp.Setdiff (TslkExp.AddrToSet(m',a1',TslkExp.LevelSucc n'), TslkExp.AddrToSet(m',a2',TslkExp.LevelSucc n')))
                        (TslkExp.Setdiff (TslkExp.AddrToSet(m',a1',n'), TslkExp.AddrToSet(m',a2',n'))))) :: (!xs)
*)
          done;
          TslkExp.addr_mark_smp_interesting a1' true;
          TslkExp.addr_mark_smp_interesting a2' true;
          TslkExp.disj_list (!xs)
      | _ -> TslkExp.Literal (literal_tsl_to_tslk l)


    let to_tslk (tsl_ls:TslExp.literal list) : TslkExp.formula =
      verbstr (Interface.Msg.info "TSL CONJUNCTIVE FORMULA TO TRANSLATE"
        (String.concat "\n" (List.map TslExp.literal_to_str tsl_ls)));
      Hashtbl.clear addrarr_tbl;
      Hashtbl.clear tidarr_tbl;
(*
      GenSet.clear interesting_addrs;
      GenSet.clear interesting_tids;
*)
      let tslk_ps = List.map trans_literal tsl_ls in
      let tslk_phi = TslkExp.conj_list tslk_ps in
      verbstr (Interface.Msg.info "OBTAINED TSLK TRANSLATED FORMULA"
        (TslkExp.formula_to_str tslk_phi));
      tslk_phi
  end



let check_sat_by_cases (lines:int)
                       (stac:Tactics.solve_tactic_t option)
                       (co : Smp.cutoff_strategy_t)
                       (cases:(TslExp.conjunctive_formula *                   (* PA formula  *)
                               TslExp.conjunctive_formula *                   (* NC formula  *)
                               (TslExp.conjunctive_formula * int) list) list) (* Arrangements *)
      : (bool * int * int) =

  (* PA satisfiability check function *)
  let check_pa (cf:TslExp.conjunctive_formula) : bool =
    match cf with
    | TslExp.TrueConj  -> (verb "**** check_pa: true\n"; true)
    | TslExp.FalseConj -> (verb "**** check_pa: false\n"; false)
    | TslExp.Conj ls   ->
        let numSolv_id = BackendSolvers.Yices.identifier in
        let module NumSol = (val NumSolver.choose numSolv_id : NumSolver.S) in
        let phi_num = NumExpression.formula_to_int_formula
                        (TSLInterface.formula_to_expr_formula
                          (TslExp.from_conjformula_to_formula
                            cf))
        in
        verb "**** TSL Solver will check satisfiability for:\n%s\n"
                  (NumExpression.int_formula_to_string phi_num);
        NumSol.is_sat phi_num in


  (* NC satisfiability check function *)
  let check_nc (cf:TslExp.conjunctive_formula) (i:int) : bool =
    match cf with
    | TslExp.TrueConj  -> true
    | TslExp.FalseConj -> false
    | TslExp.Conj ls ->
        (* A more efficient way of computing the K is to count the number
           of equivalence classes in the guessed arrangement. Note that we
           have previously added as many level variables as we require.
           Then, if the arrangement contains an assertion of the form
           "l1 = l2" there is no need to add both variables when computing
           K, as they will remain to be equal when the SMT will try to
           compute the model. *)
        (*
           let l_vs = varset_of_sort_from_conj cf Int in
           let k = VarSet.cardinal l_vs in
         *)
        let k = if i = -1 then
                  VarSet.cardinal (varset_of_sort_from_conj cf Int)
                else
                  i in
(*
        let module TslkSol = (val TslkSolver.choose "Z3" k
*)
        let module TslkSol = (val TslkSolver.choose !solver_impl k
                                         : TslkSolver.S) in
        TslkSol.compute_model (!comp_model);
        let module Trans = TranslateTsl (TslkSol.TslkExp) in
        verb "**** TSL Solver, about to translate TSL to TSLK...\n";
        let phi_tslk = Trans.to_tslk ls in
        verb "**** TSL Solver, TSL to TSLK translation done...\n";
        let res = TslkSol.is_sat lines stac co phi_tslk in
        tslk_sort_map := TslkSol.get_sort_map ();
        tslk_model := TslkSol.get_model ();
        res in


  (* General satisfiability function *)
  let rec check (pa:TslExp.conjunctive_formula)
                (nc:TslExp.conjunctive_formula)
                ((alpha,i):(TslExp.conjunctive_formula * int)) =
    verb "**** TSL Solver. Check PA formula\n%s\nand NC formula\n%s\nwith arrangement\n%s\n"
          (TslExp.conjunctive_formula_to_str pa)
          (TslExp.conjunctive_formula_to_str nc)
          (TslExp.conjunctive_formula_to_str alpha);
    let pa_sat = check_pa (TslExp.combine_conj_formula pa alpha) in
    verb "**** TSL Solver, PA sat?: %b\n" pa_sat;
    if pa_sat then
      (* Check NC /\ alpha satisfiability *)
      let _ = verb "**** TSL Solver will combine candidate arrangement wit NC.\n" in
      check_nc (TslExp.combine_conj_formula nc alpha) i
    else
      false in

  (* Main call *)
  let tslk_calls = ref 0 in
  let rec check_aux cases =
    match cases with
    | [] -> (false, 1, !tslk_calls)
    | (pa,nc,arrgs)::xs -> begin
                             let arrgs_to_try = match arrgs with
                                                | [] -> [(TslExp.TrueConj, -1)]
                                                | _  -> arrgs in
                             if (List.exists (fun (alpha, i) -> check pa nc (alpha,i)) arrgs_to_try) then
                               (true, 1, !tslk_calls)
                             else
                               check_aux xs
                           end
  in
    check_aux cases


let rec combine_splits_arrgs (sp:(TslExp.conjunctive_formula * TslExp.conjunctive_formula) list)
                             (arrgs:(TslExp.conjunctive_formula * int ) list list) :
            (TslExp.conjunctive_formula *
             TslExp.conjunctive_formula *
             (TslExp.conjunctive_formula * int) list) list =
  match (sp,arrgs) with
  | ([],[])                -> []
  | ((pa,nc)::xs,arrg::ys) -> (pa,nc,arrg)::(combine_splits_arrgs xs ys)
  | _ -> assert false


let is_sat_plus_info (lines : int)
           (stac:Tactics.solve_tactic_t option)
           (co : Smp.cutoff_strategy_t)
           (phi : TslExp.formula) : (bool * int * int) =
  (* 0. Normalize the formula and rewrite it in DNF *)
  verb "**** Will normalize TSL formula...\n";
  let phi_norm = TslExp.normalize phi in
  verbstr (Interface.Msg.info "NORMALIZED FORMULA" (TslExp.formula_to_str phi_norm));
  verb "**** Will do DNF on TSL formula...\n";
  let phi_dnf = TslExp.dnf phi_norm in
  verbstr (Interface.Msg.info "DNF RESULT"
    (String.concat "\n" (List.map TslExp.conjunctive_formula_to_str phi_dnf)));
  (* 1. Sanitize the formula *)
  verb "**** Will sanitize TSL formula...\n";
  let phi_san = List.map sanitize phi_dnf in
  verbstr (Interface.Msg.info "SANITARIZED FORMULAS"
    (String.concat "\n" (List.map TslExp.conjunctive_formula_to_str phi_san)));
  (* 2. Guess arrangements *)
  let arrgs = List.map guess_arrangements phi_san in
  (* 3. Split each conjunction into PA y NC *)
  verb "**** Will split TSL formula in NC and PA...\n";
  let splits = List.map split phi_san in
  verbstr (Interface.Msg.info "SPLITED FORMULAS"
    (String.concat "\n" (List.map (fun (pa,nc) -> "PA:\n" ^ (TslExp.conjunctive_formula_to_str pa) ^
                                                  "NC:\n" ^ (TslExp.conjunctive_formula_to_str nc)) splits)));
  (* 4. Call the solver for each possible case *)
  verb "**** Will check TSL formula satisfiability...\n";
  let (sat,tsl_calls,tslk_calls) = check_sat_by_cases lines stac co
                                      (combine_splits_arrgs splits arrgs)
  in
    (sat, tsl_calls, tslk_calls)


let is_sat (lines : int)
           (stac:Tactics.solve_tactic_t option)
           (co : Smp.cutoff_strategy_t)
           (phi : TslExp.formula) : bool =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = is_sat_plus_info lines stac co phi in s


let is_valid_plus_info (prog_lines:int)
                       (stac:Tactics.solve_tactic_t option)
                       (co:Smp.cutoff_strategy_t)
                       (phi:TslExp.formula) : (bool * int * int) =
  let (s,tsl_count,tslk_count) = is_sat_plus_info prog_lines stac co
                                   (TslExp.Not phi) in
    (not s, tsl_count, tslk_count)


let is_valid (prog_lines:int)
             (stac:Tactics.solve_tactic_t option)
             (co:Smp.cutoff_strategy_t)
             (phi:TslExp.formula) : bool =
  not (is_sat prog_lines stac co phi)


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
