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

let _ = TllSol.compute_model (!comp_model)



(* The tables containing thread identifiers, locks and buckets variables
   representing arrays *)
let tidarr_tbl : (HM.tidarr, TLL.tid list) Hashtbl.t =
  Hashtbl.create 8

let lockarr_tbl : (HM.lockarr, TLL.tid list) Hashtbl.t =
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


let expand_array_to_var (v:HM.V.t)
                        (s:TLL.sort)
                        (n:int) : TLL.V.t =
  let id_str = HM.V.id v in
  let pr_str = if HM.V.is_primed v then "_prime" else "" in
  let th_str = match HM.V.parameter v with
               | HM.V.Shared -> ""
               | HM.V.Local t -> "_" ^ (HM.V.to_str t) in
  let p_str = match HM.V.scope v with
              | HM.V.GlobalScope -> ""
              | HM.V.Scope p -> p ^ "_" in
  let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
  let v_fresh = TLL.build_var new_id s false TLL.V.Shared TLL.V.GlobalScope ~fresh:true in
  verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
  v_fresh


let gen_tid_list (levels:int) (tt:HM.tidarr) : TLL.tid list =
  let xs = ref [] in
  for n = levels downto 0 do
    let v = match tt with
            | HM.VarTidArray v ->
                TLL.VarTh (expand_array_to_var v TLL.Tid n)
            | _ -> TLL.NoTid in
    xs := v::(!xs)
  done;
  verbl _LONG_INFO "**** TSL Solver, generated thread id list for %s: [%s]\n"
          (HM.tidarr_to_str tt)
          (String.concat ";" (List.map TLL.tid_to_str !xs));
  !xs


let get_tid_list (levels:int) (tt:HM.tidarr) : TLL.tid list =
  try
    Hashtbl.find tidarr_tbl tt
  with _ -> begin
    let tt' = gen_tid_list levels tt in
    Hashtbl.add tidarr_tbl tt tt'; tt'
  end


(***********************************)
(**                               **)
(**  Translation from THM to TLL  **)
(**                               **)
(***********************************)

let rec trans_literal (levels:int) (l:HM.literal) : TLL.formula =
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
        xs := (TLL.eq_tid (List.nth tt' i) (List.nth uu' i)) :: (!xs)
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
      F.Not (trans_literal levels (F.Atom(HM.Eq(HM.TidT t, HM.TidT (HM.TidArrRd (tt,i))))))









  | F.Atom a -> TllInterface.formula_to_tll_formula(
                  ThmInterface.formula_to_expr_formula (Formula.atom_to_formula a))
  | F.NegAtom a -> TllInterface.formula_to_tll_formula(
                     ThmInterface.formula_to_expr_formula (Formula.negatom_to_formula a))



let to_tll (levels:int) (thm_ls:HM.literal list) : TLL.formula =
  Log.print "ThmSolver. Formula to translate into TLL"
    (String.concat "\n" (List.map HM.literal_to_str thm_ls));
  Hashtbl.clear tidarr_tbl;
  let tll_ps = List.map (trans_literal levels) thm_ls in
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
                    let phi_tll = to_tll levels
                                    (List.map ThmInterface.literal_to_thm_literal ls) in
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
               let phi_norm = HM.normalize phi in
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
(*
  let model = !tll_model in
  let sort_map = GM.sm_union !tll_sort_map (GM.get_aux_sort_map model) in
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
*)

let print_model () : unit =
  TllSol.print_model()
(*
  if !comp_model && (not (GM.is_empty_model !tll_model)) then
    print_endline (model_to_str())
  else
    ()
*)


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
