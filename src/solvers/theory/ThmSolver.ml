open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module HM       = ThmExpression
module F        = Formula

let solver_impl = ref ""

let use_quantifier = ref false

let choose (s:string) : unit =
  solver_impl := s

let comp_model : bool ref = ref false

let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()

let tll_sort_map = ref (GM.new_sort_map())
let tll_model = ref (GM.new_model())

let this_call_tbl : DP.call_tbl_t = DP.new_call_tbl()


let try_sat_with_presburger_arithmetic (phi:HM.formula) : Sat.t =
  DP.add_dp_calls this_call_tbl DP.Num 1;
  NumSolver.try_sat (ThmInterface.formula_to_expr_formula phi)


let check_sat_plus_info (lines : int)
                        (co : Smp.cutoff_strategy_t)
                        (use_q:bool)
                        (phi : HM.formula) : (Sat.t * int * DP.call_tbl_t) =
    Log.print_ocaml "entering tslsolver check_sat";
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
                try_sat_with_presburger_arithmetic phi
             with _ -> begin
               (* STEP 1: Normalize the formula *)
               (* ERASE *)
               Log.print "THM Solver formula" (HM.formula_to_str phi);
               let phi_norm = HM.normalize phi in
               (* ERASE *)
               Log.print "THM Solver normalized formula" (HM.formula_to_str phi_norm);
               Sat.Sat


(*
               (* STEP 1: Normalize the formula *)
               (* ERASE *)
               Log.print "THM Solver formula" (HM.formula_to_str phi);
               let phi_norm = HM.normalize phi in
               (* ERASE *)
               Log.print "THM Solver normalized formula" (HM.formula_to_str phi_norm);
               (* STEP 2: DNF of the normalized formula *)
               let phi_dnf = F.dnf phi_norm in
               (* If any of the conjunctions in DNF is SAT, then phi is sat *)
               if List.exists (fun psi -> Sat.is_sat (dnf_sat lines co psi)) phi_dnf then
                 Sat.Sat
               else
                 Sat.Unsat
                 *)
            end in
    (*
            (answer, 1, this_call_tbl)
*)
    (Sat.Sat, 1, DP.new_call_tbl())


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


let print_model () : unit =
  if !comp_model && (not (GM.is_empty_model !tll_model)) then
    print_endline (model_to_str())
  else
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
