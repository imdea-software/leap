open LeapVerbose

module Arr      = Arrangements
module GenSet   = LeapGenericSet
module GM       = GenericModel
module HM       = ThmExpression
module TLL      = TllExpression
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


let try_sat_with_pa (phi:HM.formula) : Sat.t =
  DP.add_dp_calls this_call_tbl DP.Num 1;
  NumSolver.try_sat (ThmInterface.formula_to_expr_formula phi)




(***********************************)
(**                               **)
(**  Translation from THM to TLL  **)
(**                               **)
(***********************************)

let to_tll (thm_ls:HM.literal list) : TLL.formula =
  F.True






(****************************)
(**                        **)
(**  Satisfiability check  **)
(**                        **)
(****************************)

let dnf_sat (lines:int) (co:Smp.cutoff_strategy_t) (cf:HM.conjunctive_formula) : Sat.t =
  Sat.Sat

  (*
let alpha_to_conjunctive_formula (alpha:HM.integer list list) :
    HM.conjunctive_formula =
      ArrangementSolver.alpha_to_conj_formula alpha
        (fun i1 i2 -> F.Atom(HM.Eq(HM.IntT i1, HM.IntT i2)))
        (fun i1 i2 -> F.Atom(HM.Less(i1, i2)))


let dnf_sat (lines:int) (co:Smp.cutoff_strategy_t) (cf:HM.conjunctive_formula) : Sat.t =
  Log.print_ocaml "entering THMSolver dnf_sat";
  Log.print "THMSolver dnf_sat conjunctive formula" (HM.conjunctive_formula_to_str cf);
  let arrg_sat_table : (HM.integer list list, Sat.t) Hashtbl.t = Hashtbl.create 8 in

  let check_pa (cf:SL.conjunctive_formula) : Sat.t =
    ArrangementSolver.check_pa cf alpha_sat_table try_sat_with_pa in


  let check_tll (cf:HM.conjunctive_formula)
                (alpha_r:HM.integer list list option) : Sat.t =
    match cf with
    | F.TrueConj -> Sat.Sat
    | F.FalseConj -> Sat.Unsat
    | F.Conj ls -> begin
                      let module TllSol = (val TllSolver.choose !solver_impl
                                     : TllSolver.S) in
                      TllSol.compute_model (!comp_model);
                      let phi_tll = to_tll ls in
                      let res = TllSol.check_sat lines co !use_quantifier phi_tll in
                      DP.add_dp_calls this_call_tbl DP.Tll 1;
                      tll_sort_map := TllSol.get_sort_map ();
                      tll_model := TllSol.get_model ();
                      if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
                        if Sat.is_sat res then print_string "S" else print_string "X";
                      let _ = match alpha_r with
                              | None -> ()
                              | Some a -> Hashtbl.add arrg_sat_table a res in
                      res
                    end in


  (* Main verification function *)
  let check (pa:HM.conjunctive_formula)
            (panc:HM.conjunctive_formula)
            (nc:HM.conjunctive_formula)
            (alpha:HM.integer list list) : Sat.t =
    Pervasives.flush (Pervasives.stdout);
    let alpha_phi = alpha_to_conjunctive_formula alpha in
    let pa_sat = check_pa (F.combine_conjunctive (F.combine_conjunctive pa panc) alpha_phi) in
    if Sat.is_sat pa_sat then begin
      (* We have an arrangement candidate *)
      pumping nc;
      let rel_set = relevant_levels nc in
      
      let alpha_pairs = update_arrangement alpha rel_set in
      let (panc_r, nc_r, alpha_pairs_r) = propagate_levels alpha_pairs panc nc in


      let alpha_pairs_str =
        String.concat ";" (List.map (fun (xs,mi) ->
          (String.concat "," (List.map HM.int_to_str xs)) ^":"^ (match mi with
                                                                 | Some i -> HM.int_to_str i
                                                                 | None -> "None")
        ) alpha_pairs_r) in
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

      let panc_r_level_vars = HM.varset_of_sort_from_conj panc_r HM.Int in
      let nc_r_level_vars = HM.varset_of_sort_from_conj nc_r HM.Int in

      assert (HM.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (HM.VarInt v)) panc_r_level_vars);
      assert (HM.V.VarSet.for_all (fun v -> GenSet.mem alpha_relev (HM.VarInt v)) nc_r_level_vars);







      (* Assertions only *)

      try
        let res = Hashtbl.find arrg_sat_table alpha_r in
(*        print_endline ("RA: " ^ (HM.conjunctive_formula_to_str (alpha_to_conjunctive_formula alpha_r))); *)
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
      try_sat_with_presburger_arithmetic
        (F.conjunctive_to_formula
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
*)














let check_sat_plus_info (lines : int)
                        (co : Smp.cutoff_strategy_t)
                        (use_q:bool)
                        (phi : HM.formula) : (Sat.t * int * DP.call_tbl_t) =
    (Sat.Sat, 1, this_call_tbl)

    (*


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
            end in
            (answer, 1, this_call_tbl)
*)

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
