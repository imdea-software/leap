open LeapLib
open Printf


module E = Expression
module PE = PosExpression


module GenOptions :
  sig

    val sys : System.t
    val focus : Expression.pc_t list
    val ignore : Expression.pc_t list
    val abs : System.abstraction
    val hide_pres : bool
    val output_file : string
    val inv_folder : string
    val dp : DP.t
    val pSolver : string
    val tSolver : string
    val compute_model : bool
    val group_vars : bool
    val forget_primed_mem : bool
    val default_cutoff : Smp.cutoff_strategy_t

  end

  =

  struct

    let sys               = System.empty_system
    let focus             = []
    let ignore            = []
    let abs               = System.NoAbstraction
    let hide_pres         = true
    let output_file       = ""
    let inv_folder        = ""
    let dp                = DP.NoDP
    let pSolver           = BackendSolvers.Yices.identifier
    let tSolver           = BackendSolvers.Z3.identifier
    let compute_model     = false
    let group_vars        = false
    let forget_primed_mem = true
    let default_cutoff    = Tactics.default_cutoff_algorithm

  end



module type S =
  sig

    exception No_invariant_folder

    type proof_obligation_t

    type solved_proof_obligation_t

    val decl_tag : Tag.f_tag option -> Expression.formula -> unit

    val gen_from_graph : IGraph.t -> proof_obligation_t list

    val solve_from_graph : IGraph.t -> solved_proof_obligation_t list

  end

module Make (Opt:module type of GenOptions) : S =
  struct

    module Eparser = Exprparser
    module Elexer = Exprlexer

    exception No_invariant_folder


    type proof_info_t =
      {
        cutoff : Smp.cutoff_strategy_t;
      }


    type proof_obligation_t =
      {
        vc : Tactics.vc_info; (* Maybe it should contain less information in the future *)
        obligations : E.formula list;
        proof_info : proof_info_t;
      }


    type solved_proof_obligation_t =
      {
        vc_info : Tactics.vc_info;
        solved_obligations : (E.formula * Result.info_t) list;
        result : Result.info_t;
      }



    (************************************************)
    (*             TAGGING INFORMATION              *)
    (************************************************)

    let tags : Tag.tag_table = Tag.tag_table_new


    let tags_num () : int = Tag.tag_table_size tags


    let decl_tag (t : Tag.f_tag option) (phi : E.formula) : unit =
      match t with
      | None -> ()
      | Some tag -> if Tag.tag_table_mem tags tag
          then
            raise(Tag.Duplicated_tag(Tag.tag_id tag))
          else Tag.tag_table_add tags tag phi Tag.new_info


    let read_tag (t : Tag.f_tag) : E.formula =
      if Tag.tag_table_mem tags t then
        Tag.tag_table_get_formula tags t
      else
        raise(Tag.Undefined_tag(Tag.tag_id t))


    let is_def_tag (t:Tag.f_tag) : bool =
      Tag.tag_table_mem tags t


    let clear_tags () : unit =
      Tag.tag_table_clear tags


    let load_tags_from_folder (folder:string) : unit =
      let all_files = Array.fold_left (fun xs f ->
                        (folder ^ "/" ^ f)::xs
                      ) [] (Sys.readdir folder) in
      let inv_files = List.filter (fun s -> Filename.check_suffix s "inv") all_files in
      List.iter (fun i ->
        let (phiVars, tag, phi) = Parser.open_and_parse i
                                      (Eparser.invariant Elexer.norm) in
          decl_tag tag phi
      ) inv_files


    (********************)
    (*   CONFIGURATION  *)
    (********************)

    let (requires_theta, lines_to_consider) =
            E.gen_focus_list (System.get_trans_num Opt.sys)
                             Opt.focus Opt.ignore

    let posSolver  : (module PosSolver.S) = PosSolver.choose Opt.pSolver

    let numSolver  : (module NumSolver.S) = NumSolver.choose Opt.tSolver

    let tllSolver  : (module TllSolver.S) = TllSolver.choose Opt.tSolver

    let tslkSolver : (module TslkSolver.S) = TslkSolver.choose Opt.tSolver
                                              (DP.get_tslk_param Opt.dp)

    let calls_counter : DP.call_tbl_t = DP.new_call_tbl()


    let prog_type : Bridge.prog_type = match Opt.dp with
                                       | DP.Num -> Bridge.Num
                                       | _      -> Bridge.Heap


    (*****************************)
    (*    INITIALIZATION CODE    *)
    (*****************************)
    let _ =
      if Opt.inv_folder <> "" then begin
        if Sys.is_directory Opt.inv_folder then begin
          load_tags_from_folder Opt.inv_folder
        end else begin
          Interface.Err.msg "Not a valid invariant folder" $
            sprintf "%s is not a valid folder." Opt.inv_folder;
            raise(No_invariant_folder)
        end
      end


    (******************)
    (*  CONSTRUCTORS  *)
    (******************)

    let new_proof_obligation (vc:Tactics.vc_info)
                             (obligations:E.formula list)
                             (proof_info:proof_info_t) : proof_obligation_t =
      {
        vc = vc;
        obligations = obligations;
        proof_info = proof_info;
      }


    let new_solved_proof_obligation (vc_info:Tactics.vc_info)
                                    (solved_oblig:(E.formula * Result.info_t) list)
                                    (result:Result.info_t) : solved_proof_obligation_t =
      {
        vc_info = vc_info;
        solved_obligations = solved_oblig;
        result = result;
      }

    (*********************)
    (*  PRETTY PRINTERS  *)
    (*********************)

    let proof_obligation_to_str (po:proof_obligation_t) : string =
      Printf.sprintf
        ("==  Proof obligation  ===================================================\n\
          %s\n\
          --  Obligations  --------------------------------------------------------\n\
          %s\n\
          =========================================================================\n")
        (Tactics.vc_info_to_str po.vc)
        (String.concat "\n" (List.map E.formula_to_str po.obligations))


    (*************************)
    (*  AUXILIARY FUNCTIONS  *)
    (*************************)

    let set_status (res:bool) : Result.status_t =
      if res then Result.Valid Opt.dp else Result.Invalid

    
    let add_calls (n:int) : unit =
      DP.add_dp_calls calls_counter Opt.dp n


    (**********************)
    (*  CONCURRENT SPINV  *)
    (**********************)


    let gen_vcs (supp:E.formula list)
                (inv:E.formula)
                (line:int)
                (premise:Premise.t)
                (trans_tid:E.tid)
                  : Tactics.vc_info list =
      let voc = E.voc (E.conj_list (inv::supp)) in
      let rho = System.gen_rho Opt.sys (System.SOpenArray voc) prog_type line Opt.abs
                    Opt.hide_pres trans_tid in
      let tid_diff_conj = match premise with
                          | Premise.SelfConseq -> E.True
                          | Premise.OthersConseq ->
                              E.conj_list (List.map (E.ineq_tid trans_tid) voc) in
      List.fold_left (fun rs phi ->
        Log.print "Create with support" (String.concat "\n" (List.map E.formula_to_str supp));
        let new_vc = Tactics.create_vc_info supp tid_diff_conj
                        phi inv voc trans_tid line
        in
          new_vc :: rs
      ) [] rho


    (* General Initialization premise *)
    let premise_init (inv:E.formula) : Tactics.vc_info =

      (* Initial condition *)
      let theta = System.gen_theta (System.SOpenArray (E.voc inv)) Opt.sys Opt.abs in
      let voc = E.voc (E.conj_list [theta;inv])
      in
        Tactics.create_vc_info [] E.True theta inv voc E.NoTid 0


    let spinv_transitions (supp:E.formula list)
                          (inv:E.formula)
                          (cases:IGraph.case_tbl_t)
                                : Tactics.vc_info list =
      let load_support (line:E.pc_t) (prem:Premise.t) : E.formula list =
        match IGraph.lookup_case cases line prem with
        | None -> supp
        | Some (supp_tags,_) -> List.map read_tag supp_tags
      in
      List.fold_left (fun vcs line ->
        let self_conseq_supp  = load_support line Premise.SelfConseq in
        let other_conseq_supp = load_support line Premise.OthersConseq in
        let fresh_k = E.gen_fresh_tid (E.voc (E.conj_list (inv::supp@other_conseq_supp))) in
        let self_conseq_vcs = List.fold_left (fun vcs i ->
                                gen_vcs (inv::self_conseq_supp) inv line Premise.SelfConseq i
                              ) [] (E.voc inv) in
        let other_conseq_vcs = gen_vcs (inv::other_conseq_supp) inv line Premise.OthersConseq fresh_k
        in
          vcs @ self_conseq_vcs @ other_conseq_vcs
      ) [] lines_to_consider


    let spinv_with_cases (supp:E.formula list)
                         (inv:E.formula)
                         (cases:IGraph.case_tbl_t) : Tactics.vc_info list =
      let initiation = if requires_theta then
                         [premise_init inv]
                       else
                         [] in

      let transitions = spinv_transitions supp inv cases
      in
        initiation @ transitions


    let spinv (supp:E.formula list)
              (inv:E.formula) : Tactics.vc_info list =
      spinv_with_cases supp inv (IGraph.empty_case_tbl())


    (*
    let tag_spinv (supInv_list : Tag.f_tag list)
                  (inv : Tag.f_tag) : Tactics.vc_info list =
      let supInv_list_as_formula =
        List.map (Tag.tag_table_get_formula tags) supInv_list in
      let inv_as_formula = Tag.tag_table_get_formula tags inv in
      spinv supInv_list_as_formula inv_as_formula
    *)



    (**********************)
    (*  SEQUENTIAL SPINV  *)
    (**********************)

    let seq_gen_vcs (supp:E.formula list)
                    (inv:E.formula)
                    (line:int)
                    (premise:Premise.t)
                    (trans_tid:E.tid)
                      : Tactics.vc_info list =
      let voc = E.voc (E.conj_list (inv::supp)) in
      let rho = System.gen_rho Opt.sys (System.SOpenArray voc) prog_type line Opt.abs
                    Opt.hide_pres trans_tid in
      let supp = List.map (E.param (E.Local trans_tid)) supp in
      let inv = match E.voc inv with
                | [] -> E.param (E.Local trans_tid) inv
                | _  -> inv in
      List.fold_left (fun rs phi ->
        let new_vc = Tactics.create_vc_info supp E.True phi inv voc trans_tid line in
          new_vc :: rs
      ) [] rho



    let seq_spinv_transitions (supp:E.formula list)
                              (inv:E.formula)
                              (cases:IGraph.case_tbl_t)
                                : Tactics.vc_info list =
      let trans_tid = match E.voc inv with
                      | [] -> E.gen_fresh_tid []
                      | i::[] -> i
                      | i::_ -> assert false in (* More than one thread parametrizing the invariant *)
      List.fold_left (fun vcs line ->
        let specific_supp = match IGraph.lookup_case cases line Premise.SelfConseq with
                            | None -> supp
                            | Some (supp_tags, _) -> List.map read_tag supp_tags in
        vcs @ seq_gen_vcs (inv::specific_supp) inv line Premise.SelfConseq trans_tid
      ) [] lines_to_consider




    let seq_spinv_with_cases (supp:E.formula list)
                             (inv:E.formula)
                             (cases:IGraph.case_tbl_t) : Tactics.vc_info list =
      let supp = inv :: supp in
      let need_theta = List.mem 0 lines_to_consider in
      let initiation = if need_theta then
                         [premise_init inv]
                       else
                         [] in

      let transitions = seq_spinv_transitions supp inv cases
      in
        initiation @ transitions


    let seq_spinv (supp:E.formula list)
                  (inv:E.formula) : Tactics.vc_info list =
      seq_spinv_with_cases supp inv (IGraph.empty_case_tbl())


    (*
    let tag_seq_spinv (sys : System.t)
                      (supInv_list : Tag.f_tag list)
                      (inv : Tag.f_tag) : Tactics.vc_info list =
      let supInv_list_as_formula =
        List.map (Tag.tag_table_get_formula tags) supInv_list in
      let inv_as_formula = Tag.tag_table_get_formula tags inv in
      seq_spinv sys supInv_list_as_formula inv_as_formula
    *)




    (**********************)
    (*  SOLVER REASONING  *)
    (**********************)


    let decide_cutoff (cutoff:Smp.cutoff_strategy_t option) : Smp.cutoff_strategy_t =
      match cutoff with
      | None     -> Opt.default_cutoff
      | Some cut -> cut


    let solve_proof_obligations (to_analyze:proof_obligation_t list)
                                    : solved_proof_obligation_t list =
      let module Pos  = (val posSolver) in
      let module Num  = (val numSolver) in
      let module Tll  = (val tllSolver) in
      let module Tslk = (val tslkSolver) in

      Num.compute_model(Opt.compute_model);
      Tll.compute_model(Opt.compute_model);
      Tslk.compute_model(Opt.compute_model);
      TslSolver.compute_model(Opt.compute_model);

      let case_timer = new LeapLib.timer in
      let phi_timer = new LeapLib.timer in
      (* Clear the internal data *)
      DP.clear_call_tbl calls_counter;
      (* Clear the internal data *)

      let prog_lines = (System.get_trans_num Opt.sys) in

      let vc_counter = ref 1 in
      let oblig_counter = ref 0 in

      let result =
        List.map (fun case ->
          let cutoff = case.proof_info.cutoff in
          let this_calls_counter = DP.new_call_tbl() in
          Report.report_vc_header !vc_counter case.vc (List.length case.obligations);
          case_timer#start;
          let obligation_counter = ref 1 in
          let res_list =
                List.map (fun phi_obligation ->
                  (* TODO: Choose the right to_plain function *)
                  Report.report_obligation_header !obligation_counter phi_obligation;
                  let fol_phi = phi_obligation in
                  phi_timer#start;
                  let status =
                    if Pos.is_valid prog_lines (fst (PE.keep_locations fol_phi)) 
                      then
                      (DP.add_dp_calls this_calls_counter DP.Loc 1; Result.Valid DP.Loc)
                    else begin
                      let (valid, calls) =
                        match Opt.dp with
                        | DP.NoDP   -> (false, 0)
                        | DP.Loc    -> (false, 0)
                        | DP.Num    -> let num_phi = NumInterface.formula_to_int_formula fol_phi in
                                        Num.is_valid_with_lines_plus_info prog_lines num_phi
                        | DP.Tll    -> let tll_phi = TllInterface.formula_to_tll_formula fol_phi in
                                       Tll.is_valid_plus_info prog_lines cutoff tll_phi
                        | DP.Tsl    -> let tsl_phi = TSLInterface.formula_to_tsl_formula fol_phi in
                                       let (res,tsl_calls,tslk_calls) =
                                          TslSolver.is_valid_plus_info prog_lines cutoff tsl_phi in
                                       DP.combine_call_table tslk_calls this_calls_counter;
                                       (res, tsl_calls)
                        | DP.Tslk k -> let module TSLKIntf = TSLKInterface.Make(Tslk.TslkExp) in
                                       let tslk_phi = TSLKIntf.formula_to_tslk_formula fol_phi in
                                       Tslk.is_valid_plus_info prog_lines cutoff tslk_phi
                      in
                      let _ = match Opt.dp with
                              | DP.NoDP   -> ()
                              | DP.Loc    -> ()
                              | DP.Num    -> Num.print_model()
                              | DP.Tll    -> Tll.print_model()
                              | DP.Tsl    -> TslSolver.print_model()
                              | DP.Tslk _ -> Tslk.print_model() in
                      DP.add_dp_calls this_calls_counter Opt.dp calls;
                      if (not valid) then assert false;
                      set_status valid
                     end in
                  (* Analyze the formula *)
                  phi_timer#stop;
                  let time = phi_timer#elapsed_time in
                  Report.report_obligation_tail status time;
                  incr obligation_counter;
                  let phi_result = Result.new_info status time in
                  (phi_obligation, phi_result)
                ) case.obligations in

          case_timer#stop;
          oblig_counter := !oblig_counter + (List.length case.obligations);
          let forall_res f = List.for_all (fun (_,info) -> f info) res_list in
          let exist_res  f = List.exists  (fun (_,info) -> f info) res_list in
          let vc_validity = if forall_res Result.is_valid then
                              Result.Valid Opt.dp
                            else if exist_res Result.is_invalid then
                              Result.Invalid
                            else
                              Result.Unverified in
          let case_result = Result.new_info vc_validity (case_timer#elapsed_time) in
          let res = new_solved_proof_obligation case.vc res_list case_result in
          DP.combine_call_table this_calls_counter calls_counter;
          Report.report_vc_tail !vc_counter case_result (List.map snd res_list) this_calls_counter;
          incr vc_counter;
          res
        ) to_analyze in
      Report.report_summary (!oblig_counter) (List.map (fun r -> r.result) result) calls_counter;
      result




    (************************************************)
    (*              FORMULA ANALYSIS                *)
    (************************************************)


    let check_well_defined_graph (graph:IGraph.t) : unit =
      let graph_tags = IGraph.graph_tags graph in
      let undef_tags = List.filter (fun t -> not (is_def_tag t)) graph_tags in
      if undef_tags <> [] then begin
        let undef_t = Tag.tag_id (List.hd undef_tags) in
        Interface.Err.msg "Undefined tag" $
          Printf.sprintf "Tag %s was used in the invariant graph \
            but it could not be read from the invariant folder." undef_t;
        raise(Tag.Undefined_tag undef_t)
      end


    let generate_obligations (vcs:Tactics.vc_info list)
                             (gral_plan:Tactics.proof_plan)
                             (cases:IGraph.case_tbl_t) : proof_obligation_t list =
      List.fold_left (fun res vc ->
      (* FOR LISTS *)
(*        let vc = Tactics.to_plain_vc_info E.PCVars vc in*)
        let prem = match Tactics.get_tid_constraint_from_info vc with
                   | E.True -> Premise.SelfConseq
                   | _      -> Premise.OthersConseq in
        let line = Tactics.get_line_from_info vc in
        let (obligations,cutoff) =
          match IGraph.lookup_case cases line prem with
          | None       -> (Tactics.apply_tactics_from_proof_plan [vc] gral_plan,
                           Tactics.get_cutoff gral_plan)
          | Some (_,p) -> let joint_plan = if Tactics.is_empty_proof_plan p then
                                             gral_plan
                                           else
                                             p in
                          (Tactics.apply_tactics_from_proof_plan [vc] joint_plan,
                           Tactics.get_cutoff joint_plan) in

        let proof_info = {cutoff = decide_cutoff cutoff; } in
        let proof_obligation = new_proof_obligation vc obligations proof_info in
          proof_obligation :: res
      ) [] vcs


    let gen_from_graph (graph:IGraph.t) : proof_obligation_t list =
      check_well_defined_graph graph;

      (* Process the graph *)
      let graph_info = IGraph.graph_info graph in
      List.fold_left (fun os (mode, suppTags, invTag, cases, plan) ->
        let supp_ids = String.concat "," $ List.map Tag.tag_id suppTags in
        let inv_id = Tag.tag_id invTag in
        let supp = List.map read_tag suppTags in
        let inv = read_tag invTag in
        let vc_info_list = match mode with
                           | IGraph.Concurrent ->
                             print_endline ("Concurrent problem for invariant " ^inv_id^
                                            " using as support [" ^supp_ids^ "]" ^
                                            " with " ^string_of_int (IGraph.num_of_cases cases)^
                                            " special cases.");
                             spinv_with_cases supp inv cases
                           | IGraph.Sequential ->
                             print_endline ("Sequential problem for invariant " ^inv_id^
                                            " using as support [" ^supp_ids^ "]" ^
                                            " with " ^string_of_int (IGraph.num_of_cases cases)^
                                            " special cases.");
                             seq_spinv_with_cases supp inv cases in
        Tactics.vc_info_list_to_folder Opt.output_file vc_info_list;
        let new_obligations = generate_obligations vc_info_list plan cases in
        let obligations_num = List.fold_left (fun n po ->
                                n + (List.length po.obligations)
                              ) 0 new_obligations in
        Report.report_generated_vcs vc_info_list obligations_num;
          os @ new_obligations
      ) [] graph_info


    let solve_from_graph (graph:IGraph.t) : solved_proof_obligation_t list =
(*        gen_from_graph graph; [] *)
      solve_proof_obligations (List.rev (gen_from_graph graph))
      

  end
