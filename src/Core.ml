open LeapLib
open Printf


module E = Expression
module PE = PosExpression


type file_kind_t = Inv | Axiom


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



module GenOptions :
  sig

    val sys : System.t
    val focus : Expression.pc_t list
    val ignore : Expression.pc_t list
    val abs : System.abstraction
    val hide_pres : bool
    val output_file : string
    val inv_folder : string
    val axiom_file : string
    val axiom_folder : string
    val dp : DP.t
    val pSolver : string
    val tSolver : string
    val compute_model : bool
    val group_vars : bool
    val forget_primed_mem : bool
    val default_cutoff : Smp.cutoff_strategy_t
    val use_quantifiers : bool
    val output_vcs : bool
    val stop_on_invalid : bool

  end

  =

  struct

    let sys               = System.empty_system ()
    let focus             = []
    let ignore            = []
    let abs               = System.NoAbstraction
    let hide_pres         = true
    let output_file       = ""
    let inv_folder        = ""
    let axiom_file        = ""
    let axiom_folder      = ""
    let dp                = DP.NoDP
    let pSolver           = BackendSolvers.Yices.identifier
    let tSolver           = BackendSolvers.Z3.identifier
    let compute_model     = false
    let group_vars        = false
    let forget_primed_mem = true
    let default_cutoff    = Tactics.default_cutoff_algorithm
    let use_quantifiers   = false
    let output_vcs        = false
    let stop_on_invalid   = false

  end


module type S =
  sig

    exception No_invariant_folder
    exception No_axiom_folder

    val new_proof_info : Smp.cutoff_strategy_t option -> proof_info_t
    val new_proof_obligation : Tactics.vc_info ->
                               Expression.formula list ->
                               proof_info_t ->
                               proof_obligation_t
    val obligations : proof_obligation_t -> Expression.formula list

    val lines_to_consider : int list
    val requires_theta : bool

    val report_vcs : Tactics.vc_info list -> unit

    val decl_tag : file_kind_t -> Tag.f_tag option -> Expression.formula ->
                   System.var_table_t -> unit
    val is_def_tag : Tag.f_tag -> bool
    val read_tag : file_kind_t -> Tag.f_tag -> Expression.formula
    val read_tags_and_group_by_file : file_kind_t -> Tag.f_tag list -> Expression.formula list
    val read_tag_info : file_kind_t -> Tag.f_tag -> Tag.f_info

    val system : System.t

    val theta : Expression.ThreadSet.t -> (Expression.formula * Expression.ThreadSet.t)
    val rho : System.seq_or_conc_t ->
              Expression.ThreadSet.t ->
              int ->
              Expression.ThreadSet.elt ->
              Expression.formula list

    val solve_proof_obligations : proof_obligation_t list ->
                                  solved_proof_obligation_t list

  end

module Make (Opt:module type of GenOptions) : S =
  struct

    module Eparser = ExprParser
    module Elexer = ExprLexer

    exception No_invariant_folder
    exception No_axiom_folder


    (************************************************)
    (*             TAGGING INFORMATION              *)
    (************************************************)

    let tags : Tag.tag_table = Tag.tag_table_new ()
    let axiom_tags : Tag.tag_table = Tag.tag_table_new ()

    let axioms : Axioms.t ref = ref (Axioms.empty_axioms ())

    let choose_table (k:file_kind_t) : Tag.tag_table =
      match k with
      | Inv -> tags
      | Axiom -> axiom_tags

    let tags_num () : int = Tag.tag_table_size tags
    let axiom_num () : int = Tag.tag_table_size axiom_tags


    let decl_tag (k : file_kind_t)
                 (t : Tag.f_tag option)
                 (phi : E.formula)
                 (vTbl:System.var_table_t) : unit =
      let tbl = choose_table k in
      match t with
      | None -> ()
      | Some tag -> if Tag.tag_table_mem tbl tag
          then
            raise(Tag.Duplicated_tag(Tag.tag_id tag))
          else Tag.tag_table_add tbl tag phi (Tag.new_info vTbl)


    let read_tag (k : file_kind_t) (t : Tag.f_tag) : E.formula =
      let tbl = choose_table k in
      if Tag.tag_table_mem tbl t then
        Tag.tag_table_get_formula tbl t
      else
        raise(Tag.Undefined_tag(Tag.tag_id t))


    let read_tags_and_group_by_file (k : file_kind_t)
                                    (ts : Tag.f_tag list) : E.formula list =
      let supp_tbl : (string, E.formula list) Hashtbl.t = Hashtbl.create 5 in
      List.iter (fun tag ->
        let master_id = Tag.master_id tag in
        try
          Hashtbl.replace supp_tbl master_id ((read_tag k tag)::(Hashtbl.find supp_tbl master_id))
        with Not_found -> Hashtbl.add supp_tbl master_id [read_tag k tag]
      ) ts;
      Hashtbl.fold (fun _ phi_list xs ->
        (Formula.conj_list phi_list) :: xs
      ) supp_tbl []


    let read_tag_info (k : file_kind_t) (t : Tag.f_tag) : Tag.f_info =
      let tbl = choose_table k in
      if Tag.tag_table_mem tbl t then
        Tag.tag_table_get_info tbl t
      else
        raise(Tag.Undefined_tag(Tag.tag_id t))


(*    let rad_supp_tags (ts : Tag.f_tag list) : E.formula list = *)
      


    let is_def_tag (t:Tag.f_tag) : bool =
      Tag.tag_table_mem tags t


    let clear_tags () : unit =
      Tag.tag_table_clear tags


    let load_tags_from_folder (k:file_kind_t) (folder:string) : unit =
      let all_files = Array.fold_left (fun xs f ->
                        (folder ^ "/" ^ f)::xs
                      ) [] (Sys.readdir folder) in
      let suffix = match k with
                   | Inv -> "inv"
                   | Axiom -> "axm" in
      let files = List.filter (fun s -> Filename.check_suffix s suffix) all_files in
      let rule = match k with
                 | Inv -> Eparser.invariant
                 | Axiom -> Eparser.axiom in
      List.iter (fun i ->
        let (phiVars, tag, phi_decls) = Parser.open_and_parse i
                                          (rule Elexer.norm) in
        let phi = Formula.conj_list (List.map snd phi_decls) in
        List.iter (fun (subtag,subphi) -> decl_tag k subtag subphi phiVars) phi_decls;
        decl_tag k tag phi phiVars
      ) files


    (********************)
    (*   CONFIGURATION  *)
    (********************)

    let (requires_theta, lines_to_consider) =
            E.gen_focus_list (System.get_trans_num Opt.sys)
                             Opt.focus Opt.ignore

    let posSolver  : (module PosSolver.S) = PosSolver.choose Opt.pSolver

    let numSolver  : (module NumSolver.S) = NumSolver.choose Opt.pSolver

    let pairsSolver: (module PairsSolver.S) = PairsSolver.choose Opt.pSolver

    let tllSolver  : (module TllSolver.S) = TllSolver.choose Opt.tSolver

    let tslkSolver : (module TslkSolver.S) = TslkSolver.choose Opt.tSolver
                                              (DP.get_tslk_param Opt.dp)

    let calls_counter : DP.call_tbl_t = DP.new_call_tbl()


    let prog_type : Bridge.prog_type = match Opt.dp with
                                       | DP.Num   -> Bridge.Num
                                       | DP.Pairs -> Bridge.Num
                                       | _        -> Bridge.Heap

    let _ = Tactics.set_fixed_voc
              (List.fold_left (fun set v ->
                 E.ThreadSet.add (E.VarTh v) set
               ) E.ThreadSet.empty (System.get_vars_of_sort Opt.sys E.Tid))
(*
              (List.map (fun v -> E.VarTh v)
                (System.get_vars_of_sort Opt.sys E.Tid))
*)

(*
    let _ = Tactics.set_fixed_voc (List.map (fun v -> E.VarTh v)
                (System.get_vars_of_sort Opt.sys E.Tid))
*)


    (*****************************)
    (*    INITIALIZATION CODE    *)
    (*****************************)
    let _ =
      if Opt.inv_folder <> "" then begin
        if Sys.is_directory Opt.inv_folder then begin
          load_tags_from_folder Inv Opt.inv_folder
        end else begin
          Interface.Err.msg "Not a valid invariant folder" $
            sprintf "%s is not a valid folder." Opt.inv_folder;
            raise(No_invariant_folder)
        end
      end;
      if Opt.axiom_folder <> "" then begin
        if Sys.is_directory Opt.axiom_folder then begin
          load_tags_from_folder Axiom Opt.axiom_folder
        end else begin
          Interface.Err.msg "Not a valid axiom folder" $
            sprintf "%s is not a valid folder." Opt.axiom_folder;
            raise(No_axiom_folder)
        end
      end;
      if Opt.axiom_file <> "" then begin
        try
          axioms := Parser.open_and_parse Opt.axiom_file
                      (IGraphParser.axioms IGraphLexer.norm)
        with _ -> begin
                    Interface.Err.msg "Not a valid axiom file" $
                      sprintf "%s is not a valid file with axioms." Opt.axiom_file;
                    raise(No_axiom_folder)
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


    let obligations (po:proof_obligation_t) : E.formula list =
      po.obligations


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



    (*************)
    (*  REPORTS  *)
    (*************)

    let report_vcs (vcs:Tactics.vc_info list) : unit =
      if Opt.output_vcs then
        Tactics.vc_info_list_to_folder Opt.output_file vcs



    (*************************)
    (*  AUXILIARY FUNCTIONS  *)
    (*************************)

    let set_status (res:Valid.t) : Result.status_t =
      if Valid.is_valid res then Result.Valid Opt.dp else Result.Invalid

    
    let add_calls (n:int) : unit =
      DP.add_dp_calls calls_counter Opt.dp n


    let system : System.t =
      Opt.sys


    let theta (voc:E.ThreadSet.t) : (E.formula * E.ThreadSet.t) =
      let theta = System.gen_theta (System.SOpenArray (E.ThreadSet.elements voc)) Opt.sys Opt.abs in
      let voc = E.ThreadSet.union voc (E.voc theta) in
      let init_pos = if E.ThreadSet.is_empty voc then
                       [E.pc_form 1 E.V.Shared false]
                     else
                       E.V.VarSet.fold (fun v xs ->
                         E.pc_form 1 (E.V.Local v) false :: xs
                       ) (E.voc_to_vars voc) [] in
      (Formula.conj_list (theta::init_pos), voc)


  let rho (seq_or_conc:System.seq_or_conc_t)
          (voc:E.ThreadSet.t)
          (line:int)
          (th:E.ThreadSet.elt) : E.formula list =
    System.gen_rho Opt.sys (System.SOpenArray (E.ThreadSet.elements voc))
      seq_or_conc prog_type line Opt.abs Opt.hide_pres th


    (**********************)
    (*  SOLVER REASONING  *)
    (**********************)


    let decide_cutoff (cutoff:Smp.cutoff_strategy_t option) : Smp.cutoff_strategy_t =
      match cutoff with
      | None     -> Opt.default_cutoff
      | Some cut -> cut


    let new_proof_info (cutoff:Smp.cutoff_strategy_t option) : proof_info_t =
      {
        cutoff = decide_cutoff cutoff;
      }



    let solve_proof_obligations (to_analyze:proof_obligation_t list)
                                    : solved_proof_obligation_t list =
      let module Pos   = (val posSolver) in
      let module Num   = (val numSolver) in
      let module Pairs = (val pairsSolver) in
      let module Tll   = (val tllSolver) in
      let module Tslk  = (val tslkSolver) in

      Num.compute_model(Opt.compute_model);
      Pairs.compute_model(Opt.compute_model);
      Tll.compute_model(Opt.compute_model);
      Tslk.compute_model(Opt.compute_model);
      TslSolver.compute_model(Opt.compute_model);
      ThmSolver.compute_model(Opt.compute_model);
(*
      print_endline ("FORMULA TAGS: " ^ (string_of_int (Tag.tag_table_size tags)));
      print_endline ("AXIOM TAGS: " ^ (string_of_int (Tag.tag_table_size axiom_tags)));
*)

      let axiom_table = Axioms.new_axiom_table axiom_tags in

      print_endline "Analyzing VCs...";

      let case_timer = new LeapLib.timer in
      let phi_timer = new LeapLib.timer in
      (* Clear the internal data *)
      DP.clear_call_tbl calls_counter;
      (* Clear the internal data *)

      let prog_lines = (System.get_trans_num Opt.sys) in

      let vc_counter = ref 0 in
      let oblig_counter = ref 0 in

      let show_progress = not (LeapVerbose.is_verbose_enabled()) in
      Progress.init (List.length to_analyze);

      let result =
        List.map (fun case ->
          let orig_id = Tactics.get_original_vc_id case.vc in
          let cutoff = case.proof_info.cutoff in
          let this_calls_counter = DP.new_call_tbl() in
          if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
            Report.report_vc_header !vc_counter case.vc (List.length case.obligations);
          case_timer#start;
          let obligation_counter = ref 1 in
          let res_list =
            List.map (fun phi_obligation ->
              (* TODO: Choose the right to_plain function *)
              if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
                Report.report_obligation_header !obligation_counter phi_obligation;
              let fol_phi = phi_obligation in
              (* We apply axioms if possible *)
              let phi_tag = Tactics.get_vc_tag case.vc in
              let vc_line = Tactics.get_line_from_info case.vc in
              let ax_tags = Axioms.lookup !axioms phi_tag vc_line in

              (*let _ = print_endline (Axioms.axiom_table_to_str axiom_table) in*)

              (*print_endline ("FOL_PHI:\n" ^ (E.formula_to_str fol_phi));*)
              let (axiom_list,res_phi) =
                List.fold_left (fun (axs, psi) (ax_tag,ax_kind) ->
                  let (ax_psi, psi') = Axioms.apply axiom_table psi ax_tag ax_kind in
                  (ax_psi::axs, psi')
                ) ([], fol_phi) ax_tags in

              let axiom_phi = Formula.conj_list axiom_list in
              let fol_phi = match axiom_phi with
                            | Formula.True -> res_phi
                            | _ -> Formula.Implies (axiom_phi, res_phi) in
              (*print_endline ("FOL_PHI_WITH_AXIOMS:\n" ^ (E.formula_to_str fol_phi));*)

              (* Axiom application finishes *)
              phi_timer#start;
              let status =
                if Valid.is_valid (Pos.check_valid prog_lines
                      (fst (PE.keep_locations fol_phi))) then begin
                  DP.add_dp_calls this_calls_counter DP.Loc 1 ~vc_id:orig_id;
                  Result.Valid DP.Loc
                end else begin
                  let (validity, calls) =
                    match Opt.dp with
                    | DP.NoDP   ->
                        (Valid.Invalid, 0)
                    | DP.Loc    ->
                        (Valid.Invalid, 0)
                    | DP.Num    ->
                        let num_phi = NumInterface.formula_to_int_formula fol_phi in
                        let (res, calls) = Num.check_valid_with_lines_plus_info
                                            prog_lines num_phi in
                        if Valid.is_unknown res then begin
                          let z3NumSolver : (module NumSolver.S) =
                            NumSolver.choose BackendSolvers.Z3.identifier in
                          let module Z3Num = (val z3NumSolver) in
                            Z3Num.compute_model(Opt.compute_model);
                            Z3Num.check_valid_with_lines_plus_info prog_lines num_phi
                        end else
                          (res, calls)
                    | DP.Pairs  ->
                        let pairs_phi = PairsInterface.formula_to_pairs_formula fol_phi in
                        let (res, calls) = Pairs.check_valid_with_lines_plus_info
                                            prog_lines pairs_phi in
                        if Valid.is_unknown res then begin
                          let z3PairsSolver : (module PairsSolver.S) =
                            PairsSolver.choose BackendSolvers.Z3.identifier in
                          let module Z3Pairs = (val z3PairsSolver) in
                            Z3Pairs.compute_model(Opt.compute_model);
                            Z3Pairs.check_valid_with_lines_plus_info prog_lines pairs_phi
                        end else
                          (res, calls)
                    | DP.Tll    ->
                        let tll_phi = TllInterface.formula_to_tll_formula fol_phi in
                          Tll.check_valid_plus_info prog_lines cutoff
                             Opt.use_quantifiers tll_phi
                    | DP.Tsl    ->
                        let tsl_phi = TSLInterface.formula_to_tsl_formula fol_phi in
                        let (res,tsl_calls,tslk_calls) =
                           TslSolver.check_valid_plus_info prog_lines cutoff
                             Opt.use_quantifiers tsl_phi in
                        DP.combine_call_table tslk_calls this_calls_counter;
                        (res, tsl_calls)
                    | DP.Tslk k ->
                        (* Check that the "k" DP parameter is enough for all
                         * levels in the formula *)
                        if k < Tslk.TslkExp.k then
                          Interface.Err.msg "Decision procedure not powerful enough" $
                            sprintf "A formula in TSLK[%i] cannot be analyzed with a \
                                     TSLK[%i] decision procedure. Will proceed with \
                                     TSLK[%i]." Tslk.TslkExp.k k Tslk.TslkExp.k;
                        let module TSLKIntf = TSLKInterface.Make(Tslk.TslkExp) in
                                   let tslk_phi = TSLKIntf.formula_to_tslk_formula fol_phi in
                                     Tslk.check_valid_plus_info prog_lines cutoff
                                        Opt.use_quantifiers tslk_phi
                    | DP.Thm    ->
                        let thm_phi = ThmInterface.formula_to_thm_formula fol_phi in
                        let (res,thm_calls,tll_calls) =
                           ThmSolver.check_valid_plus_info prog_lines cutoff
                             Opt.use_quantifiers thm_phi in
                        DP.combine_call_table tll_calls this_calls_counter;
                        (res, thm_calls)
                  in
                  let _ = match Opt.dp with
                          | DP.NoDP   -> ()
                          | DP.Loc    -> ()
                          | DP.Num    -> Num.print_model()
                          | DP.Pairs  -> Pairs.print_model()
                          | DP.Tll    -> Tll.print_model()
                          | DP.Tsl    -> TslSolver.print_model()
                          | DP.Tslk _ -> Tslk.print_model()
                          | DP.Thm    -> ThmSolver.print_model() in
                  DP.add_dp_calls this_calls_counter Opt.dp calls ~vc_id:orig_id;
                  if Opt.stop_on_invalid && (not (Valid.is_valid validity)) then begin
                    print_endline "!!! Process stopped because an invalid VC was found !!!";
                    exit (-1)
                  end;
                  set_status validity
                 end in
              (* Analyze the formula *)
              phi_timer#stop;
              let time = phi_timer#elapsed_time in
              if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
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
          if show_progress then
            Progress.current (!vc_counter);
          if LeapVerbose.is_verbose_level_enabled(LeapVerbose._SHORT_INFO) then
            Report.report_vc_tail !vc_counter (List.map snd res_list) this_calls_counter;
          incr vc_counter;
          res
        ) to_analyze in
      Report.report_summary (!oblig_counter)
        (List.map (fun r -> r.result) result) calls_counter;
      result


  end
