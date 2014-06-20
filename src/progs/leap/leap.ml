open Printf
open Core

open LeapLib
open Global

module Expr = Expression
module Eparser = ExprParser
module Elexer = ExprLexer
module Gparser = IGraphParser
module Glexer = IGraphLexer
module Symtbl = ExprSymTable

(****************)
(* main         *)
(****************)
let _ =

  try
    LeapArgs.parse_args();
    Version.show();
    Log.set_logFile !LeapArgs.logFile;

    let ch = LeapArgs.open_input () in
    let sys, undefTids = Parser.parse ch (StmParser.system StmLexer.norm) in
    LeapArgs.close_input ();

    LeapArgs.vcgenFlag := (!LeapArgs.binvSys       ||
                           !LeapArgs.pinvSys       ||
                           !LeapArgs.pinvPlusSys   ||
                           !LeapArgs.spinvSys      ||
                           !LeapArgs.useGraph      ||
                           (!LeapArgs.pvdFile <> ""));
    if !LeapArgs.vcgenFlag && (!LeapArgs.invCandidate = "") && 
       (!LeapArgs.iGraphFile = "" && (!LeapArgs.pvdFile = "")) then begin
      Interface.Err.msg "VCGen requested without invariant candidate"
        "Generation of verification conditions requested by user, but \
         no invariant candidate has been provided through the -i \
         argument.";
      exit 0
    end;

    (* Check SMT and SAT solvers are installed if they will be used *)
    let _ = try
              let smts = if !LeapArgs.use_z3 || !LeapArgs.use_yices_plus_z3 then
                           [SMTExecute.Z3;SMTExecute.Yices]
                         else
                           [SMTExecute.Yices] in
              if !LeapArgs.use_sat then MinisatCheck.check_installed () else ();
              SMTExecute.check_installed smts
            with
              SMTExecute.SMT_Not_Found s ->
                begin
                  Interface.Err.msg "SMT Solver not found" $
                  sprintf "SMT solver %s is required but could not be found in the system." s;
                  exit 1
                end in


    (* We load the system in the formula parser, just in case *)
    Symtbl.load_system sys;

    (* Shows the parsed system *)
    if (!LeapArgs.showFlag = true) then Report.report_system sys;

    (* Show label information if required *)
    if (!LeapArgs.show_label_info) then
      Report.report_labels (System.get_labels sys);

    (* Configure options *)
    QueryManager.set_smt_usage (!LeapArgs.use_smt);
    let module LeapOpt = struct
                           let sys = sys
                           let focus = !LeapArgs.focusPC
                           let ignore = !LeapArgs.ignorePC
                           let abs = if !LeapArgs.count_abs then System.Counting
                                     else System.NoAbstraction
                           let hide_pres = not !LeapArgs.expand_pres
                           let output_file = !LeapArgs.outFile
                           let inv_folder = !LeapArgs.invFolder
                           let dp = !LeapArgs.dpType
                           let tSolver = if !LeapArgs.use_z3 || !LeapArgs.use_yices_plus_z3 then
                                           BackendSolvers.Z3.identifier
                                         else
                                           BackendSolvers.Yices.identifier
                           let pSolver = if !LeapArgs.use_sat then
                                           (Log.print_cfg "use sat";
                                           BackendSolvers.Minisat.identifier)
                                         else if !LeapArgs.use_yices_plus_z3 then
                                           BackendSolvers.Yices.identifier
                                         else
                                           tSolver
                           let use_smt = !LeapArgs.use_smt
                           let compute_model = !LeapArgs.show_models
                           let group_vars = !LeapArgs.group_vars
                           let forget_primed_mem = (not !LeapArgs.keep_primed_mem)
                           let default_cutoff = !LeapArgs.coType
                           let use_quantifiers = !LeapArgs.use_quantifiers
                           let output_vcs = !LeapArgs.output_vcs
                           let stop_on_invalid = !LeapArgs.stop_on_invalid
                         end in

    (* Instantiate the core *)
    let module LeapCore = Core.Make(LeapOpt) in
    let module LeapParamInv = ParamInv.Make(LeapCore) in

    (* Benchmark timer *)
    let timer = new LeapLib.timer in
    timer#start;


    if (!LeapArgs.vcgenFlag) then begin

      (* Invariant candidate *)
      if (!LeapArgs.invCandidate <> "") then begin
        let (invVars, tag, inv_decls) = Parser.open_and_parse
                                        !LeapArgs.invCandidate
                                        (Eparser.invariant Elexer.norm) in
        (* Construct the global invariant as the conjuntion of all formulas *)
        let inv = Formula.conj_list (List.map snd inv_decls) in

        (* Check whether undef tids are included in invVars *)
        let _ = System.undeftids_in_formula_decl undefTids invVars in
        (* Declare the tag of the global formula as the big conjunction *)
        let _ = LeapCore.decl_tag tag inv invVars in
        (* Declare the tag of each subformula in the parsed file *)
        let _ = List.iter (fun (tag, phi) -> LeapCore.decl_tag tag phi invVars) inv_decls in
        let _ = Report.report_inv_cand inv in
(*        let sys = System.add_global_vars sys invVars in *)

        (* Use B-INV *)
        if !LeapArgs.binvSys then begin
(*
          let conds = VCG.binv sys inv in
            printf "%s\n" $ String.concat "\n--------\n" (List.map (fst>>Expr.formula_to_str) conds)
*)
        end;

        (* Use P-INV *)
        if !LeapArgs.pinvSys then begin
(*
          if VCG.some_dp_enabled () then
            ignore $ VCG.check_with_pinv sys inv
          else
            print_endline (String.concat "\n--------\n" $
              List.map (fst>>Expr.formula_to_str)
                (VCG.pinv sys inv))
*)
        end;

        (* Use P-INV+ *)
        if !LeapArgs.pinvPlusSys then begin
(*
          if VCG.some_dp_enabled () then
            ignore $ VCG.check_with_pinv_plus sys inv
          else
            print_endline (String.concat "\n--------\n" $
              List.map (fst>>Expr.formula_to_str)
                (VCG.pinv_plus sys inv))
*)
        end;

        (* SP-INV *)
        if !LeapArgs.spinvSys then begin
(*
          let supInv_file_list = Str.split (Str.regexp ",") !LeapArgs.supInvariant in
          let supInv_list = List.map (fun file ->
                              Parser.open_and_parse file (Eparser.invariant Elexer.norm)
                            ) supInv_file_list in
          Report.report_sup_inv supInv_list;
          let sup_form_list = List.map (fun (_,tag,phi) ->
                                ignore(LeapCore.decl_tag tag phi); phi
                              ) supInv_list in
*)
          ()
(*
          if VCG.some_dp_enabled () then
            ignore $ VCG.check_with_spinv sys sup_form_list inv
          else
            print_endline (String.concat "\n--------\n" $
              List.map (fst>>Expr.formula_to_str)
                (VCG.spinv sys sup_form_list inv))
*)
        end;
        ()
        end




    end;


    (* Graph parsing *)
    if !LeapArgs.useGraph then begin
      (* We load the graph information *)
      let graph = Parser.open_and_parse !LeapArgs.iGraphFile (Gparser.graph Glexer.norm) in
      let graph_solution_list = LeapParamInv.solve_from_graph graph in
      (ignore graph_solution_list)
    end;

    (* PVD Parsings *)
    if !LeapArgs.pvdFile <> "" then begin
      let pvd = Parser.open_and_parse !LeapArgs.pvdFile (Eparser.pvd Elexer.norm) in
      let pvd_support = match !LeapArgs.pvdSupport with
                        | "" -> None
                        | file -> Some (Parser.open_and_parse file
                                    (Gparser.pvd_support Glexer.norm)) in
      let module PVDSolver = Diagrams.Make(LeapCore) in
(*      let module DSolver = Diagrams.Make(LeapCore) in *)
      print_endline "PVD";
      print_endline (PVD.to_str pvd);
      ignore (PVDSolver.solve_from_pvd pvd pvd_support)
    end;


    timer#stop;
    printf "Total Analysis time: %.3f\n" timer#elapsed_time


  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" 
          (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)


let _ = LeapDebug.flush()






(*
  try LeapArgs.parse_args ();
(*    LOG "DP selected: %s" (DP.to_str !LeapArgs.dpType) LEVEL DEBUG; *)
    if !LeapArgs.verbose then LeapVerbose.enable_verbose();
    let ch = LeapArgs.open_input () in
    let sys, undefTids = Parser.parse ch (StmParser.system StmLexer.norm) in
(*    let sys = System.set_threads tmp_sys !LeapArgs.num_threads in *)
    LeapArgs.close_input ();
    LeapArgs.vcgenFlag := 
      (!LeapArgs.binvSys || !LeapArgs.pinvSys || !LeapArgs.pinvPlusSys 
       || !LeapArgs.spinvSys || !LeapArgs.useGraph);
    if !LeapArgs.vcgenFlag && (!LeapArgs.invCandidate = "") 
       && (!LeapArgs.iGraphFile = "") then begin
      Interface.Err.msg "VCGen requested without invariant candidate"
        "Generation of verification conditions requested by user, but \
         no invariant candidate has been provided through the -i \
         argument.";
      exit 0
    end;

    (* We load the system in the formula parser, just in case *)
    Symtbl.load_system sys;

    (* Shows the parsed system *)
    if (!LeapArgs.showFlag = true) then Report.report_system sys;

    (* Show label information if required *)
    if (!LeapArgs.show_label_info) then
      Report.report_labels (System.get_labels sys);
    
    (* Create VCGen module *)
    let solver = if !LeapArgs.use_z3 || !LeapArgs.use_yices_plus_z3 then
                   BackendSolvers.Z3.identifier
                 else
                   BackendSolvers.Yices.identifier in
    let pSolver = if !LeapArgs.use_sat then
                    BackendSolvers.Minisat.identifier
                  else if !LeapArgs.use_yices_plus_z3 then
                    BackendSolvers.Yices.identifier
                  else
                    solver in
    (* We get tslk's parameter if passed as argument *)
    let k_param = DP.get_tslk_param !LeapArgs.dpType in


    (* Sets whether the usage of SMT-LIB translation is preferable *)
    Printf.printf "smt_use: %b\n" (!LeapArgs.use_smt);
    QueryManager.set_smt_usage (!LeapArgs.use_smt);

    let module Pos  = (val PosSolver.choose pSolver : PosSolver.S) in
    let module Tll  = (val TllSolver.choose solver : TllSolver.S) in
    let module Tslk = (val TslkSolver.choose solver k_param : TslkSolver.S) in
    let module Num  = (val NumSolver.choose solver : NumSolver.S) in

    (* Tell Num, TLL, TSLK and TSL modules whether to compute models or not *)
    Num.compute_model (!LeapArgs.show_models);
    Tll.compute_model (!LeapArgs.show_models);
    Tslk.compute_model (!LeapArgs.show_models);
    TslSolver.compute_model (!LeapArgs.show_models);

    (* Tell TLL and TSLK modules the parsed cutoff strategy options *)
    Tll.set_forget_primed_mem (not !LeapArgs.keep_primed_mem);
    Tll.set_group_vars (!LeapArgs.group_vars);
    Tslk.set_forget_primed_mem (not !LeapArgs.keep_primed_mem);
    Tslk.set_group_vars (!LeapArgs.group_vars);

    let module VCG = VCGen.Make(Pos)(Tll)(Tslk)(Num) in
    let focus_list = Expr.gen_focus_list (System.get_trans_num sys)
                       !LeapArgs.focusPC !LeapArgs.ignorePC in
    VCG.initialize ((System.get_trans_num sys) + 1) !LeapArgs.coType
      !LeapArgs.outFile focus_list (not !LeapArgs.expand_pres) !LeapArgs.count_abs;
    VCG.set_detFolder !LeapArgs.detailedOutFile;
    VCG.set_detProbName
      (Filename.chop_extension (Filename.basename !LeapArgs.input_file));

    let module VD = Diagrams.Make(VCG) in
    
    VCG.enable_dp (!LeapArgs.dpType);
    
    (* Benchmark timer *)
    let timer = new LeapLib.timer in
    timer#start;
    
    (* Information for FTS generation *)
    if (!LeapArgs.vcgenFlag) then begin

      (* Invariant candidate *)
      if (!LeapArgs.invCandidate <> "") then begin
        let invTimer = new LeapLib.timer in
        invTimer#start;
        let (invVars, tag, inv) = 
          Parser.open_and_parse !LeapArgs.invCandidate
            (Eparser.invariant Elexer.norm) in

        (* Check whether undef tids are included in invVars *)
        let _ = System.undeftids_in_formula_decl undefTids invVars in
        let _ = VCG.decl_tag tag inv in
        let _ = Report.report_inv_cand inv in
        let sys = System.add_global_vars sys invVars in
        if !LeapArgs.binvSys then begin
          let conds = 
            VCG.binv sys inv in
            printf "%s\n" $ String.concat "\n--------\n"
              (List.map (fst>>Expr.formula_to_str) conds)
        end;

        if !LeapArgs.pinvSys then begin
          if VCG.some_dp_enabled () then
            ignore $ VCG.check_with_pinv sys inv
          else
            print_endline (String.concat "\n--------\n" $
              List.map (fst>>Expr.formula_to_str)
                (VCG.pinv sys inv))
        end;

        if !LeapArgs.pinvPlusSys then begin
          if VCG.some_dp_enabled () then
            ignore $ VCG.check_with_pinv_plus sys inv
          else
            print_endline (String.concat "\n--------\n" $
              List.map (fst>>Expr.formula_to_str)
                (VCG.pinv_plus sys inv))
        end;
        
        if !LeapArgs.spinvSys then begin
          let supInv_file_list = 
            Str.split (Str.regexp ",") !LeapArgs.supInvariant in
          let supInv_list = List.map 
            (fun file -> Parser.open_and_parse file
              (Eparser.invariant Elexer.norm))
            supInv_file_list in
          Report.report_sup_inv supInv_list;
          let sup_form_list = List.map 
            (fun (_,tag,phi) -> ignore(VCG.decl_tag tag phi); phi)
            supInv_list in
          if VCG.some_dp_enabled () then
            ignore $ VCG.check_with_spinv sys sup_form_list inv
          else
            print_endline (String.concat "\n--------\n" $
              List.map (fst>>Expr.formula_to_str)
                (VCG.spinv sys sup_form_list inv))
        end;
        
        invTimer#stop;
        printf "Total Analysis time: %.3f\n" invTimer#elapsed_time;
      end;

    end;


    if (!LeapArgs.vdFile <> "" && !LeapArgs.pvdFile <> "") then begin
      Interface.Err.msg "VD and PVD provided" $
        sprintf "Both, a verification diagram in file:\n%s\n and a \
                 parametrized verification diagram in file:\n%s\n were \
                 provided. Only one of them can be analyzed at a time."
          !LeapArgs.vdFile !LeapArgs.pvdFile
    end;
    
    (* Graph parsing *)
    if !LeapArgs.useGraph then begin
      if !LeapArgs.invFolder == "" then begin
        Interface.Err.msg "Invariant folder not provided." "";
        raise(LeapArgs.No_inv_folder)
      end;
      if not (Sys.is_directory !LeapArgs.invFolder) then begin
        Interface.Err.msg "Not a valid invariant folder" $
          Printf.sprintf "%s is not a valid folder." !LeapArgs.invFolder;
        raise(LeapArgs.No_inv_folder)
      end;
      (* We load the graph information *)
      let graph = Parser.open_and_parse !LeapArgs.iGraphFile 
        (Gparser.graph Glexer.norm) in

      (* We load the invariant information *)
      let all_files = Array.fold_left 
        (fun xs f -> 
          (!LeapArgs.invFolder ^ "/" ^ f)::xs) [] 
          (Sys.readdir !LeapArgs.invFolder) in
      let inv_files = List.filter (LeapLib.match_last_n_chars 3 "inv") all_files in
      List.iter 
        (fun i -> 
          let (phiVars, tag, phi) = 
            Parser.open_and_parse i (Eparser.invariant Elexer.norm) in
          VCG.decl_tag tag phi) 
        inv_files;

      (* Check all used formulas are defined *)
      let graph_tags = IGraph.graph_tags graph in
      let undef_tags = 
        List.filter (fun t -> not (VCG.is_def_tag t)) graph_tags in
      if undef_tags <> [] then begin
        let undef_t = Tag.tag_id (List.hd undef_tags) in
        Interface.Err.msg "Undefined tag" $
          Printf.sprintf "Tag %s was used in the invariant graph \
            but it could not be read from the invariant folder." undef_t;
        raise(LeapArgs.Unknown_tag undef_t)
      end;
(*      ignore $ VCG.check_with_graph sys graph *)
        print_endline "FORMULAS GENERATED FROM GRAPH"
(*
        List.iter (fun phi -> print_endline (Expr.formula_to_str phi)) (Gen.gen_from_graph sys graph)
*)
    end;

(*
    if (!LeapArgs.vdFile <> "" || !LeapArgs.pvdFile <> "") then begin
      let (vd_phi_voc, phi_vars, vd_phi) = match !LeapArgs.vdFormula with
        | "" -> ([], System.empty_var_table (), Expr.True)
        | _  -> 
          let phi_vars, phi_tag, phi = 
            Parser.open_and_parse !LeapArgs.vdFormula 
              (Eparser.vd_formula Elexer.norm) in
          VCG.decl_tag phi_tag phi;
          (Expr.voc phi, phi_vars, phi)
      in

      System.undeftids_in_formula_decl undefTids phi_vars;
      let sys = System.add_global_vars sys phi_vars in
      
      if (!LeapArgs.vdFile <> "") then begin
        let vd = Parser.open_and_parse !LeapArgs.vdFile 
          (Eparser.diagram Elexer.norm) in
        let vc = VD.gen_vd_vc (not !LeapArgs.expand_pres) sys vd in
        printf "---------------- Verification Diagram ----------------\n\
                %s\n\
                ---------------- Verification Diagram ----------------\n"
          (Diagrams.PP.vd_to_str vd);
        printf "--------------- Verification Conditions --------------\n\
                %s\n\
                --------------- Verification Conditions --------------\n"
          (Diagrams.PP.vc_to_str vc);
      end;

      if (!LeapArgs.pvdFile <> "") then begin
        let parsed_pvd, remains = 
          Parser.open_and_parse !LeapArgs.pvdFile
            (Eparser.param_diagram Elexer.norm) in
        let pvd = VD.load_pvd_formula_param parsed_pvd remains vd_phi_voc in
        
        (* Notice that we have in vd_phi the formula to be passed to the
           model checker *)
        printf "---------------- Verification Diagram ----------------\n\
                %s\n\
                ---------------- Verification Diagram ----------------\n"
          (VD.pvd_to_str pvd);

        if VCG.some_dp_enabled () then
          ignore (VD.check_pvd sys pvd)
        else
          let vc = VD.gen_pvd_vc (not !LeapArgs.expand_pres) sys pvd in
          printf "------------ Verification Conditions ------------\n\
                  %s\n\
                  ------------ Verification Conditions ------------\n"
            (Diagrams.PP.vc_to_str vc);
      end
    end;
*)
    timer#stop;
    Log.close();
    printf "Total Analysis time: %.3f\n" timer#elapsed_time
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" 
          (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)
*)

let _ = LeapDebug.flush()

