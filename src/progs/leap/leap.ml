open Printf

open LeapLib

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

    if not !Version._enable_ then begin
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
      printf "Total Analysis time: %.3f\n" timer#elapsed_time;
      printf "Heap usage: %s\n" (LeapLib.report_heap());
      printf "Memory consumption Ale: %s\n" (LeapLib.report_mem());
      printf "Memory consumption Juli: %s\n" (LeapLib.human_readable_byte_count());
      LeapDebug.flush()
    end

  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) 
          (Global.get_linenum())
    | e -> raise(e)
