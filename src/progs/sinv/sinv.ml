open Printf

open LeapLib
open Global


module Expr    = Expression
module Sys     = System
module Eparser = Exprparser
module Elexer  = Exprlexer
module Symtbl  = Exprsymtable


(****************)
(* main         *)
(****************)

let _ =
  try let _ = SinvArgs.parse_args () in
    (* Benchmark timer *)
    let timer = new LeapLib.timer in
    timer#start;
    
    let ch = SinvArgs.open_input () in
    let (sys,undefTids) = Parser.parse ch (Stmparser.system Stmlexer.norm) in
    let _ = SinvArgs.close_input () in

    if !SinvArgs.invCandidate = "" then begin
      Interface.Err.msg "VCGen requested without invariant candidate"
        "Generation of verification conditions requested by user, but \
         no invariant candidate has been provided through the -i \
         argument.";
      exit 0
    end;

    (* We load the system in the formula parser, just in case *)
    let _ = Symtbl.load_system sys in

    (* Shows the parsed system *)
    let _ = if (!SinvArgs.showFlag = true) then Report.report_system sys in

    (* We get tslk's parameter if passed as argument *)
    let k_param = DP.get_tslk_param !SinvArgs.dpType in

    (* Create VCGen module *)
    let solver = 
      if !SinvArgs.use_z3 then BackendSolvers.Z3.identifier 
      else BackendSolvers.Yices.identifier in
    let module Pos  = (val PosSolver.choose  solver : PosSolver.S)  in
    let module Tll  = (val TllSolver.choose  solver : TllSolver.S)  in
    let module Tslk = (val TslkSolver.choose solver k_param : TslkSolver.S) in
    let module Num  = (val NumSolver.choose  solver : NumSolver.S)  in
    let module VCG  = VCGen.Make(Pos)(Tll)(Tslk)(Num) in
    VCG.initialize ((Sys.get_trans_num sys) + 1) !SinvArgs.coType
      !SinvArgs.outFile !SinvArgs.focusPC (not !SinvArgs.expand_pres)
      !SinvArgs.count_abs;
    
    VCG.enable_dp (!SinvArgs.dpType);

    (* Information for FTS generation *)
    let (invVars, tag, inv) = Parser.open_and_parse !SinvArgs.invCandidate
      (Eparser.invariant Elexer.norm) in

    (* Check whether undef tids are included in invVars *)
    System.undeftids_in_formula_decl undefTids invVars;
    VCG.decl_tag tag inv;
    Report.report_inv_cand inv;
    let sys = System.add_global_vars sys invVars in

    let supInv_file_list = Str.split (Str.regexp ",") !SinvArgs.supInvariant in
    let supInv_list = List.map 
      (fun file -> Parser.open_and_parse file (Eparser.invariant Elexer.norm)) 
      supInv_file_list in
    Report.report_sup_inv supInv_list;
    let sup_form_list = List.map 
      (fun (_,tag,phi) -> let _ = VCG.decl_tag tag phi in phi) 
      supInv_list in
    if VCG.some_dp_enabled () then
      ignore $ VCG.check_with_spinv sys sup_form_list inv
    else
      print_endline (String.concat "\n--------\n" $ List.map 
        (fst >> Expr.formula_to_str)
        (VCG.spinv sys sup_form_list inv));
    
    (* Timer *)
    timer#stop;
    printf "Total Analysis time: %.3f\n" timer#elapsed_time
    
  with
    | Global.ParserError msg -> 
        Interface.Err.msg "sinv: Parsing error" msg
    | Parsing.Parse_error -> 
        Interface.Err.msg "sinv: Parsing error" $
          sprintf "Unexpected symbol \"%s\" at line %i" 
          (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
