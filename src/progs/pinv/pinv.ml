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
  try let _ = PinvArgs.parse_args () in
    let ch = PinvArgs.open_input () in
    let (sys,undefTids) = Parser.parse ch (Stmparser.system Stmlexer.norm) in
    let _ = PinvArgs.close_input () in

    if !PinvArgs.invCandidate = "" then begin
      Interface.Err.msg "VCGen requested without invariant candidate"
        "Generation of verification conditions requested by user, but \
         no invariant candidate has been provided through the -i \
         argument.";
      exit 0
    end;

    (* We load the system in the formula parser, just in case *)
    Symtbl.load_system sys;

    (* Shows the parsed system *)
    let _ = if (!PinvArgs.showFlag = true) then Report.report_system sys in

    (* Create VCGen module *)
    let solver = 
      if !PinvArgs.use_z3 then BackendSolvers.Z3.identifier 
      else BackendSolvers.Yices.identifier in
    let module Pos = (val PosSolver.choose solver : PosSolver.S) in
    let module Tll = (val TllSolver.choose solver : TllSolver.S) in
    let module Num = (val NumSolver.choose solver : NumSolver.S) in
    let module VCG = VCGen.Make(Pos)(Tll)(Num) in
    let focus_list = Expr.gen_focus_list (System.get_trans_num sys)
                       !PinvArgs.focusPC !PinvArgs.ignorePC in
    VCG.initialize ((Sys.get_trans_num sys) + 1) !PinvArgs.coType !PinvArgs.outFile 
      focus_list !PinvArgs.hide_pres !PinvArgs.count_abs;
    
    VCG.enable_dp (!PinvArgs.dpType);
    
    (* Benchmark timer *)
    let timer = new LeapLib.timer in
    timer#start;

    (* Information for FTS generation *)
    let invVars, tag, inv = Parser.open_and_parse !PinvArgs.invCandidate 
      (Eparser.invariant Elexer.norm) in

    (* Check whether undef tids are included in invVars *)
    System.undeftids_in_formula_decl undefTids invVars;
    VCG.decl_tag tag inv;
    Report.report_inv_cand inv;
    let sys = System.add_global_vars sys invVars in

    if !PinvArgs.pinvPlusSys then begin
      if VCG.some_dp_enabled () then
        ignore $ VCG.check_with_pinv_plus sys inv
      else begin
        print_endline (String.concat "\n--------\n" $
          List.map (fun (vc,_) -> Expr.formula_to_str vc)
            (VCG.pinv_plus sys inv))
      end
    end else if VCG.some_dp_enabled () then
      ignore $ VCG.check_with_pinv sys inv
    else begin
      print_endline (String.concat "\n--------\n" $
        List.map (fun (vc,_) -> Expr.formula_to_str vc)
          (VCG.pinv sys inv))
    end;

    timer#stop;
    printf "Total Analysis time: %.3f\n" timer#elapsed_time
  with
    | Global.ParserError msg -> Interface.Err.msg "pinv: Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "pinv: Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise e

let _ = LeapDebug.flush ()
