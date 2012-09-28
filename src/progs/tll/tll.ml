open Printf
open LeapLib


module Eparser = Exprparser
module Elexer  = Exprlexer
module Expr    = Expression
module Symtbl  = Exprsymtable

(****************)
(* main         *)
(****************)

let _ =
  try
    TllArgs.parse_args ();
    let ch = TllArgs.open_input () in
    let (tmp_sys,undefTids) = Parser.parse ch (Stmparser.system Stmlexer.norm) in

    let sys = System.set_threads tmp_sys 1 in
    TllArgs.close_input ();

    (* We load the system in the formula parser, just in case *)
    Symtbl.load_system sys;

    let phiVars, phi = Parser.open_and_parse !TllArgs.phiFile 
      (Eparser.single_formula Elexer.norm) in
      
    (* Check whether undef tids are included in invVars *)
    System.undeftids_in_formula_decl undefTids phiVars;
    let sys = System.add_global_vars sys phiVars in

    (* Create VCGen module *)
    let solver = if !TllArgs.use_z3 then "Z3" else "Yices" in
    let module Pos  = (val PosSolver.choose solver  : PosSolver.S)  in
    let module Tll  = (val TllSolver.choose solver  : TllSolver.S)  in
    let module Tslk = (val TslkSolver.choose solver : TslkSolver.S) in
    let module Num  = (val NumSolver.choose solver  : NumSolver.S)  in
    let module VCG  = VCGen.Make(Pos)(Tll)(Tslk)(Num) in
    VCG.initialize ((System.get_trans_num sys) + 1) !TllArgs.coType 
      "" [] !TllArgs.hide_pres false;
    
    (* Enable TLL Reasoning *)
    VCG.enable_tll_dp ();

    let vc_info = { VCG.pc = 0;      VCG.smp = !TllArgs.coType;
                    VCG.stac = None; VCG.supps = [];           } in
    let _ = VCG.apply_dp_on_list [(phi,vc_info)] ""
    in
      ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise e

let _ = LeapDebug.flush()
