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
    TslArgs.parse_args ();
(*
    let ch = TslArgs.open_input () in
    let (tmp_sys,undefTids) = Parser.parse ch (Stmparser.system Stmlexer.norm) in

    let sys = System.set_threads tmp_sys 1 in
    TslArgs.close_input ();
*)

    (* We load the system in the formula parser, just in case *)
(*    Symtbl.load_system sys; *)

    let phiVars, phi = Parser.open_and_parse !TslArgs.phiFile 
      (Eparser.single_formula Elexer.norm) in
      
    (* Check whether undef tids are included in invVars *)
(*
    System.undeftids_in_formula_decl undefTids phiVars;
    let sys = System.add_global_vars sys phiVars in
*)

    (* Create VCGen module *)
    let solver = if !TslArgs.use_z3 then "Z3" else "Yices" in
    let module Pos  = (val PosSolver.choose solver    : PosSolver.S)  in
    let module Tll  = (val TllSolver.choose solver    : TllSolver.S)  in
    let module Tslk = (val TslkSolver.choose solver 1 : TslkSolver.S) in
    let module Num  = (val NumSolver.choose solver    : NumSolver.S)  in
    let module VCG  = VCGen.Make(Pos)(Tll)(Tslk)(Num) in
    VCG.initialize 1 !TslArgs.coType "" [] !TslArgs.hide_pres false;
    
    (* Enable TSL Reasoning *)
    VCG.enable_tsl_dp ();

    let vc_info = { VCG.pc = 0;      VCG.smp = !TslArgs.coType;
                    VCG.stac = None; VCG.supps = []; try_pos = false; } in
    let _ = VCG.apply_dp_on_list [(phi,vc_info)] ""
    in
      ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> RAISE(e)

let _ = LeapDebug.flush()
