open Printf
open LeapLib


module Eparser = ExprParser
module Elexer  = ExprLexer
module Expr    = Expression
module Symtbl  = ExprSymTable
module SolOpt  = SolverOptions

(****************)
(* main         *)
(****************)

let _ =
  try
    TslArgs.parse_args ();

    let phi = Parser.open_and_parse !TslArgs.phiFile
        (Eparser.single_formula Elexer.norm) in
      
    TslSolver.compute_model(true);
    let tsl_phi = TSLInterface.formula_to_tsl_formula phi in
    (* Solver options *)
    let opt = SolOpt.new_opt () in
    SolOpt.set_cutoff_strategy opt !TslArgs.coType;

    let sat = TslSolver.check_sat opt tsl_phi in

    if Sat.is_sat sat then begin
      TslSolver.print_model();
      print_endline "SAT"
    end else
      print_endline "UNSAT";
    ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
