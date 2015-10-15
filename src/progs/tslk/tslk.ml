open Printf
open LeapLib


module Eparser = ExprParser
module Elexer  = ExprLexer
module Expr    = Expression
module Symtbl  = ExprSymTable

(****************)
(* main         *)
(****************)

let tslkSolver : (module TslkSolver.S) = TslkSolver.choose("z3") (!TslkArgs.k)

let _ =
  try
    TslkArgs.parse_args ();

    let phi = Parser.open_and_parse !TslkArgs.phiFile
        (Eparser.single_formula Elexer.norm) in

    

      
    let module TslkSat = (val tslkSolver) in
    let module TSLKIntf = TSLKInterface.Make(TslkSat.TslkExp) in
    let tslk_phi = TSLKIntf.formula_to_tslk_formula phi in
    TslkSat.compute_model(true);
    let sat = TslkSat.check_sat 1 (!TslkArgs.coType) false tslk_phi in

    if Sat.is_sat sat then begin
      TslkSat.print_model();
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
