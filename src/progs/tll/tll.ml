open Printf
open LeapLib


module Eparser = ExprParser
module Elexer  = ExprLexer
module Expr    = Expression
module Symtbl  = ExprSymTable

(****************)
(* main         *)
(****************)

let tllSolver : (module TllSolver.S) = TllSolver.choose("z3")


let _ =
  try
    TllArgs.parse_args ();

    let phi = Parser.open_and_parse !TllArgs.phiFile
        (Eparser.single_formula Elexer.norm) in
      

    let tll_phi = TllInterface.formula_to_tll_formula phi in
    let module TllSat = (val tllSolver) in
    TllSat.compute_model(true);

    let sat = TllSat.check_sat 1 (!TllArgs.coType) true tll_phi in
    if Sat.is_sat sat then begin
        TllSat.print_model();
        print_endline "SAT"
      end
    else
      print_endline "UNSAT";
    ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
