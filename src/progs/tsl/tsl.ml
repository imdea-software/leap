open Printf
open LeapLib


module Eparser = ExprParser
module Elexer  = ExprLexer
module Expr    = Expression
module Symtbl  = ExprSymTable

(****************)
(* main         *)
(****************)

let _ =
  try
		TslArgs.parse_args ();

		let phi = Parser.open_and_parse !TslArgs.phiFile
				(Eparser.single_formula Elexer.norm) in
      

		let tsl_phi = TSLInterface.formula_to_tsl_formula phi in
		let sat = TslSolver.is_sat 1 (!TslArgs.coType) false tsl_phi in                                     
		if sat then
			print_endline "SAT"
		else
			print_endline "UNSAT";
		()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
