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
    ThmArgs.parse_args ();

    let phi = Parser.open_and_parse !ThmArgs.phiFile
        (Eparser.single_formula Elexer.norm) in

    ThmSolver.compute_model(true);
    let thm_phi = ThmInterface.formula_to_thm_formula phi in
    let sat = ThmSolver.check_sat 1 (!ThmArgs.coType) (!ThmArgs.use_q) thm_phi in
    if Sat.is_sat sat then begin
        ThmSolver.print_model();
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
