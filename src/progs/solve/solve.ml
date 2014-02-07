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
    SolveArgs.parse_args ();
    let ch = SolveArgs.open_input () in
    let phi = Parser.parse ch (Eparser.single_formula Elexer.norm) in
    SolveArgs.close_input ();

    (* Choose decision procedure *)
    Printf.printf "Parsed formula is:\n%s\n\n" (Expr.formula_to_str phi);

    let valid =
      match !SolveArgs.dpType with
      | DP.NoDP -> (print_endline "NO DP PROVIDED"; false)
      | DP.Loc -> false
      | DP.Num -> let module Num = (val (NumSolver.choose BackendSolvers.Yices.identifier)) in
                  Num.compute_model true;
                  let valid = Num.is_valid (NumInterface.formula_to_int_formula phi) in
                  if not valid then Num.print_model();
                  valid
      | DP.Tll -> let module Tll = (val (TllSolver.choose BackendSolvers.Z3.identifier)) in
                  Tll.compute_model true;
                  let tll_phi = TllInterface.formula_to_tll_formula phi in
                  let valid = Tll.is_valid 1 !SolveArgs.coType tll_phi in
                  if not valid then Tll.print_model();
                  valid
      | DP.Tslk k -> let module Tslk = (val (TslkSolver.choose BackendSolvers.Z3.identifier k)) in
                     let module TSLKIntf = TSLKInterface.Make(Tslk.TslkExp) in
                     Tslk.compute_model true;
                     let tslk_phi = TSLKIntf.formula_to_tslk_formula phi in
                     let valid = Tslk.is_valid 1 !SolveArgs.coType
                                   !SolveArgs.use_quantifiers tslk_phi in
                     if not valid then Tslk.print_model();
                     valid
      | DP.Tsl -> let tsl_phi = TSLInterface.formula_to_tsl_formula phi in
                  TslSolver.compute_model true;
                  let valid = TslSolver.is_valid 1 !SolveArgs.coType
                                !SolveArgs.use_quantifiers tsl_phi in
                  if not valid then TslSolver.print_model();
                  valid
    in
      if valid then
        print_endline "VALID"
      else
        print_endline "NOT VALID"
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
