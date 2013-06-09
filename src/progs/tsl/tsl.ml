open Printf
open LeapLib

open Gen


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

    if !TslArgs.verbose then LeapVerbose.enable_verbose();
    let ch = TslArgs.open_input () in
    let (_,phi) = Parser.parse ch
                    (Eparser.single_formula Elexer.norm) in
    TslArgs.close_input ();

    (* Create VCGen module *)
    let solver = if !TslArgs.use_z3 then "Z3" else "Yices" in
    let module Pos  = (val PosSolver.choose solver    : PosSolver.S)  in
    let module Tll  = (val TllSolver.choose solver    : TllSolver.S)  in
    let module Tslk = (val TslkSolver.choose solver 1 : TslkSolver.S) in
    let module Num  = (val NumSolver.choose solver    : NumSolver.S)  in
    let module VCG  = VCGen.Make(Pos)(Tll)(Tslk)(Num) in
    VCG.initialize 1 !TslArgs.coType "" [] !TslArgs.hide_pres false;
    
    (* Enable TSL Reasoning *)
(*
    VCG.enable_tsl_dp ();
*)
    (* Create the single task *)
    let (ante, conse) = match phi with
                        | Expr.Implies (a,b) -> (a,b)
                        | _ -> (Expr.True, phi) in
    let inv_info = Expr.new_formula_info phi in
    inv_info.Expr.formula <- ante;
    inv_info.Expr.primed <- conse;
(*
    let task = Tactics.new_task [] None Expr.True inv_info [] Expr.NoThid 0 in
*)

(*
    let res_tasks = Tactics.apply_post_tacs [task]
                      !TslArgs.postTactics !TslArgs.hide_pres in
*)

    let vc_info = { VCG.pc = 0;      VCG.smp = !TslArgs.coType;
                    VCG.stac = None; VCG.supps = []; try_pos = false; } in
(*
    let _ = VCG.apply_dp_on_list (List.map (fun (phi,_) -> (phi,vc_info)) res_tasks) ""
    in
*)
      ()
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
