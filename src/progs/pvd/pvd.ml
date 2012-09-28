open Printf

open LeapLib
open Global


module Expr    = Expression
module Sys     = System
module Eparser = Exprparser
module Symtbl  = Exprsymtable


exception MoreThanOneInputFile
exception No_file
exception File_not_found of string



(****************)
(* main         *)
(****************)

let _ =
  try let _ = PvdArgs.parse_args () in
    let ch = PvdArgs.open_input () in
    let (sys,undefTids) = 
      Stmparser.system Stmlexer.norm (Lexing.from_channel ch) in
    let _ = PvdArgs.close_input () in

    (* We load the system in the formula parser, just in case *)
    let _ = Symtbl.load_system sys in

    (* Shows the parsed system *)
    let _ = if (!PvdArgs.showFlag = true) then Report.report_system sys in

    (* Create VCGen module *)
    let solver = 
      if !PinvArgs.use_z3 then BackendSolvers.Z3.identifier 
      else BackendSolvers.Yices.identifier in
    let module Pos  = (val PosSolver.choose  solver : PosSolver.S)  in
    let module Tll  = (val TllSolver.choose  solver : TllSolver.S)  in
    let module Tslk = (val TslkSolver.choose solver : TslkSolver.S) in
    let module Num  = (val NumSolver.choose  solver : NumSolver.S)  in
    let module VCG  = VCGen.Make(Pos)(Tll)(Tslk)(Num) in
    VCG.initialize ((Sys.get_trans_num sys) + 1) !PinvArgs.coType 
      !PinvArgs.outFile [] !PinvArgs.hide_pres !PinvArgs.count_abs;
    let module VD = Diagrams.Make(VCG) in
    
    VCG.enable_dp (!PinvArgs.dpType);

    (* No VD and PVD provided at the same time *)
    if (!PvdArgs.vdFile <> "" && !PvdArgs.pvdFile <> "") then
    begin
      Interface.Err.msg "VD and PVD provided" $
        sprintf "Both, a verification diagram in file:\n%s\n and a \
            parametrized verification diagram in file:\n%s\n were \
            provided. Only one of them can be analyzed at a time."
          !PvdArgs.vdFile !PvdArgs.pvdFile
    end;

    if (!PvdArgs.vdFile <> "" || !PvdArgs.pvdFile <> "") then begin
      let (vd_phi_voc, phi_vars, vd_phi) = match !PvdArgs.vdFormula with
        | "" -> ([], Sys.empty_var_table, Expr.True)
        | _  -> 
          let (phi_vars, tag, phi) = 
            PvdArgs.open_and_parse_expr !PvdArgs.vdFormula Eparser.vd_formula in
            (Expr.voc phi, phi_vars, phi) in
      System.undeftids_in_formula_decl undefTids phi_vars;
      let sys = System.add_global_vars sys phi_vars in

      if (!PvdArgs.vdFile <> "") then begin
        let vd = PvdArgs.open_and_parse_expr !PvdArgs.vdFile Eparser.diagram in
        let vc = VD.gen_vd_vc !PvdArgs.hide_pres sys vd in
        printf "---------------- Verification Diagram ----------------\n\
                %s\n\
                ---------------- Verification Diagram ----------------\n"
          (Diagrams.PP.vd_to_str vd);
        printf "--------------- Verification Conditions --------------\n\
                %s\n\
                --------------- Verification Conditions --------------\n"
          (Diagrams.PP.vc_to_str vc);
      end;

      if (!PvdArgs.pvdFile <> "") then begin
        let (parsed_pvd, remains) = 
          PvdArgs.open_and_parse_expr !PvdArgs.pvdFile Eparser.param_diagram in
          let pvd = VD.load_pvd_formula_param parsed_pvd remains vd_phi_voc in
          (* Notice that we have in vd_phi the formula to be passed to the
           model checker *)
          printf "---------------- Verification Diagram ----------------\n\
                  %s\n\
                  ---------------- Verification Diagram ----------------\n"
            (VD.pvd_to_str pvd);

        if VCG.some_dp_enabled () then
          ignore (VD.check_pvd sys pvd)
        else begin
          let vc = VD.gen_pvd_vc !PvdArgs.hide_pres sys pvd in
          printf "------------ Verification Conditions ------------\n\
                  %s\n\
                  ------------ Verification Conditions ------------\n"
          (Diagrams.PP.vc_to_str vc)
        end
      end
    end; ()
  with
  | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
  | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
      sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
  | e -> raise e

let _ = LeapDebug.flush()
