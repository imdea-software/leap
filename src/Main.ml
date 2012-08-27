(* File main.ml *)

open LeapLib
open Expr
open Parsers
open Interface
open Diagrams
open Arg
open Printf

(* Input parsing *)

type inputOptions = {mutable program:string;
                     mutable formula:string;
                     mutable diagram:string}

let options = ref {program=""; formula=""; diagram=""}

let inProg (s:string) =
  options := {program=s;
              formula = (!options).formula;
              diagram = (!options).diagram}

let inFormula (s:string) =
  options := {program=(!options).program;
              formula=s;
              diagram = (!options).diagram}

let inDiagram (s:string) =
  options := {program = (!options).program;
              formula = (!options).formula;
              diagram=s}

let usage_msg = "Options:"
let argv_opts = ("-p",
                  Arg.String inProg,
                  "prog Loads a program from prog file.")::
                ("-i",
                  Arg.String inFormula,
                  "form Loads an invariant formula from form file.")::
                ("-d",
                  Arg.String inDiagram,
                  "dia Loads a general verification diagrams from dia file")::
                ("-debug",
                  Arg.Set _debug_,
                  "Enables debug output")::
                []

let main () =

    Arg.parse
      argv_opts
      (fun s -> (Printf.eprintf "Unrecognized options: %s\n" s); exit(1))
      usage_msg;

    if !_debug_ then
      printf "***************   DEBUG MODE ON   ***************\n\n";
  
    if (String.compare !options.program "" != 0) then (
    (*Should check both, program and inv. *)
    try
      let resSys = SPLParser.parseSystem (File.readFile !options.program) in
      let resInv = SPLParser.parseFormula (File.readFile !options.formula) in
        match (resSys, resInv) with
          (Some sys, Some form)
                   -> printf "Invariant candidate:\n%s\n\n" 
                        (Expr.string_of_formula form);
                      printf "%s\n\n" (Expr.string_of_system sys);
                      printf "====================================\n\
                              Initial conditions:\n\
                              ====================================\n\n";
                      printf "%s"
                        (String.concat "\n"
                          (List.map
                            (fun p -> sprintf "%s:\n%s\n\n"
                                        (Expr.get_proc_name p)
                                        (Expr.string_of_boolExp
                                          (Expr.gen_theta
                                            (Expr.get_sys_global sys) p))
                            ) (Expr.get_sys_procs sys)));
                      printf "====================================\n\
                              Verification conditions:\n\
                              ====================================\n\n";
                      ignore $ List.map (fun p -> printf "Process: %s\n\n%s\n\n"
                                          (Expr.get_proc_name p)
                                          (String.concat "\n----------\n"
                                            (List.map Expr.string_of_formula
                                              (Expr.gen_inv_vc sys p form))
                                          )
                               )
                      (Expr.get_sys_procs sys);
                      printf "====================================\n\
                              Fair Transition System:\n\
                              ====================================\n\n";

                      ignore $ printf "%s\n"
                                (Expr.string_of_fts (Expr.gen_pfts sys));
                      ()
        | (_,_) -> ();
      with
        Sys_error msg -> Err.msg "Error trying to read input files.\n" ""
    );

    if (String.compare !options.diagram "" != 0) then
      (
        printf "====================================\n\
                Diagram information:\n\
                ====================================\n\n";
        let resDia = VDParser.parseVD (File.readFile !options.program) in
          match resDia with
            Some dia -> printf "%s\n" (VD.string_of_vd dia)
          | _ -> ();
      );
      

    exit 0;;


main ();;
