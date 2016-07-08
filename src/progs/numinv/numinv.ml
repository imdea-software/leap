
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


(****************)
(* ARGS         *)
(****************)

open Printf

open LeapLib
open Global

module Expr = Expression
module Sys  = System
module Vd   = Diagrams



exception MoreThanOneInputFile
exception No_file
exception File_not_found of string


(* Configuration *)
let spec_folder = "examples/invs/"
let spec_type = ".inv"


let assignopt valref valbool aval = 
  valref := aval ; valbool := true

let input_file = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose               = ref false
let showFlag              = ref false
let updLocsFlag           = ref false
let iterateFlag           = ref false
let hideNumProblemFlag    = ref false
let noSelfLoopFlag        = ref false
let show_stat_info        = ref false
let useLabelsFlag         = ref false
let invOutFile            = ref ""
let composedThreadsParams = ref [Expr.VarTh (Expr.build_global_var "i1" Expr.Tid)]
let domainType            = ref Numprog.Poly
let tacticType            = ref None
let absIntMode            = ref Numprog.Eager

let domain_opt_list = ["poly"; "intvl"; "oct"; "intvl+poly";"eq"]
let tactic_opt_list = ["split"; "focus"]
let mode_opt_list   = ["lazy"; "eager"; "interf"; "eager+"]

let set_domain d =
  match d with
    "poly"       -> domainType := Numprog.Poly
  | "intvl"      -> domainType := Numprog.Intvl
  | "oct"        -> domainType := Numprog.Oct
  | "intvl+poly" -> domainType := Numprog.IntvlPoly
  | "eq" -> domainType := Numprog.Eq
  | _            -> ()

let set_tactic t =
  match t with
    "split" -> tacticType := Some Numprog.Split
  | "focus" -> tacticType := Some Numprog.Focus
  | _       -> ()

let set_mode m =
  match m with
    "lazy"   -> absIntMode := Numprog.Lazy
  | "interf" -> absIntMode := Numprog.Interf
  | "eager"  -> absIntMode := Numprog.Eager
  | "eager+" -> absIntMode := Numprog.EagerPlus
  | _        -> ()



let assignopt s opt opt_flag = opt := s ; opt_flag := true
let assigninputfile s = assignopt s input_file is_input_file
(* Program arguments *)


let set_debug i =
  LeapDebug.enable_debug ();
  Debug._debug_ := true;
  Debug._debug_level_ := i


let set_compose_threads i =
  let th_list = LeapLib.rangeList 1 i
  in
    composedThreadsParams := List.map (fun i ->
                               Expr.VarTh (Expr.build_global_var ("i" ^ (string_of_int i)) Expr.Tid)
                             ) th_list


let set_widening i =
  if i < 2 then
    begin
      Interface.Err.msg "Insufficient steps to apply widening"
                        "At least two steps are required to apply widening";
      exit(1)
    end
  else
    Numprog.wait_for_widening := i


let set_trs_widening i =
  if i < 1 then
    begin
      Interface.Err.msg "Too small trs widening"
                        "A value greater than 0 was expected";
      exit(1)
    end
  else
    Numprog.trs_widening := i


let set_inv_out_file f =
  invOutFile := f


module MyArgs =
  struct
    let myopts =
      [ ("-v", Arg.Set verbose,"verbose");
        ("--show", Arg.Set showFlag, "show parsed program");
        ("--iterate", Arg.Set iterateFlag, "iterates looking for invariants");
        ("--inv_file", Arg.String set_inv_out_file,
              "outputs invariants to be checked against an specification");
        ("--compose", Arg.Int set_compose_threads, "composes many threads");
        ("-d", Arg.Symbol (domain_opt_list, set_domain), "sets the abst-int domain");
        ("-t", Arg.Symbol (tactic_opt_list, set_tactic), "sets the tactic for speedup");
        ("--updlocs", Arg.Set updLocsFlag, "update location guards on each iteration");
        ("-m", Arg.Symbol (mode_opt_list, set_mode), "sets abstr-int mode");
        ("--widening_after", Arg.Int set_widening,
            "applies widening after some steps");
        ("--trs_widening", Arg.Int set_trs_widening,
            "widening parameter for trs");
        ("--use_labels", Arg.Set useLabelsFlag,
            "use labels for counting abstraction");
        ("--hide_problem", Arg.Set hideNumProblemFlag,
            "hides the description of the numeric problem");
        ("--no_selfloop", Arg.Set noSelfLoopFlag,
            "does not generate information for selfloops");
        ("--show_invariants", Arg.Set Debug._debug_show_invTables_,
            "shows intermediate invariants");
        ("--show_problems", Arg.Set Debug._debug_show_problems_,
            "shows intermediate problem descriptions");
        ("--show_file_info", Arg.Set Debug._debug_show_tmpfile_info_,
            "shows path of temporary files");
        ("--show_widening_info", Arg.Set Debug._debug_show_widening_formula_,
            "shows the computed widening formulas");
        ("--show_smt", Arg.Set Debug._debug_show_smt_,
            "shows the queries made to smt solver");
        ("--show_statistic_info", Arg.Set show_stat_info,
            "displays statistic information");
        ("--debug", Arg.Int set_debug, "debug level")
      ]

    let anon_fun str = if !is_input_file then
                         raise(MoreThanOneInputFile)
                       else
                         assigninputfile str

    let usagemsg = "Generates a transition system for numeric program."

    let error msg = Arg.usage myopts msg ; exit 0

    let simple_error msg = Printf.printf "%s\n" msg ; exit 0

    let postcheck () = ()

  end


let parse_args _ = Arg.parse MyArgs.myopts MyArgs.anon_fun MyArgs.usagemsg ;
                   MyArgs.postcheck ()


let open_input _ =
  if !is_input_file then
    begin
      input_file_fd := Unix.openfile !input_file [Unix.O_RDONLY] 0 ;
      Unix.in_channel_of_descr !input_file_fd
    end
  else
    raise(No_file)
    (*stdin*)

let close_input _ =
  if !is_input_file then Unix.close !input_file_fd


(****************)
(* main         *)
(****************)

let _ =


  try
    let _        = parse_args () in
    let ch       = open_input () in
    let (tSys,_) = Parser.parse ch (StmParser.system StmLexer.norm) in
    let _        = close_input () in

    (* We do not need the heap in numeric programs *)
    let sys      = Sys.del_global_var tSys Conf.heap_name in

    let _        = Sys.check_is_numeric sys in
    (* let orig_widening_steps = !Numprog.wait_for_widening in *)


    (* Shows the parsed system *)
    let _ = if (!showFlag) then Report.report_system sys in

    let prob_name = List.hd $
                      Str.split (Str.regexp "\\.")
                                (Filename.basename !input_file) in
    (* let prob_vars = Numprog.get_num_vars_from_sys sys in
       let prob_locs = Numprog.get_locs_from_sys sys in *)
    let num_p =
        Numprog.new_num_problem (prob_name)
                                (not !noSelfLoopFlag)
                                (sys)
                                (!composedThreadsParams)
                                (!useLabelsFlag)
                                (!tacticType)
                                (!updLocsFlag)
                                (!absIntMode) in

    if !show_stat_info then
      begin
        printf "=============== Benchmark information ================\n";
        printf "%s" (Numprog.stat_info_str sys num_p);
        printf "=============== Benchmark information ================\n";
      end;


    if !iterateFlag then
        let inv_cand = Numprog.iterate num_p !domainType in
        let _ = printf "--------------------------------------------------\n" in
        match inv_cand with
          None         -> printf "No candidates.\n"
        | Some inv_tbl -> begin
                            let _ = printf "Finish after:\n\
                                            Iterations: %i\n\
                                            Widening steps : %i\n"
                                              !Numprog.iterations
                                              !Numprog.widening_steps in
                            if !invOutFile <> "" then
                              let spec_str = Numprog.invs_for_spec inv_tbl in
                              let spec_out = open_out !invOutFile in
                              let _ = output_string spec_out spec_str in
                              let _ = close_out spec_out
                              in
                                print_endline
                                 (sprintf "Invariants written to: %s"
                                            !invOutFile)
                          end
    else
      if not !hideNumProblemFlag then
        begin
          printf "=============== Problem description ==================\n";
          printf "%s" (Numprog.num_problem_to_str num_p);
          printf "=============== Problem description ==================\n";
        end;


  with
    | Global.ParserError msg -> Interface.Err.msg "numinv: Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "numinv: Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise(e)

let _ = LeapDebug.flush()
