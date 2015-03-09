(******************************************************************************)
(* @file LeapArgs.ml                                                          *)
(* Command Line Arguments for Leap                                            *)
(******************************************************************************)
open LeapLib

exception MoreThanOneInputFile
exception No_file
exception No_inv_folder
exception Unknown_tag of string

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let showFlag          = ref false
let debugFlag         = ref false
let pinvSys           = ref false
let pinvPlusSys       = ref false
let useGraph          = ref false
let openExtSys        = ref false
let binvSys           = ref false
let spinvSys          = ref false
let vcgenFlag         = ref false
let vdFlag            = ref false
let pvdFlag           = ref false
let use_z3            = ref false
let use_yices_plus_z3 = ref false
let use_sat           = ref false
let expand_pres       = ref false (*false*)
let count_abs         = ref false
let show_models       = ref false
let show_label_info   = ref false
let keep_primed_mem   = ref false (*false*)
let group_vars        = ref false
let use_smt           = ref false
let dpType            = ref (DP.NoDP)
let coType            = ref Smp.Pruning (*Smp.Dnf*)
let logFile           = ref ""
let invCandidate      = ref ""
let vdFormula         = ref ""
let supInvariant      = ref ""
let invFolder         = ref ""
let iGraphFile        = ref ""
let focusPC           = ref []
let ignorePC          = ref []
let vdFile            = ref ""
let pvdFile           = ref ""
let pvdSupport        = ref ""
let outFile           = ref ""
let detailedOutFile   = ref ""
let num_threads       = ref 1
let use_quantifiers   = ref false
let output_vcs        = ref false
let stop_on_invalid   = ref false

let assignopt (valref : 'a ref) (valbool : bool ref) (aval : 'a) : unit =
  valref := aval ; valbool := true

let setdebug () =
  LeapDebug.enable_debug();
  debugFlag := true

let inputInvFolder (s:string) =
  invFolder := s

let inputInvGraphFile (s:string) =
  useGraph := true;
  iGraphFile := s

let inputInvariant (s:string) =
  invCandidate := s

let inputFormula (s:string) =
  vdFormula := s

let inputClosedSys (s:string) = try
  binvSys := true;
  num_threads := int_of_string s;
  if !num_threads < 1 then
    Interface.Err.msg "Too few threads for a closed system" $
      "At least one thread must be part of a closed system."
  with e -> 
    Interface.Err.msg "Invalid argument" $
      Format.sprintf "Command option --vcgen-closed expects \
        an integer as argument, while \"%s\" was given." s;
    raise(e)


let inputVd (s:string) =
  vdFile := s

let inputPvd (s:string) =
  pvdFile := s

let inputPvdSupport (s:string) =
  pvdSupport := s

(* let dp_opt_list = List.map DP.to_str DP.def_dp_list *)
let set_dp dp =
  try
    dpType := (DP.from_str dp)
  with (DP.Unknown_dp_str s) as e ->
    begin
      Interface.Err.msg "Unknown decision procedure" $
        Format.sprintf "One of the following DP options was expected:\n\
                        %s. But %s was passed as argument."
        (String.concat "," (List.map DP.to_str DP.def_dp_list)) s;
        raise(e)
    end


let co_opt_list = List.map Smp.strategy_to_str Smp.def_strategy_list
let set_co co = try
                  coType := Smp.str_to_strategy co
                with (Smp.Unknown_strategy_str s) as e ->
                  begin
                    Interface.Err.msg "Unknown cutoff strategy" $
                      Format.sprintf "The strategy \"%s\" is not valid. Valid\
                                      strategies are: %s"
                                      s (String.concat "," co_opt_list);
                     raise(e)
                  end

let assigninputfile  (s:string) : unit = assignopt input_file is_input_file s
let supportInvariant (s:string) : unit = assignopt supInvariant spinvSys s

let parse_int_list (s:string) (field:int list ref) (fieldName:string) : unit =
  let regexp = Str.regexp "," in
  let split = Str.split regexp s in
  try field := List.map int_of_string split
  with e -> Interface.Err.msg"Bad argument" $
      "--" ^ fieldName^ " option expects a list of integers as argument.";
      raise(e)

let focusPos (s:string) : unit =
  parse_int_list s focusPC "focus"

let ignorePos (s:string) : unit =
  parse_int_list s ignorePC "ignore"


let opts = [
  ("-g",
     Arg.String inputInvGraphFile,
     "[file]  Input file with a proof graph for safety verification.");
  ("-d",
     Arg.String inputInvFolder,
     "[folder]  Input folder containing invariant candidates.");
  ("-pvd",
     Arg.String inputPvd,
     "[file]  Input file with a PVD, for liveness verification.");
  ("-ps",
     Arg.String inputPvdSupport,
    "[file]  Input file with support for PVD.");

  ("-focus",
     Arg.String focusPos,
     "[n1,n2..]  Verifies only the given program locations.");
  ("-ignore",
     Arg.String ignorePos,
     "[n1,n2..]  Ignores the given program locations. It overrides \"-focus\".");

  ("-dp",
     Arg.String set_dp,
     "[dp]  Indicates the DP to use. Options are: " ^
     String.concat "," (List.map DP.to_str DP.def_dp_list));
  ("-co",
     Arg.Symbol (co_opt_list,set_co),
     " Indicates the cut-off method for computing domain bounds.");

  ("-z3",
    Arg.Set use_z3,
    " Enables the use of Z3 as SMT solver.");
  ("-yices+z3",
    Arg.Set use_yices_plus_z3,
    " Enables Yices for position reasoning and Z3 for non position reasoning.");
  ("-smt",
     Arg.Set use_smt,
     " Enables the use of SMT-LIB translation if possible.");

  ("-q",
     Arg.Set use_quantifiers,
     " Enables quantifiers over finite domains when constructing SMT queries.");

  ("-si",
     Arg.Set stop_on_invalid,
     " Stops execution as soon as an invalid VC is found.");
  ("-sm",
     Arg.Set show_models,
     " Shows counter models for non valid VCs.");
  ("-show",
     Arg.Set showFlag,
     " Shows the parsed program");
  ("-sl",
     Arg.Set show_label_info,
     " Shows the information regarding parsed program labels.");

  ("-v",
     Arg.Int (fun i -> LeapVerbose.enable_verbose_up_to i),
     "[n]  Indicates the verbosity level.");
  ("-sf",
     Arg.Set Debug._debug_show_tmpfile_info_,
     " Outputs the paths to the temporary files where the SMT queries are written.");
  ("-ovc",
     Arg.Set output_vcs,
     " Enables the output of the generated VCs to a folder. See \"-o\".");
  ("-o",
     Arg.Set_string outFile,
     "[folder]  Indicates the folder where the generated VCs are output if \"-ovc\" is enabled.");

  ("-l",
     Arg.String (fun str -> logFile := str),
     "[file]  Indicates the output log file.");
  ("-debug",
     Arg.Unit setdebug,
     " Enables the output of debug information.");

  ("-version",
     Arg.Set Version._enable_,
     " Prints the current version of leap.");


(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-i",
        Arg.String inputInvariant,
        "invariant candidate");
    ("-pinv",
        Arg.Set pinvSys,
        "generate vc for an open system with arrays");
    ("-pinv+",
        Arg.Set pinvPlusSys,
        "generate vc for an open system with arrays with self support");
    ("-spinv",
        Arg.String supportInvariant,
        "file_1,file_2,...,file_n generates vc for an open system \
         using supporting invariants");
    ("-binv",
        Arg.String inputClosedSys,
        "#th generate vc for a closed system for #th threads");
    ("-f",
        Arg.String inputFormula,
        "formula to verify using diagrams");
    ("-vd",
        Arg.String inputVd,
        "analyzes a verification diagram");
    ("-sat",
        Arg.Set use_sat,
        "uses SAT when possible");
    ("-ep",
        Arg.Set expand_pres,
        "expands preservation relation in generated VCs");
    ("-ca",
        Arg.Set count_abs,
        "enables counting abstraction");
    ("-kpm",
        Arg.Set keep_primed_mem,
        "does consider primed memory variables when computing SMP cutoff");
    ("-gv",
        Arg.Set group_vars,
        "pre-group variables in equivalence classes when computing SMP cutoff");
    ("-do",
        Arg.Set_string detailedOutFile,
        "\"folder\" outputs verification conditions to \"folder\"");
*)
   ]

let anon_fun str = 
  if !is_input_file then raise(MoreThanOneInputFile)
  else assigninputfile str

let usagemsg =
  ("\n\nLEAP: A verification tool for temporal properties in concurrent parametrized systems.\n\n" ^
   "Usage:\n" ^
   "  leap [options] [prg file]\n\n" ^
   "Available options are:\n")
let error msg = Arg.usage (Arg.align opts) msg ; exit 0
let simple_error msg = Printf.printf "%s\n" msg ; exit 0
let postcheck () =
  begin
    if List.length
      (List.filter id [!binvSys;!pinvSys;!pinvPlusSys;
                       !spinvSys;!useGraph]) > 1 then
      begin
        Interface.Err.msg
          "More that one vc generation chosen"
          "Choose only one of the following options: \n\
           -binv\n\
           -pinv\n\
           -pinv+\n\
           -spinv\n\
           -g\n";
        exit(0)
      end;
  end

let parse_args _ = 
  Arg.parse opts anon_fun usagemsg;
  postcheck ()
  
let open_input _ =
  if !is_input_file then begin
    input_file_fd := Unix.openfile !input_file [Unix.O_RDONLY] 0 ;
    Unix.in_channel_of_descr !input_file_fd
    end
  else raise(No_file)(*stdin*)

let close_input _ =
  if !is_input_file then Unix.close !input_file_fd
