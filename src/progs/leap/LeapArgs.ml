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
let outFile           = ref ""
let detailedOutFile   = ref ""
let num_threads       = ref 1
let use_quantifiers   = ref false
let output_vcs        = ref false

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


let co_opt_list = ["dnf"; "union"; "pruning"]
let set_co co =
  match co with
  | "dnf" -> coType := Smp.Dnf
  | "union" -> coType := Smp.Union
  | "pruning" -> coType := Smp.Pruning
  | _ -> ()

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


let opts =
  [ ("-v",
        Arg.Int (fun i -> LeapVerbose.enable_verbose_up_to i),
        "verbosity level");
    ("-l",
        Arg.String (fun str -> logFile := str),
        "output log file");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-i",
        Arg.String inputInvariant,
        "invariant candidate");
*)
    ("-d",
        Arg.String inputInvFolder,
        "invariant folder");
    ("-g",
        Arg.String inputInvGraphFile,
        "invariant graph file");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
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
*)
    ("--focus",
        Arg.String focusPos,
        "pc1, pc2,... verifies transitions starting only at the given \
         program positions");
    ("--ignore",
        Arg.String ignorePos,
        "pc1, pc2,... ignores the given program transitions. It overrides \
         information loaded with \"focus\".");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-f",
        Arg.String inputFormula,
        "formula to verify using diagrams");
    ("-vd",
        Arg.String inputVd,
        "analyzes a verification diagram");
*)
    ("-pvd",
        Arg.String inputPvd,
        "analyzes a parametrized verification diagram");
    ("-dp",
        Arg.String set_dp,
        "indicates the DP to use. Options are: " ^
          String.concat "," (List.map DP.to_str DP.def_dp_list));
    ("-z3",
        Arg.Set use_z3,
        "uses z3 as smt solver");
    ("-yices+z3",
        Arg.Set use_yices_plus_z3,
        "uses yices for position reasoning and z3 for non position reasoning");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-sat",
        Arg.Set use_sat,
        "uses SAT when possible");
*)
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-ep",
        Arg.Set expand_pres,
        "expands preservation relation in generated VCs");
    ("-ca",
        Arg.Set count_abs,
        "enables counting abstraction");
*)
    ("-sm",
        Arg.Set show_models,
        "shows counter models for non valid VCs");
    ("-sl",
        Arg.Set show_label_info,
        "shows the information regarding parsed labels");
    ("-q",
        Arg.Set use_quantifiers,
        "use quantifiers over finite domains when constructing SMT queries");
    ("-ovc",
        Arg.Set output_vcs,
        "output VC information to a vcs folder");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-kpm",
        Arg.Set keep_primed_mem,
        "does consider primed memory variables when computing SMP cutoff");
    ("-gv",
        Arg.Set group_vars,
        "pre-group variables in equivalence classes when computing SMP cutoff");
*)
    ("-smt",
        Arg.Set use_smt,
        "enables the use of SMT-LIB translation if available");
    ("--debug",
        Arg.Unit setdebug,
        "debug output information");
    ("--show",
        Arg.Set showFlag,
        "show parsed program");
    ("--show_file_info",
        Arg.Set Debug._debug_show_tmpfile_info_,
        "shows path of temporary files");
    ("-o",
        Arg.Set_string outFile,
        "\"file\" outputs verification conditions to \"file\"");
    ("--version",
        Arg.Set Version._enable_,
        "show the current version");
(*
    THIS WAS REMOVED TO SIMPLIFIED LEAP
    ("-do",
        Arg.Set_string detailedOutFile,
        "\"folder\" outputs verification conditions to \"folder\"");
*)
   ]

let anon_fun str = 
  if !is_input_file then raise(MoreThanOneInputFile)
  else assigninputfile str

let usagemsg = "Parses a program and generates its FTS."
let error msg = Arg.usage opts msg ; exit 0
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
