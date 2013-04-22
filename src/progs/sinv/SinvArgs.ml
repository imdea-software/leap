(******************************************************************************)
(* @file SinvArgs.ml                                                          *)
(* Command Line Arguments for SInv                                            *)
(******************************************************************************)
open LeapLib

exception MoreThanOneInputFile
exception No_file

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose      = ref false
let showFlag     = ref false
let debugFlag    = ref false
let use_z3       = ref false
let expand_pres    = ref false
let count_abs    = ref false
let dpType       = ref (DP.NoDP)
let coType       = ref Smp.Pruning (*Smp.Dnf*)
let invCandidate = ref ""
let supInvariant = ref ""
let spinvSys     = ref false
let focusPC      = ref []
let ignorePC     = ref []
let outFile      = ref ""

let assignopt (valref : 'a ref) (valbool : bool ref) (aval : 'a) : unit =
  valref := aval ; valbool := true

let setdebug () =
  LeapDebug.enable_debug();
  debugFlag := true

let inputInvariant (s:string) =
  invCandidate := s


let set_dp dp =
  try
    dpType := (DP.from_str dp)
  with (DP.Unknown_dp_str s) as e ->
    begin
      Interface.Err.msg "Unknown decision procedure" $
        Format.sprintf "One of the following DP options was expected:\n\
                        %s. But %s was passed as argument."
        (String.concat "," (List.map DP.to_str DP.def_dp_list)) s;
        RAISE(e)
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
      RAISE(e)

let focusPos (s:string) : unit =
  parse_int_list s focusPC "focus"

let ignorePos (s:string) : unit =
  parse_int_list s ignorePC "ignore"

let opts =
  [ ("-v",
        Arg.Set verbose,
        "verbose");
    ("-i",
        Arg.String inputInvariant,
        "invariant candidate");
    ("-s",
            Arg.String supportInvariant,
            "file_1,file_2,...,file_n generates vc for an open system \
             using supporting invariants");
    ("-dp",
        Arg.String set_dp,
        "indicates the DP to use. Options are: " ^
          String.concat "," (List.map DP.to_str DP.def_dp_list));
    ("-z3",
        Arg.Set use_z3,
        "uses z3 as smt solver");
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
    ("-ep",
        Arg.Set expand_pres,
        "preserves preservation relation in generated VCs");
    ("-ca",
        Arg.Set count_abs,
        "enables counting abstraction");
    ("--focus",
            Arg.String focusPos,
            "pc1, pc2,... verifies transitions starting only at the given \
             program positions");
    ("--ignore",
        Arg.String ignorePos,
        "pc1, pc2,... ignores the given program transitions. It overrides \
         information loaded with \"focus\".");
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
   ]

let anon_fun str = if !is_input_file then
                     RAISE(MoreThanOneInputFile)
                   else
                     assigninputfile str

let usagemsg = "Parses a program and generates its FTS."
let error msg = Arg.usage opts msg ; exit 0
let simple_error msg = Printf.printf "%s\n" msg ; exit 0
let postcheck () = ()

let parse_args _ = 
  Arg.parse opts anon_fun usagemsg;
  postcheck ()
  
let open_input _ =
  if !is_input_file then begin
    input_file_fd := Unix.openfile !input_file [Unix.O_RDONLY] 0 ;
    Unix.in_channel_of_descr !input_file_fd
    end
  else RAISE(No_file) (*stdin*)

let close_input _ =
  if !is_input_file then Unix.close !input_file_fd
    
