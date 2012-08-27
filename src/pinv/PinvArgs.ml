(******************************************************************************)
(* @file PinvArgs.ml                                                          *)
(* Command Line Arguments for PInv                                            *)
(******************************************************************************)
open LeapLib

exception MoreThanOneInputFile
exception No_file

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose      = ref false
let pinvPlusSys  = ref false
let showFlag     = ref false
let debugFlag    = ref false
let use_z3       = ref false
let hide_pres    = ref false
let count_abs    = ref false
let dpType       = ref ""
let coType       = ref VCGen.Dnf
let invCandidate = ref ""
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


let dp_opt_list = ["num"; "tll"]
let set_dp dp =
  dpType := dp
(*  match dp with
    "num" -> dpType := Vcgen.enable_num_dp !dpType
  | "tll" -> dpType := Vcgen.enable_tll_dp !dpType
  | _     -> ()
*)

let co_opt_list = ["dnf"; "union"; "pruning"]
let set_co co =
  match co with
  | "dnf" -> coType := VCGen.Dnf
  | "union" -> coType := VCGen.Union
  | "pruning" -> coType := VCGen.Pruning
  | _ -> ()

let assigninputfile  (s:string) : unit = assignopt input_file is_input_file s

let parse_int_list (s:string) (field:int list ref) (fieldName:string) : unit =
  let regexp = Str.regexp "," in
  let split = Str.split regexp s in
  try field := List.map int_of_string split
  with e -> Interface.Err.msg"Bad argument" $
      "--" ^ fieldName^ " option expects a list of integers as argument.";
      raise e

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
    ("--self",
        Arg.Set pinvPlusSys,
        "generate vc for an open system with arrays with self support");
    ("--focus",
        Arg.String focusPos,
        "pc1, pc2,... verifies transitions starting only at the given \
         program positions");
    ("--ignore",
        Arg.String ignorePos,
        "pc1, pc2,... ignores the given program transitions. It overrides \
         information loaded with \"focus\".");
    ("-dp",
        Arg.Symbol (dp_opt_list,set_dp),
        "indicates the decision procedure to be used");
    ("-z3",
        Arg.Set use_z3,
        "uses z3 as smt solver");
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
    ("-hp",
        Arg.Set hide_pres,
        "hides preservation relation in generated VCs");
    ("-ca",
        Arg.Set count_abs,
        "enables counting abstraction");
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
                     raise(MoreThanOneInputFile)
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
  else raise No_file (*stdin*)

let close_input _ =
  if !is_input_file then Unix.close !input_file_fd
    
