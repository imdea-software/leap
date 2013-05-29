(******************************************************************************)
(* @file PvdArgs.ml                                                          *)
(* Command Line Arguments for PVD                                            *)
(******************************************************************************)
open LeapLib

exception MoreThanOneInputFile
exception No_file
exception File_not_found of string

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
let vdFile       = ref ""
let pvdFile      = ref ""
let vdFormula    = ref ""
let outFile      = ref ""

let assignopt (valref : 'a ref) (valbool : bool ref) (aval : 'a) : unit =
  valref := aval ; valbool := true

let setdebug () =
  LeapDebug.enable_debug();
  debugFlag := true

let inputFormula (s:string) =
  vdFormula := s


let inputVd (s:string) =
  vdFile := s

let inputPvd (s:string) =
  pvdFile := s

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

let opts =
  [ ("-v",
        Arg.Set verbose,
        "verbose");
    ("-f",
        Arg.String inputFormula,
        "formula to verify using diagrams");
    ("-vd",
        Arg.String inputVd,
        "analyzes a verification diagram");
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
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
    ("-ep",
        Arg.Set expand_pres,
        "expands preservation relation in generated VCs");
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
  else raise(No_file)(*stdin*)

let close_input _ =
  if !is_input_file then Unix.close !input_file_fd

(* Auxiliary functions *)
let open_and_parse_expr file_name the_parser =
  let input = try open_in file_name
    with _ -> begin
      Interface.Err.msg "File not found" $
        Printf.sprintf "File \"%s\" could not be found" file_name;
          raise(File_not_found file_name)
    end in
  let res = the_parser Exprlexer.norm (Lexing.from_channel input) in
  res    
