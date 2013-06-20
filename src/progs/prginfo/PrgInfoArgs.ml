(******************************************************************************)
(* @file P2FArgs.ml                                                           *)
(* Command Line Arguments for Prog2FTS                                        *)
(******************************************************************************)
open LeapLib

exception MoreThanOneInputFile
exception No_file

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose         = ref false
let debugFlag       = ref false
let show_label_info = ref false

let assignopt (valref : 'a ref) (valbool : bool ref) (aval : 'a) : unit =
  valref := aval ; valbool := true

let assigninputfile  (s:string) : unit = assignopt input_file is_input_file s

let setdebug () =
  LeapDebug.enable_debug();
  debugFlag := true

let opts =
  [ ("-v",
        Arg.Set verbose,
        "verbose");
    ("-sl",
        Arg.Set show_label_info,
        "shows the information regarding parsed labels");
    ("--debug",
        Arg.Unit setdebug,
        "debug output information");
   ]

let anon_fun str = 
  if !is_input_file then raise(MoreThanOneInputFile)
  else assigninputfile str

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
    
