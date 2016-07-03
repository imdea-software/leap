(******************************************************************************)
(* @file ThmArgs.ml                                                           *)
(* Command Line Arguments for Thm                                             *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let debugFlag       = ref false
let use_z3          = ref false
let use_q           = ref false
let coType          = ref Smp.Pruning (*Smp.Dnf*)
let hide_pres       = ref true
let phiFile         = ref ""
let arrangement_gen = ref false

let assignopt (valref : 'a ref) (valbool : bool ref) (aval : 'a) : unit =
  valref := aval ; valbool := true

let setdebug () =
  LeapDebug.enable_debug();
  debugFlag := true

let inputFormula (s:string) = 
  phiFile := s

let co_opt_list = ["dnf"; "union"; "pruning"]
let set_co co =
  match co with
  | "dnf" -> coType := Smp.Dnf
  | "union" -> coType := Smp.Union
  | "pruning" -> coType := Smp.Pruning
  | _ -> ()

let assigninputfile  (s:string) : unit = assignopt input_file is_input_file s

let opts =
  [
    ("-f",
        Arg.String inputFormula,
        "TLL formula");
    ("-ag",
       Arg.Set arrangement_gen,
       " Enables the generation of satisfiable arrangements using SMT solvers.");  
    ("-q",
        Arg.Set use_q,
        "activates the use of quantifier over finite domains");
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
    ("-hp",
        Arg.Set hide_pres,
        "hides preservation relation in generated VCs");
    ("-sf",
        Arg.Set Debug._debug_show_tmpfile_info_,
        "shows path of temporary files");
    ("--debug",
        Arg.Unit setdebug,
        "debug output information");
    ("-testing",
       Arg.Set LeapDebug._testing_,
       " Reduces the size of the generated models for accelerating testing."); 
  ]

let anon_fun str = 
  if !is_input_file then raise(MoreThanOneInputFile)
  else assigninputfile str

let usagemsg = "Parses a program and generates its FTS."
let error msg = Arg.usage opts msg ; exit 0
let simple_error msg = Printf.eprintf "%s\n" msg ; exit 0
let postcheck () = () (*
  if !phiFile = "" then begin
    Interface.Err.msg "Missing file"
      "No file with TLL formula using the -f flag has been provided.";
    raise(No_file)
  end
*)
let parse_args _ = 
  Arg.parse opts anon_fun usagemsg;
  postcheck ()

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
