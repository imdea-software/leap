(******************************************************************************)
(* @file SolveArgs.ml                                                         *)
(* Command Line Arguments for Solve                                           *)
(******************************************************************************)

open LeapLib

exception MoreThanOneInputFile
exception No_file

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let debugFlag       = ref false
let use_z3          = ref false
let coType          = ref Smp.Pruning (*Smp.Dnf*)
let hide_pres       = ref false
let phiFile         = ref ""
let dpType          = ref (DP.NoDP)
let use_quantifiers = ref false
let arrangement_gen = ref false

let assignopt (valref : 'a ref) (valbool : bool ref) (aval : 'a) : unit =
  valref := aval ; valbool := true

let setdebug () =
  LeapDebug.enable_debug();
  debugFlag := true

let inputFormula (s:string) = 
  phiFile := s


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
  [
    ("-dp",
        Arg.String set_dp,
        "indicates the DP to use. Options are: " ^
          String.concat "," (List.map DP.to_str DP.def_dp_list));
    ("-ag",
       Arg.Set arrangement_gen,
       " Enables the generation of satisfiable arrangements using SMT solvers.");
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
    ("--show_file_info",
        Arg.Set Debug._debug_show_tmpfile_info_,
        "shows path of temporary files");
    ("-q",
        Arg.Set use_quantifiers,
        "use quantifiers over finite domains when constructing SMT queries");
    ("--debug",
        Arg.Unit setdebug,
        "debug output information");
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
