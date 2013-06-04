(******************************************************************************)
(* @file TslArgs.ml                                                           *)
(* Command Line Arguments for Tsl                                             *)
(******************************************************************************)

open LeapLib

exception MoreThanOneInputFile
exception No_file

let input_file    = ref ""
let is_input_file = ref false
let input_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose       = ref false
let debugFlag     = ref false
let use_z3        = ref false
let coType        = ref Smp.Union (*Smp.Dnf*)
let hide_pres     = ref false
let phiFile       = ref ""
(*let postTactics   = ref [] *)

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

(*
let parse_tac_list (s:string) : Tactics.post_tac_t list =
  let regexp = Str.regexp "," in
  let split = Str.split regexp s in
  try List.map Tactics.post_tac_from_string split
  with e -> Interface.Err.msg"Bad argument" $
      "List of tactics name expected as argument.";
      raise(e)
*)

let assigninputfile  (s:string) : unit = assignopt input_file is_input_file s

let opts =
  [ ("-v",
        Arg.Set verbose,
        "verbose");
    ("-z3",
        Arg.Set use_z3,
        "uses z3 as smt solver");
    ("-co",
        Arg.Symbol (co_opt_list,set_co),
        "indicates the method used for computing the cut-off");
    ("-hp",
        Arg.Set hide_pres,
        "hides preservation relation in generated VCs");
    ("--show_file_info",
        Arg.Set Debug._debug_show_tmpfile_info_,
        "shows path of temporary files");
(*
    ("--tacs",
        Arg.String (fun s -> postTactics := (parse_tac_list s)),
        "tac_1,tac_2,...,tac_n post tactics to be applied");
*)
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
