(****************)
(* ARGS         *)
(****************)

open Printf
open LeapLib
open Global

open Specparser
open Speclexer
open Debug

module Pars = Specparser
module Lex = Speclexer

module NumExp = NumExpression
module NumSolver = (val NumSolver.choose "default" : NumSolver.S)

exception File_not_found of string
exception ArgsError

let assignopt valref valbool aval = 
  valref := aval ; valbool := true

let inv_file = ref ""
let is_inv_file = ref false
let inv_file_fd    : Unix.file_descr ref = ref Unix.stdin

let spec_file = ref ""
let is_spec_file = ref false
let spec_file_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose            = ref false
let show_stat_info     = ref false

let assignopt s opt opt_flag = opt := s ; opt_flag := true
let assign_inv_file s = assignopt s inv_file is_inv_file
let assign_spec_file s = assignopt s spec_file is_spec_file
(* Program arguments *)

let set_debug i = Debug._debug_ := true;
                  Debug._debug_level_ := i

module MyArgs =
struct
  let myopts =
    [ ("-v", Arg.Set verbose,"verbose");
      ("--invs", Arg.String assign_inv_file, "file with invariants");
      ("--spec", Arg.String assign_spec_file, "file with spec");
      ("--show_stats", Arg.Set show_stat_info,"displays statistic information");
      ("--debug", Arg.Int set_debug, "debug level")
    ]

      
  let usagemsg = "Generates a transition system for numeric program."
    
  let error msg = Arg.usage myopts msg ; exit 0

  let anon_fun str = 
    let _ = error "Unrecognized arg: \"" ^ str ^ "\"\n" in
      ()
    
  let simple_error msg = Printf.printf "%s\n" msg ; exit 0
    
  let postcheck () = ()
    
end


let parse_args _ = Arg.parse MyArgs.myopts MyArgs.anon_fun MyArgs.usagemsg ;
                   MyArgs.postcheck ()




let open_files _ =
  if (not !is_inv_file) && (not !is_spec_file) then
    MyArgs.error "must specify invariants file and spec file."
  else if (not !is_inv_file) then
    MyArgs.error "must specify invariants file."
  else if (not !is_spec_file) then
    MyArgs.error "must specify invariants file."
  else
    let _ =  inv_file_fd := Unix.openfile !inv_file [Unix.O_RDONLY] 0 in
    let _ = spec_file_fd := Unix.openfile !spec_file [Unix.O_RDONLY] 0 in
    let inv_channel  = Unix.in_channel_of_descr !inv_file_fd in
    let spec_channel = Unix.in_channel_of_descr !spec_file_fd in
      (inv_channel , spec_channel)

let close_input _ =
  Unix.close !inv_file_fd ;
  Unix.close !spec_file_fd

let read_input_files _ =
  let (inv_ch,spec_ch) = open_files () in
  let invs  = Pars.invariant_list Lex.norm (Lexing.from_channel inv_ch) in
  let specs = Pars.specification  Lex.norm (Lexing.from_channel spec_ch) in
  let _    = close_input () in
    (invs,specs)


let forall f ls =
  List.fold_left (fun sofar x -> (f x) & sofar) true ls

let prove_one_spec invs  sCount a_spec =
  let (name, phi) = a_spec in
  let prove_at_one_location an_invariant = 
    let (loc, conj_inv) = an_invariant in
    let inv = NumExp.conj_literals_to_formula conj_inv in
    let is_valid = NumSolver.is_valid (NumExp.Implies(inv,phi)) in
      if not is_valid then begin
  Printf.eprintf "\"%s\" fails at location \"%s\".\n" name loc 
      end ;
      is_valid
  in
  let res =     forall prove_at_one_location invs in 
  if (res) then incr sCount;
  res

let prove_all_specs invs spec =
  let sCount = ref 0 in 
  let rVal = forall (prove_one_spec invs sCount) spec in 
  Printf.printf "Total specs: %d. Proved fully: %d \n" (List.length spec) (!sCount);
  rVal



(****************)
(* main         *)
(****************)

let _ =
  try
    let _    = parse_args () in
    let (invs,specs)  = read_input_files () in
    if (prove_all_specs invs specs) then
  Printf.printf "All Specs are proved.\n"
      else
  Printf.printf "Some specs unproved.\n"
  with
      e -> RAISE(e)
