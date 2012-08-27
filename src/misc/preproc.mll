(******************************************************************************)
(* @file preproc.mll                                                          *)
(* Very simple preprocesor for Ocaml files                                    *)
(*                                                                            *)
(* @authors Julian Samborski-Forlese                                          *)
(* @version 0.1.0                                                             *)
(* @since 2011/07/14                                                          *)
(*                                                                            *)
(******************************************************************************)
{
open Lexing
open Format
  
exception EOF 

let line = ref 1
let filename = ref ""
let incLine() = incr line
}

let SPACE = [' ''\t''\r']

rule token = 
  parse eof             { raise EOF }
  | '\n'                { incLine(); printf "\n"; token lexbuf }
  | "__line__"          { print_int (!line); token lexbuf } 
  | "__file__"          { printf "\"%s\"" (!filename); token lexbuf }
  | "_DEBUG" SPACE+ '"' { print_string "LeapDebug.debug \"@[<hov 2>DEBUG:";
                          printf "%s:%i:@@ " (!filename) (!line); 
                          string lexbuf; print_string "@]@.\""; 
                          token lexbuf }
  | "__DEBUG" SPACE+ '"'{ printf "LeapDebug.debug \""; string lexbuf; 
                           printf "\""; token lexbuf }
  | "_DEBUG_FLUSH_"     { printf "LeapDebug.flush ()"; token lexbuf }
  | _ as c              { print_char c; token lexbuf }

and string =
  parse eof             { raise EOF }
  | '\n'                { incLine(); printf "\n"; string lexbuf }
  | '"'                 { () }
  | "\\\""              { print_string "\\\""; string lexbuf }
  | _ as c              { print_char c; string lexbuf }



{
let main(args) =
  let input = try open_in (args.(1)) with e -> raise e in
  let lexbuf = from_channel input in
  filename := args.(1);
  try token lexbuf with EOF -> ()
;;

let _ = main(Sys.argv)
}