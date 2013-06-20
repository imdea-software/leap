(******************************************************************************)
(* @file P2FArgs.mli                                                          *)
(* Command Line Arguments for Prog2FTS                                        *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file

val input_file : string ref
val is_input_file : bool ref
val input_file_fd : Unix.file_descr ref
val verbose : bool ref
val debugFlag : bool ref
val show_label_info : bool ref
val assignopt : 'a ref -> bool ref -> 'a -> unit
val assigninputfile : string -> unit
val opts : (string * Arg.spec * string) list
val anon_fun : string -> unit
val usagemsg : string
val error : Arg.usage_msg -> 'a
val simple_error : string -> 'a
val postcheck : unit -> unit
val parse_args : 'a -> unit
val open_input : 'a -> in_channel
val close_input : 'a -> unit
