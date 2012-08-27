(******************************************************************************)
(* @file TllArgs.mli                                                          *)
(* Command Line Arguments for Tll                                             *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file

val input_file : string ref
val is_input_file : bool ref
val input_file_fd : Unix.file_descr ref
val debugFlag : bool ref
val use_z3 : bool ref
val coType : VCGen.cutoff_type ref
val hide_pres : bool ref
val phiFile : string ref
val assignopt : 'a ref -> bool ref -> 'a -> unit
val setdebug : unit -> unit
val inputFormula : string -> unit
val co_opt_list : string list
val set_co : string -> unit
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
