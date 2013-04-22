(******************************************************************************)
(* @file PinvArgs.mli                                                         *)
(* Command Line Arguments for PInv                                            *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file

val input_file : string ref
val is_input_file : bool ref
val input_file_fd : Unix.file_descr ref
val verbose : bool ref
val pinvPlusSys : bool ref
val showFlag : bool ref
val debugFlag : bool ref
val use_z3 : bool ref
val expand_pres : bool ref
val count_abs : bool ref
val dpType : DP.t ref
val coType : Smp.cutoff_strategy_t ref
val invCandidate : string ref
val focusPC : int list ref
val ignorePC : int list ref
val outFile : string ref
val assignopt : 'a ref -> bool ref -> 'a -> unit
val inputInvariant : string -> unit
val set_dp : string -> unit
val co_opt_list : string list
val set_co : string -> unit
val assigninputfile : string -> unit
val focusPos : string -> unit
val ignorePos : string -> unit
val opts : (string * Arg.spec * string) list
val anon_fun : string -> unit
val usagemsg : string
val error : Arg.usage_msg -> 'a
val simple_error : string -> 'a
val postcheck : unit -> unit
val parse_args : 'a -> unit
val open_input : 'a -> in_channel
val close_input : 'a -> unit

