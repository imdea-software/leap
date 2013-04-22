(******************************************************************************)
(* @file LeapArgs.ml                                                          *)
(* Command Line Arguments for Leap                                            *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file
exception No_inv_folder
exception Unknown_tag of string

val input_file : string ref
val is_input_file : bool ref
val input_file_fd : Unix.file_descr ref
val verbose : bool ref
val showFlag : bool ref
val debugFlag : bool ref
val pinvSys : bool ref
val pinvPlusSys : bool ref
val useGraph : bool ref
val openExtSys : bool ref
val binvSys : bool ref
val spinvSys : bool ref
val vcgenFlag : bool ref
val vdFlag : bool ref
val pvdFlag : bool ref
val use_z3 : bool ref
val use_yices_plus_z3 : bool ref
val use_sat : bool ref
val expand_pres : bool ref
val count_abs : bool ref
val show_models : bool ref
val show_label_info : bool ref
val keep_primed_mem : bool ref
val group_vars : bool ref
val use_smt : bool ref
val dpType : DP.t ref
val coType : Smp.cutoff_strategy ref
val invCandidate : string ref
val vdFormula : string ref
val supInvariant : string ref
val invFolder : string ref
val iGraphFile : string ref
val focusPC : int list ref
val ignorePC : int list ref
val vdFile : string ref
val pvdFile : string ref
val outFile : string ref
val detailedOutFile : string ref
val num_threads : int ref
val assignopt : 'a ref -> bool ref -> 'a -> unit
val setdebug : unit -> unit
val inputInvFolder : string -> unit
val inputInvGraphFile : string -> unit
val inputInvariant : string -> unit
val inputFormula : string -> unit
val inputClosedSys : string -> unit
val inputVd : string -> unit
val inputPvd : string -> unit
(*val dp_opt_list : string list*)
val set_dp : string -> unit
val co_opt_list : string list
val set_co : string -> unit
val assigninputfile : string -> unit
val supportInvariant : string -> unit
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
