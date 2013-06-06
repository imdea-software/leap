(******************************************************************************)
(* @file ApplyTacArgs.mli                                                     *)
(* Command Line Arguments for ApplyTac                                        *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file

val input_file : string ref
val is_input_file : bool ref
val verbose : bool ref
val input_file_fd : Unix.file_descr ref
val debugFlag : bool ref
val use_z3 : bool ref
val coType : Smp.cutoff_strategy_t ref
val hide_pres : bool ref
val phiFile : string ref
val solve_tactic           : Tactics.solve_tactic option ref
val supp_tac_list          : Tactics.support_tactic list ref
val supp_split_tac_list    : Tactics.support_split_tactic list ref
val formula_tac_list       : Tactics.formula_tactic list ref
val formula_split_tac_list : Tactics.formula_split_tactic list ref
val support_files : string list ref
val outfile : string ref
(*val postTactics : (Tactics.post_tac_t list) ref *)
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

val is_vc_file : unit -> bool
