val _debug_ : bool ref
val _debug_level_ : int ref
val _debug_show_tmpfile_info_ : bool ref
val _debug_show_problems_ : bool ref
val _debug_show_invTables_ : bool ref
val _debug_show_widening_formula_ : bool ref
val _debug_show_smt_ : bool ref


val msg : string -> int -> unit
val print_file_name : string -> string -> unit
val force_print_file_name : string -> string -> unit
val print_smt_result : Sat.t -> unit
val print_trsProblem : string -> unit
val print_invTables : string -> string -> unit
val print_widening_formulas : int list -> string -> string -> string -> unit
val print_smt : string -> unit
val print_smt_query : string -> unit

val infoMsg : string -> unit
