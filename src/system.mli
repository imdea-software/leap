(* Type declaration *)

type var_table_t = (Expression.varId, Expression.var_info_t) Hashtbl.t


type proc_info_t

and proc_table_t = (string, proc_info_t) Hashtbl.t


type tran_table_t = (int, Expression.formula list) Hashtbl.t

type st_table_t = (Expression.pc_t, string * Statement.statement_t) Hashtbl.t

type label_table_t = (string, Expression.pc_t * Expression.pc_t) Hashtbl.t

type system_t


type sysMode =
    SClosed
  | SOpenArray of Expression.tid list


(* Exceptions *)
exception Duplicated_var of Expression.varId * Expression.sort * Expression.sort
exception Duplicated_procedure of string
exception Unknown_procedure of string
exception Undefined_variable of Expression.varId
exception Not_position of Expression.pc_t
exception Invalid_argument



(* Default configuration values *)
val initVarNum       : int
val initProcNum      : int
val initTranNum      : int
val initLabelNum     : int
val defMainProcedure : string
val heap_name        : string
val me_tid           : string
val me_tid_var       : Expression.variable
val me_tid_th        : Expression.tid


val empty_var_table : var_table_t
val empty_system    : system_t


(* SYSTEM MANIPULATION FUNCTIONS *)
val new_system : var_table_t ->
                 Statement.boolean option ->
                 proc_table_t ->
                 tran_table_t ->
                 int list ->
                 st_table_t ->
                 label_table_t ->
                 system_t

val get_global            : system_t -> var_table_t
val get_assume            : system_t -> Statement.boolean option
val get_procs             : system_t -> proc_table_t
val get_trans             : system_t -> tran_table_t
val get_fair              : system_t -> int list
val get_threads           : system_t -> int
val get_statements        : system_t -> st_table_t
val get_labels            : system_t -> label_table_t
val set_threads           : system_t -> int -> system_t
val is_proc               : system_t -> string -> bool
val get_proc_name_list    : system_t -> bool -> string list
val get_all_local_vars    : system_t -> (string * Expression.variable list) list
val get_proc_by_name      : system_t -> string -> proc_info_t
val get_input_by_name     : system_t -> string -> var_table_t
val get_local_by_name     : system_t -> string -> var_table_t
val get_accvars_by_name   : system_t -> string -> (var_table_t * var_table_t)
val get_accvars           : system_t -> (string * var_table_t * var_table_t) list
val get_all_vars_id       : system_t -> Expression.varId list
val gen_all_vars_as_terms : system_t -> Expression.term list
val gen_all_vars_as_array_terms : system_t -> Expression.term list
val get_sys_var_tables    : system_t ->
                            var_table_t * (string * var_table_t * var_table_t)list
val get_fLine_by_name     : system_t -> string -> Expression.pc_t
val get_lLine_by_name     : system_t -> string -> Expression.pc_t
val get_prog_by_name      : system_t -> string -> Statement.statement_t option
val get_statement_at      : system_t ->
                            Expression.pc_t ->
                            (string * Statement.statement_t)
val get_trans_num         : system_t -> int
val add_global_vars       : system_t -> var_table_t -> system_t
val del_global_var        : system_t -> Expression.varId -> system_t
val del_global_var_regexp : system_t -> Str.regexp -> system_t


(* SYSTEM QUERY FUNCTIONS *)
val get_accvars_by_name : system_t ->
                          string ->
                          (var_table_t * var_table_t)


(* TABLE OF VARIABLES FUNCTIONS *)
val new_var_table : var_table_t
val copy_var_table : var_table_t -> var_table_t
(* Copies all elements from the second one to the first one, using replace *)
val join_var_table : var_table_t -> var_table_t -> unit
val add_var : var_table_t ->
              Expression.varId ->
              Expression.sort ->
              Expression.initVal_t option ->
              Expression.tid option ->
              Expression.kind_t ->
              unit
val del_var : var_table_t -> Expression.varId -> var_table_t
val mem_var : var_table_t -> Expression.varId -> bool
val find_var_type : var_table_t -> Expression.varId -> Expression.sort
val find_var_expr : var_table_t ->
                    Expression.varId ->
                    Expression.initVal_t option
val find_var_tid : var_table_t -> Expression.varId -> Expression.tid option
val find_var_kind : var_table_t -> Expression.varId -> Expression.kind_t
val get_var_id_list : var_table_t -> Expression.varId list
val get_variable_list : var_table_t -> Expression.variable list
val get_var_list : var_table_t -> string option -> Expression.variable list
val clear_table : var_table_t -> unit
val filter_table : var_table_t ->  Expression.varId list -> unit
val num_of_vars : var_table_t -> int
val undeftids_in_formula_decl : Expression.varId list -> var_table_t -> unit 


(* LABEL TABLE FUNCTIONS *)
val new_label_table : label_table_t
val copy_label_table : label_table_t -> label_table_t
val add_single_label : label_table_t -> string -> Expression.pc_t -> unit
val add_open_label : label_table_t -> string -> Expression.pc_t -> unit
val add_close_label : label_table_t -> string -> Expression.pc_t -> unit
val get_label_pos : label_table_t -> string -> (Expression.pc_t * Expression.pc_t) option
val get_labels_list : label_table_t -> string list
val get_labels_for_pos : label_table_t -> Expression.pc_t -> string list


(* GENERATION FUNCTIONS *)
val gen_global_vars_as_terms : system_t -> Expression.TermSet.t
val gen_local_vars_as_terms : system_t ->
                              (string * Expression.TermSet.t) list
val gen_local_vars_as_array_terms : system_t ->
                                    (string * Expression.TermSet.t) list


(* SYSTEM EXTRA FUNCTIONS *)
val get_sort_from_variable : var_table_t ->
                             var_table_t ->
                             var_table_t ->
                             var_table_t ->
                             Expression.varId ->
                             Expression.sort
val get_sort_from_term : var_table_t ->
                         var_table_t ->
                         var_table_t ->
                         var_table_t ->
                         Expression.term ->
                         Expression.sort


(* PROCEDURE TABLE FUNCTIONS *)
val new_proc_table_from_list : (string * proc_info_t) list -> proc_table_t
val proc_table_vars_to_str : proc_table_t -> string


(* PROCEDURE INFORMATION FUNCTIONS *)
val new_proc_info : Expression.sort option ->
                    var_table_t ->
                    var_table_t ->
                    (Expression.varId * Expression.sort) list ->
                    Expression.pc_t ->
                    Expression.pc_t ->
                    Statement.statement_t option ->
                    proc_info_t
val proc_info_get_sort : proc_info_t -> Expression.sort option
val proc_info_get_input : proc_info_t -> var_table_t
val proc_info_get_local : proc_info_t -> var_table_t
val proc_info_get_args : proc_info_t -> (Expression.varId * Expression.sort) list
val proc_info_get_args_sig : proc_info_t -> Expression.sort list
val proc_init_line : proc_info_t -> Expression.pc_t
val proc_last_line : proc_info_t -> Expression.pc_t


(* TRANSITION TABLE FUNCTIONS *)
val new_tran_table : tran_table_t
val add_trans : tran_table_t ->
                Expression.pc_t ->
                Expression.formula list ->
                unit
val get_tran : tran_table_t -> Expression.pc_t -> Expression.formula list
val tran_table_to_str : tran_table_t -> string


val check_is_numeric : system_t -> unit


(* PRINTING FUNCTIONS *)
val system_to_str : system_t -> string
