(* Type declaration *)

type var_table_t = (Expression.varId, Expression.var_info_t) Hashtbl.t


type proc_info_t

and proc_table_t = (string, proc_info_t) Hashtbl.t


type tran_table_t = (int, Expression.formula list) Hashtbl.t

type st_table_t = (Expression.pc_t, string * Statement.statement_t) Hashtbl.t

type label_table_t = (string, Expression.pc_t * Expression.pc_t) Hashtbl.t

type t


type sysMode =
  | SClosed of int
  | SOpenArray of Expression.tid list


type abstraction =
  | NoAbstraction
  | Counting


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
val empty_system    : t


(* SYSTEM MANIPULATION FUNCTIONS *)
val new_system : var_table_t ->
                 Statement.boolean option ->
                 proc_table_t ->
                 tran_table_t ->
                 int list ->
                 st_table_t ->
                 label_table_t ->
                 t

val get_global            : t -> var_table_t
val get_assume            : t -> Statement.boolean option
val get_procs             : t -> proc_table_t
val get_trans             : t -> tran_table_t
val get_fair              : t -> int list
val get_statements        : t -> st_table_t
val get_labels            : t -> label_table_t
val lines                 : t -> int
val is_proc               : t -> string -> bool
val get_proc_name_list    : t -> bool -> string list
val get_all_local_vars    : t -> (string * Expression.variable list) list
val get_proc_by_name      : t -> string -> proc_info_t
val get_input_by_name     : t -> string -> var_table_t
val get_local_by_name     : t -> string -> var_table_t
val get_accvars_by_name   : t -> string -> (var_table_t * var_table_t)
val get_accvars           : t -> (string * var_table_t * var_table_t) list
val get_all_vars_id       : t -> Expression.varId list
val get_sys_var_tables    : t ->
                            var_table_t * (string * var_table_t * var_table_t)list
val get_fLine_by_name     : t -> string -> Expression.pc_t
val get_lLine_by_name     : t -> string -> Expression.pc_t
val get_prog_by_name      : t -> string -> Statement.statement_t option
val get_statement_at      : t ->
                            Expression.pc_t ->
                            (string * Statement.statement_t)
val get_trans_num         : t -> int
val add_global_vars       : t -> var_table_t -> t
val del_global_var        : t -> Expression.varId -> t
val del_global_var_regexp : t -> Str.regexp -> t


(* SYSTEM QUERY FUNCTIONS *)
val get_accvars_by_name : t ->
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
              Expression.shared_or_local ->
              Expression.var_nature ->
              unit
val del_var : var_table_t -> Expression.varId -> var_table_t
val mem_var : var_table_t -> Expression.varId -> bool
val find_var_type : var_table_t -> Expression.varId -> Expression.sort
val find_var_expr : var_table_t ->
                    Expression.varId ->
                    Expression.initVal_t option
val find_var_tid : var_table_t -> Expression.varId -> Expression.shared_or_local
val find_var_kind : var_table_t -> Expression.varId -> Expression.var_nature
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
val gen_global_vars_as_terms : t -> Expression.TermSet.t
val gen_local_vars_as_terms : t ->
                              (string * Expression.TermSet.t) list
val gen_local_vars_as_array_terms : t ->
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


val check_is_numeric : t -> unit


(* PRINTING FUNCTIONS *)
val to_str : t -> string


(* TRANSITION RELATION FUNCTIONS *)
val gen_theta : sysMode -> t -> abstraction -> Expression.formula

val gen_rho : t ->
              sysMode ->
              Expression.pc_t ->
              abstraction ->
              bool ->
              Expression.tid ->
              Expression.formula list
