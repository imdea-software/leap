
val choose : string -> unit
(** [choose s] selects [s] as the DP implementation to be used *)


val is_sat       : int ->
                   Tactics.solve_tactic option ->
                   Smp.cutoff_strategy_t ->
                   TSLExpression.formula -> bool
(** [is_sat lines stac co phi] checks the satisfiability of formula [phi],
    assuming the program contains [lines] lines, using tactics [stac] and
    cutoff strategy [co]. It returns true if the formula is satisfiable,
    otherwise false. *)


val is_valid     : int ->
                   Tactics.solve_tactic option ->
                   Smp.cutoff_strategy_t ->
                   TSLExpression.formula -> bool
(** [is_valid lines stac co phi] checks the validity of formula [phi], assuming
    the program contains [lines] lines, using tactics [stac] and cutoff
    strategy [co]. It returns true if the formula is valid, otherwise false. *)

  
val is_sat_plus_info : int ->
                       Tactics.solve_tactic option ->
                       Smp.cutoff_strategy_t ->
                       TSLExpression.formula -> (bool * int * int)
(** [is_sat_plus_info lines stac co phi] checks the satisfiability of formula
    [phi], assuming the program contains [lines] lines, using tactics [stac]
    and cutoff strategy [co]. It returns three values. The first value
    indicates whether the formula is satisfiable. The second value is the
    number of calls made to the TSL DP (generally 1) and the third argument
    is the number of calls made to a TSLK DP, which aids the TSL DP. *)


val is_valid_plus_info : int ->
                         Tactics.solve_tactic option ->
                         Smp.cutoff_strategy_t ->
                         TSLExpression.formula -> (bool * int * int)
(** [is_valid lines stac co phi] checks the validity of formula [phi], assuming
    the program contains [lines] lines, using tactics [stac] and cutoff
    strategy [co]. It returns three values. The first value indicates whether the
    formula is satisfiable. The second value is the number of calls made to
    the TSL DP (generally 1) and the third argument is the number of calls
    made to a TSLK DP, which aids the TSL DP. *)


val compute_model: bool -> unit
(** [compute_model b] enables or disables the computation of a model in
    case a counter example is found *)

val model_to_str : unit -> string
(** [model_to_str ()] returns a string representing the model of the counter
    example found in the last call to the DP *)


val print_model  : unit -> unit
(** [print_model ()] prints in the standard output the result of
    [model_to_str ()] *)


val set_forget_primed_mem : bool -> unit
(** [set_forget_primed_mem b] indicates whether primed memory variables should
    be taken or not in consideration when computing the SMP *)


val set_group_vars : bool -> unit
(** [set_group_vars b] indicates whether variables should be group in
    equivalence classes according to the information retrieved from the
    formula, in order to reduce the domain space when computing the SMP *)
