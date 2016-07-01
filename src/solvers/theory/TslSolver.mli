
val choose : string -> unit
(** [choose s] selects [s] as the decision procedure implementation to be
    used. *)


val check_sat    : int ->
                   Smp.cutoff_strategy_t ->
                   bool ->
                   TSLExpression.formula -> Sat.t
(** [check_sat lines co useq phi] checks the satisfiability of formula
    [phi], assuming the program contains [lines] lines, using tactics
    [stac] and cutoff strategy [co]. It returns [Sat] if the formula is
    satisfiable, otherwise [Unsat]. *)


val check_valid  : int ->
                   Smp.cutoff_strategy_t ->
                   bool ->
                   TSLExpression.formula -> Valid.t
(** [check_valid lines co useq phi] checks the validity of formula [phi],
    assuming the program contains [lines] lines, using tactics [stac] and
    cutoff strategy [co]. It returns [Valid] if the formula is valid,
    otherwise [Invalid]. *)

  
val check_sat_plus_info : int ->
                          Smp.cutoff_strategy_t ->
                          bool ->
                          TSLExpression.formula -> (Sat.t * int * DP.call_tbl_t)
(** [check_sat_plus_info lines co useq phi] checks the satisfiability of
    formula [phi], assuming the program contains [lines] lines, using
    tactics [stac] and cutoff strategy [co]. It returns three values. The
    first value indicates whether the formula is satisfiable. The second
    value is the number of calls made to the TSL decision procedure
    (generally 1) and the third argument is the number of calls made to a
    TSLK decision procedure, which aids the TSL decision procedure. *)


val check_valid_plus_info : int ->
                            Smp.cutoff_strategy_t ->
                            bool ->
                            TSLExpression.formula -> (Valid.t * int * DP.call_tbl_t)
(** [check_valid lines co useq phi] checks the validity of formula [phi],
    assuming the program contains [lines] lines, using tactics [stac] and
    cutoff strategy [co]. It returns three values. The first value
    indicates whether the formula is satisfiable. The second value is the
    number of calls made to the TSL decision procedure (generally 1) and
    the third argument is the number of calls made to a TSLK decision
    procedure, which aids the TSL decision procedure. *)


val compute_model: bool -> unit
(** [compute_model b] enables or disables the computation of a model in
    case a counter example is found. *)


val model_to_str : unit -> string
(** [model_to_str ()] returns a string representing the model of the
    counter example found in the last call to the decision procedure. *)


val print_model  : unit -> unit
(** [print_model ()] prints in the standard output the result of
    [model_to_str ()]. *)


val get_sort_map : unit -> GenericModel.sort_map_t
(** [get_sort_map ()] returns the map from identifiers to sorts computed
    in the last call of the decision procedure. *)


val get_model  : unit -> GenericModel.t
(** [get_model ()] returns the model computed at the last call to the
   decision procedure. *)


val set_forget_primed_mem : bool -> unit
(** [set_forget_primed_mem b] indicates whether primed memory variables
    should be taken or not in consideration when computing the SMP. *)


val set_group_vars : bool -> unit
(** [set_group_vars b] indicates whether variables should be group in
    equivalence classes according to the information retrieved from the
    formula, in order to reduce the domain space when computing the SMP. *)
