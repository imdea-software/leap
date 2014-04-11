module type S =
  sig
    type t

    type id = string
    type sort
    type info
    type shared_or_local = Shared | Local of t
    type procedure_name  = GlobalScope | Scope of string

    type fresh_var_gen_t
    type subst_t

    module VarIdSet : Set.S with type elt = id
    module VarSet : Set.S with type elt = t

    (**********************)
    (**   Constructors   **)
    (**********************)

    val build : ?fresh:bool ->
                id ->
                sort ->
                bool ->
                shared_or_local ->
                procedure_name ->
                info ->
                t

    val build_global : id -> sort -> info -> t

    val dupp : t -> t



    (****************)
    (**   Getters  **)
    (****************)

    val id : t -> id
    val sort : t -> sort
    val is_primed : t -> bool
    val parameter : t-> shared_or_local
    val scope : t -> procedure_name
    val info : t -> info


    (****************)
    (**   Setters  **)
    (****************)

    val set_sort : t -> sort -> t
    val set_param : t -> shared_or_local -> t
    val set_info : t -> info -> t
    val unparam : t -> t



    (***********************)
    (**  Extra functions  **)
    (***********************)

    val same_var : t -> t -> bool
    val is_local : t -> bool
    val is_global : t -> bool
    val prime : t -> t
    val unprime : t -> t
    val prime_var_id : id -> id
    val is_fresh : t -> bool
    val localize : t -> t
    val localize_var_id : id -> string -> id
    val localize_var_id_with_procedure : id -> procedure_name -> id
    val localize_with_underscore : id -> procedure_name -> id


    (*********************************)
    (**  Fresh variable generators  **)
    (*********************************)

    val new_fresh_gen : VarIdSet.t -> fresh_var_gen_t
    val gen_fresh_var :(sort -> string) -> info -> fresh_var_gen_t -> sort -> t



    (*****************************)
    (**  Variable substitution  **)
    (*****************************)

    val new_subst : unit -> subst_t
    val add_subst : subst_t -> t -> t -> unit
    val subst : subst_t -> t -> t
    val subst_shared_or_local : subst_t -> shared_or_local -> shared_or_local


    (****************************)
    (**  Sets of variable ids  **)
    (****************************)

    val varidset_to_str : VarIdSet.t -> string
    val print_varidset : VarIdSet.t -> unit
    val varidset_from_list : id list -> VarIdSet.t


    (*****************************)
    (**  Lists of variable ids  **)
    (*****************************)

    val varidlist_to_str : id list -> string
    val print_varidlist : id list -> unit


    (***********************************)
    (**  Lists of typed variable ids  **)
    (***********************************)

    val typed_varidlist_to_str  : (sort -> string) -> (id * sort) list -> string
    val print_typed_varidlist : (sort -> string) -> (id * sort) list -> unit


    (*************************)
    (**  Sets of variables  **)
    (*************************)

    val typed_variable_set_to_str : (sort -> string) -> VarSet.t -> string
    val print_typed_variable_set : (sort -> string) -> VarSet.t -> unit
    val varset_of_sort : VarSet.t -> sort -> VarSet.t
    val split_by_sort : VarSet.t -> (sort, VarSet.t) Hashtbl.t
    val find_in_table_sort : (sort, VarSet.t) Hashtbl.t -> sort -> VarSet.t
    val varset_from_list : t list -> VarSet.t

    val varidlist_of_sort :t list -> sort -> id list


    (****************)
    (**  Printers  **)
    (****************)

    val shared_or_local_to_str : shared_or_local -> string
    val procedure_name_to_str : procedure_name -> string
    val to_str : t -> string
    val to_simple_str : t -> string
    val to_full_str : (sort -> string) -> (info -> string) -> t -> string
  end

module Make (VS : VarSpec.S) : S
  with type sort = VS.sort_t
  with type info = VS.info_t
