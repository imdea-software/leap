

module type S =
  sig
    type atom
    type formula = atom Formula.formula

    type sort
    type tid
    type v_info

    type tid_subst_t = (tid, tid) Hashtbl.t

    module V : Variable.S with type sort = sort with type info = v_info
    module ThreadSet : Set.S with type elt = tid

    (* Casting *)
    val cast : Expression.formula -> formula
    val cast_var : Expression.V.t -> V.t

    (* Basic Thread ID operations *)
    val tid_sort : sort
    val tid_var : V.t -> tid
    val no_tid : tid
    val tid_to_str : tid -> string
    val unprime_tid : tid -> tid

    (* Basic sort operations *)
    val sort_to_str : sort -> string

    (* Other basic operations *)
    val defInfo : unit -> v_info

    (* Thread substitution *)
    val new_tid_subst : (tid * tid) list -> tid_subst_t
    val new_comb_subst : ThreadSet.t -> ThreadSet.t -> tid_subst_t list
    val subst_to_str : tid_subst_t -> string
    val subst_tid : tid_subst_t -> formula -> formula
    val subst_domain : tid_subst_t -> ThreadSet.t
    val subst_codomain : tid_subst_t -> ThreadSet.t
    val subst_domain_in : ThreadSet.t -> tid_subst_t -> bool
    val subst_codomain_in : ThreadSet.t -> tid_subst_t -> bool

    (* Variable substitution *)
    val subst_vars : V.subst_t -> formula -> formula

    (* Expression operations *)
    val to_str : formula -> string
(*    val plain : fol_mode_t -> formula -> formula *)
    val voc : formula -> ThreadSet.t
    val prime_modified : formula -> formula -> formula
    val all_vars : formula -> V.VarSet.t
    val is_pc_var : V.t -> bool

    (* Expression constructors *)
    val ineq_tid : tid -> tid -> formula
    val pc_form : int -> V.shared_or_local -> bool -> formula
    val build_pc_var : bool -> V.shared_or_local -> V.t

    (* Vocabulary *)
    val voc_to_var : tid -> V.t
    val gen_fresh_tids : ThreadSet.t -> int -> ThreadSet.t
    val param : V.shared_or_local -> formula -> formula

    (* Matching *)
    val is_pc_update : formula -> (bool * int * tid)
    val is_var_update : formula -> (bool * V.t * tid)
    val is_int_val_assign : formula -> (bool * V.t * int)
    (* Should check VarT and (IntT VarInt) *)
    (* Poner un assert para asegurarme que el sort de las variables en IntVar el Int *)
    val integer_implies : (V.t * int) -> atom Formula.literal -> bool
    val integer_implies_neg : (V.t * int) -> atom Formula.literal -> bool
    (* By default these two functions return false *)


    (* Simplification *)
    val canonical : atom -> atom

  end
