module type S =
  sig
    type atom
    type formula = atom Formula.formula

    type sort
    type tid

(*
    module V : Variable.S
      with type sort = sort_t
      with type info = var_info_t
*)
    module V : Variable.S
    module ThreadSet : Set.S with type elt = tid

    (* Casting *)
    val cast : Expression.formula -> formula
    val cast_var : Expression.V.t -> V.t

    (* Basic Thread ID operations *)
    val tid_sort : sort
    val tid_var : V.t -> tid
    val no_tid : tid
    val tid_to_str : tid -> string

    (* Expression operations *)
    val to_str : formula -> string
    val voc : formula -> ThreadSet.t

    (* Expression constructors *)
    val ineq_tid : tid -> tid -> formula
    val pc_form : int -> V.shared_or_local -> bool -> formula

    (* Vocabulary *)
    val voc_to_var : tid -> V.t
    val gen_fresh_tids : ThreadSet.t -> int -> ThreadSet.t
    val param : V.shared_or_local -> formula -> formula

  end

