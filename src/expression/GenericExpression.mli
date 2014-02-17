module type S =
  sig
    type t

    type sort_t
(*    type var_info_t *)
    type tid_t

(*
    module V : Variable.S
      with type sort = sort_t
      with type info = var_info_t
*)
    module V : Variable.S
    module ThreadSet : Set.S

    (* Basic Thread ID operations *)
    val tid_sort : sort_t
    val tid_var : V.t -> tid_t
    val no_tid : tid_t

    (* Expression operations *)
    val to_str : t -> string
    val voc : t -> ThreadSet.t

    (* Expression constructors *)
    val ineq_tid : tid_t -> tid_t -> t
    val pc_form : int -> V.shared_or_local -> bool -> t

    (* Vocabulary *)
    val voc_to_var : tid_t -> V.t
    val gen_fresh_tids : ThreadSet.t -> int -> ThreadSet.t
    val param : V.shared_or_local -> t -> t


  end

