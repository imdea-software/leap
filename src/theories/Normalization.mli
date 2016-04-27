module type S =
  sig

    module V : Variable.S
    type t
    type term
    type formula

    val new_norm : formula -> t

    val add_term_map : t -> term -> V.t -> unit
    val remove_term_map : t -> term -> unit
    val find_term_map : t -> term -> V.t
    val gen_if_not_var : t -> (term -> bool) -> (term -> V.t) -> term -> V.sort -> V.t
    val term_map_size : t -> int
    val iter_term_map : (term -> V.t -> unit) -> t -> unit

    val add_proc_term_map : t -> term -> V.t -> unit
    val find_proc_term : t -> term -> V.t

    val gen_fresh_var : t -> V.sort -> V.t
    val to_str : t -> (term -> string) -> (V.t -> string) -> string

  end

module Make (Opt:NormSpec.S) : S
  with type term = Opt.norm_term
  with type formula = Opt.norm_formula
  with type V.t = Opt.VS.t
  with type V.sort = Opt.VS.sort
