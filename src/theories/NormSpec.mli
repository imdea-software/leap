module type S =
  sig

    module VS : Variable.S
    type norm_atom
    type norm_term
    type norm_formula

    val norm_varset : norm_formula -> VS.VarSet.t
    val norm_fresh_vinfo : unit -> VS.info
    val norm_fresh_vname : VS.sort -> string

  end
