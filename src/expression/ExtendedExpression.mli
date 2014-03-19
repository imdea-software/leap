
type fol_mode_t =
  | PCOnly
  | VarsOnly
  | PCVars

type 'var fol_ops_t =
  {
    fol_pc : bool;
    fol_var : 'var -> 'var;
  }

module type S =
  sig
    type atom
    type formula = atom Formula.formula

    val plain : fol_mode_t -> formula -> formula
  end

(*
val plain : fol_mode_t -> 'atom Formula.formula -> 'atom Formula.formula
*)
