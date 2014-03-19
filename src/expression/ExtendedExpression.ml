
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
let Make (V:Variable.S) : 

let plain (mode:fol_mode_t) (phi:'atom Formula.formula) : 'atom Formula.formula =
  let rec to_plain_var (v:V.t) : V.t =
    let plain_th = to_plain_shared_or_local
                      {fol_pc=true; fol_var=to_plain_var;} (V.parameter v) in
    let new_id = V.to_simple_str (V.set_param v plain_th) in
    build_var new_id (V.sort v) (V.is_primed v) V.Shared V.GlobalScope in
  let ops = match mode with
            | PCOnly -> {fol_pc=true; fol_var=id;}
            | VarsOnly -> {fol_pc=false; fol_var=to_plain_var;}
            | PCVars -> {fol_pc=true; fol_var=to_plain_var;} in
  F.formula_trans plain_fs ops phi
*)
