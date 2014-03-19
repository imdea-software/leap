module type Toolkit =
  sig
    val defInfo : 'info
    val plain_formula : 'var ExtendedExpression.fol_ops_t ->
                        'atom Formula.formula ->
                        'atom Formula.formula
  end

module type S =
  sig
    val plain : ExtendedExpression.fol_mode_t -> 'atom Formula.formula -> 'atom Formula.formula
  end

module Make (V:Variable.S)
            (TK:Toolkit) : S =
  struct
    module EE = ExtendedExpression
    module F = Formula

    let to_plain_shared_or_local (ops:V.t EE.fol_ops_t)
                                 (th:V.shared_or_local) : V.shared_or_local =
      match th with
      | V.Shared  -> V.Shared
      | V.Local t -> V.Local (ops.EE.fol_var t)


    let rec to_plain_var (v:V.t) : V.t =
      let plain_th = to_plain_shared_or_local
                        {EE.fol_pc=true; EE.fol_var=to_plain_var;} (V.parameter v) in
      let new_id = V.to_simple_str (V.set_param v plain_th) in
      V.build new_id (V.sort v) (V.is_primed v) V.Shared V.GlobalScope TK.defInfo


    let plain (mode:ExtendedExpression.fol_mode_t)
              (phi:'atom Formula.formula) : 'atom Formula.formula =
      let rec to_plain_var (v:V.t) : V.t =
        let plain_th = to_plain_shared_or_local
                          {EE.fol_pc=true; EE.fol_var=to_plain_var;} (V.parameter v) in
        let new_id = V.to_simple_str (V.set_param v plain_th) in
        V.build new_id (V.sort v) (V.is_primed v) V.Shared V.GlobalScope TK.defInfo in
      let ops = match mode with
                | EE.PCOnly -> {EE.fol_pc=true; EE.fol_var=LeapLib.id;}
                | EE.VarsOnly -> {EE.fol_pc=false; EE.fol_var=to_plain_var;}
                | EE.PCVars -> {EE.fol_pc=true; EE.fol_var=to_plain_var;} in
      TK.plain_formula ops phi
  end
