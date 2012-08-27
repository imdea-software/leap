module type CUSTOM_NUMSOLVER = sig
  module Exp    : ExpressionTypes.EXPRESSION
  module NumExp : ExpressionTypes.NUMEXP
  
  (* Basic invocations *)
  val is_sat              : NumExp.formula -> bool
  val is_valid            : NumExp.formula -> bool
  
  
  (* Invocations with extra information *)
  val is_valid_plus_info  : NumExp.formula -> (bool * int)
  
  val is_sat_with_lines   : int -> NumExp.formula -> bool
  val is_valid_with_lines : int -> NumExp.formula -> bool
  
  val is_valid_with_lines_plus_info 
                          : int -> NumExp.formula -> (bool * int)
  
  
  (* Queries over numeric formulas *)
  val int_implies         : NumExp.formula -> NumExp.formula -> bool
  val int_equivalent      : NumExp.formula -> NumExp.formula -> bool
  val compare_int_formulas
                          : NumExp.formula -> NumExp.formula -> bool
  val compare_eq_int_formulas 
                          : NumExp.formula -> NumExp.formula -> bool
  
  
  (* Queries over formulas, with implicit conversion to numeric formulas *)
  val implies             : Exp.formula -> Exp.formula -> bool
  val equivalent          : Exp.formula -> Exp.formula -> bool
  val compare_formulas    : Exp.formula -> Exp.formula -> bool
  val compare_eq_formulas : Exp.formula -> Exp.formula -> bool
  
  
  (* Standard widening *)
  val standard_widening   : NumExp.formula -> NumExp.formula -> NumExp.formula
  
  val standard_widening_conj 
                          : NumExp.literal list -> NumExp.literal list 
                              -> NumExp.literal list
end

module type S = CUSTOM_NUMSOLVER
  with module Exp = Expression
  and  module NumExp = NumExpression

module Make(Solver : BackendSolverIntf.BACKEND_NUM) : S =
struct
  module Exp    = Expression
  module NumExp = Solver.Translate.Num.Exp

  (* INVOCATIONS *)
  let is_sat (phi : NumExp.formula) : bool =
    Solver.sat (Solver.Translate.Num.int_formula phi)
  
  
  let is_valid (phi : NumExp.formula) : bool =
    not (is_sat (NumExp.Not phi))
  
  
  let is_valid_plus_info (phi : NumExp.formula) : (bool * int) =
    let _ = Solver.reset_calls () in
    let res = is_valid phi in 
    (res, Solver.calls_count ())
  
  
  let is_sat_with_lines (prog_lines : int) (phi : NumExp.formula) : bool =
    let f = Solver.Translate.Num.int_formula_with_lines phi prog_lines in 
    Solver.sat f
  
  
  let is_valid_with_lines (prog_lines : int) (phi : NumExp.formula) : bool =
    not (is_sat_with_lines prog_lines (NumExp.Not phi))
  
  
  let is_valid_with_lines_plus_info (prog_lines : int) (phi : NumExp.formula) 
    : (bool * int) =
    Solver.reset_calls ();
    let res = is_valid_with_lines prog_lines phi
    in (res, Solver.calls_count ())
  
  
  let int_implies (ante : NumExp.formula) (conse : NumExp.formula) : bool =
      is_valid (NumExp.Implies(ante, conse))
  
  
  let int_equivalent (f1 : NumExp.formula) (f2 : NumExp.formula) : bool =
      is_valid (NumExp.Iff(f1, f2))
  
  
  let compare_int_formulas (pre:NumExp.formula) (post:NumExp.formula) : bool =
    int_implies post pre
  
  
  let compare_eq_int_formulas (f1:NumExp.formula) (f2:NumExp.formula) : bool =
    int_equivalent f1 f2
  
  
  (* Operations with conversion from formulas *)
  
  let implies (ante : Exp.formula) (conse : Exp.formula) : bool =
    let int_ante  = NumExp.formula_to_int_formula ante in
    let int_conse = NumExp.formula_to_int_formula conse 
    in int_implies int_ante int_conse
  
  
  let compare_formulas (pre:Exp.formula) (post:Exp.formula) : bool =
    implies post pre
  
  
  let equivalent (f1 : Exp.formula) (f2 : Exp.formula) : bool =
    let int_f1 = NumExp.formula_to_int_formula f1 in
    let int_f2 = NumExp.formula_to_int_formula f2 
    in int_equivalent int_f1 int_f2
  
  
  let compare_eq_formulas (f1 : Exp.formula) (f2 : Exp.formula) : bool =
    equivalent f1 f2
  
  
  (* Standard widening *)
  (*  
  let standard_widening (x : NumExp.formula) (y : NumExp.formula) 
    : NumExp.formula =
    let x_conj = NumExp.formula_to_conj_literals x in
    let vars_set = NumExp.VarSet.elements
      (NumExp.VarSet.union (NumExp.all_vars_set x) (NumExp.all_vars_set y)) in
    let var_str = Solver.int_varlist vars_set in
    let y_str    = Solver.formula y in
    let is_preserved c = let c_str = Solver.literal c in
      let query = Printf.sprintf "%s\n(assert+ (not (=> %s %s)))\n(check)\n" 
            var_str y_str c_str in
        Solver.unsat query
    in
      NumExp.list_literals_to_formula (List.filter is_preserved x_conj)
    *)
  let standard_widening 
        (x : NumExp.formula) (y : NumExp.formula) : NumExp.formula =
    let x_conj = NumExp.formula_to_conj_literals x in
    let vars_set = NumExp.VarSet.elements
      (NumExp.VarSet.union (NumExp.all_vars_set x) (NumExp.all_vars_set y)) in
    let is_preserved c = 
      Solver.unsat (Solver.Translate.Num.std_widening vars_set y c)
    in NumExp.list_literals_to_formula (List.filter is_preserved x_conj)
  
  let standard_widening_conj (x : NumExp.literal list) 
        (y : NumExp.literal list) : NumExp.literal list =
    let vars_set = NumExp.VarSet.elements
      (List.fold_left (fun s lit ->
          NumExp.VarSet.union s (NumExp.all_vars_set_literal lit)
        ) NumExp.VarSet.empty (x @ y)) in
    let y' = NumExp.list_literals_to_formula y in
    let is_preserved c = 
      Solver.unsat (Solver.Translate.Num.std_widening vars_set y' c)
    in List.filter is_preserved x
end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.numTbl solverIdent
    with Not_found -> BackendSolvers.defaultNum () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_NUM) in
  (module Make(Sol) : S)
