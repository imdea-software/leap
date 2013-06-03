open LeapLib

module type CUSTOM_NUMSOLVER = sig
  module Exp     : ExpressionTypes.EXPRESSION
  module NumExp  : ExpressionTypes.NUMEXP
  
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


  (* Counter models management *)
  val compute_model : bool -> unit
  val model_to_str  : unit -> string
  val print_model   : unit -> unit
 
  
end

module type S = CUSTOM_NUMSOLVER
  with module Exp = Expression
  and  module NumExp = NumExpression

module Make(Solver : BackendSolverIntf.BACKEND_NUM) : S =
struct
  module Exp    = Expression
  module NumExp = Solver.Translate.Num.Exp
  module GM     = GenericModel

  (* Compute counter model for not valid formulas? *)
  let comp_model : bool ref = ref false

  (* INVOCATIONS *)
  let is_sat (phi : NumExp.formula) : bool =
    let module Q = (val QueryManager.get_num_query Solver.identifier) in
    let module Trans = Solver.Translate.Num.Query(Q) in
    Solver.sat (Trans.int_formula phi)
  
  
  let is_valid (phi : NumExp.formula) : bool =
    not (is_sat (NumExp.Not phi))
  
  
  let is_valid_plus_info (phi : NumExp.formula) : (bool * int) =
    let _ = Solver.reset_calls () in
    let res = is_valid phi in 
    (res, Solver.calls_count ())
  
  
  let is_sat_with_lines (prog_lines : int) (phi : NumExp.formula) : bool =
    let module Q = (val QueryManager.get_num_query Solver.identifier) in
    let module Trans = Solver.Translate.Num.Query(Q) in
    let _ = Trans.set_prog_lines prog_lines in
    let f = Trans.int_formula_with_lines phi in
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
    let int_ante  = NumInterface.formula_to_int_formula ante in
    let int_conse = NumInterface.formula_to_int_formula conse
    in int_implies int_ante int_conse
  
  
  let compare_formulas (pre:Exp.formula) (post:Exp.formula) : bool =
    implies post pre
  
  
  let equivalent (f1 : Exp.formula) (f2 : Exp.formula) : bool =
    let int_f1 = NumInterface.formula_to_int_formula f1 in
    let int_f2 = NumInterface.formula_to_int_formula f2
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
    let module Q = (val QueryManager.get_num_query Solver.identifier) in
    let module Trans = Solver.Translate.Num.Query(Q) in
    let is_preserved c = Solver.unsat (Trans.std_widening vars_set y c)
    in NumExp.list_literals_to_formula (List.filter is_preserved x_conj)
  
  let standard_widening_conj (x : NumExp.literal list) 
        (y : NumExp.literal list) : NumExp.literal list =
    let vars_set = NumExp.VarSet.elements
      (List.fold_left (fun s lit ->
          NumExp.VarSet.union s (NumExp.all_vars_set_literal lit)
        ) NumExp.VarSet.empty (x @ y)) in
    let y' = NumExp.list_literals_to_formula y in
    let module Q = (val QueryManager.get_num_query Solver.identifier) in
    let module Trans = Solver.Translate.Num.Query(Q) in
    let is_preserved c = Solver.unsat (Trans.std_widening vars_set y' c)
    in List.filter is_preserved x


  (* Counter model computation functions *)
  let search_type_to_str (model:GM.t) (sm:GM.sort_map_t) (s:GM.sort) : string =
    let xs = GM.sm_dom_of_type sm (GM.Const s) @
             GM.sm_dom_of_type sm (GM.Fun ([GM.tid_s],[s]))
    in
      GM.id_list_to_str model xs

  let search_sets_to_str (model:GM.t) (sm:GM.sort_map_t) (s:GM.sort) : string =
    let set_to_str (id:GM.id) : string =
      let elems = Hashtbl.fold (fun es b xs ->
                    match (es,b) with
                    | ([Some e], GM.Single "true") -> e :: xs
                    | ([None]  , GM.Single "true") -> "_" :: xs
                    | _                            -> xs
                  ) (GM.get_fun model id) [] in
      Printf.sprintf "%s = {%s}\n" id (String.concat "," elems) in
    let local_set_to_str (id:GM.id) : string =
      let locTbl = Hashtbl.create 10 in
      let _ = Hashtbl.iter (fun es b ->
                match es with
                | x::y::[] -> begin
                                try
                                  let zs = Hashtbl.find locTbl x in
                                  Hashtbl.replace locTbl x ((y,b)::zs)
                                with
                                  _ -> Hashtbl.add locTbl x [(y,b)]
                              end
                | _ -> ()
              ) (GM.get_fun model id) in
      Hashtbl.fold (fun t es str ->
        let elems = List.fold_left (fun xs elem ->
                      match elem with
                      | (Some e, GM.Single "true") -> e::xs
                      | (None  , GM.Single "true") -> "_"::xs
                      | _                          -> xs
                    ) [] es in
        str ^ (Printf.sprintf "%s[%s] = {%s}\n" id (Option.default "_" t)
                (String.concat "," elems))
      ) locTbl "" in
    let gSets = GM.sm_dom_of_type sm (GM.Const s) in
    let lSets = GM.sm_dom_of_type sm (GM.Fun ([GM.tid_s],[s])) in
      (List.fold_left (fun str s -> str ^ set_to_str s) "" gSets) ^
      (List.fold_left (fun str s -> str ^ local_set_to_str s) "" lSets)


  let compute_model (b:bool) : unit =
    let _ = comp_model := b
    in
      Solver.compute_model b


  let model_to_str () : string =
    let module Q = (val QueryManager.get_num_query Solver.identifier) in
    let module Trans = Solver.Translate.Num.Query(Q) in
    let sort_map = Trans.sort_map () in
    let model = Solver.get_model () in
    let thid_str = search_type_to_str model sort_map GM.tid_s in
    let pc_str   = search_type_to_str model sort_map GM.loc_s in
    let int_str  = search_type_to_str model sort_map GM.int_s in
    (* Special description for sets *)
    let set_str  = search_sets_to_str model sort_map GM.set_s
    in
      "\nThreads:\n" ^ thid_str ^
      "\nProgram counters:\n" ^ pc_str ^
      "\nIntegers:\n" ^ int_str ^
      "\nSets:\n" ^ set_str


  let print_model () : unit =
    if !comp_model then
      print_endline (model_to_str())
    else
      ()
end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.numTbl solverIdent
    with Not_found -> BackendSolvers.defaultNum () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_NUM) in
  (module Make(Sol) : S)
