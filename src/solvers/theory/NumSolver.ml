
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


open LeapLib

module type CUSTOM_NUMSOLVER = sig
  module Exp     : ExpressionTypes.EXPRESSION
  module NumExp  : ExpressionTypes.NUMEXP
  
  (* Basic invocations *)
  val check_sat              : NumExp.formula -> Sat.t
  val check_valid            : NumExp.formula -> Valid.t
  
  
  (* Invocations with extra information *)
  val check_valid_plus_info  : NumExp.formula -> (Valid.t * int)
  
  val check_sat_with_lines   : int -> NumExp.formula -> Sat.t
  val check_valid_with_lines : int -> NumExp.formula -> Valid.t
  
  val check_valid_with_lines_plus_info 
                          : int -> NumExp.formula -> (Valid.t * int)


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
  val get_sort_map  : unit -> GenericModel.sort_map_t
  val get_model     : unit -> GenericModel.t
 
  
end

module type S = CUSTOM_NUMSOLVER
  with module Exp = Expression
  and  module NumExp = NumExpression

module Make(Solver : BackendSolverIntf.BACKEND_NUM) : S =
struct
  module Exp    = Expression
  module NumExp = Solver.Translate.Num.Exp
  module GM     = GenericModel
    
  module Q = (val QueryManager.get_num_query Solver.identifier)
  module Trans = Solver.Translate.Num.Query(Q)

  (* Compute counter model for not valid formulas? *)
  let comp_model : bool ref = ref false

  (* INVOCATIONS *)
  let check_sat (phi : NumExp.formula) : Sat.t =
    Solver.check_sat (Trans.int_formula phi)
  
  
  let check_valid (phi : NumExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat (Formula.Not phi))
  
  
  let check_valid_plus_info (phi : NumExp.formula) : (Valid.t * int) =
    let _ = Solver.reset_calls () in
    let res = check_valid phi in 
    (res, Solver.calls_count ())
  
  
  let check_sat_with_lines (prog_lines : int) (phi : NumExp.formula) : Sat.t =
    let _ = Trans.set_prog_lines prog_lines in
    let f = Trans.int_formula_with_lines phi in
    Solver.check_sat f
  
  
  let check_valid_with_lines (prog_lines : int) (phi : NumExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat_with_lines prog_lines (Formula.Not phi))
  
  
  let check_valid_with_lines_plus_info (prog_lines : int) (phi : NumExp.formula) 
    : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid_with_lines prog_lines phi
    in (res, Solver.calls_count ())

  
  let int_implies (ante : NumExp.formula) (conse : NumExp.formula) : bool =
    Valid.is_valid (check_valid (Formula.Implies(ante, conse)))
  
  
  let int_equivalent (f1 : NumExp.formula) (f2 : NumExp.formula) : bool =
    Valid.is_valid (check_valid (Formula.Iff(f1, f2)))
  
  
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
  let standard_widening 
        (x : NumExp.formula) (y : NumExp.formula) : NumExp.formula =
    let x_conj = Formula.to_conj_literals x in
    let vars_set = NumExp.V.VarSet.elements
      (NumExp.V.VarSet.union (NumExp.all_vars_set x) (NumExp.all_vars_set y)) in
    let is_preserved c = Sat.is_unsat
                          (Solver.check_sat (Trans.std_widening vars_set y c))
    in Formula.conj_literals (List.filter is_preserved x_conj)
  
  let standard_widening_conj (x : NumExp.literal list) 
        (y : NumExp.literal list) : NumExp.literal list =
    let vars_set = NumExp.V.VarSet.elements
      (List.fold_left (fun s lit ->
          NumExp.V.VarSet.union s (NumExp.all_vars_set (Formula.Literal lit))
        ) NumExp.V.VarSet.empty (x @ y)) in
    let y' = Formula.conj_literals y in
    let is_preserved c = Sat.is_unsat
                           (Solver.check_sat (Trans.std_widening vars_set y' c))
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
    let query_sort_map = Trans.sort_map () in
    let model = Solver.get_model () in
    let sort_map = GM.sm_union query_sort_map (GM.get_aux_sort_map model) in
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
    if !comp_model && (not (GM.is_empty_model (Solver.get_model()))) then
      print_endline (model_to_str())
    else
      ()

  let get_sort_map () : GM.sort_map_t =
    Trans.sort_map ()

  let get_model () : GM.t =
    Solver.get_model()

end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.numTbl solverIdent
    with Not_found -> BackendSolvers.defaultNum () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_NUM) in
  (module Make(Sol) : S)


let try_sat (phi:Expression.formula) : Sat.t =
  let num_phi = NumInterface.formula_to_int_formula phi in
  let numSolv_id = BackendSolvers.Yices.identifier in
  let module NumSol = (val choose numSolv_id : S)
  in
    NumSol.check_sat num_phi
