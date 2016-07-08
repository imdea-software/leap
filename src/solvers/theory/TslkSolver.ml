
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



module type CUSTOM_TSLKSOLVER = sig
  module TslkExp : ExpressionTypes.TSLKEXP
 
  
  val check_sat_conj  : SolverOptions.t -> TslkExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : SolverOptions.t -> TslkExp.formula -> Sat.t
  
  val check_valid_dnf : SolverOptions.t -> TslkExp.formula -> Valid.t
  val check_valid_dnf_pus_info : SolverOptions.t -> TslkExp.formula -> (Valid.t * int)
    
  val check_sat : SolverOptions.t -> TslkExp.formula -> Sat.t
  val check_valid : SolverOptions.t -> TslkExp.formula -> Valid.t
  
  val check_valid_plus_info : SolverOptions.t -> TslkExp.formula -> (Valid.t * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model    : unit -> GenericModel.t

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TSLKSOLVER


module Make(K : Level.S) (Solver : BackendSolverIntf.BACKEND_TSLK) : S =
struct
  module TslkSol  = Solver.Translate.Tslk(K)
  module TslkExp  = TslkSol.Exp
  module VarIdSet = TslkExp.V.VarIdSet
  module GM       = GenericModel
  module F        = Formula
  module SolOpt   = SolverOptions

  let comp_model : bool ref = ref false

  let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
  
  (* 
   * is_var 
   *)
  let is_var_path = function
      TslkExp.VarPath(_) -> true
    | _               -> false
  and is_var_addr = function
      TslkExp.VarAddr(_) -> true
    | _               -> false
  and is_var_mem = function
      TslkExp.VarMem(_) -> true
    | _              -> false
  and is_var_level = function
      TslkExp.VarLevel(_) -> true
    | _              -> false
  and is_var_cell = function
      TslkExp.VarCell(_) -> true
    | _               -> false
  and is_var_elem = function
      TslkExp.VarElem(_) -> true
    | _               -> false
  and is_var_thid = function
      TslkExp.VarTh(_) -> true
    | _             -> false
  and is_var_set = function
      TslkExp.VarSet(_) -> true
    | _              -> false
  and is_var_setth = function
      TslkExp.VarSetTh(_) -> true
    | _                -> false
  and is_var_setelem = function
      TslkExp.VarSetElem(_) -> true
    | _                    -> false
  
  let is_var_term = function
      TslkExp.VarT(_)     -> true
    | TslkExp.SetT(s)     -> is_var_set s
    | TslkExp.ElemT(e)    -> is_var_elem e
    | TslkExp.TidT(t)    -> is_var_thid t
    | TslkExp.AddrT(a)    -> is_var_addr a
    | TslkExp.CellT(c)    -> is_var_cell c
    | TslkExp.SetThT(st)  -> is_var_setth st
    | TslkExp.SetElemT(st)-> is_var_setelem st
    | TslkExp.PathT(p)    -> is_var_path p
    | TslkExp.MemT(m)     -> is_var_mem m
    | TslkExp.LevelT(l)   -> is_var_level l
    | TslkExp.VarUpdate _ -> false (* Check if fine *)
  
  (* 
   * is_constant 
   *)
  let is_constant_set = function
        TslkExp.EmptySet -> true
      | _             -> false
  and is_constant_setth = function
        TslkExp.EmptySetTh -> true
      | _               -> false
  and is_constant_setelem = function
        TslkExp.EmptySetElem -> true
      | _                   -> false
  and is_constant_elem _ = false
  and is_constant_thid _ = false
  and is_constant_addr =  function
        TslkExp.Null -> true
      | _         -> false
  and is_constant_cell = function
        TslkExp.Error -> true
      | _          -> false
  and is_constant_path = function
        TslkExp.Epsilon -> true
      | _            -> false
  and is_constant_mem  = function
        TslkExp.Emp -> true
      | _        -> false
  and is_constant_level = function
        TslkExp.LevelVal _ -> true
      | _        -> false
  
  let is_constant_term = function
        TslkExp.VarT(_)     -> false
      | TslkExp.SetT(s)     -> is_constant_set s
      | TslkExp.ElemT(e)    -> is_constant_elem e
      | TslkExp.TidT(th)   -> is_constant_thid th
      | TslkExp.AddrT(a)    -> is_constant_addr a
      | TslkExp.CellT(c)    -> is_constant_cell c
      | TslkExp.SetThT(st)  -> is_constant_setth st
      | TslkExp.SetElemT(st)-> is_constant_setelem st
      | TslkExp.PathT(p)    -> is_constant_path p
      | TslkExp.MemT(m)     -> is_constant_mem m
      | TslkExp.LevelT(l)   -> is_constant_level l
      | TslkExp.VarUpdate _ -> false
  
  (* 
   * is_flat
   *)
  
  let is_flat_set     s  = is_var_set     s  || is_constant_set     s
  and is_flat_setth   st = is_var_setth   st || is_constant_setth   st
  and is_flat_setelem se = is_var_setelem se || is_constant_setelem se
  and is_flat_elem    e  = is_var_elem    e  || is_constant_elem    e
  and is_flat_thid    th = is_var_thid    th || is_constant_thid    th
  and is_flat_addr    a  = is_var_addr    a  || is_constant_addr    a
  and is_flat_cell    c  = is_var_cell    c  || is_constant_cell    c
  and is_flat_mem     m  = is_var_mem     m  || is_constant_mem     m
  and is_flat_level   l  = is_var_level   l  || is_constant_level   l
  and is_flat_path    p  = is_var_path    p  || is_constant_path    p
  
  let is_flat_term t =
    match t with
        TslkExp.VarT   _    -> true
      | TslkExp.SetT   s    -> is_flat_set s
      | TslkExp.ElemT  e    -> is_flat_elem e
      | TslkExp.TidT  th   -> is_flat_thid th
      | TslkExp.AddrT  a    -> is_flat_addr a
      | TslkExp.CellT  c    -> is_flat_cell c
      | TslkExp.SetThT st   -> is_flat_setth st
      | TslkExp.SetElemT se -> is_flat_setelem se
      | TslkExp.PathT  p    -> is_flat_path p
      | TslkExp.MemT   m    -> is_flat_mem m
      | TslkExp.LevelT l    -> is_flat_level l
      | TslkExp.VarUpdate _ -> false
  
  
  let is_flat_literal lit =
    match lit with
      | TslkExp.Append(p1,p2,p3)      -> is_var_path p1 && is_var_path p2 &&
                                        is_var_path p3
      | TslkExp.Reach(m,a1,a2,l,p)    -> is_var_mem m && is_var_addr a1 &&
                                         is_var_addr a2 && is_var_level l &&
                                         is_var_path p
      | TslkExp.OrderList(m,a1,a2)    -> is_var_mem m && is_var_addr a1 &&
                                         is_var_addr a2
      | TslkExp.In (a,s)              -> is_var_addr a && is_var_set s
      | TslkExp.SubsetEq(s1,s2)       -> is_var_set s1 && is_var_set s2
      | TslkExp.InTh(t,st)            -> is_var_thid t && is_var_setth st
      | TslkExp.SubsetEqTh(st1,st2)   -> is_var_setth st1 && is_var_setth st2
      | TslkExp.InElem(e,se)          -> is_var_elem e && is_var_setelem se
      | TslkExp.SubsetEqElem(se1,se2) -> is_var_setelem se1 && is_var_setelem se2
      | TslkExp.Less(l1,l2)           -> is_var_level l1 && is_var_level l2
      | TslkExp.LessEq(l1,l2)         -> is_var_level l1 && is_var_level l2
      | TslkExp.Greater(l1,l2)        -> is_var_level l1 && is_var_level l2
      | TslkExp.GreaterEq(l1,l2)      -> is_var_level l1 && is_var_level l2
      | TslkExp.LessElem(e1,e2)       -> is_var_elem e1 && is_var_elem e2
      | TslkExp.GreaterElem(e1,e2)    -> is_var_elem e1 && is_var_elem e2
      | TslkExp.Eq((t1,t2))           -> is_var_term t1 && is_var_term t2
      | TslkExp.InEq((t1,t2))         -> is_var_term t1 && is_var_term t2
      | TslkExp.BoolVar _             -> true
      | TslkExp.PC _                  -> true
      | TslkExp.PCUpdate _            -> true
      | TslkExp.PCRange _             -> true
  
  let is_flat expr =
    List.for_all is_flat_literal expr
      
  
  (* INVOCATIONS TRANSFORMING TO DNF FIRST *)
  let check_sat_conj (opt:SolOpt.t) (phi : TslkExp.conjunctive_formula) : Sat.t =
    match phi with
        F.TrueConj   -> Sat.Sat
      | F.FalseConj  -> Sat.Unsat
      | F.Conj conjs -> begin
          TslkSol.set_prog_lines (SolOpt.lines opt);
          Solver.check_sat (TslkSol.literal_list (SolOpt.use_quantifiers opt) conjs)
        end
  
  let check_sat_dnf (opt:SolOpt.t) (phi:TslkExp.formula) : Sat.t =
    let dnf_phi = F.dnf phi in
    let check phi = Sat.is_sat (check_sat_conj opt phi) in
    if List.exists check dnf_phi then
      Sat.Sat
    else
      Sat.Unsat
  
  
  let check_valid_dnf (opt:SolOpt.t) (phi:TslkExp.formula) : Valid.t =
    let dnf_phi       = F.dnf (F.Not phi) in
    let is_unsat conj = Sat.is_unsat (check_sat_conj opt conj) in
    if List.for_all is_unsat dnf_phi then
      Valid.Valid
    else
      Valid.Invalid
  
  
  let check_valid_dnf_pus_info (opt:SolOpt.t) (phi:TslkExp.formula) : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid_dnf opt phi in
    (res, Solver.calls_count ())
  
  
  (* INVOCATIONS WITHOUT CONVERTING TO DNF *)
  let check_sat (opt:SolOpt.t) (phi : TslkExp.formula) : Sat.t =
    match phi with
    | F.Not(F.Implies(_,F.True)) -> (Solver.calls_force_incr(); Sat.Unsat)
    | F.Not (F.Implies(F.False, _)) -> (Solver.calls_force_incr(); Sat.Unsat)
    | F.Implies(F.False, _) -> (Solver.calls_force_incr(); Sat.Sat)
    | F.Implies(_, F.True) -> (Solver.calls_force_incr(); Sat.Sat)
    | _ -> begin
             TslkSol.set_prog_lines (SolOpt.lines opt);
             Solver.check_sat (TslkSol.formula (SolOpt.cutoff_strategy opt)
                                               cutoff_opt
                                               (SolOpt.use_quantifiers opt) phi)
           end
  
  let check_valid (opt:SolOpt.t) (phi:TslkExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat opt (F.Not phi))
  
  let check_valid_plus_info (opt:SolOpt.t) (phi:TslkExp.formula) : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid opt phi in
    (res, Solver.calls_count())


  let compute_model (b:bool) : unit =
    let _ = comp_model := b
    in
      Solver.compute_model b


  let model_to_str () : string =
    let query_sort_map = TslkSol.sort_map () in
    let model = Solver.get_model () in
    let sort_map = GM.sm_union query_sort_map (GM.get_aux_sort_map model) in
    let thid_str = GM.search_type_to_str model sort_map GM.tid_s in
    let int_str  = GM.search_type_to_str model sort_map GM.int_s in
    let addr_str = GM.search_type_to_str model sort_map GM.addr_s in
    let elem_str = GM.search_type_to_str model sort_map GM.elem_s in
    let cell_str = GM.search_type_to_str model sort_map GM.cell_s in
    let path_str = GM.search_type_to_str model sort_map GM.path_s in
    let level_str = GM.search_type_to_str model sort_map GM.level_s in
    (* Special description for sets *)
    let set_str = GM.search_sets_to_str model sort_map GM.set_s in
    let setth_str = GM.search_sets_to_str model sort_map GM.setth_s in
    let setelem_str = GM.search_sets_to_str model sort_map GM.setelem_s in
    (* Special description for sets *)
    let heap_str = GM.search_type_to_str model sort_map GM.heap_s
    in
      "\nThreads:\n" ^ thid_str ^
      "\nIntegers:\n" ^ int_str ^
      "\nAddresses:\n" ^ addr_str ^
      "\nElements:\n" ^ elem_str ^
      "\nCells:\n" ^ cell_str ^
      "\nPaths:\n" ^ path_str ^
      "\nLevels:\n" ^ level_str ^
      "\nSets:\n" ^ set_str ^
      "\nSets of tids:\n" ^ setth_str ^
      "\nSets of elements:\n" ^ setelem_str ^
      "\nHeap:\n" ^ heap_str

  let print_model () : unit =
    if !comp_model && (not (GM.is_empty_model (Solver.get_model()))) then
      print_endline (model_to_str())
    else
      ()


  let get_sort_map () : GenericModel.sort_map_t =
    TslkSol.sort_map ()


  let get_model () : GenericModel.t =
    Solver.get_model ()


  let set_forget_primed_mem (b:bool) : unit =
    Smp.set_forget_primed_mem cutoff_opt b


  let set_group_vars (b:bool) : unit =
    Smp.set_group_vars cutoff_opt b

end

let choose (solverIdent : string) (k : int) : (module S) =
  let m = try Hashtbl.find BackendSolvers.tslkTbl solverIdent
    with Not_found -> BackendSolvers.defaultTslk () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_TSLK) in
  let module K = struct let level = k end in
  (module Make(K)(Sol) : S)
