
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
open LeapVerbose

module type CUSTOM_TLLSOLVER = sig
  module TllExp : ExpressionTypes.TLLEXP
  
  val check_sat_conj  : SolverOptions.t -> TllExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : SolverOptions.t -> TllExp.formula -> Sat.t
  
  val check_valid_dnf : SolverOptions.t -> TllExp.formula -> Valid.t
  val check_valid_dnf_pus_info : SolverOptions.t -> TllExp.formula -> (Valid.t * int)
    
  val check_sat : SolverOptions.t -> TllExp.formula -> Sat.t
  val check_valid : SolverOptions.t -> TllExp.formula -> Valid.t
  
  val check_valid_plus_info : SolverOptions.t -> TllExp.formula -> (Valid.t * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model    : unit -> GenericModel.t

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TLLSOLVER
  with module TllExp = TLLExpression
  
module Make(Solver : BackendSolverIntf.BACKEND_TLL) : S =
struct
  module TllExp   = Solver.Translate.Tll.Exp
  module VarIdSet = TllExp.V.VarIdSet
  module GM       = GenericModel
  module SolOpt   = SolverOptions

  module Q = (val QueryManager.get_tll_query Solver.identifier)
  module Trans = Solver.Translate.Tll.Query(Q)

  let comp_model : bool ref = ref false

  let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
  
  (* 
   * is_var 
   *)
  let is_var_path = function
      TllExp.VarPath(_) -> true
    | _               -> false
  and is_var_addr = function
      TllExp.VarAddr(_) -> true
    | _               -> false
  and is_var_mem = function
      TllExp.VarMem(_) -> true
    | _              -> false
  and is_var_int = function
      TllExp.VarInt(_) -> true
    | _              -> false
  and is_var_mark = function
      TllExp.VarMark(_) -> true
    | _                 -> false
  and is_var_cell = function
      TllExp.VarCell(_) -> true
    | _               -> false
  and is_var_elem = function
      TllExp.VarElem(_) -> true
    | _               -> false
  and is_var_thid = function
      TllExp.VarTh(_) -> true
    | _             -> false
  and is_var_set = function
      TllExp.VarSet(_) -> true
    | _              -> false
  and is_var_setth = function
      TllExp.VarSetTh(_) -> true
    | _                -> false
  and is_var_setelem = function
      TllExp.VarSetElem(_) -> true
    | _                    -> false
  
  let is_var_term = function
      TllExp.VarT(_)     -> true
    | TllExp.SetT(s)     -> is_var_set s
    | TllExp.ElemT(e)    -> is_var_elem e
    | TllExp.TidT(t)     -> is_var_thid t
    | TllExp.AddrT(a)    -> is_var_addr a
    | TllExp.CellT(c)    -> is_var_cell c
    | TllExp.SetThT(st)  -> is_var_setth st
    | TllExp.SetElemT(st)-> is_var_setelem st
    | TllExp.PathT(p)    -> is_var_path p
    | TllExp.MemT(m)     -> is_var_mem m
    | TllExp.IntT(i)     -> is_var_int i
    | TllExp.MarkT(m)    -> is_var_mark m
    | TllExp.VarUpdate _ -> false (* Check this case. *)
  
  (* 
   * is_constant 
   *)
  let is_constant_set = function
        TllExp.EmptySet -> true
      | _             -> false
  and is_constant_setth = function
        TllExp.EmptySetTh -> true
      | _               -> false
  and is_constant_setelem = function
        TllExp.EmptySetElem -> true
      | _                   -> false
  and is_constant_elem = function
        TllExp.LowestElem  -> true
      | TllExp.HighestElem -> true
      | _                  -> false
  and is_constant_thid = function
        TllExp.NoTid -> true
      | _             -> false
  and is_constant_addr =  function
        TllExp.Null -> true
      | _         -> false
  and is_constant_cell = function
        TllExp.Error -> true
      | _          -> false
  and is_constant_path = function
        TllExp.Epsilon -> true
      | _            -> false
  and is_constant_mem  = function
        TllExp.Emp -> true
      | _        -> false
  and is_constant_int  = function
        TllExp.IntVal _ -> true
      | _        -> false
  and is_constant_mark  = function
        TllExp.MarkTrue -> true
      | TllExp.MarkFalse -> true
      | _        -> false
  
  let is_constant_term = function
        TllExp.VarT(_)     -> false
      | TllExp.SetT(s)     -> is_constant_set s
      | TllExp.ElemT(e)    -> is_constant_elem e
      | TllExp.TidT(th)    -> is_constant_thid th
      | TllExp.AddrT(a)    -> is_constant_addr a
      | TllExp.CellT(c)    -> is_constant_cell c
      | TllExp.SetThT(st)  -> is_constant_setth st
      | TllExp.SetElemT(st)-> is_constant_setelem st
      | TllExp.PathT(p)    -> is_constant_path p
      | TllExp.MemT(m)     -> is_constant_mem m
      | TllExp.IntT(i)     -> is_constant_int i
      | TllExp.MarkT(m)    -> is_constant_mark m
      | TllExp.VarUpdate _ -> false
  
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
  and is_flat_int     i  = is_var_int     i  || is_constant_int     i
  and is_flat_mark    m  = is_var_mark    m  || is_constant_mark    m
  and is_flat_path    p  = is_var_path    p  || is_constant_path    p
  
  let is_flat_term t =
    match t with
        TllExp.VarT   _    -> true
      | TllExp.SetT   s    -> is_flat_set s
      | TllExp.ElemT  e    -> is_flat_elem e
      | TllExp.TidT  th   -> is_flat_thid th
      | TllExp.AddrT  a    -> is_flat_addr a
      | TllExp.CellT  c    -> is_flat_cell c
      | TllExp.SetThT st   -> is_flat_setth st
      | TllExp.SetElemT se -> is_flat_setelem se
      | TllExp.PathT  p    -> is_flat_path p
      | TllExp.MemT   m    -> is_flat_mem m
      | TllExp.IntT   i    -> is_flat_int i
      | TllExp.MarkT  m    -> is_flat_mark m
      | TllExp.VarUpdate _ -> false
  
  
  let is_flat_literal lit =
    match lit with
      | TllExp.Append(p1,p2,p3)      -> is_var_path p1 && is_var_path p2 &&
                                        is_var_path p3
      | TllExp.Reach(m,a1,a2,p)      -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2 && is_var_path p
      | TllExp.OrderList(m,a1,a2)    -> is_var_mem m && is_var_addr a1 &&
                                        is_var_addr a2
      | TllExp.In (a,s)              -> is_var_addr a && is_var_set s
      | TllExp.SubsetEq(s1,s2)       -> is_var_set s1 && is_var_set s2
      | TllExp.InTh(t,st)            -> is_var_thid t && is_var_setth st
      | TllExp.SubsetEqTh(st1,st2)   -> is_var_setth st1 && is_var_setth st2
      | TllExp.InElem(e,se)          -> is_var_elem e && is_var_setelem se
      | TllExp.SubsetEqElem(se1,se2) -> is_var_setelem se1 && is_var_setelem se2
      | TllExp.Less(i1,i2)           -> is_var_int i1 && is_var_int i2
      | TllExp.LessEq(i1,i2)         -> is_var_int i1 && is_var_int i2
      | TllExp.Greater(i1,i2)        -> is_var_int i1 && is_var_int i2
      | TllExp.GreaterEq(i1,i2)      -> is_var_int i1 && is_var_int i2
      | TllExp.LessElem(e1,e2)       -> is_var_elem e1 && is_var_elem e2
      | TllExp.GreaterElem(e1,e2)    -> is_var_elem e1 && is_var_elem e2
      | TllExp.Eq((t1,t2))           -> is_var_term t1 && is_var_term t2
      | TllExp.InEq((t1,t2))         -> is_var_term t1 && is_var_term t2
      | TllExp.BoolVar _             -> true
      | TllExp.PC _                  -> true
      | TllExp.PCUpdate _            -> true
      | TllExp.PCRange _             -> true
  
  let is_flat expr =
    List.for_all is_flat_literal expr
      
  
  (* INVOCATIONS TRANSFORMING TO DNF FIRST *)
  let check_sat_conj (opt:SolOpt.t) (phi : TllExp.conjunctive_formula) : Sat.t =
    match phi with
      | Formula.TrueConj   -> Sat.Sat
      | Formula.FalseConj  -> Sat.Unsat
      | Formula.Conj conjs ->
        begin
          Trans.set_prog_lines (SolOpt.lines opt);
          Solver.check_sat(Trans.literal_list (SolOpt.use_quantifiers opt) conjs)
        end
  
  let check_sat_dnf (opt:SolOpt.t) (phi : TllExp.formula) : Sat.t =
    let dnf_phi = Formula.dnf phi in
    let check phi = Sat.is_sat (check_sat_conj opt phi) in
    if List.exists check dnf_phi then
      Sat.Sat
    else
      Sat.Unsat
  
  
  let check_valid_dnf (opt:SolOpt.t) (phi : TllExp.formula) : Valid.t =
    let dnf_phi       = Formula.dnf (Formula.Not phi) in
    let is_unsat conj = Sat.is_unsat (check_sat_conj opt conj) in
    if (List.for_all is_unsat dnf_phi) then
      Valid.Valid
    else
      Valid.Invalid

   
  let check_valid_dnf_pus_info (opt:SolOpt.t) (phi:TllExp.formula) : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid_dnf opt phi in
    (res, Solver.calls_count ())


  (* INVOCATIONS WITHOUT CONVERTING TO DNF *)
  let check_sat (opt:SolOpt.t) (phi : TllExp.formula) : Sat.t =
    match phi with
    | Formula.Not(Formula.Implies(_,Formula.True)) ->
        (Solver.calls_force_incr(); Sat.Unsat)
    | Formula.Not (Formula.Implies(Formula.False, _)) ->
        (Solver.calls_force_incr(); Sat.Unsat)
    | Formula.Implies(Formula.False, _) ->
        (Solver.calls_force_incr(); Sat.Sat)
    | Formula.Implies(_, Formula.True) ->
        (Solver.calls_force_incr(); Sat.Sat)
    | _ -> begin
             verbl _LONG_INFO "**** TLL Solver, about to translate TLL...\n";
             Trans.set_prog_lines (SolOpt.lines opt);
             Solver.check_sat (Trans.formula (SolOpt.cutoff_strategy opt)
                                             cutoff_opt
                                             (SolOpt.use_quantifiers opt)
                                             phi)
           end
  
  let check_valid (opt:SolOpt.t) (phi:TllExp.formula) : Valid.t =
    Response.sat_to_valid (check_sat opt (Formula.Not phi))
  
  let check_valid_plus_info (opt:SolOpt.t) (phi:TllExp.formula) : (Valid.t * int) =
    Solver.reset_calls ();
    let res = check_valid opt phi in
    (res, Solver.calls_count())


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
    let int_str  = search_type_to_str model sort_map GM.int_s in
    let addr_str = search_type_to_str model sort_map GM.addr_s in
    let elem_str = search_type_to_str model sort_map GM.elem_s in
    let cell_str = search_type_to_str model sort_map GM.cell_s in
    let path_str = search_type_to_str model sort_map GM.path_s in
    (* Special description for sets *)
    let set_str = search_sets_to_str model sort_map GM.set_s in
    let setth_str = search_sets_to_str model sort_map GM.setth_s in
    let setelem_str = search_sets_to_str model sort_map GM.setelem_s in
    (* Special description for sets *)
    let heap_str = search_type_to_str model sort_map GM.heap_s
    in
      "\nThreads:\n" ^ thid_str ^
      "\nIntegers:\n" ^ int_str ^
      "\nAddresses:\n" ^ addr_str ^
      "\nElements:\n" ^ elem_str ^
      "\nCells:\n" ^ cell_str ^
      "\nPaths:\n" ^ path_str ^
      "\nSets:\n" ^ set_str ^
      "\nSets of tids:\n" ^ setth_str ^
      "\nSets of elements:\n" ^ setelem_str ^
      "\nHeap:\n" ^ heap_str

  let print_model () : unit =
    if !comp_model && (not (GM.is_empty_model (Solver.get_model()))) then
      print_endline (model_to_str())
    else
      ()

  let get_sort_map () : GM.sort_map_t =
    Trans.sort_map ()


  let get_model () : GM.t =
    Solver.get_model()


  let set_forget_primed_mem (b:bool) : unit =
    Smp.set_forget_primed_mem cutoff_opt b


  let set_group_vars (b:bool) : unit =
    Smp.set_group_vars cutoff_opt b

end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.tllTbl solverIdent
    with Not_found -> BackendSolvers.defaultTll () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_TLL) in
  (module Make(Sol) : S)
