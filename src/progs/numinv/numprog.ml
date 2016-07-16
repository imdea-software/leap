
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


open Printf
open LeapLib
open TrsLexer
open Interface

module Expr = Expression
module Sys  = System
module Stm  = Statement
module NumExp = NumExpression

(* ALE: This code should be changed in the future *)
module PosSolver  = (val PosSolver.choose  "default" : PosSolver.S)
module TllSolver  = (val TllSolver.choose  "default" : TllSolver.S)
module TslkSolver = (val TslkSolver.choose "default" 1 : TslkSolver.S)
module NumSolver  = (val NumSolver.choose  "default" : NumSolver.S)
module VCG = VCGen.Make(PosSolver)(TllSolver)(TslkSolver)(NumSolver)
(* ALE: This code should be changed in the future *)

(* FOR DEBUG ONLY. OUTPUTS INTERMEDIATE INVARIANTS TO CHECK WITH SPECS *)
let tmpCounter = ref 0
(* FOR DEBUG ONLY. OUTPUTS INTERMEDIATE INVARIANTS TO CHECK WITH SPECS *)

type loc_t = int list

type vrnt_t = int

type guard_t = Expr.formula

type trans_rel_t = Expr.formula

type num_assign_t = Expr.varId * Expr.integer

type num_trans_info_t = loc_t * loc_t * guard_t * trans_rel_t * Expr.V.t list

type num_trans_prj_t = (int * int * int, Expr.formula * Expr.formula) Hashtbl.t

type num_trans_info_table_t = (int * int * int, num_trans_info_t) Hashtbl.t

type num_location_t = loc_t * guard_t

type num_trans_t = loc_t                         * (* from              *)
                   loc_t                         * (* to                *)
                   vrnt_t                        * (* variant           *)
                   int                           * (* subclass for \/   *)
                   (int * int * Expr.tid)        * (* tau from, to, tid *)
                   num_trans_info_t                (* information       *)

type tactic_t = Split | Focus

type absIntMode_t = Lazy | Interf | Eager | EagerPlus

type num_problem_info_t =
  {
    ths         : Expr.tid list   ; (* Materialized threads      *)
    tactic      : tactic_t option ; (* Split the problem?        *)
    visit_order : loc_t list      ; (* Location visiting order   *)
    init_loc    : loc_t           ; (* Initial location          *)
    updLocs     : bool            ; (* Updates location guards   *)
    absIntMode  : absIntMode_t    ; (* Abstract interpreter mode *)
  }

type inv_table_t = (loc_t, Expr.formula) Hashtbl.t


type num_problem_t =
  {         name  : string                 ; (* The problem name             *)
            vars  : Expr.V.t list          ; (* The problem variables        *)
    mutable locs  : num_location_t list    ; (* The location list            *)
            mats  : num_trans_t list       ; (* The main thread transitions  *)
    mutable self  : num_trans_t list       ; (* The spaghetti transitions    *)
            trans : num_trans_info_table_t ; (* Orig. transition information *)
    mutable invs  : inv_table_t            ; (* Last generated invariants    *)
            info  : num_problem_info_t     ; (* Problem information          *)
  }


type numprog_pos_t = string * Expr.tid option

type domain_t = Poly | Intvl | Oct | IntvlPoly | Eq



module LocSet = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = loc_t
  end
)

let loc_list_to_set (ls:loc_t list) : LocSet.t =
  List.fold_left (fun s l -> LocSet.add l s) LocSet.empty ls


let testingCounter = ref 0

let wait_for_widening = ref 0

let trs_widening = ref 2

let iterations = ref 0

let widening_steps = ref 0



(* EXCEPTIONS *)
exception No_numerical_expression of string
exception No_invariant_info




(* CONFIGURATION *)
let no_tid      : string        = "noTid"
let defLoc      : string        = "loc_"
let defSelfLoop : string        = "selfloop"
let defTranName : string        = "tran"

let trsParser   : string        = "trsParse"
let trsCmd      : string        = "../concurAbstrInterpreter/" ^ trsParser
let trsCmdLazy  : string        = "../numericalInvGen-v2/" ^ trsParser

let pProject    : string        = "pProject"
let pProjectCmd : string        = "../polyProject/" ^ pProject

let spagetthi_param : Expr.tid  = Expr.VarTh (Expr.build_global_var "k" Expr.Tid)




(* VARIABLE DATABASE *)
let all_vars : Expr.V.VarSet.t ref = ref Expr.V.VarSet.empty


(* VARIABLE PRINTING *)

let num_localize_var_id (v:Expr.varId) (p_name:string) : Expr.varId =
  sprintf "%s_%s" p_name v


let num_loc_var_option (v:Expr.varId) (p_name:string option) : Expr.varId =
  (* ALE: Provisional fix until we add support for pc using labels *)
  match p_name with
    Some "" -> (v)
  | _       -> Option.map_default (num_localize_var_id v) v p_name


let var_to_num_repres (id:Expr.varId) : Expr.varId =
  Str.global_replace (Str.regexp "::") "_" id


let domain_to_str (dType:domain_t) : string =
  match dType with
    Poly      -> "-poly"
  | Intvl     -> "-intvl"
  | Oct       -> "-oct"
  | IntvlPoly -> "-intvl+poly"
  | Eq        -> "-eq"


let absIntMode_to_str (m:absIntMode_t) : string =
  match m with
    Lazy   -> "-lazy"
  | Interf -> "-interf-only"
  | Eager  -> ""
  | EagerPlus -> "-eager+"

let num_th_to_str (expr:Expr.tid) : string =
  match expr with
    Expr.VarTh v        -> "__" ^ (Expr.V.t_to_str v)
  | Expr.NoTid         -> no_tid
  | Expr.CellLockId _   -> raise(No_numerical_expression(Expr.tid_to_str expr))
  | Expr.CellLockIdAt _ -> raise(No_numerical_expression(Expr.tid_to_str expr))
  | Expr.TidArrayRd _  -> raise(No_numerical_expression(Expr.tid_to_str expr))
  | Expr.TidArrRd _    -> raise(No_numerical_expression(Expr.tid_to_str expr))


let num_th_option_to_str (expr:Expr.tid option) : string =
  Option.map_default num_th_to_str "" expr


(* Moves the priming to the end, to meet trsParse syntax *)
let numvar_to_str (id:Expr.varId)
                  (pr:bool)
                  (th:Expr.tid option)
                  (p:string option) : string =
  let th_str = num_th_option_to_str th in
  let localized_var = num_loc_var_option id p in
  let var_name = sprintf "%s%s" localized_var th_str
  in
    if pr then var_name ^ "'" else var_name


let numvariable_to_str (v:Expr.V.t) : string =
  let id = Expr.V.id   v in
  let pr = Expr.var_pr   v in
  let th = Expr.var_th   v in
  let p  = Expr.var_proc v
  in
    numvar_to_str id pr th p


let loc_to_str (loc:loc_t) : string =
  String.concat "," (List.map string_of_int loc)


(* QUERY FUNCTIONS *)

let num_apply_localization (base:Expr.varId -> Expr.varId list)
                           (p_name:string option)
                           (v:Expr.varId) : Expr.varId list =
  match p_name with
    None   -> base v
  | Some "" -> base v (* FIX: provisional for label pc variables *)
  | Some p -> List.map (fun v -> num_localize_var_id v p) (base v)


let num_primed_vars (f:Expr.formula) : Expr.V.t list =
  Expr.primed_vars f


let num_all_vars (f:Expr.formula) : Expr.V.t list =
  Expr.all_vars f


(* CONSTRUCTION FUNCTIONS *)
let new_loc (xs:int list) : loc_t = xs



let pos_from_loc (l:loc_t) : int list = l


let new_guard (g:Expr.formula) : guard_t = g

let new_trans_rel (tr:Expr.formula) : trans_rel_t = tr

let new_num_assign (v:Expr.varId) (expr:Expr.integer) : num_assign_t = (v, expr)


let new_trans_info (s_loc:loc_t)
                   (e_loc:loc_t)
                   (guard:guard_t)
                   (t_rel:trans_rel_t) : num_trans_info_t =
  let p_vars = num_primed_vars t_rel in
  let pres_vars = List.fold_left (fun s e ->
                    Expr.V.VarSet.remove e s
                  ) !all_vars p_vars in
    (s_loc, e_loc, guard, t_rel, Expr.V.VarSet.elements pres_vars)



let get_info_sloc  ((s_loc,_,_,_,_):num_trans_info_t) : loc_t = s_loc
let get_info_eloc  ((_,e_loc,_,_,_):num_trans_info_t) : loc_t = e_loc
let get_info_guard ((_,_,guard,_,_):num_trans_info_t) : guard_t = guard
let get_info_relat ((_,_,_,relat,_):num_trans_info_t) : trans_rel_t = relat
let get_info_pres  ((_,_,_,_, pres):num_trans_info_t) : Expr.V.t list = pres



let new_num_location (name:loc_t) (initial:guard_t) : num_location_t =
  (name,initial)


let new_selfloop_label (loc:int list)
                       (from_loc:int list)
                       (to_loc:int list)
                       (variant:int)
                       (sub:int) : string =
  sprintf "%s_l%s_f%s_t%s_v%i%s"
              (defSelfLoop)
              (String.concat "_" $ List.map string_of_int loc)
              (String.concat "_" $ List.map string_of_int from_loc)
              (String.concat "_" $ List.map string_of_int to_loc)
              (variant)
              ("_sub" ^ string_of_int sub)


let new_tran_label (from_loc:int list) (to_loc:int list) (variant:int) :string =
  sprintf "%s_f%s_t%s_v%i" (defTranName)
                           (String.concat "_" $ List.map string_of_int from_loc)
                           (String.concat "_" $ List.map string_of_int to_loc)
                           (variant)



(* PRINTING FUNCTIONS *)

let numprog_pos_name (p:numprog_pos_t) : Expr.varId =
  let (n,_) = p
  in
    Conf.defCountAbs_name ^ n


let numprog_pos_to_variable (p:numprog_pos_t) : Expr.V.t =
  let var_name = numprog_pos_name p
  in
    Expr.build_var var_name Expr.Int false None None Expr.Normal


let numprog_pos_to_str (p:numprog_pos_t) : string =
  let (n,t) = p in
  let t_str = Option.map_default num_th_to_str "" t
  in
    Conf.defCountAbs_name ^ n ^ t_str



let rec num_integer_to_str (expr:Expr.integer) : string =
  match expr with
    Expr.VarInt v       -> numvariable_to_str v
  | Expr.IntNeg i       -> sprintf "-%s" (num_integer_to_str i)
  | Expr.IntAdd (i1,i2) -> sprintf "%s + %s" (num_integer_to_str i1)
                                             (num_integer_to_str i2)
  | Expr.IntSub (i1,i2) -> sprintf "%s - %s" (num_integer_to_str i1)
                                             (num_integer_to_str i2)
  | Expr.IntMul (i1,i2) -> sprintf "%s * %s" (num_integer_to_str i1)
                                             (num_integer_to_str i2)
  | Expr.IntDiv (i1,i2) -> sprintf "%s / %s" (num_integer_to_str i1)
                                             (num_integer_to_str i2)
  | _                   -> Expr.integer_to_str expr


let rec num_integer_paren_to_str (expr:Expr.integer) : string =
  match expr with
    Expr.VarInt v       -> numvariable_to_str v
  | Expr.IntNeg i       -> sprintf "-(%s)" (num_integer_paren_to_str i)
  | Expr.IntAdd (i1,i2) -> sprintf "(%s + %s)" (num_integer_paren_to_str i1)
                                             (num_integer_paren_to_str i2)
  | Expr.IntSub (i1,i2) -> sprintf "(%s - %s)" (num_integer_paren_to_str i1)
                                             (num_integer_paren_to_str i2)
  | Expr.IntMul (i1,i2) -> sprintf "(%s * %s)" (num_integer_paren_to_str i1)
                                             (num_integer_paren_to_str i2)
  | Expr.IntDiv (i1,i2) -> sprintf "(%s / %s)" (num_integer_paren_to_str i1)
                                             (num_integer_paren_to_str i2)
  | _                   -> Expr.integer_to_str expr




let num_term_to_str (expr:Expr.term) : string =
  match expr with
    Expr.VarT v -> numvariable_to_str v
  | Expr.IntT i -> num_integer_to_str i
  | _           -> Expr.term_to_str expr


let num_eq_to_str ((e1,e2):Expr.eq) : string =
      sprintf "%s = %s" (num_term_to_str e1) (num_term_to_str e2)


let num_diseq_to_str (expr:Expr.diseq) : string =
    let (e1,e2) = expr in
      sprintf "%s != %s" (num_term_to_str e1) (num_term_to_str e2)


let num_atom_to_str (ato:Expr.atom) : string =
  match ato with
    Expr.Less (i1, i2)      -> sprintf "%s < %s" (num_integer_to_str i1)
                                                 (num_integer_to_str i2)
  | Expr.Greater (i1, i2)   -> sprintf "%s > %s" (num_integer_to_str i1)
                                                 (num_integer_to_str i2)
  | Expr.LessEq (i1, i2)    -> sprintf "%s <= %s" (num_integer_to_str i1)
                                                  (num_integer_to_str i2)
  | Expr.GreaterEq (i1, i2) -> sprintf "%s >= %s" (num_integer_to_str i1)
                                                  (num_integer_to_str i2)
  | Expr.Eq(exp)            -> num_eq_to_str (exp)
  | Expr.InEq(exp)          -> num_diseq_to_str (exp)
  | _                       -> Expr.atom_to_str ato


let num_literal_to_str (lit:Expr.literal) : string =
  match lit with
    Expr.Atom a    -> num_atom_to_str a
  | Expr.NegAtom a -> sprintf "~ %s" (num_atom_to_str a)


let rec num_formula_to_str (expr:Expr.formula) : string =

  let rec clean_trues_in_ands f =
    match f with
      Expr.And(f1,f2) -> let cf1 = clean_trues_in_ands f1 in
                         let cf2 = clean_trues_in_ands f2
                         in
                           if      cf1 = Expr.True then cf2
                           else if cf2 = Expr.True then cf1
                           else    Expr.And(cf1,cf2)
    |  _              -> f
  in
  match (clean_trues_in_ands expr) with
    Expr.Literal (lit)  -> num_literal_to_str lit
  | Expr.And(f1, f2)    -> sprintf "%s & %s" (num_formula_to_str f1) (num_formula_to_str f2)
  | Expr.Or(f1,f2)      -> sprintf "%s \\/ %s" (num_formula_to_str f1)
                                               (num_formula_to_str f2)
  | Expr.Not(f)         -> sprintf "~ %s" (num_formula_to_str f)
  | Expr.Implies(f1,f2) -> sprintf "%s -> %s" (num_formula_to_str f1)
                                              (num_formula_to_str f2)
  | Expr.Iff (f1,f2)    -> sprintf "%s <-> %s" (num_formula_to_str f1)
                                               (num_formula_to_str f2)
  | _                   -> Expr.formula_to_str expr

let rec num_formula_vars_to_str (expr:Expr.formula) : string =
  String.concat ", " $ List.map numvariable_to_str (Expr.all_vars expr)


let num_expr_to_str (expr:Expr.expr_t) : string =
  match expr with
    Expr.Term t    -> Expr.term_to_str t
  | Expr.Formula b -> num_formula_to_str b


(* Printing for invariant specifications *)

let rec spec_inv_integer_to_str (expr:Expr.integer) : string =
  match expr with
    Expr.VarInt v       -> numvariable_to_str v
  | Expr.IntNeg i       -> sprintf "-%s" (spec_inv_integer_to_str i)
  | Expr.IntAdd (i1,i2) -> sprintf "%s + %s" (spec_inv_integer_to_str i1)
                                             (spec_inv_integer_to_str i2)
  | Expr.IntSub (i1,i2) -> sprintf "%s - %s" (spec_inv_integer_to_str i1)
                                             (spec_inv_integer_to_str i2)
  | Expr.IntMul (i1,i2) -> sprintf "%s * %s" (spec_inv_integer_to_str i1)
                                             (spec_inv_integer_to_str i2)
  | Expr.IntDiv (i1,i2) -> sprintf "%s / %s" (spec_inv_integer_to_str i1)
                                             (spec_inv_integer_to_str i2)
  | _                   -> Expr.integer_to_str expr


let spec_inv_term_to_str (expr:Expr.term) : string =
  match expr with
    Expr.VarT v -> numvariable_to_str v
  | Expr.IntT i -> spec_inv_integer_to_str i
  | _           -> Expr.term_to_str expr


let spec_inv_eq_to_str ((e1,e2):Expr.eq) : string =
      sprintf "%s = %s" (spec_inv_term_to_str e1) (spec_inv_term_to_str e2)


let spec_inv_diseq_to_str (expr:Expr.diseq) : string =
    let (e1,e2) = expr in
      sprintf "%s != %s" (spec_inv_term_to_str e1) (spec_inv_term_to_str e2)


let spec_inv_atom_to_str (ato:Expr.atom) : string =
  match ato with
    Expr.Less (i1, i2)      -> sprintf "%s < %s" (spec_inv_integer_to_str i1)
                                                 (spec_inv_integer_to_str i2)
  | Expr.Greater (i1, i2)   -> sprintf "%s > %s" (spec_inv_integer_to_str i1)
                                                 (spec_inv_integer_to_str i2)
  | Expr.LessEq (i1, i2)    -> sprintf "%s <= %s" (spec_inv_integer_to_str i1)
                                                  (spec_inv_integer_to_str i2)
  | Expr.GreaterEq (i1, i2) -> sprintf "%s >= %s" (spec_inv_integer_to_str i1)
                                                  (spec_inv_integer_to_str i2)
  | Expr.Eq(exp)            -> spec_inv_eq_to_str (exp)
  | Expr.InEq(exp)          -> spec_inv_diseq_to_str (exp)
  | _                       -> Expr.atom_to_str ato


let spec_inv_literal_to_str (lit:Expr.literal) : string =
  match lit with
    Expr.Atom a    -> spec_inv_atom_to_str a
  | Expr.NegAtom a -> sprintf "~ %s" (spec_inv_atom_to_str a)


let rec spec_inv_formula_to_str (expr:Expr.formula) : string =

  let rec clean_trues_in_ands f =
    match f with
      Expr.And(f1,f2) -> let cf1 = clean_trues_in_ands f1 in
                         let cf2 = clean_trues_in_ands f2
                         in
                           if      cf1 = Expr.True then cf2
                           else if cf2 = Expr.True then cf1
                           else    Expr.And(cf1,cf2)
    |  _              -> f
  in
  match (clean_trues_in_ands expr) with
    Expr.Literal (lit)  -> num_literal_to_str lit
  | Expr.And(f1, f2)    -> sprintf "%s /\\ %s" (spec_inv_formula_to_str f1)
                                             (spec_inv_formula_to_str f2)
  | Expr.Or(f1,f2)      -> sprintf "%s \\/ %s" (spec_inv_formula_to_str f1)
                                               (spec_inv_formula_to_str f2)
  | Expr.Not(f)         -> sprintf "~ %s" (spec_inv_formula_to_str f)
  | Expr.Implies(f1,f2) -> sprintf "%s -> %s" (spec_inv_formula_to_str f1)
                                              (spec_inv_formula_to_str f2)
  | Expr.Iff (f1,f2)    -> sprintf "%s <-> %s" (spec_inv_formula_to_str f1)
                                               (spec_inv_formula_to_str f2)
  | _                   -> Expr.formula_to_str expr



(* INFORMATION UPDATING FUNCTIONS *)
let update_param_trans_info (t_info:num_trans_info_t)
                            (from_loc:loc_t)
                            (to_loc:loc_t)
                            (th:Expr.tid) : num_trans_info_t =
  let (_,_,guard,trel,_) = t_info in
  let param_guard = Expr.param (Some th) guard in
  let param_trel = Expr.param (Some th) trel in
  let p_vars = num_primed_vars param_trel in
  let pres_vars = List.fold_left (fun s e ->
                    Expr.V.VarSet.remove e s
                  ) !all_vars p_vars
  in
    (from_loc, to_loc, param_guard, param_trel, Expr.V.VarSet.elements pres_vars)



let update_selfloop_pos (t_info:num_trans_info_t)
                        (loc:loc_t) : num_trans_info_t =
  let (_,_,guard,trel,vars) = t_info
  in
    (loc,loc,guard,trel,vars)


let update_info (t_info:num_trans_info_t)
                (new_guard:Expr.formula)
                (new_effect:Expr.formula) : num_trans_info_t =
  (* FIX: The guard here should be updated by the new_effect formula *)
  (* FIX: The guard may be the enabling condition of the formula *)
  let (s_loc, e_loc, _, prev_effect, presVars) = t_info in
  (* ALE: Check whether this is fine. *)
  let new_info = (*if prev_effect = new_effect then
                   (s_loc, e_loc, new_guard, prev_effect, presVars)
                 else*)
                   new_trans_info s_loc e_loc new_guard new_effect
  in
    new_info



(* Printing for invariant specifications *)

let loc_to_str (l:loc_t) : string =
  defLoc ^ (String.concat "_" $ List.map string_of_int l)


let guard_to_str (g:guard_t) : string = num_formula_to_str g


let trans_rel_to_str (tr:trans_rel_t) : string = num_formula_to_str tr


let num_trans_info_to_str (info:num_trans_info_t) : string =
  let (s_loc,e_loc,guard,t_rel,vars) = info in
  let guard_str = guard_to_str guard in
  let t_str = trans_rel_to_str t_rel in
  let vars_str = String.concat ", " $ List.map numvariable_to_str vars in
  let s_loc_str = loc_to_str s_loc in
  let e_loc_str = loc_to_str e_loc
  in
    sprintf "\t%s, %s,\n\
             \t(%s),\n\
             \t(\n\
             \t  %s\n\
             \t),\n\
             \tpres {%s}" s_loc_str e_loc_str guard_str t_str vars_str


let num_location_to_str (loc:num_location_t) : string =
  let (name, initial) = loc in
  let name_str = loc_to_str name in
  let initial_str = guard_to_str initial
  in
    sprintf "location %s [\n\
             \tinitial\n\
             \t\t%s\n]" name_str initial_str


let num_problem_to_str (prob:num_problem_t) : string =
  (* let vars_str  = String.concat "," $ List.map numvariable_to_str prob.vars in *)
  (* Partition prob.vars into local and global vars *)
  let locVars,glbVars = List.partition (Expr.V.is_local) prob.vars in
  let allVars_str = String.concat " , " (List.map numvariable_to_str prob.vars) in

  let glbVars = List.filter (fun v -> v <> Sys.me_tid_var) glbVars in
  let locVars = Sys.me_tid_var :: locVars in

  let gvars_str = String.concat " , " (List.map numvariable_to_str glbVars) in 
  let lvars_str = String.concat " , "( List.map numvariable_to_str locVars) in 
  let locs_str  = String.concat "\n\n" $ List.map num_location_to_str prob.locs in
  let trans_str = String.concat "\n\n" $
    List.map (fun (f,t,v,_,_,info) ->
      let label    = new_tran_label f t v in
      let tran_str = num_trans_info_to_str info
      in
      sprintf "transition %s [\n%s\n]" label tran_str
    ) prob.mats in
  let self_str  = match prob.info.absIntMode with
      Eager -> ""
    | EagerPlus -> ""
    | Interf -> ""
    | _     -> List.fold_left (fun str (f,t,v,sub,_,info) ->
      let guard = get_info_guard info in
      if guard = Expr.False then
        str
      else
        let (pos,_,_,_,_) = info in
        let label = new_selfloop_label pos f t v sub in
        let tran_str = num_trans_info_to_str info
        in
        str ^ sprintf "transition %s [\n%s\n]\n\n" label tran_str
    ) "" prob.self
  in
    if prob.info.absIntMode = Lazy then
      sprintf "problem %s\n\n\
               var %s \n\n\
               %s\n\n%s\n\n%s\n\n end \n" 
          prob.name allVars_str locs_str trans_str self_str
    else
      sprintf "problem %s\n\n\
               shared %s \n\n\
               local %s\n\n\
               %s\n\n%s\n\n%s\n\n end \n" 
          prob.name gvars_str lvars_str locs_str trans_str self_str


let exist_elimination_to_str (gVars:Expr.V.t list)
    (lVars:Expr.V.t list)
    (cond:Expr.formula) : string =
  let gVars_str = String.concat ", " $ List.map numvariable_to_str gVars in
  let lVars_str = String.concat ", " $ List.map numvariable_to_str lVars in
  let cond_str  = num_formula_to_str cond
  in
  sprintf "vars %s\n\
             exists %s\n\n\
             %s\n" gVars_str lVars_str cond_str


let inv_table_to_str (inv_tbl:inv_table_t) : string =
  let tbl_str = Hashtbl.fold (fun loc inv str ->
    let loc_str = loc_to_str loc in
    sprintf "%s%s:\n%s\n\n" str loc_str (num_formula_to_str inv)
  ) inv_tbl ""
  in
  tbl_str


let invs_for_spec (inv_tbl:inv_table_t) : string =
  let spec_str = Hashtbl.fold (fun loc inv str ->
                   let loc_str = loc_to_str loc in
                     sprintf "%s%s: %s\n\n"
                        str loc_str (spec_inv_formula_to_str inv)
                 ) inv_tbl ""
  in
    spec_str


let stat_info_str (sys:Sys.t) (prob:num_problem_t) : string =
  let pos_num = 1 + Sys.get_trans_num sys in
  let var_num = List.length prob.vars in
  let loc_num = List.length prob.locs in
  let trans_num = Hashtbl.length prob.trans in
  let trans_list = String.concat ", " $ Hashtbl.fold (fun (f,t,v) _ xs -> (sprintf "%i->%i[%i]" f t v)::xs ) prob.trans [] in
  let comp_trans_num = List.length prob.mats in
  let selfloop_num = List.length prob.self
  in
    sprintf "Program positions : %i\n\
             Total variables : %i\n\
             Locations : %i\n\
             Transitions : %i\n\
              %s\n\
             Composed transitions : %i\n\
             Selfloops : %i \n"
      pos_num var_num loc_num trans_num trans_list comp_trans_num selfloop_num



(* NUMERIC PROGRAM MANIPULATION FUNCTIONS *)

let gen_all_position_vars (sys:Sys.t) : Expr.varId list =
  let prog_lines = Sys.get_trans_num sys
  in
    List.map (Expr.new_num_pos_var_id Conf.defCountAbs_name) $
      LeapLib.rangeList 1 (prog_lines+1)


let gen_all_position_vars_from_labels (sys:Sys.t) : Expr.varId list =
  let label_list = Sys.get_labels_list (Sys.get_labels sys)
  in
    List.map (Expr.new_label_pos_var_id Conf.defCountAbs_name) label_list


let get_all_num_vars_from_sys (sys:Sys.t) : Expr.varId list =
  let var_ids    = Sys.get_all_vars_id sys in
  let pos_vars   = gen_all_position_vars sys
  in
    var_ids @ [Conf.defCountAbs_name] @ pos_vars


let get_all_numlabel_vars_from_sys (sys:Sys.t) : Expr.varId list =
  let var_ids = Sys.get_all_vars_id sys in
  let labels_vars = gen_all_position_vars_from_labels sys
  in
    var_ids @ [Conf.defCountAbs_name] @ labels_vars



(* NEW FUNCTIONS *)

let new_numprog_pos (n:int) (t:Expr.tid option) : numprog_pos_t =
  (string_of_int n, t)


let new_numprog_pos_from_label (l:string) (t:Expr.tid option) : numprog_pos_t =
  (l, t)


let gen_position_vars (sys:Sys.t) : numprog_pos_t list =
  let prog_lines = LeapLib.rangeList 1( (Sys.get_trans_num sys) + 1)
  in
    List.map (fun l -> (string_of_int l, None)) prog_lines


let gen_position_vars_from_labels (sys:Sys.t) : numprog_pos_t list =
  let label_list = Sys.get_labels_list (Sys.get_labels sys)
  in
    List.map (fun l -> (l, None)) label_list


let param_progpos ((n,_):numprog_pos_t) (t:Expr.tid option) : numprog_pos_t =
  (n, t)


let numprogpos_to_integer (np:numprog_pos_t) : Expr.integer =
  let (_,t) = np
  in
    Expr.VarInt (Expr.build_var (numprog_pos_name np) Expr.Int false t None Expr.Normal)


let build_num_pos_eq (np:numprog_pos_t) (expr:Expr.integer) : Expr.formula =
  Expr.eq_int (numprogpos_to_integer np) expr



(* NEW FUNCTIONS *)

let param_num_var_id (t:Expr.tid) (id:Expr.varId) : Expr.varId =
  match t with
    Expr.VarTh v        -> id ^ "_" ^ (Expr.V.t_to_str v)
  | Expr.NoTid         -> id
  | Expr.CellLockId _   -> raise(No_numerical_expression(Expr.tid_to_str t))
  | Expr.CellLockIdAt _ -> raise(No_numerical_expression(Expr.tid_to_str t))
  | Expr.TidArrayRd _  -> raise(No_numerical_expression(Expr.tid_to_str t))
  | Expr.TidArrRd _    -> raise(No_numerical_expression(Expr.tid_to_str t))


let build_trans_info (sys:Sys.t)
                     (use_labels:bool) : num_trans_info_table_t =
  let variant_count = ref 0 in
  let label_tbl  = Sys.get_labels sys in
  let tbl        = Hashtbl.create 100 in
  let lines_num  = Sys.get_trans_num sys in
  let prog_lines = LeapLib.rangeList 1 lines_num in
  let _ = List.iter (fun line ->
            let (_,stm) = Sys.get_statement_at sys line in
            let someone = if use_labels then
                            Expr.someone_at_labels
                              (Sys.get_labels_for_pos label_tbl line)
                          else
                            Expr.someone_at line in
            let effects = Bridge.gen_st_cond_effect Bridge.Num stm false in
            let _ = List.iter (fun (grd,effect,c,n) ->
                      let pos_change = if c = n then
                                         Expr.True
                                       else
                                         if use_labels then
                                           Expr.build_label_change
                                            (Sys.get_labels_for_pos label_tbl c)
                                            (Sys.get_labels_for_pos label_tbl n)
                                         else
                                           Expr.build_pos_change c n in
                      let c_dnf = Expr.dnf (Expr.to_trs grd) in
                      List.iter (fun phi_list ->
                        let cond = Expr.conj_list phi_list in
                        let guard = Expr.expr_and_removing_true someone cond in
                        let t_rel = Expr.expr_and_removing_true pos_change effect in
                        let info = new_trans_info [c] [n] guard t_rel
                        in
                          Hashtbl.add tbl (c, n, !variant_count) info;
                          incr variant_count
                      ) c_dnf
                    ) effects
            in
              variant_count := 0
          ) prog_lines
  in
    tbl


let build_global_init_cond (sys:Sys.t) (conc_ths:int) : Expr.formula =
  let global_theta = VCG.gen_global_init_cond sys in
  let cond_n = Expr.greatereq_form Expr.defCountVar (Expr.IntVal conc_ths)
  in
    Expr.conj_list (cond_n :: global_theta)



let build_loc_init_cond (sys:Sys.t)
                        (ths:Expr.tid list)
                        (use_labels:bool) : Expr.formula =

  let lines_num          = Sys.get_trans_num sys + 1 in
  let prog_lines         = LeapLib.rangeList 1 lines_num in
  let local_theta        = VCG.gen_local_init_cond sys Sys.defMainProcedure in
  let assign_zero v      = Expr.eq_int v (Expr.IntVal 0) in
  let main_proc_info     = Sys.get_proc_by_name sys Sys.defMainProcedure in
  let first_line         = Sys.proc_init_line main_proc_info in
  let lines_except_first = List.filter (fun i -> i != first_line) prog_lines in


  let label_tbl    = Sys.get_labels sys in
  let label_list   = Sys.get_labels_list label_tbl in
  let init_labels  = Sys.get_labels_for_pos label_tbl first_line in
  let other_labels = List.filter (fun e ->
                       not (List.mem e init_labels)
                     ) label_list in

  let pos_var_n1 =
    if use_labels then
      List.map (fun l -> new_numprog_pos_from_label l None) init_labels
    else
      [new_numprog_pos first_line None] in

  let pos_var_others =
    if use_labels then
      List.map (fun l -> new_numprog_pos_from_label l None) other_labels
    else
      List.map (fun l -> new_numprog_pos l None) lines_except_first in

  let local_theta_list = match ths with
                           [] -> local_theta
                         | _  -> List.flatten $ List.map (fun t ->
                                   List.map (fun cond ->
                                     Expr.param (Some t) cond
                                   ) local_theta
                                 ) ths in

  let init_cond = let cond_n1 = List.map (fun pv ->
                                    build_num_pos_eq pv Expr.defCountVar
                                  ) pos_var_n1 in

                    let cond_others = List.map (fun pv ->
                                        assign_zero (numprogpos_to_integer pv)
                                      ) pos_var_others

                    in
                      Expr.conj_list (cond_n1 @ cond_others)
  in
    Expr.conj_list (local_theta_list @ [init_cond])


let gen_all_num_vars (sys:Sys.t)
                     (ths:Expr.tid list)
                     (use_labels:bool) : Expr.V.t list =
  let (gTbl, l_list) = Sys.get_sys_var_tables sys in
  let gVars = Sys.get_var_list gTbl None in
  let lVars = List.fold_left (fun xs (p,iTbl,lTbl) ->
                let is = Sys.get_var_list iTbl (Some p) in
                let ls = Sys.get_var_list lTbl (Some p)
                in
                  is @ ls @ xs
              ) [] l_list in
  let pos_vars = if use_labels then
                   gen_position_vars_from_labels sys
                 else
                   gen_position_vars sys in
  let lVars_list = match ths with
                     [] -> lVars
                   | _  -> List.flatten $
                             List.map (fun t ->
                               List.map (fun v ->
                                  Expr.V.set_paramiable (Some t) v
                               ) lVars
                             ) ths in
  let pos_vars_list = List.map numprog_pos_to_variable pos_vars in
  let def_n_var = Expr.build_var Conf.defCountAbs_name Expr.Int
                                 false None None Expr.Normal
  in
    Sys.me_tid_var :: gVars @ lVars_list @ [def_n_var] @ pos_vars_list



let gen_locations (sys:Sys.t)
                  (ths:Expr.tid list)
                  (use_labels:bool) : (num_location_t list * loc_t) =

  (* Initial location *)
  let init_loc = ref [] in

  (* Common part *)
  let prog_lines = LeapLib.rangeList 1 (Sys.get_trans_num sys + 1) in
  let main_proc_info = Sys.get_proc_by_name sys Sys.defMainProcedure in
  let first_line = Sys.proc_init_line main_proc_info in
  let conc_ths = match ths with
                      [] -> 1
                    | _  -> List.length ths in
  (* Common part *)

  let combinations = match ths with
                      [] -> List.map (fun x -> [x]) prog_lines
                    | _  -> LeapLib.comb prog_lines (List.length ths) in

  let locs = List.map (fun ps ->
               let label = new_loc ps in
               let is_init_pos = List.for_all (fun p -> p = first_line) ps in
               let cond = if is_init_pos then
                            let gConds = build_global_init_cond sys conc_ths in
                            let lConds = build_loc_init_cond sys ths use_labels in
                            let _ = init_loc := label
                            in
                              Expr.expr_and_removing_true gConds lConds
                          else
                            Expr.False
               in
                 (label, cond)
             ) combinations
  in
    (locs, !init_loc)




(* NEW FUNCTIONS *)
let gen_transitions (trans_tbl:num_trans_info_table_t)
                    (sys:Sys.t)
                    (ths:Expr.tid list)
                        : (num_trans_t list * num_trans_t list) =

  let prog_lines = LeapLib.rangeList 1 (Sys.get_trans_num sys + 1) in
  let param_num = List.length ths in
  let index_pos_list = LeapLib.rangeList 0 (param_num - 1) in

  let trans_pair =
    let ts = Hashtbl.fold (fun (curr, next, varnt) info ts ->
               List.fold_left (fun ts ix ->
                 let cmb_list = mid_comb_tuple prog_lines param_num ix
                 in
                   List.fold_left (fun ts (pre,post) ->
                     let curr_loc = pre @ [curr] @ post in
                     let next_loc = pre @ [next] @ post in
                     let param = List.nth ths ix in
                     let p_info = update_param_trans_info info
                                     curr_loc next_loc param in
                     let t = (curr_loc, next_loc, varnt, 0,
                                    (curr, next, param), p_info)
                     in
                       t::ts
                   ) ts cmb_list
               ) ts index_pos_list
             ) trans_tbl [] in

    let all_possible_locs = comb prog_lines param_num in

    let ss = List.fold_left (fun ss pos ->
               Hashtbl.fold (fun (curr, next, varnt) info ss ->
                 let self_info = new_trans_info pos pos Expr.False Expr.True in
                    List.fold_left (fun xs sub ->
                      let s = ([curr], [next], varnt, sub,
                                (curr, next, spagetthi_param), self_info)
                      in
                        s::xs
                    ) ss (rangeList 0 (param_num-1))
               ) trans_tbl ss
             ) [] all_possible_locs
    in
      (ts, ss)
  in
    trans_pair




(* Given a formula, makes the query of such formula to polyProject *)
let call_polyProject (phi:Expr.formula) (ths:Expr.tid list) : Expr.formula =
  let gVars = Expr.all_global_vars phi in
  let lVars = Sys.me_tid_var :: Expr.all_local_vars phi in
  let (prjVars, keepVars) = List.partition (fun v ->
                              match Expr.var_th v with
                                None -> false
                              | Some t -> not (List.mem t ths)
                            ) lVars in
  if (gVars = [] || prjVars = []) then
    (* No local variables to be projected *)
    phi
  else
    (* Local variables to project and global variables to reflect projection *)
    (* We kept the non-thread id variables *)
    let query = exist_elimination_to_str (gVars@keepVars) prjVars phi in
    (* Output to a tempfile Sriram query *)
    let temp  = Filename.temp_file "project_" ".in" in
    let _ = Debug.print_file_name "Projection" temp in
    let out_ch = open_out temp in
    let _ = output_string out_ch query in
    let _ = close_out out_ch in
    (* Call the "exists" program *)
    let cmd = pProjectCmd ^ " " ^ temp in
    let in_ch = Unix.open_process_in cmd in
    let pProjectRes = Interface.File.readChannel in_ch in
    let prjForm = TrsParser.exists_projector norm
                      (Lexing.from_string pProjectRes) in
    Debug.infoMsg (fun _ -> "Given formula:\n" ^ (Expr.formula_to_str phi) ^ "\n");
    Debug.infoMsg (fun _ -> "Projected formula:\n" ^ (Expr.formula_to_str prjForm) ^ "\n");
    prjForm



let gen_visit_order (trans:num_trans_t list)
                    (sys:Sys.t)
                    (ths:Expr.tid list)
                    (loc_num:int) : loc_t list =

  (* We create a table with the location relation extracted from transitions *)
  let locTbl = Hashtbl.create loc_num in
  let _ = List.iter (fun (f,t,_,_,_,_) -> Hashtbl.add locTbl f t) trans in
  (* The queue construction function: BFS *)
  let rec bfs es s =
    match es with
      []    -> []
    | x::xs -> if (LocSet.mem x s) then
                 bfs xs s
               else
                 let s' = LocSet.add x s in
                 let next = loc_list_to_set (Hashtbl.find_all locTbl x) in
                 let unvisited = LocSet.elements (LocSet.diff next s)
                 in
                   x :: (bfs (xs @ unvisited) s') in
  let main_proc_info = Sys.get_proc_by_name sys Sys.defMainProcedure in
  let first_line = Sys.proc_init_line main_proc_info in
  let visit_order = bfs [list_of (List.length ths) first_line] LocSet.empty
  in
    visit_order




let new_num_problem (name:string)
                    (sloops:bool)
                    (sys:Sys.t)
                    (ths:Expr.tid list)
                    (use_labels:bool)
                    (tactic:tactic_t option)
                    (updLocs:bool)
                    (absIntMode:absIntMode_t) : num_problem_t =

  (**********************************************************************)
  (* Only for this kind of programs, we eliminate all global
     variables of the form Nx, used to denote program locations.
     This is not needed, but this way we prevent variable duplication.
     Perhaps we need a better mechanism. By now, it will be enough as to
     carry out some tests.
  *)
  let pos_regexp = Str.regexp "N[0-9]*" in
  let sys = Sys.del_global_var_regexp sys pos_regexp in
  (**********************************************************************)
  let vars = gen_all_num_vars sys ths use_labels in
  let _ = all_vars := Expr.V.varset_from_list vars in
  let (locs, init_loc) = gen_locations sys ths use_labels in
  let info_tbl = build_trans_info sys use_labels in
  (* let prj_tbl = build_prj_table info_tbl ths in *)
  let (trans,selfs) = gen_transitions info_tbl sys ths in
  let final_selfs = if sloops then selfs else [] in
  let locs_num = List.length locs in
  let order = gen_visit_order trans sys ths locs_num in
  let info = {ths         = ths    ; tactic     = tactic    ;
              visit_order = order  ; init_loc   = init_loc  ;
              updLocs     = updLocs; absIntMode = absIntMode;
             }
  (* let _ = Printf.printf "SELFS: %i\n" (List.length final_selfs) in *)
  in
    { name = name;
      vars = vars;
      locs = locs;
      mats = trans;
      self = final_selfs;
      trans = info_tbl;
      invs = Hashtbl.create (List.length locs);
      info = info;
    } 



(* Invariant manipulation functions *)

let extract_trs_info (input:string) : string =
  let init_pos = Str.search_forward (Str.regexp "@") input 0 in
  let end_pos = Str.search_backward (Str.regexp ")[^)]*") input
                    (String.length input) in
  let substring = "Invariant " ^
                  String.sub input init_pos (end_pos - init_pos) ^ ")"
  in
    substring


let update_selfloops (prob:num_problem_t) (iTbl:inv_table_t) : num_problem_t =
  let _ = print_endline "Projecting local variables..." in

  (* We compute the projections only once *)
  let prjTbl = Hashtbl.create 100 in

  let new_selfs =
    List.map (fun (f,t,v,sub,(trans_f,trans_t,th),info) ->
      let loc = get_info_sloc info in
      let loc' = insert_at trans_f loc sub in
      let (new_grd,new_eff) =
        try
          Hashtbl.find prjTbl (loc', trans_f, trans_t, v, sub)
        with
          _ -> let (_,_,grd,eff,_) = Hashtbl.find prob.trans (trans_f, trans_t, v) in
               let grd' = Expr.param (Some spagetthi_param) grd in
               let eff' = Expr.param (Some spagetthi_param) eff in
               let subst = Expr.new_tid_subst [(List.nth prob.info.ths sub,
                                                spagetthi_param)] in
               let inv' = Expr.subst_tid subst (Hashtbl.find iTbl loc') in
               let phi = [inv';grd';eff'] in
               let prj = if (List.exists (fun l -> l = Expr.False) phi) then
                           Expr.False
                         else
                           call_polyProject (Expr.conj_list [inv';grd';eff'])
                                            (prob.info.ths) in

               let (grds, effs) = List.partition (fun phi ->
                                    (Expr.primed_vars phi) = []
                                  ) (Expr.to_conj_list prj) in

               let newG = Expr.conj_list grds in
               let newE = Expr.conj_list effs in
               let _ = Hashtbl.add prjTbl (loc', trans_f, trans_t, v, sub) (newG,newE)
               in
                 (newG, newE)
      in
        (f,t,v,sub, (trans_f,trans_t,th), update_info info new_grd new_eff)
    ) prob.self in
    let _ = prob.self <- new_selfs
  in
    prob



let call_trs (prob:num_problem_t) (dType:domain_t) : inv_table_t =
  let prob_str    = num_problem_to_str prob in
  let tempFile    = Filename.temp_file "trsParser_" ".in" in
  let _           = Debug.print_file_name "Problem" tempFile in
  let out_ch      = Pervasives.open_out tempFile in
  let _           = fprintf out_ch "%s" prob_str in
  let _           = Pervasives.close_out out_ch in
  
  let cmd         = if prob.info.absIntMode = Lazy then
                      sprintf "%s %s -w %i %s" (trsCmdLazy) (domain_to_str dType)
                                               (!trs_widening) (tempFile)
                    else
                      sprintf "%s %s %s -w %i %s" (trsCmd) (domain_to_str dType)
                                                (absIntMode_to_str prob.info.absIntMode)
                                                (!trs_widening) (tempFile) in
  let _           = print_endline $
                      sprintf "Calling invariant generator \
                               with widening %i..." !trs_widening in
  let _           = print_endline (sprintf "Calling command: %s" cmd) in
  let in_ch       = Unix.open_process_in cmd in
  let trsString   = Interface.File.readChannel in_ch in
  let _           = print_endline trsString in
  let trs_str     = extract_trs_info trsString in
  let _           = Debug.print_trsProblem trsString in

  let _           = print_endline "Parsing generated invariants..." in
  let _           = Printf.printf "%s\n" trs_str in
  let inv_tbl     = TrsParser.invariant_info norm (Lexing.from_string trs_str)
  in
    inv_tbl


let gen_widening_for_invs (inv:inv_table_t) (inv':inv_table_t) : inv_table_t =
  let wide_tbl = Hashtbl.create 100 in
  let _ = Hashtbl.iter (fun loc form ->
            let form'     = Hashtbl.find inv' loc in
            let num_form  = NumExp.formula_to_int_formula form in
            let num_form' = NumExp.formula_to_int_formula form' in
            let num_wide  = NumSolver.standard_widening num_form num_form' in
            let wide      = NumExp.int_formula_to_formula num_wide in
            let _         = Debug.print_widening_formulas
                              (loc)
                              (NumExp.formula_to_string num_form)
                              (NumExp.formula_to_string num_form')
                              (NumExp.formula_to_string num_wide)
            in
              Hashtbl.add wide_tbl loc wide
          ) inv
  in
    wide_tbl


let make_round_focus (prob:num_problem_t) (dType:domain_t) : num_problem_t =
  let _       = incr iterations in

  (* First I compute the system without loops *)
  (* Notice that if it works, then I can compute the system without loops only once
     and keep the results, as the only change between iterations are in selfloops *)

  let _ = printf "===== Computing full problem without selfloops =========\n" in

  let full_prob = {name = prob.name;
                   vars = prob.vars;
                   locs = prob.locs;
                   mats = prob.mats;
                   self = [];
                   trans = prob.trans;
                   invs = prob.invs;
                   info = prob.info;} in

  let temp_inv_tbl = call_trs full_prob dType in

  let with_selfloops_inv_tbl = Hashtbl.create (List.length prob.locs) in

  (* Then I compute each location in isolation using the invariants we have computed *)
  let _ = List.iter (fun (loc, _) ->
            let imp_self = List.filter (fun s ->
                             let (_,_,_,_,_,info) = s in
                               get_info_sloc info = loc
                           ) prob.self in

            let tmpProb = {name = prob.name;
                           vars = prob.vars;
                           locs = [(loc, Hashtbl.find temp_inv_tbl loc)];
                           mats = [];
                           self = imp_self;
                           trans = prob.trans;
                           invs = prob.invs;
                           info = prob.info;} in

            let _ = printf "===== Computing selfloop effect for location %s =========\n" (loc_to_str loc) in
            let tmp_tbl = call_trs tmpProb dType
            in
              Hashtbl.add with_selfloops_inv_tbl loc (Hashtbl.find tmp_tbl loc)
          ) prob.locs in

(*
  (* We apply internal widening to reduce the size of invariants *)
  let widening_invs = if Hashtbl.length prob.invs = 0 then
                        with_selfloops_inv_tbl
                      else
                        gen_widening_for_invs prob.invs with_selfloops_inv_tbl in
  (* We apply internal widening to reduce the size of invariants *)
*)

  let upd_prob = update_selfloops prob with_selfloops_inv_tbl in
  let _ = upd_prob.invs <- with_selfloops_inv_tbl in



  (* We make a final round with the full updated problem *)
  let final_invs = call_trs upd_prob dType in
  let final_prob = update_selfloops upd_prob final_invs in
  let _ = final_prob.invs <- final_invs in
  (* We make a final round with the full updated problem *)

  (* Updates location guards if necessary *)
  let upd_locs = if prob.info.updLocs then
                   List.map (fun (loc, grd) ->
                     (loc, Hashtbl.find final_invs loc)
                   ) prob.locs
                 else
                   prob.locs in
  let _ = final_prob.locs <- upd_locs
  (* Updates location guards if necessary *)
  in
    final_prob


let make_round_split (prob:num_problem_t) (dType:domain_t) : num_problem_t =
  let _       = incr iterations in
  let inv_tbl = Hashtbl.create (List.length prob.locs) in
  let lookup_inv tbl loc = try
                             Hashtbl.find inv_tbl loc
                           with
                             _ -> List.assoc loc prob.locs in
  let _ = List.iter (fun loc ->
            let imp_trans = List.filter (fun (f,t,_,_,_,_) ->
                              f = loc || t = loc
                            ) prob.mats in
            let imp_selfs = List.filter (fun (_,_,_,_,_,info) ->
                              let (f,_,_,_,_) = info in f = loc
                            ) prob.self in
            let used_locs = List.fold_left (fun s (f,t,_,_,_,_) ->
                              LocSet.add f (LocSet.add t s)
                            ) (LocSet.singleton loc) (imp_trans @ imp_selfs) in
            let focused_prob = {name  = prob.name;
                                vars  = prob.vars;
                                locs  = List.fold_left (fun xs (l,_) ->
                                          if LocSet.mem l used_locs then
                                            (l, lookup_inv inv_tbl l)::xs
                                          else
                                            xs
                                        ) [] prob.locs;
                                mats  = imp_trans;
                                self  = imp_selfs;
                                trans = prob.trans;
                                invs = prob.invs;
                                info  = prob.info} in

            let _ = print_endline "=====  Making a focused round  =========" in
            let tmp_inv_tbl = call_trs focused_prob dType
            in
              Hashtbl.add inv_tbl loc (Hashtbl.find tmp_inv_tbl loc)
          ) prob.info.visit_order in
  let upd_prob = update_selfloops prob inv_tbl in
  let _ = upd_prob.invs <- inv_tbl in
  (* Updates location guards if necessary *)
  let upd_locs = if prob.info.updLocs then
                   List.map (fun (loc, grd) ->
                     (loc, Hashtbl.find inv_tbl loc)
                   ) prob.locs
                 else
                   prob.locs in
  let _ = upd_prob.locs <- upd_locs
  (* Updates location guards if necessary *)
  in
    upd_prob
  
  

let make_round (prob:num_problem_t) (dType:domain_t) : num_problem_t =
  let _       = incr iterations in
  let inv_tbl = call_trs prob dType in
  let _       = Debug.infoMsg (fun _ ->
                                "First invariant table: \n" ^ (inv_table_to_str inv_tbl) ^ "\n") in
  let _       = print_endline "Invariants generated..." in
  (* call project_local over all the found *)
  let prjProblem  = update_selfloops prob inv_tbl in
  let _ = prjProblem.invs <- inv_tbl in
  (* Updates location guards if necessary *)
  let upd_locs = if prob.info.updLocs then
                   List.map (fun (loc, grd) ->
                     (loc, Hashtbl.find inv_tbl loc)
                   ) prob.locs
                 else
                   prob.locs in
  let _ = prjProblem.locs <- upd_locs
  (* Updates location guards if necessary *)
  in
    prjProblem




let compare_tables (invs:inv_table_t) (invs':inv_table_t) : bool =
  let invs_list = Hashtbl.fold (fun k v l -> (k,v)::l) invs [] in
  let check_one (loc,exp) =
    let exp' = Hashtbl.find invs' loc in
    let int_exp  = NumExp.formula_to_int_formula exp in
    let int_exp' = NumExp.formula_to_int_formula exp' in
    let _ = if not (NumExp.formula_is_linear int_exp) then
      Printf.printf "NOT_LINEAR: %s\n" (NumExp.formula_to_string int_exp) in
    let _ = if not (NumExp.formula_is_linear int_exp') then
      Printf.printf "NOT_LINEAR: %s\n" (NumExp.formula_to_string int_exp') in
(*    Printf.printf "%s\n<=\n%s" (Expr.formula_to_str exp)
                                 (Expr.formula_to_str exp'); *)
      NumSolver.compare_formulas exp exp'
  in
    List.for_all check_one invs_list



let stop (invs:inv_table_t option) (invs':inv_table_t) : bool =
  match invs with
    None -> false
  | Some(pre) -> let _ = Debug.print_invTables (inv_table_to_str pre)
                                               (inv_table_to_str invs')
                 in
                   compare_tables pre invs'


let iterate (prob:num_problem_t) (dType:domain_t) : inv_table_t option =
  let debug_original p = Debug.infoMsg (fun _ -> "BEGIN ORIGINAL==================\n" ^
                                                 (num_problem_to_str p) ^ "\n" ^
                                                 "END ORIGINAL ===================\n") in
  let debug_prob p i = Debug.infoMsg (fun _ -> "=================================\n" ^
                                                (num_problem_to_str p) ^ "\n" ^
                                                "---------------------------------\n" ^
                                                (inv_table_to_str i) ^ "\n" ^
                                                "=================================\n") in
  let rec find_invs inv prob =
    let prob' = match prob.info.tactic with
                  Some Split -> make_round_split prob dType
                | Some Focus -> make_round_focus prob dType
                | None       -> make_round prob dType in
    let inv' = prob'.invs
    in
      if (prob.info.absIntMode = Eager  ||
          prob.info.absIntMode = Interf ||
          prob.info.absIntMode = EagerPlus ) then
        Some inv'
      else
        (* FOR DEBUG ONLY. OUTPUTS INTERMEDIATE INVARIANTS TO CHECK WITH SPECS *)
        let spec_str = invs_for_spec inv' in
        let spec_out = open_out ("tmpinv_" ^ string_of_int !tmpCounter) in
        let _ = incr tmpCounter in
        let _ = output_string spec_out spec_str in
        let _ = close_out spec_out in
        (* FOR DEBUG ONLY. OUTPUTS INTERMEDIATE INVARIANTS TO CHECK WITH SPECS *)

        let use_widening = !wait_for_widening = 1 in
        let _ = if !wait_for_widening > 1 then
                  wait_for_widening := !wait_for_widening - 1 in
        let new_inv =
          if use_widening then
            match inv with
              None   -> Interface.Err.msg "Invariant information expected"
                         "When applying widening, information about previous \
                          invariants is expected, and no information could be \
                          found.";
                        raise(No_invariant_info)
            | Some i -> let _ = print_endline "Using widening..." in
                        let _ = widening_steps := !widening_steps + 1 in
                          gen_widening_for_invs i inv'
          else
            let _ = print_endline
                      (sprintf "No widening. Will start in %i steps..."
                        !wait_for_widening) in
              inv'
        in

        if stop inv new_inv then
            inv
        else
          let _ = debug_prob prob' new_inv in
            find_invs (Some new_inv) prob'
  in
    (* Main body *)
    let _ = debug_original prob in
      find_invs None prob




