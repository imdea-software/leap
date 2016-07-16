
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

module E = Expression
module Stm  = Statement
module GenSet = LeapGenericSet


(* Type declaration *)
type seq_or_conc_t = Sequential | Concurrent

type sys_var_info_t =
    E.sort *
    E.initVal_t option *
    E.V.shared_or_local *
    E.var_nature

type var_table_t = (E.V.id, sys_var_info_t) Hashtbl.t

type proc_info_t = {sort : E.sort option;
                    inputVars : var_table_t;
                    localVars : var_table_t;
                    args : (string * E.sort) list;
                    fLine : E.pc_t; (* ALE: Check if it is set somewhere? *)
                    lLine : E.pc_t;
                    prog : Stm.statement_t option
                   }

and proc_table_t = (string, proc_info_t) Hashtbl.t


(* ALE: Check if this is absolutely required. *)
type tran_table_t = (int, E.formula list) Hashtbl.t 


type st_table_t = (E.pc_t, (string * Stm.statement_t)) Hashtbl.t


type label_table_t = (string, E.pc_t * E.pc_t) Hashtbl.t


type t =
  {
    globalVars : var_table_t ;         (* global variables       *)
    assumptions : Stm.boolean option ; (* the initial assumption *)
    procedures : proc_table_t ;        (* procedures             *)
    transitions : tran_table_t ;       (* transition relations   *)
    fair : E.pc_t list ;               (* fair transitions       *)
    statements : st_table_t ;          (* system statements      *)
    labels : label_table_t ;           (* program line labels    *)
  }


type sysMode =
  | SClosed of int
  | SOpenArray of E.tid list


type abstraction =
  | NoAbstraction
  | Counting



(* Exceptions *)
exception Duplicated_var of E.V.id * E.sort * E.sort
exception Duplicated_procedure of string
exception Unknown_procedure of string
exception Undefined_variable of E.V.id
exception Not_position of E.pc_t
exception Duplicated_label of string * E.pc_t * E.pc_t * E.pc_t
exception Undefined_label of string * E.pc_t
exception Invalid_argument
exception Impossible_call of string
exception No_numeric_variable of E.V.id * E.sort


(* Configuration *)
let initVarNum       : int    = 40
let initProcNum      : int    = 10
let initTranNum      : int    = 200
let initLabelNum     : int    = 20
let defMainProcedure : string = "main"
let me_tid           : string = "me"
let me_tid_var       : E.V.t = E.build_var me_tid E.Tid
                                         false E.V.Shared
                                         E.V.GlobalScope
let me_tid_th        : E.tid = E.VarTh me_tid_var


let empty_var_table () = Hashtbl.create 1

let empty_system () =
  {
    globalVars = Hashtbl.create 1;
    assumptions = None;
    procedures = Hashtbl.create 1;
    transitions = Hashtbl.create 1;
    fair = [];
    statements = Hashtbl.create 1;
    labels = Hashtbl.create 1;
  }
                    

(* TABLE OF VARIABLES FUNCTIONS *)
let var_info_sort (info:sys_var_info_t) : E.sort =
  let (s,_,_,_) = info in s

let var_info_expr (info:sys_var_info_t) : E.initVal_t option =
  let (_,e,_,_) = info in e

let var_info_shared_or_local (info:sys_var_info_t) : E.V.shared_or_local =
  let (_,_,th,_) = info in th

let var_info_nature (info:sys_var_info_t) : E.var_nature =
  let (_,_,_,nat) = info in nat


let new_var_table : var_table_t =
  Hashtbl.create initVarNum


let copy_var_table (table:var_table_t) : var_table_t =
  Hashtbl.copy table


let join_var_table (dst:var_table_t) (src:var_table_t) : unit =
  Hashtbl.iter (Hashtbl.replace dst) src


let add_var (table:var_table_t)
            (v:E.V.id)
            (s:E.sort)
            (e:E.initVal_t option)
            (t:E.V.shared_or_local)
            (k:E.var_nature) : unit =
  if Hashtbl.mem table v then
    begin
      let prevSort = var_info_sort (Hashtbl.find table v) in
      Interface.Err.msg "Variable already defined" $
        sprintf "Variable \"%s\" of sort %s has already been defined \
                 previously with sort %s." v (E.sort_to_str s)
                                             (E.sort_to_str prevSort);
      raise(Duplicated_var(v, s, prevSort))
    end
  else
    Hashtbl.replace table v (s,e,t,k)


let del_var (table:var_table_t) (v:E.V.id) : var_table_t =
  Hashtbl.remove table v; table


let mem_var (table:var_table_t) (v:E.V.id) : bool =
  Hashtbl.mem table v


let find_var_type (table:var_table_t) (v:E.V.id) : E.sort =
  var_info_sort (Hashtbl.find table v)


let find_var_expr (table:var_table_t) (v:E.V.id) : E.initVal_t option =
  var_info_expr (Hashtbl.find table v)


let find_var_tid (table:var_table_t) (v:E.V.id) : E.V.shared_or_local =
  var_info_shared_or_local (Hashtbl.find table v)


let find_var_kind (table:var_table_t) (v:E.V.id) : E.var_nature =
  var_info_nature (Hashtbl.find table v)


let get_var_id_list (table:var_table_t) : E.V.id list =
  let res = Hashtbl.fold (fun var _ xs -> var :: xs) table []
  in
    res


let get_variable_list (table:var_table_t) : E.V.t list =
  let res = Hashtbl.fold (fun var info xs ->
              let s  = var_info_sort info in
              let th = var_info_shared_or_local info
              in
                (E.build_var var s false th E.V.GlobalScope) :: xs
            ) table []
  in
    res


let get_var_list (table:var_table_t) (p:string option) : E.V.t list =
  let res = Hashtbl.fold (fun var info xs ->
              let s = var_info_sort info in
              let scope = match p with
                          | None -> E.V.GlobalScope
                          | Some proc -> E.V.Scope proc in
                (E.build_var var s false E.V.Shared scope) :: xs
            ) table []
  in
    res


let get_var_list_of_sort (table:var_table_t)
                         (s:E.sort)
                         (p:string option) : E.V.t list =
  let res = Hashtbl.fold (fun var info xs ->
              let v_s = var_info_sort info in
              let scope = match p with
                          | None -> E.V.GlobalScope
                          | Some proc -> E.V.Scope proc in
                if s = v_s then
                  (E.build_var var v_s false E.V.Shared scope) :: xs
                else
                  xs
            ) table []
  in
    res 


let clear_table (table:var_table_t) : unit =
  Hashtbl.clear table


let filter_table (table:var_table_t) (vars:E.V.id list) : unit =
  List.iter (Hashtbl.remove table) vars


let num_of_vars (table:var_table_t) : int =
  Hashtbl.length table


let undeftids_in_formula_decl (ts:E.V.id list) (invVars:var_table_t) :unit =
  List.iter (fun id ->
    if not (mem_var invVars id) then
      begin
        Interface.Err.msg "Undefined variable" $
          sprintf "Variable %s was used in the program and assumed to be a \
                   parameter of the formula to be verified. However, such \
                   variable is not declared as a formula parameter." id;
        raise(Undefined_variable id)
      end
    ) ts



(* LABEL TABLE FUNCTIONS *)
let new_label_table : label_table_t =
  Hashtbl.create initLabelNum


let copy_label_table (table:label_table_t) : label_table_t =
  Hashtbl.copy table


let check_undefined_label (tbl:label_table_t) (l:string) (p:E.pc_t) : unit =
  if (Hashtbl.mem tbl l) then
    begin
    let (init_pos, end_pos) = Hashtbl.find tbl l
    in
      Interface.Err.msg "Duplicated label" $
        sprintf "Trying to label line %i with tag \"%s\", but this tag has \
                 already been used to label lines between %i and %i"
          p l init_pos end_pos;
      raise(Duplicated_label(l, p, init_pos, end_pos))
    end


let check_defined_label (tbl:label_table_t) (l:string) (p:E.pc_t) : unit =
  if not (Hashtbl.mem tbl l) then
    begin
      Interface.Err.msg "Undefined label" $
        sprintf "Trying to close label \"%s\" at line %i, but no opening \
                 tag for this label was found." l p;
      raise(Undefined_label(l, p))
    end


let add_single_label (tbl:label_table_t) (l:string) (p:E.pc_t) : unit =
  let _ = check_undefined_label tbl l p in
    Hashtbl.replace tbl l (p,p)


let add_open_label (tbl:label_table_t) (l:string) (p:E.pc_t) : unit =
  let _ = check_undefined_label tbl l p in
    Hashtbl.replace tbl l (p,p)


let add_close_label (tbl:label_table_t) (l:string) (p:E.pc_t) : unit =
  let _ = check_defined_label tbl l p in
  let (pc_init,_) = Hashtbl.find tbl l in
  let _ = assert (pc_init >= 0) in
    Hashtbl.replace tbl l (pc_init, p)


let get_label_pos (tbl:label_table_t) (l:string) : (E.pc_t * E.pc_t) option =
  try
    Some (Hashtbl.find tbl l)
  with _ -> None


let get_labels_list (tbl:label_table_t) : string list =
  let label_list = Hashtbl.fold (fun s _ xs ->
                     s::xs
                   ) tbl []
  in
    label_list


let get_labels_for_pos (tbl:label_table_t) (pc:E.pc_t) : string list =
  let label_list = Hashtbl.fold (fun l (init_pos, end_pos) xs ->
                     if init_pos <= pc && pc <= end_pos then
                       l::xs
                     else
                       xs
                   ) tbl []
  in
    label_list


let lines (sys:t) : int =
  Hashtbl.length sys.statements
  

(* SYSTEM MANIPULATION FUNCTIONS *)
let new_system (gVars:var_table_t)
               (assume:Stm.boolean option)
               (procs:proc_table_t)
               (trans:tran_table_t)
               (fair:int list)
               (st_table:st_table_t)
               (lt:label_table_t) : t =
  {
    globalVars = gVars ;
    assumptions = assume ;
    procedures = procs ;
    transitions = trans ;
    fair = fair ;
    statements = st_table ;
    labels = lt ;
  }


let get_global     (s:t) : var_table_t = s.globalVars
let get_assume     (s:t) : Stm.boolean option = s.assumptions
let get_procs      (s:t) : proc_table_t = s.procedures
let get_trans      (s:t) : tran_table_t = s.transitions
let get_fair       (s:t) : int list = s.fair
let get_statements (s:t) : st_table_t = s.statements
let get_labels     (s:t) : label_table_t = s.labels


let is_proc (sys:t) (p_name:string) : bool =
  let proc_tbl = get_procs sys in
    Hashtbl.mem proc_tbl p_name


let get_proc_by_name (sys:t) (p_name:string) : proc_info_t =
  let tbl = get_procs sys in
  if Hashtbl.mem tbl p_name then
    Hashtbl.find tbl p_name
  else
    begin
      Interface.Err.msg "Process name not found" $
              sprintf "A process with name %s could not be found" p_name;
      raise(Unknown_procedure p_name)
    end


let get_input_by_name (sys:t) (p_name:string) : var_table_t =
  let info = get_proc_by_name sys p_name in info.inputVars


let get_local_by_name (sys:t) (p_name:string) : var_table_t =
  let info = get_proc_by_name sys p_name in info.localVars


let get_fLine_by_name (sys:t) (p_name:string) : E.pc_t =
  let info = get_proc_by_name sys p_name in info.fLine


let get_lLine_by_name (sys:t) (p_name:string) : E.pc_t =
  let info = get_proc_by_name sys p_name in info.lLine


let get_prog_by_name (sys:t) (p_name:string) : Stm.statement_t option =
  let info = get_proc_by_name sys p_name in info.prog


let get_proc_init_vals (sys:t) (p_name:string) : (E.V.t * E.initVal_t) list =
  Hashtbl.fold (fun v_id (s,val_opt,sh,k) xs ->
    match val_opt with
    | Some value -> (E.build_var v_id s false sh (E.V.Scope p_name) ~nature:k, value)::xs
    | None       -> xs
  ) (get_local_by_name sys p_name) []


let proc_sort_func (sys:t) (p1:string) (p2:string) : int =
  let p1_init = get_fLine_by_name sys p1 in
  let p2_init = get_fLine_by_name sys p2 in
    p1_init - p2_init


let get_proc_name_list (sys:t) (sorted:bool) : string list =
  let proc_tbl = get_procs sys in
  let res : string list ref = ref [] in
  let _ = Hashtbl.iter (fun name _ -> res := name :: !res) proc_tbl in
    if sorted then
      List.fast_sort (proc_sort_func sys) !res
    else
      !res


let get_all_local_vars (sys:t) : (string * E.V.t list) list =
  let procs = get_proc_name_list sys false
  in
    List.map (fun p ->
      let vTable = get_local_by_name sys p in
      let vList = get_var_list vTable (Some p)
      in
        (p, vList)
    ) procs


let get_statement_at (sys:t) (pos:E.pc_t) : (string*Stm.statement_t) =
  let tbl = get_statements sys in
  try
    Hashtbl.find tbl pos
  with
    Not_found -> Interface.Err.msg "Not a system position" $
                         sprintf "Position %i does not corresponds to a \
                                  valid statement position within the \
                                  declared system." pos;
    raise(Not_position pos)


let get_trans_num (sys:t) : int =
  let tbl = get_statements sys in
  Hashtbl.length tbl


let add_global_vars (sys:t) (tbl:var_table_t) : t =
  join_var_table sys.globalVars tbl; sys


let del_global_var (sys:t) (id:E.V.id) : t =
  ignore (del_var sys.globalVars id); sys


let del_global_var_regexp (sys:t) (expr:Str.regexp) : t =
  let _ = Hashtbl.iter (fun id _ ->
            if (Str.string_match expr id 0) then
              Hashtbl.remove sys.globalVars id
          ) sys.globalVars
  in
    sys


(* SYSTEM QUERY FUNCTIONS *)
let get_accvars_by_name (sys:t)
                        (p_name:string) : (var_table_t * var_table_t) =
  let gVars = get_global sys in
  let iVars = get_input_by_name sys p_name in
  let lVars = get_local_by_name sys p_name in
  let gTbl  = Hashtbl.copy gVars in
  let lTbl  = Hashtbl.copy iVars in
  let _     = List.iter (Hashtbl.remove gTbl) (get_var_id_list lTbl) in
  let _     = Hashtbl.iter (Hashtbl.replace lTbl) lVars
  in
    (gTbl, lTbl)


(* All global and local variables accessible by each thread *)
(* Notice that not all global variables may appear fr each process,
   as they may be shadowed by a local variable. *)
let get_accvars (sys:t) : (string * var_table_t * var_table_t) list =
  let proc_names = get_proc_name_list sys false in
  let proc_vars  = List.map (fun p ->
                              let accVars = get_accvars_by_name sys p in
                                (p, fst accVars, snd accVars)) proc_names
  in
    proc_vars


let get_all_vars_id (sys:t) : E.V.id list =
  let gv_tbl = get_global sys in
  let lv_lst = get_accvars sys in
  let gv = Hashtbl.fold (fun v _ l -> v::l) gv_tbl [] in
  let lv = List.map (fun (p,_,lt) ->
             Hashtbl.fold (fun v _ xs ->
               (E.V.localize_var_id v p)::xs
             ) lt []
           ) lv_lst
  in
    gv @ (List.flatten lv)


let get_sys_var_tables (sys:t)
                          : var_table_t *
                            (string * var_table_t * var_table_t) list =
  let proc_list = get_proc_name_list sys false in
  let gTbl = get_global sys in
  let iTbl = Hashtbl.create 20 in
  let lTbl = Hashtbl.create 20 in
  let _ = List.iter (fun p ->
            let input_vars = get_input_by_name sys p in
            let local_vars = get_local_by_name sys p in
              Hashtbl.add iTbl p input_vars;
              Hashtbl.add lTbl p local_vars;
          ) proc_list in
  let full_list = List.fold_left (fun xs p ->
                    (p, Hashtbl.find iTbl p, Hashtbl.find lTbl p)::xs
                  ) [] proc_list
  in
    (gTbl, full_list)


let get_vars_of_sort (sys:t) (s:E.sort) : E.V.t list =
  let process (set:E.V.t GenSet.t) (p:E.V.procedure_name)
              (id:E.V.id) ((s',th,k):(E.sort * E.V.shared_or_local * E.var_nature))
    : unit =
      if s' = s then
        GenSet.add set (E.build_var id s' false th p ~nature:k) in
  let (gTbl, lTbls) = get_sys_var_tables sys in
  let set = GenSet.empty() in

  Hashtbl.iter (fun id (s',_,th,k) -> process set E.V.GlobalScope id (s',th,k)) gTbl;
  List.iter (fun (p,iTbl,lTbl) ->
    Hashtbl.iter (fun id (s',_,th,k) -> process set (E.V.Scope p) id (s',th,k)) iTbl;
    Hashtbl.iter (fun id (s',_,th,k) -> process set (E.V.Scope p) id (s',th,k)) lTbl
  ) lTbls;
  GenSet.to_list set



(* SYSTEM EXTRA FUNCTIONS *)
let get_sort_from_variable (gVars:var_table_t)
                           (iVars:var_table_t)
                           (lVars:var_table_t)
                           (auxVars:var_table_t)
                           (v:E.V.id) : E.sort =
  if mem_var gVars v then
    find_var_type gVars v
  else if mem_var iVars v then
    find_var_type iVars v
  else if mem_var lVars v then
    find_var_type lVars v
  else if mem_var auxVars v then
    find_var_type auxVars v
  else
    E.Tid
    (* ALE: We are just assuming that undefined variables are used to identify threads *)


let get_sort_from_term (gVars:var_table_t)
                       (iVars:var_table_t)
                       (lVars:var_table_t)
                       (auxVars:var_table_t)
                       (t:E.term) : E.sort =
  match t with
    E.SetT(_)           -> E.Set
  | E.VarT v            -> get_sort_from_variable gVars iVars lVars auxVars (E.V.id v)
                            (* ALE: Should it be just s? *)
  | E.ElemT(_)          -> E.Elem
  | E.TidT(_)           -> E.Tid
  | E.AddrT(_)          -> E.Addr
  | E.CellT(_)          -> E.Cell
  | E.SetThT(_)         -> E.SetTh
  | E.SetIntT(_)        -> E.SetInt
  | E.SetElemT(_)       -> E.SetElem
  | E.SetPairT(_)       -> E.SetPair
  | E.PathT(_)          -> E.Path
  | E.MemT(_)           -> E.Mem
  | E.IntT(_)           -> E.Int
  | E.PairT(_)          -> E.Pair
  | E.ArrayT(_)         -> E.Array
  | E.AddrArrayT(_)     -> E.AddrArray
  | E.TidArrayT(_)      -> E.TidArray
  | E.BucketArrayT(_)   -> E.BucketArray
  | E.MarkT(_)          -> E.Mark
  | E.BucketT(_)        -> E.Bucket
  | E.LockT(_)          -> E.Lock
  | E.LockArrayT(_)     -> E.LockArray



(* PROCEDURE INFORMATION FUNCTIONS *)
let new_proc_info (s:E.sort option)
                  (input : var_table_t)
                  (local : var_table_t)
                  (args : (E.V.id * E.sort) list)
                  (fLine : E.pc_t)
                  (lLine : E.pc_t)
                  (prog : Stm.statement_t option)
                  : proc_info_t =
  { sort = s;
    inputVars = input;
    localVars = local;
    args = args;
    fLine = fLine;
    lLine = lLine;
    prog = prog }

let proc_info_get_sort (info:proc_info_t) : E.sort option =
  info.sort


let proc_info_get_input (info:proc_info_t) : var_table_t =
  info.inputVars


let proc_info_get_local (info:proc_info_t) : var_table_t =
  info.localVars


let proc_init_line (info:proc_info_t) : E.pc_t =
  info.fLine


let proc_last_line (info:proc_info_t) : E.pc_t =
  info.lLine


let proc_info_get_args (info:proc_info_t) : (E.V.id * E.sort) list =
  info.args


let proc_info_get_args_sig (info:proc_info_t) : E.sort list =
  List.map snd info.args


(* PROCEDURE TABLE FUNCTIONS *)
let new_proc_table_from_list (xs:(string * proc_info_t) list):proc_table_t =
  let tbl = Hashtbl.create initProcNum in
  let _ = List.iter (fun (n,i) ->
            if Hashtbl.mem tbl n then
              begin
                Interface.Err.msg "Procedure already defined" $
                        sprintf "A procedure with name \"%s\"has already been \
                                 defined" n;
                raise(Duplicated_procedure n)
              end
            else
              Hashtbl.replace tbl n i;
          ) xs
  in
    tbl

let proc_table_vars_to_str (pt:proc_table_t) : string =
  let str = Hashtbl.fold (fun p info str ->
              let input_vars = proc_info_get_input info in
              let local_vars = proc_info_get_local info in
              let input_str  = Hashtbl.fold (fun id _ xs -> id::xs)
                                            input_vars [] in
              let local_str  = Hashtbl.fold (fun id _ xs -> id::xs)
                                            local_vars [] in
              (String.concat ", " $ List.map (fun id -> p^"::"^id)
                                              (input_str@local_str)) ^"\n"^ str
            ) pt ""
  in
    str



(* GENERATION FUNCTIONS *)
(** Generates the list of global variables for a system, but described as terms 
    instead of variable identifiers.
    @param sys the system where variables are extracted from
    @return the list of global variables in sys represented as terms *)
let gen_global_vars_as_terms (sys:t) : E.TermSet.t =
  let gTbl = get_global sys in
  let gVars = ref E.TermSet.empty in
  let _ = Hashtbl.iter (fun id info ->
            let (s,_,th,nat) = info in
            let v = E.build_var id s false th E.V.GlobalScope ~nature:nat in
            gVars := E.TermSet.add (E.var_to_term v) !gVars
          ) gTbl
  in
    !gVars


(** Generates the list of local variables for a system, but described as
    terms instead of variable identifiers.
    @param sys the system where variables are extracted from
    @return a list of pairs made by the process name and its local variables *)
let gen_local_vars_as_terms (sys:t) : (string * E.TermSet.t) list =
  let vInfo   = get_accvars sys in
  let lVars   = ref E.TermSet.empty in
  let resVars = ref [] in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun id info ->
              let (s,_,_,nat) = info in
              let v = E.build_var id s false E.V.Shared (E.V.Scope p) ~nature:nat in
              lVars := E.TermSet.add (E.var_to_term v) !lVars
            )l;
            resVars := (p, !lVars):: !resVars;
            lVars := E.TermSet.empty) vInfo
  in
    !resVars


let gen_local_vars_as_array_terms (sys:t)
                                    : (string * E.TermSet.t) list =
  let vInfo   = get_accvars sys in
  let lVars   = ref E.TermSet.empty in
  let resVars = ref [] in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v info ->
              let k   = var_info_nature info in
              let s   = var_info_sort info in
              let var = E.build_var v s false E.V.Shared (E.V.Scope p) ~nature:k in
              lVars   := E.TermSet.add (E.ArrayT
                           (E.VarArray var)
                         ) !lVars) l;
            resVars := (p, !lVars) :: !resVars;
            lVars   := E.TermSet.empty) vInfo
  in
    !resVars



(* TRANSITION TABLE FUNCTIONS *)
let new_tran_table : tran_table_t =
  Hashtbl.create initTranNum


let add_trans (tbl:tran_table_t)
              (pos:E.pc_t)
              (form:E.formula list) : unit =
  Hashtbl.replace tbl pos form


let get_tran (tbl:tran_table_t) (pos:E.pc_t) : E.formula list =
  try
    Hashtbl.find tbl pos
  with _ -> []


let tran_table_to_str (tt:tran_table_t) : string =
  let str = Hashtbl.fold (fun pc fs str ->
              (sprintf "Line %i:\n%s" pc
                  (String.concat "\n" $ List.map E.formula_to_str fs))^
              "\n" ^ str
            ) tt ""
  in
    str




(* NUMERIC SYSTEM FUNCTIONS *)
let check_is_numeric (sys:t) : unit =
  let check_numeric (id:E.V.id) (info:sys_var_info_t) : unit =
    let s = var_info_sort info in
    match s with
    | E.Int  -> ()
    (* ALE: We allow tid, provided we interpret them as integer later. *)
    | E.Tid -> ()
    | _   -> Interface.Err.msg "Non-numeric variable" $
               sprintf "Variables are expected to be numeric, but variable \
                        %s has sort %s."
                        (id)
                        (E.sort_to_str s);
             raise(No_numeric_variable(id,s)) in
  let gv_tbl = get_global sys in
  let lv_list = get_accvars sys in

  let _ = Hashtbl.iter check_numeric gv_tbl in
  let _ = List.iter (fun (p,_,lt) ->
            Hashtbl.iter (fun v info ->
              check_numeric (E.V.localize_var_id v p) info
            ) lt
          ) lv_list
  in
    ()


  let filter_me_tid (ts:E.ThreadSet.t) : E.ThreadSet.t =
    E.ThreadSet.remove me_tid_th ts


(* PRINTING FUNCTIONS *)
let var_table_to_str (tbl:var_table_t) : string =
  let decl_to_str v info =
    let s     = var_info_sort info in
    let e     = var_info_expr info in
    let k     = var_info_nature info in
    let k_str = match k with
                | E.RealVar -> ""
                | E.GhostVar -> "ghost " in
    let s_str = E.sort_to_str s
    in
      match e with
        Some (E.Equality t)  -> sprintf "\t%s%s %s := %s" k_str s_str v
                                                          (E.term_to_str t)
      | Some (E.Condition c) -> sprintf "\t%s%s %s" k_str s_str
                                                       (E.formula_to_str c)
      | None                    -> sprintf "\t%s%s %s" k_str s_str v
  in
  let tbl_str = String.concat "\n" $ Hashtbl.fold (fun v info xs ->
                                      (decl_to_str v info)::xs) tbl [] in
tbl_str


let procedure_to_str (sys:t) (p_name:string) : string =
  let proc_arg      = get_input_by_name sys p_name in
  let proc_local    = get_local_by_name sys p_name in
  let proc_prog     = get_prog_by_name sys p_name in

  let arg_str       = String.concat ", " $
                     Hashtbl.fold (fun v info xs ->
                       let s = var_info_sort info in
                         (sprintf "%s:%s" v (E.sort_to_str s))::xs
                                  ) proc_arg [] in
  let local_str     = var_table_to_str proc_local in
  let statement_str = Option.map_default (Stm.statement_to_str 1)
                                          "" proc_prog
  in
    sprintf "Procedure %s (%s) \n\
              %s \n\
              begin \n\
              %s\
              end"
              p_name arg_str local_str statement_str


let to_str (sys:t) : string =
  let assume        = match get_assume sys with
                        None -> ""
                      | Some f -> sprintf "assume\n\t%s\n\n"
                                    (Stm.boolean_to_str f) in
  let global_tbl    = get_global sys in
  let global_str    = var_table_to_str global_tbl in
  let proc_list     = get_proc_name_list sys true in
  let proc_list_str = String.concat "\n\n" $
                          List.map (procedure_to_str sys) (proc_list)
  in
    sprintf "Global\n\
              %s\n\n\
              %s\
              %s\n\n"
            global_str assume proc_list_str


(*********************************************************)
(*       TRANSITION RELATION GENERATION                  *)
(*********************************************************)



(* Program counter *)
let build_curr_pc (th : E.tid) (p : E.pc_t) : E.formula =
  E.pc_form p (E.V.Local (E.voc_to_var th)) false


let build_next_pc (mode : sysMode)
                  (th : E.tid)
                  (next_list : E.pc_t list) : E.formula =
  match next_list with
  | [] -> Formula.True
  | _ -> begin
           assert (List.length next_list > 0);
           let fst_next_pos = List.hd next_list in
           let build_eq' i = match mode with
                             | SClosed _ -> E.pcupd_form i th
                             | SOpenArray _ -> E.pcupd_form i th in
           let fst_eq = build_eq' fst_next_pos in
           let next_eq = List.fold_left (fun b p ->
                           Formula.Or (build_eq' p,b)
                         ) (fst_eq) (List.tl next_list)
           in
             next_eq
         end


let build_pres_pc (mode : sysMode)
                  (th_list : E.tid list) : E.formula list =
  match mode with
  | SClosed _ -> (* Deprecated *)
      let pc = E.VarArray
        (E.build_var Conf.pc_name E.Unknown false E.V.Shared E.V.GlobalScope) in
      let pc' = E.VarArray
        (E.build_var Conf.pc_name E.Unknown false E.V.Shared E.V.GlobalScope) in
      let pc_arr arr id  = E.IntArrayRd(arr,id) in
      let eq_list = List.map 
        (fun i -> E.eq_int (pc_arr pc' i) (pc_arr pc i)) th_list in
      eq_list
  | SOpenArray _ -> []


let build_pc (mode : sysMode)
             (curr_th:E.tid)
             (now : E.pc_t)
             (next_list : E.pc_t list) : E.formula list =
  let other_ths =
    match mode with
    | SClosed m -> E.gen_tid_list_except 1 m curr_th
    | SOpenArray js -> List.filter (fun t -> t <> curr_th) js in
  let curr_eq = build_curr_pc curr_th now in
  let next_eq = build_next_pc mode curr_th next_list in
  let pres_eq = build_pres_pc mode other_ths in
  curr_eq :: next_eq :: pres_eq



(* Initial condition *)

let gen_global_init_cond (sys : t) : E.formula list =
  let gVars = get_global sys in
  let conds = Hashtbl.fold (fun id info xs ->
                let (s,init,th,nat) = info in
                let v = E.build_var id s false th E.V.GlobalScope ~nature:nat in
                (E.assign_var v init) @ xs
              ) gVars [] in
  conds

let gen_local_init_cond (sys : t) 
    (p_name : string) : E.formula list =
  let _, lVars = get_accvars_by_name sys p_name in
  let conds = Hashtbl.fold
    (fun id info xs ->
      let (s,init,_,nat) = info in
      let v = E.build_var id s false E.V.Shared (E.V.Scope p_name) ~nature:nat in
      (E.assign_var v init) @ xs
    ) lVars [] in
  conds

let gen_init_cond (sys : t) (p_name : string) (th_list : E.tid list) : E.formula =
  let gConds = gen_global_init_cond sys in
  let lConds = gen_local_init_cond sys p_name in
  let full_lConds = match th_list with
    |  [] -> lConds
    | _  -> List.flatten $ List.map 
      (fun t -> let me_subst = E.new_tid_subst [(me_tid_th,t)]in
        List.map (fun c -> E.subst_tid me_subst (E.param (E.V.Local (E.voc_to_var t)) c)) lConds)
      th_list in 
  Formula.conj_list (gConds @ full_lConds)


let gen_theta_classic (mode : sysMode)
                      (sys : t) : E.formula =
  let main_proc = defMainProcedure in
  let param_list = match mode with
    | SClosed m -> E.gen_tid_list 1 m
    | SOpenArray xs -> xs in
  let main_fLine = get_fLine_by_name sys main_proc in
  let init_line = Pervasives.max 1 main_fLine in
  let init_pc_list = List.map (fun i->build_curr_pc i init_line) param_list in
  let init_pc_cond = Formula.conj_list init_pc_list in
  let prog_cond = gen_init_cond sys main_proc param_list in
  let init_sys_cond = match get_assume sys with
    | None   -> prog_cond
    | Some c -> Formula.And(Stm.boolean_to_expr_formula c, prog_cond) in
  Formula.And (init_pc_cond, init_sys_cond)


let gen_theta_with_count_abs (mode:sysMode)
                             (sys:t) : E.formula =
  let theta_cond = gen_theta_classic mode sys in
  let lines = rangeList 1 (get_trans_num sys + 1) in
  let main_fLine = get_fLine_by_name sys (defMainProcedure) in
  let full_cond = List.fold_left 
    (fun phi i -> if i = main_fLine then
        Formula.And (E.eq_int (E.VarInt (E.countAbs_var i)) E.defCountVar, phi)
      else
        Formula.And (E.eq_int (E.VarInt (E.countAbs_var i)) (E.IntVal 0), phi)) 
    theta_cond lines in
  full_cond


let gen_theta (mode:sysMode)
              (sys:t)
              (abs:abstraction) : E.formula =
  match abs with
  | NoAbstraction  -> gen_theta_classic mode sys
  | Counting -> gen_theta_with_count_abs mode sys

(* Transition relations *)

let gen_pres (p_name : string)
             (gs : E.TermSet.t)
             (ls : E.TermSet.t)
             (os : (string * E.TermSet.t) list)
             (ts : E.TermSet.t)
             (mode : sysMode)
             (th:E.tid) : E.formula list =
  let gTermConj = E.TermSet.fold
    (fun x l -> (E.construct_pres_term x E.V.Shared) :: l) gs [] in
  let lTermConj = match mode with
    | SClosed _ -> E.TermSet.fold
        (fun x l -> (E.construct_pres_term x (E.V.Local (E.voc_to_var th)))::l) ls []
    | SOpenArray _ -> E.TermSet.fold
        (fun x bs -> (E.construct_pres_term x E.V.Shared)::bs) ls [] in
  let oTermConj = match mode with
    | SClosed m ->
        let th_list = E.gen_tid_list 1 m in
        let f p x bs i = if (i<>th || p<>p_name) then
            (E.construct_pres_term x (E.V.Local (E.voc_to_var i)))::bs
          else bs in
        let g p x l =
            List.fold_left (f p x) [] th_list @ l in
        let h (p, ts) =
          E.TermSet.fold (g p) ts [] in
        List.flatten $ List.map h os
    | SOpenArray _ ->
        List.flatten $ List.map
        (fun (_,ts) -> E.TermSet.fold
          (fun x bs -> (E.construct_pres_term x E.V.Shared)::bs) ts []) os in
  let thTermConj =
    E.TermSet.fold (fun x l -> (E.construct_pres_term x E.V.Shared) :: l) ts [] in
  gTermConj @ lTermConj @ oTermConj @ thTermConj

  
let rec aux_rho_for_st
    (sys:t)
    (soc:seq_or_conc_t)
    (gSet:E.TermSet.t) (* Global accessible terms. *)
    (lSet:E.TermSet.t) (* Local accessible terms. *)
    (thSet:E.TermSet.t) (* Extra formula tids. *)
    (mode:sysMode) (* System type. *)
    (st:Stm.statement_t) (* Generate rho for statem. *)
    (th:E.tid) (* Thread taking the transition *)
    (is_ghost:bool) (* Is ghost code? *)
    (abs:abstraction) (* Include counting abstraction? *)
    (mInfo:Bridge.malloc_info)
    (pt:Bridge.prog_type)
    : (E.TermSet.t * E.TermSet.t * E.TermSet.t * E.formula list list) =
  let conv_bool = Stm.boolean_to_expr_formula in
  let th_p = E.V.Local (E.voc_to_var th) in
  let append_to_ghost gc gS lS tS (ps:E.formula list list) =
    match gc with
    | Some code ->
        let eff_list = Bridge.gen_st_cond_effect_as_array pt code true th_p in
        let rho_list = List.fold_left (fun xs (cond, eff, _, _) ->
                         (List.map (fun normal_code ->
                           (E.param th_p cond :: eff :: normal_code)
                          ) ps) @ xs
                       ) [] eff_list in
          (* ALE: Check if preservation works when no -hp is used. *)
        (E.TermSet.empty, E.TermSet.empty, E.TermSet.empty, rho_list)
    | None -> (gS, lS, tS, ps) in
  let make_pos_change (c:int) (ns:int list) : E.formula list =
    let running_tid_is_me = match soc with
                            | Concurrent -> [E.eq_tid me_tid_th th]
                            | Sequential -> [] in
    let pc_change = build_pc mode th c ns in
    let next_pos =
      Formula.disj_list $ List.map (fun n -> E.build_pos_change c n) ns in
    match abs with
    | Counting -> [E.someone_at c; next_pos] @ running_tid_is_me @ pc_change
    | NoAbstraction -> running_tid_is_me @ pc_change in
  match (st, is_ghost) with

  (************************** Skip @topLevel ******************************)
  | Stm.StSkip (g, Some i), false ->
      let pred = make_pos_change i.Stm.pos [i.Stm.next_pos] in
      append_to_ghost g gSet lSet thSet [pred]
   
  (************************* Skip @ghostLevel ****************************)
  | Stm.StSkip _, true -> (gSet, lSet, thSet, [])
  
  (************************* Await @topLevel *****************************)
  | Stm.StAwait (c, g, Some i), false ->
      let c'    = conv_bool c in
      let predT = 
        make_pos_change i.Stm.pos [i.Stm.next_pos] @ [E.param th_p c'] in
      let predF = make_pos_change i.Stm.pos
                    [i.Stm.pos] @ [E.param th_p (Formula.Not c')] in
      append_to_ghost g gSet lSet thSet [predT; predF]
      
  (************************ Await @ghostLevel ****************************)
  (* I must fix this case, to allow await on atomic statements *)
  | Stm.StAwait _, true -> (gSet, lSet, thSet, []) (* ????? *)
  
  (************************ Noncritical @topLevel ************************)
  | Stm.StNonCrit (g, Some i), false ->
      let pred = make_pos_change i.Stm.pos [i.Stm.next_pos] in
      append_to_ghost g gSet lSet thSet [pred]
  
  (************************ Noncritical @ghostLevel **********************)
  | Stm.StNonCrit _, true -> (gSet, lSet, thSet, []) (* ????? *)
  
  (************************ Critical @topLevel ***************************)
  | Stm.StCrit (g, Some i), false ->
      let pred = make_pos_change i.Stm.pos [i.Stm.next_pos] in
      append_to_ghost g gSet lSet thSet [pred]
      
  (************************ Critical @ghostLevel *************************)
  | Stm.StCrit _, true -> (gSet, lSet, thSet, []) (* ????? *)
  
  (************************ If @topLevel *********************************)
  | Stm.StIf (c, _, _, g, Some i), false ->
      let c' = conv_bool c in
      let predT = make_pos_change i.Stm.pos [i.Stm.next_pos] @
                  [E.param th_p c'] in
      let predF = make_pos_change i.Stm.pos [i.Stm.else_pos] @
                  [E.param th_p (Formula.Not c')] in
      append_to_ghost g gSet lSet thSet [predT; predF]
  
  (************************ If @ghostLevel *******************************)
  | Stm.StIf (_, _, _, _, _), true -> (gSet, lSet, thSet, []) (* ????? *)
  
  (************************ While @topLevel ******************************)
  | Stm.StWhile (c, _, g, Some i), false ->
      let c' = conv_bool c in
      let predT = 
        make_pos_change i.Stm.pos [i.Stm.next_pos] @ [E.param th_p c'] in
      let predF = make_pos_change i.Stm.pos
                    [i.Stm.else_pos] @ [E.param th_p (Formula.Not c')] in
      append_to_ghost g gSet lSet thSet [predT; predF]
   
  (************************ While @ghostLevel ****************************)
  | Stm.StWhile _, true -> (gSet, lSet, thSet, []) (* ????? *)
    
  (************************ Choice @topLevel *****************************)
  | Stm.StSelect (_, g, Some i),  false ->
      let pred = make_pos_change i.Stm.pos i.Stm.opt_pos in
      append_to_ghost g gSet lSet thSet [pred]
  
  (************************ Choice  @ghostLevel **************************)
  | Stm.StSelect _,  true -> (gSet, lSet, thSet, []) (* ????? *)
  
  (************************ Assignment @anyLevel *************************)
  | Stm.StAssign (v, e, g, info), is_ghost ->
    let (gSet',lSet',thSet',equiv) =
      begin
        match mode with
        | SClosed _ ->
            let modif, equiv = Bridge.construct_stm_term_eq mInfo v th_p e in
            let still_gSet = E.filter_term_set modif gSet in
            let still_lSet = E.filter_term_set modif lSet in
            let still_thSet = E.filter_term_set modif thSet in
            (still_gSet, still_lSet, still_thSet, equiv)
        | SOpenArray _ ->
            let (modif, equiv) = Bridge.construct_stm_term_eq_as_array mInfo v th_p e in
            let still_gSet = E.filter_term_set modif gSet in
            let still_lSet = E.filter_term_set modif lSet in
            let still_thSet = E.filter_term_set modif thSet in
            (still_gSet, still_lSet, still_thSet, equiv)
      end in
    if is_ghost then (gSet', lSet', thSet', [[equiv]])
    else begin
      let _ = assert (info <> None) in
      let pred = match info with
        | Some i -> (make_pos_change i.Stm.pos [i.Stm.next_pos]) @ [equiv]
        | None   -> [] in
      append_to_ghost g gSet' lSet' thSet' [pred]
    end
    
  (************************ Unit @anyLevel *******************************)
  | Stm.StUnit (cmd, g, Some i), is_ghost ->
    let op = Stm.get_unit_op cmd in
    let a = E.param_addr th_p $ Stm.addr_used_in_unit_op cmd in
    let cell = E.CellAt (E.heap, a) in
    let cond = match op with
      | Stm.Lock   -> E.eq_tid (E.CellLockId cell) E.NoTid
      | Stm.Unlock -> E.eq_tid (E.CellLockId cell)
                               (match th_p with
                                | E.V.Shared -> E.NoTid
                                | E.V.Local t -> (E.VarTh t)) in
    let new_tid  = match op with
      | Stm.Lock -> th
      | Stm.Unlock -> E.NoTid in
    let mkcell = E.MkCell (E.CellData (E.CellAt (E.heap, a)),
      E.Next (E.CellAt (E.heap, a)), new_tid) in
    let upd = E.eq_mem (E.prime_mem E.heap) (E.Update (E.heap, a, mkcell)) in
    let modif = [E.MemT E.heap] in
    let (gSet',lSet',thSet') = begin
      match mode with
      | SClosed _ ->
          let still_gSet  = E.filter_term_set (modif) gSet in
          let still_lSet  = E.filter_term_set (modif) lSet in
          let still_thSet = E.filter_term_set (modif) thSet in
            (still_gSet, still_lSet, still_thSet)
      | SOpenArray _ ->
          let still_gSet  = E.filter_term_set (modif) gSet in
          let still_lSet  = E.filter_term_set (modif) lSet in
          let still_thSet = E.filter_term_set (modif) thSet in
            (still_gSet, still_lSet, still_thSet)
    end in
    if is_ghost then (gSet', lSet', thSet', [[cond;upd]])
    else begin
      let pred = 
        (make_pos_change i.Stm.pos [i.Stm.next_pos]) @ [cond;upd] in
      append_to_ghost g gSet' lSet' thSet' [pred]
    end

  (************************ Sequences @anyLevel **************************)
  | Stm.StSeq xs, is_ghost ->
      let f (g,l,t,fs) cmd =
        let (gS,lS,tS,fS) =
          aux_rho_for_st sys soc g l t mode cmd th is_ghost abs mInfo pt in
        (gS, lS, tS, fS@fs) in
      List.fold_left f (gSet, lSet, thSet, []) xs
      
  (************************ Ill-formed statements ************************)
  | Stm.StAtomic (_, _, Some _), false ->
      let eff_list = Bridge.gen_st_cond_effect_as_array pt st false th_p in
      let f (cond, eff, c, n) = 
        let pos_change = make_pos_change c [n] in
        [Formula.conj_list (pos_change @ [E.param th_p cond; eff])] in
      let rho_list = List.map f eff_list in
      (E.TermSet.empty, E.TermSet.empty, E.TermSet.empty, rho_list)
  (************************ Call @topLevel *******************************)
  | Stm.StCall (_,proc_name,ps,gc,Some i), false ->
      (* We make the argument assignment *)
      let (modif_list, equiv_list) =
        let gen_f = match mode with
                    | SClosed _ -> Bridge.construct_stm_term_eq
                    | SOpenArray _ -> Bridge.construct_stm_term_eq_as_array in
        let call_proc_args = proc_info_get_args
                               (get_proc_by_name sys proc_name) in
        let proc_init_vals = (get_proc_init_vals sys proc_name) in
        let (init_assign,initialized_vars) =
                  List.fold_left (fun (fs,vs) (v,value) ->
                    let v_term = E.var_to_term v in
                    let v' = E.V.prime (E.V.set_param v th_p) in
                    match value with
                    | E.Equality t  -> ((E.eq_term (E.var_to_term v') t)::fs,v_term::vs)
                    | E.Condition c -> (Formula.Iff(E.boolvar v',c)::fs,v_term::vs)
                  ) ([],[]) proc_init_vals in
        let assignments = List.combine call_proc_args ps
        in
          List.fold_left (fun (ms,es) ((arg,arg_sort),value) ->
            let v = Stm.VarT (Stm.build_var arg arg_sort (Stm.Scope proc_name)) in
            let (m,e) = gen_f mInfo v th_p (Stm.Term value)
            in
              (m@ms, e::es)
          ) (initialized_vars,init_assign) assignments in
      let gSet' = E.filter_term_set modif_list gSet in
      let lSet' = E.filter_term_set modif_list lSet in
      let thSet' = E.filter_term_set modif_list thSet in
      (* We make position change *)
      let call_pos = match i.Stm.call_pos with
                     | None   -> begin
                                   Interface.Err.msg "Missing call position" $
                                     Printf.sprintf "There is no information \
                                                     on where to jump for \
                                                     procedure %s" proc_name;
                                   raise(Impossible_call proc_name)
                                 end
                     | Some p -> [p] in
      (* Final transition predicate *)
      let pred = (make_pos_change i.Stm.pos call_pos) @ equiv_list
      in
        append_to_ghost gc gSet' lSet' thSet' [pred]
  (************************ Return @topLevel *****************************)
  | Stm.StReturn (t_opt,gc,Some i), false ->
      let (gSet', lSet', thSet',equiv) =
        match t_opt with
        (* Return value to process *)
        | Some t ->
            begin
              let call_pos = i.Stm.called_from_pos in
              let (modif,equiv) =
                List.fold_left (fun (ms,es) pos ->
                  let call_stm = get_statement_at sys pos in
                  match call_stm with
                  | (_, Stm.StCall (Some ret_t, _,_,_,Some info)) ->
                    begin
                      let (k,(m,e)) =
                        match mode with
                        | SClosed _   ->
                            (th, Bridge.construct_stm_term_eq
                                  mInfo ret_t th_p (Stm.Term t))
                        | SOpenArray _ ->
                            (th, Bridge.construct_stm_term_eq_as_array
                                  mInfo ret_t th_p (Stm.Term t)) in
                      let pos_assignment =
                        Formula.Implies (build_next_pc mode k [info.Stm.next_pos], e) in
                      (m@ms, pos_assignment::es)
                    end
                  | _ -> (ms,es)
                ) ([],[]) call_pos in
              let still_gSet = E.filter_term_set modif gSet in
              let still_lSet = E.filter_term_set modif lSet in
              let still_thSet = E.filter_term_set modif thSet in
              (still_gSet, still_lSet, still_thSet, Formula.conj_list equiv)
            end
        (* No return value *)
        | None   -> (gSet, lSet, thSet, Formula.True) in
      let pred = (make_pos_change i.Stm.pos i.Stm.return_pos) @ [equiv] in
      append_to_ghost gc gSet' lSet' thSet' [pred]
  | _ -> (gSet, lSet, thSet, [])



let gen_rho (sys : t)             (* The system                           *)
            (mode : sysMode)      (* For closed or open system?           *)
            (soc:seq_or_conc_t)   (* Sequential or concurrent system      *)
            (pt:Bridge.prog_type) (* Program type. Heap based or numeric  *)
            (p : E.pc_t)          (* Program line                         *)
            (abs : abstraction)   (* Counting abstraction or not?         *)
            (hide_pres : bool)    (* Hide variable preservation?          *)
            (th:E.tid)            (* Thread taking the transition         *)
              : E.formula list =
  (* LOG "Entering gen_rho..." LEVEL TRACE; *)
  let gSet = gen_global_vars_as_terms sys in
  let (proc,st) = get_statement_at sys p in
  (* let remLocList = List.remove_assoc proc allLocList in *)
  let th_list = match mode with
                | SClosed m -> E.gen_tid_list 1 m
                | SOpenArray js -> js in
  let thSet = 
    E.construct_term_set $ List.map (fun x -> E.TidT x) th_list in

  (* For Malloc -- BEGIN *)
  let is_sort s v = (E.V.sort v = s) in
  let gVars = get_variable_list (get_global sys) in
  let lVars = get_all_local_vars sys in
  let gAddrVars = List.filter (is_sort E.Addr) gVars in
  let gSetVars = List.filter (is_sort E.Set) gVars in
  let lAddrVars = List.fold_left 
    (fun xs (_,vs) -> (List.filter (is_sort E.Addr) vs) @ xs) [] lVars in
  let lSetVars = List.fold_left 
    (fun xs (_,vs) -> (List.filter (is_sort E.Set) vs) @ xs) [] lVars in

  let mInfo = {
    Bridge.tids = th_list;
    Bridge.gAddrs = gAddrVars; 
    Bridge.gSets = gSetVars;
    Bridge.lAddrs = lAddrVars; 
    Bridge.lSets = lSetVars
  } in

  let all_local, filtered_local =
    match mode with
    | SClosed _ ->  let ls = gen_local_vars_as_terms sys in (ls,ls)
    | SOpenArray _ -> let ls = gen_local_vars_as_array_terms sys in
        (ls, List.remove_assoc proc ls) in
  let lSet = List.assoc proc all_local in
  let (gSet',lSet',thSet',rhoList) =
    aux_rho_for_st sys soc gSet lSet thSet mode st th false abs mInfo pt in

  let phi_list =
    if hide_pres then
      rhoList
    else begin
      match st with
      (* If atomic statement, I need to generate the preservation
         for each list of conjunctions separately *)
      | Stm.StAtomic _ -> 
          let f xs = 
            let phi = Formula.conj_list xs in
            let f' v = E.ArrayT (E.VarArray (E.V.unparam v)) in
            let p_vars = List.map f' (E.primed_vars phi) in
            let gSet' = E.filter_term_set p_vars gSet in
            let lSet' = E.filter_term_set p_vars lSet in
            let thSet' = E.filter_term_set p_vars thSet in
            let pres = gen_pres proc gSet' lSet' filtered_local thSet' mode th in
            (phi::pres) in
          List.map f rhoList
      (* Otherwise, I already have the terms to be preserved *)
      | _ ->
          let pres_list =
            gen_pres proc gSet' lSet' filtered_local thSet' mode th in
          List.map (fun x -> x @ pres_list) rhoList 
    end in
    List.map Formula.conj_list phi_list
