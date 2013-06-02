open Printf
open LeapLib

module E = Expression
module Stm  = Statement


(* Type declaration *)
type var_table_t = (E.varId, E.var_info_t) Hashtbl.t

type proc_info_t = {sort : E.sort option;
                    inputVars : var_table_t;
                    localVars : var_table_t;
                    args : (string * E.sort) list;
                    fLine : E.pc_t; (* TODO: Is set somewhere? *)
                    lLine : E.pc_t;
                    prog : Stm.statement_t option
                   }

and proc_table_t = (string, proc_info_t) Hashtbl.t


(*TODO: Used somewhere? *)
type tran_table_t = (int, E.formula list) Hashtbl.t 


type st_table_t = (E.pc_t, (string * Stm.statement_t)) Hashtbl.t


type label_table_t = (string, E.pc_t * E.pc_t) Hashtbl.t


type system_t = (var_table_t          *   (* global variables *)
                 Stm.boolean option   *   (* the initial assumption *)
                 proc_table_t         *   (* procedures *)
                 tran_table_t         *   (* transition relations *)
                 E.pc_t list       *   (* fair transitions *)
                 int                  *   (* number of threads *)
                 st_table_t           *   (* system statements *)
                 label_table_t)           (* program line labels *)


type sysMode =
    SClosed
  | SOpenArray of E.tid list




(* Exceptions *)
exception Duplicated_var of E.varId * E.sort * E.sort
exception Duplicated_procedure of string
exception Unknown_procedure of string
exception Undefined_variable of E.varId
exception Not_position of E.pc_t
exception Duplicated_label of string * E.pc_t * E.pc_t * E.pc_t
exception Undefined_label of string * E.pc_t
exception Invalid_argument




(* Configuration *)
let initVarNum       : int    = 40
let initProcNum      : int    = 10
let initTranNum      : int    = 200
let initLabelNum     : int    = 20
let defMainProcedure : string = "main"
let heap_name        : string = "heap"
let me_tid           : string = "me"
let me_tid_var       : E.variable = E.build_var me_tid E.Thid
                                         false E.Shared
                                         E.GlobalScope E.RealVar
let me_tid_th        : E.tid = E.VarTh me_tid_var


let empty_var_table = Hashtbl.create 1

let empty_system = (Hashtbl.create 1,
                    None,
                    Hashtbl.create 1,
                    Hashtbl.create 1,
                    [],
                    0,
                    Hashtbl.create 1,
                    Hashtbl.create 1)
                    

(* TABLE OF VARIABLES FUNCTIONS *)
let new_var_table : var_table_t =
  Hashtbl.create initVarNum


let copy_var_table (table:var_table_t) : var_table_t =
  Hashtbl.copy table


let join_var_table (dst:var_table_t) (src:var_table_t) : unit =
  Hashtbl.iter (Hashtbl.replace dst) src


let add_var (table:var_table_t)
            (v:E.varId)
            (s:E.sort)
            (e:E.initVal_t option)
            (t:E.shared_or_local)
            (k:E.var_nature) : unit =
  if Hashtbl.mem table v then
    begin
      let prevSort = E.var_info_sort (Hashtbl.find table v) in
      Interface.Err.msg "Variable already defined" $
        sprintf "Variable \"%s\" of sort %s has already been defined \
                 previously with sort %s." v (E.sort_to_str s)
                                             (E.sort_to_str prevSort);
      raise(Duplicated_var(v, s, prevSort))
    end
  else
    Hashtbl.replace table v (s,e,t,k)


let del_var (table:var_table_t) (v:E.varId) : var_table_t =
  Hashtbl.remove table v; table


let mem_var (table:var_table_t) (v:E.varId) : bool =
  Hashtbl.mem table v


let find_var_type (table:var_table_t) (v:E.varId) : E.sort =
  E.var_info_sort (Hashtbl.find table v)


let find_var_expr (table:var_table_t) (v:E.varId) : E.initVal_t option =
  E.var_info_expr (Hashtbl.find table v)


let find_var_tid (table:var_table_t) (v:E.varId) : E.shared_or_local =
  E.var_info_shared_or_local (Hashtbl.find table v)


let find_var_kind (table:var_table_t) (v:E.varId) : E.var_nature =
  E.var_info_nature (Hashtbl.find table v)


let get_var_id_list (table:var_table_t) : E.varId list =
  let res = Hashtbl.fold (fun var _ xs -> var :: xs) table []
  in
    res


let get_variable_list (table:var_table_t) : E.variable list =
  let res = Hashtbl.fold (fun var info xs ->
              let s  = E.var_info_sort info in
              let th = E.var_info_shared_or_local info
              in
                (E.build_var var s false th E.GlobalScope E.RealVar) :: xs
            ) table []
  in
    res


let get_var_list (table:var_table_t) (p:string option) : E.variable list =
  let res = Hashtbl.fold (fun var info xs ->
              let s = E.var_info_sort info in
              let scope = match p with
                          | None -> E.GlobalScope
                          | Some proc -> E.Scope proc in
                (E.build_var var s false E.Shared scope E.RealVar) :: xs
            ) table []
  in
    res
    


let clear_table (table:var_table_t) : unit =
  Hashtbl.clear table


let filter_table (table:var_table_t) (vars:E.varId list) : unit =
  List.iter (Hashtbl.remove table) vars


let num_of_vars (table:var_table_t) : int =
  Hashtbl.length table


let undeftids_in_formula_decl (ts:E.varId list) (invVars:var_table_t) :unit =
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
  

(* SYSTEM MANIPULATION FUNCTIONS *)
let new_system (gVars:var_table_t)
               (assume:Stm.boolean option)
               (procs:proc_table_t)
               (trans:tran_table_t)
               (fair:int list)
               (st_table:st_table_t)
               (lt:label_table_t) : system_t =
  (gVars, assume, procs, trans, fair, 1, st_table, lt)


let get_global     ((g,_,_,_,_,_,_,_):system_t) : var_table_t = g
let get_assume     ((_,a,_,_,_,_,_,_):system_t) : Stm.boolean option = a
let get_procs      ((_,_,p,_,_,_,_,_):system_t) : proc_table_t = p
let get_trans      ((_,_,_,t,_,_,_,_):system_t) : tran_table_t = t
let get_fair       ((_,_,_,_,f,_,_,_):system_t) : int list = f
let get_threads    ((_,_,_,_,_,n,_,_):system_t) : int = n
let get_statements ((_,_,_,_,_,_,s,_):system_t) : st_table_t = s
let get_labels     ((_,_,_,_,_,_,_,l):system_t) : label_table_t = l


let set_threads    ((g,a,p,t,f,_,s,l):system_t) (n:int) : system_t =
  (g,a,p,t,f,n,s,l)


let is_proc (sys:system_t) (p_name:string) : bool =
  let proc_tbl = get_procs sys in
    Hashtbl.mem proc_tbl p_name


let get_proc_by_name (sys:system_t) (p_name:string) : proc_info_t =
  let tbl = get_procs sys in
  if Hashtbl.mem tbl p_name then
    Hashtbl.find tbl p_name
  else
    begin
      Interface.Err.msg "Process name not found" $
              sprintf "A process with name %s could not be found" p_name;
      raise(Unknown_procedure p_name)
    end


let get_input_by_name (sys:system_t) (p_name:string) : var_table_t =
  let info = get_proc_by_name sys p_name in info.inputVars


let get_local_by_name (sys:system_t) (p_name:string) : var_table_t =
  let info = get_proc_by_name sys p_name in info.localVars


let get_fLine_by_name (sys:system_t) (p_name:string) : E.pc_t =
  let info = get_proc_by_name sys p_name in info.fLine


let get_lLine_by_name (sys:system_t) (p_name:string) : E.pc_t =
  let info = get_proc_by_name sys p_name in info.lLine


let get_prog_by_name (sys:system_t) (p_name:string) : Stm.statement_t option =
  let info = get_proc_by_name sys p_name in info.prog


let proc_sort_func (sys:system_t) (p1:string) (p2:string) : int =
  let p1_init = get_fLine_by_name sys p1 in
  let p2_init = get_fLine_by_name sys p2 in
    p1_init - p2_init


let get_proc_name_list (sys:system_t) (sorted:bool) : string list =
  let proc_tbl = get_procs sys in
  let res : string list ref = ref [] in
  let _ = Hashtbl.iter (fun name _ -> res := name :: !res) proc_tbl in
    if sorted then
      List.fast_sort (proc_sort_func sys) !res
    else
      !res


let get_all_local_vars (sys:system_t) : (string * E.variable list) list =
  let procs = get_proc_name_list sys false
  in
    List.map (fun p ->
      let vTable = get_local_by_name sys p in
      let vList = get_var_list vTable (Some p)
      in
        (p, vList)
    ) procs


let get_statement_at (sys:system_t) (pos:E.pc_t) : (string*Stm.statement_t) =
  let tbl = get_statements sys in
  try
    Hashtbl.find tbl pos
  with
    Not_found -> Interface.Err.msg "Not a system position" $
                         sprintf "Position %i does not corresponds to a \
                                  valid statement position within the \
                                  declared system." pos;
    raise(Not_position pos)


let get_trans_num (sys:system_t) : int =
  let tbl = get_statements sys in
  Hashtbl.length tbl


let add_global_vars (sys:system_t) (tbl:var_table_t) : system_t =
  let (g,a,p,t,f,n,s,l) = sys in
  let _                 = join_var_table g tbl in
    (g, a, p, t, f, n, s, l)


let del_global_var (sys:system_t) (id:E.varId) : system_t =
  let (g,a,p,t,f,n,s,l) = sys
  in
    (del_var g id,a,p,t,f,n,s,l)


let del_global_var_regexp (sys:system_t) (expr:Str.regexp) : system_t =
  let (g,a,p,t,f,n,s,l) = sys in
  let _ = Hashtbl.iter (fun id _ ->
            if (Str.string_match expr id 0) then
              Hashtbl.remove g id
          ) g
  in
    (g,a,p,t,f,n,s,l)



(* SYSTEM QUERY FUNCTIONS *)
let get_accvars_by_name (sys:system_t)
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
let get_accvars (sys:system_t) : (string * var_table_t * var_table_t) list =
  let proc_names = get_proc_name_list sys false in
  let proc_vars  = List.map (fun p ->
                              let accVars = get_accvars_by_name sys p in
                                (p, fst accVars, snd accVars)) proc_names
  in
    proc_vars
(*
  let proc_vars  = List.map (fun p->(p,get_allvars_by_name sys p)) proc_names in
  let res        = List.map (fun (n, (gV, lV)) -> (n, gV, lV)) proc_vars
  in
    res
*)


let get_all_vars_id (sys:system_t) : E.varId list =
  let gv_tbl = get_global sys in
  let lv_lst = get_accvars sys in
  let gv = Hashtbl.fold (fun v _ l -> v::l) gv_tbl [] in
  let lv = List.map (fun (p,_,lt) ->
             Hashtbl.fold (fun v _ xs ->
               (E.localize_var_id v p)::xs
             ) lt []
           ) lv_lst
  in
    gv @ (List.flatten lv)


let gen_all_vars_as_terms (sys:system_t) : E.term list =
  let param_list = E.gen_tid_list 1 (get_threads sys) in
  let gTbl       = get_global sys in
  let vInfo      = get_accvars sys in
  let allVars    = ref [] in
  let _ = Hashtbl.iter (fun v info ->
            allVars := (E.convert_var_to_term E.GlobalScope v info)::!allVars) gTbl in
  let _ = List.iter (fun t ->
            List.iter (fun (p,_,l) ->
              Hashtbl.iter (fun v (s,e,_,k) ->
                allVars := (E.convert_var_to_term
                              (E.Scope p) v (s,e,E.Local t,k)) :: !allVars
                           ) l
                      ) vInfo
                    ) param_list
  in
        !allVars


let gen_all_vars_as_array_terms (sys:system_t) : E.term list =
  let gTbl    = get_global sys in
  let vInfo   = get_accvars sys in
  let allVars = ref [] in
  let _ = Hashtbl.iter (fun v info ->
            let k   = E.var_info_nature info in
            let s   = E.var_info_sort info in
            let var = E.build_var v s false E.Shared E.GlobalScope k in
            allVars := E.ArrayT(E.VarArray var) :: !allVars
          ) gTbl in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v info ->
              let k = E.var_info_nature info in
              let s = E.var_info_sort info in
              let var = E.build_var v s false E.Shared (E.Scope p) k in
              allVars :=
                E.ArrayT(E.VarArray var) :: !allVars
            ) l
          ) vInfo
  in
    !allVars


let get_sys_var_tables (sys:system_t)
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



(* SYSTEM EXTRA FUNCTIONS *)
let get_sort_from_variable (gVars:var_table_t)
                           (iVars:var_table_t)
                           (lVars:var_table_t)
                           (auxVars:var_table_t)
                           (v:E.varId) : E.sort =
  if mem_var gVars v then
    find_var_type gVars v
  else if mem_var iVars v then
    find_var_type iVars v
  else if mem_var lVars v then
    find_var_type lVars v
  else if mem_var auxVars v then
    find_var_type auxVars v
  else
    E.Thid
    (* FIX: We are just assuming that undefined variables are used to identify threads *)
(*
    begin
      Interface.Err.msg "Undefined variable" $
        sprintf "Variable %s could not be found nor as global variable nor \
                 in the given variable tables." v;
      raise(Undefined_variable v)
    end
*)


let get_sort_from_term (gVars:var_table_t)
                       (iVars:var_table_t)
                       (lVars:var_table_t)
                       (auxVars:var_table_t)
                       (t:E.term) : E.sort =
  match t with
    E.SetT(_)           -> E.Set
  | E.VarT v            -> get_sort_from_variable gVars iVars lVars auxVars v.E.id
                            (* TODO: Or maybe just s? *)
  | E.ElemT(_)          -> E.Elem
  | E.ThidT(_)          -> E.Thid
  | E.AddrT(_)          -> E.Addr
  | E.CellT(_)          -> E.Cell
  | E.SetThT(_)         -> E.SetTh
  | E.SetIntT(_)        -> E.SetInt
  | E.SetElemT(_)       -> E.SetElem
  | E.PathT(_)          -> E.Path
  | E.MemT(_)           -> E.Mem
  | E.IntT(_)           -> E.Int
  | E.ArrayT(_)         -> E.Array
  | E.AddrArrayT(_)     -> E.AddrArray
  | E.TidArrayT(_)      -> E.TidArray



(* PROCEDURE INFORMATION FUNCTIONS *)
let new_proc_info (s:E.sort option)
                  (input : var_table_t)
                  (local : var_table_t)
                  (args : (E.varId * E.sort) list)
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


let proc_info_get_args (info:proc_info_t) : (E.varId * E.sort) list =
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
    @return the list of global variables in sys represented as terms
  *)
let gen_global_vars_as_terms (sys:system_t) : E.TermSet.t =
  let gTbl = get_global sys in
  let gVars = ref E.TermSet.empty in
  let _ = Hashtbl.iter (fun v info ->
            gVars := E.TermSet.add (E.convert_var_to_term E.GlobalScope v info)
                       !gVars) gTbl
  in
    !gVars


(** Generates the list of local variables for a system, but described as
    terms instead of variable identifiers.
    @param sys the system where variables are extracted from
    @return a list of pairs made by the process name and its local variables
  *)
let gen_local_vars_as_terms (sys:system_t) : (string * E.TermSet.t) list =
  let vInfo   = get_accvars sys in
  let lVars   = ref E.TermSet.empty in
  let resVars = ref [] in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v (s,e,_,k) ->
              lVars := E.TermSet.add
                       (E.convert_var_to_term (E.Scope p) v (s,e,E.Shared,k)) !lVars
            )l;
            resVars := (p, !lVars):: !resVars;
            lVars := E.TermSet.empty) vInfo
  in
    !resVars


let gen_local_vars_as_array_terms (sys:system_t)
                                    : (string * E.TermSet.t) list =
  let vInfo   = get_accvars sys in
  let lVars   = ref E.TermSet.empty in
  let resVars = ref [] in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v info ->
              let k   = E.var_info_nature info in
              let s   = E.var_info_sort info in
              let var = E.build_var v s false E.Shared (E.Scope p) k in
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
let check_is_numeric (sys:system_t) : unit =
  let gv_tbl = get_global sys in
  let lv_list = get_accvars sys in

  let _ = Hashtbl.iter E.check_numeric gv_tbl in
  let _ = List.iter (fun (p,_,lt) ->
            Hashtbl.iter (fun v info ->
              E.check_numeric (E.localize_var_id v p) info
            ) lt
          ) lv_list
  in
    ()




(* PRINTING FUNCTIONS *)
let var_table_to_str (tbl:var_table_t) : string =
  let decl_to_str v info =
    let s     = E.var_info_sort info in
    let e     = E.var_info_expr info in
    let k     = E.var_info_nature info in
    let k_str = match k with
                  E.RealVar -> ""
                | E.GhostVar -> "ghost " in
    let s_str = E.sort_to_str s
    in
      match e with
        Some (E.Equality t)  -> sprintf "\t%s%s %s := %s" k_str s_str v
                                                          (E.term_to_str t)
      | Some (E.Condition c) -> sprintf "\t%s%s %s" k_str s_str
                                                       (E.formula_to_str c)
      | None                    -> sprintf "\t%s%s %s" k_str s_str v
(*
    Obsolete code
    sprintf "\t%s%s %s %s" k_str (E.sort_to_str s) v
        (Option.map_default (fun t -> " := " ^ (E.expr_to_str t)) "" e)
*)
  in
  let tbl_str = String.concat "\n" $ Hashtbl.fold (fun v info xs ->
                                      (decl_to_str v info)::xs) tbl [] in
tbl_str


let procedure_to_str (sys:system_t) (p_name:string) : string =
  let proc_arg      = get_input_by_name sys p_name in
  let proc_local    = get_local_by_name sys p_name in
  let proc_prog     = get_prog_by_name sys p_name in

  let arg_str       = String.concat ", " $
                     Hashtbl.fold (fun v info xs ->
                       let s = E.var_info_sort info in
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


let system_to_str (sys:system_t) : string =
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

