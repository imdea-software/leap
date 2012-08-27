open Printf

open LeapLib

module Expr = Expression
module Stm  = Statement


(* Type declaration *)
type var_table_t = (Expr.varId, Expr.var_info_t) Hashtbl.t

type proc_info_t = {sort : Expr.sort option;
                    inputVars : var_table_t;
                    localVars : var_table_t;
                    args : (string * Expr.sort) list;
                    fLine : Expr.pc_t; (* TODO: Is set somewhere? *)
                    lLine : Expr.pc_t;
                    prog : Stm.statement_t option
                   }

and proc_table_t = (string, proc_info_t) Hashtbl.t


(*TODO: Used somewhere? *)
type tran_table_t = (int, Expr.formula list) Hashtbl.t 


type st_table_t = (Expr.pc_t, (string * Stm.statement_t)) Hashtbl.t


type label_table_t = (string, Expr.pc_t * Expr.pc_t) Hashtbl.t


type system_t = (var_table_t          *   (* global variables *)
                 Stm.boolean option   *   (* the initial assumption *)
                 proc_table_t         *   (* procedures *)
                 tran_table_t         *   (* transition relations *)
                 Expr.pc_t list       *   (* fair transitions *)
                 int                  *   (* number of threads *)
                 st_table_t           *   (* system statements *)
                 label_table_t)           (* program line labels *)


type sysMode =
    SClosed
  | SOpenArray of Expr.tid list




(* Exceptions *)
exception Duplicated_var of Expr.varId * Expr.sort * Expr.sort
exception Duplicated_procedure of string
exception Unknown_procedure of string
exception Undefined_variable of Expr.varId
exception Not_position of Expr.pc_t
exception Duplicated_label of string * Expr.pc_t * Expr.pc_t * Expr.pc_t
exception Undefined_label of string * Expr.pc_t
exception Invalid_argument




(* Configuration *)
let initVarNum       : int    = 40
let initProcNum      : int    = 10
let initTranNum      : int    = 200
let initLabelNum     : int    = 20
let defMainProcedure : string = "main"
let heap_name        : string = "heap"
let me_tid           : string = "me"
let me_tid_var       : Expr.variable = Expr.build_var me_tid Expr.Thid
                                         false None None Expr.Normal
let me_tid_th        : Expr.tid = Expr.VarTh me_tid_var


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
            (v:Expr.varId)
            (s:Expr.sort)
            (e:Expr.initVal_t option)
            (t:Expr.tid option)
            (k:Expr.kind_t) : unit =
  if Hashtbl.mem table v then
    begin
      let prevSort = Expr.var_info_sort (Hashtbl.find table v) in
      Interface.Err.msg "Variable already defined" $
        sprintf "Variable \"%s\" of sort %s has already been defined \
                 previously with sort %s." v (Expr.sort_to_str s)
                                             (Expr.sort_to_str prevSort);
      raise (Duplicated_var (v, s, prevSort))
    end
  else
    Hashtbl.replace table v (s,e,t,k)


let del_var (table:var_table_t) (v:Expr.varId) : var_table_t =
  Hashtbl.remove table v; table


let mem_var (table:var_table_t) (v:Expr.varId) : bool =
  Hashtbl.mem table v


let find_var_type (table:var_table_t) (v:Expr.varId) : Expr.sort =
  Expr.var_info_sort (Hashtbl.find table v)


let find_var_expr (table:var_table_t) (v:Expr.varId) : Expr.initVal_t option =
  Expr.var_info_expr (Hashtbl.find table v)


let find_var_tid (table:var_table_t) (v:Expr.varId) : Expr.tid option =
  Expr.var_info_tid (Hashtbl.find table v)


let find_var_kind (table:var_table_t) (v:Expr.varId) : Expr.kind_t =
  Expr.var_info_kind (Hashtbl.find table v)


let get_var_id_list (table:var_table_t) : Expr.varId list =
  let res = Hashtbl.fold (fun var _ xs -> var :: xs) table []
  in
    res


let get_variable_list (table:var_table_t) : Expr.variable list =
  let res = Hashtbl.fold (fun var info xs ->
              let s  = Expr.var_info_sort info in
              let th = Expr.var_info_tid info
              in
                (Expr.build_var var s false th None Expr.Normal) :: xs
            ) table []
  in
    res


let get_var_list (table:var_table_t) (p:string option) : Expr.variable list =
  let res = Hashtbl.fold (fun var info xs ->
              let s = Expr.var_info_sort info in
                (Expr.build_var var s false None p Expr.Normal) :: xs
            ) table []
  in
    res
    


let clear_table (table:var_table_t) : unit =
  Hashtbl.clear table


let filter_table (table:var_table_t) (vars:Expr.varId list) : unit =
  List.iter (Hashtbl.remove table) vars


let num_of_vars (table:var_table_t) : int =
  Hashtbl.length table


let undeftids_in_formula_decl (ts:Expr.varId list) (invVars:var_table_t) :unit =
  List.iter (fun id ->
    if not (mem_var invVars id) then
      begin
        Interface.Err.msg "Undefined variable" $
          sprintf "Variable %s was used in the program and assumed to be a \
                   parameter of the formula to be verified. However, such \
                   variable is not declared as a formula parameter." id;
        raise (Undefined_variable id)
      end
    ) ts



(* LABEL TABLE FUNCTIONS *)
let new_label_table : label_table_t =
  Hashtbl.create initLabelNum


let copy_label_table (table:label_table_t) : label_table_t =
  Hashtbl.copy table


let check_undefined_label (tbl:label_table_t) (l:string) (p:Expr.pc_t) : unit =
  if (Hashtbl.mem tbl l) then
    begin
    let (init_pos, end_pos) = Hashtbl.find tbl l
    in
      Interface.Err.msg "Duplicated label" $
        sprintf "Trying to label line %i with tag \"%s\", but this tag has \
                 already been used to label lines between %i and %i"
          p l init_pos end_pos;
      raise (Duplicated_label (l, p, init_pos, end_pos))
    end


let check_defined_label (tbl:label_table_t) (l:string) (p:Expr.pc_t) : unit =
  if not (Hashtbl.mem tbl l) then
    begin
      Interface.Err.msg "Undefined label" $
        sprintf "Trying to close label \"%s\" at line %i, but no opening \
                 tag for this label was found." l p;
      raise (Undefined_label (l, p))
    end


let add_single_label (tbl:label_table_t) (l:string) (p:Expr.pc_t) : unit =
  let _ = check_undefined_label tbl l p in
    Hashtbl.replace tbl l (p,p)


let add_open_label (tbl:label_table_t) (l:string) (p:Expr.pc_t) : unit =
  let _ = check_undefined_label tbl l p in
    Hashtbl.replace tbl l (p,p)


let add_close_label (tbl:label_table_t) (l:string) (p:Expr.pc_t) : unit =
  let _ = check_defined_label tbl l p in
  let (pc_init,_) = Hashtbl.find tbl l in
  let _ = assert (pc_init >= 0) in
    Hashtbl.replace tbl l (pc_init, p)


let get_label_pos (tbl:label_table_t) (l:string) : (Expr.pc_t * Expr.pc_t) option =
  try
    Some (Hashtbl.find tbl l)
  with _ -> None


let get_labels_list (tbl:label_table_t) : string list =
  let label_list = Hashtbl.fold (fun s _ xs ->
                     s::xs
                   ) tbl []
  in
    label_list


let get_labels_for_pos (tbl:label_table_t) (pc:Expr.pc_t) : string list =
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
      raise (Unknown_procedure p_name)
    end


let get_input_by_name (sys:system_t) (p_name:string) : var_table_t =
  let info = get_proc_by_name sys p_name in info.inputVars


let get_local_by_name (sys:system_t) (p_name:string) : var_table_t =
  let info = get_proc_by_name sys p_name in info.localVars


let get_fLine_by_name (sys:system_t) (p_name:string) : Expr.pc_t =
  let info = get_proc_by_name sys p_name in info.fLine


let get_lLine_by_name (sys:system_t) (p_name:string) : Expr.pc_t =
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


let get_all_local_vars (sys:system_t) : (string * Expr.variable list) list =
  let procs = get_proc_name_list sys false
  in
    List.map (fun p ->
      let vTable = get_local_by_name sys p in
      let vList = get_var_list vTable (Some p)
      in
        (p, vList)
    ) procs


let get_statement_at (sys:system_t) (pos:Expr.pc_t) : (string*Stm.statement_t) =
  let tbl = get_statements sys in
  try
    Hashtbl.find tbl pos
  with
    Not_found -> Interface.Err.msg "Not a system position" $
                         sprintf "Position %i does not corresponds to a \
                                  valid statement position within the \
                                  declared system." pos;
    raise (Not_position pos)


let get_trans_num (sys:system_t) : int =
  let tbl = get_statements sys in
  Hashtbl.length tbl


let add_global_vars (sys:system_t) (tbl:var_table_t) : system_t =
  let (g,a,p,t,f,n,s,l) = sys in
  let _                 = join_var_table g tbl in
    (g, a, p, t, f, n, s, l)


let del_global_var (sys:system_t) (id:Expr.varId) : system_t =
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


let get_all_vars_id (sys:system_t) : Expr.varId list =
  let gv_tbl = get_global sys in
  let lv_lst = get_accvars sys in
  let gv = Hashtbl.fold (fun v _ l -> v::l) gv_tbl [] in
  let lv = List.map (fun (p,_,lt) ->
             Hashtbl.fold (fun v _ xs ->
               (Expr.localize_var_id v p)::xs
             ) lt []
           ) lv_lst
  in
    gv @ (List.flatten lv)


let gen_all_vars_as_terms (sys:system_t) : Expr.term list =
  let param_list = Expr.gen_thread_list 1 (get_threads sys) in
  let gTbl       = get_global sys in
  let vInfo      = get_accvars sys in
  let allVars    = ref [] in
  let _ = Hashtbl.iter (fun v info ->
            allVars := (Expr.convert_var_to_term None v info)::!allVars) gTbl in
  let _ = List.iter (fun t ->
            List.iter (fun (p,_,l) ->
              Hashtbl.iter (fun v (s,e,_,k) ->
                allVars := (Expr.convert_var_to_term
                              (Some p) v (s,e,Some t,k)) :: !allVars
                           ) l
                      ) vInfo
                    ) param_list
  in
        !allVars


let gen_all_vars_as_array_terms (sys:system_t) : Expr.term list =
  let gTbl    = get_global sys in
  let vInfo   = get_accvars sys in
  let allVars = ref [] in
  let _ = Hashtbl.iter (fun v info ->
            let k   = Expr.var_info_kind info in
            let s   = Expr.var_info_sort info in
            let var = Expr.build_var v s false None None k in
            allVars := Expr.ArrayT(Expr.VarArray var) :: !allVars
          ) gTbl in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v info ->
              let k = Expr.var_info_kind info in
              let s = Expr.var_info_sort info in
              let var = Expr.build_var v s false None (Some p) k in
              allVars :=
                Expr.ArrayT(Expr.VarArray var) :: !allVars
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
                           (v:Expr.varId) : Expr.sort =
  if mem_var gVars v then
    find_var_type gVars v
  else if mem_var iVars v then
    find_var_type iVars v
  else if mem_var lVars v then
    find_var_type lVars v
  else if mem_var auxVars v then
    find_var_type auxVars v
  else
    Expr.Thid
    (* FIX: We are just assuming that undefined variables are used to identify threads *)
(*
    begin
      Interface.Err.msg "Undefined variable" $
        sprintf "Variable %s could not be found nor as global variable nor \
                 in the given variable tables." v;
      raise (Undefined_variable v)
    end
*)


let get_sort_from_term (gVars:var_table_t)
                       (iVars:var_table_t)
                       (lVars:var_table_t)
                       (auxVars:var_table_t)
                       (t:Expr.term) : Expr.sort =
  match t with
    Expr.SetT(_)           -> Expr.Set
  | Expr.VarT(v,_,_,_,s,_) -> get_sort_from_variable gVars iVars lVars auxVars v
                            (* TODO: Or maybe just s? *)
  | Expr.ElemT(_)          -> Expr.Elem
  | Expr.ThidT(_)          -> Expr.Thid
  | Expr.AddrT(_)          -> Expr.Addr
  | Expr.CellT(_)          -> Expr.Cell
  | Expr.SetThT(_)         -> Expr.SetTh
  | Expr.SetIntT(_)        -> Expr.SetInt
  | Expr.SetElemT(_)       -> Expr.SetElem
  | Expr.PathT(_)          -> Expr.Path
  | Expr.MemT(_)           -> Expr.Mem
  | Expr.IntT(_)           -> Expr.Int
  | Expr.ArrayT(_)         -> Expr.Array



(* PROCEDURE INFORMATION FUNCTIONS *)
let new_proc_info (s:Expr.sort option)
                  (input : var_table_t)
                  (local : var_table_t)
                  (args : (Expr.varId * Expr.sort) list)
                  (fLine : Expr.pc_t)
                  (lLine : Expr.pc_t)
                  (prog : Stm.statement_t option)
                  : proc_info_t =
  { sort = s;
    inputVars = input;
    localVars = local;
    args = args;
    fLine = fLine;
    lLine = lLine;
    prog = prog }

let proc_info_get_sort (info:proc_info_t) : Expr.sort option =
  info.sort


let proc_info_get_input (info:proc_info_t) : var_table_t =
  info.inputVars


let proc_info_get_local (info:proc_info_t) : var_table_t =
  info.localVars


let proc_init_line (info:proc_info_t) : Expr.pc_t =
  info.fLine


let proc_last_line (info:proc_info_t) : Expr.pc_t =
  info.lLine


let proc_info_get_args (info:proc_info_t) : (Expr.varId * Expr.sort) list =
  info.args


let proc_info_get_args_sig (info:proc_info_t) : Expr.sort list =
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
                raise (Duplicated_procedure n)
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
let gen_global_vars_as_terms (sys:system_t) : Expr.TermSet.t =
  let gTbl = get_global sys in
  let gVars = ref Expr.TermSet.empty in
  let _ = Hashtbl.iter (fun v info ->
            gVars := Expr.TermSet.add (Expr.convert_var_to_term None v info) 
                       !gVars) gTbl
  in
    !gVars


(** Generates the list of local variables for a system, but described as
    terms instead of variable identifiers.
    @param sys the system where variables are extracted from
    @return a list of pairs made by the process name and its local variables
  *)
let gen_local_vars_as_terms (sys:system_t) : (string * Expr.TermSet.t) list =
  let vInfo   = get_accvars sys in
  let lVars   = ref Expr.TermSet.empty in
  let resVars = ref [] in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v (s,e,_,k) ->
              lVars := Expr.TermSet.add
                       (Expr.convert_var_to_term (Some p) v (s,e,None,k)) !lVars
            )l;
            resVars := (p, !lVars):: !resVars;
            lVars := Expr.TermSet.empty) vInfo
  in
    !resVars


let gen_local_vars_as_array_terms (sys:system_t)
                                    : (string * Expr.TermSet.t) list =
  let vInfo   = get_accvars sys in
  let lVars   = ref Expr.TermSet.empty in
  let resVars = ref [] in
  let _ = List.iter (fun (p,_,l) ->
            Hashtbl.iter (fun v info ->
              let k   = Expr.var_info_kind info in
              let s   = Expr.var_info_sort info in
              let var = Expr.build_var v s false None (Some p) k in
              lVars   := Expr.TermSet.add (Expr.ArrayT
                           (Expr.VarArray var)
                         ) !lVars) l;
            resVars := (p, !lVars) :: !resVars;
            lVars   := Expr.TermSet.empty) vInfo
  in
    !resVars



(* TRANSITION TABLE FUNCTIONS *)
let new_tran_table : tran_table_t =
  Hashtbl.create initTranNum


let add_trans (tbl:tran_table_t)
              (pos:Expr.pc_t)
              (form:Expr.formula list) : unit =
  Hashtbl.replace tbl pos form


let get_tran (tbl:tran_table_t) (pos:Expr.pc_t) : Expr.formula list =
  try
    Hashtbl.find tbl pos
  with _ -> []


let tran_table_to_str (tt:tran_table_t) : string =
  let str = Hashtbl.fold (fun pc fs str ->
              (sprintf "Line %i:\n%s" pc
                  (String.concat "\n" $ List.map Expr.formula_to_str fs))^
              "\n" ^ str
            ) tt ""
  in
    str




(* NUMERIC SYSTEM FUNCTIONS *)
let check_is_numeric (sys:system_t) : unit =
  let gv_tbl = get_global sys in
  let lv_list = get_accvars sys in

  let _ = Hashtbl.iter Expr.check_numeric gv_tbl in
  let _ = List.iter (fun (p,_,lt) ->
            Hashtbl.iter (fun v info ->
              Expr.check_numeric (Expr.localize_var_id v p) info
            ) lt
          ) lv_list
  in
    ()




(* PRINTING FUNCTIONS *)
let var_table_to_str (tbl:var_table_t) : string =
  let decl_to_str v info =
    let s     = Expr.var_info_sort info in
    let e     = Expr.var_info_expr info in
    let k     = Expr.var_info_kind info in
    let k_str = match k with
                  Expr.Normal -> ""
                | Expr.Ghost  -> "ghost " in
    let s_str = Expr.sort_to_str s
    in
      match e with
        Some (Expr.Equality t)  -> sprintf "\t%s%s %s := %s" k_str s_str v
                                                          (Expr.term_to_str t)
      | Some (Expr.Condition c) -> sprintf "\t%s%s %s" k_str s_str
                                                       (Expr.formula_to_str c)
      | None                    -> sprintf "\t%s%s %s" k_str s_str v
(*
    Obsolete code
    sprintf "\t%s%s %s %s" k_str (Expr.sort_to_str s) v
        (Option.map_default (fun t -> " := " ^ (Expr.expr_to_str t)) "" e)
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
                       let s = Expr.var_info_sort info in
                         (sprintf "%s:%s" v (Expr.sort_to_str s))::xs
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

