open Printf
open LeapLib
open LeapDebug

module OcamlSys = Sys

module E = Expression
module Stm = Statement
module Sys = System
module NumExp = NumExpression
module PosExp = PosExpression
module Tac = Tactics

type cutoff_type = Dnf | Union | Pruning
type valid_t = Unverified | NotValid | CheckedLocation | Checked | Unneeded

type dp_result_t = valid_t * (* Validity of the formula                    *)
                   int     * (* Total calls to current DP                  *)
                   int     * (* Total calls to DP, including auxiliary DPs *)
                   int     * (* Number of verified formulas                *)
                   float     (* Total time in seconds                      *)


module type S =
sig 
  type rhoMode
  
  type formula_table_t
  
  type vc_info_t = {  pc  : E.pc_t                     ;
                      smp : cutoff_type                ;
                      stac : Tac.solve_tactic_t option ;
                      mutable supps : Tag.f_tag list   ;
                   }
  
  type dp_info

  (*
  type solver_info 
    {
      prog_lines : int ;
      dp         : dp_info ;
      cutoff     : cutoff_type ;
      out_file   : string ;
      focus      : Expression.pc_t list;
      hide_pres  : bool ;
      count_abs  : bool ;
    }
  *)

  val cutoff : unit -> cutoff_type
  val out_file : unit -> string
  val hide_pres : unit -> bool
  val tactics : unit -> Tactics.t
  
  val decl_tag : Tag.f_tag option -> Expression.formula -> unit
  val read_tag : Tag.f_tag -> Expression.formula option
  val is_def_tag : Tag.f_tag -> bool
  val tags_num : unit -> int
  
  
  (** Decision procedure *)
  val none_dp : unit -> dp_info
  val enable_num_dp  : unit -> unit
  val enable_tll_dp  : unit -> unit
  val enable_tsl_dp  : unit -> unit
  val enable_tslk_dp : int  -> unit
  val enable_dp      : DP.t -> unit
  val some_dp_enabled : unit -> bool
  val apply_pos_dp  : unit -> bool
  val apply_num_dp  : unit -> bool
  val apply_tll_dp  : unit -> bool
  val apply_tsl_dp  : unit -> bool
  val apply_tslk_dp : unit -> (bool * int)
  
  
  
  (** Solver information functions *)
  (* val new_solver_info : int  *)
  (*   -> cutoff_type           *)
  (*   -> string                *)
  (*   -> Expression.pc_t list  *)
  (*   -> bool                  *)
  (*   -> bool                  *)
  (*   -> solver_info           *)
  val initialize : int       (** Number of lines in the program. *)
    -> cutoff_type           (** Cutoff strategy to follow. *)
    -> string                (** Output file. *)
    -> Expression.pc_t list  (** Program lines where the VCGen focuses.*)
    -> bool                  (** Hide unmodified variables. *)
    -> bool                  (** Enable counting abstraction. *)
    -> unit

  val set_detFolder : string -> unit

  val set_detProbName : string -> unit

  val set_detFileName : string -> unit
 
  val set_cases : (Expression.pc_t * IGraph.premise_t, 
       Expression.formula list * Tac.t) Hashtbl.t 
    -> unit
  
  val set_tactics : Tac.t -> unit

  (** Transition relation generation *)
  val gen_rho : rhoMode
    -> bool 
    -> bool 
    -> System.system_t 
    -> Expression.tid list 
    -> Expression.pc_t 
    -> Expression.formula list
  
  val gen_all_transitions : System.system_t 
    -> (Expression.pc_t * Expression.formula list) list
  
  val all_transitions_to_str : System.system_t -> string
  
  (** Mode constructor *)
  val new_open_thid_array_mode : Expression.tid 
    -> Expression.tid list 
    -> rhoMode
  
  (* Theta *)
  
  val gen_global_init_cond : System.system_t 
    -> Expression.formula list
  
  val gen_local_init_cond : System.system_t 
    -> string 
    -> Expression.formula list
  
  val gen_init_cond : System.system_t 
    -> string 
    -> Expression.tid list 
    -> bool 
    -> Expression.formula
    
  val gen_theta : System.sysMode 
    -> System.system_t 
    -> Expression.formula
  
  
  (** VC generation for a closed system respect to an invariant candidate *)
  val vcgen_closed : bool 
    -> bool 
    -> System.system_t 
    -> (int * Expression.pc_t * Expression.formula list) list
  
  
  (** VC generation for an open system respect to an invariant candidate *)
  val vcgen_open_inv : bool 
    -> bool 
    -> System.system_t 
    -> (int * Expression.pc_t * Expression.formula list) list
  
  (** B-INV for a closed system *)
  val binv : System.system_t 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list
  
  
  val pinv : System.system_t 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list
  
  
  (** P-INV+ for an open system *)
  val pinv_plus : System.system_t 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list
  
  
  (** SP-INV for an open system *)
  val spinv : System.system_t 
    -> Expression.formula list 
    -> Expression.formula 
    -> (Expression.formula * vc_info_t) list


  (** Sequential B-INV *)
  val seq_binv : System.system_t
    -> Expression.formula
    -> (Expression.formula * vc_info_t) list


  (** Sequential SP-INV for an open system *)
  val seq_spinv : System.system_t
    -> Expression.formula list
    -> Expression.formula
    -> (Expression.formula * vc_info_t) list


  val check_with_pinv : System.system_t 
    -> Expression.formula
    (*-> solver_info*)
    -> bool
  
  val check_with_pinv_plus : System.system_t 
    -> Expression.formula 
    (*-> solver_info*)
    -> bool
  
  val check_with_spinv : System.system_t
    -> Expression.formula list
    -> Expression.formula
    (*-> solver_info*)
    -> bool


  val check_with_seq_binv : System.system_t
    -> Expression.formula
    -> bool


  val check_with_seq_spinv : System.system_t
    -> Expression.formula list
    -> Expression.formula
    (*-> solver_info*)
    -> bool

  
  val check_with_graph : System.system_t 
    -> IGraph.iGraph_t 
    -> bool
  
  (** Formula table update functions *)
  val support_formula_table : Expression.formula list 
    -> formula_table_t 
    -> formula_table_t
  
  
  (** Decision procedure functions *)
  val filter_system : System.system_t 
    -> System.system_t
  
  val clean_formula : Expression.formula 
    -> Expression.formula
  
  
  val apply_dp_on_table : formula_table_t 
    (* -> solver_info  *)
    -> string 
    -> bool
  
  val apply_dp_on_list : (Expression.formula * vc_info_t) list 
    (* -> solver_info  *)
    -> string 
    -> bool
  
  val formula_list_to_table : (Expression.formula * vc_info_t) list 
    -> formula_table_t
end

module Make (PS    : PosSolver.S )
            (TS    : TllSolver.S )
            (TSLKS : TslkSolver.S)
            (NS    : NumSolver.S ) : S =
struct
  type rhoMode =
      RClosed of E.tid * int
    | ROpenArray of E.tid * E.tid list
    | ROpenExt of E.tid * E.tid list
  
  type dp_t = Pos | Num | TLL
  
  type vc_info_t = {  pc  : E.pc_t                     ;
                      smp : cutoff_type                ;
                      stac : Tac.solve_tactic_t option ;
                      mutable supps : Tag.f_tag list   ;
                   }

  type formula_status_t =
    {
      desc : string              ;    (** Brief description *)
      trans : (E.pc_t * int)     ;    (** Transition that represents *)
      supp_tags : Tag.f_tag list ;    (** Support used      *)
      mutable pos_time  : float  ;    (** Pos DP time       *)
      mutable num_time  : float  ;    (** Num DP time       *)
      mutable tll_time  : float  ;    (** TLL DP time       *)
      mutable tslk_time : float  ;    (** TSLK DP time      *)
      mutable tsl_time  : float  ;    (** TSL DP time       *)
    }
  
  type formula_table_t =
    (int,                            (** An ID for the formula      *)
    (E.formula                     * (** The original formula       *)
     PosExp.expression             * (** The formula with pos only  *)
     string list                   * (** New added boolean preds    *)
     valid_t                       * (** Status                     *)
     Tactics.solve_tactic_t option * (** Solving aided tactic       *)
     cutoff_type                   * (** Cutoff strategy to be used *)
     formula_status_t                (** Brief description          *)
    )) Hashtbl.t
  
  type dp_info =
    {
      mutable pos_dp  : bool;
      mutable tll_dp  : bool;
      mutable num_dp  : bool;
      mutable tsl_dp  : bool;
      mutable tslk_dp : bool * int;
    }
  
  type special_cases_tag_tbl_t = (E.pc_t * IGraph.premise_t,
                                  Tag.f_tag list * Tac.t) Hashtbl.t

  type special_cases_form_tbl_t = (E.pc_t * IGraph.premise_t,
                                   E.formula list * Tac.t) Hashtbl.t

  type desc_t =
    {
      mutable detFolder : string ;
        (** Folder for detailed information output  *)
      mutable detProg : string ;
        (** Program name for detailed information   *)
      mutable detInv : string ;
        (** Target invariant used for detailed info *)
      mutable gral_supp : Tag.f_tag list ;
        (** General support tags *)
      supp_table : (E.pc_t*IGraph.premise_t, Tag.f_tag list) Hashtbl.t;
        (** Special cases support tags *)
    }

  type solver_info =
    {
      mutable prog_lines : int ;
      dp : dp_info;
      mutable cutoff : cutoff_type ;
      mutable out_file : string ;
      mutable detailed_desc : desc_t ;
      mutable focus : E.pc_t list;
      mutable hide_pres : bool;
      mutable count_abs : bool;
      mutable special : special_cases_form_tbl_t;
      mutable tactics : Tac.t;
    }
  
  type spinv_info_t =
    {
      ts : E.tid list;
      diff_conj : E.formula;
      psi : E.formula;
      psi_extra : E.formula;
      fresh_tid : E.tid;
      vs : E.tid list;
    }

  type premise_t = Normal | Extra
   
  (* Exceptions *)
  exception Invalid_argument
  exception Impossible_call of string
  exception Not_implemented of string
  
  (* Configuration *)
  let defFormulaTableSize = 200
  
  let countAbsVarName = "N"
  
  let solverInfo : solver_info = {
    prog_lines = 0;
    dp = { pos_dp  = false;
           tll_dp  = false;
           num_dp  = false;
           tsl_dp  = false;
           tslk_dp = (false, 0) };
    cutoff = Dnf;
    out_file = "";
    detailed_desc = {detFolder = ""; detProg = ""; detInv = "";
                     gral_supp = []; supp_table = Hashtbl.create 10; };
    focus = [];
    hide_pres = false;
    count_abs = false;
    special = Hashtbl.create 10;
    tactics = Tac.new_tactics (Some Tac.Dnf) None [] [];
  }
  
  (* This should not go here *)
  let cutoff ()    : cutoff_type = solverInfo.cutoff
  let out_file ()  : string      = solverInfo.out_file
  let hide_pres () : bool        = solverInfo.hide_pres
  let tactics ()   : Tactics.t   = solverInfo.tactics
  (* This should not go here *)
  
  (** Initialization status of the module. *)
  let initialized = ref false
  let setInitialized (status : bool) = initialized := status
  let isInitialized () = !initialized
  
  (** This module must be initialized using this function. Otherwise, it
      will not work properly. When not initialized, any call to a function 
      in this module will fail with an assertion failure.  *)
  let initialize 
        (pl : int) 
          (** Number of lines in the program. *)
        (co : cutoff_type) 
          (** Cutoff strategy to follow. *)
        (file : string)
          (** Output file. *)
        (focus : E.pc_t list)
          (** Program lines where the VCGen focuses.*)
        (hide_pres : bool) 
          (** Hides unmodified variables. *)
        (count_abs : bool) 
          (** Enables counting abstraction. *)
        : unit =
    begin
      solverInfo.prog_lines <- pl;
      solverInfo.cutoff <- co;
      solverInfo.out_file <- file;
      solverInfo.focus <- focus;
      solverInfo.hide_pres <- hide_pres;
      solverInfo.count_abs <- count_abs;
      setInitialized(true);
    end


  let set_descFolder (d:desc_t) (folder:string) : unit =
    (d.detFolder <- folder; d.detInv <- "")

  let set_descProg (d:desc_t) (prog:string) : unit =
    (d.detProg <- prog; d.detInv <- "")

  let set_descInv (d:desc_t) (inv:string) : unit =
    d.detInv <- inv

  let set_descGralSupp (d:desc_t) (ts:Tag.f_tag list) : unit =
    d.gral_supp <- ts

  let set_descSuppTbl (d:desc_t)
                      ((pos,prem):E.pc_t * IGraph.premise_t)
                      (ts:Tag.f_tag list) : unit =
    Hashtbl.add d.supp_table (pos,prem) ts


  let set_detFolder (folder:string) : unit =
    set_descFolder solverInfo.detailed_desc folder

  let set_detProbName (prog_name:string) : unit =
    set_descProg solverInfo.detailed_desc prog_name

  let set_detFileName (inv:string) : unit =
    set_descInv solverInfo.detailed_desc inv


  let set_cases (cases : (E.pc_t * IGraph.premise_t, E.formula list * Tac.t) 
      Hashtbl.t) : unit =
    solverInfo.special <- cases
  
  let set_tactics (tactics : Tac.t) : unit = 
    solverInfo.tactics <- tactics
  
  (* Tagging formula table *)
  let tags : Tag.tag_table = Tag.tag_table_new
  
  let tags_num () : int = Tag.tag_table_size tags
  
  let decl_tag (t : Tag.f_tag option) (phi : E.formula) : unit =
    match t with
    | None -> ()
    | Some tag -> if Tag.tag_table_mem tags tag
        then
          RAISE(Tag.Duplicated_tag(Tag.tag_id tag))
        else Tag.tag_table_add tags tag phi Tag.new_info
  
  let read_tag (t : Tag.f_tag) : E.formula option =
    if Tag.tag_table_mem tags t then
      Some (Tag.tag_table_get_formula tags t)
    else None
  
  let is_def_tag (t:Tag.f_tag) : bool =
    Tag.tag_table_mem tags t
  
  (* Decision procedures *)
  let none_dp (unit) : dp_info =
    {
      pos_dp  = false;
      tll_dp  = false;
      num_dp  = false;
      tsl_dp  = false;
      tslk_dp = (false,0);
    }
  
  let enable_num_dp () : unit =
    assert(isInitialized());
    solverInfo.dp.pos_dp <- true;
    solverInfo.dp.num_dp <- true;
    LOG "Enabled num DP." LEVEL DEBUG
  
  let enable_tll_dp () : unit =
    assert(isInitialized());
    solverInfo.dp.pos_dp <- true;
    solverInfo.dp.tll_dp <- true;
    LOG "Enabled tll DP." LEVEL DEBUG

  let enable_tsl_dp () : unit =
    assert(isInitialized());
    solverInfo.dp.pos_dp  <- true;
    solverInfo.dp.tsl_dp <- true;
    LOG "Enabled tsl DP." LEVEL DEBUG

  let enable_tslk_dp (k:int) : unit =
    assert(isInitialized());
    solverInfo.dp.pos_dp  <- true;
    solverInfo.dp.tslk_dp <- (true,k);
    LOG "Enabled tslk DP." LEVEL DEBUG
  
  let enable_dp : DP.t -> unit = function
    | DP.NoDP   -> ()
    | DP.Num    -> enable_num_dp ()
    | DP.Tll    -> enable_tll_dp ()
    | DP.Tsl    -> enable_tsl_dp ()
    | DP.Tslk k -> enable_tslk_dp k
  
  let some_dp_enabled () : bool =
    assert(isInitialized());
    solverInfo.dp.pos_dp        ||
    solverInfo.dp.num_dp        ||
    solverInfo.dp.tll_dp        ||
    solverInfo.dp.tsl_dp        ||
    fst (solverInfo.dp.tslk_dp)
  
  let apply_pos_dp () : bool =
    assert(isInitialized());
    LOG "Apply Pos DP? %b" solverInfo.dp.pos_dp LEVEL DEBUG;
    solverInfo.dp.pos_dp
  
  let apply_num_dp () : bool =
    assert(isInitialized());
    LOG "Apply Num DP? %b" solverInfo.dp.num_dp LEVEL DEBUG;
    solverInfo.dp.num_dp
  
  let apply_tll_dp () : bool =
    assert(isInitialized());
    LOG "Apply Tll DP? %b" solverInfo.dp.tll_dp LEVEL DEBUG;
    solverInfo.dp.tll_dp
  
  let apply_tsl_dp () : bool =
    assert(isInitialized());
    LOG "Apply Tsl DP? %b" solverInfo.dp.tsl_dp LEVEL DEBUG;
    solverInfo.dp.tsl_dp

  let apply_tslk_dp () : (bool * int) =
    assert(isInitialized());
    let (b,k) = solverInfo.dp.tslk_dp in
    LOG "Apply Tslk[%i] DP? %b" k b LEVEL DEBUG;
    (b, k)

  let apply_heap_based_dp () : bool =
    apply_tll_dp ()        ||
    fst (apply_tslk_dp ()) ||
    apply_tsl_dp ()


  (* MODE CONVERSION FUNCTION *)
  let rhoMode_to_sysMode : rhoMode -> Sys.sysMode = function
    | RClosed _ -> Sys.SClosed
    | ROpenArray (k,js) -> Sys.SOpenArray (k::js)
    | ROpenExt (k,js) -> Sys.SOpenArray (k::js)
  
  
  (* SATISFIABILITY STATUS PRINTER *)
  let valid_to_str : valid_t -> string = function
    | Unverified -> "[   ?   ]"
    | NotValid -> "[   X   ]"
    | CheckedLocation -> "[ OK(L) ]"
    | Checked -> "[  CHK  ]"
    | Unneeded -> "[   -   ]"
  
  
  (* PROGRAM COUNTER FUNCTIONS *)
  let build_curr_pc (th : E.tid) (p : E.pc_t) : E.formula =
  (* FIX: I have replaced all this code with the line below. Not sure if it works
          in all cases. For array representation of open systems is OK
  
    let pc_arr arr id = E.IntT(E.IntArrayRd(arr,id)) in
    let int_val i     = E.IntT(E.IntVal i) in
    let pc            = E.VarArray(E.pc_name,false,None,None,E.Normal) in
    let curr_pos      = int_val p in
    let curr_eq       = E.Literal(E.Eq(pc_arr pc th, curr_pos)) in
  *)
    let curr_eq       = E.Literal (E.Atom (E.PC(p, Some th, false))) in 
    curr_eq
  
  
  let build_next_pc (mode : Sys.sysMode) (th : E.tid) 
      (next_list : E.pc_t list) : E.formula =
    assert (List.length next_list > 0);
  (*  let primed_pc_name = E.prime_var_name E.pc_name in *)
  (* FIX: This was before having BPCUpdate. Check if it is alright.         *)
  (* let pc             = E.VarArray(E.pc_name,false,None,None,E.Normal) in *)
  
    let fst_next_pos = List.hd next_list in
    let build_eq' i = match mode with
      | Sys.SClosed -> E.pcupd_form i th
      (* FIX: This was before having PCUpdate. Check if it is alright *)
      (* E.eq_int (E.IntArrayRd(pc',th)) (E.IntVal i) *)
      | Sys.SOpenArray _ -> E.pcupd_form i th in
      (* FIX: This was before having BPCUpdate. Check if
              it is alright.
        let primed_arr = E.ArrayT pc' in
        let new_pos p  = E.Term(int_val p)in
        let upd_arr p  = E.ArrayT
          (E.ArrayUp(pc,th,new_pos p)) in
        E.Literal(E.Eq(primed_arr,upd_arr i)) in
      *)
    let fst_eq = build_eq' fst_next_pos in
    let next_eq = List.fold_left (fun b p -> E.Or (build_eq' p,b))
      (fst_eq) (List.tl next_list) in
    next_eq
  
  
  let build_pres_pc (mode : Sys.sysMode) 
      (th_list : E.tid list) : E.formula list = match mode with
    | Sys.SClosed -> (* Deprecated *)
        let pc = E.VarArray
          (E.build_var E.pc_name E.Unknown false None None E.Normal) in
        let pc' = E.VarArray
          (E.build_var E.pc_name E.Unknown true None None E.Normal) in
        let pc_arr arr id  = E.IntArrayRd(arr,id) in
        let eq_list = List.map 
          (fun i -> E.eq_int (pc_arr pc' i) (pc_arr pc i)) th_list in
        eq_list
    | Sys.SOpenArray _ -> []
  
  
  let build_pc (mode : rhoMode) (now : E.pc_t)
      (next_list : E.pc_t list) : E.formula list =
    let curr_th, other_ths = match mode with
      | RClosed (k,m) -> (k, E.gen_thread_list_except 1 m k)
      | ROpenArray (k,js) -> (k, js)
      | ROpenExt (k,js) -> (k, js) in
    let sMode = rhoMode_to_sysMode mode in
    let curr_eq = build_curr_pc curr_th now in
    let next_eq = build_next_pc sMode curr_th next_list in
    let pres_eq = build_pres_pc sMode other_ths in
    curr_eq :: next_eq :: pres_eq
  
  (* VARIABLE PRESERVATION FUNCTIONS *)
  let gen_pres (p_name : string) (gs : E.TermSet.t) (ls : E.TermSet.t)
      (os : (string * E.TermSet.t) list) (ts : E.TermSet.t)
      (mode : rhoMode) : E.formula list =
    let gTermConj = E.TermSet.fold 
      (fun x l -> (E.construct_pres_term x None) :: l) gs [] in
    let lTermConj = match mode with
      | RClosed (k,_) -> E.TermSet.fold 
          (fun x l -> (E.construct_pres_term x (Some k))::l) ls []
      | ROpenArray _ -> E.TermSet.fold 
          (fun x bs -> (E.construct_pres_term x None)::bs) ls []
      | ROpenExt _ -> [] in
    let oTermConj = match mode with
      | RClosed (k, th_num) -> 
          let th_list = E.gen_thread_list 1 th_num in
          let f p x bs i = if (i<>k || p<>p_name) then
              (E.construct_pres_term x (Some i))::bs
            else bs in
          let g p x l =
              List.fold_left (f p x) [] th_list @ l in
          let h (p, ts) =
            E.TermSet.fold (g p) ts [] in
          List.flatten $ List.map h os
      | ROpenArray _ ->
          List.flatten $ List.map 
          (fun (_,ts) -> E.TermSet.fold 
            (fun x bs -> (E.construct_pres_term x None)::bs) 
            ts []) 
          os
      | ROpenExt (k, ks) ->
          let f x bs = 
            let constr_pt t = E.construct_pres_term x (Some t) in
            let curr_pres = constr_pt k in
            let others_pres = List.map constr_pt ks in 
            curr_pres :: (others_pres @ bs) in
          List.flatten $ List.map (fun (_,ts) -> E.TermSet.fold f ts []) os in
    let thTermConj = 
      E.TermSet.fold (fun x l -> (E.construct_pres_term x None) :: l) ts [] in
    gTermConj @ lTermConj @ oTermConj @ thTermConj
  
  
  let get_mode_param : rhoMode -> E.tid = function
    | RClosed (t,_) -> t
    | ROpenArray (t,_) -> t
    | ROpenExt (t,_) -> t
  
  (* INITIAL CONDITION AUXILIARY FUNCTIONS *)
  let gen_global_init_cond (sys : Sys.system_t) : E.formula list =
    let gVars = Sys.get_global sys in
    let conds = Hashtbl.fold 
      (fun v info xs -> (E.assign_var None v info) @ xs ) gVars [] in
    conds

  let gen_local_init_cond (sys : Sys.system_t) 
      (p_name : string) : E.formula list =
    let _, lVars = Sys.get_accvars_by_name sys p_name in
    let conds = Hashtbl.fold 
      (fun v info xs -> 
        let (s,e,_,k) = info in
        let new_info = (s,e,None,k) in
        (E.assign_var (Some p_name) v new_info) @ xs) 
      lVars [] in
    conds
  
  let gen_init_cond (sys : Sys.system_t) (p_name : string)
      (th_list : E.tid list) (loc : bool) : E.formula =
    let gConds = gen_global_init_cond sys in
    let lConds = gen_local_init_cond sys p_name in
    let full_lConds = match th_list with
      |  [] -> lConds
      | _  -> List.flatten $ List.map 
        (fun t -> let me_subst = E.new_tid_subst [(Sys.me_tid_th,t)]in
          List.map (fun c -> E.subst_tid me_subst (E.param (Some t) c)) lConds) 
        th_list in 
    E.conj_list (gConds @ full_lConds)

  (*
  let gen_init_cond (sys:Sys.system_t)
                    (p_name:string)
                    (th_list:E.tid list)
                    (loc:bool) : E.formula =
  
    let (gVars,lVars) = Sys.get_accvars_by_name sys p_name in
    let conds = ref [] in
    let _ = Hashtbl.iter (fun v info ->
              conds := (E.assign_var None v info) @ !conds) gVars in
    let add_local_cond param =
      Hashtbl.iter (fun v info ->
        let (s,e,_,k) = info in
          let new_info = (s,e,param,k) in
            conds := (E.assign_var (Some p_name) v new_info) @ !conds
      ) lVars in
    let _ = match th_list with
              [] -> add_local_cond None
            | _  -> List.iter (fun th_p -> add_local_cond (Some th_p)) th_list
    in
      E.conj_list !conds
  *)
  
  let gen_init_cond_as_array (sys : Sys.system_t) (p_name:string) 
      (th_list:E.tid list) : E.formula =
      let conds = ref [] in
      let gVars, lVars = Sys.get_accvars_by_name sys p_name in
      let _ = Hashtbl.iter 
        (fun v info -> conds := (E.assign_var None v info) @ !conds) gVars in
      let _ = List.iter 
        (fun th_p -> Hashtbl.iter 
          (fun v (s,e,_,k) ->
            let arr = E.VarArray(E.build_var v s false None (Some p_name) k) in
            let eq = E.cons_arrayRd_eq_from_var s th_p arr e in
            (* Obsolete code *)
            (* let arr = E.VarArray(v, None, Some p_name, k) in    *)
            (* let eq = E.cons_arrayRd_eq_from_var s th_p arr e in *)
            conds := eq @ !conds)
          lVars) 
        th_list in
      E.conj_list !conds
  
  (* RHO MODE DEFINITION FUNCTIONS *)
  let new_closed_mode (sys : Sys.system_t) (i : int) : rhoMode =
    let th_num = Sys.get_threads sys in
    if (i < 1 || i > th_num) then
      begin
        Interface.Err.msg "Out of bounds parameter" $
          sprintf "Thread identifier \"%i\" is out of the limits for \
            the a closed system, since a system with only %i \
            threads was declared." i th_num;
        RAISE(Invalid_argument)
      end
    else
      let th_p = E.build_num_tid i in
      RClosed (th_p, th_num)
  
  let new_open_array_mode (k : E.varId) (p_list : E.varId list) : rhoMode =
    let k_th = E.build_var_tid k in
    let other_th = List.map (fun i -> E.build_var_tid i) p_list in
    ROpenArray (k_th, other_th)
  
  let new_open_thid_array_mode (k:E.tid) (p_list:E.tid list) : rhoMode =
    ROpenArray (k, p_list)

  (* THETA FUNCTIONS *)
  let gen_theta (mode : Sys.sysMode) (sys : Sys.system_t) : E.formula =
    let main_proc = Sys.defMainProcedure in
    let param_list = match mode with
      | Sys.SClosed -> E.gen_thread_list 1 (Sys.get_threads sys)
      | Sys.SOpenArray xs -> xs in
    let main_fLine = Sys.get_fLine_by_name sys main_proc in
    let init_line = Pervasives.max 1 main_fLine in
    let init_pc_list = List.map (fun i->build_curr_pc i init_line) param_list in
    let init_pc_cond = E.conj_list init_pc_list in
    let prog_cond = gen_init_cond sys main_proc param_list true in
    let init_sys_cond = match Sys.get_assume sys with
      | None   -> prog_cond
      | Some c -> E.And(Stm.boolean_to_expr_formula c, prog_cond) in
    E.And (init_pc_cond, init_sys_cond)
  
  let gen_theta_with_count_abs (mode:Sys.sysMode)
      (sys:Sys.system_t) : E.formula =
    let theta_cond = gen_theta mode sys in
    let lines = rangeList 1 (Sys.get_trans_num sys + 1) in
    let main_fLine = Sys.get_fLine_by_name sys (Sys.defMainProcedure) in
    let full_cond = List.fold_left 
      (fun phi i -> if i = main_fLine then
          (* E.And (E.someone_at main_fLine, phi) *)
          E.And (E.eq_int (E.VarInt (E.countAbs_var i)) E.defCountVar, phi)
        else
          E.And (E.eq_int (E.VarInt (E.countAbs_var i)) (E.IntVal 0), phi)) 
      theta_cond lines in
    full_cond
  
  
  let gen_theta_general (mode:Sys.sysMode) (sys:Sys.system_t) 
      (count_abs:bool) : E.formula =
    if count_abs then gen_theta_with_count_abs mode sys
    else gen_theta mode sys
  
  
  (* TRANSITION RELATION FUNCTIONS *)
  let rec aux_rho_for_st
      (sys:Sys.system_t)
      (gSet:E.TermSet.t) (* Global accessible terms. *)
      (lSet:E.TermSet.t) (* Local accessible terms. *)
      (thSet:E.TermSet.t) (* Extra formula tids. *)
      (mode:rhoMode) (* System type. *)
      (st:Stm.statement_t) (* Generate rho for statem. *)
      (is_ghost:bool) (* Is ghost code? *)
      (count_abs:bool) (* Include counting abstraction? *)
      (mInfo:Bridge.malloc_info)
      (pt:Bridge.prog_type)
      : (E.TermSet.t * E.TermSet.t * E.TermSet.t * E.formula list list) =
    let conv_bool = Stm.boolean_to_expr_formula in
    let th_p = Some (get_mode_param mode) in
    let append_to_ghost gc gS lS tS (ps:E.formula list list) =
      match gc with
      | Some code -> 
          let eff_list = 
            Bridge.gen_st_cond_effect_as_array pt code true th_p in
          let rho_list = List.fold_left (fun xs (cond, eff, _, _) ->
                           (List.map (fun normal_code ->
                             (E.param th_p cond :: eff :: normal_code)
                            ) ps) @ xs
                         ) [] eff_list in
            (* URGENT FIX: Preservation when no -hp is used *)
          (E.TermSet.empty, E.TermSet.empty, E.TermSet.empty, rho_list)
      | None -> (gS, lS, tS, ps) in
    let make_pos_change c ns =
      let pc_change = build_pc mode c ns in
      let next_pos = 
        E.disj_list $ List.map (fun n -> E.build_pos_change c n) ns in
      if count_abs then [E.someone_at c; next_pos] @ pc_change
      else pc_change in
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
        let predF = 
          make_pos_change i.Stm.pos [i.Stm.pos] @ [E.param th_p (E.Not c')] in
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
    | Stm.StIf (c, t, e, g, Some i), false ->
        let c' = conv_bool c in
        let predT = make_pos_change i.Stm.pos [i.Stm.next_pos] @
                    [E.param th_p c'] in
        let predF = make_pos_change i.Stm.pos [i.Stm.else_pos] @
                    [E.param th_p (E.Not c')] in
        append_to_ghost g gSet lSet thSet [predT; predF]
    
    (************************ If @ghostLevel *******************************)
    | Stm.StIf (c, t, e, _, _), true -> (gSet, lSet, thSet, []) (* ????? *)
    
    (************************ While @topLevel ******************************)
    | Stm.StWhile (c, l, g, Some i), false ->
        let c' = conv_bool c in
        let predT = 
          make_pos_change i.Stm.pos [i.Stm.next_pos] @ [E.param th_p c'] in
        let predF = 
          make_pos_change i.Stm.pos [i.Stm.else_pos] 
          @ [E.param th_p (E.Not c')] in
        append_to_ghost g gSet lSet thSet [predT; predF]
     
    (************************ While @ghostLevel ****************************)
    | Stm.StWhile _, true -> (gSet, lSet, thSet, []) (* ????? *)
      
    (************************ Choice @topLevel *****************************)
    | Stm.StSelect (xs, g, Some i),  false ->
        let pred = make_pos_change i.Stm.pos i.Stm.opt_pos in
        append_to_ghost g gSet lSet thSet [pred]
    
    (************************ Choice  @ghostLevel **************************)
    | Stm.StSelect _,  true -> (gSet, lSet, thSet, []) (* ????? *)
    
    (************************ Assignment @anyLevel *************************)
    | Stm.StAssign (v, e, g, info), is_ghost ->
      let (gSet',lSet',thSet',equiv) =
        match mode with
        | RClosed _ ->
            let modif, equiv = 
              Bridge.construct_stm_term_eq mInfo pt v th_p e in
            let still_gSet = E.filter_term_set modif gSet in
            let still_lSet = E.filter_term_set modif lSet in
            let still_thSet = E.filter_term_set modif thSet in
            (still_gSet, still_lSet, still_thSet, equiv)
        | ROpenArray _ ->
            let (modif, equiv) = 
              Bridge.construct_stm_term_eq_as_array mInfo pt v th_p e in
            let still_gSet = E.filter_term_set modif gSet in
            let still_lSet = E.filter_term_set modif lSet in
            let still_thSet = E.filter_term_set modif thSet in
            (still_gSet, still_lSet, still_thSet, equiv)
        | ROpenExt _ ->
              (gSet, lSet, thSet, E.True) in
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
        | Stm.Lock   -> E.eq_tid (E.CellLockId cell) E.NoThid
        | Stm.Unlock -> 
            E.eq_tid (E.CellLockId cell) (Option.default E.NoThid th_p) in
      let new_tid  = match op with
        | Stm.Lock -> get_mode_param mode
        | Stm.Unlock -> E.NoThid in
      let mkcell = E.MkCell (E.CellData (E.CellAt (E.heap, a)), 
        E.Next (E.CellAt (E.heap, a)), new_tid) in
      let upd = E.eq_mem (E.prime_mem E.heap) (E.Update (E.heap, a, mkcell)) in
      let modif = [E.MemT E.heap] in
      let (gSet',lSet',thSet') = begin
        match mode with
        | RClosed _ ->
            let still_gSet  = E.filter_term_set (modif) gSet in
            let still_lSet  = E.filter_term_set (modif) lSet in
            let still_thSet = E.filter_term_set (modif) thSet in
              (still_gSet, still_lSet, still_thSet)
        | ROpenArray _ ->
            let still_gSet  = E.filter_term_set (modif) gSet in
            let still_lSet  = E.filter_term_set (modif) lSet in
            let still_thSet = E.filter_term_set (modif) thSet in
              (still_gSet, still_lSet, still_thSet)
        | ROpenExt _ ->
              (gSet, lSet, thSet)
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
            aux_rho_for_st sys g l t mode cmd is_ghost count_abs mInfo pt in
          (gS, lS, tS, fS@fs) in
        List.fold_left f (gSet, lSet, thSet, []) xs
        
    (************************ Ill-formed statements ************************)
    | Stm.StAtomic (xs, g, Some i), false ->
        let eff_list = Bridge.gen_st_cond_effect_as_array pt st false th_p in
        let f (cond, eff, c, n) = 
          let pos_change = make_pos_change c [n] in
          [E.conj_list (pos_change @ [E.param th_p cond; eff])] in
        let rho_list = List.map f eff_list in
        (E.TermSet.empty, E.TermSet.empty, E.TermSet.empty, rho_list)
    (************************ Call @topLevel *******************************)
    | Stm.StCall (t,proc_name,ps,gc,Some i), false ->
        (* We make the argument assignment *)
        let (modif_list, equiv_list) =
          match mode with
          | ROpenExt _ -> ([], [])
          | _ -> let gen_f = match mode with
                             | RClosed _ -> Bridge.construct_stm_term_eq
                             | _ -> Bridge.construct_stm_term_eq_as_array in
                 let call_proc_args = Sys.proc_info_get_args
                                        (Sys.get_proc_by_name sys proc_name) in
                 let assignments = List.combine call_proc_args ps
                 in
                   List.fold_left (fun (ms,es) ((arg,arg_sort),value) ->
                     let v = Stm.VarT (Stm.build_var arg arg_sort
                                          (Some proc_name) E.Normal) in
                     let (m,e) = gen_f mInfo pt v th_p (Stm.Term value)
                     in
                       (m@ms, e::es)
                   ) ([],[]) assignments in
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
                                     RAISE(Impossible_call proc_name)
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
              let _ = printf "Going to process term: %s\n" (Stm.term_to_str t) in
              begin
                match mode with
                | ROpenExt _ -> (gSet, lSet, thSet, E.True)
                | _          ->
                  begin
                    let ret_pos = i.Stm.called_from_pos in
                    let _ = printf "RETPOS: %s\n" (String.concat ";" $ List.map string_of_int ret_pos) in
                    let (modif,equiv) =
                      List.fold_left (fun (ms,es) pos ->
                        let call_stm = Sys.get_statement_at sys pos in
                        match call_stm with
                        | (_, Stm.StCall (Some ret_t, _,_,_,_)) ->
                          begin
                            let (k,(m,e)) =
                              match mode with
                              | RClosed (k,_)    ->
                                  (k, Bridge.construct_stm_term_eq
                                        mInfo pt ret_t th_p (Stm.Term t))
                              | ROpenArray (k,_) ->
                                  (k, Bridge.construct_stm_term_eq_as_array
                                        mInfo pt ret_t th_p (Stm.Term t))
                              | _ -> RAISE(Not_implemented
                                              "Extra case on return statement") in
                            let sMode = rhoMode_to_sysMode mode in
                            let pos_assignment =
                              E.Implies (build_next_pc sMode k [pos], e) in
                            (m@ms, pos_assignment::es)
                          end
                        | _ -> (ms,es)
                      ) ([],[]) ret_pos in
                    let still_gSet = E.filter_term_set modif gSet in
                    let still_lSet = E.filter_term_set modif lSet in
                    let still_thSet = E.filter_term_set modif thSet in
                    (still_gSet, still_lSet, still_thSet, E.conj_list equiv)
                  end
              end
          (* No return value *)
          | None   -> (gSet, lSet, thSet, E.True) in
        let pred = (make_pos_change i.Stm.pos i.Stm.return_pos) @ [equiv] in
        append_to_ghost gc gSet' lSet' thSet' [pred]
    | _ -> (gSet, lSet, thSet, [])

  
  let rho_for_st (sys : Sys.system_t)
      (mode : rhoMode) (* System type *)
      (hide_pres : bool) (* Hide preserve relation *)
      (count_abs : bool) (* Include counting abstraction *)
      (th_list : E.tid list) (* New formula parameters *)
      (p : E.pc_t) (* Statement position *)
      : E.formula list =
    LOG "Entering rho_for_st..." LEVEL TRACE;
    let gSet = Sys.gen_global_vars_as_terms sys in
    let (proc,st) = Sys.get_statement_at sys p in
    (* let remLocList = List.remove_assoc proc allLocList in *)
    let thSet = 
      E.construct_term_set $ List.map (fun x -> E.ThidT x) th_list in
  
    (* For Malloc -- BEGIN *)
    let is_sort s v = (E.var_sort v = s) in
    let gVars = Sys.get_variable_list (Sys.get_global sys) in
    let lVars = Sys.get_all_local_vars sys in
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
    let pt = if Sys.mem_var (Sys.get_global sys) Sys.heap_name then
      Bridge.Heap
    else Bridge.Num in
    (* For Malloc -- END *)
  
    let all_local, filtered_local = match mode with
      | RClosed _ ->  let ls = Sys.gen_local_vars_as_terms sys in (ls,ls)
      | ROpenArray _ -> 
          let ls = Sys.gen_local_vars_as_array_terms sys in
          (ls, List.remove_assoc proc ls)
      | ROpenExt _ -> ([], []) in
    let lSet = List.assoc proc all_local in
    let (gSet',lSet',thSet',rhoList) =
      aux_rho_for_st sys gSet lSet thSet mode st false count_abs mInfo pt in
    let phi_list = 
      if hide_pres then rhoList
      else begin
        match st with
        (* If atomic statement, I need to generate the preservation
           for each list of conjunctions separately *)
        | Stm.StAtomic _ -> 
            let f xs = 
              let phi = E.conj_list xs in
              let f' v = E.ArrayT (E.VarArray (E.var_clear_param_info v)) in
              let p_vars = List.map f' (E.primed_vars phi) in
              let gSet' = E.filter_term_set p_vars gSet in
              let lSet' = E.filter_term_set p_vars lSet in
              let thSet' = E.filter_term_set p_vars thSet in
              let pres = 
                gen_pres proc gSet' lSet' filtered_local thSet' mode in
              (phi::pres) in
            List.map f rhoList
        (* Otherwise, I already have the terms to be preserved *)
        | _ -> 
            let pres_list = 
              gen_pres proc gSet' lSet' filtered_local thSet' mode in
            List.map (fun x -> x @ pres_list) rhoList 
      end in
      List.map E.conj_list phi_list
  
  
  let gen_rho (mode : rhoMode) (hide_pres:bool) (count_abs : bool)
      (sys : Sys.system_t) (th_list : E.tid list)
      (p : E.pc_t) : E.formula list =
    LOG "Entering gen_rho..." LEVEL TRACE;
    rho_for_st sys mode hide_pres count_abs th_list p
      
  let gen_all_transitions (sys:Sys.system_t) : (E.pc_t * E.formula list) list =
    let lines = LeapLib.rangeList 1 (Sys.get_trans_num sys) in
    let simple_mode = ROpenArray (E.build_var_tid "i", []) in
    List.map (fun pc -> (pc, gen_rho simple_mode false false sys [] pc)) lines
  
  let all_transitions_to_str (sys:Sys.system_t) : string =
    let info_list = gen_all_transitions sys in
    String.concat "\n------\n" $
    List.map 
      (fun (pc,fs) -> 
        sprintf "line %i\n%s" 
          pc (String.concat "\n" $ List.map E.formula_to_str fs)) 
      info_list
  
  (* VCGEN FOR INVARIANT ON A CLOSED SYSTEM *)
  let vcgen_closed (hide_pres:bool)
                   (count_abs:bool)
                   (sys:Sys.system_t)
                      : (int * E.pc_t * E.formula list) list =
    let th_list    = LeapLib.rangeList 1 (Sys.get_threads sys) in
    let trans_list = LeapLib.rangeList 1 (Sys.get_trans_num sys) in
    let rho_list   = List.flatten $
                       List.map (fun t ->
                         List.map (fun p ->
                           let mode = new_closed_mode sys t in
  (* FIX: Maybe the function should get a list of tids *)
                             (t, p, gen_rho mode hide_pres count_abs sys [] p)
                         ) trans_list) th_list
    in
      rho_list
  
  
  let vcgen_open_inv (hide_pres:bool)
                     (count_abs)
                     (sys:Sys.system_t)
                        : (int * E.pc_t * E.formula list) list =
    let trans_list = LeapLib.rangeList 1 (Sys.get_trans_num sys) in
    (* TODO: Make all possible arrangements with info get from inv candidate *)
    let mode       = new_open_array_mode "k" ["i"; "j"] in
  (* FIX: Maybe the function should get a list of tids *)
    let rho_list = List.map (fun p ->
                     (0, p, gen_rho mode hide_pres count_abs sys [] p)
                   ) trans_list
    in
      rho_list
  
  
  (* Support generation. Not currently used in SP-INV rule generator *)
  let support (sup_list:E.formula list)
              (ante:E.formula)
              (cons:E.formula)
              (ext_sup:bool) : E.formula =
    let implication  = E.Implies(ante, cons) in
    let all_sup_list = if ext_sup then implication :: sup_list else sup_list in
    let voc_formula  = List.filter E.is_tid_var (E.unprimed_voc implication) in
  
    (* Replace supporting formula parameters by fresh ones *)
    let (new_sup,vs) = List.fold_left(fun (fs, vs) f ->
                         let f_voc   = E.voc f in
                         let new_ths = E.gen_fresh_thread_list
                                         (voc_formula @ vs) (List.length f_voc) in
                         let subst   = E.new_tid_subst
                                         (List.combine f_voc new_ths) in
                         let new_f   = E.subst_tid subst f
                         in
                           (new_f :: fs, new_ths@vs)
                       ) ([],[]) all_sup_list in
    let sup          = E.conj_list new_sup in
    let voc_sup      = List.filter E.is_tid_var (E.voc sup) in
    let subst        = E.new_comb_subst voc_sup voc_formula in
    let psi          = E.conj_list $ sup :: List.map (fun s ->
                                              E.subst_tid s sup
                                            ) subst
    in
      E.Implies (E.And (psi,ante), cons)
  
  
  let tag_support (sup_list:Tag.f_tag list)
                  (ante:E.formula)
                  (cons:E.formula)
                  (ext_sup:bool) : E.formula =
    let sup_list_as_formula = List.map (Tag.tag_table_get_formula tags) sup_list
    in
      support sup_list_as_formula ante cons ext_sup
    
  
  (* Invariant vcgen for closed systems *)
  let binv (sys : Sys.system_t) 
      (inv : E.formula) : (E.formula * vc_info_t) list =
    let v = E.voc inv in
    let th_list = List.filter E.is_tid_var v in
    let th_num = Sys.get_threads sys in
    let th_id_list = E.gen_thread_list 1 th_num in
    let _ = Printf.printf "LIST: [%s]\n" (String.concat ";" (List.map E.tid_to_str th_id_list)) in
    let prog_lines = List.filter (fun x -> x <> 0) solverInfo.focus in
    let len_voc = List.length th_list in
    let thList = E.voc inv in
    let loc_inv = if th_num = 1 then E.param (Some (List.hd th_id_list)) inv else inv in
    let inv_list =
      if len_voc = 0 then
        [(loc_inv, E.prime loc_inv)]
      else begin
        let comb_list = LeapLib.comb th_id_list len_voc in
        let subst_list = List.map (fun x ->
                           E.new_tid_subst (List.combine th_list x)
                         ) comb_list
        in
          List.map (fun x ->
            let i = E.subst_tid x loc_inv
            in
              (i, E.prime i)
          ) subst_list
      end in
    let theta = gen_theta_general Sys.SClosed sys solverInfo.count_abs in
    let init_conds =
      if List.mem 0 solverInfo.focus then
        List.map (fun x ->
          let vc_info = {pc = 0; smp = cutoff(); stac = None; supps=[]; } in
            (E.Implies(theta, fst x), vc_info)
        ) inv_list
      else [] in
    let tran_conds = ref [] in
    let _ = List.iter (fun f ->
              List.iter (fun l ->
                List.iter (fun i ->
                  let rho = gen_rho (RClosed (i, th_num)) solverInfo.hide_pres
                                     solverInfo.count_abs sys thList l in
                  List.iter (fun r ->
                    let antecedent = E.And (fst f, r) in
                    let consequent = if solverInfo.hide_pres then
                                       E.prime_modified antecedent (fst f)
                                     else
                                      snd f in
                    let new_vc = E.Implies (antecedent, consequent) in
                    let vc_info = {pc = l; smp = cutoff(); stac = None; supps=[];}
                    in
                      tran_conds := (new_vc, vc_info) :: !tran_conds
                  ) rho
                ) th_id_list
              ) prog_lines
            ) inv_list
    in
      init_conds @ List.rev(!tran_conds)

      
  let tag_binv (sys:Sys.system_t)
               (inv:Tag.f_tag) : (E.formula * vc_info_t) list =
    let inv_as_formula = Tag.tag_table_get_formula tags inv
    in
      binv sys inv_as_formula

  
  let spinv_premise_init (sys:Sys.system_t)
                         (inv:E.formula_info_t) : E.formula * vc_info_t =
    (* Initial condition *)
    let theta = gen_theta_general
                  (Sys.SOpenArray inv.E.voc) sys solverInfo.count_abs in
    let vc_info = {pc   = 0;
                   smp  = solverInfo.cutoff;
                   stac = Tac.solve_tactic solverInfo.tactics;
                   supps= [];} in
    let init_cond = (E.Implies (theta, inv.E.formula), vc_info)
    in
      init_cond
  
  (* Generates the support invariant for the normal and extra case,
   in addition to the conjunction of tid difference *)
  let gen_general_support_info (sys : System.system_t) 
      (supInvs : E.formula list) (inv : E.formula_info_t) : spinv_info_t =
        
    (* All parametrized formulas used for support *)
    let param_sup_list = match inv.E.voc with
      | [] -> supInvs
      | _  -> inv.E.formula :: supInvs in
    (* let param_sup = E.conj_list param_sup_list in *)
    
  
    (* Replace invariant parameters by fresh ones *)
    let (new_supInv,vs) = 
      let h (fs, vs) f = 
        let f_voc = E.voc f in
        let new_ths = E.gen_fresh_thread_list
          (inv.E.voc @ vs) (List.length f_voc) in
        let subst = E.new_tid_subst (List.combine f_voc new_ths) in
        let new_f = E.subst_tid subst f in
        (new_f :: fs, new_ths@vs) in
      List.fold_left h ([],[]) param_sup_list in
  
    (* New support formula with threads ids renamed *)
    let supInv = E.conj_list new_supInv in

    (* Vocabulary of the support and a fresh tid for extra premise *)
    let voc_sup    = List.filter E.is_tid_var (E.voc supInv) in
    let fresh_tid  = E.gen_fresh_thread vs in

    (* Generates the conjunction of thid disjunctions *)
    let diff_conj  = E.conj_list $ List.map (fun j -> E.ineq_tid fresh_tid j) inv.E.voc in

    (* Construct the substitutions for support renaming *)
    let subst_normal = E.new_comb_subst voc_sup inv.E.voc in
    let subst_with_fresh = E.new_comb_subst voc_sup (fresh_tid::inv.E.voc) in
    
    (* All normal supports with partial tid substitution *)
    let supInv_normal = 
      E.conj_list (List.map (fun s -> E.subst_tid s supInv) subst_normal) in

    (* All extra support with partial tid substitution *)
    let supInv_extra = E.conj_list 
      (supInv :: List.map (fun s -> E.subst_tid s supInv) subst_with_fresh) in

    let (psi,psi_extra) = match inv.E.voc with
      | [] -> 
        (E.And (inv.E.formula, supInv_normal), 
         E.And (inv.E.formula, supInv_extra))
      | _  -> (supInv_normal, supInv_extra) in
    
    let ts = inv.E.voc @ voc_sup in
    begin
      Printf.printf "TS: %s\n" (String.concat "," $ List.map E.tid_to_str ts);
      Printf.printf "VS: %s\n" (String.concat "," $ List.map E.tid_to_str vs);
      {
        ts = ts;
        diff_conj = diff_conj ;
        psi = psi;
        psi_extra = psi_extra;
        fresh_tid = fresh_tid;
        vs = vs;
      }
    end
  
  
  (* HERE GOES THE NEW CODE *)

  let vcgen_to_smp_cutoff (smp:cutoff_type) : Smp.cutoff_strategy =
    match smp with
    | Dnf     -> Smp.Dnf
    | Union   -> Smp.Union
    | Pruning -> Smp.Pruning


  let tac_to_vcgen_cutoff (smp:Tac.smp_tactic_t) : cutoff_type =
    match smp with
    | Tac.Dnf     -> Dnf
    | Tac.Union   -> Union
    | Tac.Pruning -> Pruning


  let cutoff_to_str (smp:cutoff_type) : string =
    match smp with
    | Dnf     -> "dnf"
    | Union   -> "union"
    | Pruning -> "pruning"
 
 
  let gen_vcs (sys : System.system_t)
              (supp_info : Tac.support_info_t)
              (inv : E.formula_info_t)
              (spec_stac:Tac.solve_tactic_t option)
              (spec_cutoff:cutoff_type)
              (tacs : Tac.post_tac_t list)
              (line : E.pc_t)
              (trans_tid : E.tid)
              (premise : premise_t) : (E.formula * vc_info_t) list =
    LOG "Entering gen_vcs..." LEVEL TRACE;
    let me_subst = E.new_tid_subst [(Sys.me_tid_th, trans_tid)] in
    let rho = gen_rho (ROpenArray (trans_tid, inv.E.voc)) solverInfo.hide_pres 
      solverInfo.count_abs sys (Tac.supp_voc supp_info @ inv.E.voc) line in
    List.fold_left (fun rs r ->
      let r_final = E.subst_tid me_subst r in
      let prem = match premise with
       | Normal -> None
       | Extra  -> Some (Tac.diff_conj supp_info) in
      let supp = match premise with
       | Normal -> Tac.supp_list supp_info
       | Extra  -> Tac.extra_supp_list supp_info in
      let task = Tac.new_task supp prem r_final inv
        (Tac.supp_voc supp_info) trans_tid line in
      let new_vcs = Tac.apply_post_tacs [task] tacs (hide_pres()) in
      let vc_info = {pc = line; smp = spec_cutoff; stac = spec_stac; supps=[];}
      in
        (List.map (fun phi -> (E.cleanup phi, vc_info)) new_vcs) @ rs
    ) [] rho

  
  let spinv_premise_transitions (sys : Sys.system_t)
                                (lines_to_consider : int list)
                                (supInvs : E.formula list)
                                (inv : E.formula_info_t)
                                  : (E.formula * vc_info_t) list =
    LOG "Entering spinv_premise_transitions..." LEVEL TRACE;
    let basic_supp = inv.E.formula :: supInvs in
    let general_supp_info = Tac.gen_support basic_supp inv.E.voc 
      (Tac.pre_tacs solverInfo.tactics) in
    
    let load_info (line : E.pc_t) (p : IGraph.premise_t) :
          (Tag.f_tag list          *
           Tac.smp_tactic_t option *
           Tac.support_info_t      *
           Tac.post_tac_t list     *
           Tac.solve_tactic_t option) =
      try
        let (supp, tacs) = Hashtbl.find solverInfo.special (line, p) in
        let supp_tags = Hashtbl.find solverInfo.detailed_desc.supp_table (line,p) in
        let final_tacs = Tac.specialize_tacs solverInfo.tactics tacs in
        let special_supp = Tac.gen_support (basic_supp @ supp)
                             inv.E.voc (Tac.pre_tacs final_tacs)
        in
          (supp_tags,
           Tac.smp_cutoff final_tacs,
           special_supp,
           Tac.post_tacs final_tacs,
           Tac.solve_tactic final_tacs)
      with
        Not_found -> ([],
                      Tac.smp_cutoff solverInfo.tactics,
                      general_supp_info,
                      Tac.post_tacs solverInfo.tactics,
                      Tac.solve_tactic solverInfo.tactics) in
    let assign_cutoff (smp:Tac.smp_tactic_t option) : cutoff_type =
      match smp with
      | None -> solverInfo.cutoff
      | Some cut -> tac_to_vcgen_cutoff cut
    in
      List.fold_left (fun vcs line ->
        let (n_tags, tmp_n_smp, normal_info, n_tacs, n_stac) =
          load_info line IGraph.Normal in
        let (e_tags, tmp_e_smp, extra_info, e_tacs, e_stac) =
          load_info line IGraph.Extra in
        let (n_smp, e_smp) = (assign_cutoff tmp_n_smp,
                              assign_cutoff tmp_e_smp) in
        let normal_vc = List.fold_left (fun norm_vcs i ->
                          norm_vcs @ gen_vcs sys normal_info inv n_stac
                                       n_smp n_tacs line i Normal
                        ) [] inv.E.voc in
        let extra_vc = gen_vcs sys extra_info inv e_stac e_smp e_tacs line
                        (Tac.supp_fresh_tid extra_info) Extra in
        (* Update support tags information *)
        let normal_vc = List.map (fun (phi,info) ->
                          (info.supps <- n_tags; (phi,info))) normal_vc in
        let extra_vc = List.map (fun (phi,info) ->
                          (info.supps <- e_tags; (phi,info))) extra_vc in
        vcs @ normal_vc @ extra_vc
      ) [] lines_to_consider


  let seq_binv (sys : Sys.system_t) (inv : E.formula)
        : (E.formula * vc_info_t) list =
    LOG "Entering seq_binv..." LEVEL TRACE;
    (* TODO: FIX THIS NOT TO USE DIRECTLY BINV *)
    binv sys inv
  

  let tag_seq_binv (sys : Sys.system_t) (inv : Tag.f_tag)
        : (E.formula * vc_info_t) list =
    let inv_as_formula = Tag.tag_table_get_formula tags inv in
    seq_binv sys inv_as_formula


  let seq_gen_vcs (sys : System.system_t)
                  (inv : E.formula_info_t)
                  (supInvs : E.formula list)
                  (spec_stac:Tac.solve_tactic_t option)
                  (spec_cutoff:cutoff_type)
                  (tacs : Tac.post_tac_t list)
                  (line : E.pc_t) : (E.formula * vc_info_t) list =
    LOG "Entering seq_gen_vcs..." LEVEL TRACE;
    assert (List.length inv.E.voc = 1);
    let trans_tid = List.hd inv.E.voc in
    let rho = gen_rho (ROpenArray (trans_tid, inv.E.voc))
                      solverInfo.hide_pres solverInfo.count_abs sys
                      inv.E.voc line in
    List.fold_left (fun rs r ->
      let all_voc = E.voc (E.conj_list (inv.E.formula :: supInvs)) in
      let task = Tac.new_task supInvs None r inv all_voc trans_tid line in
      let new_vcs = Tac.apply_post_tacs [task] tacs (hide_pres()) in
      let vc_info = {pc = line; smp = spec_cutoff; stac = spec_stac; supps=[];}
      in
        (List.map (fun phi -> (E.cleanup phi, vc_info)) new_vcs) @ rs
    ) [] rho


  let seq_spinv_premise_transitions (sys : Sys.system_t)
                                    (lines_to_consider : int list)
                                    (supInvs : E.formula list)
                                    (inv : E.formula_info_t)
                                      : (E.formula * vc_info_t) list =
    LOG "Entering seq_spinv_premise_transitions..." LEVEL TRACE;
    let load_info (line : E.pc_t) :
          (Tag.f_tag list          *
           Tac.smp_tactic_t option *
           Tac.post_tac_t list     *
           Tac.solve_tactic_t option) =
      try
        let p = IGraph.Normal in
        let (supp, tacs) = Hashtbl.find solverInfo.special (line, p) in
        let supp_tags = Hashtbl.find solverInfo.detailed_desc.supp_table (line,p) in
        let final_tacs = Tac.specialize_tacs solverInfo.tactics tacs
        in
          (supp_tags,
           Tac.smp_cutoff final_tacs,
           Tac.post_tacs final_tacs,
           Tac.solve_tactic final_tacs)
      with
        Not_found -> ([],
                      Tac.smp_cutoff solverInfo.tactics,
                      Tac.post_tacs solverInfo.tactics,
                      Tac.solve_tactic solverInfo.tactics) in
    let assign_cutoff (smp:Tac.smp_tactic_t option) : cutoff_type =
      match smp with
      | None -> solverInfo.cutoff
      | Some cut -> tac_to_vcgen_cutoff cut
    in
      List.fold_left (fun vcs line ->
        let (tags, tmp_smp, tacs, stac) = load_info line in
        let smp = assign_cutoff tmp_smp in

        let new_vc = List.map (fun (phi,info) ->
                       (info.supps <- tags; (phi,info)))
                         (seq_gen_vcs sys inv supInvs stac smp tacs line) in

        vcs @ new_vc
      ) [] lines_to_consider


  let seq_spinv (sys : Sys.system_t) (supInvs:E.formula list)
      (inv : E.formula) : (E.formula * vc_info_t) list =
    LOG "Entering seq_spinv..." LEVEL TRACE;
    let fresh_th = E.gen_fresh_thread (E.voc (E.conj_list (inv::supInvs))) in
    let loc_inv = E.param (Some fresh_th) inv in
    let loc_supInvs = List.map (E.param (Some fresh_th)) supInvs in

    let need_theta = List.mem 0 solverInfo.focus in
    let lines_to_consider = List.filter (fun x -> x <> 0) solverInfo.focus in
    let inv_info = E.new_formula_info loc_inv in
   
    let premise_init = if need_theta then
                         [spinv_premise_init sys inv_info]
                       else
                         [] in

    let premise_transitions = seq_spinv_premise_transitions sys
                                lines_to_consider loc_supInvs inv_info in
      premise_init @ premise_transitions

 
  let tag_seq_spinv (sys : Sys.system_t) (supInv_list : Tag.f_tag list)
      (inv : Tag.f_tag) : (E.formula * vc_info_t) list =
    let supInv_list_as_formula = 
      List.map (Tag.tag_table_get_formula tags) supInv_list in
    let inv_as_formula = Tag.tag_table_get_formula tags inv in
    seq_spinv sys supInv_list_as_formula inv_as_formula

  
  let spinv (sys : Sys.system_t) (supInvs:E.formula list)
      (inv : E.formula) : (E.formula * vc_info_t) list =
    LOG "Entering spinv..." LEVEL TRACE;
(*    let voc_inv = List.filter E.is_tid_var (E.voc inv) in *)
    let need_theta = List.mem 0 solverInfo.focus in
    let lines_to_consider = List.filter (fun x -> x <> 0) solverInfo.focus in
    let inv_info = E.new_formula_info inv in
   
    let premise_init = if need_theta then
                         [spinv_premise_init sys inv_info]
                       else
                         [] in

    let premise_transitions = spinv_premise_transitions sys
                                lines_to_consider supInvs inv_info in
      premise_init @ premise_transitions

 
  let tag_spinv (sys : Sys.system_t) (supInv_list : Tag.f_tag list)
      (inv : Tag.f_tag) : (E.formula * vc_info_t) list =
    let supInv_list_as_formula = 
      List.map (Tag.tag_table_get_formula tags) supInv_list in
    let inv_as_formula = Tag.tag_table_get_formula tags inv in
    spinv sys supInv_list_as_formula inv_as_formula
    
  
  let pinv_plus (sys : Sys.system_t)
      (inv : E.formula) : (E.formula * vc_info_t) list =
    LOG "Entering pinv_plus..." LEVEL TRACE;
    spinv sys [] inv
  
  
  let tag_pinv_plus (sys : Sys.system_t)
      (inv : Tag.f_tag) : (E.formula * vc_info_t) list =
    let inv_as_formula = Tag.tag_table_get_formula tags inv in
    pinv_plus sys inv_as_formula
  
  
  let pinv (sys : Sys.system_t) 
      (inv:E.formula) : (E.formula * vc_info_t) list =
    LOG "Entering pinv..." LEVEL TRACE;
    let v = E.voc inv in
    let primed_inv = E.prime inv in
  
    let th_list = List.filter (fun x -> E.is_tid_var x) v in
    let sys_lines = List.filter (fun x -> x <> 0) solverInfo.focus in
    let need_theta = List.mem 0 solverInfo.focus in
    let fresh_tid = E.gen_fresh_thread th_list in
    let diff_list = List.map (fun j -> E.ineq_tid fresh_tid j) th_list in
    (* TODO: Support Threads as terms? *)
    let diff_conj = E.conj_list diff_list in
    let gen_vc_info (l:E.pc_t) = {pc  =l;
                                  smp =solverInfo.cutoff;
                                  stac=Tac.solve_tactic solverInfo.tactics;
                                  supps = [];} in
  
    (* FIX: I think that invariants are not parametrized *)
    (* when the invariant does not contains a tid *)
 
    let init_cond = if need_theta then
                      let theta = gen_theta_general (Sys.SOpenArray th_list) sys
                                    solverInfo.count_abs in
                      let init_vc_info = gen_vc_info 0 in
                        [(E.Implies (theta, inv), init_vc_info)]
                    else
                      [] in

    let tran_conds = ref [] in
    
    let gen_cond l invar a1 a2 tid =
      let me_subst = E.new_tid_subst [(Sys.me_tid_th,tid)] in
      let rho = gen_rho (ROpenArray (tid, th_list)) solverInfo.hide_pres 
        solverInfo.count_abs sys v l in
      List.iter (fun r ->
        let r_final = E.subst_tid me_subst r in
        let antecedent = E.And (a1, a2 r_final) in
        let consequent = if solverInfo.hide_pres then 
            E.prime_modified antecedent invar
          else primed_inv in
        let new_vc = E.Implies (antecedent, consequent) in
        let vc_info = gen_vc_info l
        in
          tran_conds := (new_vc, vc_info) :: !tran_conds
      ) rho in

    let _ = List.iter (fun l ->
              List.iter (gen_cond l inv inv LeapLib.id) th_list;
              gen_cond l inv diff_conj (fun a -> E.And(inv,a)) fresh_tid
            ) sys_lines
    in
      init_cond @ List.rev(!tran_conds)
 
  
  let tag_pinv (sys:Sys.system_t)
      (inv:Tag.f_tag) : (E.formula * vc_info_t) list =
    let inv_as_formula = Tag.tag_table_get_formula tags inv
    in pinv sys inv_as_formula
  
  
  let formula_list_to_table 
      (fs:(E.formula * vc_info_t) list) : formula_table_t =
    let auxTbl : (E.pc_t, int) Hashtbl.t = Hashtbl.create (List.length fs) in
    let get_id (pos:E.pc_t) : int =
      try
        let j = Hashtbl.find auxTbl pos in
        let _ = Hashtbl.replace auxTbl pos (j+1) in
        j
      with _ -> (Hashtbl.add auxTbl pos 1; 0) in
    let tbl = Hashtbl.create defFormulaTableSize in
    let i = ref 1 in
    let iter (f, info) =
      let (p_only, new_preds) = PosExp.keep_locations f in
      let f_status = {
                       desc = "T_" ^ string_of_int info.pc;
                       trans = (info.pc, get_id info.pc);
                       supp_tags = solverInfo.detailed_desc.gral_supp @
                                   info.supps;
                       pos_time  = 0.0;
                       num_time  = 0.0;
                       tll_time  = 0.0;
                       tslk_time = 0.0;
                       tsl_time  = 0.0;
                     } in
      Hashtbl.add tbl !i (f, p_only, new_preds, Unverified,
                          info.stac, info.smp, f_status);
      incr i in
    List.iter iter fs;
    tbl
  
  
  let support_formula_table (sup:E.formula list)
      (tbl:formula_table_t) : formula_table_t =
    let iter i (phi, _, _, valid, stac, smp, desc) =
      if valid = NotValid then
        match phi with
        | E.Implies (ante, cons) ->
            let new_phi = support sup ante cons false in
            let new_pos_phi, new_preds = PosExp.keep_locations new_phi in
            Hashtbl.replace tbl i
              (new_phi, new_pos_phi, new_preds, Unverified, stac, smp, desc)
        | _ -> 
            Interface.Err.smsg "support_formula_table" "Unsupported formula" in
    Hashtbl.iter iter tbl;
    tbl
  
  
  let output_results (vc_tbl:formula_table_t)
      (out_file:string) (header:string) : unit =
    if out_file <> "" then
      let out = open_out_gen [Open_creat;Open_append;Open_wronly] 0o666 out_file in
      output_string out header;
      for i = 1 to (Hashtbl.length vc_tbl) do
        let (f, pf, _, status, _, _, desc) = Hashtbl.find vc_tbl i in
        let f_str = E.formula_to_str f in
        let status_str = valid_to_str status in
        output_string out (sprintf "--- %i : %s ---\n%s: %s\n"
                            i desc.desc  status_str f_str)
      done;
      close_out out
  
  
  (* Processes the generated VC and eliminates heap variables if needed *)
  let clean_formula (phi:E.formula) : E.formula =
    let rec clean phi = match phi with
      | E.Literal(E.Atom(E.Eq (E.MemT _,E.MemT _))) -> E.True
      | E.And (f1,f2) -> E.And(clean f1, clean f2)
      | E.Or (f1,f2) -> E.Or(clean f1, clean f2)
      | E.Not f -> E.Not (clean f)
      | E.Implies (f1,f2) -> E.Implies(clean f1, clean f2)
      | E.Iff (f1,f2) -> E.Iff(clean f1, clean f2)
      | _ -> phi in
    if apply_heap_based_dp () then phi else clean phi
  
  
  let filter_system (sys:Sys.system_t) : Sys.system_t =
    if apply_num_dp () then
      Sys.del_global_var sys Sys.heap_name
    else sys
  
  
  let post_process (fs:E.formula) : E.formula =
    let rec clean = function
      | E.Literal (E.Atom (E.Eq (E.MemT _, E.MemT _))) -> E.True
      | E.And (f1,f2) -> E.And(clean f1, clean f2)
      | E.Or (f1,f2) -> E.Or(clean f1, clean f2)
      | E.Not f -> E.Not (clean f)
      | E.Implies (f1,f2) -> E.Implies(clean f1, clean f2)
      | E.Iff (f1,f2) -> E.Iff(clean f1, clean f2)
      | _ as phi -> phi in
    if apply_heap_based_dp () then fs else clean fs
    
  
  let include_count_abs (sys:Sys.system_t) : Sys.system_t =
    let lines = rangeList 1 (Sys.get_trans_num sys + 1) in
    let tmpVarTbl = Sys.new_var_table in
    List.iter 
      (fun i -> Sys.add_var tmpVarTbl (countAbsVarName ^ string_of_int i) 
       (E.Int) (None) (None) (E.Normal)) 
      lines;
    Sys.add_global_vars sys tmpVarTbl
  
  
  (* Erases output file, if exists *)
  let clear_file (file_name:string) : unit =
    if OcamlSys.file_exists file_name then OcamlSys.remove file_name
  
  
  let prepare_system (sys:Sys.system_t) : Sys.system_t =
    LOG "Entering prepare_system..." LEVEL TRACE;
    assert(isInitialized());
    let _ = clear_file solverInfo.out_file in
    let filtered_sys = filter_system sys in
    let extended_sys = if solverInfo.count_abs then
        include_count_abs filtered_sys
      else filtered_sys in
    extended_sys
  
  let call_pos_dp (phi:PosExp.expression) (status:valid_t) : dp_result_t =
    LOG "Entering call_pos_dp..." LEVEL TRACE;
    assert(isInitialized());
    if status = Unverified || status = NotValid then begin
      let timer = new LeapLib.timer in
      timer#start;
      let valid = PS.is_valid solverInfo.prog_lines phi in
      timer#stop;
      if valid then
        (CheckedLocation, 1, 1, 1, timer#elapsed_time)
      else
        (NotValid, 1, 1, 0, timer#elapsed_time)
    end else (status, 0, 0, 0, 0.0)
  
  
  let call_num_dp (phi : E.formula) (status : valid_t) : dp_result_t =
    LOG "Entering call_num_dp..." LEVEL TRACE;
    assert(isInitialized());
    if status = Unverified || status = NotValid then begin
      let num_phi = NumExp.formula_to_int_formula phi in
      let timer = new LeapLib.timer in
      timer#start;
      let valid, calls = 
        NS.is_valid_with_lines_plus_info solverInfo.prog_lines num_phi in
      timer#stop;
      if valid then
        (Checked, calls, calls, 1, timer#elapsed_time)
      else
        begin
          NS.print_model ();
          (NotValid, calls, calls, 0, timer#elapsed_time)
        end
    end else (Unneeded, 0, 0, 0, 0.0)
  
  
  let call_tll_dp (phi    : E.formula)
                  (stac   : Tac.solve_tactic_t option)
                  (cutoff : Smp.cutoff_strategy)
                  (status : valid_t) : dp_result_t =
    LOG "Entering call_tll_dp..." LEVEL TRACE;
    assert(isInitialized());
    if status = Unverified || status = NotValid then begin
      let tll_phi = TllInterface.formula_to_tll_formula phi in
      let timer = new LeapLib.timer in
      timer#start;
      let valid, calls = TS.is_valid_plus_info
                           solverInfo.prog_lines stac cutoff tll_phi in
      timer#stop;
      if valid then
        (Checked, calls, calls, 1, timer#elapsed_time)
      else
        begin
          TS.print_model ();
          (NotValid, calls, calls, 0, timer#elapsed_time)
        end
    end else (Unneeded, 0, 0, 0, 0.0)


  let call_tslk_dp (phi    : E.formula)
                   (stac   : Tac.solve_tactic_t option)
                   (cutoff : Smp.cutoff_strategy)
                   (status : valid_t) : dp_result_t =
    LOG "Entering call_tslk_dp..." LEVEL TRACE;
    assert(isInitialized());
    if status = Unverified || status = NotValid then begin
      let module TSLKExpr = TSLKS.TslkExp in
      let module TSLKIntf = TSLKInterface.Make(TSLKExpr) in
      let tslk_phi = TSLKIntf.formula_to_tslk_formula phi in
      let timer = new LeapLib.timer in
      timer#start;
      let valid, calls = TSLKS.is_valid_plus_info
                           solverInfo.prog_lines stac cutoff tslk_phi in
      timer#stop;
      if valid then
        (Checked, calls, calls, 1, timer#elapsed_time)
      else
        begin
          TSLKS.print_model ();
          (NotValid, calls, calls, 0, timer#elapsed_time)
        end
    end else (Unneeded, 0, 0, 0, 0.0)


(* TUKA: Repair this function *)
  let call_tsl_dp (phi    : E.formula)
                  (stac   : Tac.solve_tactic_t option)
                  (cutoff : Smp.cutoff_strategy)
                  (status : valid_t) : dp_result_t =
    LOG "Entering call_tsl_dp..." LEVEL TRACE;
    assert(isInitialized());
    if status = Unverified || status = NotValid then begin
      debug "**** Going to translate %s\n" (E.formula_to_str phi);
      debug "**** Will perform TSL translation...";
      let tsl_phi = TSLInterface.formula_to_tsl_formula phi in
      let timer = new LeapLib.timer in
      timer#start;
      debug "**** TSL translation done...";
      let valid, tsl_calls, tslk_calls =
            TslSolver.is_valid_plus_info
                solverInfo.prog_lines stac cutoff tsl_phi in
      timer#stop;
      if valid then
        (Checked, tsl_calls, tslk_calls, 1, timer#elapsed_time)
      else
        begin
          TslSolver.print_model ();
          (NotValid, tsl_calls, tslk_calls, 0, timer#elapsed_time)
        end
    end else (Unneeded, 0, 0, 0, 0.0)
 
 
  let apply_dp_on_table (vc_tbl:formula_table_t) (header:string) : bool =
    LOG "Entering apply_dp_on_table..." LEVEL TRACE;
    assert(isInitialized());
    let analysis_timer = new LeapLib.timer in
    analysis_timer#start;
    let total_vcs = Hashtbl.length vc_tbl in
    (* Counters *)
    let pos_calls     = ref 0 in
    let pos_sats      = ref 0 in
    let num_calls     = ref 0 in
    let num_sats      = ref 0 in
    let tll_calls     = ref 0 in
    let tll_sats      = ref 0 in
    let tsl_calls     = ref 0 in
    let tsl_aux_calls = ref 0 in
    let tsl_sats      = ref 0 in
    let tslk_calls    = ref 0 in
    let tslk_sats     = ref 0 in
    (* Set the SMT solvers *)
    let to_vc_status st = match st with
      | Unverified -> Report.Unverified
      | NotValid   -> Report.NotValid
      | Unneeded   -> Report.Unneeded
      | _          -> Report.Valid in
    let _ = Report.report_vc_run_header() in
    (* Hashtbl iteration not valid anymore after ocaml 4.0, as order is lost *)
    (* Hashtbl.iter (fun i (f, p_f, preds, status, stac, cutoff, desc) -> *)
    for i = 1 to (Hashtbl.length vc_tbl) do
      try begin
      let (f, p_f, preds, status, stac, cutoff, desc) = Hashtbl.find vc_tbl i in
      (* Call position DP *)
      let pos_status, pos_time =
        if apply_pos_dp () then begin
          let new_status, calls, _, sats, time = call_pos_dp p_f status in
          pos_calls := !pos_calls + calls;
          pos_sats := !pos_sats + sats;
          let st = if new_status = Unneeded then
                     status
                   else
                     (desc.pos_time <- time; new_status) in
          Hashtbl.replace vc_tbl i (f, p_f, preds, st, stac, cutoff, desc);
          (new_status, time)
        end else (status, 0.0) in
        
      (* Call numeric DP *)
      let num_status, num_time =
        if apply_num_dp () then begin
          let new_status, calls, _, sats, time = call_num_dp f pos_status in
          num_calls := !num_calls + calls;
          num_sats := !num_sats + sats;
          let st = if new_status = Unneeded then
                     pos_status
                   else
                     (desc.num_time <- time; new_status) in
          Hashtbl.replace vc_tbl i (f, p_f, preds, st, stac, cutoff, desc);
          (new_status, time)
        end else (Unneeded, 0.0) in
      
      (* Call TLL DP *)
      let tll_status, tll_time =
        if apply_tll_dp () then begin
          let prev_st = 
            if num_status = Unneeded then pos_status else num_status in
          let new_status, calls, _, sats, time =
            call_tll_dp f stac (vcgen_to_smp_cutoff cutoff) prev_st in
          tll_calls := !tll_calls + calls;
          tll_sats := !tll_sats + sats;
          let st = if new_status = Unneeded then
                     pos_status
                   else
                     (desc.tll_time <- time; new_status) in
          Hashtbl.replace vc_tbl i (f, p_f, preds, st, stac, cutoff, desc);
          (new_status, time)
        end else (num_status, 0.0) in

      (* Call TSLK DP *)
      let tslk_status, tslk_time =
        let (apply_tslk, k) = apply_tslk_dp() in
        if apply_tslk then begin
          let prev_st = if num_status = Unneeded then pos_status else num_status in
          let new_status, calls, _, sats, time =
            call_tslk_dp f stac (vcgen_to_smp_cutoff cutoff) prev_st in
          tslk_calls := !tslk_calls + calls;
          tslk_sats := !tslk_sats + sats;
          let st = if new_status = Unneeded then
                     pos_status
                   else
                     (desc.tslk_time <- time; new_status) in
          Hashtbl.replace vc_tbl i (f, p_f, preds, st, stac, cutoff, desc);
          (new_status, time)
        end else (tll_status, 0.0) in

      (* Call TSL DP *)
      let tsl_status, tsl_time =
        if apply_tsl_dp() then begin
          let prev_st = if num_status = Unneeded then pos_status else num_status in
          let new_status, tsl_call, tslk_call, sats, time =
            call_tsl_dp f stac (vcgen_to_smp_cutoff cutoff) prev_st in
          tsl_calls := !tsl_calls + tsl_call;
          tsl_aux_calls := !tsl_aux_calls + tslk_call;
          tsl_sats := !tsl_sats + sats;
          let st = if new_status = Unneeded then
                     pos_status
                   else
                     (desc.tsl_time <- time; new_status) in
          Hashtbl.replace vc_tbl i (f, p_f, preds, st, stac, cutoff, desc);
          (new_status, time)
        end else (tll_status, 0.0) in


      (* We report the results *)
      Report.report_vc_run i
        (to_vc_status pos_status)  pos_time
        (to_vc_status num_status)  num_time
        (to_vc_status tll_status)  tll_time
        (to_vc_status tslk_status) tslk_time
        (to_vc_status tsl_status)  tsl_time desc.desc "";
      (* TODO: Extend this section to get detailed information
               for TSL and TSLK *)
      if solverInfo.detailed_desc.detFolder <> "" then
        let time_list = [("POS", desc.pos_time);
                         ("NUM", desc.num_time);
                         ("TLL", desc.tll_time)] in
        Report.report_details_to_file
          solverInfo.detailed_desc.detFolder
          solverInfo.detailed_desc.detProg
          solverInfo.detailed_desc.detInv
          (i, fst desc.trans, snd desc.trans)
          desc.supp_tags (tll_status = NotValid) time_list
      end with _ -> ()
    done;
    (* ) vc_tbl; *)
    let remains = total_vcs -
                    (!pos_sats + !num_sats +
                     !tll_sats + !tslk_sats + !tsl_sats) in
    output_results vc_tbl solverInfo.out_file header;
    analysis_timer#stop;
    Report.report_analysis_time (analysis_timer#elapsed_time);
    Report.report_results (total_vcs,
      !pos_calls,  !pos_sats,
      !num_calls,  !num_sats,
      !tll_calls,  !tll_sats,
      !tslk_calls, !tslk_sats,
      !tsl_calls,  !tsl_sats,
      remains, solverInfo.out_file);
    remains = 0
  
  let apply_dp_on_list (vc_list:(E.formula * vc_info_t) list)
      (header:string) : bool =
    LOG "Entering apply_dp_on_list..." LEVEL TRACE;
    let vc_tbl = formula_list_to_table vc_list in
    apply_dp_on_table vc_tbl header
  
  
  let check_with_pinv (sys : Sys.system_t) (inv : E.formula) : bool =
    assert(isInitialized());
    LOG "Entering check_with_pinv..." LEVEL TRACE;
    (* Erases output file, if exists *)
    let extended_sys = prepare_system sys in
    let vcs = pinv extended_sys inv in
    let vc_list = 
      List.map (fun (vc,desc) -> (post_process vc, desc)) vcs in
    let res = apply_dp_on_list vc_list "Checked VCs with PINV\n\n" in
    res
  
  
  let check_with_pinv_plus (sys : Sys.system_t) (inv : E.formula) : bool =
    assert(isInitialized());
    LOG "Entering check_with_pinv_plus..." LEVEL TRACE;
    (* Erases output file, if exists *)
    let extended_sys = prepare_system sys in
    let vcs = pinv_plus extended_sys inv in
    let vc_list = 
      List.map (fun (vc,desc) -> (post_process vc, desc)) vcs in
    let res = apply_dp_on_list vc_list "Checked VCs with PINV+\n\n" in
    res
  
  
  let check_with_spinv (sys : Sys.system_t) (supInv_list : E.formula list)
      (inv : E.formula) : bool =
    assert(isInitialized());
    LOG "Entering check_with_spinv..." LEVEL TRACE;
    (* Erases output file, if exists *)
    let extended_sys = prepare_system sys in
    let vcs = spinv extended_sys supInv_list inv in
    let vc_list = 
      List.map (fun (vc, desc) -> (post_process vc, desc)) vcs in
    let res = apply_dp_on_list vc_list "Checked VCs with SINV\n\n" in
    res


  let check_with_seq_binv (sys : Sys.system_t) (inv : E.formula) : bool =
    assert(isInitialized());
    LOG "Entering check_with_seq_binv..." LEVEL TRACE;
    (* Erases output file, if exists *)
    let extended_sys = prepare_system sys in
    let vcs = seq_binv extended_sys inv in
    let vc_list =
      List.map (fun (vc, desc) -> (post_process vc, desc)) vcs in
    let res = apply_dp_on_list vc_list "Checked VCs with SEQINV\n\n" in
    res


  let check_with_seq_spinv (sys : Sys.system_t) (supInv_list : E.formula list)
      (inv : E.formula) : bool =
    assert(isInitialized());
    LOG "Entering check_with_seq_spinv..." LEVEL TRACE;
    let extended_sys = prepare_system sys in
    let vcs = seq_spinv extended_sys supInv_list inv in
    let vc_list = 
      List.map (fun (vc, desc) -> (post_process vc, desc)) vcs in
    let res = apply_dp_on_list vc_list "Checked VCs with SEQSINV\n\n" in
    res


  let check_with_graph (sys:Sys.system_t)
      (graph:IGraph.iGraph_t) : bool =
    (* Auxiliary function for loading cases *)
    let _ = LOG "Entering check_with_graph..." LEVEL TRACE in

      let load_cases (sc_tbl:special_cases_tag_tbl_t) : special_cases_form_tbl_t =
      let case_tbl = Hashtbl.create (Hashtbl.length sc_tbl) in
      let _ = Hashtbl.iter (fun (pc, prem) (tags, tacs) ->
                set_descSuppTbl solverInfo.detailed_desc (pc,prem) tags;
                Hashtbl.add case_tbl (pc, prem)
                  (List.map (fun t -> let phi = read_tag t in
                                        Option.default E.False phi
                   )tags, tacs)
              ) sc_tbl
      in
        case_tbl in
        
    (* Process each rule in the invariant relation graph *)
    let graph_info = IGraph.graph_info graph in
    let base_out_name = solverInfo.out_file in
    let foldop res (mode, sup, inv, cases, tacs) =
      solverInfo.tactics <- tacs;
      let inv_id = Tag.tag_id inv in
      let sup_id = String.concat "," $ List.map Tag.tag_id sup in
      let inv_phi = Option.default E.False (read_tag inv) in
      let sup_phi = List.map (read_tag>>Option.(default E.False)) sup in
      let _ = set_detFileName inv_id in
      let _ = set_descGralSupp solverInfo.detailed_desc sup in
      match mode with
      | IGraph.Concurrent ->
        if sup_phi = [] then begin
          (* PINV *)
          if Hashtbl.length cases = 0 then printf "PINV+ for %s\n" inv_id
          else printf "PINV+ WITH CASES for %s\n" inv_id;
          let output_name = "_pinv_" ^ inv_id in
          solverInfo.out_file <- (base_out_name ^ output_name);
          let case_tbl = load_cases cases in
          solverInfo.special <- case_tbl;
          solverInfo.tactics <- tacs;
          let this_res = check_with_pinv_plus sys inv_phi in
          res && this_res
        end else begin
          if Hashtbl.length cases = 0 then begin
            (* SPINV *)
            printf "SPINV for %s -> %s\n" sup_id inv_id;
            let output_name = "_sinv_" ^ sup_id ^ "->" ^ inv_id in
            solverInfo.out_file <- (base_out_name ^ output_name);
            let this_res = check_with_spinv sys sup_phi inv_phi
            in
              res && this_res
          end else begin
            (* SPINV WITH SPECIAL CASES *)
            printf "SPINV WITH CASES for %s -> %s\n" sup_id inv_id;
            let output_name = "_sinvsp_" ^ sup_id ^ "->" ^ inv_id in
            solverInfo.out_file <- (base_out_name ^ output_name);
            let case_tbl = load_cases cases in
            solverInfo.special <- case_tbl;
            let this_res = check_with_spinv sys sup_phi inv_phi in
            res & this_res
          end
        end
    | IGraph.Sequential ->
      if sup_phi = [] then begin
        (* B-INV *)
        printf "B-INV for %s" inv_id;
        let output_name = "_seq_binv_" ^ inv_id in
        solverInfo.out_file <- (base_out_name ^ output_name);
        let this_res = check_with_seq_binv sys inv_phi in
        res & this_res
      end else begin
        if Hashtbl.length cases = 0 then begin
          (* SEQ_SPINV *)
            printf "SEQ_SPINV for %s -> %s\n" sup_id inv_id;
            let output_name = "_seq_sinv_" ^ sup_id ^ "->" ^ inv_id in
            solverInfo.out_file <- (base_out_name ^ output_name);
            let this_res = check_with_seq_spinv sys sup_phi inv_phi
            in
              res && this_res
        end else begin
          (* SEQ_SPINV WITH SPECIAL CASES *)
            printf "SEQ_SPINV WITH CASES for %s -> %s\n" sup_id inv_id;
            let output_name = "_seq_sinvsp_" ^ sup_id ^ "->" ^ inv_id in
            solverInfo.out_file <- (base_out_name ^ output_name);
            let case_tbl = load_cases cases in
            solverInfo.special <- case_tbl;
            let this_res = check_with_seq_spinv sys sup_phi inv_phi in
            res & this_res

        end
      end
    in

      List.fold_left foldop true graph_info
end
