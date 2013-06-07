
open Printf
open LeapLib


module E = Expression


type variable =
  {
            id        : string          ;
    mutable is_primed : bool            ;
    mutable parameter : shared_or_local ;
            scope     : procedure_name  ;
  }

and shared_or_local = Shared  | Local of tid
and procedure_name  = GlobalScope | Scope of string

and tid =
    VarTh      of variable
  | NoThid
  | CellLockId of variable
  

type expression =
  | Eq            of tid * tid
  | InEq          of tid * tid
  | Pred          of string
  | PC            of int * shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * shared_or_local * bool
  | True
  | False
  | And           of expression * expression
  | Or            of expression * expression
  | Not           of expression
  | Implies       of expression * expression
  | Iff           of expression * expression


type pred_table_t = (E.formula, string) Hashtbl.t


exception NotSupportedInPosEession of string


module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )


module PredSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = string
  end )


module PosSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = int
  end )

(* Pool of terms *)
let term_pool = E.TermPool.empty


(* Configuration *)
let pc_name = "pc"
let abs_cell_id = "abs_cell_lock_"
let abs_array_id = "abs_tid_array_"
let defPredTableSize = 200


let abs_cell_counter = ref 0


let build_var (id:string) (pr:bool) (th:shared_or_local) (p:procedure_name) : variable =
  {
    id = id ;
    is_primed = pr ;
    parameter = th ;
    scope = p ;
  }


let build_fresh_lockid_var (t:E.tid) : variable =
  let lockid_term = E.ThidT t in
  let cell_tag = E.TermPool.tag term_pool lockid_term in
  let var = build_var (abs_cell_id ^ string_of_int cell_tag) false Shared GlobalScope
  in
    var


let build_fresh_tid_array_var (t:E.tid) : variable =
  let tid_array_term = E.ThidT t in
  let tid_tag = E.TermPool.tag term_pool tid_array_term in
  let var = build_var (abs_array_id ^ string_of_int tid_tag) false Shared GlobalScope
  in
    var


let rec conv_variable (v:E.variable) : variable =
  build_var (E.var_id v) (E.var_is_primed v)
            (conv_shared_or_local (E.var_parameter v))
            (conv_procedure_name (E.var_scope v))


and conv_shared_or_local (th:E.shared_or_local) : shared_or_local =
  match th with
  | E.Shared -> Shared
  | E.Local t -> Local (conv_th t)


and conv_procedure_name (p:E.procedure_name) : procedure_name =
  match p with
  | E.GlobalScope -> GlobalScope
  | E.Scope proc -> Scope proc


and conv_th (th:E.tid) : tid =
  match th with
    E.VarTh v            -> VarTh (conv_variable v)
  | E.NoThid             -> NoThid
  | E.CellLockId _       -> VarTh (build_fresh_lockid_var th)
  | E.CellLockIdAt _     -> VarTh (build_fresh_lockid_var th)
  | E.ThidArrayRd _      -> VarTh (build_fresh_tid_array_var th)
  | E.ThidArrRd _        -> VarTh (build_fresh_tid_array_var th)


let localize_var_id (v:string) (p_name:string) : string =
  sprintf "%s::%s" p_name v


let loc_var_option (v:string) (p_name:procedure_name) : string =
  match p_name with
  | GlobalScope -> v
  | Scope proc -> localize_var_id v proc


let rec variable_to_str (var:variable) : string =
  let var_str = sprintf "%s%s" (loc_var_option var.id var.scope)
                               (shared_or_local_to_str var.parameter)
  in
    if var.is_primed then var_str ^ "'" else var_str


and shared_or_local_to_str (exp:shared_or_local) : string =
  match exp with 
    Shared  -> ""
  | Local t -> param_tid_to_str  t


and tid_to_str (expr:tid) : string =
  match expr with
    VarTh v -> variable_to_str v
  | NoThid -> "#"
  | CellLockId v -> variable_to_str v ^ ".lockid"


and param_tid_to_str (expr:tid) : string =
  match expr with
    VarTh v -> begin
                 try
                   sprintf "[%i]" (int_of_string v.id)
                 with
                   _ -> sprintf "(%s)" (variable_to_str v)
               end
  | NoThid -> sprintf "(#)"
  | CellLockId v -> sprintf "(%s)" (tid_to_str expr)


and var_to_str id pr th p k =
  let var_str = sprintf "%s%s" (loc_var_option id p) (shared_or_local_to_str th)
  in
    if pr then var_str ^ "'" else var_str


and prime_variable (pr:bool) (v:variable) : variable =
  v.is_primed <- pr; v


and priming_tid (pr:bool) (t:tid) : tid =
  match t with
    VarTh v -> VarTh (prime_variable pr v)
  | NoThid -> NoThid
  | CellLockId v -> CellLockId (prime_variable pr v)


and priming_option_tid (pr:bool) (expr:shared_or_local) : shared_or_local =
  match expr with
  | Shared -> Shared
  | Local t -> Local (priming_tid pr t)


let rec expr_to_str (expr:expression) : string =
  match expr with
    Eq (t1,t2)            -> sprintf "%s = %s" (tid_to_str t1) (tid_to_str t2)
  | InEq (t1, t2)         -> sprintf "%s != %s" (tid_to_str t1) (tid_to_str t2)
  | Pred p                -> p
  | PC (pc,t,p)           -> let t_str = shared_or_local_to_str t in
                             let v_name = if p then pc_name ^ "'" else pc_name in
                               sprintf "%s%s=%i" v_name t_str pc
  | PCUpdate (pc,t)       -> sprintf "%s' = %s{%s<-%i}"
                                pc_name pc_name (tid_to_str t) pc
  | PCRange (pc1,pc2,t,p) -> let t_str = if p then
                                           shared_or_local_to_str (priming_option_tid p t)
                                         else
                                           shared_or_local_to_str t in
                             let v_name = if p then
                                            pc_name ^ "'"
                                          else
                                            pc_name
                              in
                                sprintf "%i <= %s%s <=%i" pc1 v_name t_str pc2
  | True                  -> sprintf "true"
  | False                 -> sprintf "false"
  | And(f1, f2)           -> sprintf "(%s /\\ %s)" (expr_to_str f1)
                                                   (expr_to_str f2)
  | Or(f1,f2)             -> sprintf "(%s \\/ %s)" (expr_to_str f1)
                                                   (expr_to_str f2)
  | Not(f)                -> sprintf "(~ %s)" (expr_to_str f)
  | Implies(f1,f2)        -> sprintf "(%s -> %s)" (expr_to_str f1)
                                                  (expr_to_str f2)
  | Iff (f1,f2)           -> sprintf "(%s <-> %s)" (expr_to_str f1)
                                                   (expr_to_str f2)


let conj_list (es:expression list) : expression =
  match es with
  | []    -> True
  | x::xs -> List.fold_left (fun phi e -> And(e, phi)) x xs


let disj_list (es:expression list) : expression =
  match es with
  | []    -> False
  | x::xs -> List.fold_left (fun phi e -> Or(e, phi)) x xs


let rec all_preds (expr:expression) : string list =
  let all_preds_aux expr =
    match expr with
      Pred p           -> [p]
    | And (e1,e2)      -> all_preds e1 @ all_preds e2
    | Or (e1,e2)       -> all_preds e1 @ all_preds e2
    | Not e            -> all_preds e
    | Implies (e1,e2)  -> all_preds e1 @ all_preds e2
    | Iff (e1,e2)      -> all_preds e1 @ all_preds e2
    | _                -> [] in
  let pred_list = all_preds_aux expr in
  let pred_set  = List.fold_left (fun s p ->
                    PredSet.add p s
                  ) PredSet.empty pred_list
  in
    PredSet.elements pred_set


let rec voc (expr:expression) : tid list =
  let rec voc_aux exp =
    match exp with
    Eq (t1,t2)      -> [t1;t2]
  | InEq (t1,t2)    -> [t1;t2]
  | PC (i,th,p)     -> begin
                         match th with
                         | Shared -> []
                         | Local t -> [t]
                       end
  | PCUpdate (i,th) -> [th]
  | PCRange (i,j,th,p) -> begin
                            match th with
                            | Shared -> []
                            | Local t -> [t]
                          end
  | And (e1,e2)     -> voc_aux e1 @ voc_aux e2
  | Or (e1,e2)      -> voc_aux e1 @ voc_aux e2
  | Not e           -> voc_aux e
  | Implies (e1,e2) -> voc_aux e1 @ voc_aux e2
  | Iff (e1,e2)     -> voc_aux e1 @ voc_aux e2
  | Pred _          -> []
  | True            -> []
  | False           -> [] in
  let voc_list = voc_aux expr in
  let voc_set = List.fold_left (fun set e -> ThreadSet.add e set)
                              (ThreadSet.empty)
                              (voc_list)
  in
    ThreadSet.elements voc_set


let rec pos (expr:expression) : int list =
  let rec pos_aux exp =
    match exp with
    | PC (i,_,_)        -> [i]
    | PCUpdate (i,_)    -> [i]
    | PCRange (i,j,_,_) -> rangeList i j
    | And (e1,e2)       -> pos_aux e1 @ pos_aux e2
    | Or (e1,e2)        -> pos_aux e1 @ pos_aux e2
    | Not e             -> pos_aux e
    | Implies (e1,e2)   -> pos_aux e1 @ pos_aux e2
    | Iff (e1,e2)       -> pos_aux e1 @ pos_aux e2
    | _                 -> [] in
  let pos_list = pos_aux expr in
  let pos_set = List.fold_left (fun set e ->
                  PosSet.add e set
                ) PosSet.empty pos_list
  in
    PosSet.elements pos_set
  

let keep_locations (f:E.formula) : (expression * string list) =
  let curr_id = ref 0 in
  let pred_tbl = Hashtbl.create defPredTableSize in
  let rec apply (f:E.formula) =
    match f with
      E.True             -> True
    | E.False            -> False
    | E.And(e1,e2)       -> And (apply e1, apply e2)
    | E.Or (e1, e2)      -> Or (apply e1, apply e2)
    | E.Not e            -> Not (apply e)
    | E.Implies (e1, e2) -> Implies (apply e1, apply e2)
    | E.Iff (e1, e2)     -> apply (E.And (E.Implies (e1,e2),
                                                E.Implies (e2,e1)))
    | E.Literal(E.Atom(E.PC(i,th,pr)))     ->
        PC (i, conv_shared_or_local th, pr)
    | E.Literal(E.Atom(E.PCUpdate (i,th))) ->
        PCUpdate (i, conv_th th)
    | E.Literal(E.Atom(E.PCRange(i,j,th,pr))) ->
        PCRange (i, j, conv_shared_or_local th, pr)
    | E.Literal (E.NegAtom (E.Eq (E.ThidT t1, E.ThidT t2))) ->
        apply $ E.Literal(E.Atom(E.InEq(E.ThidT t1, E.ThidT t2)))
    | E.Literal (E.Atom (E.Eq (E.ThidT t1, E.ThidT t2))) ->
        let th1 = conv_th t1 in
        let th2 = conv_th t2
        in
          Eq (th1, th2)
    | E.Literal (E.NegAtom (E.InEq (E.ThidT t1, E.ThidT t2))) ->
        apply $ E.Literal(E.Atom(E.Eq(E.ThidT t1,E.ThidT t2)))
    | E.Literal (E.Atom (E.InEq (E.ThidT t1, E.ThidT t2))) ->
        let th1 = conv_th t1 in
        let th2 = conv_th t2
        in
          InEq (th1, th2)
    | _ -> begin
             if Hashtbl.mem pred_tbl f then
               Pred (Hashtbl.find pred_tbl f)
             else
               let new_pred = "pred" ^ (string_of_int !curr_id) in
               let _ = Hashtbl.add pred_tbl f new_pred in
               let _ = curr_id := !curr_id + 1
               in
                 Pred new_pred
             end in
  let new_formula = apply f
  in
    (new_formula, Hashtbl.fold (fun _ p xs -> p::xs) pred_tbl [])


let rec expand_pc_range (expr:expression) : expression =
  let expand = expand_pc_range in
  match expr with
    And (e1,e2)         -> And (expand e1, expand e2)
  | Or (e1,e2)          -> Or (expand e1, expand e2)
  | Not (e)             -> Not (expand e)
  | Implies (e1,e2)     -> Implies (expand e1, expand e2)
  | Iff (e1,e2)         -> Iff (expand e1, expand e2)
  | PCRange (i,j,th,pr) -> List.fold_left (fun phi k ->
                             Or (phi, PC (k,th,pr))
                           ) (PC (i,th,pr)) (rangeList (i+1) j)
  | _                   -> expr


let rec cnf (expr:expression) : expression list list =
  match expr with
    Iff (e1,e2) -> cnf (And (Implies (e1,e2),Implies (e2,e1)))
  | Implies(e1,e2) -> cnf (Or (Not e1, e2))
  | Or(e1,e2)   -> let e1_cnf = cnf e1 in
                   let e2_cnf = cnf e2 in
                     List.fold_left (fun final_lst x1 ->
                       let lst = List.fold_left (fun l2 x2 ->
                                    (x1 @ x2) :: l2
                                 ) [] e2_cnf
                       in
                          lst @ final_lst
                     ) [] e1_cnf
  | And (e1,e2) -> cnf e1 @ cnf e2
  | Not (Not e) -> cnf e
  | Not (And (e1,e2)) -> cnf (Or (Not e1, Not e2))
  | Not (Or (e1, e2)) -> cnf (And (Not e1, Not e2))
  | Not (Implies (e1, e2)) -> cnf (And (e1, Not e2))
  | Not (Iff (e1, e2)) -> cnf (Or (And (e1, Not e2), And (Not e1, e2)))
  | e -> [[e]]
