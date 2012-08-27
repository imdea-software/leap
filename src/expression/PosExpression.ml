
open Printf
open LeapLib


module Expr = Expression


type variable = string * bool * tid option * string option

and tid =
    VarTh      of variable
  | NoThid
  | CellLockId of variable
  

type expression =
  | Eq            of tid * tid
  | InEq          of tid * tid
  | Pred          of string
  | PC            of int * tid option * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * tid option * bool
  | True
  | False
  | And           of expression * expression
  | Or            of expression * expression
  | Not           of expression
  | Implies       of expression * expression
  | Iff           of expression * expression


type pred_table_t = (Expr.formula, string) Hashtbl.t


exception NotSupportedInPosExpression of string


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
let term_pool = Expr.TermPool.empty


(* Configuration *)
let pc_name = "pc"
let abs_cell_id = "abs_cell_lock_"
let abs_array_id = "abs_tid_array_"
let defPredTableSize = 200


let abs_cell_counter = ref 0


let build_fresh_lockid_var (c:Expr.cell) : variable =
  let lockid_term = Expr.ThidT (Expr.CellLockId c) in
  let cell_tag = Expr.TermPool.tag term_pool lockid_term in
  let var = (abs_cell_id ^ string_of_int cell_tag, false, None, None)
  in
    var


let build_fresh_tid_array_var (t:Expr.tid) : variable =
  let tid_array_term = Expr.ThidT t in
  let tid_tag = Expr.TermPool.tag term_pool tid_array_term in
  let var = (abs_array_id ^ string_of_int tid_tag, false, None, None)
  in
    var

  

let rec conv_variable (v:Expr.variable) : variable =
  let (id,_,pr,th,p,_) = v in (id, pr, Option.lift conv_th th, p)


and conv_th (th:Expr.tid) : tid =
  match th with
    Expr.VarTh v -> VarTh (conv_variable v)
  | Expr.NoThid -> NoThid
  | Expr.CellLockId c -> VarTh (build_fresh_lockid_var c)
  | Expr.ThidArrayRd _ -> VarTh (build_fresh_tid_array_var th)


let localize_var_id (v:string) (p_name:string) : string =
  sprintf "%s::%s" p_name v


let loc_var_option (v:string) (p_name:string option) : string =
  Option.map_default (localize_var_id v) v p_name


let rec variable_to_str (var:variable) : string =
  let (id,pr,th,p) = var in
  let var_str = sprintf "%s%s" (loc_var_option id p) (th_option_to_str th)
  in
    if pr then var_str ^ "'" else var_str


and tid_to_str (expr:tid) : string =
  match expr with
    VarTh v -> variable_to_str v
  | NoThid -> "#"
  | CellLockId v -> variable_to_str v ^ ".lockid"


and param_tido_str (expr:tid) : string =
  match expr with
    VarTh v -> let (id,_,_,_) = v in
               begin
                 try
                   sprintf "[%i]" (int_of_string id)
                 with
                   _ -> sprintf "(%s)" (variable_to_str v)
               end
  | NoThid -> sprintf "(#)"
  | CellLockId v -> sprintf "(%s)" (tid_to_str expr)


and th_option_to_str (expr:tid option) : string =
  Option.map_default param_tido_str "" expr


and var_to_str id pr th p k =
  let var_str = sprintf "%s%s" (loc_var_option id p) (th_option_to_str th)
  in
    if pr then var_str ^ "'" else var_str


and prime_variable (pr:bool) (v:variable) : variable =
  let (id,_,th,p) = v
  in
    (id,pr,th,p) 


and priming_tid (pr:bool) (t:tid) : tid =
  match t with
    VarTh v -> VarTh (prime_variable pr v)
  | NoThid -> NoThid
  | CellLockId v -> CellLockId (prime_variable pr v)


and priming_option_tid (pr:bool) (expr:tid option) : tid option =
  Option.lift (priming_tid pr) expr


let rec expr_to_str (expr:expression) : string =
  match expr with
    Eq (t1,t2)            -> sprintf "%s = %s" (tid_to_str t1) (tid_to_str t2)
  | InEq (t1, t2)         -> sprintf "%s != %s" (tid_to_str t1) (tid_to_str t2)
  | Pred p                -> p
  | PC (pc,t,p)           -> let t_str = if p then
                                          th_option_to_str
                                            (priming_option_tid true t)
                                         else
                                          th_option_to_str t in
                             let v_name = if p then
                                            pc_name ^ "'"
                                          else
                                            pc_name
                              in
                                sprintf "%s%s=%i" v_name t_str pc
  | PCUpdate (pc,t)       -> sprintf "%s' = %s{%s<-%i}"
                                pc_name pc_name (tid_to_str t) pc
  | PCRange (pc1,pc2,t,p) -> let t_str = if p then
                                          th_option_to_str
                                            (priming_option_tid true t)
                                         else
                                          th_option_to_str t in
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
  | PC (i,th,p)     -> Option.map_default (fun t -> [t]) [] th
  | PCUpdate (i,th) -> [th]
  | PCRange (i,j,th,p) -> Option.map_default (fun t -> [t]) [] th
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
  

let keep_locations (f:Expr.formula) : (expression * string list) =
  let curr_id = ref 0 in
  let pred_tbl = Hashtbl.create defPredTableSize in
  let rec apply (f:Expr.formula) =
    match f with
      Expr.True             -> True
    | Expr.False            -> False
    | Expr.And(e1,e2)       -> And (apply e1, apply e2)
    | Expr.Or (e1, e2)      -> Or (apply e1, apply e2)
    | Expr.Not e            -> Not (apply e)
    | Expr.Implies (e1, e2) -> Implies (apply e1, apply e2)
    | Expr.Iff (e1, e2)     -> apply (Expr.And (Expr.Implies (e1,e2),
                                                Expr.Implies (e2,e1)))
    | Expr.Literal(Expr.Atom(Expr.PC(i,th,pr)))     ->
        PC (i, Option.lift conv_th th, pr)
    | Expr.Literal(Expr.Atom(Expr.PCUpdate (i,th))) ->
        PCUpdate (i, conv_th th)
    | Expr.Literal(Expr.Atom(Expr.PCRange(i,j,th,pr))) ->
        PCRange (i, j, Option.lift conv_th th, pr)
    | Expr.Literal (Expr.NegAtom (Expr.Eq (Expr.ThidT t1, Expr.ThidT t2))) ->
        apply $ Expr.Literal(Expr.Atom(Expr.InEq(Expr.ThidT t1, Expr.ThidT t2)))
    | Expr.Literal (Expr.Atom (Expr.Eq (Expr.ThidT t1, Expr.ThidT t2))) ->
        let th1 = conv_th t1 in
        let th2 = conv_th t2
        in
          Eq (th1, th2)
    | Expr.Literal (Expr.NegAtom (Expr.InEq (Expr.ThidT t1, Expr.ThidT t2))) ->
        apply $ Expr.Literal(Expr.Atom(Expr.Eq(Expr.ThidT t1,Expr.ThidT t2)))
    | Expr.Literal (Expr.Atom (Expr.InEq (Expr.ThidT t1, Expr.ThidT t2))) ->
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
