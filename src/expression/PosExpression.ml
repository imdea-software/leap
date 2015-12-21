open Printf
open LeapLib

module E = Expression
module F = Formula

module V = Variable.Make (
  struct
    type sort_t = unit
    type info_t = unit
  end )

type tid =
  | VarTh      of V.t
  | NoTid
  | CellLockId of V.t
  

type expression =
  | Eq            of tid * tid
  | InEq          of tid * tid
  | Pred          of string
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
  | True
  | False
  | And           of expression * expression
  | Or            of expression * expression
  | Not           of expression
  | Implies       of expression * expression
  | Iff           of expression * expression


exception Not_tid_var of tid

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

module TermPool =
  Pool.Make (
    struct
      type t = E.term
      let compare = Pervasives.compare
    end)

(* Pool of terms *)
let term_pool = TermPool.empty


(* Configuration *)
let abs_cell_id = "abs_cell_lock_"
let abs_array_id = "abs_tid_array_"
let abs_bucket_id = "abs_bucket_"
let abs_lock_id = "abs_lock_"
let defPredTableSize = 200


let abs_cell_counter = ref 0


let build_var ?(fresh=false)
              (id:V.id)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
  V.build id () pr th p () ~fresh:fresh


let build_fresh (t:E.tid) (abs_id:V.id) : V.t =
  let new_tag = TermPool.tag term_pool (E.TidT t) in
  let id = (abs_id ^ string_of_int new_tag) in
  let var = build_var id false V.Shared V.GlobalScope ~fresh:true
  in
    var


let rec conv_variable (v:E.V.t) : V.t =
  build_var (E.V.id v) (E.V.is_primed v)
            (conv_shared_or_local (E.V.parameter v))
            (conv_procedure_name (E.V.scope v))
            ~fresh:(E.V.is_fresh v)


and conv_shared_or_local (th:E.V.shared_or_local) : V.shared_or_local =
  match th with
  | E.V.Shared -> V.Shared
  | E.V.Local t -> V.Local (conv_variable t)


and conv_procedure_name (p:E.V.procedure_name) : V.procedure_name =
  match p with
  | E.V.GlobalScope -> V.GlobalScope
  | E.V.Scope proc -> V.Scope proc



and conv_th (th:E.tid) : tid =
  match th with
    E.VarTh v           -> VarTh (conv_variable v)
  | E.NoTid             -> NoTid
  | E.CellLockId _      -> VarTh (build_fresh th abs_cell_id)
  | E.CellLockIdAt _    -> VarTh (build_fresh th abs_cell_id)
  | E.TidArrayRd _      -> VarTh (build_fresh th abs_array_id)
  | E.TidArrRd _        -> VarTh (build_fresh th abs_array_id)
  | E.PairTid _         -> VarTh (build_fresh th abs_array_id)
  | E.BucketTid _       -> VarTh (build_fresh th abs_bucket_id)
  | E.LockId _          -> VarTh (build_fresh th abs_lock_id)


let rec tid_to_str (expr:tid) : string =
  match expr with
    VarTh v -> V.to_str v
  | NoTid -> "#"
  | CellLockId v -> V.to_str v ^ ".lockid"


and param_tid_to_str (expr:tid) : string =
  match expr with
    VarTh v -> begin
                 try
                   sprintf "[%i]" (int_of_string (V.id v))
                 with
                   _ -> sprintf "(%s)" (V.to_str v)
               end
  | NoTid -> sprintf "(#)"
  | CellLockId _ -> sprintf "(%s)" (tid_to_str expr)


and priming_tid (t:tid) : tid =
  match t with
    VarTh v -> VarTh (V.prime v)
  | NoTid -> NoTid
  | CellLockId v -> CellLockId (V.prime v)


and priming_option_tid (expr:V.shared_or_local) : V.shared_or_local =
  match expr with
  | V.Shared -> V.Shared
  | V.Local t -> V.Local (V.prime t)


let rec expr_to_str (expr:expression) : string =
  match expr with
    Eq (t1,t2)            -> sprintf "%s = %s" (tid_to_str t1) (tid_to_str t2)
  | InEq (t1, t2)         -> sprintf "%s != %s" (tid_to_str t1) (tid_to_str t2)
  | Pred p                -> p
  | PC (pc,t,p)           -> let t_str = V.shared_or_local_to_str t in
                             let v_name = if p then Conf.pc_name ^ "'" else Conf.pc_name in
                               sprintf "%s%s=%i" v_name t_str pc
  | PCUpdate (pc,t)       -> sprintf "%s' = %s{%s<-%i}"
                                Conf.pc_name Conf.pc_name (tid_to_str t) pc
  | PCRange (pc1,pc2,t,p) -> let t_str = if p then
                                           V.shared_or_local_to_str (priming_option_tid t)
                                         else
                                           V.shared_or_local_to_str t in
                             let v_name = if p then
                                            Conf.pc_name ^ "'"
                                          else
                                            Conf.pc_name
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


let voc (expr:expression) : tid list =
  let rec voc_aux exp =
    match exp with
    Eq (t1,t2)      -> [t1;t2]
  | InEq (t1,t2)    -> [t1;t2]
  | PC (_,th,_)     -> begin
                         match th with
                         | V.Shared -> []
                         | V.Local t -> [VarTh t]
                       end
  | PCUpdate (_,th) -> [th]
  | PCRange (_,_,th,_) -> begin
                            match th with
                            | V.Shared -> []
                            | V.Local t -> [VarTh t]
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


let pos (expr:expression) : int list =
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
      F.True             -> True
    | F.False            -> False
    | F.And(e1,e2)       -> And (apply e1, apply e2)
    | F.Or (e1, e2)      -> Or (apply e1, apply e2)
    | F.Not e            -> Not (apply e)
    | F.Implies (e1, e2) -> Implies (apply e1, apply e2)
    | F.Iff (e1, e2)     -> apply (F.And (F.Implies (e1,e2),
                                          F.Implies (e2,e1)))
    | F.Literal(F.Atom(E.PC(i,th,pr)))     ->
        PC (i, conv_shared_or_local th, pr)
    | F.Literal(F.Atom(E.PCUpdate (i,th))) ->
        PCUpdate (i, conv_th th)
    | F.Literal(F.Atom(E.PCRange(i,j,th,pr))) ->
        PCRange (i, j, conv_shared_or_local th, pr)
    | F.Literal (F.NegAtom (E.Eq (E.TidT t1, E.TidT t2))) ->
        apply (E.ineq_tid t1 t2)
    | F.Literal (F.Atom (E.Eq (E.TidT t1, E.TidT t2))) ->
        let th1 = conv_th t1 in
        let th2 = conv_th t2
        in
          Eq (th1, th2)
    | F.Literal (F.NegAtom (E.InEq (E.TidT t1, E.TidT t2))) ->
        apply (E.eq_tid t1 t2)
    | F.Literal (F.Atom (E.InEq (E.TidT t1, E.TidT t2))) ->
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


let rec has_pc (expr:expression) : bool =
  match expr with
  | Eq _            -> false
  | InEq _          -> false
  | Pred _          -> false
  | PC _            -> true
  | PCUpdate _      -> true
  | PCRange _       -> true
  | True            -> false
  | False           -> false
  | And (e1,e2)     -> (has_pc e1) || (has_pc e2)
  | Or (e1,e2)      -> (has_pc e1) || (has_pc e2)
  | Not e1          -> (has_pc e1)
  | Implies (e1,e2) -> (has_pc e1) || (has_pc e2)
  | Iff (e1,e2)     -> (has_pc e1) || (has_pc e2)


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


let rec nnf (expr:expression) : expression =
  match expr with
  | False -> False
  | True  -> True
  | Eq _ | InEq _ | Pred _ | PC _ | PCUpdate _ | PCRange _ -> expr
  | Iff (e1,e2)            -> And (nnf (Implies (e1,e2)),nnf (Implies(e2,e1)))
  | Implies(e1,e2)         -> Or (nnf (Not e1), nnf e2)
  | And(e1,e2)             -> And(nnf e1, nnf e2)
  | Or(e1,e2)              -> Or(nnf e1, nnf e2)
  | Not (Not e)            -> nnf e
  | Not (And (e1,e2))      -> Or (nnf (Not e1), nnf (Not e2))
  | Not (Or (e1, e2))      -> And (nnf (Not e1), nnf (Not e2))
  | Not (Implies (e1, e2)) -> And (nnf e1, nnf (Not e2))
  | Not (Iff (e1, e2))     -> Or(And(nnf e1, nnf (Not e2)),And (nnf (Not e1), nnf e2))
  | Not (Eq (x,y))         -> InEq (x,y)
  | Not (InEq (x,y))       -> Eq (x,y)
  | Not True               -> False
  | Not False              -> True
  | Not (Pred _) | Not (PC _) | Not (PCUpdate _) | Not (PCRange _) -> expr


let rec dnf (expr:expression) : expression list list =
  match expr with
    Iff (e1,e2) -> dnf (Or (And (e1,e2), And (Not e1, Not e2)))
  | Implies(e1,e2) -> dnf (Or (Not e1, e2))
  | Or(e1,e2)   -> let e1_dnf = dnf e1 in
                   let e2_dnf = dnf e2 in
                     List.fold_left (fun final_lst x1 ->
                       let lst = List.fold_left (fun l2 x2 ->
                                    (x1 @ x2) :: l2
                                 ) [] e2_dnf
                       in
                          lst @ final_lst
                     ) [] e1_dnf
  | And (e1,e2) -> dnf e1 @ dnf e2
  | Not (Not e) -> dnf e
  | Not (And (e1,e2)) -> dnf (Or (Not e1, Not e2))
  | Not (Or (e1, e2)) -> dnf (And (Not e1, Not e2))
  | Not (Implies (e1, e2)) -> dnf (And (e1, Not e2))
  | Not (Iff (e1, e2)) -> dnf (Or (And (e1, Not e2), And (Not e1, e2)))
  | e -> [[e]]


let rec cnf (expr:expression) : expression list list =
  match expr with
    Iff (e1,e2) -> cnf (Or (And (e1,e2), And (Not e1, Not e2)))
  | Implies(e1,e2) -> cnf (Or (Not e1, e2))
  | And(e1,e2)   -> let e1_cnf = cnf e1 in
                    let e2_cnf = cnf e2 in
                     List.fold_left (fun final_lst x1 ->
                       let lst = List.fold_left (fun l2 x2 ->
                                    (x1 @ x2) :: l2
                                 ) [] e2_cnf
                       in
                          lst @ final_lst
                     ) [] e1_cnf
  | Or (e1,e2) -> cnf e1 @ cnf e2
  | Not (Not e) -> cnf e
  | Not (And (e1,e2)) -> cnf (Or (Not e1, Not e2))
  | Not (Or (e1, e2)) -> cnf (And (Not e1, Not e2))
  | Not (Implies (e1, e2)) -> cnf (And (e1, Not e2))
  | Not (Iff (e1, e2)) -> cnf (Or (And (e1, Not e2), And (Not e1, e2)))
  | e -> [[e]]


(* Vocabulary to variable conversion *)
let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)
