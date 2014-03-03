open LeapLib

module E = Expression
module F = Formula

type sort = Int | Set | Tid

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = unit
  end )

type tid =
  | VarTh of V.t
  | NoTid
and integer =
    Val           of int
  | Var           of V.t
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | SetMin        of set
  | SetMax        of set
and set =
    VarSet        of V.t
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
and term =
  | IntT          of integer
  | SetT          of set
  | FuntermT      of fun_term
  | TidT          of tid
and fun_term =
  | FunVar        of V.t
  | FunUpd        of fun_term * tid * term
and eq =          term * term
and diseq =       term * term
and atom =
    Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | In            of integer * set
  | Subset        of set * set
  | Eq            of eq
  | InEq          of diseq
(*
  | TidEq         of tid * tid
  | TidInEq       of tid * tid
  | FunEq         of fun_term * fun_term
  | FunInEq       of fun_term * fun_term
*)
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula

(*
and literal =
    Atom            of atom
  | NegAtom         of atom
and conjunctive_formula =
    ConjTrue
  | ConjFalse    
  | Conjuncts     of literal list
and formula =
    Literal       of literal
  | True
  | False
  | And           of formula * formula
  | Or            of formula * formula
  | Not           of formula
  | Implies       of formula * formula
  | Iff           of formula * formula
*)


exception NotConjunctiveExpr of formula
exception Not_tid_var of tid

module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )

(*

(**********  Folding  ***************)

type ('info, 'a) fold_ops_t =
  {
    base : 'info -> 'a;
    concat : 'a -> 'a -> 'a;
    var_f : ('info,'a) fold_ops_t -> 'info -> V.t -> 'a;
    mutable tid_f : ('info,'a) fold_ops_t -> 'info -> tid -> 'a;
    mutable int_f : ('info,'a) fold_ops_t -> 'info -> integer -> 'a;
    mutable set_f : ('info,'a) fold_ops_t -> 'info -> set -> 'a;
    mutable funterm_f : ('info,'a) fold_ops_t -> 'info -> fun_term -> 'a;
    mutable atom_f : ('info,'a) fold_ops_t -> 'info -> atom -> 'a;
    mutable term_f : ('info,'a) fold_ops_t -> 'info -> term -> 'a;
  }

type ('info, 'a) folding_t =
  {
    var_f : 'info -> V.t -> 'a;
    tid_f : 'info -> tid -> 'a;
    int_f : 'info -> integer -> 'a;
    set_f : 'info -> set -> 'a;
    funterm_f : 'info -> fun_term -> 'a;
    atom_f : 'info -> atom -> 'a;
    term_f : 'info -> term -> 'a;
  }



let rec fold_tid (fs:('info,'a) fold_ops_t) (info:'info) (t:tid) : 'a =
  match t with
  | VarTh v -> fs.var_f fs info v
  | NoTid   -> fs.base info

and fold_int (fs:('info,'a) fold_ops_t) (info:'info) (i:integer) : 'a =
  match i with
  | Val _ -> fs.base info
  | Var v -> fs.var_f fs info v
  | Neg j -> fs.int_f fs info j
  | Add (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | Sub (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | Mul (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | Div (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | SetMin s -> fs.set_f fs info s
  | SetMax s -> fs.set_f fs info s

and fold_funterm (fs:('info,'a) fold_ops_t) (info:'info) (f:fun_term) : 'a =
  match f with
  | FunVar v -> fs.var_f fs info v
  | FunUpd (ft,th,t) -> fs.concat (fs.funterm_f fs info ft)
                                  (fs.concat (fs.tid_f fs info th)
                                             (fs.term_f fs info t))

and fold_atom (fs:('info,'a) fold_ops_t) (info:'info) (a:atom) : 'a =
  match a with
  | Less(i1,i2)               -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | LessEq(i1,i2)             -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | Greater(i1,i2)            -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | GreaterEq(i1,i2)          -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | LessTid (t1,t2)           -> fs.concat (fs.tid_f fs info t1)
                                           (fs.tid_f fs info t2)
  | In(i,s)                   -> fs.concat (fs.int_f fs info a) (fs.set_f fs info s)
  | Subset(s1,s2)             -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Eq((x,y))                 -> fs.concat (fs.term_f fs info x)
                                           (fs.term_f fs info y)
  | InEq((x,y))               -> fs.concat (fs.term_f fs info x)
                                           (fs.term_f fs info y)
  | PC(pc,th,pr)              -> (match th with
                                   | V.Shared -> fs.base info
                                   | V.Local t -> fs.var_f fs info t)
  | PCUpdate (pc,th)          -> fs.tid_f fs info th
  | PCRange(pc1,pc2,th,pr)    -> (match th with
                                   | V.Shared -> fs.base info
                                   | V.Local t -> fs.var_f fs info t)

and fold_term (fs:('info,'a) fold_ops_t) (info:'info) (t:term) : 'a =
  match t with

  | IntT   i   -> fs.int_f fs info i
  | SetT   s   -> fs.set_f fs info s
  | TidT  th   -> fs.tid_f fs info th
  | FuntermT t -> fs.funterm_f fs info t  


let make_fold ?(tid_f=fold_tid)
              ?(int_f=fold_int)
              ?(set_f=fold_set)
              ?(funterm_f=fold_funterm)
              ?(atom_f=fold_atom)
              ?(term_f=fold_term)
              (base:('info -> 'a))
              (concat:('a -> 'a -> 'a))
              (var_f :(('info,'a) fold_ops_t -> 'info -> V.t -> 'a))
    : ('info,'a) folding_t =
  let fs = {
    tid_f = tid_f; int_f = int_f; set_f = set_f; funterm_f = funterm_f;
    atom_f = atom_f; term_f = term_f;
    base = base; concat = concat; var_f = var_f; } in
  { tid_f = tid_f fs; int_f = int_f fs; set_f = set_f fs;
    funterm_f = funterm_f fs; atom_f = atom_f fs; term_f = term_f fs;
    var_f = var_f fs; }
*)



(*
let var_compare (x:V.t) (y:V.t) : int =
  let cmp_scope p1 p2 = (p1 = GlobalScope && (p2 = GlobalScope || p2 = Scope "")) ||
                        (p2 = GlobalScope && (p1 = GlobalScope || p1 = Scope "")) in
  (* I am not comparing whether ghost/normal kind matches *)
  let cmp = Pervasives.compare (x.id,x.is_primed,x.parameter)
                               (y.id,y.is_primed,y.parameter)
  in
    if cmp = 0 then
      if cmp_scope x.scope y.scope then
        0
      else
        Pervasives.compare x.scope y.scope
    else
      cmp
*)
      
(*
module VarSet = Set.Make(
  struct
    let compare = var_compare
    type t = variable
  end )*)


(* Variable constructor *)
let build_var ?(fresh=false)
              (id:V.id)
              (s:sort)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
  V.build id s pr th p () ~fresh:fresh


(* CONVERTERS TO STRING *)
(* EXPR TO STR *)
let sort_to_str (s:sort) : string =
  match s with
    Int  -> "int"
  | Set  -> "set"
  | Tid -> "tid"

let generic_int_tid_to_str (srf:string -> string) (t:tid) : string =
  match t with
  | VarTh t -> V.to_str t
  | NoTid -> "#"

let rec generic_int_integer_to_str (srf:string -> string) (t:integer) : string =
  let tid_str_f = generic_int_tid_to_str srf in
  let int_str_f = generic_int_integer_to_str srf in
  let set_str_f = generic_int_set_to_str srf in
  match t with
    Val i          -> string_of_int i
  | Var v          -> V.to_str v
  | Neg t          -> srf ("-" ^ int_str_f t)
  | Add (t1,t2)    -> srf (int_str_f t1 ^ " + " ^ int_str_f t2)
  | Sub (t1,t2)    -> srf (int_str_f t1 ^ " - " ^ int_str_f t2)
  | Mul (t1,t2)    -> srf (int_str_f t1 ^ " * " ^ int_str_f t2)
  | Div (t1,t2)    -> srf (int_str_f t1 ^ " / " ^ int_str_f t2)
  | SetMin s       -> srf ("setIntMin(" ^ set_str_f s ^ ")")
  | SetMax s       -> srf ("setIntMax(" ^ set_str_f s ^ ")")


and generic_int_set_to_str (srf:string -> string) (s:set): string =
  let int_str_f = generic_int_integer_to_str srf in
  let set_str_f = generic_int_set_to_str srf in
  match s with
    VarSet v      -> V.to_str v
  | EmptySet      -> srf "emptyset"
  | Singl i       -> srf ("{" ^ int_str_f i ^ "}")
  | Union (s1,s2) -> srf (set_str_f s1 ^ " union " ^ set_str_f s2)
  | Intr (s1,s2)  -> srf (set_str_f s1 ^ " intr "  ^ set_str_f s2)
  | Diff (s1,s2)  -> srf (set_str_f s1 ^ " diff "  ^ set_str_f s2)


and generic_int_term_to_str (srf:string -> string) (t:term) : string =
  match t with
    IntT i -> generic_int_integer_to_str srf i
  | SetT s -> generic_int_set_to_str srf s
  | FuntermT t -> generic_funterm_to_str srf t
  | TidT th -> generic_int_tid_to_str srf th


and generic_funterm_to_str (srf:string -> string) (t:fun_term) : string =
  match t with
    FunVar v        -> V.to_str v
  | FunUpd (f,th,v) -> srf (Printf.sprintf "%s{%s<-%s}"
                            (generic_funterm_to_str srf f)
                            (generic_int_tid_to_str srf th)
                            (generic_int_term_to_str srf v))


let rec generic_atom_to_str (srf:string -> string) (a:atom) : string =
  let tid_str_f  = generic_int_tid_to_str srf in
  let int_str_f  = generic_int_integer_to_str srf in
  let set_str_f  = generic_int_set_to_str srf in
  let term_str_f = generic_int_term_to_str srf in
  let fun_str_f  = generic_funterm_to_str srf in
  match a with
    Less (t1,t2)      -> srf (int_str_f t1  ^ " < "  ^ int_str_f t2)
  | Greater (t1,t2)   -> srf (int_str_f t1  ^ " > "  ^ int_str_f t2)
  | LessEq (t1,t2)    -> srf (int_str_f t1  ^ " <= " ^ int_str_f t2)
  | GreaterEq (t1,t2) -> srf (int_str_f t1  ^ " >= " ^ int_str_f t2)
  | LessTid (th1,th2) -> srf (tid_str_f th1 ^ " < " ^ tid_str_f th2)
  | Eq (t1,t2)        -> srf (term_str_f t1 ^ " = "  ^ term_str_f t2)
  | InEq (t1,t2)      -> srf (term_str_f t1 ^ " != " ^ term_str_f t2)
  | In (i,s)          -> srf (int_str_f i   ^ " in " ^ set_str_f s)
  | Subset (s1,s2)    -> srf (set_str_f s1  ^ " subset " ^ set_str_f s2)
  | PC (pc,th,pr)    -> let i_str = if pr then "pc'" else "pc" in
                        let th_str = V.shared_or_local_to_str th in
                          Printf.sprintf "%s(%s) = %i" i_str th_str pc
  | PCUpdate (pc,th) -> let th_str = tid_str_f th in
                          Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,th,pr) -> let i_str = if pr then "pc'" else "pc" in
                               let th_str = V.shared_or_local_to_str th in
                                 Printf.sprintf "%i <= %s(%s) <= %i" pc1 i_str th_str pc2


(*
let generic_literal_to_str (srf:string -> string) (l:literal) : string =
  match l with
    F.Atom a -> generic_atom_to_str srf a
  | F.NegAtom a -> srf ("~" ^ generic_atom_to_str srf a)


let rec generic_int_formula_to_str (srf:string -> string)
                                      (f:formula) : string =
  match f with
    Literal l        -> generic_literal_to_str srf l
  | True             -> "true"
  | False            -> "false"
  | And (f1,f2)      -> srf (generic_int_formula_to_str srf f1 ^ " /\\ " ^
                             generic_int_formula_to_str srf f2)
  | Or (f1,f2)       -> srf (generic_int_formula_to_str srf f1 ^ " \\/ " ^
                             generic_int_formula_to_str srf f2)
  | Not f1           -> srf ("~" ^ generic_int_formula_to_str srf f1)
  | Implies (f1,f2)  -> srf (generic_int_formula_to_str srf f1 ^ " -> "  ^
                             generic_int_formula_to_str srf f2)
  | Iff (f1,f2)      -> srf (generic_int_formula_to_str srf f1 ^ " <->"  ^
                             generic_int_formula_to_str srf f2)


let conjlit_to_str (srf:string -> string) (cl:conjunctive_formula) :string =
  match cl with
    ConjTrue     -> "true"
  | ConjFalse    -> "false"
  | Conjuncts ls -> String.concat " /\\ " $ List.map (generic_literal_to_str srf) ls
*)




and no_parenthesis (str:string) : string = str
and add_parenthesis (str:string) : string = "(" ^ str ^ ")"

(* No parenthesis printing functions *)
and integer_to_str (t:integer) : string =
  generic_int_integer_to_str no_parenthesis t

and funterm_to_str (t:fun_term) : string =
  generic_funterm_to_str no_parenthesis t

and atom_to_str (a:atom) : string =
  generic_atom_to_str no_parenthesis a

and literal_to_str (l:literal) : string =
  Formula.literal_to_str (generic_atom_to_str no_parenthesis) l

and formula_to_str (phi:formula) : string =
  Formula.formula_to_str (generic_atom_to_str no_parenthesis) phi
(*  generic_int_formula_to_str no_parenthesis f*)



(* Parenthesis printing functions *)
let integer_to_par_string (t:integer) : string =
  generic_int_integer_to_str add_parenthesis t

let funterm_to_par_string (t:fun_term) : string =
  generic_funterm_to_str add_parenthesis t

let literal_to_par_string (l:literal) : string =
  Formula.literal_to_str (generic_atom_to_str no_parenthesis) l

let formula_to_par_string (phi:formula) : string =
  Formula.formula_to_str (generic_atom_to_str no_parenthesis) phi
(*  generic_int_formula_to_str add_parenthesis f*)




(* CHECKERS *)
(*
let rec is_int_formula (phi:E.formula) : bool =
  match phi with
    E.Literal(l)         -> (is_int_literal l)
  | E.True               -> true
  | E.False              -> true
  | E.And(x,y)           -> (is_int_formula x) && (is_int_formula y)
  | E.Or(x,y)            -> (is_int_formula x) && (is_int_formula y)
  | E.Not(x)             -> (is_int_formula x)
  | E.Implies(x,y)       -> (is_int_formula x) && (is_int_formula y)
  | E.Iff(x,y)           -> (is_int_formula x) && (is_int_formula y)
and is_int_literal lit =
  match lit with
    E.Atom a   -> is_int_atom a
  | E.NegAtom a -> is_int_atom a
*)
let rec is_int_atom ato =
  match ato with
    E.Append(_,_,_)                    -> false
  | E.Reach(_,_,_,_)                   -> false
  | E.ReachAt(_,_,_,_,_)               -> false
  | E.OrderList(_,_,_)                 -> false
  | E.Skiplist(_,_,_,_,_,_)            -> false
  | E.In(_,_)                          -> false
  | E.SubsetEq(_,_)                    -> false
  | E.InTh(_,_)                        -> false
  | E.SubsetEqTh(_,_)                  -> false
  | E.InInt(_,_)                       -> false
  | E.SubsetEqInt(_,_)                 -> false
  | E.InElem(_,_)                      -> false
  | E.SubsetEqElem(_,_)                -> false
  | E.Less(_,_)                        -> true
  | E.Greater(_,_)                     -> true
  | E.LessEq(_,_)                      -> true
  | E.GreaterEq(_,_)                   -> true
  | E.LessTid(_,_)                     -> true
  | E.LessElem(_,_)                    -> true
  | E.GreaterElem(_,_)                 -> true
  | E.Eq(E.TidT _, E.TidT _)   -> true
  | E.InEq(E.TidT _, E.TidT _) -> true
  | E.Eq(x,y)                          -> (is_int_integer x) && (is_int_integer y)
  | E.InEq(x,y)                        -> (is_int_integer x) && (is_int_integer y)
  | E.BoolVar _                        -> false
  | E.BoolArrayRd (_,_)                -> false
  | E.PC(_)                            -> true
  | E.PCUpdate(_)                      -> true
  | E.PCRange(_)                       -> true
and is_int_integer t =
  match t with
    E.VarT(_)       -> false
  | E.SetT(_)       -> false
  | E.ElemT(_)      -> false
  | E.TidT(_)       -> false
  | E.AddrT(_)      -> false
  | E.CellT(_)      -> false
  | E.SetThT(_)     -> false
  | E.SetIntT(_)    -> false
  | E.SetElemT(_)   -> false
  | E.PathT(_)      -> false
  | E.MemT(_)       -> false
  | E.IntT(_)       -> true
  | E.ArrayT(_)     -> false
  | E.AddrArrayT(_) -> false
  | E.TidArrayT(_)  -> false
and is_int_expression e = 
  match e with
    E.Term(t)      -> is_int_integer t
  | E.Formula(phi) -> is_int_formula phi

and is_int_fs () = Formula.make_fold
                     Formula.GenericLiteralFold
                     (fun info a -> is_int_atom a)
                     (fun info -> true)
                     (&&)

and is_int_formula (phi:E.formula) : bool =
  Formula.formula_fold (is_int_fs()) () phi


(* CONJUNCTIONS OF LITERAL *)

(*
let formula_to_conj_literals (phi:formula) : literal list =
  let rec try_to_build_conjunction x =
    match x with
     Literal l -> [l]
    | And(a,b)  -> (try_to_build_conjunction a) @ (try_to_build_conjunction b)
    | True      -> []
    |   _       -> Printf.printf "Error: %s\n" (formula_to_str phi);
                   raise(NotConjunctiveExpr phi)
  in
    try_to_build_conjunction phi
*)

(*
let list_literals_to_formula (lits:literal list) : formula =
  match lits with
   [] -> True
  | l::ls -> let folder phi l = And(phi,Literal(l)) in
               (List.fold_left folder (Literal l) ls)
  *)

(*
let conj_literals_to_formula (conj:coVnjunctive_formula) : formula =
  match conj with
    ConjTrue   -> True
  | ConjFalse -> False
  | Conjuncts cs -> list_literals_to_formula cs
*)


(* has_variable : integer -> bool *)

let rec has_variable (t:integer) : bool =
  match t with
      Val(n)       -> false
    | Var _        -> true
    | Neg(x)       -> has_variable x
    | Add(x,y)     -> has_variable x || has_variable y
    | Sub(x,y)     -> has_variable x || has_variable y
    | Mul(x,y)     -> has_variable x || has_variable y
    | Div(x,y)     -> has_variable x || has_variable y
    | SetMin(s)    -> false
    | SetMax(s)    -> false


(* formula_is_linear : formula -> bool *)
(* term_is_linear    : term    -> bool *)
(* literal_is_linear : literal -> bool *)
(* expr_is_linear    : expr    -> bool *)


(*
let rec formula_is_linear (phi:formula) : bool =
  let is_linear = formula_is_linear in
    match phi with
      Literal(l)   -> literal_is_linear l
    | True         -> true
    | False        -> true
    | And(x,y)     -> (is_linear x) && (is_linear y)
    | Or(x,y)      -> (is_linear x) && (is_linear y)
    | Not(x)       -> (is_linear x)
    | Implies(x,y) -> (is_linear x) && (is_linear y)
    | Iff(x,y)     -> (is_linear x) && (is_linear y)
*)

let rec term_is_linear t =
  let is_linear = term_is_linear in
    match t with
      Val(_)         -> true
    | Var _          -> true
    | Neg(t)         -> is_linear t
    | Add(x,y)       -> (is_linear x) && (is_linear y)
    | Sub(x,y)       -> (is_linear x) && (is_linear y)
    | Mul(x,y)       -> (is_linear x) && (is_linear y) &&
                        ( not ((has_variable x) && (has_variable y)))
    | Div(x,y)       -> false
    | SetMin(s)      -> true
    | SetMax(s)      -> true
(*
and literal_is_linear l =
  match l with
    Atom a    -> (atom_is_linear a)
  | NegAtom a -> (atom_is_linear a)
*)

and atom_is_linear a =
  let is_linear = term_is_linear in
  match a with
    Less(x,y)            -> (is_linear x) && (is_linear y)
  | Greater(x,y)         -> (is_linear x) && (is_linear y)
  | LessEq(x,y)          -> (is_linear x) && (is_linear y)
  | GreaterEq(x,y)       -> (is_linear x) && (is_linear y)
  | LessTid(x,y)         -> false
  | Eq(IntT x,IntT y)    -> (is_linear x) && (is_linear y)
  | InEq(IntT x, IntT y) -> (is_linear x) && (is_linear y)
  | Eq(_,_)              -> false
  | InEq(_,_)            -> false
  | In (_,_)             -> false
  | Subset (_,_)         -> false
  | PC _                 -> false
  | PCUpdate _           -> false
  | PCRange _            -> false

and is_linear_fs () = Formula.make_fold
                        Formula.GenericLiteralFold
                        (fun info a -> atom_is_linear a)
                        (fun info -> true)
                        (&&)

and formula_is_linear (phi:formula) : bool =
  Formula.formula_fold (is_linear_fs()) () phi



(* FOR SETVAR *)
let rec generic_set_from_int_integer (base:V.t -> 'a)
                                     (empty:'a)
                                     (union:'a -> 'a -> 'a)
                                     (t:integer) : 'a =
  match t with
    Val i          -> empty
  | Var v          -> base v
  | Neg t          -> generic_set_from_int_integer base empty union t
  | Add (t1,t2)    -> union (generic_set_from_int_integer
                                base empty union t1)
                            (generic_set_from_int_integer
                                base empty union t2)
  | Sub (t1,t2)    -> union (generic_set_from_int_integer
                                base empty union t1)
                            (generic_set_from_int_integer
                                base empty union t2)
  | Mul (t1,t2)    -> union (generic_set_from_int_integer
                                base empty union t1)
                            (generic_set_from_int_integer
                                base empty union t2)
  | Div (t1,t2)    -> union (generic_set_from_int_integer
                                base empty union t1)
                            (generic_set_from_int_integer
                                base empty union t2)
  | SetMin s       -> generic_set_from_int_set base empty union s
  | SetMax s       -> generic_set_from_int_set base empty union s


and generic_set_from_funterm (base:V.t -> 'a)
                             (empty:'a)
                             (union:'a -> 'a -> 'a)
                             (t:fun_term) : 'a =
  match t with
    FunVar (v)      -> base v
  | FunUpd (f,th,v) -> generic_set_from_funterm base empty union f


and generic_set_from_int_set (base:V.t -> 'a)
                             (empty:'a)
                             (union:'a -> 'a -> 'a)
                             (s:set) : 'a =
  let int_f  = generic_set_from_int_integer base empty union in
  let set_f  = generic_set_from_int_set base empty union in
  match s with
    VarSet (v)    -> base v
  | EmptySet      -> empty
  | Singl i       -> int_f i
  | Union (s1,s2) -> union (set_f s1) (set_f s2)
  | Intr (s1,s2)  -> union (set_f s1) (set_f s2)
  | Diff (s1,s2)  -> union (set_f s1) (set_f s2)


let generic_set_from_int_term (base:V.t -> 'a)
                              (empty:'a)
                              (union:'a -> 'a -> 'a)
                              (t:term) : 'a =
  match t with
    IntT i -> generic_set_from_int_integer base empty union i
  | SetT s -> generic_set_from_int_set base empty union s
  | FuntermT t -> generic_set_from_funterm base empty union t
  | TidT th -> empty


let generic_set_from_int_atom (base:V.t -> 'a)
                              (empty:'a)
                              (union:'a -> 'a -> 'a)
                              (a:atom) : 'a =
  let int_f  = generic_set_from_int_integer base empty union in
  let set_f  = generic_set_from_int_set base empty union in
  let term_f = generic_set_from_int_term base empty union in
  let fun_f  = generic_set_from_funterm base empty union in
  match a with
    Less (t1,t2)      -> union (int_f t1) (int_f t2)
  | Greater (t1,t2)   -> union (int_f t1) (int_f t2)
  | LessEq (t1,t2)    -> union (int_f t1) (int_f t2)
  | GreaterEq (t1,t2) -> union (int_f t1) (int_f t2)
  | LessTid (th1,th2) -> empty
  | Eq (t1,t2)        -> union (term_f t1) (term_f t2)
  | InEq (t1,t2)      -> union (term_f t1) (term_f t2)
  | In (i,s)          -> union (int_f i) (set_f s)
  | Subset (s1,s2)    -> union (set_f s1) (set_f s2)
  | PC (pc,th,pr)     -> empty
  | PCUpdate (pc,th)  -> empty
  | PCRange (_,_,_,_) -> empty


let varset_fs = Formula.make_fold
                  Formula.GenericLiteralFold
                  (fun info a -> generic_set_from_int_atom info V.VarSet.empty V.VarSet.union a)
                  (fun info -> V.VarSet.empty)
                  V.VarSet.union


let varset_from_int_formula (base:V.t -> 'a)
                            (phi:formula) : 'a =
  Formula.formula_fold varset_fs base phi


let varidset_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (fun info a -> generic_set_from_int_atom info V.VarIdSet.empty V.VarIdSet.union a)
                    (fun info -> V.VarIdSet.empty)
                    V.VarIdSet.union


let varidset_from_int_formula (base:V.t -> 'a)
                              (phi:formula) : 'a =
  Formula.formula_fold varidset_fs base phi
                                 


(*
let generic_set_from_int_literal (base:V.t -> 'a)
                                 (empty:'a)
                                 (union:'a -> 'a -> 'a)
                                 (l:literal) : 'a =
  match l with
    Atom a    -> generic_set_from_int_atom base empty union a
  | NegAtom a -> generic_set_from_int_atom base empty union a
  

let rec generic_set_from_int_formula (base:V.t -> 'a)
                                     (empty:'a)
                                     (union:'a -> 'a -> 'a)
                                     (f:formula) : 'a =
  match f with
    Literal l        -> generic_set_from_int_literal base empty union l
  | True             -> empty
  | False            -> empty
  | And (f1,f2)      -> union (generic_set_from_int_formula base empty union f1)
                              (generic_set_from_int_formula base empty union f2)
  | Or (f1,f2)       -> union (generic_set_from_int_formula base empty union f1)
                              (generic_set_from_int_formula base empty union f2)
  | Not f            -> generic_set_from_int_formula base empty union f
  | Implies (f1,f2)  -> union (generic_set_from_int_formula base empty union f1)
                              (generic_set_from_int_formula base empty union f2)
  | Iff (f1,f2)      -> union (generic_set_from_int_formula base empty union f1)
                              (generic_set_from_int_formula base empty union f2)
*)

(*
let conjlit_to_str (base:V.t -> 'a)
                      (empty:'a)
                      (union:'a -> 'a -> 'a)
                      (cl:conjunctive_formula) : 'a =
  match cl with
    ConjTrue     -> empty
  | ConjFalse    -> empty
  | Conjuncts ls -> List.fold_left (fun s l ->
                      union s (generic_set_from_int_literal base empty union l)
                    ) ls empty
*)

(* Base functions for variables id *)

let base_setid_all_vars (v:V.t) : V.VarIdSet.t =
  V.VarIdSet.singleton (V.id v)


let base_setid_local_vars (v:V.t) : V.VarIdSet.t =
  match (V.scope v) with
  | V.Scope _ -> V.VarIdSet.singleton (V.id v)
  | V.GlobalScope -> V.VarIdSet.empty


let base_setid_global_vars (v:V.t) : V.VarIdSet.t =
  match (V.scope v) with
  | V.GlobalScope -> V.VarIdSet.singleton (V.id v)
  | V.Scope _ -> V.VarIdSet.empty



(* Functions for all variables *)

let vset_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_setid_all_vars phi


(* Functions for global variables *)

let global_vset_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_setid_global_vars phi


(* Functions for local variables *)

let local_vset_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_setid_local_vars phi



let all_varid_set         = vset_from_int_formula
(*let all_varid_set_literal = vset_from_int_literal *)
let all_global_varid_set  = global_vset_from_int_formula
let all_local_varid_set   = local_vset_from_int_formula

let all_varid phi         = V.VarIdSet.elements (all_varid_set phi)
(*let all_varid_literal l   = V.VarIdSet.elements (all_varid_set_literal l) *)
let all_local_varid phi   = V.VarIdSet.elements (all_local_varid_set phi)
let all_global_varid phi  = V.VarIdSet.elements (all_global_varid_set phi)



(* Base functions for full variables *)

let base_set_all_vars (v:V.t) : V.VarSet.t =
  V.VarSet.singleton v


let base_set_local_vars (v:V.t) : V.VarSet.t =
  if (V.scope v) <> V.GlobalScope && (V.scope v) <> V.Scope "" then
    V.VarSet.singleton v
  else
    V.VarSet.empty


let base_set_global_vars (v:V.t) : V.VarSet.t =
  if (V.scope v) = V.GlobalScope || (V.scope v) = V.Scope "" then
    V.VarSet.singleton v
  else
    V.VarSet.empty



(* Functions for all variables *)

let var_set_from_int_formula (phi:formula) : V.VarSet.t =
  varset_from_int_formula base_set_all_vars phi



(* Functions for global variables *)

let var_global_set_from_int_formula (phi:formula) : V.VarSet.t =
  varset_from_int_formula base_set_global_vars phi


(* Functions for local variables *)

let var_local_set_from_int_formula (phi:formula) : V.VarSet.t =
  varset_from_int_formula base_set_local_vars phi



let all_vars_set         = var_set_from_int_formula
(*let all_vars_set_literal = var_set_from_int_literal*)
let all_global_vars_set  = var_global_set_from_int_formula
let all_local_vars_set   = var_local_set_from_int_formula


let all_vars phi        = V.VarSet.elements (all_vars_set phi)
(*let all_vars_literal l  = V.VarSet.elements (all_vars_set_literal l)*)
let all_global_vars phi = V.VarSet.elements (all_global_vars_set phi)
let all_local_vars phi  = V.VarSet.elements (all_local_vars_set phi)


let filter_var_set (v_set:V.VarSet.t) : V.t list =
  let filtered_set = V.VarSet.fold (fun v s ->
                       V.VarSet.add (V.unparam v) s
                     ) v_set V.VarSet.empty
  in
    V.VarSet.elements filtered_set


let all_global_vars_without_param (phi:formula) : V.t list =
  filter_var_set (all_global_vars_set phi)


let all_local_vars_without_param (phi:formula) : V.t list =
  filter_var_set (all_local_vars_set phi)



(* Primed vars *)

let base_primed_vars (v:V.t) : V.VarIdSet.t =
   if V.is_primed v then
    V.VarIdSet.singleton (V.id v)
  else
    V.VarIdSet.empty


let vset_primed_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_primed_vars phi



(* List of vars *)
let base_list_vars (v:V.t) : V.VarIdSet.t =
  V.VarIdSet.singleton (V.id v)


let vlist_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_list_vars phi


(* Vocabulary functions *)
let opt_th (th:V.shared_or_local) : ThreadSet.t =
  match th with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


let thset_from (ths:tid list) : ThreadSet.t =
  List.fold_left (fun s t -> ThreadSet.add t s) ThreadSet.empty ths


let rec voc_from_int_integer (t:integer) : ThreadSet.t =
  match t with
    Val i                  -> ThreadSet.empty
  | Var v                  -> opt_th (V.parameter v)
  | Neg t                  -> voc_from_int_integer t
  | Add (t1,t2)            -> ThreadSet.union (voc_from_int_integer t1)
                                                (voc_from_int_integer t2)
  | Sub (t1,t2)            -> ThreadSet.union (voc_from_int_integer t1)
                                                (voc_from_int_integer t2)
  | Mul (t1,t2)            -> ThreadSet.union (voc_from_int_integer t1)
                                                (voc_from_int_integer t2)
  | Div (t1,t2)            -> ThreadSet.union (voc_from_int_integer t1)
                                                (voc_from_int_integer t2)
  | SetMin s               -> ThreadSet.empty
  | SetMax s               -> ThreadSet.empty


let voc_from_funterm (t:fun_term) : ThreadSet.t =
  match t with
    FunVar v        -> opt_th (V.parameter v)
  | FunUpd (f,th,v) -> ThreadSet.singleton th


let rec voc_from_int_set (s:set) : ThreadSet.t =
  match s with
    VarSet v      -> opt_th (V.parameter v)
  | EmptySet      -> ThreadSet.empty
  | Singl i       -> voc_from_int_integer i
  | Union (s1,s2) -> ThreadSet.union (voc_from_int_set s1)
                                       (voc_from_int_set s2)
  | Intr (s1,s2)  -> ThreadSet.union (voc_from_int_set s1)
                                       (voc_from_int_set s2)
  | Diff (s1,s2)  -> ThreadSet.union (voc_from_int_set s1)
                                       (voc_from_int_set s2)


let voc_from_int_term (t:term) : ThreadSet.t =
  match t with
    IntT i -> voc_from_int_integer i
  | SetT s -> voc_from_int_set s
  | FuntermT t -> voc_from_funterm t
  | TidT th -> ThreadSet.singleton th


let voc_from_int_atom (a:atom) : ThreadSet.t =
  let union = ThreadSet.union in
  let voc_int  = voc_from_int_integer in
  let voc_term = voc_from_int_term in
  let voc_set  = voc_from_int_set in
  match a with
    Less (t1,t2)      -> union (voc_int t1) (voc_int t2)
  | Greater (t1,t2)   -> union (voc_int t1) (voc_int t2)
  | LessEq (t1,t2)    -> union (voc_int t1) (voc_int t2)
  | GreaterEq (t1,t2) -> union (voc_int t1) (voc_int t2)
  | LessTid (th1,th2) -> thset_from [th1;th2]
  | Eq (t1,t2)        -> union (voc_term t1) (voc_term t2)
  | InEq (t1,t2)      -> union (voc_term t1) (voc_term t2)
  | In (i,s)          -> union (voc_int i) (voc_set s)
  | Subset (s1,s2)    -> union (voc_set s1) (voc_set s2)
  | PC (pc,th,pr)     -> opt_th th
  | PCUpdate (pc,th)  -> ThreadSet.singleton th
  | PCRange (_,_,th,_)-> opt_th th

let voc_fs = Formula.make_fold
               Formula.GenericLiteralFold
               (fun info a -> voc_from_int_atom a)
               (fun info -> ThreadSet.empty)
               ThreadSet.union

let voc_from_int_formula (phi:formula) : ThreadSet.t =
  Formula.formula_fold voc_fs () phi


(*
let voc_from_int_literal (l:literal) : ThreadSet.t =
  match l with
    Atom a    -> voc_from_int_atom a
  | NegAtom a -> voc_from_int_atom a


let rec voc_from_int_formula (f:formula) : ThreadSet.t =
  let union = ThreadSet.union in
  let empty = ThreadSet.empty in
  let voc_formula = voc_from_int_formula in
  match f with
    Literal l        -> voc_from_int_literal l
  | True             -> empty
  | False            -> empty
  | And (f1,f2)      -> union (voc_formula f1) (voc_formula f2)
  | Or (f1,f2)       -> union (voc_formula f1) (voc_formula f2)
  | Not f            -> voc_formula f
  | Implies (f1,f2)  -> union (voc_formula f1) (voc_formula f2)
  | Iff (f1,f2)      -> union (voc_formula f1) (voc_formula f2)



let voc_from_conjlit (cl:conjunctive_formula) : ThreadSet.t =
  match cl with
    ConjTrue     -> ThreadSet.empty
  | ConjFalse    -> ThreadSet.empty
  | Conjuncts ls -> List.fold_left (fun s l ->
                      ThreadSet.union s (voc_from_int_literal l)
                    ) ThreadSet.empty ls
*)



let voc (phi:formula) : tid list =
  ThreadSet.elements (voc_from_int_formula phi)


let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)
