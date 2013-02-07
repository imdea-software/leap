open LeapLib

module Expr = Expression

exception NotAnIntExpression of string
exception NotIntSort of string
exception MalformedExpression of string

type sort = Int | Set | Thid

type varId = Expr.varId

type tid = Expr.tid

type variable = varId * sort * bool * tid option * string option


type integer =
    Val           of int
  | Var           of variable
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | ArrayRd       of Expr.arrays * Expr.tid
  | SetMin        of set
  | SetMax        of set
and set =
    VarSet        of variable
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
and term =
  | IntV          of integer
  | SetV          of set
and fun_term =
  | FunVar        of variable
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
  | TidEq         of tid * tid
  | TidInEq       of tid * tid
  | FunEq         of fun_term * fun_term
  | FunInEq       of fun_term * fun_term
  | PC            of int * tid option * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * tid option * bool
and literal =
    Atom            of atom
  | NegAtom         of atom
and conjunction_literals =
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


let var_compare (x:variable) (y:variable) : int =
  let cmp_p p1 p2 = (p1 = None && (p2 = None || p2 = Some"")) ||
                    (p2 = None && (p1 = None || p1 = Some"")) in
  (* I am not comparing whether ghost/normal kind matches *)
  let (x_id, x_s, x_pr, x_th, x_p) = x in
  let (y_id, y_s, y_pr, y_th, y_p) = y in
  let cmp = Pervasives.compare (x_id,x_pr,x_th) (y_id,y_pr,y_th)
  in
    if cmp = 0 then
      if cmp_p x_p y_p then
        0
      else
        Pervasives.compare x_p y_p
    else
      cmp
      

module VarSet = Set.Make(
  struct
    let compare = var_compare
    type t = variable
  end )


(* Variable constructor *)
let build_var (id:varId)
              (s:sort)
              (pr:bool)
              (th:tid option)
              (p:string option) : variable =
  (id,s,pr,th,p)


let get_sort (v:variable) : sort =
  let (_,s,_,_,_) = v in s


let is_primed_var (v:variable) : bool =
  let (_,_,pr,_,_) = v in pr


let get_proc (v:variable) : string option =
  let (_,_,_,_,p) = v in p


let get_th (v:variable) : tid option =
  let (_,_,_,th,_) = v in th


let get_id (v:variable) : varId =
  let (id,_,_,_,_) = v in id


let var_clear_param_info (v:variable) : variable =
  let (id,s,pr,_,p) = v
  in
    build_var id s pr None p


let param_var (v:variable) (th:tid) : variable =
  let (id,s,pr,_,p) = v
  in
    build_var id s pr (Some th) p


let var_is_global (v:variable) : bool =
  let (_,_,_,th,p) = v
  in
    (p = None || p = Some "") && th = None



(* Sort conversion *)
let sort_to_int_sort (s:Expr.sort) : sort =
  match s with
    Expr.Int    -> Int
  | Expr.SetInt -> Set
  | Expr.Thid   -> Thid
  | _           -> RAISE(NotIntSort(Expr.sort_to_str s))


let int_sort_to_sort (s:sort) : Expr.sort =
  match s with
    Int  -> Expr.Int
  | Set  -> Expr.SetInt
  | Thid -> Expr.Thid



(* CONVERTERS TO STRING *)
(* EXPR TO STR *)
let sort_to_string (s:sort) : string =
  match s with
    Int  -> "int"
  | Set  -> "set"
  | Thid -> "tid"


let variable_to_string (v:variable) : string =
  let (id,s,pr,th,p) =  v in
  let var_str = (Expr.loc_var_option id p) ^ (Expr.tid_option_to_str th)
  in
    if pr then var_str ^ "'" else var_str


let rec generic_int_integer_to_string (srf:string -> string) (t:integer) : string =
  let int_str_f = generic_int_integer_to_string srf in
  let set_str_f = generic_int_set_to_string srf in
  match t with
    Val i          -> string_of_int i
  | Var v          -> variable_to_string v
  | Neg t          -> srf ("-" ^ int_str_f t)
  | Add (t1,t2)    -> srf (int_str_f t1 ^ " + " ^ int_str_f t2)
  | Sub (t1,t2)    -> srf (int_str_f t1 ^ " - " ^ int_str_f t2)
  | Mul (t1,t2)    -> srf (int_str_f t1 ^ " * " ^ int_str_f t2)
  | Div (t1,t2)    -> srf (int_str_f t1 ^ " / " ^ int_str_f t2)
  | ArrayRd (a,th) -> srf (Expr.arrays_to_str a ^ "[" ^
                           Expr.tid_to_str th ^ "]")
  | SetMin s       -> srf ("setIntMin(" ^ set_str_f s ^ ")")
  | SetMax s       -> srf ("setIntMax(" ^ set_str_f s ^ ")")


and generic_int_set_to_string (srf:string -> string) (s:set): string =
  let int_str_f = generic_int_integer_to_string srf in
  let set_str_f = generic_int_set_to_string srf in
  match s with
    VarSet v      -> variable_to_string v
  | EmptySet      -> srf "emptyset"
  | Singl i       -> srf ("{" ^ int_str_f i ^ "}")
  | Union (s1,s2) -> srf (set_str_f s1 ^ " union " ^ set_str_f s2)
  | Intr (s1,s2)  -> srf (set_str_f s1 ^ " intr "  ^ set_str_f s2)
  | Diff (s1,s2)  -> srf (set_str_f s1 ^ " diff "  ^ set_str_f s2)


let generic_int_term_to_string (srf:string -> string) (t:term) : string =
  match t with
    IntV i -> generic_int_integer_to_string srf i
  | SetV s -> generic_int_set_to_string srf s


let rec generic_funterm_to_string (srf:string -> string) (t:fun_term) : string =
  match t with
    FunVar v        -> variable_to_string v
  | FunUpd (f,th,v) -> srf (Printf.sprintf "%s{%s<-%s}"
                            (generic_funterm_to_string srf f)
                            (Expr.tid_to_str th)
                            (generic_int_term_to_string srf v))


let generic_atom_to_string (srf:string -> string) (a:atom) : string =
  let int_str_f  = generic_int_integer_to_string srf in
  let set_str_f  = generic_int_set_to_string srf in
  let term_str_f = generic_int_term_to_string srf in
  let fun_str_f  = generic_funterm_to_string srf in
  match a with
    Less (t1,t2)      -> srf (int_str_f t1  ^ " < "  ^ int_str_f t2)
  | Greater (t1,t2)   -> srf (int_str_f t1  ^ " > "  ^ int_str_f t2)
  | LessEq (t1,t2)    -> srf (int_str_f t1  ^ " <= " ^ int_str_f t2)
  | GreaterEq (t1,t2) -> srf (int_str_f t1  ^ " >= " ^ int_str_f t2)
  | LessTid (th1,th2) -> srf (Expr.tid_to_str th1 ^ " < " ^ Expr.tid_to_str th2)
  | Eq (t1,t2)        -> srf (term_str_f t1 ^ " = "  ^ term_str_f t2)
  | InEq (t1,t2)      -> srf (term_str_f t1 ^ " != " ^ term_str_f t2)
  | In (i,s)          -> srf (int_str_f i   ^ " in " ^ set_str_f s)
  | Subset (s1,s2)    -> srf (set_str_f s1  ^ " subset " ^ set_str_f s2)
  | TidEq (th1,th2)   -> srf (Expr.tid_to_str th1   ^ " = "  ^
                              Expr.tid_to_str th2)
  | TidInEq (th1,th2) -> srf (Expr.tid_to_str th1   ^ " != " ^
                              Expr.tid_to_str th2)
  | FunEq (f1,f2)     -> srf (fun_str_f f1  ^ " = "  ^ fun_str_f f2)
  | FunInEq (f1,f2)   -> srf (fun_str_f f1  ^ " != " ^ fun_str_f f2)
  | PC (pc,th,pr)    -> let i_str  = if pr then "pc" else "pc'" in
                        let th_str = Expr.tid_option_to_str th in
                          Printf.sprintf "%s(%s) = %i" i_str th_str pc
  | PCUpdate (pc,th) -> let th_str = Expr.tid_to_str th in
                          Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,th,pr) -> let i_str  = if pr then "pc" else "pc'" in
                               let th_str = Expr.tid_option_to_str th in
                                 Printf.sprintf "%i <= %s(%s) <= %i" pc1 i_str th_str pc2



let generic_literal_to_string (srf:string -> string) (l:literal) : string =
  match l with
    Atom a -> generic_atom_to_string srf a
  | NegAtom a -> srf ("~" ^ generic_atom_to_string srf a)


let rec generic_int_formula_to_string (srf:string -> string)
                                      (f:formula) : string =
  match f with
    Literal l        -> generic_literal_to_string srf l
  | True             -> "true"
  | False            -> "false"
  | And (f1,f2)      -> srf (generic_int_formula_to_string srf f1 ^ " /\\ " ^
                             generic_int_formula_to_string srf f2)
  | Or (f1,f2)       -> srf (generic_int_formula_to_string srf f1 ^ " \\/ " ^
                             generic_int_formula_to_string srf f2)
  | Not f1           -> srf ("~" ^ generic_int_formula_to_string srf f1)
  | Implies (f1,f2)  -> srf (generic_int_formula_to_string srf f1 ^ " -> "  ^
                             generic_int_formula_to_string srf f2)
  | Iff (f1,f2)      -> srf (generic_int_formula_to_string srf f1 ^ " <->"  ^
                             generic_int_formula_to_string srf f2)


let conjlit_to_string (srf:string -> string) (cl:conjunction_literals) :string =
  match cl with
    ConjTrue     -> "true"
  | ConjFalse    -> "false"
  | Conjuncts ls -> String.concat " /\\ " $ List.map (generic_literal_to_string srf) ls




let no_parenthesis (str:string) : string = str
let add_parenthesis (str:string) : string = "(" ^ str ^ ")"

(* No parenthesis printing functions *)
let int_integer_to_string (t:integer) : string =
  generic_int_integer_to_string no_parenthesis t

let funterm_to_string (t:fun_term) : string =
  generic_funterm_to_string no_parenthesis t

let int_atom_to_string (a:atom) : string =
  generic_atom_to_string no_parenthesis a

let int_literal_to_string (l:literal) : string =
  generic_literal_to_string no_parenthesis l

let int_formula_to_string (f:formula) : string =
  generic_int_formula_to_string no_parenthesis f



(* Parenthesis printing functions *)
let int_integer_to_par_string (t:integer) : string =
  generic_int_integer_to_string add_parenthesis t

let funterm_to_par_string (t:fun_term) : string =
  generic_funterm_to_string add_parenthesis t

let int_literal_to_par_string (l:literal) : string =
  generic_literal_to_string add_parenthesis l

let int_formula_to_par_string (f:formula) : string =
  generic_int_formula_to_string add_parenthesis f




(* CHECKERS *)

(* is_int_formula    : Expr.formula -> bool  *)
(* is_int_literal    : Expr.literal -> bool  *)
(* is_int_integer      : Expr.term    -> bool  *)
(* is_int_expression : Expr.expr    -> bool  *)

let rec is_int_formula (phi:Expr.formula) : bool =
  match phi with
    Expr.Literal(l)         -> (is_int_literal l)
  | Expr.True               -> true
  | Expr.False              -> true
  | Expr.And(x,y)           -> (is_int_formula x) && (is_int_formula y)
  | Expr.Or(x,y)            -> (is_int_formula x) && (is_int_formula y)
  | Expr.Not(x)             -> (is_int_formula x)
  | Expr.Implies(x,y)       -> (is_int_formula x) && (is_int_formula y)
  | Expr.Iff(x,y)           -> (is_int_formula x) && (is_int_formula y)
and is_int_literal lit =
  match lit with
    Expr.Atom a   -> is_int_atom a
  | Expr.NegAtom a -> is_int_atom a
and is_int_atom ato =
  match ato with
    Expr.Append(_,_,_)                    -> false
  | Expr.Reach(_,_,_,_)                   -> false
  | Expr.ReachAt(_,_,_,_,_)               -> false
  | Expr.OrderList(_,_,_)                 -> false
  | Expr.Skiplist(_,_,_,_,_)              -> false
  | Expr.In(_,_)                          -> false
  | Expr.SubsetEq(_,_)                    -> false
  | Expr.InTh(_,_)                        -> false
  | Expr.SubsetEqTh(_,_)                  -> false
  | Expr.InInt(_,_)                       -> false
  | Expr.SubsetEqInt(_,_)                 -> false
  | Expr.InElem(_,_)                      -> false
  | Expr.SubsetEqElem(_,_)                -> false
  | Expr.Less(_,_)                        -> true
  | Expr.Greater(_,_)                     -> true
  | Expr.LessEq(_,_)                      -> true
  | Expr.GreaterEq(_,_)                   -> true
  | Expr.LessTid(_,_)                     -> true
  | Expr.LessElem(_,_)                    -> true
  | Expr.GreaterElem(_,_)                 -> true
  | Expr.Eq(Expr.ThidT _, Expr.ThidT _)   -> true
  | Expr.InEq(Expr.ThidT _, Expr.ThidT _) -> true
  | Expr.Eq(x,y)                          -> (is_int_integer x) && (is_int_integer y)
  | Expr.InEq(x,y)                        -> (is_int_integer x) && (is_int_integer y)
  | Expr.BoolVar _                        -> false
  | Expr.BoolArrayRd (_,_)                -> false
  | Expr.PC(_)                            -> true
  | Expr.PCUpdate(_)                      -> true
  | Expr.PCRange(_)                       -> true
and is_int_integer t =
  match t with
    Expr.VarT(_)       -> false
  | Expr.SetT(_)       -> false
  | Expr.ElemT(_)      -> false
  | Expr.ThidT(_)      -> false
  | Expr.AddrT(_)      -> false
  | Expr.CellT(_)      -> false
  | Expr.SetThT(_)     -> false
  | Expr.SetIntT(_)    -> false
  | Expr.SetElemT(_)   -> false
  | Expr.PathT(_)      -> false
  | Expr.MemT(_)       -> false
  | Expr.IntT(_)       -> true
  | Expr.ArrayT(_)     -> false
  | Expr.AddrArrayT(_) -> false
  | Expr.TidArrayT(_)  -> false
and is_int_expression e = 
  match e with
    Expr.Term(t)      -> is_int_integer t
  | Expr.Formula(phi) -> is_int_formula phi


(* SUBTYPE CONVERTER: *)
(* integer_to_int_integer  : Expr.integer -> term *)
(* term_to_int_integer     : Expr.term -> term    *)
(* literal_to_int_literal  : Expr.literal -> literal    *)
(* formula_to_int_formula  : Expr.formula -> formula    *)

let variable_to_int_variable (v:Expr.variable) : variable =
  let (id,s,pr,th,p,_) = v
  in
    (id, sort_to_int_sort s, pr, th ,p)
    (* No evict problems with thid variables within th_p vars *)
(*
    if s = Some Expr.Thid then
      (id, None, pr, th, p)
    else
      (id, Option.lift sort_to_int_sort s, pr, th, p)
*)


let rec array_to_funterm (x:Expr.arrays) : fun_term =
  match x with
    Expr.VarArray v -> FunVar (variable_to_int_variable v)
  | Expr.ArrayUp (a,th,Expr.Term (Expr.IntT i)) ->
      FunUpd (array_to_funterm a, th, IntV (integer_to_int_integer i))
  | Expr.ArrayUp (a,th,Expr.Term (Expr.SetIntT i)) ->
      FunUpd (array_to_funterm a, th, SetV (set_to_int_set i))
  | _ -> RAISE(NotAnIntExpression(Expr.arrays_to_str x))


and funterm_to_array (x:fun_term) : Expr.arrays =
  let from_int  = int_integer_to_integer in
  let from_set  = int_set_to_set in
  match x with
    FunVar v             -> Expr.VarArray (int_variable_to_variable v)
  | FunUpd (f,th,IntV i) -> Expr.ArrayUp (funterm_to_array f, th,
                                          Expr.Term (Expr.IntT (from_int i)))
  | FunUpd (f,th,SetV s) -> Expr.ArrayUp (funterm_to_array f, th,
                                          Expr.Term (Expr.SetIntT (from_set s)))


and set_to_int_set (s:Expr.setint) : set =
  let toset = set_to_int_set in
  match s with
    Expr.VarSetInt v       -> VarSet (variable_to_int_variable v)
  | Expr.EmptySetInt       -> EmptySet
  | Expr.SinglInt i        -> Singl (integer_to_int_integer i)
  | Expr.UnionInt(s1,s2)   -> Union (toset s1, toset s2)
  | Expr.IntrInt(s1,s2)    -> Intr (toset s1, toset s2)
  | Expr.SetdiffInt(s1,s2) -> Diff (toset s1, toset s2)
  | _ -> RAISE(NotAnIntExpression(Expr.setint_to_str s))


and integer_to_int_integer t =
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
    match t with
      Expr.IntVal(i)       -> Val(i)
    | Expr.VarInt v        -> Var(variable_to_int_variable v)
    | Expr.IntNeg(i)       -> Neg(toint i)
    | Expr.IntAdd(x,y)     -> Add(toint x,toint y)
    | Expr.IntSub(x,y)     -> Sub(toint x,toint y)
    | Expr.IntMul(x,y)     -> Mul(toint x,toint y)
    | Expr.IntDiv(x,y)     -> Div(toint x,toint y)
    | Expr.IntArrayRd(a,i) -> ArrayRd(a,i)
    | Expr.IntSetMin(s)    -> SetMin (toset s)
    | Expr.IntSetMax(s)    -> SetMax (toset s)
    | Expr.CellMax(c)      -> RAISE(NotAnIntExpression(Expr.integer_to_str t))
    | Expr.HavocLevel      -> RAISE(NotAnIntExpression(Expr.integer_to_str t))

and term_to_int_integer t =
  match t with
      Expr.IntT(x) -> integer_to_int_integer x
    | _            -> RAISE(NotAnIntExpression(Expr.term_to_str t))

and atom_to_int_atom a =
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
    match a with
      Expr.Append _      -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.Reach _       -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.ReachAt _     -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.OrderList _   -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.Skiplist _    -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.In _          -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.SubsetEq _    -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.InTh _        -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.SubsetEqTh _  -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.InInt _       -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.SubsetEqInt _ -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.InElem _      -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.SubsetEqElem _-> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.Less(x,y)     -> Less(toint x,toint y)
    | Expr.Greater(x,y)  -> Greater(toint x,toint y)
    | Expr.LessEq(x,y)   -> LessEq(toint x,toint y)
    | Expr.GreaterEq(x,y)-> GreaterEq(toint x,toint y)
    | Expr.LessTid(x,y)  -> LessTid(x,y)
    | Expr.LessElem _    -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.GreaterElem _ -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.Eq(Expr.ThidT x,Expr.ThidT y)      -> TidEq(x, y)
    | Expr.InEq(Expr.ThidT x,Expr.ThidT y)    -> TidInEq(x, y)
    | Expr.Eq(Expr.ArrayT x, Expr.ArrayT y)   -> FunEq (array_to_funterm x,
                                                        array_to_funterm y)
    | Expr.InEq(Expr.ArrayT x, Expr.ArrayT y) -> FunInEq (array_to_funterm x,
                                                          array_to_funterm y)
    | Expr.Eq(Expr.IntT x, Expr.IntT y)       -> Eq(IntV (toint x),
                                                    IntV (toint y))
    | Expr.Eq(Expr.SetIntT x, Expr.SetIntT y) -> Eq(SetV (toset x),
                                                    SetV (toset y))
    | Expr.InEq(Expr.IntT x, Expr.IntT y)     -> InEq(IntV(toint x),
                                                      IntV(toint y))
    | Expr.InEq(Expr.SetIntT x, Expr.SetIntT y) -> InEq(SetV(toset x),
                                                      SetV(toset y))
    | Expr.Eq (_,_)   -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.InEq (_,_) -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.BoolVar _      -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.BoolArrayRd _  -> RAISE(NotAnIntExpression(Expr.atom_to_str a))
    | Expr.PC(i,th,pr)    -> PC (i,th,pr)
    | Expr.PCUpdate(i,th) -> PCUpdate (i,th)
    | Expr.PCRange(i,j,th,pr) -> PCRange (i,j,th,pr)

and literal_to_int_literal lit =
  match lit with
    Expr.Atom a    -> Atom (atom_to_int_atom a)
  | Expr.NegAtom a -> NegAtom (atom_to_int_atom a)

and formula_to_int_formula phi =
  let toint = formula_to_int_formula in
    match phi with
        Expr.Literal(l)   -> Literal(literal_to_int_literal l)
      | Expr.True         -> True
      | Expr.False        -> False
      | Expr.And(x,y)     -> And(toint x,toint y)
      | Expr.Or(x,y)      -> Or(toint x,toint y)
      | Expr.Not(x)       -> Not(toint x)
      | Expr.Implies(x,y) -> Implies(toint x,toint y)
      | Expr.Iff(x,y)     -> Iff(toint x,toint y)


(* SUPERTYPE CONVERTER: *)
(* int_integer_to_term        : term    -> Expr.term *)
(* int_literal_to_literal : literal -> Expr.literal *)
(* int_formula_to_formula : formula -> Expr.formula *)
(* int_expr_to_expr : expr_t -> Expr.expr_t *)


and int_variable_to_variable (v:variable) : Expr.variable =
  let (id,s,pr,th,p) = v
  in
    (id, int_sort_to_sort s, pr, th, p, Expr.Normal)


and int_formula_to_formula (phi:formula) : Expr.formula =
  let to_formula = int_formula_to_formula in
  match phi with
      Literal(l)     -> Expr.Literal(int_literal_to_literal l)
    | True           -> Expr.True
    | False          -> Expr.False
    | And(x,y)       -> Expr.And    (to_formula x, to_formula y)
    | Or(x,y)        -> Expr.Or     (to_formula x, to_formula y)
    | Not(x)         -> Expr.Not    (to_formula x)
    | Implies(x,y)   -> Expr.Implies(to_formula x, to_formula y)
    | Iff(x,y)       -> Expr.Iff    (to_formula x, to_formula y)

and int_literal_to_literal (l:literal) : Expr.literal =
  match l with
    Atom a    -> Expr.Atom (int_atom_to_atom a)
  | NegAtom a -> Expr.NegAtom (int_atom_to_atom a)

and int_atom_to_atom (a:atom) : Expr.atom =
  let from_int = int_integer_to_integer in
  let from_set = int_set_to_set in
  match a with
      Less(x,y)           -> Expr.Less        (from_int x,  from_int y)
    | Greater(x,y)        -> Expr.Greater     (from_int x, from_int y)
    | LessEq(x,y)         -> Expr.LessEq      (from_int x, from_int y)
    | GreaterEq(x,y)      -> Expr.GreaterEq   (from_int x, from_int y)
    | LessTid(x,y)        -> Expr.LessTid     (x, y)
    | Eq(IntV x,IntV y)   -> Expr.Eq          (Expr.IntT(from_int x),
                                               Expr.IntT(from_int y))
    | Eq(SetV x,SetV y)   -> Expr.Eq          (Expr.SetIntT(from_set x),
                                               Expr.SetIntT(from_set y))
    | InEq(IntV x,IntV y) -> Expr.InEq        (Expr.IntT(from_int x),
                                               Expr.IntT(from_int y))
    | InEq(SetV x,SetV y) -> Expr.InEq        (Expr.SetIntT(from_set x),
                                               Expr.SetIntT(from_set y))
    | In(i,s)             -> Expr.InInt       (from_int i, from_set s)
    | Subset(x,y)         -> Expr.SubsetEqInt (from_set x, from_set y)
    | TidEq(x,y)          -> Expr.Eq          (Expr.ThidT x, Expr.ThidT y)
    | TidInEq(x,y)        -> Expr.InEq        (Expr.ThidT x, Expr.ThidT y)
    | FunEq(x,y)          -> Expr.Eq          (Expr.ArrayT (funterm_to_array x),
                                               Expr.ArrayT (funterm_to_array y))
    | FunInEq(x,y)        -> Expr.InEq        (Expr.ArrayT (funterm_to_array x),
                                               Expr.ArrayT (funterm_to_array y))
    | Eq(_,_)             -> RAISE(MalformedExpression(int_atom_to_string a))
    | InEq(_,_)           -> RAISE(MalformedExpression(int_atom_to_string a))
    | PC(i,th,pr)         -> Expr.PC (i, th, pr)
    | PCUpdate(i,th)      -> Expr.PCUpdate (i, th)
    | PCRange(i,j,th,pr)  -> Expr.PCRange (i, j, th, pr)



and int_set_to_set (s:set) : Expr.setint =
  let from_set = int_set_to_set in
  match s with
    VarSet v     -> Expr.VarSetInt (int_variable_to_variable v)
  | EmptySet     -> Expr.EmptySetInt
  | Singl i      -> Expr.SinglInt (int_integer_to_integer i)
  | Union(s1,s2) -> Expr.UnionInt (from_set s1, from_set s2)
  | Intr(s1,s2)  -> Expr.IntrInt (from_set s1, from_set s2)
  | Diff(s1,s2)  -> Expr.SetdiffInt (from_set s1, from_set s2)
    

and int_integer_to_integer (t:integer) : Expr.integer =
  let from_int = int_integer_to_integer in
  let from_set = int_set_to_set in
  match t with
      Val(n)       -> Expr.IntVal(n)
    | Var v        -> Expr.VarInt (int_variable_to_variable v)
    | Neg(x)       -> Expr.IntNeg(from_int x)
    | Add(x,y)     -> Expr.IntAdd(from_int x,from_int y)
    | Sub(x,y)     -> Expr.IntSub(from_int x,from_int y)
    | Mul(x,y)     -> Expr.IntMul(from_int x,from_int y)
    | Div(x,y)     -> Expr.IntDiv(from_int x,from_int y)
    | ArrayRd(a,i) -> Expr.IntArrayRd(a,i)
    | SetMin(s)    -> Expr.IntSetMin(from_set s)
    | SetMax(s)    -> Expr.IntSetMax(from_set s)


and int_integer_to_term (t:integer) : Expr.term =
  Expr.IntT(int_integer_to_integer t)


(* CONJUNCTIONS OF LITERAL *)
let rec is_conjunctive (phi:formula) : bool =
  match phi with
      Literal(_) -> true
    | True       -> true
    | False      -> true
    | And(f,g)   -> (is_conjunctive f) && (is_conjunctive g)
    | _          -> false      


exception NotConjunctiveExpr of formula


let formula_to_conj_literals (phi:formula) : literal list =
  let rec try_to_build_conjunction x =
    match x with
     Literal l -> [l]
    | And(a,b)  -> (try_to_build_conjunction a) @ (try_to_build_conjunction b)
    | True      -> []
    |   _       -> Printf.printf "Error: %s\n"
                      (Expr.formula_to_str (int_formula_to_formula phi));
                   RAISE(NotConjunctiveExpr phi)
  in
    try_to_build_conjunction phi


let list_literals_to_formula (lits:literal list) : formula =
  match lits with
   [] -> True
  | l::ls -> let folder phi l = And(phi,Literal(l)) in
               (List.fold_left folder (Literal l) ls)
  

let conj_literals_to_formula (conj:conjunction_literals) : formula =
  match conj with
    ConjTrue   -> True
  | ConjFalse -> False
  | Conjuncts cs -> list_literals_to_formula cs


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
    | ArrayRd(a,i) -> false
    | SetMin(s)    -> false
    | SetMax(s)    -> false


(* formula_is_linear : formula -> bool *)
(* term_is_linear    : term    -> bool *)
(* literal_is_linear : literal -> bool *)
(* expr_is_linear    : expr    -> bool *)


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

and term_is_linear t =
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
    | ArrayRd(a,i)   -> true
    | SetMin(s)      -> true
    | SetMax(s)      -> true

and literal_is_linear l =
  match l with
    Atom a    -> (atom_is_linear a)
  | NegAtom a -> (atom_is_linear a)

and atom_is_linear a =
  let is_linear = term_is_linear in
  match a with
    Less(x,y)            -> (is_linear x) && (is_linear y)
  | Greater(x,y)         -> (is_linear x) && (is_linear y)
  | LessEq(x,y)          -> (is_linear x) && (is_linear y)
  | GreaterEq(x,y)       -> (is_linear x) && (is_linear y)
  | LessTid(x,y)         -> false
  | Eq(IntV x,IntV y)    -> (is_linear x) && (is_linear y)
  | InEq(IntV x, IntV y) -> (is_linear x) && (is_linear y)
  | Eq(_,_)              -> false
  | InEq(_,_)            -> false
  | In (_,_)             -> false
  | Subset (_,_)         -> false
  | TidEq(x,y)           -> false
  | TidInEq(x,y)         -> false
  | FunEq(x,y)           -> false
  | FunInEq(x,y)         -> false
  | PC _                 -> false
  | PCUpdate _           -> false
  | PCRange _            -> false



(* FOR SETVAR *)
let rec generic_set_from_int_integer (base:variable -> 'a)
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
  | ArrayRd (a,th) -> empty
  | SetMin s       -> generic_set_from_int_set base empty union s
  | SetMax s       -> generic_set_from_int_set base empty union s


and generic_set_from_funterm (base:variable -> 'a)
                             (empty:'a)
                             (union:'a -> 'a -> 'a)
                             (t:fun_term) : 'a =
  match t with
    FunVar (v)      -> base v
  | FunUpd (f,th,v) -> generic_set_from_funterm base empty union f


and generic_set_from_int_set (base:variable -> 'a)
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


let generic_set_from_int_term (base:variable -> 'a)
                              (empty:'a)
                              (union:'a -> 'a -> 'a)
                              (t:term) : 'a =
  match t with
    IntV i -> generic_set_from_int_integer base empty union i
  | SetV s -> generic_set_from_int_set base empty union s


let generic_set_from_int_atom (base:variable -> 'a)
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
  | TidEq (th1,th2)   -> empty
  | TidInEq (th1,th2) -> empty
  | FunEq (f1,f2)     -> union (fun_f f1) (fun_f f2)
  | FunInEq (f1,f2)   -> union (fun_f f1) (fun_f f2)
  | PC (pc,th,pr)     -> empty
  | PCUpdate (pc,th)  -> empty
  | PCRange (_,_,_,_) -> empty

let generic_set_from_int_literal (base:variable -> 'a)
                                 (empty:'a)
                                 (union:'a -> 'a -> 'a)
                                 (l:literal) : 'a =
  match l with
    Atom a    -> generic_set_from_int_atom base empty union a
  | NegAtom a -> generic_set_from_int_atom base empty union a
  

let rec generic_set_from_int_formula (base:variable -> 'a)
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


let conjlit_to_string (base:variable -> 'a)
                      (empty:'a)
                      (union:'a -> 'a -> 'a)
                      (cl:conjunction_literals) : 'a =
  match cl with
    ConjTrue     -> empty
  | ConjFalse    -> empty
  | Conjuncts ls -> List.fold_left (fun s l ->
                      union s (generic_set_from_int_literal base empty union l)
                    ) ls empty

(* Base functions for variables id *)

let base_setid_all_vars (v:variable) : Expr.VarIdSet.t =
  let (id,_,_,_,_) = v in
    Expr.VarIdSet.singleton id


let base_setid_local_vars (v:variable) : Expr.VarIdSet.t =
  let (id,_,_,_,p) = v in
    if p <> None then
      Expr.VarIdSet.singleton id
    else
      Expr.VarIdSet.empty


let base_setid_global_vars (v:variable) : Expr.VarIdSet.t =
  let (id,_,_,_,p) = v in
    if p = None then
      Expr.VarIdSet.singleton id
    else
      Expr.VarIdSet.empty



(* Functions for all variables *)

let vset_from_int_integer (t:integer) : Expr.VarIdSet.t =
  generic_set_from_int_integer base_setid_all_vars Expr.VarIdSet.empty
                        Expr.VarIdSet.union t


let vset_from_funterm (t:fun_term) : Expr.VarIdSet.t =
  generic_set_from_funterm base_setid_all_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union t


let vset_from_int_formula (f:formula) : Expr.VarIdSet.t =
  generic_set_from_int_formula base_setid_all_vars Expr.VarIdSet.empty
                               Expr.VarIdSet.union f


let vset_from_int_literal (l:literal) : Expr.VarIdSet.t =
  generic_set_from_int_literal base_setid_all_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union l



(* Functions for global variables *)

let global_vset_from_int_integer (t:integer) : Expr.VarIdSet.t =
  generic_set_from_int_integer base_setid_global_vars Expr.VarIdSet.empty
                        Expr.VarIdSet.union t


let global_vset_from_funterm (t:fun_term) : Expr.VarIdSet.t =
  generic_set_from_funterm base_setid_global_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union t


let global_vset_from_int_literal (l:literal) : Expr.VarIdSet.t =
  generic_set_from_int_literal base_setid_global_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union l


let global_vset_from_int_formula (f:formula) : Expr.VarIdSet.t =
  generic_set_from_int_formula base_setid_global_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union f



(* Functions for local variables *)

let local_vset_from_int_integer (t:integer) : Expr.VarIdSet.t =
  generic_set_from_int_integer base_setid_local_vars Expr.VarIdSet.empty
                        Expr.VarIdSet.union t


let local_vset_from_funterm (t:fun_term) : Expr.VarIdSet.t =
  generic_set_from_funterm base_setid_local_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union t


let local_vset_from_int_literal (l:literal) : Expr.VarIdSet.t =
  generic_set_from_int_literal base_setid_local_vars Expr.VarIdSet.empty
                           Expr.VarIdSet.union l


let local_vset_from_int_formula (f:formula) : Expr.VarIdSet.t =
  generic_set_from_int_formula base_setid_local_vars Expr.VarIdSet.empty
                               Expr.VarIdSet.union f



let all_varid_set         = vset_from_int_formula
let all_varid_set_literal = vset_from_int_literal
let all_global_varid_set  = global_vset_from_int_formula
let all_local_varid_set   = local_vset_from_int_formula

let all_varid phi         = Expr.VarIdSet.elements (all_varid_set phi)
let all_varid_literal l   = Expr.VarIdSet.elements (all_varid_set_literal l)
let all_local_varid phi   = Expr.VarIdSet.elements (all_local_varid_set phi)
let all_global_varid phi  = Expr.VarIdSet.elements (all_global_varid_set phi)



(* Base functions for full variables *)

let base_set_all_vars (v:variable) : VarSet.t =
  VarSet.singleton v


let base_set_local_vars (v:variable) : VarSet.t =
  let (id,s,pr,th,p) = v in
    if p <> None && p <> Some "" then
      VarSet.singleton v
    else
      VarSet.empty


let base_set_global_vars (v:variable) : VarSet.t =
  let (id,s,pr,th,p) = v in
    if p = None || p = Some "" then
      VarSet.singleton v
    else
      VarSet.empty



(* Functions for all variables *)

let var_set_from_int_integer (t:integer) : VarSet.t =
  generic_set_from_int_integer base_set_all_vars VarSet.empty
                        VarSet.union t


let var_set_from_funterm (t:fun_term) : VarSet.t =
  generic_set_from_funterm base_set_all_vars VarSet.empty
                           VarSet.union t


let var_set_from_int_formula (f:formula) : VarSet.t =
  generic_set_from_int_formula base_set_all_vars VarSet.empty
                               VarSet.union f


let var_set_from_int_formula (f:formula) : VarSet.t =
  generic_set_from_int_formula base_set_all_vars VarSet.empty
                               VarSet.union f


let var_set_from_int_literal (l:literal) : VarSet.t =
  generic_set_from_int_literal base_set_all_vars VarSet.empty
                               VarSet.union l



(* Functions for global variables *)

let var_global_set_from_int_integer (t:integer) : VarSet.t =
  generic_set_from_int_integer base_set_global_vars VarSet.empty
                        VarSet.union t


let var_global_set_from_funterm (t:fun_term) : VarSet.t =
  generic_set_from_funterm base_set_global_vars VarSet.empty
                           VarSet.union t


let var_global_set_from_int_formula (f:formula) : VarSet.t =
  generic_set_from_int_formula base_set_global_vars VarSet.empty
                               VarSet.union f


let var_global_set_from_int_literal (l:literal) : VarSet.t =
  generic_set_from_int_literal base_set_global_vars VarSet.empty
                               VarSet.union l



(* Functions for local variables *)

let var_local_set_from_int_integer (t:integer) : VarSet.t =
  generic_set_from_int_integer base_set_local_vars VarSet.empty
                        VarSet.union t


let var_local_set_from_funterm (t:fun_term) : VarSet.t =
  generic_set_from_funterm base_set_local_vars VarSet.empty
                           VarSet.union t


let var_local_set_from_int_formula (f:formula) : VarSet.t =
  generic_set_from_int_formula base_set_local_vars VarSet.empty
                               VarSet.union f


let var_local_set_from_int_literal (l:literal) : VarSet.t =
  generic_set_from_int_literal base_set_local_vars VarSet.empty
                               VarSet.union l



let all_vars_set         = var_set_from_int_formula
let all_vars_set_literal = var_set_from_int_literal
let all_global_vars_set  = var_global_set_from_int_formula
let all_local_vars_set   = var_local_set_from_int_formula


let all_vars phi        = VarSet.elements (all_vars_set phi)
let all_vars_literal l  = VarSet.elements (all_vars_set_literal l)
let all_global_vars phi = VarSet.elements (all_global_vars_set phi)
let all_local_vars phi  = VarSet.elements (all_local_vars_set phi)


let filter_var_set (v_set:VarSet.t) : variable list =
  let filtered_set = VarSet.fold (fun v s ->
                       VarSet.add (var_clear_param_info v) s
                     ) v_set VarSet.empty
  in
    VarSet.elements filtered_set


let all_global_vars_without_param (phi:formula) : variable list =
  filter_var_set (all_global_vars_set phi)


let all_local_vars_without_param (phi:formula) : variable list =
  filter_var_set (all_local_vars_set phi)



(* Primed vars *)

let base_primed_vars (v:variable) : Expr.VarIdSet.t =
  let (id,_,pr,_,_) = v in
    if pr then
      Expr.VarIdSet.singleton id
    else
      Expr.VarIdSet.empty


let vset_primed_from_int_formula (phi:formula) : Expr.VarIdSet.t =
  generic_set_from_int_formula base_primed_vars Expr.VarIdSet.empty
                               Expr.VarIdSet.union phi



(* List of vars *)
let base_list_vars (v:variable) : Expr.VarIdSet.t =
  let (id,_,_,_,_) = v
  in
    Expr.VarIdSet.singleton id


let vlist_from_int_formula (phi:formula) : Expr.VarIdSet.t =
  generic_set_from_int_formula base_list_vars Expr.VarIdSet.empty
                               Expr.VarIdSet.union  phi


(* Vocabulary functions *)
let opt_th (th:Expr.tid option) : Expr.ThreadSet.t =
  Option.map_default Expr.ThreadSet.singleton Expr.ThreadSet.empty th


let thset_from (ths:Expr.tid list) : Expr.ThreadSet.t =
  List.fold_left (fun s t -> Expr.ThreadSet.add t s) Expr.ThreadSet.empty ths


let rec voc_from_int_integer (t:integer) : Expr.ThreadSet.t =
  match t with
    Val i                  -> Expr.ThreadSet.empty
  | Var v                  -> opt_th (get_th v)
  | Neg t                  -> voc_from_int_integer t
  | Add (t1,t2)            -> Expr.ThreadSet.union (voc_from_int_integer t1)
                                                   (voc_from_int_integer t2)
  | Sub (t1,t2)            -> Expr.ThreadSet.union (voc_from_int_integer t1)
                                                   (voc_from_int_integer t2)
  | Mul (t1,t2)            -> Expr.ThreadSet.union (voc_from_int_integer t1)
                                                   (voc_from_int_integer t2)
  | Div (t1,t2)            -> Expr.ThreadSet.union (voc_from_int_integer t1)
                                                   (voc_from_int_integer t2)
  | ArrayRd (a,th)         -> Expr.ThreadSet.empty
  | SetMin s               -> Expr.ThreadSet.empty
  | SetMax s               -> Expr.ThreadSet.empty


let voc_from_funterm (t:fun_term) : Expr.ThreadSet.t =
  match t with
    FunVar v        -> opt_th (get_th v)
  | FunUpd (f,th,v) -> Expr.ThreadSet.singleton th


let rec voc_from_int_set (s:set) : Expr.ThreadSet.t =
  match s with
    VarSet v      -> opt_th (get_th v)
  | EmptySet      -> Expr.ThreadSet.empty
  | Singl i       -> voc_from_int_integer i
  | Union (s1,s2) -> Expr.ThreadSet.union (voc_from_int_set s1)
                                          (voc_from_int_set s2)
  | Intr (s1,s2)  -> Expr.ThreadSet.union (voc_from_int_set s1)
                                          (voc_from_int_set s2)
  | Diff (s1,s2)  -> Expr.ThreadSet.union (voc_from_int_set s1)
                                          (voc_from_int_set s2)


let voc_from_int_term (t:term) : Expr.ThreadSet.t =
  match t with
    IntV i -> voc_from_int_integer i
  | SetV s -> voc_from_int_set s


let voc_from_int_atom (a:atom) : Expr.ThreadSet.t =
  let union = Expr.ThreadSet.union in
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
  | TidEq (th1,th2)   -> thset_from [th1;th2]
  | TidInEq (th1,th2) -> thset_from [th1;th2]
  | FunEq (f1,f2)     -> Expr.ThreadSet.empty
  | FunInEq (f1,f2)   -> Expr.ThreadSet.empty
  | PC (pc,th,pr)     -> opt_th th
  | PCUpdate (pc,th)  -> Expr.ThreadSet.singleton th
  | PCRange (_,_,th,_)-> opt_th th


let voc_from_int_literal (l:literal) : Expr.ThreadSet.t =
  match l with
    Atom a    -> voc_from_int_atom a
  | NegAtom a -> voc_from_int_atom a


let rec voc_from_int_formula (f:formula) : Expr.ThreadSet.t =
  let union = Expr.ThreadSet.union in
  let empty = Expr.ThreadSet.empty in
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



let voc_from_conjlit (cl:conjunction_literals) : Expr.ThreadSet.t =
  match cl with
    ConjTrue     -> Expr.ThreadSet.empty
  | ConjFalse    -> Expr.ThreadSet.empty
  | Conjuncts ls -> List.fold_left (fun s l ->
                      Expr.ThreadSet.union s (voc_from_int_literal l)
                    ) Expr.ThreadSet.empty ls



let voc (phi:formula) : Expr.tid list =
  Expr.ThreadSet.elements (voc_from_int_formula phi)

