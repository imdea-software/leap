open LeapLib

module E = Expression
module F = Formula

type sort = Int | Set | Tid | Pair | SetPair

type var_info_t =
  {
    treat_as_pc : bool;
  }

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = var_info_t
  end )

type tid =
    VarTh         of V.t
  | NoTid
  | PairTid       of pair
and integer =
    Val           of int
  | Var           of V.t
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | ArrayRd       of E.arrays * tid
  | SetMin        of set
  | SetMax        of set
  | PairInt       of pair
and pair =
    VarPair       of V.t
  | IntTidPair    of integer * tid
  | SetPairMin    of setpair
  | SetPairMax    of setpair
and set =
    VarSet        of V.t
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
  | Lower         of set * integer
and setpair =
    VarSetPair    of V.t
  | EmptySetPair
  | SinglPair  of pair
  | UnionPair  of setpair * setpair
  | IntrPair   of setpair * setpair
  | SetdiffPair   of setpair * setpair
  | LowerPair  of setpair * integer
and term =
    IntV          of integer
  | PairV         of pair
  | SetV          of set
  | SetPairV      of setpair
and fun_term =
    FunVar        of V.t
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
  | InTidPair     of tid * setpair
  | InIntPair     of integer * setpair
  | InPair        of pair * setpair
  | SubsetEqPair of setpair * setpair
  | Eq            of eq
  | InEq          of diseq
  | TidEq         of tid * tid
  | TidInEq       of tid * tid
  | FunEq         of fun_term * fun_term
  | FunInEq       of fun_term * fun_term
  | UniqueInt     of setpair
  | UniqueTid     of setpair
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula


exception NotConjunctiveExpr of formula
exception Not_tid_var of tid


module AtomSet = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = atom
  end
)

module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )


(* Variable constructor *)
let build_var ?(fresh=false)
              ?(treat_as_pc=false)
              (id:V.id)
              (s:sort)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
  V.build id s pr th p {treat_as_pc = treat_as_pc; } ~fresh:fresh


let treat_as_pc (v:V.t) : bool =
  (V.info v).treat_as_pc


(* CONVERTERS TO STRING *)
(* EXPR TO STR *)
let sort_to_str (s:sort) : string =
  match s with
    Int      -> "int"
  | Pair     -> "pair"
  | Set      -> "set"
  | SetPair  -> "setpair"
  | Tid      -> "tid"

let rec generic_pair_tid_to_str (srf:string -> string) (t:tid) : string =
  match t with
  | VarTh t -> V.to_str t
  | NoTid -> "#"
  | PairTid p -> "tid_of(" ^(generic_pair_pair_to_str srf p)^ ")"

and generic_pair_integer_to_str (srf:string -> string) (t:integer) : string =
  let tid_str_f = generic_pair_tid_to_str srf in
  let int_str_f = generic_pair_integer_to_str srf in
  let set_str_f = generic_pair_set_to_str srf in
  let pair_str_f = generic_pair_pair_to_str srf in
  match t with
    Val i          -> string_of_int i
  | Var v          -> V.to_str v
  | Neg t          -> srf ("-" ^ int_str_f t)
  | Add (t1,t2)    -> srf (int_str_f t1 ^ " + " ^ int_str_f t2)
  | Sub (t1,t2)    -> srf (int_str_f t1 ^ " - " ^ int_str_f t2)
  | Mul (t1,t2)    -> srf (int_str_f t1 ^ " * " ^ int_str_f t2)
  | Div (t1,t2)    -> srf (int_str_f t1 ^ " / " ^ int_str_f t2)
  | ArrayRd (a,th) -> srf (E.arrays_to_str a ^ "[" ^
                           tid_str_f th ^ "]")
  | SetMin s       -> srf ("setIntMin(" ^ set_str_f s ^ ")")
  | SetMax s       -> srf ("setIntMax(" ^ set_str_f s ^ ")")
  | PairInt p      -> srf ("int_of(" ^ pair_str_f p ^ ")")


and generic_pair_pair_to_str (srf:string -> string) (p:pair): string =
  let int_str_f = generic_pair_integer_to_str srf in
  let tid_str_f = generic_pair_tid_to_str srf in
  let setpair_str_f = generic_pair_setpair_to_str srf in
  match p with
    VarPair v        -> V.to_str v
  | IntTidPair (i,t) -> "(" ^ int_str_f i ^ "," ^ tid_str_f t ^ ")"
  | SetPairMin ps -> "psmin(" ^ setpair_str_f ps ^ ")"
  | SetPairMax ps -> "psmax(" ^ setpair_str_f ps ^ ")"


and generic_pair_set_to_str (srf:string -> string) (s:set): string =
  let pair_str_f = generic_pair_integer_to_str srf in
  let set_str_f = generic_pair_set_to_str srf in
  match s with
    VarSet v      -> V.to_str v
  | EmptySet      -> srf "emptyset"
  | Singl i       -> srf ("{" ^ pair_str_f i ^ "}")
  | Union (s1,s2) -> srf (set_str_f s1 ^ " union " ^ set_str_f s2)
  | Intr (s1,s2)  -> srf (set_str_f s1 ^ " intr "  ^ set_str_f s2)
  | Diff (s1,s2)  -> srf (set_str_f s1 ^ " diff "  ^ set_str_f s2)
  | Lower (s,i)   -> srf ("lower (" ^ set_str_f s ^ "," ^ pair_str_f i ^ ")")


and generic_pair_setpair_to_str (srf:string -> string) (ps:setpair): string =
  let int_str_f = generic_pair_integer_to_str srf in
  let pair_str_f = generic_pair_pair_to_str srf in
  let setpair_str_f = generic_pair_setpair_to_str srf in
  match ps with
    VarSetPair v         -> V.to_str v
  | EmptySetPair         -> srf "spempty"
  | SinglPair i       -> srf ("spsingle(" ^ pair_str_f i ^ ")")
  | UnionPair (s1,s2) -> srf ("spunion(" ^ setpair_str_f s1 ^ "," ^ setpair_str_f s2 ^ ")")
  | IntrPair (s1,s2)  -> srf ("spintr(" ^ setpair_str_f s1 ^ ","  ^ setpair_str_f s2 ^ ")")
  | SetdiffPair (s1,s2)  -> srf ("spdiff(" ^ setpair_str_f s1 ^ ","  ^ setpair_str_f s2 ^ ")")
  | LowerPair (s,i)   -> srf ("splower (" ^ setpair_str_f s ^ "," ^ int_str_f i ^ ")")


let generic_pair_term_to_str (srf:string -> string) (t:term) : string =
  match t with
    IntV i -> generic_pair_integer_to_str srf i
  | PairV p -> generic_pair_pair_to_str srf p
  | SetV s -> generic_pair_set_to_str srf s
  | SetPairV s -> generic_pair_setpair_to_str srf s


let rec generic_funterm_to_str (srf:string -> string) (t:fun_term) : string =
  match t with
    FunVar v        -> V.to_str v
  | FunUpd (f,th,v) -> srf (Printf.sprintf "%s{%s<-%s}"
                            (generic_funterm_to_str srf f)
                            (generic_pair_tid_to_str srf th)
                            (generic_pair_term_to_str srf v))


let rec generic_atom_to_str (srf:string -> string) (a:atom) : string =
  let tid_str_f  = generic_pair_tid_to_str srf in
  let int_str_f  = generic_pair_integer_to_str srf in
  let pair_str_f  = generic_pair_pair_to_str srf in
  let set_str_f  = generic_pair_set_to_str srf in
  let setpair_str_f  = generic_pair_setpair_to_str srf in
  let term_str_f = generic_pair_term_to_str srf in
  let fun_str_f  = generic_funterm_to_str srf in
  match a with
    Less (t1,t2)            -> srf (int_str_f t1  ^ " < "  ^ int_str_f t2)
  | Greater (t1,t2)         -> srf (int_str_f t1  ^ " > "  ^ int_str_f t2)
  | LessEq (t1,t2)          -> srf (int_str_f t1  ^ " <= " ^ int_str_f t2)
  | GreaterEq (t1,t2)       -> srf (int_str_f t1  ^ " >= " ^ int_str_f t2)
  | LessTid (th1,th2)       -> srf (tid_str_f th1 ^ " < " ^ tid_str_f th2)
  | Eq (t1,t2)              -> srf (term_str_f t1 ^ " = "  ^ term_str_f t2)
  | InEq (t1,t2)            -> srf (term_str_f t1 ^ " != " ^ term_str_f t2)
  | In (i,s)                -> srf (int_str_f i   ^ " in " ^ set_str_f s)
  | Subset (s1,s2)          -> srf (set_str_f s1  ^ " subset " ^ set_str_f s2)
  | InTidPair (t,ps)        -> srf ("pstidin(" ^ tid_str_f t ^ "," ^ setpair_str_f ps ^ ")")
  | InIntPair (i,ps)        -> srf ("psintin(" ^ int_str_f i ^ "," ^ setpair_str_f ps ^ ")")
  | InPair (p,ps)           -> srf ("psin(" ^ pair_str_f p ^ "," ^ setpair_str_f ps ^ ")")
  | SubsetEqPair (ps1,ps2)  -> srf ("pssubset(" ^ setpair_str_f ps1  ^ "," ^ setpair_str_f ps2 ^ ")")
  | TidEq (th1,th2)         -> srf (tid_str_f th1   ^ " = "  ^
                                    tid_str_f th2)
  | TidInEq (th1,th2)       -> srf (tid_str_f th1   ^ " != " ^
                                    tid_str_f th2)
  | FunEq (f1,f2)           -> srf (fun_str_f f1  ^ " = "  ^ fun_str_f f2)
  | FunInEq (f1,f2)         -> srf (fun_str_f f1  ^ " != " ^ fun_str_f f2)
  | UniqueInt (ps)          -> srf ("uniqueint(" ^ setpair_str_f ps ^ ")")
  | UniqueTid (ps)          -> srf ("uniquetid(" ^ setpair_str_f ps ^ ")")
  | PC (pc,th,pr)           -> let i_str = if pr then "pc'" else "pc" in
                               let th_str = V.shared_or_local_to_str th in
                                 Printf.sprintf "%s(%s) = %i" i_str th_str pc
  | PCUpdate (pc,th)        -> let th_str = tid_str_f th in
                                 Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,th,pr) -> let i_str = if pr then "pc'" else "pc" in
                               let th_str = V.shared_or_local_to_str th in
                                 Printf.sprintf "%i <= %s(%s) <= %i" pc1 i_str th_str pc2



and no_parenthesis (str:string) : string = str
and add_parenthesis (str:string) : string = "(" ^ str ^ ")"

(* No parenthesis printing functions *)
and integer_to_str (t:integer) : string =
  generic_pair_integer_to_str no_parenthesis t

and funterm_to_str (t:fun_term) : string =
  generic_funterm_to_str no_parenthesis t

and atom_to_str (a:atom) : string =
  generic_atom_to_str no_parenthesis a

and literal_to_str (l:literal) : string =
  Formula.literal_to_str (generic_atom_to_str no_parenthesis) l

and formula_to_str (phi:formula) : string =
  Formula.formula_to_str (generic_atom_to_str no_parenthesis) phi
(*  generic_pair_formula_to_str no_parenthesis f*)



(* Parenthesis printing functions *)
let integer_to_par_string (t:integer) : string =
  generic_pair_integer_to_str add_parenthesis t

let funterm_to_par_string (t:fun_term) : string =
  generic_funterm_to_str add_parenthesis t

let literal_to_par_string (l:literal) : string =
  Formula.literal_to_str (generic_atom_to_str no_parenthesis) l

let conjunctive_formula_to_str (cf:conjunctive_formula) : string =
  Formula.conjunctive_formula_to_str (generic_atom_to_str no_parenthesis) cf

let formula_to_par_string (phi:formula) : string =
  Formula.formula_to_str (generic_atom_to_str no_parenthesis) phi
(*  generic_pair_formula_to_str add_parenthesis f*)




(* CHECKERS *)
let rec is_pair_atom ato =
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
  | E.InPair(_,_)                      -> true
  | E.SubsetEqPair(_,_)                -> true
  | E.InTidPair(_,_)                   -> true
  | E.InIntPair(_,_)                   -> true
  | E.Less(_,_)                        -> true
  | E.Greater(_,_)                     -> true
  | E.LessEq(_,_)                      -> true
  | E.GreaterEq(_,_)                   -> true
  | E.LessTid(_,_)                     -> true
  | E.LessElem(_,_)                    -> true
  | E.GreaterElem(_,_)                 -> true
  | E.Eq(E.TidT _, E.TidT _)           -> true
  | E.InEq(E.TidT _, E.TidT _)         -> true
  | E.Eq(x,y)                          -> (is_pair_integer x) && (is_pair_integer y)
  | E.InEq(x,y)                        -> (is_pair_integer x) && (is_pair_integer y)
  | E.BoolVar _                        -> false
  | E.BoolArrayRd (_,_)                -> false
  | E.UniqueInt(_)                     -> true
  | E.UniqueTid(_)                     -> true
  | E.PC(_)                            -> true
  | E.PCUpdate(_)                      -> true
  | E.PCRange(_)                       -> true
and is_pair_integer t =
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
  | E.SetPairT(_)   -> false
  | E.PathT(_)      -> false
  | E.MemT(_)       -> false
  | E.IntT(_)       -> true
  | E.PairT(_)      -> true
  | E.ArrayT(_)     -> false
  | E.AddrArrayT(_) -> false
  | E.TidArrayT(_)  -> false
and is_pair_expression e = 
  match e with
    E.Term(t)      -> is_pair_integer t
  | E.Formula(phi) -> is_pair_formula phi

and is_pair_fs () = Formula.make_fold
                     Formula.GenericLiteralFold
                     (fun info a -> is_pair_atom a)
                     (fun info -> true)
                     (&&)

and is_pair_formula (phi:E.formula) : bool =
  Formula.formula_fold (is_pair_fs()) () phi


(* CONJUNCTIONS OF LITERAL *)

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
    | PairInt(ps)  -> false


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
    | ArrayRd(a,i)   -> true
    | SetMin(s)      -> true
    | SetMax(s)      -> true
    | PairInt(ps)    -> true

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
  | InTidPair _          -> false
  | InIntPair _          -> false
  | InPair (_,_)         -> false
  | SubsetEqPair (_,_)   -> false
  | TidEq(x,y)           -> false
  | TidInEq(x,y)         -> false
  | FunEq(x,y)           -> false
  | FunInEq(x,y)         -> false
  | UniqueInt _          -> false
  | UniqueTid _          -> false
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
let rec generic_set_from_pair_integer (base:V.t -> 'a)
                                      (empty:'a)
                                      (union:'a -> 'a -> 'a)
                                      (t:integer) : 'a =
  match t with
    Val i          -> empty
  | Var v          -> base v
  | Neg t          -> generic_set_from_pair_integer base empty union t
  | Add (t1,t2)    -> union (generic_set_from_pair_integer
                                base empty union t1)
                            (generic_set_from_pair_integer
                                base empty union t2)
  | Sub (t1,t2)    -> union (generic_set_from_pair_integer
                                base empty union t1)
                            (generic_set_from_pair_integer
                                base empty union t2)
  | Mul (t1,t2)    -> union (generic_set_from_pair_integer
                                base empty union t1)
                            (generic_set_from_pair_integer
                                base empty union t2)
  | Div (t1,t2)    -> union (generic_set_from_pair_integer
                                base empty union t1)
                            (generic_set_from_pair_integer
                                base empty union t2)
  | ArrayRd (a,th) -> empty
  | SetMin s       -> generic_set_from_pair_set base empty union s
  | SetMax s       -> generic_set_from_pair_set base empty union s
  | PairInt p      -> generic_set_from_pair_pair base empty union p


and generic_set_from_pair_pair (base:V.t -> 'a)
                               (empty:'a)
                               (union:'a -> 'a -> 'a)
                               (p:pair) : 'a =
  match p with
    VarPair v        -> base v
  | IntTidPair (i,t) -> generic_set_from_pair_integer base empty union i
  | SetPairMin ps    -> generic_set_from_pair_setpair base empty union ps
  | SetPairMax ps    -> generic_set_from_pair_setpair base empty union ps


and generic_set_from_funterm (base:V.t -> 'a)
                             (empty:'a)
                             (union:'a -> 'a -> 'a)
                             (t:fun_term) : 'a =
  match t with
    FunVar (v)      -> base v
  | FunUpd (f,th,v) -> generic_set_from_funterm base empty union f


and generic_set_from_pair_set (base:V.t -> 'a)
                              (empty:'a)
                              (union:'a -> 'a -> 'a)
                              (s:set) : 'a =
  let int_f  = generic_set_from_pair_integer base empty union in
  let set_f  = generic_set_from_pair_set base empty union in
  match s with
    VarSet (v)    -> base v
  | EmptySet      -> empty
  | Singl i       -> int_f i
  | Union (s1,s2) -> union (set_f s1) (set_f s2)
  | Intr (s1,s2)  -> union (set_f s1) (set_f s2)
  | Diff (s1,s2)  -> union (set_f s1) (set_f s2)
  | Lower (s,i)   -> union (set_f  s) (int_f  i)


and generic_set_from_pair_setpair (base:V.t -> 'a)
                                  (empty:'a)
                                  (union:'a -> 'a -> 'a)
                                  (ps:setpair) : 'a =
  let int_f  = generic_set_from_pair_integer base empty union in
  let pair_f  = generic_set_from_pair_pair base empty union in
  let setpair_f  = generic_set_from_pair_setpair base empty union in
  match ps with
    VarSetPair (v)         -> base v
  | EmptySetPair           -> empty
  | SinglPair p         -> pair_f p
  | UnionPair (ps1,ps2) -> union (setpair_f ps1) (setpair_f ps2)
  | IntrPair (ps1,ps2)  -> union (setpair_f ps1) (setpair_f ps2)
  | SetdiffPair (ps1,ps2)  -> union (setpair_f ps1) (setpair_f ps2)
  | LowerPair (ps,i)    -> union (setpair_f ps)   (int_f  i)


and generic_set_from_pair_term (base:V.t -> 'a)
                               (empty:'a)
                               (union:'a -> 'a -> 'a)
                               (t:term) : 'a =
  match t with
    IntV i      -> generic_set_from_pair_integer base empty union i
  | PairV p     -> generic_set_from_pair_pair base empty union p
  | SetV s      -> generic_set_from_pair_set base empty union s
  | SetPairV ps -> generic_set_from_pair_setpair base empty union ps


let generic_set_from_pair_atom (base:V.t -> 'a)
                               (empty:'a)
                               (union:'a -> 'a -> 'a)
                               (a:atom) : 'a =
  let int_f  = generic_set_from_pair_integer base empty union in
  let pair_f  = generic_set_from_pair_pair base empty union in
  let set_f  = generic_set_from_pair_set base empty union in
  let setpair_f  = generic_set_from_pair_setpair base empty union in
  let term_f = generic_set_from_pair_term base empty union in
  let fun_f  = generic_set_from_funterm base empty union in
  match a with
    Less (t1,t2)             -> union (int_f t1) (int_f t2)
  | Greater (t1,t2)          -> union (int_f t1) (int_f t2)
  | LessEq (t1,t2)           -> union (int_f t1) (int_f t2)
  | GreaterEq (t1,t2)        -> union (int_f t1) (int_f t2)
  | LessTid (th1,th2)        -> empty
  | Eq (t1,t2)               -> union (term_f t1) (term_f t2)
  | InEq (t1,t2)             -> union (term_f t1) (term_f t2)
  | In (i,s)                 -> union (int_f i) (set_f s)
  | Subset (s1,s2)           -> union (set_f s1) (set_f s2)
  | InTidPair (t,ps)         -> (setpair_f ps)
  | InIntPair (i,ps)         -> union (int_f i) (setpair_f ps)
  | InPair (p,ps)         -> union (pair_f p) (setpair_f ps)
  | SubsetEqPair (ps1,ps2)  -> union (setpair_f ps1) (setpair_f ps2)
  | TidEq (th1,th2)          -> empty
  | TidInEq (th1,th2)        -> empty
  | FunEq (f1,f2)            -> union (fun_f f1) (fun_f f2)
  | FunInEq (f1,f2)          -> union (fun_f f1) (fun_f f2)
  | UniqueInt ps             -> (setpair_f ps)
  | UniqueTid ps             -> (setpair_f ps)
  | PC (pc,th,pr)            -> empty
  | PCUpdate (pc,th)         -> empty
  | PCRange (_,_,_,_)        -> empty


let varset_fs = Formula.make_fold
                  Formula.GenericLiteralFold
                  (fun info a -> generic_set_from_pair_atom info V.VarSet.empty V.VarSet.union a)
                  (fun info -> V.VarSet.empty)
                  V.VarSet.union


let varset_from_pair_formula (base:V.t -> 'a)
                            (phi:formula) : 'a =
  Formula.formula_fold varset_fs base phi


let varidset_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (fun info a -> generic_set_from_pair_atom info V.VarIdSet.empty V.VarIdSet.union a)
                    (fun info -> V.VarIdSet.empty)
                    V.VarIdSet.union


let varidset_from_pair_formula (base:V.t -> 'a)
                              (phi:formula) : 'a =
  Formula.formula_fold varidset_fs base phi
                                 


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

let vset_from_pair_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_pair_formula base_setid_all_vars phi


(* Functions for global variables *)

let global_vset_from_pair_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_pair_formula base_setid_global_vars phi


(* Functions for local variables *)

let local_vset_from_pair_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_pair_formula base_setid_local_vars phi



let all_varid_set         = vset_from_pair_formula
(*let all_varid_set_literal = vset_from_pair_literal *)
let all_global_varid_set  = global_vset_from_pair_formula
let all_local_varid_set   = local_vset_from_pair_formula

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

let var_set_from_pair_formula (phi:formula) : V.VarSet.t =
  varset_from_pair_formula base_set_all_vars phi



(* Functions for global variables *)

let var_global_set_from_pair_formula (phi:formula) : V.VarSet.t =
  varset_from_pair_formula base_set_global_vars phi


(* Functions for local variables *)

let var_local_set_from_pair_formula (phi:formula) : V.VarSet.t =
  varset_from_pair_formula base_set_local_vars phi



let all_vars_set         = var_set_from_pair_formula
(*let all_vars_set_literal = var_set_from_pair_literal*)
let all_global_vars_set  = var_global_set_from_pair_formula
let all_local_vars_set   = var_local_set_from_pair_formula


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


let vset_primed_from_pair_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_pair_formula base_primed_vars phi



(* List of vars *)
let base_list_vars (v:V.t) : V.VarIdSet.t =
  V.VarIdSet.singleton (V.id v)


let vlist_from_pair_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_pair_formula base_list_vars phi


(* Vocabulary functions *)
let opt_th (th:V.shared_or_local) : ThreadSet.t =
  match th with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


let thset_from (ths:tid list) : ThreadSet.t =
  List.fold_left (fun s t -> ThreadSet.add t s) ThreadSet.empty ths


let rec voc_from_pair_tid (t:tid) : ThreadSet.t =
  match t with
  | VarTh v -> ThreadSet.singleton t
  | NoTid -> ThreadSet.singleton t
  | PairTid p -> voc_from_pair_pair p


and voc_from_pair_integer (t:integer) : ThreadSet.t =
  match t with
    Val i                  -> ThreadSet.empty
  | Var v                  -> opt_th (V.parameter v)
  | Neg t                  -> voc_from_pair_integer t
  | Add (t1,t2)            -> ThreadSet.union (voc_from_pair_integer t1)
                                              (voc_from_pair_integer t2)
  | Sub (t1,t2)            -> ThreadSet.union (voc_from_pair_integer t1)
                                              (voc_from_pair_integer t2)
  | Mul (t1,t2)            -> ThreadSet.union (voc_from_pair_integer t1)
                                              (voc_from_pair_integer t2)
  | Div (t1,t2)            -> ThreadSet.union (voc_from_pair_integer t1)
                                              (voc_from_pair_integer t2)
  | ArrayRd (a,th)         -> ThreadSet.empty
  | SetMin s               -> ThreadSet.empty
  | SetMax s               -> ThreadSet.empty
  | PairInt p              -> voc_from_pair_pair p


and voc_from_pair_pair (p:pair) : ThreadSet.t =
  match p with
    VarPair v        -> opt_th (V.parameter v)
  | IntTidPair (i,t) -> ThreadSet.add t (voc_from_pair_integer i)
  | SetPairMin ps    -> voc_from_pair_setpair ps
  | SetPairMax ps    -> voc_from_pair_setpair ps


and voc_from_funterm (t:fun_term) : ThreadSet.t =
  match t with
    FunVar v        -> opt_th (V.parameter v)
  | FunUpd (f,th,v) -> ThreadSet.singleton th


and voc_from_pair_set (s:set) : ThreadSet.t =
  match s with
    VarSet v      -> opt_th (V.parameter v)
  | EmptySet      -> ThreadSet.empty
  | Singl i       -> voc_from_pair_integer i
  | Union (s1,s2) -> ThreadSet.union (voc_from_pair_set s1)
                                       (voc_from_pair_set s2)
  | Intr (s1,s2)  -> ThreadSet.union (voc_from_pair_set s1)
                                       (voc_from_pair_set s2)
  | Diff (s1,s2)  -> ThreadSet.union (voc_from_pair_set s1)
                                       (voc_from_pair_set s2)
  | Lower (s,i)   -> ThreadSet.union (voc_from_pair_set s)
                                     (voc_from_pair_integer i)


and voc_from_pair_setpair (ps:setpair) : ThreadSet.t =
  match ps with
    VarSetPair v         -> opt_th (V.parameter v)
  | EmptySetPair         -> ThreadSet.empty
  | SinglPair p          -> voc_from_pair_pair p
  | UnionPair (s1,s2) -> ThreadSet.union (voc_from_pair_setpair s1)
                                            (voc_from_pair_setpair s2)
  | IntrPair (s1,s2)  -> ThreadSet.union (voc_from_pair_setpair s1)
                                            (voc_from_pair_setpair s2)
  | SetdiffPair (s1,s2)  -> ThreadSet.union (voc_from_pair_setpair s1)
                                            (voc_from_pair_setpair s2)
  | LowerPair (ps,i)  -> ThreadSet.union (voc_from_pair_setpair ps)
                                            (voc_from_pair_integer i)


and voc_from_pair_term (t:term) : ThreadSet.t =
  match t with
    IntV i      -> voc_from_pair_integer i
  | PairV p     -> voc_from_pair_pair p
  | SetV s      -> voc_from_pair_set s
  | SetPairV ps -> voc_from_pair_setpair ps


let voc_from_pair_atom (a:atom) : ThreadSet.t =
  let union = ThreadSet.union in
  let voc_tid     = voc_from_pair_tid in
  let voc_int     = voc_from_pair_integer in
  let voc_pair    = voc_from_pair_pair in
  let voc_term    = voc_from_pair_term in
  let voc_set     = voc_from_pair_set in
  let voc_setpair = voc_from_pair_setpair in
  match a with
    Less (t1,t2)            -> union (voc_int t1) (voc_int t2)
  | Greater (t1,t2)         -> union (voc_int t1) (voc_int t2)
  | LessEq (t1,t2)          -> union (voc_int t1) (voc_int t2)
  | GreaterEq (t1,t2)       -> union (voc_int t1) (voc_int t2)
  | LessTid (th1,th2)       -> thset_from [th1;th2]
  | Eq (t1,t2)              -> union (voc_term t1) (voc_term t2)
  | InEq (t1,t2)            -> union (voc_term t1) (voc_term t2)
  | In (i,s)                -> union (voc_int i) (voc_set s)
  | Subset (s1,s2)          -> union (voc_set s1) (voc_set s2)
  | InTidPair (t,ps)        -> union (voc_tid t) (voc_setpair ps)
  | InIntPair (i,ps)        -> union (voc_int i) (voc_setpair ps)
  | InPair (p,ps)           -> union (voc_pair p) (voc_setpair ps)
  | SubsetEqPair (ps1,ps2)  -> union (voc_setpair ps1) (voc_setpair ps2)
  | TidEq (th1,th2)         -> union (voc_tid th1) (voc_tid th2)
  | TidInEq (th1,th2)       -> union (voc_tid th1) (voc_tid th2)
  | FunEq (f1,f2)           -> ThreadSet.empty
  | FunInEq (f1,f2)         -> ThreadSet.empty
  | UniqueInt ps            -> (voc_setpair ps)
  | UniqueTid ps            -> (voc_setpair ps)
  | PC (pc,th,pr)           -> opt_th th
  | PCUpdate (pc,th)        -> ThreadSet.singleton th
  | PCRange (_,_,th,_)      -> opt_th th

let voc_fs = Formula.make_fold
               Formula.GenericLiteralFold
               (fun info a -> voc_from_pair_atom a)
               (fun info -> ThreadSet.empty)
               ThreadSet.union

let voc_from_pair_formula (phi:formula) : ThreadSet.t =
  Formula.formula_fold voc_fs () phi



let voc (phi:formula) : tid list =
  ThreadSet.elements (voc_from_pair_formula phi)


let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)


(* Set of variables from a formula *)

let (@@) s1 s2 =
  V.VarSet.union s1 s2

let rec get_varset_from_param (v:V.t) : V.VarSet.t =
  match V.parameter v with
  | V.Local t -> V.VarSet.singleton t
  | _ -> V.VarSet.empty

and get_varset_tid th =
  match th with
  | VarTh v   -> V.VarSet.singleton v @@ get_varset_from_param v
  | NoTid     -> V.VarSet.empty
  | PairTid p -> (get_varset_pair p)

and get_varset_int i =
  match i with
  | Val _         -> V.VarSet.empty
  | Var v         -> V.VarSet.singleton v @@ get_varset_from_param v
  | Neg j         -> (get_varset_int j)
  | Add (i1,i2)   -> (get_varset_int i1) @@ (get_varset_int i2)
  | Sub (i1,i2)   -> (get_varset_int i1) @@ (get_varset_int i2)
  | Mul (i1,i2)   -> (get_varset_int i1) @@ (get_varset_int i2)
  | Div (i1,i2)   -> (get_varset_int i1) @@ (get_varset_int i2)
  | ArrayRd (_,t) -> (get_varset_tid t)
  | SetMin s      -> (get_varset_set s)
  | SetMax s      -> (get_varset_set s)
  | PairInt p     -> (get_varset_pair p)

and get_varset_pair p =
  match p with
  | VarPair v        -> V.VarSet.singleton v @@ get_varset_from_param v
  | IntTidPair (i,t) -> (get_varset_int i) @@ (get_varset_tid t)
  | SetPairMin sp    -> (get_varset_setpair sp)
  | SetPairMax sp    -> (get_varset_setpair sp)

and get_varset_set s =
  match s with
  | VarSet v     -> V.VarSet.singleton v @@ get_varset_from_param v
  | EmptySet     -> V.VarSet.empty
  | Singl(i)     -> (get_varset_int i)
  | Union(s1,s2) -> (get_varset_set s1) @@ (get_varset_set s2)
  | Intr(s1,s2)  -> (get_varset_set s1) @@ (get_varset_set s2)
  | Diff(s1,s2)  -> (get_varset_set s1) @@ (get_varset_set s2)
  | Lower(s,i)   -> (get_varset_set s) @@ (get_varset_int i)

and get_varset_setpair s =
  match s with
  | VarSetPair v     -> V.VarSet.singleton v @@ get_varset_from_param v
  | EmptySetPair     -> V.VarSet.empty
  | SinglPair(p)     -> (get_varset_pair p)
  | UnionPair(s1,s2) -> (get_varset_setpair s1) @@ (get_varset_setpair s2)
  | IntrPair(s1,s2)  -> (get_varset_setpair s1) @@ (get_varset_setpair s2)
  | SetdiffPair(s1,s2)  -> (get_varset_setpair s1) @@ (get_varset_setpair s2)
  | LowerPair(s,i)   -> (get_varset_setpair s) @@ (get_varset_int i)

and get_varset_term t =
  match t with
  | IntV i      -> get_varset_int i
  | PairV p     -> get_varset_pair p
  | SetV s      -> get_varset_set s
  | SetPairV sp -> get_varset_setpair sp

and get_varset_fun f =
  match f with
  | FunVar v -> V.VarSet.singleton v @@ get_varset_from_param v
  | FunUpd (g,t,x) -> (get_varset_fun g) @@ (get_varset_tid t) @@ (get_varset_term x)
  
and get_varset_atom a =
  match a with
    Less (i1,i2)           -> (get_varset_int i1) @@ (get_varset_int i2)
  | Greater (i1,i2)        -> (get_varset_int i1) @@ (get_varset_int i2)
  | LessEq (i1,i2)         -> (get_varset_int i1) @@ (get_varset_int i2)
  | GreaterEq (i1,i2)      -> (get_varset_int i1) @@ (get_varset_int i2)
  | LessTid (t1,t2)        -> (get_varset_tid t1) @@ (get_varset_tid t2)
  | In (i,s)               -> (get_varset_int i) @@ (get_varset_set s)
  | Subset (s1,s2)         -> (get_varset_set s1) @@ (get_varset_set s2)
  | InTidPair (t,sp)       -> (get_varset_tid t) @@ (get_varset_setpair sp)
  | InIntPair (i,sp)       -> (get_varset_int i) @@ (get_varset_setpair sp)
  | InPair (p,sp)          -> (get_varset_pair p) @@ (get_varset_setpair sp)
  | SubsetEqPair (sp1,sp2) -> (get_varset_setpair sp1) @@ (get_varset_setpair sp2)
  | Eq (x1,x2)             -> (get_varset_term x1) @@ (get_varset_term x2)
  | InEq (x1,x2)           -> (get_varset_term x1) @@ (get_varset_term x2)
  | TidEq (t1,t2)          -> (get_varset_tid t1) @@ (get_varset_tid t2)
  | TidInEq (t1,t2)        -> (get_varset_tid t1) @@ (get_varset_tid t2)
  | FunEq (f1,f2)          -> (get_varset_fun f1) @@ (get_varset_fun f2)
  | FunInEq (f1,f2)        -> (get_varset_fun f1) @@ (get_varset_fun f2)
  | UniqueInt sp           -> get_varset_setpair sp
  | UniqueTid sp           -> get_varset_setpair sp
  | PC(pc,th,pr)           -> (match th with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> V.VarSet.singleton t)
  | PCUpdate (pc,th)       -> (get_varset_tid th)
  | PCRange(pc1,pc2,th,pr) -> (match th with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> V.VarSet.singleton t)


let varset_fs = Formula.make_fold
                  Formula.GenericLiteralFold
                  (fun info a -> get_varset_atom a)
                  (fun info -> V.VarSet.empty)
                  V.VarSet.union


let get_varset_from_literal (l:literal) : V.VarSet.t =
  Formula.literal_fold varset_fs () l


let get_varset_from_conj (cf:conjunctive_formula) : V.VarSet.t =
  Formula.conjunctive_formula_fold varset_fs () cf

  
let get_varset_from_formula (phi:formula) : V.VarSet.t =
  Formula.formula_fold varset_fs () phi
