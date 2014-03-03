module E = Expression
module NE = NumExpression
module F = Formula


exception NotAnIntExpression of string
exception NotIntSort of string
exception MalformedExpression of string

(* Sort conversion *)
let sort_to_int_sort (s:E.sort) : NE.sort =
  match s with
    E.Int    -> NE.Int
  | E.SetInt -> NE.Set
  | E.Tid   -> NE.Tid
  | _           -> raise(NotIntSort(E.sort_to_str s))


let sort_to_expr_sort (s:NE.sort) : E.sort =
  match s with
    NE.Int  -> E.Int
  | NE.Set  -> E.SetInt
  | NE.Tid -> E.Tid


(* SUBTYPE CONVERTER: *)

let rec variable_to_int_variable (v:E.V.t) : NE.V.t =
  NE.build_var (E.V.id v)
               (sort_to_int_sort (E.V.sort v))
               (E.V.is_primed v)
               (shared_to_int_shared (E.V.parameter v))
               (scope_to_int_scope (E.V.scope v))


and shared_to_int_shared (th:E.V.shared_or_local) : NE.V.shared_or_local =
  match th with
  | E.V.Shared -> NE.V.Shared
  | E.V.Local t -> NE.V.Local (variable_to_int_variable t)


and scope_to_int_scope (p:E.V.procedure_name) : NE.V.procedure_name =
  match p with
  | E.V.GlobalScope -> NE.V.GlobalScope
  | E.V.Scope proc -> NE.V.Scope proc



let rec tid_to_int_tid (th:E.tid) : NE.tid =
  match th with
  | E.VarTh t -> NE.VarTh (variable_to_int_variable t)
  | E.NoTid -> NE.NoTid
  | _ -> raise(NotAnIntExpression(E.tid_to_str th))


and array_to_funterm (x:E.arrays) : NE.fun_term =
  match x with
    E.VarArray v -> NE.FunVar (variable_to_int_variable v)
  | E.ArrayUp (a,th,E.Term (E.IntT i)) ->
      NE.FunUpd (array_to_funterm a,
      tid_to_int_tid th,
      NE.IntT (integer_to_int_integer i))
  | E.ArrayUp (a,th,E.Term (E.SetIntT i)) ->
      NE.FunUpd (array_to_funterm a,
      tid_to_int_tid th,
      NE.SetT (set_to_int_set i))
  | _ -> raise(NotAnIntExpression(E.arrays_to_str x))


and set_to_int_set (s:E.setint) : NE.set =
  let toset = set_to_int_set in
  match s with
    E.VarSetInt v       -> NE.VarSet (variable_to_int_variable v)
  | E.EmptySetInt       -> NE.EmptySet
  | E.SinglInt i        -> NE.Singl (integer_to_int_integer i)
  | E.UnionInt(s1,s2)   -> NE.Union (toset s1, toset s2)
  | E.IntrInt(s1,s2)    -> NE.Intr (toset s1, toset s2)
  | E.SetdiffInt(s1,s2) -> NE.Diff (toset s1, toset s2)
  | _ -> raise(NotAnIntExpression(E.setint_to_str s))


and integer_to_int_integer (t:E.integer) : NE.integer =
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
    match t with
      E.IntVal(i)       -> NE.Val(i)
    | E.VarInt v        -> NE.Var(variable_to_int_variable v)
    | E.IntNeg(i)       -> NE.Neg(toint i)
    | E.IntAdd(x,y)     -> NE.Add(toint x,toint y)
    | E.IntSub(x,y)     -> NE.Sub(toint x,toint y)
    | E.IntMul(x,y)     -> NE.Mul(toint x,toint y)
    | E.IntDiv(x,y)     -> NE.Div(toint x,toint y)
    | E.IntArrayRd(a,i) -> raise(NotAnIntExpression(E.integer_to_str t))
    | E.IntSetMin(s)    -> NE.SetMin (toset s)
    | E.IntSetMax(s)    -> NE.SetMax (toset s)
    | E.CellMax(c)      -> raise(NotAnIntExpression(E.integer_to_str t))
    | E.HavocLevel      -> raise(NotAnIntExpression(E.integer_to_str t))


and atom_to_int_atom (a:E.atom) : NE.atom =
  let totid = tid_to_int_tid in
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
    match a with
      E.Append _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Reach _       -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.ReachAt _     -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.OrderList _   -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Skiplist _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.In _          -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.SubsetEq _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InTh _        -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.SubsetEqTh _  -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InInt _       -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.SubsetEqInt _ -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InElem _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.SubsetEqElem _-> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Less(x,y)     -> NE.Less(toint x,toint y)
    | E.Greater(x,y)  -> NE.Greater(toint x,toint y)
    | E.LessEq(x,y)   -> NE.LessEq(toint x,toint y)
    | E.GreaterEq(x,y)-> NE.GreaterEq(toint x,toint y)
    | E.LessTid(x,y)  -> NE.LessTid(totid x, totid y)
    | E.LessElem _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.GreaterElem _ -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Eq(E.TidT x,E.TidT y)      -> NE.Eq(NE.TidT (totid x),
                                            NE.TidT (totid y))
    | E.InEq(E.TidT x,E.TidT y)    -> NE.Eq(NE.TidT (totid x),
                                            NE.TidT (totid y))
    | E.Eq(E.ArrayT x, E.ArrayT y)   -> NE.Eq (NE.FuntermT (array_to_funterm x),
                                               NE.FuntermT (array_to_funterm y))
    | E.InEq(E.ArrayT x, E.ArrayT y) -> NE.InEq (NE.FuntermT (array_to_funterm x),
                                                 NE.FuntermT (array_to_funterm y))
    | E.Eq(E.IntT x, E.IntT y)       -> NE.Eq(NE.IntT (toint x),
                                              NE.IntT (toint y))
    | E.Eq(E.SetIntT x, E.SetIntT y) -> NE.Eq(NE.SetT (toset x),
                                              NE.SetT (toset y))
    | E.InEq(E.IntT x, E.IntT y)     -> NE.InEq(NE.IntT(toint x),
                                                NE.IntT(toint y))
    | E.InEq(E.SetIntT x, E.SetIntT y) -> NE.InEq(NE.SetT(toset x),
                                                  NE.SetT(toset y))
    | E.Eq (_,_)   -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InEq (_,_) -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.BoolVar _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.BoolArrayRd _  -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.PC(i,th,pr)    -> NE.PC (i,shared_to_int_shared th,pr)
    | E.PCUpdate(i,th) -> NE.PCUpdate (i,totid th)
    | E.PCRange(i,j,th,pr) -> NE.PCRange (i,j,shared_to_int_shared th,pr)

and formula_to_int_formula (phi:E.formula) : NE.formula =
  Formula.formula_conv atom_to_int_atom phi

(*
and literal_to_int_literal (lit:E.literal) : NE.literal =
  match lit with
    F.Atom a    -> F.Atom (atom_to_int_atom a)
  | F.NegAtom a -> F.NegAtom (atom_to_int_atom a)

and formula_to_int_formula (phi:E.formula) : NE.formula =
  let toint = formula_to_int_formula in
    match phi with
        F.Literal(l)   -> F.Literal(literal_to_int_literal l)
      | F.True         -> F.True
      | F.False        -> F.False
      | F.And(x,y)     -> F.And(toint x,toint y)
      | F.Or(x,y)      -> F.Or(toint x,toint y)
      | F.Not(x)       -> F.Not(toint x)
      | F.Implies(x,y) -> F.Implies(toint x,toint y)
      | F.Iff(x,y)     -> F.Iff(toint x,toint y)
*)


(* SUPERTYPE CONVERTER: *)
let rec variable_to_expr_variable (v:NE.V.t) : E.V.t =
  E.build_var (NE.V.id v)
              (sort_to_expr_sort (NE.V.sort v))
              (NE.V.is_primed v)
              (shared_to_expr_shared (NE.V.parameter v))
              (scope_to_expr_scope (NE.V.scope v))


and shared_to_expr_shared (th:NE.V.shared_or_local) : E.V.shared_or_local =
  match th with
  | NE.V.Shared  -> E.V.Shared
  | NE.V.Local t -> E.V.Local (variable_to_expr_variable t)


and scope_to_expr_scope (p:NE.V.procedure_name) : E.V.procedure_name =
  match p with
  | NE.V.GlobalScope -> E.V.GlobalScope
  | NE.V.Scope proc  -> E.V.Scope proc

and formula_to_expr_formula (phi:NE.formula) : E.formula =
  Formula.formula_conv atom_to_expr_atom phi
(*
and formula_to_expr_formula (phi:NE.formula) : E.formula =
  let to_formula = formula_to_expr_formula in
  match phi with
      F.Literal(l)     -> F.Literal(literal_to_expr_literal l)
    | F.True           -> F.True
    | F.False          -> F.False
    | F.And(x,y)       -> F.And    (to_formula x, to_formula y)
    | F.Or(x,y)        -> F.Or     (to_formula x, to_formula y)
    | F.Not(x)         -> F.Not    (to_formula x)
    | F.Implies(x,y)   -> F.Implies(to_formula x, to_formula y)
    | F.Iff(x,y)       -> F.Iff    (to_formula x, to_formula y)

and literal_to_expr_literal (l:NE.literal) : E.literal =
  match l with
    NE.Atom a    -> E.Atom (atom_to_expr_atom a)
  | NE.NegAtom a -> E.NegAtom (atom_to_expr_atom a)
*)


and atom_to_expr_atom (a:NE.atom) : E.atom =
  let from_tid = tid_to_expr_tid in
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match a with
      NE.Less(x,y)           -> E.Less        (from_int x,  from_int y)
    | NE.Greater(x,y)        -> E.Greater     (from_int x, from_int y)
    | NE.LessEq(x,y)         -> E.LessEq      (from_int x, from_int y)
    | NE.GreaterEq(x,y)      -> E.GreaterEq   (from_int x, from_int y)
    | NE.LessTid(x,y)        -> E.LessTid     (from_tid x, from_tid y)
    | NE.Eq(NE.IntT x,NE.IntT y) -> E.Eq      (E.IntT(from_int x),
                                               E.IntT(from_int y))
    | NE.Eq(NE.SetT x,NE.SetT y) -> E.Eq      (E.SetIntT(from_set x),
                                               E.SetIntT(from_set y))
    | NE.InEq(NE.IntT x,NE.IntT y) -> E.InEq  (E.IntT(from_int x),
                                               E.IntT(from_int y))
    | NE.InEq(NE.SetT x,NE.SetT y) -> E.InEq  (E.SetIntT(from_set x),
                                               E.SetIntT(from_set y))
    | NE.In(i,s)             -> E.InInt       (from_int i, from_set s)
    | NE.Subset(x,y)         -> E.SubsetEqInt (from_set x, from_set y)
    | NE.Eq(NE.TidT x,NE.TidT y) -> E.Eq (E.TidT (from_tid x), E.TidT (from_tid y))
    | NE.InEq(NE.TidT x, NE.TidT y) -> E.InEq (E.TidT (from_tid x), E.TidT (from_tid y))
    | NE.Eq(NE.FuntermT x, NE.FuntermT y) -> E.Eq (E.ArrayT (funterm_to_array x),
                                                   E.ArrayT (funterm_to_array y))
    | NE.InEq(NE.FuntermT x, NE.FuntermT y) -> E.InEq (E.ArrayT (funterm_to_array x),
                                                       E.ArrayT (funterm_to_array y))
    | NE.Eq(_,_)             -> raise(MalformedExpression(NE.atom_to_str a))
    | NE.InEq(_,_)           -> raise(MalformedExpression(NE.atom_to_str a))
    | NE.PC(i,th,pr)         -> E.PC (i, shared_to_expr_shared th, pr)
    | NE.PCUpdate(i,th)      -> E.PCUpdate (i, from_tid th)
    | NE.PCRange(i,j,th,pr)  -> E.PCRange (i, j, shared_to_expr_shared th, pr)


and tid_to_expr_tid (th:NE.tid) : E.tid =
  match th with
  | NE.VarTh t -> E.VarTh (variable_to_expr_variable t)
  | NE.NoTid -> E.NoTid


and funterm_to_array (x:NE.fun_term) : E.arrays =
  let from_tid  = tid_to_expr_tid in
  let from_int  = integer_to_expr_integer in
  let from_set  = set_to_expr_set in
  match x with
    NE.FunVar v                -> E.VarArray (variable_to_expr_variable v)
  | NE.FunUpd (f,th,NE.IntT i) -> E.ArrayUp (funterm_to_array f, from_tid th,
                                              E.Term (E.IntT (from_int i)))
  | NE.FunUpd (f,th,NE.SetT s) -> E.ArrayUp (funterm_to_array f, from_tid th,
                                              E.Term (E.SetIntT (from_set s)))
  | NE.FunUpd (_,_,_) -> raise(MalformedExpression(NE.funterm_to_str x))


and set_to_expr_set (s:NE.set) : E.setint =
  let from_set = set_to_expr_set in
  match s with
    NE.VarSet v     -> E.VarSetInt (variable_to_expr_variable v)
  | NE.EmptySet     -> E.EmptySetInt
  | NE.Singl i      -> E.SinglInt (integer_to_expr_integer i)
  | NE.Union(s1,s2) -> E.UnionInt (from_set s1, from_set s2)
  | NE.Intr(s1,s2)  -> E.IntrInt (from_set s1, from_set s2)
  | NE.Diff(s1,s2)  -> E.SetdiffInt (from_set s1, from_set s2)
    

and integer_to_expr_integer (t:NE.integer) : E.integer =
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match t with
      NE.Val(n)       -> E.IntVal(n)
    | NE.Var v        -> E.VarInt (variable_to_expr_variable v)
    | NE.Neg(x)       -> E.IntNeg(from_int x)
    | NE.Add(x,y)     -> E.IntAdd(from_int x,from_int y)
    | NE.Sub(x,y)     -> E.IntSub(from_int x,from_int y)
    | NE.Mul(x,y)     -> E.IntMul(from_int x,from_int y)
    | NE.Div(x,y)     -> E.IntDiv(from_int x,from_int y)
    | NE.SetMin(s)    -> E.IntSetMin(from_set s)
    | NE.SetMax(s)    -> E.IntSetMax(from_set s)
