module E = Expression
module NE = NumExpression


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

let rec variable_to_int_variable (v:E.variable) : NE.variable =
  NE.build_var (E.var_id v)
               (sort_to_int_sort (E.var_sort v))
               (E.var_is_primed v)
               (shared_to_int_shared (E.var_parameter v))
               (scope_to_int_scope (E.var_scope v))


and shared_to_int_shared (th:E.shared_or_local) : NE.shared_or_local =
  match th with
  | E.Shared -> NE.Shared
  | E.Local t -> NE.Local t


and scope_to_int_scope (p:E.procedure_name) : NE.procedure_name =
  match p with
  | E.GlobalScope -> NE.GlobalScope
  | E.Scope proc -> NE.Scope proc



let rec array_to_funterm (x:E.arrays) : NE.fun_term =
  match x with
    E.VarArray v -> NE.FunVar (variable_to_int_variable v)
  | E.ArrayUp (a,th,E.Term (E.IntT i)) ->
      NE.FunUpd (array_to_funterm a, th, NE.IntV (integer_to_int_integer i))
  | E.ArrayUp (a,th,E.Term (E.SetIntT i)) ->
      NE.FunUpd (array_to_funterm a, th, NE.SetV (set_to_int_set i))
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
    | E.IntArrayRd(a,i) -> NE.ArrayRd(a,i)
    | E.IntSetMin(s)    -> NE.SetMin (toset s)
    | E.IntSetMax(s)    -> NE.SetMax (toset s)
    | E.CellMax(c)      -> raise(NotAnIntExpression(E.integer_to_str t))
    | E.HavocLevel      -> raise(NotAnIntExpression(E.integer_to_str t))


and atom_to_int_atom (a:E.atom) : NE.atom =
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
    | E.LessTid(x,y)  -> NE.LessTid(x,y)
    | E.LessElem _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.GreaterElem _ -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Eq(E.TidT x,E.TidT y)      -> NE.TidEq(x, y)
    | E.InEq(E.TidT x,E.TidT y)    -> NE.TidInEq(x, y)
    | E.Eq(E.ArrayT x, E.ArrayT y)   -> NE.FunEq (array_to_funterm x,
                                                        array_to_funterm y)
    | E.InEq(E.ArrayT x, E.ArrayT y) -> NE.FunInEq (array_to_funterm x,
                                                          array_to_funterm y)
    | E.Eq(E.IntT x, E.IntT y)       -> NE.Eq(NE.IntV (toint x),
                                                    NE.IntV (toint y))
    | E.Eq(E.SetIntT x, E.SetIntT y) -> NE.Eq(NE.SetV (toset x),
                                                    NE.SetV (toset y))
    | E.InEq(E.IntT x, E.IntT y)     -> NE.InEq(NE.IntV(toint x),
                                                      NE.IntV(toint y))
    | E.InEq(E.SetIntT x, E.SetIntT y) -> NE.InEq(NE.SetV(toset x),
                                                      NE.SetV(toset y))
    | E.Eq (_,_)   -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InEq (_,_) -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.BoolVar _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.BoolArrayRd _  -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.PC(i,th,pr)    -> NE.PC (i,shared_to_int_shared th,pr)
    | E.PCUpdate(i,th) -> NE.PCUpdate (i,th)
    | E.PCRange(i,j,th,pr) -> NE.PCRange (i,j,shared_to_int_shared th,pr)

and literal_to_int_literal (lit:E.literal) : NE.literal =
  match lit with
    E.Atom a    -> NE.Atom (atom_to_int_atom a)
  | E.NegAtom a -> NE.NegAtom (atom_to_int_atom a)

and formula_to_int_formula (phi:E.formula) : NE.formula =
  let toint = formula_to_int_formula in
    match phi with
        E.Literal(l)   -> NE.Literal(literal_to_int_literal l)
      | E.True         -> NE.True
      | E.False        -> NE.False
      | E.And(x,y)     -> NE.And(toint x,toint y)
      | E.Or(x,y)      -> NE.Or(toint x,toint y)
      | E.Not(x)       -> NE.Not(toint x)
      | E.Implies(x,y) -> NE.Implies(toint x,toint y)
      | E.Iff(x,y)     -> NE.Iff(toint x,toint y)


(* SUPERTYPE CONVERTER: *)
let rec variable_to_expr_variable (v:NE.variable) : E.variable =
  E.build_var (NE.var_id v)
              (sort_to_expr_sort (NE.var_sort v))
              (NE.var_is_primed v)
              (shared_to_expr_shared (NE.var_parameter v))
              (scope_to_expr_scope (NE.var_scope v))
              (E.RealVar)


and shared_to_expr_shared (th:NE.shared_or_local) : E.shared_or_local =
  match th with
  | NE.Shared  -> E.Shared
  | NE.Local t -> E.Local t


and scope_to_expr_scope (p:NE.procedure_name) : E.procedure_name =
  match p with
  | NE.GlobalScope -> E.GlobalScope
  | NE.Scope proc  -> E.Scope proc


and formula_to_expr_formula (phi:NE.formula) : E.formula =
  let to_formula = formula_to_expr_formula in
  match phi with
      NE.Literal(l)     -> E.Literal(literal_to_expr_literal l)
    | NE.True           -> E.True
    | NE.False          -> E.False
    | NE.And(x,y)       -> E.And    (to_formula x, to_formula y)
    | NE.Or(x,y)        -> E.Or     (to_formula x, to_formula y)
    | NE.Not(x)         -> E.Not    (to_formula x)
    | NE.Implies(x,y)   -> E.Implies(to_formula x, to_formula y)
    | NE.Iff(x,y)       -> E.Iff    (to_formula x, to_formula y)


and literal_to_expr_literal (l:NE.literal) : E.literal =
  match l with
    NE.Atom a    -> E.Atom (atom_to_expr_atom a)
  | NE.NegAtom a -> E.NegAtom (atom_to_expr_atom a)


and atom_to_expr_atom (a:NE.atom) : E.atom =
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match a with
      NE.Less(x,y)           -> E.Less        (from_int x,  from_int y)
    | NE.Greater(x,y)        -> E.Greater     (from_int x, from_int y)
    | NE.LessEq(x,y)         -> E.LessEq      (from_int x, from_int y)
    | NE.GreaterEq(x,y)      -> E.GreaterEq   (from_int x, from_int y)
    | NE.LessTid(x,y)        -> E.LessTid     (x, y)
    | NE.Eq(NE.IntV x,NE.IntV y) -> E.Eq      (E.IntT(from_int x),
                                               E.IntT(from_int y))
    | NE.Eq(NE.SetV x,NE.SetV y) -> E.Eq      (E.SetIntT(from_set x),
                                               E.SetIntT(from_set y))
    | NE.InEq(NE.IntV x,NE.IntV y) -> E.InEq  (E.IntT(from_int x),
                                               E.IntT(from_int y))
    | NE.InEq(NE.SetV x,NE.SetV y) -> E.InEq  (E.SetIntT(from_set x),
                                               E.SetIntT(from_set y))
    | NE.In(i,s)             -> E.InInt       (from_int i, from_set s)
    | NE.Subset(x,y)         -> E.SubsetEqInt (from_set x, from_set y)
    | NE.TidEq(x,y)          -> E.Eq          (E.TidT x, E.TidT y)
    | NE.TidInEq(x,y)        -> E.InEq        (E.TidT x, E.TidT y)
    | NE.FunEq(x,y)          -> E.Eq          (E.ArrayT (funterm_to_array x),
                                               E.ArrayT (funterm_to_array y))
    | NE.FunInEq(x,y)        -> E.InEq        (E.ArrayT (funterm_to_array x),
                                               E.ArrayT (funterm_to_array y))
    | NE.Eq(_,_)             -> raise(MalformedExpression(NE.atom_to_str a))
    | NE.InEq(_,_)           -> raise(MalformedExpression(NE.atom_to_str a))
    | NE.PC(i,th,pr)         -> E.PC (i, shared_to_expr_shared th, pr)
    | NE.PCUpdate(i,th)      -> E.PCUpdate (i, th)
    | NE.PCRange(i,j,th,pr)  -> E.PCRange (i, j, shared_to_expr_shared th, pr)


and funterm_to_array (x:NE.fun_term) : E.arrays =
  let from_int  = integer_to_expr_integer in
  let from_set  = set_to_expr_set in
  match x with
    NE.FunVar v                -> E.VarArray (variable_to_expr_variable v)
  | NE.FunUpd (f,th,NE.IntV i) -> E.ArrayUp (funterm_to_array f, th,
                                              E.Term (E.IntT (from_int i)))
  | NE.FunUpd (f,th,NE.SetV s) -> E.ArrayUp (funterm_to_array f, th,
                                              E.Term (E.SetIntT (from_set s)))


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
    | NE.ArrayRd(a,i) -> E.IntArrayRd(a,i)
    | NE.SetMin(s)    -> E.IntSetMin(from_set s)
    | NE.SetMax(s)    -> E.IntSetMax(from_set s)
