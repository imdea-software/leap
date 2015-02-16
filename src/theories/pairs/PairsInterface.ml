module E = Expression
module PE = PairsExpression
module F = Formula


exception NotAPairsExpression of string
exception NotPairsSort of string
exception MalformedExpression of string

(* Sort conversion *)
let sort_to_pairs_sort (s:E.sort) : PE.sort =
  match s with
    E.Int    -> PE.Int
  | E.SetInt -> PE.Set
  | E.Tid   -> PE.Tid
  | _           -> raise(NotPairsSort(E.sort_to_str s))


let sort_to_expr_sort (s:PE.sort) : E.sort =
  match s with
    PE.Int  -> E.Int
  | PE.Set  -> E.SetInt
  | PE.Tid -> E.Tid


(* SUBTYPE CONVERTER: *)

let rec variable_to_pairs_variable (v:E.V.t) : PE.V.t =
  PE.build_var (E.V.id v)
               (sort_to_pairs_sort (E.V.sort v))
               (E.V.is_primed v)
               (shared_to_pairs_shared (E.V.parameter v))
               (scope_to_pairs_scope (E.V.scope v))
               ~treat_as_pc:(E.is_pc_var v)


and shared_to_pairs_shared (th:E.V.shared_or_local) : PE.V.shared_or_local =
  match th with
  | E.V.Shared -> PE.V.Shared
  | E.V.Local t -> PE.V.Local (variable_to_pairs_variable t)


and scope_to_pairs_scope (p:E.V.procedure_name) : PE.V.procedure_name =
  match p with
  | E.V.GlobalScope -> PE.V.GlobalScope
  | E.V.Scope proc -> PE.V.Scope proc



let rec tid_to_pairs_tid (th:E.tid) : PE.tid =
  match th with
  | E.VarTh t -> PE.VarTh (variable_to_pairs_variable t)
  | E.NoTid -> PE.NoTid
  | _ -> raise(NotAPairsExpression(E.tid_to_str th))


and array_to_funterm (x:E.arrays) : PE.fun_term =
  match x with
    E.VarArray v -> PE.FunVar (variable_to_pairs_variable v)
  | E.ArrayUp (a,th,E.Term (E.IntT i)) ->
      PE.FunUpd (array_to_funterm a,
      tid_to_pairs_tid th,
      PE.IntV (integer_to_pairs_integer i))
  | E.ArrayUp (a,th,E.Term (E.SetIntT i)) ->
      PE.FunUpd (array_to_funterm a,
      tid_to_pairs_tid th,
      PE.SetV (set_to_pairs_set i))
  | _ -> raise(NotAPairsExpression(E.arrays_to_str x))


and set_to_pairs_set (s:E.setint) : PE.set =
  let toint = integer_to_pairs_integer in
  let toset = set_to_pairs_set in
  match s with
    E.VarSetInt v       -> PE.VarSet (variable_to_pairs_variable v)
  | E.EmptySetInt       -> PE.EmptySet
  | E.SinglInt i        -> PE.Singl (toint i)
  | E.UnionInt(s1,s2)   -> PE.Union (toset s1, toset s2)
  | E.IntrInt(s1,s2)    -> PE.Intr (toset s1, toset s2)
  | E.SetdiffInt(s1,s2) -> PE.Diff (toset s1, toset s2)
  | E.SetLower(s,i)     -> PE.Lower (toset s, toint i)
  | _ -> raise(NotAPairsExpression(E.setint_to_str s))


and integer_to_pairs_integer (t:E.integer) : PE.integer =
  let totid = tid_to_pairs_tid in
  let toint = integer_to_pairs_integer in
  let toset = set_to_pairs_set in
    match t with
      E.IntVal(i)       -> PE.Val(i)
    | E.VarInt v        -> PE.Var(variable_to_pairs_variable v)
    | E.IntNeg(i)       -> PE.Neg(toint i)
    | E.IntAdd(x,y)     -> PE.Add(toint x,toint y)
    | E.IntSub(x,y)     -> PE.Sub(toint x,toint y)
    | E.IntMul(x,y)     -> PE.Mul(toint x,toint y)
    | E.IntDiv(x,y)     -> PE.Div(toint x,toint y)
    | E.IntArrayRd(a,i) -> PE.ArrayRd(a,totid i)
    | E.IntSetMin(s)    -> PE.SetMin (toset s)
    | E.IntSetMax(s)    -> PE.SetMax (toset s)
    | E.CellMax(c)      -> raise(NotAPairsExpression(E.integer_to_str t))
    | E.HavocLevel      -> raise(NotAPairsExpression(E.integer_to_str t))


and atom_to_pairs_atom (a:E.atom) : PE.atom =
  let totid = tid_to_pairs_tid in
  let toint = integer_to_pairs_integer in
  let toset = set_to_pairs_set in
    match a with
      E.Append _      -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.Reach _       -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.ReachAt _     -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.OrderList _   -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.Skiplist _    -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.In _          -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.SubsetEq _    -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.InTh _        -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.SubsetEqTh _  -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.InInt (i,s)   -> PE.In (toint i, toset s)
    | E.SubsetEqInt (s1,s2) -> PE.Subset(toset s1, toset s2)
    | E.InElem _      -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.SubsetEqElem _-> raise(NotAPairsExpression(E.atom_to_str a))
    | E.Less(x,y)     -> PE.Less(toint x,toint y)
    | E.Greater(x,y)  -> PE.Greater(toint x,toint y)
    | E.LessEq(x,y)   -> PE.LessEq(toint x,toint y)
    | E.GreaterEq(x,y)-> PE.GreaterEq(toint x,toint y)
    | E.LessTid(x,y)  -> PE.LessTid(totid x, totid y)
    | E.LessElem _    -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.GreaterElem _ -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.Eq(E.TidT x,E.TidT y)      -> PE.TidEq(totid x, totid y)
    | E.InEq(E.TidT x,E.TidT y)    -> PE.TidInEq(totid x, totid y)
    | E.Eq(E.ArrayT x, E.ArrayT y)   -> PE.FunEq (array_to_funterm x,
                                                        array_to_funterm y)
    | E.InEq(E.ArrayT x, E.ArrayT y) -> PE.FunInEq (array_to_funterm x,
                                                          array_to_funterm y)
    | E.Eq(E.IntT x, E.IntT y)       -> PE.Eq(PE.IntV (toint x),
                                                    PE.IntV (toint y))
    | E.Eq(E.SetIntT x, E.SetIntT y) -> PE.Eq(PE.SetV (toset x),
                                                    PE.SetV (toset y))
    | E.InEq(E.IntT x, E.IntT y)     -> PE.InEq(PE.IntV(toint x),
                                                      PE.IntV(toint y))
    | E.InEq(E.SetIntT x, E.SetIntT y) -> PE.InEq(PE.SetV(toset x),
                                                      PE.SetV(toset y))
    | E.Eq (_,_)   -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.InEq (_,_) -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.BoolVar _      -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.BoolArrayRd _  -> raise(NotAPairsExpression(E.atom_to_str a))
    | E.PC(i,th,pr)    -> PE.PC (i,shared_to_pairs_shared th,pr)
    | E.PCUpdate(i,th) -> PE.PCUpdate (i,totid th)
    | E.PCRange(i,j,th,pr) -> PE.PCRange (i,j,shared_to_pairs_shared th,pr)

and formula_to_pairs_formula (phi:E.formula) : PE.formula =
  Formula.formula_conv atom_to_pairs_atom phi

(*
and literal_to_pairs_literal (lit:E.literal) : PE.literal =
  match lit with
    F.Atom a    -> F.Atom (atom_to_pairs_atom a)
  | F.NegAtom a -> F.NegAtom (atom_to_pairs_atom a)

and formula_to_pairs_formula (phi:E.formula) : PE.formula =
  let toint = formula_to_pairs_formula in
    match phi with
        F.Literal(l)   -> F.Literal(literal_to_pairs_literal l)
      | F.True         -> F.True
      | F.False        -> F.False
      | F.And(x,y)     -> F.And(toint x,toint y)
      | F.Or(x,y)      -> F.Or(toint x,toint y)
      | F.Not(x)       -> F.Not(toint x)
      | F.Implies(x,y) -> F.Implies(toint x,toint y)
      | F.Iff(x,y)     -> F.Iff(toint x,toint y)
*)


(* SUPERTYPE CONVERTER: *)
let rec variable_to_expr_variable (v:PE.V.t) : E.V.t =
  E.build_var (PE.V.id v)
              (sort_to_expr_sort (PE.V.sort v))
              (PE.V.is_primed v)
              (shared_to_expr_shared (PE.V.parameter v))
              (scope_to_expr_scope (PE.V.scope v))


and shared_to_expr_shared (th:PE.V.shared_or_local) : E.V.shared_or_local =
  match th with
  | PE.V.Shared  -> E.V.Shared
  | PE.V.Local t -> E.V.Local (variable_to_expr_variable t)


and scope_to_expr_scope (p:PE.V.procedure_name) : E.V.procedure_name =
  match p with
  | PE.V.GlobalScope -> E.V.GlobalScope
  | PE.V.Scope proc  -> E.V.Scope proc

and formula_to_expr_formula (phi:PE.formula) : E.formula =
  Formula.formula_conv atom_to_expr_atom phi
(*
and formula_to_expr_formula (phi:PE.formula) : E.formula =
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

and literal_to_expr_literal (l:PE.literal) : E.literal =
  match l with
    PE.Atom a    -> E.Atom (atom_to_expr_atom a)
  | PE.NegAtom a -> E.NegAtom (atom_to_expr_atom a)
*)


and atom_to_expr_atom (a:PE.atom) : E.atom =
  let from_tid = tid_to_expr_tid in
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match a with
      PE.Less(x,y)           -> E.Less        (from_int x,  from_int y)
    | PE.Greater(x,y)        -> E.Greater     (from_int x, from_int y)
    | PE.LessEq(x,y)         -> E.LessEq      (from_int x, from_int y)
    | PE.GreaterEq(x,y)      -> E.GreaterEq   (from_int x, from_int y)
    | PE.LessTid(x,y)        -> E.LessTid     (from_tid x, from_tid y)
    | PE.Eq(PE.IntV x,PE.IntV y) -> E.Eq      (E.IntT(from_int x),
                                               E.IntT(from_int y))
    | PE.Eq(PE.SetV x,PE.SetV y) -> E.Eq      (E.SetIntT(from_set x),
                                               E.SetIntT(from_set y))
    | PE.InEq(PE.IntV x,PE.IntV y) -> E.InEq  (E.IntT(from_int x),
                                               E.IntT(from_int y))
    | PE.InEq(PE.SetV x,PE.SetV y) -> E.InEq  (E.SetIntT(from_set x),
                                               E.SetIntT(from_set y))
    | PE.In(i,s)             -> E.InInt       (from_int i, from_set s)
    | PE.Subset(x,y)         -> E.SubsetEqInt (from_set x, from_set y)
    | PE.TidEq(x,y)          -> E.Eq          (E.TidT (from_tid x), E.TidT (from_tid y))
    | PE.TidInEq(x,y)        -> E.InEq        (E.TidT (from_tid x), E.TidT (from_tid y))
    | PE.FunEq(x,y)          -> E.Eq          (E.ArrayT (funterm_to_array x),
                                               E.ArrayT (funterm_to_array y))
    | PE.FunInEq(x,y)        -> E.InEq        (E.ArrayT (funterm_to_array x),
                                               E.ArrayT (funterm_to_array y))
    | PE.Eq(_,_)             -> raise(MalformedExpression(PE.atom_to_str a))
    | PE.InEq(_,_)           -> raise(MalformedExpression(PE.atom_to_str a))
    | PE.PC(i,th,pr)         -> E.PC (i, shared_to_expr_shared th, pr)
    | PE.PCUpdate(i,th)      -> E.PCUpdate (i, from_tid th)
    | PE.PCRange(i,j,th,pr)  -> E.PCRange (i, j, shared_to_expr_shared th, pr)


and tid_to_expr_tid (th:PE.tid) : E.tid =
  match th with
  | PE.VarTh t -> E.VarTh (variable_to_expr_variable t)
  | PE.NoTid -> E.NoTid


and funterm_to_array (x:PE.fun_term) : E.arrays =
  let from_tid  = tid_to_expr_tid in
  let from_int  = integer_to_expr_integer in
  let from_set  = set_to_expr_set in
  match x with
    PE.FunVar v                -> E.VarArray (variable_to_expr_variable v)
  | PE.FunUpd (f,th,PE.IntV i) -> E.ArrayUp (funterm_to_array f, from_tid th,
                                              E.Term (E.IntT (from_int i)))
  | PE.FunUpd (f,th,PE.SetV s) -> E.ArrayUp (funterm_to_array f, from_tid th,
                                              E.Term (E.SetIntT (from_set s)))


and set_to_expr_set (s:PE.set) : E.setint =
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match s with
    PE.VarSet v     -> E.VarSetInt (variable_to_expr_variable v)
  | PE.EmptySet     -> E.EmptySetInt
  | PE.Singl i      -> E.SinglInt (from_int i)
  | PE.Union(s1,s2) -> E.UnionInt (from_set s1, from_set s2)
  | PE.Intr(s1,s2)  -> E.IntrInt (from_set s1, from_set s2)
  | PE.Diff(s1,s2)  -> E.SetdiffInt (from_set s1, from_set s2)
  | PE.Lower(s,i)   -> E.SetLower (from_set s, from_int i)
    

and integer_to_expr_integer (t:PE.integer) : E.integer =
  let from_tid = tid_to_expr_tid in
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match t with
      PE.Val(n)       -> E.IntVal(n)
    | PE.Var v        -> E.VarInt (variable_to_expr_variable v)
    | PE.Neg(x)       -> E.IntNeg(from_int x)
    | PE.Add(x,y)     -> E.IntAdd(from_int x,from_int y)
    | PE.Sub(x,y)     -> E.IntSub(from_int x,from_int y)
    | PE.Mul(x,y)     -> E.IntMul(from_int x,from_int y)
    | PE.Div(x,y)     -> E.IntDiv(from_int x,from_int y)
    | PE.ArrayRd(a,i) -> E.IntArrayRd(a,from_tid i)
    | PE.SetMin(s)    -> E.IntSetMin(from_set s)
    | PE.SetMax(s)    -> E.IntSetMax(from_set s)
