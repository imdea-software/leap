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
               ~treat_as_pc:(E.is_pc_var v)


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
      NE.IntV (integer_to_int_integer i))
  | E.ArrayUp (a,th,E.Term (E.SetIntT i)) ->
      NE.FunUpd (array_to_funterm a,
      tid_to_int_tid th,
      NE.SetV (set_to_int_set i))
  | _ -> raise(NotAnIntExpression(E.arrays_to_str x))


and set_to_int_set (s:E.setint) : NE.set =
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
  match s with
    E.VarSetInt v       -> NE.VarSet (variable_to_int_variable v)
  | E.EmptySetInt       -> NE.EmptySet
  | E.SinglInt i        -> NE.Singl (toint i)
  | E.UnionInt(s1,s2)   -> NE.Union (toset s1, toset s2)
  | E.IntrInt(s1,s2)    -> NE.Intr (toset s1, toset s2)
  | E.SetdiffInt(s1,s2) -> NE.Diff (toset s1, toset s2)
  | E.SetLower(s,i)     -> NE.Lower (toset s, toint i)
  | _ -> raise(NotAnIntExpression(E.setint_to_str s))


and integer_to_int_integer (t:E.integer) : NE.integer =
  let totid = tid_to_int_tid in
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
    | E.IntArrayRd(a,i) -> NE.ArrayRd(a,totid i)
    | E.IntSetMin(s)    -> NE.SetMin (toset s)
    | E.IntSetMax(s)    -> NE.SetMax (toset s)
    | E.CellMax _       -> raise(NotAnIntExpression(E.integer_to_str t))
    | E.HavocLevel      -> raise(NotAnIntExpression(E.integer_to_str t))
    | E.PairInt _       -> raise(NotAnIntExpression(E.integer_to_str t))


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
    | E.InInt (i,s)   -> NE.In (toint i, toset s)
    | E.SubsetEqInt (s1,s2) -> NE.Subset(toset s1, toset s2)
    | E.InElem _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.SubsetEqElem _-> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InPair _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.SubsetEqPair _-> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InTidPair _   -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.InIntPair _   -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Less(x,y)     -> NE.Less(toint x,toint y)
    | E.Greater(x,y)  -> NE.Greater(toint x,toint y)
    | E.LessEq(x,y)   -> NE.LessEq(toint x,toint y)
    | E.GreaterEq(x,y)-> NE.GreaterEq(toint x,toint y)
    | E.LessTid(x,y)  -> NE.LessTid(totid x, totid y)
    | E.LessElem _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.GreaterElem _ -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.Eq(E.TidT x,E.TidT y)      -> NE.TidEq(totid x, totid y)
    | E.InEq(E.TidT x,E.TidT y)    -> NE.TidInEq(totid x, totid y)
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
    | E.UniqueInt _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.UniqueTid _    -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.BoolVar _      -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.BoolArrayRd _  -> raise(NotAnIntExpression(E.atom_to_str a))
    | E.PC(i,th,pr)    -> NE.PC (i,shared_to_int_shared th,pr)
    | E.PCUpdate(i,th) -> NE.PCUpdate (i,totid th)
    | E.PCRange(i,j,th,pr) -> NE.PCRange (i,j,shared_to_int_shared th,pr)

and formula_to_int_formula (phi:E.formula) : NE.formula =
  Formula.formula_conv atom_to_int_atom phi



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
    | NE.TidEq(x,y)          -> E.Eq          (E.TidT (from_tid x), E.TidT (from_tid y))
    | NE.TidInEq(x,y)        -> E.InEq        (E.TidT (from_tid x), E.TidT (from_tid y))
    | NE.FunEq(x,y)          -> E.Eq          (E.ArrayT (funterm_to_array x),
                                               E.ArrayT (funterm_to_array y))
    | NE.FunInEq(x,y)        -> E.InEq        (E.ArrayT (funterm_to_array x),
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
  | NE.FunUpd (f,th,NE.IntV i) -> E.ArrayUp (funterm_to_array f, from_tid th,
                                              E.Term (E.IntT (from_int i)))
  | NE.FunUpd (f,th,NE.SetV s) -> E.ArrayUp (funterm_to_array f, from_tid th,
                                              E.Term (E.SetIntT (from_set s)))


and set_to_expr_set (s:NE.set) : E.setint =
  let from_int = integer_to_expr_integer in
  let from_set = set_to_expr_set in
  match s with
    NE.VarSet v     -> E.VarSetInt (variable_to_expr_variable v)
  | NE.EmptySet     -> E.EmptySetInt
  | NE.Singl i      -> E.SinglInt (from_int i)
  | NE.Union(s1,s2) -> E.UnionInt (from_set s1, from_set s2)
  | NE.Intr(s1,s2)  -> E.IntrInt (from_set s1, from_set s2)
  | NE.Diff(s1,s2)  -> E.SetdiffInt (from_set s1, from_set s2)
  | NE.Lower(s,i)   -> E.SetLower (from_set s, from_int i)
    

and integer_to_expr_integer (t:NE.integer) : E.integer =
  let from_tid = tid_to_expr_tid in
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
    | NE.ArrayRd(a,i) -> E.IntArrayRd(a,from_tid i)
    | NE.SetMin(s)    -> E.IntSetMin(from_set s)
    | NE.SetMax(s)    -> E.IntSetMax(from_set s)
