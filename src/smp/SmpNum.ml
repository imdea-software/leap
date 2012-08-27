module IntExpr = NumExpression

let counter = ref 0

let cut_off (f:IntExpr.formula) : int =
  let _ = counter := 1 in (* Count 1 to represent undefined value *)
  let rec cut_off_integer (i:IntExpr.integer) =
    match i with
      IntExpr.Neg j       -> cut_off_integer j
    | IntExpr.Add (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | IntExpr.Sub (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | IntExpr.Mul (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | IntExpr.Div (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | IntExpr.SetMin _    -> incr counter
    | IntExpr.SetMax _    -> incr counter
    | _                   -> () in
  let cut_off_atom (a:IntExpr.atom) =
    match a with
    | IntExpr.Less(i1,i2)      -> (cut_off_integer i1);(cut_off_integer i2)
    | IntExpr.Greater(i1,i2)   -> (cut_off_integer i1);(cut_off_integer i2)
    | IntExpr.LessEq(i1,i2)    -> (cut_off_integer i1);(cut_off_integer i2)
    | IntExpr.GreaterEq(i1,i2) -> (cut_off_integer i1);(cut_off_integer i2)
    | IntExpr.In(i,s)          -> (cut_off_integer i)
    | IntExpr.Subset _                              -> incr counter
    | IntExpr.InEq (IntExpr.SetV _, IntExpr.SetV _) -> incr counter
    | IntExpr.FunInEq (IntExpr.FunVar v, _)     ->
          if IntExpr.get_sort v = IntExpr.Set then incr counter
    | IntExpr.FunInEq (IntExpr.FunUpd (_,_,t),_)    ->
          begin
            match t with
              IntExpr.SetV _ -> incr counter
            | _              -> ()
          end
    | _                                             -> () in
  let rec cut_off_literal (l:IntExpr.literal) =
    match l with
      IntExpr.Atom a    -> (cut_off_atom a)
    | IntExpr.NegAtom a -> (cut_off_atom a) in
  let rec cut_off_formula (f:IntExpr.formula) =
    match f with
      IntExpr.And(f1,f2)     -> (cut_off_formula f1);(cut_off_formula f2)
    | IntExpr.Or(f1,f2)      -> (cut_off_formula f1);(cut_off_formula f2)
    | IntExpr.Not (f1)       -> (cut_off_formula f1)
    | IntExpr.Implies(f1,f2) -> (cut_off_formula f1);(cut_off_formula f2)
    | IntExpr.Iff(f1,f2)     -> (cut_off_formula f1);(cut_off_formula f2)
    | IntExpr.Literal l      -> (cut_off_literal l)
    | _                      -> () in
  let _ = cut_off_formula f
  in
    !counter
