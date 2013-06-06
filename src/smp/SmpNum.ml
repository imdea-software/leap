module NE = NumExpression

let counter = ref 0

let cut_off (f:NE.formula) : int =
  let _ = counter := 1 in (* Count 1 to represent undefined value *)
  let rec cut_off_integer (i:NE.integer) =
    match i with
      NE.Neg j       -> cut_off_integer j
    | NE.Add (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | NE.Sub (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | NE.Mul (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | NE.Div (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | NE.SetMin _    -> incr counter
    | NE.SetMax _    -> incr counter
    | _                   -> () in
  let cut_off_atom (a:NE.atom) =
    match a with
    | NE.Less(i1,i2)      -> (cut_off_integer i1);(cut_off_integer i2)
    | NE.Greater(i1,i2)   -> (cut_off_integer i1);(cut_off_integer i2)
    | NE.LessEq(i1,i2)    -> (cut_off_integer i1);(cut_off_integer i2)
    | NE.GreaterEq(i1,i2) -> (cut_off_integer i1);(cut_off_integer i2)
    | NE.In(i,s)          -> (cut_off_integer i)
    | NE.Subset _                              -> incr counter
    | NE.InEq (NE.SetV _, NE.SetV _) -> incr counter
    | NE.FunInEq (NE.FunVar v, _)     ->
          if v.NE.sort = NE.Set then incr counter
    | NE.FunInEq (NE.FunUpd (_,_,t),_)    ->
          begin
            match t with
              NE.SetV _ -> incr counter
            | _              -> ()
          end
    | _                                             -> () in
  let rec cut_off_literal (l:NE.literal) =
    match l with
      NE.Atom a    -> (cut_off_atom a)
    | NE.NegAtom a -> (cut_off_atom a) in
  let rec cut_off_formula (f:NE.formula) =
    match f with
      NE.And(f1,f2)     -> (cut_off_formula f1);(cut_off_formula f2)
    | NE.Or(f1,f2)      -> (cut_off_formula f1);(cut_off_formula f2)
    | NE.Not (f1)       -> (cut_off_formula f1)
    | NE.Implies(f1,f2) -> (cut_off_formula f1);(cut_off_formula f2)
    | NE.Iff(f1,f2)     -> (cut_off_formula f1);(cut_off_formula f2)
    | NE.Literal l      -> (cut_off_literal l)
    | _                      -> () in
  let _ = cut_off_formula f
  in
    !counter
