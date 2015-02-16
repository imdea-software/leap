module PE = PairsExpression

let counter = ref 0

let cut_off (f:PE.formula) : int =
  let _ = counter := 1 in (* Count 1 to represent undefined value *)
  let rec cut_off_integer (i:PE.integer) =
    match i with
      PE.Neg j       -> cut_off_integer j
    | PE.Add (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | PE.Sub (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | PE.Mul (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | PE.Div (j1,j2) -> (cut_off_integer j1);(cut_off_integer j2)
    | PE.SetMin _    -> incr counter
    | PE.SetMax _    -> incr counter
    | _                   -> () in
  let cut_off_atom (a:PE.atom) =
    match a with
    | PE.Less(i1,i2)      -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.Greater(i1,i2)   -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.LessEq(i1,i2)    -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.GreaterEq(i1,i2) -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.In(i,s)          -> (cut_off_integer i)
    | PE.Subset _                              -> incr counter
    | PE.InEq (PE.SetV _, PE.SetV _) -> incr counter
    | PE.FunInEq (PE.FunVar v, _)     ->
          if (PE.V.sort v) = PE.Set then incr counter
    | PE.FunInEq (PE.FunUpd (_,_,t),_)    ->
          begin
            match t with
              PE.SetV _ -> incr counter
            | _              -> ()
          end
    | _                                             -> () in

  let cutoff_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (fun info a -> cut_off_atom a)
                    (fun info -> ())
                    (fun a b -> a;b) in

  let cut_off_formula (phi:PE.formula) : unit =
    Formula.formula_fold cutoff_fs () phi in
(*
  let rec cut_off_literal (l:PE.literal) =
    match l with
      PE.Atom a    -> (cut_off_atom a)
    | PE.NegAtom a -> (cut_off_atom a) in
  let rec cut_off_formula (f:PE.formula) =
    match f with
      PE.And(f1,f2)     -> (cut_off_formula f1);(cut_off_formula f2)
    | PE.Or(f1,f2)      -> (cut_off_formula f1);(cut_off_formula f2)
    | PE.Not (f1)       -> (cut_off_formula f1)
    | PE.Implies(f1,f2) -> (cut_off_formula f1);(cut_off_formula f2)
    | PE.Iff(f1,f2)     -> (cut_off_formula f1);(cut_off_formula f2)
    | PE.Literal l      -> (cut_off_literal l)
    | _                      -> () in
*)
  let _ = cut_off_formula f
  in
    !counter
