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
    | NE.In(i,_)          -> (cut_off_integer i)
    | NE.Subset _         -> incr counter
    | NE.InEq (NE.SetV _, NE.SetV _) -> incr counter
    | NE.FunInEq (NE.FunVar v, _)     ->
          if (NE.V.sort v) = NE.Set then incr counter
    | NE.FunInEq (NE.FunUpd (_,_,t),_)    ->
          begin
            match t with
              NE.SetV _ -> incr counter
            | _              -> ()
          end
    | _                                             -> () in

  let cutoff_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (fun _ a -> cut_off_atom a)
                    (fun _ -> ())
                    (fun a b -> a;b) in

  let cut_off_formula (phi:NE.formula) : unit =
    Formula.formula_fold cutoff_fs () phi in

  let _ = cut_off_formula f
  in
    !counter
