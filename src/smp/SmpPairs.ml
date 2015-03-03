module PE = PairsExpression

let int_counter = ref 1
let tid_counter = ref 1

let cut_off (f:PE.formula) : (int * int) =
  let rec cut_off_integer (i:PE.integer) =
    match i with
    | PE.Var _       -> incr int_counter
    | PE.Val _       -> ()
    | PE.Neg j       -> cut_off_integer j
    | PE.Add (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.Sub (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.Mul (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.Div (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.SetMin _    -> incr int_counter
    | PE.SetMax _    -> incr int_counter
    | PE.PairInt p   -> cut_off_pair p
    | _                   -> ()
  and cut_off_tid (t:PE.tid) =
    match t with
    | PE.VarTh _     -> incr tid_counter
    | PE.NoTid       -> ()
    | PE.PairTid p   -> cut_off_pair p
  and cut_off_pair (p:PE.pair) =
    match p with
    | PE.VarPair _   -> ()
    | PE.IntTidPair (i,t) -> (cut_off_integer i; cut_off_tid t)
    | PE.SetPairMin (sp) -> ()
    | PE.SetPairMax (sp) -> () in
  let cut_off_atom (a:PE.atom) =
    match a with
    | PE.Less(i1,i2)      -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.Greater(i1,i2)   -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.LessEq(i1,i2)    -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.GreaterEq(i1,i2) -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.LessTid (t1,t2)  -> (cut_off_tid t1);(cut_off_tid t2)
    | PE.In(i,s)          -> (cut_off_integer i)
    | PE.Subset _         -> incr int_counter
    | PE.InTidPair (t,sp) -> (incr int_counter; cut_off_tid t)
    | PE.InIntPair (i,sp) -> (incr tid_counter; cut_off_integer i)
    | PE.UniqueTid sp     -> (incr tid_counter)
    | PE.UniqueInt sp     -> (incr int_counter)
    | PE.InEq (PE.SetV _, PE.SetV _) -> incr int_counter
    | PE.FunInEq (PE.FunVar v, _)     ->
          if (PE.V.sort v) = PE.Set then incr int_counter
    | PE.FunInEq (PE.FunUpd (_,_,t),_)    ->
          begin
            match t with
              PE.SetV _ -> incr int_counter
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

  let _ = cut_off_formula f
  in
    (!tid_counter, !int_counter)
