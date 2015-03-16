type 'atom literal =
  | Atom              of 'atom
  | NegAtom           of 'atom

type 'atom conjunctive_formula =
  | FalseConj
  | TrueConj
  | Conj              of 'atom literal list

type 'atom disjunctive_formula =
  | FalseDisj
  | TrueDisj
  | Disj              of 'atom literal list

type 'atom formula =
  | Literal           of 'atom literal
  | True
  | False
  | And               of 'atom formula * 'atom formula
  | Or                of 'atom formula * 'atom formula
  | Not               of 'atom formula
  | Implies           of 'atom formula * 'atom formula
  | Iff               of 'atom formula * 'atom formula

type ('atom, 'info, 'a) functions_t =
  {
    mutable literal_f : 'info -> 'atom literal -> 'a;
    atom_f : 'info -> 'atom -> 'a;
    base : 'info -> 'a;
    concat : 'a -> 'a -> 'a;
  }

type ('info, 'atom, 'a) literal_op_t =
  | GenericLiteralFold
  | ThisLiteralFold of ('info -> 'atom literal ->'a)

type ('atom, 'info) trans_functions_t =
  {
    mutable trans_literal_f : 'info -> 'atom literal -> 'atom literal;
    trans_atom_f : 'info -> 'atom -> 'atom;
  }

type ('info, 'atom) trans_literal_op_t =
  | GenericLiteralTrans
  | ThisLiteralTrans of ('info -> 'atom literal ->'atom literal)


(* Operation for pretty printing *)
type logic_op_t = AndOp | OrOp | ImpliesOp | IffOp | NotOp | NoneOp

exception ErrorInNNF
exception NotConjunctiveFormula
exception NotDisjunctiveFormula

module GenSet = LeapGenericSet


(* Configuration *)
let trueSym = "true"
let falseSym = "false"
let andSym = "/\\"
let orSym = "\\/"
let notSym = "~"
let implSym = "->"
let iffSym = "<->"


(*******************************)
(**  Formula transformations  **)
(*******************************)

let rec formula_trans (fs:('atom, 'info) trans_functions_t)
                      (info:'info)
                      (phi:'atom formula) : 'atom formula =
  match phi with
  | Literal l -> Literal (fs.trans_literal_f info l)
  | True -> True
  | False -> False
  | And (phi1,phi2) -> And (formula_trans fs info phi1,
                            formula_trans fs info phi2)
  | Or (phi1,phi2) -> Or (formula_trans fs info phi1,
                          formula_trans fs info phi2)
  | Not phi1 -> Not (formula_trans fs info phi1)
  | Implies (phi1,phi2) -> Implies (formula_trans fs info phi1,
                                    formula_trans fs info phi2)
  | Iff (phi1,phi2) -> Iff (formula_trans fs info phi1,
                            formula_trans fs info phi2)


let conjunctive_formula_trans (fs:('atom, 'info) trans_functions_t)
                              (info:'info)
                              (cf:'atom conjunctive_formula) : 'atom conjunctive_formula =
  match cf with
  | FalseConj -> FalseConj
  | TrueConj -> TrueConj
  | Conj ls -> Conj (List.map (fs.trans_literal_f info) ls)


let disjunctive_formula_trans (fs:('atom, 'info) trans_functions_t)
                              (info:'info)
                              (df:'atom disjunctive_formula) : 'atom disjunctive_formula =
  match df with
  | FalseDisj -> FalseDisj
  | TrueDisj -> TrueDisj
  | Disj ls -> Disj (List.map (fs.trans_literal_f info) ls)


let literal_trans (fs:('atom, 'info) trans_functions_t)
                  (info:'info)
                  (l:'atom literal) : 'atom literal =
  match l with
  | Atom a -> Atom (fs.trans_atom_f info a)
  | NegAtom a -> NegAtom (fs.trans_atom_f info a)


let make_trans (literal_fun:('info, 'atom) trans_literal_op_t)
               (atom_fun:'info -> 'atom -> 'atom)
    : ('atom, 'info) trans_functions_t =
  let trans_ops =
    {
      trans_literal_f = (fun _ l -> l);
      trans_atom_f = atom_fun;
    }
  in
    trans_ops.trans_literal_f <-
      begin
        match literal_fun with
        | GenericLiteralTrans -> literal_trans trans_ops
        | ThisLiteralTrans f -> f
      end;
    trans_ops


(*********************)
(**  Formula folds  **)
(*********************)

let rec formula_fold (fs:('atom, 'info, 'a) functions_t)
                     (info:'info)
                     (phi:'atom formula) : 'a =
  match phi with
  | Literal l -> fs.literal_f info l
  | True -> fs.base info
  | False -> fs.base info
  | Not phi1 -> formula_fold fs info phi1
  | And (phi1, phi2)
  | Or (phi1, phi2)
  | Implies (phi1, phi2)
  | Iff (phi1, phi2) -> fs.concat (formula_fold fs info phi1)
                                  (formula_fold fs info phi2)

let conjunctive_formula_fold (fs:('atom, 'info, 'a) functions_t)
                             (info:'info)
                             (cf:'atom conjunctive_formula) : 'a =
  match cf with
  | FalseConj -> fs.base info
  | TrueConj -> fs.base info
  | Conj ls -> List.fold_left (fun res l ->
                 fs.concat res (fs.literal_f info l)
               ) (fs.base info) ls


let disjunctive_formula_fold (fs:('atom, 'info, 'a) functions_t)
                             (info:'info)
                             (df:'atom disjunctive_formula) : 'a =
  match df with
  | FalseDisj -> fs.base info
  | TrueDisj -> fs.base info
  | Disj ls -> List.fold_left (fun res l ->
                 fs.concat res (fs.literal_f info l)
               ) (fs.base info) ls


let literal_fold (fs:('atom, 'info, 'a) functions_t)
                 (info:'info)
                 (l:'atom literal) : 'a =
  match l with
  | Atom a -> fs.atom_f info a
  | NegAtom a -> fs.atom_f info a


let make_fold (literal_fun:('info, 'atom, 'a) literal_op_t)
              (atom_fun:'info -> 'atom -> 'a)
              (base_elem:'info -> 'a)
              (concat_fun:'a -> 'a -> 'a)
    : ('atom, 'info, 'a) functions_t =
  let fold_ops =
    {
      literal_f = (fun info _ -> base_elem info);
      atom_f = atom_fun;
      base = base_elem;
      concat = concat_fun;
    }
  in
    fold_ops.literal_f <- begin
                            match literal_fun with
                            | GenericLiteralFold -> literal_fold fold_ops
                            | ThisLiteralFold f -> f
                          end;
    fold_ops


(***********************)
(**  Atom conversion  **)
(***********************)

let literal_conv (f:('a -> 'b))
                 (l:'a literal) : 'b literal =
  match l with
  | Atom a -> Atom (f a)
  | NegAtom a -> NegAtom (f a)


let conjunctive_formula_conv (f:('a -> 'b))
                             (cf:'a conjunctive_formula)
    : 'b conjunctive_formula =
  match cf with
  | FalseConj -> FalseConj
  | TrueConj -> TrueConj
  | Conj ls -> Conj (List.map (literal_conv f) ls)


let disjunctive_formula_conv (f:('a -> 'b))
                             (df:'a disjunctive_formula)
    : 'b disjunctive_formula =
  match df with
  | FalseDisj -> FalseDisj
  | TrueDisj -> TrueDisj
  | Disj ls -> Disj (List.map (literal_conv f) ls)


let rec formula_conv (f:('a -> 'b))
                     (phi:'a formula) : 'b formula =
  match phi with
  | Literal l -> Literal (literal_conv f l)
  | True -> True
  | False -> False
  | Not phi1 -> Not (formula_conv f phi1)
  | And (phi1, phi2) -> And (formula_conv f phi1,
                             formula_conv f phi2)
  | Or (phi1, phi2) -> Or (formula_conv f phi1,
                           formula_conv f phi2)
  | Implies (phi1, phi2) -> Implies (formula_conv f phi1,
                                     formula_conv f phi2)
  | Iff (phi1, phi2) -> Iff (formula_conv f phi1,
                             formula_conv f phi2)



(**************************)
(**  Formula operations  **)
(**************************)

let conj_list (xs:'atom formula list) : 'atom formula =
  match xs with
  | [] -> True
  | x::xs -> List.fold_left (fun a b -> And(a,b)) x xs

  
let disj_list (xs:'atom formula list) : 'atom formula =
  match xs with
  | [] -> False
  | x::xs -> List.fold_left (fun a b -> Or(a,b)) x xs


let conj_literals (ls:'atom literal list) : 'atom formula =
  match ls with
  | []    -> True
  | x::xs -> List.fold_left (fun phi l -> And(phi,Literal l)) (Literal x) xs  


let disj_literals (ls:'atom literal list) : 'atom formula =
  match ls with
  | []    -> False
  | x::xs -> List.fold_left (fun phi l -> Or(phi,Literal l)) (Literal x) xs


let to_conj_literals (phi:'atom formula) : 'atom literal list =
  let rec try_to_build_conjunction x =
    match x with
    | Literal l -> [l]
    | And(a,b)  -> (try_to_build_conjunction a) @ (try_to_build_conjunction b)
    | True      -> []
    |   _       -> raise(NotConjunctiveFormula)
  in
    try_to_build_conjunction phi


let to_disj_literals (phi:'atom formula) : 'atom literal list =
  let rec try_to_build_disjunction x =
    match x with
    | Literal l -> [l]
    | Or(a,b)   -> (try_to_build_disjunction a) @ (try_to_build_disjunction b)
    | False     -> []
    |   _       -> raise(NotDisjunctiveFormula)
  in
    try_to_build_disjunction phi


let rec to_conj_list (phi:'atom formula) : 'atom formula list =
  match phi with
  | And (f1,f2) -> (to_conj_list f1) @ (to_conj_list f2)
  | _           -> [phi]


let rec to_disj_list (phi:'atom formula) : 'atom formula list =
  match phi with
  | Or (f1,f2) -> (to_disj_list f1) @ (to_disj_list f2)
  | _          -> [phi]


let rec nnf (phi:'atom formula) : 'atom formula =
  match phi with
  | False -> False
  | True  -> True
  | Iff (e1,e2)    -> And (nnf (Implies (e1,e2)),nnf (Implies(e2,e1)))
  | Implies(e1,e2) -> Or (nnf (Not e1), nnf e2)
  | And(e1,e2)     -> And(nnf e1, nnf e2)
  | Or(e1,e2)      -> Or(nnf e1, nnf e2)
  | Not (Not e)    -> nnf e
  | Not (And (e1,e2)) -> Or (nnf (Not e1), nnf (Not e2))
  | Not (Or (e1, e2)) -> And (nnf (Not e1), nnf (Not e2))
  | Not (Implies (e1, e2)) ->And (nnf e1, nnf (Not e2))
  | Not (Iff (e1, e2)) ->  Or (And (nnf e1, nnf (Not e2)), And (nnf (Not e1), nnf e2))
  | Not Literal(Atom a) -> Literal(NegAtom a)
  | Not Literal(NegAtom a) -> Literal(Atom a)
  | Not True  -> False
  | Not False -> True
  | Literal(a) -> Literal(a)


let cnf (phi:'atom formula) : 'atom disjunctive_formula list =
  let rec cnf_nnf (nnfphi:'atom formula) : 'atom disjunctive_formula list =
    match nnfphi with
    | And(e1,e2)  ->
        begin
          match (cnf_nnf e1, cnf_nnf e2) with
          | ([FalseDisj],_)  -> [FalseDisj]
          | (_,[FalseDisj])  -> [FalseDisj]
          | ([TrueDisj],x) -> x
          | (x,[TrueDisj]) -> x
          | (lx,ly) -> lx @ ly
        end
    | Or(e1,e2) ->
        begin
          match (cnf_nnf e1, cnf_nnf e2) with
            ([TrueDisj],_) -> [TrueDisj]
          | (_,[TrueDisj]) -> [TrueDisj]
          | ([FalseDisj],x)  -> x
          | (x,[FalseDisj])  -> x
          | (e1_cnf, e2_cnf) ->
                let get_disjuncts d =
                  match d with
                  | Disj l -> l
                  | _ -> raise(ErrorInNNF)
                in
                (* here lx and ly  are lists of Disj none of which is 
                 * True or False *)
                let add_to_all_in_e2 final_list x1 =
                  let lx1 = get_disjuncts x1 in
                  let add_x1 l2 x2 = Disj(lx1 @ (get_disjuncts x2))::l2 in
                  let lst = List.fold_left add_x1 [] e2_cnf in
                    lst @ final_list
                in
                  List.fold_left add_to_all_in_e2 [] e1_cnf
        end
    | Literal(l) -> [ Disj [ l ]]
    | True       -> [TrueDisj]
    | False      -> [FalseDisj]
    | _          -> raise(ErrorInNNF)
  in
    cnf_nnf (nnf phi)


let dnf (phi:'atom formula) : 'atom conjunctive_formula list =
  let rec dnf_nnf (nnfphi:'atom formula) : 'atom conjunctive_formula list =
    match nnfphi with
    | Or(e1,e2)  ->
        begin
          match (dnf_nnf e1, dnf_nnf e2) with
          | ([TrueConj],_)  -> [TrueConj]
          | (_,[TrueConj])  -> [TrueConj]
          | ([FalseConj],x) -> x
          | (x,[FalseConj]) -> x
          | (lx,ly) -> lx @ ly
        end
    | And(e1,e2) ->
        begin
          match (dnf_nnf e1, dnf_nnf e2) with
            ([FalseConj],_) -> [FalseConj]
          | (_,[FalseConj]) -> [FalseConj]
          | ([TrueConj],x)  -> x
          | (x,[TrueConj])  -> x
          | (e1_dnf, e2_dnf) ->
                let get_conjuncts c =
                  match c with
                    Conj l -> l
                  | _ -> (*let msg = "Formula "^(FormulaStr.formula_to_str nnfphi)^" is not in NNF.\n" in*)
                           raise(ErrorInNNF)
                in
                (* here lx and ly  are lists of Conj none of which is 
                 * True or False *)
                let add_to_all_in_e2 final_list x1 =
                  let lx1 = get_conjuncts x1 in
                  let add_x1 l2 x2 = Conj(lx1 @ (get_conjuncts x2))::l2 in
                  let lst = List.fold_left add_x1 [] e2_dnf in
                    lst @ final_list
                in
                  List.fold_left add_to_all_in_e2 [] e1_dnf
        end
    | Literal(l) -> [ Conj [ l ]]
    | True       -> [TrueConj]
    | False      -> [FalseConj]
    | _          -> (*let msg = "Formula " ^(formula_to_str nnfexpr)^ " is not in NNF.\n" in*)
                      raise(ErrorInNNF)
  in
    dnf_nnf (nnf phi)


let conjunctive_to_formula (cf:'atom conjunctive_formula) : 'atom formula =
  match cf with
  | TrueConj -> True
  | FalseConj -> False
  | Conj ls -> conj_literals ls


let disjunctive_to_formula (df:'atom disjunctive_formula) : 'atom formula =
  match df with
  | TrueDisj  -> True
  | FalseDisj -> False
  | Disj ls -> disj_literals ls


let conjunctive_list_to_formula_list (cfs:'atom conjunctive_formula list)
    : 'atom formula list list =
  match cfs with
  | [] -> []
  | _  -> List.map (fun cf ->
            match cf with
            | TrueConj -> [True]
            | FalseConj -> [False]
            | Conj ls -> [conj_literals ls]
          ) cfs


let disjunctive_list_to_formula_list (dfs:'atom disjunctive_formula list)
    : 'atom formula list list =
  match dfs with
  | [] -> []
  | _  -> List.map (fun df ->
            match df with
            | TrueDisj -> [True]
            | FalseDisj -> [False]
            | Disj ls -> [disj_literals ls]
          ) dfs


let clean_lits (ls:'atom literal list) : 'atom literal list =
  let set = GenSet.empty () in
  let xs = List.fold_left (fun xs l ->
             if GenSet.mem set l then
               xs
             else
               (GenSet.add set l; l::xs)
           ) [] ls
  in
    List.rev xs


let cleanup_conj (cf:'atom conjunctive_formula) : 'atom conjunctive_formula =
  match cf with
  | TrueConj -> TrueConj
  | FalseConj -> FalseConj
  | Conj ls -> Conj (clean_lits ls)


let cleanup_disj (df:'atom disjunctive_formula) : 'atom disjunctive_formula =
  match df with
  | TrueDisj -> TrueDisj
  | FalseDisj -> FalseDisj
  | Disj ls -> Disj (clean_lits ls)


let rec cleanup (phi:'atom formula) : 'atom formula =
  match phi with
  | And (e, True)    -> cleanup e
  | And (True, e)    -> cleanup e
  | And (e1, e2)     -> And (cleanup e1, cleanup e2)
  | Or  (e, False)   -> cleanup e
  | Or  (False, e)   -> cleanup e
  | Or (e1, e2)      -> Or (cleanup e1, cleanup e2)
  | Not e            -> Not (cleanup e)
  | Implies (e1, e2) -> Implies(cleanup e1, cleanup e2)
  | Iff (e1, e2)     -> Iff (cleanup e1, cleanup e2)
  | _                -> phi


let cleanup_dups (ps:'atom formula list) : 'atom formula list =
  let set = GenSet.empty () in
  let xs = List.fold_left (fun xs p ->
             let ys' = List.fold_left (fun ys phi ->
                         if GenSet.mem set phi then
                           ys
                         else
                           (GenSet.add set phi; phi::ys)
                       ) [] (to_conj_list p)
              in
                (conj_list (List.rev ys')) :: xs
           ) [] ps
  in
    List.rev xs


let combine_conjunctive (cf1:'atom conjunctive_formula)
                        (cf2:'atom conjunctive_formula)
    : 'atom conjunctive_formula =
  match (cf1,cf2) with
  | (FalseConj, _) -> FalseConj
  | (_, FalseConj) -> FalseConj
  | (TrueConj, _)  -> cf2
  | (_, TrueConj)  -> cf1
  | (Conj ls1, Conj ls2) -> Conj (ls1 @ ls2)


let combine_conjunctive_list (cfs:'atom conjunctive_formula list)
    : 'atom conjunctive_formula =
  match cfs with
  | [] -> TrueConj
  | x::xs -> List.fold_left combine_conjunctive x xs


let atom_to_formula (a:'atom) : 'atom formula =
  Literal (Atom a)


let negatom_to_formula (a:'atom) : 'atom formula =
  Literal (NegAtom a)


let rec is_conjunctive (phi:'atom formula) : bool =
  match phi with
  | Literal _ -> true
  | True      -> true
  | False     -> true
  | And(f,g)  -> (is_conjunctive f) && (is_conjunctive g)
  | _         -> false



(***********************)
(**  Pretty printers  **)
(***********************)


let literal_to_str (atom_to_str:'atom -> string)
                   (l:'atom literal) : string =
  match l with
  | Atom a -> atom_to_str a
  | NegAtom a  -> "(" ^notSym^ " " ^(atom_to_str a)^ ")"


let concat_literals (atom_to_str:'atom -> string)
                    (ls:'atom literal list)
                    (sym:string) : string =
  match ls with
  | [] -> ""
  | l::[] -> literal_to_str atom_to_str l
  | x::xs -> List.fold_left (fun str l ->
               str ^ " " ^ sym ^ " " ^ (literal_to_str atom_to_str l)
             ) (literal_to_str atom_to_str x) xs


let conjunctive_formula_to_str (atom_to_str:'atom -> string)
                               (cf:'atom conjunctive_formula) : string =
  match cf with
  | TrueConj -> trueSym
  | FalseConj -> falseSym
  | Conj ls -> concat_literals atom_to_str ls andSym


let disjunctive_formula_to_str (atom_to_str:'atom -> string)
                               (df:'atom disjunctive_formula) : string =
  match df with
  | TrueDisj -> trueSym
  | FalseDisj -> falseSym
  | Disj ls -> concat_literals atom_to_str ls orSym


let rec formula_to_str_aux (atom_to_str:'atom -> string)
                           (op:logic_op_t)
                           (phi:'atom formula) : string =
  match phi with
  | Literal l -> literal_to_str atom_to_str l
  | True -> trueSym
  | False -> falseSym
  | And(a,b)     -> let a_str = formula_to_str_aux atom_to_str AndOp a in
                    let b_str = formula_to_str_aux atom_to_str AndOp b in
                    if op = AndOp then
                      a_str ^ " " ^andSym^ " " ^ b_str
                    else
                      "(" ^ a_str ^ " " ^andSym^ " " ^ b_str ^ ")"
  | Or(a,b)      -> let a_str = formula_to_str_aux atom_to_str OrOp a in
                    let b_str = formula_to_str_aux atom_to_str OrOp b in
                    if op = OrOp then
                      a_str ^ " " ^orSym^ " " ^ b_str
                    else
                      "(" ^ a_str ^ " " ^orSym^ " " ^ b_str ^ ")"
  | Not a        -> let a_str = formula_to_str_aux atom_to_str NotOp a in
                    if op = NotOp then
                      notSym ^ " " ^ a_str
                    else
                      "(" ^notSym^ " " ^ a_str ^ ")"
  | Implies(a,b) -> let a_str = formula_to_str_aux atom_to_str ImpliesOp a in
                    let b_str = formula_to_str_aux atom_to_str ImpliesOp b in
                    if op = ImpliesOp then
                      a_str ^ " " ^implSym^ " " ^ b_str
                    else
                      "(" ^ a_str ^ " " ^implSym^ " " ^ b_str ^ ")"
  | Iff(a,b)     -> let a_str = formula_to_str_aux atom_to_str IffOp a in
                    let b_str = formula_to_str_aux atom_to_str IffOp b in
                    if op = IffOp then
                      a_str ^ " " ^iffSym^ " " ^ b_str
                    else
                      "(" ^ a_str ^ " " ^iffSym^ " " ^ b_str ^ ")"

let formula_to_str (atom_to_str:'atom -> string)
                   (phi:'atom formula) : string =
  formula_to_str_aux atom_to_str NoneOp phi


(* Pruning functions *)

let prune_literal (prune_atom_f:'atom -> 'atom option)
                  (lit:'atom literal) : 'atom literal option =
  match lit with
  | Atom a    -> LeapLib.Option.lift (fun a' -> Atom a') (prune_atom_f a)
  | NegAtom a -> LeapLib.Option.lift (fun a' -> NegAtom a') (prune_atom_f a)


let rec prune_formula (prune_atom_f:'atom -> 'atom option)
                      (phi:'atom formula) : 'atom formula option =
  let prune_f = prune_formula prune_atom_f in
  match phi with
  | Literal lit     -> LeapLib.Option.lift (fun l -> Literal l) (prune_literal prune_atom_f lit)
  | True            -> None
  | False           -> None
  | And (f1,f2)     -> begin
                         match (prune_f f1, prune_f f2) with
                           (Some f1', Some f2') -> Some (And (f1',f2'))
                         | (Some f1', None    ) -> Some f1'
                         | (None    , Some f2') -> Some f2'
                         | (None    , None    ) -> None
                       end
  | Or (f1,f2)      -> begin
                         match (prune_f f1, prune_f f2) with
                           (Some f1', Some f2') -> Some (Or (f1',f2'))
                         | (Some f1', None    ) -> Some f1'
                         | (None    , Some f2') -> Some f2'
                         | (None    , None    ) -> None
                       end
  | Not (f)         -> LeapLib.Option.lift (fun f'-> Not f') (prune_f f)
  | Implies (f1,f2) -> prune_f (Or (Not f1, f2))
  | Iff (f1,f2)     -> prune_f (And (Implies (f1,f2), Implies (f2,f1)))
