open LeapLib

module E = Expression
module F = Formula

type sort = Int | Set | Tid

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = unit
  end )

type tid =
  | VarTh of V.t
  | NoTid
and integer =
    Val           of int
  | Var           of V.t
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | SetMin        of set
  | SetMax        of set
and set =
    VarSet        of V.t
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
and term =
  | IntT          of integer
  | SetT          of set
  | FuntermT      of fun_term
  | TidT          of tid
and fun_term =
  | FunVar        of V.t
  | FunUpd        of fun_term * tid * term
and eq =          term * term
and diseq =       term * term
and atom =
    Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | In            of integer * set
  | Subset        of set * set
  | Eq            of eq
  | InEq          of diseq
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula


exception NotConjunctiveExpr of formula
exception Not_tid_var of tid

module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )



(**********  Folding  ***************)

type ('info, 'a) fold_ops_t =
  {
    base : 'info -> 'a;
    concat : 'a -> 'a -> 'a;
    var_f : ('info,'a) fold_ops_t -> 'info -> V.t -> 'a;
    mutable tid_f : ('info,'a) fold_ops_t -> 'info -> tid -> 'a;
    mutable int_f : ('info,'a) fold_ops_t -> 'info -> integer -> 'a;
    mutable set_f : ('info,'a) fold_ops_t -> 'info -> set -> 'a;
    mutable funterm_f : ('info,'a) fold_ops_t -> 'info -> fun_term -> 'a;
    mutable atom_f : ('info,'a) fold_ops_t -> 'info -> atom -> 'a;
    mutable term_f : ('info,'a) fold_ops_t -> 'info -> term -> 'a;
  }

type ('info, 'a) folding_t =
  {
    var_f : 'info -> V.t -> 'a;
    tid_f : 'info -> tid -> 'a;
    int_f : 'info -> integer -> 'a;
    set_f : 'info -> set -> 'a;
    funterm_f : 'info -> fun_term -> 'a;
    atom_f : 'info -> atom -> 'a;
    term_f : 'info -> term -> 'a;
  }



let rec fold_tid (fs:('info,'a) fold_ops_t) (info:'info) (t:tid) : 'a =
  match t with
  | VarTh v -> fs.var_f fs info v
  | NoTid   -> fs.base info

and fold_int (fs:('info,'a) fold_ops_t) (info:'info) (i:integer) : 'a =
  match i with
  | Val _ -> fs.base info
  | Var v -> fs.var_f fs info v
  | Neg j -> fs.int_f fs info j
  | Add (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | Sub (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | Mul (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | Div (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | SetMin s -> fs.set_f fs info s
  | SetMax s -> fs.set_f fs info s

and fold_set (fs:('info,'a) fold_ops_t) (info:'info) (s:set) : 'a =
  match s with
  | VarSet v     -> fs.var_f fs info v
  | EmptySet     -> fs.base info
  | Singl(i)     -> fs.int_f fs info i
  | Union(s1,s2) -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Intr(s1,s2)  -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Diff(s1,s2)  -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)

and fold_funterm (fs:('info,'a) fold_ops_t) (info:'info) (f:fun_term) : 'a =
  match f with
  | FunVar v -> fs.var_f fs info v
  | FunUpd (ft,th,t) -> fs.concat (fs.funterm_f fs info ft)
                                  (fs.concat (fs.tid_f fs info th)
                                             (fs.term_f fs info t))

and fold_atom (fs:('info,'a) fold_ops_t) (info:'info) (a:atom) : 'a =
  match a with
  | Less(i1,i2)               -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | LessEq(i1,i2)             -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | Greater(i1,i2)            -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | GreaterEq(i1,i2)          -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | LessTid (t1,t2)           -> fs.concat (fs.tid_f fs info t1)
                                           (fs.tid_f fs info t2)
  | In(i,s)                   -> fs.concat (fs.int_f fs info i) (fs.set_f fs info s)
  | Subset(s1,s2)             -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Eq((x,y))                 -> fs.concat (fs.term_f fs info x)
                                           (fs.term_f fs info y)
  | InEq((x,y))               -> fs.concat (fs.term_f fs info x)
                                           (fs.term_f fs info y)
  | PC(pc,th,pr)              -> (match th with
                                   | V.Shared -> fs.base info
                                   | V.Local t -> fs.var_f fs info t)
  | PCUpdate (pc,th)          -> fs.tid_f fs info th
  | PCRange(pc1,pc2,th,pr)    -> (match th with
                                   | V.Shared -> fs.base info
                                   | V.Local t -> fs.var_f fs info t)

and fold_term (fs:('info,'a) fold_ops_t) (info:'info) (t:term) : 'a =
  match t with

  | IntT   i   -> fs.int_f fs info i
  | SetT   s   -> fs.set_f fs info s
  | TidT  th   -> fs.tid_f fs info th
  | FuntermT t -> fs.funterm_f fs info t  


let make_fold ?(tid_f=fold_tid)
              ?(int_f=fold_int)
              ?(set_f=fold_set)
              ?(funterm_f=fold_funterm)
              ?(atom_f=fold_atom)
              ?(term_f=fold_term)
              (base:('info -> 'a))
              (concat:('a -> 'a -> 'a))
              (var_f :(('info,'a) fold_ops_t -> 'info -> V.t -> 'a))
    : ('info,'a) folding_t =
  let fs = {
    tid_f = tid_f; int_f = int_f; set_f = set_f; funterm_f = funterm_f;
    atom_f = atom_f; term_f = term_f;
    base = base; concat = concat; var_f = var_f; } in
  { tid_f = tid_f fs; int_f = int_f fs; set_f = set_f fs;
    funterm_f = funterm_f fs; atom_f = atom_f fs; term_f = term_f fs;
    var_f = var_f fs; }


(**********  Mapping  ***************)

type 'info map_ops_t =
  {
    var_f : 'info map_ops_t -> 'info -> V.t -> V.t;
    mutable tid_f : 'info map_ops_t -> 'info -> tid -> tid;
    mutable int_f : 'info map_ops_t -> 'info -> integer -> integer;
    mutable set_f : 'info map_ops_t -> 'info -> set -> set;
    mutable funterm_f : 'info map_ops_t -> 'info -> fun_term -> fun_term;
    mutable atom_f : 'info map_ops_t -> 'info -> atom -> atom;
    mutable term_f : 'info map_ops_t -> 'info -> term -> term;
  }

type 'info mapping_t =
  {
    var_f : 'info -> V.t -> V.t;
    tid_f : 'info -> tid -> tid;
    int_f : 'info -> integer -> integer;
    set_f : 'info -> set -> set;
    funterm_f : 'info -> fun_term -> fun_term;
    atom_f : 'info -> atom -> atom;
    term_f : 'info -> term -> term;
  }



let rec map_tid (fs:'info map_ops_t) (info:'info) (t:tid) : tid =
  match t with
  | VarTh v            -> VarTh (fs.var_f fs info v)
  | NoTid              -> NoTid

and map_int (fs:'info map_ops_t) (info:'info) (i:integer) : integer =
  match i with
  | Val j -> Val j
  | Var v -> Var (fs.var_f fs info v)
  | Neg j -> Neg (fs.int_f fs info j)
  | Add (j1,j2) -> Add (fs.int_f fs info j1, fs.int_f fs info j2)
  | Sub (j1,j2) -> Sub (fs.int_f fs info j1, fs.int_f fs info j2)
  | Mul (j1,j2) -> Mul (fs.int_f fs info j1, fs.int_f fs info j2)
  | Div (j1,j2) -> Div (fs.int_f fs info j1, fs.int_f fs info j2)
  | SetMin s -> SetMin (fs.set_f fs info s)
  | SetMax s -> SetMax (fs.set_f fs info s)

and map_set (fs:'info map_ops_t) (info:'info) (s:set) : set =
  match s with
  | VarSet v     -> VarSet (fs.var_f fs info v)
  | EmptySet     -> EmptySet
  | Singl(i)     -> Singl (fs.int_f fs info i)
  | Union(s1,s2) -> Union (fs.set_f fs info s1, fs.set_f fs info s2)
  | Intr(s1,s2)  -> Intr (fs.set_f fs info s1, fs.set_f fs info s2)
  | Diff(s1,s2)  -> Diff (fs.set_f fs info s1, fs.set_f fs info s2)

and map_funterm (fs:'info map_ops_t) (info:'info) (f:fun_term) : fun_term =
  match f with
  | FunVar v -> FunVar (fs.var_f fs info v)
  | FunUpd (ft,th,t) -> FunUpd (fs.funterm_f fs info ft,
                                fs.tid_f fs info th,
                                fs.term_f fs info t)


and map_atom (fs:'info map_ops_t) (info:'info) (a:atom) : atom =
  match a with


  | Less(i1,i2)               -> Less (fs.int_f fs info i1,
                                       fs.int_f fs info i2)
  | Greater(i1,i2)            -> Greater (fs.int_f fs info i1,
                                          fs.int_f fs info i2)
  | LessEq(i1,i2)             -> LessEq (fs.int_f fs info i1,
                                         fs.int_f fs info i2)
  | GreaterEq(i1,i2)          -> GreaterEq (fs.int_f fs info i1,
                                            fs.int_f fs info i2)
  | LessTid(t1,t2)            -> LessTid (fs.tid_f fs info t1,
                                          fs.tid_f fs info t2)
  | In(i,s)                   -> In (fs.int_f fs info i, fs.set_f fs info s)
  | Subset(s1,s2)             -> Subset (fs.set_f fs info s1, fs.set_f fs info s2)
  | Eq((x,y))                 -> Eq (fs.term_f fs info x,
                                     fs.term_f fs info y)
  | InEq((x,y))               -> InEq (fs.term_f fs info x,
                                       fs.term_f fs info y)
  | PC(pc,th,pr)              -> PC(pc, (match th with
                                         | V.Shared -> V.Shared
                                         | V.Local t -> V.Local(fs.var_f fs info t)),
                                    pr)
  | PCUpdate (pc,th)          -> PCUpdate (pc, fs.tid_f fs info th)
  | PCRange(pc1,pc2,th,pr)    -> PCRange (pc1, pc2,
                                          (match th with
                                           | V.Shared -> V.Shared
                                           | V.Local t -> V.Local(fs.var_f fs info t)),
                                          pr)

and map_term (fs:'info map_ops_t) (info:'info) (t:term) : term =
  match t with
  | SetT   s   -> SetT (fs.set_f fs info s)
  | TidT  th   -> TidT (fs.tid_f fs info th)
  | IntT   i   -> IntT (fs.int_f fs info i)
  | FuntermT t -> FuntermT (fs.funterm_f fs info t)



let make_map ?(tid_f=map_tid)
             ?(int_f=map_int)
             ?(set_f=map_set)
             ?(funterm_f=map_funterm)
             ?(atom_f=map_atom)
             ?(term_f=map_term)
             (var_f :('info map_ops_t -> 'info -> V.t -> V.t))
    : 'info mapping_t =
  let fs : 'info map_ops_t = {
    tid_f = tid_f; int_f = int_f; set_f = set_f; funterm_f = funterm_f;
    atom_f = atom_f; term_f = term_f; var_f = var_f; } in
  { tid_f = tid_f fs; int_f = int_f fs; set_f = set_f fs;
    funterm_f = funterm_f fs;
    atom_f = atom_f fs; term_f = term_f fs; var_f = var_f fs; }



(* Variable constructor *)
let build_var ?(fresh=false)
              (id:V.id)
              (s:sort)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
  V.build id s pr th p () ~fresh:fresh


(* CONVERTERS TO STRING *)
(* EXPR TO STR *)
let sort_to_str (s:sort) : string =
  match s with
    Int  -> "int"
  | Set  -> "set"
  | Tid -> "tid"

let generic_int_tid_to_str (srf:string -> string) (t:tid) : string =
  match t with
  | VarTh t -> V.to_str t
  | NoTid -> "#"

let rec generic_int_integer_to_str (srf:string -> string) (t:integer) : string =
  let int_str_f = generic_int_integer_to_str srf in
  let set_str_f = generic_int_set_to_str srf in
  match t with
    Val i          -> string_of_int i
  | Var v          -> V.to_str v
  | Neg t          -> srf ("-" ^ int_str_f t)
  | Add (t1,t2)    -> srf (int_str_f t1 ^ " + " ^ int_str_f t2)
  | Sub (t1,t2)    -> srf (int_str_f t1 ^ " - " ^ int_str_f t2)
  | Mul (t1,t2)    -> srf (int_str_f t1 ^ " * " ^ int_str_f t2)
  | Div (t1,t2)    -> srf (int_str_f t1 ^ " / " ^ int_str_f t2)
  | SetMin s       -> srf ("setIntMin(" ^ set_str_f s ^ ")")
  | SetMax s       -> srf ("setIntMax(" ^ set_str_f s ^ ")")


and generic_int_set_to_str (srf:string -> string) (s:set): string =
  let int_str_f = generic_int_integer_to_str srf in
  let set_str_f = generic_int_set_to_str srf in
  match s with
    VarSet v      -> V.to_str v
  | EmptySet      -> srf "emptyset"
  | Singl i       -> srf ("{" ^ int_str_f i ^ "}")
  | Union (s1,s2) -> srf (set_str_f s1 ^ " union " ^ set_str_f s2)
  | Intr (s1,s2)  -> srf (set_str_f s1 ^ " intr "  ^ set_str_f s2)
  | Diff (s1,s2)  -> srf (set_str_f s1 ^ " diff "  ^ set_str_f s2)


and generic_int_term_to_str (srf:string -> string) (t:term) : string =
  match t with
    IntT i -> generic_int_integer_to_str srf i
  | SetT s -> generic_int_set_to_str srf s
  | FuntermT t -> generic_funterm_to_str srf t
  | TidT th -> generic_int_tid_to_str srf th


and generic_funterm_to_str (srf:string -> string) (t:fun_term) : string =
  match t with
    FunVar v        -> V.to_str v
  | FunUpd (f,th,v) -> srf (Printf.sprintf "%s{%s<-%s}"
                            (generic_funterm_to_str srf f)
                            (generic_int_tid_to_str srf th)
                            (generic_int_term_to_str srf v))


let rec generic_atom_to_str (srf:string -> string) (a:atom) : string =
  let tid_str_f  = generic_int_tid_to_str srf in
  let int_str_f  = generic_int_integer_to_str srf in
  let set_str_f  = generic_int_set_to_str srf in
  let term_str_f = generic_int_term_to_str srf in
  match a with
    Less (t1,t2)      -> srf (int_str_f t1  ^ " < "  ^ int_str_f t2)
  | Greater (t1,t2)   -> srf (int_str_f t1  ^ " > "  ^ int_str_f t2)
  | LessEq (t1,t2)    -> srf (int_str_f t1  ^ " <= " ^ int_str_f t2)
  | GreaterEq (t1,t2) -> srf (int_str_f t1  ^ " >= " ^ int_str_f t2)
  | LessTid (th1,th2) -> srf (tid_str_f th1 ^ " < " ^ tid_str_f th2)
  | Eq (t1,t2)        -> srf (term_str_f t1 ^ " = "  ^ term_str_f t2)
  | InEq (t1,t2)      -> srf (term_str_f t1 ^ " != " ^ term_str_f t2)
  | In (i,s)          -> srf (int_str_f i   ^ " in " ^ set_str_f s)
  | Subset (s1,s2)    -> srf (set_str_f s1  ^ " subset " ^ set_str_f s2)
  | PC (pc,th,pr)    -> let i_str = if pr then "pc'" else "pc" in
                        let th_str = V.shared_or_local_to_str th in
                          Printf.sprintf "%s(%s) = %i" i_str th_str pc
  | PCUpdate (pc,th) -> let th_str = tid_str_f th in
                          Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,th,pr) -> let i_str = if pr then "pc'" else "pc" in
                               let th_str = V.shared_or_local_to_str th in
                                 Printf.sprintf "%i <= %s(%s) <= %i" pc1 i_str th_str pc2


and no_parenthesis (str:string) : string = str
and add_parenthesis (str:string) : string = "(" ^ str ^ ")"

(* No parenthesis printing functions *)
and integer_to_str (t:integer) : string =
  generic_int_integer_to_str no_parenthesis t

and funterm_to_str (t:fun_term) : string =
  generic_funterm_to_str no_parenthesis t

and tid_to_str (th:tid) : string =
  generic_int_tid_to_str no_parenthesis th

and atom_to_str (a:atom) : string =
  generic_atom_to_str no_parenthesis a

and literal_to_str (l:literal) : string =
  Formula.literal_to_str (generic_atom_to_str no_parenthesis) l

and formula_to_str (phi:formula) : string =
  Formula.formula_to_str (generic_atom_to_str no_parenthesis) phi
(*  generic_int_formula_to_str no_parenthesis f*)



(* Parenthesis printing functions *)
let integer_to_par_string (t:integer) : string =
  generic_int_integer_to_str add_parenthesis t

let funterm_to_par_string (t:fun_term) : string =
  generic_funterm_to_str add_parenthesis t

let literal_to_par_string (l:literal) : string =
  Formula.literal_to_str (generic_atom_to_str no_parenthesis) l

let formula_to_par_string (phi:formula) : string =
  Formula.formula_to_str (generic_atom_to_str no_parenthesis) phi
(*  generic_int_formula_to_str add_parenthesis f*)




(* has_variable : integer -> bool *)

let rec has_variable (t:integer) : bool =
  match t with
      Val(n)       -> false
    | Var _        -> true
    | Neg(x)       -> has_variable x
    | Add(x,y)     -> has_variable x || has_variable y
    | Sub(x,y)     -> has_variable x || has_variable y
    | Mul(x,y)     -> has_variable x || has_variable y
    | Div(x,y)     -> has_variable x || has_variable y
    | SetMin(s)    -> false
    | SetMax(s)    -> false


let is_linear_fold =
  make_fold (fun _ -> false) (&&) (fun _ _ v -> false)
  ~int_f:(fun fs info i ->
      match i with
      | Mul(x,y) -> (fs.int_f fs info x) && (fs.int_f fs info y) &&
                    (not ((has_variable x) && (has_variable y)))
      | Div _ -> false
      | Val _
      | Var _
      | SetMin _
      | SetMax _ -> true
      | _ -> fold_int fs info i)
  ~atom_f:(fun fs info a ->
      match a with
      | Less(x,y)            
      | Greater(x,y)         
      | LessEq(x,y)          
      | GreaterEq(x,y)       
      | Eq(IntT x,IntT y)    
      | InEq(IntT x, IntT y) -> fold_atom fs info a
      | _ -> false)

let is_linear_fs = Formula.make_fold
                     Formula.GenericLiteralFold
                     (is_linear_fold.atom_f)
                     (fun info -> true)
                     (&&)

let formula_is_linear (phi:formula) : bool =
  Formula.formula_fold is_linear_fs () phi



(* FOR SETVAR *)

let varset_fold =
  make_fold (fun _ -> V.VarSet.empty) V.VarSet.union
            (fun _ base v -> base v)

let varset_fs = Formula.make_fold
                  Formula.GenericLiteralFold
                  (varset_fold.atom_f)
                  (fun info -> V.VarSet.empty)
                  V.VarSet.union


let varset_from_int_formula (base:V.t -> 'a)
                            (phi:formula) : 'a =
  Formula.formula_fold varset_fs base phi


let varidset_fold =
  make_fold (fun _ -> V.VarIdSet.empty) V.VarIdSet.union
            (fun _ base v -> base v)

let varidset_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (varidset_fold.atom_f)
                    (fun info -> V.VarIdSet.empty)
                    V.VarIdSet.union


let varidset_from_int_formula (base:V.t -> 'a)
                              (phi:formula) : 'a =
  Formula.formula_fold varidset_fs base phi
                                 

(* Base functions for variables id *)

let base_setid_all_vars (v:V.t) : V.VarIdSet.t =
  V.VarIdSet.singleton (V.id v)


let base_setid_local_vars (v:V.t) : V.VarIdSet.t =
  match (V.scope v) with
  | V.Scope _ -> V.VarIdSet.singleton (V.id v)
  | V.GlobalScope -> V.VarIdSet.empty


let base_setid_global_vars (v:V.t) : V.VarIdSet.t =
  match (V.scope v) with
  | V.GlobalScope -> V.VarIdSet.singleton (V.id v)
  | V.Scope _ -> V.VarIdSet.empty



(* Functions for all variables *)

let vset_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_setid_all_vars phi


(* Functions for global variables *)

let global_vset_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_setid_global_vars phi


(* Functions for local variables *)

let local_vset_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_setid_local_vars phi



let all_varid_set         = vset_from_int_formula
(*let all_varid_set_literal = vset_from_int_literal *)
let all_global_varid_set  = global_vset_from_int_formula
let all_local_varid_set   = local_vset_from_int_formula

let all_varid phi         = V.VarIdSet.elements (all_varid_set phi)
(*let all_varid_literal l   = V.VarIdSet.elements (all_varid_set_literal l) *)
let all_local_varid phi   = V.VarIdSet.elements (all_local_varid_set phi)
let all_global_varid phi  = V.VarIdSet.elements (all_global_varid_set phi)



(* Base functions for full variables *)

let base_set_all_vars (v:V.t) : V.VarSet.t =
  V.VarSet.singleton v


let base_set_local_vars (v:V.t) : V.VarSet.t =
  if (V.scope v) <> V.GlobalScope && (V.scope v) <> V.Scope "" then
    V.VarSet.singleton v
  else
    V.VarSet.empty


let base_set_global_vars (v:V.t) : V.VarSet.t =
  if (V.scope v) = V.GlobalScope || (V.scope v) = V.Scope "" then
    V.VarSet.singleton v
  else
    V.VarSet.empty



(* Functions for all variables *)

let var_set_from_int_formula (phi:formula) : V.VarSet.t =
  varset_from_int_formula base_set_all_vars phi



(* Functions for global variables *)

let var_global_set_from_int_formula (phi:formula) : V.VarSet.t =
  varset_from_int_formula base_set_global_vars phi


(* Functions for local variables *)

let var_local_set_from_int_formula (phi:formula) : V.VarSet.t =
  varset_from_int_formula base_set_local_vars phi



let all_vars_set         = var_set_from_int_formula
(*let all_vars_set_literal = var_set_from_int_literal*)
let all_global_vars_set  = var_global_set_from_int_formula
let all_local_vars_set   = var_local_set_from_int_formula


let all_vars phi        = V.VarSet.elements (all_vars_set phi)
(*let all_vars_literal l  = V.VarSet.elements (all_vars_set_literal l)*)
let all_global_vars phi = V.VarSet.elements (all_global_vars_set phi)
let all_local_vars phi  = V.VarSet.elements (all_local_vars_set phi)


let filter_var_set (v_set:V.VarSet.t) : V.t list =
  let filtered_set = V.VarSet.fold (fun v s ->
                       V.VarSet.add (V.unparam v) s
                     ) v_set V.VarSet.empty
  in
    V.VarSet.elements filtered_set


let all_global_vars_without_param (phi:formula) : V.t list =
  filter_var_set (all_global_vars_set phi)


let all_local_vars_without_param (phi:formula) : V.t list =
  filter_var_set (all_local_vars_set phi)



(* Primed vars *)

let base_primed_vars (v:V.t) : V.VarIdSet.t =
   if V.is_primed v then
    V.VarIdSet.singleton (V.id v)
  else
    V.VarIdSet.empty


let vset_primed_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_primed_vars phi



(* List of vars *)
let base_list_vars (v:V.t) : V.VarIdSet.t =
  V.VarIdSet.singleton (V.id v)


let vlist_from_int_formula (phi:formula) : V.VarIdSet.t =
  varidset_from_int_formula base_list_vars phi


(* Vocabulary functions *)
let opt_th (th:V.shared_or_local) : ThreadSet.t =
  match th with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


let thset_from (ths:tid list) : ThreadSet.t =
  List.fold_left (fun s t -> ThreadSet.add t s) ThreadSet.empty ths



let voc_fold =
  make_fold (fun _ -> ThreadSet.empty)
            (ThreadSet.union)
            (fun _ _ v -> opt_th (V.parameter v))
  ~tid_f:(fun fs info th ->
      match th with
      | VarTh v -> ThreadSet.add th (opt_th (V.parameter v))
      | _ -> fold_tid fs info th)
  ~atom_f:(fun fs info a ->
      match a with
      | PC (pc,t,_) -> (match t with
                        | V.Shared -> ThreadSet.empty
                        | V.Local x -> ThreadSet.singleton (VarTh x))
      | PCUpdate (pc,t) -> ThreadSet.singleton t
      | PCRange (pc1,pc2,t,_) -> (match t with
                                  | V.Shared -> ThreadSet.empty
                                  | V.Local x -> ThreadSet.singleton (VarTh x))
      | _ -> fold_atom fs info a)


let voc_fs = Formula.make_fold
               Formula.GenericLiteralFold
               (voc_fold.atom_f)
               (fun info -> ThreadSet.empty)
               ThreadSet.union

let voc_from_int_formula (phi:formula) : ThreadSet.t =
  Formula.formula_fold voc_fs () phi


let voc (phi:formula) : tid list =
  ThreadSet.elements (voc_from_int_formula phi)


let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)


let param_map =
  make_map (fun _ pfun v -> V.set_param v (pfun (Some v)))

let param_fs =
  F.make_trans F.GenericLiteralTrans param_map.atom_f


(**********************  Generic Expression Functions  ********************)

let tid_sort : sort = Tid

let tid_var (v:V.t) : tid = VarTh v

let no_tid : tid = NoTid

let to_str (phi:formula) : string = formula_to_str phi

let ineq_tid (t1:tid) (t2:tid) : formula =
  F.atom_to_formula (InEq(TidT t1, TidT t2))

let pc_form (i:int) (scope:V.shared_or_local) (pr:bool) : formula =
  F.atom_to_formula (PC(i,scope,pr))

let gen_fresh_tids (set:ThreadSet.t) (n:int) : ThreadSet.t =
  let gen_cand i = VarTh (build_var ("k_" ^ (string_of_int i))
                           Tid false V.Shared V.GlobalScope) in
  LeapLib.gen_fresh
    set ThreadSet.empty ThreadSet.add ThreadSet.mem gen_cand n

let param (p:V.shared_or_local) (phi:formula) =
  F.formula_trans param_fs (V.param_local_only p) phi
