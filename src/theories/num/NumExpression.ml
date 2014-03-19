open LeapLib

module E = Expression
module F = Formula
module EE = ExtendedExpression

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

type tid_subst_t = (tid, tid) Hashtbl.t


exception NotConjunctiveExpr of formula
exception Not_tid_var of tid
exception UnsupportedNumExpr of string
exception UnsupportedSort of string
exception No_variable_term of string
exception No_sort_for_term of string

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
  | Int  -> "int"
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

and term_to_str (t:term) : string =
  generic_int_term_to_str no_parenthesis t

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





let priming_variable (pr:bool)
                     (prime_set:V.VarSet.t option)
                     (v:V.t) : V.t =
  let v' = if pr then V.prime v else V.unprime v in
  match prime_set with
  | None   -> v'
(* DO NOT ERASE: This may be needed!!!! *)
  | Some s -> if (V.VarSet.mem (V.set_param v V.Shared) s ||
                  V.VarSet.mem (v) s                  ) then v' else v
(*      | Some s -> if V.VarSet.mem v s then v' else v *)




let prime_map =
  make_map (fun _ (pr,prime_set) v ->
              let v' = if pr then V.prime v else V.unprime v in
              match prime_set with
              | None -> v'
              | Some s -> if (V.VarSet.mem (V.set_param v V.Shared) s ||
                              V.VarSet.mem v s) then v' else v)

let prime_fs =
  F.make_trans F.GenericLiteralTrans prime_map.atom_f


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

let voc (phi:formula) : ThreadSet.t =
  Formula.formula_fold voc_fs () phi


let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)


let param_map =
  make_map (fun _ pfun v -> V.set_param v (pfun (Some v)))

let param_fs =
  F.make_trans F.GenericLiteralTrans param_map.atom_f


let canonical_map =
  make_map (fun _ _ v -> v)
  ~atom_f:(fun fs info a ->
        match a with
        | Eq (x,y) -> if compare x y > 0 then
                        Eq(fs.term_f fs info y, fs.term_f fs info x) else a
        | InEq (x,y) -> if compare x y > 0 then
                          InEq(fs.term_f fs info y, fs.term_f fs info x) else a
        | _ -> map_atom fs info a)
  ~int_f:(fun fs info i ->
        match i with
        | Add(x,y) -> if compare x y > 0 then
                        Add (fs.int_f fs info y, fs.int_f fs info x) else i
        | Mul(x,y) -> if compare x y > 0 then
                        Mul (fs.int_f fs info y, fs.int_f fs info x) else i
        | _ -> map_int fs info i)
  ~set_f:(fun fs info s ->
        match s with
        | Union(x,y) -> if compare x y > 0 then
                          Union (fs.set_f fs info y, fs.set_f fs info x) else s
        | Intr(x,y) -> if compare x y > 0 then
                         Intr (fs.set_f fs info y, fs.set_f fs info x) else s
        | _ -> map_set fs info s)




(* Conversion from Expression to NumExpression *)

(* Sort conversion *)
let sort_to_int_sort (s:E.sort) : sort =
  match s with
    E.Int    -> Int
  | E.SetInt -> Set
  | E.Tid    -> Tid
  | _        -> raise(UnsupportedSort(E.sort_to_str s))


let rec variable_to_int_variable (v:E.V.t) : V.t =
  build_var (E.V.id v)
               (sort_to_int_sort (E.V.sort v))
               (E.V.is_primed v)
               (shared_to_int_shared (E.V.parameter v))
               (scope_to_int_scope (E.V.scope v))


and shared_to_int_shared (th:E.V.shared_or_local) : V.shared_or_local =
  match th with
  | E.V.Shared -> V.Shared
  | E.V.Local t -> V.Local (variable_to_int_variable t)


and scope_to_int_scope (p:E.V.procedure_name) : V.procedure_name =
  match p with
  | E.V.GlobalScope -> V.GlobalScope
  | E.V.Scope proc -> V.Scope proc



let rec tid_to_int_tid (th:E.tid) : tid =
  match th with
  | E.VarTh t -> VarTh (variable_to_int_variable t)
  | E.NoTid -> NoTid
  | _ -> raise(UnsupportedNumExpr(E.tid_to_str th))


and array_to_funterm (x:E.arrays) : fun_term =
  match x with
    E.VarArray v -> FunVar (variable_to_int_variable v)
  | E.ArrayUp (a,th,E.Term (E.IntT i)) ->
      FunUpd (array_to_funterm a,
      tid_to_int_tid th,
      IntT (integer_to_int_integer i))
  | E.ArrayUp (a,th,E.Term (E.SetIntT i)) ->
      FunUpd (array_to_funterm a,
      tid_to_int_tid th,
      SetT (set_to_int_set i))
  | _ -> raise(UnsupportedNumExpr(E.arrays_to_str x))


and set_to_int_set (s:E.setint) : set =
  let toset = set_to_int_set in
  match s with
    E.VarSetInt v       -> VarSet (variable_to_int_variable v)
  | E.EmptySetInt       -> EmptySet
  | E.SinglInt i        -> Singl (integer_to_int_integer i)
  | E.UnionInt(s1,s2)   -> Union (toset s1, toset s2)
  | E.IntrInt(s1,s2)    -> Intr (toset s1, toset s2)
  | E.SetdiffInt(s1,s2) -> Diff (toset s1, toset s2)
  | _ -> raise(UnsupportedNumExpr(E.setint_to_str s))


and integer_to_int_integer (t:E.integer) : integer =
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
    match t with
      E.IntVal(i)       -> Val(i)
    | E.VarInt v        -> Var(variable_to_int_variable v)
    | E.IntNeg(i)       -> Neg(toint i)
    | E.IntAdd(x,y)     -> Add(toint x,toint y)
    | E.IntSub(x,y)     -> Sub(toint x,toint y)
    | E.IntMul(x,y)     -> Mul(toint x,toint y)
    | E.IntDiv(x,y)     -> Div(toint x,toint y)
    | E.IntArrayRd(a,i) -> raise(UnsupportedNumExpr(E.integer_to_str t))
    | E.IntSetMin(s)    -> SetMin (toset s)
    | E.IntSetMax(s)    -> SetMax (toset s)
    | E.CellMax(c)      -> raise(UnsupportedNumExpr(E.integer_to_str t))
    | E.HavocLevel      -> raise(UnsupportedNumExpr(E.integer_to_str t))


and atom_to_int_atom (a:E.atom) : atom =
  let totid = tid_to_int_tid in
  let toint = integer_to_int_integer in
  let toset = set_to_int_set in
    match a with
    | E.Less(x,y)     -> Less(toint x,toint y)
    | E.Greater(x,y)  -> Greater(toint x,toint y)
    | E.LessEq(x,y)   -> LessEq(toint x,toint y)
    | E.GreaterEq(x,y)-> GreaterEq(toint x,toint y)
    | E.LessTid(x,y)  -> LessTid(totid x, totid y)
    | E.Eq(E.TidT x,E.TidT y)      -> Eq(TidT (totid x),
                                            TidT (totid y))
    | E.InEq(E.TidT x,E.TidT y)    -> Eq(TidT (totid x),
                                            TidT (totid y))
    | E.Eq(E.ArrayT x, E.ArrayT y)   -> Eq (FuntermT (array_to_funterm x),
                                               FuntermT (array_to_funterm y))
    | E.InEq(E.ArrayT x, E.ArrayT y) -> InEq (FuntermT (array_to_funterm x),
                                                 FuntermT (array_to_funterm y))
    | E.Eq(E.IntT x, E.IntT y)       -> Eq(IntT (toint x),
                                              IntT (toint y))
    | E.Eq(E.SetIntT x, E.SetIntT y) -> Eq(SetT (toset x),
                                              SetT (toset y))
    | E.InEq(E.IntT x, E.IntT y)     -> InEq(IntT(toint x),
                                                IntT(toint y))
    | E.InEq(E.SetIntT x, E.SetIntT y) -> InEq(SetT(toset x),
                                                  SetT(toset y))
    | E.PC(i,th,pr)    -> PC (i,shared_to_int_shared th,pr)
    | E.PCUpdate(i,th) -> PCUpdate (i,totid th)
    | E.PCRange(i,j,th,pr) -> PCRange (i,j,shared_to_int_shared th,pr)
    | _ -> raise(UnsupportedNumExpr(E.atom_to_str a))

and formula_to_int_formula (phi:E.formula) : formula =
  Formula.formula_conv atom_to_int_atom phi


(* Integer implications *)
let integer_implies ((v,k):V.t * int) (l:literal) : bool =
  let same (v1,k1) (v2,k2) = (V.same_var v1 v2) && (k1=k2) in
  match l with
  | (* v=k -> v2=k2 *)
      F.Atom(Eq(IntT(Var v2),IntT(Val k2))) -> same (v,k) (v2,k2)
  | (* v=k -> k2=v2 *)
      F.Atom(Eq(IntT(Val k2 ),IntT(Var v2))) -> same (v,k) (v2,k2)
  | (* v=k -> k2<v2 *)
      F.Atom(Less(Val k2, Var v2)) -> (V.same_var v v2) && (k > k2)
  | (* v=k -> v2>k2 *)
      F.Atom(Greater(Var v2, Val k2)) -> (V.same_var v v2) && (k > k2)
  | (* v=k -> v2<k2 *)
      F.Atom(Less(Var v2, Val k2)) -> (V.same_var v v2) && (k < k2)
  | (* v=k -> k2>v2 *)
      F.Atom(Greater(Val k2, Var v2)) -> (V.same_var v v2) && (k < k2)
  | (* v=k -> k2<=v2 *)
      F.Atom(LessEq(Val k2 ,Var v2)) -> (V.same_var v v2) && (k >= k2)
  | (* v=k -> v2>=k2 *)
      F.Atom(GreaterEq(Var v2 ,Val k2)) -> (V.same_var v v2) && (k >= k2)
  | (* v=k -> v2<=k2 *)
      F.Atom(LessEq(Var v2,Val k2)) -> (V.same_var v v2) && (k <= k2)
  | (* v=k -> k2>=v2 *)
      F.Atom(GreaterEq(Val k2 ,Var v2)) -> (V.same_var v v2) && (k <= k2)
  | _ -> false


let integer_implies_neg ((v,k):V.t * int) (l:literal) : bool =
  match l with
  |  (* v=k -> v2=k2 *)
      F.Atom(Eq(IntT(Var v2),IntT(Val k2))) -> V.same_var v v2 && k!=k2
  | (* v=k -> k2=v2 *)
      F.Atom(Eq(IntT(Val k2),IntT(Var v2))) -> V.same_var v v2 && k!=k2
  | (* v=k -> k2<v2 *)
      F.Atom(Less(Val k2,Var v2)) -> (V.same_var v v2) && not (k > k2)
  | (* v=k -> v2>k2 *)
      F.Atom(Greater(Var v2, Val k2)) -> (V.same_var v v2) && not (k > k2)
  | (* v=k -> v2<k2 *)
      F.Atom(Less(Var v2, Val k2)) -> (V.same_var v v2) && not (k < k2)
  | (* v=k -> k2>v2 *)
      F.Atom(Greater(Val k2, Var v2)) -> (V.same_var v v2) && not (k < k2)
  | (* v=k -> k2<=v2 *)
      F.Atom(LessEq(Val k2, Var v2)) -> (V.same_var v v2) && not (k >= k2)
  | (* v=k -> v2>=k2 *)
      F.Atom(GreaterEq(Var v2, Val k2)) -> (V.same_var v v2) && not (k >= k2)
  | (* v=k -> v2<=k2 *)
      F.Atom(LessEq(Var v2, Val k2)) -> (V.same_var v v2) && not (k <= k2)
  | (* v=k -> k2>=v2 *)
      F.Atom(GreaterEq(Val k2, Var v2)) -> (V.same_var v v2) && not (k <= k2)
  | _ -> false

(* Matching *)
let defVar = V.build_global "" Int ()

let is_int_val_assign (phi:formula) : (bool * V.t * int) =
  match phi with
  | F.Literal (F.Atom (Eq (IntT (Var v), IntT (Val i))))
  | F.Literal (F.Atom (Eq (IntT (Val i), IntT (Var v)))) -> (true, v, i)
  | _ -> (false, defVar, -1)


let is_var_update (phi:formula) : (bool * V.t * tid) =
  match phi with
  | F.Literal (F.Atom (Eq (FuntermT (FunVar v), FuntermT (FunUpd (_,i,_))))) ->
      (true, v, i)
  | _ -> (false, defVar, NoTid)


let is_pc_update (phi:formula) : (bool * int * tid) =
  match phi with
  | F.Or (F.Literal (F.Atom (PCUpdate (pc,i))), _)
  | F.Literal (F.Atom (PCUpdate (pc,i))) -> (true, pc, i)
  | _ -> (false, 0, NoTid)


let build_pc_var (pr:bool) (th:V.shared_or_local) : V.t =
  let pr_str = if pr then "_prime" else "" in
  let th_str = match th with
               | V.Shared-> ""
               | V.Local t -> "_" ^ (V.to_simple_str t)
  in
    V.build_global ("pc" ^ pr_str ^ th_str) Int ()


let is_pc_var (v:V.t) : bool =
  String.sub (V.id v) 0 3 = "pc_"


let prime_modified (rho:formula) (phi:formula) : formula =
  let base_f = fun v -> if V.is_primed v then
                          V.VarSet.singleton v
                        else V.VarSet.empty in
  let rec analyze_fs () = Formula.make_fold
                            Formula.GenericLiteralFold
                            (fun info a -> analyze_atom a)
                            (fun info -> V.VarSet.empty)
                            (V.VarSet.union)
  and analyze_formula (phi:formula) : V.VarSet.t =
    Formula.formula_fold (analyze_fs()) () phi
  and analyze_atom (a:atom) : V.VarSet.t =
    match a with
    | Eq (FuntermT (FunVar v), FuntermT (FunUpd (aa,t,e)))
    | Eq (FuntermT (FunUpd (aa,t,e)), FuntermT (FunVar v)) ->
        V.VarSet.singleton (V.set_param (V.unprime v) (V.Local (voc_to_var t)))
    | _ -> varset_fold.atom_f base_f a in
  let p_set = V.VarSet.fold (fun v set ->
                 V.VarSet.add (V.unprime v) set
               ) (analyze_formula rho) V.VarSet.empty in
    F.formula_trans prime_fs (true, Some p_set) phi


let to_plain_shared_or_local (ops:V.t EE.fol_ops_t)
                             (th:V.shared_or_local) : V.shared_or_local =
  match th with
  | V.Shared  -> V.Shared
  | V.Local t -> V.Local (ops.EE.fol_var t)


let plain_map =
  make_map (fun _ ops v -> ops.EE.fol_var v)
  ~atom_f:(fun fs ops a ->
      match a with
      | PC (pc,th,p) -> if ops.EE.fol_pc then
                          let pc_var = build_pc_var p (to_plain_shared_or_local ops th) in
                            Eq(IntT(Var pc_var),IntT(Val pc))
                        else
                            PC (pc,to_plain_shared_or_local ops th,p)
      | PCUpdate (pc,t) -> if ops.EE.fol_pc then
                             let pc_prime_var = build_pc_var true (V.Local (voc_to_var (fs.tid_f fs ops t))) in
                               Eq (IntT (Var pc_prime_var), IntT (Val pc))
                             else
                               PCUpdate (pc, fs.tid_f fs ops t)
      | PCRange (pc1,pc2,th,p) -> if ops.EE.fol_pc then
                                    (assert false)
                                  else
                                    PCRange (pc1,pc2,to_plain_shared_or_local ops th,p)
      | _ -> map_atom fs ops a)


let plain_fs =
  F.make_trans F.GenericLiteralTrans plain_map.atom_f


let var_to_term (v:V.t) : term =
  match V.sort v with
  | Set -> SetT(VarSet v)
  | Tid -> TidT(VarTh  v)
  | Int -> IntT(Var    v)



let term_to_var (t:term) : V.t =
  match t with
  | SetT    (VarSet v) -> V.set_sort v Set
  | TidT    (VarTh  v) -> V.set_sort v Tid
  | IntT    (Var    v) -> V.set_sort v Int
  | _                  -> raise(No_variable_term(term_to_str t))


let term_sort (t:term) : sort =
  match t with
  | SetT _     -> Set
  | TidT _     -> Tid
  | IntT _     -> Int
  | FuntermT _ -> raise(No_sort_for_term (term_to_str t))


let rec to_plain_formula (ops:V.t EE.fol_ops_t) (phi:formula) : formula =
  match phi with
  | F.True           -> F.True
  | F.False          -> F.False
  | F.And(f1,f2)     -> F.And(to_plain_formula ops f1, to_plain_formula ops f2)
  | F.Or(f1,f2)      -> F.Or(to_plain_formula ops f1, to_plain_formula ops f2)
  | F.Not(f)         -> F.Not(to_plain_formula ops f)
  | F.Implies(f1,f2) -> F.Implies(to_plain_formula ops f1, to_plain_formula ops f2)
  | F.Iff (f1,f2)    -> F.Iff(to_plain_formula ops f1, to_plain_formula ops f2)
  | F.Literal l      -> begin
                        let conv_lit (lit:literal) : formula =
                          begin
                            match lit with
                              (* Update of a local variable of a parametrized system *)
                            | F.Atom(Eq(v',FuntermT(FunUpd(arr,t,ter))))
                            | F.Atom(Eq(FuntermT(FunUpd(arr,t,ter)),v'))
                            | F.NegAtom(InEq(v',FuntermT(FunUpd(arr,t,ter))))
                            | F.NegAtom(InEq(FuntermT(FunUpd(arr,t,ter)),v')) ->
                                let new_v' = V.prime (V.set_param (term_to_var v')
                                                (V.Local (voc_to_var t))) in
                                let s = term_sort ter in
                                let as_term = plain_map.term_f ops (var_to_term
                                                  (V.set_sort new_v' s)) in
                                  F.atom_to_formula (Eq (as_term, ter))
                            | _ -> F.Literal(F.literal_trans plain_fs ops lit)
                          end in
                        if ops.EE.fol_pc then begin
                          match l with
                          | F.Atom(PCRange(pc1,pc2,th,p)) ->
                              let pc_var = build_pc_var p (to_plain_shared_or_local ops th) in
                                F.And (F.atom_to_formula (LessEq (Val pc1, Var pc_var)),
                                       F.atom_to_formula (LessEq (Var pc_var, Val pc2)))
                          | F.NegAtom(PCRange(pc1,pc2,th,p)) ->
                              let pc_var = build_pc_var p (to_plain_shared_or_local ops th) in
                                F.Or (F.atom_to_formula (Less (Var pc_var, Val pc1)),
                                      F.atom_to_formula (Less (Val pc2, Var pc_var)))
                          | _ -> conv_lit l
                        end else
                          conv_lit l
                      end


let substVars_map =
  make_map (fun _ subs v -> V.subst subs v)

let substVars_fs =
  F.make_trans Formula.GenericLiteralTrans (substVars_map.atom_f)


let subst_shared_or_local (subst: tid_subst_t)
                          (th:V.shared_or_local) : V.shared_or_local =
  match th with
  | V.Shared -> V.Shared
  | V.Local t -> V.Local (try (voc_to_var (Hashtbl.find subst (VarTh t))) with _ -> t)


let substTid_map =
  make_map (fun _ subs v -> V.set_param v (subst_shared_or_local subs (V.parameter v)))
  ~atom_f:(fun fs subs a ->
      match a with
      | PC (pc,t,primed)           -> PC (pc, subst_shared_or_local subs t,primed)
      | PCRange (pc1,pc2,t,primed) -> PCRange (pc1, pc2, subst_shared_or_local subs t, primed)
      | _ -> map_atom fs subs a)

let substTid_fs =
  F.make_trans F.GenericLiteralTrans substTid_map.atom_f


(**********************  Generic Expression Functions  ********************)

include DefaultExpression.Make(V)
        (struct
          let build_var id s pr sh sc = build_var id s pr sh sc ()
          let plain_formula = F.formula_trans plain_fs
         end)

let cast (phi:Expression.formula) : formula =
  formula_to_int_formula phi

let cast_var (v:Expression.V.t) : V.t =
  variable_to_int_variable v

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

let canonical (a:atom) : atom =
  canonical_map.atom_f () a

(*module Ex = ExtendedExpression.Make (struct type atom_t = atom end) *)
(*include ExtendedExpression *)


(*let plain = ExtendedExpression.plain *)
(*
*)

let defInfo () : unit = ()

let unprime_tid (t:tid) : tid =
  prime_map.tid_f (false,None) t

let subst_vars (subs:V.subst_t) (phi:formula) : formula =
  F.formula_trans substVars_fs subs phi

let subst_tid (subs:tid_subst_t) (phi:formula) : formula =
  F.formula_trans substTid_fs subs phi

let subst_domain (subst:tid_subst_t) : ThreadSet.t =
  Hashtbl.fold (fun d _ set -> ThreadSet.add d set) subst ThreadSet.empty

let subst_codomain (subst:tid_subst_t) : ThreadSet.t =
  Hashtbl.fold (fun _ r set -> ThreadSet.add r set) subst ThreadSet.empty

let subst_domain_in (tid_set:ThreadSet.t) (subst:tid_subst_t) : bool =
  Hashtbl.fold (fun d _ b -> if (not b) then false else ThreadSet.mem d tid_set) subst true

let subst_codomain_in (tid_set:ThreadSet.t) (subst:tid_subst_t) : bool =
  Hashtbl.fold (fun _ r b -> if (not b) then
                               false
                             else
                               ThreadSet.mem r tid_set) subst true


let subst_to_str (sub:tid_subst_t) : string =
  "{" ^ (Hashtbl.fold (fun i j str -> str^(tid_to_str j)^"<-"^(tid_to_str i)^";") sub "") ^ "}"


let new_tid_subst (info:(tid * tid) list) : tid_subst_t =
  let subs = Hashtbl.create (List.length info) in
  List.iter (fun (x,y) ->
    Hashtbl.add subs x y
  ) info;
  subs


let new_comb_subst (th_domain:ThreadSet.t)
                   (th_range:ThreadSet.t) : tid_subst_t list =
  let domain_list = ThreadSet.elements th_domain in
  let range_list = ThreadSet.elements th_range in
  let comb_th_domain = choose_range domain_list 1 (List.length domain_list)
  in
    List.flatten $
      List.map (fun xs ->
        let ln = List.length xs in
        let assign_comb = comb range_list ln in
        List.map (fun ys ->
          new_tid_subst (List.combine xs ys)
        ) assign_comb
      ) comb_th_domain
