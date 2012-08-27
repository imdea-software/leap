type term =
    Val  of int
  | Var  of variable
  | Neg  of term
  | Add  of term * term
  | Sub  of term * term
  | Mul  of term * term
and literal =
    Less          of term * term
  | Greater       of term * term
  | LessEq        of term * term
  | GreaterEq     of term * term
  | Eq            of term * term
  | InEq          of term * term
and conjunction_literals =
    ConjTrue
  | ConjFalse    
  | Conjuncts     of literal list
and variable =
  string        * (* Variable name *)
  bool          * (* is primed? *)
  int option    * (* Thread id parameterizing the variable *)
  string option   (* None   -> global var;
                                  Some p -> local var belonging to p *)
type loc = int list (* codification for location. [1;2] = loc_1_2 *)


type location =
  loc                 * (* [1;2] = loc_2_3 *)
  conjunction_literals  (* location initial condition *)

type transition =
  loc                  * (* From location *)
  loc                  * (* To location *)
  int                  * (* Variant See NOTE *)
  conjunction_literals * (* Enabling condition *)
  conjunction_literals * (* Transition effect *)
  variable list          (* Variable list preservation *)


(* NOTE: A single transition may be decomposed into many possible cases.
         As we are working with conjunction of literals, a transition with
         enabling condition p \/ q, for instance, is split into two transitions,
         one with enabling condition p and variant 1, and the other with
         enabling condition q and labeled as variant 2.
*)


type transition_system =
  string          * (* The problem name *)
  variable list   * (* The problem variables *)
  location list   * (* The location list *)
  transition list * (* The main thread transitions *)
  transition list   (* The spaghetti transitions *)

