
(**************************)
(**  Formula definition  **)
(**************************)

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


(*************************)
(**  Folding datatypes  **)
(*************************)

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


(*****************************)
(**  Translation datatypes  **)
(*****************************)

type ('atom, 'info) trans_functions_t =
  {
    mutable literal_f : 'info -> 'atom literal -> 'atom literal;
    atom_f : 'info -> 'atom -> 'atom;
  }


type ('info, 'atom) trans_literal_op_t =
  | GenericLiteralTrans
  | ThisLiteralTrans of ('info -> 'atom literal ->'atom literal)


(*************************)
(**  Folding functions  **)
(*************************)
val formula_fold : ('atom, 'info, 'a) functions_t ->
                   'info ->
                   'atom formula ->
                   'a

val conjunctive_formula_fold : ('atom, 'info, 'a) functions_t ->
                               'info ->
                               'atom conjunctive_formula ->
                               'a

val disjunctive_formula_fold : ('atom, 'info, 'a) functions_t ->
                               'info ->
                               'atom disjunctive_formula ->
                               'a

val literal_fold : ('atom, 'info, 'a) functions_t ->
                   'info ->
                   'atom literal -> 'a


val make_fold : ('info, 'atom, 'a) literal_op_t ->
                ('info -> 'atom -> 'a) ->
                ('info -> 'a) ->
                ('a -> 'a -> 'a) ->
                ('atom, 'info, 'a) functions_t


(*****************************)
(**  Translation functions  **)
(*****************************)

val formula_trans : ('atom, 'info) trans_functions_t ->
                    'info ->
                    'atom formula ->
                    'atom formula

val conjunctive_formula_trans : ('atom, 'info) trans_functions_t ->
                                'info ->
                                'atom conjunctive_formula ->
                                'atom conjunctive_formula

val disjunctive_formula_trans : ('atom, 'info) trans_functions_t ->
                                'info ->
                                'atom disjunctive_formula ->
                                'atom disjunctive_formula

val literal_trans : ('atom, 'info) trans_functions_t ->
                    'info ->
                    'atom literal ->
                    'atom literal

val make_trans : ('info, 'atom) trans_literal_op_t ->
                 ('info -> 'atom -> 'atom) ->
                 ('atom, 'info) trans_functions_t

(**************************)
(**  Formula conversion  **)
(**************************)

val formula_conv : ('a -> 'b) -> 'a formula -> 'b formula

(**************************)
(**  Formula operations  **)
(**************************)


val conj_list : 'atom formula list -> 'atom formula
val disj_list : 'atom formula list -> 'atom formula

val conj_literals : 'atom literal list -> 'atom formula
val disj_literals : 'atom literal list -> 'atom formula

val to_conj_literals : 'atom formula -> 'atom literal list
val to_disj_literals : 'atom formula -> 'atom literal list

val to_conj_list : 'atom formula -> 'atom formula list
val to_disj_list : 'atom formula -> 'atom formula list

val split_conj : 'atom formula -> 'atom formula list

val nnf : 'atom formula -> 'atom formula
val dnf : 'atom formula -> 'atom conjunctive_formula list
val cnf : 'atom formula -> 'atom disjunctive_formula list

val conjunctive_to_formula : 'atom conjunctive_formula -> 'atom formula
val disjunctive_to_formula : 'atom disjunctive_formula -> 'atom formula

val conjunctive_list_to_formula_list : 'atom conjunctive_formula list ->
                                       'atom formula list list
val disjunctive_list_to_formula_list : 'atom disjunctive_formula list ->
                                       'atom formula list list


val cleanup_conj : 'atom conjunctive_formula -> 'atom conjunctive_formula
val cleanup_disj : 'atom disjunctive_formula -> 'atom disjunctive_formula
val cleanup : 'atom formula -> 'atom formula
val cleanup_dups : 'atom formula list -> 'atom formula list

val combine_conjunctive : 'atom conjunctive_formula ->
                          'atom conjunctive_formula -> 'atom conjunctive_formula
val combine_conjunctive_list : 'atom conjunctive_formula list ->
                               'atom conjunctive_formula

val atom_to_formula : 'atom -> 'atom formula
val negatom_to_formula : 'atom -> 'atom formula

val is_conjunctive : 'atom formula -> bool


(***********************)
(**  Pretty printers  **)
(***********************)

val literal_to_str : ('atom -> string) -> 'atom literal -> string
val conjunctive_formula_to_str : ('atom -> string) -> 'atom conjunctive_formula -> string
val disjunctive_formula_to_str : ('atom -> string) -> 'atom disjunctive_formula -> string
val formula_to_str : ('atom -> string) -> 'atom formula -> string
