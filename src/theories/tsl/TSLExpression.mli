
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)



type sort =
    Set
  | Elem
  | Tid
  | Addr
  | Cell
  | SetTh
  | SetElem
  | Path
  | Mem
  | Int
  | AddrArray
  | TidArray
  | Bool
  | Unknown

type var_info_t

module V : Variable.S
  with type sort = sort
  with type info = var_info_t

type term =
    VarT              of V.t
  | SetT              of set
  | ElemT             of elem
  | TidT              of tid
  | AddrT             of addr
  | CellT             of cell
  | SetThT            of setth
  | SetElemT          of setelem
  | PathT             of path
  | MemT              of mem
  | IntT              of integer
  | AddrArrayT        of addrarr
  | TidArrayT         of tidarr
  | VarUpdate         of V.t * tid * term
and eq = term * term
and diseq = term * term
and set =
    VarSet            of V.t
  | EmptySet
  | Singl             of addr
  | Union             of set * set
  | Intr              of set * set
  | Setdiff           of set * set
  | PathToSet         of path
  | AddrToSet         of mem * addr * integer
and tid =
    VarTh             of V.t
  | NoTid
  | CellLockIdAt      of cell * integer
  | TidArrRd         of tidarr * integer
and elem =
    VarElem           of V.t
  | CellData          of cell
  | HavocSkiplistElem
  | LowestElem
  | HighestElem
and addr =
    VarAddr           of V.t
  | Null
  | ArrAt            of cell * integer
  | AddrArrRd         of addrarr * integer
and cell =
    VarCell           of V.t
  | Error
  | MkCell            of elem * addrarr * tidarr * integer
  | CellLockAt        of cell * integer * tid
  | CellUnlockAt      of cell * integer
  | CellAt            of mem * addr
and setth =
    VarSetTh          of V.t
  | EmptySetTh
  | SinglTh           of tid
  | UnionTh           of setth * setth
  | IntrTh            of setth * setth
  | SetdiffTh         of setth * setth
and setelem =
    VarSetElem        of V.t
  | EmptySetElem
  | SinglElem         of elem
  | UnionElem         of setelem * setelem
  | IntrElem          of setelem * setelem
  | SetToElems        of set * mem
  | SetdiffElem       of setelem * setelem
and path =
    VarPath           of V.t
  | Epsilon
  | SimplePath        of addr
  | GetPath           of mem * addr * addr * integer
and mem =
    VarMem            of V.t
  | Update            of mem * addr * cell
and integer =
    IntVal            of int
  | VarInt            of V.t
  | IntNeg            of integer
  | IntAdd            of integer * integer
  | IntSub            of integer * integer
  | IntMul            of integer * integer
  | IntDiv            of integer * integer
  | CellMax           of cell
  | HavocLevel
and addrarr =
  | VarAddrArray      of V.t
  | AddrArrayUp       of addrarr * integer * addr
  | CellArr           of cell
and tidarr =
  | VarTidArray       of V.t
  | TidArrayUp        of tidarr * integer * tid
  | CellTids          of cell
and atom =
    Append            of path * path * path
  | Reach             of mem * addr * addr * integer * path
  | OrderList         of mem * addr * addr
  | Skiplist          of mem * set * integer * addr * addr * setelem
  | In                of addr * set
  | SubsetEq          of set  * set
  | InTh              of tid * setth
  | SubsetEqTh        of setth * setth
  | InElem            of elem * setelem
  | SubsetEqElem      of setelem * setelem
  | Less              of integer * integer
  | Greater           of integer * integer
  | LessEq            of integer * integer
  | GreaterEq         of integer * integer
  | LessElem          of elem * elem
  | GreaterElem       of elem * elem
  | Eq                of eq
  | InEq              of diseq
  | BoolVar           of V.t
  | PC                of int * V.shared_or_local * bool
  | PCUpdate          of int * tid
  | PCRange           of int * int * V.shared_or_local * bool
and literal = atom Formula.literal
and conjunctive_formula = atom Formula.conjunctive_formula
and disjunctive_formula = atom Formula.disjunctive_formula
and formula = atom Formula.formula


type special_op_t =
  | Reachable
  | Addr2Set
  | Path2Set
  | FstLocked
  | Getp
  | Set2Elem
  | ElemOrder
  | OrderedList
  | SkiplistProp


exception WrongType of term

(* CALCULATE SET OF VARS *)
module TermSet : Set.S with type elt = term
module AtomSet : Set.S with type elt = atom
module ThreadSet : Set.S with type elt = tid

val build_var : ?fresh:bool ->
                ?treat_as_pc:bool ->
                V.id ->
                sort ->
                bool ->
                V.shared_or_local ->
                V.procedure_name ->
                V.t

(* returns all variables form a formula *)
val varlist_from_conj           : conjunctive_formula -> V.t list
val varlist                     : formula -> V.t list

val varidlist_of_sort_from_conj : conjunctive_formula -> sort -> V.id list
val varidlist_of_sort           : formula -> sort -> V.id list

val varset_from_conj              : conjunctive_formula -> V.VarSet.t
val varset                        : formula -> V.VarSet.t
val varset_instances_from_conj    : conjunctive_formula -> V.VarSet.t
val varset_instances              : formula -> V.VarSet.t
val varset_of_sort_from_literal   : literal -> sort -> V.VarSet.t
val varset_of_sort_from_conj      : conjunctive_formula -> sort -> V.VarSet.t
val varset_of_sort                : formula -> sort -> V.VarSet.t
val varset_instances_of_sort_from_conj : conjunctive_formula -> sort -> V.VarSet.t
val varset_instances_of_sort           : formula -> sort -> V.VarSet.t

val termset                     : formula -> TermSet.t
val termset_from_conj           : conjunctive_formula -> TermSet.t
val filter_termset_with_sort    : TermSet.t -> sort -> TermSet.t

val voc_term : term -> ThreadSet.t
val voc : formula -> ThreadSet.t
val voc_conjunctive_formula : conjunctive_formula -> ThreadSet.t
val unprimed_voc : formula -> ThreadSet.t

val voc_to_var : tid -> V.t


(* PRETTY_PRINTERS *)
val atom_to_str     : atom    -> string
val literal_to_str  : literal -> string
val conjunctive_formula_to_str : conjunctive_formula -> string
val term_to_str     : term   -> string
val addr_to_str     : addr   -> string
val cell_to_str     : cell   -> string
val elem_to_str     : elem   -> string
val tid_to_str      : tid   -> string
val mem_to_str      : mem    -> string
val int_to_str      : integer -> string
val path_to_str     : path   -> string
val set_to_str      : set    -> string
val setth_to_str    : setth  -> string
val addrarr_to_str  : addrarr -> string
val tidarr_to_str   : tidarr  -> string
val formula_to_str  : formula -> string
val sort_to_str : sort -> string


val print_formula : formula -> unit
val print_conjunctive_formula: conjunctive_formula -> unit
val print_atom    : atom    -> unit
val print_literal : literal -> unit
val print_addr  : addr  -> unit
val print_cell  : cell  -> unit
val print_elem  : elem  -> unit
val print_tid  : tid  -> unit
val print_mem   : mem   -> unit
val print_path  : path  -> unit
val print_set   : set   -> unit
val print_setth : setth -> unit
  
val required_sorts : formula -> sort list
val special_ops : formula -> special_op_t list

val normalize : formula -> formula
(** [normalize phi] returns a new formula that is the normalization of
    [phi], adding fresh variables if required *)

val replace_terms_literal : (term, term) Hashtbl.t -> literal -> literal

val replace_terms : (term, term) Hashtbl.t ->
                    formula ->
                    formula


