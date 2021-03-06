
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


open Printf
open LeapLib


module E = Expression
module F = Formula


(* Statement declaration *)
type st_info_t = {
  (** Current statement position *)
  pos                     : E.pc_t;
  (** Next statement position *)
  mutable next_pos        : E.pc_t;
  (** Position where to jump if statement was a conditional and
      the condition is not satisfied *)
  mutable else_pos        : E.pc_t;
  (** Position where the invoked procedure begins in case of a call statement *)
  mutable call_pos        : E.pc_t option;
  (** Optional next positions in case of a non-deterministic choice *)
  mutable opt_pos         : E.pc_t list;
  (** Positions from where a procedure has been invoked *)
  mutable called_from_pos : E.pc_t list;
  (** Positions where to return after a return in a procedure *)
  mutable return_pos      : E.pc_t list;
  }

type varId = string

type unit_op = Lock | Unlock

type procedure_name = GlobalScope | Scope of string

(* Expression representation in program statements *)

type variable =
  {
            id        : varId          ;
            sort      : E.sort         ;
            scope     : procedure_name ;
            nature    : E.var_nature   ;
  }

type term =
    VarT          of variable
  | SetT          of set
  | ElemT         of elem
  | TidT          of tid
  | AddrT         of addr
  | CellT         of cell
  | SetThT        of setth
  | SetIntT       of setint
  | SetElemT      of setelem
  | SetPairT      of setpair
  | PathT         of path
  | MemT          of mem
  | IntT          of integer
  | PairT         of pair
  | ArrayT        of arrays
  | AddrArrayT    of addrarr
  | TidArrayT     of tidarr
  | BucketArrayT  of bucketarr
  | MarkT         of mark
  | BucketT       of bucket
  | LockT         of lock
  | LockArrayT    of lockarr

and eq =          term * term

and diseq =       term * term

and arrays =
    VarArray      of variable
  | ArrayUp       of arrays * tid * expr_t

and addrarr =
  | VarAddrArray  of variable
  | AddrArrayUp   of addrarr * integer * addr

and tidarr =
  | VarTidArray   of variable
  | TidArrayUp    of tidarr * integer * tid

and bucketarr =
    | VarBucketArray of variable
    | BucketArrayUp  of bucketarr * integer * bucket

and integer =
    IntVal        of int
  | VarInt        of variable
  | IntNeg        of integer
  | IntAdd        of integer * integer
  | IntSub        of integer * integer
  | IntMul        of integer * integer
  | IntDiv        of integer * integer
  | IntMod        of integer * integer
  | IntArrayRd    of arrays * tid
  | IntSetMin     of setint
  | IntSetMax     of setint
  | HavocLevel
  | HashCode      of elem
  | PairInt       of pair

and pair =
    VarPair       of variable
  | IntTidPair    of integer * tid
  | SetPairMin    of setpair
  | SetPairMax    of setpair
  | PairArrayRd   of arrays * tid

and set =
    VarSet        of variable
  | EmptySet
  | Singl         of addr
  | Union         of set * set
  | Intr          of set * set
  | Setdiff       of set * set
  | PathToSet     of path
  | AddrToSet     of mem * addr
  | AddrToSetAt   of mem * addr * integer
  | SetArrayRd    of arrays * tid
  | BucketRegion  of bucket

and tid =
  | VarTh           of variable
  | NoTid
  | CellLockId      of cell
  | CellLockIdAt    of cell * integer
  | TidArrayRd      of arrays * tid
  | PointerLockid   of addr
  | PointerLockidAt of addr * integer
  | TidArrRd        of tidarr * integer
  | PairTid         of pair
  | BucketTid       of bucket
  | LockId          of lock

and lock =
    VarLock       of variable
  | LLock         of lock * tid
  | LUnlock       of lock
  | LockArrRd     of lockarr * integer

and lockarr =
  | VarLockArray  of variable
  | LockArrayUp   of lockarr * integer * lock

and elem =
    VarElem           of variable
  | CellData          of cell
  | ElemArrayRd       of arrays * tid
  | PointerData       of addr
  | HavocListElem
  | HavocSkiplistElem
  | LowestElem
  | HighestElem

and addr =
  | VarAddr       of variable
  | Null
  | Next          of cell
  | NextAt        of cell * integer
  | ArrAt         of cell * integer
  | FirstLocked   of mem * path
  | LastLocked    of mem * path
  | AddrArrayRd   of arrays * tid
  | Malloc        of elem * addr * tid
  | MallocSL      of elem * integer
  | MallocSLK     of elem * integer
  | PointerNext   of addr
  | PointerNextAt of addr * integer
  | PointerArrAt  of addr * integer
  | AddrArrRd     of addrarr * integer
  | BucketInit    of bucket
  | BucketEnd     of bucket

and cell =
    VarCell       of variable
  | Error
  | MkCell        of elem * addr * tid
  | MkCellMark    of elem * addr * tid * mark
  | MkSLKCell     of elem * addr list * tid list
  | MkSLCell      of elem * addrarr * tidarr * integer
  | CellLock      of cell
  | CellUnlock    of cell
  | CellLockAt    of cell * integer
  | CellUnlockAt  of cell * integer
  | CellAt        of mem * addr
  | CellArrayRd   of arrays * tid

and mark =
    VarMark       of variable
  | MarkTrue
  | MarkFalse
  | Marked        of cell
  | PointerMarked of addr

and bucket =
    VarBucket     of variable
  | MkBucket      of addr * addr * set * tid
  | BucketArrRd   of bucketarr * integer

and setth =
    VarSetTh      of variable
  | EmptySetTh
  | SinglTh       of tid
  | UnionTh       of setth * setth
  | IntrTh        of setth * setth
  | SetdiffTh     of setth * setth
  | SetThArrayRd  of arrays * tid

and setint =
    VarSetInt     of variable
  | EmptySetInt
  | SinglInt      of integer
  | UnionInt      of setint * setint
  | IntrInt       of setint * setint
  | SetdiffInt    of setint * setint
  | SetIntArrayRd of arrays * tid

and setelem =
    VarSetElem     of variable
  | EmptySetElem
  | SinglElem      of elem
  | UnionElem      of setelem * setelem
  | IntrElem       of setelem * setelem
  | SetdiffElem    of setelem * setelem
  | SetToElems     of set * mem
  | SetElemArrayRd of arrays * tid

and setpair =
    VarSetPair     of variable
  | EmptySetPair
  | SinglPair      of pair
  | UnionPair      of setpair * setpair
  | IntrPair       of setpair * setpair
  | SetdiffPair    of setpair * setpair
  | SetPairArrayRd of arrays * tid

and path =
    VarPath       of variable
  | Epsilon
  | SimplePath    of addr
  | GetPath       of mem * addr * addr
  | PathArrayRd   of arrays * tid

and mem =
    VarMem        of variable
  | Update        of mem * addr * cell
  | MemArrayRd    of arrays * tid

and atom =
    Append        of path * path * path
  | Reach         of mem * addr * addr * path
  | OrderList     of mem * addr * addr
  | Skiplist      of mem * set * integer * addr * addr * setelem
  | Hashtbl       of mem * set * setelem * bucketarr * integer
  | In            of addr * set
  | SubsetEq      of set * set
  | InTh          of tid * setth
  | SubsetEqTh    of setth * setth
  | InInt         of integer * setint
  | SubsetEqInt   of setint * setint
  | InElem        of elem * setelem
  | SubsetEqElem  of setelem * setelem
  | InPair        of pair * setpair
  | SubsetEqPair  of setpair * setpair
  | Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | LessElem      of elem * elem
  | GreaterElem   of elem * elem
  | Eq            of eq
  | InEq          of diseq
  | BoolVar       of variable
  | BoolArrayRd   of arrays * tid

and boolean =
  atom F.formula


and expr_t =
    Term          of term
  | Formula       of boolean


type unit_operation =
    UnitLock      of addr
  | UnitUnlock    of addr
  | UnitLockAt    of addr * integer
  | UnitUnlockAt  of addr * integer


type statement_t =
    StSkip of
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAssert of
      boolean            *  (* Condition *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAwait of
      boolean            *  (* Condition *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StNonCrit of
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StCrit of
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StIf of
      boolean            *  (* Condition *)
      statement_t        *  (* True branch *)
      statement_t option *  (* False branch *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StWhile of
      boolean            *  (* Condition *)
      statement_t        *  (* Loop *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StSelect of
      statement_t list   *  (* Options *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAssign of
      term               *  (* Variable *)
      expr_t             *  (* Expression *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StUnit of
      unit_operation     *  (* Unit operation *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAtomic of
      statement_t list   *  (* Atomic statements *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StSeq of
      statement_t list      (* Statement list *)
  | StCall of
      term option        *  (* Possible assignment term *)
      string             *  (* Procedure name *)
      term list          *  (* Call arguments *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StReturn of
      term option        *  (* Return value *)
      statement_t option *  (* Ghost code *)
      st_info_t option
      


module TermSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = term
  end )



(* Exceptions *)
exception Statement_info_unavailable
exception Empty_sequence
exception Not_supported_conversion of string
exception Invalid_argument




(* VARIABLE FUNCTIONS *)
let build_var ?(nature=E.RealVar)
              (id:varId)
              (s:E.sort)
              (p:procedure_name)
      : variable =
  {
    id = id;
    sort = s;
    scope = p;
    nature = nature;
  }


let var_replace_sort (v:variable) (s:E.sort) : variable =
  build_var v.id s v.scope ~nature:v.nature


(* General constants *)
let me_tid = VarTh (build_var "me" E.Tid GlobalScope)


(* Pretty printing for statement formulas *)

let localize_var_id (v:varId) (p_name:string) : varId =
  sprintf "%s::%s" p_name v


let loc_var_option (v:varId) (p_name:procedure_name) : varId =
  match p_name with
  | GlobalScope -> v
  | Scope proc -> localize_var_id v proc


(* variable_to_str fold function *)
let rec variable_to_str (loc:bool) (var:variable) : string =
  if loc then
    loc_var_option var.id var.scope
  else
    var.id


and atom_to_str (loc:bool) (expr:atom) : string =
  match expr with
    Append(p1,p2,pres)               -> sprintf "append(%s,%s,%s)"
                                                  (path_to_str loc p1)
                                                  (path_to_str loc p2)
                                                  (path_to_str loc pres)
  | Reach(h,add_from,add_to,p)       -> sprintf "reach(%s,%s,%s,%s)"
                                                  (mem_to_str loc h)
                                                  (addr_to_str loc add_from)
                                                  (addr_to_str loc add_to)
                                                  (path_to_str loc p)
  | OrderList(h,add_from,add_to)     -> sprintf "orderlist(%s,%s,%s)"
                                                  (mem_to_str loc h)
                                                  (addr_to_str loc add_from)
                                                  (addr_to_str loc add_to)
  | Skiplist (h,s,l,a_from,a_to,elems)-> sprintf "skiplist(%s,%s,%s,%s,%s,%s)"
                                            (mem_to_str loc h)
                                            (set_to_str loc s)
                                            (integer_to_str loc l)
                                            (addr_to_str loc a_from)
                                            (addr_to_str loc a_to)
                                            (setelem_to_str loc elems)
  | Hashtbl (h,s,se,bb,i)            -> sprintf "hashtbl(%s,%s,%s,%s,%s)"
                                            (mem_to_str loc h)
                                            (set_to_str loc s)
                                            (setelem_to_str loc se)
                                            (bucketarr_to_str loc bb)
                                            (integer_to_str loc i)
  | In(a,s)                          -> sprintf "%s in %s "
                                                  (addr_to_str loc a)
                                                  (set_to_str loc s)
  | SubsetEq(s_in,s_out)             -> sprintf "%s subseteq %s"
                                                  (set_to_str loc s_in)
                                                  (set_to_str loc s_out)
  | InTh(th,s)                       -> sprintf "%s inTh %s"
                                                  (tid_to_str loc th)
                                                  (setth_to_str loc s)
  | SubsetEqTh(s_in,s_out)           -> sprintf "%s subseteqTh %s"
                                                  (setth_to_str loc s_in)
                                                  (setth_to_str loc s_out)
  | InInt(i,s)                       -> sprintf "%s inInt %s"
                                                  (integer_to_str loc i)
                                                  (setint_to_str loc s)
  | SubsetEqInt(s_in,s_out)          -> sprintf "%s subseteqInt %s"
                                                  (setint_to_str loc s_in)
                                                  (setint_to_str loc s_out)
  | InElem(e,s)                      -> sprintf "%s inElem %s"
                                                  (elem_to_str loc e)
                                                  (setelem_to_str loc s)
  | SubsetEqElem(s_in,s_out)         -> sprintf "%s subseteqElem %s"
                                                  (setelem_to_str loc s_in)
                                                  (setelem_to_str loc s_out)
  | InPair(p,s)                      -> sprintf "%s inPair %s"
                                                  (pair_to_str loc p)
                                                  (setpair_to_str loc s)
  | SubsetEqPair(s_in,s_out)         -> sprintf "%s subseteqPair %s"
                                                  (setpair_to_str loc s_in)
                                                  (setpair_to_str loc s_out)
  | Less(i1,i2)                      -> sprintf "%s < %s"
                                                  (integer_to_str loc i1)
                                                  (integer_to_str loc i2)
  | Greater(i1,i2)                   -> sprintf "%s > %s"
                                                  (integer_to_str loc i1)
                                                  (integer_to_str loc i2)
  | LessEq(i1,i2)                    -> sprintf "%s <= %s"
                                                  (integer_to_str loc i1)
                                                  (integer_to_str loc i2)
  | GreaterEq(i1,i2)                 -> sprintf "%s >= %s"
                                                  (integer_to_str loc i1)
                                                  (integer_to_str loc i2)
  | LessTid(t1,t2)                   -> sprintf "%s < %s"
                                                  (tid_to_str loc t1)
                                                  (tid_to_str loc t2)
  | LessElem(e1,e2)                  -> sprintf "%s < %s"
                                                  (elem_to_str loc e1)
                                                  (elem_to_str loc e2)
  | GreaterElem(e1,e2)               -> sprintf "%s > %s"
                                                  (elem_to_str loc e1)
                                                  (elem_to_str loc e2)
  | Eq(exp)                          -> eq_to_str loc (exp)
  | InEq(exp)                        -> diseq_to_str loc (exp)
  | BoolVar v                        -> variable_to_str loc v
  | BoolArrayRd(arr,t)               -> sprintf "%s%s" (arrays_to_str loc arr)
                                                       (tid_to_str loc t)


and arrays_to_str (loc:bool) (expr:arrays) : string =
  match expr with
    VarArray v                -> variable_to_str loc v
  | ArrayUp(arr,t,e)          -> sprintf "%s{%s<-%s}" (arrays_to_str loc arr)
                                                      (tid_to_str loc t)
                                                      (expr_to_str_aux loc e)

and addrarr_to_str (loc:bool) (expr:addrarr) : string =
  match expr with
    VarAddrArray v            -> variable_to_str loc v
  | AddrArrayUp(arr,i,a)      -> sprintf "%s{%s<-%s}" (addrarr_to_str loc arr)
                                                      (integer_to_str loc i)
                                                      (addr_to_str loc a)

and tidarr_to_str (loc:bool) (expr:tidarr) : string =
  match expr with
    VarTidArray v             -> variable_to_str loc v
  | TidArrayUp(arr,i,t)       -> sprintf "%s{%s<-%s}" (tidarr_to_str loc arr)
                                                      (integer_to_str loc i)
                                                      (tid_to_str loc t)


and bucketarr_to_str (loc:bool) (expr:bucketarr) : string =
  match expr with
    VarBucketArray v       -> variable_to_str loc v
  | BucketArrayUp(arr,i,b) -> sprintf "%s{%s<-%s}" (bucketarr_to_str loc arr)
                                                   (integer_to_str loc i)
                                                   (bucket_to_str loc b)


and integer_to_str (loc:bool) (expr:integer) : string =
  match expr with
    IntVal (i)            -> string_of_int i
  | VarInt v              -> variable_to_str loc v
  | IntNeg i              -> sprintf "-%s" (integer_to_str loc i)
  | IntAdd (i1,i2)        -> sprintf "%s + %s" (integer_to_str loc i1)
                                               (integer_to_str loc i2)
  | IntSub (i1,i2)        -> sprintf "%s - %s" (integer_to_str loc i1)
                                               (integer_to_str loc i2)
  | IntMul (i1,i2)        -> sprintf "%s * %s" (integer_to_str loc i1)
                                               (integer_to_str loc i2)
  | IntDiv (i1,i2)        -> sprintf "%s / %s" (integer_to_str loc i1)
                                               (integer_to_str loc i2)
  | IntMod (i1,i2)        -> sprintf "%s %% %s" (integer_to_str loc i1)
                                                (integer_to_str loc i2)
  | IntArrayRd(arr,t)     -> sprintf "%s%s" (arrays_to_str loc arr)
                                            (tid_to_str loc t)
  | IntSetMin(s)          -> sprintf "setIntMin(%s)" (setint_to_str loc s)
  | IntSetMax(s)          -> sprintf "setIntMax(%s)" (setint_to_str loc s)
  | HavocLevel            -> sprintf "havocLevel()"
  | HashCode(e)           -> sprintf "hashCode(%s)" (elem_to_str loc e)
  | PairInt p             -> sprintf "int_of(%s)" (pair_to_str loc p)


and pair_to_str (loc:bool) (expr:pair) : string =
  match expr with
    VarPair v              -> variable_to_str loc v
  | IntTidPair (i,t)       -> sprintf "(%s,%s)" (integer_to_str loc i)
                                                (tid_to_str loc t)
  | SetPairMin ps          -> sprintf "psmin(%s)" (setpair_to_str loc ps)
  | SetPairMax ps          -> sprintf "psmax(%s)" (setpair_to_str loc ps)
  | PairArrayRd(arr,t)     -> sprintf "%s%s" (arrays_to_str loc arr)
                                             (tid_to_str loc t)


and mem_to_str (loc:bool) (expr:mem) : string =
  match expr with
    VarMem  v            -> variable_to_str loc v
  | Update(mem,add,cell) -> sprintf "upd(%s,%s,%s)" (mem_to_str loc mem)
                                                    (addr_to_str loc add)
                                                    (cell_to_str loc cell)
  | MemArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                           (tid_to_str loc t)



and path_to_str (loc:bool) (expr:path) : string =
  match expr with
    VarPath v                    -> variable_to_str loc v
  | Epsilon                      -> sprintf "epsilon"
  | SimplePath(addr)             -> sprintf "[ %s ]" (addr_to_str loc addr)
  | GetPath(mem,add_from,add_to) -> sprintf "getp(%s,%s,%s)"
                                              (mem_to_str loc mem)
                                              (addr_to_str loc add_from)
                                              (addr_to_str loc add_to)
  | PathArrayRd(arr,t)           -> sprintf "%s%s" (arrays_to_str loc arr)
                                                   (tid_to_str loc t)


and set_to_str (loc:bool) (expr:set) : string =
  match expr with
    VarSet v            -> variable_to_str loc v
  | EmptySet            -> "empty"
  | Singl(addr)         -> sprintf "{ %s }" (addr_to_str loc addr)
  | Union(s1,s2)        -> sprintf "union(%s,%s)" (set_to_str loc s1)
                                                  (set_to_str loc s2)
  | Intr(s1,s2)         -> sprintf "intr(%s,%s)" (set_to_str loc s1)
                                                 (set_to_str loc s2)
  | Setdiff(s1,s2)      -> sprintf "diff(%s,%s)" (set_to_str loc s1)
                                                 (set_to_str loc s2)
  | PathToSet(path)     -> sprintf "path2set(%s)" (path_to_str loc path)
  | AddrToSet(mem,addr) -> sprintf "addr2set(%s,%s)" (mem_to_str loc mem)
                                                     (addr_to_str loc addr)
  | AddrToSetAt(m,a,l)  -> sprintf "addr2set(%s,%s,%s)" (mem_to_str loc m)
                                                        (addr_to_str loc a)
                                                        (integer_to_str loc l)
  | SetArrayRd(arr,t)   -> sprintf "%s%s" (arrays_to_str loc arr)
                                          (tid_to_str loc t)
  | BucketRegion(b)     -> sprintf "%s.breg" (bucket_to_str loc b)


and setth_to_str (loc:bool) (expr:setth) : string =
  match expr with
    VarSetTh v             -> variable_to_str loc v
  | EmptySetTh             -> "tempty"
  | SinglTh(th)            -> sprintf "tsingle(%s)" (tid_to_str loc th)
  | UnionTh(s_1,s_2)       -> sprintf "tunion(%s,%s)" (setth_to_str loc s_1)
                                                      (setth_to_str loc s_2)
  | IntrTh(s_1,s_2)        -> sprintf "tintr(%s,%s)" (setth_to_str loc s_1)
                                                     (setth_to_str loc s_2)
  | SetdiffTh(s_1,s_2)     -> sprintf "tdiff(%s,%s)" (setth_to_str loc s_1)
                                                     (setth_to_str loc s_2)
  | SetThArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                             (tid_to_str loc t)


and setint_to_str (loc:bool) (expr:setint) : string =
  match expr with
    VarSetInt v             -> variable_to_str loc v
  | EmptySetInt             -> "iempty"
  | SinglInt(th)            -> sprintf "isingle(%s)" (integer_to_str loc th)
  | UnionInt(s_1,s_2)       -> sprintf "iunion(%s,%s)" (setint_to_str loc s_1)
                                                       (setint_to_str loc s_2)
  | IntrInt(s_1,s_2)        -> sprintf "iintr(%s,%s)" (setint_to_str loc s_1)
                                                      (setint_to_str loc s_2)
  | SetdiffInt(s_1,s_2)     -> sprintf "idiff(%s,%s)"
                                                  (setint_to_str loc s_1)
                                                  (setint_to_str loc s_2)
  | SetIntArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                              (tid_to_str loc t)


and setelem_to_str (loc:bool) (expr:setelem) : string =
  match expr with
    VarSetElem v             -> variable_to_str loc v
  | EmptySetElem             -> "eempty"
  | SinglElem(th)            -> sprintf "esingle(%s)" (elem_to_str loc th)
  | UnionElem(s_1,s_2)       -> sprintf "eunion(%s,%s)" (setelem_to_str loc s_1)
                                                        (setelem_to_str loc s_2)
  | IntrElem(s_1,s_2)        -> sprintf "eintr(%s,%s)" (setelem_to_str loc s_1)
                                                       (setelem_to_str loc s_2)
  | SetdiffElem(s_1,s_2)     -> sprintf "ediff(%s,%s)"
                                                  (setelem_to_str loc s_1)
                                                  (setelem_to_str loc s_2)
  | SetToElems(s,m)          -> sprintf "SetToElems(%s,%s)" (set_to_str loc s)
                                                            (mem_to_str loc m)
  | SetElemArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                               (tid_to_str loc t)


and setpair_to_str (loc:bool) (expr:setpair) : string =
  match expr with
    VarSetPair v             -> variable_to_str loc v
  | EmptySetPair             -> "spempty"
  | SinglPair(p)             -> sprintf "spsingle(%s)" (pair_to_str loc p)
  | UnionPair(s_1,s_2)       -> sprintf "spunion(%s,%s)" (setpair_to_str loc s_1)
                                                         (setpair_to_str loc s_2)
  | IntrPair(s_1,s_2)        -> sprintf "spintr(%s,%s)" (setpair_to_str loc s_1)
                                                        (setpair_to_str loc s_2)
  | SetdiffPair(s_1,s_2)     -> sprintf "spdiff(%s,%s)"
                                                  (setpair_to_str loc s_1)
                                                  (setpair_to_str loc s_2)
  | SetPairArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                                (tid_to_str loc t)


and cell_to_str (loc:bool) (expr:cell) : string =
  let apply_str f xs = String.concat "," (List.map f xs) in
  match expr with
    VarCell v                  -> variable_to_str loc v
  | Error -> "Error"
  | MkCell(data,addr,th)       -> sprintf "mkcell(%s,%s,%s)"
                                               (elem_to_str loc data)
                                               (addr_to_str loc addr)
                                               (tid_to_str loc th)
  | MkCellMark(data,addr,th,m) -> sprintf "mkcell(%s,%s,%s,%s)"
                                           (elem_to_str loc data)
                                           (addr_to_str loc addr)
                                           (tid_to_str loc th)
                                           (mark_to_str loc m)
  | MkSLKCell(data,aa,tt)      -> sprintf "mkcell(%s,[%s],[%s])"
                                             (elem_to_str loc data)
                                             (apply_str (addr_to_str loc) aa)
                                             (apply_str (tid_to_str loc) tt)
  | MkSLCell(data,aa,ta,l)     -> sprintf "mkcell(%s,%s,%s,%s)"
                                             (elem_to_str loc data)
                                             (addrarr_to_str loc aa)
                                             (tidarr_to_str loc ta)
                                             (integer_to_str loc l)
  | CellLock(cell)             -> sprintf "%s.lock" (cell_to_str loc cell)
  | CellUnlock(cell)           -> sprintf "%s.unlock" (cell_to_str loc cell)
  | CellLockAt(cell,l)         -> sprintf "%s.lock[%s]" (cell_to_str loc cell)
                                                        (integer_to_str loc l)
  | CellUnlockAt(cell,l)       -> sprintf "%s.unlock[%s]" (cell_to_str loc cell)
                                                          (integer_to_str loc l)
  | CellAt(mem,addr)           -> sprintf "rd(%s,%s)" (mem_to_str loc mem)
                                                      (addr_to_str loc addr)
  | CellArrayRd(arr,t)         -> sprintf "%s%s" (arrays_to_str loc arr)
                                                 (tid_to_str loc t)


and mark_to_str (loc:bool) (expr:mark) : string =
  match expr with
    VarMark v       -> variable_to_str loc v
  | MarkTrue        -> "T"
  | MarkFalse       -> "F"
  | Marked c        -> sprintf "%s.marked" (cell_to_str loc c)
  | PointerMarked a -> sprintf "%s->marked" (addr_to_str loc a)


and bucket_to_str (loc:bool) (b:bucket) :string =
  match b with
    VarBucket v -> variable_to_str loc v
  | MkBucket (i,e,s,t) -> sprintf "mkbucket(%s,%s,%s,%s)" (addr_to_str loc i)
                                                          (addr_to_str loc e)
                                                          (set_to_str loc s)
                                                          (tid_to_str loc t)
  | BucketArrRd(bb,i)  -> sprintf "%s[%s]" (bucketarr_to_str loc bb)
                                           (integer_to_str loc i)


and addr_to_str (loc:bool) (expr:addr) : string =
  match expr with
    VarAddr v             -> variable_to_str loc v
  | Null                  -> "null"
  | Next(cell)            -> sprintf "%s.next" (cell_to_str loc cell)
  | NextAt(cell,l)        -> sprintf "%s.nextat[%s]" (cell_to_str loc cell)
                                                     (integer_to_str loc l)
  | ArrAt(cell,l)         -> sprintf "%s.arr[%s]" (cell_to_str loc cell)
                                                  (integer_to_str loc l)
  | FirstLocked(mem,path) -> sprintf "firstlocked(%s,%s)"
                                            (mem_to_str loc mem)
                                            (path_to_str loc path)

  | LastLocked(mem,path)  -> sprintf "lastlocked(%s,%s)"
                                            (mem_to_str loc mem)
                                            (path_to_str loc path)
  | AddrArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                              (tid_to_str loc t)
  | Malloc(e,a,t)         -> sprintf "malloc(%s,%s,%s)" (elem_to_str loc e)
                                                        (addr_to_str loc a)
                                                        (tid_to_str loc t)
  | MallocSL(e,l)         -> sprintf "mallocSL(%s,%s)" (elem_to_str loc e)
                                                       (integer_to_str loc l)
  | MallocSLK(e,l)        -> sprintf "mallocSLK(%s,%s)" (elem_to_str loc e)
                                                        (integer_to_str loc l)
  | PointerNext a         -> sprintf "%s->next" (addr_to_str loc a)
  | PointerNextAt(a,l)    -> sprintf "%s->nextat[%s]" (addr_to_str loc a)
                                                      (integer_to_str loc l)
  | PointerArrAt(a,l)     -> sprintf "%s->arr[%s]" (addr_to_str loc a)
                                                   (integer_to_str loc l)
  | AddrArrRd (arr,i)     -> sprintf "%s[%s]" (addrarr_to_str loc arr)
                                              (integer_to_str loc i)
  | BucketInit(b)         -> sprintf "%s.binit" (bucket_to_str loc b)
  | BucketEnd(b)          -> sprintf "%s.bend" (bucket_to_str loc b)


and tid_to_str (loc:bool) (th:tid) : string =
  match th with
    VarTh v              -> variable_to_str loc v
  | NoTid               -> sprintf "#"
  | CellLockId(cell)     -> sprintf "%s.lockid" (cell_to_str loc cell)
  | CellLockIdAt(cell,l) -> sprintf "%s.lockid[%s]" (cell_to_str loc cell)
                                                    (integer_to_str loc l)
  | TidArrayRd(arr,t)   -> sprintf "%s%s" (arrays_to_str loc arr)
                                           (tid_to_str loc t)
  | PointerLockid a      -> sprintf "%s->lockid" (addr_to_str loc a)
  | PointerLockidAt(a,l) -> sprintf "%s->lockid[%s]" (addr_to_str loc a)
                                                     (integer_to_str loc l)
  | TidArrRd (arr,i)    -> sprintf "%s[%s]" (tidarr_to_str loc arr)
                                             (integer_to_str loc i)
  | PairTid p           -> sprintf "tid_of(%s)" (pair_to_str loc p)
  | BucketTid b         -> sprintf "%s.btid" (bucket_to_str loc b)
  | LockId l            -> sprintf "%s.id" (lock_to_str loc l)


and lock_to_str (loc:bool) (expr:lock) : string =
  match expr with
    VarLock v        -> variable_to_str loc v
  | LLock (l,t)      -> sprintf "lock(%s,%s)" (lock_to_str loc l)
                                              (tid_to_str loc t)
  | LUnlock (l)      -> sprintf "unlock(%s)" (lock_to_str loc l)
  | LockArrRd (ll,i) -> sprintf "%s[%s]" (lockarr_to_str loc ll)
                                         (integer_to_str loc i)


and lockarr_to_str (loc:bool) (expr:lockarr) : string =
  match expr with
    VarLockArray v       -> variable_to_str loc v
  | LockArrayUp(arr,i,l) -> sprintf "%s{%s<-%s}" (lockarr_to_str loc arr)
                                                 (integer_to_str loc i)
                                                 (lock_to_str loc l)


and eq_to_str (loc:bool) ((e1,e2):eq) : string =
      sprintf "%s = %s" (term_to_str_aux loc e1) (term_to_str_aux loc e2)


and diseq_to_str (loc:bool) (expr:diseq) : string =
    let (e1,e2) = expr in
      sprintf "%s != %s" (term_to_str_aux loc e1) (term_to_str_aux loc e2)


and elem_to_str (loc:bool) (expr:elem) : string =
  match expr with
    VarElem v             -> variable_to_str loc v
  | CellData(cell)        -> sprintf "%s.data" (cell_to_str loc cell)
  | ElemArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str loc arr)
                                         (tid_to_str loc t)
  | PointerData a         -> sprintf "%s->data" (addr_to_str loc a)
  | HavocListElem         -> sprintf "havocListElem()"
  | HavocSkiplistElem     -> sprintf "havocSLElem()"
  | LowestElem            -> sprintf "lowestElem"
  | HighestElem           -> sprintf "highestElem"


and term_to_str_aux (loc:bool) (expr:term) : string =
  match expr with
    VarT v              -> variable_to_str loc v
  | SetT(set)           -> (set_to_str loc set)
  | AddrT(addr)         -> (addr_to_str loc addr)
  | ElemT(elem)         -> (elem_to_str loc elem)
  | TidT(th)            -> (tid_to_str loc th)
  | CellT(cell)         -> (cell_to_str loc cell)
  | SetThT(setth)       -> (setth_to_str loc setth)
  | SetIntT(setint)     -> (setint_to_str loc setint)
  | SetElemT(setelem)   -> (setelem_to_str loc setelem)
  | SetPairT(setpair)   -> (setpair_to_str loc setpair)
  | PathT(path)         -> (path_to_str loc path)
  | MemT(mem)           -> (mem_to_str loc mem)
  | IntT(i)             -> (integer_to_str loc i)
  | PairT(p)            -> (pair_to_str loc p)
  | ArrayT(arr)         -> (arrays_to_str loc arr)
  | AddrArrayT(arr)     -> (addrarr_to_str loc arr)
  | TidArrayT(arr)      -> (tidarr_to_str loc arr)
  | BucketArrayT(arr)   -> (bucketarr_to_str loc arr)
  | MarkT(m)            -> (mark_to_str loc m)
  | BucketT(b)          -> (bucket_to_str loc b)
  | LockT(l)            -> (lock_to_str loc l)
  | LockArrayT(arr)     -> (lockarr_to_str loc arr)



and expr_to_str_aux (loc:bool) (expr:expr_t) : string =
  match expr with
    Term t    -> term_to_str_aux loc t
  | Formula b -> boolean_to_str_aux loc b


and boolean_to_str_aux (loc:bool) (expr:boolean) : string =
  F.formula_to_str (atom_to_str loc) expr


(* Type conversion functions *)


let term_to_integer (t:term) : integer =
  match t with
    IntT i -> i
  | _      -> Interface.Err.msg "Not an integer term" $
                sprintf "Impossible to convert to integer a non integer \
                         term. An integer term was expected, but \"%s\" was \
                         received." (term_to_str_aux true t);
              raise(Invalid_argument)


let term_to_set (t:term) : set =
  match t with
    SetT s -> s
  | _      -> Interface.Err.msg "Not a set term" $
                sprintf "Impossible to convert to set a non set \
                         term. A set term was expected, but \"%s\" was \
                         received." (term_to_str_aux true t);
              raise(Invalid_argument)


let term_to_setth (t:term) : setth =
  match t with
    SetThT s -> s
  | _        -> Interface.Err.msg "Not a set of thread identifiers term" $
                  sprintf "Impossible to convert to set of thread identifiers \
                           a non set of thread identifiers term. A set of \
                           thread identifiers term was expected, but \"%s\" \
                           was received." (term_to_str_aux true t);
                raise(Invalid_argument)


let term_to_setint (t:term) : setint =
  match t with
    SetIntT s -> s
  | _        -> Interface.Err.msg "Not a set of integers term" $
                  sprintf "Impossible to convert to set of integers \
                           a non set of integers term. A set of \
                            integers term was expected, but \"%s\" \
                           was received." (term_to_str_aux true t);
                raise(Invalid_argument)


let term_to_setelem (t:term) : setelem =
  match t with
    SetElemT s -> s
  | _          -> Interface.Err.msg "Not a set of elements term" $
                    sprintf "Impossible to convert to set of elements \
                             a non set of elements term. A set of \
                             elements term was expected, but \"%s\" \
                             was received." (term_to_str_aux true t);
                  raise(Invalid_argument)


let term_to_setpair (t:term) : setpair =
  match t with
    SetPairT s -> s
  | _          -> Interface.Err.msg "Not a set of pairs term" $
                    sprintf "Impossible to convert to set of pairs \
                             a non set of pairs term. A set of \
                             pairs term was expected, but \"%s\" \
                             was received." (term_to_str_aux true t);
                  raise(Invalid_argument)


let variable_to_expr_var (v:variable) :E.V.t =
  let new_scope = match v.scope with
                  | GlobalScope -> E.V.GlobalScope
                  | Scope p -> E.V.Scope p in
  E.build_var v.id v.sort false E.V.Shared new_scope ~nature:v.nature


let rec term_to_expr_term (t:term) : E.term =
  match t with
    VarT v         -> E.VarT         (variable_to_expr_var v)
  | SetT s         -> E.SetT         (set_to_expr_set s)
  | ElemT e        -> E.ElemT        (elem_to_expr_elem e)
  | TidT t         -> E.TidT         (tid_to_expr_tid t)
  | AddrT a        -> E.AddrT        (addr_to_expr_addr a)
  | CellT c        -> E.CellT        (cell_to_expr_cell c)
  | SetThT s       -> E.SetThT       (setth_to_expr_setth s)
  | SetIntT s      -> E.SetIntT      (setint_to_expr_setint s)
  | SetElemT s     -> E.SetElemT     (setelem_to_expr_setelem s)
  | SetPairT s     -> E.SetPairT     (setpair_to_expr_setpair s)
  | PathT p        -> E.PathT        (path_to_expr_path p)
  | MemT m         -> E.MemT         (mem_to_expr_mem m)
  | IntT i         -> E.IntT         (integer_to_expr_integer i)
  | PairT i        -> E.PairT        (pair_to_expr_pair i)
  | ArrayT a       -> E.ArrayT       (array_to_expr_array a)
  | AddrArrayT a   -> E.AddrArrayT   (addrarray_to_expr_array a)
  | TidArrayT a    -> E.TidArrayT    (tidarray_to_expr_array a)
  | BucketArrayT a -> E.BucketArrayT (bucketarray_to_expr_array a)
  | MarkT m        -> E.MarkT        (mark_to_expr_mark m)
  | BucketT b      -> E.BucketT      (bucket_to_expr_bucket b)
  | LockT l        -> E.LockT        (lock_to_expr_lock l)
  | LockArrayT a   -> E.LockArrayT   (lockarr_to_expr_lockarr a)


and eq_to_expr_eq ((t1,t2):eq) : E.eq =
  (term_to_expr_term t1, term_to_expr_term t2)


and diseq_to_expr_diseq ((t1,t2):diseq) : E.diseq =
  (term_to_expr_term t1, term_to_expr_term t2)


and array_to_expr_array (a:arrays) : E.arrays =
  match a with
    VarArray v      -> E.VarArray (variable_to_expr_var v)
  | ArrayUp (a,t,e) -> E.ArrayUp (array_to_expr_array a,
                                  tid_to_expr_th t,
                                  expr_to_expr_expr e)

and addrarray_to_expr_array (a:addrarr) : E.addrarr =
  match a with
    VarAddrArray v        -> E.VarAddrArray (variable_to_expr_var v)
  | AddrArrayUp (arr,i,a) -> E.AddrArrayUp (addrarray_to_expr_array arr,
                                            integer_to_expr_integer i,
                                            addr_to_expr_addr a)

and tidarray_to_expr_array (a:tidarr) : E.tidarr =
  match a with
    VarTidArray v        -> E.VarTidArray (variable_to_expr_var v)
  | TidArrayUp (arr,i,t) -> E.TidArrayUp (tidarray_to_expr_array arr,
                                          integer_to_expr_integer i,
                                          tid_to_expr_tid t)


and bucketarray_to_expr_array (a:bucketarr) : E.bucketarr =
  match a with
    VarBucketArray v        -> E.VarBucketArray (variable_to_expr_var v)
  | BucketArrayUp (arr,i,b) -> E.BucketArrayUp (bucketarray_to_expr_array arr,
                                                integer_to_expr_integer i,
                                                bucket_to_expr_bucket b)


and integer_to_expr_integer (i:integer) : E.integer =
  let to_int = integer_to_expr_integer in
  match i with
    IntVal i         -> E.IntVal i
  | VarInt v         -> E.VarInt (variable_to_expr_var v)
  | IntNeg i         -> E.IntNeg (to_int i)
  | IntAdd (i1,i2)   -> E.IntAdd(to_int i1, to_int i2)
  | IntSub (i1,i2)   -> E.IntSub(to_int i1, to_int i2)
  | IntMul (i1,i2)   -> E.IntMul(to_int i1, to_int i2)
  | IntDiv (i1,i2)   -> E.IntDiv(to_int i1, to_int i2)
  | IntMod (i1,i2)   -> E.IntMod(to_int i1, to_int i2)
  | IntArrayRd (a,t) -> E.IntArrayRd (array_to_expr_array a,
                                      tid_to_expr_th t)
  | IntSetMin s      -> E.IntSetMin (setint_to_expr_setint s)
  | IntSetMax s      -> E.IntSetMax (setint_to_expr_setint s)
  | HavocLevel       -> E.HavocLevel
  | HashCode e       -> E.HashCode (elem_to_expr_elem e)
  | PairInt p        -> E.PairInt (pair_to_expr_pair p)


and pair_to_expr_pair (p:pair) : E.pair =
  let to_int = integer_to_expr_integer in
  let to_tid = tid_to_expr_tid in
  let to_setpair = setpair_to_expr_setpair in
  match p with
    VarPair v         -> E.VarPair (variable_to_expr_var v)
  | IntTidPair (i,t)  -> E.IntTidPair (to_int i, to_tid t)
  | SetPairMin ps     -> E.SetPairMin(to_setpair ps)
  | SetPairMax ps     -> E.SetPairMax(to_setpair ps)
  | PairArrayRd (a,t) -> E.PairArrayRd (array_to_expr_array a,
                                        tid_to_expr_th t)


and set_to_expr_set (s:set) : E.set =
  let to_set = set_to_expr_set in
  match s with
    VarSet v            -> E.VarSet (variable_to_expr_var v)
  | EmptySet            -> E.EmptySet
  | Singl a             -> E.Singl (addr_to_expr_addr a)
  | Union (s1,s2)       -> E.Union (to_set s1, to_set s2)
  | Intr (s1,s2)        -> E.Intr (to_set s1, to_set s2)
  | Setdiff (s1,s2)     -> E.Setdiff (to_set s1, to_set s2)
  | PathToSet p         -> E.PathToSet (path_to_expr_path p)
  | AddrToSet (m,a)     -> E.AddrToSet (mem_to_expr_mem m, addr_to_expr_addr a)
  | AddrToSetAt (m,a,l) -> E.AddrToSetAt (mem_to_expr_mem m, addr_to_expr_addr a,
                                          integer_to_expr_integer l)
  | SetArrayRd (a,t)    -> E.SetArrayRd (array_to_expr_array a,
                                      tid_to_expr_th t)
  | BucketRegion b      -> E.BucketRegion (bucket_to_expr_bucket b)


and tid_to_expr_tid (t:tid) : E.tid =
  match t with
    VarTh v              -> E.VarTh (variable_to_expr_var v)
  | NoTid                -> E.NoTid
  | CellLockId c         -> E.CellLockId (cell_to_expr_cell c)
  | CellLockIdAt(c,l)    -> E.CellLockIdAt (cell_to_expr_cell c,
                                            integer_to_expr_integer l)
  | TidArrayRd (a,t)     -> E.TidArrayRd (array_to_expr_array a,
                                          tid_to_expr_th t)
  | TidArrRd (a,l)       -> E.TidArrRd (tidarray_to_expr_array a,
                                        integer_to_expr_integer l)
  | PointerLockid a      -> E.CellLockId(E.CellAt(E.heap,addr_to_expr_addr a))
  | PointerLockidAt(a,l) -> E.CellLockIdAt(E.CellAt(E.heap,addr_to_expr_addr a),
                                           integer_to_expr_integer l)
  | PairTid p            -> E.PairTid(pair_to_expr_pair p)
  | BucketTid b          -> E.BucketTid (bucket_to_expr_bucket b)
  | LockId l             -> E.LockId (lock_to_expr_lock l)


and lock_to_expr_lock (x:lock) : E.lock =
  match x with
    VarLock v        -> E.VarLock (variable_to_expr_var v)
  | LLock (l,t)      -> E.LLock (lock_to_expr_lock l, tid_to_expr_th t)
  | LUnlock (l)      -> E.LUnlock (lock_to_expr_lock l)
  | LockArrRd (ll,i) -> E.LockArrRd (lockarr_to_expr_lockarr ll,
                                     integer_to_expr_integer i)

and lockarr_to_expr_lockarr (x:lockarr) : E.lockarr =
  match x with
    VarLockArray v       -> E.VarLockArray (variable_to_expr_var v)
  | LockArrayUp (ll,i,l) -> E.LockArrayUp (lockarr_to_expr_lockarr ll,
                                           integer_to_expr_integer i,
                                           lock_to_expr_lock l)


and tid_to_expr_th (t:tid) : E.tid =
  match t with
    VarTh v            -> E.VarTh (variable_to_expr_var v)
  | NoTid              -> E.NoTid
  | CellLockId c       -> E.CellLockId (cell_to_expr_cell c)
  | CellLockIdAt (c,l) -> E.TidArrRd (E.CellTids (cell_to_expr_cell c),
                                       integer_to_expr_integer l)
  | TidArrayRd _       -> raise(Not_supported_conversion(tid_to_str true t))
  | TidArrRd _         -> raise(Not_supported_conversion(tid_to_str true t))
  | PointerLockid _    -> raise(Not_supported_conversion(tid_to_str true t))
  | PointerLockidAt _  -> raise(Not_supported_conversion(tid_to_str true t))
  | PairTid _          -> raise(Not_supported_conversion(tid_to_str true t))
  | BucketTid _        -> raise(Not_supported_conversion(tid_to_str true t))
  | LockId _           -> raise(Not_supported_conversion(tid_to_str true t))


and elem_to_expr_elem (e:elem) : E.elem =
  match e with
    VarElem v         -> E.VarElem (variable_to_expr_var v)
  | CellData c        -> E.CellData (cell_to_expr_cell c)
  | ElemArrayRd (a,t) -> E.ElemArrayRd (array_to_expr_array a,
                                        tid_to_expr_th t)
  | PointerData a     -> E.CellData(E.CellAt(E.heap,addr_to_expr_addr a))
  | HavocListElem     -> E.HavocListElem
  | HavocSkiplistElem -> E.HavocSkiplistElem
  | LowestElem        -> E.LowestElem
  | HighestElem       -> E.HighestElem


and addr_to_expr_addr (a:addr) : E.addr =
  match a with
    VarAddr v           -> E.VarAddr (variable_to_expr_var v)
  | Null                -> E.Null
  | Next c              -> E.Next (cell_to_expr_cell c)
  | NextAt (c,l)        -> E.NextAt (cell_to_expr_cell c,
                                     integer_to_expr_integer l)
  | ArrAt (c,l)         -> E.AddrArrRd (E.CellArr (cell_to_expr_cell c),
                                        integer_to_expr_integer l)
  | FirstLocked (m,p)   -> E.FirstLocked (mem_to_expr_mem m,
                                          path_to_expr_path p)
  | LastLocked (m,p)    -> E.LastLocked (mem_to_expr_mem m,
                                         path_to_expr_path p)
  | AddrArrayRd (a,t)   -> E.AddrArrayRd (array_to_expr_array a,
                                        tid_to_expr_th t)
  | AddrArrRd (a,i)     -> E.AddrArrRd (addrarray_to_expr_array a,
                                        integer_to_expr_integer i)
  | Malloc _            -> raise(Not_supported_conversion(addr_to_str true a))
  | MallocSL _          -> raise(Not_supported_conversion(addr_to_str true a))
  | MallocSLK _         -> raise(Not_supported_conversion(addr_to_str true a))
  | PointerNext a       -> E.Next(E.CellAt(E.heap,addr_to_expr_addr a))
  | PointerNextAt (a,l) -> E.NextAt(E.CellAt(E.heap,addr_to_expr_addr a),
                                    integer_to_expr_integer l)
  | PointerArrAt (a,l)  -> E.AddrArrRd (E.CellArr(E.CellAt(E.heap,addr_to_expr_addr a)),
                                        integer_to_expr_integer l)
  | BucketInit b        -> E.BucketInit(bucket_to_expr_bucket b)
  | BucketEnd b         -> E.BucketEnd(bucket_to_expr_bucket b)



and cell_to_expr_cell (c:cell) : E.cell =
  match c with
    VarCell v            -> E.VarCell (variable_to_expr_var v)
  | Error                -> E.Error
  | MkCell (e,a,t)       -> E.MkCell (elem_to_expr_elem e,
                                      addr_to_expr_addr a,
                                      tid_to_expr_tid t)
  | MkCellMark (e,a,t,m) -> E.MkCellMark (elem_to_expr_elem e,
                                          addr_to_expr_addr a,
                                          tid_to_expr_tid t,
                                          mark_to_expr_mark m)
  | MkSLKCell (e,aa,tt)  -> E.MkSLKCell (elem_to_expr_elem e,
                                          List.map addr_to_expr_addr aa,
                                          List.map tid_to_expr_tid tt)
  | MkSLCell (e,aa,ta,l) -> E.MkSLCell (elem_to_expr_elem e,
                                        addrarray_to_expr_array aa,
                                        tidarray_to_expr_array ta,
                                        integer_to_expr_integer l)
  (* ALE: Check whether this case should be here or have a NoTid as an option. *)
  | CellLock c           -> E.CellLock (cell_to_expr_cell c, E.NoTid)
  | CellLockAt (c,l)     -> E.CellLockAt (cell_to_expr_cell c,
                                          integer_to_expr_integer l,
                                          E.NoTid)
  | CellUnlock c         -> E.CellUnlock (cell_to_expr_cell c)
  | CellUnlockAt (c,l)   -> E.CellUnlockAt (cell_to_expr_cell c,
                                            integer_to_expr_integer l)
  | CellAt (m,a)         -> E.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)
  | CellArrayRd (a,t)    -> E.CellArrayRd (array_to_expr_array a,
                                           tid_to_expr_th t) 


and mark_to_expr_mark (m:mark) : E.mark =
  match m with
    VarMark v       -> E.VarMark (variable_to_expr_var v)
  | MarkTrue        -> E.MarkTrue
  | MarkFalse       -> E.MarkFalse
  | Marked c        -> E.Marked (cell_to_expr_cell c)
  | PointerMarked a -> E.Marked(E.CellAt(E.heap,addr_to_expr_addr a))


and bucket_to_expr_bucket (b:bucket) : E.bucket =
  match b with
    VarBucket v        -> E.VarBucket (variable_to_expr_var v)
  | MkBucket(i,e,s,t)  -> E.MkBucket (addr_to_expr_addr i,
                                      addr_to_expr_addr e,
                                      set_to_expr_set s,
                                      tid_to_expr_tid t)
  | BucketArrRd (bb,i) -> E.BucketArrRd (bucketarray_to_expr_array bb,
                                         integer_to_expr_integer i)


and setth_to_expr_setth (s:setth) : E.setth =
  let to_setth = setth_to_expr_setth in
  match s with
    VarSetTh v         -> E.VarSetTh (variable_to_expr_var v)
  | EmptySetTh         -> E.EmptySetTh
  | SinglTh t          -> E.SinglTh (tid_to_expr_tid t)
  | UnionTh (s1,s2)    -> E.UnionTh (to_setth s1, to_setth s2)
  | IntrTh (s1,s2)     -> E.IntrTh (to_setth s1, to_setth s2)
  | SetdiffTh (s1,s2)  -> E.SetdiffTh (to_setth s1, to_setth s2)
  | SetThArrayRd (a,t) -> E.SetThArrayRd (array_to_expr_array a,
                                          tid_to_expr_th t)


and setint_to_expr_setint (s:setint) : E.setint =
  let to_setint = setint_to_expr_setint in
  match s with
    VarSetInt v         -> E.VarSetInt(variable_to_expr_var v)
  | EmptySetInt         -> E.EmptySetInt
  | SinglInt i          -> E.SinglInt (integer_to_expr_integer i)
  | UnionInt (s1,s2)    -> E.UnionInt (to_setint s1, to_setint s2)
  | IntrInt (s1,s2)     -> E.IntrInt (to_setint s1, to_setint s2)
  | SetdiffInt (s1,s2)  -> E.SetdiffInt (to_setint s1, to_setint s2)
  | SetIntArrayRd (a,t) -> E.SetIntArrayRd (array_to_expr_array a,
                                            tid_to_expr_th t)


and setelem_to_expr_setelem (s:setelem) : E.setelem =
  let to_setelem = setelem_to_expr_setelem in
  match s with
    VarSetElem v         -> E.VarSetElem(variable_to_expr_var v)
  | EmptySetElem         -> E.EmptySetElem
  | SinglElem e          -> E.SinglElem (elem_to_expr_elem e)
  | UnionElem (s1,s2)    -> E.UnionElem (to_setelem s1, to_setelem s2)
  | IntrElem (s1,s2)     -> E.IntrElem (to_setelem s1, to_setelem s2)
  | SetdiffElem (s1,s2)  -> E.SetdiffElem (to_setelem s1, to_setelem s2)
  | SetToElems (s,m)     -> E.SetToElems (set_to_expr_set s, mem_to_expr_mem m)
  | SetElemArrayRd (a,t) -> E.SetElemArrayRd (array_to_expr_array a,
                                            tid_to_expr_th t)



and setpair_to_expr_setpair (s:setpair) : E.setpair =
  let to_setpair = setpair_to_expr_setpair in
  match s with
    VarSetPair v         -> E.VarSetPair(variable_to_expr_var v)
  | EmptySetPair         -> E.EmptySetPair
  | SinglPair p          -> E.SinglPair (pair_to_expr_pair p)
  | UnionPair (s1,s2)    -> E.UnionPair (to_setpair s1, to_setpair s2)
  | IntrPair (s1,s2)     -> E.IntrPair (to_setpair s1, to_setpair s2)
  | SetdiffPair (s1,s2)  -> E.SetdiffPair (to_setpair s1, to_setpair s2)
  | SetPairArrayRd (a,t) -> E.SetPairArrayRd (array_to_expr_array a,
                                              tid_to_expr_th t)


and path_to_expr_path (p:path) : E.path =
  match p with
    VarPath v         -> E.VarPath (variable_to_expr_var v)
  | Epsilon           -> E.Epsilon
  | SimplePath a      -> E.SimplePath (addr_to_expr_addr a)
  | GetPath (m,a1,a2) -> E.GetPath (mem_to_expr_mem m,
                                    addr_to_expr_addr a1,
                                    addr_to_expr_addr a2)
  | PathArrayRd (a,t) -> E.PathArrayRd (array_to_expr_array a,
                                        tid_to_expr_th t)


and mem_to_expr_mem (m:mem) : E.mem =
  match m with
    VarMem v         -> E.VarMem (variable_to_expr_var v)
  | Update (m,a,c)   -> E.Update (mem_to_expr_mem m,
                                  addr_to_expr_addr a,
                                  cell_to_expr_cell c)
  | MemArrayRd (a,t) -> E.MemArrayRd (array_to_expr_array a,
                                      tid_to_expr_th t)


and atom_to_expr_atom (a:atom) : E.atom =
  let to_int = integer_to_expr_integer in
  match a with
    Append (p1,p2,p3)         -> E.Append (path_to_expr_path p1,
                                           path_to_expr_path p2,
                                           path_to_expr_path p3)
  | Reach (m,a1,a2,p)         -> E.Reach (mem_to_expr_mem m,
                                          addr_to_expr_addr a1,
                                          addr_to_expr_addr a2,
                                          path_to_expr_path p)
  | OrderList (m,a1,a2)       -> E.OrderList (mem_to_expr_mem m,
                                              addr_to_expr_addr a1,
                                              addr_to_expr_addr a2)
  | Skiplist (m,s,l,a1,a2,es) -> E.Skiplist (mem_to_expr_mem m,
                                             set_to_expr_set s,
                                             integer_to_expr_integer l,
                                             addr_to_expr_addr a1,
                                             addr_to_expr_addr a2,
                                             setelem_to_expr_setelem es)
  | Hashtbl (m,s,se,bb,i)     -> E.Hashtbl (mem_to_expr_mem m,
                                            set_to_expr_set s,
                                            setelem_to_expr_setelem se,
                                            bucketarray_to_expr_array bb,
                                            integer_to_expr_integer i)
  | In (a,s)                  -> E.In (addr_to_expr_addr a, set_to_expr_set s)
  | SubsetEq (s1,s2)          -> E.SubsetEq (set_to_expr_set s1, set_to_expr_set s2)
  | InTh (t,s)                -> E.InTh (tid_to_expr_tid t, setth_to_expr_setth s)
  | SubsetEqTh (s1,s2)        -> E.SubsetEqTh (setth_to_expr_setth s1,
                                               setth_to_expr_setth s2)
  | InInt (i,s)               -> E.InInt (integer_to_expr_integer i,
                                          setint_to_expr_setint s)
  | SubsetEqInt (s1,s2)       -> E.SubsetEqInt (setint_to_expr_setint s1,
                                                setint_to_expr_setint s2)
  | InElem (e,s)              -> E.InElem (elem_to_expr_elem e,
                                           setelem_to_expr_setelem s)
  | SubsetEqElem (s1,s2)      -> E.SubsetEqElem (setelem_to_expr_setelem s1,
                                                 setelem_to_expr_setelem s2)
  | InPair (p,s)              -> E.InPair (pair_to_expr_pair p,
                                           setpair_to_expr_setpair s)
  | SubsetEqPair (s1,s2)      -> E.SubsetEqPair (setpair_to_expr_setpair s1,
                                                 setpair_to_expr_setpair s2)
  | Less (i1,i2)              -> E.Less      (to_int i1, to_int i2)
  | Greater (i1,i2)           -> E.Greater   (to_int i1, to_int i2)
  | LessEq (i1,i2)            -> E.LessEq    (to_int i1, to_int i2)
  | GreaterEq (i1,i2)         -> E.GreaterEq (to_int i1, to_int i2)
  | LessTid (t1,t2)           -> E.LessTid   (tid_to_expr_th t1, tid_to_expr_th t2)
  | LessElem (e1,e2)          -> E.LessElem  (elem_to_expr_elem e1,
                                              elem_to_expr_elem e2)
  | GreaterElem (e1,e2)       -> E.GreaterElem (elem_to_expr_elem e1,
                                                elem_to_expr_elem e2)
  | Eq e                      -> E.Eq        (eq_to_expr_eq e)
  | InEq d                    -> E.InEq      (diseq_to_expr_diseq d)
  | BoolVar v                 -> E.BoolVar (variable_to_expr_var v)
  | BoolArrayRd (a,t)         -> E.BoolArrayRd (array_to_expr_array a,
                                                tid_to_expr_th t)


and boolean_to_expr_formula (b:boolean) : E.formula =
  F.formula_conv atom_to_expr_atom b


and expr_to_expr_expr (e:expr_t) : E.expr_t =
  match e with
    Term t    -> E.Term (term_to_expr_term t)
  | Formula b -> E.Formula (boolean_to_expr_formula b)



let construct_var_from_sort (id:varId)
                            (p_name:procedure_name)
                            (s:E.sort)
                            (k:E.var_nature) : term =
  let v = build_var id s p_name ~nature:k in
  match s with
    E.Set         -> SetT          (VarSet           v)
  | E.Elem        -> ElemT         (VarElem          v)
  | E.Tid         -> TidT          (VarTh            v)
  | E.Addr        -> AddrT         (VarAddr          v)
  | E.Cell        -> CellT         (VarCell          v)
  | E.SetTh       -> SetThT        (VarSetTh         v)
  | E.SetInt      -> SetIntT       (VarSetInt        v)
  | E.SetElem     -> SetElemT      (VarSetElem       v)
  | E.SetPair     -> SetPairT      (VarSetPair       v)
  | E.Path        -> PathT         (VarPath          v)
  | E.Mem         -> MemT          (VarMem           v)
  | E.Bool        -> VarT          v
  | E.Int         -> IntT          (VarInt           v)
  | E.Pair        -> PairT         (VarPair          v)
  | E.Array       -> ArrayT        (VarArray         v)
  | E.AddrArray   -> AddrArrayT    (VarAddrArray     v)
  | E.TidArray    -> TidArrayT     (VarTidArray      v)
  | E.BucketArray -> BucketArrayT  (VarBucketArray   v)
  | E.Mark        -> MarkT         (VarMark          v)
  | E.Bucket      -> BucketT       (VarBucket        v)
  | E.Lock        -> LockT         (VarLock          v)
  | E.LockArray   -> LockArrayT    (VarLockArray     v)
  | E.Unknown     -> VarT          v


let term_to_str (t:term) : string =
  term_to_str_aux true t


let boolean_to_str (expr:boolean) : string =
  boolean_to_str_aux true expr


let boolean_to_simp_str (expr:boolean) : string =
  boolean_to_str_aux false expr


let expr_to_str (e:expr_t) : string =
  expr_to_str_aux true e


(* GHOST TERMS *)
let rec var_kind_term (kind:E.var_nature) (expr:term) : term list =
  match expr with
      VarT v            -> if v.nature = kind then [expr] else []
    | SetT(set)         -> var_kind_set kind set
    | AddrT(addr)       -> var_kind_addr kind addr
    | ElemT(elem)       -> var_kind_elem kind elem
    | TidT(th)          -> var_kind_th kind th
    | CellT(cell)       -> var_kind_cell kind cell
    | SetThT(setth)     -> var_kind_setth kind setth
    | SetIntT(setint)   -> var_kind_setint kind setint
    | SetElemT(setelem) -> var_kind_setelem kind setelem
    | SetPairT(setpair) -> var_kind_setpair kind setpair
    | PathT(path)       -> var_kind_path kind path
    | MemT(mem)         -> var_kind_mem kind mem
    | IntT(i)           -> var_kind_int kind i
    | PairT(p)          -> var_kind_pair kind p
    | ArrayT(arr)       -> var_kind_array kind arr
    | AddrArrayT(arr)   -> var_kind_addrarr kind arr
    | TidArrayT(arr)    -> var_kind_tidarr kind arr
    | BucketArrayT(arr) -> var_kind_bucketarr kind arr
    | MarkT(m)          -> var_kind_mark kind m
    | BucketT(b)        -> var_kind_bucket kind b
    | LockT(l)          -> var_kind_lock kind l
    | LockArrayT(arr)   -> var_kind_lockarr kind arr


and var_kind_expr (kind:E.var_nature) (e:expr_t) : term list =
  match e with
    Term t    -> var_kind_term kind t
  | Formula b -> var_kind_boolean kind b


and var_kind_array (kind:E.var_nature) (a:arrays) : term list =
  match a with
    VarArray v        -> if v.nature = kind then [ArrayT a] else []
  | ArrayUp(arr,_,e)  -> (var_kind_array kind arr) @ (var_kind_expr kind e)


and var_kind_addrarr (kind:E.var_nature) (a:addrarr) : term list =
  match a with
    VarAddrArray v        -> if v.nature = kind then [AddrArrayT a] else []
  | AddrArrayUp(arr,i,a)  -> (var_kind_addrarr kind arr) @
                             (var_kind_int kind i)       @
                             (var_kind_addr kind a)


and var_kind_tidarr (kind:E.var_nature) (a:tidarr) : term list =
  match a with
    VarTidArray v        -> if v.nature = kind then [TidArrayT a] else []
  | TidArrayUp(arr,i,t)  -> (var_kind_tidarr kind arr) @
                            (var_kind_int kind i)      @
                            (var_kind_th kind t)


and var_kind_bucketarr (kind:E.var_nature) (a:bucketarr) : term list =
  match a with
    VarBucketArray v        -> if v.nature = kind then [BucketArrayT a] else []
  | BucketArrayUp(arr,i,b)  -> (var_kind_bucketarr kind arr) @
                               (var_kind_int kind i)      @
                               (var_kind_bucket kind b)


and var_kind_set (kind:E.var_nature) (e:set) : term list =
  match e with
    VarSet v            -> if v.nature = kind then [SetT e] else []
  | EmptySet            -> []
  | Singl(addr)         -> (var_kind_addr kind addr)
  | Union(s1,s2)        -> (var_kind_set kind s1) @ (var_kind_set kind s2)
  | Intr(s1,s2)         -> (var_kind_set kind s1) @ (var_kind_set kind s2)
  | Setdiff(s1,s2)      -> (var_kind_set kind s1) @ (var_kind_set kind s2)
  | PathToSet(path)     -> (var_kind_path kind path)
  | AddrToSet(mem,addr) -> (var_kind_mem kind mem) @ (var_kind_addr kind addr)
  | AddrToSetAt(m,a,l)  -> (var_kind_mem kind m) @ (var_kind_addr kind a) @
                           (var_kind_int kind l)
  | SetArrayRd(arr,_)   -> (var_kind_array kind arr)
  | BucketRegion b      -> (var_kind_bucket kind b)


and var_kind_addr (kind:E.var_nature) (a:addr) : term list =
  match a with
    VarAddr v                 -> if v.nature = kind then [AddrT a] else []
  | Null                      -> []
  | Next(cell)                -> (var_kind_cell kind cell)
  | NextAt(cell,l)            -> (var_kind_cell kind cell) @
                                 (var_kind_int kind l)
  | ArrAt(cell,l)             -> (var_kind_cell kind cell) @
                                 (var_kind_int kind l)
  | FirstLocked(mem,path)     -> (var_kind_mem kind mem) @
                                 (var_kind_path kind path)
  | LastLocked(mem,path)      -> (var_kind_mem kind mem) @
                                 (var_kind_path kind path)
  | AddrArrayRd(arr,_)        -> (var_kind_array kind arr)
  | AddrArrRd(arr,i)          -> (var_kind_addrarr kind arr) @
                                 (var_kind_int kind i)
  | Malloc(data,addr,th)      -> (var_kind_elem kind data) @
                                 (var_kind_addr kind addr) @
                                 (var_kind_th kind th)
  | MallocSL(data,l)          -> (var_kind_elem kind data) @
                                 (var_kind_int kind l)
  | MallocSLK(data,l)         -> (var_kind_elem kind data) @
                                 (var_kind_int kind l)
  | PointerNext a             -> (var_kind_addr kind a)
  | PointerNextAt (a,l)       -> (var_kind_addr kind a) @
                                 (var_kind_int kind l)
  | PointerArrAt (a,l)        -> (var_kind_addr kind a) @
                                 (var_kind_int kind l)
  | BucketInit b              -> (var_kind_bucket kind b)
  | BucketEnd b               -> (var_kind_bucket kind b)


and var_kind_elem (kind:E.var_nature) (e:elem) : term list =
  match e with
    VarElem v           -> if v.nature = kind then [ElemT e] else []
  | CellData(cell)      -> (var_kind_cell kind cell)
  | ElemArrayRd(arr,_)  -> (var_kind_array kind arr)
  | PointerData a       -> (var_kind_addr kind a)
  | HavocListElem       -> []
  | HavocSkiplistElem   -> []
  | LowestElem          -> []
  | HighestElem         -> []


and var_kind_th (kind:E.var_nature) (th:tid) : term list =
  match th with
    VarTh v               -> if v.nature = kind then [TidT th] else []
  | NoTid                 -> []
  | CellLockId(cell)      -> (var_kind_cell kind cell)
  | CellLockIdAt(cell,l)  -> (var_kind_cell kind cell) @
                             (var_kind_int kind l)
  | TidArrayRd(arr,_)     -> (var_kind_array kind arr)
  | TidArrRd(arr,i)       -> (var_kind_tidarr kind arr) @
                             (var_kind_int kind i)
  | PointerLockid a       -> (var_kind_addr kind a)
  | PointerLockidAt (a,l) -> (var_kind_addr kind a) @
                             (var_kind_int kind l)
  | PairTid p             -> (var_kind_pair kind p)
  | BucketTid b           -> (var_kind_bucket kind b)
  | LockId l              -> (var_kind_lock kind l)

  
and var_kind_lock (kind:E.var_nature) (x:lock) : term list =
  match x with
    VarLock v        -> if v.nature = kind then [LockT x] else []
  | LLock (l,t)      -> (var_kind_lock kind l) @ (var_kind_th kind t)
  | LUnlock (l)      -> (var_kind_lock kind l)
  | LockArrRd (ll,i) -> (var_kind_lockarr kind ll) @ (var_kind_int kind i)


and var_kind_lockarr (kind:E.var_nature) (xx:lockarr) : term list =
  match xx with
    VarLockArray v       -> if v.nature = kind then [LockArrayT xx] else []
  | LockArrayUp(arr,i,l) -> (var_kind_lockarr kind arr) @
                            (var_kind_int kind i)       @
                            (var_kind_lock kind l)


and var_kind_cell (kind:E.var_nature) (c:cell) : term list =
  let fold f xs = List.fold_left (fun ys x -> (f kind x) @ ys) [] xs in
  match c with
    VarCell v                  -> if v.nature = kind then [CellT c] else []
  | Error                      -> []
  | MkCell(data,addr,th)       -> (var_kind_elem kind data) @
                                  (var_kind_addr kind addr) @
                                  (var_kind_th kind th)
  | MkCellMark(data,addr,th,m) -> (var_kind_elem kind data) @
                                  (var_kind_addr kind addr) @
                                  (var_kind_th kind th)     @
                                  (var_kind_mark kind m)
  | MkSLKCell(data,aa,tt)      -> (var_kind_elem kind data) @
                                  (fold var_kind_addr aa)   @
                                  (fold var_kind_th tt)
  | MkSLCell(data,aa,ta,l)     -> (var_kind_elem kind data)  @
                                  (var_kind_addrarr kind aa) @
                                  (var_kind_tidarr kind ta)  @
                                  (var_kind_int kind l)
  | CellLock(cell)             -> (var_kind_cell kind cell)
  | CellLockAt(cell,l)         -> (var_kind_cell kind cell) @
                                  (var_kind_int kind l)
  | CellUnlock(cell)           -> (var_kind_cell kind cell)
  | CellUnlockAt(cell,l)       -> (var_kind_cell kind cell) @
                                  (var_kind_int kind l)
  | CellAt(mem,addr)           -> (var_kind_mem kind mem) @
                                  (var_kind_addr kind addr)
  | CellArrayRd(arr,_)         -> (var_kind_array kind arr)


and var_kind_mark (kind:E.var_nature) (m:mark) : term list =
  match m with
    VarMark v       -> if v.nature = kind then [MarkT m] else []
  | MarkTrue        -> []
  | MarkFalse       -> []
  | Marked c        -> (var_kind_cell kind c)
  | PointerMarked a -> (var_kind_addr kind a)


and var_kind_bucket (kind:E.var_nature) (b:bucket) : term list =
  match b with
    VarBucket v  -> if v.nature = kind then [BucketT b] else []
  | MkBucket(i,e,s,t) -> (var_kind_addr kind i) @
                         (var_kind_addr kind e) @
                         (var_kind_set kind s) @
                         (var_kind_th kind t)
  | BucketArrRd(bb,i) -> (var_kind_bucketarr kind bb) @
                         (var_kind_int kind i)


and var_kind_setth (kind:E.var_nature) (s:setth) : term list =
  match s with
    VarSetTh v          -> if v.nature = kind then [SetThT s] else []
  | EmptySetTh          -> []
  | SinglTh(th)         -> (var_kind_th kind th)
  | UnionTh(s1,s2)      -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | IntrTh(s1,s2)       -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | SetdiffTh(s1,s2)    -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | SetThArrayRd(arr,_) -> (var_kind_array kind arr)


and var_kind_setint (kind:E.var_nature) (s:setint) : term list =
  match s with
    VarSetInt v          -> if v.nature = kind then [SetIntT s] else []
  | EmptySetInt          -> []
  | SinglInt(i)          -> (var_kind_int kind i)
  | UnionInt(s1,s2)      -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | IntrInt(s1,s2)       -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | SetdiffInt(s1,s2)    -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | SetIntArrayRd(arr,_) -> (var_kind_array kind arr)


and var_kind_setelem (kind:E.var_nature) (s:setelem) : term list =
  match s with
    VarSetElem v          -> if v.nature = kind then [SetElemT s] else []
  | EmptySetElem          -> []
  | SinglElem(e)          -> (var_kind_elem kind e)
  | UnionElem(s1,s2)      -> (var_kind_setelem kind s1) @
                             (var_kind_setelem kind s2)
  | IntrElem(s1,s2)       -> (var_kind_setelem kind s1) @
                             (var_kind_setelem kind s2)
  | SetdiffElem(s1,s2)    -> (var_kind_setelem kind s1) @
                             (var_kind_setelem kind s2)
  | SetToElems(s,m)       -> (var_kind_set kind s) @ (var_kind_mem kind m)
  | SetElemArrayRd(arr,_) -> (var_kind_array kind arr)


and var_kind_setpair (kind:E.var_nature) (s:setpair) : term list =
  match s with
    VarSetPair v          -> if v.nature = kind then [SetPairT s] else []
  | EmptySetPair          -> []
  | SinglPair(p)          -> (var_kind_pair kind p)
  | UnionPair(s1,s2)      -> (var_kind_setpair kind s1) @
                             (var_kind_setpair kind s2)
  | IntrPair(s1,s2)       -> (var_kind_setpair kind s1) @
                             (var_kind_setpair kind s2)
  | SetdiffPair(s1,s2)    -> (var_kind_setpair kind s1) @
                             (var_kind_setpair kind s2)
  | SetPairArrayRd(arr,_) -> (var_kind_array kind arr)


and var_kind_path (kind:E.var_nature) (p:path) : term list =
  match p with
    VarPath v                    -> if v.nature = kind then [PathT p] else []
  | Epsilon                      -> []
  | SimplePath(addr)             -> (var_kind_addr kind addr)
  | GetPath(mem,add_from,add_to) -> (var_kind_mem kind mem) @
                                    (var_kind_addr kind add_from) @
                                    (var_kind_addr kind add_to)
  | PathArrayRd(arr,_)           -> (var_kind_array kind arr)


and var_kind_mem (kind:E.var_nature) (m:mem) : term list =
  match m with
    VarMem v             -> if v.nature = kind then [MemT m] else []
  | Update(mem,add,cell) -> (var_kind_mem kind mem) @
                            (var_kind_addr kind add) @
                            (var_kind_cell kind cell)
  | MemArrayRd(arr,_)    -> (var_kind_array kind arr)


and var_kind_int (kind:E.var_nature) (i:integer) : term list =
  match i with
    IntVal _          -> []
  | VarInt v          -> if v.nature = kind then [IntT i] else []
  | IntNeg(i)         -> (var_kind_int kind i)
  | IntAdd(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntSub(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntMul(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntDiv(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntMod(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntArrayRd(arr,_) -> (var_kind_array kind arr)
  | IntSetMin(s)      -> (var_kind_setint kind s)
  | IntSetMax(s)      -> (var_kind_setint kind s)
  | HavocLevel        -> []
  | HashCode e        -> (var_kind_elem kind e)
  | PairInt p         -> (var_kind_pair kind p)


and var_kind_pair (kind:E.var_nature) (p:pair) : term list =
  match p with
    VarPair v          -> if v.nature = kind then [PairT p] else []
  | IntTidPair (i,t)   -> (var_kind_int kind i) @ (var_kind_th kind t)
  | SetPairMin ps      -> (var_kind_setpair kind ps)
  | SetPairMax ps      -> (var_kind_setpair kind ps)
  | PairArrayRd(arr,_) -> (var_kind_array kind arr)


and var_kind_atom (kind:E.var_nature) (a:atom) : term list =
  match a with
    Append(p1,p2,pres)           -> (var_kind_path kind p1) @
                                    (var_kind_path kind p2) @
                                    (var_kind_path kind pres)
  | Reach(h,add_from,add_to,p)   -> (var_kind_mem kind h) @
                                    (var_kind_addr kind add_from) @
                                    (var_kind_addr kind add_to) @
                                    (var_kind_path kind p)
  | OrderList(h,add_from,add_to) -> (var_kind_mem kind h) @
                                    (var_kind_addr kind add_from) @
                                    (var_kind_addr kind add_to)
  | Skiplist(h,s,l,a1,a2,es)     -> (var_kind_mem kind h) @
                                    (var_kind_set kind s) @
                                    (var_kind_int kind l) @
                                    (var_kind_addr kind a1) @
                                    (var_kind_addr kind a2) @
                                    (var_kind_setelem kind es)
  | Hashtbl(h,s,se,bb,i)         -> (var_kind_mem kind h) @
                                    (var_kind_set kind s) @
                                    (var_kind_setelem kind se) @
                                    (var_kind_bucketarr kind bb) @
                                    (var_kind_int kind i)
  | In(a,s)                      -> (var_kind_addr kind a) @
                                    (var_kind_set kind s)
  | SubsetEq(s_in,s_out)         -> (var_kind_set kind s_in) @
                                    (var_kind_set kind s_out)
  | InTh(th,s)                   -> (var_kind_th kind th) @
                                    (var_kind_setth kind s)
  | SubsetEqTh(s_in,s_out)       -> (var_kind_setth kind s_in) @
                                    (var_kind_setth kind s_out)
  | InInt(i,s)                   -> (var_kind_int kind i) @
                                    (var_kind_setint kind s)
  | SubsetEqInt(s_in,s_out)      -> (var_kind_setint kind s_in) @
                                    (var_kind_setint kind s_out)
  | InElem(e,s)                  -> (var_kind_elem kind e) @
                                    (var_kind_setelem kind s)
  | SubsetEqElem(s_in,s_out)     -> (var_kind_setelem kind s_in) @
                                    (var_kind_setelem kind s_out)
  | InPair(p,s)                  -> (var_kind_pair kind p) @
                                    (var_kind_setpair kind s)
  | SubsetEqPair(s_in,s_out)     -> (var_kind_setpair kind s_in) @
                                    (var_kind_setpair kind s_out)
  | Less(i1,i2)                  -> (var_kind_int kind i1) @
                                    (var_kind_int kind i2)
  | Greater(i1,i2)               -> (var_kind_int kind i1) @
                                    (var_kind_int kind i2)
  | LessEq(i1,i2)                -> (var_kind_int kind i1) @
                                    (var_kind_int kind i2)
  | GreaterEq(i1,i2)             -> (var_kind_int kind i1) @
                                    (var_kind_int kind i2)
  | LessTid(t1,t2)               -> (var_kind_th kind t1) @
                                    (var_kind_th kind t2)
  | LessElem(e1,e2)              -> (var_kind_elem kind e1) @
                                    (var_kind_elem kind e2)
  | GreaterElem(e1,e2)           -> (var_kind_elem kind e1) @
                                    (var_kind_elem kind e2)
  | Eq(exp)                      -> (var_kind_eq kind exp)
  | InEq(exp)                    -> (var_kind_ineq kind exp)
  | BoolVar v                    -> if v.nature = kind then [VarT v] else []
  | BoolArrayRd(arr,_)           -> (var_kind_array kind arr)


and var_kind_fs () = F.make_fold
                       F.GenericLiteralFold
                       (fun info a -> var_kind_atom info a)
                       (fun _ -> [])
                       (@)


and var_kind_eq (kind:E.var_nature) ((t1,t2):eq) : term list =
  (var_kind_term kind t1) @ (var_kind_term kind t2)


and var_kind_ineq (kind:E.var_nature) ((t1,t2):diseq) : term list =
  (var_kind_term kind t1) @ (var_kind_term kind t2)
    

and var_kind_boolean (kind:E.var_nature) (b:boolean) : term list =
  F.formula_fold (var_kind_fs()) kind b


let var_kind (kind:E.var_nature) (e:expr_t) : term list =
  let ghost_list = var_kind_expr kind e in
  let ghost_set = List.fold_left (fun set e -> TermSet.add e set)
                               (TermSet.empty)
                               (ghost_list)
  in
    TermSet.elements ghost_set





(* PRINTING FUNCTIONS *)
let pad (n:int) (st:string) (g:string) =
  let fill (n:int) (s:string) =
    (String.make n '\t') ^ s in
  fill n st ^ "\n" ^
    (match g with
      "" -> ""
    | _  -> fill n "+-------\n" ^ g ^ fill n "+-------\n"
    )

let unit_cmd_to_str (op:unit_operation) : string =
  match op with
    UnitLock a         -> sprintf "%s->lock" (addr_to_str false a)
  | UnitUnlock a       -> sprintf "%s->unlock" (addr_to_str false a)
  | UnitLockAt (a,l)   -> sprintf "%s->lock[%s]" (addr_to_str false a)
                                                 (integer_to_str false l)
  | UnitUnlockAt (a,l) -> sprintf "%s->unlock[%s]" (addr_to_str false a)
                                                   (integer_to_str false l)


let rec statement_to_str (n:int) (s:statement_t) =
  let pos info = match info with
                   Some i -> sprintf "%i:" i.pos
                 | None   -> ""
  in
  match s with
    StSkip (g,opt) ->
      pos opt ^ pad n "skip" (Option.map_default (statement_to_str n) "" g)
  | StAssert (b,g,opt) ->
      pos opt ^ pad n (sprintf "assert (%s)" (boolean_to_simp_str b))
        (Option.map_default (statement_to_str n) "" g)
  | StAwait (b,g,opt) ->
      pos opt ^ pad n (sprintf "await (%s)" (boolean_to_simp_str b))
        (Option.map_default (statement_to_str n) "" g)
  | StNonCrit (g,opt) ->
      pos opt ^ pad n "noncritical"
        (Option.map_default (statement_to_str n) "" g)
  | StCrit (g,opt) ->
      pos opt ^ pad n "critical"
        (Option.map_default (statement_to_str n) "" g)
  | StIf (b,t,f,g,opt)   ->
      pos opt ^ pad n ("if ("^(boolean_to_simp_str b)^") then")
        (Option.map_default (statement_to_str n) "" g) ^
                            (statement_to_str (n+1) t) ^
            (match f with
             | Some st -> pad n "else" "" ^ (statement_to_str (n+1) st)
             | None   -> ""
            ) ^ pad n "end if" ""
  | StWhile (b,st,g,opt) ->
      pos opt ^ pad n ("while ("^ (boolean_to_simp_str b) ^")")
        (Option.map_default (statement_to_str n) "" g)  ^
                            (statement_to_str (n+1) st) ^ pad n "end while" ""
  | StSelect (st,_,opt) ->
      pos opt ^ pad n "choose" "" ^ (String.concat (pad n "or" "")
        (List.map (statement_to_str (n+1)) st)) ^ pad n "end choose" ""
  | StAssign (v,e,g,opt) ->
      pos opt ^ pad n ((term_to_str_aux false v) ^ " := " ^
        (expr_to_str_aux false e))
        (Option.map_default (statement_to_str n) "" g)
  | StUnit (u_cmd,g,opt) ->
      pos opt ^ pad n (unit_cmd_to_str u_cmd)
        (Option.map_default (statement_to_str n) "" g)
  | StAtomic (st,g,opt) ->
      pos opt ^ pad n "{" "" ^
        (String.concat "" (List.map (statement_to_str (n+1)) st)) ^ pad n "}"
        (Option.map_default (statement_to_str n) "" g)
  | StSeq xs ->
      String.concat "" (List.map (statement_to_str n) xs)
  | StCall (t_opt,proc,params,g,opt) ->
      pos opt ^ pad n ((match t_opt with
                        | Some t -> (term_to_str t) ^ " := "
                        | None    -> "") ^
      "call " ^ proc ^ "(" ^
      (String.concat "," $ List.map (term_to_str_aux false) params) ^ ")")
      (Option.map_default (statement_to_str n) "" g)
  | StReturn (t,g,opt) ->
      pos opt ^ pad n ("return (" ^ Option.map_default term_to_str "" t ^ ")")
        (Option.map_default (statement_to_str n) "" g)



(* Statement formula manipulation *)


(* STATEMENT INFORMATION *)
let rec get_st_info_aux (st:statement_t) : st_info_t =
  match st with
    StSkip (_,Some info)       -> info
  | StAssert (_,_,Some info)   -> info
  | StAwait (_,_,Some info)    -> info
  | StNonCrit (_,Some info)    -> info
  | StCrit (_,Some info)       -> info
  | StIf (_,_,_,_,Some info)   -> info
  | StWhile (_,_,_,Some info)  -> info
  | StSelect (_,_,Some info)   -> info
  | StAssign (_,_,_,Some info) -> info
  | StUnit (_,_,Some info)     -> info
  | StAtomic (_,_,Some info)   -> info
  | StSeq xs                   -> get_st_info_aux (LeapLib.lastElem xs)
  | StCall (_,_,_,_,Some info) -> info
  | StReturn (_,_,Some info)   -> info
  | _                          -> raise(Statement_info_unavailable)


let get_st_info (st:statement_t) : st_info_t =
  try
    get_st_info_aux st
  with
    Statement_info_unavailable ->
      begin
        Interface.Err.msg "Information unavailable" $
                  sprintf "Information for statement\n%s\n could not be found"
                  (statement_to_str 1 st);
        raise(Statement_info_unavailable)
      end


let get_st_pos (st:statement_t) : E.pc_t =
  (get_st_info st).pos


let get_st_else_pos (st:statement_t) : E.pc_t =
  (get_st_info st).else_pos


let get_st_next_pos (st:statement_t) : E.pc_t =
  (get_st_info st).next_pos


let get_st_call_pos (st:statement_t) : E.pc_t option =
  (get_st_info st).call_pos


let get_forced_st_pos (st:statement_t) : E.pc_t =
  try
    (get_st_info_aux st).pos
  with
    Statement_info_unavailable -> -1


let get_forced_st_else_pos (st:statement_t) : E.pc_t =
  try
    (get_st_info_aux st).else_pos
  with
    Statement_info_unavailable -> -1


let get_forced_st_next_pos (st:statement_t) : E.pc_t =
  try
    (get_st_info_aux st).next_pos
  with
    Statement_info_unavailable -> -1


let rec get_last_st_info (st:statement_t) : st_info_t =
  match st with
    StSeq [] -> raise(Empty_sequence)
  | StSeq xs -> get_last_st_info (lastElem xs)
  | StIf (_, t_branch, e_branch, _, _) -> begin
                                            match e_branch with
                                              None -> get_last_st_info t_branch
                                            | Some ys -> get_last_st_info ys
                                          end
  | StWhile (_, loop, _, _) -> get_last_st_info loop
  | s -> get_st_info s


let rec get_last_st_pos (st:statement_t) : E.pc_t =
  match st with
  | StIf (_,t,e,_,_) -> begin
                          match e with
                          | None      -> get_last_st_pos t
                          | Some e_st -> get_last_st_pos e_st
                        end
  | StWhile (_,e,_,_) -> get_last_st_pos e
  | StSelect (xs,_,_) -> begin
                              match xs with
                              | [] -> (get_last_st_info st).pos
                              | ys -> get_last_st_pos (lastElem ys)
                            end
  | StSeq xs -> begin
                  match xs with
                  | [] -> -1
                  | ys -> get_last_st_pos (lastElem ys)
                end
  | _ -> let info = get_last_st_info st in
           info.pos



let rec get_fst_st_pos (st:statement_t) : E.pc_t =
  match st with
    StSeq [] -> raise(Empty_sequence)
  | StSeq xs -> get_fst_st_pos (List.hd xs)
  | s        -> get_st_pos s


let rec enabling_condition_aux (is_ghost:bool)
                               (th:E.V.shared_or_local)
                               (st:statement_t) : E.formula list list =
  let e_cond          = enabling_condition_aux in
  let to_expr         = boolean_to_expr_formula>>(E.param th) in
  let to_addr a       = E.param_addr th (addr_to_expr_addr a) in
  let to_cell         = cell_to_expr_cell in
  let read_at a       = E.CellLockId(E.CellAt(E.heap, to_addr a)) in
  let read_at_lvl a l = E.CellLockIdAt(E.CellAt(E.heap, to_addr a),
                                       integer_to_expr_integer l) in
  let ghost gc        = Option.map_default (fun stm ->
                          List.flatten $ e_cond true th stm
                        ) [] gc in
  let pos info = match info with
                   None   -> []
                 | Some i -> if is_ghost then
                               []
                             else
                               [E.atom_form (E.PC(i.pos, th, false))]
  in
  match st with
    StSkip    (      g,info) -> [pos info @ ghost g]
  | StAssert  (c,    g,info) -> [(to_expr c) :: pos info @ ghost g]
  | StAwait   (c,    g,info) -> [(to_expr c) :: pos info @ ghost g]
  | StNonCrit (      g,info) -> [pos info @ ghost g]
  | StCrit    (      g,info) -> [pos info @ ghost g]
  | StIf      (c,_,_,g,info) -> [(to_expr c) :: pos info @ ghost g;
                                 (to_expr (F.Not c)) :: pos info @ ghost g]
  | StWhile   (c,_,  g,info) -> [(to_expr c) :: pos info @ ghost g;
                                 (to_expr (F.Not c)) :: pos info @ ghost g]
  | StSelect  (_,    g,info) -> [pos info @ ghost g]
  | StAssign  (_,e,  g,info) ->
      let cond =
        begin
          match e with
            Term(CellT(CellLock c))   ->
              [E.eq_tid (E.CellLockId (to_cell c)) E.NoTid]
          | Term(CellT(CellUnlock c)) ->
              begin
                match th with
                | E.V.Local t -> [E.eq_tid (E.CellLockId (to_cell c)) (E.VarTh t)]
                | E.V.Shared  -> [E.eq_tid (E.CellLockId (to_cell c)) E.NoTid]
              end
          | _ -> []
        end
      in
        [cond @ pos info @ ghost g]
  | StUnit    (op,   g,info) ->
      let cond =
        begin
          match op with
          | UnitLock a   -> [E.eq_tid (read_at a) E.NoTid]
          | UnitUnlock a ->
              begin
                match th with
                | E.V.Local t -> [E.eq_tid   (read_at a) (E.VarTh t)]
                | E.V.Shared  -> [E.ineq_tid (read_at a) E.NoTid]
              end
          | UnitLockAt (a,l)   -> [E.eq_tid (read_at_lvl a l) E.NoTid]
          | UnitUnlockAt (a,l) ->
              begin
                match th with
                | E.V.Local t -> [E.eq_tid   (read_at_lvl a l) (E.VarTh t)]
                | E.V.Shared  -> [E.ineq_tid (read_at_lvl a l) E.NoTid]
              end
        end
      in
        [cond @ pos info @ ghost g]
  | StAtomic  (_, g,info) -> [pos info @ ghost g]
  (* ALE: Complete the implementation of the case above. *)
  | StSeq _                  -> [[F.True]]
  | StCall (_,_,_,g,info)    -> [pos info @ ghost g]
  | StReturn (_,g,info)      -> [pos info @ ghost g]





let enabling_condition (th:E.V.shared_or_local) (st:statement_t) : E.formula list =
  List.map F.conj_list (enabling_condition_aux false th st)


let addr_used_in_unit_op (op:unit_operation) : E.addr =
  match op with
  | UnitLock a         -> addr_to_expr_addr a
  | UnitUnlock a       -> addr_to_expr_addr a
  | UnitLockAt (a,_)   -> addr_to_expr_addr a
  | UnitUnlockAt (a,_) -> addr_to_expr_addr a

let level_used_in_unit_op (op:unit_operation) : E.integer =
  match op with
  | UnitLock _         -> E.IntVal 0
  | UnitUnlock _       -> E.IntVal 0
  | UnitLockAt (_,l)   -> integer_to_expr_integer l
  | UnitUnlockAt (_,l) -> integer_to_expr_integer l


let get_unit_op (op:unit_operation) : unit_op =
  match op with
    UnitLock _     -> Lock
  | UnitUnlock _   -> Unlock
  | UnitLockAt _   -> Lock
  | UnitUnlockAt _ -> Unlock

