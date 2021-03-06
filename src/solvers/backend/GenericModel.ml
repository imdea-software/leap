
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



open LeapLib

module Expr = Expression


(** A constant, function, record label or field label identifier*)
type id = string

(** A name for the a sort *)
type sort = string

(** Types that can be taken by an identifier within a model *)
type typeDecl = Const of sort | Fun of sort list * sort list

(** A map from identifier to the type of each of them *)
type sort_map_t = (id, typeDecl) LeapIdMap.t

(** A way to identifier each possible value in the value table *)
type value_id = int

(** The representation of a single values *)
type vals = string

(** Type for variables in the model *)
type var = Var of id | Function of id * (id option) list

(** Type representation for values within a model *)
type value = Single of string | Record of (id * (id * vals) list)

(** Type to store functions information *)
type fun_table_t = ((id option) list, value_id) LeapIdMap.t


(** A representation of a function *)
type fun_t = ((id option) list, value) Hashtbl.t


(** A generic model *)
type t =
  {
    id_counter   : int ref                     ;
    const_map    : (id, value_id) LeapIdMap.t  ;
    fun_map      : (id, fun_table_t) Hashtbl.t  ;
    values       : (value_id, value) Hashtbl.t ;
    aux_sort_map : sort_map_t ;
  }


exception Undefined of id


(* Sort names *)
let bool_s      : string = "Bool"
let int_s       : string = "Int"
let addr_s      : string = "Address"
let set_s       : string = "Set"
let elem_s      : string = "Elem"
let tid_s       : string = "Tid"
let cell_s      : string = "Cell"
let setth_s     : string = "Setth"
let setint_s    : string = "Setint"
let setelem_s   : string = "SetElem"
let setpair_s   : string = "SetPair"
let path_s      : string = "Path"
let level_s     : string = "Level"
let heap_s      : string = "Heap"
let bool_s      : string = "Bool"
let int_s       : string = "Int"
let pair_s      : string = "Pair"
let array_s     : string = "Array"
let addrarr_s   : string = "AddrArr"
let tidarr_s    : string = "TidArr"
let bucketarr_s : string = "BucketArr"
let mark_s      : string = "Mark"
let bucket_s    : string = "Bucket"
let lock_s      : string = "Lock"
let lockarr_s   : string = "LockArr"
let unk_s       : string = "Unknown"
let loc_s       : string = "Loc"


(* Sort map functions *)

let new_sort_map () : sort_map_t =
  LeapIdMap.create 10


let clear_sort_map (sm:sort_map_t) : unit =
  LeapIdMap.clear sm


let copy_sort_map (sm:sort_map_t) : sort_map_t =
  LeapIdMap.copy sm


let normalize_sort (s:sort) : sort =
  String.capitalize s


let sm_decl_const (sm:sort_map_t) (i:id) (s:sort) : unit =
  LeapIdMap.add sm i (Const (normalize_sort s))


let sm_decl_fun (sm:sort_map_t) (i:id) (ds:sort list) (cs:sort list) : unit =
  let ds' = List.map normalize_sort ds in
  let cs' = List.map normalize_sort cs
  in
    LeapIdMap.add sm i (Fun (ds',cs'))


let sm_dom (sm:sort_map_t) : id list =
  LeapIdMap.dom sm


let sm_codom (sm:sort_map_t) : typeDecl list =
  LeapIdMap.codom sm


let sm_dom_of_type (sm:sort_map_t) (t:typeDecl) : id list =
  try
    LeapIdMap.find_dom sm t
  with _ -> []


let sm_union (sm1:sort_map_t) (sm2:sort_map_t) : sort_map_t =
  LeapIdMap.union sm1 sm2


(* Generic model functions *)

let gen_fresh_id (m:t) : value_id =
  let _ = incr m.id_counter
  in
    !(m.id_counter)


let new_model () : t =
  {
    id_counter   = ref 0;
    const_map    = LeapIdMap.create 10;
    fun_map      = Hashtbl.create 10;
    values       = Hashtbl.create 10;
    aux_sort_map = new_sort_map();
  }


let is_empty_model (m:t) : bool =
  !(m.id_counter) = 0 &&
  LeapIdMap.is_empty m.const_map &&
  Hashtbl.length m.fun_map = 0 &&
  Hashtbl.length m.values = 0 &&
  LeapIdMap.is_empty m.aux_sort_map
  


let clear_model (m:t) : unit =
  m.id_counter := 0;
  LeapIdMap.clear m.const_map;
  Hashtbl.clear m.fun_map;
  Hashtbl.clear m.values;
  LeapIdMap.clear m.aux_sort_map


let copy_model (m:t) : t =
  {
    id_counter = m.id_counter                    ;
    const_map  = LeapIdMap.copy m.const_map      ;
    fun_map    = Hashtbl.copy m.fun_map          ;
    values     = Hashtbl.copy m.values           ;
    aux_sort_map = LeapIdMap.copy m.aux_sort_map ;
  }


let decl_const (m:t) (i:id) (v:value) : unit =
  if (LeapIdMap.mem m.const_map i) then
    Hashtbl.add m.values (LeapIdMap.find_id m.const_map i) v
  else
    let j = gen_fresh_id m in
    let _ = LeapIdMap.add m.const_map i j
    in
      Hashtbl.add m.values j v


let decl_fun (m:t) (i:id) (params:(id option) list) (v:value) : unit =
  if (Hashtbl.mem m.fun_map i) then
    let tbl = Hashtbl.find m.fun_map i in
    if LeapIdMap.mem tbl params then
      Hashtbl.add m.values (LeapIdMap.find_id tbl params) v
    else
      let j = gen_fresh_id m in
      let _ = LeapIdMap.add tbl params j
      in
        Hashtbl.add m.values j v
  else
    let tbl = LeapIdMap.create 10 in
    let _ = Hashtbl.add m.fun_map i tbl in
    let j = gen_fresh_id m in
    let _ = LeapIdMap.add tbl params j
    in
      Hashtbl.add m.values j v


let unify (m:t) (v1:var) (v2:var) : unit =
  let get_id (y:var) =
    match y with
    | Var v -> begin
                 try
                   Some (LeapIdMap.find_id m.const_map v)
                 with _ -> None
               end
    | Function (f,ps) -> if Hashtbl.mem m.fun_map f then
                           try
                             Some (LeapIdMap.find_id
                                    (Hashtbl.find m.fun_map f) ps)
                           with _ -> None
                         else
                           let tbl = LeapIdMap.create 10 in
                           let _ = Hashtbl.add m.fun_map f tbl in
                           let j = gen_fresh_id m in
                           let _ = LeapIdMap.add tbl ps j
                           in
                             Some j in
  let add_id (y:var) (i:value_id) =
    match y with
    | Var v           -> LeapIdMap.add m.const_map v i
    | Function (f,ps) -> LeapIdMap.add (Hashtbl.find m.fun_map f) ps i
  in
    match (get_id v1, get_id v2) with
    | (Some j1, Some j2) -> LeapIdMap.unify_id m.const_map j2 j1;
                            Hashtbl.iter (fun _ tbl ->
                              LeapIdMap.unify_id tbl j2 j1;
                            ) m.fun_map
    | (Some j1, None   ) -> add_id v2 j1
    | (None   , Some j2) -> add_id v1 j2
    | (None   , None   ) -> let j = gen_fresh_id m
                            in
                              add_id v1 j;
                              add_id v2 j

let get_const (m:t) (i:id) : value =
  try
    Hashtbl.find m.values (LeapIdMap.find_id m.const_map i)
  with _ -> raise(Undefined i)


let get_fun_def (m:t) (i:id) : value option =
  try
    Some (Hashtbl.find m.values (LeapIdMap.find_id m.const_map i))
  with _ -> None


let get_aux_sort_map (m:t) : sort_map_t =
  m.aux_sort_map


let get_fun (m:t) (i:id) : fun_t =
  let f = Hashtbl.create 10 in
  try
    let tbl = Hashtbl.find m.fun_map i in
    let _ = LeapIdMap.iter (fun args v ->
              try
                Hashtbl.add f args (Hashtbl.find m.values v)
              with _ -> ()
            ) tbl
    in
      f
  with _ -> f



(* Pretty printing functions *)
let value_to_str (v:value) : string =
  match v with
  | Single v      -> v
  | Record (r,xs) -> let xs_str = List.map (fun (i,v) -> i ^ "::"  ^ v) xs
                     in
                       Printf.sprintf "%s {%s}" r (String.concat "; " xs_str)


let params_to_str (ids:(id option) list) : string =
  String.concat "," $ List.map (fun id ->
                        match id with
                        | None   -> "_"
                        | Some s -> s
                      ) ids


let model_to_str (m:t) : string =
  let c_str = LeapIdMap.fold (fun c i str ->
                let val_str = try
                                value_to_str (Hashtbl.find m.values i)
                              with _ -> "undef"
                in
                  str ^ Printf.sprintf "%s = %s\n" c val_str
              ) m.const_map "" in
  let f_str = Hashtbl.fold (fun f tbl str ->
                let p_str = LeapIdMap.fold (fun ids v str ->
                              try
                                str ^ Printf.sprintf "%s (%s) = %s\n"
                                        f (params_to_str ids)
                                        (value_to_str (Hashtbl.find m.values v))
                              with _ -> str
                            ) tbl ""
                in
                  str ^ p_str
              ) m.fun_map ""
  in
    c_str ^ f_str


let typedecl_to_str (t:typeDecl) : string =
  match t with
  | Const s     -> s
  | Fun (ds,rs) -> (String.concat " x " ds) ^ " -> " ^ (String.concat " x " rs)


let const_to_str (m:t) (i:id) : string =
  try
    let value = Hashtbl.find m.values (LeapIdMap.find_id m.const_map i)
    in
      Printf.sprintf "%s = %s\n" i (value_to_str value)
  with _ -> ""


let fun_to_str (m:t) (i:id) : string =
  try
    let tbl = Hashtbl.find m.fun_map i in
    let f_str = LeapIdMap.fold (fun ps v str ->
                  try
                    str ^ (Printf.sprintf "%s(%s) = %s\n"
                            i (params_to_str ps)
                            (value_to_str (Hashtbl.find m.values v)))
                  with _ -> str
                ) tbl ""
    in
      f_str
  with _ -> ""


let model_with_sorts_to_str (m:t) (s:sort_map_t) : string =
  let sort_list = LeapIdMap.codom s in
  let str = List.fold_left (fun str sort ->
              let sort_str = typedecl_to_str sort in
              let dom = LeapIdMap.find_dom s sort in
              let this_str = List.fold_left (fun str d ->
                               let const_str = const_to_str m d in
                               let fun_str = fun_to_str m d
                               in
                                 str ^ const_str ^ fun_str
                             ) "" dom
              in
                str ^ "\n\n" ^ sort_str ^ "\n" ^ this_str
            ) "" sort_list
  in
    str


let id_to_str (m:t) (i:id) : string =
  let c_str = try
                let c = get_const m i
                in
                  Printf.sprintf "%s = %s\n" i (value_to_str c)
              with _ -> "" in
  let f_str = if Hashtbl.mem m.fun_map i then
                Hashtbl.fold (fun ps v str ->
                  str ^ Printf.sprintf "%s[%s] = %s\n" i
                          (params_to_str ps) (value_to_str v)
                ) (get_fun m i) ""
              else
                ""
  in
    c_str ^ f_str


let id_list_to_str (m:t) (ids:id list) : string =
  List.fold_left (fun str x ->
    str ^ (id_to_str m x)
  ) "" ids

let conv_sort (s:Expression.sort) : sort =
  match s with
  | Expr.Set           -> set_s
  | Expr.Elem          -> elem_s
  | Expr.Tid           -> tid_s
  | Expr.Addr          -> addr_s
  | Expr.Cell          -> cell_s
  | Expr.SetTh         -> setth_s
  | Expr.SetInt        -> setint_s
  | Expr.SetElem       -> setelem_s
  | Expr.SetPair       -> setpair_s
  | Expr.Path          -> path_s
  | Expr.Mem           -> heap_s
  | Expr.Bool          -> bool_s
  | Expr.Int           -> int_s
  | Expr.Pair          -> pair_s
  | Expr.Array         -> array_s
  | Expr.AddrArray     -> addrarr_s
  | Expr.TidArray      -> tidarr_s
  | Expr.BucketArray   -> bucketarr_s
  | Expr.Mark          -> mark_s
  | Expr.Bucket        -> bucket_s
  | Expr.Lock          -> lock_s
  | Expr.LockArray     -> lockarr_s
  | Expr.Unknown       -> unk_s


let search_type_to_str (model:t) (sm:sort_map_t) (s:sort) : string =
  let xs = sm_dom_of_type sm (Const s) @
           sm_dom_of_type sm (Fun ([tid_s],[s]))
  in
    id_list_to_str model xs


let search_sets_to_str (model:t) (sm:sort_map_t) (s:sort) : string =
  let set_to_str (id:id) : string =
    let elems = Hashtbl.fold (fun es b xs ->
                  match (es,b) with
                  | ([Some e], Single "true") -> e :: xs
                  | ([None]  , Single "true") -> "_" :: xs
                  | _                            -> xs
                ) (get_fun model id) [] in
    Printf.sprintf "%s = {%s}\n" id (String.concat "," elems) in
  let local_set_to_str (id:id) : string =
    let locTbl = Hashtbl.create 10 in
    let _ = Hashtbl.iter (fun es b ->
              match es with
              | x::y::[] -> begin
                              try
                                let zs = Hashtbl.find locTbl x in
                                Hashtbl.replace locTbl x ((y,b)::zs)
                              with
                                _ -> Hashtbl.add locTbl x [(y,b)]
                            end
              | _ -> ()
            ) (get_fun model id) in
    Hashtbl.fold (fun t es str ->
      let elems = List.fold_left (fun xs elem ->
                    match elem with
                    | (Some e, Single "true") -> e::xs
                    | (None  , Single "true") -> "_"::xs
                    | _                          -> xs
                  ) [] es in
      str ^ (Printf.sprintf "%s[%s] = {%s}\n" id (Option.default "_" t)
              (String.concat "," elems))
    ) locTbl "" in
  let gSets = sm_dom_of_type sm (Const s) in
  let lSets = sm_dom_of_type sm (Fun ([tid_s],[s])) in
    (List.fold_left (fun str s -> str ^ set_to_str s) "" gSets) ^
    (List.fold_left (fun str s -> str ^ local_set_to_str s) "" lSets)
