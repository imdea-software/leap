module Expr = Expression

exception Undefined_tag of string
exception Duplicated_tag of string

(* tag *)
type f_tag = string

(* formula properties or extra information *)
type f_info = unit


(* mapping table for tags *)
type tag_table = (f_tag, Expr.formula * f_info) Hashtbl.t

(* Set of tags *)
module TagSet = Set.Make(
  struct
    let compare = String.compare
    type t = f_tag
  end )

(* Configuration *)
let tag_table_initial_size = 20


(* builds a new tag from a string identifier *)
let new_tag (str:string) : f_tag = str

let new_info : f_info = ()

(* returns the string identifying a tag *)
let tag_id (t:f_tag) : string = t


(* Manipulation of tag table *)
let tag_table_new : tag_table =
  Hashtbl.create tag_table_initial_size

let tag_table_clear (tbl:tag_table) : unit =
  Hashtbl.clear tbl

let tag_table_add (tbl:tag_table) (t:f_tag) (phi:Expr.formula) (info:f_info) : unit =
  Hashtbl.add tbl t (phi, info)

let tag_table_mem (tbl:tag_table) (t:f_tag) : bool =
  Hashtbl.mem tbl t

let tag_table_find (tbl:tag_table) (t:f_tag) : (Expr.formula * f_info) =
  try
    Hashtbl.find tbl t
  with
    _ -> raise (Undefined_tag t)

let tag_table_get_formula (tbl:tag_table) (t:f_tag) : Expr.formula =
  fst (tag_table_find tbl t)

let tag_table_get_info (tbl:tag_table) (t:f_tag) : f_info =
  snd (tag_table_find tbl t)

let tag_table_size (tbl:tag_table) : int =
  Hashtbl.length tbl
