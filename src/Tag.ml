
exception Undefined_tag of string
exception Duplicated_tag of string


(* tag *)
type f_tag =
  {
    master : string;
    subtag : string;
  }


(* returns the string identifying a tag *)
let tag_id (t:f_tag) : string =
  match t.subtag with
  | "" -> t.master
  | _ -> t.master ^"::"^ t.subtag


let master_id (t:f_tag) : string =
  t.master


let subtag_id (t:f_tag) : string =
  t.subtag


(* builds a new tag from a string identifier *)
let new_tag (mst:string) (sub:string) : f_tag =
  { master = mst; subtag = sub; }


(* Set of tags *)
module TagSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = f_tag
  end )


module type S =
  sig

    type formula
    type f_info
    type tag_table

    val new_info    : f_info

    val tag_table_new         : tag_table
    val tag_table_clear       : tag_table -> unit
    val tag_table_add         : tag_table ->
                                f_tag ->
                                formula ->
                                f_info ->
                                unit
    val tag_table_mem         : tag_table -> f_tag -> bool
    val tag_table_find        : tag_table -> f_tag -> formula * f_info
    val tag_table_get_formula : tag_table -> f_tag -> formula
    val tag_table_get_info    : tag_table -> f_tag -> f_info
    val tag_table_size        : tag_table -> int
  end


module Make (E:GenericExpression.S) =
  struct

    (* The type of stored formulas *)
    type formula = E.formula

    (* formula properties or extra information *)
    type f_info = unit

    (* mapping table for tags *)
    type tag_table = (f_tag, formula * f_info) Hashtbl.t


    (* Configuration *)
    let tag_table_initial_size = 20


    let new_info : f_info = ()


    (* Manipulation of tag table *)
    let tag_table_new : tag_table =
      Hashtbl.create tag_table_initial_size

    let tag_table_clear (tbl:tag_table) : unit =
      Hashtbl.clear tbl

    let tag_table_add (tbl:tag_table) (t:f_tag) (phi:formula) (info:f_info)
          : unit =
      Hashtbl.add tbl t (phi, info)

    let tag_table_mem (tbl:tag_table) (t:f_tag) : bool =
      Hashtbl.mem tbl t

    let tag_table_find (tbl:tag_table) (t:f_tag) : (formula * f_info) =
      try
        Hashtbl.find tbl t
      with
        _ -> raise (Undefined_tag(tag_id t))

    let tag_table_get_formula (tbl:tag_table) (t:f_tag) : formula =
      fst (tag_table_find tbl t)

    let tag_table_get_info (tbl:tag_table) (t:f_tag) : f_info =
      snd (tag_table_find tbl t)

    let tag_table_size (tbl:tag_table) : int =
      Hashtbl.length tbl
  end
