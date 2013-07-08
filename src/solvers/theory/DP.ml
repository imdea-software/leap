

exception Unknown_dp_str of string


type t =
  | NoDP
  | Loc
  | Num
  | Tll
  | Tsl
  | Tslk of int


type call_tbl_t = (t,int) Hashtbl.t


let def_dp_list : t list = [ Num; Loc; Tll; Tsl; Tslk 0 ]


let to_str (dp:t) : string =
  match dp with
  | NoDP   -> ""
  | Loc    -> "loc"
  | Num    -> "num"
  | Tll    -> "tll"
  | Tsl    -> "tsl"
  | Tslk k -> let arg = if k > 0 then string_of_int k else "_" in
                "tslk[" ^ arg ^ "]"


let from_str (str:string) : t =
  match str with
  | ""    -> NoDP
  | "loc" -> Loc
  | "num" -> Num
  | "tll" -> Tll
  | "tsl" -> Tsl
  | s     -> let regexp = Str.regexp "tslk\\[[0-9]+\\]" in
             if Str.string_match regexp s 0 then
               let k = String.sub s 5 (String.length s - 6) in
               Tslk (int_of_string k)
             else
               raise(Unknown_dp_str s)


let get_tslk_param (dp:t) : int =
  match dp with
  | Tslk k -> k
  | _      -> 1

(*******************************)
(*  COUNTING CALLS TO EACH DP  *)
(*******************************)

let new_call_tbl() : call_tbl_t =
  Hashtbl.create 10


let clear_call_tbl (tbl:call_tbl_t) : unit =
  Hashtbl.clear tbl


let copy_call_tbl (tbl:call_tbl_t) : call_tbl_t =
  Hashtbl.copy tbl


let add_dp_calls (tbl:call_tbl_t) (dp:t) (n:int) : unit =
  try
    Hashtbl.replace tbl dp ((Hashtbl.find tbl dp) + n)
  with _ -> Hashtbl.add tbl dp n


let combine_call_table (src_tbl:call_tbl_t) (dst_tbl:call_tbl_t) : unit =
  Hashtbl.iter (add_dp_calls dst_tbl) src_tbl
