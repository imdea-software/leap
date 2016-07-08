
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




exception Unknown_dp_str of string


type t =
  | NoDP
  | Loc
  | Num
  | Pairs
  | Tll
  | Tsl
  | Tslk of int
  | Thm


type call_tbl_t =
  {
    calls : (t,int) Hashtbl.t;
    solving : (int,t) Hashtbl.t;
  }


let def_dp_list : t list = [ Num; Loc; Tll; Tsl; Tslk 0 ]


let to_str (dp:t) : string =
  match dp with
  | NoDP   -> ""
  | Loc    -> "loc"
  | Num    -> "num"
  | Pairs  -> "pairs"
  | Tll    -> "tll"
  | Tsl    -> "tsl"
  | Tslk k -> let arg = if k > 0 then string_of_int k else "_" in
                "tslk[" ^ arg ^ "]"
  | Thm    -> "thm"


let from_str (str:string) : t =
  match str with
  | ""      -> NoDP
  | "loc"   -> Loc
  | "num"   -> Num
  | "pairs" -> Pairs
  | "tll"   -> Tll
  | "tsl"   -> Tsl
  | "thm"   -> Thm
  | s       -> let regexp = Str.regexp "tslk\\[[0-9]+\\]" in
               if Str.string_match regexp s 0 then
                 let k = String.sub s 5 (String.length s - 6) in
                 Tslk (int_of_string k)
               else
                 raise(Unknown_dp_str s)


let get_tslk_param (dp:t) : int =
  match dp with
  | Tslk k -> k
  | _      -> 1


let stronger (dp1:t) (dp2:t) : t =
  match (dp1,dp2) with
  | (Tsl, _) | (_, Tsl) -> Tsl
  | (Tslk i, Tslk j) -> if i>j then dp1 else dp2
  | (Tslk _, _) -> dp1
  | (_, Tslk _) -> dp2
  | (Tll, _)   | (_, Tll) -> Tll
  | (Thm, _)   | (_, Thm) -> Thm
  | (Pairs, _) | (_, Pairs) -> Num
  | (Num, _)   | (_, Num) -> Num
  | (Loc, _)   | (_, Loc) -> Loc
  | _ -> NoDP
  

(*******************************)
(*  COUNTING CALLS TO EACH DP  *)
(*******************************)

let new_call_tbl() : call_tbl_t =
  {
    calls = Hashtbl.create 10;
    solving = Hashtbl.create 10;
  }


let clear_call_tbl (tbl:call_tbl_t) : unit =
  Hashtbl.clear tbl.calls;
  Hashtbl.clear tbl.solving


let copy_call_tbl (tbl:call_tbl_t) : call_tbl_t =
  {
    calls = Hashtbl.copy tbl.calls;
    solving = Hashtbl.copy tbl.solving;
  }


let add_calls (tbl:call_tbl_t) (dp:t) (n:int) : unit =
  try
    Hashtbl.replace tbl.calls dp ((Hashtbl.find tbl.calls dp) + n)
  with _ -> Hashtbl.add tbl.calls dp n


let add_solving (tbl:call_tbl_t) (vc_id:int) (dp:t) : unit =
  try
    Hashtbl.replace tbl.solving vc_id
      (stronger (Hashtbl.find tbl.solving vc_id) dp)
  with _ -> Hashtbl.add tbl.solving vc_id dp


let add_dp_calls ?(vc_id = -1) (tbl:call_tbl_t) (dp:t) (n:int) : unit =
  add_calls tbl dp n;
  add_solving tbl vc_id dp


let combine_call_table (src_tbl:call_tbl_t) (dst_tbl:call_tbl_t) : unit =
  Hashtbl.iter (add_calls dst_tbl) src_tbl.calls;
  Hashtbl.iter (add_solving dst_tbl) src_tbl.solving


let call_tbl_to_list (tbl:call_tbl_t) : (t * int) list =
  List.sort Pervasives.compare (Hashtbl.fold (fun dp i xs -> (dp,i)::xs) tbl.calls [])


let call_tbl_solving_to_list (tbl:call_tbl_t) : (t * int) list =
  let res = Hashtbl.create 10 in
  (Hashtbl.iter (fun id dp ->
    if id <> -1 then
       try
         Hashtbl.replace res dp ((Hashtbl.find res dp) + 1)
       with _ -> Hashtbl.add res dp 1) tbl.solving);
  Hashtbl.fold (fun dp n xs -> (dp,n)::xs) res []
