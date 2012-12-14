
exception Unknown_dp_str of string


type t =
  | NoDP
  | Num
  | Tll
  | Tsl
  | Tslk of int


let def_dp_list : t list = [ Num; Tll; Tsl; Tslk 0 ]


let to_str (dp:t) : string =
  match dp with
  | NoDP   -> ""
  | Num    -> "num"
  | Tll    -> "tll"
  | Tsl    -> "tsl"
  | Tslk k -> let arg = if k > 0 then string_of_int k else "_" in
                "tslk[" ^ arg ^ "]"


let from_str (str:string) : t =
  match str with
  | ""    -> NoDP
  | "num" -> Num
  | "tll" -> Tll
  | "tsl" -> Tsl
  | s     -> let regexp = Str.regexp "tslk\\[[0-9]+\\]" in
             if Str.string_match regexp s 0 then
               let k = String.sub s 5 (String.length s - 6) in
               Tslk (int_of_string k)
             else
               raise (Unknown_dp_str s)


let get_tslk_param (dp:t) : int =
  match dp with
  | Tslk k -> k
  | _      -> 1
