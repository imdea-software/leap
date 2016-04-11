type dom_t =
  | Int
  | Level
  | Elem
  | Addr
  | Tid


type t = (dom_t, int) Hashtbl.t


let create () : t =
  Hashtbl.create 5

let get (ms:t) (d:dom_t) : int =
  try
    Hashtbl.find ms d
  with
    Not_found -> 0


let set (ms:t) (d:dom_t) (i:int) : unit =
  Hashtbl.replace ms d i


let add (ms:t) (d:dom_t) (i:int) : unit =
  try
    Hashtbl.replace ms d ((Hashtbl.find ms d) + i)
  with
    Not_found -> Hashtbl.add ms d i


let incr (ms:t) (d:dom_t) : unit =
  add ms d 1


let max (ms:t) (d:dom_t) (i:int) : unit =
  let curr = get ms d in
  if i > curr then
    Hashtbl.replace ms d i


let max_of (ms1:t) (ms2:t) : unit =
  Hashtbl.iter (max ms1) ms2


let create_with (xs:(dom_t * int) list) : t =
  let ms = create () in
  List.iter (fun (d,i) -> add ms d i) xs;
  ms


let dom_to_str (d:dom_t) : string =
  match d with
  | Int -> "integers"
  | Level -> "levels"
  | Elem -> "elements"
  | Addr -> "addresses"
  | Tid -> "thread ids"


let to_str (ms:t) : string =
  "========  Model size ========\n" ^
  (String.concat "\n" (Hashtbl.fold (fun d i xs ->
                        ((dom_to_str d) ^ ": " ^ (string_of_int i)) :: xs
                      ) ms [])) ^
  "\n=============================\n"
