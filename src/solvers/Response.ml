

exception Unknown_answer_str of string

(** Declares all possibilities answers from the SMT solver *)
type t =
  | Sat
  | Unsat
  | Unknown


let to_str (answer:t) : string =
  match answer with
  | Sat     -> "SAT"
  | Unsat   -> "UNSAT"
  | Unknown -> "UNKNOWN"


let from_str (str:string) : t =
  match (String.uppercase str) with
  | "SAT"     -> Sat
  | "UNSAT"   -> Unsat
  | "UNKNOWN" -> Unknown
  | _         -> raise(Unknown_answer_str str)


let is_sat (answer:t) : bool =
  t == Sat


let is_unsat (answer:t) : bool =
  t == Unsat


let is_unknown (answer:t) : bool =
  t == Unknown
