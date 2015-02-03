

exception Unknown_answer_str of string

(** Declares all possibilities answers from the SMT solver *)
type t =
  | Valid
  | Invalid
  | Unknown


let to_str (answer:t) : string =
  match answer with
  | Valid   -> "VALID"
  | Invalid -> "INVALID"
  | Unknown -> "UNKNOWN"


let from_str (str:string) : t =
  match (String.uppercase str) with
  | "VALID"   -> Valid
  | "INVALID" -> Invalid
  | "UNKNOWN" -> Unknown
  | _         -> raise(Unknown_answer_str str)


let is_valid (answer:t) : bool =
  answer == Valid


let is_invalid (answer:t) : bool =
  answer == Invalid


let is_unknown (answer:t) : bool =
  answer == Unknown

