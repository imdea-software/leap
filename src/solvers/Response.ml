
let sat_to_valid (answer:Sat.t) : Valid.t =
  match answer with
  | Sat.Sat     -> Valid.Invalid
  | Sat.Unsat   -> Valid.Valid
  | Sat.Unknown -> Valid.Unknown


let valid_to_sat (answer:Valid.t) : Sat.t =
  match answer with
  | Valid.Valid   -> Sat.Unsat
  | Valid.Invalid -> Sat.Sat
  | Valid.Unknown -> Sat.Unknown
