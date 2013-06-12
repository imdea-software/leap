let sys : System.t ref = ref System.empty_system

let load_system (s:System.t) : unit =
  sys := s

let sys : System.t ref =
  sys
