let sys : System.system_t ref = ref System.empty_system

let load_system (s:System.system_t) : unit =
  sys := s

let sys : System.system_t ref =
  sys
