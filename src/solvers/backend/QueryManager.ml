
open NumQuery
open TllQuery
open TslkQuery
open YicesNumQuery
open YicesTllQuery
open Z3TllQuery
open SMTTllQuery

let use_smtlib = ref false


let set_smt_usage (b:bool) : unit =
  let _ = print_endline "set_smt_usage function called" in
  use_smtlib := b


let get_num_query (id:string) : (module NUM_QUERY) =
  match (id,!use_smtlib) with
  | ("Yices", _) -> (module YicesNumQuery)
  | _            -> (module YicesNumQuery)


let get_tll_query (id:string) : (module TLL_QUERY) =
  match (id,!use_smtlib) with
  | (_,       true ) -> (module SMTTllQuery)
  | ("Z3",    false) -> (module Z3TllQuery)
  | ("Yices", false) -> (module YicesTllQuery)
  | _                -> (module Z3TllQuery)

(*
let get_tslk_query (id:string) : (functor (K : Level.S) -> (module TSLK_QUERY)) =
  match (id,!use_smtlib) with
  | ("Z3", false) -> (module Z3TslkQuery.Make)
  | _             -> (module Z3TslkQuery.Make)
*)


