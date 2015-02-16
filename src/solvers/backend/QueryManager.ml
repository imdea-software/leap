
open NumQuery
open PairsQuery
open TllQuery
open TslkQuery
open YicesNumQuery
open Z3NumQuery
open YicesPairsQuery
open Z3PairsQuery
open YicesTllQuery
open Z3TllQuery
open SMTTllQuery

let use_smtlib = ref false


let set_smt_usage (b:bool) : unit =
  use_smtlib := b


let get_num_query (id:string) : (module NUM_QUERY) =
  match (id,!use_smtlib) with
  | ("Yices", _) -> (module YicesNumQuery)
  | ("Z3",    _) -> (module Z3NumQuery)
  | _            -> (module YicesNumQuery)


let get_pairs_query (id:string) : (module PAIRS_QUERY) =
  match (id,!use_smtlib) with
  | ("Yices", _) -> (module YicesPairsQuery)
  | ("Z3",    _) -> (module Z3PairsQuery)
  | _            -> (module YicesPairsQuery)


let get_tll_query (id:string) : (module TLL_QUERY) =
  match (id,!use_smtlib) with
  | (_,       true ) -> (module SMTTllQuery)
  | ("Z3",    false) -> (module Z3TllQuery)
  | ("Yices", false) -> (module YicesTllQuery)
  | _                -> (module Z3TllQuery)

(*
(*let get_tslk_query (id:string) : (functor (K : Level.S) -> (module TSLK_QUERY)) = *)
let get_tslk_query (id:string) =
  match (id,!use_smtlib) with
(*  | (_,    true ) -> (module SMTTslkQuery.Make) *)
  | ("Z3", false) -> (module Z3TslkQuery.Make)
  | _             -> (module Z3TslkQuery.Make)
*)

