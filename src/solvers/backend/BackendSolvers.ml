open BackendSolverIntf

(** Yices implementation *)
include Yices

(** Z3 Implementation *)
include Z3

(** Minisat Implementation *)
include Minisat


(* Backends that support Position reasoning *)
let posTbl : (string, (module BACKEND_POS)) Hashtbl.t = Hashtbl.create 3
let _ = Hashtbl.add posTbl Yices.identifier   (module Yices   : BACKEND_POS)
let _ = Hashtbl.add posTbl Z3.identifier      (module Z3      : BACKEND_POS)
let _ = Hashtbl.add posTbl Minisat.identifier (module Minisat : BACKEND_POS)
let defaultPos () = (module Yices : BACKEND_POS)


(* Backends that support TLL reasoning *)
let tllTbl : (string, (module BACKEND_TLL)) Hashtbl.t = Hashtbl.create 2
let _ = Hashtbl.add tllTbl Yices.identifier (module Yices : BACKEND_TLL)
let _ = Hashtbl.add tllTbl Z3.identifier    (module Z3    : BACKEND_TLL)
let defaultTll () = (module Z3 : BACKEND_TLL)


(* Backends that support TSLK reasoning *)
let tslkTbl : (string, (module BACKEND_TSLK)) Hashtbl.t = Hashtbl.create 2
let _ = Hashtbl.add tslkTbl Yices.identifier (module Yices : BACKEND_TSLK)
let _ = Hashtbl.add tslkTbl Z3.identifier    (module Z3    : BACKEND_TSLK)
let defaultTslk () = (module Z3 : BACKEND_TSLK)
(* TUKA: Put Yices as default once generic Backend is modified *)


(* Backends that support Numeric reasoning *)
let numTbl : (string, (module BACKEND_NUM)) Hashtbl.t = Hashtbl.create 1
let _ = Hashtbl.add numTbl Yices.identifier (module Yices : BACKEND_NUM)
let _ = Hashtbl.add numTbl Z3.identifier    (module Z3    : BACKEND_NUM)
let defaultNum () = (module Yices : BACKEND_NUM)


(* Backends that support Pairs reasoning *)
let pairsTbl : (string, (module BACKEND_PAIRS)) Hashtbl.t = Hashtbl.create 1
let _ = Hashtbl.add pairsTbl Yices.identifier (module Yices : BACKEND_PAIRS)
let _ = Hashtbl.add pairsTbl Z3.identifier    (module Z3    : BACKEND_PAIRS)
let defaultPairs () = (module Yices : BACKEND_PAIRS)
