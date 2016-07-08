
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


open BackendSolverIntf
open NumQuery
open PairsQuery
open TllQuery

module Z3 : BACKEND_SOLVER =
struct
  type t = string
  
  (** Unique identifier *)
  let identifier = "Z3"
  
  (** the configuration register *)
  let config = SMTExecute.new_configuration SMTExecute.Z3
  
  
  (** [reset_calls ()] resets the calls counter to [0]. *)
  let reset_calls () : unit =
    SMTExecute.reset_calls config

  
  (** [calls_count ()] returns the number of calls performed to the SMT. *)
  let calls_count () : int =
    SMTExecute.calls_count config


  (** [calls_force_incr ()] forces to increment by one the number of calls
      performed by the SMT. *)
  let calls_force_incr () : unit =
    SMTExecute.calls_force_incr config

 
  (** [compute_model b] sets whether a counter model for non valid
      VCs should be computed *)
  let compute_model (b:bool) : unit =
    SMTExecute.compute_model config b

  
  (** [get_model ()] returns a generic model in case the last call to
      [sat] has been satisfiable. Otherwise returns an empty model *)
  let get_model () : GenericModel.t =
    SMTExecute.get_model ()
  
    
  (* RUNING Z3 *)
  

  (** [sat formula] returns [true] whenever the [formula] is satisfiable, [false] otherwise. *)
  let check_sat (query:t) : Sat.t =
    SMTExecute.run config query

(*
  (** [unsat formula] returns [not(sat formula)]. *)
  let unsat (query:string) : Sat.t =
    Sat.alternate (sat query)
*)
  
  module Translate = 
  struct
    module Pos = 
    struct
      module Exp = PosExpression

      let set_prog_lines = Z3PosQuery.set_prog_lines
      let expression = Z3PosQuery.pos_expression_to_str
    end
    
    module Tll =
    struct
      module Exp = TllExpression
      module Smp = SmpTll
      module Query = functor (Q : TLL_QUERY) ->
      struct
        let set_prog_lines = Q.set_prog_lines
        let literal_list   = Q.literal_list_to_str
        let formula        = Q.formula_to_str
        let conjformula    = Q.conjformula_to_str
        let sort_map       = Q.get_sort_map
      end
    end

    module Tslk (K : Level.S) =
    struct
      module Smp     = SmpTslk
      module Z3Query = Z3TslkQuery.Make(K)
      module Exp     = Z3Query.Expr

      let set_prog_lines = Z3Query.set_prog_lines
      let literal_list   = Z3Query.literal_list_to_str
      let formula        = Z3Query.formula_to_str
      let conjformula    = Z3Query.conjformula_to_str
      let sort_map       = Z3Query.get_sort_map
    end

    module Num =
    struct
      module Exp = NumExpression
      module Query = functor (Q : NUM_QUERY) ->
      struct
        let set_prog_lines         = Q.set_prog_lines
        let int_varlist            = Q.int_varlist_to_str
        let formula                = Q.string_of_formula
        let literal                = Q.string_of_literal
        let int_formula            = Q.int_formula_to_str
        let int_formula_with_lines = Q.int_formula_with_lines_to_str
        let std_widening           = Q.standard_widening
        let sort_map               = Q.get_sort_map
      end
    end

    module Pairs =
    struct
      module Exp = PairsExpression
      module Query = functor (Q : PAIRS_QUERY) ->
      struct
        let set_prog_lines           = Q.set_prog_lines
        let pairs_formula            = Q.pairs_formula_to_str
        let pairs_formula_with_lines = Q.pairs_formula_with_lines_to_str
        let sort_map                 = Q.get_sort_map
      end
    end

  end
end
