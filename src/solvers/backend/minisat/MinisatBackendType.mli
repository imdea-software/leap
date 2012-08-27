open BackendSolverIntf

module type CUSTOM_BACKEND_POS =
sig
  include BackendCommon
  module Translate : sig
    include PosBackend with type t := t
  end
end

module type BACKEND_POS = CUSTOM_BACKEND_POS
  with module Translate.Pos.Exp = PosExpression
