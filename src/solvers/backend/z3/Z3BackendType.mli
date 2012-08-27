open BackendSolverIntf

module type CUSTOM_BACKEND_POS_TLL = 
  sig
  include BackendCommon
  module Translate : sig
    include PosBackend with type t := t
    include TllBackend with type t := t
  end
end

module type BACKEND_POS_TLL = CUSTOM_BACKEND_POS_TLL
  with module Translate.Pos.Exp = PosExpression
  and  module Translate.Tll.Exp = TllExpression
  and  module Translate.Tll.Smp = SmpTll
