defmodule THOU.TermOrder.Signature do
  import HOL.Data
  import THOU.HOL.Definitions

  def accessible_arguments(declaration(name: name) = head) when name in signature_symbols() do
    case head do
      # Type perservation is ensured
      neg_const() -> [0]
      or_const() -> [0, 1]
      and_const() -> [0, 1]
      implies_const() -> [0, 1]
      equivalent_const() -> [0, 1]
      equals_const(type_o()) -> [0, 1]
      # No type perservation
      equals_const(_) -> []
      pi_const(_) -> []
      sigma_const(_) -> []
    end
  end
end
