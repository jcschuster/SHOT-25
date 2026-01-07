defmodule THOU.PrettyPrint do
  import THOU.HOL.Patterns, only: [negated: 1]

  def pp_assignment(clause) when is_struct(clause, MapSet) do
    pretty_assignments =
      Enum.map(clause, fn t ->
        case t do
          negated(inner) -> "#{PrettyPrint.pp_term(inner)} ← false"
          _ -> "#{PrettyPrint.pp_term(t)} ← true"
        end
      end)

    "[" <> Enum.join(pretty_assignments, ", ") <> "]"
  end

  def pp_constraints(constraints) when is_list(constraints) do
    pretty_constraints =
      Enum.map(constraints, fn {t1, t2} ->
        "#{PrettyPrint.pp_term(t1)} = #{PrettyPrint.pp_term(t2)}"
      end)

    "[" <> Enum.join(pretty_constraints, ", ") <> "]"
  end

  @spec pp_proof_result(THOU.Prover.proof_result()) :: String.t()
  def pp_proof_result(res) do
    case res do
      {:valid, :proven} ->
        "STATUS: Theorem (Proof Found)"

      {:countersat, countermodel} ->
        "STATUS: CounterSatisfiable (Counter-model found)\n#{countermodel}"

      {:unknown, nil, reason} ->
        "STATUS: Unknown (#{reason})"

      {:unknown, partial_model, reason} ->
        "STATUS: Unknown (#{reason})\nPartial Model: #{partial_model}"
    end
  end
end
