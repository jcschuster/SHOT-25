defmodule THOU.Runner do
  alias THOU.Parser.TPTP
  alias THOU.Prover

  @doc """
  Parses a THF file and attempts to prove the conjecture found within it.
  """
  def prove_file(path, is_tptp \\ true) do
    # 1. Parse the file into a Problem struct
    case TPTP.parse_file(path, is_tptp) do
      {:ok, problem} ->
        run_prover(problem)

      {:error, reason} ->
        IO.puts(:stderr, "Error parsing file: #{reason}")
    end
  end

  defp run_prover(problem) do
    axiom_terms = Enum.map(problem.axioms, fn {_name, term} -> term end)
    definition_terms = Enum.map(problem.definitions, fn {_name, term} -> term end)

    assumptions = axiom_terms ++ definition_terms

    case problem.conjecture do
      {name, conjecture_term} ->
        IO.puts("--------------------------------------------------")
        IO.puts("Proving Conjecture: #{name}")
        IO.puts("Loaded #{length(assumptions)} axioms/definitions.")
        IO.puts("--------------------------------------------------")

        result = Prover.prove(conjecture_term, assumptions)
        print_result(result)

      nil ->
        # Fallback: If there is no conjecture, check if the axioms are satisfiable
        IO.puts("No conjecture found. Checking consistency (SAT) of axioms...")
        result = Prover.sat(assumptions)

        case result do
          :unsat -> IO.puts("Result: Unsatisfiable (Axioms contain a contradiction)")
          _ -> IO.puts("Result: Satisfiable (Axioms are consistent)")
        end
    end
  end

  defp print_result(:valid), do: IO.puts("STATUS: Theorem (Proof Found)")

  defp print_result({:countersat, _}),
    do: IO.puts("STATUS: CounterSatisfiable (Counter-model found)")

  defp print_result({:unknown, _}), do: IO.puts("STATUS: Unknown (Timeout or incomplete)")
end
