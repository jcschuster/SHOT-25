defmodule THOU.Runner do
  alias THOU.Parser.TPTP
  alias THOU.Prover

  @doc """
  Parses a THF file and attempts to prove the conjecture found within it.
  """
  def prove_file(path) do
    # 1. Parse the file into a Problem struct
    case TPTP.parse_file(path) do
      {:ok, problem} ->
        run_prover(problem)

      {:error, reason} ->
        IO.puts(:stderr, "Error parsing file: #{reason}")
    end
  end

  defp run_prover(problem) do
    # 2. Extract Axioms
    # Axioms are stored as {name, term} tuples. We only need the terms.
    axiom_terms = Enum.map(problem.axioms, fn {_name, term} -> term end)

    # 3. Extract Definitions
    # In THF, definitions (like `name = expression`) are just formulas.
    # We treat them exactly like axioms for the prover.
    definition_terms = Enum.map(problem.definitions, fn {_name, term} -> term end)

    # Combine all assumptions
    assumptions = axiom_terms ++ definition_terms

    # 4. Handle the Conjecture
    case problem.conjecture do
      {name, conjecture_term} ->
        IO.puts("--------------------------------------------------")
        IO.puts("Proving Conjecture: #{name}")
        IO.puts("Loaded #{length(assumptions)} axioms/definitions.")
        IO.puts("--------------------------------------------------")

        # Call the Prover
        # The prover will negate the conjecture and search for a contradiction (unsat).
        result = Prover.prove(conjecture_term, assumptions)

        print_result(result)

      nil ->
        # Fallback: If there is no conjecture, check if the axioms are consistent (satisfiable)
        IO.puts("No conjecture found. Checking consistency (SAT) of axioms...")
        result = Prover.sat(assumptions)

        case result do
          :unsat -> IO.puts("Result: Unsatisfiable (Axioms contain a contradiction)")
          _ -> IO.puts("Result: Satisfiable (Axioms are consistent)")
        end
    end
  end

  defp print_result(:valid), do: IO.puts("STATUS: Theorem (Proof Found)")
  # Should not happen for a conjecture check usually
  defp print_result(:unsat), do: IO.puts("STATUS: Unsatisfiable")

  defp print_result({:countersat, _}),
    do: IO.puts("STATUS: CounterSatisfiable (Counter-model found)")

  defp print_result({:unknown, _}), do: IO.puts("STATUS: Unknown (Timeout or incomplete)")
end
