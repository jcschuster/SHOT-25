defmodule THOU.Runner do
  @moduledoc """
  Extends the functionality of `THOU.Prover` for more general proving of TPTP
  files and `BeHOLd.TPTP.Problem` structures. Main entry point for running the
  prover on files.
  """

  alias BeHOLd.TPTP
  import THOU.PrettyPrint, only: [pp_proof_result: 1]
  alias THOU.Prover

  @doc """
  Parses a TPTP problem file in TH0 syntax, attempts to prove the conjecture
  found within it and prints the result to stdout. If no conjecture could be
  found in the given file, tries to satisfy the axioms.

  If a custom file is given, the flag `is_tptp` should be set to `false`. Note
  that only imports from the TPTP library are supported. In that case, an
  environment variable `TPTP_ROOT` must be specified which points to the root
  folder of the TPTP problem library. Note that this may require a system
  restart for Elixir to register the variable.

  When proving a file from the TPTP problem library, the same environment
  variable `TPTP_ROOT` needs to be registered. After the variable has been
  registered, a TPTP problem file can be parsed by specifying the path from the
  root folder to that problem in `path`.

  If no conjecture could be found within the given problem, tries to satisfy
  the axioms.

  Options for `THOU.Prover.prove/4` can be specified.
  """
  @spec prove_file(String.t(), boolean(), Keyword.t()) :: no_return()
  def prove_file(path, is_tptp \\ true, opts \\ []) do
    case TPTP.parse_file(path, is_tptp) do
      {:ok, problem} ->
        run_prover(problem, opts)

      {:error, reason} ->
        IO.puts(:stderr, "Error parsing file: #{reason}")
    end
  end

  @doc """
  Runs the prover on a given `BeHOLd.Data.Problem` struct from parsing a TPTP
  Problem file specified as string and prints the result to stdout. If no
  conjecture could be found within the given problem, tries to satisfy the
  axioms.

  Options for `THOU.Prover.prove/4` can be specified.
  """
  @spec run_prover(BeHOLd.Data.Problem.t(), Keyword.t()) :: no_return()
  def run_prover(problem, opts \\ []) do
    assumptions = Enum.map(problem.axioms, fn {_name, term} -> term end)

    case problem.conjecture do
      {name, conjecture_term} ->
        IO.puts("--------------------------------------------------")
        IO.puts("Proving Conjecture: #{name}")

        num_assms = length(assumptions)
        num_defs = length(Map.keys(problem.definitions))

        IO.puts(
          "Loaded #{num_assms} assumption#{if num_assms != 1, do: "s", else: ""}" <>
            " and #{num_defs} definition#{if num_defs != 1, do: "s", else: ""}."
        )

        IO.puts("--------------------------------------------------")

        result = Prover.prove(conjecture_term, assumptions, problem.definitions, opts)
        pp_proof_result(result) |> IO.puts()

      nil ->
        # Fallback: If there is no conjecture, check if the axioms are satisfiable
        IO.puts("No conjecture found. Checking consistency (SAT) of axioms...")
        result = Prover.sat(assumptions, problem.definitions, opts)

        case result do
          {:unsat, :closed} -> IO.puts("Result: Unsatisfiable (Axioms contain a contradiction)")
          _ -> IO.puts("Result: Satisfiable (Axioms are consistent)")
        end
    end
  end
end
