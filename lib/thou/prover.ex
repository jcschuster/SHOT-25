defmodule THOU.Prover do
  @moduledoc """
  Main entry point to the prover. Contains a `sat/3` and a `prove/4` function
  to satisfy or prove HOL formulas. The heart of the prover is
  `THOU.Tableaux.tableau/3`, which describes a tableau procedure to satisfy a
  given set of formulas. A formula is proven by negating it and showing that no
  model can be found for this negation.
  """

  import THOU.Tableaux
  import THOU.Util
  alias THOU.Data.{Model, Parameters}
  require Logger
  require Record

  @type definitions() :: %{String.t() => HOL.Data.hol_term()}

  @typedoc """
  Represents the result of the `sat/3` function wich can be one of:

  - `{:sat, model}` means that the formulas are satisfiable with `model` being
    a satisfying assignment with corresponding constraints.

  - `{:unsat, :closed}` means that the formulas are unsatisfiable because every
    branch of the tableau closed.

  - `{:unknown, partial_model, reason}` where reason can be `:incomplete` or
    `:timeout`. In case of `:incomplete`, a partial model is returned, which is
    `:nil` when the reason is `:timeout`
  """
  @type sat_result ::
          {:unknown, Model.t() | nil, :incomplete | :timeout}
          | {:unsat, :closed}
          | {:sat, Model.t()}

  @type proof_result ::
          {:valid, :proven}
          | {:countersat, Model.t()}
          | {:unknown, Model.t() | nil, atom()}

  @doc """
  Tries to satisfy a given formula or list of formulas with respect to the
  given definitions. Returns a `sat_result` describing one of three outcomes.

  Internally relies on the `THOU.Tableaux.tableau/3` function as model finder.

  Parameters that can be given in the `opts` field are a `:timeout` in
  milliseconds, which defaults to 30s and all technical parameters of
  `THOU.Tableaux.tableau/3`.
  """
  @spec sat(HOL.Data.hol_term() | [HOL.Data.hol_term()], definitions(), Keyword.t()) ::
          sat_result()
  def sat(formulas, definitions \\ %{}, opts \\ [])

  def sat(formulas, definitions, opts) when is_list(formulas) do
    {timeout, prover_opts} = Keyword.pop(opts, :timeout, 30_000)
    params = Parameters.new(prover_opts)

    task =
      Task.async(fn ->
        tableau(formulas, definitions, params)
      end)

    case Task.yield(task, timeout) do
      {:ok, res} ->
        res

      nil ->
        Task.shutdown(task, :brutal_kill)
        :timeout
    end
    |> as_assignment()
  end

  def sat(formula, definitions, opts), do: sat([formula], definitions, opts)

  @doc """
  Tries to proof a given term based on the given assumptions and definitions by
  showing that there is no couterexample for its negation, i.e., that
  `THOU.Tableaux.tableau/3` can close all branches. Returns a `proof_result`
  describing the output, which can be pretty-printed with a call to
  `THOU.PrettyPrint.pp_proof_result/1`.

  Parameters that can be given in the `opts` field are a timeout in
  milliseconds (defaults to 30s) and all technical parameters of
  `THOU.Tableaux.tableau/3`.
  """
  @spec prove(HOL.Data.hol_term(), [HOL.Data.hol_term()], definitions(), Keyword.t()) ::
          proof_result()
  def prove(conclusion, assumptions \\ [], definitions \\ %{}, opts \\ []) do
    neg_conclusion = sem_negate(conclusion)

    case sat([neg_conclusion | assumptions], definitions, opts) do
      {:unsat, _} -> {:valid, :proven}
      {:unknown, partial_model, reason} -> {:unknown, partial_model, reason}
      {:sat, counter_model} -> {:countersat, counter_model}
    end
  end

  defp as_assignment({:closed, _}) do
    "All branches closed -> unsatisfiable" |> Logger.notice()
    {:unsat, :closed}
  end

  defp as_assignment({:open, clause, constraints}) do
    "Some branches still open -> countermodel exists" |> Logger.notice()

    {:sat, %Model{assignments: clause, constraints: constraints}}
  end

  defp as_assignment({:incomplete, clause, constraints}) do
    "Result unknown due to prover incompleteness" |> Logger.notice()

    {:unknown, %Model{assignments: clause, constraints: constraints}, :incomplete}
  end

  defp as_assignment(:timeout), do: {:unknown, nil, :timeout}
end
