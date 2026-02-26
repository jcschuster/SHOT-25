defmodule SHOT25.Tableaux.Branching do
  @moduledoc """
  Contains functionality for or-branching in the tableaux. This includes a
  function to order branches given a heuristic and the actual or-branching
  logic.
  """

  import SHOT25.Util, only: [apply_subst: 2]
  alias SHOT25.Heuristics.NCPO
  require Logger

  @doc """
  Orders the given terms or list of terms according to the given heuristic. If
  no heuristic is given, the terms are returned as lists in their given order.
  Currently, only NCPO is implemented as order.
  """
  @spec order(
          HOL.Data.hol_term() | [HOL.Data.hol_term()],
          HOL.Data.hol_term() | [HOL.Data.hol_term()],
          nil | :ncpo
        ) :: {[HOL.Data.hol_term()], [HOL.Data.hol_term()]}

  def order(a, b, nil), do: {List.flatten([a]), List.flatten([b])}

  def order(a, b, :ncpo) do
    a_terms = List.flatten([a])
    b_terms = List.flatten([b])

    if NCPO.smaller_multiset?(b_terms, a_terms) do
      {b_terms, a_terms}
    else
      {a_terms, b_terms}
    end
  end

  @doc """
  Solves the second branch of the tableau which consists of or-branches with
  the solutions found for the first branch. Accepts a function which attempts
  to solve a given or-branch and returns the original checkpoint as well as the
  corresponding solution.
  """
  @spec or_branch(
          [SHOT25.Tableaux.unif_checkpoint()],
          SHOT25.Data.Parameters.t(),
          (SHOT25.Tableaux.unif_checkpoint() ->
             {SHOT25.Tableaux.unif_checkpoint(), SHOT25.Tableaux.tableau_res()})
        ) :: SHOT25.Tableaux.tableau_res()
  def or_branch(solutions, params, solve_fn) do
    Logger.info(
      "First branch closed with #{length(solutions)} solutions. Solving second branch..."
    )

    case params.max_concurrency do
      1 ->
        Enum.map(solutions, solve_fn)

      num ->
        Task.async_stream(solutions, solve_fn,
          max_concurrency: num,
          ordered: false,
          timeout: :infinity
        )
        |> Enum.map(fn {:ok, res} -> res end)
    end
    |> Enum.reduce_while({:open, MapSet.new(), []}, fn {original_cp, res}, acc ->
      process_result(res, original_cp, acc)
    end)
  end

  #############################################################################
  # HELPER FUNCTIONS
  #############################################################################

  @spec process_result(
          SHOT25.Tableaux.tableau_res(),
          SHOT25.Tableaux.unif_checkpoint(),
          SHOT25.Tableaux.unif_checkpoint()
        ) ::
          {:halt, SHOT25.Tableaux.unif_checkpoint()} | {:cont, SHOT25.Tableaux.unif_checkpoint()}
  defp process_result(res, original_cp, acc)

  defp process_result({:closed, new_checkpoints}, original_cp, _acc) do
    combined = merge_checkpoints(original_cp, new_checkpoints)
    {:halt, {:closed, combined}}
  end

  # Don't overwrite open branches with incomplete ones
  defp process_result({:incomplete, clause, constrs}, _original_cp, acc) do
    case acc do
      {:open, _, _} -> {:cont, acc}
      _ -> {:cont, {:incomplete, clause, constrs}}
    end
  end

  defp process_result(open, _original_cp, _acc) do
    {:cont, open}
  end

  @spec merge_checkpoints(SHOT25.Tableaux.unif_checkpoint(), [SHOT25.Tableaux.unif_checkpoint()]) ::
          [
            SHOT25.Tableaux.unif_checkpoint()
          ]
  defp merge_checkpoints(original_cp, new_checkpoints) do
    require SHOT25.Tableaux, as: T
    T.unif_checkpoint(substs: old_substs) = original_cp

    if Enum.empty?(new_checkpoints) do
      [original_cp]
    else
      Enum.map(new_checkpoints, fn T.unif_checkpoint(substs: new_substs) = c ->
        T.unif_checkpoint(c,
          substs: apply_subst(new_substs, old_substs) ++ new_substs
        )
      end)
    end
  end
end
