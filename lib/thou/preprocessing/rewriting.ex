defmodule THOU.Preprocessing.Rewriting do
  @moduledoc """
  Utilizes an e-graph implementation provided by the Rust library egg
  (https://egraphs-good.github.io/) to simplify/orient the conjunctions and
  disjunctions in a given formula. This can be used as a preprocessing step.
  The Rust code is integrated in this module using the library Rustler
  (https://hexdocs.pm/rustler/readme.html). Note that rewriting is only
  implemented on propositional level.
  """

  use Rustler, otp_app: :thou
  import THOU.Preprocessing.Serialization

  @doc """
  Simplifies a given term by converting it to an s-expression and relying on
  the Rust library egg to find an optimal representation (and orientation for
  conjunctions and disjunctions). Does not orient equality and equivalence
  symbols as this leads to problems within the prover.
  """
  @spec simplify(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def simplify(term) do
    term
    |> to_s_expr()
    |> egg_simplify()
    |> from_s_expr()
  end

  @doc """
  Orients the conjunctions and disjunctions in the given term canonically based
  on the optimal e-graph representation found by the Rust library egg.
  """
  @spec orient(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def orient(term) do
    term
    |> to_s_expr()
    |> egg_simplify_ac()
    |> from_s_expr()
  end

  @doc false
  @spec egg_simplify(String.t()) :: String.t()
  def egg_simplify(_str), do: :erlang.nif_error(:nif_not_loaded)

  @doc false
  @spec egg_simplify_ac(String.t()) :: String.t()
  def egg_simplify_ac(_str), do: :erlang.nif_error(:nif_not_loaded)
end
