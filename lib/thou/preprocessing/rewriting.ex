defmodule THOU.Preprocessing.Rewriting do
  @moduledoc """
  Utilizes an e-graph implementation provided by the Rust library egg
  (https://egraphs-good.github.io/) to canonicalize/simplify a given formula.
  This can be used as a preprocessing step. The Rust code is integrated in this
  module using the library Rustler (https://hexdocs.pm/rustler/readme.html).
  """

  use Rustler, otp_app: :thou
  import THOU.Preprocessing.Serialization

  @doc """
  Canonicalizes/simplifies a given term by converting it to an s-expression and
  relying on the Rust library egg to find an optimal representation (and
  orientation for boolean logical connectives).
  """
  @spec canonicalize(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def canonicalize(term) do
    term
    |> to_s_expr()
    |> simplify()
    |> from_s_expr()
  end

  @doc """
  This function gets replaced by the `simplify` function defined in the Rust
  implementation by Rustler. It uses e-graphs to find an optimal representation
  of the given term modulo the defined rewrite rules.
  """
  @spec simplify(String.t()) :: String.t()
  def simplify(_str), do: :erlang.nif_error(:nif_not_loaded)
end
