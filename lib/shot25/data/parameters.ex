defmodule SHOT25.Data.Parameters do
  @moduledoc """
  The (default) parameters of the prover.

  The parameters are:

  - `:rewrite`: What method to use for preprocessing a formula. Can be
  `:orient` (default), `:simplify` or `nil` if no preprocessing should happen.

  - `:branch_heuristic`: Which branch heuristic to use (default: `:ncpo`)

  - `:max_instantiations`: The maximum instantiations of a quantor. Note that
  the prover will be incomplete if finite. Defaults to 4.

  - `:unification_depth`: Depth limit for the unification algorithm. Defaults
  to 8.

  - `:max_concurrency`: The maximum number of threads to use for parallel
  checking of unification checkpoints. Defaults to the
  number of available threads (at runtime).
  """

  defstruct rewrite: :orient,
            branch_heuristic: :ncpo,
            max_instantiations: 4,
            unification_depth: 8,
            max_concurrency: nil

  @typedoc """
  The field `rewrite` specifies whether to just orient disjunction and
  conjunction symbols, use additional simplification rules or do nothing. The
  branch heuristic can be an atom or `nil` if no heuristic should be used. The
  maximum instantiations of a quantifier, the unification depth and the maximum
  number of threads to use for parallelization is a positive integer. `nil`
  corresponds to all available schedulers.
  """
  @type t() :: %__MODULE__{
          rewrite: :simplify | :orient | nil,
          branch_heuristic: atom() | nil,
          max_instantiations: pos_integer(),
          unification_depth: pos_integer(),
          max_concurrency: pos_integer() | nil
        }

  @doc """
  Constructor for a set of parameters. Uses default parameters if not specified
  otherwise. Arguments can be given as keywords.
  """
  @spec new(Keyword.t()) :: t()
  def new(opts \\ []) do
    params = struct!(%__MODULE__{}, opts)
    %{params | max_concurrency: params.max_concurrency || System.schedulers_online()}
  end
end
