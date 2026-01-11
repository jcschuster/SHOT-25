defmodule THOU.Data.Parameters do
  @moduledoc """
  The (default) parameters of the prover.

  The parameters are:

  - `:canonicalize`: Whether or not to preprocess/canonicalize a formula.
  Defaults to `true`.

  - `:branch_heuristic`: Which branch heuristic to use (default: `:ncpo`)

  - `:max_instantiations`: The maximum instantiations of a quantor. Note that
  the prover will be incomplete if finite. Defaults to 4.

  - `:unification_depth`: Depth limit for the unification algorithm. Defaults
  to 8.

  - `:max_concurrency`: The maximum number of threads to use for parallel
  checking of unification checkpoints. Defaults to the
  number of available threads.
  """

  defstruct canonicalize: true,
            branch_heuristic: :ncpo,
            max_instantiations: 4,
            unification_depth: 8,
            max_concurrency: System.schedulers_online()

  @typedoc """
  Whether or not to canonicalize a formula can be `true` or `false`. The branch
  heuristic can be an atom or `nil` if no heuristic should be used. The maximum
  instantiations of a quantifier, the unification depth and the maximum number
  of threads to use for parallelization is a positive integer.
  """
  @type t() :: %__MODULE__{
          canonicalize: boolean(),
          branch_heuristic: atom() | nil,
          max_instantiations: pos_integer(),
          unification_depth: pos_integer(),
          max_concurrency: pos_integer()
        }

  @doc """
  Constructor for a set of parameters. Uses default parameters if not specified
  otherwise. Arguments can be given as keywords.
  """
  @spec new(Keyword.t()) :: t()
  def new(opts \\ []) do
    default_params = %__MODULE__{}

    canonicalize = Keyword.get(opts, :canonicalize, default_params.canonicalize)
    branch_heuristic = Keyword.get(opts, :branch_heuristic, default_params.branch_heuristic)

    max_instantiations =
      Keyword.get(opts, :max_instantiations, default_params.max_instantiations)

    unification_depth = Keyword.get(opts, :unification_depth, default_params.unification_depth)

    max_concurrency = Keyword.get(opts, :max_concurrency, default_params.max_concurrency)

    %__MODULE__{
      canonicalize: canonicalize,
      branch_heuristic: branch_heuristic,
      max_instantiations: max_instantiations,
      unification_depth: unification_depth,
      max_concurrency: max_concurrency
    }
  end
end
