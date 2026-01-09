defmodule THOU.Data.Model do
  @moduledoc """
  A data structure representing a model consisting of assignments to literals
  and constraints under which the model holds.

  A string representation of the model is also implemented, which allows the
  model to be printed like:

      iex>IO.puts(model)
  """

  defstruct assignments: MapSet.new(), constraints: []

  @typedoc """
  The type of a model.

  A model consists of assignments and constraints, where the assignments are a
  `MapSet` of terms, which can be negated or not. The constraints are given as
  list of `HOL.Data.hol_term()` pairs.
  """
  @type t() :: %__MODULE__{
          assignments: MapSet.t(HOL.Data.hol_term()),
          constraints: [{HOL.Data.hol_term(), HOL.Data.hol_term()}]
        }
end

defimpl String.Chars, for: THOU.Data.Model do
  import THOU.PrettyPrint

  def to_string(model) do
    assignments_str = pp_assignment(model.assignments)
    constraints_str = pp_constraints(model.constraints)
    "#{assignments_str} || #{constraints_str}"
  end
end

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
