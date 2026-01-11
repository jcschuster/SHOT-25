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
