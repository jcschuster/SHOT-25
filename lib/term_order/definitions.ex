defmodule THOU.TermOrder.Definitions do
  import HOL.Data
  import THOU.Util
  import THOU.HOL.Definitions

  # Constants are nonversatile
  def nonversatile?(declaration(kind: :co)), do: true
  # Variables are always versatile
  def nonversatile?(declaration(kind: :fv)), do: false
  # Saturated constant symbols are nonversatile
  def nonversatile?(
        hol_term(head: declaration(kind: :co, type: type(goal: t)), type: type(goal: t, args: []))
      ),
      do: true

  # Terms made of single variables are always versatile
  def nonversatile?(hol_term(head: declaration(kind: :fv, type: t), type: t)),
    do: false

  def nonversatile?(hol_term(head: head, args: args) = term) do
    cond do
      is_appl_term?(term) ->
        nonversatile?(head)
        # TODO: handle lambda structures
    end
  end
end
