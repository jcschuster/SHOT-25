defmodule THOU.TermOrder.TypeOrder do
  import HOL.Data

  def base_rank(:o), do: 1
  def base_rank(t) when is_atom(t), do: 2
  def base_rank(_), do: 3

  def compare_types(type(goal: ret1, args: args1), type(goal: ret2, args: args2)) do
    cond do
      base_rank(ret1) > base_rank(ret2) -> :gt
      base_rank(ret1) < base_rank(ret2) -> :lt
      length(args1) > length(args2) -> :gt
      length(args1) < length(args2) -> :lt
      true -> compare_args_lex(args1, args2)
    end
  end

  defp compare_args_lex([], []), do: :eq

  defp compare_args_lex([type() = h1 | t1], [type() = h2 | t2]) do
    case compare_types(h1, h2) do
      :eq -> compare_args_lex(t1, t2)
      res -> res
    end
  end
end
