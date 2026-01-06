defmodule THOU.Heuristics.TypePositions do
  # implements type positions as defined in
  # https://doi.org/10.1016/S0304-3975(97)00143-6
  import HOL.Data

  def occurs_only_positively?(sort, type) do
    pos_a = positions_of_sort(sort, type)
    pos_plus = positive_positions(type)
    MapSet.subset?(pos_a, pos_plus)
  end

  def positions_of_sort(sort, type) do
    pos_rec(type, sort) |> MapSet.new()
  end

  def positive_positions(type) do
    pos_plus_rec(type) |> MapSet.new()
  end

  def negative_positions(type) do
    pos_minus_rec(type) |> MapSet.new()
  end

  defp pos_rec(type(goal: g, args: []), sort) do
    if g == sort, do: [[]], else: []
  end

  defp pos_rec(type(goal: v, args: [u]), sort) when not is_atom(v) do
    p_u = pos_rec(u, sort) |> Enum.map(&[1 | &1])
    p_v = pos_rec(v, sort) |> Enum.map(&[2 | &1])

    p_u ++ p_v
  end

  defp pos_rec(type(args: [u | rest]) = t, sort) do
    v = type(t, args: rest)

    p_u = pos_rec(u, sort) |> Enum.map(&[1 | &1])
    p_v = pos_rec(v, sort) |> Enum.map(&[2 | &1])

    p_u ++ p_v
  end

  defp pos_plus_rec(type(goal: _, args: [])), do: [[]]

  defp pos_plus_rec(type(goal: v, args: [u])) when not is_atom(v) do
    p_u = pos_minus_rec(u) |> Enum.map(&[1 | &1])
    p_v = pos_plus_rec(v) |> Enum.map(&[2 | &1])

    p_u ++ p_v
  end

  defp pos_plus_rec(type(args: [u | rest]) = t) do
    v = type(t, args: rest)

    p_u = pos_minus_rec(u) |> Enum.map(&[1 | &1])
    p_v = pos_plus_rec(v) |> Enum.map(&[2 | &1])

    p_u ++ p_v
  end

  defp pos_minus_rec(type(goal: _, args: [])), do: []

  defp pos_minus_rec(type(goal: v, args: [u])) when not is_atom(v) do
    p_u = pos_plus_rec(u) |> Enum.map(&[1 | &1])
    p_v = pos_minus_rec(v) |> Enum.map(&[2 | &1])

    p_u ++ p_v
  end

  defp pos_minus_rec(type(args: [u | rest]) = t) do
    v = type(t, args: rest)

    p_u = pos_plus_rec(u) |> Enum.map(&[1 | &1])
    p_v = pos_minus_rec(v) |> Enum.map(&[2 | &1])

    p_u ++ p_v
  end
end
