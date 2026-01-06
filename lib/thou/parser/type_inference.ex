defmodule THOU.Parser.TypeInference do
  import HOL.Data
  import THOU.Util, only: [unknown_type?: 1]

  def solve(constraints) do
    Enum.reduce(constraints, %{}, fn {t1, t2}, subst ->
      unify(apply_subst(t1, subst), apply_subst(t2, subst), subst)
    end)
  end

  def apply_subst(type(goal: g, args: args), subst) do
    resolved_base =
      if unknown_type?(g) and Map.has_key?(subst, g) do
        apply_subst(Map.get(subst, g), subst)
      else
        type(goal: g, args: [])
      end

    {base_goal, base_args} =
      if is_atom(resolved_base) do
        {resolved_base, []}
      else
        {get_goal_type(resolved_base), get_arg_types(resolved_base)}
      end

    resolved_args = Enum.map(args, &apply_subst(&1, subst))

    mk_type(base_goal, resolved_args ++ base_args)
  end

  def apply_subst(atom, subst) when is_atom(atom) do
    if Map.has_key?(subst, atom) do
      apply_subst(Map.get(subst, atom), subst)
    else
      atom
    end
  end

  def apply_subst(other, _), do: other

  defp unify(t, t, subst), do: subst
  defp unify(g, type(goal: g, args: []), subst), do: subst
  defp unify(type(goal: g, args: []), g, subst), do: subst

  defp unify(g1, g2, subst) when is_atom(g1) and is_atom(g2) do
    cond do
      unknown_type?(g1) ->
        Map.put(subst, g1, g2) |> map_substitutions(g1, g2)

      unknown_type?(g2) ->
        Map.put(subst, g2, g1) |> map_substitutions(g2, g1)

      true ->
        raise(
          "Type Error: Cannot unify #{inspect(g1)} with #{inspect(g2)} under substitutions #{inspect(subst)}."
        )
    end
  end

  defp unify(g1, type(goal: g2, args: args2) = t2, subst) when is_atom(g1) do
    cond do
      unknown_type?(g1) ->
        if occurs?(g1, t2), do: raise("Type Error: Recursive type check failed (Occurs check)")
        Map.put(subst, g1, t2) |> map_substitutions(g1, t2)

      args2 == [] and unknown_type?(g2) ->
        Map.put(subst, g2, g1) |> map_substitutions(g2, g1)

      true ->
        raise(
          "Type Error: Cannot unify #{inspect(g1)} with #{inspect(t2)} under substitutions #{inspect(subst)}."
        )
    end
  end

  defp unify(t1, g2, subst) when is_atom(g2), do: unify(g2, t1, subst)

  defp unify(type(goal: g1, args: []), type(goal: g2, args: []), subst) do
    unify(g1, g2, subst)
  end

  defp unify(type(goal: g1, args: []), t2, subst) do
    unify(g1, t2, subst)
  end

  defp unify(t1, type(goal: g2, args: []), subst) do
    unify(t1, g2, subst)
  end

  defp unify(type(goal: g1, args: args1) = t1, type(goal: g2, args: args2) = t2, subst) do
    cond do
      length(args1) == length(args2) ->
        unify_concrete(t1, t2, subst)

      length(args1) < length(args2) ->
        if not unknown_type?(g1) do
          raise(
            "Type Error: Cannot unify #{inspect(t1)} with #{inspect(t2)} under substitutions #{inspect(subst)}."
          )
        else
          {shared_args2, extra_args2} = Enum.split(args2, length(args1))

          subst_after_args =
            Enum.zip(args1, shared_args2)
            |> Enum.reduce(subst, fn {a1, a2}, acc ->
              unify(apply_subst(a1, acc), apply_subst(a2, acc), acc)
            end)

          tail_type = mk_type(g2, extra_args2)

          unify(
            apply_subst(g1, subst_after_args),
            apply_subst(tail_type, subst_after_args),
            subst_after_args
          )
        end

      length(args1) > length(args2) ->
        unify(t2, t1, subst)
    end
  end

  defp unify_concrete(type(goal: g1, args: args1), type(goal: g2, args: args2), subst) do
    if (not unknown_type?(g1) and not unknown_type?(g2) and g1 != g2) or
         length(args1) != length(args2) do
      raise "Type Error: Cannot unify #{inspect(g1)} with #{inspect(g2)} or argument count mismatch. (Unifying types #{inspect(type(goal: g1, args: args1))} and #{inspect(type(goal: g2, args: args2))})"
    end

    Enum.zip([g1 | args1], [g2 | args2])
    |> Enum.reduce(subst, fn {a1, a2}, current_subst ->
      unify(apply_subst(a1, current_subst), apply_subst(a2, current_subst), current_subst)
    end)
  end

  defp map_substitutions(subst, var_key, type_val) do
    Map.new(subst, fn
      {^var_key, _} -> {var_key, type_val}
      {k, v} -> {k, apply_subst(v, Map.put(subst, var_key, type_val))}
    end)
    |> Map.put(var_key, type_val)
  end

  defp occurs?(var_atom, type(goal: g, args: args)) do
    g == var_atom or Enum.any?(args, &occurs?(var_atom, &1))
  end

  defp occurs?(var_atom, atom) when is_atom(atom) do
    var_atom == atom
  end
end
