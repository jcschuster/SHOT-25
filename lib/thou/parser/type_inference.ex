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

    mk_type(base_goal, base_args ++ resolved_args)
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

  defp unify(type(goal: u, args: []) = t1, t2, subst) do
    if unknown_type?(t1) do
      if occurs?(u, t2), do: raise("Type Error: Recursive type check failed (Occurs check)")
      Map.put(subst, u, t2) |> map_substitutions(u, t2)
    else
      unify_concrete(t1, t2, subst)
    end
  end

  defp unify(u, t2, subst) when is_atom(u) do
    if unknown_type?(u) do
      if occurs?(u, t2), do: raise("Type Error: Recursive type check failed (Occurs check)")
      Map.put(subst, u, t2) |> map_substitutions(u, t2)
    else
      unify_concrete(u, t2, subst)
    end
  end

  defp unify(t1, type(goal: _, args: []) = t2, subst) do
    if unknown_type?(t2) do
      unify(t2, t1, subst)
    else
      unify_concrete(t1, t2, subst)
    end
  end

  defp unify(t1, t2, subst), do: unify_concrete(t1, t2, subst)

  defp unify_concrete(type(goal: g1, args: args1), type(goal: g2, args: args2), subst) do
    if (not unknown_type?(g1) and not unknown_type?(g2) and g1 != g2) or
         length(args1) != length(args2) do
      raise "Type Error: Cannot unify #{inspect(g1)} with #{inspect(g2)} or argument count mismatch."
    end

    Enum.zip([g1 | args1], [g2 | args2])
    |> Enum.reduce(subst, fn {a1, a2}, current_subst ->
      unify(apply_subst(a1, current_subst), apply_subst(a2, current_subst), current_subst)
    end)
  end

  defp unify_concrete(t1, t2, subst) when is_atom(t1) and is_atom(t2) do
    if not unknown_type?(t1) and not unknown_type?(t2) and t1 != t2 do
      raise "Type Error: Cannot unify #{inspect(t1)} with #{inspect(t2)}."
    end

    unify(apply_subst(t1, subst), apply_subst(t2, subst), subst)
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
