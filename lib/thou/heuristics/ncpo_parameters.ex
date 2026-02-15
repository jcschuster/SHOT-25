defmodule THOU.Heuristics.NCPOParameters do
  @moduledoc """
  Contains the hard-coded parameters of NCPO which include an ordering on base
  types, a general type-ordering, a precedence map for constants and the status
  (lexicographic or multiset) of constants.

  To use NCPO as a termination order, these parameter would need via
  SAT-Solving by encoding the conditions (well-foundedness etc.) of the
  parameters.
  """

  import HOL.Data
  import BeHOLd.ClassicalHOL.Definitions

  @type type_or_atom() :: HOL.Data.type() | atom()
  @type base_type_or_atom() :: {:type, atom(), []} | atom()

  @spec precedence(binary()) :: non_neg_integer()
  def precedence(name) do
    case symbol_precedence_map()[name] do
      nil ->
        if String.starts_with?(name, "__sk_") do
          8
        else
          user_constant_precedence()
        end

      precedence_value ->
        precedence_value
    end
  end

  defp symbol_precedence_map do
    %{
      "⊤" => 1,
      "⊥" => 1,
      "¬" => 2,
      "∨" => 3,
      "∧" => 3,
      "⊃" => 4,
      "≡" => 5,
      "=" => 6,
      "Π" => 7,
      "Σ" => 7
    }
  end

  defp user_constant_precedence, do: 1

  @spec status(binary()) :: :lex | :mul
  def status(name) do
    if name in (signature_symbols() -- ["⊃"]) do
      :mul
    else
      :lex
    end
  end

  @spec base_type_precedence(base_type_or_atom()) :: non_neg_integer()
  def base_type_precedence(base_type)

  def base_type_precedence(type(goal: s, args: [])), do: base_type_precedence(s)

  def base_type_precedence(s) when is_atom(s) do
    case s do
      :o ->
        1

      :i ->
        2

      _ ->
        if String.starts_with?("__unknown_", Atom.to_string(s)) do
          4
        else
          3
        end
    end
  end

  @spec type_geq?(type_or_atom(), type_or_atom()) :: boolean()
  def type_geq?(t, u), do: t == u || type_gt?(t, u)

  @spec type_gt?(type_or_atom(), type_or_atom()) :: boolean()
  def type_gt?(type1, type2)

  def type_gt?(t, t), do: false

  def type_gt?(t, u) do
    cond do
      subtype_or_eq?(u, get_args_safe(t)) ->
        true

      right_subterm?(t, u) ->
        true

      base_type_precedence(get_goal_safe(t)) > base_type_precedence(get_goal_safe(u)) ->
        Enum.all?(get_args_safe(u), &type_gt?(t, &1))

      get_goal_safe(t) == get_goal_safe(u) ->
        lexicographic_gt?(get_args_safe(t), get_args_safe(u))

      true ->
        false
    end
  end

  defp get_args_safe(type(args: args)), do: args
  defp get_args_safe(_), do: []

  defp get_goal_safe(type(goal: g)), do: g
  defp get_goal_safe(atom) when is_atom(atom), do: atom

  defp right_subterm?(type(goal: g, args: [_ | t_rest]), type(goal: g, args: u_args)) do
    if t_rest == u_args do
      true
    else
      right_subterm?(type(goal: g, args: t_rest), type(goal: g, args: u_args))
    end
  end

  defp right_subterm?(_, _), do: false

  defp subtype_or_eq?(_, []), do: false

  defp subtype_or_eq?(u, [arg | rest]) do
    arg == u || type_gt?(arg, u) || subtype_or_eq?(u, rest)
  end

  defp lexicographic_gt?([], []), do: false

  defp lexicographic_gt?([t1 | t_rest], [u1 | u_rest]) do
    cond do
      type_gt?(t1, u1) -> true
      t1 == u1 -> lexicographic_gt?(t_rest, u_rest)
      true -> false
    end
  end

  defp lexicographic_gt?(_, _), do: false
end
