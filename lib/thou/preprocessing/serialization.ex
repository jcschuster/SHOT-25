defmodule THOU.Preprocessing.Serialization do
  import HOL.{Data, Terms}
  import THOU.HOL.{Patterns, Definitions}
  import THOU.Preprocessing.Tokenizer

  #############################################################################
  # TERM -> S-EXPRESSION
  #############################################################################

  def to_s_expr(type() = t), do: type_to_s_expr(t)

  def to_s_expr(declaration(kind: :co, name: n, type: t)) do
    "#{n}∷#{to_s_expr(t)}"
  end

  def to_s_expr(declaration(name: n, type: t)) do
    cond do
      is_binary(n) ->
        "$VAR~#{n}∷#{to_s_expr(t)}"

      is_tuple(n) ->
        "$VAR~#{Tuple.to_list(n) |> Enum.map(&inspect/1) |> Enum.join("")}∷#{to_s_expr(t)}"

      true ->
        "$VAR~#{inspect(n)}∷#{to_s_expr(t)}"
    end
  end

  def to_s_expr(hol_term(bvars: [b | bs]) = t) do
    "(^ #{to_s_expr(b)} #{to_s_expr(hol_term(t, bvars: bs))})"
  end

  def to_s_expr(hol_term(head: h, args: [])), do: to_s_expr(h)

  def to_s_expr(equality(a, b)), do: "(= #{to_s_expr(a)} #{to_s_expr(b)})"

  def to_s_expr(hol_term(head: declaration(kind: :co, name: name) = h, args: args))
      when name in ["¬", "∨", "∧", "⊃", "≡"] do
    args_str =
      Enum.map(args, &to_s_expr/1)
      |> Enum.join(" ")

    "(#{to_s_expr(h)} #{args_str})"
  end

  def to_s_expr(hol_term(head: h, args: args)) do
    Enum.reduce(args, to_s_expr(h), &"(@ #{&2} #{to_s_expr(&1)})")
  end

  defp type_to_s_expr(type(goal: g, args: [])), do: Atom.to_string(g)

  defp type_to_s_expr(type(goal: g, args: args)) do
    args_str =
      Enum.map(args, &type_to_s_expr_inner/1)
      |> Enum.join("⇾")

    "#{args_str}⇾#{type_to_s_expr_inner(g)}"
  end

  defp type_to_s_expr_inner(a) when is_atom(a), do: Atom.to_string(a)
  defp type_to_s_expr_inner(type(goal: g, args: [])), do: Atom.to_string(g)

  defp type_to_s_expr_inner(type(goal: g, args: args)) do
    args_str =
      Enum.map(args, &type_to_s_expr_inner/1)
      |> Enum.join("⇾")

    "[#{args_str}⇾#{type_to_s_expr_inner(g)}]"
  end

  #############################################################################
  # S-EXPRESSION -> TERM
  #############################################################################

  def from_s_expr(str) do
    {:ok, tokens, "", _, _, _} = tokenize(str)
    {term, []} = tokens_to_term(tokens)
    term
  end

  defp tokens_to_term([{:var, id}, {:dcolon, _} | rest]) do
    "$VAR~" <> name = id
    {type, rest2} = tokens_to_type(rest)
    {mk_free_var_term(name, type), rest2}
  end

  defp tokens_to_term([{:const, "="} | rest]) do
    case rest do
      [{:dcolon, _} | rest2] ->
        {type, rest3} = tokens_to_type(rest2)
        {mk_const_term("=", type), rest3}

      _ ->
        {arg1, rest2} = tokens_to_term(rest)
        {arg2, rest3} = tokens_to_term(rest2)
        type = get_term_type(arg1)
        {equals_term(type) |> mk_appl_term(arg1) |> mk_appl_term(arg2), rest3}
    end
  end

  defp tokens_to_term([{:const, name}, {:dcolon, _} | rest]) do
    {type, rest2} = tokens_to_type(rest)
    {mk_const_term(name, type), rest2}
  end

  defp tokens_to_term([{:lparen, _}, {:abs, _}, {:var, id}, {:dcolon, _} | rest]) do
    "$VAR~" <> var_name = id
    {var_type, rest2} = tokens_to_type(rest)
    var = mk_free_var(var_name, var_type)
    {body, [{:rparen, _} | rest3]} = tokens_to_term(rest2)
    {mk_abstr_term(body, var), rest3}
  end

  defp tokens_to_term([{:lparen, _}, {:app, _} | rest]) do
    {head, rest2} = tokens_to_term(rest)
    {body, rest3} = tokens_to_term(rest2)
    [{:rparen, _} | rest4] = rest3
    {mk_appl_term(head, body), rest4}
  end

  defp tokens_to_term([{:lparen, _} | rest]) do
    {head, rest2} = tokens_to_term(rest)
    {args, rest3} = collect_args(rest2)

    term = Enum.reduce(args, head, &mk_appl_term(&2, &1))

    {term, rest3}
  end

  defp collect_args(tokens) do
    case tokens do
      [{:rparen, _} | rest] ->
        {[], rest}

      _ ->
        {arg, rest} = tokens_to_term(tokens)
        {args, rest2} = collect_args(rest)
        {[arg | args], rest2}
    end
  end

  defp tokens_to_type(tokens) do
    {lhs, rest} = tokens_to_atomic_type(tokens)

    case rest do
      [{:arrow, _} | rest2] ->
        {rhs, rest3} = tokens_to_type(rest2)
        type = mk_type(rhs, [lhs])
        {type, rest3}

      _ ->
        {lhs, rest}
    end
  end

  defp tokens_to_atomic_type([{:const, t} | rest]), do: {mk_type(String.to_atom(t)), rest}

  defp tokens_to_atomic_type([{:lbracket, _} | rest]) do
    {type, [{:rbracket, _} | rest2]} = tokens_to_type(rest)
    {type, rest2}
  end
end
