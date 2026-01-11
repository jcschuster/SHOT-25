defmodule THOU.Preprocessing.Serialization do
  @moduledoc """
  Contains functionality to serialize and deserialize terms into and from
  s-expressions to be used in the rewriting process.
  """

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.{Patterns, Definitions}
  alias THOU.Preprocessing.SExprTokenizer, as: Tokenizer

  #############################################################################
  # TERM -> S-EXPRESSION
  #############################################################################

  @doc """
  Converts a given term to a string representation as s-expression in a way
  that is reconstructible by `from_s_expr/1`.

  ## Example:

      iex> HOL.Terms.mk_const_term("p", mk_type(:o, [mk_type(:i)])) |> to_s_expr()
      "(^ $VAR~1∷i (@ p∷i⇾o $VAR~1∷i))"
  """
  @spec to_s_expr(HOL.Data.hol_term()) :: String.t()
  def to_s_expr(term)

  def to_s_expr(hol_term(bvars: [b | bs]) = t) do
    "(^ #{serialize_decl(b)} #{to_s_expr(hol_term(t, bvars: bs))})"
  end

  def to_s_expr(hol_term(head: h, args: [])), do: serialize_decl(h)

  def to_s_expr(equality(a, b)), do: "(= #{to_s_expr(a)} #{to_s_expr(b)})"

  def to_s_expr(hol_term(head: declaration(kind: :co, name: name) = h, args: args))
      when name in ["¬", "∨", "∧", "⊃", "≡"] do
    args_str = Enum.map_join(args, " ", &to_s_expr/1)

    "(#{serialize_decl(h)} #{args_str})"
  end

  def to_s_expr(hol_term(head: h, args: args)) do
    Enum.reduce(args, serialize_decl(h), &"(@ #{&2} #{to_s_expr(&1)})")
  end

  defp serialize_decl(declaration(kind: :co, name: n, type: t)) do
    "#{n}∷#{serialize_type(t)}"
  end

  defp serialize_decl(declaration(name: n, type: t)) do
    "$VAR~#{encode_var_name(n)}∷#{serialize_type(t)}"
  end

  defp encode_var_name(n) when is_binary(n), do: n
  defp encode_var_name(n) when is_integer(n), do: Integer.to_string(n)
  defp encode_var_name(n), do: "HEX:" <> Base.encode16(:erlang.term_to_binary(n))

  defp serialize_type(type(goal: g, args: [])), do: Atom.to_string(g)

  defp serialize_type(type(goal: g, args: args)) do
    args_str = Enum.map_join(args, "⇾", &serialize_type_inner/1)

    "#{args_str}⇾#{serialize_type_inner(g)}"
  end

  defp serialize_type_inner(a) when is_atom(a), do: Atom.to_string(a)
  defp serialize_type_inner(type(goal: g, args: [])), do: Atom.to_string(g)

  defp serialize_type_inner(type(goal: g, args: args)) do
    args_str = Enum.map_join(args, "⇾", &serialize_type_inner/1)

    "[#{args_str}⇾#{serialize_type_inner(g)}]"
  end

  #############################################################################
  # S-EXPRESSION -> TERM
  #############################################################################

  @doc """
  Deserializes a s-expression to its corresponding representation as
  `HOL.Data.hol_term()`.
  """
  @spec from_s_expr(String.t()) :: HOL.Data.hol_term()
  def from_s_expr(str) do
    {:ok, tokens, "", _, _, _} = Tokenizer.tokenize(str)
    {term, []} = tokens_to_term(tokens)
    term
  end

  defp tokens_to_term([{:var, id}, {:dcolon, _} | rest]) do
    "$VAR~" <> raw_name = id
    var_name = decode_var_name(raw_name)
    {var_type, rest2} = tokens_to_type(rest)
    var = declaration(kind: :fv, name: var_name, type: var_type)
    {mk_term(var), rest2}
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
    "$VAR~" <> raw_name = id
    var_name = decode_var_name(raw_name)
    {var_type, rest2} = tokens_to_type(rest)
    var = declaration(kind: :fv, name: var_name, type: var_type)
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

  defp decode_var_name("HEX:" <> hex_str) do
    Base.decode16!(hex_str) |> :erlang.binary_to_term()
  end

  defp decode_var_name(n), do: n

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
