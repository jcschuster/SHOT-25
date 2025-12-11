defmodule THOU.Parser.Parser do
  import HOL.Data
  import HOL.Terms
  import THOU.HOL.Definitions
  import THOU.Util
  import THOU.Parser.Tokenizer
  alias THOU.Parser.TypeInference

  # Context struct to track variable types and declared constants
  defmodule Context do
    defstruct vars: %{}, consts: %{}, constraints: MapSet.new()

    def new, do: %Context{}

    def put_var(ctx, name, type) do
      %{ctx | vars: Map.put(ctx.vars, name, type)}
    end

    def get_type(ctx, name) do
      Map.get(ctx.vars, name) || Map.get(ctx.consts, name)
    end

    def put_const(ctx, name, type) do
      %{ctx | consts: Map.put(ctx.consts, name, type)}
    end

    def add_constraint(ctx, t1, t2) do
      %{ctx | constraints: MapSet.put(ctx.constraints, {t1, t2})}
    end
  end

  # --- Entry Point ---

  def parse(formula_str, context \\ Context.new()) do
    {:ok, tokens, "", _, _, _} = tokenize(formula_str)
    parse_tokens(tokens, context)
  end

  def parse_tokens(tokens, context \\ Context.new()) do
    {pre_term, [], final_ctx} = parse_formula(tokens, context)
    substitutions = TypeInference.solve(final_ctx.constraints)
    build_term(pre_term, substitutions)
  end

  # --- Term Builder ---

  defp build_term({:pre_app, f, arg, _type}, subst) do
    mk_appl_term(build_term(f, subst), build_term(arg, subst))
  end

  defp build_term({:pre_abs, name, var_type, body, _type}, subst) do
    concrete_var_type = TypeInference.apply_subst(var_type, subst)
    var = mk_free_var(name, concrete_var_type)
    mk_abstr_term(build_term(body, subst), var)
  end

  defp build_term({:pre_var, name, type}, subst) do
    mk_term(mk_free_var(name, TypeInference.apply_subst(type, subst)))
  end

  defp build_term({:pre_const, "!=", type}, subst) do
    not_equals_term(TypeInference.apply_subst(type, subst))
  end

  defp build_term({:pre_const, "<~>", _}, _), do: xor_term()
  defp build_term({:pre_const, "<=", _}, _), do: implied_by_term()
  defp build_term({:pre_const, "~|", _}, _), do: nor_term()
  defp build_term({:pre_const, "~&", _}, _), do: nand_term()

  defp build_term({:pre_const, name, type}, subst) do
    mk_term(mk_const(name, TypeInference.apply_subst(type, subst)))
  end

  # --- Parsing Logic ---

  defp constrain(ctx, term_node, expected_type) do
    term_type = get_pre_type(term_node)
    Context.add_constraint(ctx, term_type, expected_type)
  end

  defp get_pre_type({_, _, _, type}), do: type
  defp get_pre_type({_, _, _, _, type}), do: type
  defp get_pre_type({_, _, type}), do: type

  # --- Precedence Levels ---

  # Level 1: <, >, <=, =>, <=>, <~>
  def parse_formula(tokens, ctx) do
    {lhs, rest, ctx2} = parse_disjunction(tokens, ctx)
    parse_formula_op(lhs, rest, ctx2)
  end

  defp parse_formula_op(lhs, [{:equiv, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_formula(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_app, {:pre_const, "≡", type_ooo()}, lhs, type_oo()}, rhs, type_o()}

    {term, rest2, ctx3}
  end

  defp parse_formula_op(lhs, [{:implies, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_formula(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_app, {:pre_const, "⊃", type_ooo()}, lhs, type_oo()}, rhs, type_o()}

    {term, rest2, ctx3}
  end

  defp parse_formula_op(lhs, [{:implied_by, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_formula(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_app, {:pre_const, "⊃", type_ooo()}, rhs, type_oo()}, lhs, type_o()}

    {term, rest2, ctx3}
  end

  defp parse_formula_op(lhs, [{:xor, _} | rest], ctx) do
    # Desugar: A <~> B  becomes  ~(A <=> B)
    {rhs, rest2, ctx2} = parse_formula(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_const, "¬", type_oo()},
       {:pre_app, {:pre_app, {:pre_const, "≡", type_ooo()}, lhs, type_oo()}, rhs, type_o()},
       type_o()}

    {term, rest2, ctx3}
  end

  defp parse_formula_op(lhs, tokens, ctx), do: {lhs, tokens, ctx}

  # Level 2: | (OR), & (AND), ~| (NOR), ~& (NAND)
  defp parse_disjunction(tokens, ctx) do
    {lhs, rest, ctx2} = parse_conjunction(tokens, ctx)
    parse_disjunction_op(lhs, rest, ctx2)
  end

  defp parse_disjunction_op(lhs, [{:or, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_conjunction(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_app, {:pre_const, "∨", type_ooo()}, lhs, type_oo()}, rhs, type_o()}

    parse_disjunction_op(term, rest2, ctx3)
  end

  defp parse_disjunction_op(lhs, [{:nor, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_conjunction(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_const, "¬", type_oo()},
       {:pre_app, {:pre_app, {:pre_const, "∨", type_ooo()}, lhs, type_oo()}, rhs, type_o()},
       type_o()}

    parse_disjunction_op(term, rest2, ctx3)
  end

  defp parse_disjunction_op(lhs, tokens, ctx), do: {lhs, tokens, ctx}

  defp parse_conjunction(tokens, ctx) do
    {lhs, rest, ctx2} = parse_unitary(tokens, ctx)
    parse_conjunction_op(lhs, rest, ctx2)
  end

  defp parse_conjunction_op(lhs, [{:and, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_unitary(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term = {:pre_app, {:pre_app, {:pre_const, "∧", type_ooo()}, lhs, type_oo()}, rhs, type_o()}

    parse_conjunction_op(term, rest2, ctx3)
  end

  defp parse_conjunction_op(lhs, [{:nand, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_unitary(rest, ctx)
    ctx3 = ctx2 |> constrain(lhs, type_o()) |> constrain(rhs, type_o())

    term =
      {:pre_app, {:pre_const, "¬", type_oo()},
       {:pre_app, {:pre_app, {:pre_const, "∧", type_ooo()}, lhs, type_oo()}, rhs, type_o()},
       type_o()}

    parse_conjunction_op(term, rest2, ctx3)
  end

  defp parse_conjunction_op(lhs, tokens, ctx), do: {lhs, tokens, ctx}

  # Level 3: Unitary (~), Quantifiers (!, ?), Equality (=), Application (@)
  defp parse_unitary([{:not, _} | rest], ctx) do
    {term, rest2, ctx2} = parse_unitary(rest, ctx)
    {{:pre_app, {:pre_const, "¬", type_oo()}, term, type_o()}, rest2, ctx2}
  end

  defp parse_unitary([{:forall, _} | rest], ctx), do: parse_quantifier(:pi, rest, ctx)
  defp parse_unitary([{:exists, _} | rest], ctx), do: parse_quantifier(:sigma, rest, ctx)
  defp parse_unitary([{:lambda, _} | rest], ctx), do: parse_lambda(rest, ctx)

  defp parse_unitary([{:pi, _} | [{:lparen, _}, {:lambda, _} | _] = rest], ctx),
    do: parse_quantifier(:sigma, rest, ctx)

  defp parse_unitary([{:sigma, _} | [{:lparen, _}, {:lambda, _} | _] = rest], ctx),
    do: parse_quantifier(:sigma, rest, ctx)

  defp parse_unitary(tokens, ctx), do: parse_equality(tokens, ctx)

  # Equality (=) requires STRICT type checking to generate the correct constant
  defp parse_equality(tokens, ctx) do
    {lhs, rest, ctx2} = parse_application(tokens, ctx)

    case rest do
      [{:eq, _} | rest2] ->
        {rhs, rest3, ctx3} = parse_application(rest2, ctx2)

        lhs_type = get_pre_type(lhs)
        rhs_type = get_pre_type(rhs)
        ctx4 = Context.add_constraint(ctx3, lhs_type, rhs_type)

        eq_type = mk_type(:o, [lhs_type, lhs_type])

        term =
          {:pre_app, {:pre_app, {:pre_const, "=", eq_type}, lhs, mk_type(:o, [lhs_type])}, rhs,
           type_o()}

        {term, rest3, ctx4}

      [{:neq, _} | rest2] ->
        {rhs, rest3, ctx3} = parse_application(rest2, ctx2)

        lhs_type = get_pre_type(lhs)
        rhs_type = get_pre_type(rhs)
        ctx4 = Context.add_constraint(ctx3, lhs_type, rhs_type)

        eq_type = mk_type(:o, [lhs_type, lhs_type])

        term =
          {:pre_app, {:pre_const, "¬", type_oo()},
           {:pre_app, {:pre_app, {:pre_const, "=", eq_type}, lhs, mk_type(:o, [lhs_type])}, rhs,
            type_o()}, type_o()}

        {term, rest3, ctx4}

      _ ->
        {lhs, rest, ctx2}
    end
  end

  # Application (@) is Left Associative: f @ a @ b -> (f @ a) @ b
  defp parse_application(tokens, ctx) do
    {lhs, rest, ctx2} = parse_atomic(tokens, ctx)
    parse_app_chain(lhs, rest, ctx2)
  end

  defp parse_app_chain(lhs, [{:app, _} | rest], ctx) do
    {rhs, rest2, ctx2} = parse_atomic(rest, ctx)

    t_f = get_pre_type(lhs)
    t_x = get_pre_type(rhs)
    t_ret = mk_new_unknown_type()

    arrow_type = mk_type(t_ret, [t_x])
    ctx3 = Context.add_constraint(ctx2, t_f, arrow_type)

    term = {:pre_app, lhs, rhs, t_ret}
    parse_app_chain(term, rest2, ctx3)
  end

  defp parse_app_chain(lhs, tokens, ctx), do: {lhs, tokens, ctx}

  # --- Quantifiers and Abstractions ---

  # Handles ! [X:Type, Y:Type]: Body
  defp parse_quantifier(type_key, [{:lbracket, _} | rest], ctx) do
    {vars, [{:rbracket, _}, {:colon, _} | body_tokens]} = parse_typed_vars_with_inference(rest)

    inner_ctx =
      Enum.reduce(vars, ctx, fn {name, type}, acc ->
        Context.put_var(acc, name, type)
      end)

    {body_pre_term, rest_tokens, body_ctx} = parse_formula(body_tokens, inner_ctx)

    final_ctx = Context.add_constraint(body_ctx, get_pre_type(body_pre_term), type_o())

    outer_ctx = %{ctx | constraints: final_ctx.constraints}

    term =
      Enum.reverse(vars)
      |> Enum.reduce(body_pre_term, fn {name, var_type}, acc_term ->
        abs_type = mk_type(:o, [var_type])
        abs_node = {:pre_abs, name, var_type, acc_term, abs_type}

        quant_type = mk_type(:o, [abs_type])

        quant_name =
          case type_key do
            :pi -> "Π"
            :sigma -> "Σ"
          end

        quant_const = {:pre_const, quant_name, quant_type}
        {:pre_app, quant_const, abs_node, type_o()}
      end)

    {term, rest_tokens, outer_ctx}
  end

  defp parse_quantifier(type_key, [{:lparen, _}, {:lambda, _} | rest], ctx) do
    {abs_term, rest_after_lambda, lambda_ctx} = parse_lambda(rest, ctx)

    case rest_after_lambda do
      [{:rparen, _} | final_tokens] ->
        abs_type = get_pre_type(abs_term)
        domain_type = mk_new_unknown_type()
        expected_pred_type = mk_type(:o, [domain_type])

        final_ctx = Context.add_constraint(lambda_ctx, abs_type, expected_pred_type)

        quant_name =
          case type_key do
            :pi -> "Π"
            :sigma -> "Σ"
          end

        quant_const = {:pre_const, quant_name, mk_type(:o, [expected_pred_type])}

        term = {:pre_app, quant_const, abs_term, type_o()}
        {term, final_tokens, final_ctx}

      [{type, val} | _] ->
        raise "Syntax Error: Expected ')', found '#{val}' (#{inspect(type)})."

      [] ->
        raise "Syntax Error: Unexpected end of input."
    end
  end

  # Handles ^ [X:Type]: Body
  defp parse_lambda([{:lbracket, _} | rest], ctx) do
    {vars, rest_after_vars} = parse_typed_vars_with_inference(rest)

    inner_ctx = Enum.reduce(vars, ctx, fn {n, t}, c -> Context.put_var(c, n, t) end)

    [{:rbracket, _}, {:colon, _} | body_tokens] = rest_after_vars
    {body_term, rest_tokens, body_ctx} = parse_formula(body_tokens, inner_ctx)

    final_ctx = %{ctx | constraints: body_ctx.constraints}

    term =
      Enum.reverse(vars)
      |> Enum.reduce(body_term, fn {name, type}, acc ->
        body_type = get_pre_type(acc)
        abs_type = mk_type(body_type, [type])
        {:pre_abs, name, type, acc, abs_type}
      end)

    {term, rest_tokens, final_ctx}
  end

  defp parse_typed_vars_with_inference(tokens, acc \\ []) do
    case tokens do
      [{:var, name}, {:comma, _} | rest] ->
        t = mk_new_unknown_type()
        parse_typed_vars_with_inference(rest, acc ++ [{name, t}])

      [{:var, name}, {:rbracket, _} = rb | rest] ->
        t = mk_new_unknown_type()
        {acc ++ [{name, t}], [rb | rest]}

      [{:var, name}, {:colon, _} | rest] ->
        {type, rest2} = parse_type(rest)
        new_acc = acc ++ [{name, type}]

        case rest2 do
          [{:comma, _} | rest3] -> parse_typed_vars_with_inference(rest3, new_acc)
          _ -> {new_acc, rest2}
        end
    end
  end

  # --- Types ---

  # Parses $i, $o, or A > B
  def parse_type(tokens) do
    {lhs, rest} = parse_atomic_type(tokens)

    case rest do
      [{:arrow, _} | rest2] ->
        {rhs, rest3} = parse_type(rest2)
        type = mk_type(rhs, [lhs])
        {type, rest3}

      _ ->
        {lhs, rest}
    end
  end

  defp parse_atomic_type([{:system, "$i"} | rest]), do: {mk_type(:i), rest}
  defp parse_atomic_type([{:system, "$o"} | rest]), do: {mk_type(:o), rest}
  defp parse_atomic_type([{:atom, name} | rest]), do: {mk_type(String.to_atom(name)), rest}

  defp parse_atomic_type([{:lparen, _} | rest]) do
    {type, [{:rparen, _} | rest2]} = parse_type(rest)
    {type, rest2}
  end

  # --- Atomics ---

  defp parse_atomic([{:lparen, _} | rest], ctx) do
    {term, [{:rparen, _} | rest2], ctx2} = parse_formula(rest, ctx)
    {term, rest2, ctx2}
  end

  defp parse_atomic([{:var, name} | rest], ctx) do
    case Context.get_type(ctx, name) do
      nil ->
        new_type = mk_new_unknown_type()
        ctx2 = Context.put_var(ctx, name, new_type)
        {{:pre_var, name, new_type}, rest, ctx2}

      type ->
        {{:pre_var, name, type}, rest, ctx}
    end
  end

  defp parse_atomic([{:atom, name} | rest], ctx) do
    case Context.get_type(ctx, name) do
      nil ->
        new_type = mk_new_unknown_type()
        ctx2 = Context.put_const(ctx, name, new_type)
        {{:pre_const, name, new_type}, rest, ctx2}

      type ->
        {{:pre_const, name, type}, rest, ctx}
    end
  end

  defp parse_atomic([{:system, "$true"} | rest], ctx) do
    {{:pre_const, "⊤", type_o()}, rest, ctx}
  end

  defp parse_atomic([{:system, "$false"} | rest], ctx) do
    {{:pre_const, "⊥", type_o()}, rest, ctx}
  end

  defp parse_atomic([{:eq, _} | rest], ctx) do
    alpha = mk_new_unknown_type()
    type = mk_type(:o, [alpha, alpha])
    {{:pre_const, "=", type}, rest, ctx}
  end

  defp parse_atomic([{:neq, _} | rest], ctx) do
    alpha = mk_new_unknown_type()
    type = mk_type(:o, [alpha, alpha])
    {{:pre_const, "!=", type}, rest, ctx}
  end

  defp parse_atomic([{:equiv, _} | rest], ctx) do
    {{:pre_const, "≡", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:implies, _} | rest], ctx) do
    {{:pre_const, "⊃", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:implied_by, _} | rest], ctx) do
    {{:pre_const, "<=", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:xor, _} | rest], ctx) do
    {{:pre_const, "<~>", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:nor, _} | rest], ctx) do
    {{:pre_const, "~|", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:nand, _} | rest], ctx) do
    {{:pre_const, "~&", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:pi, _} | rest], ctx) do
    alpha = mk_new_unknown_type()
    pred_type = mk_type(:o, [alpha])
    type = mk_type(:o, [pred_type])
    {{:pre_const, "Π", type}, rest, ctx}
  end

  defp parse_atomic([{:sigma, _} | rest], ctx) do
    alpha = mk_new_unknown_type()
    pred_type = mk_type(:o, [alpha])
    type = mk_type(:o, [pred_type])
    {{:pre_const, "Σ", type}, rest, ctx}
  end

  defp parse_atomic([{:lambda, _} | rest], ctx) do
    parse_lambda(rest, ctx)
  end

  defp parse_atomic([{:not, _} | rest], ctx) do
    {{:pre_const, "¬", type_oo()}, rest, ctx}
  end

  defp parse_atomic([{:or, _} | rest], ctx) do
    {{:pre_const, "∨", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([{:and, _} | rest], ctx) do
    {{:pre_const, "∧", type_ooo()}, rest, ctx}
  end

  defp parse_atomic([token | _rest], _ctx) do
    {type, value} = token

    raise "Syntax Error: Expected atomic term (variable, constant, or expression), but found token '#{value}' (: #{inspect(type)})."
  end

  defp parse_atomic([], _ctx) do
    raise "Syntax Error: Unexpected end of input."
  end
end
