defmodule THOU.Parser.Parser do
  import HOL.Data
  import HOL.Terms
  import THOU.HOL.Definitions
  import THOU.Util
  import THOU.Parser.Tokenizer

  # Context struct to track variable types and declared constants
  defmodule Context do
    defstruct vars: %{}, consts: %{}

    def new, do: %Context{}

    def put_var(ctx, name, type) do
      %Context{ctx | vars: Map.put(ctx.vars, name, type)}
    end

    def get_type(ctx, name) do
      Map.get(ctx.vars, name) || Map.get(ctx.consts, name)
    end

    # In a full implementation, you would populate consts from previous type declarations
    def put_const(ctx, name, type) do
      %Context{ctx | consts: Map.put(ctx.consts, name, type)}
    end
  end

  # --- Entry Point ---

  def parse(formula_str, context \\ Context.new()) do
    {:ok, tokens, "", _, _, _} = tokenize(formula_str)
    {term, []} = parse_formula(tokens, context)
    term
  end

  # --- Precedence Levels ---

  # Level 1: <, >, <=, =>, <=>, <~>
  defp parse_formula(tokens, ctx) do
    {lhs, rest} = parse_disjunction(tokens, ctx)
    parse_formula_op(lhs, rest, ctx)
  end

  defp parse_formula_op(lhs, [{:equiv, _} | rest], ctx) do
    {rhs, rest2} = parse_formula(rest, ctx)
    # Construct: equivalent_term @ lhs @ rhs
    # Note: We assume standard HOL boolean types for connectives
    term = mk_appl_term(mk_appl_term(equivalent_term(), lhs), rhs)
    {term, rest2}
  end

  defp parse_formula_op(lhs, [{:implies, _} | rest], ctx) do
    {rhs, rest2} = parse_formula(rest, ctx)
    term = mk_appl_term(mk_appl_term(implies_term(), lhs), rhs)
    {term, rest2}
  end

  defp parse_formula_op(lhs, [{:implied_by, _} | rest], ctx) do
    # Desugar: A <= B  becomes  B => A
    {rhs, rest2} = parse_formula(rest, ctx)
    # Note order: implies @ rhs @ lhs
    term = mk_appl_term(mk_appl_term(implies_term(), rhs), lhs)
    {term, rest2}
  end

  defp parse_formula_op(lhs, [{:xor, _} | rest], ctx) do
    # Desugar: A <~> B  becomes  ~(A <=> B)
    {rhs, rest2} = parse_formula(rest, ctx)
    inner = mk_appl_term(mk_appl_term(equivalent_term(), lhs), rhs)
    term = mk_appl_term(neg_term(), inner)
    {term, rest2}
  end

  defp parse_formula_op(lhs, tokens, _ctx), do: {lhs, tokens}

  # Level 2: | (OR), & (AND), ~| (NOR), ~& (NAND)
  defp parse_disjunction(tokens, ctx) do
    {lhs, rest} = parse_conjunction(tokens, ctx)
    parse_disjunction_op(lhs, rest, ctx)
  end

  defp parse_disjunction_op(lhs, [{:or, _} | rest], ctx) do
    {rhs, rest2} = parse_conjunction(rest, ctx)
    term = mk_appl_term(mk_appl_term(or_term(), lhs), rhs)
    parse_disjunction_op(term, rest2, ctx)
  end

  defp parse_disjunction_op(lhs, [{:nor, _} | rest], ctx) do
    # Desugar: A ~| B  becomes  ~(A | B)
    {rhs, rest2} = parse_conjunction(rest, ctx)

    inner = mk_appl_term(mk_appl_term(or_term(), lhs), rhs)
    term = mk_appl_term(neg_term(), inner)
    parse_disjunction_op(term, rest2, ctx)
  end

  defp parse_disjunction_op(lhs, tokens, _ctx), do: {lhs, tokens}

  defp parse_conjunction(tokens, ctx) do
    {lhs, rest} = parse_unitary(tokens, ctx)
    parse_conjunction_op(lhs, rest, ctx)
  end

  defp parse_conjunction_op(lhs, [{:and, _} | rest], ctx) do
    {rhs, rest2} = parse_unitary(rest, ctx)
    term = mk_appl_term(mk_appl_term(and_term(), lhs), rhs)
    parse_conjunction_op(term, rest2, ctx)
  end

  defp parse_conjunction_op(lhs, [{:nand, _} | rest], ctx) do
    # Desugar: A ~& B  becomes  ~(A & B)
    {rhs, rest2} = parse_unitary(rest, ctx)

    inner = mk_appl_term(mk_appl_term(and_term(), lhs), rhs)
    term = mk_appl_term(neg_term(), inner)
    parse_conjunction_op(term, rest2, ctx)
  end

  defp parse_conjunction_op(lhs, tokens, _ctx), do: {lhs, tokens}

  # Level 3: Unitary (~), Quantifiers (!, ?), Equality (=), Application (@)
  defp parse_unitary([{:not, _} | rest], ctx) do
    {term, rest2} = parse_unitary(rest, ctx)
    {mk_appl_term(neg_term(), term), rest2}
  end

  defp parse_unitary([{:forall, _} | rest], ctx), do: parse_quantifier(:pi, rest, ctx)
  defp parse_unitary([{:exists, _} | rest], ctx), do: parse_quantifier(:sigma, rest, ctx)
  defp parse_unitary([{:lambda, _} | rest], ctx), do: parse_lambda(rest, ctx)

  defp parse_unitary([{:pi, _} | [{:lparen, _}, {:lambda, _} | _] = rest], ctx),
    do: parse_quantifier(:sigma, rest, ctx)

  defp parse_unitary([{:sigma, _} | [{:lparen, _}, {:lambda, _} | _] = rest], ctx),
    do: parse_quantifier(:sigma, rest, ctx)

  defp parse_unitary(tokens, ctx) do
    parse_equality(tokens, ctx)
  end

  # Equality (=) requires STRICT type checking to generate the correct constant
  defp parse_equality(tokens, ctx) do
    {lhs, rest} = parse_application(tokens, ctx)

    case rest do
      [{:eq, _} | rest2] ->
        {rhs, rest3} = parse_application(rest2, ctx)

        lhs_type = get_term_type(lhs)

        eq_const_decl = equals_const(lhs_type)
        eq_term = mk_term(eq_const_decl)

        # Build (Eq @ LHS) @ RHS
        term = mk_appl_term(mk_appl_term(eq_term, lhs), rhs)
        {term, rest3}

      [{:neq, _} | rest2] ->
        # != is just ~(A = B)
        {rhs, rest3} = parse_application(rest2, ctx)
        lhs_type = get_term_type(lhs)
        eq_const_decl = equals_const(lhs_type)
        eq_term = mk_term(eq_const_decl)
        inner = mk_appl_term(mk_appl_term(eq_term, lhs), rhs)
        {mk_appl_term(neg_term(), inner), rest3}

      _ ->
        {lhs, rest}
    end
  end

  # Application (@) is Left Associative: f @ a @ b -> (f @ a) @ b
  defp parse_application(tokens, ctx) do
    {lhs, rest} = parse_atomic(tokens, ctx)
    parse_app_chain(lhs, rest, ctx)
  end

  defp parse_app_chain(lhs, [{:app, _} | rest], ctx) do
    {rhs, rest2} = parse_atomic(rest, ctx)
    term = mk_appl_term(lhs, rhs)
    parse_app_chain(term, rest2, ctx)
  end

  defp parse_app_chain(lhs, tokens, _ctx), do: {lhs, tokens}

  # --- Quantifiers and Abstractions ---

  # Handles ! [X:Type, Y:Type]: Body
  defp parse_quantifier(type_key, [{:lbracket, _} | rest], ctx) do
    {vars, [{:rbracket, _}, {:colon, _} | body_tokens]} = parse_typed_vars(rest, [])

    inner_ctx =
      Enum.reduce(vars, ctx, fn {name, type}, acc ->
        Context.put_var(acc, name, type)
      end)

    {body_term, rest_tokens} = parse_formula(body_tokens, inner_ctx)

    term =
      vars
      |> Enum.reverse()
      |> Enum.reduce(body_term, fn {name, var_type}, acc_term ->
        var_const = mk_free_var(name, var_type)
        abs_term = mk_abstr_term(acc_term, var_const)

        pred_type = get_term_type(abs_term)

        quant_const_decl =
          case type_key do
            :pi -> pi_const(pred_type)
            :sigma -> sigma_const(pred_type)
          end

        quant_term = mk_term(quant_const_decl)

        mk_appl_term(quant_term, abs_term)
      end)

    {term, rest_tokens}
  end

  defp parse_quantifier(type_key, [{:lparen, _}, {:lambda, _} | rest], ctx) do
    {abs_term, rest_after_lambda} = parse_lambda(rest, ctx)

    case rest_after_lambda do
      [{:rparen, _} | final_tokens] ->
        pred_type = get_term_type(abs_term)

        quant_const_decl =
          case type_key do
            :pi -> pi_const(pred_type)
            :sigma -> sigma_const(pred_type)
          end

        quant_term = mk_term(quant_const_decl)
        term = mk_appl_term(quant_term, abs_term)

        {term, final_tokens}

      [{type, val} | _] ->
        raise "Syntax Error: Expected closing parenthesis ')' after quantified lambda, found '#{val}' (#{inspect(type)})."

      [] ->
        raise "Syntax Error: Unexpected end of input inside quantified lambda."
    end
  end

  # Handles ^ [X:Type]: Body
  defp parse_lambda([{:lbracket, _} | rest], ctx) do
    {vars, [{:rbracket, _}, {:colon, _} | body_tokens]} = parse_typed_vars(rest, [])

    inner_ctx =
      Enum.reduce(vars, ctx, fn {name, type}, acc ->
        Context.put_var(acc, name, type)
      end)

    {body_term, rest_tokens} = parse_formula(body_tokens, inner_ctx)

    term =
      vars
      |> Enum.reverse()
      |> Enum.reduce(body_term, fn {name, var_type}, acc_term ->
        var_const = mk_free_var(name, var_type)
        mk_abstr_term(acc_term, var_const)
      end)

    {term, rest_tokens}
  end

  # Helper to parse [X: $i, Y: $o]
  defp parse_typed_vars([{:var, name}, {:colon, _} | rest], acc) do
    {type, rest2} = parse_type(rest)
    new_acc = acc ++ [{name, type}]

    case rest2 do
      [{:comma, _} | rest3] -> parse_typed_vars(rest3, new_acc)
      _ -> {new_acc, rest2}
    end
  end

  # --- Types ---

  # Parses $i, $o, or A > B
  defp parse_type(tokens) do
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

  defp parse_atomic_type([{:lparen, _} | rest]) do
    {type, [{:rparen, _} | rest2]} = parse_type(rest)
    {type, rest2}
  end

  # --- Atomics ---

  defp parse_atomic([{:lparen, _} | rest], ctx) do
    {term, [{:rparen, _} | rest2]} = parse_formula(rest, ctx)
    {term, rest2}
  end

  defp parse_atomic([{:var, name} | rest], ctx) do
    case Context.get_type(ctx, name) do
      nil -> raise "Variable #{name} used without type declaration or quantifier binding"
      type -> {mk_term(mk_free_var(name, type)), rest}
    end
  end

  defp parse_atomic([{:atom, name} | rest], ctx) do
    case Context.get_type(ctx, name) do
      nil -> raise "Constant #{name} unknown"
      type -> {mk_term(mk_const(name, type)), rest}
    end
  end

  defp parse_atomic([{:system, "$true"} | rest], _ctx) do
    {true_term(), rest}
  end

  defp parse_atomic([{:system, "$false"} | rest], _ctx) do
    {false_term(), rest}
  end

  defp parse_atomic([{:equiv, _} | rest], _ctx) do
    {equivalent_term(), rest}
  end

  defp parse_atomic([{:implies, _} | rest], _ctx) do
    {implies_term(), rest}
  end

  defp parse_atomic([{:implied_by, _} | rest], _ctx) do
    {implied_by_term(), rest}
  end

  defp parse_atomic([{:xor, _} | rest], _ctx) do
    {xor_term(), rest}
  end

  defp parse_atomic([{:nor, _} | rest], _ctx) do
    {nor_term(), rest}
  end

  defp parse_atomic([{:nand, _} | rest], _ctx) do
    {nand_term(), rest}
  end

  defp parse_atomic([{:pi, _} | rest], _ctx) do
    {mk_term(pi_const(mk_type(:o, [mk_new_unknown_type()]))), rest}
  end

  defp parse_atomic([{:sigma, _} | rest], _ctx) do
    {mk_term(sigma_const(mk_type(:o, [mk_new_unknown_type()]))), rest}
  end

  defp parse_atomic([{:not, _} | rest], _ctx) do
    {neg_term(), rest}
  end

  defp parse_atomic([{:or, _} | rest], _ctx) do
    {or_term(), rest}
  end

  defp parse_atomic([{:and, _} | rest], _ctx) do
    {and_term(), rest}
  end

  defp parse_atomic([{:neq, _} | rest], _ctx) do
    {not_equals_term(mk_new_unknown_type()), rest}
  end

  defp parse_atomic([{:eq, _} | rest], _ctx) do
    {equals_term(mk_new_unknown_type()), rest}
  end

  defp parse_atomic([token | _rest], _ctx) do
    {type, value} = token

    raise "Syntax Error: Expected atomic term (variable, constant, or expression), but found token '#{value}' (: #{inspect(type)})."
  end

  defp parse_atomic([], _ctx) do
    raise "Syntax Error: Unexpected end of input."
  end
end
