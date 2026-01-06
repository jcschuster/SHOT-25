defmodule THOU.Parser.TPTP do
  import HOL.Data
  import THOU.HOL.{Definitions, Patterns}
  alias THOU.Parser.TPTPTokenizer, as: Tokenizer
  alias THOU.Parser.Parser
  alias THOU.Parser.Parser.Context

  defmodule Problem do
    defstruct path: "", includes: [], types: %{}, definitions: [], axioms: [], conjecture: nil
  end

  #############################################################################
  # TERM TO TPTP REPRESENTATION
  #############################################################################

  def type_to_tptp(:o), do: "$o"
  def type_to_tptp(:i), do: "$i"
  def type_to_tptp(a) when is_atom(a), do: Atom.to_string(a)
  def type_to_tptp(type_o()), do: "$o"
  def type_to_tptp(type_i()), do: "$i"
  def type_to_tptp(type(goal: g, args: [])) when is_atom(g), do: Atom.to_string(g)

  def type_to_tptp(type(goal: g, args: args)) do
    args_str = Enum.map(args, &type_to_tptp_inner/1) |> Enum.join(" > ")
    "#{args_str} > #{type_to_tptp(g)}"
  end

  defp type_to_tptp_inner(type(args: []) = type), do: type_to_tptp(type)

  defp type_to_tptp_inner(type(goal: g, args: args)) do
    args_str = Enum.map(args, &type_to_tptp_inner/1) |> Enum.join(" > ")
    "(#{args_str} > #{type_to_tptp(g)})"
  end

  def term_to_tptp(true_const()), do: "$true"
  def term_to_tptp(false_const()), do: "$false"
  def term_to_tptp(neg_const()), do: "~"
  def term_to_tptp(or_const()), do: "|"
  def term_to_tptp(and_const()), do: "&"
  def term_to_tptp(implies_const()), do: "=>"
  def term_to_tptp(equivalent_const()), do: "<=>"
  def term_to_tptp(equals_const(_)), do: "="
  def term_to_tptp(pi_const(_)), do: "!"
  def term_to_tptp(sigma_const(_)), do: "?"
  def term_to_tptp(declaration(kind: :bv, name: name)), do: "BV__#{name}"

  def term_to_tptp(declaration(kind: :co, name: "__" <> name)) do
    "skolem_" <> String.downcase(name)
  end

  def term_to_tptp(declaration(kind: :co, name: name)), do: String.downcase(name)

  def term_to_tptp(declaration(kind: :fv, name: name)) when is_binary(name) do
    String.capitalize(name)
  end

  def term_to_tptp(declaration(kind: :fv, name: name)) do
    "VAR_" <> String.replace(inspect(name), ~r/[^0-9]/, "")
  end

  def term_to_tptp(nor_term()), do: "~|"
  def term_to_tptp(nand_term()), do: "~&"
  def term_to_tptp(implied_by_term()), do: "<="
  def term_to_tptp(xor_term()), do: "<~>"
  def term_to_tptp(not_equals_term(_)), do: "!="

  def term_to_tptp(hol_term(bvars: [], head: or_const(), args: args)) do
    case args do
      [] -> "|"
      [a] -> "( | @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} | #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: [], head: and_const(), args: args)) do
    case args do
      [] -> "&"
      [a] -> "( & @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} & #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: [], head: implies_const(), args: args)) do
    case args do
      [] -> "=>"
      [a] -> "( => @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} => #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: [], head: equivalent_const(), args: args)) do
    case args do
      [] -> "<=>"
      [a] -> "( <=> @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} <=> #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: [], head: equals_const(_), args: args)) do
    case args do
      [] -> "="
      [a] -> "( = @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} = #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(negated(hol_term(bvars: [], head: or_const(), args: args))) do
    case args do
      [] -> "~|"
      [a] -> "( ~| @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} ~| #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(negated(hol_term(bvars: [], head: and_const(), args: args))) do
    case args do
      [] -> "~&"
      [a] -> "( ~& @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} ~& #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(negated(hol_term(bvars: [], head: equivalent_const(), args: args))) do
    case args do
      [] -> "<~>"
      [a] -> "( <~> @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} <~> #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(negated(hol_term(bvars: [], head: equals_const(_), args: args))) do
    case args do
      [] -> "!="
      [a] -> "( != @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} != #{term_to_tptp(b)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: [], head: neg_const(), args: [inner])) do
    "~ #{term_to_tptp(inner)}"
  end

  def term_to_tptp(
        hol_term(
          bvars: [],
          head: pi_const(_),
          args: [hol_term(bvars: bvars) = inner]
        ) = term
      ) do
    case bvars do
      [] ->
        "!! ( #{term_to_tptp(inner)} )"

      [_] ->
        {vars, rest} = collect_quantified_vars("Π", term)
        "! [#{Enum.join(vars, ", ")}]: ( #{term_to_tptp(rest)} )"
    end
  end

  def term_to_tptp(
        hol_term(
          bvars: [],
          head: sigma_const(_),
          args: [hol_term(bvars: bvars) = inner]
        ) = term
      ) do
    case bvars do
      [] ->
        "?? ( #{term_to_tptp(inner)} )"

      [_] ->
        {vars, rest} = collect_quantified_vars("Σ", term)
        "? [#{Enum.join(vars, ", ")}]: ( #{term_to_tptp(rest)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: [], head: head, args: args, type: type) = term) do
    case args do
      [] ->
        term_to_tptp(head)

      [arg] ->
        case arg do
          hol_term(bvars: [], head: declaration(name: n), args: [])
          when n in signature_symbols() ->
            "( (#{term_to_tptp(head)}) @ #{term_to_tptp(arg)} )"

          _ ->
            if arg in [implied_by_term(), xor_term(), nand_term(), nor_term()] or
                 match?(not_equals_term(_), arg) do
              "( (#{term_to_tptp(head)}) @ #{term_to_tptp(arg)} )"
            else
              "( #{term_to_tptp(head)} @ #{term_to_tptp(arg)} )"
            end
        end

      _ ->
        [hol_term(type: t) = last_arg | rest] = Enum.reverse(args)

        head_fvars =
          case head do
            declaration(kind: :fv) -> [head]
            hol_term(fvars: fvars) -> fvars
            _ -> []
          end

        reduced_fvars =
          (head_fvars ++ Enum.reduce(rest, [], &(get_fvars(&1) ++ &2))) |> Enum.uniq()

        "( #{term_to_tptp(hol_term(term, head: head, args: rest, type: mk_type(type, [t]), fvars: reduced_fvars))} @ " <>
          "#{term_to_tptp(last_arg)} )"
    end
  end

  def term_to_tptp(hol_term(bvars: bvars, max_num: max_num) = term) do
    "^ [#{Enum.map(bvars, &"#{term_to_tptp(&1)} : #{type_to_tptp(get_type(&1))}") |> Enum.join(", ")}]: " <>
      "( #{term_to_tptp(hol_term(term, bvars: [], max_num: max_num - length(bvars)))} )"
  end

  defp collect_quantified_vars(quantifier_name, term, acc \\ [])

  defp collect_quantified_vars(
         quantifier_name,
         hol_term(
           bvars: [],
           head: declaration(name: quantifier_name),
           args: [hol_term(bvars: [var], max_num: max_num) = expr]
         ),
         acc
       ) do
    declaration(type: t) = var
    new_acc = acc ++ ["#{term_to_tptp(var)} : #{type_to_tptp(t)}"]

    collect_quantified_vars(
      quantifier_name,
      hol_term(expr, bvars: [], max_num: max_num - 1),
      new_acc
    )
  end

  defp collect_quantified_vars(_quantifier, term, acc), do: {acc, term}

  #############################################################################
  # TPTP REPRESENTATION TO TERM
  #############################################################################

  def parse_file(problem, is_tptp \\ true) do
    path =
      if is_tptp and System.get_env("TPTP_ROOT") == nil do
        raise "Error: TPTP_ROOT environment variable is not set"
      else
        if is_tptp do
          Path.join(System.get_env("TPTP_ROOT"), problem)
        else
          problem
        end
      end

    case File.read(path) do
      {:ok, content} -> parse_string(content, path)
      {:error, reason} -> {:error, "Could not read file #{path}: #{reason}"}
    end
  end

  def parse_string(content, path \\ "memory") do
    {:ok, tokens, _, _, _, _} = Tokenizer.tokenize(content)

    problem = %Problem{path: path}

    process_tokens(tokens, problem)
  end

  defp process_tokens([], problem), do: {:ok, problem}

  defp process_tokens(
         [
           {:keyword, :include},
           {:lparen, _},
           {:distinct, file_path},
           {:rparen, _},
           {:dot, _} | rest
         ],
         problem
       ) do
    case parse_file(file_path) do
      {:ok, included_problem} ->
        merged_problem = merge_problems(problem, included_problem)
        process_tokens(rest, merged_problem)

      error ->
        error
    end
  end

  defp process_tokens(
         [
           {:keyword, :thf},
           {:lparen, _},
           {:atom, name},
           {:comma, _},
           {:role, role},
           {:comma, _} | rest
         ],
         problem
       ) do
    {formula_tokens, remaining_tokens} = extract_formula(rest)

    case role do
      :type ->
        {entry_name, type_struct} = parse_type_decl(formula_tokens)
        new_types = Map.put(problem.types, entry_name, type_struct)
        process_tokens(remaining_tokens, %{problem | types: new_types})

      _ ->
        try do
          ctx = build_context(problem)
          term = Parser.parse_tokens(formula_tokens, ctx)

          new_problem =
            case role do
              :definition ->
                %{problem | definitions: problem.definitions ++ [{name, term}]}

              :axiom ->
                %{problem | axioms: problem.axioms ++ [{name, term}]}

              :conjecture ->
                %{problem | conjecture: {name, term}}

              _ ->
                problem
            end

          process_tokens(remaining_tokens, new_problem)
        rescue
          e ->
            # === DEBUGGING TRAP ===
            IO.puts("\n========================================")
            IO.puts("CRASH DETECTED PARSING: #{name}")
            IO.puts("TYPES: #{inspect(problem.types, limit: :infinity)}")
            IO.puts("ROLE: #{role}")
            IO.puts("TOKENS: #{inspect(formula_tokens, limit: :infinity)}")
            IO.puts("========================================\n")

            # Re-raise the error so you still get the stack trace
            reraise e, __STACKTRACE__
        end
    end
  end

  defp extract_formula(tokens) do
    split_at_entry_end(tokens, 0, [])
  end

  defp split_at_entry_end([{:rparen, _}, {:dot, _} | rest], 0, acc), do: {Enum.reverse(acc), rest}

  defp split_at_entry_end([], _depth, _acc) do
    raise "TPTP Parser Error: Unexpected end of file while extracting formula. Missing ' thf( ... ). ' closing sequence."
  end

  defp split_at_entry_end([{:lparen, _} = t | rest], depth, acc),
    do: split_at_entry_end(rest, depth + 1, [t | acc])

  defp split_at_entry_end([{:rparen, _} = t | rest], depth, acc),
    do: split_at_entry_end(rest, depth - 1, [t | acc])

  defp split_at_entry_end([t | rest], depth, acc), do: split_at_entry_end(rest, depth, [t | acc])

  defp parse_type_decl([{:atom, name}, {:colon, _} | type_tokens]) do
    if type_tokens == [{:system, "$tType"}] do
      {name, :base_type}
    else
      {type_struct, []} = Parser.parse_type(type_tokens)
      {name, type_struct}
    end
  end

  defp build_context(problem) do
    ctx_with_types =
      Enum.reduce(problem.types, Context.new(), fn
        {_name, :base_type}, ctx ->
          ctx

        {name, type_struct}, ctx ->
          Context.put_const(ctx, name, type_struct)
      end)

    Enum.reduce(problem.definitions, ctx_with_types, fn {_name, term}, ctx ->
      case extract_defined_constant(term) do
        {name, type} -> Context.put_const(ctx, name, type)
        nil -> ctx
      end
    end)
  end

  defp extract_defined_constant(equality(lhs, _rhs)) do
    case lhs do
      hol_term(head: declaration(kind: :co, name: name, type: type)) ->
        {name, type}

      _ ->
        nil
    end
  end

  defp merge_problems(main, included) do
    %{
      main
      | types: Map.merge(main.types, included.types),
        axioms: main.axioms ++ included.axioms,
        definitions: main.definitions ++ included.definitions
    }
  end
end
