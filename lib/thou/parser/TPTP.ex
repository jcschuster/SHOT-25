defmodule THOU.Parser.TPTP do
  alias THOU.Parser.{Tokenizer, Parser}
  alias THOU.Parser.Parser.Context

  defmodule Problem do
    defstruct path: "", includes: [], types: %{}, definitions: [], axioms: [], conjecture: nil
  end

  def parse_file(problem) do
    path =
      if System.get_env("TPTP_ROOT") == nil do
        raise "TPTP_ROOT environment variable is not set"
      else
        Path.join(System.get_env("TPTP_ROOT"), problem)
      end

    case File.read(path) do
      {:ok, content} -> parse_string(content, path)
      {:error, reason} -> {:error, "Could not read file #{path}: #{reason}"}
    end
  end

  def parse_string(content, path) do
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

      :definition ->
        ctx = build_context(problem)
        term = Parser.parse_tokens(formula_tokens, ctx)
        new_defs = problem.definitions ++ [{name, term}]
        process_tokens(remaining_tokens, %{problem | definitions: new_defs})

      :axiom ->
        ctx = build_context(problem)
        term = Parser.parse_tokens(formula_tokens, ctx)
        new_axioms = problem.axioms ++ [{name, term}]
        process_tokens(remaining_tokens, %{problem | axioms: new_axioms})

      :conjecture ->
        ctx = build_context(problem)
        term = Parser.parse_tokens(formula_tokens, ctx)
        process_tokens(remaining_tokens, %{problem | conjecture: {name, term}})

      _ ->
        process_tokens(remaining_tokens, problem)
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
    Enum.reduce(problem.types, Context.new(), fn
      {_name, :base_type}, ctx ->
        ctx

      {name, type_struct}, ctx ->
        Context.put_const(ctx, name, type_struct)
    end)
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
