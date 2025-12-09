defmodule THOU.Parser.FileParser do
  alias THOU.Parser.{Tokenizer, Parser}
  alias THOU.Parser.Parser.Context

  defmodule Problem do
    defstruct path: "", includes: [], types: %{}, definitions: [], axioms: [], conjecture: nil
  end

  def parse_file(path) do
    case File.read(path) do
      {:ok, content} -> parse_string(content, path)
      {:error, reason} -> {:error, "Could not read file #{path}: #{reason}"}
    end
  end

  def parse_string(content, path \\ "memory") do
    {:ok, tokens, _, _, _, _} = Tokenizer.tokenize(content)

    # Initial problem structure
    problem = %Problem{path: path}

    # Process tokens recursively
    process_tokens(tokens, problem)
  end

  defp process_tokens([], problem), do: {:ok, problem}

  # --- Handle Includes ---
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
    # You might want to recursively parse the included file here or just store the path
    # For a full system, you'd merge the included problem's types/axioms into the current one.

    # Naive recursive load (be careful of cycles and paths!)
    base_dir = Path.dirname(problem.path)
    # Simplified path resolution
    full_path = Path.join(base_dir, file_path)

    case parse_file(full_path) do
      {:ok, included_problem} ->
        merged_problem = merge_problems(problem, included_problem)
        process_tokens(rest, merged_problem)

      error ->
        error
    end
  end

  # --- Handle THF Entries ---
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
    # Extract the formula tokens up to the closing parenthesis and dot
    {formula_tokens, remaining_tokens} = extract_formula(rest)

    case role do
      :type ->
        # Parse type declaration: name : type
        {entry_name, type_struct} = parse_type_decl(formula_tokens)
        new_types = Map.put(problem.types, entry_name, type_struct)
        process_tokens(remaining_tokens, %{problem | types: new_types})

      :definition ->
        # Parse definition: name = term
        # For definitions, we parse it as a standard formula where the top level is equality
        # You might need to supply the current known types to the parser context

        ctx = build_context(problem)
        {term, _rest, _} = Parser.parse_formula(formula_tokens, ctx)

        # Note: Your Parser.parse returns a term directly or {term, rest, ctx} depending on function
        # You likely want to use Parser.parse/2 entry point logic here but adapted for tokens

        new_defs = problem.definitions ++ [{name, term}]
        process_tokens(remaining_tokens, %{problem | definitions: new_defs})

      :axiom ->
        ctx = build_context(problem)
        # You might need to adapt your Parser.parse to accept tokens directly
        term = parse_term_from_tokens(formula_tokens, ctx)
        new_axioms = problem.axioms ++ [{name, term}]
        process_tokens(remaining_tokens, %{problem | axioms: new_axioms})

      :conjecture ->
        ctx = build_context(problem)
        term = parse_term_from_tokens(formula_tokens, ctx)
        process_tokens(remaining_tokens, %{problem | conjecture: {name, term}})

      _ ->
        # Handle other roles or ignore
        process_tokens(remaining_tokens, problem)
    end
  end

  # Helper to extract tokens until the matching ')' and '.' for the thf entry
  defp extract_formula(tokens) do
    # This needs a simple counter to handle nested parentheses
    split_at_entry_end(tokens, 0, [])
  end

  defp split_at_entry_end([{:rparen, _}, {:dot, _} | rest], 0, acc), do: {Enum.reverse(acc), rest}

  defp split_at_entry_end([{:lparen, _} = t | rest], depth, acc),
    do: split_at_entry_end(rest, depth + 1, [t | acc])

  defp split_at_entry_end([{:rparen, _} = t | rest], depth, acc),
    do: split_at_entry_end(rest, depth - 1, [t | acc])

  defp split_at_entry_end([t | rest], depth, acc), do: split_at_entry_end(rest, depth, [t | acc])

  # --- Type Parsing Logic ---
  # Handles: constant : type_signature
  defp parse_type_decl([{:atom, name}, {:colon, _} | type_tokens]) do
    # You can reuse Parser.parse_type logic here
    # Be aware: $tType is a special case

    if type_tokens == [{:system, "$tType"}] do
      # It's a new base type declaration
      {name, :base_type}
    else
      {type_struct, []} = Parser.parse_type(type_tokens)
      {name, type_struct}
    end
  end

  # --- Helpers ---

  defp build_context(problem) do
    # Convert problem.types into a Parser.Context
    Enum.reduce(problem.types, Context.new(), fn
      {_name, :base_type}, ctx ->
        # Depending on how your context handles base types vs constants
        ctx

      {name, type_struct}, ctx ->
        Context.put_const(ctx, name, type_struct)
    end)
  end

  defp parse_term_from_tokens(tokens, ctx) do
    # We need to bridge the gap because Parser.parse/2 expects a string
    # Create a temporary function in Parser to accept tokens directly
    # or reconstruct string (inefficient)

    # Assuming you modify Parser to expose parse_tokens/2:
    THOU.Parser.Parser.parse_tokens(tokens, ctx)
  end

  defp merge_problems(main, included) do
    # Merge types, definitions, axioms.
    # Usually, the included conjecture is ignored or treated as axiom if role is axiom
    %{
      main
      | types: Map.merge(main.types, included.types),
        axioms: main.axioms ++ included.axioms,
        definitions: main.definitions ++ included.definitions
    }
  end
end
