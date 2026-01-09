defmodule THOU.Parser.TPTP do
  @moduledoc """
  Contains utility to parse files from the TPTP problem library
  (https://tptp.org/TPTP/) as well as custom files in TPTP's TH0 syntax. Also
  contains utility to generate TH0 string representation of terms, types and
  declarations. This module only works with files in TH0 syntax. For reference,
  the TH0 language is defined in https://doi.org/10.1007/s10817-017-9407-7.

  Note that there is no functionality of generating a full TPTP file from a
  given term which would include definitions and user type declarations.
  """

  import HOL.Data
  import THOU.HOL.{Definitions, Patterns}
  alias THOU.Parser.TPTPTokenizer, as: Tokenizer
  alias THOU.Parser.Parser
  alias THOU.Parser.Parser.Context

  defmodule Problem do
    @moduledoc """
    A data structure to describe a (TPTP) proof problem.

    It contains meta-information about the problem (path to proof file,
    included files) as well as the problem definition which consist of:

    - A map of types which maps symbols (user types or constants) to their type

    - The definitions given by the user

    - The axioms defined by the user

    - The conjecture to be proven based on the axioms and definitions

    Note that definitions are not unfolded in the proof problem but kept as
    constants.
    """
    require HOL.Data

    defstruct path: "", includes: [], types: %{}, definitions: %{}, axioms: [], conjecture: nil

    @typedoc """
    A `Problem` is a collection holding the relevant information and
    meta-information of a problem stored in separate fields.

    The `:path` to a problem file is given as a string. This also includes the
    paths to the included files in `:includes`.

    The types are given as a map mapping symbol names (or type names) to their
    defined types (can be `:base_type` for user-defined base types).

    The definitions are given as a map from the symbol's name to the equation
    describing it. Note that the equation must first be deconstructed into the
    defined constant on the left hand side and it's definition on the right
    hand side.

    The axioms are stored as a list of pairs containing the axiom's name as
    string and term as `HOL.Data.hol_term()`.

    The conjecture is tuple containing the conjecture's name as string and the
    conjecture itself as `HOL.Data.hol_term()`. The field's value is `nil` if
    no conjecture could be found.
    """
    @type t() :: %__MODULE__{
            path: String.t(),
            includes: [String.t()],
            types: %{String.t() => :base_type | HOL.Data.type()},
            definitions: %{String.t() => HOL.Data.hol_term()},
            axioms: [{String.t(), HOL.Data.hol_term()}],
            conjecture: {String.t(), HOL.Data.hol_term()} | nil
          }
  end

  #############################################################################
  # TERM TO TPTP REPRESENTATION
  #############################################################################

  @doc group: "To TPTP Representation"
  @doc """
  Converts a type given as `HOL.Data.type()` or atom to TPTP's TH0 string
  representation. Does not introduce declarations as required for handling user
  types when creating a TPTP file.
  """
  @spec type_to_tptp(HOL.Data.type() | atom()) :: String.t()
  def type_to_tptp(type_or_atom)

  def type_to_tptp(:o), do: "$o"
  def type_to_tptp(:i), do: "$i"
  def type_to_tptp(a) when is_atom(a), do: Atom.to_string(a)
  def type_to_tptp(type_o()), do: "$o"
  def type_to_tptp(type_i()), do: "$i"
  def type_to_tptp(type(goal: g, args: [])) when is_atom(g), do: Atom.to_string(g)

  def type_to_tptp(type(goal: g, args: args)) do
    args_str = Enum.map_join(args, " > ", &type_to_tptp_inner/1)
    "#{args_str} > #{type_to_tptp(g)}"
  end

  defp type_to_tptp_inner(type(args: []) = type), do: type_to_tptp(type)

  defp type_to_tptp_inner(type(goal: g, args: args)) do
    args_str = Enum.map_join(args, " > ", &type_to_tptp_inner/1)
    "(#{args_str} > #{type_to_tptp(g)})"
  end

  @doc group: "To TPTP Representation"
  @doc """
  Converts a given term or variable/constant declaration to TPTP's TH0 syntax.
  Tries to reconstruct the syntactic sugar (e.g., the XOR operator "<~>")
  present in the TH0 language and eta-reduces the terms.

  As bound variables are named using deBrujn indices, they are prefixed with
  "BV_". Skolem constants, which are internally named by prefixing them with
  "__sk_" followed by an identifying number, are prefixed by "skolem_",
  removing the double underscore before the name. To ensure TH0's variable
  encoding scheme (variables start with uppercase letters), variables are
  prefixed with "VAR_".
  """
  @spec term_to_tptp(HOL.Data.hol_term() | HOL.Data.declaration()) :: String.t()
  def term_to_tptp(term_or_declaration)

  def term_to_tptp(declaration() = decl), do: do_term_to_tptp(decl)

  def term_to_tptp(term) do
    eta_reduce(term) |> do_term_to_tptp()
  end

  defp do_term_to_tptp(true_const()), do: "$true"
  defp do_term_to_tptp(false_const()), do: "$false"
  defp do_term_to_tptp(neg_const()), do: "~"
  defp do_term_to_tptp(or_const()), do: "|"
  defp do_term_to_tptp(and_const()), do: "&"
  defp do_term_to_tptp(implies_const()), do: "=>"
  defp do_term_to_tptp(equivalent_const()), do: "<=>"
  defp do_term_to_tptp(equals_const(_)), do: "="
  defp do_term_to_tptp(pi_const(_)), do: "!"
  defp do_term_to_tptp(sigma_const(_)), do: "?"
  defp do_term_to_tptp(declaration(kind: :bv, name: name)), do: "BV__#{name}"

  defp do_term_to_tptp(declaration(kind: :co, name: "__" <> name)) do
    "skolem_" <> String.downcase(name)
  end

  defp do_term_to_tptp(declaration(kind: :co, name: name)), do: String.downcase(name)

  defp do_term_to_tptp(declaration(kind: :fv, name: name)) when is_binary(name) do
    String.capitalize(name)
  end

  defp do_term_to_tptp(declaration(kind: :fv, name: name)) do
    "VAR_" <> String.replace(inspect(name), ~r/[^0-9]/, "")
  end

  defp do_term_to_tptp(nor_term()), do: "~|"
  defp do_term_to_tptp(nand_term()), do: "~&"
  defp do_term_to_tptp(xor_term()), do: "<~>"
  defp do_term_to_tptp(not_equals_term(_)), do: "!="

  defp do_term_to_tptp(hol_term(bvars: [], head: or_const(), args: args)) do
    case args do
      [] -> "|"
      [a] -> "( | @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} | #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(hol_term(bvars: [], head: and_const(), args: args)) do
    case args do
      [] -> "&"
      [a] -> "( & @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} & #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(hol_term(bvars: [], head: implies_const(), args: args)) do
    case args do
      [] -> "=>"
      [a] -> "( => @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} => #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(hol_term(bvars: [], head: equivalent_const(), args: args)) do
    case args do
      [] -> "<=>"
      [a] -> "( <=> @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} <=> #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(hol_term(bvars: [], head: equals_const(_), args: args)) do
    case args do
      [] -> "="
      [a] -> "( = @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} = #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(negated(hol_term(bvars: [], head: or_const(), args: args))) do
    case args do
      [] -> "~|"
      [a] -> "( ~| @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} ~| #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(negated(hol_term(bvars: [], head: and_const(), args: args))) do
    case args do
      [] -> "~&"
      [a] -> "( ~& @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} ~& #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(negated(hol_term(bvars: [], head: equivalent_const(), args: args))) do
    case args do
      [] -> "<~>"
      [a] -> "( <~> @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} <~> #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(negated(hol_term(bvars: [], head: equals_const(_), args: args))) do
    case args do
      [] -> "!="
      [a] -> "( != @ #{term_to_tptp(a)} )"
      [a, b] -> "( #{term_to_tptp(a)} != #{term_to_tptp(b)} )"
    end
  end

  defp do_term_to_tptp(hol_term(bvars: [], head: neg_const(), args: [inner])) do
    "~ #{term_to_tptp(inner)}"
  end

  defp do_term_to_tptp(
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

  defp do_term_to_tptp(
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

  defp do_term_to_tptp(hol_term(bvars: [], head: head, args: args, type: type) = term) do
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
            _ -> []
          end

        reduced_fvars =
          (head_fvars ++ Enum.reduce(rest, [], &(get_fvars(&1) ++ &2))) |> Enum.uniq()

        "( #{term_to_tptp(hol_term(term, head: head, args: rest, type: mk_type(type, [t]), fvars: reduced_fvars))} @ " <>
          "#{term_to_tptp(last_arg)} )"
    end
  end

  defp do_term_to_tptp(hol_term(bvars: bvars, max_num: max_num) = term) do
    "^ [#{Enum.map_join(bvars, ", ", &"#{term_to_tptp(&1)} : #{type_to_tptp(get_type(&1))}")}]: " <>
      "( #{term_to_tptp(hol_term(term, bvars: [], max_num: max_num - length(bvars)))} )"
  end

  @spec collect_quantified_vars(String.t(), HOL.Data.hol_term(), [String.t()]) ::
          {[String.t()], HOL.Data.hol_term()}
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

  @spec eta_reduce(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defp eta_reduce(term)

  defp eta_reduce(hol_term(bvars: bvars, args: args) = term)
       when bvars != [] and args != [] do
    declaration(type: t) = last_bvar = List.last(bvars)
    last_arg = List.last(args)

    if match?(hol_term(head: ^last_bvar, type: ^t), last_arg) do
      remaining_args = Enum.drop(args, -1)
      hol_term(head: head) = term

      if not occurs_in?(last_bvar, head) and
           not Enum.any?(remaining_args, &occurs_in?(last_bvar, &1)) do
        eta_reduce(hol_term(term, bvars: Enum.drop(bvars, -1), args: remaining_args))
      else
        term
      end
    else
      term
    end
  end

  defp eta_reduce(other), do: other

  @spec occurs_in?(HOL.Data.declaration(), HOL.Data.hol_term()) :: boolean()
  defp occurs_in?(var, term)

  defp occurs_in?(var, declaration() = decl), do: var == decl

  defp occurs_in?(var, hol_term(head: h, args: args)) do
    occurs_in?(var, h) || Enum.any?(args, &occurs_in?(var, &1))
  end

  #############################################################################
  # TPTP REPRESENTATION TO TERM
  #############################################################################

  @doc group: "From TPTP Representation"
  @doc """
  Parses a TPTP file in TH0 syntax at the proveded path into a `Problem`
  structure. Returns `{:error, reason}` if a problem occured when reading the
  file.

  This function serves two purposes: parsing a file from the TPTP problem
  library (https://tptp.org/TPTP/) or a custom problem file given by the user.

  The default is to parse a file from the TPTP problem library. In that case,
  the flag `is_tptp` should be set to `true`. This also requires an environment
  variable `TPTP_ROOT` which points to the unpacked root folder of the TPTP
  problem library. Setting this environment variable may require a system
  restart before Elixir recognizes it.

  When parsing a custom problem file, the flag `is_tptp` should be set to
  false. `problem` should contain the absolute path to the problem file. Note
  that imports of custom files are not supported. Only axioms from the TPTP
  problem library can be imported (this also requires the `TPTP_ROOT`
  environment variable to be set).
  """
  @spec parse_file(String.t(), boolean()) :: {:ok, Problem.t()} | {:error, String.t()}
  def parse_file(problem, is_tptp \\ true) do
    path =
      if is_tptp and System.get_env("TPTP_ROOT") == nil do
        raise "TPTP Parser Error: TPTP_ROOT environment variable is not set"
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

  @doc group: "From TPTP Representation"
  @doc """
  Parses a string representing a problem file in TPTP's TH0 syntax into a
  `Problem` structure.

  The parsing of `content` only supports including files from the TPTP problem
  library. If such includes are present, make sure that the `TPTP_ROOT`
  environment variable is set.

  The `path` does not need to be specified when calling this method. It is
  purely for keeping track of the file name from a call to `parse_file/2`.
  """
  @spec parse_string(String.t(), String.t()) :: {:ok, Problem.t()} | {:error, String.t()}
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
    if file_path == problem.path do
      raise "TPTP Parser Error: Cyclic import of #{file_path}"
    end

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
                %{problem | definitions: Map.put(problem.definitions, name, term)}

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
        definitions: Map.merge(main.definitions, included.definitions),
        includes: main.includes ++ [included.path | included.includes]
    }
  end
end
