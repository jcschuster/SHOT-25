defmodule THOU.Parser.TPTPTokenizer do
  import NimbleParsec

  whitespace = ascii_string([?\s, ?\t, ?\n, ?\r], min: 1) |> ignore()

  comment = string("%") |> concat(ascii_string([not: ?\n], min: 0)) |> ignore()

  def categorize_atom(name) do
    case name do
      "include" -> {:keyword, :include}
      "thf" -> {:keyword, :thf}
      "type" -> {:role, :type}
      "axiom" -> {:role, :axiom}
      "definition" -> {:role, :definition}
      "conjecture" -> {:role, :conjecture}
      "lemma" -> {:role, :lemma}
      "hypothesis" -> {:role, :hypothesis}
      _ -> {:atom, name}
    end
  end

  system_symbol =
    string("$")
    |> ascii_string([?a..?z, ?A..?Z, ?0..?9, ?_], min: 1)
    |> reduce({Enum, :join, []})
    |> unwrap_and_tag(:system)

  variable =
    ascii_string([?A..?Z], 1)
    |> optional(ascii_string([?a..?z, ?A..?Z, ?0..?9, ?_], min: 1))
    |> reduce({Enum, :join, []})
    |> unwrap_and_tag(:var)

  atom_ident =
    ascii_string([?a..?z], 1)
    |> optional(ascii_string([?a..?z, ?A..?Z, ?0..?9, ?_], min: 1))
    |> reduce({Enum, :join, []})
    |> map({__MODULE__, :categorize_atom, []})

  distinct_object =
    ignore(string("'"))
    |> concat(ascii_string([not: ?'], min: 1))
    |> ignore(string("'"))
    |> unwrap_and_tag(:distinct)

  symbols =
    choice([
      # Connectives
      string("<=>") |> replace({:equiv, "<=>"}),
      string("=>") |> replace({:implies, "=>"}),
      string("<=") |> replace({:implied_by, "<="}),
      string("<~>") |> replace({:xor, "<~>"}),
      string("~|") |> replace({:nor, "~|"}),
      string("~&") |> replace({:nand, "~&"}),

      # Quantifiers and Operators
      string("!!") |> replace({:pi, "!!"}),
      string("!=") |> replace({:neq, "!="}),
      string("!") |> replace({:forall, "!"}),
      string("??") |> replace({:sigma, "??"}),
      string("?") |> replace({:exists, "?"}),
      string("^") |> replace({:lambda, "^"}),
      string("@") |> replace({:app, "@"}),
      string("~") |> replace({:not, "~"}),
      string("|") |> replace({:or, "|"}),
      string("&") |> replace({:and, "&"}),
      string("=") |> replace({:eq, "="}),

      # Punctuation
      string("(") |> replace({:lparen, "("}),
      string(")") |> replace({:rparen, ")"}),
      string("[") |> replace({:lbracket, "["}),
      string("]") |> replace({:rbracket, "]"}),
      string(":") |> replace({:colon, ":"}),
      string(",") |> replace({:comma, ","}),
      string(".") |> replace({:dot, "."}),

      # Types
      string(">") |> replace({:arrow, ">"})
    ])

  defparsec(
    :tokenize,
    repeat(
      choice([
        whitespace,
        comment,
        symbols,
        system_symbol,
        variable,
        atom_ident,
        distinct_object
      ])
    )
  )
end
