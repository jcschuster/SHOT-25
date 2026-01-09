defmodule THOU.Preprocessing.SExprTokenizer do
  @moduledoc """
  Defines a `tokenize/1` fucntion for tokenization of an s-expression for
  deserialization using `NimbleParsec` to annotate tokens for easy matching.
  For information about the returned structure, see
  https://hexdocs.pm/nimble_parsec/NimbleParsec.html.
  """
  import NimbleParsec

  whitespace = ascii_string([?\s, ?\t, ?\n, ?\r], min: 1) |> ignore()

  punctuation =
    choice([
      string("(") |> replace({:lparen, "("}),
      string(")") |> replace({:rparen, ")"}),
      string("[") |> replace({:lbracket, "["}),
      string("]") |> replace({:rbracket, "]"}),
      string("∷") |> replace({:dcolon, "∷"}),
      string("⇾") |> replace({:arrow, "⇾"})
    ])

  abstraction = string("^") |> replace({:abs, "^"})

  application = string("@") |> replace({:app, "@"})

  variable =
    string("$VAR~")
    |> utf8_string(
      [
        not: ?\s,
        not: ?\t,
        not: ?\n,
        not: ?\r,
        not: ?(,
        not: ?),
        not: ?[,
        not: ?],
        not: ?⇾,
        not: ?∷,
        not: ?^,
        not: ?@
      ],
      min: 1
    )
    |> reduce({Enum, :join, []})
    |> unwrap_and_tag(:var)

  constant =
    utf8_string(
      [
        not: ?\s,
        not: ?\t,
        not: ?\n,
        not: ?\r,
        not: ?(,
        not: ?),
        not: ?[,
        not: ?],
        not: ?⇾,
        not: ?∷,
        not: ?^,
        not: ?@
      ],
      min: 1
    )
    |> unwrap_and_tag(:const)

  defparsec(
    :tokenize,
    repeat(
      choice([
        whitespace,
        punctuation,
        abstraction,
        application,
        variable,
        constant
      ])
    )
  )
end
