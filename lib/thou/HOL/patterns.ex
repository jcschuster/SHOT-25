defmodule THOU.HOL.Patterns do
  import HOL.Data
  import THOU.HOL.Definitions

  defmacro any_equals_const, do: Macro.escape(declaration(kind: :co, name: "="))

  defmacro negated(term) do
    quote do
      hol_term(head: neg_const(), args: [unquote(term)])
    end
  end
end
