defmodule THOU.HOL.Patterns do
  import HOL.Data
  import THOU.HOL.Definitions

  defmacro any_equals_const do
    quote do
      declaration(kind: :co, name: "=")
    end
  end

  defmacro negated(term) do
    quote do
      hol_term(bvars: [], head: neg_const(), args: [unquote(term)])
    end
  end
end
