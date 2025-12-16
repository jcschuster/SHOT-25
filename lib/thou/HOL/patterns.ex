defmodule THOU.HOL.Patterns do
  import HOL.Data
  import THOU.HOL.Definitions

  defmacro negated(term) do
    quote do
      hol_term(bvars: [], head: neg_const(), args: [unquote(term)])
    end
  end

  defmacro conjunction(p, q) do
    quote do
      hol_term(bvars: [], head: and_const(), args: [unquote(p), unquote(q)])
    end
  end

  defmacro disjunction(p, q) do
    quote do
      hol_term(bvars: [], head: or_const(), args: [unquote(p), unquote(q)])
    end
  end

  defmacro implication(p, q) do
    quote do
      hol_term(bvars: [], head: implies_const(), args: [unquote(p), unquote(q)])
    end
  end

  defmacro equivalence(p, q) do
    quote do
      hol_term(bvars: [], head: equivalent_const(), args: [unquote(p), unquote(q)])
    end
  end

  defmacro equality(a, b) do
    quote do
      hol_term(bvars: [], head: equals_const(_), args: [unquote(a), unquote(b)])
    end
  end

  defmacro typed_equality(a, b, t) do
    quote do
      hol_term(bvars: [], head: equals_const(unquote(t)), args: [unquote(a), unquote(b)])
    end
  end

  defmacro existential_quantification(pp) do
    quote do
      hol_term(bvars: [], head: sigma_const(_), args: [unquote(pp)])
    end
  end

  defmacro typed_existential_quantification(pp, t) do
    quote do
      hol_term(bvars: [], head: sigma_const(unquote(t)), args: [unquote(pp)])
    end
  end

  defmacro universal_quantification(pp) do
    quote do
      hol_term(bvars: [], head: pi_const(_), args: [unquote(pp)])
    end
  end

  defmacro typed_universal_quantification(pp, t) do
    quote do
      hol_term(bvars: [], head: pi_const(unquote(t)), args: [unquote(pp)])
    end
  end
end
