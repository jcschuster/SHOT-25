defmodule THOU.HOL.Patterns do
  @moduledoc """
  Defines patterns on terms with respect to the definitions introduced in
  `THOU.HOL.Definitions`. Note that this should only be used for pattern
  matching and not for term construction!
  """

  import HOL.Data
  import THOU.HOL.Definitions

  # The use of macros messes up the type checking, so we ignore the warnings.
  @dialyzer :no_contracts

  @doc """
  Pattern to match a negated term.
  """
  @spec negated(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro negated(term) do
    quote do
      hol_term(bvars: [], head: neg_const(), args: [unquote(term)])
    end
  end

  @doc """
  Pattern to match the conjunction of two terms.
  """
  @spec conjunction(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro conjunction(p, q) do
    quote do
      hol_term(bvars: [], head: and_const(), args: [unquote(p), unquote(q)])
    end
  end

  @doc """
  Pattern to match the disjunction of two terms.
  """
  @spec disjunction(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro disjunction(p, q) do
    quote do
      hol_term(bvars: [], head: or_const(), args: [unquote(p), unquote(q)])
    end
  end

  @doc """
  Pattern to match the implication of two terms, where the first term implies
  the second.
  """
  @spec implication(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro implication(p, q) do
    quote do
      hol_term(bvars: [], head: implies_const(), args: [unquote(p), unquote(q)])
    end
  end

  @doc """
  Pattern to match the equivalence of two terms.
  """
  @spec equivalence(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro equivalence(p, q) do
    quote do
      hol_term(bvars: [], head: equivalent_const(), args: [unquote(p), unquote(q)])
    end
  end

  @doc """
  Pattern to match equiality of two terms, ignoring the type.
  """
  @spec equality(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro equality(a, b) do
    quote do
      hol_term(bvars: [], head: equals_const(_), args: [unquote(a), unquote(b)])
    end
  end

  @doc """
  Pattern to match equality of two terms with respect to their type.
  """
  @spec typed_equality(HOL.Data.hol_term(), HOL.Data.hol_term(), HOL.Data.type()) ::
          HOL.Data.hol_term()
  defmacro typed_equality(a, b, t) do
    quote do
      hol_term(bvars: [], head: equals_const(unquote(t)), args: [unquote(a), unquote(b)])
    end
  end

  @doc """
  Pattern to match the existential quantification of a given predicate,
  ignoring the type.
  """
  @spec existential_quantification(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro existential_quantification(pp) do
    quote do
      hol_term(bvars: [], head: sigma_const(_), args: [unquote(pp)])
    end
  end

  @doc """
  Pattern to match the existential quantification of a given predicate with
  respect to its type.
  """
  @spec typed_existential_quantification(HOL.Data.hol_term(), HOL.Data.type()) ::
          HOL.Data.hol_term()
  defmacro typed_existential_quantification(pp, t) do
    quote do
      hol_term(bvars: [], head: sigma_const(unquote(t)), args: [unquote(pp)])
    end
  end

  @doc """
  Pattern to match the universal quantification of a given predicate ignoring
  the type.
  """
  @spec universal_quantification(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  defmacro universal_quantification(pp) do
    quote do
      hol_term(bvars: [], head: pi_const(_), args: [unquote(pp)])
    end
  end

  @doc """
  Pattern to match the universal quantification of a given predicate with
  respect to its type.
  """
  @spec typed_universal_quantification(HOL.Data.hol_term(), HOL.Data.type()) ::
          HOL.Data.hol_term()
  defmacro typed_universal_quantification(pp, t) do
    quote do
      hol_term(bvars: [], head: pi_const(unquote(t)), args: [unquote(pp)])
    end
  end
end
