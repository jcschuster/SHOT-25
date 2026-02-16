defmodule THOU.Util do
  @moduledoc """
  Contains utility functions used by the prover. This includes the generation
  of skolem terms, utility to negate and to apply substitutions to terms.
  """

  import HOL.Data
  import HOL.Terms
  import HOL.Substitution
  use BeHOLd.ClassicalHOL.Definitions
  import BeHOLd.ClassicalHOL.Equality

  @typedoc """
  Type for a term or a collection of terms.
  """
  @type term_or_collection ::
          HOL.Data.hol_term()
          | [HOL.Data.hol_term()]
          | MapSet.t(HOL.Data.hol_term())

  @doc """
  Creates a new and unique skolem term which is of type `return_type` and
  dependent on `fvars`.
  """
  @spec mk_new_skolem_term([HOL.Data.declaration()], HOL.Data.type()) :: HOL.Data.hol_term()
  def mk_new_skolem_term(fvars, return_type) do
    skolem_const =
      mk_const(
        "__sk_#{System.unique_integer([:positive, :monotonic])}",
        mk_type(return_type, Enum.map(fvars, &get_type/1))
      )

    # Apply skolem constant to free variables
    Enum.reduce(fvars, mk_term(skolem_const), fn declaration() = fvar, acc ->
      fvar_term = mk_term(fvar)
      mk_appl_term(acc, fvar_term)
    end)
  end

  @doc """
  Generates a term stating that `a` and `b` are Leibniz equal. Note that
  Leibniz equality is stated in terms of equivalence.
  """
  @spec mk_leibniz_equal(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def mk_leibniz_equal(hol_term(type: t) = a, hol_term(type: t) = b) do
    leibniz_equality(t, equivalent_term()) |> mk_appl_term(a) |> mk_appl_term(b)
  end

  @doc """
  Generates a term stating that `a` and `b` are equal in their extensions.
  """
  @spec mk_ext_equal(HOL.Data.hol_term(), HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def mk_ext_equal(hol_term(type: t) = a, hol_term(type: t) = b) do
    extensional_equality(t) |> mk_appl_term(a) |> mk_appl_term(b)
  end

  @doc """
  Negates the given term or every term in the given collection by prefixing it
  with a negation symbol.
  """
  @spec negate(t) :: t when t: term_or_collection()
  def negate(term_or_collection)

  def negate(clause) when is_list(clause) do
    Enum.map(clause, fn t -> negate(t) end)
  end

  def negate(clause) when is_struct(clause, MapSet) do
    MapSet.new(clause, fn t -> negate(t) end)
  end

  def negate(hol_term(bvars: [], type: type_o()) = term), do: mk_appl_term(neg_term(), term)

  @doc """
  Negates the given term or every term in the given collection by removing a
  negation symbol at head position if present and adding it otherwise.
  """
  @spec lit_negate(t) :: t when t: term_or_collection()

  def lit_negate(clause) when is_map(clause) or is_list(clause) do
    Enum.map(clause, fn t -> lit_negate(t) end)
  end

  def lit_negate(hol_term(bvars: [], head: neg_const(), args: [term])), do: term

  def lit_negate(hol_term(bvars: [], type: type_o()) = term), do: mk_appl_term(neg_term(), term)

  @doc """
  Applies a list of substitutions to the given term, pair of terms, collection
  of terms or substitution.
  """
  @spec apply_subst([HOL.Data.substitution()], t) :: t
        when t: term_or_collection() | HOL.Data.substitution()
  def apply_subst(substitutions, term_or_collection)

  def apply_subst([], x), do: x

  def apply_subst(substitutions, formulas) when is_list(formulas) do
    Enum.map(formulas, &apply_subst(substitutions, &1))
  end

  def apply_subst(substitutions, literals) when is_map(literals) do
    MapSet.new(literals, &apply_subst(substitutions, &1))
  end

  def apply_subst(substitutions, substitution(fvar: fvar, term: term)) do
    mk_substitution(fvar, apply_subst(substitutions, term))
  end

  def apply_subst(substitutions, term) do
    subst(substitutions, term)
  end
end
