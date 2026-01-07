defmodule THOU.Util do
  import HOL.Data
  import HOL.Terms
  import HOL.Substitution
  import THOU.HOL.Definitions
  import THOU.HOL.Patterns

  @spec mk_new_skolem_term([HOL.Data.declaration()], HOL.Data.type()) ::
          HOL.Data.hol_term()
  def mk_new_skolem_term(fvars, type() = return_type) do
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

  @spec constant?(HOL.Data.hol_term()) :: boolean()
  def constant?(term) do
    case term do
      negated(body) ->
        constant?(body)

      hol_term(bvars: bvars, head: declaration(kind: :co), args: args) ->
        Enum.all?(args, &(get_head(&1) in bvars))

      _ ->
        false
    end
  end

  @spec variable?(HOL.Data.hol_term()) :: boolean()
  def variable?(term) do
    case term do
      negated(body) ->
        variable?(body)

      hol_term(bvars: bvars, head: declaration(kind: :fv), args: args) ->
        Enum.all?(args, &(get_head(&1) in bvars))

      _ ->
        false
    end
  end

  @spec unknown_type?(HOL.Data.type() | atom()) :: boolean()
  def unknown_type?(t) when is_atom(t) do
    String.starts_with?(Atom.to_string(t), "__unknown_")
  end

  def unknown_type?(type(goal: g)) do
    is_atom(g) and unknown_type?(g)
  end

  def unknown_type?(_), do: false

  @spec syn_negate([HOL.Data.hol_term()] | MapSet.t(HOL.Data.hol_term())) ::
          [HOL.Data.hol_term()]
  @spec syn_negate(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def syn_negate(term_or_collection)

  def syn_negate(clause) when is_map(clause) or is_list(clause) do
    Enum.map(clause, fn t -> syn_negate(t) end)
  end

  def syn_negate(hol_term(bvars: [], type: type_o()) = term), do: mk_appl_term(neg_term(), term)

  @spec sem_negate([HOL.Data.hol_term()] | MapSet.t(HOL.Data.hol_term())) ::
          [HOL.Data.hol_term()]
  @spec sem_negate(HOL.Data.hol_term()) :: HOL.Data.hol_term()
  def sem_negate(term_or_collection)

  def sem_negate(clause) when is_map(clause) or is_list(clause) do
    Enum.map(clause, fn t -> sem_negate(t) end)
  end

  def sem_negate(hol_term(bvars: [], head: neg_const(), args: [term])), do: term

  def sem_negate(hol_term(bvars: [], type: type_o()) = term), do: mk_appl_term(neg_term(), term)

  @spec apply_subst([HOL.Data.substitution()], HOL.Data.hol_term()) :: HOL.Data.hol_term()
  @spec apply_subst([HOL.Data.substitution()], [HOL.Data.hol_term()]) :: [HOL.Data.hol_term()]
  @spec apply_subst([HOL.Data.substitution()], MapSet.t(HOL.Data.hol_term())) ::
          MapSet.t(HOL.Data.hol_term())
  def apply_subst(substitutions, term_or_collection)

  def apply_subst([], x), do: x

  def apply_subst(substitutions, formulas) when is_list(formulas) do
    Enum.map(formulas, &apply_subst(substitutions, &1))
  end

  def apply_subst(substitutions, literals) when is_map(literals) do
    MapSet.new(literals, &apply_subst(substitutions, &1))
  end

  def apply_subst(substitutions, hol_term() = term) do
    subst(substitutions, term)
  end

  def apply_subst(substitutions, {hol_term() = t1, hol_term() = t2}) do
    {apply_subst(substitutions, t1), apply_subst(substitutions, t2)}
  end

  def apply_subst(substitutions, substitution(fvar: fvar, term: term)) do
    mk_substitution(fvar, apply_subst(substitutions, term))
  end
end
