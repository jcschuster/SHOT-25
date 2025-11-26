defmodule THOU.Util do
  import HOL.Data
  import HOL.Terms
  import HOL.Substitution
  import THOU.HOL.Definitions

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

  def mk_new_free_var(type() = type), do: mk_uniqe_var(type)

  def constant?(hol_term() = term) do
    case term do
      hol_term(bvars: [], head: neg_const(), args: [body]) ->
        constant?(body)

      hol_term(bvars: [], head: declaration(kind: :co)) ->
        true

      _ ->
        false
    end
  end

  def variable?(hol_term() = term) do
    case term do
      hol_term(bvars: [], head: neg_const(), args: [body]) ->
        variable?(body)

      hol_term(bvars: [], head: declaration(kind: :fv)) ->
        true

      _ ->
        false
    end
  end

  def syn_negate(clause) when is_map(clause) or is_list(clause) do
    Enum.map(clause, fn t -> syn_negate(t) end)
  end

  def syn_negate(hol_term(bvars: [], type: type_o()) = term), do: mk_appl_term(neg_term(), term)

  def sem_negate(clause) when is_map(clause) or is_list(clause) do
    Enum.map(clause, fn t -> sem_negate(t) end)
  end

  def sem_negate(hol_term(bvars: [], head: neg_const(), args: [term])), do: term

  def sem_negate(hol_term(bvars: [], type: type_o()) = term), do: mk_appl_term(neg_term(), term)

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

  def flex_flex?({
        hol_term(bvars: [], head: declaration(kind: :fv), type: type),
        hol_term(bvars: [], head: declaration(kind: :fv), type: type)
      }) do
    true
  end

  def flex_flex?({hol_term(type: type), hol_term(type: type)}) do
    false
  end

  def pp_constraints(constraints) when is_list(constraints) do
    Enum.reduce(constraints, "[", fn {t1, t2}, str ->
      str <>
        case String.length(str) do
          1 -> ""
          _ -> ", "
        end <>
        PrettyPrint.pp_term(t1) <>
        " = " <>
        PrettyPrint.pp_term(t2)
    end) <> "]"
  end
end
