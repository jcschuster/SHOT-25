defmodule THOU.Util do
  import HOL.Data
  import HOL.Terms
  import HOL.Substitution
  import THOU.HOL.Definitions
  import THOU.HOL.Patterns

  def mk_new_unknown_type() do
    mk_type(:"__unknown_#{System.unique_integer([:positive, :monotonic])}")
  end

  def unknown_type?(t) when is_atom(t) do
    String.starts_with?(Atom.to_string(t), "__unknown_")
  end

  def unknown_type?(type(goal: g)) do
    is_atom(g) and unknown_type?(g)
  end

  def unknown_type?(_), do: false

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

  def constant?(hol_term() = term) do
    case term do
      negated(body) ->
        constant?(body)

      hol_term(bvars: bvars, head: declaration(kind: :co), args: args) ->
        Enum.all?(args, &(get_head(&1) in bvars))

      _ ->
        false
    end
  end

  def variable?(hol_term() = term) do
    case term do
      negated(body) ->
        variable?(body)

      hol_term(bvars: bvars, head: declaration(kind: :fv), args: args) ->
        Enum.all?(args, &(get_head(&1) in bvars))

      _ ->
        false
    end
  end

  def atomic_term?(hol_term(bvars: [], args: args)), do: args == []

  def atomic_term?(hol_term(bvars: bvars, args: args)) do
    Enum.all?(args, fn arg -> atomic_term?(arg) && Enum.any?(bvars, &(&1 == get_head(arg))) end)
  end

  def is_appl_term?(hol_term(bvars: bvars, args: args)) do
    # All arguments are atomic terms,
    # all bound variables appear exactly once as term in argument list
    # and there is at least one argument that is not a bound variable
    Enum.all?(args, &atomic_term?/1) &&
      Enum.all?(bvars, fn bvar -> Enum.any?(args, &match?(hol_term(head: ^bvar), &1)) end) &&
      Enum.any?(args, fn arg -> !Enum.any?(bvars, &match?(hol_term(head: &1), arg)) end)
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

  def pp_assignment(clause) when is_map(clause) do
    pretty_assignments =
      Enum.map(clause, fn t ->
        case t do
          negated(inner) -> "#{PrettyPrint.pp_term(inner)} ← false"
          _ -> "#{PrettyPrint.pp_term(t)} ← true"
        end
      end)

    "[" <> Enum.join(pretty_assignments, ", ") <> "]"
  end

  def pp_constraints(constraints) when is_list(constraints) do
    pretty_constraints =
      Enum.map(constraints, fn {t1, t2} ->
        "#{PrettyPrint.pp_term(t1)} = #{PrettyPrint.pp_term(t2)}"
      end)

    "[" <> Enum.join(pretty_constraints, ", ") <> "]"
  end
end
