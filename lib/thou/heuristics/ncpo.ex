defmodule THOU.Heuristics.NCPO do
  @moduledoc """
  Implements NCPO-LNF as introduced in
  https://www.imn.htwk-leipzig.de/WST2025/proceedings/WST2025_paper_6.pdf,
  which is an adaption of NCPO (https://arxiv.org/abs/2505.20121) for
  beta-eta-long normal form.

  NCPO is a termination order for non-versatile terms, i.e. terms, that are
  stable under substitution (e.g., applied function symbols but not applied
  free variables). To get around that condition, free variables can be
  universally quantified before given to the order.
  """

  import HOL.Data
  import HOL.Terms
  import THOU.Heuristics.{TypePositions, NCPOParameters}
  import THOU.HOL.Definitions

  # The use of MapSet generates weird opaqueness warnings which we can ignore
  @dialyzer {
    :no_opaque,
    ncpo: 5, ncpo_weak: 5, bawo: 4, structurally_smaller?: 3, lex_gt_helper: 7
  }

  #############################################################################
  # ENTRY POINT
  #############################################################################

  @doc """
  Checks if every term from the first argument is dominated by some term from
  the second argument. Uses the `greater?/2` function to check that condition.
  """
  @spec smaller_multiset?([HOL.Data.hol_term()], [HOL.Data.hol_term()]) :: boolean()
  def smaller_multiset?(terms_s, terms_t) do
    diff_s = terms_s -- terms_t
    diff_t = terms_t -- terms_s

    if Enum.empty?(diff_t) do
      false
    else
      Enum.all?(diff_s, fn s ->
        Enum.any?(diff_t, &greater?(&1, s))
      end)
    end
  end

  @doc """
  Checks if the first term is dominated by the second term in terms of `ncpo/5`
  with initial parameters. Free variables are universally quantified before
  given to the order to satisfy the non-versatility condition.
  """
  @spec greater?(HOL.Data.hol_term(), HOL.Data.hol_term()) :: boolean()
  def greater?(s, t) do
    s_nv = quantify_fvars(s)
    t_nv = quantify_fvars(t)

    ncpo(s_nv, t_nv, true, false, MapSet.new())
  end

  @doc """
  Weak version of `greater?/2`, where equal terms are permitted. Equality here
  is given by the term structure modulo α-renaming which is implicitly handled
  by the use of deBrujn-indices in the `HOL` library.
  """
  @spec greater_eq?(HOL.Data.hol_term(), HOL.Data.hol_term()) :: boolean()
  def greater_eq?(s, t) do
    s_nv = quantify_fvars(s)
    t_nv = quantify_fvars(t)

    ncpo_weak(s_nv, t_nv, true, false, MapSet.new())
  end

  #############################################################################
  # MAIN NCPO
  #############################################################################

  @spec ncpo(
          HOL.Data.hol_term(),
          HOL.Data.hol_term(),
          boolean(),
          boolean(),
          MapSet.t(HOL.Data.hol_term())
        ) ::
          boolean()
  defp ncpo(t, t, _, _, _), do: false

  defp ncpo(s, t, var_rec, type_comp, vars) do
    if not type_comp || type_geq?(get_term_type(s), get_term_type(t)) do
      case s do
        # s is λ-abstraction
        hol_term(bvars: [declaration(type: type) | _]) ->
          case t do
            # λ=
            hol_term(bvars: [declaration(type: ^type) | _]) ->
              ncpo(peel_binder(s), peel_binder(t), var_rec, false, vars)

            # λ≠
            hol_term(bvars: [_ | _]) ->
              ncpo(s, peel_binder(t), var_rec, false, vars)

            # λ▷
            _ ->
              ncpo_weak(peel_binder(s), t, var_rec, true, vars)
          end

        # s is an applied function symbol
        hol_term(head: declaration(kind: :co, name: f_name), args: s_args) ->
          # F▷
          if Enum.any?(s_args, &bawo(&1, t, var_rec, vars)) do
            true
          else
            case t do
              # FX and Fλ cases
              hol_term(bvars: [declaration(type: type) | _]) ->
                if eta_expanded_var?(t) do
                  MapSet.member?(vars, t)
                else
                  var = mk_uniqe_var(type) |> mk_term()
                  ncpo(s, mk_appl_term(t, var), var_rec, false, MapSet.put(vars, var))
                end

              # applied function symbol (F= cases)
              hol_term(bvars: [], head: declaration(kind: :co, name: g_name), args: t_args) ->
                cond do
                  # F= cases
                  precedence(f_name) == precedence(g_name) ->
                    case status(f_name) do
                      :mul ->
                        diff_s = s_args -- t_args
                        diff_t = t_args -- s_args

                        if Enum.empty?(diff_s) and Enum.empty?(diff_t) do
                          false
                        else
                          Enum.all?(diff_t, fn t_elem ->
                            Enum.any?(diff_s, fn s_elem ->
                              # beta reduction is implicitly handled by the HOL library
                              ncpo(s_elem, t_elem, var_rec, true, MapSet.new()) ||
                                structurally_smaller?(s_elem, t_elem, vars)
                            end)
                          end)
                        end

                      :lex ->
                        Enum.zip(s_args, t_args)
                        |> lex_gt_helper(s, s_args, t_args, 0, var_rec, vars)
                    end

                  # F≻
                  precedence(f_name) > precedence(g_name) ->
                    Enum.all?(t_args, &ncpo(s, &1, var_rec, false, vars))

                  true ->
                    false
                end

              # singleton variable symbol
              hol_term(bvars: [], head: declaration(kind: :fv), args: []) ->
                MapSet.member?(vars, t)

              # applied variable symbol
              hol_term(bvars: [], head: declaration(kind: :fv) = h, args: t_args) ->
                var_rec &&
                  ncpo(s, mk_term(h), false, false, vars) &&
                  Enum.all?(t_args, &ncpo(s, &1, true, false, vars))
            end
          end

        # s is versatile (cannot order)
        hol_term(head: declaration(kind: :fv)) ->
          false
      end
    else
      false
    end
  end

  @spec ncpo_weak(HOL.Data.hol_term(), HOL.Data.hol_term(), boolean(), boolean(), MapSet.t()) ::
          boolean()
  defp ncpo_weak(s, t, var_rec, type_comp, vars) do
    s == t || ncpo(s, t, var_rec, type_comp, vars)
  end

  #############################################################################
  # LEXICOGRAPHIC COMPARISON
  #############################################################################

  defp lex_gt_helper([], _, s_args, t_args, _, _, _) do
    length(s_args) > length(t_args)
  end

  defp lex_gt_helper([{si, ti} | rest], s, s_args, t_args, idx, var_rec, vars) do
    if si == ti do
      lex_gt_helper(rest, s, s_args, t_args, idx + 1, var_rec, vars)
    else
      comp_check =
        ncpo(si, ti, var_rec, true, MapSet.new()) || structurally_smaller?(si, ti, vars)

      if comp_check do
        Enum.drop(t_args, idx + 1) |> Enum.all?(&ncpo(s, &1, var_rec, false, vars))
      else
        false
      end
    end
  end

  #############################################################################
  # ACCESSIBILITY & STRUCTURALLY SMALLER
  #############################################################################

  defp bawo(s, t, var_rec, vars) do
    if s == t || ncpo(s, t, var_rec, true, vars) do
      true
    else
      case s do
        hol_term(bvars: [_ | _]) ->
          bawo(peel_binder(s), t, var_rec, vars)

        hol_term(head: declaration(kind: :co), args: s_args, type: s_type) ->
          Enum.any?(accessible_indices(s_type), fn i ->
            u = Enum.at(s_args, i)
            # check if u is versatile -> not sure if this needs recursion
            case u do
              hol_term(bvars: [], head: declaration(kind: :fv)) -> u == t
              # This case should never happen, only listed as safety fallback
              hol_term(bvars: [], head: declaration(kind: :bv)) -> u == t
              _ -> bawo(u, t, var_rec, vars)
            end
          end)

        _ ->
          false
      end
    end
  end

  defp structurally_smaller?(s, t, vars) do
    {u, x_args} = decompose_app(t)

    if Enum.all?(x_args, &MapSet.member?(vars, &1)) && accessible_subterm?(s, u) do
      type(goal: a_sort) = get_term_type(t) |> get_goal_type_recursive()

      Enum.all?(x_args, fn x ->
        MapSet.size(positions_of_sort(a_sort, get_term_type(x))) == 0
      end)
    else
      false
    end
  end

  #############################################################################
  # UTILITY FUNCTIONS
  #############################################################################

  defp accessible_indices(type) do
    type(goal: return_sort) = get_goal_type_recursive(type)

    get_arg_types(type)
    |> Enum.with_index()
    |> Enum.filter(fn {ti, _idx} ->
      type(goal: ti_base_sort) = get_goal_type_recursive(ti)

      sort_cond =
        not (return_sort == ti_base_sort or
               base_type_precedence(return_sort) > base_type_precedence(ti_base_sort))

      sort_cond and occurs_only_positively?(return_sort, ti)
    end)
    |> Enum.map(fn {_, idx} -> idx end)
  end

  defp accessible_subterm?(s, u) do
    case s do
      ^u ->
        true

      hol_term(head: declaration(kind: :co), args: s_args, type: s_type) ->
        Enum.any?(accessible_indices(s_type), fn i ->
          si = Enum.at(s_args, i)
          accessible_subterm?(si, u)
        end)

      _ ->
        false
    end
  end

  defp decompose_app(t) do
    case t do
      hol_term(bvars: [], head: h, args: args) -> {mk_term(h), args}
      _ -> {t, []}
    end
  end

  defp get_goal_type_recursive(type(goal: g)) when is_atom(g), do: type(goal: g, args: [])
  defp get_goal_type_recursive(type(goal: g)), do: get_goal_type_recursive(g)

  defp eta_expanded_var?(hol_term(bvars: bvs, head: declaration(kind: :fv), args: args)) do
    # All bound variables have a corresponding argument and vice versa
    Enum.all?(bvs, fn bv ->
      Enum.any?(args, &match?(hol_term(head: ^bv), &1))
    end) &&
      Enum.all?(args, fn arg ->
        Enum.any?(bvs, &match?(hol_term(head: &1), arg))
      end)
  end

  defp eta_expanded_var?(_), do: false

  defp peel_binder(hol_term(bvars: [declaration(type: type) | _]) = term) do
    var_term = mk_uniqe_var(type) |> mk_term()
    term |> mk_appl_term(var_term)
  end

  defp peel_binder(t), do: t

  defp quantify_fvars(hol_term(fvars: []) = t), do: t

  defp quantify_fvars(hol_term(fvars: [declaration(type: type) = fv | _]) = t) do
    abs = mk_abstr_term(t, fv)
    pi_term(mk_type(:o, [type])) |> mk_appl_term(abs) |> quantify_fvars()
  end
end
