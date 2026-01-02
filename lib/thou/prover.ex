defmodule THOU.Prover do
  import HOL.Data
  import HOL.Terms
  import HOL.Unification
  import THOU.Util
  import THOU.HOL.Definitions
  import THOU.HOL.Patterns
  alias THOU.Preprocessing.Rewriting
  require Logger

  @empty_clause MapSet.new()

  # Bounds for ensuring termination and complexity control
  @max_instantiations 4
  @unification_depth 8

  def sat(formulas, definitions \\ %{})

  def sat(formulas, definitions) when is_list(formulas) do
    tableaux(formulas, definitions, @max_instantiations)
    |> as_assignment()
  end

  def sat(formula, definitions), do: sat([formula], definitions)

  def prove(conclusion, assumptions \\ [], definitions \\ []) do
    neg_conclusion = sem_negate(conclusion)

    case sat([neg_conclusion | assumptions], definitions) do
      :unsat -> :valid
      {:unknown, assignment} -> {:unknown, assignment}
      assignment -> {:countersat, assignment}
    end
  end

  def unify_with_literals(formula, literals, constraints) do
    Enum.reduce(literals, [], fn lit, solutions ->
      ("Trying to unify #{PrettyPrint.pp_term(formula)} with literal #{PrettyPrint.pp_term(lit)}" <>
         " under constraints #{pp_constraints(constraints)}")
      |> Logger.notice()

      result = unify([{formula, lit} | constraints], true, @unification_depth)

      PrettyPrint.pp_res(result) |> Logger.notice()

      {:unif_res_sum, unif_solutions, _} = result

      new_solutions =
        Enum.map(unif_solutions, fn {:unif_sol, substitutions, flexlist} ->
          {:unif_checkpoint, substitutions, flexlist}
        end)

      solutions ++ new_solutions
    end)
  end

  defp handle_atom(
         formula,
         polarity,
         clause,
         rest,
         constraints,
         definitions,
         max_inst,
         instantiation_count,
         incomplete?
       ) do
    unif_set =
      case polarity do
        :pos -> sem_negate(clause)
        :neg -> clause
      end

    stripped_formula =
      case formula do
        hol_term(bvars: [], head: neg_const(), args: [inner]) -> inner
        _ -> formula
      end

    unif_checkpoints =
      case unify_with_literals(stripped_formula, unif_set, constraints) do
        [] -> unify_with_literals(sem_negate(formula), syn_negate(unif_set), constraints)
        sol -> sol
      end

    case unif_checkpoints do
      [] ->
        # no solutions found with current atom
        tableaux(
          rest,
          definitions,
          max_inst,
          MapSet.put(clause, formula),
          constraints,
          instantiation_count,
          incomplete?
        )

      candidates ->
        {:closed, candidates}
    end
  end

  # Which branch to check first? -> Introduce Term Orderings and Heuristics
  defp branch(
         a,
         b,
         rest,
         clause,
         constraints,
         definitions,
         max_inst,
         instantiation_count,
         incomplete?
       ) do
    left_side = List.flatten([a])
    right_side = List.flatten([b])

    case tableaux(
           left_side ++ rest,
           definitions,
           max_inst,
           clause,
           constraints,
           instantiation_count,
           incomplete?
         ) do
      {:incomplete, clause, constr} ->
        {:incomplete, clause, constr}

      {:open, res_clause, constr} ->
        {:open, res_clause, constr}

      {:closed, unif_checkpoints} ->
        # Option for concurrency here, as unification checkpoints can be checked in parallel
        case unif_checkpoints do
          [] ->
            # closed without substitutions or constraints
            tableaux(
              right_side ++ rest,
              definitions,
              max_inst,
              clause,
              constraints,
              instantiation_count,
              incomplete?
            )

          _ ->
            # Try checkpoints on right branch and propagate up
            {new_checkpoints, last_open} =
              Enum.reduce_while(unif_checkpoints, {[], nil}, fn {:unif_checkpoint, substitutions,
                                                                 remaining},
                                                                {checkpoints, prev_open} ->
                new_rest = apply_subst(substitutions, rest)
                new_clause = apply_subst(substitutions, clause)
                new_right_side = apply_subst(substitutions, right_side)

                case tableaux(
                       new_right_side ++ new_rest,
                       definitions,
                       max_inst,
                       new_clause,
                       remaining,
                       instantiation_count,
                       incomplete?
                     ) do
                  {:closed, new_cpts} ->
                    added_cpts =
                      if new_cpts == [] do
                        [{:unif_checkpoint, substitutions, remaining}]
                      else
                        Enum.map(
                          new_cpts,
                          fn {:unif_checkpoint, new_substs, new_remaining} ->
                            updated_substitutions = apply_subst(new_substs, substitutions)
                            {:unif_checkpoint, updated_substitutions ++ new_substs, new_remaining}
                          end
                        )
                      end

                    combined_checkpoints = checkpoints ++ added_cpts

                    {:halt, {combined_checkpoints, prev_open}}

                  {:open, right_clause, right_constraints} ->
                    {:cont, {checkpoints, {:open, right_clause, right_constraints}}}

                  other ->
                    case prev_open do
                      nil ->
                        {:cont, {checkpoints, other}}

                      _ ->
                        # don't overwrite :open branches with :incomplete
                        {:cont, {checkpoints, prev_open}}
                    end
                end
              end)

            if new_checkpoints != [] do
              {:closed, new_checkpoints}
            else
              last_open
            end
        end
    end
  end

  defp tableaux(
         formulas,
         definitions,
         max_inst,
         clause \\ @empty_clause,
         constraints \\ [],
         # Track instantiations of quantifiers
         instantiation_count \\ %{},
         incomplete? \\ false
       ) do
    if formulas == [] do
      if incomplete? do
        # empty formulas and incomplete flag -> rules exhausted while max_inst met
        Logger.notice("OPEN: no formulas remain, exceeded maximum instantiation limit")
        {:incomplete, clause, constraints}
      else
        Logger.notice("OPEN: no formulas remain")
        {:open, clause, constraints}
      end
    else
      [current_formula | rest] = formulas
      formula = Rewriting.canonicalize(current_formula)
      "Processing formula #{PrettyPrint.pp_term(current_formula)}" |> Logger.notice()
      "Canonicalized: #{PrettyPrint.pp_term(formula)}" |> Logger.notice()
      rest_pp = Enum.map(rest, &PrettyPrint.pp_term/1) |> inspect()
      ("Rest: " <> rest_pp) |> Logger.info()
      clause_pp = Enum.map(clause, &PrettyPrint.pp_term/1) |> inspect()
      ("Clause: " <> clause_pp) |> Logger.info()

      case formula do
        #################################################################################
        # BOOLEAN CONSTANTS
        #################################################################################

        true_term() ->
          Logger.notice("applying \"⊤\"")

          tableaux(
            rest,
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        negated(true_term()) ->
          Logger.notice("applying \"¬⊤\" (closing branch)")
          {:closed, []}

        false_term() ->
          Logger.notice("applying \"⊥\" (closing branch)")
          {:closed, []}

        negated(false_term()) ->
          Logger.notice("applying \"⊤\"")

          tableaux(
            rest,
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        #################################################################################
        # ATOMS
        #################################################################################

        # atomic formula with free variable head
        hol_term(head: declaration(kind: :fv), type: type_o()) ->
          Logger.notice("applying \"Atom\"")

          handle_atom(
            formula,
            :pos,
            clause,
            rest,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # negated atomic formula with free variable head
        negated(hol_term(head: declaration(kind: :fv))) ->
          Logger.notice("applying \"Atom\"")

          handle_atom(
            formula,
            :neg,
            clause,
            rest,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # non-unfolded definition
        hol_term(head: declaration(kind: :co, name: name), args: args, type: type_o())
        when is_map_key(definitions, name) ->
          Logger.notice("unfolding definition for \"#{name}\"")

          equality(_id, def_body) = Map.get(definitions, name)

          unfolded_term =
            Enum.reduce(args, def_body, fn arg, acc ->
              mk_appl_term(acc, arg)
            end)

          tableaux(
            [unfolded_term | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # negated non-unfolded definition
        negated(hol_term(head: declaration(kind: :co, name: name), args: args))
        when is_map_key(definitions, name) ->
          Logger.notice("unfolding negated definition for \"#{name}\"")

          equality(_id, def_body) = Map.get(definitions, name)

          unfolded_inner =
            Enum.reduce(args, def_body, fn arg, acc ->
              mk_appl_term(acc, arg)
            end)

          tableaux(
            [syn_negate(unfolded_inner) | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # atomic formula with constant as head (no logical connective)
        hol_term(head: declaration(kind: :co, name: name), type: type_o())
        when name not in signature_symbols() ->
          Logger.notice("applying \"Atom\"")

          handle_atom(
            formula,
            :pos,
            clause,
            rest,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # negated atomic formula with constant as head (no logical connective)
        negated(hol_term(head: declaration(kind: :co, name: name)))
        when name not in signature_symbols() ->
          Logger.notice("applying \"Atom\"")

          handle_atom(
            formula,
            :neg,
            clause,
            rest,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        #################################################################################
        # DOUBLE NEGATION
        #################################################################################

        # double negation
        negated(negated(a)) ->
          Logger.notice("applying \"¬¬\"")

          tableaux(
            [a | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        #################################################################################
        # EQUALITY
        #################################################################################

        ################################## REFLEXIVITY ##################################

        # reflexivity of equality -> a=a is always true
        equality(a, a) ->
          Logger.notice("applying \"=r\"")

          tableaux(
            rest,
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # negated equality -> ¬(a=a) is always false
        negated(equality(a, a)) ->
          Logger.notice("applying \"¬=r\"")
          {:closed, []}

        ################################# EXTENSIONALITY ################################

        equality(
          hol_term(bvars: [], head: declaration(name: n) = h, args: args1, type: t),
          hol_term(bvars: [], head: h, args: args2, type: t)
        )
        when n not in signature_symbols() ->
          Logger.notice("applying \"=ext\"")

          subproblems =
            Enum.zip(args1, args2)
            |> Enum.map(fn {t1, t2} ->
              get_term_type(t1) |> equals_term() |> mk_appl_term(t1) |> mk_appl_term(t2)
            end)
            |> Enum.reduce(true_term(), fn t, acc ->
              and_term() |> mk_appl_term(t) |> mk_appl_term(acc)
            end)

          tableaux(
            [subproblems | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        equality(
          hol_term(bvars: [], head: hol_term() = h, args: args1, type: t),
          hol_term(bvars: [], head: h, args: args2, type: t)
        ) ->
          Logger.notice("applying \"=ext\"")

          subproblems =
            Enum.zip(args1, args2)
            |> Enum.map(fn {t1, t2} ->
              get_term_type(t1) |> equals_term() |> mk_appl_term(t1) |> mk_appl_term(t2)
            end)
            |> Enum.reduce(true_term(), fn t, acc ->
              and_term() |> mk_appl_term(t) |> mk_appl_term(acc)
            end)

          tableaux(
            [subproblems | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        negated(
          equality(
            hol_term(bvars: [], head: hol_term() = h, args: args1, type: t),
            hol_term(bvars: [], head: h, args: args2, type: t)
          )
        ) ->
          Logger.notice("applying \"¬=ext\"")

          inner_subproblems =
            Enum.zip(args1, args2)
            |> Enum.map(fn {t1, t2} ->
              get_term_type(t1) |> equals_term() |> mk_appl_term(t1) |> mk_appl_term(t2)
            end)
            |> Enum.reduce(true_term(), fn t, acc ->
              and_term() |> mk_appl_term(t) |> mk_appl_term(acc)
            end)

          subproblems = mk_appl_term(neg_term(), inner_subproblems)

          tableaux(
            [subproblems | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        negated(
          equality(
            hol_term(bvars: [], head: declaration(name: n) = h, args: args1, type: t),
            hol_term(bvars: [], head: h, args: args2, type: t)
          )
        )
        when n not in signature_symbols() ->
          Logger.notice("applying \"¬=ext\"")

          inner_subproblems =
            Enum.zip(args1, args2)
            |> Enum.map(fn {t1, t2} ->
              get_term_type(t1) |> equals_term() |> mk_appl_term(t1) |> mk_appl_term(t2)
            end)
            |> Enum.reduce(true_term(), fn t, acc ->
              and_term() |> mk_appl_term(t) |> mk_appl_term(acc)
            end)

          subproblems = mk_appl_term(neg_term(), inner_subproblems)

          tableaux(
            [subproblems | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        ############################# TYPED EQUALITY SYMBOLS ############################

        # equality (type o) -> transform to equivalence
        typed_equality(a, b, type_o()) ->
          Logger.notice("applying \"=o\"")
          equiv = equivalent_term() |> mk_appl_term(a) |> mk_appl_term(b)

          tableaux(
            [equiv | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # negated equality (type o)
        negated(typed_equality(a, b, type_o())) ->
          Logger.notice("applying \"¬=o\"")
          eq = equivalent_term() |> mk_appl_term(a) |> mk_appl_term(b)
          neg_eq = neg_term() |> mk_appl_term(eq)

          tableaux(
            [neg_eq | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # equality (other atomic types) -> Leibnitz equality
        typed_equality(a, b, type(goal: g, args: [])) when is_atom(g) ->
          t = type(goal: g, args: [])

          if unknown_type?(t) do
            Logger.notice("applying \"Atom\"")

            handle_atom(
              formula,
              :pos,
              clause,
              rest,
              constraints,
              definitions,
              max_inst,
              instantiation_count,
              incomplete?
            )
          else
            Logger.notice("applying \"=ι\"")

            p = mk_uniqe_var(mk_type(:o, [t]))
            p_term = mk_term(p)
            p_a = mk_appl_term(p_term, a)
            p_b = mk_appl_term(p_term, b)
            pi = pi_const(mk_type(:o, [mk_type(:o, [t])])) |> mk_term()

            inner_equiv = equivalent_term() |> mk_appl_term(p_a) |> mk_appl_term(p_b)
            abstr = inner_equiv |> mk_abstr_term(p)
            quant = pi |> mk_appl_term(abstr)

            tableaux(
              [quant | rest],
              definitions,
              max_inst,
              clause,
              constraints,
              instantiation_count,
              incomplete?
            )
          end

        # negated equality (other atomic types) -> negated Leibnitz equality
        negated(typed_equality(a, b, type(goal: g, args: []))) when is_atom(g) ->
          t = type(goal: g, args: [])

          if unknown_type?(t) do
            Logger.notice("applying \"Atom\"")

            handle_atom(
              formula,
              :neg,
              clause,
              rest,
              constraints,
              definitions,
              max_inst,
              instantiation_count,
              incomplete?
            )
          else
            Logger.notice("applying \"¬=ι\"")

            p = mk_uniqe_var(mk_type(:o, [t]))
            p_term = mk_term(p)
            p_a = mk_appl_term(p_term, a)
            p_b = mk_appl_term(p_term, b)
            pi = pi_const(mk_type(:o, [mk_type(:o, [t])])) |> mk_term()

            inner_equiv = equivalent_term() |> mk_appl_term(p_a) |> mk_appl_term(p_b)
            abstr = inner_equiv |> mk_abstr_term(p)
            quant = pi |> mk_appl_term(abstr)
            neg_quant = neg_term() |> mk_appl_term(quant)

            tableaux(
              [neg_quant | rest],
              definitions,
              max_inst,
              clause,
              constraints,
              instantiation_count,
              incomplete?
            )
          end

        # equality (function types) -> functional extensionality
        typed_equality(a, b, type) ->
          Logger.notice("applying \"=(α⇾β)\"")
          [first_arg_type | rest_arg_types] = get_arg_types(type)
          goal_type = mk_type(get_goal_type(type), rest_arg_types)
          x = mk_uniqe_var(first_arg_type)
          x_term = mk_term(x)
          a_x = mk_appl_term(a, x_term)
          b_x = mk_appl_term(b, x_term)
          equals_term = mk_term(equals_const(goal_type))
          pi = pi_const(mk_type(type_o(), [first_arg_type])) |> mk_term()

          inner_equality = equals_term |> mk_appl_term(a_x) |> mk_appl_term(b_x)
          abstr = inner_equality |> mk_abstr_term(x)
          quant = pi |> mk_appl_term(abstr)

          tableaux(
            [quant | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # negated equality (function types) -> negated functional extensionality
        negated(typed_equality(a, b, type)) ->
          Logger.notice("applying \"¬=(α⇾β)\"")
          [first_arg_type | rest_arg_types] = get_arg_types(type)
          goal_type = mk_type(get_goal_type(type), rest_arg_types)
          x = mk_uniqe_var(first_arg_type)
          x_term = mk_term(x)
          a_x = mk_appl_term(a, x_term)
          b_x = mk_appl_term(b, x_term)
          equals_term = mk_term(equals_const(goal_type))
          pi = pi_const(mk_type(type_o(), [first_arg_type])) |> mk_term()

          inner_equality = equals_term |> mk_appl_term(a_x) |> mk_appl_term(b_x)
          abstr = inner_equality |> mk_abstr_term(x)
          quant = pi |> mk_appl_term(abstr)
          neg_quant = neg_term() |> mk_appl_term(quant)

          tableaux(
            [neg_quant | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        #################################################################################
        # LOGICAL CONNECTIVES
        #################################################################################

        # disjunction
        disjunction(a, b) ->
          Logger.notice("applying \"∨\"")

          branch(
            a,
            b,
            rest,
            clause,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # negated disjunction
        negated(disjunction(a, b)) ->
          Logger.notice("applying \"¬∨\"")

          tableaux(
            [sem_negate(a), sem_negate(b) | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # conjunction
        conjunction(a, b) ->
          Logger.notice("applying \"∧\"")

          tableaux(
            [a, b | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # negated conjunction
        negated(conjunction(a, b)) ->
          Logger.notice("applying \"¬∧\"")

          branch(
            sem_negate(a),
            sem_negate(b),
            rest,
            clause,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # implication
        implication(a, b) ->
          Logger.notice("applying \"⊃\"")

          branch(
            sem_negate(a),
            b,
            rest,
            clause,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # negated implication
        negated(implication(a, b)) ->
          Logger.notice("applying \"¬⊃\"")

          tableaux(
            [a, sem_negate(b) | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # equivalence
        equivalence(a, b) ->
          Logger.notice("applying \"≡\"")

          branch(
            [a, b],
            [sem_negate(a), sem_negate(b)],
            rest,
            clause,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        # negated equivalence
        negated(equivalence(a, b)) ->
          Logger.notice("applying \"¬≡\"")

          branch(
            [sem_negate(a), b],
            [a, sem_negate(b)],
            rest,
            clause,
            constraints,
            definitions,
            max_inst,
            instantiation_count,
            incomplete?
          )

        #################################################################################
        # QUANTORS
        #################################################################################

        # universal quantification -> fresh variable (can be repeated!)
        universal_quantification(body) ->
          Logger.notice("applying \"Π\"")
          count = Map.get(instantiation_count, formula, 0)

          if count < max_inst do
            type(args: [type]) = get_term_type(body)
            new_instantiation_count = Map.put(instantiation_count, formula, count + 1)
            fresh_variable = mk_term(mk_uniqe_var(type))
            fresh_instance = mk_appl_term(body, fresh_variable)

            tableaux(
              [fresh_instance | rest] ++ [formula],
              definitions,
              max_inst,
              clause,
              constraints,
              new_instantiation_count,
              incomplete?
            )
          else
            # skip the universal quantification - upper bound of instantiations reached
            Logger.info("instantiation limit exceeded")
            tableaux(rest, definitions, max_inst, clause, constraints, instantiation_count, true)
          end

        # negated universal quantification -> skolemization
        negated(universal_quantification(body)) ->
          Logger.notice("applying \"¬Π\"")

          type(args: [type]) = get_term_type(body)

          tableaux(
            [
              mk_appl_term(
                neg_term(),
                mk_appl_term(body, mk_new_skolem_term(get_fvars(body), type))
              )
              | rest
            ],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # existential quantification -> skolemization
        existential_quantification(body) ->
          Logger.notice("applying \"Σ\"")

          type(args: [type]) = get_term_type(body)

          tableaux(
            [mk_appl_term(body, mk_new_skolem_term(get_fvars(body), type)) | rest],
            definitions,
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )

        # negated existential quantification -> fresh variable (can be repeated!)
        negated(existential_quantification(body)) ->
          Logger.notice("applying \"¬Σ\"")
          count = Map.get(instantiation_count, formula, 0)

          if count < max_inst do
            type(args: [type]) = get_term_type(body)
            new_instantiation_count = Map.put(instantiation_count, formula, count + 1)
            fresh_variable = mk_term(mk_uniqe_var(type))
            fresh_instance = syn_negate(mk_appl_term(body, fresh_variable))

            tableaux(
              [fresh_instance | rest] ++ [formula],
              definitions,
              max_inst,
              clause,
              constraints,
              new_instantiation_count,
              incomplete?
            )
          else
            # skip the negated existential quantification - upper bound of instantiations reached
            Logger.info("instantiation limit exceeded")
            tableaux(rest, definitions, max_inst, clause, constraints, instantiation_count, true)
          end
      end
    end
  end

  defp as_assignment({:closed, _}) do
    "All branches closed -> unsatisfiable" |> Logger.notice()
    :unsat
  end

  defp as_assignment({:open, clause, constraints}) do
    "Some branches still open -> countermodel exists" |> Logger.notice()

    pp_assignment(clause) <> " || " <> pp_constraints(constraints)
  end

  defp as_assignment({:incomplete, clause, constraints}) do
    "Result unknown due to prover incompleteness" |> Logger.notice()

    {:unknown, pp_assignment(clause) <> " || " <> pp_constraints(constraints)}
  end
end
