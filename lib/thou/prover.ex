defmodule THOU.Prover do
  import HOL.Data
  import HOL.Terms
  import HOL.Unification
  import THOU.Util
  import THOU.HOL.Definitions
  import THOU.HOL.Patterns
  require Logger

  @empty_clause MapSet.new()

  # Bounds for ensuring termination and complexity control
  @max_instantiations 4
  @unification_depth 8

  def sat(formulas) when is_list(formulas) do
    # iterative deepening
    Enum.reduce_while(1..@max_instantiations//1, {:incomplete, [], []}, fn max_inst, _ ->
      case tableaux(formulas, max_inst) do
        {:incomplete, clause, constr} ->
          Logger.debug("\nInstantiation limit exceeded, trying higher limit\n")
          {:cont, {:incomplete, clause, constr}}

        res_state ->
          {:halt, res_state}
      end
    end)
    |> as_assignment()
  end

  def sat(formula), do: sat([formula])

  def prove(conclusion, assumptions \\ []) do
    neg_conclusion = sem_negate(conclusion)

    case sat([neg_conclusion | assumptions]) do
      :unsat -> :valid
      {:unknown, assignment} -> {:unknown, assignment}
      assignment -> {:countersat, assignment}
    end
  end

  def unify_with_literals(formula, literals, constraints) do
    Enum.reduce(literals, [], fn lit, solutions ->
      ("Trying to unify #{PrettyPrint.pp_term(formula)} with literal #{PrettyPrint.pp_term(lit)}" <>
         " under constraints #{pp_constraints(constraints)}")
      |> Logger.debug()

      result = unify([{formula, lit} | constraints], true, @unification_depth)

      PrettyPrint.pp_res(result) |> Logger.debug()

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
  defp branch(a, b, rest, clause, constraints, max_inst, instantiation_count, incomplete?) do
    left_side = List.flatten([a])
    right_side = List.flatten([b])

    case tableaux(
           left_side ++ rest,
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
         # For iterative deepening
         max_inst,
         clause \\ @empty_clause,
         constraints \\ [],
         # Track instantiations of quantifiers
         instantiation_count \\ %{},
         incomplete? \\ false
       ) do
    if formulas == [] do
      "\nNo formulas remain" |> Logger.debug()
    else
      [formula | rest] = formulas
      "\nProcessing formula #{PrettyPrint.pp_term(formula)}" |> Logger.debug()
      rest_pp = Enum.map(rest, &PrettyPrint.pp_term/1) |> inspect()
      ("Rest: " <> rest_pp) |> Logger.debug()
      clause_pp = Enum.map(clause, &PrettyPrint.pp_term/1) |> inspect()
      ("Clause: " <> clause_pp) |> Logger.debug()

      if get_term_type(formula) != type_o() do
        IO.puts("All formulas must be of type bool")
      end
    end

    case formulas do
      # empty formulas and incomplete flag -> rules exhausted while max_inst met
      [] when incomplete? ->
        Logger.debug("branch open due to exceeding maximum instantiations")
        {:incomplete, clause, constraints}

      # empty formulas -> rules exhausted
      [] ->
        Logger.debug("branch stays open")
        {:open, clause, constraints}

      #################################################################################
      # BOOLEAN CONSTANTS
      #################################################################################

      [true_term() | rest] ->
        Logger.debug("top constant")
        tableaux(rest, max_inst, clause, constraints, instantiation_count, incomplete?)

      [negated(true_term()) | _rest] ->
        Logger.debug("negated top constant -> branch closed")
        {:closed, []}

      [false_term() | _rest] ->
        Logger.debug("bottom constant -> branch closed")
        {:closed, []}

      [negated(false_term()) | rest] ->
        Logger.debug("negated bottom constant")
        tableaux(rest, max_inst, clause, constraints, instantiation_count, incomplete?)

      #################################################################################
      # ATOMS
      #################################################################################

      # atomic formula with free variable head
      [formula = hol_term(head: declaration(kind: :fv), type: type_o()) | rest] ->
        Logger.debug("positive atom")

        handle_atom(
          formula,
          :pos,
          clause,
          rest,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      # atomic formula with constant as head (no logical connective)
      [hol_term(head: declaration(kind: :co, name: name), type: type_o()) = formula | rest]
      when name not in signature_symbols() ->
        Logger.debug("positive atom")

        handle_atom(
          formula,
          :pos,
          clause,
          rest,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      # negated atomic formula with free variable head
      [negated(hol_term(head: declaration(kind: :fv))) = formula | rest] ->
        Logger.debug("negative atom")

        handle_atom(
          formula,
          :neg,
          clause,
          rest,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      # negated atomic formula with constant as head (no logical connective)
      [negated(hol_term(head: declaration(kind: :co, name: name))) = formula | rest]
      when name not in signature_symbols() ->
        Logger.debug("negative atom")

        handle_atom(
          formula,
          :neg,
          clause,
          rest,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      #################################################################################
      # DOUBLE NEGATION
      #################################################################################

      # double negation
      [negated(negated(a)) | rest] ->
        Logger.debug("double negation")
        tableaux([a | rest], max_inst, clause, constraints, instantiation_count, incomplete?)

      #################################################################################
      # EQUALITY
      #################################################################################

      ################################## REFLEXIVITY ##################################

      # reflexivity of equality -> a=a is always true
      [hol_term(head: any_equals_const(), args: [a, a]) | rest] ->
        Logger.debug("reflexivity of equality")
        tableaux(rest, max_inst, clause, constraints, instantiation_count, incomplete?)

      # negated equality -> ¬(a=a) is always false
      [negated(hol_term(head: any_equals_const(), args: [a, a])) | _rest] ->
        Logger.debug("irreflexivity of inequality")
        {:closed, []}

      ################################# EXTENSIONALITY ################################

      [
        hol_term(
          head: any_equals_const(),
          args: [
            hol_term(bvars: [], head: declaration(name: n) = h, args: args1, type: t),
            hol_term(bvars: [], head: h, args: args2, type: t)
          ]
        )
        | rest
      ]
      when n not in signature_symbols() ->
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
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      [
        hol_term(
          head: any_equals_const(),
          args: [
            hol_term(bvars: [], head: hol_term() = h, args: args1, type: t),
            hol_term(bvars: [], head: h, args: args2, type: t)
          ]
        )
        | rest
      ] ->
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
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      [
        negated(
          hol_term(
            head: any_equals_const(),
            args: [
              hol_term(bvars: [], head: hol_term() = h, args: args1, type: t),
              hol_term(bvars: [], head: h, args: args2, type: t)
            ]
          )
        )
        | rest
      ] ->
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
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      [
        negated(
          hol_term(
            head: any_equals_const(),
            args: [
              hol_term(bvars: [], head: declaration(name: n) = h, args: args1, type: t),
              hol_term(bvars: [], head: h, args: args2, type: t)
            ]
          )
        )
        | rest
      ]
      when n not in signature_symbols() ->
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
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      ############################# TYPED EQUALITY SYMBOLS ############################

      # equality (type o) -> transform to equivalence
      [hol_term(head: equals_const(type_o()), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("equality o")
        equiv = equivalent_term() |> mk_appl_term(a) |> mk_appl_term(b)
        tableaux([equiv | rest], max_inst, clause, constraints, instantiation_count, incomplete?)

      # negated equality (type o)
      [
        negated(hol_term(head: equals_const(type_o()), args: [hol_term() = a, hol_term() = b]))
        | rest
      ] ->
        Logger.debug("negated equality o")
        eq = equivalent_term() |> mk_appl_term(a) |> mk_appl_term(b)
        neg_eq = neg_term() |> mk_appl_term(eq)
        tableaux([neg_eq | rest], max_inst, clause, constraints, instantiation_count, incomplete?)

      # equality (other atomic types) -> Leibnitz equality
      [
        hol_term(
          head: equals_const(type(goal: g, args: [])),
          args: [hol_term() = a, hol_term() = b]
        ) = formula
        | rest
      ]
      when is_atom(g) ->
        t = type(goal: g, args: [])

        if unknown_type?(t) do
          Logger.debug("equality unknown type (treated as atom)")

          handle_atom(
            formula,
            :pos,
            clause,
            rest,
            constraints,
            max_inst,
            instantiation_count,
            incomplete?
          )
        else
          Logger.debug("equality other atomic types")
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
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )
        end

      # negated equality (other atomic types) -> negated Leibnitz equality
      [
        negated(
          hol_term(
            head: equals_const(type(goal: g, args: [])),
            args: [hol_term() = a, hol_term() = b]
          )
        ) = formula
        | rest
      ]
      when is_atom(g) ->
        t = type(goal: g, args: [])

        if unknown_type?(t) do
          Logger.debug("negated equality unknown type (treated as atom)")

          handle_atom(
            formula,
            :neg,
            clause,
            rest,
            constraints,
            max_inst,
            instantiation_count,
            incomplete?
          )
        else
          Logger.debug("negated equality other atomic types")
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
            max_inst,
            clause,
            constraints,
            instantiation_count,
            incomplete?
          )
        end

      # equality (function types) -> functional extensionality
      [hol_term(head: equals_const(type), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("equality function")
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

        tableaux([quant | rest], max_inst, clause, constraints, instantiation_count, incomplete?)

      # negated equality (function types) -> negated functional extensionality
      [negated(hol_term(head: equals_const(type), args: [hol_term() = a, hol_term() = b])) | rest] ->
        Logger.debug("negated equality function")
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
      [hol_term(head: or_const(), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("disjunction")
        branch(a, b, rest, clause, constraints, max_inst, instantiation_count, incomplete?)

      # negated disjunction
      [negated(hol_term(head: or_const(), args: [hol_term() = a, hol_term() = b])) | rest] ->
        Logger.debug("negated disjunction")

        tableaux(
          [sem_negate(a), sem_negate(b) | rest],
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      # conjunction
      [hol_term(head: and_const(), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("conjunction")
        tableaux([a, b | rest], max_inst, clause, constraints, instantiation_count, incomplete?)

      # negated conjunction
      [negated(hol_term(head: and_const(), args: [hol_term() = a, hol_term() = b])) | rest] ->
        Logger.debug("negated conjunction")

        branch(
          sem_negate(a),
          sem_negate(b),
          rest,
          clause,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      # implication
      [hol_term(head: implies_const(), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("implication")

        branch(
          sem_negate(a),
          b,
          rest,
          clause,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      # negated implication
      [negated(hol_term(head: implies_const(), args: [hol_term() = a, hol_term() = b])) | rest] ->
        Logger.debug("negated implication")

        tableaux(
          [a, sem_negate(b) | rest],
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      # equivalence
      [hol_term(head: equivalent_const(), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("equivalence")

        branch(
          [a, b],
          [sem_negate(a), sem_negate(b)],
          rest,
          clause,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      # negated equivalence
      [negated(hol_term(head: equivalent_const(), args: [hol_term() = a, hol_term() = b])) | rest] ->
        Logger.debug("negated equivalence")

        branch(
          [sem_negate(a), b],
          [a, sem_negate(b)],
          rest,
          clause,
          constraints,
          max_inst,
          instantiation_count,
          incomplete?
        )

      #################################################################################
      # QUANTORS
      #################################################################################

      # universal quantification -> fresh variable (can be repeated!)
      [hol_term(head: pi_const(type(args: [type])), args: [hol_term() = body]) = term | rest] ->
        Logger.debug("universal quantification")
        count = Map.get(instantiation_count, term, 0)

        if count < max_inst do
          new_instantiation_count = Map.put(instantiation_count, term, count + 1)
          fresh_variable = mk_term(mk_uniqe_var(type))
          fresh_instance = mk_appl_term(body, fresh_variable)

          tableaux(
            [fresh_instance | rest] ++ [term],
            max_inst,
            clause,
            constraints,
            new_instantiation_count,
            incomplete?
          )
        else
          # skip the universal quantification - upper bound of instantiations reached
          Logger.debug("instantiation limit exceeded")
          tableaux(rest, max_inst, clause, constraints, instantiation_count, true)
        end

      # negated universal quantification -> skolemization
      [negated(hol_term(head: pi_const(type(args: [type])), args: [hol_term() = body])) | rest] ->
        Logger.debug("negated universal quantification")

        tableaux(
          [
            mk_appl_term(
              neg_term(),
              mk_appl_term(body, mk_new_skolem_term(get_fvars(body), type))
            )
            | rest
          ],
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      # existential quantification -> skolemization
      [hol_term(head: sigma_const(type(args: [type])), args: [hol_term() = body]) | rest] ->
        Logger.debug("existential quantification")

        tableaux(
          [mk_appl_term(body, mk_new_skolem_term(get_fvars(body), type)) | rest],
          max_inst,
          clause,
          constraints,
          instantiation_count,
          incomplete?
        )

      # negated existential quantification -> fresh variable (can be repeated!)
      [
        negated(hol_term(head: sigma_const(type(args: [type])), args: [hol_term() = body])) = term
        | rest
      ] ->
        Logger.debug("negated existential quantification")
        count = Map.get(instantiation_count, term, 0)

        if count < max_inst do
          new_instantiation_count = Map.put(instantiation_count, term, count + 1)
          fresh_variable = mk_term(mk_uniqe_var(type))
          fresh_instance = syn_negate(mk_appl_term(body, fresh_variable))

          tableaux(
            [fresh_instance | rest] ++ [term],
            max_inst,
            clause,
            constraints,
            new_instantiation_count,
            incomplete?
          )
        else
          # skip the negated existential quantification - upper bound of instantiations reached
          Logger.debug("instantiation limit exceeded")
          tableaux(rest, max_inst, clause, constraints, instantiation_count, true)
        end
    end
  end

  defp as_assignment({:closed, _}) do
    "All branches closed -> unsatisfiable" |> Logger.debug()
    :unsat
  end

  defp as_assignment({:open, clause, constraints}) do
    "Some branches still open -> countermodel exists" |> Logger.debug()

    pp_assignment(clause) <> " || " <> pp_constraints(constraints)
  end

  defp as_assignment({:incomplete, clause, constraints}) do
    "Result unknown due to prover incompleteness" |> Logger.debug()

    {:unknown, pp_assignment(clause) <> " || " <> pp_constraints(constraints)}
  end
end
