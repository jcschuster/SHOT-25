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
                    combined_checkpoints =
                      checkpoints ++
                        Enum.map(
                          new_cpts,
                          fn {:unif_checkpoint, new_substs, new_remaining} ->
                            updated_substitutions = apply_subst(new_substs, substitutions)
                            {:unif_checkpoint, updated_substitutions ++ new_substs, new_remaining}
                          end
                        )

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
      Enum.map(rest, &PrettyPrint.pp_term/1) |> inspect(label: "Rest") |> Logger.debug()
      Enum.map(clause, &PrettyPrint.pp_term/1) |> inspect(label: "Clause") |> Logger.debug()

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

      # reflexivity of equality -> a=a is always true
      [hol_term(head: any_equals_const(), args: [a, a]) | rest] ->
        tableaux(rest, max_inst, clause, constraints, instantiation_count, incomplete?)

      # negated equality -> ¬(a=a) is always false
      [negated(hol_term(head: any_equals_const(), args: [a, a])) | _rest] ->
        {:closed, []}

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

      # equality (type i) -> Leibnitz equality
      [hol_term(head: equals_const(type_i()), args: [hol_term() = a, hol_term() = b]) | rest] ->
        Logger.debug("equality i")
        p = mk_uniqe_var(type_io())
        p_term = mk_term(p)
        p_a = mk_appl_term(p_term, a)
        p_b = mk_appl_term(p_term, b)
        pi = pi_const(type_io_o()) |> mk_term()

        inner_equiv = equivalent_term() |> mk_appl_term(p_a) |> mk_appl_term(p_b)
        abstr = inner_equiv |> mk_abstr_term(p)
        quant = pi |> mk_appl_term(abstr)

        tableaux([quant | rest], max_inst, clause, constraints, instantiation_count, incomplete?)

      # negated equality (type i) -> negated Leibnitz equality
      [
        negated(hol_term(head: equals_const(type_i()), args: [hol_term() = a, hol_term() = b]))
        | rest
      ] ->
        Logger.debug("negated equality i")
        p = mk_uniqe_var(type_io())
        p_term = mk_term(p)
        p_a = mk_appl_term(p_term, a)
        p_b = mk_appl_term(p_term, b)
        pi = pi_const(type_io_o()) |> mk_term()

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
