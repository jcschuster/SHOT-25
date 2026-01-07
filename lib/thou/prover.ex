defmodule THOU.Prover do
  import HOL.Data
  import HOL.Terms
  import HOL.Unification
  import THOU.HOL.Definitions
  import THOU.HOL.Patterns
  import THOU.Util
  import THOU.PrettyPrint
  alias THOU.Preprocessing.Rewriting
  alias THOU.Heuristics.NCPO
  alias THOU.Prover.{Model, Parameters, State}
  require Logger
  require Record

  Record.defrecord(:unif_checkpoint, substs: nil, constrs: nil)

  @type definitions() :: %{String.t() => HOL.Data.hol_term()}

  @type tableaux_res() ::
          {:closed, [unif_checkpoint()]}
          | {:open, MapSet.t(HOL.Data.hol_term()), [HOL.Data.hol_term()]}
          | {:incomplete, MapSet.t(HOL.Data.hol_term()), [HOL.Data.hol_term()]}

  @type unif_checkpoint() ::
          {:unif_checkpoint, [HOL.Data.substitution()], [HOL.Data.Unification.term_pair()]}

  @type sat_result ::
          {:unknown, Model.t() | nil, :incomplete | :timeout}
          | {:unsat, :closed}
          | {:sat, Model.t()}

  @type proof_result ::
          {:valid, :proven}
          | {:countersat, Model.t()}
          | {:unknown, Model.t() | nil, atom()}

  defmodule Model do
    defstruct assignments: MapSet.new(), constraints: []

    @type t() :: %__MODULE__{
            assignments: MapSet.t(),
            constraints: [{HOL.Data.hol_term(), HOL.Data.hol_term()}]
          }

    defimpl String.Chars, for: __MODULE__ do
      def to_string(model) do
        assignments_str = pp_assignment(model.clause)
        constraints_str = pp_constraints(model.constraints)
        "#{assignments_str} || #{constraints_str}"
      end
    end
  end

  defmodule Parameters do
    defstruct canonicalize: true,
              branch_heuristic: :ncpo,
              max_instantiations: 4,
              unification_depth: 8

    @type t() :: %__MODULE__{
            canonicalize: boolean(),
            branch_heuristic: atom() | nil,
            max_instantiations: pos_integer(),
            unification_depth: pos_integer()
          }

    @spec new() :: t()
    def new(opts \\ []) do
      default_params = %__MODULE__{}

      canonicalize = Keyword.get(opts, :canonicalize, default_params.canonicalize)
      branch_heuristic = Keyword.get(opts, :branch_heuristic, default_params.branch_heuristic)

      max_instantiations =
        Keyword.get(opts, :max_instantiations, default_params.max_instantiations)

      unification_depth = Keyword.get(opts, :unification_depth, default_params.unification_depth)

      %__MODULE__{
        canonicalize: canonicalize,
        branch_heuristic: branch_heuristic,
        max_instantiations: max_instantiations,
        unification_depth: unification_depth
      }
    end
  end

  defmodule State do
    defstruct clause: MapSet.new(),
              constraints: [],
              incomplete?: false,
              inst_count: %{}

    @type t() :: %__MODULE__{
            clause: MapSet.t(),
            constraints: [{HOL.Data.hol_term(), HOL.Data.hol_term()}],
            incomplete?: boolean(),
            inst_count: %{HOL.Data.hol_term() => pos_integer()}
          }

    @spec new() :: t()
    def new(), do: %__MODULE__{}
  end

  @spec sat([HOL.Data.hol_term()], definitions(), Keyword.t()) :: sat_result()
  def sat(formulas, definitions \\ %{}, opts \\ [])

  def sat(formulas, definitions, opts) when is_list(formulas) do
    default_params = Parameters.new()

    timeout = Keyword.get(opts, :timeout, 30_000)
    canonicalize = Keyword.get(opts, :canonicalize, default_params.canonicalize)
    branch_heuristic = Keyword.get(opts, :branch_heuristic, default_params.branch_heuristic)
    max_instantiations = Keyword.get(opts, :max_instantiations, default_params.max_instantiations)
    unification_depth = Keyword.get(opts, :unification_depth, default_params.unification_depth)

    task =
      Task.async(fn ->
        tableaux(
          formulas,
          definitions,
          State.new(),
          Parameters.new(
            canonicalize: canonicalize,
            branch_heuristic: branch_heuristic,
            max_instantiations: max_instantiations,
            unification_depth: unification_depth
          )
        )
      end)

    case Task.yield(task, timeout) do
      {:ok, res} ->
        res

      nil ->
        Task.shutdown(task, :brutal_kill)
        :timeout
    end
    |> as_assignment()
  end

  def sat(formula, definitions, opts), do: sat([formula], definitions, opts)

  @spec prove(HOL.Data.hol_term(), [HOL.Data.hol_term()], definitions(), Keyword.t()) ::
          proof_result()
  def prove(conclusion, assumptions \\ [], definitions \\ %{}, opts \\ []) do
    neg_conclusion = sem_negate(conclusion)

    case sat([neg_conclusion | assumptions], definitions, opts) do
      {:unsat, _} -> {:valid, :proven}
      {:unknown, partial_model, reason} -> {:unknown, partial_model, reason}
      {:sat, counter_model} -> {:countersat, counter_model}
    end
  end

  defp unify_with_literals(formula, literals, constraints, parameters) do
    Enum.reduce(literals, [], fn lit, solutions ->
      ("Trying to unify #{PrettyPrint.pp_term(formula)} with literal #{PrettyPrint.pp_term(lit)}" <>
         " under constraints #{pp_constraints(constraints)}")
      |> Logger.notice()

      result = unify([{formula, lit} | constraints], true, parameters.unification_depth)

      PrettyPrint.pp_res(result) |> Logger.notice()

      {:unif_res_sum, unif_solutions, _} = result

      new_solutions =
        Enum.map(unif_solutions, fn {:unif_sol, substitutions, flexlist} ->
          {:unif_checkpoint, substitutions, flexlist}
        end)

      solutions ++ new_solutions
    end)
  end

  @spec handle_atom(
          HOL.Data.hol_term(),
          :pos | :neg,
          [HOL.Data.hol_term()],
          definitions(),
          State.t(),
          Parameters.t()
        ) ::
          tableaux_res()
  defp handle_atom(formula, polarity, rest, definitions, state, parameters) do
    unif_set =
      case polarity do
        :pos -> sem_negate(state.clause)
        :neg -> state.clause
      end

    stripped_formula =
      case formula do
        hol_term(bvars: [], head: neg_const(), args: [inner]) -> inner
        _ -> formula
      end

    unif_checkpoints =
      case unify_with_literals(stripped_formula, unif_set, state.constraints, parameters) do
        [] ->
          unify_with_literals(
            sem_negate(formula),
            sem_negate(unif_set),
            state.constraints,
            parameters
          )

        sol ->
          sol
      end

    case unif_checkpoints do
      [] ->
        # no solutions found with current atom
        tableaux(
          rest,
          definitions,
          %State{state | clause: MapSet.put(state.clause, formula)},
          parameters
        )

      candidates ->
        {:closed, candidates}
    end
  end

  @spec branch(
          HOL.Data.hol_term() | [HOL.Data.hol_term()],
          HOL.Data.hol_term() | [HOL.Data.hol_term()],
          [HOL.Data.hol_term()],
          definitions(),
          State.t(),
          Parameters.t()
        ) ::
          tableaux_res()
  defp branch(a, b, rest, definitions, state, parameters) do
    a_terms = List.flatten([a])
    b_terms = List.flatten([b])

    {left_side, right_side} =
      case parameters.branch_heuristic do
        :ncpo ->
          if NCPO.smaller_multiset?(a_terms, b_terms) do
            {a_terms, b_terms}
          else
            {b_terms, a_terms}
          end

        _ ->
          {a_terms, b_terms}
      end

    case tableaux(left_side ++ rest, definitions, state, parameters) do
      {:incomplete, clause, constr} ->
        {:incomplete, clause, constr}

      {:open, res_clause, constr} ->
        {:open, res_clause, constr}

      {:closed, unif_checkpoints} ->
        # Option for concurrency here, as unification checkpoints can be checked in parallel
        case unif_checkpoints do
          [] ->
            # closed without substitutions or constraints
            tableaux(right_side ++ rest, definitions, state, parameters)

          _ ->
            # Try checkpoints on right branch and propagate up
            {new_checkpoints, last_open} =
              Enum.reduce_while(unif_checkpoints, {[], nil}, fn unif_checkpoint(
                                                                  substs: substitutions,
                                                                  constrs: remaining
                                                                ),
                                                                {checkpoints, prev_open} ->
                new_rest = apply_subst(substitutions, rest)
                new_clause = apply_subst(substitutions, state.clause)
                new_right_side = apply_subst(substitutions, right_side)

                case tableaux(
                       new_right_side ++ new_rest,
                       definitions,
                       %State{state | clause: new_clause, constraints: remaining},
                       parameters
                     ) do
                  {:closed, new_cpts} ->
                    added_cpts =
                      if new_cpts == [] do
                        [unif_checkpoint(substs: substitutions, constrs: remaining)]
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

  @spec tableaux([HOL.Data.hol_term()], definitions(), State.t(), Parameters.t()) ::
          tableaux_res()
  defp tableaux([], _, %State{} = state, _) do
    if state.incomplete? do
      # empty formulas and incomplete flag -> rules exhausted while max_inst met
      Logger.notice("OPEN: no formulas remain, exceeded maximum instantiation limit")
      {:incomplete, state.clause, state.constraints}
    else
      Logger.notice("OPEN: no formulas remain")
      {:open, state.clause, state.constraints}
    end
  end

  defp tableaux(
         [current_formula | rest],
         definitions,
         %State{} = state,
         %Parameters{} = parameters
       ) do
    "Processing formula #{PrettyPrint.pp_term(current_formula)}" |> Logger.notice()

    formula =
      if parameters.canonicalize do
        f = Rewriting.canonicalize(current_formula)
        "Canonicalized: #{PrettyPrint.pp_term(f)}" |> Logger.notice()
        f
      else
        current_formula
      end

    rest_pp = Enum.map(rest, &PrettyPrint.pp_term/1) |> inspect()
    ("Rest: " <> rest_pp) |> Logger.info()
    clause_pp = Enum.map(state.clause, &PrettyPrint.pp_term/1) |> inspect()
    ("Clause: " <> clause_pp) |> Logger.info()

    case formula do
      #################################################################################
      # BOOLEAN CONSTANTS
      #################################################################################

      true_term() ->
        Logger.notice("applying \"⊤\"")
        tableaux(rest, definitions, state, parameters)

      negated(true_term()) ->
        Logger.notice("applying \"¬⊤\" (closing branch)")
        {:closed, []}

      false_term() ->
        Logger.notice("applying \"⊥\" (closing branch)")
        {:closed, []}

      negated(false_term()) ->
        Logger.notice("applying \"¬⊥\"")
        tableaux(rest, definitions, state, parameters)

      #################################################################################
      # ATOMS
      #################################################################################

      # atomic formula with free variable head
      hol_term(head: declaration(kind: :fv), type: type_o()) ->
        Logger.notice("applying \"Atom\"")
        handle_atom(formula, :pos, rest, definitions, state, parameters)

      # negated atomic formula with free variable head
      negated(hol_term(head: declaration(kind: :fv))) ->
        Logger.notice("applying \"Atom\"")
        handle_atom(formula, :neg, rest, definitions, state, parameters)

      # non-unfolded definition
      hol_term(head: declaration(kind: :co, name: name), args: args, type: type_o())
      when is_map_key(definitions, name) ->
        Logger.notice("unfolding definition for \"#{name}\"")

        equality(_id, def_body) = Map.get(definitions, name)

        unfolded_term =
          Enum.reduce(args, def_body, fn arg, acc ->
            mk_appl_term(acc, arg)
          end)

        tableaux([unfolded_term | rest], definitions, state, parameters)

      # negated non-unfolded definition
      negated(hol_term(head: declaration(kind: :co, name: name), args: args))
      when is_map_key(definitions, name) ->
        Logger.notice("unfolding negated definition for \"#{name}\"")

        equality(_id, def_body) = Map.get(definitions, name)

        unfolded_inner =
          Enum.reduce(args, def_body, fn arg, acc ->
            mk_appl_term(acc, arg)
          end)

        tableaux([syn_negate(unfolded_inner) | rest], definitions, state, parameters)

      # atomic formula with constant as head (no logical connective)
      hol_term(head: declaration(kind: :co, name: name), type: type_o())
      when name not in signature_symbols() ->
        Logger.notice("applying \"Atom\"")
        handle_atom(formula, :pos, rest, definitions, state, parameters)

      # negated atomic formula with constant as head (no logical connective)
      negated(hol_term(head: declaration(kind: :co, name: name)))
      when name not in signature_symbols() ->
        Logger.notice("applying \"Atom\"")
        handle_atom(formula, :neg, rest, definitions, state, parameters)

      #################################################################################
      # DOUBLE NEGATION
      #################################################################################

      # double negation
      negated(negated(a)) ->
        Logger.notice("applying \"¬¬\"")
        tableaux([a | rest], definitions, state, parameters)

      #################################################################################
      # EQUALITY
      #################################################################################

      ################################## REFLEXIVITY ##################################

      # reflexivity of equality -> a=a is always true
      equality(a, a) ->
        Logger.notice("applying \"=r\"")
        tableaux(rest, definitions, state, parameters)

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

        tableaux([subproblems | rest], definitions, state, parameters)

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

        tableaux([subproblems | rest], definitions, state, parameters)

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

        tableaux([subproblems | rest], definitions, state, parameters)

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

        tableaux([subproblems | rest], definitions, state, parameters)

      ############################# TYPED EQUALITY SYMBOLS ############################

      # equality (type o) -> transform to equivalence
      typed_equality(a, b, type_o()) ->
        Logger.notice("applying \"=o\"")
        equiv = equivalent_term() |> mk_appl_term(a) |> mk_appl_term(b)
        tableaux([equiv | rest], definitions, state, parameters)

      # negated equality (type o)
      negated(typed_equality(a, b, type_o())) ->
        Logger.notice("applying \"¬=o\"")
        eq = equivalent_term() |> mk_appl_term(a) |> mk_appl_term(b)
        neg_eq = neg_term() |> mk_appl_term(eq)
        tableaux([neg_eq | rest], definitions, state, parameters)

      # equality (other atomic types) -> Leibnitz equality
      typed_equality(a, b, type(goal: g, args: [])) when is_atom(g) ->
        t = type(goal: g, args: [])

        if unknown_type?(t) do
          Logger.notice("applying \"Atom\"")
          handle_atom(formula, :pos, rest, definitions, state, parameters)
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

          tableaux([quant | rest], definitions, state, parameters)
        end

      # negated equality (other atomic types) -> negated Leibnitz equality
      negated(typed_equality(a, b, type(goal: g, args: []))) when is_atom(g) ->
        t = type(goal: g, args: [])

        if unknown_type?(t) do
          Logger.notice("applying \"Atom\"")
          handle_atom(formula, :neg, rest, definitions, state, parameters)
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

          tableaux([neg_quant | rest], definitions, state, parameters)
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

        tableaux([quant | rest], definitions, state, parameters)

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

        tableaux([neg_quant | rest], definitions, state, parameters)

      #################################################################################
      # LOGICAL CONNECTIVES
      #################################################################################

      # disjunction
      disjunction(a, b) ->
        Logger.notice("applying \"∨\"")
        branch(a, b, rest, definitions, state, parameters)

      # negated disjunction
      negated(disjunction(a, b)) ->
        Logger.notice("applying \"¬∨\"")
        tableaux([sem_negate(a), sem_negate(b) | rest], definitions, state, parameters)

      # conjunction
      conjunction(a, b) ->
        Logger.notice("applying \"∧\"")
        tableaux([a, b | rest], definitions, state, parameters)

      # negated conjunction
      negated(conjunction(a, b)) ->
        Logger.notice("applying \"¬∧\"")
        branch(sem_negate(a), sem_negate(b), rest, definitions, state, parameters)

      # implication
      implication(a, b) ->
        Logger.notice("applying \"⊃\"")
        branch(sem_negate(a), b, rest, definitions, state, parameters)

      # negated implication
      negated(implication(a, b)) ->
        Logger.notice("applying \"¬⊃\"")
        tableaux([a, sem_negate(b) | rest], definitions, state, parameters)

      # equivalence
      equivalence(a, b) ->
        Logger.notice("applying \"≡\"")
        branch([a, b], [sem_negate(a), sem_negate(b)], rest, definitions, state, parameters)

      # negated equivalence
      negated(equivalence(a, b)) ->
        Logger.notice("applying \"¬≡\"")
        branch([sem_negate(a), b], [a, sem_negate(b)], rest, definitions, state, parameters)

      #################################################################################
      # QUANTORS
      #################################################################################

      # universal quantification -> fresh variable (can be repeated!)
      universal_quantification(body) ->
        Logger.notice("applying \"Π\"")
        count = Map.get(state.inst_count, formula, 0)

        if count < parameters.max_instantiations do
          type(args: [type]) = get_term_type(body)
          new_inst_count = Map.put(state.inst_count, formula, count + 1)
          fresh_variable = mk_term(mk_uniqe_var(type))
          fresh_instance = mk_appl_term(body, fresh_variable)

          tableaux(
            [fresh_instance | rest] ++ [formula],
            definitions,
            %State{state | inst_count: new_inst_count},
            parameters
          )
        else
          # skip the universal quantification - upper bound of instantiations reached
          Logger.info("instantiation limit exceeded")
          tableaux(rest, definitions, %State{state | incomplete?: true}, parameters)
        end

      # negated universal quantification -> skolemization
      negated(universal_quantification(body)) ->
        Logger.notice("applying \"¬Π\"")

        type(args: [type]) = get_term_type(body)

        tableaux(
          [sem_negate(mk_appl_term(body, mk_new_skolem_term(get_fvars(body), type))) | rest],
          definitions,
          state,
          parameters
        )

      # existential quantification -> skolemization
      existential_quantification(body) ->
        Logger.notice("applying \"Σ\"")

        type(args: [type]) = get_term_type(body)

        tableaux(
          [mk_appl_term(body, mk_new_skolem_term(get_fvars(body), type)) | rest],
          definitions,
          state,
          parameters
        )

      # negated existential quantification -> fresh variable (can be repeated!)
      negated(existential_quantification(body)) ->
        Logger.notice("applying \"¬Σ\"")
        count = Map.get(state.inst_count, formula, 0)

        if count < parameters.max_instantiations do
          type(args: [type]) = get_term_type(body)
          new_inst_count = Map.put(state.inst_count, formula, count + 1)
          fresh_variable = mk_term(mk_uniqe_var(type))
          fresh_instance = syn_negate(mk_appl_term(body, fresh_variable))

          tableaux(
            [fresh_instance | rest] ++ [formula],
            definitions,
            %State{state | inst_count: new_inst_count},
            parameters
          )
        else
          # skip the negated existential quantification - upper bound of instantiations reached
          Logger.info("instantiation limit exceeded")
          tableaux(rest, definitions, %State{state | incomplete?: true}, parameters)
        end
    end
  end

  defp as_assignment({:closed, _}) do
    "All branches closed -> unsatisfiable" |> Logger.notice()
    {:unsat, :closed}
  end

  defp as_assignment({:open, clause, constraints}) do
    "Some branches still open -> countermodel exists" |> Logger.notice()

    {:sat, %Model{assignments: clause, constraints: constraints}}
  end

  defp as_assignment({:incomplete, clause, constraints}) do
    "Result unknown due to prover incompleteness" |> Logger.notice()

    {:unknown, %Model{assignments: clause, constraints: constraints}, :incomplete}
  end

  defp as_assignment(:timeout), do: {:unknown, nil, :timeout}
end
