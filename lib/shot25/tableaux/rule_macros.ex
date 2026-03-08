defmodule SHOT25.Tableaux.RuleMacros do
  @moduledoc """
  Macros for defining tableau rules declaratively.
  """

  @doc """
  Injects the required imports into the module.
  """
  @spec __using__(keyword()) :: Macro.t()
  defmacro __using__(_opts) do
    quote do
      import SHOT25.Tableaux.RuleMacros
      import BeHOLd.ClassicalHOL.Patterns
      require Logger
    end
  end

  @doc """
  Defines a rule for a tautology where the formula is discarded. Does not take
  a block; the pattern match itself implies a tautology.
  """
  defmacro deftautology(name, pattern) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state) do
        Logger.notice("applying " <> unquote(name) <> " (discarding formula)")
        tableau(rest, defs, params, state)
      end
    end
  end

  @doc """
  Defines a rule for branch closure due to an immediate contradiction. Does not
  take a block; the pattern match itself implies closure.
  """
  defmacro defcontradiction(name, pattern) do
    quote do
      defp apply_rule(unquote(pattern), _rest, _defs, _params, _state) do
        Logger.notice("applying " <> unquote(name) <> " (closing branch)")
        {:closed, []}
      end
    end
  end

  @doc """
  Defines an Alpha rule (linear decomposition). Expects a block that returns a
  list of new formulae to add to the goal stack.
  """
  defmacro defalpha(name, pattern, do: block) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state) do
        Logger.notice("applying" <> unquote(name))
        new_formulas = unquote(block)
        tableau(new_formulas ++ rest, defs, params, state)
      end
    end
  end

  @doc """
  Defines a Beta rule (branching decomposition). Expects a block that returns a
  tuple `{branch_a, branch_b}` (lists of formulae).
  """
  defmacro defbeta(name, pattern, do: block) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state) do
        Logger.notice("applying " <> unquote(name))
        {branch_a, branch_b} = unquote(block)
        branch(branch_a, branch_b, rest, defs, params, state)
      end
    end
  end

  @doc """
  Defines a Gamma rule (universal quantification). Expects the user to give a
  variable name for the fresh variable term. Automatically handles
  instantiation limits and state updates.
  """
  defmacro defgamma(name, pattern, body, fresh_term_var, do: block) do
    quote do
      defp apply_rule(unquote(pattern) = formula, rest, defs, params, state) do
        Logger.notice("applying " <> unquote(name))
        tableau_state(inst_count: counts) = state
        count = Map.get(counts, formula, 0)

        if count < params.max_instantiations do
          type(args: [type]) = get_term_type(unquote(body))
          new_counts = Map.put(counts, formula, count + 1)

          unquote(fresh_term_var) = mk_term(mk_uniqe_var(type))
          fresh_instance = unquote(block)
          new_state = tableau_state(state, inst_count: new_counts)
          tableau([fresh_instance | rest] ++ [formula], defs, params, new_state)
        else
          Logger.info("instantiation limit exceeded")
          new_state = tableau_state(state, incomplete?: true)
          tableau(rest, defs, params, new_state)
        end
      end
    end
  end

  @doc """
  Defines a Delta rule (existential quantification). Expects the user to give a
  variable name for the new skolem term. Automatically finds free variables for
  the skolem term.
  """
  defmacro defdelta(name, pattern, body, sk_var, do: block) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state) do
        Logger.notice("applying " <> unquote(name))
        type(args: [type]) = get_term_type(unquote(body))

        unquote(sk_var) = mk_new_skolem_term(get_fvars(unquote(body)), type)
        new_instance = unquote(block)
        tableau([new_instance | rest], defs, params, state)
      end
    end
  end

  @doc """
  Defines a rule which either corresponds to an alpha rule if the given type is
  not unknown and handling the given formula as an atom otherwise.
  """
  defmacro defmaybeatomic(name, pattern, type, polarity, do: block) do
    quote do
      defp apply_rule(unquote(pattern) = formula, rest, defs, params, state) do
        if unknown_type?(unquote(type)) do
          handle_atom(formula, unquote(polarity), rest, defs, params, state)
        else
          Logger.notice("applying " <> unquote(name))
          new_formulas = unquote(block)
          tableau(new_formulas ++ rest, defs, params, state)
        end
      end
    end
  end

  @doc """
  Defines a rule for unfolding a definition on head position. Includes a guard
  so that terms without a defined symbol at head position are skipped. Expects
  the pattern to introduce variables `name` and `args`.
  """
  defmacro defunfold(label, pattern, unfolded_var, do: block) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state)
           when is_map_key(defs, var!(name)) do
        Logger.notice("unfolding " <> unquote(label) <> " for \"#{var!(name)}\"")

        equality(_id, def_body) = Map.get(defs, var!(name))
        unquote(unfolded_var) = Enum.reduce(var!(args), def_body, &mk_appl_term(&2, &1))

        final_term = unquote(block)
        tableau([final_term | rest], defs, params, state)
      end
    end
  end

  @doc """
  Defines an atomic rule.
  """
  defmacro defatomic(pattern, polarity) do
    quote do
      defp apply_rule(unquote(pattern) = formula, rest, defs, params, state) do
        Logger.notice("applying \"Atom\" (#{unquote(polarity)})")
        handle_atom(formula, unquote(polarity), rest, defs, params, state)
      end
    end
  end
end
