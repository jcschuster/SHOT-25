defmodule THOU.Tableaux.RuleMacros do
  @moduledoc """
  Macros for defining tableau rules declaratively.
  """

  @doc """
  Injects the required imports into the module.
  """
  @spec __using__(keyword()) :: Macro.t()
  defmacro __using__(_opts) do
    quote do
      import THOU.Tableaux.RuleMacros
      import BeHOLd.ClassicalHOL.Patterns
      require Logger
    end
  end

  @doc """
  Defines a rule for a tautology where the formula is discarded. Does not take
  a block; the pattern match itself implies a tautology.
  """
  @spec deftautology(String.t(), Macro.t()) :: Macro.t()
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
  @spec defcontradiction(String.t(), Macro.t()) :: Macro.t()
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
  @spec defalpha(String.t(), Macro.t(), do: Macro.t()) :: Macro.t()
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
  @spec defbeta(String.t(), Macro.t(), do: Macro.t()) :: Macro.t()
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
  Defines a Gamma rule (universal quantification). Injects `var!(fresh_term)`
  into the context of the block. Automatically handles instantiation limits and
  state updates.
  """
  @spec defgamma(String.t(), Macro.t(), Macro.t(), do: Macro.t()) :: Macro.t()
  defmacro defgamma(name, pattern, body, do: block) do
    quote do
      defp apply_rule(unquote(pattern) = formula, rest, defs, params, state) do
        Logger.notice("applying " <> unquote(name))
        tableau_state(inst_count: counts) = state
        count = Map.get(counts, formula, 0)

        if count < params.max_instantiations do
          type(args: [type]) = get_term_type(unquote(body))
          new_counts = Map.put(counts, formula, count + 1)

          var!(fresh_term) = mk_term(mk_uniqe_var(type))
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
  Defines a Delta rule (existential quantification). Injects
  `var!(skolem_term)` into the context of the block. Automatically finds free
  variables for the skolem term.
  """
  @spec defdelta(String.t(), Macro.t(), Macro.t(), do: Macro.t()) :: Macro.t()
  defmacro defdelta(name, pattern, body, do: block) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state) do
        Logger.notice("applying " <> unquote(name))
        type(args: [type]) = get_term_type(unquote(body))

        var!(skolem_term) = mk_new_skolem_term(get_fvars(unquote(body)), type)
        new_instance = unquote(block)
        tableau([new_instance | rest], defs, params, state)
      end
    end
  end

  @doc """
  Defines a rule which either corresponds to an alpha rule if the given type is
  not unknown and handling the given formula as an atom otherwise.
  """
  @spec defmaybeatomic(String.t(), Macro.t(), Macro.t(), Macro.t(), do: Macro.t()) ::
          Macro.t()
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
  @spec defunfold(String.t(), Macro.t(), do: Macro.t()) :: Macro.t()
  defmacro defunfold(label, pattern, do: block) do
    quote do
      defp apply_rule(unquote(pattern), rest, defs, params, state)
           when is_map_key(defs, var!(name)) do
        Logger.notice("unfolding " <> unquote(label) <> " for \"#{var!(name)}\"")

        equality(_id, def_body) = Map.get(defs, var!(name))
        var!(unfolded) = Enum.reduce(var!(args), def_body, &mk_appl_term(&2, &1))

        final_term = unquote(block)
        tableau([final_term | rest], defs, params, state)
      end
    end
  end

  @doc """
  Defines an atomic rule.
  """
  @spec defatomic(Macro.t(), Macro.t()) :: Macro.t()
  defmacro defatomic(pattern, polarity) do
    quote do
      defp apply_rule(unquote(pattern) = formula, rest, defs, params, state) do
        Logger.notice("applying \"Atom\" (#{unquote(polarity)})")
        handle_atom(formula, unquote(polarity), rest, defs, params, state)
      end
    end
  end
end
