defmodule THOU.HOL.Definitions do
  @moduledoc groups: [:Signature, :Types, :Constants, :Terms]
  @moduledoc """
  Contains macros for HOL connectives, constants and terms facilitating pattern
  matching and term construction. Note that more types, constants and terms can
  be introduced via the `HOL` library
  (https://hexdocs.pm/hol/api-reference.html).
  """

  import HOL.Data

  # The use of macros in combination with module attributes messes up the type
  # checking, so we ignore the warnings.
  @dialyzer :no_contracts

  @doc group: :Signature
  @doc """
  Returns a list of the names of the signature symbols in the logic.

  ## Example

      iex> signature_symbols()
      ["⊤", "⊥", "¬", "∨", "∧", "⊃", "≡", "Π", "Σ", "="]
  """
  defmacro signature_symbols, do: Macro.escape(["⊤", "⊥", "¬", "∨", "∧", "⊃", "≡", "Π", "Σ", "="])

  #############################################################################
  # TYPES
  #############################################################################

  @type_i type(goal: :i)

  @type_o type(goal: :o)

  @type_oo type(goal: :o, args: [@type_o])
  @type_ooo type(goal: :o, args: [@type_o, @type_o])

  @type_io type(goal: :o, args: [@type_i])
  @type_io_o type(goal: :o, args: [@type_io])

  @doc group: :Types
  @doc """
  Base type for booleans. Represents true or false.
  """
  @spec type_o() :: HOL.Data.type()
  defmacro type_o, do: Macro.escape(@type_o)

  @doc group: :Types
  @doc """
  Type for symbols of type o⇾o, e.g. unary connectives like negateion.
  """
  @spec type_oo() :: HOL.Data.type()
  defmacro type_oo, do: Macro.escape(@type_oo)

  @doc group: :Types
  @doc """
  Type for symbols of type o⇾o⇾o, e.g. binary connectives like conjunction.
  """
  @spec type_ooo() :: HOL.Data.type()
  defmacro type_ooo, do: Macro.escape(@type_ooo)

  @doc group: :Types
  @doc """
  Base type for individuals.
  """
  @spec type_i() :: HOL.Data.type()
  defmacro type_i, do: Macro.escape(@type_i)

  @doc group: :Types
  @doc """
  Type for sets of individuals.
  """
  @spec type_io() :: HOL.Data.type()
  defmacro type_io, do: Macro.escape(@type_io)

  @doc group: :Types
  @doc """
  Type for sets of sets of individuals, or predicates over sets of individuals.
  """
  @spec type_io_o() :: HOL.Data.type()
  defmacro type_io_o, do: Macro.escape(@type_io_o)

  #############################################################################
  # CONSTANTS
  #############################################################################

  @true_const declaration(kind: :co, name: "⊤", type: @type_o)
  @false_const declaration(kind: :co, name: "⊥", type: @type_o)

  @neg_const declaration(kind: :co, name: "¬", type: @type_oo)
  @or_const declaration(kind: :co, name: "∨", type: @type_ooo)
  @and_const declaration(kind: :co, name: "∧", type: @type_ooo)
  @implies_const declaration(kind: :co, name: "⊃", type: @type_ooo)
  @equivalent_const declaration(kind: :co, name: "≡", type: @type_ooo)

  @doc group: :Constants
  @doc """
  Constant representing truth.
  """
  @spec true_const() :: HOL.Data.declaration()
  defmacro true_const, do: Macro.escape(@true_const)

  @doc group: :Constants
  @doc """
  Constant representing falsity.
  """
  @spec false_const() :: HOL.Data.declaration()
  defmacro false_const, do: Macro.escape(@false_const)

  @doc group: :Constants
  @doc """
  Constant representing the negation operator.
  """
  @spec neg_const() :: HOL.Data.declaration()
  defmacro neg_const, do: Macro.escape(@neg_const)

  @doc group: :Constants
  @doc """
  Constant representing the disjunction operator.
  """
  @spec or_const() :: HOL.Data.declaration()
  defmacro or_const, do: Macro.escape(@or_const)

  @doc group: :Constants
  @doc """
  Constant representing the conjunction operator.
  """
  @spec and_const() :: HOL.Data.declaration()
  defmacro and_const, do: Macro.escape(@and_const)

  @doc group: :Constants
  @doc """
  Constant representing the implication operator.
  """
  @spec implies_const() :: HOL.Data.declaration()
  defmacro implies_const, do: Macro.escape(@implies_const)

  @doc group: :Constants
  @doc """
  Constant representing the equivalence operator.
  """
  @spec equivalent_const() :: HOL.Data.declaration()
  defmacro equivalent_const, do: Macro.escape(@equivalent_const)

  @doc group: :Constants
  @doc """
  Constant representing equality over instances of the given type.
  """
  @spec equals_const(HOL.Data.type()) :: HOL.Data.declaration()
  defmacro equals_const(type) do
    quote do
      declaration(
        kind: :co,
        name: "=",
        type: type(goal: :o, args: [unquote(type), unquote(type)])
      )
    end
  end

  @doc group: :Constants
  @doc """
  Constant representing the pi operator (universal quantification) over the
  given domain type (must have goal type o).
  """
  @spec pi_const(HOL.Data.type()) :: HOL.Data.declaration()
  defmacro pi_const(type) do
    quote do
      declaration(
        kind: :co,
        name: "Π",
        type: type(goal: :o, args: [unquote(type)])
      )
    end
  end

  @doc group: :Constants
  @doc """
  Constant representing the sigma operator (existential quantification) over
  the given domain type (must have goal type o).
  """
  @spec sigma_const(HOL.Data.type()) :: HOL.Data.declaration()
  defmacro sigma_const(type) do
    quote do
      declaration(
        kind: :co,
        name: "Σ",
        type: type(goal: :o, args: [unquote(type)])
      )
    end
  end

  #############################################################################
  # TERMS
  #############################################################################

  defmacrop unary_hol_term_oo(head) do
    quote do
      hol_term(
        bvars: [declaration(kind: :bv, name: 1, type: @type_o)],
        head: unquote(head),
        args: [
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 1, type: @type_o),
            args: [],
            type: @type_o,
            fvars: [],
            max_num: 0
          )
        ],
        type: @type_oo,
        fvars: [],
        max_num: 1
      )
    end
  end

  defmacrop binary_hol_term_ooo(head) do
    quote do
      hol_term(
        bvars: [
          declaration(kind: :bv, name: 2, type: @type_o),
          declaration(kind: :bv, name: 1, type: @type_o)
        ],
        head: unquote(head),
        args: [
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 2, type: @type_o),
            args: [],
            type: @type_o,
            fvars: [],
            max_num: 0
          ),
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 1, type: @type_o),
            args: [],
            type: @type_o,
            fvars: [],
            max_num: 0
          )
        ],
        type: @type_ooo,
        fvars: [],
        max_num: 2
      )
    end
  end

  ############################## FROM SIGNATURE ###############################

  @doc group: :Terms
  @doc """
  A term representation of truth.
  """
  @spec true_term() :: HOL.Data.hol_term()
  defmacro true_term,
    do:
      Macro.escape(
        hol_term(
          bvars: [],
          head: @true_const,
          args: [],
          type: @type_o,
          fvars: [],
          max_num: 0
        )
      )

  @doc group: :Terms
  @doc """
  A term representation of falsity.
  """
  @spec false_term() :: HOL.Data.hol_term()
  defmacro false_term,
    do:
      Macro.escape(
        hol_term(
          bvars: [],
          head: @false_const,
          args: [],
          type: @type_o,
          fvars: [],
          max_num: 0
        )
      )

  @doc group: :Terms
  @doc """
  A term representation of the negation operator.
  """
  @spec neg_term() :: HOL.Data.hol_term()
  defmacro neg_term,
    do: Macro.escape(unary_hol_term_oo(@neg_const))

  @doc group: :Terms
  @doc """
  A term representation of the disjunction operator.
  """
  @spec or_term() :: HOL.Data.hol_term()
  defmacro or_term,
    do: Macro.escape(binary_hol_term_ooo(@or_const))

  @doc group: :Terms
  @doc """
  A term representation of the conjunction operator.
  """
  @spec and_term() :: HOL.Data.hol_term()
  defmacro and_term,
    do: Macro.escape(binary_hol_term_ooo(@and_const))

  @doc group: :Terms
  @doc """
  A term representation of the implication operator.
  """
  @spec implies_term() :: HOL.Data.hol_term()
  defmacro implies_term,
    do: Macro.escape(binary_hol_term_ooo(@implies_const))

  @doc group: :Terms
  @doc """
  A term representation of the equivalence operator.
  """
  @spec equivalent_term() :: HOL.Data.hol_term()
  defmacro equivalent_term,
    do: Macro.escape(binary_hol_term_ooo(@equivalent_const))

  @doc group: :Terms
  @doc """
  A term representation of the equality operator operating on the given type.
  """
  @spec equals_term(HOL.Data.type()) :: HOL.Data.hol_term()
  defmacro equals_term(t) do
    quote do
      hol_term(
        bvars: [
          declaration(kind: :bv, name: 2, type: unquote(t)),
          declaration(kind: :bv, name: 1, type: unquote(t))
        ],
        head: equals_const(unquote(t)),
        args: [
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 2, type: unquote(t)),
            args: [],
            type: unquote(t),
            fvars: [],
            max_num: 0
          ),
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 1, type: unquote(t)),
            args: [],
            type: unquote(t),
            fvars: [],
            max_num: 0
          )
        ],
        type: type(goal: :o, args: [unquote(t), unquote(t)]),
        fvars: [],
        max_num: 2
      )
    end
  end

  @doc group: :Terms
  @doc """
  A term representation of the pi operator (universal quantification) for the
  given domain type (must have goal type o).
  """
  @spec sigma_term(HOL.Data.type()) :: HOL.Data.hol_term()
  defmacro pi_term(t) do
    quote do
      hol_term(
        bvars: [
          declaration(kind: :bv, name: 1, type: unquote(t))
        ],
        head: pi_const(unquote(t)),
        args: [
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 1, type: unquote(t)),
            args: [],
            type: unquote(t),
            fvars: [],
            max_num: 0
          )
        ],
        type: type(goal: :o, args: [unquote(t)]),
        fvars: [],
        max_num: 1
      )
    end
  end

  @doc group: :Terms
  @doc """
  A term representation of the sigma operator (existential quantification) for
  the given domain type (must have goal type o).
  """
  @spec sigma_term(HOL.Data.type()) :: HOL.Data.hol_term()
  defmacro sigma_term(t) do
    quote do
      hol_term(
        bvars: [
          declaration(kind: :bv, name: 1, type: unquote(t))
        ],
        head: sigma_const(unquote(t)),
        args: [
          hol_term(
            bvars: [],
            head: declaration(kind: :bv, name: 1, type: unquote(t)),
            args: [],
            type: unquote(t),
            fvars: [],
            max_num: 0
          )
        ],
        type: type(goal: :o, args: [unquote(t)]),
        fvars: [],
        max_num: 1
      )
    end
  end

  ################################# DEFINED ###################################

  @doc group: :Terms
  @doc """
  Term representation of the reverse implication operator. Rewrites the term in
  terms of (normal) implication.
  """
  @spec implied_by_term() :: HOL.Data.hol_term()
  defmacro implied_by_term,
    do:
      Macro.escape(
        hol_term(
          bvars: [
            declaration(kind: :bv, name: 2, type: @type_o),
            declaration(kind: :bv, name: 1, type: @type_o)
          ],
          head: @implies_const,
          args: [
            hol_term(
              bvars: [],
              head: declaration(kind: :bv, name: 1, type: @type_o),
              args: [],
              type: @type_o,
              fvars: [],
              max_num: 0
            ),
            hol_term(
              bvars: [],
              head: declaration(kind: :bv, name: 2, type: @type_o),
              args: [],
              type: @type_o,
              fvars: [],
              max_num: 0
            )
          ],
          type: @type_ooo,
          fvars: [],
          max_num: 2
        )
      )

  @doc group: :Terms
  @doc """
  Term representation of the XOR-operator. Rewrites the term in terms of
  negated equivalence.
  """
  @spec xor_term() :: HOL.Data.hol_term()
  defmacro xor_term,
    do:
      Macro.escape(
        hol_term(
          bvars: [
            declaration(kind: :bv, name: 2, type: @type_o),
            declaration(kind: :bv, name: 1, type: @type_o)
          ],
          head: @neg_const,
          args: [
            hol_term(
              bvars: [],
              head: equivalent_const(),
              args: [
                hol_term(
                  bvars: [],
                  head: declaration(kind: :bv, name: 2, type: @type_o),
                  args: [],
                  type: @type_o,
                  fvars: [],
                  max_num: 0
                ),
                hol_term(
                  bvars: [],
                  head: declaration(kind: :bv, name: 1, type: @type_o),
                  args: [],
                  type: @type_o,
                  fvars: [],
                  max_num: 0
                )
              ],
              type: @type_o,
              fvars: [],
              max_num: 0
            )
          ],
          type: @type_ooo,
          fvars: [],
          max_num: 2
        )
      )

  @doc group: :Terms
  @doc """
  Term representation of the NAND-operator. Rewrites the term in terms of
  negated conjunction.
  """
  @spec nand_term() :: HOL.Data.hol_term()

  defmacro nand_term,
    do:
      Macro.escape(
        hol_term(
          bvars: [
            declaration(kind: :bv, name: 2, type: @type_o),
            declaration(kind: :bv, name: 1, type: @type_o)
          ],
          head: @neg_const,
          args: [
            hol_term(
              bvars: [],
              head: and_const(),
              args: [
                hol_term(
                  bvars: [],
                  head: declaration(kind: :bv, name: 2, type: @type_o),
                  args: [],
                  type: @type_o,
                  fvars: [],
                  max_num: 0
                ),
                hol_term(
                  bvars: [],
                  head: declaration(kind: :bv, name: 1, type: @type_o),
                  args: [],
                  type: @type_o,
                  fvars: [],
                  max_num: 0
                )
              ],
              type: @type_o,
              fvars: [],
              max_num: 0
            )
          ],
          type: @type_ooo,
          fvars: [],
          max_num: 2
        )
      )

  @doc group: :Terms
  @doc """
  Term representation of the NOR-operator. Rewrites the term in terms of
  negated disjunction.
  """
  @spec nor_term() :: HOL.Data.hol_term()

  defmacro nor_term,
    do:
      Macro.escape(
        hol_term(
          bvars: [
            declaration(kind: :bv, name: 2, type: @type_o),
            declaration(kind: :bv, name: 1, type: @type_o)
          ],
          head: @neg_const,
          args: [
            hol_term(
              bvars: [],
              head: or_const(),
              args: [
                hol_term(
                  bvars: [],
                  head: declaration(kind: :bv, name: 2, type: @type_o),
                  args: [],
                  type: @type_o,
                  fvars: [],
                  max_num: 0
                ),
                hol_term(
                  bvars: [],
                  head: declaration(kind: :bv, name: 1, type: @type_o),
                  args: [],
                  type: @type_o,
                  fvars: [],
                  max_num: 0
                )
              ],
              type: @type_o,
              fvars: [],
              max_num: 0
            )
          ],
          type: @type_ooo,
          fvars: [],
          max_num: 2
        )
      )

  @doc group: :Terms
  @doc """
  Term representation of the negated equality operator operating on the given type.
  """
  @spec not_equals_term(HOL.Data.type()) :: HOL.Data.hol_term()
  defmacro not_equals_term(t) do
    quote do
      hol_term(
        bvars: [
          declaration(kind: :bv, name: 2, type: unquote(t)),
          declaration(kind: :bv, name: 1, type: unquote(t))
        ],
        head: neg_const(),
        args: [
          hol_term(
            bvars: [],
            head: equals_const(unquote(t)),
            args: [
              hol_term(
                bvars: [],
                head: declaration(kind: :bv, name: 2, type: unquote(t)),
                args: [],
                type: unquote(t),
                fvars: [],
                max_num: 0
              ),
              hol_term(
                bvars: [],
                head: declaration(kind: :bv, name: 1, type: unquote(t)),
                args: [],
                type: unquote(t),
                fvars: [],
                max_num: 0
              )
            ],
            type: type(goal: :o, args: [unquote(t), unquote(t)]),
            fvars: [],
            max_num: 0
          )
        ],
        type: type(goal: :o, args: [unquote(t), unquote(t)]),
        fvars: [],
        max_num: 2
      )
    end
  end
end
