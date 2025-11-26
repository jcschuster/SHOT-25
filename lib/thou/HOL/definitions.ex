defmodule THOU.HOL.Definitions do
  import HOL.Data

  defmacro signature_symbols, do: Macro.escape(["¬", "∨", "∧", "⊃", "≡", "Π", "Σ", "="])

  ############################################################
  # TYPES
  ############################################################

  @type_i type(goal: :i)
  @type_o type(goal: :o)

  @type_oo type(goal: :o, args: [@type_o])
  @type_ooo type(goal: :o, args: [@type_o, @type_o])

  @type_io type(goal: :o, args: [@type_i])
  @type_io_o type(goal: :o, args: [@type_io])

  defmacro type_o, do: Macro.escape(@type_o)
  defmacro type_i, do: Macro.escape(@type_i)
  defmacro type_io, do: Macro.escape(@type_io)
  defmacro type_io_o, do: Macro.escape(@type_io_o)

  ############################################################
  # CONSTANTS
  ############################################################

  @neg_const declaration(kind: :co, name: "¬", type: @type_oo)
  @or_const declaration(kind: :co, name: "∨", type: @type_ooo)
  @and_const declaration(kind: :co, name: "∧", type: @type_ooo)
  @implies_const declaration(kind: :co, name: "⊃", type: @type_ooo)
  @equivalent_const declaration(kind: :co, name: "≡", type: @type_ooo)

  defmacro neg_const, do: Macro.escape(@neg_const)
  defmacro or_const, do: Macro.escape(@or_const)
  defmacro and_const, do: Macro.escape(@and_const)
  defmacro implies_const, do: Macro.escape(@implies_const)
  defmacro equivalent_const, do: Macro.escape(@equivalent_const)

  defmacro equals_const(type) do
    quote do
      declaration(
        kind: :co,
        name: "=",
        type: type(goal: :o, args: [unquote(type), unquote(type)])
      )
    end
  end

  defmacro pi_const(type) do
    quote do
      declaration(
        kind: :co,
        name: "Π",
        type: type(goal: :o, args: [unquote(type)])
      )
    end
  end

  defmacro sigma_const(type) do
    quote do
      declaration(
        kind: :co,
        name: "Σ",
        type: type(goal: :o, args: [unquote(type)])
      )
    end
  end

  ############################################################
  # TERMS
  ############################################################

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

  defmacro neg_term,
    do: Macro.escape(unary_hol_term_oo(@neg_const))

  defmacro or_term,
    do: Macro.escape(binary_hol_term_ooo(@or_const))

  defmacro and_term,
    do: Macro.escape(binary_hol_term_ooo(@and_const))

  defmacro implies_term,
    do: Macro.escape(binary_hol_term_ooo(@implies_const))

  defmacro equivalent_term,
    do: Macro.escape(binary_hol_term_ooo(@equivalent_const))
end
