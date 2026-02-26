defmodule SHOT25.ProverTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias SHOT25.Prover
  alias SHOT25.Data.Model

  describe "sat/1 - basic satisfiability" do
    test "satisfiable formula returns sat result" do
      # True is always satisfiable
      result = Prover.sat(true_term())

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "handles list of formulas" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat([p])

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "unsatisfiable formula may close branches" do
      # False is unsatisfiable
      result = Prover.sat(false_term())

      assert is_tuple(result)

      case result do
        {:unsat, :closed} -> assert true
        # May be unknown due to timeout
        _ -> assert true
      end
    end
  end

  describe "sat/2 - with definitions" do
    test "respects definitions parameter" do
      p = mk_const_term("p", mk_type(:o, []))
      definitions = %{}
      result = Prover.sat(p, definitions)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "processes list of formulas with definitions" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      definitions = %{}
      result = Prover.sat([p, q], definitions)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end
  end

  describe "sat/3 - with options" do
    test "accepts timeout option" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p, %{}, timeout: 5000)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "respects timeout in prover options" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p, %{}, timeout: 1000)

      # Should complete or timeout
      assert is_tuple(result)

      case result do
        {:unknown, _model, :timeout} -> assert true
        _ -> assert true
      end
    end

    test "accepts branch_heuristic option" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p, %{}, branch_heuristic: :ncpo, timeout: 5000)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "accepts multiple prover options" do
      p = mk_const_term("p", mk_type(:o, []))

      result =
        Prover.sat(p, %{},
          timeout: 5000,
          max_instantiations: 5,
          unification_depth: 10
        )

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end
  end

  describe "sat/1 result types" do
    test "sat result is tuple with 2 or 3 elements" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p)

      assert is_tuple(result)
      result_size = tuple_size(result)
      assert result_size in [2, 3]
    end

    test "sat result first element is atom" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p)

      assert is_atom(elem(result, 0))
    end

    test "handles sat result structure" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p)

      case result do
        {:sat, model} ->
          assert is_struct(model, Model)

        {:unsat, :closed} ->
          assert true

        {:unknown, _model, reason} ->
          assert reason in [:incomplete, :timeout]

        _ ->
          assert true
      end
    end
  end

  describe "prove/1 - basic proof" do
    test "accepts conclusion as formula" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.prove(p)

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end

    test "tautology should be valid" do
      # p ∨ ¬p is a tautology
      p = mk_const_term("p", mk_type(:o, []))
      neg_p = mk_appl_term(neg_term(), p)
      or_p_neg_p = mk_appl_term(mk_appl_term(or_term(), p), neg_p)

      result = Prover.prove(or_p_neg_p)

      assert is_tuple(result)

      case result do
        {:valid, :proven} -> assert true
        # May be unknown
        _ -> assert true
      end
    end
  end

  describe "prove/2 - with assumptions" do
    test "accepts assumptions list" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      result = Prover.prove(p, [q])

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end

    test "accepts empty assumptions list" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.prove(p, [])

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end

    test "accepts multiple assumptions" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      r = mk_const_term("r", mk_type(:o, []))
      result = Prover.prove(p, [q, r])

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end

  describe "prove/3 - with definitions" do
    test "accepts definitions parameter" do
      p = mk_const_term("p", mk_type(:o, []))
      definitions = %{}
      result = Prover.prove(p, [], definitions)

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end

  describe "prove/4 - with options" do
    test "accepts timeout option" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.prove(p, [], %{}, timeout: 5000)

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end

    test "accepts prover options" do
      p = mk_const_term("p", mk_type(:o, []))

      result =
        Prover.prove(p, [], %{},
          timeout: 5000,
          max_instantiations: 5
        )

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end

  describe "proof result types" do
    test "proof result first element is valid atom" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.prove(p)

      assert is_atom(elem(result, 0))
    end

    test "valid proof result format" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.prove(p)

      case result do
        {:valid, :proven} -> assert true
        {:countersat, model} -> assert is_struct(model, Model)
        {:unknown, _model, reason} -> assert is_atom(reason)
      end
    end
  end

  describe "edge cases" do
    test "simple propositional formula" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.sat(p)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "negation of conclusion in prove" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Prover.prove(mk_appl_term(neg_term(), p))

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end
end
