defmodule SHOT25.PrettyPrintTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias SHOT25.PrettyPrint
  alias SHOT25.Data.Model

  describe "pp_assignment/1" do
    test "pretty prints empty MapSet" do
      empty_set = MapSet.new()
      result = PrettyPrint.pp_assignment(empty_set)

      assert is_binary(result)
      assert result == "[]"
    end

    test "pretty prints single positive literal" do
      p = mk_const_term("p", mk_type(:o, []))
      literals = MapSet.new([p])
      result = PrettyPrint.pp_assignment(literals)

      assert is_binary(result)
      assert String.contains?(result, "p")
      assert String.contains?(result, "true")
    end

    test "pretty prints single negated literal" do
      p = mk_const_term("p", mk_type(:o, []))
      neg_p = mk_appl_term(neg_term(), p)
      literals = MapSet.new([neg_p])
      result = PrettyPrint.pp_assignment(literals)

      assert is_binary(result)
      assert String.contains?(result, "p")
      assert String.contains?(result, "false")
    end

    test "pretty prints multiple literals mixed" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      neg_q = mk_appl_term(neg_term(), q)
      literals = MapSet.new([p, neg_q])
      result = PrettyPrint.pp_assignment(literals)

      assert is_binary(result)
      assert String.contains?(result, "p")
      assert String.contains?(result, "q")
    end
  end

  describe "pp_constraints/1" do
    test "pretty prints empty constraints list" do
      result = PrettyPrint.pp_constraints([])

      assert is_binary(result)
      assert result == "[]"
    end

    test "pretty prints single constraint" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      constraints = [{a, b}]
      result = PrettyPrint.pp_constraints(constraints)

      assert is_binary(result)
      assert String.contains?(result, "a")
      assert String.contains?(result, "b")
      assert String.contains?(result, "=")
    end

    test "pretty prints multiple constraints" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      c = mk_const_term("c", mk_type(:i, []))
      constraints = [{a, b}, {b, c}]
      result = PrettyPrint.pp_constraints(constraints)

      assert is_binary(result)
      assert String.contains?(result, "a")
      assert String.contains?(result, "b")
      assert String.contains?(result, "c")
    end
  end

  describe "pp_proof_result/1 - valid" do
    test "formats proven result" do
      result = PrettyPrint.pp_proof_result({:valid, :proven})

      assert is_binary(result)
      assert String.contains?(result, "Theorem")
      assert String.contains?(result, "Proof Found")
    end
  end

  describe "pp_proof_result/1 - countersat" do
    test "formats countersat result with model" do
      model = %Model{
        assignments: MapSet.new(),
        constraints: []
      }

      result = PrettyPrint.pp_proof_result({:countersat, model})

      assert is_binary(result)
      assert String.contains?(result, "CounterSatisfiable")
    end
  end

  describe "pp_proof_result/1 - unknown" do
    test "formats unknown result with timeout" do
      result = PrettyPrint.pp_proof_result({:unknown, nil, :timeout})

      assert is_binary(result)
      assert String.contains?(result, "Unknown")
      assert String.contains?(result, "timeout")
    end

    test "formats unknown result with incomplete" do
      result = PrettyPrint.pp_proof_result({:unknown, nil, :incomplete})

      assert is_binary(result)
      assert String.contains?(result, "Unknown")
      assert String.contains?(result, "incomplete")
    end

    test "formats unknown result with partial model" do
      model = %Model{
        assignments: MapSet.new(),
        constraints: []
      }

      result = PrettyPrint.pp_proof_result({:unknown, model, :incomplete})

      assert is_binary(result)
      assert String.contains?(result, "Unknown")
      assert String.contains?(result, "Partial Model")
    end
  end
end
