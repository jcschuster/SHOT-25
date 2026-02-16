defmodule THOUTest do
  use ExUnit.Case
  doctest THOU

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions

  describe "THOU API delegation - sat/1" do
    test "delegates sat/1 to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      result = THOU.sat(p)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end

    test "handles list of formulas" do
      p = mk_const_term("p", mk_type(:o, []))
      result = THOU.sat([p])

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end
  end

  describe "THOU API delegation - sat/2" do
    test "delegates sat/2 with definitions to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      definitions = %{}
      result = THOU.sat(p, definitions)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end
  end

  describe "THOU API delegation - sat/3" do
    test "delegates sat/3 with options to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      definitions = %{}
      result = THOU.sat(p, definitions, timeout: 5000)

      assert is_tuple(result)
      assert elem(result, 0) in [:sat, :unsat, :unknown]
    end
  end

  describe "THOU API delegation - prove/1" do
    test "delegates prove/1 to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      result = THOU.prove(p)

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end

  describe "THOU API delegation - prove/2" do
    test "delegates prove/2 with assumptions to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      result = THOU.prove(p, [q])

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end

  describe "THOU API delegation - prove/3" do
    test "delegates prove/3 with definitions to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      definitions = %{}
      result = THOU.prove(p, [q], definitions)

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end

  describe "THOU API delegation - prove/4" do
    test "delegates prove/4 with options to Prover" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      definitions = %{}
      result = THOU.prove(p, [q], definitions, timeout: 5000)

      assert is_tuple(result)
      assert elem(result, 0) in [:valid, :countersat, :unknown]
    end
  end
end
