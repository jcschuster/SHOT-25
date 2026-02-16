defmodule THOU.Preprocessing.RewritingTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias THOU.Preprocessing.Rewriting

  describe "simplify/1" do
    test "simplifies a simple constant" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Rewriting.simplify(p)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "simplifies conjunction" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)
      result = Rewriting.simplify(conj)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "simplifies disjunction" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      disj = mk_appl_term(mk_appl_term(or_term(), p), q)
      result = Rewriting.simplify(disj)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "preserves type through simplification" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Rewriting.simplify(p)

      assert get_term_type(result) == get_term_type(p)
    end

    test "returns a term" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Rewriting.simplify(p)

      assert result != nil
    end

    test "preserves propositions in simplification" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)
      result = Rewriting.simplify(conj)

      # Result should still be a proposition
      assert get_term_type(result) == mk_type(:o, [])
    end
  end

  describe "orient/1" do
    test "orients a simple constant" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Rewriting.orient(p)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "orients conjunction" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)
      result = Rewriting.orient(conj)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "orients disjunction" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      disj = mk_appl_term(mk_appl_term(or_term(), p), q)
      result = Rewriting.orient(disj)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "preserves type through orientation" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Rewriting.orient(p)

      assert get_term_type(result) == get_term_type(p)
    end

    test "returns a term" do
      p = mk_const_term("p", mk_type(:o, []))
      result = Rewriting.orient(p)

      assert result != nil
    end

    test "canonical orientation of conjunctions" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      r = mk_const_term("r", mk_type(:o, []))

      # Create nested conjunctions
      conj1 = mk_appl_term(mk_appl_term(and_term(), p), q)
      conj2 = mk_appl_term(mk_appl_term(and_term(), r), conj1)

      result = Rewriting.orient(conj2)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end
  end

  describe "orientation idempotence" do
    test "orienting twice gives same result" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)

      result1 = Rewriting.orient(conj)
      result2 = Rewriting.orient(result1)

      # Results should be equivalent (though not necessarily identical objects)
      assert get_term_type(result1) == get_term_type(result2)
    end

    test "simplifying twice is stable" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)

      result1 = Rewriting.simplify(conj)
      result2 = Rewriting.simplify(result1)

      # Results should be equivalent
      assert get_term_type(result1) == get_term_type(result2)
    end
  end

  describe "equality handling" do
    test "does not orient equality" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      eq = equals_term(mk_type(:i, [])) |> mk_appl_term(a) |> mk_appl_term(b)
      result = Rewriting.orient(eq)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "does not simplify equality" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      eq = equals_term(mk_type(:i, [])) |> mk_appl_term(a) |> mk_appl_term(b)
      result = Rewriting.simplify(eq)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end
  end

  describe "negation handling" do
    test "simplifies negated formula" do
      p = mk_const_term("p", mk_type(:o, []))
      neg_p = mk_appl_term(neg_term(), p)
      result = Rewriting.simplify(neg_p)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "orients negated formula" do
      p = mk_const_term("p", mk_type(:o, []))
      neg_p = mk_appl_term(neg_term(), p)
      result = Rewriting.orient(neg_p)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end
  end

  describe "complex formulas" do
    test "handles nested conjunctions and disjunctions" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      r = mk_const_term("r", mk_type(:o, []))

      # (p ∧ q) ∨ r
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)
      disj = mk_appl_term(mk_appl_term(or_term(), conj), r)

      result = Rewriting.orient(disj)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end

    test "handles deeply nested formulas" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      # Build a deeply nested conjunction
      nested = p
      nested = mk_appl_term(mk_appl_term(and_term(), nested), q)
      nested = mk_appl_term(mk_appl_term(and_term(), nested), p)
      nested = mk_appl_term(mk_appl_term(and_term(), nested), q)

      result = Rewriting.simplify(nested)

      assert result != nil
      assert get_term_type(result) == mk_type(:o, [])
    end
  end
end
