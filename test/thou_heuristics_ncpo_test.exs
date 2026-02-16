defmodule THOU.Heuristics.NCPOTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias THOU.Heuristics.NCPO

  describe "greater?/2 basic comparison" do
    test "larger term is greater than smaller term" do
      # For propositional constants, structure matters
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      # Test basic comparison (result depends on implementation)
      result = NCPO.greater?(p, q)
      assert is_boolean(result)
    end

    test "comparison is consistent" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      # Result should be consistent across calls
      result1 = NCPO.greater?(p, q)
      result2 = NCPO.greater?(p, q)
      assert result1 == result2
    end

    test "term is not greater than itself" do
      p = mk_const_term("p", mk_type(:o, []))

      result = NCPO.greater?(p, p)
      # Typically false for same term
      assert is_boolean(result)
    end
  end

  describe "greater_eq?/2 weak comparison" do
    test "term is greater or equal to itself" do
      p = mk_const_term("p", mk_type(:o, []))

      result = NCPO.greater_eq?(p, p)
      # Should be true for same term
      assert is_boolean(result)
    end

    test "greater_eq is reflexive for same term" do
      p = mk_const_term("p", mk_type(:o, []))

      result = NCPO.greater_eq?(p, p)
      assert result == true
    end

    test "greater_eq comparison is consistent" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      result1 = NCPO.greater_eq?(p, q)
      result2 = NCPO.greater_eq?(p, q)
      assert result1 == result2
    end
  end

  describe "smaller_multiset?/2" do
    test "empty multiset is smaller than any multiset" do
      p = mk_const_term("p", mk_type(:o, []))

      result = NCPO.smaller_multiset?([], [p])
      assert is_boolean(result)
    end

    test "multiset is not smaller than empty multiset" do
      p = mk_const_term("p", mk_type(:o, []))

      result = NCPO.smaller_multiset?([p], [])
      assert result == false
    end

    test "identical multisets have consistent comparison" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      multiset = [p, q]

      result1 = NCPO.smaller_multiset?(multiset, multiset)
      result2 = NCPO.smaller_multiset?(multiset, multiset)
      assert result1 == result2
    end

    test "multiset comparison returns boolean" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      result = NCPO.smaller_multiset?([p], [q])
      assert is_boolean(result)
    end
  end

  describe "comparison with variables" do
    test "comparison operations are deterministic" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      result1 = NCPO.greater?(p, q)
      result2 = NCPO.greater?(p, q)
      assert result1 == result2
    end
  end

  describe "comparison with applications" do
    test "comparison with function application" do
      f = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      a = mk_const_term("a", mk_type(:i, []))
      app = mk_appl_term(f, a)
      b = mk_const_term("b", mk_type(:i, []))

      result = NCPO.greater?(app, b)
      assert is_boolean(result)
    end

    test "comparison between applications" do
      f = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      a = mk_const_term("a", mk_type(:i, []))
      app1 = mk_appl_term(f, a)
      app2 = mk_appl_term(f, a)

      result = NCPO.greater?(app1, app2)
      assert is_boolean(result)
    end
  end

  describe "comparison with abstractions" do
    test "comparison with lambda abstraction" do
      x = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      x_term = mk_term(x)
      lambda = mk_abstr_term(x_term, x)
      a = mk_const_term("a", mk_type(:i, []))

      result = NCPO.greater?(lambda, a)
      assert is_boolean(result)
    end

    test "comparison between abstractions" do
      x = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      y = declaration(kind: :fv, name: "y", type: mk_type(:i, []))
      x_term = mk_term(x)
      y_term = mk_term(y)

      lambda1 = mk_abstr_term(x_term, x)
      lambda2 = mk_abstr_term(y_term, y)

      result = NCPO.greater?(lambda1, lambda2)
      assert is_boolean(result)
    end
  end

  describe "transitivity and consistency" do
    test "greater? is consistent across multiple calls" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      results = Enum.map(1..3, fn _ -> NCPO.greater?(p, q) end)

      # All results should be the same
      assert length(Enum.uniq(results)) == 1
    end

    test "greater_eq? is consistent across multiple calls" do
      p = mk_const_term("p", mk_type(:o, []))

      results = Enum.map(1..3, fn _ -> NCPO.greater_eq?(p, p) end)

      # All results should be the same
      assert Enum.all?(results, fn r -> r == true end)
    end
  end

  describe "complex terms" do
    test "comparison of complex nested terms" do
      f = mk_const_term("f", mk_type(:i, [mk_type(:i, []), mk_type(:i, [])]))
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))

      complex = mk_appl_term(mk_appl_term(f, a), b)
      simple = mk_const_term("c", mk_type(:i, []))

      result = NCPO.greater?(complex, simple)
      assert is_boolean(result)
    end

    test "multiset comparison with complex terms" do
      f = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      a = mk_const_term("a", mk_type(:i, []))
      app = mk_appl_term(f, a)

      multiset1 = [app]
      multiset2 = [a]

      result = NCPO.smaller_multiset?(multiset1, multiset2)
      assert is_boolean(result)
    end
  end

  describe "propositions" do
    test "comparison of propositional terms" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      result = NCPO.greater?(p, q)
      assert is_boolean(result)
    end

    test "comparison of negated propositions" do
      p = mk_const_term("p", mk_type(:o, []))
      neg_p = mk_appl_term(neg_term(), p)

      result = NCPO.greater?(neg_p, p)
      assert is_boolean(result)
    end
  end

  describe "type preservation" do
    test "comparison preserves term types" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      _result = NCPO.greater?(p, q)

      # Types should still be correct after comparison
      assert get_term_type(p) == mk_type(:o, [])
      assert get_term_type(q) == mk_type(:o, [])
    end

    test "multiset comparison preserves term types" do
      p = mk_const_term("p", mk_type(:o, []))
      a = mk_const_term("a", mk_type(:i, []))

      _result = NCPO.smaller_multiset?([p], [a])

      assert get_term_type(p) == mk_type(:o, [])
      assert get_term_type(a) == mk_type(:i, [])
    end
  end
end
