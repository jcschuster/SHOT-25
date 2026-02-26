defmodule SHOT25.UtilTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  import SHOT25.Util

  describe "mk_new_skolem_term/2" do
    test "creates a skolem term with correct type" do
      fvars = [declaration(kind: :fv, name: "x", type: mk_type(:i, []))]
      return_type = mk_type(:o, [])
      skolem_term = mk_new_skolem_term(fvars, return_type)

      assert skolem_term != nil
      assert get_term_type(skolem_term) == return_type
    end

    test "creates different skolem terms on successive calls" do
      fvars = [declaration(kind: :fv, name: "x", type: mk_type(:i, []))]
      return_type = mk_type(:o, [])
      skolem_term1 = mk_new_skolem_term(fvars, return_type)
      skolem_term2 = mk_new_skolem_term(fvars, return_type)

      assert skolem_term1 != skolem_term2
    end

    test "creates skolem term with multiple free variables" do
      fvars = [
        declaration(kind: :fv, name: "x", type: mk_type(:i, [])),
        declaration(kind: :fv, name: "y", type: mk_type(:i, []))
      ]

      return_type = mk_type(:o, [])
      skolem_term = mk_new_skolem_term(fvars, return_type)

      assert skolem_term != nil
      assert get_term_type(skolem_term) == return_type
    end

    test "creates skolem term with empty free variables" do
      fvars = []
      return_type = mk_type(:i, [])
      skolem_term = mk_new_skolem_term(fvars, return_type)

      assert skolem_term != nil
      assert get_term_type(skolem_term) == return_type
    end
  end

  describe "mk_leibniz_equal/2" do
    test "creates leibniz equality between identical types" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      leibniz_eq = mk_leibniz_equal(a, b)

      assert leibniz_eq != nil
      assert get_term_type(leibniz_eq) == mk_type(:o, [])
    end

    test "creates leibniz equality for constants" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      leibniz_eq = mk_leibniz_equal(p, q)

      assert leibniz_eq != nil
      assert get_term_type(leibniz_eq) == mk_type(:o, [])
    end

    test "creates leibniz equality for function types" do
      f = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      g = mk_const_term("g", mk_type(:i, [mk_type(:i, [])]))
      leibniz_eq = mk_leibniz_equal(f, g)

      assert leibniz_eq != nil
      assert get_term_type(leibniz_eq) == mk_type(:o, [])
    end
  end

  describe "mk_ext_equal/2" do
    test "creates extensional equality for function types" do
      f = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      g = mk_const_term("g", mk_type(:i, [mk_type(:i, [])]))
      ext_eq = mk_ext_equal(f, g)

      assert ext_eq != nil
      assert get_term_type(ext_eq) == mk_type(:o, [])
    end

    test "creates extensional equality for higher-order function types" do
      f = mk_const_term("f", mk_type(:o, [mk_type(:i, [])]))
      g = mk_const_term("g", mk_type(:o, [mk_type(:i, [])]))
      ext_eq = mk_ext_equal(f, g)

      assert ext_eq != nil
      assert get_term_type(ext_eq) == mk_type(:o, [])
    end
  end

  describe "negate/1 - single term" do
    test "negates a simple constant" do
      p = mk_const_term("p", mk_type(:o, []))
      negated = negate(p)

      assert negated != nil
      assert get_term_type(negated) == mk_type(:o, [])
    end

    test "negates a complex formula" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      conj = mk_appl_term(mk_appl_term(and_term(), p), q)
      negated = negate(conj)

      assert negated != nil
      assert get_term_type(negated) == mk_type(:o, [])
    end
  end

  describe "negate/1 - list of terms" do
    test "negates all terms in a list" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      terms = [p, q]
      negated = negate(terms)

      assert is_list(negated)
      assert length(negated) == 2
    end

    test "negates empty list returns empty list" do
      negated = negate([])
      assert negated == []
    end
  end

  describe "negate/1 - MapSet of terms" do
    test "negates all terms in a MapSet" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      terms = MapSet.new([p, q])
      negated = negate(terms)

      assert is_struct(negated, MapSet)
      assert MapSet.size(negated) == 2
    end
  end

  describe "lit_negate/1 - single term" do
    test "removes negation from negated term" do
      p = mk_const_term("p", mk_type(:o, []))
      neg_p = mk_appl_term(neg_term(), p)
      lit_neq = lit_negate(neg_p)

      assert lit_neq == p
    end

    test "adds negation to non-negated term" do
      p = mk_const_term("p", mk_type(:o, []))
      lit_neq = lit_negate(p)

      assert lit_neq != nil
      assert get_term_type(lit_neq) == mk_type(:o, [])
    end
  end

  describe "lit_negate/1 - list of terms" do
    test "toggles negation for all terms in a list" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      terms = [p, q]
      lit_neq = lit_negate(terms)

      assert is_list(lit_neq)
      assert length(lit_neq) == 2
    end
  end

  describe "apply_subst/2 - empty substitution" do
    test "applying empty substitution returns term unchanged" do
      p = mk_const_term("p", mk_type(:o, []))
      result = apply_subst([], p)

      assert result == p
    end

    test "applying empty substitution to list returns list unchanged" do
      p = mk_const_term("p", mk_type(:o, []))
      terms = [p]
      result = apply_subst([], terms)

      assert result == terms
    end
  end

  describe "apply_subst/2 - with substitution" do
    test "applies substitution to variable" do
      x = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      x_term = mk_term(x)
      a = mk_const_term("a", mk_type(:i, []))
      subst = make_substitution(x, a)

      result = apply_subst([subst], x_term)

      assert result == a
    end

    test "applies substitution to list of terms" do
      x = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      x_term = mk_term(x)
      a = mk_const_term("a", mk_type(:i, []))
      subst = make_substitution(x, a)

      result = apply_subst([subst], [x_term])

      assert is_list(result)
      assert Enum.at(result, 0) == a
    end

    test "applies substitution to MapSet of terms" do
      x = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      x_term = mk_term(x)
      a = mk_const_term("a", mk_type(:i, []))
      subst = make_substitution(x, a)
      terms = MapSet.new([x_term])

      result = apply_subst([subst], terms)

      assert is_struct(result, MapSet)
      assert MapSet.member?(result, a)
    end
  end

  # Helper function
  defp make_substitution(fvar, term) do
    import HOL.Substitution
    mk_substitution(fvar, term)
  end
end
