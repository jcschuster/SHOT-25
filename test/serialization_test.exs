defmodule SHOT25.Preprocessing.SerializationTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias SHOT25.Preprocessing.Serialization

  describe "to_s_expr/1 - Term to S-Expression" do
    test "serializes a simple constant" do
      const = mk_const_term("p", mk_type(:o, []))
      result = Serialization.to_s_expr(const)
      assert is_binary(result)
      assert String.contains?(result, "p")
      assert String.contains?(result, "o")
    end

    test "serializes a variable" do
      var = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      term = mk_term(var)
      result = Serialization.to_s_expr(term)
      assert is_binary(result)
      assert String.contains?(result, "$VAR")
      assert String.contains?(result, "i")
    end

    test "serializes an abstraction (lambda)" do
      var = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      body_var = declaration(kind: :fv, name: "y", type: mk_type(:i, []))
      body = mk_term(body_var)
      abstr = mk_abstr_term(body, var)
      result = Serialization.to_s_expr(abstr)
      assert is_binary(result)
      assert String.contains?(result, "^")
    end

    test "serializes an application" do
      func = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      arg = mk_const_term("a", mk_type(:i, []))
      app = mk_appl_term(func, arg)
      result = Serialization.to_s_expr(app)
      assert is_binary(result)
      assert String.contains?(result, "@")
    end

    test "serializes function type with arrow notation" do
      const = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      result = Serialization.to_s_expr(const)
      assert is_binary(result)
      assert String.contains?(result, "⇾")
    end

    test "serializes logical operators" do
      p = mk_const_term("p", mk_type(:o, []))
      _q = mk_const_term("q", mk_type(:o, []))

      # Test negation
      not_op = mk_const_term("¬", mk_type(:o, [mk_type(:o, [])]))
      neg = mk_appl_term(not_op, p)
      result = Serialization.to_s_expr(neg)
      assert is_binary(result)
      assert String.contains?(result, "¬")
    end

    test "serializes equality" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      eq = equals_term(mk_type(:i, [])) |> mk_appl_term(a) |> mk_appl_term(b)
      result = Serialization.to_s_expr(eq)
      assert is_binary(result)
      assert String.contains?(result, "=")
    end
  end

  describe "from_s_expr/1 - S-Expression to Term" do
    test "deserializes a simple constant" do
      s_expr = "p∷o"
      term = Serialization.from_s_expr(s_expr)
      assert term != nil
      assert get_term_type(term) == mk_type(:o, [])
    end

    test "deserializes a variable" do
      s_expr = "$VAR~x∷i"
      term = Serialization.from_s_expr(s_expr)
      assert term != nil
      assert get_term_type(term) == mk_type(:i, [])
    end

    test "deserialization handles type parsing correctly" do
      s_expr = "f∷i⇾i"
      term = Serialization.from_s_expr(s_expr)
      assert term != nil
      # Verify it's a function type
      term_type = get_term_type(term)
      assert term_type == mk_type(:i, [mk_type(:i, [])])
    end

    test "deserialization handles bracketed types" do
      s_expr = "f∷[i⇾o]⇾o"
      term = Serialization.from_s_expr(s_expr)
      assert term != nil
    end
  end

  describe "Roundtrip - Serialization and Deserialization" do
    test "roundtrip: simple constant" do
      original = mk_const_term("p", mk_type(:o, []))
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert get_term_type(original) == get_term_type(deserialized)
    end

    test "roundtrip: variable" do
      var = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      original = mk_term(var)
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert original == deserialized
    end

    test "roundtrip: function type" do
      original = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert get_term_type(original) == get_term_type(deserialized)
    end

    test "roundtrip: application" do
      func = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      arg = mk_const_term("a", mk_type(:i, []))
      original = mk_appl_term(func, arg)
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert get_term_type(original) == get_term_type(deserialized)
    end

    test "roundtrip: lambda abstraction" do
      var = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      body = mk_const_term("p", mk_type(:o, []))
      original = mk_abstr_term(body, var)
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert get_term_type(original) == get_term_type(deserialized)
    end

    test "roundtrip: complex nested expression" do
      x = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      x_term = mk_term(x)

      f = mk_const_term("f", mk_type(:i, [mk_type(:i, [])]))
      app = mk_appl_term(f, x_term)

      original = mk_abstr_term(app, x)
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert get_term_type(original) == get_term_type(deserialized)
    end
  end

  describe "Edge cases and special handling" do
    test "serializes and deserializes empty type arguments" do
      const = mk_const_term("c", mk_type(:o, []))
      serialized = Serialization.to_s_expr(const)
      deserialized = Serialization.from_s_expr(serialized)
      assert get_term_type(const) == get_term_type(deserialized)
    end

    test "serializes multiple bound variables" do
      var1 = declaration(kind: :fv, name: "x", type: mk_type(:i, []))
      var2 = declaration(kind: :fv, name: "y", type: mk_type(:i, []))
      body = mk_const_term("p", mk_type(:o, []))

      term = mk_abstr_term(body, var1)
      term = mk_abstr_term(term, var2)

      serialized = Serialization.to_s_expr(term)
      assert is_binary(serialized)
      assert String.contains?(serialized, "^")
    end

    test "variable names with special characters are preserved" do
      var = declaration(kind: :fv, name: "var_1", type: mk_type(:i, []))
      original = mk_term(var)
      serialized = Serialization.to_s_expr(original)
      deserialized = Serialization.from_s_expr(serialized)
      assert original == deserialized
    end
  end
end
