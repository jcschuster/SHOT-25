defmodule SHOT25.Data.ModelTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias SHOT25.Data.Model

  describe "Model struct creation" do
    test "creates model with default values" do
      model = %Model{}

      assert is_struct(model)
      assert model.assignments == MapSet.new()
      assert model.constraints == []
    end

    test "creates model with assignments" do
      p = mk_const_term("p", mk_type(:o, []))
      assignments = MapSet.new([p])
      model = %Model{assignments: assignments}

      assert model.assignments == assignments
      assert model.constraints == []
    end

    test "creates model with constraints" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      constraints = [{a, b}]
      model = %Model{constraints: constraints}

      assert model.assignments == MapSet.new()
      assert model.constraints == constraints
    end

    test "creates model with both assignments and constraints" do
      p = mk_const_term("p", mk_type(:o, []))
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))

      model = %Model{
        assignments: MapSet.new([p]),
        constraints: [{a, b}]
      }

      assert model.assignments == MapSet.new([p])
      assert model.constraints == [{a, b}]
    end
  end

  describe "Model string representation" do
    test "converts empty model to string" do
      model = %Model{}
      result = to_string(model)

      assert is_binary(result)
      assert String.contains?(result, "[]")
    end

    test "converts model with assignments to string" do
      p = mk_const_term("p", mk_type(:o, []))
      model = %Model{assignments: MapSet.new([p])}
      result = to_string(model)

      assert is_binary(result)
    end

    test "converts model with constraints to string" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      model = %Model{constraints: [{a, b}]}
      result = to_string(model)

      assert is_binary(result)
      assert String.contains?(result, "=")
    end

    test "converts model with both to string" do
      p = mk_const_term("p", mk_type(:o, []))
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))

      model = %Model{
        assignments: MapSet.new([p]),
        constraints: [{a, b}]
      }

      result = to_string(model)

      assert is_binary(result)
      assert String.contains?(result, "||")
    end
  end

  describe "Model type specification" do
    test "model is a valid struct" do
      model = %Model{}
      assert is_struct(model, Model)
    end

    test "model assignments are MapSet" do
      p = mk_const_term("p", mk_type(:o, []))
      model = %Model{assignments: MapSet.new([p])}

      assert is_struct(model.assignments, MapSet)
    end

    test "model constraints are list of tuples" do
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      model = %Model{constraints: [{a, b}]}

      assert is_list(model.constraints)
      assert length(model.constraints) == 1
      assert is_tuple(hd(model.constraints))
    end
  end

  describe "Model updates" do
    test "updates assignments" do
      model = %Model{}
      p = mk_const_term("p", mk_type(:o, []))
      updated = %{model | assignments: MapSet.new([p])}

      assert updated.assignments != model.assignments
      assert MapSet.member?(updated.assignments, p)
    end

    test "updates constraints" do
      model = %Model{}
      a = mk_const_term("a", mk_type(:i, []))
      b = mk_const_term("b", mk_type(:i, []))
      updated = %{model | constraints: [{a, b}]}

      assert updated.constraints != model.constraints
      assert length(updated.constraints) == 1
    end
  end
end
