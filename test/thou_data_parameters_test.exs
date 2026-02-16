defmodule THOU.Data.ParametersTest do
  use ExUnit.Case

  alias THOU.Data.Parameters

  describe "Parameters struct creation with defaults" do
    test "new() creates parameters with default values" do
      params = Parameters.new()

      assert is_struct(params)
      assert params.rewrite == :orient
      assert params.branch_heuristic == :ncpo
      assert params.max_instantiations == 4
      assert params.unification_depth == 8
      assert params.max_concurrency != nil
      assert is_integer(params.max_concurrency)
    end

    test "default max_concurrency matches schedulers online" do
      params = Parameters.new()

      assert params.max_concurrency == System.schedulers_online()
    end
  end

  describe "Parameters struct creation with options" do
    test "new() with rewrite option" do
      params = Parameters.new(rewrite: :simplify)

      assert params.rewrite == :simplify
      assert params.branch_heuristic == :ncpo
    end

    test "new() with rewrite as nil" do
      params = Parameters.new(rewrite: nil)

      assert params.rewrite == nil
    end

    test "new() with branch_heuristic option" do
      params = Parameters.new(branch_heuristic: :custom)

      assert params.branch_heuristic == :custom
    end

    test "new() with branch_heuristic as nil" do
      params = Parameters.new(branch_heuristic: nil)

      assert params.branch_heuristic == nil
    end

    test "new() with max_instantiations option" do
      params = Parameters.new(max_instantiations: 10)

      assert params.max_instantiations == 10
    end

    test "new() with unification_depth option" do
      params = Parameters.new(unification_depth: 16)

      assert params.unification_depth == 16
    end

    test "new() with max_concurrency option" do
      params = Parameters.new(max_concurrency: 2)

      assert params.max_concurrency == 2
    end

    test "new() with all options" do
      params =
        Parameters.new(
          rewrite: :simplify,
          branch_heuristic: :custom,
          max_instantiations: 5,
          unification_depth: 12,
          max_concurrency: 4
        )

      assert params.rewrite == :simplify
      assert params.branch_heuristic == :custom
      assert params.max_instantiations == 5
      assert params.unification_depth == 12
      assert params.max_concurrency == 4
    end
  end

  describe "Parameters type validation" do
    test "parameters struct is valid" do
      params = Parameters.new()

      assert is_struct(params, Parameters)
    end

    test "rewrite field is atom or nil" do
      params1 = Parameters.new(rewrite: :orient)
      params2 = Parameters.new(rewrite: nil)

      assert is_atom(params1.rewrite)
      assert params2.rewrite == nil
    end

    test "branch_heuristic field is atom or nil" do
      params1 = Parameters.new(branch_heuristic: :ncpo)
      params2 = Parameters.new(branch_heuristic: nil)

      assert is_atom(params1.branch_heuristic)
      assert params2.branch_heuristic == nil
    end

    test "max_instantiations field is positive integer" do
      params = Parameters.new(max_instantiations: 4)

      assert is_integer(params.max_instantiations)
      assert params.max_instantiations > 0
    end

    test "unification_depth field is positive integer" do
      params = Parameters.new(unification_depth: 8)

      assert is_integer(params.unification_depth)
      assert params.unification_depth > 0
    end

    test "max_concurrency field is positive integer or nil" do
      params1 = Parameters.new(max_concurrency: 4)
      params2 = Parameters.new()

      assert is_integer(params1.max_concurrency) or is_nil(params1.max_concurrency)
      assert is_integer(params2.max_concurrency)
    end
  end

  describe "Parameters field constraints" do
    test "max_instantiations default is 4" do
      params = Parameters.new()

      assert params.max_instantiations == 4
    end

    test "unification_depth default is 8" do
      params = Parameters.new()

      assert params.unification_depth == 8
    end

    test "branch_heuristic default is :ncpo" do
      params = Parameters.new()

      assert params.branch_heuristic == :ncpo
    end

    test "rewrite default is :orient" do
      params = Parameters.new()

      assert params.rewrite == :orient
    end
  end

  describe "Parameters keyword argument handling" do
    test "accepts empty keyword list" do
      params = Parameters.new([])

      assert params.rewrite == :orient
      assert params.max_instantiations == 4
    end

    test "accepts single keyword argument" do
      params = Parameters.new(max_instantiations: 8)

      assert params.max_instantiations == 8
    end

    test "accepts multiple keyword arguments" do
      opts = [
        max_instantiations: 6,
        unification_depth: 10,
        rewrite: nil
      ]

      params = Parameters.new(opts)

      assert params.max_instantiations == 6
      assert params.unification_depth == 10
      assert params.rewrite == nil
    end
  end
end
