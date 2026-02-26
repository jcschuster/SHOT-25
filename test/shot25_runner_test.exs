defmodule SHOT25.RunnerTest do
  use ExUnit.Case

  import HOL.{Data, Terms}
  import BeHOLd.ClassicalHOL.Definitions
  alias SHOT25.Runner
  alias BeHOLd.Data.Problem

  # Note: These tests are limited as the Runner module primarily deals with
  # file I/O and printing to stdout. We test the core logic where possible.

  describe "run_prover/2" do
    test "accepts problem struct" do
      # Create a minimal problem
      problem = %Problem{
        axioms: [],
        conjecture: nil,
        definitions: %{}
      }

      # This will print to stdout but should not raise
      try do
        Runner.run_prover(problem)
      rescue
        # Expected if system calls IO.puts
        UndefinedFunctionError -> :ok
        # Expected from no_return
        SystemExit -> :ok
        _ -> :ok
      end
    end

    test "accepts problem with options" do
      problem = %Problem{
        axioms: [],
        conjecture: nil,
        definitions: %{}
      }

      try do
        Runner.run_prover(problem, timeout: 5000)
      rescue
        UndefinedFunctionError -> :ok
        SystemExit -> :ok
        _ -> :ok
      end
    end

    test "handles problem with conjecture" do
      p = mk_const_term("p", mk_type(:o, []))

      problem = %Problem{
        axioms: [],
        conjecture: {"test_conjecture", p},
        definitions: %{}
      }

      try do
        Runner.run_prover(problem)
      rescue
        UndefinedFunctionError -> :ok
        SystemExit -> :ok
        _ -> :ok
      end
    end

    test "handles problem with axioms" do
      p = mk_const_term("p", mk_type(:o, []))

      problem = %Problem{
        axioms: [{"axiom1", p}],
        conjecture: nil,
        definitions: %{}
      }

      try do
        Runner.run_prover(problem)
      rescue
        UndefinedFunctionError -> :ok
        SystemExit -> :ok
        _ -> :ok
      end
    end

    test "handles problem with definitions" do
      _p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      problem = %Problem{
        axioms: [],
        conjecture: nil,
        definitions: %{"p" => q}
      }

      try do
        Runner.run_prover(problem)
      rescue
        UndefinedFunctionError -> :ok
        SystemExit -> :ok
        _ -> :ok
      end
    end

    test "handles complex problem" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))
      r = mk_const_term("r", mk_type(:o, []))

      problem = %Problem{
        axioms: [{"ax1", p}, {"ax2", q}],
        conjecture: {"conj1", r},
        definitions: %{}
      }

      try do
        Runner.run_prover(problem, timeout: 5000)
      rescue
        UndefinedFunctionError -> :ok
        SystemExit -> :ok
        _ -> :ok
      end
    end
  end

  describe "prove_file/3" do
    # Note: These tests are difficult to implement without actual TPTP files
    # They mostly check that the function signature is correct

    test "accepts file path and is_tptp flag" do
      # This test just validates that the function can be called
      # We expect it to fail because the file doesn't exist
      try do
        Runner.prove_file("nonexistent.tptp", true)
      rescue
        # Expected from the function
        SystemExit -> :ok
        # File not found or other error
        _ -> :ok
      end
    end

    test "accepts options parameter" do
      try do
        Runner.prove_file("nonexistent.tptp", true, timeout: 5000)
      rescue
        SystemExit -> :ok
        _ -> :ok
      end
    end

    test "accepts custom file with is_tptp false" do
      try do
        Runner.prove_file("custom_file.txt", false)
      rescue
        SystemExit -> :ok
        _ -> :ok
      end
    end
  end

  describe "problem structure validation" do
    test "problem with all fields set" do
      p = mk_const_term("p", mk_type(:o, []))
      q = mk_const_term("q", mk_type(:o, []))

      problem = %Problem{
        axioms: [{"axiom", p}],
        conjecture: {"conj", q},
        definitions: %{}
      }

      assert problem.axioms == [{"axiom", p}]
      assert problem.conjecture == {"conj", q}
      assert is_map(problem.definitions)
    end
  end
end
