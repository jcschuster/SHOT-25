defmodule SHOT25 do
  @moduledoc """
  `SHOT25` (simply-typed higher-order tableaux) is a tableau prover for
  simply-typed higher-order logic which relies on pre-unification provided by
  the `HOL` library (https://hexdocs.pm/hol/api-reference.html) for branch
  closure.

  This module collects the main API calls to the prover.
  """

  @doc """
  Tries to satisfy a given formula or list of formulas. Returns a
  `SHOT25.Prover.sat_result` describing one of three outcomes.

  Internally relies on the `SHOT25.Tableaux.tableau/3` function as model
  finder.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec sat(HOL.Data.hol_term() | [HOL.Data.hol_term()]) ::
          SHOT25.Prover.sat_result()
  defdelegate sat(formulas), to: SHOT25.Prover

  @doc """
  Tries to satisfy a given formula or list of formulas with respect to the
  given definitions. Returns a `SHOT25.Prover.sat_result` describing one of
  three outcomes.

  Internally relies on the `SHOT25.Tableaux.tableau/3` function as model
  finder.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec sat(HOL.Data.hol_term() | [HOL.Data.hol_term()], SHOT25.Prover.definitions()) ::
          SHOT25.Prover.sat_result()
  defdelegate sat(formulas, definitions), to: SHOT25.Prover

  @doc """
  Tries to satisfy a given formula or list of formulas with respect to the
  given definitions. Returns a `SHOT25.Prover.sat_result` describing one of three
  outcomes.

  Internally relies on the `SHOT25.Tableaux.tableau/3` function as model finder.

  Parameters that can be given in the `opts` field are a `:timeout` in
  milliseconds, which defaults to 30s and all technical parameters of
  `SHOT25.Tableaux.tableau/3`.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec sat(HOL.Data.hol_term() | [HOL.Data.hol_term()], SHOT25.Prover.definitions(), Keyword.t()) ::
          SHOT25.Prover.sat_result()
  defdelegate sat(formulas, definitions, opts), to: SHOT25.Prover

  @doc """
  Tries to proof a given term by showing that there is no couterexample for its
  negation, i.e., that `SHOT25.Tableaux.tableau/3` can close all branches.
  Returns a `SHOT25.Prover.proof_result` describing the output, which can be
  pretty-printed with a call to `SHOT25.PrettyPrint.pp_proof_result/1`.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec prove(HOL.Data.hol_term()) ::
          SHOT25.Prover.proof_result()
  defdelegate prove(conclusion), to: SHOT25.Prover

  @doc """
  Tries to proof a given term based on the given assumptions by showing that
  there is no couterexample for its negation, i.e., that
  `SHOT25.Tableaux.tableau/3` can close all branches. Returns a
  `SHOT25.Prover.proof_result` describing the output, which can be
  pretty-printed with a call to `SHOT25.PrettyPrint.pp_proof_result/1`.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec prove(HOL.Data.hol_term(), [HOL.Data.hol_term()]) ::
          SHOT25.Prover.proof_result()
  defdelegate prove(conclusion, assumptions), to: SHOT25.Prover

  @doc """
  Tries to proof a given term based on the given assumptions and definitions by
  showing that there is no couterexample for its negation, i.e., that
  `SHOT25.Tableaux.tableau/3` can close all branches. Returns a
  `SHOT25.Prover.proof_result` describing the output, which can be pretty-printed
  with a call to `SHOT25.PrettyPrint.pp_proof_result/1`.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec prove(HOL.Data.hol_term(), [HOL.Data.hol_term()], SHOT25.Prover.definitions()) ::
          SHOT25.Prover.proof_result()
  defdelegate prove(conclusion, assumptions, definitions), to: SHOT25.Prover

  @doc """
  Tries to proof a given term based on the given assumptions and definitions by
  showing that there is no couterexample for its negation, i.e., that
  `SHOT25.Tableaux.tableau/3` can close all branches. Returns a
  `SHOT25.Prover.proof_result` describing the output, which can be
  pretty-printed with a call to `SHOT25.PrettyPrint.pp_proof_result/1`.

  Parameters that can be given in the `opts` field are a timeout in
  milliseconds (defaults to 30s) and all technical parameters of
  `SHOT25.Tableaux.tableau/3`.

  Delegates function call to `SHOT25.Prover`.
  """
  @spec prove(
          HOL.Data.hol_term(),
          [HOL.Data.hol_term()],
          SHOT25.Prover.definitions(),
          Keyword.t()
        ) ::
          SHOT25.Prover.proof_result()
  defdelegate prove(conclusion, assumptions, definitions, opts), to: SHOT25.Prover

  @doc """
  Parses a TPTP problem file in TH0 syntax, attempts to prove the conjecture
  found within it and prints the result to stdout. If no conjecture could be
  found in the given file, tries to satisfy the axioms.

  This function assumes, that an environment variable `TPTP_ROOT` is registered
  and points to the root directory of the TPTP problem library. `path` should
  then specify the path from this root directory to the problem file.

  For proving custom files, use `prove_file/2` and set the field `is_tptp` to
  `false` to be able to specify the absolute path to the problem file.

  If no conjecture could be found within the given problem, tries to satisfy
  the axioms.

  Delegates function call to `SHOT25.Runner`.
  """
  @spec prove_file(String.t()) :: no_return()
  defdelegate prove_file(path), to: SHOT25.Runner

  @doc """
  Parses a TPTP problem file in TH0 syntax, attempts to prove the conjecture
  found within it and prints the result to stdout. If no conjecture could be
  found in the given file, tries to satisfy the axioms.

  If a custom file is given, the flag `is_tptp` should be set to `false`. Note
  that only imports from the TPTP library are supported. In that case, an
  environment variable `TPTP_ROOT` must be specified which points to the root
  folder of the TPTP problem library. Note that this may require a system
  restart for Elixir to register the variable.

  When proving a file from the TPTP problem library, the same environment
  variable `TPTP_ROOT` needs to be registered. After the variable has been
  registered, a TPTP problem file can be parsed by specifying the path from the
  root folder to that problem in `path`.

  If no conjecture could be found within the given problem, tries to satisfy
  the axioms.

  Delegates function call to `SHOT25.Runner`.
  """
  @spec prove_file(String.t(), boolean()) :: no_return()
  defdelegate prove_file(path, is_tptp), to: SHOT25.Runner

  @doc """
  Parses a TPTP problem file in TH0 syntax, attempts to prove the conjecture
  found within it and prints the result to stdout. If no conjecture could be
  found in the given file, tries to satisfy the axioms.

  If a custom file is given, the flag `is_tptp` should be set to `false`. Note
  that only imports from the TPTP library are supported. In that case, an
  environment variable `TPTP_ROOT` must be specified which points to the root
  folder of the TPTP problem library. Note that this may require a system
  restart for Elixir to register the variable.

  When proving a file from the TPTP problem library, the same environment
  variable `TPTP_ROOT` needs to be registered. After the variable has been
  registered, a TPTP problem file can be parsed by specifying the path from the
  root folder to that problem in `path`.

  If no conjecture could be found within the given problem, tries to satisfy
  the axioms.

  Options for `SHOT25.Prover.prove/4` can be specified.

  Delegates function call to `SHOT25.Runner`.
  """
  @spec prove_file(String.t(), boolean(), Keyword.t()) :: no_return()
  defdelegate prove_file(path, is_tptp, opts), to: SHOT25.Runner

  @doc """
  Runs the prover on a given `BeHOLd.Data.Problem` struct from parsing a TPTP
  Problem file specified as string and prints the result to stdout. If no
  conjecture could be found within the given problem, tries to satisfy the
  axioms.

  Delegates function call to `SHOT25.Runner`.
  """
  @spec run_prover(BeHOLd.Data.Problem.t()) :: no_return()
  defdelegate run_prover(problem), to: SHOT25.Runner

  @doc """
  Runs the prover on a given `BeHOLd.Data.Problem` struct from parsing a TPTP
  Problem file specified as string and prints the result to stdout. If no
  conjecture could be found within the given problem, tries to satisfy the
  axioms.

  Options for `SHOT25.Prover.prove/4` can be specified.

  Delegates function call to `SHOT25.Runner`.
  """
  @spec run_prover(BeHOLd.Data.Problem.t(), Keyword.t()) :: no_return()
  defdelegate run_prover(problem, opts), to: SHOT25.Runner
end
