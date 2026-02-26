# SHOT-25

**SHOT-25** (simply-typed higher-order tableaux) is an automated theorem prover
for simply-typed higher-order logic (HOL). It is an implementation of a
higher-order tableaux prover that utilizes **higher-order pre-unification** for
branch closure.

By finding diagonal arguments through unification, SHOT-25 enables shallow
proof trees for classic benchmarks like Cantor's theorem.

## Key Features

- **Logic Framework**: Built on the simply-typed lambda calculus using
  **de Bruijn indices** to ensure unique representation and avoid variable
  capture.
- **Proof Procedure**: Employs a semantic tableau search where rules are
  exhaustively applied to a negated proof goal.
- **Unification**: Uses a semi-decision procedure for higher-order
  pre-unification similar to Huet's algorithm.
- **Parallelism**: Processes unification solutions and branching in parallel,
  utilizing all available schedulers on the Erlang VM.
- **E-Graph Integration**: Uses the Rust library `egg` (via Rustler) to orient
  commutative connectives and simplify formulas at the propositional level.

---

## Technical Integration

SHOT-25 tightly integrates with the following Elixir ecosystem tools:

- [**HOL**](https://hexdocs.pm/hol/readme.html): Handles data structures, term
  construction, and the core unification algorithm.
- [**BeHOLd**](https://hexdocs.pm/behold/readme.html): Provides definitions of
  logical symbols, a parser for **TPTP TH0** syntax, complete type inference, and
  file parsing for the TPTP library.

---

## Tableau Rules

The prover aims to show that a set of formulas is unsatisfiable by closing all
branches. It utilizes the following rule sets:

### Core Rules

- **Propositional**: $\alpha$-rules (conjunctive), $\beta$-rules (disjunctive),
  and double-negation elimination.
- **Quantifiers**: $\gamma$-rules (universal) which introduce fresh variables,
  and $\delta$-rules (existential) which introduce Skolem constants.
- **Equality**: Supports Boolean equality ($\equiv$), Leibniz equality for base
  types, and functional extensionality for function types.
- **Optimization**: Includes reflexivity ($s=s$) and irreflexivity
  ($\neg(s=s)$) checks on a syntactic level to discard redundant literals or
  close branches early.

### Branch Closure

A branch closes via **Atom Unification** when an atom $A$ can be unified with
the negation of an existing literal $B$ in the clause.

---

## Usage Example

You can run the prover within an Elixir environment by passing a formula, a
list of assumptions, definitions and a keyword list of parameters:

```elixir
# Define a goal formula (e.g., via the BeHOLd parser)
formula = BeHOLd.Parser.parse("![X: $i]: (p @ X) => ?[X: $i]: (p @ X)")

# Define proving parameters
params = [
  timeout: 30_000,            # 30 seconds
  rewrite: :simplify,         # Use e-graphs for propositional simplification
  branch_heuristic: :ncpo,    # Prioritize branches using NCPO
  max_instantiations: 4,      # Limit gamma-rule applications
  unification_depth: 8,       # Unification algorithm search depth
  max_concurrency: 16         # Max parallel workers
]

assms = []                    # A list of formulas, treated as assumptions
defs = %{}                    # A map of symbol names and equations

# Execute the tableau procedure
case SHOT25.prove(formula, assms, defs, params) do
  {:valid, :proven} -> IO.puts("Theorem proven!")
  {:countersat, _countermodel} -> IO.puts("Formula is false.")
  {:unknown, _partial, reason} -> IO.puts("Search exhausted: #{reason}")
end
```

---

## Parameters & Heuristics

| Parameter             | Description                                                                                      |
| --------------------- | ------------------------------------------------------------------------------------------------ |
| `:timeout`            | Global timeout in milliseconds (default: 30s)                                                    |
| `:rewrite`            | Preprocessing via e-graphs: `:orient` or `:simplify`                                             |
| `:branch_heuristic`   | Uses [**NCPO**](https://arxiv.org/abs/2505.20121) to prioritize branches likely to close earlier |
| `:max_instantiations` | Limits how many times $\gamma$-rules can be applied.                                             |
| `:unification_depth`  | Limits the depth of the pre-unification search to ensure termination.                            |
| `:max_concurrency`    | Bounds the number of parallel schedulers for checking unification solutions.                     |

---

## Limitations of SHOT-25

While `egg` handles extensionality modulo propositional rewriting, complex
cases such as proving $p(a \land b) \supset p(a) \land p(b)$ currently fail.
Improvements planned for the prover involve adapting subformula renaming in
preprocessing and the adaption of extensionality rules from other calculi,
e.g. instantiations in finite domains such as for type $o$, $o\to o$ etc.

The undecidability of HOL additionally yields the challenge of non-termination
whenever a countersatisfiable formula is processed and the tableau involves
$\gamma$-rule instantiations.
