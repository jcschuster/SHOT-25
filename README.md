# SHOT-25

**SHOT-25** (simply-typed higher-order tableaux) is a tableau prover for
simply-typed higher-order logic (HOL) that relies on higher-order
pre-unification for branch closure.

Tightly integrates with the Elixir libraries
[**HOL**](https://hexdocs.pm/hol/readme.html), which defines data structures
and handles term construction and pre-unification for the simply-typed lambda
calculus, and [**BeHOLd**](https://hexdocs.pm/behold/readme.html), which
extends this library by logical connectives, facilitates pattern matching and
comes with a parser for TPTP syntax.

## Tableau Rules

Generally, to prove a formula $\varphi$, the prover needs to show that
$\neg \varphi$ is unsatisfiable. In terms of semantic tableaux, a formula is
unsatisfiable if all branches close after exhaustive application of the defined
tableau rules. Conversely, if branches remain open, i.e., when no more rules
can be applied, the formula is countersatisfiable.

The prover works with the signature symbols defined in the
[**BeHOLd** package](https://hexdocs.pm/behold/readme.html). It uses the
following rules, where $\star$ refers to branch closure, $\mathbf X_\alpha$ to
a fresh variable of type $\alpha$, $\mathbf{sk}_{\bar t \to \alpha}$ to a fresh
Skolem constant mapping the list of types $\bar t$ to type $\alpha$,
$\operatorname{FV}(\varphi)^i_\alpha$ to the $i$-th free variable in formula
$\varphi$ which is of type $\alpha$ and $\iota$ to a known atomic type other
than $o$.

_Atoms:_

$$
\displaystyle\frac{\top}{}\top
\qquad
\displaystyle\frac{\bot}{\star}\bot
\qquad
\displaystyle\frac{\neg\top}{\star}\neg\top
\qquad
\displaystyle\frac{\neg\bot}{}\neg\bot
\qquad
\displaystyle\frac{\dots,A_o,\dots,B_o}{\star~(\text{if } \sigma(\neg A) = \sigma(B))}\text{Atom}
$$

_Equality:_

$$
\displaystyle\frac{s_o = t_o}{s_o \equiv t_o}=_o
\qquad
\displaystyle\frac{s_\iota = t_\iota}{\Pi(\lambda P. P s \equiv P t)}=_\iota
\qquad
\displaystyle\frac{s_{\alpha\to\beta} = t_{\alpha\to\beta}}{\Pi(\lambda x_\alpha. s x = t x)}=_{\alpha\to\beta}
$$

$$
\displaystyle\frac{\neg (s_o = t_o)}{\neg (s_o \equiv t_o)}\neg=_o
\qquad
\displaystyle\frac{\neg (s_\iota = t_\iota)}{\neg (\Pi(\lambda P. P s \equiv P t))}\neg=_\iota
\qquad
\displaystyle\frac{\neg(s_{\alpha\to\beta} = t_{\alpha\to\beta})}{\neg(\Pi(\lambda x_\alpha. s x = t x))}\neg=_{\alpha\to\beta}
$$

_Reflexivity of Equality:_

$$
\displaystyle\frac{s_\alpha = s_\alpha}{}=^r
\qquad
\displaystyle\frac{\neg (s_\alpha = s_\alpha)}{\star}\neg=^r
$$

_Logical Connectives and their Negation:_

$$
\displaystyle\frac{\neg\neg t}{t}\neg\neg
\qquad
\displaystyle\frac{s \lor t}{s \mid t}\lor
\qquad
\displaystyle\frac{s \land t}{s, t}\land
\qquad
\displaystyle\frac{s \supset t}{\neg s \mid t}\supset
\qquad
\displaystyle\frac{s \equiv t}{s, t \mid \neg s, \neg t}\equiv
$$

$$
\displaystyle\frac{\neg(s \lor t)}{\neg s, \neg t}\neg\lor
\qquad
\displaystyle\frac{\neg(s \land t)}{\neg s \mid \neg t}\neg\land
\qquad
\displaystyle\frac{\neg(s \supset t)}{s, \neg t}\neg\supset
\qquad
\displaystyle\frac{\neg(s \equiv t)}{\neg s, t \mid s, \neg t}\neg\equiv
$$

_Quantors and their Negation (rules $\Pi$ and $\neg\Sigma$ can be repeated infinitely many times):_

$$
\displaystyle\frac{\Pi P_{\alpha\to o}}{P \mathbf{X}_\alpha}\Pi
\qquad
\displaystyle\frac{\Sigma P_{\alpha\to o}}{P (\mathbf{sk}_{\bar t\to\alpha}(\operatorname{FV}(P)^1_{t_1}, \dots, \operatorname{FV}(P)^n_{t_n})_\alpha)}\Sigma
$$

$$
\displaystyle\frac{\neg(\Sigma P_{\alpha\to o})}{\neg (P \mathbf{X}_\alpha)}\neg\Sigma
\qquad
\displaystyle\frac{\neg(\Pi P_{\alpha\to o})}{\neg(P (\mathbf{sk}_{\bar t\to\alpha}(\operatorname{FV}(P)^1_{t_1}, \dots, \operatorname{FV}(P)^n_{t_n})_\alpha))}\neg\Pi
$$

## Parameters

The following parameters can be specified to adapt the prover for the desired
problem:

- `:timeout`: timeout in milliseconds, defaults to 30s
- `:rewrite`: what method to use for rewriting the formula before processing
    - `:orient`: default, just orient the disjunctions and conjunctions in the
      formula based on e-graphs
    - `:simplify`: additionally simplify the formula on propositional level
    - `nil`: don't rewrite the formula
- `:branch_heuristic`: which heuristic to employ when ordering branches
    - `:ncpo`: default, use [NCPO](https://arxiv.org/abs/2505.20121),
      originally a termination order for higher-order rewriting systems on
      $\beta\eta$-normal terms
    - `nil`: don't order branches and process them as they occur
- `:max_instantiations`: how many times the $\Pi$ and $\neg\Sigma$ rules can be
  instantiated on the same formula, defaults to 4
- `:unification_depth`: parameter for the
  [unification algorithm](https://hexdocs.pm/hol/HOL.Unification.html) that
  limits the depth up to which solutions should be searched for the given
  unification problem, defaults to 8
- `:max_concurrency`: upper bound for the amount of schedulers to use when
  checking unification solutions in parallel, defaults to all available
  schedulers

Note that when `:timeout` and `:max_instantiations` have finite values, the
prover is inherently incomplete.

## Limitations

While some simple cases of extensionality are handled by formula rewriting via
e-graphs, this does not extend to more complex extensionality problems. E.g.,
the formula $p(a) \land p(b) \supset p(a \land b)$ is not provable by
**SHOT-25**. A promising approach to solving this could be the adaption of
[subformula renaming](https://doi.org/10.1007/978-3-642-38574-2_7) to classical
HOL and employ it in preprocessing. Instantiation for finite domains is another
direction which can solve extensionality by rephrasing the problem as a
SMT-problem eliminating quantifiers for finite domains.

HOL is undecidable. There might however still be instances where branches that
will remain open can be detected regardless. Such a method is not implemented,
though, which leads to non-termination in countersatisfiable cases whenever
universal or negated existential quantifiers occur on the branches.
