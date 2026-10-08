# Markov decision processes in Lean

This is the `FiniteStates/MarkovDecisionProcesses/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/MarkovDecisionProcesses`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 5, "Markov Decision Processes" (pp. 128–181),
including every provable exercise (Exercises 5.1.1–5.1.13, 5.2.2–5.2.3,
5.3.1–5.3.8). The library contains **176 theorems** and audits every
declaration, including structure constructors and projections.

* **The MDP model and its optimality theory** (§5.1): an MDP is `(Γ, β, r, P)`;
  a feasible policy `σ` has closed-loop matrix `P_σ`, reward `r_σ` and lifetime
  value `v_σ = ∑ βᵗP_σᵗ r_σ = (I − βP_σ)⁻¹ r_σ`, (5.18), the unique fixed point
  of the policy operator `T_σ v = r_σ + βP_σ v` (Exercise 5.1.7), with the
  bounds of Exercise 5.1.6 and the finite-horizon identity of Exercises
  5.1.8–5.1.9. The Bellman operator maximises the action value over `Γ(x)`; it is
  the pointwise maximum of the `T_σ` (Exercises 5.1.10–5.1.11) and a
  `β`-contraction (Exercise 5.1.12). Proposition 5.1.1: the value function
  `v* = ⋁_σ v_σ` is the unique solution of the Bellman equation, value function
  iteration converges, a policy is optimal iff it is `v*`-greedy, and an optimal
  policy exists (Exercise 5.1.13).
* **Algorithms** (§5.1.4): Lemma 5.1.2, that `βP_σ` is a subgradient of `T` at
  `v` for a `v`-greedy `σ`; the identity `(I − βP_σ)⁻¹(Tv − βP_σ v) = v_σ` that
  makes Howard policy iteration a Newton step; the monotone improvement step
  `v_σ ≤ v_σ'` and the termination criterion (if the value stops changing the
  policy is optimal); optimistic policy iteration with `m = 1` is VFI, and its
  inner iterates converge to `v_σ` as `m → ∞`.
* **Seven MDPs** (§5.1.2, §5.2): the renewal problem (Exercise 5.1.1), optimal
  inventories with the geometric kernel in closed form (Exercise 5.1.2), cake
  eating (Exercise 5.1.4), job search with Markov wages as an MDP on
  `{0, 1} × W`, whose value function reproduces the job search Bellman equation
  of Chapter 3 (Exercise 5.1.5), optimal savings with labour income, optimal
  investment with Exercise 5.2.2, and the firm hiring model of Exercise 5.2.3.
* **Operator factorisations** (§5.3.4–§5.3.5): `T = MDE`, `R = EMD`, `S = DEM`;
  the explicit forms of `R` and `S` (Exercise 5.3.5), the iterate relations
  (Exercises 5.3.6 and 5.3.8), nonexpansiveness of `E` and `M` and contraction of
  `D` (Exercise 5.3.7), so all three are `β`-contractions (Lemma 5.3.5); the
  fixed points satisfy `g* = Ev*`, `q* = Dg*`, `v* = Mq*` (Proposition 5.3.6);
  a policy is optimal iff it is `v*`-, `g*`- or `q*`-greedy (Corollary 5.3.7,
  containing Proposition 5.3.4 on Q-factors); refactored OPI tracks regular OPI
  through `R_σᵐ(Ev) = E(T_σᵐ v)`.
* **Expected value functions** (§5.3.1, §5.3.3): for structural models with a
  finite shock space, the expected value function depends only on `(y, a)`, the
  expected value Bellman operator is an order-preserving `β`-contraction
  (Exercise 5.3.1), and Proposition 5.3.1 characterises optimal policies through
  its fixed point. Optimal savings with stochastic returns and the transient
  income model of Exercise 5.3.3 are instances, with their Bellman equations in
  both forms.
* **The Gumbel max trick** (§5.3.2): the log-sum-exp operator (5.36) is a
  contraction of modulus `β` by Blackwell's condition (Proposition 5.3.3), and
  the shift property of Exercise 5.3.2 holds for the Gumbel distribution
  function, whose formula the book prints with the wrong sign.

The main entry points are `MDP.isContractionOn_Tσ`, `MDP.vσ_eq_inv`,
`MDP.isFixedPt_T_vstar`, `MDP.bellman_equation`, `MDP.isOptimal_iff_isGreedy`,
`MDP.subgradient_of_isGreedy`, `MDP.vσ_le_vσ_of_isGreedy`, `MDP.isContractionOn_R`,
`MDP.isOptimal_iff_isQGreedy`, `MDP.Rσ_iterate_E`, `Structural.isOptimal_iff`,
`jobSearch.vstar_unemployed` and `isContractionOn_gumbelR`, all in the namespace
`SargentStachurski.MarkovDecisionProcesses`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (the Gumbel CDF's sign; the structural model
with a finite shock space), the hypotheses the book leaves implicit, and what
is not formalised: the quadratic convergence (5.27) and finite termination of
HPI, the global convergence of OPI, and the exactness of VFI after finitely
many steps, all of which the book defers to Chapter 8 or cites.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](MarkovDecisionProcesses/Basics.lean) | 18 | Markov matrices, contractions with Banach's theorem, Prop 2.2.7, the HPI improvement lemma, Blackwell's condition, Lemma 2.2.2 (restated Chapter 1–3 facts) |
| [MDP](MarkovDecisionProcesses/MDP.lean) | 22 | `(Γ, β, r, P)`, feasible policies, `P_σ`, `r_σ`, `T_σ` (5.19)–(5.20), Ex 5.1.7, `v_σ` and (5.18), Ex 5.1.6, 5.1.8–5.1.9 |
| [Bellman](MarkovDecisionProcesses/Bellman.lean) | 32 | `T` (5.24), greedy policies (5.22), Ex 5.1.10–5.1.12, `v*` (5.21), Prop 5.1.1 (Ex 5.1.13), Lemma 5.1.2, HPI as Newton, HPI improvement and termination, OPI |
| [Examples](MarkovDecisionProcesses/Examples.lean) | 18 | Renewal (5.3)–(5.4), Ex 5.1.1; inventories (5.6)–(5.9), Ex 5.1.2; deterministic kernels |
| [Applications](MarkovDecisionProcesses/Applications.lean) | 18 | Choice kernels; cake eating (Ex 5.1.4); savings (5.29)–(5.30), `P_σ`, `r_σ`; investment, Ex 5.2.2; hiring, Ex 5.2.3; job search as an MDP (Ex 5.1.5) with Vol. 1 (3.23) recovered |
| [Refactoring](MarkovDecisionProcesses/Refactoring.lean) | 42 | `E`, `D`, `M`, (5.40), Ex 5.3.5–5.3.8, Lemma 5.3.5, Prop 5.3.6, Cor 5.3.7, Prop 5.3.4, `M_σ`, `R_σ`, `S_σ`, refactored OPI |
| [ExpectedValue](MarkovDecisionProcesses/ExpectedValue.lean) | 19 | (5.33)–(5.35) with finite shocks, Ex 5.3.1, Prop 5.3.1, `R_σ` reduced; stochastic returns (5.37) and p. 169; Ex 5.3.3 |
| [Gumbel](MarkovDecisionProcesses/Gumbel.lean) | 7 | Gumbel CDF and Ex 5.3.2; the operator (5.36); Prop 5.3.3 by Blackwell |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
