# Dynamic Programming in Lean

Checked dynamic programming, following Sargent and Stachurski, *Dynamic
Programming*, Volume 1: *Finite States* and Volume 2: *General States*. Each
folder is an independent Lean/Mathlib project for one chapter, with precise
statements, a source map to the book's results and pages, and reproducible
proof checks. Volume 1 projects live under `FiniteStates/`, Volume 2 under
`GeneralStates/`.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [FiniteStates/JobSearch](FiniteStates/JobSearch/README.md) | I.1 Introduction | 201 theorems: Banach's theorem by the book's route, the Neumann series lemma from the spectral radius with Gelfand's formula, the Solow–Swan map globally stable without being a contraction, finite-horizon reservation wages at every horizon, the Bellman operator as a `β`-contraction with value function iteration, the continuation-value map, quantiles on a finite set | [Chapter overview](FiniteStates/JobSearch/README.md) |
| [FiniteStates/OperatorsFixedPoints](FiniteStates/OperatorsFixedPoints/README.md) | I.2 Operators and Fixed Points | 235 theorems: the Perron–Frobenius theorem for nonnegative matrices proved from scratch through the resolvent, with its row-sum and column-sum bounds, the local spectral radius and stationary distributions of Markov matrices; conjugacy and local stability, convergence rates and the Newton map; partial orders, the pointwise lattice on `ℝ^X`, Blackwell's condition, stochastic dominance with the counter-CDF converse by Abel summation, parametric monotonicity for Solow–Swan and job search; the lake model; linear, positive and Markov operators | [Chapter overview](FiniteStates/OperatorsFixedPoints/README.md) |
| [FiniteStates/MarkovDynamics](FiniteStates/MarkovDynamics/README.md) | I.3 Markov Dynamics | 145 theorems: `k`-step transition probabilities as path sums, marginal and stationary distributions, irreducibility and the S–s inventory chain; global stability of `ψ ↦ ψP` for every `P ≫ 0` by Dobrushin's contraction; Tauchen's discretisation is Markov and monotone; conditional expectations, iterated expectations and monotone Markov operators; lifetime values `(I − βP)⁻¹h` with firm and consumption valuations; job search with Markov wages and with separation | [Chapter overview](FiniteStates/MarkovDynamics/README.md) |
| [FiniteStates/OptimalStopping](FiniteStates/OptimalStopping/README.md) | I.4 Optimal Stopping | 143 theorems: policy operators and lifetime values with `ρ(L_σ) < 1`, the Bellman operator as a `β`-contraction whose fixed point is the value function, Bellman's principle of optimality for stopping problems, continuation values and their operator, monotone values and threshold policies, dimensionality reduction for IID components, firm exit with `w ≪ v*`, American options with an exercise region that expands over time, R&D with constant and IID costs | [Chapter overview](FiniteStates/OptimalStopping/README.md) |
| [FiniteStates/MarkovDecisionProcesses](FiniteStates/MarkovDecisionProcesses/README.md) | I.5 Markov Decision Processes | 176 theorems: policy operators and lifetime values `(I − βP_σ)⁻¹r_σ`, the Bellman operator as `⋁_σ T_σ` and a `β`-contraction with the value function as its unique fixed point, Bellman's principle of optimality, the subgradient lemma that makes Howard policy iteration a Newton step with its improvement and termination steps, seven worked MDPs from renewal to firm hiring, the factorisations `T = MDE`, `R = EMD`, `S = DEM` with the refactored principle of optimality, expected value functions for structural models and stochastic returns, the Gumbel max trick as a Blackwell contraction | [Chapter overview](FiniteStates/MarkovDecisionProcesses/README.md) |
| [FiniteStates/StochasticDiscounting](FiniteStates/StochasticDiscounting/README.md) | I.6 Stochastic Discounting | 263 theorems: the Perron–Frobenius theorem completed (irreducible and everywhere-positive cases, `ρ(A)⁻ᵗAᵗ → eεᵀ`, the unique positive stationary distribution), lifetime values `(I − L)⁻¹h` under time-varying discount factors with `ρ(L) = lim ℓₜ^{1/t}`, eventual contractions and the generalised Blackwell condition, MDPs with state-dependent discounting and Bellman's principle of optimality under `ρ(L_σ) < 1`, exogenous discounting with convergent value function iteration, the inventory model with time-varying interest rates, Markov asset pricing with stationary and growing dividends, the Harrison–Kreps operator | [Chapter overview](FiniteStates/StochasticDiscounting/README.md) |
| [FiniteStates/NonlinearValuation](FiniteStates/NonlinearValuation/README.md) | I.7 Nonlinear Valuation | 251 theorems: Knaster–Tarski on order intervals and Du's theorem under all four conditions, one-dimensional concave stability (Solow–Swan, Inada, Fajgelbaum et al.), Theorem 7.1.4 (`[h + (Av)^{1/θ}]^θ` is globally stable iff `ρ(A)^{1/θ} < 1`), risk-sensitive and Epstein–Zin lifetime utility, the entropic risk-adjusted expectation, linear, entropic, Kreps–Porteus and quantile certainty equivalents, Koopmans operators with the Blackwell-type condition, quantile and Uzawa preferences, Epstein–Zin with state-dependent discounting | [Chapter overview](FiniteStates/NonlinearValuation/README.md) |
| [FiniteStates/RecursiveDecisionProcesses](FiniteStates/RecursiveDecisionProcesses/README.md) | I.8 Recursive Decision Processes | 431 theorems: RDPs `(Γ, V, B)`, Theorems 8.1.1 and 8.1.2 (optimality, HPI, OPI and VFI for globally stable and for well-posed bounded RDPs), topologically conjugate RDPs, contracting RDPs with the error bound and Blackwell's condition, eventually contracting RDPs (completing Proposition 6.2.2), convex and concave RDPs, optimal default, quantile and risk-sensitive job search, adversarial agents, robust control and the KL variational formula, Epstein–Zin RDPs, smooth ambiguity, min-optimality (Theorem 8.3.7), shortest paths and negative discount rates | [Chapter overview](FiniteStates/RecursiveDecisionProcesses/README.md) |
| [FiniteStates/AbstractDynamicProgramming](FiniteStates/AbstractDynamicProgramming/README.md) | I.9 Abstract Dynamic Programming | 241 theorems: order stability of self-maps of partially ordered sets and its relation to global stability and order duality, abstract dynamic programs with greedy policies, Bellman and Howard operators, Theorem 9.2.4 and Proposition 9.2.5 (max-optimality, finite termination of HPI), ADPs from RDPs, MDPs and (risk-sensitive) Q-factors, well-posed iff order stable on order intervals, Theorems 8.1.1–8.1.2 proved through ADPs with the OPI lemmas, mixed strategies, min-optimality by duality (Theorem 9.2.11) | [Chapter overview](FiniteStates/AbstractDynamicProgramming/README.md) |
| [FiniteStates/ContinuousTime](FiniteStates/ContinuousTime/README.md) | I.10 Continuous Time | 269 theorems: the memoryless characterisation of the exponential distribution, the matrix exponential with Lemma 10.1.2 (and a counterexample to its eigenvalue converse), uniqueness for linear IVPs, the spectral mapping theorem `σ(e^A) = e^{σ(A)}` and Theorem 10.1.5 in full (`s(A) < 0` iff exponential decay iff `L^p` integrability), every `C₀`-semigroup on `ℝ^X` is exponential, intensity matrices and Markov semigroups with the Kolmogorov equations, jump chains and the integrated backward equation, lifetime valuation `v = −A⁻¹h` with order stability, continuous-time MDPs through ADPs (Theorem 10.2.4: HJB uniqueness, Bellman's principle, finite termination of HPI), continuous-time job search | [Chapter overview](FiniteStates/ContinuousTime/README.md) |
| [GeneralStates/PreludeExamples](GeneralStates/PreludeExamples/README.md) | II.1 Prelude: Examples of Dynamic Programs | 153 theorems: Banach's theorem on the bounded measurable functions `bX` with Markov operators and the Neumann series, one optimality template for contracting dynamic programs (VFI, HPI in finitely many steps, OPI from every start), the firm sale problem (Theorem 1.1.1), entropic certainty equivalents and recursive risk adjustment (1.14) proved well posed, mean-variance shown not order preserving, finite MDPs (Theorems 1.2.1–1.2.2, the LP characterisation), cash management, uniformization and the HJB equation, service rate control, optimal savings (Lemma 1.3.1) and the CRRA closed form, sequential analysis | [Chapter overview](GeneralStates/PreludeExamples/README.md) |
| [GeneralStates/AbstractDecisionProcesses](GeneralStates/AbstractDecisionProcesses/README.md) | II.2 Abstract Decision Processes | 351 theorems: order stability and its duality, Knaster–Tarski on chain complete posets via Zorn, Tarski–Kantorovich; abstract dynamic programs on posets, greedy policies, the Bellman operator and the fundamental optimality properties (Proposition 2.1.4, Theorems 2.1.5 and 2.1.7); VFI, OPI and HPI for every greedy selector (Theorems 2.2.6–2.2.8); minimization through the dual ADP (Theorem 2.2.9); the firm, optimal savings and finite MDP problems as ADPs (Proposition 2.3.1); distributional dynamic programming under stochastic dominance with the Wasserstein contraction (Proposition 2.3.2); LQ control with the Loewner order and the Riccati equation (Lemmas 2.3.3 and 2.3.5–2.3.9) | [Chapter overview](GeneralStates/AbstractDecisionProcesses/README.md) |
| [GeneralStates/ADPsOnPospaces](GeneralStates/ADPsOnPospaces/README.md) | II.3 ADPs on Pospaces | 434 theorems: globally stable ADPs on pospaces (Theorems 3.1.2 and 3.1.4, Corollary 3.1.3), contracting ADPs on sup-nonexpansive metric spaces (Theorem 3.1.5, shown to need a nonempty V₀), minimization (Theorems 3.1.6–3.1.8, with the inf-nonexpansiveness Theorem 3.1.7's proof needs), nonstationary policies (Theorem 3.1.10), bounded measurable functions as a Banach lattice, countable MDPs and Q-factors, optimal savings in the weakly continuous case with an explicit measurable greedy policy (Proposition 3.2.2), no-discount optimal stopping (Theorem 3.2.9) and sequential analysis (Proposition 3.2.10, on the belief space [0, 1]) | [Chapter overview](GeneralStates/ADPsOnPospaces/README.md) |
| [GeneralStates/ADPsOnBanachSpace](GeneralStates/ADPsOnBanachSpace/README.md) | II.4 ADPs on Banach Space | 387 theorems: eventually contracting maps (Theorem 4.1.1), normalized order units and Blackwell's condition (Lemma 4.1.2, Theorem 4.1.3, Proposition A.5.23), discount operators and order contractions (Theorems 4.1.4–4.1.8), Du's theorem proved for Banach lattices (Theorems 4.1.10–4.1.11), firm valuation on bX, in L¹ and with state-dependent discounting (Propositions 4.2.1–4.2.2), a real option problem in L¹ (Proposition 4.2.3, with the misprint in (4.17) corrected), and structural estimation with measurable greedy policies, state-dependent discounting and risk-sensitive certainty equivalents (Propositions 4.2.4–4.2.6) | [Chapter overview](GeneralStates/ADPsOnBanachSpace/README.md) |
| [GeneralStates/ADPTransformations](GeneralStates/ADPTransformations/README.md) | II.5 ADP Transformations | 587 theorems: conjugate, topologically conjugate and order conjugate systems (Propositions 5.1.1–5.1.2, Lemma 5.1.3, stability of a diagonalizable matrix from its eigenvalues), isomorphic and anti-isomorphic ADPs (Theorems 5.1.5–5.1.10), Epstein–Zin optimality without irreducibility (Proposition 5.1.13, with Du's theorem for minimization), strong semiconjugacy (Theorems 5.2.3–5.2.4, shown false under one-sided order continuity and proved with limits in both directions) and firm entry (Proposition 5.2.7), factored dynamic programs (Theorems 5.2.13 and 5.2.18, Proposition 5.2.14), and applications to Q-factors (Propositions 5.3.1–5.3.2, the latter needing β > 0), structural estimation and Epstein–Zin savings (Algorithm 5.1) | [Chapter overview](GeneralStates/ADPTransformations/README.md) |
| [GeneralStates/LinearDecisionProcesses](GeneralStates/LinearDecisionProcesses/README.md) | II.6 Linear Decision Processes | 309 theorems: weak and strong Feller kernels (Example 6.1.1, Lemma 6.1.1 with Scheffé's lemma, Example 6.1.2), linear decision processes as additive ADPs with lifetime values (6.6), finite and Feller LDPs (Propositions 6.1.2–6.1.3, regularity in the finite case by pasting policies), exogenous discount processes (Lemma 6.1.4 as a path expectation, Lemma 6.1.5, Exercise 6.1.1, Proposition 6.1.6 with a measurable discount operator), general-state MDPs (Proposition 6.1.7, Example 6.1.8), and natural resource management, stochastic returns and mortality (Proposition 6.2.1, §6.2.2, Exercise 6.2.1), with Berge's theorem and a Borel selection proved for interval correspondences | [Chapter overview](GeneralStates/LinearDecisionProcesses/README.md) |

## Scope

The plan is in [PROPOSAL-SargentStachurski.md](PROPOSAL-SargentStachurski.md):
nineteen chapter projects built one at a time, in book order. Volume 1 works
on a finite state space, where value functions are vectors and the Bellman
operator acts on `ℝ^X`; Volume 2 moves to general state spaces, bounded
functions, Banach spaces and partially ordered sets.

Where the book argues from a figure, the Lean statement is a theorem with
explicit hypotheses. Where the book leaves a hypothesis implicit, it is
stated. Where the book's claim is false or imprecise as printed, the corrected
statement is proved and the change is recorded in that project's
`docs/corrections.md`. The provable exercises are formalised; computational
exercises and code listings are not.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.12+. Each project
pins Lean and Mathlib `v4.34.0`, and its Lake manifest pins transitive
dependencies. From the repository root:

```sh
cd FiniteStates/JobSearch
lake exe cache get
python scripts/verify.py
```

The verifier builds the complete project, freshly recompiles every contributed
proof without importing its compiled project module, and audits each named
declaration's transitive axioms. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Warnings, failed proofs, or placeholder axioms fail
the check. Every file carries the Apache 2.0 header that Mathlib's header linter
checks. GitHub Actions runs every project independently on pushes and pull
requests. The generated `verification/verification.json` records source hashes
and axiom lists. Proof checking happens in Lean's kernel; the JSON is a record
of a run.

The layout follows
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Each project is self-contained: a lemma needed by more than one chapter is
copied into each project that uses it, rather than shared through a
cross-project dependency.

## Development and provenance

These contributions are developed with **Claude Code** (Anthropic), under the
direction of Robert Kirkby. The books are cited by result, equation and page
number and are not reproduced; see each project's `THIRD_PARTY_NOTICES.md`.

## License

Apache License 2.0; see [LICENSE](LICENSE).
