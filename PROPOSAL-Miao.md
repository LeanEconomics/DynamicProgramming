# Proposal: Miao, *Economic Dynamics in Discrete Time*, in Lean

**Source.** Jianjun Miao, *Economic Dynamics in Discrete Time*, MIT Press, 2014: 22 chapters
in four parts, plus four mathematical appendices. The PDF in
`~/Dropbox/Papers_and_Textbooks/Various Textbooks/` is the author's draft of 21 April 2013
(926 pages, with a text layer). Its section and result numbers are those of the draft, and
its page numbers differ from the printed book. Citations give the result number and the
draft page. Nothing from the book is reproduced in the repository.

**Target.** This repository, `LeanEconomics/DynamicProgramming`, alongside the Sargent and
Stachurski, Stokey–Lucas–Prescott and Meyn–Tweedie projects. Same conventions as
`PROPOSAL-SargentStachurski.md` §1–2: one independent Lean/Mathlib v4.34.0 project per
chapter, built one chapter at a time, each with a README library map, `docs/source-map.md`,
`docs/corrections.md`, `proof-manifest.json` and the `scripts/verify.py` audit; a CI matrix
entry; a row in the root README.

Status: decisions settled 2026-11-05 (§3); Chapters 1–2 done 2026-11-05, Chapters 3–5 done 2026-11-07, Chapter 6 done 2026-11-07, Chapters 7–9 done 2026-11-08, Chapters 10–11 done 2026-11-10.

---

## 1. Layout and conventions

```
DynamicProgramming/
└── EconomicDynamics/             one project per chapter
```

- **Folder** `EconomicDynamics/`; projects named after the chapter's subject.
- **Namespace** `Miao.<Project>`.
- **Citations** in docstrings as `Miao, Thm 4.1.1, p. 115`; every numbered result and every
  exercise appears in `docs/source-map.md`, either formalised or listed with a reason.
- **What is formalised.** The book is lighter on theorems than Sargent–Stachurski or SLP
  (about 260 numbered definitions and results in all) and heavier on derivations. A
  derivation the text carries out (a steady state, a log-linearised system, a closed-form
  policy, a set of equilibrium conditions) is stated and proved as a theorem. Dynare and
  Matlab sections, simulations, figures and calibrated numbers are not formalised.
- **Re-prove everything** from the book, in the book's setting. Copying from this
  repository's other projects is allowed and marked (`Copied from RecursiveMethods/<Project>`);
  each project stays self-contained.
- **Exercises.** Every provable exercise is formalised.
- **Corrections.** Where the book's claim is false or imprecise as printed, the corrected
  statement is proved and the change recorded in `docs/corrections.md`.
- **Branches** `miao-chN-<name>`, stacked in book order, the first one on `origin/main`;
  committed only after `scripts/verify.py` passes; never pushed by the assistant.
- **Worktree.** The main checkout is in use by the SetValuedFixedPoints work, on branch
  `ext-set-valued-fixed-points`. This programme runs in its own worktree under
  `~/.cache/lean-builds/worktrees/`, with the shared Mathlib build cache.

---

## 2. Chapter projects

| Ch | Project | Content | Reuse, infrastructure and risks |
| ---: | --- | --- | --- |
| 1 | `DifferenceEquations` | Scalar first- and second-order linear equations, lag operators, nonsingular systems (Blanchard–Kahn, Thms 1.4.1–1.4.3), singular systems (the complex generalised Schur form, Thm 1.4.4, and Klein's method, Thm 1.4.5), phase diagrams, the optimal-growth linearisation and the logistic two-cycle, Exercises 1–2 | **Mathlib has no Schur triangulation and no QZ decomposition: both are built here** (decision 3). The Jordan form is replaced by the real stable/unstable splitting copied from `RecursiveMethods/DeterministicDynamics` |
| 2 | `RationalExpectations` | Stochastic linear systems, scalar models by lag operators and by undetermined coefficients, Blanchard–Kahn (Thm 2.3.1 existence and uniqueness), Klein and Sims methods, the perturbation view of nonlinear models | The QZ decomposition is copied from Chapter 1 |
| 3 | `MarkovProcesses` | Classification of states, stationary distributions, countable chains, general Markov processes, strong (total variation) and weak convergence | Copies from `RecursiveMethods/StrongConvergence`, `WeakConvergence` and `StochasticStability` |
| 4 | `ErgodicTheory` | Birkhoff's theorem and the maximal ergodic lemma, the SLLN for stationary processes, mixing implies ergodic, ergodic decomposition of invariant measures for Markov processes (Thms 4.3.1–4.3.2) | Birkhoff copied from `StochasticStability/LimitTheorems` |
| 5 | `MarkovDecisionProcesses` | The model setup, discrete choice, optimal stopping, bandits (the Gittins index), optimal control | The Gittins-index optimality is the main new proof |
| 6 | `FiniteHorizonDP` | The principle of optimality, the measurability issue, optimal control, the maximum principle, the secretary problem, consumption–saving | Measurable selection copied from SLP Ch 9 / S&S Vol 2 Ch 6 |
| 7 | `InfiniteHorizonDP` | The principle of optimality, bounded and unbounded rewards, the maximum principle and transversality, Euler equations with transversality | Copies from `RecursiveMethods/DeterministicDP` and `StochasticDP` |
| 8 | `Applications` | Option exercise, discrete choice, consumption and saving (deterministic and stochastic income, Lemmas and Props of §8.3), portfolio choice, inventory (s, S), investment and Q theory | The largest application chapter |
| 9 | `LinearQuadratic` | Finite-horizon LQ and the Riccati recursion, infinite-horizon limits, optimal policy under commitment and discretion, robust control | Copies from `GeneralStates/AbstractDecisionProcesses` (LQ) |
| 10 | `PartialInformation` | The Kalman filter, hidden Markov chains and the Hamilton filter, control under partial information, LQ with partial information | Kalman proved as recursive linear least-squares projection, so it does not need multivariate Gaussian conditioning |
| 11 | `NumericalMethods` | Only the theorems: Gaussian quadrature exactness, Chebyshev interpolation (Thm 11.3.1), spline interpolation, Tauchen and Rouwenhorst discretisations (moment matching), convergence of discretised value function iteration | Algorithms themselves are not formalised |
| 12 | `StructuralEstimation` | Consistency and asymptotic normality of GMM (Thms 12.1.1–12.1.2) and of ML; SMM and indirect inference as stated | Uniform laws of large numbers are a likely gap; may be stated hypotheses |
| 13 | `CompleteMarkets` | Pareto optima, the two welfare theorems, Arrow–Debreu and Radner equilibria and their equivalence, no-arbitrage and complete markets, bubbles under debt constraints, recursive asset pricing | Copies from `RecursiveMethods/ParetoOptimaEquilibria` |
| 14 | `NeoclassicalGrowth` | Ramsey model (steady state, saddle path, fiscal policy), the basic RBC model and its extensions as equilibrium-condition theorems | Uses Ch 1–2 |
| 15 | (none) | Bayesian estimation with Dynare: computational | Listed in the root README as not formalised |
| 16 | `OverlappingGenerations` | Exchange OLG (Samuelson and classical cases, Props 16.1.1–16.1.3), production OLG (Diamond), bubbles | |
| 17 | `IncompleteMarkets` | Income fluctuation problem, Aiyagari stationary equilibrium, Bewley models with fiat money, interest on currency and seigniorage (Props 17.2.1–17.2.3), recursive equilibrium with aggregate shocks | Existence of stationary equilibrium via Brouwer, copied from `RecursiveMethods/EquilibriaWithDistortions`; the Krusell–Smith method is an algorithm and is not formalised |
| 18 | `SearchAndMatching` | The DMP model (existence and uniqueness of steady state, comparative statics), endogenous job destruction, business-cycle dynamics | |
| 19 | `NewKeynesian` | The basic DNK model, the log-linearised system and determinacy (Taylor principle via Blanchard–Kahn), the quadratic welfare approximation, commitment versus discretion, fiscal multipliers | Uses Ch 2; the medium-scale model §19.4 is listed only |
| 20 | `RecursiveUtility` | Koopmans utility (Thms 20.1.1–20.1.2), Epstein–Zin, ambiguity aversion, temporal resolution, concavity and risk aversion, utility gradients, Pareto optimality (Lucas–Stokey, Dumas–Wang–Uppal) | Copies from `FiniteStates/RecursiveDecisionProcesses` |
| 21 | `DynamicGames` | Repeated games: one-shot deviation, APS self-generation, factorisation, the maximal fixed point, compactness (Lemmas and Thms 21.1.x), simple strategies; dynamic stochastic games; the fish war; credible government policies (§21.4) | APS is new to the repository |
| 22 | `RecursiveContracts` | Limited commitment (dynamic programming and Lagrangian methods), hidden action and the inverse Euler equation, hidden information and long-run poverty (Prop 22.3.4) | |

Appendices A–D are covered by Mathlib and get no project. Results the chapters need from them
are proved where they are used.

---

## 3. Decisions (settled by the user, 2026-11-05)

1. **Folder and namespace:** `EconomicDynamics/` and `Miao.<Project>`.
2. **The computational chapters:** only the theorems in Chapters 11–12; Chapter 15 is skipped.
3. **QZ decomposition:** built, not assumed. It is Theorem 1.4.4, so it is built in Chapter 1.
4. **Citations:** the 2013 draft's pages.
5. **Order:** Chapter 1 first, then book order.
