# Miao Chapter 14: Neoclassical Growth Models, in Lean

This is the `EconomicDynamics/NeoclassicalGrowth` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 14 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 14 builds the neoclassical growth model up to the real business cycle model: the Ramsey
model and its decentralisations, fiscal policy, the basic RBC model, and extensions with other
utility functions, capacity utilisation, capital and investment adjustment costs, and stochastic
trends. The chapter's content is mostly derivations; every numbered result (Propositions 14.1.1
and 14.3.1) and every derivation the text carries out is proved — equilibrium conditions and the
equivalence of decentralisations with the planner, steady states (existence, uniqueness,
comparative statics), the log-linearised systems and their saddle paths, detrending — as is the
mathematical content of Exercises 1–7. Calibration, Dynare runs, impulse-response figures and
data comparisons are not formalised. The corrections are recorded in
[corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **734 theorems**; 383 of them are carried
over from Chapters 1, 2 and 8.

* **The Ramsey model** (§14.1.1): both Inada conditions are misprinted as impossible limits
  (`rm_inada_u_misprint`, `rm_inada_F_misprint`); Arrow–Debreu, household-capital and
  firm-capital decentralisations and the planner give the same allocations (`rm_ad_of_hh`,
  `eq_14_14_iff_eq_14_7`, `rm_ce_planner`); the steady state exists uniquely with its comparative
  statics (`rm_steady_ratio_exists_unique`, `rm_cs_beta`); the saddle path, with eigenvalues
  `0 < λ₁ < 1 < λ₂` and monotone convergence (`rm_lin_saddle`, `rm_lin_saddle_monotone`).
* **Fiscal policy** (§14.1.2): **Proposition 14.1.1**, whose proof drops `(1 − τᵈ)`
  (`proposition_14_1_1`, `rm_prop_14_1_1_misprint`); a permanent distribution tax is neutral and a
  temporary one distorts (`rm_distribution_tax_neutral`, `rm_temporary_distribution_tax_distorts`);
  Ricardian equivalence (`rm_ricardian`); the printed government budget contradicts Walras' law
  (`rm_gov_budget_misprint`); Exercises 1–2 (`ex_14_1`, `ex_14_2`).
* **The basic RBC model** (§14.2): planner and competitive equilibrium, with a concrete instance
  (`rb_planner_optimal`, `rb_sce_iff`, `rb_bm_sce`); the steady state and calibration, where the
  stated parameters give `χ ≈ 1.778`, not 1.75 (`rb_ss_exists_unique`, `rb_calib_chi_ne`); the
  log-linearised system with a sign error in (14.34) corrected (`eq_14_34_C`,
  `eq_14_34_printed_false`), the deterministic and stochastic saddle paths via Blanchard–Kahn
  (`rb_saddle_det`, `rb_saddle_stoch`), and the stock return (`rb_stock_return_printed_false`).
* **Utility functions** (§14.3.1): KPR preferences and balanced growth, the Frisch elasticity,
  the Hansen–Rogerson lottery, GHH preferences outside the KPR class (`rb_u38_bgp`,
  `rb_u39_frisch`, `rb_lottery`, `rb_ghh_not_kpr`).
* **Capacity utilisation and adjustment costs** (§14.3.2–14.3.3): utilisation amplifies TFP
  shocks (`rx_cu_amplification`); **Proposition 14.3.1** (Hayashi: marginal Q = average Q,
  `proposition_14_3_1`, `proposition_14_3_1_marginal`); the three decentralisations, where
  Exercise 5 fails for producer-owned adjustment unless the rents are returned
  (`ex_14_5_dec3_counterexample`, `ex_14_5_dec3_corrected`); investment dynamics (`ex_14_6_differences`).
* **Stochastic trends** (§14.3.4): detrending and the detrended steady state
  (`rx_detrend_euler`, `rx_trend_steady_exists`), investment-specific shocks (`rx_ist_price`).

All names are in the namespace `Miao.NeoclassicalGrowth`. The Chapter 1 and 2 modules are copied
from [EconomicDynamics/DifferenceEquations](../DifferenceEquations/README.md) and
[EconomicDynamics/RationalExpectations](../RationalExpectations/README.md); `RXCopied` from
[EconomicDynamics/Applications](../Applications/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DeterministicBasics](NeoclassicalGrowth/DeterministicBasics.lean) | 3 | Definitions of Chapter 1 (from Chapter 1) |
| [Triangular](NeoclassicalGrowth/Triangular.lean) | 14 | Powers of triangular matrices (copied and extended) |
| [Spectral](NeoclassicalGrowth/Spectral.lean) | 16 | Stable and unstable subspaces (copied) |
| [RealSplitting](NeoclassicalGrowth/RealSplitting.lean) | 24 | The real splitting `E_s ⊕ E_u` and its dimension (copied) |
| [Dichotomy](NeoclassicalGrowth/Dichotomy.lean) | 16 | Projections and geometric bounds (copied) |
| [LinearSystems](NeoclassicalGrowth/LinearSystems.lean) | 28 | §1.4: stable matrices, regularity, the steady state (1.21) (from Chapter 1) |
| [BlockSplit](NeoclassicalGrowth/BlockSplit.lean) | 9 | The real block split replacing the Jordan form, and its existence (from Chapter 1) |
| [Nonsingular](NeoclassicalGrowth/Nonsingular.lean) | 35 | §1.4.1: Theorems 1.4.1–1.4.2, Corollary 1.4.1, the stable manifold (from Chapter 1) |
| [Basics](NeoclassicalGrowth/Basics.lean) | 8 | `CondExpSystem`, adapted and stable processes, the system (2.11) (from Chapter 2) |
| [BKStable](NeoclassicalGrowth/BKStable.lean) | 43 | §2.3: stable processes, (2.12), the jump-only system (from Chapter 2) |
| [StochasticBK](NeoclassicalGrowth/StochasticBK.lean) | 35 | §2.3.1: Blanchard–Kahn, Corollary 1.4.1, Theorem 1.4.3, certainty equivalence (from Chapter 2) |
| [NewKeynesian](NeoclassicalGrowth/NewKeynesian.lean) | 34 | Example 2.3.1 and Exercise 2 (from Chapter 2) |
| [Scalar](NeoclassicalGrowth/Scalar.lean) | 61 | §1.1: scalar first-order equations, Examples 1.1.1–1.1.2 (from Chapter 1) |
| [PhaseDiagram](NeoclassicalGrowth/PhaseDiagram.lean) | 39 | §1.5, and a 2×2 saddle toolkit (from Chapter 1) |
| [Nonlinear](NeoclassicalGrowth/Nonlinear.lean) | 16 | §1.6: optimal growth, periodic points, the logistic map (from Chapter 1) |
| [RMBasics](NeoclassicalGrowth/RMBasics.lean) | 17 | Primitives of the basic Ramsey model |
| [RMPlanner](NeoclassicalGrowth/RMPlanner.lean) | 9 | The social planner's problem of the basic Ramsey model |
| [RMDecentral](NeoclassicalGrowth/RMDecentral.lean) | 20 | Decentralisations of the basic Ramsey model |
| [RMSteady](NeoclassicalGrowth/RMSteady.lean) | 16 | The steady state of the basic Ramsey model |
| [RMDynamics](NeoclassicalGrowth/RMDynamics.lean) | 8 | Dynamics of the detrended Ramsey model: phase diagram and saddle path |
| [RMFiscal](NeoclassicalGrowth/RMFiscal.lean) | 16 | Incorporating fiscal policy |
| [RMExercises](NeoclassicalGrowth/RMExercises.lean) | 10 | Exercises 14.1 and 14.2 |
| [RBModel](NeoclassicalGrowth/RBModel.lean) | 23 | The basic RBC model: technology, preferences and the static first-order conditions |
| [RBPlanner](NeoclassicalGrowth/RBPlanner.lean) | 9 | The stochastic planner's problem of the basic RBC model |
| [RBEquilibrium](NeoclassicalGrowth/RBEquilibrium.lean) | 6 | The decentralised equilibrium of the basic RBC model |
| [RBSteadyState](NeoclassicalGrowth/RBSteadyState.lean) | 23 | The nonstochastic steady state of the basic RBC model |
| [RBLogLinear](NeoclassicalGrowth/RBLogLinear.lean) | 26 | The log-linearised basic RBC model |
| [RBSaddle](NeoclassicalGrowth/RBSaddle.lean) | 20 | The phase diagram and the saddle path of the log-linearised RBC model |
| [RBBlanchardKahn](NeoclassicalGrowth/RBBlanchardKahn.lean) | 5 | The stochastic saddle path of the log-linearised RBC model (Blanchard–Kahn) |
| [RBUtility](NeoclassicalGrowth/RBUtility.lean) | 20 | Various utility functions in the RBC model |
| [RXCopied](NeoclassicalGrowth/RXCopied.lean) | 2 | Partial derivatives and Euler's theorem (copied) |
| [RXTree](NeoclassicalGrowth/RXTree.lean) | 16 | The event tree of §14.3 |
| [RXCapacity](NeoclassicalGrowth/RXCapacity.lean) | 20 | §14.3.2 Capacity utilization and Exercise 14.3 |
| [RXAdjustment](NeoclassicalGrowth/RXAdjustment.lean) | 35 | §14.3.3 Capital adjustment costs: the planner and the three decentralisations |
| [RXHayashi](NeoclassicalGrowth/RXHayashi.lean) | 11 | Proposition 14.3.1 (Exercise 14.4): marginal Q equals average Q |
| [RXInvestment](NeoclassicalGrowth/RXInvestment.lean) | 22 | Investment adjustment costs (14.50)–(14.52) and Exercise 14.6 |
| [RXTrend](NeoclassicalGrowth/RXTrend.lean) | 19 | §14.3.4 Stochastic trends |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
