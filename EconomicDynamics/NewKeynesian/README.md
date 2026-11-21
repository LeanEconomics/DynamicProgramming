# Miao Chapter 19: Dynamic New Keynesian Models, in Lean

This is the `EconomicDynamics/NewKeynesian` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 19 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 19 develops the dynamic New Keynesian model: households, Dixit–Stiglitz aggregation and
Calvo pricing, the log-linearised three-equation system and its determinacy, optimal monetary
policy (the efficient allocation, the quadratic approximation to welfare, commitment, the
timeless perspective and discretion), and fiscal stimulus at the zero lower bound. The chapter
states no numbered results; every derivation the text carries out and Exercises 1–5 are proved,
log-linearisations as derivatives along paths through the steady state and second-order
approximations as Taylor statements with explicit remainders. The medium-scale model of §19.4
(and Exercise 6, its steady state and log-linearisation) is listed only, as decided for this
library. The corrections are recorded in [corrections](docs/corrections.md), and every book item
is located in the [source map](docs/source-map.md). The library contains **742 theorems**; 458 of
them are carried over from Chapters 1, 2 and 9.

* **The basic DNK model** (§19.1): household and firm conditions, the Dixit–Stiglitz demand and
  price index, Calvo reset prices and price dispersion (`eq_19_3`, `eq_19_6`, `eq_19_7`,
  `eq_19_11`, `eq_19_17`); natural output (`eq_19_18`); the log-linearised Phillips curve and IS
  curve (`eq_19_25`, `nk_kappa_pos`, `eq_19_26`, `eq_19_29`); the satiation assumption fails for
  (19.1) (`nk_u_no_satiation`). **Exercise 1** (Bullard–Mitra): (19.31) is necessary and
  sufficient for determinacy when the rule's coefficients are nonnegative, with a second branch
  otherwise (`ex_19_1`, `ex_19_1_exact`, `ex_19_1_not_necessary`).
* **Monetary policy design** (§19.2): the efficient allocation and the employment subsidy
  (`mp_subsidy`, `mp_flex_subsidy_efficient`); the second-order approximation (19.30) and the loss
  function (`eq_19_30`, `mp_h_expansion`, `mp_step3`); strict inflation targeting
  (`mp_strict_targeting`); commitment, the timeless perspective and discretion, with the printed
  discretionary-inflation coefficient and price-level law corrected (`mp_commit_rule`,
  `eq_19_35`, `mp_inflation_bias`, `mp_discretion_printed_false`,
  `mp_price_level_printed_false`). **Exercise 2** is false with a constant intercept unless the
  natural rate is constant, and holds with the natural-rate rule (`mp_printed_rule_counterexample`,
  `ex_19_2`).
* **Fiscal stimulus** (§19.3): the neoclassical multiplier, where the book's `v″ < 0` allows a
  multiplier above one (`eq_19_41`, `fs_eq_19_41_vpp_neg`); the New Keynesian multiplier
  (`eq_19_52`); the zero lower bound, (19.55) with `μ < μ̄` (`eq_19_55_iff`), the short-run
  multipliers (`eq_19_60`, `fs_thetaG_tendsto_atTop`); the duration of stimulus (19.61), with
  the printed `ϑ_π` corrected (`eq_19_61`, `fs_thetaPi_printed_ne`); optimal government purchases
  (`fs_optimal_GL`, `fs_zero_gap_printed`); Exercises 3–5 (`ex_19_3`, `ex_19_4`, `ex_19_5`).

All names are in the namespace `Miao.NewKeynesian`. The Chapter 1–2 modules are copied from
[EconomicDynamics/DifferenceEquations](../DifferenceEquations/README.md) and
[EconomicDynamics/RationalExpectations](../RationalExpectations/README.md), the `CP*` modules from
[EconomicDynamics/LinearQuadratic](../LinearQuadratic/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DeterministicBasics](NewKeynesian/DeterministicBasics.lean) | 3 | Definitions of Chapter 1 (from Chapter 1) |
| [Triangular](NewKeynesian/Triangular.lean) | 14 | Powers of triangular matrices (copied and extended) |
| [Spectral](NewKeynesian/Spectral.lean) | 16 | Stable and unstable subspaces (copied) |
| [RealSplitting](NewKeynesian/RealSplitting.lean) | 24 | The real splitting `E_s ⊕ E_u` and its dimension (copied) |
| [Dichotomy](NewKeynesian/Dichotomy.lean) | 16 | Projections and geometric bounds (copied) |
| [LinearSystems](NewKeynesian/LinearSystems.lean) | 28 | §1.4: stable matrices, regularity, the steady state (1.21) (from Chapter 1) |
| [BlockSplit](NewKeynesian/BlockSplit.lean) | 9 | The real block split replacing the Jordan form, and its existence (from Chapter 1) |
| [Nonsingular](NewKeynesian/Nonsingular.lean) | 35 | §1.4.1: Theorems 1.4.1–1.4.2, Corollary 1.4.1, the stable manifold (from Chapter 1) |
| [QZ](NewKeynesian/QZ.lean) | 27 | Definition 1.4.6, Theorem 1.4.4 (generalized Schur form) (from Chapter 1) |
| [Singular](NewKeynesian/Singular.lean) | 48 | §1.4.2: Theorem 1.4.5 (Klein), the Cagan example, augmentation (from Chapter 1) |
| [Basics](NewKeynesian/Basics.lean) | 8 | `CondExpSystem`, adapted and stable processes, the system (2.11) (from Chapter 2) |
| [CondExpL1](NewKeynesian/CondExpL1.lean) | 13 | The `L¹` conditional expectations as a `CondExpSystem` (from Chapter 2) |
| [ScalarRE](NewKeynesian/ScalarRE.lean) | 59 | §2.2: lag operators, (2.3)–(2.10), Example 2.2.1, undetermined coefficients (from Chapter 2) |
| [BKStable](NewKeynesian/BKStable.lean) | 43 | §2.3: stable processes, (2.12), the jump-only system (from Chapter 2) |
| [StochasticBK](NewKeynesian/StochasticBK.lean) | 35 | §2.3.1: Blanchard–Kahn, Corollary 1.4.1, Theorem 1.4.3, certainty equivalence (from Chapter 2) |
| [NewKeynesian](NewKeynesian/NewKeynesian.lean) | 34 | Example 2.3.1 and Exercise 2 (from Chapter 2) |
| [CPRamsey](NewKeynesian/CPRamsey.lean) | 12 | Optimal policy under commitment: the Ramsey problem and its first-order conditions (from Chapter 9) |
| [CPNKCommitment](NewKeynesian/CPNKCommitment.lean) | 25 | The New Keynesian model under commitment: Examples 9.4.1 and 9.4.2 (from Chapter 9) |
| [CPNKDiscretion](NewKeynesian/CPNKDiscretion.lean) | 9 | The New Keynesian model under discretion: Example 9.5.1, and commitment versus discretion (from Chapter 9) |
| [NKHouseholds](NewKeynesian/NKHouseholds.lean) | 14 | The basic DNK model: households (Miao §19.1.1) |
| [NKFinalGoods](NewKeynesian/NKFinalGoods.lean) | 10 | The basic DNK model: final goods firms (Miao §19.1.2) |
| [NKIntermediate](NewKeynesian/NKIntermediate.lean) | 10 | The basic DNK model: intermediate goods firms and Calvo pricing (Miao §19.1.3) |
| [NKEquilibrium](NewKeynesian/NKEquilibrium.lean) | 7 | The basic DNK model: aggregation, the Taylor rule and the sticky price equilibrium |
| [NKFlexPrice](NewKeynesian/NKFlexPrice.lean) | 4 | The basic DNK model: the flexible price equilibrium (Miao §19.1.6) |
| [NKLogLinear](NewKeynesian/NKLogLinear.lean) | 17 | The basic DNK model: log-linearising the equilibrium conditions (Miao §19.1.7) |
| [NKPhillips](NewKeynesian/NKPhillips.lean) | 15 | The New Keynesian Phillips curve and the IS curve (Miao §19.1.7) |
| [NKDeterminacy](NewKeynesian/NKDeterminacy.lean) | 14 | Determinacy of the basic DNK model: Exercise 19.1 (Bullard–Mitra) |
| [MPEfficient](NewKeynesian/MPEfficient.lean) | 19 | Monetary policy design: the efficient allocation (Miao §19.2.1) |
| [MPDispersion](NewKeynesian/MPDispersion.lean) | 19 | Monetary policy design: price dispersion to second order (Miao §19.2.2, Step 1) |
| [MPQuadratic](NewKeynesian/MPQuadratic.lean) | 16 | Monetary policy design: the quadratic approximation to utility (Miao §19.2.2) |
| [MPPolicy](NewKeynesian/MPPolicy.lean) | 33 | Monetary policy design: commitment versus discretion (Miao §19.2.3) |
| [MPTaylorRule](NewKeynesian/MPTaylorRule.lean) | 8 | Implementing strict inflation targeting: the Taylor principle (19.31) and Exercise 19.2 |
| [FSNeoclassical](NewKeynesian/FSNeoclassical.lean) | 13 | Fiscal stimulus: the neoclassical benchmark and monopolistic competition |
| [FSDNK](NewKeynesian/FSDNK.lean) | 23 | Fiscal stimulus in a DNK model: the Phillips curve and the Taylor-rule multiplier |
| [FSZLB](NewKeynesian/FSZLB.lean) | 25 | Fiscal stimulus at the zero lower bound |
| [FSDuration](NewKeynesian/FSDuration.lean) | 15 | Duration of fiscal stimulus: the three-state example and the multiplier (19.61) |
| [FSWelfare](NewKeynesian/FSWelfare.lean) | 22 | Government purchases and welfare |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
