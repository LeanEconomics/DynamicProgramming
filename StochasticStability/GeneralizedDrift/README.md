# Meyn and Tweedie, Chapter 19: Generalized Classification Criteria, in Lean

This is the `StochasticStability/GeneralizedDrift` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 19 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 482–509, together with Appendix B.2, the complete classification of
the scalar SETAR model, pp. 540–542 (and the glossary of drift conditions of §B.1, pp. 538–540,
which it summarises). Run the commands below from this directory. [Return to the library
index](../../README.md).

Chapter 19 ends the book's treatment of drift criteria with three generalisations of the one-step
drift `ΔV(x) = ∫ P(x, dy)[V(y) − V(x)]`. §19.1 lets the number of steps `n(x)` after which the
drift is examined depend on the state. The embedded chain `Φ̂ₖ = Φ_{s(k)}` with kernel
`P̂(x, ·) = P^{n(x)}(x, ·)` ((19.2)–(19.5)) gives state-dependent criteria for Harris recurrence
(Theorem 19.1.1), for positive Harris recurrence with the hitting-time bound (19.11) (Theorem
19.1.2) and for geometric ergodicity (Theorem 19.1.3). They are applied to the reflected random
walk on `ℝ²₊` (Theorem 19.1.4, with the linear bound (19.25)) and to an invasion/antibody model on
`ℤ²₊` (§19.1.3). §19.2 replaces `V(Φₖ)` by an adapted sequence `Vₖ(Φ₀, …, Φₖ)` and proves
history-dependent criteria for regularity (Theorem 19.2.1), for an infinite mean return time
(Theorem 19.2.2), for `f`-geometric ergodicity of T-chains (Theorem 19.2.3), for non-evanescence
and Harris recurrence (Theorem 19.2.4) and for transience (Theorem 19.2.5). Theorem 19.2.6 applies
them to the dependent parameter bilinear model, which is geometrically ergodic and obeys the LLN,
the CLT and the LIL. §19.3 studies drifts that change sign. Under increments bounded in mean
(19.46), a negative limiting average of the drift off a petite set gives positivity (Theorem
19.3.1), the `π`-average of the drift vanishes (Theorem 19.3.2), and it is negative off a sublevel
set (Theorem 19.3.3), so that (19.48) characterises positivity. For the ladder chain with
homogeneous zero-level transitions (19.65), the average drift condition (19.68) gives positivity
(Theorem 19.3.4); the up-or-down ladder (19.78)–(19.80) shows what can happen without (19.65); and
Theorem 19.3.5 recovers the stability condition `λ > µ` of the GI/G/1 queue. Appendix B.2 assembles
the classification of the SETAR model into a regular interior, null recurrent margins and a
transient exterior from results of Chapters 6, 8, 9 and 11.

Every numbered result of Chapter 19 is formalised: Theorems 19.1.1–19.1.4, Theorems 19.2.1–19.2.6
and Theorems 19.3.1–19.3.5, together with the claims of the text about the walk on `ℝ²₊`, the
invasion model, the bilinear model, the ladder examples (19.78)–(19.80) and the GI/G/1 queue, and
the classification of Appendix B.2. Six claims are false as printed. Each is refuted in Lean by a
counterexample of this project, and a corrected statement is proved. Theorems 19.1.1–19.1.3 allow
`n(x) = 0`, and Theorem 19.1.2 then fails (`theorem_19_1_2_counterexample`); the three theorems are
proved for `n ≥ 1`. The bound (19.25) fails at the origin (`theorem_19_1_4_counterexample`); the
bound `c(1 + x⁺ + y⁺)` for the hitting time of a square is proved (`theorem_19_1_4_linear`). The
`δ_{(0,0)}`-irreducibility claimed on p. 487 needs independent coordinates
(`orthant_not_irreducible_counterexample`); Theorem 19.1.4 is proved under a joint condition that
independence implies. The test function that p. 498 calls coercive is not when `α = 0`
(`dbl_bookV_not_coercive`); Theorem 19.2.6 is proved with a modified test sequence. STEP 2 of
Appendix B.2 claims (V4) with linear test functions in the whole interior, which fails at a
unit-slope end (`setar_not_linear_driftV4_top`, `setar_not_linear_driftV4_bot`); (V4) and geometric
ergodicity are proved on (11.36). The busy-period decomposition (19.84) is false for the GI/G/1
queue (`eq_19_84_counterexample`); the second part of Theorem 19.3.5 is proved by Wald's bound
(`theorem_19_3_5_ii`). Further corrections concern proofs and remarks. (19.50) has `Pⁿ` for `Pᵏ`
and p. 498 has `3ε³Aₖ²` for `3ε³Aₖ`. The justification of (19.77) does not hold, and the
`δ_{(0,0)}`-irreducibility of the invasion model does not follow from (A1)–(A3). The printed
left-continuity (19.29) is too weak for the book's own `(j + 1)`-step bound and is read in each
coordinate. The bottom rung of p. 506 is not petite for (19.79) either, even when that chain is
positive (`exLadder_rung_zero_not_petite`). The mean return time in (19.81) is `1/(1 − 2q)`, not
`(1 − q)/(1 − 2q)`; the transience it serves is proved in quantified form (`eq_19_81_transient`).
Further points are made explicit. A countably generated σ-algebra is assumed where the Harris and
positivity theory of the earlier chapters is used; conditional drift conditions are stated in
integrated form under every `P_x`; the topological hypotheses of §19.2 are spelled out; the
irreducibility, aperiodicity and T-chain property of the bilinear model and the irreducibility of
the invasion model are hypotheses; and the rung position of the ladder chain lives in `ℝ`. The
following are not formalised: the general form (19.1); the book's state-dependent drift
construction for the walk on `ℝ²₊`, (19.21)–(19.24); the geometric ergodicity sketch for the
invasion model, (19.30)–(19.31); (19.77) for general ladder chains; the bound (19.81) as printed;
the Blackwell bound (19.85); geometric ergodicity of the SETAR model off (11.36); the informal
remarks; and the commentary of §19.4. See [corrections](docs/corrections.md). The library contains
**3926 theorems**. Of these, 248 are in the 13 Chapter 19 modules. The other 3678 are in the 172
modules carried from earlier projects: all 131 modules of the Chapter 15 project
`GeometricErgodicity` (Chapters 1–11 and 13–15 and the renewal theory), and 41 modules copied from
the Chapter 17 project `LimitTheorems` (26), the Chapter 18 project `Positivity` (4), the Chapter 11
project `DriftRegularity` (4), the Chapter 14 project `FErgodicity` (6) and the Chapter 9 project
`HarrisRecurrence` (1).

Several routes differ from the book. Theorem 19.1.1 uses Theorem 9.1.3 and Proposition 9.1.7 in
place of the case analysis through Theorems 8.3.5 and 9.0.1. Theorem 19.1.4 uses Kingman's
quadratic test function with `n = 1` (the alternative of the Commentary, p. 508) instead of the
state-dependent construction, and the linear bound uses its square root and Jensen's inequality.
Theorem 19.2.5 needs only the submartingale inequality, not Kolmogorov's inequality. The three
conditional bounds that the book takes from [275] for Theorem 19.2.6 are proved, and its LLN, CLT
and LIL come from Theorem 17.0.1 through a (V4) function produced by the proof of Theorem 19.2.3.
(19.57) is derived from a Cesàro ergodic theorem for positive chains, where the book calls it
identical to (19.56). Theorem 19.3.4 truncates the ladder heights instead of the drifts. The second
part of Theorem 19.3.5 dominates the busy period by a random walk and applies Wald's bound, in
place of (19.77) and (19.84)–(19.85). The transience of the process on `[0]` for (19.80) is proved
with an exponential test function on the whole ladder and Proposition 8.4.1. Appendix B.2 adds
aperiodicity and geometric ergodicity on (11.36) (Theorem 15.0.1).

The chapter rests on ten groups of results.

* **State-dependent drift** (`StateDependentDrift`). The kernel `P̂` (`stateKernel`), the embedded
  times and path (`embTime`, `embPath`, `isStoppingTime_embTime`, `embPath_isMarkovChain`,
  `pathKernel_map_embPath`), (19.4) as `embTime_eq_sum` and (19.5) as
  `toENNReal_firstReturn_le_sumBefore`. Theorem 19.1.1 is `theorem_19_1_1` (supermartingale step
  `ae_hit_or_bdd`), Theorem 19.1.2 is `theorem_19_1_2` with (19.11) as
  `meanReturnTime_le_stateDrift` and the counterexample `theorem_19_1_2_counterexample`, and
  Theorem 19.1.3 is `theorem_19_1_3` with (19.19) as `kendallMoment_le_stateDrift`.
* **The walk on `ℝ²₊`** (`OrthantWalk`). The walk (19.20) (`orthantKernel`), irreducibility and
  small squares under a joint condition (`orthant_isPhiIrreducible`, `orthant_isSmall`,
  `exists_joint_neg_of_prod`), Kingman's quadratic drift (`orthant_drift_real`), Theorem 19.1.4 as
  `theorem_19_1_4`, (19.25) as `theorem_19_1_4_linear`, and the counterexamples
  `theorem_19_1_4_counterexample` and `orthant_not_irreducible_counterexample`.
* **The invasion model** (`InvasionModel`). The state-dependent drift with `n(0, j) = j + 1`
  (`invasion_stateDrift`), the bound `E_{(i,j)}[τ_C] ≤ (i + j)/β` (`invasion_meanReturnTime`) and
  positive Harris recurrence (`invasion_positiveHarris`).
* **History-dependent drift** (`HistoryDependentDrift`). Theorem 19.2.1 is `theorem_19_2_1` and
  `theorem_19_2_1_regular`, Theorem 19.2.2 is `theorem_19_2_2`, Theorem 19.2.3 is `theorem_19_2_3`
  with `theorem_19_2_3_driftV4`, Theorem 19.2.4 is `theorem_19_2_4` and `theorem_19_2_4_harris`
  (killed supermartingale `ae_bdd_of_avoid_seq`), and Theorem 19.2.5 is `theorem_19_2_5` and
  `theorem_19_2_5_transient`.
* **The bilinear model** (`BilinearDrift`, `BilinearLimits`). The pathwise bounds (19.42)–(19.45)
  (`abs_prod_le_prod_exp`, `abs_prod_theta_le`, `abs_prod_Ico_theta_le`, `dbl_Y_sq_le`), the
  conditional bounds (`dbl_condA`, `dbl_condB`, `dbl_condC`, `dbl_condY`), the drift (19.37)
  (`dblVs`, `dbl_drift`, `exists_dblLam_lt_one`), Theorem 19.2.6 as `theorem_19_2_6` and
  `theorem_19_2_6_limits`, and `dbl_bookV_not_coercive`.
* **Mixed drift** (`MixedDrift`). (19.49)–(19.50) (`integral_pow_driftR`,
  `eventually_cesaro_drift_ge`), Theorem 19.3.1 as `theorem_19_3_1`, Theorem 19.3.2 as
  `theorem_19_3_2`, the balanced flow (19.63) (`flow_balance`), (19.64) as
  `setIntegral_driftR_pos`, Theorem 19.3.3 as `theorem_19_3_3`, (19.57) as
  `tendsto_cesaro_setIntegral_driftR`, and the equivalence `theorem_19_3_3_iff`.
* **The ladder chain** (`LadderDrift`). (19.65) (`ladderStar`, `avgLadderKernel`), (19.66)
  (`avgLadderKernel_pow_map_snd`), (19.67) (`ladderBeta`, `truncBeta`), the drift of `V(i, w) = i`
  (`meanRung_add_truncBeta_le`), (19.70)/(19.74) (`cesaro_truncBeta_bound`), (19.75)
  (`tendsto_cesaro_low_of_isNull`), and Theorem 19.3.4 as `theorem_19_3_4`.
* **The up-or-down ladder** (`LadderExample`, `Ladder80Transience`). (19.78)–(19.79) (`exLam`),
  the marginal walk and its invariant law (`exMarg_hasInvariant_iff`), `β = 2(1 − q)` (`exBeta`),
  positivity for `q < ½ < p` (`exLadder_isPositive`), (19.80) (`ex80Star`), the bottom rung not
  petite (`ex80_rung_zero_not_petite`, `exLadder_rung_zero_not_petite`), and the transience of
  (19.81) in quantified form (`eq_19_81_transient`).
* **The GI/G/1 queue** (`GIG1Drift`, `GIG1Stability`). `β(x) = ∫ G(dt) E[N(t) | R₀ = x]`
  (`ladderBeta_gig1`), the invariance of the stationary forward recurrence law
  (`isInvariant_eqLaw_gig1`), (19.83) (`lintegral_ladderBeta_gig1`), Theorem 19.3.5 as
  `theorem_19_3_5` and `theorem_19_3_5_ii`, Wald's bound for the busy period (`tsum_wE_le`), and
  `eq_19_84_counterexample`.
* **The SETAR classification** (`SetarClassification`). The regions of Figures B.1–B.3
  (`SetarInterior`, `SetarMargin`, `SetarExterior`) and their partition (`setar_regions_cover`,
  `setar_regions_disjoint`), the classification `setar_classification`, aperiodicity
  (`setar_isAperiodic`), (V4) and geometric ergodicity on (11.36) (`setar_geometric_36`), and the
  failure of linear (V4) at unit slope (`setar_not_linear_driftV4_top`,
  `setar_not_linear_driftV4_bot`).

The library covers the chapter as follows.

* **Introduction** (pp. 482–483). The three generalisations, informal.
* **The state-dependent drift criteria** (§19.1.1). (19.2)–(19.19), Theorems 19.1.1–19.1.3 and
  the counterexample for `n = 0`.
* **Models on `ℝ²₊`** (§19.1.2). (19.20), the irreducibility claim and its counterexample, Theorem
  19.1.4 with (19.25), its counterexample and the corrected linear bound.
* **An invasion/antibody model** (§19.1.3). (A1)–(A3), (19.26)–(19.29) in a precise reading, the
  state-dependent drift, the hitting-time bound and positive Harris recurrence.
* **Generalized criteria for positivity and nullity** (§19.2.1). (19.32)–(19.35), Theorems 19.2.1
  and 19.2.2.
* **Generalized criteria for geometric ergodicity** (§19.2.2). (19.36)–(19.37), Theorem 19.2.3.
* **Generalized criteria for non-evanescence and transience** (§19.2.3). (19.38)–(19.40), Theorems
  19.2.4 and 19.2.5.
* **The dependent parameter bilinear model** (§19.2.4). (19.41)–(19.45), the conditional bounds,
  the drift and Theorem 19.2.6, with the coercivity counterexample.
* **The limiting-average drift** (§19.3.1). (19.46)–(19.64), Theorems 19.3.1–19.3.3.
* **The ladder chain** (§19.3.2). (19.65)–(19.75), Theorem 19.3.4, the examples (19.78)–(19.80)
  and the transience behind (19.81).
* **The GI/G/1 queue** (§19.3.3). (19.82)–(19.83), Theorem 19.3.5, the counterexample to (19.84).
* **Appendix B.2** (pp. 540–542). The regions of Figures B.1–B.3, STEPS 1–4, the STEP 2
  counterexample, aperiodicity and geometric ergodicity on (11.36).

All names are in the namespace `MeynTweedie.GeneralizedDrift`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

### The Chapter 19 modules (248 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [StateDependentDrift](GeneralizedDrift/StateDependentDrift.lean) | 34 | §19.1.1: the kernel `P̂` (19.2), the embedded times and path (19.3), their stopping-time and Markov properties, (19.4)–(19.5), (19.11) without irreducibility, Theorem 19.1.2 and its counterexample for `n = 0`, the supermartingale step and Theorem 19.1.1, the geometric increments, (19.19), Theorem 19.1.3 |
| [OrthantWalk](GeneralizedDrift/OrthantWalk.lean) | 18 | §19.1.2: the walk (19.20), reaching the origin from squares, `δ_{(0,0)}`-irreducibility and small squares under a joint condition, Kingman's quadratic drift, Theorem 19.1.4, the linear bound (19.25) corrected, the counterexamples to (19.25) and to the irreducibility claim, independent coordinates |
| [InvasionModel](GeneralizedDrift/InvasionModel.lean) | 4 | §19.1.3: the `m`-step interior drift, the state-dependent drift (19.10) with `n(0, j) = j + 1`, the hitting-time bound of p. 490, positive Harris recurrence |
| [HistoryDependentDrift](GeneralizedDrift/HistoryDependentDrift.lean) | 23 | §§19.2.1–19.2.3: Theorem 19.2.1 and regularity, Theorem 19.2.2, the killed supermartingale (19.38), Theorem 19.2.4 and Harris recurrence, Theorem 19.2.5 and transience, the arithmetic and Dynkin steps of Theorem 19.2.3, Theorem 19.2.3 and its (V4) form |
| [BilinearDrift](GeneralizedDrift/BilinearDrift.lean) | 35 | §19.2.4: the innovations read off the path, (19.42)–(19.45), `Aₖ`, `Bₖ`, `Cₖ`, the one-step Markov identity with a weight from the past, the three conditional bounds of p. 497, the test sequence and the drift (19.37), the choice of `ε`, Theorem 19.2.6, the coercivity counterexample |
| [BilinearLimits](GeneralizedDrift/BilinearLimits.lean) | 3 | §19.2.4: (V4) under scaling, Theorem 19.2.6 (the LLN for `Yₖ²`, the CLT and the LIL for `θ` and `Y`) |
| [MixedDrift](GeneralizedDrift/MixedDrift.lean) | 29 | §19.3.1: (19.46) and its consequences, (19.49)–(19.50), Theorem 19.3.1, (19.52)–(19.55), Theorem 19.3.2, the balanced flow (19.63), (19.64), Theorem 19.3.3, Cesàro averages from phase averages, (19.57), the equivalence for positivity |
| [LadderDrift](GeneralizedDrift/LadderDrift.lean) | 13 | §19.3.2: (19.65)–(19.67), the drift of `V(i, w) = i` and (19.69), the truncated heights, (19.70)/(19.74), (19.75), irreducibility of `Φ^Λ`, Theorem 19.3.4 |
| [LadderExample](GeneralizedDrift/LadderExample.lean) | 33 | §19.3.2, pp. 505–506: (19.78)–(19.79), the marginal walk, `β = 2(1 − q)`, the invariant law of `Φ^Λ` iff `p > ½`, irreducibility and positivity for `q < ½ < p`, sets not petite under bounded downward steps, (19.80), the bottom rung not petite for (19.79) and (19.80) |
| [Ladder80Transience](GeneralizedDrift/Ladder80Transience.lean) | 19 | §19.3.2, p. 506: integrals against the ladder kernel, the exponential test function, its superharmonicity, the choice of `K` and `θ`, the transience behind (19.81) in quantified form |
| [GIG1Drift](GeneralizedDrift/GIG1Drift.lean) | 10 | §19.3.3: pathwise renewal identities, `β(x) = ∫ G(dt) E[N(t) \| R₀ = x]`, the invariance of the stationary forward recurrence law for `Λ`, (19.83), Theorem 19.3.5 (first part) |
| [GIG1Stability](GeneralizedDrift/GIG1Stability.lean) | 19 | §19.3.3: busy periods without idling, the counterexample to (19.84), Wald's bound for a truncated random walk, (19.82) from the queue, `π̃(X)` bounded by the busy period, Theorem 19.3.5 (second part, corrected) |
| [SetarClassification](GeneralizedDrift/SetarClassification.lean) | 8 | App. B.2: the interior, margins and exterior of Figures B.1–B.3 and their partition, the classification (STEPS 1–4), aperiodicity, (V4) and geometric ergodicity on (11.36), the failure of linear (V4) at unit slope |

### Carried modules (3678 theorems)

Carried from the Chapter 15 project `GeometricErgodicity` (2916 theorems): all 131 of its modules.
They are its 9 Chapter 15 modules (275 theorems), `GeometricSums` (56), `KendallSets` (41),
`GeometricDrift` (30), `GeometricAtoms` (28), `GeometricSkeletons` (18), `GeometricErgodicTheorem`
(30), `GeometricConverse` (7), `GeometricConverseGeneral` (18) and `GeometricModels` (47), and the
122 modules (2641 theorems) that `GeometricErgodicity` carries from the Chapter 14 project
`FErgodicity`, which cover Chapters 1–11, 13 and 14 and the renewal theory (see those projects'
READMEs for the lists and for how the copies differ from the originals). The carried modules are
identical to the copies in `GeometricErgodicity` except for the namespace and the imports. As in
the Chapter 18 project `Positivity`, `GeometricConverseGeneral` is carried and `GeometricConverse`
and `GeometricErgodicTheorem` have their current module docstrings.

The other 41 carried modules (762 theorems) are copied from five other projects. Each has a
"Copied for Chapter 19" note in its module docstring and is otherwise identical to its source
except for the namespace and the imports, with two exceptions noted below.

* From the Chapter 17 project `LimitTheorems` (457 theorems), 26 of its 54 Chapter 17 modules:
  `BirkhoffErgodic` (47), `InvariantFields` (35), `HarrisLLN` (23), `RegenerationCycles` (31),
  `AtomLLN` (20), `KolmogorovAnscombe` (6), `AtomCLT` (26), `MartingaleCLT` (17),
  `PoissonEquation` (12), `CLTTransfer` (8), `CLTCriteria` (6), `CLTMoment` (18), `LILAnalysis`
  (26), `LILExponential` (8), `LILUpper` (12), `LILLower` (13), `IIDLIL` (7), `DependentLIL` (24),
  `MartingaleLILTools` (38), `MartingaleLILBlock` (26), `MartingaleLILUpper` (7),
  `MartingaleLILLower` (12), `MartingaleLIL` (3), `MartingaleLILChains` (13),
  `MartingaleLILApplications` (5) and `LimitApplications` (14). They give Theorem 17.0.1 and its
  LIL for Theorem 19.2.6.
* From the Chapter 18 project `Positivity` (119 theorems): `OrnsteinCoupling` (80),
  `NullRecurrence` (16), `NullPeriodic` (3) and `PositivityPn` (20), for Theorem 18.2.2 (a null
  chain has `Pⁿ(x, C) → 0` on petite sets).
* From the Chapter 11 project `DriftRegularity` (104 theorems): `DriftExamples` (58),
  `NonPositivity` (14), `SetarMarginRecurrence` (25) and `SetarNullMargins` (7), the SETAR
  results of §§11.4–11.5 and Theorems 11.5.1–11.5.2.
* From the Chapter 14 project `FErgodicity` (57 theorems), six modules that `GeometricErgodicity`
  does not carry: `FNormMeasurable` (12), `RenewalMeasure` (10), `RenewalRegeneration` (2),
  `RenewalKey` (10), `RenewalChain` (15) and `RenewalEquilibrium` (8), for the renewal measure and
  the stationary forward recurrence law of the GI/G/1 queue.
* From the Chapter 9 project `HarrisRecurrence` (25 theorems): `SETAR` (25), the transience of the
  SETAR model in the exterior (Proposition 9.5.4). Its lemma `setarRegime_of_gt` is renamed
  `setarRegime_of_bound_lt`, since `DriftExamples` has a lemma of that name.

From these modules the Chapter 19 modules use, among others, path measures, the strong Markov
property and hitting times (`pathKernel`, `natFilt`, `strong_markov_lintegral`, `firstHit`,
`firstReturn`, `hitProb`, `hitProbZero`, `meanReturnTime`), Dynkin's formula and the supermartingale
lemma (`proposition_11_3_3`, `avoidSet`, `ae_bddAbove_of_avoid`), irreducibility, petite and small
sets (`IsMaximalIrreducibility`, `maxIrrMeasure`, `IsPhiIrreducible`, `IsPetite`, `IsSmall`), Harris
recurrence, positivity and regularity (`IsHarris`, `IsPositiveHarris`, `IsPositive`,
`isPositive_or_isNull`, `theorem_9_1_3_ae`, `proposition_9_1_7_ii`, `theorem_10_4_10_ii`,
`IsRegularChain`, `theorem_11_3_4`, `theorem_11_3_15`, `IsTransientChain`), the drift conditions
and the Geometric Ergodic Theorem (`driftR`, `DriftV4`, `IsCoercive`, `proposition_8_4_1`,
`theorem_15_2_4`, `theorem_15_4_1`, `geomG`, `fNorm`), T-chains (`IsTChain`, `theorem_9_2_2_ii`,
`IsNonEvanescent`), the ergodic theorem for positive chains (`theorem_13_3_4_ii`), Theorem 18.2.2
(`IsNull.tendsto_pow_of_isPetite`), Theorem 17.0.1 (`theorem_17_0_1`, `theorem_17_0_1_iv`,
`theorem_17_0_1_iv_lil_poisson`, `asymptoticVariance`, `HasLIL`, `pathSum`), and the models
(`ladderChainKernel`, `gig1Ladder`, `gig1Lambda`, `gig1_isMarkovChain`, `law_eq_pathMeasure`,
`gig1_law_past_future`, `gig1Tilde`, `ladderS_eq_pow`, `theorem_10_5_4_invariant`, `eqLaw`,
`renMeas`, `renMeas_eqLaw`, `renMean`, `dblKernel`, `setarKernel`, `proposition_6_3_6`,
`proposition_9_5_4`, `proposition_11_4_5`, `proposition_11_5_4`, `proposition_11_5_5_all`). No
Chapter 19 module depends, directly or through other modules, on `CountableErgodic`,
`CouplingRenewal`, `EChains`, `EChainsStability`, `FPeriodicErgodic`, `GIG1SmallSets`,
`GeometricConverseGeneral`, `KeyRenewal`, `LinearInvariant`, `LinearTChains`, `RandomWalkIntegers`,
`SkipFreeWalk`, `SplitPetite`, `StateSpaces` or `TopologicalExamples`. Every one of the 41 copied
modules is used.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (4578 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
