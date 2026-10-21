# Meyn and Tweedie, Chapter 12: Invariance and Tightness, in Lean

This is the `StochasticStability/InvarianceTightness` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 12 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 288–310. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 12 constructs invariant measures for chains on topological spaces from limits of the
transition probabilities, without ψ-irreducibility. A sequence of probabilities is tight in the
sense (12.1) if for each `ε > 0` some compact `C` has `liminf_k μₖ(C) ≥ 1 − ε`, and a chain is
bounded in probability on average if the Cesàro averages `P̄ᵏ(x, ·) = k⁻¹ Σ_{i=1}^{k} Pⁱ(x, ·)`
(12.2) are tight for every `x`. §12.1 shows that this implies non-evanescence (Proposition 12.1.1)
and proves Foguel's theorem: a weak Feller chain without an invariant probability has
`P̄ⁿ(x, C) → 0` and `K_ε(x, C) → 0` uniformly in `x` for every compact `C` (Theorem 12.1.2 (i),
(12.4)–(12.5)), so a weak Feller chain bounded in probability on average has an invariant
probability (Theorem 12.1.2 (ii), Theorem 12.0.1 (i)); if that probability is unique, the Cesàro
averages converge to it weakly (Proposition 12.1.4). §12.2 introduces Neveu's kernels
`U_h = Σₖ (P I_{1−h})ᵏ P` (12.14) for `0 ≤ h ≤ 1`, the randomized first entrance time `τ_h` and the
balayage kernel `P_h = U_h I_h`, proves the resolvent equation (Theorem 12.2.1), relates
`L(x, h) = U_h(x, h)` and `Q(x, h) = P_x{Σₖ h(Φₖ) = ∞}` through a bivariate chain with uniform
marks (Theorem 12.2.2), and represents subinvariant and invariant measures through `U_h`
(Theorem 12.2.3). §12.3 smooths the process on a compact set: `P_h` is weak Feller for continuous
`h` (Proposition 12.3.1), so a compact set reached from every state gives an invariant measure
finite on compact sets (Theorem 12.3.2), as does (V1) (Theorem 12.3.3), while (V2) gives an
invariant probability (Theorem 12.3.4). §12.4 shows that an e-chain has a substochastic limit
kernel `Π`, with `P̄ᵏ(x, ·) → Π(x, ·)` and `K_ε(x, ·) → Π(x, ·)` vaguely, `PʲΠᵏPˡ = Π`, and
`Π(x, X) ≡ 1` iff the chain is bounded in probability on average (Theorem 12.4.1); it proves the
bound `K_ε(x, C) ≥ (sup_{y ∈ C} E_y[τ_C])⁻¹`, a weak form of Kac's theorem (Proposition 12.4.2),
the zero–one structure of `Π(x, X)` (Theorem 12.4.3), and hitting time and (V2) criteria for
boundedness in probability on average (Proposition 12.4.4, Theorem 12.4.5). §12.5 proves
boundedness in probability for the linear state space model under (LSS5), with positive Harris
recurrence under (LSS4) and (LCM3) as well (Proposition 12.5.1), for the bilinear model when
`E|θ + bW| < 1`, and for the adaptive control model through a moment bound (Proposition 12.5.2).

Every numbered result is formalised: Theorem 12.0.1, Proposition 12.1.1, Theorem 12.1.2,
Propositions 12.1.3–12.1.4, Theorems 12.2.1–12.2.3, Proposition 12.3.1, Theorems 12.3.2–12.3.4,
Theorem 12.4.1, Proposition 12.4.2, Theorem 12.4.3, Proposition 12.4.4, Theorem 12.4.5 and
Propositions 12.5.1–12.5.2, together with Lemma D.5.3, on which §12.5 rests, and the bilinear
model of §12.5.2. For the adaptive control model this includes (12.38) itself: the Kalman filter
is derived for the Gaussian model by characteristic functions, so (12.38) holds at every time
from a Kalman initial law, as a theorem rather than a hypothesis. Three claims are false as
printed. Each is refuted in Lean by a counterexample, and a corrected statement is proved.
Proposition 12.1.3, with `liminf_k E_x[V(Φₖ)] < ∞` for a coercive `V`, fails for a weak Feller
deterministic chain on `ℕ × ℕ∞` that has `liminf_k E_x[V(Φₖ)] = 0` and no invariant probability;
the Cesàro form, which is what Theorem 12.1.2 supports, is proved. Theorem 12.2.3 (i) needs
`∫ h dμ < ∞`: for the successor chain on `ℕ` with `h ≡ 1`, counting measure is σ-finite and
subinvariant but not invariant. Theorem 12.3.3 needs `V` coercive: the successor chain satisfies
(V1) with `V ≡ 0` and `C = ∅`, and its only invariant measure is `0`. The book's last step in
Proposition 12.5.2, that the adaptive control model is positive recurrent, appeals to the false
Proposition 12.1.3; it is proved here from the tightness of the laws from a Kalman initial law and
Theorem 12.1.2 (i). The remark (12.22), that pointwise convergence `Pᵏf → Πf` to a weak Feller
`Π` forces an e-chain, repeats the argument of Proposition 6.4.2 and fails for the Chapter 6
counterexample to that proposition, which is carried. Further points are made explicit without a
counterexample of their own: `X` is nonempty in Theorems 12.0.1 (i), 12.1.2 (ii), 12.3.2, 12.3.3
and 12.4.3 (i); the invariant
measures of Theorems 12.3.2 and 12.3.3 are nonzero; Theorem 12.2.3 (ii) is read with `νP_h = ν`;
`C` is nonempty in Theorem 12.4.3 (iii); (12.25) needs `k ≥ 1`; (V2) is an inequality in
`[0, ∞]`; Proposition 12.5.1 needs only `E‖W‖ < ∞`; the adaptive control model takes `α ≠ 0` and
`σ_z ≠ 0` from Proposition 7.4.3, and the book's initial example `y₀ = θ̃₀ = Σ₀ = 0` lies outside
the state space, so the Kalman initial law `sacKalmanInit` is used; and Lemma D.5.3 (i) is stated
with a uniform bound. Some statements are proved in a stronger form: Proposition 12.3.1 needs no
condition on `Q`, Theorem 12.2.3 (i) needs `L ≡ 1` in place of `Q ≡ 1` and no σ-finiteness, and
Proposition 12.4.2 holds for every `ε < 1` and every measurable `C`. The following are not
formalised: the randomized stopping time `τ_h` as a random time with (12.10)–(12.11) and (12.13)
(the kernels are defined by (12.14), and (12.12) is proved as a path expectation); the case
`h ≡ 1/2` of p. 294; the quadratic Lyapunov function (12.31)–(12.34) of the linear model, replaced
by `V(x) = ‖x‖` and the closed form; the remarks on (V2) for the linear and bilinear models and
the instability for `σ_z² ≥ 1`; and the commentary of §12.6. See
[corrections](docs/corrections.md). The library contains **1936 theorems**. Of these, 242 are in
the Chapter 12 modules and 1694 in the modules carried from Chapters 1–10.

The chapter rests on six groups of results.

* **Invariant probabilities for weak Feller chains** (`BoundedInProbability`). `cesaroKernel P n`
  is `P̄ⁿ` (12.2), the sampled kernel of the uniform distribution on `{1, …, n}`, and
  `IsBoundedInProbabilityOnAverage P` is (12.1)–(12.2). Vague limit points are built without
  sequential compactness. For measures `μᵢ` of mass at most one and an ultrafilter `U`,
  `vagueLimit μs hμ U` is the Riesz–Markov–Kakutani measure of the positive functional
  `f ↦ lim_U ∫ f dμᵢ` on `C_c(X)` (`vagueFunctional`), with `tendsto_integral_vagueLimit` and the
  lower bound (D.6) for bounded continuous `g ≥ 0` (`integral_vagueLimit_le`). A finite measure
  with `∫ Pg dν ≤ ∫ g dν` for every nonnegative `g ∈ C_c(X)` is invariant
  (`isInvariant_of_integral_le`), and Foguel's argument (12.6)–(12.7) is
  `exists_isInvariant_of_vague`. Theorem 12.1.2 is `theorem_12_1_2_i` ((12.4)),
  `theorem_12_1_2_i_resolvent` ((12.5)) and `theorem_12_1_2_ii`; Theorem 12.0.1 (i) is
  `theorem_12_0_1_i`. The form used through the rest of the chapter is
  `exists_isInvariant_of_frequently`: if `P̄ⁿ(x, C) ≥ δ > 0` for infinitely many `n`, for one `x`
  and one compact `C`, an invariant probability exists. Proposition 12.1.4 is
  `proposition_12_1_4`, through Prokhorov's theorem.
* **Generalized sampling** (`GeneralizedSampling`). `killOp P w u = P I_w u` and
  `geomOp P w φ = Σₖ (P I_w)ᵏ φ`, with the minimality principle `geomOp_le`. `genPotKernel P h` is
  `U_h` (12.14), `balayage P h` is `P_h = U_h I_h`, and `genL P h` and `genQ P h` are `L(x, h)` and
  `Q(x, h)`; for `h ≡ 1`, `h ≡ 0` and `h = 1_B` they reduce to `P`, `U`, `U_B`, `L(x, B)` and
  `Q(x, B)` (`genPotKernel_one`, `genPotKernel_zero`, `genPotKernel_indicator`, `genL_indicator`,
  `genQ_indicator`). The resolvent equation is `theorem_12_2_1`, proved by Neveu's operator
  argument from the series (`geomOp_resolvent`). Theorem 12.2.2 (i) is `theorem_12_2_2_i`, stated
  for the bivariate chain with path law `P_x ⊗ (uniform)^ℕ` and proved by the two Borel–Cantelli
  lemmas conditionally on the path of `Φ`; (ii) and (iii) are `theorem_12_2_2_ii` and
  `theorem_12_2_2_iii`, through the path identity `L(x, h) = 1 − E_x[∏_{i ≥ 1} (1 − h(Φᵢ))]`
  (`genL_add_lintegral_iInf`). Theorem 12.2.3 is `theorem_12_2_3_i` (corrected) and
  `theorem_12_2_3_ii`.
* **σ-finite invariant measures** (`SigmaFiniteInvariant`). `P_h` is weak Feller for every
  continuous `h` (`proposition_12_3_1`). If a compact `C` has `L(·, C) ≡ 1` (12.19), a weak Feller
  chain has a nonzero invariant measure finite on compact sets (`theorem_12_3_2`): a compactly
  supported Urysohn function `h ≥ 1_C` makes `P_h` a weak Feller transition kernel concentrated on
  a compact set, Theorem 12.1.2 gives it an invariant probability `ν`, and `νU_h` is invariant for
  `P` by Theorem 12.2.3 (ii). (V1) off a compact set with a coercive `V` gives the same conclusion
  (`theorem_12_3_3`), and (V2) with `V(x₀) < ∞` gives an invariant probability (`theorem_12_3_4`,
  with (12.21) as `eventually_le_cesaroKernel_of_V2`).
* **e-chains** (`EChainInvariant`, `EChainCriteria`). For an e-chain (`IsEChain`, carried) the
  Cesàro averages are equicontinuous (`eventually_abs_cesaroFun_sub_le`); a diagonal argument over
  a countable dense family in `C_c(X)` gives subsequences along which `P̄ⁿ f(x)` converges for every
  `f` and every `x` (`exists_dense_cc`, `exists_subseq_tendsto_cesaroFun`), and all the limits
  coincide (`limMeasure_eq`). The limit kernel is `eChainLimit he`. Theorem 12.4.1 is
  `theorem_12_4_1_i` ((12.23)), `theorem_12_4_1_resolvent` ((12.24), from Cesàro to Abel means by
  `tendsto_abel_of_cesaro`), `theorem_12_4_1_ii` ((12.25)) and `theorem_12_4_1_iii`; Theorem 12.0.1
  (ii) is `theorem_12_0_1_ii`. With `u = eChainMass he = Π(·, X)`, Proposition 12.4.2 is
  `proposition_12_4_2` (and `proposition_12_4_2_liminf`), Theorem 12.4.3 is `theorem_12_4_3_i`,
  `theorem_12_4_3_ii`, `theorem_12_4_3_iii` and `theorem_12_4_3_iv`, Proposition 12.4.4 is
  `proposition_12_4_4`, and Theorem 12.4.5 is `theorem_12_4_5`, with the mean return time bound
  `E_x[τ_C] ≤ V(x) + b 1_C(x)` under (V2) proved directly (`meanReturnTime_le_of_V2`).
* **Boundedness in probability** (`BoundednessCriteria`, `TightnessCriteria`). Lemma D.5.3 (i) is
  `lemma_D_5_3_i`, with the halves `isTightMeasureSet_range_of_lintegral_le` and
  `lemma_D_5_3_i_necessity`; Lemma D.5.3 (ii) is `lemma_D_5_3_ii`. A coercive `V` with
  `PV ≤ αV + β`, `α < 1`, makes a chain bounded in probability (`isBoundedInProbability_of_drift`).
  Proposition 12.5.1 is `proposition_12_5_1_i` (bounded in probability) and
  `proposition_12_5_1_ii` (positive Harris), and the bilinear model of §12.5.2 is
  `bilinear_isBoundedInProbability`.
* **The adaptive control model** (`BoundednessCriteria`, `AdaptiveControlStability`). One step of
  the Kalman filter is `kalman_step_map`: if `θ̃ = √Σ ξ` with `ξ ~ N(0, 1)` independent of the
  noise, then `(θ̃', Y')` has law `N(0, Σ') ⊗ N(0, ΣY² + σ_w²)`, proved by comparing
  characteristic functions. `IsKalmanLaw ν` is (12.38) as a property of the law of `Φₖ`
  (`θ̃ ~ N(0, Σ)` given `(Σ, Y)`); the filter preserves it (`IsKalmanLaw.comp`,
  `isKalmanLaw_sacGaussian_pow`), and under it `E[g(Σ, Y) θ̃²] = E[g(Σ, Y) Σ]`
  (`IsKalmanLaw.lintegral_sq`), which is all that (12.39)–(12.41) use. Proposition 12.5.2 is
  `proposition_12_5_2` (the moment bound from that identity, taken as a hypothesis, for a general
  noise law), `proposition_12_5_2_tight`, `proposition_12_5_2_kalman` (`sup_k E|Φₖ|² < ∞` for the
  Gaussian model from any Kalman initial law on the state space with `E Y₀² < ∞`) and
  `proposition_12_5_2_positive` (the chain restricted to its state space is a positive recurrent,
  aperiodic T-chain).

The library covers the chapter as follows.

* **Tightness and boundedness in probability on average** (Chapter 12 introduction, pp. 288–289).
  (12.1)–(12.2), Theorem 12.0.1.
* **Weak and vague convergence** (§12.1.1). Proposition 12.1.1 and (12.3).
* **Feller chains and invariant probability measures** (§12.1.2). Theorem 12.1.2 and
  (12.4)–(12.7), vague limits (Proposition D.5.6, (D.6)), Proposition 12.1.3 with its
  counterexample and correction, (12.8), Proposition 12.1.4 and (12.9).
* **Generalized sampling and invariant measures** (§12.2). (12.12), (12.14) and its special cases,
  Theorem 12.2.1, (12.17), `L(x, h)` and `Q(x, h)`, Theorem 12.2.2 for the bivariate chain, and
  Theorem 12.2.3 with the counterexample to (i).
* **The smoothed chain on a compact set** (§12.3.1). (12.19)–(12.20), Proposition 12.3.1,
  Theorem 12.3.2.
* **Drift criteria for the existence of invariant measures** (§12.3.2). Theorem 12.3.3 with its
  counterexample and correction, Theorem 12.3.4 and (12.21).
* **Existence of an invariant measure for e-chains** (§12.4.1). Theorem 12.4.1, (12.23)–(12.26).
* **Hitting time and drift criteria for e-chains** (§12.4.2). Proposition 12.4.2 and (12.27),
  Theorem 12.4.3 and (12.28)–(12.30), Proposition 12.4.4, Theorem 12.4.5.
* **Linear state space models** (§12.5.1). Lemma D.5.3, Proposition 12.5.1 by `V(x) = ‖x‖`.
* **Bilinear models** (§12.5.2). (12.35)–(12.37).
* **Adaptive control models** (§12.5.3). The Kalman filter and (12.38), (12.39)–(12.41),
  Proposition 12.5.2 with the corrected last step.

All names are in the namespace `MeynTweedie.InvarianceTightness`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [BoundedInProbability](InvarianceTightness/BoundedInProbability.lean) | 49 | Chapter 12 introduction and §12.1: Cesàro and resolvent averages (12.2), boundedness in probability on average, Proposition 12.1.1 and (12.3), vague limits by the Riesz–Markov–Kakutani theorem, Foguel's argument (12.6)–(12.7), Theorem 12.1.2, Theorem 12.0.1 (i), Proposition 12.1.3 in the Cesàro and the eventually bounded forms, Proposition 12.1.4, the successor chain |
| [LiminfCounterexample](InvarianceTightness/LiminfCounterexample.lean) | 10 | §12.1.2: the space `ℕ × ℕ∞` and the chapter's standing hypotheses, the deterministic loop chain, its weak Feller property, the coercive `V`, the absence of an invariant probability, the counterexample to Proposition 12.1.3 |
| [GeneralizedSampling](InvarianceTightness/GeneralizedSampling.lean) | 63 | §12.2: the operators `P I_w` and `Σₖ (P I_w)ᵏ`, the kernels `U_h` (12.14), `U_h I_w` and `P_h`, the special cases of p. 294, Theorem 12.2.1, `L(x, h)` and (12.17), `Q(x, h)` and (12.12), Theorem 12.2.2 for the bivariate chain, `K_{1/2}(x, h)`, Theorem 12.2.3 with the counterexample to (i) |
| [SigmaFiniteInvariant](InvarianceTightness/SigmaFiniteInvariant.lean) | 14 | §12.3: lower semicontinuity of `P I_w`, Proposition 12.3.1, Theorem 12.3.2, Theorem 12.3.3 with its counterexample, the iteration of (V2) and (12.21), Theorem 12.3.4 |
| [EChainInvariant](InvarianceTightness/EChainInvariant.lean) | 39 | §12.4.1: equicontinuity of the Cesàro averages, a countable dense family in `C_c(X)`, the diagonal argument (12.26), limit measures along subsequences and their uniqueness, the limit kernel `Π`, Theorem 12.4.1 (12.23), (12.25) and (iii), Theorem 12.0.1 (ii) |
| [EChainCriteria](InvarianceTightness/EChainCriteria.lean) | 32 | §12.4: Abel means and (12.24), Proposition 12.4.2 and (12.27), the mass function `Π(·, X)`, (D.6) for open sets, (12.29), Theorem 12.4.3, Proposition 12.4.4, the mean return time bound under (V2), Theorem 12.4.5 |
| [BoundednessCriteria](InvarianceTightness/BoundednessCriteria.lean) | 19 | §12.5 and Lemma D.5.3 (ii) with the sufficiency half of (i): geometric drift, Proposition 12.5.1, the bilinear model (12.36)–(12.37), the adaptive control identities (12.40)–(12.41), Proposition 12.5.2 under (12.38) and its tightness form |
| [TightnessCriteria](InvarianceTightness/TightnessCriteria.lean) | 2 | Lemma D.5.3 (i): the necessity half and the equivalence |
| [AdaptiveControlStability](InvarianceTightness/AdaptiveControlStability.lean) | 14 | §12.5.3: characteristic functions of Gaussian laws, the Kalman filter step, Kalman laws (12.38) and their propagation, Proposition 12.5.2 for the Gaussian model, the Kalman initial law, the restricted chain as a weak Feller random recursion, positive recurrence |

Carried from the Chapter 10 project `InvariantMeasures` (1477 theorems): 71 of the 89 modules of
that project, identical to the copies there except for the namespace and the last paragraph of the
module docstrings of `ModelInvariant` and `QueueInvariant`, which point to modules that are not
carried and are replaced by a note of what is not formalised. Its own Chapter 10 modules (208
theorems): `Invariance` (39), `MinimalInvariant` (22), `AtomInvariant` (30), `SplitInvariant` (8),
`UniqueInvariant` (18), `PositiveNull` (14), `CountableInvariant` (22), `QueueInvariant` (19),
`MG1Invariant` (25), `ModelInvariant` (11). Its Chapter 10 modules `LadderInvariant`,
`GIG1Invariant`, `RenewalInvariant`, `LinearInvariant` and `QueueInvariantMinimal`, and the
modules it carried directly from the Chapter 5 project `PseudoAtoms` (`ModelKernels`,
`ModelCountableModels`, `ModelQueues`, `ModelStorage`, `ModelRenewal`, `SpecificKernels`,
`Regeneration`, `PoissonCounts`, `RenewalSkeletons`, `LadderChains`, `GIG1Embedding`,
`GIG1SmallSets`, `RenewalSmallSets`), are not carried. Invariant and subinvariant measures
(`IsInvariant`, `IsSubinvariant`, `IsInvariant.resolvent`), positive and positive Harris chains
(`IsPositive`, `IsPositiveHarris`), Proposition 10.1.1 (`proposition_10_1_1`), the uniqueness
devices `eq_of_le_of_lintegral_le` and `eq_of_add_eq_of_le`, and mean return times
(`meanReturnTime`, `meanReturnTime_eq_tabooPotKernel`, `one_le_meanReturnTime`,
`hitProb_eq_one_of_meanReturnTime_ne_top`) are used. No Chapter 12 module depends, directly or
through other modules, on `CountableInvariant`, `QueueInvariant`, `MG1Invariant` or
`ModelInvariant`.

Carried in turn by `InvariantMeasures` from the Chapter 9 project `HarrisRecurrence` (1269
theorems; see those projects' READMEs for how they differ from the originals):

* Its own Chapter 9 modules (212 theorems): `HarrisDefinitions` (29), `HarrisProperties` (15),
  `HarrisDecomposition` (18), `SupermartingaleDrift` (14), `NonEvanescence` (21),
  `TopologicalRecurrence` (21), `TopologicalExamples` (33), `DriftHarris` (29),
  `StochasticComparison` (32). The function `Q(x, B)` and infinitely-often sets (`harrisQ`,
  `ioSet`), Proposition 9.1.1 (`proposition_9_1_1`), non-evanescence (`IsNonEvanescent`), coercive
  functions (`IsCoercive`), Theorem 9.2.2 (ii) (`theorem_9_2_2_ii`) and the supermartingale of
  Theorem 9.4.1 (`ae_bddAbove_of_avoid`, `killedV`, `ae_tendsto_killedV`) are used. No Chapter 12
  module depends on `TopologicalExamples` or `StochasticComparison`.
* From the Chapter 8 project `TransienceRecurrence` (220 theorems): `UniformTransience` (46),
  `Decompositions` (8), `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23),
  `CountableClassification` (18), `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16),
  `SkipFreeWalk` (15), `RandomWalkMeanZero` (5). Recurrent chains (`IsRecurrentChain`) are used.
  No Chapter 12 module depends on `RandomWalkIntegers`, `RandomWalkMeanZero` or `SkipFreeWalk`.
* From the Chapter 6 project `TopologyContinuity` (130 theorems): `FellerChains` (40), `TChains`
  (14), `EChains` (16), `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16),
  `TChainModels` (10), `EChainsStability` (12). Weak Feller chains (`IsWeakFeller`,
  `proposition_6_1_1_i_weak`), T-chains (`IsTChain`), e-chains (`IsEChain`,
  `eventually_dist_lt_of_eChain`), boundedness in probability (`IsBoundedInProbability`), the
  eigenvalue condition (LSS5) (`IsStableMatrix`, `isStableMatrix_geometric`), Proposition 6.3.5
  (`proposition_6_3_5`) and the Feller property of random recursions
  (`isWeakFeller_recursionKernel`) are used.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` (`pathKernel`),
  the shift (`shift`), the kernels `U`, `U_A`, `K_a`, `K_{a_ε}` and `I_A` (`potKernel`,
  `tabooPotKernel`, `sampledKernel`, `resolvent`, `indKernel`), integrals against kernels (`kfun`,
  `kfunR`), hitting probabilities and return times (`hitProb`, `firstReturn`) and the strong Markov
  property (`strong_markov_lintegral_mul`, `stoppedState`) are used throughout. No Chapter 12
  module depends on `StateSpaces` or `SpecificMatrices`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). The restriction of a chain to an absorbing set (`restrictKernel`)
  and Proposition 4.2.2 (`proposition_4_2_2_maximal`) are used. No Chapter 12 module depends on
  `CountableIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). The uniform sampling distribution
  (`uniformDist`, `isSamplingDist_uniformDist`) and aperiodicity (`IsAperiodic`) are used. No
  Chapter 12 module depends on `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). Random recursions
  (`recursionKernel`), the linear state space model (`lssMatrixKernel`, `IsControllable`), the
  bilinear model (`bilinearKernel`) and the adaptive control model (`sacStep`, `sacKernel`,
  `sacGaussianKernel`) come from these modules.

Carried from the Chapter 7 project `NonlinearStateSpace` (217 theorems): its Chapter 7 modules
other than `NSSEquicontinuity`, namely `ControlModel` (33), `ForwardAccessibility` (18),
`LocalInverse` (8), `NSSTChain` (12), `MinimalSets` (29), `PeriodicOrbits` (37),
`NSSIrreducibility` (8), `NSSPeriodicity` (10), `NSSExamples` (44) and `NSSAdaptiveControl` (18).
Its modules from Chapters 1–6 are not taken from it; this library has them from
`InvariantMeasures`. The ten modules are identical to the copies in `NonlinearStateSpace` except
for the namespace and one rename. The invariant sets of the control model, `IsInvariant` in
`ControlModel`, would clash with `IsInvariant` for measures in `Invariance`, and are renamed
`IsCMInvariant`. The lemmas named after them follow (`isCMInvariant_iff_step`,
`IsCMInvariant.reach_subset`, `isCMInvariant_iUnion` and the others in `ControlModel` and
`MinimalSets`), as do their uses in `PeriodicOrbits`, `NSSIrreducibility`, `NSSExamples` and
`NSSAdaptiveControl`; `reachSet_subset_of_isInvariant` keeps its name. Proposition 7.4.3
(`proposition_7_4_3`) and the state space of the adaptive control model (`sacSpace`,
`isClosed_sacSpace`, `isAbsorbing_sacSpace`) are used, by `AdaptiveControlStability` only.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
