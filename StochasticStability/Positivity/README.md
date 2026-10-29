# Meyn and Tweedie, Chapter 18: Positivity, in Lean

This is the `StochasticStability/Positivity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 18 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 462–481. Run the commands below from this directory. [Return to the
library index](../../README.md).

Chapter 18 returns from sample paths to the limits of the transition probabilities `Pⁿ(x, A)`,
now for chains that need not be positive. Theorem 18.0.1 collects two limit theorems for Harris
chains: for an aperiodic Harris chain the `n`-step laws from any two initial laws merge in total
variation (18.1), and for a null chain they leave every set of finite invariant measure,
uniformly in the sense `sup_A λPⁿ(A)/(π(A) + ε) → 0` (18.2). Theorem 18.0.2 characterises the
positivity of T-chains and e-chains that have a reachable state `x*`, through boundedness in
probability and the behaviour of `Pⁿ` near `x*`. §18.1 first explains why the independent coupling
of §13.2 needs a finite mean (p. 464: two independent copies of the recurrent simple random walk on
`ℤ²` form a transient walk). It then builds Ornstein's dependent coupling of two renewal processes,
which gives the renewal limits (18.6)–(18.7) with no finite mean (Theorem 18.1.1), and from it
Orey's theorem (Theorem 18.1.2, (18.13)) and Jain's theorem (Theorem 18.1.3, (18.15)). §18.2
classifies states (on a countable space) and sets (in general) as null or positive through the
behaviour of `Pⁿ`, and shows that this agrees with the classification through `π`: on a countable
space through the solidarity inequality (18.23) (Theorem 18.2.1), and for `ψ`-irreducible chains
through the sets of `B⁺(X)` and the petite sets (Theorem 18.2.2). §18.3 shows that a T-chain with a
reachable state is positive Harris iff it is bounded in probability (Proposition 18.3.1 on a
countable space, Theorem 18.3.2), and positive iff its reachable state is topologically positive
(Proposition 18.3.3). §18.4 does the same for e-chains: Lemma 18.4.1 relates evanescence to the
visits near `x*`; Proposition 18.4.2 makes a unique invariant probability with Cesàro convergence,
boundedness in probability on average and positivity of `x*` equivalent; and with a topologically
aperiodic `x*` the laws `Pᵏ(x, ·)` converge weakly, first from the support of `π` (Proposition
18.4.3) and then from every state (Theorem 18.4.4). §18.5 proves the weak and the strong law of
large numbers for the occupation probabilities (18.30) of an e-chain (Theorem 18.5.1) and gives the
drift condition (V4) for a coercive function as a sufficient condition for the strong law (Theorem
18.5.2). §18.6 is commentary.

Every numbered result of Chapter 18 is formalised: Theorems 18.0.1–18.0.2, Theorems 18.1.1–18.1.3,
Theorems 18.2.1–18.2.2, Proposition 18.3.1, Theorem 18.3.2, Proposition 18.3.3, Lemma 18.4.1,
Propositions 18.4.2–18.4.3, Theorem 18.4.4 and Theorems 18.5.1–18.5.2, together with the
illustration of p. 464 that independent coupling fails for null renewal processes. Two claims are
false as printed. Each is refuted in Lean by a counterexample of this project, and a corrected
statement is proved. The solidarity inequality (18.23) is printed strict and fails for the
one-point chain (`eq_18_23_counterexample`); the non-strict inequality is proved
(`limsup_pow_add_ge`), and it is all that the solidarity argument needs. Theorem 18.1.3 is stated
for aperiodic null recurrent chains, but it is false without the Harris property
(`theorem_18_1_3_counterexample`, a recurrent, null and aperiodic chain on `ℕ ⊕ ℕ` with an escape
path); it is proved for aperiodic Harris null chains (`theorem_18_1_3`). Further corrections
concern proofs. The book proves Theorems 18.2.1 and 18.2.2 (ii) by applying Theorem 18.1.3 to
chains that may be periodic and, in Theorem 18.2.2 (ii), not Harris; both theorems are proved for
every period with no Harris hypothesis, and so Theorem 18.3.2, whose proof uses Theorem 18.2.2
(ii), holds for periodic chains too. The proof of Proposition 18.4.2 uses the positivity of `x*`
only through `Π(x*, X) > 0`, which the definition of p. 473 does not give; the equivalence is
proved with `x*` positive in the Cesàro sense (`IsCesaroPositive`), which implies the book's sense,
and whether the book's sense suffices is left as an open question. Theorem 18.0.2 (ii) (c) is read
in the same way.
Further points are made explicit. A countably generated σ-algebra is assumed where the period, the
maximal Harris set or Theorem 9.1.4 is used; the state space of §§18.3–18.5 is a locally compact,
second-countable Hausdorff space with its Borel σ-algebra, metrizable for e-chains; the null part
(18.2) of Theorem 18.0.1 is read under the theorem's standing hypothesis that the chain is
aperiodic and Harris; the tightness of Theorem 18.5.1 (ii) is taken in an eventual form; and the
set of (V4) in Theorem 18.5.2 need not be compact. The following are not formalised: the remark
(18.22) and the other informal remarks; the claim of p. 474 that a reachable state is equivalent
to `Π(x, X)` not depending on `x` (one direction, and Theorem 18.4.4 (i), are formalised); the
special cases in which the open question is settled; and the commentary of §18.6, with the
decomposition of chains without a reachable state and the random limit (18.36). See
[corrections](docs/corrections.md). The library contains **3419 theorems**. Of these, 275 are in
the 11 Chapter 18 modules. The other 3144 are in the 139 modules carried from earlier projects: all
131 modules of the Chapter 15 project `GeometricErgodicity`, which cover Chapters 1–11 and 13–15
and the renewal theory, and 8 Chapter 12 modules of the Chapter 12 project `InvarianceTightness`.

Several routes differ from the book. Theorem 18.5.2 is proved where the book cites Meyn [259],
and the strong law for martingale differences, which the book takes from Doob, is proved for
bounded and for square integrable differences. (18.6) is the carried Theorem 13.2.2, whose
analytic proof needs no finite mean; the coupling proves (18.7). The coupling is built from the
start as a Markov chain on `ℕ × ℕ` with the lazy law `½δ₀ + ½p`, which is the book's `p⁰` with
`p⁰(0) = ½`, so that the book's two passes (first under (18.8), then for `p⁰`) become one. Jain's
theorem replaces Egorov's theorem by the increasing sets on which (18.17) has already taken place,
and uses no σ-finiteness of `π`. The positive half of Theorem 18.2.2 (i) goes through the phase
averages of Theorem 13.3.4 (ii), and the null case of Theorem 18.2.2 (ii) through the maximal
Harris set, the uniform transience of its complement on petite sets and the `d`-skeleton on each
cycle class. The "only if" half of Theorem 18.3.2 uses no T-chain property. Proposition 18.4.3 is
proved for every `f ∈ C_c(X)` by running the argument for `Pᵏf − π(f)`. Theorem 18.5.1 (i) bounds
the `P_x`-mean of the error term of (18.33) instead of using (18.32). The converse half of Theorem
18.4.4 (i), which the book does not prove, is proved through a point of the support of `π`. The
walks of p. 464 are analysed through Spitzer's 45° rotation of `ℤ²` and explicit bounds on the
central binomial probabilities.

The chapter rests on nine groups of results.

* **Ornstein's coupling** (`OrnsteinCoupling`). The lazy law `q = ½δ₀ + ½p` (`lazyLaw`), the
  coupled increments `ρ = ornsteinLaw p M` (both marginals `q`, `ornsteinLaw_map_fst`,
  `ornsteinLaw_map_snd`), the pair chain of the two sequences of renewal epochs (`pairKernel`) and
  its difference walk with the symmetric bounded increment law `Γ = diffLaw p M`
  (`pairKernel_map_diff`, `integral_diffLaw`). The level `M` of (18.8) is `exists_aperiodic_level`;
  the difference walk is then irreducible and recurrent (`isIrreducibleChain_diffWalk`,
  `hitProb_diffWalk_eq_one`), so the coupling succeeds (`pairKernel_firstHit_ne_top`). The ages
  (`ageEvent`, `pathMeasure_fst_ageEvent`) give (18.9)–(18.10) (`sum_abs_age_sub_le`). Theorem
  18.1.1 is `theorem_18_1_1_i` and `theorem_18_1_1_ii`.
* **Orey's and Jain's theorems** (`NullRecurrence`). Orey's theorem at an atom
  (`tendsto_tvNorm_sub_atom`, with (18.14) as `tvNorm_comp_pow_succ_sub_atom_le`), the contraction
  `tvNorm_comp_pow_add_le`, and Theorem 18.1.2 as `theorem_18_1_2`, `theorem_18_1_2_measures`
  and `theorem_18_1_2_dirac`. A null chain has `π(X) = ∞` (`IsNull.measure_univ_eq_top`), (18.19)
  is `measure_mul_le_of_forall_le`, the core of Jain's theorem is
  `tendsto_iSup_div_of_measure_univ_eq_top`, and Theorem 18.1.3 is `theorem_18_1_3`. Theorem
  18.0.1 is `theorem_18_0_1`.
* **A null recurrent chain that is not Harris** (`NullNotHarris`). `escKernel` runs the forward
  recurrence time chain of the infinite-mean law `escP` on one copy of `ℕ` and an escape path on
  the other; it is recurrent, null and aperiodic with an invariant `π ≠ 0`, and (18.15) fails from
  the escape path (`theorem_18_1_3_counterexample`).
* **Independent coupling** (`IndependentCoupling`). The simple random walk on `ℤ²` is recurrent
  (`ssrw2_isRecurrentState`), two independent copies of it are transient
  (`ssrw4_isTransientState`), and so the return times form a proper renewal process whose
  independent coupling fails with positive probability (`independent_coupling_fails`).
* **Null Harris chains of any period** (`NullPeriodic`). The `d`-skeleton on a cycle class is
  Harris and aperiodic (`IsCycle.absorbKernel_isHarris_isAperiodic`), and a Harris null chain has
  `Pⁿ(x, A) → 0` whenever `π(A) < ∞` (`tendsto_pow_of_isHarris_of_isNull`).
* **Positivity through `Pⁿ`** (`PositivityPn`). Null and positive states (`IsNullState`,
  `IsPositiveState`) and sets (`IsNullSet`, `IsPositiveSet`); (18.20) ⇒ (18.21)
  (`potKernel_eq_top_of_limsup_pos`); (18.23) as `limsup_pow_add_ge`, with
  `eq_18_23_counterexample`; Theorem 18.2.1 as `theorem_18_2_1`, `theorem_18_2_1_positive`,
  `theorem_18_2_1_null` and `positive_or_null_states`; null chains leave petite sets
  (`IsNull.tendsto_pow_of_isPetite`); Theorem 18.2.2 as `theorem_18_2_2_i` and
  `theorem_18_2_2_ii`.
* **T-chains** (`TChainPositivity`). Positive Harris chains are bounded in probability
  (`IsPositiveHarris.isBoundedInProbability`) and bounded in probability T-chains are positive
  Harris (`IsBoundedInProbability.isPositiveHarris`). Proposition 18.3.1 is `proposition_18_3_1`,
  Theorem 18.3.2 is `theorem_18_3_2`, the topological notions are `IsTopNull` and `IsTopPositive`,
  Proposition 18.3.3 is `proposition_18_3_3` (with `isTopNull_iff_isNull`), and Theorem 18.0.2 (i)
  is `theorem_18_0_2_i`.
* **e-chains: positivity and aperiodicity** (`EChainPositivity`, `EChainAperiodic`). Lemma 18.4.1
  is `lemma_18_4_1`; the limit kernel does not depend on the starting point
  (`eChainLimit_eq_of_isReachable`, from `harmonic_eq_of_isReachable`); Proposition 18.4.2 is
  `proposition_18_4_2` with `IsCesaroPositive` and `IsCesaroPositive.isTopPositive`; Theorem
  18.4.4 (i) is `theorem_18_4_4_i`. Topological aperiodicity is `IsTopAperiodic`, Proposition
  18.4.3 is `proposition_18_4_3` (core `tendsto_pow_cc_of_mem_support`, sign step
  `sign_of_integral_abs_eq`), and Theorem 18.4.4 (ii) is `theorem_18_4_4_ii` and
  `theorem_18_4_4_ii_converse`.
* **The LLN for e-chains** (`EChainLLN`, `EChainDriftLLN`). The martingale differences `mdTerm`
  and their strong law (`ae_tendsto_mdSum_div`, `ae_tendsto_mdSum_div_of_sq`), the decomposition
  (18.33)–(18.34) (`abs_sum_sub_sum_cesaroIter_le`, `abs_occAvg_sub_le`), the occupation measures
  (18.30) (`occMeasure`). Theorem 18.5.1 is `theorem_18_5_1_i` and `theorem_18_5_1_ii`, Theorem
  18.0.2 (ii) is `theorem_18_0_2_ii`, and Theorem 18.5.2 is `theorem_18_5_2` and
  `theorem_18_5_2_bounded`, through the martingale of `√V` (`ae_tendsto_mdSum_sqrt_div`,
  `tight_of_tendsto_mdSum_sqrt`).

The library covers the chapter as follows.

* **Introduction** (pp. 462–464). Theorem 18.0.1 with (18.1)–(18.2), (18.3), Theorem 18.0.2 with
  (18.4)–(18.5).
* **Null recurrent chains** (§18.1). The failure of independent coupling (p. 464).
* **Coupling renewal processes for null chains** (§18.1.1). The Ornstein coupling, Theorem 18.1.1
  with (18.6)–(18.12).
* **Orey's convergence theorem** (§18.1.2). Theorem 18.1.2 with (18.13)–(18.14); Theorem 18.1.3
  with (18.15)–(18.19), its counterexample and correction.
* **Countable spaces** (§18.2.1). (18.20)–(18.21), null and positive states, (18.23) with its
  counterexample and correction, Theorem 18.2.1.
* **General spaces** (§18.2.2). Null and positive sets, Theorem 18.2.2.
* **T-chains bounded in probability** (§18.3.1). Proposition 18.3.1 with (18.24), Theorem 18.3.2
  with (18.25).
* **Positive and null states for T-chains** (§18.3.2). Topological positivity and nullity,
  Proposition 18.3.3.
* **Reachability and positivity** (§18.4.1). Lemma 18.4.1, Proposition 18.4.2 with its Cesàro
  reading.
* **Aperiodicity and convergence** (§18.4.2). Topological aperiodicity, Proposition 18.4.3 with
  (18.26)–(18.28), Theorem 18.4.4 with (18.29).
* **The LLN for e-chains** (§18.5). (18.30), Theorem 18.5.1 with (18.31)–(18.34), Theorem 18.5.2
  with (18.35).

All names are in the namespace `MeynTweedie.Positivity`. See the [source map](docs/source-map.md)
and the [corrections](docs/corrections.md).

## Library map

### The Chapter 18 modules (275 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [OrnsteinCoupling](Positivity/OrnsteinCoupling.lean) | 80 | §18.1.1: lumping of chains, the lazy law `p⁰` of p. 467, the Ornstein coupling of the increments and its marginals, the pair chain and its difference walk, the level `M` of (18.8), irreducibility and recurrence of the difference walk, the lazy renewal potential, the ages and (18.10), the coupling inequality (18.9), Theorem 18.1.1, the companion of (18.7) with `p` in place of `p̄` |
| [NullRecurrence](Positivity/NullRecurrence.lean) | 16 | §18.1.2 and Theorem 18.0.1: (18.14) in total variation form, Orey's theorem at an atom, the contraction of the total variation norm, Theorem 18.1.2 with (18.13), `π(X) = ∞` for null chains, (18.19), Theorem 18.1.3 for Harris chains, Theorem 18.0.1 |
| [NullPeriodic](Positivity/NullPeriodic.lean) | 3 | §§18.1–18.2: the `d`-skeleton on a cycle class is Harris and aperiodic, residue classes, `Pⁿ(x, A) → 0` for Harris null chains of any period |
| [NullNotHarris](Positivity/NullNotHarris.lean) | 40 | Theorem 18.1.3: an infinite-mean renewal law, the escape path, the chain `escKernel` on `ℕ ⊕ ℕ`, its maximal irreducibility measure, recurrence, invariant measure, nullity and aperiodicity, the failure of (18.15), the counterexample |
| [PositivityPn](Positivity/PositivityPn.lean) | 20 | §18.2: null and positive sets and states, uniformly transient sets, the first-entrance step, the chain on a maximal Harris set, null chains leave petite sets, Theorem 18.2.2, (18.20)–(18.21), (18.23) corrected and its counterexample, Theorem 18.2.1 and the solidarity of states |
| [TChainPositivity](Positivity/TChainPositivity.lean) | 12 | §18.3 and Theorem 18.0.2 (i): positive Harris chains are bounded in probability, bounded in probability T-chains are positive Harris, Theorem 18.3.2, topologically null and positive states, Proposition 18.3.3, Theorem 18.0.2 (i) with (18.4), Proposition 18.3.1 on a countable discrete space |
| [EChainPositivity](Positivity/EChainPositivity.lean) | 11 | §18.4.1: e-chains are weak Feller, reachable states are reached and charged, Lemma 18.4.1, constant harmonic functions, the limit kernel `Π(y, ·)` independent of `y`, Cesàro positivity, Proposition 18.4.2, Theorem 18.4.4 (i) |
| [EChainAperiodic](Positivity/EChainAperiodic.lean) | 11 | §18.4.2: the Ascoli step, equicontinuity of `{Pᵏf}`, the strict triangle inequality, topological aperiodicity, the sign step, Proposition 18.4.3 with (18.26)–(18.27), Theorem 18.4.4 (ii) with (18.29) and its converse |
| [EChainLLN](Positivity/EChainLLN.lean) | 35 | §18.5 and Theorem 18.0.2 (ii): martingale differences and their weak and strong laws, iterates and Cesàro iterates, the telescoping identities, (18.33)–(18.34), the occupation averages and measures (18.30), Theorem 18.5.1 with (18.31)–(18.32), the dense family and vague-to-weak steps, Theorem 18.0.2 (ii) with (18.5) |
| [EChainDriftLLN](Positivity/EChainDriftLLN.lean) | 17 | §18.5: Chebyshev's inequality, square integrable martingale differences and their strong law, (V4) in real form, the square root of a (V4) function, moments along the path, tightness of the occupation measures, Theorem 18.5.2 with (18.35) |
| [IndependentCoupling](Positivity/IndependentCoupling.lean) | 30 | §18.1, p. 464: products of independent chains, the simple random walks on `ℤ` and `ℤ²`, the 45° rotation, two independent copies on `ℤ⁴`, bounds on `C(2n, n)/4ⁿ`, recurrence in two dimensions, transience of the two copies, the failure of independent coupling |

### Carried modules (3144 theorems)

Carried from the Chapter 15 project `GeometricErgodicity` (2916 theorems): all 131 of its modules.
They are its 9 Chapter 15 modules (275 theorems), `GeometricSums` (56), `KendallSets` (41),
`GeometricDrift` (30), `GeometricAtoms` (28), `GeometricSkeletons` (18), `GeometricErgodicTheorem`
(30), `GeometricConverse` (7), `GeometricConverseGeneral` (18) and `GeometricModels` (47), and the
122 modules (2641 theorems) that `GeometricErgodicity` carries from the Chapter 14 project
`FErgodicity`, which cover Chapters 1–11, 13 and 14 and the renewal theory (see those projects'
READMEs for the lists and for how the copies differ from the originals). The carried modules are
identical to the copies in `GeometricErgodicity` except for the namespace and the imports. Unlike
the Chapter 16 and 17 projects `VUniformErgodicity` and `LimitTheorems`, this library carries
`GeometricConverseGeneral`, and `GeometricConverse` and `GeometricErgodicTheorem` have their
current module docstrings, so Theorem 15.4.2 without an atom (`theorem_15_4_2`,
`theorem_15_4_2_univ`) is part of this library. None of the Chapter 16 and Chapter 17 modules is
carried.

From these modules the Chapter 18 modules use, among others, path measures, the Markov and strong
Markov properties (`pathKernel`, `pathMeasure`, `natFilt`, `markov_property`,
`strong_markov_lintegral`), hitting times and potentials (`hitProb`, `firstHit`, `potKernel`), the
renewal theory (`IsIncrementLaw`, `IsAperiodicLaw`, `delayedRenewal`, `renewalTail`, `realConv`,
`theorem_13_2_2`, `lemma_D_7_1`), the forward recurrence time chain (`fwdRecKernel`,
`isInvariant_fwdRecInv`), atoms, splitting and the Regenerative Decomposition (`IsAtom`,
`Minorization`, `exists_skeleton_minorization`, `entryLaw`, `lastExitSeq`,
`regenerative_decomposition_47`), countable chains (`matKernel`, `IsIrreducibleChain`,
`IsRecurrentState`, `IsTransientState`, `isHarris_of_countable`), the random walk on `ℤ`
(`randomWalkKernel`, `theorem_8_1_5`), transience and Harris recurrence (`IsUniformlyTransient`,
`IsRecurrentChain`, `theorem_8_3_5`, `IsHarris`, `IsMaximalHarrisSet`, `theorem_9_1_5`,
`theorem_9_1_6`, `theorem_9_2_2_ii`), invariant measures and positivity (`IsInvariant`,
`IsInvariantMeasure`, `IsPositive`, `IsNull`, `IsPositiveHarris`, `proposition_10_1_1`,
`theorem_10_0_1`, `stationaryDist`), periods and cycles (`IsAperiodic`, `IsCycle`,
`absorbKernel`, `theorem_13_3_3_dirac`, `theorem_13_3_4_ii`), the total variation norm
(`tvNorm`), T-chains and Feller chains (`IsTChain`, `proposition_6_2_1`, `theorem_6_2_5_ii`,
`IsReachable`, `IsWeakFeller`, `proposition_6_1_1_iii`), e-chains, non-evanescence and topological
recurrence (`IsEChain`, `IsBoundedInProbability`, `IsNonEvanescent`, `IsTopRecurrent`), and (V4)
(`DriftV4`, `IsCoercive`). No Chapter 18 module depends, directly or through other modules, on
`ContinuousRenewal`, `CountableErgodic`, `CouplingRenewal`, `FErgodicModels`, `FPeriodicErgodic`,
`GIG1Embedding`, `GIG1Invariant`, `GIG1SmallSets`, `GeometricAtoms`, `GeometricConverse`,
`GeometricConverseGeneral`, `GeometricErgodicTheorem`, `GeometricModels`, `GeometricSkeletons`,
`KeyRenewal`, `LadderChains`, `LadderInvariant`, `LinearInvariant`, `MG1Invariant`,
`ModelInvariant`, `QueueInvariant`, `QueueInvariantMinimal`, `RandomWalkIntegers`, `Regeneration`,
`RenewalInvariant`, `RenewalSkeletons`, `RenewalSmallSets`, `SkipFreeWalk`, `SplitPetite`,
`StateSpaces`, `StochasticComparison` or `TopologicalExamples`.

Carried from the Chapter 12 project `InvarianceTightness` (228 theorems): 8 of its 9 Chapter 12
modules, `BoundedInProbability` (49), `LiminfCounterexample` (10), `GeneralizedSampling` (63),
`SigmaFiniteInvariant` (14), `EChainInvariant` (39), `EChainCriteria` (32), `BoundednessCriteria`
(19) and `TightnessCriteria` (2), identical to the copies there except for the namespace and the
imports. Its Chapter 12 module `AdaptiveControlStability` and the Chapter 7 modules that it
carries from `NonlinearStateSpace` are not carried; the modules of `InvarianceTightness` that the
eight need are among those carried from `GeometricErgodicity`. Boundedness in probability on
average and the Cesàro kernel (`IsBoundedInProbabilityOnAverage`, `cesaroKernel`,
`proposition_12_1_1`), the limit kernel `Π` of an e-chain and its properties (`eChainLimit`,
`theorem_12_4_1_i`, `theorem_12_4_1_ii`, `theorem_12_4_1_iii`, `theorem_12_4_3_i`, `eChainMass`,
`eChainLimit_open_le`, `cesaroFun`, `eventually_abs_cesaroFun_sub_le`), the dense family in
`C_c(X)` (`exists_dense_cc`, `tendsto_integral_bcf_of_cc`) and the drift bound
`isBoundedInProbability_of_drift` are used. No Chapter 18 module depends on `LiminfCounterexample`
or `TightnessCriteria`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (3991 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
