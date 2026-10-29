# Meyn and Tweedie, Chapter 17: Sample Paths and Limit Theorems, in Lean

This is the `StochasticStability/LimitTheorems` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 17 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 421–461, together with the parts of Appendix D that the chapter uses:
Kolmogorov's inequality (Theorem D.6.3), standard Brownian motion (§D.6.2) and the functional CLT
for martingales (Theorem D.6.4), pp. 561–563. Run the commands below from this directory. [Return to
the library index](../../README.md).

Chapter 17 studies the partial sums `Sₙ(g) = Σ_{k=1}^n g(Φₖ)` (17.1) through the law of large
numbers (LLN), the central limit theorem (CLT) and the law of the iterated logarithm (LIL), and
Theorem 17.0.1 collects the main results for positive Harris and `V`-uniformly ergodic chains, with
the asymptotic variance (17.3) written through the autocovariances. §17.1 links invariant random
variables and events to harmonic functions (Lemma 17.1.1, Theorem 17.1.3, Proposition 17.1.4),
proves the ergodic theorem for a stationary chain (Theorem 17.1.2), shows that bounded harmonic
functions of a Harris chain are constant (Theorem 17.1.5), so that a limit law holding under one
initial law holds under all (Proposition 17.1.6), and characterises positive Harris chains by the
LLN (Theorem 17.1.7). §17.2 cuts the path at the visits to an atom into i.i.d. cycles (17.9)–(17.10)
and derives the ratio LLN (Theorem 17.2.1) and, under the moment condition (17.14), the CLT and LIL
with the variance (17.13) (Theorem 17.2.2). §17.3 splits an `m`-skeleton and embeds the whole chain
in the split construction (17.21), so that the cycle sums are stationary and one-dependent (Theorem
17.3.1). This gives the ratio LLN for Harris chains with a σ-finite invariant measure (Theorem
17.3.2), the running maximum (Theorem 17.3.3), the bilinear model (Propositions 17.3.4–17.3.5) and
the CLT and LIL under the split-chain moment condition (17.31) (Theorem 17.3.6). §17.4 solves
Poisson's equation `ĝ − Pĝ = g − π(g)` (17.37) under (V3) (Proposition 17.4.1, Theorem 17.4.2),
writes `Sₙ(g)` as a martingale plus a bounded term (Theorem 17.4.3), and proves the functional CLT
for Markov chains from Theorem D.6.4 (Theorems 17.4.4–17.4.5), with the variance `π(ĝ² − (Pĝ)²)`
(17.46). §17.5 reduces all of this to a drift condition, the CLT moment condition (Lemmas
17.5.1–17.5.2, Theorems 17.5.3–17.5.4). §17.6 applies it to the random walk on a half line
(Proposition 17.6.1) and the linear state space model (Theorem 17.6.2). The commentary §17.7 adds
Poisson's equation without `π(V) < ∞` (Theorem 17.7.1) and a uniqueness criterion for invariance
equations (Theorem 17.7.2, Lemma 17.7.3).

Every numbered result of Chapter 17 is formalised: Theorem 17.0.1, Lemma 17.1.1, Theorems
17.1.2–17.1.3, Proposition 17.1.4, Theorem 17.1.5, Proposition 17.1.6, Theorem 17.1.7, Theorems
17.2.1–17.2.2, Theorems 17.3.1–17.3.3, Propositions 17.3.4–17.3.5, Theorem 17.3.6, Proposition
17.4.1, Theorems 17.4.2–17.4.5, Lemmas 17.5.1–17.5.2, Theorems 17.5.3–17.5.4, Proposition 17.6.1,
Theorem 17.6.2, Theorems 17.7.1–17.7.2 and Lemma 17.7.3, with the LIL wherever the book claims it
(except for the linear model in dimension `n > 1`), and from Appendix D, Theorem D.6.3, standard
Brownian motion and Theorem D.6.4. Two claims are false as printed. Each is refuted in Lean by a
counterexample of this project, and a corrected statement is proved. Theorem 17.1.7 (iii) does not
imply positive Harris recurrence (`theorem_17_1_7_counterexample`); the theorem is proved with
triviality of the invariant σ-field under every initial law. Theorem 17.3.2 (ii) implies neither (i)
nor (iii), even for an irreducible chain (`theorem_17_3_2_counterexample`,
`theorem_17_3_2_counterexample_irreducible`); the equivalence is proved for recurrent chains.
Further corrections concern proofs. The split-skeleton proof of Theorem 17.3.2 needs aperiodicity
(`skeleton_isHarris_counterexample`), and the theorem is proved for every Harris chain by another
route. The statement of Theorem 17.3.1 is garbled, and its proof treats consecutive cycle sums as
independent; the stationarity and one-dependence that the proof establishes are formalised. The
argument of Proposition 17.1.6 covers the LLN and the LIL but not the CLT, and the transfer of the
CLT and the FCLT from `P_π` to every initial law is proved separately, for every period. Further
points are made explicit. A countably generated σ-algebra is assumed where Theorem 9.1.4 is used;
`V`-uniform ergodicity is aperiodicity and (V4) for a petite set; "ergodic" is positive Harris and
aperiodic; the CLT and the LIL include the case `γ_g² = 0`; the irreducibility, aperiodicity and
petiteness hypotheses that the book takes from T-chain results of other chapters are hypotheses for
the bilinear and linear models; and the condition (17.27) is read in an extended sense. The
following are not formalised: the aperiodicity in Proposition 17.3.5; the LIL for the linear model
in dimension `n > 1` and its spectral density; the second limit of Lemma 17.7.3 (iii); the atom
solution (17.38) of Poisson's equation and the computation (17.52); Theorem D.6.3 (i) for `p` not an
even integer; the informal remarks; and the commentary of §17.7. See
[corrections](docs/corrections.md). The library contains **4007 theorems**. Of these, 1109 are in
the 54 Chapter 17 modules. The other 2898 are in the 130 modules carried from the Chapter 15 project
`GeometricErgodicity`, which cover Chapters 1–11 and 13–15 and the renewal theory.

The Chapter 17 modules build the probability they need. Mathlib has the i.i.d. CLT, martingales and
their convergence, Doob's maximal inequality, weak convergence and Prokhorov's theorem, but not
Birkhoff's pointwise ergodic theorem, the existence of Brownian motion, a martingale CLT, a
functional CLT or any LIL. They are proved here:

* **Birkhoff's ergodic theorem** (`BirkhoffErgodic`): the maximal ergodic lemma (`maximal_ergodic`)
  and a.e. convergence of Birkhoff averages to the conditional expectation on the invariant σ-field
  (`ae_tendsto_birkhoffLimit`), for a measure-preserving map of a finite measure space. It gives
  Theorem 17.1.2, the LLN for positive Harris chains (`lln_of_harris`), and, applied to the
  stationary path measure of an infinite invariant measure, the ratio limit theorem below.
* **Brownian motion and Wiener measure** (`LevyCiesielski`, `BrownianMotion`). Brownian motion on
  `[0, 1]` is built by the Lévy–Ciesielski series `Σ_m ξ_m S_m(t)` of Schauder functions with i.i.d.
  Gaussian coefficients (`gaussSeq`, `levyPath`). The covariance identity
  `Σ_m S_m(s) S_m(t) = min(s, t)` (`tendsto_schauder_sum_mul`) and a fourth-moment Borel–Cantelli
  argument give a.s. uniform convergence, so every path is continuous. `wienerMeasure` is its law on
  `C(unitInterval, ℝ)`, characterised by its linear finite-dimensional laws
  (`eq_wienerMeasure_of_fidiLin`), and the properties (i)–(iii) of §D.6.2 are proved
  (`continuous_brownian`, `indepFun_brownian_increment`, `gaussSeq_map_brownian_sub`).
* **Weak convergence on `C[0, 1]`** (`PathSpaceC01`, `TightnessC01`, `WeakConvergenceC01`).
  Polygonal interpolation `polygonal n` ((17.45), (D.7)); finite measures with the same linear
  finite-dimensional laws are equal (`ext_of_fidiLin`, Cramér–Wold); the modulus of continuity,
  Arzelà–Ascoli sets and Billingsley's tightness criterion (`isTightMeasureSet_of_modulus`);
  tightness plus converging finite-dimensional laws give convergence in distribution
  (`tendstoInDistribution_of_tight_of_fidiLin`, with Mathlib's Prokhorov theorem); the continuous
  functionals `f ↦ f(1)` and `f ↦ max f` of Theorem 17.4.5 (`continuous_supPath`).
* **Martingale limit theorems** (`MartingaleCLT`, `MartingaleArrayCLT`, `MartingaleUI`,
  `MartingaleFCLT`, `MartingaleFCLTGeneralTools`, `MartingaleFCLTGeneral`). McLeish's CLT for
  martingale differences (`martingale_clt`) and for martingale-difference arrays
  (`martingale_array_clt`); Doob's and Kolmogorov's maximal inequalities
  (`measureReal_sup_abs_ge_le`) and Lenglart's inequality (`measureReal_sum_ge_le_lenglart`); and
  **Theorem D.6.4 under the book's hypotheses (D.8)–(D.9)** (`theorem_D_6_4`), by truncation at
  `√(εn)`, stopping at the conditional-variance clock, a fourth-moment block bound and Billingsley's
  criterion. Shorter versions under uniformly integrable squares come first
  (`theorem_D_6_4_of_unifSqIntegrable`, `theorem_D_6_4_identDistrib`).
* **The Hartman–Wintner LIL** (`LILAnalysis`, `LILExponential`, `LILUpper`, `LILLower`, `IIDLIL`).
  For i.i.d. centred square-integrable summands, `hasLIL_iid`: the upper half by truncation and an
  exponential maximal inequality along geometric blocks (`lil_upper`), the lower half by the CLT on
  independent sub-blocks and the second Borel–Cantelli lemma (`lil_lower_normalized`). The LIL is
  the `ε`-form `HasLIL s γ`, which includes `γ = 0`.
* **One-dependent sequences** (`DependentLIL`, `SkeletonOneDependent`). For stationary one-dependent
  sequences (`IsOneDependent`, `IsStationarySeq`): the strong law
  (`IsOneDependent.ae_tendsto_average`), the CLT with variance `γ₀ + 2γ₁`
  (`IsOneDependent.tendstoInDistribution`), the LIL (`hasLIL_oneDependent`), and the random-index
  steps (17.35) (`IsOneDependent.tendstoInMeasure_randomIndex`) and `HasLIL.comp_index`.
* **Stout's LIL for martingales** (`MartingaleLILTools`, `MartingaleLILBlock`, `MartingaleLILUpper`,
  `MartingaleLILLower`, `MartingaleLIL`). For identically distributed square integrable martingale
  differences whose conditional variances and conditional truncated second moments obey the ergodic
  theorem (`hasLIL_martingale`): exponential supermartingales and Ville's inequality for the upper
  half; Kolmogorov's lower exponential bound applied conditionally to blocks with a variance budget,
  and a conditional second Borel–Cantelli lemma, for the lower half (`kolmogorov_lower`,
  `ae_frequently_of_cond_lower`). Applied to the Poisson martingale `Mₙ(g)` (17.43), it gives the
  LIL for Markov chains from every initial law, with no minorization and no aperiodicity
  (`hasLIL_pathSum_poisson`).
* **The split `m`-skeleton** (`SkeletonSplit`, `SkeletonCycles`, `SkeletonLimitTheorems`,
  `SkeletonErgodic`, `SkeletonMoment`). The book's construction (17.21) is a Markov chain on blocks
  `(Φ_{(n−1)m+1}, …, Φ_{nm})` with a level bit (`skelKernel`), whose skeleton states form the split
  chain of `Pᵐ` (`skel_map_skelState`) and from which the original path is recovered with law `P_μ`
  (`skel_map_recover`). Its cycle sums are stationary and one-dependent (Theorem 17.3.1,
  `theorem_17_3_1_general`), which gives Theorems 17.3.2 and 17.3.6 for any `m` and, with the
  existence of the split skeleton for aperiodic Harris chains (`exists_skeleton_split`), under the
  book's hypotheses. `SkeletonMoment` proves the moment bound (17.53) of Lemma 17.5.2 (ii) and so
  the LIL of §17.5 by the book's route. `SplitLimitTheorems` is the case `m = 1`.
* **The periodic case** (`PeriodicPoisson`, `PeriodicInvariance`, `PeriodicCLT`). Theorems 17.4.2
  and 17.7.1 are proved for every period through the resolvent `K_{a_ε}`, as in the book: the
  identity (17.40) (`resolvent_eq_dirac_add_comp`), (V3) for `K_{a_{1/2}}`
  (`driftV3_resolvent_half`) and the transfer (17.42) (`isPoissonSolution_of_resolvent`). Theorem
  17.7.2 and Lemma 17.7.3 use Cesàro convergence from Theorem 14.3.6 (i), and the CLT is carried
  from `P_π` to every initial state of a periodic chain through phase averages
  (`tendstoInDistribution_pathKernel_of_stationary_periodic`).
* **Theorem 17.3.2 without Chacon–Ornstein** (`GapsChaconOrnstein`, `GapsTransientWalk`). The
  maximal ergodic lemma holds for the shift on `P_π = ∫ P_x π(dx)` for any σ-finite invariant `π`
  (`measurePreserving_shift_one_of_isInvariant`), and with the zero–one law of a Harris chain
  (`harris_dichotomy`) it gives the ratio limit for every Harris chain, null recurrent ones included
  (`theorem_17_3_2_harris`, Hopf's argument). The equivalences of Theorem 17.3.2 follow for
  recurrent chains (`theorem_17_3_2_tfae`), with the two counterexamples.

Several routes differ from the book. Birkhoff's theorem, the i.i.d. LIL, Kolmogorov's inequality,
Brownian motion and Theorem D.6.4 are proved where the book cites them. The ratio limit theorem for
Harris chains uses Hopf's maximal-lemma argument where the book uses the Chacon–Ornstein theorem and
the split skeleton (the book's route is formalised too, for aperiodic chains). The CLT of
§17.4–§17.5 comes directly from McLeish's martingale CLT for `Mₙ(g)` and a transfer of
characteristic functions, besides the FCLT route of the book (`theorem_17_4_5_clt_periodic`,
`theorem_17_5_3_clt`). The LIL of Theorems 17.0.1 (iv), 17.5.3, 17.5.4 and of §17.6 is proved twice:
by the book's split skeleton (`theorem_17_5_3_lil_skeleton`) and by Stout's martingale LIL
(`theorem_17_5_3_lil_poisson`). Proposition 17.4.1 uses a martingale argument in place of Theorem
14.3.6. The aperiodic Theorem 17.7.1 sums `Pⁿg(x) − Pⁿg(x₀)` with the `f`-norm bound of Theorem
14.3.4. Proposition 17.3.5 constructs the stationary output series instead of proving tightness, and
Theorem 17.6.2 computes the variance through Poisson's equation instead of the spectral density. The
degenerate case `γ_g² = 0` of Theorems 17.5.3–17.5.4 uses vanishing martingale increments and
Proposition 17.1.6 instead of the martingale convergence theorem.

The chapter rests on nine groups of results.

* **Invariant σ-fields and the LLN** (`BirkhoffErgodic`, `InvariantFields`, `HarrisLLN`).
  `h_Y = expectFn P Y` (17.6), invariant random variables (`IsPathInvariant`, `IsInvariantRV`) and
  harmonic functions (`IsHarmonic`, (17.8)). Lemma 17.1.1 is `lemma_17_1_1`, Theorem 17.1.2 is
  `theorem_17_1_2`, Theorem 17.1.3 is `theorem_17_1_3_i` and `theorem_17_1_3_ii`, Proposition 17.1.4
  is `proposition_17_1_4`, Theorem 17.1.5 is `theorem_17_1_5` and Proposition 17.1.6 is
  `proposition_17_1_6`. Theorem 17.1.7 is `theorem_17_1_7`, with `theorem_17_1_7_counterexample`.
* **Chains with an atom** (`RegenerationCycles`, `AtomLLN`, `KolmogorovAnscombe`, `AtomCLT`). The
  excursions between visits are i.i.d. random paths (`map_cycles_eq_infinitePi`), and (17.10) is
  `lintegral_cycleSumE`. Theorem 17.2.1 is `theorem_17_2_1` and `theorem_17_2_1_harris`.
  Kolmogorov's inequality (`kolmogorov_ineq`) gives the random-index step (17.19)–(17.20)
  (`tendstoInMeasure_anscombe`), and Theorem 17.2.2 is `theorem_17_2_2`, with (17.13) as
  `theorem_17_2_2_variance` and the LIL as `theorem_17_2_2_lil`.
* **Splitting and the LLN for Harris chains** (`SplitLimitTheorems`, `LLNApplications`, the
  `Skeleton…` modules, `GapsChaconOrnstein`, `GapsTransientWalk`). Theorem 17.3.1 is
  `theorem_17_3_1_general` (`theorem_17_3_1` for `m = 1`), (17.23) is `theorem_17_3_1_general_mean`,
  and Theorem 17.3.2 is `theorem_17_3_2_harris` and `theorem_17_3_2_tfae`, with
  `theorem_17_3_2_skeleton` by the book's route. Theorem 17.3.3 is `theorem_17_3_3`.
* **The bilinear model** (`GapsBilinear`). Proposition 17.3.4 is `proposition_17_3_4_dbl`, the
  backward LLN (17.26) is `theorem_17_26`, and Proposition 17.3.5 is `proposition_17_3_5`, through
  the stationary solution `dblStationaryLaw`.
* **The CLT and LIL for Harris chains** (`SkeletonLimitTheorems`, `SkeletonErgodic`, `ChainLIL`).
  The variance (17.32) is `skelCLTVariance`, and Theorem 17.3.6 is `theorem_17_3_6_skeleton` and
  `theorem_17_3_6_lil_skeleton` (general forms `theorem_17_3_6_general`,
  `theorem_17_3_6_lil_general`; `m = 1`: `theorem_17_3_6`, `theorem_17_3_6_lil`).
* **Poisson's equation** (`PoissonEquation`, `PeriodicPoisson`, `PoissonInvariance`,
  `PeriodicInvariance`). `IsPoissonSolution P g ĝ c` is (17.37) and `poissonMart` is (17.43).
  Proposition 17.4.1 is `proposition_17_4_1`, Theorem 17.4.2 is `theorem_17_4_2_periodic`
  (`theorem_17_4_2`, aperiodic), and Theorem 17.4.3 is `theorem_17_4_3`. Theorems 17.7.1–17.7.2 and
  Lemma 17.7.3 are `theorem_17_7_1_periodic`, `theorem_17_7_2_periodic` and `lemma_17_7_3_periodic`,
  with aperiodic forms `theorem_17_7_1`, `theorem_17_7_2`, `lemma_17_7_3`; `V* = gKernelFn P C f`
  (17.60).
* **The functional CLT** (`FunctionalCLT`, with the path-space and martingale modules). Theorem
  17.4.4 is `theorem_17_4_4`, from `theorem_D_6_4` with (D.8)–(D.9) for `Mₙ(g)`
  (`condVar_poisson_tendsto`, `lindeberg_poisson`) and (17.48)
  (`norm_sumPath_sub_polygonal_poissonMart_le`). Theorem 17.4.5 is `theorem_17_4_5_max`,
  `theorem_17_4_5_endpoint` and the CLT forms `theorem_17_4_5_clt_harris`,
  `theorem_17_4_5_clt_periodic` (`MartingaleCLT`, `CLTTransfer`, `CLTCriteria`, `PeriodicCLT`).
* **Criteria for the CLT and LIL** (`CLTMoment`, `SkeletonMoment`, `MartingaleLILChains`,
  `MartingaleLILApplications`). Lemma 17.5.1 is `lemma_17_5_1`, Lemma 17.5.2 is `lemma_17_5_2_i` and
  `lemma_17_5_2_ii`, Theorem 17.5.3 is `theorem_17_5_3` with (17.56), `theorem_17_5_3_clt` and
  `theorem_17_5_3_degenerate`, and Theorem 17.5.4 is `theorem_17_5_4` and `theorem_17_5_4_clt`.
  Theorem 17.0.1 is `theorem_17_0_1` and `theorem_17_0_1_iv`. The LILs are the `…_lil_poisson` and
  `…_lil_skeleton` forms.
* **Applications** (`LimitApplications`, `GapsVectorLinear`). Proposition 17.6.1 is
  `proposition_17_6_1`, `proposition_17_6_1_variance`, `proposition_17_6_1_clt` and
  `proposition_17_6_1_lil_poisson`. Theorem 17.6.2 is `theorem_17_6_2_vector` and
  `theorem_17_6_2_vector_clt` on `ℝⁿ`, with the Lyapunov matrix (`lyapunov_equation`) and the vector
  CLT (`theorem_17_6_2_vector_clt_vec`), and `theorem_17_6_2`, `theorem_17_6_2_clt`,
  `theorem_17_6_2_lil_poisson` for the scalar model.

The library covers the chapter as follows.

* **Introduction** (pp. 421–423). (17.1)–(17.4), the LLN, CLT and LIL, and Theorem 17.0.1.
* **Invariant random variables and events** (§17.1.1). (17.5)–(17.7), Lemma 17.1.1 and Theorem
  17.1.2.
* **Harmonic functions** (§17.1.2). (17.8), Theorem 17.1.3, Proposition 17.1.4, Theorem 17.1.5 and
  Proposition 17.1.6, with its correction.
* **The LLN for positive Harris chains** (§17.1.3). Theorem 17.1.7, its counterexample and
  correction.
* **Chains possessing an atom** (§17.2). (17.9)–(17.20), Theorems 17.2.1 and 17.2.2.
* **Splitting general Harris chains** (§17.3.1). (17.21)–(17.24) and Theorem 17.3.1, corrected.
* **The LLN for general Harris chains** (§17.3.2). Theorem 17.3.2, its counterexamples and
  correction, by Hopf's argument and by the book's route.
* **Applications of the LLN** (§17.3.3). Theorem 17.3.3 and (17.25); (17.26)–(17.29), Propositions
  17.3.4 and 17.3.5.
* **The CLT and LIL for Harris chains** (§17.3.4). (17.31)–(17.36) and Theorem 17.3.6.
* **Poisson's equation** (§17.4.1). (17.37), (17.39)–(17.44), Proposition 17.4.1, Theorems 17.4.2
  and 17.4.3.
* **The functional CLT** (§17.4.2). (17.45)–(17.48), Theorems 17.4.4 and 17.4.5.
* **The representations of `γ_g²`** (§17.4.3). (17.49), (17.50) through (17.56), (17.51).
* **Criteria for the CLT and the LIL** (§17.5). The CLT moment condition, Lemmas 17.5.1–17.5.2,
  (17.53)–(17.56), Theorems 17.5.3–17.5.4.
* **Applications** (§17.6). Proposition 17.6.1; (17.57), Theorem 17.6.2 and the vector CLT.
* **Commentary** (§17.7). Theorems 17.7.1–17.7.2, Lemma 17.7.3, (17.59)–(17.62).
* **Appendix D.6** (pp. 561–563). Theorem D.6.3, (D.7), standard Brownian motion, Theorem D.6.4 with
  (D.8)–(D.9).

All names are in the namespace `MeynTweedie.LimitTheorems`. See the [source map](docs/source-map.md)
and the [corrections](docs/corrections.md).

## Library map

### The Chapter 17 modules (1109 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [BirkhoffErgodic](LimitTheorems/BirkhoffErgodic.lean) | 47 | Background for §17.1: the maximal ergodic lemma, Birkhoff's pointwise ergodic theorem for a measure-preserving map of a finite measure space, the limit as a conditional expectation on the invariant σ-field, the ergodic case |
| [InvariantFields](LimitTheorems/InvariantFields.lean) | 35 | §17.1.1–17.1.2: invariant random variables, `h_Y` (17.6)–(17.7), harmonic functions (17.8) and their martingales, Lemma 17.1.1, Theorem 17.1.3, Proposition 17.1.4, Theorem 17.1.5, Proposition 17.1.6 for shift-invariant events |
| [HarrisLLN](LimitTheorems/HarrisLLN.lean) | 23 | §17.1.1, §17.1.3: `Sₙ(g)` (17.1) as Birkhoff sums, the shift on `P_π`, ergodicity of `P_π` for Harris chains, Theorem 17.1.2, the LLN for Harris chains, Theorem 17.1.7 corrected and its counterexample |
| [RegenerationCycles](LimitTheorems/RegenerationCycles.lean) | 31 | §17.2: excursions and cycles between visits to an atom, visit times, cycle sums (17.9), the strong Markov property at the visit, the i.i.d. cycles (`map_cycles_eq_infinitePi`), the strong law for cycle functionals |
| [AtomLLN](LimitTheorems/AtomLLN.lean) | 20 | §17.2.1: (17.10), averages along visit times, the sandwich (17.11)–(17.12), Theorem 17.2.1 |
| [KolmogorovAnscombe](LimitTheorems/KolmogorovAnscombe.lean) | 6 | Theorem D.6.3 for independent sums (Kolmogorov's inequality) and the random-index step (17.19)–(17.20) |
| [AtomCLT](LimitTheorems/AtomCLT.lean) | 26 | §17.2.2: i.i.d. cycle variables, the number of completed cycles, (17.15), (17.18), (17.13), Theorem 17.2.2 (CLT) |
| [LLNApplications](LimitTheorems/LLNApplications.lean) | 5 | §17.3.2–17.3.3: Theorem 17.3.2 for positive Harris chains, Theorem 17.3.3 and (17.25), Proposition 17.3.4 for any positive Harris chain |
| [SplitLimitTheorems](LimitTheorems/SplitLimitTheorems.lean) | 9 | §17.3 for a one-step minorization: transfer from the split chain, Theorem 17.3.1 (i.i.d. cycle sums, (17.22)–(17.23)), Theorem 17.3.2 (iii) ⇒ (i), Theorem 17.3.6 (CLT), (17.32) |
| [SkeletonSplit](LimitTheorems/SkeletonSplit.lean) | 51 | §17.3.1: the split `m`-skeleton with the whole chain attached (17.21), the block kernel and density, lumpable chains, the skeleton states as the split chain of `Pᵐ`, recovery of the original chain |
| [SkeletonOneDependent](LimitTheorems/SkeletonOneDependent.lean) | 32 | §17.3: stationary one-dependent sequences, independence of even and odd terms, the big blocks (17.36), the strong law, the CLT, the random-index step (17.35) |
| [SkeletonCycles](LimitTheorems/SkeletonCycles.lean) | 58 | §17.3.1: cycle sums of the split skeleton, the decomposition (17.24), the fresh restart after a visit, the regeneration induction, Theorem 17.3.1 corrected (stationary, one-dependent, law (17.22)), (17.23) |
| [SkeletonLimitTheorems](LimitTheorems/SkeletonLimitTheorems.lean) | 32 | §17.3.2, §17.3.4 for a general `m`: completed segments, (17.33)–(17.34), Theorem 17.3.2 (iii) ⇒ (i), the variance (17.32), Theorem 17.3.6 (CLT and LIL) |
| [SkeletonErgodic](LimitTheorems/SkeletonErgodic.lean) | 9 | §17.3.1: existence of a Harris split skeleton for aperiodic Harris chains, the counterexample for periodic chains, Theorems 17.3.2 and 17.3.6 under the book's hypotheses |
| [GapsChaconOrnstein](LimitTheorems/GapsChaconOrnstein.lean) | 23 | Theorem 17.3.2: the shift on `P_π` for σ-finite `π`, the Harris zero–one law, Hopf's argument, (iii) ⇒ (i) for every Harris chain, (i) ⇔ (iii), (ii) ⇔ (iii) for recurrent chains, the corrected equivalence and the counterexample on `Bool` |
| [GapsTransientWalk](LimitTheorems/GapsTransientWalk.lean) | 9 | Theorem 17.3.2: the biased walk on `ℤ`, its constant bounded harmonic functions, the irreducible counterexample to (ii) ⇒ (iii) |
| [GapsBilinear](LimitTheorems/GapsBilinear.lean) | 37 | §17.3.3: Proposition 11.4.2 (copied), the bilinear model and its parameter process, Proposition 17.3.4, the Bernoulli shift, stationary solutions of random recursions, the backward LLN (17.26), (17.28)–(17.29), Proposition 17.3.5, the remark on (17.27) |
| [PoissonEquation](LimitTheorems/PoissonEquation.lean) | 12 | §17.4.1, §17.4.3: Poisson's equation (17.37), `Mₙ(g)` (17.43), Proposition 17.4.1, Theorem 17.4.2 (aperiodic), Theorem 17.4.3 (17.44), (17.46), (17.49) |
| [PoissonInvariance](LimitTheorems/PoissonInvariance.lean) | 6 | §17.7 (aperiodic): `V*` (17.60), Lemma 17.7.3 with (17.61)–(17.62), Theorems 17.7.1 and 17.7.2 |
| [PeriodicPoisson](LimitTheorems/PeriodicPoisson.lean) | 13 | §17.4.1, §17.7: the resolvent identity (17.40), (17.41)–(17.42), (V3) for the resolvent, Theorems 17.4.2 and 17.7.1 for every period |
| [PeriodicInvariance](LimitTheorems/PeriodicInvariance.lean) | 7 | §17.7: Cesàro convergence from Theorem 14.3.6 (i), Lemma 17.7.3 and Theorem 17.7.2 for every period |
| [MartingaleCLT](LimitTheorems/MartingaleCLT.lean) | 17 | Background for §17.4–17.5: McLeish's CLT for martingale differences |
| [CLTTransfer](LimitTheorems/CLTTransfer.lean) | 8 | §17.1.2, §17.4–17.5: the LLN for path functionals, the transfer of a CLT from `P_π` to every `P_x` for aperiodic chains |
| [CLTCriteria](LimitTheorems/CLTCriteria.lean) | 6 | §17.4.2, §17.5: orthogonal martingale increments, the increments of `Mₙ(g)` under `P_π`, Theorem 17.4.5 (CLT, aperiodic), (17.4) |
| [PeriodicCLT](LimitTheorems/PeriodicCLT.lean) | 9 | §17.4.2: phase averages, the transfer of a CLT from `P_π` to every `P_x` and `P_μ` for every period, Theorem 17.4.5 (CLT) for every period |
| [CLTMoment](LimitTheorems/CLTMoment.lean) | 18 | §17.5 and Theorem 17.0.1: the degenerate variance, autocovariances, the series (17.3) and (17.39), Lemma 17.5.1, Lemma 17.5.2 (i), Theorem 17.5.3 with (17.56), Theorem 17.5.4, Theorem 17.0.1 |
| [PathSpaceC01](LimitTheorems/PathSpaceC01.lean) | 41 | App. D.6.2: polygonal interpolation (17.45), (D.7), linear finite-dimensional functionals, the Borel σ-algebra of `C[0, 1]`, uniqueness of laws by Cramér–Wold |
| [TightnessC01](LimitTheorems/TightnessC01.lean) | 29 | App. D.6.2: the modulus of continuity, Arzelà–Ascoli sets, Billingsley's tightness criterion, block conditions for partial-sum processes |
| [WeakConvergenceC01](LimitTheorems/WeakConvergenceC01.lean) | 16 | App. D.6.2: tightness plus finite-dimensional laws, continuous mapping for `u(1)` and `max u`, converging together |
| [LevyCiesielski](LimitTheorems/LevyCiesielski.lean) | 53 | App. D.6.2: Schauder functions, the covariance identity, Gaussian sums, a.s. uniform convergence, the Lévy–Ciesielski path |
| [BrownianMotion](LimitTheorems/BrownianMotion.lean) | 22 | App. D.6.2: standard Brownian motion on `[0, 1]`, its Gaussian finite-dimensional laws, Wiener measure, the defining properties (i)–(iii) |
| [MartingaleArrayCLT](LimitTheorems/MartingaleArrayCLT.lean) | 9 | Background for Theorem D.6.4: the CLT for martingale-difference arrays, weighted sums, finite-dimensional laws of partial sums |
| [MartingaleUI](LimitTheorems/MartingaleUI.lean) | 20 | Background for Theorem D.6.4: Doob's and Kolmogorov's inequalities (Theorem D.6.3 (i), even `p`), truncation, uniformly integrable squares, block maxima |
| [MartingaleFCLT](LimitTheorems/MartingaleFCLT.lean) | 12 | Theorem D.6.4 under uniformly integrable squares: finite-dimensional laws, tightness, the identically distributed case |
| [MartingaleFCLTGeneralTools](LimitTheorems/MartingaleFCLTGeneralTools.lean) | 21 | Theorem D.6.4: arrays along rows, localisation, Lenglart's inequality, (D.9) and large increments, a fourth-moment bound under a variance clock, the truncated and stopped increments |
| [MartingaleFCLTGeneral](LimitTheorems/MartingaleFCLTGeneral.lean) | 20 | Theorem D.6.4 under (D.8)–(D.9): tightness of the localised process, the law of large numbers for the squares, finite-dimensional laws |
| [FunctionalCLT](LimitTheorems/FunctionalCLT.lean) | 20 | §17.4.2: transfer from `P_π` to every initial law, the running maximum, (D.8)–(D.9) for `Mₙ(g)`, (17.48), Theorem 17.4.4, Theorem 17.4.5 |
| [LILAnalysis](LimitTheorems/LILAnalysis.lean) | 26 | Background for the LIL: the normaliser `√(2n log log n)`, Kronecker's lemma, geometric index sequences, truncation levels |
| [LILExponential](LimitTheorems/LILExponential.lean) | 8 | Background for the LIL: Kolmogorov's upper exponential bound, the exponential maximal inequality, independence of blocks |
| [LILUpper](LimitTheorems/LILUpper.lean) | 12 | The upper half of the Hartman–Wintner LIL |
| [LILLower](LimitTheorems/LILLower.lean) | 13 | The lower half of the Hartman–Wintner LIL, by the CLT on sub-blocks |
| [IIDLIL](LimitTheorems/IIDLIL.lean) | 7 | The LIL of p. 422 in `ε`-form (`HasLIL`), the Hartman–Wintner LIL for i.i.d. sequences |
| [DependentLIL](LimitTheorems/DependentLIL.lean) | 24 | §17.2–17.3: perturbations of the LIL, the random-index step and its counterexample, measurability of the LIL event, one-dependent sequences, the LIL for stationary one-dependent sequences |
| [ChainLIL](LimitTheorems/ChainLIL.lean) | 10 | §17.2–17.5: the LIL of Theorems 17.2.2 and 17.3.6 (`m = 1`), and of Theorems 17.0.1 (iv) and 17.5.3 under a one-step minorization and (17.31) |
| [SkeletonMoment](LimitTheorems/SkeletonMoment.lean) | 29 | §17.5: the moment bound (17.53)–(17.55), Lemma 17.5.2 (ii), (17.32) as `π(ĝ² − (Pĝ)²)`, the LIL of Theorems 17.5.3, 17.5.4 and 17.0.1 (iv) by the book's route |
| [MartingaleLILTools](LimitTheorems/MartingaleLILTools.lean) | 38 | Background for the martingale LIL: exponential super- and submartingales, Ville's inequality (Theorem D.6.3 (ii) on finite horizons), truncation of martingale differences |
| [MartingaleLILBlock](LimitTheorems/MartingaleLILBlock.lean) | 26 | Background for the martingale LIL: Kolmogorov's lower exponential bound, blocks with a variance budget, the conditional second Borel–Cantelli lemma |
| [MartingaleLILUpper](LimitTheorems/MartingaleLILUpper.lean) | 7 | The upper half of the LIL for martingale differences |
| [MartingaleLILLower](LimitTheorems/MartingaleLILLower.lean) | 12 | The lower half of the LIL for martingale differences (Stout) |
| [MartingaleLIL](LimitTheorems/MartingaleLIL.lean) | 3 | The Hartman–Wintner LIL for martingale differences (Stout) |
| [MartingaleLILChains](LimitTheorems/MartingaleLILChains.lean) | 13 | §17.4–17.5: shift invariance of the LIL event, conditional averages along the chain, the LIL for `Mₙ(g)` and for `Sₙ(g − c)` from every initial law |
| [MartingaleLILApplications](LimitTheorems/MartingaleLILApplications.lean) | 5 | The LIL of Theorems 17.0.1 (iv), 17.5.3, 17.5.4, Proposition 17.6.1 and Theorem 17.6.2 without minorization |
| [LimitApplications](LimitTheorems/LimitApplications.lean) | 14 | §17.6: positive Harris recurrence from (V4), the random walk on a half line and Proposition 17.6.1, the scalar linear model and Theorem 17.6.2 |
| [GapsVectorLinear](LimitTheorems/GapsVectorLinear.lean) | 50 | §17.6.2: the Lyapunov matrix (12.34), one step of LSS(F, G), (V4) for `1 + xᵀMx`, Poisson's equation for linear functions, Theorem 17.6.2 on `ℝⁿ`, the CLT for `cᵀXₖ`, the vector-valued CLT, irreducibility and petite compact sets |

### Carried modules (2898 theorems)

Carried from the Chapter 15 project `GeometricErgodicity` (2898 theorems): 130 of its 131 modules,
all but `GeometricConverseGeneral`. They are its 8 Chapter 15 modules (257 theorems) and the 122
modules (2641 theorems) that `GeometricErgodicity` carries from the Chapter 14 project
`FErgodicity`, which cover Chapters 1–11, 13 and 14 and the renewal theory (see those projects'
READMEs for the lists and for how the copies differ from the originals). The carried modules are
identical to the copies in the Chapter 16 project `VUniformErgodicity` except for the namespace and
the imports. In particular `GeometricConverse` and `GeometricErgodicTheorem` keep the module
docstrings they had before `GeometricConverseGeneral` was written, so Theorem 15.4.2 without an atom
is not part of this library. None of the Chapter 16 modules, and none of the Chapter 12 and Chapter
7 modules carried by `VUniformErgodicity`, is carried here.

From the carried modules the Chapter 17 modules use, among others, path measures and the shift
(`pathKernel`, `pathMeasure`, `shift`, `natFilt`), hitting times and atoms (`firstHit`, `hitProb`,
`IsAtom`, `IsAccessibleAtom`, `atomMeasure`), Harris recurrence and its consequences (`IsHarris`,
`IsPositiveHarris`, `theorem_9_1_4`, `theorem_9_1_5`, `theorem_9_1_6`, `theorem_9_1_8`), invariant
measures (`IsInvariant`, `IsInvariantMeasure`, `proposition_10_1_1`, `theorem_10_2_1_ii_smul`,
`proposition_10_4_1_ii`, `theorem_10_4_9_equiv`), splitting and small sets (`Minorization`,
`theorem_5_1_3_i_path`, `theorem_5_1_3_ii`, `theorem_5_2_3`, `proposition_5_5_4_i`,
`proposition_5_5_6_i`), aperiodicity and total variation convergence (`IsAperiodic`,
`theorem_13_3_3_dirac`, `theorem_13_3_4_i`), `f`-regularity and the `f`-Norm Ergodic Theorem
(`DriftV3`, `IsFRegularSet`, `gKernelFn`, `tabooPotFn`, `theorem_11_3_5_i`,
`theorem_14_0_1_consequences`, `theorem_14_2_5`, `theorem_14_3_6_i`, `tsum_fNorm_le_of_driftV3`),
(V4) (`DriftV4`, `lemma_15_2_8`, `lemma_15_2_9`), and the models (`halfLineWalkKernel`,
`proposition_14_4_1`, `ar1Kernel`, `lssMatrixKernel`, `proposition_6_3_5`). No Chapter 17 module
depends, directly or through other modules, on `CompactPetite`, `ContinuousRenewal`,
`CountableErgodic`, `CouplingRenewal`, `EChains`, `EChainsStability`, `ErgodicTheorem`,
`GIG1Embedding`, `GIG1Invariant`, `GIG1SmallSets`, `KeyRenewal`, `ModelKernels`, `ModelQueues`,
`ModelRenewal`, `ModelStorage`, `PoissonCounts`, `RandomWalkMeanZero`, `Regeneration`,
`RenewalInvariant`, `RenewalSkeletons`, `RenewalSmallSets`, `SkipFreeWalk`, `SpecificKernels`,
`SplitPetite`, `StateSpaces` or `TopologicalExamples`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (4658 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
