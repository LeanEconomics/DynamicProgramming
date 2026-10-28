# Meyn and Tweedie, Chapter 16: V-Uniform Ergodicity, in Lean

This is the `StochasticStability/VUniformErgodicity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 16 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 392–420. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 16 reads the geometric ergodicity of Chapter 15 as convergence in an operator norm. For
`V ≥ 1` the `V`-norm distance between two kernels is
`|||P₁ − P₂|||_V = sup_x ‖P₁(x, ·) − P₂(x, ·)‖_V / V(x)` (16.1), and the chain is `V`-uniformly
ergodic if `|||Pⁿ − 1 ⊗ π|||_V → 0` (16.2). §16.1 shows that `||| · |||_V` is the operator norm on
the weighted space `L∞_V` (Lemma 16.1.1) and that it is submultiplicative, so one distance below
`1` gives a geometric rate (Proposition 16.1.3). (V4) for a petite set gives `V`-uniform ergodicity
(Theorem 16.1.2), and conversely a geometric rate in `||| · |||_V` gives (V4) for an equivalent
function (Theorem 16.1.4). Together they make Theorem 16.0.1. `V`-uniformly ergodic chains are
`V`-geometrically mixing (Theorem 16.1.5, (16.17)). The forward recurrence time `δ`-skeleton and
the random walk on `[0, ∞)` are `e^{γx}`-uniformly ergodic when the increments have exponential
moments, `Γ ∈ G⁺(γ)` (16.18)–(16.19). §16.2 takes `V ≡ 1`, uniform ergodicity. It is equivalent to
a uniform geometric rate (Theorem 16.2.1), to `X` petite or small, to bounded hitting times or
their geometric moments, to a bounded solution of (V4) (Theorem 16.2.2), and to Doeblin's
condition (Theorem 16.2.3). A minorization of the whole space gives the explicit rate of
Theorem 16.2.4. These results make Theorem 16.0.2. Uniform ergodicity need not give geometric
convergence of unbounded functions (§16.2.2). A T-chain on a compact space is uniformly ergodic
(Theorem 16.2.5), and so is a Lagrange stable nonlinear state space model on each compact
absorbing set (Lemma 16.2.6, Theorem 16.2.7). §16.3 strengthens Foster's criterion (16.25) to
`e^{δV}`-uniform ergodicity when the right increments of `V` have uniform exponential moments and
the left increments uniform second moments (Theorem 16.3.1). The examples (16.30) and (15.20) show
that neither condition can be dropped. Geometric ergodicity also gives geometric tails to `π`
(Theorem 16.3.2). §16.4 applies Theorem 16.3.1 to the embedded M/G/1 queue, a gated-limited
polling system and the M/PH/1 queue (Theorems 16.4.1–16.4.3). §16.5 treats the multidimensional
RCA model (Theorem 16.5.1) and the simple adaptive control model (Proposition 16.5.2, (16.49)).
§16.6 is commentary.

Every numbered result of Chapter 16 is formalised: Theorems 16.0.1–16.0.2, Lemma 16.1.1,
Theorem 16.1.2, Proposition 16.1.3, Theorems 16.1.4–16.1.5, Theorems 16.2.1–16.2.5, Lemma 16.2.6,
Theorem 16.2.7, Theorems 16.3.1–16.3.2, Theorems 16.4.1–16.4.3, Theorem 16.5.1 and
Proposition 16.5.2. Two claims are false as printed. Each is refuted in Lean by a counterexample of
this project, and a corrected statement is proved. Theorem 16.0.1 (i) does not imply (ii)–(iv) when
some `|||Pⁿ − 1 ⊗ π|||_V` is infinite (`theorem_16_0_1_counterexample`); the theorem is proved with
every distance finite in (i). The rate `2ρ^{n/m}` of (16.11) and (16.21) needs the integer part
`⌊n/m⌋` (`theorem_16_2_4_counterexample`). Further corrections have no counterexample. The
transition probabilities of the M/PH/1 queue on p. 413 are corrected in four places. The proof of
Theorem 16.3.1 uses the petite set `C ∩ {V < b + 1}` in place of `C`. The linear test functions of
the M/G/1 and polling proofs are rescaled, `1` is added to the weights `|x|²` of Theorem 16.5.1 and
(16.44) of Proposition 16.5.2, which vanish at `0`, and the bound for the forward recurrence time
chain on p. 399 needs a constant. Further points are made explicit. `V ≥ 1` is measurable and finite
and `μ(V) < ∞` is assumed where the book's signed measures of finite `V`-variation are used;
Theorem 16.0.2 is proved for `ψ`-irreducible chains; "ergodic" in Theorem 16.3.1 is aperiodicity;
Theorem 16.3.2 holds for every `B ∈ B⁺(X)` and needs no condition on `g`; the forward recurrence
time chain lives on `ℝ` with `C = (−∞, δ]`; the polling system is read literally, with no switchover
times; and the RCA model takes the two results of [299], `ψ`-irreducibility, aperiodicity and petite
compact sets as hypotheses. The ladder chain (16.24) is replaced by a simpler chain with the same
property (`reset_not_fGeometric`). The following are not formalised: the centred bound (16.16); the
necessity of `Γ ∈ G⁺(γ)` for the forward recurrence time chain and its uniform ergodicity on
`[0, c]` for bounded range; the identification of the linear function with `E_i[σ₀]` in the M/PH/1
queue; the T-chain property of the RCA model from (RCA3); the informal remarks; and the commentary
of §16.6. See [corrections](docs/corrections.md). The library contains **3489 theorems**. Of these,
265 are in the 17 Chapter 16 modules. The other 3224 are in the 146 modules carried from earlier
projects: 130 from the Chapter 15 project `GeometricErgodicity`, which cover Chapters 1–11 and 13–15
and the renewal theory; 13 from the Chapter 12 project `InvarianceTightness`, among them its copies
of the nonlinear state space modules of Chapter 7 (`NSS*`, `ControlModel` and the others) and
`AdaptiveControlStability`; and the renewal modules `RenewalMeasure`, `RenewalRegeneration` and
`RenewalChain` of the Chapter 14 project `FErgodicity`.

The chapter rests on nine groups of results.

* **The operator norm** (`OperatorNorm`). `|f|_V` is `vNormFn V f`, `|||P₁ − P₂|||_V` (16.1) is
  `vOpNorm V P₁ P₂` and `|||Pⁿ − 1 ⊗ μ|||_V` is `vErgDist V P μ n`, with `1 ⊗ μ = Kernel.const X μ`.
  Lemma 16.1.1 is `lemma_16_1_1` and `lemma_16_1_1_bounded`. `μ(f) ≤ ‖μ − ν‖_f + ν(f)`
  (`lintegral_le_fNorm_add`) gives (16.15) (`lintegral_pow_le_vErgDist`). The submultiplicativity
  is `vOpNorm_comp_le` and `vErgDist_add_le`, Proposition 16.1.3 is `proposition_16_1_3`, and
  Theorem 16.1.2 is `theorem_16_1_2`, through `vErgDist_le_of_driftV4` and Theorem 15.4.1.
* **`V`-uniform ergodicity** (`VUniformErgodic`). `IsVUniformlyErgodic V P μ` is (16.2). The
  sublevel sets of `V` are petite (`isUnboundedOffPetite_of_tendsto`), and Theorem 16.1.4 is
  `theorem_16_1_4`, with `V₀ = Σ_{i<n} sⁱ PⁱV`. Equivalent weights give equivalent distances
  (`vErgDist_le_of_equiv`). Theorem 16.0.1 is `theorem_16_0_1`, a `List.TFAE` (Mathlib) with (i)
  corrected, and its counterexample is `theorem_16_0_1_counterexample`. `V`-uniformly ergodic
  chains are `V`-geometrically ergodic (`tsum_fNorm_le_of_tsum_vErgDist`).
* **Mixing** (`GeometricMixing`). The pair `(Φₖ, Φₖ₊ₙ)` has law `Pᵏ(x, ·) ⊗ Pⁿ`
  (`pathKernel_map_pair`, `integral_pair_eq`), and the geometric rate passes to `√V`
  (`exists_vErgDist_sqrt_le`, by Lemma 15.2.9). Theorem 16.1.5 is `theorem_16_1_5` and
  `theorem_16_1_5_mixing` (`IsVGeomMixing`), (16.17) is `eq_16_17`, and the stationary chain is
  strong mixing (`IsStrongMixing`, `isStrongMixing_of_vUniformlyErgodic`).
* **Regenerative models** (`RegenerativeModels`, `FwdRecurrenceSkeleton`). `Γ ∈ G⁺(γ)` (16.18) is
  `IsLaplaceFinite Γ γ`. A negative mean gives `∫ e^{s₀w} Γ(dw) < 1` (`exists_mgf_lt_one`), and
  the random walk on `[0, ∞)` is `e^{s₀x}`-uniformly ergodic (`halfLine_vUniformlyErgodic`, with
  (16.19) as `lintegral_halfLine_exp_le`). The forward recurrence time `δ`-skeleton, on `ℝ` with a
  restart from `(−∞, 0]` (`fwdChain`, carried), satisfies (V4) for `e^{γx⁺}` (`fwdChain_driftV4`)
  and is `e^{γx⁺}`-uniformly ergodic (`fwdChain_vUniformlyErgodic`). It is not uniformly ergodic
  (`fwdChain_not_uniformlyErgodic`), nor is any restriction carrying its stationary law unless
  `Γ` has bounded range (`fwdChain_unbounded_not_uniformlyErgodic`).
* **Uniform ergodicity** (`UniformErgodic`, `UniformModels`, `NSSUniformErgodic`).
  `IsUniformlyErgodic P μ` is (16.6), the case `V ≡ 1` (`isUniformlyErgodic_iff`). Theorems
  16.2.1–16.2.5 are `theorem_16_2_1`, `theorem_16_2_2` (with `theorem_16_2_2_hitting`),
  `theorem_16_2_3` (`IsDoeblin`), `theorem_16_2_4` and `theorem_16_2_5`, and Theorem 16.0.2 is
  `theorem_16_0_2`. The contraction `tvNorm_comp_le_of_le` replaces the coupling (16.23), and the
  integer part in (16.21) is forced by `theorem_16_2_4_counterexample`. An i.i.d. chain is
  uniformly ergodic (`isUniformlyErgodic_const`). The reset chain is uniformly ergodic with
  `π(f) < ∞` and no geometric rate in `‖·‖_f` (`reset_uniformlyErgodic`, `reset_not_fGeometric`).
  A T-chain restricted to a compact absorbing set is uniformly ergodic
  (`theorem_16_2_7_restrict`), and Lemma 16.2.6 and Theorem 16.2.7 are `lemma_16_2_6` and
  `theorem_16_2_7`, from Theorem 7.3.5 (ii).
* **Increment analysis** (`IncrementAnalysis`, `IncrementExamples`). The bounds
  `eᵗ ≤ 1 + t + t² e^{max(t, 0)}` (`exp_le_one_add_add_sq`) and (16.29) (`exp_mul_le_increment`)
  give (V4) for `e^{δV}` (`increment_driftV4`), and Theorem 16.3.1 is `theorem_16_3_1`; with
  increments of bounded range (16.50) it is `theorem_16_3_1_bounded_range`. The chain (16.30)
  (`upDownKernel`) satisfies (16.27) but not (16.26) and is not geometrically ergodic
  (`upDown_not_geomErgodic`); the chain (15.20) satisfies (16.26) but not (16.27)
  (`nonGeom_left_increments_unbounded`).
* **The structure of `π`** (`InvariantTails`). Jensen's inequality for hitting times
  (`ofReal_exp_meanHitTime_le`) and Theorem 15.3.3 give (16.32) (`theorem_16_3_2`) for every
  `B ∈ B⁺(X)`, and skip-free chains (16.31) (`pow_skipFree`) give (16.33)
  (`theorem_16_3_2_skipFree`).
* **Queueing models** (`QueueModels`, `PollingModels`, `PHQueue`). For the M/G/1 chain the
  generating function of the arrivals is `tsum_exp_mul_poissonWeight`, and Theorem 16.4.1 is
  `theorem_16_4_1`. The polling system is built visit by visit (`visitMeasure`, `pollTail`,
  `pollKernel`) from total service times (`sumLaw`) and Poisson arrivals (`arrLaw`); the drift and
  the exponential moments over a cycle are `pollTail_drift` and `pollTail_exp`, and
  Theorem 16.4.2 is `theorem_16_4_2`. The `h`-approximation of the M/PH/1 queue is `phKernel`,
  with corrected transitions; the linear `V(i) = w(m i₁ + i₂)` has `PV = V − 1` off `0`
  (`phKernel_drift`), and Theorem 16.4.3 is `theorem_16_4_3` and `theorem_16_4_3_finite`.
* **Autoregressive and state space models** (`ARModels`, `AdaptiveControl`,
  `AdaptiveControlKalman`). Quadratic forms (`quadForm`, `exists_quadForm_bounds`) give (16.42)
  (`rca_lintegral_quadForm`), and Theorem 16.5.1 is `theorem_16_5_1`. For the adaptive control
  model, (16.44) is `sacV` and the drift (16.45)–(16.47) is `sac_drift`; Proposition 16.5.2 is
  `proposition_16_5_2`, and for Gaussian disturbances `proposition_16_5_2_gaussian`, with the
  irreducibility hypotheses derived from Proposition 7.4.3. Every invariant probability of the
  Gaussian model is a Kalman law (`isKalmanLaw_of_isInvariant`), which gives the steady state
  identities (`sac_steady_state_identities`) and (16.49) (`eq_16_49_gaussian`, and `eq_16_49`
  from the identities).

The library covers the chapter as follows.

* **`V`-uniform ergodicity** (Chapter 16 introduction, pp. 392–395). (16.1)–(16.2),
  Theorem 16.0.1 with (16.3)–(16.5), its counterexample and correction, (16.6), Theorem 16.0.2
  with (16.7)–(16.10), and (16.11) corrected.
* **The operator norm `||| · |||_V`** (§16.1.1). Lemma 16.1.1, Theorem 16.1.2 and (16.12),
  Proposition 16.1.3, Theorem 16.1.4 with (16.13)–(16.15).
* **`V`-geometric mixing** (§16.1.2). Strong mixing, `V`-geometric mixing, Theorem 16.1.5 and
  (16.17).
* **Regenerative models** (§16.1.3). (16.18), the forward recurrence time `δ`-skeleton, and the
  random walk on `[0, ∞)` with (16.19).
* **Equivalent conditions for uniform ergodicity** (§16.2.1). Theorems 16.2.1–16.2.3, Doeblin's
  condition, Theorem 16.2.4 with (16.20)–(16.23), its counterexample and correction.
* **Geometric convergence of given moments** (§16.2.2). The claim of the example (16.24), for the
  reset chain.
* **T-chains on compact spaces** (§16.2.3). Theorem 16.2.5, Lagrange stability, Lemma 16.2.6 and
  Theorem 16.2.7.
* **Increment analysis** (§16.3.1). (16.25)–(16.29), Theorem 16.3.1 with the corrected set, the
  chains (16.30) and (15.20).
* **Geometric ergodicity and the structure of `π`** (§16.3.2). (16.31), Theorem 16.3.2 with
  (16.32)–(16.34).
* **Models from queueing theory** (§16.4). Theorem 16.4.1, the polling system and Theorem 16.4.2
  with (16.35), the M/PH/1 queue with the corrected transitions, (16.36)–(16.37) in drift form, and
  Theorem 16.4.3.
* **Autoregressive and state space models** (§16.5). (16.38), (16.42)–(16.43), Theorem 16.5.1;
  (16.44)–(16.49) and Proposition 16.5.2.
* **Commentary** (§16.6). The bounded-range condition (16.50).

All names are in the namespace `MeynTweedie.VUniformErgodicity`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

### The Chapter 16 modules (265 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [OperatorNorm](VUniformErgodicity/OperatorNorm.lean) | 24 | Chapter 16 introduction and §16.1.1: the weighted norm `|f|_V` and `L∞_V`, the `V`-norm distance (16.1), `|||Pⁿ − 1 ⊗ μ|||_V`, Lemma 16.1.1, truncation and (16.15), the submultiplicativity, Proposition 16.1.3 and its geometric bound, Theorem 16.1.2 and (16.12) |
| [VUniformErgodic](VUniformErgodicity/VUniformErgodic.lean) | 15 | `V`-uniform ergodicity (16.2), the petiteness of the sublevel sets of `V`, Theorem 16.1.4 with (16.13)–(16.14), equivalent weights, Theorem 16.0.1 corrected and its counterexample, `V`-geometric ergodicity from (16.12) |
| [GeometricMixing](VUniformErgodicity/GeometricMixing.lean) | 10 | §16.1.2: the two-dimensional distributions, the rate for `√V`, Theorem 16.1.5, `V`-geometric mixing, (16.17), strong mixing of the stationary chain |
| [RegenerativeModels](VUniformErgodicity/RegenerativeModels.lean) | 5 | §16.1.3: `G⁺(γ)` (16.18), the moment generating function below `1`, (16.19), (V4) and `e^{s₀x}`-uniform ergodicity of the random walk on `[0, ∞)` |
| [FwdRecurrenceSkeleton](VUniformErgodicity/FwdRecurrenceSkeleton.lean) | 17 | §16.1.3: the exponential overshoot, (V4) for `e^{γx⁺}`, the petite set `(−∞, δ]`, `e^{γx⁺}`-uniform ergodicity of the forward recurrence time `δ`-skeleton, deterministic descent, the failure of uniform ergodicity and the need for bounded range |
| [UniformErgodic](VUniformErgodicity/UniformErgodic.lean) | 26 | §16.2.1 and Theorem 16.0.2: uniform ergodicity (16.6), Theorem 16.2.1, irreducibility and aperiodicity of uniformly ergodic chains, Theorem 16.2.2 and its hitting-time parts, Doeblin's condition and Theorem 16.2.3, the contraction behind (16.23), Theorem 16.2.4 corrected and its counterexample, Theorem 16.0.2, i.i.d. chains, Theorem 16.2.5 |
| [UniformModels](VUniformErgodicity/UniformModels.lean) | 15 | §§16.2.2–16.2.3: the reset chain in place of (16.24), uniformly ergodic with no geometric rate in `‖·‖_f`; compact sets of T-chains are small, Lemma 16.2.6 and Theorem 16.2.7 for a T-chain and a compact absorbing set |
| [NSSUniformErgodic](VUniformErgodicity/NSSUniformErgodic.lean) | 6 | §16.2.3: restricted chains on the ambient space, uniqueness of the invariant probability of a positive chain, `A₊(x)` closed and absorbing, Lemma 16.2.6, Theorem 16.2.7 |
| [IncrementAnalysis](VUniformErgodicity/IncrementAnalysis.lean) | 13 | §16.3.1: the bounds replacing (16.28), (16.29), (V4) for `e^{δV}` with the corrected set, Theorem 16.3.1, increments of bounded range (16.50), the minimal solution `V₀` for the chain (15.20) and the need for (16.27) |
| [IncrementExamples](VUniformErgodicity/IncrementExamples.lean) | 16 | §16.3.1: the chain (16.30), (16.27) and the failure of (16.26), skip-freeness to the left, `E_0[r^{τ_0}] = ∞`, irreducibility, the failure of geometric ergodicity, the drift of `V(x) = x` and (V2) |
| [InvariantTails](VUniformErgodicity/InvariantTails.lean) | 7 | §16.3.2: Jensen's inequality for hitting times, geometric moments of hitting times under (V4), Theorem 16.3.2 with (16.32), skip-free chains (16.31), (16.33) |
| [QueueModels](VUniformErgodicity/QueueModels.lean) | 4 | §16.4.1: the generating function of the M/G/1 arrivals, the one-step integrals, Theorem 16.4.1 |
| [PollingModels](VUniformErgodicity/PollingModels.lean) | 36 | §16.4.2: Poisson laws, total service times, arrivals during a time, one visit and its moments, the polling chain, the drift and the exponential moments over a cycle, the empty state, Theorem 16.4.2 |
| [PHQueue](VUniformErgodicity/PHQueue.lean) | 29 | §16.4.3: the state space and the corrected `h`-approximation of the M/PH/1 queue, one-step integrals, the linear drift (16.36)–(16.37), the increment bounds (16.26)–(16.27), irreducibility, Theorem 16.4.3, finitely many phases |
| [ARModels](VUniformErgodicity/ARModels.lean) | 12 | §16.5.1: quadratic forms and their two-sided bounds, (16.42), Theorem 16.5.1 |
| [AdaptiveControl](VUniformErgodicity/AdaptiveControl.lean) | 14 | §16.5.2: the function (16.44), Young's inequalities, the estimation error update, the drift (16.45)–(16.47), the absorbing set and compact sublevel sets, Proposition 16.5.2 and (16.48), (16.49) and the performance bounds |
| [AdaptiveControlKalman](VUniformErgodicity/AdaptiveControlKalman.lean) | 16 | §16.5.2 for Gaussian disturbances: the restricted chain, Proposition 16.5.2 with its hypotheses derived, total variation from an initial law, Kalman laws as limits, the steady state is a Kalman law, (16.45), the steady state identities, (16.49) |

### Carried modules (3224 theorems)

Carried from the Chapter 15 project `GeometricErgodicity` (2898 theorems): 130 of its 131 modules,
all but `GeometricConverseGeneral`. They are its 8 Chapter 15 modules (257 theorems)
`GeometricSums` (56), `KendallSets` (41), `GeometricDrift` (30), `GeometricAtoms` (28),
`GeometricSkeletons` (18), `GeometricErgodicTheorem` (30), `GeometricConverse` (7) and
`GeometricModels` (47), and the 122 modules (2641 theorems) that `GeometricErgodicity` carries from
the Chapter 14 project `FErgodicity`, which cover Chapters 1–11, 13 and 14 and the renewal theory
(see that project's README for the list and for how those copies differ from the originals). The
carried modules are identical to the copies there except for the namespace and the imports, and
except that `GeometricConverse` and `GeometricErgodicTheorem` keep the module docstrings they had
before `GeometricConverseGeneral` was written. So Theorem 15.4.2 without an atom
(`theorem_15_4_2`, `theorem_15_4_2_univ`) is not part of this library; its atom case
(`theorem_15_4_2_atom`) is. Theorem 15.4.1 in the form (15.4) (`geometric_ergodic_of_driftV4`),
(V4) and its consequences (`DriftV4`, `IsUnboundedOffPetite`, `lemma_15_2_8`, `lemma_15_2_9`,
`theorem_15_2_6`, `theorem_15_3_3`), Kendall sets and geometric sums (`IsKendall`,
`kendallMoment`, `geomTaboo`, `tpow`), Theorem 15.1.5 (`theorem_15_1_5`, `IsGeomErgodicAtom`) and
the chain (15.20) (`nonGeomKernel`, `nonGeom_meanReturnTime_pos`) are used. From the deeper
projects, the `f`-norm and the total variation norm (`fNorm`, `tvNorm`, `proposition_13_3_2`),
invariant measures and positivity (`IsInvariant`, `IsPositive`, `proposition_10_1_1`), hitting
times (`meanReturnTime`, `meanHitTime`, `regV`), small and petite sets (`IsSmallSet`, `IsSmall`,
`IsPetite`, `proposition_5_2_4_i`, `proposition_5_5_4_i`, `theorem_5_5_7`, `theorem_5_2_2`),
aperiodicity (`IsAperiodic`, `isAperiodic_of_minorization`), T-chains (`IsTChain`,
`theorem_6_2_5_ii`), restricted chains (`restrictKernel`), path measures (`pathKernel`,
`pathMeasure`), the models (`halfLineWalkKernel`, `halfLine_isPetite_Iic`, `mG1Matrix`,
`poissonWeight`, `mG1_poisson_isIrreducibleChain`, `matKernel`, `rcaKernel`, `sacKernel`,
`sacGaussianKernel`, `nssKernel`) and the forward recurrence time skeleton (`fwdSkelKernel`,
`fwdSkelInv`, `proposition_5_3_3`) are used. No Chapter 16 module depends, directly or through
other modules, on `ContinuousRenewal`, `CountableErgodic`, `CouplingRenewal`, `ErgodicTheorem`,
`FPeriodicErgodic`, `GIG1Embedding`, `GIG1Invariant`, `GIG1SmallSets`, `KeyRenewal`,
`LinearInvariant`, `RandomWalkIntegers`, `RandomWalkMeanZero`, `SkipFreeWalk`, `SplitPetite`,
`StateSpaces` or `TopologicalExamples`.

Carried from the Chapter 12 project `InvarianceTightness` (299 theorems): 13 of its modules. They
are three of its Chapter 12 modules (82 theorems), `BoundedInProbability` (49),
`BoundednessCriteria` (19) and `AdaptiveControlStability` (14), and the ten Chapter 7 modules it
carries from the Chapter 7 project `NonlinearStateSpace` (217 theorems): `ControlModel` (33),
`ForwardAccessibility` (18), `LocalInverse` (8), `NSSTChain` (12), `MinimalSets` (29),
`PeriodicOrbits` (37), `NSSIrreducibility` (8), `NSSPeriodicity` (10), `NSSExamples` (44) and
`NSSAdaptiveControl` (18). They are identical to the copies in `InvarianceTightness` except for the
namespace and the imports; in particular they keep that project's renaming of the invariant sets
of the control model to `IsCMInvariant` (see its README). Its other Chapter 12 modules,
`LiminfCounterexample`, `GeneralizedSampling`, `SigmaFiniteInvariant`, `EChainInvariant`,
`EChainCriteria` and `TightnessCriteria`, are not carried. Theorem 7.3.5 (ii)
(`theorem_7_3_5_ii`), Proposition 7.2.2 (i) (`proposition_7_2_2_i`,
`isCMInvariant_closure_reach`), the control model and the NSS(F) hypotheses (`reach`,
`controlSet`, `IsLSCDensity`, `RankCondition`, `IsMIrreducible`, `IsMinimal`, `IsPeriodOf`),
Proposition 7.4.3 and the state space of the adaptive control model (`proposition_7_4_3`,
`sacSpace`, `isClosed_sacSpace`, `isAbsorbing_sacSpace`), and the Kalman laws of §12.5.3
(`IsKalmanLaw`, `sacKalmanInit`, `sacKalmanInit_spec`, `isKalmanLaw_sacGaussian_pow`,
`sacGaussian_noise_moments`, `integral_sq_gaussianReal`) are used.

Carried from the Chapter 14 project `FErgodicity` (27 theorems): three of the §14.5 follow-up
modules that `GeometricErgodicity` does not carry, `RenewalMeasure` (10), `RenewalRegeneration` (2)
and `RenewalChain` (15), identical to the copies there except for the namespace and the imports.
The renewal measure (`renMeas`, `renMeas_dirac_apply`, `renMeas_dirac_Iic_le`, `incr`,
`incr_map_partialSum`, `exp_moment_lt_one`) and the restarted forward recurrence time chain
(`fwdChain`, `isMarkovKernel_fwdChain`, `fwdChain_pow_of_pos`, `fwdChain_structure`) are used. Its
other follow-up modules, `RenewalKey`, `RenewalEquilibrium`, `RenewalUniform`, `RenewalAbsCont`,
`BlackwellHarmonic`, `BlackwellRenewal`, `FNormMeasurable`, `FHalfLineIntegrated`, `FLazyChain`,
`FPeriodicCycle` and `FPeriodicAll`, are not carried.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (4096 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
