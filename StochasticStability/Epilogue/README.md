# Meyn and Tweedie, Chapter 20: Epilogue to the Second Edition, in Lean

This is the `StochasticStability/Epilogue` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 20 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 510–528. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 20 was written for the second edition. It surveys three directions of work since the
first edition, and most of it reports results from the literature with short proofs or none.
§20.1 reads geometric ergodicity as spectral theory on the weighted space `L∞_V`. It defines the
spectrum `S_V(P)` through the resolvent `T_z = [Iz − P]⁻¹` and the kernel
`Z_z = [Iz − P + 1 ⊗ π]⁻¹` (20.2), poles of finite multiplicity, a spectral gap and a discrete
spectrum (p. 512). Theorem 20.1.1 shows that `V`-uniform ergodicity gives a spectral gap, with
`Z_z` bounded for `|z| > ε₀`, `ε₀ < 1`, and conversely that such a bound gives `V`-uniform
ergodicity at the rate (20.3) set by the spectral radius `λ*` of `P − 1 ⊗ π`. After reversibility
(20.5), the Diaconis–Stroock bound (20.6) and geometric ergodicity in `Lᵖ(π)` (20.7),
Proposition 20.1.2 compares these notions: a reversible `V`-uniformly ergodic chain need not be
geometrically ergodic in `L¹(π)` (i), a `V`-uniformly ergodic chain need not be geometrically
ergodic in `L²(π)` (ii), and a reversible chain is geometrically ergodic in `L²(π)` iff it is
`V`-uniformly ergodic for some `V` (iii). Proposition 20.1.3 computes eigenvalues of the M/M/1
queue (20.8)–(20.9): it has a spectral gap but not a discrete spectrum. §20.1.4 introduces the
nonlinear generator (20.10) and the Donsker–Varadhan condition (DV3) (20.11); under (DV3) the
truncated kernels converge to `P` (Proposition 20.1.4), and on a countable space `P` has a
discrete spectrum (Proposition 20.1.5). §§20.1.5–20.1.6 survey multiplicative ergodic theory, the
Feynman–Kac semigroup (20.12)–(20.14), large deviations (20.15) and quasi-stationarity through
the killed semigroup (20.16). §20.2 turns to simulation: control variates (20.17)–(20.20), with
zero variance when the control variate solves Poisson's equation, Figure 20.1, the
Metropolis–Hastings algorithm (20.21) and what is known about its ergodicity, and machine
learning. §20.3 sketches continuous time: Doeblin's equations (20.22)–(20.23), Markov
semigroups, the resolvent (20.24) and the sampled chains, ergodicity from a skeleton
((20.25) ⇒ (20.26)), the generator and the extended generator (20.27)–(20.28), the resolvent
equations (Theorem 20.3.1, (20.29)–(20.30)), the Exponential Ergodic Theorem (Theorem 20.3.2,
(20.31)–(20.34)) and the continuous-time Feynman–Kac semigroup (20.35)–(20.36).

The results that the chapter proves, or that follow from the book's own methods, are formalised:
Theorem 20.1.1 (i)–(ii); Proposition 20.1.2 (i) and (ii); Propositions 20.1.3, 20.1.4 and
20.1.5; Theorem 20.3.1; and Theorem 20.3.2 at the level of kernels and skeletons. So are the
claims of the text around them: the algebra of `P`, `1 ⊗ π` and `Z_z` and the Riesz projection
at `1` (p. 513), the exact rate for an eigenfunction (p. 512), Poisson's equation through the
fundamental kernel (p. 511), reversibility and invariance (20.5), the (V4) bound from (DV3)
(p. 517), the Feynman–Kac representation (20.13), the killed semigroup (20.16), the twisted
kernel and the multiplicative Poisson equation (p. 519), the control-variate identities and the
zero-variance estimator of §20.2.1, the variance bound in the proof of Proposition 20.1.2,
detailed balance for the Metropolis–Hastings chain and the uniform ergodicity of the independence
sampler (pp. 522–523), the resolvent kernel of the sampled chain (p. 525) and (20.25) ⇒ (20.26).
Proposition 20.1.5 rests on Theorem 3.5 of [219], that a norm limit of finite-rank operators has
a discrete spectrum. This is the Riesz–Schauder theory of compact operators: Mathlib has compact
operators and the Fredholm alternative, and the rest (finitely many spectral points outside each
disc, idempotent compact Riesz projections of finite rank, so poles of finite multiplicity) is
proved here. Proposition 20.1.2 (ii) is proved with a different, simpler chain than Häggström's
example [150] cited by the book: the branch chain (`branchKernel`), which is `V`-uniformly
ergodic, while the indicator of branch `2n` keeps an `L²(π)` distance of order `‖g‖₂` from its
mean after `n` steps.

The results the Epilogue quotes from the literature are not formalised, for the following
reasons. Proposition 20.1.2 (iii), from Roberts and Rosenthal [329], needs the spectral theorem
for self-adjoint operators on `L²(π)`. The Diaconis–Stroock bound (20.6) [90] and the bounds of
[119] for finite chains rest on the spectral decomposition of reversible and symmetrised
matrices. The multiplicative ergodic theorems (20.14), the large deviation limit (20.15), the
existence of quasi-stationary laws and the ratio limit theorem of §20.1.6 need Perron–Frobenius
theory for positive operators on `L∞_V` and the twisted-kernel arguments of
[17, 118, 218, 219]. The converse in claim (i) of p. 523 and claim (ii) on the random-walk
Metropolis–Hastings algorithm are quoted from [256, 179]. In §20.3, Mathlib has no construction
of a continuous-time Markov process from a semigroup, no càdlàg path spaces, and no
continuous-time hitting times or strong Markov property. So non-explosion, the generator (20.27),
the local-martingale definition (20.28) of the extended generator, the definitions of
irreducibility and petiteness for the process, the equivalence of (i)–(iii) in Theorem 20.3.2,
which the book takes from Down, Meyn and Tweedie [101], and the absorbing set `S_V` are not
formalised. A Markov semigroup is given by its kernels, the extended generator is taken in its
semigroup (Dynkin) form, and Theorem 20.3.2 is proved for a skeleton. Doeblin's equations
(20.22)–(20.23), the generalized resolvent (20.35)–(20.36), Figure 20.1, §20.2.3 and the
historical remarks are not formalised either.

Six claims are false as printed. Each is refuted in Lean by a counterexample of this project, and
a corrected statement is proved. In (20.9) the coefficients of the two geometric series are
interchanged, and so is the constant `c` of the proof (`mm1EigfnBook_counterexample`). The
limiting eigenfunction of Proposition 20.1.3 (iii) is wrong (`mm1EigLimBook_counterexample`). The
constant `b'` of the (V4) bound derived from (DV3) on p. 517 must be `e^b sup_C e^V`, not
`b + sup_C e^V` (`driftV4_of_driftDV3_book_counterexample`). With (20.7) as printed, with `p`-th
powers, the variance bound of p. 515 fails (`asymptoticVariance_book_counterexample`); it holds
for the norm form. The multiplicative Poisson equation of p. 519 has the wrong right-hand side
(`nonlinGen_book_counterexample`). (20.16) is false with `τ_M` the return time to `M`; it holds
with the exit time (`killedKernel_returnTime_counterexample`). One step of a proof is also
repaired: the proof of Proposition 20.1.2 (i) takes every `λ` in an interval up to `1` as an
eigenvalue in a fixed `L∞_V`, which the book's own remark on p. 517 contradicts, and the argument
is run in `L¹(π)` instead. Further points are made explicit. `L∞_V` is complex; Theorem 20.1.1
(i) starts from the geometric bound (20.4), the corrected form of `V`-uniform ergodicity of the
Chapter 16 project, and (ii) assumes that `P` and `1 ⊗ π` act on `L∞_V`; the limit in (20.3) is
a `lim sup`; Propositions 20.1.4–20.1.5 take `V` real-valued; geometric ergodicity in `Lᵖ(π)` is
stated in norm form; and the continuous-time results assume what they need of the skeleton. See
[corrections](docs/corrections.md). The library contains **3711 theorems**. Of these, 222 are in
the 13 Chapter 20 modules. The other 3489 are in the 163 modules carried from the Chapter 16
project `VUniformErgodicity`: all of its modules, that is its 17 Chapter 16 modules and the 146
modules it carries from earlier projects.

Several routes differ from the book. Theorem 20.1.1 (ii) is proved through Gelfand's spectral
radius formula (Mathlib) where the book integrates `Z_z` over a circle, and the "finite
multiplicity" of (i) is proved by computing the Riesz projection at `1`, which is `1 ⊗ π`, of
rank one. Proposition 20.1.5 is proved by showing that `P` is a compact operator on `L∞_v`, a norm
limit of the finite-rank truncations. Theorem 20.3.2 is proved from (V4) for a skeleton through
Theorem 16.1.2 and a bound `PˢV ≤ cV` on `[0, δ]`, and the generator drift (20.31) is carried to
the sampled chain in integrated form (`resolventKernel_drift`).

The chapter rests on seven groups of results.

* **Kernels as operators on `L∞_V`** (`WeightedSpace`). `L∞_V` is the Banach space `BM X` of
  bounded measurable complex functions in the weighted coordinates `g = f/V` (`completeSpace_BM`).
  A kernel `κ` with `κV ≤ cV` (`WeightOK V κ`) acts as `kOp V κ`, compositions and powers of
  kernels act as products of operators (`kOp_comp`, `kOp_pow`), and `1 ⊗ π` acts as a projection
  `Π` with `PΠ = ΠP = Π² = Π` (`kOp_mul_kOp_const`, `kOp_const_mul_kOp`, `kOp_const_mul_self`).
  The operator norm and the distance `|||·|||_V` of Chapter 16 agree up to a factor `2`
  (`vErgDist_le_norm`, `norm_le_vErgDist`).
* **The spectrum and Theorem 20.1.1** (`SpectralGap`). `S_V(P)` is `spectrumV V P`, `Z_z` is
  `fundKernel V P π z`, and `rieszProj`, `IsFinitePole`, `HasSpectralGap` and
  `HasDiscreteSpectrum` are the definitions of p. 512. Theorem 20.1.1 is `theorem_20_1_1_i` and
  `theorem_20_1_1_ii` (with `spectral_rate_op`), the formula for `T_z` is
  `resolvent_eq_fundKernel`, the Riesz projection at `1` is `rieszProj_one_eq`, Poisson's
  equation is `fundKernel_poisson`, and the eigenfunction rate is `eigen_rate`.
* **The M/M/1 queue and Proposition 20.1.2 (i)** (`MM1Spectrum`). The queue is the Bernoulli walk
  `bernoulliWalk p` (carried), `IsReversible` is (20.5), and `mm1_isReversible` gives the invariant
  law `mm1Pi`. Proposition 20.1.3 is `proposition_20_1_3_i`, `proposition_20_1_3_ii` (with the
  corrected (20.9), `mm1Op_eigfn`) and `proposition_20_1_3_iii` (with `mm1Op_eigLim`), and
  `mm1_spectralGap_not_discrete` gives the spectral gap without a discrete spectrum. Geometric
  ergodicity in `Lᵖ(π)` is `IsLpGeomErgodic`, and Proposition 20.1.2 (i) is
  `proposition_20_1_2_i`.
* **A chain that is not `L²`-geometrically ergodic** (`BranchChain`). Proposition 20.1.2 (ii) is
  `proposition_20_1_2_ii`, for the branch chain `branchKernel` with invariant law `branchPi`,
  `V`-uniformly ergodic by (V4) (`branch_driftV4`, `branch_vUniform`).
* **(DV3) and a discrete spectrum** (`DiscreteSpectrum`, `CompactSpectrum`). The nonlinear
  generator is `nonlinGen` and (DV3) is `DriftDV3`; `driftV4_of_driftDV3` is the corrected
  (V4) bound. Proposition 20.1.4 is `proposition_20_1_4`, for the truncations `truncKernel`. The
  Riesz–Schauder theory gives `hasDiscreteSpectrum_of_compact` (through `finite_spectrum_compact`
  and `isFinitePole_of_compact`), and Proposition 20.1.5 is `proposition_20_1_5`, through
  `proposition_20_1_5_compact`.
* **Feynman–Kac, simulation and MCMC** (`MultiplicativeErgodic`, `VarianceReduction`, `MCMC`).
  (20.13) is `feynmanKac_apply` for `fkKernel`, (20.16) is `killedKernel_apply`, the twisted
  kernel is `twistedKernel` (`isMarkovKernel_twistedKernel`), and the multiplicative Poisson
  equation is `nonlinGen_log_eigen`. The control variate has steady-state mean zero
  (`integral_controlVariate_eq_zero`), the estimator (20.19) built from Poisson's equation is exact
  (`cvEstimator_poisson`), and a solution exists for a `V`-uniformly ergodic chain
  (`exists_poisson_of_vUniform`). The variance bound of p. 515 is `asymptoticVariance_le`. The
  Metropolis–Hastings kernel is `mhKernel`, reversible by `mhKernel_isReversible`, and the
  independence sampler is uniformly ergodic when `π ≤ Mp` (`indepSampler_uniformlyErgodic`).
* **Continuous time** (`ContinuousTimeResolvent`, `ExponentialErgodic`,
  `ExponentialErgodicKernel`, `ResolventDrift`). A Markov semigroup is `MarkovSemigroup X`, the
  resolvent (20.24) is `MarkovSemigroup.resolvent` and the sampled chain is
  `MarkovSemigroup.resolventKernel`. Theorem 20.3.1 is `MarkovSemigroup.theorem_20_3_1_i` and
  `MarkovSemigroup.theorem_20_3_1_ii` (`MarkovSemigroup.IsExtGenerator`), and (20.25) ⇒ (20.26) is
  `MarkovSemigroup.tendsto_tvNorm_of_skeleton`. Theorem 20.3.2 is `theorem_20_3_2_skeleton`,
  `theorem_20_3_2_skeleton_tfae` and `theorem_20_3_2_kernel`, through `vUniform_of_skeleton`.

The library covers the chapter as follows.

* **Introduction** (pp. 510, 523–524). Not formalised (informal and historical).
* **The spectrum of `P`** (§20.1.1). The space `L∞_V`, (20.2) and its power series, the
  fundamental kernel and Poisson's equation, and the definitions of the spectrum, poles of finite
  multiplicity, spectral gaps and discrete spectra. The finite-rank form (20.1) enters only
  through finite-rank operators.
* **Rates of convergence and eigenvalues** (§20.1.2). Eigenfunctions and the exact rate,
  Theorem 20.1.1 with (20.3)–(20.4), reversibility (20.5), (20.7) in norm form, Proposition
  20.1.2 (i)–(ii) and the variance bound of its proof.
* **The spectrum of the M/M/1 queue** (§20.1.3). (20.8), the invariant law, reversibility,
  Proposition 20.1.3 with the corrected (20.9) and limiting eigenfunction, and the failure of a
  discrete spectrum.
* **Drift criterion for a discrete spectrum** (§20.1.4). (20.10)–(20.11), the corrected (V4)
  bound, Propositions 20.1.4 and 20.1.5.
* **Multiplicative ergodic theory** (§20.1.5). The positive kernel `P_f`, (20.12)–(20.13), the
  twisted kernel and the corrected multiplicative Poisson equation.
* **Quasi-stationarity** (§20.1.6). The corrected (20.16).
* **Variance reduction** (§20.2.1). (20.19)–(20.20), the steady-state mean of the control variate,
  the zero-variance estimator and the existence of the solution of Poisson's equation.
* **MCMC** (§20.2.2). (20.21), the Metropolis–Hastings kernel and detailed balance, and the
  "if" half of claim (i) of p. 523.
* **Continuous time** (§§20.3.1–20.3.3). Markov semigroups, (20.24) and the sampled chain,
  (20.25) ⇒ (20.26), Theorem 20.3.1 with (20.29)–(20.30) and the extended generator in semigroup
  form, and Theorem 20.3.2 for skeletons with (20.34).

All names are in the namespace `MeynTweedie.Epilogue`. See the [source map](docs/source-map.md)
and the [corrections](docs/corrections.md).

## Library map

### The Chapter 20 modules (222 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [WeightedSpace](Epilogue/WeightedSpace.lean) | 35 | §20.1.1: the Banach space `BM X` of bounded measurable complex functions, `L∞_V` in weighted coordinates, admissible weights, kernels as operators, composition, identity and powers, the projection `1 ⊗ π`, the operator norm against `|||·|||_V` |
| [SpectralGap](Epilogue/SpectralGap.lean) | 33 | §§20.1.1–20.1.2: the algebra of `P`, `Π` and `P − Π`, power series for the resolvent, eigenvalues in the spectrum, Riesz projections, poles, spectral gaps and discrete spectra, `S_V(P)` and `Z_z` (20.2), the Riesz projection at `1`, Theorem 20.1.1 (i)–(ii) with (20.3), Poisson's equation, eigenfunctions and the exact rate |
| [MM1Spectrum](Epilogue/MM1Spectrum.lean) | 38 | §20.1.3: the operator (20.8), the corrected (20.9) and its counterexample, the corrected limiting eigenfunction and its counterexample, reversibility (20.5), the invariant law, Proposition 20.1.3 (i)–(iii), a spectral gap without a discrete spectrum, (20.7) in norm form, Proposition 20.1.2 (i) |
| [DiscreteSpectrum](Epilogue/DiscreteSpectrum.lean) | 7 | §20.1.4: the nonlinear generator (20.10), (DV3) (20.11), the corrected (V4) bound and its counterexample, the truncated kernels, Proposition 20.1.4, finite-rank truncations and compactness of `P` |
| [CompactSpectrum](Epilogue/CompactSpectrum.lean) | 16 | §20.1.4: Riesz–Schauder theory (finitely many eigenvalues and spectral points outside each disc, the resolvent identity, Riesz projections of compact operators, compact idempotents of finite rank, poles of finite multiplicity, a discrete spectrum), Proposition 20.1.5 |
| [BranchChain](Epilogue/BranchChain.lean) | 30 | §20.1.2: the branch chain, its invariant law, irreducibility, (V4) and `V`-uniform ergodicity, the deterministic descent along a branch, Proposition 20.1.2 (ii) |
| [VarianceReduction](Epilogue/VarianceReduction.lean) | 7 | §20.2.1 and p. 515: the control variate (20.20) and its steady-state mean, the estimator (20.19) with zero variance, Poisson's equation for `V`-uniformly ergodic chains, the variance bound and its counterexample for (20.7) as printed |
| [MCMC](Epilogue/MCMC.lean) | 9 | §20.2.2: the acceptance probability (20.21), the Metropolis–Hastings kernel and detailed balance, the minorization and uniform ergodicity of the independence sampler |
| [MultiplicativeErgodic](Epilogue/MultiplicativeErgodic.lean) | 9 | §§20.1.5–20.1.6: the kernel `P_f`, the Feynman–Kac representation (20.13), the killed semigroup (20.16) and its counterexample, the twisted kernel, the corrected multiplicative Poisson equation and its counterexample |
| [ContinuousTimeResolvent](Epilogue/ContinuousTimeResolvent.lean) | 24 | §§20.3.1–20.3.2: Laplace transforms on `(0, ∞)`, Markov semigroups, the resolvent (20.24), the sampled chain, Theorem 20.3.1 with (20.29)–(20.30) and the extended generator in semigroup form |
| [ExponentialErgodic](Epilogue/ExponentialErgodic.lean) | 8 | §§20.3.1, 20.3.3: monotonicity of `‖Pᵗ(x, ·) − π‖`, (20.25) ⇒ (20.26), skeletons, (20.34) from a `V`-uniformly ergodic skeleton, Theorem 20.3.2 from (V4) for a skeleton |
| [ExponentialErgodicKernel](Epilogue/ExponentialErgodicKernel.lean) | 2 | §20.3.3: the skeleton analogues of (20.31)–(20.33) are equivalent, and (20.34) holds iff a skeleton satisfies (V4) |
| [ResolventDrift](Epilogue/ResolventDrift.lean) | 4 | §20.3.3: the Laplace–Tonelli identity, the sampled chain on nonnegative functions, the generator drift (20.31) carried to the sampled chain |

### Carried modules (3489 theorems)

Carried from the Chapter 16 project `VUniformErgodicity` (3489 theorems): all 163 of its modules.
They are its 17 Chapter 16 modules (265 theorems) `OperatorNorm` (24), `VUniformErgodic` (15),
`GeometricMixing` (10), `RegenerativeModels` (5), `FwdRecurrenceSkeleton` (17), `UniformErgodic`
(26), `UniformModels` (15), `NSSUniformErgodic` (6), `IncrementAnalysis` (13),
`IncrementExamples` (16), `InvariantTails` (7), `QueueModels` (4), `PollingModels` (36), `PHQueue`
(29), `ARModels` (12), `AdaptiveControl` (14) and `AdaptiveControlKalman` (16), and the 146
modules (3224 theorems) that `VUniformErgodicity` carries from the Chapter 15 project
`GeometricErgodicity`, the Chapter 12 project `InvarianceTightness` and the Chapter 14 project
`FErgodicity`, which cover Chapters 1–15 and the renewal theory (see that project's README for the
list and for how those copies differ from the originals). The carried modules are identical to
the copies in `VUniformErgodicity` except for the namespace and the imports. The corrections they
contain belong to Chapters 1–16 and are recorded in those projects.

From these modules the Chapter 20 modules use, among others, the `V`-norm distances and
`V`-uniform ergodicity (`vOpNorm`, `vErgDist`, `IsVUniformlyErgodic`, `vErgDist_le_of_driftV4`,
`theorem_16_0_1`), Theorem 16.2.4 (`theorem_16_2_4`) and the contraction `tvNorm_comp_le_of_le`,
Theorem 15.0.1 and its conditions (`theorem_15_0_1`, `IsLocallyGeomErgodic`, `HasKendallPetite`,
`HasDriftV4`), (V4) (`DriftV4`), the `f`-norm and the total variation norm (`fNorm`, `tvNorm`),
invariance (`IsInvariant`), irreducibility, aperiodicity and small and petite sets
(`IsMaximalIrreducibility`, `IsPhiIrreducible`, `IsAperiodic`, `isAperiodic_of_minorization`,
`IsSmallSet`, `IsPetite`, `proposition_5_5_3`), path measures (`pathKernel`, `pathMeasure`), and
the Bernoulli walk on `ℤ₊` (`bernoulliWalk`, `bernoulliWalk_driftV4`,
`bernoulliWalk_isIrreducibleChain`). Of the Chapter 16 modules only `OperatorNorm`,
`VUniformErgodic` and `UniformErgodic` are dependencies of the Chapter 20 modules. No Chapter 20
module depends, directly or through other modules, on `AdaptiveControl`, `AdaptiveControlKalman`,
`AdaptiveControlStability`, `ARModels`, `BoundedInProbability`, `BoundednessCriteria`,
`CompactPetite`, `ContinuousRenewal`, `ControlModel`, `CountableErgodic`,
`CountableIrreducibility`, `CouplingRenewal`, `EChains`, `EChainsStability`, `ErgodicTheorem`,
`ForwardAccessibility`, `FPeriodicErgodic`, `FwdRecurrenceSkeleton`, `GeometricMixing`,
`GIG1Embedding`, `GIG1Invariant`, `GIG1SmallSets`, `IncrementAnalysis`, `IncrementExamples`,
`InvariantTails`, `KeyRenewal`, `LinearInvariant`, `LinearTChains`, `LocalInverse`,
`MinimalSets`, `ModelKernels`, `ModelQueues`, `ModelRenewal`, `ModelStorage`,
`NSSAdaptiveControl`, `NSSExamples`, `NSSIrreducibility`, `NSSPeriodicity`, `NSSTChain`,
`NSSUniformErgodic`, `PeriodicOrbits`, `PHQueue`, `PoissonCounts`, `PollingModels`,
`QueueModels`, `RandomWalkIntegers`, `RandomWalkMeanZero`, `Regeneration`, `RegenerativeModels`,
`RenewalChain`, `RenewalInvariant`, `RenewalMeasure`, `RenewalRegeneration`, `RenewalSkeletons`,
`RenewalSmallSets`, `SkipFreeWalk`, `SpecificKernels`, `SpecificMatrices`, `SplitPetite`,
`StateSpaces`, `TopologicalExamples` or `UniformModels`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (4381 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
