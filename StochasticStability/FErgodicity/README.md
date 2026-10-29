# Meyn and Tweedie, Chapter 14: f-Ergodicity and f-Regularity, in Lean

This is the `StochasticStability/FErgodicity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 14 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 336–361. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 14 replaces the bounded functions of Chapter 13 by a fixed function `f ≥ 1`. The
`f`-norm of a signed measure is `‖μ − ν‖_f = sup_{|g| ≤ f} |μ(g) − ν(g)|` (p. 336), and for
`f ≡ 1` it is the total variation norm. A set `C` is `f`-regular if
`sup_{x ∈ C} E_x[Σ_{k<τ_B} f(Φ_k)] < ∞` for every `B ∈ B⁺(X)`, and the chain is `f`-regular if
countably many `f`-regular sets cover `X` (p. 339). The `f`-modulated drift condition (V3),
`ΔV ≤ −f + b 1_C` (14.16), is the dual of `f`-regularity. §14.1 works with an accessible atom.
A recurrent chain with a self-`f`-regular set (14.10) is positive with `π(f) < ∞`
(Proposition 14.1.1). The `f`-regular sets are the sets on which `G_α(·, f)` is bounded
(Proposition 14.1.2). The Regenerative Decomposition in `f`-norm (14.6) gives `f`-norm
convergence and the summed bound (14.13) (Theorems 14.1.3–14.1.4). §14.2 proves the duality. Under
(V3) for a petite set, every set on which `V` is bounded is `f`-regular, and for an `f`-regular
`C ∈ B⁺(X)` the function `G_C(·, f)` solves (V3) (Lemma 14.2.1, Theorems 14.2.2–14.2.7). The
duality passes to the `m`-skeletons with `f^{(m)} = Σ_{i<m} Pⁱf` (14.22) (Lemma 14.2.8,
Theorems 14.2.9–14.2.10), and `π(f) < ∞` gives `f`-regular sets whose union is full
(Theorem 14.2.11). §14.3 proves the `f`-ergodic theorems: through the split chain for strongly
aperiodic chains (Proposition 14.3.1), from a skeleton to the chain (Lemma 14.3.2), for aperiodic
chains (Theorem 14.3.3), the summed bounds (14.24)–(14.25) (Theorems 14.3.4–14.3.5), the periodic
case (Theorem 14.3.6) and the criterion `π(f) ≤ π(s)` (Theorem 14.3.7). These results make up the
`f`-Norm Ergodic Theorem 14.0.1: for a `ψ`-irreducible aperiodic chain, positivity with
`π(f) < ∞`, the bound (14.2) on a petite set and the drift (14.3) are equivalent, and (14.4)–(14.5)
follow. §14.4 applies the theorem to random walk on a half line (Proposition 14.4.1) and to the
bilinear model (Proposition 14.4.2). §14.5 turns to renewal processes on `ℝ₊`. It quotes
Blackwell's renewal theorem (Theorem 14.5.1) from Feller. From the total variation theory of the
forward recurrence time `δ`-skeleton it proves the Uniform Key Renewal Theorem 14.5.2 for
spread-out increments (Propositions 14.5.3–14.5.5). §14.6 is commentary, with
Proposition 14.6.1 on the drift (V4′) of Jarner and Roberts.

Every numbered result of Chapter 14 is formalised: Theorem 14.0.1, Propositions 14.1.1–14.1.2,
Theorems 14.1.3–14.1.4, Lemma 14.2.1, Theorems 14.2.2–14.2.7, Lemma 14.2.8,
Theorems 14.2.9–14.2.11, Proposition 14.3.1, Lemma 14.3.2, Theorems 14.3.3–14.3.7,
Propositions 14.4.1–14.4.2, Theorems 14.5.1–14.5.2, Propositions 14.5.3–14.5.5 and
Proposition 14.6.1. Blackwell's renewal theorem, which the book quotes from Feller, is proved for
non-lattice increment laws with finite mean. Five claims are false as printed. Each is refuted in
Lean by a counterexample of this project, and for each a corrected statement is proved.
Proposition 14.1.1 and Theorem 14.2.4 (i) ⇒ (ii) fail for `C = ∅`, which satisfies (14.10) and
(14.19) vacuously (`proposition_14_1_1_counterexample`, `theorem_14_2_4_counterexample`). For the
same reason Theorem 14.0.1 (ii) needs a non-empty petite set. Theorem 14.0.1 also states that every
sublevel set of a solution of (14.3) satisfies (14.2); this fails for a sublevel set outside
`B⁺(X)` (`theorem_14_0_1_counterexample`). Proposition 14.4.2 has no stability condition: the AR(1)
model `Xₙ₊₁ = 2Xₙ + Wₙ₊₁` satisfies its hypotheses and is not positive Harris
(`proposition_14_4_2_counterexample`). It is proved under `E|θ + bW|ᵏ < 1`. Two arguments of §14.5
are corrected; the statements are true, so there is no counterexample. (14.40) follows from (14.36)
only with reflected test functions. The truncation argument that the book gives for
Theorem 14.5.2 (iii) uses `δ₀`, which is not absolutely continuous; (iii) is proved by smoothing
`f` with `Γ₀`. Further points are made explicit without a counterexample of their own. Where the
book's standing assumption `f : X → [1, ∞)` is used, `f ≥ 1` is assumed, and `f` is assumed finite
everywhere or at one point; `b < ∞` in (V3); the state space is countably generated; strong
aperiodicity puts the small set in `B⁺(X)`; Proposition 14.4.2 takes `ψ`-irreducibility,
aperiodicity and petite compact sets as hypotheses; and in §14.5 the first-epoch laws live on
`(0, ∞)` and `Γ(−∞, 0) = 0 < Γ(0, ∞)`. Some statements are proved in a stronger form or in full.
Theorem 14.2.11 holds for every positive chain; the book's proof covers only aperiodic chains, and
the lazy chain `½ (I + P)` removes aperiodicity. Theorem 14.3.6, which the book states without
proof, is proved in full, with (ii) for every initial state. Theorems 14.3.4–14.3.5 need
positivity and aperiodicity, not positive Harris recurrence. Theorem 14.3.7 holds for any finite
invariant measure, without the ergodic theorems. Theorem 14.5.1 holds for every first-epoch law
on `ℝ`. The book uses the integrals
`∫ λ(dx) ‖Pⁿ(x, ·) − π‖_f` without comment; the measurability of `x ↦ ‖Pⁿ(x, ·) − π‖_f` is
proved for finite `f`, and gives Proposition 14.4.1 (i) in the book's integrated form. The
following are not formalised: Blackwell's theorem for infinite mean; the general Key Renewal
Theorem for directly Riemann integrable `f`, quoted from Feller; the informal remarks, among them
the GI/M/1 remark on (V4′) and the discussions of moments; and the commentary of §14.6, apart from
Proposition 14.6.1. See [corrections](docs/corrections.md). The library contains
**2787 theorems**. Of these, 362 are in the 25 Chapter 14 modules. The other 2425 are in the
modules carried from the Chapter 13 project `Ergodicity`, which cover Chapters 1–11 and 13 and
the renewal theory.

The chapter rests on nine groups of results.

* **The `f`-norm** (`FNorm`, `FNormMeasurable`). `fNorm f μ ν` is `sup_{|g| ≤ f} |μ(g) − ν(g)|`
  over measurable `g : X → ℝ` with `|g| ≤ f` that are integrable for both measures (`IsFTest`). It
  is valued in `[0, ∞]`, so it needs no finiteness of `μ(f)` or `ν(f)`, and it is at most
  `μ(f) + ν(f)` (`fNorm_le_add`). For `f ≡ 1` it is the total variation norm (`fNorm_one`), and for
  `f ≥ 1` it dominates it (`ofReal_tvNorm_le_fNorm`). A decomposition `μ + σ₂ = ν + σ₁` bounds it by
  `σ₁(f) + σ₂(f)` (`fNorm_le_of_add_eq`), which turns the regenerative decompositions into `f`-norm
  bounds. Transport by a kernel gives `‖μQ − νQ‖_f ≤ ‖μ − ν‖_{Qf}` (`fNorm_comp_le`) and
  `‖λQ − μQ‖_f ≤ ∫∫ λ(dx) μ(dy) ‖Q(x, ·) − Q(y, ·)‖_f` (`fNorm_comp_le_lintegral`). On a countably
  generated space and for finite `f`, the norm is a supremum over one countable algebra of sets that
  does not depend on the measures (`fNorm_eq_iSup_fNormAlgebra`, through the Hahn decomposition of
  `fμ − fν`). So `x ↦ ‖κ(x, ·) − ν‖_f` is measurable for a finite kernel `κ`
  (`measurable_fNorm_kernel`).
* **`f`-regularity and (V3)** (`FRegularSets`, `FRegularityDrift`). `fSumReturn P B f x` is
  `E_x[Σ_{k<τ_B} f(Φ_k)]`. The `f`-regular sets, states, measures and chains are `IsFRegularSet`,
  `IsFRegularState`, `IsFRegularMeasure` and `IsFRegularChain`. (V3) is `DriftV3 P V f b C`, written
  `PV + f ≤ V + b 1_C` with `b` finite as a separate hypothesis. A strong Markov bound for sums
  (`fSumReturn_le_stopping`) and Theorem 10.4.9 for functions (`lintegral_eq_fSumReturn`) carry the
  arguments. Proposition 14.1.1 is `proposition_14_1_1`, Lemma 14.2.1 is `lemma_14_2_1`, and the
  Comparison Theorem 14.2.2 is `theorem_14_2_2`. Theorems 14.2.3–14.2.7 are `theorem_14_2_3_i`,
  `theorem_14_2_3_i_fRegular`, `theorem_14_2_3_ii`, `theorem_14_2_4`, `theorem_14_2_5`,
  `theorem_14_2_6` and `theorem_14_2_7`; `G_C(·, f)` solves (V3) by `driftV3_gKernelFn`.
* **Chains with atoms** (`FRegularAtoms`). The Regenerative Decomposition (14.6) is an `f`-norm
  bound for every measurable `f ≥ 0`, bounded or not (`fNorm_comp_pow_succ_le`), with its form
  (14.14)–(14.15) against the atom (`fNorm_comp_pow_succ_le_atom`). From an ergodic atom it gives
  `‖λPⁿ − π‖_f → 0` (`tendsto_fNorm_of_ergodic_atom`), and summed it gives
  `tsum_fNorm_comp_le_atom`. Proposition 14.1.2 is `proposition_14_1_2_i` and
  `proposition_14_1_2_ii`, Theorem 14.1.3 is `theorem_14_1_3_i`, `theorem_14_1_3_ii` and
  `theorem_14_1_3_iii`, and Theorem 14.1.4 is `theorem_14_1_4`. `f`-ergodicity (p. 337) is
  `IsFErgodic`.
* **Skeletons and the split chain** (`FSkeletons`, `FSplitChain`, `FNormErgodic`). `f^{(m)}` is
  `fSkel P m f`. (V3) iterates to (14.21) (`driftV3_iterate`) and becomes (V3) for the skeleton
  with `½ f^{(m)}` and a set that is small for `Pᵐ` (`driftV3_skeleton`, through
  Lemma 14.2.8, `lemma_14_2_8`). Theorems 14.2.9–14.2.10 are `theorem_14_2_9` and
  `theorem_14_2_10`, and Lemma 14.3.2 is `lemma_14_3_2_i`, `lemma_14_3_2_ii` and
  `lemma_14_3_2_iii`. For a minorization on a set in `B⁺(X)`, the split chain carries the atom
  results back to `X` (`Minorization.fSumReturn_split`, `Minorization.tendsto_fNorm`,
  `Minorization.tsum_fNorm_le`, `Minorization.exists_fRegular_cover`). For an aperiodic chain a
  skeleton has such a minorization (`exists_skeleton_minorization`, carried). This gives the two
  workhorses of the chapter: under (V3) on a petite set, `‖λPⁿ − π‖_f → 0` whenever `λ(V) < ∞`
  (`tendsto_fNorm_of_driftV3`), and `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ A (V(x) + V(y)) + B`
  (`tsum_fNorm_le_of_driftV3`). Theorem 14.2.11 for aperiodic chains is `theorem_14_2_11`, and
  Theorem 14.3.7 is `theorem_14_3_7`, by truncating `V`.
* **The `f`-Norm Ergodic Theorem** (`FNormErgodicTheorem`, `FLazyChain`). Theorem 14.0.1 is
  `theorem_14_0_1`, a `List.TFAE` (Mathlib) of (i) an invariant probability with `π(f) < ∞`,
  (ii) the bound (14.2) on a non-empty petite set and (iii) (14.3) for a petite set and a `V`
  finite somewhere. Its consequences, that `S_V` is absorbing and full, that the sublevel sets of `V`
  are `f`-regular, and (14.4) and (14.5), are `theorem_14_0_1_consequences`. The counterexample to
  the sublevel-set claim is `theorem_14_0_1_counterexample`. Proposition 14.3.1 is
  `proposition_14_3_1_i`, `proposition_14_3_1_ii` and `proposition_14_3_1_iii`, Theorem 14.3.3 is
  `theorem_14_3_3_i`, `theorem_14_3_3_ii`, `theorem_14_3_3_iii` and `theorem_14_3_3_iii_converse`,
  and Theorems 14.3.4–14.3.5 are `theorem_14_3_4` and `theorem_14_3_5`. Theorem 14.2.11 without
  aperiodicity is `theorem_14_2_11_of_isPositive`. The lazy chain `K = ½ (I + P)` (`lazyKernel`,
  carried) is aperiodic (`isAperiodic_lazyKernel`). Its return sums dominate those of `P`
  (`fSumReturn_le_lazy`, by the Comparison Theorem for `½ G^K_B(·, f 1_{Bᶜ})`), so an `f`-regular set
  of `K` is `f`-regular for `P`.
* **Periodic chains** (`FPeriodicErgodic`, `FPeriodicCycle`, `FPeriodicAll`). On a cycle class
  `Dᵢ` the chain that moves by `Pᵈ` and jumps to `πᵢ = d π(· ∩ Dᵢ)` off `Dᵢ` (`absorbKernel`,
  `cycleInv`, carried) is positive Harris and aperiodic (`IsCycle.absorbKernel_isPositiveHarris`),
  and Theorem 14.3.3 applies to it (`IsCycle.fRegular_absorbKernel`). Theorem 14.3.6 (i) is
  `theorem_14_3_6_i`. With the cycle inside a measurable full absorbing set `S_f` it is
  `theorem_14_3_6_i_cycle`, and in the labelling of (14.26) it is `theorem_14_3_6_i_book`.
  Theorem 14.3.6 (ii) is `theorem_14_3_6_ii` on the cycle and `theorem_14_3_6_ii_all` for every
  initial state. The proof of the latter decomposes `Pⁿ(x, ·)` at the first entrance into part of
  one cycle class and lets the mixtures converge by dominated convergence for series
  (`IsCycle.exists_mixture_set`, `tendsto_tsum_of_le`).
* **Specific models** (`FErgodicModels`, `FHalfLineIntegrated`). For random walk on a half line
  (`halfLineWalkKernel`, carried), (14.29) is `halfLine_drift_14_29` and Proposition 14.4.1 is
  `proposition_14_4_1`. The book's integrated form of (i) is `proposition_14_4_1_i_integrated`. It
  combines the pointwise limit, `measurable_fNorm_kernel` and a generalised dominated convergence
  theorem (`tendsto_lintegral_of_le_of_tendsto`). For the bilinear model (`bilinearKernel`,
  carried), (V3) with `V = a|x|ᵏ` and `f = |x|ᵏ + 1` holds when `E|W|ᵏ < ∞` and `E|θ + bW|ᵏ < 1`
  (`bilinear_driftV3`, by Minkowski's inequality `bilinear_lintegral_pow_le`). Proposition 14.4.2
  is `proposition_14_4_2` under that condition, and `proposition_14_4_2_counterexample` refutes it
  as printed. (14.32) is the case `k = 2` (`bilinear_condition_14_32`). Proposition 14.6.1 is
  `proposition_14_6_1`.
* **§14.5 in continuous time** (`ContinuousRenewal`, `RenewalMeasure`, `RenewalRegeneration`,
  `RenewalChain`, `RenewalKey`, `RenewalEquilibrium`, `RenewalUniform`, `RenewalAbsCont`). The
  renewal measure `μ ∗ U = Σ_{m ≥ 0} μ ∗ Γ^{m∗}` is `renMeas Γ μ`, the expected number of epochs of
  the delayed renewal process in a set. It is locally finite, by a Chernoff bound
  (`renMeas_dirac_Iic_le`). The regeneration identity (14.43) at the skeleton times `nδ` is
  `renMeas_eq_lintegral_skeleton`. The forward recurrence time `δ`-skeleton (`fwdSkelKernel`,
  carried) is made into a chain on `ℝ` (`fwdChain`) that is irreducible, positive and aperiodic,
  satisfies (V2) and has regular initial laws of finite mean (`fwdChain_structure`); Theorem 13.4.4
  then gives (14.41) (`tsum_tvNorm_fwdSkel_ne_top`). Propositions 14.5.3–14.5.5 are
  `proposition_14_5_3`, `proposition_14_5_4_renewal` and `proposition_14_5_5`. The equilibrium
  renewal measure is `Γₑ ∗ U = β⁻¹ μ_Leb` on `(0, ∞)` (`renMeas_eqLaw`). Theorem 14.5.2 is
  `theorem_14_5_2_i`, `theorem_14_5_2_ii` and `theorem_14_5_2_iii`, and Theorem 14.5.1 for
  spread-out laws is `theorem_14_5_1_spreadOut`.
* **Blackwell's renewal theorem** (`BlackwellHarmonic`, `BlackwellRenewal`). Theorem 14.5.1 is
  `theorem_14_5_1`, for every non-lattice `Γ` on `[0, ∞)` with finite mean (`IsNonLattice`) and
  every first-epoch law. The proof is analytic. For a Lipschitz `g` with compact support, put
  `Z = δ₁ ∗ U ∗ g`; it is bounded and uniformly continuous, and it satisfies the iterated renewal
  equation (`convAt_eq_iterate`). A maximum principle replaces the Choquet–Deny lemma and the
  compactness of vague limits (`eventually_sub_le_of_harmonic`, `tendsto_sub_of_harmonic`). It gives
  `Z(t) − Z(t − y) → 0` at every support point `y` of `Γ`. The `a` with `Z(t) − Z(t − a) → 0` form a
  closed additive subgroup of `ℝ`, and since `Γ` is non-lattice it is all of `ℝ`
  (`tendsto_sub_of_isNonLattice`, through `AddSubgroup.dense_or_cyclic`, Mathlib). Averaging against
  the stationary delay, with `Γₑ ∗ U = β⁻¹ μ_Leb`, identifies the limit as `β⁻¹ ∫ g`
  (`tendsto_convAt_of_lipschitz`). Trapezoids squeeze the indicator of `[a, b]`
  (`blackwell_dirac`), and mixing over the first epoch gives the theorem.

The library covers the chapter as follows.

* **The `f`-Norm Ergodic Theorem** (Chapter 14 introduction, pp. 336–338). The `f`-norm,
  Theorem 14.0.1 with (14.1)–(14.5) and the corrections to (ii) and to the sublevel-set claim, and
  the definition of `f`-ergodicity.
* **`f`-regularity for chains with atoms** (§14.1.1). (14.6)–(14.9), the definitions of
  `f`-regularity, Proposition 14.1.1 with its counterexample and correction, Proposition 14.1.2 and
  (14.11)–(14.12).
* **`f`-ergodicity for chains with atoms** (§14.1.2). Theorem 14.1.3, (14.13)–(14.15) and
  Theorem 14.1.4.
* **The drift characterization of `f`-regularity** (§14.2.1). (V3), (14.16)–(14.18), Lemma 14.2.1,
  the Comparison Theorem 14.2.2 and Theorem 14.2.3.
* **`f`-regular sets** (§14.2.2). Theorem 14.2.4 with its counterexample and correction,
  Theorem 14.2.5 and (14.20), Theorems 14.2.6–14.2.7.
* **`f`-regularity and `m`-skeletons** (§14.2.3). (14.21)–(14.22), Lemma 14.2.8,
  Theorems 14.2.9–14.2.10, Theorem 14.2.11 with and without aperiodicity.
* **The aperiodic `f`-ergodic theorem** (§14.3.1). Proposition 14.3.1, Lemma 14.3.2 and
  Theorem 14.3.3.
* **Sums of transition probabilities** (§14.3.2). (14.23), Theorems 14.3.4–14.3.5 and
  (14.24)–(14.25), and Theorem 14.3.6 with (14.26)–(14.27).
* **A criterion for finiteness of `π(f)`** (§14.3.3). Theorem 14.3.7.
* **Random walk on `ℝ₊`** (§14.4.1). (14.28)–(14.29) and Proposition 14.4.1, pointwise and
  integrated.
* **Bilinear models** (§14.4.2). (14.30)–(14.33) and Proposition 14.4.2 with its counterexample and
  correction.
* **A key renewal theorem** (§14.5). (14.34), Theorem 14.5.1 and (14.35), Theorem 14.5.2 and
  (14.36)–(14.40), (14.41), Proposition 14.5.3 and (14.42)–(14.44), Proposition 14.5.4 and
  (14.45)–(14.47), `Γₑ ∗ U = β⁻¹ μ_Leb`, Proposition 14.5.5 and (14.48)–(14.49), and (14.50) with
  the absolute continuity of `Γ₀ ∗ U`.
* **Commentary** (§14.6). Proposition 14.6.1 and (14.51)–(14.52).

All names are in the namespace `MeynTweedie.FErgodicity`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

### The Chapter 14 modules (362 theorems)

| Module | Theorems | Contents |
| --- | ---: | --- |
| [FNorm](FErgodicity/FNorm.lean) | 23 | Chapter 14 introduction: the `f`-norm and its test functions, the defining bound, symmetry, monotonicity in `f`, the triangle inequality, bounds from decompositions `μ + σ₂ = ν + σ₁`, `‖μ − ν‖_1 = ‖μ − ν‖`, transport by maps and kernels, convexity over initial laws, the remark of p. 337 |
| [FRegularSets](FErgodicity/FRegularSets.lean) | 44 | §§14.1.1, 14.2.1: `E_x[Σ_{k<τ_B} f(Φ_k)]`, the strong Markov bound for sums, `U_A(x, f)`, Theorem 10.4.9 for functions, `f`-regular sets, states, measures and chains, (V3) and (14.17), Lemma 14.2.1, the Comparison Theorem 14.2.2, Proposition 14.1.1 corrected and its counterexample |
| [FRegularityDrift](FErgodicity/FRegularityDrift.lean) | 21 | §§14.2.1–14.2.2: the occupation bound (11.27), `G_A(x, f)` and its bounds, `G_C(·, f)` solves (V3), Theorem 14.2.3, the `f`-regularity of measures with `λ(V) < ∞`, Theorem 14.2.4 corrected and its counterexample, Theorems 14.2.5–14.2.7 |
| [FRegularAtoms](FErgodicity/FRegularAtoms.lean) | 29 | §14.1: the Regenerative Decomposition (14.6) and (14.14)–(14.15) in `f`-norm, (14.7), (14.9), convergence from an ergodic atom, the summed bound, (V3) for `G_α(·, f)`, Proposition 14.1.2, `f`-ergodicity, Theorems 14.1.3–14.1.4 |
| [FSkeletons](FErgodicity/FSkeletons.lean) | 23 | §14.2.3, Lemma 14.3.2: `f^{(m)}` (14.22), (14.21), minorizations at all large times, Lemma 14.2.8, (V3) for the skeleton, the skeleton dominates the chain, Theorems 14.2.9–14.2.10, Lemma 14.3.2 |
| [FSplitChain](FErgodicity/FSplitChain.lean) | 10 | §§14.2.3, 14.3.1: return sums of the split chain, positivity of the split chain, Theorem 14.2.11 and Proposition 14.3.1 (ii) for a minorization on a set in `B⁺(X)`, the pointwise strongly aperiodic case of Theorem 14.3.4 |
| [FNormErgodic](FErgodicity/FNormErgodic.lean) | 8 | §§14.2.3, 14.3.3: Theorem 14.3.7 by truncation, `π(f) ≤ b π(C)` under (V3), aperiodicity from a minorization, Lemma 14.3.2 (i) from an initial law, convergence and summability from (V3), Theorem 14.2.11 for aperiodic chains |
| [FNormErgodicTheorem](FErgodicity/FNormErgodicTheorem.lean) | 20 | §14.3 and Theorem 14.0.1: the `f`-regular states, `Pᵏ(x, f) → ∞` when `π(f) = ∞`, Proposition 14.3.1, Theorems 14.3.3–14.3.5, positivity from (V3), Theorem 14.0.1 and its consequences, the counterexample to the sublevel-set claim |
| [FErgodicModels](FErgodicity/FErgodicModels.lean) | 25 | §§14.4, 14.6: the moment calculations (14.28), (14.29), Proposition 14.4.1, Minkowski's inequality for the bilinear step, (V3) for the bilinear model, (14.31)–(14.32), Proposition 14.4.2 corrected and its counterexample, Jensen's inequality for `√V`, Proposition 14.6.1 |
| [FPeriodicErgodic](FErgodicity/FPeriodicErgodic.lean) | 10 | Theorem 14.3.6: the chain on a cycle class, its `f^{(d)}`-regular states and their convergence, return sums through `U_B(x, f 1_{Bᶜ})` and on absorbing sets, the skeleton on a cycle class, Theorem 14.3.6 (i) on `Dᵢ ∩ S_f`, Theorem 14.3.6 (ii) on the cycle |
| [ContinuousRenewal](FErgodicity/ContinuousRenewal.lean) | 3 | §14.5: `ρ ∗ g(t)`, the bound (14.47), Proposition 14.5.4 from (14.42), Theorem 14.5.2 (ii) from (i) with reflected test functions |
| [FNormMeasurable](FErgodicity/FNormMeasurable.lean) | 12 | The `f`-norm through a Hahn decomposition of `fμ − fν`, a countable algebra of sets that determines it, the measurability of `x ↦ ‖κ(x, ·) − ν‖_f`, generalised dominated convergence |
| [FHalfLineIntegrated](FErgodicity/FHalfLineIntegrated.lean) | 3 | §14.4.1: convergence of `μₙ(f)` from `f`-norm convergence, `PⁿV ≤ V + nD`, Proposition 14.4.1 (i) in integrated form |
| [FLazyChain](FErgodicity/FLazyChain.lean) | 8 | Theorem 14.2.11: sums before hitting times as `G_B(·, f 1_{Bᶜ})`, return sums of the lazy chain dominate those of `P`, the lazy chain is aperiodic, Theorem 14.2.11 for every positive chain |
| [FPeriodicCycle](FErgodicity/FPeriodicCycle.lean) | 5 | Theorem 14.3.6 (i): absorbing full subsets of full sets, cycles restricted to them, Theorem 14.3.6 (i) with the cycle inside `S_f` and in the labelling of (14.26) |
| [FPeriodicAll](FErgodicity/FPeriodicAll.lean) | 11 | Theorem 14.3.6 (ii): `f`-norm algebra for sums and multiples, phases of a sequence, dominated convergence for series, a uniform bound from (V3), mixtures started in one cycle class, Theorem 14.3.6 (ii) for every initial state |
| [RenewalMeasure](FErgodicity/RenewalMeasure.lean) | 10 | §14.5: the renewal measure `μ ∗ U` of a delayed renewal process on `ℝ₊` as a mixture over the first epoch, the laws of the partial sums, local finiteness by a Chernoff bound, no mass on `(−∞, 0]` |
| [RenewalRegeneration](FErgodicity/RenewalRegeneration.lean) | 2 | (14.43): the epochs after `nδ` as those of the restarted process, the regeneration identity at the skeleton times |
| [RenewalChain](FErgodicity/RenewalChain.lean) | 15 | §14.5, p. 356: the forward recurrence time `δ`-skeleton restarted from `(−∞, 0]`, irreducibility, the mean forward recurrence time, (V2) with `V(x) = x/δ + 1`, positivity, aperiodicity and regular initial laws, (14.41) |
| [RenewalKey](FErgodicity/RenewalKey.lean) | 10 | Proposition 14.5.3: additivity and shifts of the renewal measure, a Jordan decomposition, the slabs `(nδ, (n + 1)δ]`, the renewal measure on a slab, (14.42) and (14.44) |
| [RenewalEquilibrium](FErgodicity/RenewalEquilibrium.lean) | 8 | Proposition 14.5.4 for renewal measures, the equilibrium law `Γₑ` (10.36), stationarity of `Γₑ ∗ U`, Cauchy's equation, the renewal equation `μ ∗ U = μ + (μ ∗ Γ) ∗ U`, `Γₑ ∗ U = β⁻¹ μ_Leb` |
| [RenewalUniform](FErgodicity/RenewalUniform.lean) | 22 | Theorem 14.5.2 (i)–(ii), Proposition 14.5.5: the renewal measure as a mixture, shifts, the bound (14.49), truncation and (14.48), Proposition 14.5.5, `Γₑ ∗ U ∗ g(t) = β⁻¹ ∫_{s<t} g`, Theorem 14.5.2 (i) and (ii), Theorem 14.5.1 for spread-out laws |
| [RenewalAbsCont](FErgodicity/RenewalAbsCont.lean) | 8 | Theorem 14.5.2 (iii): the step (14.50), absolute continuity of `Γ₀ ∗ U`, minimal couplings, Proposition 14.5.4 without (14.39), smoothing by the first-epoch law, Theorem 14.5.2 (iii) |
| [BlackwellHarmonic](FErgodicity/BlackwellHarmonic.lean) | 5 | Theorem 14.5.1: non-lattice laws and support points, the maximum principle that replaces the Choquet–Deny lemma, translation invariance at infinity for non-lattice laws |
| [BlackwellRenewal](FErgodicity/BlackwellRenewal.lean) | 27 | Theorem 14.5.1: the epoch laws and their lower bounds, `sup_t U₁[t, t + l] < ∞`, mixing over the first epoch, the iterated renewal equation, the key renewal theorem for Lipschitz `g`, trapezoids, Blackwell's theorem from the first epoch `1` and from every first-epoch law |

### Carried modules (2425 theorems)

Carried from the Chapter 13 project `Ergodicity` (2425 theorems): all 111 modules of that
project, identical to the copies there except for the namespace and the imports. Its own modules
(420 theorems) are the renewal modules (134 theorems) `SequenceLemmas` (30), `RenewalSequences`
(41), `RenewalTheorem` (22), `KeyRenewal` (5), `KendallTheorem` (36), and the Chapter 13 modules
(286 theorems) `TotalVariation` (36), `RegenerativeDecomposition` (52), `AtomErgodic` (11),
`SplitErgodic` (14), `AperiodicErgodic` (9), `CountableErgodic` (35), `PeriodicErgodic` (47),
`LinkedRenewal` (25), `SumsOfTransitions` (31), `CouplingRenewal` (10), `SumsNoAtom` (12),
`ErgodicTheorem` (4). The total variation norm (`tvNorm`), the entry law, renewal sequence and
taboo kernels of an atom (`entryLaw`, `atomRenewal`, `eq_smul_atomMeasure_of_accessible`,
`pow_succ_eq_firstEntrance`), ergodic atoms (`proposition_13_2_4_i`,
`tendsto_atomRenewal_of_aperiodicLaw`), the split chain (`theorem_13_3_1_ii`,
`split_comp_pow_map_fst`), skeletons with a minorization on a set in `B⁺(X)`
(`exists_skeleton_minorization`), chains agreeing on an absorbing set and the probabilities of a
cycle (`absorbKernel`, `cycleInv`, `IsCycle.tendsto_tvNorm_pow_mul`, `tendsto_tvNorm_of_isPositive`),
`Var(u)` (`renewalVar`), the Harris property from every state (`IsHarris.hitProb_eq_one`) and
Theorem 13.4.4 (`theorem_13_4_4`) are used. No Chapter 14 module
depends, directly or through other modules, on `KeyRenewal`, `CountableErgodic`, `CouplingRenewal`
or `ErgodicTheorem`; the discrete forms of §14.5 in `KeyRenewal` are not used by the
continuous-time proofs.

Carried in turn by `Ergodicity` from the Chapter 11 project `DriftRegularity` and the Chapter 10
project `InvariantMeasures`, and by `InvariantMeasures` from the earlier projects (see those
projects' READMEs for how the copies differ from the originals):

* From the Chapter 11 project `DriftRegularity` (134 theorems): `Comparison` (33), `RegularSets`
  (29), `FosterCriterion` (27), `RegularityConverse` (38), `AtomHittingBounds` (7). Sums along the
  path and the Comparison Theorem (`sumBefore`, `comparison_theorem_pathKernel`,
  `lemma_11_3_10`), `G_A(x, f)` and `U_A(x, f)` (`gKernelFn`, `tabooPotFn`, `theorem_11_3_5_i`),
  regular sets, measures and chains (`IsRegularSet`, `IsRegularMeasure`, `IsRegularChain`), (V2)
  (`DriftV2`), Proposition 11.3.8 (`proposition_11_3_8`), Theorems 11.3.12 and 11.3.14
  (`theorem_11_3_12_i`, `theorem_11_3_14`), positive Harris recurrence from (V2)
  (`theorem_11_3_4_positiveHarris`), the equivalence of regularity and positivity
  (`isPositive_of_isRegularSet`) and the lazy chain (`lazyKernel`, `isMarkovKernel_lazyKernel`,
  `isMaximalIrreducibility_lazy_pow`) are used.
* From the Chapter 10 project `InvariantMeasures`, its own modules (316 theorems):
  `Invariance` (39), `MinimalInvariant` (22), `AtomInvariant` (30), `SplitInvariant` (8),
  `UniqueInvariant` (18), `PositiveNull` (14), `CountableInvariant` (22), `QueueInvariant` (19),
  `MG1Invariant` (25), `ModelInvariant` (11), `QueueInvariantMinimal` (26), `LadderInvariant` (42),
  `GIG1Invariant` (9), `RenewalInvariant` (17), `LinearInvariant` (14). Invariant measures and
  positive chains (`IsInvariant`, `IsInvariantMeasure`, `IsPositive`, `IsPositiveHarris`,
  `proposition_10_1_1`), mean return times (`meanReturnTime`), the taboo measures (`tabooSeq`),
  Theorems 10.4.5 and 10.4.9 (`theorem_10_4_5_positive`, `theorem_10_4_9`, `theorem_10_4_9_equiv`),
  the forward recurrence time chain of a heavy-tailed renewal law (`heavyRenewal`, `fwdRecInv`) and
  the invariant measure of the forward recurrence time skeleton (`fwdSkelInv`) are used. No
  Chapter 14 module depends on `QueueInvariant`, `MG1Invariant`, `ModelInvariant`,
  `QueueInvariantMinimal`, `LadderInvariant`, `GIG1Invariant` or `LinearInvariant`.
* From the Chapter 9 project `HarrisRecurrence` (212 theorems): `HarrisDefinitions` (29),
  `HarrisProperties` (15), `HarrisDecomposition` (18), `SupermartingaleDrift` (14),
  `NonEvanescence` (21), `TopologicalRecurrence` (21), `TopologicalExamples` (33), `DriftHarris`
  (29), `StochasticComparison` (32). Harris chains (`IsHarris`),
  Proposition 9.1.1 (`proposition_9_1_1`), the Harris decomposition (`theorem_9_1_5`) and
  Proposition 9.5.2 (`proposition_9_5_2_necessity`: a Harris recurrent AR(1) model with bounded
  noise has `|α| ≤ 1`) are used.
  No Chapter 14 module depends on `TopologicalExamples`.
* From the Chapter 8 project `TransienceRecurrence` (220 theorems): `UniformTransience` (46),
  `Decompositions` (8), `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23),
  `CountableClassification` (18), `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16),
  `SkipFreeWalk` (15), `RandomWalkMeanZero` (5). Recurrent chains (`IsRecurrentChain`) and the
  drift and petite sets of random walk on a half line (`halfLine_drift_neg`, `halfLine_isPetite_Iic`)
  are used. No Chapter 14 module depends on `RandomWalkIntegers`, `SkipFreeWalk` or
  `RandomWalkMeanZero`.
* From the Chapter 6 project `TopologyContinuity` (130 theorems): `FellerChains` (40), `TChains`
  (14), `EChains` (16), `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16),
  `TChainModels` (10), `EChainsStability` (12). No Chapter 14 module depends on `EChains`,
  `LinearTChains`, `FellerModels`, `CompactPetite`, `TChainModels` or `EChainsStability`.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` (`pathKernel`),
  the kernels `U_A` and `_APⁿ` (`tabooPotKernel`, `tabooKernel`), hitting and return times
  (`firstHit`, `firstReturn`, `hitProb`) and the strong Markov property (`strong_markov_lintegral`)
  are used throughout. No Chapter 14 module depends on `StateSpaces`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Absorbing and full sets (`IsAbsorbing`, `IsFull`,
  `proposition_4_2_3_i`) and irreducibility (`IsPhiIrreducible`, `IsMaximalIrreducibility`) are
  used. No Chapter 14 module depends on `CountableIrreducibility`, `LinearControllability` or
  `LinearIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Atoms (`IsAtom`,
  `IsAccessibleAtom`), the split chain (`Minorization`, `Minorization.checkAlpha`), small and petite
  sets (`IsSmall`, `IsSmallSet`, `IsPetite`, `proposition_5_5_3`), periods, cycles and aperiodicity
  (`IsPeriod`, `IsCycle`, `IsAperiodic`, `proposition_5_4_5_iii`) and the forward recurrence time
  chain (`fwdRecKernel`) are used. No Chapter 14 module depends on `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). Random walk on a
  half line and spread-out laws (`halfLineWalkKernel`, `IsSpreadOut`, `convPow`), the AR(1) model
  (`ar1Kernel`) and the bilinear model (`bilinearKernel`) are used.
* From the Chapter 5 project `PseudoAtoms` directly (286 theorems): `ModelKernels` (19),
  `ModelCountableModels` (9), `ModelQueues` (16), `ModelStorage` (18), `ModelRenewal` (29),
  `SpecificKernels` (42), `Regeneration` (12), `PoissonCounts` (12), `RenewalSkeletons` (53),
  `LadderChains` (25), `GIG1Embedding` (37), `GIG1SmallSets` (7), `RenewalSmallSets` (7). The
  epochs of a delayed renewal process (`resEpoch`), the forward recurrence time and its
  `δ`-skeleton (`fwdTimeCts`, `fwdSkelKernel`, `fwdSkel`, `fwdIndex`), regeneration of i.i.d.
  sequences (`lintegral_regeneration`, `tailSeq`) and the small sets and aperiodicity of the
  skeleton (`proposition_5_3_3`, `proposition_5_4_7`) are used. No Chapter 14 module depends on
  `GIG1Embedding` or `GIG1SmallSets`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
