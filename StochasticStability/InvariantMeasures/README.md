# Meyn and Tweedie, Chapter 10: The Existence of π, in Lean

This is the `StochasticStability/InvariantMeasures` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 10 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 229–255. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 10 divides recurrent chains into positive and null chains through their invariant
measures. A measure `μ` is invariant if `μP = μ` (10.1) and subinvariant if `μP ≤ μ` (10.5); a
ψ-irreducible chain is positive if it has an invariant probability measure and null otherwise.
§10.1 shows that positive chains are recurrent (Proposition 10.1.1), that the chain started at an
invariant probability is stationary, that limits of `μPⁿ` are invariant (10.4), that a subinvariant
measure finite on one set of `B⁺(X)` is σ-finite, dominates `ψ`, is finite on petite sets and is
invariant when finite (Proposition 10.1.2), and that a transient chain has a strictly
subinvariant measure (Proposition 10.1.3). §10.2 constructs the minimal subinvariant measure
`μ°_α = U_α(α, ·)` of an accessible atom (10.10), shows that it is invariant iff the chain is
recurrent, unique, and finite iff `E_α[τ_α] < ∞` (Theorem 10.2.1), and proves Kac's theorem
`π(α) = E_α[τ_α]⁻¹` (Theorem 10.2.2, Proposition 10.2.3). §10.3 computes invariant measures of
the forward recurrence time chain and its linked pair, the M/G/1 queue (Proposition 10.3.1) and
the GI/M/1 queue (Proposition 10.3.2). §10.4 lifts the atom case to every recurrent chain by
splitting (Propositions 10.4.1–10.4.2) and by the resolvent (Theorem 10.4.3), giving existence and
uniqueness up to constant multiples (Theorem 10.4.4) and the passage to skeletons (Theorem
10.4.5); it then studies the minimal measure `μ°_A(B) = ∫_A μ(dy) U_A(y, B)` (10.27) without
irreducibility (Proposition 10.4.6, Theorem 10.4.7, Proposition 10.4.8), proves the
representation (10.31) of `π` through excursions from a set `A` and the equivalence `π ≅ ψ`
(Theorem 10.4.9), and characterises positivity by mean return times (Theorem 10.4.10). §10.5
treats Lebesgue measure for random walk (Propositions 10.5.1–10.5.2), the forward recurrence time
`δ`-skeleton (10.36), ladder chains and their operator-geometric invariant measure (Theorem
10.5.3), the GI/G/1 queue (Theorem 10.5.4), and the linear state space model.

Every numbered result is formalised: Theorem 10.0.1, Propositions 10.1.1–10.1.3, Theorems
10.2.1–10.2.2, Propositions 10.2.3, 10.3.1 and 10.3.2, Propositions 10.4.1–10.4.2, Theorems
10.4.3–10.4.5, Proposition 10.4.6, Theorem 10.4.7, Proposition 10.4.8, Theorems 10.4.9–10.4.10,
Propositions 10.5.1–10.5.2 and Theorems 10.5.3–10.5.4, together with the claims the text makes
about its models. For the GI/M/1 queue this includes the book's own route: the chain is a ladder
chain with one-point rungs, so the last-exit decomposition of §10.5.3 gives `μ°_α(k) = s_αᵏ`
(10.24) with `s_α` the minimal root of (10.25) in `(0, 1]`, equal to `1` when `Σⱼ j pⱼ ≤ 1`, and
the recurrent case `Σⱼ j pⱼ = 1` of Proposition 10.3.2 follows. Three claims are false as printed.
Each is refuted in Lean by a counterexample, and a corrected statement is proved. Proposition
10.1.2 (ii), `ψ ≪ μ`, needs `μ ≠ 0`: the zero measure satisfies every hypothesis. The finiteness
criterion of Theorem 10.0.1 needs a non-empty petite set: `∅` is petite with
`sup_{x ∈ ∅} E_x[τ_∅] = 0`, while the forward recurrence time chain of the renewal law
`heavyRenewal`, which has infinite mean, is null recurrent. The taboo formula
`₁Pⁿ(1, j) = p(j + n − 1)` for the forward recurrence time chain holds for every `j`, and the
book's restriction to `j ≤ n`, "zero otherwise", is false: for `p = δ₂`, `₁P¹(1, 2) = 1`. Further
points are corrected without a counterexample of their own: in Theorem 10.4.7 (ii),
`μ°_A(Āᶜ) = 0` does not "follow by definition" and is proved by a mass argument; Proposition
10.4.1 holds for every minorization, not only for strongly aperiodic chains; Proposition 10.4.2
needs the split set in `B⁺(X)`; Theorem 10.4.3 needs `π` σ-finite; Theorem 10.4.10 (i) needs
`μ ≠ 0`; Proposition 10.3.1 defines `β` twice, and the condition proved is `Σⱼ j q(j) < 1`; and
Proposition 10.4.8 needs neither a probability `ν` nor `ν` supported on `A`. Countable generation
of `B(X)` is assumed for Theorem 10.4.4 and the results that depend on it. Theorem 10.4.5 assumes
recurrence for its first part; (10.2) and (10.31) are taken for `π(A) < ∞`; Proposition 10.5.2
takes `μ^{Leb}(A) < ∞`; the queues take ψ-irreducibility (for the recurrent GI/M/1 case, an
accessible atom `{0}`) and `q(0) > 0` or `p(0) > 0` as hypotheses; the forward recurrence time
chain takes a renewal law with `p(0) = 0` and, where irreducibility is used, unbounded support;
Theorem 10.5.3 is stated for a recurrent chain with `ψ([0]) > 0` and `π([0]) < ∞`, with rungs in
`ℝ`; and the linear model takes the eigenvalue condition (LSS5) and `E|W| < ∞`. The following are
not formalised: the sandwich `F[y, ∞) dy ≤ U_{[0, δ]}(x, dy) ≤ F[y − δ, ∞) dy` and the `δ/2ⁿ`
uniqueness argument by which the book guesses (10.36), which is verified directly; the
convergence `Pᵏg(x₀) → E[g(X_∞)]` for the linear model, replaced by a direct identity; the
aperiodicity remarks (10.18) and the ψ-irreducibility and positive Harris property of the linked
chain; the Gaussian form `N(0, Σ)` and the density (10.54) for the multivariate linear model (the
scalar case is proved); and the commentary of §10.6. See [corrections](docs/corrections.md). The
library contains **1871 theorems**. Of these, 316 are in the Chapter 10 modules and 1555 in the
modules carried from Chapters 1–6, 8 and 9.

Six results carry the chapter, and they are the interface that Chapters 11–17 use.

* **Invariance and positivity** (`Invariance`). `IsInvariant P μ` is the equation of measures
  `P ∘ₘ μ = μ` (10.1) and `IsSubinvariant P μ` is `P ∘ₘ μ ≤ μ` (10.5), with no σ-finiteness;
  `IsInvariantMeasure` and `IsSubinvariantMeasure` add `SigmaFinite μ`, as the book's definitions
  do. Set-wise forms are `isInvariant_iff` and `isSubinvariant_iff`. `IsPositive P ψ` and
  `IsNull P ψ` include that `ψ` is a maximal irreducibility measure, and `isPositive_or_isNull`
  splits every ψ-irreducible chain; `IsPositiveHarris` adds the Harris property. Stationarity is
  `IsInvariant.map_shift` (the shifted chain `θⁿΦ` has the law `P_π`) and its converse
  `isInvariant_iff_map_shift`; iterates and sampled kernels are `IsInvariant.pow`,
  `IsSubinvariant.sampledKernel` (10.6) and `IsInvariant.resolvent`. Positive chains are recurrent
  (`proposition_10_1_1`).
* **The invariant measure of a recurrent chain** (`UniqueInvariant`, `SplitInvariant`). A
  recurrent chain has a nonzero invariant measure, and every subinvariant measure is a finite
  multiple of it (`theorem_10_4_4`); so every subinvariant measure is invariant
  (`IsRecurrentChain.isInvariant_of_isSubinvariantMeasure`) and any two are proportional
  (`IsRecurrentChain.exists_eq_smul`). `invMeasure P h` is a chosen one, with
  `isInvariantMeasure_invMeasure`, `invMeasure_ne_zero` and `eq_smul_invMeasure`. The proof is the
  book's: the resolvent `K_{a_{1/2}}` has a minorization on a set of `B⁺(X)`
  (`theorem_5_2_3_resolvent`, carried) and is recurrent (`proposition_8_2_4`, carried); the
  invariant measure `μ°_α̌` of the split atom `α̌` has as marginal an invariant measure of the
  resolvent (`proposition_10_4_1_i`, `proposition_10_4_2`), and Theorem 10.4.3
  (`theorem_10_4_3`) transfers invariance back to `P`.
* **Atoms and Kac's theorem** (`AtomInvariant`). `meanReturnTime P A x = E_x[τ_A]` in `[0, ∞]`,
  with `E_x[τ_A] = Σ_{n ≥ 1} P_x(τ_A ≥ n) = U_A(x, X)` (10.12)
  (`meanReturnTime_eq_tabooPotKernel`). `atomMeasure P hα a = U_α(a, ·)` is `μ°_α` of (10.10) for a
  point `a ∈ α`; it is subinvariant, invariant iff the chain is recurrent (`theorem_10_2_1_i`),
  minimal among subinvariant measures with `μ(α) = 1` (`theorem_10_2_1_ii`), the only one for a
  recurrent chain (`theorem_10_2_1_ii_unique`, `IsSubinvariantMeasure.eq_smul_atomMeasure`), and
  has total mass `E_a[τ_α]` (`theorem_10_2_1_iii`, `atomMeasure_univ`). Kac's theorem
  (`theorem_10_2_2`): for an accessible atom the chain is positive iff `E_a[τ_α] < ∞`, and every
  invariant probability has `π(α) = E_a[τ_α]⁻¹` (10.14).
* **The structure of `π`** (`MinimalInvariant`, `UniqueInvariant`). `minimalMeasure P hA μ` is
  `μ°_A` of (10.27). For any chain and any subinvariant `μ` it is subinvariant and below `μ`
  (`proposition_10_4_6`, `proposition_10_4_6_minimal`); if `μ(A) < ∞` and `L(x, A) = 1` for
  `μ`-almost every `x ∈ A`, it agrees with `μ` on `A` and is invariant (`theorem_10_4_7_i`,
  `theorem_10_4_7_ii`). For a recurrent chain, a nonzero invariant measure is equivalent to `ψ`
  (`theorem_10_4_9_equiv`), `L(·, A) = 1` holds `π`-almost everywhere for `A ∈ B⁺(X)`
  (`ae_hitProb_eq_one`, from the Harris decomposition `theorem_9_1_5`, carried), and
  `π(B) = ∫_A π(dy) U_A(y, B)` for every `A ∈ B⁺(X)` with `π(A) < ∞` (10.31) (`theorem_10_4_9`),
  in the two path forms `theorem_10_4_9_path` (`k = 1, …, τ_A`) and `theorem_10_4_9_path'`
  (`k = 0, …, τ_A − 1`). Theorem 10.0.1 collects existence, uniqueness and (10.2)
  (`theorem_10_0_1`).
* **Positive and null chains** (`PositiveNull`). A positive chain has exactly one invariant
  probability (`IsPositive.invariant_prob_unique`), `stationaryDist P h`, with
  `isProbabilityMeasure_stationaryDist`, `isInvariant_stationaryDist` and `eq_stationaryDist`;
  every subinvariant measure is a finite multiple of it (`IsPositive.eq_smul_stationaryDist`). A
  recurrent chain is positive iff `invMeasure` is finite (`isPositive_iff_invMeasure_univ`).
  For a nonzero subinvariant `μ`, positivity holds iff `∫_A μ(dy) E_y[τ_A] < ∞` for one, and then
  every, `A` with `μ(A) > 0` (`theorem_10_4_10_i`); it follows from `sup_{y ∈ C} E_y[τ_C] < ∞` on a petite `C ∈ B⁺(X)`, with
  positive Harris recurrence if also `E_x[τ_C] < ∞` everywhere (`theorem_10_4_10_ii`); the
  finiteness criterion of Theorem 10.0.1 is `theorem_10_0_1_finite`.
* **The operator-geometric form for ladder chains** (`LadderInvariant`, `GIG1Invariant`). For the
  ladder chain (3.40) on `ℤ₊ × ℝ` (`ladderChainKernel Λ Λ*`, carried), the kernels
  `S^{(k)}(y, A) = U_{[0]}(0, y; k × A)` (10.42) are `ladderS Λ Λ* k`, and `S = S^{(1)}` is
  `ladS Λ Λ*`. The level-wise last-exit decomposition is proved for a general kernel `Q` and set
  `D` (`restrict_pow_comp_decomp`); with `D` the levels above `k` and the skip-free property (the
  last visit to `[k]` before reaching level `k + 1` is at level `k`) it gives one term of (10.45)
  (`ladQ_pow_succ_decomp`), hence `S^{(k+1)} = S^{(k)}S` (`ladderS_succ`) and `S^{(k)} = Sᵏ`
  (10.39) (`ladderS_eq_pow`). `S` solves `S = Σₖ SᵏΛₖ` (10.40) (`ladS_eq`) and is its minimal
  solution (10.47)–(10.51) (`ladS_minimal`). Theorem 10.5.3 (`theorem_10_5_3`):
  `π(k × A) = ∫ π₀(dy) Sᵏ(y, A)` (10.38) for a recurrent ladder chain with `ψ([0]) > 0` and
  `π([0]) < ∞`. For the GI/G/1 queue every entrance to `[0]` has the service law `H`
  (`gig1_entrance`, `tabooPotKernel_rung_zero_of_entrance`), and Theorem 10.5.4
  (`theorem_10_5_4`): the chain has an invariant probability iff
  `π̃(k × A) = ∫ H(dy) Sᵏ(y, A)` (`gig1Tilde`) is finite, and it is then `π̃/π̃(X)`.
  With one-point rungs the GI/M/1 chain is a ladder chain (`gim1LadderKernel`,
  `gim1Ladder_eq_map`, with taboo probabilities transferred by `tabooKernel_map_of_comp`); there
  `S = s_α δ₀` (`gim1_ladS`, `gim1_ladS_pow`), which gives `μ°_α(k) = s_αᵏ` (10.24)
  (`gim1_minimal_geom`) and, from `ladS_minimal`, the minimality of `s_α = gim1Alpha p` among the
  roots of (10.25) (`gim1Alpha_root`, `gim1Alpha_le_of_root`).

The library covers the chapter as follows.

* **Invariant measures** (Chapter 10 introduction, pp. 229–230). (10.1), Theorem 10.0.1 and
  (10.2), positive and null chains.
* **Invariant measures and stationarity** (§10.1.1). (10.3), stationarity of the chain started at
  an invariant probability, Proposition 10.1.1, positive Harris chains, and (10.4).
* **Subinvariant measures** (§10.1.2). (10.5)–(10.6), Proposition 10.1.2 with the correction to
  (ii), (10.7)–(10.8), Proposition 10.1.3 and (10.9).
* **Chains with atoms** (§10.2). Theorem 10.2.1 and (10.10)–(10.12), (10.13), Kac's theorem
  10.2.2 and (10.14), Proposition 10.2.3.
* **Renewal chains** (§10.3.1). The forward recurrence time chain, its taboo probabilities with
  the correction to their range, and (10.15)–(10.17), the linked
  chain (10.19) and its product invariant measure, and the null recurrent chain that refutes
  Theorem 10.0.1 for `C = ∅`.
* **The M/G/1 queue** (§10.3.2). (10.20), the cut equations, the uniqueness of the invariant
  measure whether the chain is transient or recurrent, (10.21) and Proposition 10.3.1, with
  the correction to `β`.
* **The GI/M/1 queue** (§10.3.3). (10.22)–(10.25) through the GI/M/1 chain as a ladder chain, the
  minimal root `s_α`, and Proposition 10.3.2 in the positive and the recurrent case.
* **Invariant measures for recurrent chains** (§10.4.1). Proposition 10.4.1 and (10.26),
  Proposition 10.4.2, Theorems 10.4.3–10.4.5.
* **Minimal subinvariant measures** (§10.4.2). (10.27), Proposition 10.4.6, Theorem 10.4.7 and
  (10.28)–(10.30), Proposition 10.4.8.
* **The structure of `π`** (§10.4.3). Theorem 10.4.9 and (10.31), Theorem 10.4.10 and
  (10.32)–(10.34).
* **Random walk** (§10.5.1). (10.35), Propositions 10.5.1 and 10.5.2, and the null recurrence of
  the mean-zero walk.
* **Forward recurrence time chains** (§10.5.2). (10.36) for every `δ ≥ 0`, by direct integration.
* **Ladder chains and GI/G/1 queues** (§10.5.3). (10.37), Theorem 10.5.3 and (10.38)–(10.51),
  Theorem 10.5.4 and (10.52)–(10.53).
* **Linear state space models** (§10.5.4). The series `X_∞ = Σᵢ Fⁱ G Wᵢ`, the invariance of its
  law, and the Gaussian invariant law of the scalar model.

All names are in the namespace `MeynTweedie.InvariantMeasures`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Invariance](InvariantMeasures/Invariance.lean) | 39 | Chapter 10 introduction and §10.1: invariant and subinvariant measures (10.1), (10.5), positive, null and positive Harris chains, iterates and sampled kernels (10.6), stationarity, Propositions 10.1.1, 10.1.2 (with the counterexample to (ii)) and 10.1.3, (10.9) |
| [MinimalInvariant](InvariantMeasures/MinimalInvariant.lean) | 22 | §10.4.2: the taboo measures `ρ_APⁿ`, the identities behind (10.11) and (10.30), the minimal measure `μ°_A` (10.27), Proposition 10.4.6, Theorem 10.4.7, Proposition 10.4.8, a uniqueness device for measures |
| [AtomInvariant](InvariantMeasures/AtomInvariant.lean) | 30 | §10.2: mean return times (10.12), (10.13), taboo kernels on an atom, `μ°_α` (10.10)–(10.11), Theorem 10.2.1, subinvariant measures finite on petite sets and atoms, Kac's theorem 10.2.2, Proposition 10.2.3 |
| [SplitInvariant](InvariantMeasures/SplitInvariant.lean) | 8 | §10.4.1: Proposition 10.4.1 for every minorization, Proposition 10.4.2 with `C ∈ B⁺(X)`, Theorem 10.4.3 |
| [UniqueInvariant](InvariantMeasures/UniqueInvariant.lean) | 18 | §§10.4.1, 10.4.3: Theorem 10.4.4, `invMeasure`, Theorem 10.4.5 for skeletons, Theorem 10.4.9 and the three forms of (10.31), Theorem 10.0.1 |
| [PositiveNull](InvariantMeasures/PositiveNull.lean) | 14 | §10.4.3: Theorem 10.4.10, `stationaryDist` and the uniqueness of the invariant probability, positivity iff `invMeasure` is finite, the finiteness criterion of Theorem 10.0.1 |
| [CountableInvariant](InvariantMeasures/CountableInvariant.lean) | 22 | §10.3.1: the forward recurrence time chain (10.16)–(10.17), its irreducibility, recurrence and positivity, product invariant measures and the linked chain (10.19), the null recurrent counterexample to Theorem 10.0.1 |
| [QueueInvariant](InvariantMeasures/QueueInvariant.lean) | 19 | §10.3.3: measures on `ℤ₊` given by weights, the GI/M/1 chain, (10.23)–(10.25) verified directly, a root of (10.25), Proposition 10.3.2 for positive chains |
| [QueueInvariantMinimal](InvariantMeasures/QueueInvariantMinimal.lean) | 26 | §§10.3.1–10.3.3, 10.5.1: taboo probabilities along an embedding, the GI/M/1 chain as a ladder chain, `μ°_α(k) = s_αᵏ` (10.24), `s_α` the minimal root of (10.25), `s_α = 1` when `Σⱼ j pⱼ ≤ 1`, Proposition 10.3.2 for `Σⱼ j pⱼ = 1`, the taboo formula of the forward recurrence time chain and its counterexample, M/G/1 uniqueness, the null recurrence of the mean-zero random walk |
| [MG1Invariant](InvariantMeasures/MG1Invariant.lean) | 25 | §10.3.2: the M/G/1 chain, the cut equations (10.20) for an invariant probability, their solution with `π(0) = 1`, (10.21), Proposition 10.3.1 |
| [ModelInvariant](InvariantMeasures/ModelInvariant.lean) | 11 | §§10.1.1, 10.5.1, 10.5.4: (10.35), Propositions 10.5.1 and 10.5.2, limits of `μPⁿ` are invariant (10.4), the Gaussian invariant law of AR(1) |
| [LadderInvariant](InvariantMeasures/LadderInvariant.lean) | 42 | §10.5.3: measures on `ℤ₊ × ℝ`, the last-exit decomposition, translation invariance (10.44), `S^{(k)}` (10.42), (10.45), (10.39), (10.40), (10.46), minimality (10.47)–(10.51), Theorem 10.5.3, ladder chains entering `[0]` with a fixed law |
| [GIG1Invariant](InvariantMeasures/GIG1Invariant.lean) | 9 | §10.5.3: the GI/G/1 ladder chain enters `[0]` with the service law `H`, the measure (10.52), Theorem 10.5.4 |
| [RenewalInvariant](InvariantMeasures/RenewalInvariant.lean) | 17 | §10.5.2: the renewal interval straddling a time, the kernel of `V⁺_δ`, (10.36) by direct integration, its total mass and normalisation |
| [LinearInvariant](InvariantMeasures/LinearInvariant.lean) | 14 | §10.5.4: the head and tail of an i.i.d. sequence, the series `X_∞ = Σ Fⁱ G Wᵢ` and its almost sure convergence under (LSS5), the invariance of its law `π_∞` |

Carried from the Chapter 9 project `HarrisRecurrence` (1269 theorems): 61 of the 65 modules of
that project, identical to the copies there except for the namespace. Its modules
`LinearModelHarris`, `SETAR`, `CxChain` and `IncrementAnalysis` are not carried. Its own Chapter 9
modules (212 theorems): `HarrisDefinitions` (29), `HarrisProperties` (15), `HarrisDecomposition`
(18), `SupermartingaleDrift` (14), `NonEvanescence` (21), `TopologicalRecurrence` (21),
`TopologicalExamples` (33), `DriftHarris` (29), `StochasticComparison` (32). Harris chains
(`IsHarris`), `Q ≤ L` (`harrisQ_le_hitProb`), the Harris decomposition (`theorem_9_1_5`), the
hitting time criterion (`proposition_9_1_7_ii`), Theorem 9.2.2 (ii) (`theorem_9_2_2_ii`) and
Proposition 9.4.5 (`proposition_9_4_5`) are used. No Chapter 10 module depends, directly or
through other modules, on `TopologicalExamples` or `StochasticComparison`.

Carried in turn by `HarrisRecurrence` from the Chapter 8 project `TransienceRecurrence` (1057
theorems; see those projects' READMEs for how they differ from the originals):

* Its own Chapter 8 modules (220 theorems): `UniformTransience` (46), `Decompositions` (8),
  `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23), `CountableClassification` (18),
  `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16), `SkipFreeWalk` (15), `RandomWalkMeanZero`
  (5). Recurrent, transient and uniformly transient chains (`IsRecurrentChain`,
  `IsTransientChain`, `IsUniformlyTransient`), Proposition 8.3.1 (i) (`proposition_8_3_1_i`), the
  dichotomy (`theorem_8_3_4`), Theorem 8.3.6 (i) (`theorem_8_3_6_i`), the split chain and the
  resolvent (`theorem_8_2_1_i`, `proposition_8_2_4`), skeletons (`theorem_8_2_6_ii`), and the
  recurrence of countable chains (`isRecurrentChain_count_iff`, `fwdRec_isRecurrentState`) are
  used. No Chapter 10 module depends on `RandomWalkIntegers`, `RandomWalkMeanZero` or
  `SkipFreeWalk`.
* From the Chapter 6 project `TopologyContinuity` (130 theorems): `FellerChains` (40), `TChains`
  (14), `EChains` (16), `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16),
  `TChainModels` (10), `EChainsStability` (12). The eigenvalue condition (LSS5)
  (`IsStableMatrix`, `isStableMatrix_geometric`) and the T-chain property of spread-out random
  walk (`proposition_6_3_2`) are used. No Chapter 10 module depends on `CompactPetite`, `EChains`
  or `EChainsStability`.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` and `P_μ`
  (`pathKernel`, `pathMeasure`), the shift (`shift`), the kernels `U`, `K_a`, `K_{a_ε}` and `I_A`
  (`potKernel`, `sampledKernel`, `resolvent`, `indKernel`), the taboo kernels and probabilities (`tabooKernel`, `tabooPotKernel`, `tabooProb`), return times and
  hitting probabilities (`firstReturn`, `hitProb`) and matrix kernels (`matKernel`,
  `IsTransitionMatrix`) are used throughout. No Chapter 10 module depends on `StateSpaces`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Irreducibility (`IsPhiIrreducible`, `IsMaximalIrreducibility`,
  `IsIrreducibleChain`, `isMaximalIrreducibility_count`), the resolvent `K_{a_{1/2}}`
  (`resolventHalf`), Proposition 4.2.1 (`proposition_4_2_1`) and the set `Āᶜ = {L(·, A) = 0}`
  (`noHitSet`) are used. No Chapter 10 module depends on `CountableIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Atoms (`IsAtom`,
  `IsAccessibleAtom`), minorizations and the split chain (`Minorization`,
  `Minorization.splitKernel`, `Minorization.split`, `Minorization.theorem_5_1_3_ii`), the
  minorization of the resolvent (`theorem_5_2_3_resolvent`), petite sets (`IsPetite`,
  `proposition_5_5_3`), sampling distributions (`IsSamplingDist`), aperiodicity and skeletons
  (`IsAperiodic`, `proposition_5_4_5_iii`) and the forward recurrence time chain
  (`fwdRecKernel`) are used. No Chapter 10 module depends on `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). Random walk
  (`randomWalkKernel`, `IsSpreadOut`, `convPow`), the scalar linear model (`ar1Kernel`) and the
  linear state space model (`lssMatrixKernel`) come from these modules.

Carried from the Chapter 5 project `PseudoAtoms` directly (286 theorems): the models and the §3.5
and §5.3 modules that `HarrisRecurrence` does not contain. The models are `ModelKernels` (19),
`ModelCountableModels` (9), `ModelQueues` (16), `ModelStorage` (18) and `ModelRenewal` (29); the
§3.5 modules are `SpecificKernels` (42), `Regeneration` (12), `PoissonCounts` (12),
`RenewalSkeletons` (53), `LadderChains` (25) and `GIG1Embedding` (37), which `PseudoAtoms` copied
from `TransitionProbabilities`; the §5.3 modules are `GIG1SmallSets` (7) and `RenewalSmallSets`
(7). They are identical to the copies in `PseudoAtoms` except for the namespace, with one
exception: `isProbabilityMeasure_convPow` of `SpecificKernels` is renamed
`isProbabilityMeasure_convPow_real`, since the carried `TChainModels` already has a theorem of
that name, and its two uses in `RenewalSkeletons` follow the rename. The ladder chain and the
GI/G/1 kernels (`ladderChainKernel`, `ladderChainKernel_translate`, `eq_3_40_zero`,
`eq_3_40_mid`, `eq_3_40_up`, `gig1Ladder`, `gig1Lambda`, `gig1LambdaStar`, `resEpoch`) and the
forward recurrence time `δ`-skeleton (`fwdSkelKernel`, `fwdSkelStep`, `fwdTimeCts`) are used. No
Chapter 10 module depends on `GIG1Embedding`, `GIG1SmallSets` or `RenewalSmallSets`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
