# Meyn and Tweedie, Chapter 9: Harris and Topological Recurrence, in Lean

This is the `StochasticStability/HarrisRecurrence` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 9 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 199–228. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 9 strengthens the recurrence of Chapter 8, an infinite expected number of visits, to an
almost surely infinite number of visits. With `Q(x, A) = P_x{Φ ∈ A i.o.}` (9.1), a set `A` is
Harris recurrent if `Q(x, A) = 1` for `x ∈ A`, and a ψ-irreducible chain is Harris if every set in
`B⁺(X)` is Harris recurrent. §9.1 shows that `L(x, A) ≡ 1` on `A` already makes `A` Harris
recurrent (Proposition 9.1.1), proves from the strong law that random walk on `ℤ` with non-zero
mean is transient (Proposition 9.1.2), shows that `D ⇝ A` gives `{Φ ∈ D i.o.} ⊆ {Φ ∈ A i.o.}`
almost surely (Theorem 9.1.3) and that a Harris chain has `Q(x, B) = 1` for every `x` and every
`B ∈ B⁺(X)` (Theorem 9.1.4), decomposes a recurrent chain into a maximal Harris set and a
transient ψ-null set (Theorems 9.1.5 and 9.0.1), passes the Harris property between a chain and
its skeletons (Theorem 9.1.6), and gives a hitting-time criterion and a drift criterion for Harris
recurrence (Proposition 9.1.7, Theorem 9.1.8). §9.2 introduces the event `{Φ → ∞}` that the path
visits every compact set only finitely often, shows that the paths of a T-chain converge to
infinity or return to the part of the space from which a given transient set is not reached
(Theorem 9.2.1), and proves that a ψ-irreducible T-chain is Harris if and only if it is
non-evanescent (Theorems 9.2.2 and 9.0.2). §9.3 classifies individual states through their
neighbourhoods: topologically recurrent and topologically Harris recurrent states (Proposition
9.3.1, Lemma 9.3.2), the solidarity of recurrence for T-chains (Theorem 9.3.3), conditions under
which topologically recurrent states are topologically Harris recurrent (Proposition 9.3.4), and
two decompositions of the space (Theorems 9.3.5 and 9.3.6). §9.4 gives a drift criterion for
non-evanescence with a coercive test function (Theorem 9.4.1), a converse for weak Feller chains
(Theorem 9.4.2), and applies the criterion to random walk on `ℝ` with mean zero and finite variance
(Lemmas 9.4.3–9.4.4, Proposition 9.4.5). §9.5 treats stochastic comparison (9.44), random walk on
`ℝ₊` and on `ℝ` with non-zero mean (Propositions 9.5.1 and 9.5.3), the scalar linear model
(Proposition 9.5.2), the transience of SETAR models in the exterior of the parameter space
(Proposition 9.5.4), and the increment analysis of chains on `ℝ₊` with bounded increments (Theorem
9.5.5) and with `2 + ε` moments (Theorem 9.5.6), with the `c/x` chain showing that the moment
condition cannot be dropped.

Every numbered result is formalised: Theorems 9.0.1–9.0.2, Propositions 9.1.1–9.1.2, Theorems
9.1.3–9.1.6, Proposition 9.1.7, Theorem 9.1.8, Theorems 9.2.1–9.2.2, Proposition 9.3.1, Lemma
9.3.2, Theorem 9.3.3, Proposition 9.3.4, Theorems 9.3.5–9.3.6, Theorems 9.4.1–9.4.2, Lemmas
9.4.3–9.4.4, Proposition 9.4.5, Propositions 9.5.1–9.5.4 and Theorems 9.5.5–9.5.6, together with
the claims the text makes about its examples. Theorem 9.5.6, which the book states without proof,
is proved. Six claims are false as printed. Each is refuted in Lean by a counterexample, and a
corrected statement is proved. The last claim of Theorem 9.3.6, that every state of the transient
part `N` is topologically transient, fails for a ν-irreducible T-chain on `ℕ∞ ⊕ ℕ`; every state of
`N` has an open neighbourhood `O` with `O ∩ N` uniformly transient, and the states of `N` with
`T(x*, H) = 0` are topologically transient. The step "hence `O ⇝ B`" of Lemma 9.3.2 needs
`a(0) = 0`; the lemma holds with `P_y(σ_B < ∞)` in place of `L(y, B)`. The proof of Proposition
9.5.2 asserts that the linear model is irreducible for Lebesgue measure on `ℝ`, which is false for
`|α| < 1`; the proposition holds as stated, with Lebesgue measure on `[−R/2, R/2]` as the
irreducibility measure. For the `c/x` chain after Theorem 9.5.6, the identity for `2xm(x) − v(x)`
should read `x(2xm(x) − v(x)) = (2 − 3c)x² − (2c + 1)x + c`, the product for `P_0(τ₀ > n)` stops
at `n − 1`, and the bound `E_x|W_x|^{2+ε} > x^{1+ε}` is false, although these moments are unbounded
in `x`, which is what the argument needs. Further points are corrected without a counterexample of
their own: Proposition 9.1.7 (i) needs `C ≠ ∅`; Proposition 9.1.2 holds for every `β ≠ 0`, not only
`β > 0`; Proposition 9.4.5 is about the walk on `ℝ`, not on `ℝ₊`; Lemma 9.4.4 holds with `lim sup`
in place of `lim`; the conclusion "transient" of Proposition 9.5.1 needs ψ-irreducibility; and
region (9.51) of Proposition 9.5.4 is proved pathwise, without (SETAR3), and the side conditions of
(9.48) and (9.49) are not needed. Countable generation of `B(X)` is assumed only for Theorems
9.0.1, 9.1.4–9.1.6 and 9.1.8 and Proposition 9.1.7 (i). The topological results of §§9.2–9.4 are
proved on locally compact, second-countable Hausdorff spaces with the Borel σ-algebra, and several
under weaker assumptions. In Theorem 9.5.5 the book's standing assumption is replaced by what the
proofs use: the sets `[0, c]` are petite for (i), and the tails `(c, ∞)` lie in `B⁺(X)` for (ii).
Theorem 9.5.6 assumes a maximal irreducibility measure `ψ`, petite sets `[0, c]` for (i), tails of
positive `ψ`-measure for (ii), the moment bound, and `v(x) ≥ v₀ > 0` for large `x`, without which
it fails. Lemma 9.4.3 assumes that both sides are integrable. The following are not formalised: the
examples (9.22) and (9.24), whose phenomenon, a topologically recurrent state of a T-chain that is
not topologically Harris recurrent, is shown for a ψ-irreducible chain by
`cex_not_isTopHarrisRecurrent`; the example with rational states after Theorem 9.4.2; and the
commentary of §9.6. See [corrections](docs/corrections.md). The library contains **1332
theorems**. Of these, 275 are in the Chapter 9 modules and 1057 in the modules carried from
Chapters 1–6 and 8.

Six results carry the chapter.

* **The drift supermartingale on path space** (`SupermartingaleDrift`). For a measurable
  `V : X → ℝ₊` with (V1) off a measurable set `C`, the killed process
  `Mₖ = V(Φₖ) 1{σ_C ≥ k}` (`killedV`) is a supermartingale for the natural filtration `𝓕ₖ^Φ`
  (`natFilt`, carried, a Mathlib `MeasureTheory.Filtration`) under `P_μ`, for every initial law
  `μ` with `∫ V dμ < ∞`; the statement uses Mathlib's `MeasureTheory.Supermartingale`
  (`supermartingale_killedV`). The step is the book's computation on p. 214,
  `∫_G M_{k+1} dP_μ ≤ ∫_G M_k dP_μ` for `G ∈ 𝓕ₖ^Φ` (`setLIntegral_killedVE_succ_le`), with
  `{σ_C ≥ k + 1} ∈ 𝓕ₖ^Φ` (`measurableSet_natFilt_avoidSet`). Mathlib's martingale convergence
  theorem (`MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`, applied to `−M`) gives an
  almost surely finite limit (`ae_tendsto_killedV`), so `V(Φₖ)` stays bounded on `{σ_C = ∞}`
  (`ae_bddAbove_of_avoid`). With a coercive `V` and a compact `C` this proves Theorem 9.4.1
  (`theorem_9_4_1`), and through it Propositions 9.4.5 and 9.5.2.
* **Theorem 9.1.3 by Lévy's upward theorem** (`HarrisProperties`). If `P_y(σ_A < ∞) ≥ δ > 0` for
  `y ∈ D`, then `{Φ ∈ D i.o.} ⊆ {Φ ∈ A i.o.}` `P_μ`-almost surely, for every initial law `μ`
  (`theorem_9_1_3_ae`). The proof uses the events `Hₖ = {Φⱼ ∉ A for all j ≥ k}` (`noVisitFrom`):
  by the Markov property `P_μ(Hₙ | 𝓕ₙ) = P_{Φₙ}(σ_A = ∞) ≤ 1 − δ` when `Φₙ ∈ D`, while
  `P_μ(Hₖ | 𝓕ₙ) ≤ P_μ(Hₙ | 𝓕ₙ)` for `n ≥ k` and `P_μ(Hₖ | 𝓕ₙ) → 1_{Hₖ}` by Lévy's upward
  theorem (Mathlib's `MeasureTheory.Integrable.tendsto_ae_condExp`). So a path in `D` infinitely
  often lies in no `Hₖ`, and a path in no `Hₖ` is in `A` infinitely often
  (`exists_noVisitFrom_of_notMem_ioSet`). This is the book's argument (9.7)–(9.10) with the
  complementary events. It gives `Q(y, D) ≤ Q(y, A)` (`theorem_9_1_3_i`; with the book's
  hypothesis `D ⇝ A`, `theorem_9_1_3_i_unifAccessible`), `Q ≡ 1` when `X ⇝ A`
  (`theorem_9_1_3_ii`), and, through a cover by petite sets, Theorem 9.1.4 (`theorem_9_1_4`,
  `IsPetite.unifAccessible`).
* **The Harris decomposition** (`HarrisDecomposition`). For a recurrent chain and a petite
  `C ∈ B⁺(X)` (`exists_petite_pos`), the set `H = {Q(·, C) = 1}` is absorbing
  (`prob_eq_one_of_lintegral_eq_one`) and maximal absorbing (`harrisInfty`). It is non-empty:
  otherwise `{x ∈ C : L(x, C) < 1}` is charged by `ψ` (`psi_pos_hitProb_lt_one`), and Proposition
  8.3.1 (iii) contradicts recurrence. Theorem 9.1.3 makes the chain restricted to `H` Harris, and
  `Hᶜ` is ψ-null and transient by Propositions 4.2.3 and 8.3.7 (`theorem_9_1_5`,
  `IsMaximalHarrisSet`). Theorem 9.0.1 follows (`theorem_9_0_1`), and so do Harris recurrence of
  recurrent irreducible chains on a countable space (`isHarris_of_countable`), Proposition 9.1.7
  (`proposition_9_1_7_i`, `proposition_9_1_7_ii`), Theorem 9.1.8 (`theorem_9_1_8`) and the
  skeleton theorem (`theorem_9_1_6`), whose direction from a skeleton to the chain needs no
  aperiodicity (`isHarris_of_skeleton`).
* **Non-evanescence** (`NonEvanescence`). `{Φ → ∞}` (`tendsToInfty`) is the event that every
  compact set is visited only finitely often; for a compact exhaustion `Kₙ` it is
  `⋂ₙ {Φ ∈ Kₙ i.o.}ᶜ` (`tendsToInfty_eq_iInter`). For a T-chain and a transient `A`,
  `P_x({Φ → ∞} ∪ {Φ ∈ A⁰ i.o.}) = 1` (`theorem_9_2_1`), which is stronger than the book's (9.12)
  (`theorem_9_2_1_enters`). For a ψ-irreducible T-chain, `X = H ∪ N` with `H` empty or a maximal
  Harris set, `N` transient, and `L(x, H) = 1 − P_x{Φ → ∞}` (9.14) (`theorem_9_2_2`); the chain is
  recurrent iff `P_x{Φ → ∞} < 1` for some `x` (`theorem_9_2_2_i`) and Harris iff it is
  non-evanescent (`theorem_9_2_2_ii`, `theorem_9_0_2`). Where the book's proof uses
  `L(x, B) ≥ K_a(x, B)`, which needs `a(0) = 0`, the proof here uses
  `P_x(σ_B < ∞) ≥ K_a(x, B)` (`sampledKernel_le_hitProbZero`) and the first-hitting form of
  Theorem 9.1.3.
* **Theorem 9.5.6** (`IncrementAnalysis`), which the book states without proof. For a chain on
  `ℝ₊` with `sup_x E_x|W_x|^{2+ε} ≤ B` (`HasMomentBound`) and `v(x) ≥ v₀ > 0` for large `x`:
  (ii) if `m(x) ≥ θv(x)/2x` with `θ > 1`, the chain is transient (`theorem_9_5_6_ii`). The test
  function is `V(x) = 1 − (1 + x)^{−α}` with `α = min((θ − 1)/2, ε/2)`; (9.67) is expanded on
  `{|W_x| ≤ η(1 + x)}`, and the tail is controlled by `E[W²; |W| > s] ≤ B/s^ε` and
  `P(|W| > s) ≤ B/s^{2+ε}` (`setIntegral_sq_tail_le`, `measure_tail_le`,
  `integral_rpow_neg_le_of_moment`). (i) If `m(x) ≤ v(x)/2x + Kx^{−1−δ}` with `δ > 0`, the chain is
  Harris recurrent (`theorem_9_5_6_i`). The test function is the book's suggestion
  `V(x) = log log(x + e)`; both logarithms are expanded to second order (`loglog_step_le`,
  `integral_loglog_le`), and the second-order term `≈ v/(2x² s²)`, `s = log(x + e)`, dominates the
  remaining terms.
* **The SETAR classification** (`SETAR`). Proposition 9.5.4 is proved in all six exterior regions
  (9.46)–(9.51) (`proposition_9_5_4_46`, `proposition_9_5_4_47`, `proposition_9_5_4_48`,
  `proposition_9_5_4_49`, `proposition_9_5_4_50`, `proposition_9_5_4_51`; together
  `proposition_9_5_4`) by one pathwise argument on the noise path space
  (`pathKernel_recursion`). Beyond `ρ = 1 + Σ|rᵢ|` (`setarBound`) the chain follows one of the two
  end linear models; a linear lower recursion gives `gₙ ≥ Aₙ(x − Σ_{k ≤ n} c_k/A_k)`
  (`escape_of_lower_recursion`); the correction terms are almost surely bounded, by first moments
  or by the strong law (`ae_bdd_weighted_sum`, `ae_bdd_partialSum_of_neg`); one level bounds them
  on a set of noise paths of positive probability (`exists_measure_pos_forall_le`); so
  `L(x, [−ρ, ρ]) < 1` (`hitProb_recursion_lt_one`), and Theorem 8.3.6 gives transience
  (`setar_transient_of_escape`). In region (9.51), `θ(1)θ(M) = 1`, the two-step chain is the
  random walk `X₂ₙ = x + Tₙ` with drift `θ(1)(φ(M) + θ(M)φ(1)) > 0`. It is controlled by a strong
  law for the two-step blocks `(W₂ᵢ₊₁, W₂ᵢ₊₂)`, which are pairwise independent and identically
  distributed (`ae_tendsto_blockSum`, from Mathlib's `ProbabilityTheory.strong_law_ae`), and the
  odd steps stay far to the left. Only first moments are used, so (SETAR3) is not needed.

The library covers the chapter as follows.

* **Harris recurrence** (§9.0, pp. 199–200). The event `{Φ ∈ A i.o.}`, `Q(x, A)` and (9.2), the
  strong Markov property for shift-invariant events, Harris recurrent sets and Harris chains, and
  Theorems 9.0.1 and 9.0.2.
* **Harris properties of sets** (§9.1.1). Proposition 9.1.1, Proposition 9.1.2 and (9.4)–(9.5),
  Theorem 9.1.3 and (9.6)–(9.10), Theorem 9.1.4.
* **Harris recurrent chains** (§9.1.2). A recurrent chain that is not Harris, `D^∞`, maximal
  Harris sets, Theorem 9.1.5, and Theorem 9.1.6 for skeletons.
* **A hitting time criterion** (§9.1.3). Proposition 9.1.7, with the correction to (i), and Theorem
  9.1.8.
* **Evanescence and transience** (§9.2.1). The event `{Φ → ∞}`, non-evanescence, Theorem 9.2.1 and
  (9.12)–(9.13).
* **Non-evanescence and recurrence** (§9.2.2). Theorem 9.2.2 and (9.14).
* **Topological recurrence of states** (§9.3.1). Topologically recurrent, transient and Harris
  recurrent states, Proposition 9.3.1 and (9.15)–(9.21).
* **Solidarity of recurrence for T-chains** (§9.3.2). Lemma 9.3.2, refuted as printed and corrected;
  Theorem 9.3.3; Proposition 9.3.4 and (9.25)–(9.29); Theorem 9.3.5; Theorem 9.3.6, refuted as
  printed and corrected; the example with `R ⊊ H`.
* **A drift criterion for non-evanescence** (§9.4.1). Coercive functions, Theorem 9.4.1 and (9.30),
  the example on p. 214.
* **A converse for Feller chains** (§9.4.2). Theorem 9.4.2 and (9.31)–(9.39).
* **Non-evanescence of random walk** (§9.4.3). Lemmas 9.4.3 and 9.4.4, (9.40)–(9.41), and
  Proposition 9.4.5.
* **Stochastic comparison and the linear model** (§9.5.1). (9.44) in both directions, Proposition
  9.5.1, and Proposition 9.5.2 in three forms, with the irreducibility claim of its proof refuted.
* **Random walk on `ℝ` and SETAR models** (§9.5.2). Proposition 9.5.3 and the evanescence of the
  walk, the exterior regions (9.46)–(9.51), and Proposition 9.5.4.
* **General chains with bounded increments** (§9.5.3). `m(x)`, `v(x)`, (9.57)–(9.58), Theorem
  9.5.5 and (9.59)–(9.67), Theorem 9.5.6 and (9.68)–(9.69), and the `c/x` chain with its three
  corrections.

All names are in the namespace `MeynTweedie.HarrisRecurrence`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [HarrisDefinitions](HarrisRecurrence/HarrisDefinitions.lean) | 29 | §§9.0–9.1: the event `{Φ ∈ A i.o.}`, `Q(x, A)` (9.1), `Q ≤ L`, shift-invariant events and the strong Markov property for them, (9.2), occupation times along the first return, Harris recurrent sets and Harris chains |
| [HarrisProperties](HarrisRecurrence/HarrisProperties.lean) | 15 | §9.1.1: Proposition 9.1.1, petite sets reach `B⁺(X)` uniformly, Theorem 9.1.3 through Lévy's upward theorem, Theorem 9.1.4, Harris chains are recurrent |
| [HarrisDecomposition](HarrisRecurrence/HarrisDecomposition.lean) | 18 | §§9.0, 9.1.2–9.1.3: escape to absorbing sets, `D^∞`, maximal Harris sets, Theorems 9.1.5 and 9.0.1, countable spaces, Proposition 9.1.7 and the correction to (i), Theorem 9.1.8, Theorem 9.1.6 for skeletons |
| [SupermartingaleDrift](HarrisRecurrence/SupermartingaleDrift.lean) | 14 | §9.4.1: the killed drift process `V(Φₖ) 1{σ_C ≥ k}`, the supermartingale inequality of p. 214, Mathlib's `Supermartingale` for `natFilt`, almost sure convergence, boundedness of `V(Φₖ)` on `{σ_C = ∞}` |
| [NonEvanescence](HarrisRecurrence/NonEvanescence.lean) | 21 | §§9.0, 9.2: the event `{Φ → ∞}`, non-evanescence, covers of `Ā` for transient `A`, the corrected (5.45), Theorems 9.2.1, 9.2.2 and 9.0.2, (9.14) |
| [TopologicalRecurrence](HarrisRecurrence/TopologicalRecurrence.lean) | 21 | §9.3: topologically recurrent, transient and Harris recurrent states, Proposition 9.3.1, Lemma 9.3.2 and its counterexample, Theorem 9.3.3, Proposition 9.3.4, Theorem 9.3.5, Theorem 9.3.6 corrected |
| [TopologicalExamples](HarrisRecurrence/TopologicalExamples.lean) | 33 | §§9.1.2, 9.3: a ν-irreducible T-chain on `ℕ∞ ⊕ ℕ` with a topologically recurrent state that is not topologically Harris recurrent, the counterexample to Theorem 9.3.6, a recurrent chain that is not Harris, the example after Theorem 9.3.6 |
| [DriftHarris](HarrisRecurrence/DriftHarris.lean) | 29 | §9.4: coercive functions, Theorem 9.4.1, Harris recurrence from a coercive drift, the example on p. 214, Lemma 9.4.3, Theorem 9.4.2, Proposition 9.4.5, Lemma 9.4.4 |
| [StochasticComparison](HarrisRecurrence/StochasticComparison.lean) | 32 | §§9.1.1, 9.5: the path law of a random recursion, the strong law along the path, Propositions 9.1.2, 9.5.3 and 9.5.1, a transience criterion through `Q`, (9.44), Proposition 9.5.2 and the refutation of its irreducibility claim, Theorem 9.5.5 |
| [LinearModelHarris](HarrisRecurrence/LinearModelHarris.lean) | 7 | §9.5.1: the linear model with a symmetric noise density on `[−R, R]` is a T-chain, irreducible for `\|α\| ≤ 1`, and Proposition 9.5.2 under the book's hypotheses |
| [CxChain](HarrisRecurrence/CxChain.lean) | 16 | §9.5.3: the `c/x` chain, its tail probabilities and recurrence, `m(x)` and `v(x)`, (9.69), the moments, and the three corrections |
| [IncrementAnalysis](HarrisRecurrence/IncrementAnalysis.lean) | 15 | §9.5.3: the moment bound, tail estimates, Theorem 9.5.6 (ii) with `1 − (1 + x)^{−α}`, Theorem 9.5.6 (i) with `log log(x + e)` |
| [SETAR](HarrisRecurrence/SETAR.lean) | 25 | §9.5.2: escape from linear lower recursions, almost sure bounds on noise sums, the strong law for two-step blocks, the SETAR model beyond its thresholds, Proposition 9.5.4 in each region (9.46)–(9.51) |

Carried from the Chapter 8 project `TransienceRecurrence` (1057 theorems): every module of that
project, identical to the copies there except for the namespace. No Chapter 9 module depends,
directly or through other modules, on `RandomWalkIntegers`, `RandomWalkMeanZero` or
`SkipFreeWalk`. Its own Chapter 8 modules (220 theorems): `UniformTransience` (46),
`Decompositions` (8), `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23),
`CountableClassification` (18), `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16),
`SkipFreeWalk` (15), `RandomWalkMeanZero` (5). Uniformly transient, recurrent and transient sets
and chains (`IsUniformlyTransient`, `IsRecurrentSet`, `IsTransientSet`, `IsRecurrentChain`,
`IsTransientChain`), transient states (`IsTransientState`), truncated occupation times
(`occTimeN`), the first hitting probability `P_x(σ_C < ∞)` (`hitProbZero`), the drift (`drift`),
the dichotomy (`theorem_8_3_4`), Proposition 8.3.1 (iii) (`proposition_8_3_1_iii`), Proposition
8.3.2 (`proposition_8_3_2`), Proposition 8.3.7 (`proposition_8_3_7`), the transience criteria
`theorem_8_3_6_ii` and `theorem_8_4_2`, `lemma_8_4_3_hitProb`, skeletons (`theorem_8_2_6_ii`) and
the bound `log_one_add_le` are used.

Carried in turn by `TransienceRecurrence` from the Chapter 6 project `TopologyContinuity` (837
theorems; see those projects' READMEs for how they differ from the originals):

* Its own Chapter 6 modules (130 theorems): `FellerChains` (40), `TChains` (14), `EChains` (16),
  `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16), `TChainModels` (10),
  `EChainsStability` (12). Weak and strong Feller chains (`IsWeakFeller`, `IsStrongFeller`),
  reachable points (`IsReachable`), the tail probabilities `P_x(τ_A ≥ n)` (`tailProb`), T-chains
  and continuous components (`IsTChain`, `IsContinuousComponent`) and the irreducibility of SETAR
  models (`proposition_6_3_6`) are used. No Chapter 9 module depends on `CompactPetite`,
  `EChains`, `EChainsStability` or `LinearTChains`.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` and `P_μ`
  (`pathKernel`, `pathMeasure`), the natural filtration (`natFilt`), the shift (`shift`), the
  strong Markov property (`strong_markov_lintegral`), stopped states (`stoppedState`), hitting and
  return times and probabilities (`firstReturn`, `firstHit`, `returnTimeK`, `hitProb`), the
  potential kernels (`potKernel`, `tabooPotKernel`), the sampled kernels (`sampledKernel`) and
  occupation times (`occTime`) are used throughout. No Chapter 9 module depends on `StateSpaces`
  or `SpecificMatrices`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Absorbing sets (`IsAbsorbing`), irreducibility
  (`IsIrreducibleChain`, `IsPhiIrreducible`, `IsMaximalIrreducibility`), full absorbing sets
  (`proposition_4_2_3_i`, `proposition_4_2_3_ii`), uniform accessibility (`UnifAccessible`),
  and the set `A⁰` (`noHitSet`) are used. No Chapter 9 module
  depends on `CountableIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Petite sets (`IsPetite`),
  sampling distributions and sampled accessibility (`IsSamplingDist`, `SampledAccessible`),
  Proposition 5.5.5 (`proposition_5_5_5_i`, `proposition_5_5_5_ii`,
  `proposition_5_5_5_iii_cover`), aperiodicity (`IsAperiodic`) and the counterexample to Lemma
  5.5.1 (`lemma_5_5_1_counterexample`) are used. No Chapter 9 module depends on `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). The random walks
  on a group and on `ℝ₊` (`randomWalkKernel`, `halfLineWalkKernel`), the scalar linear model
  (`ar1Kernel`), the SETAR model (`setarKernel`, `setarStep`) and the orbits of a random recursion
  (`orbit`) come from these modules.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
