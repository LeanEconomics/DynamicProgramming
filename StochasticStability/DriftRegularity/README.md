# Meyn and Tweedie, Chapter 11: Drift and Regularity, in Lean

This is the `StochasticStability/DriftRegularity` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 11 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 256–287. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 11 gives two descriptions of positive recurrence that are equivalent to the finiteness of
the invariant measure. A set `C` is regular if `sup_{x ∈ C} E_x[τ_B] < ∞` for every `B ∈ B⁺(X)`
(11.1), and the chain is regular if `X` is a countable union of regular sets; the drift condition
(V2) is `ΔV ≤ −1 + b 1_C` (11.17). For a Harris recurrent chain, `π(X) < ∞` iff some petite set
has bounded mean return times (11.3) iff (V2) holds for a petite set (Theorem 11.0.1). §11.1 shows
that positivity and regularity agree on a countable space (Proposition 11.1.1), that a positive
chain with an accessible atom `α` is regular on the full absorbing set `{x : E_x[τ_α] < ∞}`
(Theorem 11.1.2), that this set can miss every state but one (11.12), and that every positive chain
is regular on a full absorbing set (Proposition 11.1.3, Theorem 11.1.4). §11.2 treats the
deterministic system (DS1) and its drift condition (DS2) (Theorem 11.2.1). §11.3 proves Dynkin's
formula (Theorem 11.3.1) and the comparison inequalities (Propositions 11.3.2–11.3.3), Foster's
criterion (Theorem 11.3.4), the identities for the kernel `G_A` and the function
`V_A = 1 + E_·[σ_A]` (Theorem 11.3.5), and the characterisations of regular sets, regular measures
and regular chains by drift and by mean hitting times (Lemmas 11.3.6–11.3.7, Proposition 11.3.8,
Lemmas 11.3.9–11.3.10, Theorems 11.3.11–11.3.12, Proposition 11.3.13, Theorems 11.3.14–11.3.15).
§11.4 applies the criteria to random walk on a half line (Proposition 11.4.1), the forward
recurrence time chain (11.28)–(11.29), the simple linear model (Proposition 11.4.2), the GI/G/1
queue with re-entry (Propositions 11.4.3–11.4.4) and the SETAR model in the interior of its
parameter space (Proposition 11.4.5). §11.5 gives a drift criterion for non-positivity (Theorems
11.5.1–11.5.2) and applies it to random walk on a half line (Proposition 11.5.3) and to the SETAR
model on the margins of its parameter space, where the chain is recurrent but not positive
(Propositions 11.5.4–11.5.5).

Every numbered result is formalised: Theorem 11.0.1, Propositions 11.1.1 and 11.1.3, Theorems
11.1.2 and 11.1.4, Theorem 11.2.1, Theorem 11.3.1, Propositions 11.3.2–11.3.3, Theorems
11.3.4–11.3.5, Lemmas 11.3.6–11.3.7, Proposition 11.3.8, Lemmas 11.3.9–11.3.10, Theorems
11.3.11–11.3.12, Proposition 11.3.13, Theorems 11.3.14–11.3.15, Propositions 11.4.1–11.4.5,
Theorems 11.5.1–11.5.2 and Propositions 11.5.3–11.5.5, together with the claims the text makes
about its examples. Theorem 11.1.4 is proved without aperiodicity. Proposition 11.5.4 is proved on
all five margins (11.45)–(11.49), including the two the book leaves to symmetry, and Proposition
11.5.5 on all five, although the book proves it only for (11.49). Seven claims are false as
printed. Six are refuted in Lean in the Chapter 11 modules, and for each a corrected statement is
proved. (11.24) should read `P V_A(x) = E_x[τ_A]` for `x ∈ A`, not `E_x[τ_A] − 1`: for `A = X`,
`P V_A = 1` while `E_x[τ_A] − 1 = 0`. Theorem 11.3.14 needs `C ≠ ∅`: `∅` is petite with
`sup_{x ∈ ∅} E_x[τ_∅] = 0` but is not in `B⁺(X)`. The final claim of Theorem 11.0.1, that every
sublevel set of `V` satisfies (11.3), needs the sublevel set to be in `B⁺(X)`: a positive Harris
chain on two states has a solution of (V2) whose sublevel set `{true}` has
`E_true[τ_{true}] = ∞`. In the example (11.12) the condition for non-regularity is
`Σ_j Π_{k ≤ j} (1 − β_k) = ∞`; the book's `Σ_j Π_{k ≤ j} β_k = ∞` holds for `β ≡ 1`, where the
chain is regular. The inequality `E_x[τ_x] ≥ ₓPⁿ(x, y) [E_y[τ_x] + n]` in the proof of Proposition
11.1.1, written "for any fixed states `x, y`", fails for `y = x`. In the proof of Proposition 11.5.4
the slope chosen for the region (11.45) with `θ(1) < 0`, `a = −bθ(M)`, is negative, and the
identity the proof uses holds iff `a = −b/θ(1)`. The seventh claim is Theorem 11.0.1 (ii), which
needs `C ≠ ∅` for the same reason as Theorem 10.0.1: Chapter 10's `theorem_10_0_1_counterexample`
(carried) is a recurrent forward recurrence time chain with an infinite invariant measure for which
`∅` satisfies (11.3). That chain is Harris by `isHarris_of_countable` and
`fwdRec_isIrreducibleChain` (carried), a step that is not stated as a theorem; the corrected
statement, with `C ≠ ∅`, is proved. One further point is corrected without a counterexample: the
proof of Proposition 11.5.5 swaps the roles of `φ` and `θ`. Test functions are measurable, which
the book uses implicitly, and the constant `b` of (V2) is finite (`b ≠ ∞`), as in the book.
Countable generation of `B(X)` is
assumed where small sets are needed (Theorem 5.2.2): for Theorems 11.0.1, 11.1.2, 11.1.4 and
11.5.2, (11.7), Propositions 11.1.3, 11.3.8 and 11.3.13, the positivity statement of Theorem
11.3.4, and Theorems 11.3.11, 11.3.12 (i), 11.3.14 and 11.3.15. Dynkin's formula
is stated for bounded stopping times and integrable `Z`, and Proposition 11.3.3 for processes
`Z_k = z_k(Φ_k)`. Proposition 11.1.3 takes a minorization on a set of `B⁺(X)`. Theorem 11.2.1 (ii)
and (iii) are stated on a locally compact Hausdorff space. Random walk on a half line takes
`E|W| < ∞` and ψ-irreducibility; for the linear model of Proposition 11.4.2 the ψ-irreducibility
and the petiteness of compact sets are hypotheses. The GI/G/1 queue with re-entry takes
`0 < r ≤ 1`, finite means of the interarrival and service laws, and, for Proposition 11.4.4,
`E S > 0`. In the SETAR results the noise is integrable with mean zero, (SETAR3) is the finiteness
of the second moments in the two end regimes, and non-positivity uses only (SETAR1)–(SETAR2). The
following are not formalised: the identification of the re-entry recursion with a queue built on
one probability space from global sequences of interarrival times, service times and re-entry
decisions; the book's monotonicity remark `P_x(Φ_m = [0]) ≤ P_y(Φ_m = [0])` for `x ≥ y`, which the
proof here does not need; the commentary of §11.6; and the informal remarks of the text. See
[corrections](docs/corrections.md). The library contains **1788 theorems**. Of these, 292 are in
the Chapter 11 modules and 1496 in the modules carried from Chapters 1–6 and 8–10.

Five results carry the chapter. The first is the interface that Chapters 14–16 use.

* **Dynkin's formula and the comparison theorem** (`Comparison`). For a random time `τ` with
  values in `ℕ ∪ {∞}`, `sumBefore τ F` is `Σ_{k<τ} F_k`, and
  `∫ Σ_{k<τ} F_k = Σ_k ∫_{k<τ} F_k` (`lintegral_sumBefore`). The comparison theorem on an
  arbitrary measure space (`comparison_lintegral`) is stated entirely in `[0, ∞]`: if
  `∫_{n<τ} Z_{n+1} + ∫_{n<τ} F_n ≤ ∫_{n<τ} Z_n + ∫_{n<τ} S_n` for every `n`, then
  `∫ Σ_{k<τ} F_k ≤ ∫ Z_0 + ∫ Σ_{k<τ} S_k`. No integrability is assumed, and no truncation of `τ`
  or of `Z` (the book's `τⁿ`) is used. Proposition 11.3.2 follows for every stopping time
  (`proposition_11_3_2`, with the drift as an inequality of integrals over the events of `𝓕_k`;
  `proposition_11_3_2_condExp` takes it as an inequality of conditional expectations), and for a
  Markov chain `comparison_theorem` and `comparison_theorem_pathKernel` give
  `E_x[Σ_{k<τ} f(Φ_k)] ≤ V(x) + E_x[Σ_{k<τ} s(Φ_k)]` whenever `PV + f ≤ V + s` on a set the chain
  does not leave before `τ`. Dynkin's formula (`theorem_11_3_1`) is proved for an adapted process
  of integrable real random variables and a bounded stopping time, through Mathlib's Doob
  decomposition (`martingalePart`, `predictablePart`) and its optional stopping theorem.
  Proposition 11.3.3 (`proposition_11_3_3`) bounds `E_x[Σ_{i<τ_A} ε_i(Φ_i)]` by `z_0(x)` off `A`
  and by `ε_0(x) + c P z_0(x)` everywhere, and Lemma 11.3.10 (`lemma_11_3_10`) moves a sampled
  kernel inside a sum up to any stopping time.
* **Foster's criterion** (`FosterCriterion`, `RegularSets`). `DriftV2 P V b C` is (V2),
  `PV + 1 ≤ V + b 1_C` for `V : X → [0, ∞]`; it is the book's `ΔV ≤ −1 + b 1_C` for the
  extended-valued drift of Chapter 8 (`driftV2_iff_drift`). Under (V2), `E_x[τ_C] ≤ V(x) + b 1_C(x)`
  (Theorem 11.3.4, `theorem_11_3_4`); if `C` is petite, `b < ∞` and `V` is finite everywhere and
  bounded on `C`, the chain is positive Harris (`theorem_11_3_4_positiveHarris`). Conversely, the
  function `V_C = 1 + E_·[σ_C]` (`regV`) has `P V_C = V_C − 1` off `C` and `P V_C = E_·[τ_C]` on
  `C` (`theorem_11_3_5_ii`), so bounded mean return times on `C` give a solution of (V2)
  (`regV_drift`), and `E_·[σ_A]` is the minimal solution of `PV ≤ V − 1` off `A`
  (`theorem_11_3_5_iii`). Under (V2) for a petite set, `E_x[τ_B] ≤ V(x) + c(B)` for every
  `B ∈ B⁺(X)` (`theorem_11_3_11_i`), so every set on which `V` is bounded is regular
  (`theorem_11_3_11_i_regular`). Regular sets are petite (`proposition_11_3_8`); a set is petite,
  non-empty and has bounded mean return times iff it is regular and in `B⁺(X)`
  (`theorem_11_3_14`); and the chain is regular iff (V2) holds for a petite set and a finite `V`,
  iff some petite `C` has `E_x[τ_C]` finite everywhere and bounded on `C` (`theorem_11_3_15`).
  Theorem 11.0.1 (`theorem_11_0_1`): for a Harris recurrent chain with a nonzero invariant measure
  `π`, `π(X) < ∞` iff some non-empty petite set satisfies (11.3), iff (V2) holds for a petite set
  and a `V` finite at one state; under (V2) the chain is regular on the full absorbing set
  `{V < ∞}` (`theorem_11_0_1_sublevel`).
* **Positive chains are regular on a full absorbing set** (`RegularityConverse`). Theorem 11.1.4
  (`theorem_11_1_4`): a ψ-irreducible chain is positive iff it is regular on a full absorbing set.
  The book proves it through an `m`-skeleton with a Nummelin splitting (Proposition 5.4.5), which
  needs the chain to be aperiodic, while the theorem assumes only ψ-irreducibility; the book also
  does not say why the absorbing set of the skeleton is absorbing for `Φ`. Here the proof uses the
  lazy chain `K = ½ (I + P)` (`lazyKernel`), the sampled chain with weights `½ δ₀ + ½ δ₁`. Its
  powers satisfy `2⁻ⁿ Σ_{j ≤ n} Pʲ ≤ Kⁿ ≤ Σ_{j ≤ n} Pʲ` (`lazy_pow_ge`, `lazy_pow_le`), so every
  skeleton `Kᵐ` has the same maximal irreducibility measure as `P`
  (`isMaximalIrreducibility_lazy_pow`) and is positive when `P` is (`isPositive_lazy_pow`). For a
  `ν_M`-small set `C ∈ B⁺(X)` with `ν_M(C) > 0` (Theorem 5.2.2), the skeleton `Kᴹ` has a
  minorization on `C`, so Proposition 11.1.3 gives a regular set for `Kᴹ`; and
  `E_x[τ_B] ≤ E^K_x[τ_B] ≤ M E^{Kᴹ}_x[τ_B]` (`meanReturnTime_le_lazy`, by the minimality in
  Theorem 11.3.5 (iii), and `meanReturnTime_le_skeleton`, from `τ_B ≤ M τ_B^{(M)}`) makes it
  regular for `P` (`exists_regularSet_of_isPositive`). Proposition 11.3.13 then supplies the full
  absorbing set. Proposition 11.1.3 (`proposition_11_1_3`) itself goes through the split chain:
  the split atom is regular by Kac's theorem and Theorem 11.3.14, and
  `E_x[τ_B] ≤ Ě_{x₀}[τ_{B̌}] + Ě_{x₁}[τ_{B̌}]` (`meanReturnTime_le_split`) transfers regular sets
  back to `Φ` (`exists_regular_of_minorization`).
* **The GI/G/1 queue with re-entry** (`GIG1Reentry`). The chain `Φₙ = (Nₙ, Rₙ)` on `ℤ₊ × ℝ₊` is
  built as a random recursion. Inside one interarrival interval the queue is followed event by
  event on configurations `(C, ρ, t, β)` (`QConfig`, `cstep`) until the system empties or the
  service in progress outlasts the interval (`QConfig.IsFinal`); the innovations of one interval
  (`QNoise`) are the interarrival time, a service time for an arrival that finds the server free,
  and i.i.d. pairs of service times and re-entry decisions, with law `gig1rNoise G H r`. The step
  `gig1rStep` reads `Φₙ₊₁` off the first final configuration, `gig1rKernel G H r` is the kernel,
  and a recursion driven by i.i.d. innovations independent of `Φ₀` is a Markov chain with this
  kernel (`gig1r_isMarkovChain`). Every interval ends almost surely when services are not
  identically zero (`gig1rNoise_not_final`). Proposition 11.4.3 (`proposition_11_4_3`): under the
  load condition `E S / r < E T` the chain is `δ_{[0]}`-irreducible, strongly aperiodic and
  aperiodic, and every compact set is petite; the book's sketch of (11.33) is made precise with the
  potential `R + N a` (`qpot`), which a good interval (`goodNoise`) lowers by more than `δ` unless
  it empties the queue (`good_step`), so that `Pᵏ⁺¹(x, [0])` has a positive lower bound uniform on
  compact sets (`gig1r_reach_zero`). Proposition 11.4.4 (`proposition_11_4_4`): with `E S > 0`, the
  expected work `V(x) = E_x[W₀]` (`qworkV`), scaled by a constant, satisfies (11.34) with `k = 1`;
  the chain is regular and positive Harris. The proof rests on work conservation in one interval,
  `E_x[V(Φ₁)] + E[busy time] ≤ V(x) + m/r` (`lintegral_qworkV_add_busy`), and on the server being
  busy for almost the whole interval off a compact set (`gig1rBusy_ge`, `gig1r_drift`).
* **The SETAR model on the margins** (`SetarMarginRecurrence`, `SetarNullMargins`,
  `DriftExamples`). Proposition 11.5.4 (`proposition_11_5_4`): under (SETAR1)–(SETAR3) the SETAR
  model is Harris recurrent, and hence recurrent, on each margin (11.45)–(11.49). The test function
  is `log max(u + ax, v − bx)` (`marginL`), the book's (11.50) with the two pieces joined by a
  maximum, and one second-order bound for `log` (`log_hinge_drift`) replaces Lemmas 8.5.2, 8.5.3,
  9.4.3 and 9.4.4; the drift at each end (`marginL_right_end`, `marginL_left_end`) gives (V1) off a
  compact interval and Harris recurrence by Theorem 9.1.8 (`setar_harris_of_ends`). Proposition
  11.5.5: the chain is non-positive on every margin (`proposition_11_5_5_all`). The book proves only
  the case `θ(1) < 0`, `θ(1)θ(M) = 1`, `φ(M) + θ(M)φ(1) ≤ 0`, which contains (11.49)
  (`proposition_11_5_5`, with the kinked test function `max(x + c, d − bx)`, `kinkV`), and states
  the other four without proof; here they follow from a unit-slope end
  (`setar_null_of_top_unit`, `setar_null_of_bot_unit`, `proposition_11_5_5_margins`), through
  versions of Theorems 11.5.1–11.5.2 that need the mean increments bounded only off `C`
  (`theorem_11_5_1_off`, `theorem_11_5_2_off`). With Proposition 11.4.5 (`proposition_11_4_5`) in
  the interior (11.36)–(11.40), where the region (11.40) is handled in one step rather than through
  the two-step kernel, this completes the classification of §§11.4.3 and 11.5.2.

The library covers the chapter as follows.

* **Drift and regularity** (Chapter 11 introduction, pp. 256–257). Regular sets and chains (11.1),
  the mean drift (11.2), Theorem 11.0.1 and (11.3)–(11.4) with the corrections to (ii) and to its
  final claim, and the reverse drift (11.5)–(11.6).
* **Regular chains** (§11.1). Proposition 11.1.1 and the corrected inequality of its proof, (11.7),
  Theorem 11.1.2 and (11.8)–(11.11), the example (11.12) with the corrected condition, Proposition
  11.1.3 and (11.13)–(11.14), Theorem 11.1.4 and (11.15).
* **Deterministic models** (§11.2). (DS1), (11.16), recurrence and ultimate boundedness, (DS2),
  Theorem 11.2.1.
* **Mean drift and Dynkin's formula** (§11.3.1). (V2) and (11.17)–(11.19), (11.20), Theorem 11.3.1,
  Propositions 11.3.2–11.3.3, Theorem 11.3.4.
* **Hitting times and test functions** (§11.3.2). (11.21)–(11.22), Theorem 11.3.5 and (11.23)–(11.25)
  with the correction to (11.24), Lemmas 11.3.6–11.3.7, Proposition 11.3.8.
* **Regularity, drifts and petite sets** (§11.3.3). Lemma 11.3.9 and (11.26), Lemma 11.3.10,
  Theorem 11.3.11 and (11.27), regular measures and Theorem 11.3.12, Proposition 11.3.13, Theorem
  11.3.14 with the correction for `C = ∅`, Theorem 11.3.15.
* **Straightforward applications** (§11.4.1). Proposition 11.4.1, the forward recurrence time chain
  and (11.28)–(11.29), Proposition 11.4.2 and (11.30)–(11.31).
* **The GI/G/1 queue with re-entry** (§11.4.2). The chain, (11.32)–(11.33), Proposition 11.4.3,
  the expected work, (11.34)–(11.35) in expectation, Proposition 11.4.4.
* **The SETAR model in the interior** (§11.4.3). (11.36)–(11.41), Proposition 11.4.5.
* **A drift criterion for non-positivity** (§11.5.1). Theorem 11.5.1 and (11.42)–(11.44), Theorem
  11.5.2, and the example showing that (11.43) cannot be dropped.
* **Random walk and the SETAR margins** (§11.5.2). Proposition 11.5.3, the margins (11.45)–(11.49),
  Proposition 11.5.4 and (11.50)–(11.58) with the correction to the slope, Proposition 11.5.5 and
  (11.59)–(11.66) on all five margins.

All names are in the namespace `MeynTweedie.DriftRegularity`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Comparison](DriftRegularity/Comparison.lean) | 33 | §11.3.1 and Lemma 11.3.10: sums before a random time, the comparison theorem on a measure space in `[0, ∞]`, Dynkin's formula (Theorem 11.3.1), Propositions 11.3.2–11.3.3, the comparison theorem for Markov chains, restarting at time one, Lemma 11.3.10 |
| [RegularSets](DriftRegularity/RegularSets.lean) | 29 | §§11.1, 11.3.2: regular sets, chains and measures (11.1), mean hitting times and first-step analysis, `G_A` (11.21), `U_A`, `V_A` (11.22), Theorem 11.3.5 with the counterexample to (11.24) |
| [FosterCriterion](DriftRegularity/FosterCriterion.lean) | 27 | §11.3: (V2) (11.17)–(11.19), Theorem 11.3.4, Lemmas 11.3.6, 11.3.7 and 11.3.9, Proposition 11.3.8, Theorems 11.3.11–11.3.12, Proposition 11.3.13, Theorem 11.3.14 with its counterexample, Theorem 11.3.15 |
| [RegularityConverse](DriftRegularity/RegularityConverse.lean) | 38 | §11.1 and Theorem 11.0.1: atoms, regularity implies positivity, Theorem 11.1.2, Proposition 11.1.1, the split chain and Proposition 11.1.3, the lazy chain `½ (I + P)`, skeletons, Theorem 11.1.4, (11.7), Theorem 11.0.1 with the counterexample for sublevel sets, the example (11.12) and its counterexample |
| [AtomHittingBounds](DriftRegularity/AtomHittingBounds.lean) | 7 | §11.1: the hitting-time bound behind (11.11), (11.11), the inequality in the proof of Proposition 11.1.1 and its counterexample for `y = x` |
| [NonPositivity](DriftRegularity/NonPositivity.lean) | 14 | §11.5.1: the Markov property for one transition, Theorems 11.5.1–11.5.2, the example showing that (11.43) cannot be dropped |
| [DriftExamples](DriftRegularity/DriftExamples.lean) | 58 | §§11.2, 11.4.1, 11.4.3, 11.5.2: the semi-dynamical system and Theorem 11.2.1, random walk on a half line (Propositions 11.4.1 and 11.5.3), the forward recurrence time chain (11.28)–(11.29), the linear model (Proposition 11.4.2), the SETAR model in the interior (Proposition 11.4.5) and Proposition 11.5.5 in the case the book proves |
| [GIG1Reentry](DriftRegularity/GIG1Reentry.lean) | 54 | §11.4.2: the GI/G/1 queue with re-entry as a random recursion, its Markov property, Proposition 11.4.3 through the potential `R + N a`, the expected work and work conservation, Proposition 11.4.4 |
| [SetarMarginRecurrence](DriftRegularity/SetarMarginRecurrence.lean) | 25 | §11.5.2: the second-order bound for `log`, the test function `log max(u + ax, v − bx)` (11.50), the drift at the two ends, Proposition 11.5.4 on all five margins, the correction to the slope |
| [SetarNullMargins](DriftRegularity/SetarNullMargins.lean) | 7 | §11.5.2: Theorems 11.5.1–11.5.2 with (11.43) off `C`, a unit-slope end makes the SETAR model null, Proposition 11.5.5 on the margins (11.45)–(11.48) and on all five |

Carried from the Chapter 10 project `InvariantMeasures` (1477 theorems): 71 of the 89 modules of
that project. They are identical to the copies there except for the namespace and the last
paragraph of the module docstrings of `ModelInvariant` and `QueueInvariant`, which here describe
what those modules leave out, while the copies in `InvariantMeasures` point to the modules of that
project that supply it. Its Chapter 10 modules `QueueInvariantMinimal`, `RenewalInvariant`, `LadderInvariant`,
`GIG1Invariant` and `LinearInvariant` are not carried, nor are twelve of the thirteen modules it
carried directly from `PseudoAtoms`; the thirteenth, `ModelKernels`, is copied here from
`PseudoAtoms` (see below).

* Its own Chapter 10 modules (208 theorems): `Invariance` (39), `MinimalInvariant` (22),
  `AtomInvariant` (30), `SplitInvariant` (8), `UniqueInvariant` (18), `PositiveNull` (14),
  `CountableInvariant` (22), `QueueInvariant` (19), `MG1Invariant` (25), `ModelInvariant` (11).
  Positive, null and positive Harris chains (`IsPositive`, `IsNull`, `IsPositiveHarris`), invariant
  measures (`IsInvariant`, `IsInvariantMeasure`), mean return times (`meanReturnTime`), Kac's
  theorem (`theorem_10_2_2`), Theorem 10.4.10 (`theorem_10_4_10_ii`, `theorem_10_4_10_i_forall`),
  Proposition 10.4.1 (`proposition_10_4_1_ii`) and the counterexample `theorem_10_0_1_counterexample`
  are used. No Chapter 11 module depends, directly or through other modules, on `MG1Invariant`,
  `ModelInvariant` or `QueueInvariant`.

Carried in turn by `InvariantMeasures` from the Chapter 9 project `HarrisRecurrence` (1269
theorems; see those projects' READMEs for how they differ from the originals):

* Its own Chapter 9 modules (212 theorems): `HarrisDefinitions` (29), `HarrisProperties` (15),
  `HarrisDecomposition` (18), `SupermartingaleDrift` (14), `NonEvanescence` (21),
  `TopologicalRecurrence` (21), `TopologicalExamples` (33), `DriftHarris` (29),
  `StochasticComparison` (32). Harris chains (`IsHarris`), Proposition 9.1.1
  (`proposition_9_1_1`) and Theorem 9.1.8 (`theorem_9_1_8`) are used. No Chapter 11 module depends
  on `DriftHarris`, `NonEvanescence`, `StochasticComparison`, `SupermartingaleDrift`,
  `TopologicalExamples` or `TopologicalRecurrence`.
* From the Chapter 8 project `TransienceRecurrence` (220 theorems): `UniformTransience` (46),
  `Decompositions` (8), `Dichotomy` (17), `SplitDichotomy` (32), `DriftCriteria` (23),
  `CountableClassification` (18), `RandomWalkIntegers` (40), `RandomWalkHalfLine` (16),
  `SkipFreeWalk` (15), `RandomWalkMeanZero` (5). The extended-valued drift (`drift`), recurrent
  chains (`IsRecurrentChain`), Theorem 8.3.6 (i) (`theorem_8_3_6_i`), the strong Markov property
  at a return time (`lintegral_shiftAt_firstReturn`), and the drift and petite sets of random walk
  on a half line (`halfLine_drift_neg`, `halfLine_isPetite_Iic`) are used. No Chapter 11 module
  depends on `RandomWalkIntegers`, `RandomWalkMeanZero` or `SkipFreeWalk`.
* From the Chapter 6 project `TopologyContinuity` (130 theorems): `FellerChains` (40), `TChains`
  (14), `EChains` (16), `LinearTChains` (10), `FellerModels` (12), `CompactPetite` (16),
  `TChainModels` (10), `EChainsStability` (12). Proposition 6.3.6 (`proposition_6_3_6`: the SETAR
  model is a Lebesgue-irreducible T-chain whose compact sets are small) is used. No Chapter 11
  module depends on `CompactPetite`, `EChains`, `EChainsStability` or `LinearTChains`.
* From the Chapter 3 project `TransitionProbabilities` (169 theorems): `StateSpaces` (2),
  `PathSpace` (23), `Kernels` (32), `MarkovProperty` (22), `StrongMarkov` (20), `HittingTimes`
  (36), `CountableChains` (13), `SpecificMatrices` (21). The path measures `P_x` and `P_μ`
  (`pathKernel`, `pathMeasure`), the natural filtration (`natFilt`), the shift (`shift`), hitting
  and return times (`firstHit`, `firstReturn`) and their stopping-time property
  (`proposition_3_4_4`), hitting and taboo probabilities (`hitProb`, `tabooProb`,
  `tabooPotKernel`) and sampled kernels (`sampledKernel`) are used throughout. No Chapter 11 module
  depends on `StateSpaces` or `SpecificMatrices`.
* From the Chapter 4 project `Irreducibility` (177 theorems): `Communication` (33),
  `CountableIrreducibility` (32), `PsiIrreducibility` (13), `MaximalIrreducibility` (30),
  `Accessibility` (9), `RandomWalkIrreducibility` (20), `LinearControllability` (26),
  `LinearIrreducibility` (14). Irreducibility (`IsPhiIrreducible`, `IsMaximalIrreducibility`,
  `maxIrrMeasure`), absorbing and full sets (`IsAbsorbing`, `IsFull`) and Proposition 4.2.3
  (`proposition_4_2_3_i`) are used. No Chapter 11 module depends on `CountableIrreducibility`.
* From the Chapter 5 project `PseudoAtoms` (244 theorems): `Atoms` (8), `Splitting` (51),
  `SplitMarginal` (13), `SmallSets` (13), `SmallSetExistence` (17), `SampledChains` (21),
  `PetiteSets` (17), `Period` (22), `Cycles` (33), `CycleAperiodic` (10), `ForwardRecurrence` (8),
  `SmallSetsModels` (11), `SpreadOut` (6), `SplitPetite` (14). Atoms (`IsAtom`,
  `IsAccessibleAtom`), minorizations and the split chain (`Minorization`,
  `Minorization.splitKernel`), the existence of small sets (`theorem_5_2_2`), petite sets
  (`IsPetite`, `proposition_5_5_3`, `proposition_5_5_4_i`, `proposition_5_5_5_i`), sampling
  distributions (`IsSamplingDist`), aperiodicity (`IsStronglyAperiodic`, `IsAperiodic`) and the
  forward recurrence time chain (`fwdRecKernel`) are used. No Chapter 11 module depends on
  `SplitPetite`.
* From the Chapters 1–2 project `MarkovModels` (117 theorems): `ModelRecursion` (18),
  `ModelRandomWalk` (19), `ModelLinearModels` (39), `ModelNonlinearModels` (41). Random walk on a
  half line (`halfLineWalkKernel`), the simple linear model (`ar1Kernel`), the SETAR model
  (`setarKernel`, `setarRegime`) and orbits of a recursion (`orbit`) come from these modules.

Carried from the Chapter 5 project `PseudoAtoms` directly (19 theorems): `ModelKernels`, which
`PseudoAtoms` copied from `TransitionProbabilities`. It is identical to the copy in `PseudoAtoms`
except for the namespace and the sentence of its docstring that records the copy. Random
recursions driven by i.i.d. noise as Markov chains (`isMarkovChain_of_iid`, `IsIIDNoise`) are used
for the GI/G/1 queue with re-entry.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
