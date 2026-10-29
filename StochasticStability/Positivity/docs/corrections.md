# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Two claims are false as
printed. Each is refuted in Lean by a counterexample of this project, and a corrected statement is
proved: the solidarity inequality (18.23) and Theorem 18.1.3. Further entries concern proofs. The
proofs of Theorems 18.2.1 and 18.2.2 (ii) apply Theorem 18.1.3 beyond its hypotheses, and the
theorems are proved for every period without the Harris property. The proof of Proposition 18.4.2
uses more than the book's definition of a positive state; the proposition is proved with a Cesàro
form of positivity, and whether the book's form suffices is recorded as an open question. The
book's statements are paraphrased. The last section lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| (18.23), p. 470 | For an irreducible countable chain and `w, z`, with `Pʳ(w, x) > 0` and `Pˢ(y, z) > 0`, the strict inequality `lim sup_n P^{r+s+n}(w, z) > Pʳ(w, x)[lim sup_n Pⁿ(x, y)]Pˢ(y, z)`. | The strict inequality is false. `eq_18_23_counterexample` is the one-point chain on `Unit`, which is irreducible: every `Pⁿ` is `1`, so both sides equal `1` for all `r` and `s`. The PDF text layer prints the inequality sign correctly here; the page image confirms the strict `>`. The non-strict inequality holds for every chain and all `r`, `s` (`limsup_pow_add_ge`), and it is all that the solidarity argument of p. 470 needs: a positive `lim sup` at `(x, y)` gives a positive `lim sup` at `(w, z)` (`positive_or_null_states`, `theorem_18_2_1`). |
| Theorem 18.1.3, p. 468 | For an aperiodic null recurrent chain with invariant measure `π`, every initial law `λ` and every `ε > 0`, `sup_A λPⁿ(A)/(π(A) + ε) → 0` (18.15). | False without the Harris property. `theorem_18_1_3_counterexample` is `escKernel` on `ℕ ⊕ ℕ` (`NullNotHarris`). On `inl j` it is the forward recurrence time chain of the renewal law `escP = Σₖ 2^{−(k+1)} δ_{2ᵏ}`, which has `p(1) = ½` and infinite mean; on the escape path `inr k` it moves to `inr (k + 1)` with probability `βₖ = aₖ₊₁/aₖ`, `aₖ = ½ + 2^{−(k+1)}`, and otherwise jumps to `inl 0`. Counting measure on the renewal part is a maximal irreducibility measure (`escKernel_isMaximalIrreducibility`), the chain is recurrent (`escKernel_isRecurrentChain`) and aperiodic (`escKernel_isAperiodic`), `π = Σⱼ p{n > j} δ_{inl j}` is invariant with `π(X) = ∞` (`isInvariant_escPi`, `escPi_univ`), and the chain is null (`escKernel_isNull`). But `Pⁿ(inr 0, {inr n}) ≥ ½` while `π{inr n} = 0` (`escKernel_pow_escape`, `escPi_inr`), so (18.15) fails for `λ = δ_{inr 0}` and `ε = 1` (`escKernel_not_tendsto`). The book's proof uses (18.13) from every starting point, which is Theorem 18.1.2 and needs the Harris property. The theorem is proved for aperiodic Harris null chains with an invariant `π ≠ 0` (`theorem_18_1_3`), and the counterexample shows through it that `escKernel` is not Harris. In Theorem 18.0.1 the statement (18.2) follows the hypothesis that the chain is aperiodic and Harris, and is read under it (`theorem_18_0_1`). |
| Theorems 18.2.1 and 18.2.2 (ii), proofs, pp. 470–471 | A null recurrent chain has all its states (countable case) or petite sets null "from Theorem 18.1.3", with `π` finite on petite sets by Proposition 10.1.2. | Theorem 18.1.3 assumes aperiodicity, which neither theorem assumes, and (as corrected above) the Harris property, which a null recurrent chain on a general space need not have. The theorems hold as stated and are proved without either hypothesis. `IsNull.tendsto_pow_of_isPetite` splits a null recurrent chain into a maximal Harris set `H` and its complement (Theorem 9.1.5, carried): a petite set meets `Hᶜ` in a uniformly transient set (`IsPetite.isUniformlyTransient_inter_compl`), the chain on `H` is a Harris null chain (`absorbKernel_isHarris_of_maximalHarris`), and on each cycle class of `H` the `d`-skeleton is Harris and aperiodic (`IsCycle.absorbKernel_isHarris_isAperiodic`), so the core of Theorem 18.1.3 gives `Pⁿ(x, A) → 0` when `π(A) < ∞` (`tendsto_pow_of_isHarris_of_isNull`); a first-entrance decomposition carries the limit to every starting point (`tendsto_pow_of_firstEntrance`). This gives `theorem_18_2_2_ii` and, with `isPetite_singleton`, `theorem_18_2_1_null`; Theorem 18.3.2, whose proof uses Theorem 18.2.2 (ii), is proved for every period too (`theorem_18_3_2`). This corrects steps of proofs; there is no counterexample. |
| Proposition 18.4.2, proof of (iii) ⇒ (i), p. 475; Theorem 18.0.2 (ii) (c), p. 464 | If `x*` is positive (p. 473: `lim sup Pⁿ(x*, O) > 0` for every neighbourhood `O`), then `Π(x*, X) > 0`. | `Π(x*, ·)` is a limit of Cesàro averages `P̄ₙ(x*, ·)`, and a positive `lim sup` of `Pⁿ(x*, O)` along a sparse set of times does not bound the Cesàro averages from below. The proof uses positivity only through `Π(x*, X) > 0`, which follows from positivity in the Cesàro sense, `lim sup P̄ₙ(x*, O) > 0` for every open `O ∋ x*` (`IsCesaroPositive`, `IsCesaroPositive.eChainMass_pos`). Proposition 18.4.2 is proved with (iii) in that form (`proposition_18_4_2`), and so is Theorem 18.0.2 (ii) (c) (`theorem_18_0_2_ii`). The Cesàro form implies the book's form (`IsCesaroPositive.isTopPositive`), so (i) and (ii) give the book's (iii). **Open question:** whether the book's form suffices for (iii) ⇒ (i), that is, whether a non-evanescent e-chain with a reachable `x*` and `Π(·, X) ≡ 0` can have `lim sup Pⁿ(x*, O) > 0` for every open `O ∋ x*` while `P̄ₙ(x*, O) → 0`. If it cannot, `IsTopPositive` can replace `IsCesaroPositive` in both results. It cannot when `X` is countable and discrete, or when `x*` is isolated (then `{x*}` is an accessible atom and Theorem 18.2.2 (ii) applies); these cases are not formalised. The question is not settled. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorems 18.0.1, 18.1.2, 18.1.3, 18.2.2 and the step for null chains of any period | A general state space. | `MeasurableSpace.CountablyGenerated X` (Mathlib) where the period, the maximal Harris set or Theorem 9.1.4 (carried) is used, as in the earlier chapters. |
| §§18.3–18.5 | A topological state space; for e-chains, the setting of Chapter 12. | `X` is a locally compact, second-countable Hausdorff space with its Borel σ-algebra (§18.3), and in addition pseudo-metrizable for e-chains (§§18.4–18.5). Proposition 18.3.1 takes a countable space with the discrete topology. |
| Theorem 18.0.1, p. 462 | For an aperiodic Harris chain, (18.1); "if `Φ` is a null recurrent chain with invariant measure `π`", (18.2). | (18.2) is read under the theorem's first hypothesis: the chain is aperiodic, Harris and null, and `π ≠ 0` is invariant (`theorem_18_0_1`). Without the Harris property it is false (above). |
| Theorem 18.1.1, p. 465 | `a`, `b`, `p` proper distributions on `ℤ₊`, `p` aperiodic. | `p` is an increment law with `p(0) = 0` (`IsIncrementLaw`, carried) and aperiodic (`IsAperiodicLaw`); `a`, `b` are nonnegative with sum `1` (`theorem_18_1_1_i`, `theorem_18_1_1_ii`). No finite mean is assumed. |
| Theorem 18.1.3, p. 468 | An invariant measure `π`. | `π ≠ 0`, invariant; no σ-finiteness is needed (`theorem_18_1_3`). The core holds for a subinvariant `π` with `π(X) = ∞` (`tendsto_iSup_div_of_measure_univ_eq_top`). The step to chains of any period assumes `π` σ-finite (`tendsto_pow_of_isHarris_of_isNull`). |
| Theorem 18.2.1, p. 470 | An irreducible chain on a countable space; "for some `d ≥ 1`". | `X` is countable with measurable singletons, irreducibility is `IsIrreducibleChain P` (carried), and the positive and null cases are `IsPositive P Measure.count` and `IsNull P Measure.count`. In `theorem_18_2_1_positive`, `d` is the period and `π` is `stationaryDist P hpos` (carried). |
| Theorem 18.2.2, p. 471 | `Φ` `ψ`-irreducible. | `ψ` is a maximal irreducibility measure (`theorem_18_2_2_i`). In (ii), `Pⁿ(x, C) → 0` is proved for every `x`, not only `x ∈ C` (`IsNull.tendsto_pow_of_isPetite`). |
| Theorem 18.3.2, Proposition 18.3.3, Theorem 18.0.2 (i), pp. 463, 472–473 | A T-chain with a reachable state, which is `ψ`-irreducible by Proposition 6.2.1. | A maximal irreducibility measure `ψ` is a parameter (`theorem_18_3_2`, `proposition_18_3_3`, `theorem_18_0_2_i`); one exists by `exists_isMaximalIrreducibility_of_isReachable`. In Theorem 18.0.2 (i) "`x*` positive" is the topological notion of p. 473 (`IsTopPositive`), and (18.4) holds for every invariant probability. The "only if" half of Theorem 18.3.2 needs no T-chain property (`IsPositiveHarris.isBoundedInProbability`). |
| Proposition 18.3.1, p. 472 | An irreducible chain on a countable space. | The discrete topology, so that every chain is a T-chain (`isTChain_of_discreteTopology`); `ψ` is counting measure (`proposition_18_3_1`). |
| p. 473; Lemma 18.4.1, p. 474 | Topological null and positive states for neighbourhoods; a Feller chain and a precompact neighbourhood `O`; "a.s. [`P_*`]". | Neighbourhoods are open (`IsTopNull`, `IsTopPositive`), which gives the same notions. In Lemma 18.4.1 the chain is weak Feller, `O` is open with compact closure, and the identity holds `P_μ`-a.s. for every initial probability (`lemma_18_4_1`). |
| Proposition 18.4.3 and Theorem 18.4.4 (ii), pp. 475–477 | "A recurrent state `x` is called aperiodic if …". | `IsTopAperiodic` does not ask for recurrence. The converse of Theorem 18.4.4 (ii) also proves that every state of `supp π` is topologically recurrent (`theorem_18_4_4_ii_converse`). |
| Theorem 18.4.4 (i), p. 476 | "The proof of (i) follows immediately from Proposition 18.4.2." | Proposition 18.4.2 gives the "if" half. The "only if" half (a unique invariant probability gives a reachable state) is proved separately: each `Π(x, ·)` is an invariant probability, hence equal to `π`, and any point of `supp π` is reachable by (D.6) (`theorem_18_4_4_i`). |
| Theorem 18.5.1 (ii), p. 478 | The occupation probabilities are almost surely tight for each initial condition. | Tightness in the eventual form: for every `δ > 0` there is a compact `K` with `μ̃_N(Kᶜ) ≤ δ` for all large `N`, almost surely from the given initial state (`theorem_18_5_1_ii`), which tightness of `{μ̃_N}` implies. Eventual tightness and tightness are equivalent along a path (`tight_of_eventually_tight`). |
| Theorem 18.5.1 (i), p. 478 | `f ∈ C(X)`, convergence in probability "for each initial condition". | `f` bounded continuous (`X →ᵇ ℝ`), convergence in `P_x`-probability for every `x` (`theorem_18_5_1_i`). |
| Theorem 18.5.2, p. 480 | A coercive `V` and a compact set `C` satisfy (V4). | `C` need not be compact (any set), `V : X → ℝ≥0` is measurable and coercive (`IsCoercive`, carried), and (V4) is `PV ≤ ρV + b 1_C` with `ρ < 1`, `b < ∞` (`DriftV4`, carried). The tightness proved holds for all `N`, not only eventually (`theorem_18_5_2`). |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 18.1.1, (18.6), p. 466 | (18.6) follows from the successful coupling, `P(T_ab < ∞) = 1`. | (18.6) is Theorem 13.2.2 (`theorem_13_2_2`, carried), whose analytic proof does not use a finite mean (`theorem_18_1_1_i`). The coupling proves (18.7). |
| Theorem 18.1.1, (18.7)–(18.12), pp. 465–467 | First under the strong aperiodicity (18.8), then for the modified law `p⁰` with `p⁰(0) = p`, through (18.11)–(18.12) and `u⁰ = (1 − p)⁻¹u`. | The coupling is run once, for the lazy law `q = ½δ₀ + ½p` (`lazyLaw`, the book's `p⁰` with `p = ½`), as a Markov chain on `ℕ × ℕ` (`pairKernel`). Its difference is a random walk (`pairKernel_map_diff`), irreducible for the level `M` of `exists_aperiodic_level` and recurrent by Theorem 8.1.5 (`hitProb_diffWalk_eq_one`; the book cites Proposition 8.4.4). The lazy renewal potential `2u` (`tsum_lazyRenewalKernel_pow`) and the age laws (`pathMeasure_fst_ageEvent`) give (18.10) directly for `u` and `p̄` (`theorem_18_1_1_ii`). |
| Theorem 18.1.2, p. 467 | From (18.14) for each state `x` and the atom. | From an initial law `λ`, in the total variation form `‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖ ≤ 2(P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − u| ∗ t₁(n + 1))` with `t₁(m + 1) = p̄(m)` (`tvNorm_comp_pow_succ_sub_atom_le`); only the tail convolution of Theorem 18.1.1 is needed (`tendsto_tvNorm_sub_atom`). The rest follows the book: a split skeleton with an aperiodic atom, then the contraction of the total variation norm (`theorem_18_1_2_measures`). The double integral of (18.13) is taken in `[0, ∞]`, with no measurability of the integrand (`tendsto_lintegral_of_le_const`). |
| Theorem 18.1.3, p. 468 | Egorov's theorem, with `π(X) = ∞`, makes (18.17) uniform on a set `D` with `π(D) > δ⁻¹`. | The sets `D_N` of points at which (18.17) holds from stage `N` on increase to `X`, so `π(D_N) ↑ π(X) = ∞` and one of them serves as `D`; no σ-finiteness is used (`tendsto_iSup_div_of_measure_univ_eq_top`, `measure_mul_le_of_forall_le`, `jain_arith`). |
| Theorem 18.2.2 (i), p. 471 | On `D₀ ∩ H`, `P^{nd+r}(x, A) → dπ(A ∩ D_r)`, positive for some `r`, and `L(x, D₀ ∩ H) > 0`. | From `x` the chain enters the complement of the `ψ`-null set of Theorem 13.3.4 (ii) (`theorem_13_3_4_ii`, carried) at some time, after which the phase averages of `Pⁿ(·, B)` converge to `π(B) > 0` (`IsPositive.isPositiveSet`). |
| Theorem 18.3.2, "only if", p. 472 | Compact `C_r ⊆ D_r` with `π_r(C_r) > 1 − ε` and (18.25); off the cycle classes, Harris recurrence. | One compact `K` with `π(Kᶜ)` small serves all classes; on each class the `d`-step laws converge in total variation (Theorem 13.3.3 for the skeleton, carried), and Fatou's lemma combines the classes with the time spent outside them (`IsPositiveHarris.isBoundedInProbability`, `eventually_of_forall_mul_add`). No T-chain property is used. |
| Theorem 18.0.2 (ii), proof, p. 464 | The equivalence of (a)–(c) follows from Proposition 18.4.2. | (a) contains the weak LLN, which Proposition 18.4.2 does not give; (b) ⇒ (a) uses Theorem 18.5.1 (i) as well (`theorem_18_0_2_ii`, through `theorem_18_5_1_i`). |
| Proposition 18.4.3, p. 476 | The argument for `f ∈ C_c(X)` with `∫ f dπ = 0`. | The argument is run for `Fₖ = Pᵏf − π(f)`, which is bounded and equicontinuous but not compactly supported, so that every `f ∈ C_c(X)` is covered (`tendsto_pow_cc_of_mem_support`); weak convergence follows because `π` is a probability. The Ascoli step is `exists_subseq_tendsto_of_equicontinuousAt` (pointwise convergence along a subsequence suffices). |
| Theorem 18.4.4 (ii), p. 477 | `O_ε = {x : lim sup |Pᵏf| < ε}` is an open neighbourhood of `supp π`, and `P̄_N(x, O_ε) → 1` by Theorem 18.4.4 (i). | `O_ε` is taken as a union of equicontinuity neighbourhoods of the points of `supp π`, and `P̄_N(x, O_ε) → 1` comes from (D.6) for the limit kernel, `Π(x, ·) = π` (`theorem_18_4_4_ii`). |
| Theorem 18.5.1 (i), pp. 478–479 | The bound (18.32), uniform convergence of `P̄_M f` on a compact set plus the time spent outside it, then Markov's inequality. | The `P_x`-mean of `N⁻¹ Σₖ |P̄_M f(Φₖ) − π(f)|` is `P̄_N(x, |P̄_M f − π(f)|)` (`integral_occAvg`), which tends to `π(|P̄_M f − π(f)|)` as `N → ∞` because `P̄_M f` is continuous (`continuous_cesaroIter`) and `P̄_N(x, ·) →w π`, and this tends to `0` as `M → ∞` by dominated convergence; Markov's inequality then gives (i) (`tendsto_occAvg_inProb`). (18.32) is proved for `f ∈ C_c(X)` (`eventually_forall_abs_cesaroIter_sub_le`) and used, as in the book, for (ii). |
| Theorem 18.5.1, (18.33), p. 479 | Bounded martingale differences obey the strong law, by Theorem 5.2 of Chapter 4 of Doob [99]. | Proved here: orthogonality by the Markov property, `E[Mₘ²] ≤ 4B²m`, Chebyshev's bound along the squares and Borel–Cantelli (`ae_tendsto_mdSum_div`). |
| Theorem 18.5.2, p. 480 | "For a proof see [259]." | Proved here. `W = √V` satisfies `PW ≤ √ρ W + √b` (`kfunR_sqrt_le_of_drift`, AM–GM) and `E_x[V(Φₖ)] ≤ V(x) + b/(1 − ρ)` (`integral_coord_le_of_drift`), so the martingale differences of `W` are square integrable with bounded second moments and obey the strong law (`ae_tendsto_mdSum_div_of_sq`, `ae_tendsto_mdSum_sqrt_div`). Summing `W − PW` along the path bounds the averages of `W` by `(2 + √b)/(1 − √ρ)` eventually, and Markov's inequality on the compact sublevel sets of `V` gives tightness (`tight_of_tendsto_mdSum_sqrt`, `tight_of_eventually_tight`); Theorem 18.5.1 (ii) gives (18.35) (`theorem_18_5_2`). Boundedness in probability follows from the moment bound (`theorem_18_5_2_bounded`). |
| Independent coupling, p. 464 | The walk on `ℤ²` is recurrent and the walk on `ℤ⁴` transient, citing Spitzer [369]. | Two independent copies of the walk on `ℤ²` are the chain `ssrw4` (`matKernel_ssrw4`). The 45° rotation turns the walk on `ℤ²` into two independent walks on `ℤ` (`ssrw2_eq_prodMat`), so the return probabilities at time `2n` are `c_n²` and `c_n⁴` with `c_n = C(2n, n)/4ⁿ` (`matPow_ssrw2_even`, `matPow_ssrw4_even`), and `1/(4(n + 1)) ≤ c_{n+1}²`, `c_n² ≤ 1/(2n + 1)` (`centralC_sq_ge`, `centralC_sq_le`) decide recurrence and transience by the Chapter 8 classification (`ssrw2_isRecurrentState`, `ssrw4_isTransientState`). |

## Conventions

* Transition laws are Mathlib's kernels and `Pⁿ` is the kernel power. Measures, kernels and test
  functions take values in `[0, ∞]` (`ℝ≥0∞`); the ratios of (18.2) and (18.15) are taken in
  `[0, ∞]`, with the supremum over measurable sets. The chain lives on the path space `ℕ → X` with
  laws `P_x = pathKernel P x` and `P_μ = pathMeasure P μ` (carried).
* `tvNorm μ ν` (carried) is `sup_{|f| ≤ 1} |μ(f) − ν(f)|`, which is at most `2`, as in (13.7).
* `IsPositive P ψ` and `IsNull P ψ` (carried) include `ψ`-irreducibility with a maximal
  irreducibility measure `ψ`; positive recurrence is `IsPositive`.
* Weak convergence `μₖ →w μ` is `∫ f dμₖ → ∫ f dμ` for every `f : X →ᵇ ℝ`. The Cesàro kernel is
  `cesaroKernel P n = n⁻¹ Σ_{i=1}^n Pⁱ` (carried), and Proposition 18.4.2 and Theorem 18.0.2 (ii)
  state its convergence along `n + 1`. In §§18.4–18.5 the invariant probability is the limit
  kernel at the reachable state, `Π(x*, ·) = eChainLimit he x₀` (carried).
* The occupation averages of (18.30) are written as `N⁻¹ Σ_{k=1}^N f(Φₖ)`; the occupation measure
  of a path is `occMeasure ω N`. "Almost surely tight" and "a.s. [`P_*`]" are stated under
  `P_x = pathMeasure P (Measure.dirac x)` for each initial state `x`.
* The renewal sequences of §18.1.1 are real sequences on `ℕ`: `a ∗ u` is `delayedRenewal a p`,
  `p̄` is `renewalTail p` and `∗` is `realConv` (carried). The age `V⁻(n) = n − k` is the event
  `ageEvent n k` for the lazy renewal chain.
* The PDF text layer drops several symbols of this chapter, and the Lean statements follow the
  printed page. The tail `p̄` in (18.7), (18.10), (18.12) and (18.14) is printed as `p`; the
  Cesàro averages `P̄ₖ` of Theorem 18.0.2 (ii) (a), Proposition 18.4.2 (i), (18.32)–(18.34) and of
  the proof of Theorem 18.4.4 are printed as `Pₖ`; the star of `x*` is often lost. The strict
  inequality of (18.23) is as printed.
* The carried modules are copied from the earlier projects without change apart from the namespace
  and the imports (see the [README](../README.md)). The corrections they contain belong to
  Chapters 1–15 and 12, are recorded in their module docstrings and in those projects, and are not
  repeated here.

## Not formalised

* **The equivalence of p. 474** for non-evanescent e-chains, that a reachable state exists iff
  `Π(x, X)` does not depend on `x`: one direction (`eChainLimit_eq_of_isReachable`) and the form
  under boundedness in probability on average (`theorem_18_4_4_i`) are formalised.
* **The open question** of Proposition 18.4.2 (above), and the special cases in which it is
  settled: a countable discrete space, and an isolated reachable state.
* **The justification of topological aperiodicity** by Lemma D.7.4 (p. 475).
* **§18.6**, the commentary (pp. 480–481): the history; the analogues of Theorem 18.3.2 and
  Proposition 18.3.3 for chains that are not irreducible [277]; the decomposition of a chain
  without a reachable state into the classes `E_x` and a transient set, and the extension of
  Theorem 18.4.4 to such chains [281]; the random limit (18.36) and Theorem 18.5.1 with `π̃` in
  place of `π`.
* **Informal remarks.** The aims of the chapter (pp. 462–464); the remark that the increments of
  `Φ*` may live on a sublattice (p. 465); (18.22) (p. 469); the classical approach through `Pⁿ`
  (p. 469) and why Theorem 18.2.1 waited until §18.2 (p. 470); the expected positivity of bounded
  in probability chains (pp. 471–472); the series begun with Theorem 9.3.3 (p. 473); the role of
  reachable states for e-chains (p. 473); the difficulty of limits of `Pⁿ` for weak Feller chains
  (p. 475); the reference to Theorem 17.1.2 and its null set (pp. 477–478), Chapter 17 not being
  carried; and the interpretation of Theorems 18.1.2 and 18.1.3 (p. 469).
