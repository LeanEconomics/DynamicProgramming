# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Three of the claims below are
refuted in Lean by a counterexample, and a corrected statement is proved. For the other entries
the table says why no counterexample is given. The last section lists what is not formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Proposition 6.4.2, (6.17), p. 141 | If `Φ` is Feller and `Pⁿ(x, ·) → π` weakly for every `x`, for a unique probability `π`, then `Φ` is an e-chain. The proof: the limit is continuous (indeed constant), so by Ascoli's Theorem D.4.2 the functions `{Pᵏf}` are equicontinuous on compact sets. | Ascoli's theorem gives equicontinuity from uniform convergence on compact sets, and the hypothesis gives only pointwise convergence. The statement fails. The doubling chain `jumpKernel 2` on `ℝ` jumps from `x` to `0` with probability `min(\|x\|, 1)` and otherwise moves to `2x`. It is weak Feller (`jumpKernel_isWeakFeller`). From every `x` the chain is at `0` from some time on (`jumpKernel_two_pow_zero_eq_one`), so `Pᵏ(x, ·) → δ₀` for every `x`. But the point `2^{−(k+1)}` reaches `1` at time `k + 1` with probability at least `1/4` (`jumpKernel_two_pow_one_ge`), while `0` is absorbing. So for the compactly supported tent function `f(y) = max(0, 1 − \|y − 1\|)` (`tentAtOne`), `{Pᵏf}` is not equicontinuous on `[−1, 1]` at `0`, and the chain is not an e-chain (`proposition_6_4_2_counterexample`). What holds is the statement with the convergence the proof uses: if for every continuous compactly supported `f`, `Pᵏf` converges uniformly on compact sets to a continuous limit, the chain is an e-chain (`proposition_6_4_2_corrected`, via `equicontinuousOn_of_tendstoUniformlyOn`). |
| Lemma 6.1.4, p. 129 | If `Φ` is ψ-irreducible, then `x*` is reachable if and only if `x* ∈ supp ψ`. | The book's proof of the "only if" direction goes through the absorbing full set of Proposition 4.2.3, and uses `ψ` maximal. For an irreducibility measure that is not maximal the lemma fails: the zero measure is an irreducibility measure of every chain, and on the one-point space with the identity kernel the point is reachable but `supp 0 = ∅` (`lemma_6_1_4_counterexample`). For a maximal irreducibility measure the lemma holds (`lemma_6_1_4`). As almost everywhere in the book, "ψ-irreducible" is read with `ψ` maximal. |
| (6.15), p. 137 | For any constants `ρ₁ < ρ(F) < ρ₂` there is `c > 1` with `c⁻¹ ρ₁ⁿ ≤ ‖Fⁿ‖ ≤ c ρ₂ⁿ`. | The lower bound needs `ρ₁ ≥ 0`. For `F = 0`, a `1 × 1` complex matrix, `ρ(F) = 0` and `ρ₁ = −1 < ρ(F)`, but `c⁻¹ (−1)² ≤ ‖0²‖ = 0` holds for no `c ≥ 1` (`lemma_6_3_4_bounds_counterexample`). For `0 ≤ ρ₁ < ρ(F) < ρ₂` both bounds hold, with `c ≥ 1` (`lemma_6_3_4_bounds`); the upper bound alone needs only `ρ(F) < ρ₂` (`lemma_6_3_4_upper`). |
| p. 133 | After Theorem 6.2.9: on `X = [0, 1]`, with `0 < \|α\| < 1`, `P(x, {0}) = 1 − P(x, {αx}) = x` for `x > 0` and `P(0, {0}) = 1`, the chain is Feller and `δ₀`-irreducible but not a T-chain, since `lim_{x→0} Pₓ(τ_{0} ≥ n) = 1`. | The claim is proved (`feller_not_tChain_counterexample`), for `α = 1/2` and on `ℝ` rather than `[0, 1]`: `jumpKernel 2⁻¹` jumps from `x` to `0` with probability `min(\|x\|, 1)` and otherwise moves to `x/2`. On `[0, 1]` this is the book's chain with `α = 1/2`. (For `α < 0` the move to `αx` leaves `[0, 1]`.) The proof does not go through `Pₓ(τ_{0} ≥ n)`. It uses `Pⁿ(x, {0}) ≤ n\|x\|` (`jumpKernel_half_pow_le`), so `K_a(x, {0}) → 0` as `x → 0`, whereas a continuous component `T` would have `T(0, {0}) = T(0, X) > 0` and keep `K_a(·, {0})` bounded below near `0`. Since `supp δ₀ = {0}`, the example shows that the hypothesis on `supp ψ` in Theorem 6.2.9 cannot be dropped. The claim is true, so there is no counterexample. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| The whole chapter (p. 123) | `X` is a locally compact, separable, metrizable space with its Borel σ-field. | `X` carries a topology and a σ-algebra containing the open sets (`OpensMeasurableSpace`, or `BorelSpace` where stated). Each result assumes only what it uses. *First countable*: the lower-semicontinuity core (`IsWeakFeller.lowerSemicontinuous_lintegral`, `IsWeakFeller.pow`, `IsWeakFeller.lsc_sampledKernel`, `IsWeakFeller.usc_pow_closed`, `IsWeakFeller.usc_sampledKernel_closed`), the strong Feller part of Proposition 6.1.1 (i), Proposition 6.1.1 (ii)–(iii), Propositions 6.1.5–6.1.6, and `isWeakFeller_recursionKernel`. *Pseudo-metrizable*: the weak Feller part of Proposition 6.1.1 (i), Proposition 6.4.1 (the portmanteau theorem), Proposition 6.4.2 corrected, Proposition 6.2.6 and Lemma 6.2.7. *Metrizable*: Proposition 6.2.8, Theorems 6.2.9 and 6.0.1, and Proposition 6.4.5. *Second countable*: Proposition 6.2.4 (Lindelöf), Theorem 6.2.5 (i), Theorems 6.2.9 and 6.0.1, and Propositions 6.4.3 and 6.4.4. *Locally compact*: Theorem 6.2.5 (i), Proposition 6.2.8 (ii) (the Baire category theorem), Theorems 6.2.9 and 6.0.1, and Propositions 6.4.3–6.4.5. *Hausdorff*: Theorem 6.2.5 (ii), where compact sets must be measurable, Proposition 6.4.3 and `isTight_orbit_of_boundedInProbability`. *Countably generated σ-algebra*: Theorem 6.2.5 (ii), Proposition 6.2.6, Lemma 6.2.7 and Proposition 6.2.8 (ii), through Theorem 5.2.2 and Proposition 5.5.5 (carried); it holds for the Borel σ-algebra of a second-countable space. Lemma 6.1.4 and Propositions 6.2.1–6.2.3 need no hypothesis beyond the topology itself and, for Lemma 6.1.4 and Proposition 6.2.3, the measurability of open sets. |
| Proposition 6.4.4, p. 142 | Boundedness in probability is tightness, and a set of probabilities is tight if and only if it is precompact in `(M, d_m)`. | `proposition_6_4_4` assumes a complete separable locally compact metric space. Mathlib's converse of Prokhorov's theorem (`isTightMeasureSet_of_isCompact_closure`) needs a complete metric. A locally compact separable metrizable space admits one, so the book's setting is covered. |
| Proposition 6.4.3, (6.16), pp. 140–141 | `d_m` is built from "an appropriate set of functions in `C_c(X)`", and the chain is an e-chain if and only if `(P, M, d_m)` is stable in the sense of Lyapunov. | The equivalence depends on the `fⱼ`: for `fⱼ = 0`, `d_m = 0` and every chain is Lyapunov stable. `proposition_6_4_3` assumes `‖fⱼ‖ ≤ 1`, compact supports, and that the `fⱼ` approximate every compactly supported `f` with `‖f‖ ≤ 1` in the sup norm. The "if" direction needs neither compact supports nor local compactness (`proposition_6_4_3_of_lyapunov`). The book omits the proof; the "only if" direction rests on `eventually_forall_abs_integral_sub_lt`. |
| Proposition 6.1.1 (ii), p. 125 | `m : ℤ₊ → ℤ₊` non-decreasing; then `Pₓ{τ_C ≥ n}`, `Eₓ[τ_C]` and `Eₓ[r^{τ_C}]`, `r > 1`, are lower semicontinuous. | The book applies the result to `m(n) = rⁿ`, which is not integer-valued. Here `m : ℕ → ℝ≥0` is any non-decreasing function, with `m(∞) = sup m` on `{τ_C = ∞}` (`extendSup`, `expectReturn`, `proposition_6_1_1_ii`). The book's reduction to `m(0) = 0` is replaced by keeping the term `m(0)` (`expectReturn_eq_tsum`). The geometric case holds for `r ≥ 1` (`proposition_6_1_1_ii_geom`). |
| (6.14), p. 137 | `log ρ(F) = lim n⁻¹ log ‖Fⁿ‖` for any matrix norm. | For a nilpotent `F` the book's `log ρ(F) = −∞` has no counterpart with Lean's `Real.log 0 = 0`, so the log form is stated for `ρ(F) > 0` (`lemma_6_3_4_log`). The root form `‖Fᵏ‖^{1/k} → ρ(F)` holds without restriction (`lemma_6_3_4`). Both are stated in a complex Banach algebra, so for matrices with a complete algebra norm. |
| (LSS5), p. 137 | The eigenvalues of `F` fall within the open unit disk in `ℂ`. | `IsStableMatrix F`: the spectral radius of `F`, viewed as a complex matrix, is less than `1`. The spectrum of a matrix is the set of roots of its characteristic polynomial (Mathlib's `Matrix.mem_spectrum_iff_isRoot_charpoly`), so this is the book's condition. |
| (SETAR2), p. 139 | Each `W(j)` has a density positive on the whole real line. | `Γⱼ ≪ μ_Leb` and `μ_Leb ≪ Γⱼ`, that is, `Γⱼ` is equivalent to Lebesgue measure (`proposition_6_3_6`), which is what a density positive almost everywhere gives. The zero-mean condition of (SETAR1) is not used, and the thresholds need not be ordered. |
| p. 128 | `x` is reachable if `Σₙ Pⁿ(y, O) > 0` for every `y` and every open `O ∋ x`. | The sum is over `n ≥ 1`: `IsReachable` asks for `U(y, O) > 0` (`potKernel`, carried), which is what the proof of Lemma 6.1.4 uses. With `n = 0` included, the condition would hold automatically for `y ∈ O`. |
| Proposition 6.1.2, p. 127 | NSS(F) with `F` smooth on an open subset of `ℝⁿ`. | The state space is a second-countable real normed space, for instance `ℝⁿ` (`proposition_6_1_2`), as in the carried `nssKernel`. The weak Feller property holds for every random recursion with `x ↦ F(x, w)` continuous (`isWeakFeller_recursionKernel`). |
| Propositions 6.1.6, 6.2.2, Theorem 6.0.1 (i), pp. 124–130 | The chain is ψ-irreducible. | The conclusion is that `Φ` is `ψ`-irreducible for some `ψ ≠ 0`, on a non-empty `X`. Theorem 6.0.1 (i) assumes `L(x, O) > 0` for non-empty open `O`, since `L(x, ∅) = 0`. |
| Proposition 6.2.1, p. 130; Theorem 6.2.5 (ii), p. 131; Proposition 6.2.8 (i), p. 133 | `T` is an everywhere non-trivial continuous component; `Φ` is ψ-irreducible. | Proposition 6.2.1 holds for every continuous component `T` of any `K_a`, without non-triviality (`proposition_6_2_1`). Theorem 6.2.5 (ii) and Proposition 6.2.8 (i) take any nonzero irreducibility measure, not necessarily maximal (`theorem_6_2_5_ii`, `proposition_6_2_8_i`). |
| Proposition 6.3.3, (LSS4), p. 135 | `Γ` is nonsingular with respect to Lebesgue measure, with non-trivial density `γ_w`. | `¬ Γ ⟂ₘ volume` (`proposition_6_3_3`), which is the existence of a non-trivial absolutely continuous part. The continuous component is for `Pⁿ`, `n` the dimension of the state space (`diracDist n`). |
| Proposition 6.4.5, p. 142 | `Φ` is bounded in probability; `(P, C(X), d_c)` is a dynamical system when `P` is weak Feller. | `proposition_6_4_5` assumes that `P` is weak Feller, which the paragraph before the proposition assumes, so that the orbit `{Pᵏf}` lies in `C(X)`. |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Lemma 6.2.7, p. 132 | A petite set is characterised by `K_a(x, C) ≥ δ` on `A` for a compact petite `C`, using the regularity of probability measures by compact sets; `K_a(·, C)` is upper semicontinuous for compact `C`. | A closed set suffices. Proposition 5.5.5 (i) makes the minorizing measure `ψ_b` of `A` maximal, Theorem 5.2.2 gives a small set `C` with `ψ_b(C) > 0`, and inner regularity of the finite measure `ψ_b` by closed sets on a pseudo-metrizable space gives a closed `D ⊆ C` with `ψ_b(D) > 0`. Then `K_b(·, D)` is upper semicontinuous (`IsWeakFeller.usc_sampledKernel_closed`), so `K_b(x, D) ≥ ψ_b(D)` extends from `A` to `Ā`, and Proposition 5.5.4 (i) makes `Ā` petite (`lemma_6_2_7`). No compactness is used, so local compactness is not needed. |
| Proposition 6.3.6, p. 139 | Near a threshold `rᵢ`, `Tᵢ(x, ·) = min(P'(rᵢ, ·), P(rᵢ, ·), P(x, ·))` is a continuous component, with `P'(rᵢ, ·)` the limit from the right; the local components are combined by Proposition 6.2.4. | No minimum of measures is used. Theorem 5.2.2 gives a small set `C` with `μ_Leb(C) > 0`. In every regime, `x ↦ Γⱼ{w : φ(j) + θ(j)x + w ∈ C}` is lower semicontinuous (`lsc_translate`) and positive, so on a compact `K` the one-step probability `P(x, C)` is bounded below by the least of finitely many positive minima. So every compact set is small (`proposition_5_2_4_i`, carried) and Theorem 6.2.5 (i) gives the T-chain (`proposition_6_3_6`). |
| Proposition 6.3.3, pp. 136–137 | The proof is given for scalar noise, with the change of variables `vₙ = Cₙwₙ`, `\|Cₙ\| ≠ 0`, Lemma D.4.3 and dominated convergence; the case `W ∈ ℝᵖ` "needs much more notation". | The proof covers every noise dimension `p`. The component is `T(x, A) = ν{v : Fⁿx + v ∈ A}`, with `ν` the law of `Cₙ(W₁, …, Wₙ)` when the `Wᵢ` are drawn from the absolutely continuous part of `Γ`. `ν` is absolutely continuous because `Cₙ` is onto (`range_ctrbMap_eq_top`, carried), and `T(·, A)` is lower semicontinuous by `lsc_translate`. No determinant is needed (`proposition_6_3_3`). |
| Lemma D.4.3, used on pp. 128 and 137 | The convolution of a density with a bounded function is continuous. | Replaced by the continuity of translation in measure: for a finite `ν ≪ μ`, `μ` a Haar measure on a finite-dimensional real normed space, `t ↦ ν{w : t + w ∈ B}` is lower semicontinuous for every measurable `B` (`lsc_translate`, from `lsc_translate_of_finite` and Mathlib's `tendsto_measure_symmDiff_preimage_nhds_zero`). It is used in Propositions 6.1.3, 6.3.2, 6.3.3 and 6.3.6. |
| Proposition 6.1.1, p. 126 | Theorem D.4.1: a lower semicontinuous function is an increasing limit of continuous functions; `P f_N ↑ P f` and `(P I_{fᵢ})^{k−1} ↑ (P I_{Cᶜ})^{k−1}`. | Replaced by Fatou's lemma along a sequence of measures for a lower semicontinuous integrand (`lintegral_ofReal_le_liminf`, `lintegral_le_liminf_of_lsc`), which gives `IsWeakFeller.lowerSemicontinuous_lintegral` on a first-countable space. Parts (ii) and (iii) then follow by induction from the first-step equations `tailProb_succ` and `hitWithin_succ`. |
| Proposition 6.4.4, p. 142 | "Boundedness in probability is simply tightness for the collection `{Pᵏ(x, ·)}`", and tight sets are precompact. | Lagrange stability concerns the orbit `{μPᵏ}` of every initial law `μ`, and the book's argument covers only `μ = δₓ`. For a general `μ` the orbit is shown tight by Fatou's lemma along a compact exhaustion for large `k`, the finitely many remaining `μPᵏ` being tight on their own (`isTight_orbit_of_boundedInProbability`). The statement is true, so there is no counterexample. |

## Conventions

* Transition laws are Mathlib's kernels, and `Pⁿ` is the kernel power. `L(x, A)` is `hitProb`,
  `τ_C` is `firstReturn` (the first time `n ≥ 1` in `C`), `K_a` is `sampledKernel`, `K_{a_{1/2}}`
  is `resolventHalf`, and `U` is `potKernel`, all from the carried modules. φ-irreducibility,
  maximal irreducibility measures, small and petite sets are the carried `IsPhiIrreducible`,
  `IsMaximalIrreducibility`, `IsSmallSet`/`IsSmall` and `IsPetiteSet`/`IsPetite`. "The chain is
  ψ-irreducible" means that `ψ` satisfies `IsMaximalIrreducibility`, except where a result is
  stated for any nonzero irreducibility measure.
* Lower and upper semicontinuity are Mathlib's `LowerSemicontinuous` and `UpperSemicontinuous`, for
  functions into `[0, ∞]`. `supp ψ` is Mathlib's `Measure.support`.
* `IsWeakFeller P` is the book's definition (i) on p. 124: `P(·, O)` is lower semicontinuous for
  every open `O`. The form "`P` maps `C(X)` to `C(X)`" is `proposition_6_1_1_i_weak`.
  `IsStrongFeller P` asks that `x ↦ ∫ f dP(x)` be continuous for every bounded measurable `f`.
* `Pₓ(τ_C ≥ k)` is `tailProb`, `Pₓ(τ_O ≤ n)` is `hitWithin`, and `Eₓ[m(τ_C)]` is `expectReturn`,
  with `m(∞) = sup m` (`extendSup`).
* `IsContinuousComponent P a T` requires `T` substochastic (`IsSubstochasticKernel`, carried),
  `T(x, ·) ≤ K_a(x, ·)` for every `x`, and `T(·, A)` lower semicontinuous for every measurable `A`.
  It does not require `a` to be a sampling distribution; `IsTChain P` does, and asks for
  `T(x, X) > 0` for every `x`.
* `IsReachable P x` asks for `U(y, O) > 0` for every `y` and every open `O ∋ x`.
  `IsOpenSetIrreducible P` asks this for every `x`.
* `M` is Mathlib's `ProbabilityMeasure X` with the topology of weak convergence. The map `μ ↦ μP`
  is `pushPM`, the orbit `k ↦ μPᵏ` is `orbitPM`, and `Pᵏ(x, ·)` as a probability measure is
  `powPM`. The metric `d_m` of (6.16) enters only through `dmDist fs`, for a given sequence `fs` of
  bounded continuous functions, in Proposition 6.4.3. `IsLyapunovStable P fs` is Lyapunov stability
  for `dmDist fs`; `IsLagrangeStable P` asks that every orbit `{μPᵏ}` have compact closure.
* `(C(X), d_c)` is `C(X, ℝ)` with Mathlib's compact-open topology, the topology of uniform
  convergence on compact sets that `d_c` generates. The orbit `k ↦ Pᵏf` of a bounded continuous `f`
  is `orbitCM`.
* `IsEChain P`: for every continuous `f` with compact support and every compact `K`, the functions
  `Pᵏf`, `k ≥ 0`, are equicontinuous on `K` (`EquicontinuousOn`).
  `IsBoundedInProbability P` follows p. 142, with `ε ∈ (0, ∞]`.
* `ℝⁿ` is `Fin n → ℝ`, and `μ_Leb` is Mathlib's Lebesgue (product) measure `volume`. LSS(F, G) is
  the carried `lssMatrixKernel Γ F G`, (LCM3) is `IsControllable F G`, the controllability map `Cₙ`
  is `ctrbMap`, and (LSS4) is `¬ Γ ⟂ₘ volume`.
* The SETAR model is the carried `setarKernel Γ φ θ r`, with `m + 1` regimes, thresholds
  `r : Fin m → ℝ`, the regime `setarRegime r x` given by `r_{j−1} < x ≤ rⱼ`, and independent regime
  noises.
* The example (6.1)–(6.2) is `recipKernel α` on `ℝ`. Its points are `1/(n + 1)`, `n ≥ 0`, so the
  book's `αₙ` at `n⁻¹` is `α (n − 1)`. Every point other than the `1/(n + 1)`, including `0`, moves
  to `1`.
* `jumpKernel c` jumps from `x` to `0` with probability `min(|x|, 1)` and otherwise moves to `cx`.
  `c = 1/2` is the chain of p. 133, and `c = 2` is the counterexample to Proposition 6.4.2.
* The carried modules are copied without change apart from the namespace, the imports and module
  docstrings. The corrections they contain belong to Chapters 1–5, are recorded in their module
  docstrings and in those projects, and are not repeated here.

## Not formalised

* **The multiplicative random walk** (6.20), pp. 143–144: the claim that it is Feller but not an
  e-chain, and an e-chain once `{0}` is made open. The book gives only a sketch, which relies on
  Section 10.5.4.
* **The storage-model remark** after Proposition 6.3.1 (p. 134): the storage model with a general
  state-dependent release rule is not constructed in this project.
* **The ARMA and controllable-subspace remarks** after Proposition 6.3.3 (p. 137). The AR(k) case is
  formalised (`arKernel_isTChain`).
* **The strong Feller property of the controllable Gaussian model** (p. 137). It rests on the
  exact form of (4.18), which is not formalised as a density.
* **The weakened support conditions** after Proposition 6.3.6 (p. 139), which are informal.
* **The remarks on the example (6.1)–(6.2)** (pp. 124–125): that it fails to visit most open sets,
  that it is unstable when `Σ αₙ < ∞`, and that every continuous component property fails when
  `αₙ → 0`. That it is not weak Feller and is `δ₀`-irreducible is formalised.
* **The claim that a random walk with rational increments enters every open set** (p. 130). As
  stated it needs a condition on `Γ`: for `Γ = δ₀` the walk never moves. That such a walk is weak
  Feller and irreducible for no nonzero measure is formalised.
* **Proof devices replaced by other arguments.** The compact inner approximation in Lemma 6.2.7,
  the minimum of the boundary measures in Proposition 6.3.6, the scalar change of variables in
  Proposition 6.3.3, Lemma D.4.3 and Theorem D.4.1; see "Proofs that differ from the book" above.
* **Forward references and informal remarks.** The role of CM(F) and Chapter 7 (p. 127), the
  comparison of the T-chain and e-chain routes (p. 129), the remarks on how widely the T-chain
  property holds (pp. 130, 134), the remark that chains with good limiting behaviour are e-chains
  (p. 141), invariant probabilities as stationary points (6.18) (p. 141), the summary after
  Proposition 6.4.5 (p. 142), and the remark on non-e Feller chains (p. 144).
* **§6.5**, the commentary (pp. 144–145), including the remarks on random walks on groups and
  semigroups and on Athreya and Pantula's condition for the linear model.
