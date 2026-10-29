/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.ModelKernels
import GeneralizedDrift.SpecificMatrices
import GeneralizedDrift.ModelStorage
import GeneralizedDrift.ModelRenewal
import GeneralizedDrift.ModelLinearModels
import GeneralizedDrift.PoissonCounts

/-!
# Kernels of the specific models (MT §§3.3 and 3.5.1–3.5.3)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/SpecificKernels.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `InvariantMeasures.*`.

Meyn and Tweedie, §3.5, pp. 67–70, and the derivations left open in §§3.2–3.3. Every model is a
recursion `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)`, so `isMarkovChain_of_iid` (`ModelKernels`) shows it is a Markov
chain with the kernel of `ModelRecursion`; here each kernel is connected to the book's formula.

**§§3.2–3.3 from the recursions** (i.i.d. noise ⇒ Markov):
* `matKernel_rwMatrix`, `randomWalkInt_isMarkovChain`: (3.11), random walk on `ℤ`.
* `matKernel_rwhlMatrix`, `rwhl_isMarkovChain`: (3.12)–(3.14), random walk on `ℤ₊`.
* `matKernel_giM1Matrix`, `proposition_3_3_1_of_recursion`, `proposition_3_3_1_derived`:
  Proposition 3.3.1 (GI/M/1); the `_derived` form takes the service counts from their primitive
  description, using (3.15) from `PoissonCounts`.
* `matKernel_mG1Matrix`, `proposition_3_3_2_of_recursion`, `proposition_3_3_2_derived`:
  Proposition 3.3.2 (M/G/1), with (3.19).
* `matKernel_arMatrix`, `proposition_3_3_3_of_recursion`: Proposition 3.3.3 (AR(1) on `ℚ`);
  `ar1_isMarkovChain`: AR(1) on `ℝ`; `lssMatrix_isMarkovChain`: the linear state space model;
  `waitingTime_isMarkovChain`: the GI/G/1 waiting time (Lindley) chain.

**§3.5.1** Random walk on a half line: `eq_3_35` (3.35), `eq_3_36` (3.36),
`halfLineWalk_isMarkovChain`; on `ℝ`, `randomWalkKernel_apply_image` and
`randomWalkReal_isMarkovChain`.

**§3.5.2** Storage models: `eq_3_37` and `eq_3_37_div` (3.37, corrected), `storage_isMarkovChain`.

**§3.5.3** Renewal processes: `renewalReal_isMarkovChain` (`Zₙ` is a random walk),
`renewalReal_map_eq` (`P(Zₙ ∈ ·) = Γ₀ ∗ Γ^{n∗}`), `eq_3_38` (3.38), `renewalMeasure` and
`renewal_expected_count`, `renewal_expected_count_undelayed` (`U[0, t]` and `Γ₀ ∗ U[0, t]` are
expected numbers of renewals). For the recurrence time processes (RT3)–(RT4), the pathwise
transitions: `fwdTimeCts_add_of_lt` and `fwdSkeleton_succ_of_lt` (`P^δ(x, {x − δ}) = 1` for
`x > δ`), and `bwdTimeCts_add_of_no_renewal` (the backward chain ages by `δ` when no renewal
occurs).

**Corrections.**
* (3.37) has the wrong sign: `∫ G(A/r + y/r) H(dy)` is the law of `J − S`. The increment law is
  `∫ G{t : y − rt ∈ A} H(dy)` (`eq_3_37`); counterexample `eq_3_37_counterexample` (`S = 0`,
  `T = 1`, `r = 1`). This repeats the sign error of the integer storage model on p. 56 (see
  `storage_increment_counterexample`).
* (3.39) has the wrong sign on `δ − x`: `P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)`.
  `eq_3_39_counterexample` uses deterministic renewals of length `1` from `x = 1/4`, `δ = 1/2`,
  where the chain moves surely to `3/4` but the printed formula gives `P^δ(1/4, {3/4}) = 0`.

**See also.** The Markov property of the `δ`-skeletons `V⁺_δ`, `V⁻_δ` for a general increment
law, the kernel (3.39) (`eq_3_39`, which proves `eq_3_39_corrected` is the kernel) and the
backward-chain probabilities of p. 70, with the corrected normalisation, are in
`RenewalSkeletons`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Matrix

/-- (3.11): the matrix `P(x, y) = Γ(y − x)` of §3.3.2 is the kernel of the recursion
`Φₙ₊₁ = Φₙ + Wₙ₊₁` on `ℤ` (`randomWalkKernel`). -/
theorem matKernel_rwMatrix (ν : Measure ℤ) [SFinite ν] :
    matKernel (rwMatrix fun k => ν {k}) = randomWalkKernel ν := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton, randomWalkKernel_apply' ν x (measurableSet_singleton y), rwMatrix]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff]
  omega

/-- (3.12)–(3.14): the matrix of random walk on the half line `ℤ₊` is the kernel of the
recursion `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` (`reflectedWalkKernel`). -/
theorem matKernel_rwhlMatrix (p : Measure ℤ) [SFinite p] :
    matKernel (rwhlMatrix fun k => p {k}) = reflectedWalkKernel p := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [reflectedWalkKernel_apply_zero, ← Measure.tsum_indicator_apply_singleton p _
      measurableSet_Iic]
    simp only [rwhlMatrix, ite_true]
    refine tsum_congr fun k => ?_
    by_cases hk : k ≤ -(x : ℤ) <;> simp [hk]
  · rw [reflectedWalkKernel_apply_pos p x y hy]
    simp [rwhlMatrix, Nat.pos_iff_ne_zero.1 hy]

/-- `q[j + 1, ∞) = Σᵢ q{i + j + 1}` for a measure on `ℕ`. -/
theorem measure_Ici_succ_eq_tsum (q : Measure ℕ) (j : ℕ) :
    q (Ici (j + 1)) = ∑' i, q {i + j + 1} := by
  have h : Ici (j + 1) = ⋃ i : ℕ, ({i + j + 1} : Set ℕ) := by
    ext m
    simp only [mem_Ici, mem_iUnion, mem_singleton_iff]
    constructor
    · intro hm
      exact ⟨m - j - 1, by omega⟩
    · rintro ⟨i, rfl⟩
      omega
  rw [h, measure_iUnion (fun a b hab => Set.disjoint_singleton.2 (by omega))
    (fun _ => measurableSet_singleton _)]

/-- The GI/M/1 matrix of Proposition 3.3.1 with `pⱼ = q{j}` is the kernel of the recursion
`Nₙ₊₁ = [Nₙ + 1 − Dₙ₊₁]⁺` (`giM1Kernel q`), `D` the number of possible service completions
in an interarrival time. -/
theorem matKernel_giM1Matrix (q : Measure ℕ) [SFinite q] :
    matKernel (giM1Matrix fun j => q {j}) = giM1Kernel q := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [giM1Kernel_apply_zero, measure_Ici_succ_eq_tsum]
    simp [giM1Matrix]
  · rw [giM1Kernel_apply' q x]
    by_cases hyx : y ≤ x + 1
    · simp only [giM1Matrix, Nat.pos_iff_ne_zero.1 hy, hyx, ite_true, ite_false]
      congr 1
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff]
      omega
    · simp only [giM1Matrix, Nat.pos_iff_ne_zero.1 hy, hyx, ite_false]
      symm
      convert measure_empty (μ := q)
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
      omega

/-- The M/G/1 matrix of Proposition 3.3.2 with `qⱼ = a{j}` is the kernel of the recursion
`N*ₙ₊₁ = [N*ₙ − 1]⁺ + Aₙ₊₁` (`mG1Kernel a`), `A` the number of arrivals in a service time. -/
theorem matKernel_mG1Matrix (a : Measure ℕ) [SFinite a] :
    matKernel (mG1Matrix fun j => a {j}) = mG1Kernel a := by
  ext1 x
  refine Measure.ext_of_singleton fun y => ?_
  rw [matKernel_singleton, mG1Kernel, recursionKernel_apply' a (measurable_of_countable _) x
    (measurableSet_singleton y)]
  by_cases hx : x = 0
  · subst hx
    simp only [mG1Matrix, ite_true]
    congr 1
    ext d
    simp only [mem_ofPred_eq, mem_singleton_iff, mG1Step]
    omega
  · by_cases hxy : x ≤ y + 1
    · simp only [mG1Matrix, hx, hxy, ite_true, ite_false]
      congr 1
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff, mG1Step]
      omega
    · simp only [mG1Matrix, hx, hxy, ite_false]
      symm
      convert measure_empty (μ := a)
      ext d
      simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, mG1Step]
      omega

/-- Proposition 3.3.3: the matrix `P(r, q) = Γ(q − αr)` is the kernel of the AR(1)
recursion `Xₙ₊₁ = αXₙ + Wₙ₊₁` on `ℚ`. -/
theorem matKernel_arMatrix (α : ℚ) (ν : Measure ℚ) [SFinite ν] :
    matKernel (arMatrix α fun q => ν {q}) = recursionKernel ν fun p : ℚ × ℚ => α * p.1 + p.2 := by
  ext1 r
  refine Measure.ext_of_singleton fun q => ?_
  rw [matKernel_singleton, recursionKernel_apply' ν (measurable_of_countable _) r
    (measurableSet_singleton q), arMatrix]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor <;> intro h <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- (3.11) derived from the recursion: if `Φₙ₊₁ = Φₙ + Wₙ₊₁` on `ℤ` with i.i.d. increments
`W ∼ Γ` independent of `Φ₀`, then `Φ` is a Markov chain with matrix `P(x, y) = Γ(y − x)`. -/
theorem randomWalkInt_isMarkovChain (ν μ : Measure ℤ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ W : ℕ → Ω → ℤ}
    (hΦ0 : Measurable (Φ 0)) (hrec : ∀ n ω, Φ (n + 1) ω = Φ n ω + W (n + 1) ω)
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W ν) :
    IsMarkovChain (matKernel (rwMatrix fun k => ν {k})) μ pr Φ := by
  rw [matKernel_rwMatrix]
  exact isMarkovChain_of_iid μ ν measurable_add_step hΦ0 hrec hinit hW

/-- Random walk on the half line `ℤ₊` (3.12)–(3.14) derived from the recursion
`Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` with i.i.d. increments independent of `Φ₀`. -/
theorem rwhl_isMarkovChain (p : Measure ℤ) [IsProbabilityMeasure p] (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ : ℕ → Ω → ℕ}
    {W : ℕ → Ω → ℤ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = ((Φ n ω : ℤ) + W (n + 1) ω).toNat)
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W p) :
    IsMarkovChain (matKernel (rwhlMatrix fun k => p {k})) μ pr Φ := by
  rw [matKernel_rwhlMatrix]
  exact isMarkovChain_of_iid μ p (measurable_of_countable reflectStep) hΦ0 hrec hinit hW

/-- **Proposition 3.3.1** (MT p. 56) derived from the recursion. If the queue length at
arrivals satisfies `Nₙ₊₁ = [Nₙ + 1 − Dₙ₊₁]⁺` where the numbers `Dₙ` of possible service
completions in successive interarrival times are i.i.d. with the mixed Poisson law
`pⱼ = ∫ e^{−rt}(rt)ʲ/j! G(dt)` and independent of `N₀`, then `N` is a Markov chain with the
GI/M/1 matrix. -/
theorem proposition_3_3_1_of_recursion (G : Measure ℝ≥0) (r : ℝ≥0) (q : Measure ℕ)
    [IsProbabilityMeasure q] (hq : ∀ j, q {j} = poissonWeight G r j) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {N D : ℕ → Ω → ℕ}
    (hN0 : Measurable (N 0)) (hrec : ∀ n ω, N (n + 1) ω = N n ω + 1 - D (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hD : IsIIDNoise pr (N 0) D q) :
    IsMarkovChain (matKernel (giM1Matrix (poissonWeight G r))) μ pr N := by
  have h : poissonWeight G r = fun j => q {j} := funext fun j => (hq j).symm
  rw [h, matKernel_giM1Matrix]
  exact isMarkovChain_of_iid μ q (measurable_of_countable giM1Step) hN0 hrec hinit hD

/-- **Proposition 3.3.2** (MT p. 57) derived from the recursion `N*ₙ₊₁ = [N*ₙ − 1]⁺ + Aₙ₊₁`
with i.i.d. arrival counts `A` of mixed Poisson law `qⱼ` (3.19), independent of `N*₀`. -/
theorem proposition_3_3_2_of_recursion (H : Measure ℝ≥0) (r : ℝ≥0) (a : Measure ℕ)
    [IsProbabilityMeasure a] (ha : ∀ j, a {j} = poissonWeight H r j) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {N A : ℕ → Ω → ℕ}
    (hN0 : Measurable (N 0)) (hrec : ∀ n ω, N (n + 1) ω = N n ω - 1 + A (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hA : IsIIDNoise pr (N 0) A a) :
    IsMarkovChain (matKernel (mG1Matrix (poissonWeight H r))) μ pr N := by
  have h : poissonWeight H r = fun j => a {j} := funext fun j => (ha j).symm
  rw [h, matKernel_mG1Matrix]
  exact isMarkovChain_of_iid μ a (measurable_of_countable mG1Step) hN0 hrec hinit hA

/-- **Proposition 3.3.1** from the primitives of the GI/M/1 queue: if `Dₙ` counts the rate-`r`
exponential services completed in an independent interarrival time `T ∼ G` (so its law is
given by `countEvent`), the queue length at arrivals is a Markov chain with the GI/M/1 matrix
with weights (3.15). -/
theorem proposition_3_3_1_derived (G : Measure ℝ≥0) [SFinite G] {r : ℝ≥0} (hr : 0 < r)
    (q : Measure ℕ) [IsProbabilityMeasure q]
    (hq : ∀ j, q {j} = (G.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure r))
      {p | p.2 ∈ countEvent j p.1})
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {N D : ℕ → Ω → ℕ} (hN0 : Measurable (N 0))
    (hrec : ∀ n ω, N (n + 1) ω = N n ω + 1 - D (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hD : IsIIDNoise pr (N 0) D q) :
    IsMarkovChain (matKernel (giM1Matrix (poissonWeight G r))) μ pr N :=
  proposition_3_3_1_of_recursion G r q (fun j => (hq j).trans (eq_3_15 G hr j)) μ hN0 hrec
    hinit hD

/-- **Proposition 3.3.2** from the primitives of the M/G/1 queue: if `Aₙ` counts the
Poisson(`r`) arrivals in an independent service time `∼ H`, the queue length after departures
is a Markov chain with the M/G/1 matrix with weights (3.19). -/
theorem proposition_3_3_2_derived (H : Measure ℝ≥0) [SFinite H] {r : ℝ≥0} (hr : 0 < r)
    (a : Measure ℕ) [IsProbabilityMeasure a]
    (ha : ∀ j, a {j} = (H.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure r))
      {p | p.2 ∈ countEvent j p.1})
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {N A : ℕ → Ω → ℕ} (hN0 : Measurable (N 0))
    (hrec : ∀ n ω, N (n + 1) ω = N n ω - 1 + A (n + 1) ω)
    (hinit : pr.map (N 0) = μ) (hA : IsIIDNoise pr (N 0) A a) :
    IsMarkovChain (matKernel (mG1Matrix (poissonWeight H r))) μ pr N :=
  proposition_3_3_2_of_recursion H r a (fun j => (ha j).trans (eq_3_19 H hr j)) μ hN0 hrec
    hinit hA

/-- **Proposition 3.3.3** (MT p. 58) derived from the recursion: if `Xₙ₊₁ = αXₙ + Wₙ₊₁` on
`ℚ` with i.i.d. noise independent of `X₀`, then `X` is a Markov chain with matrix
`P(r, q) = Γ(q − αr)`. -/
theorem proposition_3_3_3_of_recursion (α : ℚ) (ν μ : Measure ℚ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {X W : ℕ → Ω → ℚ}
    (hX0 : Measurable (X 0)) (hrec : ∀ n ω, X (n + 1) ω = α * X n ω + W (n + 1) ω)
    (hinit : pr.map (X 0) = μ) (hW : IsIIDNoise pr (X 0) W ν) :
    IsMarkovChain (matKernel (arMatrix α fun q => ν {q})) μ pr X := by
  rw [matKernel_arMatrix]
  exact isMarkovChain_of_iid μ ν (measurable_of_countable _) hX0 hrec hinit hW

/-- The AR(1) model on `ℝ` (SLM1)–(SLM2): with i.i.d. noise independent of `X₀` it is a Markov
chain with kernel `ar1Kernel` (MT p. 58, "the Markovian nature of the process is immediate"). -/
theorem ar1_isMarkovChain (α : ℝ) (Γ μ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {X W : ℕ → Ω → ℝ}
    (hX0 : Measurable (X 0)) (hrec : ∀ n ω, X (n + 1) ω = α * X n ω + W (n + 1) ω)
    (hinit : pr.map (X 0) = μ) (hW : IsIIDNoise pr (X 0) W Γ) :
    IsMarkovChain (ar1Kernel Γ α) μ pr X :=
  isMarkovChain_of_iid μ Γ (measurable_ar1Step α) hX0 hrec hinit hW

/-- The linear state space model LSS(F, G) on `ℝⁿ` (MT (LSS1)–(LSS2)): `Xₙ₊₁ = FXₙ + GWₙ₊₁`
with i.i.d. noise independent of `X₀` is a Markov chain with kernel `lssMatrixKernel`. -/
theorem lssMatrix_isMarkovChain {n p : ℕ} (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {X : ℕ → Ω → Fin n → ℝ} {W : ℕ → Ω → Fin p → ℝ} (hX0 : Measurable (X 0))
    (hrec : ∀ k ω, X (k + 1) ω = F *ᵥ X k ω + G *ᵥ W (k + 1) ω)
    (hinit : pr.map (X 0) = μ) (hW : IsIIDNoise pr (X 0) W Γ) :
    IsMarkovChain (lssMatrixKernel Γ F G) μ pr X :=
  isMarkovChain_of_iid μ Γ (measurable_lssMatrixStep F G) hX0 hrec hinit hW

/-- The GI/G/1 waiting time chain (Lindley's recursion `Wₙ₊₁ = [Wₙ + Sₙ − Tₙ₊₁]⁺`, the residual
service model of §3.5.2 with `r = 1`): with i.i.d. pairs `(Sₙ, Tₙ₊₁) ∼ H ⊗ G` independent of
`W₀` it is a Markov chain with kernel `waitingTimeKernel`. -/
theorem waitingTime_isMarkovChain (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {pr : Measure Ω}
    [IsProbabilityMeasure pr] {Φ : ℕ → Ω → ℝ≥0} {V : ℕ → Ω → ℝ × ℝ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = Real.toNNReal (Φ n ω + (V (n + 1) ω).1 - (V (n + 1) ω).2))
    (hinit : pr.map (Φ 0) = μ) (hV : IsIIDNoise pr (Φ 0) V (H.prod G)) :
    IsMarkovChain (waitingTimeKernel H G) μ pr Φ :=
  isMarkovChain_of_iid μ (H.prod G) measurable_lindleyStep hΦ0 hrec hinit hV

/-- Random walk on `ℝ`: with i.i.d. increments independent of `Φ₀` it is a Markov chain
with kernel `P(x, A) = Γ(A − x)`. -/
theorem randomWalkReal_isMarkovChain (Γ μ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ W : ℕ → Ω → ℝ}
    (hΦ0 : Measurable (Φ 0)) (hrec : ∀ n ω, Φ (n + 1) ω = Φ n ω + W (n + 1) ω)
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W Γ) :
    IsMarkovChain (randomWalkKernel Γ) μ pr Φ :=
  isMarkovChain_of_iid μ Γ measurable_add_step hΦ0 hrec hinit hW

/-- `P(x, A) = Γ(A − x)` for random walk on `ℝ` (MT pp. 67, 69). -/
theorem randomWalkKernel_apply_image (Γ : Measure ℝ) [SFinite Γ] (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : randomWalkKernel Γ x A = Γ ((fun a => a - x) '' A) := by
  rw [randomWalkKernel_apply' Γ x hA]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨x + w, h, by ring⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

/-- **(3.35)**, MT p. 67: for random walk on the half line `[0, ∞)` and `A ⊆ (0, ∞)`,
`P(x, A) = Γ(A − x)`. -/
theorem eq_3_35 (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) {A : Set ℝ≥0} (hA : MeasurableSet A)
    (h0 : (0 : ℝ≥0) ∉ A) :
    halfLineWalkKernel Γ x A = Γ ((fun a : ℝ≥0 => (a : ℝ) - x) '' A) := by
  rw [halfLineWalkKernel_apply' Γ x hA]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h
    refine ⟨Real.toNNReal (x + w), h, ?_⟩
    have hpos : 0 < (x : ℝ) + w := by
      by_contra hn
      rw [Real.toNNReal_eq_zero.2 (not_lt.1 hn)] at h
      exact h0 h
    rw [Real.coe_toNNReal _ hpos.le]
    ring
  · rintro ⟨a, ha, rfl⟩
    have : (x : ℝ) + ((a : ℝ) - x) = a := by ring
    rwa [this, Real.toNNReal_coe]

/-- **(3.36)**, MT p. 67: `P(x, {0}) = Γ(−∞, −x]`. -/
theorem eq_3_36 (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) :
    halfLineWalkKernel Γ x {0} = Γ (Iic (-(x : ℝ))) :=
  halfLineWalkKernel_apply_zero Γ x

/-- Random walk on the half line `[0, ∞)` (§3.5.1): `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` with i.i.d.
increments independent of `Φ₀` is a Markov chain with kernel (3.35)–(3.36). -/
theorem halfLineWalk_isMarkovChain (Γ : Measure ℝ) (μ : Measure ℝ≥0) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr] {Φ : ℕ → Ω → ℝ≥0}
    {W : ℕ → Ω → ℝ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = Real.toNNReal (Φ n ω + W (n + 1) ω))
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W Γ) :
    IsMarkovChain (halfLineWalkKernel Γ) μ pr Φ :=
  isMarkovChain_of_iid μ Γ measurable_halfLineStep hΦ0 hrec hinit hW

/-- **(3.37)** corrected, MT p. 68: the increment `S − J = S − rT` of the storage model has
law `Γ(A) = ∫ G{t : y − rt ∈ A} H(dy)`. -/
theorem eq_3_37 (H G : Measure ℝ) [SFinite H] [SFinite G] (r : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ((H.prod G).map fun p => p.1 - r * p.2) A = ∫⁻ y, G {t | y - r * t ∈ A} ∂H := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - r * p.2 :=
    measurable_fst.sub (measurable_const.mul measurable_snd)
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA)]
  rfl

/-- (3.37) corrected, with `r > 0`: `Γ(A) = ∫ G((y − A)/r) H(dy)`. -/
theorem eq_3_37_div (H G : Measure ℝ) [SFinite H] [SFinite G] {r : ℝ} (hr : 0 < r)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ((H.prod G).map fun p => p.1 - r * p.2) A =
      ∫⁻ y, G ((fun a => (y - a) / r) '' A) ∂H := by
  rw [eq_3_37 H G r hA]
  refine lintegral_congr fun y => ?_
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨y - r * t, h, by field_simp; ring⟩
  · rintro ⟨a, ha, rfl⟩
    have : y - r * ((y - a) / r) = a := by field_simp; ring
    rwa [this]

/-- **Correction to (3.37)** (MT p. 68). The printed `Γ(A) = ∫ G(A/r + y/r) H(dy)` is the law
of `J − S`, not `S − J`. With `S = 0`, `T = 1` surely and `r = 1`, `S − J = −1` surely, but the
printed formula gives mass `0` to `{−1}`. -/
theorem eq_3_37_counterexample :
    ((Measure.dirac (0 : ℝ)).prod (Measure.dirac (1 : ℝ))).map (fun p => p.1 - 1 * p.2)
        {-1} ≠
      ∫⁻ y, Measure.dirac (1 : ℝ) {t | 1 * t - y ∈ ({-1} : Set ℝ)} ∂Measure.dirac (0 : ℝ) := by
  rw [eq_3_37 _ _ 1 (measurableSet_singleton _), lintegral_dirac, lintegral_dirac]
  have h1 : {t : ℝ | 0 - 1 * t ∈ ({-1} : Set ℝ)} = {1} := by
    ext t
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  have h2 : {t : ℝ | 1 * t - 0 ∈ ({-1} : Set ℝ)} = {-1} := by
    ext t
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [h1, h2, Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  norm_num

/-- The storage model (§3.5.2): the content `Φₙ₊₁ = [Φₙ + Sₙ − rTₙ₊₁]⁺` with i.i.d. pairs
`(Sₙ, Tₙ₊₁) ∼ H ⊗ G` independent of `Φ₀` is a Markov chain with kernel `storageKernel`, which
is random walk on the half line with increment law (3.37) (`storageKernel_eq_halfLineWalk`). -/
theorem storage_isMarkovChain (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (r : ℝ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {Φ : ℕ → Ω → ℝ≥0} {W : ℕ → Ω → ℝ × ℝ} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = Real.toNNReal (Φ n ω + (W (n + 1) ω).1 - r * (W (n + 1) ω).2))
    (hinit : pr.map (Φ 0) = μ) (hW : IsIIDNoise pr (Φ 0) W (H.prod G)) :
    IsMarkovChain (storageKernel H G r) μ pr Φ :=
  isMarkovChain_of_iid μ (H.prod G) (measurable_storageStep r) hΦ0 hrec hinit hW

/-- The renewal measure `U = Σₙ Γ^{n∗}` (MT p. 69). -/
noncomputable def renewalMeasure (Γ : Measure ℝ) : Measure ℝ := Measure.sum fun n => convPow Γ n

/-- `Γ^{n∗}` is a probability measure. -/
theorem isProbabilityMeasure_convPow_real (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (n : ℕ) :
    IsProbabilityMeasure (convPow Γ n) := by
  unfold convPow
  infer_instance

/-- The renewal measure is s-finite. -/
theorem sFinite_renewalMeasure (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    SFinite (renewalMeasure Γ) := by
  have : ∀ n, SFinite (convPow Γ n) := fun n => by
    have := isProbabilityMeasure_convPow_real Γ n
    infer_instance
  unfold renewalMeasure
  infer_instance

/-- `(μ ∗ ν)(A) = ∫ ν{y : s + y ∈ A} μ(ds)`. -/
theorem conv_apply_eq_lintegral (μ ν : Measure ℝ) [SFinite ν] {A : Set ℝ} (hA : MeasurableSet A) :
    (μ ∗ ν) A = ∫⁻ s, ν {y | s + y ∈ A} ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add hA, Measure.prod_apply (measurable_add hA)]
  rfl

/-- `A − s = {y : s + y ∈ A}`. -/
theorem image_sub_const_eq_setOf (s : ℝ) (A : Set ℝ) : (fun a => a - s) '' A = {y | s + y ∈ A} := by
  ext y
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨s + y, h, by ring⟩

/-- **(3.38)**, MT p. 68: `Γ₀ ∗ Γ(A) = ∫ Γ(A − s) Γ₀(ds) = ∫ Γ₀(A − s) Γ(ds)`. -/
theorem eq_3_38 (Γ₀ Γ : Measure ℝ) [SFinite Γ₀] [SFinite Γ] {A : Set ℝ}
    (hA : MeasurableSet A) :
    (Γ₀ ∗ Γ) A = ∫⁻ s, Γ ((fun a => a - s) '' A) ∂Γ₀ ∧
      (Γ₀ ∗ Γ) A = ∫⁻ s, Γ₀ ((fun a => a - s) '' A) ∂Γ := by
  simp_rw [image_sub_const_eq_setOf]
  exact ⟨conv_apply_eq_lintegral Γ₀ Γ hA,
    by rw [Measure.conv_comm, conv_apply_eq_lintegral Γ Γ₀ hA]⟩

/-- §3.5.3, MT p. 69: the delayed renewal process `Zₙ = Y₀ + ⋯ + Yₙ` with `Y₀ ∼ Γ₀` and
`Y₁, Y₂, …` i.i.d. `∼ Γ` independent of `Y₀` is a Markov chain with `P(x, A) = Γ(A − x)`. -/
theorem renewalReal_isMarkovChain (Γ Γ₀ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure Γ₀] {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Γ₀) (hY : IsIIDNoise pr (Z 0) Y Γ) :
    IsMarkovChain (randomWalkKernel Γ) Γ₀ pr Z :=
  randomWalkReal_isMarkovChain Γ Γ₀ hZ0 hrec hinit hY

/-- MT p. 68: `P(Zₙ ∈ ·) = Γ₀ ∗ Γ^{n∗}`. -/
theorem renewalReal_map_eq (Γ Γ₀ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure Γ₀] {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Γ₀) (hY : IsIIDNoise pr (Z 0) Y Γ) (n : ℕ) :
    pr.map (Z n) = Γ₀ ∗ convPow Γ n := by
  have := isMarkovKernel_randomWalkKernel Γ
  have := isProbabilityMeasure_convPow_real Γ n
  rw [(renewalReal_isMarkovChain Γ Γ₀ hZ0 hrec hinit hY).map_eq n]
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), conv_apply_eq_lintegral _ _ hA]
  refine lintegral_congr fun x => ?_
  rw [randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add x) hA]
  rfl

/-- MT p. 69: `E_{Γ₀}[number of renewals in A] = Γ₀ ∗ U(A)`. -/
theorem renewal_expected_count (Γ Γ₀ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure Γ₀] {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Γ₀) (hY : IsIIDNoise pr (Z 0) Y Γ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ ω, ∑' n, A.indicator 1 (Z n ω) ∂pr = (Γ₀ ∗ renewalMeasure Γ) A := by
  have hM := renewalReal_isMarkovChain Γ Γ₀ hZ0 hrec hinit hY
  have hZ : ∀ n, Measurable (Z n) := hM.measurable
  have := sFinite_renewalMeasure Γ
  have : ∀ n, IsProbabilityMeasure (convPow Γ n) := isProbabilityMeasure_convPow_real Γ
  rw [lintegral_tsum (f := fun n ω => A.indicator 1 (Z n ω))
    fun n => ((measurable_one.indicator hA).comp (hZ n)).aemeasurable]
  have h1 : ∀ n, ∫⁻ ω, A.indicator 1 (Z n ω) ∂pr = (Γ₀ ∗ convPow Γ n) A := fun n => by
    rw [← renewalReal_map_eq Γ Γ₀ hZ0 hrec hinit hY n, Measure.map_apply (hZ n) hA,
      ← lintegral_indicator_one ((hZ n) hA)]
    rfl
  have h2 : ∀ x, renewalMeasure Γ {y | x + y ∈ A} = ∑' n, convPow Γ n {y | x + y ∈ A} :=
    fun x => Measure.sum_apply _ (measurable_const_add x hA)
  simp_rw [h1, conv_apply_eq_lintegral _ _ hA, h2]
  exact (lintegral_tsum (f := fun n s => convPow Γ n {y | s + y ∈ A}) fun n =>
    (measurable_measure_prodMk_left (ν := convPow Γ n) (measurable_add hA)).aemeasurable).symm

/-- MT p. 69: with the first renewal at `0`, `E₀[number of renewals in A] = U(A)`. -/
theorem renewal_expected_count_undelayed (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    {pr : Measure Ω} [IsProbabilityMeasure pr] {Z Y : ℕ → Ω → ℝ}
    (hZ0 : Measurable (Z 0)) (hrec : ∀ n ω, Z (n + 1) ω = Z n ω + Y (n + 1) ω)
    (hinit : pr.map (Z 0) = Measure.dirac 0) (hY : IsIIDNoise pr (Z 0) Y Γ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ ω, ∑' n, A.indicator 1 (Z n ω) ∂pr = renewalMeasure Γ A := by
  have := sFinite_renewalMeasure Γ
  rw [renewal_expected_count Γ _ hZ0 hrec hinit hY hA, Measure.dirac_zero_conv]

/-- The candidates for `V⁺(t + δ)` are those for `V⁺(t)` shifted down by `δ`, when
`V⁺(t) > δ ≥ 0`. -/
theorem fwdTimeCts_set_eq (Z : ℕ → ℝ) {t δ : ℝ} (hδ : 0 ≤ δ) (h : δ < fwdTimeCts Z t) :
    {d | ∃ n, 1 ≤ n ∧ t + δ < Z n ∧ d = Z n - (t + δ)} =
      (fun d => d - δ) '' {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t} := by
  have hbdd : BddBelow {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t} :=
    ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  ext d
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨n, hn, htn, rfl⟩
    exact ⟨Z n - t, ⟨n, hn, by linarith, rfl⟩, by ring⟩
  · rintro ⟨e, ⟨n, hn, htn, rfl⟩, rfl⟩
    have hle : fwdTimeCts Z t ≤ Z n - t := csInf_le hbdd ⟨n, hn, htn, rfl⟩
    exact ⟨n, hn, by linarith, by ring⟩

/-- MT p. 69: if `V⁺(t) > δ ≥ 0` then `V⁺(t + δ) = V⁺(t) − δ`. -/
theorem fwdTimeCts_add_of_lt (Z : ℕ → ℝ) {t δ : ℝ} (hδ : 0 ≤ δ) (h : δ < fwdTimeCts Z t) :
    fwdTimeCts Z (t + δ) = fwdTimeCts Z t - δ := by
  set S := {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t}
  have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hne : S.Nonempty := by
    by_contra hS
    rw [not_nonempty_iff_eq_empty] at hS
    have : fwdTimeCts Z t = 0 := by
      change sInf S = 0
      rw [hS, Real.sInf_empty]
    linarith
  change sInf _ = sInf S - δ
  rw [fwdTimeCts_set_eq Z hδ h]
  exact ((Monotone.map_csInf_of_continuousAt (f := fun d : ℝ => d - δ)
    (continuous_sub_right δ).continuousAt (fun a b hab => by linarith) hne hbdd)).symm

/-- MT p. 69: the forward recurrence `δ`-skeleton moves deterministically from `x > δ` to
`x − δ`, the pathwise content of `P^δ(x, {x − δ}) = 1`. -/
theorem fwdSkeleton_succ_of_lt (Z : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (h : δ < fwdSkeleton Z δ n) : fwdSkeleton Z δ (n + 1) = fwdSkeleton Z δ n - δ := by
  unfold fwdSkeleton at *
  rw [← fwdTimeCts_add_of_lt Z hδ h]
  congr 1
  push_cast
  ring

/-- MT p. 70: if there is no renewal in `(t, t + δ]` then `V⁻(t + δ) = V⁻(t) + δ`. -/
theorem bwdTimeCts_add_of_no_renewal (Z : ℕ → ℝ) {t δ : ℝ} (hδ : 0 ≤ δ)
    (hne : ∃ n, 1 ≤ n ∧ Z n ≤ t) (hno : ∀ n, 1 ≤ n → Z n ≤ t + δ → Z n ≤ t) :
    bwdTimeCts Z (t + δ) = bwdTimeCts Z t + δ := by
  set S := {d | ∃ n, 1 ≤ n ∧ Z n ≤ t ∧ d = t - Z n}
  have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hSne : S.Nonempty := by
    obtain ⟨n, hn, hz⟩ := hne
    exact ⟨_, n, hn, hz, rfl⟩
  have hset : {d | ∃ n, 1 ≤ n ∧ Z n ≤ t + δ ∧ d = t + δ - Z n} = (fun d => d + δ) '' S := by
    ext d
    simp only [mem_ofPred_eq, mem_image, S]
    constructor
    · rintro ⟨n, hn, hz, rfl⟩
      exact ⟨t - Z n, ⟨n, hn, hno n hn hz, rfl⟩, by ring⟩
    · rintro ⟨e, ⟨n, hn, hz, rfl⟩, rfl⟩
      exact ⟨n, hn, by linarith, by ring⟩
  change sInf _ = sInf S + δ
  rw [hset]
  exact ((Monotone.map_csInf_of_continuousAt (f := fun d : ℝ => d + δ)
    (continuous_id.add continuous_const).continuousAt (fun a b hab => by linarith) hSne hbdd)).symm


/-- The product of Dirac masses at `c` is the Dirac mass at the constant tuple. -/
theorem pi_dirac_const (n : ℕ) (c : ℝ) :
    Measure.pi (fun _ : Fin n => Measure.dirac c) = Measure.dirac fun _ => c := by
  refine Measure.pi_eq (μ := fun _ : Fin n => Measure.dirac c) fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  by_cases h : ∀ i, c ∈ s i
  · have h1 : (fun _ : Fin n => c) ∈ univ.pi s := fun i _ => h i
    rw [indicator_of_mem h1]
    exact (Finset.prod_eq_one fun i _ => by rw [indicator_of_mem (h i)]; rfl).symm
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have h1 : (fun _ : Fin n => c) ∉ univ.pi s := fun hm => hi (hm i (mem_univ i))
    rw [indicator_of_notMem h1]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [indicator_of_notMem hi])).symm

/-- `(δ_c)^{n∗} = δ_{nc}`. -/
theorem convPow_dirac (c : ℝ) (n : ℕ) : convPow (Measure.dirac c) n = Measure.dirac (n * c) := by
  rw [convPow, pi_dirac_const, Measure.map_dirac' (measurable_sum_fin (G := ℝ) n)]
  simp

/-- For deterministic renewals of length `1`, the renewal measure on `[0, b]`, `b < 1`, is
the unit mass at `0`. -/
theorem setLIntegral_renewalMeasure_dirac_one {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc 0 b, f t ∂renewalMeasure (Measure.dirac 1) = f 0 := by
  rw [← lintegral_indicator measurableSet_Icc, renewalMeasure, lintegral_sum_measure]
  simp_rw [convPow_dirac, mul_one, lintegral_dirac]
  rw [tsum_eq_single 0 fun n hn => ?_]
  · simp [hb0]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    rw [indicator_of_notMem]
    simp only [mem_Icc, not_and, not_le]
    intro _
    linarith

/-- The right side of (3.39) as printed: `∫_{[0, δ−x]} U(dt) Γ(A − [δ − x] − t)`. -/
noncomputable def eq_3_39_printed (Γ : Measure ℝ) (δ x : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc 0 (δ - x), Γ ((fun a => a - (δ - x) - t) '' A) ∂renewalMeasure Γ

/-- The corrected right side of (3.39): `∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)`. -/
noncomputable def eq_3_39_corrected (Γ : Measure ℝ) (δ x : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc 0 (δ - x), Γ ((fun a => a + (δ - x) - t) '' A) ∂renewalMeasure Γ

/-- **Correction to (3.39)** (MT p. 70). Take deterministic renewals of length `1`
(`Γ = δ₁`), `δ = 1/2` and current forward recurrence time `x = 1/4`. The epochs are
`1/4, 5/4, …`, so `V⁺` moves surely from `1/4` to `3/4`: `P^δ(1/4, {3/4}) = 1`. The printed
formula gives `0` at `{3/4}`; the corrected one gives `1`. -/
theorem eq_3_39_counterexample :
    fwdTimeCts (fun n => (n : ℝ) - 3 / 4) 0 = 1 / 4 ∧
      fwdTimeCts (fun n => (n : ℝ) - 3 / 4) (0 + 1 / 2) = 3 / 4 ∧
      eq_3_39_printed (Measure.dirac 1) (1 / 2) (1 / 4) {3 / 4} = 0 ∧
      eq_3_39_corrected (Measure.dirac 1) (1 / 2) (1 / 4) {3 / 4} = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine IsLeast.csInf_eq ⟨⟨1, le_rfl, by norm_num, by norm_num⟩, ?_⟩
    rintro d ⟨n, hn, -, rfl⟩
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · refine IsLeast.csInf_eq ⟨⟨2, by norm_num, by norm_num, by norm_num⟩, ?_⟩
    rintro d ⟨n, -, hlt, rfl⟩
    have h1 : (1 : ℝ) < n := by linarith
    have h2 : 1 < n := by exact_mod_cast h1
    have : (2 : ℝ) ≤ n := by exact_mod_cast h2
    linarith
  · rw [eq_3_39_printed, setLIntegral_renewalMeasure_dirac_one (by norm_num) (by norm_num),
      image_singleton, Measure.dirac_apply' _ (measurableSet_singleton _)]
    norm_num
  · rw [eq_3_39_corrected, setLIntegral_renewalMeasure_dirac_one (by norm_num) (by norm_num),
      image_singleton, Measure.dirac_apply' _ (measurableSet_singleton _)]
    norm_num

end MeynTweedie.GeneralizedDrift
