/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.Helly
import ConvergenceApplications.TransitionFunctions

/-!
# The Feller property and existence of invariant measures (SLP §12.4, pp. 375–378)

* **Exercise 12.7**: on any metric space, the Feller property `T[C(S)] ⊆ C(S)` is equivalent to
  `sₙ → s ⇒ P(sₙ, ·) ⇒ P(s, ·)` and to `λₙ ⇒ λ ⇒ T*λₙ ⇒ T*λ` (`ex_12_7`);
* **Exercise 12.8**: the cycle `s ↦ 1 - s` on `[0, 1]` is Feller; from `δ_s`, `s ≠ 1/2`, the even
  and odd iterates converge to the distinct non-invariant `δ_s`, `δ_{1-s}`; the invariant
  measures are exactly the measures symmetric about `1/2` (`ex_12_8a`–`ex_12_8c`);
* the limit step shared by Theorems 12.10 and 12.12 and Exercise 12.12 (`invariant_of_convWeak`):
  if `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
  invariant;
* **Theorem 12.10**: on a compact metric space a Feller transition function has an invariant
  probability measure, through the Cesàro averages of `T*ⁿδ_s` and Prokhorov's theorem. (The book
  works on compact `S ⊆ ℝˡ` and invokes Helly on `ℝˡ`; any compact metric space works. `S` must be
  nonempty.)
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
/-- Bounded continuous functions are bounded by their sup norm. -/
theorem bcf_abs_le_norm (f : S →ᵇ ℝ) (s : S) : |f s| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s

/-- Point masses at a convergent sequence converge weakly. -/
theorem convWeak_dirac {s : ℕ → S} {s₀ : S} (hs : Tendsto s atTop (𝓝 s₀)) :
    ConvWeak (fun n => Measure.dirac (s n)) (Measure.dirac s₀) := fun f => by
  simp only [integral_dirac]
  exact (f.continuous.tendsto s₀).comp hs

variable (κ : Kernel S S) [IsMarkovKernel κ]

omit [MetricSpace S] [BorelSpace S] [IsMarkovKernel κ] in
theorem adjointOp_dirac (s : S) : adjointOp κ (Measure.dirac s) = κ s :=
  Measure.dirac_bind κ.measurable s

/-- `∫ Tf dλ = ∫ f d(T*λ)` for bounded continuous `f` (Theorem 8.3). -/
theorem integral_markovOpR (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, markovOpR κ f s ∂lam = ∫ s, f s ∂adjointOp κ lam :=
  theorem_8_3_cor κ lam f.continuous.measurable (bcf_abs_le_norm f)

/-- Under the Feller property, `Tf` as a bounded continuous function. -/
noncomputable def fellerBCF {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ) :
    S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨markovOpR κ f, hF f f.continuous ⟨‖f‖, bcf_abs_le_norm f⟩⟩ (2 * ‖f‖) fun x y => by
      have hx := (theorem_8_1_cor κ f.continuous.measurable (bcf_abs_le_norm f)).2 x
      have hy := (theorem_8_1_cor κ f.continuous.measurable (bcf_abs_le_norm f)).2 y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      linarith [abs_sub (markovOpR κ f x) (markovOpR κ f y)]

theorem fellerBCF_apply {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : fellerBCF hF f s = markovOpR κ f s := rfl

/-- **Exercise 12.7.** On a metric space the following are equivalent: (a) the Feller property;
(b) `sₙ → s` implies `P(sₙ, ·) ⇒ P(s, ·)`; (c) `λₙ ⇒ λ` implies `T*λₙ ⇒ T*λ`. -/
theorem ex_12_7 :
    (IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀)) ∧
    (IsFeller κ ↔ ∀ (ls : ℕ → Measure S) (lam : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
      IsProbabilityMeasure lam → ConvWeak ls lam →
        ConvWeak (fun n => adjointOp κ (ls n)) (adjointOp κ lam)) := by
  have hab : IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀) := by
    constructor
    · intro hF s s₀ hs f
      exact ((hF f f.continuous ⟨‖f‖, bcf_abs_le_norm f⟩).tendsto s₀).comp hs
    · intro h f hf ⟨M, hM⟩
      rw [continuous_iff_seqContinuous]
      intro s s₀ hs
      exact h s s₀ hs (BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        linarith [abs_sub (f x) (f y), hM x, hM y])
  refine ⟨hab, ⟨fun hF ls lam hls hlam h f => ?_, fun h => hab.2 fun s s₀ hs => ?_⟩⟩
  · rw [← integral_markovOpR κ lam f]
    exact (h (fellerBCF hF f)).congr fun n => integral_markovOpR κ (ls n) f
  · have := h _ _ (fun n => inferInstance) inferInstance (convWeak_dirac hs)
    simpa only [adjointOp_dirac] using this

/-! ### Exercise 12.8: the cycle `s ↦ 1 - s` -/

/-- The transition function of `sₜ₊₁ = 1 - sₜ` on `[0, 1]`: `P(s, ·) = δ_{1-s}`. -/
noncomputable def flipKernel : Kernel unitInterval unitInterval :=
  Kernel.deterministic unitInterval.symm unitInterval.continuous_symm.measurable

theorem isMarkovKernel_flipKernel : IsMarkovKernel flipKernel := by
  unfold flipKernel; infer_instance

theorem adjointOp_flip (μ : Measure unitInterval) :
    adjointOp flipKernel μ = μ.map unitInterval.symm :=
  Measure.deterministic_comp_eq_map _

theorem adjointOp_flip_dirac (s : unitInterval) :
    adjointOp flipKernel (Measure.dirac s) = Measure.dirac (unitInterval.symm s) := by
  rw [adjointOp_flip, Measure.map_dirac' unitInterval.continuous_symm.measurable]

/-- **Exercise 12.8a.** `P(s, ·) = δ_{1-s}`, and `P` has the Feller property. -/
theorem ex_12_8a : (∀ s, flipKernel s = Measure.dirac (unitInterval.symm s)) ∧
    IsFeller flipKernel := by
  have hP : ∀ s, flipKernel s = Measure.dirac (unitInterval.symm s) := fun s =>
    Kernel.deterministic_apply _ s
  refine ⟨hP, fun f hf _ => ?_⟩
  have : markovOpR flipKernel f = f ∘ unitInterval.symm := funext fun s => by
    simp only [markovOpR, hP, integral_dirac, Function.comp_apply]
  rw [this]
  exact hf.comp unitInterval.continuous_symm

theorem iterate_flip_dirac (s : unitInterval) (n : ℕ) :
    (adjointOp flipKernel)^[2 * n] (Measure.dirac s) = Measure.dirac s ∧
      (adjointOp flipKernel)^[2 * n + 1] (Measure.dirac s) =
        Measure.dirac (unitInterval.symm s) := by
  induction n with
  | zero => exact ⟨rfl, adjointOp_flip_dirac s⟩
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h2, Function.iterate_succ_apply', ih.2, adjointOp_flip_dirac, unitInterval.symm_symm,
      Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2, adjointOp_flip_dirac,
      unitInterval.symm_symm, adjointOp_flip_dirac]
    exact ⟨rfl, rfl⟩

theorem symm_ne_self {s : unitInterval} (hs : (s : ℝ) ≠ 1 / 2) : unitInterval.symm s ≠ s := by
  intro h
  have := congrArg Subtype.val h
  rw [unitInterval.coe_symm_eq] at this
  exact hs (by linarith)

/-- **Exercise 12.8b.** From `δ_s` with `s ≠ 1/2`, the even iterates converge to `δ_s` and the odd
ones to `δ_{1-s}`; the two limits differ and neither is invariant. -/
theorem ex_12_8b (s : unitInterval) (hs : (s : ℝ) ≠ 1 / 2) :
    ConvWeak (fun n => (adjointOp flipKernel)^[2 * n] (Measure.dirac s)) (Measure.dirac s) ∧
      ConvWeak (fun n => (adjointOp flipKernel)^[2 * n + 1] (Measure.dirac s))
        (Measure.dirac (unitInterval.symm s)) ∧
      Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) ∧
      adjointOp flipKernel (Measure.dirac s) ≠ Measure.dirac s ∧
      adjointOp flipKernel (Measure.dirac (unitInterval.symm s)) ≠
        Measure.dirac (unitInterval.symm s) := by
  have hne : Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) := fun h =>
    symm_ne_self hs (dirac_eq_dirac_iff.1 h).symm
  refine ⟨fun f => ?_, fun f => ?_, hne, ?_, ?_⟩
  · simp only [fun n => (iterate_flip_dirac s n).1]; exact tendsto_const_nhds
  · simp only [fun n => (iterate_flip_dirac s n).2]; exact tendsto_const_nhds
  · rw [adjointOp_flip_dirac]; exact hne.symm
  · rw [adjointOp_flip_dirac, unitInterval.symm_symm]; exact hne

/-- **Exercise 12.8c.** The invariant measures are exactly the measures symmetric about `1/2`;
among them are `δ_{1/2}` and `½(δ_s + δ_{1-s})` for every `s`, so there are infinitely many. -/
theorem ex_12_8c :
    (∀ μ : Measure unitInterval, adjointOp flipKernel μ = μ ↔ μ.map unitInterval.symm = μ) ∧
      ∀ s : unitInterval, adjointOp flipKernel
        ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s))) =
          (2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s)) := by
  refine ⟨fun μ => by rw [adjointOp_flip], fun s => ?_⟩
  have hm := unitInterval.continuous_symm.measurable
  rw [adjointOp_flip, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm, unitInterval.symm_symm, add_comm]
  exact hm.aemeasurable

/-! ### Invariant limits and Theorem 12.10 -/

variable {κ}

omit [MetricSpace S] [BorelSpace S] in
theorem isProbabilityMeasure_iterate (lam : Measure S) [IsProbabilityMeasure lam] (n : ℕ) :
    IsProbabilityMeasure ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure lam)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (theorem_8_2 κ _).1

/-- If `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
invariant under a Feller `P` (the limit step of Theorem 12.10). -/
theorem invariant_of_convWeak (hF : IsFeller κ) {ν : ℕ → Measure S}
    [∀ n, IsProbabilityMeasure (ν n)] {μ : Measure S} [IsProbabilityMeasure μ]
    (hconv : ConvWeak ν μ)
    (hdiff : ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ν n - ∫ s, f s ∂adjointOp κ (ν n))
      atTop (𝓝 0)) : adjointOp κ μ = μ := by
  have : IsProbabilityMeasure (adjointOp κ μ) := (theorem_8_2 κ μ).1
  refine theorem_12_6_cor2 fun f => ?_
  rw [← integral_markovOpR κ μ f]
  have h1 : Tendsto (fun n => ∫ s, f s ∂adjointOp κ (ν n)) atTop (𝓝 (∫ s, f s ∂μ)) := by
    have := (hconv f).sub (hdiff f)
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  exact tendsto_nhds_unique ((hconv (fellerBCF hF f)).congr fun n =>
    integral_markovOpR κ (ν n) f) h1

/-- **Theorem 12.10.** On a nonempty compact metric space, a transition function with the Feller
property has an invariant probability measure. -/
theorem theorem_12_10 [CompactSpace S] [Nonempty S] (hF : IsFeller κ) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  have : TopologicalSpace.SeparableSpace S := inferInstance
  set lam₀ := Measure.dirac (Classical.arbitrary S)
  set L : ℕ → Measure S := fun n => (adjointOp κ)^[n] lam₀
  have hL : ∀ n, IsProbabilityMeasure (L n) := fun n => isProbabilityMeasure_iterate lam₀ n
  have hLs : ∀ n, L (n + 1) = adjointOp κ (L n) := fun n => Function.iterate_succ_apply' _ _ _
  set c : ℕ → ℝ≥0∞ := fun N => ((N : ℝ≥0∞) + 1)⁻¹
  have hc : ∀ N, (c N).toReal = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [c, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
    simp
  set avg : ℕ → Measure S := fun N => c N • ∑ n ∈ Finset.range (N + 1), L n
  have havg : ∀ N, IsProbabilityMeasure (avg N) := fun N => ⟨by
    simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul, c]
    push_cast
    exact ENNReal.inv_mul_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top N, ENNReal.one_ne_top⟩)⟩
  have hint : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂avg N =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L n := fun N g => by
    simp only [avg]
    rw [integral_smul_measure, integral_finsetSum_measure fun n _ => g.integrable _, hc,
      smul_eq_mul]
  have hintT : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L (n + 1) := fun N g => by
    rw [← integral_markovOpR κ (avg N) g]
    change ∫ s, fellerBCF hF g s ∂avg N = _
    rw [hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hLs, ← integral_markovOpR κ (L n) g]
    rfl
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight avg fun ε hε =>
    ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((avg ∘ φ) n) := fun n => havg (φ n)
  refine ⟨μ, hμ, invariant_of_convWeak hF hconv fun f => ?_⟩
  have hdiff : ∀ N, ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * (∫ s, f s ∂L 0 - ∫ s, f s ∂L (N + 1)) := fun N => by
    rw [hint, hintT, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hbd : ∀ n, |∫ s, f s ∂L n| ≤ ‖f‖ := fun n => by
    rw [← Real.norm_eq_abs]
    exact f.norm_integral_le_norm (L n)
  have hlim : Tendsto (fun N : ℕ => ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N)) atTop
      (𝓝 0) := by
    simp_rw [hdiff]
    refine squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖)) (fun N => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      gcongr
      linarith [abs_sub (∫ s, f s ∂L 0) (∫ s, f s ∂L (N + 1)), hbd 0, hbd (N + 1)]
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))).mul_const (2 * ‖f‖)
  exact hlim.comp hφ.tendsto_atTop

end StokeyLucasPrescott.ConvergenceApplications
