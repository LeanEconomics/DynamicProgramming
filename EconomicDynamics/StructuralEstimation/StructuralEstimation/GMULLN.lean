/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMBasic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# The uniform law of large numbers behind Theorem 12.1.1 (Miao, §12.1, pp. 388–390)

Miao, p. 388 ("when a law of large numbers applies, we can replace the population moment by the
empirical moment") and p. 389 (the proof of Theorem 12.1.1 is referred to Hall 2005, p. 68, whose
key step is that `Q_T → Q₀` uniformly on `Θ`). We prove, from Birkhoff's ergodic theorem
(`theorem_4_1_1_ergodic`, Chapter 4), that for a stationary ergodic process (Assumptions 12.1.1,
12.1.5), a compact `Θ` (12.1.6), `h(x, ·)` continuous on `Θ` (12.1.2) and an integrable envelope
(12.1.7),

`sup_{θ∈Θ} ‖g_T(θ) − E h(x₀, θ)‖ → 0` almost surely (`gm_ulln`, `TendstoUniformlyOn`).

The proof is the classical bracketing argument: for `θ₀ ∈ Θ` and `δ > 0` the modulus
`Δ(x) = sup {|f(x, c) − f(x, θ₀)| : c ∈ C, |c − θ₀| < δ}` over a countable dense `C ⊆ Θ` is
measurable, dominates the oscillation of `f(x, ·)` on the `δ`-ball (`gm_abs_sub_le_modulus`),
and `E Δ(x₀) → 0` as `δ → 0` by dominated convergence (`gm_exists_modulus_lt`); a finite cover of
`Θ` by such balls and Birkhoff's theorem for the finitely many functions involved finish the
argument (`gm_ulln_scalar_eps`).

Also: the population moment `θ ↦ E h(x₀, θ)` is finite and continuous on `Θ`
(`gm_continuousOn_popMoment`), so the second half of Assumption 12.1.2 follows from the first half
and Assumption 12.1.7.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Miao, p. 388 (the law of large numbers used for `g_T`): for a stationary ergodic process and
a measurable `φ` with `E|φ(x₀)| < ∞`, `(1/N) Σ_{t<N} φ(x_t) → E φ(x₀)` almost surely; Birkhoff's
theorem (`theorem_4_1_1_ergodic`) on path space. -/
theorem gm_ergodic_avg {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {φ : E → ℝ} (hφ : Measurable φ) (hint : Integrable (fun ω => φ (X 0 ω)) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, φ (X t ω)) atTop
      (𝓝 (∫ ω, φ (X 0 ω) ∂P)) := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hfm : Measurable (fun y : ℕ → E => φ (y 0)) := hφ.comp (measurable_pi_apply 0)
  have hf : Integrable (fun y : ℕ → E => φ (y 0)) (pathLaw P X) :=
    (integrable_map_measure hfm.aestronglyMeasurable hΦ.aemeasurable).2 hint
  have h := theorem_4_1_1_ergodic hmp ((isErgodicProcess_iff_isErgodic hX hst).1 herg) hfm hf
  have hE : ∫ y, (fun y : ℕ → E => φ (y 0)) y ∂pathLaw P X = ∫ ω, φ (X 0 ω) ∂P :=
    integral_map hΦ.aemeasurable hfm.aestronglyMeasurable
  rw [hE] at h
  filter_upwards [ae_of_ae_map hΦ.aemeasurable h] with ω hω
  refine hω.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [iterate_shift_one, shift_apply, add_zero]
  rfl

/-- If `φ` is continuous on `Θ`, `S ⊆ Θ`, `θ ∈ Θ ∩ closure S` and `φ ≤ M` on `S`, then
`φ θ ≤ M`. -/
theorem gm_le_of_mem_closure {α : Type*} [TopologicalSpace α] {S Θ : Set α} (hS : S ⊆ Θ)
    {φ : α → ℝ} (hφ : ContinuousOn φ Θ) {θ : α} (hθ : θ ∈ Θ) (hcl : θ ∈ closure S) {M : ℝ}
    (hM : ∀ c ∈ S, φ c ≤ M) : φ θ ≤ M := by
  have h1 := ((hφ θ hθ).mono hS).mem_closure_image hcl
  have hsub : φ '' S ⊆ Set.Iic M := by
    rintro _ ⟨c, hc, rfl⟩
    exact hM c hc
  exact closure_minimal hsub isClosed_Iic h1

/-- The modulus `Δ(x) = sup {|f(x, c) − f(x, θ₀)| : c ∈ C, |c − θ₀| < δ}` (a countable
supremum). -/
noncomputable def gm_modulus {k : ℕ} (C : Set (Fin k → ℝ)) (f : E → (Fin k → ℝ) → ℝ)
    (θ₀ : Fin k → ℝ) (δ : ℝ) (x : E) : ℝ :=
  ⨆ c : ↥(C ∩ Metric.ball θ₀ δ), |f x c - f x θ₀|

omit [MeasurableSpace E] in
theorem gm_modulus_nonneg {k : ℕ} (C : Set (Fin k → ℝ)) (f : E → (Fin k → ℝ) → ℝ)
    (θ₀ : Fin k → ℝ) (δ : ℝ) (x : E) : 0 ≤ gm_modulus C f θ₀ δ x :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [MeasurableSpace E] in
theorem gm_modulus_le {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCΘ : C ⊆ Θ) {f : E → (Fin k → ℝ) → ℝ}
    {D : E → ℝ} (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) (δ : ℝ)
    (x : E) : gm_modulus C f θ₀ δ x ≤ 2 * D x := by
  have hD : 0 ≤ D x := (abs_nonneg _).trans (hdom x θ₀ hθ₀)
  refine Real.iSup_le (fun c => ?_) (by linarith)
  have h1 := hdom x c (hCΘ c.2.1)
  have h2 := hdom x θ₀ hθ₀
  have := abs_sub (f x c) (f x θ₀)
  linarith

theorem gm_measurable_modulus {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCc : C.Countable)
    (hCΘ : C ⊆ Θ) {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) (δ : ℝ) : Measurable (gm_modulus C f θ₀ δ) := by
  have : Countable ↥(C ∩ Metric.ball θ₀ δ) := (hCc.mono Set.inter_subset_left).to_subtype
  exact Measurable.iSup fun c =>
    continuous_abs.measurable.comp ((hfm c (hCΘ c.2.1)).sub (hfm θ₀ hθ₀))

omit [MeasurableSpace E] in
/-- The modulus dominates the oscillation of `f(x, ·)` on `Θ ∩ B(θ₀, δ)`. -/
theorem gm_abs_sub_le_modulus {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCΘ : C ⊆ Θ)
    (hΘC : Θ ⊆ closure C) {f : E → (Fin k → ℝ) → ℝ} (hfc : ∀ x, ContinuousOn (f x) Θ)
    {D : E → ℝ} (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) {δ : ℝ}
    (x : E) {θ : Fin k → ℝ} (hθ : θ ∈ Θ) (hd : dist θ θ₀ < δ) :
    |f x θ - f x θ₀| ≤ gm_modulus C f θ₀ δ x := by
  have hcl : θ ∈ closure (C ∩ Metric.ball θ₀ δ) := by
    have h := Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball.2 hd, hΘC hθ⟩
    rwa [Set.inter_comm] at h
  have hφ : ContinuousOn (fun θ' => |f x θ' - f x θ₀|) Θ :=
    ((hfc x).sub continuousOn_const).abs
  refine gm_le_of_mem_closure ((Set.inter_subset_left).trans hCΘ) hφ hθ hcl fun c hc => ?_
  have hbdd : BddAbove (Set.range fun c : ↥(C ∩ Metric.ball θ₀ δ) => |f x c - f x θ₀|) := by
    refine ⟨2 * D x, ?_⟩
    rintro _ ⟨c', rfl⟩
    have h1 := hdom x c' (hCΘ c'.2.1)
    have h2 := hdom x θ₀ hθ₀
    have := abs_sub (f x c') (f x θ₀)
    simp only
    linarith
  exact le_ciSup (f := fun c : ↥(C ∩ Metric.ball θ₀ δ) => |f x c - f x θ₀|) hbdd ⟨c, hc⟩

/-- Dominated convergence: `E Δ(x₀) → 0` as the radius shrinks, so some radius makes it
smaller than any `ε > 0`. -/
theorem gm_exists_modulus_lt {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCc : C.Countable) (hCΘ : C ⊆ Θ)
    {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    (hfc : ∀ x, ContinuousOn (f x) Θ) {D : E → ℝ}
    (hDi : Integrable (fun ω => D (X 0 ω)) P) (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x)
    {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∫ ω, gm_modulus C f θ₀ δ (X 0 ω) ∂P < ε := by
  have hlim : Tendsto (fun n : ℕ => ∫ ω, gm_modulus C f θ₀ (1 / ((n : ℝ) + 1)) (X 0 ω) ∂P)
      atTop (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => 2 * D (X 0 ω)) (fun n => ?_)
      (hDi.const_mul 2) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact ((gm_measurable_modulus hCc hCΘ hfm hθ₀ _).comp (hX 0)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (gm_modulus_nonneg _ _ _ _ _)]
      exact gm_modulus_le hCΘ hdom hθ₀ _ _
    · rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨r, hr, hcont⟩ := Metric.continuousWithinAt_iff.1 (hfc (X 0 ω) θ₀ hθ₀) (η / 2)
        (by linarith)
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
      refine ⟨N, fun n hn => ?_⟩
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have hM : gm_modulus C f θ₀ (1 / ((n : ℝ) + 1)) (X 0 ω) ≤ η / 2 := by
        refine Real.iSup_le (fun c => ?_) (by linarith)
        have hc := Metric.mem_ball.1 c.2.2
        have := hcont (hCΘ c.2.1) (by linarith)
        rw [Real.dist_eq] at this
        exact this.le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (gm_modulus_nonneg _ _ _ _ _)]
      linarith
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- The uniform law of large numbers at a fixed tolerance `ε`: almost surely, eventually
`|E f(x₀, θ) − (1/T) Σ_{t<T} f(x_t, θ)| < ε` for all `θ ∈ Θ` simultaneously. -/
theorem gm_ulln_scalar_eps {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    (hfc : ∀ x, ContinuousOn (f x) Θ) {D : E → ℝ}
    (hDi : Integrable (fun ω => D (X 0 ω)) P) (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ T : ℕ in atTop, ∀ θ ∈ Θ,
      dist (∫ ω', f (X 0 ω') θ ∂P) ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (X t ω) θ) < ε := by
  obtain ⟨C, hCΘ, hCc, hΘC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Θ).exists_countable_dense_subset
  have hε3 : 0 < ε / 3 := by linarith
  have hδ : ∀ θ₀ : Fin k → ℝ, ∃ δ > 0, θ₀ ∈ Θ →
      ∫ ω, gm_modulus C f θ₀ δ (X 0 ω) ∂P < ε / 3 := by
    intro θ₀
    by_cases hθ₀ : θ₀ ∈ Θ
    · obtain ⟨δ, hδ, h⟩ := gm_exists_modulus_lt hX hCc hCΘ hfm hfc hDi hdom hθ₀ hε3
      exact ⟨δ, hδ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hθ₀⟩
  choose δ hδpos hδint using hδ
  obtain ⟨t, htΘ, hcov⟩ := hΘ.elim_nhds_subcover (fun θ₀ => Metric.ball θ₀ (δ θ₀))
    (fun θ₀ _ => Metric.ball_mem_nhds θ₀ (hδpos θ₀))
  have hint : ∀ θ ∈ Θ, Integrable (fun ω => f (X 0 ω) θ) P := fun θ hθ =>
    Integrable.mono' hDi ((hfm θ hθ).comp (hX 0)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hdom _ θ hθ)
  have hintΔ : ∀ θ₀ ∈ Θ, Integrable (fun ω => gm_modulus C f θ₀ (δ θ₀) (X 0 ω)) P :=
    fun θ₀ hθ₀ => Integrable.mono' (hDi.const_mul 2)
      ((gm_measurable_modulus hCc hCΘ hfm hθ₀ _).comp (hX 0)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gm_modulus_nonneg _ _ _ _ _)]
        exact gm_modulus_le hCΘ hdom hθ₀ _ _)
  have hae : ∀ᵐ ω ∂P, ∀ i : ↥t,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ s ∈ Finset.range N, f (X s ω) (i : Fin k → ℝ)) atTop
        (𝓝 (∫ ω, f (X 0 ω) (i : Fin k → ℝ) ∂P)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ s ∈ Finset.range N,
        gm_modulus C f i (δ i) (X s ω)) atTop
        (𝓝 (∫ ω, gm_modulus C f i (δ i) (X 0 ω) ∂P)) := by
    refine ae_all_iff.2 fun i => ?_
    have hi := htΘ i i.2
    exact (gm_ergodic_avg hX hst herg (hfm i hi) (hint i hi)).and
      (gm_ergodic_avg hX hst herg (gm_measurable_modulus hCc hCΘ hfm hi _) (hintΔ i hi))
  filter_upwards [hae] with ω hω
  have hev : ∀ᶠ T : ℕ in atTop, ∀ i : ↥t,
      dist ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) (i : Fin k → ℝ))
        (∫ ω, f (X 0 ω) (i : Fin k → ℝ) ∂P) < ε / 3 ∧
      (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, gm_modulus C f i (δ i) (X s ω) < ε / 3 := by
    refine Filter.eventually_all.2 fun i => ?_
    exact (Metric.tendsto_nhds.1 (hω i).1 _ hε3).and
      ((hω i).2.eventually_lt_const (hδint i (htΘ i i.2)))
  filter_upwards [hev] with T hT θ hθ
  obtain ⟨θ₀, hθ₀t, hball⟩ := Set.mem_iUnion₂.1 (hcov hθ)
  have hθ₀ := htΘ θ₀ hθ₀t
  have hd := Metric.mem_ball.1 hball
  obtain ⟨h1, h2⟩ := hT ⟨θ₀, hθ₀t⟩
  simp only at h1 h2
  rw [Real.dist_eq] at h1 ⊢
  -- the empirical oscillation
  have hosc : |(T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ -
      (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ₀| ≤
      (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, gm_modulus C f θ₀ (δ θ₀) (X s ω) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by positivity)
    exact Finset.sum_le_sum fun s _ =>
      gm_abs_sub_le_modulus hCΘ hΘC hfc hdom hθ₀ _ hθ hd
  -- the population oscillation
  have hpop : |∫ ω, f (X 0 ω) θ₀ ∂P - ∫ ω, f (X 0 ω) θ ∂P| ≤
      ∫ ω, gm_modulus C f θ₀ (δ θ₀) (X 0 ω) ∂P := by
    rw [← integral_sub (hint θ₀ hθ₀) (hint θ hθ)]
    refine abs_integral_le_integral_abs.trans (integral_mono ((hint θ₀ hθ₀).sub
      (hint θ hθ)).abs (hintΔ θ₀ hθ₀) fun ω => ?_)
    rw [abs_sub_comm]
    exact gm_abs_sub_le_modulus hCΘ hΘC hfc hdom hθ₀ _ hθ hd
  have hδ3 := hδint θ₀ hθ₀
  have key := abs_sub_le (∫ ω, f (X 0 ω) θ ∂P) (∫ ω, f (X 0 ω) θ₀ ∂P)
    ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ)
  have key2 := abs_sub_le (∫ ω, f (X 0 ω) θ₀ ∂P)
    ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ₀)
    ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ)
  rw [abs_sub_comm] at hpop h1 hosc
  linarith

/-- The uniform law of large numbers (scalar case): almost surely
`sup_{θ∈Θ} |(1/T) Σ_{t<T} f(x_t, θ) − E f(x₀, θ)| → 0`. -/
theorem gm_ulln_scalar {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    (hfc : ∀ x, ContinuousOn (f x) Θ) {D : E → ℝ}
    (hDi : Integrable (fun ω => D (X 0 ω)) P) (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun (T : ℕ) θ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (X t ω) θ)
      (fun θ => ∫ ω', f (X 0 ω') θ ∂P) atTop Θ := by
  have h := ae_all_iff.2 fun m : ℕ =>
    gm_ulln_scalar_eps hX hst herg hΘ hfm hfc hDi hdom (ε := 1 / ((m : ℝ) + 1)) (by positivity)
  filter_upwards [h] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with T hT θ hθ
  exact (hT θ hθ).trans hm

/-- **Uniform law of large numbers** (Miao, pp. 388–390, the step behind Theorem 12.1.1). Under
Assumptions 12.1.1, 12.1.2 (continuity of `h` in `θ`), 12.1.5, 12.1.6 and 12.1.7, almost surely
`sup_{θ∈Θ} ‖g_T(θ) − E h(x₀, θ)‖ → 0`. -/
theorem gm_ulln {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hdom : Assumption_12_1_7 P X h Θ) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun T θ => gm_sampleMoment X h T ω θ)
      (gm_popMoment P X h) atTop Θ := by
  obtain ⟨D, -, hDi, hD⟩ := hdom
  have h1 := ae_all_iff.2 fun i : Fin q =>
    gm_ulln_scalar hX hst herg hΘ (f := fun x θ => h x θ i)
      (fun θ hθ => measurable_pi_iff.1 (hm θ hθ) i)
      (fun x => continuousOn_pi.1 (hc x) i) hDi
      (fun x θ hθ => (norm_le_pi_norm (h x θ) i).trans (hD x θ hθ))
  filter_upwards [h1] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := Filter.eventually_all.2 fun i : Fin q =>
    (Metric.tendstoUniformlyOn_iff.1 (hω i)) ε hε
  filter_upwards [hev] with T hT θ hθ
  exact (dist_pi_lt_iff hε).2 fun i => hT i θ hθ

/-- Miao, Assumption 12.1.2 (p. 387): under Assumption 12.1.7, continuity of `h(x, ·)` on `Θ`
makes `θ ↦ E h(x₀, θ)` continuous on `Θ` (dominated convergence). -/
theorem gm_continuousOn_popMoment {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ) (hc : ∀ x, ContinuousOn (h x) Θ)
    (hdom : Assumption_12_1_7 P X h Θ) : ContinuousOn (gm_popMoment P X h) Θ := by
  obtain ⟨D, -, hDi, hD⟩ := hdom
  refine continuousOn_pi.2 fun i => ?_
  refine continuousOn_of_dominated (F := fun θ ω => h (X 0 ω) θ i)
    (fun θ hθ => ((measurable_pi_iff.1 (hm θ hθ) i).comp (hX 0)).aestronglyMeasurable)
    (fun θ hθ => ae_of_all _ fun ω => ?_) hDi (ae_of_all _ fun ω => ?_)
  · rw [Real.norm_eq_abs]
    exact (norm_le_pi_norm (h (X 0 ω) θ) i).trans (hD _ θ hθ)
  · exact continuousOn_pi.1 (hc (X 0 ω)) i

/-- Miao, Assumption 12.1.2 (p. 387): under Assumption 12.1.7 each `E h_i(x₀, θ)` is finite. -/
theorem gm_integrable_moment {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ) (hdom : Assumption_12_1_7 P X h Θ)
    {θ : Fin k → ℝ} (hθ : θ ∈ Θ) (i : Fin q) : Integrable (fun ω => h (X 0 ω) θ i) P := by
  obtain ⟨D, -, hDi, hD⟩ := hdom
  exact Integrable.mono' hDi ((measurable_pi_iff.1 (hm θ hθ) i).comp (hX 0)).aestronglyMeasurable
    (ae_of_all _ fun ω => (norm_le_pi_norm (h (X 0 ω) θ) i).trans (hD _ θ hθ))

end Miao.StructuralEstimation
