/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.CesaroAverages

/-!
# Cesàro convergence for measures with bounded density

Let `π` be an invariant probability measure. For a measure `λ = hπ` with bounded density, the
Cesàro averages of `T*ⁿλ` are uniformly Cauchy on sets (`cesaroCauchy_withDensity`). This is von
Neumann's mean ergodic theorem in `L²(π)` (Mathlib's
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`), applied to the adjoint of
the Markov operator `T`.

`T` is built without choosing representatives: with `ρ = π ⊗ P` the joint law of two successive
states, the maps `J₁ f = f ∘ fst` and `J₂ f = f ∘ snd` are isometries `L²(π) → L²(ρ)` (both
marginals of `ρ` are `π`, by invariance), and `T = J₁† J₂`. Thus `‖T‖ ≤ 1`, and
`⟪T f, g⟫ = ∫ g(x) ∫ f(y) P(x, dy) π(dx)`, so `T` acts on bounded functions as
`f ↦ ∫ f(y) P(·, dy)` (`markovL2_toLp`). Since
`(T*ᵏλ)(A) = ⟪Tᵏ 1_A, h⟫ = ⟪1_A, (T†)ᵏ h⟫`, the averages of `λ` are inner products of `1_A`
with the Birkhoff averages of `T†` at `h`, which converge in `L²(π)`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ] {π : Measure S}
  [IsProbabilityMeasure π]

theorem measurePreserving_fst_compProd :
    MeasurePreserving Prod.fst (π ⊗ₘ κ) π :=
  ⟨measurable_fst, Measure.fst_compProd π κ⟩

theorem measurePreserving_snd_compProd (hπ : adjointOp κ π = π) :
    MeasurePreserving Prod.snd (π ⊗ₘ κ) π :=
  ⟨measurable_snd, by rw [← Measure.snd, Measure.snd_compProd]; exact hπ⟩

variable (κ π) in
/-- `J₁ f = f ∘ fst`, an isometry `L²(π) → L²(π ⊗ P)`. -/
noncomputable def jFst : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 (π ⊗ₘ κ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst_compProd).toContinuousLinearMap

/-- `J₂ f = f ∘ snd`, an isometry `L²(π) → L²(π ⊗ P)` when `π` is invariant. -/
noncomputable def jSnd (hπ : adjointOp κ π = π) : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 (π ⊗ₘ κ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.snd (measurePreserving_snd_compProd hπ)).toContinuousLinearMap

/-- The Markov operator on `L²(π)`, `T = J₁† J₂`. -/
noncomputable def markovL2 (hπ : adjointOp κ π = π) : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  (jFst κ π).adjoint.comp (jSnd hπ)

theorem norm_markovL2_le (hπ : adjointOp κ π = π) : ‖markovL2 hπ‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  calc ‖jFst κ π‖ * ‖jSnd hπ‖ ≤ 1 * 1 := mul_le_mul
        (LinearIsometry.norm_toContinuousLinearMap_le _)
        (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem inner_real_apply (a b : ℝ) : inner ℝ a b = a * b := by
  simp [RCLike.inner_apply, mul_comm]

omit [IsProbabilityMeasure π] in
/-- A bounded measurable function is in `L²` of a finite measure. -/
theorem memLp_two_of_bound {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact hC s)

/-- `⟪T f, g⟫ = ∫ f(y) g(x) d(π ⊗ P)`. -/
theorem inner_markovL2 (hπ : adjointOp κ π = π) (f g : Lp ℝ 2 π) :
    inner ℝ (markovL2 hπ f) g = ∫ p, f p.2 * g p.1 ∂(π ⊗ₘ κ) := by
  rw [markovL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 := Lp.coeFn_compMeasurePreserving f (measurePreserving_snd_compProd hπ)
  have h2 := Lp.coeFn_compMeasurePreserving g (measurePreserving_fst_compProd (κ := κ))
  filter_upwards [h1, h2] with p hp1 hp2
  rw [inner_real_apply]
  exact congrArg₂ (· * ·) hp1 hp2

/-- On bounded measurable functions `T f = ∫ f(y) P(·, dy)`. -/
theorem markovL2_toLp (hπ : adjointOp κ π = π) {F : S → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ s, |F s| ≤ C) :
    markovL2 hπ ((memLp_two_of_bound hF hC).toLp F) =
      (memLp_two_of_bound (theorem_8_1_cor κ hF hC).1 (theorem_8_1_cor κ hF hC).2).toLp
        (markovOpR κ F) := by
  refine ext_inner_right ℝ fun g => ?_
  rw [inner_markovL2, MeasureTheory.L2.inner_def]
  have hFa := MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) hF hC)
  have hKa := MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) (theorem_8_1_cor κ hF hC).1
    (theorem_8_1_cor κ hF hC).2)
  -- the left side, by Fubini
  have hFsnd : (fun p : S × S => (memLp_two_of_bound (μ := π) hF hC).toLp F p.2) =ᵐ[π ⊗ₘ κ]
      fun p => F p.2 :=
    (measurePreserving_snd_compProd hπ).quasiMeasurePreserving.ae_eq_comp hFa
  have hgint : Integrable (fun p : S × S => g p.1) (π ⊗ₘ κ) := by
    have := (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact (measurePreserving_fst_compProd (κ := κ)).integrable_comp_of_integrable this
  have hint : Integrable (fun p : S × S => F p.2 * g p.1) (π ⊗ₘ κ) :=
    hgint.bdd_mul (hF.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC p.2)
  have hL : ∫ p, (memLp_two_of_bound (μ := π) hF hC).toLp F p.2 * g p.1 ∂(π ⊗ₘ κ) =
      ∫ p, F p.2 * g p.1 ∂(π ⊗ₘ κ) :=
    integral_congr_ae (by filter_upwards [hFsnd] with p hp; rw [hp])
  rw [hL, Measure.integral_compProd hint]
  refine integral_congr_ae ?_
  filter_upwards [hKa] with x hx
  rw [inner_real_apply, hx, markovOpR, ← integral_mul_const]

/-- The `n`-step probabilities `x ↦ Pⁿ(x, A)`. -/
noncomputable def stepFn (κ : Kernel S S) (k : ℕ) (A : Set S) (x : S) : ℝ := (kpow κ k x).real A

omit [IsMarkovKernel κ] in
theorem measurable_stepFn (k : ℕ) {A : Set S} (hA : MeasurableSet A) :
    Measurable (stepFn κ k A) :=
  (Kernel.measurable_coe (kpow κ k) hA).ennreal_toReal

theorem abs_stepFn_le (k : ℕ) (A : Set S) (x : S) : |stepFn κ k A x| ≤ 1 := by
  have := isMarkov_kpow (κ := κ) k
  rw [stepFn, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one

theorem markovOpR_stepFn (k : ℕ) {A : Set S} (hA : MeasurableSet A) :
    markovOpR κ (stepFn κ k A) = stepFn κ (k + 1) A := by
  funext x
  have := isMarkov_kpow (κ := κ) k
  simp only [markovOpR, stepFn]
  change _ = ((kpow κ k ∘ₖ κ) x).real A
  rw [measureReal_def, Kernel.comp_apply' _ _ _ hA,
    ← integral_toReal (Kernel.measurable_coe _ hA).aemeasurable
      (Eventually.of_forall fun y => measure_lt_top (kpow κ k y) A)]
  rfl

theorem markovL2_iterate (hπ : adjointOp κ π = π) {A : Set S} (hA : MeasurableSet A) (k : ℕ) :
    (markovL2 hπ)^[k] ((memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
      (abs_stepFn_le 0 A)).toLp _) =
      (memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) k hA)
        (abs_stepFn_le k A)).toLp _ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, markovL2_toLp hπ (measurable_stepFn k hA)
      (abs_stepFn_le k A)]
    congr 1
    exact markovOpR_stepFn k hA

omit [IsProbabilityMeasure π] in
/-- `⟪Tᵏ x, y⟫ = ⟪x, (T†)ᵏ y⟫`. -/
theorem inner_iterate_adjoint (T : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π) (k : ℕ) (x y : Lp ℝ 2 π) :
    inner ℝ (T^[k] x) y = inner ℝ x (T.adjoint^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ContinuousLinearMap.adjoint_inner_right, ih,
      Function.iterate_succ_apply]

/-- A bounded density gives a finite measure. -/
theorem isFiniteMeasure_withDensity_of_bound {H : S → ℝ≥0} {C : ℝ≥0} (hC : ∀ s, H s ≤ C) :
    IsFiniteMeasure (π.withDensity fun s => (H s : ℝ≥0∞)) := by
  refine isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt (lintegral_mono fun s =>
    (ENNReal.coe_le_coe.2 (hC s))) ?_))
  simp

/-- `(T*ᵏ(hπ))(A) = ∫ Pᵏ(x, A) h(x) π(dx)`. -/
theorem adjoint_withDensity_real {H : S → ℝ≥0} (hH : Measurable H) {C : ℝ≥0}
    (hC : ∀ s, H s ≤ C) (k : ℕ) {A : Set S} (hA : MeasurableSet A) :
    have : IsFiniteMeasure (π.withDensity fun s => (H s : ℝ≥0∞)) :=
      isFiniteMeasure_withDensity_of_bound hC
    (adjointOp (kpow κ k) (π.withDensity fun s => (H s : ℝ≥0∞))).real A =
      ∫ x, stepFn κ k A x * (H x : ℝ) ∂π := by
  intro _
  have := isMarkov_kpow (κ := κ) k
  rw [bind_real_eq _ _ hA, integral_withDensity_eq_integral_smul hH]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, stepFn]
  ring

/-- `⟪f, h⟫ = ∫ f h dπ` for bounded measurable functions. -/
theorem inner_toLp_toLp {F G : S → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ s, |F s| ≤ C)
    (hG : Measurable G) {D : ℝ} (hD : ∀ s, |G s| ≤ D) :
    inner ℝ ((memLp_two_of_bound (μ := π) hF hC).toLp F)
      ((memLp_two_of_bound (μ := π) hG hD).toLp G) = ∫ x, F x * G x ∂π := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) hF hC),
    MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) hG hD)] with x h1 h2
  rw [inner_real_apply, h1, h2]

/-- **Cesàro convergence for bounded densities.** If `π` is invariant and `λ = hπ` with `h`
bounded, the Cesàro averages of `T*ⁿλ` are uniformly Cauchy on sets. -/
theorem cesaroCauchy_withDensity (hπ : adjointOp κ π = π) {H : S → ℝ≥0} (hH : Measurable H)
    {C : ℝ≥0} (hC : ∀ s, H s ≤ C) :
    CesaroCauchy κ (π.withDensity fun s => (H s : ℝ≥0∞)) := by
  have hfin := isFiniteMeasure_withDensity_of_bound (π := π) hC
  set V := (markovL2 hπ).adjoint
  have hV : ‖V‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]; exact norm_markovL2_le hπ
  have hHm : Measurable fun s => (H s : ℝ) := hH.coe_nnreal_real
  have hHb : ∀ s, |(H s : ℝ)| ≤ C := fun s => by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact_mod_cast hC s
  set h := (memLp_two_of_bound (μ := π) hHm hHb).toLp _
  set B : ℕ → Lp ℝ 2 π := fun n => birkhoffAverage ℝ V _root_.id n h
  have hcauchy : CauchySeq B := (V.tendsto_birkhoffAverage_orthogonalProjection hV h).cauchySeq
  -- the averages as inner products
  have hkey : ∀ n A, (hA : MeasurableSet A) →
      (cesaroM κ n (π.withDensity fun s => (H s : ℝ≥0∞))).real A =
        inner ℝ ((memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
          (abs_stepFn_le 0 A)).toLp _) (V (B (n + 1))) := by
    intro n A hA
    set u := (memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
      (abs_stepFn_le 0 A)).toLp _
    have hterm : ∀ k, (adjointOp (kpow κ (k + 1)) (π.withDensity fun s => (H s : ℝ≥0∞))).real A =
        inner ℝ u (V^[k + 1] h) := fun k => by
      rw [adjoint_withDensity_real hH hC (k + 1) hA, ← inner_iterate_adjoint,
        markovL2_iterate hπ hA, inner_toLp_toLp (measurable_stepFn (k + 1) hA)
          (abs_stepFn_le (k + 1) A) hHm hHb]
    rw [cesaroM_real, Finset.sum_congr rfl fun k _ => hterm k, ← inner_sum, ← real_inner_smul_right]
    congr 1
    simp only [B, birkhoffAverage, birkhoffSum, id, map_smul, map_sum]
    congr 1
    · push_cast; ring
    · exact Finset.sum_congr rfl fun k _ => Function.iterate_succ_apply' V k h
  intro η hη
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcauchy η hη
  refine ⟨N, fun n hn m hm A hA => ?_⟩
  rw [hkey n A hA, hkey m A hA, ← inner_sub_right, ← map_sub]
  set u := (memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
    (abs_stepFn_le 0 A)).toLp _
  have hu : ‖u‖ ≤ 1 := by
    have := Lp.norm_le_of_ae_bound (f := u) zero_le_one (by
      filter_upwards [MemLp.coeFn_toLp (memLp_two_of_bound (μ := π)
        (measurable_stepFn (κ := κ) 0 hA) (abs_stepFn_le 0 A))] with x hx
      rw [hx, Real.norm_eq_abs]; exact abs_stepFn_le 0 A x)
    rw [show measureUnivNNReal π = 1 by simp [measureUnivNNReal]] at this
    simpa using this
  have hd : ‖B (n + 1) - B (m + 1)‖ < η := by
    rw [← dist_eq_norm]; exact hN _ (by omega) _ (by omega)
  calc |inner ℝ u (V (B (n + 1) - B (m + 1)))| ≤ ‖u‖ * ‖V (B (n + 1) - B (m + 1))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ 1 * (1 * ‖B (n + 1) - B (m + 1)‖) := by
        gcongr
        exact (V.le_opNorm _).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
    _ ≤ η := by linarith

end StokeyLucasPrescott.StrongConvergence
