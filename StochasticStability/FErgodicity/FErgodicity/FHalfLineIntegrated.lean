/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.FErgodicModels
import FErgodicity.FNormMeasurable

/-!
# Proposition 14.4.1 (i) in integrated form

Meyn and Tweedie, Proposition 14.4.1 (i), p. 352–353: for random walk on a half line with
increments of mean `β < 0` and finite `(k + 1)`-st moment, and every initial law `λ` with
`∫ λ(dx) x^{k+1} < ∞`, `∫ λ(dx) ‖Pⁿ(x, ·) − π‖_{f_k} → 0`, where `f_k(x) = xᵏ + 1`.

* `tendsto_lintegral_of_tendsto_fNorm`: `‖μₙ − ν‖_f → 0` gives `μₙ(f) → ν(f)` for a finite-valued
  `f` with `μₙ(f), ν(f) < ∞`.
* `lintegral_pow_le_of_drift`: `PV ≤ V + D` iterates to `PⁿV ≤ V + nD`.
* **Proposition 14.4.1 (i)**, integrated (`proposition_14_4_1_i_integrated`): the convergence of
  `x ↦ ‖Pⁿ(x, ·) − π‖_{f_k}` in `L¹(λ)`. The proof combines the pointwise convergence and the
  convergence from `λ` (`proposition_14_4_1`), the measurability of `x ↦ ‖Pⁿ(x, ·) − π‖_{f_k}`
  (`measurable_fNorm_kernel`) and generalised dominated convergence with the bounds
  `‖Pⁿ(x, ·) − π‖_{f_k} ≤ Pⁿ(x, f_k) + π(f_k)`, whose integrals `λPⁿ(f_k) + π(f_k)` converge to
  `2π(f_k)`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-- `‖μₙ − ν‖_f → 0` gives `μₙ(f) → ν(f)` for a finite-valued measurable `f` with
`μₙ(f), ν(f) < ∞`. -/
theorem tendsto_lintegral_of_tendsto_fNorm {f : X → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∀ x, f x ≠ ∞) {μs : ℕ → Measure X} {ν : Measure X}
    (h : Tendsto (fun n => fNorm f (μs n) ν) atTop (𝓝 0)) (hμ : ∀ n, ∫⁻ x, f x ∂μs n ≠ ∞)
    (hν : ∫⁻ x, f x ∂ν ≠ ∞) :
    Tendsto (fun n => ∫⁻ x, f x ∂μs n) atTop (𝓝 (∫⁻ x, f x ∂ν)) := by
  have hgb : ∀ x, ENNReal.ofReal |(f x).toReal| ≤ f x := fun x => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin x)]
  have hr := tendsto_integral_of_tendsto_fNorm h hμ hν hf.ennreal_toReal hgb
  have e : ∀ ρ : Measure X, ∫⁻ x, f x ∂ρ ≠ ∞ →
      ∫⁻ x, f x ∂ρ = ENNReal.ofReal (∫ x, (f x).toReal ∂ρ) := fun ρ h0 => by
    rw [integral_toReal hf.aemeasurable (Eventually.of_forall fun x =>
      lt_top_iff_ne_top.2 (hfin x)), ENNReal.ofReal_toReal h0]
  have e2 : (fun n => ∫⁻ x, f x ∂μs n) =
      fun n => ENNReal.ofReal (∫ x, (f x).toReal ∂μs n) := by
    funext n
    exact e _ (hμ n)
  rw [e2, e ν hν]
  exact ENNReal.tendsto_ofReal hr

/-- `PV ≤ V + D` iterates to `PⁿV ≤ V + nD`. -/
theorem lintegral_pow_le_of_drift (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ≥0∞}
    (hV : Measurable V) {D : ℝ≥0∞} (h : ∀ x, ∫⁻ y, V y ∂P x ≤ V x + D) (n : ℕ) (x : X) :
    ∫⁻ y, V y ∂(P ^ n : Kernel X X) x ≤ V x + n * D := by
  induction n generalizing x with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ hV, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [pow_succ]
    change ∫⁻ y, V y ∂((P ^ n : Kernel X X) ∘ₖ P) x ≤ _
    rw [Kernel.lintegral_comp _ _ _ hV]
    calc ∫⁻ b, ∫⁻ c, V c ∂(P ^ n : Kernel X X) b ∂P x ≤ ∫⁻ b, (V b + n * D) ∂P x :=
          lintegral_mono fun b => ih b
      _ ≤ ∫⁻ b, V b ∂P x + n * D := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add le_rfl (mul_le_of_le_one_right zero_le prob_le_one)
      _ ≤ V x + D + n * D := add_le_add (h x) le_rfl
      _ = V x + (n + 1 : ℕ) * D := by push_cast; ring

/-- **Proposition 14.4.1 (i)** in the book's integrated form (MT p. 352): for random walk on a
half line with `E[W] < 0` and `E|W|^{k+1} < ∞`, every invariant probability `π` and every initial
law `λ` with `∫ λ(dx) x^{k+1} < ∞`, `∫ λ(dx) ‖Pⁿ(x, ·) − π‖_{f_k} → 0` with `f_k(x) = xᵏ + 1`. -/
theorem proposition_14_4_1_i_integrated (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) (k : ℕ)
    (hint : ∀ l ≤ k + 1, Integrable (fun w => |w| ^ l) Γ) (π : Measure ℝ≥0)
    [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_halfLineWalkKernel Γ; IsInvariant (halfLineWalkKernel Γ) π)
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (hμ : ∫⁻ x, (x : ℝ≥0∞) ^ (k + 1) ∂μ ≠ ∞) :
    Tendsto (fun n => ∫⁻ x, fNorm (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ k + 1)
      ((halfLineWalkKernel Γ ^ n : Kernel ℝ≥0 ℝ≥0) x) π ∂μ) atTop (𝓝 0) := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  set P := halfLineWalkKernel Γ with hP
  set f : ℝ≥0 → ℝ≥0∞ := fun x => (x : ℝ≥0∞) ^ k + 1 with hfdef
  set V : ℝ≥0 → ℝ≥0∞ := fun x => (x : ℝ≥0∞) ^ (k + 1) with hVdef
  have hf : Measurable f := ((measurable_coe_nnreal_ennreal).pow_const _).add measurable_const
  have hV : Measurable V := (measurable_coe_nnreal_ennreal).pow_const _
  have hfin : ∀ x, f x ≠ ∞ := fun x =>
    ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
  obtain ⟨-, -, -, -, -, hall⟩ := proposition_14_4_1 Γ hW hβ k hint
  obtain ⟨hπk, hconv, hmix, -⟩ := hall π inferInstance hπ
  obtain ⟨c, hc0, hct, X₀, D, hD, hdrift⟩ := halfLine_drift_14_29 Γ hW hβ k hint
  -- `PV ≤ V + D` and `c f ≤ V + D`
  have hPV : ∀ x, ∫⁻ y, V y ∂P x ≤ V x + D := fun x =>
    le_self_add.trans ((hdrift k le_rfl x).trans (add_le_add le_rfl
      (indicator_le_self' (s := Iic X₀) (f := fun _ : ℝ≥0 => D) (fun _ _ => zero_le) x)))
  have hcf : ∀ x, c * f x ≤ V x + D := fun x =>
    le_add_self.trans ((hdrift k le_rfl x).trans (add_le_add le_rfl
      (indicator_le_self' (s := Iic X₀) (f := fun _ : ℝ≥0 => D) (fun _ _ => zero_le) x)))
  have hci : c⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hc0.ne'
  have hfle : ∀ x, f x ≤ c⁻¹ * (V x + D) := fun x => by
    calc f x = c⁻¹ * (c * f x) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0.ne' hct, one_mul]
      _ ≤ c⁻¹ * (V x + D) := mul_le_mul' le_rfl (hcf x)
  have hπf : ∫⁻ x, f x ∂π ≠ ∞ := by
    rw [hfdef, lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.2 ⟨hπk, ENNReal.one_ne_top⟩
  -- finiteness of `Pⁿ(x, f)` and of `λPⁿ(f)`
  have hPnf : ∀ n x, ∫⁻ y, f y ∂(P ^ n : Kernel ℝ≥0 ℝ≥0) x ≠ ∞ := fun n x => by
    have := isMarkovKernel_pow P n
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun y => hfle y)
    rw [lintegral_const_mul (f := fun a => V a + D) _ (hV.add measurable_const),
      lintegral_add_right _ measurable_const,
      lintegral_const, measure_univ, mul_one]
    refine ENNReal.mul_ne_top hci (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ?_
      (lintegral_pow_le_of_drift P hV hPV n x), hD⟩)
    exact ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top ENNReal.coe_ne_top,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hD⟩
  have hmixf : ∀ n, ∫⁻ y, f y ∂((P ^ n : Kernel ℝ≥0 ℝ≥0) ∘ₘ μ) ≠ ∞ := fun n => by
    have := isMarkovKernel_pow P n
    rw [← lintegral_comp_kernel _ μ hf]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x =>
      (lintegral_mono fun y => hfle y).trans (le_of_eq (lintegral_const_mul
        (f := fun a => V a + D) _ (hV.add measurable_const))))
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => mul_le_mul' le_rfl
      ((lintegral_add_right _ measurable_const).le.trans (add_le_add
        (lintegral_pow_le_of_drift P hV hPV n x) (by rw [lintegral_const, measure_univ,
          mul_one]))))
    rw [lintegral_const_mul (f := fun a => V a + ↑n * D + D) _
      ((hV.add measurable_const).add measurable_const),
      lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
      lintegral_const, lintegral_const, measure_univ, mul_one, mul_one]
    exact ENNReal.mul_ne_top hci (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hμ,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hD⟩, hD⟩)
  -- generalised dominated convergence
  refine tendsto_lintegral_of_le_of_tendsto μ (h := fun n x =>
      ∫⁻ y, f y ∂(P ^ n : Kernel ℝ≥0 ℝ≥0) x + ∫⁻ y, f y ∂π)
    (H := fun _ => ∫⁻ y, f y ∂π + ∫⁻ y, f y ∂π) (fun n => ?_) (fun n => ?_)
    (fun n x => fNorm_le_add f _ π) (fun x => hconv x) (fun x => ?_) ?_ ?_
  · have := isMarkovKernel_pow P n
    exact measurable_fNorm_kernel (P ^ n) π hf hfin (hPnf n) hπf
  · exact hf.lintegral_kernel.add measurable_const
  · exact (tendsto_lintegral_of_tendsto_fNorm hf hfin (hconv x) (hPnf · x) hπf).add
      tendsto_const_nhds
  · have e : ∀ n, ∫⁻ x, (∫⁻ y, f y ∂(P ^ n : Kernel ℝ≥0 ℝ≥0) x + ∫⁻ y, f y ∂π) ∂μ =
        ∫⁻ y, f y ∂((P ^ n : Kernel ℝ≥0 ℝ≥0) ∘ₘ μ) + ∫⁻ y, f y ∂π := fun n => by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_comp_kernel _ μ hf]
    simp_rw [e]
    rw [lintegral_const, measure_univ, mul_one]
    have hm := hmix μ hμ
    exact (tendsto_lintegral_of_tendsto_fNorm hf hfin hm hmixf hπf).add tendsto_const_nhds
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.2 ⟨hπf, hπf⟩

end MeynTweedie.FErgodicity
