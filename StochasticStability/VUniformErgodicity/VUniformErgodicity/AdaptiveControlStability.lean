/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.BoundednessCriteria
import VUniformErgodicity.NSSAdaptiveControl

/-!
# The adaptive control model: Kalman filter and positive recurrence (MT §12.5.3)

Meyn and Tweedie, Proposition 12.5.2, p. 307, for the Gaussian adaptive control model
(SAC1)–(SAC2), `sacGaussianKernel`, on the state `Φ = (Σ, θ̃, Y)`. This module completes
`proposition_12_5_2` (in `BoundednessCriteria`) in two ways. It derives the hypothesis (12.38)
from the Kalman filter, and it proves the last step of the proof, that `Φ` is positive recurrent.

**The Kalman filter.**
* `kalman_step_map`: one Kalman step, `(N(0, 1) ⊗ N(0, σ_z²) ⊗ N(0, σ_w²))`-law of
  `(θ̃', Y')` from `θ̃ = √Σ ξ`. It is `N(0, Σ') ⊗ N(0, ΣY² + σ_w²)`, by characteristic functions
  (`strongDual_prod_apply`, `integral_cexp_gaussianReal`).
* `IsKalmanLaw ν`: (12.38) as a property of the law of `Φₖ`, namely `θ̃ ~ N(0, Σ)` given
  `(Σ, Y)`.
* `lintegral_sacGaussian_comp_of_isKalmanLaw`: one step of the chain from a Kalman law.
* `IsKalmanLaw.comp`, `isKalmanLaw_sacGaussian_pow`: the filter preserves Kalman laws, so (12.38)
  holds at every time when it holds at time `0`.
* `IsKalmanLaw.lintegral_sq`: under a Kalman law, `E[g(Σ, Y) θ̃²] = E[g(Σ, Y) Σ]`. This is the
  hypothesis `hcond` of `proposition_12_5_2`, and it gives (12.39).
* `integral_sq_gaussianReal`, `sacGaussian_noise_moments`: the moments of (SAC2).
* **`proposition_12_5_2_kalman`**: `sup_k E|Φₖ|² < ∞` from any Kalman initial law on the state
  space with `E Y₀² < ∞`.
* `sacKalmanInit`, `sacKalmanInit_spec`: such an initial law, with `Σ₀ = σ_z²`, `Y₀ = 0` and
  `θ̃₀ ~ N(0, σ_z²)`.

**Positive recurrence.**
* `sacStepX`, `restrictKernel_sacKernel_eq`: the chain restricted to the absorbing state space
  `X = [σ_z², σ_z²/(1 − α²)] × ℝ²` is a random recursion on `X`.
* `isWeakFeller_restrict_sacKernel`: the restricted chain is weak Feller.
* **`proposition_12_5_2_positive`**: under the hypotheses of Proposition 7.4.3 together with
  `σ_z² < 1`, the restricted chain is a positive recurrent, aperiodic T-chain.
  - The invariant probability comes from Theorem 12.1.2 (i). The laws from `sacKalmanInit` are
    tight, so their Cesàro means do not vanish on a compact set.
  - Positivity uses Proposition 7.4.3 (`proposition_7_4_3`, copied from the Chapter 7 project
    with `NSSAdaptiveControl` and its dependencies).
  - Recurrence is Proposition 10.1.1.

**Corrections and hypotheses.**
* The book's last step invokes Proposition 12.1.3, which is false as stated
  (`proposition_12_1_3_counterexample`). The argument here uses the Cesàro form, through tightness
  and Theorem 12.1.2 (i).
* Proposition 7.4.3 needs `α ≠ 0` and `σ_z ≠ 0`, as recorded in `NSSAdaptiveControl`.
* (12.38) is formalised as the Kalman law `IsKalmanLaw`: the estimation error is centred Gaussian
  with variance `Σ` given `(Σ, Y)`. This is the Kalman-filter prior; the book's example
  `y₀ = θ̃₀ = Σ₀ = 0` lies outside the state space `Σ ≥ σ_z²`, so the initial law used here is
  `sacKalmanInit`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped ENNReal NNReal

/-- A continuous linear functional on `ℝ × ℝ` is `L(a, b) = a L(1, 0) + b L(0, 1)`. -/
theorem strongDual_prod_apply (L : StrongDual ℝ (ℝ × ℝ)) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : (a, b) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The characteristic function of a centred Gaussian, `∫ e^{itx} dN(0, v) = e^{−vt²/2}`. -/
theorem integral_cexp_gaussianReal (v : ℝ≥0) (t : ℝ) :
    ∫ x, cexp (t * x * I) ∂gaussianReal 0 v = cexp (-(v * t ^ 2 / 2)) := by
  rw [← charFun_apply_real, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- **The Kalman filter step for the adaptive control model** (MT (2.23)–(2.24), behind (12.38)
and (12.39)). Let `θ̃ = √Σ ξ` with `ξ ~ N(0, 1)` independent of `(Z, W) ~ N(0, σ_z²) ⊗ N(0, σ_w²)`,
and let `D = ΣY² + σ_w²` and `Σ' = σ_z² + α²σ_w²Σ/D`. Then the pair
`(θ̃', Y') = (αθ̃ − αΣY'Y/D + Z, θ̃Y + W)` is `N(0, Σ') ⊗ N(0, D)`: the new estimation error is
centred Gaussian with variance `Σ'` and independent of the new observation. Proved by comparing
characteristic functions. -/
theorem kalman_step_map {α σz σw S y : ℝ} (hS : 0 ≤ S) (hσw : σw ≠ 0) :
    ((gaussianReal 0 1).prod ((gaussianReal 0 (σz ^ 2).toNNReal).prod
        (gaussianReal 0 (σw ^ 2).toNNReal))).map
      (fun p : ℝ × ℝ × ℝ =>
        (α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / (S * y ^ 2 + σw ^ 2) + p.2.1,
          √S * p.1 * y + p.2.2)) =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun q : ℝ × ℝ =>
        (√(σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2)) * q.1,
          √(S * y ^ 2 + σw ^ 2) * q.2)) := by
  set D := S * y ^ 2 + σw ^ 2 with hD
  set Sn := σz ^ 2 + α ^ 2 * σw ^ 2 * S / D with hSn
  have hw2 : 0 < σw ^ 2 := by positivity
  have hD0 : 0 < D := by positivity
  have hSn0 : 0 ≤ Sn := by positivity
  have hm1 : Measurable fun p : ℝ × ℝ × ℝ =>
      (α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / D + p.2.1, √S * p.1 * y + p.2.2) :=
    by fun_prop
  have hm2 : Measurable fun q : ℝ × ℝ => (√Sn * q.1, √D * q.2) := by fun_prop
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  set u := L (1, 0)
  set v := L (0, 1)
  rw [charFunDual_apply, charFunDual_apply, integral_map hm1.aemeasurable (by fun_prop),
    integral_map hm2.aemeasurable (by fun_prop)]
  set A := √S * (u * (α - α * S * y ^ 2 / D) + v * y)
  set B := u
  set C := v - u * (α * S * y / D)
  have h1 : ∀ p : ℝ × ℝ × ℝ, cexp ((L (α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / D +
      p.2.1, √S * p.1 * y + p.2.2) : ℂ) * I) =
      cexp (A * p.1 * I) * (cexp (B * p.2.1 * I) * cexp (C * p.2.2 * I)) := fun p => by
    rw [← Complex.exp_add, ← Complex.exp_add, strongDual_prod_apply]
    congr 1
    have : (α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / D + p.2.1) * u +
        (√S * p.1 * y + p.2.2) * v = A * p.1 + B * p.2.1 + C * p.2.2 := by
      simp only [A, B, C]
      field_simp
      ring
    rw [this]
    push_cast
    ring
  have h2 : ∀ q : ℝ × ℝ, cexp ((L (√Sn * q.1, √D * q.2) : ℂ) * I) =
      cexp ((√Sn * u : ℝ) * q.1 * I) * cexp ((√D * v : ℝ) * q.2 * I) := fun q => by
    rw [← Complex.exp_add, strongDual_prod_apply]
    congr 1
    push_cast
    ring
  simp_rw [h1, h2]
  rw [integral_prod_mul (fun ξ : ℝ => cexp (A * ξ * I))
      (fun zw : ℝ × ℝ => cexp (B * zw.1 * I) * cexp (C * zw.2 * I)),
    integral_prod_mul (fun z : ℝ => cexp (B * z * I)) (fun w : ℝ => cexp (C * w * I)),
    integral_prod_mul (fun a : ℝ => cexp ((√Sn * u : ℝ) * a * I))
      (fun b : ℝ => cexp ((√D * v : ℝ) * b * I))]
  simp only [integral_cexp_gaussianReal]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hreal : A ^ 2 + σz ^ 2 * B ^ 2 + σw ^ 2 * C ^ 2 = (√Sn * u) ^ 2 + (√D * v) ^ 2 := by
    rw [mul_pow (√Sn), mul_pow (√D), Real.sq_sqrt hSn0, Real.sq_sqrt hD0.le]
    have hD' : D ≠ 0 := hD0.ne'
    simp only [A, B, C, mul_pow, Real.sq_sqrt hS, hSn]
    field_simp
    rw [hD]
    ring
  have hz : (((σz ^ 2).toNNReal : ℝ≥0) : ℝ) = σz ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hw : (((σw ^ 2).toNNReal : ℝ≥0) : ℝ) = σw ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simp only [hz, hw, NNReal.coe_one] at hc ⊢
  push_cast at hc ⊢
  linear_combination (-1 / 2 : ℂ) * hc

/-- **The Kalman-filter law** of the adaptive control state `(Σ, θ̃, Y)` (MT (12.38)): given
`(Σ, Y)`, the estimation error is `θ̃ ~ N(0, Σ)`, i.e. `θ̃ = √Σ ξ` with `ξ ~ N(0, 1)` independent
of `(Σ, Y)`. As a property of the law `ν`: `∫ g dν = ∫∫ g(Σ, √Σ ξ, Y) dN(0, 1)(ξ) dν` for every
measurable `g ≥ 0`. -/
def IsKalmanLaw (ν : Measure (ℝ × ℝ × ℝ)) : Prop :=
  ∀ g : ℝ × ℝ × ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ φ, g φ ∂ν = ∫⁻ φ, ∫⁻ ξ, g (φ.1, √φ.1 * ξ, φ.2.2) ∂gaussianReal 0 1 ∂ν

/-- One step of the Gaussian adaptive control chain from a Kalman law: with
`Σ' = σ_z² + α²σ_w²Σ/D` and `D = ΣY² + σ_w²`,
`∫ h d(νP) = ∫∫ h(Σ', √Σ' ξ, √D η) dN(0, 1)²(ξ, η) dν`. -/
theorem lintegral_sacGaussian_comp_of_isKalmanLaw {α σz σw : ℝ} (hσw : σw ≠ 0)
    {ν : Measure (ℝ × ℝ × ℝ)} [IsFiniteMeasure ν] (hνS : ∀ᵐ φ ∂ν, 0 ≤ φ.1)
    (hK : IsKalmanLaw ν) {h : ℝ × ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ψ, h ψ ∂(sacGaussianKernel α σz σw ∘ₘ ν) =
      ∫⁻ φ, ∫⁻ q, h (σz ^ 2 + α ^ 2 * σw ^ 2 * φ.1 / (φ.1 * φ.2.2 ^ 2 + σw ^ 2),
          √(σz ^ 2 + α ^ 2 * σw ^ 2 * φ.1 / (φ.1 * φ.2.2 ^ 2 + σw ^ 2)) * q.1,
          √(φ.1 * φ.2.2 ^ 2 + σw ^ 2) * q.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) ∂ν := by
  set N := gaussianReal 0 1
  set Γ := (gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)
  set F := sacStep α σz σw
  have hF : Measurable F := measurable_sacStep α σz σw
  have hP : ∀ φ, sacGaussianKernel α σz σw φ = Γ.map fun w => F (φ, w) := fun φ =>
    recursionKernel_apply Γ hF φ
  have hG : Measurable fun φ : ℝ × ℝ × ℝ => ∫⁻ zw, h (F (φ, zw)) ∂Γ :=
    (hh.comp hF).lintegral_prod_right'
  rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable hh.aemeasurable]
  simp_rw [hP]
  rw [show (fun φ => ∫⁻ ψ, h ψ ∂Γ.map fun w => F (φ, w)) = fun φ => ∫⁻ zw, h (F (φ, zw)) ∂Γ from
    funext fun φ => lintegral_map hh (hF.comp measurable_prodMk_left), hK _ hG]
  refine lintegral_congr_ae ?_
  filter_upwards [hνS] with φ hφ
  obtain ⟨S, t, y⟩ := φ
  simp only at hφ ⊢
  have hm1 : Measurable fun p : ℝ × ℝ × ℝ =>
      (α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / (S * y ^ 2 + σw ^ 2) + p.2.1,
        √S * p.1 * y + p.2.2) := by fun_prop
  have hm2 : Measurable fun q : ℝ × ℝ =>
      (√(σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2)) * q.1, √(S * y ^ 2 + σw ^ 2) * q.2) :=
    by fun_prop
  have hhS : Measurable fun r : ℝ × ℝ =>
      h (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2), r) :=
    hh.comp (by fun_prop)
  have hm0 : Measurable fun p : ℝ × (ℝ × ℝ) => h (F ((S, √S * p.1, y), p.2)) :=
    hh.comp (hF.comp (by fun_prop))
  calc ∫⁻ ξ, ∫⁻ zw, h (F ((S, √S * ξ, y), zw)) ∂Γ ∂N
      = ∫⁻ p, h (F ((S, √S * p.1, y), p.2)) ∂(N.prod Γ) :=
        (lintegral_prod _ hm0.aemeasurable).symm
    _ = ∫⁻ p, h (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2),
          α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / (S * y ^ 2 + σw ^ 2) + p.2.1,
          √S * p.1 * y + p.2.2) ∂(N.prod Γ) := by
        refine lintegral_congr fun p => ?_
        simp only [F, sacStep]
    _ = ∫⁻ r, h (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2), r)
          ∂((N.prod Γ).map fun p : ℝ × ℝ × ℝ =>
            (α * (√S * p.1) - α * S * (√S * p.1 * y + p.2.2) * y / (S * y ^ 2 + σw ^ 2) + p.2.1,
              √S * p.1 * y + p.2.2)) := (lintegral_map hhS hm1).symm
    _ = ∫⁻ r, h (σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2), r)
          ∂((N.prod N).map fun q : ℝ × ℝ =>
            (√(σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * y ^ 2 + σw ^ 2)) * q.1,
              √(S * y ^ 2 + σw ^ 2) * q.2)) := by rw [kalman_step_map hφ hσw]
    _ = _ := lintegral_map hhS hm2

/-- **The Kalman filter preserves the Kalman law** (MT (12.38), propagated by (2.23)–(2.24)): if
`θ̃ₖ ~ N(0, Σₖ)` given `(Σₖ, Yₖ)`, then `θ̃ₖ₊₁ ~ N(0, Σₖ₊₁)` given `(Σₖ₊₁, Yₖ₊₁)`. -/
theorem IsKalmanLaw.comp {α σz σw : ℝ} (hσw : σw ≠ 0) {ν : Measure (ℝ × ℝ × ℝ)}
    [IsFiniteMeasure ν] (hνS : ∀ᵐ φ ∂ν, 0 ≤ φ.1) (hK : IsKalmanLaw ν) :
    IsKalmanLaw (sacGaussianKernel α σz σw ∘ₘ ν) := by
  intro g hg
  set N := gaussianReal 0 1
  have hg' : Measurable fun ψ : ℝ × ℝ × ℝ => ∫⁻ ξ, g (ψ.1, √ψ.1 * ξ, ψ.2.2) ∂N :=
    (hg.comp (by fun_prop : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (p.1.1, √p.1.1 * p.2, p.1.2.2))).lintegral_prod_right'
  rw [lintegral_sacGaussian_comp_of_isKalmanLaw hσw hνS hK hg,
    lintegral_sacGaussian_comp_of_isKalmanLaw hσw hνS hK hg']
  refine lintegral_congr fun φ => ?_
  set a := σz ^ 2 + α ^ 2 * σw ^ 2 * φ.1 / (φ.1 * φ.2.2 ^ 2 + σw ^ 2)
  set b := φ.1 * φ.2.2 ^ 2 + σw ^ 2
  have hm : Measurable fun q : ℝ × ℝ => g (a, √a * q.1, √b * q.2) := hg.comp (by fun_prop)
  have hm' : Measurable fun q : ℝ × ℝ => ∫⁻ ξ, g (a, √a * ξ, √b * q.2) ∂N :=
    (hg.comp (by fun_prop : Measurable fun p : (ℝ × ℝ) × ℝ => (a, √a * p.2, √b * p.1.2))
      ).lintegral_prod_right'
  rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hm'.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  exact lintegral_lintegral_swap (hg.comp (by fun_prop)).aemeasurable

/-- Under a Kalman law, `E[g(Σ, Y) θ̃²] = E[g(Σ, Y) Σ]` for every measurable `g ≥ 0`: the averaged
form of (12.38), `E[θ̃² | Σ, Y] = Σ`. -/
theorem IsKalmanLaw.lintegral_sq {ν : Measure (ℝ × ℝ × ℝ)} (hνS : ∀ᵐ φ ∂ν, 0 ≤ φ.1)
    (hK : IsKalmanLaw ν) {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) ∂ν =
      ∫⁻ φ, g (φ.1, φ.2.2) * ENNReal.ofReal φ.1 ∂ν := by
  have h1 : ∫⁻ ξ, ENNReal.ofReal (ξ ^ 2) ∂gaussianReal 0 1 = 1 := by
    have hint : Integrable (fun ξ : ℝ => ξ ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    have hv : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      have := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := fun x : ℝ => x)
        aemeasurable_id' integral_id_gaussianReal
      rw [variance_fun_id_gaussianReal] at this
      exact_mod_cast this.symm
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ξ => sq_nonneg ξ), hv,
      ENNReal.ofReal_one]
  have hm : Measurable fun φ : ℝ × ℝ × ℝ => g (φ.1, φ.2.2) * ENNReal.ofReal (φ.2.1 ^ 2) :=
    (hg.comp (by fun_prop)).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  rw [hK _ hm]
  refine lintegral_congr_ae ?_
  filter_upwards [hνS] with φ hφ
  simp_rw [mul_pow, Real.sq_sqrt hφ, ENNReal.ofReal_mul hφ]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop), h1, mul_one]

/-- The Kalman law propagates along the whole chain: if the initial law is a Kalman law on
`[σ_z², σ_z²/(1 − α²)] × ℝ²`, so is every `μPᵏ`. -/
theorem isKalmanLaw_sacGaussian_pow {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0)
    {μ : Measure (ℝ × ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0) (hK : IsKalmanLaw μ) (k : ℕ) :
    IsKalmanLaw ((sacGaussianKernel α σz σw ^ k : Kernel _ _) ∘ₘ μ) := by
  have hM := isMarkovKernel_sacGaussianKernel α σz σw
  induction k with
  | zero => rw [pow_zero_comp]; exact hK
  | succ k ih =>
    have := isMarkovKernel_pow (sacGaussianKernel α σz σw) k
    have hS : ∀ᵐ φ ∂((sacGaussianKernel α σz σw ^ k) ∘ₘ μ), 0 ≤ φ.1 :=
      (measure_eq_zero_iff_ae_notMem.1 (sacKernel_pow_comp_compl _ hα hσw μ hμ k)).mono
        fun φ h => (sq_nonneg σz).trans (not_not.1 h).1.1
    have h := ih.comp (α := α) (σz := σz) hσw hS
    rw [Measure.comp_assoc] at h
    rw [pow_succ']
    exact h

/-- `∫ x² dN(0, v) = v`. -/
theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := fun x : ℝ => x)
    aemeasurable_id' integral_id_gaussianReal
  rw [variance_fun_id_gaussianReal] at this
  exact this.symm

/-- The disturbance law of (SAC2), `N(0, σ_z²) ⊗ N(0, σ_w²)`, has `E W = 0`, `E W² = σ_w²`, and
`W, W²` integrable. -/
theorem sacGaussian_noise_moments (σz σw : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.2)
        ((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) ∧
      Integrable (fun z : ℝ × ℝ => z.2 ^ 2)
        ((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) ∧
      ∫ z, z.2 ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal)) =
        0 ∧
      ∫ z, z.2 ^ 2 ∂((gaussianReal 0 (σz ^ 2).toNNReal).prod
        (gaussianReal 0 (σw ^ 2).toNNReal)) = σw ^ 2 := by
  refine ⟨((memLp_id_gaussianReal 1).integrable le_rfl).comp_snd _,
    (memLp_id_gaussianReal 2).integrable_sq.comp_snd _, ?_, ?_⟩
  · rw [integral_fun_snd (fun w : ℝ => w), integral_id_gaussianReal]
    simp
  · rw [integral_fun_snd (fun w : ℝ => w ^ 2), integral_sq_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg _)]
    simp

/-- **Proposition 12.5.2 under the Kalman filter** (MT p. 307). For the Gaussian adaptive
control model (SAC1)–(SAC2) with `|α| < 1`, `σ_z² < 1` and `σ_z, σ_w ≠ 0`, started from a Kalman
law (12.38) on `[σ_z², σ_z²/(1 − α²)] × ℝ²` with `E Y₀² < ∞`, `sup_k E|Φₖ|² < ∞`. The hypothesis
`hcond` of `proposition_12_5_2` is now a theorem (`isKalmanLaw_sacGaussian_pow`,
`IsKalmanLaw.lintegral_sq`). -/
theorem proposition_12_5_2_kalman {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) (hσz : σz ≠ 0)
    (hσz1 : σz ^ 2 < 1) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0)
    (hY : ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂μ ≠ ∞) (hK : IsKalmanLaw μ) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ k : ℕ, ∫⁻ φ, ENNReal.ofReal (φ.1 ^ 2 + φ.2.1 ^ 2 + φ.2.2 ^ 2)
      ∂((sacGaussianKernel α σz σw ^ k : Kernel _ _) ∘ₘ μ) ≤ M := by
  obtain ⟨hW1, hW2, hm, hv⟩ := sacGaussian_noise_moments σz σw
  refine proposition_12_5_2 _ hα hσw hσz hσz1 hW1 hW2 hm hv μ hμ hY fun k g hg => ?_
  have hS : ∀ᵐ φ ∂((sacGaussianKernel α σz σw ^ k : Kernel _ _) ∘ₘ μ), 0 ≤ φ.1 :=
    (measure_eq_zero_iff_ae_notMem.1 (sacKernel_pow_comp_compl _ hα hσw μ hμ k)).mono
      fun φ h => (sq_nonneg σz).trans (not_not.1 h).1.1
  exact (isKalmanLaw_sacGaussian_pow hα hσw hμ hK k).lintegral_sq hS hg

/-- The Kalman initial law `Σ₀ = σ_z²`, `Y₀ = 0`, `θ̃₀ ~ N(0, σ_z²)`: it satisfies (12.38) at
time `0` and lives on `[σ_z², σ_z²/(1 − α²)] × ℝ²`. -/
noncomputable def sacKalmanInit (σz : ℝ) : Measure (ℝ × ℝ × ℝ) :=
  (gaussianReal 0 (σz ^ 2).toNNReal).map fun t => (σz ^ 2, t, 0)

/-- The initial law `sacKalmanInit` is a probability measure, a Kalman law, lives on the state
space and has `E Y₀² = 0`. -/
theorem sacKalmanInit_spec {α : ℝ} (hα : |α| < 1) (σz : ℝ) :
    IsProbabilityMeasure (sacKalmanInit σz) ∧
      sacKalmanInit σz (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = 0 ∧
      ∫⁻ φ, ENNReal.ofReal (φ.2.2 ^ 2) ∂sacKalmanInit σz = 0 ∧ IsKalmanLaw (sacKalmanInit σz) := by
  have hm : Measurable fun t : ℝ => ((σz ^ 2, t, 0) : ℝ × ℝ × ℝ) := by fun_prop
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have hb : σz ^ 2 ≤ σz ^ 2 / (1 - α ^ 2) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg σz, sq_nonneg α]
  refine ⟨by rw [sacKalmanInit]; infer_instance, ?_, ?_, ?_⟩
  · rw [sacKalmanInit, Measure.map_apply hm (measurableSet_Icc.prod MeasurableSet.univ).compl]
    have : (fun t : ℝ => ((σz ^ 2, t, 0) : ℝ × ℝ × ℝ)) ⁻¹'
        (Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ)ᶜ = ∅ :=
      eq_empty_of_forall_notMem fun t ht => ht ⟨⟨le_rfl, hb⟩, mem_univ _⟩
    rw [this, measure_empty]
  · have hY : Measurable fun φ : ℝ × ℝ × ℝ => ENNReal.ofReal (φ.2.2 ^ 2) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [sacKalmanInit, lintegral_map hY hm]
    simp
  · intro g hg
    have hg' : Measurable fun φ : ℝ × ℝ × ℝ => ∫⁻ ξ, g (φ.1, √φ.1 * ξ, φ.2.2) ∂gaussianReal 0 1 :=
      (hg.comp (by fun_prop : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ =>
        (p.1.1, √p.1.1 * p.2, p.1.2.2))).lintegral_prod_right'
    rw [sacKalmanInit, lintegral_map hg hm, lintegral_map hg' hm]
    simp only [lintegral_const, measure_univ, mul_one]
    have hc : (gaussianReal 0 1).map (fun ξ => √(σz ^ 2) * ξ) =
        gaussianReal 0 (σz ^ 2).toNNReal := by
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      ext
      simp [Real.sq_sqrt (sq_nonneg σz), Real.coe_toNNReal _ (sq_nonneg σz)]
    have h1 : Measurable fun t : ℝ => g (σz ^ 2, t, 0) := hg.comp (by fun_prop)
    have h2 : Measurable fun ξ : ℝ => √(σz ^ 2) * ξ := by fun_prop
    rw [← hc, lintegral_map h1 h2]

/-! ### Positive recurrence on the state space -/

/-- The adaptive control step restricted to its state space `X = [σ_z², σ_z²/(1 − α²)] × ℝ²`,
as a map `X × ℝ² → X`. -/
noncomputable def sacStepX {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0)
    (p : sacSpace α σz × (ℝ × ℝ)) : sacSpace α σz :=
  ⟨sacStep α σz σw ((p.1 : ℝ × ℝ × ℝ), p.2), sacStep_sigma_mem hα hσw p.1.2 p.2⟩

/-- The adaptive control chain restricted to its state space is the random recursion of the
restricted step. -/
theorem restrictKernel_sacKernel_eq (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) :
    restrictKernel (sacKernel Γ α σz σw) (isClosed_sacSpace α σz).measurableSet =
      recursionKernel Γ (sacStepX hα hσw) := by
  have hm : Measurable (sacStepX (σz := σz) hα hσw) :=
    ((measurable_sacStep α σz σw).comp (measurable_subtype_coe.prodMap measurable_id)).subtype_mk
  ext x B hB
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe (isClosed_sacSpace α σz).measurableSet).measurableSet_image.2
      hB
  rw [restrictKernel_apply _ _ x hB, sacKernel,
    recursionKernel_apply' Γ (measurable_sacStep α σz σw) _ hB', recursionKernel_apply' Γ hm _ hB]
  congr 1
  ext w
  change sacStep α σz σw ((x : ℝ × ℝ × ℝ), w) ∈ Subtype.val '' B ↔ sacStepX hα hσw (x, w) ∈ B
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = sacStepX hα hσw (x, w) := Subtype.ext hyx
    rwa [← this]
  · intro h
    exact ⟨_, h, rfl⟩

/-- The restricted adaptive control chain is weak Feller: on the state space the denominator
`ΣY² + σ_w²` is positive, so the step is continuous there. -/
theorem isWeakFeller_restrict_sacKernel (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ]
    {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) :
    IsWeakFeller (restrictKernel (sacKernel Γ α σz σw) (isClosed_sacSpace α σz).measurableSet) := by
  rw [restrictKernel_sacKernel_eq Γ hα hσw]
  have hm : Measurable (sacStepX (σz := σz) hα hσw) :=
    ((measurable_sacStep α σz σw).comp (measurable_subtype_coe.prodMap measurable_id)).subtype_mk
  refine isWeakFeller_recursionKernel Γ hm fun w => Continuous.subtype_mk ?_ _
  have hd : ∀ x : sacSpace α σz, (x : ℝ × ℝ × ℝ).1 * (x : ℝ × ℝ × ℝ).2.2 ^ 2 + σw ^ 2 ≠ 0 :=
    fun x => (sac_den_pos hσw x.2).ne'
  have hc : Continuous fun x : sacSpace α σz => (x : ℝ × ℝ × ℝ) := continuous_subtype_val
  simp only [sacStep]
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact continuous_const.add (Continuous.div (by fun_prop) (by fun_prop) hd)
  · exact (Continuous.sub (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) hd)).add
      continuous_const
  · fun_prop

/-- **Proposition 12.5.2, the final step** (MT p. 307, with Proposition 7.4.3 and
Proposition 10.1.1). For the Gaussian adaptive control model with `|α| < 1`, `α ≠ 0`,
`σ_z ≠ 0`, `σ_w ≠ 0` and `σ_z² < 1`, the chain restricted to its state space
`[σ_z², σ_z²/(1 − α²)] × ℝ²` is a positive recurrent, aperiodic T-chain. The invariant
probability comes from Theorem 12.1.2 (i): the laws from the Kalman initial law
`sacKalmanInit` are tight (`proposition_12_5_2_tight` with the Kalman filter), so their Cesàro
means cannot vanish on a compact set. This is used in place of the book's appeal to
Proposition 12.1.3, which is false as stated (`proposition_12_1_3_counterexample`). -/
theorem proposition_12_5_2_positive {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) (hσz1 : σz ^ 2 < 1) :
    have := isMarkovKernel_sacGaussianKernel α σz σw
    let _ := isMarkovKernel_restrictKernel (sacGaussianKernel α σz σw)
      (isClosed_sacSpace α σz).measurableSet (isAbsorbing_sacSpace _ hα hσw)
    IsTChain
        (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet) ∧
      ∃ ψ : Measure (sacSpace α σz),
        IsPositive
          (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet) ψ ∧
        IsRecurrentChain
          (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet) ψ ∧
        IsAperiodic
          (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet)
          ψ := by
  intro hP hPX
  set P := sacGaussianKernel α σz σw
  set X := sacSpace α σz
  have hXc : IsClosed X := isClosed_sacSpace α σz
  have hXm : MeasurableSet X := hXc.measurableSet
  set PX := restrictKernel P hXm
  have hX : X = Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext p
    simp [X, sacSpace]
  obtain ⟨hT, ψ, hψ, hap⟩ := proposition_7_4_3 hα hα0 hσz hσw
  -- an invariant probability for the restricted chain
  have hinv : ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant PX π := by
    have : LocallyCompactSpace X := hXc.isClosedEmbedding_subtypeVal.locallyCompactSpace
    by_contra hno
    set μ := sacKalmanInit σz
    obtain ⟨hμP, hμX, hμY, hμK⟩ := sacKalmanInit_spec hα σz
    obtain ⟨hW1, hW2, hm, hv⟩ := sacGaussian_noise_moments σz σw
    have htight := proposition_12_5_2_tight _ hα hσw hσz hσz1 hW1 hW2 hm hv μ hμX
      (by rw [hμY]; exact ENNReal.zero_ne_top) fun k g hg => by
        have hS : ∀ᵐ φ ∂((P ^ k : Kernel _ _) ∘ₘ μ), 0 ≤ φ.1 :=
          (measure_eq_zero_iff_ae_notMem.1 (sacKernel_pow_comp_compl _ hα hσw μ hμX k)).mono
            fun φ h => (sq_nonneg σz).trans (not_not.1 h).1.1
        exact (isKalmanLaw_sacGaussian_pow hα hσw hμX hμK k).lintegral_sq hS hg
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
    obtain ⟨K, hK, hKle⟩ := htight 4⁻¹ (by simp)
    set C : Set X := Subtype.val ⁻¹' K
    have hC : IsCompact C := hXc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have hCm : MeasurableSet C := hK.isClosed.measurableSet.preimage measurable_subtype_coe
    have hWF : IsWeakFeller PX := isWeakFeller_restrict_sacKernel _ hα hσw
    have hev := theorem_12_1_2_i hWF hno hC (ε := 4⁻¹) (by simp)
    obtain ⟨n, hn, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
    set ν : Measure X := μ.comap Subtype.val
    have hνmap : ν.map Subtype.val = μ := by
      rw [map_comap_subtype_coe hXm, Measure.restrict_eq_self_of_ae_mem]
      rw [hX]
      exact measure_eq_zero_iff_ae_notMem.1 hμX |>.mono fun _ h => not_not.1 h
    have : IsProbabilityMeasure (ν.map Subtype.val) := by rw [hνmap]; exact hμP
    have hνP : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable
    -- each `μPⁱ` gives the compact set mass at least `1/2`
    have hi : ∀ i : ℕ, 2⁻¹ ≤ ∫⁻ x, (PX ^ i) x C ∂ν := by
      intro i
      have := isMarkovKernel_pow P i
      have hKX : MeasurableSet (K ∩ X) := hK.isClosed.measurableSet.inter hXm
      have hval : Subtype.val '' C = K ∩ X := by
        ext y
        simp [C, and_comm]
      have h1 : ∫⁻ x, (PX ^ i) x C ∂ν = ((P ^ i : Kernel _ _) ∘ₘ μ) (K ∩ X) := by
        rw [Measure.bind_apply hKX (Kernel.aemeasurable _), ← hνmap,
          lintegral_map (Kernel.measurable_coe _ hKX) measurable_subtype_coe, ← hval]
        exact lintegral_congr fun x =>
          restrictKernel_pow_apply P hXm (isAbsorbing_sacSpace _ hα hσw) i x hCm
      rw [h1]
      have hc : ((P ^ i : Kernel _ _) ∘ₘ μ) (K ∩ X)ᶜ ≤ 4⁻¹ := by
        rw [compl_inter]
        calc ((P ^ i : Kernel _ _) ∘ₘ μ) (Kᶜ ∪ Xᶜ)
            ≤ ((P ^ i : Kernel _ _) ∘ₘ μ) Kᶜ + ((P ^ i : Kernel _ _) ∘ₘ μ) Xᶜ :=
              measure_union_le _ _
          _ ≤ 4⁻¹ + 0 := by
              gcongr
              · exact hKle _ ⟨i, rfl⟩
              · rw [hX]
                exact (sacKernel_pow_comp_compl _ hα hσw μ hμX i).le
          _ = 4⁻¹ := add_zero _
      have hsum := measure_add_measure_compl (μ := (P ^ i : Kernel _ _) ∘ₘ μ) hKX
      rw [measure_univ] at hsum
      by_contra hlt
      rw [not_le] at hlt
      have h42 : (4⁻¹ : ℝ≥0∞) ≤ 2⁻¹ := ENNReal.inv_le_inv.2 (by norm_num)
      have : (1 : ℝ≥0∞) < 1 :=
        calc (1 : ℝ≥0∞) = _ := hsum.symm
          _ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_of_lt_of_le (by finiteness) hlt (hc.trans h42)
          _ = 1 := ENNReal.inv_two_add_inv_two
      exact lt_irrefl _ this
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hup : ∫⁻ x, cesaroKernel PX n x C ∂ν ≤ 4⁻¹ :=
      (lintegral_mono fun x => hn x).trans (by rw [lintegral_const, measure_univ, mul_one])
    have hlow : 2⁻¹ ≤ ∫⁻ x, cesaroKernel PX n x C ∂ν := by
      simp_rw [cesaroKernel_apply PX n _ hCm]
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => Kernel.measurable_coe _ hCm),
        lintegral_finsetSum _ fun i _ => Kernel.measurable_coe _ hCm]
      calc (2⁻¹ : ℝ≥0∞) = (n : ℝ≥0∞)⁻¹ * ∑ _i ∈ Finset.Icc 1 n, 2⁻¹ := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_assoc,
              ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
        _ ≤ _ := by gcongr with i; exact hi i
    have : (2⁻¹ : ℝ≥0∞) ≤ 4⁻¹ := hlow.trans hup
    rw [ENNReal.inv_le_inv] at this
    norm_num at this
  obtain ⟨π, hπ, hπinv⟩ := hinv
  have hpos : IsPositive PX ψ := ⟨hψ, π, hπ, hπinv⟩
  exact ⟨hT, ψ, hpos, proposition_10_1_1 hpos, hap⟩

end MeynTweedie.VUniformErgodicity
