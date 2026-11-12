/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Covariance
import AKMMHeterogeneousFirms.SimpleModel

/-!
# Lognormal productivity and wedges (AKMM (22.8), (22.10)–(22.11), App. 22.A.1, 22.A.3)

AKMM, §22.2, p. 665, §22.4, pp. 672–673, and Appendix 22.A.1 and 22.A.3, pp. 888–892. The unit
mass of firms is a probability space `(Ω, P)`, and the book's appeal to the law of large numbers
(`∫ · di = E[·]`) is the identification of the cross-section integral with `∫ · ∂P`.

* **(22.8)** and App. 22.A.1: if `log a ∼ N(ν − σ²/2, σ²)` then `∫ a = e^ν` and
  `A = exp(ν + γσ²/(2(1−γ)))` (`lognormal_mean`, `eq_22_8`); at fixed mean, `A` is strictly
  increasing in the dispersion `σ²` (`lognormal_A_strictMono`).
* **For any distribution**: `A ≥ ∫ a` (`aggTFP_ge_mean`), the general form of "dispersion raises
  `A`".
* **(22.10)–(22.11)** and App. 22.A.3: the normal fact used (the moment generating function of
  `αX + βY` for a bivariate normal `(X, Y)`, `bivariate_mgf`); with
  `(log a, log(1−τ))` bivariate normal with means `(ν_a − σ_a²/2, ν_τ − σ_τ²/2)`,
  `A = exp(ν_a + γ(σ_a² − σ_τ²)/(2(1−γ)))` (`eq_22_11`); `A` depends neither on `ν_τ` nor on
  the correlation (`wedge_A_indep`) and is strictly decreasing in `σ_τ²` (`wedge_A_strictAnti`).
-/

open MeasureTheory ProbabilityTheory

namespace AKMM.HeterogeneousFirms

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### (22.8) -/

/-- AKMM, p. 665: for `log a ∼ N(ν − σ²/2, σ²)` the mean productivity is `∫ a = e^ν`. -/
theorem lognormal_mean {P : Measure Ω} {Z : Ω → ℝ} {ν : ℝ} {v : NNReal}
    (hZ : HasLaw Z (gaussianReal (ν - v / 2) v) P) :
    ∫ ω, Real.exp (Z ω) ∂P = Real.exp ν := by
  have h := mgf_gaussianReal hZ 1
  simp only [mgf, one_mul, one_pow, mul_one] at h
  rw [h]; congr 1; ring

/-- AKMM, (22.8), p. 665 and App. 22.A.1, p. 888: for `log a ∼ N(ν − σ²/2, σ²)`,
`A = (∫ a^{1/(1−γ)})^{1−γ} = exp(ν + γσ²/(2(1−γ)))`. -/
theorem eq_22_8 {P : Measure Ω} {Z : Ω → ℝ} {ν γ : ℝ} {v : NNReal} (hγ1 : γ < 1)
    (hZ : HasLaw Z (gaussianReal (ν - v / 2) v) P) :
    aggTFP P γ (fun ω => Real.exp (Z ω)) = Real.exp (ν + γ / (1 - γ) * (1 / 2) * v) := by
  have h1γ : (1 - γ) ≠ 0 := by linarith
  have h := mgf_gaussianReal hZ (1 / (1 - γ))
  have e : ∀ ω, Real.exp (Z ω) ^ (1 / (1 - γ)) = Real.exp (1 / (1 - γ) * Z ω) := fun ω => by
    rw [← Real.exp_mul, mul_comm]
  unfold aggTFP
  simp only [e]
  rw [show (∫ ω, Real.exp (1 / (1 - γ) * Z ω) ∂P) = mgf Z P (1 / (1 - γ)) from rfl, h,
    ← Real.exp_mul]
  congr 1
  field_simp
  ring

/-- AKMM, p. 665: **dispersion raises `A` at a fixed mean**. With `log a ∼ N(ν − σ²/2, σ²)`
(mean `e^ν` for every `σ`), the closed form of `A` is strictly increasing in `σ²`. -/
theorem lognormal_A_strictMono {ν γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    StrictMono fun s : ℝ => Real.exp (ν + γ / (1 - γ) * (1 / 2) * s) := by
  have hk : 0 < γ / (1 - γ) * (1 / 2) := by
    have : 0 < 1 - γ := by linarith
    positivity
  intro s t hst
  simp only
  rw [Real.exp_lt_exp]
  nlinarith

/-- AKMM, p. 665: **`A` is at least mean productivity**, for any distribution: with `a > 0`,
`p = 1/(1−γ) > 1`, `∫ a > 0` and `a`, `a^p` integrable, `(∫ a^p)^{1/p} ≥ ∫ a` (Jensen). -/
theorem aggTFP_ge_mean {P : Measure Ω} [IsProbabilityMeasure P] {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ < 1) {a : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (haI : Integrable a P)
    (hpI : Integrable (fun ω => a ω ^ (1 / (1 - γ))) P) :
    ∫ ω, a ω ∂P ≤ aggTFP P γ a := by
  set m := ∫ ω, a ω ∂P with hm
  have hm0 : 0 < m := integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => (ha ω).le) haI |>.mpr (by
      have : Function.support a = Set.univ := Set.eq_univ_of_forall fun ω => (ha ω).ne'
      rw [this]; simp)
  have h1γ : 0 < 1 - γ := by linarith
  set p := 1 / (1 - γ) with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ h1γ]; linarith
  -- Bernoulli: (a/m)^p ≥ 1 + p(a/m − 1)
  have hpt : ∀ ω, m ^ p * (1 + p * (a ω / m - 1)) ≤ a ω ^ p := fun ω => by
    have hb := one_add_mul_self_le_rpow_one_add (by
      have : 0 ≤ a ω / m := (div_pos (ha ω) hm0).le
      linarith : (-1 : ℝ) ≤ a ω / m - 1) hp1
    rw [add_sub_cancel, Real.div_rpow (ha ω).le hm0.le] at hb
    have hmp : 0 < m ^ p := Real.rpow_pos_of_pos hm0 p
    calc m ^ p * (1 + p * (a ω / m - 1)) ≤ m ^ p * (a ω ^ p / m ^ p) :=
          mul_le_mul_of_nonneg_left hb hmp.le
      _ = a ω ^ p := by field_simp
  have hlin : Integrable (fun ω => m ^ p * (1 + p * (a ω / m - 1))) P :=
    ((integrable_const 1).add (((haI.div_const m).sub (integrable_const 1)).const_mul p)).const_mul
      _
  have hI := integral_mono hlin hpI hpt
  have hval : ∫ ω, m ^ p * (1 + p * (a ω / m - 1)) ∂P = m ^ p := by
    have h2 : ∀ ω, m ^ p * (1 + p * (a ω / m - 1)) = m ^ p * (1 - p) + m ^ p * p / m * a ω :=
      fun ω => by field_simp; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h2),
      integral_add (integrable_const _) (haI.const_mul _), integral_const, integral_const_mul,
      ← hm]
    simp only [probReal_univ, one_smul]
    field_simp
    ring
  rw [hval] at hI
  unfold aggTFP
  have := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm0 p).le hI h1γ.le
  rwa [← Real.rpow_mul hm0.le, hp, one_div, inv_mul_cancel₀ h1γ.ne', Real.rpow_one,
    ← one_div] at this

/-! ### Bivariate normal and (22.11) -/

/-- AKMM, App. 22.A.3, p. 889: **the normal fact used**. If `(X, Y)` is jointly Gaussian then
`E[exp(αX + βY)] = exp(αE X + βE Y + (α² Var X + 2αβ Cov(X, Y) + β² Var Y)/2)`: `αX + βY` is
normal with that mean and variance. -/
theorem bivariate_mgf {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (α β : ℝ) :
    ∫ ω, Real.exp (α * X ω + β * Y ω) ∂P = Real.exp (α * P[X] + β * P[Y] +
      (α ^ 2 * Var[X; P] + 2 * α * β * cov[X, Y; P] + β ^ 2 * Var[Y; P]) / 2) := by
  have hX := hXY.fst
  have hY := hXY.snd
  set L : ℝ × ℝ →L[ℝ] ℝ := α • ContinuousLinearMap.fst ℝ ℝ ℝ +
    β • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hZ' := hXY.map_fun L
  have eZ : (fun ω => L (X ω, Y ω)) = fun ω => α * X ω + β * Y ω := by
    funext ω; simp [L]
  rw [eZ] at hZ'
  have hαX : MemLp (fun ω => α * X ω) 2 P := hX.memLp_two.const_mul α
  have hβY : MemLp (fun ω => β * Y ω) 2 P := hY.memLp_two.const_mul β
  have hmean : P[fun ω => α * X ω + β * Y ω] = α * P[X] + β * P[Y] := by
    rw [integral_add (hX.integrable.const_mul α) (hY.integrable.const_mul β),
      integral_const_mul, integral_const_mul]
  have hvar : Var[fun ω => α * X ω + β * Y ω; P] =
      α ^ 2 * Var[X; P] + 2 * α * β * cov[X, Y; P] + β ^ 2 * Var[Y; P] := by
    rw [variance_fun_add hαX hβY, variance_const_mul, variance_const_mul,
      covariance_const_mul_left, covariance_const_mul_right]
    ring
  have hlaw := hZ'.map_eq_gaussianReal
  have hmg : mgf (fun ω => α * X ω + β * Y ω) P 1 = ∫ ω, Real.exp (α * X ω + β * Y ω) ∂P := by
    simp [mgf]
  rw [← hmg, ← mgf_id_map hZ'.aemeasurable, hlaw, mgf_id_gaussianReal, hmean, hvar,
    Real.coe_toNNReal _ (by rw [← hvar]; exact variance_nonneg _ _)]
  ring_nf

/-- AKMM, (22.10), p. 672: aggregate productivity with output wedges `τ`,
`A = ∫ a^{1/(1−γ)}(1−τ)^{γ/(1−γ)} / (∫ a^{1/(1−γ)}(1−τ)^{1/(1−γ)})^γ`, written with `b = 1 − τ`. -/
noncomputable def wedgeTFP (P : Measure Ω) (γ : ℝ) (a b : Ω → ℝ) : ℝ :=
  (∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (γ / (1 - γ)) ∂P) /
    (∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ)) ∂P) ^ γ

/-- AKMM, p. 672: with no wedges (`τ ≡ 0`, `b ≡ 1`), (22.10) reduces to (22.6). -/
theorem wedgeTFP_one (P : Measure Ω) {γ : ℝ} {a : Ω → ℝ}
    (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P) :
    wedgeTFP P γ a (fun _ => 1) = aggTFP P γ a := by
  unfold wedgeTFP aggTFP
  simp only [Real.one_rpow, mul_one]
  rw [Real.rpow_sub hI, Real.rpow_one]

/-- The exponent algebra behind (22.11). -/
theorem wedge_exponent {γ νa ντ va vτ cv : ℝ} (hγ1 : γ < 1) :
    1 / (1 - γ) * (νa - va / 2) + γ / (1 - γ) * (ντ - vτ / 2) +
        ((1 / (1 - γ)) ^ 2 * va + 2 * (1 / (1 - γ)) * (γ / (1 - γ)) * cv +
          (γ / (1 - γ)) ^ 2 * vτ) / 2 -
      γ * (1 / (1 - γ) * (νa - va / 2) + 1 / (1 - γ) * (ντ - vτ / 2) +
        ((1 / (1 - γ)) ^ 2 * va + 2 * (1 / (1 - γ)) * (1 / (1 - γ)) * cv +
          (1 / (1 - γ)) ^ 2 * vτ) / 2) =
      νa + γ / (1 - γ) * (1 / 2) * (va - vτ) := by
  have h1γ : (1 - γ) ≠ 0 := by linarith
  field_simp
  ring

/-- AKMM, (22.11), p. 672 and App. 22.A.3, pp. 889–892: if `(log a, log(1−τ))` is bivariate
normal with means `(ν_a − σ_a²/2, ν_τ − σ_τ²/2)`, variances `(σ_a², σ_τ²)` and covariance
`ρσ_aσ_τ`, then `A = exp(ν_a + γ(σ_a² − σ_τ²)/(2(1−γ)))`. -/
theorem eq_22_11 {P : Measure Ω} [IsProbabilityMeasure P] {X T : Ω → ℝ}
    (hXT : HasGaussianLaw (fun ω => (X ω, T ω)) P) {γ νa ντ : ℝ} (hγ1 : γ < 1)
    (hmX : P[X] = νa - Var[X; P] / 2) (hmT : P[T] = ντ - Var[T; P] / 2) :
    wedgeTFP P γ (fun ω => Real.exp (X ω)) (fun ω => Real.exp (T ω)) =
      Real.exp (νa + γ / (1 - γ) * (1 / 2) * (Var[X; P] - Var[T; P])) := by
  have e : ∀ (x t p q : ℝ), Real.exp x ^ p * Real.exp t ^ q = Real.exp (p * x + q * t) :=
    fun x t p q => by rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]; ring_nf
  unfold wedgeTFP
  simp only [e]
  rw [bivariate_mgf hXT, bivariate_mgf hXT, ← Real.exp_mul, ← Real.exp_sub, hmX, hmT]
  congr 1
  rw [← wedge_exponent hγ1]
  ring

/-- AKMM, p. 673: in the lognormal case `A` does not depend on `ν_τ` (the level of the wedge does
not distort the allocation) nor on the correlation `ρ` between `a` and `1 − τ`. -/
theorem wedge_A_indep {P : Measure Ω} [IsProbabilityMeasure P] {X T X' T' : Ω → ℝ}
    (hXT : HasGaussianLaw (fun ω => (X ω, T ω)) P)
    (hXT' : HasGaussianLaw (fun ω => (X' ω, T' ω)) P) {γ νa ντ ντ' : ℝ} (hγ1 : γ < 1)
    (hmX : P[X] = νa - Var[X; P] / 2) (hmT : P[T] = ντ - Var[T; P] / 2)
    (hmX' : P[X'] = νa - Var[X'; P] / 2) (hmT' : P[T'] = ντ' - Var[T'; P] / 2)
    (hvX : Var[X'; P] = Var[X; P]) (hvT : Var[T'; P] = Var[T; P]) :
    wedgeTFP P γ (fun ω => Real.exp (X' ω)) (fun ω => Real.exp (T' ω)) =
      wedgeTFP P γ (fun ω => Real.exp (X ω)) (fun ω => Real.exp (T ω)) := by
  rw [eq_22_11 hXT hγ1 hmX hmT, eq_22_11 hXT' hγ1 hmX' hmT', hvX, hvT]

/-- AKMM, p. 673: **wedge dispersion lowers `A`**: the closed form (22.11) is strictly decreasing
in `σ_τ²`, and equals (22.8) at `σ_τ = 0`. -/
theorem wedge_A_strictAnti {νa γ va : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    StrictAnti (fun vτ : ℝ => Real.exp (νa + γ / (1 - γ) * (1 / 2) * (va - vτ))) ∧
      Real.exp (νa + γ / (1 - γ) * (1 / 2) * (va - 0)) =
        Real.exp (νa + γ / (1 - γ) * (1 / 2) * va) := by
  have hk : 0 < γ / (1 - γ) * (1 / 2) := by
    have : 0 < 1 - γ := by linarith
    positivity
  refine ⟨fun s t hst => ?_, by rw [sub_zero]⟩
  simp only
  rw [Real.exp_lt_exp]
  nlinarith

end AKMM.HeterogeneousFirms
