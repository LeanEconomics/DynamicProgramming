/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Matrix.Mul

/-!
# The scalar Kalman filter of Exercise 10.6(a) and the recursion (10.16)

Miao, Exercise 10.6(a), p. 346, with Example 10.1.1 (p. 329) and Example 10.2.1 (p. 342). With
`α = β = 0` the labour-income model (10.5)–(10.6) is `y_t = z_t + v_t`, `z_{t+1} = ρz_t + η_{t+1}`:
the state space form `x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = Gx_t + Dε_t` with `x = z`, `A = ρ`,
`G = 1`, `ε = (η, v)′`, `C = (σ_η, 0)`, `D = (0, σ_v)`, so `CC′ = σ_η²`, `DD′ = σ_v²`, `CD′ = 0`
(`ex_10_6_a_shocks`). The scalar Kalman objects are defined here under the prefix `hm_`.

Two readings of the filter are proved.

* Least squares (book's (10.8)–(10.11) in the scalar case). For a prior error `e = x − x̂` and
  measurement noise `d = Dε` with second moments `Σ`, `CD′`, `DD′`, the error of the update
  `x̂ + k(Ge + d)` has mean square `(1 − kG)²Σ + k²DD′ − 2(1 − kG)k CD′` (`hm_mse_eq`, the scalar
  (10.11) as an integral against any probability measure), minimised exactly at the gain (10.10)
  `K = (ΣG + CD′)/Ω` with `Ω = G²Σ + DD′ + 2G CD′` (10.8), with minimum
  `Σ_{t|t} = (1 − KG)Σ − K CD′` (`hm_mse_min`). For Exercise 10.6:
  `K_t = Σ_t/(Σ_t + σ_v²)`, `Σ_{t|t} = Σ_t σ_v²/(Σ_t + σ_v²)`, the Riccati equation
  `Σ_{t+1} = ρ²Σ_tσ_v²/(Σ_t + σ_v²) + σ_η²` and the forecast recursion
  `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})` (`ex_10_6_a_gain`, `ex_10_6_a_riccati`,
  `ex_10_6_a_recursion`).
* Gaussian conditioning (book p. 328). With prior `z_t | yᵗ⁻¹ ~ N(x̂, Σ)` and `y_t = z_t + v_t`,
  Bayes' rule gives `z_t | yᵗ ~ N(x̂ + K(y − x̂), Σσ_v²/(Σ + σ_v²))` and
  `y_t | yᵗ⁻¹ ~ N(x̂, Σ + σ_v²)`
  (`hm_gauss_bayes`, `hm_gauss_marginal`); the prediction `z_{t+1} = ρz_t + η` gives
  `N(ρx̂_{t|t}, ρ²Σ_{t|t} + σ_η²)`, and `y_{t+1} | yᵗ ~ N(x̂_{t+1|t}, Ω_{t+1|t})`, the conditional
  law used in Example 10.2.1 (`hm_gauss_predict`, `ex_10_6_a_predictive`).

Finally (10.16): `x̂_{t|t} = x̂_{t|t−1} + K_t(y_t − G_t x̂_{t|t−1})` (10.7) and
`x̂_{t+1|t} = A x̂_{t|t}`
give `x̂_{t+1|t} = A x̂_{t|t−1} + AK_t(y_t − G_t x̂_{t|t−1})` (`eq_10_16`).
-/

namespace Miao.PartialInformation

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Miao, (10.16), p. 342: with the updating equation (10.7) (no control) and
`x̂_{t+1|t} = Ax̂_{t|t}`, `x̂_{t+1|t} = Ax̂_{t|t−1} + AK_t(y_t − G_tx̂_{t|t−1})`. -/
theorem eq_10_16 {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n n ℝ) (G : Matrix m n ℝ)
    (K : Matrix n m ℝ) (xpred xfilt xnext : n → ℝ) (y : m → ℝ)
    (h107 : xfilt = xpred + K.mulVec (y - G.mulVec xpred)) (hnext : xnext = A.mulVec xfilt) :
    xnext = A.mulVec xpred + (A * K).mulVec (y - G.mulVec xpred) := by
  rw [hnext, h107, Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- Miao, Exercise 10.6(a) with Example 10.1.1, p. 329: for `C = (σ_η, 0)`, `D = (0, σ_v)`,
`CC′ = σ_η²`, `DD′ = σ_v²`, `CD′ = 0`. -/
theorem ex_10_6_a_shocks (ση σv : ℝ) :
    let C : Fin 2 → ℝ := ![ση, 0]
    let D : Fin 2 → ℝ := ![0, σv]
    (∑ i, C i * C i = ση ^ 2) ∧ (∑ i, D i * D i = σv ^ 2) ∧ ∑ i, C i * D i = 0 := by
  intro C D
  simp [C, D, Fin.sum_univ_two, sq]

/-- The scalar innovation variance (10.8): `Ω = GΣG′ + DD′ + GCD′ + DC′G′`. -/
def hm_kOmega (G S DD CD : ℝ) : ℝ := G * S * G + DD + G * CD + CD * G

/-- The scalar Kalman gain (10.10): `K = (ΣG′ + CD′)Ω⁻¹`. -/
noncomputable def hm_kGain (G S DD CD : ℝ) : ℝ := (S * G + CD) / hm_kOmega G S DD CD

/-- The scalar mean-square error (10.11) of the update with gain `k`. -/
def hm_kMSE (G S DD CD k : ℝ) : ℝ :=
  (1 - k * G) * S * (1 - k * G) + k * DD * k - (1 - k * G) * CD * k - k * CD * (1 - k * G)

/-- Miao, (10.11), p. 331 (scalar case): if the prior error `e = x_t − x̂_{t|t−1}` and the noise
`d = D_tε_t` have `E[e²] = Σ`, `E[ed] = C_tD′_t` and `E[d²] = D_tD′_t`, the error
`x_t − x̂_{t|t}` of the update `x̂_{t|t} = x̂_{t|t−1} + k a_t`, `a_t = Ge + d`, has mean square
`(1 − kG)Σ(1 − kG) + kDD′k − (1 − kG)CD′k − kDC′(1 − kG)`. -/
theorem hm_mse_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (e d : Ω → ℝ)
    (he : Integrable (fun w => e w ^ 2) μ) (hed : Integrable (fun w => e w * d w) μ)
    (hd : Integrable (fun w => d w ^ 2) μ) (G S DD CD k : ℝ) (hS : ∫ w, e w ^ 2 ∂μ = S)
    (hCD : ∫ w, e w * d w ∂μ = CD) (hDD : ∫ w, d w ^ 2 ∂μ = DD) :
    ∫ w, (e w - k * (G * e w + d w)) ^ 2 ∂μ = hm_kMSE G S DD CD k := by
  have h : (fun w => (e w - k * (G * e w + d w)) ^ 2) = fun w =>
      (1 - k * G) ^ 2 * e w ^ 2 + (k ^ 2 * d w ^ 2 - 2 * (1 - k * G) * k * (e w * d w)) := by
    funext w; ring
  have i1 : Integrable (fun w => (1 - k * G) ^ 2 * e w ^ 2) μ := he.const_mul _
  have i2 : Integrable (fun w => k ^ 2 * d w ^ 2) μ := hd.const_mul _
  have i3 : Integrable (fun w => 2 * (1 - k * G) * k * (e w * d w)) μ := hed.const_mul _
  have i23 : Integrable (fun w => k ^ 2 * d w ^ 2 - 2 * (1 - k * G) * k * (e w * d w)) μ :=
    i2.sub i3
  rw [h, integral_add i1 i23, integral_sub i2 i3, integral_const_mul, integral_const_mul,
    integral_const_mul, hS, hCD, hDD]
  unfold hm_kMSE
  ring

/-- Miao, (10.10)–(10.11), pp. 330–332 (scalar case): when `Ω ≠ 0`,
`MSE(k) = MSE(K) + Ω(k − K)²`, so (for `Ω > 0`) the gain `K = (ΣG + CD′)/Ω` is the unique
minimiser, and `MSE(K) = (1 − KG)Σ − KDC′`. -/
theorem hm_mse_min (G S DD CD k : ℝ) (hΩ : hm_kOmega G S DD CD ≠ 0) :
    hm_kMSE G S DD CD k = hm_kMSE G S DD CD (hm_kGain G S DD CD) +
        hm_kOmega G S DD CD * (k - hm_kGain G S DD CD) ^ 2 ∧
      hm_kMSE G S DD CD (hm_kGain G S DD CD) =
        (1 - hm_kGain G S DD CD * G) * S - hm_kGain G S DD CD * CD := by
  have hM : ∀ k, hm_kMSE G S DD CD k = S - 2 * k * (S * G + CD) + k ^ 2 * hm_kOmega G S DD CD :=
    fun k => by unfold hm_kMSE hm_kOmega; ring
  unfold hm_kGain
  rw [hM, hM]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- Miao, (10.10)–(10.11): for `Ω > 0` the Kalman gain minimises the mean-square error. -/
theorem hm_mse_le (G S DD CD k : ℝ) (hΩ : 0 < hm_kOmega G S DD CD) :
    hm_kMSE G S DD CD (hm_kGain G S DD CD) ≤ hm_kMSE G S DD CD k := by
  rw [(hm_mse_min G S DD CD k hΩ.ne').1]
  exact le_add_of_nonneg_right (mul_nonneg hΩ.le (sq_nonneg _))

/-- Miao, Exercise 10.6(a): with `G = 1`, `DD′ = σ_v²`, `CD′ = 0`, `Ω_t = Σ_t + σ_v²`,
`K_t = Σ_t/(Σ_t + σ_v²)` and `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)`. -/
theorem ex_10_6_a_gain (S sv2 : ℝ) (h : S + sv2 ≠ 0) :
    hm_kOmega 1 S sv2 0 = S + sv2 ∧ hm_kGain 1 S sv2 0 = S / (S + sv2) ∧
      (1 - hm_kGain 1 S sv2 0 * 1) * S - hm_kGain 1 S sv2 0 * 0 = S * sv2 / (S + sv2) := by
  have hO : hm_kOmega 1 S sv2 0 = S + sv2 := by unfold hm_kOmega; ring
  have hK : hm_kGain 1 S sv2 0 = S / (S + sv2) := by unfold hm_kGain; rw [hO]; ring
  refine ⟨hO, hK, ?_⟩
  rw [hK]
  field_simp
  ring

/-- The prediction-error variances `Σ_{t|t−1}` of Exercise 10.6:
`Σ_{0|−1} = Σ₀`, `Σ_{t+1|t} = ρ²Σ_{t|t} + σ_η²` with `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)`. -/
noncomputable def hm_kSig (ρ sη2 sv2 S0 : ℝ) : ℕ → ℝ
  | 0 => S0
  | t + 1 => ρ ^ 2 * (hm_kSig ρ sη2 sv2 S0 t * sv2 / (hm_kSig ρ sη2 sv2 S0 t + sv2)) + sη2

/-- The Kalman gains `K_t = Σ_t/(Σ_t + σ_v²)` of Exercise 10.6. -/
noncomputable def hm_kK (ρ sη2 sv2 S0 : ℝ) (t : ℕ) : ℝ :=
  hm_kSig ρ sη2 sv2 S0 t / (hm_kSig ρ sη2 sv2 S0 t + sv2)

/-- The innovation variances `Ω_{t|t−1} = Σ_t + σ_v²`, as `ℝ≥0`. -/
noncomputable def hm_kOm (ρ sη2 sv2 S0 : ℝ) (t : ℕ) : ℝ≥0 :=
  Real.toNNReal (hm_kSig ρ sη2 sv2 S0 t + sv2)

/-- Miao, Exercise 10.6(a): the prediction variances are nonnegative when
`Σ₀, σ_η² ≥ 0` and `σ_v² > 0`. -/
theorem hm_kSig_nonneg (ρ sη2 sv2 S0 : ℝ) (hS0 : 0 ≤ S0) (hη : 0 ≤ sη2) (hv : 0 < sv2) :
    ∀ t, 0 ≤ hm_kSig ρ sη2 sv2 S0 t
  | 0 => hS0
  | t + 1 => by
    have := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv t
    simp only [hm_kSig]
    have : 0 < hm_kSig ρ sη2 sv2 S0 t + sv2 := by linarith
    positivity

/-- Miao, Exercise 10.6(a) (Riccati equation): `Σ_{t+1|t} = ρ²Σ_{t|t} + σ_η²` with
`Σ_{t|t} = (1 − K_t)Σ_t`, i.e. the book's `Σ_{t+1|t} = A Σ_{t|t} A′ + CC′`. -/
theorem ex_10_6_a_riccati (ρ sη2 sv2 S0 : ℝ) (hS0 : 0 ≤ S0) (hη : 0 ≤ sη2) (hv : 0 < sv2)
    (t : ℕ) :
    hm_kSig ρ sη2 sv2 S0 (t + 1) =
      ρ * ((1 - hm_kK ρ sη2 sv2 S0 t) * hm_kSig ρ sη2 sv2 S0 t) * ρ + sη2 := by
  have h0 := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv t
  have : hm_kSig ρ sη2 sv2 S0 t + sv2 ≠ 0 := by linarith
  simp only [hm_kSig, hm_kK]
  field_simp
  ring

/-- Miao, Exercise 10.6(a) and (10.16): `x̂_{t|t} = x̂_{t|t−1} + K_t(y_t − x̂_{t|t−1})` and
`x̂_{t+1|t} = ρx̂_{t|t}` give `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})`. -/
theorem ex_10_6_a_recursion (ρ K xpred y : ℝ) :
    ρ * (xpred + K * (y - xpred)) = ρ * xpred + ρ * K * (y - xpred) := by ring

/-- Miao, p. 328 (Gaussian conditioning, scalar): with prior `z ~ N(m, v₁)` and `y = z + v`,
`v ~ N(0, v₂)` independent, the joint density factors as
`φ(z; m, v₁) φ(y; z, v₂) = φ(y; m, v₁ + v₂) φ(z; m + K(y − m), v₁v₂/(v₁ + v₂))`,
`K = v₁/(v₁ + v₂)`. -/
theorem hm_gauss_bayes (m : ℝ) {v1 v2 : ℝ≥0} (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (z y : ℝ) :
    gaussianPDFReal m v1 z * gaussianPDFReal z v2 y =
      gaussianPDFReal m (v1 + v2) y *
        gaussianPDFReal (m + v1 / (v1 + v2) * (y - m)) (v1 * v2 / (v1 + v2)) z := by
  have p1 : (0 : ℝ) < v1 := lt_of_le_of_ne v1.2 (fun h => h1 (by exact_mod_cast h.symm))
  have p2 : (0 : ℝ) < v2 := lt_of_le_of_ne v2.2 (fun h => h2 (by exact_mod_cast h.symm))
  have p12 : (0 : ℝ) < v1 + v2 := by linarith
  simp only [gaussianPDFReal, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul]
  have hs : √(2 * Real.pi * v1) * √(2 * Real.pi * v2) =
      √(2 * Real.pi * (v1 + v2)) * √(2 * Real.pi * (v1 * v2 / (v1 + v2))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have he : -(z - m) ^ 2 / (2 * (v1 : ℝ)) + -(y - z) ^ 2 / (2 * v2) =
      -(y - m) ^ 2 / (2 * (v1 + v2)) +
        -(z - (m + v1 / (v1 + v2) * (y - m))) ^ 2 / (2 * (v1 * v2 / (v1 + v2))) := by
    field_simp
    ring
  calc _ = (√(2 * Real.pi * v1) * √(2 * Real.pi * v2))⁻¹ *
        Real.exp (-(z - m) ^ 2 / (2 * (v1 : ℝ)) + -(y - z) ^ 2 / (2 * v2)) := by
        rw [mul_inv, Real.exp_add]; ring
    _ = _ := by rw [hs, he, mul_inv, Real.exp_add]; ring

/-- Miao, p. 329: the predictive density of the signal, `y | yᵗ⁻¹ ~ N(m, v₁ + v₂)`:
`∫ φ(z; m, v₁) φ(y; z, v₂) dz = φ(y; m, v₁ + v₂)`. -/
theorem hm_gauss_marginal (m : ℝ) {v1 v2 : ℝ≥0} (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (y : ℝ) :
    ∫ z, gaussianPDFReal m v1 z * gaussianPDFReal z v2 y = gaussianPDFReal m (v1 + v2) y := by
  have hw : v1 * v2 / (v1 + v2) ≠ 0 := by
    have : v1 + v2 ≠ 0 := by
      intro h; exact h1 (le_antisymm (h ▸ le_add_of_nonneg_right v2.2) v1.2)
    exact div_ne_zero (mul_ne_zero h1 h2) this
  simp only [hm_gauss_bayes m h1 h2]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hw, mul_one]

/-- Miao, p. 328 (prediction step, Gaussian): if `z ~ N(m, P)` and `η ~ N(0, σ_η²)` are
independent then `ρz + η ~ N(ρm, ρ²P + σ_η²)`. -/
theorem hm_gauss_predict (ρ m : ℝ) (P sη2 : ℝ≥0) :
    ((gaussianReal m P).map (ρ * ·)) ∗ gaussianReal 0 sη2 =
      gaussianReal (ρ * m) (Real.toNNReal (ρ ^ 2) * P + sη2) := by
  rw [gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal, add_zero]
  congr 2
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg ρ)]
  rfl

/-- Miao, Example 10.2.1, p. 342, in the setting of Exercise 10.6(a): if
`z_t | yᵗ ~ N(x̂_{t|t}, Σ_{t|t})` with `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)`, then
`y_{t+1} = ρz_t + η_{t+1} + v_{t+1}` has the conditional law `N(ρx̂_{t|t}, Ω_{t+1|t})`,
`Ω_{t+1|t} = Σ_{t+1|t} + σ_v²`. -/
theorem ex_10_6_a_predictive (ρ sη2 sv2 S0 : ℝ) (hS0 : 0 ≤ S0) (hη : 0 ≤ sη2) (hv : 0 < sv2)
    (t : ℕ) (xfilt : ℝ) :
    (((gaussianReal xfilt (Real.toNNReal (hm_kSig ρ sη2 sv2 S0 t * sv2 /
        (hm_kSig ρ sη2 sv2 S0 t + sv2)))).map (ρ * ·)) ∗ gaussianReal 0 (Real.toNNReal sη2)) ∗
        gaussianReal 0 (Real.toNNReal sv2) =
      gaussianReal (ρ * xfilt) (hm_kOm ρ sη2 sv2 S0 (t + 1)) := by
  rw [hm_gauss_predict, gaussianReal_conv_gaussianReal, add_zero]
  congr 1
  have h0 := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv t
  have h1 := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv (t + 1)
  unfold hm_kOm
  apply NNReal.eq
  have hp : 0 ≤ hm_kSig ρ sη2 sv2 S0 t * sv2 / (hm_kSig ρ sη2 sv2 S0 t + sv2) := by positivity
  rw [Real.coe_toNNReal _ (by linarith), NNReal.coe_add, NNReal.coe_add, NNReal.coe_mul,
    Real.coe_toNNReal _ (sq_nonneg ρ), Real.coe_toNNReal _ hp, Real.coe_toNNReal _ hη,
    Real.coe_toNNReal _ hv.le]
  rfl

end Miao.PartialInformation
