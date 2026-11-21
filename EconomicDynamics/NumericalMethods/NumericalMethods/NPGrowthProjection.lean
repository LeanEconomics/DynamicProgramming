/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The projection method for the stochastic growth model

Miao, *Economic Dynamics in Discrete Time*, §11.5 (pp. 373–376).

For the growth model `max E ∑ βᵗ u(C_t)`, `C_t + K_{t+1} = f(K_t, z_t)`,
`ln z_{t+1} = ρ ln z_t + σ ε_{t+1}`, the book rewrites the Euler equation (11.8)
for a policy `K' = g(K, z)` as the functional equation
`0 = f(k, z) − g(k, z) − (u')⁻¹(β ∫ I(k, z, ε) e^{−ε²/2}/√(2π) dε) ≡ F(g)(k, z)`.

* `np_growthF_iff_euler`: `F(g)(k, z) = 0` iff the Euler equation (11.8) holds at
  `(k, z)` (for positive consumption, with `(u')⁻¹` a two-sided inverse of `u'`
  on positive reals, e.g. CRRA `np_crra_inverse`).
* `np_gaussHermite_change`: the change of variables `ε = √2 y` behind the
  Gauss–Hermite approximation:
  `∫ I(ε) e^{−ε²/2}/√(2π) dε = π^{−1/2} ∫ I(√2 y) e^{−y²} dy`; hence when the
  Gauss–Hermite rule is exact the book's residual `R(k, z; c)` equals
  `F(ĝ)(k, z)` (`np_growth_residual_eq_F`).
* The truncation `z_m = exp(−4σ/√(1 − ρ²))`, `z_M = exp(4σ/√(1 − ρ²))` is four
  stationary standard deviations of `ln z` on each side (`np_ar1_stationary_variance`,
  `np_z_bounds`), and the normalisation `x = (2k − k_m − k_M)/(k_M − k_m)` maps
  `[k_m, k_M]` onto `[−1, 1]`, where the Chebyshev weight is defined
  (`np_normalize_mem_Icc`).

The numerical solution (choice of `c`, root finding, stability checks) is
algorithmic and not formalised.
-/

namespace Miao.NumericalMethods.NP

open Real MeasureTheory

/-- Miao, p. 374: `I(k, z, ε) = u'(f(g(k, z), z') − g(g(k, z), z')) f'(g(k, z), z')` with
`z' = exp(ρ ln z + σε)`. Here `up = u'` and `fk = ∂f/∂k`. -/
noncomputable def np_growthI (up : ℝ → ℝ) (f fk g : ℝ → ℝ → ℝ) (ρ σ k z ε : ℝ) : ℝ :=
  up (f (g k z) (exp (ρ * log z + σ * ε)) - g (g k z) (exp (ρ * log z + σ * ε))) *
    fk (g k z) (exp (ρ * log z + σ * ε))

/-- Miao, p. 374: the operator `F(g)(k, z) = f(k, z) − g(k, z) − (u')⁻¹(β ∫ I(k, z, ε) φ(ε) dε)`
with `φ` the standard normal density. -/
noncomputable def np_growthF (up upinv : ℝ → ℝ) (f fk g : ℝ → ℝ → ℝ) (β ρ σ k z : ℝ) : ℝ :=
  f k z - g k z - upinv (β * ∫ ε, np_growthI up f fk g ρ σ k z ε * (exp (-ε ^ 2 / 2) / √(2 * π)))

/-- Miao, (11.8) and p. 374: for positive consumption `f(k, z) − g(k, z)` and a positive
right-hand side, `F(g)(k, z) = 0` iff the Euler equation
`u'(f(k, z) − g(k, z)) = β E[u'(f(k', z') − g(k', z')) f'(k', z')]`, `k' = g(k, z)`, holds, where
`(u')⁻¹` is a two-sided inverse of `u'` on the positive reals. -/
theorem np_growthF_iff_euler {up upinv : ℝ → ℝ}
    (hinv1 : ∀ c, 0 < c → upinv (up c) = c) (hinv2 : ∀ y, 0 < y → up (upinv y) = y)
    (f fk g : ℝ → ℝ → ℝ) (β ρ σ k z : ℝ) (hc : 0 < f k z - g k z)
    (hE : 0 < β * ∫ ε, np_growthI up f fk g ρ σ k z ε * (exp (-ε ^ 2 / 2) / √(2 * π))) :
    np_growthF up upinv f fk g β ρ σ k z = 0 ↔
      up (f k z - g k z) =
        β * ∫ ε, np_growthI up f fk g ρ σ k z ε * (exp (-ε ^ 2 / 2) / √(2 * π)) := by
  unfold np_growthF
  constructor
  · intro h
    rw [sub_eq_zero] at h
    rw [h, hinv2 _ hE]
  · intro h
    rw [← h, hinv1 _ hc, sub_self]

/-- CRRA marginal utility `u'(c) = c^{−γ}` has the inverse `(u')⁻¹(y) = y^{−1/γ}` on the positive
reals (an instance of the hypotheses of `np_growthF_iff_euler`). -/
theorem np_crra_inverse {γ : ℝ} (hγ : 0 < γ) :
    (∀ c : ℝ, 0 < c → (c ^ (-γ)) ^ (-1 / γ) = c) ∧
      ∀ y : ℝ, 0 < y → (y ^ (-1 / γ)) ^ (-γ) = y := by
  have key : -γ * (-1 / γ) = 1 := by field_simp
  refine ⟨fun c hc => ?_, fun y hy => ?_⟩
  · rw [← rpow_mul hc.le, key, rpow_one]
  · rw [← rpow_mul hy.le, mul_comm, key, rpow_one]

/-- Miao, p. 374, the Gauss–Hermite change of variables `ε = √2 y`:
`∫ I(ε) e^{−ε²/2}/√(2π) dε = π^{−1/2} ∫ I(√2 y) e^{−y²} dy`. -/
theorem np_gaussHermite_change (I : ℝ → ℝ) :
    ∫ ε, I ε * (exp (-ε ^ 2 / 2) / √(2 * π)) = (√π)⁻¹ * ∫ y, I (√2 * y) * exp (-y ^ 2) := by
  set h : ℝ → ℝ := fun ε => I ε * (exp (-ε ^ 2 / 2) / √(2 * π)) with hh
  have hs2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hspi : 0 < √π := sqrt_pos.2 pi_pos
  have hs2pos : 0 < √2 := sqrt_pos.2 (by norm_num)
  have hsplit : √(2 * π) = √2 * √π := sqrt_mul (by norm_num) π
  have h1 : (fun y => I (√2 * y) * exp (-y ^ 2)) = fun y => √(2 * π) * h (√2 * y) := by
    funext y
    simp only [hh]
    have : -(√2 * y) ^ 2 / 2 = -y ^ 2 := by rw [mul_pow, hs2]; ring
    rw [this]
    have hne : √(2 * π) ≠ 0 := by rw [hsplit]; positivity
    field_simp
  rw [h1, integral_const_mul, Measure.integral_comp_mul_left h √2, abs_of_pos (inv_pos.2 hs2pos),
    hsplit, smul_eq_mul]
  field_simp

/-- Miao, p. 375: when the Gauss–Hermite rule with nodes `εⱼ` and weights `wⱼ` is exact for
`y ↦ I(k, z, √2 y)`, the residual `R(k, z; c) = f − ĝ − (u')⁻¹(βπ^{−1/2} ∑ⱼ I(k, z, √2 εⱼ) wⱼ)`
equals `F(ĝ)(k, z)`. -/
theorem np_growth_residual_eq_F (up upinv : ℝ → ℝ) (f fk g : ℝ → ℝ → ℝ) (β ρ σ k z : ℝ)
    {m : ℕ} (εq wq : Fin m → ℝ)
    (hexact : ∑ j, np_growthI up f fk g ρ σ k z (√2 * εq j) * wq j =
      ∫ y, np_growthI up f fk g ρ σ k z (√2 * y) * exp (-y ^ 2)) :
    f k z - g k z - upinv (β * ((√π)⁻¹ * ∑ j, np_growthI up f fk g ρ σ k z (√2 * εq j) * wq j)) =
      np_growthF up upinv f fk g β ρ σ k z := by
  rw [hexact, ← np_gaussHermite_change]
  rfl

/-- The stationary variance of the AR(1) `s' = ρs + σε` (Miao, p. 375): `v = ρ²v + σ²` iff
`v = σ²/(1 − ρ²)`, for `|ρ| < 1`. -/
theorem np_ar1_stationary_variance {ρ σ v : ℝ} (hρ : |ρ| < 1) :
    v = ρ ^ 2 * v + σ ^ 2 ↔ v = σ ^ 2 / (1 - ρ ^ 2) := by
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ρ]
    linarith
  rw [eq_div_iff h.ne']
  constructor <;> intro e <;> linarith

/-- Miao, p. 375: the truncation `z_m = exp(−4σ/√(1 − ρ²))`, `z_M = exp(4σ/√(1 − ρ²))` satisfies
`z_m < 1 < z_M`, `z_m z_M = 1`, and `ln z_M` is four stationary standard deviations of `ln z`. -/
theorem np_z_bounds {ρ σ : ℝ} (hρ : |ρ| < 1) (hσ : 0 < σ) :
    exp (-4 * σ / √(1 - ρ ^ 2)) < 1 ∧ 1 < exp (4 * σ / √(1 - ρ ^ 2)) ∧
      exp (-4 * σ / √(1 - ρ ^ 2)) * exp (4 * σ / √(1 - ρ ^ 2)) = 1 ∧
        log (exp (4 * σ / √(1 - ρ ^ 2))) = 4 * √(σ ^ 2 / (1 - ρ ^ 2)) := by
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ρ]
    linarith
  have hs : 0 < √(1 - ρ ^ 2) := sqrt_pos.2 h
  have hpos : 0 < 4 * σ / √(1 - ρ ^ 2) := by positivity
  refine ⟨?_, one_lt_exp_iff.2 hpos, ?_, ?_⟩
  · rw [exp_lt_one_iff, neg_mul, neg_div]
    linarith
  · rw [← exp_add, neg_mul, neg_div, neg_add_cancel, exp_zero]
  · rw [log_exp, sqrt_div (sq_nonneg σ), sqrt_sq hσ.le]
    ring

/-- Miao, p. 375: the normalisation `x = (2k − k_m − k_M)/(k_M − k_m)` maps `[k_m, k_M]` onto
`[−1, 1]` (endpoints to endpoints), the domain of the Chebyshev weight `(1 − x²)^{−1/2}`. -/
theorem np_normalize_mem_Icc {km kM : ℝ} (h : km < kM) (k : ℝ) :
    (k ∈ Set.Icc km kM ↔ (2 * k - km - kM) / (kM - km) ∈ Set.Icc (-1) 1) ∧
      (2 * km - km - kM) / (kM - km) = -1 ∧ (2 * kM - km - kM) / (kM - km) = 1 := by
  have hd : 0 < kM - km := sub_pos.2 h
  refine ⟨?_, by field_simp; ring, by field_simp; ring⟩
  simp only [Set.mem_Icc, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end Miao.NumericalMethods.NP
