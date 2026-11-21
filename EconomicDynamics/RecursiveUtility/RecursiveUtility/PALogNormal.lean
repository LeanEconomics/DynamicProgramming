/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PAPortfolio
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Basic

/-!
# The log-linear (lognormal) approximation of Campbell

Miao, *Economic Dynamics in Discrete Time*, §20.4.2 (pp. 715–716), equations (20.32)–(20.35).

The time-`t` conditional distribution is a probability measure `P` on a sample space `Ω`. The
log consumption growth, log wealth return and log return on asset `i` are the random variables
`X 0 = Δc_{t+1}`, `X 1 = r_{w,t+1}`, `X 2 = r_{i,t+1}`; "conditionally lognormal and
homoskedastic" means they are jointly Gaussian with mean vector `μ` and covariance matrix `V`
(`pa_JointGaussian`: every linear combination `∑ a_k X_k` has law `N(a·μ, aᵀVa)`; a concrete
instance is `pa_jointGaussian_rank_one`). The book's notation is
`σ_c² = V 0 0`, `σ_w² = V 1 1`, `σ_cw = V 0 1`, `σ_i² = V 2 2`, `σ_ic = V 2 0`, `σ_iw = V 2 1`.

* Campbell's formula `ln E X = E ln X + ½ Var ln X` for lognormal `X`:
  `pa_log_integral_exp_gaussian`, and for linear combinations `pa_integral_exp_lin`,
  `pa_lognormal_euler`.
* The log form of (20.26): `pa_eq_20_26_log`; (20.32): `eq_20_32`; (20.33): `eq_20_33`;
  (20.34): `eq_20_34`; (20.35): `eq_20_35`; and the expected log return on equity
  `E_t r_{e,t+1} = μ_e + ρ E_t Δc_{t+1}` (p. 718): `pa_expected_equity_return`.

Departure: in (20.32) the last variance term is `½((ρ−γ)/(1−ρ))² σ_w²` (the square is lost
in the printed text; (20.34) prints it). See `docs/PA-corrections.md`.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- The linear form `a · μ = ∑_k a_k μ_k`. -/
def pa_lin {n : ℕ} (μ a : Fin n → ℝ) : ℝ := ∑ k, a k * μ k

/-- The quadratic form `aᵀ V a = ∑_k ∑_l a_k a_l V_{kl}`. -/
def pa_quad {n : ℕ} (V : Fin n → Fin n → ℝ) (a : Fin n → ℝ) : ℝ := ∑ k, ∑ l, a k * a l * V k l

/-- Miao, p. 715: the random vector `X` is (conditionally) jointly Gaussian with mean `μ` and
covariance matrix `V`: every linear combination `∑ a_k X_k` has law `N(a · μ, aᵀ V a)`. -/
def pa_JointGaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (μ : Fin n → ℝ) (V : Fin n → Fin n → ℝ) : Prop :=
  ∀ a : Fin n → ℝ, HasLaw (fun ω => ∑ k, a k * X k ω)
    (gaussianReal (pa_lin μ a) (pa_quad V a).toNNReal) P

/-- A concrete instance of `pa_JointGaussian`: on `(ℝ, N(0, 1))`, the vector `X_k(ω) = b_k ω`
is jointly Gaussian with mean `0` and covariance `V_{kl} = b_k b_l`. -/
theorem pa_jointGaussian_rank_one {n : ℕ} (b : Fin n → ℝ) :
    pa_JointGaussian (gaussianReal 0 1) (fun k ω => b k * ω) (fun _ => 0)
      (fun k l => b k * b l) := by
  intro a
  have hfun : (fun ω : ℝ => ∑ k, a k * (b k * ω)) = fun ω => (∑ k, a k * b k) * ω := by
    funext ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hq : pa_quad (fun k l => b k * b l) a = (∑ k, a k * b k) ^ 2 := by
    simp only [pa_quad, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨by fun_prop, ?_⟩
  rw [hfun, gaussianReal_map_const_mul, hq]
  simp only [pa_lin, mul_zero, Finset.sum_const_zero, mul_one]
  congr 1
  ext
  simp only [NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg _)]

/-- Miao, p. 715: Campbell's formula `ln E X = E ln X + ½ Var ln X` for a lognormal `X = e^Y`,
`Y ∼ N(m, v)`: `ln E e^Y = m + v/2 = E Y + ½ Var Y`. -/
theorem pa_log_integral_exp_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} {m : ℝ} {v : NNReal} (hY : HasLaw Y (gaussianReal m v) P) :
    Real.log (∫ ω, Real.exp (Y ω) ∂P) = m + v / 2 ∧ m + v / 2 = P[Y] + Var[Y; P] / 2 := by
  have h := mgf_gaussianReal hY 1
  simp only [mgf, one_mul, mul_one, one_pow] at h
  refine ⟨by rw [h, Real.log_exp], ?_⟩
  rw [hY.integral_eq, integral_id_gaussianReal, hY.variance_eq, variance_id_gaussianReal]

/-- The expectation of `exp(c + ∑ a_k X_k)` for a jointly Gaussian `X`:
`E exp(c + a · X) = exp(c + a · μ + ½ aᵀ V a)`. -/
theorem pa_integral_exp_lin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ} {μ : Fin n → ℝ} {V : Fin n → Fin n → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * X k ω) ∂P = Real.exp (c + pa_lin μ a + pa_quad V a / 2) := by
  have h := mgf_gaussianReal (hG a) 1
  simp only [mgf, one_mul, mul_one, one_pow, Real.coe_toNNReal _ (hV a)] at h
  simp only [Real.exp_add, integral_const_mul]
  rw [h, Real.exp_add, mul_assoc]

/-- Miao, p. 715: an Euler equation `E_t exp(c + a · X) = 1` with jointly Gaussian log
variables holds iff `c + a · μ + ½ aᵀ V a = 0`. -/
theorem pa_lognormal_euler {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ} {μ : Fin n → ℝ} {V : Fin n → Fin n → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * X k ω) ∂P = 1 ↔ c + pa_lin μ a + pa_quad V a / 2 = 0 := by
  rw [pa_integral_exp_lin hG hV, Real.exp_eq_one_iff]

theorem pa_lin_three (μ : Fin 3 → ℝ) (a0 a1 a2 : ℝ) :
    pa_lin μ ![a0, a1, a2] = a0 * μ 0 + a1 * μ 1 + a2 * μ 2 := by
  simp only [pa_lin, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem pa_quad_three {V : Fin 3 → Fin 3 → ℝ} (hV : ∀ k l, V k l = V l k) (a0 a1 a2 : ℝ) :
    pa_quad V ![a0, a1, a2] = a0 ^ 2 * V 0 0 + a1 ^ 2 * V 1 1 + a2 ^ 2 * V 2 2
      + 2 * a0 * a1 * V 0 1 + 2 * a2 * a0 * V 2 0 + 2 * a2 * a1 * V 2 1 := by
  simp only [pa_quad, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [hV 1 0, hV 0 2, hV 1 2]
  ring

theorem pa_sum_three (X : Fin 3 → ℝ) (a0 a1 a2 : ℝ) :
    ∑ k, ![a0, a1, a2] k * X k = a0 * X 0 + a1 * X 1 + a2 * X 2 := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- In levels, `β^θ (C'/C)^{−ρθ} R_w^{θ'} R_i^{θ''} = exp(θ ln β − ρθ Δc + θ' r_w + θ'' r_i)`. -/
theorem pa_levels_eq_exp {β : ℝ} (hβ : 0 < β) (θ e0 e1 e2 x0 x1 x2 : ℝ) :
    β ^ θ * Real.exp x0 ^ e0 * Real.exp x1 ^ e1 * Real.exp x2 ^ e2
      = Real.exp (θ * Real.log β + ∑ k, ![e0, e1, e2] k * ![x0, x1, x2] k) := by
  rw [Real.rpow_def_of_pos hβ, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, pa_sum_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring_nf

/-- Miao, p. 715: the log form of (20.26). With `θ = (1 − γ)/(1 − ρ)`, `C'/C = e^{Δc}`,
`R_w = e^{r_w}` and `(Δc, r_w, r_i)` jointly Gaussian,
`0 = θ ln β − ρθ E_t Δc + θ E_t r_w + ½(ρθ)² σ_c² − ρθ·θ σ_cw + ½ θ² σ_w²`. -/
theorem pa_eq_20_26_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin 3 → Ω → ℝ} {μ : Fin 3 → ℝ} {V : Fin 3 → Fin 3 → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (hVs : ∀ k l, V k l = V l k)
    {β ρ γ : ℝ} (hβ : 0 < β)
    (h26 : ∫ ω, β ^ ((1 - γ) / (1 - ρ)) * Real.exp (X 0 ω) ^ (-ρ * ((1 - γ) / (1 - ρ)))
      * Real.exp (X 1 ω) ^ ((1 - γ) / (1 - ρ)) ∂P = 1) :
    0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * μ 0
      + (1 - γ) / (1 - ρ) * μ 1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * V 0 0
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * V 0 1
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * V 1 1 := by
  set θ := (1 - γ) / (1 - ρ)
  have hpt : ∀ ω, β ^ θ * Real.exp (X 0 ω) ^ (-ρ * θ) * Real.exp (X 1 ω) ^ θ
      = Real.exp (θ * Real.log β + ∑ k, ![-ρ * θ, θ, 0] k * X k ω) := by
    intro ω
    have := pa_levels_eq_exp hβ θ (-ρ * θ) θ 0 (X 0 ω) (X 1 ω) (X 2 ω)
    rw [Real.rpow_zero, mul_one] at this
    rw [this, pa_sum_three, pa_sum_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  simp only [hpt] at h26
  rw [pa_lognormal_euler hG hV, pa_lin_three, pa_quad_three hVs] at h26
  linear_combination -h26

/-- Miao, (20.32), p. 715: the log form of (20.28) (riskless asset, `R_f = e^{r_f}` known at
`t`), `0 = r_f + θ ln β − ρθ E_t Δc + (θ − 1) E_t r_w + ½(ρθ)² σ_c² − ρθ(θ − 1) σ_cw
+ ½(θ − 1)² σ_w²`, with `θ − 1 = (ρ − γ)/(1 − ρ)`. -/
theorem eq_20_32 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin 3 → Ω → ℝ} {μ : Fin 3 → ℝ} {V : Fin 3 → Fin 3 → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (hVs : ∀ k l, V k l = V l k)
    {β ρ γ rf : ℝ} (hβ : 0 < β)
    (h28 : ∫ ω, β ^ ((1 - γ) / (1 - ρ)) * Real.exp (X 0 ω) ^ (-ρ * ((1 - γ) / (1 - ρ)))
      * Real.exp (X 1 ω) ^ ((1 - γ) / (1 - ρ) - 1) * Real.exp rf ∂P = 1) :
    0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * μ 0
      + ((1 - γ) / (1 - ρ) - 1) * μ 1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * V 0 0
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * V 0 1
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * V 1 1 := by
  set θ := (1 - γ) / (1 - ρ)
  have hpt : ∀ ω, β ^ θ * Real.exp (X 0 ω) ^ (-ρ * θ) * Real.exp (X 1 ω) ^ (θ - 1)
      * Real.exp rf = Real.exp ((rf + θ * Real.log β) + ∑ k, ![-ρ * θ, θ - 1, 0] k * X k ω) := by
    intro ω
    have := pa_levels_eq_exp hβ θ (-ρ * θ) (θ - 1) 0 (X 0 ω) (X 1 ω) (X 2 ω)
    rw [Real.rpow_zero, mul_one] at this
    rw [this, pa_sum_three, pa_sum_three, ← Real.exp_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    ring_nf
  simp only [hpt] at h28
  rw [pa_lognormal_euler hG hV, pa_lin_three, pa_quad_three hVs] at h28
  linear_combination -h28

/-- Miao, (20.33), p. 716: eliminating `σ_cw` between the log form of (20.26) and (20.32),
`r_f = −ln β + ρ E_t Δc − ½ (γ − ρ)/(1 − ρ) σ_w² − ρ²(1 − γ)/(2(1 − ρ)) σ_c²`. -/
theorem eq_20_33 {β ρ γ rf m0 m1 v00 v01 v11 : ℝ} (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hA : 0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + (1 - γ) / (1 - ρ) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * v11)
    (hB : 0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11) :
    rf = -Real.log β + ρ * m0 - 1 / 2 * ((γ - ρ) / (1 - ρ)) * v11
      - ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) * v00 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  set θ := (1 - γ) / (1 - ρ) with hθ
  have hθ0 : θ ≠ 0 := div_ne_zero h2 h1
  have key : θ * (rf - (-Real.log β + ρ * m0 + 1 / 2 * (θ - 1) * v11
      - ρ ^ 2 * θ / 2 * v00)) = 0 := by
    linear_combination (θ - 1) * hA - θ * hB
  have := (mul_eq_zero.1 key).resolve_left hθ0
  have e1 : θ - 1 = -((γ - ρ) / (1 - ρ)) := by rw [hθ]; field_simp; ring
  have e2 : ρ ^ 2 * θ / 2 = ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) := by rw [hθ]; field_simp
  rw [e1, e2] at this
  linarith

/-- Miao, (20.34), p. 716: the log form of the Euler equation (20.29) for asset `i`,
`0 = E_t r_i + θ ln β − ρθ E_t Δc + (θ − 1) E_t r_w + ½(ρθ)² σ_c² − ρθ(θ − 1)σ_cw
+ ½(θ − 1)² σ_w² + ½ σ_i² − ρθ σ_ic + (θ − 1) σ_iw`. -/
theorem eq_20_34 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin 3 → Ω → ℝ} {μ : Fin 3 → ℝ} {V : Fin 3 → Fin 3 → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (hVs : ∀ k l, V k l = V l k)
    {β ρ γ : ℝ} (hβ : 0 < β)
    (h29 : ∫ ω, β ^ ((1 - γ) / (1 - ρ)) * Real.exp (X 0 ω) ^ (-ρ * ((1 - γ) / (1 - ρ)))
      * Real.exp (X 1 ω) ^ ((1 - γ) / (1 - ρ) - 1) * Real.exp (X 2 ω) ^ (1 : ℝ) ∂P = 1) :
    0 = μ 2 + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * μ 0
      + ((1 - γ) / (1 - ρ) - 1) * μ 1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * V 0 0
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * V 0 1
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * V 1 1
      + 1 / 2 * V 2 2 - ρ * ((1 - γ) / (1 - ρ)) * V 2 0
      + ((1 - γ) / (1 - ρ) - 1) * V 2 1 := by
  set θ := (1 - γ) / (1 - ρ)
  have hpt : ∀ ω, β ^ θ * Real.exp (X 0 ω) ^ (-ρ * θ) * Real.exp (X 1 ω) ^ (θ - 1)
      * Real.exp (X 2 ω) ^ (1 : ℝ)
      = Real.exp (θ * Real.log β + ∑ k, ![-ρ * θ, θ - 1, 1] k * X k ω) := by
    intro ω
    rw [pa_levels_eq_exp hβ θ (-ρ * θ) (θ - 1) 1 (X 0 ω) (X 1 ω) (X 2 ω), pa_sum_three,
      pa_sum_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  simp only [hpt] at h29
  rw [pa_lognormal_euler hG hV, pa_lin_three, pa_quad_three hVs] at h29
  linear_combination -h29

/-- Miao, (20.35), p. 716: combining (20.32) and (20.34), the risk premium on asset `i`,
`E_t r_i − r_f + ½ σ_i² = ρ(1 − γ)/(1 − ρ) σ_ic + (γ − ρ)/(1 − ρ) σ_iw`. -/
theorem eq_20_35 {β ρ γ rf m0 m1 m2 v00 v01 v11 v22 v20 v21 : ℝ} (hρ : ρ ≠ 1)
    (h32 : 0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11)
    (h34 : 0 = m2 + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11
      + 1 / 2 * v22 - ρ * ((1 - γ) / (1 - ρ)) * v20 + ((1 - γ) / (1 - ρ) - 1) * v21) :
    m2 - rf + 1 / 2 * v22 = ρ * (1 - γ) / (1 - ρ) * v20 + (γ - ρ) / (1 - ρ) * v21 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have e1 : (1 - γ) / (1 - ρ) - 1 = -((γ - ρ) / (1 - ρ)) := by field_simp; ring
  have e2 : ρ * ((1 - γ) / (1 - ρ)) = ρ * (1 - γ) / (1 - ρ) := by ring
  rw [e1, e2] at h32 h34
  linarith

/-- Miao, p. 718: equations (20.33) and (20.35) imply `E_t r_{e,t+1} = μ_e + ρ E_t Δc_{t+1}`
with the asset-specific constant
`μ_e = −ln β − ½(γ−ρ)/(1−ρ) σ_w² − ρ²(1−γ)/(2(1−ρ)) σ_c² − ½σ_e² + ρ(1−γ)/(1−ρ) σ_ec
+ (γ−ρ)/(1−ρ) σ_ew`. -/
theorem pa_expected_equity_return {β ρ γ rf m0 me ve vc vw vec vew : ℝ}
    (h33 : rf = -Real.log β + ρ * m0 - 1 / 2 * ((γ - ρ) / (1 - ρ)) * vw
      - ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) * vc)
    (h35 : me - rf + 1 / 2 * ve = ρ * (1 - γ) / (1 - ρ) * vec + (γ - ρ) / (1 - ρ) * vew) :
    me = (-Real.log β - 1 / 2 * ((γ - ρ) / (1 - ρ)) * vw - ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) * vc
      - 1 / 2 * ve + ρ * (1 - γ) / (1 - ρ) * vec + (γ - ρ) / (1 - ρ) * vew) + ρ * m0 := by
  linarith

/-- Miao, p. 716: the weights in (20.35). When `0 < ρ < 1` (EIS above one) and `γ > 1` (so
`γ > ρ`), the weight `ρ(1 − γ)/(1 − ρ)` on `σ_ic` is negative and the weight
`(γ − ρ)/(1 − ρ)` on `σ_iw` is positive. -/
theorem pa_eq_20_35_weights {ρ γ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 < γ) :
    ρ * (1 - γ) / (1 - ρ) < 0 ∧ 0 < (γ - ρ) / (1 - ρ) :=
  ⟨div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hρ0 (by linarith)) (by linarith),
    div_pos (by linarith) (by linarith)⟩

end Miao.RecursiveUtility
