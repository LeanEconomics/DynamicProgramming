/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.VARMoments

/-!
# The AR(1) process

AKMM, §7.1.1 (covariance stationarity, p. 188) and §7.1.3, (7.1), pp. 191–192.

`x_{t+1} = ρx_t + bε_{t+1} + (1 − ρ)µ` with `Eₜ[ε_{t+1}] = 0`, `Eₜ[ε²_{t+1}] = 1` (the shock
conditions are Miao's `var_ShockMDS`, which also give `Eₜ[ε_{t+1}ε_{t+1+s}] = 0`). The moments
are obtained from Miao's `RationalExpectations` (the first-order system (2.1) on a one-dimensional
state, `var_stationary_moments`, `lyap_fixed`).

* Covariance stationarity (p. 188) for scalar processes (`ar1_IsCovStationary`).
* The moving-average form `x_t = µ + ρᵗ(x₀ − µ) + b Σ_{s<t} ρˢε_{t−s}` (`ar1_ma`), whose
  initial term vanishes for `|ρ| < 1` (`ar1_ma_initial_tendsto`).
* For `|ρ| < 1` and a covariance-stationary solution: `E[x_t] = µ`, `Var[x_t] = b²/(1 − ρ²)` and
  `Cov(x_t, x_{t+j}) = b²ρʲ/(1 − ρ²)` (`ar1_moments`), so the correlation is `ρʲ`
  (`ar1_correlation`).

Departure: the process is indexed by `t ≥ 0` with a given `x₀`, so the book's infinite moving
average `µ + b Σ_{s ≥ 0} ρˢε_{t−s}` appears as the finite sum plus the term `ρᵗ(x₀ − µ)`; the
moments are proved for every covariance-stationary solution (which is what "stationary" means in
the text).
-/

namespace AKMM.Uncertainty

open MeasureTheory Filter Topology Matrix Miao.RationalExpectations

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- AKMM, p. 188: a scalar process is covariance stationary if it is square integrable and
neither its mean nor its autocovariances `E[(X_{t+j} − m)(X_t − m)]` depend on `t`. -/
def ar1_IsCovStationary (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  (∀ t, MemLp (X t) 2 μ) ∧ ∃ m : ℝ, ∃ γ : ℕ → ℝ, (∀ t, ∫ ω, X t ω ∂μ = m) ∧
    ∀ t j, ∫ ω, (X (t + j) ω - m) * (X t ω - m) ∂μ = γ j

/-- AKMM, p. 191: repeated substitution in (7.1) gives
`x_t = µ + ρᵗ(x₀ − µ) + b Σ_{s<t} ρˢε_{t−s}`. -/
theorem ar1_ma {ρ b mu : ℝ} {x e : ℕ → ℝ}
    (h71 : ∀ t, x (t + 1) = ρ * x t + b * e (t + 1) + (1 - ρ) * mu) (t : ℕ) :
    x t = mu + ρ ^ t * (x 0 - mu) + b * ∑ s ∈ Finset.range t, ρ ^ s * e (t - s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [h71, ih, Finset.sum_range_succ', pow_zero, one_mul, Nat.sub_zero]
    have h : ∑ s ∈ Finset.range t, ρ ^ (s + 1) * e (t + 1 - (s + 1)) =
        ρ * ∑ s ∈ Finset.range t, ρ ^ s * e (t - s) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [Nat.add_sub_add_right, pow_succ]; ring
    rw [h]
    ring

/-- AKMM, p. 191: "if `|ρ| < 1`, the effect on `x_t` of shocks in the distant past vanishes":
`ρᵗ(x₀ − µ) → 0`. -/
theorem ar1_ma_initial_tendsto {ρ : ℝ} (hρ : |ρ| < 1) (c : ℝ) :
    Tendsto (fun t : ℕ => ρ ^ t * c) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ).mul_const c

/-- The one-dimensional coefficient matrix `[ρ]`. -/
def ar1Mat (ρ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => ρ

theorem ar1Mat_stable {ρ : ℝ} (hρ : |ρ| < 1) :
    IsStableMatrix ((ar1Mat ρ).map Complex.ofRealHom) := by
  refine isStableMatrix_of_tendsto _ fun v => ?_
  simp only [ar1Mat, diagonal_pow]
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec_diagonal, Pi.pow_apply, Pi.zero_apply]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ).mul_const (v i)

/-- **AKMM, pp. 191–192: the moments of the AR(1).** Let `|ρ| < 1`, let `ε` satisfy the shock
conditions and `x` solve (7.1) from a square-integrable, `ℱ₀`-measurable `x₀`. If `x` is
covariance stationary then `E[x_t] = µ` and `E[(x_{t+j} − µ)(x_t − µ)] = b²ρʲ/(1 − ρ²)`; in
particular `Var[x_t] = b²/(1 − ρ²)`. -/
theorem ar1_moments {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {ρ b mu : ℝ} (hρ : |ρ| < 1) {x ε : ℕ → Ω → ℝ}
    (hε : var_ShockMDS μ ℱ fun t ω (_ : Fin 1) => ε t ω)
    (h71 : ∀ t ω, x (t + 1) ω = ρ * x t ω + b * ε (t + 1) ω + (1 - ρ) * mu)
    (hx0m : Measurable[ℱ 0] (x 0)) (hs : ar1_IsCovStationary μ x) :
    (∀ t, ∫ ω, x t ω ∂μ = mu) ∧
      (∀ t j, ∫ ω, (x (t + j) ω - mu) * (x t ω - mu) ∂μ = b ^ 2 * ρ ^ j / (1 - ρ ^ 2)) ∧
      ∀ t, ∫ ω, (x t ω - mu) ^ 2 ∂μ = b ^ 2 / (1 - ρ ^ 2) := by
  obtain ⟨hmem, mx, γ, hmx, hγ⟩ := hs
  set z : ℕ → Ω → Fin 1 → ℝ := fun t ω _ => x t ω - mu with hz
  have hint : ∀ t, Integrable (x t) μ := fun t => (hmem t).integrable one_le_two
  have hmodel : var_Model (Fin 1) μ ℱ (ar1Mat ρ) (Matrix.diagonal fun _ => b) z
      (fun t ω _ => ε t ω) := by
    refine ⟨fun t ω => ?_, fun _ => (hmem 0).sub (memLp_const mu), fun _ => ?_, hε⟩
    · funext i
      simp only [hz, ar1Mat, mulVec_diagonal, Pi.add_apply, h71]
      ring
    · exact hx0m.sub measurable_const
  have hmean_z : ∀ t, var_mean μ (z t) = fun _ => mx - mu := fun t => by
    funext i
    simp only [var_mean, hz]
    rw [integral_sub (hint t) (integrable_const mu), hmx, integral_const]
    simp
  have hcs : var_IsCovStationary μ z := by
    refine ⟨fun t _ => (hmem t).sub (memLp_const mu), fun _ => mx - mu,
      fun j => Matrix.of fun _ _ => γ j, hmean_z, fun t j => ?_⟩
    ext a c
    simp only [var_mom, Matrix.of_apply, hz, Pi.sub_apply]
    rw [← hγ t j]
    congr 1
    funext ω
    ring
  have hstab := ar1Mat_stable hρ
  obtain ⟨Γ, hm0, hΓ, h0, hj⟩ := var_stationary_moments hmodel hstab hcs
  -- the stationary variance
  set L := var_lyapSol (ar1Mat ρ) ((Matrix.diagonal fun _ => b) * (Matrix.diagonal fun _ => b)ᵀ)
  have hmap : ∀ M : Matrix (Fin 1) (Fin 1) ℝ, var_lyapMap (ar1Mat ρ)
      ((Matrix.diagonal fun _ => b) * (Matrix.diagonal fun _ => b)ᵀ) M 0 0 =
        ρ * M 0 0 * ρ + b * b := fun M => by
    simp [var_lyapMap, ar1Mat, Matrix.mul_apply]
  have hfix := hmap L
  rw [lyap_fixed (ar1Mat ρ) hstab] at hfix
  have hρ2 : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg ρ) hρ two_ne_zero
    linarith
  have hL : L 0 0 = b ^ 2 / (1 - ρ ^ 2) := by
    rw [eq_div_iff hρ2.ne']
    nlinarith
  have hcov : ∀ t j, ∫ ω, (x (t + j) ω - mu) * (x t ω - mu) ∂μ = b ^ 2 * ρ ^ j / (1 - ρ ^ 2) := by
    intro t j
    have h1 := congrFun (congrFun (hΓ t j) 0) 0
    rw [hj j] at h1
    simp only [var_mom, Matrix.of_apply, hz, ar1Mat, diagonal_pow, diagonal_mul, Pi.pow_apply] at h1
    rw [h1, hL]
    ring
  refine ⟨fun t => ?_, hcov, fun t => ?_⟩
  · have h := congrFun (hm0 t) 0
    simp only [var_mean, hz, Pi.zero_apply] at h
    rw [integral_sub (hint t) (integrable_const mu), integral_const] at h
    simp at h
    linarith
  · have := hcov t 0
    simp only [Nat.add_zero, pow_zero, mul_one] at this
    rw [← this]
    congr 1
    funext ω
    ring

/-- AKMM, p. 192: the correlation between `x_t` and `x_{t+j}` is `ρʲ` (for `b ≠ 0`). -/
theorem ar1_correlation {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {ρ b mu : ℝ} (hρ : |ρ| < 1) (hb : b ≠ 0) {x ε : ℕ → Ω → ℝ}
    (hε : var_ShockMDS μ ℱ fun t ω (_ : Fin 1) => ε t ω)
    (h71 : ∀ t ω, x (t + 1) ω = ρ * x t ω + b * ε (t + 1) ω + (1 - ρ) * mu)
    (hx0m : Measurable[ℱ 0] (x 0)) (hs : ar1_IsCovStationary μ x) (t j : ℕ) :
    (∫ ω, (x (t + j) ω - mu) * (x t ω - mu) ∂μ) /
        √((∫ ω, (x (t + j) ω - mu) ^ 2 ∂μ) * ∫ ω, (x t ω - mu) ^ 2 ∂μ) = ρ ^ j := by
  obtain ⟨-, hcov, hvar⟩ := ar1_moments hρ hε h71 hx0m hs
  have hρ2 : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg ρ) hρ two_ne_zero
    linarith
  have hv : 0 < b ^ 2 / (1 - ρ ^ 2) := div_pos (by positivity) hρ2
  rw [hcov, hvar, hvar, Real.sqrt_mul_self hv.le]
  field_simp

end AKMM.Uncertainty
