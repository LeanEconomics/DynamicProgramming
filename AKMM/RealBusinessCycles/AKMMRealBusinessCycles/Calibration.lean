/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Calibration of the core RBC model

AKMM, §14.4.3–14.4.4, pp. 425–428.

* The Solow residual `log zₜ = log yₜ − α log kₜ − (1 − α) log ℓₜ` for `y = zk^αℓ^{1−α}`
  (`cal_solow_residual`).
* Perpetual inventory: `kₜ = (1 − δ)kₜ₋₁ + iₜ` gives `kₜ = (1 − δ)ᵗk₀ + Σ(1 − δ)^{t−1−s}i_{s+1}`
  (`cal_perpetual_inventory`); the effect of the initial guess decays as `(1 − δ)ᵗ`
  (`cal_perpetual_guess`).
* The quarterly `β = 0.99` is an annual discount rate of about 4%: `(1/0.99)⁴ − 1 ∈ (0.040, 0.042)`
  (`cal_discount_rate`).
* **The calibration identity** (p. 428): with `u = (1 − φ)ln c + φ ln(1 − ℓ)` and
  `y = zk^αℓ^{1−α}`, (14.8) `zF₂ = U₂/U₁` is equivalent to
  `φ/(1 − φ)·ℓ/(1 − ℓ) = (1 − α)y/c` (`cal_phi_identity`, with the marginal product of labour
  `zF₂ = (1 − α)y/ℓ`, `cal_mpl`).
* The steady state: the Euler equation gives `k/y = αβ/(1 − β(1 − δ))` and `c/y = 1 − δk/y`
  (`cal_steady_ratios`); at `ℓ = 1/3`, `φ = X/(1 + X)` with `X = 2(1 − α)y/c`
  (`cal_phi_formula`).
* **Numeric certificate** (p. 428, "`φ = 0.6325`"): at `α = 0.36`, `β = 0.99`, `δ = 0.025`,
  `0.63245 < φ < 0.63255` (`cal_phi_value`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology

/-- AKMM, p. 426: the Solow residual. If `y = zk^αℓ^{1−α}` with `z, k, ℓ > 0`, then
`log z = log y − α log k − (1 − α) log ℓ`. -/
theorem cal_solow_residual {α z k ℓ y : ℝ} (hz : 0 < z) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hy : y = z * k ^ α * ℓ ^ (1 - α)) :
    Real.log z = Real.log y - α * Real.log k - (1 - α) * Real.log ℓ := by
  rw [hy, Real.log_mul (by positivity) (by positivity), Real.log_mul hz.ne' (by positivity),
    Real.log_rpow hk, Real.log_rpow hℓ]
  ring

/-- AKMM, p. 426: the perpetual-inventory method. If `kₜ₊₁ = (1 − δ)kₜ + iₜ₊₁`, then
`kₜ = (1 − δ)ᵗk₀ + Σ_{s<t}(1 − δ)^{t−1−s}i_{s+1}`. -/
theorem cal_perpetual_inventory {δ : ℝ} {k i : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + i (t + 1)) (t : ℕ) :
    k t = (1 - δ) ^ t * k 0 + ∑ s ∈ Finset.range t, (1 - δ) ^ (t - 1 - s) * i (s + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hk, ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum]
    have : ∀ s ∈ Finset.range t, (1 - δ) * ((1 - δ) ^ (t - 1 - s) * i (s + 1)) =
        (1 - δ) ^ (t - s) * i (s + 1) := fun s hs => by
      have := Finset.mem_range.1 hs
      rw [show t - s = (t - 1 - s) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- AKMM, p. 426: with `0 < δ ≤ 1`, two capital series built by perpetual inventory from the same
investment data but different initial guesses differ by `(1 − δ)ᵗ(k₀ − k₀′) → 0`. -/
theorem cal_perpetual_guess {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {k k' i : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + i (t + 1))
    (hk' : ∀ t, k' (t + 1) = (1 - δ) * k' t + i (t + 1)) :
    (∀ t, k t - k' t = (1 - δ) ^ t * (k 0 - k' 0)) ∧
      Tendsto (fun t => k t - k' t) atTop (𝓝 0) := by
  have e : ∀ t, k t - k' t = (1 - δ) ^ t * (k 0 - k' 0) := fun t => by
    rw [cal_perpetual_inventory hk t, cal_perpetual_inventory hk' t]
    ring
  refine ⟨e, ?_⟩
  rw [show (fun t => k t - k' t) = fun t => (1 - δ) ^ t * (k 0 - k' 0) from funext e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const
    (k 0 - k' 0)

/-- AKMM, p. 428: "`β = 0.99`, representing an annual 4% discount rate":
`0.040 < (1/0.99)⁴ − 1 < 0.042`. -/
theorem cal_discount_rate : (0.040 : ℝ) < (1 / 0.99) ^ 4 - 1 ∧ (1 / 0.99 : ℝ) ^ 4 - 1 < 0.042 := by
  constructor <;> norm_num

/-- The marginal product of labour of `y = zk^αℓ^{1−α}`: `zF₂ = (1 − α)y/ℓ`. -/
theorem cal_mpl {α z k ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasDerivAt (fun x => z * k ^ α * x ^ (1 - α)) ((1 - α) * (z * k ^ α * ℓ ^ (1 - α)) / ℓ) ℓ := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hℓ.ne')).const_mul (z * k ^ α)
  convert this using 1
  rw [Real.rpow_sub_one hℓ.ne']
  ring

/-- **AKMM, p. 428: the calibration identity.** With `U₁ = (1 − φ)/c`, `U₂ = φ/(1 − ℓ)` and
`zF₂ = (1 − α)y/ℓ`, (14.8) holds iff `φ/(1 − φ)·ℓ/(1 − ℓ) = (1 − α)y/c`. -/
theorem cal_phi_identity {α φ c ℓ y : ℝ} (hφ1 : φ < 1) (hc : 0 < c) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (1 - α) * y / ℓ = (φ / (1 - ℓ)) / ((1 - φ) / c) ↔
      φ / (1 - φ) * (ℓ / (1 - ℓ)) = (1 - α) * (y / c) := by
  have h1 : 0 < 1 - φ := by linarith
  have h2 : 0 < 1 - ℓ := by linarith
  have e1 : (φ / (1 - ℓ)) / ((1 - φ) / c) = φ * c / ((1 - ℓ) * (1 - φ)) := by
    field_simp
  have e2 : φ / (1 - φ) * (ℓ / (1 - ℓ)) = φ * ℓ / ((1 - φ) * (1 - ℓ)) := by
    field_simp
  have e3 : (1 - α) * (y / c) = (1 - α) * y / c := by ring
  rw [e1, e2, e3, div_eq_div_iff hℓ0.ne' (by positivity),
    div_eq_div_iff (by positivity) hc.ne']
  constructor <;> intro h <;> linarith

/-- AKMM, p. 428: the steady state of the calibrated model. With `c` constant the Euler equation
`1 = β(αy/k + 1 − δ)` holds iff `k/y = αβ/(1 − β(1 − δ))`; the resource constraint
`c + δk = y` gives `c/y = 1 − δk/y`. -/
theorem cal_steady_ratios {α β δ k y c : ℝ} (hk : 0 < k) (hy : 0 < y)
    (hb : β * (1 - δ) ≠ 1) :
    (1 = β * (α * y / k + 1 - δ) ↔ k / y = α * β / (1 - β * (1 - δ))) ∧
      (c + δ * k = y → c / y = 1 - δ * (k / y)) := by
  have hb' : 1 - β * (1 - δ) ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · rw [div_eq_div_iff hy.ne' hb']
    field_simp at h
    linarith
  · rw [div_eq_div_iff hy.ne' hb'] at h
    field_simp
    linarith
  · have hne : c + δ * k ≠ 0 := by rw [h]; exact hy.ne'
    rw [← h]
    field_simp
    ring

/-- AKMM, p. 428: at the target `ℓ = 1/3`, the identity gives `φ/(1 − φ) = X` with
`X = 2(1 − α)y/c`, i.e. `φ = X/(1 + X)`. -/
theorem cal_phi_formula {α φ y c : ℝ} (hφ1 : φ < 1) (hα : α < 1) (hyc : 0 < y / c) :
    φ / (1 - φ) * ((1 / 3) / (1 - 1 / 3)) = (1 - α) * (y / c) ↔
      φ = 2 * (1 - α) * (y / c) / (1 + 2 * (1 - α) * (y / c)) := by
  have h1 : 0 < 1 - φ := by linarith
  have hX : 0 < 1 + 2 * (1 - α) * (y / c) := by
    have : 0 < (1 - α) * (y / c) := mul_pos (by linarith) hyc
    linarith
  set q := y / c
  have e : φ / (1 - φ) * ((1 / 3) / (1 - 1 / 3)) = φ / (2 * (1 - φ)) := by
    field_simp; ring
  rw [eq_div_iff hX.ne', e, div_eq_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- The calibrated capital–output ratio `k/y = αβ/(1 − β(1 − δ))` at `α = 0.36`, `β = 0.99`,
`δ = 0.025`. -/
noncomputable def calKY : ℝ := 0.36 * 0.99 / (1 - 0.99 * (1 - 0.025))

/-- The calibrated `φ = X/(1 + X)`, `X = 2(1 − α)y/c`, `c/y = 1 − δk/y`. -/
noncomputable def calPhi : ℝ :=
  2 * (1 - 0.36) * (1 / (1 - 0.025 * calKY)) / (1 + 2 * (1 - 0.36) * (1 / (1 - 0.025 * calKY)))

/-- **AKMM, p. 428: "we can then solve for `φ = 0.6325`"** (numeric certificate):
`0.63245 < φ < 0.63255` at `α = 0.36`, `β = 0.99`, `δ = 0.025`, `ℓ = 1/3`. -/
theorem cal_phi_value : (0.63245 : ℝ) < calPhi ∧ calPhi < 0.63255 := by
  unfold calPhi calKY
  constructor <;> norm_num

end AKMM.RealBusinessCycles
