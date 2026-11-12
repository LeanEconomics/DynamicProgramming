/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Impulse responses from linear policy functions

AKMM, §14.4.2, p. 424. Linearised around the steady state (all variables in deviations), the
policies are `y = G(k, z) = G_k k + G_z z` and `k′ = H(k, z) = H_k k + H_z z`, and
`zₜ = ρzₜ₋₁`. The impulse response to a TFP shock `ε` at the steady state is
`k₀ = 0`, `z_s = ρˢε`, `k_{s+1} = H(k_s, z_s)` (`irfK`), `y_s = G(k_s, z_s)` (`irfY`).

* The sequence `y₀ = G(k_ss, z₀)`, `y₁ = G(H(k_ss, z₀), z₁)`, `y₂ = G(H(H(k_ss, z₀), z₁), z₂)`
  (`irf_first_terms`; the book labels the third term `y₁` again).
* "The composition of linear functions is linear": the response is linear in the shock, so
  `y_s/ε` does not depend on `ε` (`irf_linear`); closed form
  `k_s = H_zεΣ_{j<s}H_kˢ⁻¹⁻ʲρʲ` (`irf_closed`).
* Geometric decay: with `m ≥ |H_k|, |ρ|`, `|k_{s+1}| ≤ |H_z||ε|(s + 1)mˢ` (`irf_bound`), so for
  `|H_k| < 1` and `|ρ| < 1` the responses of capital, TFP and output vanish (`irf_decay`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology

/-- The capital response `k₀ = 0`, `k_{s+1} = H_k k_s + H_z ρˢε`. -/
def irfK (Hk Hz ρ ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => Hk * irfK Hk Hz ρ ε s + Hz * (ρ ^ s * ε)

/-- The output response `y_s = G_k k_s + G_z ρˢε`. -/
def irfY (Gk Gz Hk Hz ρ ε : ℝ) (s : ℕ) : ℝ := Gk * irfK Hk Hz ρ ε s + Gz * (ρ ^ s * ε)

/-- **AKMM, p. 424: the impulse-response sequence.** With `G(k, z) = G_k k + G_z z`,
`H(k, z) = H_k k + H_z z`, `k_ss = 0` (deviations) and `z_s = ρˢz₀`, `z₀ = ε`:
`y₀ = G(0, z₀)`, `y₁ = G(H(0, z₀), z₁)` and `y₂ = G(H(H(0, z₀), z₁), z₂)`. -/
theorem irf_first_terms (Gk Gz Hk Hz ρ ε : ℝ) :
    let G := fun k z => Gk * k + Gz * z
    let H := fun k z => Hk * k + Hz * z
    irfY Gk Gz Hk Hz ρ ε 0 = G 0 ε ∧ irfY Gk Gz Hk Hz ρ ε 1 = G (H 0 ε) (ρ * ε) ∧
      irfY Gk Gz Hk Hz ρ ε 2 = G (H (H 0 ε) (ρ * ε)) (ρ ^ 2 * ε) := by
  simp only [irfY, irfK]
  refine ⟨by ring, by ring, by ring⟩

/-- The response is linear in the shock: `k_s(ε) = εk_s(1)`. -/
theorem irf_K_linear (Hk Hz ρ ε : ℝ) (s : ℕ) : irfK Hk Hz ρ ε s = ε * irfK Hk Hz ρ 1 s := by
  induction s with
  | zero => simp [irfK]
  | succ s ih => simp only [irfK]; rw [ih]; ring

/-- AKMM, p. 424: "since the composition of linear functions is linear", the impulse response
per unit of shock `y_s/ε` is independent of the size of the shock: `y_s(ε) = εy_s(1)`. -/
theorem irf_linear (Gk Gz Hk Hz ρ ε : ℝ) (s : ℕ) :
    irfY Gk Gz Hk Hz ρ ε s = ε * irfY Gk Gz Hk Hz ρ 1 s := by
  simp only [irfY]
  rw [irf_K_linear Hk Hz ρ ε s]
  ring

/-- Closed form: `k_s = H_zεΣ_{j<s}H_k^{s−1−j}ρʲ`. -/
theorem irf_closed (Hk Hz ρ ε : ℝ) (s : ℕ) :
    irfK Hk Hz ρ ε s = Hz * ε * ∑ j ∈ Finset.range s, Hk ^ (s - 1 - j) * ρ ^ j := by
  induction s with
  | zero => simp [irfK]
  | succ s ih =>
    simp only [irfK]
    rw [ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have : ∀ j ∈ Finset.range s, Hk * (Hz * ε * (Hk ^ (s - 1 - j) * ρ ^ j)) =
        Hz * ε * (Hk ^ (s - j) * ρ ^ j) := fun j hj => by
      have hj' : j < s := Finset.mem_range.1 hj
      rw [show s - j = (s - 1 - j) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- The geometric bound `|k_{s+1}| ≤ |H_z||ε|(s + 1)mˢ` for `|H_k| ≤ m` and `|ρ| ≤ m`. -/
theorem irf_bound {Hk Hz ρ ε m : ℝ} (hk : |Hk| ≤ m) (hr : |ρ| ≤ m) (s : ℕ) :
    |irfK Hk Hz ρ ε (s + 1)| ≤ |Hz| * |ε| * ((s + 1) * m ^ s) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hk
  have hz : ∀ j : ℕ, |ρ ^ j * ε| ≤ m ^ j * |ε| := fun j => by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hr j) (abs_nonneg _)
  induction s with
  | zero => simp [irfK, abs_mul]
  | succ s ih =>
    simp only [irfK] at ih ⊢
    calc |Hk * irfK Hk Hz ρ ε (s + 1) + Hz * (ρ ^ (s + 1) * ε)|
        ≤ |Hk| * |irfK Hk Hz ρ ε (s + 1)| + |Hz| * |ρ ^ (s + 1) * ε| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ m * (|Hz| * |ε| * ((s + 1) * m ^ s)) + |Hz| * (m ^ (s + 1) * |ε|) := by
          gcongr
          · simpa [irfK] using ih
          · exact hz (s + 1)
      _ = |Hz| * |ε| * ((↑(s + 1) + 1) * m ^ (s + 1)) := by push_cast; ring

/-- **AKMM, p. 424: the impulse responses die out geometrically.** If `|H_k| < 1` and `|ρ| < 1`,
the responses of capital, TFP and output tend to zero. -/
theorem irf_decay {Gk Gz Hk Hz ρ ε : ℝ} (hk : |Hk| < 1) (hr : |ρ| < 1) :
    Tendsto (irfK Hk Hz ρ ε) atTop (𝓝 0) ∧ Tendsto (fun s : ℕ => ρ ^ s * ε) atTop (𝓝 0) ∧
      Tendsto (irfY Gk Gz Hk Hz ρ ε) atTop (𝓝 0) := by
  set m := max |Hk| |ρ|
  have hm0 : 0 ≤ m := le_max_of_le_left (abs_nonneg _)
  have hm1 : m < 1 := max_lt hk hr
  have hz : Tendsto (fun s : ℕ => ρ ^ s * ε) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).mul_const ε
  have hb : Tendsto (fun s : ℕ => |Hz| * |ε| * ((s + 1 : ℝ) * m ^ s)) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hm0 hm1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hm0 hm1
    have := (h1.add h2).const_mul (|Hz| * |ε|)
    simp only [add_zero, mul_zero] at this
    refine this.congr fun s => ?_
    ring
  have hK1 : Tendsto (fun s => irfK Hk Hz ρ ε (s + 1)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun s => irf_bound (le_max_left _ _) (le_max_right _ _) s) hb
  have hK : Tendsto (irfK Hk Hz ρ ε) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).1 hK1
  refine ⟨hK, hz, ?_⟩
  have := (hK.const_mul Gk).add (hz.const_mul Gz)
  simp only [mul_zero, add_zero] at this
  exact this

end AKMM.RealBusinessCycles
