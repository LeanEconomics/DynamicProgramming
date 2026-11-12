/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Other extensions: habits, adjustment costs and capital

AKMM, §18.6.2, pp. 558–560.

* `ext_habit`: `C_t − γC_{t−1} = (1 − γ)C_t + γ(C_t − C_{t−1})` (habits (18.26)).
* **Adjustment costs** (footnote 24): with `K′ = (1 − δ)K + ξ(I/K)K`, the first-order condition
  for investment gives Tobin's `Q = 1/ξ′(I/K)` (`ext_adj_foc`, `ext_tobin_q`); the deterministic
  steady state `K′ = K` has `ξ(I/K) = δ`, so `ξ(δ) = δ` makes `I/K = δ` a steady state
  (`ext_adj_steady`), and there `Q = 1` iff `ξ′(δ) = 1` (`ext_q_one_iff`).
  **Correction**: the footnote says `ξ(δ) = δ` makes `Q = 1`; it also needs `ξ′(δ) = 1`:
  `ξ(x) = √(δx)` is increasing and concave with `ξ(δ) = δ` but `Q = 2` (`ext_q_counterexample`).
* **Capital** (18.27): the output elasticity of labour is `1 − α` (`ext_labour_elasticity`), so a
  1% increase in output needs `1/(1 − α)`% more labour (`ext_labour_requirement_pct`).
  **Correction**: in units the requirement is `1/MPL = ℓ/((1 − α) y)`, which is `1/(1 − α)` only
  when `y = ℓ` (`ext_labour_requirement_units`, `ext_units_printed_false`).
-/

namespace AKMM.NominalFrictions

/-- AKMM, (18.26), p. 558: the habit term is a weighted average of the level and the change of
consumption, `C_t − γC_{t−1} = (1 − γ)C_t + γ(C_t − C_{t−1})`. -/
theorem ext_habit (γ C Cm : ℝ) : C - γ * Cm = (1 - γ) * C + γ * (C - Cm) := by ring

/-- AKMM, p. 559 and footnote 24: with the shadow value `q` of installed capital, the
derivative of `−I + q((1 − δ)K + ξ(I/K)K)` in `I` is `−1 + q ξ′(I/K)` (`K > 0`). -/
theorem ext_adj_foc {ξ : ℝ → ℝ} {ξ' q δ K I : ℝ} (hK : 0 < K) (hξ : HasDerivAt ξ ξ' (I / K)) :
    HasDerivAt (fun J => -J + q * ((1 - δ) * K + ξ (J / K) * K)) (-1 + q * ξ') I := by
  have h1 : HasDerivAt (fun J => J / K) (1 / K) I := by
    simpa using (hasDerivAt_id I).div_const K
  have h2 := ((hξ.comp I h1).mul_const K).const_add ((1 - δ) * K)
  have h3 := ((h2.const_mul q).const_add 0).add (hasDerivAt_neg I)
  convert h3 using 1
  · funext J; simp only [Function.comp_apply, zero_add, Pi.add_apply]; ring
  · field_simp; ring

/-- **AKMM, footnote 24, p. 559**: optimal investment sets the derivative to zero, so Tobin's
`Q = q = 1/ξ′(I/K)` (`ξ′ ≠ 0`). -/
theorem ext_tobin_q {ξ' q : ℝ} (h : -1 + q * ξ' = 0) : q = 1 / ξ' := by
  have hξ : ξ' ≠ 0 := by rintro rfl; simp at h
  field_simp; linarith

/-- AKMM, p. 559: the deterministic steady state `K′ = K` (`K > 0`) holds iff `ξ(I/K) = δ`. -/
theorem ext_adj_steady {ξ : ℝ → ℝ} {δ K I : ℝ} (hK : 0 < K) :
    (1 - δ) * K + ξ (I / K) * K = K ↔ ξ (I / K) = δ := by
  constructor
  · intro h
    have := mul_right_cancel₀ hK.ne' (by linarith : ξ (I / K) * K = δ * K)
    exact this
  · intro h; rw [h]; ring

/-- **AKMM, footnote 24, p. 559**: at the steady state `I/K = δ`, `Q = 1/ξ′(δ) = 1` iff
`ξ′(δ) = 1`. -/
theorem ext_q_one_iff {ξ'δ : ℝ} : 1 / ξ'δ = 1 ↔ ξ'δ = 1 := by
  constructor
  · intro h
    have hξ : ξ'δ ≠ 0 := by rintro rfl; simp at h
    field_simp at h; linarith
  · intro h; rw [h]; norm_num

/-- **AKMM, footnote 24, p. 559 (correction)**: `ξ(x) = √(δ x)` (`δ > 0`) satisfies `ξ(δ) = δ`
and is increasing and concave, but `ξ′(δ) = 1/2`, so Tobin's `Q = 2 ≠ 1` at the steady state. -/
theorem ext_q_counterexample {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt (δ * δ) = δ ∧ HasDerivAt (fun x => Real.sqrt (δ * x)) (1 / 2) δ ∧
      StrictMonoOn (fun x => Real.sqrt (δ * x)) (Set.Ici 0) ∧
      ConcaveOn ℝ (Set.Ici 0) (fun x => Real.sqrt (δ * x)) ∧ 1 / (1 / 2 : ℝ) = 2 := by
  refine ⟨Real.sqrt_mul_self hδ.le, ?_, ?_, ?_, by norm_num⟩
  · have h1 : HasDerivAt (fun x => δ * x) δ δ := by simpa using (hasDerivAt_id δ).const_mul δ
    have h2 := h1.sqrt (by positivity)
    convert h2 using 1
    rw [Real.sqrt_mul_self hδ.le]
    field_simp
  · intro x hx y hy hxy
    simp only
    exact Real.sqrt_lt_sqrt (mul_nonneg hδ.le hx) (mul_lt_mul_of_pos_left hxy hδ)
  · have hc := Real.strictConcaveOn_sqrt.concaveOn
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have := hc.2 (Set.mem_Ici.2 (mul_nonneg hδ.le hx)) (Set.mem_Ici.2 (mul_nonneg hδ.le hy))
      ha hb hab
    simp only [smul_eq_mul] at this ⊢
    convert this using 2
    ring

/-- **AKMM, (18.27), p. 560**: with `y = A k^α ℓ^{1−α}` and `k` fixed, the elasticity of output
with respect to labour is `1 − α`: `s ↦ log y(e^s)` has derivative `1 − α`. -/
theorem ext_labour_elasticity {A k α s : ℝ} (hA : 0 < A) (hk : 0 < k) :
    HasDerivAt (fun r => Real.log (A * k ^ α * Real.exp r ^ (1 - α))) (1 - α) s := by
  have e : ∀ r, Real.log (A * k ^ α * Real.exp r ^ (1 - α)) =
      Real.log (A * k ^ α) + (1 - α) * r := by
    intro r
    rw [Real.log_mul (by positivity) (by positivity), ← Real.exp_mul, Real.log_exp]
    ring
  simp_rw [e]
  simpa using ((hasDerivAt_id s).const_mul (1 - α)).const_add (Real.log (A * k ^ α))

/-- AKMM, p. 560: in percentages, raising output by `d log y` needs `d log ℓ = d log y/(1 − α)`
more labour, more than `d log y` when `0 < α < 1`. -/
theorem ext_labour_requirement_pct {α dy : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hdy : 0 < dy) :
    (1 - α) * (dy / (1 - α)) = dy ∧ dy < dy / (1 - α) := by
  have h : 0 < 1 - α := by linarith
  refine ⟨by field_simp, ?_⟩
  rw [lt_div_iff₀ h]; nlinarith

/-- **AKMM, p. 560 (correction)**: in units, one more unit of output needs `1/MPL` more labour;
with `y = A k^α ℓ^{1−α}`, `MPL = (1 − α) y/ℓ`, so the requirement is `ℓ/((1 − α) y)`. -/
theorem ext_labour_requirement_units {A k α ℓ : ℝ} (hℓ : 0 < ℓ) (hα : α ≠ 1) (hA : 0 < A)
    (hk : 0 < k) :
    HasDerivAt (fun l => A * k ^ α * l ^ (1 - α))
        ((1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ) ℓ ∧
      1 / ((1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ) =
        ℓ / ((1 - α) * (A * k ^ α * ℓ ^ (1 - α))) := by
  have h1α : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  refine ⟨?_, by rw [one_div_div]⟩
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hℓ.ne')).const_mul (A * k ^ α)
  convert h using 1
  rw [Real.rpow_sub_one hℓ.ne']
  have : 0 < k ^ α := Real.rpow_pos_of_pos hk _
  field_simp

/-- **AKMM, p. 560 (correction)**: the units requirement `ℓ/((1 − α)y)` equals the printed
`1/(1 − α)` iff `y = ℓ` (`α < 1`, `y, ℓ > 0`). -/
theorem ext_units_printed_false {α y ℓ : ℝ} (hα : α < 1) (hy : 0 < y) :
    ℓ / ((1 - α) * y) = 1 / (1 - α) ↔ y = ℓ := by
  have h : 0 < 1 - α := by linarith
  rw [div_eq_div_iff (by positivity) h.ne']
  constructor
  · intro h1
    have := mul_right_cancel₀ h.ne' (by linarith : ℓ * (1 - α) = y * (1 - α))
    exact this.symm
  · intro h1; rw [h1]; ring

end AKMM.NominalFrictions
