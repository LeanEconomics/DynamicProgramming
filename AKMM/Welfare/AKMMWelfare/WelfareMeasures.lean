/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IntermediateValue

/-!
# Quantifying welfare losses, and the veil of ignorance

AKMM, §6.3.6, pp. 175–176, and §6.5.2, pp. 185–186.

* The consumption-equivalent `∆` (p. 176): if `u(·, ℓ_l)` is continuous and strictly increasing
  on `[0, c_l]` and `u(0, ℓ_l) < u(c_d, ℓ_d) < u(c_l, ℓ_l)`, there is exactly one `∆ ∈ (0, 1)` with
  `u(c_l(1 − ∆), ℓ_l) = u(c_d, ℓ_d)` (`welfare_cev_static`). In a dynamic model with log utility
  the uniform proportional cut `∆` is unique and given in closed form,
  `∆ = 1 − exp((1 − β)(U_d − U_l))` (`welfare_cev_dynamic_log`).
* Behind the veil of ignorance (p. 186): with strictly concave `u`, the problem
  `max πu(c_A) + (1 − π)u(c_B)` subject to `πc_A + (1 − π)c_B = πω_A + (1 − π)ω_B` is solved by
  `c_A = c_B` (`veil_equal_split`), and only by it (`veil_optimum_equal`).

The book's existence claim for general dynamic utilities ("a unique `∆` can still be defined")
is formalised for log utility only.
-/

namespace AKMM.Welfare

/-- **AKMM, p. 176: the consumption-equivalent welfare measure.** Let `g = u(·, ℓ_l)` be
continuous and strictly increasing on `[0, c_l]`, `c_l > 0`, and `g(0) < U_d < g(c_l)`, where
`U_d = u(c_d, ℓ_d)` and `g(c_l) = u(c_l, ℓ_l)`. Then there is exactly one `∆ ∈ (0, 1)` with
`u(c_l(1 − ∆), ℓ_l) = U_d`. -/
theorem welfare_cev_static {g : ℝ → ℝ} {cl Ud : ℝ} (hcl : 0 < cl)
    (hcont : ContinuousOn g (Set.Icc 0 cl)) (hmono : StrictMonoOn g (Set.Icc 0 cl))
    (h0 : g 0 < Ud) (h1 : Ud < g cl) :
    ∃! Δ : ℝ, Δ ∈ Set.Ioo 0 1 ∧ g (cl * (1 - Δ)) = Ud := by
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo hcl.le hcont ⟨h0, h1⟩
  have hx0 := hx.1
  have hx1 := hx.2
  refine ⟨1 - x / cl, ⟨⟨by rw [sub_pos, div_lt_one hcl]; exact hx1,
    by have := div_pos hx0 hcl; linarith⟩,
    by rw [sub_sub_cancel, mul_div_cancel₀ _ hcl.ne']; exact hgx⟩,
    fun Δ ⟨hΔ, hgΔ⟩ => ?_⟩
  have hm : cl * (1 - Δ) ∈ Set.Icc 0 cl :=
    ⟨by nlinarith [hΔ.1, hΔ.2], by nlinarith [hΔ.1, hΔ.2]⟩
  have hxm : x ∈ Set.Icc 0 cl := ⟨hx0.le, hx1.le⟩
  have : cl * (1 - Δ) = x := hmono.injOn hm hxm (by rw [hgΔ, hgx])
  field_simp
  linarith

/-- **AKMM, p. 176: the dynamic consumption equivalent with log utility.** For `0 ≤ β < 1`, a
positive consumption path `c` with a convergent utility series `U_l = Σ βᵗ log cₜ`, and `∆ < 1`,
cutting consumption by the fraction `∆` at every date gives utility
`Σ βᵗ log((1 − ∆)cₜ) = log(1 − ∆)/(1 − β) + U_l`; this equals `U_d` iff
`∆ = 1 − exp((1 − β)(U_d − U_l))`. So `∆` is unique, and positive iff `U_d < U_l`. -/
theorem welfare_cev_dynamic_log {β Ud Δ : ℝ} {c : ℕ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ t, 0 < c t) (hU : Summable fun t => β ^ t * Real.log (c t)) (hΔ : Δ < 1) :
    (∑' t, β ^ t * Real.log ((1 - Δ) * c t) =
        Real.log (1 - Δ) / (1 - β) + ∑' t, β ^ t * Real.log (c t)) ∧
      (∑' t, β ^ t * Real.log ((1 - Δ) * c t) = Ud ↔
        Δ = 1 - Real.exp ((1 - β) * (Ud - ∑' t, β ^ t * Real.log (c t)))) ∧
      (0 < 1 - Real.exp ((1 - β) * (Ud - ∑' t, β ^ t * Real.log (c t))) ↔
        Ud < ∑' t, β ^ t * Real.log (c t)) := by
  have h1Δ : 0 < 1 - Δ := by linarith
  have hgeo := summable_geometric_of_lt_one hβ0 hβ1
  have e : (fun t => β ^ t * Real.log ((1 - Δ) * c t)) =
      fun t => Real.log (1 - Δ) * β ^ t + β ^ t * Real.log (c t) := by
    funext t; rw [Real.log_mul h1Δ.ne' (hc t).ne']; ring
  have hsum : ∑' t, β ^ t * Real.log ((1 - Δ) * c t) =
      Real.log (1 - Δ) / (1 - β) + ∑' t, β ^ t * Real.log (c t) := by
    rw [e, (hgeo.mul_left _).tsum_add hU, tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1,
      div_eq_mul_inv]
  have hb : 0 < 1 - β := by linarith
  refine ⟨hsum, ?_, ?_⟩
  · rw [hsum]
    set Ul := ∑' t, β ^ t * Real.log (c t)
    constructor
    · intro h
      have : Real.log (1 - Δ) = (1 - β) * (Ud - Ul) := by
        field_simp at h ⊢; linarith
      rw [← this, Real.exp_log h1Δ]; ring
    · intro h
      have : 1 - Δ = Real.exp ((1 - β) * (Ud - Ul)) := by linarith
      rw [this, Real.log_exp]
      field_simp
      ring
  · rw [sub_pos, Real.exp_lt_one_iff, mul_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h; left; exact ⟨hb, by linarith⟩

/-- **AKMM, p. 186: behind the veil of ignorance.** If `u` is strictly concave on `(0, ∞)`,
`0 < π < 1`, and `(c_A, c_B)` is positive with `πc_A + (1 − π)c_B = m`, then
`πu(c_A) + (1 − π)u(c_B) ≤ u(m)`, strictly unless `c_A = c_B`: equal consumption `m` is the
unique optimum. -/
theorem veil_equal_split {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) {pr cA cB m : ℝ}
    (hpr0 : 0 < pr) (hpr1 : pr < 1) (hA : 0 < cA) (hB : 0 < cB)
    (hres : pr * cA + (1 - pr) * cB = m) :
    pr * u cA + (1 - pr) * u cB ≤ u m ∧ (cA ≠ cB → pr * u cA + (1 - pr) * u cB < u m) := by
  have hstrict : cA ≠ cB → pr * u cA + (1 - pr) * u cB < u m := by
    intro hne
    have := hu.2 (Set.mem_Ioi.2 hA) (Set.mem_Ioi.2 hB) hne hpr0 (by linarith : 0 < 1 - pr)
      (by ring)
    simpa [smul_eq_mul, hres] using this
  refine ⟨?_, hstrict⟩
  rcases eq_or_ne cA cB with h | h
  · subst h
    have : m = cA := by linarith
    subst this
    linarith
  · exact (hstrict h).le

/-- **AKMM, p. 186: "this optimization problem … delivers `c_A = c_B`".** Any solution of the
veil-of-ignorance problem (with strictly concave `u`, `0 < π < 1` and `m > 0`) has
`c_A = c_B = m`. -/
theorem veil_optimum_equal {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) {pr cA cB m : ℝ}
    (hpr0 : 0 < pr) (hpr1 : pr < 1) (hA : 0 < cA) (hB : 0 < cB) (hm : 0 < m)
    (hres : pr * cA + (1 - pr) * cB = m)
    (hopt : ∀ xA xB, 0 < xA → 0 < xB → pr * xA + (1 - pr) * xB = m →
      pr * u xA + (1 - pr) * u xB ≤ pr * u cA + (1 - pr) * u cB) : cA = m ∧ cB = m := by
  have heq : cA = cB := by
    by_contra hne
    have h1 := (veil_equal_split hu hpr0 hpr1 hA hB hres).2 hne
    have h2 := hopt m m hm hm (by ring)
    linarith
  subst heq
  constructor <;> linarith

end AKMM.Welfare
