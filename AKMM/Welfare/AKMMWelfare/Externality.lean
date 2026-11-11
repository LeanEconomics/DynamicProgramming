/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A production externality

AKMM, §6.3.2, pp. 168–169. The consumer maximises `log c − Bℓ^{1+1/θ}/(1 + 1/θ)` subject to
`c = rk + wℓ`; the representative firm produces `A(ȳ)k^αℓ^{1−α}` taking aggregate output `ȳ`
as given.

* The equilibrium condition `1 − α = Bℓ^{1+1/θ}` from the consumer's condition
  `w/(rk + wℓ) = Bℓ^{1/θ}` and the firm's `r/w = αℓ/((1 − α)k)` (`ext_equilibrium_hours`); its
  positive solution is unique and does not involve `A` (`ext_equilibrium_hours_unique`).
* The planner's first-order conditions give `(1 − α)/(1 − A′(y)k^αℓ^{1−α}) = Bℓ^{1+1/θ}`
  (`ext_planner_hours`); the equilibrium is optimal only if `A′(y) = 0` (`ext_not_optimal`); with
  a negative externality (`A′ < 0`) the planner's hours are strictly lower
  (`ext_overwork`).
* Fn. 7: at a zero-profit input choice, a rise in the firm's TFP makes profits positive and
  unbounded along a ray of input choices (`ext_fn7`).
-/

namespace AKMM.Welfare

/-- **AKMM, p. 169: equilibrium hours.** With `k, ℓ, w > 0`, `α < 1`, the consumer's condition
`w/(rk + wℓ) = Bℓ^{1/θ}` and the firm's `r/w = αℓ/((1 − α)k)` give `1 − α = Bℓ^{1+1/θ}`. -/
theorem ext_equilibrium_hours {α B θ k l r w : ℝ} (hα : α < 1) (hk : 0 < k) (hl : 0 < l)
    (hw : 0 < w) (hcons : w / (r * k + w * l) = B * l ^ (1 / θ))
    (hfirm : r / w = α * l / ((1 - α) * k)) : 1 - α = B * l ^ (1 + 1 / θ) := by
  have h1α : 0 < 1 - α := by linarith
  have hr : r * k = α * w * l / (1 - α) := by
    field_simp at hfirm ⊢
    linarith
  have hinc : r * k + w * l = w * l / (1 - α) := by
    rw [hr]; field_simp; ring
  rw [hinc] at hcons
  have e : w / (w * l / (1 - α)) = (1 - α) / l := by field_simp
  rw [e] at hcons
  rw [Real.rpow_add hl, Real.rpow_one]
  field_simp at hcons
  linarith

/-- **AKMM, p. 169: uniqueness.** For `B > 0`, `θ > 0`, `α < 1`, the positive solution of
`1 − α = Bℓ^{1+1/θ}` is `ℓ = ((1 − α)/B)^{1/(1+1/θ)}`, the same for every TFP function `A`. -/
theorem ext_equilibrium_hours_unique {α B θ l : ℝ} (hB : 0 < B) (hθ : 0 < θ) (hl : 0 < l)
    (h : 1 - α = B * l ^ (1 + 1 / θ)) : l = ((1 - α) / B) ^ (1 / (1 + 1 / θ)) := by
  have hpos : 0 < 1 + 1 / θ := by positivity
  rw [h, mul_div_cancel_left₀ _ hB.ne', ← Real.rpow_mul hl.le, mul_one_div_cancel hpos.ne',
    Real.rpow_one]

/-- **AKMM, p. 169: the planner's hours.** From the first-order conditions
`Bℓ^{1/θ} = λ(1 − α)A(y)k^αℓ^{−α}` and `1/y = λ(1 − A′(y)k^αℓ^{1−α})` and the constraint
`y = A(y)k^αℓ^{1−α}` (with `y, ℓ > 0`) follows `(1 − α)/(1 − A′(y)k^αℓ^{1−α}) = Bℓ^{1+1/θ}`. -/
theorem ext_planner_hours {α B θ k l y lam Ay dA : ℝ} (hl : 0 < l) (hy : 0 < y)
    (hfoc1 : B * l ^ (1 / θ) = lam * (1 - α) * Ay * k ^ α * l ^ (-α))
    (hfoc2 : 1 / y = lam * (1 - dA * k ^ α * l ^ (1 - α)))
    (hcon : y = Ay * k ^ α * l ^ (1 - α)) :
    1 - dA * k ^ α * l ^ (1 - α) ≠ 0 ∧
      (1 - α) / (1 - dA * k ^ α * l ^ (1 - α)) = B * l ^ (1 + 1 / θ) := by
  set D := dA * k ^ α * l ^ (1 - α) with hD
  have hD1 : 1 - D ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfoc2
    exact (one_div_pos.2 hy).ne' hfoc2
  refine ⟨hD1, ?_⟩
  have hlam : lam = 1 / (y * (1 - D)) := by
    field_simp at hfoc2 ⊢
    linarith
  have hsplit : l ^ (1 - α) = l * l ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hl, Real.rpow_one]
  have hyl : Ay * k ^ α * l ^ (-α) = y / l := by
    rw [hcon, hsplit]; field_simp
  rw [Real.rpow_add hl, Real.rpow_one, mul_comm l, ← mul_assoc, hfoc1, hlam]
  have e : 1 / (y * (1 - D)) * (1 - α) * Ay * k ^ α * l ^ (-α) * l =
      (1 - α) / (y * (1 - D)) * (Ay * k ^ α * l ^ (-α)) * l := by ring
  rw [e, hyl]
  field_simp

/-- **AKMM, p. 169: the equilibrium is not optimal unless `A′(y) = 0`.** If the same `ℓ` solves
the equilibrium condition `1 − α = Bℓ^{1+1/θ}` and the planner's condition (with `k, ℓ > 0` and
`α < 1`), then `A′(y) = 0`. -/
theorem ext_not_optimal {α B θ k l dA : ℝ} (hα : α < 1) (hk : 0 < k) (hl : 0 < l)
    (hD1 : 1 - dA * k ^ α * l ^ (1 - α) ≠ 0) (heq : 1 - α = B * l ^ (1 + 1 / θ))
    (hpl : (1 - α) / (1 - dA * k ^ α * l ^ (1 - α)) = B * l ^ (1 + 1 / θ)) : dA = 0 := by
  rw [← heq, div_eq_iff hD1] at hpl
  have h1α : (1 - α) ≠ 0 := by linarith
  have : (1 - α) * (dA * k ^ α * l ^ (1 - α)) = 0 := by linarith
  have hkl : k ^ α * l ^ (1 - α) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hl _).ne'
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h1α
  · rw [mul_assoc] at h
    exact (mul_eq_zero.1 h).resolve_right hkl

/-- **AKMM, p. 169: too much work under a negative externality.** If `A′ < 0` at the planner's
optimum `(ℓ_P, y_P)` and `ℓ_E` solves the equilibrium condition, then `ℓ_P < ℓ_E`. -/
theorem ext_overwork {α B θ k lP lE dA : ℝ} (hα : α < 1) (hB : 0 < B) (hθ : 0 < θ)
    (hk : 0 < k) (hlP : 0 < lP) (hlE : 0 < lE) (hdA : dA < 0)
    (heq : 1 - α = B * lE ^ (1 + 1 / θ))
    (hpl : (1 - α) / (1 - dA * k ^ α * lP ^ (1 - α)) = B * lP ^ (1 + 1 / θ)) : lP < lE := by
  have hD : dA * k ^ α * lP ^ (1 - α) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdA (Real.rpow_pos_of_pos hk _))
      (Real.rpow_pos_of_pos hlP _)
  have h1α : 0 < 1 - α := by linarith
  have hlt : (1 - α) / (1 - dA * k ^ α * lP ^ (1 - α)) < 1 - α := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hpow : lP ^ (1 + 1 / θ) < lE ^ (1 + 1 / θ) := by
    rw [hpl] at hlt
    rw [heq] at hlt
    exact lt_of_mul_lt_mul_left hlt hB.le
  have hpos : 0 < 1 + 1 / θ := by positivity
  exact (Real.rpow_lt_rpow_iff hlP.le hlE.le hpos).1 hpow

/-- **AKMM, fn. 7, p. 169.** If the input choice `(k, ℓ)` makes zero profit at TFP `A`,
`Ak^αℓ^{1−α} = rk + wℓ`, and the firm's TFP rises to `A′ > A` (other firms produce less), then
profits at `(sk, sℓ)` are `s(A′ − A)k^αℓ^{1−α}`: positive and unbounded in `s`. -/
theorem ext_fn7 {A A' α r w k l : ℝ} (hk : 0 < k) (hl : 0 < l) (hA : A < A')
    (hzero : A * k ^ α * l ^ (1 - α) = r * k + w * l) :
    (∀ s, 0 < s → A' * (s * k) ^ α * (s * l) ^ (1 - α) - r * (s * k) - w * (s * l) =
      s * ((A' - A) * k ^ α * l ^ (1 - α))) ∧
    ∀ M : ℝ, ∃ s, 0 < s ∧ M < A' * (s * k) ^ α * (s * l) ^ (1 - α) - r * (s * k) - w * (s * l) := by
  have hprof : ∀ s, 0 < s → A' * (s * k) ^ α * (s * l) ^ (1 - α) - r * (s * k) - w * (s * l) =
      s * ((A' - A) * k ^ α * l ^ (1 - α)) := by
    intro s hs
    rw [Real.mul_rpow hs.le hk.le, Real.mul_rpow hs.le hl.le]
    have hss : s ^ α * s ^ (1 - α) = s := by
      rw [← Real.rpow_add hs, add_sub_cancel, Real.rpow_one]
    have : A' * (s ^ α * k ^ α) * (s ^ (1 - α) * l ^ (1 - α)) =
        (s ^ α * s ^ (1 - α)) * (A' * k ^ α * l ^ (1 - α)) := by ring
    rw [this, hss]
    linear_combination s * hzero
  refine ⟨hprof, fun M => ?_⟩
  have hg : 0 < (A' - A) * k ^ α * l ^ (1 - α) :=
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hk _)) (Real.rpow_pos_of_pos hl _)
  refine ⟨(|M| + 1) / ((A' - A) * k ^ α * l ^ (1 - α)), by positivity, ?_⟩
  rw [hprof _ (by positivity), div_mul_cancel₀ _ hg.ne']
  linarith [le_abs_self M]

end AKMM.Welfare
