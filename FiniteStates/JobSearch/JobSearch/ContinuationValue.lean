/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.BellmanOperator

/-!
# Computing the continuation value directly

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.3.2.2 (pp. 39–41).

Substituting `v*(w') = max{w'/(1 − β), h*}` into the definition of the
continuation value gives the scalar equation (1.32),

  `h* = c + β ∑ max{w'/(1 − β), h*} φ(w')`,

so `h*` is the fixed point of the map `g : ℝ₊ → ℝ₊` of (1.33). Exercise 1.3.2
shows `g` is a contraction and `h*` its unique fixed point in `ℝ₊`; iterating
`g` from any `h ≥ 0` converges to `h*`, a one-dimensional computation in place
of value function iteration in `ℝⁿ`. Exercise 1.3.3's identity
`v*(w) = max{w/(1 − β), h*}` and the policy characterisation (1.34) follow.

The comparative static of p. 7 is proved for the infinite horizon as well:
higher compensation raises `h*` and the reservation wage.
-/

open Filter Topology Function Set Finset

namespace SargentStachurski.JobSearch

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

/-- The map `g` of (1.33), p. 40: `g(h) = c + β ∑ max{w'/(1 − β), h} φ(w')`. -/
noncomputable def g (h : ℝ) : ℝ := m.c + m.β * m.E (fun w => max (m.stop w) h)

/-- (1.32), p. 40: `h*` solves `h = g(h)`. -/
theorem isFixedPt_g_hstar : IsFixedPt m.g m.hstar := by
  change m.g m.hstar = m.hstar
  unfold g
  have : (fun w => max (m.stop w) m.hstar) = m.vstar := by
    funext w
    exact (m.vstar_eq_max w).symm
  rw [this]
  rfl

/-- `g` maps `ℝ₊` into `ℝ₊` (indeed `g(h) ≥ c > 0`). -/
theorem g_nonneg (h : ℝ) : 0 ≤ m.g h := by
  unfold g
  have : 0 ≤ m.E (fun w => max (m.stop w) h) :=
    m.E_nonneg fun w => (m.stop_nonneg w).trans (le_max_left _ _)
  nlinarith [m.c_pos, m.β_pos]

theorem mapsTo_g : MapsTo m.g (Ici 0) (Ici 0) := fun h _ => m.g_nonneg h

/-- `|g(h) − g(h')| ≤ β|h − h'|`, by the bound (1.28) inside the expectation. -/
theorem abs_g_sub_g_le (h h' : ℝ) : |m.g h - m.g h'| ≤ m.β * |h - h'| := by
  unfold g
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos m.β_pos]
  refine mul_le_mul_of_nonneg_left ?_ m.β_nonneg
  rw [E, E, ← sum_sub_distrib]
  calc |∑ w, (max (m.stop w) h * m.φ w - max (m.stop w) h' * m.φ w)|
      ≤ ∑ w, |max (m.stop w) h * m.φ w - max (m.stop w) h' * m.φ w| := abs_sum_le_sum_abs _ _
    _ = ∑ w, |max (m.stop w) h - max (m.stop w) h'| * m.φ w := by
        refine sum_congr rfl fun w _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (m.φ_nonneg w)]
    _ ≤ ∑ w, |h - h'| * m.φ w :=
        sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (abs_max_sub_max_le _ _ _) (m.φ_nonneg w)
    _ = |h - h'| := by rw [← mul_sum, m.φ_sum, mul_one]

/-- Exercise 1.3.2 (p. 40): `g` is a contraction of modulus `β` on `ℝ₊`. -/
theorem isContractionOn_g : IsContractionOn m.g (Ici 0) m.β :=
  ⟨m.mapsTo_g, m.β_nonneg, m.β_lt_one, fun h _ h' _ => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact m.abs_g_sub_g_le h h'⟩

/-- `g` is a contraction of modulus `β` on all of `ℝ`. -/
theorem isContractionOn_g_univ : IsContractionOn m.g univ m.β :=
  ⟨mapsTo_univ _ _, m.β_nonneg, m.β_lt_one, fun h _ h' _ => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact m.abs_g_sub_g_le h h'⟩

/-- `h* ≥ 0`, so `h*` lies in the domain `ℝ₊` of (1.33). -/
theorem hstar_nonneg : 0 ≤ m.hstar := by
  rw [← m.isFixedPt_g_hstar.eq]
  exact m.g_nonneg _

/-- Exercise 1.3.2 (p. 40), conclusion: `h*` is the unique fixed point of `g` in `ℝ₊`. -/
theorem eq_hstar_of_isFixedPt_g {h : ℝ} (hh : IsFixedPt m.g h) : h = m.hstar :=
  m.isContractionOn_g_univ.fixedPt_unique trivial trivial hh m.isFixedPt_g_hstar

/-- Iterating `g` from any `h` converges to `h*` (p. 40): the one-dimensional computation of
the continuation value. -/
theorem tendsto_iterate_g (h : ℝ) : Tendsto (fun k : ℕ => m.g^[k] h) atTop (𝓝 m.hstar) :=
  m.isContractionOn_g_univ.tendsto_iterate_fixedPt trivial trivial m.isFixedPt_g_hstar

/-- The rate: `|gᵏ(h) − h*| ≤ βᵏ|h − h*|`. -/
theorem abs_iterate_g_sub_hstar_le (h : ℝ) (k : ℕ) :
    |m.g^[k] h - m.hstar| ≤ m.β ^ k * |h - m.hstar| := by
  have := m.isContractionOn_g_univ.norm_iterate_sub_fixedPt_le trivial trivial
    m.isFixedPt_g_hstar (u := h) k
  simpa [Real.norm_eq_abs] using this

/-- Exercise 1.3.3 (p. 41): with `h*` in hand, `v*(w) = max{w/(1 − β), h*}`, so the value
function computed from `h*` agrees with the one from value function iteration. -/
theorem vstar_eq_max_hstar (w : W) : m.vstar w = max (m.wage w / (1 - m.β)) m.hstar :=
  m.vstar_eq_max w

/-- (1.34), p. 41: a policy is `v*`-greedy iff it accepts exactly when `w/(1 − β) ≥ h*`. -/
theorem isGreedy_vstar_iff_hstar (σ : Policy W) :
    m.IsGreedy m.vstar σ ↔ ∀ w, σ w = true ↔ m.hstar ≤ m.stop w :=
  Iff.rfl

/-! ### Higher compensation raises the continuation value and the reservation wage

The two-period comparative static of p. 7, for the infinite horizon: if `c ≤ c'` with the same
wages, distribution and discount factor, then `h* ≤ h*'` and `w* ≤ w*'`. The argument is the
scalar case of Proposition 2.2.7 (Chapter 2): `g ≤ g'` pointwise, `g'` is order preserving, and
both are contractions, so the fixed points are ordered. -/

/-- `g` is order preserving. -/
theorem g_mono : Monotone m.g := by
  intro h h' hh
  unfold g
  have : m.E (fun w => max (m.stop w) h) ≤ m.E (fun w => max (m.stop w) h') :=
    m.E_mono fun w => max_le_max_left _ hh
  nlinarith [m.β_pos]

/-- `g ≤ g'` pointwise when `c ≤ c'`. -/
theorem g_le_g_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ) (hβ : m.β = m'.β)
    (hc : m.c ≤ m'.c) (h : ℝ) : m.g h ≤ m'.g h := by
  unfold g
  have : m.E (fun w => max (m.stop w) h) = m'.E (fun w => max (m'.stop w) h) := by
    simp only [E, stop, hw, hφ, hβ]
  rw [this, hβ]
  linarith

/-- The continuation value is increasing in `c`. -/
theorem hstar_le_hstar_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) : m.hstar ≤ m'.hstar := by
  by_contra hlt
  have hlt' : m'.hstar < m.hstar := not_le.1 hlt
  -- `h*' = g'(h*') ≥ g(h*')` and `g(h*) − g(h*') ≤ β(h* − h*')`, so `(1 − β)(h* − h*') ≤ 0`
  have h1 : m.g m'.hstar ≤ m'.hstar := by
    calc m.g m'.hstar ≤ m'.g m'.hstar := m.g_le_g_of_c_le m' hw hφ hβ hc _
      _ = m'.hstar := m'.isFixedPt_g_hstar
  have h2 : m.hstar - m.g m'.hstar ≤ m.β * (m.hstar - m'.hstar) := by
    have := m.abs_g_sub_g_le m.hstar m'.hstar
    rw [m.isFixedPt_g_hstar.eq] at this
    have hpos : 0 < m.hstar - m'.hstar := by linarith
    rw [abs_of_pos hpos] at this
    exact (le_abs_self _).trans this
  have h3 := m.β_lt_one
  nlinarith

/-- The reservation wage is increasing in `c`. -/
theorem reservationWage_le_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) : m.reservationWage ≤ m'.reservationWage := by
  unfold reservationWage
  rw [hβ]
  exact mul_le_mul_of_nonneg_left (m.hstar_le_hstar_of_c_le m' hw hφ hβ hc) m'.one_sub_β_pos.le

end Model

end SargentStachurski.JobSearch
