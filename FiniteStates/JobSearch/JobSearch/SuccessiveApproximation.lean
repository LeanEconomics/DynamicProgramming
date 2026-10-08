/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.Contractions
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Successive approximation and the Solow–Swan example

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.3 (pp. 24–28).

Successive approximation (p. 24) computes the fixed point of a globally
stable map by iterating it; the convergence claim *is* global stability, so
the theorem here only unpacks the definition. The substance of the section is
the Solow–Swan example (1.19), `k' = s f(k) + (1 − δ)k` with `f(k) = A kᵅ`:
Exercise 1.2.25 shows the map `g` is a self-map of `U = (0, ∞)` but *not* a
contraction there (its slope is unbounded near `0`), and Exercise 1.2.26 shows
it is nonetheless globally stable, with fixed point `k* = (sA/δ)^{1/(1−α)}`,
because `g` moves every `k` monotonically towards `k*`.
-/

open Filter Topology Function Set

namespace SargentStachurski.JobSearch

/-- Successive approximation (p. 24): under global stability the iterates converge to the fixed
point from any starting point. -/
theorem GloballyStable.tendsto_iterate {U : Type*} [TopologicalSpace U] {T : U → U}
    (h : GloballyStable T) {u' : U} (hu' : IsFixedPt T u') (u : U) :
    Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  obtain ⟨u₀, -, huniq, hlim⟩ := h
  rw [huniq u' hu']
  exact hlim u

/-- The Solow–Swan model with Cobb–Douglas production, Exercise 1.2.25 (p. 27):
`f(k) = A kᵅ`, saving rate `s`, depreciation `δ`. -/
structure Solow where
  A : ℝ
  s : ℝ
  δ : ℝ
  α : ℝ
  A_pos : 0 < A
  s_pos : 0 < s
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  α_pos : 0 < α
  α_lt_one : α < 1

namespace Solow

variable (m : Solow)

/-- The Solow–Swan map (1.19), p. 27: `g(k) = s A kᵅ + (1 − δ)k`. -/
noncomputable def g (k : ℝ) : ℝ := m.s * m.A * k ^ m.α + (1 - m.δ) * k

/-- The steady state of Exercise 1.2.26 (p. 27): `k* = (sA/δ)^{1/(1−α)}`. -/
noncomputable def kstar : ℝ := (m.s * m.A / m.δ) ^ (1 / (1 - m.α))

theorem one_sub_α_pos : 0 < 1 - m.α := by linarith [m.α_lt_one]

theorem one_sub_δ_pos : 0 < 1 - m.δ := by linarith [m.δ_lt_one]

theorem sA_pos : 0 < m.s * m.A := mul_pos m.s_pos m.A_pos

theorem kstar_pos : 0 < m.kstar :=
  Real.rpow_pos_of_pos (div_pos m.sA_pos m.δ_pos) _

/-- `δ (sA/δ) = sA`. -/
theorem δ_mul_div : m.δ * (m.s * m.A / m.δ) = m.s * m.A := by
  have hδ := m.δ_pos.ne'
  rw [mul_div_assoc', mul_comm m.δ, mul_div_assoc, div_self hδ, mul_one]

/-- `(k*)^{1−α} = sA/δ`. -/
theorem kstar_rpow : m.kstar ^ (1 - m.α) = m.s * m.A / m.δ := by
  unfold kstar
  rw [← Real.rpow_mul (div_pos m.sA_pos m.δ_pos).le, one_div_mul_cancel m.one_sub_α_pos.ne',
    Real.rpow_one]

/-- `kᵅ k^{1−α} = k` for `k > 0`. -/
theorem rpow_mul_rpow {k : ℝ} (hk : 0 < k) : k ^ m.α * k ^ (1 - m.α) = k := by
  rw [← Real.rpow_add hk]
  simp

/-- Exercise 1.2.25 (p. 27), first part: `g` sends `U = (0, ∞)` into itself. -/
theorem g_pos {k : ℝ} (hk : 0 < k) : 0 < m.g k := by
  unfold g
  have h1 := mul_pos m.sA_pos (Real.rpow_pos_of_pos hk m.α)
  have h2 := mul_pos m.one_sub_δ_pos hk
  linarith

/-- `g` maps `(0, ∞)` to itself, as a `MapsTo`. -/
theorem mapsTo_g : MapsTo m.g (Ioi 0) (Ioi 0) := fun _ hk => m.g_pos hk

/-- `g` is strictly increasing on `(0, ∞)`. -/
theorem g_strictMonoOn : StrictMonoOn m.g (Ioi 0) := by
  intro x hx y hy hxy
  unfold g
  have h1 : x ^ m.α < y ^ m.α := Real.rpow_lt_rpow (le_of_lt hx) hxy m.α_pos
  have h2 := m.one_sub_δ_pos
  have h3 := m.sA_pos
  nlinarith

/-- `g` is continuous. -/
theorem continuous_g : Continuous m.g := by
  unfold g
  have := Real.continuous_rpow_const m.α_pos.le
  fun_prop

/-- Exercise 1.2.25 (p. 27), second part: `g` is not a contraction on `(0, ∞)` for any modulus.
The book's hint is the derivative `g'(k) → ∞` as `k → 0`; here the chord from `k/2` to `k` is
compared with its length directly. -/
theorem not_isContractionOn_g (L : ℝ) : ¬ IsContractionOn m.g (Ioi 0) L := by
  intro h
  -- the contraction inequality on the pair `(x, x/2)` gives `sA xᵅ (1 − 2^{−α}) < δ x / 2`
  have key : ∀ x : ℝ, 0 < x → m.s * m.A * x ^ m.α * (1 - (2 : ℝ) ^ (-m.α)) < m.δ * x / 2 := by
    intro x hx
    have hx2 : 0 < x / 2 := by positivity
    have hb := h.norm_sub_le x hx (x / 2) hx2
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hb
    have hmono : m.g (x / 2) < m.g x := m.g_strictMonoOn hx2 hx (by linarith)
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hb
    have hL : L * (x - x / 2) < x - x / 2 := by
      have := h.lt_one
      nlinarith
    have hhalf : (x / 2) ^ m.α = x ^ m.α * (2 : ℝ) ^ (-m.α) := by
      rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
    unfold g at hb hmono
    rw [hhalf] at hb
    nlinarith [hb, hL]
  have h2 : 0 < 1 - (2 : ℝ) ^ (-m.α) := by
    have : (2 : ℝ) ^ (-m.α) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [m.α_pos])
    linarith
  -- choose `x` with `x^{1−α} = 2 sA (1 − 2^{−α}) / δ`, which turns the strict inequality into
  -- an equality
  set c : ℝ := 2 * (m.s * m.A) * (1 - (2 : ℝ) ^ (-m.α)) / m.δ with hc
  have hcpos : 0 < c := by have := m.sA_pos; have := m.δ_pos; positivity
  have hcδ : c * m.δ = 2 * (m.s * m.A) * (1 - (2 : ℝ) ^ (-m.α)) := by
    rw [hc]
    exact div_mul_cancel₀ _ m.δ_pos.ne'
  set x : ℝ := c ^ (1 / (1 - m.α)) with hxdef
  have hxpos : 0 < x := Real.rpow_pos_of_pos hcpos _
  have hxc : x ^ (1 - m.α) = c := by
    rw [hxdef, ← Real.rpow_mul hcpos.le, one_div_mul_cancel m.one_sub_α_pos.ne', Real.rpow_one]
  have hx_eq : x = x ^ m.α * c := by
    rw [← hxc]
    exact (m.rpow_mul_rpow hxpos).symm
  have hk := key x hxpos
  -- `δ x / 2 = δ xᵅ c / 2 = sA xᵅ (1 − 2^{−α})`, so the strict inequality reads `t < t`
  have e : m.δ * x / 2 = m.s * m.A * x ^ m.α * (1 - (2 : ℝ) ^ (-m.α)) := by
    calc m.δ * x / 2 = m.δ * (x ^ m.α * c) / 2 := by rw [← hx_eq]
      _ = m.s * m.A * x ^ m.α * (1 - (2 : ℝ) ^ (-m.α)) := by
        linear_combination (x ^ m.α / 2) * hcδ
  linarith

/-- Exercise 1.2.26 (p. 27): `k*` is a fixed point of `g`. -/
theorem isFixedPt_kstar : IsFixedPt m.g m.kstar := by
  change m.g m.kstar = m.kstar
  have h2 : m.δ * m.kstar ^ (1 - m.α) = m.s * m.A := by
    rw [m.kstar_rpow]
    exact m.δ_mul_div
  have h1 : m.s * m.A * m.kstar ^ m.α = m.δ * m.kstar := by
    calc m.s * m.A * m.kstar ^ m.α = m.kstar ^ m.α * (m.δ * m.kstar ^ (1 - m.α)) := by
          rw [h2]; ring
      _ = m.δ * (m.kstar ^ m.α * m.kstar ^ (1 - m.α)) := by ring
      _ = m.δ * m.kstar := by rw [m.rpow_mul_rpow m.kstar_pos]
  unfold g
  rw [h1]
  ring

/-- The sign of `g(k) − k` on `(0, ∞)`: `g(k) − k = kᵅ (sA − δ k^{1−α})`. -/
theorem g_sub_self {k : ℝ} (hk : 0 < k) :
    m.g k - k = k ^ m.α * (m.s * m.A - m.δ * k ^ (1 - m.α)) := by
  unfold g
  calc m.s * m.A * k ^ m.α + (1 - m.δ) * k - k
      = m.s * m.A * k ^ m.α - m.δ * (k ^ m.α * k ^ (1 - m.α)) := by
        rw [m.rpow_mul_rpow hk]; ring
    _ = k ^ m.α * (m.s * m.A - m.δ * k ^ (1 - m.α)) := by ring

/-- Exercise 1.2.26 (i), p. 27: if `0 < k ≤ k*` then `k ≤ g(k) ≤ k*`. -/
theorem le_g_le_of_le_kstar {k : ℝ} (hk : 0 < k) (hle : k ≤ m.kstar) :
    k ≤ m.g k ∧ m.g k ≤ m.kstar := by
  constructor
  · have h1 : k ^ (1 - m.α) ≤ m.kstar ^ (1 - m.α) :=
      Real.rpow_le_rpow hk.le hle m.one_sub_α_pos.le
    rw [m.kstar_rpow] at h1
    have h2 : m.δ * k ^ (1 - m.α) ≤ m.s * m.A := by
      calc m.δ * k ^ (1 - m.α) ≤ m.δ * (m.s * m.A / m.δ) :=
            mul_le_mul_of_nonneg_left h1 m.δ_pos.le
        _ = m.s * m.A := m.δ_mul_div
    have h3 : 0 ≤ k ^ m.α := (Real.rpow_pos_of_pos hk _).le
    have := m.g_sub_self hk
    nlinarith
  · calc m.g k ≤ m.g m.kstar := m.g_strictMonoOn.monotoneOn hk m.kstar_pos hle
      _ = m.kstar := m.isFixedPt_kstar

/-- Exercise 1.2.26 (ii), p. 27: if `k* ≤ k` then `k* ≤ g(k) ≤ k`. -/
theorem kstar_le_g_le_of_kstar_le {k : ℝ} (hle : m.kstar ≤ k) :
    m.kstar ≤ m.g k ∧ m.g k ≤ k := by
  have hk : 0 < k := lt_of_lt_of_le m.kstar_pos hle
  constructor
  · calc m.kstar = m.g m.kstar := m.isFixedPt_kstar.eq.symm
      _ ≤ m.g k := m.g_strictMonoOn.monotoneOn m.kstar_pos hk hle
  · have h1 : m.kstar ^ (1 - m.α) ≤ k ^ (1 - m.α) :=
      Real.rpow_le_rpow m.kstar_pos.le hle m.one_sub_α_pos.le
    rw [m.kstar_rpow] at h1
    have h2 : m.s * m.A ≤ m.δ * k ^ (1 - m.α) := by
      calc m.s * m.A = m.δ * (m.s * m.A / m.δ) := m.δ_mul_div.symm
        _ ≤ m.δ * k ^ (1 - m.α) := mul_le_mul_of_nonneg_left h1 m.δ_pos.le
    have h3 : 0 ≤ k ^ m.α := (Real.rpow_pos_of_pos hk _).le
    have := m.g_sub_self hk
    nlinarith

/-- Exercise 1.2.26 (p. 27): `k*` is the unique fixed point of `g` in `(0, ∞)`. -/
theorem eq_kstar_of_isFixedPt {k : ℝ} (hk : 0 < k) (hfix : IsFixedPt m.g k) : k = m.kstar := by
  have h0 := m.g_sub_self hk
  rw [hfix.eq, sub_self] at h0
  have h3 : 0 < k ^ m.α := Real.rpow_pos_of_pos hk _
  have h4 : m.δ * k ^ (1 - m.α) = m.s * m.A := by
    have := mul_eq_zero.1 h0.symm
    rcases this with h | h
    · exact absurd h h3.ne'
    · linarith
  rcases lt_trichotomy k m.kstar with hlt | heq | hgt
  · exfalso
    have h1 : k ^ (1 - m.α) < m.kstar ^ (1 - m.α) :=
      Real.rpow_lt_rpow hk.le hlt m.one_sub_α_pos
    rw [m.kstar_rpow] at h1
    have h2 : m.δ * k ^ (1 - m.α) < m.s * m.A := by
      calc m.δ * k ^ (1 - m.α) < m.δ * (m.s * m.A / m.δ) :=
            mul_lt_mul_of_pos_left h1 m.δ_pos
        _ = m.s * m.A := m.δ_mul_div
    linarith
  · exact heq
  · exfalso
    have h1 : m.kstar ^ (1 - m.α) < k ^ (1 - m.α) :=
      Real.rpow_lt_rpow m.kstar_pos.le hgt m.one_sub_α_pos
    rw [m.kstar_rpow] at h1
    have h2 : m.s * m.A < m.δ * k ^ (1 - m.α) := by
      calc m.s * m.A = m.δ * (m.s * m.A / m.δ) := m.δ_mul_div.symm
        _ < m.δ * k ^ (1 - m.α) := mul_lt_mul_of_pos_left h1 m.δ_pos
    linarith

/-- The iterates stay positive. -/
theorem iterate_g_pos {k : ℝ} (hk : 0 < k) (j : ℕ) : 0 < m.g^[j] k :=
  iterate_mem_of_mapsTo m.mapsTo_g hk j

/-- From `0 < k₀ ≤ k*` the iterates stay below `k*`. -/
theorem iterate_le_kstar {k : ℝ} (hk : 0 < k) (hle : k ≤ m.kstar) (j : ℕ) :
    m.g^[j] k ≤ m.kstar := by
  induction j with
  | zero => simpa using hle
  | succ j ih =>
    rw [iterate_succ_apply']
    exact (m.le_g_le_of_le_kstar (m.iterate_g_pos hk j) ih).2

/-- From `k* ≤ k₀` the iterates stay above `k*`. -/
theorem kstar_le_iterate {k : ℝ} (hle : m.kstar ≤ k) (j : ℕ) : m.kstar ≤ m.g^[j] k := by
  induction j with
  | zero => simpa using hle
  | succ j ih =>
    rw [iterate_succ_apply']
    exact (m.kstar_le_g_le_of_kstar_le ih).1

/-- Exercise 1.2.26 (p. 27), conclusion: from every `k₀ > 0` the Solow–Swan iterates converge to
`k*`. The sequence is monotone and bounded by (i) or (ii), so it converges; its limit is a
positive fixed point by continuity (Exercise 1.2.16), hence `k*`. -/
theorem tendsto_iterate_kstar {k : ℝ} (hk : 0 < k) :
    Tendsto (fun j : ℕ => m.g^[j] k) atTop (𝓝 m.kstar) := by
  rcases le_total k m.kstar with hle | hle
  · -- increasing, bounded above by `k*`
    have hmono : Monotone fun j : ℕ => m.g^[j] k := by
      refine monotone_nat_of_le_succ fun j => ?_
      rw [iterate_succ_apply']
      exact (m.le_g_le_of_le_kstar (m.iterate_g_pos hk j) (m.iterate_le_kstar hk hle j)).1
    have hbdd : BddAbove (range fun j : ℕ => m.g^[j] k) :=
      ⟨m.kstar, by rintro _ ⟨j, rfl⟩; exact m.iterate_le_kstar hk hle j⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hℓpos : 0 < ⨆ j : ℕ, m.g^[j] k :=
      lt_of_lt_of_le hk (by simpa using le_ciSup hbdd 0)
    have hfix : IsFixedPt m.g (⨆ j : ℕ, m.g^[j] k) :=
      isFixedPt_of_tendsto_iterate hlim m.continuous_g.continuousAt
    rwa [m.eq_kstar_of_isFixedPt hℓpos hfix] at hlim
  · -- decreasing, bounded below by `k*`
    have hanti : Antitone fun j : ℕ => m.g^[j] k := by
      refine antitone_nat_of_succ_le fun j => ?_
      rw [iterate_succ_apply']
      exact (m.kstar_le_g_le_of_kstar_le (m.kstar_le_iterate hle j)).2
    have hbdd : BddBelow (range fun j : ℕ => m.g^[j] k) :=
      ⟨m.kstar, by rintro _ ⟨j, rfl⟩; exact m.kstar_le_iterate hle j⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hℓpos : 0 < ⨅ j : ℕ, m.g^[j] k :=
      lt_of_lt_of_le m.kstar_pos (le_ciInf fun j => m.kstar_le_iterate hle j)
    have hfix : IsFixedPt m.g (⨅ j : ℕ, m.g^[j] k) :=
      isFixedPt_of_tendsto_iterate hlim m.continuous_g.continuousAt
    rwa [m.eq_kstar_of_isFixedPt hℓpos hfix] at hlim

/-- Exercise 1.2.26 (p. 27): `g` is globally stable on `U = (0, ∞)`, as a self-map of the
subtype. The "why?" of the exercise: monotone bounded sequences converge, limits of iterates
of a continuous map are fixed points, and the fixed point is unique. -/
theorem globallyStable_g : GloballyStable (m.mapsTo_g.restrict m.g (Ioi 0) (Ioi 0)) := by
  have hiter : ∀ (u : Ioi (0 : ℝ)) (j : ℕ),
      ((m.mapsTo_g.restrict m.g (Ioi 0) (Ioi 0))^[j] u : ℝ) = m.g^[j] u := by
    intro u j
    rw [MapsTo.iterate_restrict]
    rfl
  refine globallyStable_of_tendsto (u' := ⟨m.kstar, m.kstar_pos⟩) ?_ fun u => ?_
  · exact Subtype.ext (by simpa [MapsTo.val_restrict_apply] using m.isFixedPt_kstar.eq)
  · rw [tendsto_subtype_rng]
    simp only [hiter]
    exact m.tendsto_iterate_kstar u.2

end Solow

end SargentStachurski.JobSearch
