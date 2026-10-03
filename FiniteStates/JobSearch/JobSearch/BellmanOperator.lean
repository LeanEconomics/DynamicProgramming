/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.Contractions
import JobSearch.Lattice
import JobSearch.Model
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# The Bellman operator for infinite-horizon job search

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.1.2 (pp. 10–12)
and §1.3.1 (pp. 32–36).

The worker maximises `E ∑ βᵗ Rₜ`, (1.6). Accepting `w` yields `w/(1 − β)`,
(1.7); the value function `v*` satisfies the Bellman equation (1.8) = (1.25).
The Bellman operator (1.27),

  `(Tv)(w) = max{ w/(1 − β), c + β ∑ v(w') φ(w') }`,

is a contraction of modulus `β` on `V = ℝ^W₊` in the supremum norm,
Proposition 1.3.1 (p. 33), so by Theorem 1.2.3 it has a unique fixed point
`v*` in `V`, and value function iteration `Tᵏv → v*` converges from every
`v ∈ V` at rate `βᵏ` (§1.3.2.1). The continuation value `h*`, (1.26), the
`v`-greedy policies, (1.29), and the reservation wage `w* = (1 − β)h*`,
(1.30), complete the section. The principle of optimality, that a `v*`-greedy
policy is optimal for (1.6), is stated in the book without proof here ("later
we prove it in a general setting", p. 12) and is not claimed.
-/

open Filter Topology Function Set Finset

namespace SargentStachurski.JobSearch

/-- The candidate space `V = ℝ^W₊` of nonnegative functions (p. 33). -/
def V (W : Type*) : Set (W → ℝ) := {v | ∀ w, 0 ≤ v w}

theorem V_nonempty (W : Type*) : (V W).Nonempty := ⟨0, fun _ => le_rfl⟩

theorem isClosed_V (W : Type*) : IsClosed (V W) := by
  have : V W = ⋂ w, {v : W → ℝ | 0 ≤ v w} := by
    ext v
    simp [V]
  rw [this]
  exact isClosed_iInter fun w => isClosed_le continuous_const (continuous_apply w)

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

/-- (1.7), p. 11: the lifetime payoff of a permanent job at wage `w` is
`w + βw + β²w + ⋯ = w/(1 − β)`. -/
theorem tsum_geometric_wage (w : W) : ∑' t : ℕ, m.β ^ t * m.wage w = m.wage w / (1 - m.β) := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one m.β_nonneg m.β_lt_one, div_eq_inv_mul]

/-- The stopping value `w/(1 − β)` of accepting the current offer. -/
noncomputable def stop (w : W) : ℝ := m.wage w / (1 - m.β)

theorem stop_nonneg (w : W) : 0 ≤ m.stop w := div_nonneg (m.wage_nonneg w) m.one_sub_β_pos.le

/-- The Bellman operator (1.27), p. 33: `(Tv)(w) = max{w/(1 − β), c + β ∑ v(w') φ(w')}`. -/
noncomputable def T (v : W → ℝ) : W → ℝ := fun w => max (m.stop w) (m.c + m.β * m.E v)

/-- `T` maps `V` into `V`: `Tv ≥ w/(1 − β) ≥ 0`. -/
theorem mapsTo_T : MapsTo m.T (V W) (V W) :=
  fun _ _ w => (m.stop_nonneg w).trans (le_max_left _ _)

/-- The pointwise estimate in the proof of Proposition 1.3.1 (p. 34):
`|(Tf)(w) − (Tg)(w)| ≤ β ∑ |f(w') − g(w')| φ(w') ≤ β‖f − g‖_∞`. -/
theorem abs_T_sub_T_le (f g : W → ℝ) (w : W) : |m.T f w - m.T g w| ≤ m.β * ‖f - g‖ := by
  calc |m.T f w - m.T g w| ≤ |(m.c + m.β * m.E f) - (m.c + m.β * m.E g)| :=
        abs_max_sub_max_le _ _ _
    _ = m.β * |m.E f - m.E g| := by
        rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos m.β_pos]
    _ ≤ m.β * ‖f - g‖ := mul_le_mul_of_nonneg_left (m.abs_E_sub_E_le f g) m.β_nonneg

/-- Proposition 1.3.1 (p. 33), the norm inequality: `‖Tf − Tg‖_∞ ≤ β‖f − g‖_∞`. -/
theorem norm_T_sub_T_le (f g : W → ℝ) : ‖m.T f - m.T g‖ ≤ m.β * ‖f - g‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg m.β_nonneg (norm_nonneg _))]
  intro w
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact m.abs_T_sub_T_le f g w

/-- Proposition 1.3.1 (p. 33): `T` is a contraction of modulus `β` on `V`. -/
theorem isContractionOn_T : IsContractionOn m.T (V W) m.β :=
  ⟨m.mapsTo_T, m.β_nonneg, m.β_lt_one, fun f _ g _ => m.norm_T_sub_T_le f g⟩

/-- `T` is in fact a contraction of modulus `β` on all of `ℝ^W`. -/
theorem isContractionOn_T_univ : IsContractionOn m.T univ m.β :=
  ⟨mapsTo_univ _ _, m.β_nonneg, m.β_lt_one, fun f _ g _ => m.norm_T_sub_T_le f g⟩

/-- The value function `v*` (p. 11, p. 33): the fixed point of `T` in `V` delivered by Theorem
1.2.3. -/
noncomputable def vstar : W → ℝ :=
  (m.isContractionOn_T.exists_fixedPt (isClosed_V W) (V_nonempty W)).choose

theorem vstar_mem_V : m.vstar ∈ V W :=
  (m.isContractionOn_T.exists_fixedPt (isClosed_V W) (V_nonempty W)).choose_spec.1

theorem vstar_nonneg (w : W) : 0 ≤ m.vstar w := m.vstar_mem_V w

theorem isFixedPt_vstar : IsFixedPt m.T m.vstar :=
  (m.isContractionOn_T.exists_fixedPt (isClosed_V W) (V_nonempty W)).choose_spec.2

/-- The Bellman equation (1.8), (1.25): `v*(w) = max{w/(1 − β), c + β ∑ v*(w') φ(w')}`. -/
theorem bellman_equation (w : W) :
    m.vstar w = max (m.wage w / (1 - m.β)) (m.c + m.β * m.E m.vstar) :=
  (congrFun m.isFixedPt_vstar.eq w).symm

/-- Any solution of the Bellman equation in `ℝ^W` is `v*`: uniqueness, from the contraction
property on all of `ℝ^W`. -/
theorem eq_vstar_of_isFixedPt {v : W → ℝ} (hv : IsFixedPt m.T v) : v = m.vstar :=
  m.isContractionOn_T_univ.fixedPt_unique trivial trivial hv m.isFixedPt_vstar

/-- `v*` is the unique fixed point of `T`. -/
theorem existsUnique_fixedPt : ∃! v : W → ℝ, IsFixedPt m.T v :=
  ⟨m.vstar, m.isFixedPt_vstar, fun _ hv => m.eq_vstar_of_isFixedPt hv⟩

/-- Value function iteration (§1.3.2.1, Algorithm 1.1): `Tᵏv → v*` from every `v ∈ ℝ^W`, in
particular from every `v ∈ V` as the book states after Proposition 1.3.1 (p. 33). -/
theorem tendsto_iterate_T (v : W → ℝ) : Tendsto (fun k : ℕ => m.T^[k] v) atTop (𝓝 m.vstar) :=
  m.isContractionOn_T_univ.tendsto_iterate_fixedPt trivial trivial m.isFixedPt_vstar

/-- The rate of value function iteration, (1.18) for `T`: `‖Tᵏv − v*‖ ≤ βᵏ‖v − v*‖`. -/
theorem norm_iterate_T_sub_vstar_le (v : W → ℝ) (k : ℕ) :
    ‖m.T^[k] v - m.vstar‖ ≤ m.β ^ k * ‖v - m.vstar‖ :=
  m.isContractionOn_T_univ.norm_iterate_sub_fixedPt_le trivial trivial m.isFixedPt_vstar k

/-- `T` is globally stable on `ℝ^W`. -/
theorem globallyStable_T : GloballyStable m.T :=
  globallyStable_of_tendsto m.isFixedPt_vstar m.tendsto_iterate_T

/-- The continuation value (1.26), p. 33: `h* = c + β ∑ v*(w') φ(w')`. -/
noncomputable def hstar : ℝ := m.c + m.β * m.E m.vstar

/-- The value function in terms of the continuation value: `v*(w) = max{w/(1 − β), h*}`
(p. 39). -/
theorem vstar_eq_max (w : W) : m.vstar w = max (m.wage w / (1 - m.β)) m.hstar :=
  m.bellman_equation w

/-- A policy (p. 35): a map from wage offers to `{accept, reject}`, here `Bool` with `true` for
accept (the book's `1`). -/
abbrev Policy (W : Type*) := W → Bool

/-- A `v`-greedy policy (1.29), p. 35: accept iff `w/(1 − β) ≥ c + β ∑ v(w') φ(w')`. -/
def IsGreedy (v : W → ℝ) (σ : Policy W) : Prop :=
  ∀ w, σ w = true ↔ m.c + m.β * m.E v ≤ m.stop w

/-- Every `v` has a greedy policy. -/
theorem exists_isGreedy (v : W → ℝ) : ∃ σ : Policy W, m.IsGreedy v σ := by
  classical
  exact ⟨fun w => decide (m.c + m.β * m.E v ≤ m.stop w), fun w => by simp⟩

/-- The reservation wage (1.30), p. 36: `w* = (1 − β) h*`. -/
noncomputable def reservationWage : ℝ := (1 - m.β) * m.hstar

/-- The optimal choice of §1.3.1.1 (p. 33): accept iff `w/(1 − β) ≥ h*`, equivalently iff
`w ≥ w*`. -/
theorem hstar_le_stop_iff (w : W) : m.hstar ≤ m.stop w ↔ m.reservationWage ≤ m.wage w := by
  rw [stop, reservationWage, le_div_iff₀ m.one_sub_β_pos, mul_comm]

/-- (1.30), p. 36: a policy is `v*`-greedy iff it accepts exactly the offers at or above the
reservation wage, `σ*(w) = 1{w ≥ w*}`. -/
theorem isGreedy_vstar_iff (σ : Policy W) :
    m.IsGreedy m.vstar σ ↔ ∀ w, σ w = true ↔ m.reservationWage ≤ m.wage w := by
  unfold IsGreedy
  refine forall_congr' fun w => ?_
  change (σ w = true ↔ m.hstar ≤ m.stop w) ↔ _
  rw [hstar_le_stop_iff]

end Model

end SargentStachurski.JobSearch
