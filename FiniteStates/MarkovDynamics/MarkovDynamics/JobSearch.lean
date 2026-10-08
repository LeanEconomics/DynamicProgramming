/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.GeometricSums
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Job search with Markov wages and with separation

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.3 (pp. 97–104).

Wages are `P`-Markov on a finite set `W ⊂ ℝ₊`. The Bellman operator (3.23)
`Tv(w) = max{w/(1 − β), c + β ∑ v(w')P(w, w')}` is an order-preserving
self-map of `V = ℝ^W₊` and a contraction of modulus `β` in the supremum norm
(Exercise 3.3.1), so the value function `v*` is its unique fixed point in `V`
and value function iteration converges. Lemma 3.3.1: `v*` is increasing when
`P` is monotone increasing. The continuation value `h* = c + βPv*` satisfies
the recursion of Exercise 3.3.3 and is the unique fixed point in `V` of the
operator `Q` of (3.24), itself an order-preserving `β`-contraction
(Exercise 3.3.4); the optimal policy is `1{w/(1 − β) ≥ h*(w)}`.

With separation at rate `α`, (3.25)–(3.26) reduce to (3.27)–(3.28); the
operator of (3.28) is the upper envelope of two contractions of moduli
`αβ/(1 − β(1 − α))` and `β` (Lemma 2.2.3), so `v_u*` exists uniquely in `V`,
iteration converges, and the pair `(v_u*, v_e*)` is the unique solution of
(3.25)–(3.26) (Exercise 3.3.5). Exercises 3.3.2 and 3.3.6 are discussion and
computation.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.MarkovDynamics

/-- The job search model with Markov wages (§3.3.1): a finite set `W` of offers with nonnegative
wages, a Markov matrix `P`, compensation `c > 0` and discount factor `β ∈ (0, 1)`. -/
structure MarkovJobSearch (W : Type*) [Fintype W] where
  wage : W → ℝ
  wage_nonneg : ∀ w, 0 ≤ wage w
  P : Matrix W W ℝ
  P_markov : IsMarkov P
  c : ℝ
  c_pos : 0 < c
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

namespace MarkovJobSearch

variable {W : Type*} [Fintype W] (m : MarkovJobSearch W)

/-- The candidate value functions `V = ℝ^W₊`. -/
def V : Set (W → ℝ) := {v | ∀ w, 0 ≤ v w}

omit [Fintype W] in
theorem isClosed_V : IsClosed (V : Set (W → ℝ)) := by
  have : (V : Set (W → ℝ)) = ⋂ w, {v | 0 ≤ v w} := by ext; simp [V]
  rw [this]
  exact isClosed_iInter fun w => isClosed_le continuous_const (continuous_apply w)

omit [Fintype W] in
theorem zero_mem_V : (0 : W → ℝ) ∈ V := fun _ => le_rfl

theorem one_sub_β_pos : 0 < 1 - m.β := by linarith [m.β_lt_one]

/-- The stopping value `e(w) = w/(1 − β)`. -/
noncomputable def e (w : W) : ℝ := m.wage w / (1 - m.β)

theorem e_nonneg (w : W) : 0 ≤ m.e w := div_nonneg (m.wage_nonneg w) m.one_sub_β_pos.le

/-- `Pv ≥ 0` for `v ≥ 0`. -/
theorem mulVec_nonneg {v : W → ℝ} (hv : v ∈ V) (w : W) : 0 ≤ (m.P *ᵥ v) w := by
  have := m.P_markov.mulVec_le_mulVec (f := 0) (g := v) hv w
  simpa using this

/-- The Bellman operator (p. 98): `Tv(w) = max{w/(1 − β), c + β(Pv)(w)}`. -/
noncomputable def T (v : W → ℝ) : W → ℝ := fun w => max (m.e w) (m.c + m.β * (m.P *ᵥ v) w)

/-- Exercise 3.3.1 (i), p. 98: `T` maps `V` into `V`. -/
theorem T_mapsTo : MapsTo m.T V V := fun _ hv w =>
  le_max_of_le_right (add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg hv w)))

/-- Exercise 3.3.1 (i), p. 98: `T` is order preserving. -/
theorem T_monotone : Monotone m.T := by
  intro v v' hvv' w
  exact max_le_max le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (m.P_markov.mulVec_le_mulVec hvv' w) m.β_pos.le))

/-- Pointwise estimate: `|Tv(w) − Tv'(w)| ≤ β‖v − v'‖`. -/
theorem abs_T_sub_le (v v' : W → ℝ) (w : W) : |m.T v w - m.T v' w| ≤ m.β * ‖v - v'‖ := by
  unfold T
  rw [max_comm (m.e w), max_comm (m.e w)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg m.β_pos.le]
  have := m.P_markov.abs_mulVec_le (v - v') w
  rw [mulVec_sub, Pi.sub_apply] at this
  exact mul_le_mul_of_nonneg_left this m.β_pos.le

/-- Exercise 3.3.1 (ii), p. 98: `T` is a contraction of modulus `β` on `V` in the supremum norm. -/
theorem isContractionOn_T : IsContractionOn m.T V m.β where
  mapsTo := m.T_mapsTo
  nonneg := m.β_pos.le
  lt_one := m.β_lt_one
  norm_sub_le u _ v _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg m.β_pos.le (norm_nonneg _))]
    intro w
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact m.abs_T_sub_le u v w

/-- The value function `v*`: the fixed point of `T` in `V` given by Banach's theorem. -/
noncomputable def vstar : W → ℝ :=
  Classical.choose (m.isContractionOn_T.exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)

theorem vstar_mem : m.vstar ∈ V :=
  (Classical.choose_spec (m.isContractionOn_T.exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).1

theorem isFixedPt_vstar : IsFixedPt m.T m.vstar :=
  (Classical.choose_spec (m.isContractionOn_T.exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).2

/-- The Bellman equation (3.23), p. 97. -/
theorem bellman_equation (w : W) :
    m.vstar w = max (m.wage w / (1 - m.β)) (m.c + m.β * ∑ w', m.vstar w' * m.P w w') := by
  have := congrFun m.isFixedPt_vstar.eq w
  rw [← this]
  unfold T e
  rw [mulVec_apply_eq]

/-- `v*` is the only fixed point of `T` in `V` (p. 98). -/
theorem eq_vstar_of_isFixedPt {v : W → ℝ} (hv : v ∈ V) (hfix : IsFixedPt m.T v) : v = m.vstar :=
  m.isContractionOn_T.fixedPt_unique hv m.vstar_mem hfix m.isFixedPt_vstar

/-- Value function iteration (p. 98): `Tᵏv → v*` for every `v ∈ V`, at rate `βᵏ`. -/
theorem tendsto_iterate_T {v : W → ℝ} (hv : v ∈ V) :
    Tendsto (fun k : ℕ => m.T^[k] v) atTop (𝓝 m.vstar) :=
  m.isContractionOn_T.tendsto_iterate_fixedPt hv m.vstar_mem m.isFixedPt_vstar

theorem norm_iterate_T_sub_vstar_le {v : W → ℝ} (hv : v ∈ V) (k : ℕ) :
    ‖m.T^[k] v - m.vstar‖ ≤ m.β ^ k * ‖v - m.vstar‖ :=
  m.isContractionOn_T.norm_iterate_sub_fixedPt_le hv m.vstar_mem m.isFixedPt_vstar k

/-- A `v`-greedy policy (p. 98): accept iff `w/(1 − β) ≥ c + β(Pv)(w)`. -/
def IsGreedy (v : W → ℝ) (σ : W → Bool) : Prop :=
  ∀ w, σ w = true ↔ m.c + m.β * (m.P *ᵥ v) w ≤ m.e w

/-- **Lemma 3.3.1** (p. 98): `v*` is increasing on `(W, ≤)` whenever the wage is increasing and `P`
is monotone increasing. The increasing functions in `V` form a closed set that `T` maps into
itself, so the fixed point lies in it (Vol. 1, Ex 1.2.18). -/
theorem monotone_vstar [PartialOrder W] (hw : Monotone m.wage) (hP : MonotoneIncreasing m.P) :
    Monotone m.vstar := by
  set I : Set (W → ℝ) := V ∩ {v | Monotone v} with hI
  have hclosed : IsClosed I := isClosed_V.inter (isClosed_monotone W)
  have hmaps : ∀ v ∈ I, m.T v ∈ I := by
    rintro v ⟨hvV, hvm⟩
    refine ⟨m.T_mapsTo hvV, fun w w' hww' => ?_⟩
    have h1 : m.e w ≤ m.e w' := div_le_div_of_nonneg_right (hw hww') m.one_sub_β_pos.le
    have h2 := (monotoneIncreasing_iff m.P).1 hP v hvm hww'
    exact max_le_max h1 (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 m.β_pos.le))
  have hiter : ∀ k, m.T^[k] 0 ∈ I := by
    intro k
    induction k with
    | zero => exact ⟨zero_mem_V, fun _ _ _ => le_rfl⟩
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact (hclosed.mem_of_tendsto (m.tendsto_iterate_T zero_mem_V)
    (Eventually.of_forall hiter)).2

/-! ### Continuation values (§3.3.1.2) -/

/-- The continuation value function `h*(w) = c + β ∑ v*(w')P(w, w')` (p. 100). -/
noncomputable def hstar : W → ℝ := fun w => m.c + m.β * (m.P *ᵥ m.vstar) w

theorem hstar_mem : m.hstar ∈ V := fun w =>
  add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg m.vstar_mem w))

/-- `v* = e ∨ h*`: the value is the larger of stopping and continuing. -/
theorem vstar_eq_max (w : W) : m.vstar w = max (m.e w) (m.hstar w) :=
  (congrFun m.isFixedPt_vstar.eq w).symm

/-- The `v*`-greedy policy accepts iff the stopping value is at least the continuation value. -/
theorem isGreedy_vstar : m.IsGreedy m.vstar fun w => decide (m.hstar w ≤ m.e w) := fun w => by
  rw [decide_eq_true_iff]
  rfl

/-- The operator `Q` of (3.24): `(Qh)(w) = c + β ∑ max{w'/(1 − β), h(w')} P(w, w')`. -/
noncomputable def Q (h : W → ℝ) : W → ℝ := fun w =>
  m.c + m.β * (m.P *ᵥ fun w' => max (m.e w') (h w')) w

/-- Exercise 3.3.3 (p. 100): `h*` satisfies `h*(w) = c + β ∑ max{w'/(1 − β), h*(w')} P(w, w')`,
i.e. `h*` is a fixed point of `Q`. -/
theorem isFixedPt_hstar : IsFixedPt m.Q m.hstar := by
  funext w
  unfold Q
  have : (fun w' => max (m.e w') (m.hstar w')) = m.vstar :=
    funext fun w' => (m.vstar_eq_max w').symm
  rw [this]
  rfl

/-- Exercise 3.3.4 (a), p. 101: `Q` maps `V` into `V`. -/
theorem Q_mapsTo : MapsTo m.Q V V := fun h _ w => by
  unfold Q
  refine add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg (fun w' => ?_) w))
  exact le_max_of_le_left (m.e_nonneg w')

/-- Exercise 3.3.4 (a), p. 101: `Q` is order preserving. -/
theorem Q_monotone : Monotone m.Q := by
  intro h h' hhh' w
  unfold Q
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (m.P_markov.mulVec_le_mulVec
    (fun w' => max_le_max le_rfl (hhh' w')) w) m.β_pos.le)

/-- Exercise 3.3.4 (b), p. 101: `Q` is a contraction of modulus `β` on `V` in the supremum
norm. -/
theorem isContractionOn_Q : IsContractionOn m.Q V m.β where
  mapsTo := m.Q_mapsTo
  nonneg := m.β_pos.le
  lt_one := m.β_lt_one
  norm_sub_le h _ h' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg m.β_pos.le (norm_nonneg _))]
    intro w
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold Q
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg m.β_pos.le]
    have hmv := m.P_markov.abs_mulVec_le ((fun w' => max (m.e w') (h w')) -
      fun w' => max (m.e w') (h' w')) w
    rw [mulVec_sub, Pi.sub_apply] at hmv
    refine mul_le_mul_of_nonneg_left (hmv.trans ?_) m.β_pos.le
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro w'
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [max_comm (m.e w') (h w'), max_comm (m.e w') (h' w')]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := norm_le_pi_norm (h - h') w'
    simpa [Real.norm_eq_abs] using this

/-- `h*` is the unique fixed point of `Q` in `V`, and iterating `Q` from any `h ∈ V` converges to
it (p. 101). -/
theorem eq_hstar_of_isFixedPt {h : W → ℝ} (hh : h ∈ V) (hfix : IsFixedPt m.Q h) : h = m.hstar :=
  m.isContractionOn_Q.fixedPt_unique hh m.hstar_mem hfix m.isFixedPt_hstar

theorem tendsto_iterate_Q {h : W → ℝ} (hh : h ∈ V) :
    Tendsto (fun k : ℕ => m.Q^[k] h) atTop (𝓝 m.hstar) :=
  m.isContractionOn_Q.tendsto_iterate_fixedPt hh m.hstar_mem m.isFixedPt_hstar

/-! ### Job search with separation (§3.3.2) -/

/-- The denominator `1 − β(1 − α)` of (3.27) is positive for `α ≥ 0`. -/
theorem denom_pos {α : ℝ} (hα0 : 0 ≤ α) : 0 < 1 - m.β * (1 - α) := by
  have := m.β_pos; have := m.β_lt_one
  nlinarith

/-- The modulus `αβ/(1 − β(1 − α))` of the stopping branch of (3.28) is below one. -/
theorem sep_modulus_lt_one {α : ℝ} (hα0 : 0 ≤ α) :
    α * m.β / (1 - m.β * (1 - α)) < 1 := by
  rw [div_lt_one (m.denom_pos hα0)]
  have := m.β_lt_one
  nlinarith [m.β_pos]

theorem sep_modulus_nonneg {α : ℝ} (hα0 : 0 ≤ α) :
    0 ≤ α * m.β / (1 - m.β * (1 - α)) :=
  div_nonneg (mul_nonneg hα0 m.β_pos.le) (m.denom_pos hα0).le

/-- The employed worker's value (3.27) given the unemployed value `v`:
`v_e(w) = (w + αβ(Pv)(w)) / (1 − β(1 − α))`. -/
noncomputable def employedValue (α : ℝ) (v : W → ℝ) : W → ℝ := fun w =>
  (m.wage w + α * m.β * (m.P *ᵥ v) w) / (1 - m.β * (1 - α))

/-- The operator of (3.28): `v ↦ max{v_e(v), c + βPv}`. -/
noncomputable def S (α : ℝ) (v : W → ℝ) : W → ℝ := fun w =>
  max (m.employedValue α v w) (m.c + m.β * (m.P *ᵥ v) w)

/-- (3.26) ⟺ (3.27): given `v_u`, the equation `v_e(w) = w + β[α(Pv_u)(w) + (1 − α)v_e(w)]` has
the unique solution `v_e = employedValue α v_u`. -/
theorem employed_recursion_iff {α : ℝ} (hα0 : 0 ≤ α) (vu ve : W → ℝ) :
    (∀ w, ve w = m.wage w + m.β * (α * (m.P *ᵥ vu) w + (1 - α) * ve w)) ↔
      ve = m.employedValue α vu := by
  have hD := m.denom_pos hα0
  constructor
  · intro h
    funext w
    unfold employedValue
    rw [eq_div_iff hD.ne']
    linear_combination h w
  · intro h w
    rw [h]
    unfold employedValue
    field_simp
    ring

/-- Substituting (3.27) into (3.25) gives (3.28): the pair `(v_u, v_e)` solves (3.25)–(3.26) iff
`v_u` is a fixed point of `S` and `v_e = employedValue α v_u`. -/
theorem system_iff {α : ℝ} (hα0 : 0 ≤ α) (vu ve : W → ℝ) :
    ((∀ w, vu w = max (ve w) (m.c + m.β * (m.P *ᵥ vu) w)) ∧
      ∀ w, ve w = m.wage w + m.β * (α * (m.P *ᵥ vu) w + (1 - α) * ve w)) ↔
      IsFixedPt (m.S α) vu ∧ ve = m.employedValue α vu := by
  rw [m.employed_recursion_iff hα0]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨funext fun w => ?_, h2⟩
    rw [S, ← h2]
    exact (h1 w).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun w => ?_, h2⟩
    rw [h2]
    exact (congrFun h1 w).symm

/-- `S` maps `V` into `V`. -/
theorem S_mapsTo (α : ℝ) : MapsTo (m.S α) V V := fun _ hv w =>
  le_max_of_le_right (add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg hv w)))

/-- Exercise 3.3.5 (p. 102): `S` is a contraction on `V` with modulus
`max{αβ/(1 − β(1 − α)), β} < 1`, as the upper envelope of two contractions (Vol. 1,
Lemma 2.2.3). -/
theorem isContractionOn_S {α : ℝ} (hα0 : 0 ≤ α) :
    IsContractionOn (m.S α) V (max (α * m.β / (1 - m.β * (1 - α))) m.β) where
  mapsTo := m.S_mapsTo α
  nonneg := le_max_of_le_right m.β_pos.le
  lt_one := max_lt (m.sep_modulus_lt_one hα0) m.β_lt_one
  norm_sub_le u _ v _ := by
    have hD := m.denom_pos hα0
    have hL0 : 0 ≤ max (α * m.β / (1 - m.β * (1 - α))) m.β := le_max_of_le_right m.β_pos.le
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hL0 (norm_nonneg _))]
    intro w
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold S employedValue
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · have hmv := m.P_markov.abs_mulVec_le (u - v) w
      rw [mulVec_sub, Pi.sub_apply] at hmv
      rw [← sub_div, add_sub_add_left_eq_sub, ← mul_sub, abs_div, abs_mul,
        abs_of_pos hD, abs_of_nonneg (mul_nonneg hα0 m.β_pos.le), mul_div_right_comm]
      exact mul_le_mul (le_max_left _ _) hmv (abs_nonneg _) hL0
    · have hmv := m.P_markov.abs_mulVec_le (u - v) w
      rw [mulVec_sub, Pi.sub_apply] at hmv
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg m.β_pos.le]
      exact mul_le_mul (le_max_right _ _) hmv (abs_nonneg _) hL0

/-- The unemployed worker's value `v_u*` with separation: the fixed point of `S` in `V`. -/
noncomputable def vuStar {α : ℝ} (hα0 : 0 ≤ α) : W → ℝ :=
  Classical.choose ((m.isContractionOn_S hα0).exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)

theorem vuStar_mem {α : ℝ} (hα0 : 0 ≤ α) : m.vuStar hα0 ∈ V :=
  (Classical.choose_spec
    ((m.isContractionOn_S hα0).exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).1

theorem isFixedPt_vuStar {α : ℝ} (hα0 : 0 ≤ α) :
    IsFixedPt (m.S α) (m.vuStar hα0) :=
  (Classical.choose_spec
    ((m.isContractionOn_S hα0).exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).2

/-- Exercise 3.3.5 (p. 102): (3.28) has exactly one solution in `V`. -/
theorem eq_vuStar_of_isFixedPt {α : ℝ} (hα0 : 0 ≤ α) {v : W → ℝ} (hv : v ∈ V)
    (hfix : IsFixedPt (m.S α) v) : v = m.vuStar hα0 :=
  (m.isContractionOn_S hα0).fixedPt_unique hv (m.vuStar_mem hα0) hfix
    (m.isFixedPt_vuStar hα0)

/-- Exercise 3.3.5 (p. 102), the convergent method: iterate `S` from any `v ∈ V` to obtain `v_u*`,
then read off `v_e*` from (3.27). -/
theorem tendsto_iterate_S {α : ℝ} (hα0 : 0 ≤ α) {v : W → ℝ} (hv : v ∈ V) :
    Tendsto (fun k : ℕ => (m.S α)^[k] v) atTop (𝓝 (m.vuStar hα0)) :=
  (m.isContractionOn_S hα0).tendsto_iterate_fixedPt hv (m.vuStar_mem hα0)
    (m.isFixedPt_vuStar hα0)

/-- The employed worker's value `v_e*`, (3.27). -/
noncomputable def veStar {α : ℝ} (hα0 : 0 ≤ α) : W → ℝ :=
  m.employedValue α (m.vuStar hα0)

/-- The claim of p. 102: the system (3.25)–(3.26) has the unique solution `(v_u*, v_e*)` in
`V × V`. -/
theorem system_unique {α : ℝ} (hα0 : 0 ≤ α) :
    ((∀ w, m.vuStar hα0 w =
        max (m.veStar hα0 w) (m.c + m.β * (m.P *ᵥ m.vuStar hα0) w)) ∧
      ∀ w, m.veStar hα0 w = m.wage w + m.β * (α * (m.P *ᵥ m.vuStar hα0) w +
        (1 - α) * m.veStar hα0 w)) ∧
    ∀ vu ve : W → ℝ, vu ∈ V →
      (∀ w, vu w = max (ve w) (m.c + m.β * (m.P *ᵥ vu) w)) →
      (∀ w, ve w = m.wage w + m.β * (α * (m.P *ᵥ vu) w + (1 - α) * ve w)) →
      vu = m.vuStar hα0 ∧ ve = m.veStar hα0 := by
  refine ⟨(m.system_iff hα0 _ _).2 ⟨m.isFixedPt_vuStar hα0, rfl⟩, fun vu ve hvu h1 h2 => ?_⟩
  obtain ⟨hfix, hve⟩ := (m.system_iff hα0 vu ve).1 ⟨h1, h2⟩
  have huu := m.eq_vuStar_of_isFixedPt hα0 hvu hfix
  exact ⟨huu, by rw [hve, huu]; rfl⟩

/-- `v_e* ∈ V`: the employed value is nonnegative. -/
theorem veStar_mem {α : ℝ} (hα0 : 0 ≤ α) : m.veStar hα0 ∈ V := fun w =>
  div_nonneg (add_nonneg (m.wage_nonneg w) (mul_nonneg (mul_nonneg hα0 m.β_pos.le)
    (m.mulVec_nonneg (m.vuStar_mem hα0) w))) (m.denom_pos hα0).le

/-- The stopping value `s*` and continuation value `h*_e` of p. 102; `v_u* = s* ∨ h*_e`. -/
theorem vuStar_eq_max {α : ℝ} (hα0 : 0 ≤ α) (w : W) :
    m.vuStar hα0 w =
      max (m.veStar hα0 w) (m.c + m.β * (m.P *ᵥ m.vuStar hα0) w) :=
  (congrFun (m.isFixedPt_vuStar hα0).eq w).symm

end MarkovJobSearch

end SargentStachurski.MarkovDynamics
