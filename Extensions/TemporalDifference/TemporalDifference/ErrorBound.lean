/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TemporalDifference.Features

/-!
# How good is the TD fixed point?

Tsitsiklis and Van Roy (1997).

Let `V = r + βPV` be the true value. The best approximation in the span of the features for
`‖·‖_d` is the projection `ΠV = V_θ̂`, characterized by the normal equations
`⟨V_θ̂ − V, V_z⟩_d = 0` for all `z` (`exists_best_approx`, `best_approx`). The TD fixed point
`V_θ*` is instead the fixed point of `ΠT`: `h(θ*) = 0` says exactly that `TV_θ* − V_θ*` is
orthogonal to the features (`inner_meanField`).

* `tvr_bound`: `(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²`, i.e.
  `‖V_θ* − V‖_d ≤ ‖ΠV − V‖_d / √(1 − β²)`: TD learning is never much worse than the best linear
  approximation when `β` is not close to `1`, and it is exact when the value function lies in the
  span of the features. Tsitsiklis and Van Roy bound the error by `1/(1 − β)` times the
  projection error; the Pythagorean argument used here sharpens the factor to `1/√(1 − β²)`.
-/

open Finset

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dinner_add_left (d v w u : X → ℝ) :
    dinner d (fun x => v x + w x) u = dinner d v u + dinner d w u := by
  simp only [dinner, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

/-- `⟪z, h(θ)⟫ = ⟨TV_θ − V_θ, V_z⟩_d`. -/
theorem inner_meanField (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) (θ z : E) :
    inner ℝ z (meanField P d r β φ θ) =
      dinner d (fun x => r x + β * applyP P (vθ φ θ) x - vθ φ θ x) (vθ φ z) := by
  simp only [meanField, inner_sum, real_inner_smul_right, dinner]
  refine sum_congr rfl fun x _ => ?_
  have : inner ℝ z (φ x) = vθ φ z x := real_inner_comm _ _
  rw [this]

/-- Solutions of the normal equations are best approximations. -/
theorem best_approx {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) {φ : X → E} {V : X → ℝ} {θh : E}
    (hθh : ∀ z, dinner d (fun x => vθ φ θh x - V x) (vθ φ z) = 0) (θ : E) :
    dsq d (fun x => vθ φ θh x - V x) ≤ dsq d (fun x => vθ φ θ x - V x) := by
  have e : (fun x => vθ φ θ x - V x) = fun x => (vθ φ θh x - V x) + vθ φ (θ - θh) x := by
    funext x
    rw [vθ_sub]
    ring
  rw [e, dsq_add, hθh, mul_zero, add_zero]
  linarith [dsq_nonneg hd (vθ φ (θ - θh))]

/-- **The projection exists**: if `d > 0` and the features span `E`, the normal equations have a
solution. -/
theorem exists_best_approx [FiniteDimensional ℝ E] {d : X → ℝ} (hd : ∀ x, 0 < d x) {φ : X → E}
    (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) (V : X → ℝ) :
    ∃ θh, ∀ z, dinner d (fun x => vθ φ θh x - V x) (vθ φ z) = 0 := by
  obtain ⟨m, hm, hgram⟩ := exists_gram_lower hd hspan
  let G : E →ₗ[ℝ] E :=
    { toFun := fun z => ∑ x, (d x * vθ φ z x) • φ x
      map_add' := fun z w => by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [← add_smul]
        congr 1
        simp only [vθ, inner_add_right]
        ring
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, smul_sum, smul_smul]
        refine sum_congr rfl fun x _ => ?_
        congr 1
        simp only [vθ, real_inner_smul_right]
        ring }
  have hG : ∀ z w, inner ℝ w (G z) = dinner d (vθ φ z) (vθ φ w) := fun z w => by
    simp only [G, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, real_inner_smul_right, dinner]
    refine sum_congr rfl fun x _ => ?_
    have : inner ℝ w (φ x) = vθ φ w x := real_inner_comm _ _
    rw [this]
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h1 := hG z z
    rw [hz, inner_zero_right, dinner_self] at h1
    have h2 := hgram z
    have h3 : ‖z‖ ^ 2 ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos hm h]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))
  obtain ⟨θh, hθh⟩ := (LinearMap.injective_iff_surjective.1 hinj) (∑ x, (d x * V x) • φ x)
  refine ⟨θh, fun z => ?_⟩
  have h1 := hG θh z
  rw [hθh] at h1
  have h2 : inner ℝ z (∑ x, (d x * V x) • φ x) = dinner d V (vθ φ z) := by
    simp only [inner_sum, real_inner_smul_right, dinner]
    refine sum_congr rfl fun x _ => ?_
    have : inner ℝ z (φ x) = vθ φ z x := real_inner_comm _ _
    rw [this]
  have e : dinner d (fun x => vθ φ θh x - V x) (vθ φ z) =
      dinner d (vθ φ θh) (vθ φ z) - dinner d V (vθ φ z) := by
    simp only [dinner, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [e, ← h1, ← h2, sub_self]

/-- **The TD error bound** (after Tsitsiklis and Van Roy, 1997):
`(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²`. -/
theorem tvr_bound {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) {r : X → ℝ} {β : ℝ}
    {φ : X → E} {V : X → ℝ} (hV : ∀ x, V x = r x + β * applyP P V x) {θs : E}
    (hθs : meanField P d r β φ θs = 0) {θh : E}
    (hθh : ∀ z, dinner d (fun x => vθ φ θh x - V x) (vθ φ z) = 0) :
    (1 - β ^ 2) * dsq d (fun x => vθ φ θs x - V x) ≤ dsq d (fun x => vθ φ θh x - V x) := by
  set a : X → ℝ := fun x => vθ φ θh x - V x
  set s : X → ℝ := vθ φ (θs - θh)
  set e : X → ℝ := fun x => vθ φ θs x - V x
  have hs : ∀ x, s x = vθ φ θs x - vθ φ θh x := fun x => by simp [s, vθ_sub]
  have hes : e = fun x => s x + a x := funext fun x => by simp only [e, a, hs]; ring
  -- `TV_θ* − V_θ*` is orthogonal to the features
  have horth : ∀ z, dinner d (fun x => r x + β * applyP P (vθ φ θs) x - vθ φ θs x)
      (vθ φ z) = 0 := fun z => by
    rw [← inner_meanField, hθs, inner_zero_right]
  -- `w = TV_θ* − TV = βPe`
  set w : X → ℝ := fun x => β * applyP P e x
  have hw : ∀ x, w x - s x =
      (r x + β * applyP P (vθ φ θs) x - vθ φ θs x) + a x := fun x => by
    simp only [w, a, hs, e, applyP, mul_sub, sum_sub_distrib]
    rw [hV x]
    simp only [applyP]
    ring
  have hws : ∀ z, dinner d (fun x => w x - s x) (vθ φ z) = 0 := fun z => by
    rw [show (fun x => w x - s x) = fun x =>
      (r x + β * applyP P (vθ φ θs) x - vθ φ θs x) + a x from funext hw, dinner_add_left,
      horth, hθh, add_zero]
  -- Pythagoras twice
  have h1 : dsq d e = dsq d s + dsq d a := by
    rw [hes, dsq_add, dinner_comm, hθh, mul_zero, add_zero]
  have h2 : dsq d s ≤ dsq d w := by
    have e2 : w = fun x => s x + (w x - s x) := funext fun x => by ring
    have h3 := dsq_add d s (fun x => w x - s x)
    rw [← e2, dinner_comm, hws, mul_zero, add_zero] at h3
    rw [h3]
    linarith [dsq_nonneg hd (fun x => w x - s x)]
  have h4 : dsq d w ≤ β ^ 2 * dsq d e := by
    simp only [w]
    rw [dsq_smul]
    exact mul_le_mul_of_nonneg_left (dsq_applyP_le hP0 hP1 hd hstat e) (sq_nonneg β)
  nlinarith

end DPExtensions.TemporalDifference
