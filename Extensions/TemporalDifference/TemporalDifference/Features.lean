/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TemporalDifference.WeightedNorm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear value-function approximation and the TD fixed point

Tsitsiklis and Van Roy (1997); Sutton (1988).

Values are approximated by `V_θ(x) = ⟪φ(x), θ⟫` with features `φ : X → E` in a finite-dimensional
real inner product space. TD(0) moves `θ` along `φ(x)(r(x) + βV_θ(x') − V_θ(x))`, whose mean under
the stationary distribution `d` and the transitions `P` is the **mean field**
`h(θ) = ∑_x d(x)(r(x) + β(PV_θ)(x) − V_θ(x))φ(x)`.

* `exists_gram_lower`: if `d > 0` and the features span `E`, `‖V_z‖_d² ≥ m‖z‖²` for some `m > 0`.
* `inner_meanField_sub`, `meanField_lyapunov`: `⟪θ − θ', h(θ) − h(θ')⟫ ≤ −(1 − β)‖V_{θ−θ'}‖_d²`
  — the mean field is strongly monotone, although TD is not the gradient of any objective.
* `meanField_lipschitz`: `h` is Lipschitz.
* `exists_unique_fixedPoint`: the TD fixed point `h(θ*) = 0` exists and is unique.
-/

open Finset

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear approximation `V_θ(x) = ⟪φ(x), θ⟫`. -/
def vθ (φ : X → E) (θ : E) (x : X) : ℝ := inner ℝ (φ x) θ

omit [Fintype X] in
theorem vθ_sub (φ : X → E) (θ θ' : E) : vθ φ (θ - θ') = fun x => vθ φ θ x - vθ φ θ' x :=
  funext fun _ => inner_sub_right _ _ _

omit [Fintype X] in
theorem vθ_smul (φ : X → E) (c : ℝ) (θ : E) : vθ φ (c • θ) = fun x => c * vθ φ θ x :=
  funext fun _ => real_inner_smul_right _ _ _

/-- With `d > 0` and spanning features, `‖V_z‖_d² > 0` for `z ≠ 0`. -/
theorem dsq_vθ_pos {d : X → ℝ} (hd : ∀ x, 0 < d x) {φ : X → E}
    (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) {z : E} (hz : z ≠ 0) :
    0 < dsq d (vθ φ z) := by
  refine lt_of_le_of_ne (dsq_nonneg (fun x => (hd x).le) _) fun h => hz (hspan z fun x => ?_)
  have h0 := (sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (hd x).le (sq_nonneg (vθ φ z x))).1 h.symm x (mem_univ x)
  have : vθ φ z x ^ 2 = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (hd x).ne'
    · exact h1
  exact pow_eq_zero_iff two_ne_zero |>.1 this

/-- **The Gram form is coercive**: `‖V_z‖_d² ≥ m‖z‖²` with `m > 0`. -/
theorem exists_gram_lower [FiniteDimensional ℝ E] {d : X → ℝ} (hd : ∀ x, 0 < d x)
    {φ : X → E} (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) :
    ∃ m > 0, ∀ z, m * ‖z‖ ^ 2 ≤ dsq d (vθ φ z) := by
  have hq0 : ∀ z, 0 ≤ dsq d (vθ φ z) := fun z => dsq_nonneg (fun x => (hd x).le) _
  by_cases hE : ∃ z : E, z ≠ 0
  · obtain ⟨z1, hz1⟩ := hE
    set q : E → ℝ := fun z => dsq d (vθ φ z)
    have hqc : Continuous q :=
      continuous_finsetSum _ fun x _ =>
        continuous_const.mul ((continuous_const.inner continuous_id).pow 2)
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      ⟨‖z1‖⁻¹ • z1, by simp [norm_smul, norm_ne_zero_iff.2 hz1]⟩
    obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hqc.continuousOn
    have hz0ne : z0 ≠ 0 := by
      intro h
      simp [h] at hz0
    refine ⟨q z0, dsq_vθ_pos hd hspan hz0ne, fun z => ?_⟩
    rcases eq_or_ne z 0 with h | h
    · simp [h, hq0]
    · have hw : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, norm_ne_zero_iff.2 h]
      have h1 := hmin hw
      have e : q z = ‖z‖ ^ 2 * q (‖z‖⁻¹ • z) := by
        simp only [q, vθ_smul, dsq_smul]
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_pow, one_mul]
      change q z0 * ‖z‖ ^ 2 ≤ q z
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · push Not at hE
    exact ⟨1, one_pos, fun z => by simp [hE z, hq0]⟩

/-- The mean field of TD(0), `h(θ) = ∑_x d(x)(r(x) + β(PV_θ)(x) − V_θ(x))φ(x)`. -/
noncomputable def meanField (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) (θ : E) : E :=
  ∑ x, (d x * (r x + β * applyP P (vθ φ θ) x - vθ φ θ x)) • φ x

/-- The linear part of the mean field. -/
noncomputable def meanFieldLin (P : X → X → ℝ) (d : X → ℝ) (β : ℝ) (φ : X → E) : E →ₗ[ℝ] E where
  toFun z := ∑ x, (d x * (β * applyP P (vθ φ z) x - vθ φ z x)) • φ x
  map_add' z w := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← add_smul]
    congr 1
    simp only [vθ, applyP, inner_add_right, mul_add, sum_add_distrib]
    ring
  map_smul' c z := by
    simp only [RingHom.id_apply, smul_sum, smul_smul]
    refine sum_congr rfl fun x _ => ?_
    congr 1
    simp only [vθ, applyP, real_inner_smul_right]
    rw [show ∑ i, P x i * (c * inner ℝ (φ i) z) = c * ∑ i, P x i * inner ℝ (φ i) z by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring]
    ring

theorem meanField_sub (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) (θ θ' : E) :
    meanField P d r β φ θ - meanField P d r β φ θ' = meanFieldLin P d β φ (θ - θ') := by
  simp only [meanField, meanFieldLin, LinearMap.coe_mk, AddHom.coe_mk, ← sum_sub_distrib,
    ← sub_smul]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  simp only [vθ, applyP, inner_sub_right, mul_sub, sum_sub_distrib]
  ring

theorem inner_meanFieldLin (P : X → X → ℝ) (d : X → ℝ) (β : ℝ) (φ : X → E) (z : E) :
    inner ℝ z (meanFieldLin P d β φ z) =
      β * dinner d (vθ φ z) (applyP P (vθ φ z)) - dsq d (vθ φ z) := by
  simp only [meanFieldLin, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, real_inner_smul_right,
    dinner, dsq, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  have : inner ℝ z (φ x) = vθ φ z x := real_inner_comm _ _
  rw [this]
  ring

/-- **The TD mean field is strongly monotone**:
`⟪θ − θ', h(θ) − h(θ')⟫ ≤ −(1 − β)‖V_{θ−θ'}‖_d²`. -/
theorem meanField_lyapunov {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x)
    (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (φ : X → E)
    (θ θ' : E) :
    inner ℝ (θ - θ') (meanField P d r β φ θ - meanField P d r β φ θ') ≤
      -(1 - β) * dsq d (vθ φ (θ - θ')) := by
  rw [meanField_sub, inner_meanFieldLin]
  have := dinner_applyP_le hP0 hP1 hd hstat (vθ φ (θ - θ'))
  nlinarith

/-- **The mean field is Lipschitz.** -/
theorem meanField_lipschitz {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (r : X → ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (φ : X → E) (θ θ' : E) :
    ‖meanField P d r β φ θ - meanField P d r β φ θ'‖ ≤
      ((β + 1) * (∑ y, ‖φ y‖) * (∑ y, ‖φ y‖) * ∑ x, d x) * ‖θ - θ'‖ := by
  rw [meanField_sub]
  set z := θ - θ'
  set Φ := ∑ y, ‖φ y‖
  have hφ : ∀ y, ‖φ y‖ ≤ Φ := fun y =>
    single_le_sum (f := fun y => ‖φ y‖) (fun y _ => norm_nonneg _) (mem_univ y)
  have hu : ∀ y, |vθ φ z y| ≤ Φ * ‖z‖ := fun y =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hφ y) (norm_nonneg _))
  have hPu : ∀ x, |applyP P (vθ φ z) x| ≤ Φ * ‖z‖ := fun x => by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ y, |P x y * vθ φ z y| ≤ ∑ y, P x y * (Φ * ‖z‖) := sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (hP0 x y)]
          exact mul_le_mul_of_nonneg_left (hu y) (hP0 x y)
      _ = Φ * ‖z‖ := by rw [← sum_mul, hP1 x, one_mul]
  simp only [meanFieldLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖(d x * (β * applyP P (vθ φ z) x - vθ φ z x)) • φ x‖
      ≤ ∑ x, d x * ((β + 1) * (Φ * ‖z‖)) * Φ := sum_le_sum fun x _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd x)]
        refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (hd x)) (hφ x) (norm_nonneg _)
          (mul_nonneg (hd x) (by positivity))
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hβ0]
        have h1 := mul_le_mul_of_nonneg_left (hPu x) hβ0
        have h2 := hu x
        linarith
    _ = ((β + 1) * Φ * Φ * ∑ x, d x) * ‖z‖ := by
        rw [← sum_mul, ← sum_mul]
        simp only [sum_mul, mul_sum]
        exact sum_congr rfl fun x _ => by ring

/-- **The TD fixed point exists and is unique**: if `d > 0`, the features span `E` and `β < 1`,
there is exactly one `θ*` with `h(θ*) = 0`. -/
theorem exists_unique_fixedPoint [FiniteDimensional ℝ E] {P : X → X → ℝ}
    (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 < d x)
    (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {φ : X → E} (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) :
    ∃! θs, meanField P d r β φ θs = 0 := by
  obtain ⟨m, hm, hgram⟩ := exists_gram_lower hd hspan
  have hd0 : ∀ x, 0 ≤ d x := fun x => (hd x).le
  set A := meanFieldLin P d β φ
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h1 := meanField_lyapunov hP0 hP1 hd0 hstat r hβ0 φ z 0
    rw [meanField_sub, sub_zero] at h1
    change inner ℝ z (A z) ≤ _ at h1
    rw [hz, inner_zero_right] at h1
    have h2 := hgram z
    have h4 : dsq d (vθ φ z) ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos (sub_pos.2 hβ1) h]
    have h3 : ‖z‖ ^ 2 ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos hm h]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))
  obtain ⟨θs, hθs⟩ := (LinearMap.injective_iff_surjective.1 hinj) (-meanField P d r β φ 0)
  have hfix : meanField P d r β φ θs = 0 := by
    have := meanField_sub P d r β φ θs 0
    rw [sub_zero] at this
    change _ = A θs at this
    rw [hθs] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this, neg_add_cancel]
  refine ⟨θs, hfix, fun θ hθ => hinj ?_⟩
  have h1 := meanField_sub P d r β φ θ θs
  rw [hθ, hfix, sub_zero, map_sub] at h1
  exact sub_eq_zero.1 h1.symm

end DPExtensions.TemporalDifference
