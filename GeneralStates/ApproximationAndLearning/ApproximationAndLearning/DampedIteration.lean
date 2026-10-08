/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.Real

/-!
# Damped iteration and the asset pricing example

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.3.1 and §9.1.3.4
(pp. 304–308).

* (9.13) and **Lemma 9.1.7**: if `T` is a contraction of modulus `β` on a convex set `Θ`, the
  damped map `Fθ = θ + α(Tθ − θ)` is a self-map of `Θ` and a contraction of modulus
  `1 − α + αβ < 1` with the same fixed points; damped iteration converges geometrically.
  Convexity is needed for `F` to map `Θ` into itself (`lemma_9_1_7_needs_convex`).
* §9.1.3.4: the asset pricing operator `(Tv)(x) = β ∑_{x'} [v(x') + d(x')]P(x, x')`.
  **Exercise 9.1.1**: `T` is a contraction of modulus `β` on `(ℝ^X, ‖·‖∞)`; it is order
  preserving; its fixed point is `v* = (I − K)⁻¹Kd`, `K = βP`. The sampled operator `T̂`
  is unbiased, `𝔼[(T̂v)(x)] = (Tv)(x)`, the update (9.15) is the Robbins–Monro rule (9.14) with
  `W = T̂v − Tv`, and the noise obeys the bounds of footnote 1 (condition (ii) of
  Theorem 9.1.8).
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The damped map `Fθ = θ + α(Tθ − θ)` (9.13). -/
def damped (T : E → E) (α : ℝ) (θ : E) : E := θ + α • (T θ - θ)

theorem damped_eq (T : E → E) (α : ℝ) (θ : E) :
    damped T α θ = (1 - α) • θ + α • T θ := by
  unfold damped
  rw [smul_sub, sub_smul, one_smul]
  abel

/-- **Lemma 9.1.7** (p. 304): if `T` maps the convex set `Θ` into itself and is a contraction of
modulus `β` there, then for `α ∈ (0, 1]` the damped map `F` maps `Θ` into itself, is a
contraction of modulus `1 − α + αβ < 1`, and has the same fixed points as `T`. -/
theorem lemma_9_1_7 {T : E → E} {Θ : Set E} (hΘ : Convex ℝ Θ) (hT : MapsTo T Θ Θ) {β : ℝ}
    (hβ1 : β < 1) (hc : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, ‖T θ - T θ'‖ ≤ β * ‖θ - θ'‖) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MapsTo (damped T α) Θ Θ ∧
      (∀ θ ∈ Θ, ∀ θ' ∈ Θ, ‖damped T α θ - damped T α θ'‖ ≤ (1 - α + α * β) * ‖θ - θ'‖) ∧
      1 - α + α * β < 1 ∧ ∀ θ, damped T α θ = θ ↔ T θ = θ := by
  refine ⟨fun θ hθ => ?_, fun θ hθ θ' hθ' => ?_, by nlinarith, fun θ => ?_⟩
  · rw [damped_eq]
    exact hΘ hθ (hT hθ) (by linarith) hα0.le (by ring)
  · rw [damped_eq, damped_eq]
    have e : (1 - α) • θ + α • T θ - ((1 - α) • θ' + α • T θ') =
        (1 - α) • (θ - θ') + α • (T θ - T θ') := by
      simp only [smul_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hα0.le]
    nlinarith [hc θ hθ θ' hθ', norm_nonneg (θ - θ')]
  · unfold damped
    constructor
    · intro h
      have h1 : α • (T θ - θ) = 0 := by
        have := congrArg (· - θ) h
        simpa using this
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hα0.ne'
      · exact sub_eq_zero.1 h2
    · intro h
      rw [h, sub_self, smul_zero, add_zero]

/-- Damped iteration converges geometrically to the fixed point `θ̄ ∈ Θ` of `T`:
`‖Fᵏθ − θ̄‖ ≤ (1 − α + αβ)ᵏ ‖θ − θ̄‖`. -/
theorem damped_iterate_le {T : E → E} {Θ : Set E} (hΘ : Convex ℝ Θ) (hT : MapsTo T Θ Θ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, ‖T θ - T θ'‖ ≤ β * ‖θ - θ'‖) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {θbar : E} (hbar : θbar ∈ Θ) (hfix : T θbar = θbar)
    {θ : E} (hθ : θ ∈ Θ) (k : ℕ) :
    ‖(damped T α)^[k] θ - θbar‖ ≤ (1 - α + α * β) ^ k * ‖θ - θbar‖ := by
  obtain ⟨hmaps, hcon, -, hfixd⟩ := lemma_9_1_7 hΘ hT hβ1 hc hα0 hα1
  have hq : 0 ≤ 1 - α + α * β := by nlinarith [mul_nonneg hα0.le hβ0]
  have hF : damped T α θbar = θbar := (hfixd θbar).2 hfix
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', pow_succ]
    have hk := hmaps.iterate k hθ
    calc ‖damped T α ((damped T α)^[k] θ) - θbar‖
        = ‖damped T α ((damped T α)^[k] θ) - damped T α θbar‖ := by rw [hF]
      _ ≤ (1 - α + α * β) * ‖(damped T α)^[k] θ - θbar‖ := hcon _ hk _ hbar
      _ ≤ (1 - α + α * β) * ((1 - α + α * β) ^ k * ‖θ - θbar‖) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = _ := by ring

/-- Convexity is needed in Lemma 9.1.7: on `Θ = {0, 1} ⊂ ℝ` the constant map `T ≡ 1` is a
contraction of modulus `0` mapping `Θ` into itself, yet the damped map sends `0` to `α ∉ Θ`
for `α ∈ (0, 1)`. -/
theorem lemma_9_1_7_needs_convex {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    MapsTo (fun _ : ℝ => (1 : ℝ)) ({0, 1} : Set ℝ) {0, 1} ∧
      ¬ MapsTo (damped (fun _ : ℝ => (1 : ℝ)) α) ({0, 1} : Set ℝ) {0, 1} := by
  refine ⟨fun _ _ => Or.inr rfl, fun h => ?_⟩
  have h0 := h (Or.inl rfl : (0 : ℝ) ∈ ({0, 1} : Set ℝ))
  simp only [damped, sub_zero, smul_eq_mul, mul_one, zero_add, Set.mem_insert_iff,
    Set.mem_singleton_iff] at h0
  rcases h0 with h0 | h0 <;> linarith

/-! ### The asset pricing example (§9.1.3.4) -/

/-- The asset pricing model: a `P`-Markov state on a finite set, dividends `d(X_{t+1})`, discount
factor `β ∈ [0, 1)`. -/
structure AssetPricing (X : Type*) [Fintype X] where
  /-- the transition matrix -/
  P : X → X → ℝ
  P_nonneg : ∀ x x', 0 ≤ P x x'
  P_sum : ∀ x, ∑ x', P x x' = 1
  /-- the dividend function -/
  d : X → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace AssetPricing

variable {X : Type*} [Fintype X] (M : AssetPricing X)

/-- `(Tv)(x) = β ∑_{x'} [v(x') + d(x')]P(x, x')`. -/
def T (v : X → ℝ) (x : X) : ℝ := M.β * ∑ x', (v x' + M.d x') * M.P x x'

/-- `T` is order preserving (p. 308). -/
theorem T_mono : Monotone M.T := fun _ _ h x =>
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (add_le_add (h x') le_rfl) (M.P_nonneg x x')) M.β_nonneg

theorem abs_sum_le {u : X → ℝ} {c : ℝ} (hu : ∀ y, |u y| ≤ c) (x : X) :
    |∑ x', u x' * M.P x x'| ≤ c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x', |u x' * M.P x x'| ≤ ∑ x', c * M.P x x' := Finset.sum_le_sum fun x' _ => by
        rw [abs_mul, abs_of_nonneg (M.P_nonneg x x')]
        exact mul_le_mul_of_nonneg_right (hu x') (M.P_nonneg x x')
    _ = c := by rw [← Finset.mul_sum, M.P_sum, mul_one]

/-- **Exercise 9.1.1** (p. 307): `T` is a contraction of modulus `β` on `(ℝ^X, ‖·‖∞)`. -/
theorem exercise_9_1_1 (v w : X → ℝ) : dist (M.T v) (M.T w) ≤ M.β * dist v w := by
  refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq]
  have e : M.T v x - M.T w x = M.β * ∑ x', (v x' - w x') * M.P x x' := by
    unfold T
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x' _ => by ring
  rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left (M.abs_sum_le (fun y => ?_) x) M.β_nonneg
  rw [← Real.dist_eq]
  exact dist_le_pi_dist v w y

/-- `K = βP` as a matrix. -/
def K : Matrix X X ℝ := Matrix.of fun x x' => M.β * M.P x x'

theorem T_eq_mulVec (v : X → ℝ) : M.T v = M.K.mulVec (v + M.d) := by
  funext x
  simp only [T, K, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- `I − K` is invertible, and `v* = (I − K)⁻¹Kd` is the unique fixed point of `T` (p. 307). -/
theorem fixedPoint [DecidableEq X] :
    IsUnit (1 - M.K) ∧ M.T ((1 - M.K)⁻¹.mulVec (M.K.mulVec M.d)) =
      (1 - M.K)⁻¹.mulVec (M.K.mulVec M.d) ∧
      ∀ v, M.T v = v → v = (1 - M.K)⁻¹.mulVec (M.K.mulVec M.d) := by
  -- `v = Kv` forces `v = 0`
  have hker : ∀ u : X → ℝ, M.K.mulVec u = u → u = 0 := fun u hu => by
    have h1 : dist u 0 ≤ M.β * dist u 0 := by
      have := M.exercise_9_1_1 u 0
      have e1 : M.T u = M.K.mulVec u + M.K.mulVec M.d := by
        rw [T_eq_mulVec, Matrix.mulVec_add]
      have e2 : M.T 0 = M.K.mulVec M.d := by rw [T_eq_mulVec, zero_add]
      have e3 : dist (M.K.mulVec u + M.K.mulVec M.d) (M.K.mulVec M.d) = dist u 0 := by
        rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_right, sub_zero, hu]
      rwa [e1, e2, e3] at this
    have h2 : dist u 0 = 0 := by
      nlinarith [dist_nonneg (x := u) (y := 0), M.β_lt_one]
    exact dist_eq_zero.1 h2
  have hinj : Injective (1 - M.K).mulVec := fun a b hab => by
    have h0 : (1 - M.K).mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact sub_eq_zero.1 (hker _ h0.symm)
  have hunit : IsUnit (1 - M.K) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (1 - M.K).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  set vs := (1 - M.K)⁻¹.mulVec (M.K.mulVec M.d)
  have hvs : (1 - M.K).mulVec vs = M.K.mulVec M.d := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hfix : M.T vs = vs := by
    rw [T_eq_mulVec, Matrix.mulVec_add]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hvs
    linear_combination -hvs
  refine ⟨hunit, hfix, fun v hv => ?_⟩
  have h1 : (1 - M.K).mulVec v = M.K.mulVec M.d := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [T_eq_mulVec, Matrix.mulVec_add] at hv
    linear_combination -hv
  exact hinj (h1.trans hvs.symm)

/-- The sampled operator: with draws `x'(x) ∼ P(x, ·)`, `(T̂v)(x) = β[v(x'(x)) + d(x'(x))]`. -/
def That (v : X → ℝ) (draw : X → X) (x : X) : ℝ := M.β * (v (draw x) + M.d (draw x))

/-- `T̂` is unbiased: `𝔼[(T̂v)(x)] = ∑_{x'} β[v(x') + d(x')]P(x, x') = (Tv)(x)` (p. 307). -/
theorem That_unbiased (v : X → ℝ) (x : X) :
    ∑ x', M.β * (v x' + M.d x') * M.P x x' = M.T v x := by
  unfold T
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- (9.15) is the Robbins–Monro rule (9.14) with `W = T̂v − Tv`. -/
theorem update_eq (v w : X → ℝ) (α : ℝ) :
    v + α • (w - v) = v + α • (M.T v + (w - M.T v) - v) := by
  congr 2
  abel

/-- Footnote 1 (p. 308): `|W(x)| ≤ 2β(‖v‖∞ + ‖d‖∞)`, whatever the draws. -/
theorem abs_noise_le (v : X → ℝ) (draw : X → X) (x : X) :
    |M.That v draw x - M.T v x| ≤ 2 * M.β * (‖v‖ + ‖M.d‖) := by
  have hb : ∀ y, |v y + M.d y| ≤ ‖v‖ + ‖M.d‖ := fun y =>
    (abs_add_le _ _).trans (add_le_add (by simpa using norm_le_pi_norm v y)
      (by simpa using norm_le_pi_norm M.d y))
  have h1 : |M.That v draw x| ≤ M.β * (‖v‖ + ‖M.d‖) := by
    rw [That, abs_mul, abs_of_nonneg M.β_nonneg]
    exact mul_le_mul_of_nonneg_left (hb _) M.β_nonneg
  have h2 : |M.T v x| ≤ M.β * (‖v‖ + ‖M.d‖) := by
    rw [T, abs_mul, abs_of_nonneg M.β_nonneg]
    exact mul_le_mul_of_nonneg_left (M.abs_sum_le hb x) M.β_nonneg
  calc |M.That v draw x - M.T v x| ≤ |M.That v draw x| + |M.T v x| := abs_sub _ _
    _ ≤ 2 * M.β * (‖v‖ + ‖M.d‖) := by linarith

/-- Footnote 1 (p. 308), condition (ii) of Theorem 9.1.8: whatever the draws,
`∑ₓ W(x)² ≤ C(1 + ‖v‖∞²)` with `C = 8|X|β²(1 + ‖d‖∞²)`, a constant depending only on `β`, `|X|`
and `‖d‖∞`. -/
theorem sum_sq_noise_le (v : X → ℝ) (draw : X → X) :
    ∑ x, (M.That v draw x - M.T v x) ^ 2 ≤
      8 * Fintype.card X * M.β ^ 2 * (1 + ‖M.d‖ ^ 2) * (1 + ‖v‖ ^ 2) := by
  have hpt : ∀ x, (M.That v draw x - M.T v x) ^ 2 ≤ 4 * M.β ^ 2 * (‖v‖ + ‖M.d‖) ^ 2 := fun x => by
    have h := M.abs_noise_le v draw x
    have h0 : 0 ≤ 2 * M.β * (‖v‖ + ‖M.d‖) :=
      mul_nonneg (mul_nonneg zero_le_two M.β_nonneg) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    calc (M.That v draw x - M.T v x) ^ 2 = |M.That v draw x - M.T v x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M.β * (‖v‖ + ‖M.d‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := by ring
  have hsq : (‖v‖ + ‖M.d‖) ^ 2 ≤ 2 * (1 + ‖M.d‖ ^ 2) * (1 + ‖v‖ ^ 2) := by
    nlinarith [sq_nonneg (‖v‖ - ‖M.d‖), sq_nonneg ‖v‖, sq_nonneg ‖M.d‖,
      mul_nonneg (sq_nonneg ‖v‖) (sq_nonneg ‖M.d‖)]
  calc ∑ x, (M.That v draw x - M.T v x) ^ 2 ≤ ∑ _x : X, 4 * M.β ^ 2 * (‖v‖ + ‖M.d‖) ^ 2 :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = Fintype.card X * (4 * M.β ^ 2 * (‖v‖ + ‖M.d‖) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Fintype.card X * (4 * M.β ^ 2 * (2 * (1 + ‖M.d‖ ^ 2) * (1 + ‖v‖ ^ 2))) := by
        gcongr
    _ = _ := by ring

end AssetPricing

end SargentStachurski.ApproximationAndLearning
