/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.EulerEquations
import DeterministicDynamics.Assumption42

/-!
# Linear–quadratic problems: optimality of Euler paths

SLP §6.4, pp. 149–152. A quadratic return on `ℝˡ × ℝˡ`,
`F(x, y) = c₀ + F̄_x·x + F̄_y·y + ½x'F_xx x + x'F_xy y + ½y'F_yy y` (`lqF`), with `F_xx`, `F_yy`
symmetric, has partial derivatives `F_x = F̄_x + F_xx x + F_xy y` and
`F_y = F̄_y + F'_xy x + F_yy y` (`lqFx`, `lqFy`), and the Taylor expansion is exact
(`lqF_add`). Strict concavity makes the quadratic part negative definite (`lqQ_neg`), and
by compactness of the unit sphere uniformly so (`exists_lqQ_bound`).

* `lq_sufficient`: with `Γ(x) = ℝˡ` and `0 < β < 1`, a convergent path satisfying the Euler
  equations (2) is optimal. Plans with `u(x) > −∞` have `Σβᵗ|x_t|² < ∞`, which kills the
  boundary terms of `euler_sufficient`.
* `lq_unique`: an optimal plan with finite value is the only optimal plan (the midpoint of two
  optimal plans would do strictly better).
-/

open Set Filter Topology
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {P Q R : Matrix (Fin l) (Fin l) ℝ} {a b : Fin l → ℝ} {c₀ β : ℝ}

/-- The quadratic part `½u'F_xx u + u'F_xy v + ½v'F_yy v`. -/
noncomputable def lqQ (P Q R : Matrix (Fin l) (Fin l) ℝ) (u v : Fin l → ℝ) : ℝ :=
  u ⬝ᵥ (P *ᵥ u) / 2 + u ⬝ᵥ (Q *ᵥ v) + v ⬝ᵥ (R *ᵥ v) / 2

/-- The quadratic return `F(x, y) = c₀ + a·x + b·y + ½x'Px + x'Qy + ½y'Ry`. -/
noncomputable def lqF (P Q R : Matrix (Fin l) (Fin l) ℝ) (a b : Fin l → ℝ) (c₀ : ℝ)
    (p : (Fin l → ℝ) × (Fin l → ℝ)) : ℝ :=
  c₀ + a ⬝ᵥ p.1 + b ⬝ᵥ p.2 + lqQ P Q R p.1 p.2

/-- `F_x(x, y) = a + Px + Qy`. -/
def lqFx (P Q : Matrix (Fin l) (Fin l) ℝ) (a x y : Fin l → ℝ) : Fin l → ℝ := a + P *ᵥ x + Q *ᵥ y

/-- `F_y(x, y) = b + Q'x + Ry`. -/
def lqFy (Q R : Matrix (Fin l) (Fin l) ℝ) (b x y : Fin l → ℝ) : Fin l → ℝ := b + Qᵀ *ᵥ x + R *ᵥ y

theorem dot_sym (hP : Pᵀ = P) (u x : Fin l → ℝ) : u ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP, dotProduct_comm]

theorem dot_transpose (Q : Matrix (Fin l) (Fin l) ℝ) (x v : Fin l → ℝ) :
    (Qᵀ *ᵥ x) ⬝ᵥ v = x ⬝ᵥ (Q *ᵥ v) := by
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

/-- **The Taylor expansion of a quadratic is exact.** -/
theorem lqF_add (hP : Pᵀ = P) (hR : Rᵀ = R) (x y u v : Fin l → ℝ) :
    lqF P Q R a b c₀ (x + u, y + v) = lqF P Q R a b c₀ (x, y) + lqFx P Q a x y ⬝ᵥ u +
      lqFy Q R b x y ⬝ᵥ v + lqQ P Q R u v := by
  have e1 : (P *ᵥ x) ⬝ᵥ u = x ⬝ᵥ (P *ᵥ u) := by rw [dotProduct_comm, dot_sym hP]
  have e2 : (Q *ᵥ y) ⬝ᵥ u = u ⬝ᵥ (Q *ᵥ y) := dotProduct_comm _ _
  have e3 : (R *ᵥ y) ⬝ᵥ v = y ⬝ᵥ (R *ᵥ v) := by rw [dotProduct_comm, dot_sym hR]
  have e5 : u ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ u) := dot_sym hP u x
  have e6 : v ⬝ᵥ (R *ᵥ y) = y ⬝ᵥ (R *ᵥ v) := dot_sym hR v y
  simp only [lqF, lqQ, lqFx, lqFy, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    dot_transpose, e1, e2, e3, e5, e6]
  ring

theorem lqQ_smul (t : ℝ) (u v : Fin l → ℝ) :
    lqQ P Q R (t • u) (t • v) = t ^ 2 * lqQ P Q R u v := by
  simp only [lqQ, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem lqQ_zero_left : lqQ P Q R 0 0 = 0 := by simp [lqQ]

/-- **Strict concavity makes the quadratic part negative definite.** -/
theorem lqQ_neg (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) {u v : Fin l → ℝ}
    (huv : (u, v) ≠ 0) : lqQ P Q R u v < 0 := by
  have hne : (u, v) ≠ -(u, v) := fun h => huv (by
    have h2 : (2 : ℝ) • (u, v) = 0 := by
      rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero)
  have := hconc.2 (mem_univ (u, v)) (mem_univ (-(u, v))) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • (u, v) + (1 / 2 : ℝ) • -(u, v) = 0 := by
    rw [smul_neg, add_neg_cancel]
  rw [e] at this
  simp only [lqF, lqQ, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero,
    Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, Matrix.mulVec_zero,
    dotProduct_zero, smul_eq_mul] at this
  unfold lqQ
  linarith

/-- The quadratic part is continuous. -/
theorem continuous_lqQ : Continuous fun w : (Fin l → ℝ) × (Fin l → ℝ) => lqQ P Q R w.1 w.2 := by
  unfold lqQ
  fun_prop

/-- **Uniform negative definiteness**: `q(u, v) ≤ −m‖(u, v)‖²`. -/
theorem exists_lqQ_bound (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ P Q R u v < 0) :
    ∃ m > 0, ∀ u v : Fin l → ℝ, lqQ P Q R u v ≤ -m * ‖(u, v)‖ ^ 2 := by
  set φ : (Fin l → ℝ) × (Fin l → ℝ) → ℝ := fun w => lqQ P Q R w.1 w.2
  -- `φ(w) = ‖w‖²φ(w/‖w‖)`
  have hhom : ∀ w : (Fin l → ℝ) × (Fin l → ℝ), w ≠ 0 →
      φ w = ‖w‖ ^ 2 * φ (‖w‖⁻¹ • w) ∧ ‖w‖⁻¹ • w ∈ Metric.sphere 0 1 := fun w hw => by
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    refine ⟨?_, by simp [norm_smul, hn]⟩
    have := lqQ_smul (P := P) (Q := Q) (R := R) ‖w‖ (‖w‖⁻¹ • w).1 (‖w‖⁻¹ • w).2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_smul, mul_inv_cancel₀ hn, one_smul] at this
    exact this
  by_cases hs : (Metric.sphere (0 : (Fin l → ℝ) × (Fin l → ℝ)) 1).Nonempty
  · obtain ⟨w₀, hw₀, hmax⟩ := (isCompact_sphere (0 : (Fin l → ℝ) × (Fin l → ℝ)) 1).exists_isMaxOn
      hs (continuous_lqQ (P := P) (Q := Q) (R := R)).continuousOn
    have hw₀0 : w₀ ≠ 0 := by
      intro h; rw [h] at hw₀; simp at hw₀
    refine ⟨-φ w₀, by linarith [hneg w₀.1 w₀.2 hw₀0], fun u v => ?_⟩
    by_cases hw : (u, v) = 0
    · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 hw; simp [lqQ_zero_left]
    · obtain ⟨e, hmem⟩ := hhom (u, v) hw
      have : φ (‖(u, v)‖⁻¹ • (u, v)) ≤ φ w₀ := hmax hmem
      change φ (u, v) ≤ _
      rw [e]
      have h2 : 0 ≤ ‖(u, v)‖ ^ 2 := sq_nonneg _
      nlinarith
  · refine ⟨1, one_pos, fun u v => ?_⟩
    by_cases hw : (u, v) = 0
    · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 hw; simp [lqQ_zero_left]
    · exact absurd ⟨_, (hhom (u, v) hw).2⟩ hs

/-- `|g·v| ≤ (Σ|gᵢ|)‖v‖` in the sup norm. -/
theorem abs_dot_le (g v : Fin l → ℝ) : |g ⬝ᵥ v| ≤ (∑ i, |g i|) * ‖v‖ := by
  rw [dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v i) (abs_nonneg _)

/-- **`F` is bounded above by a downward parabola**: `F(p) ≤ C − m‖p‖²`. -/
theorem exists_lqF_bound (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) :
    ∃ C, ∃ m > 0, ∀ p, lqF P Q R a b c₀ p ≤ C - m * ‖p‖ ^ 2 := by
  obtain ⟨m, hm, hq⟩ := exists_lqQ_bound (P := P) (Q := Q) (R := R)
    fun u v huv => lqQ_neg hconc huv
  set G := (∑ i, |a i|) + ∑ i, |b i|
  refine ⟨c₀ + G ^ 2 / (2 * m), m / 2, by linarith, fun p => ?_⟩
  have h1 : a ⬝ᵥ p.1 ≤ (∑ i, |a i|) * ‖p‖ :=
    (le_abs_self _).trans ((abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left (norm_fst_le p)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)))
  have h2 : b ⬝ᵥ p.2 ≤ (∑ i, |b i|) * ‖p‖ :=
    (le_abs_self _).trans ((abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left (norm_snd_le p)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)))
  have h3 := hq p.1 p.2
  have h4 : G * ‖p‖ ≤ m / 2 * ‖p‖ ^ 2 + G ^ 2 / (2 * m) := by
    have e : m / 2 * ‖p‖ ^ 2 + G ^ 2 / (2 * m) - G * ‖p‖ = (m * ‖p‖ - G) ^ 2 / (2 * m) := by
      field_simp; ring
    have : 0 ≤ (m * ‖p‖ - G) ^ 2 / (2 * m) := by positivity
    linarith
  simp only [lqF]
  simp only [G] at h4
  nlinarith

/-- **Assumption 4.2** holds for the quadratic return with `Γ(x) = ℝˡ`. -/
theorem lq_assumption42 (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    Assumption42 (fun _ : Fin l → ℝ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β := by
  obtain ⟨C, m, hm, hb⟩ := exists_lqF_bound hconc
  exact assumption42_of_bddAbove (M := C) (fun x y => (hb (x, y)).trans
    (by nlinarith [sq_nonneg ‖(x, y)‖])) hβ0 hβ1

/-- **A plan with `u(x) > −∞` has `βᵗ‖(x_t, x_{t+1})‖² → 0`.** -/
theorem tendsto_of_total_ne_bot (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀))
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → Fin l → ℝ}
    (hx : total (fun x y => lqF P Q R a b c₀ (x, y)) β x ≠ ⊥) :
    Tendsto (fun t => β ^ t * ‖(x t, x (t + 1))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, m, hm, hb⟩ := exists_lqF_bound hconc
  have h42 := lq_assumption42 (a := a) (b := b) (c₀ := c₀) hconc hβ0 hβ1
  have hlim := tendsto_total h42 (x₀ := x 0) (x := x) ⟨rfl, fun _ => mem_univ _⟩
  -- the partial sums are eventually above some real `r`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) < total (fun x y => lqF P Q R a b c₀ (x, y)) β x := by
    induction h : total (fun x y => lqF P Q R a b c₀ (x, y)) β x with
    | bot => exact absurd h hx
    | coe s => exact ⟨s - 1, EReal.coe_lt_coe_iff.2 (by linarith)⟩
    | top => exact ⟨0, EReal.coe_lt_top 0⟩
  have hev := hlim.eventually (lt_mem_nhds hr)
  set s : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), β ^ t * ‖(x t, x (t + 1))‖ ^ 2
  have hgeo : ∀ n, ∑ t ∈ Finset.range (n + 1), β ^ t * |C| ≤ |C| / (1 - β) := fun n => by
    have hb1 : 0 < 1 - β := by linarith
    rw [← Finset.sum_mul, geom_sum_eq (by linarith : β ≠ 1)]
    have e : (β ^ (n + 1) - 1) / (β - 1) = (1 - β ^ (n + 1)) / (1 - β) := by
      rw [div_eq_div_iff (by linarith) hb1.ne']; ring
    rw [e, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hb1]
    nlinarith [abs_nonneg C, pow_nonneg hβ0 (n + 1)]
  have hbound : ∀ n, partialSum (fun x y => lqF P Q R a b c₀ (x, y)) β x n ≤
      |C| / (1 - β) - m * s n := fun n => by
    simp only [partialSum, s, Finset.mul_sum]
    refine le_trans ?_ (sub_le_sub_right (hgeo n) _)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have := hb (x t, x (t + 1))
    have hβt := pow_nonneg hβ0 t
    nlinarith [le_abs_self C]
  -- so `s` is eventually, hence always, bounded
  have hmono : Monotone s := fun n n' hnn' => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega)) fun t _ _ => mul_nonneg (pow_nonneg hβ0 t)
      (sq_nonneg _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsb : ∀ n, s n ≤ (|C| / (1 - β) - r) / m := fun n => by
    have h1 := hN (max n N) (le_max_right _ _)
    have h2 := hbound (max n N)
    have h3 : r < partialSum (fun x y => lqF P Q R a b c₀ (x, y)) β x (max n N) :=
      EReal.coe_lt_coe_iff.1 h1
    rw [le_div_iff₀ hm]
    nlinarith [hmono (le_max_left n N)]
  have hsum : Summable fun t => β ^ t * ‖(x t, x (t + 1))‖ ^ 2 :=
    summable_of_sum_range_le (fun t => mul_nonneg (pow_nonneg hβ0 t) (sq_nonneg _))
      fun n => (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2
        (Nat.le_succ n)) fun t _ _ => mul_nonneg (pow_nonneg hβ0 t) (sq_nonneg _)).trans (hsb n)
  exact hsum.tendsto_atTop_zero

theorem lqQ_nonpos (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (u v : Fin l → ℝ) :
    lqQ P Q R u v ≤ 0 := by
  by_cases h : (u, v) = 0
  · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 h
    rw [lqQ_zero_left]
  · exact (lqQ_neg hconc h).le

theorem continuous_lqF : Continuous (lqF P Q R a b c₀) := by
  unfold lqF lqQ
  fun_prop

/-- The derivative `(u, v) ↦ g₁·u + g₂·v`. -/
noncomputable def lqD (g₁ g₂ : Fin l → ℝ) : ((Fin l → ℝ) × (Fin l → ℝ)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => g₁ ⬝ᵥ p.1 + g₂ ⬝ᵥ p.2
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, dotProduct_add]; ring
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul,
          RingHom.id_apply]
        ring }

theorem lqD_apply (g₁ g₂ : Fin l → ℝ) (p : (Fin l → ℝ) × (Fin l → ℝ)) :
    lqD g₁ g₂ p = g₁ ⬝ᵥ p.1 + g₂ ⬝ᵥ p.2 := rfl

/-- **A convergent Euler path is optimal.** With `Γ(x) = ℝˡ`, `0 < β < 1` and `F` strictly
concave, a path satisfying the Euler equations (2)
`F_y(x_t, x_{t+1}) + βF_x(x_{t+1}, x_{t+2}) = 0` and converging is optimal. -/
theorem lq_sufficient (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β) (hβ1 : β < 1)
    {xs : ℕ → Fin l → ℝ} {xbar : Fin l → ℝ}
    (heuler : ∀ t, lqFy Q R b (xs t) (xs (t + 1)) + β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) = 0)
    (hconv : Tendsto xs atTop (𝓝 xbar)) :
    total (fun x y => lqF P Q R a b c₀ (x, y)) β xs =
      vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β (xs 0) := by
  have h42 := lq_assumption42 (a := a) (b := b) (c₀ := c₀) hconc hβ0.le hβ1
  set D : ℕ → ((Fin l → ℝ) × (Fin l → ℝ)) →L[ℝ] ℝ := fun t =>
    lqD (lqFx P Q a (xs t) (xs (t + 1))) (lqFy Q R b (xs t) (xs (t + 1)))
  refine euler_sufficient (F := lqF P Q R a b c₀) (Γ := fun _ => univ) h42
    ⟨rfl, fun _ => mem_univ _⟩ D ?_ ?_ hβ0.le ?_
  · -- `F` lies below its tangent planes
    intro t x y _
    have := lqF_add hP hR (Q := Q) (a := a) (b := b) (c₀ := c₀) (xs t) (xs (t + 1)) (x - xs t)
      (y - xs (t + 1))
    rw [show xs t + (x - xs t) = x by abel, show xs (t + 1) + (y - xs (t + 1)) = y by abel]
      at this
    rw [this, lqD_apply]
    simp only [Prod.fst_sub, Prod.snd_sub]
    linarith [lqQ_nonpos hconc (x - xs t) (y - xs (t + 1))]
  · -- the Euler equations
    intro t v
    have h := congrArg (· ⬝ᵥ v) (heuler t)
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h
    simp only [Fy, Fx, D, lqD_apply, dotProduct_zero, zero_add, add_zero]
    exact h
  · -- the boundary terms vanish against plans with `u(x) > −∞`
    intro x _ hx
    have hg : Tendsto (fun t => ∑ i, |lqFx P Q a (xs t) (xs (t + 1)) i|) atTop
        (𝓝 (∑ i, |lqFx P Q a xbar xbar i|)) := by
      have hFx : Continuous fun p : (Fin l → ℝ) × (Fin l → ℝ) => lqFx P Q a p.1 p.2 :=
        (continuous_const.add (continuous_const.matrix_mulVec continuous_fst)).add
          (continuous_const.matrix_mulVec continuous_snd)
      have hc : Continuous fun p : (Fin l → ℝ) × (Fin l → ℝ) => ∑ i, |lqFx P Q a p.1 p.2 i| :=
        continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hFx).abs
      have hp : Tendsto (fun t => (xs t, xs (t + 1))) atTop (𝓝 (xbar, xbar)) :=
        hconv.prodMk_nhds (hconv.comp (tendsto_add_atTop_nat 1))
      have h := (hc.tendsto (xbar, xbar)).comp hp
      simp only [Function.comp_def] at h
      exact h
    obtain ⟨G, hG⟩ := hg.bddAbove_range
    obtain ⟨B, hB⟩ := hconv.norm.bddAbove_range
    have hpT := tendsto_of_total_ne_bot (a := a) (b := b) (c₀ := c₀) hconc hβ0.le hβ1 hx
    have hxT : Tendsto (fun T => β ^ (T + 1) * ‖x (T + 1)‖) atTop (𝓝 0) := by
      have hup : Tendsto (fun T => β * (β ^ T + β ^ T * ‖(x T, x (T + 1))‖ ^ 2)) atTop
          (𝓝 (β * (0 + 0))) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).add hpT |>.const_mul β
      rw [add_zero, mul_zero] at hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun T => mul_nonneg (pow_nonneg hβ0.le _) (norm_nonneg _)) fun T => ?_
      have h1 : ‖x (T + 1)‖ ≤ ‖(x T, x (T + 1))‖ := norm_snd_le (x T, x (T + 1))
      have h2 : ‖(x T, x (T + 1))‖ ≤ 1 + ‖(x T, x (T + 1))‖ ^ 2 := by
        nlinarith [sq_nonneg (‖(x T, x (T + 1))‖ - 1)]
      have hβT := pow_nonneg hβ0.le T
      have := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hβT hβ0.le)
      calc β ^ (T + 1) * ‖x (T + 1)‖ = β ^ T * β * ‖x (T + 1)‖ := by rw [pow_succ]
        _ ≤ β ^ T * β * (1 + ‖(x T, x (T + 1))‖ ^ 2) := this
        _ = _ := by ring
    set G' := max G 0
    refine ⟨fun T => G' * (B * β ^ (T + 1) + β ^ (T + 1) * ‖x (T + 1)‖), ?_, fun T => ?_⟩
    · have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
        (tendsto_add_atTop_nat 1)).const_mul B |>.add hxT |>.const_mul G'
      simpa [Function.comp_def] using this
    · simp only [Fx, D, lqD_apply, dotProduct_zero, add_zero]
      have hd := (le_abs_self _).trans (abs_dot_le (lqFx P Q a (xs (T + 1)) (xs (T + 1 + 1)))
        (xs (T + 1) - x (T + 1)))
      have hGT : ∑ i, |lqFx P Q a (xs (T + 1)) (xs (T + 1 + 1)) i| ≤ G' :=
        (hG ⟨T + 1, rfl⟩).trans (le_max_left _ _)
      have hn : ‖xs (T + 1) - x (T + 1)‖ ≤ B + ‖x (T + 1)‖ :=
        (norm_sub_le _ _).trans (add_le_add (hB ⟨T + 1, rfl⟩) le_rfl)
      have hG0 : 0 ≤ G' := le_max_right _ _
      have hβT := pow_nonneg hβ0.le (T + 1)
      have h3 : (∑ i, |lqFx P Q a (xs (T + 1)) (xs (T + 1 + 1)) i|) *
          ‖xs (T + 1) - x (T + 1)‖ ≤ G' * (B + ‖x (T + 1)‖) :=
        mul_le_mul hGT hn (norm_nonneg _) hG0
      nlinarith

/-- **The midpoint gains `−¼q(d)`**: with `d = (y, y') − (x, x')`,
`F(midpoint) = ½F(x, x') + ½F(y, y') − ¼q(d)`. -/
theorem lqF_midpoint (hP : Pᵀ = P) (hR : Rᵀ = R) (x x' y y' : Fin l → ℝ) :
    lqF P Q R a b c₀ (x + (1 / 2 : ℝ) • (y - x), x' + (1 / 2 : ℝ) • (y' - x')) =
      lqF P Q R a b c₀ (x, x') / 2 + lqF P Q R a b c₀ (y, y') / 2 -
        lqQ P Q R (y - x) (y' - x') / 4 := by
  have h1 := lqF_add hP hR (Q := Q) (a := a) (b := b) (c₀ := c₀) x x' ((1 / 2 : ℝ) • (y - x))
    ((1 / 2 : ℝ) • (y' - x'))
  have h2 := lqF_add hP hR (Q := Q) (a := a) (b := b) (c₀ := c₀) x x' (y - x) (y' - x')
  rw [show x + (y - x) = y by abel, show x' + (y' - x') = y' by abel] at h2
  rw [h1, h2, lqQ_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The optimal plan is unique.** If a convergent plan `x*` is optimal, every optimal plan
from `x₀ = x*₀` equals it: otherwise their midpoint would do strictly better. -/
theorem lq_unique (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β) (hβ1 : β < 1)
    {xs : ℕ → Fin l → ℝ} {xbar : Fin l → ℝ} (hconv : Tendsto xs atTop (𝓝 xbar))
    (hopt : total (fun x y => lqF P Q R a b c₀ (x, y)) β xs =
      vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β (xs 0))
    {y : ℕ → Fin l → ℝ} (hy0 : y 0 = xs 0)
    (hyopt : total (fun x y => lqF P Q R a b c₀ (x, y)) β y =
      vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β (xs 0)) : y = xs := by
  have h42 := lq_assumption42 (a := a) (b := b) (c₀ := c₀) hconc hβ0.le hβ1
  set Fc : (Fin l → ℝ) → (Fin l → ℝ) → ℝ := fun x y => lqF P Q R a b c₀ (x, y)
  -- the value of `x*` is finite: its terms are bounded by a geometric sequence
  have hFt : Tendsto (fun t => lqF P Q R a b c₀ (xs t, xs (t + 1))) atTop
      (𝓝 (lqF P Q R a b c₀ (xbar, xbar))) := by
    have hp : Tendsto (fun t => (xs t, xs (t + 1))) atTop (𝓝 (xbar, xbar)) :=
      hconv.prodMk_nhds (hconv.comp (tendsto_add_atTop_nat 1))
    have h := ((continuous_lqF (P := P) (Q := Q) (R := R) (a := a) (b := b) (c₀ := c₀)).tendsto
      (xbar, xbar)).comp hp
    simp only [Function.comp_def] at h
    exact h
  obtain ⟨K, hK⟩ := hFt.norm.bddAbove_range
  have hsum : Summable fun t => β ^ t * Fc (xs t) (xs (t + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
      fun t => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hβ0.le]
    exact mul_le_mul_of_nonneg_left (hK ⟨t, rfl⟩) (pow_nonneg hβ0.le t)
  set ℓ := ∑' t, β ^ t * Fc (xs t) (xs (t + 1))
  have hxs : Tendsto (fun n => partialSum Fc β xs n) atTop (𝓝 ℓ) :=
    hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have htot : total Fc β xs = (ℓ : EReal) :=
    tendsto_nhds_unique (tendsto_total h42 ⟨rfl, fun _ => mem_univ _⟩)
      (EReal.tendsto_coe.2 hxs)
  have hys : Tendsto (fun n => partialSum Fc β y n) atTop (𝓝 ℓ) := by
    have := tendsto_total h42 (x₀ := xs 0) (x := y) ⟨hy0, fun _ => mem_univ _⟩
    rw [hyopt, ← hopt, htot] at this
    exact EReal.tendsto_coe.1 this
  -- a first date at which the plans differ
  by_contra hne
  obtain ⟨s, hs⟩ : ∃ s, y s ≠ xs s := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨t₀, rfl⟩ : ∃ t₀, s = t₀ + 1 := by
    rcases s with _ | t₀
    · exact absurd hy0 hs
    · exact ⟨t₀, rfl⟩
  have hd : (y t₀ - xs t₀, y (t₀ + 1) - xs (t₀ + 1)) ≠ 0 := fun h =>
    hs (sub_eq_zero.1 (Prod.mk_eq_zero.1 h).2)
  set δ := β ^ t₀ * (-(lqQ P Q R (y t₀ - xs t₀) (y (t₀ + 1) - xs (t₀ + 1)) / 4))
  have hδ : 0 < δ := mul_pos (pow_pos hβ0 t₀) (by linarith [lqQ_neg hconc hd])
  -- the midpoint plan
  set z : ℕ → Fin l → ℝ := fun t => xs t + (1 / 2 : ℝ) • (y t - xs t)
  have hz : z ∈ Feasible (fun _ => univ) (xs 0) :=
    ⟨by simp [z, hy0], fun _ => mem_univ _⟩
  have hzle : total Fc β z ≤ (ℓ : EReal) := by
    rw [← htot, hopt]; exact le_biSup _ hz
  have hgain : ∀ n, t₀ ≤ n →
      partialSum Fc β xs n / 2 + partialSum Fc β y n / 2 + δ ≤ partialSum Fc β z n := by
    intro n hn
    have hterm : ∀ t, β ^ t * Fc (z t) (z (t + 1)) = β ^ t * Fc (xs t) (xs (t + 1)) / 2 +
        β ^ t * Fc (y t) (y (t + 1)) / 2 +
        β ^ t * (-(lqQ P Q R (y t - xs t) (y (t + 1) - xs (t + 1)) / 4)) := fun t => by
      simp only [Fc, z, lqF_midpoint hP hR]; ring
    simp only [partialSum, hterm, Finset.sum_add_distrib, ← Finset.sum_div]
    have hsingle : δ ≤ ∑ t ∈ Finset.range (n + 1), β ^ t *
        (-(lqQ P Q R (y t - xs t) (y (t + 1) - xs (t + 1)) / 4)) :=
      Finset.single_le_sum (f := fun t => β ^ t *
        (-(lqQ P Q R (y t - xs t) (y (t + 1) - xs (t + 1)) / 4)))
        (fun t _ => mul_nonneg (pow_nonneg hβ0.le t)
          (by linarith [lqQ_nonpos hconc (y t - xs t) (y (t + 1) - xs (t + 1))]))
        (Finset.mem_range.2 (by omega))
    linarith
  have hlow : Tendsto (fun n => partialSum Fc β xs n / 2 + partialSum Fc β y n / 2 + δ) atTop
      (𝓝 (ℓ / 2 + ℓ / 2 + δ)) := ((hxs.div_const 2).add (hys.div_const 2)).add_const δ
  have hge : ((ℓ / 2 + ℓ / 2 + δ : ℝ) : EReal) ≤ total Fc β z :=
    le_of_tendsto_of_tendsto (EReal.tendsto_coe.2 hlow) (tendsto_total h42 hz)
      (eventually_atTop.2 ⟨t₀, fun n hn => EReal.coe_le_coe_iff.2 (hgain n hn)⟩)
  have := EReal.coe_le_coe_iff.1 (hge.trans hzle)
  linarith

end StokeyLucasPrescott.DeterministicDynamics
