/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.NonlinearEuler
import DeterministicDynamics.LinearQuadratic

/-!
# Local stability of optimal paths (Theorem 6.9)

SLP §6.4, p. 153. `F` is strictly concave on the convex graph of `Γ`, bounded there, and the
states are bounded; `x̄` is an interior stationary point at which `F` has gradient `(F_x, F_y)`
near `(x̄, x̄)`, strictly differentiable there with second derivatives `F_xx`, `F_xy`, `F_yy`;
`F_xy` is nonsingular and `A` has `l` characteristic roots inside the unit circle. Then for
every `x₀` close to `x̄` the optimal plan exists, is unique, and converges to `x̄`
(`theorem_6_9`).

The proof: `exists_convergent_euler_path` gives a feasible path satisfying the Euler equations
and converging to `x̄`. It is optimal by `euler_sufficient` (concavity, bounded states), and
optimal plans are unique by strict concavity (`optimal_unique`).

**Correction.** The book's proof needs the second-order form
`½u'F_xx u + u'F_xy v + ½v'F_yy v` to be negative definite (not just `F` strictly concave): see
`NonlinearEuler`.
-/

open Set Filter Topology Module
open scoped Matrix NNReal

namespace StokeyLucasPrescott.DeterministicDynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Bounded returns make the value of a feasible plan the sum of a convergent series. -/
theorem total_eq_tsum_of_bdd {Γ : E → Set E} {F : E × E → ℝ} {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hM : ∀ p : E × E, p.2 ∈ Γ p.1 → |F p| ≤ M) {x₀ : E} {x : ℕ → E}
    (hx : x ∈ Feasible Γ x₀) :
    Summable (fun t => β ^ t * F (x t, x (t + 1))) ∧
      total (fun a b => F (a, b)) β x = ((∑' t, β ^ t * F (x t, x (t + 1)) : ℝ) : EReal) := by
  have hs : Summable fun t => β ^ t * F (x t, x (t + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
      fun t => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hβ0, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _ (hx.2 t)) (pow_nonneg hβ0 t)
  refine ⟨hs, ?_⟩
  have hlim : Tendsto (fun n => (partialSum (fun a b => F (a, b)) β x n : EReal)) atTop
      (𝓝 ((∑' t, β ^ t * F (x t, x (t + 1)) : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, hlim⟩) hlim

/-- **Uniqueness of the optimal plan** under strict concavity on a convex graph. -/
theorem optimal_unique {Γ : E → Set E} {F : E × E → ℝ} {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hconv : Convex ℝ {p : E × E | p.2 ∈ Γ p.1})
    (hconc : StrictConcaveOn ℝ {p : E × E | p.2 ∈ Γ p.1} F)
    (hM : ∀ p : E × E, p.2 ∈ Γ p.1 → |F p| ≤ M) {x₀ : E} {x y : ℕ → E}
    (hx : x ∈ Feasible Γ x₀) (hy : y ∈ Feasible Γ x₀)
    (hxo : total (fun a b => F (a, b)) β x = vstar Γ (fun a b => F (a, b)) β x₀)
    (hyo : total (fun a b => F (a, b)) β y = vstar Γ (fun a b => F (a, b)) β x₀) : y = x := by
  obtain ⟨hsx, htx⟩ := total_eq_tsum_of_bdd hβ0.le hβ1 hM hx
  obtain ⟨hsy, hty⟩ := total_eq_tsum_of_bdd hβ0.le hβ1 hM hy
  by_contra hne
  obtain ⟨s, hs⟩ : ∃ s, y s ≠ x s := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨t₀, rfl⟩ : ∃ t₀, s = t₀ + 1 := by
    rcases s with _ | t₀
    · exact absurd (hy.1.trans hx.1.symm) hs
    · exact ⟨t₀, rfl⟩
  -- the midpoint plan
  set z : ℕ → E := fun t => (1 / 2 : ℝ) • x t + (1 / 2 : ℝ) • y t
  have hmem : ∀ t, (z t, z (t + 1)) = (1 / 2 : ℝ) • (x t, x (t + 1)) +
      (1 / 2 : ℝ) • (y t, y (t + 1)) := fun t => by simp [z]
  have hxG : ∀ t, (x t, x (t + 1)) ∈ {p : E × E | p.2 ∈ Γ p.1} := hx.2
  have hyG : ∀ t, (y t, y (t + 1)) ∈ {p : E × E | p.2 ∈ Γ p.1} := hy.2
  have hz : z ∈ Feasible Γ x₀ := ⟨by
      simp only [z, hx.1, hy.1]; rw [← add_smul]; norm_num, fun t => by
    have := hconv (hxG t) (hyG t) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [← hmem] at this; exact this⟩
  have hgain : ∀ t, (F (x t, x (t + 1)) + F (y t, y (t + 1))) / 2 ≤ F (z t, z (t + 1)) :=
    fun t => by
      have := hconc.concaveOn.2 (hxG t) (hyG t) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      rw [← hmem] at this; simp only [smul_eq_mul] at this; linarith
  have hpair : (x t₀, x (t₀ + 1)) ≠ (y t₀, y (t₀ + 1)) := fun h =>
    hs (congrArg Prod.snd h).symm
  have hstrict : (F (x t₀, x (t₀ + 1)) + F (y t₀, y (t₀ + 1))) / 2 < F (z t₀, z (t₀ + 1)) := by
    have := hconc.2 (hxG t₀) (hyG t₀) hpair (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [← hmem] at this; simp only [smul_eq_mul] at this; linarith
  obtain ⟨hsz, htz⟩ := total_eq_tsum_of_bdd hβ0.le hβ1 hM hz
  set ℓ := ∑' t, β ^ t * F (x t, x (t + 1))
  have hyℓ : ∑' t, β ^ t * F (y t, y (t + 1)) = ℓ := by
    have := hty.symm.trans (hyo.trans (hxo.symm.trans htx))
    exact EReal.coe_injective this
  have hzle : ∑' t, β ^ t * F (z t, z (t + 1)) ≤ ℓ := by
    have h1 : total (fun a b => F (a, b)) β z ≤ vstar Γ (fun a b => F (a, b)) β x₀ :=
      le_biSup (fun p => total (fun a b => F (a, b)) β p) hz
    rw [htz, ← hxo, htx] at h1
    have := h1
    exact EReal.coe_le_coe_iff.1 this
  -- termwise `β^t F(z) ≥ ½(β^t F(x) + β^t F(y))`, strictly at `t₀`
  have hlt : ∑' t, (β ^ t * F (x t, x (t + 1)) + β ^ t * F (y t, y (t + 1))) / 2 <
      ∑' t, β ^ t * F (z t, z (t + 1)) := by
    refine Summable.tsum_lt_tsum (i := t₀) (fun t => ?_) ?_ ((hsx.add hsy).div_const 2) hsz
    · have := mul_le_mul_of_nonneg_left (hgain t) (pow_nonneg hβ0.le t)
      linarith
    · have := mul_lt_mul_of_pos_left hstrict (pow_pos hβ0 t₀)
      linarith
  have e : ∑' t, (β ^ t * F (x t, x (t + 1)) + β ^ t * F (y t, y (t + 1))) / 2 = ℓ := by
    rw [tsum_div_const, hsx.tsum_add hsy, hyℓ]; ring
  linarith

variable {l : ℕ} {Fx Fy : (Fin l → ℝ) → (Fin l → ℝ) → (Fin l → ℝ)}
  {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} {xbar : Fin l → ℝ}

/-- **Theorem 6.9.** -/
theorem theorem_6_9 {Γ : (Fin l → ℝ) → Set (Fin l → ℝ)} {F : (Fin l → ℝ) × (Fin l → ℝ) → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hconv : Convex ℝ {p : (Fin l → ℝ) × (Fin l → ℝ) | p.2 ∈ Γ p.1})
    (hconc : StrictConcaveOn ℝ {p : (Fin l → ℝ) × (Fin l → ℝ) | p.2 ∈ Γ p.1} F)
    {M : ℝ} (hM : ∀ p : (Fin l → ℝ) × (Fin l → ℝ), p.2 ∈ Γ p.1 → |F p| ≤ M)
    {B : ℝ} (hB : ∀ x, ∀ y ∈ Γ x, ‖y‖ ≤ B)
    (hint : {p : (Fin l → ℝ) × (Fin l → ℝ) | p.2 ∈ Γ p.1} ∈ 𝓝 (xbar, xbar))
    (hdiff : ∀ᶠ p in 𝓝 (xbar, xbar), HasFDerivAt F (lqD (Fx p.1 p.2) (Fy p.1 p.2)) p)
    (hFx : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fx p.1 p.2)
      (blockCLM Fxx Fxy) (xbar, xbar))
    (hFy : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fy p.1 p.2)
      (blockCLM Fxyᵀ Fyy) (xbar, xbar))
    (hstat : Fy xbar xbar + β • Fx xbar xbar = 0) (hQ : Fxy.det ≠ 0)
    (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ Fxx Fxy Fyy u v < 0)
    (hroots : (((eulerA Fxx Fxy Fyy β).charpoly.map Complex.ofRealHom).roots.filter
      fun μ => ‖μ‖ < 1).card = l) :
    ∃ U ∈ 𝓝 xbar, ∀ x₀ ∈ U, ∃ xs : ℕ → Fin l → ℝ, xs ∈ Feasible Γ x₀ ∧
      total (fun a b => F (a, b)) β xs = vstar Γ (fun a b => F (a, b)) β x₀ ∧
      (∀ y ∈ Feasible Γ x₀,
        total (fun a b => F (a, b)) β y = vstar Γ (fun a b => F (a, b)) β x₀ → y = xs) ∧
      Tendsto xs atTop (𝓝 xbar) := by
  set G := {p : (Fin l → ℝ) × (Fin l → ℝ) | p.2 ∈ Γ p.1}
  have hW : G ∩ {p | HasFDerivAt F (lqD (Fx p.1 p.2) (Fy p.1 p.2)) p} ∈ 𝓝 (xbar, xbar) :=
    inter_mem hint hdiff
  obtain ⟨U, hU, hpath⟩ := exists_convergent_euler_path hQ hβ0 hβ1 hneg hroots hstat hFx hFy hW
  refine ⟨U, hU, fun x₀ hx₀ => ?_⟩
  obtain ⟨xs, hx0, heul, hWt, hconvx⟩ := hpath x₀ hx₀
  have hfeas : xs ∈ Feasible Γ x₀ := ⟨hx0, fun t => (hWt t).1⟩
  -- Assumption 4.2 from bounded returns
  have h42 : Assumption42 Γ (fun a b => F (a, b)) β :=
    assumption42_of_summable_pos fun x₀ x hx =>
      summable_max_of_le_geometric hβ0.le hβ1 (le_max_right M 0) fun t => by
        rw [mul_comm (max M 0)]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((hM _ (hx.2 t)).trans
          (le_max_left _ _))) (pow_nonneg hβ0.le t)
  -- the gradient of `F` along the path is bounded
  have hFxc : ContinuousAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fx p.1 p.2) (xbar, xbar) :=
    hFx.continuousAt
  have hpt : Tendsto (fun t => (xs t, xs (t + 1))) atTop (𝓝 (xbar, xbar)) :=
    hconvx.prodMk_nhds (hconvx.comp (tendsto_add_atTop_nat 1))
  have hg : Tendsto (fun t => ∑ i, |Fx (xs t) (xs (t + 1)) i|) atTop
      (𝓝 (∑ i, |Fx xbar xbar i|)) := by
    have h := hFxc.tendsto.comp hpt
    simp only [Function.comp_def] at h
    exact tendsto_finsetSum _ fun i _ => (tendsto_pi_nhds.1 h i).abs
  obtain ⟨Gb, hGb⟩ := hg.bddAbove_range
  obtain ⟨Bx, hBx⟩ := hconvx.norm.bddAbove_range
  -- optimality
  set D : ℕ → (Fin l → ℝ) × (Fin l → ℝ) →L[ℝ] ℝ := fun t =>
    lqD (Fx (xs t) (xs (t + 1))) (Fy (xs t) (xs (t + 1)))
  have hopt : total (fun a b => F (a, b)) β xs = vstar Γ (fun a b => F (a, b)) β x₀ := by
    refine euler_sufficient h42 hfeas D (fun t x y hy => ?_) (fun t v => ?_) hβ0.le
      (fun y _ _ => ?_)
    · have := concave_le_fderiv hconc.concaveOn (hWt t).1 (show (x, y) ∈ G from hy) (hWt t).2
      exact this
    · have h := congrArg (· ⬝ᵥ v) (heul t)
      simp only [eulerG, add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h
      simp only [DeterministicDynamics.Fy, DeterministicDynamics.Fx, D, lqD_apply,
        dotProduct_zero, zero_add, add_zero]
      exact h
    · set G' := max Gb 0
      refine ⟨fun T => G' * (Bx + B) * β ^ (T + 1), ?_, fun T => ?_⟩
      · have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
          (tendsto_add_atTop_nat 1)).const_mul (G' * (Bx + B))
        simpa [Function.comp_def] using this
      · simp only [DeterministicDynamics.Fx, D, lqD_apply, dotProduct_zero, add_zero]
        have hd := (le_abs_self _).trans (abs_dot_le (Fx (xs (T + 1)) (xs (T + 1 + 1)))
          (xs (T + 1) - y (T + 1)))
        have hGT : ∑ i, |Fx (xs (T + 1)) (xs (T + 1 + 1)) i| ≤ G' :=
          (hGb ⟨T + 1, rfl⟩).trans (le_max_left _ _)
        have hn : ‖xs (T + 1) - y (T + 1)‖ ≤ Bx + B :=
          (norm_sub_le _ _).trans (add_le_add (hBx ⟨T + 1, rfl⟩) (hB _ _ (by
            rename_i hy _; exact hy.2 T)))
        have hG0 : 0 ≤ G' := le_max_right _ _
        have hβT := pow_nonneg hβ0.le (T + 1)
        have h3 := mul_le_mul hGT hn (norm_nonneg _) hG0
        nlinarith
  exact ⟨xs, hfeas, hopt, fun y hy hyo =>
    optimal_unique hβ0 hβ1 hconv hconc hM hfeas hy hopt hyo, hconvx⟩

end StokeyLucasPrescott.DeterministicDynamics
