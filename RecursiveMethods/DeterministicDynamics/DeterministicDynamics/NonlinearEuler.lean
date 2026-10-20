/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.EulerMap

/-!
# Convergent Euler paths near a stationary point

SLP §6.4, pp. 152–154, proof of Theorem 6.9. Apply the stable manifold construction
(`local_stable_family`) to the stacked Euler map `H` (`EulerMap`), whose Jacobian is `A`. The
stable manifold of `H` is (near `(x̄, x̄)`) a graph over the stable subspace `E_s`, which has
dimension `l`. The book then claims that the first `l × l` block of the derivative of `φ` has
full rank because `φ(x₁, x̄) = 0` only at `x₁ = x̄`; an isolated zero does not give a nonsingular
derivative. The step goes through when the second-order form of `F` at the steady state is
negative definite: then `(z₁, z₀) ↦ z₀` is injective on `E_s` (the linear–quadratic argument
`stable_real_inr_zero`), hence bijective, and we can solve for the point of the manifold with
prescribed `x₀` by a contraction (`exists_convergent_euler_path`).
-/

open Set Filter Topology Module
open scoped Matrix NNReal

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {Fx Fy : (Fin l → ℝ) → (Fin l → ℝ) → (Fin l → ℝ)}
  {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} {xbar : Fin l → ℝ}

/-- `‖Y ∘ inr‖ ≤ ‖Y‖`. -/
theorem norm_comp_inr_le (Y : Fin l ⊕ Fin l → ℝ) : ‖Y ∘ Sum.inr‖ ≤ ‖Y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm Y (Sum.inr i)

theorem norm_comp_inl_le (Y : Fin l ⊕ Fin l → ℝ) : ‖Y ∘ Sum.inl‖ ≤ ‖Y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm Y (Sum.inl i)

/-- **Convergent Euler paths.** With `F_xy` nonsingular, the second-order form negative
definite, and `l` characteristic roots of `A` inside the unit circle: for every neighborhood `W`
of `(x̄, x̄)` there is a neighborhood `U` of `x̄` such that from every `x₀ ∈ U` some path
satisfies the Euler equations, stays in `W` and converges to `x̄`. -/
theorem exists_convergent_euler_path (hQ : Fxy.det ≠ 0) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ Fxx Fxy Fyy u v < 0)
    (hroots : (((eulerA Fxx Fxy Fyy β).charpoly.map Complex.ofRealHom).roots.filter
      fun μ => ‖μ‖ < 1).card = l)
    (hstat : eulerG Fx Fy β (xbar, xbar, xbar) = 0)
    (hFx : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fx p.1 p.2)
      (blockCLM Fxx Fxy) (xbar, xbar))
    (hFy : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fy p.1 p.2)
      (blockCLM Fxyᵀ Fyy) (xbar, xbar))
    {W : Set ((Fin l → ℝ) × (Fin l → ℝ))} (hW : W ∈ 𝓝 (xbar, xbar)) :
    ∃ U ∈ 𝓝 xbar, ∀ x₀ ∈ U, ∃ x : ℕ → Fin l → ℝ, x 0 = x₀ ∧
      (∀ t, eulerG Fx Fy β (x t, x (t + 1), x (t + 2)) = 0) ∧
      (∀ t, (x t, x (t + 1)) ∈ W) ∧ Tendsto x atTop (𝓝 xbar) := by
  set A := eulerA Fxx Fxy Fyy β
  obtain ⟨ζ, hζ0, hζG, hζ⟩ := exists_eulerZeta hQ hβ0.ne' hstat hFx hFy
  have hH := hasStrictFDerivAt_stackH hζ
  set Ybar : Fin l ⊕ Fin l → ℝ := Sum.elim xbar xbar
  have hfix : stackH ζ Ybar = Ybar := by
    funext s; rcases s with i | i
    · change ζ (xbar, xbar) i = xbar i; rw [hζ0]
    · rfl
  obtain ⟨γ, hγ0, hγ1, C, hC0, δ, hδ, Z, hZP, hZb, horbit, hlipQ⟩ := local_stable_family hfix hH
  -- the projection `(z₁, z₀) ↦ z₀` on `E_s` is a bijection onto `ℝˡ`
  set L : stableR A →ₗ[ℝ] (Fin l → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inr).comp (stableR A).subtype
  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun ξ hξ => Subtype.ext ?_
    exact stable_real_inr_zero hneg hβ0 hβ1 hQ (fun i => congrFun hξ i)
      ((mem_stableR_iff A ξ).1 ξ.2)
  have hdim : finrank ℝ (stableR A) = finrank ℝ (Fin l → ℝ) := by
    rw [finrank_stableR, hroots, Module.finrank_fin_fun]
  have hLsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hLinj
  set Le := LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩
  set Linv : (Fin l → ℝ) →L[ℝ] (Fin l ⊕ Fin l → ℝ) :=
    LinearMap.toContinuousLinearMap ((stableR A).subtype ∘ₗ Le.symm.toLinearMap)
  set CL := ‖Linv‖
  have hLinv_mem : ∀ d, Linv d ∈ stableR A := fun d => (Le.symm d).2
  have hLinv_inr : ∀ d, Linv d ∘ Sum.inr = d := fun d => by
    have := Le.apply_symm_apply d
    exact this
  have hZ00 : Z 0 0 = 0 := by
    have := hZb 0 0
    simp only [norm_zero, mul_zero, zero_mul] at this
    exact norm_le_zero_iff.1 this
  set η := 1 / (2 * (CL + 1))
  have hCL : 0 ≤ CL := norm_nonneg _
  have hη : 0 < η := by positivity
  obtain ⟨δ', hδ', hlip⟩ := hlipQ η hη
  -- neighborhoods
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.1 (inter_mem hW hζG)
  set R := min (min δ δ') (ρ / (2 * (C + 1)))
  have hR : 0 < R := lt_min (lt_min hδ hδ') (by positivity)
  have hRδ : R ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hRδ' : R ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hRρ : C * R < ρ := by
    have h1 : R ≤ ρ / (2 * (C + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨Metric.ball xbar (R / (2 * (CL + 1))), Metric.ball_mem_nhds _ (by positivity),
    fun x₀ hx₀ => ?_⟩
  set d := x₀ - xbar
  have hd : ‖d‖ ≤ R / (2 * (CL + 1)) := by
    rw [Metric.mem_ball, dist_eq_norm] at hx₀; exact hx₀.le
  have hCLd : CL * ‖d‖ ≤ R / 2 := by
    rw [le_div_iff₀ (by positivity)] at hd
    have : CL * ‖d‖ * (2 * (CL + 1)) ≤ R * CL := by nlinarith [norm_nonneg d]
    nlinarith [norm_nonneg d]
  have hCLη : CL * η ≤ 1 / 2 := by
    simp only [η]; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- the contraction `T ξ = L⁻¹(d − (Q z₀(ξ))₀)`
  set T : (Fin l ⊕ Fin l → ℝ) → (Fin l ⊕ Fin l → ℝ) :=
    fun ξ => Linv (d - projU A (Z ξ 0) ∘ Sum.inr)
  set s := Metric.closedBall (0 : Fin l ⊕ Fin l → ℝ) R
  have hQ0 : ∀ ξ ∈ s, ‖projU A (Z ξ 0)‖ ≤ η * ‖ξ‖ := fun ξ hξ => by
    rw [Metric.mem_closedBall, dist_zero_right] at hξ
    have := hlip ξ 0 (hξ.trans hRδ') (by rw [norm_zero]; exact hδ'.le)
    rwa [hZ00, map_zero, sub_zero, sub_zero] at this
  have hsf : MapsTo T s s := fun ξ hξ => by
    have hξ' := hξ
    rw [Metric.mem_closedBall, dist_zero_right] at hξ ⊢
    refine (Linv.le_opNorm _).trans ?_
    have h1 : ‖d - projU A (Z ξ 0) ∘ Sum.inr‖ ≤ ‖d‖ + η * ‖ξ‖ :=
      (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_comp_inr_le _).trans (hQ0 ξ hξ')))
    have h2 := mul_le_mul_of_nonneg_left h1 hCL
    have h3 : CL * (η * ‖ξ‖) ≤ R / 2 := by
      have := mul_le_mul_of_nonneg_right hCLη (norm_nonneg ξ)
      nlinarith
    linarith
  have hTlip : ∀ ξ ∈ s, ∀ ξ' ∈ s, ‖T ξ - T ξ'‖ ≤ (1 / 2) * ‖ξ - ξ'‖ := fun ξ hξ ξ' hξ' => by
    have hξn : ‖ξ‖ ≤ δ' := by
      rw [Metric.mem_closedBall, dist_zero_right] at hξ; exact hξ.trans hRδ'
    have hξn' : ‖ξ'‖ ≤ δ' := by
      rw [Metric.mem_closedBall, dist_zero_right] at hξ'; exact hξ'.trans hRδ'
    have e : T ξ - T ξ' = Linv ((projU A (Z ξ' 0) - projU A (Z ξ 0)) ∘ Sum.inr) := by
      simp only [T, ← map_sub]; congr 1; funext i; simp
    rw [e]
    refine (Linv.le_opNorm _).trans ?_
    have h1 := (norm_comp_inr_le _).trans (hlip ξ' ξ hξn' hξn)
    rw [norm_sub_rev ξ' ξ] at h1
    have := mul_le_mul_of_nonneg_left h1 hCL
    have := mul_le_mul_of_nonneg_right hCLη (norm_nonneg (ξ - ξ'))
    nlinarith
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hsf.restrict T s s) :=
    ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a b => by
      simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
      simpa using hTlip a a.2 b b.2⟩
  obtain ⟨ξ, hξs, hξfix, -⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hsf hcontr (Metric.mem_closedBall_self hR.le)
    (edist_ne_top _ _)
  have hξfix' : T ξ = ξ := hξfix
  have hξR : ‖ξ‖ ≤ R := by rw [Metric.mem_closedBall, dist_zero_right] at hξs; exact hξs
  -- `ξ` is stable, and `z₀(ξ)` has second block `d`
  have hξst : ξ ∈ stableR A := by rw [← hξfix']; exact hLinv_mem _
  have hz0 : Z ξ 0 ∘ Sum.inr = d := by
    have h1 : Z ξ 0 = ξ + projU A (Z ξ 0) := by
      conv_lhs => rw [← projS_add_projU A (Z ξ 0)]
      rw [hZP, projS_of_mem A hξst]
    have h2 : ξ ∘ Sum.inr = d - projU A (Z ξ 0) ∘ Sum.inr := by
      conv_lhs => rw [← hξfix']
      exact hLinv_inr _
    funext i
    have := congrFun h2 i
    simp only [Function.comp_apply, Pi.sub_apply] at this
    rw [Function.comp_apply, h1, Pi.add_apply, this]
    ring
  -- the orbit of `H` and the path
  set Yt : ℕ → Fin l ⊕ Fin l → ℝ := fun t => Ybar + Z ξ t
  have hYt : ∀ t, Yt (t + 1) = stackH ζ (Yt t) := fun t => by
    simp only [Yt]
    rw [← horbit ξ (hξR.trans hRδ) (t + 1), ← horbit ξ (hξR.trans hRδ) t,
      Function.iterate_succ_apply']
  set x : ℕ → Fin l → ℝ := fun t => Yt t ∘ Sum.inr
  have hx1 : ∀ t, x (t + 1) = Yt t ∘ Sum.inl := fun t => by
    simp only [x]; rw [hYt]; rfl
  have hx2 : ∀ t, x (t + 2) = ζ (x t, x (t + 1)) := fun t => by
    rw [hx1 (t + 1), hYt, hx1 t]; rfl
  have hZt : ∀ t, ‖Z ξ t‖ ≤ C * R := fun t => (hZb ξ t).trans (by
    have := pow_le_one₀ hγ0.le hγ1.le (n := t)
    have := mul_le_mul_of_nonneg_left hξR hC0
    nlinarith [norm_nonneg ξ, mul_nonneg hC0 (norm_nonneg ξ)])
  have hpair : ∀ t, (x t, x (t + 1)) ∈ W ∩ {p | eulerG Fx Fy β (p.1, p.2, ζ p) = 0} :=
    fun t => hρN (by
      rw [Metric.mem_ball, Prod.dist_eq, hx1]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm]
        have : x t - xbar = Z ξ t ∘ Sum.inr := by funext i; simp [x, Yt, Ybar]
        rw [this]; exact ((norm_comp_inr_le _).trans (hZt t)).trans_lt hRρ
      · rw [dist_eq_norm]
        have : Yt t ∘ Sum.inl - xbar = Z ξ t ∘ Sum.inl := by funext i; simp [Yt, Ybar]
        rw [this]; exact ((norm_comp_inl_le _).trans (hZt t)).trans_lt hRρ)
  refine ⟨x, ?_, fun t => ?_, fun t => (hpair t).1, ?_⟩
  · funext i
    have := congrFun hz0 i
    simp only [Function.comp_apply] at this
    simp [x, Yt, Ybar, this, d]
  · rw [hx2]; exact (hpair t).2
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).const_mul (C * ‖ξ‖)
    rw [mul_zero] at hlim
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hlim
    have : x t - xbar = Z ξ t ∘ Sum.inr := by funext i; simp [x, Yt, Ybar]
    rw [this]
    exact (norm_comp_inr_le _).trans (hZb ξ t)

end StokeyLucasPrescott.DeterministicDynamics
