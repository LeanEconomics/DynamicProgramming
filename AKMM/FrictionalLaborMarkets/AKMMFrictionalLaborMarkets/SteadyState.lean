/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.Matching
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The steady state and the transition dynamics of the DMP model

AKMM, §20.4.2, pp. 601–602, with footnotes 6–7. With constant productivity `z` the job-creation
equation (20.16) is the first-order difference equation
`κ/((1 − γ)λ_f(θ_t)) = β[z − b + (1 − σ − γλ_w(θ_{t+1}))/(1 − γ) · κ/λ_f(θ_{t+1})]`
(`jcLHS θ_t = β · jcRHS θ_{t+1}`).

* `eq_20_17`, `ss_phi_strictAntiOn`, `ss_unique`: multiplying (20.17) by `λ_f(θ̄)` gives
  `jcPhi(θ̄) = 0` with `jcPhi` strictly decreasing when `z > b`, so there is at most one steady
  state.
* `ss_exists`, `ss_exists_of_tendsto`, `ss_cd_existsUnique`: existence, which the book does not
  argue, holds if `λ_f` is continuous, `λ_f(θ) → 0` as `θ → ∞` and the steady-state map is
  positive somewhere (for instance if `λ_f → ∞` as `θ → 0`); the Cobb–Douglas case (20.23) has a
  unique steady state for every `z > b`.
* `ss_theta_mono_z`, `ss_ubar_strictAntiOn`, `ss_vbar_strictMonoOn`: a fall in `z` lowers `θ̄`,
  raises `ū` and lowers `v̄ = θ̄ū` (Figure 20.5, p. 602).
* Footnote 6: `fn6_rhs_hasDerivAt`, `fn6_rhs_strictMonoOn`: with `η = −θλ_f′/λ_f` the right side
  of (20.16) has derivative `κ((1 − σ)η − γλ_w)/((1 − γ)λ_w)`, so it is increasing where
  `(1 − σ)η − γλ_w > 0`, and then `θ_{t+1}` is an increasing function of `θ_t`
  (`fn6_next_strictMono`).
* Footnote 7: `fn7_slope`, `fn7_slope_gt_one`: at `θ̄`, `dθ_{t+1}/dθ_t = η/(β((1 − σ)η − γλ_w))`,
  which exceeds `1`; `fn7_diverge_above`, `fn7_diverge_below`, `fn7_jump`: any path with
  `θ_0 ≠ θ̄` moves monotonically away from `θ̄`, so the only path converging to `θ̄` is the
  constant one, and after a permanent shock `θ` jumps at once to its new steady state.

Departures: existence of `θ̄` is proved under the stated limit conditions (the book asserts it);
the divergence of footnote 7 is proved globally from the monotonicity of footnote 6 on an interval
containing the path, rather than from the local slope.
-/

namespace AKMM.FrictionalLaborMarkets

open Filter Topology

/-- The left side of (20.16), `κ/((1 − γ)λ_f(θ))`. -/
noncomputable def jcLHS (MF : MatchFn) (κ γ θ : ℝ) : ℝ := κ / ((1 - γ) * lamF MF θ)

/-- The bracket on the right side of (20.16), `z − b + (1 − σ − γλ_w(θ))/(1 − γ) · κ/λ_f(θ)`. -/
noncomputable def jcRHS (MF : MatchFn) (z b σ γ κ θ : ℝ) : ℝ :=
  z - b + (1 - σ - γ * lamW MF θ) / (1 - γ) * (κ / lamF MF θ)

/-- (20.17) multiplied by `λ_f(θ)`: `β[(z − b)λ_f(θ) + (1 − σ − γλ_w(θ))κ/(1 − γ)] − κ/(1 − γ)`. -/
noncomputable def jcPhi (MF : MatchFn) (z b σ γ κ β θ : ℝ) : ℝ :=
  β * ((z - b) * lamF MF θ + (1 - σ - γ * lamW MF θ) * κ / (1 - γ)) - κ / (1 - γ)

/-- The identity behind p. 601: `λ_f(θ)(β·jcRHS(θ) − jcLHS(θ)) = jcPhi(θ)`. -/
theorem ss_phi_eq (MF : MatchFn) {z b σ γ κ β θ : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ) :
    lamF MF θ * (β * jcRHS MF z b σ γ κ θ - jcLHS MF κ γ θ) = jcPhi MF z b σ γ κ β θ := by
  have hl := match_lamF_pos MF hθ
  have hγ : (1 - γ) ≠ 0 := by linarith
  unfold jcRHS jcLHS jcPhi
  field_simp

/-- AKMM, (20.17), p. 601: `θ̄` is a steady state of (20.16) iff `jcPhi(θ̄) = 0` ("multiplying by
`λ_f(θ̄)` on both sides"). -/
theorem eq_20_17 (MF : MatchFn) {z b σ γ κ β θ : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ) :
    jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ θ ↔ jcPhi MF z b σ γ κ β θ = 0 := by
  have hl := match_lamF_pos MF hθ
  rw [← ss_phi_eq MF hγ1 hθ, mul_eq_zero, or_iff_right hl.ne', sub_eq_zero, eq_comm]

/-- AKMM, p. 601: the right side of (20.17) multiplied by `λ_f` is decreasing in `θ`: `jcPhi` is
strictly decreasing (when `z > b`, `κ, β > 0`, `γ ∈ [0, 1)`). -/
theorem ss_phi_strictAntiOn (MF : MatchFn) {z b σ γ κ β : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    StrictAntiOn (jcPhi MF z b σ γ κ β) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hf := match_lamF_strictAntiOn MF hx hy hxy
  have hw := match_lamW_strictMonoOn MF hx hy hxy
  have h1γ : 0 < 1 - γ := by linarith
  unfold jcPhi
  have e1 : (z - b) * lamF MF y < (z - b) * lamF MF x := mul_lt_mul_of_pos_left hf (by linarith)
  have e2 : (1 - σ - γ * lamW MF y) * κ / (1 - γ) ≤ (1 - σ - γ * lamW MF x) * κ / (1 - γ) := by
    apply div_le_div_of_nonneg_right _ h1γ.le
    apply mul_le_mul_of_nonneg_right _ hκ.le
    nlinarith
  nlinarith

/-- AKMM, p. 601: (20.17) has at most one solution `θ̄ > 0`. -/
theorem ss_unique (MF : MatchFn) {z b σ γ κ β θ₁ θ₂ : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (h₁ : jcLHS MF κ γ θ₁ = β * jcRHS MF z b σ γ κ θ₁)
    (h₂ : jcLHS MF κ γ θ₂ = β * jcRHS MF z b σ γ κ θ₂) : θ₁ = θ₂ := by
  rw [eq_20_17 MF hγ1 hθ₁] at h₁
  rw [eq_20_17 MF hγ1 hθ₂] at h₂
  exact (ss_phi_strictAntiOn MF hzb hκ hβ hγ0 hγ1).injOn hθ₁ hθ₂ (h₁.trans h₂.symm)

/-- AKMM, p. 601 (existence, added): if `λ_f` is continuous on `θ > 0`, `λ_f(θ) → 0` as `θ → ∞`,
`β(1 − σ) < 1`, and `jcPhi(θ₁) ≥ 0` at some `θ₁ > 0`, then (20.17) has a solution `θ̄ ≥ θ₁`. -/
theorem ss_exists (MF : MatchFn) {z b σ γ κ β θ₁ : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hσ : 0 ≤ σ) (hβ1 : β < 1)
    (hc : ContinuousOn (lamF MF) (Set.Ioi 0)) (hlim : Tendsto (lamF MF) atTop (𝓝 0))
    (hθ₁ : 0 < θ₁) (h₁ : 0 ≤ jcPhi MF z b σ γ κ β θ₁) :
    ∃ θ, θ₁ ≤ θ ∧ jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ θ := by
  have h1γ : 0 < 1 - γ := by linarith
  -- a point where `jcPhi < 0`
  set ε := (1 - β * (1 - σ)) * κ / (1 - γ) / (2 * β * (z - b) + 1) with hε
  have hεp : 0 < ε := by
    have : 0 < 1 - β * (1 - σ) := by nlinarith
    positivity
  obtain ⟨θ₂, hθ₂⟩ := (eventually_atTop.mp ((hlim.eventually (gt_mem_nhds hεp)).and
    (eventually_gt_atTop θ₁)))
  obtain ⟨hθ₂ε, hθ₂1⟩ := hθ₂ θ₂ le_rfl
  have hθ₂p : 0 < θ₂ := hθ₁.trans hθ₂1
  have hneg : jcPhi MF z b σ γ κ β θ₂ < 0 := by
    have hw := match_lamW_pos MF hθ₂p
    have hf := match_lamF_pos MF hθ₂p
    unfold jcPhi
    have e1 : (1 - σ - γ * lamW MF θ₂) * κ / (1 - γ) ≤ (1 - σ) * κ / (1 - γ) := by
      apply div_le_div_of_nonneg_right _ h1γ.le
      nlinarith [mul_nonneg (mul_nonneg hγ0 hw.le) hκ.le]
    have e2 : (z - b) * lamF MF θ₂ ≤ (z - b) * ε := by nlinarith
    have e3 : β * ((z - b) * ε) < (1 - β * (1 - σ)) * κ / (1 - γ) := by
      rw [hε]
      have hA : 0 < (1 - β * (1 - σ)) * κ / (1 - γ) := by
        have : 0 < 1 - β * (1 - σ) := by nlinarith
        positivity
      rw [show β * ((z - b) * ((1 - β * (1 - σ)) * κ / (1 - γ) / (2 * β * (z - b) + 1))) =
        (1 - β * (1 - σ)) * κ / (1 - γ) * (β * (z - b) / (2 * β * (z - b) + 1)) by ring]
      have : β * (z - b) / (2 * β * (z - b) + 1) < 1 := by
        rw [div_lt_one (by nlinarith)]; nlinarith
      nlinarith
    have e4 : β * ((1 - σ) * κ / (1 - γ)) - κ / (1 - γ) = -((1 - β * (1 - σ)) * κ / (1 - γ)) := by
      ring
    nlinarith
  have hcont : ContinuousOn (jcPhi MF z b σ γ κ β) (Set.Icc θ₁ θ₂) := by
    have hcf : ContinuousOn (lamF MF) (Set.Icc θ₁ θ₂) :=
      hc.mono fun x hx ↦ lt_of_lt_of_le hθ₁ hx.1
    have hcw : ContinuousOn (lamW MF) (Set.Icc θ₁ θ₂) := by
      have : ContinuousOn (fun x ↦ x * lamF MF x) (Set.Icc θ₁ θ₂) := continuousOn_id.mul hcf
      refine this.congr fun x hx ↦ ?_
      exact match_lamW_eq MF (lt_of_lt_of_le hθ₁ hx.1)
    unfold jcPhi
    fun_prop
  obtain ⟨θ, hθ, heq⟩ := isPreconnected_Icc.intermediate_value₂ (Set.left_mem_Icc.mpr hθ₂1.le)
    (Set.right_mem_Icc.mpr hθ₂1.le) continuousOn_const hcont h₁ hneg.le
  exact ⟨θ, hθ.1, (eq_20_17 MF hγ1 (hθ₁.trans_le hθ.1)).mpr heq.symm⟩

/-- AKMM, p. 601 (existence, added): if moreover `λ_f(θ) → ∞` as `θ → 0⁺` (as for Cobb–Douglas
matching), (20.17) has a solution. -/
theorem ss_exists_of_tendsto (MF : MatchFn) {z b σ γ κ β : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hβ1 : β < 1)
    (hc : ContinuousOn (lamF MF) (Set.Ioi 0)) (hlim : Tendsto (lamF MF) atTop (𝓝 0))
    (hlim0 : Tendsto (lamF MF) (𝓝[>] 0) atTop) :
    ∃ θ, 0 < θ ∧ jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ θ := by
  have h1γ : 0 < 1 - γ := by linarith
  set C := (κ / (1 - γ) + β * γ * lamW MF 1 * κ / (1 - γ) + 1) / (β * (z - b)) with hC
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), C ≤ lamF MF θ ∧ θ ∈ Set.Ioo 0 1 :=
    (hlim0.eventually (eventually_ge_atTop C)).and (Ioo_mem_nhdsGT one_pos)
  obtain ⟨θ₁, hθ₁C, hθ₁0, hθ₁1⟩ := hev.exists
  have hphi : 0 ≤ jcPhi MF z b σ γ κ β θ₁ := by
    have hw : lamW MF θ₁ ≤ lamW MF 1 :=
      (match_lamW_strictMonoOn MF (Set.mem_Ioi.mpr hθ₁0) (Set.mem_Ioi.mpr one_pos) hθ₁1).le
    have hw0 := match_lamW_pos MF hθ₁0
    unfold jcPhi
    have hbz : 0 < β * (z - b) := by nlinarith
    have hCf : β * (z - b) * C ≤ β * (z - b) * lamF MF θ₁ :=
      mul_le_mul_of_nonneg_left hθ₁C hbz.le
    rw [hC, mul_div_cancel₀ _ hbz.ne'] at hCf
    have e : β * ((1 - σ - γ * lamW MF θ₁) * κ / (1 - γ)) ≥
        -(β * γ * lamW MF 1 * κ / (1 - γ)) + β * ((1 - σ) * κ / (1 - γ)) := by
      have hg : γ * lamW MF θ₁ ≤ γ * lamW MF 1 := mul_le_mul_of_nonneg_left hw hγ0
      have : β * ((1 - σ - γ * lamW MF θ₁) * κ / (1 - γ)) - β * ((1 - σ) * κ / (1 - γ)) =
          -(β * (γ * lamW MF θ₁) * κ / (1 - γ)) := by ring
      have : β * (γ * lamW MF θ₁) * κ / (1 - γ) ≤ β * γ * lamW MF 1 * κ / (1 - γ) := by
        apply div_le_div_of_nonneg_right _ h1γ.le
        have := mul_le_mul_of_nonneg_left hg hβ.le
        nlinarith
      linarith
    have : 0 ≤ β * ((1 - σ) * κ / (1 - γ)) := by
      have : 0 ≤ 1 - σ := by linarith
      positivity
    nlinarith
  obtain ⟨θ, hθ, h⟩ := ss_exists MF hzb hκ hβ hγ0 hγ1 hσ hβ1 hc hlim hθ₁0 hphi
  exact ⟨θ, hθ₁0.trans_le hθ, h⟩

/-- The Cobb–Douglas `λ_f(θ) = χθ^{−η}` is continuous, tends to `0` as `θ → ∞` and to `∞` as
`θ → 0⁺`. -/
theorem ss_cd_lamF_limits {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) :
    ContinuousOn (lamF (cdMatch χ η hχ hη0 hη1)) (Set.Ioi 0) ∧
      Tendsto (lamF (cdMatch χ η hχ hη0 hη1)) atTop (𝓝 0) ∧
      Tendsto (lamF (cdMatch χ η hχ hη0 hη1)) (𝓝[>] 0) atTop := by
  have heq : ∀ θ ∈ Set.Ioi (0 : ℝ), χ * θ ^ (-η) = lamF (cdMatch χ η hχ hη0 hη1) θ :=
    fun θ hθ ↦ ((eq_20_23 hχ hη0 hη1 hθ).2).symm
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.congr (f := fun θ ↦ χ * θ ^ (-η)) ?_ fun θ hθ ↦ (heq θ hθ).symm
    exact continuousOn_const.mul (fun θ hθ ↦
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hθ))).continuousWithinAt)
  · have h := (tendsto_rpow_neg_atTop hη0).const_mul χ
    rw [mul_zero] at h
    exact h.congr' ((eventually_gt_atTop 0).mono fun θ hθ ↦ heq θ hθ)
  · have h := (tendsto_rpow_neg_nhdsGT_zero (by linarith : -η < 0)).const_mul_atTop hχ
    exact h.congr' (eventually_nhdsWithin_of_forall fun θ hθ ↦ heq θ hθ)

/-- AKMM, (20.17), p. 601, with Cobb–Douglas matching (20.23): for every `z > b` there is exactly
one steady state `θ̄ > 0`. -/
theorem ss_cd_existsUnique {χ η z b σ γ κ β : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃! θ, 0 < θ ∧ jcLHS (cdMatch χ η hχ hη0 hη1) κ γ θ =
      β * jcRHS (cdMatch χ η hχ hη0 hη1) z b σ γ κ θ := by
  obtain ⟨hc, hlim, hlim0⟩ := ss_cd_lamF_limits hχ hη0 hη1
  obtain ⟨θ, hθ, h⟩ := ss_exists_of_tendsto _ hzb hκ hβ hγ0 hγ1 hσ hσ1 hβ1 hc hlim hlim0
  exact ⟨θ, ⟨hθ, h⟩, fun θ' ⟨hθ', h'⟩ ↦ ss_unique _ hzb hκ hβ hγ0 hγ1 hθ' hθ h' h⟩

/-- AKMM, p. 602 (Figure 20.5): when `z` goes down, `θ̄` goes down: steady states are strictly
increasing in `z`. -/
theorem ss_theta_mono_z (MF : MatchFn) {z₁ z₂ b σ γ κ β θ₁ θ₂ : ℝ} (hz : z₁ < z₂)
    (hzb : b < z₁) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : jcLHS MF κ γ θ₁ = β * jcRHS MF z₁ b σ γ κ θ₁)
    (h₂ : jcLHS MF κ γ θ₂ = β * jcRHS MF z₂ b σ γ κ θ₂) : θ₁ < θ₂ := by
  rw [eq_20_17 MF hγ1 hθ₁] at h₁
  rw [eq_20_17 MF hγ1 hθ₂] at h₂
  have hl := match_lamF_pos MF hθ₁
  have hgt : 0 < jcPhi MF z₂ b σ γ κ β θ₁ := by
    have : jcPhi MF z₂ b σ γ κ β θ₁ - jcPhi MF z₁ b σ γ κ β θ₁ = β * (z₂ - z₁) * lamF MF θ₁ := by
      unfold jcPhi; ring
    have : 0 < β * (z₂ - z₁) * lamF MF θ₁ := by have := sub_pos.mpr hz; positivity
    linarith
  by_contra hcon
  rcases (not_lt.mp hcon).lt_or_eq with hlt | heq
  · have := ss_phi_strictAntiOn MF (σ := σ) (hzb.trans hz) hκ hβ hγ0 hγ1 hθ₂ hθ₁ hlt
    linarith
  · rw [heq] at h₂; linarith

/-- AKMM, p. 602 (Figure 20.5): steady-state unemployment `ū = σ/(λ_w(θ̄) + σ)` is strictly
decreasing in `θ̄`. -/
theorem ss_ubar_strictAntiOn (MF : MatchFn) {σ : ℝ} (hσ : 0 < σ) :
    StrictAntiOn (fun θ ↦ σ / (lamW MF θ + σ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have := match_lamW_strictMonoOn MF hx hy hxy
  have := match_lamW_pos MF hx
  exact div_lt_div_of_pos_left hσ (by linarith) (by linarith)

/-- AKMM, p. 602 (Figure 20.5): steady-state vacancies `v̄ = θ̄ū` are strictly increasing in
`θ̄`; with `ss_theta_mono_z`, a fall in `z` gives smaller `v` and larger `u`. -/
theorem ss_vbar_strictMonoOn (MF : MatchFn) {σ : ℝ} (hσ : 0 < σ) :
    StrictMonoOn (fun θ ↦ θ * (σ / (lamW MF θ + σ))) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hf := match_lamF_strictAntiOn MF hx hy hxy
  have hfy := match_lamF_pos MF hy0
  have hfx := match_lamF_pos MF hx0
  simp only
  rw [match_lamW_eq MF hx0, match_lamW_eq MF hy0, ← mul_div_assoc, ← mul_div_assoc,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos hx0 hy0) (sub_pos.mpr hf), mul_pos hσ (sub_pos.mpr hxy)]

/-- AKMM, footnote 6, p. 602: if `λ_f` has derivative `d` at `θ > 0`, the left side of (20.16)
has derivative `κη/((1 − γ)λ_w(θ))` with `η = −θd/λ_f(θ)`. -/
theorem fn6_lhs_hasDerivAt (MF : MatchFn) {κ γ θ d : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ)
    (hd : HasDerivAt (lamF MF) d θ) :
    HasDerivAt (jcLHS MF κ γ) (κ * (-θ * d / lamF MF θ) / ((1 - γ) * lamW MF θ)) θ := by
  have hl := match_lamF_pos MF hθ
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h := (hasDerivAt_const θ κ).div (hd.const_mul (1 - γ)) (by positivity)
  refine h.congr_deriv ?_
  rw [match_lamW_eq MF hθ]
  field_simp
  ring

/-- AKMM, footnote 6, p. 602: if `λ_f` has derivative `d` at `θ > 0`, the right side of (20.16)
has derivative `κ((1 − σ)η − γλ_w(θ))/((1 − γ)λ_w(θ))` with `η = −θd/λ_f(θ)`. -/
theorem fn6_rhs_hasDerivAt (MF : MatchFn) {z b σ γ κ θ d : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ)
    (hd : HasDerivAt (lamF MF) d θ) :
    HasDerivAt (jcRHS MF z b σ γ κ)
      (κ * ((1 - σ) * (-θ * d / lamF MF θ) - γ * lamW MF θ) / ((1 - γ) * lamW MF θ)) θ := by
  have hl := match_lamF_pos MF hθ
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h1 := ((hd.inv hl.ne').const_mul ((1 - σ) * κ / (1 - γ))).const_add (z - b)
  have h2 := h1.sub ((hasDerivAt_id θ).const_mul (γ * κ / (1 - γ)))
  have heq : (fun x ↦ z - b + (1 - σ) * κ / (1 - γ) * (lamF MF x)⁻¹ - γ * κ / (1 - γ) * id x)
      =ᶠ[𝓝 θ] jcRHS MF z b σ γ κ := by
    filter_upwards [lt_mem_nhds hθ] with x hx
    have hlx := match_lamF_pos MF hx
    rw [jcRHS, match_lamW_eq MF hx]
    simp only [id]
    field_simp
    ring
  refine (h2.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [match_lamW_eq MF hθ]
  field_simp

/-- AKMM, footnote 6, p. 602: where `(1 − σ)η(θ) − γλ_w(θ) > 0` on an interval, the right side
of (20.16) is strictly increasing there. -/
theorem fn6_rhs_strictMonoOn (MF : MatchFn) {z b σ γ κ a c : ℝ} (hκ : 0 < κ) (hγ1 : γ < 1)
    (ha : 0 ≤ a) {d : ℝ → ℝ} (hd : ∀ θ ∈ Set.Ioo a c, HasDerivAt (lamF MF) (d θ) θ)
    (hcond : ∀ θ ∈ Set.Ioo a c, 0 < (1 - σ) * (-θ * d θ / lamF MF θ) - γ * lamW MF θ) :
    StrictMonoOn (jcRHS MF z b σ γ κ) (Set.Ioo a c) := by
  have hpos : ∀ θ ∈ Set.Ioo a c, 0 < θ := fun θ hθ ↦ lt_of_le_of_lt ha hθ.1
  have hder : ∀ θ ∈ Set.Ioo a c, HasDerivAt (jcRHS MF z b σ γ κ)
      (κ * ((1 - σ) * (-θ * d θ / lamF MF θ) - γ * lamW MF θ) / ((1 - γ) * lamW MF θ)) θ :=
    fun θ hθ ↦ fn6_rhs_hasDerivAt MF hγ1 (hpos θ hθ) (hd θ hθ)
  refine strictMonoOn_of_deriv_pos (convex_Ioo a c)
    (fun θ hθ ↦ (hder θ hθ).continuousAt.continuousWithinAt) fun θ hθ ↦ ?_
  rw [interior_Ioo] at hθ
  rw [(hder θ hθ).deriv]
  have := match_lamW_pos MF (hpos θ hθ)
  have := hcond θ hθ
  have : 0 < 1 - γ := by linarith
  positivity

/-- AKMM, p. 601: the left side of (20.16) is strictly increasing in `θ_t`. -/
theorem ss_lhs_strictMonoOn (MF : MatchFn) {κ γ : ℝ} (hκ : 0 < κ) (hγ1 : γ < 1) :
    StrictMonoOn (jcLHS MF κ γ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hf := match_lamF_strictAntiOn MF hx hy hxy
  have := match_lamF_pos MF hy
  have : 0 < 1 - γ := by linarith
  unfold jcLHS
  exact div_lt_div_of_pos_left hκ (by positivity) (by nlinarith)

/-- AKMM, footnote 7, p. 602: where the right side of (20.16) is increasing (footnote 6),
`θ_{t+1}` is an increasing function of `θ_t`. -/
theorem fn6_next_strictMono (MF : MatchFn) {z b σ γ κ β : ℝ} {I : Set ℝ} (hκ : 0 < κ)
    (hγ1 : γ < 1) (hβ : 0 < β) (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I)
    {θ θ' φ φ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (hφ : φ ∈ I) (hφ' : φ' ∈ I)
    (h : jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ φ)
    (h' : jcLHS MF κ γ θ' = β * jcRHS MF z b σ γ κ φ') (hlt : θ < θ') : φ < φ' := by
  have := ss_lhs_strictMonoOn MF hκ hγ1 hθ hθ' hlt
  rw [h, h'] at this
  exact (hmono.lt_iff_lt hφ hφ').mp (lt_of_mul_lt_mul_left this hβ.le)

/-- AKMM, footnote 7, p. 602: if the transition `θ_t ↦ θ_{t+1} = φ(θ_t)` is differentiable at the
steady state, its slope is `L/(βR)`, `L` and `R` the derivatives of the two sides of (20.16). -/
theorem fn7_slope (MF : MatchFn) {z b σ γ κ β θ L R φ' : ℝ} {φ : ℝ → ℝ} (hβ : β ≠ 0)
    (hR : R ≠ 0) (hφ : HasDerivAt φ φ' θ) (hfix : φ θ = θ)
    (hL : HasDerivAt (jcLHS MF κ γ) L θ) (hRd : HasDerivAt (jcRHS MF z b σ γ κ) R θ)
    (hpath : ∀ᶠ x in 𝓝 θ, jcLHS MF κ γ x = β * jcRHS MF z b σ γ κ (φ x)) :
    φ' = L / (β * R) := by
  have hR' : HasDerivAt (jcRHS MF z b σ γ κ) R (φ θ) := by rwa [hfix]
  have h := (hR'.comp θ hφ).const_mul β
  have h2 := hL.congr_of_eventuallyEq (hpath.mono fun x hx ↦ hx.symm)
  have := h2.unique h
  rw [eq_div_iff (mul_ne_zero hβ hR), this]
  ring

/-- AKMM, footnote 7, p. 602: at the steady state, `dθ_{t+1}/dθ_t = η/(β((1 − σ)η − γλ_w)) > 1`
when `(1 − σ)η − γλ_w > 0` (footnote 6), `β ∈ (0, 1)`, `σ ≥ 0` and `γλ_w ≥ 0`. -/
theorem fn7_slope_gt_one {η σ γ lw β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    (hγ : 0 ≤ γ * lw) (hη : 0 < η) (hcond : 0 < (1 - σ) * η - γ * lw) :
    1 < η / (β * ((1 - σ) * η - γ * lw)) := by
  rw [one_lt_div (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hβ1 hcond, mul_nonneg hσ hη.le]

/-- AKMM, footnote 7, p. 602, the steady-state slope as a quotient of the derivatives of
footnote 6: `(κη/((1 − γ)λ_w))/(β · κ((1 − σ)η − γλ_w)/((1 − γ)λ_w)) =
η/(β((1 − σ)η − γλ_w))`. -/
theorem fn7_slope_eq {κ η σ γ lw β : ℝ} (hκ : 0 < κ) (hγ1 : γ < 1) (hlw : 0 < lw)
    (hβ : 0 < β) :
    κ * η / ((1 - γ) * lw) / (β * (κ * ((1 - σ) * η - γ * lw) / ((1 - γ) * lw))) =
      η / (β * ((1 - σ) * η - γ * lw)) := by
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

/-- One step of the divergence of footnote 7: above the steady state, `θ_{t+1} > θ_t`. -/
theorem fn7_step_above (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hpath : jcLHS MF κ γ x = β * jcRHS MF z b σ γ κ y) (hxb : θbar < x) : x < y := by
  have hx0 : 0 < x := hI hx
  have hphi := ss_phi_strictAntiOn MF (σ := σ) hzb hκ hβ hγ0 hγ1 (Set.mem_Ioi.mpr hbar)
    (Set.mem_Ioi.mpr hx0) hxb
  rw [(eq_20_17 MF hγ1 hbar).mp hss, ← ss_phi_eq MF hγ1 hx0] at hphi
  have hl := match_lamF_pos MF hx0
  have h1 : β * jcRHS MF z b σ γ κ x < β * jcRHS MF z b σ γ κ y := by
    rw [← hpath]; nlinarith
  exact (hmono.lt_iff_lt hx hy).mp (lt_of_mul_lt_mul_left h1 hβ.le)

/-- One step of the divergence of footnote 7: below the steady state, `θ_{t+1} < θ_t`. -/
theorem fn7_step_below (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hpath : jcLHS MF κ γ x = β * jcRHS MF z b σ γ κ y) (hxb : x < θbar) : y < x := by
  have hx0 : 0 < x := hI hx
  have hphi := ss_phi_strictAntiOn MF (σ := σ) hzb hκ hβ hγ0 hγ1 (Set.mem_Ioi.mpr hx0)
    (Set.mem_Ioi.mpr hbar) hxb
  rw [(eq_20_17 MF hγ1 hbar).mp hss, ← ss_phi_eq MF hγ1 hx0] at hphi
  have hl := match_lamF_pos MF hx0
  have h1 : β * jcRHS MF z b σ γ κ y < β * jcRHS MF z b σ γ κ x := by
    rw [← hpath]; nlinarith
  exact (hmono.lt_iff_lt hy hx).mp (lt_of_mul_lt_mul_left h1 hβ.le)

/-- AKMM, footnote 7, p. 602: a path of (20.16) staying in a set `I` where the right side is
increasing, and starting above `θ̄`, increases strictly and stays above `θ̄`. -/
theorem fn7_diverge_above (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {θ : ℕ → ℝ} (hθI : ∀ t, θ t ∈ I)
    (hpath : ∀ t, jcLHS MF κ γ (θ t) = β * jcRHS MF z b σ γ κ (θ (t + 1)))
    (h0 : θbar < θ 0) : StrictMono θ ∧ ∀ t, θbar < θ t := by
  have hall : ∀ t, θbar < θ t := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => exact ih.trans (fn7_step_above MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss
        (hθI n) (hθI (n + 1)) (hpath n) ih)
  exact ⟨strictMono_nat_of_lt_succ fun n ↦ fn7_step_above MF hI hzb hκ hβ hγ0 hγ1 hmono hbar
    hss (hθI n) (hθI (n + 1)) (hpath n) (hall n), hall⟩

/-- AKMM, footnote 7, p. 602: a path starting below `θ̄` decreases strictly and stays below. -/
theorem fn7_diverge_below (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {θ : ℕ → ℝ} (hθI : ∀ t, θ t ∈ I)
    (hpath : ∀ t, jcLHS MF κ γ (θ t) = β * jcRHS MF z b σ γ κ (θ (t + 1)))
    (h0 : θ 0 < θbar) : StrictAnti θ ∧ ∀ t, θ t < θbar := by
  have hall : ∀ t, θ t < θbar := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => exact (fn7_step_below MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss
        (hθI n) (hθI (n + 1)) (hpath n) ih).trans ih
  exact ⟨strictAnti_nat_of_succ_lt fun n ↦ fn7_step_below MF hI hzb hκ hβ hγ0 hγ1 hmono hbar
    hss (hθI n) (hθI (n + 1)) (hpath n) (hall n), hall⟩

/-- AKMM, p. 602 and footnote 7: the only path of (20.16) in `I` converging to `θ̄` is the
constant path; so after a permanent change in `z`, `θ` must jump at once to the new `θ̄`. -/
theorem fn7_jump (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {θ : ℕ → ℝ} (hθI : ∀ t, θ t ∈ I)
    (hpath : ∀ t, jcLHS MF κ γ (θ t) = β * jcRHS MF z b σ γ κ (θ (t + 1)))
    (hlim : Tendsto θ atTop (𝓝 θbar)) (t : ℕ) : θ t = θbar := by
  -- the shifted path has the same properties; show its first term is `θ̄`
  have key : ∀ s : ℕ → ℝ, (∀ t, s t ∈ I) →
      (∀ t, jcLHS MF κ γ (s t) = β * jcRHS MF z b σ γ κ (s (t + 1))) →
      Tendsto s atTop (𝓝 θbar) → s 0 = θbar := by
    intro s hsI hs hslim
    rcases lt_trichotomy (s 0) θbar with h | h | h
    · obtain ⟨hanti, -⟩ := fn7_diverge_below MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss hsI hs h
      have : θbar ≤ s 0 := le_of_tendsto hslim (Eventually.of_forall fun n ↦ hanti.antitone
        (Nat.zero_le n))
      linarith
    · exact h
    · obtain ⟨hmon, -⟩ := fn7_diverge_above MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss hsI hs h
      have : s 0 ≤ θbar := ge_of_tendsto hslim (Eventually.of_forall fun n ↦ hmon.monotone
        (Nat.zero_le n))
      linarith
  have := key (fun n ↦ θ (n + t)) (fun n ↦ hθI _) (fun n ↦ by
    simpa [add_right_comm] using hpath (n + t)) ((tendsto_add_atTop_iff_nat t).mpr hlim)
  simpa using this

end AKMM.FrictionalLaborMarkets
