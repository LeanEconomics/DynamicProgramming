/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.NGMDynamics

/-!
# The slope of the policy function at the steady state

AKMM, §4.4.6, "Approximating the policy function" and "Calibration", pp. 125–127.

* (4.29) (`eq_4_29`): if the policy `g` is differentiable at the steady state `k̄` with slope
  `a₁`, differentiating the functional Euler equation (4.26) at `k̄` gives
  `u''(c̄)[1 − βa₁] = u''(c̄)[a₁ − βa₁²] + β²u'(c̄)f''(k̄)a₁`. Differentiability of `g` is a
  hypothesis, as in the book (fn. 17); in SLP's setting it is proved in `DeterministicDynamics`
  (`growth_policy_deriv`).
* (4.29) is the quadratic `βa² − (1 + β + Θ)a + 1 = 0`, `Θ = β²u'f''/u''`
  (`eq_4_29_quadratic`), whose roots are `slopeRoot` and `slopeRootOther`, with product `1/β`.
* (4.30) and the claims after it: see `slopeRoot_isRoot`, `slopeRoot_mem`, `slopeRoot_zero`,
  `slopeRoot_strictAnti`, `slopeRoot_tendsto_zero`, `slopeRoot_tendsto_one`.
* Calibration: `theta_crra`, `theta_crra_strictAnti`, `crra_slope_limits`, `theta_cobbDouglas`,
  `theta_cobbDouglas_strictAnti_alpha`, `theta_cobbDouglas_strictMono_delta` and
  `cobbDouglas_slope_mono` (convergence is slower for larger `α` and smaller `δ`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real

/-- **AKMM, (4.29), p. 125.** Let `h = f + (1 − δ)·id`, `g(k̄) = k̄`, `g'(k̄) = a₁`, `u''(c̄) = u₂`,
`h''(k̄) = f''(k̄) = f₂`, and `βh'(k̄) = 1` (4.27). If (4.26)
`u'(h(k) − g(k)) = βu'(h(g(k)) − g(g(k)))h'(g(k))` holds for `k` near `k̄`, then
`u₂(1 − βa₁) = u₂(a₁ − βa₁²) + β²u'(c̄)f₂a₁`. -/
theorem eq_4_29 {u' h h' g : ℝ → ℝ} {β kbar a1 u2 f2 : ℝ} (hβ : 0 < β) (hss : g kbar = kbar)
    (hg : HasDerivAt g a1 kbar) (hu' : HasDerivAt u' u2 (h kbar - kbar))
    (hh : HasDerivAt h (h' kbar) kbar) (hh' : HasDerivAt h' f2 kbar) (h427 : β * h' kbar = 1)
    (h426 : ∀ᶠ k in 𝓝 kbar, u' (h k - g k) = β * u' (h (g k) - g (g k)) * h' (g k)) :
    u2 * (1 - β * a1) = u2 * (a1 - β * a1 ^ 2) + β ^ 2 * u' (h kbar - kbar) * f2 * a1 := by
  have hg' : HasDerivAt g a1 (g kbar) := by rw [hss]; exact hg
  have hhg : HasDerivAt h (h' kbar) (g kbar) := by rw [hss]; exact hh
  have hh'g : HasDerivAt h' f2 (g kbar) := by rw [hss]; exact hh'
  -- the left-hand side
  have hL : HasDerivAt (fun k => u' (h k - g k)) (u2 * (h' kbar - a1)) kbar := by
    have hin := hh.sub hg
    have hu : HasDerivAt u' u2 (h kbar - g kbar) := by rw [hss]; exact hu'
    exact hu.comp kbar hin
  -- the right-hand side
  have hR : HasDerivAt (fun k => β * u' (h (g k) - g (g k)) * h' (g k))
      (β * (u2 * (h' kbar * a1 - a1 * a1)) * h' kbar + β * u' (h kbar - kbar) * (f2 * a1))
      kbar := by
    have hin : HasDerivAt (fun k => h (g k) - g (g k)) (h' kbar * a1 - a1 * a1) kbar :=
      (hhg.comp kbar hg).sub (hg'.comp kbar hg)
    have hu : HasDerivAt u' u2 (h (g kbar) - g (g kbar)) := by rw [hss, hss]; exact hu'
    have h1 := (hu.comp kbar hin).const_mul β
    have h2 := hh'g.comp kbar hg
    have := h1.mul h2
    convert this using 1
    · funext k; simp only [Pi.mul_apply, Function.comp_apply]
    · simp only [Function.comp_apply, hss]
  have hEq := hL.unique (hR.congr_of_eventuallyEq h426)
  have hh1 : h' kbar = 1 / β := by field_simp; linarith
  rw [hh1] at hEq
  field_simp at hEq
  linear_combination hEq

/-- **AKMM, p. 125.** With `u'' ≠ 0` and `Θ = β²u'f''/u''`, (4.29) is the quadratic
`βa² − (1 + β + Θ)a + 1 = 0`. -/
theorem eq_4_29_quadratic {β a u1 u2 f2 : ℝ} (hu2 : u2 ≠ 0) :
    u2 * (1 - β * a) = u2 * (a - β * a ^ 2) + β ^ 2 * u1 * f2 * a ↔
      β * a ^ 2 - (1 + β + β ^ 2 * u1 * f2 / u2) * a + 1 = 0 := by
  constructor <;> intro h
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h

/-- AKMM, (4.30), p. 125: the stable root `a₁ = (1 + β + Θ − √((1 + β + Θ)² − 4β))/(2β)`. -/
noncomputable def slopeRoot (β Θ : ℝ) : ℝ :=
  (1 + β + Θ - √((1 + β + Θ) ^ 2 - 4 * β)) / (2 * β)

/-- The other root `(1 + β + Θ + √((1 + β + Θ)² − 4β))/(2β)`. -/
noncomputable def slopeRootOther (β Θ : ℝ) : ℝ :=
  (1 + β + Θ + √((1 + β + Θ) ^ 2 - 4 * β)) / (2 * β)

theorem slopeRoot_disc_nonneg {β Θ : ℝ} (hβ : 0 < β) (hΘ : 0 ≤ Θ) :
    0 ≤ (1 + β + Θ) ^ 2 - 4 * β := by nlinarith [sq_nonneg (1 - β)]

/-- AKMM, p. 125: both formulas solve `βa² − (1 + β + Θ)a + 1 = 0`, and their product is `1/β`. -/
theorem slopeRoot_isRoot {β Θ : ℝ} (hβ : 0 < β) (hΘ : 0 ≤ Θ) :
    β * slopeRoot β Θ ^ 2 - (1 + β + Θ) * slopeRoot β Θ + 1 = 0 ∧
      β * slopeRootOther β Θ ^ 2 - (1 + β + Θ) * slopeRootOther β Θ + 1 = 0 ∧
      slopeRoot β Θ * slopeRootOther β Θ = 1 / β := by
  have hs := Real.sq_sqrt (slopeRoot_disc_nonneg hβ hΘ)
  unfold slopeRoot slopeRootOther
  obtain ⟨s, hsd⟩ : ∃ s, s = √((1 + β + Θ) ^ 2 - 4 * β) := ⟨_, rfl⟩
  rw [← hsd] at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination hs
  · field_simp
    linear_combination hs
  · field_simp
    linear_combination -1 * hs

theorem slopeRoot_sqrt_pos {β Θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hΘ : 0 < Θ) :
    1 - β < √((1 + β + Θ) ^ 2 - 4 * β) := by
  rw [show 1 - β = √((1 - β) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)

/-- The stable root in rationalized form, `a₁ = 2/(1 + β + Θ + √((1 + β + Θ)² − 4β))`. -/
theorem slopeRoot_eq {β Θ : ℝ} (hβ : 0 < β) (hΘ : 0 ≤ Θ) :
    slopeRoot β Θ = 2 / (1 + β + Θ + √((1 + β + Θ) ^ 2 - 4 * β)) := by
  have hs := Real.sq_sqrt (slopeRoot_disc_nonneg hβ hΘ)
  have hs0 := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
  unfold slopeRoot
  obtain ⟨s, hsd⟩ : ∃ s, s = √((1 + β + Θ) ^ 2 - 4 * β) := ⟨_, rfl⟩
  rw [← hsd] at hs hs0 ⊢
  have hpos : 0 < 1 + β + Θ + s := by linarith
  rw [div_eq_div_iff (by positivity) hpos.ne']
  linear_combination -1 * hs

/-- **AKMM, p. 125: "one root strictly between zero and one, the other strictly greater than
one"** (for `Θ > 0`, `0 < β < 1`). -/
theorem slopeRoot_mem {β Θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hΘ : 0 < Θ) :
    0 < slopeRoot β Θ ∧ slopeRoot β Θ < 1 ∧ 1 < slopeRootOther β Θ := by
  have hsq := slopeRoot_sqrt_pos hβ hβ1 hΘ
  have hs0 := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
  rw [slopeRoot_eq hβ hΘ.le]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · unfold slopeRootOther
    rw [one_lt_div (by positivity)]; linarith

/-- **AKMM, p. 125: `a₁ = 1` when `Θ = 0`** (for `0 < β < 1`; the other root is `1/β`). -/
theorem slopeRoot_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    slopeRoot β 0 = 1 ∧ slopeRootOther β 0 = 1 / β := by
  have e : √((1 + β + 0) ^ 2 - 4 * β) = 1 - β := by
    rw [show (1 + β + 0) ^ 2 - 4 * β = (1 - β) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  unfold slopeRoot slopeRootOther
  rw [e]
  constructor <;> field_simp <;> ring

/-- **AKMM, p. 125: `a₁` is decreasing in `Θ`** on `[0, ∞)`. -/
theorem slopeRoot_strictAnti {β : ℝ} (hβ : 0 < β) :
    StrictAntiOn (slopeRoot β) (Set.Ici 0) := by
  intro Θ hΘ Θ' hΘ' hlt
  have hΘ0 : (0 : ℝ) ≤ Θ := hΘ
  have hΘ0' : (0 : ℝ) ≤ Θ' := hΘ'
  rw [slopeRoot_eq hβ hΘ0, slopeRoot_eq hβ hΘ0']
  have hs : √((1 + β + Θ) ^ 2 - 4 * β) ≤ √((1 + β + Θ') ^ 2 - 4 * β) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h0 := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
  exact div_lt_div_of_pos_left two_pos (by positivity) (by linarith)

/-- **AKMM, p. 125: `a₁ → 0` as `Θ → ∞`.** -/
theorem slopeRoot_tendsto_zero {β : ℝ} (hβ : 0 < β) :
    Tendsto (slopeRoot β) atTop (𝓝 0) := by
  have hden : Tendsto (fun Θ : ℝ => 1 + β + Θ + √((1 + β + Θ) ^ 2 - 4 * β)) atTop atTop := by
    refine tendsto_atTop_mono (fun Θ => ?_) (tendsto_atTop_add_const_left _ (1 + β) tendsto_id)
    have := Real.sqrt_nonneg ((1 + β + Θ) ^ 2 - 4 * β)
    simp only [id]; linarith
  refine ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hden).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with Θ hΘ
  exact (slopeRoot_eq hβ hΘ).symm

/-- **AKMM, p. 125: `a₁ → 1` as `Θ → 0`** (continuity of (4.30)). -/
theorem slopeRoot_tendsto_one {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (slopeRoot β) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (slopeRoot β) := by
    unfold slopeRoot
    exact ((continuous_const.add continuous_id).sub
      (Real.continuous_sqrt.comp (((continuous_const.add continuous_id).pow 2).sub
        continuous_const))).div_const _
  have := hc.tendsto 0
  rwa [(slopeRoot_zero hβ hβ1).1] at this

/-- **AKMM, p. 126: `Θ` under CRRA utility.** With `u'(c) = c^{−σ}`, `u''(c) = −σc^{−σ−1}`,
`c̄ > 0`, `σ > 0`: `Θ = β²u'f''/u'' = −β²f''(k̄)c̄/σ`, where `c̄ = f(k̄) − δk̄`. -/
theorem theta_crra {β σ c f2 : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    β ^ 2 * c ^ (-σ) * f2 / (-σ * c ^ (-σ - 1)) = -(β ^ 2 * f2 * c) / σ := by
  have hP : 0 < c ^ (-σ) := rpow_pos_of_pos hc _
  rw [rpow_sub_one hc.ne']
  field_simp

/-- **AKMM, p. 126.** With `f'' < 0` and `c̄ > 0`, the CRRA `Θ = −β²f''c̄/σ` is positive and
strictly decreasing in `σ > 0`. -/
theorem theta_crra_strictAnti {β c f2 : ℝ} (hβ : 0 < β) (hc : 0 < c) (hf2 : f2 < 0) :
    (∀ σ, 0 < σ → 0 < -(β ^ 2 * f2 * c) / σ) ∧
      StrictAntiOn (fun σ => -(β ^ 2 * f2 * c) / σ) (Set.Ioi 0) := by
  have hK : 0 < -(β ^ 2 * f2 * c) := by
    have : β ^ 2 * f2 * c < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity)
      hf2) hc
    linarith
  exact ⟨fun σ hσ => div_pos hK hσ, fun σ hσ σ' _ hlt => div_lt_div_of_pos_left hK hσ hlt⟩

/-- **AKMM, p. 126: the limits in `σ`.** As `σ → 0⁺`, `Θ → ∞` and `a₁ → 0` (immediate
convergence); as `σ → ∞`, `Θ → 0` and `a₁ → 1` (infinitely slow convergence). -/
theorem crra_slope_limits {β c f2 : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hf2 : f2 < 0) :
    Tendsto (fun σ => slopeRoot β (-(β ^ 2 * f2 * c) / σ)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun σ => slopeRoot β (-(β ^ 2 * f2 * c) / σ)) atTop (𝓝 1) := by
  have hK : 0 < -(β ^ 2 * f2 * c) := by
    have : β ^ 2 * f2 * c < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity)
      hf2) hc
    linarith
  refine ⟨(slopeRoot_tendsto_zero hβ).comp ?_, (slopeRoot_tendsto_one hβ hβ1).comp ?_⟩
  · have := tendsto_inv_nhdsGT_zero.const_mul_atTop hK
    exact this.congr fun σ => (div_eq_mul_inv _ _).symm
  · exact (tendsto_const_nhds (x := -(β ^ 2 * f2 * c))).div_atTop tendsto_id

/-- **AKMM, p. 126: `Θ` with `f(k) = k^α`.** If `k̄ > 0` and `αk̄^{α−1} = ρ = 1/β − 1 + δ`, then
`−β²f''(k̄)(f(k̄) − δk̄)/σ = (β²(1 − α)/σ)ρ(ρ/α − δ)`, the book's formula. -/
theorem theta_cobbDouglas {α β δ σ kbar : ℝ} (hα0 : 0 < α) (hk : 0 < kbar)
    (hss : α * kbar ^ (α - 1) = 1 / β - 1 + δ) :
    -(β ^ 2 * (α * (α - 1) * kbar ^ (α - 2)) * (kbar ^ α - δ * kbar)) / σ =
      β ^ 2 * (1 - α) / σ * (1 / β - 1 + δ) * ((1 / β - 1 + δ) / α - δ) := by
  have h2 : kbar ^ (α - 2) = kbar ^ (α - 1) / kbar := by
    rw [show α - 2 = (α - 1) - 1 by ring, rpow_sub_one hk.ne']
  have h3 : kbar ^ α = kbar ^ (α - 1) * kbar := by
    rw [← rpow_add_one hk.ne']; ring_nf
  have hk1 : kbar ^ (α - 1) = (1 / β - 1 + δ) / α := by
    field_simp; linarith
  rw [h2, h3, hk1]
  field_simp
  ring

/-- The Cobb–Douglas `Θ(α, δ) = (β²(1 − α)/σ)ρ(ρ/α − δ)`, `ρ = 1/β − 1 + δ`. -/
noncomputable def thetaCD (β σ α δ : ℝ) : ℝ :=
  β ^ 2 * (1 - α) / σ * (1 / β - 1 + δ) * ((1 / β - 1 + δ) / α - δ)

theorem thetaCD_pos {β σ α δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hα0 : 0 < α)
    (hα1 : α < 1) (hδ : 0 ≤ δ) : 0 < thetaCD β σ α δ := by
  have hρ : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  have h2 : 0 < (1 / β - 1 + δ) / α - δ := by
    rw [sub_pos, lt_div_iff₀ hα0]; nlinarith
  unfold thetaCD
  have : 0 < β ^ 2 * (1 - α) / σ := div_pos (mul_pos (by positivity) (by linarith)) hσ
  positivity

/-- **AKMM, p. 127: `Θ` is decreasing in `α`** on `(0, 1)`. -/
theorem theta_cobbDouglas_strictAnti_alpha {β σ δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hδ : 0 ≤ δ) : StrictAntiOn (fun α => thetaCD β σ α δ) (Set.Ioo 0 1) := by
  intro α hα α' hα' hlt
  have hρ : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  set ρ := 1 / β - 1 + δ
  have hρ' : 0 < ρ := by simp only [ρ]; linarith
  have hd' : 0 < ρ / α' - δ := by rw [sub_pos, lt_div_iff₀ hα'.1]; nlinarith [hα'.2]
  have hdlt : ρ / α' - δ < ρ / α - δ := by
    have := div_lt_div_of_pos_left hρ' hα.1 hlt; linarith
  have h1 : 0 < 1 - α' := by linarith [hα'.2]
  have hc : 0 < β ^ 2 / σ * ρ := by positivity
  simp only [thetaCD]
  have e : ∀ x : ℝ, β ^ 2 * (1 - x) / σ * ρ * (ρ / x - δ) =
      β ^ 2 / σ * ρ * ((1 - x) * (ρ / x - δ)) := fun x => by ring
  rw [e, e]
  exact mul_lt_mul_of_pos_left (mul_lt_mul'' (by linarith) hdlt h1.le hd'.le) hc

/-- **AKMM, p. 127: `Θ` is increasing in `δ`** on `[0, ∞)`. -/
theorem theta_cobbDouglas_strictMono_delta {β σ α : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hα0 : 0 < α) (hα1 : α < 1) :
    StrictMonoOn (fun δ => thetaCD β σ α δ) (Set.Ici 0) := by
  intro δ hδ δ' hδ' hlt
  have hδ0 : (0 : ℝ) ≤ δ := hδ
  have hρ : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  have hc : 0 < β ^ 2 * (1 - α) / σ := div_pos (mul_pos (by positivity) (by linarith)) hσ
  have h2 : 0 < (1 / β - 1 + δ) / α - δ := by rw [sub_pos, lt_div_iff₀ hα0]; nlinarith
  have h3 : (1 / β - 1 + δ) / α - δ < (1 / β - 1 + δ') / α - δ' := by
    have e : ∀ x : ℝ, (1 / β - 1 + x) / α - x = (1 / β - 1) / α + x * (1 / α - 1) := fun x => by
      field_simp; ring
    rw [e, e]
    have : 0 < 1 / α - 1 := by rw [sub_pos, lt_div_iff₀ hα0]; linarith
    nlinarith
  simp only [thetaCD]
  rw [mul_assoc, mul_assoc (β ^ 2 * (1 - α) / σ)]
  exact mul_lt_mul_of_pos_left (mul_lt_mul'' (by linarith) h3 (by linarith) h2.le) hc

/-- **AKMM, p. 127: convergence is slower when production is closer to linear and depreciation
is small.** With Cobb–Douglas technology, `a₁ = slopeRoot β Θ(α, δ)` is increasing in `α` and
decreasing in `δ`. -/
theorem cobbDouglas_slope_mono {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) :
    (∀ δ, 0 ≤ δ → StrictMonoOn (fun α => slopeRoot β (thetaCD β σ α δ)) (Set.Ioo 0 1)) ∧
      ∀ α, 0 < α → α < 1 → StrictAntiOn (fun δ => slopeRoot β (thetaCD β σ α δ)) (Set.Ici 0) := by
  refine ⟨fun δ hδ α hα α' hα' hlt => ?_, fun α hα0 hα1 δ hδ δ' hδ' hlt => ?_⟩
  · exact slopeRoot_strictAnti hβ0 (thetaCD_pos hβ0 hβ1 hσ hα'.1 hα'.2 hδ).le
      (thetaCD_pos hβ0 hβ1 hσ hα.1 hα.2 hδ).le
      (theta_cobbDouglas_strictAnti_alpha hβ0 hβ1 hσ hδ hα hα' hlt)
  · exact slopeRoot_strictAnti hβ0 (thetaCD_pos hβ0 hβ1 hσ hα0 hα1 hδ).le
      (thetaCD_pos hβ0 hβ1 hσ hα0 hα1 hδ').le
      (theta_cobbDouglas_strictMono_delta hβ0 hβ1 hσ hα0 hα1 hδ hδ' hlt)

end AKMM.DynamicOptimization
