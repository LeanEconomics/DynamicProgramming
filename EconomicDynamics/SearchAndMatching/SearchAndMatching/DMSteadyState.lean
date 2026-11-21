/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMBellman
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# §18.1: the steady state — job creation and wage curves, Beveridge curve, comparative statics

Miao, §18.1, "Steady State", pp. 592–594, equations (18.16)–(18.19) and Figures 18.1–18.2.

* `eq_18_16`, `dm_jc_iff`, `dm_jc_strictAntiOn`: the steady-state job creation condition and the
  downward-sloping job creation curve `w = A − κ(1 − β(1 − ρ))/(βq(θ))`.
* `eq_18_17`, `dm_wc_strictMono`: the upward-sloping wage curve `w = η(A + κθ) + (1 − η)b`.
* `eq_18_18`, `dm_ssLHS_strictMonoOn`, `dm_ss_unique`, `dm_ss_exists`, `dm_cd_ss_existsUnique`:
  eliminating `w`, `θ*` solves (18.18); the solution is unique, and exists under a condition at
  small `θ`. For Cobb–Douglas matching it exists iff `A > b`. Correction: the book's "unique
  solution" needs `A > b`; for `A ≤ b` there is no solution (`dm_ss_not_exists`).
* `eq_18_19`, `dm_uStar`: on the job creation line `v = θu`, the steady-state Beveridge relation
  `ρ(1 − u) = M(u, v)` gives `u* = ρ/(ρ + θq(θ))`; `dm_uStar_strictAntiOn`,
  `dm_vStar_strictMonoOn`: unemployment falls and vacancies rise with `θ`.
* Comparative statics (p. 593): `dm_cs_shifts` (the job creation curve shifts up one-for-one in
  `A`, the wage curve by `η < 1`), `dm_cs_A` (higher `A`: higher `θ`, `w`, `v`, lower `u`),
  `dm_cs_b` (higher `b`: higher `w`, `u`, lower `θ`, `v`), `dm_cs_eta` (higher `η`: the same
  signs as `b`, when `A > b`).
* `dm_steady_isSearchEqm`, `dm_searchEqm_exists`: the steady state is a search equilibrium; a
  concrete Cobb–Douglas economy has one.
-/

namespace Miao.SearchAndMatching

/-- Miao, (18.16), p. 592: the **job creation curve** `w = A − κ(1 − β(1 − ρ))/(βq(θ))`. -/
noncomputable def dm_jcCurve (MF : DMMatchingFn) (A κ β ρ θ : ℝ) : ℝ :=
  A - κ * (1 - β * (1 - ρ)) / (β * dm_q MF θ)

/-- Miao, (18.17), p. 592: the **wage curve** `w = η(A + κθ) + (1 − η)b`. -/
def dm_wageCurve (A b κ η θ : ℝ) : ℝ := η * (A + κ * θ) + (1 - η) * b

/-- Miao, (18.18), p. 593: the left side `κ(1 − β(1 − ρ))/q(θ) + βηκθ` of (18.18). -/
noncomputable def dm_ssLHS (MF : DMMatchingFn) (κ β ρ η θ : ℝ) : ℝ :=
  κ / dm_q MF θ * (1 - β * (1 - ρ)) + β * η * κ * θ

/-- Miao, (18.19), p. 593: steady-state unemployment `u* = ρ/(ρ + θq(θ))`. -/
noncomputable def dm_uStar (MF : DMMatchingFn) (ρ θ : ℝ) : ℝ := ρ / (ρ + θ * dm_q MF θ)

/-- Miao, (18.16), p. 592: in a steady state, the job creation equation (18.8) reads
`κ(1 − β(1 − ρ))/q(θ) = β(A − w)`. -/
theorem eq_18_16 (MF : DMMatchingFn) (A κ β ρ w θ : ℝ) :
    κ / dm_q MF θ = β * (A - w + (1 - ρ) * κ / dm_q MF θ) ↔
      κ / dm_q MF θ * (1 - β * (1 - ρ)) = β * (A - w) := by
  have e : (1 - ρ) * κ / dm_q MF θ = (1 - ρ) * (κ / dm_q MF θ) := by ring
  rw [e]
  constructor <;> intro h <;> linear_combination h

/-- Miao, (18.16), p. 592: (18.16) holds iff `w` lies on the job creation curve. -/
theorem dm_jc_iff (MF : DMMatchingFn) {A κ β ρ w θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ) :
    κ / dm_q MF θ * (1 - β * (1 - ρ)) = β * (A - w) ↔ w = dm_jcCurve MF A κ β ρ θ := by
  have hq := (dm_q_pos MF hθ).ne'
  rw [dm_jcCurve]
  constructor
  · intro h
    have e : κ * (1 - β * (1 - ρ)) / (β * dm_q MF θ) = κ / dm_q MF θ * (1 - β * (1 - ρ)) / β := by
      field_simp
    rw [e, h, mul_div_cancel_left₀ _ hβ.ne']
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Miao, p. 592: the job creation curve slopes down in the `(θ, w)` plane. -/
theorem dm_jc_strictAntiOn (MF : DMMatchingFn) {A κ β ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hc : 0 < 1 - β * (1 - ρ)) :
    StrictAntiOn (fun θ ↦ dm_jcCurve MF A κ β ρ θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hqx := dm_q_pos MF hx
  have hqy := dm_q_pos MF hy
  have hlt := dm_q_strictAntiOn MF hx hy hxy
  simp only [dm_jcCurve]
  have : κ * (1 - β * (1 - ρ)) / (β * dm_q MF x) < κ * (1 - β * (1 - ρ)) / (β * dm_q MF y) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    exact mul_lt_mul_of_pos_left hlt hβ
  linarith

/-- Miao, (18.17), p. 592: the steady-state version of the wage equation (18.15). -/
theorem eq_18_17 (A b κ η w θ : ℝ) :
    w = η * (A + κ * θ) + (1 - η) * b ↔ w = dm_wageCurve A b κ η θ := Iff.rfl

/-- Miao, p. 593: the wage curve slopes up. -/
theorem dm_wc_strictMono {A b κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    StrictMono (fun θ ↦ dm_wageCurve A b κ η θ) := by
  intro x y hxy
  simp only [dm_wageCurve]
  have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hxy hκ) hη
  nlinarith

/-- Miao, (18.18), p. 593: the steady state `(θ, w)` lies on both curves iff `θ` solves
`κ(1 − β(1 − ρ))/q(θ) + βηκθ = β(1 − η)(A − b)` and `w` is on the wage curve. -/
theorem eq_18_18 (MF : DMMatchingFn) (A b κ β ρ η w θ : ℝ) :
    (κ / dm_q MF θ * (1 - β * (1 - ρ)) = β * (A - w) ∧ w = dm_wageCurve A b κ η θ) ↔
      (dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b) ∧ w = dm_wageCurve A b κ η θ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, dm_wageCurve] at h1
    rw [dm_ssLHS]
    linear_combination h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, dm_wageCurve]
    rw [dm_ssLHS] at h1
    linear_combination h1

/-- Miao, p. 593: at a solution of (18.18) the wage curve and the job creation curve meet. -/
theorem dm_wc_eq_jc (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b)) :
    dm_wageCurve A b κ η θ = dm_jcCurve MF A κ β ρ θ := by
  have := ((eq_18_18 MF A b κ β ρ η (dm_wageCurve A b κ η θ) θ).mpr ⟨h, rfl⟩).1
  exact (dm_jc_iff MF hβ hθ).mp this

/-- Miao, p. 593: the left side of (18.18) is strictly increasing in `θ`. -/
theorem dm_ssLHS_strictMonoOn (MF : DMMatchingFn) {κ β ρ η : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hc : 0 < 1 - β * (1 - ρ)) :
    StrictMonoOn (fun θ ↦ dm_ssLHS MF κ β ρ η θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hqx := dm_q_pos MF hx
  have hqy := dm_q_pos MF hy
  have hlt := dm_q_strictAntiOn MF hx hy hxy
  simp only [dm_ssLHS]
  have h1 : κ / dm_q MF x < κ / dm_q MF y := div_lt_div_of_pos_left hκ hqy hlt
  have h2 := mul_lt_mul_of_pos_right h1 hc
  have h3 : β * η * κ * x < β * η * κ * y := mul_lt_mul_of_pos_left hxy (by positivity)
  linarith

/-- Miao, p. 593: `θ*` is the **unique** solution of (18.18). -/
theorem dm_ss_unique (MF : DMMatchingFn) {A b κ β ρ η θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hc : 0 < 1 - β * (1 - ρ)) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (h₁ : dm_ssLHS MF κ β ρ η θ₁ = β * (1 - η) * (A - b))
    (h₂ : dm_ssLHS MF κ β ρ η θ₂ = β * (1 - η) * (A - b)) : θ₁ = θ₂ :=
  (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).injOn hθ₁ hθ₂ (h₁.trans h₂.symm)

/-- Miao, p. 593: **existence** of a solution of (18.18), when the left side is below the right
side at some `θ₀ > 0` (by continuity of `q` and the intermediate value theorem). -/
theorem dm_ss_exists (MF : DMMatchingFn) {A b κ β ρ η θ₀ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hθ₀ : 0 < θ₀) (h₀ : dm_ssLHS MF κ β ρ η θ₀ < β * (1 - η) * (A - b))
    (hc : 0 < 1 - β * (1 - ρ)) :
    ∃ θ, 0 < θ ∧ dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b) := by
  set R := β * (1 - η) * (A - b)
  set T := max θ₀ (R / (β * η * κ))
  have hT : θ₀ ≤ T := le_max_left _ _
  have hk : 0 < β * η * κ := by positivity
  have hcont : ContinuousOn (fun θ ↦ dm_ssLHS MF κ β ρ η θ) (Set.Icc θ₀ T) := by
    have hq : ContinuousOn (dm_q MF) (Set.Icc θ₀ T) :=
      (dm_q_continuousOn MF).mono fun x hx ↦ lt_of_lt_of_le hθ₀ hx.1
    simp only [dm_ssLHS]
    refine ((continuousOn_const.div hq ?_).mul continuousOn_const).add
      (continuousOn_const.mul continuousOn_id)
    intro x hx
    exact (dm_q_pos MF (lt_of_lt_of_le hθ₀ hx.1)).ne'
  have hfT : R ≤ dm_ssLHS MF κ β ρ η T := by
    have hTpos : 0 < T := lt_of_lt_of_le hθ₀ hT
    have hq := dm_q_pos MF hTpos
    simp only [dm_ssLHS]
    have h1 : 0 ≤ κ / dm_q MF T * (1 - β * (1 - ρ)) := by positivity
    have h2 : R / (β * η * κ) ≤ T := le_max_right _ _
    have h3 : R ≤ β * η * κ * T := by
      rw [div_le_iff₀ hk] at h2; linarith
    linarith
  obtain ⟨θ, hθI, hθeq⟩ := intermediate_value_Icc hT hcont ⟨h₀.le, hfT⟩
  exact ⟨θ, lt_of_lt_of_le hθ₀ hθI.1, hθeq⟩

/-- Miao, p. 593 (correction): if `A ≤ b`, (18.18) has **no** solution `θ > 0`. -/
theorem dm_ss_not_exists (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hη1 : η < 1) (hc : 0 < 1 - β * (1 - ρ)) (hAb : A ≤ b) (hθ : 0 < θ) :
    dm_ssLHS MF κ β ρ η θ ≠ β * (1 - η) * (A - b) := by
  have hq := dm_q_pos MF hθ
  have h1 : 0 < dm_ssLHS MF κ β ρ η θ := by
    simp only [dm_ssLHS]; positivity
  have h2 : β * (1 - η) * (A - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by linarith)
  intro h
  linarith

/-- Miao, p. 593: for Cobb–Douglas matching the left side of (18.18) is
`κ(1 − β(1 − ρ))θ^α/μ + βηκθ`. -/
theorem dm_cd_ssLHS {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {κ β ρ η θ : ℝ}
    (hθ : 0 < θ) :
    dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ η θ =
      κ * (1 - β * (1 - ρ)) * θ ^ α / μ + β * η * κ * θ := by
  rw [dm_ssLHS, dm_cd_q hμ hα0 hα1 hθ, Real.rpow_neg hθ.le]
  have : 0 < θ ^ α := by positivity
  field_simp

/-- Miao, p. 593: for Cobb–Douglas matching, (18.18) has a unique solution `θ* > 0` iff
`A > b` (the "if" part; the "only if" part is `dm_ss_not_exists`). -/
theorem dm_cd_ss_existsUnique {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1)
    {A b κ β ρ η : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hη : 0 < η) (hη1 : η < 1)
    (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A) :
    ∃! θ, 0 < θ ∧ dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ η θ =
      β * (1 - η) * (A - b) := by
  set MF := dm_cdMatching μ α hμ hα0 hα1
  set R := β * (1 - η) * (A - b) with hR
  have hRpos : 0 < R := by
    have : 0 < 1 - η := by linarith
    have : 0 < A - b := by linarith
    positivity
  set g : ℝ → ℝ := fun θ ↦ κ * (1 - β * (1 - ρ)) * θ ^ α / μ + β * η * κ * θ with hg
  have hk : 0 < β * η * κ := by positivity
  set T := R / (β * η * κ)
  have hTpos : 0 < T := div_pos hRpos hk
  have hcont : ContinuousOn g (Set.Icc 0 T) := by
    refine Continuous.continuousOn ?_
    exact ((continuous_const.mul (Real.continuous_rpow_const hα0.le)).div_const _).add
      (continuous_const.mul continuous_id)
  have hg0 : g 0 = 0 := by simp [hg, Real.zero_rpow hα0.ne']
  have hgT : R ≤ g T := by
    simp only [hg]
    have h1 : 0 ≤ κ * (1 - β * (1 - ρ)) * T ^ α / μ := by positivity
    have h3 : β * η * κ * T = R := by simp only [T]; field_simp
    linarith
  obtain ⟨θ, hθI, hθeq⟩ := intermediate_value_Icc hTpos.le hcont ⟨by rw [hg0]; exact hRpos.le, hgT⟩
  have hθpos : 0 < θ := by
    rcases hθI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hg0] at hθeq; linarith
  refine ⟨θ, ⟨hθpos, ?_⟩, ?_⟩
  · rw [dm_cd_ssLHS hμ hα0 hα1 hθpos]; exact hθeq
  · rintro θ' ⟨hθ', h'⟩
    refine dm_ss_unique MF hκ hβ hη hc hθ' hθpos h' ?_
    rw [dm_cd_ssLHS hμ hα0 hα1 hθpos]; exact hθeq

/-- Miao, (18.19), p. 593: on the job creation line `v = θu`, the Beveridge relation
`ρ(1 − u) = M(u, v)` holds iff `u = ρ/(ρ + θq(θ))`. -/
theorem eq_18_19 (MF : DMMatchingFn) {ρ θ u : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hu : 0 < u) :
    ρ * (1 - u) = MF.M u (θ * u) ↔ u = dm_uStar MF ρ θ := by
  have hM : MF.M u (θ * u) = u * (θ * dm_q MF θ) := by
    rw [dm_M_eq_mul_q MF hu (mul_pos hθ hu)]
    have : θ * u / u = θ := by field_simp
    rw [this]; ring
  have hq := dm_q_pos MF hθ
  have hd : 0 < ρ + θ * dm_q MF θ := by positivity
  rw [hM, dm_uStar, eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 593: `0 < u* < 1`. -/
theorem dm_uStar_mem (MF : DMMatchingFn) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) :
    0 < dm_uStar MF ρ θ ∧ dm_uStar MF ρ θ < 1 := by
  have hq := dm_q_pos MF hθ
  have hd : 0 < ρ + θ * dm_q MF θ := by positivity
  refine ⟨div_pos hρ hd, (div_lt_one hd).mpr ?_⟩
  have : 0 < θ * dm_q MF θ := by positivity
  linarith

/-- Miao, p. 593 (Figure 18.2): steady-state unemployment falls as `θ` rises (the job creation
line rotates anticlockwise along the Beveridge curve). -/
theorem dm_uStar_strictAntiOn (MF : DMMatchingFn) {ρ : ℝ} (hρ : 0 < ρ) :
    StrictAntiOn (fun θ ↦ dm_uStar MF ρ θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h := dm_jobFinding_strictMonoOn MF hx hy hxy
  have hqx := dm_q_pos MF hx
  simp only [dm_uStar] at h ⊢
  have hx' : 0 < ρ + x * dm_q MF x := by
    have : 0 < x * dm_q MF x := mul_pos hx hqx
    linarith
  exact div_lt_div_of_pos_left hρ hx' (by linarith)

/-- Miao, p. 593 (Figure 18.2): steady-state vacancies `v* = θu*` rise with `θ`. -/
theorem dm_vStar_strictMonoOn (MF : DMMatchingFn) {ρ : ℝ} (hρ : 0 < ρ) :
    StrictMonoOn (fun θ ↦ θ * dm_uStar MF ρ θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hqx := dm_q_pos MF hx0
  have hqy := dm_q_pos MF hy0
  have e : ∀ θ, 0 < θ → θ * dm_uStar MF ρ θ = ρ / (ρ / θ + dm_q MF θ) := by
    intro θ hθ
    have := dm_q_pos MF hθ
    rw [dm_uStar]
    field_simp
  simp only
  rw [e x hx0, e y hy0]
  have h1 : ρ / y < ρ / x := div_lt_div_of_pos_left hρ hx0 hxy
  have h2 := dm_q_strictAntiOn MF hx hy hxy
  apply div_lt_div_of_pos_left hρ (by positivity)
  linarith

/-- Miao, p. 593: an increase in `A` shifts the job creation curve up one-for-one and the wage
curve up by `η < 1`. -/
theorem dm_cs_shifts (MF : DMMatchingFn) (A b κ β ρ η θ Δ : ℝ) :
    dm_jcCurve MF (A + Δ) κ β ρ θ - dm_jcCurve MF A κ β ρ θ = Δ ∧
      dm_wageCurve (A + Δ) b κ η θ - dm_wageCurve A b κ η θ = η * Δ := by
  constructor
  · simp only [dm_jcCurve]; ring
  · simp only [dm_wageCurve]; ring

/-- Miao, p. 593: an increase in productivity `A` raises market tightness, the wage and
vacancies, and lowers unemployment. -/
theorem dm_cs_A (MF : DMMatchingFn) {A₁ A₂ b κ β ρ η θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hη1 : η < 1) (hρ : 0 < ρ) (hc : 0 < 1 - β * (1 - ρ)) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : dm_ssLHS MF κ β ρ η θ₁ = β * (1 - η) * (A₁ - b))
    (h₂ : dm_ssLHS MF κ β ρ η θ₂ = β * (1 - η) * (A₂ - b)) (hA : A₁ < A₂) :
    θ₁ < θ₂ ∧ dm_wageCurve A₁ b κ η θ₁ < dm_wageCurve A₂ b κ η θ₂ ∧
      dm_uStar MF ρ θ₂ < dm_uStar MF ρ θ₁ ∧ θ₁ * dm_uStar MF ρ θ₁ < θ₂ * dm_uStar MF ρ θ₂ := by
  have hθ : θ₁ < θ₂ := by
    by_contra hcon
    have hle := (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).monotoneOn hθ₂ hθ₁ (not_lt.mp hcon)
    have : β * (1 - η) * (A₁ - b) < β * (1 - η) * (A₂ - b) := by
      have : 0 < β * (1 - η) := mul_pos hβ (by linarith)
      nlinarith
    linarith
  refine ⟨hθ, ?_, dm_uStar_strictAntiOn MF hρ hθ₁ hθ₂ hθ,
    dm_vStar_strictMonoOn MF hρ hθ₁ hθ₂ hθ⟩
  simp only [dm_wageCurve]
  have := mul_lt_mul_of_pos_left hθ hκ
  nlinarith

/-- Miao, p. 593: an increase in the unemployment benefit `b` lowers market tightness and
vacancies and raises the wage and unemployment. -/
theorem dm_cs_b (MF : DMMatchingFn) {A b₁ b₂ κ β ρ η θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hη1 : η < 1) (hρ : 0 < ρ) (hc : 0 < 1 - β * (1 - ρ)) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : dm_ssLHS MF κ β ρ η θ₁ = β * (1 - η) * (A - b₁))
    (h₂ : dm_ssLHS MF κ β ρ η θ₂ = β * (1 - η) * (A - b₂)) (hb : b₁ < b₂) :
    θ₂ < θ₁ ∧ dm_wageCurve A b₁ κ η θ₁ < dm_wageCurve A b₂ κ η θ₂ ∧
      dm_uStar MF ρ θ₁ < dm_uStar MF ρ θ₂ ∧ θ₂ * dm_uStar MF ρ θ₂ < θ₁ * dm_uStar MF ρ θ₁ := by
  have hθ : θ₂ < θ₁ := by
    by_contra hcon
    have hle := (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).monotoneOn hθ₁ hθ₂ (not_lt.mp hcon)
    have : β * (1 - η) * (A - b₂) < β * (1 - η) * (A - b₁) := by
      have : 0 < β * (1 - η) := mul_pos hβ (by linarith)
      nlinarith
    linarith
  refine ⟨hθ, ?_, dm_uStar_strictAntiOn MF hρ hθ₂ hθ₁ hθ,
    dm_vStar_strictMonoOn MF hρ hθ₂ hθ₁ hθ⟩
  rw [dm_wc_eq_jc MF hβ hθ₁ h₁, dm_wc_eq_jc MF hβ hθ₂ h₂]
  exact dm_jc_strictAntiOn MF hκ hβ hc hθ₂ hθ₁ hθ

/-- Miao, p. 594: an increase in the worker's bargaining power `η` has the same effects as an
increase in `b` (when `A > b`): lower tightness and vacancies, higher wage and unemployment. -/
theorem dm_cs_eta (MF : DMMatchingFn) {A b κ β ρ η₁ η₂ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η₁) (hρ : 0 < ρ) (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : dm_ssLHS MF κ β ρ η₁ θ₁ = β * (1 - η₁) * (A - b))
    (h₂ : dm_ssLHS MF κ β ρ η₂ θ₂ = β * (1 - η₂) * (A - b)) (hη12 : η₁ < η₂) :
    θ₂ < θ₁ ∧ dm_wageCurve A b κ η₁ θ₁ < dm_wageCurve A b κ η₂ θ₂ ∧
      dm_uStar MF ρ θ₁ < dm_uStar MF ρ θ₂ ∧ θ₂ * dm_uStar MF ρ θ₂ < θ₁ * dm_uStar MF ρ θ₁ := by
  have hθ : θ₂ < θ₁ := by
    by_contra hcon
    have hle := (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).monotoneOn hθ₁ hθ₂ (not_lt.mp hcon)
    simp only [dm_ssLHS] at hle h₁ h₂
    have hd : 0 < β * κ * θ₂ + β * (A - b) := by
      have : 0 < β * κ * θ₂ := by positivity
      have : 0 < β * (A - b) := mul_pos hβ (by linarith)
      linarith
    nlinarith
  refine ⟨hθ, ?_, dm_uStar_strictAntiOn MF hρ hθ₂ hθ₁ hθ,
    dm_vStar_strictMonoOn MF hρ hθ₂ hθ₁ hθ⟩
  rw [dm_wc_eq_jc MF hβ hθ₁ h₁, dm_wc_eq_jc MF hβ hθ₂ h₂]
  exact dm_jc_strictAntiOn MF hκ hβ hc hθ₂ hθ₁ hθ

/-- Miao, p. 592: the steady state `(θ*, w*, u*, v* = θ*u*)` (constant sequences, with
`N = 1 − u*` and `q^v = q(θ*)`) is a search equilibrium. -/
theorem dm_steady_isSearchEqm (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hρ : 0 < ρ)
    (hθ : 0 < θ) (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b)) :
    dm_IsSearchEqm MF A b κ β ρ η (fun _ ↦ 1 - dm_uStar MF ρ θ) (fun _ ↦ dm_uStar MF ρ θ)
      (fun _ ↦ θ * dm_uStar MF ρ θ) (fun _ ↦ θ) (fun _ ↦ dm_wageCurve A b κ η θ)
      (fun _ ↦ dm_q MF θ) := by
  intro t
  obtain ⟨hu0, -⟩ := dm_uStar_mem MF hρ hθ
  have hB := (eq_18_19 MF hρ hθ hu0).mpr rfl
  have h16 := ((eq_18_18 MF A b κ β ρ η _ θ).mpr ⟨h, rfl⟩).1
  refine ⟨hu0, mul_pos hθ hu0, by field_simp, rfl, ?_, by ring, ?_, rfl⟩
  · simp only
    rw [← hB]; ring
  · exact (eq_18_16 MF A κ β ρ _ θ).mpr h16

/-- Miao, p. 592: a search equilibrium exists in a concrete economy (Cobb–Douglas matching with
`μ = 1`, `α = 1/2`; `A = 1`, `b = 0`, `κ = 1`, `β = ρ = η = 1/2`). -/
theorem dm_searchEqm_exists :
    ∃ N u v θ w qv : ℕ → ℝ, dm_IsSearchEqm (dm_cdMatching 1 (1 / 2) one_pos (by norm_num)
      (by norm_num)) 1 0 1 (1 / 2) (1 / 2) (1 / 2) N u v θ w qv := by
  obtain ⟨θ, ⟨hθ, h⟩, -⟩ := dm_cd_ss_existsUnique (μ := 1) (α := 1 / 2) one_pos (by norm_num)
    (by norm_num) (A := 1) (b := 0) (κ := 1) (β := 1 / 2) (ρ := 1 / 2) (η := 1 / 2) one_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, _, _, _, _, _, dm_steady_isSearchEqm _ (by norm_num) hθ h⟩

end Miao.SearchAndMatching
