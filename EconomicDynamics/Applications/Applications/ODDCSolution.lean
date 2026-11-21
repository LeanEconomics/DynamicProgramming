/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.ODDCTrigger
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Discrete choice: the free boundary problem (8.1) and its solution

Miao, §8.2, pp. 235–236. In addition to the standing assumptions of `ODDCTrigger`, `c` is
differentiable with continuous derivative `c′`, and `s* ≥ 0` is an indifference point (it exists
under the condition of `od_dc_trigger_exists`). Write `k = λ(1 − β)`.

* `od_dcE_hasDerivAt`: `(E V)′(s) = λE V(s) − λV(s)`, from `E V(s) = λe^{λs} ∫_s^∞ V e^{−λs′}`.
* **(8.1)** (`eq_8_1`): on `(0, s*)`, `V′(s) = −c′(s) + λc(s) + λ(1 − β)V(s)`.
* `od_dc_solution` (p. 236): on `[0, s*]`,
  `V(s) = −c(s)/(1 − β) − ∫_s^{s*} βc′(y)/(1 − β) e^{−k(y − s)} dy`, and, equivalently
  (`od_dc_solution_book`), `V(s) = −c(s*)/(1 − β) + ∫_s^{s*} c′(y)/(1 − β)[1 − βe^{−k(y − s)}] dy`;
  on `[s*, ∞)`, `V = −c(s*)/(1 − β)` (`eq_8_2`, `od_dc_trigger`).
* `od_dc_trigger_eq` (p. 236): `P_b − P_s = ∫_0^{s*} c′(z)/(1 − β)[1 − βe^{−kz}] dz`, and
  `od_dc_trigger_eq_unique`: `s*` is its only solution in `[0, ∞)`.
* The optimal policy is to replace iff `s > s*` (`od_dc_trigger`).

**Correction (the solution formula).** The book prints
`V(s) = max{−c(s*)/(1 − β), −c(s)/(1 − β) + ∫_s^{s*} c′(y)/(1 − β)[1 − βe^{−k(y − s)}] dy}`. The
second term exceeds the true value by `(c(s*) − c(s))/(1 − β) > 0` on `[0, s*)`
(`od_dc_solution_misprint`); the leading term must be `−c(s*)/(1 − β)`, not `−c(s)/(1 − β)`. The
printed formula is also inconsistent with the trigger equation printed next to it. A concrete
model where it fails is `od_dc_example_misprint` in `ODDCExamples`. We state the corrected formula
on `[0, s*]` and the constant value on `[s*, ∞)` separately.
-/

namespace Miao.Applications

open MeasureTheory Real BoundedContinuousFunction Filter Topology

/-- A function with a derivative at `z` that is increasing on `[z, ∞)` has a nonnegative
derivative at `z`. -/
theorem od_deriv_nonneg_of_monotoneOn {g : ℝ → ℝ} {g' z : ℝ} (hd : HasDerivAt g g' z)
    (hg : MonotoneOn g (Set.Ici z)) : 0 ≤ g' := by
  have h := hd.hasDerivWithinAt (s := Set.Ioi z)
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.sdiff_singleton_eq_self (by simp)] at h
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.2 (hg (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_of_lt hy))
    (le_of_lt hy))) (sub_nonneg.2 (le_of_lt hy))

/-- `(E V)′(s) = λ E V(s) − λ V(s)`. -/
theorem od_dcE_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (V : ℝ →ᵇ ℝ) (s : ℝ) :
    HasDerivAt (od_dcE lam V) (lam * od_dcE lam V s - lam * V s) s := by
  set g := fun y => V y * exp (-(lam * y))
  have hgc : Continuous g := V.continuous.mul (by fun_prop)
  have hgi : ∀ a, IntegrableOn g (Set.Ioi a) := fun a => by
    have he : IntegrableOn (fun y => exp (-(lam * y))) (Set.Ioi a) := by
      have := exp_neg_integrableOn_Ioi a hlam
      simpa only [neg_mul] using this
    refine Integrable.mono' (he.const_mul ‖V‖) hgc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [g, norm_mul, Real.norm_of_nonneg (exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (V.norm_coe_le_norm y) (exp_pos _).le
  have hform : ∀ t, od_dcE lam V t =
      lam * exp (lam * t) * ((∫ y in Set.Ioi 0, g y) - ∫ y in (0 : ℝ)..t, g y) := fun t => by
    rw [od_dcE_book, ← intervalIntegral.integral_Ioi_sub_Ioi' (hgi 0) (hgi t), sub_sub_cancel,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [g]
    rw [show -(lam * (y - t)) = lam * t + -(lam * y) by ring, exp_add]
    ring
  have hG : HasDerivAt (fun t => (∫ y in Set.Ioi 0, g y) - ∫ y in (0 : ℝ)..t, g y) (0 - g s) s :=
    (hasDerivAt_const _ _).sub (intervalIntegral.integral_hasDerivAt_right
      (hgc.intervalIntegrable _ _) (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt)
  have hexp : HasDerivAt (fun t => lam * exp (lam * t)) (lam * (exp (lam * s) * (lam * 1))) s :=
    (((hasDerivAt_id s).const_mul lam).exp).const_mul lam
  have h := hexp.mul hG
  have hfun : od_dcE lam V = fun t =>
      lam * exp (lam * t) * ((∫ y in Set.Ioi 0, g y) - ∫ y in (0 : ℝ)..t, g y) := funext hform
  rw [hfun]
  convert h using 1
  have h1 : exp (lam * s) * exp (-(lam * s)) = 1 := by rw [← exp_add]; simp
  simp only [g]
  linear_combination (lam * V s) * h1

variable {lam β Pb Ps : ℝ} {c : ℝ →ᵇ ℝ} {c' : ℝ → ℝ} {V : ℝ →ᵇ ℝ}

/-- The maintenance value `M = −c + βE V` is differentiable. -/
theorem od_dcM_hasDerivAt (hlam : 0 < lam) (hc' : ∀ s, HasDerivAt c (c' s) s) (s : ℝ) :
    HasDerivAt (od_dcM c lam β V) (-c' s + β * (lam * od_dcE lam V s - lam * V s)) s :=
  (hc' s).neg.add ((od_dcE_hasDerivAt hlam V s).const_mul β)

/-- **(8.1)** (Miao, p. 235): on the maintenance region `(0, s*)`,
`V′(s) = −c′(s) + λc(s) + λ(1 − β)V(s)`. -/
theorem eq_8_1 (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s)
    (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    ∀ s ∈ Set.Ioo 0 ss, HasDerivAt V (-c' s + lam * c s + lam * (1 - β) * V s) s := by
  obtain ⟨-, hlow, -, -, -⟩ := od_dc_trigger hlam hβ0 hβ1 hPb hc hV hss hind
  intro s hs
  have hev : (od_dcM c lam β V) =ᶠ[𝓝 s] V := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with y hy
    exact ((hlow y hy.1.le hy.2).2).symm
  have hVs : V s = od_dcM c lam β V s := (hlow s hs.1.le hs.2).2
  have h := (od_dcM_hasDerivAt (β := β) (V := V) hlam hc' s).congr_of_eventuallyEq hev.symm
  convert h using 1
  rw [od_dcM] at hVs
  linear_combination lam * hVs

/-- On `[0, s*]` the value function equals the maintenance value. -/
theorem od_dc_eq_M (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    ∀ s ∈ Set.Icc 0 ss, V s = od_dcM c lam β V s := by
  obtain ⟨-, hlow, -, hR, -⟩ := od_dc_trigger hlam hβ0 hβ1 hPb hc hV hss hind
  intro s hs
  rcases hs.2.lt_or_eq with h | h
  · exact (hlow s hs.1 h).2
  · rw [h, hR ss le_rfl, hind]

/-- Miao, p. 236, the solution of the free boundary problem: on `[0, s*]`,
`V(s) = −c(s)/(1 − β) − ∫_s^{s*} βc′(y)/(1 − β) e^{−λ(1 − β)(y − s)} dy`. -/
theorem od_dc_solution (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s) (hc'c : Continuous c')
    (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    ∀ s ∈ Set.Icc 0 ss, V s = -c s / (1 - β) -
      ∫ y in s..ss, β * c' y / (1 - β) * exp (-(lam * (1 - β) * (y - s))) := by
  intro s hs
  have hne : 1 - β ≠ 0 := by linarith
  have hM := od_dc_eq_M hlam hβ0 hβ1 hPb hc hV hss hind
  set φ := fun y => exp (-(lam * (1 - β) * y)) * (od_dcM c lam β V y + c y / (1 - β))
  have hderiv : ∀ y ∈ Set.uIcc s ss,
      HasDerivAt φ (exp (-(lam * (1 - β) * y)) * (β * c' y / (1 - β))) y := by
    intro y hy
    rw [Set.uIcc_of_le hs.2] at hy
    have hy' : y ∈ Set.Icc 0 ss := ⟨hs.1.trans hy.1, hy.2⟩
    have hVy := hM y hy'
    have hMd := od_dcM_hasDerivAt (β := β) (V := V) hlam hc' y
    have he : HasDerivAt (fun y => exp (-(lam * (1 - β) * y)))
        (exp (-(lam * (1 - β) * y)) * (-(lam * (1 - β) * 1))) y :=
      ((hasDerivAt_id y).const_mul (lam * (1 - β))).neg.exp
    have h := he.mul (hMd.add ((hc' y).div_const (1 - β)))
    convert h using 1
    rw [od_dcM] at hVy
    simp only [Pi.add_apply, od_dcM]
    have hκ : (1 - β)⁻¹ * (1 - β) = 1 := inv_mul_cancel₀ hne
    simp only [div_eq_mul_inv]
    linear_combination (exp (-(lam * (1 - β) * y)) * β * lam) * hVy +
      (exp (-(lam * (1 - β) * y)) * (lam * c y - c' y)) * hκ
  have hint : IntervalIntegrable (fun y => exp (-(lam * (1 - β) * y)) * (β * c' y / (1 - β)))
      volume s ss :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  obtain ⟨-, -, -, h4, -⟩ := eq_8_2 hlam hβ0 hβ1 hPb hc hV hss hind
  have hφss : φ ss = 0 := by
    simp only [φ]
    rw [← hM ss ⟨hss, le_rfl⟩, h4]
    field_simp
    ring
  rw [hφss, zero_sub] at hftc
  have hφs : φ s = exp (-(lam * (1 - β) * s)) * (V s + c s / (1 - β)) := by
    simp only [φ]; rw [← hM s hs]
  have hpull : ∫ y in s..ss, β * c' y / (1 - β) * exp (-(lam * (1 - β) * (y - s))) =
      exp (lam * (1 - β) * s) *
        ∫ y in s..ss, exp (-(lam * (1 - β) * y)) * (β * c' y / (1 - β)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [show -(lam * (1 - β) * (y - s)) = lam * (1 - β) * s + -(lam * (1 - β) * y) by ring,
      exp_add]
    ring
  rw [hpull, hftc, hφs]
  have h1 : exp (lam * (1 - β) * s) * exp (-(lam * (1 - β) * s)) = 1 := by rw [← exp_add]; simp
  linear_combination (-(V s + c s / (1 - β))) * h1

/-- Miao, p. 236 (corrected form of the printed solution): on `[0, s*]`,
`V(s) = −c(s*)/(1 − β) + ∫_s^{s*} c′(y)/(1 − β)[1 − βe^{−λ(1 − β)(y − s)}] dy`. -/
theorem od_dc_solution_book (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s) (hc'c : Continuous c')
    (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    ∀ s ∈ Set.Icc 0 ss, V s = -c ss / (1 - β) +
      ∫ y in s..ss, c' y / (1 - β) * (1 - β * exp (-(lam * (1 - β) * (y - s)))) := by
  intro s hs
  have hne : 1 - β ≠ 0 := by linarith
  rw [od_dc_solution hlam hβ0 hβ1 hPb hc hc' hc'c hV hss hind s hs]
  have hsplit : ∫ y in s..ss, c' y / (1 - β) * (1 - β * exp (-(lam * (1 - β) * (y - s)))) =
      (∫ y in s..ss, c' y) / (1 - β) -
        ∫ y in s..ss, β * c' y / (1 - β) * exp (-(lam * (1 - β) * (y - s))) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      ((hc'c.div_const _).intervalIntegrable _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  have hftc : ∫ y in s..ss, c' y = c ss - c s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hc' y) (hc'c.intervalIntegrable _ _)
  rw [hsplit, hftc]
  field_simp
  ring

/-- Miao, p. 236, the trigger equation:
`P_b − P_s = ∫_0^{s*} c′(z)/(1 − β)[1 − βe^{−λ(1 − β)z}] dz`. -/
theorem od_dc_trigger_eq (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s) (hc'c : Continuous c')
    (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    Pb - Ps = ∫ z in (0 : ℝ)..ss, c' z / (1 - β) * (1 - β * exp (-(lam * (1 - β) * z))) := by
  have h := od_dc_solution_book hlam hβ0 hβ1 hPb hc hc' hc'c hV hss hind 0 ⟨le_rfl, hss⟩
  obtain ⟨-, -, -, -, h5⟩ := eq_8_2 hlam hβ0 hβ1 hPb hc hV hss hind
  simp only [sub_zero] at h
  rw [neg_div] at h
  linarith

/-- The right side of the trigger equation, `h(t) = ∫_0^t c′(z)/(1 − β)[1 − βe^{−λ(1 − β)z}] dz`. -/
noncomputable def od_dcH (c' : ℝ → ℝ) (lam β t : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..t, c' z / (1 - β) * (1 - β * exp (-(lam * (1 - β) * z)))

/-- `h` is strictly increasing on `[0, ∞)` when `c` is strictly increasing there. -/
theorem od_dcH_strictMonoOn (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s) (hc'c : Continuous c') :
    StrictMonoOn (od_dcH c' lam β) (Set.Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ h12
  have hi : Continuous fun z => c' z / (1 - β) * (1 - β * exp (-(lam * (1 - β) * z))) := by
    fun_prop
  have hdiff : od_dcH c' lam β t₂ - od_dcH c' lam β t₁ =
      ∫ z in t₁..t₂, c' z / (1 - β) * (1 - β * exp (-(lam * (1 - β) * z))) := by
    unfold od_dcH
    rw [intervalIntegral.integral_interval_sub_left (hi.intervalIntegrable _ _)
      (hi.intervalIntegrable _ _)]
  have hle : ∫ z in t₁..t₂, c' z ≤
      ∫ z in t₁..t₂, c' z / (1 - β) * (1 - β * exp (-(lam * (1 - β) * z))) := by
    refine intervalIntegral.integral_mono_on h12.le (hc'c.intervalIntegrable _ _)
      (hi.intervalIntegrable _ _) fun z hz => ?_
    have hz0 : 0 ≤ z := (Set.mem_Ici.1 ht₁).trans hz.1
    have hcz : 0 ≤ c' z := od_deriv_nonneg_of_monotoneOn (hc' z) fun x hx y hy hxy =>
      hc.monotoneOn (Set.mem_Ici.2 (hz0.trans hx)) (Set.mem_Ici.2 (hz0.trans hy)) hxy
    have he : exp (-(lam * (1 - β) * z)) ≤ 1 := by
      rw [exp_le_one_iff]
      have : 0 ≤ lam * (1 - β) * z := mul_nonneg (mul_nonneg hlam.le (by linarith)) hz0
      linarith
    have hpos : 0 < 1 - β := by linarith
    have hfac : 1 ≤ (1 - β * exp (-(lam * (1 - β) * z))) / (1 - β) := by
      rw [le_div_iff₀ hpos]; nlinarith
    calc c' z = c' z * 1 := (mul_one _).symm
      _ ≤ c' z * ((1 - β * exp (-(lam * (1 - β) * z))) / (1 - β)) :=
          mul_le_mul_of_nonneg_left hfac hcz
      _ = c' z / (1 - β) * (1 - β * exp (-(lam * (1 - β) * z))) := by ring
  have hftc : ∫ z in t₁..t₂, c' z = c t₂ - c t₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hc' y) (hc'c.intervalIntegrable _ _)
  have := hc ht₁ ht₂ h12
  linarith

/-- Miao, p. 236 ("`s*` is the unique solution"): `s*` is the only `t ≥ 0` solving the trigger
equation `P_b − P_s = h(t)`. -/
theorem od_dc_trigger_eq_unique (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s) (hc'c : Continuous c')
    (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) {t : ℝ} (ht : 0 ≤ t)
    (htrig : Pb - Ps = od_dcH c' lam β t) : t = ss := by
  have hs := od_dc_trigger_eq hlam hβ0 hβ1 hPb hc hc' hc'c hV hss hind
  exact (od_dcH_strictMonoOn hlam hβ0 hβ1 hc hc' hc'c).injOn ht hss (htrig.symm.trans hs)

/-- Miao, p. 236, the misprint: the printed second term
`P(s) = −c(s)/(1 − β) + ∫_s^{s*} c′(y)/(1 − β)[1 − βe^{−λ(1 − β)(y − s)}] dy` exceeds the value
function by `(c(s*) − c(s))/(1 − β)` on `[0, s*]`, so on `[0, s*)` the printed formula
`max{−c(s*)/(1 − β), P(s)}` is strictly above `V(s)`. -/
theorem od_dc_solution_misprint (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hc' : ∀ s, HasDerivAt c (c' s) s) (hc'c : Continuous c')
    (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    ∀ s ∈ Set.Ico 0 ss,
      let P := -c s / (1 - β) +
        ∫ y in s..ss, c' y / (1 - β) * (1 - β * exp (-(lam * (1 - β) * (y - s))))
      P = V s + (c ss - c s) / (1 - β) ∧ V s < max (-c ss / (1 - β)) P := by
  intro s hs P
  have hb := od_dc_solution_book hlam hβ0 hβ1 hPb hc hc' hc'c hV hss hind s ⟨hs.1, hs.2.le⟩
  have hne : 1 - β ≠ 0 := by linarith
  have hpos : 0 < 1 - β := by linarith
  have hP : P = V s + (c ss - c s) / (1 - β) := by
    simp only [P]; rw [hb]; field_simp; ring
  refine ⟨hP, lt_of_lt_of_le ?_ (le_max_right _ _)⟩
  rw [hP]
  have := hc (Set.mem_Ici.2 hs.1) (Set.mem_Ici.2 hss) hs.2
  have : 0 < (c ss - c s) / (1 - β) := div_pos (by linarith) hpos
  linarith

end Miao.Applications
