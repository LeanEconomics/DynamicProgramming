/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# Hidden action: expectations over the output interval

Miao, §22.2, pp. 785–787. The integral facts the proofs of Propositions 22.2.1–22.2.3 use, for
expectations `E[g] = ∫_{y_lo}^{y_hi} g(y) p(y) dy` against a density `p` on the output interval:

* the mean value theorem for integrals (`ha_integral_mean_value`, used for (22.22));
* the expectation of the likelihood ratio, `E[f_a / f] = ∫ f_a` (`ha_expect_lr`), the
  covariance decomposition `E[g X] = Cov(g, X) + E[g] E[X]` (`ha_expect_mul_eq_cov_add`) and the
  MLRC covariance inequality: for `g` increasing and `f_a / f` increasing with `∫ f_a = 0`,
  `∫ g f_a = Cov(g, f_a / f) ≥ 0` (`ha_sign_change`, `ha_mlrc_integral_nonneg`,
  `ha_cov_lr_eq`, `ha_cov_lr_nonneg`), strictly when both are strictly increasing
  (`ha_mlrc_integral_pos`);
* the harmonic-mean form of Jensen's inequality, `(E[1/h])⁻¹ ≤ E[h]` for `h > 0`, strict when
  `h` is not constant (`ha_inv_expect_inv_le`, `ha_inv_expect_inv_lt`).

Functions are taken continuous on `ℝ`; only their values on `[y_lo, y_hi]` enter.
-/

namespace Miao.RecursiveContracts

open MeasureTheory

/-- Miao, p. 786: the expectation `E[g] = ∫ g(y) p(y) dy` over the output interval against the
density `p`. -/
noncomputable def ha_expect (ylo yhi : ℝ) (p g : ℝ → ℝ) : ℝ :=
  ∫ y in ylo..yhi, g y * p y

/-- Miao, p. 786: the covariance `Cov(g, h) = E[g h] − E[g] E[h]` under the density `p`. -/
noncomputable def ha_cov (ylo yhi : ℝ) (p g h : ℝ → ℝ) : ℝ :=
  ha_expect ylo yhi p (fun y => g y * h y) - ha_expect ylo yhi p g * ha_expect ylo yhi p h

/-- Miao, p. 786: `E[g h] = Cov(g, h) + E[g] E[h]`. -/
theorem ha_expect_mul_eq_cov_add (ylo yhi : ℝ) (p g h : ℝ → ℝ) :
    ha_expect ylo yhi p (fun y => g y * h y) =
      ha_cov ylo yhi p g h + ha_expect ylo yhi p g * ha_expect ylo yhi p h := by
  unfold ha_cov
  ring

/-- Miao, (22.22), p. 785: the mean value theorem for integrals: if `g` is continuous and `p` is
a continuous density on `[y_lo, y_hi]` (`p ≥ 0`, `∫ p = 1`), then `∫ g p = g(ŷ)` for some
`ŷ ∈ [y_lo, y_hi]`. -/
theorem ha_integral_mean_value {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g p : ℝ → ℝ}
    (hg : Continuous g) (hp : Continuous p) (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (hp1 : ∫ y in ylo..yhi, p y = 1) :
    ∃ yh ∈ Set.Icc ylo yhi, ∫ y in ylo..yhi, g y * p y = g yh := by
  have hK : IsCompact (Set.Icc ylo yhi) := isCompact_Icc
  have hne : (Set.Icc ylo yhi).Nonempty := Set.nonempty_Icc.2 hle
  obtain ⟨y1, hy1, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  obtain ⟨y2, hy2, hmax⟩ := hK.exists_isMaxOn hne hg.continuousOn
  have hlo : g y1 ≤ ∫ y in ylo..yhi, g y * p y := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hle
      ((show Continuous fun y => g y1 * p y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g y * p y by fun_prop).intervalIntegrable ylo yhi)
      (fun y hy => mul_le_mul_of_nonneg_right (hmin hy) (hp0 y hy))
    rwa [intervalIntegral.integral_const_mul, hp1, mul_one] at h
  have hhi : ∫ y in ylo..yhi, g y * p y ≤ g y2 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hle
      ((show Continuous fun y => g y * p y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g y2 * p y by fun_prop).intervalIntegrable ylo yhi)
      (fun y hy => mul_le_mul_of_nonneg_right (hmax hy) (hp0 y hy))
    rwa [intervalIntegral.integral_const_mul, hp1, mul_one] at h
  obtain ⟨yh, hyh, heq⟩ := intermediate_value_uIcc hg.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hlo, hhi⟩))
  exact ⟨yh, Set.uIcc_subset_Icc hy1 hy2 hyh, heq.symm⟩

/-- Miao, p. 786 (the step behind "by MLRC … the covariance term is nonnegative"): an increasing
likelihood ratio `r` changes sign once on `[y_lo, y_hi]`. For any `r` there is
`y* ∈ [y_lo, y_hi]` such that below `y*` some later point has `r ≤ 0` (so `r ≤ 0` there when `r` is
increasing) and `r > 0` above `y*`. -/
theorem ha_sign_change {ylo yhi : ℝ} (hle : ylo ≤ yhi) (r : ℝ → ℝ) :
    ∃ ys ∈ Set.Icc ylo yhi,
      (∀ y ∈ Set.Icc ylo yhi, y < ys → ∃ s ∈ Set.Icc ylo yhi, y < s ∧ r s ≤ 0) ∧
      (∀ y ∈ Set.Icc ylo yhi, ys < y → 0 < r y) := by
  set S : Set ℝ := insert ylo {y | y ∈ Set.Icc ylo yhi ∧ r y ≤ 0} with hS
  have hSne : S.Nonempty := ⟨ylo, Set.mem_insert _ _⟩
  have hSbdd : ∀ s ∈ S, s ≤ yhi := by
    intro s hs
    rcases hs with hs | hs
    · rw [hs]
      exact hle
    · exact hs.1.2
  have hbdd : BddAbove S := ⟨yhi, hSbdd⟩
  refine ⟨sSup S, ⟨le_csSup hbdd (Set.mem_insert _ _), csSup_le hSne hSbdd⟩, ?_, ?_⟩
  · intro y hy hlt
    obtain ⟨s, hs, hys⟩ := exists_lt_of_lt_csSup hSne hlt
    rcases hs with hs | hs
    · rw [hs] at hys
      exact absurd hy.1 (not_le.2 hys)
    · exact ⟨s, hs.1, hys, hs.2⟩
  · intro y hy hlt
    by_contra hneg
    have hmem : y ∈ S := Set.mem_insert_of_mem _ ⟨hy, not_lt.1 hneg⟩
    exact absurd (le_csSup hbdd hmem) (not_le.2 hlt)

/-- Miao, p. 786: the MLRC inequality: if `g` is increasing, the likelihood ratio `r = f_a / f`
is increasing (`f_a = r f`, `f ≥ 0` on the output interval) and `∫ f_a = 0`, then
`∫ g f_a ≥ 0`. -/
theorem ha_mlrc_integral_nonneg {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g r p q : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc ylo yhi)) (hr : MonotoneOn r (Set.Icc ylo yhi))
    (hq : ∀ y ∈ Set.Icc ylo yhi, q y = r y * p y) (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hgc : Continuous g) (hqc : Continuous q) :
    0 ≤ ∫ y in ylo..yhi, g y * q y := by
  obtain ⟨ys, hys, hbelow, habove⟩ := ha_sign_change hle r
  have hpt : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ (g y - g ys) * q y := by
    intro y hy
    rw [hq y hy]
    rcases lt_trichotomy y ys with hlt | heq | hgt
    · obtain ⟨s, hs, hys', hrs⟩ := hbelow y hy hlt
      have hry : r y ≤ 0 := (hr hy hs hys'.le).trans hrs
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hg hy hys hlt.le))
        (mul_nonpos_of_nonpos_of_nonneg hry (hp0 y hy))
    · rw [heq, sub_self, zero_mul]
    · exact mul_nonneg (sub_nonneg.2 (hg hys hy hgt.le))
        (mul_nonneg (habove y hy hgt).le (hp0 y hy))
  have hsplit : ∫ y in ylo..yhi, g y * q y =
      (∫ y in ylo..yhi, (g y - g ys) * q y) + g ys * ∫ y in ylo..yhi, q y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((show Continuous fun y => (g y - g ys) * q y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g ys * q y by fun_prop).intervalIntegrable ylo yhi)]
    congr 1
    funext y
    ring
  rw [hsplit, hq0, mul_zero, add_zero]
  exact intervalIntegral.integral_nonneg hle hpt

/-- Miao, p. 787 ("contradicting MLRC"): under the strict MLRC, `∫ g f_a > 0` for every strictly
increasing continuous `g` (in particular `g(y) = y`), when `y_lo < y_hi`, `f > 0` on the output
interval and `∫ f_a = 0`. -/
theorem ha_mlrc_integral_pos {ylo yhi : ℝ} (hlt : ylo < yhi) {g r p q : ℝ → ℝ}
    (hg : StrictMonoOn g (Set.Icc ylo yhi)) (hr : StrictMonoOn r (Set.Icc ylo yhi))
    (hq : ∀ y ∈ Set.Icc ylo yhi, q y = r y * p y) (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 < p y)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hgc : Continuous g) (hqc : Continuous q) :
    0 < ∫ y in ylo..yhi, g y * q y := by
  obtain ⟨ys, hys, hbelow, habove⟩ := ha_sign_change hlt.le r
  have hpt : ∀ y ∈ Set.Icc ylo yhi, y ≠ ys → 0 < (g y - g ys) * q y := by
    intro y hy hne
    rw [hq y hy]
    rcases lt_or_gt_of_ne hne with hlt' | hgt
    · obtain ⟨s, hs, hys', hrs⟩ := hbelow y hy hlt'
      have hry : r y < 0 := (hr hy hs hys').trans_le hrs
      exact mul_pos_of_neg_of_neg (sub_neg.2 (hg hy hys hlt'))
        (mul_neg_of_neg_of_pos hry (hp0 y hy))
    · exact mul_pos (sub_pos.2 (hg hys hy hgt)) (mul_pos (habove y hy hgt) (hp0 y hy))
  have hpt0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ (g y - g ys) * q y := by
    intro y hy
    by_cases hne : y = ys
    · rw [hne, sub_self, zero_mul]
    · exact (hpt y hy hne).le
  have hsplit : ∫ y in ylo..yhi, g y * q y =
      (∫ y in ylo..yhi, (g y - g ys) * q y) + g ys * ∫ y in ylo..yhi, q y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((show Continuous fun y => (g y - g ys) * q y by fun_prop).intervalIntegrable ylo yhi)
      ((show Continuous fun y => g ys * q y by fun_prop).intervalIntegrable ylo yhi)]
    congr 1
    funext y
    ring
  rw [hsplit, hq0, mul_zero, add_zero]
  have hex : ∃ c ∈ Set.Icc ylo yhi, 0 < (g c - g ys) * q c := by
    by_cases hne : ylo = ys
    · exact ⟨yhi, ⟨hlt.le, le_rfl⟩, hpt yhi ⟨hlt.le, le_rfl⟩ (by rw [← hne]; exact hlt.ne')⟩
    · exact ⟨ylo, ⟨le_rfl, hlt.le⟩, hpt ylo ⟨le_rfl, hlt.le⟩ hne⟩
  exact intervalIntegral.integral_pos hlt
    ((show Continuous fun y => (g y - g ys) * q y by fun_prop).continuousOn)
    (fun y hy => hpt0 y ⟨hy.1.le, hy.2⟩) hex

/-- Miao, p. 786: `E[f_a / f] = ∫ f_a(y | a) dy` when `f > 0` on the output interval. -/
theorem ha_expect_lr {ylo yhi : ℝ} (hle : ylo ≤ yhi) {p q : ℝ → ℝ}
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) :
    ha_expect ylo yhi p (fun y => q y / p y) = ∫ y in ylo..yhi, q y := by
  unfold ha_expect
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le hle] at hy
  have := (hp y hy).ne'
  field_simp

/-- Miao, p. 786: with `∫ f_a = 0`, `∫ g f_a = E[g · f_a / f] = Cov(g, f_a / f)`, the book's
rewriting of the first term of (22.18). -/
theorem ha_cov_lr_eq {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g p q : ℝ → ℝ}
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0) :
    ∫ y in ylo..yhi, g y * q y = ha_cov ylo yhi p g (fun y => q y / p y) := by
  unfold ha_cov
  rw [ha_expect_lr hle hp, hq0, mul_zero, sub_zero]
  unfold ha_expect
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le hle] at hy
  have := (hp y hy).ne'
  simp only
  field_simp

/-- Miao, p. 786: "By MLRC and the monotonicity of `[y − c(v, y) + β P(w(v, y))]`, the above
covariance term is nonnegative": `Cov(g, f_a / f) ≥ 0` for `g` increasing under MLRC, when
`∫ f_a = 0`. -/
theorem ha_cov_lr_nonneg {ylo yhi : ℝ} (hle : ylo ≤ yhi) {g p q : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc ylo yhi))
    (hr : MonotoneOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0)
    (hgc : Continuous g) (hqc : Continuous q) :
    0 ≤ ha_cov ylo yhi p g (fun y => q y / p y) := by
  rw [← ha_cov_lr_eq hle hp hq0]
  refine ha_mlrc_integral_nonneg hle hg hr (fun y hy => ?_) (fun y hy => (hp y hy).le) hq0 hgc hqc
  have := (hp y hy).ne'
  field_simp

/-- Miao, p. 787 ("It follows from Jensen's inequality"), harmonic-mean form: for a continuous
`h > 0` and a continuous density `p` on the output interval, `(∫ (1/h) p)⁻¹ ≤ ∫ h p`. -/
theorem ha_inv_expect_inv_le {ylo yhi : ℝ} (hle : ylo ≤ yhi) {h p : ℝ → ℝ}
    (hh : Continuous h) (hpos : ∀ y, 0 < h y) (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y) (hp1 : ∫ y in ylo..yhi, p y = 1) :
    (∫ y in ylo..yhi, 1 / h y * p y)⁻¹ ≤ ∫ y in ylo..yhi, h y * p y := by
  have hinvc : Continuous fun y => 1 / h y := continuous_const.div hh (fun y => (hpos y).ne')
  obtain ⟨yh, -, hG⟩ := ha_integral_mean_value hle hinvc hp hp0 hp1
  set G := ∫ y in ylo..yhi, 1 / h y * p y with hGdef
  have hGpos : 0 < G := by rw [hG]; exact one_div_pos.2 (hpos yh)
  set t := G⁻¹ with ht
  have hpt : ∀ y ∈ Set.Icc ylo yhi, 2 * t * p y - t ^ 2 * (1 / h y * p y) ≤ h y * p y := by
    intro y hy
    have hhy := hpos y
    have hid : h y * p y - (2 * t * p y - t ^ 2 * (1 / h y * p y)) =
        (h y - t) ^ 2 / h y * p y := by
      field_simp
      ring
    have : 0 ≤ (h y - t) ^ 2 / h y * p y :=
      mul_nonneg (div_nonneg (sq_nonneg _) hhy.le) (hp0 y hy)
    linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hle
    ((show Continuous fun y => 2 * t * p y - t ^ 2 * (1 / h y * p y) by
      fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => h y * p y by fun_prop).intervalIntegrable ylo yhi) hpt
  rw [intervalIntegral.integral_sub
    ((show Continuous fun y => 2 * t * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => t ^ 2 * (1 / h y * p y) by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp1, ← hGdef]
    at hmono
  have htG : t * G = 1 := inv_mul_cancel₀ hGpos.ne'
  nlinarith

/-- Miao, p. 787: the strict harmonic-mean Jensen inequality: if moreover `p > 0` on the output
interval, `y_lo < y_hi` and `h` is not constant on it, then `(∫ (1/h) p)⁻¹ < ∫ h p`. -/
theorem ha_inv_expect_inv_lt {ylo yhi : ℝ} (hlt : ylo < yhi) {h p : ℝ → ℝ}
    (hh : Continuous h) (hpos : ∀ y, 0 < h y) (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hnc : ∃ y₁ ∈ Set.Icc ylo yhi, ∃ y₂ ∈ Set.Icc ylo yhi, h y₁ ≠ h y₂) :
    (∫ y in ylo..yhi, 1 / h y * p y)⁻¹ < ∫ y in ylo..yhi, h y * p y := by
  have hinvc : Continuous fun y => 1 / h y := continuous_const.div hh (fun y => (hpos y).ne')
  obtain ⟨yh, -, hG⟩ := ha_integral_mean_value hlt.le hinvc hp (fun y hy => (hp0 y hy).le) hp1
  set G := ∫ y in ylo..yhi, 1 / h y * p y with hGdef
  have hGpos : 0 < G := by rw [hG]; exact one_div_pos.2 (hpos yh)
  set t := G⁻¹ with ht
  have hid : ∀ y, h y * p y - (2 * t * p y - t ^ 2 * (1 / h y * p y)) =
      (h y - t) ^ 2 / h y * p y := by
    intro y
    have hhy := hpos y
    field_simp
    ring
  have hpt : ∀ y ∈ Set.Ioc ylo yhi, 2 * t * p y - t ^ 2 * (1 / h y * p y) ≤ h y * p y := by
    intro y hy
    have : 0 ≤ (h y - t) ^ 2 / h y * p y :=
      mul_nonneg (div_nonneg (sq_nonneg _) (hpos y).le) (hp0 y ⟨hy.1.le, hy.2⟩).le
    linarith [hid y]
  have hex : ∃ c ∈ Set.Icc ylo yhi, 2 * t * p c - t ^ 2 * (1 / h c * p c) < h c * p c := by
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hnc
    have hc : ∃ c ∈ Set.Icc ylo yhi, h c ≠ t := by
      by_cases h1 : h y₁ = t
      · exact ⟨y₂, hy₂, fun h2 => hne (h1.trans h2.symm)⟩
      · exact ⟨y₁, hy₁, h1⟩
    obtain ⟨c, hc, hct⟩ := hc
    refine ⟨c, hc, ?_⟩
    have : 0 < (h c - t) ^ 2 / h c * p c :=
      mul_pos (div_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hct)) (hpos c)) (hp0 c hc)
    linarith [hid c]
  have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hlt
    ((show Continuous fun y => 2 * t * p y - t ^ 2 * (1 / h y * p y) by
      fun_prop).continuousOn)
    ((show Continuous fun y => h y * p y by fun_prop).continuousOn) hpt hex
  rw [intervalIntegral.integral_sub
    ((show Continuous fun y => 2 * t * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => t ^ 2 * (1 / h y * p y) by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp1, ← hGdef]
    at hstrict
  have htG : t * G = 1 := inv_mul_cancel₀ hGpos.ne'
  nlinarith

end Miao.RecursiveContracts
