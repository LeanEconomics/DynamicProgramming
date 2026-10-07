/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.ContinuationValues
import AdditionalApplications.BMOperators
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.ProjIcc

/-!
# Job search with learning

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.2.3 (pp. 264–269), with
Proposition A.5.34 (p. 391).

Offers are drawn iid from one of two densities `f`, `g` on `ℝ`, positive on `(0, M)` and zero
elsewhere (Assumption 8.2.1); the worker's belief that the density is `f` updates by Bayes' rule
`κ(w, π) = πf(w)/(πf(w) + (1 − π)g(w))` (8.32), and `φ_π = πf + (1 − π)g`.

The state space is taken to be `[0, M] × [0, 1]` rather than `(0, M) × (0, 1)`: the closed
intervals are invariant (`κ(w', π) ∈ [0, 1]` for `π ∈ [0, 1]`), and offers outside `(0, M)` carry
no weight.

* **Exercises 8.2.6–8.2.7**: the ADP on `b([0, M] × [0, 1])`; the stopping policy is greedy and
  the Bellman equation is (8.33).
* **Exercises 8.2.8–8.2.9**: the reservation wage operator `T̂` (8.36) is a contraction of
  modulus `β` on `b[0, 1]` and maps `bc[0, 1]` into itself.
* **Proposition A.5.34** (monotone likelihood ratio implies first order stochastic dominance),
  **Exercise 8.2.10** (mixtures are ordered in `α`) and **Proposition 8.2.1**: under the monotone
  likelihood ratio property, the optimal reservation wage `ω*` is increasing in `π`.
* **Exercise 8.2.11**: the Beta(4, 2) and Beta(2, 4) densities of (8.38) have the monotone
  likelihood ratio property.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### Monotone likelihood ratios and stochastic dominance -/

/-- The monotone likelihood ratio property on `(0, M)`: `g/f` is decreasing, written without
division as `g(w₂)f(w₁) ≤ g(w₁)f(w₂)` for `w₁ ≤ w₂`. -/
def IsMLR (f g : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ w₁ ∈ Ioo 0 M, ∀ w₂ ∈ Ioo 0 M, w₁ ≤ w₂ → g w₂ * f w₁ ≤ g w₁ * f w₂

/-- Two densities positive on `(0, M)` and vanishing elsewhere (Assumption 8.2.1). -/
structure TwoDensities (M : ℝ) where
  M_pos : 0 < M
  f : ℝ → ℝ
  g : ℝ → ℝ
  measurable_f : Measurable f
  measurable_g : Measurable g
  integral_f : ∫ w, f w = 1
  integral_g : ∫ w, g w = 1
  f_pos : ∀ w ∈ Ioo 0 M, 0 < f w
  g_pos : ∀ w ∈ Ioo 0 M, 0 < g w
  f_zero : ∀ w ∉ Ioo 0 M, f w = 0
  g_zero : ∀ w ∉ Ioo 0 M, g w = 0

namespace TwoDensities

variable {M : ℝ} (D : TwoDensities M)

theorem f_nonneg (w : ℝ) : 0 ≤ D.f w := by
  by_cases h : w ∈ Ioo 0 M
  · exact (D.f_pos w h).le
  · rw [D.f_zero w h]

theorem g_nonneg (w : ℝ) : 0 ≤ D.g w := by
  by_cases h : w ∈ Ioo 0 M
  · exact (D.g_pos w h).le
  · rw [D.g_zero w h]

theorem integrable_f : Integrable D.f :=
  Integrable.of_integral_ne_zero (by rw [D.integral_f]; exact one_ne_zero)

theorem integrable_g : Integrable D.g :=
  Integrable.of_integral_ne_zero (by rw [D.integral_g]; exact one_ne_zero)

theorem integrable_mul {u : ℝ → ℝ} (hum : Measurable u) {C : ℝ} (hC : ∀ w, |u w| ≤ C)
    {h : ℝ → ℝ} (hh : Integrable h) : Integrable (fun w => u w * h w) :=
  hh.bdd_mul hum.aestronglyMeasurable (Eventually.of_forall fun w => by
    rw [Real.norm_eq_abs]; exact hC w)

/-- **Proposition A.5.34** (p. 391), for densities: if `g/f` is decreasing on `(0, M)`, then
`G ⪯_F F`: `∫ ug ≤ ∫ uf` for every bounded measurable `u` increasing on `(0, M)`. The densities
cross once: `f < g` on an initial segment of `(0, M)` and `f ≥ g` after it. -/
theorem proposition_A_5_34 (hmlr : IsMLR D.f D.g M) {u : ℝ → ℝ} (hum : Measurable u) {C : ℝ}
    (hC : ∀ w, |u w| ≤ C) (hmono : MonotoneOn u (Ioo 0 M)) :
    ∫ w, u w * D.g w ≤ ∫ w, u w * D.f w := by
  classical
  -- the set where `f < g` is an initial segment of `(0, M)`
  set A := {w ∈ Ioo 0 M | D.f w < D.g w}
  have hdown : ∀ w ∈ A, ∀ w' ∈ Ioo 0 M, w' ≤ w → w' ∈ A := by
    rintro w ⟨hw, hfg⟩ w' hw' hle
    refine ⟨hw', not_le.1 fun hge => ?_⟩
    have h1 := hmlr w' hw' w hw hle
    have hf' := D.f_pos w' hw'
    have : D.g w * D.f w' ≤ D.f w' * D.f w := h1.trans (mul_le_mul_of_nonneg_right hge
      (D.f_pos w hw).le)
    have : D.g w ≤ D.f w := by nlinarith
    linarith
  have hbdd : BddAbove (insert 0 A) := ⟨M, by
    rintro x (rfl | hx)
    · exact D.M_pos.le
    · exact hx.1.2.le⟩
  set x0 := sSup (insert 0 A)
  have hleft : ∀ w ∈ Ioo 0 M, w < x0 → D.f w < D.g w := by
    intro w hw hlt
    obtain ⟨a, ha, hwa⟩ := exists_lt_of_lt_csSup (insert_nonempty 0 A) hlt
    rcases ha with rfl | ha
    · exact absurd hwa (not_lt.2 hw.1.le)
    · exact (hdown a ha w hw hwa.le).2
  have hright : ∀ w ∈ Ioo 0 M, x0 < w → D.g w ≤ D.f w := by
    intro w hw hlt
    by_contra h
    have : w ∈ A := ⟨hw, not_le.1 h⟩
    exact absurd (le_csSup hbdd (mem_insert_of_mem 0 this)) (not_le.2 hlt)
  -- a constant separating the values of `u` on either side of `x0`
  set L := {w ∈ Ioo 0 M | w < x0}
  set k : ℝ := if L.Nonempty then sSup (u '' L) else -C
  have hkL : ∀ w ∈ L, u w ≤ k := by
    intro w hw
    have hne : L.Nonempty := ⟨w, hw⟩
    simp only [k, hne, ↓reduceIte]
    exact le_csSup ⟨C, by rintro _ ⟨y, -, rfl⟩; exact (le_abs_self _).trans (hC y)⟩ ⟨w, hw, rfl⟩
  have hkR : ∀ w ∈ Ioo 0 M, x0 < w → k ≤ u w := by
    intro w hw hlt
    by_cases hne : L.Nonempty
    · simp only [k, hne, ↓reduceIte]
      refine csSup_le (hne.image u) ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hmono hy.1 hw (hy.2.trans hlt).le
    · simp only [k, hne, ↓reduceIte]
      exact neg_le_of_abs_le (hC w)
  -- the integrand `(u − k)(f − g)` is nonnegative off `x0`
  have hpt : ∀ w, w ≠ x0 → 0 ≤ (u w - k) * (D.f w - D.g w) := by
    intro w hne
    by_cases hw : w ∈ Ioo 0 M
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hkL w ⟨hw, hlt⟩))
          (sub_nonpos.2 (hleft w hw hlt).le)
      · exact mul_nonneg (sub_nonneg.2 (hkR w hw hgt)) (sub_nonneg.2 (hright w hw hgt))
    · rw [D.f_zero w hw, D.g_zero w hw, sub_self, mul_zero]
  have hae : ∀ᵐ w ∂(volume : Measure ℝ), w ≠ x0 := by
    rw [ae_iff]
    simp
  have hint : 0 ≤ ∫ w, (u w - k) * (D.f w - D.g w) :=
    integral_nonneg_of_ae (hae.mono fun w hw => hpt w hw)
  have hiuf := integrable_mul hum hC D.integrable_f
  have hiug := integrable_mul hum hC D.integrable_g
  have h1 : Integrable (fun w => u w * D.f w - u w * D.g w) := hiuf.sub hiug
  have h2 : Integrable (fun w => D.f w - D.g w) := D.integrable_f.sub D.integrable_g
  have h3 : Integrable (fun w => k * (D.f w - D.g w)) := h2.const_mul k
  have e1 : ∫ w, (u w - k) * (D.f w - D.g w) =
      (∫ w, (u w * D.f w - u w * D.g w)) - ∫ w, k * (D.f w - D.g w) := by
    rw [← integral_sub h1 h3]
    exact integral_congr_ae (Eventually.of_forall fun w => by simp only; ring)
  have e2 : ∫ w, (u w * D.f w - u w * D.g w) = (∫ w, u w * D.f w) - ∫ w, u w * D.g w :=
    integral_sub hiuf hiug
  have e3 : ∫ w, k * (D.f w - D.g w) = 0 := by
    rw [integral_const_mul, integral_sub D.integrable_f D.integrable_g, D.integral_f,
      D.integral_g, sub_self, mul_zero]
  rw [e1, e2, e3, sub_zero] at hint
  exact sub_nonneg.1 hint

end TwoDensities

/-- **Exercise 8.2.10** (p. 269): if `G ⪯_F F` and `H_α = αF + (1 − α)G`, then `α₁ ≤ α₂` implies
`H_{α₁} ⪯_F H_{α₂}`. -/
theorem exercise_8_2_10 {F G : Measure ℝ} [IsFiniteMeasure F] [IsFiniteMeasure G]
    (h : FOSDle G F) {α₁ α₂ : ℝ} (h0 : 0 ≤ α₁) (h12 : α₁ ≤ α₂) (h1 : α₂ ≤ 1) :
    FOSDle (ENNReal.ofReal α₁ • F + ENNReal.ofReal (1 - α₁) • G)
      (ENNReal.ofReal α₂ • F + ENNReal.ofReal (1 - α₂) • G) := by
  intro u hu hum hub
  obtain ⟨C, hC⟩ := hub
  have hi : ∀ μ : Measure ℝ, IsFiniteMeasure μ → Integrable u μ := fun μ _ =>
    Integrable.of_bound hum.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hmix : ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      ∫ x, u x ∂(ENNReal.ofReal α • F + ENNReal.ofReal (1 - α) • G) =
        α * ∫ x, u x ∂F + (1 - α) * ∫ x, u x ∂G := fun α ha0 ha1 => by
    rw [integral_add_measure ((hi F inferInstance).smul_measure ENNReal.ofReal_ne_top)
      ((hi G inferInstance).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
      integral_smul_measure, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul, smul_eq_mul]
  rw [hmix α₁ h0 (h12.trans h1), hmix α₂ (h0.trans h12) h1]
  have := h u hu hum ⟨C, hC⟩
  nlinarith

/-- The Beta(4, 2) density `20w³(1 − w)` on `(0, 1)` (8.38). -/
def betaF (w : ℝ) : ℝ := 20 * w ^ 3 * (1 - w)

/-- The Beta(2, 4) density `20w(1 − w)³` on `(0, 1)` (8.38). -/
def betaG (w : ℝ) : ℝ := 20 * w * (1 - w) ^ 3

/-- **Exercise 8.2.11** (p. 269): the densities (8.38) have the monotone likelihood ratio
property: `g/f = ((1 − w)/w)²` is decreasing on `(0, 1)`. -/
theorem exercise_8_2_11 : IsMLR betaF betaG 1 := by
  rintro w₁ ⟨h10, h11⟩ w₂ ⟨h20, h21⟩ h12
  have key : (1 - w₂) * w₁ ≤ (1 - w₁) * w₂ := by nlinarith
  have hsq : ((1 - w₂) * w₁) ^ 2 ≤ ((1 - w₁) * w₂) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) h10.le) key 2
  have hpos : 0 ≤ 400 * w₁ * w₂ * (1 - w₁) * (1 - w₂) := by
    have : 0 ≤ 1 - w₁ := by linarith
    have : 0 ≤ 1 - w₂ := by linarith
    positivity
  calc betaG w₂ * betaF w₁ = 400 * w₁ * w₂ * (1 - w₁) * (1 - w₂) * ((1 - w₂) * w₁) ^ 2 := by
        unfold betaF betaG; ring
    _ ≤ 400 * w₁ * w₂ * (1 - w₁) * (1 - w₂) * ((1 - w₁) * w₂) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hpos
    _ = betaG w₁ * betaF w₂ := by unfold betaF betaG; ring

/-! ### Beliefs -/

namespace TwoDensities

variable {M : ℝ} (D : TwoDensities M)

/-- The estimated offer density `φ_π = πf + (1 − π)g`. -/
def φ (π w : ℝ) : ℝ := π * D.f w + (1 - π) * D.g w

/-- Bayes' rule (8.32): `κ(w, π) = πf(w)/(πf(w) + (1 − π)g(w))`. -/
noncomputable def κ (w π : ℝ) : ℝ := π * D.f w / D.φ π w

/-- The updated belief `κ(w, π)`, as a point of `[0, 1]`. -/
noncomputable def pκ (w π : ℝ) : Icc (0 : ℝ) 1 := projIcc 0 1 zero_le_one (D.κ w π)

/-- The offer `w`, as a point of `[0, M]`. -/
noncomputable def pw (w : ℝ) : Icc (0 : ℝ) M := projIcc 0 M D.M_pos.le w

theorem φ_nonneg {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) : 0 ≤ D.φ π w :=
  add_nonneg (mul_nonneg hπ.1 (D.f_nonneg w)) (mul_nonneg (sub_nonneg.2 hπ.2) (D.g_nonneg w))

theorem φ_le {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) : D.φ π w ≤ D.f w + D.g w := by
  unfold φ
  nlinarith [D.f_nonneg w, D.g_nonneg w, hπ.1, hπ.2, mul_nonneg hπ.1 (D.g_nonneg w),
    mul_nonneg (sub_nonneg.2 hπ.2) (D.f_nonneg w)]

theorem φ_pos {w : ℝ} (hw : w ∈ Ioo 0 M) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    0 < D.φ π w := by
  have hf := D.f_pos w hw
  have hg := D.g_pos w hw
  have h1 : 0 ≤ 1 - π := sub_nonneg.2 hπ.2
  unfold φ
  rcases le_total (D.f w) (D.g w) with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h h1]
  · nlinarith [mul_le_mul_of_nonneg_left h hπ.1]

theorem φ_zero {w : ℝ} (hw : w ∉ Ioo 0 M) (π : ℝ) : D.φ π w = 0 := by
  rw [φ, D.f_zero w hw, D.g_zero w hw]
  ring

theorem measurable_φ : Measurable (fun p : ℝ × ℝ => D.φ p.1 p.2) :=
  (measurable_fst.mul (D.measurable_f.comp measurable_snd)).add
    ((measurable_const.sub measurable_fst).mul (D.measurable_g.comp measurable_snd))

theorem measurable_κ : Measurable (fun p : ℝ × ℝ => D.κ p.2 p.1) :=
  (measurable_fst.mul (D.measurable_f.comp measurable_snd)).div D.measurable_φ

theorem measurable_pκ : Measurable (fun p : ℝ × ℝ => D.pκ p.2 p.1) :=
  continuous_projIcc.measurable.comp D.measurable_κ

theorem measurable_pw : Measurable D.pw :=
  (continuous_projIcc (a := (0 : ℝ)) (b := M) (h := D.M_pos.le)).measurable

theorem integrable_φ (π : ℝ) : Integrable (D.φ π) :=
  (D.integrable_f.const_mul π).add (D.integrable_g.const_mul (1 - π))

theorem integral_φ (π : ℝ) : ∫ w, D.φ π w = 1 := by
  unfold φ
  rw [integral_add (D.integrable_f.const_mul π) (D.integrable_g.const_mul (1 - π)),
    integral_const_mul, integral_const_mul, D.integral_f, D.integral_g]
  ring

/-- `∫ u φ_π = π ∫ uf + (1 − π) ∫ ug`. -/
theorem integral_mul_φ {u : ℝ → ℝ} (hum : Measurable u) {C : ℝ} (hC : ∀ w, |u w| ≤ C)
    (π : ℝ) :
    ∫ w, u w * D.φ π w = π * (∫ w, u w * D.f w) + (1 - π) * ∫ w, u w * D.g w := by
  have hf := integrable_mul hum hC D.integrable_f
  have hg := integrable_mul hum hC D.integrable_g
  have e : (fun w => u w * D.φ π w) = fun w => π * (u w * D.f w) + (1 - π) * (u w * D.g w) :=
    funext fun w => by simp only [φ]; ring
  rw [e, integral_add (hf.const_mul π) (hg.const_mul (1 - π)), integral_const_mul,
    integral_const_mul]

/-- Integration against `φ_π` is an average: `|∫ u φ_π| ≤ C` when `|u| ≤ C`. -/
theorem abs_integral_mul_φ_le {u : ℝ → ℝ} {C : ℝ} (hC : ∀ w, |u w| ≤ C) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) : |∫ w, u w * D.φ π w| ≤ C := by
  have h := norm_integral_le_of_norm_le (f := fun w => u w * D.φ π w)
    ((D.integrable_φ π).const_mul C) (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (D.φ_nonneg hπ w)]
      exact mul_le_mul_of_nonneg_right (hC w) (D.φ_nonneg hπ w))
  rwa [integral_const_mul, D.integral_φ, mul_one, Real.norm_eq_abs] at h

theorem κ_mem {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) : D.κ w π ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (mul_nonneg hπ.1 (D.f_nonneg w)) (D.φ_nonneg hπ w), ?_⟩
  refine div_le_one_of_le₀ ?_ (D.φ_nonneg hπ w)
  unfold φ
  linarith [mul_nonneg (sub_nonneg.2 hπ.2) (D.g_nonneg w)]

/-- The posterior `κ(w, π)` is increasing in the prior `π`. -/
theorem κ_mono_prior (w : ℝ) {π₁ π₂ : ℝ} (h1 : π₁ ∈ Set.Icc (0 : ℝ) 1)
    (h2 : π₂ ∈ Set.Icc (0 : ℝ) 1) (h12 : π₁ ≤ π₂) : D.κ w π₁ ≤ D.κ w π₂ := by
  by_cases hw : w ∈ Ioo 0 M
  · rw [κ, κ, div_le_div_iff₀ (D.φ_pos hw h1) (D.φ_pos hw h2), φ, φ]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h12) (D.f_nonneg w)) (D.g_nonneg w)]
  · rw [κ, κ, D.φ_zero hw, D.φ_zero hw, div_zero, div_zero]

/-- Under the monotone likelihood ratio property the posterior `κ(w, π)` is increasing in the
offer `w`. -/
theorem κ_mono_offer (hmlr : IsMLR D.f D.g M) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1)
    {w₁ w₂ : ℝ} (hw₁ : w₁ ∈ Ioo 0 M) (hw₂ : w₂ ∈ Ioo 0 M) (h12 : w₁ ≤ w₂) :
    D.κ w₁ π ≤ D.κ w₂ π := by
  rw [κ, κ, div_le_div_iff₀ (D.φ_pos hw₁ hπ) (D.φ_pos hw₂ hπ), φ, φ]
  have h := hmlr w₁ hw₁ w₂ hw₂ h12
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hπ.1 (sub_nonneg.2 hπ.2))]

theorem continuous_κ (w : ℝ) : Continuous fun π : Set.Icc (0 : ℝ) 1 => D.κ w π := by
  by_cases hw : w ∈ Ioo 0 M
  · change Continuous fun π : Set.Icc (0 : ℝ) 1 =>
      (π : ℝ) * D.f w / ((π : ℝ) * D.f w + (1 - (π : ℝ)) * D.g w)
    exact (continuous_subtype_val.mul continuous_const).div
      ((continuous_subtype_val.mul continuous_const).add
        ((continuous_const.sub continuous_subtype_val).mul continuous_const))
      fun π => (D.φ_pos hw π.2).ne'
  · have : (fun π : Set.Icc (0 : ℝ) 1 => D.κ w π) = fun _ => 0 :=
      funext fun π => by rw [κ, D.φ_zero hw, div_zero]
    rw [this]
    exact continuous_const

end TwoDensities

/-! ### The learning model -/

/-- The job search model with learning (§8.2.3.1). -/
structure LearningSearch (M : ℝ) where
  /-- the two candidate offer densities -/
  D : TwoDensities M
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

/-- The state space `[0, M] × [0, 1]` of offers and beliefs. -/
abbrev LState (M : ℝ) := Set.Icc (0 : ℝ) M × Set.Icc (0 : ℝ) 1

namespace LearningSearch

variable {M : ℝ} (L : LearningSearch M)

theorem one_sub_β_pos : 0 < 1 - L.β := sub_pos.2 L.β_lt_one

/-- The continuation value `c + β ∫ v(w', κ(w', π)) φ_π(w') dw'`. -/
noncomputable def contR (v : BM (LState M)) (π : ℝ) : ℝ :=
  L.c + L.β * ∫ w, v.toFun (L.D.pw w, L.D.pκ w π) * L.D.φ π w

theorem measurable_integrand (v : BM (LState M)) :
    Measurable (fun p : ℝ × ℝ => v.toFun (L.D.pw p.2, L.D.pκ p.2 p.1) * L.D.φ p.1 p.2) :=
  (v.measurable'.comp ((L.D.measurable_pw.comp measurable_snd).prodMk L.D.measurable_pκ)).mul
    L.D.measurable_φ

theorem measurable_section (v : BM (LState M)) (π : ℝ) :
    Measurable (fun w => v.toFun (L.D.pw w, L.D.pκ w π)) :=
  v.measurable'.comp (L.D.measurable_pw.prodMk
    (L.D.measurable_pκ.comp (measurable_const.prodMk measurable_id)))

theorem integrable_section (v : BM (LState M)) (π : ℝ) :
    Integrable (fun w => v.toFun (L.D.pw w, L.D.pκ w π) * L.D.φ π w) :=
  TwoDensities.integrable_mul (L.measurable_section v π) (fun _ => BM.abs_le_norm v _)
    (L.D.integrable_φ π)

theorem measurable_contR (v : BM (LState M)) : Measurable (L.contR v) :=
  measurable_const.add (measurable_const.mul
    (L.measurable_integrand v).stronglyMeasurable.integral_prod_right'.measurable)

theorem abs_contR_le (v : BM (LState M)) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    |L.contR v π| ≤ |L.c| + L.β * ‖v‖ := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_pos L.β_pos]
  exact mul_le_mul_of_nonneg_left
    (L.D.abs_integral_mul_φ_le (fun _ => BM.abs_le_norm v _) hπ) L.β_pos.le

theorem abs_contR_sub_le (v w : BM (LState M)) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    |L.contR v π - L.contR w π| ≤ L.β * ‖v - w‖ := by
  have h : L.contR v π - L.contR w π =
      L.β * ∫ x, (v - w).toFun (L.D.pw x, L.D.pκ x π) * L.D.φ π x := by
    rw [contR, contR, add_sub_add_left_eq_sub, ← mul_sub,
      ← integral_sub (L.integrable_section v π) (L.integrable_section w π)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [BM.sub_apply]; ring)
  rw [h, abs_mul, abs_of_pos L.β_pos]
  exact mul_le_mul_of_nonneg_left
    (L.D.abs_integral_mul_φ_le (fun _ => BM.abs_le_norm (v - w) _) hπ) L.β_pos.le

theorem measurable_stop : Measurable (fun x : LState M => (x.1 : ℝ) / (1 - L.β)) :=
  (measurable_subtype_coe.comp measurable_fst).div_const _

theorem measurable_cont (v : BM (LState M)) : Measurable (fun x : LState M => L.contR v x.2) :=
  (L.measurable_contR v).comp (measurable_subtype_coe.comp measurable_snd)

/-- The policy operator `T_σ v = σ w/(1 − β) + (1 − σ)[c + β ∫ v(w', κ(w', π)) φ_π(w') dw']`. -/
noncomputable def T (σ : StopPolicy (LState M)) (v : BM (LState M)) : BM (LState M) :=
  ⟨fun x => if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2,
    Measurable.ite (σ.2 (measurableSet_singleton true)) L.measurable_stop (L.measurable_cont v), by
    refine ⟨M / (1 - L.β) + (|L.c| + L.β * ‖v‖), fun x => ?_⟩
    have h1 := L.one_sub_β_pos
    have hs : |(x.1 : ℝ) / (1 - L.β)| ≤ M / (1 - L.β) := by
      rw [abs_div, abs_of_pos h1, abs_of_nonneg x.1.2.1]
      exact div_le_div_of_nonneg_right x.1.2.2 h1.le
    have hc := L.abs_contR_le v x.2.2
    have hM : 0 ≤ M / (1 - L.β) := div_nonneg L.D.M_pos.le h1.le
    have hcn : 0 ≤ |L.c| + L.β * ‖v‖ :=
      add_nonneg (abs_nonneg _) (mul_nonneg L.β_pos.le (norm_nonneg _))
    split_ifs
    · linarith
    · linarith⟩

/-- The ADP `(V, 𝕋)` of §8.2.3.1, on `V = b([0, M] × [0, 1])`. -/
noncomputable def adp : ADP (BM (LState M)) (StopPolicy (LState M)) where
  T := L.T
  mono σ v w hvw := BM.le_def.2 fun x => by
    have hc : L.contR v x.2 ≤ L.contR w x.2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono (L.integrable_section v _)
        (L.integrable_section w _) fun y => mul_le_mul_of_nonneg_right (BM.le_def.1 hvw _)
          (L.D.φ_nonneg x.2.2 y)) L.β_pos.le)
    change (if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2) ≤
      (if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR w x.2)
    split_ifs
    · exact le_rfl
    · exact hc
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The policy of Exercise 8.2.6: accept when `w/(1 − β) ≥ c + β ∫ v(w', κ(w', π)) φ_π(w') dw'`. -/
noncomputable def accept (v : BM (LState M)) : StopPolicy (LState M) :=
  acceptWhere L.measurable_stop (L.measurable_cont v)

theorem accept_isGreedy (v : BM (LState M)) :
    L.adp.IsGreedy v (L.accept v) ∧
      ∀ x, (L.adp.bellman v).toFun x = max ((x.1 : ℝ) / (1 - L.β)) (L.contR v x.2) := by
  have hval : ∀ x, (L.adp.T (L.accept v) v).toFun x =
      max ((x.1 : ℝ) / (1 - L.β)) (L.contR v x.2) := fun x => acceptWhere_apply _ _ x
  have hg : L.adp.IsGreedy v (L.accept v) := fun τ => BM.le_def.2 fun x => by
    rw [hval]
    change (if τ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2) ≤ _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq : L.adp.bellman v = L.adp.T (L.accept v) v :=
    le_antisymm (hg _) (L.adp.isGreedy_greedy ⟨_, hg⟩ _)
  exact ⟨hg, fun x => by rw [heq, hval]⟩

/-- **Exercise 8.2.6** (p. 266): the policy `σ = 𝟙{w/(1 − β) ≥ c + β ∫ v(w', κ(w', π)) φ_π}` is
`v`-greedy. -/
theorem exercise_8_2_6 (v : BM (LState M)) : L.adp.IsGreedy v (L.accept v) :=
  (L.accept_isGreedy v).1

/-- **Exercise 8.2.7** (p. 266): the Bellman operator is (8.33),
`(Tv)(w, π) = max{w/(1 − β), c + β ∫ v(w', κ(w', π)) φ_π(w') dw'}`. -/
theorem exercise_8_2_7 (v : BM (LState M)) (x : LState M) :
    (L.adp.bellman v).toFun x = max ((x.1 : ℝ) / (1 - L.β)) (L.contR v x.2) :=
  (L.accept_isGreedy v).2 x

theorem regular : L.adp.Regular := fun v => ⟨_, L.exercise_8_2_6 v⟩

theorem T_contraction (σ : StopPolicy (LState M)) (v w : BM (LState M)) :
    dist (L.adp.T σ v) (L.adp.T σ w) ≤ L.β * dist v w := by
  rw [dist_eq_norm, dist_eq_norm]
  refine BM.norm_le (mul_nonneg L.β_pos.le (norm_nonneg _)) fun x => ?_
  change |(if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2) -
    (if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR w x.2)| ≤ _
  split_ifs
  · rw [sub_self, abs_zero]
    exact mul_nonneg L.β_pos.le (norm_nonneg _)
  · exact L.abs_contR_sub_le v w x.2.2

/-- The learning ADP is well-posed, the fundamental optimality properties hold, and VFI, OPI and
HPI converge: each `T_σ` is a contraction of modulus `β` (Theorem 3.1.5). -/
theorem optimality :
    ∃ hw : L.adp.WellPosed, L.adp.FundamentalOptimality hw ∧ ∃ vstar,
      L.adp.VFIGeometric univ vstar ∧
        ∀ g, L.adp.IsSelector g → L.adp.OPIConverges g vstar ∧ L.adp.HPIConverges hw g vstar := by
  obtain ⟨hFO, vstar, -, hgeo, hconv⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive L.β_pos.le
    L.β_lt_one L.T_contraction (V₀ := univ)
    ⟨isClosed_univ, fun v _ => L.regular v, mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨_, hFO, vstar, hgeo, hconv L.regular⟩

/-! ### The reservation wage operator -/

/-- The integrand `max{w', ω[κ(w', π)]}` of (8.36), with the offer read in `[0, M]` (this changes
nothing where `φ_π > 0`; see `That_eq`). -/
noncomputable def G (ω : BM (Set.Icc (0 : ℝ) 1)) (π w : ℝ) : ℝ :=
  max (L.D.pw w : ℝ) (ω.toFun (L.D.pκ w π))

theorem measurable_Gφ (ω : BM (Set.Icc (0 : ℝ) 1)) :
    Measurable (fun p : ℝ × ℝ => L.G ω p.1 p.2 * L.D.φ p.1 p.2) :=
  ((measurable_subtype_coe.comp (L.D.measurable_pw.comp measurable_snd)).max
    (ω.measurable'.comp L.D.measurable_pκ)).mul L.D.measurable_φ

theorem measurable_G (ω : BM (Set.Icc (0 : ℝ) 1)) (π : ℝ) : Measurable (L.G ω π) :=
  (measurable_subtype_coe.comp L.D.measurable_pw).max
    (ω.measurable'.comp (L.D.measurable_pκ.comp (measurable_const.prodMk measurable_id)))

theorem abs_G_le (ω : BM (Set.Icc (0 : ℝ) 1)) (π w : ℝ) : |L.G ω π w| ≤ M + ‖ω‖ := by
  have hw := (L.D.pw w).2
  refine (abs_max_le_max_abs_abs).trans (max_le ?_ ?_)
  · rw [abs_of_nonneg hw.1]
    linarith [norm_nonneg ω, hw.2]
  · linarith [BM.abs_le_norm ω (L.D.pκ w π), L.D.M_pos]

theorem integrable_Gφ (ω : BM (Set.Icc (0 : ℝ) 1)) (π : ℝ) :
    Integrable (fun w => L.G ω π w * L.D.φ π w) :=
  TwoDensities.integrable_mul (L.measurable_G ω π) (L.abs_G_le ω π) (L.D.integrable_φ π)

/-- The reservation wage operator (8.36),
`(T̂ω)(π) = (1 − β)c + β ∫ max{w', ω[κ(w', π)]} φ_π(w') dw'`, on `V̂ = b[0, 1]`. -/
noncomputable def That (ω : BM (Set.Icc (0 : ℝ) 1)) : BM (Set.Icc (0 : ℝ) 1) :=
  ⟨fun π => (1 - L.β) * L.c + L.β * ∫ w, L.G ω π w * L.D.φ π w,
    measurable_const.add (measurable_const.mul
      ((L.measurable_Gφ ω).stronglyMeasurable.integral_prod_right'.measurable.comp
        measurable_subtype_coe)), by
    refine ⟨|(1 - L.β) * L.c| + L.β * (M + ‖ω‖), fun π => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_pos L.β_pos]
    exact mul_le_mul_of_nonneg_left (L.D.abs_integral_mul_φ_le (L.abs_G_le ω π) π.2)
      L.β_pos.le⟩

theorem That_apply (ω : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    (L.That ω).toFun π = (1 - L.β) * L.c + L.β * ∫ w, L.G ω π w * L.D.φ π w := rfl

/-- `T̂` is (8.36) as written: offers outside `(0, M)` carry no weight. -/
theorem That_eq (ω : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    (L.That ω).toFun π =
      (1 - L.β) * L.c + L.β * ∫ w, max w (ω.toFun (L.D.pκ w π)) * L.D.φ π w := by
  rw [That_apply]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ Ioo 0 M
  · have : (L.D.pw w : ℝ) = w :=
      congrArg Subtype.val (projIcc_of_mem L.D.M_pos.le (Ioo_subset_Icc_self hw))
    simp only [G, this]
  · simp only [L.D.φ_zero hw, mul_zero]

theorem abs_That_sub_le (ω ω' : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    |(L.That ω).toFun π - (L.That ω').toFun π| ≤ L.β * dist ω ω' := by
  have h : (L.That ω).toFun π - (L.That ω').toFun π =
      L.β * ∫ w, (L.G ω π w - L.G ω' π w) * L.D.φ π w := by
    rw [That_apply, That_apply, add_sub_add_left_eq_sub, ← mul_sub,
      ← integral_sub (L.integrable_Gφ ω π) (L.integrable_Gφ ω' π)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun w => by simp only; ring)
  have hG : ∀ w, |L.G ω π w - L.G ω' π w| ≤ dist ω ω' := fun w => by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (BM.abs_sub_le_dist _ _ _))
    rw [sub_self, abs_zero]
    exact dist_nonneg
  rw [h, abs_mul, abs_of_pos L.β_pos]
  exact mul_le_mul_of_nonneg_left (L.D.abs_integral_mul_φ_le hG π.2) L.β_pos.le

/-- **Exercise 8.2.8** (p. 267): `T̂` is a contraction of modulus `β` on `V̂ = b[0, 1]`. -/
theorem exercise_8_2_8 :
    (∀ ω ω', dist (L.That ω) (L.That ω') ≤ L.β * dist ω ω') ∧
      ContractingWith ⟨L.β, L.β_pos.le⟩ L.That := by
  have h : ∀ ω ω', dist (L.That ω) (L.That ω') ≤ L.β * dist ω ω' := fun ω ω' =>
    BM.dist_le (mul_nonneg L.β_pos.le dist_nonneg) (L.abs_That_sub_le ω ω')
  exact ⟨h, L.β_lt_one, LipschitzWith.of_dist_le_mul h⟩

theorem That_contracting : ContractingWith ⟨L.β, L.β_pos.le⟩ L.That := L.exercise_8_2_8.2

/-- **Exercise 8.2.9** (p. 267): `T̂` maps `bc[0, 1]` into itself. -/
theorem exercise_8_2_9 {ω : BM (Set.Icc (0 : ℝ) 1)} (hω : Continuous ω.toFun) :
    Continuous (L.That ω).toFun := by
  refine continuous_const.add (continuous_const.mul (continuous_of_dominated
    (F := fun (π : Set.Icc (0 : ℝ) 1) w => L.G ω π w * L.D.φ π w)
    (bound := fun w => (M + ‖ω‖) * (L.D.f w + L.D.g w))
    (fun π => (L.integrable_Gφ ω π).aestronglyMeasurable)
    (fun π => Eventually.of_forall fun w => ?_)
    ((L.D.integrable_f.add L.D.integrable_g).const_mul _)
    (Eventually.of_forall fun w => ?_)))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.D.φ_nonneg π.2 w)]
    exact mul_le_mul (L.abs_G_le ω π w) (L.D.φ_le π.2 w) (L.D.φ_nonneg π.2 w)
      (add_nonneg L.D.M_pos.le (norm_nonneg ω))
  · exact (continuous_const.max (hω.comp (continuous_projIcc.comp (L.D.continuous_κ w)))).mul
      ((continuous_subtype_val.mul continuous_const).add
        ((continuous_const.sub continuous_subtype_val).mul continuous_const))

/-- The optimal reservation wage function `ω*`, the fixed point of `T̂`. -/
noncomputable def ωstar : BM (Set.Icc (0 : ℝ) 1) :=
  ContractingWith.fixedPoint L.That L.That_contracting

theorem That_ωstar : L.That L.ωstar = L.ωstar :=
  ContractingWith.fixedPoint_isFixedPt L.That_contracting

theorem tendstoUniformly_ωstar :
    TendstoUniformly (fun n => (L.That^[n] (BM.const 0)).toFun) L.ωstar.toFun atTop :=
  BM.tendstoUniformly_of_tendsto
    (ContractingWith.tendsto_iterate_fixedPoint L.That_contracting (BM.const 0))

/-- `ω*` is continuous: `T̂` preserves `bc[0, 1]` and uniform limits of continuous functions are
continuous. -/
theorem continuous_ωstar : Continuous L.ωstar.toFun := by
  have hit : ∀ n, Continuous (L.That^[n] (BM.const 0)).toFun := by
    intro n
    induction n with
    | zero => exact continuous_const
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact L.exercise_8_2_9 ih
  exact L.tendstoUniformly_ωstar.continuous (Eventually.of_forall hit).frequently

/-- The value `v_ω(w, π) = max{w, ω(π)}/(1 − β)` of a reservation wage function `ω`. -/
noncomputable def vOf (ω : BM (Set.Icc (0 : ℝ) 1)) : BM (LState M) :=
  ⟨fun x => max (x.1 : ℝ) (ω.toFun x.2) / (1 - L.β),
    ((measurable_subtype_coe.comp measurable_fst).max
      (ω.measurable'.comp measurable_snd)).div_const _,
    ⟨(M + ‖ω‖) / (1 - L.β), fun x => by
      have h1 := L.one_sub_β_pos
      rw [abs_div, abs_of_pos h1]
      refine div_le_div_of_nonneg_right ((abs_max_le_max_abs_abs).trans (max_le ?_ ?_)) h1.le
      · rw [abs_of_nonneg x.1.2.1]
        linarith [norm_nonneg ω, x.1.2.2]
      · linarith [BM.abs_le_norm ω x.2, L.D.M_pos]⟩⟩

/-- (8.34)–(8.35): the continuation value of `v_ω` is `(T̂ω)(π)/(1 − β)`. -/
theorem contR_vOf (ω : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    L.contR (L.vOf ω) π = (L.That ω).toFun π / (1 - L.β) := by
  have h1 := L.one_sub_β_pos
  have e : ∫ w, (L.vOf ω).toFun (L.D.pw w, L.D.pκ w π) * L.D.φ π w =
      (∫ w, L.G ω π w * L.D.φ π w) / (1 - L.β) := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun w => by
      simp only [vOf, G]
      ring)
  rw [contR, e, That_apply]
  field_simp

theorem abs_bellman_sub_le (v w : BM (LState M)) (x : LState M) :
    |(L.adp.bellman v).toFun x - (L.adp.bellman w).toFun x| ≤ L.β * dist v w := by
  rw [L.exercise_8_2_7, L.exercise_8_2_7, dist_eq_norm]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (L.abs_contR_sub_le v w x.2.2))
  rw [sub_self, abs_zero]
  exact mul_nonneg L.β_pos.le (norm_nonneg _)

theorem bellman_contracting : ContractingWith ⟨L.β, L.β_pos.le⟩ L.adp.bellman :=
  ⟨L.β_lt_one, LipschitzWith.of_dist_le_mul fun v w =>
    BM.dist_le (mul_nonneg L.β_pos.le dist_nonneg) (L.abs_bellman_sub_le v w)⟩

/-- §8.2.3.2: the Bellman equation (8.33) has exactly one solution in `V`, namely
`v*(w, π) = max{w, ω*(π)}/(1 − β)`, so `ω*` is the reservation wage of the optimal policy
(8.34): the worker accepts exactly when `w ≥ ω*(π)`. -/
theorem bellman_eq_iff (v : BM (LState M)) :
    L.adp.bellman v = v ↔ v = L.vOf L.ωstar := by
  have hfix : L.adp.bellman (L.vOf L.ωstar) = L.vOf L.ωstar := BM.ext fun x => by
    rw [L.exercise_8_2_7, L.contR_vOf, L.That_ωstar]
    exact max_div_div_right L.one_sub_β_pos.le _ _
  constructor
  · intro h
    exact (L.bellman_contracting.fixedPoint_unique' h hfix)
  · rintro rfl
    exact hfix

/-! ### Parametric monotonicity -/

/-- Under the monotone likelihood ratio property, `T̂` maps increasing functions to increasing
functions (the proof of Proposition 8.2.1). -/
theorem That_monotone (hmlr : IsMLR L.D.f L.D.g M) {ω : BM (Set.Icc (0 : ℝ) 1)}
    (hω : Monotone ω.toFun) : Monotone (L.That ω).toFun := by
  intro π₁ π₂ h12
  have h12' : (π₁ : ℝ) ≤ π₂ := h12
  rw [That_apply, That_apply]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ L.β_pos.le)
  -- `h(w', π) = ω[κ(w', π)]` is increasing in `π`
  have step1 : ∫ w, L.G ω π₁ w * L.D.φ π₁ w ≤ ∫ w, L.G ω π₂ w * L.D.φ π₁ w :=
    integral_mono (L.integrable_Gφ ω π₁)
      (TwoDensities.integrable_mul (L.measurable_G ω π₂) (L.abs_G_le ω π₂)
        (L.D.integrable_φ π₁)) fun w =>
      mul_le_mul_of_nonneg_right (max_le_max le_rfl (hω (monotone_projIcc zero_le_one
        (L.D.κ_mono_prior w π₁.2 π₂.2 h12'))))
        (L.D.φ_nonneg π₁.2 w)
  -- `w' ↦ max{w', h(w', π₂)}` is increasing on `(0, M)`, and `π ↦ φ_π` is `⪯_F`-isotone
  have hmono : MonotoneOn (L.G ω π₂) (Ioo 0 M) := fun w₁ hw₁ w₂ hw₂ hw12 =>
    max_le_max (monotone_projIcc L.D.M_pos.le hw12)
      (hω (monotone_projIcc zero_le_one (L.D.κ_mono_offer hmlr π₂.2 hw₁ hw₂ hw12)))
  have hA := L.D.proposition_A_5_34 hmlr (L.measurable_G ω π₂) (L.abs_G_le ω π₂) hmono
  have step2 : ∫ w, L.G ω π₂ w * L.D.φ π₁ w ≤ ∫ w, L.G ω π₂ w * L.D.φ π₂ w := by
    rw [L.D.integral_mul_φ (L.measurable_G ω π₂) (L.abs_G_le ω π₂),
      L.D.integral_mul_φ (L.measurable_G ω π₂) (L.abs_G_le ω π₂)]
    nlinarith [mul_nonneg (sub_nonneg.2 h12') (sub_nonneg.2 hA)]
  exact step1.trans step2

/-- **Proposition 8.2.1** (p. 269): if `f` and `g` have the monotone likelihood ratio property,
then the optimal reservation wage `ω*` is increasing in `π`. -/
theorem proposition_8_2_1 (hmlr : IsMLR L.D.f L.D.g M) : Monotone L.ωstar.toFun := by
  have hit : ∀ n, Monotone (L.That^[n] (BM.const 0)).toFun := by
    intro n
    induction n with
    | zero => exact fun _ _ _ => le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact L.That_monotone hmlr ih
  intro π₁ π₂ h12
  exact le_of_tendsto_of_tendsto' (L.tendstoUniformly_ωstar.tendsto_at π₁)
    (L.tendstoUniformly_ωstar.tendsto_at π₂) fun n => hit n h12

end LearningSearch

end SargentStachurski.AdditionalApplications
