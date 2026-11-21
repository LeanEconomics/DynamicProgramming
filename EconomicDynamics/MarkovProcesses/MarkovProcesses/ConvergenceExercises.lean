/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ConvergenceStrong
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Formulas for the total variation distance (Exercise 3.5 and (3.7))

Miao, (3.7), p. 105, and Exercise 3.5, p. 114, with the book's normalisation
`dTV(λ₁, λ₂) = sup_A |λ₁(A) − λ₂(A)|` (3.6). With this normalisation all three formulas hold as
printed; SLP's norm `‖λ₁ − λ₂‖` is `2 dTV` (`gp_tvDist_eq_two_mul_dTV`), which is where a factor
of `2` would otherwise appear.

* **Exercise 3.5(b)** (`ex_3_5b`): if `λ₁, λ₂` have densities `g, h` with respect to `ρ`, then
  `dTV(λ₁, λ₂) = 1 − ∫ min(g, h) dρ = ½ ∫ |g − h| dρ = ∫ (g − h)⁺ dρ`, the supremum being
  attained at `A = {g > h}`.
* **(3.7)** (`eq_3_7`): the same with `ρ = ν = λ₁ + λ₂` and the Radon–Nikodym derivatives
  `dλᵢ/dν`.
* **Exercise 3.5(a)** (`ex_3_5a`): for `a < b`,
  `dTV(λ₁, λ₂) = (b − a)⁻¹ sup_{f : X → [a, b]} |∫ f dλ₁ − ∫ f dλ₂|`, the supremum over
  measurable `f`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A measure with a nonnegative integrable density: `λ(A) = ∫_A g dρ`. -/
theorem gp_withDensity_real {ρ : Measure X} {g : X → ℝ} (hg0 : 0 ≤ g) (hgi : Integrable g ρ)
    {A : Set X} (hA : MeasurableSet A) :
    (ρ.withDensity fun x => ENNReal.ofReal (g x)).real A = ∫ x in A, g x ∂ρ := by
  rw [measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (ae_of_all _ fun x => hg0 x),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => hg0 x)]

/-- The density of a probability measure is integrable. -/
theorem gp_integrable_density {ρ : Measure X} {lam : Measure X} [IsProbabilityMeasure lam]
    {g : X → ℝ} (hgm : Measurable g) (hg0 : 0 ≤ g)
    (hl : lam = ρ.withDensity fun x => ENNReal.ofReal (g x)) : Integrable g ρ := by
  refine ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 ?_⟩
  have := measure_univ (μ := lam)
  rw [hl, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  rw [this]
  exact ENNReal.one_lt_top

/-- **Exercise 3.5(b)** (Miao, p. 114). If `λ₁` and `λ₂` have densities `g` and `h` with respect
to `ρ`, then `dTV(λ₁, λ₂) = 1 − ∫ min(g, h) dρ`; moreover `dTV(λ₁, λ₂) = ½ ∫ |g − h| dρ` and
the supremum in (3.6) is attained at `A = {g > h}`. -/
theorem ex_3_5b {ρ : Measure X} (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] {g h : X → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (h1 : lam₁ = ρ.withDensity fun x => ENNReal.ofReal (g x))
    (h2 : lam₂ = ρ.withDensity fun x => ENNReal.ofReal (h x)) :
    dTV lam₁ lam₂ = 1 - ∫ x, min (g x) (h x) ∂ρ ∧
      dTV lam₁ lam₂ = 1 / 2 * ∫ x, |g x - h x| ∂ρ ∧
      dTV lam₁ lam₂ = lam₁.real {x | h x < g x} - lam₂.real {x | h x < g x} := by
  have hgi := gp_integrable_density hgm hg0 h1
  have hhi := gp_integrable_density hhm hh0 h2
  have hr1 : ∀ A, MeasurableSet A → lam₁.real A = ∫ x in A, g x ∂ρ := fun A hA => by
    rw [h1]; exact gp_withDensity_real hg0 hgi hA
  have hr2 : ∀ A, MeasurableSet A → lam₂.real A = ∫ x in A, h x ∂ρ := fun A hA => by
    rw [h2]; exact gp_withDensity_real hh0 hhi hA
  have hg1 : ∫ x, g x ∂ρ = 1 := by
    have := hr1 Set.univ MeasurableSet.univ
    rwa [probReal_univ, Measure.restrict_univ, eq_comm] at this
  have hh1 : ∫ x, h x ∂ρ = 1 := by
    have := hr2 Set.univ MeasurableSet.univ
    rwa [probReal_univ, Measure.restrict_univ, eq_comm] at this
  set D := ∫ x, max (g x - h x) 0 ∂ρ
  set D' := ∫ x, max (h x - g x) 0 ∂ρ
  have hgh : Integrable (fun x => g x - h x) ρ := hgi.sub hhi
  have hhg : Integrable (fun x => h x - g x) ρ := hhi.sub hgi
  have hpi : Integrable (fun x => max (g x - h x) 0) ρ := hgh.sup (integrable_zero _ _ _)
  have hpi' : Integrable (fun x => max (h x - g x) 0) ρ := hhg.sup (integrable_zero _ _ _)
  have hDD : D = D' := by
    have : ∫ x, (max (g x - h x) 0 - max (h x - g x) 0) ∂ρ = 0 := by
      have e : (fun x => max (g x - h x) 0 - max (h x - g x) 0) = fun x => g x - h x :=
        funext fun x => by
          rcases le_total (g x) (h x) with hx | hx
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      rw [e, integral_sub hgi hhi, hg1, hh1, sub_self]
    rw [integral_sub hpi hpi'] at this
    linarith
  have hB : MeasurableSet {x | h x < g x} := measurableSet_lt hhm hgm
  have hDB : D = ∫ x in {x | h x < g x}, (g x - h x) ∂ρ := by
    rw [← integral_indicator hB]
    change ∫ x, max (g x - h x) 0 ∂ρ = _
    congr 1
    funext x
    by_cases hx : h x < g x
    · rw [Set.indicator_of_mem (show x ∈ {x | h x < g x} from hx), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show x ∉ {x | h x < g x} from hx),
        max_eq_right (by push Not at hx; linarith)]
  have hdiff : ∀ A, MeasurableSet A →
      lam₁.real A - lam₂.real A = ∫ x in A, (g x - h x) ∂ρ := fun A hA => by
    rw [hr1 A hA, hr2 A hA, integral_sub hgi.integrableOn hhi.integrableOn]
  have hbound : ∀ A, MeasurableSet A → |lam₁.real A - lam₂.real A| ≤ D := by
    intro A hA
    rw [hdiff A hA, abs_le]
    constructor
    · have : ∫ x in A, (h x - g x) ∂ρ ≤ D' :=
        (setIntegral_mono hhg.integrableOn hpi'.integrableOn fun x => le_max_left _ _).trans
          (setIntegral_le_integral hpi' (ae_of_all _ fun x => le_max_right _ _))
      have e : ∫ x in A, (h x - g x) ∂ρ = -∫ x in A, (g x - h x) ∂ρ := by
        rw [← integral_neg]; congr 1; funext x; ring
      linarith
    · exact (setIntegral_mono hgh.integrableOn hpi.integrableOn fun x => le_max_left _ _).trans
        (setIntegral_le_integral hpi (ae_of_all _ fun x => le_max_right _ _))
  have hdTV : dTV lam₁ lam₂ = D := by
    refine le_antisymm (gp_dTV_le_of_forall _ _ hbound) ?_
    have := gp_abs_le_dTV lam₁ lam₂ hB
    rw [hdiff _ hB, ← hDB] at this
    exact (le_abs_self D).trans this
  refine ⟨?_, ?_, ?_⟩
  · rw [hdTV]
    have e : (fun x => max (g x - h x) 0) = fun x => g x - min (g x) (h x) := funext fun x => by
      rcases le_total (g x) (h x) with hx | hx
      · rw [max_eq_right (by linarith), min_eq_left hx]; ring
      · rw [max_eq_left (by linarith), min_eq_right hx]
    have hmi : Integrable (fun x => min (g x) (h x)) ρ := hgi.inf hhi
    change ∫ x, max (g x - h x) 0 ∂ρ = _
    rw [e, integral_sub hgi hmi, hg1]
  · rw [hdTV]
    have e : (fun x => |g x - h x|) = fun x => max (g x - h x) 0 + max (h x - g x) 0 :=
      funext fun x => by
        rcases le_total (g x) (h x) with hx | hx
        · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
          ring
        · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
          ring
    rw [e, integral_add hpi hpi']
    change D = 1 / 2 * (D + D')
    rw [← hDD]
    ring
  · rw [hdTV, hdiff _ hB, hDB]

/-- **(3.7)** (Miao, p. 105). With `ν = λ₁ + λ₂` and the Radon–Nikodym derivatives
`dλᵢ/dν`, `dTV(λ₁, λ₂) = ½ ∫ |dλ₁/dν − dλ₂/dν| dν = 1 − ∫ min(dλ₁/dν, dλ₂/dν) dν`. -/
theorem eq_3_7 (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁] [IsProbabilityMeasure lam₂] :
    dTV lam₁ lam₂ = 1 / 2 * ∫ x, |(lam₁.rnDeriv (lam₁ + lam₂) x).toReal -
        (lam₂.rnDeriv (lam₁ + lam₂) x).toReal| ∂(lam₁ + lam₂) ∧
      dTV lam₁ lam₂ = 1 - ∫ x, min (lam₁.rnDeriv (lam₁ + lam₂) x).toReal
        (lam₂.rnDeriv (lam₁ + lam₂) x).toReal ∂(lam₁ + lam₂) := by
  set ν := lam₁ + lam₂
  have hdens : ∀ (lam : Measure X) [IsProbabilityMeasure lam], lam ≤ ν →
      lam = ν.withDensity fun x => ENNReal.ofReal (lam.rnDeriv ν x).toReal := by
    intro lam _ hle
    have hac : lam ≪ ν := Measure.absolutelyContinuous_of_le hle
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq lam ν hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top lam ν] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  have e1 := hdens lam₁ (Measure.le_add_right le_rfl)
  have e2 := hdens lam₂ (Measure.le_add_left le_rfl)
  obtain ⟨hmin, habs, -⟩ := ex_3_5b lam₁ lam₂ (Measure.measurable_rnDeriv _ _).ennreal_toReal
    (Measure.measurable_rnDeriv _ _).ennreal_toReal (fun x => ENNReal.toReal_nonneg)
    (fun x => ENNReal.toReal_nonneg) e1 e2
  exact ⟨habs, hmin⟩

/-- **Exercise 3.5(a)** (Miao, p. 114). For `a < b`,
`dTV(λ₁, λ₂) = (b − a)⁻¹ sup_{f : X → [a, b]} |∫ f dλ₁ − ∫ f dλ₂|`, the supremum taken over
measurable `f`. -/
theorem ex_3_5a (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁] [IsProbabilityMeasure lam₂]
    {a b : ℝ} (hab : a < b) :
    dTV lam₁ lam₂ = (b - a)⁻¹ * sSup {r | ∃ f : X → ℝ, Measurable f ∧
      (∀ x, f x ∈ Set.Icc a b) ∧ r = |∫ x, f x ∂lam₁ - ∫ x, f x ∂lam₂|} := by
  set S := {r | ∃ f : X → ℝ, Measurable f ∧
      (∀ x, f x ∈ Set.Icc a b) ∧ r = |∫ x, f x ∂lam₁ - ∫ x, f x ∂lam₂|}
  have hba : 0 < b - a := sub_pos.2 hab
  have hbound : ∀ r ∈ S, r ≤ (b - a) * dTV lam₁ lam₂ := by
    rintro _ ⟨f, hf, hfab, rfl⟩
    set φ : X → ℝ := fun x => (2 * f x - (a + b)) / (b - a)
    have hφ : Measurable φ := ((hf.const_mul 2).sub_const _).div_const _
    have hφ1 : ∀ x, |φ x| ≤ 1 := fun x => by
      obtain ⟨h1, h2⟩ := hfab x
      rw [abs_div, abs_of_pos hba, div_le_one hba, abs_le]
      constructor <;> linarith
    have hfi : ∀ (lam : Measure X) [IsProbabilityMeasure lam], Integrable f lam :=
      fun lam _ => gp_integrable_of_bounded hf (M := max |a| |b|) fun x => by
        obtain ⟨h1, h2⟩ := hfab x
        rw [abs_le]
        constructor
        · linarith [neg_abs_le a, le_max_left |a| |b|]
        · linarith [le_abs_self b, le_max_right |a| |b|]
    have hint : ∀ (lam : Measure X) [IsProbabilityMeasure lam],
        ∫ x, φ x ∂lam = (2 * ∫ x, f x ∂lam - (a + b)) / (b - a) := fun lam _ => by
      simp only [φ]
      rw [integral_div, integral_sub ((hfi lam).const_mul 2) (integrable_const _),
        integral_const_mul, integral_const, probReal_univ, one_smul]
    have h := gp_abs_integral_sub_le_tvDist lam₁ lam₂ hφ hφ1
    rw [hint lam₁, hint lam₂, gp_tvDist_eq_two_mul_dTV, ← sub_div, abs_div, abs_of_pos hba,
      div_le_iff₀ hba] at h
    have e : 2 * ∫ x, f x ∂lam₁ - (a + b) - (2 * ∫ x, f x ∂lam₂ - (a + b)) =
        2 * (∫ x, f x ∂lam₁ - ∫ x, f x ∂lam₂) := by ring
    rw [e, abs_mul, abs_two] at h
    nlinarith
  have hne : S.Nonempty := ⟨_, fun _ => a, measurable_const, fun _ => ⟨le_rfl, hab.le⟩, rfl⟩
  have hbdd : BddAbove S := ⟨_, hbound⟩
  have hattain : ∀ A, MeasurableSet A →
      (b - a) * |lam₁.real A - lam₂.real A| ∈ S := by
    intro A hA
    refine ⟨fun x => a + (b - a) * A.indicator 1 x,
      measurable_const.add ((measurable_one.indicator hA).const_mul _), fun x => ?_, ?_⟩
    · by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact ⟨by linarith, by linarith⟩
      · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero]
        exact ⟨le_rfl, hab.le⟩
    · have hint : ∀ (lam : Measure X) [IsProbabilityMeasure lam],
          ∫ x, (a + (b - a) * A.indicator 1 x) ∂lam = a + (b - a) * lam.real A :=
        fun lam _ => by
          have hI : Integrable (fun x => (b - a) * A.indicator (1 : X → ℝ) x) lam :=
            ((integrable_const (1 : ℝ)).indicator hA).const_mul _
          rw [integral_add (integrable_const _) hI, integral_const,
            probReal_univ, one_smul, integral_const_mul, integral_indicator_one hA]
      rw [hint lam₁, hint lam₂]
      have e : a + (b - a) * lam₁.real A - (a + (b - a) * lam₂.real A) =
          (b - a) * (lam₁.real A - lam₂.real A) := by ring
      rw [e, abs_mul, abs_of_pos hba]
  have hS : sSup S = (b - a) * dTV lam₁ lam₂ := by
    refine le_antisymm (csSup_le hne hbound) ?_
    rw [← le_div_iff₀' hba]
    refine gp_dTV_le_of_forall _ _ fun A hA => ?_
    rw [le_div_iff₀' hba]
    exact le_csSup hbdd (hattain A hA)
  rw [hS, ← mul_assoc, inv_mul_cancel₀ hba.ne', one_mul]

end Miao.MarkovProcesses
