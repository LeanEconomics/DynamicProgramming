/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.Integration

/-!
# Riemann and Lebesgue integrals

SLP §7.4, pp. 184–185: Exercise 7.16. Darboux lower and upper sums over partitions
`0 = a₀ < a₁ < ⋯ < aₙ = 1` of `[0, 1]` (`lowerSum`, `upperSum`) and the lower and upper Riemann
integrals (`lowerRiemann`, `upperRiemann`). For the indicator of the rationals every subinterval
contains rationals and irrationals, so every lower sum is `0` and every upper sum is `1`
(`ex_7_16`): the Riemann integral does not exist. Its Lebesgue integral exists and is `0`, the
rationals being a null set (`dirichlet_lintegral`).
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory

/-- The indicator of the rationals (SLP Exercise 7.16). -/
noncomputable def dirichlet (x : ℝ) : ℝ := (range ((↑) : ℚ → ℝ)).indicator 1 x

/-- A partition `0 = a₀ < a₁ < ⋯ < aₙ = 1` of `[0, 1]`. -/
def IsPartition01 (n : ℕ) (a : ℕ → ℝ) : Prop :=
  a 0 = 0 ∧ a n = 1 ∧ ∀ i < n, a i < a (i + 1)

/-- The lower Darboux sum `Σ (aᵢ₊₁ − aᵢ) inf_{[aᵢ, aᵢ₊₁]} f`. -/
noncomputable def lowerSum (f : ℝ → ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (a (i + 1) - a i) * sInf (f '' Icc (a i) (a (i + 1)))

/-- The upper Darboux sum `Σ (aᵢ₊₁ − aᵢ) sup_{[aᵢ, aᵢ₊₁]} f`. -/
noncomputable def upperSum (f : ℝ → ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (a (i + 1) - a i) * sSup (f '' Icc (a i) (a (i + 1)))

/-- The lower Riemann integral: the supremum of the lower sums. -/
noncomputable def lowerRiemann (f : ℝ → ℝ) : ℝ :=
  sSup {L | ∃ n a, IsPartition01 n a ∧ L = lowerSum f n a}

/-- The upper Riemann integral: the infimum of the upper sums. -/
noncomputable def upperRiemann (f : ℝ → ℝ) : ℝ :=
  sInf {U | ∃ n a, IsPartition01 n a ∧ U = upperSum f n a}

/-- On a nondegenerate interval the indicator of the rationals takes exactly the values `0`
and `1`. -/
theorem dirichlet_image {x y : ℝ} (hxy : x < y) : dirichlet '' Icc x y = {0, 1} := by
  apply Subset.antisymm
  · rintro _ ⟨z, -, rfl⟩
    by_cases hz : z ∈ range ((↑) : ℚ → ℝ)
    · simp [dirichlet, indicator_of_mem hz]
    · simp [dirichlet, indicator_of_notMem hz]
  · rintro v (rfl | rfl)
    · obtain ⟨r, hr, hxr, hry⟩ := exists_irrational_btwn hxy
      refine ⟨r, ⟨hxr.le, hry.le⟩, indicator_of_notMem ?_ _⟩
      rintro ⟨q, hq⟩
      exact hr ⟨q, hq⟩
    · obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
      exact ⟨q, ⟨hxq.le, hqy.le⟩, by simp [dirichlet]⟩

/-- **Exercise 7.16.** For the indicator of the rationals on `[0, 1]`, every lower sum is `0`
and every upper sum is `1`; so the lower Riemann integral is `0`, the upper is `1`, and the
Riemann integral does not exist. -/
theorem ex_7_16 :
    (∀ n a, IsPartition01 n a → lowerSum dirichlet n a = 0 ∧ upperSum dirichlet n a = 1) ∧
      lowerRiemann dirichlet = 0 ∧ upperRiemann dirichlet = 1 := by
  have hsums : ∀ n a, IsPartition01 n a →
      lowerSum dirichlet n a = 0 ∧ upperSum dirichlet n a = 1 := by
    rintro n a ⟨h0, hn, hmono⟩
    constructor
    · refine Finset.sum_eq_zero fun i hi => ?_
      rw [dirichlet_image (hmono i (Finset.mem_range.1 hi)), csInf_pair]
      simp
    · have : upperSum dirichlet n a = ∑ i ∈ Finset.range n, (a (i + 1) - a i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [dirichlet_image (hmono i (Finset.mem_range.1 hi)), csSup_pair]
        simp
      rw [this, Finset.sum_range_sub (f := a), hn, h0, sub_zero]
  have hpart : IsPartition01 1 (fun i => if i = 0 then 0 else 1) := ⟨rfl, rfl, fun i hi => by
    simp only [Nat.lt_one_iff] at hi
    subst hi
    norm_num⟩
  refine ⟨hsums, ?_, ?_⟩
  · have : {L | ∃ n a, IsPartition01 n a ∧ L = lowerSum dirichlet n a} = {0} := by
      ext L
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨n, a, ha, rfl⟩
        exact (hsums n a ha).1
      · rintro rfl
        exact ⟨1, _, hpart, ((hsums 1 _ hpart).1).symm⟩
    rw [lowerRiemann, this, csSup_singleton]
  · have : {U | ∃ n a, IsPartition01 n a ∧ U = upperSum dirichlet n a} = {1} := by
      ext U
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨n, a, ha, rfl⟩
        exact (hsums n a ha).2
      · rintro rfl
        exact ⟨1, _, hpart, ((hsums 1 _ hpart).2).symm⟩
    rw [upperRiemann, this, csInf_singleton]

/-- The Lebesgue integral of the indicator of the rationals over `[0, 1]` exists and is `0`
(SLP p. 185: the Lebesgue integral is defined for a broader class of functions). -/
theorem dirichlet_lintegral :
    ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (dirichlet x) = 0 := by
  have hnull : volume (range ((↑) : ℚ → ℝ)) = 0 := (countable_range _).measure_zero volume
  have hae : (fun x => ENNReal.ofReal (dirichlet x)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
    refine ae_restrict_of_ae (measure_mono_null (fun x hx => ?_) hnull)
    by_contra h
    exact hx (by simp [dirichlet, indicator_of_notMem h])
  rw [lintegral_congr_ae hae]
  simp

end StokeyLucasPrescott.MeasureIntegration
