/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.FiniteUnions

/-!
# The algebra of intervals and length

SLP §7.2, pp. 174–176: Exercises 7.6 and 7.7. The half-open intervals `(a, b]` with
`a, b ∈ [−∞, +∞]` (`hoi`) are `(−∞, b]`, `(a, b]`, `(a, +∞)` and `(−∞, +∞)` (`hoi_bot_coe`,
`hoi_coe_coe`, `hoi_coe_top`, `hoi_bot_top`), and they form a semialgebra
(`isSemialgebra_hoi`). So the complements and finite unions of such sets form an algebra
(`ex_7_6a`), each of whose members is a finite disjoint union of half-open intervals, and the
Borel sets are the σ-algebra it generates (`ex_7_6b`). Length is a measure on this algebra
(`ex_7_7a`), and a density on `(a, b]` defines one (`ex_7_7b`). With Theorems 7.2 and 7.3,
length determines a unique measure on the Borel sets (`length_unique`, SLP p. 175).

Countable additivity of length on the algebra is taken from Mathlib's Lebesgue measure, whose
construction proves it; the book leaves it as an exercise.
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory MeasurableSpace Function
open scoped ENNReal

/-- The half-open interval `(a, b]` with extended-real endpoints. -/
def hoi (a b : EReal) : Set ℝ := {x | a < (x : EReal) ∧ (x : EReal) ≤ b}

theorem hoi_bot_coe (b : ℝ) : hoi ⊥ b = Iic b := by
  ext x
  simp [hoi, EReal.bot_lt_coe]

theorem hoi_coe_coe (a b : ℝ) : hoi a b = Ioc a b := by
  ext x
  simp [hoi]

theorem hoi_coe_top (a : ℝ) : hoi a ⊤ = Ioi a := by
  ext x
  simp [hoi]

theorem hoi_bot_top : hoi ⊥ ⊤ = univ := by
  ext x
  simp [hoi, EReal.bot_lt_coe]

theorem hoi_inter (a b c d : EReal) : hoi a b ∩ hoi c d = hoi (max a c) (min b d) := by
  ext x
  simp only [hoi, mem_inter_iff, mem_ofPred_eq, max_lt_iff, le_min_iff]
  tauto

theorem hoi_eq_empty {a b : EReal} (h : b ≤ a) : hoi a b = ∅ :=
  eq_empty_of_forall_notMem fun _ hx => absurd (hx.1.trans_le hx.2) (not_lt.2 h)

/-- The generating family of half-open intervals. -/
def intervalGens : Set (Set ℝ) := range fun p : EReal × EReal => hoi p.1 p.2

/-- The half-open intervals form a semialgebra. -/
theorem isSemialgebra_hoi : IsSemialgebra intervalGens := by
  classical
  refine ⟨⟨(⊤, ⊤), hoi_eq_empty le_rfl⟩, ⟨(⊥, ⊤), hoi_bot_top⟩, ?_, ?_⟩
  · rintro _ ⟨⟨a, b⟩, rfl⟩ _ ⟨⟨c, d⟩, rfl⟩
    exact ⟨(max a c, min b d), (hoi_inter a b c d).symm⟩
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    by_cases hab : a < b
    · refine ⟨{hoi ⊥ a, hoi b ⊤}, ?_, ?_, ?_⟩
      · intro X hX
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff] at hX
        rcases hX with rfl | rfl
        exacts [⟨(⊥, a), rfl⟩, ⟨(b, ⊤), rfl⟩]
      · intro X hX Y hY hXY
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff] at hX hY
        have hd : Disjoint (hoi ⊥ a) (hoi b ⊤) := disjoint_left.2 fun x hx hx' =>
          absurd (hx.2.trans_lt (hab.trans hx'.1)) (lt_irrefl _)
        rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
        · exact absurd rfl hXY
        · exact hd
        · exact hd.symm
        · exact absurd rfl hXY
      · ext x
        simp only [hoi, mem_compl_iff, mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton,
          sUnion_insert, sUnion_singleton, mem_union, EReal.bot_lt_coe, true_and, le_top,
          and_true, not_and_or, not_lt, not_le]
    · refine ⟨{univ}, by simpa using ⟨(⊥, ⊤), hoi_bot_top⟩, by simp, ?_⟩
      change (hoi a b)ᶜ = _
      rw [hoi_eq_empty (not_lt.1 hab)]
      simp

/-- The algebra of complements and finite unions of half-open intervals (Exercise 7.6). -/
def intervalAlgebra : Set (Set ℝ) := finUnions intervalGens

/-- **Exercise 7.6a.** `𝒜` is an algebra; it contains the half-open intervals and is contained in
every algebra that does, so it is the family of complements and finite unions of half-open
intervals; and every member is a finite union of disjoint half-open intervals. -/
theorem ex_7_6a :
    IsSetAlgebra intervalAlgebra ∧ intervalGens ⊆ intervalAlgebra ∧
      (∀ 𝒜, IsSetAlgebra 𝒜 → intervalGens ⊆ 𝒜 → intervalAlgebra ⊆ 𝒜) ∧
      ∀ A ∈ intervalAlgebra, ∃ J : Finset (Set ℝ), ↑J ⊆ intervalGens ∧
        (↑J : Set (Set ℝ)).PairwiseDisjoint id ∧ A = ⋃₀ ↑J :=
  ⟨isSetAlgebra_finUnions isSemialgebra_hoi, subset_finUnions,
    fun _ h𝒜 h => finUnions_subset h𝒜 h, fun _ hA => exists_disjoint_rep isSemialgebra_hoi hA⟩

theorem measurableSet_hoi (a b : EReal) : MeasurableSet (hoi a b) := by
  have h1 : MeasurableSet {x : ℝ | a < (x : EReal)} :=
    measurableSet_lt measurable_const measurable_coe_real_ereal
  have h2 : MeasurableSet {x : ℝ | (x : EReal) ≤ b} :=
    measurableSet_le measurable_coe_real_ereal measurable_const
  exact h1.inter h2

theorem measurableSet_of_mem_intervalAlgebra {A : Set ℝ} (hA : A ∈ intervalAlgebra) :
    MeasurableSet A := by
  obtain ⟨I, hI, rfl⟩ := hA
  refine MeasurableSet.sUnion I.countable_toSet fun X hX => ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := hI hX
  exact measurableSet_hoi a b

/-- **Exercise 7.6b.** The Borel sets are the smallest σ-algebra containing `𝒜`. -/
theorem ex_7_6b : borel ℝ = generateFrom intervalAlgebra := by
  apply le_antisymm
  · rw [ex_7_2_Ioc]
    refine generateFrom_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact measurableSet_generateFrom (subset_finUnions ⟨((a : EReal), (b : EReal)),
      hoi_coe_coe a b⟩)
  · exact generateFrom_le fun A hA => by
      exact measurableSet_of_mem_intervalAlgebra hA

/-- **Exercise 7.7a.** Length is a measure on `𝒜`: Lebesgue measure gives `μ(∅) = 0`,
`μ((a, b]) = b − a`, the value `+∞` on unbounded intervals, adds over finite disjoint unions of
bounded intervals, and is countably additive on `𝒜`. -/
theorem ex_7_7a :
    volume (∅ : Set ℝ) = 0 ∧
      (∀ a b : ℝ, a ≤ b → volume (Ioc a b) = ENNReal.ofReal (b - a)) ∧
      (∀ a b : ℝ, volume (Iic b) = ∞ ∧ volume (Ioi a) = ∞ ∧ volume (univ : Set ℝ) = ∞) ∧
      (∀ (n : ℕ) (a b : Fin n → ℝ), Pairwise (Disjoint on fun i => Ioc (a i) (b i)) →
        volume (⋃ i, Ioc (a i) (b i)) = ∑ i, ENNReal.ofReal (b i - a i)) ∧
      IsAlgebraMeasure intervalAlgebra (fun A => volume A) := by
  refine ⟨measure_empty, fun a b _ => Real.volume_Ioc, fun a b => ⟨by simp, by simp, by simp⟩,
    fun n a b hd => ?_, ⟨measure_empty, fun A hA hd _ => ?_⟩⟩
  · rw [measure_iUnion hd fun _ => measurableSet_Ioc, tsum_fintype]
    exact Finset.sum_congr rfl fun i _ => Real.volume_Ioc
  · exact measure_iUnion hd fun n => measurableSet_of_mem_intervalAlgebra (hA n)

/-- On a bounded half-open interval with extended endpoints, two measures that agree on the
intervals `(a, b]` agree. -/
theorem measure_hoi_bounded {ν ν' : Measure ℝ} (h : ∀ a b : ℝ, ν (Ioc a b) = ν' (Ioc a b))
    {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊤) : ν (hoi x y) = ν' (hoi x y) := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => rw [hoi_eq_empty le_top, measure_empty, measure_empty]
  | coe a =>
    induction y using EReal.rec with
    | bot => rw [hoi_eq_empty bot_le, measure_empty, measure_empty]
    | top => exact absurd rfl hy
    | coe b => rw [hoi_coe_coe]; exact h a b

/-- Two measures that agree on the intervals `(a, b]` agree on every half-open interval with
extended endpoints, by continuity from below (Theorem 7.1). -/
theorem measure_hoi_eq {ν ν' : Measure ℝ} (h : ∀ a b : ℝ, ν (Ioc a b) = ν' (Ioc a b))
    (x y : EReal) : ν (hoi x y) = ν' (hoi x y) := by
  let B : ℕ → Set ℝ := fun n => hoi x y ∩ Ioc (-(n : ℝ)) n
  have hB : ∀ n, B n = hoi (max x (-(n : ℝ) : ℝ)) (min y ((n : ℝ) : EReal)) := fun n => by
    change hoi x y ∩ Ioc (-(n : ℝ)) n = _
    rw [← hoi_coe_coe, hoi_inter]
  have hBe : ∀ n, ν (B n) = ν' (B n) := fun n => by
    rw [hB]
    refine measure_hoi_bounded h ?_ ?_
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (min_le_right _ _)
  have hmono : Monotone B := fun m n hmn => inter_subset_inter_right _
    (Ioc_subset_Ioc (by simp [hmn]) (by simp [hmn]))
  have hU : (⋃ n, B n) = hoi x y := by
    rw [← inter_iUnion]
    refine inter_eq_left.2 fun z _ => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_gt |z|
    exact ⟨n, by linarith [neg_abs_le z], (le_abs_self z).trans hn.le⟩
  have h1 := tendsto_measure_iUnion_atTop (μ := ν) hmono
  have h2 := tendsto_measure_iUnion_atTop (μ := ν') hmono
  rw [hU] at h1 h2
  exact tendsto_nhds_unique (h1.congr fun n => hBe n) h2

/-- **Lebesgue measure is unique** (SLP p. 175): a Borel measure that gives every half-open
interval `(a, b]` its length is Lebesgue measure. By Theorems 7.2–7.3: the measure agrees with
length on the algebra `𝒜`, and `ℝ` is the union of the intervals `(−n, n]`, of finite length,
so length is σ-finite on `𝒜`. -/
theorem length_unique {ν : Measure ℝ}
    (hν : ∀ a b : ℝ, a ≤ b → ν (Ioc a b) = ENNReal.ofReal (b - a)) : ν = volume := by
  have hν' : ∀ a b : ℝ, ν (Ioc a b) = volume (Ioc a b) := fun a b => by
    rcases le_total a b with hab | hab
    · rw [hν a b hab, Real.volume_Ioc]
    · rw [Ioc_eq_empty (not_lt.2 hab), measure_empty, measure_empty]
  have hAeq : ∀ A ∈ intervalAlgebra, ν A = volume A := by
    intro A hA
    obtain ⟨J, hJ, hJd, rfl⟩ := exists_disjoint_rep isSemialgebra_hoi hA
    have hJm : ∀ P ∈ J, MeasurableSet (id P) := fun P hP => by
      obtain ⟨⟨a, b⟩, rfl⟩ := hJ hP
      exact measurableSet_hoi a b
    rw [sUnion_eq_biUnion, Finset.set_biUnion_coe]
    change ν (⋃ P ∈ J, id P) = volume (⋃ P ∈ J, id P)
    rw [measure_biUnion_finset hJd hJm, measure_biUnion_finset hJd hJm]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := hJ hP
    exact measure_hoi_eq hν' a b
  refine theorem_7_3 (isSetAlgebra_finUnions isSemialgebra_hoi)
    ((BorelSpace.measurable_eq (α := ℝ)).trans ex_7_6b) ?_ hAeq fun _ _ => rfl
  refine ⟨fun n => Ioc (-(n : ℝ)) n, fun n => subset_finUnions ⟨((-(n : ℝ) : ℝ), (n : ℝ)),
    hoi_coe_coe _ _⟩, fun n => by simp [Real.volume_Ioc], ?_⟩
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact ⟨n, by linarith [neg_abs_le x], (le_abs_self x).trans hn.le⟩

/-- **Exercise 7.7b.** On `S = (a, b]`, a density `π ≥ 0` with `∫ₐᵇ π = 1` defines
`μ(A) = ∫_{A ∩ S} π`: on intervals `μ((c, d]) = μ([c, d]) = μ([c, d)) = μ((c, d)) = ∫_c^d π`
(SLP (1), p. 171), `μ(S) = 1`, and `μ` is a measure on the algebra generated by the half-open
subintervals of `S`. -/
theorem ex_7_7b {a b : ℝ} (hab : a ≤ b) {π : ℝ → ℝ} (hπ0 : ∀ x, 0 ≤ π x)
    (hπi : IntegrableOn π (Ioc a b)) (hπ1 : ∫ x in a..b, π x = 1) :
    (∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b →
      ∫⁻ x in Ioc c d ∩ Ioc a b, ENNReal.ofReal (π x) = ENNReal.ofReal (∫ x in c..d, π x) ∧
      ∫⁻ x in Icc c d ∩ Ioc a b, ENNReal.ofReal (π x) =
        ∫⁻ x in Ioc c d ∩ Ioc a b, ENNReal.ofReal (π x) ∧
      ∫⁻ x in Ico c d ∩ Ioc a b, ENNReal.ofReal (π x) =
        ∫⁻ x in Ioc c d ∩ Ioc a b, ENNReal.ofReal (π x) ∧
      ∫⁻ x in Ioo c d ∩ Ioc a b, ENNReal.ofReal (π x) =
        ∫⁻ x in Ioc c d ∩ Ioc a b, ENNReal.ofReal (π x)) ∧
    ∫⁻ x in Ioc a b ∩ Ioc a b, ENNReal.ofReal (π x) = 1 ∧
    IsAlgebraMeasure {B | ∃ A ∈ intervalAlgebra, B = A ∩ Ioc a b}
      (fun A => ∫⁻ x in A ∩ Ioc a b, ENNReal.ofReal (π x)) := by
  have hint : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b →
      ∫⁻ x in Ioc c d ∩ Ioc a b, ENNReal.ofReal (π x) = ENNReal.ofReal (∫ x in c..d, π x) := by
    intro c d hac hcd hdb
    rw [inter_eq_left.2 (Ioc_subset_Ioc hac hdb), intervalIntegral.integral_of_le hcd,
      ofReal_integral_eq_lintegral_ofReal (hπi.mono_set (Ioc_subset_Ioc hac hdb))
        (Filter.Eventually.of_forall hπ0)]
  refine ⟨fun c d hac hcd hdb => ⟨hint c d hac hcd hdb, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact setLIntegral_congr (Ioc_ae_eq_Icc.symm.inter (Filter.EventuallyEq.refl _ _))
  · exact setLIntegral_congr (Ico_ae_eq_Ioc.inter (Filter.EventuallyEq.refl _ _))
  · exact setLIntegral_congr (Ioo_ae_eq_Ioc.inter (Filter.EventuallyEq.refl _ _))
  · rw [hint a b le_rfl hab le_rfl, hπ1, ENNReal.ofReal_one]
  · refine ⟨by simp, fun A hA hd _ => ?_⟩
    rw [iUnion_inter]
    have hm : ∀ n, MeasurableSet (A n ∩ Ioc a b) := fun n => by
      obtain ⟨A', hA', hAeq⟩ := hA n
      rw [hAeq, inter_assoc, inter_self]
      exact (measurableSet_of_mem_intervalAlgebra hA').inter measurableSet_Ioc
    rw [lintegral_iUnion hm (fun m n hmn => (hd hmn).mono inter_subset_left inter_subset_left)]

end StokeyLucasPrescott.MeasureIntegration
