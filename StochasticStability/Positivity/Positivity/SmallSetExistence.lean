/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.SmallSets
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The existence of small sets (MT §5.2, Theorems 5.2.1–5.2.3)

Meyn and Tweedie, §5.2, pp. 103–106. Throughout, `B(X)` is **countably generated**
(`MeasurableSpace.CountablyGenerated X`), the standing assumption of MT p. 50 (a "general state
space"); this is the hypothesis the proof needs, both for jointly measurable densities and for a
countable family of sets approximating every measurable set.

* `transDensity P φ n x y = pⁿ(x, y)` (5.15): the density of the absolutely continuous part of
  `Pⁿ(x, ·)` with respect to `φ`, taken to be Mathlib's kernel Radon–Nikodym derivative, which is
  jointly measurable (`measurable_transDensity`). `theorem_5_2_1_density` is (5.15):
  `Pⁿ(x, B) = ∫_B pⁿ(x, y) φ(dy) + P⊥(x, B)` with `P⊥(x, ·) ⟂ φ`. This is part (i) of the proof
  of Theorem 5.2.1.
* `ae_exists_transDensity_pos`: under the hypothesis of Theorem 5.2.1,
  `Σₙ pⁿ(x, y) > 0` for `x ∈ A` and `φ`-a.e. `y ∈ A` (MT p. 104).
* `exists_rect_of_not_ae_zero`: the replacement for the density-point argument (5.19)–(5.23).
  If `F(x, z) = φ(Uₓ ∩ Vᶻ)` does not vanish for a.e. `x, z ∈ A`, there are `E, D ⊆ A` of positive
  measure with `F ≥ ε > 0` on `E × D`. The proof approximates the sections `Uₓ`, `Vᶻ` by the sets
  of a countable measure-dense family; no differentiation of measures is needed.
* **Theorem 5.2.1** (`theorem_5_2_1`, p. 103): for finite `φ` and `A` with `φ(A) > 0` such that
  every `B ⊆ A` with `φ(B) > 0` is reached from every `x ∈ A`, there are `C ⊆ A` with
  `φ(C) > 0`, `m ≥ 1` and `δ > 0` with `Pᵐ(x, B) ≥ δ φ(B ∩ C)` for all `x ∈ C`: this is the
  integrated form of (5.16), `pᵐ(x, y) ≥ δ` on `C × C`, which is how (5.16) is used.
* `theorem_5_2_1_density_ge`: the density form of (5.16), `pᵐ(x, y) ≥ δ` for `x ∈ C` and
  `φ`-a.e. `y ∈ C`, for the jointly measurable version of the densities.
* **Theorem 5.2.2** (`theorem_5_2_2`, p. 105): for a `ψ`-irreducible chain, every `A ∈ B⁺(X)`
  contains a `νₘ`-small set `C ∈ B⁺(X)` with `νₘ(C) > 0`.
* **Theorem 5.2.3** (`theorem_5_2_3`, `theorem_5_2_3_resolvent`, p. 105): the minorization
  condition (5.2) holds for some `m`-skeleton, and for every resolvent `K_{a_ε}`, `0 < ε < 1`.
* **Proposition 5.2.4 (ii)** (`proposition_5_2_4_ii`, p. 106): `X` is a countable union of small
  sets, `C̄(n, m) = {y : Pⁿ(y, C) ≥ m⁻¹}` (5.27).

**Corrections and hypotheses.** The theorems need `B(X)` countably generated (the book's standing
assumption). The book takes `φ` σ-finite in Theorem 5.2.1; the statement here takes `φ` finite,
which is all Theorem 5.2.2 needs (a maximal irreducibility measure has an equivalent probability
measure). The specific version of the densities built in the book's proof (with the
Chapman–Kolmogorov inequality (5.17)) is not needed: the Chapman–Kolmogorov equations for the
kernels themselves suffice.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal symmDiff

variable {X : Type*} [MeasurableSpace X]

variable [MeasurableSpace.CountablyGenerated X]

/-! ### Jointly measurable densities -/

/-- The density `pⁿ(x, y)` of (5.15): the Radon–Nikodym derivative of the absolutely continuous
part of `Pⁿ(x, ·)` with respect to `φ`. -/
noncomputable def transDensity (P : Kernel X X) (φ : Measure X) (n : ℕ) (x y : X) : ℝ≥0∞ :=
  Kernel.rnDeriv (P ^ n) (Kernel.const X φ) x y

/-- The densities are jointly measurable (part (i) of the proof of Theorem 5.2.1, MT p. 103). -/
theorem measurable_transDensity (P : Kernel X X) (φ : Measure X) (n : ℕ) :
    Measurable fun p : X × X => transDensity P φ n p.1 p.2 :=
  Kernel.measurable_rnDeriv _ _

/-- `∫_B pⁿ(x, y) φ(dy) ≤ Pⁿ(x, B)`. -/
theorem setLIntegral_transDensity_le (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    ∫⁻ y in B, transDensity P φ n x y ∂φ ≤ (P ^ n) x B := by
  have := isMarkovKernel_pow P n
  have h := Kernel.setLIntegral_rnDeriv_le (κ := P ^ n) (η := Kernel.const X φ) (a := x) hB
  rwa [Kernel.const_apply] at h

/-- `∫ pⁿ(x, y) g(y) φ(dy) ≤ ∫ g dPⁿ(x, ·)` for measurable `g ≥ 0`. -/
theorem lintegral_transDensity_mul_le (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] (n : ℕ) (x : X) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, transDensity P φ n x y * g y ∂φ ≤ ∫⁻ y, g y ∂(P ^ n) x := by
  have := isMarkovKernel_pow P n
  have h := Kernel.withDensity_rnDeriv_le (P ^ n) (Kernel.const X φ) x
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _), Kernel.const_apply] at h
  calc ∫⁻ y, transDensity P φ n x y * g y ∂φ
      = ∫⁻ y, g y ∂φ.withDensity (Kernel.rnDeriv (P ^ n) (Kernel.const X φ) x) :=
        (lintegral_withDensity_eq_lintegral_mul _
          (Kernel.measurable_rnDeriv_right _ _ x) hg).symm
    _ ≤ ∫⁻ y, g y ∂(P ^ n) x := lintegral_mono' h le_rfl

/-- **(5.15)** (MT p. 103): the Lebesgue decomposition
`Pⁿ(x, B) = ∫_B pⁿ(x, y) φ(dy) + P⊥(x, B)`, with `P⊥(x, ·)` singular with respect to `φ`, and
with jointly measurable densities. -/
theorem theorem_5_2_1_density (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] (n : ℕ) :
    Measurable (fun p : X × X => transDensity P φ n p.1 p.2) ∧
      ∀ x, ∃ Q : Measure X, Q ⟂ₘ φ ∧ ∀ B, MeasurableSet B →
        (P ^ n) x B = ∫⁻ y in B, transDensity P φ n x y ∂φ + Q B := by
  have := isMarkovKernel_pow P n
  refine ⟨measurable_transDensity P φ n, fun x => ⟨Kernel.singularPart (P ^ n)
    (Kernel.const X φ) x, ?_, fun B hB => ?_⟩⟩
  · have h := Kernel.mutuallySingular_singularPart (P ^ n) (Kernel.const X φ) x
    rwa [Kernel.const_apply] at h
  · have h := congrArg (fun κ : Kernel X X => κ x B)
      (Kernel.rnDeriv_add_singularPart (P ^ n) (Kernel.const X φ))
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add] at h
    rw [← h, Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _), Kernel.const_apply,
      withDensity_apply _ hB]
    rfl

/-- Under the hypothesis of Theorem 5.2.1, for `x ∈ A`, `Σₙ pⁿ⁺¹(x, y) > 0` for `φ`-a.e.
`y ∈ A` (MT p. 104). -/
theorem ae_exists_transDensity_pos (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] {A : Set X} (hA : MeasurableSet A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 < φ B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B)
    {x : X} (hx : x ∈ A) :
    ∀ᵐ y ∂φ.restrict A, ∃ n, 0 < transDensity P φ (n + 1) x y := by
  set N : Set X := A ∩ ⋂ n, {y | transDensity P φ (n + 1) x y = 0} with hNdef
  have hmeas : ∀ n, Measurable fun y => transDensity P φ n x y := fun n =>
    Kernel.measurable_rnDeriv_right _ _ x
  have hNm : MeasurableSet N :=
    hA.inter (MeasurableSet.iInter fun n => hmeas (n + 1) (measurableSet_singleton 0))
  have hN : φ N = 0 := by
    by_contra hpos
    -- the singular parts live on null sets
    have hdec : ∀ n, ∃ Q : Measure X, Q ⟂ₘ φ ∧ ∀ B, MeasurableSet B →
        (P ^ (n + 1)) x B = ∫⁻ y in B, transDensity P φ (n + 1) x y ∂φ + Q B :=
      fun n => (theorem_5_2_1_density P φ (n + 1)).2 x
    choose Q hQ hQB using hdec
    have hsing : ∀ n, ∃ s, MeasurableSet s ∧ Q n s = 0 ∧ φ sᶜ = 0 := fun n => by
      obtain ⟨s, hs, h1, h2⟩ := hQ n
      exact ⟨s, hs, h1, h2⟩
    choose s hs hs0 hs1 using hsing
    set B := N ∩ ⋂ n, s n
    have hBm : MeasurableSet B := hNm.inter (MeasurableSet.iInter hs)
    have hBφ : φ B = φ N := by
      refine measure_congr ?_
      refine (inter_ae_eq_left_of_ae_eq_univ ?_)
      refine ae_eq_univ.2 ?_
      rw [compl_iInter]
      exact measure_iUnion_null hs1
    obtain ⟨k, hk⟩ := h B hBm (inter_subset_left.trans inter_subset_left)
      (by rw [hBφ]; exact pos_iff_ne_zero.2 hpos) x hx
    have hz1 : ∫⁻ y in B, transDensity P φ (k + 1) x y ∂φ = 0 := by
      rw [setLIntegral_congr_fun hBm (g := fun _ => 0) fun y hy => by
        have : y ∈ ⋂ n, {y | transDensity P φ (n + 1) x y = 0} := hy.1.2
        exact mem_iInter.1 this k]
      simp
    have hz2 : Q k B = 0 :=
      measure_mono_null (inter_subset_right.trans (iInter_subset _ k)) (hs0 k)
    rw [hQB k B hBm, hz1, hz2, add_zero] at hk
    exact lt_irrefl _ hk
  have h1 : ∀ᵐ y ∂φ, y ∉ N := measure_eq_zero_iff_ae_notMem.1 hN
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae h1] with y hyA hyN
  by_contra hc
  push Not at hc
  exact hyN ⟨hyA, mem_iInter.2 fun n => nonpos_iff_eq_zero.1 (hc n)⟩

/-! ### Selecting a rectangle -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- `φ(s ∩ t) ≤ φ(a ∩ b) + φ(a ∆ s) + φ(b ∆ t)`. -/
theorem measure_inter_le_add_symmDiff (φ : Measure X) (a b s t : Set X) :
    φ (s ∩ t) ≤ φ (a ∩ b) + φ (a ∆ s) + φ (b ∆ t) := by
  calc φ (s ∩ t) ≤ φ ((a ∩ b) ∪ (a ∆ s) ∪ (b ∆ t)) := measure_mono fun y ⟨hs, ht⟩ => by
        by_cases ha : y ∈ a <;> by_cases hb : y ∈ b
        · exact Or.inl (Or.inl ⟨ha, hb⟩)
        · exact Or.inr (Or.inr ⟨ht, hb⟩)
        · exact Or.inl (Or.inr (Or.inr ⟨hs, ha⟩))
        · exact Or.inl (Or.inr (Or.inr ⟨hs, ha⟩))
    _ ≤ φ ((a ∩ b) ∪ (a ∆ s)) + φ (b ∆ t) := measure_union_le _ _
    _ ≤ φ (a ∩ b) + φ (a ∆ s) + φ (b ∆ t) := by gcongr; exact measure_union_le _ _

omit [MeasurableSpace.CountablyGenerated X] in
/-- If `a < 5 (j + 1)⁻¹` for every `j`, then `a = 0`. -/
theorem eq_zero_of_forall_lt_five_inv {a : ℝ≥0∞} (h : ∀ j : ℕ, a < 5 * ((j : ℝ≥0∞) + 1)⁻¹) :
    a = 0 := by
  by_contra ha
  have h5 : a / 5 ≠ 0 := by simp [ha]
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h5
  have h1 := (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).1 hj
  have h2 : 5 * ((j : ℝ≥0∞) + 1)⁻¹ ≤ (j : ℝ≥0∞)⁻¹ * 5 := by
    rw [mul_comm]
    gcongr
    exact le_self_add
  exact lt_irrefl _ ((h j).trans_le h2 |>.trans h1)

/-- **Selecting a rectangle** (the replacement for (5.19)–(5.23), MT pp. 104–105). Let
`F(x, z) = φ(Uₓ ∩ Vᶻ)`, where `Uₓ = {y : (x, y) ∈ U}` and `Vᶻ = {y : (y, z) ∈ V}`. If it is not
true that `F(x, z) = 0` for a.e. `x ∈ A` and a.e. `z ∈ A`, then there are `E, D ⊆ A` of positive
measure and `ε > 0` with `F ≥ ε` on `E × D`. The sections are approximated by the sets of a
countable measure-dense family (here `B(X)` countably generated is used). -/
theorem exists_rect_of_not_ae_zero (φ : Measure X) [IsFiniteMeasure φ] {A : Set X}
    (hA : MeasurableSet A) {U V : Set (X × X)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : ¬ ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A,
      φ (Prod.mk x ⁻¹' U ∩ (fun y => (y, z)) ⁻¹' V) = 0) :
    ∃ E D : Set X, E ⊆ A ∧ D ⊆ A ∧ MeasurableSet E ∧ MeasurableSet D ∧ 0 < φ E ∧ 0 < φ D ∧
      ∃ ε : ℝ≥0∞, 0 < ε ∧
        ∀ x ∈ E, ∀ z ∈ D, ε ≤ φ (Prod.mk x ⁻¹' U ∩ (fun y => (y, z)) ⁻¹' V) := by
  set F : X → X → ℝ≥0∞ := fun x z => φ (Prod.mk x ⁻¹' U ∩ (fun y => (y, z)) ⁻¹' V) with hFdef
  -- a positive threshold
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ¬ ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A,
      F x z < 5 * ((j : ℝ≥0∞) + 1)⁻¹ := by
    by_contra hc
    push Not at hc
    refine h ?_
    have h1 : ∀ᵐ x ∂φ.restrict A, ∀ j : ℕ, ∀ᵐ z ∂φ.restrict A,
        F x z < 5 * ((j : ℝ≥0∞) + 1)⁻¹ := ae_all_iff.2 hc
    filter_upwards [h1] with x hx
    filter_upwards [ae_all_iff.2 hx] with z hz
    exact eq_zero_of_forall_lt_five_inv hz
  set ε : ℝ≥0∞ := ((j : ℝ≥0∞) + 1)⁻¹ with hεdef
  have hε0 : 0 < ε := ENNReal.inv_pos.2 (by simp)
  have hεt : ε ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
  have hε2 : ε + ε ≠ ∞ := ENNReal.add_ne_top.2 ⟨hεt, hεt⟩
  obtain ⟨𝒜, h𝒜c, h𝒜d⟩ := exists_countable_measureDense φ
  have := h𝒜c.to_subtype
  -- the two families of approximating pieces
  set Es : Set X → Set X := fun S => {x | x ∈ A ∧ φ ((Prod.mk x ⁻¹' U) ∆ S) < ε} with hEs
  set Ds : Set X → Set X := fun T => {z | z ∈ A ∧ φ (((fun y => (y, z)) ⁻¹' V) ∆ T) < ε}
    with hDs
  have hEsm : ∀ S ∈ 𝒜, MeasurableSet (Es S) := fun S hS => by
    have hset : (fun x => φ ((Prod.mk x ⁻¹' U) ∆ S)) =
        fun x => φ (Prod.mk x ⁻¹' (U ∆ (univ ×ˢ S))) := by
      ext x; congr 1; ext y; simp [mem_symmDiff]
    have hmeas : Measurable fun x => φ ((Prod.mk x ⁻¹' U) ∆ S) := by
      rw [hset]
      exact measurable_measure_prodMk_left (hU.symmDiff (MeasurableSet.univ.prod
        (h𝒜d.measurable S hS)))
    exact hA.inter (measurableSet_lt hmeas measurable_const)
  have hDsm : ∀ T ∈ 𝒜, MeasurableSet (Ds T) := fun T hT => by
    have hset : (fun z => φ (((fun y => (y, z)) ⁻¹' V) ∆ T)) =
        fun z => φ ((fun y => (y, z)) ⁻¹' (V ∆ (T ×ˢ univ))) := by
      ext z; congr 1; ext y; simp [mem_symmDiff]
    have hmeas : Measurable fun z => φ (((fun y => (y, z)) ⁻¹' V) ∆ T) := by
      rw [hset]
      exact measurable_measure_prodMk_right (hV.symmDiff ((h𝒜d.measurable T hT).prod
        MeasurableSet.univ))
    exact hA.inter (measurableSet_lt hmeas measurable_const)
  -- every point of `A` lies in one of the pieces
  have hεr : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal hεt
  have hEcov : ∀ x ∈ A, ∃ S ∈ 𝒜, x ∈ Es S := fun x hx => by
    obtain ⟨S, hS, hlt⟩ := h𝒜d.approx (Prod.mk x ⁻¹' U) (measurable_prodMk_left hU)
      (measure_ne_top _ _) ε.toReal (ENNReal.toReal_pos hε0.ne' hεt)
    exact ⟨S, hS, hx, by rwa [hεr] at hlt⟩
  have hDcov : ∀ z ∈ A, ∃ T ∈ 𝒜, z ∈ Ds T := fun z hz => by
    obtain ⟨T, hT, hlt⟩ := h𝒜d.approx ((fun y => (y, z)) ⁻¹' V)
      ((measurable_id.prodMk measurable_const) hV) (measure_ne_top _ _) ε.toReal
      (ENNReal.toReal_pos hε0.ne' hεt)
    exact ⟨T, hT, hz, by rwa [hεr] at hlt⟩
  by_contra hcon
  refine hj ?_
  -- the null pieces
  set N₁ : Set X := ⋃ S : 𝒜, ⋃ (_ : φ (Es S) = 0), Es S
  set N₂ : Set X := ⋃ T : 𝒜, ⋃ (_ : φ (Ds T) = 0), Ds T
  have hN₁ : φ N₁ = 0 := measure_iUnion_null fun S => measure_iUnion_null fun h => h
  have hN₂ : φ N₂ = 0 := measure_iUnion_null fun T => measure_iUnion_null fun h => h
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₁)]
    with x hxA hxN
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₂)]
    with z hzA hzN
  by_contra hge
  push Not at hge
  obtain ⟨S, hS, hxS⟩ := hEcov x hxA
  obtain ⟨T, hT, hzT⟩ := hDcov z hzA
  have hES : φ (Es S) ≠ 0 := fun h0 => hxN (mem_iUnion.2 ⟨⟨S, hS⟩, mem_iUnion.2 ⟨h0, hxS⟩⟩)
  have hDT : φ (Ds T) ≠ 0 := fun h0 => hzN (mem_iUnion.2 ⟨⟨T, hT⟩, mem_iUnion.2 ⟨h0, hzT⟩⟩)
  refine hcon ⟨Es S, Ds T, fun y hy => hy.1, fun y hy => hy.1, hEsm S hS, hDsm T hT,
    pos_iff_ne_zero.2 hES, pos_iff_ne_zero.2 hDT, ε, hε0, fun x' hx' z' hz' => ?_⟩
  -- `φ(S ∩ T) > 3ε`
  have hST : 3 * ε < φ (S ∩ T) := by
    have h1 := measure_inter_le_add_symmDiff φ S T (Prod.mk x ⁻¹' U) ((fun y => (y, z)) ⁻¹' V)
    rw [symmDiff_comm S, symmDiff_comm T] at h1
    have h2 : F x z < φ (S ∩ T) + (ε + ε) := by
      calc F x z ≤ _ := h1
        _ = φ (S ∩ T) + (φ ((Prod.mk x ⁻¹' U) ∆ S) + φ (((fun y => (y, z)) ⁻¹' V) ∆ T)) := by
          rw [add_assoc]
        _ < φ (S ∩ T) + (ε + ε) :=
          ENNReal.add_lt_add_left (measure_ne_top _ _) (ENNReal.add_lt_add hxS.2 hzT.2)
    have h3 : 3 * ε + (ε + ε) < φ (S ∩ T) + (ε + ε) := by
      calc 3 * ε + (ε + ε) = 5 * ε := by ring
        _ ≤ F x z := hge
        _ < _ := h2
    exact (ENNReal.add_lt_add_iff_right hε2).1 h3
  have h1 := measure_inter_le_add_symmDiff φ (Prod.mk x' ⁻¹' U) ((fun y => (y, z')) ⁻¹' V) S T
  have h4 : ε + (ε + ε) < F x' z' + (ε + ε) := by
    calc ε + (ε + ε) = 3 * ε := by ring
      _ < φ (S ∩ T) := hST
      _ ≤ _ := h1
      _ = F x' z' + (φ ((Prod.mk x' ⁻¹' U) ∆ S) + φ (((fun y => (y, z')) ⁻¹' V) ∆ T)) := by
        rw [add_assoc]
      _ < F x' z' + (ε + ε) :=
        ENNReal.add_lt_add_left (measure_ne_top _ _) (ENNReal.add_lt_add hx'.2 hz'.2)
  exact ((ENNReal.add_lt_add_iff_right hε2).1 h4).le

/-! ### Theorem 5.2.1 -/

/-- The level sets `{(x, y) : pⁿ⁺¹(x, y) ≥ (k + 1)⁻¹}` of the densities, the sets `Aₙ(η)` of
MT p. 104. -/
def densLevel (P : Kernel X X) (φ : Measure X) (n k : ℕ) : Set (X × X) :=
  {p | ((k : ℝ≥0∞) + 1)⁻¹ ≤ transDensity P φ (n + 1) p.1 p.2}

/-- The level sets are measurable. -/
theorem measurableSet_densLevel (P : Kernel X X) (φ : Measure X) (n k : ℕ) :
    MeasurableSet (densLevel P φ n k) :=
  measurableSet_le measurable_const (measurable_transDensity P φ (n + 1))

/-- The positivity statement of MT p. 104: under the hypothesis of Theorem 5.2.1 there are
`n, m, η` such that `φ{y : pⁿ(x, y) ≥ η, pᵐ(y, z) ≥ η}` is not zero for a.e. `x, z ∈ A`. -/
theorem exists_densLevel_not_ae_zero (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] {A : Set X} (hA : MeasurableSet A) (hφA : 0 < φ A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 < φ B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B) :
    ∃ n m k : ℕ, ¬ ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A,
      φ (Prod.mk x ⁻¹' densLevel P φ n k ∩ (fun y => (y, z)) ⁻¹' densLevel P φ m k) = 0 := by
  by_contra hc
  push Not at hc
  have hne : φ.restrict A ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hφA.ne'
  have : (ae (φ.restrict A)).NeBot := ae_neBot.2 hne
  -- for a.e. `x, z`, a.e. `y` lies in no pair of level sets
  have h1 : ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A, ∀ᵐ y ∂φ.restrict A,
      ∀ n m k : ℕ, ¬ ((x, y) ∈ densLevel P φ n k ∧ (y, z) ∈ densLevel P φ m k) := by
    have hx : ∀ᵐ x ∂φ.restrict A, ∀ n m k : ℕ, ∀ᵐ z ∂φ.restrict A,
        φ (Prod.mk x ⁻¹' densLevel P φ n k ∩ (fun y => (y, z)) ⁻¹' densLevel P φ m k) = 0 :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun k => hc n m k
    filter_upwards [hx] with x hx
    have hz : ∀ᵐ z ∂φ.restrict A, ∀ n m k : ℕ,
        φ (Prod.mk x ⁻¹' densLevel P φ n k ∩ (fun y => (y, z)) ⁻¹' densLevel P φ m k) = 0 :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun k => hx n m k
    filter_upwards [hz] with z hz
    exact ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun k =>
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hz n m k))
  -- hence for a.e. `x, z`, a.e. `y` does not reach `z`
  have h2 : ∀ᵐ x ∂φ.restrict A, ∀ᵐ z ∂φ.restrict A, ∀ᵐ y ∂φ.restrict A,
      ∀ m, transDensity P φ (m + 1) y z = 0 := by
    filter_upwards [ae_restrict_mem hA, h1] with x hxA hx
    filter_upwards [hx] with z hz
    filter_upwards [hz, ae_exists_transDensity_pos P φ hA h hxA] with y hy hpos
    obtain ⟨n, hn⟩ := hpos
    intro m
    by_contra hm
    obtain ⟨k₁, hk₁⟩ := ENNReal.exists_inv_nat_lt hn.ne'
    obtain ⟨k₂, hk₂⟩ := ENNReal.exists_inv_nat_lt hm
    refine hy n m (max k₁ k₂) ⟨?_, ?_⟩
    · refine le_trans ?_ hk₁.le
      gcongr
      exact (Nat.cast_le.2 (le_max_left k₁ k₂)).trans le_self_add
    · refine le_trans ?_ hk₂.le
      gcongr
      exact (Nat.cast_le.2 (le_max_right k₁ k₂)).trans le_self_add
  obtain ⟨x, hx⟩ := h2.exists
  have hmeas : MeasurableSet {q : X × X | ∀ m, transDensity P φ (m + 1) q.2 q.1 = 0} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun m =>
      ((measurable_transDensity P φ (m + 1)).comp measurable_swap) (measurableSet_singleton 0)
  have h3 := (Measure.ae_ae_comm (μ := φ.restrict A) (ν := φ.restrict A)
    (p := fun z y => ∀ m, transDensity P φ (m + 1) y z = 0) hmeas).1 hx
  obtain ⟨y, hy, hyA⟩ := (h3.and (ae_restrict_mem hA)).exists
  obtain ⟨z, hz1, hz2⟩ := (hy.and (ae_exists_transDensity_pos P φ hA h hyA)).exists
  obtain ⟨m, hm⟩ := hz2
  exact hm.ne' (hz1 m)

/-- **Theorem 5.2.1** (MT p. 103). Let `B(X)` be countably generated, `φ` a finite measure and
`A` a set with `φ(A) > 0` such that every `B ⊆ A` with `φ(B) > 0` is reached from every
`x ∈ A`: `Σ_{k ≥ 1} Pᵏ(x, B) > 0`. Then there are `C ⊆ A` with `φ(C) > 0`, `m ≥ 1` and `δ > 0`
such that `Pᵐ(x, B) ≥ δ φ(B ∩ C)` for every `x ∈ C`: the integrated form of (5.16). -/
theorem theorem_5_2_1 (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) [IsFiniteMeasure φ]
    {A : Set X} (hA : MeasurableSet A) (hφA : 0 < φ A)
    (h : ∀ B, MeasurableSet B → B ⊆ A → 0 < φ B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B) :
    ∃ C ⊆ A, MeasurableSet C ∧ 0 < φ C ∧ ∃ m, 0 < m ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ x ∈ C, δ • φ.restrict C ≤ (P ^ m) x := by
  obtain ⟨n, m, k, hnmk⟩ := exists_densLevel_not_ae_zero P φ hA hφA h
  obtain ⟨E, D, hEA, hDA, hEm, hDm, hEpos, hDpos, ε, hε, hF⟩ :=
    exists_rect_of_not_ae_zero φ hA (measurableSet_densLevel P φ n k)
      (measurableSet_densLevel P φ m k) hnmk
  set η : ℝ≥0∞ := ((k : ℝ≥0∞) + 1)⁻¹ with hη
  have hη0 : 0 < η := ENNReal.inv_pos.2 (by simp)
  -- step 1: `P^{n+m+2}(x, ·) ≥ η² ε φ(· ∩ D)` on `E`, as in (5.24)
  have hstep : ∀ x ∈ E, (η * η * ε) • φ.restrict D ≤ (P ^ ((n + 1) + (m + 1))) x := by
    intro x hx
    refine Measure.le_intro fun B hB _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
      Kernel.pow_add_apply_eq_lintegral P (n + 1) (m + 1) x hB]
    set W : Set (X × X) :=
      {q | (x, q.2) ∈ densLevel P φ n k ∧ (q.2, q.1) ∈ densLevel P φ m k} with hW
    have hWm : MeasurableSet W :=
      ((measurable_const.prodMk measurable_snd) (measurableSet_densLevel P φ n k)).inter
        ((measurable_snd.prodMk measurable_fst) (measurableSet_densLevel P φ m k))
    have hsec : ∀ z, ∫⁻ y, W.indicator (fun _ => η * η) (z, y) ∂φ =
        η * η * φ (Prod.mk x ⁻¹' densLevel P φ n k ∩
          (fun y => (y, z)) ⁻¹' densLevel P φ m k) := fun z => by
      have hfun : (fun y => W.indicator (fun _ => η * η) (z, y)) =
          (Prod.mk z ⁻¹' W).indicator (fun _ => η * η) := by
        ext y
        by_cases hy : (z, y) ∈ W <;> simp [hy]
      rw [hfun, lintegral_indicator_const (measurable_prodMk_left hWm)]
      rfl
    have hpt : ∀ z y, W.indicator (fun _ => η * η) (z, y) ≤
        transDensity P φ (n + 1) x y * transDensity P φ (m + 1) y z := fun z y => by
      by_cases hq : (z, y) ∈ W
      · rw [indicator_of_mem hq]
        exact mul_le_mul' hq.1 hq.2
      · rw [indicator_of_notMem hq]
        exact zero_le
    have hmeasW : Measurable (Function.uncurry fun z y => W.indicator (fun _ => η * η) (z, y)) :=
      measurable_const.indicator hWm
    calc η * η * ε * φ (B ∩ D) = ∫⁻ _ in B ∩ D, η * η * ε ∂φ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in B ∩ D, ∫⁻ y, W.indicator (fun _ => η * η) (z, y) ∂φ ∂φ := by
          refine setLIntegral_mono' (hB.inter hDm) fun z hz => ?_
          rw [hsec z]
          gcongr
          exact hF x hx z hz.2
      _ = ∫⁻ y, ∫⁻ z in B ∩ D, W.indicator (fun _ => η * η) (z, y) ∂φ ∂φ :=
          lintegral_lintegral_swap hmeasW.aemeasurable
      _ ≤ ∫⁻ y, transDensity P φ (n + 1) x y * (P ^ (m + 1)) y B ∂φ := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ z in B ∩ D, W.indicator (fun _ => η * η) (z, y) ∂φ
              ≤ ∫⁻ z in B ∩ D, transDensity P φ (n + 1) x y *
                  transDensity P φ (m + 1) y z ∂φ := lintegral_mono fun z => hpt z y
            _ = transDensity P φ (n + 1) x y *
                  ∫⁻ z in B ∩ D, transDensity P φ (m + 1) y z ∂φ :=
                lintegral_const_mul _ ((measurable_transDensity P φ (m + 1)).comp
                  (measurable_const.prodMk measurable_id))
            _ ≤ transDensity P φ (n + 1) x y * ∫⁻ z in B, transDensity P φ (m + 1) y z ∂φ := by
                gcongr
                exact inter_subset_left
            _ ≤ transDensity P φ (n + 1) x y * (P ^ (m + 1)) y B := by
                gcongr
                exact setLIntegral_transDensity_le P φ (m + 1) y hB
      _ ≤ ∫⁻ y, (P ^ (m + 1)) y B ∂(P ^ (n + 1)) x :=
          lintegral_transDensity_mul_le P φ (n + 1) x (Kernel.measurable_coe _ hB)
  -- step 2: pass from `E` to a subset `C` of `D` from which `E` is reached
  have hreach : ∀ z ∈ D, ∃ k', ∃ j : ℕ, (j : ℝ≥0∞)⁻¹ ≤ (P ^ (k' + 1)) z E := fun z hz => by
    obtain ⟨k', hk'⟩ := h E hEm hEA hEpos z (hDA hz)
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hk'.ne'
    exact ⟨k', j, hj.le⟩
  set Cs : ℕ → ℕ → Set X := fun k' j => D ∩ {z | (j : ℝ≥0∞)⁻¹ ≤ (P ^ (k' + 1)) z E}
  have hcov : D ⊆ ⋃ k', ⋃ j, Cs k' j := fun z hz => by
    obtain ⟨k', j, hj⟩ := hreach z hz
    exact mem_iUnion.2 ⟨k', mem_iUnion.2 ⟨j, hz, hj⟩⟩
  obtain ⟨k', hk'⟩ := exists_measure_pos_of_iUnion (hDpos.trans_le (measure_mono hcov))
  obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion hk'
  have hCm : MeasurableSet (Cs k' j) :=
    hDm.inter (measurableSet_le measurable_const (Kernel.measurable_coe _ hEm))
  refine ⟨Cs k' j, fun z hz => hDA hz.1, hCm, hj, (k' + 1) + ((n + 1) + (m + 1)), by omega,
    (j : ℝ≥0∞)⁻¹ * (η * η * ε), ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (by simp))
      (ENNReal.mul_pos (ENNReal.mul_pos hη0.ne' hη0.ne').ne' hε.ne').ne', fun x hx => ?_⟩
  refine le_trans ?_ (smul_le_pow_add_of_le P hstep x)
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, Measure.restrict_apply hB, Measure.restrict_apply hB, mul_assoc]
  gcongr
  · exact hx.2
  · exact inter_subset_left

/-- **(5.16)**, density form: under the conclusion of Theorem 5.2.1, for every `x ∈ C` the
density of `Pᵐ(x, ·)` with respect to `φ` is at least `δ` at `φ`-almost every `y ∈ C`. -/
theorem theorem_5_2_1_density_ge (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsFiniteMeasure φ] {C : Set X} (hC : MeasurableSet C) {m : ℕ} {δ : ℝ≥0∞} {x : X}
    (hx : δ • φ.restrict C ≤ (P ^ m) x) : ∀ᵐ y ∂φ.restrict C, δ ≤ transDensity P φ m x y := by
  obtain ⟨-, hdec⟩ := theorem_5_2_1_density P φ m
  obtain ⟨Q, hQ, hQB⟩ := hdec x
  obtain ⟨S, hSm, hQS, hφS⟩ := hQ
  have hmeas : Measurable fun y => transDensity P φ m x y := Kernel.measurable_rnDeriv_right _ _ x
  -- the bad set inside `C ∩ S`, where the singular part vanishes
  set Bad := C ∩ S ∩ {y | transDensity P φ m x y < δ} with hBad
  have hBadm : MeasurableSet Bad :=
    (hC.inter hSm).inter (measurableSet_lt hmeas measurable_const)
  have hBad0 : φ Bad = 0 := by
    by_contra hpos
    have h1 := hx Bad
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hBadm,
      inter_eq_left.2 (fun y hy => hy.1.1), hQB Bad hBadm,
      measure_mono_null (fun y hy => hy.1.2) hQS, add_zero] at h1
    have hfin : ∫⁻ y in Bad, transDensity P φ m x y ∂φ ≠ ∞ := by
      have := isMarkovKernel_pow P m
      exact ne_top_of_le_ne_top (measure_ne_top ((P ^ m) x) Bad)
        (setLIntegral_transDensity_le P φ m x hBadm)
    have h2 : ∫⁻ y in Bad, transDensity P φ m x y ∂φ < ∫⁻ _ in Bad, δ ∂φ :=
      setLIntegral_strict_mono hBadm hpos measurable_const hfin
        (Filter.Eventually.of_forall fun y hy => hy.2)
    rw [setLIntegral_const] at h2
    exact absurd h1 (not_le.2 h2)
  have hS' : ∀ᵐ y ∂φ, y ∈ S := mem_ae_iff.2 hφS
  filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hS',
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hBad0)] with y hyC hyS hyB
  by_contra hlt
  push Not at hlt
  exact hyB ⟨⟨hyC, hyS⟩, hlt⟩

/-! ### Theorems 5.2.2 and 5.2.3 -/

/-- **Theorem 5.2.2** (MT p. 105). Let `B(X)` be countably generated and `ψ` a maximal
irreducibility measure. Every `A ∈ B⁺(X)` contains a `νₘ`-small set `C ∈ B⁺(X)` with
`νₘ(C) > 0`. -/
theorem theorem_5_2_2 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hψA : 0 < ψ A) :
    ∃ C ⊆ A, ∃ m ν, IsSmallSet P m ν C ∧ 0 < ψ C ∧ 0 < ν C := by
  obtain ⟨ψ', hψ', hprob, hψψ', -⟩ := theorem_4_0_1 P hψ.2.1 hψ.1
  obtain ⟨h1, h2⟩ := hψ.equiv hψ'
  have hψ'A : 0 < ψ' A := pos_iff_ne_zero.2 fun h0 => hψA.ne' (h1 h0)
  have hyp : ∀ B, MeasurableSet B → B ⊆ A → 0 < ψ' B → ∀ x ∈ A, ∃ k, 0 < (P ^ (k + 1)) x B :=
    fun B hB _ hpos x _ => (hitProb_pos_iff P hB x).1 (hψ'.2.1 B hB hpos x)
  obtain ⟨C, hCA, hCm, hψ'C, m, hm, δ, hδ, hC⟩ := theorem_5_2_1 P ψ' hA hψ'A hyp
  have hνC : 0 < (δ • ψ'.restrict C) C := by
    rw [Measure.smul_apply, Measure.restrict_apply hCm, inter_self, smul_eq_mul]
    exact ENNReal.mul_pos hδ.ne' hψ'C.ne'
  refine ⟨C, hCA, m, δ • ψ'.restrict C, ⟨hCm, hm, fun h0 => ?_, hC⟩,
    pos_iff_ne_zero.2 fun h0 => hψ'C.ne' (h2 h0), hνC⟩
  rw [h0] at hνC
  exact lt_irrefl _ hνC

/-- **Theorem 5.2.3** (MT p. 105), skeleton form. For a `ψ`-irreducible chain on a countably
generated space, the minorization condition (5.2) holds for some `m`-skeleton `Pᵐ`, on a set
`C ∈ B⁺(X)` and with `ν(Cᶜ) = 0`. -/
theorem theorem_5_2_3 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ m, 0 < m ∧ ∃ M : Minorization (P ^ m), M.IsConcentrated ∧ 0 < ψ M.C := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  exact ⟨m, hC.2.1, hC.minorization hνC, hC.minorization_isConcentrated hνC, hψC⟩

omit [MeasurableSpace.CountablyGenerated X] in
/-- The resolvent dominates its terms: `K_{a_ε}(x, ·) ≥ (1 − ε) εᵐ Pᵐ(x, ·)`. -/
theorem smul_pow_le_resolvent (P : Kernel X X) (ε : ℝ≥0∞) (m : ℕ) (x : X) :
    ((1 - ε) * ε ^ m) • (P ^ m) x ≤ resolvent P ε x :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul, resolvent_apply P ε x hB, mul_assoc]
    gcongr
    exact ENNReal.le_tsum (f := fun i => ε ^ i * (P ^ i) x B) m

/-- **Theorem 5.2.3** (MT p. 105), resolvent form: for `0 < ε < 1` the minorization condition
(5.2) holds for the `K_{a_ε}`-chain, on a set `C ∈ B⁺(X)` and with `ν(Cᶜ) = 0`. -/
theorem theorem_5_2_3_resolvent (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1) :
    haveI := isMarkovKernel_resolvent P hε1
    ∃ M : Minorization (resolvent P ε), M.IsConcentrated ∧ 0 < ψ M.C := by
  have := isMarkovKernel_resolvent P hε1
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hc : 0 < (1 - ε) * ε ^ m :=
    ENNReal.mul_pos (tsub_pos_of_lt hε1).ne' (pow_ne_zero _ hε0.ne')
  have hle : ∀ x ∈ C, ((1 - ε) * ε ^ m) • ν ≤ resolvent P ε x := fun x hx => by
    refine le_trans ?_ (smul_pow_le_resolvent P ε m x)
    refine Measure.le_intro fun B _ _ => ?_
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
    exact hC.2.2.2 x hx
  have hpos : 0 < (((1 - ε) * ε ^ m) • ν) C := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc.ne' hνC.ne'
  have hfin : (((1 - ε) * ε ^ m) • ν) C ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx C).trans prob_le_one)
  exact ⟨Minorization.ofLe hC.1 hle hpos hfin, Minorization.ofLe_isConcentrated _ _ _ _, hψC⟩

/-- **Proposition 5.2.4 (ii)** (MT p. 106). For a `ψ`-irreducible chain on a countably generated
space, `X` is a countable union of small sets: with `C` the small set of Theorem 5.2.2, the sets
`C̄(n, j) = {y : Pⁿ⁺¹(y, C) ≥ (j + 1)⁻¹}` of (5.27) are small and cover `X`. -/
theorem proposition_5_2_4_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ Cs : ℕ → ℕ → Set X, (∀ n j, IsSmall P (Cs n j)) ∧ ⋃ n, ⋃ j, Cs n j = univ := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  refine ⟨fun n j => {y | ((j : ℝ≥0∞) + 1)⁻¹ ≤ (P ^ (n + 1)) y C}, fun n j => ?_, ?_⟩
  · exact ⟨(n + 1) + m, _, proposition_5_2_4_i P hC
      (measurableSet_le measurable_const (Kernel.measurable_coe _ hC.1))
      (ENNReal.inv_pos.2 (by simp)) fun x hx => hx⟩
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P hC.1 y).1 (hψ.2.1 C hC.1 hψC y)
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hn.ne'
    refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨j, ?_⟩⟩
    refine le_trans ?_ hj.le
    gcongr
    exact le_self_add

end MeynTweedie.Positivity
