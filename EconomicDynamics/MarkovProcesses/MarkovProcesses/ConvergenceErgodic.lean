/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.GeneralKernels
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Invariant sets, ergodic measures and Theorem 3.3.4

Miao, §3.3.2, pp. 111–112.

* **Definition 3.3.5**: `P`-invariant sets (`IsPInvariantSet`) and ergodic measures
  (`IsErgodicMeasure`). The book's definition of an *ergodic set* (`IsErgodicSetBook`: `E` with
  `P(x, E) = 1` for `π`-a.e. `x ∈ E` and no proper subset with this property) is defective: `∅`
  has the property vacuously and is a proper subset of every nonempty set, so the only ergodic
  set is `∅` (`definition_3_3_5_ergodicSet_eq_empty`).
* The example on p. 111: for `P(0, ·) = δ₀`, `P(1, ·) = δ₁` every probability measure is invariant
  (`example_p111_invariant`), and `π` is ergodic iff `π{0} ∈ {0, 1}`, so `δ₀` and `δ₁` are the
  ergodic measures (`example_p111_ergodic`). (The book calls `{0}` "a `δ{0}`-invariant set";
  invariance of a set refers to `P`, and `{0}`, `{1}` are `P`-invariant.)
* **Theorem 3.3.4** (the book refers to the Birkhoff theorem of Chapter 4). Proved here directly:
  - `I` is convex (`theorem_3_3_4_convex`);
  - `E` is the set of extreme points of `I` (`theorem_3_3_4_extreme`). If `A` is invariant with
    `0 < π(A) < 1`, `π` is the average of its normalised restrictions to `A` and `Aᶜ`, both
    invariant. Conversely, if `π` is ergodic and `π = aπ₁ + bπ₂`, the density `h = dπ₁/dπ` has
    `{h > 1}` invariant up to a `π`-null set (`gp_ae_invariant_of_density`, comparing `π₁` with the
    invariant measure with density `min(h, 1)`), hence it contains an invariant set of the same
    measure (`gp_exists_invariantSet`); ergodicity forces `h = 1`;
  - distinct ergodic measures are mutually singular (`theorem_3_3_4_singular`), by the same
    argument applied to `π₁` and `(π₁ + π₂)/2`.
  - "Every invariant measure is a convex combination of ergodic measures" is false for finite
    convex combinations: for `P(x, ·) = δₓ` on `ℝ` the uniform distribution on `[0, 1]` is
    invariant but is no finite combination of ergodic measures
    (`theorem_3_3_4_combination_counterexample`). The correct statement is the ergodic
    decomposition (an integral over ergodic measures, for standard Borel spaces), which is not
    formalised here.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A **`P`-invariant set** (Miao, Definition 3.3.5, p. 111): `P(x, A) = 1` for every `x ∈ A`. -/
def IsPInvariantSet (κ : Kernel X X) (A : Set X) : Prop :=
  MeasurableSet A ∧ ∀ x ∈ A, κ x A = 1

/-- An **ergodic** invariant measure (Miao, Definition 3.3.5, p. 111): `π(A) ∈ {0, 1}` for every
`P`-invariant set `A`. -/
def IsErgodicMeasure (κ : Kernel X X) (π : Measure X) : Prop :=
  IsInvariantDist κ π ∧ ∀ A, IsPInvariantSet κ A → π A = 0 ∨ π A = 1

/-- The book's **ergodic set** (Miao, Definition 3.3.5, p. 111), literally: `P(x, E) = 1` for
`π`-a.e. `x ∈ E`, and no proper subset of `E` has this property. -/
def IsErgodicSetBook (κ : Kernel X X) (π : Measure X) (E : Set X) : Prop :=
  MeasurableSet E ∧ (∀ᵐ x ∂π, x ∈ E → κ x E = 1) ∧
    ∀ F, F ⊂ E → MeasurableSet F → ¬ ∀ᵐ x ∂π, x ∈ F → κ x F = 1

/-- **Definition 3.3.5** (Miao, p. 111) is defective: the empty set has the defining property
and is a proper subset of every nonempty set, so the only "ergodic set" is `∅`. -/
theorem definition_3_3_5_ergodicSet_eq_empty {κ : Kernel X X} {π : Measure X} {E : Set X}
    (h : IsErgodicSetBook κ π E) : E = ∅ := by
  by_contra hE
  exact h.2.2 ∅ (Set.empty_ssubset.2 (Set.nonempty_iff_ne_empty.2 hE)) MeasurableSet.empty
    (ae_of_all _ fun x hx => absurd hx (Set.notMem_empty x))

/-- Miao, p. 111: for `P(0, ·) = δ₀`, `P(1, ·) = δ₁` (the identity kernel on `{0, 1}`) every
probability measure is invariant. -/
theorem example_p111_invariant (π : Measure (Fin 2)) [IsProbabilityMeasure π] :
    IsInvariantDist Kernel.id π :=
  ⟨inferInstance, (gp_adjointOp_iterate (Kernel.id : Kernel (Fin 2) (Fin 2)) 0 π).symm⟩

/-- Miao, pp. 111–112: for the identity kernel on `{0, 1}`, `π` is ergodic iff `π{0} = 0` or
`π{0} = 1`; so `δ₀` and `δ₁` are the ergodic measures, and `π = pδ₀ + (1 − p)δ₁` is ergodic only
for `p ∈ {0, 1}`. -/
theorem example_p111_ergodic (π : Measure (Fin 2)) [IsProbabilityMeasure π] :
    IsErgodicMeasure Kernel.id π ↔ π {0} = 0 ∨ π {0} = 1 := by
  constructor
  · rintro ⟨-, h⟩
    exact h {0} ⟨MeasurableSet.singleton 0, fun x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx; simp [Kernel.id_apply]⟩
  · intro h0
    refine ⟨example_p111_invariant π, fun A _ => ?_⟩
    have h1 : π {1} = 1 - π {0} := by
      rw [← prob_compl_eq_one_sub (MeasurableSet.singleton 0)]
      congr 1
      ext x; fin_cases x <;> simp
    have hd : ∀ y : Fin 2, π {y} = 1 → π = Measure.dirac y := fun y hy => by
      rw [Measure.ext_iff_singleton]
      intro a
      by_cases ha : a = y
      · subst ha; simp [hy]
      · have : π {a} = 0 := by
          refine le_antisymm ?_ zero_le
          have := prob_add_prob_compl (μ := π) (MeasurableSet.singleton y)
          rw [hy] at this
          calc π {a} ≤ π {y}ᶜ :=
              measure_mono (Set.singleton_subset_iff.2 (Set.mem_compl_singleton_iff.2 ha))
            _ = 0 := by
              have h2 : (1 : ℝ≥0∞) + π {y}ᶜ = 1 + 0 := by rw [this, add_zero]
              exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h2
        rw [this, Measure.dirac_apply' _ (MeasurableSet.singleton a),
          Set.indicator_of_notMem (Set.notMem_singleton_iff.2 (Ne.symm ha))]
    have hA : ∀ y : Fin 2, (Measure.dirac y) A = 0 ∨ (Measure.dirac y) A = 1 := fun y => by
      by_cases hy : y ∈ A
      · exact Or.inr (Measure.dirac_apply_of_mem hy)
      · left; simp [Measure.dirac_apply' _ (MeasurableSet.of_discrete), hy]
    rcases h0 with h0 | h0
    · rw [hd 1 (by rw [h1, h0, tsub_zero])]; exact hA 1
    · rw [hd 0 h0]; exact hA 0

/-- `T*` is affine: `T*(aμ + bν) = aT*μ + bT*ν`. -/
theorem gp_adjointOp_add_smul (κ : Kernel X X) (μ ν : Measure X) (a b : ℝ≥0∞) :
    adjointOp κ (a • μ + b • ν) = a • adjointOp κ μ + b • adjointOp κ ν := by
  ext A hA
  simp only [gp_adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

/-- `T*(cμ) = cT*μ`. -/
theorem gp_adjointOp_smul (κ : Kernel X X) (μ : Measure X) (c : ℝ≥0∞) :
    adjointOp κ (c • μ) = c • adjointOp κ μ := by
  ext A hA
  simp only [gp_adjointOp_apply κ _ hA, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_smul_measure]
  rfl

/-- **Theorem 3.3.4** (Miao, p. 112): the set `I` of invariant probability measures is convex. -/
theorem theorem_3_3_4_convex (κ : Kernel X X) :
    Convex ℝ≥0∞ {π : Measure X | IsInvariantDist κ π} := by
  rintro π₁ ⟨h₁, e₁⟩ π₂ ⟨h₂, e₂⟩ a b - - hab
  refine ⟨⟨?_⟩, ?_⟩
  · simp [hab]
  · rw [gp_adjointOp_add_smul, e₁, e₂]

/-- `T*(μ.withDensity f)(A) = ∫ f(x) P(x, A) μ(dx)`. -/
theorem gp_adjointOp_withDensity (κ : Kernel X X) (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) {A : Set X} (hA : MeasurableSet A) :
    adjointOp κ (μ.withDensity f) A = ∫⁻ x, f x * κ x A ∂μ := by
  rw [gp_adjointOp_apply κ _ hA, lintegral_withDensity_eq_lintegral_mul _ hf (κ.measurable_coe hA)]
  rfl

/-- If a measurable `f ≤ 1` has `∫ f dμ = 1` for a probability measure `μ`, then `f = 1`
`μ`-a.e. -/
theorem gp_ae_eq_one_of_lintegral {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) (h1 : ∀ x, f x ≤ 1) (hint : ∫⁻ x, f x ∂μ = 1) : ∀ᵐ x ∂μ, f x = 1 := by
  have h0 : ∫⁻ x, (1 - f x) ∂μ = 0 := by
    rw [lintegral_sub hf (by rw [hint]; exact ENNReal.one_ne_top) (ae_of_all _ h1), hint]
    simp
  replace h0 := (lintegral_eq_zero_iff (f := fun x => 1 - f x) (measurable_const.sub hf)).1 h0
  filter_upwards [h0] with x hx
  exact le_antisymm (h1 x) (tsub_eq_zero_iff_le.1 hx)

/-- A set that is invariant up to a null set of an invariant `π` contains an invariant set of the
same `π`-measure: if `P(x, B) = 1` for `π`-a.e. `x ∈ B`, then
`B' = {x : Pⁿ(x, B) = 1 for all n}` is `P`-invariant, `B' ⊆ B` and `π(B \ B') = 0`. -/
theorem gp_exists_invariantSet (κ : Kernel X X) [IsMarkovKernel κ] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : adjointOp κ π = π) {B : Set X} (hB : MeasurableSet B)
    (hae : ∀ᵐ x ∂π, x ∈ B → κ x B = 1) :
    ∃ B', B' ⊆ B ∧ IsPInvariantSet κ B' ∧ π (B \ B') = 0 := by
  set Bn : ℕ → Set X := fun n => {x | kpow κ n x B = 1}
  have hBn : ∀ n, MeasurableSet (Bn n) := fun n =>
    (Kernel.measurable_coe (kpow κ n) hB) (measurableSet_singleton 1)
  have hB0 : Bn 0 = B := by
    ext x
    by_cases hx : x ∈ B <;> simp [Bn, kpow, Kernel.id_apply, Measure.dirac_apply' _ hB, hx]
  have hstep : ∀ n x, kpow κ (n + 1) x B = ∫⁻ y, kpow κ n y B ∂κ x := fun n x => by
    rw [eq_3_5 κ n 1 x hB, gp_kpow_one]
  have hmk : ∀ n, IsMarkovKernel (kpow κ n) := theorem_3_2_5 κ
  refine ⟨⋂ n, Bn n, fun x hx => hB0 ▸ Set.mem_iInter.1 hx 0, ⟨MeasurableSet.iInter hBn,
    fun x hx => ?_⟩, ?_⟩
  · -- invariance
    have hc : ∀ n, κ x (Bn n)ᶜ = 0 := fun n => by
      have h1 : ∫⁻ y, kpow κ n y B ∂κ x = 1 := by
        rw [← hstep]; exact Set.mem_iInter.1 hx (n + 1)
      have := gp_ae_eq_one_of_lintegral (μ := κ x) (Kernel.measurable_coe _ hB)
        (fun y => prob_le_one) h1
      rw [ae_iff] at this
      exact this
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iInter hBn), Set.compl_iInter]
    exact measure_iUnion_null hc
  · -- `π(B \ B') = 0`
    have hnull : ∀ n, π (B \ Bn n) = 0 := by
      intro n
      induction n with
      | zero => rw [hB0, Set.sdiff_self, measure_empty]
      | succ n ih =>
        set N := B \ Bn n
        have hN : MeasurableSet N := hB.diff (hBn n)
        have hκN : ∀ᵐ x ∂π, κ x N = 0 := by
          have : ∫⁻ x, κ x N ∂π = 0 := by rw [← gp_adjointOp_apply κ π hN, hπ, ih]
          exact (lintegral_eq_zero_iff (κ.measurable_coe hN)).1 this
        have hgood : ∀ᵐ x ∂π, x ∈ B → x ∈ Bn (n + 1) := by
          filter_upwards [hae, hκN] with x hx1 hx2 hxB
          have hBN : κ x (B \ N) = 1 := by rw [measure_sdiff_null hx2, hx1 hxB]
          refine le_antisymm prob_le_one ?_
          rw [hstep, ← hBN, ← lintegral_indicator_one (hB.diff hN)]
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ B \ N
          · rw [Set.indicator_of_mem hy, Pi.one_apply]
            have : y ∈ Bn n := by
              by_contra hyn
              exact hy.2 ⟨hy.1, hyn⟩
            exact le_of_eq this.symm
          · rw [Set.indicator_of_notMem hy]; exact zero_le
        rw [ae_iff] at hgood
        refine le_antisymm (le_of_eq_of_le ?_ hgood.le) zero_le
        congr 1
        ext x
        simp
    rw [Set.sdiff_iInter]
    exact measure_iUnion_null hnull

/-- If `π` and `π.withDensity h` are invariant (the latter finite), the set `{h > 1}` is
invariant up to a `π`-null set. The invariant measure with density `min(h, 1)` is subinvariant,
hence invariant, so the measure with density `h − min(h, 1)`, which lives on `{h > 1}`, is
invariant too. -/
theorem gp_ae_invariant_of_density (κ : Kernel X X) [IsMarkovKernel κ] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : adjointOp κ π = π) {h : X → ℝ≥0∞} (hh : Measurable h)
    (hπ₁ : adjointOp κ (π.withDensity h) = π.withDensity h) :
    ∀ᵐ x ∂π, x ∈ {x | 1 < h x} → κ x {x | 1 < h x} = 1 := by
  set B := {x | 1 < h x}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hh
  set g : X → ℝ≥0∞ := fun x => min (h x) 1
  have hg : Measurable g := hh.min measurable_const
  set ρ := π.withDensity g
  set D := {x | h x ≤ 1}
  have hD : MeasurableSet D := measurableSet_le hh measurable_const
  have hgh : ∀ x, g x ≤ h x := fun x => min_le_left _ _
  have hhg : Measurable fun x => h x - g x := hh.sub hg
  have hg1 : ∀ x, g x ≤ 1 := fun x => min_le_right _ _
  have hρfin : ∀ A, ρ A ≠ ∞ := fun A => by
    refine ne_top_of_le_ne_top (measure_ne_top π Set.univ) ?_
    calc ρ A ≤ ρ Set.univ := measure_mono (Set.subset_univ A)
      _ = ∫⁻ x, g x ∂π := by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono hg1
      _ = π Set.univ := by simp
  -- Step 1: `T*ρ ≤ ρ`
  have hsub : ∀ A, MeasurableSet A → adjointOp κ ρ A ≤ ρ A := by
    intro A hA
    have h1 : adjointOp κ ρ (A ∩ D) ≤ ρ (A ∩ D) := by
      calc adjointOp κ ρ (A ∩ D) = ∫⁻ x, g x * κ x (A ∩ D) ∂π :=
            gp_adjointOp_withDensity κ π hg (hA.inter hD)
        _ ≤ ∫⁻ x, h x * κ x (A ∩ D) ∂π := lintegral_mono fun x => mul_le_mul_left (hgh x) _
        _ = π.withDensity h (A ∩ D) := by
            rw [← gp_adjointOp_withDensity κ π hh (hA.inter hD), hπ₁]
        _ = ρ (A ∩ D) := by
            rw [withDensity_apply _ (hA.inter hD), withDensity_apply _ (hA.inter hD)]
            refine setLIntegral_congr_fun (hA.inter hD) fun x hx => ?_
            exact (min_eq_left hx.2).symm
    have h2 : adjointOp κ ρ (A \ D) ≤ ρ (A \ D) := by
      calc adjointOp κ ρ (A \ D) = ∫⁻ x, g x * κ x (A \ D) ∂π :=
            gp_adjointOp_withDensity κ π hg (hA.diff hD)
        _ ≤ ∫⁻ x, κ x (A \ D) ∂π := lintegral_mono fun x => by
            calc g x * κ x (A \ D) ≤ 1 * κ x (A \ D) := mul_le_mul_left (hg1 x) _
              _ = κ x (A \ D) := one_mul _
        _ = π (A \ D) := by rw [← gp_adjointOp_apply κ π (hA.diff hD), hπ]
        _ = ρ (A \ D) := by
            rw [withDensity_apply _ (hA.diff hD), ← setLIntegral_one]
            refine setLIntegral_congr_fun (hA.diff hD) fun x hx => ?_
            have : 1 < h x := lt_of_not_ge hx.2
            exact (min_eq_right this.le).symm
    calc adjointOp κ ρ A = adjointOp κ ρ (A ∩ D) + adjointOp κ ρ (A \ D) :=
          (measure_inter_add_sdiff A hD).symm
      _ ≤ ρ (A ∩ D) + ρ (A \ D) := add_le_add h1 h2
      _ = ρ A := measure_inter_add_sdiff A hD
  -- Step 2: `T*ρ = ρ`
  have hρuniv : adjointOp κ ρ Set.univ = ρ Set.univ := by
    rw [gp_adjointOp_withDensity κ π hg MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    simp
  have hinv : ∀ A, MeasurableSet A → adjointOp κ ρ A = ρ A := by
    intro A hA
    refine le_antisymm (hsub A hA) ?_
    have e1 := measure_add_measure_compl (μ := ρ) hA
    have e2 := measure_add_measure_compl (μ := adjointOp κ ρ) hA
    rw [hρuniv, ← e1] at e2
    refine ENNReal.le_of_add_le_add_right (hρfin Aᶜ) ?_
    calc ρ A + ρ Aᶜ = adjointOp κ ρ A + adjointOp κ ρ Aᶜ := e2.symm
      _ ≤ adjointOp κ ρ A + ρ Aᶜ := add_le_add le_rfl (hsub Aᶜ hA.compl)
  -- Step 3: the measure `σ` with density `h - g` is invariant on `Bᶜ`
  have hsplit : ∀ A, MeasurableSet A →
      π.withDensity h A = π.withDensity (fun x => h x - g x) A + ρ A := fun A hA => by
    rw [withDensity_apply _ hA, withDensity_apply _ hA, withDensity_apply _ hA,
      ← lintegral_add_right _ hg]
    exact lintegral_congr fun x => (tsub_add_cancel_of_le (hgh x)).symm
  have hσ : adjointOp κ (π.withDensity fun x => h x - g x) Bᶜ =
      π.withDensity (fun x => h x - g x) Bᶜ := by
    have hm2 : Measurable fun x => g x * κ x Bᶜ := hg.mul (κ.measurable_coe hB.compl)
    have e : adjointOp κ (π.withDensity h) Bᶜ =
        adjointOp κ (π.withDensity fun x => h x - g x) Bᶜ + adjointOp κ ρ Bᶜ := by
      rw [gp_adjointOp_withDensity κ π hh hB.compl,
        gp_adjointOp_withDensity κ π hhg hB.compl,
        gp_adjointOp_withDensity κ π hg hB.compl, ← lintegral_add_right _ hm2]
      refine lintegral_congr fun x => ?_
      rw [← add_mul, tsub_add_cancel_of_le (hgh x)]
    rw [hπ₁, hsplit _ hB.compl, hinv _ hB.compl] at e
    exact ((ENNReal.add_left_inj (hρfin _)).1 e).symm
  -- Step 4: `σ(Bᶜ) = 0`, so `P(x, Bᶜ) = 0` for `π`-a.e. `x ∈ B`
  have hσ0 : π.withDensity (fun x => h x - g x) Bᶜ = 0 := by
    rw [withDensity_apply _ hB.compl]
    refine (setLIntegral_congr_fun hB.compl fun x hx => ?_).trans (lintegral_zero)
    have hx' : h x ≤ 1 := not_lt.1 hx
    simp [g, min_eq_left hx']
  rw [← hσ, gp_adjointOp_withDensity κ π hhg hB.compl,
    lintegral_eq_zero_iff (f := fun x => (h x - g x) * κ x Bᶜ)
      (hhg.mul (κ.measurable_coe hB.compl))] at hσ0
  filter_upwards [hσ0] with x hx hxB
  have hpos : h x - g x ≠ 0 := by
    have : 1 < h x := hxB
    simp only [g, min_eq_right this.le]
    exact (tsub_pos_of_lt this).ne'
  have : κ x Bᶜ = 0 := (mul_eq_zero.1 hx).resolve_left hpos
  exact (prob_compl_eq_zero_iff hB).1 this

/-- The key lemma for Theorem 3.3.4. If `π` and `π₁ ≪ π` are invariant probability measures,
there is a `P`-invariant set `B'` (built from `{dπ₁/dπ > 1}`) with `π(B') ≠ 1` and such that
`π₁(B') = 0` forces `π₁ = π`. -/
theorem gp_density_invariantSet (κ : Kernel X X) [IsMarkovKernel κ] {π π₁ : Measure X}
    [IsProbabilityMeasure π] [IsProbabilityMeasure π₁] (hπ : adjointOp κ π = π)
    (hπ₁ : adjointOp κ π₁ = π₁) (hac : π₁ ≪ π) :
    ∃ B', IsPInvariantSet κ B' ∧ (π₁ B' = 0 → π₁ = π) ∧ π B' ≠ 1 := by
  set h := π₁.rnDeriv π
  have hh : Measurable h := Measure.measurable_rnDeriv _ _
  have hπ1eq : π.withDensity h = π₁ := Measure.withDensity_rnDeriv_eq _ _ hac
  have hint : ∫⁻ x, h x ∂π = 1 := by
    rw [← Measure.restrict_univ (μ := π), ← withDensity_apply _ MeasurableSet.univ, hπ1eq,
      measure_univ]
  set B := {x | 1 < h x}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hh
  have hae := gp_ae_invariant_of_density κ hπ hh (by rw [hπ1eq]; exact hπ₁)
  obtain ⟨B', hB'B, hB'inv, hnull⟩ := gp_exists_invariantSet κ hπ hB hae
  refine ⟨B', hB'inv, fun h0 => ?_, fun h1 => ?_⟩
  · -- `π₁(B') = 0` gives `π(B) = 0`, so `h ≤ 1`, so `h = 1`
    have hπ₁B : π₁ B = 0 := by
      refine le_antisymm ?_ zero_le
      calc π₁ B ≤ π₁ (B \ B') + π₁ B' := by
            rw [← measure_union Set.disjoint_sdiff_left hB'inv.1, Set.sdiff_union_self]
            exact measure_mono Set.subset_union_left
        _ = 0 := by rw [hac hnull, h0, add_zero]
    have hπB : π B = 0 := by
      refine le_antisymm ?_ zero_le
      calc π B = ∫⁻ _ in B, 1 ∂π := by rw [setLIntegral_one]
        _ ≤ ∫⁻ x in B, h x ∂π := setLIntegral_mono hh fun x hx => le_of_lt hx
        _ = π₁ B := by rw [← withDensity_apply _ hB, hπ1eq]
        _ = 0 := hπ₁B
    have hle : ∀ᵐ x ∂π, h x ≤ 1 := by
      rw [ae_iff]
      simpa [B, not_le] using hπB
    have h0' : ∫⁻ x, (1 - h x) ∂π = 0 := by
      rw [lintegral_sub hh (by rw [hint]; exact ENNReal.one_ne_top) hle, hint]
      simp
    have hge := (lintegral_eq_zero_iff (f := fun x => 1 - h x) (measurable_const.sub hh)).1 h0'
    have heq : h =ᵐ[π] 1 := by
      filter_upwards [hle, hge] with x hx1 hx2
      exact le_antisymm hx1 (tsub_eq_zero_iff_le.1 hx2)
    rw [← hπ1eq, withDensity_congr_ae heq, withDensity_one]
  · -- `π(B') = 1` is impossible: `h > 1` a.e. contradicts `∫ h dπ = 1`
    have hπB : π Bᶜ = 0 := by
      have : π B = 1 := le_antisymm prob_le_one (h1 ▸ measure_mono hB'B)
      exact (prob_compl_eq_zero_iff hB).2 this
    have hgt : ∀ᵐ x ∂π, 1 < h x := by
      have e : {x | ¬ 1 < h x} = Bᶜ := by ext x; simp [B]
      rw [ae_iff, e]
      exact hπB
    have h0' : ∫⁻ x, (h x - 1) ∂π = 0 := by
      rw [lintegral_sub measurable_const (by simp) (hgt.mono fun x hx => hx.le), hint]
      simp
    have hle := (lintegral_eq_zero_iff (f := fun x => h x - 1) (hh.sub measurable_const)).1 h0'
    have hfalse : ∀ᵐ x ∂π, False := by
      filter_upwards [hgt, hle] with x hx1 hx2
      exact absurd (tsub_eq_zero_iff_le.1 hx2) (not_le.2 hx1)
    rw [ae_iff] at hfalse
    simp at hfalse

/-- **Theorem 3.3.4** (Miao, p. 112): the ergodic measures are exactly the extreme points of the
convex set `I` of invariant probability measures. -/
theorem theorem_3_3_4_extreme (κ : Kernel X X) [IsMarkovKernel κ] (π : Measure X) :
    IsErgodicMeasure κ π ↔ π ∈ Set.extremePoints ℝ≥0∞ {π : Measure X | IsInvariantDist κ π} := by
  constructor
  · rintro ⟨⟨hπp, hπ⟩, herg⟩
    refine mem_extremePoints.2 ⟨⟨hπp, hπ⟩, ?_⟩
    have key : ∀ π₁ : Measure X, IsInvariantDist κ π₁ → ∀ a b : ℝ≥0∞, 0 < a →
        ∀ π₂ : Measure X, a • π₁ + b • π₂ = π → π₁ = π := by
      rintro π₁ ⟨hp₁, hi₁⟩ a b ha π₂ hsum
      have hac : π₁ ≪ π := fun A hA => by
        have : a * π₁ A ≤ π A := by
          rw [← hsum, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
          exact le_self_add
        rw [hA, nonpos_iff_eq_zero, mul_eq_zero] at this
        exact this.resolve_left ha.ne'
      obtain ⟨B', hB', himp, hne⟩ := gp_density_invariantSet κ hπ hi₁ hac
      rcases herg B' hB' with h0 | h1
      · exact himp (hac h0)
      · exact absurd h1 hne
    intro π₁ h₁ π₂ h₂ ⟨a, b, ha, hb, hab, hsum⟩
    refine ⟨key π₁ h₁ a b ha π₂ hsum, key π₂ h₂ b a hb π₁ ?_⟩
    rw [add_comm]; exact hsum
  · intro hext
    obtain ⟨⟨hπp, hπ⟩, hext'⟩ := mem_extremePoints.1 hext
    refine ⟨⟨hπp, hπ⟩, fun A hA => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hA0, hA1⟩ := hcon
    have hAc0 : π Aᶜ ≠ 0 := fun h => hA1 ((prob_compl_eq_zero_iff hA.1).1 h)
    have hAc1 : π Aᶜ ≠ ∞ := measure_ne_top _ _
    have hAt : π A ≠ ∞ := measure_ne_top _ _
    -- the restrictions to `A` and `Aᶜ` are invariant
    have hzero : ∫⁻ x in Aᶜ, κ x A ∂π = 0 := by
      have e := lintegral_add_compl (fun x => κ x A) (μ := π) hA.1
      rw [← gp_adjointOp_apply κ π hA.1, hπ, setLIntegral_congr_fun hA.1 hA.2,
        setLIntegral_const, one_mul] at e
      have : π A + ∫⁻ x in Aᶜ, κ x A ∂π = π A + 0 := by rw [e, add_zero]
      exact (ENNReal.add_right_inj hAt).1 this
    have hresA : adjointOp κ (π.restrict A) = π.restrict A := by
      ext B hB
      rw [gp_adjointOp_apply κ _ hB, Measure.restrict_apply hB]
      have e1 : ∀ x ∈ A, κ x B = κ x (B ∩ A) := fun x hx => by
        have : κ x Aᶜ = 0 := (prob_compl_eq_zero_iff hA.1).2 (hA.2 x hx)
        rw [← measure_inter_add_sdiff B hA.1, Set.sdiff_eq,
          measure_mono_null Set.inter_subset_right this, add_zero]
      have e2 : ∫⁻ x in Aᶜ, κ x (B ∩ A) ∂π = 0 :=
        le_antisymm ((setLIntegral_mono (κ.measurable_coe hA.1) fun x _ =>
          measure_mono Set.inter_subset_right).trans hzero.le) zero_le
      have e3 := lintegral_add_compl (fun x => κ x (B ∩ A)) (μ := π) hA.1
      rw [e2, add_zero, ← gp_adjointOp_apply κ π (hB.inter hA.1), hπ] at e3
      rw [setLIntegral_congr_fun hA.1 e1, e3]
    have hresAc : adjointOp κ (π.restrict Aᶜ) = π.restrict Aᶜ := by
      have hadd : adjointOp κ π = adjointOp κ (π.restrict A) + adjointOp κ (π.restrict Aᶜ) := by
        have := gp_adjointOp_add_smul κ (π.restrict A) (π.restrict Aᶜ) 1 1
        rw [one_smul, one_smul, one_smul, one_smul, Measure.restrict_add_restrict_compl hA.1]
          at this
        exact this
      ext B hB
      have e := congrArg (fun μ : Measure X => μ B) hadd
      simp only [Measure.add_apply] at e
      rw [hπ, hresA] at e
      have e2 : π B = π.restrict A B + π.restrict Aᶜ B := by
        rw [← Measure.add_apply, Measure.restrict_add_restrict_compl hA.1]
      rw [e2] at e
      exact ((ENNReal.add_right_inj (measure_ne_top (π.restrict A) B)).1 e).symm
    set π₁ := (π A)⁻¹ • π.restrict A
    set π₂ := (π Aᶜ)⁻¹ • π.restrict Aᶜ
    have hp : ∀ (C : Set X), MeasurableSet C → π C ≠ 0 → π C ≠ ∞ →
        IsProbabilityMeasure ((π C)⁻¹ • π.restrict C) := fun C hC h0 ht => ⟨by
      rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]⟩
    have h₁ : IsInvariantDist κ π₁ :=
      ⟨hp A hA.1 hA0 hAt, by rw [gp_adjointOp_smul, hresA]⟩
    have h₂ : IsInvariantDist κ π₂ :=
      ⟨hp Aᶜ hA.1.compl hAc0 hAc1, by rw [gp_adjointOp_smul, hresAc]⟩
    have hseg : π ∈ openSegment ℝ≥0∞ π₁ π₂ := by
      refine ⟨π A, π Aᶜ, pos_iff_ne_zero.2 hA0, pos_iff_ne_zero.2 hAc0,
        by rw [measure_add_measure_compl hA.1, measure_univ], ?_⟩
      simp only [π₁, π₂, smul_smul, ENNReal.mul_inv_cancel hA0 hAt,
        ENNReal.mul_inv_cancel hAc0 hAc1, one_smul]
      exact Measure.restrict_add_restrict_compl hA.1
    have h1 := (hext' π₁ h₁ π₂ h₂ hseg).1
    have : π₁ A = 1 := by
      simp only [π₁, Measure.smul_apply, Measure.restrict_apply hA.1, Set.inter_self, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hA0 hAt
    exact hA1 (h1 ▸ this)

/-- **Theorem 3.3.4** (Miao, p. 112): two distinct ergodic measures are mutually singular. -/
theorem theorem_3_3_4_singular (κ : Kernel X X) [IsMarkovKernel κ] {π₁ π₂ : Measure X}
    (h₁ : IsErgodicMeasure κ π₁) (h₂ : IsErgodicMeasure κ π₂) (hne : π₁ ≠ π₂) :
    π₁ ⟂ₘ π₂ := by
  obtain ⟨⟨hp₁, hi₁⟩, he₁⟩ := h₁
  obtain ⟨⟨hp₂, hi₂⟩, he₂⟩ := h₂
  set π := (2⁻¹ : ℝ≥0∞) • π₁ + (2⁻¹ : ℝ≥0∞) • π₂
  have hhalf : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  have hπ : IsInvariantDist κ π :=
    theorem_3_3_4_convex κ ⟨hp₁, hi₁⟩ ⟨hp₂, hi₂⟩ (zero_le) (zero_le) hhalf
  obtain ⟨hπp, hπi⟩ := hπ
  have hac : π₁ ≪ π := fun A hA => by
    have : 2⁻¹ * π₁ A ≤ π A := by
      simp only [π, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact le_self_add
    rw [hA, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (by simp)
  obtain ⟨B', hB', himp, hne1⟩ := gp_density_invariantSet κ hπi hi₁ hac
  have hB'm := hB'.1
  rcases he₁ B' hB' with h0 | h1
  · exfalso
    have heq := himp h0
    refine hne ?_
    rw [heq]
    ext A hA
    have e : π A = 2⁻¹ * π A + 2⁻¹ * π₂ A := by
      conv_lhs => rw [show π = (2⁻¹ : ℝ≥0∞) • π₁ + (2⁻¹ : ℝ≥0∞) • π₂ from rfl]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [heq]
    have hfin : 2⁻¹ * π A ≠ ∞ := ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have e2 : 2⁻¹ * π A + 2⁻¹ * π A = 2⁻¹ * π A + 2⁻¹ * π₂ A := by
      rw [← add_mul, hhalf, one_mul]; exact e
    have e3 := (ENNReal.add_right_inj hfin).1 e2
    exact (ENNReal.mul_right_inj (by simp) (by simp)).1 e3
  · rcases he₂ B' hB' with h0' | h1'
    · exact ⟨B'ᶜ, hB'm.compl, (prob_compl_eq_zero_iff hB'm).2 h1, by rw [compl_compl]; exact h0'⟩
    · exfalso
      refine hne1 ?_
      simp only [π, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h1, h1', mul_one, hhalf]

/-- **Theorem 3.3.4** (Miao, p. 112): "every invariant measure is a convex combination of
ergodic measures" is false for finite convex combinations. For `P(x, ·) = δₓ` on `ℝ` the uniform
distribution on `[0, 1]` is invariant, but it is not `Σᵢ tᵢπᵢ` for any finitely many ergodic
`πᵢ`: every ergodic `πᵢ` gives mass `0` or `1` to every Borel set, so some interval
`[j/(n+1), (j+1)/(n+1))` is null for all of them. -/
theorem theorem_3_3_4_combination_counterexample :
    IsInvariantDist (Kernel.id : Kernel ℝ ℝ) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ¬ ∃ (n : ℕ) (t : Fin n → ℝ≥0∞) (πs : Fin n → Measure ℝ),
        (∀ i, IsErgodicMeasure Kernel.id (πs i)) ∧
          volume.restrict (Set.Icc (0 : ℝ) 1) = ∑ i, t i • πs i := by
  have hprob : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  refine ⟨⟨hprob, (gp_adjointOp_iterate (Kernel.id : Kernel ℝ ℝ) 0 _).symm⟩, ?_⟩
  rintro ⟨n, t, πs, herg, hsum⟩
  -- every Borel set is invariant, so ergodic measures are `0`–`1` valued
  have h01 : ∀ i A, MeasurableSet A → πs i A = 0 ∨ πs i A = 1 := fun i A hA =>
    (herg i).2 A ⟨hA, fun x hx => by simp [Kernel.id_apply, Measure.dirac_apply_of_mem hx]⟩
  have hprobi : ∀ i, IsProbabilityMeasure (πs i) := fun i => (herg i).1.1
  set I : Fin (n + 1) → Set ℝ := fun j =>
    Set.Ico ((j : ℝ) / (n + 1)) (((j : ℝ) + 1) / (n + 1))
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hIsub : ∀ j, I j ⊆ Set.Icc 0 1 := fun j x hx => by
    obtain ⟨h1, h2⟩ := hx
    have hj : ((j : ℕ) : ℝ) + 1 ≤ n + 1 := by
      have := j.2; exact_mod_cast Nat.succ_le_of_lt this
    refine ⟨le_trans (by positivity) h1, h2.le.trans ?_⟩
    rw [div_le_one hn]; exact hj
  have hIpos : ∀ j, volume.restrict (Set.Icc (0 : ℝ) 1) (I j) ≠ 0 := fun j => by
    rw [Measure.restrict_apply measurableSet_Ico, Set.inter_eq_left.2 (hIsub j), Real.volume_Ico]
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    rw [← sub_div, add_sub_cancel_left]
    positivity
  have hdisj : ∀ j j', j ≠ j' → Disjoint (I j) (I j') := fun j j' hjj' => by
    rw [Set.disjoint_left]
    rintro x ⟨a1, a2⟩ ⟨b1, b2⟩
    have c1 : ((j : ℕ) : ℝ) < (j' : ℕ) + 1 := by
      have := a1.trans_lt b2; rwa [div_lt_div_iff_of_pos_right hn] at this
    have c2 : ((j' : ℕ) : ℝ) < (j : ℕ) + 1 := by
      have := b1.trans_lt a2; rwa [div_lt_div_iff_of_pos_right hn] at this
    have d1 : (j : ℕ) < j' + 1 := by exact_mod_cast c1
    have d2 : (j' : ℕ) < j + 1 := by exact_mod_cast c2
    exact hjj' (Fin.ext (by omega))
  -- each interval gets mass `1` from some `πᵢ`
  have hpick : ∀ j, ∃ i, πs i (I j) = 1 := fun j => by
    by_contra hcon
    push Not at hcon
    have hz : ∀ i, πs i (I j) = 0 := fun i =>
      (h01 i (I j) measurableSet_Ico).resolve_right (hcon i)
    refine hIpos j ?_
    rw [hsum, Measure.coe_finsetSum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by simp [hz i]
  choose f hf using hpick
  have hinj : Function.Injective f := fun j j' hjj' => by
    by_contra hne
    have hu := measure_union (μ := πs (f j)) (hdisj j j' hne) measurableSet_Ico
    rw [hf j, hjj', hf j'] at hu
    have : πs (f j') (I j ∪ I j') ≤ 1 := prob_le_one
    rw [hu] at this
    norm_num at this
  have := Fintype.card_le_of_injective f hinj
  simp at this

end Miao.MarkovProcesses
