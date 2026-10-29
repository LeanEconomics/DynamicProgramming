/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.Atoms

/-!
# Minorization and the Nummelin splitting (MT §5.1.1)

Meyn and Tweedie, §5.1.1, pp. 98–100, and (5.10), p. 101. The split space is `X̌ = X × Bool`:
`X₀ = X × {false}` is the "top" copy of `X` and `X₁ = X × {true}` the "bottom" copy.

* `Minorization P` (5.2): a measurable set `C`, a constant `0 < δ < 1` and a probability
  measure `ν` with `P(x, ·) ≥ δ ν` for `x ∈ C`. `Minorization.IsConcentrated`: the book's extra
  requirement `ν(Cᶜ) = 0`; `Minorization.ofLe`: any bound `P(x, ·) ≥ ν'` on `C` with
  `0 < ν'(C) < ∞` gives a concentrated minorization.
* `splitK`: the kernel `x ↦ (1 − r(x)) δ_{(x,0)} + r(x) δ_{(x,1)}`, `r = δ 1_C`, which tosses the
  `δ`-coin; `split μ = μ*` (5.3) is `splitK ∘ₘ μ`. `split_apply_false`, `split_apply_true` are
  (5.3); `split_fst_preimage`, `split_map_fst` are the marginal identity (5.4); `split_add`,
  `split_smul`, `split_sub` express that `μ ↦ μ*` is linear.
* `resid`: the residual kernel `R(x, ·) = (1 − δ)⁻¹ (P(x, ·) − δν)` on `C` and `P(x, ·)` off `C`;
  it is a transition kernel (`isMarkovKernel_resid`): this is where (5.2) is used (p. 100).
* `baseK`: the kernel `Q(x₀, ·) = R(x, ·)`, `Q(x₁, ·) = ν`, and the split kernel
  `splitKernel = P̌ = splitK ∘ₖ baseK`: first move by `Q`, then toss the coin. This is (5.5)–(5.7)
  (`splitKernel_apply_false_of_notMem`, `splitKernel_apply_false_of_mem`,
  `splitKernel_apply_true`).
* `baseK_comp_splitK`: the factorisation `Q ∘ₖ splitK = P`, the heart of the construction.
* (5.10) `split_comp_splitKernel`: `μ* P̌ = (μP)*`, and `split_comp_splitKernel_pow`:
  `μ* P̌ⁿ = (μPⁿ)*`; `splitKernel_pow_succ`: `P̌ⁿ⁺¹ = splitK ∘ₖ Pⁿ ∘ₖ Q`.
* **Theorem 5.1.3 (i)** in the form (5.9) (`theorem_5_1_3_i`, p. 100):
  `∫ λ(dx) Pᵏ(x, A) = ∫ λ*(dy) P̌ᵏ(y, A₀ ∪ A₁)`.
* The atoms (p. 100): `isAtom_bottom` (`X₁` is an atom with `P̌(x₁, ·) = ν*`),
  `isAtom_checkAlpha` (`α̌ = C₁`, (5.8)), `splitKernel_pow_bottom_compl` (`P̌ⁿ(xᵢ, X₁ \ C₁) = 0`
  for `n ≥ 1`) and `split_bottom` (`φ*(X₁) = δ φ(C)`).

**Corrections.** The book allows `δ = 1` in (5.2), when (5.6) divides by `0`; the structure here
requires `δ < 1`, which costs nothing (`Minorization.ofLe` uses `δ ≤ 1/2`). The book requires
`ν(Cᶜ) = 0`; the construction and Theorem 5.1.3 do not need it, and it is kept as the separate
hypothesis `IsConcentrated` where it matters.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

variable (P : Kernel X X) in
/-- The **minorization condition** (5.2), MT p. 98: a measurable set `C`, a constant
`0 < δ < 1` and a probability measure `ν` with `P(x, A) ≥ δ ν(A)` for every `x ∈ C`. -/
structure Minorization where
  /-- The set `C` on which the chain is split. -/
  C : Set X
  /-- The constant `δ`. -/
  δ : ℝ≥0∞
  /-- The minorizing probability measure `ν`. -/
  ν : Measure X
  /-- `C` is measurable. -/
  measurableSet_C : MeasurableSet C
  /-- `δ > 0`. -/
  δ_pos : 0 < δ
  /-- `δ < 1`. -/
  δ_lt_one : δ < 1
  /-- `ν` is a probability measure. -/
  isProbabilityMeasure_ν : IsProbabilityMeasure ν
  /-- `P(x, ·) ≥ δ ν` for `x ∈ C`. -/
  le : ∀ x ∈ C, δ • ν ≤ P x

namespace Minorization

variable {P : Kernel X X}

/-- The book's normalisation in (5.2): `ν(Cᶜ) = 0`. -/
def IsConcentrated (M : Minorization P) : Prop := M.ν M.Cᶜ = 0

/-- `δ ≠ ∞`. -/
theorem δ_ne_top (M : Minorization P) : M.δ ≠ ∞ := (M.δ_lt_one.trans ENNReal.one_lt_top).ne

/-- `1 − δ ≠ 0`. -/
theorem one_sub_δ_ne_zero (M : Minorization P) : 1 - M.δ ≠ 0 :=
  (tsub_pos_of_lt M.δ_lt_one).ne'

/-- `δ ν` is a finite measure. -/
theorem isFiniteMeasure_smul_ν (M : Minorization P) : IsFiniteMeasure (M.δ • M.ν) := by
  have := M.isProbabilityMeasure_ν
  exact ⟨by simp [M.δ_ne_top.lt_top]⟩

/-- (5.2) on sets: `P(x, A) ≥ δ ν(A)` for `x ∈ C`. -/
theorem le_apply (M : Minorization P) {x : X} (hx : x ∈ M.C) (A : Set X) :
    M.δ * M.ν A ≤ P x A := by
  have := M.le x hx A
  rwa [Measure.smul_apply, smul_eq_mul] at this

/-- A minorization from any bound `P(x, ·) ≥ ν'` on `C` with `0 < ν'(C) < ∞`: take
`δ = min(ν'(C), 1/2)` and `ν = ν'(· ∩ C)/ν'(C)`. -/
noncomputable def ofLe {C : Set X} (hC : MeasurableSet C) {ν' : Measure X}
    (hle : ∀ x ∈ C, ν' ≤ P x) (hpos : 0 < ν' C) (hfin : ν' C ≠ ∞) : Minorization P where
  C := C
  δ := min (ν' C) 2⁻¹
  ν := (ν' C)⁻¹ • ν'.restrict C
  measurableSet_C := hC
  δ_pos := lt_min hpos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
  δ_lt_one := (min_le_right _ _).trans_lt (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  isProbabilityMeasure_ν := ⟨by
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
      ENNReal.inv_mul_cancel hpos.ne' hfin]⟩
  le x hx := by
    refine Measure.le_intro fun A hA _ => ?_
    rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    calc min (ν' C) 2⁻¹ * (ν' C)⁻¹ * ν' (A ∩ C) ≤ 1 * ν' (A ∩ C) := by
          gcongr
          calc min (ν' C) 2⁻¹ * (ν' C)⁻¹ ≤ ν' C * (ν' C)⁻¹ := by gcongr; exact min_le_left _ _
            _ = 1 := ENNReal.mul_inv_cancel hpos.ne' hfin
      _ ≤ P x A := by rw [one_mul]; exact (measure_mono inter_subset_left).trans (hle x hx A)

/-- The minorization `ofLe` lives on the given set. -/
theorem ofLe_C {C : Set X} (hC : MeasurableSet C) {ν' : Measure X} (hle : ∀ x ∈ C, ν' ≤ P x)
    (hpos : 0 < ν' C) (hfin : ν' C ≠ ∞) : (ofLe hC hle hpos hfin).C = C := rfl

/-- The minorization `ofLe` satisfies the book's normalisation `ν(Cᶜ) = 0`. -/
theorem ofLe_isConcentrated {C : Set X} (hC : MeasurableSet C) {ν' : Measure X}
    (hle : ∀ x ∈ C, ν' ≤ P x) (hpos : 0 < ν' C) (hfin : ν' C ≠ ∞) :
    (ofLe hC hle hpos hfin).IsConcentrated := by
  change ((ν' C)⁻¹ • ν'.restrict C) Cᶜ = 0
  rw [Measure.smul_apply, Measure.restrict_apply hC.compl, compl_inter_self, measure_empty,
    smul_zero]

/-! ### The coin and the split of a measure -/

/-- The coin probability `r(x) = δ 1_C(x)`: the probability that the split chain drops to the
bottom level on arriving at `x`. -/
noncomputable def splitProb (M : Minorization P) (x : X) : ℝ≥0∞ := M.C.indicator (fun _ => M.δ) x

/-- `r` is measurable. -/
theorem measurable_splitProb (M : Minorization P) : Measurable M.splitProb :=
  measurable_const.indicator M.measurableSet_C

/-- `r(x) ≤ δ`. -/
theorem splitProb_le (M : Minorization P) (x : X) : M.splitProb x ≤ M.δ := by
  unfold splitProb
  by_cases hx : x ∈ M.C <;> simp [hx]

/-- `r(x) ≤ 1`. -/
theorem splitProb_le_one (M : Minorization P) (x : X) : M.splitProb x ≤ 1 :=
  (M.splitProb_le x).trans M.δ_lt_one.le

/-- `r(x) = δ` on `C`. -/
theorem splitProb_of_mem (M : Minorization P) {x : X} (hx : x ∈ M.C) : M.splitProb x = M.δ := by
  simp [splitProb, hx]

/-- `r(x) = 0` off `C`. -/
theorem splitProb_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) : M.splitProb x = 0 := by
  simp [splitProb, hx]

/-- The coin measure `(1 − r(x)) δ_{(x,0)} + r(x) δ_{(x,1)}` on `X × Bool`. -/
noncomputable def splitMeas (M : Minorization P) (x : X) : Measure (X × Bool) :=
  (1 - M.splitProb x) • Measure.dirac (x, false) + M.splitProb x • Measure.dirac (x, true)

/-- The coin measure of a measurable set. -/
theorem splitMeas_apply (M : Minorization P) (x : X) {s : Set (X × Bool)} (hs : MeasurableSet s) :
    M.splitMeas x s = (1 - M.splitProb x) * s.indicator 1 (x, false) +
      M.splitProb x * s.indicator 1 (x, true) := by
  simp [splitMeas, Measure.dirac_apply' _ hs]

/-- The coin kernel `splitK : X → X × Bool`. -/
noncomputable def splitK (M : Minorization P) : Kernel X (X × Bool) where
  toFun := M.splitMeas
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [M.splitMeas_apply _ hs]
    have h0 : Measurable fun x : X => s.indicator (1 : X × Bool → ℝ≥0∞) (x, false) :=
      (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
    have h1 : Measurable fun x : X => s.indicator (1 : X × Bool → ℝ≥0∞) (x, true) :=
      (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
    exact ((measurable_const.sub M.measurable_splitProb).mul h0).add
      (M.measurable_splitProb.mul h1)

/-- `splitK x = (1 − r(x)) δ_{(x,0)} + r(x) δ_{(x,1)}`. -/
theorem splitK_apply (M : Minorization P) (x : X) : M.splitK x = M.splitMeas x := rfl

/-- The coin kernel is Markov. -/
theorem isMarkovKernel_splitK (M : Minorization P) : IsMarkovKernel M.splitK := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [splitK_apply, M.splitMeas_apply x MeasurableSet.univ]
  simp [tsub_add_cancel_of_le (M.splitProb_le_one x)]

/-- `∫ f d(splitK x) = (1 − r(x)) f(x, 0) + r(x) f(x, 1)`. -/
theorem lintegral_splitK (M : Minorization P) (x : X) {f : X × Bool → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂M.splitK x = (1 - M.splitProb x) * f (x, false) + M.splitProb x * f (x, true) := by
  rw [splitK_apply, splitMeas, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac' _ hf, lintegral_dirac' _ hf, smul_eq_mul,
    smul_eq_mul]

/-- The **split measure** `μ*` of (5.3), MT p. 99: `μ* = splitK ∘ₘ μ`. -/
noncomputable def split (M : Minorization P) (μ : Measure X) : Measure (X × Bool) := M.splitK ∘ₘ μ

/-- `μ*(s) = ∫ μ(dx) [(1 − r(x)) 1_s(x, 0) + r(x) 1_s(x, 1)]`. -/
theorem split_apply (M : Minorization P) (μ : Measure X) {s : Set (X × Bool)}
    (hs : MeasurableSet s) :
    M.split μ s = ∫⁻ x, (1 - M.splitProb x) * s.indicator 1 (x, false) +
      M.splitProb x * s.indicator 1 (x, true) ∂μ := by
  rw [split, Measure.bind_apply hs M.splitK.aemeasurable]
  exact lintegral_congr fun x => M.splitMeas_apply x hs

/-- `∫ f dμ* = ∫ μ(dx) [(1 − r(x)) f(x, 0) + r(x) f(x, 1)]`. -/
theorem lintegral_split (M : Minorization P) (μ : Measure X) {f : X × Bool → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂M.split μ =
      ∫⁻ x, (1 - M.splitProb x) * f (x, false) + M.splitProb x * f (x, true) ∂μ := by
  rw [split, Measure.lintegral_bind M.splitK.aemeasurable hf.aemeasurable]
  exact lintegral_congr fun x => M.lintegral_splitK x hf

/-- **(5.3), top level**: `μ*(A₀) = (1 − δ) μ(A ∩ C) + μ(A ∩ Cᶜ)`. -/
theorem split_apply_false (M : Minorization P) (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    M.split μ (A ×ˢ {false}) = (1 - M.δ) * μ (A ∩ M.C) + μ (A ∩ M.Cᶜ) := by
  rw [M.split_apply μ (hA.prod (measurableSet_singleton false))]
  have hfun : (fun x => (1 - M.splitProb x) * (A ×ˢ {false}).indicator (1 : X × Bool → ℝ≥0∞)
      (x, false) + M.splitProb x * (A ×ˢ {false}).indicator 1 (x, true)) =
      fun x => (A ∩ M.C).indicator (fun _ => 1 - M.δ) x + (A ∩ M.Cᶜ).indicator 1 x := by
    ext x
    by_cases hx : x ∈ A <;> by_cases hc : x ∈ M.C <;>
      simp [hx, hc, M.splitProb_of_mem, M.splitProb_of_notMem, indicator]
  rw [hfun, lintegral_add_left (measurable_const.indicator (hA.inter M.measurableSet_C)),
    lintegral_indicator_const (hA.inter M.measurableSet_C),
    lintegral_indicator_one (hA.inter M.measurableSet_C.compl)]

/-- **(5.3), bottom level**: `μ*(A₁) = δ μ(A ∩ C)`. -/
theorem split_apply_true (M : Minorization P) (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    M.split μ (A ×ˢ {true}) = M.δ * μ (A ∩ M.C) := by
  rw [M.split_apply μ (hA.prod (measurableSet_singleton true))]
  have hfun : (fun x => (1 - M.splitProb x) * (A ×ˢ {true}).indicator (1 : X × Bool → ℝ≥0∞)
      (x, false) + M.splitProb x * (A ×ˢ {true}).indicator 1 (x, true)) =
      (A ∩ M.C).indicator (fun _ => M.δ) := by
    ext x
    by_cases hx : x ∈ A <;> by_cases hc : x ∈ M.C <;>
      simp [hx, hc, M.splitProb_of_mem, M.splitProb_of_notMem, indicator]
  rw [hfun, lintegral_indicator_const (hA.inter M.measurableSet_C)]

/-- The bottom level: `φ*(X₁) = δ φ(C)` (MT p. 100). -/
theorem split_bottom (M : Minorization P) (μ : Measure X) :
    M.split μ (univ ×ˢ {true}) = M.δ * μ M.C := by
  rw [M.split_apply_true μ MeasurableSet.univ, univ_inter]

/-- **(5.4)**: `μ*(A₀ ∪ A₁) = μ(A)`, where `A₀ ∪ A₁ = A × Bool`. -/
theorem split_fst_preimage (M : Minorization P) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : M.split μ (Prod.fst ⁻¹' A) = μ A := by
  rw [M.split_apply μ (measurable_fst hA)]
  have hfun : (fun x => (1 - M.splitProb x) * (Prod.fst ⁻¹' A).indicator
      (1 : X × Bool → ℝ≥0∞) (x, false) + M.splitProb x * (Prod.fst ⁻¹' A).indicator 1 (x, true))
      = A.indicator 1 := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx, tsub_add_cancel_of_le (M.splitProb_le_one x)]
  rw [hfun, lintegral_indicator_one hA]

/-- (5.4) as an identity of measures: the marginal of `μ*` on `X` is `μ`. -/
theorem split_map_fst (M : Minorization P) (μ : Measure X) : (M.split μ).map Prod.fst = μ := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, M.split_fst_preimage μ hA]

/-- `μ*(X̌) = μ(X)`. -/
theorem split_univ (M : Minorization P) (μ : Measure X) : M.split μ univ = μ univ := by
  rw [← preimage_univ (f := (Prod.fst : X × Bool → X)), M.split_fst_preimage μ MeasurableSet.univ]

/-- `μ*` is a probability measure when `μ` is. -/
theorem isProbabilityMeasure_split (M : Minorization P) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (M.split μ) :=
  ⟨by rw [M.split_univ, measure_univ]⟩

/-- Splitting is additive: `(μ + ρ)* = μ* + ρ*`. -/
theorem split_add (M : Minorization P) (μ ρ : Measure X) :
    M.split (μ + ρ) = M.split μ + M.split ρ :=
  Measure.comp_add

/-- Splitting is homogeneous: `(c μ)* = c μ*`. -/
theorem split_smul (M : Minorization P) (c : ℝ≥0∞) (μ : Measure X) :
    M.split (c • μ) = c • M.split μ :=
  Measure.comp_smul c

/-- Splitting commutes with subtraction: `(μ − ρ)*(s) = μ*(s) − ρ*(s)` for `ρ ≤ μ`, `ρ` finite. -/
theorem split_sub (M : Minorization P) {μ ρ : Measure X} [IsFiniteMeasure ρ] (h : ρ ≤ μ)
    (s : Set (X × Bool)) : M.split (μ - ρ) s = M.split μ s - M.split ρ s := by
  have hfin : M.split ρ s ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ s))
    rw [M.split_univ]
    exact measure_ne_top ρ univ
  have hadd : M.split (μ - ρ) + M.split ρ = M.split μ := by
    rw [← M.split_add, Measure.sub_add_cancel_of_le h]
  rw [← hadd, Measure.add_apply, ENNReal.add_sub_cancel_right hfin]

/-- Splitting commutes with restriction to a cylinder: `μ*` restricted to `A × Bool` is
`(μ restricted to A)*`. -/
theorem split_restrict_fst (M : Minorization P) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) :
    (M.split μ).restrict (Prod.fst ⁻¹' A) = M.split (μ.restrict A) := by
  ext s hs
  rw [Measure.restrict_apply hs, M.split_apply _ (hs.inter (measurable_fst hA)),
    M.split_apply _ hs, ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · have h1 : ∀ b : Bool, (s ∩ Prod.fst ⁻¹' A).indicator (1 : X × Bool → ℝ≥0∞) (x, b) =
        s.indicator 1 (x, b) := fun b => by
      by_cases hb : (x, b) ∈ s <;> simp [hb, hx]
    simp [hx, h1]
  · have h1 : ∀ b : Bool, (s ∩ Prod.fst ⁻¹' A).indicator (1 : X × Bool → ℝ≥0∞) (x, b) = 0 :=
      fun b => by simp [hx]
    simp [hx]

/-! ### The residual kernel and the split kernel -/

/-- The residual measure `R(x, ·)`: `(1 − δ)⁻¹ (P(x, ·) − δ ν)` on `C` (5.6) and `P(x, ·)` off
`C` (5.5). -/
noncomputable def residMeas (M : Minorization P) (x : X) : Measure X := by
  classical
  exact if x ∈ M.C then (1 - M.δ)⁻¹ • (P x - M.δ • M.ν) else P x

/-- `R(x, A) = (1 − δ)⁻¹ (P(x, A) − δ ν(A))` on `C`. -/
theorem residMeas_apply_of_mem (M : Minorization P) {x : X} (hx : x ∈ M.C) {A : Set X}
    (hA : MeasurableSet A) :
    M.residMeas x A = (1 - M.δ)⁻¹ * (P x A - M.δ * M.ν A) := by
  have := M.isFiniteMeasure_smul_ν
  simp [residMeas, hx, Measure.sub_apply hA (M.le x hx)]

/-- `R(x, ·) = P(x, ·)` off `C`. -/
theorem residMeas_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) :
    M.residMeas x = P x := by
  simp [residMeas, hx]

/-- The residual kernel `R`. -/
noncomputable def resid (M : Minorization P) : Kernel X X where
  toFun := M.residMeas
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    classical
    have hfun : (fun x => M.residMeas x A) = fun x =>
        if x ∈ M.C then (1 - M.δ)⁻¹ * (P x A - M.δ * M.ν A) else P x A := by
      ext x
      by_cases hx : x ∈ M.C
      · simp only [hx, ite_true]
        exact M.residMeas_apply_of_mem hx hA
      · simp only [hx, ite_false]
        rw [M.residMeas_of_notMem hx]
    rw [hfun]
    exact Measurable.ite M.measurableSet_C
      (measurable_const.mul ((Kernel.measurable_coe P hA).sub measurable_const))
      (Kernel.measurable_coe P hA)

/-- `R(x, ·) = residMeas x`. -/
theorem resid_apply (M : Minorization P) (x : X) : M.resid x = M.residMeas x := rfl

/-- The residual kernel is a transition kernel (MT p. 100: "(5.6) is always non-negative"). -/
theorem isMarkovKernel_resid (M : Minorization P) [IsMarkovKernel P] :
    IsMarkovKernel M.resid := by
  have := M.isProbabilityMeasure_ν
  refine ⟨fun x => ⟨?_⟩⟩
  rw [resid_apply]
  by_cases hx : x ∈ M.C
  · rw [M.residMeas_apply_of_mem hx MeasurableSet.univ, measure_univ, measure_univ, mul_one,
      ENNReal.inv_mul_cancel M.one_sub_δ_ne_zero (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  · rw [M.residMeas_of_notMem hx, measure_univ]

/-- The measure `Q(z, ·)`: `ν` on the bottom level and `R(x, ·)` on the top level. -/
noncomputable def baseMeas (M : Minorization P) (z : X × Bool) : Measure X :=
  if z.2 then M.ν else M.resid z.1

/-- The kernel `Q : X̌ → X`. -/
noncomputable def baseK (M : Minorization P) : Kernel (X × Bool) X where
  toFun := M.baseMeas
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have hfun : (fun z => M.baseMeas z A) = fun z : X × Bool =>
        if z.2 = true then M.ν A else M.resid z.1 A := by
      ext z
      cases h : z.2 <;> simp [baseMeas, h]
    rw [hfun]
    exact Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
      ((Kernel.measurable_coe _ hA).comp measurable_fst)

/-- `Q(x₀, ·) = R(x, ·)`. -/
theorem baseK_apply_false (M : Minorization P) (x : X) : M.baseK (x, false) = M.resid x := by
  change M.baseMeas (x, false) = _
  simp [baseMeas]

/-- `Q(x₁, ·) = ν`. -/
theorem baseK_apply_true (M : Minorization P) (x : X) : M.baseK (x, true) = M.ν := by
  change M.baseMeas (x, true) = _
  simp [baseMeas]

/-- `Q` is a transition kernel. -/
theorem isMarkovKernel_baseK (M : Minorization P) [IsMarkovKernel P] : IsMarkovKernel M.baseK := by
  have := M.isProbabilityMeasure_ν
  have := M.isMarkovKernel_resid
  refine ⟨fun z => ?_⟩
  obtain ⟨x, b⟩ := z
  cases b
  · rw [baseK_apply_false]; infer_instance
  · rw [baseK_apply_true]; infer_instance

/-- **The factorisation** `Q ∘ₖ splitK = P`: tossing the coin at `x` and then moving by `Q`
is the same as moving by `P`. On `C`, `(1 − δ) R(x, ·) + δ ν = P(x, ·)`. -/
theorem baseK_comp_splitK (M : Minorization P) : M.baseK ∘ₖ M.splitK = P := by
  have := M.isFiniteMeasure_smul_ν
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA, M.lintegral_splitK x (Kernel.measurable_coe _ hA),
    baseK_apply_false, baseK_apply_true,
    resid_apply]
  by_cases hx : x ∈ M.C
  · rw [M.residMeas_apply_of_mem hx hA, M.splitProb_of_mem hx, ← mul_assoc,
      ENNReal.mul_inv_cancel M.one_sub_δ_ne_zero (ENNReal.sub_ne_top ENNReal.one_ne_top), one_mul,
      tsub_add_cancel_of_le (M.le_apply hx A)]
  · rw [M.residMeas_of_notMem hx, M.splitProb_of_notMem hx]
    simp

/-- The **split kernel** `P̌ = splitK ∘ₖ Q` (5.5)–(5.7), MT p. 99: from `xᵢ`, move to `y` by
`Q(xᵢ, ·)` and then toss the `δ`-coin at `y`. -/
noncomputable def splitKernel (M : Minorization P) : Kernel (X × Bool) (X × Bool) :=
  M.splitK ∘ₖ M.baseK

/-- `P̌(z, ·) = Q(z, ·)*`. -/
theorem splitKernel_apply (M : Minorization P) (z : X × Bool) :
    M.splitKernel z = M.split (M.baseK z) := by
  rw [splitKernel, Kernel.comp_apply]
  rfl

/-- The split kernel is a transition kernel. -/
theorem isMarkovKernel_splitKernel (M : Minorization P) [IsMarkovKernel P] :
    IsMarkovKernel M.splitKernel := by
  have := M.isMarkovKernel_baseK
  have := M.isMarkovKernel_splitK
  unfold splitKernel
  infer_instance

/-- **(5.5)**: `P̌(x₀, ·) = P(x, ·)*` for `x ∉ C`. -/
theorem splitKernel_apply_false_of_notMem (M : Minorization P) {x : X} (hx : x ∉ M.C) :
    M.splitKernel (x, false) = M.split (P x) := by
  rw [splitKernel_apply, baseK_apply_false, resid_apply, M.residMeas_of_notMem hx]

/-- **(5.6)**: `P̌(x₀, ·) = (1 − δ)⁻¹ [P(x, ·)* − δ ν*]` for `x ∈ C`. -/
theorem splitKernel_apply_false_of_mem (M : Minorization P) {x : X} (hx : x ∈ M.C)
    (s : Set (X × Bool)) :
    M.splitKernel (x, false) s = (1 - M.δ)⁻¹ * (M.split (P x) s - M.δ * M.split M.ν s) := by
  have := M.isFiniteMeasure_smul_ν
  rw [splitKernel_apply, baseK_apply_false, resid_apply]
  simp only [residMeas, hx, ite_true]
  rw [M.split_smul, Measure.smul_apply, smul_eq_mul, M.split_sub (M.le x hx), M.split_smul,
    Measure.smul_apply, smul_eq_mul]

/-- **(5.7)**: `P̌(x₁, ·) = ν*`. -/
theorem splitKernel_apply_true (M : Minorization P) (x : X) :
    M.splitKernel (x, true) = M.split M.ν := by
  rw [splitKernel_apply, baseK_apply_true]

/-- **(5.10)**, MT p. 101: `μ* P̌ = (μP)*`. -/
theorem split_comp_splitKernel (M : Minorization P) (μ : Measure X) :
    M.splitKernel ∘ₘ M.split μ = M.split (P ∘ₘ μ) := by
  rw [splitKernel, split, Measure.comp_assoc, Kernel.comp_assoc, baseK_comp_splitK,
    ← Measure.comp_assoc]
  rfl

/-- (5.10) iterated: `μ* P̌ⁿ = (μPⁿ)*`. -/
theorem split_comp_splitKernel_pow (M : Minorization P) (n : ℕ) (μ : Measure X) :
    (M.splitKernel ^ n : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split μ =
      M.split ((P ^ n : Kernel X X) ∘ₘ μ) := by
  induction n generalizing μ with
  | zero =>
    rw [pow_zero, pow_zero]
    change Kernel.id ∘ₘ _ = M.split (Kernel.id ∘ₘ μ)
    rw [Measure.id_comp, Measure.id_comp]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change ((M.splitKernel ^ n) ∘ₖ M.splitKernel) ∘ₘ _ = M.split (((P ^ n) ∘ₖ P) ∘ₘ μ)
    rw [← Measure.comp_assoc, split_comp_splitKernel, ih, Measure.comp_assoc]

/-- `P̌ⁿ⁺¹ = splitK ∘ₖ Pⁿ ∘ₖ Q`. -/
theorem splitKernel_pow_succ (M : Minorization P) (n : ℕ) :
    M.splitKernel ^ (n + 1) = M.splitK ∘ₖ ((P ^ n) ∘ₖ M.baseK) := by
  induction n with
  | zero =>
    rw [zero_add, pow_one, pow_zero]
    change _ = M.splitK ∘ₖ (Kernel.id ∘ₖ M.baseK)
    rw [Kernel.id_comp]
    rfl
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    change (M.splitK ∘ₖ ((P ^ n) ∘ₖ M.baseK)) ∘ₖ (M.splitK ∘ₖ M.baseK) =
      M.splitK ∘ₖ (((P ^ n) ∘ₖ P) ∘ₖ M.baseK)
    rw [show M.splitK ∘ₖ ((P ^ n) ∘ₖ M.baseK) ∘ₖ (M.splitK ∘ₖ M.baseK) =
      M.splitK ∘ₖ ((P ^ n) ∘ₖ (M.baseK ∘ₖ M.splitK) ∘ₖ M.baseK) by simp only [Kernel.comp_assoc],
      baseK_comp_splitK]

/-- `P̌ⁿ⁺¹(z, ·) = (Q(z, ·) Pⁿ)*`. -/
theorem splitKernel_pow_succ_apply (M : Minorization P) (n : ℕ) (z : X × Bool) :
    (M.splitKernel ^ (n + 1)) z = M.split ((P ^ n : Kernel X X) ∘ₘ M.baseK z) := by
  rw [splitKernel_pow_succ, Kernel.comp_apply, Kernel.comp_apply]
  rfl

/-- **Theorem 5.1.3 (i)** in the form (5.9), MT p. 100: for every measure `λ` and measurable `A`,
`∫ λ(dx) Pᵏ(x, A) = ∫ λ*(dy) P̌ᵏ(y, A₀ ∪ A₁)`. -/
theorem theorem_5_1_3_i (M : Minorization P) (k : ℕ) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) :
    ∫⁻ x, (P ^ k) x A ∂μ = ∫⁻ z, (M.splitKernel ^ k) z (Prod.fst ⁻¹' A) ∂M.split μ := by
  rw [← measure_kernel_apply μ _ hA, ← Measure.bind_apply (measurable_fst hA)
    (Kernel.aemeasurable _)]
  rw [split_comp_splitKernel_pow, M.split_fst_preimage _ hA]

/-! ### The atoms of the split chain -/

/-- The bottom level `X₁` is an atom for the split chain, with `P̌(x₁, ·) = ν*` (MT p. 100). -/
theorem isAtom_bottom (M : Minorization P) : IsAtom M.splitKernel (univ ×ˢ {true}) :=
  ⟨MeasurableSet.univ.prod (measurableSet_singleton true), M.split M.ν, fun z hz => by
    obtain ⟨x, b⟩ := z
    simp only [mem_prod, mem_univ, mem_singleton_iff, true_and] at hz
    rw [hz, splitKernel_apply_true]⟩

/-- The atom `α̌ = C₁` of (5.8), MT p. 100. -/
def checkAlpha (M : Minorization P) : Set (X × Bool) := M.C ×ˢ {true}

/-- `α̌ = C₁` is measurable. -/
theorem measurableSet_checkAlpha (M : Minorization P) : MeasurableSet M.checkAlpha :=
  M.measurableSet_C.prod (measurableSet_singleton true)

/-- `α̌ = C₁` is an atom (5.8). -/
theorem isAtom_checkAlpha (M : Minorization P) : IsAtom M.splitKernel M.checkAlpha :=
  ⟨M.measurableSet_checkAlpha, M.split M.ν, fun z hz => by
    obtain ⟨x, b⟩ := z
    simp only [checkAlpha, mem_prod, mem_singleton_iff] at hz
    rw [hz.2, splitKernel_apply_true]⟩

/-- `μ*(X₁ \ C₁) = 0`: the split measures put no mass on the bottom level outside `C`. -/
theorem split_bottom_compl (M : Minorization P) (μ : Measure X) :
    M.split μ (M.Cᶜ ×ˢ {true}) = 0 := by
  rw [M.split_apply_true μ M.measurableSet_C.compl, compl_inter_self, measure_empty, mul_zero]

/-- MT p. 100: `P̌ⁿ(xᵢ, X₁ \ C₁) = 0` for every `n ≥ 1` and every `xᵢ`, so that `α̌ = C₁` is the
only part of the bottom level reached with positive probability. -/
theorem splitKernel_pow_bottom_compl (M : Minorization P) (n : ℕ) (z : X × Bool) :
    (M.splitKernel ^ (n + 1)) z (M.Cᶜ ×ˢ {true}) = 0 := by
  rw [splitKernel_pow_succ_apply, split_bottom_compl]

end Minorization

end MeynTweedie.GeneralizedDrift
