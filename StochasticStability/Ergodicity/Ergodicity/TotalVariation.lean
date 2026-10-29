/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.Invariance
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The total variation norm (MT §13.0, (13.7)–(13.8), Proposition 13.3.2)

Meyn and Tweedie, pp. 315 and 327–328. For two finite measures `μ`, `ν` on `X` the total
variation norm of the signed measure `μ − ν` is (13.7)

  `‖μ − ν‖ = sup_{|f| ≤ 1} |μ(f) − ν(f)|`,

the supremum over measurable `f : X → ℝ` with `|f| ≤ 1`. This is `tvNorm μ ν`; Chapters 14–16
use the same definition (the `f`-norm with `f ≡ 1`).

**Basic properties.**
* `tvNorm_nonneg`, `tvNorm_comm`, `tvNorm_self`, `tvNorm_triangle` (a pseudometric);
  `abs_integral_sub_le_tvNorm` (the defining bound), `tvNorm_le` (bounds on all `|f| ≤ 1` bound
  the norm), `abs_integral_sub_le_mul_tvNorm` (for `|f| ≤ C`);
  `tvNorm_le_add_measureReal` (`‖μ − ν‖ ≤ μ(X) + ν(X)`).
* `tvNorm_le_of_sub_eq`: if `μ(B) − ν(B) = σ₁(B) − σ₂(B)` for all `B` with finite measures
  `σ₁`, `σ₂`, then `‖μ − ν‖ ≤ σ₁(X) + σ₂(X)`. This is how the regenerative decompositions of
  §13.2–13.3 are turned into total variation bounds.
* `abs_measureReal_sub_le_tvNorm`: `|μ(A) − ν(A)| ≤ ‖μ − ν‖`.
* `tvNorm_add_le`, `tvNorm_smul_le`, `tvNorm_finsetSum_le`: the norm is subadditive over sums of
  measures and `‖cμ − cν‖ ≤ c‖μ − ν‖`.

**The forms (13.7) and (13.8).**
* `tvNorm_eq_sup_sub_inf` (13.7): `‖μ − ν‖ = sup_A (μ − ν)(A) − inf_A (μ − ν)(A)`, through the
  Hahn decomposition of `μ − ν` (Mathlib's `IsHahnDecomposition`).
* `tvNorm_eq_two_mul_tvSup` (13.8): when `μ(X) = ν(X)`, `‖μ − ν‖ = 2 sup_A |μ(A) − ν(A)|`;
  `two_mul_abs_sub_le_tvNorm` is the easy half. `tendsto_tvNorm_iff_tvSup`: convergence in the
  two forms is the same.
* `tvNorm_eq_tsum` (p. 319): on a countable space with measurable points,
  `‖μ − ν‖ = Σ_y |μ{y} − ν{y}|`; `abs_singleton_sub_le_tvNorm` is the remark after (13.8) that
  total variation convergence gives the pointwise convergence (13.6) uniformly in the end point.

**Transport.**
* `tvNorm_map_le`: `‖μg⁻¹ − νg⁻¹‖ ≤ ‖μ − ν‖` for measurable `g` (used for the marginal of the
  split chain, (13.57)).
* `integral_comp_kernel` (`(μP)(f) = μ(Pf)` for bounded `f`) and `tvNorm_comp_le`:
  `‖μP − νP‖ ≤ ‖μ − ν‖` for a transition kernel `P` (since `|Pf| ≤ 1`).
* **Proposition 13.3.2** (`proposition_13_3_2`, p. 327): if `π` is invariant, `‖λPⁿ − π‖` is
  non-increasing in `n`.
* `tendsto_integral_of_tendsto_tvNorm` (p. 315): total variation convergence implies the
  convergence of `μₙ(f)` for every bounded measurable `f`, in particular weak convergence.

**Corrections.** None.
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The values `|μ(f) − ν(f)|` over measurable `f : X → ℝ` with `|f| ≤ 1`. -/
def tvValues (μ ν : Measure X) : Set ℝ :=
  {r | ∃ f : X → ℝ, Measurable f ∧ (∀ x, |f x| ≤ 1) ∧ r = |∫ x, f x ∂μ - ∫ x, f x ∂ν|}

/-- The **total variation norm** `‖μ − ν‖ = sup_{|f| ≤ 1} |μ(f) − ν(f)|` (13.7), MT p. 315. -/
noncomputable def tvNorm (μ ν : Measure X) : ℝ := sSup (tvValues μ ν)

/-- `0` is a value (take `f = 0`). -/
theorem zero_mem_tvValues (μ ν : Measure X) : (0 : ℝ) ∈ tvValues μ ν :=
  ⟨fun _ => 0, measurable_const, fun _ => by simp, by simp⟩

/-- A measurable `f` with `|f| ≤ 1` is integrable for a finite measure. -/
theorem integrable_of_abs_le_one {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (h1 : ∀ x, |f x| ≤ 1) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h1 x)

/-- `|μ(f)| ≤ μ(X)` when `|f| ≤ 1`. -/
theorem abs_integral_le_measureReal {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (h1 : ∀ x, |f x| ≤ 1) : |∫ x, f x ∂μ| ≤ μ.real univ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := 1) (f := f)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h1 x)
  rwa [Real.norm_eq_abs, one_mul] at h

/-- The values are bounded by `μ(X) + ν(X)`. -/
theorem bddAbove_tvValues (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove (tvValues μ ν) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro r ⟨f, -, h1, rfl⟩
  exact (abs_sub _ _).trans
    (add_le_add (abs_integral_le_measureReal h1) (abs_integral_le_measureReal h1))

/-- The defining bound: `|μ(f) − ν(f)| ≤ ‖μ − ν‖` for measurable `|f| ≤ 1`. -/
theorem abs_integral_sub_le_tvNorm (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : Measurable f) (h1 : ∀ x, |f x| ≤ 1) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ tvNorm μ ν :=
  le_csSup (bddAbove_tvValues μ ν) ⟨f, hf, h1, rfl⟩

/-- `‖μ − ν‖ ≥ 0`. -/
theorem tvNorm_nonneg (μ ν : Measure X) : 0 ≤ tvNorm μ ν :=
  Real.sSup_nonneg fun _ ⟨_, _, _, h⟩ => h ▸ abs_nonneg _

/-- A bound valid for every measurable `|f| ≤ 1` bounds the norm. -/
theorem tvNorm_le {μ ν : Measure X} {c : ℝ}
    (h : ∀ f : X → ℝ, Measurable f → (∀ x, |f x| ≤ 1) → |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ c) :
    tvNorm μ ν ≤ c :=
  csSup_le ⟨0, zero_mem_tvValues μ ν⟩ (by rintro r ⟨f, hf, h1, rfl⟩; exact h f hf h1)

/-- `‖μ − ν‖ = ‖ν − μ‖`. -/
theorem tvNorm_comm (μ ν : Measure X) : tvNorm μ ν = tvNorm ν μ := by
  have h : tvValues μ ν = tvValues ν μ := by
    ext r
    constructor
    · rintro ⟨f, hf, h1, rfl⟩; exact ⟨f, hf, h1, abs_sub_comm _ _⟩
    · rintro ⟨f, hf, h1, rfl⟩; exact ⟨f, hf, h1, abs_sub_comm _ _⟩
  rw [tvNorm, tvNorm, h]

/-- `‖μ − μ‖ = 0`. -/
theorem tvNorm_self (μ : Measure X) : tvNorm μ μ = 0 :=
  le_antisymm (tvNorm_le fun _ _ _ => by simp) (tvNorm_nonneg μ μ)

/-- The triangle inequality `‖μ − ρ‖ ≤ ‖μ − ν‖ + ‖ν − ρ‖`. -/
theorem tvNorm_triangle (μ ν ρ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] : tvNorm μ ρ ≤ tvNorm μ ν + tvNorm ν ρ :=
  tvNorm_le fun _ hf h1 => (abs_sub_le _ _ _).trans
    (add_le_add (abs_integral_sub_le_tvNorm μ ν hf h1) (abs_integral_sub_le_tvNorm ν ρ hf h1))

/-- `‖μ − ν‖ ≤ μ(X) + ν(X)`. -/
theorem tvNorm_le_add_measureReal (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvNorm μ ν ≤ μ.real univ + ν.real univ :=
  tvNorm_le fun _ _ h1 => (abs_sub _ _).trans
    (add_le_add (abs_integral_le_measureReal h1) (abs_integral_le_measureReal h1))

/-- For `|f| ≤ C`, `|μ(f) − ν(f)| ≤ C ‖μ − ν‖`. -/
theorem abs_integral_sub_le_mul_tvNorm (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 < C)
    (hfC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ C * tvNorm μ ν := by
  have h := abs_integral_sub_le_tvNorm μ ν (f := fun x => C⁻¹ * f x)
    (measurable_const.mul hf) fun x => by
      rw [abs_mul, abs_of_pos (inv_pos.2 hC), inv_mul_le_iff₀ hC, mul_one]; exact hfC x
  rw [integral_const_mul, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hC),
    inv_mul_le_iff₀ hC] at h
  exact h

/-- **Total variation bounds from decompositions.** If `μ(B) − ν(B) = σ₁(B) − σ₂(B)` for every
measurable `B`, with `σ₁`, `σ₂` finite, then `‖μ − ν‖ ≤ σ₁(X) + σ₂(X)`. -/
theorem tvNorm_le_of_sub_eq {μ ν σ₁ σ₂ : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    (h : ∀ B, MeasurableSet B → μ.real B - ν.real B = σ₁.real B - σ₂.real B) :
    tvNorm μ ν ≤ σ₁.real univ + σ₂.real univ := by
  have heq : μ + σ₂ = ν + σ₁ := by
    ext B hB
    rw [Measure.add_apply, Measure.add_apply, ← ENNReal.toReal_eq_toReal_iff'
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have := h B hB
    simp only [measureReal_def] at this
    linarith
  refine tvNorm_le fun f hf h1 => ?_
  have h2 : ∫ x, f x ∂μ + ∫ x, f x ∂σ₂ = ∫ x, f x ∂ν + ∫ x, f x ∂σ₁ := by
    rw [← integral_add_measure (integrable_of_abs_le_one hf h1)
      (integrable_of_abs_le_one hf h1), ← integral_add_measure (integrable_of_abs_le_one hf h1)
      (integrable_of_abs_le_one hf h1), heq]
  have e : ∫ x, f x ∂μ - ∫ x, f x ∂ν = ∫ x, f x ∂σ₁ - ∫ x, f x ∂σ₂ := by linarith
  rw [e]
  exact (abs_sub _ _).trans
    (add_le_add (abs_integral_le_measureReal h1) (abs_integral_le_measureReal h1))

/-- `|μ(A) − ν(A)| ≤ ‖μ − ν‖` (take `f = 1_A`). -/
theorem abs_measureReal_sub_le_tvNorm (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set X} (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ tvNorm μ ν := by
  have h := abs_integral_sub_le_tvNorm μ ν (f := A.indicator 1) (measurable_one.indicator hA)
    fun x => by by_cases hx : x ∈ A <;> simp [hx]
  rwa [integral_indicator_one hA, integral_indicator_one hA] at h

/-- The integral of `2 · 1_A − 1`. -/
theorem integral_two_indicator_sub_one (μ : Measure X) [IsFiniteMeasure μ] {A : Set X}
    (hA : MeasurableSet A) :
    ∫ x, (2 * A.indicator (1 : X → ℝ) x - 1) ∂μ = 2 * μ.real A - μ.real univ := by
  have hi : Integrable (A.indicator (1 : X → ℝ)) μ :=
    integrable_of_abs_le_one (measurable_one.indicator hA) fun x => by
      by_cases hx : x ∈ A <;> simp [hx]
  rw [integral_sub (hi.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_indicator_one hA, integral_const, smul_eq_mul, mul_one]

/-- (13.8), easy half: for `μ(X) = ν(X)`, `2 |μ(A) − ν(A)| ≤ ‖μ − ν‖` (take `f = 1_A − 1_{Aᶜ}`). -/
theorem two_mul_abs_sub_le_tvNorm (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) {A : Set X} (hA : MeasurableSet A) :
    2 * |μ.real A - ν.real A| ≤ tvNorm μ ν := by
  have hm : μ.real univ = ν.real univ := by simp only [measureReal_def, hmass]
  have h := abs_integral_sub_le_tvNorm μ ν (f := fun x => 2 * A.indicator (1 : X → ℝ) x - 1)
    ((measurable_one.indicator hA).const_mul 2 |>.sub measurable_const) fun x => by
      by_cases hx : x ∈ A <;> norm_num [hx]
  rw [integral_two_indicator_sub_one μ hA, integral_two_indicator_sub_one ν hA, hm,
    show 2 * μ.real A - ν.real univ - (2 * ν.real A - ν.real univ) =
      2 * (μ.real A - ν.real A) by ring, abs_mul, abs_two] at h
  exact h

/-- The values `μ(A) − ν(A)` of the signed measure `μ − ν`. -/
def signedValues (μ ν : Measure X) : Set ℝ := {r | ∃ A, MeasurableSet A ∧ r = μ.real A - ν.real A}

/-- `μ(A) − ν(A)` lies in `[−ν(X), μ(X)]`. -/
theorem signedValues_mem_Icc (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r : ℝ} (hr : r ∈ signedValues μ ν) : r ∈ Icc (-ν.real univ) (μ.real univ) := by
  obtain ⟨A, -, rfl⟩ := hr
  have h1 : μ.real A ≤ μ.real univ := measureReal_mono (subset_univ A)
  have h2 : ν.real A ≤ ν.real univ := measureReal_mono (subset_univ A)
  exact ⟨by linarith [measureReal_nonneg (μ := μ) (s := A)],
    by linarith [measureReal_nonneg (μ := ν) (s := A)]⟩

/-- `μ(A) − ν(A) − (μ(B) − ν(B)) ≤ ‖μ − ν‖` (take `f = 1_A − 1_B`). -/
theorem sub_signedValues_le_tvNorm (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.real A - ν.real A - (μ.real B - ν.real B) ≤ tvNorm μ ν := by
  have h := abs_integral_sub_le_tvNorm μ ν
    (f := fun x => A.indicator (1 : X → ℝ) x - B.indicator 1 x)
    ((measurable_one.indicator hA).sub (measurable_one.indicator hB)) fun x => by
      by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;> simp [hx, hy]
  have hi : ∀ (ρ : Measure X) [IsFiniteMeasure ρ] {C : Set X}, MeasurableSet C →
      Integrable (C.indicator (1 : X → ℝ)) ρ := fun ρ _ C hC =>
    integrable_of_abs_le_one (measurable_one.indicator hC) fun x => by
      by_cases hx : x ∈ C <;> simp [hx]
  rw [integral_sub (hi μ hA) (hi μ hB), integral_sub (hi ν hA) (hi ν hB),
    integral_indicator_one hA, integral_indicator_one hB, integral_indicator_one hA,
    integral_indicator_one hB] at h
  exact (le_abs_self _).trans (by convert h using 2; ring)

/-- The Hahn bound: for a Hahn decomposition `s` of `(μ, ν)`,
`‖μ − ν‖ ≤ (μ − ν)(sᶜ) − (μ − ν)(s)`. -/
theorem tvNorm_le_hahn {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Set X}
    (hs : IsHahnDecomposition μ ν s) :
    tvNorm μ ν ≤ (μ.real sᶜ - ν.real sᶜ) - (μ.real s - ν.real s) := by
  set σ₁ := μ.restrict sᶜ - ν.restrict sᶜ
  set σ₂ := ν.restrict s - μ.restrict s
  have hσ₁ : ∀ B, MeasurableSet B → σ₁.real B = μ.real (B ∩ sᶜ) - ν.real (B ∩ sᶜ) := fun B hB => by
    rw [measureReal_def, Measure.sub_apply hB hs.ge_on_compl, Measure.restrict_apply hB,
      Measure.restrict_apply hB, ENNReal.toReal_sub_of_le (by
        have := hs.ge_on_compl B
        rwa [Measure.restrict_apply hB, Measure.restrict_apply hB] at this)
        (measure_ne_top _ _)]
    rfl
  have hσ₂ : ∀ B, MeasurableSet B → σ₂.real B = ν.real (B ∩ s) - μ.real (B ∩ s) := fun B hB => by
    rw [measureReal_def, Measure.sub_apply hB hs.le_on, Measure.restrict_apply hB,
      Measure.restrict_apply hB, ENNReal.toReal_sub_of_le (by
        have := hs.le_on B
        rwa [Measure.restrict_apply hB, Measure.restrict_apply hB] at this)
        (measure_ne_top _ _)]
    rfl
  have h := tvNorm_le_of_sub_eq (μ := μ) (ν := ν) (σ₁ := σ₁) (σ₂ := σ₂) fun B hB => by
    rw [hσ₁ B hB, hσ₂ B hB, ← measureReal_inter_add_sdiff (s := B) hs.measurableSet (μ := μ),
      ← measureReal_inter_add_sdiff (s := B) hs.measurableSet (μ := ν), sdiff_eq]
    ring
  rw [hσ₁ univ MeasurableSet.univ, hσ₂ univ MeasurableSet.univ, univ_inter, univ_inter] at h
  linarith

/-- **(13.7)**, MT p. 315: `‖μ − ν‖ = sup_A (μ − ν)(A) − inf_A (μ − ν)(A)`. -/
theorem tvNorm_eq_sup_sub_inf (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvNorm μ ν = sSup (signedValues μ ν) - sInf (signedValues μ ν) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hne : (signedValues μ ν).Nonempty := ⟨_, univ, MeasurableSet.univ, rfl⟩
  have hbdd : BddAbove (signedValues μ ν) :=
    ⟨μ.real univ, fun _ hr => (signedValues_mem_Icc μ ν hr).2⟩
  have hbdd' : BddBelow (signedValues μ ν) :=
    ⟨-ν.real univ, fun _ hr => (signedValues_mem_Icc μ ν hr).1⟩
  refine le_antisymm ((tvNorm_le_hahn hs).trans (sub_le_sub
    (le_csSup hbdd ⟨sᶜ, hs.measurableSet.compl, rfl⟩)
    (csInf_le hbdd' ⟨s, hs.measurableSet, rfl⟩))) ?_
  rw [sub_le_iff_le_add]
  refine csSup_le hne fun r ⟨A, hA, hr⟩ => ?_
  rw [← sub_le_iff_le_add']
  refine le_csInf hne fun t ⟨B, hB, ht⟩ => ?_
  rw [hr, ht, sub_le_comm]
  exact sub_signedValues_le_tvNorm μ ν hA hB

/-- `sup_A |μ(A) − ν(A)|`. -/
noncomputable def tvSup (μ ν : Measure X) : ℝ :=
  sSup {r | ∃ A, MeasurableSet A ∧ r = |μ.real A - ν.real A|}

/-- `|μ(A) − ν(A)| ≤ sup_A |μ(A) − ν(A)|`. -/
theorem abs_sub_le_tvSup (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X}
    (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ tvSup μ ν := by
  refine le_csSup ⟨μ.real univ + ν.real univ, ?_⟩ ⟨A, hA, rfl⟩
  rintro r ⟨B, -, rfl⟩
  refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
    rw [abs_of_nonneg measureReal_nonneg] <;> exact measureReal_mono (subset_univ B)

/-- **(13.8)**, MT p. 315: for `μ(X) = ν(X)`, `‖μ − ν‖ = 2 sup_A |μ(A) − ν(A)|`. -/
theorem tvNorm_eq_two_mul_tvSup (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) : tvNorm μ ν = 2 * tvSup μ ν := by
  have hm : μ.real univ = ν.real univ := by simp only [measureReal_def, hmass]
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine le_antisymm ((tvNorm_le_hahn hs).trans ?_) ?_
  · have hc : μ.real sᶜ - ν.real sᶜ = -(μ.real s - ν.real s) := by
      rw [measureReal_compl hs.measurableSet, measureReal_compl hs.measurableSet, hm]; ring
    rw [hc]
    have := abs_sub_le_tvSup μ ν hs.measurableSet
    linarith [neg_abs_le (μ.real s - ν.real s)]
  · rw [← le_div_iff₀' two_pos]
    refine csSup_le ⟨_, univ, MeasurableSet.univ, rfl⟩ fun r ⟨A, hA, hr⟩ => ?_
    rw [hr, le_div_iff₀' two_pos]
    exact two_mul_abs_sub_le_tvNorm μ ν hmass hA

/-- Convergence in total variation is convergence of `sup_A |μₙ(A) − ν(A)|`, for equal masses. -/
theorem tendsto_tvNorm_iff_tvSup {μ : ℕ → Measure X} {ν : Measure X} [∀ n, IsFiniteMeasure (μ n)]
    [IsFiniteMeasure ν] (hmass : ∀ n, μ n univ = ν univ) :
    Tendsto (fun n => tvNorm (μ n) ν) atTop (𝓝 0) ↔
      Tendsto (fun n => tvSup (μ n) ν) atTop (𝓝 0) := by
  simp_rw [tvNorm_eq_two_mul_tvSup _ _ (hmass _)]
  constructor
  · intro h
    simpa using h.const_mul (1 / 2 : ℝ)
  · intro h
    simpa using h.const_mul 2

/-! ### Countable spaces -/

/-- On a countable space with measurable points, `μ(X) = Σ_y μ{y}`. -/
theorem measure_univ_eq_tsum_singleton [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) : μ univ = ∑' y, μ {y} := by
  rw [← measure_iUnion (fun i j hij => disjoint_singleton.2 hij)
    (fun y => measurableSet_singleton y), iUnion_of_singleton]

/-- The masses `μ{y}` of a finite measure are summable. -/
theorem summable_measureReal_singleton [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] : Summable fun y => μ.real {y} := by
  refine ENNReal.summable_toReal ?_
  rw [← measure_univ_eq_tsum_singleton]
  exact measure_ne_top μ univ

/-- On a countable space, `μ(f) = Σ_y f(y) μ{y}` for `|f| ≤ 1`. -/
theorem integral_eq_tsum_of_countable [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (h1 : ∀ x, |f x| ≤ 1) :
    ∫ x, f x ∂μ = ∑' y, μ.real {y} * f y := by
  rw [integral_countable (integrable_of_abs_le_one (measurable_of_countable f) h1)]
  rfl

/-- **The total variation norm on a countable space** (MT p. 319):
`‖μ − ν‖ = Σ_y |μ{y} − ν{y}|`. -/
theorem tvNorm_eq_tsum [Countable X] [MeasurableSingletonClass X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvNorm μ ν = ∑' y, |μ.real {y} - ν.real {y}| := by
  have hsμ := summable_measureReal_singleton μ
  have hsν := summable_measureReal_singleton ν
  have hsd : Summable fun y => |μ.real {y} - ν.real {y}| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun y => (abs_sub _ _).trans_eq (by rw [abs_of_nonneg measureReal_nonneg,
        abs_of_nonneg measureReal_nonneg])) (hsμ.add hsν)
  have key : ∀ f : X → ℝ, (∀ x, |f x| ≤ 1) →
      ∫ x, f x ∂μ - ∫ x, f x ∂ν = ∑' y, (μ.real {y} - ν.real {y}) * f y := fun f h1 => by
    have hm : Summable fun y => μ.real {y} * f y :=
      Summable.of_norm_bounded hsμ fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
        exact mul_le_of_le_one_right measureReal_nonneg (h1 y)
    have hn : Summable fun y => ν.real {y} * f y :=
      Summable.of_norm_bounded hsν fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
        exact mul_le_of_le_one_right measureReal_nonneg (h1 y)
    rw [integral_eq_tsum_of_countable μ h1, integral_eq_tsum_of_countable ν h1,
      ← hm.tsum_sub hn]
    exact tsum_congr fun y => by ring
  refine le_antisymm (tvNorm_le fun f _ h1 => ?_) ?_
  · rw [key f h1]
    have hle : ∀ y, ‖(μ.real {y} - ν.real {y}) * f y‖ ≤ |μ.real {y} - ν.real {y}| := fun y => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (h1 y)
    have hsum : Summable fun y => ‖(μ.real {y} - ν.real {y}) * f y‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsd
    calc |∑' y, (μ.real {y} - ν.real {y}) * f y|
        = ‖∑' y, (μ.real {y} - ν.real {y}) * f y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' y, ‖(μ.real {y} - ν.real {y}) * f y‖ := norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' y, |μ.real {y} - ν.real {y}| := hsum.tsum_le_tsum hle hsd
  · classical
    set g : X → ℝ := fun y => if 0 ≤ μ.real {y} - ν.real {y} then 1 else -1
    have hg1 : ∀ x, |g x| ≤ 1 := fun x => by
      simp only [g]; split_ifs <;> simp
    have h := abs_integral_sub_le_tvNorm μ ν (measurable_of_countable g) hg1
    rw [key g hg1] at h
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) ((le_abs_self _).trans h)
    simp only [g]
    split_ifs with hy
    · rw [mul_one, abs_of_nonneg hy]
    · rw [mul_neg_one, abs_of_neg (not_le.1 hy)]

/-- The remark after (13.8): `|μ{y} − ν{y}| ≤ ‖μ − ν‖` for every `y`, so convergence in total
variation gives the pointwise convergence (13.6), uniformly in `y`. -/
theorem abs_singleton_sub_le_tvNorm [MeasurableSingletonClass X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (y : X) :
    |μ.real {y} - ν.real {y}| ≤ tvNorm μ ν :=
  abs_measureReal_sub_le_tvNorm μ ν (measurableSet_singleton y)

/-! ### Transport by maps and kernels -/

/-- `‖μg⁻¹ − νg⁻¹‖ ≤ ‖μ − ν‖` for a measurable map `g`. -/
theorem tvNorm_map_le {Y : Type*} [MeasurableSpace Y] {g : Y → X} (hg : Measurable g)
    (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvNorm (μ.map g) (ν.map g) ≤ tvNorm μ ν :=
  tvNorm_le fun _ hf h1 => by
    rw [integral_map hg.aemeasurable hf.aestronglyMeasurable,
      integral_map hg.aemeasurable hf.aestronglyMeasurable]
    exact abs_integral_sub_le_tvNorm μ ν (hf.comp hg) fun y => h1 (g y)

/-- `(μP)(f) = μ(Pf)` for a transition kernel `P` and measurable `|f| ≤ 1`. -/
theorem integral_comp_kernel {Y : Type*} [MeasurableSpace Y] (P : Kernel X Y) [IsMarkovKernel P]
    (μ : Measure X) [IsFiniteMeasure μ] {f : Y → ℝ} (hf : Measurable f) (h1 : ∀ y, |f y| ≤ 1) :
    ∫ y, f y ∂(P ∘ₘ μ) = ∫ x, (∫ y, f y ∂P x) ∂μ := by
  rw [← Measure.snd_compProd μ P, Measure.snd,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd (f := fun z : X × Y => f z.2)
      (integrable_of_abs_le_one (hf.comp measurable_snd) fun z => h1 z.2)]

/-- `‖μP − νP‖ ≤ ‖μ − ν‖` for a transition kernel `P`: `|Pf| ≤ 1` when `|f| ≤ 1`. -/
theorem tvNorm_comp_le (P : Kernel X X) [IsMarkovKernel P] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : tvNorm (P ∘ₘ μ) (P ∘ₘ ν) ≤ tvNorm μ ν :=
  tvNorm_le fun _ hf h1 => by
    rw [integral_comp_kernel P μ hf h1, integral_comp_kernel P ν hf h1]
    exact abs_integral_sub_le_tvNorm μ ν (measurable_kfunR P hf) (abs_kfunR_le P h1)

/-- **Proposition 13.3.2** (MT p. 327): if `π` is invariant for `P`, then `‖λPⁿ − π‖` is
non-increasing in `n`. -/
theorem proposition_13_3_2 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X} [IsFiniteMeasure π]
    (hπ : IsInvariant P π) (μ : Measure X) [IsFiniteMeasure μ] :
    Antitone fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π := by
  refine antitone_nat_of_succ_le fun n => ?_
  have := isMarkovKernel_pow P n
  have h : (P ^ (n + 1) : Kernel X X) ∘ₘ μ = P ∘ₘ ((P ^ n : Kernel X X) ∘ₘ μ) := by
    rw [pow_succ', Measure.comp_assoc]
    rfl
  calc tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π
        = tvNorm (P ∘ₘ ((P ^ n : Kernel X X) ∘ₘ μ)) (P ∘ₘ π) := by rw [h, hπ]
    _ ≤ tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π := tvNorm_comp_le P _ _

/-- The remark on p. 315: total variation convergence `‖μₙ − μ‖ → 0` gives `μₙ(f) → μ(f)` for
every bounded measurable `f` (in particular weak convergence on a topological space). -/
theorem tendsto_integral_of_tendsto_tvNorm {μs : ℕ → Measure X} {μ : Measure X}
    [∀ n, IsFiniteMeasure (μs n)] [IsFiniteMeasure μ]
    (h : Tendsto (fun n => tvNorm (μs n) μ) atTop (𝓝 0)) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 < C) (hfC : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using h.const_mul C)
  rw [Real.norm_eq_abs]
  exact abs_integral_sub_le_mul_tvNorm _ _ hf hC hfC

/-! ### Sums and multiples -/

/-- `‖(μ₁ + μ₂) − (ν₁ + ν₂)‖ ≤ ‖μ₁ − ν₁‖ + ‖μ₂ − ν₂‖`. -/
theorem tvNorm_add_le (μ₁ μ₂ ν₁ ν₂ : Measure X) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    tvNorm (μ₁ + μ₂) (ν₁ + ν₂) ≤ tvNorm μ₁ ν₁ + tvNorm μ₂ ν₂ :=
  tvNorm_le fun f hf h1 => by
    rw [integral_add_measure (integrable_of_abs_le_one hf h1) (integrable_of_abs_le_one hf h1),
      integral_add_measure (integrable_of_abs_le_one hf h1) (integrable_of_abs_le_one hf h1)]
    calc |∫ x, f x ∂μ₁ + ∫ x, f x ∂μ₂ - (∫ x, f x ∂ν₁ + ∫ x, f x ∂ν₂)|
        = |(∫ x, f x ∂μ₁ - ∫ x, f x ∂ν₁) + (∫ x, f x ∂μ₂ - ∫ x, f x ∂ν₂)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_integral_sub_le_tvNorm μ₁ ν₁ hf h1)
          (abs_integral_sub_le_tvNorm μ₂ ν₂ hf h1))

/-- `‖cμ − cν‖ ≤ c ‖μ − ν‖`. -/
theorem tvNorm_smul_le (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ≥0∞) :
    tvNorm (c • μ) (c • ν) ≤ c.toReal * tvNorm μ ν :=
  tvNorm_le fun f hf h1 => by
    rw [integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_sub,
      abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (abs_integral_sub_le_tvNorm μ ν hf h1) ENNReal.toReal_nonneg

/-- `‖Σᵢ μᵢ − Σᵢ νᵢ‖ ≤ Σᵢ ‖μᵢ − νᵢ‖` for finite sums. -/
theorem tvNorm_finsetSum_le {ι : Type*} (s : Finset ι) (μ ν : ι → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    tvNorm (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, tvNorm (μ i) (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tvNorm_self]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (tvNorm_add_le _ _ _ _).trans (add_le_add le_rfl ih)

end MeynTweedie.Ergodicity
