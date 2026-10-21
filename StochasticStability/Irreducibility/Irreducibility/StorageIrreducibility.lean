/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Irreducibility.PsiIrreducibility
import Irreducibility.ModelRandomWalk

/-!
# Content-dependent storage models (MT §4.3.2)

Meyn and Tweedie, §4.3.2, p. 88. In the content-dependent storage model the content is released
at rate `r(x)`; a store at level `y` with no further input empties after the time
`R(y) = ∫₀^y r(z)⁻¹ dz` of (2.32), and stays empty afterwards.

The model is taken, as in the `MarkovModels` project, just before inputs (the order input, then
release, `contentPreInputKernel`; see the correction to (CSM2) there): from level `x` an input
`S ∼ H_x` is added, then the store releases for an interarrival time `T ∼ G` to the level
`q([x + S]⁺, T)`. The release function `q` is abstract; the release time enters only through
`q(y, t) = 0` for `t > R(y)`. The definitions `inputKernel` and `contentPreInputKernel` are
copied from `MarkovModels.Storage`.

* `contentPreInput_zero_pos`, `contentPreInput_isPhiIrreducible` (p. 88): if `R(y) < ∞` for every
  level and `P(T > R(y)) > 0` for every `y`, the chain reaches `{0}` in one step from every state
  and is `δ₀`-irreducible.
* `contentPreInput_hitProb_zero` (p. 88): if the store never empties (`q(y, t) > 0` for `y > 0`,
  the case `R(y) = ∞`) and inputs are nonnegative, `{0}` is never reached from `x > 0`, and the
  chain is not `δ₀`-irreducible (`contentPreInput_not_isPhiIrreducible`).

The claim that with `R = ∞` one still gets `μ_Leb`-irreducibility when the interarrival times
have a density is only sketched in the book ("determined by modifying the construction") and is
not formalised. The book's remark that exact conditions for φ-irreducibility are unknown is not a
mathematical claim.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- The input kernel `y ↦ law of [y + S(y)]⁺` with `S(y) ∼ H_y` (copied from
`MarkovModels.Storage`). -/
noncomputable def inputKernel (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  (Kernel.id ×ₖ Hin).map halfLineStep

/-- The input kernel at `y` is the image of `H_y` under `s ↦ [y + s]⁺`. -/
theorem inputKernel_apply (Hin : Kernel ℝ≥0 ℝ) [IsSFiniteKernel Hin] (y : ℝ≥0) :
    inputKernel Hin y = (Hin y).map fun s => Real.toNNReal (y + s) := by
  rw [inputKernel, Kernel.map_apply _ measurable_halfLineStep, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map measurable_halfLineStep measurable_prodMk_left]
  rfl

/-- The input kernel is a Markov kernel. -/
theorem isMarkovKernel_inputKernel (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin] :
    IsMarkovKernel (inputKernel Hin) := by
  unfold inputKernel
  exact Kernel.IsMarkovKernel.map _ measurable_halfLineStep

/-- The content-dependent storage model taken just before inputs: add the input `S ∼ H_x`, then
release for an interarrival time `T ∼ G` (copied from `MarkovModels.Storage`). -/
noncomputable def contentPreInputKernel (G : Measure ℝ) (q : ℝ≥0 × ℝ → ℝ≥0)
    (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel G q ∘ₖ inputKernel Hin

/-- The content-dependent storage model is a Markov kernel. -/
theorem isMarkovKernel_contentPreInputKernel (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin] :
    IsMarkovKernel (contentPreInputKernel G q Hin) := by
  have := isMarkovKernel_recursionKernel G hq
  have := isMarkovKernel_inputKernel Hin
  unfold contentPreInputKernel
  infer_instance

/-- MT p. 88: if a store at level `y` is empty after the release time `R(y) < ∞`
(`q(y, t) = 0` for `t > R(y)`) and `P(T > R(y)) > 0` for every `y`, then from every state the
store is empty before the next input with positive probability. -/
theorem contentPreInput_zero_pos (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    (R : ℝ≥0 → ℝ) (hq0 : ∀ y t, R y < t → q (y, t) = 0) (hG : ∀ y, 0 < G (Ioi (R y)))
    (x : ℝ≥0) : 0 < contentPreInputKernel G q Hin x {0} := by
  have := isMarkovKernel_inputKernel Hin
  rw [contentPreInputKernel, Kernel.comp_apply' _ _ _ (measurableSet_singleton 0),
    lintegral_pos_iff_support (Kernel.measurable_coe _ (measurableSet_singleton 0))]
  have hsupp : Function.support (fun y => recursionKernel G q y {0}) = univ := by
    refine eq_univ_of_forall fun y => ?_
    rw [Function.mem_support, recursionKernel_apply' G hq y (measurableSet_singleton 0)]
    refine (lt_of_lt_of_le (hG y) (measure_mono fun t ht => ?_)).ne'
    exact mem_singleton_iff.2 (hq0 y t ht)
  rw [hsupp, measure_univ]
  exact one_pos

/-- MT p. 88: under the hypotheses of `contentPreInput_zero_pos` the content-dependent storage
model is `δ₀`-irreducible. -/
theorem contentPreInput_isPhiIrreducible (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    (R : ℝ≥0 → ℝ) (hq0 : ∀ y t, R y < t → q (y, t) = 0) (hG : ∀ y, 0 < G (Ioi (R y))) :
    ∃ _ : IsMarkovKernel (contentPreInputKernel G q Hin),
      IsPhiIrreducible (contentPreInputKernel G q Hin) (Measure.dirac 0) := by
  have hM := isMarkovKernel_contentPreInputKernel G hq Hin
  refine ⟨hM, (isPhiIrreducible_dirac_iff _ 0).2 fun x => ?_⟩
  refine (hitProb_pos_iff _ (measurableSet_singleton 0) x).2 ⟨0, ?_⟩
  rw [zero_add, pow_one]
  exact contentPreInput_zero_pos G hq Hin R hq0 hG x

/-- MT p. 88: if the store never empties (`q(y, t) ≠ 0` for `y ≠ 0`, the case `R(y) = ∞`) and the
inputs are nonnegative, the empty state is never reached from a positive level. -/
theorem contentPreInput_hitProb_zero (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    [IsMarkovKernel (contentPreInputKernel G q Hin)]
    (hpos : ∀ y t, y ≠ 0 → q (y, t) ≠ 0) (hin : ∀ y, Hin y (Iio 0) = 0) {x : ℝ≥0}
    (hx : x ≠ 0) : hitProb (contentPreInputKernel G q Hin) {0} x = 0 := by
  have := isMarkovKernel_inputKernel Hin
  have hm : MeasurableSet ({0}ᶜ : Set ℝ≥0) := (measurableSet_singleton 0).compl
  have hAbs : IsAbsorbing (contentPreInputKernel G q Hin) {0}ᶜ := by
    intro y hy
    rw [← prob_compl_eq_zero_iff hm, compl_compl, contentPreInputKernel,
      Kernel.comp_apply' _ _ _ (measurableSet_singleton 0)]
    refine nonpos_iff_eq_zero.1 ?_
    calc ∫⁻ z, recursionKernel G q z {0} ∂inputKernel Hin y
        ≤ ∫⁻ z, ({0} : Set ℝ≥0).indicator 1 z ∂inputKernel Hin y := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z = 0
          · subst hz
            rw [indicator_of_mem (mem_singleton 0), Pi.one_apply]
            have := isMarkovKernel_recursionKernel G hq
            exact prob_le_one
          · rw [recursionKernel_apply' G hq z (measurableSet_singleton 0)]
            have : {t | q (z, t) ∈ ({0} : Set ℝ≥0)} = ∅ :=
              eq_empty_of_forall_notMem fun t ht => hpos z t hz (mem_singleton_iff.1 ht)
            rw [this, measure_empty]
            exact zero_le
      _ = inputKernel Hin y {0} := lintegral_indicator_one (measurableSet_singleton 0)
      _ ≤ 0 := by
          rw [inputKernel_apply, Measure.map_apply (f := fun s => Real.toNNReal (y + s))
            (measurable_halfLineStep.comp measurable_prodMk_left) (measurableSet_singleton 0),
            ← hin y]
          refine measure_mono fun s hs => ?_
          simp only [mem_preimage, mem_singleton_iff, Real.toNNReal_eq_zero] at hs
          have : (0 : ℝ) < y := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hy)
          exact mem_Iio.2 (by change (y : ℝ) + s ≤ 0 at hs; linarith)
  exact hAbs.hitProb_eq_zero hm (Set.disjoint_left.2 fun z hz h0 => hz h0) hx

/-- MT p. 88: with `R = ∞` (the store never empties) and nonnegative inputs, the content-dependent
storage model is not `δ₀`-irreducible. -/
theorem contentPreInput_not_isPhiIrreducible (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin]
    [IsMarkovKernel (contentPreInputKernel G q Hin)]
    (hpos : ∀ y t, y ≠ 0 → q (y, t) ≠ 0) (hin : ∀ y, Hin y (Iio 0) = 0) :
    ¬ IsPhiIrreducible (contentPreInputKernel G q Hin) (Measure.dirac 0) := by
  rw [isPhiIrreducible_dirac_iff]
  intro h
  have := h 1
  rw [contentPreInput_hitProb_zero G hq Hin hpos hin one_ne_zero] at this
  exact lt_irrefl _ this

end MeynTweedie.Irreducibility
