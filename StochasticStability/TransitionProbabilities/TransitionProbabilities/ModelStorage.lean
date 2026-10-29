/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransitionProbabilities.ModelQueues
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Storage models

Copied from the `MarkovModels` project (`MarkovModels/Storage.lean`), with the namespace
renamed to `MeynTweedie.TransitionProbabilities`.

MT, §2.4.3–2.4.4, pp. 43–46, the Commentary, p. 47, and (SSM1)–(SSM2), (CSM1)–(CSM2) of
Appendix C, p. 545.

* `storageKernel H G r`: the simple storage model (Moran dam), `Φₙ₊₁ = [Φₙ + Sₙ − Jₙ]⁺` with
  inputs `S ~ H`, interarrival times `T ~ G` and release `J = rT` (MT, (SSM1)–(SSM2), p. 44). It
  is random walk on a half line with increment `W = S − J` (`storageKernel_eq_halfLineWalk`,
  MT, p. 44). The law of `J` satisfies (2.31), `P(J ≤ x) = G(−∞, x/r]` (`releaseLaw_Iic`), and
  the mean increment is `α − β`, mean input minus mean output (`storage_mean_increment`, MT,
  p. 44). With `r = 1` the model is the GI/G/1 waiting time chain (`storageKernel_one`, MT,
  p. 47).
* `releaseTime r x = ∫₀ˣ r(y)⁻¹ dy` (MT, (2.32), p. 45): strictly increasing for a positive
  continuous rate (`releaseTime_strictMonoOn`), and maps `[0, x]` one-to-one onto `[0, R(x)]`
  (`releaseTime_bijOn`), so `q(x, t) = R⁻¹(R(x) − t)` is well defined for `0 ≤ t ≤ R(x)`.
  **Correction:** MT say `R⁻¹(t)` is defined for all `t`; for `r(y) = 1 + y²`, `R = arctan` never
  reaches `π/2` (`releaseTime_not_surjective`).
* `contentKernel G q Hin`: the content-dependent storage model as printed in (CSM2), MT, p. 46,
  `Φₙ₊₁ = [Φₙ − Jₙ + Sₙ(Φₙ − Jₙ)]⁺`: release over an interarrival time (the level `q(x, T)`),
  then an input with level-dependent law `H_y`. The law of `Jₙ` is (2.33)
  (`contentRelease_Iic`), and `contentKernel_apply'` gives the transition law.
  **Correction:** that order (release, then input) gives the content just *after* inputs, not just
  before them as MT state; with constant release rate and input law it is not the simple storage
  model (`contentKernel_ne_storageKernel`). The content before inputs is `contentPreInputKernel`
  (input, then release), which reduces to the simple storage model
  (`contentPreInputKernel_eq_storageKernel`).
-/

namespace MeynTweedie.TransitionProbabilities

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-! ### The simple storage model -/

/-- The simple storage step `Φ' = [Φ + S − rT]⁺` with disturbance `(S, T)`. -/
noncomputable def storageStep (r : ℝ) (p : ℝ≥0 × (ℝ × ℝ)) : ℝ≥0 :=
  Real.toNNReal (p.1 + p.2.1 - r * p.2.2)

/-- The storage step is measurable. -/
theorem measurable_storageStep (r : ℝ) : Measurable (storageStep r) :=
  (((measurable_coe_nnreal_real.comp measurable_fst).add
    (measurable_fst.comp measurable_snd)).sub
      (measurable_const.mul (measurable_snd.comp measurable_snd))).real_toNNReal

/-- The simple storage model with release rate `r` (MT, (SSM1)–(SSM2), p. 44): the contents
`Φₙ` just before the `n`-th input, with inputs `S ~ H` and interarrival times `T ~ G`
independent. -/
noncomputable def storageKernel (H G : Measure ℝ) (r : ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel (H.prod G) (storageStep r)

/-- The simple storage model is a Markov kernel. -/
theorem isMarkovKernel_storageKernel (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (r : ℝ) : IsMarkovKernel (storageKernel H G r) :=
  isMarkovKernel_recursionKernel _ (measurable_storageStep r)

/-- MT, p. 44: the simple storage model is random walk on a half line with increments
`Wₙ = Sₙ − Jₙ`, `Jₙ = rTₙ`. -/
theorem storageKernel_eq_halfLineWalk (H G : Measure ℝ) [SFinite H] [SFinite G] (r : ℝ) :
    storageKernel H G r = halfLineWalkKernel ((H.prod G).map fun p => p.1 - r * p.2) := by
  rw [halfLineWalkKernel, ← recursionKernel_comp_noise _ measurable_halfLineStep
    (g := fun p : ℝ × ℝ => p.1 - r * p.2)
    (measurable_fst.sub (measurable_const.mul measurable_snd)), storageKernel]
  congr 1
  funext p
  simp only [storageStep, halfLineStep, add_sub_assoc]

/-- (2.31), MT p. 44: the release `J = rT` between inputs has `P(J ≤ x) = G(−∞, x/r]`. -/
theorem releaseLaw_Iic (G : Measure ℝ) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (G.map (r * ·)) (Iic x) = G (Iic (x / r)) := by
  rw [Measure.map_apply (measurable_const_mul r) measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_preimage, mem_Iic]
  rw [le_div_iff₀ hr, mul_comm]

/-- The commentary of MT, p. 47: the residual workload of the GI/G/1 queue is the storage model
with unit release rate. -/
theorem storageKernel_one (H G : Measure ℝ) : storageKernel H G 1 = waitingTimeKernel H G := by
  rw [storageKernel, waitingTimeKernel]
  congr 1
  funext p
  simp only [storageStep, lindleyStep, one_mul]

/-- MT, p. 44: the mean increment of the storage model is `α − β`, the mean input
`α = ∫ x H(dx)` minus the mean output between inputs `β = ∫ rx G(dx)`. -/
theorem storage_mean_increment (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH : Integrable id H) (hG : Integrable id G) (r : ℝ) :
    ∫ w, w ∂((H.prod G).map fun p => p.1 - r * p.2) = (∫ x, x ∂H) - ∫ x, r * x ∂G := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - r * p.2 :=
    measurable_fst.sub (measurable_const.mul measurable_snd)
  rw [integral_map (f := fun w : ℝ => w) hm.aemeasurable measurable_id.aestronglyMeasurable]
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (H.prod G) := hH.comp_fst G
  have h2 : Integrable (fun p : ℝ × ℝ => r * p.2) (H.prod G) := (hG.const_mul r).comp_snd H
  rw [integral_sub h1 h2, integral_fun_fst (fun x : ℝ => x),
    integral_fun_snd (fun x : ℝ => r * x)]
  simp

/-! ### Content-dependent release -/

/-- The time to empty from level `x` without input, `R(x) = ∫₀ˣ r(y)⁻¹ dy` (MT, (2.32), p. 45). -/
noncomputable def releaseTime (r : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, (r y)⁻¹

/-- `R` is continuous for a positive continuous release rate. -/
theorem continuous_releaseTime {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) :
    Continuous (releaseTime r) :=
  intervalIntegral.continuous_primitive
    (fun a b => (hr.inv₀ fun y => (hpos y).ne').intervalIntegrable a b) 0

/-- MT, p. 45: `R` is strictly increasing for a positive continuous release rate. -/
theorem releaseTime_strictMono {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) :
    StrictMono (releaseTime r) := by
  intro a b hab
  have hint : ∀ c d, IntervalIntegrable (fun y => (r y)⁻¹) MeasureSpace.volume c d :=
    fun c d => (hr.inv₀ fun y => (hpos y).ne').intervalIntegrable c d
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)
  have hpos' : 0 < ∫ y in a..b, (r y)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint a b)
      (fun y _ => inv_pos.mpr (hpos y)) hab
  simp only [releaseTime]
  linarith

/-- `R` is strictly increasing on `[0, ∞)`. -/
theorem releaseTime_strictMonoOn {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) :
    StrictMonoOn (releaseTime r) (Ici 0) :=
  (releaseTime_strictMono hr hpos).strictMonoOn _

/-- **Corrected inverse.** For a positive continuous release rate and `x ≥ 0`, `R` maps `[0, x]`
one-to-one onto `[0, R(x)]`. Hence `q(x, t) = R⁻¹(R(x) − t)` is well defined for
`0 ≤ t ≤ R(x)`, which is all the model uses. -/
theorem releaseTime_bijOn {r : ℝ → ℝ} (hr : Continuous r) (hpos : ∀ y, 0 < r y) {x : ℝ}
    (hx : 0 ≤ x) : BijOn (releaseTime r) (Icc 0 x) (Icc 0 (releaseTime r x)) := by
  have hmono := releaseTime_strictMono hr hpos
  have h0 : releaseTime r 0 = 0 := intervalIntegral.integral_same
  refine ⟨fun y hy => ⟨?_, hmono.monotone hy.2⟩, (hmono.strictMonoOn _).injOn, fun s hs => ?_⟩
  · rw [← h0]
    exact hmono.monotone hy.1
  · rw [← h0] at hs
    exact intermediate_value_Icc hx (continuous_releaseTime hr hpos).continuousOn hs

/-- `R(x) = arctan x` for the release rate `r(y) = 1 + y²`. -/
theorem releaseTime_one_add_sq (x : ℝ) : releaseTime (fun y => 1 + y ^ 2) x = Real.arctan x := by
  simp only [releaseTime, ← one_div]
  rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]

/-- **Correction to MT, p. 45.** `R⁻¹(t)` need not be defined for all `t ≥ 0`: for
`r(y) = 1 + y²` the time to empty is `R(x) = arctan x < π/2` for every level `x`. -/
theorem releaseTime_not_surjective :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ x, releaseTime (fun y => 1 + y ^ 2) x ≠ t :=
  ⟨Real.pi / 2, by positivity, fun x => by
    rw [releaseTime_one_add_sq]
    exact (Real.arctan_lt_pi_div_two x).ne⟩

/-- The input kernel `y ↦ law of [y + S(y)]⁺` with `S(y) ~ H_y`. -/
noncomputable def inputKernel (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  (Kernel.id ×ₖ Hin).map halfLineStep

/-- The input kernel at `y` is the image of `H_y` under `s ↦ [y + s]⁺`. -/
theorem inputKernel_apply (Hin : Kernel ℝ≥0 ℝ) [IsSFiniteKernel Hin] (y : ℝ≥0) :
    inputKernel Hin y = (Hin y).map fun s => Real.toNNReal (y + s) := by
  rw [inputKernel, Kernel.map_apply _ measurable_halfLineStep, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map measurable_halfLineStep measurable_prodMk_left]
  rfl

/-- The content-dependent storage model as printed in (CSM2), MT p. 46: from level `x`, release
for an interarrival time `T ~ G` to the level `q(x, T)` (so `J = x − q(x, T)`), then add an input
`S ~ H_y` with `y = q(x, T)`. -/
noncomputable def contentKernel (G : Measure ℝ) (q : ℝ≥0 × ℝ → ℝ≥0) (Hin : Kernel ℝ≥0 ℝ) :
    Kernel ℝ≥0 ℝ≥0 :=
  inputKernel Hin ∘ₖ recursionKernel G q

/-- The content-dependent storage model taken just before inputs: add the input `S ~ H_x`, then
release for an interarrival time `T ~ G`. -/
noncomputable def contentPreInputKernel (G : Measure ℝ) (q : ℝ≥0 × ℝ → ℝ≥0)
    (Hin : Kernel ℝ≥0 ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel G q ∘ₖ inputKernel Hin

/-- Both content-dependent kernels are Markov kernels. -/
theorem isMarkovKernel_contentKernel (G : Measure ℝ) [IsProbabilityMeasure G]
    {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (Hin : Kernel ℝ≥0 ℝ) [IsMarkovKernel Hin] :
    IsMarkovKernel (contentKernel G q Hin) ∧ IsMarkovKernel (contentPreInputKernel G q Hin) := by
  have := isMarkovKernel_recursionKernel G hq
  have : IsMarkovKernel (inputKernel Hin) := by
    unfold inputKernel
    exact Kernel.IsMarkovKernel.map _ measurable_halfLineStep
  exact ⟨by unfold contentKernel; infer_instance, by unfold contentPreInputKernel; infer_instance⟩

/-- (2.33), MT p. 46: given `Φₙ = x`, the release `Jₙ = x − q(x, Tₙ)` has
`P(Jₙ ≤ y) = ∫ G(dt) 1{J_x(t) ≤ y}`. -/
theorem contentRelease_Iic (G : Measure ℝ) {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q) (x : ℝ≥0)
    (y : ℝ) :
    (G.map fun t => (x : ℝ) - q (x, t)) (Iic y) =
      ∫⁻ t, (Iic y).indicator 1 ((x : ℝ) - q (x, t)) ∂G := by
  have hm : Measurable fun t => (x : ℝ) - q (x, t) :=
    measurable_const.sub (measurable_coe_nnreal_real.comp (hq.comp measurable_prodMk_left))
  rw [Measure.map_apply hm measurableSet_Iic, ← lintegral_indicator_one (hm measurableSet_Iic)]
  rfl

/-- The transition law of (CSM2): `P(x, A) = ∫ G(dt) H_{q(x,t)}{s : [q(x, t) + s]⁺ ∈ A}`. -/
theorem contentKernel_apply' (G : Measure ℝ) [SFinite G] {q : ℝ≥0 × ℝ → ℝ≥0} (hq : Measurable q)
    (Hin : Kernel ℝ≥0 ℝ) [IsSFiniteKernel Hin] (x : ℝ≥0) {A : Set ℝ≥0} (hA : MeasurableSet A) :
    contentKernel G q Hin x A =
      ∫⁻ t, Hin (q (x, t)) {s | Real.toNNReal (q (x, t) + s) ∈ A} ∂G := by
  rw [contentKernel, Kernel.comp_apply' _ _ _ hA, recursionKernel_apply G hq,
    lintegral_map (g := fun w => q (x, w)) (Kernel.measurable_coe _ hA)
      (hq.comp measurable_prodMk_left)]
  refine lintegral_congr fun t => ?_
  rw [inputKernel_apply, Measure.map_apply (f := fun s => Real.toNNReal (q (x, t) + s))
    (measurable_halfLineStep.comp measurable_prodMk_left) hA]
  rfl

/-- **Correction to (CSM2).** With constant release rate `1` (`q(x, t) = [x − t]⁺`), unit inputs
and unit interarrival times, (CSM2) moves from `0` to `1` with probability one, whereas the
contents just before inputs, the simple storage model, stay at `0`. -/
theorem contentKernel_ne_storageKernel :
    contentKernel (Measure.dirac 1) (fun p => Real.toNNReal (p.1 - p.2))
        (Kernel.const ℝ≥0 (Measure.dirac 1)) 0 {1} ≠
      storageKernel (Measure.dirac 1) (Measure.dirac 1) 1 0 {1} := by
  have hq : Measurable fun p : ℝ≥0 × ℝ => Real.toNNReal (p.1 - p.2) :=
    ((measurable_coe_nnreal_real.comp measurable_fst).sub measurable_snd).real_toNNReal
  rw [contentKernel_apply' _ hq _ 0 (measurableSet_singleton 1), lintegral_dirac,
    storageKernel,
    recursionKernel_apply' _ (measurable_storageStep 1) 0 (measurableSet_singleton 1),
    Measure.dirac_prod_dirac, Kernel.const_apply, Measure.dirac_apply, Measure.dirac_apply]
  norm_num [indicator, storageStep]

/-- **Corrected content-dependent model.** With constant release rate `r ≥ 0`
(`q(x, t) = [x − rt]⁺`), level-independent input law `H` and interarrival law `G` on `[0, ∞)`,
the content just before inputs is the simple storage model. -/
theorem contentPreInputKernel_eq_storageKernel (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hG : G (Iio 0) = 0) {r : ℝ} (hr : 0 ≤ r) :
    contentPreInputKernel G (fun p => Real.toNNReal (p.1 - r * p.2)) (Kernel.const ℝ≥0 H) =
      storageKernel H G r := by
  have hq : Measurable fun p : ℝ≥0 × ℝ => Real.toNNReal (p.1 - r * p.2) :=
    ((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_const.mul measurable_snd)).real_toNNReal
  ext x A hA
  rw [contentPreInputKernel, Kernel.comp_apply' _ _ _ hA, inputKernel_apply, Kernel.const_apply,
    lintegral_map (g := fun s : ℝ => Real.toNNReal (x + s)) (Kernel.measurable_coe _ hA)
      (measurable_halfLineStep.comp measurable_prodMk_left),
    storageKernel, recursionKernel_apply' _ (measurable_storageStep r) x hA,
    Measure.prod_apply (s := {w | storageStep r (x, w) ∈ A})
      ((measurable_storageStep r).comp measurable_prodMk_left hA)]
  refine lintegral_congr fun s => ?_
  rw [recursionKernel_apply' G hq _ hA]
  refine measure_congr ?_
  have hae : ∀ᵐ t ∂G, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hG
  filter_upwards [hae] with t ht
  change (Real.toNNReal ((Real.toNNReal (x + s) : ℝ) - r * t) ∈ A) =
    (Real.toNNReal (x + s - r * t) ∈ A)
  have hrt : 0 ≤ r * t := mul_nonneg hr ht
  have hkey : Real.toNNReal ((Real.toNNReal (x + s) : ℝ) - r * t) =
      Real.toNNReal (x + s - r * t) := by
    rcases le_or_gt 0 ((x : ℝ) + s) with h | h
    · rw [Real.coe_toNNReal _ h]
    · rw [Real.toNNReal_of_nonpos h.le, NNReal.coe_zero, Real.toNNReal_of_nonpos (by linarith),
        Real.toNNReal_of_nonpos (by linarith)]
  rw [hkey]

end MeynTweedie.TransitionProbabilities
