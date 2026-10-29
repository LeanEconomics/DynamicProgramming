/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.FellerChains
import GeneralizedDrift.ModelNonlinearModels
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Weak and strong Feller models (MT §6.1.1)

Meyn and Tweedie, §6.1.1, pp. 127–128.

* `isWeakFeller_recursionKernel`: a random recursion `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)` with `x ↦ F(x, w)`
  continuous for every `w` is weak Feller, on any first-countable space.
* **Proposition 6.1.2** (`proposition_6_1_2`, p. 127): the smooth nonlinear state space model
  NSS(F) is weak Feller, and maps bounded continuous functions to continuous functions.
* `translateMap`, `lsc_translate_of_finite`, `lsc_translate`: on a finite-dimensional real
  normed space with a Haar measure `μ`, `t ↦ ν{w : t + w ∈ B}` is lower semicontinuous for every
  finite `ν ≪ μ` and measurable `B` (continuity of translation in measure; this is the role of
  Lemma D.4.3 in the book).
* `lintegral_translate_volume` (p. 128): `∫ μ_Leb(dy) Γ(B − y) = μ_Leb(B)`.
* **Proposition 6.1.3** (`proposition_6_1_3`, p. 127): the unrestricted random walk on `ℝ` is weak
  Feller, and strong Feller iff `Γ ≪ μ_Leb`.

* The example (6.1)–(6.2) (pp. 124–125): `recipKernel α` moves from `1/n` to `1/(n + 1)` with
  probability `1 − αₙ` and to `0` with probability `αₙ`, and from every other point to `1`
  (`recipKernel_apply_recip`, `recipKernel_apply_of_notMem`, `isMarkovKernel_recipKernel`);
  `recipKernel_not_weakFeller_irreducible`: it is not weak Feller, and it is `δ₀`-irreducible
  when every `αₙ > 0`. The remarks on its instability when `Σ αₙ < ∞` and on continuous
  components when `αₙ → 0` are not formalised (informal).

**Hypotheses.** The book's NSS(F) lives on an open subset of `ℝⁿ`; here the state space is a
second-countable real normed space (for instance `ℝⁿ`).

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff symmDiff

/-- A random recursion `Φₙ₊₁ = F(Φₙ, Wₙ₊₁)` whose map `x ↦ F(x, w)` is continuous for every `w`
is weak Feller (the argument of MT Proposition 6.1.2, with Fatou's lemma in place of dominated
convergence). -/
theorem isWeakFeller_recursionKernel {X W : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [FirstCountableTopology X] [MeasurableSpace W] (Γ : Measure W)
    [SFinite Γ] {F : X × W → X} (hF : Measurable F) (hc : ∀ w, Continuous fun x => F (x, w)) :
    IsWeakFeller (recursionKernel Γ F) := by
  intro O hO
  have he : (fun x => recursionKernel Γ F x O) =
      fun x => ∫⁻ w, O.indicator 1 (F (x, w)) ∂Γ := by
    ext x
    have hm : MeasurableSet {w | F (x, w) ∈ O} :=
      (hF.comp measurable_prodMk_left) hO.measurableSet
    rw [recursionKernel_apply' Γ hF x hO.measurableSet, ← lintegral_indicator_one hm]
    refine lintegral_congr fun w => ?_
    by_cases h : F (x, w) ∈ O <;> simp [h]
  rw [he]
  refine lowerSemicontinuous_of_seq fun x z hz => ?_
  have hlsc : ∀ w, LowerSemicontinuous fun x => O.indicator (1 : X → ℝ≥0∞) (F (x, w)) :=
    fun w => by
      have : (fun x => O.indicator (1 : X → ℝ≥0∞) (F (x, w))) =
          ((fun x => F (x, w)) ⁻¹' O).indicator 1 := by
        ext x; by_cases h : F (x, w) ∈ O <;> simp [h]
      rw [this]
      exact (hO.preimage (hc w)).lowerSemicontinuous_indicator zero_le
  calc ∫⁻ w, O.indicator 1 (F (x, w)) ∂Γ
      ≤ ∫⁻ w, atTop.liminf (fun n => O.indicator (1 : X → ℝ≥0∞) (F (z n, w))) ∂Γ :=
        lintegral_mono fun w => le_liminf_seq_of_lsc (hlsc w) hz
    _ ≤ _ := lintegral_liminf_le fun n =>
        (measurable_one.indicator hO.measurableSet).comp (hF.comp measurable_prodMk_left)

/-- **Proposition 6.1.2** (MT p. 127): the nonlinear state space model NSS(F) with smooth `F` is
weak Feller, and `Ph(x) = E[h(F(x, W))]` is continuous for every bounded continuous `h`. -/
theorem proposition_6_1_2 {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (Γ : Measure V) [IsProbabilityMeasure Γ] {F : E × V → E} (hF : ContDiff ℝ ∞ F) :
    IsWeakFeller (nssKernel Γ F) ∧
      ∀ h : BoundedContinuousFunction E ℝ, Continuous fun x => ∫ y, h y ∂nssKernel Γ F x := by
  have hW : IsWeakFeller (nssKernel Γ F) := isWeakFeller_recursionKernel Γ
    hF.continuous.measurable fun w => hF.continuous.comp (Continuous.prodMk_left w)
  have := isMarkovKernel_nssKernel_of_contDiff Γ hF
  exact ⟨hW, (proposition_6_1_1_i_weak _).1 hW⟩

/-! ### Translates of absolutely continuous measures -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- The translations `w ↦ t + w` as a continuous family of continuous maps. -/
noncomputable def translateMap (t : G) : C(G, G) :=
  ContinuousMap.curry ⟨fun q : G × G => q.1 + q.2, continuous_add⟩ t

/-- For a finite measure `ν ≪ μ` (`μ` a Haar measure) and a set `B` with `μ(B) < ∞`,
`t ↦ ν{w : t + w ∈ B}` is lower semicontinuous (continuity of translation in measure; this
replaces Lemma D.4.3). -/
theorem lsc_translate_of_finite (μ : Measure G) [μ.IsAddHaarMeasure] {ν : Measure G}
    [IsFiniteMeasure ν] (hν : ν ≪ μ) {B : Set G} (hBm : MeasurableSet B) (hBfin : μ B ≠ ⊤) :
    LowerSemicontinuous fun t => ν {w | t + w ∈ B} := by
  intro t₀ y hy
  have hfg : Tendsto translateMap (𝓝 t₀) (𝓝 (translateMap t₀)) :=
    (ContinuousMap.curry _).continuous.tendsto t₀
  have hvol := tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) hfg
    (Eventually.of_forall fun t => measurePreserving_add_left μ t)
    (measurePreserving_add_left μ t₀) hBm.nullMeasurableSet hBfin
  have hνeq : μ.withDensity (ν.rnDeriv μ) = ν := Measure.withDensity_rnDeriv_eq ν μ hν
  have hint : ∫⁻ x, ν.rnDeriv μ x ∂μ ≠ ⊤ := by
    rw [Measure.lintegral_rnDeriv hν]
    exact measure_ne_top ν univ
  have hνt : Tendsto (fun t => ν ((translateMap t ⁻¹' B) ∆ (translateMap t₀ ⁻¹' B)))
      (𝓝 t₀) (𝓝 0) := by
    refine (tendsto_setLIntegral_zero hint hvol).congr fun t => ?_
    rw [← withDensity_apply', hνeq]
  have hε : 0 < ν (translateMap t₀ ⁻¹' B) - y := tsub_pos_of_lt hy
  filter_upwards [hνt.eventually (gt_mem_nhds hε)] with t ht
  have hle : ν (translateMap t₀ ⁻¹' B) ≤
      ν (translateMap t ⁻¹' B) + ν ((translateMap t ⁻¹' B) ∆ (translateMap t₀ ⁻¹' B)) := by
    have := le_measure_symmDiff (μ := ν) (s₁ := translateMap t₀ ⁻¹' B)
      (s₂ := translateMap t ⁻¹' B)
    rw [symmDiff_comm] at this
    rw [add_comm]
    exact tsub_le_iff_right.1 this
  by_contra hcon
  push Not at hcon
  have : ν (translateMap t₀ ⁻¹' B) < ν (translateMap t₀ ⁻¹' B) :=
    calc ν (translateMap t₀ ⁻¹' B) ≤
          y + ν ((translateMap t ⁻¹' B) ∆ (translateMap t₀ ⁻¹' B)) :=
          hle.trans (add_le_add_left hcon _)
      _ < y + (ν (translateMap t₀ ⁻¹' B) - y) := ENNReal.add_lt_add_left hy.ne_top ht
      _ = ν (translateMap t₀ ⁻¹' B) := add_tsub_cancel_of_le hy.le
  exact lt_irrefl _ this

/-- For a finite measure `ν ≪ μ` (`μ` a Haar measure on a finite-dimensional space),
`t ↦ ν{w : t + w ∈ B}` is lower semicontinuous for every measurable `B`. -/
theorem lsc_translate (μ : Measure G) [μ.IsAddHaarMeasure] {ν : Measure G}
    [IsFiniteMeasure ν] (hν : ν ≪ μ) {B : Set G} (hBm : MeasurableSet B) :
    LowerSemicontinuous fun t => ν {w | t + w ∈ B} := by
  have hU : ∀ t, ν {w | t + w ∈ B} =
      ⨆ R : ℕ, ν {w | t + w ∈ B ∩ Metric.ball (0 : G) R} := fun t => by
    rw [← Monotone.measure_iUnion]
    · congr 1
      ext w
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      refine ⟨fun h => ?_, fun ⟨_, h, _⟩ => h⟩
      obtain ⟨R, hR⟩ := exists_nat_gt ‖t + w‖
      exact ⟨R, h, hR⟩
    · intro R S hRS w hw
      exact ⟨hw.1, Metric.ball_subset_ball (by exact_mod_cast hRS) hw.2⟩
  have : (fun t => ν {w | t + w ∈ B}) =
      fun t => ⨆ R : ℕ, ν {w | t + w ∈ B ∩ Metric.ball (0 : G) R} := funext hU
  rw [this]
  exact lowerSemicontinuous_iSup fun R => lsc_translate_of_finite μ hν
    (hBm.inter Metric.isOpen_ball.measurableSet)
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne

/-! ### Proposition 6.1.3 -/

/-- Translation invariance and Fubini (MT p. 128): `∫ μ_Leb(dy) Γ(B − y) = μ_Leb(B)` for a
probability measure `Γ` on `ℝ`. -/
theorem lintegral_translate_volume (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {B : Set ℝ}
    (hB : MeasurableSet B) : ∫⁻ y, Γ {w | y + w ∈ B} ∂volume = volume B := by
  have hm : Measurable (Function.uncurry fun (y w : ℝ) => B.indicator (1 : ℝ → ℝ≥0∞) (y + w)) :=
    (measurable_one.indicator hB).comp measurable_add
  have h1 : ∀ y, Γ {w | y + w ∈ B} = ∫⁻ w, B.indicator 1 (y + w) ∂Γ := fun y => by
    have hmeas : MeasurableSet {w | y + w ∈ B} := (measurable_const_add y) hB
    rw [← lintegral_indicator_one hmeas]
    refine lintegral_congr fun w => ?_
    by_cases h : y + w ∈ B <;> simp [h]
  simp_rw [h1]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have h2 : ∀ w, ∫⁻ y, B.indicator (1 : ℝ → ℝ≥0∞) (y + w) ∂volume = volume B := fun w => by
    have hmeas : MeasurableSet {y | y + w ∈ B} := (measurable_add_const w) hB
    rw [← measure_preimage_add_right volume w B]
    change _ = volume {y | y + w ∈ B}
    rw [← lintegral_indicator_one hmeas]
    refine lintegral_congr fun y => ?_
    by_cases h : y + w ∈ B <;> simp [h]
  simp_rw [h2, lintegral_const, measure_univ, mul_one]

/-- **Proposition 6.1.3** (MT p. 127): the unrestricted random walk on `ℝ` is weak Feller, and it
is strong Feller iff the increment law `Γ` is absolutely continuous with respect to Lebesgue
measure. -/
theorem proposition_6_1_3 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsWeakFeller (randomWalkKernel Γ) ∧ (IsStrongFeller (randomWalkKernel Γ) ↔ Γ ≪ volume) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  refine ⟨isWeakFeller_recursionKernel Γ measurable_add_step
    fun w => continuous_id.add continuous_const, ?_⟩
  rw [proposition_6_1_1_i_strong]
  constructor
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
    by_contra hpos
    have hδ : 0 < Γ B := pos_iff_ne_zero.2 hpos
    have h0' : randomWalkKernel Γ 0 B = Γ B := by
      rw [randomWalkKernel_apply' Γ 0 hB]; simp
    have hev := h B hB 0 (Γ B / 2) (by
      change Γ B / 2 < randomWalkKernel Γ 0 B
      rw [h0']; exact ENNReal.half_lt_self hpos (measure_ne_top Γ B))
    have hfm : Measurable fun y => Γ {w | y + w ∈ B} := by
      simpa only [randomWalkKernel_apply' Γ _ hB] using
        Kernel.measurable_coe (randomWalkKernel Γ) hB
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hint := lintegral_translate_volume Γ hB
    rw [h0] at hint
    have hpos' : 0 < ∫⁻ y, Γ {w | y + w ∈ B} ∂volume := by
      calc (0 : ℝ≥0∞) < Γ B / 2 * volume (Metric.ball (0 : ℝ) ε) :=
            ENNReal.mul_pos (ENNReal.half_pos hpos).ne' (Metric.measure_ball_pos _ _ hε).ne'
        _ = ∫⁻ _ in Metric.ball (0 : ℝ) ε, Γ B / 2 ∂volume := by rw [setLIntegral_const]
        _ ≤ ∫⁻ y in Metric.ball (0 : ℝ) ε, Γ {w | y + w ∈ B} ∂volume :=
            setLIntegral_mono hfm fun y hy => by
              have : Γ B / 2 ≤ randomWalkKernel Γ y B := (hball hy).le
              rwa [randomWalkKernel_apply' Γ y hB] at this
        _ ≤ _ := setLIntegral_le_lintegral _ _
    exact absurd hint hpos'.ne'
  · intro h A hA
    have : (fun x => randomWalkKernel Γ x A) = fun x => Γ {w | x + w ∈ A} := by
      ext x; exact randomWalkKernel_apply' Γ x hA
    rw [this]
    exact lsc_translate volume h hA

/-! ### The example (6.1)–(6.2) -/

/-- The points `1/(n + 1)`, `n ≥ 0`, of the example (6.1)–(6.2). -/
def recipSet : Set ℝ := range fun n : ℕ => 1 / ((n : ℝ) + 1)

/-- `n ↦ 1/(n + 1)` is injective. -/
theorem recip_injective : Function.Injective fun n : ℕ => 1 / ((n : ℝ) + 1) := by
  intro m n h
  simp only [one_div, inv_inj] at h
  exact_mod_cast add_right_cancel h

/-- The law from `1/(n + 1)`: to `0` with probability `αₙ`, to `1/(n + 2)` otherwise. -/
noncomputable def recipStep (α : ℕ → ℝ≥0∞) (n : ℕ) : Measure ℝ :=
  α n • Measure.dirac 0 + (1 - α n) • Measure.dirac (1 / ((n : ℝ) + 2))

/-- The chain (6.1)–(6.2) on `ℝ` (MT p. 124): `P(1/n, 1/(n + 1)) = 1 − αₙ`, `P(1/n, 0) = αₙ`, and
`P(x, 1) = 1` at every other point. -/
noncomputable def recipKernel (α : ℕ → ℝ≥0∞) : Kernel ℝ ℝ where
  toFun x := Measure.sum (fun n : ℕ => ({1 / ((n : ℝ) + 1)} : Set ℝ).indicator
      (fun _ => recipStep α n) x) + recipSetᶜ.indicator (fun _ => Measure.dirac 1) x
  measurable' := by
    have hS : MeasurableSet recipSet := (countable_range _).measurableSet
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.add_apply, Measure.sum_apply _ hs]
    refine (Measurable.tsum fun n : ℕ => ?_).add ?_
    · have : (fun x : ℝ => (({1 / ((n : ℝ) + 1)} : Set ℝ).indicator (fun _ => recipStep α n) x)
          s) = ({1 / ((n : ℝ) + 1)} : Set ℝ).indicator (fun _ => recipStep α n s) := by
        ext x
        by_cases hx : x ∈ ({1 / ((n : ℝ) + 1)} : Set ℝ)
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx]; rfl
      rw [this]
      exact measurable_const.indicator (measurableSet_singleton _)
    · have : (fun x : ℝ => (recipSetᶜ.indicator (fun _ => Measure.dirac (1 : ℝ)) x) s) =
          recipSetᶜ.indicator (fun _ => Measure.dirac (1 : ℝ) s) := by
        ext x
        by_cases hx : x ∈ recipSetᶜ
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx]; rfl
      rw [this]
      exact measurable_const.indicator hS.compl

/-- `P(1/(n + 1), ·) = αₙ δ₀ + (1 − αₙ) δ_{1/(n+2)}`. -/
theorem recipKernel_apply_recip (α : ℕ → ℝ≥0∞) (n : ℕ) :
    recipKernel α (1 / ((n : ℝ) + 1)) = recipStep α n := by
  change Measure.sum _ + _ = _
  have hmem : (1 / ((n : ℝ) + 1)) ∈ recipSet := ⟨n, rfl⟩
  rw [indicator_of_notMem (show 1 / ((n : ℝ) + 1) ∉ recipSetᶜ from not_not.2 hmem), add_zero]
  ext s hs
  rw [Measure.sum_apply _ hs, tsum_eq_single n]
  · simp
  · intro m hm
    rw [indicator_of_notMem]
    · rfl
    · intro h
      exact hm (recip_injective (mem_singleton_iff.1 h).symm)

/-- `P(x, ·) = δ₁` off the points `1/(n + 1)`. -/
theorem recipKernel_apply_of_notMem (α : ℕ → ℝ≥0∞) {x : ℝ} (hx : x ∉ recipSet) :
    recipKernel α x = Measure.dirac 1 := by
  change Measure.sum _ + _ = _
  rw [indicator_of_mem (show x ∈ recipSetᶜ from hx)]
  have : (fun n : ℕ => ({1 / ((n : ℝ) + 1)} : Set ℝ).indicator (fun _ => recipStep α n) x) =
      0 := by
    ext1 n
    rw [indicator_of_notMem]
    · rfl
    · intro h; exact hx ⟨n, (mem_singleton_iff.1 h).symm⟩
  ext s hs
  rw [Measure.add_apply, Measure.sum_apply _ hs,
    ENNReal.tsum_eq_zero.2 fun i => by rw [congrFun this i]; rfl, zero_add]

/-- `0` is not one of the points `1/(n + 1)`. -/
theorem zero_notMem_recipSet : (0 : ℝ) ∉ recipSet := by
  rintro ⟨n, hn⟩
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- The chain (6.1)–(6.2) is a transition probability kernel when every `αₙ ≤ 1`. -/
theorem isMarkovKernel_recipKernel (α : ℕ → ℝ≥0∞) (hα1 : ∀ n, α n ≤ 1) :
    IsMarkovKernel (recipKernel α) := by
  refine ⟨fun x => ⟨?_⟩⟩
  by_cases hx : x ∈ recipSet
  · obtain ⟨n, rfl⟩ := hx
    rw [recipKernel_apply_recip]
    simp [recipStep, hα1 n]
  · rw [recipKernel_apply_of_notMem α hx]; simp

/-- **The example (6.1)–(6.2)** (MT pp. 124–125). The chain is not weak Feller (the Feller
property fails at `0`), whatever the `αₙ`; and if every `αₙ ∈ (0, 1]`, it is `δ₀`-irreducible. -/
theorem recipKernel_not_weakFeller_irreducible (α : ℕ → ℝ≥0∞) (hα1 : ∀ n, α n ≤ 1) :
    ¬ IsWeakFeller (recipKernel α) ∧
      ((∀ n, 0 < α n) →
        (haveI := isMarkovKernel_recipKernel α hα1;
          IsPhiIrreducible (recipKernel α) (Measure.dirac 0))) := by
  have hM := isMarkovKernel_recipKernel α hα1
  refine ⟨fun hW => ?_, fun hpos => ?_⟩
  · -- `P(·, (1/2, 3/2))` is `1` at `0` and `0` at every `1/(n + 2)`
    have hO : IsOpen (Ioo (1 / 2 : ℝ) (3 / 2)) := isOpen_Ioo
    have hlsc := hW _ hO 0 (1 / 2) (by
      change (1 / 2 : ℝ≥0∞) < recipKernel α 0 (Ioo (1 / 2) (3 / 2))
      rw [recipKernel_apply_of_notMem α zero_notMem_recipSet,
        Measure.dirac_apply' _ hO.measurableSet]
      norm_num)
    have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
    obtain ⟨n, hn⟩ := (hseq.eventually hlsc).exists
    have hval : recipKernel α (1 / ((n : ℝ) + 2)) (Ioo (1 / 2) (3 / 2)) = 0 := by
      have h2 : (1 / ((n : ℝ) + 2)) = 1 / (((n + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
      rw [h2, recipKernel_apply_recip]
      have h0 : (0 : ℝ) ∉ Ioo (1 / 2 : ℝ) (3 / 2) := by norm_num
      have h1 : 1 / (((n + 1 : ℕ) : ℝ) + 2) ∉ Ioo (1 / 2 : ℝ) (3 / 2) := by
        intro h
        have : 1 / (((n + 1 : ℕ) : ℝ) + 2) ≤ 1 / 3 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; linarith
        linarith [h.1]
      simp only [recipStep, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' _ hO.measurableSet, indicator_of_notMem h0, indicator_of_notMem h1,
        mul_zero, add_zero]
    have hn' : (1 / 2 : ℝ≥0∞) < recipKernel α (1 / ((n : ℝ) + 2)) (Ioo (1 / 2) (3 / 2)) := hn
    rw [hval] at hn'
    exact absurd hn' (by simp)
  · -- every state reaches `0`
    refine (isPhiIrreducible_dirac_iff _ 0).2 fun x => ?_
    have hrecip : ∀ n : ℕ, 0 < hitProb (recipKernel α) {0} (1 / ((n : ℝ) + 1)) := fun n =>
      (hitProb_pos_iff _ (measurableSet_singleton 0) _).2 ⟨0, by
        rw [zero_add, pow_one, recipKernel_apply_recip]
        simp only [recipStep, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply_of_mem (mem_singleton (0 : ℝ)), mul_one]
        exact lt_of_lt_of_le (hpos n) le_self_add⟩
    by_cases hx : x ∈ recipSet
    · obtain ⟨n, rfl⟩ := hx
      exact hrecip n
    · -- one step to `1 = 1/(0 + 1)`, then to `0`
      have h1 := hrecip 0
      rw [hitProb_pos_iff _ (measurableSet_singleton 0)] at h1 ⊢
      obtain ⟨m, hm⟩ := h1
      refine ⟨m + 1, ?_⟩
      rw [show m + 1 + 1 = 1 + (m + 1) by omega,
        pow_add_pos_iff _ 1 (m + 1) x (measurableSet_singleton 0), pow_one,
        recipKernel_apply_of_notMem α hx]
      rw [Measure.dirac_apply' _ ((measurableSet_lt measurable_const
        (Kernel.measurable_coe _ (measurableSet_singleton 0))))]
      have : (1 : ℝ) ∈ {y | 0 < (recipKernel α ^ (m + 1)) y {0}} := by
        simpa using hm
      simp [this]

end MeynTweedie.GeneralizedDrift
