/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.InvariantFields
import GeneralizedDrift.MaximalIrreducibility
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The LLN for positive Harris chains (MT §17.1.1, §17.1.3)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/HarrisLLN.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Theorem 17.1.2 (p. 424) and Theorem 17.1.7 (p. 427). The sums are
`pathSum g n = Sₙ(g) = Σ_{k=1}^n g(Φₖ)` (17.1); `pathSum_eq_birkhoffSum` identifies them with
the Birkhoff sums of `ω ↦ g(ω₁)` under the shift, so that `BirkhoffErgodic` applies to the
stationary chain `P_π`.

**Tools.**
* `shift_one_iterate`: `θ¹` iterated `k` times is `θᵏ`; `measurePreserving_shift`: under an
  invariant probability `π` every `θᵏ` preserves `P_π`.
* `llnSet g c`, the event `{(1/n) Sₙ(g) → c}`, is measurable (`measurableSet_llnSet`) and
  shift-invariant (`isShiftInvariant_llnSet`).
* `ergodic_pathMeasure`: for a Harris chain with invariant probability `π`, every strictly
  invariant event has `P_π`-probability `0` or `1` (Theorems 17.1.3 and 17.1.5).

**Results.**
* **Theorem 17.1.2** (`theorem_17_1_2`, p. 424): for an invariant probability `π` and
  `Y ∈ L¹(P_π)`, there is a set `F_Y` of full `π`-measure such that for `x ∈ F_Y`,
  `(1/N) Σ_{k=1}^N θᵏY → Y_∞(x)`, `P_x`-a.s.; `theorem_17_1_2_condExp`: `Y_∞(Φ₀)` is the
  conditional expectation of `Y` on the invariant σ-field (`∫_E Y_∞(Φ₀) = ∫_E Y` on strictly
  invariant `E`). No irreducibility is assumed.
* `lln_of_harris`: the LLN `(1/n) Sₙ(f) → π(f)`, `P_x`-a.s. for every `x`, for a Harris chain
  with an invariant probability and `f ∈ L¹(π)`; `lln_of_harris_measure` for every initial law.
* **Theorem 17.1.7** (`theorem_17_1_7`, p. 427): for a chain with an invariant probability `π`,
  (i) positive Harris, (ii) the LLN for every `f ∈ L¹(π)` from every state, and (iii) every
  invariant event has `P_μ`-probability `0` or `1` for every initial law `μ`, are equivalent.

**Correction.** Theorem 17.1.7 (iii) asks only that `Σ` be `P_x`-trivial for every `x`. That is
not enough: `theorem_17_1_7_counterexample` is the identity chain on `Bool` with `π = δ_true`,
for which every event has `P_x`-probability `0` or `1` (each `P_x` is a point mass on path space)
but the chain is not positive Harris. The proof of (iii) ⇒ (i) needs `Q(·, A)` constant, which
uses triviality under mixtures of two point masses; (iii) is therefore stated for every initial
distribution, as in Proposition 17.1.4.

**Hypotheses.** Theorem 17.1.7 and the LLN use Theorem 9.1.4, hence a countably generated
σ-algebra on `X`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Partial sums and the shift -/

/-- The partial sums `Sₙ(g) = Σ_{k=1}^n g(Φₖ)` (17.1), MT p. 421. -/
def pathSum (g : X → ℝ) (n : ℕ) (ω : ℕ → X) : ℝ := ∑ k ∈ Finset.range n, g (ω (k + 1))

omit [MeasurableSpace X] in
/-- `θ¹` iterated `k` times is `θᵏ`. -/
theorem shift_one_iterate (k : ℕ) (ω : ℕ → X) : (shift 1)^[k] ω = shift k ω := by
  induction k generalizing ω with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, shift_shift]
    congr 1
    omega

omit [MeasurableSpace X] in
/-- `Sₙ(g)` is the Birkhoff sum of `ω ↦ g(ω₁)` under the shift. -/
theorem pathSum_eq_birkhoffSum (g : X → ℝ) (n : ℕ) (ω : ℕ → X) :
    pathSum g n ω = birkhoffSum (shift 1) (fun ω => g (ω 1)) n ω := by
  unfold pathSum birkhoffSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shift_one_iterate]
  rfl

omit [MeasurableSpace X] in
/-- `Sₙ(g)/n` is the Birkhoff average of `ω ↦ g(ω₁)`. -/
theorem pathSum_div_eq_birkhoffAverage (g : X → ℝ) (n : ℕ) (ω : ℕ → X) :
    pathSum g n ω / n = birkhoffAverage ℝ (shift 1) (fun ω => g (ω 1)) n ω := by
  rw [birkhoffAverage_eq_div, pathSum_eq_birkhoffSum]

/-- `Sₙ(g)` is measurable. -/
theorem measurable_pathSum {g : X → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (pathSum g n) :=
  Finset.measurable_sum _ fun k _ => hg.comp (measurable_pi_apply (k + 1))

/-- Under an invariant probability `π`, every `θᵏ` preserves `P_π`. -/
theorem measurePreserving_shift {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (k : ℕ) :
    MeasurePreserving (shift k) (pathMeasure P π) (pathMeasure P π) :=
  ⟨measurable_shift k, hπ.map_shift k⟩

/-- The set where a sequence of measurable functions converges to a measurable function is
measurable. -/
theorem measurableSet_tendsto_fun {β : Type*} [MeasurableSpace β] {F : ℕ → β → ℝ}
    {G : β → ℝ} (hF : ∀ n, Measurable (F n)) (hG : Measurable G) :
    MeasurableSet {ω | Tendsto (fun n => F n ω) atTop (𝓝 (G ω))} := by
  have : {ω | Tendsto (fun n => F n ω) atTop (𝓝 (G ω))} =
      {ω | Tendsto (fun n => F n ω - G ω) atTop (𝓝 0)} := by
    ext ω
    simp only [mem_ofPred_eq, tendsto_sub_nhds_zero_iff]
  rw [this]
  exact measurableSet_tendsto (𝓝 0) fun n => (hF n).sub hG

/-- The LLN event `{(1/n) Sₙ(g) → c}`. -/
def llnSet (g : X → ℝ) (c : ℝ) : Set (ℕ → X) :=
  {ω | Tendsto (fun n => pathSum g n ω / n) atTop (𝓝 c)}

/-- The LLN event is measurable. -/
theorem measurableSet_llnSet {g : X → ℝ} (hg : Measurable g) (c : ℝ) :
    MeasurableSet (llnSet g c) :=
  measurableSet_tendsto (𝓝 c) fun n => (measurable_pathSum hg n).div_const _

omit [MeasurableSpace X] in
/-- The LLN event is shift-invariant. -/
theorem isShiftInvariant_llnSet (g : X → ℝ) (c : ℝ) : IsShiftInvariant (llnSet g c) := by
  intro m ω
  induction m generalizing ω with
  | zero => simp
  | succ m ih =>
    rw [← shift_shift 1 m, show shift 1 (shift m ω) ∈ llnSet g c ↔ shift m ω ∈ llnSet g c from ?_,
      ih]
    simp only [llnSet, mem_ofPred_eq, pathSum_div_eq_birkhoffAverage]
    exact ⟨tendsto_birkhoffAverage_of_apply, tendsto_birkhoffAverage_apply⟩

/-! ### Theorem 17.1.2 -/

omit [MeasurableSpace X] in
/-- Under an invariant probability, the Birkhoff limit of `Y` along the shift is `P_π`-invariant:
if the averages converge at `ω`, they converge to the same limit at every `θᵏω`. -/
theorem tendsto_birkhoffAverage_shift {f : (ℕ → X) → ℝ} {ω : ℕ → X} {c : ℝ}
    (h : Tendsto (fun n => birkhoffAverage ℝ (shift 1) f n ω) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n => birkhoffAverage ℝ (shift 1) f n (shift k ω)) atTop (𝓝 c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := tendsto_birkhoffAverage_apply ih
    rwa [shift_shift] at this

/-- **Theorem 17.1.2** (MT p. 424, Doob): let `π` be an invariant probability and `Y ∈ L¹(P_π)`.
Then for `π`-almost every `x` (a measurable set `F_Y` of full measure),
`(1/N) Σ_{k=1}^N Y(θᵏΦ) → Y_∞(x)`, `P_x`-a.s., where `Y_∞ = h_L` for the Birkhoff limit `L`. -/
theorem theorem_17_1_2 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {Y : (ℕ → X) → ℝ} (hYm : Measurable Y)
    (hYi : Integrable Y (pathMeasure P π)) :
    ∃ F : Set X, MeasurableSet F ∧ π Fᶜ = 0 ∧ ∀ x ∈ F, ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, Y (shift (k + 1) ω)) atTop
        (𝓝 (expectFn P (birkhoffLimit (shift 1) fun ω => Y (shift 1 ω)) x)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hmp := measurePreserving_shift hπ 1
  set f : (ℕ → X) → ℝ := fun ω => Y (shift 1 ω) with hf
  have hfm : Measurable f := hYm.comp (measurable_shift 1)
  have hfi : Integrable f (pathMeasure P π) := hmp.integrable_comp_of_integrable hYi
  set L := birkhoffLimit (shift 1) f with hL
  have hLm : Measurable L := measurable_birkhoffLimit (measurable_shift 1) hfm
  have hconv := ae_tendsto_birkhoffLimit hmp hfm hfi
  have hLinv : IsPathInvariant P π L := by
    intro k
    filter_upwards [hconv] with ω hω
    exact ((tendsto_birkhoffAverage_shift hω k).limUnder_eq).trans hω.limUnder_eq.symm
  have hLi := (integrable_birkhoffLimit hmp hfm hfi).1
  have h11 := lemma_17_1_1 P hπ hLm hLi hLinv
  set Yinf := expectFn P L with hYinf
  have hYinfm : Measurable Yinf := measurable_expectFn P hLm
  -- the event `B = {averages → Y_∞(Φ₀)}` has `P_π`-probability one
  set avg : ℕ → (ℕ → X) → ℝ := fun N ω => birkhoffAverage ℝ (shift 1) f N ω with havg
  have havgm : ∀ N, Measurable (avg N) := fun N =>
    measurable_birkhoffAverage (measurable_shift 1) hfm N
  set B := {ω : ℕ → X | Tendsto (fun N => avg N ω) atTop (𝓝 (Yinf (ω 0)))} with hB
  have hBm : MeasurableSet B :=
    measurableSet_tendsto_fun havgm (hYinfm.comp (measurable_pi_apply 0))
  have hBc : pathMeasure P π Bᶜ = 0 := by
    have hae : ∀ᵐ ω ∂pathMeasure P π, ω ∈ B := by
      filter_upwards [hconv, h11] with ω h1 h2
      rwa [show birkhoffLimit (shift 1) f ω = Yinf (ω 0) from h2] at h1
    exact mem_ae_iff.1 hae
  rw [pathMeasure_eq_comp, Measure.bind_apply hBm.compl (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hBm.compl)] at hBc
  refine ⟨{x | pathKernel P x Bᶜ = 0},
    (Kernel.measurable_coe _ hBm.compl) (measurableSet_singleton 0), ?_, fun x hx => ?_⟩
  · have hae : ∀ᵐ x ∂π, pathKernel P x Bᶜ = 0 := hBc
    exact mem_ae_iff.1 hae
  · -- under `P_x`, `Y_∞(Φ₀) = Y_∞(x)` almost surely
    have hA : MeasurableSet (Yinf ⁻¹' {Yinf x}ᶜ) := hYinfm (measurableSet_singleton _).compl
    have h0 : pathKernel P x {ω | ω 0 ∈ Yinf ⁻¹' {Yinf x}ᶜ} = 0 := by
      rw [pathKernel_zero_mem P x hA, indicator_of_notMem (by simp)]
    have hxB : ∀ᵐ ω ∂pathKernel P x, ω ∈ B := by rw [ae_iff]; exact hx
    have hx0 : ∀ᵐ ω ∂pathKernel P x, Yinf (ω 0) = Yinf x := by
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      simpa using hω
    filter_upwards [hxB, hx0] with ω h1 h2
    have h1' : Tendsto (fun N => avg N ω) atTop (𝓝 (Yinf x)) := by
      have : ω ∈ B := h1
      rwa [hB, mem_ofPred_eq, h2] at this
    refine h1'.congr fun N => ?_
    simp only [havg, hf, birkhoffAverage, birkhoffSum, smul_eq_mul, shift_one_iterate,
      shift_shift]

/-- **Theorem 17.1.2**, the identification of the limit (MT p. 424): `Y_∞(Φ₀)` is the
conditional expectation of `Y` given the invariant σ-field, `∫_E Y_∞(Φ₀) dP_π = ∫_E Y dP_π` for
every strictly invariant event `E`, and it is the Birkhoff limit `P_π`-a.s. -/
theorem theorem_17_1_2_condExp (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {Y : (ℕ → X) → ℝ} (hYm : Measurable Y)
    (hYi : Integrable Y (pathMeasure P π)) :
    (birkhoffLimit (shift 1) fun ω => Y (shift 1 ω)) =ᵐ[pathMeasure P π]
        (fun ω => expectFn P (birkhoffLimit (shift 1) fun ω => Y (shift 1 ω)) (ω 0)) ∧
      ∀ E : Set (ℕ → X), MeasurableSet E → shift 1 ⁻¹' E = E →
        ∫ ω in E, expectFn P (birkhoffLimit (shift 1) fun ω => Y (shift 1 ω)) (ω 0)
          ∂pathMeasure P π = ∫ ω in E, Y ω ∂pathMeasure P π := by
  have := isProbabilityMeasure_pathMeasure P π
  have hmp := measurePreserving_shift hπ 1
  set f : (ℕ → X) → ℝ := fun ω => Y (shift 1 ω) with hf
  have hfm : Measurable f := hYm.comp (measurable_shift 1)
  have hfi : Integrable f (pathMeasure P π) := hmp.integrable_comp_of_integrable hYi
  have hLm : Measurable (birkhoffLimit (shift 1) f) :=
    measurable_birkhoffLimit (measurable_shift 1) hfm
  have hconv := ae_tendsto_birkhoffLimit hmp hfm hfi
  have hLinv : IsPathInvariant P π (birkhoffLimit (shift 1) f) := by
    intro k
    filter_upwards [hconv] with ω hω
    exact ((tendsto_birkhoffAverage_shift hω k).limUnder_eq).trans hω.limUnder_eq.symm
  have h11 := lemma_17_1_1 P hπ hLm (integrable_birkhoffLimit hmp hfm hfi).1 hLinv
  refine ⟨h11, fun E hEm hE => ?_⟩
  rw [← setIntegral_congr_ae hEm (h11.mono fun ω h _ => h),
    setIntegral_birkhoffLimit hmp hfm hfi hEm hE]
  -- `∫_E Y ∘ θ = ∫_E Y` for invariant `E`
  have h := setIntegral_comp_iterate hmp hYm hEm hE 1
  simpa using h

/-! ### Ergodicity of the stationary Harris chain and the LLN -/

omit [MeasurableSpace X] in
/-- A strictly `θ¹`-invariant event is shift-invariant. -/
theorem isShiftInvariant_of_preimage {E : Set (ℕ → X)} (hE : shift 1 ⁻¹' E = E) :
    IsShiftInvariant E := by
  intro m ω
  rw [← shift_one_iterate]
  exact iterate_mem_iff hE m ω

/-- For a Harris chain with an invariant probability `π`, every strictly invariant event has
`P_π`-probability `0` or `1`. -/
theorem ergodic_pathMeasure [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) (μ : Measure X)
    [IsProbabilityMeasure μ] (E : Set (ℕ → X)) (hEm : MeasurableSet E)
    (hE : shift 1 ⁻¹' E = E) : pathMeasure P μ E = 0 ∨ pathMeasure P μ E = 1 := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hinv := isShiftInvariant_of_preimage hE
  have hYm : Measurable (E.indicator (1 : (ℕ → X) → ℝ)) := measurable_one.indicator hEm
  have hYb : ∀ ω, |E.indicator (1 : (ℕ → X) → ℝ) ω| ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E <;> simp [hω]
  have hYinv : IsInvariantRV P (E.indicator 1) := isInvariantRV_of_shift P fun k ω => by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω, indicator_of_mem ((hinv k ω).2 hω)]; rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem fun h => hω ((hinv k ω).1 h)]
  obtain ⟨hharm, hlim⟩ := theorem_17_1_3_i P hYm hYb hYinv
  obtain ⟨c, hc⟩ := theorem_17_1_5 hHar (measurable_expectFn P hYm) (abs_expectFn_le P hYb)
    hharm
  have hae : E.indicator (1 : (ℕ → X) → ℝ) =ᵐ[pathMeasure P μ] fun _ => c := by
    filter_upwards [hlim μ inferInstance] with ω hω
    simp_rw [hc] at hω
    exact tendsto_nhds_unique hω tendsto_const_nhds
  exact measure_eq_zero_or_one_of_ae_eq_const hEm hae

/-- **The LLN for Harris chains** (the implication (i) ⇒ (ii) of Theorem 17.1.7): for a Harris
chain with an invariant probability `π` and `f ∈ L¹(π)`, `(1/n) Sₙ(f) → π(f)`, `P_x`-a.s. for
every initial state `x`. -/
theorem lln_of_harris [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ} (hfm : Measurable f)
    (hfi : Integrable f π) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum f n ω / n) atTop (𝓝 (∫ y, f y ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hmp := measurePreserving_shift hπ 1
  have hFm : Measurable fun ω : ℕ → X => f (ω 1) := hfm.comp (measurable_pi_apply 1)
  have hlaw : (pathMeasure P π).map (fun ω => ω 1) = π := hπ.map_coord 1
  have hFi : Integrable (fun ω : ℕ → X => f (ω 1)) (pathMeasure P π) := by
    have : Integrable f ((pathMeasure P π).map fun ω => ω 1) := by rwa [hlaw]
    exact this.comp_measurable (measurable_pi_apply 1)
  have hint : ∫ ω, f (ω 1) ∂pathMeasure P π = ∫ y, f y ∂π := by
    rw [show ∫ y, f y ∂π = ∫ y, f y ∂((pathMeasure P π).map fun ω => ω 1) by rw [hlaw],
      integral_map (measurable_pi_apply 1).aemeasurable hfm.aestronglyMeasurable]
  have hb := ae_tendsto_birkhoffAverage_of_ergodic hmp hFm hFi
    (ergodic_pathMeasure hHar π)
  rw [hint] at hb
  have hE := measurableSet_llnSet hfm (∫ y, f y ∂π)
  have h1 : pathMeasure P π (llnSet f (∫ y, f y ∂π)) = 1 := by
    rw [← mem_ae_iff_prob_eq_one hE]
    filter_upwards [hb] with ω hω
    simp only [llnSet, mem_ofPred_eq, pathSum_div_eq_birkhoffAverage]
    exact hω
  have h2 := proposition_17_1_6 hHar hE (isShiftInvariant_llnSet f _) π h1 x
  exact (mem_ae_iff_prob_eq_one hE).2 h2

/-- The LLN for Harris chains from every initial distribution. -/
theorem lln_of_harris_measure [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ} (hfm : Measurable f)
    (hfi : Integrable f π) (μ : Measure X) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / n) atTop (𝓝 (∫ y, f y ∂π)) :=
  ae_pathMeasure_of_forall P μ (measurableSet_llnSet hfm _) (lln_of_harris hHar hπ hfm hfi)

/-! ### Theorem 17.1.7 -/

/-- `P_μ(N) = (P_x(N) + P_y(N))/2` for `μ = (δ_x + δ_y)/2`. -/
theorem pathMeasure_pair_apply (P : Kernel X X) [IsMarkovKernel P] (x y : X)
    {N : Set (ℕ → X)} (hN : MeasurableSet N) :
    pathMeasure P ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac x + Measure.dirac y)) N =
      2⁻¹ * (pathKernel P x N + pathKernel P y N) := by
  have := isMarkovKernel_pathKernel P
  rw [pathMeasure_eq_comp, Measure.bind_apply hN (Kernel.aemeasurable _),
    lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac' _ (Kernel.measurable_coe _ hN),
    lintegral_dirac' _ (Kernel.measurable_coe _ hN), smul_eq_mul]

/-- **(ii) ⇒ (iii) of Theorem 17.1.7**: if the LLN holds for every `f ∈ L¹(π)` from every state,
then every invariant event has `P_μ`-probability `0` or `1` for every initial law `μ`. -/
theorem trivial_of_lln (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π]
    (hlln : ∀ f : X → ℝ, Measurable f → Integrable f π → ∀ x, ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun n => pathSum f n ω / n) atTop (𝓝 (∫ y, f y ∂π)))
    (μ : Measure X) [IsProbabilityMeasure μ] (A : Set (ℕ → X)) (hA : MeasurableSet A)
    (hinv : IsInvariantRV P (A.indicator 1)) :
    pathMeasure P μ A = 0 ∨ pathMeasure P μ A = 1 := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hYm : Measurable (A.indicator (1 : (ℕ → X) → ℝ)) := measurable_one.indicator hA
  have hYb : ∀ ω, |A.indicator (1 : (ℕ → X) → ℝ) ω| ≤ 1 := fun ω => by
    by_cases hω : ω ∈ A <;> simp [hω]
  obtain ⟨-, hlim⟩ := theorem_17_1_3_i P hYm hYb hinv
  set h := expectFn P (A.indicator 1) with hh
  have hhm : Measurable h := measurable_expectFn P hYm
  have hhi : Integrable h π := Integrable.of_bound hhm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_expectFn_le P hYb x)
  have hl := ae_pathMeasure_of_forall P μ (measurableSet_llnSet hhm _) (hlln h hhm hhi)
  have hae : A.indicator (1 : (ℕ → X) → ℝ) =ᵐ[pathMeasure P μ] fun _ => ∫ y, h y ∂π := by
    filter_upwards [hlim μ inferInstance, hl] with ω h1 h2
    have h3 : Tendsto (fun k => h (ω (k + 1))) atTop (𝓝 (A.indicator 1 ω)) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have h4 := h3.cesaro
    refine tendsto_nhds_unique h4 (h2.congr fun n => ?_)
    rw [pathSum, div_eq_inv_mul]
  exact measure_eq_zero_or_one_of_ae_eq_const hA hae

omit [MeasurableSpace X] in
/-- Off `{Φ ∈ B i.o.}`, the averages of `1_B(Φₖ₊₁)` tend to `0`. -/
theorem tendsto_birkhoffAverage_indicator_of_notMem_ioSet {B : Set X} {ω : ℕ → X}
    (hω : ω ∉ ioSet B) :
    Tendsto (fun n => birkhoffAverage ℝ (shift 1) (fun ω => B.indicator (1 : X → ℝ) (ω 1)) n ω)
      atTop (𝓝 0) := by
  simp only [ioSet, mem_ofPred_eq, not_forall, not_exists, not_and] at hω
  obtain ⟨N, hN⟩ := hω
  have hbd : ∀ n, 0 ≤ birkhoffSum (shift 1) (fun ω => B.indicator (1 : X → ℝ) (ω 1)) n ω ∧
      birkhoffSum (shift 1) (fun ω => B.indicator (1 : X → ℝ) (ω 1)) n ω ≤ N := by
    intro n
    rw [← pathSum_eq_birkhoffSum]
    unfold pathSum
    constructor
    · exact Finset.sum_nonneg fun k _ => indicator_nonneg (fun _ _ => zero_le_one) _
    · calc ∑ k ∈ Finset.range n, B.indicator (1 : X → ℝ) (ω (k + 1))
          ≤ ∑ k ∈ Finset.range N, B.indicator (1 : X → ℝ) (ω (k + 1)) := by
            rcases le_total n N with hnN | hnN
            · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hnN)
                fun k _ _ => indicator_nonneg (fun _ _ => zero_le_one) _
            · rw [← Finset.sum_range_add_sum_Ico _ hnN]
              have : ∑ k ∈ Finset.Ico N n, B.indicator (1 : X → ℝ) (ω (k + 1)) = 0 :=
                Finset.sum_eq_zero fun k hk => indicator_of_notMem
                  (hN (k + 1) (by have := (Finset.mem_Ico.1 hk).1; omega)) _
              rw [this, add_zero]
        _ ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun k _ =>
            indicator_le_self' (fun _ _ => zero_le_one) _
        _ = N := by simp
  have hup : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
  · rw [birkhoffAverage_eq_div]
    exact div_nonneg (hbd n).1 (Nat.cast_nonneg n)
  · rw [birkhoffAverage_eq_div]
    exact div_le_div_of_nonneg_right (hbd n).2 (Nat.cast_nonneg n)

/-- With an invariant probability `π`, `π(B) > 0` forces `P_π(Φ ∈ B i.o.) > 0`
(Theorem 17.1.2 for `1_B`). -/
theorem pathMeasure_ioSet_pos (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {B : Set X} (hB : MeasurableSet B)
    (hpos : 0 < π B) : 0 < pathMeasure P π (ioSet B) := by
  have := isProbabilityMeasure_pathMeasure P π
  have hmp := measurePreserving_shift hπ 1
  set F : (ℕ → X) → ℝ := fun ω => B.indicator 1 (ω 1) with hF
  have hFm : Measurable F := (measurable_one.indicator hB).comp (measurable_pi_apply 1)
  have hFb : ∀ ω, |F ω| ≤ 1 := fun ω => by
    by_cases h : ω 1 ∈ B <;> simp [hF, h]
  have hint := setIntegral_birkhoffLimit_of_bdd hmp hFm hFb MeasurableSet.univ preimage_univ
  simp only [Measure.restrict_univ] at hint
  have hFint : ∫ ω, F ω ∂pathMeasure P π = π.real B := by
    have hlaw : (pathMeasure P π).map (fun ω => ω 1) = π := hπ.map_coord 1
    rw [hF, show ∫ ω, B.indicator (1 : X → ℝ) (ω 1) ∂pathMeasure P π =
        ∫ y, B.indicator (1 : X → ℝ) y ∂((pathMeasure P π).map fun ω => ω 1) from
        (integral_map (measurable_pi_apply 1).aemeasurable
          (measurable_one.indicator hB).aestronglyMeasurable).symm, hlaw,
      integral_indicator_one hB]
  by_contra hzero
  push Not at hzero
  have h0 : pathMeasure P π (ioSet B) = 0 := le_antisymm hzero bot_le
  have hL0 : birkhoffLimit (shift 1) F =ᵐ[pathMeasure P π] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0,
      ae_tendsto_birkhoffLimit hmp hFm (integrable_of_bdd P π hFm hFb)] with ω h1 h2
    exact tendsto_nhds_unique h2 (tendsto_birkhoffAverage_indicator_of_notMem_ioSet h1)
  rw [integral_congr_ae hL0, hFint] at hint
  simp only [Pi.zero_apply, integral_zero] at hint
  have : 0 < π.real B := by
    rw [Measure.real]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

/-- **(iii) ⇒ (i) of Theorem 17.1.7**: with an invariant probability `π`, if every invariant event
has `P_μ`-probability `0` or `1` for every initial law, the chain is positive Harris (with `π` as
an irreducibility measure). -/
theorem positiveHarris_of_trivial (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (htriv : ∀ μ : Measure X, IsProbabilityMeasure μ → ∀ A : Set (ℕ → X), MeasurableSet A →
      IsInvariantRV P (A.indicator 1) → pathMeasure P μ A = 0 ∨ pathMeasure P μ A = 1) :
    ∃ ψ, IsPositiveHarris P ψ := by
  have := isMarkovKernel_pathKernel P
  -- `π(B) > 0` forces `Q(·, B) ≡ 1`
  have hQ : ∀ B : Set X, MeasurableSet B → 0 < π B → ∀ x, harrisQ P B x = 1 := by
    intro B hB hpos
    have hE := measurableSet_ioSet hB
    have hinv : IsInvariantRV P ((ioSet B).indicator 1) :=
      isInvariantRV_of_shift P fun k ω => by
        by_cases hω : ω ∈ ioSet B
        · rw [indicator_of_mem hω, indicator_of_mem ((isShiftInvariant_ioSet B k ω).2 hω)]; rfl
        · rw [indicator_of_notMem hω,
            indicator_of_notMem fun h => hω ((isShiftInvariant_ioSet B k ω).1 h)]
    have h01 : ∀ x, pathKernel P x (ioSet B) = 0 ∨ pathKernel P x (ioSet B) = 1 := fun x => by
      have := htriv (Measure.dirac x) inferInstance _ hE hinv
      rwa [pathMeasure_dirac] at this
    -- `Q(·, B)` is constant
    have hconst : ∀ x y, pathKernel P x (ioSet B) = pathKernel P y (ioSet B) := by
      intro x y
      have hp := htriv _ (isProbabilityMeasure_pair x y) _ hE hinv
      rw [pathMeasure_pair_apply P x y hE] at hp
      rcases h01 x with hx | hx <;> rcases h01 y with hy | hy <;> rw [hx, hy] at hp ⊢
      · exfalso; rcases hp with hp | hp <;> simp at hp
      · exfalso; rcases hp with hp | hp <;> simp at hp
    -- `P_π(Φ ∈ B i.o.) > 0` makes the constant `1`
    have hposπ := pathMeasure_ioSet_pos P hπ hB hpos
    intro x
    rw [harrisQ]
    rcases h01 x with hx | hx
    · exfalso
      rw [pathMeasure_eq_comp, Measure.bind_apply hE (Kernel.aemeasurable _)] at hposπ
      simp_rw [hconst _ x, hx] at hposπ
      simp at hposπ
    · exact hx
  -- `π` is an irreducibility measure, and a maximal one `ψ` is equivalent to `π`
  have hirr : IsPhiIrreducible P π := fun A hA hpos x =>
    lt_of_lt_of_le (by rw [hQ A hA hpos x]; exact zero_lt_one) (harrisQ_le_hitProb P A x)
  have hπ0 : π ≠ 0 := IsProbabilityMeasure.ne_zero π
  obtain ⟨ψ, hψ, -, -, -, -, -⟩ := theorem_4_0_1 P hirr hπ0
  have hac : ψ ≪ π := proposition_10_1_2_ii hψ.2.1 (le_of_eq hπ) hπ0
  refine ⟨ψ, ⟨hψ, fun A hA hψA x _ => ?_⟩, hψ, π, inferInstance, hπ⟩
  have hπA : 0 < π A := pos_iff_ne_zero.2 fun h => (pos_iff_ne_zero.1 hψA) (hac h)
  exact hQ A hA hπA x

/-- **Theorem 17.1.7** (MT p. 427), with (iii) corrected: for a chain with an invariant
probability `π`, the following are equivalent:
(i) the chain is positive Harris;
(ii) for every `f ∈ L¹(π)`, `(1/n) Sₙ(f) → π(f)`, `P_x`-a.s., for every `x`;
(iii) for every initial distribution `μ`, every invariant event has `P_μ`-probability `0` or
`1`. -/
theorem theorem_17_1_7 [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    List.TFAE [∃ ψ, IsPositiveHarris P ψ,
      ∀ f : X → ℝ, Measurable f → Integrable f π → ∀ x, ∀ᵐ ω ∂pathKernel P x,
        Tendsto (fun n => pathSum f n ω / n) atTop (𝓝 (∫ y, f y ∂π)),
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∀ A : Set (ℕ → X), MeasurableSet A →
        IsInvariantRV P (A.indicator 1) → pathMeasure P μ A = 0 ∨ pathMeasure P μ A = 1] := by
  tfae_have 1 → 2 := fun ⟨ψ, hψ⟩ f hfm hfi x => lln_of_harris hψ.1 hπ hfm hfi x
  tfae_have 2 → 3 := fun hlln μ hμ A hA hinv => trivial_of_lln P hlln μ A hA hinv
  tfae_have 3 → 1 := positiveHarris_of_trivial P hπ
  tfae_finish

/-- Under the identity kernel, the path from `x` is constant almost surely. -/
theorem ae_eq_const_pathKernel_id (x : Bool) :
    ∀ᵐ ω ∂pathKernel (Kernel.id : Kernel Bool Bool) x, ω = fun _ => x := by
  have hpow : ∀ n : ℕ, ((Kernel.id : Kernel Bool Bool) ^ n) x = Measure.dirac x := by
    intro n
    induction n with
    | zero => exact pow_zero_apply _ x
    | succ n ih =>
      ext A hA
      rw [pow_succ_apply _ n x hA, Kernel.id_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hA),
        ih]
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂pathKernel (Kernel.id : Kernel Bool Bool) x, ω n = x := by
    intro n
    have h := pathKernel_coord_mem (Kernel.id : Kernel Bool Bool) x n
      (measurableSet_singleton x)
    rw [hpow, Measure.dirac_apply_of_mem (mem_singleton x)] at h
    have := isMarkovKernel_pathKernel (Kernel.id : Kernel Bool Bool)
    exact (mem_ae_iff_prob_eq_one (measurable_pi_apply n (measurableSet_singleton x))).2 h
  filter_upwards [ae_all_iff.2 hn] with ω hω
  exact funext hω

/-- **Correction to Theorem 17.1.7 (iii).** Triviality of the invariant σ-field under every `P_x`
does not make a chain positive Harris: for the identity chain on `Bool` with the invariant
probability `δ_true`, every event has `P_x`-probability `0` or `1` for every `x`, but the chain
is not positive Harris (it is irreducible for no nonzero measure). -/
theorem theorem_17_1_7_counterexample :
    IsInvariant (Kernel.id : Kernel Bool Bool) (Measure.dirac true) ∧
      (∀ x : Bool, ∀ A : Set (ℕ → Bool), MeasurableSet A →
        pathKernel Kernel.id x A = 0 ∨ pathKernel Kernel.id x A = 1) ∧
      ¬ ∃ ψ, IsPositiveHarris (Kernel.id : Kernel Bool Bool) ψ := by
  refine ⟨Measure.id_comp, fun x A hA => ?_, ?_⟩
  · have := isMarkovKernel_pathKernel (Kernel.id : Kernel Bool Bool)
    by_cases hc : (fun _ : ℕ => x) ∈ A
    · right
      refine (mem_ae_iff_prob_eq_one hA).1 ?_
      filter_upwards [ae_eq_const_pathKernel_id x] with ω hω
      rw [hω]; exact hc
    · left
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [ae_eq_const_pathKernel_id x] with ω hω
      rw [hω]; exact hc
  · rintro ⟨ψ, ⟨hψ, -⟩, -⟩
    obtain ⟨ψ', hmax, hprob, -, -, -, -⟩ := theorem_4_0_1 _ hψ.2.1 hψ.1
    obtain ⟨-, hno⟩ := proposition_4_2_2_zero_counterexample
    exact hno ⟨ψ', hprob, hmax.2.1⟩

end MeynTweedie.GeneralizedDrift
