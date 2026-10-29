/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.HarrisProperties
import GeneralizedDrift.Invariance
import GeneralizedDrift.BirkhoffErgodic
import Mathlib.Probability.Martingale.Convergence

/-!
# Invariant σ-fields and harmonic functions (MT §17.1.1–17.1.2)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/InvariantFields.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, §17.1, pp. 423–427. Random variables are measurable functions `Y` on the path
space `ℕ → X`; `θᵏ` is `shift k`.

**Definitions.**
* `expectFn P Y x = h_Y(x) = E_x[Y]` (17.6).
* `IsPathInvariant P μ Y` (p. 423): `θᵏY = Y`, `P_μ`-a.s., for every `k` (a `P_μ`-invariant random
  variable); `IsInvariantRV P Y` (p. 425): `P_μ`-invariant for every initial distribution `μ`.
  An event `A` is (`P_μ`-)invariant when `1_A` is.
* `IsHarmonic P h` (17.8): `∫ P(x, dy) h(y) = h(x)` for every `x`.
* `harmonicLimit h ω = limsup_k h(Φₖ)`, the random variable `H` of Theorem 17.1.3 (ii); it is
  strictly invariant, `H ∘ θᵏ = H` (`harmonicLimit_shift`).

**Tools.**
* `condExp_eq_expectFn` (17.7): for a `P_μ`-invariant integrable `Y`,
  `E_μ[Y | 𝓕ₖ^Φ] = h_Y(Φₖ)`; `tendsto_expectFn_coord`: hence `h_Y(Φₖ) → Y`, `P_μ`-a.s. (Lévy's
  upward theorem).
* `IsHarmonic.integral_pow`: `Pⁿh = h`; `IsHarmonic.martingale`: `(h(Φₖ), 𝓕ₖ^Φ)` is a
  `P_μ`-martingale (p. 425).
* `pathMeasure_eq_zero_of_forall`, `ae_pathMeasure_of_forall`: an event null for every `P_x` is
  null for every `P_μ`.

**Results.**
* **Lemma 17.1.1** (`lemma_17_1_1`, p. 423): for an invariant probability `π` and a
  `P_π`-invariant `Y` with `E_π|Y| < ∞`, `Y = h_Y(Φ₀)`, `P_π`-a.s.
* **Theorem 17.1.3** (p. 425): (i) `theorem_17_1_3_i`, for a bounded invariant `Y`, `h_Y` is
  harmonic and `Y = lim h_Y(Φₖ)` a.s. for every initial law; (ii) `theorem_17_1_3_ii`, for a
  bounded harmonic `h`, `H = limsup h(Φₖ)` is invariant, `h(Φₖ) → H` a.s., and `h_H = h`.
* **Proposition 17.1.4** (`proposition_17_1_4`, p. 426): all bounded harmonic functions are
  constant iff every `P_μ`-invariant event has `P_μ`-probability `0` or `1`, for every `μ`.
* **Theorem 17.1.5** (`theorem_17_1_5`, p. 426): for a Harris chain the bounded harmonic
  functions are constant.
* **Proposition 17.1.6** (`proposition_17_1_6`, p. 426): for a Harris chain, a shift-invariant
  event of probability one under one initial law has probability one under every `P_x` (and
  every `P_μ`, `proposition_17_1_6_measure`).

**Hypotheses.** Theorem 17.1.5 and Proposition 17.1.6 use Theorem 9.1.4, hence a countably
generated σ-algebra on `X`.

**Corrections.** Proposition 17.1.6 is stated by the book for the LLN, the CLT and the LIL, "the
proof for the CLT and LIL being identical". The proof applies to events: the LLN and the LIL
are shift-invariant events, and they are covered here. The CLT is a statement about laws, not an
event of path space, and the harmonic-function argument does not apply to it. The CLT is proved
directly for every initial condition where this project proves it.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Expectations along the path -/

/-- `h_Y(x) = E_x[Y]` (17.6), MT p. 423. -/
noncomputable def expectFn (P : Kernel X X) [IsMarkovKernel P] (Y : (ℕ → X) → ℝ) (x : X) : ℝ :=
  ∫ ω, Y ω ∂pathKernel P x

/-- `h_Y` is strongly measurable. -/
theorem stronglyMeasurable_expectFn (P : Kernel X X) [IsMarkovKernel P] {Y : (ℕ → X) → ℝ}
    (hY : Measurable Y) : StronglyMeasurable (expectFn P Y) := by
  have := isMarkovKernel_pathKernel P
  exact StronglyMeasurable.integral_kernel hY.stronglyMeasurable

/-- `h_Y` is measurable. -/
theorem measurable_expectFn (P : Kernel X X) [IsMarkovKernel P] {Y : (ℕ → X) → ℝ}
    (hY : Measurable Y) : Measurable (expectFn P Y) :=
  (stronglyMeasurable_expectFn P hY).measurable

/-- `|h_Y| ≤ C` when `|Y| ≤ C`. -/
theorem abs_expectFn_le (P : Kernel X X) [IsMarkovKernel P] {Y : (ℕ → X) → ℝ} {C : ℝ}
    (hY : ∀ ω, |Y ω| ≤ C) (x : X) : |expectFn P Y x| ≤ C := by
  have := isMarkovKernel_pathKernel P
  have h := norm_integral_le_of_norm_le_const (μ := pathKernel P x) (f := Y) (C := C)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hY ω)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at h

/-- A bounded measurable function on path space is integrable for every `P_μ`. -/
theorem integrable_of_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {Y : (ℕ → X) → ℝ} (hY : Measurable Y) {C : ℝ}
    (hC : ∀ ω, |Y ω| ≤ C) : Integrable Y (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  exact Integrable.of_bound hY.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

/-- An event null for every `P_x` is null for every `P_μ` (the mixture formula). -/
theorem pathMeasure_eq_zero_of_forall (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {N : Set (ℕ → X)} (hN : MeasurableSet N) (h : ∀ x, pathKernel P x N = 0) :
    pathMeasure P μ N = 0 := by
  have := isMarkovKernel_pathKernel P
  rw [pathMeasure_eq_comp, Measure.bind_apply hN (Kernel.aemeasurable _)]
  simp [h]

/-- A property of paths that defines an event and holds `P_x`-a.s. for every `x` holds
`P_μ`-a.s. for every `μ`. -/
theorem ae_pathMeasure_of_forall (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {p : (ℕ → X) → Prop} (hp : MeasurableSet {ω | p ω})
    (h : ∀ x, ∀ᵐ ω ∂pathKernel P x, p ω) : ∀ᵐ ω ∂pathMeasure P μ, p ω := by
  rw [ae_iff]
  refine pathMeasure_eq_zero_of_forall P μ hp.compl fun x => ?_
  have := h x
  rw [ae_iff] at this
  exact this

/-- `P_x ≤ 2 P_μ` for `μ = (δ_x + δ_y)/2`, in the form needed for null sets. -/
theorem pathKernel_eq_zero_of_pair (P : Kernel X X) [IsMarkovKernel P] (x y : X)
    {N : Set (ℕ → X)} (hN : MeasurableSet N)
    (h : pathMeasure P ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac x + Measure.dirac y)) N = 0) :
    pathKernel P x N = 0 ∧ pathKernel P y N = 0 := by
  have := isMarkovKernel_pathKernel P
  rw [pathMeasure_eq_comp, Measure.bind_apply hN (Kernel.aemeasurable _),
    lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac' _ (Kernel.measurable_coe _ hN),
    lintegral_dirac' _ (Kernel.measurable_coe _ hN)] at h
  have h2 : pathKernel P x N + pathKernel P y N = 0 := by
    rcases mul_eq_zero.1 h with h | h
    · simp at h
    · exact h
  exact add_eq_zero.1 h2

/-- `(δ_x + δ_y)/2` is a probability measure. -/
theorem isProbabilityMeasure_pair (x y : X) :
    IsProbabilityMeasure ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac x + Measure.dirac y)) := by
  constructor
  rw [Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul]
  rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ### Invariant random variables and harmonic functions -/

/-- `Y` is `P_μ`-invariant (MT p. 423): `θᵏY = Y`, `P_μ`-a.s., for every `k`. -/
def IsPathInvariant (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    (Y : (ℕ → X) → ℝ) : Prop :=
  ∀ k : ℕ, (fun ω => Y (shift k ω)) =ᵐ[pathMeasure P μ] Y

/-- `Y` is invariant (MT p. 425): `P_μ`-invariant for every initial distribution `μ`. -/
def IsInvariantRV (P : Kernel X X) [IsMarkovKernel P] (Y : (ℕ → X) → ℝ) : Prop :=
  ∀ μ : Measure X, IsProbabilityMeasure μ → IsPathInvariant P μ Y

/-- A strictly invariant random variable (`Y ∘ θᵏ = Y` everywhere) is invariant. -/
theorem isInvariantRV_of_shift (P : Kernel X X) [IsMarkovKernel P] {Y : (ℕ → X) → ℝ}
    (hY : ∀ k ω, Y (shift k ω) = Y ω) : IsInvariantRV P Y :=
  fun _ _ k => Eventually.of_forall fun ω => hY k ω

/-- A harmonic function (17.8), MT p. 425: `∫ P(x, dy) h(y) = h(x)` for every `x`. -/
def IsHarmonic (P : Kernel X X) (h : X → ℝ) : Prop := ∀ x, ∫ y, h y ∂P x = h x

/-- `E_x[h(Φₙ)] = ∫ Pⁿ(x, dy) h(y)`. -/
theorem integral_coord_eq (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ} (hh : Measurable h)
    (x : X) (n : ℕ) : ∫ ω, h (ω n) ∂pathKernel P x = ∫ y, h y ∂(P ^ n) x := by
  rw [← pathKernel_map_coord P x n, integral_map (measurable_pi_apply n).aemeasurable
    hh.aestronglyMeasurable]

/-- A bounded harmonic function satisfies `Pⁿh = h`. -/
theorem IsHarmonic.integral_pow {P : Kernel X X} [IsMarkovKernel P] {h : X → ℝ}
    (hH : IsHarmonic P h) (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (n : ℕ) (x : X) :
    ∫ y, h y ∂(P ^ n) x = h x := by
  induction n generalizing x with
  | zero => rw [pow_zero_apply, integral_dirac' _ _ hm.stronglyMeasurable]
  | succ n ih =>
    have := isMarkovKernel_pow P n
    have hint : Integrable h (((P ^ n) ∘ₖ P) x) :=
      Integrable.of_bound hm.aestronglyMeasurable C
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)
    rw [pow_succ]
    change ∫ y, h y ∂((P ^ n) ∘ₖ P) x = h x
    rw [Kernel.integral_comp hint]
    simp_rw [ih]
    exact hH x

/-- For a bounded harmonic `h`, `E_x[h(Φₙ)] = h(x)`. -/
theorem IsHarmonic.integral_coord {P : Kernel X X} [IsMarkovKernel P] {h : X → ℝ}
    (hH : IsHarmonic P h) (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (n : ℕ) (x : X) :
    ∫ ω, h (ω n) ∂pathKernel P x = h x := by
  rw [integral_coord_eq P hm x n, hH.integral_pow hm hC n x]

/-- For a bounded harmonic `h`, `E_μ[h(Φₖ₊₁) | 𝓕ₖ^Φ] = h(Φₖ)` (p. 425). -/
theorem IsHarmonic.condExp_succ {P : Kernel X X} [IsMarkovKernel P] {h : X → ℝ}
    (hH : IsHarmonic P h) (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (μ : Measure X)
    [IsProbabilityMeasure μ] (k : ℕ) :
    (pathMeasure P μ)[fun ω => h (ω (k + 1)) | natFilt k] =ᵐ[pathMeasure P μ]
      fun ω => h (ω k) := by
  have h1 := markov_property_bdd P μ k (H := fun ω => h (ω 1))
    (hm.comp (measurable_pi_apply 1)) (B := C) fun ω => hC _
  refine h1.trans (Eventually.of_forall fun ω => ?_)
  have h2 := hH.integral_coord hm hC 1 (ω k)
  exact h2

/-- For a bounded harmonic `h`, `(h(Φₖ), 𝓕ₖ^Φ)` is a `P_μ`-martingale (MT p. 425). -/
theorem IsHarmonic.martingale {P : Kernel X X} [IsMarkovKernel P] {h : X → ℝ}
    (hH : IsHarmonic P h) (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    Martingale (fun k ω => h (ω k)) natFilt (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  refine martingale_nat (fun k => ?_) (fun k => ?_) (fun k => (hH.condExp_succ hm hC μ k).symm)
  · exact (hm.comp (measurable_coord_natFilt k)).stronglyMeasurable
  · exact integrable_of_bdd P μ (hm.comp (measurable_pi_apply k)) (C := C) fun ω => hC _

/-! ### Conditional expectations of invariant random variables -/

/-- (17.7): for a `P_μ`-invariant integrable `Y`, `E_μ[Y | 𝓕ₖ^Φ] = h_Y(Φₖ)`, `P_μ`-a.s. -/
theorem condExp_eq_expectFn (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {Y : (ℕ → X) → ℝ} (hYm : Measurable Y)
    (hYi : Integrable Y (pathMeasure P μ)) (hinv : IsPathInvariant P μ Y) (k : ℕ) :
    (pathMeasure P μ)[Y | natFilt k] =ᵐ[pathMeasure P μ] fun ω => expectFn P Y (ω k) := by
  have hint : Integrable (fun ω => Y (shift k ω)) (pathMeasure P μ) := hYi.congr (hinv k).symm
  exact (condExp_congr_ae (hinv k)).symm.trans (markov_property P μ k hYm hint)

/-- `Y` is measurable for `⨆ₖ 𝓕ₖ^Φ`. -/
theorem stronglyMeasurable_iSup_natFilt {Y : (ℕ → X) → ℝ} (hYm : Measurable Y) :
    StronglyMeasurable[⨆ n, natFilt (X := X) n] Y := by
  rw [iSup_natFilt]
  exact hYm.stronglyMeasurable

/-- For a `P_μ`-invariant integrable `Y`, `h_Y(Φₖ) → Y`, `P_μ`-a.s. (Lévy's upward theorem). -/
theorem tendsto_expectFn_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {Y : (ℕ → X) → ℝ} (hYm : Measurable Y)
    (hYi : Integrable Y (pathMeasure P μ)) (hinv : IsPathInvariant P μ Y) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun k => expectFn P Y (ω k)) atTop (𝓝 (Y ω)) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hlevy := hYi.tendsto_ae_condExp (ℱ := natFilt) (stronglyMeasurable_iSup_natFilt hYm)
  have hk := ae_all_iff.2 (condExp_eq_expectFn P μ hYm hYi hinv)
  filter_upwards [hlevy, hk] with ω h1 h2
  exact h1.congr fun k => h2 k

/-- **Lemma 17.1.1** (MT p. 423): if `π` is an invariant probability and `Y` is a
`P_π`-invariant random variable with `E_π|Y| < ∞`, then `Y = h_Y(Φ₀)`, `P_π`-a.s. -/
theorem lemma_17_1_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {Y : (ℕ → X) → ℝ} (hYm : Measurable Y)
    (hYi : Integrable Y (pathMeasure P π)) (hinv : IsPathInvariant P π Y) :
    Y =ᵐ[pathMeasure P π] fun ω => expectFn P Y (ω 0) := by
  have := isProbabilityMeasure_pathMeasure P π
  have hhm : Measurable (expectFn P Y) := measurable_expectFn P hYm
  -- `E|E[Y | 𝓕ₖ] − Y| → 0`
  have hL1 := hYi.tendsto_eLpNorm_condExp (ℱ := natFilt) (stronglyMeasurable_iSup_natFilt hYm)
  -- `E|E[Y | 𝓕ₖ] − Y| = E|h(Φ₀) − Y|` for every `k`, by stationarity
  have hconst : ∀ k, eLpNorm ((pathMeasure P π)[Y | natFilt k] - Y) 1 (pathMeasure P π) =
      eLpNorm (fun ω => expectFn P Y (ω 0) - Y ω) 1 (pathMeasure P π) := by
    intro k
    have hmp : MeasurePreserving (shift k) (pathMeasure P π) (pathMeasure P π) :=
      ⟨measurable_shift k, hπ.map_shift k⟩
    have h1 : (pathMeasure P π)[Y | natFilt k] - Y =ᵐ[pathMeasure P π]
        (fun ω => expectFn P Y (ω 0) - Y ω) ∘ shift k := by
      filter_upwards [condExp_eq_expectFn P π hYm hYi hinv k, hinv k] with ω h1 h2
      simp only [Pi.sub_apply, Function.comp_apply, h1, h2, shift_apply, add_zero]
    rw [eLpNorm_congr_ae h1, eLpNorm_comp_measurePreserving
      (g := fun ω => expectFn P Y (ω 0) - Y ω)
      ((hhm.comp (measurable_pi_apply 0)).sub hYm).aestronglyMeasurable hmp]
  simp_rw [hconst] at hL1
  have h0 : eLpNorm (fun ω => expectFn P Y (ω 0) - Y ω) 1 (pathMeasure P π) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hL1
  rw [eLpNorm_eq_zero_iff one_ne_zero] at h0
  filter_upwards [h0] with ω hω
  have : expectFn P Y (ω 0) - Y ω = 0 := hω
  linarith

/-! ### Theorem 17.1.3 -/

/-- **Theorem 17.1.3 (i)** (MT p. 425): if `Y` is bounded and invariant, then `h_Y` is harmonic,
and `Y = lim h_Y(Φₖ)` almost surely for every initial distribution. -/
theorem theorem_17_1_3_i (P : Kernel X X) [IsMarkovKernel P] {Y : (ℕ → X) → ℝ}
    (hYm : Measurable Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) (hinv : IsInvariantRV P Y) :
    IsHarmonic P (expectFn P Y) ∧
      ∀ μ : Measure X, IsProbabilityMeasure μ →
        ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun k => expectFn P Y (ω k)) atTop (𝓝 (Y ω)) := by
  refine ⟨fun x => ?_, fun μ hμ =>
    tendsto_expectFn_coord P μ hYm (integrable_of_bdd P μ hYm hYb) (hinv μ hμ)⟩
  have hx := hinv (Measure.dirac x) inferInstance 1
  rw [pathMeasure_dirac] at hx
  have h1 : ∫ y, expectFn P Y y ∂P x = ∫ ω, expectFn P Y (ω 1) ∂pathKernel P x := by
    rw [integral_coord_eq P (measurable_expectFn P hYm) x 1, pow_one]
  have h2 := markov_setIntegral P (Measure.dirac x) (n := 1) MeasurableSet.univ hYm
    (integrable_shift_of_bdd P (Measure.dirac x) 1 hYm hYb).integrableOn
  simp only [pathMeasure_dirac, Measure.restrict_univ] at h2
  calc ∫ y, expectFn P Y y ∂P x = ∫ ω, expectFn P Y (ω 1) ∂pathKernel P x := h1
    _ = ∫ ω, Y (shift 1 ω) ∂pathKernel P x := h2.symm
    _ = ∫ ω, Y ω ∂pathKernel P x := integral_congr_ae hx
    _ = expectFn P Y x := rfl

/-- `H = limsup_k h(Φₖ)`, the random variable of Theorem 17.1.3 (ii). -/
noncomputable def harmonicLimit (h : X → ℝ) (ω : ℕ → X) : ℝ := limsup (fun k => h (ω k)) atTop

omit [MeasurableSpace X] in
/-- `limsup` is unchanged by dropping finitely many terms. -/
theorem limsup_shift_nat (u : ℕ → ℝ) (m : ℕ) :
    limsup (fun k => u (m + k)) atTop = limsup u atTop := by
  have : (fun k => u (m + k)) = u ∘ fun k => k + m := by
    ext k; simp [add_comm]
  rw [this, Filter.limsup, Filter.limsup, ← Filter.map_map, map_add_atTop_eq_nat]

omit [MeasurableSpace X] in
/-- `H` is strictly invariant: `H ∘ θᵐ = H`. -/
theorem harmonicLimit_shift (h : X → ℝ) (m : ℕ) (ω : ℕ → X) :
    harmonicLimit h (shift m ω) = harmonicLimit h ω :=
  limsup_shift_nat (fun k => h (ω k)) m

/-- `H` is measurable. -/
theorem measurable_harmonicLimit {h : X → ℝ} (hm : Measurable h) :
    Measurable (harmonicLimit h) :=
  Measurable.limsup fun k => hm.comp (measurable_pi_apply k)

omit [MeasurableSpace X] in
/-- `|limsup uₖ| ≤ C` when `|uₖ| ≤ C`. -/
theorem abs_limsup_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, |u n| ≤ C) : |limsup u atTop| ≤ C := by
  have hb : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of ⟨C, fun n => (le_abs_self _).trans (h n)⟩
  have hb' : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of ⟨-C, fun n => by have := neg_abs_le (u n); linarith [h n]⟩
  rw [abs_le]
  constructor
  · exact le_limsup_of_frequently_le (Frequently.of_forall fun n => by
      have := neg_abs_le (u n); linarith [h n]) hb
  · exact limsup_le_of_le hb'.isCoboundedUnder_le (Eventually.of_forall fun n =>
      (le_abs_self _).trans (h n))

omit [MeasurableSpace X] in
/-- `|H| ≤ C` when `|h| ≤ C`. -/
theorem abs_harmonicLimit_le {h : X → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) (ω : ℕ → X) :
    |harmonicLimit h ω| ≤ C :=
  abs_limsup_le fun n => hC (ω n)

/-- **Theorem 17.1.3 (ii)** (MT p. 425): for a bounded harmonic `h`, the random variable
`H = limsup h(Φₖ)` is (strictly) invariant, `h(Φₖ) → H` almost surely for every initial law
(martingale convergence), and `h_H = h`. -/
theorem theorem_17_1_3_ii (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ} (hm : Measurable h)
    {C : ℝ} (hC : ∀ x, |h x| ≤ C) (hH : IsHarmonic P h) :
    (∀ k ω, harmonicLimit h (shift k ω) = harmonicLimit h ω) ∧
      IsInvariantRV P (harmonicLimit h) ∧
      (∀ μ : Measure X, IsProbabilityMeasure μ →
        ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun k => h (ω k)) atTop (𝓝 (harmonicLimit h ω))) ∧
      expectFn P (harmonicLimit h) = h := by
  have hconv : ∀ μ : Measure X, IsProbabilityMeasure μ →
      ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun k => h (ω k)) atTop (𝓝 (harmonicLimit h ω)) := by
    intro μ hμ
    have := isProbabilityMeasure_pathMeasure P μ
    have hmart := hH.martingale hm hC μ
    have hbdd : ∀ n, eLpNorm (fun ω => h (ω n)) 1 (pathMeasure P μ) ≤ C.toNNReal := by
      intro n
      have h1 := eLpNorm_le_of_ae_bound (p := 1) (μ := pathMeasure P μ)
        (hm.comp (measurable_pi_apply n)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC (ω n))
      rwa [measure_univ, ENNReal.one_rpow, one_mul] at h1
    filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hbdd] with ω hω
    rw [harmonicLimit, hω.limsup_eq]
    exact hω
  refine ⟨harmonicLimit_shift h, isInvariantRV_of_shift P (harmonicLimit_shift h), hconv, ?_⟩
  ext x
  have := isMarkovKernel_pathKernel P
  have hlim := tendsto_integral_of_dominated_convergence (μ := pathKernel P x)
    (F := fun k ω => h (ω k)) (fun _ => C)
    (fun k => (hm.comp (measurable_pi_apply k)).aestronglyMeasurable) (integrable_const C)
    (fun k => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC (ω k))
    (by have := hconv (Measure.dirac x) inferInstance; rwa [pathMeasure_dirac] at this)
  simp_rw [hH.integral_coord hm hC] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-! ### Proposition 17.1.4 -/

/-- A bounded random variable that is `P_μ`-a.s. a constant `c`, with values in `{0, 1}`, has
`c ∈ {0, 1}`: the probability of an event that is a.s. constant is `0` or `1`. -/
theorem measure_eq_zero_or_one_of_ae_eq_const {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω}
    [IsProbabilityMeasure m] {A : Set Ω} (hA : MeasurableSet A) {c : ℝ}
    (h : A.indicator (1 : Ω → ℝ) =ᵐ[m] fun _ => c) : m A = 0 ∨ m A = 1 := by
  by_cases hc : c = 0
  · left
    have : A.indicator (1 : Ω → ℝ) =ᵐ[m] 0 := by rw [hc] at h; exact h
    rw [indicator_ae_eq_zero, Function.support_one, inter_univ] at this
    exact this
  · right
    have hae : ∀ᵐ ω ∂m, ω ∈ A := by
      filter_upwards [h] with ω hω
      by_contra hω'
      rw [indicator_of_notMem hω'] at hω
      exact hc hω.symm
    exact (mem_ae_iff_prob_eq_one hA).1 hae

/-- **Proposition 17.1.4** (MT p. 426): all bounded harmonic functions are constant iff, for every
initial distribution `μ`, every `P_μ`-invariant event has `P_μ`-probability `0` or `1` (so the
σ-fields `Σ_μ`, and hence `Σ`, are `P_μ`-trivial). -/
theorem proposition_17_1_4 (P : Kernel X X) [IsMarkovKernel P] :
    (∀ h : X → ℝ, Measurable h → (∃ C, ∀ x, |h x| ≤ C) → IsHarmonic P h → ∃ c, ∀ x, h x = c) ↔
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∀ A : Set (ℕ → X), MeasurableSet A →
        IsPathInvariant P μ (A.indicator 1) → pathMeasure P μ A = 0 ∨ pathMeasure P μ A = 1 := by
  constructor
  · intro hconst μ hμ A hA hinv
    have := isProbabilityMeasure_pathMeasure P μ
    have hYm : Measurable (A.indicator (1 : (ℕ → X) → ℝ)) := measurable_one.indicator hA
    have hYb : ∀ ω, |A.indicator (1 : (ℕ → X) → ℝ) ω| ≤ 1 := fun ω => by
      by_cases hω : ω ∈ A <;> simp [hω]
    -- `h(x) = P_x(A)` and `h(Φₖ) → 1_A`, `P_μ`-a.s.
    set h := expectFn P (A.indicator 1) with hh
    have hhm : Measurable h := measurable_expectFn P hYm
    have hhb : ∀ x, |h x| ≤ 1 := abs_expectFn_le P hYb
    have hconv := tendsto_expectFn_coord P μ hYm (integrable_of_bdd P μ hYm hYb) hinv
    -- the strictly invariant `H' = limsup h(Φₖ)` equals `1_A`, `P_μ`-a.s.
    set H := harmonicLimit h with hH
    have hHA : H =ᵐ[pathMeasure P μ] A.indicator 1 := by
      filter_upwards [hconv] with ω hω
      rw [hH, harmonicLimit, hω.limsup_eq]
    have hHm : Measurable H := measurable_harmonicLimit hhm
    have hHb : ∀ ω, |H ω| ≤ 1 := abs_harmonicLimit_le hhb
    obtain ⟨hharm, hlim⟩ := theorem_17_1_3_i P hHm hHb
      (isInvariantRV_of_shift P (harmonicLimit_shift h))
    obtain ⟨c, hc⟩ := hconst _ (measurable_expectFn P hHm) ⟨1, abs_expectFn_le P hHb⟩ hharm
    have hHc : H =ᵐ[pathMeasure P μ] fun _ => c := by
      filter_upwards [hlim μ hμ] with ω hω
      simp_rw [hc] at hω
      exact tendsto_nhds_unique hω tendsto_const_nhds
    exact measure_eq_zero_or_one_of_ae_eq_const hA (hHA.symm.trans hHc)
  · intro htriv h hm ⟨C, hC⟩ hharm
    obtain ⟨hshift, -, -, hexp⟩ := theorem_17_1_3_ii P hm hC hharm
    have hHm : Measurable (harmonicLimit h) := measurable_harmonicLimit hm
    have hHi : ∀ x, Integrable (harmonicLimit h) (pathKernel P x) := fun x => by
      have := integrable_of_bdd P (Measure.dirac x) hHm (abs_harmonicLimit_le hC)
      rwa [pathMeasure_dirac] at this
    -- two states with `h x < h z` are impossible
    have hlt : ∀ x z, ¬ h x < h z := by
      intro x z hxz
      obtain ⟨t, ht1, ht2⟩ := exists_between hxz
      set μ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac x + Measure.dirac z) with hμ
      have hμp : IsProbabilityMeasure μ := isProbabilityMeasure_pair x z
      set A := {ω | harmonicLimit h ω ≤ t} with hA
      have hAm : MeasurableSet A := measurableSet_le hHm measurable_const
      have hAinv : IsPathInvariant P μ (A.indicator 1) := by
        intro k
        refine Eventually.of_forall fun ω => ?_
        have : shift k ω ∈ A ↔ ω ∈ A := by simp only [hA, mem_ofPred_eq, hshift k ω]
        change A.indicator (1 : (ℕ → X) → ℝ) (shift k ω) = A.indicator 1 ω
        by_cases hω : ω ∈ A
        · rw [indicator_of_mem hω, indicator_of_mem (this.2 hω)]; rfl
        · rw [indicator_of_notMem hω, indicator_of_notMem fun h' => hω (this.1 h')]
      rcases htriv μ hμp A hAm hAinv with h0 | h1
      · -- `H > t`, `P_x`-a.s., so `h(x) = E_x[H] ≥ t`
        have hx : pathKernel P x A = 0 := (pathKernel_eq_zero_of_pair P x z hAm h0).1
        have hae : ∀ᵐ ω ∂pathKernel P x, t ≤ harmonicLimit h ω := by
          rw [ae_iff]
          refine measure_mono_null (fun ω hω => ?_) hx
          simp only [mem_ofPred_eq, not_le] at hω
          exact hω.le
        have := isMarkovKernel_pathKernel P
        have hge : t ≤ h x := by
          rw [← congrFun hexp x]
          calc t = ∫ _ω, t ∂pathKernel P x := by simp
            _ ≤ expectFn P (harmonicLimit h) x :=
                integral_mono_ae (integrable_const t) (hHi x) hae
        linarith
      · -- `H ≤ t`, `P_z`-a.s., so `h(z) ≤ t`
        have := isProbabilityMeasure_pathMeasure P μ
        have h0c : pathMeasure P μ Aᶜ = 0 := by rw [prob_compl_eq_zero_iff hAm]; exact h1
        have hz : pathKernel P z Aᶜ = 0 := (pathKernel_eq_zero_of_pair P x z hAm.compl h0c).2
        have hae : ∀ᵐ ω ∂pathKernel P z, harmonicLimit h ω ≤ t := by
          rw [ae_iff]; exact hz
        have := isMarkovKernel_pathKernel P
        have hle : h z ≤ t := by
          rw [← congrFun hexp z]
          calc expectFn P (harmonicLimit h) z ≤ ∫ _ω, t ∂pathKernel P z :=
                integral_mono_ae (hHi z) (integrable_const t) hae
            _ = t := by simp
        linarith
    by_cases hX : Nonempty X
    · obtain ⟨x₀⟩ := hX
      exact ⟨h x₀, fun y => le_antisymm (not_lt.1 (hlt x₀ y)) (not_lt.1 (hlt y x₀))⟩
    · exact ⟨0, fun x => absurd ⟨x⟩ hX⟩

/-! ### Harris chains: Theorem 17.1.5 and Proposition 17.1.6 -/

omit [MeasurableSpace X] in
/-- A limit of a sequence that is frequently at least `a` is at least `a`. -/
theorem le_of_tendsto_of_frequently_le {u : ℕ → ℝ} {L a : ℝ} (hu : Tendsto u atTop (𝓝 L))
    (hf : ∃ᶠ k in atTop, a ≤ u k) : a ≤ L := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ k in atTop, u k < a := hu.eventually_lt_const hlt
  exact (hf.and_eventually hev).exists.elim fun k hk => absurd hk.1 (not_le.2 hk.2)

omit [MeasurableSpace X] in
/-- A limit of a sequence that is frequently at most `a` is at most `a`. -/
theorem le_of_tendsto_of_frequently_ge {u : ℕ → ℝ} {L a : ℝ} (hu : Tendsto u atTop (𝓝 L))
    (hf : ∃ᶠ k in atTop, u k ≤ a) : L ≤ a := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ k in atTop, a < u k := hu.eventually_const_lt hlt
  exact (hf.and_eventually hev).exists.elim fun k hk => absurd hk.1 (not_le.2 hk.2)

omit [MeasurableSpace X] in
/-- A path in `{Φ ∈ B i.o.}` is frequently in `B`. -/
theorem frequently_of_mem_ioSet {B : Set X} {ω : ℕ → X} (h : ω ∈ ioSet B) :
    ∃ᶠ k in atTop, ω k ∈ B := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨k, hk, hkB⟩ := h N
  exact ⟨k, hk, hkB⟩

/-- The two halves of the proof of Theorem 17.1.5: for a bounded harmonic `h` of a Harris chain,
`{h ≥ a} ∈ B⁺(X)` forces `h ≥ a` everywhere, and `{h ≤ a} ∈ B⁺(X)` forces `h ≤ a` everywhere. -/
theorem harmonic_bound_of_harris [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {h : X → ℝ} (hm : Measurable h)
    {C : ℝ} (hC : ∀ x, |h x| ≤ C) (hharm : IsHarmonic P h) (a : ℝ) :
    (0 < ψ {x | a ≤ h x} → ∀ x, a ≤ h x) ∧ (0 < ψ {x | h x ≤ a} → ∀ x, h x ≤ a) := by
  obtain ⟨-, -, hconv, hexp⟩ := theorem_17_1_3_ii P hm hC hharm
  have hHm : Measurable (harmonicLimit h) := measurable_harmonicLimit hm
  have hHi : ∀ x, Integrable (harmonicLimit h) (pathKernel P x) := fun x => by
    have := integrable_of_bdd P (Measure.dirac x) hHm (abs_harmonicLimit_le hC)
    rwa [pathMeasure_dirac] at this
  have := isMarkovKernel_pathKernel P
  have hcx : ∀ x, ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun k => h (ω k)) atTop (𝓝 (harmonicLimit h ω)) := fun x => by
    have := hconv (Measure.dirac x) inferInstance
    rwa [pathMeasure_dirac] at this
  have hio : ∀ {B : Set X}, MeasurableSet B → 0 < ψ B → ∀ x, ∀ᵐ ω ∂pathKernel P x,
      ω ∈ ioSet B := by
    intro B hB hpos x
    have hQ := theorem_9_1_4 hHar hB hpos x
    rw [harrisQ] at hQ
    exact (mem_ae_iff_prob_eq_one (measurableSet_ioSet hB)).2 hQ
  constructor
  · intro hpos x
    have hB : MeasurableSet {x | a ≤ h x} := measurableSet_le measurable_const hm
    have hae : ∀ᵐ ω ∂pathKernel P x, a ≤ harmonicLimit h ω := by
      filter_upwards [hio hB hpos x, hcx x] with ω hω hc
      exact le_of_tendsto_of_frequently_le hc (frequently_of_mem_ioSet hω)
    rw [← congrFun hexp x]
    calc a = ∫ _ω, a ∂pathKernel P x := by simp
      _ ≤ expectFn P (harmonicLimit h) x := integral_mono_ae (integrable_const a) (hHi x) hae
  · intro hpos x
    have hB : MeasurableSet {x | h x ≤ a} := measurableSet_le hm measurable_const
    have hae : ∀ᵐ ω ∂pathKernel P x, harmonicLimit h ω ≤ a := by
      filter_upwards [hio hB hpos x, hcx x] with ω hω hc
      exact le_of_tendsto_of_frequently_ge hc (frequently_of_mem_ioSet hω)
    rw [← congrFun hexp x]
    calc expectFn P (harmonicLimit h) x ≤ ∫ _ω, a ∂pathKernel P x :=
          integral_mono_ae (hHi x) (integrable_const a) hae
      _ = a := by simp

/-- **Theorem 17.1.5** (MT p. 426): for a Harris recurrent chain the constants are the only
bounded harmonic functions. -/
theorem theorem_17_1_5 [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {h : X → ℝ} (hm : Measurable h)
    {C : ℝ} (hC : ∀ x, |h x| ≤ C) (hharm : IsHarmonic P h) : ∃ c, ∀ x, h x = c := by
  have hψ : ψ ≠ 0 := hHar.1.1
  -- for every `a`, either `h ≥ a` everywhere or `h ≤ a` everywhere
  have hdich : ∀ a : ℝ, (∀ x, a ≤ h x) ∨ (∀ x, h x ≤ a) := by
    intro a
    obtain ⟨h1, h2⟩ := harmonic_bound_of_harris hHar hm hC hharm a
    by_cases hpos : 0 < ψ {x | a ≤ h x}
    · exact Or.inl (h1 hpos)
    · right
      refine h2 (pos_iff_ne_zero.2 fun h0 => hψ ?_)
      have h0' : ψ {x | a ≤ h x} = 0 := le_antisymm (not_lt.1 hpos) bot_le
      rw [← Measure.measure_univ_eq_zero]
      refine measure_mono_null (fun x _ => ?_) (measure_union_null h0' h0)
      rcases le_total a (h x) with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    refine ⟨h x₀, fun y => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨a, ha1, ha2⟩ := exists_between hlt
      rcases hdich a with h1 | h1
      · exact absurd (h1 y) (not_le.2 ha1)
      · exact absurd (h1 x₀) (not_le.2 ha2)
    · obtain ⟨a, ha1, ha2⟩ := exists_between hlt
      rcases hdich a with h1 | h1
      · exact absurd (h1 x₀) (not_le.2 ha1)
      · exact absurd (h1 y) (not_le.2 ha2)
  · exact ⟨0, fun x => absurd ⟨x⟩ hX⟩

/-- For a shift-invariant event `E`, `x ↦ P_x(E)` is a bounded harmonic function. -/
theorem isHarmonic_pathKernel_shiftInvariant (P : Kernel X X) [IsMarkovKernel P]
    {E : Set (ℕ → X)} (hE : MeasurableSet E) (hinv : IsShiftInvariant E) :
    IsHarmonic P fun x => (pathKernel P x E).toReal := by
  have := isMarkovKernel_pathKernel P
  intro x
  have h := pathKernel_shiftInvariant_eq_pow P x 1 hE hinv
  rw [pow_one] at h
  rw [integral_toReal (Kernel.measurable_coe _ hE).aemeasurable
    (Eventually.of_forall fun y => measure_lt_top _ _), ← h]

/-- **Proposition 17.1.6** (MT p. 426): for a Harris chain, if a shift-invariant event (such as
the event that the LLN or the LIL holds) has probability one under one initial distribution,
then it has probability one from every initial state. -/
theorem proposition_17_1_6 [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {E : Set (ℕ → X)}
    (hE : MeasurableSet E) (hinv : IsShiftInvariant E) (μ₀ : Measure X)
    [IsProbabilityMeasure μ₀] (h1 : pathMeasure P μ₀ E = 1) (x : X) : pathKernel P x E = 1 := by
  have := isMarkovKernel_pathKernel P
  set g : X → ℝ := fun x => (pathKernel P x E).toReal with hg
  have hgm : Measurable g := (Kernel.measurable_coe _ hE).ennreal_toReal
  have hgb : ∀ x, |g x| ≤ 1 := fun x => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  obtain ⟨c, hc⟩ := theorem_17_1_5 hHar hgm hgb (isHarmonic_pathKernel_shiftInvariant P hE hinv)
  have hint : ∫ y, g y ∂μ₀ = 1 := by
    rw [hg, integral_toReal (Kernel.measurable_coe _ hE).aemeasurable
      (Eventually.of_forall fun y => measure_lt_top _ _)]
    rw [pathMeasure_eq_comp, Measure.bind_apply hE (Kernel.aemeasurable _)] at h1
    rw [h1, ENNReal.toReal_one]
  have hc1 : c = 1 := by
    rw [← hint]
    simp_rw [hc]
    simp
  have hx := hc x
  rw [hc1, hg] at hx
  exact (ENNReal.toReal_eq_one_iff _).1 hx

/-- Proposition 17.1.6 for every initial distribution. -/
theorem proposition_17_1_6_measure [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {E : Set (ℕ → X)}
    (hE : MeasurableSet E) (hinv : IsShiftInvariant E) (μ₀ : Measure X)
    [IsProbabilityMeasure μ₀] (h1 : pathMeasure P μ₀ E = 1) (μ : Measure X)
    [IsProbabilityMeasure μ] : pathMeasure P μ E = 1 := by
  have := isMarkovKernel_pathKernel P
  rw [pathMeasure_eq_comp, Measure.bind_apply hE (Kernel.aemeasurable _)]
  simp_rw [proposition_17_1_6 hHar hE hinv μ₀ h1]
  simp

end MeynTweedie.GeneralizedDrift
