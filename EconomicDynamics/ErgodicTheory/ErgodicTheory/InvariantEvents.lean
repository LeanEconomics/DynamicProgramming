/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ErgodicTheory.MarkovProperty
import Mathlib.Probability.Martingale.Convergence

/-!
# Invariant measures and invariant events of a Markov chain

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, modules
`LimitTheorems/Invariance.lean`, `LimitTheorems/StrongMarkov.lean` and
`LimitTheorems/InvariantFields.lean`; only the results listed here), namespace renamed to
`Miao.ErgodicTheory` and Meyn–Tweedie-numbered results prefixed `mt_`.

* `IsInvariant P μ`: `μP = μ` (MT (10.1)); `isInvariant_iff`, `IsInvariant.smul`,
  `IsInvariant.add`, `IsInvariant.pow`.
* `IsInvariant.map_coord`, `IsInvariant.map_shift`, `isInvariant_iff_map_shift`: started at an
  invariant probability the chain is stationary, and conversely.
* `iSup_natFilt`: `⋁ₙ σ(Φ₀, …, Φₙ)` is the product σ-algebra.
* `expectFn P Y x = E_x[Y]`; `IsPathInvariant`; `condExp_eq_expectFn`:
  `E_μ[Y | 𝓕ₖ] = h_Y(Φₖ)` for a `P_μ`-invariant `Y`; `tendsto_expectFn_coord` (Lévy upward).
* `mt_lemma_17_1_1` (MT Lemma 17.1.1, p. 423): for an invariant probability `π` and a
  `P_π`-invariant integrable `Y`, `Y = h_Y(Φ₀)`, `P_π`-a.s.
-/

namespace Miao.ErgodicTheory

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The invariance equation (10.1), MT p. 229: `μP = μ`, i.e. `μ(A) = ∫ μ(dx) P(x, A)`. -/
def IsInvariant (P : Kernel X X) (μ : Measure X) : Prop := P ∘ₘ μ = μ

/-- (10.1) set-wise: `μ` is invariant iff `∫ μ(dx) P(x, A) = μ(A)` for measurable `A`. -/
theorem isInvariant_iff (P : Kernel X X) (μ : Measure X) :
    IsInvariant P μ ↔ ∀ A, MeasurableSet A → ∫⁻ x, P x A ∂μ = μ A := by
  constructor
  · intro h A hA
    rw [← measure_kernel_apply μ P hA, h]
  · intro h
    ext A hA
    rw [measure_kernel_apply μ P hA, h A hA]


/-- Invariance is preserved by positive scalar multiples. -/
theorem IsInvariant.smul {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ) (c : ℝ≥0∞) :
    IsInvariant P (c • μ) := by
  unfold IsInvariant at *
  rw [Measure.comp_smul, h]


/-- Invariance is preserved by sums. -/
theorem IsInvariant.add {P : Kernel X X} {μ ν : Measure X} (hμ : IsInvariant P μ)
    (hν : IsInvariant P ν) : IsInvariant P (μ + ν) := by
  unfold IsInvariant at *
  rw [Measure.comp_add, hμ, hν]

/-! ### Iterates and stationarity -/

/-- The iteration on MT p. 231: an invariant `μ` satisfies `μPⁿ = μ`. -/
theorem IsInvariant.pow {P : Kernel X X} {μ : Measure X} (h : IsInvariant P μ) (n : ℕ) :
    IsInvariant (P ^ n) μ := by
  unfold IsInvariant at *
  induction n with
  | zero => rw [pow_zero]; exact Measure.id_comp
  | succ n ih =>
    rw [pow_add_eq P n 1, pow_one, ← Measure.comp_assoc, ih, h]



/-- MT p. 231: under `P_π`, with `π` an invariant probability, every `Φₙ` has law `π`. -/
theorem IsInvariant.map_coord {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (h : IsInvariant P π) (n : ℕ) :
    (pathMeasure P π).map (fun ω => ω n) = π :=
  (pathMeasure_map_coord P π n).trans (h.pow n)

/-- **Stationarity** (MT p. 231): started at an invariant probability `π`, the shifted chain
`θⁿΦ` has the same law `P_π` as `Φ`; all finite-dimensional distributions are invariant under
translation in time. -/
theorem IsInvariant.map_shift {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (h : IsInvariant P π) (n : ℕ) :
    (pathMeasure P π).map (shift n) = pathMeasure P π := by
  have hm := markov_measure P π (n := n) (G := univ) MeasurableSet.univ
  rw [Measure.restrict_univ] at hm
  rw [hm, h.map_coord n, pathMeasure_eq_comp]

/-- MT p. 231: the chain started at a probability `π` is stationary iff `π` is invariant. -/
theorem isInvariant_iff_map_shift {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] :
    IsInvariant P π ↔ ∀ n, (pathMeasure P π).map (shift n) = pathMeasure P π := by
  refine ⟨fun h n => h.map_shift n, fun h => ?_⟩
  have h1 := congrArg (fun m : Measure (ℕ → X) => m.map (fun ω => ω 0)) (h 1)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_shift 1)] at h1
  have h2 : (fun ω : ℕ → X => ω 0) ∘ shift 1 = fun ω => ω 1 := by
    ext ω; simp [shift]
  rw [h2, pathMeasure_map_coord, pathMeasure_map_coord, pow_one, pow_zero] at h1
  unfold IsInvariant
  rw [h1]
  exact Measure.id_comp


/-- The natural filtration generates the product σ-algebra: `⋁ₙ 𝓕ₙ^Φ = B(X)^ℕ`. -/
theorem iSup_natFilt :
    ⨆ n, natFilt (X := X) n = (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) := by
  refine le_antisymm (iSup_le (natFilt (X := X)).le) ?_
  refine iSup_le fun i => ?_
  exact ((measurable_coord_natFilt i).comap_le).trans (le_iSup (fun n => natFilt (X := X) n) i)


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
theorem mt_lemma_17_1_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
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


end Miao.ErgodicTheory
