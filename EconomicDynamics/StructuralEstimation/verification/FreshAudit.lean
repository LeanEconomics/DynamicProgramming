import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Probability.Independence.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.FDeriv.Prod
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Birkhoff's pointwise ergodic theorem (used in MT §17.1)

Copied from `EconomicDynamics/ErgodicTheory` (module `BirkhoffErgodic`), namespace renamed.

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/BirkhoffErgodic.lean`), namespace renamed to `Miao.StructuralEstimation`.

Meyn and Tweedie prove Theorem 17.1.2 (p. 424) by citing "the strong law of large numbers for
stationary sequences" (Doob [99]), which is Birkhoff's pointwise ergodic theorem. Mathlib has
Birkhoff sums and the mean ergodic theorem, but not the pointwise theorem, so it is proved here
for a measure-preserving map `T` of a finite measure space and an integrable `f`. The sums are
Mathlib's `birkhoffSum T f n ω = Σ_{k<n} f(Tᵏω)`.

* `birkhoffMax T f n = max(0, S₁, …, Sₙ)` and the **maximal ergodic lemma** (`maximal_ergodic`,
  Garsia's proof): `∫_{Mₙ > 0} f ≥ 0`; `maximal_ergodic_inter`: the same on an invariant set.
* `upSet T h`: the strictly invariant event that the Birkhoff sums of `h` are unbounded above;
  `integral_upSet_nonneg`: `∫_{E ∩ upSet h} h ≥ 0` for every invariant `E`;
  `mul_measure_le_setIntegral`, `setIntegral_le_mul_measure`: hence
  `a μ(E ∩ upSet(f − a)) ≤ ∫_{E ∩ upSet(f − a)} f` and
  `∫_{E ∩ upSet(b − f)} f ≤ b μ(E ∩ upSet(b − f))`.
* `tendsto_div_of_bdd`: a deterministic criterion for `sₙ/n → c`.
* **Birkhoff's theorem** (`ae_tendsto_birkhoffLimit`): the averages `(1/n) Sₙ f` converge
  `μ`-a.e.; the limit `birkhoffLimit T f` is invariant (`birkhoffLimit_apply_of_tendsto`),
  integrable with `∫ |L| ≤ ∫ |f|` (`integrable_birkhoffLimit`), and `∫_E L = ∫_E f` for every
  invariant `E` (`setIntegral_birkhoffLimit`), so `L = E[f | invariant σ-field]`.
* **The ergodic case** (`ae_tendsto_birkhoffAverage_of_ergodic`): if every invariant event has
  measure `0` or `1`, the averages converge to `∫ f dμ` almost everywhere.

The convergence proof avoids `limsup`: for rationals `b < a` the invariant event
`upSet(f − a) ∩ upSet(b − f)` has `a m ≤ ∫ f ≤ b m` for its measure `m`, so `m = 0`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory Filter Set Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Birkhoff sums -/

/-- Birkhoff sums of a measurable function are measurable. -/
theorem measurable_birkhoffSum {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f)
    (n : ℕ) : Measurable (birkhoffSum T f n) :=
  Finset.measurable_sum _ fun i _ => hf.comp (hT.iterate i)

/-- Birkhoff sums of an integrable function under a measure-preserving map are integrable. -/
theorem integrable_birkhoffSum {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (n : ℕ) : Integrable (birkhoffSum T f n) μ := by
  unfold birkhoffSum
  exact integrable_finsetSum _ fun i _ => (hT.iterate i).integrable_comp_of_integrable hf

omit [MeasurableSpace Ω] in
/-- The Birkhoff sums of `f − a` are `Sₙ f − n a`. -/
theorem birkhoffSum_sub_const (T : Ω → Ω) (f : Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSum T (fun x => f x - a) n ω = birkhoffSum T f n ω - n * a := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

omit [MeasurableSpace Ω] in
/-- The Birkhoff sums of `b − f` are `n b − Sₙ f`. -/
theorem birkhoffSum_const_sub (T : Ω → Ω) (f : Ω → ℝ) (b : ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSum T (fun x => b - f x) n ω = n * b - birkhoffSum T f n ω := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

omit [MeasurableSpace Ω] in
/-- On a strictly invariant set `E` (`T⁻¹E = E`), the orbit stays in `E` or in `Eᶜ`. -/
theorem iterate_mem_iff {T : Ω → Ω} {E : Set Ω} (hE : T ⁻¹' E = E) (k : ℕ) (ω : Ω) :
    T^[k] ω ∈ E ↔ ω ∈ E := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    exact Set.ext_iff.1 hE ω

omit [MeasurableSpace Ω] in
/-- On a strictly invariant set, Birkhoff sums commute with the indicator. -/
theorem birkhoffSum_indicator {T : Ω → Ω} {E : Set Ω} (hE : T ⁻¹' E = E) (f : Ω → ℝ) (n : ℕ)
    (ω : Ω) : birkhoffSum T (E.indicator f) n ω = E.indicator (birkhoffSum T f n) ω := by
  by_cases hω : ω ∈ E
  · rw [Set.indicator_of_mem hω]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Set.indicator_of_mem ((iterate_mem_iff hE k ω).2 hω)]
  · rw [Set.indicator_of_notMem hω]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Set.indicator_of_notMem (fun h => hω ((iterate_mem_iff hE k ω).1 h))]

/-! ### The running maximum and the maximal ergodic lemma -/

/-- The running maximum `Mₙ = max(S₀, S₁, …, Sₙ) = max(0, S₁, …, Sₙ)` of the Birkhoff sums. -/
noncomputable def birkhoffMax (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => birkhoffSum T f k ω

omit [MeasurableSpace Ω] in
/-- `Sₖ ≤ Mₙ` for `k ≤ n`. -/
theorem birkhoffSum_le_birkhoffMax (T : Ω → Ω) (f : Ω → ℝ) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    birkhoffSum T f k ω ≤ birkhoffMax T f n ω :=
  Finset.le_sup' (fun k => birkhoffSum T f k ω) (Finset.mem_range.2 (by omega))

omit [MeasurableSpace Ω] in
/-- `Mₙ ≥ 0`. -/
theorem birkhoffMax_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ birkhoffMax T f n ω := by
  have h := birkhoffSum_le_birkhoffMax T f (Nat.zero_le n) ω
  rwa [birkhoffSum_zero_apply] at h

omit [MeasurableSpace Ω] in
/-- `Mₙ` is nondecreasing in `n`. -/
theorem birkhoffMax_mono (T : Ω → Ω) (f : Ω → ℝ) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    birkhoffMax T f m ω ≤ birkhoffMax T f n ω :=
  Finset.sup'_le _ _ fun _ hk =>
    birkhoffSum_le_birkhoffMax T f ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)).trans hmn) ω

omit [MeasurableSpace Ω] in
/-- The key inequality of Garsia's proof: where `Mₙ > 0`, `Mₙ ≤ f + Mₙ ∘ T`. -/
theorem birkhoffMax_le_add (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) {ω : Ω}
    (hpos : 0 < birkhoffMax T f n ω) : birkhoffMax T f n ω ≤ f ω + birkhoffMax T f n (T ω) := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun k => birkhoffSum T f k ω)
  rw [birkhoffMax, hkeq]
  rw [birkhoffMax, hkeq] at hpos
  rcases k with _ | j
  · simp at hpos
  · rw [birkhoffSum_succ_apply']
    have hj : j ≤ n := by have := Finset.mem_range.1 hk; omega
    linarith [birkhoffSum_le_birkhoffMax T f hj (T ω)]

omit [MeasurableSpace Ω] in
/-- `Mₙ ≤ Σ_{k<n} |f(Tᵏω)|`. -/
theorem birkhoffMax_le_sum_abs (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffMax T f n ω ≤ birkhoffSum T (fun x => |f x|) n ω := by
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  calc birkhoffSum T f k ω ≤ birkhoffSum T (fun x => |f x|) k ω :=
        Finset.sum_le_sum fun i _ => le_abs_self _
    _ ≤ birkhoffSum T (fun x => |f x|) n ω := by
        unfold birkhoffSum
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkn)
          fun i _ _ => abs_nonneg _

/-- `Mₙ` is measurable. -/
theorem measurable_birkhoffMax {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f)
    (n : ℕ) : Measurable (birkhoffMax T f n) := by
  have h := Finset.measurable_sup' (Finset.nonempty_range_add_one (n := n))
    (fun k _ => measurable_birkhoffSum hT hf k)
  have heq : birkhoffMax T f n =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => birkhoffSum T f k := by
    ext ω; simp [birkhoffMax, Finset.sup'_apply]
  rw [heq]
  exact h

/-- `Mₙ` is integrable. -/
theorem integrable_birkhoffMax {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffMax T f n) μ := by
  refine Integrable.mono' (integrable_birkhoffSum hT hf.abs n)
    (measurable_birkhoffMax hT.measurable hfm n).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (birkhoffMax_nonneg T f n ω)]
  exact birkhoffMax_le_sum_abs T f n ω

/-- **The maximal ergodic lemma** (Garsia): `∫_{Mₙ > 0} f dμ ≥ 0`. -/
theorem maximal_ergodic {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < birkhoffMax T f n ω}, f ω ∂μ := by
  set M := birkhoffMax T f n with hM
  have hMm : Measurable M := measurable_birkhoffMax hT.measurable hfm n
  have hMi : Integrable M μ := integrable_birkhoffMax hT hfm hf n
  have hMTi : Integrable (fun ω => M (T ω)) μ := hT.integrable_comp_of_integrable hMi
  have hA : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hMm
  have h1 : ∫ ω in {ω | 0 < M ω}, (M ω - M (T ω)) ∂μ ≤ ∫ ω in {ω | 0 < M ω}, f ω ∂μ := by
    refine setIntegral_mono_on (hMi.sub hMTi).integrableOn hf.integrableOn hA fun ω hω => ?_
    have := birkhoffMax_le_add T f n hω
    linarith
  have h2 : ∫ ω in {ω | 0 < M ω}, M ω ∂μ = ∫ ω, M ω ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ω hω => ?_
    simp only [mem_ofPred_eq, not_lt] at hω
    exact le_antisymm hω (birkhoffMax_nonneg T f n ω)
  have h3 : ∫ ω in {ω | 0 < M ω}, M (T ω) ∂μ ≤ ∫ ω, M (T ω) ∂μ :=
    setIntegral_le_integral hMTi (Eventually.of_forall fun ω => birkhoffMax_nonneg T f n (T ω))
  have h4 : ∫ ω, M (T ω) ∂μ = ∫ ω, M ω ∂μ := by
    rw [← integral_map hT.measurable.aemeasurable hMm.aestronglyMeasurable, hT.map_eq]
  rw [integral_sub hMi.integrableOn hMTi.integrableOn, h2] at h1
  linarith

omit [MeasurableSpace Ω] in
/-- On a strictly invariant set `E`, `Mₙ(1_E f) = 1_E Mₙ(f)`. -/
theorem birkhoffMax_indicator {T : Ω → Ω} {E : Set Ω} (hE : T ⁻¹' E = E) (f : Ω → ℝ) (n : ℕ)
    (ω : Ω) : birkhoffMax T (E.indicator f) n ω = E.indicator (birkhoffMax T f n) ω := by
  unfold birkhoffMax
  simp_rw [birkhoffSum_indicator hE]
  by_cases hω : ω ∈ E
  · simp only [Set.indicator_of_mem hω]
  · simp only [Set.indicator_of_notMem hω, Finset.sup'_const]

/-- **The maximal ergodic lemma on an invariant set**: `∫_{E ∩ {Mₙ > 0}} f dμ ≥ 0`. -/
theorem maximal_ergodic_inter {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) {E : Set Ω} (hEm : MeasurableSet E)
    (hE : T ⁻¹' E = E) (n : ℕ) :
    0 ≤ ∫ ω in E ∩ {ω | 0 < birkhoffMax T f n ω}, f ω ∂μ := by
  have h := maximal_ergodic hT (hfm.indicator hEm) (hf.indicator hEm) n
  have hset : {ω | 0 < birkhoffMax T (E.indicator f) n ω} =
      E ∩ {ω | 0 < birkhoffMax T f n ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, birkhoffMax_indicator hE]
    by_cases hω : ω ∈ E
    · simp [hω]
    · simp [hω]
  rw [hset, setIntegral_indicator hEm] at h
  have hsub : E ∩ {ω | 0 < birkhoffMax T f n ω} ∩ E = E ∩ {ω | 0 < birkhoffMax T f n ω} := by
    ext ω; simp only [mem_inter_iff]; tauto
  rwa [hsub] at h

/-! ### Unbounded Birkhoff sums -/

/-- The event that the Birkhoff sums `Sₙ h` are unbounded above. -/
def upSet (T : Ω → Ω) (h : Ω → ℝ) : Set Ω :=
  {ω | ¬ BddAbove (Set.range fun n => birkhoffSum T h n ω)}

omit [MeasurableSpace Ω] in
/-- Bounded above sequences: dropping the first term and adding a constant changes nothing. -/
theorem bddAbove_range_succ_add_iff (s t : ℕ → ℝ) (c : ℝ) (h : ∀ n, s (n + 1) = c + t n) :
    BddAbove (Set.range s) ↔ BddAbove (Set.range t) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M - c, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hM ⟨n + 1, rfl⟩
    rw [h n] at this
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨max (s 0) (c + M), ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases n with _ | n
    · exact le_max_left _ _
    · rw [h n]
      exact le_max_of_le_right (by linarith [hM ⟨n, rfl⟩])

omit [MeasurableSpace Ω] in
/-- `upSet T h` is strictly invariant. -/
theorem preimage_upSet (T : Ω → Ω) (h : Ω → ℝ) : T ⁻¹' upSet T h = upSet T h := by
  ext ω
  simp only [upSet, mem_preimage, mem_ofPred_eq]
  rw [bddAbove_range_succ_add_iff (fun n => birkhoffSum T h n ω)
    (fun n => birkhoffSum T h n (T ω)) (h ω) fun n => birkhoffSum_succ_apply' T h n ω]

omit [MeasurableSpace Ω] in
/-- Unboundedness above, tested along the natural numbers. -/
theorem not_bddAbove_range_iff (s : ℕ → ℝ) :
    ¬ BddAbove (Set.range s) ↔ ∀ M : ℕ, ∃ n, (M : ℝ) < s n := by
  rw [not_bddAbove_iff]
  constructor
  · intro h M
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := h M
    exact ⟨n, hn⟩
  · intro h x
    obtain ⟨M, hM⟩ := exists_nat_gt x
    obtain ⟨n, hn⟩ := h M
    exact ⟨s n, ⟨n, rfl⟩, hM.trans hn⟩

/-- `upSet T h` is measurable. -/
theorem measurableSet_upSet {T : Ω → Ω} (hT : Measurable T) {h : Ω → ℝ} (hh : Measurable h) :
    MeasurableSet (upSet T h) := by
  have : upSet T h = ⋂ M : ℕ, ⋃ n : ℕ, {ω | (M : ℝ) < birkhoffSum T h n ω} := by
    ext ω
    simp only [upSet, mem_ofPred_eq, mem_iInter, mem_iUnion]
    exact not_bddAbove_range_iff _
  rw [this]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_birkhoffSum hT hh n)

/-- `∫_{E ∩ upSet h} h ≥ 0` for every strictly invariant event `E`. -/
theorem integral_upSet_nonneg {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {h : Ω → ℝ} (hhm : Measurable h) (hh : Integrable h μ) {E : Set Ω} (hEm : MeasurableSet E)
    (hE : T ⁻¹' E = E) : 0 ≤ ∫ ω in E ∩ upSet T h, h ω ∂μ := by
  set E' := E ∩ upSet T h with hE'
  have hE'm : MeasurableSet E' := hEm.inter (measurableSet_upSet hT.measurable hhm)
  have hE'inv : T ⁻¹' E' = E' := by rw [hE', preimage_inter, hE, preimage_upSet]
  set s : ℕ → Set Ω := fun n => E' ∩ {ω | 0 < birkhoffMax T h n ω} with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    hE'm.inter (measurableSet_lt measurable_const (measurable_birkhoffMax hT.measurable hhm n))
  have hmono : Monotone s := fun m n hmn ω hω =>
    ⟨hω.1, lt_of_lt_of_le hω.2 (birkhoffMax_mono T h hmn ω)⟩
  have hU : ⋃ n, s n = E' := by
    refine Subset.antisymm (iUnion_subset fun n => inter_subset_left) fun ω hω => ?_
    have hub : ¬ BddAbove (Set.range fun n => birkhoffSum T h n ω) := hω.2
    obtain ⟨k, hk⟩ := (not_bddAbove_range_iff _).1 hub 0
    refine mem_iUnion.2 ⟨k, hω, ?_⟩
    exact lt_of_lt_of_le (by exact_mod_cast hk) (birkhoffSum_le_birkhoffMax T h le_rfl ω)
  have ht := tendsto_setIntegral_of_monotone hsm hmono (hh.integrableOn)
  rw [hU] at ht
  exact ge_of_tendsto' ht fun n => maximal_ergodic_inter hT hhm hh hE'm hE'inv n

/-- `a μ(E ∩ upSet(f − a)) ≤ ∫_{E ∩ upSet(f − a)} f` for a strictly invariant `E`. -/
theorem mul_measure_le_setIntegral {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    {E : Set Ω} (hEm : MeasurableSet E) (hE : T ⁻¹' E = E) (a : ℝ) :
    a * μ.real (E ∩ upSet T (fun x => f x - a)) ≤
      ∫ ω in E ∩ upSet T (fun x => f x - a), f ω ∂μ := by
  have h := integral_upSet_nonneg (h := fun x => f x - a) hT (hfm.sub measurable_const)
    (hf.sub (integrable_const a)) hEm hE
  rw [integral_sub hf.integrableOn (integrable_const a).integrableOn, setIntegral_const,
    smul_eq_mul] at h
  linarith

/-- `∫_{E ∩ upSet(b − f)} f ≤ b μ(E ∩ upSet(b − f))` for a strictly invariant `E`. -/
theorem setIntegral_le_mul_measure {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    {E : Set Ω} (hEm : MeasurableSet E) (hE : T ⁻¹' E = E) (b : ℝ) :
    ∫ ω in E ∩ upSet T (fun x => b - f x), f ω ∂μ ≤
      b * μ.real (E ∩ upSet T (fun x => b - f x)) := by
  have h := integral_upSet_nonneg (h := fun x => b - f x) hT (measurable_const.sub hfm)
    ((integrable_const b).sub hf) hEm hE
  rw [integral_sub (integrable_const b).integrableOn hf.integrableOn, setIntegral_const,
    smul_eq_mul] at h
  linarith

/-! ### A deterministic convergence criterion -/

omit [MeasurableSpace Ω] in
/-- If `sₙ − n a` is bounded above for every rational `a > c` and `n b − sₙ` is bounded above
for every rational `b < c`, then `sₙ/n → c`. -/
theorem tendsto_div_of_bdd (s : ℕ → ℝ) (c : ℝ)
    (hup : ∀ a : ℚ, c < a → BddAbove (Set.range fun n : ℕ => s n - n * a))
    (hlo : ∀ b : ℚ, (b : ℝ) < c → BddAbove (Set.range fun n : ℕ => n * b - s n)) :
    Tendsto (fun n : ℕ => s n / n) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show c < c + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show c - ε / 2 < c by linarith)
  obtain ⟨M, hM⟩ := hup a ha1
  obtain ⟨M', hM'⟩ := hlo b hb2
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|M| + |M'|) / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
  have h1 : s n - n * a ≤ M := hM ⟨n, rfl⟩
  have h2 : n * b - s n ≤ M' := hM' ⟨n, rfl⟩
  have hbig : 2 * (|M| + |M'|) < ε * n := by
    have := (div_lt_iff₀ hε).1 (hN.trans hNn)
    linarith
  have hMa : M ≤ |M| := le_abs_self M
  have hMb : M' ≤ |M'| := le_abs_self M'
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hM0' : 0 ≤ |M'| := abs_nonneg M'
  have ha3 : (a : ℝ) * n < (c + ε / 2) * n := mul_lt_mul_of_pos_right ha2 hn0
  have hb3 : (c - ε / 2) * n < (b : ℝ) * n := mul_lt_mul_of_pos_right hb1 hn0
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hn0]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hn0]
    nlinarith

/-! ### The ergodic case -/

/-- `upSet(f − a)` is null when `a > ∫ f` and every invariant event has measure `0` or `1`. -/
theorem measure_upSet_sub_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    (herg : ∀ E, MeasurableSet E → T ⁻¹' E = E → μ E = 0 ∨ μ E = 1) {a : ℝ}
    (ha : ∫ ω, f ω ∂μ < a) : μ (upSet T (fun x => f x - a)) = 0 := by
  have hUm := measurableSet_upSet (h := fun x => f x - a) hT.measurable
    (hfm.sub measurable_const)
  rcases herg _ hUm (preimage_upSet T _) with h | h
  · exact h
  · exfalso
    have hle := mul_measure_le_setIntegral hT hfm hf MeasurableSet.univ preimage_univ a
    rw [univ_inter] at hle
    have hreal : μ.real (upSet T fun x => f x - a) = 1 := by simp [Measure.real, h]
    have hae : ∀ᵐ ω ∂μ, ω ∈ upSet T (fun x => f x - a) := (mem_ae_iff_prob_eq_one hUm).2 h
    rw [hreal, mul_one, Measure.restrict_eq_self_of_ae_mem hae] at hle
    linarith

/-- `upSet(b − f)` is null when `b < ∫ f` and every invariant event has measure `0` or `1`. -/
theorem measure_upSet_const_sub_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    (herg : ∀ E, MeasurableSet E → T ⁻¹' E = E → μ E = 0 ∨ μ E = 1) {b : ℝ}
    (hb : b < ∫ ω, f ω ∂μ) : μ (upSet T (fun x => b - f x)) = 0 := by
  have hUm := measurableSet_upSet (h := fun x => b - f x) hT.measurable
    (measurable_const.sub hfm)
  rcases herg _ hUm (preimage_upSet T _) with h | h
  · exact h
  · exfalso
    have hle := setIntegral_le_mul_measure hT hfm hf MeasurableSet.univ preimage_univ b
    rw [univ_inter] at hle
    have hreal : μ.real (upSet T fun x => b - f x) = 1 := by simp [Measure.real, h]
    have hae : ∀ᵐ ω ∂μ, ω ∈ upSet T (fun x => b - f x) := (mem_ae_iff_prob_eq_one hUm).2 h
    rw [hreal, mul_one, Measure.restrict_eq_self_of_ae_mem hae] at hle
    linarith

omit [MeasurableSpace Ω] in
/-- `birkhoffAverage = Sₙ / n`. -/
theorem birkhoffAverage_eq_div (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffAverage ℝ T f n ω = birkhoffSum T f n ω / n := by
  rw [birkhoffAverage, smul_eq_mul, div_eq_inv_mul]

/-- **Birkhoff's ergodic theorem, ergodic case.** If every strictly invariant event has measure
`0` or `1`, then `(1/n) Σ_{k<n} f(Tᵏω) → ∫ f dμ` for `μ`-almost every `ω`. -/
theorem ae_tendsto_birkhoffAverage_of_ergodic {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) (herg : ∀ E, MeasurableSet E → T ⁻¹' E = E → μ E = 0 ∨ μ E = 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 (∫ ω, f ω ∂μ)) := by
  set c := ∫ ω, f ω ∂μ with hc
  have hA : ∀ᵐ ω ∂μ, ∀ a : ℚ, c < a → ω ∉ upSet T (fun x => f x - a) := by
    rw [ae_all_iff]
    intro a
    by_cases ha : c < a
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (measure_upSet_sub_eq_zero hT hfm hf herg ha)] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h ha
  have hB : ∀ᵐ ω ∂μ, ∀ b : ℚ, (b : ℝ) < c → ω ∉ upSet T (fun x => (b : ℝ) - f x) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : (b : ℝ) < c
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (measure_upSet_const_sub_eq_zero hT hfm hf herg hb)] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hb
  filter_upwards [hA, hB] with ω hωA hωB
  have key := tendsto_div_of_bdd (fun n => birkhoffSum T f n ω) c
    (fun a ha => by
      have h := hωA a ha
      simp only [upSet, mem_ofPred_eq, not_not] at h
      simpa only [birkhoffSum_sub_const] using h)
    (fun b hb => by
      have h := hωB b hb
      simp only [upSet, mem_ofPred_eq, not_not] at h
      simpa only [birkhoffSum_const_sub] using h)
  exact key.congr fun n => (birkhoffAverage_eq_div T f n ω).symm

/-! ### The general case -/

/-- For `b < a`, the invariant event `upSet(f − a) ∩ upSet(b − f)` is null. -/
theorem measure_upSet_inter_eq_zero {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    {a b : ℝ} (hba : b < a) :
    μ (upSet T (fun x => f x - a) ∩ upSet T (fun x => b - f x)) = 0 := by
  have hUa := measurableSet_upSet (h := fun x => f x - a) hT.measurable
    (hfm.sub measurable_const)
  have hUb := measurableSet_upSet (h := fun x => b - f x) hT.measurable
    (measurable_const.sub hfm)
  have h1 := mul_measure_le_setIntegral hT hfm hf hUb (preimage_upSet T _) a
  have h2 := setIntegral_le_mul_measure hT hfm hf hUa (preimage_upSet T _) b
  rw [inter_comm] at h1
  have hnn : 0 ≤ μ.real (upSet T (fun x => f x - a) ∩ upSet T (fun x => b - f x)) :=
    measureReal_nonneg
  have hm : μ.real (upSet T (fun x => f x - a) ∩ upSet T (fun x => b - f x)) = 0 := by
    nlinarith
  exact (measureReal_eq_zero_iff).1 hm

/-- The sums of an integrable function are bounded above by `n a + M` for some `a ∈ ℕ`,
almost everywhere. -/
theorem measure_iInter_upSet_eq_zero {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    μ (⋂ a : ℕ, upSet T (fun x => f x - a)) = 0 := by
  set I := ⋂ a : ℕ, upSet T (fun x => f x - (a : ℝ)) with hI
  have hbound : ∀ a : ℕ, (a : ℝ) * μ.real I ≤ ∫ ω, |f ω| ∂μ := by
    intro a
    have h := mul_measure_le_setIntegral hT hfm hf MeasurableSet.univ preimage_univ (a : ℝ)
    rw [univ_inter] at h
    calc (a : ℝ) * μ.real I ≤ a * μ.real (upSet T fun x => f x - a) :=
          mul_le_mul_of_nonneg_left (measureReal_mono (iInter_subset _ a)) (Nat.cast_nonneg a)
      _ ≤ ∫ ω in upSet T (fun x => f x - a), f ω ∂μ := h
      _ ≤ ∫ ω in upSet T (fun x => f x - a), |f ω| ∂μ :=
          setIntegral_mono hf.integrableOn hf.abs.integrableOn fun ω => le_abs_self _
      _ ≤ ∫ ω, |f ω| ∂μ :=
          setIntegral_le_integral hf.abs (Eventually.of_forall fun _ => abs_nonneg _)
  by_contra hne
  have hpos : 0 < μ.real I :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm fun h => hne ((measureReal_eq_zero_iff).1 h))
  obtain ⟨a, ha⟩ := exists_nat_gt ((∫ ω, |f ω| ∂μ) / μ.real I)
  have := hbound a
  rw [div_lt_iff₀ hpos] at ha
  linarith

omit [MeasurableSpace Ω] in
/-- If `sₙ − n a ≤ M` and `n b − sₙ ≤ M'` for all `n`, then `b ≤ a`. -/
theorem le_of_bddAbove_both (s : ℕ → ℝ) {a b : ℝ}
    (ha : BddAbove (Set.range fun n : ℕ => s n - n * a))
    (hb : BddAbove (Set.range fun n : ℕ => n * b - s n)) : b ≤ a := by
  obtain ⟨M, hM⟩ := ha
  obtain ⟨M', hM'⟩ := hb
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + M') / (b - a))
  have h1 := hM ⟨n, rfl⟩
  have h2 := hM' ⟨n, rfl⟩
  simp only at h1 h2
  rw [div_lt_iff₀ (by linarith)] at hn
  nlinarith

omit [MeasurableSpace Ω] in
/-- A deterministic criterion: if `sₙ − n a` is bounded above for some `a`, `n b − sₙ` for some
`b`, and for rationals `b < a` one of `sₙ − n a`, `n b − sₙ` is bounded above, then `sₙ/n`
converges. -/
theorem exists_tendsto_div_of_bdd (s : ℕ → ℝ)
    (h1 : ∃ a : ℕ, BddAbove (Set.range fun n : ℕ => s n - n * a))
    (h2 : ∃ b : ℕ, BddAbove (Set.range fun n : ℕ => n * (-(b : ℝ)) - s n))
    (h3 : ∀ a b : ℚ, b < a → BddAbove (Set.range fun n : ℕ => s n - n * a) ∨
      BddAbove (Set.range fun n : ℕ => n * b - s n)) :
    ∃ c, Tendsto (fun n : ℕ => s n / n) atTop (𝓝 c) := by
  set A : Set ℝ := {r | ∃ a : ℚ, (a : ℝ) = r ∧ BddAbove (Set.range fun n : ℕ => s n - n * a)}
    with hA
  obtain ⟨a₀, ha₀⟩ := h1
  obtain ⟨b₀, hb₀⟩ := h2
  have hne : A.Nonempty := ⟨a₀, (a₀ : ℚ), by simp, by simpa using ha₀⟩
  have hbdd : BddBelow A := by
    refine ⟨-(b₀ : ℝ), ?_⟩
    rintro r ⟨a, rfl, ha⟩
    exact le_of_bddAbove_both s ha hb₀
  refine ⟨sInf A, tendsto_div_of_bdd s (sInf A) (fun a ha => ?_) (fun b hb => ?_)⟩
  · obtain ⟨r, ⟨a', rfl, ha'⟩, hr⟩ := exists_lt_of_csInf_lt hne ha
    obtain ⟨M, hM⟩ := ha'
    refine ⟨M, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hM ⟨n, rfl⟩
    simp only at this ⊢
    have : (n : ℝ) * a' ≤ n * a := mul_le_mul_of_nonneg_left hr.le (Nat.cast_nonneg n)
    linarith
  · obtain ⟨a', hba', ha'⟩ := exists_rat_btwn hb
    have hnot : ¬ BddAbove (Set.range fun n : ℕ => s n - n * (a' : ℝ)) := fun h =>
      absurd (csInf_le hbdd ⟨a', rfl, h⟩) (not_le.2 ha')
    exact (h3 a' b (by exact_mod_cast hba')).resolve_left hnot

/-- **Birkhoff's pointwise ergodic theorem**: for a measure-preserving map of a finite measure
space and an integrable `f`, the averages `(1/n) Σ_{k<n} f(Tᵏω)` converge for almost every `ω`. -/
theorem ae_exists_tendsto_birkhoffAverage {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 c) := by
  have hpair : ∀ᵐ ω ∂μ, ∀ a b : ℚ, b < a →
      ω ∉ upSet T (fun x => f x - a) ∩ upSet T (fun x => (b : ℝ) - f x) := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro b
    by_cases hba : b < a
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (measure_upSet_inter_eq_zero hT hfm hf (a := a) (b := b) (by exact_mod_cast hba))]
        with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hba
  have hneg : (⋂ b : ℕ, upSet T (fun x => -(b : ℝ) - f x)) =
      ⋂ b : ℕ, upSet T (fun x => (fun y => -f y) x - b) := by
    congr 1; ext1 b; congr 1; ext1 x; ring
  have hup := measure_eq_zero_iff_ae_notMem.1 (measure_iInter_upSet_eq_zero hT hfm hf)
  have hlo := measure_eq_zero_iff_ae_notMem.1 (hneg ▸
    measure_iInter_upSet_eq_zero hT hfm.neg hf.neg)
  filter_upwards [hpair, hup, hlo] with ω hωp hωu hωl
  have key := exists_tendsto_div_of_bdd (fun n => birkhoffSum T f n ω) ?_ ?_ ?_
  · obtain ⟨c, hc⟩ := key
    exact ⟨c, hc.congr fun n => (birkhoffAverage_eq_div T f n ω).symm⟩
  · simp only [mem_iInter, not_forall] at hωu
    obtain ⟨a, ha⟩ := hωu
    simp only [upSet, mem_ofPred_eq, not_not] at ha
    exact ⟨a, by simpa only [birkhoffSum_sub_const] using ha⟩
  · simp only [mem_iInter, not_forall] at hωl
    obtain ⟨b, hb⟩ := hωl
    simp only [upSet, mem_ofPred_eq, not_not] at hb
    exact ⟨b, by simpa only [birkhoffSum_const_sub] using hb⟩
  · intro a b hba
    have h := hωp a b hba
    simp only [mem_inter_iff, not_and_or, upSet, mem_ofPred_eq, not_not] at h
    rcases h with h | h
    · exact Or.inl (by simpa only [birkhoffSum_sub_const] using h)
    · exact Or.inr (by simpa only [birkhoffSum_const_sub] using h)

/-! ### The limit -/

/-- The Birkhoff limit `L(ω) = lim (1/n) Sₙ f(ω)` (junk where the limit does not exist). -/
noncomputable def birkhoffLimit (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => birkhoffAverage ℝ T f n ω

/-- Birkhoff averages of a measurable function are measurable. -/
theorem measurable_birkhoffAverage {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (birkhoffAverage ℝ T f n) := by
  have : birkhoffAverage ℝ T f n = fun ω => (n : ℝ)⁻¹ * birkhoffSum T f n ω := by
    ext ω; rw [birkhoffAverage, smul_eq_mul]
  rw [this]
  exact measurable_const.mul (measurable_birkhoffSum hT hf n)

/-- The Birkhoff limit is measurable. -/
theorem measurable_birkhoffLimit {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ}
    (hf : Measurable f) : Measurable (birkhoffLimit T f) :=
  (StronglyMeasurable.limUnder (l := atTop) fun n =>
    (measurable_birkhoffAverage hT hf n).stronglyMeasurable).measurable

/-- **Birkhoff's theorem**: the averages converge to `birkhoffLimit T f` almost everywhere. -/
theorem ae_tendsto_birkhoffLimit {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 (birkhoffLimit T f ω)) :=
  (ae_exists_tendsto_birkhoffAverage hT hfm hf).mono fun _ ⟨c, hc⟩ => tendsto_nhds_limUnder ⟨c, hc⟩

omit [MeasurableSpace Ω] in
/-- If the averages converge at `ω`, they converge to the same limit at `Tω`. -/
theorem tendsto_birkhoffAverage_apply {T : Ω → Ω} {f : Ω → ℝ} {ω : Ω} {c : ℝ}
    (h : Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 c)) :
    Tendsto (fun n => birkhoffAverage ℝ T f n (T ω)) atTop (𝓝 c) := by
  have h1 : Tendsto (fun n : ℕ => birkhoffAverage ℝ T f (n + 1) ω) atTop (𝓝 c) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have h3 : Tendsto (fun n : ℕ => f ω / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h4 := (h1.mul h2).sub h3
  rw [mul_one, sub_zero] at h4
  refine h4.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [birkhoffAverage_eq_div, birkhoffSum_succ_apply', Nat.cast_add, Nat.cast_one]
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- Conversely, if the averages converge at `Tω`, they converge to the same limit at `ω`. -/
theorem tendsto_birkhoffAverage_of_apply {T : Ω → Ω} {f : Ω → ℝ} {ω : Ω} {c : ℝ}
    (h : Tendsto (fun n => birkhoffAverage ℝ T f n (T ω)) atTop (𝓝 c)) :
    Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 c) := by
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have h3 : Tendsto (fun n : ℕ => f ω / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h4 := (h.mul h2).add h3
  rw [mul_one, add_zero] at h4
  refine h4.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [birkhoffAverage_eq_div, birkhoffSum_succ_apply', Nat.cast_add, Nat.cast_one]
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- The Birkhoff limit is invariant where the averages converge. -/
theorem birkhoffLimit_apply_of_tendsto {T : Ω → Ω} {f : Ω → ℝ} {ω : Ω} {c : ℝ}
    (h : Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 c)) :
    birkhoffLimit T f (T ω) = birkhoffLimit T f ω := by
  rw [birkhoffLimit, birkhoffLimit, (tendsto_birkhoffAverage_apply h).limUnder_eq, h.limUnder_eq]

/-! ### Integrals of the averages and of the limit -/

/-- `|f|` is measurable. -/
theorem measurable_abs_of_measurable {f : Ω → ℝ} (hf : Measurable f) :
    Measurable fun x => |f x| :=
  continuous_abs.measurable.comp hf

/-- `∫_E f ∘ Tᵏ = ∫_E f` for a strictly invariant `E`. -/
theorem setIntegral_comp_iterate {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hfm : Measurable f) {E : Set Ω} (hEm : MeasurableSet E) (hE : T ⁻¹' E = E)
    (k : ℕ) : ∫ ω in E, f (T^[k] ω) ∂μ = ∫ ω in E, f ω ∂μ := by
  rw [← integral_indicator hEm, ← integral_indicator hEm]
  have : E.indicator (fun ω => f (T^[k] ω)) = fun ω => (E.indicator f) (T^[k] ω) := by
    ext ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem ((iterate_mem_iff hE k ω).2 hω)]
    · rw [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem fun h => hω ((iterate_mem_iff hE k ω).1 h)]
  rw [this, ← integral_map (hT.iterate k).measurable.aemeasurable
    (hfm.indicator hEm).aestronglyMeasurable, (hT.iterate k).map_eq]

/-- `∫_E (1/n) Sₙ f = ∫_E f` for `n ≥ 1` and a strictly invariant `E`. -/
theorem setIntegral_birkhoffAverage {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) {E : Set Ω} (hEm : MeasurableSet E)
    (hE : T ⁻¹' E = E) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω in E, birkhoffAverage ℝ T f n ω ∂μ = ∫ ω in E, f ω ∂μ := by
  simp_rw [birkhoffAverage, smul_eq_mul, birkhoffSum]
  rw [integral_const_mul, integral_finsetSum (f := fun k a => f (T^[k] a)) _ fun k _ =>
    ((hT.iterate k).integrable_comp_of_integrable hf).integrableOn]
  simp_rw [setIntegral_comp_iterate hT hfm hEm hE]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- `∫ |(1/n) Sₙ f| ≤ ∫ |f|`, in `[0, ∞]`. -/
theorem lintegral_abs_birkhoffAverage_le {μ : Measure Ω} {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    (n : ℕ) : ∫⁻ ω, ENNReal.ofReal |birkhoffAverage ℝ T f n ω| ∂μ ≤
      ENNReal.ofReal (∫ ω, |f ω| ∂μ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpt : ∀ ω, |birkhoffAverage ℝ T f n ω| ≤ birkhoffAverage ℝ T (fun x => |f x|) n ω := by
    intro ω
    simp only [birkhoffAverage, smul_eq_mul, birkhoffSum]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  have hint : Integrable (birkhoffAverage ℝ T (fun x => |f x|) n) μ := by
    have : birkhoffAverage ℝ T (fun x => |f x|) n =
        fun ω => (n : ℝ)⁻¹ * birkhoffSum T (fun x => |f x|) n ω := by
      ext ω; rw [birkhoffAverage, smul_eq_mul]
    rw [this]
    exact (integrable_birkhoffSum hT hf.abs n).const_mul _
  calc ∫⁻ ω, ENNReal.ofReal |birkhoffAverage ℝ T f n ω| ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (birkhoffAverage ℝ T (fun x => |f x|) n ω) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, birkhoffAverage ℝ T (fun x => |f x|) n ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
          (abs_nonneg _).trans (hpt ω))).symm
    _ = ENNReal.ofReal (∫ ω, |f ω| ∂μ) := by
        have h := setIntegral_birkhoffAverage hT (measurable_abs_of_measurable hfm) hf.abs
          MeasurableSet.univ preimage_univ hn.ne'
        simp only [Measure.restrict_univ] at h
        rw [h]

/-- The Birkhoff limit is integrable, with `∫ |L| ≤ ∫ |f|` (Fatou). -/
theorem integrable_birkhoffLimit {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    Integrable (birkhoffLimit T f) μ ∧
      ∫ ω, |birkhoffLimit T f ω| ∂μ ≤ ∫ ω, |f ω| ∂μ := by
  have hLm := measurable_birkhoffLimit hT.measurable hfm
  have hlim : ∫⁻ ω, ENNReal.ofReal |birkhoffLimit T f ω| ∂μ ≤
      ENNReal.ofReal (∫ ω, |f ω| ∂μ) := by
    have hae : (fun ω => ENNReal.ofReal |birkhoffLimit T f ω|) =ᵐ[μ]
        fun ω => liminf (fun n => ENNReal.ofReal |birkhoffAverage ℝ T f n ω|) atTop := by
      filter_upwards [ae_tendsto_birkhoffLimit hT hfm hf] with ω hω
      have h := ((ENNReal.continuous_ofReal.comp continuous_abs).tendsto _).comp hω
      exact h.liminf_eq.symm
    rw [lintegral_congr_ae hae]
    refine (lintegral_liminf_le' fun n =>
      ((measurable_abs_of_measurable
        (measurable_birkhoffAverage hT.measurable hfm n)).ennreal_ofReal).aemeasurable).trans ?_
    exact liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
      lintegral_abs_birkhoffAverage_le hT hfm hf n)
  have hfin : HasFiniteIntegral (birkhoffLimit T f) μ := by
    rw [hasFiniteIntegral_iff_norm]
    simp_rw [Real.norm_eq_abs]
    exact hlim.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hLm.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => abs_nonneg _)
    (measurable_abs_of_measurable hLm).aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal |birkhoffLimit T f ω| ∂μ).toReal
      ≤ (ENNReal.ofReal (∫ ω, |f ω| ∂μ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlim
    _ = ∫ ω, |f ω| ∂μ := ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)

/-- For bounded `f`, `∫_E L = ∫_E f` on every strictly invariant `E` (dominated convergence). -/
theorem setIntegral_birkhoffLimit_of_bdd {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) {E : Set Ω} (hEm : MeasurableSet E) (hE : T ⁻¹' E = E) :
    ∫ ω in E, birkhoffLimit T f ω ∂μ = ∫ ω in E, f ω ∂μ := by
  have hf : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have hbd : ∀ n ω, ‖birkhoffAverage ℝ T f n ω‖ ≤ C := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [birkhoffAverage_zero, Pi.zero_apply, norm_zero]
      exact (abs_nonneg _).trans (hC ω)
    rw [Real.norm_eq_abs, birkhoffAverage_eq_div, abs_div, Nat.abs_cast,
      div_le_iff₀ (by exact_mod_cast hn)]
    calc |birkhoffSum T f n ω| ≤ ∑ k ∈ Finset.range n, |f (T^[k] ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
      _ = C * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hconv := tendsto_integral_of_dominated_convergence (μ := μ.restrict E) (fun _ => C)
    (fun n => (measurable_birkhoffAverage hT.measurable hfm n).aestronglyMeasurable)
    (integrable_const C) (fun n => Eventually.of_forall (hbd n))
    (ae_restrict_of_ae (ae_tendsto_birkhoffLimit hT hfm hf))
  refine tendsto_nhds_unique hconv (tendsto_const_nhds.congr' ?_)
  exact eventually_atTop.2 ⟨1, fun n hn =>
    (setIntegral_birkhoffAverage hT hfm hf hEm hE (by omega)).symm⟩

/-- The two-sided truncation `max(−M, min(f, M))`. -/
def truncAt (M : ℝ) (f : Ω → ℝ) (ω : Ω) : ℝ := max (-M) (min (f ω) M)

omit [MeasurableSpace Ω] in
/-- `|f − truncAt M f| ≤ |f|`, and `= 0` once `M ≥ |f|`. -/
theorem abs_sub_truncAt_le (M : ℝ) (hM : 0 ≤ M) (f : Ω → ℝ) (ω : Ω) :
    |f ω - truncAt M f ω| ≤ |f ω| := by
  unfold truncAt
  rcases le_total (f ω) M with h | h <;> rcases le_total (-M) (f ω) with h' | h'
  all_goals
    first
    | (rw [min_eq_left h, max_eq_right h']; simp)
    | (rw [abs_le]; constructor <;>
        cases abs_cases (f ω) <;> simp only [min_def, max_def] <;> split_ifs <;> linarith)

/-- **The limit is the conditional expectation on the invariant σ-field**: `∫_E L = ∫_E f` for
every strictly invariant event `E`. -/
theorem setIntegral_birkhoffLimit {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    {E : Set Ω} (hEm : MeasurableSet E) (hE : T ⁻¹' E = E) :
    ∫ ω in E, birkhoffLimit T f ω ∂μ = ∫ ω in E, f ω ∂μ := by
  have htm : ∀ M : ℕ, Measurable (truncAt (M : ℝ) f) := fun M =>
    measurable_const.max (hfm.min measurable_const)
  have hbd : ∀ M : ℕ, ∀ ω, |truncAt (M : ℝ) f ω| ≤ M := by
    intro M ω
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
      (min_le_right _ _)⟩
  have hti : ∀ M : ℕ, Integrable (truncAt (M : ℝ) f) μ := fun M =>
    Integrable.of_bound (htm M).aestronglyMeasurable (M : ℝ)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd M ω)
  set g : ℕ → Ω → ℝ := fun M ω => f ω - truncAt (M : ℝ) f ω with hg
  have hgm : ∀ M, Measurable (g M) := fun M => hfm.sub (htm M)
  have hgi : ∀ M, Integrable (g M) μ := fun M => hf.sub (hti M)
  -- the limit splits
  have hsplit : ∀ M : ℕ, ∫ ω in E, birkhoffLimit T f ω ∂μ - ∫ ω in E, f ω ∂μ =
      ∫ ω in E, birkhoffLimit T (g M) ω ∂μ - ∫ ω in E, g M ω ∂μ := by
    intro M
    have hae : birkhoffLimit T f =ᵐ[μ]
        fun ω => birkhoffLimit T (truncAt (M : ℝ) f) ω + birkhoffLimit T (g M) ω := by
      filter_upwards [ae_tendsto_birkhoffLimit hT hfm hf,
        ae_tendsto_birkhoffLimit hT (htm M) (hti M),
        ae_tendsto_birkhoffLimit hT (hgm M) (hgi M)] with ω h1 h2 h3
      refine tendsto_nhds_unique h1 ((h2.add h3).congr fun n => ?_)
      rw [← birkhoffAverage_add_apply]
      congr 1
      ext x
      simp [hg]
    rw [setIntegral_congr_ae hEm (hae.mono fun ω h _ => h),
      integral_add (integrable_birkhoffLimit hT (htm M) (hti M)).1.integrableOn
        (integrable_birkhoffLimit hT (hgm M) (hgi M)).1.integrableOn,
      setIntegral_birkhoffLimit_of_bdd hT (htm M) (hbd M) hEm hE]
    have : ∫ ω in E, f ω ∂μ = ∫ ω in E, truncAt (M : ℝ) f ω ∂μ + ∫ ω in E, g M ω ∂μ := by
      rw [← integral_add (hti M).integrableOn (hgi M).integrableOn]
      congr 1; ext ω; simp [hg]
    rw [this]
    ring
  -- the error is at most `2 ∫ |g M|`
  have hle : ∀ M : ℕ, |∫ ω in E, birkhoffLimit T f ω ∂μ - ∫ ω in E, f ω ∂μ| ≤
      2 * ∫ ω, |g M ω| ∂μ := by
    intro M
    rw [hsplit M]
    have hL := integrable_birkhoffLimit hT (hgm M) (hgi M)
    calc |∫ ω in E, birkhoffLimit T (g M) ω ∂μ - ∫ ω in E, g M ω ∂μ|
        ≤ |∫ ω in E, birkhoffLimit T (g M) ω ∂μ| + |∫ ω in E, g M ω ∂μ| := abs_sub _ _
      _ ≤ ∫ ω in E, |birkhoffLimit T (g M) ω| ∂μ + ∫ ω in E, |g M ω| ∂μ :=
          add_le_add (abs_integral_le_integral_abs) (abs_integral_le_integral_abs)
      _ ≤ ∫ ω, |birkhoffLimit T (g M) ω| ∂μ + ∫ ω, |g M ω| ∂μ :=
          add_le_add (setIntegral_le_integral hL.1.abs (Eventually.of_forall fun _ =>
            abs_nonneg _)) (setIntegral_le_integral (hgi M).abs
              (Eventually.of_forall fun _ => abs_nonneg _))
      _ ≤ ∫ ω, |g M ω| ∂μ + ∫ ω, |g M ω| ∂μ := add_le_add_left hL.2 _
      _ = 2 * ∫ ω, |g M ω| ∂μ := by ring
  -- and `∫ |g M| → 0`
  have htend : Tendsto (fun M : ℕ => ∫ ω, |g M ω| ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ))
      (fun ω => |f ω|)
      (fun M => (measurable_abs_of_measurable (hgm M)).aestronglyMeasurable) hf.abs
      (fun M => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_sub_truncAt_le (M : ℝ) (Nat.cast_nonneg M) f ω)
      (Eventually.of_forall fun ω => by
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ?_)
        obtain ⟨N, hN⟩ := exists_nat_ge (|f ω|)
        refine ⟨N, fun M hM => ?_⟩
        have hMf : |f ω| ≤ M := hN.trans (by exact_mod_cast hM)
        have : truncAt (M : ℝ) f ω = f ω := by
          unfold truncAt
          rw [abs_le] at hMf
          rw [min_eq_left hMf.2, max_eq_right hMf.1]
        simp [hg, this])
    simpa using h
  have h2 := htend.const_mul 2
  rw [mul_zero] at h2
  have h0 : |∫ ω in E, birkhoffLimit T f ω ∂μ - ∫ ω in E, f ω ∂μ| ≤ 0 :=
    ge_of_tendsto h2 (Eventually.of_forall hle)
  have := abs_nonneg (∫ ω in E, birkhoffLimit T f ω ∂μ - ∫ ω in E, f ω ∂μ)
  have h3 : ∫ ω in E, birkhoffLimit T f ω ∂μ - ∫ ω in E, f ω ∂μ = 0 :=
    abs_eq_zero.1 (le_antisymm h0 this)
  linarith

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The path space of a Markov chain (MT §3.1, §3.4.1)

Copied from `EconomicDynamics/ErgodicTheory` (module `PathSpace`), namespace renamed.

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/PathSpace.lean`), namespace renamed to `Miao.StructuralEstimation` and the
Meyn–Tweedie-numbered results prefixed `mt_`.

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd ed., §3.1 and §3.4.1,
pp. 48–61. The state space is an arbitrary measurable space `X`; no countable generation or
topology is needed. A transition probability kernel is a Markov kernel `P : Kernel X X`. The
sample space is `Ω = ℕ → X` with the product σ-algebra, and `Φₙ(ω) = ω n` are the coordinates.

* `trajKernel`, `pathKernel`, `pathMeasure`: `P_x` and `P_μ` are built from `P` by the
  Ionescu-Tulcea theorem (Mathlib's `Kernel.traj`, `Kernel.trajMeasure`). `pathKernel P` is the
  kernel `x ↦ P_x`, so `x ↦ P_x(B)` is measurable for every event `B`.
* `pathMeasure_eq_comp` (p. 53): `P_μ = ∫ P_x μ(dx)`, the mixture formula; `pathMeasure_dirac`:
  `P_{δ_x} = P_x`; `pathMeasure_inter_zero` (3.1): `P_μ(B ∩ {Φ₀ ∈ C}) = ∫_C P_x(B) μ(dx)`.
* `pathMeasure_map_zero`: the law of `Φ₀` under `P_μ` is `μ`; `ae_pathKernel_zero`:
  `Φ₀ = x`, `P_x`-a.s. (p. 49).
* `natFilt`: the natural filtration `𝓕ₙ^Φ = σ(Φ₀, …, Φₙ)` (p. 63).
* `setLIntegral_succ`: the one-step Markov identity `∫_G f(Φₙ₊₁) dP_μ = ∫_G Pf(Φₙ) dP_μ` for
  `G ∈ 𝓕ₙ^Φ`.
* `cylFn`, `measure_inter_shift_box`: the finite-dimensional distributions, even jointly with an
  event of `𝓕ₙ^Φ`.
* `IsMarkovChain`: a process with the finite-dimensional distributions (3.20), the definition of
  a time-homogeneous Markov chain with kernel `P` and initial law `μ` (p. 61).
* **Theorem 3.4.1** (`mt_theorem_3_4_1`, p. 60): the coordinate process under `P_μ` is such a chain.
  `mt_theorem_3_4_1_unique`: `P_μ` is the only probability on path space with these
  finite-dimensional distributions, and `law_eq_pathMeasure`: every Markov chain with kernel `P`
  and initial law `μ` has law `P_μ`.

**Corrections.** None. The book assumes a countably generated σ-algebra on `X`; the construction
needs no assumption on `X` at all (Ionescu-Tulcea).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The path measures -/

/-- The kernels `(x₀, …, xₙ) ↦ P(xₙ, ·)` that drive the path of the chain. -/
noncomputable def trajKernel (P : Kernel X X) (n : ℕ) : Kernel (Π _ : Finset.Iic n, X) X :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

/-- The driving kernels are Markov. -/
theorem isMarkovKernel_trajKernel (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (trajKernel P n) := by
  unfold trajKernel
  infer_instance

/-- The kernel `x ↦ P_x`: the law of the path started at `x` (MT p. 49). -/
noncomputable def pathKernel (P : Kernel X X) [IsMarkovKernel P] : Kernel X (ℕ → X) :=
  (@Kernel.traj (fun _ => X) _ (trajKernel P) (isMarkovKernel_trajKernel P) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm
    (MeasurableEquiv.measurable _)

/-- `P_x` is a probability measure. -/
theorem isMarkovKernel_pathKernel (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovKernel (pathKernel P) := by
  have := isMarkovKernel_trajKernel P
  unfold pathKernel
  infer_instance

/-- The law `P_μ` of the chain with transition kernel `P` and initial distribution `μ`
(MT p. 53, Theorem 3.4.1). -/
noncomputable def pathMeasure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    Measure (ℕ → X) :=
  @Kernel.trajMeasure (fun _ => X) _ μ (trajKernel P) (isMarkovKernel_trajKernel P)

/-- `P_μ` is a probability measure. -/
theorem isProbabilityMeasure_pathMeasure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (pathMeasure P μ) := by
  have := isMarkovKernel_trajKernel P
  unfold pathMeasure
  infer_instance

/-- **The mixture formula** (MT p. 53): `P_μ = ∫ P_x μ(dx)`. -/
theorem pathMeasure_eq_comp (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    pathMeasure P μ = pathKernel P ∘ₘ μ := by
  have := isMarkovKernel_trajKernel P
  have := isMarkovKernel_pathKernel P
  ext s hs
  rw [pathMeasure, Kernel.trajMeasure, Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (MeasurableEquiv.measurable _)]
  rfl

/-- `P_{δ_x} = P_x`. -/
theorem pathMeasure_dirac (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    pathMeasure P (Measure.dirac x) = pathKernel P x := by
  rw [pathMeasure_eq_comp, Measure.dirac_bind (Kernel.measurable _)]

/-- Under `P_x` the path starts at `x`: the law of `Φ₀` is `δ_x` (MT p. 49). -/
theorem pathKernel_map_zero (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    (pathKernel P x).map (fun ω => ω 0) = Measure.dirac x := by
  have := isMarkovKernel_trajKernel P
  have hg : Measurable fun y : Π _ : Finset.Iic 0, X => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  have hfr := Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) 0
  have h1 := Kernel.traj_map_frestrictLe (X := fun _ => X) (κ := trajKernel P) 0 0
  rw [Kernel.partialTraj_self] at h1
  have h3 := congrArg (fun η => (η (fun _ : Finset.Iic 0 => x)).map
    (fun y : Π _ : Finset.Iic 0, X => y ⟨0, Finset.mem_Iic.2 le_rfl⟩)) h1
  simp only [Kernel.map_apply _ hfr, Kernel.id_apply, Measure.map_dirac' hg,
    Measure.map_map hg hfr] at h3
  exact h3

/-- `P_x(Φ₀ ∈ A) = 1_A(x)`. -/
theorem pathKernel_zero_mem (P : Kernel X X) [IsMarkovKernel P] (x : X) {A : Set X}
    (hA : MeasurableSet A) : pathKernel P x {ω | ω 0 ∈ A} = A.indicator 1 x := by
  have h := congrArg (fun m : Measure X => m A) (pathKernel_map_zero P x)
  simp only [Measure.map_apply (measurable_pi_apply 0 : Measurable fun ω : ℕ → X => ω 0) hA,
    Measure.dirac_apply' _ hA] at h
  exact h

/-- `Φ₀ = x`, `P_x`-almost surely (when points are measurable, so that `{Φ₀ = x}` is an
event). -/
theorem ae_pathKernel_zero [MeasurableSingletonClass X] (P : Kernel X X) [IsMarkovKernel P]
    (x : X) :
    ∀ᵐ ω ∂pathKernel P x, ω 0 = x := by
  have h := pathKernel_map_zero P x
  have hae : ∀ᵐ y ∂(pathKernel P x).map (fun ω => ω 0), y = x := by
    rw [h, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable hae

/-- (3.1), MT p. 51: `P_μ(B ∩ {Φ₀ ∈ C}) = ∫_C P_x(B) μ(dx)`. In particular, for a countable
space, `P_μ(B ∩ {Φ₀ = x₀}) = μ(x₀) P_{x₀}(B)`. -/
theorem pathMeasure_inter_zero (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {B : Set (ℕ → X)} (hB : MeasurableSet B) {C : Set X} (hC : MeasurableSet C) :
    pathMeasure P μ (B ∩ {ω | ω 0 ∈ C}) = ∫⁻ x in C, pathKernel P x B ∂μ := by
  have := isMarkovKernel_pathKernel P
  have hm : MeasurableSet {ω : ℕ → X | ω 0 ∈ C} := measurable_pi_apply 0 hC
  rw [pathMeasure_eq_comp, Measure.bind_apply (hB.inter hm) (Kernel.aemeasurable _),
    ← lintegral_indicator hC]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ C
  · rw [indicator_of_mem hx]
    refine measure_inter_conull ?_
    have : {ω : ℕ → X | ω 0 ∈ C}ᶜ = {ω | ω 0 ∈ Cᶜ} := rfl
    rw [this, pathKernel_zero_mem P x hC.compl, indicator_of_notMem (by simpa using hx)]
  · rw [indicator_of_notMem hx]
    refine measure_mono_null inter_subset_right ?_
    rw [pathKernel_zero_mem P x hC, indicator_of_notMem hx]

/-- The law of `Φ₀` under `P_μ` is the initial distribution `μ`. -/
theorem pathMeasure_map_zero (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) :
    (pathMeasure P μ).map (fun ω => ω 0) = μ := by
  ext C hC
  have := isMarkovKernel_pathKernel P
  have h := pathMeasure_inter_zero P μ MeasurableSet.univ hC
  rw [univ_inter] at h
  rw [Measure.map_apply (measurable_pi_apply 0 : Measurable fun ω : ℕ → X => ω 0) hC]
  exact h.trans (by simp)

/-! ### The natural filtration and the one-step identity -/

/-- The natural filtration `𝓕ₙ^Φ = σ(Φ₀, …, Φₙ)` of the coordinate process (MT p. 63). -/
abbrev natFilt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) :=
  Filtration.piLE (X := fun _ : ℕ => X)

/-- `Φₖ` is `𝓕ₖ^Φ`-measurable. -/
theorem measurable_coord_natFilt (k : ℕ) :
    Measurable[natFilt (X := X) k] fun ω : ℕ → X => ω k :=
  fun s hs => ⟨(fun x : Π _ : Set.Iic k, X => x ⟨k, Set.mem_Iic.2 le_rfl⟩) ⁻¹' s,
    measurable_pi_apply _ hs, rfl⟩

/-- `{Φₖ ∈ A} ∈ 𝓕ₙ^Φ` for `k ≤ n`. -/
theorem measurableSet_coord_natFilt {k n : ℕ} (hkn : k ≤ n) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet[natFilt (X := X) n] {ω : ℕ → X | ω k ∈ A} :=
  (natFilt (X := X)).mono hkn _ (measurable_coord_natFilt k hA)

/-- **The one-step Markov identity.** For `G ∈ 𝓕ₙ^Φ` and measurable `f ≥ 0`,
`∫_G f(Φₙ₊₁) dP_μ = ∫_G Pf(Φₙ) dP_μ`. -/
theorem setLIntegral_succ (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in G, f (ω (n + 1)) ∂pathMeasure P μ =
      ∫⁻ ω in G, ∫⁻ y, f y ∂P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_trajKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hG' := hG
  rw [natFilt, Filtration.piLE_eq_comap_frestrictLe] at hG'
  obtain ⟨T, hT, rfl⟩ := hG'
  have hc := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => X) (μ₀ := μ) (κ := trajKernel P) (a := n)
  have hfr := Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) n
  have hF : Measurable fun ω : ℕ → X => (Preorder.frestrictLe n ω, ω (n + 1)) :=
    hfr.prodMk (measurable_pi_apply _)
  have hpre : (Preorder.frestrictLe n ⁻¹' T : Set (ℕ → X)) =
      (fun ω : ℕ → X => (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹' (T ×ˢ univ) := by
    ext ω; simp
  have hf2 : Measurable fun p : (Π _ : Finset.Iic n, X) × X => f p.2 := hf.comp measurable_snd
  have hk : Measurable fun y : Π _ : Finset.Iic n, X => ∫⁻ z, f z ∂trajKernel P n y :=
    hf.lintegral_kernel
  calc ∫⁻ ω in Preorder.frestrictLe n ⁻¹' T, f (ω (n + 1)) ∂pathMeasure P μ
      = ∫⁻ p in T ×ˢ univ, f p.2 ∂((pathMeasure P μ).map
          fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) := by
        rw [setLIntegral_map (f := fun p => f p.2) (hT.prod MeasurableSet.univ) hf2 hF,
          hpre]
    _ = ∫⁻ p in T ×ˢ univ, f p.2 ∂(((pathMeasure P μ).map (Preorder.frestrictLe n)) ⊗ₘ
          trajKernel P n) := by
        rw [pathMeasure, hc]
    _ = ∫⁻ y in T, ∫⁻ z, f z ∂trajKernel P n y ∂((pathMeasure P μ).map
          (Preorder.frestrictLe n)) := by
        rw [Measure.setLIntegral_compProd (f := fun p => f p.2) hf2 hT MeasurableSet.univ]
        simp only [Measure.restrict_univ]
    _ = ∫⁻ ω in Preorder.frestrictLe n ⁻¹' T, ∫⁻ y, f y ∂P (ω n) ∂pathMeasure P μ := by
        rw [setLIntegral_map hT hk hfr]
        rfl

/-! ### Finite-dimensional distributions -/

/-- The nested integral of (3.20): `cylFn P n A y` is the probability, starting at `y`, that
`Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ`, namely `1_{A₀}(y) ∫_{A₁} P(y, dy₁) ⋯ P(y_{n−1}, Aₙ)`. -/
noncomputable def cylFn (P : Kernel X X) : ℕ → (ℕ → Set X) → X → ℝ≥0∞
  | 0, A => (A 0).indicator 1
  | n + 1, A => (A 0).indicator fun y => ∫⁻ z, cylFn P n (fun i => A (i + 1)) z ∂P y

/-- `cylFn` is measurable. -/
theorem measurable_cylFn (P : Kernel X X) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) : Measurable (cylFn P n A) := by
  induction n generalizing A with
  | zero => exact measurable_one.indicator (hA 0)
  | succ n ih =>
    exact (ih fun i => hA (i + 1)).lintegral_kernel.indicator (hA 0)

/-- The box `{Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ}`. -/
def boxSet (n : ℕ) (A : ℕ → Set X) : Set (ℕ → X) := {ω | ∀ i ≤ n, ω i ∈ A i}

/-- Boxes are measurable. -/
theorem measurableSet_boxSet (n : ℕ) {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (boxSet n A) := by
  have : boxSet n A = ⋂ i ∈ Finset.range (n + 1), {ω : ℕ → X | ω i ∈ A i} := by
    ext ω; simp [boxSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (hA i)

/-- The finite-dimensional distributions jointly with an event of the past:
for `G ∈ 𝓕ₙ^Φ`, `P_μ(G ∩ {Φₙ ∈ A₀, …, Φₙ₊ₘ ∈ Aₘ}) = ∫_G cylFn P m A (Φₙ) dP_μ`. -/
theorem measure_inter_shift_box (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) {n : ℕ}
    {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G) :
    pathMeasure P μ (G ∩ {ω | ∀ i ≤ m, ω (n + i) ∈ A i}) =
      ∫⁻ ω in G, cylFn P m A (ω n) ∂pathMeasure P μ := by
  induction m generalizing n G A with
  | zero =>
    have hset : {ω : ℕ → X | ∀ i ≤ 0, ω (n + i) ∈ A i} = (fun ω => ω n) ⁻¹' A 0 := by
      ext ω; simp
    have hm : MeasurableSet ((fun ω : ℕ → X => ω n) ⁻¹' A 0) := measurable_pi_apply n (hA 0)
    have hind : (fun ω : ℕ → X => cylFn P 0 A (ω n)) =
        ((fun ω : ℕ → X => ω n) ⁻¹' A 0).indicator 1 := by
      ext ω; by_cases h : ω n ∈ A 0 <;> simp [cylFn, h]
    rw [hset, hind, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_comm]
  | succ m ih =>
    set A' : ℕ → Set X := fun i => A (i + 1)
    have hA' : ∀ i, MeasurableSet (A' i) := fun i => hA (i + 1)
    have hm : MeasurableSet[natFilt n] {ω : ℕ → X | ω n ∈ A 0} :=
      measurableSet_coord_natFilt le_rfl (hA 0)
    have hG' : MeasurableSet[natFilt n] (G ∩ {ω : ℕ → X | ω n ∈ A 0}) := hG.inter hm
    have hset : G ∩ {ω : ℕ → X | ∀ i ≤ m + 1, ω (n + i) ∈ A i} =
        (G ∩ {ω | ω n ∈ A 0}) ∩ {ω | ∀ i ≤ m, ω (n + 1 + i) ∈ A' i} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, A']
      constructor
      · rintro ⟨hg, h⟩
        refine ⟨⟨hg, by simpa using h 0 (Nat.zero_le _)⟩, fun i hi => ?_⟩
        have := h (i + 1) (by omega)
        rwa [show n + (i + 1) = n + 1 + i by omega] at this
      · rintro ⟨⟨hg, h0⟩, h⟩
        refine ⟨hg, fun i hi => ?_⟩
        rcases i with _ | i
        · simpa using h0
        · have := h i (by omega)
          rwa [show n + 1 + i = n + (i + 1) by omega] at this
    have hmeas := measurable_cylFn P m hA'
    rw [hset, ih hA' ((natFilt (X := X)).mono (Nat.le_succ n) _ hG'),
      setLIntegral_succ P μ hG' hmeas]
    have hmn : MeasurableSet ((fun ω : ℕ → X => ω n) ⁻¹' A 0) := measurable_pi_apply n (hA 0)
    have hind : (fun ω : ℕ → X => cylFn P (m + 1) A (ω n)) =
        ((fun ω : ℕ → X => ω n) ⁻¹' A 0).indicator
          (fun ω => ∫⁻ y, cylFn P m A' y ∂P (ω n)) := by
      ext ω; by_cases h : ω n ∈ A 0 <;> simp [cylFn, h, A']
    rw [hind, setLIntegral_indicator hmn, inter_comm]
    rfl

/-- `P_x(Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ) = cylFn P n A x`. -/
theorem pathKernel_boxSet (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) : pathKernel P x (boxSet n A) = cylFn P n A x := by
  have h := measure_inter_shift_box P (Measure.dirac x) n hA (n := 0) MeasurableSet.univ
  simp only [univ_inter, Measure.restrict_univ, zero_add] at h
  rw [pathMeasure_dirac] at h
  rw [boxSet, h, ← lintegral_map (measurable_cylFn P n hA) (measurable_pi_apply 0),
    pathKernel_map_zero, lintegral_dirac' _ (measurable_cylFn P n hA)]

/-- Under `P_μ`, `P_μ(Φ₀ ∈ A₀, …, Φₙ ∈ Aₙ) = ∫ cylFn P n A dμ`: this is (3.20). -/
theorem pathMeasure_boxSet (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) (n : ℕ)
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    pathMeasure P μ (boxSet n A) = ∫⁻ x, cylFn P n A x ∂μ := by
  have := isMarkovKernel_pathKernel P
  rw [pathMeasure_eq_comp, Measure.bind_apply (measurableSet_boxSet n hA)
    (Kernel.aemeasurable _)]
  exact lintegral_congr fun x => pathKernel_boxSet P x n hA

/-! ### Markov chains and Theorem 3.4.1 -/

variable {Ω : Type*} [MeasurableSpace Ω] (P : Kernel X X) (μ : Measure X) (pr : Measure Ω) in
/-- A process `Φ` on `(Ω, ℙ)` is a time-homogeneous Markov chain with transition kernel `P` and
initial distribution `μ` if its finite-dimensional distributions are given by (3.20)
(MT p. 61). -/
structure IsMarkovChain (Φ : ℕ → Ω → X) : Prop where
  /-- Each `Φₙ` is a random variable. -/
  measurable : ∀ n, Measurable (Φ n)
  /-- The finite-dimensional distributions are (3.20). -/
  fdd : ∀ n (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) →
    pr {ω | ∀ i ≤ n, Φ i ω ∈ A i} = ∫⁻ x, cylFn P n A x ∂μ

/-- **Theorem 3.4.1** (MT p. 60), existence. For every initial distribution `μ` and every
transition probability kernel `P`, the coordinate process on `(ℕ → X, P_μ)` is a Markov chain
with kernel `P` and initial distribution `μ`, and `P_μ` is a probability measure. -/
theorem mt_theorem_3_4_1 (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (pathMeasure P μ) ∧
      IsMarkovChain P μ (pathMeasure P μ) (fun n ω => ω n) :=
  ⟨isProbabilityMeasure_pathMeasure P μ,
    ⟨fun n => measurable_pi_apply n, fun n _ hA => pathMeasure_boxSet P μ n hA⟩⟩

/-- Boxes generate the product σ-algebra on path space. -/
theorem generateFrom_boxSets :
    (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) = MeasurableSpace.generateFrom
      {S | ∃ n, ∃ A : ℕ → Set X, (∀ i, MeasurableSet (A i)) ∧ S = boxSet n A} := by
  refine le_antisymm ?_ ?_
  · rw [← generateFrom_squareCylinders]
    refine MeasurableSpace.generateFrom_le fun S hS => ?_
    obtain ⟨s, t, ht, rfl⟩ := hS
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨s.sup id, fun i => if i ∈ s then t i else univ, fun i => ?_, ?_⟩
    · by_cases hi : i ∈ s
      · simpa [hi] using ht i (mem_univ i)
      · simp [hi]
    · ext ω
      simp only [boxSet, Set.mem_pi, Finset.mem_coe, mem_ofPred_eq]
      constructor
      · intro h i _
        by_cases hi : i ∈ s
        · simpa [hi] using h i hi
        · simp [hi]
      · intro h i hi
        have := h i (Finset.le_sup (f := id) hi)
        simpa [hi] using this
  · refine MeasurableSpace.generateFrom_le fun S hS => ?_
    obtain ⟨n, A, hA, rfl⟩ := hS
    exact measurableSet_boxSet n hA

/-- Boxes form a π-system. -/
theorem isPiSystem_boxSets :
    IsPiSystem {S : Set (ℕ → X) | ∃ n, ∃ A : ℕ → Set X, (∀ i, MeasurableSet (A i)) ∧
      S = boxSet n A} := by
  rintro _ ⟨n, A, hA, rfl⟩ _ ⟨m, B, hB, rfl⟩ _
  refine ⟨max n m, fun i => (if i ≤ n then A i else univ) ∩ (if i ≤ m then B i else univ),
    fun i => ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_ <;> split_ifs <;> simp_all
  · ext ω
    simp only [boxSet, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ i _
      constructor <;> split_ifs with h
      · exact h1 i h
      · trivial
      · exact h2 i h
      · trivial
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · simpa [hi] using (h i (le_max_of_le_left hi)).1
      · simpa [hi] using (h i (le_max_of_le_right hi)).2

/-- **Theorem 3.4.1**, uniqueness: `P_μ` is the only probability measure on path space whose
finite-dimensional distributions are given by (3.20). -/
theorem mt_theorem_3_4_1_unique (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure (ℕ → X)) [IsFiniteMeasure ν]
    (hν : ∀ n (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) →
      ν (boxSet n A) = ∫⁻ x, cylFn P n A x ∂μ) :
    ν = pathMeasure P μ := by
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨n, A, hA, rfl⟩
    rw [hν n A hA, pathMeasure_boxSet P μ n hA]
  · have hu : (univ : Set (ℕ → X)) = boxSet 0 (fun _ => univ) := by ext; simp [boxSet]
    rw [hu, hν 0 _ fun _ => MeasurableSet.univ,
      pathMeasure_boxSet P μ 0 fun _ => MeasurableSet.univ]

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- Every Markov chain with transition kernel `P` and initial distribution `μ` has law `P_μ`
on path space: the law of a Markov chain is determined by `P` and `μ`. -/
theorem law_eq_pathMeasure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {pr : Measure Ω} {Φ : ℕ → Ω → X} (h : IsMarkovChain P μ pr Φ) :
    pr.map (fun ω n => Φ n ω) = pathMeasure P μ := by
  have hΦ : Measurable fun ω n => Φ n ω := measurable_pi_iff.2 h.measurable
  have hbox : ∀ n (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) →
      pr.map (fun ω n => Φ n ω) (boxSet n A) = ∫⁻ x, cylFn P n A x ∂μ := fun n A hA => by
    rw [Measure.map_apply hΦ (measurableSet_boxSet n hA)]
    exact h.fdd n A hA
  have : IsFiniteMeasure (pr.map fun ω n => Φ n ω) := by
    refine ⟨?_⟩
    have hu : (univ : Set (ℕ → X)) = boxSet 0 (fun _ => univ) := by ext; simp [boxSet]
    rw [hu, hbox 0 _ fun _ => MeasurableSet.univ]
    simp [cylFn]
  exact mt_theorem_3_4_1_unique P μ _ hbox

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition kernels, `n`-step kernels and their operators (MT §3.4.1–3.4.2)

Copied from `EconomicDynamics/ErgodicTheory` (module `Kernels`), namespace renamed.

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/Kernels.lean`), namespace renamed to `Miao.StructuralEstimation` and the
Meyn–Tweedie-numbered results prefixed `mt_`.

Meyn and Tweedie, §3.4.1–3.4.2, pp. 59–62. A transition probability kernel on `X` is a Markov
kernel `P : Kernel X X` (p. 59); a general kernel on `X` is a `Kernel X X` (p. 60). The `n`-step
kernel `Pⁿ` is the `n`-th power in Mathlib's monoid of kernels, where `P * Q = P ∘ₖ Q` is "first
`Q`, then `P`"; powers of one kernel commute, so `Pⁿ` agrees with the book's `Pⁿ`.

* `IsSubstochasticKernel` (p. 59): `T(x, X) ≤ 1`.
* `pow_zero_apply` (3.21): `P⁰(x, A) = δ_x(A)`; `pow_succ_apply` (3.22):
  `Pⁿ⁺¹(x, A) = ∫ P(x, dy) Pⁿ(y, A)`; `isMarkovKernel_pow`: `Pⁿ` is a transition kernel.
* **Theorem 3.4.2** (`mt_theorem_3_4_2`, p. 61): the Chapman–Kolmogorov equations
  `Pⁿ(x, A) = ∫ Pᵐ(x, dy) Pⁿ⁻ᵐ(y, A)`; `pow_add_eq` (p. 62): `Pᵐ⁺ⁿ = PᵐPⁿ`.
* `skeleton` (3.25), `skeleton_pow`: the `m`-skeleton has `n`-step kernel `Pᵐⁿ`.
* `sampledKernel` (`K_a = Σ a(n) Pⁿ`), `resolvent` (3.26) (`K_{a_ε} = (1 − ε) Σ εⁱ Pⁱ`) and
  `isMarkovKernel_sampledKernel`, `isMarkovKernel_resolvent`: they are transition kernels
  when `a` is a probability on `ℕ` and `0 ≤ ε < 1`.
* The operators of p. 62: `kfun P f = Pf` on nonnegative functions, `P ∘ₘ μ = μP` on measures,
  with `kfun_comp` (`P(Qf) = (PQ)f`), `measure_kernel_assoc` (`(μP)Q = μ(PQ)`), the duality
  `lintegral_kfun` (`∫ Pf dμ = ∫ f d(μP)`), `kfun_one` (`P1 = 1`), linearity and monotonicity;
  `kfunR` on bounded real functions, with `abs_kfunR_le` and `measurable_kfunR`.
* `indKernel` (p. 66): the kernel `I_B(x, A) = 1_{A ∩ B}(x)`, and `comp_indKernel_apply`:
  `(P I_B)(x, A) = P(x, A ∩ B)`.
* `potKernel` (3.30): `U = Σ_{n ≥ 1} Pⁿ`.

**Corrections.** None.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Substochastic kernels and `n`-step kernels -/

/-- A substochastic transition kernel: `T(x, X) ≤ 1` for every `x` (MT p. 59). -/
def IsSubstochasticKernel (T : Kernel X X) : Prop := ∀ x, T x univ ≤ 1

/-- A transition probability kernel is substochastic. -/
theorem isSubstochasticKernel_of_markov (P : Kernel X X) [IsMarkovKernel P] :
    IsSubstochasticKernel P := fun x => by simp

/-- `Pⁿ` is a transition probability kernel. -/
theorem isMarkovKernel_pow (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (P ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((P ^ n) ∘ₖ P))

/-- (3.21): `P⁰(x, A) = δ_x(A)`. -/
theorem pow_zero_apply (P : Kernel X X) (x : X) : (P ^ 0) x = Measure.dirac x := by
  rw [pow_zero]; rfl

/-- (3.22): `Pⁿ⁺¹(x, A) = ∫ P(x, dy) Pⁿ(y, A)`. -/
theorem pow_succ_apply (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (P ^ (n + 1)) x A = ∫⁻ y, (P ^ n) y A ∂P x := by
  rw [pow_succ]
  exact Kernel.comp_apply' _ _ _ hA

/-- `Pⁿ⁺¹(x, A) = ∫ Pⁿ(x, dy) P(y, A)`. -/
theorem pow_succ_apply' (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (P ^ (n + 1)) x A = ∫⁻ y, P y A ∂(P ^ n) x :=
  Kernel.pow_succ_apply_eq_lintegral P n x hA

/-- **Theorem 3.4.2** (Chapman–Kolmogorov, MT p. 61). For `m ≤ n`,
`Pⁿ(x, A) = ∫ Pᵐ(x, dy) Pⁿ⁻ᵐ(y, A)`. -/
theorem mt_theorem_3_4_2 (P : Kernel X X) {m n : ℕ} (hmn : m ≤ n) (x : X) {A : Set X}
    (hA : MeasurableSet A) : (P ^ n) x A = ∫⁻ y, (P ^ (n - m)) y A ∂(P ^ m) x := by
  have := Kernel.pow_add_apply_eq_lintegral P m (n - m) x hA
  rwa [Nat.add_sub_cancel' hmn] at this

/-- The Chapman–Kolmogorov equations in operator form (MT p. 62): `Pᵐ⁺ⁿ = PᵐPⁿ`, where `PᵐPⁿ`
is "first `Pᵐ`, then `Pⁿ`". -/
theorem pow_add_eq (P : Kernel X X) (m n : ℕ) : P ^ (m + n) = (P ^ n) ∘ₖ (P ^ m) := by
  rw [add_comm]; exact Kernel.pow_add P n m

/-- The `m`-skeleton: the chain with transition kernel `Pᵐ` (3.25), MT p. 62. -/
noncomputable abbrev skeleton (P : Kernel X X) (m : ℕ) : Kernel X X := P ^ m

/-- The `n`-step kernel of the `m`-skeleton is `Pᵐⁿ` (3.25). -/
theorem skeleton_pow (P : Kernel X X) (m n : ℕ) : skeleton P m ^ n = P ^ (m * n) :=
  (pow_mul P m n).symm

/-! ### Sampled kernels and resolvents -/

/-- The sampled kernel `K_a = Σₙ a(n) Pⁿ` for weights `a : ℕ → [0, ∞]` (MT p. 62; the
`K_a`-chains of Chapter 5). -/
noncomputable def sampledKernel (P : Kernel X X) (a : ℕ → ℝ≥0∞) : Kernel X X where
  toFun x := Measure.sum fun n => a n • (P ^ n) x
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum fun n => (Kernel.measurable_coe _ hs).const_mul _

/-- `K_a(x, A) = Σₙ a(n) Pⁿ(x, A)`. -/
theorem sampledKernel_apply (P : Kernel X X) (a : ℕ → ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) : sampledKernel P a x A = ∑' n, a n * (P ^ n) x A := by
  change (Measure.sum fun n => a n • (P ^ n) x) A = _
  rw [Measure.sum_apply _ hA]
  rfl

/-- `K_a` is a transition probability kernel when `a` is a probability on `ℕ`. -/
theorem isMarkovKernel_sampledKernel (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : ∑' n, a n = 1) : IsMarkovKernel (sampledKernel P a) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have := isMarkovKernel_pow P
  rw [sampledKernel_apply P a x MeasurableSet.univ]
  simpa using ha

/-- The resolvent `K_{a_ε} = (1 − ε) Σᵢ εⁱ Pⁱ` (3.26), MT p. 62. -/
noncomputable def resolvent (P : Kernel X X) (ε : ℝ≥0∞) : Kernel X X :=
  sampledKernel P fun n => (1 - ε) * ε ^ n

/-- (3.26): `K_{a_ε}(x, A) = (1 − ε) Σᵢ εⁱ Pⁱ(x, A)`. -/
theorem resolvent_apply (P : Kernel X X) (ε : ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) : resolvent P ε x A = (1 - ε) * ∑' i, ε ^ i * (P ^ i) x A := by
  rw [resolvent, sampledKernel_apply P _ x hA, ← ENNReal.tsum_mul_left]
  simp_rw [mul_assoc]

/-- The geometric weights `(1 − ε) εⁿ` sum to one for `ε < 1`. -/
theorem tsum_geometric_weights {ε : ℝ≥0∞} (hε : ε < 1) : ∑' n, (1 - ε) * ε ^ n = 1 := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_inv_cancel (tsub_pos_of_lt hε).ne' (by simp)

/-- The resolvent is a transition probability kernel for `ε < 1`. -/
theorem isMarkovKernel_resolvent (P : Kernel X X) [IsMarkovKernel P] {ε : ℝ≥0∞} (hε : ε < 1) :
    IsMarkovKernel (resolvent P ε) :=
  isMarkovKernel_sampledKernel P (tsum_geometric_weights hε)

/-! ### The operators `Pf` and `μP` -/

/-- `Pf(x) = ∫ P(x, dy) f(y)` for nonnegative `f` (MT p. 62). -/
noncomputable def kfun (P : Kernel X X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ := ∫⁻ y, f y ∂P x

/-- `Pf` is measurable for measurable `f`. -/
theorem measurable_kfun (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (kfun P f) := hf.lintegral_kernel

/-- `P 1_A (x) = P(x, A)`. -/
theorem kfun_indicator (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : X) :
    kfun P (A.indicator 1) x = P x A := lintegral_indicator_one hA

/-- `P1 = 1` for a transition probability kernel. -/
theorem kfun_one (P : Kernel X X) [IsMarkovKernel P] : kfun P 1 = 1 := by
  ext x; simp [kfun]

/-- `P` is monotone. -/
theorem kfun_mono (P : Kernel X X) {f g : X → ℝ≥0∞} (hfg : f ≤ g) : kfun P f ≤ kfun P g :=
  fun _ => lintegral_mono fun y => hfg y

/-- `P` is additive. -/
theorem kfun_add (P : Kernel X X) {f g : X → ℝ≥0∞} (hf : Measurable f) :
    kfun P (f + g) = kfun P f + kfun P g := by
  ext x; exact lintegral_add_left hf g

/-- `P` is positively homogeneous. -/
theorem kfun_const_mul (P : Kernel X X) (c : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    kfun P (fun y => c * f y) = fun x => c * kfun P f x := by
  ext x; exact lintegral_const_mul c hf

/-- `P(Qf) = (PQ)f`, where `PQ` is "first `P`, then `Q`", i.e. `Q ∘ₖ P`. -/
theorem kfun_comp (P Q : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    kfun P (kfun Q f) = kfun (Q ∘ₖ P) f := by
  ext x; exact (Kernel.lintegral_comp Q P x hf).symm

/-- `Pⁿ⁺¹f = P(Pⁿf)`. -/
theorem kfun_pow_succ (P : Kernel X X) (n : ℕ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    kfun (P ^ (n + 1)) f = kfun P (kfun (P ^ n) f) := by
  rw [kfun_comp P (P ^ n) hf, pow_succ]
  rfl

/-- `μP(A) = ∫ μ(dx) P(x, A)` (MT p. 62). -/
theorem measure_kernel_apply (μ : Measure X) (P : Kernel X X) {A : Set X}
    (hA : MeasurableSet A) : (P ∘ₘ μ) A = ∫⁻ x, P x A ∂μ :=
  Measure.bind_apply hA P.aemeasurable

/-- `(μP)Q = μ(PQ)`. -/
theorem measure_kernel_assoc (μ : Measure X) (P Q : Kernel X X) :
    Q ∘ₘ (P ∘ₘ μ) = (Q ∘ₖ P) ∘ₘ μ := Measure.comp_assoc

/-- Duality: `∫ Pf dμ = ∫ f d(μP)`. -/
theorem lintegral_kfun (μ : Measure X) (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, kfun P f x ∂μ = ∫⁻ y, f y ∂(P ∘ₘ μ) :=
  (Measure.lintegral_bind P.aemeasurable hf.aemeasurable).symm

/-- `μP` is a probability measure when `μ` is and `P` is Markov. -/
theorem isProbabilityMeasure_measure_kernel (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P] : IsProbabilityMeasure (P ∘ₘ μ) := by
  infer_instance

/-- `δ_x P = P(x, ·)`. -/
theorem dirac_kernel (P : Kernel X X) (x : X) : P ∘ₘ Measure.dirac x = P x :=
  Measure.dirac_bind P.measurable x

/-- `Pf(x) = ∫ P(x, dy) f(y)` for real `f` (MT p. 62). -/
noncomputable def kfunR (P : Kernel X X) (f : X → ℝ) (x : X) : ℝ := ∫ y, f y ∂P x

/-- `Pf` is measurable for measurable real `f`. -/
theorem measurable_kfunR (P : Kernel X X) [IsSFiniteKernel P] {f : X → ℝ}
    (hf : Measurable f) : Measurable (kfunR P f) :=
  (StronglyMeasurable.integral_kernel (κ := P) hf.stronglyMeasurable).measurable

/-- `|Pf| ≤ B` when `|f| ≤ B`. -/
theorem abs_kfunR_le (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (x : X) : |kfunR P f x| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P x) (f := f) (C := B)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  simpa [kfunR] using this

/-! ### The kernels `I_B` and `U` -/

/-- The kernel `I_B(x, A) = 1_{A ∩ B}(x)` (MT p. 66). -/
noncomputable def indKernel {B : Set X} (hB : MeasurableSet B) : Kernel X X :=
  Kernel.id.restrict hB

/-- `I_B(x, A) = 1_{A ∩ B}(x)`. -/
theorem indKernel_apply {B : Set X} (hB : MeasurableSet B) (x : X) {A : Set X}
    (hA : MeasurableSet A) : indKernel hB x A = (A ∩ B).indicator 1 x := by
  rw [indKernel, Kernel.restrict_apply' _ _ _ hA, Kernel.id_apply,
    Measure.dirac_apply' _ (hA.inter hB)]

/-- `(P I_B)(x, A) = P(x, A ∩ B)`: "move by `P`, then kill the path outside `B`". -/
theorem comp_indKernel_apply (P : Kernel X X) {B : Set X} (hB : MeasurableSet B) (x : X)
    {A : Set X} (hA : MeasurableSet A) : (indKernel hB ∘ₖ P) x A = P x (A ∩ B) := by
  rw [Kernel.comp_apply' _ _ _ hA]
  simp_rw [indKernel_apply hB _ hA]
  exact lintegral_indicator_one (hA.inter hB)

/-- `P I_B` is substochastic. -/
theorem isSubstochasticKernel_comp_indKernel (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) : IsSubstochasticKernel (indKernel hB ∘ₖ P) := fun x => by
  rw [comp_indKernel_apply P hB x MeasurableSet.univ]
  exact prob_le_one

/-- The potential kernel `U = Σ_{n ≥ 1} Pⁿ` (3.30), MT p. 64. -/
noncomputable def potKernel (P : Kernel X X) : Kernel X X := Kernel.sum fun n => P ^ (n + 1)

/-- (3.30): `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A)`. -/
theorem potKernel_apply (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    potKernel P x A = ∑' n, (P ^ (n + 1)) x A :=
  Kernel.sum_apply' _ _ hA

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Markov property (MT §3.4.2)

Copied from `EconomicDynamics/ErgodicTheory` (module `MarkovProperty`), namespace renamed.

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/MarkovProperty.lean`), namespace renamed to `Miao.StructuralEstimation` and the
Meyn–Tweedie-numbered results prefixed `mt_`.

Meyn and Tweedie, §3.4.2, pp. 61–63. `shift n` is the shift `θⁿ` on paths,
`(θⁿω)ᵢ = ω_{n+i}` (p. 63), so `H ∘ θⁿ = θⁿH`.

* `pathMeasure_map_coord`, `pathKernel_map_coord` (3.8): the law of `Φₙ` under `P_μ` is `μPⁿ`,
  and `P_x(Φₙ ∈ A) = Pⁿ(x, A)`; `pathKernel_coord_chapmanKolmogorov` is (3.24).
* `markov_measure`: for `G ∈ 𝓕ₙ^Φ`, the law of `θⁿΦ` on `G` is `∫_G P_{Φₙ}(·) dP_μ`. This is the
  Markov property in its strongest form, as an identity of measures on path space.
* `markov_lintegral_mul`: `E_μ[F · H ∘ θⁿ] = E_μ[F · E_{Φₙ}[H]]` for `𝓕ₙ^Φ`-measurable `F ≥ 0`.
* `markov_lintegral`, `markov_setIntegral`: `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ` for
  nonnegative and for integrable `H`.
* `markov_property` (3.28), p. 63: `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for every
  measurable `H` with `θⁿH` integrable; `markov_property_bdd` for bounded `H`.
* **Proposition 3.4.3** (`mt_proposition_3_4_3`, p. 63), (3.27):
  `E_μ[h(Φₙ₊₁, Φₙ₊₂, …) | Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]` for bounded measurable `h`.
* `isMarkovChain_of_step`: a process adapted to a filtration whose one-step conditional laws are
  given by `Q` is a Markov chain with kernel `Q`. Hence `skeleton_isMarkovChain` (3.25),
  p. 61: the `m`-skeleton `(Φ_{mn})ₙ` is a Markov chain with transition kernel `Pᵐ`.

**Corrections.** None. The book states (3.27) and (3.28) for bounded `h`; they hold for every
`h` with `θⁿH` integrable (`markov_property`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The shift -/

/-- The shift `θⁿ` on paths: `(θⁿω)ᵢ = ω_{n+i}` (MT p. 63). -/
def shift (n : ℕ) (ω : ℕ → X) : ℕ → X := fun i => ω (n + i)

/-- The shift is measurable. -/
theorem measurable_shift (n : ℕ) : Measurable (shift (X := X) n) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (n + i)

omit [MeasurableSpace X] in
/-- `θ⁰ = id`. -/
@[simp] theorem shift_zero (ω : ℕ → X) : shift 0 ω = ω := by
  ext i; simp [shift]

omit [MeasurableSpace X] in
/-- `θᵐ ∘ θⁿ = θⁿ⁺ᵐ`. -/
theorem shift_shift (m n : ℕ) (ω : ℕ → X) : shift m (shift n ω) = shift (n + m) ω := by
  ext i; simp [shift, add_assoc]

omit [MeasurableSpace X] in
/-- `Φᵢ ∘ θⁿ = Φₙ₊ᵢ` (MT p. 63). -/
@[simp] theorem shift_apply (n i : ℕ) (ω : ℕ → X) : shift n ω i = ω (n + i) := rfl

/-! ### Integrals against `κ ∘ₘ ν` -/

/-- `∫ f d(κ ∘ₘ ν) = ∫ ∫ f dκ(x) ν(dx)` for integrable `f`. -/
theorem integral_measure_comp {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν] {f : Z → ℝ}
    (hf : Integrable f (κ ∘ₘ ν)) : ∫ z, f z ∂(κ ∘ₘ ν) = ∫ y, ∫ z, f z ∂κ y ∂ν := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-! ### The law of `Φₙ` -/

/-- (3.8): the law of `Φₙ` under `P_μ` is `μPⁿ`. -/
theorem pathMeasure_map_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (pathMeasure P μ).map (fun ω => ω n) = (P ^ n) ∘ₘ μ := by
  induction n with
  | zero => rw [pathMeasure_map_zero, pow_zero]; exact Measure.id_comp.symm
  | succ n ih =>
    ext A hA
    have hmA : Measurable (fun y => P y A) := Kernel.measurable_coe _ hA
    rw [Measure.map_apply (measurable_pi_apply (n + 1) : Measurable fun ω : ℕ → X => ω (n + 1))
      hA, ← lintegral_indicator_one (measurable_pi_apply (n + 1) hA)]
    have h1 := setLIntegral_succ P μ (n := n) MeasurableSet.univ
      (measurable_one.indicator hA : Measurable (A.indicator (1 : X → ℝ≥0∞)))
    simp only [Measure.restrict_univ, lintegral_indicator_one hA] at h1
    have h2 : ((fun ω : ℕ → X => ω (n + 1)) ⁻¹' A).indicator (1 : (ℕ → X) → ℝ≥0∞) =
        fun ω => A.indicator 1 (ω (n + 1)) := by
      ext ω; by_cases h : ω (n + 1) ∈ A <;> simp [h]
    rw [h2, h1, ← lintegral_map hmA (measurable_pi_apply n), ih, pow_succ',
      ← measure_kernel_apply _ _ hA, measure_kernel_assoc]
    rfl

/-- (3.8): `P_x(Φₙ ∈ ·) = Pⁿ(x, ·)`. -/
theorem pathKernel_map_coord (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) :
    (pathKernel P x).map (fun ω => ω n) = (P ^ n) x := by
  rw [← pathMeasure_dirac, pathMeasure_map_coord, dirac_kernel]

/-- `P_x(Φₙ ∈ A) = Pⁿ(x, A)`. -/
theorem pathKernel_coord_mem (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) {A : Set X}
    (hA : MeasurableSet A) : pathKernel P x {ω | ω n ∈ A} = (P ^ n) x A := by
  rw [← pathKernel_map_coord P x n,
    Measure.map_apply (measurable_pi_apply n : Measurable fun ω : ℕ → X => ω n) hA]
  rfl

/-- (3.24), MT p. 61: `P_x(Φₙ ∈ A) = ∫ P_x(Φₘ ∈ dy) P_y(Φₙ₋ₘ ∈ A)` for `m ≤ n`. -/
theorem pathKernel_coord_chapmanKolmogorov (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {m n : ℕ} (hmn : m ≤ n) {A : Set X} (hA : MeasurableSet A) :
    pathKernel P x {ω | ω n ∈ A} =
      ∫⁻ y, pathKernel P y {ω | ω (n - m) ∈ A} ∂(pathKernel P x).map (fun ω => ω m) := by
  simp_rw [pathKernel_coord_mem P _ _ hA, pathKernel_map_coord]
  exact mt_theorem_3_4_2 P hmn x hA

/-! ### The Markov property -/

/-- **The Markov property as an identity of measures.** For `G ∈ 𝓕ₙ^Φ`, the law of the shifted
path `θⁿΦ` restricted to `G` is the mixture of the `P_y` over the law of `Φₙ` restricted to
`G`. -/
theorem markov_measure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G) :
    ((pathMeasure P μ).restrict G).map (shift n) =
      pathKernel P ∘ₘ (((pathMeasure P μ).restrict G).map fun ω => ω n) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have := isMarkovKernel_pathKernel P
  have hGm : MeasurableSet G := (natFilt (X := X)).le n _ hG
  have hn : Measurable fun ω : ℕ → X => ω n := measurable_pi_apply n
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨m, A, hA, rfl⟩
    have hB := measurableSet_boxSet m hA
    rw [Measure.map_apply (measurable_shift n) hB, Measure.restrict_apply
      (measurable_shift n hB), Measure.bind_apply hB (Kernel.aemeasurable _),
      lintegral_map (Kernel.measurable_coe _ hB) hn, inter_comm]
    simp_rw [pathKernel_boxSet P _ m hA]
    exact measure_inter_shift_box P μ m hA hG
  · rw [Measure.map_apply (measurable_shift n) MeasurableSet.univ,
      Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp [Measure.map_apply hn MeasurableSet.univ]

/-- **The Markov property** for nonnegative functionals: for `G ∈ 𝓕ₙ^Φ` and measurable
`H ≥ 0`, `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ`. -/
theorem markov_lintegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in G, H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω in G, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  rw [← lintegral_map hH (measurable_shift n), markov_measure P μ hG,
    Measure.lintegral_bind (Kernel.aemeasurable _) hH.aemeasurable,
    lintegral_map hH.lintegral_kernel (measurable_pi_apply n)]

/-- **The Markov property** with an `𝓕ₙ^Φ`-measurable weight: for `F ≥ 0` measurable for
`𝓕ₙ^Φ` and measurable `H ≥ 0`, `E_μ[F · H ∘ θⁿ] = E_μ[F · E_{Φₙ}[H]]`. -/
theorem markov_lintegral_mul (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {F : (ℕ → X) → ℝ≥0∞} (hF : Measurable[natFilt n] F)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, F ω * H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω, F ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have hle := (natFilt (X := X)).le n
  have hG : Measurable fun ω => H (shift n ω) := hH.comp (measurable_shift n)
  have hK : Measurable fun ω : ℕ → X => ∫⁻ ω', H ω' ∂pathKernel P (ω n) :=
    hH.lintegral_kernel.comp (measurable_pi_apply n)
  refine Measurable.ennreal_induction (motive := fun F => ∫⁻ ω, F ω * H (shift n ω)
      ∂pathMeasure P μ = ∫⁻ ω, F ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ)
    ?_ ?_ ?_ hF
  · intro c s hs
    have hs' : MeasurableSet s := hle _ hs
    have e1 : ∀ ω, s.indicator (fun _ => c) ω * H (shift n ω) =
        s.indicator (fun ω => c * H (shift n ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∀ ω, s.indicator (fun _ => c) ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n) =
        s.indicator (fun ω => c * ∫⁻ ω', H ω' ∂pathKernel P (ω n)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    simp_rw [e1, e2, lintegral_indicator hs', lintegral_const_mul _ hG,
      lintegral_const_mul _ hK, markov_lintegral P μ hs hH]
  · intro f g _ hf hg ihf ihg
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => f ω * H (shift n ω)) ((hf.mono hle le_rfl).mul hG),
      lintegral_add_left (f := fun ω => f ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n))
        ((hf.mono hle le_rfl).mul hK), ihf, ihg]
  · intro f hf hmono ih
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun k ω => f k ω * H (shift n ω))
        (fun k => ((hf k).mono hle le_rfl).mul hG)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _),
      lintegral_iSup (f := fun k ω => f k ω * ∫⁻ ω', H ω' ∂pathKernel P (ω n))
        (fun k => ((hf k).mono hle le_rfl).mul hK)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _)]
    simp_rw [ih]

/-- The unconditional form: `E_μ[H ∘ θⁿ] = E_μ[E_{Φₙ}[H]]`. -/
theorem markov_lintegral_univ (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (shift n ω) ∂pathMeasure P μ =
      ∫⁻ ω, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  simpa using markov_lintegral P μ (n := n) MeasurableSet.univ hH

/-- **The Markov property** for integrable functionals: for `G ∈ 𝓕ₙ^Φ` and measurable `H` with
`H ∘ θⁿ` integrable on `G`, `∫_G H ∘ θⁿ dP_μ = ∫_G E_{Φₙ}[H] dP_μ`. -/
theorem markov_setIntegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : IntegrableOn (fun ω => H (shift n ω)) G (pathMeasure P μ)) :
    ∫ ω in G, H (shift n ω) ∂pathMeasure P μ =
      ∫ ω in G, ∫ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hmeas := markov_measure P μ hG
  have hi : Integrable H (((pathMeasure P μ).restrict G).map (shift n)) :=
    (integrable_map_measure hH.aestronglyMeasurable (measurable_shift n).aemeasurable).2 hint
  rw [hmeas] at hi
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  calc ∫ ω in G, H (shift n ω) ∂pathMeasure P μ
      = ∫ ω', H ω' ∂(((pathMeasure P μ).restrict G).map (shift n)) :=
        (integral_map (measurable_shift n).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ ω', H ω' ∂(pathKernel P ∘ₘ (((pathMeasure P μ).restrict G).map fun ω => ω n)) := by
        rw [hmeas]
    _ = ∫ y, ∫ ω', H ω' ∂pathKernel P y ∂(((pathMeasure P μ).restrict G).map fun ω => ω n) :=
        integral_measure_comp _ _ hi
    _ = ∫ ω in G, ∫ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        integral_map (measurable_pi_apply n).aemeasurable hk.aestronglyMeasurable

/-- `ω ↦ E_{Φₙ(ω)}[H]` is `𝓕ₙ^Φ`-strongly measurable. -/
theorem stronglyMeasurable_expect_coord (P : Kernel X X) [IsMarkovKernel P] (n : ℕ)
    {H : (ℕ → X) → ℝ} (hH : Measurable H) :
    StronglyMeasurable[natFilt n] fun ω : ℕ → X => ∫ ω', H ω' ∂pathKernel P (ω n) := by
  have := isMarkovKernel_pathKernel P
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  exact hk.comp_measurable (measurable_coord_natFilt n)

/-- `ω ↦ E_{Φₙ(ω)}[H]` is integrable when `H ∘ θⁿ` is. -/
theorem integrable_expect_coord (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ)) :
    Integrable (fun ω : ℕ → X => ∫ ω', H ω' ∂pathKernel P (ω n)) (pathMeasure P μ) := by
  refine ⟨((stronglyMeasurable_expect_coord P n hH).mono
    ((natFilt (X := X)).le n)).aestronglyMeasurable, ?_⟩
  have hlin := markov_lintegral_univ P μ n (H := fun ω => ‖H ω‖ₑ) hH.enorm
  calc ∫⁻ ω, ‖∫ ω', H ω' ∂pathKernel P (ω n)‖ₑ ∂pathMeasure P μ
      ≤ ∫⁻ ω, ∫⁻ ω', ‖H ω'‖ₑ ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ‖H (shift n ω)‖ₑ ∂pathMeasure P μ := hlin.symm
    _ < ∞ := hint.2

/-- **The Markov property** (3.28), MT p. 63: `E_μ[θⁿH | 𝓕ₙ^Φ] = E_{Φₙ}[H]`, `P_μ`-a.s., for
measurable `H` with `θⁿH` integrable. -/
theorem markov_property (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ)) :
    (pathMeasure P μ)[fun ω => H (shift n ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', H ω' ∂pathKernel P (ω n) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hg := integrable_expect_coord P μ n hH hint
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((natFilt (X := X)).le n) hint
    (fun s _ _ => hg.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_expect_coord P n hH).aestronglyMeasurable).symm
  exact (markov_setIntegral P μ hs hH hint.integrableOn).symm

/-- `H ∘ θⁿ` is integrable for bounded measurable `H`. -/
theorem integrable_shift_of_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) : Integrable (fun ω => H (shift n ω)) (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  exact Integrable.of_bound (hH.comp (measurable_shift n)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)

/-- (3.28) for bounded measurable `H`, as stated in MT p. 63. -/
theorem markov_property_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {H : (ℕ → X) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) :
    (pathMeasure P μ)[fun ω => H (shift n ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', H ω' ∂pathKernel P (ω n) :=
  markov_property P μ n hH (integrable_shift_of_bdd P μ n hH hB)

/-- **Proposition 3.4.3** (MT p. 63), (3.27): for bounded measurable `h` on path space,
`E_μ[h(Φₙ₊₁, Φₙ₊₂, …) | Φ₀, …, Φₙ] = E_{Φₙ}[h(Φ₁, Φ₂, …)]`, `P_μ`-a.s. -/
theorem mt_proposition_3_4_3 (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) {h : (ℕ → X) → ℝ} (hh : Measurable h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    (pathMeasure P μ)[fun ω => h (shift (n + 1) ω) | natFilt n] =ᵐ[pathMeasure P μ]
      fun ω => ∫ ω', h (shift 1 ω') ∂pathKernel P (ω n) := by
  have := markov_property_bdd P μ n (hh.comp (measurable_shift 1)) (fun ω => hB (shift 1 ω))
  simp only [Function.comp_apply, shift_shift] at this
  exact this

/-! ### Markov chains from the one-step property; skeletons -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] in
/-- A process `Ψ` adapted to a filtration `𝓖`, with `Ψ₀ ∼ μ` and one-step conditional laws given
by `Q` (`∫_G f(Ψₙ₊₁) = ∫_G Qf(Ψₙ)` for `G ∈ 𝓖ₙ`), is a Markov chain with kernel `Q` and initial
distribution `μ`. -/
theorem isMarkovChain_of_step (Q : Kernel X X) (μ : Measure X) {pr : Measure Ω}
    {Ψ : ℕ → Ω → X} {𝓖 : Filtration ℕ mΩ} (hΨ : ∀ n, Measurable[𝓖 n] (Ψ n))
    (h0 : pr.map (Ψ 0) = μ)
    (hstep : ∀ n G, MeasurableSet[𝓖 n] G → ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ ω in G, f (Ψ (n + 1) ω) ∂pr = ∫⁻ ω in G, ∫⁻ y, f y ∂Q (Ψ n ω) ∂pr) :
    IsMarkovChain Q μ pr Ψ := by
  have hΨm : ∀ n, Measurable (Ψ n) := fun n => (hΨ n).mono (𝓖.le n) le_rfl
  have key : ∀ m (A : ℕ → Set X), (∀ i, MeasurableSet (A i)) → ∀ n G, MeasurableSet[𝓖 n] G →
      pr (G ∩ {ω | ∀ i ≤ m, Ψ (n + i) ω ∈ A i}) = ∫⁻ ω in G, cylFn Q m A (Ψ n ω) ∂pr := by
    intro m
    induction m with
    | zero =>
      intro A hA n G hG
      have hset : {ω | ∀ i ≤ 0, Ψ (n + i) ω ∈ A i} = Ψ n ⁻¹' A 0 := by ext ω; simp
      have hm : MeasurableSet (Ψ n ⁻¹' A 0) := hΨm n (hA 0)
      have hind : (fun ω => cylFn Q 0 A (Ψ n ω)) = (Ψ n ⁻¹' A 0).indicator 1 := by
        ext ω; by_cases h : Ψ n ω ∈ A 0 <;> simp [cylFn, h]
      rw [hset, hind, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_comm]
    | succ m ih =>
      intro A hA n G hG
      set A' : ℕ → Set X := fun i => A (i + 1)
      have hA' : ∀ i, MeasurableSet (A' i) := fun i => hA (i + 1)
      have hG' : MeasurableSet[𝓖 n] (G ∩ Ψ n ⁻¹' A 0) := hG.inter (hΨ n (hA 0))
      have hset : G ∩ {ω | ∀ i ≤ m + 1, Ψ (n + i) ω ∈ A i} =
          (G ∩ Ψ n ⁻¹' A 0) ∩ {ω | ∀ i ≤ m, Ψ (n + 1 + i) ω ∈ A' i} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, A']
        constructor
        · rintro ⟨hg, h⟩
          refine ⟨⟨hg, by simpa using h 0 (Nat.zero_le _)⟩, fun i hi => ?_⟩
          have := h (i + 1) (by omega)
          rwa [show n + (i + 1) = n + 1 + i by omega] at this
        · rintro ⟨⟨hg, h0⟩, h⟩
          refine ⟨hg, fun i hi => ?_⟩
          rcases i with _ | i
          · simpa using h0
          · have := h i (by omega)
            rwa [show n + 1 + i = n + (i + 1) by omega] at this
      have hmeas := measurable_cylFn Q m hA'
      rw [hset, ih A' hA' (n + 1) _ (𝓖.mono (Nat.le_succ n) _ hG'),
        hstep n _ hG' _ hmeas]
      have hmn : MeasurableSet (Ψ n ⁻¹' A 0) := hΨm n (hA 0)
      have hind : (fun ω => cylFn Q (m + 1) A (Ψ n ω)) =
          (Ψ n ⁻¹' A 0).indicator (fun ω => ∫⁻ y, cylFn Q m A' y ∂Q (Ψ n ω)) := by
        ext ω; by_cases h : Ψ n ω ∈ A 0 <;> simp [cylFn, h, A']
      rw [hind, setLIntegral_indicator hmn, inter_comm]
  refine ⟨hΨm, fun n A hA => ?_⟩
  have := key n A hA 0 univ MeasurableSet.univ
  simp only [univ_inter, zero_add, Measure.restrict_univ] at this
  rw [this, ← lintegral_map (measurable_cylFn Q n hA) (hΨm 0), h0]

/-- The filtration `(𝓕_{mn}^Φ)ₙ` along the `m`-skeleton. -/
def skeletonFilt (m : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) where
  seq n := natFilt (X := X) (m * n)
  mono' _ _ hij := (natFilt (X := X)).mono (Nat.mul_le_mul_left m hij)
  le' n := (natFilt (X := X)).le (m * n)

/-- (3.25), MT p. 61: the `m`-skeleton `(Φ_{mn})ₙ` of the chain is a Markov chain with
transition kernel `Pᵐ`, under every `P_μ`. In particular `P_x(Φ_{mn} ∈ A) = Pᵐⁿ(x, A)`
(`pathKernel_coord_mem`). -/
theorem skeleton_isMarkovChain (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) :
    IsMarkovChain (skeleton P m) μ (pathMeasure P μ) (fun n ω => ω (m * n)) := by
  refine isMarkovChain_of_step (𝓖 := skeletonFilt m) _ μ
    (fun n => measurable_coord_natFilt (m * n)) (by simpa using pathMeasure_map_zero P μ)
    fun n G hG f hf => ?_
  have hH : Measurable fun ω : ℕ → X => f (ω m) := hf.comp (measurable_pi_apply m)
  have h := markov_lintegral P μ (n := m * n) hG hH
  simp only [shift_apply] at h
  rw [show m * (n + 1) = m * n + m by ring, h]
  refine setLIntegral_congr_fun ((skeletonFilt m).le n _ hG) fun ω _ => ?_
  rw [← lintegral_map hf (measurable_pi_apply m), pathKernel_map_coord]

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The ergodic theorem (Miao §4.1)

Copied from `EconomicDynamics/ErgodicTheory` (module `ErgodicTheorem`), namespace renamed.

Miao, §4.1, pp. 115–120. A dynamical system is a probability space `(Ω, F, Pr)` with a map
`θ : Ω → Ω`.

* **Definitions 4.1.1–4.1.4**: `IsMeasurableTransformation θ`, `IsMeasurePreserving μ θ`,
  `IsTransformationInvariant θ A` (`θ⁻¹A = A`), `IsErgodic μ θ` (every transformation-invariant
  set has measure `0` or `1`). They agree with Mathlib's `Measurable`, `MeasurePreserving`,
  `MeasurableSpace.invariants` and (for measure-preserving `θ`) `Ergodic`
  (`isMeasurableTransformation_iff`, `isMeasurePreserving_iff`, `isErgodic_iff_ergodic`).
* **Exercise 1** (`ex_4_1`, `ex_4_1_empty`, `ex_4_1_compl`, `ex_4_1_iUnion`): the invariant sets
  form a σ-algebra `I`, which is Mathlib's `MeasurableSpace.invariants θ`.
* **Example 4.1.1**: the shift on `ℝ^∞` is measurable (`example_4_1_1_measurable`), its iterates
  are `θᵏX = (X_k, X_{k+1}, …)` (`iterate_shift_one`), and it is not measure preserving in
  general (`example_4_1_1_not_measurePreserving`).
* **Example 4.1.2**: the cyclic permutation of `n + 1` points preserves the uniform measure
  (`example_4_1_2`), which exists (`exists_uniform_fin`); it is moreover ergodic
  (`example_4_1_2_ergodic`).
* **Exercise 2** (`ex_4_2`): `E f = E f ∘ θ` for measure-preserving `θ`.
* **Lemma 4.1.1** (maximal ergodic theorem, `lemma_4_1_1`): `E[f 1_{M_N > 0}] ≥ 0`, with the two
  steps of Garsia's proof (`lemma_4_1_1_step`, `lemma_4_1_1_on_pos`).
* **Theorem 4.1.1** (Birkhoff): `theorem_4_1_1` (a.s. convergence of the time averages to
  `E[f | I]`), `theorem_4_1_1_L1` (convergence in `L¹`), `theorem_4_1_1_ergodic` and
  `theorem_4_1_1_ergodic_L1` (the limit is `E f` when the system is ergodic), with the step
  `theorem_4_1_1_condExp_const` (`E[f | I] = E f` a.s. under ergodicity) and the recursion
  `theorem_4_1_1_sum_succ` used in the book's proof.

The proof of Birkhoff's theorem is the copied `ErgodicTheory.BirkhoffErgodic`
(`ae_tendsto_birkhoffLimit`, `setIntegral_birkhoffLimit`); this module identifies the limit with
the conditional expectation on `I` (`birkhoffLimit_ae_eq_condExp`) and adds `L¹` convergence by
truncation. The book's own proof (via `lim sup Sₙ/n`) is replaced by that argument.

**Departures.** The book states the theorem for a.s. convergence only; the `L¹` statement is
added. Example 4.1.2 is stated for `n + 1 ≥ 1` points (the book has `n ≥ 2`). Exercise 2 needs no
integrability (`ex_4_2`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Definitions 4.1.1–4.1.4 -/

/-- **Definition 4.1.1** (Miao, p. 116). `θ : Ω → Ω` is a measurable transformation if
`θ⁻¹A ∈ F` for every `A ∈ F`. -/
def IsMeasurableTransformation (θ : Ω → Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → MeasurableSet (θ ⁻¹' A)

/-- Definition 4.1.1 is Mathlib's `Measurable`. -/
theorem isMeasurableTransformation_iff (θ : Ω → Ω) :
    IsMeasurableTransformation θ ↔ Measurable θ :=
  ⟨fun h _ hA => h _ hA, fun h _ hA => h hA⟩

/-- **Definition 4.1.2** (Miao, p. 116). A measurable transformation `θ` is measure preserving if
`Pr(θ⁻¹A) = Pr(A)` for every `A ∈ F`. -/
def IsMeasurePreserving (μ : Measure Ω) (θ : Ω → Ω) : Prop :=
  IsMeasurableTransformation θ ∧ ∀ A : Set Ω, MeasurableSet A → μ (θ ⁻¹' A) = μ A

/-- Definition 4.1.2 is Mathlib's `MeasurePreserving θ μ μ`. -/
theorem isMeasurePreserving_iff (μ : Measure Ω) (θ : Ω → Ω) :
    IsMeasurePreserving μ θ ↔ MeasurePreserving θ μ μ := by
  constructor
  · rintro ⟨hm, h⟩
    have hθ : Measurable θ := (isMeasurableTransformation_iff θ).1 hm
    refine ⟨hθ, ?_⟩
    ext A hA
    rw [Measure.map_apply hθ hA, h A hA]
  · intro h
    refine ⟨(isMeasurableTransformation_iff θ).2 h.measurable, fun A hA => ?_⟩
    rw [← Measure.map_apply h.measurable hA, h.map_eq]

/-- **Definition 4.1.3** (Miao, p. 116). `A ∈ F` is transformation invariant if `θ⁻¹A = A`. -/
def IsTransformationInvariant (θ : Ω → Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ θ ⁻¹' A = A

/-- **Exercise 1** (Miao, p. 129). The transformation-invariant sets are exactly the measurable
sets of the σ-algebra `I = MeasurableSpace.invariants θ`; in particular they form a σ-algebra. -/
theorem ex_4_1 (θ : Ω → Ω) (A : Set Ω) :
    MeasurableSet[MeasurableSpace.invariants θ] A ↔ IsTransformationInvariant θ A :=
  MeasurableSpace.measurableSet_invariants

/-- **Exercise 1** (Miao, p. 129): `∅` is transformation invariant. -/
theorem ex_4_1_empty (θ : Ω → Ω) : IsTransformationInvariant θ ∅ :=
  ⟨MeasurableSet.empty, Set.preimage_empty⟩

/-- **Exercise 1** (Miao, p. 129): the complement of an invariant set is invariant. -/
theorem ex_4_1_compl {θ : Ω → Ω} {A : Set Ω} (h : IsTransformationInvariant θ A) :
    IsTransformationInvariant θ Aᶜ :=
  ⟨h.1.compl, by rw [Set.preimage_compl, h.2]⟩

/-- **Exercise 1** (Miao, p. 129): a countable union of invariant sets is invariant. -/
theorem ex_4_1_iUnion {θ : Ω → Ω} {A : ℕ → Set Ω} (h : ∀ n, IsTransformationInvariant θ (A n)) :
    IsTransformationInvariant θ (⋃ n, A n) :=
  ⟨MeasurableSet.iUnion fun n => (h n).1, by rw [Set.preimage_iUnion]; simp only [(h _).2]⟩

/-- **Definition 4.1.4** (Miao, p. 116). The dynamical system `(Ω, F, Pr, θ)` is ergodic if every
transformation-invariant set has measure zero or one. -/
def IsErgodic (μ : Measure Ω) (θ : Ω → Ω) : Prop :=
  ∀ A : Set Ω, IsTransformationInvariant θ A → μ A = 0 ∨ μ A = 1

/-- For a measure-preserving `θ` of a probability space, Definition 4.1.4 is Mathlib's
`Ergodic`. -/
theorem isErgodic_iff_ergodic {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) : IsErgodic μ θ ↔ Ergodic θ μ := by
  constructor
  · intro h
    refine ⟨hθ, ⟨fun s hs hθs => ?_⟩⟩
    rw [eventuallyEmptyOrUniv_iff]
    rcases h s ⟨hs, hθs⟩ with h0 | h1
    · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h0)
    · refine Or.inl ?_
      rw [ae_iff]
      have : μ sᶜ = 0 := by rw [measure_compl hs (measure_ne_top μ s), h1, measure_univ]; simp
      exact this
  · intro h A hA
    exact h.toPreErgodic.prob_eq_zero_or_one hA.1 hA.2

/-! ### Example 4.1.1: the shift -/

omit [MeasurableSpace Ω] in
/-- Example 4.1.1 (Miao, p. 116): `θᵏX = (X_k, X_{k+1}, …)`, i.e. the `k`-th iterate of the
one-step shift is `shift k`. -/
theorem iterate_shift_one {E : Type*} (k : ℕ) (x : ℕ → E) : (shift 1)^[k] x = shift k x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    ext i
    simp only [shift_apply]
    congr 1
    omega

/-- **Example 4.1.1** (Miao, p. 116): the shift `θX = (X₁, X₂, …)` on `ℝ^∞` is a measurable
transformation. -/
theorem example_4_1_1_measurable : IsMeasurableTransformation (shift 1 : (ℕ → ℝ) → ℕ → ℝ) :=
  (isMeasurableTransformation_iff _).2 (measurable_shift 1)

/-- **Example 4.1.1** (Miao, p. 116): the shift is not measure preserving in general: for the
point mass at `(1, 0, 0, …)`, `Pr(X₀ = 1) = 1` but `Pr(θ⁻¹{X₀ = 1}) = Pr(X₁ = 1) = 0`. -/
theorem example_4_1_1_not_measurePreserving :
    ∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧
      ¬ IsMeasurePreserving μ (shift 1 : (ℕ → ℝ) → ℕ → ℝ) := by
  set x : ℕ → ℝ := fun n => if n = 0 then 1 else 0 with hx
  refine ⟨Measure.dirac x, inferInstance, fun h => ?_⟩
  have hA : MeasurableSet {y : ℕ → ℝ | y 0 = 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have h1 := h.2 _ hA
  rw [Measure.dirac_apply' _ hA, Measure.dirac_apply' _ ((measurable_shift 1) hA)] at h1
  have hx0 : x ∈ {y : ℕ → ℝ | y 0 = 1} := by simp [hx]
  have hx1 : x ∉ shift 1 ⁻¹' {y : ℕ → ℝ | y 0 = 1} := by simp [hx, shift]
  rw [Set.indicator_of_mem hx0, Set.indicator_of_notMem hx1] at h1
  simp at h1

/-! ### Example 4.1.2: a cyclic permutation -/

open Fin.NatCast in
/-- Iterating the rotation of `Fin (n + 1)` adds: `θᵐ(i) = i + m`. -/
theorem iterate_finRotate (n m : ℕ) (i : Fin (n + 1)) :
    (finRotate (n + 1))^[m] i = i + (m : Fin (n + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, finRotate_apply, Nat.cast_succ, add_assoc]

/-- **Example 4.1.2** (Miao, p. 116): on `Ω = {ω₀, …, ωₙ}` (the book's `n` points, here `n + 1`)
the cyclic permutation `θωₖ = ωₖ₊₁`, `θωₙ = ω₀` preserves the measure with `Pr(ωₖ) = 1/(n+1)`. -/
theorem example_4_1_2 (n : ℕ) (μ : Measure (Fin (n + 1)))
    (hμ : ∀ k, μ {k} = ((n : ℝ≥0∞) + 1)⁻¹) :
    IsMeasurePreserving μ (finRotate (n + 1)) := by
  rw [isMeasurePreserving_iff]
  refine ⟨measurable_of_finite _, ?_⟩
  refine Measure.ext_iff_singleton.2 fun j => ?_
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton j)]
  have : (finRotate (n + 1)) ⁻¹' {j} = {(finRotate (n + 1)).symm j} := by
    ext i
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (Equiv.eq_symm_apply _).symm
  rw [this, hμ, hμ]

/-- The uniform probability of Example 4.1.2 exists: `(n + 1)⁻¹ ·` counting measure. -/
theorem exists_uniform_fin (n : ℕ) :
    ∃ μ : Measure (Fin (n + 1)), IsProbabilityMeasure μ ∧ ∀ k, μ {k} = ((n : ℝ≥0∞) + 1)⁻¹ := by
  refine ⟨((n : ℝ≥0∞) + 1)⁻¹ • Measure.count, ⟨?_⟩, fun k => ?_⟩
  · rw [Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      smul_eq_mul]
    have : (((n + 1 : ℕ) : ℕ∞) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 := by simp
    rw [this, ENNReal.inv_mul_cancel (by simp) (by simp)]
  · rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

open Fin.NatCast in
/-- Example 4.1.2, continued: the cyclic permutation is ergodic for the uniform measure, since
its only invariant sets are `∅` and `Ω`. -/
theorem example_4_1_2_ergodic (n : ℕ) (μ : Measure (Fin (n + 1))) [IsProbabilityMeasure μ] :
    IsErgodic μ (finRotate (n + 1)) := by
  intro A hA
  by_cases hne : A.Nonempty
  · obtain ⟨i, hi⟩ := hne
    have key : ∀ x, finRotate (n + 1) x ∈ A ↔ x ∈ A := fun x => by
      rw [← Set.mem_preimage, hA.2]
    have hall : ∀ j, j ∈ A := by
      intro j
      have hit : ∀ m : ℕ, (finRotate (n + 1))^[m] i ∈ A := by
        intro m
        induction m with
        | zero => exact hi
        | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact (key _).2 ih
      have := hit (j - i).val
      rwa [iterate_finRotate, Fin.cast_val_eq_self, add_sub_cancel] at this
    have : A = Set.univ := Set.eq_univ_of_forall hall
    right
    rw [this, measure_univ]
  · left
    rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]

/-! ### Exercise 2 and Lemma 4.1.1 -/

/-- **Exercise 2** (Miao, p. 129): if `θ` is measure preserving, `E f(ω) = E f(θω)`. (No
integrability is needed: both sides are `0` when `f` is not integrable.) -/
theorem ex_4_2 {μ : Measure Ω} {θ : Ω → Ω} (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) : ∫ ω, f ω ∂μ = ∫ ω, f (θ ω) ∂μ := by
  have hf' : AEStronglyMeasurable f (μ.map θ) := by rw [hθ.map_eq]; exact hf
  rw [← integral_map hθ.measurable.aemeasurable hf', hθ.map_eq]

omit [MeasurableSpace Ω] in
/-- Miao, proof of Lemma 4.1.1, p. 117: for `k ≤ N`, `f(ω) + M_N(θω) ≥ f(ω) + S_k(θω) =
S_{k+1}(ω)`. -/
theorem lemma_4_1_1_step (θ : Ω → Ω) (f : Ω → ℝ) {k N : ℕ} (hk : k ≤ N) (ω : Ω) :
    birkhoffSum θ f (k + 1) ω ≤ f ω + birkhoffMax θ f N (θ ω) := by
  rw [birkhoffSum_succ_apply']
  linarith [birkhoffSum_le_birkhoffMax θ f hk (θ ω)]

omit [MeasurableSpace Ω] in
/-- Miao, proof of Lemma 4.1.1, p. 118: on `{M_N > 0}`, `f(ω) ≥ M_N(ω) − M_N(θω)`. -/
theorem lemma_4_1_1_on_pos (θ : Ω → Ω) (f : Ω → ℝ) (N : ℕ) {ω : Ω}
    (h : 0 < birkhoffMax θ f N ω) : birkhoffMax θ f N ω - birkhoffMax θ f N (θ ω) ≤ f ω := by
  linarith [birkhoffMax_le_add θ f N h]

/-- **Lemma 4.1.1** (Maximal Ergodic Theorem, Miao, p. 117). With `S_N = Σ_{n<N} f ∘ θⁿ` and
`M_N = max{S₀, S₁, …, S_N}` (`birkhoffMax`, `S₀ = 0`), `E[f 1_{M_N > 0}] ≥ 0` for every `N`. -/
theorem lemma_4_1_1 {μ : Measure Ω} {θ : Ω → Ω} (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ}
    (hfm : Measurable f) (hf : Integrable f μ) (N : ℕ) :
    0 ≤ ∫ ω, {ω | 0 < birkhoffMax θ f N ω}.indicator f ω ∂μ := by
  rw [integral_indicator (measurableSet_lt measurable_const
    (measurable_birkhoffMax hθ.measurable hfm N))]
  exact maximal_ergodic hθ hfm hf N

/-! ### Theorem 4.1.1 -/

omit [MeasurableSpace Ω] in
/-- Miao, proof of Theorem 4.1.1, p. 118: `S_{N+1}(ω) = f(ω) + S_N(θω)`, so that
`S_{N+1}/(N+1) = f/(N+1) + (N/(N+1)) S_N(θω)/N`. -/
theorem theorem_4_1_1_sum_succ (θ : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (ω : Ω) :
    birkhoffSum θ f (N + 1) ω / (N + 1) =
      f ω / (N + 1) + (N / (N + 1)) * (birkhoffSum θ f N (θ ω) / N) := by
  rw [birkhoffSum_succ_apply']
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [birkhoffSum_zero_apply]
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

omit [MeasurableSpace Ω] in
/-- The Birkhoff average is the book's `(1/N) Σ_{n<N} f(θⁿω)`. -/
theorem birkhoffAverage_eq_sum (θ : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (ω : Ω) :
    birkhoffAverage ℝ θ f N ω = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (θ^[n] ω) := by
  rw [birkhoffAverage, smul_eq_mul, birkhoffSum]

/-- The set where the Birkhoff averages converge is measurable. -/
theorem measurableSet_convergent {θ : Ω → Ω} (hθ : Measurable θ) {f : Ω → ℝ} (hf : Measurable f) :
    MeasurableSet {ω | ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)} :=
  MeasureTheory.measurableSet_exists_tendsto fun n => measurable_birkhoffAverage hθ hf n

/-- The strictly invariant version of the Birkhoff limit: `L` on the convergence set, `0` off
it. -/
noncomputable def invariantLimit (θ : Ω → Ω) (f : Ω → ℝ) : Ω → ℝ :=
  {ω | ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)}.indicator
    (birkhoffLimit θ f)

omit [MeasurableSpace Ω] in
/-- `invariantLimit` is strictly invariant: `L̃ ∘ θ = L̃`. -/
theorem invariantLimit_comp (θ : Ω → Ω) (f : Ω → ℝ) :
    invariantLimit θ f ∘ θ = invariantLimit θ f := by
  ext ω
  simp only [Function.comp_apply, invariantLimit]
  by_cases h : ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := h
    have h' : ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n (θ ω)) atTop (𝓝 c) :=
      ⟨c, tendsto_birkhoffAverage_apply hc⟩
    rw [Set.indicator_of_mem (show θ ω ∈ {ω | ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n ω)
      atTop (𝓝 c)} from h'), Set.indicator_of_mem (show ω ∈ {ω | ∃ c, Tendsto
      (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)} from ⟨c, hc⟩),
      birkhoffLimit_apply_of_tendsto hc]
  · have h' : ¬ ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n (θ ω)) atTop (𝓝 c) :=
      fun ⟨c, hc⟩ => h ⟨c, tendsto_birkhoffAverage_of_apply hc⟩
    rw [Set.indicator_of_notMem (show θ ω ∉ {ω | ∃ c, Tendsto
      (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)} from h'), Set.indicator_of_notMem
      (show ω ∉ {ω | ∃ c, Tendsto (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)} from h)]

/-- `invariantLimit` is measurable for the invariant σ-algebra `I`. -/
theorem measurable_invariantLimit {θ : Ω → Ω} (hθ : Measurable θ) {f : Ω → ℝ}
    (hf : Measurable f) : Measurable[MeasurableSpace.invariants θ] (invariantLimit θ f) := by
  rw [MeasurableSpace.measurable_invariants_dom]
  refine ⟨(measurable_birkhoffLimit hθ hf).indicator (measurableSet_convergent hθ hf),
    fun s _ => ?_⟩
  rw [invariantLimit_comp]

/-- `invariantLimit = birkhoffLimit` almost everywhere. -/
theorem invariantLimit_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    invariantLimit θ f =ᵐ[μ] birkhoffLimit θ f := by
  filter_upwards [ae_exists_tendsto_birkhoffAverage hθ hfm hf] with ω hω
  simp only [invariantLimit, Set.indicator_of_mem (show ω ∈ {ω | ∃ c, Tendsto
    (fun n => birkhoffAverage ℝ θ f n ω) atTop (𝓝 c)} from hω)]

/-- **Identification of the limit** (Miao, Theorem 4.1.1, p. 117): the Birkhoff limit is
`E[f | I]` almost surely. -/
theorem birkhoffLimit_ae_eq_condExp {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    birkhoffLimit θ f =ᵐ[μ] μ[f | MeasurableSpace.invariants θ] := by
  have hle := MeasurableSpace.invariants_le θ
  have hL := integrable_birkhoffLimit hθ hfm hf
  have hae := invariantLimit_ae_eq hθ hfm hf
  refine hae.symm.trans ?_
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hf
    (fun s _ _ => (hL.1.congr hae.symm).integrableOn) (fun s hs _ => ?_)
    (measurable_invariantLimit hθ.measurable hfm).stronglyMeasurable.aestronglyMeasurable
  rw [setIntegral_congr_ae (hle s hs) (hae.mono fun ω h _ => h)]
  exact setIntegral_birkhoffLimit hθ hfm hf (hle s hs) hs.2

/-- **Theorem 4.1.1** (Birkhoff, Miao, p. 117). For a measure-preserving `θ` and integrable `f`,
`(1/N) Σ_{n<N} f(θⁿω) → E[f | I](ω)` for `Pr`-almost every `ω`, where `I` is the σ-algebra of
transformation-invariant sets. -/
theorem theorem_4_1_1 {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (θ^[n] ω)) atTop
      (𝓝 (μ[f | MeasurableSpace.invariants θ] ω)) := by
  filter_upwards [ae_tendsto_birkhoffLimit hθ hfm hf,
    birkhoffLimit_ae_eq_condExp hθ hfm hf] with ω h1 h2
  rw [← h2]
  simpa only [birkhoffAverage_eq_sum] using h1

omit [MeasurableSpace Ω] in
/-- `|(1/N) Sₙ f| ≤ (1/N) Sₙ |f|`. -/
theorem abs_birkhoffAverage_le (θ : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (ω : Ω) :
    |birkhoffAverage ℝ θ f N ω| ≤ birkhoffAverage ℝ θ (fun x => |f x|) N ω := by
  simp only [birkhoffAverage, smul_eq_mul, birkhoffSum]
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- The Birkhoff averages of an integrable function are integrable. -/
theorem integrable_birkhoffAverage {μ : Measure Ω} {θ : Ω → Ω} (hθ : MeasurePreserving θ μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (N : ℕ) : Integrable (birkhoffAverage ℝ θ f N) μ := by
  have : birkhoffAverage ℝ θ f N = fun ω => (N : ℝ)⁻¹ * birkhoffSum θ f N ω := by
    ext ω; rw [birkhoffAverage, smul_eq_mul]
  rw [this]
  exact (integrable_birkhoffSum hθ hf N).const_mul _

/-- `∫ |(1/N) Sₙ f| ≤ ∫ |f|` for `N ≥ 1`. -/
theorem integral_abs_birkhoffAverage_le {μ : Measure Ω} {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ)
    {N : ℕ} (hN : N ≠ 0) :
    ∫ ω, |birkhoffAverage ℝ θ f N ω| ∂μ ≤ ∫ ω, |f ω| ∂μ := by
  have h := setIntegral_birkhoffAverage hθ (measurable_abs_of_measurable hfm) hf.abs
    MeasurableSet.univ Set.preimage_univ hN
  simp only [Measure.restrict_univ] at h
  rw [← h]
  exact integral_mono (integrable_birkhoffAverage hθ hf N).abs
    (integrable_birkhoffAverage hθ hf.abs N) (abs_birkhoffAverage_le θ f N)

/-- `L¹` convergence for bounded `f` (dominated convergence). -/
theorem tendsto_integral_abs_sub_of_bdd {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) :
    Tendsto (fun N => ∫ ω, |birkhoffAverage ℝ θ f N ω - birkhoffLimit θ f ω| ∂μ) atTop
      (𝓝 0) := by
  have hf : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have hbd : ∀ N ω, |birkhoffAverage ℝ θ f N ω| ≤ C := by
    intro N ω
    refine (abs_birkhoffAverage_le θ f N ω).trans ?_
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [birkhoffAverage_zero, Pi.zero_apply]
      exact (abs_nonneg _).trans (hC ω)
    simp only [birkhoffAverage, smul_eq_mul, birkhoffSum]
    rw [inv_mul_le_iff₀ (by exact_mod_cast hN)]
    calc ∑ k ∈ Finset.range N, |f (θ^[k] ω)| ≤ ∑ _k ∈ Finset.range N, C :=
          Finset.sum_le_sum fun k _ => hC _
      _ = N * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hconv := ae_tendsto_birkhoffLimit hθ hfm hf
  have hLb : ∀ᵐ ω ∂μ, |birkhoffLimit θ f ω| ≤ C := by
    filter_upwards [hconv] with ω hω
    exact le_of_tendsto' ((continuous_abs.tendsto _).comp hω) fun N => hbd N ω
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => 2 * C)
    (F := fun N ω => |birkhoffAverage ℝ θ f N ω - birkhoffLimit θ f ω|) (f := fun _ => 0)
    (fun N => (continuous_abs.measurable.comp ((measurable_birkhoffAverage hθ.measurable hfm N).sub
      (measurable_birkhoffLimit hθ.measurable hfm))).aestronglyMeasurable)
    (integrable_const _)
    (fun N => by
      filter_upwards [hLb] with ω hω
      rw [Real.norm_eq_abs, abs_abs]
      calc |birkhoffAverage ℝ θ f N ω - birkhoffLimit θ f ω|
          ≤ |birkhoffAverage ℝ θ f N ω| + |birkhoffLimit θ f ω| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hbd N ω])
    (by
      filter_upwards [hconv] with ω hω
      have := ((hω.sub_const (birkhoffLimit θ f ω)).abs)
      simpa only [sub_self, abs_zero] using this)
  simpa only [integral_zero] using h

/-- `∫ |f − truncAt M f| → 0` as `M → ∞`. -/
theorem tendsto_integral_abs_sub_truncAt {μ : Measure Ω} {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) :
    Tendsto (fun M : ℕ => ∫ ω, |f ω - truncAt (M : ℝ) f ω| ∂μ) atTop (𝓝 0) := by
  have htm : ∀ M : ℕ, Measurable (truncAt (M : ℝ) f) := fun M =>
    measurable_const.max (hfm.min measurable_const)
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ))
    (fun ω => |f ω|)
    (fun M => (measurable_abs_of_measurable (hfm.sub (htm M))).aestronglyMeasurable) hf.abs
    (fun M => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_sub_truncAt_le (M : ℝ) (Nat.cast_nonneg M) f ω)
    (Eventually.of_forall fun ω => by
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ?_)
      obtain ⟨N, hN⟩ := exists_nat_ge (|f ω|)
      refine ⟨N, fun M hM => ?_⟩
      have hMf : |f ω| ≤ M := hN.trans (by exact_mod_cast hM)
      have : truncAt (M : ℝ) f ω = f ω := by
        unfold truncAt
        rw [abs_le] at hMf
        rw [min_eq_left hMf.2, max_eq_right hMf.1]
      simp [this])
  simpa using h

/-- `L¹` convergence of the Birkhoff averages to the Birkhoff limit. -/
theorem tendsto_integral_abs_sub_birkhoffLimit {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → Ω} (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) :
    Tendsto (fun N => ∫ ω, |birkhoffAverage ℝ θ f N ω - birkhoffLimit θ f ω| ∂μ) atTop
      (𝓝 0) := by
  have htm : ∀ M : ℕ, Measurable (truncAt (M : ℝ) f) := fun M =>
    measurable_const.max (hfm.min measurable_const)
  have hbd : ∀ M : ℕ, ∀ ω, |truncAt (M : ℝ) f ω| ≤ M := by
    intro M ω
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
      (min_le_right _ _)⟩
  have hti : ∀ M : ℕ, Integrable (truncAt (M : ℝ) f) μ := fun M =>
    Integrable.of_bound (htm M).aestronglyMeasurable (M : ℝ)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd M ω)
  set g : ℕ → Ω → ℝ := fun M ω => f ω - truncAt (M : ℝ) f ω with hg
  have hgm : ∀ M, Measurable (g M) := fun M => hfm.sub (htm M)
  have hgi : ∀ M, Integrable (g M) μ := fun M => hf.sub (hti M)
  have hfsplit : ∀ M : ℕ, f = truncAt (M : ℝ) f + g M := by
    intro M; ext ω; simp [hg]
  -- the a.e. splitting of the limit
  have hLsplit : ∀ M : ℕ, birkhoffLimit θ f =ᵐ[μ]
      fun ω => birkhoffLimit θ (truncAt (M : ℝ) f) ω + birkhoffLimit θ (g M) ω := by
    intro M
    filter_upwards [ae_tendsto_birkhoffLimit hθ hfm hf,
      ae_tendsto_birkhoffLimit hθ (htm M) (hti M),
      ae_tendsto_birkhoffLimit hθ (hgm M) (hgi M)] with ω h1 h2 h3
    refine tendsto_nhds_unique h1 ((h2.add h3).congr fun n => ?_)
    rw [← birkhoffAverage_add_apply, ← hfsplit M]
  -- the pointwise bound
  have hle : ∀ M N : ℕ, ∫ ω, |birkhoffAverage ℝ θ f N ω - birkhoffLimit θ f ω| ∂μ ≤
      ∫ ω, |birkhoffAverage ℝ θ (truncAt (M : ℝ) f) N ω -
        birkhoffLimit θ (truncAt (M : ℝ) f) ω| ∂μ +
      (∫ ω, |birkhoffAverage ℝ θ (g M) N ω| ∂μ + ∫ ω, |birkhoffLimit θ (g M) ω| ∂μ) := by
    intro M N
    have hA1 := integrable_birkhoffAverage hθ (hti M) N
    have hA2 := integrable_birkhoffAverage hθ (hgi M) N
    have hL1 := (integrable_birkhoffLimit hθ (htm M) (hti M)).1
    have hL2 := (integrable_birkhoffLimit hθ (hgm M) (hgi M)).1
    have i1 : Integrable (fun ω => |birkhoffAverage ℝ θ (truncAt (M : ℝ) f) N ω -
        birkhoffLimit θ (truncAt (M : ℝ) f) ω|) μ := (hA1.sub hL1).abs
    have i2 : Integrable (fun ω => |birkhoffAverage ℝ θ (g M) N ω|) μ := hA2.abs
    have i3 : Integrable (fun ω => |birkhoffLimit θ (g M) ω|) μ := hL2.abs
    have i23 : Integrable (fun ω => |birkhoffAverage ℝ θ (g M) N ω| +
        |birkhoffLimit θ (g M) ω|) μ := i2.add i3
    rw [← integral_add i2 i3, ← integral_add i1 i23]
    refine integral_mono_ae ((integrable_birkhoffAverage hθ hf N).sub
      (integrable_birkhoffLimit hθ hfm hf).1).abs (i1.add i23) ?_
    filter_upwards [hLsplit M] with ω hω
    have hAs : birkhoffAverage ℝ θ f N ω = birkhoffAverage ℝ θ (truncAt (M : ℝ) f) N ω +
        birkhoffAverage ℝ θ (g M) N ω := by
      rw [← birkhoffAverage_add_apply, ← hfsplit M]
    rw [hAs, hω]
    have := abs_add_le (birkhoffAverage ℝ θ (truncAt (M : ℝ) f) N ω -
      birkhoffLimit θ (truncAt (M : ℝ) f) ω)
      (birkhoffAverage ℝ θ (g M) N ω - birkhoffLimit θ (g M) ω)
    have h2 := abs_sub (birkhoffAverage ℝ θ (g M) N ω) (birkhoffLimit θ (g M) ω)
    calc _ = |(birkhoffAverage ℝ θ (truncAt (M : ℝ) f) N ω -
          birkhoffLimit θ (truncAt (M : ℝ) f) ω) +
          (birkhoffAverage ℝ θ (g M) N ω - birkhoffLimit θ (g M) ω)| := by ring_nf
      _ ≤ _ := by linarith
  have hgt := tendsto_integral_abs_sub_truncAt (μ := μ) hfm hf
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 hgt) (ε / 4) (by linarith)
  have hM' : ∫ ω, |g M ω| ∂μ < ε / 4 := by
    have := hM M le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at this
    exact this
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1
    (tendsto_integral_abs_sub_of_bdd hθ (htm M) (hbd M))) (ε / 4) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : N ≠ 0 := by omega
  have h1 := hN₀ N (le_of_max_le_left hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h1
  have h2 := integral_abs_birkhoffAverage_le hθ (hgm M) (hgi M) hN1
  have h3 := (integrable_birkhoffLimit hθ (hgm M) (hgi M)).2
  have h4 := hle M N
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  linarith

/-- **Theorem 4.1.1** (Birkhoff, Miao, p. 117), `L¹` form: `E|(1/N) Σ_{n<N} f ∘ θⁿ − E[f | I]|
→ 0`. -/
theorem theorem_4_1_1_L1 {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun N : ℕ => ∫ ω, |(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (θ^[n] ω) -
      μ[f | MeasurableSpace.invariants θ] ω| ∂μ) atTop (𝓝 0) := by
  refine (tendsto_integral_abs_sub_birkhoffLimit hθ hfm hf).congr fun N => ?_
  refine integral_congr_ae ?_
  filter_upwards [birkhoffLimit_ae_eq_condExp hθ hfm hf] with ω hω
  rw [hω, birkhoffAverage_eq_sum]

/-- Miao, proof of Theorem 4.1.1 (second part), pp. 119–120: if the system is ergodic,
`E[f | I] = E f` almost surely. -/
theorem theorem_4_1_1_condExp_const {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (herg : IsErgodic μ θ) {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) :
    μ[f | MeasurableSpace.invariants θ] =ᵐ[μ] fun _ => ∫ ω, f ω ∂μ := by
  have h1 := ae_tendsto_birkhoffAverage_of_ergodic hθ hfm hf fun E hE hθE => herg E ⟨hE, hθE⟩
  filter_upwards [h1, ae_tendsto_birkhoffLimit hθ hfm hf,
    birkhoffLimit_ae_eq_condExp hθ hfm hf] with ω h1 h2 h3
  rw [← h3]
  exact tendsto_nhds_unique h2 h1

/-- **Theorem 4.1.1** (Birkhoff, ergodic case, Miao, p. 117): if the system is also ergodic,
`(1/N) Σ_{n<N} f(θⁿω) → E f`, `Pr`-a.s. -/
theorem theorem_4_1_1_ergodic {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (herg : IsErgodic μ θ) {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (θ^[n] ω)) atTop
      (𝓝 (∫ ω, f ω ∂μ)) := by
  filter_upwards [theorem_4_1_1 hθ hfm hf, theorem_4_1_1_condExp_const hθ herg hfm hf]
    with ω h1 h2
  rwa [← h2]

/-- **Theorem 4.1.1** (ergodic case) in `L¹`: `E|(1/N) Σ_{n<N} f ∘ θⁿ − E f| → 0`. -/
theorem theorem_4_1_1_ergodic_L1 {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : Ω → Ω}
    (hθ : MeasurePreserving θ μ μ) (herg : IsErgodic μ θ) {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) :
    Tendsto (fun N : ℕ => ∫ ω, |(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (θ^[n] ω) -
      ∫ ω, f ω ∂μ| ∂μ) atTop (𝓝 0) := by
  refine (theorem_4_1_1_L1 hθ hfm hf).congr fun N => ?_
  refine integral_congr_ae ?_
  filter_upwards [theorem_4_1_1_condExp_const hθ herg hfm hf] with ω hω
  rw [hω]

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stationary processes (Miao §4.2)

Copied from `EconomicDynamics/ErgodicTheory` (module `StationaryProcesses`), namespace renamed.

Miao, §4.2, pp. 120–125. A process is a family `X : ℕ → Ω → E` of random variables on
`(Ω, F, Pr)`; the state space `E` is any measurable space (the book takes `E = ℝ`; only the strong
law needs real values). Its path is `pathOf X ω = (X₀(ω), X₁(ω), …)` and its law on `E^ℕ` is
`pathLaw P X`. The shift is `shift 1`, `θx = (x₁, x₂, …)`, with iterates `shift k`.

* **Definition 4.2.1** (`IsStationary`): the law of `(X_t, …, X_{t+n})` (`window X t n`) does not
  depend on `t`. `isStationary_iff_map_shift`, `isStationary_iff_measurePreserving`: `X` is
  stationary iff the shift preserves its law on path space.
* p. 120: `isStationary_of_iid` (an IID sequence is stationary) and `isStationary_comp_window`
  (`Y_t = g(X_t, …, X_{t+n})` is stationary when `X` is).
* p. 121: `isStationary_of_measurePreserving` (`X_k = g ∘ θᵏ` is stationary for a
  measure-preserving `θ`) and the converse representation `stationary_representation` (on
  `(E^ℕ, B(E^ℕ), P̃r)` the shift is measure preserving and the coordinate process has the law of
  `X`).
* **Definitions 4.2.2–4.2.3** (`IsShiftInvariant`, `IsErgodicProcess`), with the correction
  below: `shiftInvariant_compl_counterexample`, `exists_invariant_ae_eq`,
  `isErgodicProcess_iff_isErgodic`.
* **Theorem 4.2.1** (strong law of large numbers): `theorem_4_2_1` ((4.1), the limit
  `E[X₀ | I]` with `I = invariantField X`), `theorem_4_2_1_ergodic` ((4.2)), and `eq_4_3` (the
  path-space statement (4.3)); `condExp_comp_ae_eq` transports conditional expectations from
  path space.
* **Definition 4.2.4** (`IsMixing`) and **Theorem 4.2.3** (`theorem_4_2_3`): a mixing stationary
  process is ergodic.
* The setting of **Theorem 4.2.4** (`theorem_4_2_4_filtration_mono`: `M_k = θ⁻ᵏM₀` increases);
  the central limit theorem itself is not formalised.

**Corrections.**
1. Definition 4.2.2 calls `A` shift invariant when `θA ⊆ A` (`x ∈ A ⇒ θx ∈ A`). These sets are
   not closed under complements (`shiftInvariant_compl_counterexample`: `A = {0}`), so "the class
   of shift invariant sets" is not a σ-algebra and cannot be the `I` of Theorem 4.2.1, and the
   claim on p. 123 that it equals the σ-algebra of transformation-invariant sets is false. What is
   true: every transformation-invariant set is shift invariant
   (`isShiftInvariant_of_preimage_eq`), and every measurable shift-invariant set differs from a
   transformation-invariant one by a null set (`exists_invariant_ae_eq`). So Definition 4.2.3 is
   equivalent to ergodicity of the shift in the sense of Definition 4.1.4
   (`isErgodicProcess_iff_isErgodic`), and `I` in Theorem 4.2.1 is taken to be the σ-algebra of
   events `{(X₀, X₁, …) ∈ A}` with `θ⁻¹A = A`.
2. Definition 4.2.4 is stated with the difference `Pr(…) − Pr(…) Pr(…) → 0` (its right side
   depends on `n`).
3. Theorem 4.2.4 (Heyde's CLT) is not formalised; it needs a martingale CLT.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-! ### Paths, windows and stationarity -/

/-- The path `(X₀(ω), X₁(ω), …)` of a process. -/
def pathOf (X : ℕ → Ω → E) (ω : Ω) : ℕ → E := fun n => X n ω

/-- The window `(X_t, X_{t+1}, …, X_{t+n})`. -/
def window (X : ℕ → Ω → E) (t n : ℕ) (ω : Ω) : Fin (n + 1) → E := fun i => X (t + i) ω

/-- The first `n + 1` coordinates of a path. -/
def pathWindow (n : ℕ) (x : ℕ → E) : Fin (n + 1) → E := fun i => x i

/-- The law `P̃r = Pr ∘ (X₀, X₁, …)⁻¹` of a process on path space (Miao, p. 121). -/
noncomputable def pathLaw (P : Measure Ω) (X : ℕ → Ω → E) : Measure (ℕ → E) := P.map (pathOf X)

/-- **Definition 4.2.1** (Miao, p. 120). `X` is (strictly) stationary if the distribution of
`(X_t, X_{t+1}, …, X_{t+n})` does not depend on `t`, for every `n`. -/
def IsStationary (P : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ t n : ℕ, P.map (window X t n) = P.map (window X 0 n)

theorem measurable_pathOf {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) :
    Measurable (pathOf X) :=
  measurable_pi_iff.2 hX

theorem measurable_window {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (t n : ℕ) :
    Measurable (window X t n) :=
  measurable_pi_iff.2 fun i => hX (t + i)

theorem measurable_pathWindow (n : ℕ) : Measurable (pathWindow (E := E) n) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `(X_t, …, X_{t+n}) = (first n + 1 coordinates) ∘ θᵗ ∘ (X₀, X₁, …)`. -/
theorem window_eq (X : ℕ → Ω → E) (t n : ℕ) :
    window X t n = pathWindow n ∘ shift t ∘ pathOf X := by
  ext ω i
  rfl

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `(X₀, …, Xₙ) = (first n + 1 coordinates) ∘ (X₀, X₁, …)`. -/
theorem window_zero (X : ℕ → Ω → E) (n : ℕ) : window X 0 n = pathWindow n ∘ pathOf X := by
  ext ω i
  simp [window, pathWindow, pathOf]

/-- The law of the path is a probability measure. -/
theorem isProbabilityMeasure_pathLaw (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} : IsProbabilityMeasure (pathLaw P X) := by
  unfold pathLaw; infer_instance

omit [MeasurableSpace E] in
/-- A box `{x₀ ∈ A₀, …, xₙ ∈ Aₙ}` is the preimage of a rectangle under the first `n + 1`
coordinates. -/
theorem boxSet_eq_preimage (n : ℕ) (A : ℕ → Set E) :
    boxSet n A = pathWindow n ⁻¹' Set.univ.pi (fun i : Fin (n + 1) => A i) := by
  ext x
  simp only [boxSet, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_const, pathWindow]
  constructor
  · intro h i
    exact h i (Nat.lt_succ_iff.1 i.isLt)
  · intro h i hi
    exact h ⟨i, Nat.lt_succ_of_le hi⟩

/-- Two finite measures on path space that agree on all boxes are equal. -/
theorem ext_of_boxSet {μ ν : Measure (ℕ → E)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n (A : ℕ → Set E), (∀ i, MeasurableSet (A i)) → μ (boxSet n A) = ν (boxSet n A)) :
    μ = ν := by
  refine ext_of_generate_finite _ generateFrom_boxSets isPiSystem_boxSets ?_ ?_
  · rintro _ ⟨n, A, hA, rfl⟩
    exact h n A hA
  · have hu : (Set.univ : Set (ℕ → E)) = boxSet 0 (fun _ => Set.univ) := by
      ext; simp [boxSet]
    rw [hu, h 0 _ fun _ => MeasurableSet.univ]

/-- Stationarity is shift invariance of the law of the path:
`X` is stationary iff `P̃r ∘ (θᵗ)⁻¹ = P̃r` for every `t`. -/
theorem isStationary_iff_map_shift {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) :
    IsStationary P X ↔ ∀ t, (pathLaw P X).map (shift t) = pathLaw P X := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  constructor
  · intro h t
    have : IsProbabilityMeasure ((pathLaw P X).map (shift t)) :=
      inferInstance
    refine ext_of_boxSet fun n A hA => ?_
    have hR : MeasurableSet (Set.univ.pi fun i : Fin (n + 1) => A i) :=
      MeasurableSet.univ_pi fun i => hA i
    have hB := measurableSet_boxSet n hA
    rw [Measure.map_apply (measurable_shift t) hB, pathLaw, Measure.map_apply hΦ hB,
      Measure.map_apply hΦ ((measurable_shift t) hB), boxSet_eq_preimage]
    have h1 := congrArg (fun m : Measure (Fin (n + 1) → E) =>
      m (Set.univ.pi fun i : Fin (n + 1) => A i)) (h t n)
    rw [Measure.map_apply (measurable_window hX t n) hR,
      Measure.map_apply (measurable_window hX 0 n) hR, window_zero] at h1
    exact h1
  · intro h t n
    rw [window_eq, window_zero, ← Measure.map_map (measurable_pathWindow n)
      ((measurable_shift t).comp hΦ), ← Measure.map_map (measurable_shift t) hΦ,
      ← Measure.map_map (measurable_pathWindow n) hΦ]
    change ((pathLaw P X).map (shift t)).map _ = (pathLaw P X).map _
    rw [h t]

/-- `X` is stationary iff the one-step shift `θ` preserves the law `P̃r` of its path. -/
theorem isStationary_iff_measurePreserving {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) :
    IsStationary P X ↔ MeasurePreserving (shift 1) (pathLaw P X) (pathLaw P X) := by
  rw [isStationary_iff_map_shift hX]
  constructor
  · intro h
    exact ⟨measurable_shift 1, h 1⟩
  · intro h t
    have := (h.iterate t).map_eq
    have heq : (shift 1)^[t] = shift (X := E) t := funext (iterate_shift_one t)
    rwa [heq] at this

/-- Miao, p. 121: if `θ` is measure preserving and `g` is measurable, then `X_k = g(θᵏω)` is a
stationary process. -/
theorem isStationary_of_measurePreserving {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Ω} (hθ : MeasurePreserving θ P P) {g : Ω → E} (hg : Measurable g) :
    IsStationary P (fun k ω => g (θ^[k] ω)) := by
  have hX : ∀ k, Measurable fun ω => g (θ^[k] ω) := fun k =>
    hg.comp (hθ.measurable.iterate k)
  rw [isStationary_iff_measurePreserving hX]
  refine ⟨measurable_shift 1, ?_⟩
  have hcomm : shift 1 ∘ pathOf (fun k ω => g (θ^[k] ω)) =
      pathOf (fun k ω => g (θ^[k] ω)) ∘ θ := by
    ext ω i
    simp only [Function.comp_apply, shift_apply, pathOf]
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
  rw [pathLaw, Measure.map_map (measurable_shift 1) (measurable_pathOf hX), hcomm,
    ← Measure.map_map (measurable_pathOf hX) hθ.measurable, hθ.map_eq]

/-- Miao, p. 121 (converse): for a stationary `X`, on the coordinate space
`(E^ℕ, B(E^ℕ), P̃r)` the shift is measure preserving, `X̃_k = f(θᵏx) = x_k` for `f(x) = x₀`, and
`X̃` has the same finite-dimensional distributions as `X`. -/
theorem stationary_representation {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    MeasurePreserving (shift 1) (pathLaw P X) (pathLaw P X) ∧
      (∀ k (x : ℕ → E), (shift 1)^[k] x 0 = x k) ∧
      ∀ n, (pathLaw P X).map (pathWindow n) = P.map (window X 0 n) := by
  refine ⟨(isStationary_iff_measurePreserving hX).1 hst, fun k x => ?_, fun n => ?_⟩
  · rw [iterate_shift_one, shift_apply, add_zero]
  · rw [pathLaw, Measure.map_map (measurable_pathWindow n) (measurable_pathOf hX), window_zero]

/-- Miao, p. 120: if `X` is stationary and `g` is Borel, `Y_t = g(X_t, …, X_{t+n})` is
stationary. (The book says this for an IID `X`; it holds for every stationary `X`.) -/
theorem isStationary_comp_window {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) {F : Type*}
    [MeasurableSpace F] (n : ℕ) {g : (Fin (n + 1) → E) → F} (hg : Measurable g) :
    IsStationary P (fun t ω => g (window X t n ω)) := by
  have hY : ∀ t, Measurable fun ω => g (window X t n ω) := fun t =>
    hg.comp (measurable_window hX t n)
  set G : (ℕ → E) → ℕ → F := fun x t => g (pathWindow n (shift t x)) with hG
  have hGm : Measurable G := measurable_pi_iff.2 fun t =>
    hg.comp ((measurable_pathWindow n).comp (measurable_shift t))
  have hpath : pathOf (fun t ω => g (window X t n ω)) = G ∘ pathOf X := by
    ext ω t
    rfl
  have hcomm : shift 1 ∘ G = G ∘ shift 1 := by
    ext x t
    simp only [Function.comp_apply, shift_apply, hG, shift_shift]
  rw [isStationary_iff_measurePreserving hY]
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  refine ⟨measurable_shift 1, ?_⟩
  rw [pathLaw, hpath, ← Measure.map_map hGm (measurable_pathOf hX),
    Measure.map_map (measurable_shift 1) hGm, hcomm,
    ← Measure.map_map hGm (measurable_shift 1)]
  change ((pathLaw P X).map (shift 1)).map G = (pathLaw P X).map G
  rw [hmp.map_eq]

/-- Miao, p. 120: an IID sequence is stationary. -/
theorem isStationary_of_iid {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X P)
    (hid : ∀ n, P.map (X n) = P.map (X 0)) : IsStationary P X := by
  intro t n
  have hlaw : ∀ s : ℕ, P.map (window X s n) =
      Measure.pi (fun _ : Fin (n + 1) => P.map (X 0)) := by
    intro s
    have hinj : Function.Injective fun i : Fin (n + 1) => s + (i : ℕ) := by
      intro i j hij
      exact Fin.ext (by simpa using hij)
    have h := (iIndepFun_iff_map_fun_eq_pi_map (f := fun i : Fin (n + 1) => X (s + i))
      (fun i => (hX (s + i)).aemeasurable)).1
      (hind.precomp hinj)
    change P.map (fun ω (i : Fin (n + 1)) => X (s + i) ω) = _
    rw [h]
    congr 1
    ext1 i
    exact hid _
  rw [hlaw t, hlaw 0]

/-! ### Definitions 4.2.2–4.2.3 and the correction -/

/-- **Definition 4.2.2** (Miao, p. 122). `A ⊆ E^ℕ` is shift invariant if `θx ∈ A` whenever
`x ∈ A`. -/
def IsShiftInvariant (A : Set (ℕ → E)) : Prop := ∀ x ∈ A, shift 1 x ∈ A

/-- **Definition 4.2.3** (Miao, p. 122). A process is ergodic if every (measurable) shift
invariant set has probability zero or one: `Pr{(X₀, X₁, …) ∈ A} ∈ {0, 1}`. -/
def IsErgodicProcess (P : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ A : Set (ℕ → E), MeasurableSet A → IsShiftInvariant A →
    P (pathOf X ⁻¹' A) = 0 ∨ P (pathOf X ⁻¹' A) = 1

omit [MeasurableSpace E] in
/-- A transformation-invariant set (`θ⁻¹A = A`) is shift invariant in the sense of
Definition 4.2.2. -/
theorem isShiftInvariant_of_preimage_eq {A : Set (ℕ → E)} (h : shift 1 ⁻¹' A = A) :
    IsShiftInvariant A := fun x hx => by
  rw [← h] at hx
  exact hx

/-- **Correction to Definition 4.2.2 / p. 123.** The shift-invariant sets of Definition 4.2.2 are
not closed under complements: `A = {(0, 0, …)}` is shift invariant but its complement is not
(`(1, 0, 0, …) ∈ Aᶜ` while `θ(1, 0, 0, …) ∉ Aᶜ`). So they do not form a σ-algebra. -/
theorem shiftInvariant_compl_counterexample :
    ∃ A : Set (ℕ → ℝ), MeasurableSet A ∧ IsShiftInvariant A ∧ ¬ IsShiftInvariant Aᶜ := by
  refine ⟨{fun _ => 0}, measurableSet_singleton _, fun x hx => ?_, fun h => ?_⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  · set y : ℕ → ℝ := fun n => if n = 0 then 1 else 0 with hy
    have hy1 : y ∈ ({fun _ => 0} : Set (ℕ → ℝ))ᶜ := by
      intro hmem
      have := congrFun (Set.mem_singleton_iff.1 hmem) 0
      simp [hy] at this
    have h2 := h y hy1
    apply h2
    rw [Set.mem_singleton_iff]
    ext n
    simp [hy, shift]

omit [MeasurableSpace E] in
/-- For a shift-invariant `A`, the sets `θ⁻ⁿA` increase. -/
theorem preimage_shift_mono {A : Set (ℕ → E)} (hA : IsShiftInvariant A) (n : ℕ) :
    shift n ⁻¹' A ⊆ shift (n + 1) ⁻¹' A := by
  intro x hx
  have := hA _ hx
  simpa [Set.mem_preimage, shift_shift] using this

/-- **Correction to p. 123.** Every measurable shift-invariant set `A` (Definition 4.2.2) agrees,
up to a null set, with the transformation-invariant set `B = ⋃ₙ θ⁻ⁿA` (`θ⁻¹B = B`), for any
shift-preserving finite measure. -/
theorem exists_invariant_ae_eq {μ : Measure (ℕ → E)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {A : Set (ℕ → E)} (hAm : MeasurableSet A)
    (hA : IsShiftInvariant A) :
    ∃ B : Set (ℕ → E), MeasurableSet B ∧ shift 1 ⁻¹' B = B ∧ B =ᵐ[μ] A ∧ A ⊆ B := by
  refine ⟨⋃ n, shift n ⁻¹' A, MeasurableSet.iUnion fun n => (measurable_shift n) hAm, ?_, ?_,
    fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩⟩
  · rw [Set.preimage_iUnion]
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, shift_shift]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨1 + n, hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := preimage_shift_mono hA n hn
      simpa [Set.mem_preimage, add_comm] using this
  · have hnull : ∀ n, μ (shift n ⁻¹' A \ A) = 0 := by
      intro n
      have hsub : A ⊆ shift n ⁻¹' A := by
        induction n with
        | zero => intro x hx; simpa [Set.mem_preimage, shift_zero] using hx
        | succ n ih => exact ih.trans (preimage_shift_mono hA n)
      have hmp : MeasurePreserving (shift (X := E) n) μ μ := by
        have := hμ.iterate n
        rwa [show (shift 1)^[n] = shift (X := E) n from funext (iterate_shift_one n)] at this
      rw [measure_sdiff hsub hAm.nullMeasurableSet (measure_ne_top μ A),
        hmp.measure_preimage hAm.nullMeasurableSet, tsub_self]
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · rw [Set.iUnion_sdiff]
      exact measure_iUnion_null hnull
    · rw [Set.sdiff_eq_empty.2 (fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩),
        measure_empty]

/-- Definition 4.2.3 agrees with Definition 4.1.4 for the shift on path space: a stationary
process is ergodic iff `(E^ℕ, B(E^ℕ), P̃r, θ)` is an ergodic dynamical system. -/
theorem isErgodicProcess_iff_isErgodic {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    IsErgodicProcess P X ↔ IsErgodic (pathLaw P X) (shift 1) := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  constructor
  · intro h A hA
    have := h A hA.1 (isShiftInvariant_of_preimage_eq hA.2)
    rwa [pathLaw, Measure.map_apply hΦ hA.1]
  · intro h A hAm hA
    obtain ⟨B, hBm, hB, hBA, -⟩ := exists_invariant_ae_eq hmp hAm hA
    have h1 := h B ⟨hBm, hB⟩
    rw [measure_congr hBA, pathLaw, Measure.map_apply hΦ hAm] at h1
    exact h1

/-! ### Theorem 4.2.1 -/

/-- The σ-algebra `I` of Theorem 4.2.1 on `Ω`: the events `{(X₀, X₁, …) ∈ A}` with `A`
transformation invariant for the shift. -/
abbrev invariantField (X : ℕ → Ω → E) : MeasurableSpace Ω :=
  (MeasurableSpace.invariants (shift (X := E) 1)).comap (pathOf X)

/-- Conditional expectations transported from a law: `E[g(Φ) | Φ⁻¹m] = E_{P∘Φ⁻¹}[g | m](Φ)`. -/
theorem condExp_comp_ae_eq {S : Type*} {m : MeasurableSpace S} [mS : MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {Φ : Ω → S} (hΦ : Measurable Φ) (hm : m ≤ mS)
    {g : S → ℝ} (hg : Integrable g (P.map Φ)) :
    P[g ∘ Φ | m.comap Φ] =ᵐ[P] (P.map Φ)[g | m] ∘ Φ := by
  have hle : m.comap Φ ≤ ‹MeasurableSpace Ω› := (MeasurableSpace.comap_mono hm).trans
    hΦ.comap_le
  have hgΦ : Integrable (g ∘ Φ) P := hg.comp_measurable hΦ
  have hc : Integrable ((P.map Φ)[g | m] ∘ Φ) P :=
    integrable_condExp.comp_measurable hΦ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hgΦ (fun s _ _ => hc.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨B, hB, rfl⟩ := hs
    have hBm : MeasurableSet B := hm B hB
    simp only [Function.comp_apply]
    rw [← setIntegral_map hBm (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
      hΦ.aemeasurable, setIntegral_condExp hm hg hB, setIntegral_map hBm hg.1 hΦ.aemeasurable]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable Φ)).aestronglyMeasurable

/-- Miao, (4.3), p. 123: on path space, `(1/N) Σ_{k<N} f(θᵏx) → Ẽ[f | I]` with `f(x) = x₀`,
`P̃r`-a.s. -/
theorem eq_4_3 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hint : Integrable (X 0) P) :
    ∀ᵐ x ∂pathLaw P X, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
      (fun y : ℕ → ℝ => y 0) ((shift 1)^[k] x)) atTop
      (𝓝 ((pathLaw P X)[fun y => y 0 | MeasurableSpace.invariants (shift 1)] x)) := by
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hf : Integrable (fun y : ℕ → ℝ => y 0) (pathLaw P X) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable
      (measurable_pathOf hX).aemeasurable).2 hint
  exact theorem_4_1_1 hmp (measurable_pi_apply 0) hf

/-- **Theorem 4.2.1** (strong law of large numbers, Miao, (4.1), p. 122). For a stationary
real process with `E|X₀| < ∞`, `(1/N) Σ_{k<N} X_k → E[X₀ | I]`, `Pr`-a.s. -/
theorem theorem_4_2_1 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hint : Integrable (X 0) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, X k ω) atTop
      (𝓝 (P[X 0 | invariantField X] ω)) := by
  have hΦ := measurable_pathOf hX
  have hf : Integrable (fun y : ℕ → ℝ => y 0) (P.map (pathOf X)) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable hΦ.aemeasurable).2 hint
  have h1 := ae_of_ae_map hΦ.aemeasurable (eq_4_3 hX hst hint)
  have h2 := condExp_comp_ae_eq hΦ (MeasurableSpace.invariants_le (shift (X := ℝ) 1)) hf
  filter_upwards [h1, h2] with ω hω1 hω2
  have hX0 : (fun y : ℕ → ℝ => y 0) ∘ pathOf X = X 0 := rfl
  rw [invariantField, ← hX0, hω2]
  refine hω1.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one, shift_apply, add_zero]
  rfl

/-- **Theorem 4.2.1** (Miao, (4.2), p. 122): if `X` is also ergodic,
`(1/N) Σ_{k<N} X_k → E X₀`, `Pr`-a.s. -/
theorem theorem_4_2_1_ergodic {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    (hint : Integrable (X 0) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, X k ω) atTop
      (𝓝 (∫ ω, X 0 ω ∂P)) := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hf : Integrable (fun y : ℕ → ℝ => y 0) (pathLaw P X) :=
    (integrable_map_measure (measurable_pi_apply 0).aestronglyMeasurable hΦ.aemeasurable).2 hint
  have h := theorem_4_1_1_ergodic hmp ((isErgodicProcess_iff_isErgodic hX hst).1 herg)
    (measurable_pi_apply 0) hf
  have hE : ∫ y, (fun y : ℕ → ℝ => y 0) y ∂pathLaw P X = ∫ ω, X 0 ω ∂P :=
    integral_map hΦ.aemeasurable (measurable_pi_apply 0).aestronglyMeasurable
  rw [hE] at h
  filter_upwards [ae_of_ae_map hΦ.aemeasurable h] with ω hω
  refine hω.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one, shift_apply, add_zero]
  rfl

/-! ### Mixing: Definition 4.2.4 and Theorem 4.2.3 -/

/-- **Definition 4.2.4** (Miao, p. 124). A stationary process is mixing if for all
`A, B ∈ B(E^∞)`, `Pr{(X₁, X₂, …) ∈ A, (Xₙ, Xₙ₊₁, …) ∈ B} − Pr{(X₁, …) ∈ A} Pr{(Xₙ, …) ∈ B} → 0`.
-/
def IsMixing (P : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ A B : Set (ℕ → E), MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℕ => P.real ({ω | shift 1 (pathOf X ω) ∈ A} ∩ {ω | shift n (pathOf X ω) ∈ B})
      - P.real {ω | shift 1 (pathOf X ω) ∈ A} * P.real {ω | shift n (pathOf X ω) ∈ B}) atTop
      (𝓝 0)

/-- **Theorem 4.2.3** (Miao, p. 124). A mixing (stationary) process is ergodic. -/
theorem theorem_4_2_3 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hmix : IsMixing P X) :
    IsErgodicProcess P X := by
  intro A hAm hA
  have hΦ := measurable_pathOf hX
  have hlaw := (isStationary_iff_map_shift hX).1 hst
  -- `Pr{(Xₙ, Xₙ₊₁, …) ∈ A} = Pr{(X₀, X₁, …) ∈ A}` for every `n`
  have hstat : ∀ n, P.real {ω | shift n (pathOf X ω) ∈ A} = P.real (pathOf X ⁻¹' A) := by
    intro n
    have h := congrArg (fun m : Measure (ℕ → E) => m.real A) (hlaw n)
    simp only [pathLaw] at h
    rw [map_measureReal_apply (measurable_shift n) hAm, map_measureReal_apply hΦ
      ((measurable_shift n) hAm), map_measureReal_apply hΦ hAm] at h
    exact h
  -- `(X₁, …) ∈ A` implies `(Xₙ, …) ∈ A` for `n ≥ 1`
  have hsub : ∀ n, 1 ≤ n → {ω | shift 1 (pathOf X ω) ∈ A} ⊆ {ω | shift n (pathOf X ω) ∈ A} := by
    intro n hn ω hω
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => exact hω
    | succ k ih =>
      have := hA _ (ih (by omega))
      simp only [Set.mem_ofPred_eq, shift_shift] at this ⊢
      rwa [add_assoc] at this
  set p := P.real (pathOf X ⁻¹' A) with hp
  have hlim := hmix A A hAm hAm
  have hev : ∀ᶠ n : ℕ in atTop, P.real ({ω | shift 1 (pathOf X ω) ∈ A} ∩
      {ω | shift n (pathOf X ω) ∈ A}) - P.real {ω | shift 1 (pathOf X ω) ∈ A} *
      P.real {ω | shift n (pathOf X ω) ∈ A} = p - p * p := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Set.inter_eq_left.2 (hsub n hn), hstat 1, hstat n]
  have hpp : p - p * p = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono
    fun n h => h.symm)) hlim
  have hp01 : p = 0 ∨ p = 1 := by
    have : p * (1 - p) = 0 := by linarith [hpp]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hm : MeasurableSet (pathOf X ⁻¹' A) := hΦ hAm
  rcases hp01 with h | h
  · left
    rw [hp, measureReal_eq_zero_iff] at h
    exact h
  · right
    rw [hp, measureReal_def, ENNReal.toReal_eq_one_iff] at h
    exact h

/-! ### The setting of Theorem 4.2.4 -/

omit [MeasurableSpace Ω] in
/-- Miao, p. 124 (setting of Theorem 4.2.4): if `M₀ ⊆ θ⁻¹M₀`, the σ-algebras `M_k = θ⁻ᵏM₀`
increase. (The central limit theorem of Theorem 4.2.4 is not formalised.) -/
theorem theorem_4_2_4_filtration_mono (θ : Ω → Ω) (M₀ : MeasurableSpace Ω)
    (h : M₀ ≤ M₀.comap θ) (k : ℕ) : M₀.comap θ^[k] ≤ M₀.comap θ^[k + 1] := by
  rw [Function.iterate_succ', ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono h

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equivalent formulations of ergodicity (Miao Theorem 4.2.2, Exercise 5)

Copied from `EconomicDynamics/ErgodicTheory` (module `StationaryErgodicity`), namespace renamed.

Miao, Theorem 4.2.2, p. 123 (after Karlin and Taylor 1975), and Exercise 5, p. 129. For a
stationary process `X` (on any measurable state space) the following are equivalent
(`theorem_4_2_2`, a `List.TFAE`):

* (a) `X` is ergodic (Definition 4.2.3, with the book's shift-invariant sets `θA ⊆ A`);
* (b) `Pr{(X₀, X₁, …) ∈ A} ∈ {0, 1}` for every transformation-invariant `A` (`θ⁻¹A = A`);
* (c) `(1/n) Σ_{j=1}^n 1{(X_j, X_{j+1}, …) ∈ A} → Pr{(X₀, X₁, …) ∈ A}` a.s., for every
  `A ∈ B(E^∞)`;
* (d) the same for the windows `(X_j, …, X_{j+k})` and `A ∈ B(E^{k+1})`;
* (e) `(1/n) Σ_{j=1}^n φ(X_j, …, X_{j+k}) → E φ(X₀, …, X_k)` a.s. for every integrable Borel `φ`;
* (f) `(1/n) Σ_{k=1}^n φ(X_k, X_{k+1}, …) → E φ(X₀, X₁, …)` a.s. for every Borel `φ` with
  `E|φ(X₀, X₁, …)| < ∞`.

The proof: (a) ⇔ (b) is `isErgodicProcess_iff_isErgodic` (the book's (a) and (b) coincide by
Definition 4.2.3; here (b) uses transformation-invariant sets, which makes the equivalence the
correction of p. 123); (b) ⇒ (f) is Birkhoff's theorem; (f) ⇒ (e) ⇒ (d) and (f) ⇒ (c) are
special cases; (c) ⇒ (b) because `1_A(θʲx) = 1_A(x)` for invariant `A`; (d) ⇒ (b) because
(d) gives `P̃r(B ∩ C) = P̃r(B) P̃r(C)` for invariant `B` and every finite-dimensional box `C`,
hence for `C = B`.

`tendsto_avg_succ` moves the averages from `j = 0, …, n − 1` (Birkhoff) to the book's
`j = 1, …, n`. **Exercise 5** asks for the proofs of Theorems 4.2.2 and 4.3.2: `ex_4_5_a` is
Theorem 4.2.2 (Theorem 4.3.2 is `ex_4_5_b` in `ErgodicTheory.StationaryMarkov`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Averages over `j = 1, …, n` have the same limit as averages over `j = 0, …, n − 1`. -/
theorem tendsto_avg_succ {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a (k + 1)) atTop (𝓝 L) := by
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k) atTop
      (𝓝 L) := h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have h3 : Tendsto (fun n : ℕ => a 0 * (1 / (n : ℝ))) atTop (𝓝 (a 0 * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h3
  have h4 := (h2.mul h1).sub h3
  rw [one_mul, sub_zero] at h4
  refine h4.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum : ∑ k ∈ Finset.range n, a (k + 1) = ∑ k ∈ Finset.range (n + 1), a k - a 0 := by
    rw [Finset.sum_range_succ']
    ring
  dsimp only
  rw [hsum]
  push_cast
  field_simp

omit [MeasurableSpace E] in
/-- For `θ⁻¹A = A`, `1_A(θʲx) = 1_A(x)`. -/
theorem indicator_shift_of_invariant {A : Set (ℕ → E)} (hA : shift 1 ⁻¹' A = A) (j : ℕ)
    (x : ℕ → E) : A.indicator (1 : (ℕ → E) → ℝ) (shift j x) = A.indicator 1 x := by
  have h : shift j ⁻¹' A = A := by
    have := iterate_mem_iff hA j
    ext y
    rw [Set.mem_preimage, ← iterate_shift_one, this]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show shift j x ∈ A from
      (show x ∈ shift j ⁻¹' A by rw [h]; exact hx))]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show shift j x ∉ A from
      fun h' => hx (by rw [← h]; exact h'))]

/-- For a shift-preserving `μ` and `θ⁻¹B = B`, `μ(B ∩ θ⁻ʲC) = μ(B ∩ C)`. -/
theorem measure_inter_preimage_shift {μ : Measure (ℕ → E)} (hμ : MeasurePreserving (shift 1) μ μ)
    {B C : Set (ℕ → E)} (hB : shift 1 ⁻¹' B = B) (hBm : MeasurableSet B) (hCm : MeasurableSet C)
    (j : ℕ) : μ (B ∩ shift j ⁻¹' C) = μ (B ∩ C) := by
  have h : shift j ⁻¹' B = B := by
    have := iterate_mem_iff hB j
    ext y
    rw [Set.mem_preimage, ← iterate_shift_one, this]
  have hmp : MeasurePreserving (shift (X := E) j) μ μ := by
    have := hμ.iterate j
    rwa [show (shift 1)^[j] = shift (X := E) j from funext (iterate_shift_one j)] at this
  rw [show B ∩ shift j ⁻¹' C = shift j ⁻¹' (B ∩ C) by rw [Set.preimage_inter, h],
    hmp.measure_preimage (hBm.inter hCm).nullMeasurableSet]

/-- The key step of (d) ⇒ (b): if the averages of `1_C(θʲx)` converge a.s. to `μ(C)` for every
box `C`, then every invariant `B` has `μ(B) ∈ {0, 1}`. -/
theorem measure_eq_zero_or_one_of_boxes {μ : Measure (ℕ → E)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ)
    (hbox : ∀ n (A : ℕ → Set E), (∀ i, MeasurableSet (A i)) → ∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        (boxSet n A).indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) atTop
        (𝓝 (μ.real (boxSet n A))))
    {B : Set (ℕ → E)} (hBm : MeasurableSet B) (hB : shift 1 ⁻¹' B = B) :
    μ B = 0 ∨ μ B = 1 := by
  -- `μ(B ∩ C) = μ(B) μ(C)` for boxes
  have hprod : ∀ n (A : ℕ → Set E), (∀ i, MeasurableSet (A i)) →
      μ.real (B ∩ boxSet n A) = μ.real B * μ.real (boxSet n A) := by
    intro n A hA
    set C := boxSet n A with hC
    have hCm : MeasurableSet C := measurableSet_boxSet n hA
    set F : ℕ → (ℕ → E) → ℝ := fun N x => B.indicator 1 x * ((N : ℝ)⁻¹ *
      ∑ j ∈ Finset.range N, C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) with hF
    have hFm : ∀ N, Measurable (F N) := fun N =>
      (measurable_one.indicator hBm).mul (measurable_const.mul (Finset.measurable_sum _
        fun j _ => (measurable_one.indicator hCm).comp (measurable_shift (j + 1))))
    have hFb : ∀ N x, |F N x| ≤ 1 := by
      intro N x
      have hi : ∀ (S : Set (ℕ → E)) y, 0 ≤ S.indicator (1 : (ℕ → E) → ℝ) y ∧
          S.indicator (1 : (ℕ → E) → ℝ) y ≤ 1 := fun S y => by
        by_cases hy : y ∈ S <;> simp [hy]
      have hsum : (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) ≤ 1 := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        rw [inv_mul_le_iff₀ (by exact_mod_cast hN), mul_one]
        calc ∑ j ∈ Finset.range N, C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)
            ≤ ∑ _j ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun j _ => (hi C _).2
          _ = N := by simp
      have hsum0 : 0 ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => (hi C _).1)
      rw [hF, abs_of_nonneg (mul_nonneg (hi B x).1 hsum0)]
      calc B.indicator 1 x * _ ≤ 1 * 1 := mul_le_mul (hi B x).2 hsum hsum0 zero_le_one
        _ = 1 := one_mul 1
    -- `∫ F N = μ(B ∩ C)` for `N ≥ 1`
    have hint : ∀ N, 1 ≤ N → ∫ x, F N x ∂μ = μ.real (B ∩ C) := by
      intro N hN
      have hterm : ∀ j : ℕ, ∫ x, B.indicator (1 : (ℕ → E) → ℝ) x *
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) ∂μ = μ.real (B ∩ C) := by
        intro j
        have : (fun x => B.indicator (1 : (ℕ → E) → ℝ) x *
            C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) =
            (B ∩ shift (j + 1) ⁻¹' C).indicator 1 := by
          ext x
          by_cases hx : x ∈ B <;> by_cases hy : shift (j + 1) x ∈ C <;>
            simp [hx, hy, Set.indicator_of_mem, Set.indicator_of_notMem]
        rw [this, integral_indicator_one (hBm.inter ((measurable_shift (j + 1)) hCm)),
          measureReal_def, measure_inter_preimage_shift hμ hB hBm hCm, ← measureReal_def]
      have hInt : ∀ j : ℕ, Integrable (fun x => B.indicator (1 : (ℕ → E) → ℝ) x *
          C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) μ := by
        intro j
        refine Integrable.of_bound ((measurable_one.indicator hBm).mul
          ((measurable_one.indicator hCm).comp (measurable_shift (j + 1)))).aestronglyMeasurable
          1 (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        by_cases hx : x ∈ B <;> by_cases hy : shift (j + 1) x ∈ C <;> simp [hx, hy]
      have hFN : F N = fun x => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          B.indicator (1 : (ℕ → E) → ℝ) x * C.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x) := by
        ext x
        simp only [hF]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hFN, integral_const_mul, integral_finsetSum _ fun j _ => hInt j]
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      field_simp
    -- dominated convergence
    have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
      (F := F) (f := fun x => B.indicator 1 x * μ.real C)
      (fun N => (hFm N).aestronglyMeasurable) (integrable_const _)
      (fun N => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb N x)
      (by
        filter_upwards [hbox n A hA] with x hx
        exact tendsto_const_nhds.mul hx)
    have hlim' : ∫ x, B.indicator (1 : (ℕ → E) → ℝ) x * μ.real C ∂μ = μ.real B * μ.real C := by
      rw [integral_mul_const, integral_indicator_one hBm]
    rw [hlim'] at hlim
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' (eventually_atTop.2
      ⟨1, fun N hN => (hint N hN).symm⟩)) hlim
  -- hence `μ|_B = μ(B) μ`
  have hfinB : IsFiniteMeasure (μ B • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact measure_lt_top μ B⟩
  have hmeas : μ.restrict B = μ B • μ := by
    refine ext_of_boxSet fun n A hA => ?_
    have hCm := measurableSet_boxSet n hA
    rw [Measure.restrict_apply hCm, Measure.smul_apply, smul_eq_mul, Set.inter_comm]
    have h := hprod n A hA
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at h
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 h
  have hBB : μ B = μ B * μ B := by
    have := congrArg (fun m : Measure (ℕ → E) => m B) hmeas
    simp only [Measure.restrict_apply hBm, Set.inter_self, Measure.smul_apply,
      smul_eq_mul] at this
    exact this
  have hfin : μ B ≠ ⊤ := measure_ne_top _ _
  by_cases h0 : μ B = 0
  · exact Or.inl h0
  · right
    have := (ENNReal.mul_eq_left h0 hfin).1 hBB.symm
    exact this

/-- **Theorem 4.2.2** (Miao, p. 123). For a stationary process the conditions (a)–(f) are
equivalent (see the module docstring for (a)–(f); the averages run over `j = 1, …, n`). -/
theorem theorem_4_2_2 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    List.TFAE [
      IsErgodicProcess P X,
      ∀ A : Set (ℕ → E), MeasurableSet A → shift 1 ⁻¹' A = A →
        P (pathOf X ⁻¹' A) = 0 ∨ P (pathOf X ⁻¹' A) = 1,
      ∀ A : Set (ℕ → E), MeasurableSet A → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
          A.indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) (pathOf X ω))) atTop
          (𝓝 (P.real (pathOf X ⁻¹' A))),
      ∀ (k : ℕ) (A : Set (Fin (k + 1) → E)), MeasurableSet A → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
          A.indicator (1 : (Fin (k + 1) → E) → ℝ) (window X (j + 1) k ω)) atTop
          (𝓝 (P.real (window X 0 k ⁻¹' A))),
      ∀ (k : ℕ) (φ : (Fin (k + 1) → E) → ℝ), Measurable φ →
        Integrable (fun ω => φ (window X 0 k ω)) P → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, φ (window X (j + 1) k ω))
          atTop (𝓝 (∫ ω, φ (window X 0 k ω) ∂P)),
      ∀ φ : (ℕ → E) → ℝ, Measurable φ → Integrable (fun ω => φ (pathOf X ω)) P → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, φ (shift (j + 1) (pathOf X ω)))
          atTop (𝓝 (∫ ω, φ (pathOf X ω) ∂P))] := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hind : ∀ (S : Set (ℕ → E)), MeasurableSet S → Measurable (S.indicator
      (1 : (ℕ → E) → ℝ)) := fun S hS => measurable_one.indicator hS
  have hindb : ∀ (S : Set (ℕ → E)) (ψ : Ω → ℕ → E), Measurable ψ → MeasurableSet S →
      Integrable (fun ω => S.indicator (1 : (ℕ → E) → ℝ) (ψ ω)) P := by
    intro S ψ hψ hS
    refine Integrable.of_bound ((hind S hS).comp hψ).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ψ ω ∈ S <;> simp [h]
  tfae_have 1 ↔ 2 := by
    rw [isErgodicProcess_iff_isErgodic hX hst]
    constructor
    · intro h A hA hθA
      have := h A ⟨hA, hθA⟩
      rwa [pathLaw, Measure.map_apply hΦ hA] at this
    · intro h A hA
      have := h A hA.1 hA.2
      rwa [pathLaw, Measure.map_apply hΦ hA.1]
  tfae_have 2 → 6 := by
    intro h φ hφ hφi
    have herg : IsErgodic (pathLaw P X) (shift 1) := fun A hA => by
      have := h A hA.1 hA.2
      rwa [pathLaw, Measure.map_apply hΦ hA.1]
    have hφi' : Integrable φ (pathLaw P X) :=
      (integrable_map_measure hφ.aestronglyMeasurable hΦ.aemeasurable).2 hφi
    have hB := theorem_4_1_1_ergodic hmp herg hφ hφi'
    have hE : ∫ y, φ y ∂pathLaw P X = ∫ ω, φ (pathOf X ω) ∂P :=
      integral_map hΦ.aemeasurable hφ.aestronglyMeasurable
    rw [hE] at hB
    filter_upwards [ae_of_ae_map hΦ.aemeasurable hB] with ω hω
    have := tendsto_avg_succ hω
    refine this.congr fun n => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iterate_shift_one]
  tfae_have 6 → 3 := by
    intro h A hA
    have := h (A.indicator 1) (hind A hA) (hindb A (pathOf X) hΦ hA)
    have hE : ∫ ω, A.indicator (1 : (ℕ → E) → ℝ) (pathOf X ω) ∂P = P.real (pathOf X ⁻¹' A) := by
      rw [← integral_indicator_one (hΦ hA)]
      congr 1
    rwa [hE] at this
  tfae_have 6 → 5 := by
    intro h k φ hφ hφi
    have hφi' : Integrable (fun ω => (φ ∘ pathWindow k) (pathOf X ω)) P := by
      have : (fun ω => (φ ∘ pathWindow k) (pathOf X ω)) = fun ω => φ (window X 0 k ω) := by
        rw [window_zero]; rfl
      rw [this]; exact hφi
    have := h (φ ∘ pathWindow k) (hφ.comp (measurable_pathWindow k)) hφi'
    have hE : ∫ ω, (φ ∘ pathWindow k) (pathOf X ω) ∂P = ∫ ω, φ (window X 0 k ω) ∂P := by
      rw [window_zero]; rfl
    rw [hE] at this
    exact this
  tfae_have 5 → 4 := by
    intro h k A hA
    have hφ : Measurable (A.indicator (1 : (Fin (k + 1) → E) → ℝ)) :=
      measurable_one.indicator hA
    have hφi : Integrable (fun ω => A.indicator (1 : (Fin (k + 1) → E) → ℝ)
        (window X 0 k ω)) P := by
      refine Integrable.of_bound (hφ.comp (measurable_window hX 0 k)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      by_cases hω : window X 0 k ω ∈ A <;> simp [hω]
    have := h k _ hφ hφi
    have hE : ∫ ω, A.indicator (1 : (Fin (k + 1) → E) → ℝ) (window X 0 k ω) ∂P =
        P.real (window X 0 k ⁻¹' A) := by
      rw [← integral_indicator_one ((measurable_window hX 0 k) hA)]
      congr 1
    rwa [hE] at this
  tfae_have 3 → 2 := by
    intro h A hA hθA
    have hc := h A hA
    have hconst : ∀ᵐ ω ∂P, A.indicator (1 : (ℕ → E) → ℝ) (pathOf X ω) =
        P.real (pathOf X ⁻¹' A) := by
      filter_upwards [hc] with ω hω
      refine tendsto_nhds_unique (tendsto_const_nhds.congr' (eventually_atTop.2
        ⟨1, fun n hn => ?_⟩)) hω
      simp_rw [indicator_shift_of_invariant hθA]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_mul]
    obtain ⟨ω, hω⟩ := hconst.exists
    have hfin : P (pathOf X ⁻¹' A) ≠ ⊤ := measure_ne_top _ _
    by_cases hmem : pathOf X ω ∈ A
    · rw [Set.indicator_of_mem hmem, Pi.one_apply, measureReal_def] at hω
      right
      exact ((ENNReal.toReal_eq_one_iff _).1 hω.symm)
    · rw [Set.indicator_of_notMem hmem, measureReal_def] at hω
      left
      exact ((ENNReal.toReal_eq_zero_iff _).1 hω.symm).resolve_right hfin
  tfae_have 4 → 2 := by
    intro h A hA hθA
    have hbox : ∀ n (B : ℕ → Set E), (∀ i, MeasurableSet (B i)) → ∀ᵐ x ∂pathLaw P X,
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          (boxSet n B).indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x)) atTop
          (𝓝 ((pathLaw P X).real (boxSet n B))) := by
      intro n B hB
      set R := Set.univ.pi fun i : Fin (n + 1) => B i with hR
      have hRm : MeasurableSet R := MeasurableSet.univ_pi fun i => hB i
      have hd := h n R hRm
      have hmeasC : MeasurableSet {x : ℕ → E | Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
          ∑ j ∈ Finset.range N, (boxSet n B).indicator (1 : (ℕ → E) → ℝ) (shift (j + 1) x))
          atTop (𝓝 ((pathLaw P X).real (boxSet n B)))} :=
        measurableSet_tendsto _ fun N => measurable_const.mul (Finset.measurable_sum _
          fun j _ => (hind _ (measurableSet_boxSet n hB)).comp (measurable_shift (j + 1)))
      change ∀ᵐ x ∂(P.map (pathOf X)), _
      rw [ae_map_iff hΦ.aemeasurable hmeasC]
      have hlim : P.real (window X 0 n ⁻¹' R) = (pathLaw P X).real (boxSet n B) := by
        rw [pathLaw, map_measureReal_apply hΦ (measurableSet_boxSet n hB), boxSet_eq_preimage,
          window_zero]
        rfl
      filter_upwards [hd] with ω hω
      rw [← hlim]
      refine hω.congr fun N => ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [boxSet_eq_preimage]
      rfl
    have := measure_eq_zero_or_one_of_boxes hmp hbox hA hθA
    rwa [pathLaw, Measure.map_apply hΦ hA] at this
  tfae_finish

/-- **Exercise 5** (Miao, p. 129), first part: the proof of Theorem 4.2.2 (`theorem_4_2_2`). -/
theorem ex_4_5_a {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) :
    IsErgodicProcess P X ↔ ∀ φ : (ℕ → E) → ℝ, Measurable φ →
      Integrable (fun ω => φ (pathOf X ω)) P → ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, φ (shift (j + 1) (pathOf X ω)))
          atTop (𝓝 (∫ ω, φ (pathOf X ω) ∂P)) :=
  (theorem_4_2_2 hX hst).out 1 6

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GMM set-up (Miao, Chapter 12 introduction and §12.1, pp. 385–388)

Miao, pp. 385–388. The model generates `ℝ^r`-valued data `x_t`; here the data are a process
`X : ℕ → Ω → E` on a probability space `(Ω, P)` with values in a measurable space `E` (the book's
`ℝ^r`; nothing below needs more structure), and the observed sample is `x₀, …, x_{T−1}` (the book
indexes it `t = 1, …, T`). Parameters are `θ ∈ Θ ⊆ ℝ^k` (`Fin k → ℝ`, sup norm), and the moment
function `h : E → ℝ^k → ℝ^q` has `q` coordinates.

* `gm_sampleMoment X h T ω θ = g_T(θ) = (1/T) Σ_{t<T} h(x_t, θ)` (p. 388);
* `gm_popMoment P X h θ = g(θ) = E h(x₀, θ)` (12.1), coordinatewise (for a stationary process
  `E h(x_t, θ) = E h(x₀, θ)` for every `t`, `gm_integral_comp_eq`);
* `gm_quadForm W v = v'Wv` and the GMM objective `Q_T(θ) = g_T(θ)' W_T g_T(θ)` (`gm_objective`)
  and its population analogue `Q₀(θ) = g(θ)' W g(θ)` (`gm_popObjective`, p. 389);
* `Assumption_12_1_3` (global identification), `Assumption_12_1_7` (dominance) and
  `Assumption_12_1_4` (the weighting matrices) as named propositions. Assumptions 12.1.1, 12.1.5
  are `IsStationary` and `IsErgodicProcess` of Chapter 4; Assumptions 12.1.2, 12.1.6 are stated
  as hypotheses (`ContinuousOn`, `IsCompact`) where they are used.

Departure (see `docs/GM-corrections.md`): Assumption 12.1.7, `E[sup_θ ‖h(x_t, θ)‖] < ∞`, is stated
as the existence of an integrable envelope `D` with `‖h(x, θ)‖ ≤ D(x)` on `Θ`; the supremum over
an uncountable `Θ` need not be measurable, and when it is, `D = sup_θ ‖h(·, θ)‖` is such an
envelope (`assumption_12_1_7_of_sup`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Miao, p. 388: the sample moment `g_T(θ) = (1/T) Σ_{t<T} h(x_t, θ)`. -/
noncomputable def gm_sampleMoment {k q : ℕ} (X : ℕ → Ω → E) (h : E → (Fin k → ℝ) → Fin q → ℝ)
    (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) : Fin q → ℝ :=
  fun i => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, h (X t ω) θ i

/-- Miao, (12.1), p. 387: the population moment `g(θ) = E[h(x_t, θ)]` (at `t = 0`). -/
noncomputable def gm_popMoment {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (θ : Fin k → ℝ) : Fin q → ℝ :=
  fun i => ∫ ω, h (X 0 ω) θ i ∂P

/-- The quadratic form `v'Wv = Σ_i Σ_j v_i W_ij v_j`. -/
def gm_quadForm {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * W i j * v j

/-- Miao, p. 388: the GMM objective `Q_T(θ) = g_T(θ)' W_T g_T(θ)`. -/
noncomputable def gm_objective {k q : ℕ} (X : ℕ → Ω → E) (h : E → (Fin k → ℝ) → Fin q → ℝ)
    (WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ) (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) : ℝ :=
  gm_quadForm (WT T ω) (gm_sampleMoment X h T ω θ)

/-- Miao, p. 389: the population objective `Q₀(θ) = E[h(x_t, θ)]' W E[h(x_t, θ)]`. -/
noncomputable def gm_popObjective {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (W : Matrix (Fin q) (Fin q) ℝ) (θ : Fin k → ℝ) : ℝ :=
  gm_quadForm W (gm_popMoment P X h θ)

/-- **Assumption 12.1.3** (global identification, Miao, p. 387): on `Θ`,
`E[h(x_t, θ)] = 0` if and only if `θ = θ₀`. -/
def Assumption_12_1_3 {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (Θ : Set (Fin k → ℝ)) (θ₀ : Fin k → ℝ) : Prop :=
  ∀ θ ∈ Θ, gm_popMoment P X h θ = 0 ↔ θ = θ₀

/-- **Assumption 12.1.4** (Miao, p. 388): each `W_T` is positive semidefinite and `W_T → W` in
probability (entrywise) with `W` positive definite. -/
def Assumption_12_1_4 {q : ℕ} (P : Measure Ω) (WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ)
    (W : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  (∀ T ω, (WT T ω).PosSemidef) ∧ W.PosDef ∧
    ∀ i j, TendstoInMeasure P (fun T ω => WT T ω i j) atTop (fun _ => W i j)

/-- **Assumption 12.1.7** (dominance, Miao, p. 389), in envelope form: there is a measurable
`D` with `E D(x_t) < ∞` and `‖h(x, θ)‖ ≤ D(x)` for all `x` and `θ ∈ Θ`. -/
def Assumption_12_1_7 {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (h : E → (Fin k → ℝ) → Fin q → ℝ) (Θ : Set (Fin k → ℝ)) : Prop :=
  ∃ D : E → ℝ, Measurable D ∧ Integrable (fun ω => D (X 0 ω)) P ∧ ∀ x, ∀ θ ∈ Θ, ‖h x θ‖ ≤ D x

/-- Miao, Assumption 12.1.7 (p. 389): if `x ↦ sup_{θ∈Θ} ‖h(x, θ)‖` is finite, measurable and
integrable, it is an envelope, so the book's `E[sup_θ ‖h(x_t, θ)‖] < ∞` gives
`Assumption_12_1_7`. -/
theorem assumption_12_1_7_of_sup {k q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E}
    {h : E → (Fin k → ℝ) → Fin q → ℝ} {Θ : Set (Fin k → ℝ)}
    (hbdd : ∀ x, BddAbove ((fun θ => ‖h x θ‖) '' Θ))
    (hm : Measurable fun x => sSup ((fun θ => ‖h x θ‖) '' Θ))
    (hi : Integrable (fun ω => sSup ((fun θ => ‖h (X 0 ω) θ‖) '' Θ)) P) :
    Assumption_12_1_7 P X h Θ :=
  ⟨fun x => sSup ((fun θ => ‖h x θ‖) '' Θ), hm, hi, fun x _ hθ =>
    le_csSup (hbdd x) (Set.mem_image_of_mem _ hθ)⟩

/-- `gm_quadForm W v = v ⬝ᵥ W.mulVec v`. -/
theorem gm_quadForm_eq {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    gm_quadForm W v = v ⬝ᵥ W.mulVec v := by
  simp only [gm_quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The quadratic form is continuous in the vector. -/
theorem gm_continuous_quadForm {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) :
    Continuous (gm_quadForm W) := by
  unfold gm_quadForm
  fun_prop

/-- For positive definite `W`, `v'Wv > 0` when `v ≠ 0`. -/
theorem gm_quadForm_pos {q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef)
    {v : Fin q → ℝ} (hv : v ≠ 0) : 0 < gm_quadForm W v := by
  rw [gm_quadForm_eq]
  have := hW.dotProduct_mulVec_pos hv
  simpa using this

/-- `0'W0 = 0`. -/
theorem gm_quadForm_zero {q : ℕ} (W : Matrix (Fin q) (Fin q) ℝ) : gm_quadForm W 0 = 0 := by
  simp [gm_quadForm]

/-- Miao, p. 387: for a stationary process the mean `E h(x_t, θ)` does not depend on `t`. -/
theorem gm_integral_comp_eq {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) {φ : E → ℝ} (hφ : Measurable φ)
    (t : ℕ) : ∫ ω, φ (X t ω) ∂P = ∫ ω, φ (X 0 ω) ∂P := by
  have h := hst t 0
  have hm : Measurable fun y : Fin 1 → E => φ (y 0) := hφ.comp (measurable_pi_apply 0)
  have e1 : ∫ ω, φ (X t ω) ∂P = ∫ y, φ (y 0) ∂(P.map (window X t 0)) := by
    rw [integral_map (measurable_window hX t 0).aemeasurable hm.aestronglyMeasurable]
    simp [window]
  have e0 : ∫ ω, φ (X 0 ω) ∂P = ∫ y, φ (y 0) ∂(P.map (window X 0 0)) := by
    rw [integral_map (measurable_window hX 0 0).aemeasurable hm.aestronglyMeasurable]
    simp [window]
  rw [e1, e0, h]

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The uniform law of large numbers behind Theorem 12.1.1 (Miao, §12.1, pp. 388–390)

Miao, p. 388 ("when a law of large numbers applies, we can replace the population moment by the
empirical moment") and p. 389 (the proof of Theorem 12.1.1 is referred to Hall 2005, p. 68, whose
key step is that `Q_T → Q₀` uniformly on `Θ`). We prove, from Birkhoff's ergodic theorem
(`theorem_4_1_1_ergodic`, Chapter 4), that for a stationary ergodic process (Assumptions 12.1.1,
12.1.5), a compact `Θ` (12.1.6), `h(x, ·)` continuous on `Θ` (12.1.2) and an integrable envelope
(12.1.7),

`sup_{θ∈Θ} ‖g_T(θ) − E h(x₀, θ)‖ → 0` almost surely (`gm_ulln`, `TendstoUniformlyOn`).

The proof is the classical bracketing argument: for `θ₀ ∈ Θ` and `δ > 0` the modulus
`Δ(x) = sup {|f(x, c) − f(x, θ₀)| : c ∈ C, |c − θ₀| < δ}` over a countable dense `C ⊆ Θ` is
measurable, dominates the oscillation of `f(x, ·)` on the `δ`-ball (`gm_abs_sub_le_modulus`),
and `E Δ(x₀) → 0` as `δ → 0` by dominated convergence (`gm_exists_modulus_lt`); a finite cover of
`Θ` by such balls and Birkhoff's theorem for the finitely many functions involved finish the
argument (`gm_ulln_scalar_eps`).

Also: the population moment `θ ↦ E h(x₀, θ)` is finite and continuous on `Θ`
(`gm_continuousOn_popMoment`), so the second half of Assumption 12.1.2 follows from the first half
and Assumption 12.1.7.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Miao, p. 388 (the law of large numbers used for `g_T`): for a stationary ergodic process and
a measurable `φ` with `E|φ(x₀)| < ∞`, `(1/N) Σ_{t<N} φ(x_t) → E φ(x₀)` almost surely; Birkhoff's
theorem (`theorem_4_1_1_ergodic`) on path space. -/
theorem gm_ergodic_avg {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {φ : E → ℝ} (hφ : Measurable φ) (hint : Integrable (fun ω => φ (X 0 ω)) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, φ (X t ω)) atTop
      (𝓝 (∫ ω, φ (X 0 ω) ∂P)) := by
  have hΦ := measurable_pathOf hX
  have := isProbabilityMeasure_pathLaw P (X := X)
  have hmp := (isStationary_iff_measurePreserving hX).1 hst
  have hfm : Measurable (fun y : ℕ → E => φ (y 0)) := hφ.comp (measurable_pi_apply 0)
  have hf : Integrable (fun y : ℕ → E => φ (y 0)) (pathLaw P X) :=
    (integrable_map_measure hfm.aestronglyMeasurable hΦ.aemeasurable).2 hint
  have h := theorem_4_1_1_ergodic hmp ((isErgodicProcess_iff_isErgodic hX hst).1 herg) hfm hf
  have hE : ∫ y, (fun y : ℕ → E => φ (y 0)) y ∂pathLaw P X = ∫ ω, φ (X 0 ω) ∂P :=
    integral_map hΦ.aemeasurable hfm.aestronglyMeasurable
  rw [hE] at h
  filter_upwards [ae_of_ae_map hΦ.aemeasurable h] with ω hω
  refine hω.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [iterate_shift_one, shift_apply, add_zero]
  rfl

/-- If `φ` is continuous on `Θ`, `S ⊆ Θ`, `θ ∈ Θ ∩ closure S` and `φ ≤ M` on `S`, then
`φ θ ≤ M`. -/
theorem gm_le_of_mem_closure {α : Type*} [TopologicalSpace α] {S Θ : Set α} (hS : S ⊆ Θ)
    {φ : α → ℝ} (hφ : ContinuousOn φ Θ) {θ : α} (hθ : θ ∈ Θ) (hcl : θ ∈ closure S) {M : ℝ}
    (hM : ∀ c ∈ S, φ c ≤ M) : φ θ ≤ M := by
  have h1 := ((hφ θ hθ).mono hS).mem_closure_image hcl
  have hsub : φ '' S ⊆ Set.Iic M := by
    rintro _ ⟨c, hc, rfl⟩
    exact hM c hc
  exact closure_minimal hsub isClosed_Iic h1

/-- The modulus `Δ(x) = sup {|f(x, c) − f(x, θ₀)| : c ∈ C, |c − θ₀| < δ}` (a countable
supremum). -/
noncomputable def gm_modulus {k : ℕ} (C : Set (Fin k → ℝ)) (f : E → (Fin k → ℝ) → ℝ)
    (θ₀ : Fin k → ℝ) (δ : ℝ) (x : E) : ℝ :=
  ⨆ c : ↥(C ∩ Metric.ball θ₀ δ), |f x c - f x θ₀|

omit [MeasurableSpace E] in
theorem gm_modulus_nonneg {k : ℕ} (C : Set (Fin k → ℝ)) (f : E → (Fin k → ℝ) → ℝ)
    (θ₀ : Fin k → ℝ) (δ : ℝ) (x : E) : 0 ≤ gm_modulus C f θ₀ δ x :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [MeasurableSpace E] in
theorem gm_modulus_le {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCΘ : C ⊆ Θ) {f : E → (Fin k → ℝ) → ℝ}
    {D : E → ℝ} (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) (δ : ℝ)
    (x : E) : gm_modulus C f θ₀ δ x ≤ 2 * D x := by
  have hD : 0 ≤ D x := (abs_nonneg _).trans (hdom x θ₀ hθ₀)
  refine Real.iSup_le (fun c => ?_) (by linarith)
  have h1 := hdom x c (hCΘ c.2.1)
  have h2 := hdom x θ₀ hθ₀
  have := abs_sub (f x c) (f x θ₀)
  linarith

theorem gm_measurable_modulus {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCc : C.Countable)
    (hCΘ : C ⊆ Θ) {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) (δ : ℝ) : Measurable (gm_modulus C f θ₀ δ) := by
  have : Countable ↥(C ∩ Metric.ball θ₀ δ) := (hCc.mono Set.inter_subset_left).to_subtype
  exact Measurable.iSup fun c =>
    continuous_abs.measurable.comp ((hfm c (hCΘ c.2.1)).sub (hfm θ₀ hθ₀))

omit [MeasurableSpace E] in
/-- The modulus dominates the oscillation of `f(x, ·)` on `Θ ∩ B(θ₀, δ)`. -/
theorem gm_abs_sub_le_modulus {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCΘ : C ⊆ Θ)
    (hΘC : Θ ⊆ closure C) {f : E → (Fin k → ℝ) → ℝ} (hfc : ∀ x, ContinuousOn (f x) Θ)
    {D : E → ℝ} (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) {δ : ℝ}
    (x : E) {θ : Fin k → ℝ} (hθ : θ ∈ Θ) (hd : dist θ θ₀ < δ) :
    |f x θ - f x θ₀| ≤ gm_modulus C f θ₀ δ x := by
  have hcl : θ ∈ closure (C ∩ Metric.ball θ₀ δ) := by
    have h := Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball.2 hd, hΘC hθ⟩
    rwa [Set.inter_comm] at h
  have hφ : ContinuousOn (fun θ' => |f x θ' - f x θ₀|) Θ :=
    ((hfc x).sub continuousOn_const).abs
  refine gm_le_of_mem_closure ((Set.inter_subset_left).trans hCΘ) hφ hθ hcl fun c hc => ?_
  have hbdd : BddAbove (Set.range fun c : ↥(C ∩ Metric.ball θ₀ δ) => |f x c - f x θ₀|) := by
    refine ⟨2 * D x, ?_⟩
    rintro _ ⟨c', rfl⟩
    have h1 := hdom x c' (hCΘ c'.2.1)
    have h2 := hdom x θ₀ hθ₀
    have := abs_sub (f x c') (f x θ₀)
    simp only
    linarith
  exact le_ciSup (f := fun c : ↥(C ∩ Metric.ball θ₀ δ) => |f x c - f x θ₀|) hbdd ⟨c, hc⟩

/-- Dominated convergence: `E Δ(x₀) → 0` as the radius shrinks, so some radius makes it
smaller than any `ε > 0`. -/
theorem gm_exists_modulus_lt {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k : ℕ} {C Θ : Set (Fin k → ℝ)} (hCc : C.Countable) (hCΘ : C ⊆ Θ)
    {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    (hfc : ∀ x, ContinuousOn (f x) Θ) {D : E → ℝ}
    (hDi : Integrable (fun ω => D (X 0 ω)) P) (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x)
    {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∫ ω, gm_modulus C f θ₀ δ (X 0 ω) ∂P < ε := by
  have hlim : Tendsto (fun n : ℕ => ∫ ω, gm_modulus C f θ₀ (1 / ((n : ℝ) + 1)) (X 0 ω) ∂P)
      atTop (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => 2 * D (X 0 ω)) (fun n => ?_)
      (hDi.const_mul 2) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact ((gm_measurable_modulus hCc hCΘ hfm hθ₀ _).comp (hX 0)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (gm_modulus_nonneg _ _ _ _ _)]
      exact gm_modulus_le hCΘ hdom hθ₀ _ _
    · rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨r, hr, hcont⟩ := Metric.continuousWithinAt_iff.1 (hfc (X 0 ω) θ₀ hθ₀) (η / 2)
        (by linarith)
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
      refine ⟨N, fun n hn => ?_⟩
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have hM : gm_modulus C f θ₀ (1 / ((n : ℝ) + 1)) (X 0 ω) ≤ η / 2 := by
        refine Real.iSup_le (fun c => ?_) (by linarith)
        have hc := Metric.mem_ball.1 c.2.2
        have := hcont (hCΘ c.2.1) (by linarith)
        rw [Real.dist_eq] at this
        exact this.le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (gm_modulus_nonneg _ _ _ _ _)]
      linarith
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- The uniform law of large numbers at a fixed tolerance `ε`: almost surely, eventually
`|E f(x₀, θ) − (1/T) Σ_{t<T} f(x_t, θ)| < ε` for all `θ ∈ Θ` simultaneously. -/
theorem gm_ulln_scalar_eps {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    (hfc : ∀ x, ContinuousOn (f x) Θ) {D : E → ℝ}
    (hDi : Integrable (fun ω => D (X 0 ω)) P) (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ T : ℕ in atTop, ∀ θ ∈ Θ,
      dist (∫ ω', f (X 0 ω') θ ∂P) ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (X t ω) θ) < ε := by
  obtain ⟨C, hCΘ, hCc, hΘC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Θ).exists_countable_dense_subset
  have hε3 : 0 < ε / 3 := by linarith
  have hδ : ∀ θ₀ : Fin k → ℝ, ∃ δ > 0, θ₀ ∈ Θ →
      ∫ ω, gm_modulus C f θ₀ δ (X 0 ω) ∂P < ε / 3 := by
    intro θ₀
    by_cases hθ₀ : θ₀ ∈ Θ
    · obtain ⟨δ, hδ, h⟩ := gm_exists_modulus_lt hX hCc hCΘ hfm hfc hDi hdom hθ₀ hε3
      exact ⟨δ, hδ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hθ₀⟩
  choose δ hδpos hδint using hδ
  obtain ⟨t, htΘ, hcov⟩ := hΘ.elim_nhds_subcover (fun θ₀ => Metric.ball θ₀ (δ θ₀))
    (fun θ₀ _ => Metric.ball_mem_nhds θ₀ (hδpos θ₀))
  have hint : ∀ θ ∈ Θ, Integrable (fun ω => f (X 0 ω) θ) P := fun θ hθ =>
    Integrable.mono' hDi ((hfm θ hθ).comp (hX 0)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hdom _ θ hθ)
  have hintΔ : ∀ θ₀ ∈ Θ, Integrable (fun ω => gm_modulus C f θ₀ (δ θ₀) (X 0 ω)) P :=
    fun θ₀ hθ₀ => Integrable.mono' (hDi.const_mul 2)
      ((gm_measurable_modulus hCc hCΘ hfm hθ₀ _).comp (hX 0)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gm_modulus_nonneg _ _ _ _ _)]
        exact gm_modulus_le hCΘ hdom hθ₀ _ _)
  have hae : ∀ᵐ ω ∂P, ∀ i : ↥t,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ s ∈ Finset.range N, f (X s ω) (i : Fin k → ℝ)) atTop
        (𝓝 (∫ ω, f (X 0 ω) (i : Fin k → ℝ) ∂P)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ s ∈ Finset.range N,
        gm_modulus C f i (δ i) (X s ω)) atTop
        (𝓝 (∫ ω, gm_modulus C f i (δ i) (X 0 ω) ∂P)) := by
    refine ae_all_iff.2 fun i => ?_
    have hi := htΘ i i.2
    exact (gm_ergodic_avg hX hst herg (hfm i hi) (hint i hi)).and
      (gm_ergodic_avg hX hst herg (gm_measurable_modulus hCc hCΘ hfm hi _) (hintΔ i hi))
  filter_upwards [hae] with ω hω
  have hev : ∀ᶠ T : ℕ in atTop, ∀ i : ↥t,
      dist ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) (i : Fin k → ℝ))
        (∫ ω, f (X 0 ω) (i : Fin k → ℝ) ∂P) < ε / 3 ∧
      (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, gm_modulus C f i (δ i) (X s ω) < ε / 3 := by
    refine Filter.eventually_all.2 fun i => ?_
    exact (Metric.tendsto_nhds.1 (hω i).1 _ hε3).and
      ((hω i).2.eventually_lt_const (hδint i (htΘ i i.2)))
  filter_upwards [hev] with T hT θ hθ
  obtain ⟨θ₀, hθ₀t, hball⟩ := Set.mem_iUnion₂.1 (hcov hθ)
  have hθ₀ := htΘ θ₀ hθ₀t
  have hd := Metric.mem_ball.1 hball
  obtain ⟨h1, h2⟩ := hT ⟨θ₀, hθ₀t⟩
  simp only at h1 h2
  rw [Real.dist_eq] at h1 ⊢
  -- the empirical oscillation
  have hosc : |(T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ -
      (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ₀| ≤
      (T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, gm_modulus C f θ₀ (δ θ₀) (X s ω) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by positivity)
    exact Finset.sum_le_sum fun s _ =>
      gm_abs_sub_le_modulus hCΘ hΘC hfc hdom hθ₀ _ hθ hd
  -- the population oscillation
  have hpop : |∫ ω, f (X 0 ω) θ₀ ∂P - ∫ ω, f (X 0 ω) θ ∂P| ≤
      ∫ ω, gm_modulus C f θ₀ (δ θ₀) (X 0 ω) ∂P := by
    rw [← integral_sub (hint θ₀ hθ₀) (hint θ hθ)]
    refine abs_integral_le_integral_abs.trans (integral_mono ((hint θ₀ hθ₀).sub
      (hint θ hθ)).abs (hintΔ θ₀ hθ₀) fun ω => ?_)
    rw [abs_sub_comm]
    exact gm_abs_sub_le_modulus hCΘ hΘC hfc hdom hθ₀ _ hθ hd
  have hδ3 := hδint θ₀ hθ₀
  have key := abs_sub_le (∫ ω, f (X 0 ω) θ ∂P) (∫ ω, f (X 0 ω) θ₀ ∂P)
    ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ)
  have key2 := abs_sub_le (∫ ω, f (X 0 ω) θ₀ ∂P)
    ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ₀)
    ((T : ℝ)⁻¹ * ∑ s ∈ Finset.range T, f (X s ω) θ)
  rw [abs_sub_comm] at hpop h1 hosc
  linarith

/-- The uniform law of large numbers (scalar case): almost surely
`sup_{θ∈Θ} |(1/T) Σ_{t<T} f(x_t, θ) − E f(x₀, θ)| → 0`. -/
theorem gm_ulln_scalar {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {f : E → (Fin k → ℝ) → ℝ} (hfm : ∀ θ ∈ Θ, Measurable fun x => f x θ)
    (hfc : ∀ x, ContinuousOn (f x) Θ) {D : E → ℝ}
    (hDi : Integrable (fun ω => D (X 0 ω)) P) (hdom : ∀ x, ∀ θ ∈ Θ, |f x θ| ≤ D x) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun (T : ℕ) θ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (X t ω) θ)
      (fun θ => ∫ ω', f (X 0 ω') θ ∂P) atTop Θ := by
  have h := ae_all_iff.2 fun m : ℕ =>
    gm_ulln_scalar_eps hX hst herg hΘ hfm hfc hDi hdom (ε := 1 / ((m : ℝ) + 1)) (by positivity)
  filter_upwards [h] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with T hT θ hθ
  exact (hT θ hθ).trans hm

/-- **Uniform law of large numbers** (Miao, pp. 388–390, the step behind Theorem 12.1.1). Under
Assumptions 12.1.1, 12.1.2 (continuity of `h` in `θ`), 12.1.5, 12.1.6 and 12.1.7, almost surely
`sup_{θ∈Θ} ‖g_T(θ) − E h(x₀, θ)‖ → 0`. -/
theorem gm_ulln {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hdom : Assumption_12_1_7 P X h Θ) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun T θ => gm_sampleMoment X h T ω θ)
      (gm_popMoment P X h) atTop Θ := by
  obtain ⟨D, -, hDi, hD⟩ := hdom
  have h1 := ae_all_iff.2 fun i : Fin q =>
    gm_ulln_scalar hX hst herg hΘ (f := fun x θ => h x θ i)
      (fun θ hθ => measurable_pi_iff.1 (hm θ hθ) i)
      (fun x => continuousOn_pi.1 (hc x) i) hDi
      (fun x θ hθ => (norm_le_pi_norm (h x θ) i).trans (hD x θ hθ))
  filter_upwards [h1] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := Filter.eventually_all.2 fun i : Fin q =>
    (Metric.tendstoUniformlyOn_iff.1 (hω i)) ε hε
  filter_upwards [hev] with T hT θ hθ
  exact (dist_pi_lt_iff hε).2 fun i => hT i θ hθ

/-- Miao, Assumption 12.1.2 (p. 387): under Assumption 12.1.7, continuity of `h(x, ·)` on `Θ`
makes `θ ↦ E h(x₀, θ)` continuous on `Θ` (dominated convergence). -/
theorem gm_continuousOn_popMoment {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ) (hc : ∀ x, ContinuousOn (h x) Θ)
    (hdom : Assumption_12_1_7 P X h Θ) : ContinuousOn (gm_popMoment P X h) Θ := by
  obtain ⟨D, -, hDi, hD⟩ := hdom
  refine continuousOn_pi.2 fun i => ?_
  refine continuousOn_of_dominated (F := fun θ ω => h (X 0 ω) θ i)
    (fun θ hθ => ((measurable_pi_iff.1 (hm θ hθ) i).comp (hX 0)).aestronglyMeasurable)
    (fun θ hθ => ae_of_all _ fun ω => ?_) hDi (ae_of_all _ fun ω => ?_)
  · rw [Real.norm_eq_abs]
    exact (norm_le_pi_norm (h (X 0 ω) θ) i).trans (hD _ θ hθ)
  · exact continuousOn_pi.1 (hc (X 0 ω)) i

/-- Miao, Assumption 12.1.2 (p. 387): under Assumption 12.1.7 each `E h_i(x₀, θ)` is finite. -/
theorem gm_integrable_moment {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ) (hdom : Assumption_12_1_7 P X h Θ)
    {θ : Fin k → ℝ} (hθ : θ ∈ Θ) (i : Fin q) : Integrable (fun ω => h (X 0 ω) θ i) P := by
  obtain ⟨D, -, hDi, hD⟩ := hdom
  exact Integrable.mono' hDi ((measurable_pi_iff.1 (hm θ hθ) i).comp (hX 0)).aestronglyMeasurable
    (ae_of_all _ fun ω => (norm_le_pi_norm (h (X 0 ω) θ) i).trans (hD _ θ hθ))

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Consistency of GMM: Theorem 12.1.1 (Miao, §12.1, pp. 388–390)

Miao, pp. 388–390. The GMM estimator `θ̂_T` minimises `Q_T(θ) = g_T(θ)' W_T g_T(θ)` over `Θ`.

* `gm_exists_estimator`: for compact nonempty `Θ` and `h(x, ·)` continuous a minimiser exists
  for every `T` and every sample.
* `gm_popObjective_unique_min` (p. 389): by global identification and `W > 0`, `Q₀` has the
  unique minimiser `θ₀` on `Θ`, with `Q₀(θ₀) = 0`.
* `gm_argmin_stable`: the deterministic heart of the proof ("if `θ̂_T` minimises `Q_T` and `Q_T`
  converges to `Q₀` whose unique minimum is at `θ₀`, then `θ̂_T` must converge to `θ₀`"), in a
  quantitative form: for every `ε > 0` there is `ρ > 0` such that any minimiser of `G'VG` over
  `Θ` with `sup_Θ |G − g| ≤ ρ` and `|V − W| ≤ ρ` (entrywise) lies within `ε` of `θ₀`.
* `theorem_12_1_1` (**Theorem 12.1.1**): under Assumptions 12.1.1–12.1.7, `θ̂_T → θ₀` in
  probability. The proof combines the uniform law of large numbers `gm_ulln` (from Birkhoff's
  theorem) with `gm_argmin_stable`; it needs no measurability of `θ̂_T` (Mathlib's
  `TendstoInMeasure` uses the outer measure). `theorem_12_1_1_ae` is the strong-consistency
  variant when `W_T → W` almost surely.

Departures: of Assumption 12.1.4 only `W > 0` and `W_T → W` are used (positive semidefiniteness
of `W_T` is not needed); Assumption 12.1.2's continuity of `E h` is derived
(`gm_continuousOn_popMoment`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- If a.s. eventually `ω ∉ C_T`, for measurable `C_T`, then `P(C_T) → 0`. -/
theorem gm_tendsto_measure_of_ae_eventually {P : Measure Ω} [IsFiniteMeasure P]
    {C : ℕ → Set Ω} (hC : ∀ T, MeasurableSet (C T)) (h : ∀ᵐ ω ∂P, ∀ᶠ T in atTop, ω ∉ C T) :
    Tendsto (fun T => P (C T)) atTop (𝓝 0) := by
  set A : ℕ → Set Ω := fun N => ⋃ T, ⋃ (_ : N ≤ T), C T with hA
  have hAm : ∀ N, MeasurableSet (A N) := fun N =>
    MeasurableSet.iUnion fun T => MeasurableSet.iUnion fun _ => hC T
  have hanti : Antitone A := by
    intro N M hNM ω hω
    obtain ⟨T, hT, hTC⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2 ⟨T, le_trans hNM hT, hTC⟩
  have h0 : P (⋂ N, A N) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro ω hω hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    obtain ⟨T, hT, hTC⟩ := Set.mem_iUnion₂.1 (Set.mem_iInter.1 hω N)
    exact hN T hT hTC
  have hlim := tendsto_measure_iInter_atTop (fun N => (hAm N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  rw [h0] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun N => measure_mono fun ω hω => Set.mem_iUnion₂.2 ⟨N, le_rfl, hω⟩

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `θ ↦ g_T(θ)` is continuous on `Θ` when every `h(x, ·)` is. -/
theorem gm_continuousOn_sampleMoment {k q : ℕ} {X : ℕ → Ω → E} {Θ : Set (Fin k → ℝ)}
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hc : ∀ x, ContinuousOn (h x) Θ) (T : ℕ) (ω : Ω) :
    ContinuousOn (gm_sampleMoment X h T ω) Θ :=
  continuousOn_pi.2 fun i => continuousOn_const.mul
    (continuousOn_finsetSum _ fun _ _ => continuousOn_pi.1 (hc _) i)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Miao, p. 388: for compact nonempty `Θ` and continuous `h(x, ·)`, the GMM problem
`min_{θ∈Θ} Q_T(θ)` has a solution for every `T` and every sample. -/
theorem gm_exists_estimator {k q : ℕ} {X : ℕ → Ω → E} {Θ : Set (Fin k → ℝ)}
    (hΘ : IsCompact Θ) (hΘne : Θ.Nonempty) {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hc : ∀ x, ContinuousOn (h x) Θ) (WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ) :
    ∃ θh : ℕ → Ω → Fin k → ℝ, ∀ T ω, θh T ω ∈ Θ ∧
      ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ := by
  have : ∀ T ω, ∃ θ' ∈ Θ, IsMinOn (gm_objective X h WT T ω) Θ θ' := fun T ω =>
    hΘ.exists_isMinOn hΘne
      ((gm_continuous_quadForm _).comp_continuousOn (gm_continuousOn_sampleMoment hc T ω))
  choose θh hθh hmin using this
  exact ⟨θh, fun T ω => ⟨hθh T ω, fun θ hθ => hmin T ω hθ⟩⟩

omit [MeasurableSpace E] in
/-- Miao, p. 389: by global identification (Assumption 12.1.3) and `W > 0`, the population
objective `Q₀(θ) = E h' W E h` vanishes at `θ₀` and is positive elsewhere on `Θ`; so `θ₀` is its
unique minimiser. -/
theorem gm_popObjective_unique_min {k q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E}
    {h : E → (Fin k → ℝ) → Fin q → ℝ} {Θ : Set (Fin k → ℝ)} {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    (hid : Assumption_12_1_3 P X h Θ θ₀) {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef) :
    gm_popObjective P X h W θ₀ = 0 ∧ ∀ θ ∈ Θ, θ ≠ θ₀ → 0 < gm_popObjective P X h W θ := by
  refine ⟨by rw [gm_popObjective, (hid θ₀ hθ₀).2 rfl, gm_quadForm_zero], fun θ hθ hne => ?_⟩
  exact gm_quadForm_pos hW fun h0 => hne ((hid θ hθ).1 h0)

/-- Identification gap: away from `θ₀`, `Q₀` is bounded below by a positive constant. -/
theorem gm_identification_gap {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {g : (Fin k → ℝ) → Fin q → ℝ} (hg : ContinuousOn g Θ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosDef) {θ₀ : Fin k → ℝ} (hid : ∀ θ ∈ Θ, g θ = 0 ↔ θ = θ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ θ ∈ Θ, ε ≤ dist θ θ₀ → η ≤ gm_quadForm W (g θ) := by
  set K := Θ ∩ {θ | ε ≤ dist θ θ₀} with hKdef
  have hK : IsCompact K :=
    hΘ.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun θ hθ hd => ?_⟩
    have hmem : θ ∈ K := ⟨hθ, hd⟩
    rw [hKe] at hmem
    exact absurd hmem (Set.notMem_empty θ)
  · obtain ⟨θm, hθm, hmin⟩ := hK.exists_isMinOn hKne
      ((gm_continuous_quadForm W).comp_continuousOn (hg.mono Set.inter_subset_left))
    refine ⟨gm_quadForm W (g θm), gm_quadForm_pos hW ?_, fun θ hθ hd => hmin ⟨hθ, hd⟩⟩
    intro h0
    have he := (hid θm hθm.1).1 h0
    have hd : ε ≤ dist θm θ₀ := hθm.2
    rw [he, dist_self] at hd
    linarith

/-- Perturbation of a trilinear term: `|a'v'b' − awb| ≤ 3ρ(|w| + 1)(B + 1)²`. -/
theorem gm_abs_trilinear_sub {a b w a' b' v' ρ B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (ha' : |a' - a| ≤ ρ) (hb' : |b' - b| ≤ ρ) (hb : |b| ≤ B)
    (hv : |v' - w| ≤ ρ) : |a' * v' * b' - a * w * b| ≤ ρ * (3 * (|w| + 1) * (B + 1) ^ 2) := by
  have e : a' * v' * b' - a * w * b =
      (a' - a) * v' * b' + a * (v' - w) * b' + a * w * (b' - b) := by ring
  have hv1 : |v'| ≤ |w| + 1 := by
    have := abs_sub_abs_le_abs_sub v' w
    linarith
  have hb1 : |b'| ≤ B + 1 := by
    have := abs_sub_abs_le_abs_sub b' b
    linarith
  have hw := abs_nonneg w
  have t1 : |(a' - a) * v' * b'| ≤ ρ * ((|w| + 1) * (B + 1)) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul ha' (mul_le_mul hv1 hb1 (abs_nonneg _) (by positivity)) (by positivity) hρ0
  have t2 : |a * (v' - w) * b'| ≤ B * (ρ * (B + 1)) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul ha (mul_le_mul hv hb1 (abs_nonneg _) hρ0) (by positivity) hB
  have t3 : |a * w * (b' - b)| ≤ B * (|w| * ρ) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul ha (mul_le_mul le_rfl hb' (abs_nonneg _) hw) (by positivity) hB
  have hbr : (|w| + 1) * (B + 1) + B * (B + 1) + B * |w| ≤ 3 * (|w| + 1) * (B + 1) ^ 2 := by
    nlinarith [mul_nonneg hw hB, mul_nonneg hB hB, mul_nonneg (mul_nonneg hw hB) hB]
  have h3 := abs_add_three ((a' - a) * v' * b') (a * (v' - w) * b') (a * w * (b' - b))
  rw [e]
  have hfin : ρ * ((|w| + 1) * (B + 1)) + B * (ρ * (B + 1)) + B * (|w| * ρ) ≤
      ρ * (3 * (|w| + 1) * (B + 1) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hbr hρ0
    linarith
  linarith

/-- Perturbation of the quadratic form: `|G'VG − g'Wg| ≤ ρ K` with
`K = Σ_{ij} 3(|W_ij| + 1)(B + 1)²` when `|g_i| ≤ B`, `|G_i − g_i| ≤ ρ`, `|V_ij − W_ij| ≤ ρ`,
`ρ ≤ 1`. -/
theorem gm_quadForm_perturb {q : ℕ} {W V : Matrix (Fin q) (Fin q) ℝ} {g G : Fin q → ℝ}
    {ρ B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B) (hg : ∀ i, |g i| ≤ B)
    (hG : ∀ i, |G i - g i| ≤ ρ) (hV : ∀ i j, |V i j - W i j| ≤ ρ) :
    |gm_quadForm V G - gm_quadForm W g| ≤
      ρ * ∑ i, ∑ j, 3 * (|W i j| + 1) * (B + 1) ^ 2 := by
  unfold gm_quadForm
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact gm_abs_trilinear_sub hρ0 hρ1 hB (hg i) (hG i) (hG j) (hg j) (hV i j)

/-- Miao, p. 389–390 (the argmin argument behind Theorem 12.1.1, quantitative form): if `θ₀`
uniquely solves `g = 0` on compact `Θ` and `W > 0`, then for every `ε > 0` there is `ρ > 0`
such that every minimiser over `Θ` of `G'VG`, with `G` uniformly `ρ`-close to `g` on `Θ` and `V`
entrywise `ρ`-close to `W`, lies within `ε` of `θ₀`. -/
theorem gm_argmin_stable {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ)
    {g : (Fin k → ℝ) → Fin q → ℝ} (hg : ContinuousOn g Θ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosDef) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ) (hid : ∀ θ ∈ Θ, g θ = 0 ↔ θ = θ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ (G : (Fin k → ℝ) → Fin q → ℝ) (V : Matrix (Fin q) (Fin q) ℝ)
      (θh : Fin k → ℝ), (∀ θ ∈ Θ, ∀ i, |G θ i - g θ i| ≤ ρ) → (∀ i j, |V i j - W i j| ≤ ρ) →
      θh ∈ Θ → (∀ θ ∈ Θ, gm_quadForm V (G θh) ≤ gm_quadForm V (G θ)) → dist θh θ₀ < ε := by
  obtain ⟨η, hη, hgap⟩ := gm_identification_gap hΘ hg hW hid hε
  obtain ⟨C, hC⟩ := hΘ.exists_bound_of_continuousOn hg
  set B := max C 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hgB : ∀ θ ∈ Θ, ∀ i, |g θ i| ≤ B := fun θ hθ i =>
    ((norm_le_pi_norm (g θ) i).trans (hC θ hθ)).trans (le_max_left _ _)
  set K := ∑ i, ∑ j, 3 * (|W i j| + 1) * (B + 1) ^ 2 with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  set ρ := min 1 (η / (2 * (K + 1))) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρK : ρ * K < η / 2 := by
    have h1 : ρ ≤ η / (2 * (K + 1)) := min_le_right _ _
    have h2 : ρ * K ≤ η / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right h1 hK
    have h3 : η / (2 * (K + 1)) * K < η / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  refine ⟨ρ, hρ0, fun G V θh hG hV hθh hmin => ?_⟩
  by_contra hcon
  have hd : ε ≤ dist θh θ₀ := not_lt.1 hcon
  have e1 := abs_le.1 (gm_quadForm_perturb hρ0.le hρ1 hB (hgB θh hθh) (hG θh hθh) hV)
  have e0 := abs_le.1 (gm_quadForm_perturb hρ0.le hρ1 hB (hgB θ₀ hθ₀) (hG θ₀ hθ₀) hV)
  have hg0 : g θ₀ = 0 := (hid θ₀ hθ₀).2 rfl
  rw [hg0, gm_quadForm_zero] at e0
  have hgp := hgap θh hθh hd
  have hm := hmin θ₀ hθ₀
  linarith [e1.1, e0.2]

/-- The event "the sample moment is uniformly within `ρ` of the population moment on `Θ`" is
measurable (it is an intersection over a countable dense subset of `Θ`). -/
theorem gm_measurableSet_unif {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ) (hc : ∀ x, ContinuousOn (h x) Θ)
    (hgc : ContinuousOn (gm_popMoment P X h) Θ) (ρ : ℝ) (T : ℕ) :
    MeasurableSet {ω | ∀ θ ∈ Θ, ∀ i,
      |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i| ≤ ρ} := by
  obtain ⟨C, hCΘ, hCc, hΘC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Θ).exists_countable_dense_subset
  have heq : {ω | ∀ θ ∈ Θ, ∀ i,
      |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i| ≤ ρ} =
      ⋂ c ∈ C, ⋂ i, {ω | |gm_sampleMoment X h T ω c i - gm_popMoment P X h c i| ≤ ρ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun H c hc i => H c (hCΘ hc) i, fun H θ hθ i => ?_⟩
    have hφ : ContinuousOn (fun θ => |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i|) Θ :=
      ((continuousOn_pi.1 (gm_continuousOn_sampleMoment hc T ω) i).sub
        (continuousOn_pi.1 hgc i)).abs
    exact gm_le_of_mem_closure hCΘ hφ hθ (hΘC hθ) fun c hc => H c hc i
  rw [heq]
  refine MeasurableSet.biInter hCc fun c hc => MeasurableSet.iInter fun i => ?_
  refine measurableSet_le (continuous_abs.measurable.comp (Measurable.sub ?_ measurable_const))
    measurable_const
  exact measurable_const.mul (Finset.measurable_fun_sum _ fun t _ =>
    (measurable_pi_iff.1 (hm c (hCΘ hc)) i).comp (hX t))

/-- **Theorem 12.1.1** (consistency of GMM, Miao, p. 389). Under Assumptions 12.1.1 (strict
stationarity), 12.1.2 (`h(x, ·)` continuous on `Θ`, `h(·, θ)` measurable), 12.1.3 (global
identification), 12.1.4 (`W_T → W > 0` in probability), 12.1.5 (ergodicity), 12.1.6 (`Θ`
compact) and 12.1.7 (dominance), every GMM estimator `θ̂_T ∈ argmin_Θ Q_T` satisfies
`θ̂_T → θ₀` in probability. Proved from Birkhoff's theorem via the uniform law of large numbers
`gm_ulln` and the argmin argument `gm_argmin_stable`. -/
theorem theorem_12_1_1 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hid : Assumption_12_1_3 P X h Θ θ₀)
    (hdom : Assumption_12_1_7 P X h Θ)
    {WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hA4 : Assumption_12_1_4 P WT W)
    {θh : ℕ → Ω → Fin k → ℝ} (hθh : ∀ T ω, θh T ω ∈ Θ)
    (hmin : ∀ T ω, ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ) :
    TendstoInMeasure P θh atTop (fun _ => θ₀) := by
  obtain ⟨-, hW, hWT⟩ := hA4
  have hgc := gm_continuousOn_popMoment hX hm hc hdom
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨ρ, hρ, hstab⟩ := gm_argmin_stable hΘ hgc hW hθ₀ hid hε
  set U : ℕ → Set Ω := fun T => {ω | ∀ θ ∈ Θ, ∀ i,
    |gm_sampleMoment X h T ω θ i - gm_popMoment P X h θ i| ≤ ρ} with hUdef
  set V : ℕ → Fin q → Fin q → Set Ω := fun T i j => {ω | ρ ≤ dist (WT T ω i j) (W i j)}
    with hVdef
  have hsub : ∀ T, {ω | ε ≤ dist (θh T ω) θ₀} ⊆ (U T)ᶜ ∪ ⋃ i, ⋃ j, V T i j := by
    intro T ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_iUnion,
      not_exists] at hn
    obtain ⟨hU, hV⟩ := hn
    have hlt := hstab (gm_sampleMoment X h T ω) (WT T ω) (θh T ω) hU (fun i j => ?_)
      (hθh T ω) (hmin T ω)
    · exact absurd hω (not_le.2 hlt)
    · have hVij : ¬ (ρ ≤ dist (WT T ω i j) (W i j)) := hV i j
      rw [Real.dist_eq, not_le] at hVij
      exact hVij.le
  have hUlim : Tendsto (fun T => P (U T)ᶜ) atTop (𝓝 0) := by
    refine gm_tendsto_measure_of_ae_eventually
      (fun T => (gm_measurableSet_unif hX hm hc hgc ρ T).compl) ?_
    filter_upwards [gm_ulln hX hst herg hΘ hm hc hdom] with ω hω
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hω ρ hρ] with T hT
    simp only [hUdef, Set.mem_compl_iff, not_not]
    intro θ hθ i
    have hle := (dist_le_pi_dist _ _ i).trans (hT θ hθ).le
    rw [Real.dist_eq, abs_sub_comm] at hle
    exact hle
  have hVlim : ∀ i j, Tendsto (fun T => P (V T i j)) atTop (𝓝 0) := fun i j =>
    tendstoInMeasure_iff_dist.1 (hWT i j) ρ hρ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => P (U T)ᶜ + ∑ i, ∑ j, P (V T i j)) ?_ (fun _ => zero_le) (fun T => ?_)
  · have := hUlim.add (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => hVlim i j)
    simpa using this
  · calc P {ω | ε ≤ dist (θh T ω) θ₀} ≤ P ((U T)ᶜ ∪ ⋃ i, ⋃ j, V T i j) := measure_mono (hsub T)
      _ ≤ P (U T)ᶜ + P (⋃ i, ⋃ j, V T i j) := measure_union_le _ _
      _ ≤ P (U T)ᶜ + ∑ i, ∑ j, P (V T i j) := add_le_add le_rfl
          ((measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _))

/-- **Theorem 12.1.1** (strong consistency, Miao, p. 389): if moreover `W_T → W` almost surely,
then `θ̂_T → θ₀` almost surely. -/
theorem theorem_12_1_1_ae {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hid : Assumption_12_1_3 P X h Θ θ₀)
    (hdom : Assumption_12_1_7 P X h Θ)
    {WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef)
    (hWT : ∀ᵐ ω ∂P, ∀ i j, Tendsto (fun T => WT T ω i j) atTop (𝓝 (W i j)))
    {θh : ℕ → Ω → Fin k → ℝ} (hθh : ∀ T ω, θh T ω ∈ Θ)
    (hmin : ∀ T ω, ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ) :
    ∀ᵐ ω ∂P, Tendsto (fun T => θh T ω) atTop (𝓝 θ₀) := by
  have hgc := gm_continuousOn_popMoment hX hm hc hdom
  filter_upwards [gm_ulln hX hst herg hΘ hm hc hdom, hWT] with ω hω hWω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hstab⟩ := gm_argmin_stable hΘ hgc hW hθ₀ hid hε
  have hev1 := Metric.tendstoUniformlyOn_iff.1 hω ρ hρ
  have hev2 : ∀ᶠ T in atTop, ∀ i j, dist (WT T ω i j) (W i j) < ρ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Metric.tendsto_nhds.1 (hWω i j) ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨N, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hN T hT
  refine hstab (gm_sampleMoment X h T ω) (WT T ω) (θh T ω) (fun θ hθ i => ?_)
    (fun i j => ?_) (hθh T ω) (hmin T ω)
  · have hle := (dist_le_pi_dist _ _ i).trans (h1 θ hθ).le
    rw [Real.dist_eq, abs_sub_comm] at hle
    exact hle
  · have := h2 i j
    rw [Real.dist_eq] at this
    exact this.le

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The deterministic algebra of GMM (Miao, §12.1, pp. 388–395)

Miao, pp. 388–395. Everything here is exact (finite-sample) algebra and calculus.

* `gm_foc_line`, `eq_12_2` — the first-order condition (12.2) `(∂g_T/∂θ)' W_T g_T(θ̂_T) = 0` at
  an interior minimiser, for symmetric `W_T` (only partial derivatives are needed).
* `eq_12_3_counterexample` — the mean value form (12.3) with a single `θ̄_T` is false for
  vector-valued `g` (`g(θ) = (cos θ, sin θ)` on `[0, 2π]`); `eq_12_3` proves the correct
  row-by-row version (a separate `θ̄_{T,i}` on the segment for each moment `i`).
* `gm_linearization` — the step after (12.3): from the first-order condition and the expansion,
  `θ̂_T − θ₀ = −M_T g_T(θ₀)` with `M_T = (Ĝ'W_TḠ)⁻¹Ĝ'W_T`, hence
  `√T(θ̂_T − θ₀) = −M_T √T g_T(θ₀)` (`gm_linearization_sqrt`).
* `gm_M`, `gm_M_mul`, `gm_asymVar_eq` — `M = (G₀'WG₀)⁻¹G₀'W` (Theorem 12.1.2) and
  `MSM' = (G₀'WG₀)⁻¹G₀'WSWG₀(G₀'WG₀)⁻¹`.
* `gm_efficient_var` — with `W = S⁻¹`, `MSM' = (G₀'S⁻¹G₀)⁻¹` (p. 392);
  `gm_efficiency` — `(G'WG)⁻¹G'WSWG(G'WG)⁻¹ − (G'S⁻¹G)⁻¹` is positive semidefinite for every
  positive definite `W` (efficient GMM, the Loewner order).
* `gm_proj_*`, `eq_12_4_algebra` — the J statistic (12.4): with `S = CC'` and `H = C⁻¹G`,
  `P = H(H'H)⁻¹H'` is a symmetric idempotent of trace `k`, `I − P` one of trace `q − k`, and the
  residual moment `ĝ = (I − G(G'S⁻¹G)⁻¹G'S⁻¹)g₀` satisfies `ĝ'S⁻¹ĝ = z'(I − P)z`, `z = C⁻¹g₀`.
* `gm_linear_*`, `gm_exactly_identified`, `gm_nls_foc` — "for linear models, these conditions
  could be solved to obtain a closed-form solution" (p. 388) and the OLS / IV / NLS moment
  conditions of p. 395.
-/

namespace Miao.StructuralEstimation

open Filter Topology

/-! ### The first-order condition (12.2) -/

/-- The Jacobian matrix `(∂g_i/∂θ_j)` of a family of row derivatives `Dg i`. -/
noncomputable def gm_jacobian {k q : ℕ} (Dg : Fin q → (Fin k → ℝ) →L[ℝ] ℝ) :
    Matrix (Fin q) (Fin k) ℝ :=
  Matrix.of fun i j => Dg i (Pi.single j 1)

/-- A continuous linear functional on `ℝ^k` in coordinates: `L d = Σ_j L(e_j) d_j`. -/
theorem gm_clm_apply_eq_sum {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (d : Fin k → ℝ) :
    L d = ∑ j, L (Pi.single j 1) * d j := by
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (d j) : Fin k → ℝ) = d j • Pi.single j 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- Miao, (12.2), p. 388, along a line: if `t ↦ v(t)'Wv(t)` has a local minimum at `0`, `W` is
symmetric and `v'(0) = G`, then `G'Wv(0) = 0`. -/
theorem gm_foc_line {q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.IsSymm)
    {v : ℝ → Fin q → ℝ} {G : Fin q → ℝ} (hv : ∀ i, HasDerivAt (fun t => v t i) (G i) 0)
    (hmin : IsLocalMin (fun t => gm_quadForm W (v t)) 0) :
    G ⬝ᵥ W.mulVec (v 0) = 0 := by
  have hD : HasDerivAt (fun t => gm_quadForm W (v t))
      (∑ i, ∑ j, (G i * W i j * v 0 j + v 0 i * W i j * G j)) 0 := by
    unfold gm_quadForm
    exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      ((hv i).mul_const (W i j)).mul (hv j)
  have h0 := hmin.hasDerivAt_eq_zero hD
  have hs : ∑ i, ∑ j, v 0 i * W i j * G j = ∑ i, ∑ j, G i * W i j * v 0 j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hW.apply i j]
    ring
  simp only [Finset.sum_add_distrib, hs] at h0
  have he : G ⬝ᵥ W.mulVec (v 0) = ∑ i, ∑ j, G i * W i j * v 0 j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [he]
  linarith

/-- **(12.2)** (first-order conditions, Miao, p. 388). If `θ̂` is a local (e.g. interior)
minimiser of `Q(θ) = g(θ)'Wg(θ)`, `W` is symmetric and each `g_i` is differentiable at `θ̂`, then
`(∂g/∂θ(θ̂))' W g(θ̂) = 0`. -/
theorem eq_12_2 {k q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.IsSymm)
    {g : (Fin k → ℝ) → Fin q → ℝ} {Dg : Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θh : Fin k → ℝ}
    (hd : ∀ i, HasFDerivAt (fun θ => g θ i) (Dg i) θh)
    (hmin : IsLocalMin (fun θ => gm_quadForm W (g θ)) θh) :
    (gm_jacobian Dg).transpose.mulVec (W.mulVec (g θh)) = 0 := by
  funext j
  set e : Fin k → ℝ := Pi.single j 1 with he
  have hl : HasDerivAt (fun t : ℝ => θh + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add θh
  have hline : ∀ i, HasDerivAt (fun t : ℝ => g (θh + t • e) i) (Dg i e) 0 := fun i =>
    (hd i).comp_hasDerivAt_of_eq 0 hl (by simp)
  have hmin' : IsLocalMin (fun θ => gm_quadForm W (g θ)) (θh + (0 : ℝ) • e) := by
    simpa using hmin
  have hlm := hmin'.comp_continuous (g := fun t : ℝ => θh + t • e) (by fun_prop)
  have h := gm_foc_line hW hline hlm
  simp only [zero_smul, add_zero] at h
  rw [Matrix.mulVec_transpose]
  simpa [Matrix.vecMul, dotProduct, gm_jacobian, he, mul_comm] using h

/-! ### The mean value expansion (12.3) -/

/-- Miao, (12.3), p. 390: the single-`θ̄` mean value form is **false** for vector-valued moments.
For `g(θ) = (cos θ, sin θ)` (with derivative `(−sin θ, cos θ)`, `gm_circle_hasDerivAt`),
`θ₀ = 0`, `θ̂ = 2π`, no `θ̄ = λθ₀ + (1 − λ)θ̂`, `λ ∈ [0, 1]`, satisfies
`g(θ̂) = g(θ₀) + ∂g(θ̄)(θ̂ − θ₀)`. -/
theorem eq_12_3_counterexample : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ¬ (![Real.cos (2 * Real.pi), Real.sin (2 * Real.pi)] =
      ![Real.cos 0, Real.sin 0] + (2 * Real.pi - 0) •
        ![-Real.sin (lam * 0 + (1 - lam) * (2 * Real.pi)),
          Real.cos (lam * 0 + (1 - lam) * (2 * Real.pi))]) := by
  intro lam _ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero, mul_zero,
    zero_add, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at h0 h1
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  set θb := (1 - lam) * (2 * Real.pi)
  have hs : Real.sin θb = 0 := by
    have : 2 * Real.pi * -Real.sin θb = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hpi
    · linarith
  have hc : Real.cos θb = 0 := by
    have : 2 * Real.pi * Real.cos θb = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hpi
    · exact h'
  have := Real.sin_sq_add_cos_sq θb
  rw [hs, hc] at this
  norm_num at this

/-- The derivative used in `eq_12_3_counterexample`: `(cos θ, sin θ)' = (−sin θ, cos θ)`. -/
theorem gm_circle_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t => ![Real.cos t, Real.sin t]) ![-Real.sin θ, Real.cos θ] θ := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa using Real.hasDerivAt_cos θ
  · simpa using Real.hasDerivAt_sin θ

/-- **(12.3)** corrected (row-wise mean value theorem, Miao, p. 390). If each `g_i` is
differentiable on the segment `[θ₀, θ̂]`, then for each moment `i` there is a point
`θ̄_i = θ₀ + s_i(θ̂ − θ₀)`, `s_i ∈ (0, 1)`, with
`g_i(θ̂) = g_i(θ₀) + Σ_j ∂g_i/∂θ_j(θ̄_i) (θ̂ − θ₀)_j`. (The book's `θ̄_T = λθ₀ + (1 − λ)θ̂_T` is
`s = 1 − λ`.) -/
theorem eq_12_3 {k q : ℕ} {g : (Fin k → ℝ) → Fin q → ℝ}
    {Dg : (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θ₀ θh : Fin k → ℝ}
    (hd : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt (fun θ => g θ i) (Dg (θ₀ + s • (θh - θ₀)) i) (θ₀ + s • (θh - θ₀)))
    (i : Fin q) :
    ∃ s ∈ Set.Ioo (0 : ℝ) 1, g θh i = g θ₀ i +
      ∑ j, gm_jacobian (Dg (θ₀ + s • (θh - θ₀))) i j * (θh - θ₀) j := by
  set φ : ℝ → ℝ := fun s => g (θ₀ + s • (θh - θ₀)) i with hφdef
  have hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (Dg (θ₀ + s • (θh - θ₀)) i (θh - θ₀)) s := by
    intro s hs
    have h1 : HasDerivAt (fun t : ℝ => θ₀ + t • (θh - θ₀)) (θh - θ₀) s := by
      simpa using ((hasDerivAt_id s).smul_const (θh - θ₀)).const_add θ₀
    exact (hd i s hs).comp_hasDerivAt_of_eq s h1 rfl
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope φ
    (fun s => Dg (θ₀ + s • (θh - θ₀)) i (θh - θ₀)) zero_lt_one
    (fun s hs => (hφ s hs).continuousAt.continuousWithinAt)
    (fun s hs => hφ s (Set.Ioo_subset_Icc_self hs))
  refine ⟨c, hc, ?_⟩
  simp only [hφdef, one_smul, zero_smul, add_zero, add_sub_cancel, sub_zero, div_one] at hceq
  have hsum : ∑ j, gm_jacobian (Dg (θ₀ + c • (θh - θ₀))) i j * (θh - θ₀) j =
      Dg (θ₀ + c • (θh - θ₀)) i (θh - θ₀) := by
    rw [gm_clm_apply_eq_sum]
    rfl
  rw [hsum, hceq]
  ring

/-! ### The linearisation and the asymptotic variance -/

/-- Miao, p. 390: from the first-order condition `Ĝ'V g(θ̂) = 0` and the expansion
`g(θ̂) = g(θ₀) + Ḡ(θ̂ − θ₀)`, if `Ĝ'VḠ` is invertible then
`θ̂ − θ₀ = −(Ĝ'VḠ)⁻¹Ĝ'V g(θ₀)`. -/
theorem gm_linearization {k q : ℕ} {A B : Matrix (Fin q) (Fin k) ℝ}
    {V : Matrix (Fin q) (Fin q) ℝ} {g₀ g₁ : Fin q → ℝ} {d : Fin k → ℝ}
    (hfoc : A.transpose.mulVec (V.mulVec g₁) = 0) (hexp : g₁ = g₀ + B.mulVec d)
    (hinv : IsUnit (A.transpose * V * B).det) :
    d = -(((A.transpose * V * B)⁻¹ * A.transpose * V).mulVec g₀) := by
  have h1 : (A.transpose * V * B).mulVec d = -((A.transpose * V).mulVec g₀) := by
    rw [hexp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at hfoc
    exact eq_neg_of_add_eq_zero_right hfoc
  calc d = ((A.transpose * V * B)⁻¹ * (A.transpose * V * B)).mulVec d := by
        rw [Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]
    _ = (A.transpose * V * B)⁻¹.mulVec ((A.transpose * V * B).mulVec d) := by
        rw [Matrix.mulVec_mulVec]
    _ = _ := by
        rw [h1, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]

/-- Miao, p. 390: `√T(θ̂_T − θ₀) = −M_T √T g_T(θ₀)`, `M_T = (Ĝ'W_TḠ)⁻¹Ĝ'W_T`. -/
theorem gm_linearization_sqrt {k q : ℕ} {A B : Matrix (Fin q) (Fin k) ℝ}
    {V : Matrix (Fin q) (Fin q) ℝ} {g₀ g₁ : Fin q → ℝ} {d : Fin k → ℝ}
    (hfoc : A.transpose.mulVec (V.mulVec g₁) = 0) (hexp : g₁ = g₀ + B.mulVec d)
    (hinv : IsUnit (A.transpose * V * B).det) (c : ℝ) :
    c • d = -(((A.transpose * V * B)⁻¹ * A.transpose * V).mulVec (c • g₀)) := by
  rw [gm_linearization hfoc hexp hinv, Matrix.mulVec_smul, smul_neg]

/-- Miao, Theorem 12.1.2 (p. 391): `M = (G₀'WG₀)⁻¹G₀'W`. -/
noncomputable def gm_M {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) (W : Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin k) (Fin q) ℝ :=
  (G.transpose * W * G)⁻¹ * G.transpose * W

/-- `MG₀ = I` when `G₀'WG₀` is invertible. -/
theorem gm_M_mul {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hinv : IsUnit (G.transpose * W * G).det) : gm_M G W * G = 1 := by
  rw [gm_M, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc G.transpose,
    Matrix.nonsing_inv_mul _ hinv]

/-- Miao, p. 391 (rank condition): if `W > 0` and `G₀` has full column rank (`G₀x = 0 ⇒ x = 0`)
then `G₀'WG₀` is positive definite, hence invertible. -/
theorem gm_posDef_GWG {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosDef) (hG : Function.Injective G.mulVec) :
    (G.transpose * W * G).PosDef := by
  have := hW.conjTranspose_mul_mul_same hG
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem gm_isUnit_det_GWG {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ}
    {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef) (hG : Function.Injective G.mulVec) :
    IsUnit (G.transpose * W * G).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (gm_posDef_GWG hW hG).isUnit

/-- `G'WG` is symmetric when `W` is. -/
theorem gm_isSymm_GWG {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.IsSymm) : (G.transpose * W * G).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hW.eq,
    Matrix.mul_assoc]

/-- The inverse of a symmetric matrix is symmetric. -/
theorem gm_inv_transpose_of_isSymm {k : ℕ} {N : Matrix (Fin k) (Fin k) ℝ} (hN : N.IsSymm) :
    (N⁻¹).transpose = N⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hN.eq]

/-- `M' = WG₀(G₀'WG₀)⁻¹` for symmetric `W`. -/
theorem gm_M_transpose {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.IsSymm) : (gm_M G W).transpose = W * G * (G.transpose * W * G)⁻¹ := by
  rw [gm_M, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hW.eq,
    gm_inv_transpose_of_isSymm (gm_isSymm_GWG G hW)]
  simp only [Matrix.mul_assoc]

/-- Miao, Theorem 12.1.2 (p. 391): the asymptotic variance
`MSM' = (G₀'WG₀)⁻¹G₀'WSWG₀(G₀'WG₀)⁻¹`. -/
theorem gm_asymVar_eq {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.IsSymm) (S : Matrix (Fin q) (Fin q) ℝ) :
    gm_M G W * S * (gm_M G W).transpose =
      (G.transpose * W * G)⁻¹ * (G.transpose * W * S * W * G) * (G.transpose * W * G)⁻¹ := by
  rw [gm_M_transpose G hW, gm_M]
  simp only [Matrix.mul_assoc]

/-- Miao, p. 392: with the optimal weighting matrix `W = S⁻¹`,
`MSM' = (G₀'S⁻¹G₀)⁻¹`. -/
theorem gm_efficient_var {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ)
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosDef)
    (hinv : IsUnit (G.transpose * S⁻¹ * G).det) :
    gm_M G S⁻¹ * S * (gm_M G S⁻¹).transpose = (G.transpose * S⁻¹ * G)⁻¹ := by
  have hSi : S⁻¹.IsSymm := hS.inv.isHermitian.isSymm
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  rw [gm_asymVar_eq G hSi S]
  have h1 : G.transpose * S⁻¹ * S * S⁻¹ * G = G.transpose * S⁻¹ * G := by
    rw [Matrix.mul_assoc (G.transpose * S⁻¹) S, Matrix.mul_nonsing_inv _ hSdet, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv, Matrix.mul_one]

/-- **Efficient GMM** (Miao, p. 392). For every positive definite `W`, positive definite `S` and
full-column-rank `G`, the asymptotic variance with weighting matrix `W` exceeds the one with
`W = S⁻¹` in the Loewner order:
`(G'WG)⁻¹G'WSWG(G'WG)⁻¹ − (G'S⁻¹G)⁻¹` is positive semidefinite. -/
theorem gm_efficiency {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ} (hG : Function.Injective G.mulVec)
    {W S : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef) (hS : S.PosDef) :
    (gm_M G W * S * (gm_M G W).transpose - (G.transpose * S⁻¹ * G)⁻¹).PosSemidef := by
  set A := gm_M G W with hA
  set B := gm_M G S⁻¹ with hB
  set I := (G.transpose * S⁻¹ * G)⁻¹ with hI
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  have hSs : S.IsSymm := hS.isHermitian.isSymm
  have hSi : S⁻¹.IsSymm := hS.inv.isHermitian.isSymm
  have hWinv := gm_isUnit_det_GWG hW hG
  have hNinv := gm_isUnit_det_GWG hS.inv hG
  have hIs : I.transpose = I := gm_inv_transpose_of_isSymm (gm_isSymm_GWG G hSi)
  have hAG : A * G = 1 := gm_M_mul hWinv
  have hBG : B * G = 1 := gm_M_mul hNinv
  have hBS : B * S = I * G.transpose := by
    rw [hB, gm_M, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSdet, Matrix.mul_one]
  have hBSB : B * S * B.transpose = I := by
    rw [hBS, Matrix.mul_assoc, ← Matrix.transpose_mul, hBG, Matrix.transpose_one,
      Matrix.mul_one]
  have hBSA : B * S * A.transpose = I := by
    rw [hBS, Matrix.mul_assoc, ← Matrix.transpose_mul, hAG, Matrix.transpose_one,
      Matrix.mul_one]
  have hASB : A * S * B.transpose = I := by
    have : S * B.transpose = (B * S).transpose := by
      rw [Matrix.transpose_mul, hSs.eq]
    rw [Matrix.mul_assoc, this, hBS, Matrix.transpose_mul, Matrix.transpose_transpose, hIs,
      ← Matrix.mul_assoc, hAG, Matrix.one_mul]
  have key : (A - B) * S * (A - B).transpose = A * S * A.transpose - I := by
    simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    rw [hBSB, hBSA, hASB]
    abel
  rw [← key]
  have := hS.posSemidef.mul_mul_conjTranspose_same (A - B)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-! ### The J statistic (12.4) -/

/-- Miao, (12.4), p. 394: `J_T = T g_T(θ̂_T)' Ŝ_T⁻¹ g_T(θ̂_T)` (the book prints `Ŝ_T`; the
weighting by the inverse is Hansen's statistic). -/
noncomputable def gm_J {q : ℕ} (T : ℕ) (g : Fin q → ℝ) (S : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  T * (g ⬝ᵥ S⁻¹.mulVec g)

/-- The orthogonal projection `P = H(H'H)⁻¹H'` onto the columns of `H`. -/
noncomputable def gm_proj {q k : ℕ} (H : Matrix (Fin q) (Fin k) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  H * (H.transpose * H)⁻¹ * H.transpose

theorem gm_proj_transpose {q k : ℕ} (H : Matrix (Fin q) (Fin k) ℝ) :
    (gm_proj H).transpose = gm_proj H := by
  have hs : (H.transpose * H).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [gm_proj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    gm_inv_transpose_of_isSymm hs, Matrix.mul_assoc]

theorem gm_proj_mul_self {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) : gm_proj H * H = H := by
  rw [gm_proj, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]

/-- `P` is idempotent. -/
theorem gm_proj_idem {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) : gm_proj H * gm_proj H = gm_proj H := by
  simp only [gm_proj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc H.transpose H, ← Matrix.mul_assoc (H.transpose * H)⁻¹,
    Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

/-- `tr P = k`. -/
theorem gm_proj_trace {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) : (gm_proj H).trace = k := by
  rw [gm_proj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h,
    Matrix.trace_one, Fintype.card_fin]

/-- `I − P` is a symmetric idempotent of trace `q − k` (the degrees of freedom of the J test). -/
theorem gm_resid_proj {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) :
    (1 - gm_proj H).transpose = 1 - gm_proj H ∧
      (1 - gm_proj H) * (1 - gm_proj H) = 1 - gm_proj H ∧
      (1 - gm_proj H).trace = (q : ℝ) - k ∧ (1 - gm_proj H) * H = 0 := by
  refine ⟨by rw [Matrix.transpose_sub, Matrix.transpose_one, gm_proj_transpose], ?_, ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, gm_proj_idem h, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
    abel
  · rw [Matrix.trace_sub, Matrix.trace_one, gm_proj_trace h, Fintype.card_fin]
  · rw [Matrix.sub_mul, gm_proj_mul_self h, Matrix.one_mul, sub_self]

/-- Miao, (12.4), p. 394, the algebra behind `J_T → χ²(q − k)`: write `S = CC'` (for
positive definite `S`, e.g. Cholesky; the identity holds for any `C`) and `H = C⁻¹G`.
The efficient-GMM residual moment `ĝ = (I − G(G'S⁻¹G)⁻¹G'S⁻¹)g₀`
satisfies `ĝ'S⁻¹ĝ = z'(I − P)z` with `z = C⁻¹g₀` and `P = H(H'H)⁻¹H'` (so that, when
`√T z →d N(0, I)`, `J_T` is asymptotically a quadratic form in a symmetric idempotent of rank
`q − k`, `gm_resid_proj`). -/
theorem eq_12_4_algebra {q k : ℕ} {G : Matrix (Fin q) (Fin k) ℝ}
    {S C : Matrix (Fin q) (Fin q) ℝ} (hSC : S = C * C.transpose)
    (g₀ : Fin q → ℝ) :
    let ĝ := (1 - G * (G.transpose * S⁻¹ * G)⁻¹ * G.transpose * S⁻¹).mulVec g₀
    ĝ ⬝ᵥ S⁻¹.mulVec ĝ =
      C⁻¹.mulVec g₀ ⬝ᵥ (1 - gm_proj (C⁻¹ * G)).mulVec (C⁻¹.mulVec g₀) := by
  intro ĝ
  have hSinv : S⁻¹ = C⁻¹.transpose * C⁻¹ := by
    rw [hSC, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  have hN : G.transpose * S⁻¹ * G = (C⁻¹ * G).transpose * (C⁻¹ * G) := by
    rw [hSinv, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hmat : C⁻¹ * (1 - G * (G.transpose * S⁻¹ * G)⁻¹ * G.transpose * S⁻¹) =
      (1 - gm_proj (C⁻¹ * G)) * C⁻¹ := by
    rw [hN, gm_proj, hSinv, Matrix.transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have hz : C⁻¹.mulVec ĝ = (1 - gm_proj (C⁻¹ * G)).mulVec (C⁻¹.mulVec g₀) := by
    simp only [ĝ, Matrix.mulVec_mulVec, hmat]
  have hdot : ĝ ⬝ᵥ S⁻¹.mulVec ĝ = C⁻¹.mulVec ĝ ⬝ᵥ C⁻¹.mulVec ĝ := by
    rw [hSinv, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hdot, hz]
  set R := 1 - gm_proj (C⁻¹ * G)
  set z := C⁻¹.mulVec g₀
  have hRt : R.transpose = R := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, gm_proj_transpose]
  have hRR : R * R = R := by
    change (1 - gm_proj (C⁻¹ * G)) * (1 - gm_proj (C⁻¹ * G)) = 1 - gm_proj (C⁻¹ * G)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul]
    have hP : gm_proj (C⁻¹ * G) * gm_proj (C⁻¹ * G) = gm_proj (C⁻¹ * G) := by
      by_cases hd : IsUnit ((C⁻¹ * G).transpose * (C⁻¹ * G)).det
      · exact gm_proj_idem hd
      · have h0 : gm_proj (C⁻¹ * G) = 0 := by
          simp only [gm_proj, Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.mul_zero,
            Matrix.zero_mul]
        rw [h0, Matrix.zero_mul]
    rw [hP]
    abel
  clear_value R z
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRt, Matrix.mulVec_mulVec, hRR,
    dotProduct_comm]

/-! ### Linear models, OLS, IV and NLS (pp. 388, 395) -/

/-- Miao, p. 388 and p. 395 (OLS / IV): for the linear moment `h_t(β) = z_t(y_t − x_t'β)`,
`g_T(β) = b − Aβ` with `A = (1/T) Σ z_t x_t'` and `b = (1/T) Σ z_t y_t`. -/
theorem gm_linear_sampleMoment {q k : ℕ} (z : ℕ → Fin q → ℝ) (x : ℕ → Fin k → ℝ) (y : ℕ → ℝ)
    (T : ℕ) (β : Fin k → ℝ) :
    (fun i => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, z t i * (y t - x t ⬝ᵥ β)) =
      (fun i => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, z t i * y t) -
        (Matrix.of fun i j => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, z t i * x t j).mulVec β := by
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Miao, p. 388 ("for linear models, these conditions could be solved to obtain a closed-form
solution"): with `g(β) = b − Aβ`, symmetric `W` and invertible `A'WA`, the first-order
condition `A'W(b − Aβ) = 0` holds iff `β = (A'WA)⁻¹A'Wb` (linear GMM; 2SLS for `W` the inverse
instrument moment matrix). -/
theorem gm_linear_foc_iff {q k : ℕ} {A : Matrix (Fin q) (Fin k) ℝ}
    {W : Matrix (Fin q) (Fin q) ℝ} (hinv : IsUnit (A.transpose * W * A).det)
    (b : Fin q → ℝ) (β : Fin k → ℝ) :
    A.transpose.mulVec (W.mulVec (b - A.mulVec β)) = 0 ↔
      β = ((A.transpose * W * A)⁻¹ * A.transpose * W).mulVec b := by
  constructor
  · intro hfoc
    have h := gm_linearization (B := A) (g₀ := b) (d := -β) hfoc
      (by rw [Matrix.mulVec_neg, sub_eq_add_neg]) hinv
    exact neg_inj.1 h
  · intro hβ
    have hM : A.transpose * W * A * (A.transpose * W * A)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hinv
    rw [hβ]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hM, Matrix.one_mul,
      sub_self]

/-- Miao, p. 388: for positive semidefinite `W`, any `β*` satisfying the first-order condition
minimises the linear GMM objective `Q(β) = (b − Aβ)'W(b − Aβ)`. -/
theorem gm_linear_min {q k : ℕ} {A : Matrix (Fin q) (Fin k) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosSemidef) {b : Fin q → ℝ} {βs : Fin k → ℝ}
    (hfoc : A.transpose.mulVec (W.mulVec (b - A.mulVec βs)) = 0) (β : Fin k → ℝ) :
    gm_quadForm W (b - A.mulVec βs) ≤ gm_quadForm W (b - A.mulVec β) := by
  have hWs : W.IsSymm := hW.isHermitian.isSymm
  set r := b - A.mulVec βs with hr
  set u := A.mulVec (β - βs) with hu
  have hb : b - A.mulVec β = r - u := by
    simp only [r, u, Matrix.mulVec_sub]
    abel
  clear_value r u
  have hur : u ⬝ᵥ W.mulVec r = 0 := by
    rw [hu, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hfoc,
      zero_dotProduct]
  have hru : r ⬝ᵥ W.mulVec u = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hWs.eq, dotProduct_comm, hur]
  have hpsd := hW.dotProduct_mulVec_nonneg u
  simp only [star_trivial] at hpsd
  rw [hb, gm_quadForm_eq, gm_quadForm_eq, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, hur, hru]
  linarith

/-- Miao, p. 395 (OLS and exactly identified IV, `q = k`): if `A` and `W` are invertible the
GMM solution `(A'WA)⁻¹A'Wb = A⁻¹b` does not depend on `W`. -/
theorem gm_exactly_identified {k : ℕ} {A W : Matrix (Fin k) (Fin k) ℝ} (hA : IsUnit A.det)
    (hW : IsUnit W.det) : (A.transpose * W * A)⁻¹ * A.transpose * W = A⁻¹ := by
  have hAt : IsUnit A.transpose.det := by rwa [Matrix.det_transpose]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc W⁻¹, ← Matrix.mul_assoc A.transpose⁻¹, Matrix.nonsing_inv_mul _ hAt,
    Matrix.one_mul, Matrix.nonsing_inv_mul _ hW, Matrix.mul_one]

/-- Miao, p. 395 (NLS): at a local minimiser `β̂` of the sum of squared residuals
`Σ_t (y_t − m_t(β))²`, the NLS moment condition `Σ_t m_t'(β̂)(y_t − m_t(β̂)) = 0` holds. -/
theorem gm_nls_foc {T : ℕ} {m : ℕ → ℝ → ℝ} {m' : ℕ → ℝ} {y : ℕ → ℝ} {βh : ℝ}
    (hd : ∀ t, HasDerivAt (m t) (m' t) βh)
    (hmin : IsLocalMin (fun β => ∑ t ∈ Finset.range T, (y t - m t β) ^ 2) βh) :
    ∑ t ∈ Finset.range T, m' t * (y t - m t βh) = 0 := by
  have hD : HasDerivAt (fun β => ∑ t ∈ Finset.range T, (y t - m t β) ^ 2)
      (∑ t ∈ Finset.range T, 2 * (y t - m t βh) * (-m' t)) βh :=
    HasDerivAt.fun_sum fun t _ => by
      simpa using ((hasDerivAt_const βh (y t)).fun_sub (hd t)).fun_pow 2
  have h0 := hmin.hasDerivAt_eq_zero hD
  have : ∑ t ∈ Finset.range T, 2 * (y t - m t βh) * (-m' t) =
      -2 * ∑ t ∈ Finset.range T, m' t * (y t - m t βh) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [this] at h0
  linarith

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Probability tools for the asymptotics of GMM (Miao, §12.1, pp. 390–392)

Tools used for Lemma 12.1.1 and Theorem 12.1.2 (Miao, pp. 390–392), on top of Mathlib's
convergence in probability (`TendstoInMeasure`), convergence in distribution
(`TendstoInDistribution`, with Slutsky's theorem and the continuous mapping theorem) and the
multivariate normal law `multivariateGaussian μ S` on `EuclideanSpace ℝ (Fin q)`.

* `gm_toE`, `gm_matE`: vectors of `ℝ^q` as points of the Euclidean space, and the linear map
  `z ↦ Mz` of a `k × q` matrix.
* `gm_map_multivariateGaussian`: if `Z ~ N(0, S)` then `MZ ~ N(0, MSM')` (characteristic
  functions).
* `gm_tendstoInMeasure_comp`: the continuous mapping theorem for convergence in probability to a
  constant; `gm_tendstoInMeasure_pi`, `gm_tendstoInMeasure_apply`, `gm_tendstoInMeasure_prod`:
  convergence in probability of vectors, matrices and pairs, coordinatewise.
* `gm_tendstoInMeasure_mul`, `gm_tendstoInMeasure_matE`: if `Z_T → Z` in distribution and
  `D_T → 0` in probability then `D_T Z_T → 0` in probability (tightness via the portmanteau
  theorem); no measurability of `D_T` is required.
* `gm_continuousAt_inv`: matrix inversion is continuous at an invertible matrix.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- A vector of `ℝ^q` as a point of the Euclidean space `EuclideanSpace ℝ (Fin q)`. -/
def gm_toE {q : ℕ} (v : Fin q → ℝ) : EuclideanSpace ℝ (Fin q) := WithLp.toLp 2 v

/-- The linear map `z ↦ Mz` of a `k × q` matrix between Euclidean spaces. -/
def gm_matE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (z : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (M.mulVec z.ofLp)

theorem gm_continuous_toE (q : ℕ) : Continuous (gm_toE (q := q)) :=
  PiLp.continuous_toLp 2 _

theorem gm_continuous_matE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) :
    Continuous (gm_matE M) :=
  (PiLp.continuous_toLp 2 _).comp
    (Continuous.matrix_mulVec continuous_const (PiLp.continuous_ofLp 2 _))

theorem gm_matE_toE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (v : Fin q → ℝ) :
    gm_matE M (gm_toE v) = gm_toE (M.mulVec v) := rfl

/-- `⟪Mz, t⟫ = ⟪z, M't⟫`. -/
theorem gm_inner_matE {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (z : EuclideanSpace ℝ (Fin q))
    (t : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (gm_matE M z) t = inner ℝ z (gm_matE M.transpose t) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, gm_matE, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **Linear images of normal vectors** (used in Theorem 12.1.2, Miao, p. 391): if `Z ~ N(0, S)`
with `S` positive semidefinite, then `MZ ~ N(0, MSM')`. -/
theorem gm_map_multivariateGaussian {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ)
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (gm_matE M) =
      multivariateGaussian 0 (M * S * M.transpose) := by
  have hS' : (M * S * M.transpose).PosSemidef := by
    have := hS.mul_mul_conjTranspose_same M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hm : Measurable (gm_matE M) := (gm_continuous_matE M).measurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [gm_inner_matE]
  rw [← charFun_apply, charFun_multivariateGaussian hS, charFun_multivariateGaussian hS']
  have key : (M.transpose.mulVec t.ofLp) ⬝ᵥ S.mulVec (M.transpose.mulVec t.ofLp) =
      t.ofLp ⬝ᵥ (M * S * M.transpose).mulVec t.ofLp := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec t.ofLp M,
      ← Matrix.mulVec_transpose]
  simp only [gm_matE, WithLp.ofLp_toLp, key, inner_zero_right]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous mapping theorem for convergence in probability to a constant. -/
theorem gm_tendstoInMeasure_comp {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {P : Measure Ω} {Y : ℕ → Ω → α} {c : α} (hY : TendstoInMeasure P Y atTop (fun _ => c))
    {f : α → β} (hf : ContinuousAt f c) :
    TendstoInMeasure P (fun T ω => f (Y T ω)) atTop (fun _ => f c) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY δ hδ)
    (fun _ => zero_le) fun T => measure_mono fun ω hω => ?_
  by_contra hn
  exact absurd hω (not_le.2 (hfδ (not_le.1 hn)))

/-- Coordinatewise convergence in probability gives convergence in probability of the vector. -/
theorem gm_tendstoInMeasure_pi {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, PseudoMetricSpace (β i)] {P : Measure Ω} {Y : ℕ → Ω → ∀ i, β i} {c : ∀ i, β i}
    (h : ∀ i, TendstoInMeasure P (fun T ω => Y T ω i) atTop (fun _ => c i)) :
    TendstoInMeasure P Y atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hi := fun i => tendstoInMeasure_iff_dist.1 (h i) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => ∑ i, P {ω | ε ≤ dist (Y T ω i) (c i)}) ?_ (fun _ => zero_le) fun T => ?_
  · simpa using tendsto_finsetSum Finset.univ fun i _ => hi i
  · refine (measure_mono fun ω hω => ?_).trans (measure_iUnion_fintype_le P _)
    simp only [Set.mem_iUnion]
    by_contra hn
    push Not at hn
    exact absurd hω (not_le.2 ((dist_pi_lt_iff hε).2 fun i => not_le.1 (hn i)))

/-- A coordinate of a vector converging in probability converges in probability. -/
theorem gm_tendstoInMeasure_apply {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, PseudoMetricSpace (β i)] {P : Measure Ω} {Y : ℕ → Ω → ∀ i, β i} {c : ∀ i, β i}
    (h : TendstoInMeasure P Y atTop (fun _ => c)) (i : ι) :
    TendstoInMeasure P (fun T ω => Y T ω i) atTop (fun _ => c i) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) fun T => measure_mono fun ω hω => le_trans hω (dist_le_pi_dist _ _ i)

/-- Convergence in probability of a pair from its components. -/
theorem gm_tendstoInMeasure_prod {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {P : Measure Ω} {Y : ℕ → Ω → α} {Y' : ℕ → Ω → β} {c : α} {c' : β}
    (h : TendstoInMeasure P Y atTop (fun _ => c)) (h' : TendstoInMeasure P Y' atTop (fun _ => c')) :
    TendstoInMeasure P (fun T ω => (Y T ω, Y' T ω)) atTop (fun _ => (c, c')) := by
  rw [tendstoInMeasure_iff_dist] at h h' ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => P {ω | ε ≤ dist (Y T ω) c} + P {ω | ε ≤ dist (Y' T ω) c'}) ?_
    (fun _ => zero_le) fun T => ?_
  · simpa using (h ε hε).add (h' ε hε)
  · refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [Set.mem_ofPred_eq, Prod.dist_eq, le_max_iff] at hω
    exact hω

/-- Probability of a large value of a variable converging in distribution is eventually small
(tightness, from the portmanteau theorem). -/
theorem gm_tight_of_tendstoInDistribution {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℝ} {Z' : Ω' → ℝ} (hZ : TendstoInDistribution Z atTop Z' (fun _ => P) P')
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ T in atTop, P {ω | R ≤ |Z T ω|} < η := by
  set ν : Measure ℝ := P'.map Z'
  have : IsProbabilityMeasure ν := inferInstance
  set A : ℕ → Set ℝ := fun n => {x | (n : ℝ) ≤ |x|}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le measurable_const continuous_abs.measurable
  have hanti : Antitone A := fun n m hnm x hx =>
    show (n : ℝ) ≤ |x| from le_trans (by exact_mod_cast hnm) hx
  have hempty : (⋂ n, A n) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, not_le, A,
      Set.mem_ofPred_eq]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, hn⟩
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hAm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨n, hn, hn1⟩ := ((hlim.eventually (gt_mem_nhds hη)).and (eventually_ge_atTop 1)).exists
  refine ⟨n, by exact_mod_cast hn1, ?_⟩
  have hcl : IsClosed (A n) := isClosed_le continuous_const continuous_abs
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hZ.tendsto hcl
  simp only [ProbabilityMeasure.coe_mk] at hport
  filter_upwards [eventually_lt_of_limsup_lt (hport.trans_lt hn)] with T hT
  rwa [Measure.map_apply_of_aemeasurable (hZ.forall_aemeasurable T) (hAm n)] at hT

/-- If `Z_T → Z` in distribution and `D_T → 0` in probability then `D_T Z_T → 0` in
probability (no measurability of `D_T` needed). -/
theorem gm_tendstoInMeasure_mul {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℝ} {Z' : Ω' → ℝ} (hZ : TendstoInDistribution Z atTop Z' (fun _ => P) P')
    {D : ℕ → Ω → ℝ} (hD : TendstoInMeasure P D atTop (fun _ => 0)) :
    TendstoInMeasure P (fun T ω => D T ω * Z T ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hD ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨R, hR, hev⟩ := gm_tight_of_tendstoInDistribution hZ hη2
  have hD' := (ENNReal.tendsto_nhds_zero.1 (hD (ε / R) (by positivity))) (η / 2) hη2
  filter_upwards [hev, hD'] with T h1 h2
  calc P {ω | ε ≤ dist (D T ω * Z T ω) 0}
      ≤ P ({ω | R ≤ |Z T ω|} ∪ {ω | ε / R ≤ dist (D T ω) 0}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
        by_contra hn
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
        have hlt : |D T ω| * |Z T ω| < ε / R * R :=
          mul_lt_mul'' hn.2 hn.1 (abs_nonneg _) (abs_nonneg _)
        rw [div_mul_cancel₀ _ hR.ne', ← abs_mul] at hlt
        exact absurd hω (not_le.2 hlt)
    _ ≤ P {ω | R ≤ |Z T ω|} + P {ω | ε / R ≤ dist (D T ω) 0} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add h1.le h2
    _ = η := ENNReal.add_halves η

/-- A finite sum of terms converging to `0` in probability converges to `0` in probability. -/
theorem gm_tendstoInMeasure_sum {ι : Type*} [Fintype ι] {P : Measure Ω} {Y : ι → ℕ → Ω → ℝ}
    (h : ∀ i, TendstoInMeasure P (Y i) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun T ω => ∑ i, Y i T ω) atTop (fun _ => 0) := by
  have hpi := gm_tendstoInMeasure_pi (β := fun _ : ι => ℝ) (Y := fun T ω i => Y i T ω)
    (c := fun _ => 0) h
  have := gm_tendstoInMeasure_comp hpi (f := fun v : ι → ℝ => ∑ i, v i)
    (continuous_finsetSum _ fun i _ => continuous_apply i).continuousAt
  simpa using this

/-- If `Z_T → Z` in distribution (in `ℝ^q`) and the matrices `D_T → 0` in probability
(entrywise), then `D_T Z_T → 0` in probability. -/
theorem gm_tendstoInMeasure_matE {k q : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → EuclideanSpace ℝ (Fin q)} {Z' : Ω' → EuclideanSpace ℝ (Fin q)}
    (hZ : TendstoInDistribution Z atTop Z' (fun _ => P) P')
    {D : ℕ → Ω → Matrix (Fin k) (Fin q) ℝ}
    (hD : ∀ i j, TendstoInMeasure P (fun T ω => D T ω i j) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun T ω => gm_matE (D T ω) (Z T ω)) atTop (fun _ => 0) := by
  have hZj : ∀ j, TendstoInDistribution (fun T ω => (Z T ω).ofLp j) atTop
      (fun ω' => (Z' ω').ofLp j) (fun _ => P) P' := fun j =>
    hZ.continuous_comp (g := fun z : EuclideanSpace ℝ (Fin q) => z.ofLp j)
      ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))
  have hcoord : ∀ i, TendstoInMeasure P
      (fun T ω => (D T ω).mulVec (Z T ω).ofLp i) atTop (fun _ => 0) := fun i =>
    gm_tendstoInMeasure_sum (Y := fun j T ω => D T ω i j * (Z T ω).ofLp j)
      fun j => gm_tendstoInMeasure_mul (hZj j) (hD i j)
  have hpi := gm_tendstoInMeasure_pi (β := fun _ : Fin k => ℝ) (c := fun _ => 0) hcoord
  have := gm_tendstoInMeasure_comp hpi (f := gm_toE) (gm_continuous_toE k).continuousAt
  have h0 : gm_toE (fun _ : Fin k => (0 : ℝ)) = 0 := rfl
  rw [h0] at this
  exact this

/-- Matrix inversion is continuous at an invertible matrix. -/
theorem gm_continuousAt_inv {k : ℕ} {N : Matrix (Fin k) (Fin k) ℝ} (hN : N.det ≠ 0) :
    ContinuousAt (fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) N := by
  have h : (fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) =
      fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuousAt_inv₀ hN).comp (continuous_id.matrix_det).continuousAt).smul
    (continuous_id.matrix_adjugate).continuousAt

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asymptotic normality of GMM: Theorem 12.1.2 (Miao, §12.1, pp. 390–392)

Miao, pp. 390–392. With `θ̂_T` consistent (Theorem 12.1.1), interior, the first-order
condition (12.2), the (row-wise) mean value expansion (12.3), `M_T → M` in probability and the
central limit theorem `√T g_T(θ₀) →d N(0, S)` (Lemma 12.1.1), Slutsky's theorem gives

`√T(θ̂_T − θ₀) →d N(0, MSM')`, `M = (G₀'WG₀)⁻¹G₀'W`, `G₀ = E ∂h(x_t, θ₀)/∂θ`

(`theorem_12_1_2`). The CLT of Lemma 12.1.1 is a cited result that does not follow from the
assumptions listed for it (see `docs/GM-corrections.md`); `theorem_12_1_2` takes its conclusion as
the explicit hypothesis `hclt`, and `lemma_12_1_1_iid` (module `GMLemma1211`) proves it in the
i.i.d. case from Mathlib's central limit theorem, so the hypothesis is satisfiable.

Departures: (i) the mean value expansion uses a separate `θ̄_{T,i}` for each moment (the single
`θ̄_T` of (12.3) does not exist in general, `eq_12_3_counterexample`); (ii) the rank condition
`G₀x = 0 ⇒ x = 0` (so that `G₀'WG₀` is invertible) is added; (iii) of Assumption 12.1.8(i)
only differentiability of `h(x, ·)` on a ball around `θ₀` is used, and of Assumption 12.1.10(i)
only continuity of `E ∂h/∂θ` at `θ₀`; (iv) the estimator is assumed measurable (a random
variable), which the book takes for granted.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The sample derivative `∂g_T(θ)/∂θ = (1/T) Σ_{t<T} ∂h(x_t, θ)/∂θ`, row by row. -/
noncomputable def gm_sampleDeriv {k q : ℕ} (X : ℕ → Ω → E)
    (Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ) (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) :
    Fin q → (Fin k → ℝ) →L[ℝ] ℝ :=
  fun i => (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, Dh (X t ω) θ i

/-- The sample Jacobian `∂g_T(θ)/∂θ` as a `q × k` matrix. -/
noncomputable def gm_sampleJac {k q : ℕ} (X : ℕ → Ω → E)
    (Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ) (T : ℕ) (ω : Ω) (θ : Fin k → ℝ) :
    Matrix (Fin q) (Fin k) ℝ :=
  gm_jacobian (gm_sampleDeriv X Dh T ω θ)

/-- The population Jacobian `E[∂h(x_t, θ)/∂θ]` (Assumption 12.1.8(iii)). -/
noncomputable def gm_popJac {k q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E)
    (Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ) (θ : Fin k → ℝ) :
    Matrix (Fin q) (Fin k) ℝ :=
  Matrix.of fun i j => ∫ ω, gm_jacobian (Dh (X 0 ω) θ) i j ∂P

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `g_T` is differentiable with derivative `gm_sampleDeriv` where every `h(x_t, ·)` is. -/
theorem gm_hasFDerivAt_sampleMoment {k q : ℕ} {X : ℕ → Ω → E} {h : E → (Fin k → ℝ) → Fin q → ℝ}
    {Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θ : Fin k → ℝ}
    (hD : ∀ x i, HasFDerivAt (fun θ' => h x θ' i) (Dh x θ i) θ) (T : ℕ) (ω : Ω) (i : Fin q) :
    HasFDerivAt (fun θ' => gm_sampleMoment X h T ω θ' i) (gm_sampleDeriv X Dh T ω θ i) θ :=
  (HasFDerivAt.fun_sum fun t _ => hD (X t ω) i).const_mul ((T : ℝ)⁻¹)

/-- Points of the segment `[θ₀, θ]` are no farther from `θ₀` than `θ`. -/
theorem gm_dist_segment_le {k : ℕ} {θ₀ θ : Fin k → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    dist (θ₀ + s • (θ - θ₀)) θ₀ ≤ dist θ θ₀ := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

omit [MeasurableSpace E] in
/-- Miao, p. 391 (`M_T → M` needs `∂g_T(θ̃_T)/∂θ → G₀`): under Assumption 12.1.10 and
consistency, the sample Jacobian at any point `θ̃_T` no farther from `θ₀` than `θ̂_T` converges in
probability to `G₀ = E ∂h(x_t, θ₀)/∂θ`. -/
theorem gm_sampleJac_tendstoInMeasure {k q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E}
    {Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θ₀ : Fin k → ℝ} {r : ℝ}
    {θh θt : ℕ → Ω → Fin k → ℝ} (hcons : TendstoInMeasure P θh atTop (fun _ => θ₀))
    (hle : ∀ T ω, dist (θt T ω) θ₀ ≤ dist (θh T ω) θ₀) (hr : 0 < r) {i : Fin q} {j : Fin k}
    (hGc : ContinuousAt (fun θ => gm_popJac P X Dh θ i j) θ₀)
    (hGu : ∀ ε > 0, Tendsto (fun T => P {ω | ∃ θ ∈ Metric.ball θ₀ r,
        ε ≤ |gm_sampleJac X Dh T ω θ i j - gm_popJac P X Dh θ i j|}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun T ω => gm_sampleJac X Dh T ω (θt T ω) i j) atTop
      (fun _ => gm_popJac P X Dh θ₀ i j) := by
  rw [tendstoInMeasure_iff_dist] at hcons ⊢
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 hGc (ε / 2) (by linarith)
  have hδ' : 0 < min δ r := lt_min hδ hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun T => P {ω | min δ r ≤ dist (θh T ω) θ₀} + P {ω | ∃ θ ∈ Metric.ball θ₀ r,
      ε / 2 ≤ |gm_sampleJac X Dh T ω θ i j - gm_popJac P X Dh θ i j|}) ?_
    (fun _ => zero_le) fun T => ?_
  · simpa using (hcons _ hδ').add (hGu (ε / 2) (by linarith))
  · refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_exists, not_and] at hn
    obtain ⟨h1, h2⟩ := hn
    have hd := (hle T ω).trans_lt h1
    have hb : θt T ω ∈ Metric.ball θ₀ r := Metric.mem_ball.2 (hd.trans_le (min_le_right _ _))
    have e1 := h2 _ hb
    have e2 := hcont (hd.trans_le (min_le_left _ _))
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω e2
    have := abs_sub_le (gm_sampleJac X Dh T ω (θt T ω) i j) (gm_popJac P X Dh (θt T ω) i j)
      (gm_popJac P X Dh θ₀ i j)
    linarith

/-- **Theorem 12.1.2** (asymptotic normality of GMM, Miao, p. 391). Under Assumptions
12.1.1–12.1.10 — stationarity and ergodicity, continuity, identification, compactness and
dominance (for consistency, Theorem 12.1.1), `W_T` positive semidefinite with `W_T → W > 0`
(12.1.4), `h(x, ·)` differentiable on a ball `B(θ₀, r) ⊆ Θ` with derivative `Dh` (12.1.8),
`E ∂h/∂θ` continuous at `θ₀` and `sup_{B(θ₀,r)} |∂g_T/∂θ − E ∂h/∂θ| → 0` in probability
(12.1.10) — together with the rank condition on `G₀ = E ∂h(x_t, θ₀)/∂θ`, a measurable GMM
estimator, and the central limit theorem `√T g_T(θ₀) →d Z ~ N(0, S)` of Lemma 12.1.1 (the
explicit hypothesis `hclt`; it holds e.g. for i.i.d. data, `lemma_12_1_1_iid`),

`√T(θ̂_T − θ₀) →d −MZ ~ N(0, MSM')`, `M = (G₀'WG₀)⁻¹G₀'W`. -/
theorem theorem_12_1_2 {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (herg : IsErgodicProcess P X)
    {k q : ℕ} {Θ : Set (Fin k → ℝ)} (hΘ : IsCompact Θ) {θ₀ : Fin k → ℝ} (hθ₀ : θ₀ ∈ Θ)
    {h : E → (Fin k → ℝ) → Fin q → ℝ} (hm : ∀ θ ∈ Θ, Measurable fun x => h x θ)
    (hc : ∀ x, ContinuousOn (h x) Θ) (hid : Assumption_12_1_3 P X h Θ θ₀)
    (hdom : Assumption_12_1_7 P X h Θ)
    {WT : ℕ → Ω → Matrix (Fin q) (Fin q) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hA4 : Assumption_12_1_4 P WT W)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball θ₀ r ⊆ Θ)
    {Dh : E → (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ}
    (hDh : ∀ x, ∀ θ ∈ Metric.ball θ₀ r, ∀ i, HasFDerivAt (fun θ' => h x θ' i) (Dh x θ i) θ)
    (hGc : ∀ i j, ContinuousAt (fun θ => gm_popJac P X Dh θ i j) θ₀)
    (hGu : ∀ i j, ∀ ε > 0, Tendsto (fun T => P {ω | ∃ θ ∈ Metric.ball θ₀ r,
        ε ≤ |gm_sampleJac X Dh T ω θ i j - gm_popJac P X Dh θ i j|}) atTop (𝓝 0))
    (hrank : Function.Injective (gm_popJac P X Dh θ₀).mulVec)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) {Z : Ω' → EuclideanSpace ℝ (Fin q)}
    (hZ : HasLaw Z (multivariateGaussian 0 S) P')
    (hclt : TendstoInDistribution
      (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) atTop Z
      (fun _ => P) P')
    {θh : ℕ → Ω → Fin k → ℝ} (hθm : ∀ T, Measurable (θh T)) (hθh : ∀ T ω, θh T ω ∈ Θ)
    (hmin : ∀ T ω, ∀ θ ∈ Θ, gm_objective X h WT T ω (θh T ω) ≤ gm_objective X h WT T ω θ) :
    TendstoInDistribution (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • (θh T ω - θ₀))) atTop
      (fun ω' => gm_matE (-gm_M (gm_popJac P X Dh θ₀) W) (Z ω')) (fun _ => P) P' ∧
    HasLaw (fun ω' => gm_matE (-gm_M (gm_popJac P X Dh θ₀) W) (Z ω'))
      (multivariateGaussian 0 (gm_M (gm_popJac P X Dh θ₀) W * S *
        (gm_M (gm_popJac P X Dh θ₀) W).transpose)) P' := by
  classical
  obtain ⟨hWpsd, hW, hWT⟩ := hA4
  set G₀ := gm_popJac P X Dh θ₀ with hG₀
  set Mm := gm_M G₀ W with hMm
  have hWTs : ∀ T ω, (WT T ω).IsSymm := fun T ω => (hWpsd T ω).isHermitian.isSymm
  have hA0 : IsUnit (G₀.transpose * W * G₀).det := gm_isUnit_det_GWG hW hrank
  have hcons := theorem_12_1_1 hX hst herg hΘ hθ₀ hm hc hid hdom ⟨hWpsd, hW, hWT⟩ hθh hmin
  -- the mean value points (row-wise (12.3))
  have hsx : ∀ T ω i, ∃ s ∈ Set.Icc (0 : ℝ) 1, θh T ω ∈ Metric.ball θ₀ r →
      gm_sampleMoment X h T ω (θh T ω) i = gm_sampleMoment X h T ω θ₀ i +
        ∑ j, gm_sampleJac X Dh T ω (θ₀ + s • (θh T ω - θ₀)) i j * (θh T ω - θ₀) j := by
    intro T ω i
    by_cases hb : θh T ω ∈ Metric.ball θ₀ r
    · obtain ⟨s, hs, heq⟩ := eq_12_3 (g := gm_sampleMoment X h T ω)
        (Dg := gm_sampleDeriv X Dh T ω) (θ₀ := θ₀) (θh := θh T ω) (fun i' s hs =>
          gm_hasFDerivAt_sampleMoment (fun x i'' => hDh x _
            (Metric.mem_ball.2 ((gm_dist_segment_le hs).trans_lt (Metric.mem_ball.1 hb))) i'')
            T ω i') i
      exact ⟨s, Set.Ioo_subset_Icc_self hs, fun _ => heq⟩
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h' => absurd h' hb⟩
  choose s hs01 hsexp using hsx
  set θb : ℕ → Ω → Fin q → Fin k → ℝ := fun T ω i => θ₀ + s T ω i • (θh T ω - θ₀) with hθbdef
  have hθb : ∀ T ω i, dist (θb T ω i) θ₀ ≤ dist (θh T ω) θ₀ := fun T ω i =>
    gm_dist_segment_le (hs01 T ω i)
  set Gh : ℕ → Ω → Matrix (Fin q) (Fin k) ℝ := fun T ω => gm_sampleJac X Dh T ω (θh T ω)
    with hGhdef
  set Gb : ℕ → Ω → Matrix (Fin q) (Fin k) ℝ := fun T ω =>
    Matrix.of fun i j => gm_sampleJac X Dh T ω (θb T ω i) i j with hGbdef
  set MT : ℕ → Ω → Matrix (Fin k) (Fin q) ℝ := fun T ω =>
    ((Gh T ω).transpose * WT T ω * Gb T ω)⁻¹ * (Gh T ω).transpose * WT T ω with hMTdef
  -- convergence of the Jacobians
  have hGh : ∀ i j, TendstoInMeasure P (fun T ω => Gh T ω i j) atTop (fun _ => G₀ i j) :=
    fun i j => gm_sampleJac_tendstoInMeasure hcons (fun _ _ => le_rfl) hr (hGc i j) (hGu i j)
  have hGb : ∀ i j, TendstoInMeasure P (fun T ω => Gb T ω i j) atTop (fun _ => G₀ i j) :=
    fun i j => gm_sampleJac_tendstoInMeasure (θt := fun T ω => θb T ω i) hcons
      (fun T ω => hθb T ω i) hr (hGc i j) (hGu i j)
  -- the triple (Ĝ, Ḡ, W_T) as a function-valued random variable
  set U : ℕ → Ω → (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) × (Fin q → Fin q → ℝ) :=
    fun T ω => (fun i j => Gh T ω i j, fun i j => Gb T ω i j, fun i j => WT T ω i j) with hUdef
  have hU : TendstoInMeasure P U atTop
      (fun _ => ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j))) := by
    refine gm_tendstoInMeasure_prod ?_ (gm_tendstoInMeasure_prod ?_ ?_)
    · exact gm_tendstoInMeasure_pi fun i => gm_tendstoInMeasure_pi fun j => hGh i j
    · exact gm_tendstoInMeasure_pi fun i => gm_tendstoInMeasure_pi fun j => hGb i j
    · exact gm_tendstoInMeasure_pi fun i => gm_tendstoInMeasure_pi fun j => hWT i j
  set Nf : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) × (Fin q → Fin q → ℝ) →
      Matrix (Fin k) (Fin k) ℝ := fun p =>
    (Matrix.of p.1).transpose * Matrix.of p.2.2 * Matrix.of p.2.1 with hNfdef
  have hNc : Continuous Nf :=
    ((continuous_id.comp continuous_fst).matrix_transpose.matrix_mul
      (continuous_id.comp (continuous_snd.comp continuous_snd))).matrix_mul
      (continuous_id.comp (continuous_fst.comp continuous_snd))
  set Φ : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) × (Fin q → Fin q → ℝ) →
      Fin k → Fin q → ℝ := fun p =>
    (Nf p)⁻¹ * (Matrix.of p.1).transpose * Matrix.of p.2.2 with hΦdef
  have hN0 : Nf ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) =
      G₀.transpose * W * G₀ := rfl
  have hΦc : ContinuousAt Φ ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) := by
    have hinv : ContinuousAt (fun p => (Nf p)⁻¹)
        ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) := by
      refine ContinuousAt.comp (g := fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) ?_ hNc.continuousAt
      rw [hN0]
      exact gm_continuousAt_inv hA0.ne_zero
    have hT : ContinuousAt (fun p : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) ×
        (Fin q → Fin q → ℝ) => (Matrix.of p.1).transpose)
        ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) :=
      (continuous_id.comp continuous_fst).matrix_transpose.continuousAt
    have hV' : ContinuousAt (fun p : (Fin q → Fin k → ℝ) × (Fin q → Fin k → ℝ) ×
        (Fin q → Fin q → ℝ) => Matrix.of p.2.2)
        ((fun i j => G₀ i j), (fun i j => G₀ i j), (fun i j => W i j)) :=
      (continuous_id.comp (continuous_snd.comp continuous_snd)).continuousAt
    have hmul1 : Continuous fun x : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin q) ℝ =>
        x.1 * x.2 := continuous_fst.matrix_mul continuous_snd
    have hmul2 : Continuous fun x : Matrix (Fin k) (Fin q) ℝ × Matrix (Fin q) (Fin q) ℝ =>
        x.1 * x.2 := continuous_fst.matrix_mul continuous_snd
    have hm1 := hmul1.continuousAt.comp (hinv.prodMk hT)
    exact hmul2.continuousAt.comp (hm1.prodMk hV')
  have hMT : ∀ i j, TendstoInMeasure P (fun T ω => MT T ω i j) atTop (fun _ => Mm i j) := by
    intro i j
    have h1 := gm_tendstoInMeasure_comp hU hΦc
    exact gm_tendstoInMeasure_apply (gm_tendstoInMeasure_apply h1 i) j
  have hD : ∀ i j, TendstoInMeasure P (fun T ω => (Mm - MT T ω) i j) atTop (fun _ => 0) := by
    intro i j
    have := gm_tendstoInMeasure_comp (hMT i j) (f := fun x => Mm i j - x)
      (continuous_const.sub continuous_id).continuousAt
    simpa using this
  have hdet : TendstoInMeasure P (fun T ω => (Nf (U T ω)).det) atTop
      (fun _ => (G₀.transpose * W * G₀).det) := by
    have := gm_tendstoInMeasure_comp hU (f := fun p => (Nf p).det)
      (hNc.matrix_det).continuousAt
    rwa [hN0] at this
  -- the linear approximation
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin k) :=
    fun T ω => gm_toE (Real.sqrt (T : ℝ) • (θh T ω - θ₀)) with hYdef
  set Zs : ℕ → Ω → EuclideanSpace ℝ (Fin q) :=
    fun T ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀) with hZsdef
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin k) := fun T ω => gm_matE (-Mm) (Zs T ω) with hVdef
  have hgood : ∀ T ω, θh T ω ∈ Metric.ball θ₀ r → (Nf (U T ω)).det ≠ 0 →
      Y T ω - V T ω = gm_matE (Mm - MT T ω) (Zs T ω) := by
    intro T ω hb hdet0
    have hNU : Nf (U T ω) = (Gh T ω).transpose * WT T ω * Gb T ω := rfl
    rw [hNU] at hdet0
    have hinv : IsUnit ((Gh T ω).transpose * WT T ω * Gb T ω).det := isUnit_iff_ne_zero.2 hdet0
    have hloc : IsLocalMin (fun θ => gm_quadForm (WT T ω) (gm_sampleMoment X h T ω θ))
        (θh T ω) := by
      have hmo : IsMinOn (gm_objective X h WT T ω) Θ (θh T ω) := fun θ hθ => hmin T ω θ hθ
      exact hmo.isLocalMin (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hb) hball)
    have hfoc := eq_12_2 (hWTs T ω)
      (fun i => gm_hasFDerivAt_sampleMoment (fun x i' => hDh x _ hb i') T ω i) hloc
    have hexp : gm_sampleMoment X h T ω (θh T ω) =
        gm_sampleMoment X h T ω θ₀ + (Gb T ω).mulVec (θh T ω - θ₀) := by
      funext i
      rw [hsexp T ω i hb]
      rfl
    have hlin := gm_linearization_sqrt (A := Gh T ω) (B := Gb T ω) (V := WT T ω) hfoc hexp hinv
      (Real.sqrt T)
    simp only [hYdef, hVdef, hZsdef, gm_matE_toE]
    rw [hlin, gm_toE, gm_toE, gm_toE, ← WithLp.toLp_sub, Matrix.neg_mulVec, Matrix.sub_mulVec]
    congr 1
    change -(MT T ω).mulVec _ - -Mm.mulVec _ = Mm.mulVec _ - (MT T ω).mulVec _
    abel
  have hprod := gm_tendstoInMeasure_matE hclt hD
  have hYV : TendstoInMeasure P (Y - V) atTop 0 := by
    rw [tendstoInMeasure_iff_dist] at hprod ⊢
    have hc1 := tendstoInMeasure_iff_dist.1 hcons r hr
    have hc2 := tendstoInMeasure_iff_dist.1 hdet |(G₀.transpose * W * G₀).det|
      (abs_pos.2 hA0.ne_zero)
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun T => P {ω | r ≤ dist (θh T ω) θ₀} +
        P {ω | |(G₀.transpose * W * G₀).det| ≤ dist (Nf (U T ω)).det (G₀.transpose * W * G₀).det}
        + P {ω | ε ≤ dist (gm_matE (Mm - MT T ω) (Zs T ω)) 0}) ?_ (fun _ => zero_le) fun T => ?_
    · simpa using (hc1.add hc2).add (hprod ε hε)
    · refine (measure_mono fun ω hω => ?_).trans
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      have hdet0 : (Nf (U T ω)).det ≠ 0 := by
        intro h0
        rw [h0, Real.dist_eq, zero_sub, abs_neg] at h2
        exact lt_irrefl _ h2
      have := hgood T ω (Metric.mem_ball.2 h1) hdet0
      simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply] at hω
      rw [this] at hω
      exact absurd hω (not_le.2 h3)
  have hV : TendstoInDistribution V atTop (fun ω' => gm_matE (-Mm) (Z ω')) (fun _ => P) P' :=
    by
    have := hclt.continuous_comp (g := gm_matE (-Mm)) (gm_continuous_matE (-Mm))
    exact this
  have hYm : ∀ T, AEMeasurable (Y T) P := fun T =>
    ((gm_continuous_toE k).measurable.comp
      (((hθm T).sub measurable_const).const_smul (Real.sqrt (T : ℝ)))).aemeasurable
  refine ⟨tendstoInDistribution_of_tendstoInMeasure_sub Y _ hV hYV hYm, ?_⟩
  refine ⟨(gm_continuous_matE _).measurable.comp_aemeasurable hZ.aemeasurable, ?_⟩
  have hcomp : (fun ω' => gm_matE (-Mm) (Z ω')) = gm_matE (-Mm) ∘ Z := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
    (gm_continuous_matE _).measurable.aemeasurable hZ.aemeasurable, hZ.map_eq,
    gm_map_multivariateGaussian _ hS]
  simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- Miao, p. 392: with the optimal weighting matrix `W = S⁻¹` (`S` positive definite) the limit
law of Theorem 12.1.2 is `N(0, (G₀'S⁻¹G₀)⁻¹)`. -/
theorem theorem_12_1_2_efficient {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {k q : ℕ}
    {G₀ : Matrix (Fin q) (Fin k) ℝ} (hrank : Function.Injective G₀.mulVec)
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosDef) {L : Ω' → EuclideanSpace ℝ (Fin k)}
    (hL : HasLaw L (multivariateGaussian 0 (gm_M G₀ S⁻¹ * S * (gm_M G₀ S⁻¹).transpose)) P') :
    HasLaw L (multivariateGaussian 0 (G₀.transpose * S⁻¹ * G₀)⁻¹) P' := by
  rwa [gm_efficient_var G₀ hS (gm_isUnit_det_GWG hS.inv hrank)] at hL

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lemma 12.1.1: the central limit theorem for `√T g_T(θ₀)` (Miao, §12.1, p. 391)

Miao, p. 391, Lemma 12.1.1: under Assumptions 12.1.1, 12.1.5 and 12.1.9,
`√T g_T(θ₀) →d N(0, S)`. The book cites this (Hall 2005); it does **not** follow from
stationarity, ergodicity and a finite positive definite long-run variance alone (a CLT for
stationary ergodic sequences needs further dependence conditions, e.g. martingale differences
or mixing; Herrndorf 1983 constructs stationary ergodic sequences with finite long-run variance
that violate the CLT). `theorem_12_1_2` therefore takes the CLT as an explicit hypothesis; this
module proves it in the i.i.d. case, where `S = E h h'` (`lemma_12_1_1_iid`), via the
Cramér–Wold device and Mathlib's one-dimensional central limit theorem. With `S` the covariance
matrix `gm_covMat`, which is positive semidefinite (`gm_covMat_posSemidef`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The second-moment matrix `S = E[u(x₀) u(x₀)']` (the covariance matrix when `E u = 0`). -/
noncomputable def gm_covMat {q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E) (u : E → Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j => ∫ ω, u (X 0 ω) i * u (X 0 ω) j ∂P

omit [MeasurableSpace E] in
/-- `t'St = E[(t'u(x₀))²]`. -/
theorem gm_covMat_quad {q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E} {u : E → Fin q → ℝ}
    (hL2 : ∀ i, MemLp (fun ω => u (X 0 ω) i) 2 P) (t : Fin q → ℝ) :
    t ⬝ᵥ (gm_covMat P X u).mulVec t = ∫ ω, (∑ i, t i * u (X 0 ω) i) ^ 2 ∂P := by
  have hint : ∀ i j, Integrable (fun ω => u (X 0 ω) i * u (X 0 ω) j) P := fun i j =>
    (hL2 i).integrable_mul (hL2 j)
  have hsq : (fun ω => (∑ i, t i * u (X 0 ω) i) ^ 2) =
      fun ω => ∑ i, ∑ j, t i * t j * (u (X 0 ω) i * u (X 0 ω) j) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hsq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _]
  simp only [dotProduct, Matrix.mulVec, gm_covMat, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

omit [MeasurableSpace E] in
/-- Miao, Assumption 12.1.9: the second-moment matrix `E[u u']` is positive semidefinite. -/
theorem gm_covMat_posSemidef {q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E} {u : E → Fin q → ℝ}
    (hL2 : ∀ i, MemLp (fun ω => u (X 0 ω) i) 2 P) : (gm_covMat P X u).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun t => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [gm_covMat, Matrix.of_apply, star_trivial]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  · rw [star_trivial, gm_covMat_quad hL2]
    exact integral_nonneg fun ω => sq_nonneg _

/-- `√T · T⁻¹ = (√T)⁻¹`. -/
theorem gm_sqrt_mul_inv (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x * x⁻¹ = (Real.sqrt x)⁻¹ := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 h).ne'
    rw [show x⁻¹ = (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ by rw [← mul_inv, Real.mul_self_sqrt hx],
      ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- **Lemma 12.1.1** in the i.i.d. case (Miao, p. 391). If `x_t` are i.i.d. and
`u(x) = h(x, θ₀)` has `E u(x₀) = 0` and finite second moments, then
`√T g_T(θ₀) →d N(0, S)` with `S = E[u(x₀)u(x₀)']` (here the long-run variance of
Assumption 12.1.9 is `S = Γ₀`). Proved by the Cramér–Wold device from Mathlib's central limit
theorem. This shows the CLT hypothesis of `theorem_12_1_2` is satisfiable. -/
theorem lemma_12_1_1_iid {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    {k q : ℕ} {h : E → (Fin k → ℝ) → Fin q → ℝ} {θ₀ : Fin k → ℝ}
    (hu : Measurable fun x => h x θ₀) (hL2 : ∀ i, MemLp (fun ω => h (X 0 ω) θ₀ i) 2 P)
    (hmean : ∀ i, ∫ ω, h (X 0 ω) θ₀ i ∂P = 0) :
    TendstoInDistribution
      (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) atTop id
      (fun _ => P) (multivariateGaussian 0 (gm_covMat P X fun x => h x θ₀)) := by
  set u : E → Fin q → ℝ := fun x => h x θ₀ with hudef
  set S := gm_covMat P X u with hSdef
  have hS : S.PosSemidef := gm_covMat_posSemidef hL2
  have hui : ∀ i, Measurable fun x => u x i := fun i => measurable_pi_iff.1 hu i
  have hmeas : ∀ T : ℕ, AEMeasurable
      (fun ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) P := by
    intro T
    have hg : Measurable fun ω => gm_sampleMoment X h T ω θ₀ := measurable_pi_iff.2 fun i =>
      measurable_const.mul (Finset.measurable_fun_sum _ fun t _ => (hui i).comp (hX t))
    exact ((gm_continuous_toE q).measurable.comp (hg.const_smul (Real.sqrt (T : ℝ)))).aemeasurable
  rw [tendstoInDistribution_iff_tendstoInDistribution_inner aemeasurable_id hmeas]
  intro t
  set f : E → ℝ := fun x => ∑ i, t.ofLp i * u x i with hfdef
  have hfm : Measurable f := Finset.measurable_fun_sum _ fun i _ => measurable_const.mul (hui i)
  set Y : ℕ → Ω → ℝ := fun s ω => f (X s ω) with hYdef
  have hY0L2 : MemLp (Y 0) 2 P := by
    have := memLp_finsetSum' (μ := P) (p := 2) Finset.univ
      (f := fun i ω => t.ofLp i * u (X 0 ω) i) fun i _ => (hL2 i).const_mul _
    convert this using 1
    funext ω
    simp [hYdef, hfdef]
  have hY0mean : ∫ ω, Y 0 ω ∂P = 0 := by
    simp only [hYdef, hfdef]
    rw [integral_finsetSum _ fun i _ => ((hL2 i).integrable one_le_two).const_mul _]
    simp [integral_const_mul, hmean]
  have hvar : Var[Y 0; P] = t.ofLp ⬝ᵥ S.mulVec t.ofLp := by
    rw [variance_of_integral_eq_zero (X := Y 0) (hfm.comp (hX 0)).aemeasurable hY0mean, hSdef,
      gm_covMat_quad hL2]
  -- the law of `⟪Z, t⟫` for `Z ~ N(0, S)`
  have hlaw : HasLaw (fun z : EuclideanSpace ℝ (Fin q) => inner ℝ z t)
      (gaussianReal 0 Var[Y 0; P].toNNReal) (multivariateGaussian 0 S) := by
    refine ⟨by fun_prop, ?_⟩
    have hL := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) (innerSL ℝ t)
    have hm0 : ∫ z, (innerSL ℝ t) z ∂(multivariateGaussian 0 S) = 0 := by
      rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
        integral_id_multivariateGaussian, map_zero]
    have hfun : (⇑(innerSL ℝ t) : EuclideanSpace ℝ (Fin q) → ℝ) = fun z => inner ℝ z t := by
      funext z
      rw [innerSL_apply_apply, real_inner_comm]
    have hfun' : (⇑(innerSL ℝ t) : EuclideanSpace ℝ (Fin q) → ℝ) = fun z => inner ℝ t z := by
      funext z
      rw [innerSL_apply_apply]
    have hv0 : Var[⇑(innerSL ℝ t); multivariateGaussian 0 S] =
        t.ofLp ⬝ᵥ S.mulVec t.ofLp := by
      have hc := covarianceBilin_self (μ := multivariateGaussian 0 S) IsGaussian.memLp_two_id t
      rw [covarianceBilin_multivariateGaussian hS] at hc
      rw [hfun', ← hc]
    rw [hm0, hv0, ← hvar, hfun] at hL
    exact hL
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hlaw hY0L2
    (hind.comp (fun _ => f) fun _ => hfm) fun s => (hid s).comp hfm
  rw [hY0mean] at hclt
  have heq : (fun (T : ℕ) ω =>
      inner ℝ (gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) t) =
      fun (T : ℕ) ω => (Real.sqrt (T : ℝ))⁻¹ * (∑ s ∈ Finset.range T, Y s ω - T * 0) := by
    funext T ω
    rw [mul_zero, sub_zero, ← gm_sqrt_mul_inv T (Nat.cast_nonneg T)]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, gm_toE, star_trivial, dotProduct,
      Pi.smul_apply, smul_eq_mul, gm_sampleMoment, hYdef, hfdef, hudef, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact hclt

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The long-run covariance matrix and HAC estimators (Miao, §12.1, pp. 391–395)

Miao, pp. 391–395.

* `gm_integral_mul_shift`: for a stationary process,
  `E[φ(x_{s+n}) ψ(x_s)] = E[φ(x_n) ψ(x₀)]` ("the stationarity assumption implies that
  `E(h_t − Eh_t)(h_{t−j} − Eh_{t−j})' = Γ_j` for all `t`", p. 392).
* `gm_toeplitz_sum`, `gm_toeplitz_sum_Ico`: the double sum `Σ_{t,s<T} c_{t,s}` of a Toeplitz
  array (`c_{t,s} = a_{t−s}` for `s ≤ t`, `b_{s−t}` for `t < s`) equals
  `T a₀ + Σ_{j=1}^{T−1} (T − j)(a_j + b_j)`.
* `gm_longRunVar` (p. 392): `Var(√T g_T(θ₀))_{il} = Γ₀ + Σ_{j=1}^{T−1} ((T − j)/T)(Γ_j + Γ_j')`
  (entry `(i, l)`), for a stationary process with square-integrable (centred) moments.
* `gm_longRunVar_limit` (p. 392): if `Σ_j |Γ_j| < ∞` the limit is `S = Γ₀ + Σ_{i≥1}(Γ_i + Γ_i')`.
  The book writes the limit without a summability condition; absolute summability of the
  autocovariances is the standard sufficient condition and is made explicit.
* Table 12.1: the Bartlett, Parzen and quadratic spectral kernels (`gm_bartlett`, `gm_parzen`,
  `gm_qs`), with `ω(0) = 1`, values in `[0, 1]` and continuity of the first two; the sample
  autocovariances `Γ̂_j` and the HAC estimator `Ŝ_HAC = Γ̂₀ + Σ_i ω_{i,T}(Γ̂_i + Γ̂_i')`, which is
  symmetric (`gm_hac_isSymm`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- For a stationary process every `x_t` has the law of `x₀`. -/
theorem gm_map_eq {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    (hst : IsStationary P X) (t : ℕ) : P.map (X t) = P.map (X 0) := by
  have hc : ∀ s, X s = (fun y : Fin 1 → E => y 0) ∘ window X s 0 := fun s => by
    funext ω
    simp [window]
  rw [hc t, hc 0, ← Measure.map_map (measurable_pi_apply 0) (measurable_window hX t 0),
    ← Measure.map_map (measurable_pi_apply 0) (measurable_window hX 0 0), hst t 0]

/-- Miao, p. 392: for a stationary process `E[φ(x_{s+n}) ψ(x_s)] = E[φ(x_n) ψ(x₀)]`. -/
theorem gm_integral_mul_shift {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    (hst : IsStationary P X) {φ ψ : E → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) (s n : ℕ) :
    ∫ ω, φ (X (s + n) ω) * ψ (X s ω) ∂P = ∫ ω, φ (X n ω) * ψ (X 0 ω) ∂P := by
  set F : (Fin (n + 1) → E) → ℝ := fun y => φ (y (Fin.last n)) * ψ (y 0)
  have hF : Measurable F :=
    (hφ.comp (measurable_pi_apply _)).mul (hψ.comp (measurable_pi_apply _))
  have e : ∀ s', ∫ ω, φ (X (s' + n) ω) * ψ (X s' ω) ∂P =
      ∫ y, F y ∂(P.map (window X s' n)) := by
    intro s'
    rw [integral_map (measurable_window hX s' n).aemeasurable hF.aestronglyMeasurable]
    simp [F, window]
  have e0 := e 0
  simp only [zero_add] at e0
  rw [e s, e0, hst s n]

/-- Reflection: `Σ_{t<T} f(T − t) = Σ_{j<T} f(j + 1)`. -/
theorem gm_sum_range_reflect_sub (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, f (T - t) = ∑ j ∈ Finset.range T, f (j + 1) := by
  rw [← Finset.sum_range_reflect (fun j => f (j + 1)) T]
  exact Finset.sum_congr rfl fun t ht => by
    have := Finset.mem_range.1 ht
    congr 1
    omega

/-- The double sum of a Toeplitz array, range form:
`Σ_{t,s<T} c_{t,s} = Σ_{j<T} (T − j)(a_j + b_j) − T b₀`. -/
theorem gm_toeplitz_sum (a b : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if s ≤ t then a (t - s) else b (s - t)) =
      ∑ j ∈ Finset.range T, ((T : ℝ) - j) * (a j + b j) - T * b 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_congr rfl fun t ht => Finset.sum_range_succ _ T]
    rw [Finset.sum_add_distrib, ih]
    have h1 : ∑ t ∈ Finset.range T, (if T ≤ t then a (t - T) else b (T - t)) =
        ∑ t ∈ Finset.range T, b (T - t) := Finset.sum_congr rfl fun t ht => by
      have := Finset.mem_range.1 ht
      simp only [show ¬ T ≤ t by omega, ↓reduceIte]
    have h2 : ∑ s ∈ Finset.range (T + 1), (if s ≤ T then a (T - s) else b (s - T)) =
        ∑ s ∈ Finset.range T, a (T - s) + a 0 := by
      rw [Finset.sum_range_succ]
      simp only [le_refl, ↓reduceIte, Nat.sub_self]
      congr 1
      exact Finset.sum_congr rfl fun s hs => by
        have := Finset.mem_range.1 hs
        simp only [show s ≤ T by omega, ↓reduceIte]
    rw [h1, h2, gm_sum_range_reflect_sub, gm_sum_range_reflect_sub]
    have ha : ∑ j ∈ Finset.range (T + 1), a j = ∑ j ∈ Finset.range T, a (j + 1) + a 0 :=
      Finset.sum_range_succ' _ _
    have hb : ∑ j ∈ Finset.range (T + 1), b j = ∑ j ∈ Finset.range T, b (j + 1) + b 0 :=
      Finset.sum_range_succ' _ _
    have hw : ∑ j ∈ Finset.range (T + 1), (((T + 1 : ℕ) : ℝ) - j) * (a j + b j) =
        ∑ j ∈ Finset.range T, ((T : ℝ) - j) * (a j + b j) +
          ∑ j ∈ Finset.range (T + 1), (a j + b j) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => a j + b j)]
      push_cast
      have : ∑ j ∈ Finset.range T, (((T : ℝ) + 1) - j) * (a j + b j) =
          ∑ j ∈ Finset.range T, ((T : ℝ) - j) * (a j + b j) +
            ∑ j ∈ Finset.range T, (a j + b j) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      ring
    rw [hw, Finset.sum_add_distrib, ha, hb]
    push_cast
    ring

/-- The double sum of a Toeplitz array (Miao, p. 392):
`Σ_{t,s<T} c_{t,s} = T a₀ + Σ_{j=1}^{T−1} (T − j)(a_j + b_j)`. -/
theorem gm_toeplitz_sum_Ico (a b : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if s ≤ t then a (t - s) else b (s - t)) =
      T * a 0 + ∑ j ∈ Finset.Ico 1 T, ((T : ℝ) - j) * (a j + b j) := by
  rw [gm_toeplitz_sum]
  rcases Nat.eq_zero_or_pos T with h | h
  · subst h
    simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot h]
    push_cast
    ring

/-- `Γ_j` entry `(i, l)`: `E[u_i(x_j) u_l(x₀)]` (the autocovariance when `u` is centred). -/
noncomputable def gm_autocov {q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E) (u : E → Fin q → ℝ)
    (j : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i l => ∫ ω, u (X j ω) i * u (X 0 ω) l ∂P

/-- Miao, p. 392 (the long-run variance): for a stationary process and square-integrable `u`
(e.g. `u = h(·, θ₀) − E h`), for `T ≥ 1`,
`E[(T^{−1/2} Σ_t u_i(x_t))(T^{−1/2} Σ_s u_l(x_s))]
  = Γ₀(i,l) + Σ_{j=1}^{T−1} ((T − j)/T)(Γ_j(i,l) + Γ_j'(i,l))`. -/
theorem gm_longRunVar {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) {q : ℕ} {u : E → Fin q → ℝ}
    (hu : Measurable u) (hL2 : ∀ i, MemLp (fun ω => u (X 0 ω) i) 2 P) (i l : Fin q) {T : ℕ}
    (hT : 0 < T) :
    ∫ ω, ((Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, u (X t ω) i) *
        ((Real.sqrt T)⁻¹ * ∑ s ∈ Finset.range T, u (X s ω) l) ∂P =
      gm_autocov P X u 0 i l + ∑ j ∈ Finset.Ico 1 T,
        (((T : ℝ) - j) / T) * (gm_autocov P X u j i l + (gm_autocov P X u j).transpose i l) := by
  have hui : ∀ i, Measurable fun x => u x i := fun i => measurable_pi_iff.1 hu i
  have hL2t : ∀ t i, MemLp (fun ω => u (X t ω) i) 2 P := by
    intro t i
    have h0 := (memLp_map_measure_iff (hui i).aestronglyMeasurable (hX 0).aemeasurable).2
      (hL2 i)
    rw [← gm_map_eq hX hst t] at h0
    exact (memLp_map_measure_iff (hui i).aestronglyMeasurable (hX t).aemeasurable).1 h0
  have hint : ∀ t s, Integrable (fun ω => u (X t ω) i * u (X s ω) l) P := fun t s =>
    (hL2t t i).integrable_mul (hL2t s l)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsq : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hTpos.le]
  have hexp : (fun ω => ((Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, u (X t ω) i) *
      ((Real.sqrt T)⁻¹ * ∑ s ∈ Finset.range T, u (X s ω) l)) = fun ω =>
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, u (X t ω) i * u (X s ω) l := by
    funext ω
    rw [← hsq, mul_mul_mul_comm, Finset.sum_mul_sum]
  have hcell : ∀ t s, ∫ ω, u (X t ω) i * u (X s ω) l ∂P =
      if s ≤ t then gm_autocov P X u (t - s) i l
      else (gm_autocov P X u (s - t)).transpose i l := by
    intro t s
    split_ifs with hst'
    · have := gm_integral_mul_shift hX hst (hui i) (hui l) s (t - s)
      rw [Nat.add_sub_cancel' hst'] at this
      rw [this]
      rfl
    · have := gm_integral_mul_shift hX hst (hui l) (hui i) t (s - t)
      rw [Nat.add_sub_cancel' (by omega)] at this
      simp only [Matrix.transpose_apply, gm_autocov, Matrix.of_apply]
      rw [← this]
      exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  rw [hexp, integral_const_mul, integral_finsetSum _ fun t _ =>
    integrable_finsetSum _ fun s _ => hint t s]
  simp_rw [integral_finsetSum _ fun s _ => hint _ s, hcell]
  rw [gm_toeplitz_sum_Ico (fun j => gm_autocov P X u j i l)
    (fun j => (gm_autocov P X u j).transpose i l), mul_add, Finset.mul_sum]
  congr 1
  · field_simp
  · exact Finset.sum_congr rfl fun j _ => by field_simp

/-- Miao, p. 392: if the autocovariances are absolutely summable, the long-run variance
`Γ₀ + Σ_{j=1}^{T−1} ((T − j)/T)(Γ_j + Γ_j')` converges to `S = Γ₀ + Σ_{i≥1}(Γ_i + Γ_i')`
(entrywise; `a_j = Γ_j(i,l)`, `b_j = Γ_j'(i,l)`). -/
theorem gm_longRunVar_limit {a b : ℕ → ℝ} (ha : Summable fun j => |a j|)
    (hb : Summable fun j => |b j|) :
    Tendsto (fun T : ℕ => a 0 + ∑ j ∈ Finset.Ico 1 T, (((T : ℝ) - j) / T) * (a j + b j)) atTop
      (𝓝 (a 0 + ∑' j, (a (j + 1) + b (j + 1)))) := by
  refine tendsto_const_nhds.add ?_
  set F : ℕ → ℕ → ℝ := fun T j =>
    if j + 1 < T then (((T : ℝ) - (j + 1 : ℕ)) / T) * (a (j + 1) + b (j + 1)) else 0 with hF
  have hsum : ∀ T : ℕ, ∑ j ∈ Finset.Ico 1 T, (((T : ℝ) - j) / T) * (a j + b j) =
      ∑' j, F T j := by
    intro T
    rw [tsum_eq_sum (s := Finset.range (T - 1)) fun j hj => ?_, Finset.sum_Ico_eq_sum_range]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.1 hj
      simp only [hF, show j + 1 < T by omega, ↓reduceIte, add_comm 1 j]
    · have := Finset.mem_range.not.1 hj
      simp only [hF, show ¬ j + 1 < T by omega, ↓reduceIte]
  simp_rw [hsum]
  have hbound : Summable fun j => |a (j + 1)| + |b (j + 1)| :=
    ((summable_nat_add_iff 1).2 ha).add ((summable_nat_add_iff 1).2 hb)
  refine tendsto_tsum_of_dominated_convergence hbound (fun j => ?_) ?_
  · have hw : Tendsto (fun T : ℕ => (1 - ((j + 1 : ℕ) : ℝ) / T) * (a (j + 1) + b (j + 1)))
        atTop (𝓝 ((1 - 0) * (a (j + 1) + b (j + 1)))) :=
      (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)).mul tendsto_const_nhds
    rw [sub_zero, one_mul] at hw
    refine hw.congr' ?_
    filter_upwards [eventually_gt_atTop (j + 1)] with T hT
    have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [hF, hT, ↓reduceIte]
    field_simp
  · refine Eventually.of_forall fun T j => ?_
    simp only [hF]
    split_ifs with hj
    · have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
      have hjT : ((j + 1 : ℕ) : ℝ) < T := by exact_mod_cast hj
      have hw0 : 0 ≤ ((T : ℝ) - (j + 1 : ℕ)) / T := div_nonneg (by linarith) hT.le
      have hw1 : ((T : ℝ) - (j + 1 : ℕ)) / T ≤ 1 := by
        rw [div_le_one hT]
        have : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
      calc ((T : ℝ) - (j + 1 : ℕ)) / T * |a (j + 1) + b (j + 1)|
          ≤ 1 * |a (j + 1) + b (j + 1)| := mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
        _ ≤ |a (j + 1)| + |b (j + 1)| := by rw [one_mul]; exact abs_add_le _ _
    · simp only [norm_zero]
      positivity

/-! ### Table 12.1: HAC kernels and the HAC estimator -/

/-- Table 12.1 (Newey and West 1987): the Bartlett kernel, `1 − a` for `a ≤ 1`, `0` for
`a > 1` (with `a_i = i/(b_T + 1)`). -/
noncomputable def gm_bartlett (a : ℝ) : ℝ := if a ≤ 1 then 1 - a else 0

/-- Table 12.1 (Gallant 1987): the Parzen kernel. -/
noncomputable def gm_parzen (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then 1 - 6 * a ^ 2 + 6 * a ^ 3 else if a ≤ 1 then 2 * (1 - a) ^ 3 else 0

/-- Table 12.1 (Andrews 1991): the quadratic spectral kernel, with `d_i = i/b_T` and
`m_i = 6πd_i/5`. -/
noncomputable def gm_qs (d : ℝ) : ℝ :=
  25 / (12 * Real.pi ^ 2 * d ^ 2) *
    (Real.sin (6 * Real.pi * d / 5) / (6 * Real.pi * d / 5) - Real.cos (6 * Real.pi * d / 5))

/-- Table 12.1: the argument `a_i = i/(b_T + 1)` of the Bartlett and Parzen kernels. -/
noncomputable def gm_kernelArg (i : ℕ) (bT : ℝ) : ℝ := i / (bT + 1)

theorem gm_bartlett_zero : gm_bartlett 0 = 1 := by simp [gm_bartlett]

theorem gm_parzen_zero : gm_parzen 0 = 1 := by norm_num [gm_parzen]

/-- The Bartlett kernel takes values in `[0, 1]` for `a ≥ 0`. -/
theorem gm_bartlett_mem_Icc {a : ℝ} (ha : 0 ≤ a) : gm_bartlett a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gm_bartlett
  split_ifs with h
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The Parzen kernel takes values in `[0, 1]` for `a ≥ 0`. -/
theorem gm_parzen_mem_Icc {a : ℝ} (ha : 0 ≤ a) : gm_parzen a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gm_parzen
  split_ifs with h1 h2
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ha ha), mul_nonneg ha ha,
        mul_nonneg (sub_nonneg.2 h1) ha]
    · have h1' : a ≤ 1 := h1.trans (by norm_num)
      nlinarith [mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 h1')]
  · have h0 : 0 ≤ 1 - a := by linarith
    have h3 : 1 - a ≤ 1 / 2 := by linarith
    constructor
    · positivity
    · nlinarith [pow_le_pow_left₀ h0 h3 3]
  · exact ⟨le_rfl, zero_le_one⟩

/-- The Bartlett kernel is continuous. -/
theorem gm_continuous_bartlett : Continuous gm_bartlett :=
  Continuous.if_le (continuous_const.sub continuous_id) continuous_const continuous_id
    continuous_const fun x hx => by rw [hx, sub_self]

/-- The Parzen kernel is continuous (its pieces agree at `a = 1/2` and `a = 1`). -/
theorem gm_continuous_parzen : Continuous gm_parzen := by
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const fun x hx => ?_
  · exact Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
      fun x hx => by rw [hx]; norm_num
  · rw [hx]
    norm_num

/-- Miao, p. 393: the sample autocovariance `Γ̂_j = T⁻¹ Σ_{t=j+1}^{T} h_t h_{t−j}'` (indices
shifted to `t = j, …, T − 1`). -/
noncomputable def gm_sampleAutocov {q : ℕ} (hs : ℕ → Fin q → ℝ) (T j : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.Ico j T, Matrix.vecMulVec (hs t) (hs (t - j))

/-- Miao, p. 392: the HAC estimator `Ŝ_HAC = Γ̂₀ + Σ_{i=1}^{T−1} ω_{i,T}(Γ̂_i + Γ̂_i')`. -/
noncomputable def gm_hac {q : ℕ} (w : ℕ → ℝ) (hs : ℕ → Fin q → ℝ) (T : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  gm_sampleAutocov hs T 0 +
    ∑ i ∈ Finset.Ico 1 T, w i • (gm_sampleAutocov hs T i + (gm_sampleAutocov hs T i).transpose)

/-- The HAC estimator is symmetric for any kernel weights. -/
theorem gm_hac_isSymm {q : ℕ} (w : ℕ → ℝ) (hs : ℕ → Fin q → ℝ) (T : ℕ) :
    (gm_hac w hs T).IsSymm := by
  unfold Matrix.IsSymm gm_hac
  rw [Matrix.transpose_add, Matrix.transpose_sum]
  congr 1
  · simp only [gm_sampleAutocov, Matrix.transpose_smul, Matrix.transpose_sum,
      Matrix.transpose_vecMulVec, Nat.sub_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 12.1.1: Euler-equation moment conditions (Miao, §12.1, pp. 388–389)

Miao, Example 12.1.1, pp. 388–389. For the consumption/portfolio model of Chapter 8.3 the Euler
equation is `u'(C_t) = β E_t[R_{j,t+1} u'(C_{t+1})]`. With `h = βR_{j,t+1}u'(C_{t+1})/u'(C_t) − 1`
and CRRA utility `u(c) = c^{1−γ}/(1 − γ)` (`gm_crra_hasDerivAt`: `u'(c) = c^{−γ}`), the Euler
equation implies the orthogonality conditions `E[z_t h] = 0` for every `z_t` in the date-`t`
information set (`example_12_1_1`), and in particular the moment condition (12.1) `E h = 0`
(`example_12_1_1_mean`). The date-`t` information is a sub-σ-algebra `F`, `E_t = E[· | F]`,
`C_t` and `z_t` are `F`-measurable, and integrability of the products involved is assumed.
The Euler equation itself is quoted from Chapter 8 (it is not re-derived here).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

/-- CRRA marginal utility `u'(c) = c^{−γ}`. -/
noncomputable def gm_crraMU (γ c : ℝ) : ℝ := c ^ (-γ)

/-- Miao, Example 12.1.1: for `u(c) = c^{1−γ}/(1 − γ)` (`γ ≠ 1`), `u'(c) = c^{−γ}`. -/
theorem gm_crra_hasDerivAt {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun c : ℝ => c ^ (1 - γ) / (1 - γ)) (gm_crraMU γ c) c := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  convert this using 1
  rw [gm_crraMU, mul_div_cancel_left₀ _ h1]
  congr 1
  ring

/-- Miao, Example 12.1.1: the Euler moment function
`h(C_t, C_{t+1}, R_{j,t+1}, θ) = βR_{j,t+1}u'(C_{t+1})/u'(C_t) − 1`, `θ = (β, γ)`. -/
noncomputable def gm_eulerMoment (β γ C C' R : ℝ) : ℝ :=
  β * R * gm_crraMU γ C' / gm_crraMU γ C - 1

/-- With CRRA utility `h = βR(C_{t+1}/C_t)^{−γ} − 1`. -/
theorem gm_eulerMoment_eq {β γ C C' R : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    gm_eulerMoment β γ C C' R = β * R * (C' / C) ^ (-γ) - 1 := by
  rw [gm_eulerMoment, gm_crraMU, gm_crraMU, Real.div_rpow hC'.le hC.le, mul_div_assoc]

/-- **Example 12.1.1** (Miao, p. 389). If the Euler equation
`u'(C_t) = β E_t[R_{j,t+1} u'(C_{t+1})]` holds, with `C_t > 0` and `z_t` measurable with respect to
the date-`t` information `F`, then `E[z_t h(C_t, C_{t+1}, R_{j,t+1}, θ)] = 0`. -/
theorem example_12_1_1 {Ω : Type*} {F : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    (hF : F ≤ mΩ) {P : Measure Ω} [IsProbabilityMeasure P] {β γ : ℝ} {C C' R z : Ω → ℝ}
    (hC : Measurable[F] C) (hCpos : ∀ ω, 0 < C ω) (hz : Measurable[F] z)
    (hY : Integrable (fun ω => β * R ω * gm_crraMU γ (C' ω)) P)
    (hzY : Integrable (fun ω => z ω / gm_crraMU γ (C ω) * (β * R ω * gm_crraMU γ (C' ω))) P)
    (hzint : Integrable z P)
    (heuler : P[fun ω => β * R ω * gm_crraMU γ (C' ω) | F] =ᵐ[P]
      fun ω => gm_crraMU γ (C ω)) :
    ∫ ω, z ω * gm_eulerMoment β γ (C ω) (C' ω) (R ω) ∂P = 0 := by
  have hu : ∀ ω, gm_crraMU γ (C ω) ≠ 0 := fun ω => (Real.rpow_pos_of_pos (hCpos ω) _).ne'
  set Y : Ω → ℝ := fun ω => β * R ω * gm_crraMU γ (C' ω) with hYdef
  set w : Ω → ℝ := fun ω => z ω / gm_crraMU γ (C ω) with hwdef
  have hwm : StronglyMeasurable[F] w :=
    (hz.div (hC.pow_const (-γ))).stronglyMeasurable
  have : IsFiniteMeasure (P.trim hF) := isFiniteMeasure_trim hF
  have key : ∫ ω, w ω * Y ω ∂P = ∫ ω, z ω ∂P := by
    rw [← integral_condExp hF]
    refine integral_congr_ae ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (μ := P) (m := F) (g := Y) hwm hzY hY,
      heuler] with ω h1 h2
    change P[w * Y | F] ω = z ω
    rw [h1, Pi.mul_apply, h2]
    simp only [hwdef]
    field_simp [hu ω]
  have hpt : (fun ω => z ω * gm_eulerMoment β γ (C ω) (C' ω) (R ω)) =
      fun ω => w ω * Y ω - z ω := by
    funext ω
    simp only [gm_eulerMoment, hwdef, hYdef]
    field_simp [hu ω]
  rw [hpt, integral_sub hzY hzint, key, sub_self]

/-- Miao, (12.1) for Example 12.1.1 (`z_t = 1`): the Euler equation implies `E h = 0`. -/
theorem example_12_1_1_mean {Ω : Type*} {F : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    (hF : F ≤ mΩ) {P : Measure Ω} [IsProbabilityMeasure P] {β γ : ℝ} {C C' R : Ω → ℝ}
    (hC : Measurable[F] C) (hCpos : ∀ ω, 0 < C ω)
    (hY : Integrable (fun ω => β * R ω * gm_crraMU γ (C' ω)) P)
    (hzY : Integrable (fun ω => 1 / gm_crraMU γ (C ω) * (β * R ω * gm_crraMU γ (C' ω))) P)
    (heuler : P[fun ω => β * R ω * gm_crraMU γ (C' ω) | F] =ᵐ[P]
      fun ω => gm_crraMU γ (C ω)) :
    ∫ ω, gm_eulerMoment β γ (C ω) (C' ω) (R ω) ∂P = 0 := by
  have := example_12_1_1 hF hC hCpos (z := fun _ => 1) measurable_const hY hzY
    (integrable_const 1) heuler
  simpa using this

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A concrete instance of the GMM assumptions (Miao, §12.1, pp. 387–391)

Non-vacuity of the assumptions of Theorems 12.1.1 and 12.1.2 (Miao, pp. 387–391): a
degenerate but complete instance in which every hypothesis is verified in Lean.

The sample space is a point (`Unit` with the Dirac measure), the data are `x_t = 0`, the moment
function is the location model `h(x, θ) = θ − x` with `k = q = 1`, `Θ = [−1, 1]`, `θ₀ = 0` and
`W_T = W = I`. The process is stationary and ergodic (`gm_ex_isStationary`,
`gm_ex_isErgodic`), Assumptions 12.1.3, 12.1.4 and 12.1.7 hold (`gm_ex_assumption_12_1_3`,
`gm_ex_assumption_12_1_4`, `gm_ex_assumption_12_1_7`), so Theorem 12.1.1 applies
(`gm_ex_theorem_12_1_1`); with `∂h/∂θ = 1`, `S = 0` and the (trivial) central limit theorem
`√T g_T(θ₀) = 0 →d N(0, 0)`, every hypothesis of Theorem 12.1.2 holds and it applies too
(`gm_ex_theorem_12_1_2`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

/-- The constant data `x_t = 0` on a one-point sample space. -/
def gm_exX : ℕ → Unit → ℝ := fun _ _ => 0

/-- The location model `h(x, θ) = θ − x` (`k = q = 1`). -/
def gm_exH : ℝ → (Fin 1 → ℝ) → Fin 1 → ℝ := fun x θ i => θ i - x

/-- The parameter space `Θ = [−1, 1]`. -/
def gm_exΘ : Set (Fin 1 → ℝ) := Metric.closedBall 0 1

/-- The derivative `∂h_i/∂θ = e_i'`. -/
noncomputable def gm_exDh : ℝ → (Fin 1 → ℝ) → Fin 1 → (Fin 1 → ℝ) →L[ℝ] ℝ :=
  fun _ _ i => ContinuousLinearMap.proj i

theorem gm_ex_isStationary : IsStationary (Measure.dirac ()) gm_exX := fun _ _ => rfl

theorem gm_ex_isErgodic : IsErgodicProcess (Measure.dirac ()) gm_exX := by
  intro A hA _
  have hS : MeasurableSet (pathOf gm_exX ⁻¹' A) :=
    measurable_pathOf (fun _ => measurable_const) hA
  by_cases h : () ∈ pathOf gm_exX ⁻¹' A
  · exact Or.inr (Measure.dirac_apply_of_mem h)
  · left
    rw [Measure.dirac_apply' _ hS, Set.indicator_of_notMem h]

theorem gm_ex_popMoment (θ : Fin 1 → ℝ) :
    gm_popMoment (Measure.dirac ()) gm_exX gm_exH θ = θ := by
  funext i
  simp [gm_popMoment, gm_exH, gm_exX]

theorem gm_ex_compact : IsCompact gm_exΘ := isCompact_closedBall 0 1

theorem gm_ex_mem : (0 : Fin 1 → ℝ) ∈ gm_exΘ := Metric.mem_closedBall_self zero_le_one

theorem gm_ex_measurable : ∀ θ ∈ gm_exΘ, Measurable fun x => gm_exH x θ := fun _ _ =>
  measurable_pi_iff.2 fun _ => measurable_const.sub measurable_id

theorem gm_ex_continuous : ∀ x, ContinuousOn (gm_exH x) gm_exΘ := fun _ =>
  (continuous_pi fun i => (continuous_apply i).sub continuous_const).continuousOn

theorem gm_ex_assumption_12_1_3 :
    Assumption_12_1_3 (Measure.dirac ()) gm_exX gm_exH gm_exΘ 0 := fun θ _ => by
  rw [gm_ex_popMoment]

theorem gm_ex_assumption_12_1_7 : Assumption_12_1_7 (Measure.dirac ()) gm_exX gm_exH gm_exΘ := by
  refine ⟨fun x => 1 + |x|, by fun_prop, by simp only [gm_exX]; exact integrable_const _,
    fun x θ hθ => ?_⟩
  have hθ1 : ‖θ‖ ≤ 1 := mem_closedBall_zero_iff.1 hθ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h1 := (norm_le_pi_norm θ i).trans hθ1
  simp only [gm_exH, Real.norm_eq_abs] at h1 ⊢
  have := abs_sub (θ i) x
  linarith

theorem gm_ex_assumption_12_1_4 : Assumption_12_1_4 (Measure.dirac ())
    (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1 := by
  refine ⟨fun _ _ => Matrix.PosSemidef.one, Matrix.PosDef.one, fun i j => ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  simp only [dist_self]
  have : {x : Unit | ε ≤ 0} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp [this]

/-- Theorem 12.1.1 applies to the concrete instance: a GMM estimator exists and is consistent. -/
theorem gm_ex_theorem_12_1_1 : ∃ θh : ℕ → Unit → Fin 1 → ℝ, (∀ T ω, θh T ω ∈ gm_exΘ ∧
    ∀ θ ∈ gm_exΘ, gm_objective gm_exX gm_exH (fun _ _ => 1) T ω (θh T ω) ≤
      gm_objective gm_exX gm_exH (fun _ _ => 1) T ω θ) ∧
    TendstoInMeasure (Measure.dirac ()) θh atTop (fun _ => 0) := by
  obtain ⟨θh, hθh⟩ := gm_exists_estimator (X := gm_exX) gm_ex_compact ⟨0, gm_ex_mem⟩
    gm_ex_continuous (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
  exact ⟨θh, hθh, theorem_12_1_1 (X := gm_exX) (fun _ => measurable_const)
    gm_ex_isStationary gm_ex_isErgodic
    gm_ex_compact gm_ex_mem gm_ex_measurable gm_ex_continuous gm_ex_assumption_12_1_3
    gm_ex_assumption_12_1_7 gm_ex_assumption_12_1_4 (fun T ω => (hθh T ω).1)
    fun T ω => (hθh T ω).2⟩

theorem gm_ex_popJac (θ : Fin 1 → ℝ) :
    gm_popJac (Measure.dirac ()) gm_exX gm_exDh θ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [gm_popJac, gm_jacobian, gm_exDh]

theorem gm_ex_sampleJac {T : ℕ} (hT : 1 ≤ T) (ω : Unit) (θ : Fin 1 → ℝ) :
    gm_sampleJac gm_exX gm_exDh T ω θ = 1 := by
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  ext i j
  fin_cases i
  fin_cases j
  simp [gm_sampleJac, gm_sampleDeriv, gm_jacobian, gm_exDh, hT0]

theorem gm_ex_sampleMoment_zero (T : ℕ) (ω : Unit) :
    gm_sampleMoment gm_exX gm_exH T ω 0 = 0 := by
  funext i
  simp [gm_sampleMoment, gm_exH, gm_exX]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- `N(0, 0)` is the point mass at `0`. -/
theorem gm_ex_multivariateGaussian_zero :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 0 = Measure.dirac 0 := by
  rw [multivariateGaussian, CFC.sqrt_zero (A := Matrix (Fin 1) (Fin 1) ℝ), map_zero]
  simp [Measure.map_const]

/-- Theorem 12.1.2 applies to the concrete instance (with `S = 0`): every hypothesis, including
the central limit theorem of Lemma 12.1.1, is verified, so `√T(θ̂_T − θ₀) →d N(0, 0)`. -/
theorem gm_ex_theorem_12_1_2 : ∃ θh : ℕ → Unit → Fin 1 → ℝ,
    TendstoInDistribution (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • (θh T ω - 0))) atTop
      (fun z => gm_matE (-gm_M (gm_popJac (Measure.dirac ()) gm_exX gm_exDh 0) 1) (id z))
      (fun _ => Measure.dirac ()) (multivariateGaussian 0 0) := by
  obtain ⟨θh, hθh⟩ := gm_exists_estimator (X := gm_exX) gm_ex_compact ⟨0, gm_ex_mem⟩
    gm_ex_continuous (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
  refine ⟨θh, (theorem_12_1_2 (X := gm_exX) (fun _ => measurable_const)
    gm_ex_isStationary gm_ex_isErgodic
    gm_ex_compact gm_ex_mem gm_ex_measurable gm_ex_continuous gm_ex_assumption_12_1_3
    gm_ex_assumption_12_1_7 gm_ex_assumption_12_1_4 (r := 1 / 2) (by norm_num) ?_
    (Dh := gm_exDh) ?_ ?_ ?_ ?_ Matrix.PosSemidef.zero ⟨aemeasurable_id, Measure.map_id⟩ ?_
    (fun _ => Subsingleton.measurable) (fun T ω => (hθh T ω).1)
    fun T ω => (hθh T ω).2).1⟩
  · intro θ hθ
    simp only [gm_exΘ, Metric.mem_closedBall, Metric.mem_ball] at hθ ⊢
    linarith
  · intro x θ _ i
    exact (hasFDerivAt_apply i θ).sub_const x
  · intro i j
    simp only [gm_ex_popJac]
    exact continuousAt_const
  · intro i j ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have : {ω : Unit | ∃ θ ∈ Metric.ball (0 : Fin 1 → ℝ) (1 / 2),
        ε ≤ |gm_sampleJac gm_exX gm_exDh T ω θ i j -
          gm_popJac (Measure.dirac ()) gm_exX gm_exDh θ i j|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro θ _
      rw [gm_ex_sampleJac hT, gm_ex_popJac, sub_self, abs_zero]
      exact hε
    rw [this, measure_empty]
  · rw [gm_ex_popJac]
    intro v w hvw
    simpa [Matrix.one_mulVec] using hvw
  · have heq : (fun (T : ℕ) (ω : Unit) => gm_toE (Real.sqrt (T : ℝ) •
        gm_sampleMoment gm_exX gm_exH T ω 0)) = fun _ _ => 0 := by
      funext T ω
      rw [gm_ex_sampleMoment_zero, smul_zero]
      rfl
    rw [heq]
    refine tendstoInDistribution_of_identDistrib 0 (fun _ => IdentDistrib.refl aemeasurable_const)
      ⟨aemeasurable_const, aemeasurable_id, ?_⟩
    rw [Measure.map_id, gm_ex_multivariateGaussian_zero, Measure.map_const]
    simp

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Contraction Mapping Theorem and Blackwell's conditions

Copied from `EconomicDynamics/Applications` (module `BRContraction`), with the namespace renamed
and the names prefixed `ml_` (there it was copied from `RecursiveMethods/StochasticDP`). Used
here only for McCall's job search model (Miao Example 12.2.1).

Tools for Miao, §§7.2–7.3, pp. 204–211 ("the powerful Contraction Mapping Theorem", the
Blackwell Theorem and the Closed Subspace Theorem; SLP Theorems 3.2, 3.3 and Corollary 1 of
Theorem 3.2).

* `ml_br_IsContraction`, `ml_br_theorem_3_2` (**Contraction Mapping Theorem**: a contraction of a
  complete metric space has exactly one fixed point `v`, and `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)`).
* `ml_br_corollary_1` (**Closed Subspace Theorem**): the fixed point lies in every nonempty closed
  `S′` with `T(S′) ⊆ S′`, and in every `S″` with `T(S′) ⊆ S″`.
* `ml_br_blackwell` (**Blackwell's sufficient conditions**, SLP Theorem 3.3) on the bounded
  continuous functions on a topological space.
* `ml_br_isClosed_comb`: sets of bounded continuous functions cut out by inequalities
  `c f(a) + d f(b) ≤ f(e)` are closed (used for the sets of monotone and concave functions).
-/

open Filter Topology BoundedContinuousFunction

namespace Miao.StructuralEstimation

variable {S : Type*} [MetricSpace S]

/-- `T` is a contraction with modulus `β ∈ (0, 1)` (SLP p. 50). -/
def ml_br_IsContraction (T : S → S) (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ ∀ x y, dist (T x) (T y) ≤ β * dist x y

/-- A contraction is uniformly continuous (SLP Ex 3.8). -/
theorem ml_br_IsContraction.uniformContinuous {T : S → S} {β : ℝ} (hT : ml_br_IsContraction T β) :
    UniformContinuous T :=
  Metric.uniformContinuous_iff.2 fun ε hε => ⟨ε, hε, fun {x y} h =>
    lt_of_le_of_lt (hT.2.2 x y) (by
      calc β * dist x y ≤ 1 * dist x y := mul_le_mul_of_nonneg_right hT.2.1.le dist_nonneg
        _ < ε := by rw [one_mul]; exact h)⟩

/-- SLP (1), p. 51: `ρ(v_{n+1}, v_n) ≤ βⁿ ρ(v₁, v₀)`. -/
theorem ml_br_dist_iterate_succ_le {T : S → S} {β : ℝ} (hT : ml_br_IsContraction T β) (v₀ : S)
    (n : ℕ) : dist (T^[n + 1] v₀) (T^[n] v₀) ≤ β ^ n * dist (T v₀) v₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc dist (T^[n + 1 + 1] v₀) (T^[n + 1] v₀) = dist (T (T^[n + 1] v₀)) (T (T^[n] v₀)) := by
          rw [Function.iterate_succ_apply' T (n + 1), Function.iterate_succ_apply' T n]
      _ ≤ β * dist (T^[n + 1] v₀) (T^[n] v₀) := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist (T v₀) v₀) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist (T v₀) v₀ := by ring

/-- SLP (2), p. 51: `ρ(v_m, v_n) ≤ βⁿ/(1 − β) ρ(v₁, v₀)` for `m ≥ n`. -/
theorem ml_br_dist_iterate_le {T : S → S} {β : ℝ} (hT : ml_br_IsContraction T β) (v₀ : S) {m n : ℕ}
    (hmn : n ≤ m) : dist (T^[m] v₀) (T^[n] v₀) ≤ β ^ n / (1 - β) * dist (T v₀) v₀ := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  have key : ∀ j, dist (T^[n + j] v₀) (T^[n] v₀) ≤
      β ^ n * (1 - β ^ j) / (1 - β) * dist (T v₀) v₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := ml_br_dist_iterate_succ_le hT v₀ (n + j)
      have htri := dist_triangle (T^[n + (j + 1)] v₀) (T^[n + j] v₀) (T^[n] v₀)
      rw [← add_assoc] at htri ⊢
      have e : β ^ n * (1 - β ^ (j + 1)) / (1 - β) =
          β ^ n * (1 - β ^ j) / (1 - β) + β ^ (n + j) := by
        field_simp
        ring
      rw [e, add_mul]
      linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine (key j).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  have := pow_nonneg hT.1.le j
  rw [div_le_div_iff_of_pos_right h1β]
  nlinarith [pow_nonneg hT.1.le n]

/-- The successive approximations `vₙ = Tⁿv₀` form a Cauchy sequence. -/
theorem ml_br_cauchySeq_iterate {T : S → S} {β : ℝ} (hT : ml_br_IsContraction T β) (v₀ : S) :
    CauchySeq fun n => T^[n] v₀ := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlim : Tendsto (fun n => β ^ n / (1 - β) * dist (T v₀) v₀) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).div_const (1 - β)).mul_const
      (dist (T v₀) v₀)
    simpa using this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  exact ⟨N, fun n hn => (ml_br_dist_iterate_le hT v₀ hn).trans_lt (hN N le_rfl)⟩

/-- **The Contraction Mapping Theorem** (SLP Theorem 3.2). If `(S, ρ)` is complete and nonempty
and `T` is a contraction with modulus `β`, then `T` has exactly one fixed point `v`, and
`ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)` for every `v₀`. -/
theorem ml_br_theorem_3_2 [CompleteSpace S] [Nonempty S] {T : S → S} {β : ℝ}
    (hT : ml_br_IsContraction T β) :
    ∃ v, T v = v ∧ (∀ w, T w = w → w = v) ∧
      ∀ v₀ (n : ℕ), dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := by
  obtain ⟨v₀⟩ : Nonempty S := inferInstance
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (ml_br_cauchySeq_iterate hT v₀)
  have hfix : T v = v := by
    have h1 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 (T v)) :=
      (hT.uniformContinuous.continuous.tendsto v).comp hv
    have h2 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 v) := by
      have := hv.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Function.iterate_succ_apply'] using this
    exact tendsto_nhds_unique h1 h2
  have huniq : ∀ w, T w = w → w = v := fun w hw => by
    by_contra hne
    have hpos : 0 < dist w v := dist_pos.2 hne
    have := hT.2.2 w v
    rw [hw, hfix] at this
    nlinarith [hT.2.1]
  refine ⟨v, hfix, huniq, fun v₁ n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    calc dist (T (T^[n] v₁)) v = dist (T (T^[n] v₁)) (T v) := by rw [hfix]
      _ ≤ β * dist (T^[n] v₁) v := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist v₁ v) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist v₁ v := by ring

/-- **The Closed Subspace Theorem** (SLP Corollary 1 of Theorem 3.2). The fixed point of a
contraction lies in every nonempty closed set `S′` with `T(S′) ⊆ S′`, and in every `S″` with
`T(S′) ⊆ S″`. -/
theorem ml_br_corollary_1 {T : S → S} {β : ℝ} (hT : ml_br_IsContraction T β) {v : S} (hv : T v = v)
    {S' S'' : Set S} (hne : S'.Nonempty) (hclosed : IsClosed S') (hmaps : Set.MapsTo T S' S')
    (hS'' : Set.MapsTo T S' S'') : v ∈ S' ∧ v ∈ S'' := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hmem : ∀ n, T^[n] v₀ ∈ S' := fun n => hmaps.iterate n hv₀
  have hlim : Tendsto (fun n => T^[n] v₀) atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hrate : ∀ n, dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ']
        calc dist (T (T^[n] v₀)) v = dist (T (T^[n] v₀)) (T v) := by rw [hv]
          _ ≤ β * dist (T^[n] v₀) v := hT.2.2 _ _
          _ ≤ β * (β ^ n * dist v₀ v) := mul_le_mul_of_nonneg_left ih hT.1.le
          _ = β * β ^ n * dist v₀ v := by ring
    refine squeeze_zero (fun _ => dist_nonneg) hrate ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).mul_const (dist v₀ v)
  have hvS' : v ∈ S' := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  refine ⟨hvS', ?_⟩
  rw [← hv]
  exact hS'' hvS'

/-- **Blackwell's sufficient conditions** (SLP Theorem 3.3) on the bounded continuous functions
on any topological space: a monotone operator that discounts is a contraction of modulus `β`. -/
theorem ml_br_blackwell {X : Type*} [TopologicalSpace X] {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)} {β : ℝ}
    (hβ : 0 ≤ β) (hmono : ∀ f g, f ≤ g → T f ≤ T g)
    (hdisc : ∀ f a, 0 ≤ a → T (f + const X a) ≤ T f + const X (β * a)) (f g : X →ᵇ ℝ) :
    dist (T f) (T g) ≤ β * dist f g := by
  have hle : ∀ f g : X →ᵇ ℝ, f ≤ g + const X (dist f g) := fun f g x => by
    change f x ≤ (g + const X (dist f g)) x
    rw [BoundedContinuousFunction.add_apply, const_apply]
    have := dist_coe_le_dist (f := f) (g := g) x
    rw [Real.dist_eq] at this
    linarith [le_abs_self (f x - g x)]
  have h1 : ∀ f g : X →ᵇ ℝ, ∀ x, T f x ≤ T g x + β * dist f g := fun f g x => by
    have : T f x ≤ (T g + const X (β * dist f g)) x :=
      (hmono _ _ (hle f g)).trans (hdisc g _ dist_nonneg) x
    rwa [BoundedContinuousFunction.add_apply, const_apply] at this
  refine (dist_le (mul_nonneg hβ dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, abs_le]
  have a := h1 f g x
  have b := h1 g f x
  rw [dist_comm] at b
  constructor <;> linarith

/-- Sets of bounded continuous functions cut out by inequalities `c f(a) + d f(b) ≤ f(e)`
(each imposed under a condition `p`) are closed. -/
theorem ml_br_isClosed_comb {X ι : Type*} [TopologicalSpace X] (p : ι → Prop) (c d : ι → ℝ)
    (a b e : ι → X) :
    IsClosed {f : X →ᵇ ℝ | ∀ i, p i → c i * f (a i) + d i * f (b i) ≤ f (e i)} := by
  have : {f : X →ᵇ ℝ | ∀ i, p i → c i * f (a i) + d i * f (b i) ≤ f (e i)} =
      ⋂ i, {f : X →ᵇ ℝ | p i → c i * f (a i) + d i * f (b i) ≤ f (e i)} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun i => ?_
  by_cases hp : p i
  · simp only [hp, true_imp_iff]
    exact isClosed_le (((continuous_eval_const (a i)).const_mul (c i)).add
      ((continuous_eval_const (b i)).const_mul (d i))) (continuous_eval_const (e i))
  · simp only [hp, false_imp_iff, Set.ofPred_true]
    exact isClosed_univ

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Tools for optimal stopping with i.i.d. offers

Copied from `EconomicDynamics/Applications` (module `ODBasic`, plus `od_integrable_sub` and
`od_setIntegral_Ioi_eq` from module `ODOption`), with the namespace renamed and the names
prefixed `ml_`. Used here for McCall's job search model (Miao Example 12.2.1).

Tools for Miao, §8.1, pp. 231–234, and Exercises 8.1–8.2, p. 288. In the option exercise and
McCall problems the offer is drawn afresh from a fixed distribution `F` each period, so the
continuation value is a number `q`, the value function is `V(z) = max(q, h(z))` for the stopping
payoff `h`, and the Bellman equation reduces to the scalar equation
`q = a + β ∫ max(q, h(z′)) dF(z′)`.

* `ml_od_integrable_of_continuous`: continuous functions are `F`-integrable when `F` is a
  probability measure concentrated on `[0, B]` (the book's offer distribution).
* `ml_od_abs_integral_sub_le`: if `|G(x, z) − G(y, z)| ≤ |x − y|`, then the same holds for the
  integrals; `ml_od_lipschitz_stop`: the scalar Bellman map `x ↦ a + β∫ max(x, h) dF` has modulus
  `β`.
* `ml_od_scalar_fixed`: a map of `ℝ` with modulus `β ∈ (0, 1)` has exactly one fixed point (the
  Contraction Mapping Theorem `ml_br_theorem_3_2` on `ℝ`).
* `ml_od_fixed_le_of_le`: fixed points are monotone in the map.
* `ml_od_integral_max_eq`: `∫ max(q, h) dF = q + ∫ max(h − q, 0) dF`.
* `ml_od_integrable_sub`, `ml_od_setIntegral_Ioi_eq`: `z ↦ z − I` is integrable, and
  `∫_{z > x} (z − x) dF = ∫ max(z − x, 0) dF`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory

/-- Continuous functions are integrable for a probability measure concentrated on `[0, B]`. -/
theorem ml_od_integrable_of_continuous {F : Measure ℝ} [IsProbabilityMeasure F] {B : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g F := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B)).exists_bound_of_continuousOn
    hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C (hF.mono fun z hz => hC z hz)

/-- The integrals of a family that is `1`-Lipschitz in the parameter are `1`-Lipschitz. -/
theorem ml_od_abs_integral_sub_le {Ω : Type*} [MeasurableSpace Ω] {F : Measure Ω}
    [IsProbabilityMeasure F] {G : ℝ → Ω → ℝ} (hG : ∀ x, Integrable (G x) F)
    (hL : ∀ x y z, |G x z - G y z| ≤ |x - y|) (x y : ℝ) :
    |∫ z, G x z ∂F - ∫ z, G y z ∂F| ≤ |x - y| := by
  rw [← integral_sub (hG x) (hG y)]
  calc |∫ z, (G x z - G y z) ∂F| ≤ ∫ z, |G x z - G y z| ∂F := abs_integral_le_integral_abs
    _ ≤ ∫ _z, |x - y| ∂F :=
        integral_mono ((hG x).sub (hG y)).abs (integrable_const _) fun z => hL x y z
    _ = |x - y| := by simp

/-- The scalar Bellman map `x ↦ a + β ∫ max(x, h(z)) dF(z)` has modulus `β`. -/
theorem ml_od_lipschitz_stop {Ω : Type*} [MeasurableSpace Ω] {F : Measure Ω}
    [IsProbabilityMeasure F] {h : Ω → ℝ} (hh : Integrable h F) (a : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (x y : ℝ) :
    |(a + β * ∫ z, max x (h z) ∂F) - (a + β * ∫ z, max y (h z) ∂F)| ≤ β * |x - y| := by
  have key := ml_od_abs_integral_sub_le (F := F) (G := fun x z => max x (h z))
    (fun x => (integrable_const x).sup hh) (fun x y z => abs_max_sub_max_le_abs x y (h z)) x y
  rw [show (a + β * ∫ z, max x (h z) ∂F) - (a + β * ∫ z, max y (h z) ∂F)
      = β * (∫ z, max x (h z) ∂F - ∫ z, max y (h z) ∂F) by ring, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left key hβ

/-- A map of `ℝ` with modulus `β ∈ (0, 1)` has exactly one fixed point (the Contraction Mapping
Theorem, `ml_br_theorem_3_2`, on `ℝ`). -/
theorem ml_od_scalar_fixed {Φ : ℝ → ℝ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΦ : ∀ x y, |Φ x - Φ y| ≤ β * |x - y|) : ∃! q, Φ q = q := by
  obtain ⟨q, hq, huniq, -⟩ := ml_br_theorem_3_2 (S := ℝ) (T := Φ) (β := β)
    ⟨hβ0, hβ1, fun x y => by simpa only [Real.dist_eq] using hΦ x y⟩
  exact ⟨q, hq, huniq⟩

/-- Fixed points are monotone in the map: if `Φ₂ ≤ Φ₁` and `Φ₂` has modulus `β < 1`, the fixed
point of `Φ₂` lies below that of `Φ₁`. -/
theorem ml_od_fixed_le_of_le {Φ₁ Φ₂ : ℝ → ℝ} {β : ℝ} (hβ1 : β < 1)
    (hΦ₂ : ∀ x y, |Φ₂ x - Φ₂ y| ≤ β * |x - y|) (hle : ∀ x, Φ₂ x ≤ Φ₁ x) {q₁ q₂ : ℝ}
    (hq₁ : Φ₁ q₁ = q₁) (hq₂ : Φ₂ q₂ = q₂) : q₂ ≤ q₁ := by
  by_contra hlt
  push Not at hlt
  have h1 : q₂ - q₁ ≤ Φ₂ q₂ - Φ₂ q₁ := by linarith [hle q₁]
  have h2 := (le_abs_self _).trans (hΦ₂ q₂ q₁)
  rw [abs_of_pos (sub_pos.2 hlt)] at h2
  nlinarith

/-- `∫ max(q, h) dF = q + ∫ max(h − q, 0) dF` for a probability measure `F`. -/
theorem ml_od_integral_max_eq {Ω : Type*} [MeasurableSpace Ω] {F : Measure Ω}
    [IsProbabilityMeasure F] {h : Ω → ℝ} (hh : Integrable h F) (q : ℝ) :
    ∫ z, max q (h z) ∂F = q + ∫ z, max (h z - q) 0 ∂F := by
  have hfun : (fun z => max q (h z)) = fun z => q + max (h z - q) 0 := by
    funext z
    rcases le_total q (h z) with hz | hz
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
  have hi : Integrable (fun z => max (h z - q) 0) F :=
    (hh.sub (integrable_const q)).sup (integrable_const 0)
  rw [hfun, integral_add (integrable_const q) hi]
  simp

/-- `z ↦ z − I` is integrable for a probability measure concentrated on `[0, B]`. -/
theorem ml_od_integrable_sub {F : Measure ℝ} [IsProbabilityMeasure F] {B : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (I : ℝ) : Integrable (fun z => z - I) F :=
  ml_od_integrable_of_continuous hF (continuous_id.sub continuous_const)

/-- `∫_{z > x} (z − x) dF = ∫ max(z − x, 0) dF`. -/
theorem ml_od_setIntegral_Ioi_eq {F : Measure ℝ} (x : ℝ) :
    ∫ z in Set.Ioi x, (z - x) ∂F = ∫ z, max (z - x) 0 ∂F := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext z
  by_cases hz : x < z
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hz), max_eq_left (by linarith)]
  · rw [Set.indicator_of_notMem (by simpa using hz), max_eq_right (by linarith [not_lt.1 hz])]

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# McCall's job search model, with and without job loss

Copied from `EconomicDynamics/Applications` (module `ODMcCall`), with the namespace renamed and
the names prefixed `ml_`; the link to the stopping problem of Exercise 5.1 (which needs the
MDP modules) is omitted. Used for the job search likelihood of Miao Example 12.2.1.

Miao, §8.1, p. 234, and **Exercise 8.2**, p. 288. Wage offers are drawn i.i.d. from `F` on
`[0, B]`; an unemployed worker receives `c` and draws a new offer next period; `β ∈ (0, 1)`.

**Exercise 8.2.** Each period an employed worker is fired with probability `α ∈ [0, 1]`; a fired
worker waits one period (receiving `c`) and searches again the period after. Writing `U` for the
value of a worker who is unemployed this period and searches next period, `E(w)` for the value of
working at `w` and `V(w)` for the value of holding the offer `w`, the Bellman equations are
(`ml_od_FiringBellman`)
`U = c + β ∫ V dF`, `E(w) = w + β[(1 − α)E(w) + αU]`, `V(w) = max(E(w), U)`.
(The fired worker's position is that of a worker who rejects an offer: he receives `c` now and
draws next period, so his value is `U`.)

* `ml_ex_8_2_E`: `E(w) = (w + αβU)/(1 − β + αβ)`.
* `ml_ex_8_2`: the system has exactly one solution; `U` is the unique fixed point of
  `U ↦ c + β ∫ max((w + αβU)/(1 − β + αβ), U) dF(w)`.
* `ml_ex_8_2_reservation`: the worker accepts exactly the offers `w ≥ w̄ = (1 − β)U` (the
  reservation wage); `V = E` above `w̄` and `V = U` below.
* `ml_ex_8_2_reservation_eq`: `w̄ − c = β/(1 − β + αβ) ∫_{w > w̄} (w − w̄) dF(w)`, and this equation
  has `w̄` as its only root (`ml_ex_8_2_root_unique`).
* `ml_ex_8_2_alpha`: the reservation wage decreases with the firing probability `α`.

**McCall (p. 234).** The Bellman equation `V(w) = max(c + β ∫ V dF, w/(1 − β))`
(`ml_od_McCallBellman`) is the case `α = 0` (`ml_od_mccall_iff_firing`).
`ml_od_mccall_exists_unique`: exactly one solution,
`V(w) = max(Q, w/(1 − β))` with `Q = c + β ∫ V dF`; `ml_od_mccall_reservation`: the worker accepts
iff `w ≥ w̄ = (1 − β)Q`, and `w̄ − c = β/(1 − β) ∫_{w > w̄} (w − w̄) dF`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory

/-- The Bellman equations of **Exercise 8.2** (job search with firing probability `α`). -/
def ml_od_FiringBellman (F : Measure ℝ) (B c α β : ℝ) (V E : ℝ → ℝ) (U : ℝ) : Prop :=
  U = c + β * ∫ w, V w ∂F ∧
    ∀ w ∈ Set.Icc 0 B, E w = w + β * ((1 - α) * E w + α * U) ∧ V w = max (E w) U

/-- The scalar Bellman map for `U` in Exercise 8.2. -/
noncomputable def ml_od_firingΦ (F : Measure ℝ) (c α β U : ℝ) : ℝ :=
  c + β * ∫ w, max ((w + α * β * U) / (1 - β + α * β)) U ∂F

variable {F : Measure ℝ} [IsProbabilityMeasure F] {B c α β : ℝ}

theorem ml_od_firing_D_pos (hβ1 : β < 1) (hα0 : 0 ≤ α) (hβ0 : 0 < β) : 0 < 1 - β + α * β := by
  nlinarith

theorem ml_od_firing_integrable (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (α β U : ℝ) :
    Integrable (fun w => max ((w + α * β * U) / (1 - β + α * β)) U) F :=
  ml_od_integrable_of_continuous hF
    (((continuous_id.add continuous_const).div_const _).max continuous_const)

theorem ml_od_firingΦ_lipschitz (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (x y : ℝ) :
    |ml_od_firingΦ F c α β x - ml_od_firingΦ F c α β y| ≤ β * |x - y| := by
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  have hk0 : 0 ≤ α * β / (1 - β + α * β) := div_nonneg (mul_nonneg hα0 hβ0.le) hD.le
  have hk1 : α * β / (1 - β + α * β) ≤ 1 := by
    rw [div_le_one hD]; linarith
  have hL : ∀ x y w : ℝ, |max ((w + α * β * x) / (1 - β + α * β)) x -
      max ((w + α * β * y) / (1 - β + α * β)) y| ≤ |x - y| := fun x y w => by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ le_rfl)
    have : (w + α * β * x) / (1 - β + α * β) - (w + α * β * y) / (1 - β + α * β) =
        α * β / (1 - β + α * β) * (x - y) := by field_simp; ring
    rw [this, abs_mul, abs_of_nonneg hk0]
    exact mul_le_of_le_one_left (abs_nonneg _) hk1
  have key := ml_od_abs_integral_sub_le (F := F) (ml_od_firing_integrable hF α β) hL x y
  unfold ml_od_firingΦ
  rw [show (c + β * ∫ w, max ((w + α * β * x) / (1 - β + α * β)) x ∂F) -
      (c + β * ∫ w, max ((w + α * β * y) / (1 - β + α * β)) y ∂F) =
      β * (∫ w, max ((w + α * β * x) / (1 - β + α * β)) x ∂F -
        ∫ w, max ((w + α * β * y) / (1 - β + α * β)) y ∂F) by ring,
    abs_mul, abs_of_pos hβ0]
  exact mul_le_mul_of_nonneg_left key hβ0.le

omit [IsProbabilityMeasure F] in
/-- **Exercise 8.2** (Miao, p. 288): the value of working at `w` is
`E(w) = (w + αβU)/(1 − β + αβ)`. -/
theorem ml_ex_8_2_E (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ}
    (hB : ml_od_FiringBellman F B c α β V E U) :
    ∀ w ∈ Set.Icc 0 B, E w = (w + α * β * U) / (1 - β + α * β) := by
  intro w hw
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  have h := (hB.2 w hw).1
  rw [eq_div_iff hD.ne']
  linarith

omit [IsProbabilityMeasure F] in
/-- In a solution, `U` is a fixed point of the scalar map. -/
theorem ml_od_firing_fixed (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ} (hB : ml_od_FiringBellman F B c α β V E U) :
    ml_od_firingΦ F c α β U = U := by
  have hE := ml_ex_8_2_E hβ0 hβ1 hα0 hB
  unfold ml_od_firingΦ
  conv_rhs => rw [hB.1]
  congr 2
  refine integral_congr_ae (hF.mono fun w hw => ?_)
  simp only
  rw [(hB.2 w hw).2, hE w hw]

/-- **Exercise 8.2** (Miao, p. 288): the Bellman equations have a solution, with `U` the unique
fixed point of `U ↦ c + β ∫ max((w + αβU)/(1 − β + αβ), U) dF`, `E(w) = (w + αβU)/(1 − β + αβ)`
and `V = max(E, U)`; every solution has this `U` and agrees with it on `[0, B]`. -/
theorem ml_ex_8_2 (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) :
    ∃ U, ml_od_firingΦ F c α β U = U ∧
      ml_od_FiringBellman F B c α β (fun w => max ((w + α * β * U) / (1 - β + α * β)) U)
        (fun w => (w + α * β * U) / (1 - β + α * β)) U ∧
      ∀ V' E' U', ml_od_FiringBellman F B c α β V' E' U' → U' = U ∧
        ∀ w ∈ Set.Icc 0 B, E' w = (w + α * β * U) / (1 - β + α * β) ∧
          V' w = max ((w + α * β * U) / (1 - β + α * β)) U := by
  obtain ⟨U, hU, huniq⟩ := ml_od_scalar_fixed hβ0 hβ1
    (ml_od_firingΦ_lipschitz (c := c) hF hβ0 hβ1 hα0)
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  refine ⟨U, hU, ⟨hU.symm, fun w _ => ⟨?_, rfl⟩⟩, fun V' E' U' hB' => ?_⟩
  · field_simp; ring
  have hU' : U' = U := huniq _ (ml_od_firing_fixed hF hβ0 hβ1 hα0 hB')
  subst hU'
  refine ⟨rfl, fun w hw => ⟨ml_ex_8_2_E hβ0 hβ1 hα0 hB' w hw, ?_⟩⟩
  rw [(hB'.2 w hw).2, ml_ex_8_2_E hβ0 hβ1 hα0 hB' w hw]

omit [IsProbabilityMeasure F] in
/-- **Exercise 8.2** (Miao, p. 288): the reservation wage property. With `w̄ = (1 − β)U`, the
worker accepts the offer `w` (`E(w) ≥ U`) iff `w ≥ w̄`; `V = E` for `w ≥ w̄` and `V = U` for
`w ≤ w̄`. -/
theorem ml_ex_8_2_reservation (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ}
    (hB : ml_od_FiringBellman F B c α β V E U) :
    ∀ w ∈ Set.Icc 0 B, (U ≤ E w ↔ (1 - β) * U ≤ w) ∧
      ((1 - β) * U ≤ w → V w = E w) ∧ (w ≤ (1 - β) * U → V w = U) := by
  intro w hw
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  have hE := ml_ex_8_2_E hβ0 hβ1 hα0 hB w hw
  have hiff : ∀ {x y : ℝ}, x ≤ (y + α * β * x) / (1 - β + α * β) ↔ (1 - β) * x ≤ y :=
    fun {x y} => by rw [le_div_iff₀ hD]; constructor <;> intro h <;> nlinarith
  have hiff' : ∀ {x y : ℝ}, (y + α * β * x) / (1 - β + α * β) ≤ x ↔ y ≤ (1 - β) * x :=
    fun {x y} => by rw [div_le_iff₀ hD]; constructor <;> intro h <;> nlinarith
  refine ⟨by rw [hE]; exact hiff, fun h => ?_, fun h => ?_⟩
  · rw [(hB.2 w hw).2, max_eq_left (by rw [hE]; exact hiff.2 h)]
  · rw [(hB.2 w hw).2, max_eq_right (by rw [hE]; exact hiff'.2 h)]

/-- The function whose root is the reservation wage in Exercise 8.2,
`ψ_α(x) = x − c − β/(1 − β + αβ) ∫_{w > x} (w − x) dF`. -/
noncomputable def ml_od_firingψ (F : Measure ℝ) (c α β x : ℝ) : ℝ :=
  x - c - β / (1 - β + α * β) * ∫ w in Set.Ioi x, (w - x) ∂F

/-- **Exercise 8.2** (Miao, p. 288): the reservation wage `w̄ = (1 − β)U` solves
`w̄ − c = β/(1 − β + αβ) ∫_{w > w̄} (w − w̄) dF(w)`. -/
theorem ml_ex_8_2_reservation_eq (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ} (hB : ml_od_FiringBellman F B c α β V E U) :
    (1 - β) * U - c = β / (1 - β + α * β) * ∫ w in Set.Ioi ((1 - β) * U), (w - (1 - β) * U) ∂F := by
  have hfix := ml_od_firing_fixed hF hβ0 hβ1 hα0 hB
  have hD := ml_od_firing_D_pos hβ1 hα0 hβ0
  unfold ml_od_firingΦ at hfix
  have hfun : (fun w => max ((w + α * β * U) / (1 - β + α * β)) U) =
      fun w => U + max (w - (1 - β) * U) 0 / (1 - β + α * β) := by
    funext w
    have : (w + α * β * U) / (1 - β + α * β) = U + (w - (1 - β) * U) / (1 - β + α * β) := by
      field_simp; ring
    rw [this]
    rcases le_total 0 (w - (1 - β) * U) with h | h
    · have : 0 ≤ (w - (1 - β) * U) / (1 - β + α * β) := div_nonneg h hD.le
      rw [max_eq_left (by linarith), max_eq_left h]
    · have : (w - (1 - β) * U) / (1 - β + α * β) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hD.le
      rw [max_eq_right (by linarith), max_eq_right h]; simp
  have hi : Integrable (fun w => max (w - (1 - β) * U) 0 / (1 - β + α * β)) F :=
    ((ml_od_integrable_sub hF _).sup (integrable_const 0)).div_const _
  rw [hfun, integral_add (integrable_const U) hi, integral_div] at hfix
  rw [ml_od_setIntegral_Ioi_eq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hfix
  linear_combination -hfix

/-- `ψ_α` is strictly increasing. -/
theorem ml_od_firingψ_strictMono (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) : StrictMono (ml_od_firingψ F c α β) := by
  intro x y hxy
  unfold ml_od_firingψ
  rw [ml_od_setIntegral_Ioi_eq, ml_od_setIntegral_Ioi_eq]
  have hmono : ∫ z, max (z - y) 0 ∂F ≤ ∫ z, max (z - x) 0 ∂F :=
    integral_mono ((ml_od_integrable_sub hF y).sup (integrable_const 0))
      ((ml_od_integrable_sub hF x).sup (integrable_const 0))
      fun z => max_le_max (by linarith) le_rfl
  have hc : 0 ≤ β / (1 - β + α * β) := div_nonneg hβ0.le (ml_od_firing_D_pos hβ1 hα0 hβ0).le
  nlinarith [mul_le_mul_of_nonneg_left hmono hc]

/-- **Exercise 8.2** (Miao, p. 288): the reservation wage is the only root of its equation. -/
theorem ml_ex_8_2_root_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) {V E : ℝ → ℝ} {U : ℝ} (hB : ml_od_FiringBellman F B c α β V E U) (x : ℝ) :
    ml_od_firingψ F c α β x = 0 ↔ x = (1 - β) * U := by
  have hroot : ml_od_firingψ F c α β ((1 - β) * U) = 0 := by
    unfold ml_od_firingψ; linarith [ml_ex_8_2_reservation_eq hF hβ0 hβ1 hα0 hB]
  exact ⟨fun hx => (ml_od_firingψ_strictMono hF hβ0 hβ1 hα0).injective (hx.trans hroot.symm),
    fun hx => hx ▸ hroot⟩

/-- **Exercise 8.2** (Miao, p. 288): the reservation wage decreases with the firing
probability: if `α₁ ≤ α₂` then `w̄(α₂) ≤ w̄(α₁)`. -/
theorem ml_ex_8_2_alpha (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) {α₁ α₂ : ℝ}
    (hα₁ : 0 ≤ α₁) (h12 : α₁ ≤ α₂) {V₁ E₁ V₂ E₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : ml_od_FiringBellman F B c α₁ β V₁ E₁ U₁)
    (hB₂ : ml_od_FiringBellman F B c α₂ β V₂ E₂ U₂) :
    (1 - β) * U₂ ≤ (1 - β) * U₁ := by
  have hα₂ : 0 ≤ α₂ := hα₁.trans h12
  set x₁ := (1 - β) * U₁
  have h1 : ml_od_firingψ F c α₁ β x₁ = 0 := (ml_ex_8_2_root_unique hF hβ0 hβ1 hα₁ hB₁ x₁).2 rfl
  have hD₁ := ml_od_firing_D_pos hβ1 hα₁ hβ0
  have hcoef : β / (1 - β + α₂ * β) ≤ β / (1 - β + α₁ * β) :=
    div_le_div_of_nonneg_left hβ0.le hD₁ (by nlinarith)
  have hint : 0 ≤ ∫ w in Set.Ioi x₁, (w - x₁) ∂F := by
    rw [ml_od_setIntegral_Ioi_eq]; exact integral_nonneg fun _ => le_max_right _ _
  have h2 : 0 ≤ ml_od_firingψ F c α₂ β x₁ := by
    unfold ml_od_firingψ at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcoef hint]
  have h3 : ml_od_firingψ F c α₂ β ((1 - β) * U₂) = 0 :=
    (ml_ex_8_2_root_unique hF hβ0 hβ1 hα₂ hB₂ _).2 rfl
  exact (ml_od_firingψ_strictMono hF hβ0 hβ1 hα₂).le_iff_le.1 (by rw [h3]; exact h2)

/-- The Bellman equation of McCall's job search model (Miao, p. 234) on `[0, B]`. -/
def ml_od_McCallBellman (F : Measure ℝ) (B c β : ℝ) (V : ℝ → ℝ) : Prop :=
  ∀ w ∈ Set.Icc 0 B, V w = max (c + β * ∫ w', V w' ∂F) (w / (1 - β))

omit [IsProbabilityMeasure F] in
/-- Miao, p. 234: McCall's Bellman equation is the case `α = 0` of Exercise 8.2, with
`E(w) = w/(1 − β)` and `U = c + β ∫ V dF`. -/
theorem ml_od_mccall_iff_firing (hβ1 : β < 1) (V : ℝ → ℝ) :
    ml_od_McCallBellman F B c β V ↔
      ml_od_FiringBellman F B c 0 β V (fun w => w / (1 - β)) (c + β * ∫ w, V w ∂F) := by
  have hne : 1 - β ≠ 0 := by linarith
  have hE : ∀ w : ℝ, w / (1 - β) = w + β * ((1 - 0) * (w / (1 - β)) + 0 * (c +
      β * ∫ w, V w ∂F)) := fun w => by field_simp; ring
  constructor
  · intro h
    exact ⟨rfl, fun w hw => ⟨hE w, by rw [h w hw, max_comm]⟩⟩
  · intro h w hw
    rw [(h.2 w hw).2, max_comm]

/-- Miao, p. 234: McCall's Bellman equation has exactly one solution on `[0, B]`,
`V(w) = max(Q, w/(1 − β))` with `Q` the fixed point of `Q ↦ c + β ∫ max(Q, w/(1 − β)) dF`. -/
theorem ml_od_mccall_exists_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Q, ml_od_McCallBellman F B c β (fun w => max Q (w / (1 - β))) ∧
      ∀ W, ml_od_McCallBellman F B c β W → ∀ w ∈ Set.Icc 0 B, W w = max Q (w / (1 - β)) := by
  obtain ⟨U, hU, hB, huniq⟩ := ml_ex_8_2 (c := c) hF hβ0 hβ1 le_rfl
  have hne : 1 - β ≠ 0 := by linarith
  have hsimp : ∀ w : ℝ, (w + 0 * β * U) / (1 - β + 0 * β) = w / (1 - β) := fun w => by ring_nf
  refine ⟨U, fun w hw => ?_, fun W hW w hw => ?_⟩
  · simp only [hsimp] at hB
    have hfe : (fun w => max (w / (1 - β)) U) = fun w => max U (w / (1 - β)) :=
      funext fun _ => max_comm _ _
    rw [hfe] at hB
    change max U (w / (1 - β)) = max (c + β * ∫ w', max U (w' / (1 - β)) ∂F) (w / (1 - β))
    rw [← hB.1]
  · obtain ⟨hU', hW'⟩ := huniq W _ _ ((ml_od_mccall_iff_firing hβ1 W).1 hW)
    rw [(hW' w hw).2, hsimp, max_comm]

/-- Miao, p. 234: the reservation wage. With `Q = c + β ∫ V dF` and `w̄ = (1 − β)Q`, the worker
accepts `w` (`w/(1 − β) ≥ Q`) iff `w ≥ w̄`, and `w̄ − c = β/(1 − β) ∫_{w > w̄} (w − w̄) dF`. -/
theorem ml_od_mccall_reservation (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ → ℝ} (hV : ml_od_McCallBellman F B c β V) :
    let Q := c + β * ∫ w, V w ∂F
    (∀ w ∈ Set.Icc 0 B, (Q ≤ w / (1 - β) ↔ (1 - β) * Q ≤ w) ∧
      ((1 - β) * Q ≤ w → V w = w / (1 - β)) ∧ (w ≤ (1 - β) * Q → V w = Q)) ∧
      (1 - β) * Q - c = β / (1 - β) * ∫ w in Set.Ioi ((1 - β) * Q), (w - (1 - β) * Q) ∂F := by
  intro Q
  have hB := (ml_od_mccall_iff_firing hβ1 V).1 hV
  refine ⟨ml_ex_8_2_reservation hβ0 hβ1 le_rfl hB, ?_⟩
  have := ml_ex_8_2_reservation_eq hF hβ0 hβ1 le_rfl hB
  simpa using this

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Maximum likelihood: likelihood, score, information matrix equality, Cramér–Rao

Miao, §12.2, pp. 396–399. Observations `x₁, …, x_T` are drawn i.i.d. from `f(·, θ)`.

* `ml_likelihood`, `ml_logLikelihood`: `L(θ | x) = ∏ₜ f(xₜ, θ)` and `ln L = ∑ₜ ln f(xₜ, θ)`;
  `eq_ml_log_likelihood` (p. 396): `ln L = ∑ₜ ln f(xₜ, θ)` when `f > 0`;
  `ml_isMaxOn_likelihood_iff`: maximising `L` and maximising `ln L` are the same problem.
* `ml_first_order_condition` (p. 397): at an interior maximiser `∑ₜ ∂ ln f(xₜ, θ̂)/∂θ = 0`, i.e.
  the ML estimator sets the sample mean of the GMM moment `h(x, θ) = ∂ ln f(x, θ)/∂θ` to zero.
* `ml_score_mean_zero` (p. 397, the population moment condition `E[∂ ln f(x, θ)/∂θ] = 0`),
  `ml_information_matrix_equality` (p. 398, `−E[∂² ln f/∂θ²] = E[(∂ ln f/∂θ)²]`) and
  `ml_cramer_rao` (p. 398, the Cramér–Rao bound `Var_θ(δ) · I(θ) ≥ g′(θ)²` for an unbiased
  estimator `δ` of `g(θ)`), for a model on a finite sample space with a scalar parameter.
  `ml_cramer_rao_bernoulli`: one coin toss attains the bound with equality.
* `ml_invariance`, `ml_invariance_profile` (p. 398, invariance): `c(θ̂)` maximises the induced
  (profile) likelihood `γ ↦ sup {L(θ) : c(θ) = γ}`; no differentiability of `c` is needed.
* `ml_gaussian_tests_equal` (pp. 398–399): in the Gaussian location model with known variance
  and `H₀ : μ = μ₀`, the likelihood-ratio, Wald and Lagrange multiplier statistics all equal
  `T(x̄ − μ₀)²/σ²`.

Departures. The book states the information matrix equality and the Cramér–Rao bound for a
vector parameter and a general density, without conditions; here they are proved for a
scalar parameter and a finite sample space, where differentiating `∑ₓ f(x, θ) = 1` under the
sum is automatic. The asymptotic statements (consistency, asymptotic normality, efficiency,
the χ² limits of the three tests) are listed in the book "without explicitly stating relevant
conditions and proofs"; they are proved for the models of Exercises 12.1 and 12.2 in
`MLExercises`.
-/

namespace Miao.StructuralEstimation

open Real

/-- The likelihood of an i.i.d. sample, Miao p. 396: `L(θ | x₁, …, x_T) = ∏ₜ f(xₜ, θ)`. -/
noncomputable def ml_likelihood {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X)
    (θ : Θ) : ℝ :=
  ∏ t, f (x t) θ

/-- The log-likelihood, Miao p. 396: `∑ₜ ln f(xₜ, θ)`. -/
noncomputable def ml_logLikelihood {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X)
    (θ : Θ) : ℝ :=
  ∑ t, Real.log (f (x t) θ)

/-- Miao, p. 396: the logarithm of the likelihood is the log-likelihood
`ln L(θ | x) = ∑ₜ ln f(xₜ, θ)` (for a positive density). -/
theorem eq_ml_log_likelihood {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X) (θ : Θ)
    (hpos : ∀ t, 0 < f (x t) θ) :
    Real.log (ml_likelihood f x θ) = ml_logLikelihood f x θ := by
  unfold ml_likelihood ml_logLikelihood
  exact Real.log_prod fun t _ => (hpos t).ne'

/-- Miao, p. 396: with a positive density, `θ̂` maximises the likelihood on `Θ₀` iff it
maximises the log-likelihood there. -/
theorem ml_isMaxOn_likelihood_iff {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X)
    (Θ₀ : Set Θ) (θhat : Θ) (hpos : ∀ θ t, 0 < f (x t) θ) :
    IsMaxOn (ml_likelihood f x) Θ₀ θhat ↔ IsMaxOn (ml_logLikelihood f x) Θ₀ θhat := by
  have hL : ∀ θ, 0 < ml_likelihood f x θ := fun θ =>
    Finset.prod_pos fun t _ => hpos θ t
  constructor
  · intro h θ hθ
    have h' : ml_likelihood f x θ ≤ ml_likelihood f x θhat := h hθ
    change ml_logLikelihood f x θ ≤ ml_logLikelihood f x θhat
    rw [← eq_ml_log_likelihood f x θ (hpos θ), ← eq_ml_log_likelihood f x θhat (hpos θhat)]
    exact Real.log_le_log (hL θ) h'
  · intro h θ hθ
    have h' : ml_logLikelihood f x θ ≤ ml_logLikelihood f x θhat := h hθ
    change ml_likelihood f x θ ≤ ml_likelihood f x θhat
    rw [← eq_ml_log_likelihood f x θ (hpos θ), ← eq_ml_log_likelihood f x θhat (hpos θhat)] at h'
    exact (Real.log_le_log_iff (hL θ) (hL θhat)).1 h'

/-- Miao, p. 397: the first-order condition of ML. If `θ̂` is a local maximiser of the
log-likelihood and each `θ ↦ ln f(xₜ, θ)` has derivative `s(xₜ, θ̂)` at `θ̂`, then
`∑ₜ s(xₜ, θ̂) = 0`: the ML estimator is the GMM estimator that sets the sample mean of the
moment function `h(x, θ) = ∂ ln f(x, θ)/∂θ` (the score) to zero. -/
theorem ml_first_order_condition {X : Type*} (f : X → ℝ → ℝ) (s : X → ℝ → ℝ) {T : ℕ}
    (x : Fin T → X) (θhat : ℝ) (hmax : IsLocalMax (ml_logLikelihood f x) θhat)
    (hd : ∀ t, HasDerivAt (fun θ => Real.log (f (x t) θ)) (s (x t) θhat) θhat) :
    ∑ t, s (x t) θhat = 0 := by
  have hsum : HasDerivAt (ml_logLikelihood f x) (∑ t, s (x t) θhat) θhat := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun t _ => hd t
    exact this
  exact hmax.hasDerivAt_eq_zero hsum

/-- Miao, p. 397 (the population moment condition `E[∂ ln f(x, θ)/∂θ] = 0`): for a model
`p(·, θ)` on a finite sample space with `∑ₓ p(x, θ) = 1` for all `θ`, positive probabilities and
`∂ₜₕₑₜₐ p(x, θ) = p′(x, θ)`, the score `s = p′/p = ∂ ln p/∂θ` has mean zero:
`∑ₓ p(x, θ) s(x, θ) = 0`. Hence the ML estimator is a GMM estimator with the score as moment. -/
theorem ml_score_mean_zero {Ω : Type*} [Fintype Ω] (p p' : Ω → ℝ → ℝ)
    (hsum : ∀ θ, ∑ x, p x θ = 1) (hpos : ∀ x θ, 0 < p x θ)
    (hp : ∀ x θ, HasDerivAt (p x) (p' x θ) θ) (θ : ℝ) :
    ∑ x, p x θ * (p' x θ / p x θ) = 0 ∧ ∑ x, p' x θ = 0 := by
  have hd : HasDerivAt (fun θ => ∑ x, p x θ) (∑ x, p' x θ) θ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hp x θ
  have hconst : (fun θ => ∑ x, p x θ) = fun _ => (1 : ℝ) := funext hsum
  rw [hconst] at hd
  have h0 : ∑ x, p' x θ = 0 := (hd.unique (hasDerivAt_const θ 1)).symm ▸ rfl
  refine ⟨?_, h0⟩
  rw [← h0]
  refine Finset.sum_congr rfl fun x _ => ?_
  field_simp [(hpos x θ).ne']

/-- **Information matrix equality** (Miao, p. 398), for a scalar parameter on a finite sample
space: with `∑ₓ p(x, θ) = 1`, `p > 0`, `∂p/∂θ = p′`, `∂p′/∂θ = p″`, the score
`s = ∂ ln p/∂θ` and its derivative `H = ∂² ln p/∂θ²` satisfy
`−E[H] = E[s²]`, i.e. `I(θ) = −E[∂² ln p/∂θ²] = E[(∂ ln p/∂θ)²]`. The functions `s` and `H` are
arbitrary functions with these derivative properties. -/
theorem ml_information_matrix_equality {Ω : Type*} [Fintype Ω] (p p' p'' s H : Ω → ℝ → ℝ)
    (hsum : ∀ θ, ∑ x, p x θ = 1) (hpos : ∀ x θ, 0 < p x θ)
    (hp : ∀ x θ, HasDerivAt (p x) (p' x θ) θ) (hp' : ∀ x θ, HasDerivAt (p' x) (p'' x θ) θ)
    (hs : ∀ x θ, HasDerivAt (fun θ => Real.log (p x θ)) (s x θ) θ)
    (hH : ∀ x θ, HasDerivAt (s x) (H x θ) θ) (θ : ℝ) :
    -∑ x, p x θ * H x θ = ∑ x, p x θ * s x θ ^ 2 := by
  -- the score is `p′/p`
  have hs_eq : ∀ x θ, s x θ = p' x θ / p x θ := fun x θ =>
    (hs x θ).unique (((hp x θ).log (hpos x θ).ne'))
  -- `∑ p″ = 0`, differentiating `∑ p′ = 0`
  have h1 : ∀ θ, ∑ x, p' x θ = 0 := fun θ => (ml_score_mean_zero p p' hsum hpos hp θ).2
  have hd : HasDerivAt (fun θ => ∑ x, p' x θ) (∑ x, p'' x θ) θ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hp' x θ
  rw [show (fun θ => ∑ x, p' x θ) = fun _ => (0 : ℝ) from funext h1] at hd
  have h2 : ∑ x, p'' x θ = 0 := (hd.unique (hasDerivAt_const θ 0)).symm ▸ rfl
  -- `H = (p″ p − p′²)/p²`
  have hH_eq : ∀ x, H x θ = (p'' x θ * p x θ - p' x θ * p' x θ) / p x θ ^ 2 := fun x => by
    have hsx : s x = fun θ => p' x θ / p x θ := funext fun θ => hs_eq x θ
    have := hH x θ
    rw [hsx] at this
    exact this.unique ((hp' x θ).div (hp x θ) (hpos x θ).ne')
  have key : ∀ x, -(p x θ * H x θ) = p x θ * s x θ ^ 2 - p'' x θ := fun x => by
    rw [hH_eq x, hs_eq x θ]
    field_simp [(hpos x θ).ne']
    ring
  rw [← Finset.sum_neg_distrib, Finset.sum_congr rfl fun x _ => key x, Finset.sum_sub_distrib,
    h2, sub_zero]

/-- **Cramér–Rao bound** (Miao, p. 398), for a scalar parameter on a finite sample space. Let
`δ` be an unbiased estimator of `g(θ)`: `∑ₓ p(x, θ) δ(x) = g(θ)` for all `θ`, with
`g′(θ) = g'`. Then `g′(θ)² ≤ Var_θ(δ) · I(θ)`, where `Var_θ(δ) = ∑ₓ p (δ − g(θ))²` and
`I(θ) = ∑ₓ p s²` with the score `s = p′/p`. -/
theorem ml_cramer_rao {Ω : Type*} [Fintype Ω] (p p' : Ω → ℝ → ℝ) (δ : Ω → ℝ) (g : ℝ → ℝ)
    (hsum : ∀ θ, ∑ x, p x θ = 1) (hpos : ∀ x θ, 0 < p x θ)
    (hp : ∀ x θ, HasDerivAt (p x) (p' x θ) θ) (hunb : ∀ θ, ∑ x, p x θ * δ x = g θ)
    (θ g' : ℝ) (hg : HasDerivAt g g' θ) :
    g' ^ 2 ≤ (∑ x, p x θ * (δ x - g θ) ^ 2) * ∑ x, p x θ * (p' x θ / p x θ) ^ 2 := by
  have hd : HasDerivAt (fun θ => ∑ x, p x θ * δ x) (∑ x, p' x θ * δ x) θ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => (hp x θ).mul_const (δ x)
  rw [show (fun θ => ∑ x, p x θ * δ x) = g from funext hunb] at hd
  have hg' : g' = ∑ x, p' x θ * δ x := hg.unique hd
  have h0 := (ml_score_mean_zero p p' hsum hpos hp θ).2
  -- `g′ = ∑ √p (δ − g) · √p s`
  have hrep : g' = ∑ x, (Real.sqrt (p x θ) * (δ x - g θ)) *
      (Real.sqrt (p x θ) * (p' x θ / p x θ)) := by
    rw [hg']
    have : ∑ x, p' x θ * δ x = ∑ x, p' x θ * δ x - g θ * ∑ x, p' x θ := by rw [h0]; ring
    rw [this, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hsq : Real.sqrt (p x θ) * Real.sqrt (p x θ) = p x θ :=
      Real.mul_self_sqrt (hpos x θ).le
    have hne := (hpos x θ).ne'
    calc p' x θ * δ x - g θ * p' x θ
        = (Real.sqrt (p x θ) * Real.sqrt (p x θ)) * (δ x - g θ) * (p' x θ / p x θ) := by
          rw [hsq]; field_simp
      _ = _ := by ring
  rw [hrep]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt (hpos x θ).le]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt (hpos x θ).le]

/-- The Cramér–Rao bound is attained (Miao, p. 398, the efficiency claim, in its simplest
instance): for one coin toss with `P(heads) = θ ∈ (0, 1)`, the estimator `δ = 1{heads}` of
`g(θ) = θ` has `Var_θ(δ) = θ(1 − θ)`, the information is `I(θ) = 1/(θ(1 − θ))`, and
`Var_θ(δ) · I(θ) = 1 = g′(θ)²`. -/
theorem ml_cramer_rao_bernoulli (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    let p : Bool → ℝ → ℝ := fun b t => if b then t else 1 - t
    let p' : Bool → ℝ → ℝ := fun b _ => if b then 1 else -1
    let δ : Bool → ℝ := fun b => if b then 1 else 0
    (∑ x, p x θ * (δ x - θ) ^ 2 = θ * (1 - θ)) ∧
      (∑ x, p x θ * (p' x θ / p x θ) ^ 2 = 1 / (θ * (1 - θ))) ∧
      (∑ x, p x θ * (δ x - θ) ^ 2) * (∑ x, p x θ * (p' x θ / p x θ) ^ 2) = 1 ^ 2 := by
  intro p p' δ
  have hv : ∑ x, p x θ * (δ x - θ) ^ 2 = θ * (1 - θ) := by
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, p, δ, ite_true, ite_false, Bool.false_eq_true]
    ring
  have hI : ∑ x, p x θ * (p' x θ / p x θ) ^ 2 = 1 / (θ * (1 - θ)) := by
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, p, p', ite_true, ite_false, Bool.false_eq_true]
    have : (1 - θ) ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨hv, hI, ?_⟩
  rw [hv, hI]
  have : (1 - θ) ≠ 0 := by linarith
  field_simp

/-- **Invariance** (Miao, p. 398), for a reparametrisation `e : Θ ≃ Γ`: if `θ̂` maximises `L`
then `γ̂ = e(θ̂)` maximises the likelihood `γ ↦ L(e⁻¹ γ)` of `γ = e(θ)`. -/
theorem ml_invariance {Θ Γ : Type*} (L : Θ → ℝ) (e : Θ ≃ Γ) (θhat : Θ)
    (hmax : ∀ θ, L θ ≤ L θhat) : ∀ γ, L (e.symm γ) ≤ L (e.symm (e θhat)) := by
  intro γ
  rw [e.symm_apply_apply]
  exact hmax _

/-- The profile (induced) likelihood of `γ = c(θ)`: `L*(γ) = sup {L(θ) : c(θ) = γ}`. -/
noncomputable def ml_profileLikelihood {Θ Γ : Type*} (L : Θ → ℝ) (c : Θ → Γ) (γ : Γ) : ℝ :=
  sSup (L '' {θ | c θ = γ})

/-- **Invariance** (Miao, p. 398), for any `c : Θ → Γ` (Zehna's theorem): if `θ̂` maximises `L`,
then `c(θ̂)` maximises the profile likelihood `L*(γ) = sup {L(θ) : c(θ) = γ}` over the attainable
`γ`, and `L*(c(θ̂)) = L(θ̂)`. The book asks `c` to be continuously differentiable; no regularity
of `c` is needed. -/
theorem ml_invariance_profile {Θ Γ : Type*} (L : Θ → ℝ) (c : Θ → Γ) (θhat : Θ)
    (hmax : ∀ θ, L θ ≤ L θhat) :
    ml_profileLikelihood L c (c θhat) = L θhat ∧
      ∀ γ ∈ Set.range c, ml_profileLikelihood L c γ ≤ ml_profileLikelihood L c (c θhat) := by
  have hfib : ml_profileLikelihood L c (c θhat) = L θhat := by
    unfold ml_profileLikelihood
    refine le_antisymm (csSup_le ⟨L θhat, θhat, rfl, rfl⟩ ?_) ?_
    · rintro _ ⟨θ, -, rfl⟩
      exact hmax θ
    · exact le_csSup ⟨L θhat, by rintro _ ⟨θ, -, rfl⟩; exact hmax θ⟩ ⟨θhat, rfl, rfl⟩
  refine ⟨hfib, ?_⟩
  rintro γ ⟨θ₀, rfl⟩
  rw [hfib]
  unfold ml_profileLikelihood
  refine csSup_le ⟨L θ₀, θ₀, rfl, rfl⟩ ?_
  rintro _ ⟨θ, -, rfl⟩
  exact hmax θ

/-- The log-likelihood of the Gaussian location model with known variance `σ²`, up to the
constant `−(T/2) ln(2πσ²)`: `ℓ(μ) = −∑ₜ (xₜ − μ)²/(2σ²)`. -/
noncomputable def ml_gaussLogLik {T : ℕ} (σ2 : ℝ) (x : Fin T → ℝ) (μ : ℝ) : ℝ :=
  -(∑ t, (x t - μ) ^ 2) / (2 * σ2)

/-- Miao, pp. 398–399: the likelihood ratio, Wald and Lagrange multiplier tests of
`H₀ : μ = μ₀` in the Gaussian location model `xₜ ~ N(μ, σ²)` (known `σ² > 0`, `T ≥ 1`
observations, ML estimator `μ̂ = x̄`) coincide:
`LR = 2(ℓ(x̄) − ℓ(μ₀))`, `W = c(μ̂)² / Var(c(μ̂))` with `c(μ) = μ − μ₀`, `Var(x̄) = σ²/T`, and
`LM = ℓ′(μ₀)² / I` with the sample information `I = T/σ²` all equal `T(x̄ − μ₀)²/σ²`. -/
theorem ml_gaussian_tests_equal {T : ℕ} (hT : 0 < T) (σ2 : ℝ) (hσ : 0 < σ2) (x : Fin T → ℝ)
    (μ₀ : ℝ) :
    let xbar := (∑ t, x t) / T
    let LR := 2 * (ml_gaussLogLik σ2 x xbar - ml_gaussLogLik σ2 x μ₀)
    let W := (xbar - μ₀) ^ 2 / (σ2 / T)
    let LM := ((∑ t, (x t - μ₀)) / σ2) ^ 2 / (T / σ2)
    LR = T * (xbar - μ₀) ^ 2 / σ2 ∧ W = T * (xbar - μ₀) ^ 2 / σ2 ∧
      LM = T * (xbar - μ₀) ^ 2 / σ2 := by
  intro xbar LR W LM
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hS : ∑ t, x t = T * xbar := by
    simp only [xbar]; field_simp
  have hdecomp : ∀ m : ℝ, ∑ t, (x t - m) ^ 2 =
      ∑ t, (x t - xbar) ^ 2 + T * (xbar - m) ^ 2 := fun m => by
    have : ∀ t, (x t - m) ^ 2 = (x t - xbar) ^ 2 + 2 * (xbar - m) * x t +
        (m ^ 2 - xbar ^ 2) := fun t => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [LR, ml_gaussLogLik]
    rw [hdecomp xbar, hdecomp μ₀]
    field_simp
    ring
  · simp only [W]
    field_simp
  · simp only [LM]
    have : ∑ t, (x t - μ₀) = T * (xbar - μ₀) := by
      rw [Finset.sum_sub_distrib, hS]; simp
      ring
    rw [this]
    field_simp

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Moments of the exponential distribution

Tools for Miao, Exercise 12.2, p. 408 (and Example 12.3.3, p. 405): the exponential
distribution `f(x) = θ e^{−θx}`, `x ≥ 0`, is Mathlib's `expMeasure θ`.

* `ml_integral_expMeasure`: `∫ g d(expMeasure θ) = ∫_{x > 0} θ e^{−θx} g(x) dx`.
* `ml_integrable_expMeasure_pow`: `x ↦ xⁿ` is integrable for `n = 1, 2`;
  `ml_memLp_two_expMeasure`: the identity is square integrable.
* `ml_mean_expMeasure`: the mean is `1/θ`; `ml_second_moment_expMeasure`: `E x² = 2/θ²`;
  `ml_variance_expMeasure`: the variance is `1/θ²`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Real

/-- The density of `expMeasure θ` as a real indicator function. -/
theorem ml_gammaPDF_one_toReal {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    (gammaPDF 1 θ x).toReal = Set.indicator (Set.Ici 0) (fun x => θ * Real.exp (-(θ * x))) x := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hθ x)]
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (Set.mem_Ici.2 hx), gammaPDFReal]
    simp [hx]
  · rw [Set.indicator_of_notMem (by simpa using hx), gammaPDFReal]
    simp [hx]

/-- `∫ g d(expMeasure θ) = ∫_{x > 0} θ e^{−θx} g(x) dx`. -/
theorem ml_integral_expMeasure {θ : ℝ} (hθ : 0 < θ) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure θ) = ∫ x in Set.Ioi 0, θ * Real.exp (-(θ * x)) * g x := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF 1 θ) from (measurable_gammaPDFReal 1 θ).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ml_gammaPDF_one_toReal hθ, smul_eq_mul]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Ici (0 : ℝ)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- `x ↦ xⁿ` is `expMeasure θ`-integrable for `n ≥ 1` (used for `n = 1, 2`). -/
theorem ml_integrable_expMeasure_pow {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (expMeasure θ) := by
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul'
    (show Measurable (gammaPDF 1 θ) from (measurable_gammaPDFReal 1 θ).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ml_gammaPDF_one_toReal hθ, smul_eq_mul]
  have hfun : (fun x : ℝ => Set.indicator (Set.Ici 0) (fun x => θ * Real.exp (-(θ * x))) x *
      x ^ n) = Set.indicator (Set.Ici 0) (fun x => θ * Real.exp (-(θ * x)) * x ^ n) := by
    funext x
    by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := θ)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hθ
  refine IntegrableOn.congr_fun (Integrable.const_mul hI θ) (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]
  ring

/-- The identity is square integrable for `expMeasure θ`. -/
theorem ml_memLp_two_expMeasure {θ : ℝ} (hθ : 0 < θ) : MemLp id 2 (expMeasure θ) :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
    (by simpa using ml_integrable_expMeasure_pow hθ 2)

/-- `∫_{x > 0} θ e^{−θx} xⁿ dx = n!/θⁿ`. -/
theorem ml_integral_expMeasure_pow {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure θ) = n.factorial / θ ^ n := by
  rw [ml_integral_expMeasure hθ]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := θ) (by positivity) hθ
  have hcongr : ∫ x in Set.Ioi 0, θ * Real.exp (-(θ * x)) * x ^ n =
      θ * ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) + 1 - 1) * Real.exp (-(θ * x)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  rw [hcongr, h, Real.Gamma_nat_eq_factorial, Real.rpow_add_one (by positivity),
    Real.rpow_natCast, one_div, inv_pow]
  field_simp

/-- The exponential distribution has mean `1/θ` (Miao, Exercise 12.2 and Example 12.3.3). -/
theorem ml_mean_expMeasure {θ : ℝ} (hθ : 0 < θ) : ∫ x, x ∂(expMeasure θ) = 1 / θ := by
  simpa using ml_integral_expMeasure_pow hθ 1

/-- The exponential distribution has second moment `2/θ²`. -/
theorem ml_second_moment_expMeasure {θ : ℝ} (hθ : 0 < θ) :
    ∫ x, x ^ 2 ∂(expMeasure θ) = 2 / θ ^ 2 := by
  simpa using ml_integral_expMeasure_pow hθ 2

/-- The exponential distribution has variance `1/θ²` (Miao, Exercise 12.2). -/
theorem ml_variance_expMeasure {θ : ℝ} (hθ : 0 < θ) :
    have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
    Var[id; expMeasure θ] = 1 / θ ^ 2 := by
  have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  rw [variance_eq_sub (ml_memLp_two_expMeasure hθ)]
  have h2 := ml_second_moment_expMeasure hθ
  have h1 := ml_mean_expMeasure hθ
  simp only [Pi.pow_apply, id] at *
  rw [h2, h1]
  field_simp
  ring

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 12.1 and 12.2: coin tossing and exponential maximum likelihood

Miao, §12.4, p. 408, Exercises 12.1 and 12.2, and the asymptotic properties of ML listed on
pp. 397–398 for these two models.

* `ml_binomial_lik_le`: `pᵏ(1 − p)ⁿ⁻ᵏ ≤ (k/n)ᵏ(1 − k/n)ⁿ⁻ᵏ` for `p ∈ [0, 1]`.
* **Exercise 12.1** (coin tossing): `ex_12_1_likelihood` (`L(p) = pᵏ(1 − p)ᴺ⁻ᵏ` with `k` the number
  of heads), `ex_12_1` (the ML estimate is `p̂ = k/N`, the frequency of heads),
  `ex_12_1_consistent` (`p̂_N → p` almost surely, by the strong law), `ex_12_1_asymptotic`
  (`√N(p̂_N − p) ⇒ N(0, p(1 − p))`, by the central limit theorem; `p(1 − p) = I(p)⁻¹` by
  `ml_cramer_rao_bernoulli`).
* **Exercise 12.2** (exponential sampling, `f(x) = θe^{−xθ}`): `ex_12_2_likelihood`
  (`L(θ) = θᴺ e^{−θ ∑ xₜ}`), `ex_12_2_logLikelihood`, `ex_12_2` (the ML estimator is
  `θ̂ = N/∑ xₜ = 1/x̄`), `ex_12_2_fisher` (`−∂² ln f/∂θ² = 1/θ²`, so `I(θ) = 1/θ²`),
  `ex_12_2_consistent` (`θ̂_N → θ` almost surely) and `ex_12_2_asymptotic` (the asymptotic
  distribution: `√N(θ̂_N − θ) ⇒ N(0, θ²) = N(0, I(θ)⁻¹)`, by the central limit theorem and the
  delta method through Slutsky's theorem).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology Real

/-- The Bernoulli likelihood is maximised at the frequency: for `k ≤ n`, `0 < n` and
`p ∈ [0, 1]`, `pᵏ(1 − p)ⁿ⁻ᵏ ≤ (k/n)ᵏ(1 − k/n)ⁿ⁻ᵏ`. -/
theorem ml_binomial_lik_le (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    p ^ k * (1 - p) ^ (n - k) ≤ ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, sub_zero, one_pow, Nat.sub_zero]
    exact pow_le_one₀ (by linarith) (by linarith)
  rcases hk.lt_or_eq with hkn | rfl
  · set q : ℝ := (k : ℝ) / n with hq
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hknR : (k : ℝ) < n := by exact_mod_cast hkn
    have hq0 : 0 < q := div_pos hkR hn'
    have hq1 : q < 1 := (div_lt_one hn').2 hknR
    have hm0 : 0 < n - k := Nat.sub_pos_of_lt hkn
    have hmR : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hk
    rcases hp0.lt_or_eq with hp0' | rfl
    · rcases hp1.lt_or_eq with hp1' | rfl
      · -- interior: compare the logarithms
        have hL : 0 < p ^ k * (1 - p) ^ (n - k) := by
          have : 0 < 1 - p := by linarith
          positivity
        have hR : 0 < q ^ k * (1 - q) ^ (n - k) := by
          have : 0 < 1 - q := by linarith
          positivity
        rw [← Real.log_le_log_iff hL hR, Real.log_mul (by positivity) (by
          have : 0 < 1 - p := by linarith
          positivity), Real.log_mul (by positivity) (by
          have : 0 < 1 - q := by linarith
          positivity), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, hmR]
        have h1 : Real.log p - Real.log q ≤ p / q - 1 := by
          rw [← Real.log_div hp0'.ne' hq0.ne']
          exact Real.log_le_sub_one_of_pos (div_pos hp0' hq0)
        have h2 : Real.log (1 - p) - Real.log (1 - q) ≤ (1 - p) / (1 - q) - 1 := by
          rw [← Real.log_div (by linarith) (by linarith)]
          exact Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
        have hnkne : (n : ℝ) - k ≠ 0 := by linarith
        have hkne : (k : ℝ) ≠ 0 := hkR.ne'
        have e1 : (k : ℝ) * (p / q - 1) = n * p - k := by
          rw [hq]; field_simp
        have h1q : 1 - q = (n - k) / n := by rw [hq]; field_simp
        have e2 : ((n : ℝ) - k) * ((1 - p) / (1 - q) - 1) = k - n * p := by
          rw [h1q]; field_simp; ring
        have hsum : (k : ℝ) * (p / q - 1) + (n - k) * ((1 - p) / (1 - q) - 1) = 0 := by
          rw [e1, e2]; ring
        have hnk : (0 : ℝ) ≤ n - k := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hkR.le, mul_le_mul_of_nonneg_left h2 hnk]
      · rw [sub_self, zero_pow hm0.ne', mul_zero]
        have : 0 ≤ 1 - q := by linarith
        positivity
    · rw [zero_pow hk0.ne', zero_mul]
      have : 0 ≤ 1 - q := by linarith
      positivity
  · simp only [Nat.sub_self, pow_zero, mul_one, div_self hn'.ne', one_pow]
    exact pow_le_one₀ hp0 hp1

/-- The density of one coin toss, `Pr(x | p) = p` for heads and `1 − p` for tails. -/
def ml_coinDensity (b : Bool) (p : ℝ) : ℝ := if b then p else 1 - p

/-- The number of heads in `x₁, …, x_N`. -/
def ml_heads {N : ℕ} (x : Fin N → Bool) : ℕ := (Finset.univ.filter fun t => x t = true).card

/-- **Exercise 12.1** (Miao, p. 408): the likelihood of the tosses `x₁, …, x_N` is
`L(p) = ∏ₜ p^{xₜ}(1 − p)^{1 − xₜ} = pᵏ(1 − p)ᴺ⁻ᵏ`, `k` the number of heads. -/
theorem ex_12_1_likelihood {N : ℕ} (x : Fin N → Bool) (p : ℝ) :
    ml_likelihood ml_coinDensity x p = p ^ ml_heads x * (1 - p) ^ (N - ml_heads x) := by
  unfold ml_likelihood ml_coinDensity ml_heads
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun t : Fin N => x t = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **Exercise 12.1** (Miao, p. 408): the ML estimate of `p` is the frequency of heads
`p̂ = k/N`: it lies in `[0, 1]` and maximises the likelihood over `[0, 1]`. -/
theorem ex_12_1 {N : ℕ} (hN : 0 < N) (x : Fin N → Bool) :
    ((ml_heads x : ℝ) / N ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        ml_likelihood ml_coinDensity x p ≤
          ml_likelihood ml_coinDensity x ((ml_heads x : ℝ) / N) := by
  have hk : ml_heads x ≤ N := by
    unfold ml_heads
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨by positivity, (div_le_one hN').2 (by exact_mod_cast hk)⟩, fun p hp => ?_⟩
  rw [ex_12_1_likelihood, ex_12_1_likelihood]
  exact ml_binomial_lik_le N _ hN hk p hp.1 hp.2

/-- The mean of a `{0, 1}`-valued random variable is the probability of `1`. -/
theorem ml_integral_of_zero_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ01 : ∀ ω, Z ω = 0 ∨ Z ω = 1) (hmeas : Measurable Z) :
    ∫ ω, Z ω ∂P = P.real {ω | Z ω = 1} ∧ ∫ ω, Z ω ^ 2 ∂P = P.real {ω | Z ω = 1} := by
  have hset : MeasurableSet {ω | Z ω = 1} := hmeas (measurableSet_singleton 1)
  have hZ : Z = Set.indicator {ω | Z ω = 1} 1 := by
    funext ω
    rcases hZ01 ω with h | h
    · rw [Set.indicator_of_notMem (by simp [h]), h]
    · rw [Set.indicator_of_mem (by simp [h]), h]; rfl
  have hZ2 : (fun ω => Z ω ^ 2) = Z := by
    funext ω
    rcases hZ01 ω with h | h <;> simp [h]
  rw [hZ2]
  have : ∫ ω, Z ω ∂P = P.real {ω | Z ω = 1} := by
    conv_lhs => rw [hZ]
    exact integral_indicator_one hset
  exact ⟨this, this⟩

/-- **Exercise 12.1**, consistency (Miao, p. 397, "Consistency"): for i.i.d. tosses `Xᵢ ∈ {0, 1}`
with `P(Xᵢ = 1) = p`, the ML estimates `p̂_N = (1/N) ∑_{i<N} Xᵢ` converge to `p` almost surely
(Mathlib's strong law of large numbers). -/
theorem ex_12_1_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (p : ℝ) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmeas : Measurable (X 0)) (hp : P.real {ω | X 0 ω = 1} = p)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 p) := by
  have hint : Integrable (X 0) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rcases hX01 0 ω with h | h <;> simp [h])
  have hmean : ∫ ω, X 0 ω ∂P = p :=
    (ml_integral_of_zero_one (P := P) (X 0) (hX01 0) hmeas).1.trans hp
  have := strong_law_ae_real X hint hindep hident
  rw [hmean] at this
  exact this

/-- `√n (S/n − m) = (√n)⁻¹ (S − n m)` (both sides vanish at `n = 0`). -/
theorem ml_sqrt_mul_mean_sub (n : ℕ) (S m : ℝ) :
    Real.sqrt n * (S / n - m) = (Real.sqrt n)⁻¹ * (S - n * m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  set s := Real.sqrt (n : ℝ)
  rw [← hsq]
  field_simp

/-- **Exercise 12.1**, asymptotic normality (Miao, p. 397): for i.i.d. tosses with
`P(Xᵢ = 1) = p`, `√N(p̂_N − p) ⇒ N(0, p(1 − p))`; here `p(1 − p) = I(p)⁻¹`, the inverse Fisher
information of one toss (`ml_cramer_rao_bernoulli`). Mathlib's central limit theorem. -/
theorem ex_12_1_asymptotic {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (p : ℝ) (Y : Ω' → ℝ) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmeas : Measurable (X 0)) (hp : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY : HasLaw Y (gaussianReal 0 (p * (1 - p)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
      ((∑ i ∈ Finset.range n, X i ω) / n - p)) atTop Y (fun _ => P) P' := by
  obtain ⟨h1, h2⟩ := ml_integral_of_zero_one (P := P) (X 0) (hX01 0) hmeas
  have hL2 : MemLp (X 0) 2 P :=
    MemLp.of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rcases hX01 0 ω with h | h <;> simp [h])
  have hvar : Var[X 0; P] = p * (1 - p) := by
    rw [variance_eq_sub hL2]
    simp only [Pi.pow_apply]
    rw [h1, h2, hp]
    ring
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (P' := P') (X := X) (Y := Y)
    (by rw [hvar]; exact hY) hL2 hindep hident
  rw [h1, hp] at hclt
  have hfun : (fun (n : ℕ) ω => Real.sqrt n * ((∑ i ∈ Finset.range n, X i ω) / n - p)) =
      fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * (∑ i ∈ Finset.range n, X i ω - n * p) := by
    funext n ω
    exact ml_sqrt_mul_mean_sub n _ p
  rw [hfun]
  exact hclt

/-- The exponential density of Exercise 12.2, `f(x, θ) = θ exp(−xθ)`. -/
noncomputable def ml_expDensity (x θ : ℝ) : ℝ := θ * Real.exp (-(x * θ))

/-- **Exercise 12.2** (Miao, p. 408): the likelihood of a sample from `f(x) = θe^{−xθ}` is
`L(θ) = θᴺ exp(−θ ∑ₜ xₜ)`. -/
theorem ex_12_2_likelihood {N : ℕ} (x : Fin N → ℝ) (θ : ℝ) :
    ml_likelihood ml_expDensity x θ = θ ^ N * Real.exp (-(θ * ∑ t, x t)) := by
  unfold ml_likelihood ml_expDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **Exercise 12.2** (Miao, p. 408): the log-likelihood is `N ln θ − θ ∑ₜ xₜ` for `θ > 0`. -/
theorem ex_12_2_logLikelihood {N : ℕ} (x : Fin N → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ml_logLikelihood ml_expDensity x θ = N * Real.log θ - θ * ∑ t, x t := by
  rw [← eq_ml_log_likelihood _ _ _ (fun t => by unfold ml_expDensity; positivity),
    ex_12_2_likelihood, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp]
  ring

/-- **Exercise 12.2** (Miao, p. 408): for a sample with `∑ₜ xₜ > 0`, the ML estimator of `θ` is
`θ̂ = N/∑ₜ xₜ = 1/x̄`: it is positive and maximises the likelihood over `θ > 0`. -/
theorem ex_12_2 {N : ℕ} (x : Fin N → ℝ) (hS : 0 < ∑ t, x t) :
    let θhat := (N : ℝ) / ∑ t, x t
    0 < θhat ∧ θhat = 1 / ((∑ t, x t) / N) ∧
      IsMaxOn (ml_likelihood ml_expDensity x) (Set.Ioi 0) θhat := by
  intro θhat
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hS
    · exact h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < θhat := div_pos hN' hS
  refine ⟨hpos, by simp only [θhat]; field_simp, ?_⟩
  intro θ hθ
  have hθ' : 0 < θ := hθ
  change ml_likelihood ml_expDensity x θ ≤ ml_likelihood ml_expDensity x θhat
  have hLpos : ∀ η, 0 < η → 0 < ml_likelihood ml_expDensity x η := fun η hη => by
    rw [ex_12_2_likelihood]; positivity
  rw [← Real.log_le_log_iff (hLpos θ hθ') (hLpos θhat hpos),
    eq_ml_log_likelihood _ _ _ (fun t => by unfold ml_expDensity; positivity),
    eq_ml_log_likelihood _ _ _ (fun t => by unfold ml_expDensity; positivity),
    ex_12_2_logLikelihood x hθ', ex_12_2_logLikelihood x hpos]
  have hlog : Real.log θ - Real.log θhat ≤ θ / θhat - 1 := by
    rw [← Real.log_div hθ'.ne' hpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hθ' hpos)
  have key : (N : ℝ) * (θ / θhat - 1) = θ * ∑ t, x t - θhat * ∑ t, x t := by
    simp only [θhat]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hN'.le]

/-- **Exercise 12.2**, Fisher information (Miao, p. 398): for `θ > 0` the score of one
observation is `∂ ln f(x, θ)/∂θ = 1/θ − x` and `∂² ln f(x, θ)/∂θ² = −1/θ²`, so
`I(θ) = −E[∂² ln f/∂θ²] = 1/θ²`. -/
theorem ex_12_2_fisher (x : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun η => Real.log (ml_expDensity x η)) (1 / θ - x) θ ∧
      HasDerivAt (fun η => 1 / η - x) (-(1 / θ ^ 2)) θ := by
  constructor
  · have h1 : HasDerivAt (fun η => η * Real.exp (-(x * η)))
        (1 * Real.exp (-(x * θ)) + θ * (Real.exp (-(x * θ)) * (-(x * 1)))) θ :=
      (hasDerivAt_id θ).mul (((hasDerivAt_id θ).const_mul x).neg.exp)
    have h2 := h1.log (by positivity)
    unfold ml_expDensity
    convert h2 using 1
    field_simp
    ring
  · have := ((hasDerivAt_id θ).inv hθ.ne').sub_const x
    convert this using 1
    · funext η; simp [one_div]
    · simp only [id]; ring

/-- Convergence in distribution is unchanged by changing each random variable on a null set. -/
theorem ml_tendstoInDistribution_congr_ae {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X X' : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => P) P') (hae : ∀ n, X n =ᵐ[P] X' n) :
    TendstoInDistribution X' atTop Z (fun _ => P) P' where
  forall_aemeasurable n := (h.forall_aemeasurable n).congr (hae n)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine h.tendsto.congr' (Eventually.of_forall fun n => ?_)
    exact Subtype.ext (Measure.map_congr (hae n))

/-- **Exercise 12.2**, consistency (Miao, p. 397): for i.i.d. `Xᵢ ~ θe^{−θx}`, the ML estimates
`θ̂_N = N/∑_{i<N} Xᵢ` converge to `θ` almost surely (strong law and continuity of `x ↦ 1/x` at
`1/θ`). -/
theorem ex_12_2_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure θ) P)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ) / ∑ i ∈ Finset.range n, X i ω) atTop (𝓝 θ) := by
  have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  have hint : Integrable (X 0) P := (hlaw 0).integrable (by
    have := ml_integrable_expMeasure_pow hθ 1
    simp only [pow_one] at this
    exact this)
  have hmean : ∫ ω, X 0 ω ∂P = 1 / θ := by
    rw [(hlaw 0).integral_eq, ml_mean_expMeasure hθ]
  filter_upwards [strong_law_ae_real X hint hindep hident] with ω hω
  rw [hmean] at hω
  have := hω.inv₀ (by positivity)
  simp only [one_div, inv_inv] at this
  convert this using 2 with n
  rw [inv_div]

/-- **Exercise 12.2**, the asymptotic distribution (Miao, p. 408; p. 397 for the general claim):
for i.i.d. `Xᵢ ~ θe^{−θx}`, the ML estimator `θ̂_N = N/∑_{i<N} Xᵢ` satisfies
`√N(θ̂_N − θ) ⇒ N(0, θ²)`, and `θ² = I(θ)⁻¹` (`ex_12_2_fisher`). Proof: the central limit
theorem gives `√N(x̄_N − 1/θ) ⇒ N(0, 1/θ²)`; `θ̂_N → θ` in probability; and
`√N(θ̂_N − θ) = −θ · √N(x̄_N − 1/θ) · θ̂_N` whenever `x̄_N > 0`, so Slutsky's theorem
(the delta method) gives the limit `−θ² · N(0, 1/θ²) = N(0, θ²)`. -/
theorem ex_12_2_asymptotic {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) {θ : ℝ} (hθ : 0 < θ) (Y : Ω' → ℝ)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure θ) P) (hindep : iIndepFun X P)
    (hY : HasLaw Y (gaussianReal 0 (θ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
      ((n : ℝ) / (∑ i ∈ Finset.range n, X i ω) - θ)) atTop Y (fun _ => P) P' := by
  have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  have hL2 : MemLp (X 0) 2 P := (hlaw 0).memLp (ml_memLp_two_expMeasure hθ)
  have hmean : P[X 0] = 1 / θ := by rw [(hlaw 0).integral_eq, ml_mean_expMeasure hθ]
  have hvar : Var[X 0; P] = 1 / θ ^ 2 := by
    rw [(hlaw 0).variance_eq]; exact ml_variance_expMeasure hθ
  -- the limit of the CLT: `Z = −Y/θ² ~ N(0, 1/θ²)`
  set c : ℝ := -(θ ^ 2)⁻¹ with hc
  have hZ : HasLaw (fun ω => c * Y ω) (gaussianReal 0 Var[X 0; P].toNNReal) P' := by
    have hmul : HasLaw (fun x : ℝ => c * x) (gaussianReal 0 Var[X 0; P].toNNReal)
        (gaussianReal 0 (θ ^ 2).toNNReal) := by
      refine ⟨(measurable_const_mul c).aemeasurable, ?_⟩
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      rw [hvar]
      ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal', hc]
      rw [max_eq_left (by positivity), max_eq_left (by positivity)]
      field_simp
    exact hmul.comp hY
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (P' := P') (X := X)
    (Y := fun ω => c * Y ω) hZ hL2 hindep hident
  rw [hmean] at hclt
  -- `θ̂_N → θ` in probability
  have hcons := ex_12_2_consistent X hθ hlaw fun i j hij => hindep.indepFun hij
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hlaw i).aemeasurable
  have hYm : ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ) / ∑ i ∈ Finset.range n, X i ω) P :=
    fun n => aemeasurable_const.div (Finset.aemeasurable_fun_sum _ fun i _ => hXm i)
  have hprob : TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ) / ∑ i ∈ Finset.range n, X i ω)
      atTop (fun _ => θ) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hYm n).aestronglyMeasurable) hcons
  -- Slutsky with `g(z, y) = −θ z y`
  have hsl := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun q : ℝ × ℝ => -θ * q.1 * q.2) (by fun_prop) hprob hYm
  have hlim : (fun ω => -θ * (c * Y ω) * θ) = Y := by
    funext ω
    simp only [hc]
    field_simp
  dsimp only at hsl
  rw [hlim] at hsl
  refine ml_tendstoInDistribution_congr_ae hsl fun n => ?_
  -- equality off the null set where some `Xᵢ ≤ 0`
  have hpos : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω := by
    rw [ae_all_iff]
    intro i
    have h0 : P (X i ⁻¹' Set.Iic 0) = 0 := by
      rw [← Measure.map_apply_of_aemeasurable (hXm i) measurableSet_Iic, (hlaw i).map_eq]
      have hcdf := cdf_expMeasure_eq hθ 0
      rw [cdf_eq_real] at hcdf
      simp only [le_refl, ↓reduceIte, mul_zero, neg_zero, Real.exp_zero, sub_self] at hcdf
      exact (measureReal_eq_zero_iff).1 hcdf
    have := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with ω hω
    simpa using hω
  filter_upwards [hpos] with ω hω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hS : 0 < ∑ i ∈ Finset.range n, X i ω :=
    Finset.sum_pos (fun i _ => hω i) (Finset.nonempty_range_iff.2 hn.ne')
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  set s := Real.sqrt (n : ℝ)
  rw [← hsq]
  field_simp
  ring

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The job search likelihood (Examples 12.2.1, 12.3.1; Exercises 12.3–12.4)

Miao, §12.2, Example 12.2.1, pp. 396–397; §12.3, Example 12.3.1, p. 400; Exercises 12.3 and
12.4, pp. 408–409. McCall's model (Miao §8.1) is copied in `MLODMcCall`: the worker accepts
the offer `w` iff `w ≥ w*`, the reservation wage.

* `ml_firstPassage_iid` (Example 12.3.1, the i.i.d. case, and Example 12.2.1): if the offers
  `w₁, w₂, …` are i.i.d. with law `F` and `A` is the acceptance set, the probability of
  rejecting `n` offers and accepting the `(n + 1)`-th is `F(Aᶜ)ⁿ F(A)`.
* `example_12_2_1_duration` (Example 12.2.1): with `A = [w*, ∞)`, the probability of accepting a
  job for the first time after `t` periods is `Lᵢ = (1 − q) qᵗ⁻¹`, `q = F((−∞, w*))`;
  `ml_reject_prob_eq_cdf`: `q = F(w*)` (the book's expression) when `F` has no atom at `w*`.
* `example_12_2_1` (Example 12.2.1): the sample likelihood `L = ∏ᵢ (1 − q) q^{tᵢ − 1}` equals
  `(1 − q)ᴺ q^{∑(tᵢ − 1)}`; it depends on the structural parameters `θ` only through the
  reservation wage `w*(θ)`; and as a function of `q` it is maximised at
  `q̂ = ∑(tᵢ − 1)/∑ tᵢ`.
* `ml_resWage_mono_beta` (the content of Exercise 12.3): the McCall reservation wage is
  nondecreasing in the discount factor `β`, and `ml_resWage_strictMono_beta` strictly increasing
  when offers above it have positive probability; so `β` moves the likelihood through `w*(β)`.
* `ex_12_4_moments` (the content of Exercise 12.4): the duration `D` with
  `P(D = n + 1) = qⁿ(1 − q)` has `P(D = 1) = 1 − q`, `P(D ≤ 2) = 1 − q²`,
  `E D = 1/(1 − q)`, `E D² = (1 + q)/(1 − q)²` and `Var D = q/(1 − q)²`: the moments used for
  SMM in Example 12.3.2.

Departures. The book writes the rejection probability as `F(w*)`; with acceptance iff
`w ≥ w*` it is `F((−∞, w*))`, equal to `F(w*)` when `F` has no atom at `w*`
(`ml_reject_prob_eq_cdf`). Example 12.3.1 writes `wₜ > w*` for acceptance, which agrees with
Example 12.2.1's `w ≥ w*` under the same condition; `ml_firstPassage_iid` covers both. The
lognormal offer distribution of Exercise 12.3 is not concentrated on a bounded interval, as the
copied McCall model requires; the monotonicity result is proved for offers on `[0, B]`.
Simulation and plotting in Exercises 12.3–12.4 are computational and not formalised.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

/-- The event that offers `0, …, n − 1` are rejected and offer `n` is accepted (offer `i` is the
offer of period `i + 1`), with acceptance set `A`. -/
def ml_firstPassage {Ω : Type*} (w : ℕ → Ω → ℝ) (A : Set ℝ) (n : ℕ) : Set Ω :=
  {ω | (∀ i < n, w i ω ∉ A) ∧ w n ω ∈ A}

/-- Miao, Example 12.3.1, p. 400 (i.i.d. case) and Example 12.2.1, p. 397: if the offers are
i.i.d. with law `F` and `A` is the (measurable) acceptance set, the probability of waiting
exactly `n + 1` periods is `F(Aᶜ)ⁿ F(A)`. -/
theorem ml_firstPassage_iid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → Ω → ℝ) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hindep : iIndepFun w P) (hlaw : ∀ i, HasLaw (w i) F P) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) : P.real (ml_firstPassage w A n) = F.real Aᶜ ^ n * F.real A := by
  classical
  let sets : ℕ → Set ℝ := fun i => if i < n then Aᶜ else A
  have hsets : ∀ i, MeasurableSet (sets i) := fun i => by
    simp only [sets]; split_ifs
    · exact hA.compl
    · exact hA
  have hev : ml_firstPassage w A n = ⋂ i ∈ Finset.range (n + 1), w i ⁻¹' sets i := by
    ext ω
    simp only [ml_firstPassage, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage, sets]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      split_ifs with h
      · exact h1 i h
      · rw [show i = n by omega]; exact h2
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i (by omega)
        simp only [hi, ↓reduceIte] at this
        exact this
      · have := h n (by omega)
        simp only [lt_irrefl, ↓reduceIte] at this
        exact this
  have hprod := hindep.measure_inter_preimage_eq_mul (Finset.range (n + 1))
    (sets := sets) fun i _ => hsets i
  have hlawi : ∀ i, P (w i ⁻¹' sets i) = F (sets i) := fun i => by
    rw [← Measure.map_apply_of_aemeasurable (hlaw i).aemeasurable (hsets i), (hlaw i).map_eq]
  rw [hev, measureReal_def, hprod, Finset.prod_range_succ]
  simp only [hlawi]
  rw [Finset.prod_congr rfl fun i hi => (by
    simp only [sets, Finset.mem_range.1 hi, ↓reduceIte] : F (sets i) = F Aᶜ)]
  simp only [sets, lt_irrefl, ↓reduceIte, Finset.prod_const, Finset.card_range,
    ENNReal.toReal_mul, ENNReal.toReal_pow, measureReal_def]

/-- Miao, Example 12.2.1, p. 397: with acceptance iff `w ≥ w*`, the probability that a worker
accepts a job for the first time after `t = n + 1` periods is `(1 − q) qⁿ` with
`q = F((−∞, w*))`. -/
theorem example_12_2_1_duration {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → Ω → ℝ) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hindep : iIndepFun w P) (hlaw : ∀ i, HasLaw (w i) F P) (wstar : ℝ) (n : ℕ) :
    P.real {ω | (∀ i < n, w i ω < wstar) ∧ wstar ≤ w n ω} =
      (1 - F.real (Set.Iio wstar)) * F.real (Set.Iio wstar) ^ n := by
  have h := ml_firstPassage_iid w F hindep hlaw (measurableSet_Ici (a := wstar)) n
  have hev : ml_firstPassage w (Set.Ici wstar) n =
      {ω | (∀ i < n, w i ω < wstar) ∧ wstar ≤ w n ω} := by
    ext ω; simp [ml_firstPassage]
  rw [hev, Set.compl_Ici, ← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio] at h
  rw [h]
  ring

/-- Miao, Example 12.2.1, p. 397: the rejection probability `F((−∞, w*))` equals the book's
`F(w*)` (the distribution function at `w*`) when `F` has no atom at `w*`. -/
theorem ml_reject_prob_eq_cdf (F : Measure ℝ) [IsProbabilityMeasure F] (wstar : ℝ)
    (hatom : F {wstar} = 0) : F.real (Set.Iio wstar) = cdf F wstar := by
  rw [cdf_eq_real, ← Set.Iio_union_right, measureReal_union (by simp) (measurableSet_singleton _),
    measureReal_def F {wstar}, hatom, ENNReal.toReal_zero, add_zero]

/-- The job search likelihood of Example 12.2.1 as a function of the rejection probability
`q`: `L(q) = ∏ᵢ (1 − q) q^{tᵢ − 1}` for the observed durations `t₁, …, t_N`. -/
def ml_durationLik {N : ℕ} (t : Fin N → ℕ) (q : ℝ) : ℝ := ∏ i, (1 - q) * q ^ (t i - 1)

/-- **Example 12.2.1** (Miao, pp. 396–397). Let `w*(θ)` be the reservation wage at the
structural parameter `θ` (e.g. `θ = (c, β)`) and `q(θ) = F((−∞, w*(θ)))`; the likelihood of
the durations `t₁, …, t_N ≥ 1` is `L(θ) = ∏ᵢ (1 − F(w*(θ))) F(w*(θ))^{tᵢ − 1}`. Then
1. `L(θ) = (1 − q)ᴺ q^{∑ᵢ (tᵢ − 1)}`;
2. `L` depends on `θ` only through `w*(θ)`: `w*(θ₁) = w*(θ₂) ⇒ L(θ₁) = L(θ₂)`;
3. as a function of `q ∈ [0, 1]` it is maximised at `q̂ = ∑ᵢ (tᵢ − 1)/∑ᵢ tᵢ`. -/
theorem example_12_2_1 {Θ : Type*} (F : Measure ℝ) (wstar : Θ → ℝ) {N : ℕ} (hN : 0 < N)
    (t : Fin N → ℕ) (ht : ∀ i, 1 ≤ t i) :
    (∀ θ, ml_durationLik t (F.real (Set.Iio (wstar θ))) =
      (1 - F.real (Set.Iio (wstar θ))) ^ N *
        F.real (Set.Iio (wstar θ)) ^ (∑ i, (t i - 1))) ∧
      (∀ θ₁ θ₂, wstar θ₁ = wstar θ₂ → ml_durationLik t (F.real (Set.Iio (wstar θ₁))) =
        ml_durationLik t (F.real (Set.Iio (wstar θ₂)))) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1, ml_durationLik t q ≤
        ml_durationLik t (((∑ i, (t i - 1) : ℕ) : ℝ) / ((∑ i, t i : ℕ) : ℝ)) := by
  have hform : ∀ q, ml_durationLik t q = (1 - q) ^ N * q ^ (∑ i, (t i - 1)) := fun q => by
    unfold ml_durationLik
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow_eq_pow_sum]
  refine ⟨fun θ => hform _, fun θ₁ θ₂ h => by rw [h], fun q hq => ?_⟩
  set k := ∑ i, (t i - 1)
  set n := ∑ i, t i
  have hkn : k + N = n := by
    simp only [k, n]
    have : ∀ i, t i - 1 + 1 = t i := fun i => Nat.sub_add_cancel (ht i)
    calc ∑ i, (t i - 1) + N = ∑ i, (t i - 1 + 1) := by
          rw [Finset.sum_add_distrib]; simp
      _ = ∑ i, t i := Finset.sum_congr rfl fun i _ => this i
  have hnpos : 0 < n := by omega
  have hb := ml_binomial_lik_le n k hnpos (by omega) q hq.1 hq.2
  rw [hform, hform, mul_comm, mul_comm ((1 - _) ^ N)]
  rw [show n - k = N by omega] at hb
  exact hb

/-- The function `ψ_β(x) = x − c − β/(1 − β) ∫_{w > x} (w − x) dF` whose root is the McCall
reservation wage (`ml_od_mccall_reservation`). -/
theorem ml_mccall_psi_root {F : Measure ℝ} [IsProbabilityMeasure F] {B c β : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) {V : ℝ → ℝ}
    (hV : ml_od_McCallBellman F B c β V) (x : ℝ) :
    ml_od_firingψ F c 0 β x = 0 ↔ x = (1 - β) * (c + β * ∫ w, V w ∂F) :=
  ml_ex_8_2_root_unique hF hβ0 hβ1 le_rfl ((ml_od_mccall_iff_firing hβ1 V).1 hV) x

/-- The content of **Exercise 12.3** (Miao, p. 408): the McCall reservation wage
`w*(β) = (1 − β)(c + β ∫ V dF)` is nondecreasing in the discount factor `β`, for offers on
`[0, B]`. So the likelihood of Example 12.2.1 varies with `β` only through `q(β) = F(w*(β))`. -/
theorem ml_resWage_mono_beta {F : Measure ℝ} [IsProbabilityMeasure F] {B c β₁ β₂ : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ₁0 : 0 < β₁) (h12 : β₁ ≤ β₂) (hβ₂1 : β₂ < 1)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ml_od_McCallBellman F B c β₁ V₁)
    (hV₂ : ml_od_McCallBellman F B c β₂ V₂) :
    (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F) ≤ (1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F) := by
  have hβ₁1 : β₁ < 1 := lt_of_le_of_lt h12 hβ₂1
  have hβ₂0 : 0 < β₂ := lt_of_lt_of_le hβ₁0 h12
  set x₁ := (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)
  have h1 : ml_od_firingψ F c 0 β₁ x₁ = 0 := (ml_mccall_psi_root hF hβ₁0 hβ₁1 hV₁ x₁).2 rfl
  have h3 := (ml_mccall_psi_root hF hβ₂0 hβ₂1 hV₂ ((1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F))).2 rfl
  have hcoef : β₁ / (1 - β₁ + 0 * β₁) ≤ β₂ / (1 - β₂ + 0 * β₂) := by
    simp only [zero_mul, add_zero]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hint : 0 ≤ ∫ w in Set.Ioi x₁, (w - x₁) ∂F := by
    rw [ml_od_setIntegral_Ioi_eq]; exact integral_nonneg fun _ => le_max_right _ _
  have h2 : ml_od_firingψ F c 0 β₂ x₁ ≤ 0 := by
    unfold ml_od_firingψ at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcoef hint]
  exact (ml_od_firingψ_strictMono hF hβ₂0 hβ₂1 le_rfl).le_iff_le.1 (by rw [h3]; exact h2)

/-- The content of **Exercise 12.3** (Miao, p. 408): if `β₁ < β₂` and offers above the
reservation wage `w*(β₁)` have positive expected surplus, `∫_{w > w*(β₁)} (w − w*(β₁)) dF > 0`,
then `w*(β₁) < w*(β₂)`. -/
theorem ml_resWage_strictMono_beta {F : Measure ℝ} [IsProbabilityMeasure F] {B c β₁ β₂ : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ₁0 : 0 < β₁) (h12 : β₁ < β₂) (hβ₂1 : β₂ < 1)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ml_od_McCallBellman F B c β₁ V₁)
    (hV₂ : ml_od_McCallBellman F B c β₂ V₂)
    (hpos : 0 < ∫ w in Set.Ioi ((1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)),
      (w - (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)) ∂F) :
    (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F) < (1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F) := by
  have hβ₁1 : β₁ < 1 := lt_trans h12 hβ₂1
  have hβ₂0 : 0 < β₂ := lt_trans hβ₁0 h12
  set x₁ := (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)
  have h1 : ml_od_firingψ F c 0 β₁ x₁ = 0 := (ml_mccall_psi_root hF hβ₁0 hβ₁1 hV₁ x₁).2 rfl
  have h3 := (ml_mccall_psi_root hF hβ₂0 hβ₂1 hV₂ ((1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F))).2 rfl
  have hcoef : β₁ / (1 - β₁ + 0 * β₁) < β₂ / (1 - β₂ + 0 * β₂) := by
    simp only [zero_mul, add_zero]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : ml_od_firingψ F c 0 β₂ x₁ < 0 := by
    unfold ml_od_firingψ at h1 ⊢
    nlinarith [mul_lt_mul_of_pos_right hcoef hpos]
  exact (ml_od_firingψ_strictMono hF hβ₂0 hβ₂1 le_rfl).lt_iff_lt.1 (by rw [h3]; exact h2)

/-- The content of **Exercise 12.4** (Miao, p. 409) and Example 12.3.2: for the duration `D`
with `P(D = n + 1) = qⁿ(1 − q)`, `0 ≤ q < 1`: the probabilities sum to one,
`P(D = 1) = 1 − q`, `P(D ≤ 2) = 1 − q²`, `E D = 1/(1 − q)`, `E D² = (1 + q)/(1 − q)²` and
`Var D = E D² − (E D)² = q/(1 − q)²`. -/
theorem ex_12_4_moments {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ n * (1 - q)) 1 ∧
      q ^ 0 * (1 - q) = 1 - q ∧ q ^ 0 * (1 - q) + q ^ 1 * (1 - q) = 1 - q ^ 2 ∧
      HasSum (fun n : ℕ => ((n : ℝ) + 1) * (q ^ n * (1 - q))) (1 / (1 - q)) ∧
      HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * (q ^ n * (1 - q))) ((1 + q) / (1 - q) ^ 2) ∧
      (1 + q) / (1 - q) ^ 2 - (1 / (1 - q)) ^ 2 = q / (1 - q) ^ 2 := by
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hne : 1 - q ≠ 0 := by linarith
  have h0 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 0 hnorm
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero] at h0
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] at h1
  simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat] at h2
  refine ⟨?_, by ring, by ring, ?_, ?_, ?_⟩
  · have := h0.mul_right (1 - q)
    convert this using 1
    simp only [zero_add, pow_one]
    field_simp
  · have := h1.mul_right (1 - q)
    convert this using 1
    · funext n; ring
    · field_simp
  · -- `(n + 1)² = 2 · C(n + 2, 2) − (n + 1)`
    have := ((h2.mul_left 2).sub h1).mul_right (1 - q)
    convert this using 1
    · funext n; ring
    · field_simp
      ring
  · field_simp
    ring

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sandwich covariance matrices and the optimal weighting matrix

Matrix algebra behind the asymptotic variances of §12.3 (Miao, pp. 402 and 406–407): for a
`q × k` Jacobian `B`, a long-run covariance `Ω` and a symmetric weighting matrix `W`, the GMM-type
estimator has the sandwich variance
`V(W) = (BᵀWB)⁻¹ BᵀWΩWB (BᵀWB)⁻¹` (`ml_sandwich`).

* `ml_sandwich_inv`: for `W = (aΩ)⁻¹`, `a ≠ 0`, the sandwich collapses to `(BᵀΩ⁻¹B)⁻¹`.
* `ml_sandwich_optimal`: `V(W) − (BᵀΩ⁻¹B)⁻¹` is positive semidefinite for every symmetric `W`
  with `BᵀWB` invertible, so `W ∝ Ω⁻¹` is optimal. Proof: with `H = (BᵀWB)⁻¹BᵀW` and
  `G = (BᵀΩ⁻¹B)⁻¹BᵀΩ⁻¹`, `V(W) − (BᵀΩ⁻¹B)⁻¹ = (H − G) Ω (H − G)ᵀ`.

These are the specific algebraic facts §12.3 needs from the GMM theory of §12.1 (proved here,
not imported).
-/

namespace Miao.StructuralEstimation

open Matrix

/-- The sandwich variance `(BᵀWB)⁻¹ BᵀWΩWB (BᵀWB)⁻¹`. -/
noncomputable def ml_sandwich {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n ℝ) (Ω W : Matrix m m ℝ) : Matrix n n ℝ :=
  (Bᵀ * W * B)⁻¹ * (Bᵀ * W * Ω * W * B) * (Bᵀ * W * B)⁻¹

/-- `(aΩ)⁻¹ = a⁻¹ Ω⁻¹` for `a ≠ 0` and invertible `Ω`. -/
theorem ml_inv_smul {m : Type*} [Fintype m] [DecidableEq m] (Ω : Matrix m m ℝ)
    (hΩ : IsUnit Ω.det) {a : ℝ} (ha : a ≠ 0) : (a • Ω)⁻¹ = a⁻¹ • Ω⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul,
    Matrix.nonsing_inv_mul _ hΩ]

/-- With `W = (aΩ)⁻¹` (`a ≠ 0`) the sandwich collapses: `V(W) = (BᵀΩ⁻¹B)⁻¹`. -/
theorem ml_sandwich_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℝ) (Ω : Matrix m m ℝ) (hΩ : IsUnit Ω.det)
    (hM : IsUnit (Bᵀ * Ω⁻¹ * B).det) {a : ℝ} (ha : a ≠ 0) :
    ml_sandwich B Ω (a • Ω)⁻¹ = (Bᵀ * Ω⁻¹ * B)⁻¹ := by
  set M := Bᵀ * Ω⁻¹ * B with hMdef
  have hA : Bᵀ * (a • Ω)⁻¹ * B = a⁻¹ • M := by
    rw [ml_inv_smul Ω hΩ ha, Matrix.mul_smul, Matrix.smul_mul]
  have hMid : Bᵀ * (a • Ω)⁻¹ * Ω * (a • Ω)⁻¹ * B = (a⁻¹ * a⁻¹) • M := by
    rw [ml_inv_smul Ω hΩ ha]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    rw [hMdef, Matrix.mul_assoc (Bᵀ * Ω⁻¹) Ω, Matrix.mul_nonsing_inv _ hΩ, Matrix.mul_one]
  have hAinv : (a⁻¹ • M)⁻¹ = a • M⁻¹ := by
    rw [ml_inv_smul M hM (inv_ne_zero ha), inv_inv]
  unfold ml_sandwich
  rw [hA, hMid, hAinv]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
  have : a * (a⁻¹ * a⁻¹ * a) = 1 := by field_simp
  rw [this, one_smul]

/-- The optimal weighting matrix (Miao, pp. 402 and 407): for `Ω` positive semidefinite and
invertible and any symmetric `W` with `BᵀWB` invertible, `V(W) − (BᵀΩ⁻¹B)⁻¹` is positive
semidefinite; by `ml_sandwich_inv` the lower bound is attained at `W ∝ Ω⁻¹`. -/
theorem ml_sandwich_optimal {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (B : Matrix m n ℝ) (Ω W : Matrix m m ℝ) (hΩ : Ω.PosSemidef)
    (hΩu : IsUnit Ω.det) (hW : Wᵀ = W) (hA : IsUnit (Bᵀ * W * B).det)
    (hM : IsUnit (Bᵀ * Ω⁻¹ * B).det) :
    (ml_sandwich B Ω W - (Bᵀ * Ω⁻¹ * B)⁻¹).PosSemidef := by
  set A := Bᵀ * W * B with hAdef
  set M := Bᵀ * Ω⁻¹ * B with hMdef
  have hΩt : Ωᵀ = Ω := by
    have := hΩ.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hΩit : (Ω⁻¹)ᵀ = Ω⁻¹ := by rw [transpose_nonsing_inv, hΩt]
  have hAt : Aᵀ = A := by
    rw [hAdef, transpose_mul, transpose_mul, transpose_transpose, hW, Matrix.mul_assoc]
  have hMt : Mᵀ = M := by
    rw [hMdef, transpose_mul, transpose_mul, transpose_transpose, hΩit, Matrix.mul_assoc]
  have hAit : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAt]
  have hMit : (M⁻¹)ᵀ = M⁻¹ := by rw [transpose_nonsing_inv, hMt]
  set H := A⁻¹ * Bᵀ * W with hH
  set G := M⁻¹ * Bᵀ * Ω⁻¹ with hG
  have hHt : Hᵀ = W * B * A⁻¹ := by
    rw [hH, transpose_mul, transpose_mul, transpose_transpose, hW, hAit, Matrix.mul_assoc]
  have hGt : Gᵀ = Ω⁻¹ * B * M⁻¹ := by
    rw [hG, transpose_mul, transpose_mul, transpose_transpose, hΩit, hMit, Matrix.mul_assoc]
  have hΩΩ : Ω * Ω⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΩu
  have hΩΩ' : Ω⁻¹ * Ω = 1 := Matrix.nonsing_inv_mul _ hΩu
  have h1 : H * Ω * Hᵀ = ml_sandwich B Ω W := by
    rw [hHt, hH, ml_sandwich, ← hAdef]
    simp only [Matrix.mul_assoc]
  have h2 : H * Ω * Gᵀ = M⁻¹ := by
    rw [hGt, hH]
    calc A⁻¹ * Bᵀ * W * Ω * (Ω⁻¹ * B * M⁻¹)
        = A⁻¹ * (Bᵀ * W * (Ω * Ω⁻¹) * B) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ := by
        rw [hΩΩ, Matrix.mul_one, ← hAdef, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  have h3 : G * Ω * Hᵀ = M⁻¹ := by
    rw [hHt, hG]
    calc M⁻¹ * Bᵀ * Ω⁻¹ * Ω * (W * B * A⁻¹)
        = M⁻¹ * (Bᵀ * (Ω⁻¹ * Ω) * W * B) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ := by
        rw [hΩΩ', Matrix.mul_one, ← hAdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
          Matrix.mul_one]
  have h4 : G * Ω * Gᵀ = M⁻¹ := by
    rw [hGt, hG]
    calc M⁻¹ * Bᵀ * Ω⁻¹ * Ω * (Ω⁻¹ * B * M⁻¹)
        = M⁻¹ * (Bᵀ * (Ω⁻¹ * Ω) * Ω⁻¹ * B) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ := by
        rw [hΩΩ', Matrix.mul_one, ← hMdef, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
  have key : (H - G) * Ω * (H - G)ᴴ = ml_sandwich B Ω W - M⁻¹ := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    abel
  rw [← key]
  exact hΩ.mul_mul_conjTranspose_same (H - G)

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The simulated method of moments (§12.3.1)

Miao, §12.3.1, pp. 400–403, equation (12.5) and the asymptotic properties of SMM. Data
`x₁, …, x_T`; for each `θ`, `S` simulated paths `x_t^s(θ)`; moments `m(x) ∈ ℝ^q`.

* `ml_smmObjective`, `eq_12_5`: the SMM objective
  `[∑ₜ (m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ)))]ᵀ W [∑ₜ (…)]` is `T² g_T(θ)ᵀ W g_T(θ)` for the GMM moment
  function `h(xₜ, θ) = m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ))` of (12.5), so SMM is the GMM estimator with
  this `h` (`ml_smm_isMinOn_iff`).
* `ml_smm_moment_mean_zero`: `E h(xₜ, θ₀) = 0` when the simulated moments have the data's mean.
* `ml_variance_linear_comb`: `Var(∑ aᵢYᵢ) = ∑ aᵢ² Var Yᵢ` for independent `Yᵢ`;
  `ml_smm_variance_factor`: for independent `Y₀, Y₁, …, Y_S` with common variance `σ²`,
  `Var(Y₀ − (1/S)∑ₛ Yₛ) = (1 + 1/S)σ²` — the source of the factor `1 + 1/S` in `Q_S`.
* `ml_smm_Q`, `ml_smm_optimal_weight` (p. 402): `Q_S(W) = (1 + 1/S)(BᵀWB)⁻¹BᵀWΣWB(BᵀWB)⁻¹`;
  at `W = ((1 + 1/S)Σ)⁻¹`, `Q_S = (1 + 1/S)(BᵀΣ⁻¹B)⁻¹`, and `Q_S(W) − Q_S(W*)` is positive
  semidefinite for every symmetric `W`. `ml_smm_Q_tendsto` (p. 403): as `S → ∞` the optimal
  `Q_S` tends to the GMM variance `(BᵀΣ⁻¹B)⁻¹`.
* A concrete SMM model in which every claim of p. 402 is proved: the location model
  `xₜ = θ₀ + ωₜ`, `xₜˢ(θ) = θ + ωₜˢ`, `m(x) = x`, `W = 1`. `ml_smm_location_objective`: the SMM
  objective is `T²(θ̂ − θ)²` with `θ̂ = x̄ − (1/(TS))∑ₜ∑ₛ ωₜˢ`, the unique minimiser;
  `ml_smm_location_consistent`: `θ̂_T → θ₀` a.s. for fixed `S` (consistency);
  `ml_smm_location_variance`: `Var(√T(θ̂_T − θ₀)) = (1 + 1/S)σ²` exactly;
  `ml_smm_location_asymptotic`: `√T(θ̂_T − θ₀) ⇒ N(0, (1 + 1/S)σ²) = N(0, Q_S)`.

The J-test (12.6) and its `χ²(q − k)` limit are §12.1 GMM results (not formalised here).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology Matrix

/-- The SMM objective (Miao, p. 401): with `v(θ) = ∑ₜ (m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ)))`,
`J(θ) = v(θ)ᵀ W v(θ)`. -/
noncomputable def ml_smmObjective {X Θ : Type*} {q S T : ℕ} (m : X → Fin q → ℝ)
    (x : Fin T → X) (xs : Θ → Fin S → Fin T → X) (W : Matrix (Fin q) (Fin q) ℝ) (θ : Θ) : ℝ :=
  (∑ t, (m (x t) - (1 / (S : ℝ)) • ∑ s, m (xs θ s t))) ⬝ᵥ
    (W *ᵥ ∑ t, (m (x t) - (1 / (S : ℝ)) • ∑ s, m (xs θ s t)))

/-- The SMM moment function (12.5): `h(xₜ, θ) = m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ))`. -/
noncomputable def ml_smmMoment {X : Type*} {q S : ℕ} (m : X → Fin q → ℝ) (x : X)
    (xs : Fin S → X) : Fin q → ℝ :=
  m x - (1 / (S : ℝ)) • ∑ s, m (xs s)

/-- Miao, (12.5), p. 401: the SMM objective is `T² g_T(θ)ᵀ W g_T(θ)` with
`g_T(θ) = (1/T)∑ₜ h(xₜ, θ)`, so SMM is a special case of GMM. -/
theorem eq_12_5 {X Θ : Type*} {q S T : ℕ} (hT : 0 < T) (m : X → Fin q → ℝ) (x : Fin T → X)
    (xs : Θ → Fin S → Fin T → X) (W : Matrix (Fin q) (Fin q) ℝ) (θ : Θ) :
    let g := (1 / (T : ℝ)) • ∑ t, ml_smmMoment m (x t) (fun s => xs θ s t)
    ml_smmObjective m x xs W θ = (T : ℝ) ^ 2 * (g ⬝ᵥ (W *ᵥ g)) := by
  intro g
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hv : ∑ t, (m (x t) - (1 / (S : ℝ)) • ∑ s, m (xs θ s t)) = (T : ℝ) • g := by
    simp only [g, ml_smmMoment, smul_smul]
    rw [mul_one_div_cancel hT', one_smul]
  unfold ml_smmObjective
  rw [hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Miao, p. 401: `θ̂_ST` minimises the SMM objective iff it minimises the GMM criterion
`g_T(θ)ᵀ W g_T(θ)` with the moment function (12.5). -/
theorem ml_smm_isMinOn_iff {X Θ : Type*} {q S T : ℕ} (hT : 0 < T) (m : X → Fin q → ℝ)
    (x : Fin T → X) (xs : Θ → Fin S → Fin T → X) (W : Matrix (Fin q) (Fin q) ℝ) (Θ₀ : Set Θ)
    (θhat : Θ) :
    IsMinOn (ml_smmObjective m x xs W) Θ₀ θhat ↔
      IsMinOn (fun θ => ((1 / (T : ℝ)) • ∑ t, ml_smmMoment m (x t) (fun s => xs θ s t)) ⬝ᵥ
        (W *ᵥ ((1 / (T : ℝ)) • ∑ t, ml_smmMoment m (x t) (fun s => xs θ s t)))) Θ₀ θhat := by
  have hT2 : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
  constructor
  · intro h θ hθ
    have := h hθ
    simp only [Set.mem_ofPred_eq, eq_12_5 hT] at this ⊢
    exact le_of_mul_le_mul_left this hT2
  · intro h θ hθ
    have := h hθ
    simp only [Set.mem_ofPred_eq, eq_12_5 hT] at this ⊢
    exact mul_le_mul_of_nonneg_left this hT2.le

/-- Miao, p. 401: the population moment condition of SMM. If the simulated moments
`Yₛ = m(xₜˢ(θ₀))` have the mean of the data moment `Y₀ = m(xₜ)`, then
`E h(xₜ, θ₀) = E[Y₀ − (1/S)∑ₛ Yₛ] = 0`. -/
theorem ml_smm_moment_mean_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : ℕ}
    (hS : 0 < S) (Y₀ : Ω → ℝ) (Y : Fin S → Ω → ℝ) (h0 : Integrable Y₀ P)
    (hY : ∀ s, Integrable (Y s) P) (hmean : ∀ s, ∫ ω, Y s ω ∂P = ∫ ω, Y₀ ω ∂P) :
    ∫ ω, (Y₀ ω - (1 / (S : ℝ)) * ∑ s, Y s ω) ∂P = 0 := by
  rw [integral_sub h0 ((integrable_finsetSum _ fun s _ => hY s).const_mul _),
    integral_const_mul, integral_finsetSum _ fun s _ => hY s]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `Var(∑ᵢ aᵢYᵢ) = ∑ᵢ aᵢ² Var(Yᵢ)` for independent square-integrable `Yᵢ`. -/
theorem ml_variance_linear_comb {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] (Y : ι → Ω → ℝ) (a : ι → ℝ) (hindep : iIndepFun Y P)
    (hY : ∀ i, MemLp (Y i) 2 P) :
    Var[fun ω => ∑ i, a i * Y i ω; P] = ∑ i, a i ^ 2 * Var[Y i; P] := by
  have hfun : (fun ω => ∑ i, a i * Y i ω) = ∑ i, fun ω => a i * Y i ω := by
    funext ω; simp [Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum (fun i _ => (hY i).const_mul (a i))]
  · exact Finset.sum_congr rfl fun i _ => variance_const_mul _ _ _
  · intro i _ j _ hij
    exact (hindep.indepFun hij).comp (measurable_const_mul (a i)) (measurable_const_mul (a j))

/-- Miao, p. 402 (the factor `1 + 1/S`): if the data moment `Y₀` and the `S` simulated moments
`Y₁, …, Y_S` are independent with common variance `σ²`, then
`Var(Y₀ − (1/S)∑ₛ Yₛ) = (1 + 1/S)σ²`. -/
theorem ml_smm_variance_factor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : ℕ} (hS : 0 < S) (Y : Option (Fin S) → Ω → ℝ)
    (hindep : iIndepFun Y P) (hY : ∀ i, MemLp (Y i) 2 P) (σ2 : ℝ)
    (hvar : ∀ i, Var[Y i; P] = σ2) :
    Var[fun ω => Y none ω - (1 / (S : ℝ)) * ∑ s, Y (some s) ω; P] = (1 + 1 / S) * σ2 := by
  let a : Option (Fin S) → ℝ := fun i => Option.elim i 1 fun _ => -(1 / (S : ℝ))
  have hfun : (fun ω => Y none ω - (1 / (S : ℝ)) * ∑ s, Y (some s) ω) =
      fun ω => ∑ i, a i * Y i ω := by
    funext ω
    rw [Fintype.sum_option]
    simp only [a, Option.elim_none, Option.elim_some, one_mul, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hfun, ml_variance_linear_comb Y a hindep hY, Fintype.sum_option]
  simp only [a, Option.elim_none, Option.elim_some, hvar, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp

/-- The asymptotic variance of SMM (Miao, p. 402):
`Q_S(W) = (1 + 1/S)(BᵀWB)⁻¹BᵀWΣWB(BᵀWB)⁻¹`. -/
noncomputable def ml_smm_Q {q k : ℕ} (S : ℕ) (B : Matrix (Fin q) (Fin k) ℝ)
    (Sig W : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1 + 1 / (S : ℝ)) • ml_sandwich B Sig W

/-- **Optimal weighting matrix** of SMM (Miao, p. 402): at `W* = ((1 + 1/S)Σ)⁻¹`,
`Q_S(W*) = (1 + 1/S)(BᵀΣ⁻¹B)⁻¹`, and `Q_S(W) − Q_S(W*)` is positive semidefinite for every
symmetric `W` with `BᵀWB` invertible. -/
theorem ml_smm_optimal_weight {q k : ℕ} (S : ℕ) (B : Matrix (Fin q) (Fin k) ℝ)
    (Sig W : Matrix (Fin q) (Fin q) ℝ) (hSig : Sig.PosSemidef) (hSigu : IsUnit Sig.det)
    (hM : IsUnit (Bᵀ * Sig⁻¹ * B).det) (hW : Wᵀ = W) (hA : IsUnit (Bᵀ * W * B).det) :
    ml_smm_Q S B Sig ((1 + 1 / (S : ℝ)) • Sig)⁻¹ = (1 + 1 / (S : ℝ)) • (Bᵀ * Sig⁻¹ * B)⁻¹ ∧
      (ml_smm_Q S B Sig W - ml_smm_Q S B Sig ((1 + 1 / (S : ℝ)) • Sig)⁻¹).PosSemidef := by
  have hc : (0 : ℝ) < 1 + 1 / (S : ℝ) := by positivity
  have h1 : ml_smm_Q S B Sig ((1 + 1 / (S : ℝ)) • Sig)⁻¹ =
      (1 + 1 / (S : ℝ)) • (Bᵀ * Sig⁻¹ * B)⁻¹ := by
    unfold ml_smm_Q
    rw [ml_sandwich_inv B Sig hSigu hM hc.ne']
  refine ⟨h1, ?_⟩
  rw [h1, ml_smm_Q, ← smul_sub]
  exact (ml_sandwich_optimal B Sig W hSig hSigu hW hA hM).smul hc.le

/-- Miao, p. 403: as `S → ∞` the optimal SMM variance `(1 + 1/S)(BᵀΣ⁻¹B)⁻¹` tends to the GMM
variance `(BᵀΣ⁻¹B)⁻¹`. -/
theorem ml_smm_Q_tendsto {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ) :
    Tendsto (fun S : ℕ => (1 + 1 / (S : ℝ)) • V) atTop (𝓝 V) := by
  have h : Tendsto (fun S : ℕ => 1 + 1 / (S : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 : Tendsto (fun S : ℕ => (1 + 1 / (S : ℝ)) • V) atTop (𝓝 ((1 : ℝ) • V)) :=
    Tendsto.smul h (tendsto_const_nhds (x := V))
  rwa [one_smul] at h2

/-- The SMM estimator in the location model (`m(x) = x`, `xₜˢ(θ) = θ + ωₜˢ`):
`θ̂ = (1/T)∑ₜ xₜ − (1/(TS))∑ₜ∑ₛ ωₜˢ`. -/
noncomputable def ml_smmLocationEstimator {S T : ℕ} (x : Fin T → ℝ) (ω : Fin S → Fin T → ℝ) :
    ℝ :=
  (∑ t, x t) / T - (∑ t, ∑ s, ω s t) / (T * S)

/-- Miao, p. 401, in the location model `xₜˢ(θ) = θ + ωₜˢ` with `m(x) = x` and `W = 1`: the SMM
objective is `(∑ₜ (xₜ − (1/S)∑ₛ (θ + ωₜˢ)))² = T²(θ̂ − θ)²`, so `θ̂` is its unique minimiser. -/
theorem ml_smm_location_objective {S T : ℕ} (hS : 0 < S) (hT : 0 < T) (x : Fin T → ℝ)
    (ω : Fin S → Fin T → ℝ) (θ : ℝ) :
    (∑ t, (x t - (1 / (S : ℝ)) * ∑ s, (θ + ω s t))) ^ 2 =
      (T : ℝ) ^ 2 * (ml_smmLocationEstimator x ω - θ) ^ 2 ∧
      (∀ θ' : ℝ, (∑ t, (x t - (1 / (S : ℝ)) * ∑ s, (θ' + ω s t))) ^ 2 = 0 ↔
        θ' = ml_smmLocationEstimator x ω) := by
  have hS' : (S : ℝ) ≠ 0 := by positivity
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have key : ∀ θ' : ℝ, ∑ t, (x t - (1 / (S : ℝ)) * ∑ s, (θ' + ω s t)) =
      T * (ml_smmLocationEstimator x ω - θ') := fun θ' => by
    unfold ml_smmLocationEstimator
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  refine ⟨by rw [key]; ring, fun θ' => ?_⟩
  rw [key, mul_pow, mul_eq_zero, pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hT'
    · exact h.symm
  · intro h; exact Or.inr h.symm

/-- **Consistency of SMM** (Miao, p. 402, `θ̂_ST → θ₀` as `T → ∞` for fixed `S`), in the
location model: data `xₜ = θ₀ + ωₜ` and simulation shocks `ωₜˢ`, each sequence i.i.d. (pairwise
independent and identically distributed) and integrable with the common mean `E ωₜˢ = E ωₜ`.
Then `θ̂_T = (1/T)∑_{t<T} xₜ − (1/(TS))∑_{t<T}∑ₛ ωₜˢ → θ₀` almost surely. -/
theorem ml_smm_location_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : ℕ} (hS : 0 < S) (θ₀ : ℝ) (ω : ℕ → Ω → ℝ)
    (ωs : Fin S → ℕ → Ω → ℝ) (hint : Integrable (ω 0) P)
    (hindep : Pairwise fun i j => IndepFun (ω i) (ω j) P)
    (hident : ∀ i, IdentDistrib (ω i) (ω 0) P P) (hint' : ∀ s, Integrable (ωs s 0) P)
    (hindep' : ∀ s, Pairwise fun i j => IndepFun (ωs s i) (ωs s j) P)
    (hident' : ∀ s i, IdentDistrib (ωs s i) (ωs s 0) P P)
    (hmean : ∀ s, ∫ a, ωs s 0 a ∂P = ∫ a, ω 0 a ∂P) :
    ∀ᵐ a ∂P, Tendsto (fun T : ℕ => (∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
      (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S)) atTop (𝓝 θ₀) := by
  have h0 := strong_law_ae_real ω hint hindep hident
  have hs : ∀ᵐ a ∂P, ∀ s, Tendsto (fun T : ℕ => (∑ t ∈ Finset.range T, ωs s t a) / T) atTop
      (𝓝 (∫ a, ωs s 0 a ∂P)) :=
    ae_all_iff.2 fun s => strong_law_ae_real (ωs s) (hint' s) (hindep' s) (hident' s)
  filter_upwards [h0, hs] with a ha hsa
  simp only [hmean] at hsa
  have hS' : (S : ℝ) ≠ 0 := by positivity
  -- the estimator is `θ₀ + ω̄_T − (1/S)∑ₛ ω̄ˢ_T` for `T ≥ 1`
  have hrep : ∀ᶠ T : ℕ in atTop, (∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
      (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S) =
      θ₀ + (∑ t ∈ Finset.range T, ω t a) / T -
        (1 / (S : ℝ)) * ∑ s, (∑ t ∈ Finset.range T, ωs s t a) / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT' : (T : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_comm, ← Finset.sum_div]
    field_simp
  have hlim : Tendsto (fun T : ℕ => θ₀ + (∑ t ∈ Finset.range T, ω t a) / T -
      (1 / (S : ℝ)) * ∑ s, (∑ t ∈ Finset.range T, ωs s t a) / T) atTop
      (𝓝 (θ₀ + ∫ a, ω 0 a ∂P - (1 / (S : ℝ)) * ∑ _s : Fin S, ∫ a, ω 0 a ∂P)) :=
    ((tendsto_const_nhds.add ha).sub
      (tendsto_const_nhds.mul (tendsto_finsetSum _ fun s _ => hsa s)))
  have hval : θ₀ + ∫ a, ω 0 a ∂P - (1 / (S : ℝ)) * ∑ _s : Fin S, ∫ a, ω 0 a ∂P = θ₀ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hval] at hlim
  exact hlim.congr' (hrep.mono fun T hT => hT.symm)

/-- **The variance of SMM** (Miao, p. 402) in the location model, exactly at every `T ≥ 1`: if
the shocks `ωₜ` (data) and `ωₜˢ` (simulations), `t < T`, are all independent with common
variance `σ²`, then `Var(√T(θ̂_T − θ₀)) = (1 + 1/S)σ²` (here `B = 1`, `W = 1`, `Σ = σ²`, so
`Q_S = (1 + 1/S)σ²`). The shocks are indexed by `(i, t)`, `i = none` for the data and
`i = some s` for simulation `s`. -/
theorem ml_smm_location_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S T : ℕ} (hS : 0 < S) (hT : 0 < T) (θ₀ : ℝ)
    (Y : Option (Fin S) × Fin T → Ω → ℝ) (hindep : iIndepFun Y P)
    (hY : ∀ i, MemLp (Y i) 2 P) (σ2 : ℝ) (hvar : ∀ i, Var[Y i; P] = σ2) :
    Var[fun a => Real.sqrt T * (ml_smmLocationEstimator (fun t => θ₀ + Y (none, t) a)
      (fun s t => Y (some s, t) a) - θ₀); P] = (1 + 1 / S) * σ2 := by
  have hS' : (S : ℝ) ≠ 0 := by positivity
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg T)
  let c : Option (Fin S) → ℝ := fun i => Option.elim i 1 fun _ => -(1 / (S : ℝ))
  let a : Option (Fin S) × Fin T → ℝ := fun p => c p.1 / Real.sqrt T
  have hfun : (fun a' => Real.sqrt T * (ml_smmLocationEstimator (fun t => θ₀ + Y (none, t) a')
      (fun s t => Y (some s, t) a') - θ₀)) = fun a' => ∑ p, a p * Y p a' := by
    funext a'
    unfold ml_smmLocationEstimator
    rw [Fintype.sum_prod_type, Fintype.sum_option]
    simp only [a, c, Option.elim_none, Option.elim_some, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun (i : Fin S) (y : Fin T) =>
      -(1 / (S : ℝ)) / Real.sqrt T * Y (some i, y) a')]
    simp only [← Finset.mul_sum]
    set s := Real.sqrt (T : ℝ)
    rw [← hsq]
    field_simp
    ring
  rw [hfun, ml_variance_linear_comb Y a hindep hY, Fintype.sum_prod_type,
    Fintype.sum_option]
  simp only [a, c, Option.elim_none, Option.elim_some, hvar, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
  field_simp

/-- **Asymptotic normality of SMM** (Miao, p. 402, `√T(θ̂_ST − θ₀) ⇒ N(0, Q_S)` for fixed `S`),
in the location model. Write `ξₜ = ωₜ − (1/S)∑ₛ ωₜˢ` (`ml_smmLocationEstimator` gives
`θ̂_T − θ₀ = (1/T)∑_{t<T} ξₜ`); if the `ξₜ` are i.i.d. and, at each date, the data shock and the
`S` simulation shocks are independent with mean `μ` and variance `σ²`, then
`√T(θ̂_T − θ₀) ⇒ N(0, (1 + 1/S)σ²)`. Mathlib's central limit theorem. -/
theorem ml_smm_location_asymptotic {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {S : ℕ} (hS : 0 < S) (θ₀ μ σ2 : ℝ) (ω : ℕ → Ω → ℝ) (ωs : Fin S → ℕ → Ω → ℝ)
    (Z : Ω' → ℝ) (hZ : HasLaw Z (gaussianReal 0 ((1 + 1 / (S : ℝ)) * σ2).toNNReal) P')
    (hξindep : iIndepFun (fun t a => ω t a - (1 / (S : ℝ)) * ∑ s, ωs s t a) P)
    (hξident : ∀ t, IdentDistrib (fun a => ω t a - (1 / (S : ℝ)) * ∑ s, ωs s t a)
      (fun a => ω 0 a - (1 / (S : ℝ)) * ∑ s, ωs s 0 a) P P)
    (h0indep : iIndepFun (fun i : Option (Fin S) => Option.elim i (ω 0) fun s => ωs s 0) P)
    (h0L2 : ∀ i : Option (Fin S), MemLp (Option.elim i (ω 0) fun s => ωs s 0) 2 P)
    (h0mean : ∀ i : Option (Fin S), ∫ a, (Option.elim i (ω 0) fun s => ωs s 0) a ∂P = μ)
    (h0var : ∀ i : Option (Fin S), Var[Option.elim i (ω 0) fun s => ωs s 0; P] = σ2) :
    TendstoInDistribution (fun (T : ℕ) a => Real.sqrt T *
      ((∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
        (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S) - θ₀)) atTop Z (fun _ => P) P' := by
  set ξ : ℕ → Ω → ℝ := fun t a => ω t a - (1 / (S : ℝ)) * ∑ s, ωs s t a with hξ
  have hS' : (S : ℝ) ≠ 0 := by positivity
  -- moments of `ξ₀`
  have hvar0 : Var[ξ 0; P] = (1 + 1 / (S : ℝ)) * σ2 := by
    have := ml_smm_variance_factor hS _ h0indep h0L2 σ2 h0var
    exact this
  have hL2 : MemLp (ξ 0) 2 P := by
    have h1 : MemLp (ω 0) 2 P := by simpa using h0L2 none
    have h2 : ∀ s, MemLp (ωs s 0) 2 P := fun s => by simpa using h0L2 (some s)
    exact h1.sub ((memLp_finsetSum _ fun s _ => h2 s).const_mul _)
  have hmean0 : P[ξ 0] = 0 := by
    have hω : ∫ a, ω 0 a ∂P = μ := by simpa using h0mean none
    have hωs : ∀ s, ∫ a, ωs s 0 a ∂P = μ := fun s => by simpa using h0mean (some s)
    have := ml_smm_moment_mean_zero (P := P) hS (ω 0) (fun s => ωs s 0)
      ((by simpa using h0L2 none : MemLp (ω 0) 2 P).integrable one_le_two)
      (fun s => (by simpa using h0L2 (some s) : MemLp (ωs s 0) 2 P).integrable one_le_two)
      (fun s => by rw [hωs s, hω])
    simpa [hξ] using this
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (P' := P') (X := ξ)
    (Y := Z) (by rw [hvar0]; exact hZ) hL2 hξindep hξident
  rw [hmean0] at hclt
  simp only [mul_zero, sub_zero] at hclt
  have hfun : (fun (T : ℕ) a => Real.sqrt T * ((∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
      (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S) - θ₀)) =
      fun (T : ℕ) a => (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, ξ t a := by
    funext T a
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    have hT' : (T : ℝ) ≠ 0 := by positivity
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
    have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg T)
    simp only [hξ, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun t s => ωs s t a)]
    set s := Real.sqrt (T : ℝ)
    rw [← hsq]
    field_simp
    ring
  rw [hfun]
  exact hclt

end Miao.StructuralEstimation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Simulated maximum likelihood and indirect inference (§§12.3.2–12.3.3)

Miao, §12.3.2, pp. 403–404, and §12.3.3 with Example 12.3.3 and (12.7), pp. 404–408.

**Simulated maximum likelihood.**
* `ml_sml_average_unbiased`: the average `(1/S)∑ₛ f̃(θ | x, ωˢ)` of an unbiased simulator is
  unbiased; `ml_sml_simulator_slln`: it converges to `f(x, θ)` a.s. as `S → ∞` (the book's
  `lim (1/S)∑ₛ f̃ = f`, by the strong law).
* `ml_sml_log_bias` (why SML is inconsistent for fixed `S`): `E ln f̃ ≤ ln E f̃ = ln f`;
  `ml_sml_log_bias_strict`: strictly, for a two-point simulator (`E ln f̃ = ln f + ½ ln ¾`).

**Indirect inference.**
* `ml_iiAverage`, `ml_ii_average_correction`: `β̂_ST(θ)` must be the average
  `(1/S)∑ₛ β̂ˢ_T(θ)`; the book's sum `∑ₛ β̂ˢ_T(θ)` is `S` times it.
* `example_12_3_3`: in the exponential duration model with hazard `β` the log-likelihood is
  `N ln β − β ∑ Dᵢ` and the ML estimator is `β̂ = N/∑ᵢ Dᵢ = 1/D̄`, not the book's `∑ᵢ Dᵢ/N`;
  `example_12_3_3_book_false` is a counterexample to the printed formula.
  `example_12_3_3_mean`: parametrised by the mean duration `λ = 1/β`, the ML estimator is `D̄`;
  `example_12_3_3_ii_eq_smm`: then indirect inference is SMM matching the mean duration (as the
  book says), while `example_12_3_3_hazard_ne` shows that with the hazard parametrisation and
  `S = 2` it is not.
* `ml_binding_derivative` (p. 407): differentiating the first-order condition
  `∂ψ_∞(θ, b(θ))/∂β = 0` gives `∂b/∂θ = J₀⁻¹ ∂²ψ_∞/∂β∂θ′` (`ml_binding_derivative_J`), with
  `J₀ = −∂²ψ_∞/∂β∂β′`; for general normed spaces.
* `ml_ii_Q`, `eq_12_7_optimal` (p. 407): with `W* = J₀(I₀ − K₀)⁻¹J₀`,
  `Q_S(W*) = (1 + 1/S)(bᵀW*b)⁻¹ = (1 + 1/S)(Dᵀ(I₀ − K₀)⁻¹D)⁻¹` for `b = J₀⁻¹D`,
  `D = ∂²ψ_∞/∂β∂θ′`, and `Q_S(W) − Q_S(W*)` is positive semidefinite.

Not formalised (stated in the book without proof or computational): the SML limit theory with
`√T/S → 0`, the approximation of `I(θ₀)`, the consistent estimator of `I₀ − K₀`, the EMM
estimator, the limit (12.7) itself and the `χ²(q − k)` global specification test.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology Matrix

/-- Miao, p. 403: if each draw `f̃(θ | x, ωˢ)` is an unbiased simulator of `f(x, θ)`, so is their
average. -/
theorem ml_sml_average_unbiased {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : ℕ}
    (hS : 0 < S) (ftil : Fin S → Ω → ℝ) (f : ℝ) (hint : ∀ s, Integrable (ftil s) P)
    (hunb : ∀ s, ∫ a, ftil s a ∂P = f) :
    ∫ a, (1 / (S : ℝ)) * ∑ s, ftil s a ∂P = f := by
  rw [integral_const_mul, integral_finsetSum _ fun s _ => hint s]
  simp only [hunb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp

/-- Miao, p. 403: for i.i.d. draws `ωˢ` and an unbiased simulator,
`(1/S)∑_{s<S} f̃(θ | x, ωˢ) → f(x, θ)` almost surely as `S → ∞` (the strong law). -/
theorem ml_sml_simulator_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ftil : ℕ → Ω → ℝ) (f : ℝ) (hint : Integrable (ftil 0) P)
    (hindep : Pairwise fun i j => IndepFun (ftil i) (ftil j) P)
    (hident : ∀ i, IdentDistrib (ftil i) (ftil 0) P P) (hunb : ∫ a, ftil 0 a ∂P = f) :
    ∀ᵐ a ∂P, Tendsto (fun S : ℕ => (∑ s ∈ Finset.range S, ftil s a) / S) atTop (𝓝 f) := by
  have := strong_law_ae_real ftil hint hindep hident
  rw [hunb] at this
  exact this

/-- Miao, p. 403 (the source of the inconsistency of SML for fixed `S`): for a positive unbiased
simulator `Y` of `f > 0` (`E Y = f`), `E ln Y ≤ ln f`: the simulated log-likelihood is biased
downward. -/
theorem ml_sml_log_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (f : ℝ) (hf : 0 < f) (hpos : ∀ a, 0 < Y a)
    (hint : Integrable Y P) (hlog : Integrable (fun a => Real.log (Y a)) P)
    (hmean : ∫ a, Y a ∂P = f) : ∫ a, Real.log (Y a) ∂P ≤ Real.log f := by
  have hpt : ∀ a, Real.log (Y a) ≤ Real.log f + (Y a / f - 1) := fun a => by
    have := Real.log_le_sub_one_of_pos (div_pos (hpos a) hf)
    rw [Real.log_div (hpos a).ne' hf.ne'] at this
    linarith
  have hint2 : Integrable (fun a => Real.log f + (Y a / f - 1)) P :=
    (integrable_const _).add ((hint.div_const f).sub (integrable_const 1))
  calc ∫ a, Real.log (Y a) ∂P ≤ ∫ a, (Real.log f + (Y a / f - 1)) ∂P :=
        integral_mono hlog hint2 hpt
    _ = Real.log f := by
        have hi : Integrable (fun a => Y a / f - 1) P := (hint.div_const f).sub (integrable_const 1)
        rw [integral_add (integrable_const _) hi,
          integral_sub (hint.div_const f) (integrable_const 1), integral_div, hmean]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        field_simp
        ring

/-- Miao, p. 403: the bias is strict in general. For the unbiased two-point simulator equal to
`f/2` or `3f/2` with probability `1/2` each, `E f̃ = f` but
`E ln f̃ = ln f + ½ ln(3/4) < ln f`. -/
theorem ml_sml_log_bias_strict (f : ℝ) (hf : 0 < f) :
    (1 / 2 : ℝ) * (f / 2) + 1 / 2 * (3 * f / 2) = f ∧
      (1 / 2 : ℝ) * Real.log (f / 2) + 1 / 2 * Real.log (3 * f / 2) =
        Real.log f + 1 / 2 * Real.log (3 / 4) ∧
      (1 / 2 : ℝ) * Real.log (f / 2) + 1 / 2 * Real.log (3 * f / 2) < Real.log f := by
  have h1 : Real.log (f / 2) = Real.log f - Real.log 2 :=
    Real.log_div hf.ne' two_ne_zero
  have h2 : Real.log (3 * f / 2) = Real.log 3 + Real.log f - Real.log 2 := by
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_mul (by norm_num) hf.ne']
  have h3 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  have heq : (1 / 2 : ℝ) * Real.log (f / 2) + 1 / 2 * Real.log (3 * f / 2) =
      Real.log f + 1 / 2 * Real.log (3 / 4) := by
    rw [h1, h2, h3]; ring
  refine ⟨by ring, heq, ?_⟩
  rw [heq]
  have : Real.log (3 / 4) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-- The average auxiliary estimate over simulations, `β̂_ST(θ) = (1/S)∑ₛ β̂ˢ_T(θ)`. -/
noncomputable def ml_iiAverage {S p : ℕ} (βs : Fin S → Fin p → ℝ) : Fin p → ℝ :=
  (1 / (S : ℝ)) • ∑ s, βs s

/-- Miao, p. 405 (correction): the average of `S` identical auxiliary estimates `b` is `b`,
while the book's `∑ₛ β̂ˢ_T(θ)` is `S • b`, so the indirect inference criterion must use the
average. -/
theorem ml_ii_average_correction {S p : ℕ} (hS : 0 < S) (b : Fin p → ℝ) :
    ml_iiAverage (fun _ : Fin S => b) = b ∧ ∑ _s : Fin S, b = (S : ℝ) • b := by
  have : (S : ℝ) ≠ 0 := by positivity
  refine ⟨?_, by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]⟩
  unfold ml_iiAverage
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, one_div_mul_cancel this, one_smul]

/-- **Example 12.3.3** (Miao, p. 405): in the exponential duration model with constant hazard
`β`, the log-likelihood of the durations `D₁, …, D_N` is
`∑ᵢ ln(βe^{−βDᵢ}) = N ln β − β ∑ᵢ Dᵢ`, and (when `∑ᵢ Dᵢ > 0`) it is maximised at
`β̂ = N/∑ᵢ Dᵢ = 1/D̄`, the inverse of the mean duration. -/
theorem example_12_3_3 {N : ℕ} (D : Fin N → ℝ) (hS : 0 < ∑ i, D i) :
    (∀ β, 0 < β → ml_logLikelihood ml_expDensity D β = N * Real.log β - β * ∑ i, D i) ∧
      IsMaxOn (ml_logLikelihood ml_expDensity D) (Set.Ioi 0) ((N : ℝ) / ∑ i, D i) := by
  refine ⟨fun β hβ => ex_12_2_logLikelihood D hβ, ?_⟩
  obtain ⟨hpos, -, hmax⟩ := ex_12_2 D hS
  intro θ hθ
  have hθ' : (0 : ℝ) < θ := hθ
  have h := hmax hθ
  change ml_logLikelihood ml_expDensity D θ ≤ ml_logLikelihood ml_expDensity D (N / ∑ i, D i)
  have hdens : ∀ η : ℝ, 0 < η → ∀ t, 0 < ml_expDensity (D t) η := fun η hη t => by
    unfold ml_expDensity; positivity
  rw [← eq_ml_log_likelihood _ _ _ (hdens θ hθ'), ← eq_ml_log_likelihood _ _ _ (hdens _ hpos)]
  exact Real.log_le_log (Finset.prod_pos fun t _ => hdens θ hθ' t) h

/-- Counterexample to the printed formula `β̂_T = ∑ᵢ Dᵢ/N` of Example 12.3.3 (Miao, p. 405):
for one observed duration `D₁ = 2`, the book's value `β = 2` gives a lower log-likelihood than
`β = 1/2` (the true maximiser `1/D̄`). -/
theorem example_12_3_3_book_false :
    ml_logLikelihood ml_expDensity (fun _ : Fin 1 => (2 : ℝ)) 2 <
      ml_logLikelihood ml_expDensity (fun _ : Fin 1 => (2 : ℝ)) (1 / 2) := by
  rw [ex_12_2_logLikelihood _ (by norm_num), ex_12_2_logLikelihood _ (by norm_num)]
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, one_mul,
    Real.log_inv, one_div]
  have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
  norm_num
  linarith

/-- Example 12.3.3 (Miao, p. 405), corrected: parametrised by the mean duration `λ = 1/β`, the
exponential likelihood `λ ↦ L(1/λ)` is maximised at the mean duration `λ̂ = D̄ = ∑ᵢ Dᵢ/N`
(invariance of ML). -/
theorem example_12_3_3_mean {N : ℕ} (D : Fin N → ℝ) (hS : 0 < ∑ i, D i) :
    ∀ lam, 0 < lam → ml_likelihood ml_expDensity D (1 / lam) ≤
      ml_likelihood ml_expDensity D (1 / ((∑ i, D i) / N)) := by
  obtain ⟨-, heq, hmax⟩ := ex_12_2 D hS
  intro lam hlam
  rw [← heq]
  exact hmax (show (0 : ℝ) < 1 / lam by positivity)

/-- Example 12.3.3 (Miao, pp. 405–406): with the mean-duration parametrisation, the auxiliary
estimates are `D̄` (data) and `D̄ˢ(θ)` (simulations), and the indirect inference criterion
`W(D̄ − (1/S)∑ₛ D̄ˢ(θ))²` equals `W g²` for the SMM moment `g = (1/N)∑ᵢ (Dᵢ − (1/S)∑ₛ Dᵢˢ(θ))`
of (12.5) with `m(D) = D`: indirect inference is SMM matching the mean duration. -/
theorem example_12_3_3_ii_eq_smm {N S : ℕ} (hN : 0 < N) (D : Fin N → ℝ)
    (Dsim : Fin S → Fin N → ℝ) (W : ℝ) :
    W * ((∑ i, D i) / N - (1 / (S : ℝ)) * ∑ s, (∑ i, Dsim s i) / N) ^ 2 =
      W * ((1 / (N : ℝ)) * ∑ i, (D i - (1 / (S : ℝ)) * ∑ s, Dsim s i)) ^ 2 := by
  congr 2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm (f := fun i s => Dsim s i),
    ← Finset.sum_div]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- Example 12.3.3 (Miao, p. 406): with the hazard parametrisation and `S = 2` simulations,
indirect inference does not reduce to matching the mean duration. Data mean `D̄ = 2`, simulated
means `D̄¹ = 1`, `D̄² = 3`: the mean durations match (`2 = (1 + 3)/2`), but the auxiliary
hazards do not (`1/2 ≠ (1/1 + 1/3)/2`). -/
theorem example_12_3_3_hazard_ne :
    (2 : ℝ) - (1 / 2) * (1 + 3) = 0 ∧ (1 / 2 : ℝ) - (1 / 2) * (1 / 1 + 1 / 3) ≠ 0 := by
  norm_num

/-- Miao, p. 407: the derivative of the binding function. If `b(θ)` solves the first-order
condition `G(θ, b(θ)) = 0` for all `θ`, where `G = ∂ψ_∞/∂β` has derivative `G′` at
`(θ₀, b(θ₀))` and `b` has derivative `b′` at `θ₀`, then
`G′(·, 0) + G′(0, b′ ·) = 0`, i.e. `∂²ψ_∞/∂β∂θ′ + ∂²ψ_∞/∂β∂β′ · ∂b/∂θ′ = 0`. -/
theorem ml_binding_derivative {Eθ Eβ F : Type*} [NormedAddCommGroup Eθ] [NormedSpace ℝ Eθ]
    [NormedAddCommGroup Eβ] [NormedSpace ℝ Eβ] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Eθ × Eβ → F) (b : Eθ → Eβ) (θ₀ : Eθ) (G' : Eθ × Eβ →L[ℝ] F) (b' : Eθ →L[ℝ] Eβ)
    (hfoc : ∀ θ, G (θ, b θ) = 0) (hG : HasFDerivAt G G' (θ₀, b θ₀))
    (hb : HasFDerivAt b b' θ₀) :
    G'.comp (ContinuousLinearMap.inl ℝ Eθ Eβ) +
      (G'.comp (ContinuousLinearMap.inr ℝ Eθ Eβ)).comp b' = 0 := by
  have hpair : HasFDerivAt (fun θ => (θ, b θ)) ((ContinuousLinearMap.id ℝ Eθ).prod b') θ₀ :=
    (hasFDerivAt_id θ₀).prodMk hb
  have hcomp := hG.comp θ₀ hpair
  have hconst : (G ∘ fun θ => (θ, b θ)) = fun _ => 0 := funext hfoc
  rw [hconst] at hcomp
  have h0 := hcomp.unique (hasFDerivAt_const 0 θ₀)
  ext v
  have := congrArg (fun L : Eθ →L[ℝ] F => L v) h0
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, _root_.zero_apply] at this
  simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    _root_.zero_apply]
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  exact this

/-- Miao, p. 407: `∂b/∂θ′ = J₀⁻¹ ∂²ψ_∞/∂β∂θ′`, where `J₀ = −∂²ψ_∞/∂β∂β′` (the `β`-block of `G′`
with a minus sign) is invertible. -/
theorem ml_binding_derivative_J {Eθ Eβ F : Type*} [NormedAddCommGroup Eθ] [NormedSpace ℝ Eθ]
    [NormedAddCommGroup Eβ] [NormedSpace ℝ Eβ] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Eθ × Eβ → F) (b : Eθ → Eβ) (θ₀ : Eθ) (G' : Eθ × Eβ →L[ℝ] F) (b' : Eθ →L[ℝ] Eβ)
    (hfoc : ∀ θ, G (θ, b θ) = 0) (hG : HasFDerivAt G G' (θ₀, b θ₀))
    (hb : HasFDerivAt b b' θ₀) (J : Eβ ≃L[ℝ] F)
    (hJ : (J : Eβ →L[ℝ] F) = -G'.comp (ContinuousLinearMap.inr ℝ Eθ Eβ)) :
    b' = (J.symm : F →L[ℝ] Eβ).comp (G'.comp (ContinuousLinearMap.inl ℝ Eθ Eβ)) := by
  have h := ml_binding_derivative G b θ₀ G' b' hfoc hG hb
  ext v
  have hv := congrArg (fun L : Eθ →L[ℝ] F => L v) h
  simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    _root_.zero_apply] at hv
  have hJv : J (b' v) = G' ((ContinuousLinearMap.inl ℝ Eθ Eβ) v) := by
    have : (J : Eβ →L[ℝ] F) (b' v) = -(G' ((ContinuousLinearMap.inr ℝ Eθ Eβ) (b' v))) := by
      rw [hJ]; rfl
    rw [ContinuousLinearEquiv.coe_coe] at this
    rw [this]
    exact (neg_eq_of_add_eq_zero_left hv)
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [← hJv, ContinuousLinearEquiv.symm_apply_apply]

/-- The indirect inference asymptotic variance (12.7) (Miao, p. 406):
`Q_S(W) = (1 + 1/S)(bᵀWb)⁻¹ bᵀW J₀⁻¹(I₀ − K₀)J₀⁻¹ Wb (bᵀWb)⁻¹`, with `b = ∂b(θ₀)/∂θ′`
(`q × k`) and `Pm = I₀ − K₀`. -/
noncomputable def ml_ii_Q {q k : ℕ} (S : ℕ) (b : Matrix (Fin q) (Fin k) ℝ)
    (J Pm W : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1 + 1 / (S : ℝ)) • ml_sandwich b (J⁻¹ * Pm * J⁻¹) W

/-- Miao, (12.7) and p. 407: the optimal weighting matrix of indirect inference. With `J₀`
symmetric invertible, `I₀ − K₀` positive semidefinite invertible and
`W* = J₀(I₀ − K₀)⁻¹J₀`: `Q_S(W*) = (1 + 1/S)(bᵀW*b)⁻¹`; if `b = J₀⁻¹D` with
`D = ∂²ψ_∞/∂β∂θ′`, then `bᵀW*b = Dᵀ(I₀ − K₀)⁻¹D`, so
`Q_S(W*) = (1 + 1/S)(Dᵀ(I₀ − K₀)⁻¹D)⁻¹`; and `Q_S(W) − Q_S(W*)` is positive semidefinite for
every symmetric `W` with `bᵀWb` invertible. -/
theorem eq_12_7_optimal {q k : ℕ} (S : ℕ) (b : Matrix (Fin q) (Fin k) ℝ)
    (J Pm W : Matrix (Fin q) (Fin q) ℝ) (hJ : Jᵀ = J) (hJu : IsUnit J.det)
    (hP : Pm.PosSemidef) (hPu : IsUnit Pm.det) (hM : IsUnit (bᵀ * (J * Pm⁻¹ * J) * b).det)
    (hW : Wᵀ = W) (hA : IsUnit (bᵀ * W * b).det) :
    ml_ii_Q S b J Pm (J * Pm⁻¹ * J) = (1 + 1 / (S : ℝ)) • (bᵀ * (J * Pm⁻¹ * J) * b)⁻¹ ∧
      (∀ D : Matrix (Fin q) (Fin k) ℝ, b = J⁻¹ * D →
        bᵀ * (J * Pm⁻¹ * J) * b = Dᵀ * Pm⁻¹ * D) ∧
      (ml_ii_Q S b J Pm W - ml_ii_Q S b J Pm (J * Pm⁻¹ * J)).PosSemidef := by
  set Ω := J⁻¹ * Pm * J⁻¹ with hΩ
  have hJi : (J⁻¹)ᵀ = J⁻¹ := by rw [transpose_nonsing_inv, hJ]
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hJu
  have hPP : Pm * Pm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hJiu : IsUnit (J⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hJu.ringInverse
  have hΩu : IsUnit Ω.det := by
    rw [hΩ, Matrix.det_mul, Matrix.det_mul]
    exact (hJiu.mul hPu).mul hJiu
  have hΩinv : Ω⁻¹ = J * Pm⁻¹ * J := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hΩ]
    calc J * Pm⁻¹ * J * (J⁻¹ * Pm * J⁻¹) = J * Pm⁻¹ * (J * J⁻¹) * Pm * J⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hJJ, Matrix.mul_one, Matrix.mul_assoc J, Matrix.nonsing_inv_mul _ hPu,
            Matrix.mul_one, hJJ]
  have hΩpsd : Ω.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same J⁻¹
    rwa [conjTranspose_eq_transpose_of_trivial, hJi] at this
  have hWstar : J * Pm⁻¹ * J = ((1 : ℝ) • Ω)⁻¹ := by rw [one_smul, hΩinv]
  have hM' : IsUnit (bᵀ * Ω⁻¹ * b).det := by rw [hΩinv]; exact hM
  have h1 : ml_ii_Q S b J Pm (J * Pm⁻¹ * J) = (1 + 1 / (S : ℝ)) • (bᵀ * (J * Pm⁻¹ * J) * b)⁻¹ := by
    unfold ml_ii_Q
    rw [← hΩ]
    conv_lhs => rw [hWstar]
    rw [ml_sandwich_inv b Ω hΩu hM' one_ne_zero, hΩinv]
  have hc : (0 : ℝ) ≤ 1 + 1 / (S : ℝ) := by positivity
  refine ⟨h1, fun D hD => ?_, ?_⟩
  · rw [hD, transpose_mul, hJi]
    calc Dᵀ * J⁻¹ * (J * Pm⁻¹ * J) * (J⁻¹ * D) = Dᵀ * (J⁻¹ * J) * Pm⁻¹ * (J * J⁻¹) * D := by
          simp only [Matrix.mul_assoc]
      _ = Dᵀ * Pm⁻¹ * D := by rw [hJJ', hJJ, Matrix.mul_one, Matrix.mul_one]
  · have hopt := ml_sandwich_optimal b Ω W hΩpsd hΩu hW hA hM'
    rw [h1, ml_ii_Q, ← hΩ, ← hΩinv, ← smul_sub]
    exact hopt.smul hc

end Miao.StructuralEstimation

set_option linter.style.longLine false
#print axioms Miao.StructuralEstimation.measurable_birkhoffSum
#print axioms Miao.StructuralEstimation.integrable_birkhoffSum
#print axioms Miao.StructuralEstimation.birkhoffSum_sub_const
#print axioms Miao.StructuralEstimation.birkhoffSum_const_sub
#print axioms Miao.StructuralEstimation.iterate_mem_iff
#print axioms Miao.StructuralEstimation.birkhoffSum_indicator
#print axioms Miao.StructuralEstimation.birkhoffMax
#print axioms Miao.StructuralEstimation.birkhoffSum_le_birkhoffMax
#print axioms Miao.StructuralEstimation.birkhoffMax_nonneg
#print axioms Miao.StructuralEstimation.birkhoffMax_mono
#print axioms Miao.StructuralEstimation.birkhoffMax_le_add
#print axioms Miao.StructuralEstimation.birkhoffMax_le_sum_abs
#print axioms Miao.StructuralEstimation.measurable_birkhoffMax
#print axioms Miao.StructuralEstimation.integrable_birkhoffMax
#print axioms Miao.StructuralEstimation.maximal_ergodic
#print axioms Miao.StructuralEstimation.birkhoffMax_indicator
#print axioms Miao.StructuralEstimation.maximal_ergodic_inter
#print axioms Miao.StructuralEstimation.upSet
#print axioms Miao.StructuralEstimation.bddAbove_range_succ_add_iff
#print axioms Miao.StructuralEstimation.preimage_upSet
#print axioms Miao.StructuralEstimation.not_bddAbove_range_iff
#print axioms Miao.StructuralEstimation.measurableSet_upSet
#print axioms Miao.StructuralEstimation.integral_upSet_nonneg
#print axioms Miao.StructuralEstimation.mul_measure_le_setIntegral
#print axioms Miao.StructuralEstimation.setIntegral_le_mul_measure
#print axioms Miao.StructuralEstimation.tendsto_div_of_bdd
#print axioms Miao.StructuralEstimation.measure_upSet_sub_eq_zero
#print axioms Miao.StructuralEstimation.measure_upSet_const_sub_eq_zero
#print axioms Miao.StructuralEstimation.birkhoffAverage_eq_div
#print axioms Miao.StructuralEstimation.ae_tendsto_birkhoffAverage_of_ergodic
#print axioms Miao.StructuralEstimation.measure_upSet_inter_eq_zero
#print axioms Miao.StructuralEstimation.measure_iInter_upSet_eq_zero
#print axioms Miao.StructuralEstimation.le_of_bddAbove_both
#print axioms Miao.StructuralEstimation.exists_tendsto_div_of_bdd
#print axioms Miao.StructuralEstimation.ae_exists_tendsto_birkhoffAverage
#print axioms Miao.StructuralEstimation.birkhoffLimit
#print axioms Miao.StructuralEstimation.measurable_birkhoffAverage
#print axioms Miao.StructuralEstimation.measurable_birkhoffLimit
#print axioms Miao.StructuralEstimation.ae_tendsto_birkhoffLimit
#print axioms Miao.StructuralEstimation.tendsto_birkhoffAverage_apply
#print axioms Miao.StructuralEstimation.tendsto_birkhoffAverage_of_apply
#print axioms Miao.StructuralEstimation.birkhoffLimit_apply_of_tendsto
#print axioms Miao.StructuralEstimation.measurable_abs_of_measurable
#print axioms Miao.StructuralEstimation.setIntegral_comp_iterate
#print axioms Miao.StructuralEstimation.setIntegral_birkhoffAverage
#print axioms Miao.StructuralEstimation.lintegral_abs_birkhoffAverage_le
#print axioms Miao.StructuralEstimation.integrable_birkhoffLimit
#print axioms Miao.StructuralEstimation.setIntegral_birkhoffLimit_of_bdd
#print axioms Miao.StructuralEstimation.truncAt
#print axioms Miao.StructuralEstimation.abs_sub_truncAt_le
#print axioms Miao.StructuralEstimation.setIntegral_birkhoffLimit
#print axioms Miao.StructuralEstimation.trajKernel
#print axioms Miao.StructuralEstimation.isMarkovKernel_trajKernel
#print axioms Miao.StructuralEstimation.pathKernel
#print axioms Miao.StructuralEstimation.isMarkovKernel_pathKernel
#print axioms Miao.StructuralEstimation.pathMeasure
#print axioms Miao.StructuralEstimation.isProbabilityMeasure_pathMeasure
#print axioms Miao.StructuralEstimation.pathMeasure_eq_comp
#print axioms Miao.StructuralEstimation.pathMeasure_dirac
#print axioms Miao.StructuralEstimation.pathKernel_map_zero
#print axioms Miao.StructuralEstimation.pathKernel_zero_mem
#print axioms Miao.StructuralEstimation.ae_pathKernel_zero
#print axioms Miao.StructuralEstimation.pathMeasure_inter_zero
#print axioms Miao.StructuralEstimation.pathMeasure_map_zero
#print axioms Miao.StructuralEstimation.natFilt
#print axioms Miao.StructuralEstimation.measurable_coord_natFilt
#print axioms Miao.StructuralEstimation.measurableSet_coord_natFilt
#print axioms Miao.StructuralEstimation.setLIntegral_succ
#print axioms Miao.StructuralEstimation.cylFn
#print axioms Miao.StructuralEstimation.measurable_cylFn
#print axioms Miao.StructuralEstimation.boxSet
#print axioms Miao.StructuralEstimation.measurableSet_boxSet
#print axioms Miao.StructuralEstimation.measure_inter_shift_box
#print axioms Miao.StructuralEstimation.pathKernel_boxSet
#print axioms Miao.StructuralEstimation.pathMeasure_boxSet
#print axioms Miao.StructuralEstimation.IsMarkovChain
#print axioms Miao.StructuralEstimation.IsMarkovChain.mk
#print axioms Miao.StructuralEstimation.IsMarkovChain.measurable
#print axioms Miao.StructuralEstimation.IsMarkovChain.fdd
#print axioms Miao.StructuralEstimation.mt_theorem_3_4_1
#print axioms Miao.StructuralEstimation.generateFrom_boxSets
#print axioms Miao.StructuralEstimation.isPiSystem_boxSets
#print axioms Miao.StructuralEstimation.mt_theorem_3_4_1_unique
#print axioms Miao.StructuralEstimation.law_eq_pathMeasure
#print axioms Miao.StructuralEstimation.IsSubstochasticKernel
#print axioms Miao.StructuralEstimation.isSubstochasticKernel_of_markov
#print axioms Miao.StructuralEstimation.isMarkovKernel_pow
#print axioms Miao.StructuralEstimation.pow_zero_apply
#print axioms Miao.StructuralEstimation.pow_succ_apply
#print axioms Miao.StructuralEstimation.pow_succ_apply'
#print axioms Miao.StructuralEstimation.mt_theorem_3_4_2
#print axioms Miao.StructuralEstimation.pow_add_eq
#print axioms Miao.StructuralEstimation.skeleton
#print axioms Miao.StructuralEstimation.skeleton_pow
#print axioms Miao.StructuralEstimation.sampledKernel
#print axioms Miao.StructuralEstimation.sampledKernel_apply
#print axioms Miao.StructuralEstimation.isMarkovKernel_sampledKernel
#print axioms Miao.StructuralEstimation.resolvent
#print axioms Miao.StructuralEstimation.resolvent_apply
#print axioms Miao.StructuralEstimation.tsum_geometric_weights
#print axioms Miao.StructuralEstimation.isMarkovKernel_resolvent
#print axioms Miao.StructuralEstimation.kfun
#print axioms Miao.StructuralEstimation.measurable_kfun
#print axioms Miao.StructuralEstimation.kfun_indicator
#print axioms Miao.StructuralEstimation.kfun_one
#print axioms Miao.StructuralEstimation.kfun_mono
#print axioms Miao.StructuralEstimation.kfun_add
#print axioms Miao.StructuralEstimation.kfun_const_mul
#print axioms Miao.StructuralEstimation.kfun_comp
#print axioms Miao.StructuralEstimation.kfun_pow_succ
#print axioms Miao.StructuralEstimation.measure_kernel_apply
#print axioms Miao.StructuralEstimation.measure_kernel_assoc
#print axioms Miao.StructuralEstimation.lintegral_kfun
#print axioms Miao.StructuralEstimation.isProbabilityMeasure_measure_kernel
#print axioms Miao.StructuralEstimation.dirac_kernel
#print axioms Miao.StructuralEstimation.kfunR
#print axioms Miao.StructuralEstimation.measurable_kfunR
#print axioms Miao.StructuralEstimation.abs_kfunR_le
#print axioms Miao.StructuralEstimation.indKernel
#print axioms Miao.StructuralEstimation.indKernel_apply
#print axioms Miao.StructuralEstimation.comp_indKernel_apply
#print axioms Miao.StructuralEstimation.isSubstochasticKernel_comp_indKernel
#print axioms Miao.StructuralEstimation.potKernel
#print axioms Miao.StructuralEstimation.potKernel_apply
#print axioms Miao.StructuralEstimation.shift
#print axioms Miao.StructuralEstimation.measurable_shift
#print axioms Miao.StructuralEstimation.shift_zero
#print axioms Miao.StructuralEstimation.shift_shift
#print axioms Miao.StructuralEstimation.shift_apply
#print axioms Miao.StructuralEstimation.integral_measure_comp
#print axioms Miao.StructuralEstimation.pathMeasure_map_coord
#print axioms Miao.StructuralEstimation.pathKernel_map_coord
#print axioms Miao.StructuralEstimation.pathKernel_coord_mem
#print axioms Miao.StructuralEstimation.pathKernel_coord_chapmanKolmogorov
#print axioms Miao.StructuralEstimation.markov_measure
#print axioms Miao.StructuralEstimation.markov_lintegral
#print axioms Miao.StructuralEstimation.markov_lintegral_mul
#print axioms Miao.StructuralEstimation.markov_lintegral_univ
#print axioms Miao.StructuralEstimation.markov_setIntegral
#print axioms Miao.StructuralEstimation.stronglyMeasurable_expect_coord
#print axioms Miao.StructuralEstimation.integrable_expect_coord
#print axioms Miao.StructuralEstimation.markov_property
#print axioms Miao.StructuralEstimation.integrable_shift_of_bdd
#print axioms Miao.StructuralEstimation.markov_property_bdd
#print axioms Miao.StructuralEstimation.mt_proposition_3_4_3
#print axioms Miao.StructuralEstimation.isMarkovChain_of_step
#print axioms Miao.StructuralEstimation.skeletonFilt
#print axioms Miao.StructuralEstimation.skeleton_isMarkovChain
#print axioms Miao.StructuralEstimation.IsMeasurableTransformation
#print axioms Miao.StructuralEstimation.isMeasurableTransformation_iff
#print axioms Miao.StructuralEstimation.IsMeasurePreserving
#print axioms Miao.StructuralEstimation.isMeasurePreserving_iff
#print axioms Miao.StructuralEstimation.IsTransformationInvariant
#print axioms Miao.StructuralEstimation.ex_4_1
#print axioms Miao.StructuralEstimation.ex_4_1_empty
#print axioms Miao.StructuralEstimation.ex_4_1_compl
#print axioms Miao.StructuralEstimation.ex_4_1_iUnion
#print axioms Miao.StructuralEstimation.IsErgodic
#print axioms Miao.StructuralEstimation.isErgodic_iff_ergodic
#print axioms Miao.StructuralEstimation.iterate_shift_one
#print axioms Miao.StructuralEstimation.example_4_1_1_measurable
#print axioms Miao.StructuralEstimation.example_4_1_1_not_measurePreserving
#print axioms Miao.StructuralEstimation.iterate_finRotate
#print axioms Miao.StructuralEstimation.example_4_1_2
#print axioms Miao.StructuralEstimation.exists_uniform_fin
#print axioms Miao.StructuralEstimation.example_4_1_2_ergodic
#print axioms Miao.StructuralEstimation.ex_4_2
#print axioms Miao.StructuralEstimation.lemma_4_1_1_step
#print axioms Miao.StructuralEstimation.lemma_4_1_1_on_pos
#print axioms Miao.StructuralEstimation.lemma_4_1_1
#print axioms Miao.StructuralEstimation.theorem_4_1_1_sum_succ
#print axioms Miao.StructuralEstimation.birkhoffAverage_eq_sum
#print axioms Miao.StructuralEstimation.measurableSet_convergent
#print axioms Miao.StructuralEstimation.invariantLimit
#print axioms Miao.StructuralEstimation.invariantLimit_comp
#print axioms Miao.StructuralEstimation.measurable_invariantLimit
#print axioms Miao.StructuralEstimation.invariantLimit_ae_eq
#print axioms Miao.StructuralEstimation.birkhoffLimit_ae_eq_condExp
#print axioms Miao.StructuralEstimation.theorem_4_1_1
#print axioms Miao.StructuralEstimation.abs_birkhoffAverage_le
#print axioms Miao.StructuralEstimation.integrable_birkhoffAverage
#print axioms Miao.StructuralEstimation.integral_abs_birkhoffAverage_le
#print axioms Miao.StructuralEstimation.tendsto_integral_abs_sub_of_bdd
#print axioms Miao.StructuralEstimation.tendsto_integral_abs_sub_truncAt
#print axioms Miao.StructuralEstimation.tendsto_integral_abs_sub_birkhoffLimit
#print axioms Miao.StructuralEstimation.theorem_4_1_1_L1
#print axioms Miao.StructuralEstimation.theorem_4_1_1_condExp_const
#print axioms Miao.StructuralEstimation.theorem_4_1_1_ergodic
#print axioms Miao.StructuralEstimation.theorem_4_1_1_ergodic_L1
#print axioms Miao.StructuralEstimation.pathOf
#print axioms Miao.StructuralEstimation.window
#print axioms Miao.StructuralEstimation.pathWindow
#print axioms Miao.StructuralEstimation.pathLaw
#print axioms Miao.StructuralEstimation.IsStationary
#print axioms Miao.StructuralEstimation.measurable_pathOf
#print axioms Miao.StructuralEstimation.measurable_window
#print axioms Miao.StructuralEstimation.measurable_pathWindow
#print axioms Miao.StructuralEstimation.window_eq
#print axioms Miao.StructuralEstimation.window_zero
#print axioms Miao.StructuralEstimation.isProbabilityMeasure_pathLaw
#print axioms Miao.StructuralEstimation.boxSet_eq_preimage
#print axioms Miao.StructuralEstimation.ext_of_boxSet
#print axioms Miao.StructuralEstimation.isStationary_iff_map_shift
#print axioms Miao.StructuralEstimation.isStationary_iff_measurePreserving
#print axioms Miao.StructuralEstimation.isStationary_of_measurePreserving
#print axioms Miao.StructuralEstimation.stationary_representation
#print axioms Miao.StructuralEstimation.isStationary_comp_window
#print axioms Miao.StructuralEstimation.isStationary_of_iid
#print axioms Miao.StructuralEstimation.IsShiftInvariant
#print axioms Miao.StructuralEstimation.IsErgodicProcess
#print axioms Miao.StructuralEstimation.isShiftInvariant_of_preimage_eq
#print axioms Miao.StructuralEstimation.shiftInvariant_compl_counterexample
#print axioms Miao.StructuralEstimation.preimage_shift_mono
#print axioms Miao.StructuralEstimation.exists_invariant_ae_eq
#print axioms Miao.StructuralEstimation.isErgodicProcess_iff_isErgodic
#print axioms Miao.StructuralEstimation.invariantField
#print axioms Miao.StructuralEstimation.condExp_comp_ae_eq
#print axioms Miao.StructuralEstimation.eq_4_3
#print axioms Miao.StructuralEstimation.theorem_4_2_1
#print axioms Miao.StructuralEstimation.theorem_4_2_1_ergodic
#print axioms Miao.StructuralEstimation.IsMixing
#print axioms Miao.StructuralEstimation.theorem_4_2_3
#print axioms Miao.StructuralEstimation.theorem_4_2_4_filtration_mono
#print axioms Miao.StructuralEstimation.tendsto_avg_succ
#print axioms Miao.StructuralEstimation.indicator_shift_of_invariant
#print axioms Miao.StructuralEstimation.measure_inter_preimage_shift
#print axioms Miao.StructuralEstimation.measure_eq_zero_or_one_of_boxes
#print axioms Miao.StructuralEstimation.theorem_4_2_2
#print axioms Miao.StructuralEstimation.ex_4_5_a
#print axioms Miao.StructuralEstimation.gm_sampleMoment
#print axioms Miao.StructuralEstimation.gm_popMoment
#print axioms Miao.StructuralEstimation.gm_quadForm
#print axioms Miao.StructuralEstimation.gm_objective
#print axioms Miao.StructuralEstimation.gm_popObjective
#print axioms Miao.StructuralEstimation.Assumption_12_1_3
#print axioms Miao.StructuralEstimation.Assumption_12_1_4
#print axioms Miao.StructuralEstimation.Assumption_12_1_7
#print axioms Miao.StructuralEstimation.assumption_12_1_7_of_sup
#print axioms Miao.StructuralEstimation.gm_quadForm_eq
#print axioms Miao.StructuralEstimation.gm_continuous_quadForm
#print axioms Miao.StructuralEstimation.gm_quadForm_pos
#print axioms Miao.StructuralEstimation.gm_quadForm_zero
#print axioms Miao.StructuralEstimation.gm_integral_comp_eq
#print axioms Miao.StructuralEstimation.gm_ergodic_avg
#print axioms Miao.StructuralEstimation.gm_le_of_mem_closure
#print axioms Miao.StructuralEstimation.gm_modulus
#print axioms Miao.StructuralEstimation.gm_modulus_nonneg
#print axioms Miao.StructuralEstimation.gm_modulus_le
#print axioms Miao.StructuralEstimation.gm_measurable_modulus
#print axioms Miao.StructuralEstimation.gm_abs_sub_le_modulus
#print axioms Miao.StructuralEstimation.gm_exists_modulus_lt
#print axioms Miao.StructuralEstimation.gm_ulln_scalar_eps
#print axioms Miao.StructuralEstimation.gm_ulln_scalar
#print axioms Miao.StructuralEstimation.gm_ulln
#print axioms Miao.StructuralEstimation.gm_continuousOn_popMoment
#print axioms Miao.StructuralEstimation.gm_integrable_moment
#print axioms Miao.StructuralEstimation.gm_tendsto_measure_of_ae_eventually
#print axioms Miao.StructuralEstimation.gm_continuousOn_sampleMoment
#print axioms Miao.StructuralEstimation.gm_exists_estimator
#print axioms Miao.StructuralEstimation.gm_popObjective_unique_min
#print axioms Miao.StructuralEstimation.gm_identification_gap
#print axioms Miao.StructuralEstimation.gm_abs_trilinear_sub
#print axioms Miao.StructuralEstimation.gm_quadForm_perturb
#print axioms Miao.StructuralEstimation.gm_argmin_stable
#print axioms Miao.StructuralEstimation.gm_measurableSet_unif
#print axioms Miao.StructuralEstimation.theorem_12_1_1
#print axioms Miao.StructuralEstimation.theorem_12_1_1_ae
#print axioms Miao.StructuralEstimation.gm_jacobian
#print axioms Miao.StructuralEstimation.gm_clm_apply_eq_sum
#print axioms Miao.StructuralEstimation.gm_foc_line
#print axioms Miao.StructuralEstimation.eq_12_2
#print axioms Miao.StructuralEstimation.eq_12_3_counterexample
#print axioms Miao.StructuralEstimation.gm_circle_hasDerivAt
#print axioms Miao.StructuralEstimation.eq_12_3
#print axioms Miao.StructuralEstimation.gm_linearization
#print axioms Miao.StructuralEstimation.gm_linearization_sqrt
#print axioms Miao.StructuralEstimation.gm_M
#print axioms Miao.StructuralEstimation.gm_M_mul
#print axioms Miao.StructuralEstimation.gm_posDef_GWG
#print axioms Miao.StructuralEstimation.gm_isUnit_det_GWG
#print axioms Miao.StructuralEstimation.gm_isSymm_GWG
#print axioms Miao.StructuralEstimation.gm_inv_transpose_of_isSymm
#print axioms Miao.StructuralEstimation.gm_M_transpose
#print axioms Miao.StructuralEstimation.gm_asymVar_eq
#print axioms Miao.StructuralEstimation.gm_efficient_var
#print axioms Miao.StructuralEstimation.gm_efficiency
#print axioms Miao.StructuralEstimation.gm_J
#print axioms Miao.StructuralEstimation.gm_proj
#print axioms Miao.StructuralEstimation.gm_proj_transpose
#print axioms Miao.StructuralEstimation.gm_proj_mul_self
#print axioms Miao.StructuralEstimation.gm_proj_idem
#print axioms Miao.StructuralEstimation.gm_proj_trace
#print axioms Miao.StructuralEstimation.gm_resid_proj
#print axioms Miao.StructuralEstimation.eq_12_4_algebra
#print axioms Miao.StructuralEstimation.gm_linear_sampleMoment
#print axioms Miao.StructuralEstimation.gm_linear_foc_iff
#print axioms Miao.StructuralEstimation.gm_linear_min
#print axioms Miao.StructuralEstimation.gm_exactly_identified
#print axioms Miao.StructuralEstimation.gm_nls_foc
#print axioms Miao.StructuralEstimation.gm_toE
#print axioms Miao.StructuralEstimation.gm_matE
#print axioms Miao.StructuralEstimation.gm_continuous_toE
#print axioms Miao.StructuralEstimation.gm_continuous_matE
#print axioms Miao.StructuralEstimation.gm_matE_toE
#print axioms Miao.StructuralEstimation.gm_inner_matE
#print axioms Miao.StructuralEstimation.gm_map_multivariateGaussian
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_comp
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_pi
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_apply
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_prod
#print axioms Miao.StructuralEstimation.gm_tight_of_tendstoInDistribution
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_mul
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_sum
#print axioms Miao.StructuralEstimation.gm_tendstoInMeasure_matE
#print axioms Miao.StructuralEstimation.gm_continuousAt_inv
#print axioms Miao.StructuralEstimation.gm_sampleDeriv
#print axioms Miao.StructuralEstimation.gm_sampleJac
#print axioms Miao.StructuralEstimation.gm_popJac
#print axioms Miao.StructuralEstimation.gm_hasFDerivAt_sampleMoment
#print axioms Miao.StructuralEstimation.gm_dist_segment_le
#print axioms Miao.StructuralEstimation.gm_sampleJac_tendstoInMeasure
#print axioms Miao.StructuralEstimation.theorem_12_1_2
#print axioms Miao.StructuralEstimation.theorem_12_1_2_efficient
#print axioms Miao.StructuralEstimation.gm_covMat
#print axioms Miao.StructuralEstimation.gm_covMat_quad
#print axioms Miao.StructuralEstimation.gm_covMat_posSemidef
#print axioms Miao.StructuralEstimation.gm_sqrt_mul_inv
#print axioms Miao.StructuralEstimation.lemma_12_1_1_iid
#print axioms Miao.StructuralEstimation.gm_map_eq
#print axioms Miao.StructuralEstimation.gm_integral_mul_shift
#print axioms Miao.StructuralEstimation.gm_sum_range_reflect_sub
#print axioms Miao.StructuralEstimation.gm_toeplitz_sum
#print axioms Miao.StructuralEstimation.gm_toeplitz_sum_Ico
#print axioms Miao.StructuralEstimation.gm_autocov
#print axioms Miao.StructuralEstimation.gm_longRunVar
#print axioms Miao.StructuralEstimation.gm_longRunVar_limit
#print axioms Miao.StructuralEstimation.gm_bartlett
#print axioms Miao.StructuralEstimation.gm_parzen
#print axioms Miao.StructuralEstimation.gm_qs
#print axioms Miao.StructuralEstimation.gm_kernelArg
#print axioms Miao.StructuralEstimation.gm_bartlett_zero
#print axioms Miao.StructuralEstimation.gm_parzen_zero
#print axioms Miao.StructuralEstimation.gm_bartlett_mem_Icc
#print axioms Miao.StructuralEstimation.gm_parzen_mem_Icc
#print axioms Miao.StructuralEstimation.gm_continuous_bartlett
#print axioms Miao.StructuralEstimation.gm_continuous_parzen
#print axioms Miao.StructuralEstimation.gm_sampleAutocov
#print axioms Miao.StructuralEstimation.gm_hac
#print axioms Miao.StructuralEstimation.gm_hac_isSymm
#print axioms Miao.StructuralEstimation.gm_crraMU
#print axioms Miao.StructuralEstimation.gm_crra_hasDerivAt
#print axioms Miao.StructuralEstimation.gm_eulerMoment
#print axioms Miao.StructuralEstimation.gm_eulerMoment_eq
#print axioms Miao.StructuralEstimation.example_12_1_1
#print axioms Miao.StructuralEstimation.example_12_1_1_mean
#print axioms Miao.StructuralEstimation.gm_exX
#print axioms Miao.StructuralEstimation.gm_exH
#print axioms Miao.StructuralEstimation.gm_exΘ
#print axioms Miao.StructuralEstimation.gm_exDh
#print axioms Miao.StructuralEstimation.gm_ex_isStationary
#print axioms Miao.StructuralEstimation.gm_ex_isErgodic
#print axioms Miao.StructuralEstimation.gm_ex_popMoment
#print axioms Miao.StructuralEstimation.gm_ex_compact
#print axioms Miao.StructuralEstimation.gm_ex_mem
#print axioms Miao.StructuralEstimation.gm_ex_measurable
#print axioms Miao.StructuralEstimation.gm_ex_continuous
#print axioms Miao.StructuralEstimation.gm_ex_assumption_12_1_3
#print axioms Miao.StructuralEstimation.gm_ex_assumption_12_1_7
#print axioms Miao.StructuralEstimation.gm_ex_assumption_12_1_4
#print axioms Miao.StructuralEstimation.gm_ex_theorem_12_1_1
#print axioms Miao.StructuralEstimation.gm_ex_popJac
#print axioms Miao.StructuralEstimation.gm_ex_sampleJac
#print axioms Miao.StructuralEstimation.gm_ex_sampleMoment_zero
#print axioms Miao.StructuralEstimation.gm_ex_multivariateGaussian_zero
#print axioms Miao.StructuralEstimation.gm_ex_theorem_12_1_2
#print axioms Miao.StructuralEstimation.ml_br_IsContraction
#print axioms Miao.StructuralEstimation.ml_br_IsContraction.uniformContinuous
#print axioms Miao.StructuralEstimation.ml_br_dist_iterate_succ_le
#print axioms Miao.StructuralEstimation.ml_br_dist_iterate_le
#print axioms Miao.StructuralEstimation.ml_br_cauchySeq_iterate
#print axioms Miao.StructuralEstimation.ml_br_theorem_3_2
#print axioms Miao.StructuralEstimation.ml_br_corollary_1
#print axioms Miao.StructuralEstimation.ml_br_blackwell
#print axioms Miao.StructuralEstimation.ml_br_isClosed_comb
#print axioms Miao.StructuralEstimation.ml_od_integrable_of_continuous
#print axioms Miao.StructuralEstimation.ml_od_abs_integral_sub_le
#print axioms Miao.StructuralEstimation.ml_od_lipschitz_stop
#print axioms Miao.StructuralEstimation.ml_od_scalar_fixed
#print axioms Miao.StructuralEstimation.ml_od_fixed_le_of_le
#print axioms Miao.StructuralEstimation.ml_od_integral_max_eq
#print axioms Miao.StructuralEstimation.ml_od_integrable_sub
#print axioms Miao.StructuralEstimation.ml_od_setIntegral_Ioi_eq
#print axioms Miao.StructuralEstimation.ml_od_FiringBellman
#print axioms Miao.StructuralEstimation.ml_od_firingΦ
#print axioms Miao.StructuralEstimation.ml_od_firing_D_pos
#print axioms Miao.StructuralEstimation.ml_od_firing_integrable
#print axioms Miao.StructuralEstimation.ml_od_firingΦ_lipschitz
#print axioms Miao.StructuralEstimation.ml_ex_8_2_E
#print axioms Miao.StructuralEstimation.ml_od_firing_fixed
#print axioms Miao.StructuralEstimation.ml_ex_8_2
#print axioms Miao.StructuralEstimation.ml_ex_8_2_reservation
#print axioms Miao.StructuralEstimation.ml_od_firingψ
#print axioms Miao.StructuralEstimation.ml_ex_8_2_reservation_eq
#print axioms Miao.StructuralEstimation.ml_od_firingψ_strictMono
#print axioms Miao.StructuralEstimation.ml_ex_8_2_root_unique
#print axioms Miao.StructuralEstimation.ml_ex_8_2_alpha
#print axioms Miao.StructuralEstimation.ml_od_McCallBellman
#print axioms Miao.StructuralEstimation.ml_od_mccall_iff_firing
#print axioms Miao.StructuralEstimation.ml_od_mccall_exists_unique
#print axioms Miao.StructuralEstimation.ml_od_mccall_reservation
#print axioms Miao.StructuralEstimation.ml_likelihood
#print axioms Miao.StructuralEstimation.ml_logLikelihood
#print axioms Miao.StructuralEstimation.eq_ml_log_likelihood
#print axioms Miao.StructuralEstimation.ml_isMaxOn_likelihood_iff
#print axioms Miao.StructuralEstimation.ml_first_order_condition
#print axioms Miao.StructuralEstimation.ml_score_mean_zero
#print axioms Miao.StructuralEstimation.ml_information_matrix_equality
#print axioms Miao.StructuralEstimation.ml_cramer_rao
#print axioms Miao.StructuralEstimation.ml_cramer_rao_bernoulli
#print axioms Miao.StructuralEstimation.ml_invariance
#print axioms Miao.StructuralEstimation.ml_profileLikelihood
#print axioms Miao.StructuralEstimation.ml_invariance_profile
#print axioms Miao.StructuralEstimation.ml_gaussLogLik
#print axioms Miao.StructuralEstimation.ml_gaussian_tests_equal
#print axioms Miao.StructuralEstimation.ml_gammaPDF_one_toReal
#print axioms Miao.StructuralEstimation.ml_integral_expMeasure
#print axioms Miao.StructuralEstimation.ml_integrable_expMeasure_pow
#print axioms Miao.StructuralEstimation.ml_memLp_two_expMeasure
#print axioms Miao.StructuralEstimation.ml_integral_expMeasure_pow
#print axioms Miao.StructuralEstimation.ml_mean_expMeasure
#print axioms Miao.StructuralEstimation.ml_second_moment_expMeasure
#print axioms Miao.StructuralEstimation.ml_variance_expMeasure
#print axioms Miao.StructuralEstimation.ml_binomial_lik_le
#print axioms Miao.StructuralEstimation.ml_coinDensity
#print axioms Miao.StructuralEstimation.ml_heads
#print axioms Miao.StructuralEstimation.ex_12_1_likelihood
#print axioms Miao.StructuralEstimation.ex_12_1
#print axioms Miao.StructuralEstimation.ml_integral_of_zero_one
#print axioms Miao.StructuralEstimation.ex_12_1_consistent
#print axioms Miao.StructuralEstimation.ml_sqrt_mul_mean_sub
#print axioms Miao.StructuralEstimation.ex_12_1_asymptotic
#print axioms Miao.StructuralEstimation.ml_expDensity
#print axioms Miao.StructuralEstimation.ex_12_2_likelihood
#print axioms Miao.StructuralEstimation.ex_12_2_logLikelihood
#print axioms Miao.StructuralEstimation.ex_12_2
#print axioms Miao.StructuralEstimation.ex_12_2_fisher
#print axioms Miao.StructuralEstimation.ml_tendstoInDistribution_congr_ae
#print axioms Miao.StructuralEstimation.ex_12_2_consistent
#print axioms Miao.StructuralEstimation.ex_12_2_asymptotic
#print axioms Miao.StructuralEstimation.ml_firstPassage
#print axioms Miao.StructuralEstimation.ml_firstPassage_iid
#print axioms Miao.StructuralEstimation.example_12_2_1_duration
#print axioms Miao.StructuralEstimation.ml_reject_prob_eq_cdf
#print axioms Miao.StructuralEstimation.ml_durationLik
#print axioms Miao.StructuralEstimation.example_12_2_1
#print axioms Miao.StructuralEstimation.ml_mccall_psi_root
#print axioms Miao.StructuralEstimation.ml_resWage_mono_beta
#print axioms Miao.StructuralEstimation.ml_resWage_strictMono_beta
#print axioms Miao.StructuralEstimation.ex_12_4_moments
#print axioms Miao.StructuralEstimation.ml_sandwich
#print axioms Miao.StructuralEstimation.ml_inv_smul
#print axioms Miao.StructuralEstimation.ml_sandwich_inv
#print axioms Miao.StructuralEstimation.ml_sandwich_optimal
#print axioms Miao.StructuralEstimation.ml_smmObjective
#print axioms Miao.StructuralEstimation.ml_smmMoment
#print axioms Miao.StructuralEstimation.eq_12_5
#print axioms Miao.StructuralEstimation.ml_smm_isMinOn_iff
#print axioms Miao.StructuralEstimation.ml_smm_moment_mean_zero
#print axioms Miao.StructuralEstimation.ml_variance_linear_comb
#print axioms Miao.StructuralEstimation.ml_smm_variance_factor
#print axioms Miao.StructuralEstimation.ml_smm_Q
#print axioms Miao.StructuralEstimation.ml_smm_optimal_weight
#print axioms Miao.StructuralEstimation.ml_smm_Q_tendsto
#print axioms Miao.StructuralEstimation.ml_smmLocationEstimator
#print axioms Miao.StructuralEstimation.ml_smm_location_objective
#print axioms Miao.StructuralEstimation.ml_smm_location_consistent
#print axioms Miao.StructuralEstimation.ml_smm_location_variance
#print axioms Miao.StructuralEstimation.ml_smm_location_asymptotic
#print axioms Miao.StructuralEstimation.ml_sml_average_unbiased
#print axioms Miao.StructuralEstimation.ml_sml_simulator_slln
#print axioms Miao.StructuralEstimation.ml_sml_log_bias
#print axioms Miao.StructuralEstimation.ml_sml_log_bias_strict
#print axioms Miao.StructuralEstimation.ml_iiAverage
#print axioms Miao.StructuralEstimation.ml_ii_average_correction
#print axioms Miao.StructuralEstimation.example_12_3_3
#print axioms Miao.StructuralEstimation.example_12_3_3_book_false
#print axioms Miao.StructuralEstimation.example_12_3_3_mean
#print axioms Miao.StructuralEstimation.example_12_3_3_ii_eq_smm
#print axioms Miao.StructuralEstimation.example_12_3_3_hazard_ne
#print axioms Miao.StructuralEstimation.ml_binding_derivative
#print axioms Miao.StructuralEstimation.ml_binding_derivative_J
#print axioms Miao.StructuralEstimation.ml_ii_Q
#print axioms Miao.StructuralEstimation.eq_12_7_optimal
