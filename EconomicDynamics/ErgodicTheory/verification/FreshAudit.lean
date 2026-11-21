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
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Birkhoff's pointwise ergodic theorem (used in MT §17.1)

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/BirkhoffErgodic.lean`), namespace renamed to `Miao.ErgodicTheory`.

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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The path space of a Markov chain (MT §3.1, §3.4.1)

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/PathSpace.lean`), namespace renamed to `Miao.ErgodicTheory` and the
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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition kernels, `n`-step kernels and their operators (MT §3.4.1–3.4.2)

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/Kernels.lean`), namespace renamed to `Miao.ErgodicTheory` and the
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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Markov property (MT §3.4.2)

Copied from `StochasticStability/LimitTheorems` (Meyn–Tweedie project, module
`LimitTheorems/MarkovProperty.lean`), namespace renamed to `Miao.ErgodicTheory` and the
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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The ergodic theorem (Miao §4.1)

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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stationary processes (Miao §4.2)

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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equivalent formulations of ergodicity (Miao Theorem 4.2.2, Exercise 5)

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

namespace Miao.ErgodicTheory

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

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stationary Markov processes (Miao §4.3)

Miao, §4.3, pp. 125–129, and Exercises 3, 5 and 6. A transition function is a Markov kernel
`P : Kernel X X` on an arbitrary measurable space; `invariantDistributions P = M` is the set of
invariant distributions. `pathMeasure P μ` is the law of the chain with initial law `μ` on
`X^ℕ` (Ionescu-Tulcea, copied in `ErgodicTheory.PathSpace`), and `pathKernel P x = P_x`.

* `convex_invariantDistributions`: `M` is convex; `pathMeasure_add_smul`:
  `P_{απ₁ + βπ₂} = αP_{π₁} + βP_{π₂}` (p. 127).
* **Exercise 3** (`ex_4_3`): started at `π ∈ M` the coordinate process is stationary, Markov with
  transition function `P`, and every `Xₙ` has law `π`; `eq_4_4`: its finite-dimensional
  distributions are (4.4).
* **Definition 3.3.5** (recalled on p. 128): `IsPInvariantSet`, `IsErgodicMeasure`.
* **Lemma 4.3.1** (`lemma_4_3_1`): every shift-invariant event `A` is, up to a `P_π`-null set, of
  the form `{x₀ ∈ A₁}` (and `{xₙ ∈ A₁}` for every `n`), with `A₁` a `P`-invariant set.
* `isInvariant_restrict`, `isInvariant_restrict_compl` (p. 128): for an (a.e.) `P`-invariant
  set `A₁`, `π(A₁ ∩ ·)` and `π(A₁ᶜ ∩ ·)` are invariant.
* **Theorem 4.3.1** (`theorem_4_3_1`): `(X^ℕ, P_π, θ)` is ergodic iff `π` is an extreme point of
  `M`; `theorem_4_3_1_iff_isErgodicMeasure`: iff `π` is ergodic in the sense of
  Definition 3.3.5 (p. 128).
* **Corollary 4.3.1** (`corollary_4_3_1`): a unique invariant distribution is ergodic.
* **Theorem 4.3.2** (`theorem_4_3_2`): for an extremal `π` and bounded measurable `f`, for
  `π`-a.e. `x₀`, `(1/N) Σ_{k=1}^N f(x_k) → ∫ f dπ`, `P_{x₀}`-a.s.; `ex_4_5_b` is Exercise 5.
* **Exercise 6** (`ex_4_6`): two distinct ergodic invariant probabilities of a measurable map
  are mutually singular; `ex_4_6_markov`: two distinct ergodic invariant distributions of `P`
  (Definition 3.3.5) are mutually singular, and so are their path measures.

**Departures.** The book builds the stationary chain on the two-sided space `X^ℤ` by the
Kolmogorov extension theorem (4.4). Here the chain is the one-sided chain on `X^ℕ` with
`X₀ ∼ π` (the first construction mentioned on p. 125), and `θ` is the one-sided shift. Exercise 3,
Lemma 4.3.1 and Theorem 4.3.1 are proved for this chain. Lemma 4.3.1 then says `I ⊆ σ(x₀)` up to
null sets; the book's proof (via the remote past and future and Exercise 4) is replaced by
Lévy's upward theorem and stationarity (copied `mt_lemma_17_1_1`). The book's footnote 2 uses
"`P(x, A₁) = 1` for `π`-a.e. `x ∈ A₁`" while Definition 3.3.5 requires every `x ∈ A₁`;
Lemma 4.3.1 produces a set with the stronger property, so both readings give the same notion of
ergodic `π` (`theorem_4_3_1_iff_isErgodicMeasure`). In the proof of Theorem 4.3.1 the book picks
an `f` with `∫ f dP_{π₁} ≠ ∫ f dP_{π₂}` and derives `E₁ ∩ E₂ = ∅`; here the same ergodic theorem
shows `π₁ = π` directly (`eq_of_ergodic_of_absolutelyContinuous`).
-/

namespace Miao.ErgodicTheory

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The set `M` of invariant distributions -/

/-- `M`, the set of invariant distributions of the transition function `P` (Miao, p. 126). -/
def invariantDistributions (P : Kernel X X) : Set (Measure X) :=
  {π | IsProbabilityMeasure π ∧ IsInvariant P π}

/-- Miao, Theorem 4.3.1, p. 126: `M` is a convex set. -/
theorem convex_invariantDistributions (P : Kernel X X) :
    Convex ℝ≥0∞ (invariantDistributions P) := by
  intro π₁ h₁ π₂ h₂ a b _ _ hab
  refine ⟨⟨?_⟩, (h₁.2.smul a).add (h₂.2.smul b)⟩
  have := h₁.1
  have := h₂.1
  simp [Measure.add_apply, Measure.smul_apply, hab]

/-- Miao, p. 127: `P_{απ₁ + βπ₂} = αP_{π₁} + βP_{π₂}`. -/
theorem pathMeasure_add_smul (P : Kernel X X) [IsMarkovKernel P] (π₁ π₂ : Measure X)
    (a b : ℝ≥0∞) :
    pathMeasure P (a • π₁ + b • π₂) = a • pathMeasure P π₁ + b • pathMeasure P π₂ := by
  rw [pathMeasure_eq_comp, pathMeasure_eq_comp, pathMeasure_eq_comp, Measure.comp_add,
    Measure.comp_smul, Measure.comp_smul]

/-! ### Exercise 3: the stationary chain -/

/-- The law of the coordinate process on path space is the measure itself. -/
theorem pathLaw_coord (μ : Measure (ℕ → X)) : pathLaw μ (fun n ω => ω n) = μ :=
  Measure.map_id'

/-- **Exercise 3** (Miao, p. 129), on `X^ℕ`: if `π` is invariant, the coordinate process under
`P_π` is stationary, every `Xₙ` has distribution `π`, and it is Markov with transition function
`P`: `E[1_A(X_{n+1}) | X₀, …, Xₙ] = P(Xₙ, A)`. -/
theorem ex_4_3 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) :
    IsStationary (pathMeasure P π) (fun n ω => ω n) ∧
      (∀ n, (pathMeasure P π).map (fun ω => ω n) = π) ∧
      ∀ n {A : Set X}, MeasurableSet A →
        (pathMeasure P π)[fun ω => A.indicator (1 : X → ℝ) (ω (n + 1)) | natFilt n]
          =ᵐ[pathMeasure P π] fun ω => (P (ω n)).real A := by
  have := isProbabilityMeasure_pathMeasure P π
  refine ⟨(isStationary_iff_map_shift (fun n => measurable_pi_apply n)).2 fun t => ?_,
    fun n => hπ.map_coord n, fun n A hA => ?_⟩
  · rw [pathLaw_coord]
    exact hπ.map_shift t
  · have hH : Measurable fun ω : ℕ → X => A.indicator (1 : X → ℝ) (ω 1) :=
      (measurable_one.indicator hA).comp (measurable_pi_apply 1)
    have h := markov_property_bdd P π n hH (B := 1) fun ω => by
      by_cases h : ω 1 ∈ A <;> simp [h]
    refine h.trans (Eventually.of_forall fun ω => ?_)
    have hm : Measurable fun ω' : ℕ → X => ω' 1 := measurable_pi_apply 1
    simp only
    rw [← integral_map hm.aemeasurable (measurable_one.indicator hA).aestronglyMeasurable,
      pathKernel_map_coord, pow_one, integral_indicator_one hA]

/-- Miao, (4.4), p. 126, for the one-sided chain: `P_π(x₀ ∈ A₀, …, xₙ ∈ Aₙ) =
∫_{A₀} ⋯ ∫_{Aₙ} P(x_{n−1}, dxₙ) ⋯ P(x₀, dx₁) π(dx₀)` (`cylFn` is the nested integral). -/
theorem eq_4_4 (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) :
    pathMeasure P π {ω | ∀ i ≤ n, ω i ∈ A i} = ∫⁻ x, cylFn P n A x ∂π :=
  pathMeasure_boxSet P π n hA

/-! ### Definition 3.3.5 -/

/-- Definition 3.3.5 (Miao, p. 111, recalled on p. 128): `A` is a `P`-invariant set if
`P(x, A) = 1` for every `x ∈ A`. -/
def IsPInvariantSet (P : Kernel X X) (A : Set X) : Prop :=
  MeasurableSet A ∧ ∀ x ∈ A, P x A = 1

/-- Definition 3.3.5 (Miao, p. 111): an invariant distribution `π` is ergodic if `π(A) ∈ {0, 1}`
for every `P`-invariant set `A`. -/
def IsErgodicMeasure (P : Kernel X X) (π : Measure X) : Prop :=
  ∀ A : Set X, IsPInvariantSet P A → π A = 0 ∨ π A = 1

/-! ### Lemma 4.3.1 -/

/-- Miao, proof of Lemma 4.3.1: for a strictly shift-invariant event `A`, `h(x) = P_x(A)` is
harmonic, `∫ h(y) P(x, dy) = h(x)`. -/
theorem expectFn_harmonic_of_invariant (P : Kernel X X) [IsMarkovKernel P]
    {A : Set (ℕ → X)} (hA : MeasurableSet A) (hθA : shift 1 ⁻¹' A = A) (x : X) :
    ∫ y, expectFn P (A.indicator 1) y ∂P x = expectFn P (A.indicator 1) x := by
  have := isMarkovKernel_pathKernel P
  set Y : (ℕ → X) → ℝ := A.indicator 1 with hY
  have hYm : Measurable Y := measurable_one.indicator hA
  have hYb : ∀ ω, |Y ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [hY, h]
  have hhm : Measurable (expectFn P Y) := measurable_expectFn P hYm
  have h1 : ∫ y, expectFn P Y y ∂P x = ∫ ω, expectFn P Y (ω 1) ∂pathKernel P x := by
    rw [← integral_map (measurable_pi_apply 1).aemeasurable hhm.aestronglyMeasurable,
      pathKernel_map_coord, pow_one]
  have h2 := markov_setIntegral P (Measure.dirac x) (n := 1) MeasurableSet.univ hYm
    (integrable_shift_of_bdd P (Measure.dirac x) 1 hYm hYb).integrableOn
  simp only [pathMeasure_dirac, Measure.restrict_univ] at h2
  have h3 : (fun ω => Y (shift 1 ω)) = Y := by
    ext ω
    exact indicator_shift_of_invariant hθA 1 ω
  rw [h3] at h2
  rw [h1]
  exact h2.symm

/-- **Lemma 4.3.1** (Miao, p. 127), one-sided form: if `π` is invariant and `A` is a
shift-invariant event (`θ⁻¹A = A`), there is a `P`-invariant set `A₁` (Definition 3.3.5) with
`A = {x₀ ∈ A₁}` and indeed `A = {xₙ ∈ A₁}` for every `n`, up to `P_π`-null sets. So
`I ⊆ F₀⁰` (and `I ⊆ Fₙⁿ`) up to null sets. -/
theorem lemma_4_3_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {A : Set (ℕ → X)} (hA : MeasurableSet A) (hθA : shift 1 ⁻¹' A = A) :
    ∃ A₁ : Set X, IsPInvariantSet P A₁ ∧ A =ᵐ[pathMeasure P π] {ω | ω 0 ∈ A₁} ∧
      ∀ n, A =ᵐ[pathMeasure P π] {ω | ω n ∈ A₁} := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  set Y : (ℕ → X) → ℝ := A.indicator 1 with hY
  have hYm : Measurable Y := measurable_one.indicator hA
  have hYb : ∀ ω, |Y ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [hY, h]
  set h := expectFn P Y with hh
  have hhm : Measurable h := measurable_expectFn P hYm
  have hh1 : ∀ x, h x ≤ 1 := fun x => (abs_le.1 (abs_expectFn_le P hYb x)).2
  have hh0 : ∀ x, 0 ≤ h x := fun x => integral_nonneg fun ω => by
    by_cases hω : ω ∈ A <;> simp [hY, hω]
  have hinvY : IsPathInvariant P π Y := fun k => Eventually.of_forall fun ω =>
    indicator_shift_of_invariant hθA k ω
  have hlem := mt_lemma_17_1_1 P hπ hYm (integrable_of_bdd P π hYm hYb) hinvY
  set A₁ : Set X := {x | h x = 1} with hA₁
  have hA₁m : MeasurableSet A₁ := measurableSet_eq_fun hhm measurable_const
  have h0 : A =ᵐ[pathMeasure P π] {ω | ω 0 ∈ A₁} := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hlem] with ω hω
    change Y ω = h (ω 0) at hω
    by_cases hωA : ω ∈ A
    · have h1 : Y ω = 1 := by rw [hY, Set.indicator_of_mem hωA]; rfl
      have : ω 0 ∈ A₁ := by
        change h (ω 0) = 1
        rw [← hω, h1]
      exact iff_of_true hωA this
    · have h1 : Y ω = 0 := by rw [hY, Set.indicator_of_notMem hωA]
      have : ω 0 ∉ A₁ := by
        intro hc
        change h (ω 0) = 1 at hc
        rw [← hω, h1] at hc
        norm_num at hc
      exact iff_of_false hωA this
  refine ⟨A₁, ⟨hA₁m, fun x hx => ?_⟩, h0, fun n => ?_⟩
  · -- `h(x) = 1 = ∫ h dP(x)` and `h ≤ 1` force `h = 1`, `P(x, ·)`-a.s.
    have hharm := expectFn_harmonic_of_invariant P hA hθA x
    rw [← hh, hx] at hharm
    have hint : Integrable h (P x) := Integrable.of_bound hhm.aestronglyMeasurable 1
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hh0 y)]; exact hh1 y)
    have hii : Integrable (fun y => 1 - h y) (P x) := (integrable_const 1).sub hint
    have hnn : 0 ≤ fun y => 1 - h y := fun y => by
      simp only [Pi.zero_apply]
      linarith [hh1 y]
    have hz : ∫ y, (1 - h y) ∂P x = 0 := by
      rw [integral_sub (integrable_const 1) hint, hharm]
      simp
    rw [integral_eq_zero_iff_of_nonneg hnn hii] at hz
    have hnull : P x A₁ᶜ = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hz
      refine le_antisymm (le_of_eq_of_le ?_ (le_of_eq hz)) zero_le
      congr 1
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hA₁, Pi.zero_apply]
      constructor
      · intro hy h'
        exact hy (by linarith)
      · intro hy h'
        exact hy (by rw [h']; ring)
    exact (prob_compl_eq_zero_iff hA₁m).1 hnull
  · have hmp : MeasurePreserving (shift (X := X) n) (pathMeasure P π) (pathMeasure P π) :=
      ⟨measurable_shift n, hπ.map_shift n⟩
    have hpre := hmp.quasiMeasurePreserving.preimage_ae_eq h0
    have hAn : shift n ⁻¹' A = A := by
      ext ω
      rw [Set.mem_preimage, ← iterate_shift_one, iterate_mem_iff hθA]
    rw [hAn] at hpre
    refine hpre.trans ?_
    have : shift n ⁻¹' {ω : ℕ → X | ω 0 ∈ A₁} = {ω | ω n ∈ A₁} := by
      ext ω
      simp [shift]
    rw [this]

/-! ### Invariant restrictions -/

/-- For an invariant `π` and a set `A₁` with `P(x, A₁) = 1` for `π`-a.e. `x ∈ A₁` (Miao,
footnote 2, p. 128), `P(x, A₁) = 0` for `π`-a.e. `x ∉ A₁`. -/
theorem setLIntegral_compl_eq_zero (P : Kernel X X) {π : Measure X} [IsFiniteMeasure π]
    (hπ : IsInvariant P π) {A₁ : Set X} (hA : MeasurableSet A₁)
    (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) : ∫⁻ x in A₁ᶜ, P x A₁ ∂π = 0 := by
  have h1 : ∫⁻ x in A₁, P x A₁ ∂π = π A₁ := by
    rw [setLIntegral_congr_fun_ae hA (hinv.mono fun x hx hxA => hx hxA), setLIntegral_const,
      one_mul]
  have h2 := lintegral_add_compl (μ := π) (fun x => P x A₁) hA
  rw [h1, (isInvariant_iff P π).1 hπ A₁ hA] at h2
  exact (ENNReal.add_right_inj (measure_ne_top π A₁)).1 (h2.trans (add_zero _).symm)

/-- Miao, p. 128: if `P(x, A₁) = 1` for `π`-a.e. `x ∈ A₁`, then `B ↦ π(A₁ ∩ B)` is invariant. -/
theorem isInvariant_restrict (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) {A₁ : Set X} (hA : MeasurableSet A₁)
    (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) : IsInvariant P (π.restrict A₁) := by
  rw [isInvariant_iff]
  intro B hB
  have hπB := (isInvariant_iff P π).1 hπ
  have hout := setLIntegral_compl_eq_zero P hπ hA hinv
  have hin : ∫⁻ x in A₁, P x A₁ᶜ ∂π = 0 := by
    rw [setLIntegral_congr_fun_ae (g := fun _ => 0) hA (hinv.mono fun x hx hxA =>
      (prob_compl_eq_zero_iff hA).2 (hx hxA)), lintegral_zero]
  have hmeas : ∀ S : Set X, MeasurableSet S → Measurable fun x => P x S :=
    fun S hS => Kernel.measurable_coe P hS
  rw [Measure.restrict_apply hB]
  apply le_antisymm
  · calc ∫⁻ x in A₁, P x B ∂π ≤ ∫⁻ x in A₁, (P x (B ∩ A₁) + P x A₁ᶜ) ∂π := by
          refine lintegral_mono fun x => ?_
          calc P x B ≤ P x (B ∩ A₁) + P x (B \ A₁) := measure_le_inter_add_sdiff _ _ _
            _ ≤ P x (B ∩ A₁) + P x A₁ᶜ := by
              gcongr
              exact fun y hy => hy.2
      _ = ∫⁻ x in A₁, P x (B ∩ A₁) ∂π := by
          rw [lintegral_add_right _ (hmeas _ hA.compl), hin, add_zero]
      _ ≤ ∫⁻ x, P x (B ∩ A₁) ∂π := setLIntegral_le_lintegral _ _
      _ = π (B ∩ A₁) := hπB _ (hB.inter hA)
  · calc π (B ∩ A₁) = ∫⁻ x, P x (B ∩ A₁) ∂π := (hπB _ (hB.inter hA)).symm
      _ = ∫⁻ x in A₁, P x (B ∩ A₁) ∂π + ∫⁻ x in A₁ᶜ, P x (B ∩ A₁) ∂π :=
          (lintegral_add_compl _ hA).symm
      _ ≤ ∫⁻ x in A₁, P x B ∂π + ∫⁻ x in A₁ᶜ, P x A₁ ∂π := by
          gcongr with x x
          · exact Set.inter_subset_left
          · exact Set.inter_subset_right
      _ = ∫⁻ x in A₁, P x B ∂π := by rw [hout, add_zero]

/-- Miao, p. 128: under the same hypothesis, `B ↦ π(A₁ᶜ ∩ B)` is invariant. -/
theorem isInvariant_restrict_compl (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsFiniteMeasure π] (hπ : IsInvariant P π) {A₁ : Set X} (hA : MeasurableSet A₁)
    (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) : IsInvariant P (π.restrict A₁ᶜ) := by
  refine isInvariant_restrict P hπ hA.compl ?_
  have hout := setLIntegral_compl_eq_zero P hπ hA hinv
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe P hA), Filter.EventuallyEq,
    ae_restrict_iff' hA.compl] at hout
  filter_upwards [hout] with x hx hxA
  exact (prob_compl_eq_one_iff hA).2 (hx hxA)

/-- Miao, proof of Theorem 4.3.1 (converse), p. 128: if `A₁` is (a.e.) `P`-invariant with
`0 < π(A₁) < 1`, then `π = απ₁ + (1 − α)π₂` with `π₁ = π(A₁ ∩ ·)/α`,
`π₂ = π(A₁ᶜ ∩ ·)/(1 − α)` distinct invariant distributions, so `π` is not extremal. -/
theorem not_mem_extremePoints_of_invariantSet (P : Kernel X X) [IsMarkovKernel P]
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {A₁ : Set X}
    (hA : MeasurableSet A₁) (hinv : ∀ᵐ x ∂π, x ∈ A₁ → P x A₁ = 1) (h0 : π A₁ ≠ 0)
    (h1 : π A₁ ≠ 1) : π ∉ Set.extremePoints ℝ≥0∞ (invariantDistributions P) := by
  intro hext
  set α := π A₁ with hα
  have hαtop : α ≠ ⊤ := measure_ne_top π A₁
  have hαle : α ≤ 1 := prob_le_one
  have hα1 : 1 - α ≠ 0 := by
    intro h
    exact h1 (le_antisymm hαle (tsub_eq_zero_iff_le.1 h))
  have hα1top : 1 - α ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hc : π A₁ᶜ = 1 - α := prob_compl_eq_one_sub hA
  set π₁ := α⁻¹ • π.restrict A₁ with hπ₁
  set π₂ := (1 - α)⁻¹ • π.restrict A₁ᶜ with hπ₂
  have hm₁ : π₁ ∈ invariantDistributions P := by
    refine ⟨⟨?_⟩, (isInvariant_restrict P hπ hA hinv).smul _⟩
    rw [hπ₁, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 hαtop]
  have hm₂ : π₂ ∈ invariantDistributions P := by
    refine ⟨⟨?_⟩, (isInvariant_restrict_compl P hπ hA hinv).smul _⟩
    rw [hπ₂, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hc,
      ENNReal.inv_mul_cancel hα1 hα1top]
  have hseg : π ∈ openSegment ℝ≥0∞ π₁ π₂ := by
    refine ⟨α, 1 - α, pos_iff_ne_zero.2 h0, pos_iff_ne_zero.2 hα1,
      add_tsub_cancel_of_le hαle, ?_⟩
    rw [hπ₁, hπ₂, smul_smul, smul_smul, ENNReal.mul_inv_cancel h0 hαtop,
      ENNReal.mul_inv_cancel hα1 hα1top, one_smul, one_smul,
      Measure.restrict_add_restrict_compl hA]
  have heq := ((mem_extremePoints.1 hext).2 π₁ hm₁ π₂ hm₂ hseg).1
  have : π₁ A₁ = 1 := by
    rw [hπ₁, Measure.smul_apply, Measure.restrict_apply hA, Set.inter_self, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 hαtop]
  rw [heq] at this
  exact h1 this

/-! ### Theorem 4.3.1 -/

/-- `E_{P_ν}[1_C(x₀)] = ν(C)`. -/
theorem integral_indicator_coord_zero (P : Kernel X X) [IsMarkovKernel P] (ν : Measure X)
    {C : Set X} (hC : MeasurableSet C) :
    ∫ ω, C.indicator (1 : X → ℝ) (ω 0) ∂pathMeasure P ν = ν.real C := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
    (measurable_one.indicator hC).aestronglyMeasurable, pathMeasure_map_zero,
    integral_indicator_one hC]

/-- Miao, proof of Theorem 4.3.1, p. 127: if `(X^ℕ, P_π, θ)` is ergodic and `P_ν ≪ P_π` for an
invariant `ν`, then `ν = π` (the time averages of `1_C(x_k)` converge to `π(C)` `P_π`-a.s., hence
`P_ν`-a.s., while their `P_ν`-expectation is `ν(C)`). -/
theorem eq_of_ergodic_of_absolutelyContinuous (P : Kernel X X) [IsMarkovKernel P]
    {π ν : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure ν] (hπ : IsInvariant P π)
    (hν : IsInvariant P ν) (herg : IsErgodic (pathMeasure P π) (shift 1))
    (hac : pathMeasure P ν ≪ pathMeasure P π) : ν = π := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isProbabilityMeasure_pathMeasure P ν
  have hmpπ : MeasurePreserving (shift (X := X) 1) (pathMeasure P π) (pathMeasure P π) :=
    ⟨measurable_shift 1, hπ.map_shift 1⟩
  have hmpν : MeasurePreserving (shift (X := X) 1) (pathMeasure P ν) (pathMeasure P ν) :=
    ⟨measurable_shift 1, hν.map_shift 1⟩
  ext C hC
  set f : (ℕ → X) → ℝ := fun ω => C.indicator 1 (ω 0) with hf
  have hfm : Measurable f := (measurable_one.indicator hC).comp (measurable_pi_apply 0)
  have hfb : ∀ ω, |f ω| ≤ 1 := fun ω => by by_cases h : ω 0 ∈ C <;> simp [hf, h]
  have hint : ∀ ρ : Measure (ℕ → X), IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfb ω)
  have h1 := theorem_4_1_1_ergodic hmpπ herg hfm (hint _ inferInstance)
  have h1' := hac.ae_le h1
  have h2 := ae_tendsto_birkhoffLimit hmpν hfm (hint _ inferInstance)
  have hL : birkhoffLimit (shift 1) f =ᵐ[pathMeasure P ν]
      fun _ => ∫ ω, f ω ∂pathMeasure P π := by
    filter_upwards [h1', h2] with ω hω1 hω2
    refine tendsto_nhds_unique hω2 ?_
    simpa only [birkhoffAverage_eq_sum] using hω1
  have h3 := setIntegral_birkhoffLimit hmpν hfm (hint _ inferInstance) MeasurableSet.univ
    Set.preimage_univ
  simp only [Measure.restrict_univ] at h3
  rw [integral_congr_ae hL, integral_const, probReal_univ, one_smul,
    integral_indicator_coord_zero P π hC, integral_indicator_coord_zero P ν hC] at h3
  rw [measureReal_def, measureReal_def] at h3
  exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3).symm

/-- **Theorem 4.3.1** (Miao, p. 126), on the one-sided path space: for `π ∈ M`, the dynamical
system `(X^ℕ, X^ℕ, P_π, θ)` is ergodic iff `π` is an extreme point of the convex set `M`. -/
theorem theorem_4_3_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    IsErgodic (pathMeasure P π) (shift 1) ↔
      π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P) := by
  have := isProbabilityMeasure_pathMeasure P π
  constructor
  · intro herg
    refine mem_extremePoints.2 ⟨⟨inferInstance, hπ⟩, fun π₁ h₁ π₂ h₂ hseg => ?_⟩
    obtain ⟨a, b, ha, hb, -, hπeq⟩ := hseg
    have := h₁.1
    have := h₂.1
    have hP : pathMeasure P π = a • pathMeasure P π₁ + b • pathMeasure P π₂ := by
      rw [← hπeq, pathMeasure_add_smul]
    have hac₁ : pathMeasure P π₁ ≪ pathMeasure P π := by
      intro S hS
      rw [hP, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul] at hS
      exact (mul_eq_zero.1 (add_eq_zero.1 hS).1).resolve_left ha.ne'
    have hac₂ : pathMeasure P π₂ ≪ pathMeasure P π := by
      intro S hS
      rw [hP, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul] at hS
      exact (mul_eq_zero.1 (add_eq_zero.1 hS).2).resolve_left hb.ne'
    exact ⟨eq_of_ergodic_of_absolutelyContinuous P hπ h₁.2 herg hac₁,
      eq_of_ergodic_of_absolutelyContinuous P hπ h₂.2 herg hac₂⟩
  · intro hext A ⟨hAm, hθA⟩
    obtain ⟨A₁, ⟨hA₁m, hA₁⟩, hAe, -⟩ := lemma_4_3_1 P hπ hAm hθA
    have hPA : pathMeasure P π A = π A₁ := by
      rw [measure_congr hAe]
      change pathMeasure P π ((fun ω : ℕ → X => ω 0) ⁻¹' A₁) = _
      rw [← Measure.map_apply (measurable_pi_apply 0) hA₁m, pathMeasure_map_zero]
    rw [hPA]
    by_contra hcon
    push Not at hcon
    exact not_mem_extremePoints_of_invariantSet P hπ hA₁m
      (Eventually.of_forall fun x hx => hA₁ x hx) hcon.1 hcon.2 hext

/-- Miao, p. 128: `(X^ℕ, P_π, θ)` is ergodic iff the invariant distribution `π` is ergodic in
the sense of Definition 3.3.5. -/
theorem theorem_4_3_1_iff_isErgodicMeasure (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    IsErgodic (pathMeasure P π) (shift 1) ↔ IsErgodicMeasure P π := by
  have := isProbabilityMeasure_pathMeasure P π
  constructor
  · intro herg A ⟨hAm, hA⟩
    by_contra hcon
    push Not at hcon
    exact not_mem_extremePoints_of_invariantSet P hπ hAm
      (Eventually.of_forall fun x hx => hA x hx) hcon.1 hcon.2 ((theorem_4_3_1 P hπ).1 herg)
  · intro herg A ⟨hAm, hθA⟩
    obtain ⟨A₁, hA₁, hAe, -⟩ := lemma_4_3_1 P hπ hAm hθA
    rw [measure_congr hAe]
    change pathMeasure P π ((fun ω : ℕ → X => ω 0) ⁻¹' A₁) = 0 ∨
      pathMeasure P π ((fun ω : ℕ → X => ω 0) ⁻¹' A₁) = 1
    rw [← Measure.map_apply (measurable_pi_apply 0) hA₁.1, pathMeasure_map_zero]
    exact herg A₁ hA₁

/-- **Corollary 4.3.1** (Miao, p. 128): if `P` has a unique invariant distribution `π`, then `π`
is ergodic (Definition 3.3.5), `π` is extremal in `M`, and `(X^ℕ, P_π, θ)` is ergodic. -/
theorem corollary_4_3_1 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (huniq : ∀ ν : Measure X, IsProbabilityMeasure ν → IsInvariant P ν → ν = π) :
    IsErgodicMeasure P π ∧ π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P) ∧
      IsErgodic (pathMeasure P π) (shift 1) := by
  have hext : π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P) :=
    mem_extremePoints.2 ⟨⟨inferInstance, hπ⟩, fun π₁ h₁ π₂ h₂ _ =>
      ⟨huniq π₁ h₁.1 h₁.2, huniq π₂ h₂.1 h₂.2⟩⟩
  have herg := (theorem_4_3_1 P hπ).2 hext
  exact ⟨(theorem_4_3_1_iff_isErgodicMeasure P hπ).1 herg, hext, herg⟩

/-! ### Theorem 4.3.2 -/

/-- **Theorem 4.3.2** (strong law for Markov processes, Miao, p. 128). If `π` is an extremal
invariant distribution and `f` is bounded measurable, then for `π`-almost every `x₀`,
`(1/N) Σ_{k=1}^N f(x_k) → ∫ f dπ` for `P_{x₀}`-almost every path `(x₀, x₁, x₂, …)`. -/
theorem theorem_4_3_2 (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hext : π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P)) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ x₀ ∂π, ∀ᵐ ω ∂pathKernel P x₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, f (ω (k + 1))) atTop (𝓝 (∫ y, f y ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have herg := (theorem_4_3_1 P hπ).2 hext
  have hmp : MeasurePreserving (shift (X := X) 1) (pathMeasure P π) (pathMeasure P π) :=
    ⟨measurable_shift 1, hπ.map_shift 1⟩
  set F : (ℕ → X) → ℝ := fun ω => f (ω 0) with hF
  have hFm : Measurable F := hf.comp (measurable_pi_apply 0)
  have hFi : Integrable F (pathMeasure P π) := Integrable.of_bound hFm.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)
  have hE : ∫ ω, F ω ∂pathMeasure P π = ∫ y, f y ∂π := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable,
      pathMeasure_map_zero]
  have h1 := theorem_4_1_1_ergodic hmp herg hFm hFi
  rw [hE] at h1
  set S : Set (ℕ → X) := {ω | Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, f (ω (k + 1))) atTop (𝓝 (∫ y, f y ∂π))} with hS
  have hSm : MeasurableSet S := measurableSet_tendsto _ fun N =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hf.comp (measurable_pi_apply _))
  have hSae : ∀ᵐ ω ∂pathMeasure P π, ω ∈ S := by
    filter_upwards [h1] with ω hω
    have := tendsto_avg_succ hω
    refine this.congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, iterate_shift_one, shift_apply, add_zero]
  have hnull : pathMeasure P π Sᶜ = 0 := by
    rw [ae_iff] at hSae
    exact hSae
  rw [pathMeasure_eq_comp, Measure.bind_apply hSm.compl (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hSm.compl)] at hnull
  filter_upwards [hnull] with x hx
  rw [ae_iff]
  exact hx

/-- **Exercise 5** (Miao, p. 129), second part: the proof of Theorem 4.3.2 (`theorem_4_3_2`),
here stated for `f = 1_B` of a measurable set. -/
theorem ex_4_5_b (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hext : π ∈ Set.extremePoints ℝ≥0∞ (invariantDistributions P)) {B : Set X}
    (hB : MeasurableSet B) :
    ∀ᵐ x₀ ∂π, ∀ᵐ ω ∂pathKernel P x₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, B.indicator (1 : X → ℝ) (ω (k + 1))) atTop (𝓝 (π.real B)) := by
  have h := theorem_4_3_2 P hπ hext (measurable_one.indicator hB) (C := 1) fun x => by
    by_cases hx : x ∈ B <;> simp [hx]
  rwa [integral_indicator_one hB] at h

/-! ### Exercise 6 -/

/-- **Exercise 6** (Miao, p. 129). Two distinct ergodic invariant probability measures of a
measurable map `θ` are mutually singular. -/
theorem ex_4_6 {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {θ : Ω → Ω} (hμ : MeasurePreserving θ μ μ)
    (hν : MeasurePreserving θ ν ν) (hμe : IsErgodic μ θ) (hνe : IsErgodic ν θ) (hne : μ ≠ ν) :
    μ ⟂ₘ ν := by
  obtain ⟨C, hC, hCne⟩ : ∃ C, MeasurableSet C ∧ μ C ≠ ν C := by
    by_contra h
    push Not at h
    exact hne (Measure.ext fun C hC => h C hC)
  have hCne' : μ.real C ≠ ν.real C := by
    rw [measureReal_def, measureReal_def]
    exact fun h => hCne ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)).1 h)
  set f : Ω → ℝ := C.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hC
  have hint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; by_cases h : ω ∈ C <;> simp [hf, h])
  have hEρ : ∀ ρ : Measure Ω, ∫ ω, f ω ∂ρ = ρ.real C := fun ρ => integral_indicator_one hC
  set S : ℝ → Set Ω := fun c => {ω | Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
    ∑ n ∈ Finset.range N, f (θ^[n] ω)) atTop (𝓝 c)} with hS
  have hSm : ∀ c, MeasurableSet (S c) := fun c => measurableSet_tendsto _ fun N =>
    measurable_const.mul (Finset.measurable_sum _ fun n _ =>
      hfm.comp (hμ.measurable.iterate n))
  have hμS : μ (S (μ.real C))ᶜ = 0 := by
    have h := theorem_4_1_1_ergodic hμ hμe hfm (hint μ inferInstance)
    rw [hEρ] at h
    rw [ae_iff] at h
    exact h
  have hνS : ν (S (ν.real C))ᶜ = 0 := by
    have h := theorem_4_1_1_ergodic hν hνe hfm (hint ν inferInstance)
    rw [hEρ] at h
    rw [ae_iff] at h
    exact h
  have hdisj : S (ν.real C) ⊆ (S (μ.real C))ᶜ := fun ω h1 h2 =>
    hCne' (tendsto_nhds_unique h2 h1)
  exact ⟨S (ν.real C), hSm _, measure_mono_null hdisj hμS, hνS⟩

/-- **Exercise 6** (Miao, p. 129) for Markov processes: two distinct invariant distributions of
`P` that are ergodic (Definition 3.3.5) are mutually singular, and so are their path
measures. -/
theorem ex_4_6_markov (P : Kernel X X) [IsMarkovKernel P] {π₁ π₂ : Measure X}
    [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂] (h₁ : IsInvariant P π₁)
    (h₂ : IsInvariant P π₂) (he₁ : IsErgodicMeasure P π₁) (he₂ : IsErgodicMeasure P π₂)
    (hne : π₁ ≠ π₂) : pathMeasure P π₁ ⟂ₘ pathMeasure P π₂ ∧ π₁ ⟂ₘ π₂ := by
  have := isProbabilityMeasure_pathMeasure P π₁
  have := isProbabilityMeasure_pathMeasure P π₂
  have := isMarkovKernel_pathKernel P
  have hpne : pathMeasure P π₁ ≠ pathMeasure P π₂ := by
    intro h
    apply hne
    rw [← pathMeasure_map_zero P π₁, ← pathMeasure_map_zero P π₂, h]
  have hpath := ex_4_6 ⟨measurable_shift 1, h₁.map_shift 1⟩ ⟨measurable_shift 1, h₂.map_shift 1⟩
    ((theorem_4_3_1_iff_isErgodicMeasure P h₁).2 he₁)
    ((theorem_4_3_1_iff_isErgodicMeasure P h₂).2 he₂) hpne
  refine ⟨hpath, ?_⟩
  obtain ⟨S, hSm, hS1, hS2⟩ := hpath
  rw [pathMeasure_eq_comp, Measure.bind_apply hSm (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hSm)] at hS1
  rw [pathMeasure_eq_comp, Measure.bind_apply hSm.compl (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hSm.compl)] at hS2
  set T : Set X := {x | pathKernel P x S = 0} with hT
  have hTm : MeasurableSet T := measurableSet_eq_fun (Kernel.measurable_coe _ hSm)
    measurable_const
  refine ⟨Tᶜ, hTm.compl, ?_, ?_⟩
  · have : ∀ᵐ x ∂π₁, x ∈ T := hS1
    rw [ae_iff] at this
    exact this
  · rw [compl_compl]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hS2)
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    have hx' : pathKernel P x S = 0 := hx
    rw [prob_compl_eq_zero_iff hSm, hx']
    exact zero_ne_one

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditional independence (Miao Exercise 4)

Miao, Exercise 4, p. 129, used in the proof of Lemma 4.3.1. For random variables `ξ, η, ζ`
with values in `X, Y, Z` (on the product space `X × Y × Z` these are the three projections), with
`F_y = σ(η)` and `F_{x,y} = σ(ξ, η)`:

* `ex_4_4`: for a bounded measurable `g`, `E[f(ξ) g(ζ) | F_y] = E[f(ξ) | F_y] E[g(ζ) | F_y]` for
  **every** bounded measurable `f` iff `E[g(ζ) | F_{x,y}] = E[g(ζ) | F_y]`.

**Corrections.** As printed, the exercise asserts the equivalence of the two equations for given
`f, g`. The second equation implies the first for each `f` (`ex_4_4_of_condExp_eq`), but the
first for a single `f` does not imply the second: for `f ≡ 1` the first equation always holds
(`ex_4_4_one`), while the second can fail (`ex_4_4_counterexample`, `ξ = ζ` a fair coin and `η`
constant). The first equation must be required for all `f`. The book also takes `f, g` integrable;
then `f(ξ) g(ζ)` need not be integrable, so `f` and `g` are taken bounded.
-/

namespace Miao.ErgodicTheory

open MeasureTheory Filter
open scoped ENNReal

variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z]

/-- The σ-algebra `σ(η)` generated by a random variable (the book's `F_y`, `F_{x,y}`). -/
abbrev sigmaOf {S : Type*} [MeasurableSpace S] (η : Ω → S) : MeasurableSpace Ω :=
  MeasurableSpace.comap η inferInstance

/-- A bounded measurable function of a random variable is integrable. -/
theorem integrable_comp_of_bdd {P : Measure Ω} [IsFiniteMeasure P] {S : Type*}
    [MeasurableSpace S] {ψ : Ω → S} (hψ : Measurable ψ) {u : S → ℝ} (hu : Measurable u) {C : ℝ}
    (hC : ∀ s, |u s| ≤ C) : Integrable (fun ω => u (ψ ω)) P :=
  Integrable.of_bound (hu.comp hψ).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)

/-- **Exercise 4** (Miao, p. 129), the direction that holds for each `f`:
`E[g(ζ) | F_{x,y}] = E[g(ζ) | F_y]` implies
`E[f(ξ) g(ζ) | F_y] = E[f(ξ) | F_y] E[g(ζ) | F_y]` for bounded measurable `f, g`. -/
theorem ex_4_4_of_condExp_eq {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → X} {η : Ω → Y}
    {ζ : Ω → Z} (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ) {g : Z → ℝ}
    (hg : Measurable g) {Cg : ℝ} (hgb : ∀ z, |g z| ≤ Cg) {f : X → ℝ} (hf : Measurable f)
    {Cf : ℝ} (hfb : ∀ x, |f x| ≤ Cf)
    (h : P[fun ω => g (ζ ω) | sigmaOf (fun ω => (ξ ω, η ω))]
      =ᵐ[P] P[fun ω => g (ζ ω) | sigmaOf η]) :
    P[fun ω => f (ξ ω) * g (ζ ω) | sigmaOf η] =ᵐ[P]
      P[fun ω => f (ξ ω) | sigmaOf η] *
        P[fun ω => g (ζ ω) | sigmaOf η] := by
  set ψ : Ω → X × Y := fun ω => (ξ ω, η ω) with hψ
  have hxy : Measurable fun ω => (ξ ω, η ω) := hξ.prodMk hη
  have hFxy_le : sigmaOf ψ ≤ ‹MeasurableSpace Ω› := hxy.comap_le
  have hFy_le : sigmaOf η ≤ sigmaOf ψ := (measurable_snd.comp (comap_measurable ψ)).comap_le
  set F : Ω → ℝ := fun ω => f (ξ ω) with hF
  set G : Ω → ℝ := fun ω => g (ζ ω) with hG
  have hFi : Integrable F P := integrable_comp_of_bdd hξ hf hfb
  have hGi : Integrable G P := integrable_comp_of_bdd hζ hg hgb
  have hFG : Integrable (F * G) P := by
    have : F * G = fun ω => (fun p : X × Z => f p.1 * g p.2) (ξ ω, ζ ω) := rfl
    rw [this]
    refine integrable_comp_of_bdd (hξ.prodMk hζ) ((hf.comp measurable_fst).mul
      (hg.comp measurable_snd)) (C := Cf * Cg) fun p => ?_
    change |f p.1 * g p.2| ≤ Cf * Cg
    rw [abs_mul]
    exact mul_le_mul (hfb _) (hgb _) (abs_nonneg _) ((abs_nonneg _).trans (hfb p.1))
  have hFm : StronglyMeasurable[sigmaOf ψ] F :=
    (hf.comp (measurable_fst.comp (comap_measurable _))).stronglyMeasurable
  have hFbd : ∀ᵐ ω ∂P, ‖F ω‖ ≤ Cf := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hfb _
  -- `E[FG | F_y] = E[E[FG | F_{x,y}] | F_y] = E[F E[G | F_{x,y}] | F_y]`
  have h1 : P[F * G | sigmaOf η] =ᵐ[P] P[P[F * G | sigmaOf ψ] | sigmaOf η] :=
    (condExp_condExp_of_le hFy_le hFxy_le).symm
  have h2 : P[F * G | sigmaOf ψ] =ᵐ[P] F * P[G | sigmaOf ψ] :=
    condExp_mul_of_stronglyMeasurable_left hFm hFG hGi
  have h3 : F * P[G | sigmaOf ψ] =ᵐ[P] F * P[G | sigmaOf η] := h.mono fun ω hω => by
    simp only [Pi.mul_apply]; rw [hω]
  have hint3 : Integrable (F * P[G | sigmaOf η]) P :=
    integrable_condExp.bdd_mul hFi.aestronglyMeasurable hFbd
  have h4 : P[F * P[G | sigmaOf η] | sigmaOf η] =ᵐ[P] P[F | sigmaOf η] * P[G | sigmaOf η] :=
    condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp hint3 hFi
  exact h1.trans ((condExp_congr_ae (h2.trans h3)).trans h4)

omit [MeasurableSpace Ω] in
/-- The rectangles `{ξ ∈ A} ∩ {η ∈ B}` generate `F_{x,y} = σ(ξ, η)`. -/
theorem comap_prod_eq_generateFrom {ξ : Ω → X} {η : Ω → Y} :
    sigmaOf (fun ω => (ξ ω, η ω)) =
      MeasurableSpace.generateFrom {S | ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧
        S = ξ ⁻¹' A ∩ η ⁻¹' B} := by
  unfold sigmaOf
  rw [← generateFrom_prod, MeasurableSpace.comap_generateFrom]
  congr 1
  ext S
  simp only [Set.mem_image, Set.mem_image2, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨A, hA, B, hB, rfl⟩, rfl⟩
    exact ⟨A, B, hA, hB, by ext ω; simp⟩
  · rintro ⟨A, B, hA, hB, rfl⟩
    exact ⟨A ×ˢ B, ⟨A, hA, B, hB, rfl⟩, by ext ω; simp⟩

omit [MeasurableSpace Ω] in
/-- The rectangles form a π-system. -/
theorem isPiSystem_rectangles {ξ : Ω → X} {η : Ω → Y} :
    IsPiSystem {S : Set Ω | ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧
      S = ξ ⁻¹' A ∩ η ⁻¹' B} := by
  rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ _
  exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by ext ω; simp; tauto⟩

/-- **Exercise 4** (Miao, p. 129), corrected. For bounded measurable `g`,
`E[f(ξ) g(ζ) | F_y] = E[f(ξ) | F_y] E[g(ζ) | F_y]` for every bounded measurable `f` iff
`E[g(ζ) | F_{x,y}] = E[g(ζ) | F_y]`. -/
theorem ex_4_4 {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → X} {η : Ω → Y} {ζ : Ω → Z}
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ) {g : Z → ℝ} (hg : Measurable g)
    {Cg : ℝ} (hgb : ∀ z, |g z| ≤ Cg) :
    (∀ f : X → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      P[fun ω => f (ξ ω) * g (ζ ω) | sigmaOf η] =ᵐ[P]
        P[fun ω => f (ξ ω) | sigmaOf η] *
          P[fun ω => g (ζ ω) | sigmaOf η]) ↔
      P[fun ω => g (ζ ω) | sigmaOf (fun ω => (ξ ω, η ω))]
        =ᵐ[P] P[fun ω => g (ζ ω) | sigmaOf η] := by
  set ψ : Ω → X × Y := fun ω => (ξ ω, η ω) with hψ
  refine ⟨fun h => ?_, fun h f hf ⟨Cf, hfb⟩ => ex_4_4_of_condExp_eq hξ hη hζ hg hgb hf hfb h⟩
  have hxy : Measurable fun ω => (ξ ω, η ω) := hξ.prodMk hη
  have hFxy_le : sigmaOf ψ ≤ ‹MeasurableSpace Ω› := hxy.comap_le
  have hFy_le : sigmaOf η ≤ sigmaOf ψ := (measurable_snd.comp (comap_measurable ψ)).comap_le
  have hFy_le' : sigmaOf η ≤ ‹MeasurableSpace Ω› := hFy_le.trans hFxy_le
  set G : Ω → ℝ := fun ω => g (ζ ω) with hG
  have hGi : Integrable G P := integrable_comp_of_bdd hζ hg hgb
  set u := P[G | sigmaOf η] with hu
  have hui : Integrable u P := integrable_condExp
  -- `∫_S u = ∫_S G` for every `S ∈ F_{x,y}`
  have hrect : ∀ A B, MeasurableSet A → MeasurableSet B →
      ∫ ω in ξ ⁻¹' A ∩ η ⁻¹' B, u ω ∂P = ∫ ω in ξ ⁻¹' A ∩ η ⁻¹' B, G ω ∂P := by
    intro A B hA hB
    set FA : Ω → ℝ := fun ω => A.indicator (1 : X → ℝ) (ξ ω) with hFA
    have hFAb : ∀ x, |A.indicator (1 : X → ℝ) x| ≤ 1 := fun x => by
      by_cases hx : x ∈ A <;> simp [hx]
    have hFAi : Integrable FA P := integrable_comp_of_bdd hξ (measurable_one.indicator hA) hFAb
    have hFAbd : ∀ᵐ ω ∂P, ‖FA ω‖ ≤ 1 := Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hFAb _
    have hB' : MeasurableSet[sigmaOf η] (η ⁻¹' B) := ⟨B, hB, rfl⟩
    have hBm : MeasurableSet (η ⁻¹' B) := hη hB
    have hAm : MeasurableSet (ξ ⁻¹' A) := hξ hA
    have hind : ∀ v : Ω → ℝ, ∫ ω in ξ ⁻¹' A ∩ η ⁻¹' B, v ω ∂P =
        ∫ ω in η ⁻¹' B, (FA * v) ω ∂P := by
      intro v
      rw [Set.inter_comm, ← setIntegral_indicator hAm]
      congr 1
      ext ω
      by_cases hω : ξ ω ∈ A
      · simp [hFA, hω]
      · simp [hFA, hω]
    have hFAu : Integrable (FA * u) P := hui.bdd_mul hFAi.aestronglyMeasurable hFAbd
    have hFAG : Integrable (FA * G) P := hGi.bdd_mul hFAi.aestronglyMeasurable hFAbd
    have hpull : P[FA * u | sigmaOf η] =ᵐ[P] P[FA | sigmaOf η] * u :=
      condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp hFAu hFAi
    have hhyp := h (A.indicator 1) (measurable_one.indicator hA) ⟨1, hFAb⟩
    rw [hind, hind]
    calc ∫ ω in η ⁻¹' B, (FA * u) ω ∂P = ∫ ω in η ⁻¹' B, P[FA * u | sigmaOf η] ω ∂P :=
          (setIntegral_condExp hFy_le' hFAu hB').symm
      _ = ∫ ω in η ⁻¹' B, P[FA * G | sigmaOf η] ω ∂P := by
          refine setIntegral_congr_ae hBm ?_
          filter_upwards [hpull, hhyp] with ω h1 h2 _
          rw [h1]
          exact h2.symm
      _ = ∫ ω in η ⁻¹' B, (FA * G) ω ∂P := setIntegral_condExp hFy_le' hFAG hB'
  have hall : ∀ S, MeasurableSet[sigmaOf ψ] S → ∫ ω in S, u ω ∂P = ∫ ω in S, G ω ∂P := by
    intro S hS
    induction S, hS using MeasurableSpace.induction_on_inter comap_prod_eq_generateFrom
      isPiSystem_rectangles with
    | empty => simp
    | basic S hS =>
      obtain ⟨A, B, hA, hB, rfl⟩ := hS
      exact hrect A B hA hB
    | compl S hS ih =>
      rw [setIntegral_compl (hFxy_le S hS) hui, setIntegral_compl (hFxy_le S hS) hGi, ih,
        integral_condExp hFy_le']
    | iUnion f hdisj hf ih =>
      rw [integral_iUnion (fun i => hFxy_le _ (hf i)) hdisj hui.integrableOn,
        integral_iUnion (fun i => hFxy_le _ (hf i)) hdisj hGi.integrableOn]
      simp only [ih]
  exact (ae_eq_condExp_of_forall_setIntegral_eq hFxy_le hGi (fun s _ _ => hui.integrableOn)
    (fun s hs _ => hall s hs)
    ((stronglyMeasurable_condExp.mono hFy_le).aestronglyMeasurable)).symm

/-- For `f ≡ 1` the first equation of Exercise 4 always holds. -/
theorem ex_4_4_one {P : Measure Ω} [IsProbabilityMeasure P] {η : Ω → Y} (hη : Measurable η)
    (G : Ω → ℝ) :
    P[fun ω => 1 * G ω | sigmaOf η] =ᵐ[P]
      P[fun _ => (1 : ℝ) | sigmaOf η] *
        P[G | sigmaOf η] := by
  rw [condExp_const hη.comap_le]
  simp only [one_mul]
  exact Eventually.of_forall fun ω => by simp

/-- **Correction to Exercise 4.** The equivalence fails for a single pair `(f, g)`: with
`Ω = Bool` carrying the fair coin, `ξ = ζ = id` and `η` constant, the first equation holds for
`f ≡ 1` and `g = 1_{true}` (`ex_4_4_one`), but `E[g(ζ) | F_{x,y}] = g ≠ 1/2 = E[g(ζ) | F_y]`. -/
theorem ex_4_4_counterexample :
    ∃ (P : Measure Bool), IsProbabilityMeasure P ∧
      ¬ (P[fun ω => ({true} : Set Bool).indicator (1 : Bool → ℝ) ω |
          MeasurableSpace.comap (fun ω : Bool => (ω, ())) inferInstance] =ᵐ[P]
        P[fun ω => ({true} : Set Bool).indicator (1 : Bool → ℝ) ω |
          MeasurableSpace.comap (fun _ : Bool => ()) inferInstance]) := by
  set P : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false) with hP
  have hprob : IsProbabilityMeasure P := ⟨by
    rw [hP, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
      ← two_mul, mul_one, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]⟩
  refine ⟨P, hprob, fun h => ?_⟩
  set G : Bool → ℝ := fun ω => ({true} : Set Bool).indicator (1 : Bool → ℝ) ω with hG
  have hGm : Measurable G := measurable_of_finite _
  have hGi : Integrable G P := Integrable.of_bound hGm.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by cases ω <;> simp [hG])
  -- `F_{x,y}` is everything, so `E[G | F_{x,y}] = G`
  have hle : MeasurableSpace.comap (fun ω : Bool => (ω, ())) inferInstance ≤
      (inferInstance : MeasurableSpace Bool) :=
    (measurable_id.prodMk measurable_const).comap_le
  have hGxy : StronglyMeasurable[MeasurableSpace.comap (fun ω : Bool => (ω, ())) inferInstance]
      G := by
    have : G = (fun p : Bool × Unit => G p.1) ∘ fun ω => (ω, ()) := rfl
    rw [this]
    exact ((hGm.comp measurable_fst).comp (comap_measurable _)).stronglyMeasurable
  rw [condExp_of_stronglyMeasurable hle hGxy hGi, MeasurableSpace.comap_const,
    condExp_bot', probReal_univ, inv_one, one_smul] at h
  have hint : ∫ ω, G ω ∂P = 1 / 2 := by
    rw [hP, integral_smul_measure, integral_add_measure
      (Integrable.of_bound hGm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        cases ω <;> simp [hG]))
      (Integrable.of_bound hGm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        cases ω <;> simp [hG])),
      integral_dirac, integral_dirac]
    simp [hG]
  rw [hint] at h
  have htrue : P {true} ≠ 0 := by
    rw [hP, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ (measurableSet_singleton
      _), Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp
  rw [Filter.EventuallyEq, ae_iff] at h
  apply htrue
  refine measure_mono_null (fun ω hω => ?_) h
  rw [Set.mem_singleton_iff] at hω
  subst hω
  simp only [Set.mem_ofPred_eq, hG]
  norm_num

end Miao.ErgodicTheory

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gaussian stationary sequences (Miao Exercise 7, partial)

Miao, Exercise 7, p. 130: a centered Gaussian stationary sequence with covariance
`R_n = E X_{n+k} X_k` and `R_n → 0` is ergodic.

The intended proof: `R_n → 0` makes the sequence mixing (Definition 4.2.4), and mixing implies
ergodicity (Theorem 4.2.3). Formalised here:

* `ex_4_7_reduction`: the reduction, mixing ⇒ ergodic (Theorem 4.2.3).
* `HasCovariance`, `IsCenteredGaussian`: `E X_j X_l = R_{|j − l|}`, and every finite linear
  combination `L = Σ cᵢ X_{aᵢ}` has `E e^{iL} = e^{−E L²/2}`.
* `integral_sum_mul_sum`: `E[(Σ cᵢ X_{aᵢ})(Σ dⱼ X_{bⱼ})] = Σᵢ Σⱼ cᵢ dⱼ R_{|aᵢ − bⱼ|}`.
* `ex_4_7_cross_covariance`: if `R_n → 0`, the covariance of `Σ cᵢ X_{aᵢ}` and the shifted
  `Σ dⱼ X_{n+bⱼ}` tends to `0`.
* `ex_4_7_charFun` (**mixing for characters**): for a centered Gaussian sequence with `R_n → 0`,
  `E e^{i(Σ cᵢ X_{aᵢ} + Σ dⱼ X_{n+bⱼ})} → E e^{iΣ cᵢ X_{aᵢ}} · E e^{iΣ dⱼ X_{bⱼ}}`.

**Not formalised.** The passage from mixing for the characters `e^{i⟨t, (X_{a₁}, …)⟩}` to the
set-wise mixing of Definition 4.2.4 (by density of trigonometric polynomials in `L²` of the law
of the path, or by weak convergence of the joint finite-dimensional laws), hence the ergodicity
claim of Exercise 7 itself.
-/

namespace Miao.ErgodicTheory

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Exercise 7** (Miao, p. 130), the reduction: a mixing stationary process is ergodic
(Theorem 4.2.3). -/
theorem ex_4_7_reduction {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) (hmix : IsMixing P X) :
    IsErgodicProcess P X :=
  theorem_4_2_3 hX hst hmix

/-- Exercise 7: `R` is the covariance function, `E X_j X_l = R_{|j − l|}`. -/
def HasCovariance (P : Measure Ω) (X : ℕ → Ω → ℝ) (R : ℕ → ℝ) : Prop :=
  ∀ j l, ∫ ω, X j ω * X l ω ∂P = R (Nat.dist j l)

/-- Exercise 7: `X` is a centered Gaussian sequence: every finite linear combination
`L = Σ cᵢ X_{aᵢ}` has characteristic function `E e^{iL} = e^{−E L²/2}`. -/
def IsCenteredGaussian (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ (m : ℕ) (a : Fin m → ℕ) (c : Fin m → ℝ),
    ∫ ω, Complex.exp (Complex.I * ((∑ i, c i * X (a i) ω : ℝ) : ℂ)) ∂P =
      ((Real.exp (-(∫ ω, (∑ i, c i * X (a i) ω) ^ 2 ∂P) / 2) : ℝ) : ℂ)

/-- `E[(Σ cᵢ X_{aᵢ})(Σ dⱼ X_{bⱼ})] = Σᵢ Σⱼ cᵢ dⱼ R_{|aᵢ − bⱼ|}`. -/
theorem integral_sum_mul_sum {P : Measure Ω} {X : ℕ → Ω → ℝ} {R : ℕ → ℝ}
    (hX : ∀ j, MemLp (X j) 2 P) (hR : HasCovariance P X R) {m m' : ℕ} (a : Fin m → ℕ)
    (b : Fin m' → ℕ) (c : Fin m → ℝ) (d : Fin m' → ℝ) :
    ∫ ω, (∑ i, c i * X (a i) ω) * (∑ j, d j * X (b j) ω) ∂P =
      ∑ i, ∑ j, c i * d j * R (Nat.dist (a i) (b j)) := by
  have hint : ∀ i j, Integrable (fun ω => c i * X (a i) ω * (d j * X (b j) ω)) P := by
    intro i j
    have h := ((hX (a i)).integrable_mul (hX (b j))).const_mul (c i * d j)
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (fun ω => c i * X (a i) ω * (d j * X (b j) ω)) =
      fun ω => (c i * d j) * (X (a i) ω * X (b j) ω) := by
    ext ω; ring
  rw [this, integral_const_mul, hR]

/-- `|a − (n + b)| → ∞` as `n → ∞`. -/
theorem tendsto_dist_add (a b : ℕ) : Tendsto (fun n => Nat.dist a (n + b)) atTop atTop :=
  tendsto_atTop_atTop.2 fun M => ⟨M + a, fun n hn => by unfold Nat.dist; omega⟩

/-- **Exercise 7** (Miao, p. 130), the covariance step: if `R_n → 0`, then
`Cov(Σ cᵢ X_{aᵢ}, Σ dⱼ X_{n+bⱼ}) → 0`. -/
theorem ex_4_7_cross_covariance {P : Measure Ω} {X : ℕ → Ω → ℝ} {R : ℕ → ℝ}
    (hX : ∀ j, MemLp (X j) 2 P) (hR : HasCovariance P X R) (hR0 : Tendsto R atTop (𝓝 0))
    {m m' : ℕ} (a : Fin m → ℕ) (b : Fin m' → ℕ) (c : Fin m → ℝ) (d : Fin m' → ℝ) :
    Tendsto (fun n => ∫ ω, (∑ i, c i * X (a i) ω) * (∑ j, d j * X (n + b j) ω) ∂P) atTop
      (𝓝 0) := by
  simp_rw [integral_sum_mul_sum hX hR a (fun j => _ + b j) c d]
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin m')) fun j _ =>
      (hR0.comp (tendsto_dist_add (a i) (b j))).const_mul (c i * d j)
  simpa using h

/-- **Exercise 7** (Miao, p. 130), mixing for characters: for a centered Gaussian sequence with
covariance `R` and `R_n → 0`, `E e^{i(Σ cᵢ X_{aᵢ} + Σ dⱼ X_{n+bⱼ})} →
E e^{iΣ cᵢ X_{aᵢ}} · E e^{iΣ dⱼ X_{bⱼ}}`. -/
theorem ex_4_7_charFun {P : Measure Ω} {X : ℕ → Ω → ℝ} {R : ℕ → ℝ}
    (hX : ∀ j, MemLp (X j) 2 P) (hG : IsCenteredGaussian P X) (hR : HasCovariance P X R)
    (hR0 : Tendsto R atTop (𝓝 0)) {m : ℕ} (a b : Fin m → ℕ) (c d : Fin m → ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I *
      ((∑ i, c i * X (a i) ω + ∑ j, d j * X (n + b j) ω : ℝ) : ℂ)) ∂P) atTop
      (𝓝 ((∫ ω, Complex.exp (Complex.I * ((∑ i, c i * X (a i) ω : ℝ) : ℂ)) ∂P) *
        ∫ ω, Complex.exp (Complex.I * ((∑ j, d j * X (b j) ω : ℝ) : ℂ)) ∂P)) := by
  set A := ∑ i, ∑ i', c i * c i' * R (Nat.dist (a i) (a i')) with hA
  set B := ∑ j, ∑ j', d j * d j' * R (Nat.dist (b j) (b j')) with hB
  -- the combined family `(c, d)` at positions `(a, n + b)`
  have hsum : ∀ (n : ℕ) (ω : Ω), ∑ k, Fin.append c d k * X (Fin.append a (fun j => n + b j) k) ω
      = ∑ i, c i * X (a i) ω + ∑ j, d j * X (n + b j) ω := by
    intro n ω
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hQ : ∀ n : ℕ, ∫ ω, (∑ k, Fin.append c d k *
      X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P =
      A + B + (∑ i, ∑ j, c i * d j * R (Nat.dist (a i) (n + b j)) +
        ∑ j, ∑ i, d j * c i * R (Nat.dist (n + b j) (a i))) := by
    intro n
    simp_rw [sq]
    rw [integral_sum_mul_sum hX hR]
    rw [Fin.sum_univ_add]
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Nat.dist_add_add_left]
    rw [hA, hB]
    simp only [Finset.sum_add_distrib]
    ring
  have hlim : Tendsto (fun n : ℕ => ∑ i, ∑ j, c i * d j * R (Nat.dist (a i) (n + b j)) +
      ∑ j, ∑ i, d j * c i * R (Nat.dist (n + b j) (a i))) atTop (𝓝 0) := by
    have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ =>
        (hR0.comp (tendsto_dist_add (a i) (b j))).const_mul (c i * d j)
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
        ((hR0.comp (tendsto_dist_add (a i) (b j))).const_mul (d j * c i))
    simp only [Function.comp_apply, mul_zero, Finset.sum_const_zero] at h1 h2
    have h2' : Tendsto (fun n : ℕ => ∑ j, ∑ i, d j * c i * R (Nat.dist (n + b j) (a i))) atTop
        (𝓝 0) := h2.congr fun n => by simp_rw [Nat.dist_comm (n + _)]
    simpa using h1.add h2'
  have hQlim : Tendsto (fun n : ℕ => ∫ ω, (∑ k, Fin.append c d k *
      X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P) atTop (𝓝 (A + B)) := by
    simp_rw [hQ]
    simpa using (tendsto_const_nhds (x := A + B)).add hlim
  have hLHS : ∀ n : ℕ, ∫ ω, Complex.exp (Complex.I *
      ((∑ i, c i * X (a i) ω + ∑ j, d j * X (n + b j) ω : ℝ) : ℂ)) ∂P =
      ((Real.exp (-(∫ ω, (∑ k, Fin.append c d k *
        X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P) / 2) : ℝ) : ℂ) := by
    intro n
    rw [← hG (m + m) (Fin.append a fun j => n + b j) (Fin.append c d)]
    simp_rw [hsum]
  have hAeq : ∫ ω, (∑ i, c i * X (a i) ω) ^ 2 ∂P = A := by
    simp_rw [sq]; rw [integral_sum_mul_sum hX hR]
  have hBeq : ∫ ω, (∑ j, d j * X (b j) ω) ^ 2 ∂P = B := by
    simp_rw [sq]; rw [integral_sum_mul_sum hX hR]
  rw [hG m a c, hG m b d, hAeq, hBeq, ← Complex.ofReal_mul, ← Real.exp_add]
  simp_rw [hLHS]
  have hc : Tendsto (fun n : ℕ => -(∫ ω, (∑ k, Fin.append c d k *
      X (Fin.append a (fun j => n + b j) k) ω) ^ 2 ∂P) / 2) atTop (𝓝 (-A / 2 + -B / 2)) := by
    have := (hQlim.neg).div_const 2
    convert this using 2
    ring
  exact (Complex.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp hc)

end Miao.ErgodicTheory

set_option linter.style.longLine false
#print axioms Miao.ErgodicTheory.measurable_birkhoffSum
#print axioms Miao.ErgodicTheory.integrable_birkhoffSum
#print axioms Miao.ErgodicTheory.birkhoffSum_sub_const
#print axioms Miao.ErgodicTheory.birkhoffSum_const_sub
#print axioms Miao.ErgodicTheory.iterate_mem_iff
#print axioms Miao.ErgodicTheory.birkhoffSum_indicator
#print axioms Miao.ErgodicTheory.birkhoffMax
#print axioms Miao.ErgodicTheory.birkhoffSum_le_birkhoffMax
#print axioms Miao.ErgodicTheory.birkhoffMax_nonneg
#print axioms Miao.ErgodicTheory.birkhoffMax_mono
#print axioms Miao.ErgodicTheory.birkhoffMax_le_add
#print axioms Miao.ErgodicTheory.birkhoffMax_le_sum_abs
#print axioms Miao.ErgodicTheory.measurable_birkhoffMax
#print axioms Miao.ErgodicTheory.integrable_birkhoffMax
#print axioms Miao.ErgodicTheory.maximal_ergodic
#print axioms Miao.ErgodicTheory.birkhoffMax_indicator
#print axioms Miao.ErgodicTheory.maximal_ergodic_inter
#print axioms Miao.ErgodicTheory.upSet
#print axioms Miao.ErgodicTheory.bddAbove_range_succ_add_iff
#print axioms Miao.ErgodicTheory.preimage_upSet
#print axioms Miao.ErgodicTheory.not_bddAbove_range_iff
#print axioms Miao.ErgodicTheory.measurableSet_upSet
#print axioms Miao.ErgodicTheory.integral_upSet_nonneg
#print axioms Miao.ErgodicTheory.mul_measure_le_setIntegral
#print axioms Miao.ErgodicTheory.setIntegral_le_mul_measure
#print axioms Miao.ErgodicTheory.tendsto_div_of_bdd
#print axioms Miao.ErgodicTheory.measure_upSet_sub_eq_zero
#print axioms Miao.ErgodicTheory.measure_upSet_const_sub_eq_zero
#print axioms Miao.ErgodicTheory.birkhoffAverage_eq_div
#print axioms Miao.ErgodicTheory.ae_tendsto_birkhoffAverage_of_ergodic
#print axioms Miao.ErgodicTheory.measure_upSet_inter_eq_zero
#print axioms Miao.ErgodicTheory.measure_iInter_upSet_eq_zero
#print axioms Miao.ErgodicTheory.le_of_bddAbove_both
#print axioms Miao.ErgodicTheory.exists_tendsto_div_of_bdd
#print axioms Miao.ErgodicTheory.ae_exists_tendsto_birkhoffAverage
#print axioms Miao.ErgodicTheory.birkhoffLimit
#print axioms Miao.ErgodicTheory.measurable_birkhoffAverage
#print axioms Miao.ErgodicTheory.measurable_birkhoffLimit
#print axioms Miao.ErgodicTheory.ae_tendsto_birkhoffLimit
#print axioms Miao.ErgodicTheory.tendsto_birkhoffAverage_apply
#print axioms Miao.ErgodicTheory.tendsto_birkhoffAverage_of_apply
#print axioms Miao.ErgodicTheory.birkhoffLimit_apply_of_tendsto
#print axioms Miao.ErgodicTheory.measurable_abs_of_measurable
#print axioms Miao.ErgodicTheory.setIntegral_comp_iterate
#print axioms Miao.ErgodicTheory.setIntegral_birkhoffAverage
#print axioms Miao.ErgodicTheory.lintegral_abs_birkhoffAverage_le
#print axioms Miao.ErgodicTheory.integrable_birkhoffLimit
#print axioms Miao.ErgodicTheory.setIntegral_birkhoffLimit_of_bdd
#print axioms Miao.ErgodicTheory.truncAt
#print axioms Miao.ErgodicTheory.abs_sub_truncAt_le
#print axioms Miao.ErgodicTheory.setIntegral_birkhoffLimit
#print axioms Miao.ErgodicTheory.trajKernel
#print axioms Miao.ErgodicTheory.isMarkovKernel_trajKernel
#print axioms Miao.ErgodicTheory.pathKernel
#print axioms Miao.ErgodicTheory.isMarkovKernel_pathKernel
#print axioms Miao.ErgodicTheory.pathMeasure
#print axioms Miao.ErgodicTheory.isProbabilityMeasure_pathMeasure
#print axioms Miao.ErgodicTheory.pathMeasure_eq_comp
#print axioms Miao.ErgodicTheory.pathMeasure_dirac
#print axioms Miao.ErgodicTheory.pathKernel_map_zero
#print axioms Miao.ErgodicTheory.pathKernel_zero_mem
#print axioms Miao.ErgodicTheory.ae_pathKernel_zero
#print axioms Miao.ErgodicTheory.pathMeasure_inter_zero
#print axioms Miao.ErgodicTheory.pathMeasure_map_zero
#print axioms Miao.ErgodicTheory.natFilt
#print axioms Miao.ErgodicTheory.measurable_coord_natFilt
#print axioms Miao.ErgodicTheory.measurableSet_coord_natFilt
#print axioms Miao.ErgodicTheory.setLIntegral_succ
#print axioms Miao.ErgodicTheory.cylFn
#print axioms Miao.ErgodicTheory.measurable_cylFn
#print axioms Miao.ErgodicTheory.boxSet
#print axioms Miao.ErgodicTheory.measurableSet_boxSet
#print axioms Miao.ErgodicTheory.measure_inter_shift_box
#print axioms Miao.ErgodicTheory.pathKernel_boxSet
#print axioms Miao.ErgodicTheory.pathMeasure_boxSet
#print axioms Miao.ErgodicTheory.IsMarkovChain
#print axioms Miao.ErgodicTheory.IsMarkovChain.mk
#print axioms Miao.ErgodicTheory.IsMarkovChain.measurable
#print axioms Miao.ErgodicTheory.IsMarkovChain.fdd
#print axioms Miao.ErgodicTheory.mt_theorem_3_4_1
#print axioms Miao.ErgodicTheory.generateFrom_boxSets
#print axioms Miao.ErgodicTheory.isPiSystem_boxSets
#print axioms Miao.ErgodicTheory.mt_theorem_3_4_1_unique
#print axioms Miao.ErgodicTheory.law_eq_pathMeasure
#print axioms Miao.ErgodicTheory.IsSubstochasticKernel
#print axioms Miao.ErgodicTheory.isSubstochasticKernel_of_markov
#print axioms Miao.ErgodicTheory.isMarkovKernel_pow
#print axioms Miao.ErgodicTheory.pow_zero_apply
#print axioms Miao.ErgodicTheory.pow_succ_apply
#print axioms Miao.ErgodicTheory.pow_succ_apply'
#print axioms Miao.ErgodicTheory.mt_theorem_3_4_2
#print axioms Miao.ErgodicTheory.pow_add_eq
#print axioms Miao.ErgodicTheory.skeleton
#print axioms Miao.ErgodicTheory.skeleton_pow
#print axioms Miao.ErgodicTheory.sampledKernel
#print axioms Miao.ErgodicTheory.sampledKernel_apply
#print axioms Miao.ErgodicTheory.isMarkovKernel_sampledKernel
#print axioms Miao.ErgodicTheory.resolvent
#print axioms Miao.ErgodicTheory.resolvent_apply
#print axioms Miao.ErgodicTheory.tsum_geometric_weights
#print axioms Miao.ErgodicTheory.isMarkovKernel_resolvent
#print axioms Miao.ErgodicTheory.kfun
#print axioms Miao.ErgodicTheory.measurable_kfun
#print axioms Miao.ErgodicTheory.kfun_indicator
#print axioms Miao.ErgodicTheory.kfun_one
#print axioms Miao.ErgodicTheory.kfun_mono
#print axioms Miao.ErgodicTheory.kfun_add
#print axioms Miao.ErgodicTheory.kfun_const_mul
#print axioms Miao.ErgodicTheory.kfun_comp
#print axioms Miao.ErgodicTheory.kfun_pow_succ
#print axioms Miao.ErgodicTheory.measure_kernel_apply
#print axioms Miao.ErgodicTheory.measure_kernel_assoc
#print axioms Miao.ErgodicTheory.lintegral_kfun
#print axioms Miao.ErgodicTheory.isProbabilityMeasure_measure_kernel
#print axioms Miao.ErgodicTheory.dirac_kernel
#print axioms Miao.ErgodicTheory.kfunR
#print axioms Miao.ErgodicTheory.measurable_kfunR
#print axioms Miao.ErgodicTheory.abs_kfunR_le
#print axioms Miao.ErgodicTheory.indKernel
#print axioms Miao.ErgodicTheory.indKernel_apply
#print axioms Miao.ErgodicTheory.comp_indKernel_apply
#print axioms Miao.ErgodicTheory.isSubstochasticKernel_comp_indKernel
#print axioms Miao.ErgodicTheory.potKernel
#print axioms Miao.ErgodicTheory.potKernel_apply
#print axioms Miao.ErgodicTheory.shift
#print axioms Miao.ErgodicTheory.measurable_shift
#print axioms Miao.ErgodicTheory.shift_zero
#print axioms Miao.ErgodicTheory.shift_shift
#print axioms Miao.ErgodicTheory.shift_apply
#print axioms Miao.ErgodicTheory.integral_measure_comp
#print axioms Miao.ErgodicTheory.pathMeasure_map_coord
#print axioms Miao.ErgodicTheory.pathKernel_map_coord
#print axioms Miao.ErgodicTheory.pathKernel_coord_mem
#print axioms Miao.ErgodicTheory.pathKernel_coord_chapmanKolmogorov
#print axioms Miao.ErgodicTheory.markov_measure
#print axioms Miao.ErgodicTheory.markov_lintegral
#print axioms Miao.ErgodicTheory.markov_lintegral_mul
#print axioms Miao.ErgodicTheory.markov_lintegral_univ
#print axioms Miao.ErgodicTheory.markov_setIntegral
#print axioms Miao.ErgodicTheory.stronglyMeasurable_expect_coord
#print axioms Miao.ErgodicTheory.integrable_expect_coord
#print axioms Miao.ErgodicTheory.markov_property
#print axioms Miao.ErgodicTheory.integrable_shift_of_bdd
#print axioms Miao.ErgodicTheory.markov_property_bdd
#print axioms Miao.ErgodicTheory.mt_proposition_3_4_3
#print axioms Miao.ErgodicTheory.isMarkovChain_of_step
#print axioms Miao.ErgodicTheory.skeletonFilt
#print axioms Miao.ErgodicTheory.skeleton_isMarkovChain
#print axioms Miao.ErgodicTheory.IsInvariant
#print axioms Miao.ErgodicTheory.isInvariant_iff
#print axioms Miao.ErgodicTheory.IsInvariant.smul
#print axioms Miao.ErgodicTheory.IsInvariant.add
#print axioms Miao.ErgodicTheory.IsInvariant.pow
#print axioms Miao.ErgodicTheory.IsInvariant.map_coord
#print axioms Miao.ErgodicTheory.IsInvariant.map_shift
#print axioms Miao.ErgodicTheory.isInvariant_iff_map_shift
#print axioms Miao.ErgodicTheory.iSup_natFilt
#print axioms Miao.ErgodicTheory.expectFn
#print axioms Miao.ErgodicTheory.stronglyMeasurable_expectFn
#print axioms Miao.ErgodicTheory.measurable_expectFn
#print axioms Miao.ErgodicTheory.abs_expectFn_le
#print axioms Miao.ErgodicTheory.integrable_of_bdd
#print axioms Miao.ErgodicTheory.pathMeasure_eq_zero_of_forall
#print axioms Miao.ErgodicTheory.ae_pathMeasure_of_forall
#print axioms Miao.ErgodicTheory.pathKernel_eq_zero_of_pair
#print axioms Miao.ErgodicTheory.isProbabilityMeasure_pair
#print axioms Miao.ErgodicTheory.IsPathInvariant
#print axioms Miao.ErgodicTheory.IsInvariantRV
#print axioms Miao.ErgodicTheory.isInvariantRV_of_shift
#print axioms Miao.ErgodicTheory.condExp_eq_expectFn
#print axioms Miao.ErgodicTheory.stronglyMeasurable_iSup_natFilt
#print axioms Miao.ErgodicTheory.tendsto_expectFn_coord
#print axioms Miao.ErgodicTheory.mt_lemma_17_1_1
#print axioms Miao.ErgodicTheory.IsMeasurableTransformation
#print axioms Miao.ErgodicTheory.isMeasurableTransformation_iff
#print axioms Miao.ErgodicTheory.IsMeasurePreserving
#print axioms Miao.ErgodicTheory.isMeasurePreserving_iff
#print axioms Miao.ErgodicTheory.IsTransformationInvariant
#print axioms Miao.ErgodicTheory.ex_4_1
#print axioms Miao.ErgodicTheory.ex_4_1_empty
#print axioms Miao.ErgodicTheory.ex_4_1_compl
#print axioms Miao.ErgodicTheory.ex_4_1_iUnion
#print axioms Miao.ErgodicTheory.IsErgodic
#print axioms Miao.ErgodicTheory.isErgodic_iff_ergodic
#print axioms Miao.ErgodicTheory.iterate_shift_one
#print axioms Miao.ErgodicTheory.example_4_1_1_measurable
#print axioms Miao.ErgodicTheory.example_4_1_1_not_measurePreserving
#print axioms Miao.ErgodicTheory.iterate_finRotate
#print axioms Miao.ErgodicTheory.example_4_1_2
#print axioms Miao.ErgodicTheory.exists_uniform_fin
#print axioms Miao.ErgodicTheory.example_4_1_2_ergodic
#print axioms Miao.ErgodicTheory.ex_4_2
#print axioms Miao.ErgodicTheory.lemma_4_1_1_step
#print axioms Miao.ErgodicTheory.lemma_4_1_1_on_pos
#print axioms Miao.ErgodicTheory.lemma_4_1_1
#print axioms Miao.ErgodicTheory.theorem_4_1_1_sum_succ
#print axioms Miao.ErgodicTheory.birkhoffAverage_eq_sum
#print axioms Miao.ErgodicTheory.measurableSet_convergent
#print axioms Miao.ErgodicTheory.invariantLimit
#print axioms Miao.ErgodicTheory.invariantLimit_comp
#print axioms Miao.ErgodicTheory.measurable_invariantLimit
#print axioms Miao.ErgodicTheory.invariantLimit_ae_eq
#print axioms Miao.ErgodicTheory.birkhoffLimit_ae_eq_condExp
#print axioms Miao.ErgodicTheory.theorem_4_1_1
#print axioms Miao.ErgodicTheory.abs_birkhoffAverage_le
#print axioms Miao.ErgodicTheory.integrable_birkhoffAverage
#print axioms Miao.ErgodicTheory.integral_abs_birkhoffAverage_le
#print axioms Miao.ErgodicTheory.tendsto_integral_abs_sub_of_bdd
#print axioms Miao.ErgodicTheory.tendsto_integral_abs_sub_truncAt
#print axioms Miao.ErgodicTheory.tendsto_integral_abs_sub_birkhoffLimit
#print axioms Miao.ErgodicTheory.theorem_4_1_1_L1
#print axioms Miao.ErgodicTheory.theorem_4_1_1_condExp_const
#print axioms Miao.ErgodicTheory.theorem_4_1_1_ergodic
#print axioms Miao.ErgodicTheory.theorem_4_1_1_ergodic_L1
#print axioms Miao.ErgodicTheory.pathOf
#print axioms Miao.ErgodicTheory.window
#print axioms Miao.ErgodicTheory.pathWindow
#print axioms Miao.ErgodicTheory.pathLaw
#print axioms Miao.ErgodicTheory.IsStationary
#print axioms Miao.ErgodicTheory.measurable_pathOf
#print axioms Miao.ErgodicTheory.measurable_window
#print axioms Miao.ErgodicTheory.measurable_pathWindow
#print axioms Miao.ErgodicTheory.window_eq
#print axioms Miao.ErgodicTheory.window_zero
#print axioms Miao.ErgodicTheory.isProbabilityMeasure_pathLaw
#print axioms Miao.ErgodicTheory.boxSet_eq_preimage
#print axioms Miao.ErgodicTheory.ext_of_boxSet
#print axioms Miao.ErgodicTheory.isStationary_iff_map_shift
#print axioms Miao.ErgodicTheory.isStationary_iff_measurePreserving
#print axioms Miao.ErgodicTheory.isStationary_of_measurePreserving
#print axioms Miao.ErgodicTheory.stationary_representation
#print axioms Miao.ErgodicTheory.isStationary_comp_window
#print axioms Miao.ErgodicTheory.isStationary_of_iid
#print axioms Miao.ErgodicTheory.IsShiftInvariant
#print axioms Miao.ErgodicTheory.IsErgodicProcess
#print axioms Miao.ErgodicTheory.isShiftInvariant_of_preimage_eq
#print axioms Miao.ErgodicTheory.shiftInvariant_compl_counterexample
#print axioms Miao.ErgodicTheory.preimage_shift_mono
#print axioms Miao.ErgodicTheory.exists_invariant_ae_eq
#print axioms Miao.ErgodicTheory.isErgodicProcess_iff_isErgodic
#print axioms Miao.ErgodicTheory.invariantField
#print axioms Miao.ErgodicTheory.condExp_comp_ae_eq
#print axioms Miao.ErgodicTheory.eq_4_3
#print axioms Miao.ErgodicTheory.theorem_4_2_1
#print axioms Miao.ErgodicTheory.theorem_4_2_1_ergodic
#print axioms Miao.ErgodicTheory.IsMixing
#print axioms Miao.ErgodicTheory.theorem_4_2_3
#print axioms Miao.ErgodicTheory.theorem_4_2_4_filtration_mono
#print axioms Miao.ErgodicTheory.tendsto_avg_succ
#print axioms Miao.ErgodicTheory.indicator_shift_of_invariant
#print axioms Miao.ErgodicTheory.measure_inter_preimage_shift
#print axioms Miao.ErgodicTheory.measure_eq_zero_or_one_of_boxes
#print axioms Miao.ErgodicTheory.theorem_4_2_2
#print axioms Miao.ErgodicTheory.ex_4_5_a
#print axioms Miao.ErgodicTheory.invariantDistributions
#print axioms Miao.ErgodicTheory.convex_invariantDistributions
#print axioms Miao.ErgodicTheory.pathMeasure_add_smul
#print axioms Miao.ErgodicTheory.pathLaw_coord
#print axioms Miao.ErgodicTheory.ex_4_3
#print axioms Miao.ErgodicTheory.eq_4_4
#print axioms Miao.ErgodicTheory.IsPInvariantSet
#print axioms Miao.ErgodicTheory.IsErgodicMeasure
#print axioms Miao.ErgodicTheory.expectFn_harmonic_of_invariant
#print axioms Miao.ErgodicTheory.lemma_4_3_1
#print axioms Miao.ErgodicTheory.setLIntegral_compl_eq_zero
#print axioms Miao.ErgodicTheory.isInvariant_restrict
#print axioms Miao.ErgodicTheory.isInvariant_restrict_compl
#print axioms Miao.ErgodicTheory.not_mem_extremePoints_of_invariantSet
#print axioms Miao.ErgodicTheory.integral_indicator_coord_zero
#print axioms Miao.ErgodicTheory.eq_of_ergodic_of_absolutelyContinuous
#print axioms Miao.ErgodicTheory.theorem_4_3_1
#print axioms Miao.ErgodicTheory.theorem_4_3_1_iff_isErgodicMeasure
#print axioms Miao.ErgodicTheory.corollary_4_3_1
#print axioms Miao.ErgodicTheory.theorem_4_3_2
#print axioms Miao.ErgodicTheory.ex_4_5_b
#print axioms Miao.ErgodicTheory.ex_4_6
#print axioms Miao.ErgodicTheory.ex_4_6_markov
#print axioms Miao.ErgodicTheory.sigmaOf
#print axioms Miao.ErgodicTheory.integrable_comp_of_bdd
#print axioms Miao.ErgodicTheory.ex_4_4_of_condExp_eq
#print axioms Miao.ErgodicTheory.comap_prod_eq_generateFrom
#print axioms Miao.ErgodicTheory.isPiSystem_rectangles
#print axioms Miao.ErgodicTheory.ex_4_4
#print axioms Miao.ErgodicTheory.ex_4_4_one
#print axioms Miao.ErgodicTheory.ex_4_4_counterexample
#print axioms Miao.ErgodicTheory.ex_4_7_reduction
#print axioms Miao.ErgodicTheory.HasCovariance
#print axioms Miao.ErgodicTheory.IsCenteredGaussian
#print axioms Miao.ErgodicTheory.integral_sum_mul_sum
#print axioms Miao.ErgodicTheory.tendsto_dist_add
#print axioms Miao.ErgodicTheory.ex_4_7_cross_covariance
#print axioms Miao.ErgodicTheory.ex_4_7_charFun
