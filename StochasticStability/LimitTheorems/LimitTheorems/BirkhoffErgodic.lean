/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Birkhoff's pointwise ergodic theorem (used in MT §17.1)

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

namespace MeynTweedie.LimitTheorems

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

end MeynTweedie.LimitTheorems
