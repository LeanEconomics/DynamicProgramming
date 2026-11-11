/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ErgodicTheory.BirkhoffErgodic
import ErgodicTheory.MarkovProperty
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

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
