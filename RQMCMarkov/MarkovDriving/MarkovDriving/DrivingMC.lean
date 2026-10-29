/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.Driving
import Mathlib.Probability.ProductMeasure

/-!
# I.i.d. uniform driving gives the Markov chain, for one sequence and for stacks (post #3)

Post #3: with the inverse-CDF update, "because `u¹` is uniform, the probability that it falls in
the interval … is exactly … `p_{2j}`, so `x²` has the correct conditional distribution. We then
repeat … with a new independent draw". Reading: under the i.i.d. product `iidUniform ℕ`
(Mathlib's `Measure.infinitePi` of `uniformIco`), the finite-dimensional laws of `drivenPath P x₀`
are those of the Markov chain with matrix `P` started at `x₀`:
`P(x_0 = s_0, …, x_T = s_T) = 1{s_0 = x₀} ∏_{t<T} P s_t s_{t+1}`. The same holds for the stack
representation with all stack entries i.i.d. uniform, so both representations of MC have the
same path law. (Identification with Mathlib's `Kernel.traj` is not done: the finite-dimensional
formula is what the later modules use.)

## Main results

* `iidUniform ι`, `isProbabilityMeasure_iidUniform`: the i.i.d. `U[0,1)` measure on `ι → ℝ`.
* `infinitePi_setOf_forall_mem`, `measurableSet_setOf_forall_mem`: an i.i.d. product gives
  `∏_{t<T} ν (B t)` to `{w : w (c t) ∈ B t, t < T}` when the coordinates `c t` are distinct.
* `infinitePi_drive_cylinder`, `infinitePi_stackDrive_cylinder`: for any update rule `G` and
  i.i.d. inputs with law `ν`, both the driven path and the stack path have the cylinder
  probabilities `1{s_0 = x₀} ∏_{t<T} ν{r : G s_t r = s_{t+1}}`.
* `pathProb P x₀ s T = 1{s 0 = x₀} ∏_{t<T} P (s t) (s (t+1))`, `pathProb_nonneg`,
  `pathProb_succ`.
* `iidUniform_drivenPath_cylinder`, `iidUniform_stackPath_cylinder` (post #3, "inverse-CDF
  with i.i.d. uniforms gives the right chain"): both cylinder probabilities equal `pathProb`.
* `map_drivenPath_singleton`, `map_stackPath_singleton`, `map_drivenPath_eq_map_stackPath`:
  the laws of `(x_0, …, x_T)` under the two representations agree.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory Finset

/-- **The i.i.d. `U[0,1)` driving measure** on `ι → ℝ`: the product (Mathlib's
`Measure.infinitePi`) of copies of `uniformIco`. With `ι = ℕ` it drives `drivenPath` (MC of the
chain); with `ι = Fin n × ℕ` it gives independent i.i.d. stacks for `stackPath` (through
`Function.curry`). -/
noncomputable def iidUniform (ι : Type*) : Measure (ι → ℝ) :=
  haveI := isProbabilityMeasure_uniformIco
  Measure.infinitePi fun _ : ι ↦ uniformIco

/-- `iidUniform ι` is a probability measure. -/
theorem isProbabilityMeasure_iidUniform (ι : Type*) : IsProbabilityMeasure (iidUniform ι) := by
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  infer_instance

/-- **Cylinder sets of an i.i.d. product**: for an injective choice `c` of coordinates,
`P(w (c t) ∈ B t for all t < T) = ∏_{t < T} ν (B t)`. -/
theorem infinitePi_setOf_forall_mem {ι α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {c : ℕ → ι} (hc : Function.Injective c) {B : ℕ → Set α}
    (hB : ∀ t, MeasurableSet (B t)) (T : ℕ) :
    Measure.infinitePi (fun _ : ι ↦ ν) {w | ∀ t < T, w (c t) ∈ B t} = ∏ t ∈ range T, ν (B t) := by
  classical
  set B' : ι → Set α := fun p ↦ {a | ∀ t < T, c t = p → a ∈ B t} with hB'def
  have hset : {w : ι → α | ∀ t < T, w (c t) ∈ B t} = Set.pi ↑((range T).image c) B' := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_range, hB'def]
    constructor
    · rintro h p ⟨t', ht', rfl⟩ t ht hct
      rw [← hc hct] at ht' ⊢
      exact h t ht
    · intro h t ht
      exact h (c t) ⟨t, ht, rfl⟩ t ht rfl
  have hB'c : ∀ t < T, B' (c t) = B t := by
    intro t ht
    ext a
    simp only [hB'def, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h t ht rfl
    · intro h t' _ hct
      rw [hc hct]
      exact h
  have hmeas : ∀ p, MeasurableSet (B' p) := by
    intro p
    have : B' p = ⋂ (t : ℕ) (_ : t < T) (_ : c t = p), B t := by
      ext a
      simp only [hB'def, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun t ↦ .iInter fun _ ↦ .iInter fun _ ↦ hB t
  rw [hset, Measure.infinitePi_pi (fun _ : ι ↦ ν) fun p _ ↦ hmeas p,
    Finset.prod_image fun a _ b _ h ↦ hc h]
  exact Finset.prod_congr rfl fun t ht ↦ by rw [hB'c t (Finset.mem_range.1 ht)]

/-- Cylinder sets are measurable. -/
theorem measurableSet_setOf_forall_mem {ι α : Type*} [MeasurableSpace α] (c : ℕ → ι)
    {B : ℕ → Set α} (hB : ∀ t, MeasurableSet (B t)) (T : ℕ) :
    MeasurableSet {w : ι → α | ∀ t < T, w (c t) ∈ B t} := by
  have : {w : ι → α | ∀ t < T, w (c t) ∈ B t} =
      ⋂ (t : ℕ) (_ : t < T), (fun w : ι → α ↦ w (c t)) ⁻¹' B t := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun t ↦ .iInter fun _ ↦ measurable_pi_apply (c t) (hB t)

variable {S : Type*}

/-- The driven path matches `s` up to `T` iff `s` starts at `x₀` and the uniforms produce the
transitions of `s` (set form of `drive_eq_iff`). -/
theorem setOf_drive_eq {α : Type*} (G : S → α → S) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    {u : ℕ → α | ∀ t ≤ T, drive G x₀ u t = s t} =
      {u | s 0 = x₀ ∧ ∀ t < T, u (id t) ∈ {r | G (s t) r = s (t + 1)}} := by
  ext u
  exact drive_eq_iff G x₀ u s T

/-- The cylinder events of a driven path are measurable. -/
theorem measurableSet_drive_cylinder {α : Type*} [MeasurableSpace α] (G : S → α → S)
    (hG : ∀ x y, MeasurableSet {r | G x r = y}) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    MeasurableSet {u : ℕ → α | ∀ t ≤ T, drive G x₀ u t = s t} := by
  rw [setOf_drive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and]
    exact measurableSet_setOf_forall_mem id (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, MeasurableSet.empty]

variable [DecidableEq S]

/-- **I.i.d. driving gives the Markov chain** (post #3, generic update): driven by i.i.d.
draws with law `ν`, `P(x₀ = s₀, …, x_T = s_T) = 1{s₀ = x₀} ∏_{t<T} ν{r : G s_t r = s_{t+1}}`. -/
theorem infinitePi_drive_cylinder {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (G : S → α → S) (hG : ∀ x y, MeasurableSet {r | G x r = y})
    (x₀ : S) (s : ℕ → S) (T : ℕ) :
    Measure.infinitePi (fun _ : ℕ ↦ ν) {u | ∀ t ≤ T, drive G x₀ u t = s t} =
      if s 0 = x₀ then ∏ t ∈ range T, ν {r | G (s t) r = s (t + 1)} else 0 := by
  rw [setOf_drive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and, ↓reduceIte]
    exact infinitePi_setOf_forall_mem ν Function.injective_id (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, measure_empty, ↓reduceIte]

/-- The stack path matches `s` up to `T` iff `s` starts at `x₀` and the stack entries
`w (s t, departureIndex s t)` produce the transitions of `s`. -/
theorem setOf_stackDrive_eq {α : Type*} (G : S → α → S) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    {w : S × ℕ → α | ∀ t ≤ T, stackDrive G x₀ (Function.curry w) t = s t} =
      {w | s 0 = x₀ ∧ ∀ t < T, w ((fun t ↦ (s t, departureIndex s t)) t) ∈
        {r | G (s t) r = s (t + 1)}} := by
  ext w
  exact stackDrive_eq_iff G x₀ (Function.curry w) s T

/-- The cylinder events of a stack path are measurable. -/
theorem measurableSet_stackDrive_cylinder {α : Type*} [MeasurableSpace α] (G : S → α → S)
    (hG : ∀ x y, MeasurableSet {r | G x r = y}) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    MeasurableSet {w : S × ℕ → α | ∀ t ≤ T, stackDrive G x₀ (Function.curry w) t = s t} := by
  rw [setOf_stackDrive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and]
    exact measurableSet_setOf_forall_mem _ (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- **I.i.d. stacks give the Markov chain** (post #3, generic update): with all stack entries
`w (i, k)` i.i.d. with law `ν`, the stack path has the same finite-dimensional laws as the
path driven by one i.i.d. sequence: `1{s₀ = x₀} ∏_{t<T} ν{r : G s_t r = s_{t+1}}`. The point:
on the event that the path is `s`, the entries used are `(s t, departureIndex s t)`, `t < T`,
which are distinct (`departureIndex_injective`). -/
theorem infinitePi_stackDrive_cylinder {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (G : S → α → S) (hG : ∀ x y, MeasurableSet {r | G x r = y})
    (x₀ : S) (s : ℕ → S) (T : ℕ) :
    Measure.infinitePi (fun _ : S × ℕ ↦ ν)
        {w | ∀ t ≤ T, stackDrive G x₀ (Function.curry w) t = s t} =
      if s 0 = x₀ then ∏ t ∈ range T, ν {r | G (s t) r = s (t + 1)} else 0 := by
  rw [setOf_stackDrive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and, ↓reduceIte]
    exact infinitePi_setOf_forall_mem ν (departureIndex_injective s)
      (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, measure_empty, ↓reduceIte]

/-! ### The inverse-CDF update with uniforms -/

/-- The **path probability** of the Markov chain with matrix `P` from `x₀`:
`pathProb P x₀ s T = 1{s 0 = x₀} ∏_{t<T} P (s t) (s (t+1))`. -/
noncomputable def pathProb (P : S → S → ℝ) (x₀ : S) (s : ℕ → S) (T : ℕ) : ℝ :=
  if s 0 = x₀ then ∏ t ∈ range T, P (s t) (s (t + 1)) else 0

/-- Path probabilities are nonnegative. -/
theorem pathProb_nonneg {P : S → S → ℝ} (hP : ∀ i j, 0 ≤ P i j) (x₀ : S)
    (s : ℕ → S) (T : ℕ) : 0 ≤ pathProb P x₀ s T := by
  unfold pathProb
  split_ifs
  · exact Finset.prod_nonneg fun t _ ↦ hP _ _
  · exact le_rfl

/-- The Markov recursion for path probabilities. -/
theorem pathProb_succ (P : S → S → ℝ) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    pathProb P x₀ s (T + 1) = pathProb P x₀ s T * P (s T) (s (T + 1)) := by
  unfold pathProb
  split_ifs
  · rw [Finset.prod_range_succ]
  · rw [zero_mul]

variable {n : ℕ}

/-- The inverse-CDF update has measurable fibres. -/
theorem measurableSet_step_eq (P : Fin n → Fin n → ℝ) (x y : Fin n) :
    MeasurableSet {r | step P x r = y} :=
  measurable_step P x (measurableSet_singleton y)

/-- The `ENNReal` product of the transition probabilities along `s`. -/
theorem prod_uniformIco_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (s : ℕ → Fin n)
    (T : ℕ) : ∏ t ∈ range T, uniformIco {r | step P (s t) r = s (t + 1)} =
      ENNReal.ofReal (∏ t ∈ range T, P (s t) (s (t + 1))) := by
  rw [ENNReal.ofReal_prod_of_nonneg fun t _ ↦ hP.nonneg _ _]
  exact Finset.prod_congr rfl fun t _ ↦ uniformIco_step_eq hP _ _

/-- **Inverse-CDF with i.i.d. uniforms gives the right chain** (post #3): under
`iidUniform ℕ`, `P(x₀ = s₀, …, x_T = s_T) = 1{s₀ = x₀} ∏_{t<T} P s_t s_{t+1}` for
`drivenPath P x₀`. -/
theorem iidUniform_drivenPath_cylinder {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (s : ℕ → Fin n) (T : ℕ) :
    iidUniform ℕ {u | ∀ t ≤ T, drivenPath P x₀ u t = s t} =
      ENNReal.ofReal (pathProb P x₀ s T) := by
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  rw [infinitePi_drive_cylinder uniformIco (step P) (measurableSet_step_eq P) x₀ s T]
  unfold pathProb
  split_ifs
  · exact prod_uniformIco_step_eq hP s T
  · exact ENNReal.ofReal_zero.symm

/-- **I.i.d. uniform stacks give the right chain** (post #3): under `iidUniform (Fin n × ℕ)`
(all stack entries i.i.d. `U[0,1)`), `stackPath` has the same finite-dimensional laws,
`1{s₀ = x₀} ∏_{t<T} P s_t s_{t+1}`. -/
theorem iidUniform_stackPath_cylinder {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (s : ℕ → Fin n) (T : ℕ) :
    iidUniform (Fin n × ℕ) {w | ∀ t ≤ T, stackPath P x₀ (Function.curry w) t = s t} =
      ENNReal.ofReal (pathProb P x₀ s T) := by
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  rw [infinitePi_stackDrive_cylinder uniformIco (step P) (measurableSet_step_eq P) x₀ s T]
  unfold pathProb
  split_ifs
  · exact prod_uniformIco_step_eq hP s T
  · exact ENNReal.ofReal_zero.symm

/-! ### The law of the first `T + 1` states -/

omit [DecidableEq S] in
/-- Extend a finite path `s : Fin (T+1) → S` to `ℕ → S` (constant after `T`). -/
def extendPath {T : ℕ} (s : Fin (T + 1) → S) (t : ℕ) : S :=
  s ⟨min t T, Nat.lt_succ_of_le (min_le_right t T)⟩

omit [DecidableEq S] in
/-- A path agrees with `s : Fin (T+1) → S` iff it agrees with `extendPath s` up to `T`. -/
theorem extendPath_eq_iff {T : ℕ} (f : ℕ → S) (s : Fin (T + 1) → S) :
    (fun t : Fin (T + 1) ↦ f t) = s ↔ ∀ t ≤ T, f t = extendPath s t := by
  constructor
  · rintro rfl t ht
    change f t = f (min t T)
    rw [min_eq_left ht]
  · intro h
    funext t
    rw [h t (Nat.lt_succ_iff.1 t.isLt)]
    unfold extendPath
    congr 1
    exact Fin.ext (min_eq_left (Nat.lt_succ_iff.1 t.isLt))

/-- The first `T + 1` states of `drivenPath`, as a random vector. -/
theorem measurable_drivenPath_restrict (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measurable fun u : ℕ → ℝ ↦ fun t : Fin (T + 1) ↦ drivenPath P x₀ u t := by
  refine measurable_to_countable' fun s ↦ ?_
  have : (fun u : ℕ → ℝ ↦ fun t : Fin (T + 1) ↦ drivenPath P x₀ u t) ⁻¹' {s} =
      {u | ∀ t ≤ T, drivenPath P x₀ u t = extendPath s t} := by
    ext u
    exact extendPath_eq_iff _ s
  rw [this]
  exact measurableSet_drive_cylinder _ (measurableSet_step_eq P) x₀ _ T

/-- The first `T + 1` states of `stackPath`, as a random vector. -/
theorem measurable_stackPath_restrict (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measurable fun w : Fin n × ℕ → ℝ ↦
      fun t : Fin (T + 1) ↦ stackPath P x₀ (Function.curry w) t := by
  refine measurable_to_countable' fun s ↦ ?_
  have : (fun w : Fin n × ℕ → ℝ ↦ fun t : Fin (T + 1) ↦ stackPath P x₀ (Function.curry w) t) ⁻¹'
      {s} = {w | ∀ t ≤ T, stackPath P x₀ (Function.curry w) t = extendPath s t} := by
    ext w
    exact extendPath_eq_iff _ s
  rw [this]
  exact measurableSet_stackDrive_cylinder _ (measurableSet_step_eq P) x₀ _ T

/-- **The law of the first `T + 1` states of MC** (post #3): the probability of each finite
path `s` is `1{s₀ = x₀} ∏_{t<T} P s_t s_{t+1}`. -/
theorem map_drivenPath_singleton {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (T : ℕ) (s : Fin (T + 1) → Fin n) :
    (iidUniform ℕ).map (fun u t ↦ drivenPath P x₀ u (t : Fin (T + 1))) {s} =
      ENNReal.ofReal (pathProb P x₀ (extendPath s) T) := by
  rw [Measure.map_apply (measurable_drivenPath_restrict P x₀ T) (measurableSet_singleton s),
    ← iidUniform_drivenPath_cylinder hP x₀ (extendPath s) T]
  congr 1
  ext u
  exact extendPath_eq_iff _ s

/-- The law of the first `T + 1` states of the stack path. -/
theorem map_stackPath_singleton {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (T : ℕ) (s : Fin (T + 1) → Fin n) :
    (iidUniform (Fin n × ℕ)).map
        (fun w t ↦ stackPath P x₀ (Function.curry w) (t : Fin (T + 1))) {s} =
      ENNReal.ofReal (pathProb P x₀ (extendPath s) T) := by
  rw [Measure.map_apply (measurable_stackPath_restrict P x₀ T) (measurableSet_singleton s),
    ← iidUniform_stackPath_cylinder hP x₀ (extendPath s) T]
  congr 1
  ext w
  exact extendPath_eq_iff _ s

/-- **The two representations have the same path law** (post #3): driving the chain by one
i.i.d. uniform sequence or by i.i.d. per-state stacks gives the same law of
`(x₀, …, x_T)`, for every `T`. -/
theorem map_drivenPath_eq_map_stackPath {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (T : ℕ) :
    (iidUniform ℕ).map (fun u t ↦ drivenPath P x₀ u (t : Fin (T + 1))) =
      (iidUniform (Fin n × ℕ)).map
        (fun w t ↦ stackPath P x₀ (Function.curry w) (t : Fin (T + 1))) :=
  Measure.ext_of_singleton fun s ↦ by
    rw [map_drivenPath_singleton hP, map_stackPath_singleton hP]

end RQMCMarkov.MarkovDriving
