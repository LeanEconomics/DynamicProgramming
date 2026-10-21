/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Irreducibility.MarkovProperty
import Mathlib.Probability.ConditionalProbability

/-!
# Markov chains on a countable space (MT §3.2)

Meyn and Tweedie, §3.2, pp. 51–54. `X` is countable with all subsets measurable (measurable
singletons). Matrix entries are taken in `[0, ∞]`, where nonnegativity is automatic.

* `IsTransitionMatrix` (3.6): rows sum to one.
* `matPow` (3.7): the matrix powers `P⁰ = I`, `Pⁿ(x, z) = Σ_y P(x, y) Pⁿ⁻¹(y, z)`.
* `matKernel`: the kernel `P(x, A) = Σ_{y ∈ A} P(x, y)` of a matrix; `matKernel_singleton`,
  `matKernel_apply` (p. 53); `isMarkovKernel_matKernel`: a transition matrix gives a transition
  probability kernel; `matKernel_pow_singleton`: the kernel powers are the matrix powers, so
  `Pⁿ(x, A) = Σ_{y ∈ A} Pⁿ(x, y)` (`matKernel_pow_apply`).
* `IsMarkovChain.fdd_points` (3.3)–(3.4): a Markov chain with a transition matrix has the
  point finite-dimensional distributions of the countable-space definition (p. 52).
* **Theorem 3.2.1** (p. 54), for the chain `P_μ` built from a transition matrix:
  `theorem_3_2_1_fdd` (3.4), `P_μ(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯ P(xₙ₋₁, xₙ)`;
  `theorem_3_2_1` (3.5), `P_μ(Φₙ₊₁ = y | Φₙ = xₙ, …, Φ₀ = x₀) = P(xₙ, y)`;
  `pathMeasure_initial_coord` (3.8), `P_μ(Φ₀ = x, Φₙ = y) = μ(x) Pⁿ(x, y)`; and
  `pathMeasure_inter_initial` (3.1), `P_μ(Φ ∈ B, Φ₀ = x₀) = μ(x₀) P_{x₀}(Φ ∈ B)`.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*}

/-! ### Transition matrices and their powers -/

/-- A Markov transition matrix (3.6), MT p. 53: every row sums to one. -/
def IsTransitionMatrix (p : X → X → ℝ≥0∞) : Prop := ∀ x, ∑' y, p x y = 1

open scoped Classical in
/-- The matrix powers (3.7), MT p. 53: `P⁰ = I` and `Pⁿ⁺¹(x, z) = Σ_y P(x, y) Pⁿ(y, z)`. -/
noncomputable def matPow (p : X → X → ℝ≥0∞) : ℕ → X → X → ℝ≥0∞
  | 0 => fun x z => if x = z then 1 else 0
  | n + 1 => fun x z => ∑' y, p x y * matPow p n y z

variable [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- The kernel of a matrix: `P(x, A) = Σ_{y ∈ A} P(x, y)` (MT p. 53). -/
noncomputable def matKernel (p : X → X → ℝ≥0∞) : Kernel X X :=
  Kernel.ofFunOfCountable fun x => Measure.sum fun y => p x y • Measure.dirac y

/-- `P(x, {y}) = P(x, y)`. -/
theorem matKernel_singleton (p : X → X → ℝ≥0∞) (x y : X) : matKernel p x {y} = p x y :=
  Measure.sum_smul_dirac_singleton

/-- `P(x, A) = Σ_{y ∈ A} P(x, y)`. -/
theorem matKernel_apply (p : X → X → ℝ≥0∞) (x : X) (A : Set X) :
    matKernel p x A = ∑' y, A.indicator (p x) y := by
  rw [← Measure.tsum_indicator_apply_singleton _ A
    (Set.Countable.measurableSet (Set.to_countable A))]
  simp_rw [matKernel_singleton]

/-- A transition matrix gives a transition probability kernel. -/
theorem isMarkovKernel_matKernel {p : X → X → ℝ≥0∞} (hp : IsTransitionMatrix p) :
    IsMarkovKernel (matKernel p) :=
  ⟨fun x => ⟨by rw [matKernel_apply]; simpa using hp x⟩⟩

/-- Every measure on `X` is determined by its values on points: `∫ f dν = Σ_x f(x) ν{x}`. -/
theorem lintegral_matKernel (p : X → X → ℝ≥0∞) (x : X) (f : X → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel p x = ∑' y, p x y * f y := by
  rw [lintegral_countable']
  simp_rw [matKernel_singleton, mul_comm]

/-- The kernel powers are the matrix powers: `Pⁿ(x, {z}) = Pⁿ(x, z)` (MT p. 53). -/
theorem matKernel_pow_singleton (p : X → X → ℝ≥0∞) (n : ℕ) (x z : X) :
    (matKernel p ^ n) x {z} = matPow p n x z := by
  classical
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton z), matPow]
    by_cases h : x = z <;> simp [h]
  | succ n ih =>
    rw [pow_succ_apply _ n x (measurableSet_singleton z), lintegral_matKernel]
    simp_rw [ih]
    rfl

/-- `Pⁿ(x, A) = Σ_{y ∈ A} Pⁿ(x, y)` (MT p. 53). -/
theorem matKernel_pow_apply (p : X → X → ℝ≥0∞) (n : ℕ) (x : X) (A : Set X) :
    (matKernel p ^ n) x A = ∑' y, A.indicator (matPow p n x) y := by
  rw [← Measure.tsum_indicator_apply_singleton _ A
    (Set.Countable.measurableSet (Set.to_countable A))]
  simp_rw [matKernel_pow_singleton]

/-- The powers of a transition matrix are transition matrices. -/
theorem isTransitionMatrix_matPow {p : X → X → ℝ≥0∞} (hp : IsTransitionMatrix p) (n : ℕ) :
    IsTransitionMatrix (matPow p n) := fun x => by
  have := isMarkovKernel_matKernel hp
  have := isMarkovKernel_pow (matKernel p) n
  have h := matKernel_pow_apply p n x univ
  simp only [measure_univ, indicator_univ] at h
  exact h.symm

/-! ### Theorem 3.2.1 -/

/-- The nested integral (3.20) at points is the product (3.4). -/
theorem cylFn_singletons (p : X → X → ℝ≥0∞) (n : ℕ) (x : ℕ → X) (y : X) :
    cylFn (matKernel p) n (fun i => {x i}) y =
      ({x 0} : Set X).indicator (fun _ => ∏ i ∈ Finset.range n, p (x i) (x (i + 1))) y := by
  induction n generalizing x y with
  | zero => simp only [cylFn, Finset.range_zero, Finset.prod_empty]; rfl
  | succ n ih =>
    simp only [cylFn]
    by_cases hy : y = x 0
    · subst hy
      simp only [mem_singleton_iff, indicator_of_mem]
      simp_rw [ih (fun i => x (i + 1))]
      rw [lintegral_indicator_const (measurableSet_singleton _), matKernel_singleton,
        Finset.prod_range_succ', mul_comm]
    · simp [hy]

/-- (3.4), MT p. 52: `P_μ(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯ P(xₙ₋₁, xₙ)`. -/
theorem theorem_3_2_1_fdd (p : X → X → ℝ≥0∞) [IsMarkovKernel (matKernel p)] (μ : Measure X)
    (n : ℕ) (x : ℕ → X) :
    pathMeasure (matKernel p) μ {ω | ∀ i ≤ n, ω i = x i} =
      μ {x 0} * ∏ i ∈ Finset.range n, p (x i) (x (i + 1)) := by
  have h := pathMeasure_boxSet (matKernel p) μ n (A := fun i => {x i})
    fun i => measurableSet_singleton _
  simp_rw [cylFn_singletons] at h
  rw [lintegral_indicator_const (measurableSet_singleton _), mul_comm] at h
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- The countable-space definition (3.3)–(3.4), MT p. 52: every Markov chain with transition
matrix `P` and initial distribution `μ` has `P(Φ₀ = x₀, …, Φₙ = xₙ) = μ(x₀) P(x₀, x₁) ⋯
P(xₙ₋₁, xₙ)`. -/
theorem IsMarkovChain.fdd_points {p : X → X → ℝ≥0∞} {μ : Measure X} {pr : Measure Ω}
    {Φ : ℕ → Ω → X} (h : IsMarkovChain (matKernel p) μ pr Φ) (n : ℕ) (x : ℕ → X) :
    pr {ω | ∀ i ≤ n, Φ i ω = x i} = μ {x 0} * ∏ i ∈ Finset.range n, p (x i) (x (i + 1)) := by
  have hf := h.fdd n (fun i => {x i}) fun i => measurableSet_singleton _
  simp only [mem_singleton_iff] at hf
  simp_rw [cylFn_singletons] at hf
  rw [hf, lintegral_indicator_const (measurableSet_singleton _), mul_comm]

/-- **Theorem 3.2.1** (MT p. 54), (3.5): for a transition matrix `P` and initial distribution
`μ`, the chain `P_μ` satisfies `P_μ(Φₙ₊₁ = y | Φₙ = xₙ, …, Φ₀ = x₀) = P(xₙ, y)` whenever the
conditioning event has positive probability. -/
theorem theorem_3_2_1 (p : X → X → ℝ≥0∞) [IsMarkovKernel (matKernel p)] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ℕ → X) (y : X)
    (hpos : pathMeasure (matKernel p) μ {ω | ∀ i ≤ n, ω i = x i} ≠ 0) :
    (pathMeasure (matKernel p) μ)[{ω | ω (n + 1) = y} | {ω | ∀ i ≤ n, ω i = x i}] =
      p (x n) y := by
  classical
  have := isProbabilityMeasure_pathMeasure (matKernel p) μ
  set x' : ℕ → X := fun i => if i = n + 1 then y else x i
  have hset : {ω : ℕ → X | ∀ i ≤ n, ω i = x i} ∩ {ω | ω (n + 1) = y} =
      {ω | ∀ i ≤ n + 1, ω i = x' i} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, x']
    constructor
    · rintro ⟨h, hy⟩ i hi
      rcases Nat.lt_or_ge i (n + 1) with hl | hl
      · simp only [show i ≠ n + 1 by omega, ite_false]; exact h i (by omega)
      · simp only [show i = n + 1 by omega, ite_true]; exact hy
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i (by omega); simpa [show i ≠ n + 1 by omega] using this
      · have := h (n + 1) le_rfl; simpa using this
  have hprod : ∏ i ∈ Finset.range (n + 1), p (x' i) (x' (i + 1)) =
      (∏ i ∈ Finset.range n, p (x i) (x (i + 1))) * p (x n) y := by
    rw [Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      simp only [x', show i ≠ n + 1 by omega, show i + 1 ≠ n + 1 by omega, ite_false]
    · simp [x']
  have hmeas : MeasurableSet {ω : ℕ → X | ∀ i ≤ n, ω i = x i} := by
    have : {ω : ℕ → X | ∀ i ≤ n, ω i = x i} = boxSet n (fun i => {x i}) := by
      ext ω; simp [boxSet]
    rw [this]; exact measurableSet_boxSet n fun i => measurableSet_singleton _
  have hc := theorem_3_2_1_fdd p μ n x
  have htop : μ {x 0} * ∏ i ∈ Finset.range n, p (x i) (x (i + 1)) ≠ ⊤ :=
    hc ▸ measure_ne_top _ _
  rw [hc] at hpos
  have hx0 : x' 0 = x 0 := by simp [x']
  rw [cond_apply hmeas, hset, theorem_3_2_1_fdd p μ (n + 1) x', hprod, hc, hx0,
    ← mul_assoc (μ {x 0}), ← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]

omit [Countable X] in
/-- (3.1), MT p. 51: `P_μ(Φ ∈ B, Φ₀ = x₀) = μ(x₀) P_{x₀}(Φ ∈ B)`. -/
theorem pathMeasure_inter_initial (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    {B : Set (ℕ → X)} (hB : MeasurableSet B) (x₀ : X) :
    pathMeasure P μ (B ∩ {ω | ω 0 = x₀}) = μ {x₀} * pathKernel P x₀ B := by
  have h := pathMeasure_inter_zero P μ hB (measurableSet_singleton x₀)
  simp only [mem_singleton_iff] at h
  rw [h, lintegral_singleton, mul_comm]

/-- (3.8), MT p. 53: `P_μ(Φ₀ = x, Φₙ = y) = μ(x) Pⁿ(x, y)`. -/
theorem pathMeasure_initial_coord (p : X → X → ℝ≥0∞) [IsMarkovKernel (matKernel p)]
    (μ : Measure X) (n : ℕ) (x y : X) :
    pathMeasure (matKernel p) μ ({ω | ω n = y} ∩ {ω | ω 0 = x}) = μ {x} * matPow p n x y := by
  have hB : MeasurableSet {ω : ℕ → X | ω n = y} :=
    (measurable_pi_apply n : Measurable fun ω : ℕ → X => ω n) (measurableSet_singleton y)
  rw [pathMeasure_inter_initial _ μ hB x]
  congr 1
  have := pathKernel_coord_mem (matKernel p) x n (measurableSet_singleton y)
  simp only [mem_singleton_iff] at this
  rw [this, matKernel_pow_singleton]

end MeynTweedie.Irreducibility
