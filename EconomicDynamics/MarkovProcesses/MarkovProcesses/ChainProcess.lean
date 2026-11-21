/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainCountable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Algebra.BigOperators.Fin

/-!
# Markov processes (Definition 3.0.1) and Markov chains on path space

Miao, Chapter 3 opening and §3.1, pp. 85–87 and 94.

* **Definition 3.0.1** (p. 85): `mc_IsMarkovProcess μ X` for a process `X : ℕ → Ω → S` on a
  probability space `(Ω, μ)` with countable state space: for all `t`, `k ≤ t`, histories
  `x₀, …, xₖ` and sets `A`,
  `Pr(Xₜ₊₁ ∈ A | Xₜ = x₀, …, Xₜ₋ₖ = xₖ) = Pr(Xₜ₊₁ ∈ A | Xₜ = x₀)`. Conditional probabilities are
  elementary ratios, and the definition is stated in cross-multiplied form
  `Pr(Xₜ₊₁ ∈ A, H) Pr(Xₜ = x₀) = Pr(Xₜ₊₁ ∈ A, Xₜ = x₀) Pr(H)`, which is the book's equation
  whenever the conditioning events have positive probability and imposes nothing otherwise.
  `mc_IsTimeHomogeneous μ X`: `Pr(Xₜ₊₁ ∈ A | Xₜ = x)` does not depend on `t`.
* **The chain with transition matrix `P` and initial distribution `π₀`** (p. 86): a process
  whose finite-dimensional distributions are the path products
  `Pr(X₀ = x₀, …, Xₙ = xₙ) = π₀(x₀) p_{x₀x₁} ⋯ p_{x_{n−1}xₙ}` (`mc_cylProb`, `mc_HasChainLaw`).
  `mc_markov_of_chainLaw`: such a process is a time-homogeneous Markov process with
  `Pr(X₀ = i) = π₀ᵢ` and `Pr(Xₜ₊₁ = j | Xₜ = i) = pᵢⱼ`; `mc_marginal_of_chainLaw`: its
  distribution at time `t` is `π₀Pᵗ` (p. 94), so the `i`-th row of `Pᵗ` is the distribution `t`
  periods ahead from `i` (p. 87).

**Scope.** The existence and uniqueness of the path measure (p. 86, "a general version of this
result is stated in Theorem 3.2.3") is Theorem 3.2.3 of §3.2 and is not proved here. All the
results of §3.1 are statements about `P`, its powers and the path products, which is why the
chapter's other modules work with `P` directly; the first-passage probabilities of
`ChainCountable` are sums of the path products of this module.
-/

namespace Miao.MarkovProcesses

open MeasureTheory
open scoped ENNReal

variable {Ω S : Type*} [MeasurableSpace Ω]

/-- The history event `{Xₜ = x₀, Xₜ₋₁ = x₁, …, Xₜ₋ₖ = xₖ}`. -/
def mc_histEvent (X : ℕ → Ω → S) (t k : ℕ) (x : Fin (k + 1) → S) : Set Ω :=
  {ω | ∀ i : Fin (k + 1), X (t - i) ω = x i}

/-- **Definition 3.0.1** (Miao, p. 85): `X` is a **Markov process** under `μ`: for all `t`,
`k ≤ t`, histories `x` and sets `A`,
`Pr(Xₜ₊₁ ∈ A | Xₜ = x₀, …, Xₜ₋ₖ = xₖ) = Pr(Xₜ₊₁ ∈ A | Xₜ = x₀)` (cross-multiplied). -/
def mc_IsMarkovProcess (μ : Measure Ω) (X : ℕ → Ω → S) : Prop :=
  ∀ t k, k ≤ t → ∀ (x : Fin (k + 1) → S) (A : Set S),
    μ ({ω | X (t + 1) ω ∈ A} ∩ mc_histEvent X t k x) * μ {ω | X t ω = x 0} =
      μ ({ω | X (t + 1) ω ∈ A} ∩ {ω | X t ω = x 0}) * μ (mc_histEvent X t k x)

/-- **Definition 3.0.1** (Miao, p. 86): the Markov process is **time-homogeneous** if
`Pr(Xₜ₊₁ ∈ A | Xₜ = x)` does not depend on `t`: it is `Q(x, A)` for one `Q`. -/
def mc_IsTimeHomogeneous (μ : Measure Ω) (X : ℕ → Ω → S) : Prop :=
  ∃ Q : S → Set S → ℝ≥0∞, ∀ t x A,
    μ ({ω | X (t + 1) ω ∈ A} ∩ {ω | X t ω = x}) = Q x A * μ {ω | X t ω = x}

/-- The path product `π₀(x₀) p_{x₀x₁} ⋯ p_{x_{n−1}xₙ}`: the probability of the cylinder event
`{X₀ = x₀, …, Xₙ = xₙ}` for the chain with transition matrix `P` and initial distribution `π₀`
(Miao, p. 86). -/
noncomputable def mc_cylProb (π₀ : S → ℝ≥0∞) (P : S → S → ℝ≥0∞) (n : ℕ) (x : Fin (n + 1) → S) :
    ℝ≥0∞ :=
  π₀ (x 0) * ∏ i : Fin n, P (x i.castSucc) (x i.succ)

/-- The process `X` has the finite-dimensional distributions of the chain `(π₀, P)`. -/
def mc_HasChainLaw (μ : Measure Ω) (X : ℕ → Ω → S) (π₀ : S → ℝ≥0∞) (P : S → S → ℝ≥0∞) :
    Prop :=
  ∀ n (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), X i ω = x i} = mc_cylProb π₀ P n x

/-- The path `(X₀, …, Xₙ)` as a tuple. -/
def mc_pathVec (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) : Fin (n + 1) → S := fun i => X i ω

/-- The probability of `{(X₀, …, Xₙ) ∈ C}` is the sum of the cylinder probabilities over `C`. -/
theorem mc_measure_path_mem [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S}
    (hX : ∀ t s, MeasurableSet {ω | X t ω = s}) (n : ℕ) (C : Set (Fin (n + 1) → S)) :
    μ (mc_pathVec X n ⁻¹' C) =
      ∑' y, C.indicator (fun y => μ {ω | ∀ i : Fin (n + 1), X i ω = y i}) y := by
  have hpre : ∀ y : Fin (n + 1) → S,
      mc_pathVec X n ⁻¹' {y} = {ω | ∀ i : Fin (n + 1), X i ω = y i} := fun y => by
    ext ω; simp [mc_pathVec, funext_iff]
  have hmeas : ∀ y : Fin (n + 1) → S, MeasurableSet (mc_pathVec X n ⁻¹' {y}) := fun y => by
    rw [hpre, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => hX i (y i)
  rw [← tsum_measure_preimage_singleton (Set.to_countable C) fun y _ => hmeas y,
    tsum_subtype C (fun y => μ (mc_pathVec X n ⁻¹' {y}))]
  simp only [hpre]

/-- The key step: `Pr(Xₜ₊₁ ∈ A, (X₀, …, Xₜ) ∈ C) = Σ_{y ∈ C} Pr((X₀, …, Xₜ) = y) P(yₜ, A)`. -/
theorem mc_measure_step [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S} {π₀ : S → ℝ≥0∞}
    {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) (t : ℕ) (A : Set S) (C : Set (Fin (t + 1) → S)) :
    μ ({ω | X (t + 1) ω ∈ A} ∩ mc_pathVec X t ⁻¹' C) =
      ∑' y, C.indicator (fun y => mc_cylProb π₀ P t y *
        ∑' j, A.indicator (P (y (Fin.last t))) j) y := by
  set D : Set (Fin (t + 1 + 1) → S) := {z | z (Fin.last (t + 1)) ∈ A ∧ Fin.init z ∈ C}
  have hset : {ω | X (t + 1) ω ∈ A} ∩ mc_pathVec X t ⁻¹' C = mc_pathVec X (t + 1) ⁻¹' D := by
    ext ω
    have hinit : Fin.init (mc_pathVec X (t + 1) ω) = mc_pathVec X t ω := rfl
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, D, hinit]
    rfl
  rw [hset, mc_measure_path_mem hX, ← (Fin.snocEquiv fun _ => S).tsum_eq, ENNReal.tsum_prod',
    ENNReal.tsum_comm]
  have hsn : ∀ (j : S) (y : Fin (t + 1) → S),
      (Fin.snocEquiv fun _ => S) (j, y) = Fin.snoc y j := fun _ _ => rfl
  refine tsum_congr fun y => ?_
  simp only [hsn]
  by_cases hy : y ∈ C
  · simp only [Set.indicator_of_mem hy, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    by_cases hj : j ∈ A
    · have hD : (Fin.snoc y j : Fin (t + 1 + 1) → S) ∈ D := by
        simp [D, hj, hy, Fin.init_snoc]
      rw [Set.indicator_of_mem hD, Set.indicator_of_mem hj, hlaw, mc_cylProb, mc_cylProb,
        Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc]
      have h0 : (Fin.snoc y j : Fin (t + 1 + 1) → S) 0 = y 0 := by
        rw [show (0 : Fin (t + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      rw [h0, mul_assoc]
    · have hD : (Fin.snoc y j : Fin (t + 1 + 1) → S) ∉ D := by
        simp [D, hj]
      rw [Set.indicator_of_notMem hD, Set.indicator_of_notMem hj, mul_zero]
  · have hD : ∀ j, (Fin.snoc y j : Fin (t + 1 + 1) → S) ∉ D := fun j => by
      simp [D, hy, Fin.init_snoc]
    simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem (hD _), tsum_zero]

/-- If every `y ∈ C` ends at `s`, then
`Pr(Xₜ₊₁ ∈ A, (X₀, …, Xₜ) ∈ C) = P(s, A) Pr((X₀, …, Xₜ) ∈ C)`. -/
theorem mc_measure_step_const [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S} {π₀ : S → ℝ≥0∞}
    {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) (t : ℕ) (A : Set S) {C : Set (Fin (t + 1) → S)} {s : S}
    (hC : ∀ y ∈ C, y (Fin.last t) = s) :
    μ ({ω | X (t + 1) ω ∈ A} ∩ mc_pathVec X t ⁻¹' C) =
      (∑' j, A.indicator (P s) j) * μ (mc_pathVec X t ⁻¹' C) := by
  rw [mc_measure_step hX hlaw, mc_measure_path_mem hX, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ C
  · simp only [Set.indicator_of_mem hy, hC y hy]
    rw [hlaw t y, mul_comm]
  · simp [Set.indicator_of_notMem hy]

/-- Miao, p. 86: a process with the finite-dimensional distributions of the chain `(π₀, P)` is a
time-homogeneous Markov process (Definition 3.0.1) with `Pr(X₀ = i) = π₀ᵢ` and
`Pr(Xₜ₊₁ = j | Xₜ = i) = pᵢⱼ` (cross-multiplied). -/
theorem mc_markov_of_chainLaw [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S} {π₀ : S → ℝ≥0∞}
    {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) :
    mc_IsMarkovProcess μ X ∧ mc_IsTimeHomogeneous μ X ∧ (∀ i, μ {ω | X 0 ω = i} = π₀ i) ∧
      ∀ t i j, μ ({ω | X (t + 1) ω = j} ∩ {ω | X t ω = i}) = P i j * μ {ω | X t ω = i} := by
  -- `{Xₜ = s}` as a path event
  have hlast : ∀ t (s : S), {ω | X t ω = s} =
      mc_pathVec X t ⁻¹' {y | y (Fin.last t) = s} := fun t s => by
    ext ω; simp [mc_pathVec]
  have hhom : ∀ t s (A : Set S), μ ({ω | X (t + 1) ω ∈ A} ∩ {ω | X t ω = s}) =
      (∑' j, A.indicator (P s) j) * μ {ω | X t ω = s} := fun t s A => by
    rw [hlast]
    exact mc_measure_step_const hX hlaw t A fun y hy => hy
  refine ⟨?_, ⟨fun s A => ∑' j, A.indicator (P s) j, hhom⟩, fun i => ?_, fun t i j => ?_⟩
  · intro t k _ x A
    have hH : mc_histEvent X t k x =
        mc_pathVec X t ⁻¹' {y | ∀ i : Fin (k + 1), y ⟨t - i, by omega⟩ = x i} := by
      ext ω; simp [mc_histEvent, mc_pathVec]
    have h1 : μ ({ω | X (t + 1) ω ∈ A} ∩ mc_histEvent X t k x) =
        (∑' j, A.indicator (P (x 0)) j) * μ (mc_histEvent X t k x) := by
      rw [hH]
      refine mc_measure_step_const hX hlaw t A fun y hy => ?_
      have := hy 0
      simpa [Fin.last] using this
    rw [h1, hhom]
    ring
  · have h := hlaw 0 (fun _ => i)
    simp only [mc_cylProb, Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h
    rw [← h]
    congr 1
    ext ω
    simp
  · have h := hhom t i {j}
    simp only [Set.mem_singleton_iff] at h
    rw [h]
    congr 1
    rw [tsum_eq_single j fun k hk => by simp [hk]]
    simp

/-- Miao, pp. 87, 94: for the chain `(π₀, P)`, the distribution in period `t` is `π₀Pᵗ`:
`Pr(Xₜ = j) = Σᵢ π₀ᵢ p⁽ᵗ⁾ᵢⱼ`; in particular, starting from `i` (`π₀ = δᵢ`), it is the `i`-th
row of `Pᵗ`. -/
theorem mc_marginal_of_chainLaw [Countable S] [DecidableEq S] {μ : Measure Ω} {X : ℕ → Ω → S}
    {π₀ : S → ℝ≥0∞} {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) (t : ℕ) (j : S) :
    μ {ω | X t ω = j} = ∑' i, π₀ i * mc_powE P t i j := by
  obtain ⟨-, -, h0, hstep⟩ := mc_markov_of_chainLaw hX hlaw
  induction t generalizing j with
  | zero =>
    simp only [mc_powE, mc_idE, mul_ite, mul_one, mul_zero]
    rw [tsum_eq_single j fun i hi => by simp [hi], h0]
    simp
  | succ t ih =>
    -- partition `{Xₜ₊₁ = j}` according to `Xₜ`
    have hpart : μ {ω | X (t + 1) ω = j} =
        ∑' s, μ ({ω | X (t + 1) ω = j} ∩ {ω | X t ω = s}) := by
      have h := tsum_measure_preimage_singleton (μ := μ.restrict {ω | X (t + 1) ω = j})
        (Set.countable_univ (α := S)) (f := X t) fun s _ => hX t s
      rw [Set.preimage_univ, Measure.restrict_apply_univ] at h
      rw [← h, tsum_univ (f := fun s : S => (μ.restrict {ω | X (t + 1) ω = j}) (X t ⁻¹' {s}))]
      refine tsum_congr fun s => ?_
      rw [Measure.restrict_apply (show MeasurableSet (X t ⁻¹' {s}) from hX t s), Set.inter_comm]
      rfl
    rw [hpart]
    simp only [hstep, ih, mc_powE_succ', mc_mulE]
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun s => tsum_congr fun i => by ring

end Miao.MarkovProcesses
