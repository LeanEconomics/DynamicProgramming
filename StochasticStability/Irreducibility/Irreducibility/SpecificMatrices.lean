/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Irreducibility.CountableChains
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Specific transition matrices (MT §3.3)

Meyn and Tweedie, §3.3, pp. 54–59. Each matrix is shown to be a Markov transition matrix
(3.6), so Theorem 3.2.1 (`theorem_3_2_1`, with `isMarkovKernel_matKernel`) builds the chain.

* §3.3.1, `fwdRecMatrix`: the forward recurrence time chain `V⁺` (p. 54), with state `k`
  standing for `V⁺ = k + 1`; `isTransitionMatrix_fwdRecMatrix`.
* §3.3.1, `ptail` (3.9) and `bwdRecMatrix` (3.10): the backward recurrence time chain `V⁻`
  (p. 55); `bwdRecMatrix_rowSum` (rows sum to one on `{x : p̄(x) ≠ 0}`),
  `ptail_ne_zero_of_bwdRecMatrix` (this set is closed, so it is the state space), and
  `ptail_ne_zero_iff` (it is `{0, …, M − 1}`, `M = sup{m : p(m) > 0}`).
* §3.3.2, `rwMatrix` (3.11): the random walk on `ℤ`, `P(x, y) = Γ(y − x)`;
  `isTransitionMatrix_rwMatrix`, `rwMatrix_translate` (translation invariance), `rw_step_law`.
* §3.3.2, `rwhlMatrix` (3.13)–(3.14): the random walk on the half line `ℤ₊`,
  `P(x, y) = Γ(y − x)` for `y > 0` and `P(x, 0) = Γ(−∞, −x]`; `isTransitionMatrix_rwhlMatrix`.
* §3.3.2, `storage_increment_singleton`: the increment law of the simple storage model,
  `P(S − J = x) = Σᵢ H(i) G(i − x)`; see the correction below.
* §3.3.3, `poissonWeight` (3.14)–(3.15), (3.19): `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)`, with
  `tsum_poissonWeight` (`Σⱼ pⱼ = 1`).
* **Proposition 3.3.1** (`proposition_3_3_1`, p. 56): the GI/M/1 matrix `giM1Matrix` is a
  transition matrix, and it is the random walk on a half line with `Γ(k) = p_{1−k}`.
* **Proposition 3.3.2** (`proposition_3_3_2`, p. 57): the M/G/1 matrix `mG1Matrix` is a transition
  matrix.
* **Proposition 3.3.3** (`proposition_3_3_3`, p. 58): the linear model on `ℚ` has transition
  matrix `P(r, q) = Γ(q − αr)`.

**Corrections.**
* The displayed matrix for `V⁻` (p. 55) puts `b(x + 1)`, `b(j) = p(j + 1)/p̄(j)`, in row `x`,
  column `0`; by (3.10) the entry is `p(x + 1)/p̄(x) = b(x)`. With `p(1) = p(2) = 1/2` the display
  gives `P(0, 0) = b(1) = 1` but (3.10) gives `1/2` (`bwdRecMatrix_display_counterexample`). The
  matrix is `bwdRecMatrix` (rows `b(0), b(1), …`).
* The storage-model formula `Γ(x) = Σᵢ H(i) G(x + i)` (p. 56) has the wrong sign: with input
  `S ∼ H` and release `J ∼ G`, `P(S − J = x) = Σᵢ H(i) G(i − x)` (`storage_increment_singleton`).
  With `H = δ₀`, `G = δ₁` the book's formula gives `Γ(1) = 1`, while `S − J = −1` surely
  (`storage_increment_counterexample`).
* (3.19) is stated for `j ≥ 1` in the display but for every `j ≥ 0` in the text; `q₀` is needed
  (it is the first column), and `poissonWeight` is defined for all `j ≥ 0`.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal NNReal

/-! ### Forward and backward recurrence time chains -/

/-- The forward recurrence time chain `V⁺` (MT p. 54) for a renewal increment law `p` on
`{1, 2, …}`. State `k` stands for `V⁺ = k + 1`: from `V⁺ = 1` the chain jumps to `j` with
probability `p(j)`, and from `V⁺ = k + 1 > 1` it moves to `k`. -/
noncomputable def fwdRecMatrix (p : ℕ → ℝ≥0∞) (k j : ℕ) : ℝ≥0∞ :=
  if k = 0 then p (j + 1) else if j + 1 = k then 1 else 0

/-- The forward recurrence time matrix is a transition matrix when `p` is a probability on
`{1, 2, …}`. -/
theorem isTransitionMatrix_fwdRecMatrix {p : ℕ → ℝ≥0∞} (hp : ∑' j, p (j + 1) = 1) :
    IsTransitionMatrix (fwdRecMatrix p) := fun k => by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [fwdRecMatrix] using hp
  · simp only [fwdRecMatrix, Nat.pos_iff_ne_zero.1 hk, ite_false]
    rw [tsum_eq_single (k - 1) fun j hj => by simp only [ite_eq_right_iff]; omega]
    simp only [ite_eq_left_iff]
    omega

/-- The tail `p̄(n) = Σ_{j ≥ n + 1} p(j)` (3.9), MT p. 54. -/
noncomputable def ptail (p : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := ∑' j, p (j + n + 1)

/-- `p̄(n) = p(n + 1) + p̄(n + 1)`. -/
theorem ptail_eq (p : ℕ → ℝ≥0∞) (n : ℕ) : ptail p n = p (n + 1) + ptail p (n + 1) := by
  rw [ptail, tsum_eq_zero_add' ENNReal.summable, ptail]
  congr 1
  · simp
  · exact tsum_congr fun j => by ring_nf

/-- `p̄(x) ≠ 0` iff `p(m) > 0` for some `m > x`, i.e. iff `x < M = sup{m : p(m) > 0}`. -/
theorem ptail_ne_zero_iff (p : ℕ → ℝ≥0∞) (x : ℕ) : ptail p x ≠ 0 ↔ ∃ m, x < m ∧ p m ≠ 0 := by
  rw [ptail, ne_eq, ENNReal.tsum_eq_zero]
  push Not
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j + x + 1, by omega, hj⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m - x - 1, by rwa [show m - x - 1 + x + 1 = m by omega]⟩

/-- The backward recurrence time chain `V⁻` (3.10), MT p. 55:
`P(x, x + 1) = p̄(x + 1)/p̄(x)` and `P(x, 0) = p(x + 1)/p̄(x)`. -/
noncomputable def bwdRecMatrix (p : ℕ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if y = x + 1 then ptail p (x + 1) / ptail p x else if y = 0 then p (x + 1) / ptail p x else 0

/-- The rows of the backward recurrence matrix sum to one on `{x : 0 < p̄(x) < ∞}`. -/
theorem bwdRecMatrix_rowSum (p : ℕ → ℝ≥0∞) {x : ℕ} (h0 : ptail p x ≠ 0) (ht : ptail p x ≠ ⊤) :
    ∑' y, bwdRecMatrix p x y = 1 := by
  rw [tsum_eq_sum (s := {0, x + 1}) fun y hy => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    simp [bwdRecMatrix, hy.1, hy.2]]
  rw [Finset.sum_pair (by omega)]
  simp only [bwdRecMatrix, show (0 : ℕ) ≠ x + 1 by omega, ite_false, ite_true]
  rw [ENNReal.div_add_div_same, ← ptail_eq, ENNReal.div_self h0 ht]

/-- The set `{x : p̄(x) ≠ 0}` is closed for `V⁻` (when `p̄(0) ≠ 0`), so it is the state space
`{0, …, M − 1}` of MT p. 55. -/
theorem ptail_ne_zero_of_bwdRecMatrix (p : ℕ → ℝ≥0∞) (h00 : ptail p 0 ≠ 0) {x y : ℕ}
    (h : bwdRecMatrix p x y ≠ 0) : ptail p y ≠ 0 := by
  by_cases hy : y = x + 1
  · subst hy
    simp only [bwdRecMatrix, ite_true] at h
    exact fun h' => h (by simp [h'])
  · by_cases hy0 : y = 0
    · subst hy0; exact h00
    · simp [bwdRecMatrix, hy, hy0] at h

/-- The `V⁻` matrix has `P(x, 0) = b(x)`, with `b(j) = p(j + 1)/p̄(j)`. -/
theorem bwdRecMatrix_zero (p : ℕ → ℝ≥0∞) (x : ℕ) :
    bwdRecMatrix p x 0 = p (x + 1) / ptail p x := by
  simp [bwdRecMatrix]

/-- The renewal law with `p(1) = p(2) = 1/2`. -/
noncomputable def halfHalf (j : ℕ) : ℝ≥0∞ := if j = 1 ∨ j = 2 then 2⁻¹ else 0

/-- **Correction** (MT p. 55): the displayed `V⁻` matrix has `b(1) = p(2)/p̄(1)` in row `0`,
column `0`, but (3.10) gives `P(0, 0) = p(1)/p̄(0)`. For `p(1) = p(2) = 1/2` these are `1` and
`1/2`. -/
theorem bwdRecMatrix_display_counterexample :
    bwdRecMatrix halfHalf 0 0 ≠ halfHalf 2 / ptail halfHalf 1 := by
  have h0 : ptail halfHalf 0 = 1 := by
    rw [ptail, tsum_eq_sum (s := {0, 1}) fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp only [halfHalf]; split_ifs with h
      · exfalso; omega
      · rfl]
    simp [halfHalf, ENNReal.inv_two_add_inv_two]
  have h1 : ptail halfHalf 1 = 2⁻¹ := by
    rw [ptail, tsum_eq_single 0 fun j hj => by
      simp only [halfHalf]; split_ifs with h
      · exfalso; omega
      · rfl]
    simp [halfHalf]
  have e1 : halfHalf (0 + 1) = 2⁻¹ := by simp [halfHalf]
  have e2 : halfHalf 2 = 2⁻¹ := by simp [halfHalf]
  rw [bwdRecMatrix_zero, h0, h1, e1, e2, div_one, ENNReal.div_self (by simp) (by simp)]
  intro h
  rw [ENNReal.inv_eq_one] at h
  norm_num at h

/-! ### Random walks -/

/-- The random walk on `ℤ` (3.11), MT p. 55: `P(x, y) = Γ(y − x)`. -/
def rwMatrix (Γ : ℤ → ℝ≥0∞) (x y : ℤ) : ℝ≥0∞ := Γ (y - x)

/-- The random walk matrix is a transition matrix when `Γ` is a probability on `ℤ`. -/
theorem isTransitionMatrix_rwMatrix {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' k, Γ k = 1) :
    IsTransitionMatrix (rwMatrix Γ) := fun x => by
  rw [← hΓ]
  exact (Equiv.subRight x).tsum_eq Γ

/-- Translation invariance of the random walk (MT p. 55). -/
theorem rwMatrix_translate (Γ : ℤ → ℝ≥0∞) (x y c : ℤ) :
    rwMatrix Γ (x + c) (y + c) = rwMatrix Γ x y := by
  simp [rwMatrix]

/-- (3.11): if `W ∼ ν`, then `P(x + W = y) = ν{y − x}`. -/
theorem rw_step_law (ν : Measure ℤ) (x y : ℤ) :
    (ν.map fun w => x + w) {y} = ν {y - x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y)]
  congr 1
  ext w
  simp only [mem_preimage, mem_singleton_iff]
  omega

/-- The random walk on the half line `ℤ₊` (3.12)–(3.14), MT pp. 55–56:
`P(x, y) = Γ(y − x)` for `y > 0` and `P(x, 0) = Γ(−∞, −x]`. -/
noncomputable def rwhlMatrix (Γ : ℤ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if y = 0 then ∑' k : ℤ, (if k ≤ -(x : ℤ) then Γ k else 0) else Γ ((y : ℤ) - x)

/-- The half-line random walk matrix is a transition matrix when `Γ` is a probability on `ℤ`. -/
theorem isTransitionMatrix_rwhlMatrix {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' k, Γ k = 1) :
    IsTransitionMatrix (rwhlMatrix Γ) := fun x => by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [rwhlMatrix, ite_true, Nat.add_one_ne_zero, ite_false]
  have hg : Function.Injective fun y : ℕ => ((y + 1 : ℕ) : ℤ) - x := fun a b h => by
    simp only at h; omega
  have hsupp : Function.support (fun k : ℤ => if -(x : ℤ) < k then Γ k else 0) ⊆
      Set.range fun y : ℕ => ((y + 1 : ℕ) : ℤ) - x := by
    intro k hk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hk
    obtain ⟨hk, -⟩ := hk
    exact ⟨(k + x - 1).toNat, by simp only; omega⟩
  have h2 := hg.tsum_eq hsupp
  simp only [show ∀ y : ℕ, -(x : ℤ) < ((y + 1 : ℕ) : ℤ) - x by intro y; omega, ite_true] at h2
  rw [h2, ← ENNReal.tsum_add, ← hΓ]
  refine tsum_congr fun k => ?_
  by_cases hk : k ≤ -(x : ℤ)
  · simp [hk, not_lt.2 hk]
  · simp [hk, lt_of_not_ge hk]

/-! ### The simple storage model -/

/-- The increment `S − J` of the storage model, for independent input `S ∼ H` and release
`J ∼ G` (MT p. 56): `P(S − J = x) = Σᵢ H(i) G(i − x)`. -/
theorem storage_increment_singleton (H G : Measure ℤ) [SFinite H] [SFinite G] (x : ℤ) :
    (H.prod G).map (fun p : ℤ × ℤ => p.1 - p.2) {x} = ∑' i, H {i} * G {i - x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have hset : (fun p : ℤ × ℤ => p.1 - p.2) ⁻¹' {x} = ⋃ i : ℤ, ({i} : Set ℤ) ×ˢ {i - x} := by
    ext ⟨a, b⟩
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_prod]
    constructor
    · intro h; exact ⟨a, rfl, by omega⟩
    · rintro ⟨i, rfl, rfl⟩; omega
  rw [hset, measure_iUnion (fun i j hij => by
      refine Set.disjoint_left.2 fun p hi hj => hij ?_
      simp only [mem_prod, mem_singleton_iff] at hi hj
      rw [← hi.1, ← hj.1]) (fun i => (measurableSet_singleton i).prod (measurableSet_singleton _))]
  exact tsum_congr fun i => Measure.prod_prod _ _

/-- **Correction** (MT p. 56): the book's `Γ(x) = Σᵢ H(i) G(x + i)` is not the increment law.
With `S = 0` and `J = 1` surely, `P(S − J = 1) = 0`, but the book's sum at `x = 1` is `1`. -/
theorem storage_increment_counterexample :
    ((Measure.dirac (0 : ℤ)).prod (Measure.dirac (1 : ℤ))).map (fun p : ℤ × ℤ => p.1 - p.2) {1} ≠
      ∑' i : ℕ, Measure.dirac (0 : ℤ) {(i : ℤ)} * Measure.dirac (1 : ℤ) {1 + (i : ℤ)} := by
  rw [storage_increment_singleton, tsum_eq_single 0 fun i hi => by
      simp [Measure.dirac_apply', show (i : ℤ) ≠ 0 by omega]]
  rw [tsum_eq_single 0 fun i hi => by
      simp only [Measure.dirac_apply' _ (measurableSet_singleton _), mem_singleton_iff,
        indicator_apply]
      simp [hi]]
  simp

/-! ### Embedded queueing models -/

/-- The mixed Poisson weights `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)` of (3.14)–(3.15) and (3.19): the
probability of `j` events of a rate-`μ` Poisson process in a time `T ∼ G`. -/
noncomputable def poissonWeight (G : Measure ℝ≥0) (μ : ℝ≥0) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ t, poissonMeasure (μ * t) {j} ∂G

/-- (3.14)–(3.15): `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)`. -/
theorem poissonWeight_eq (G : Measure ℝ≥0) (μ : ℝ≥0) (j : ℕ) :
    poissonWeight G μ j =
      ∫⁻ t, ENNReal.ofReal (exp (-((μ * t : ℝ≥0) : ℝ)) * ((μ * t : ℝ≥0) : ℝ) ^ j / j.factorial)
        ∂G := by
  simp_rw [poissonWeight, poissonMeasure_singleton]

/-- `Σⱼ pⱼ = 1`: the mixed Poisson weights form a probability on `ℤ₊`. -/
theorem tsum_poissonWeight (G : Measure ℝ≥0) [IsProbabilityMeasure G] (μ : ℝ≥0) :
    ∑' j, poissonWeight G μ j = 1 := by
  have hm : ∀ j, Measurable fun t : ℝ≥0 => poissonMeasure (μ * t) {j} := fun j => by
    simp_rw [poissonMeasure_singleton]
    fun_prop
  unfold poissonWeight
  rw [← lintegral_tsum fun j => (hm j).aemeasurable]
  have : ∀ t : ℝ≥0, ∑' j, poissonMeasure (μ * t) {j} = 1 := fun t => by
    have h := Measure.tsum_indicator_apply_singleton (poissonMeasure (μ * t)) univ
      MeasurableSet.univ
    simp only [indicator_univ] at h
    rw [h, measure_univ]
  simp [this]

/-- The GI/M/1 matrix of Proposition 3.3.1 (MT p. 56): `P(x, y) = p_{x+1−y}` for
`0 < y ≤ x + 1` and `P(x, 0) = q_x = Σ_{i ≥ x+1} pᵢ`. -/
noncomputable def giM1Matrix (p : ℕ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if y = 0 then ∑' i, p (i + x + 1) else if y ≤ x + 1 then p (x + 1 - y) else 0

/-- The increment law `Γ(k) = p_{1−k}` (`k ≤ 1`) of the GI/M/1 queue as a random walk. -/
noncomputable def giM1Increment (p : ℕ → ℝ≥0∞) (k : ℤ) : ℝ≥0∞ :=
  if k ≤ 1 then p (1 - k).toNat else 0

/-- The GI/M/1 matrix is the half-line random walk with increments `Γ(k) = p_{1−k}`
(MT p. 57, "hence `N` is a random walk on a half line"). -/
theorem giM1Matrix_eq_rwhl (p : ℕ → ℝ≥0∞) : giM1Matrix p = rwhlMatrix (giM1Increment p) := by
  funext x y
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp only [giM1Matrix, rwhlMatrix, ite_true]
    have hg : Function.Injective fun i : ℕ => -(x : ℤ) - i := fun a b h => by
      simp only at h; omega
    have hsupp : Function.support (fun k : ℤ =>
        if k ≤ -(x : ℤ) then giM1Increment p k else 0) ⊆ Set.range fun i : ℕ => -(x : ℤ) - i := by
      intro k hk
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hk
      obtain ⟨hk, -⟩ := hk
      exact ⟨(-(x : ℤ) - k).toNat, by simp only; omega⟩
    rw [← hg.tsum_eq hsupp]
    refine tsum_congr fun i => ?_
    simp only [show -(x : ℤ) - i ≤ -(x : ℤ) by omega, ite_true, giM1Increment,
      show -(x : ℤ) - i ≤ 1 by omega]
    congr 1
    omega
  · simp only [giM1Matrix, rwhlMatrix, Nat.pos_iff_ne_zero.1 hy, ite_false, giM1Increment]
    by_cases h : y ≤ x + 1
    · simp only [h, show ((y : ℤ) - x ≤ 1) by omega, ite_true]
      congr 1
      omega
    · simp only [h, show ¬((y : ℤ) - x ≤ 1) by omega, ite_false]

/-- The GI/M/1 increments sum to one when the `p_j` do. -/
theorem tsum_giM1Increment {p : ℕ → ℝ≥0∞} (hp : ∑' j, p j = 1) :
    ∑' k, giM1Increment p k = 1 := by
  have hg : Function.Injective fun j : ℕ => (1 : ℤ) - j := fun a b h => by
    simp only at h; omega
  have hsupp : Function.support (giM1Increment p) ⊆ Set.range fun j : ℕ => (1 : ℤ) - j := by
    intro k hk
    simp only [Function.mem_support, giM1Increment, ne_eq, ite_eq_right_iff, not_forall] at hk
    obtain ⟨hk, -⟩ := hk
    exact ⟨(1 - k).toNat, by simp only; omega⟩
  rw [← hg.tsum_eq hsupp, ← hp]
  refine tsum_congr fun j => ?_
  simp only [giM1Increment, show (1 : ℤ) - j ≤ 1 by omega, ite_true]
  congr 1
  omega

/-- **Proposition 3.3.1** (MT p. 56). For the GI/M/1 queue with service rate `μ` and
inter-arrival law `G`, the matrix with `p_j = ∫ e^{−μt}(μt)ʲ/j! G(dt)` and
`q_j = Σ_{i ≥ j+1} pᵢ` is a transition matrix on `ℤ₊` (so Theorem 3.2.1 builds the chain `N`),
and it is the random walk on a half line with increments `Γ(k) = p_{1−k}`. -/
theorem proposition_3_3_1 (G : Measure ℝ≥0) [IsProbabilityMeasure G] (μ : ℝ≥0) :
    IsTransitionMatrix (giM1Matrix (poissonWeight G μ)) ∧
      giM1Matrix (poissonWeight G μ) = rwhlMatrix (giM1Increment (poissonWeight G μ)) := by
  refine ⟨?_, giM1Matrix_eq_rwhl _⟩
  rw [giM1Matrix_eq_rwhl]
  exact isTransitionMatrix_rwhlMatrix (tsum_giM1Increment (tsum_poissonWeight G μ))

/-- The M/G/1 matrix of Proposition 3.3.2 (MT p. 57): row `0` is `(q₀, q₁, …)` and row `x ≥ 1`
is `P(x, y) = q_{y+1−x}` for `y ≥ x − 1`. -/
noncomputable def mG1Matrix (q : ℕ → ℝ≥0∞) (x y : ℕ) : ℝ≥0∞ :=
  if x = 0 then q y else if x ≤ y + 1 then q (y + 1 - x) else 0

/-- The M/G/1 matrix is a transition matrix when the `q_j` sum to one. -/
theorem isTransitionMatrix_mG1Matrix {q : ℕ → ℝ≥0∞} (hq : ∑' j, q j = 1) :
    IsTransitionMatrix (mG1Matrix q) := fun x => by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa [mG1Matrix] using hq
  · simp only [mG1Matrix, Nat.pos_iff_ne_zero.1 hx, ite_false]
    have hg : Function.Injective fun j : ℕ => j + x - 1 := fun a b h => by
      simp only at h; omega
    have hsupp : Function.support (fun y : ℕ => if x ≤ y + 1 then q (y + 1 - x) else 0) ⊆
        Set.range fun j : ℕ => j + x - 1 := by
      intro y hy
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hy
      obtain ⟨hy, -⟩ := hy
      exact ⟨y + 1 - x, by simp only; omega⟩
    rw [← hg.tsum_eq hsupp, ← hq]
    refine tsum_congr fun j => ?_
    simp only [show x ≤ j + x - 1 + 1 by omega, ite_true]
    congr 1
    omega

/-- **Proposition 3.3.2** (MT p. 57). For the M/G/1 queue with arrival rate `r` and service law
`H`, the matrix with `q_j = ∫ e^{−rt}(rt)ʲ/j! H(dt)` (3.19) is a transition matrix on `ℤ₊`, so
Theorem 3.2.1 builds the chain `N*`. -/
theorem proposition_3_3_2 (H : Measure ℝ≥0) [IsProbabilityMeasure H] (r : ℝ≥0) :
    IsTransitionMatrix (mG1Matrix (poissonWeight H r)) :=
  isTransitionMatrix_mG1Matrix (tsum_poissonWeight H r)

/-! ### Linear models on the rationals -/

/-- The AR(1) model on `ℚ` (MT p. 58): `P(r, q) = Γ(q − αr)`. -/
def arMatrix (α : ℚ) (Γ : ℚ → ℝ≥0∞) (r q : ℚ) : ℝ≥0∞ := Γ (q - α * r)

/-- **Proposition 3.3.3** (MT p. 58). For `α ∈ ℚ` and a noise law `ν` on `ℚ` with
`Γ(q) = ν{q}`, one step of `Xₙ₊₁ = αXₙ + Wₙ₊₁` from `r` lands on `q` with probability
`Γ(q − αr)`, and `P(r, q) = Γ(q − αr)` is a transition matrix on `ℚ` (so Theorem 3.2.1 builds the
chain). -/
theorem proposition_3_3_3 (α : ℚ) (ν : Measure ℚ) [IsProbabilityMeasure ν] :
    (∀ r q, (ν.map fun w => α * r + w) {q} = arMatrix α (fun q => ν {q}) r q) ∧
      IsTransitionMatrix (arMatrix α fun q => ν {q}) := by
  refine ⟨fun r q => ?_, fun r => ?_⟩
  · rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton q), arMatrix]
    congr 1
    ext w
    simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  · simp only [arMatrix]
    have h := Measure.tsum_indicator_apply_singleton ν univ MeasurableSet.univ
    simp only [indicator_univ] at h
    have he := (Equiv.subRight (α * r)).tsum_eq fun q => ν {q}
    simp only [Equiv.subRight_apply] at he
    rw [he, h, measure_univ]

end MeynTweedie.Irreducibility
