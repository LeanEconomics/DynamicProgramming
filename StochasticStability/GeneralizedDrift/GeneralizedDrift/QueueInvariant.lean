/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.CountableInvariant
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.IntermediateValue

/-!
# Invariant measures of the GI/M/1 queue (MT §10.3.3)

Meyn and Tweedie, §10.3.3, pp. 239–241. The number `N` in a GI/M/1 queue at arrival times is
the chain on `ℤ₊` with `P(i, j) = p(i + 1 − j)` for `1 ≤ j ≤ i + 1` and
`P(i, 0) = Σ_{k > i} p(k)`, where `p(k) = P(Z = 1 − k)` (`gim1Matrix`, `gim1Kernel`).

**Measures on `ℤ₊` given by their weights.**
* `pointMeasure m = Σₓ m(x) δₓ`, `pointMeasure_singleton`;
  `isInvariant_matKernel_pointMeasure_iff` and `isSubinvariant_matKernel_pointMeasure_iff`:
  invariance and subinvariance of `m` for a matrix kernel are the equations
  `Σᵢ m(i) P(i, j) = m(j)` (resp. `≤`).
* `tsum_split`: `Σₖ f(k) = Σ_{k < n} f(k) + Σₖ f(k + n)`.

**The geometric invariant measures.** For `s ≤ 1` put `g(s) = Σⱼ p(j) sʲ`.
* `gim1_col_succ`: `Σᵢ sⁱ P(i, j + 1) = sʲ g(s)`, the translation invariance behind (10.23);
  `gim1_col_zero`: `(1 − s) Σᵢ sⁱ P(i, 0) + g(s) = 1`, and `gim1_col_zero_one`:
  `Σᵢ P(i, 0) = Σⱼ j p(j)`.
* `isInvariant_gim1_geom` (10.24)–(10.25): if `s < 1` solves `s = g(s)` (10.25), then
  `μ(k) = sᵏ` is invariant; `isInvariant_gim1_one`: `μ ≡ 1` is invariant iff `Σⱼ j p(j) = 1`,
  and `isSubinvariant_gim1_one`: subinvariant iff `Σⱼ j p(j) ≤ 1`.
* `exists_gim1_root`: if `p(0) > 0` and `Σⱼ j p(j) > 1`, (10.25) has a root `s ∈ (0, 1)`.

**Proposition 10.3.2** (`proposition_10_3_2`, p. 241): for a `ψ`-irreducible GI/M/1 chain with
`p(0) > 0`, the chain is positive iff `Σⱼ j p(j) > 1`; `proposition_10_3_2_unique`: then every
subinvariant measure is a multiple of `μ(k) = sᵏ`, for the root `s ∈ (0, 1)` of (10.25).

**See also.** The identification of `s_α = μ°_α(1)` as the minimal root of (10.25) in `(0, 1]`,
`μ°_α(k) = s_αᵏ` (10.24), `s_α = 1` when `Σⱼ j p(j) ≤ 1`, and the recurrent case `Σⱼ j p(j) = 1`
(the unique invariant measure is `μ ≡ 1`) are in `QueueInvariantMinimal`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Measures on `ℤ₊` given by weights -/

/-- The measure `Σₓ m(x) δₓ` on a countable space. -/
noncomputable def pointMeasure {X : Type*} [MeasurableSpace X] (m : X → ℝ≥0∞) : Measure X :=
  Measure.sum fun x => m x • Measure.dirac x

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- `(Σₓ m(x) δₓ){y} = m(y)`. -/
theorem pointMeasure_singleton (m : X → ℝ≥0∞) (y : X) : pointMeasure m {y} = m y :=
  Measure.sum_smul_dirac_singleton

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
/-- `(μP){j} = Σᵢ m(i) P(i, j)` for `μ = Σ m(i) δᵢ` and a matrix kernel. -/
theorem matKernel_comp_pointMeasure_singleton (M : X → X → ℝ≥0∞) (m : X → ℝ≥0∞) (j : X) :
    (matKernel M ∘ₘ pointMeasure m) {j} = ∑' i, m i * M i j := by
  rw [measure_kernel_apply _ _ (measurableSet_singleton j), lintegral_countable']
  exact tsum_congr fun i => by rw [matKernel_singleton, pointMeasure_singleton, mul_comm]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
/-- Invariance of `Σ m(i) δᵢ` for a matrix kernel: `Σᵢ m(i) P(i, j) = m(j)` for every `j`. -/
theorem isInvariant_matKernel_pointMeasure_iff (M : X → X → ℝ≥0∞) (m : X → ℝ≥0∞) :
    IsInvariant (matKernel M) (pointMeasure m) ↔ ∀ j, ∑' i, m i * M i j = m j := by
  constructor
  · intro h j
    rw [← matKernel_comp_pointMeasure_singleton, h, pointMeasure_singleton]
  · intro h
    refine Measure.ext_of_singleton fun j => ?_
    rw [matKernel_comp_pointMeasure_singleton, pointMeasure_singleton, h]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
/-- Subinvariance of `Σ m(i) δᵢ` for a matrix kernel: `Σᵢ m(i) P(i, j) ≤ m(j)` for every `j`. -/
theorem isSubinvariant_matKernel_pointMeasure_iff (M : X → X → ℝ≥0∞) (m : X → ℝ≥0∞) :
    IsSubinvariant (matKernel M) (pointMeasure m) ↔ ∀ j, ∑' i, m i * M i j ≤ m j := by
  constructor
  · intro h j
    rw [← matKernel_comp_pointMeasure_singleton, ← pointMeasure_singleton m j]
    exact h _
  · intro h
    refine Measure.le_intro fun A hA _ => ?_
    rw [← Measure.tsum_indicator_apply_singleton _ A hA,
      ← Measure.tsum_indicator_apply_singleton (pointMeasure m) A hA]
    refine ENNReal.tsum_le_tsum fun j => ?_
    by_cases hj : j ∈ A
    · simp only [indicator_of_mem hj]
      rw [matKernel_comp_pointMeasure_singleton, pointMeasure_singleton]
      exact h j
    · simp [indicator_of_notMem hj]

variable {X : Type*} [MeasurableSpace X] in
/-- `(Σ m(x) δₓ)(X) = Σ m(x)`. -/
theorem pointMeasure_univ (m : X → ℝ≥0∞) : pointMeasure m univ = ∑' x, m x := by
  rw [pointMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp

/-- `Σₖ f(k) = Σ_{k < n} f(k) + Σₖ f(k + n)`. -/
theorem tsum_split (f : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑' k, f k = ∑ k ∈ Finset.range n, f k + ∑' k, f (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, add_assoc, tsum_eq_zero_add' ENNReal.summable]
    simp only [zero_add]
    congr 2
    exact tsum_congr fun k => by congr 1; omega

/-! ### The GI/M/1 chain -/

/-- The transition matrix of the number in a GI/M/1 queue (MT p. 239):
`P(i, j) = p(i + 1 − j)` for `1 ≤ j ≤ i + 1` and `P(i, 0) = Σ_{k > i} p(k)`. -/
noncomputable def gim1Matrix (p : ℕ → ℝ≥0∞) (i j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ∑' k, (Ioi i).indicator p k else if j ≤ i + 1 then p (i + 1 - j) else 0

/-- `Σ_{k > i} p(k) = Σₖ p(k + i + 1)`. -/
theorem tsum_indicator_Ioi (p : ℕ → ℝ≥0∞) (i : ℕ) :
    ∑' k, (Ioi i).indicator p k = ∑' k, p (k + (i + 1)) := by
  rw [tsum_split _ (i + 1), Finset.sum_eq_zero (fun k hk => indicator_of_notMem
    (by simp only [Finset.mem_range] at hk; simp only [mem_Ioi, not_lt]; omega) _), zero_add]
  exact tsum_congr fun k => indicator_of_mem (by simp only [mem_Ioi]; omega) _

/-- The rows of the GI/M/1 matrix sum to one when `p` is a probability. -/
theorem isTransitionMatrix_gim1 {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) :
    IsTransitionMatrix (gim1Matrix p) := by
  intro i
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [gim1Matrix, ite_true, Nat.succ_ne_zero, ite_false]
  have h1 : (∑' b : ℕ, if b + 1 ≤ i + 1 then p (i + 1 - (b + 1)) else 0) =
      ∑ j ∈ Finset.range (i + 1), p j := by
    rw [tsum_eq_sum (s := Finset.range (i + 1)) (fun b hb => by
      simp only [Finset.mem_range, not_lt] at hb
      simp [show ¬ (b + 1 ≤ i + 1) by omega])]
    rw [← Finset.sum_range_reflect p (i + 1)]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_range] at hb
    simp only [show b + 1 ≤ i + 1 by omega, ite_true]
    congr 1
    omega
  rw [h1, tsum_indicator_Ioi, add_comm, ← tsum_split p (i + 1), hp]

/-- The GI/M/1 chain. -/
noncomputable abbrev gim1Kernel (p : ℕ → ℝ≥0∞) : Kernel ℕ ℕ := matKernel (gim1Matrix p)

/-- The generating function `g(s) = Σⱼ p(j) sʲ`. -/
noncomputable def gim1Gen (p : ℕ → ℝ≥0∞) (s : ℝ≥0∞) : ℝ≥0∞ := ∑' j, p j * s ^ j

/-- Translation invariance (10.23): `Σᵢ sⁱ P(i, j + 1) = sʲ g(s)`. -/
theorem gim1_col_succ (p : ℕ → ℝ≥0∞) (s : ℝ≥0∞) (j : ℕ) :
    ∑' i, s ^ i * gim1Matrix p i (j + 1) = s ^ j * gim1Gen p s := by
  simp only [gim1Matrix, Nat.succ_ne_zero, ite_false]
  rw [tsum_split _ j, Finset.sum_eq_zero (fun i hi => by
    simp only [Finset.mem_range] at hi
    simp [show ¬ (j + 1 ≤ i + 1) by omega]), zero_add, gim1Gen, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [show j + 1 ≤ m + j + 1 by omega, ite_true, show m + j + 1 - (j + 1) = m by omega,
    pow_add]
  ring

/-- `(1 − s) Σ_{i < k} sⁱ + sᵏ = 1` for `s ≤ 1`. -/
theorem one_sub_mul_geom_add {s : ℝ≥0∞} (hs : s ≤ 1) (k : ℕ) :
    (1 - s) * ∑ i ∈ Finset.range k, s ^ i + s ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc (1 - s) * (∑ i ∈ Finset.range k, s ^ i + s ^ k) + s ^ (k + 1)
        = (1 - s) * ∑ i ∈ Finset.range k, s ^ i + s ^ k * ((1 - s) + s) := by ring
      _ = (1 - s) * ∑ i ∈ Finset.range k, s ^ i + s ^ k := by
          rw [tsub_add_cancel_of_le hs, mul_one]
      _ = 1 := ih

/-- `Σᵢ sⁱ P(i, 0) = Σₖ p(k) Σ_{i < k} sⁱ`. -/
theorem gim1_col_zero_eq (p : ℕ → ℝ≥0∞) (s : ℝ≥0∞) :
    ∑' i, s ^ i * gim1Matrix p i 0 = ∑' k, p k * ∑ i ∈ Finset.range k, s ^ i := by
  simp only [gim1Matrix, ite_true]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_sum (s := Finset.range k) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    simp [indicator_of_notMem (show k ∉ Ioi i by simp only [mem_Ioi, not_lt]; omega)]),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [indicator_of_mem (show k ∈ Ioi i from hi), mul_comm]

/-- The column `0` (proof of (10.25)): `(1 − s) Σᵢ sⁱ P(i, 0) + g(s) = 1` for `s ≤ 1`. -/
theorem gim1_col_zero {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {s : ℝ≥0∞} (hs : s ≤ 1) :
    (1 - s) * ∑' i, s ^ i * gim1Matrix p i 0 + gim1Gen p s = 1 := by
  rw [gim1_col_zero_eq, gim1Gen, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  conv_rhs => rw [← hp]
  refine tsum_congr fun k => ?_
  calc (1 - s) * (p k * ∑ i ∈ Finset.range k, s ^ i) + p k * s ^ k
      = p k * ((1 - s) * ∑ i ∈ Finset.range k, s ^ i + s ^ k) := by ring
    _ = p k := by rw [one_sub_mul_geom_add hs, mul_one]

/-- At `s = 1`: `Σᵢ P(i, 0) = Σⱼ j p(j)`. -/
theorem gim1_col_zero_one (p : ℕ → ℝ≥0∞) :
    ∑' i, gim1Matrix p i 0 = ∑' j : ℕ, (j : ℝ≥0∞) * p j := by
  have := gim1_col_zero_eq p 1
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  rw [this]
  exact tsum_congr fun j => mul_comm _ _

/-- (10.24)–(10.25): if `s < 1` and `s = g(s)`, then `μ(k) = sᵏ` is invariant for the GI/M/1
chain. -/
theorem isInvariant_gim1_geom {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {s : ℝ≥0∞} (hs : s < 1)
    (hroot : gim1Gen p s = s) : IsInvariant (gim1Kernel p) (pointMeasure fun k => s ^ k) := by
  rw [gim1Kernel, isInvariant_matKernel_pointMeasure_iff]
  intro j
  cases j with
  | zero =>
    have h := gim1_col_zero hp hs.le
    rw [hroot] at h
    have h1 : (1 - s) * ∑' i, s ^ i * gim1Matrix p i 0 + s = (1 - s) * 1 + s := by
      rw [h, mul_one, tsub_add_cancel_of_le hs.le]
    have hsne : s ≠ ∞ := (hs.trans ENNReal.one_lt_top).ne
    have h2 := (ENNReal.add_left_inj hsne).1 h1
    rw [ENNReal.mul_right_inj (tsub_pos_of_lt hs).ne' (ENNReal.sub_ne_top ENNReal.one_ne_top)]
      at h2
    rw [h2, pow_zero]
  | succ j => rw [gim1_col_succ, hroot, pow_succ]

/-- At `s = 1`: `μ ≡ 1` is invariant iff `Σⱼ j p(j) = 1`. -/
theorem isInvariant_gim1_one {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) :
    IsInvariant (gim1Kernel p) (pointMeasure fun _ => 1) ↔ ∑' j : ℕ, (j : ℝ≥0∞) * p j = 1 := by
  rw [gim1Kernel, isInvariant_matKernel_pointMeasure_iff]
  have hg : gim1Gen p 1 = 1 := by simp [gim1Gen, hp]
  constructor
  · intro h
    have := h 0
    simp only [one_mul] at this
    rwa [gim1_col_zero_one] at this
  · intro h j
    cases j with
    | zero => simp only [one_mul]; rw [gim1_col_zero_one, h]
    | succ j =>
      have := gim1_col_succ p 1 j
      simp only [one_pow, one_mul] at this
      simp only [one_mul]
      rw [this, hg]

/-- At `s = 1`: `μ ≡ 1` is subinvariant iff `Σⱼ j p(j) ≤ 1`. -/
theorem isSubinvariant_gim1_one {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) :
    IsSubinvariant (gim1Kernel p) (pointMeasure fun _ => 1) ↔ ∑' j : ℕ, (j : ℝ≥0∞) * p j ≤ 1 := by
  rw [gim1Kernel, isSubinvariant_matKernel_pointMeasure_iff]
  have hg : gim1Gen p 1 = 1 := by simp [gim1Gen, hp]
  constructor
  · intro h
    have := h 0
    simp only [one_mul] at this
    rwa [gim1_col_zero_one] at this
  · intro h j
    cases j with
    | zero => simp only [one_mul]; rw [gim1_col_zero_one]; exact h
    | succ j =>
      have := gim1_col_succ p 1 j
      simp only [one_pow, one_mul] at this
      simp only [one_mul]
      rw [this, hg]

/-! ### The root of (10.25) -/

/-- If `p(0) > 0` and `Σⱼ j p(j) > 1`, the equation `s = g(s)` (10.25) has a root `s ∈ (0, 1)`. -/
theorem exists_gim1_root {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) (hp0 : 0 < p 0)
    (hmean : 1 < ∑' j : ℕ, (j : ℝ≥0∞) * p j) : ∃ s : ℝ≥0∞, 0 < s ∧ s < 1 ∧ gim1Gen p s = s := by
  have hpfin : ∀ j, p j ≠ ∞ := fun j =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hp ▸ ENNReal.le_tsum j)
  have hsum : Summable fun j => (p j).toReal :=
    ENNReal.summable_toReal (by rw [hp]; exact ENNReal.one_ne_top)
  have hsum1 : ∑' j, (p j).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hpfin, hp, ENNReal.toReal_one]
  -- the real generating function
  set g : ℝ → ℝ := fun s => ∑' j, (p j).toReal * s ^ j with hg
  have hsumg : ∀ s ∈ Icc (0 : ℝ) 1, Summable fun j => (p j).toReal * s ^ j := fun s hs =>
    hsum.of_nonneg_of_le (fun j => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs.1 _))
      fun j => mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs.1 hs.2)
  have hcont : ContinuousOn g (Icc 0 1) := by
    refine continuousOn_tsum (u := fun j => (p j).toReal)
      (fun j => (continuous_const.mul (continuous_pow j)).continuousOn) hsum fun j s hs => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs.1 _))]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs.1 hs.2)
  -- a finite part of the mean exceeds one
  obtain ⟨K, hK⟩ : ∃ K, 1 < ∑ j ∈ Finset.range K, (j : ℝ≥0∞) * p j := by
    rw [ENNReal.tsum_eq_iSup_nat] at hmean
    exact lt_iSup_iff.1 hmean
  set Mr : ℝ := ∑ j ∈ Finset.range K, (j : ℝ) * (p j).toReal with hMr
  have hMr1 : 1 < Mr := by
    have hfin : ∑ j ∈ Finset.range K, (j : ℝ≥0∞) * p j ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (by simp) (hpfin j)
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hfin).2 hK
    rw [ENNReal.toReal_one, ENNReal.toReal_sum fun j _ =>
      ENNReal.mul_ne_top (by simp) (hpfin j)] at this
    simpa [ENNReal.toReal_mul] using this
  -- a point `s₀ < 1` with `s₀ᴷ Mr > 1`
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, 1 < s0 ^ K * Mr ∧ s0 ∈ Ioo (0 : ℝ) 1 := by
    have ht : Tendsto (fun s : ℝ => s ^ K * Mr) (𝓝[<] 1) (𝓝 (1 ^ K * Mr)) :=
      (((continuous_pow K).mul continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
    rw [one_pow, one_mul] at ht
    exact ((ht.eventually (lt_mem_nhds hMr1)).and (Ioo_mem_nhdsLT zero_lt_one)).exists
  obtain ⟨hs0M, hs0pos, hs01⟩ := hs0
  have hs0I : s0 ∈ Icc (0 : ℝ) 1 := ⟨hs0pos.le, hs01.le⟩
  -- `g(s₀) < s₀`
  have hgs0 : g s0 < s0 := by
    have e1 : 1 - g s0 = ∑' j, (p j).toReal * (1 - s0 ^ j) := by
      conv_lhs => rw [← hsum1]
      rw [hg]
      simp only
      rw [← (hsum).tsum_sub (hsumg s0 hs0I)]
      exact tsum_congr fun j => by ring
    have hnn : ∀ j, 0 ≤ (p j).toReal * (1 - s0 ^ j) := fun j =>
      mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 (pow_le_one₀ hs0pos.le hs01.le))
    have hsumd : Summable fun j => (p j).toReal * (1 - s0 ^ j) :=
      hsum.of_nonneg_of_le hnn fun j => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (by linarith [pow_nonneg hs0pos.le j])
    have e2 : ∑ j ∈ Finset.range K, (p j).toReal * (1 - s0 ^ j) ≤ 1 - g s0 := by
      rw [e1]; exact hsumd.sum_le_tsum _ fun j _ => hnn j
    have e3 : (1 - s0) * (s0 ^ K * Mr) ≤ ∑ j ∈ Finset.range K, (p j).toReal * (1 - s0 ^ j) := by
      rw [hMr, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [← mul_neg_geom_sum]
      have hgeo : (j : ℝ) * s0 ^ K ≤ ∑ i ∈ Finset.range j, s0 ^ i := by
        calc (j : ℝ) * s0 ^ K = ∑ _i ∈ Finset.range j, s0 ^ K := by simp
          _ ≤ ∑ i ∈ Finset.range j, s0 ^ i := Finset.sum_le_sum fun i hi => by
              simp only [Finset.mem_range] at hi
              exact pow_le_pow_of_le_one hs0pos.le hs01.le (by omega)
      have h1s : 0 ≤ 1 - s0 := by linarith
      calc (1 - s0) * (s0 ^ K * ((j : ℝ) * (p j).toReal))
          = (p j).toReal * ((1 - s0) * ((j : ℝ) * s0 ^ K)) := by ring
        _ ≤ (p j).toReal * ((1 - s0) * ∑ i ∈ Finset.range j, s0 ^ i) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo h1s) ENNReal.toReal_nonneg
    have h1s : 0 < 1 - s0 := by linarith
    nlinarith
  -- the intermediate value theorem on `[0, s₀]`
  have hcont0 : ContinuousOn (fun s => g s - s) (Icc 0 s0) :=
    ((hcont.mono (Icc_subset_Icc le_rfl hs01.le)).sub continuousOn_id)
  have hg0 : g 0 = (p 0).toReal := by
    rw [hg]
    simp only
    rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
    simp
  have hp0r : 0 < (p 0).toReal := ENNReal.toReal_pos hp0.ne' (hpfin 0)
  obtain ⟨s, hsI, hs⟩ := intermediate_value_Icc' hs0pos.le hcont0
    ⟨show g s0 - s0 ≤ 0 by linarith, show (0 : ℝ) ≤ g 0 - 0 by rw [hg0]; linarith⟩
  have hs' : g s - s = 0 := hs
  have hs0' : s ≠ 0 := by
    rintro rfl
    rw [hg0] at hs'
    linarith
  have hspos : 0 < s := lt_of_le_of_ne hsI.1 (Ne.symm hs0')
  have hs1 : s < 1 := lt_of_le_of_lt hsI.2 hs01
  have hroot : g s = s := by linarith
  refine ⟨ENNReal.ofReal s, ENNReal.ofReal_pos.2 hspos,
    (ENNReal.ofReal_lt_one).2 hs1, ?_⟩
  rw [gim1Gen]
  conv_rhs => rw [← hroot]
  change _ = ENNReal.ofReal (∑' j, (p j).toReal * s ^ j)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg
    (pow_nonneg hspos.le _)) (hsumg s ⟨hspos.le, hs1.le⟩)]
  refine tsum_congr fun j => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hpfin j),
    ENNReal.ofReal_pow hspos.le]

/-! ### Proposition 10.3.2 -/

/-- **Proposition 10.3.2** (MT p. 241): a `ψ`-irreducible GI/M/1 chain with `p(0) > 0` is
positive iff `Σⱼ j p(j) > 1`. -/
theorem proposition_10_3_2 {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) (hp0 : 0 < p 0)
    {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp);
      IsMaximalIrreducibility (gim1Kernel p) ψ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp)
    IsPositive (gim1Kernel p) ψ ↔ 1 < ∑' j : ℕ, (j : ℝ≥0∞) * p j := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp)
  constructor
  · intro hpos
    by_contra hle
    rw [not_lt] at hle
    have hsub : IsSubinvariantMeasure (gim1Kernel p) (pointMeasure fun _ => 1) :=
      ⟨sigmaFinite_of_singleton_ne_top fun j => by
        rw [pointMeasure_singleton]; exact ENNReal.one_ne_top,
        (isSubinvariant_gim1_one hp).2 hle⟩
    obtain ⟨c, hc, he⟩ := hpos.eq_smul_stationaryDist hsub
    have := isProbabilityMeasure_stationaryDist hpos
    have hu := congrArg (fun m : Measure ℕ => m univ) he
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, pointMeasure_univ] at hu
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at hu
    exact hc hu.symm
  · intro hmean
    obtain ⟨s, -, hs1, hroot⟩ := exists_gim1_root hp hp0 hmean
    have hinv := isInvariant_gim1_geom hp hs1 hroot
    set μ := pointMeasure fun k => s ^ k
    have hμu : μ univ = (1 - s)⁻¹ := by rw [pointMeasure_univ, ENNReal.tsum_geometric]
    have hμfin : μ univ ≠ ∞ := by
      rw [hμu]; exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hs1).ne'
    have hμ0 : μ univ ≠ 0 := by rw [hμu]; simp
    refine ⟨hψ, (μ univ)⁻¹ • μ, ⟨?_⟩, hinv.smul _⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ0 hμfin]

/-- Proposition 10.3.2, uniqueness (MT p. 241): for a positive GI/M/1 chain, with `s ∈ (0, 1)`
a root of (10.25), every subinvariant measure is a finite multiple of `μ(k) = sᵏ`. -/
theorem proposition_10_3_2_unique {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {ψ : Measure ℕ}
    (hpos : haveI := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp);
      IsPositive (gim1Kernel p) ψ)
    {s : ℝ≥0∞} (hs1 : s < 1) (hroot : gim1Gen p s = s) {μ : Measure ℕ}
    (hμ : IsSubinvariantMeasure (gim1Kernel p) μ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • pointMeasure fun k => s ^ k := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp)
  have hrec := proposition_10_1_1 hpos
  have hinv := isInvariant_gim1_geom hp hs1 hroot
  have hne : pointMeasure (fun k => s ^ k) ≠ 0 := by
    intro h
    have := pointMeasure_singleton (fun k => s ^ k) 0
    rw [h] at this
    simp at this
  refine hrec.exists_eq_smul hμ ⟨sigmaFinite_of_singleton_ne_top fun j => ?_,
    hinv.isSubinvariant⟩ hne
  rw [pointMeasure_singleton]
  exact ENNReal.pow_ne_top (hs1.trans ENNReal.one_lt_top).ne

end MeynTweedie.GeneralizedDrift
