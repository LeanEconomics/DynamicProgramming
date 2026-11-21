/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# The firm-size distribution (AKMM §22.8, p. 692, and App. 22.A.6)

* **A Pareto stationary density** (p. 692): `h(n) = Fn^{−(ζ+1)}` satisfies
  `(1+g)h((1+g)n) = (1−δ)h(n)` for all `n > 0` iff `ζ = −log(1−δ)/log(1+g)` (`pareto_stationary`);
  then `ζ > 0` (`pareto_zeta_pos`), and the tail is thicker when `δ` is smaller or `g` larger
  (`pareto_zeta_mono`).
* **The transition of firm sizes** (App. 22.A.6, p. 896): from `j` lines a firm loses
  `Bin(j, μ)` lines and gains `Bin(j, η)`; `fsdT μ η j k` is the probability of ending with `k`
  lines (`fsd_T_sum` : the probabilities sum to one). The three groups of the book's equation
  for `M_{k,t+1}` are `fsdT (k−h) k`, `fsdT k k` and `fsdT (k+h) k`: we prove the book's sums for
  the second and third (`fsd_stay`, `fsd_from_above`) and the first with the **corrected inner
  bound** `i = 0, …, k − 2h` (`fsd_from_below`), and that sources with `2h > k` cannot reach `k`
  (`fsd_below_zero`), which justifies the outer bound `⌊k/2⌋`. The printed inner bound
  `⌊k/2 − h⌋` omits terms: for `k = 4`, `h = 1` it misses `P_μ(3,2)P_η(3,3) > 0`
  (`fsd_printed_bound_false`).
-/

namespace AKMM.HeterogeneousFirms

/-! ### The Pareto tail -/

/-- AKMM, p. 692: **a Pareto stationary density**. For `F > 0`, `g > 0`, `0 < δ < 1`, the density
`h(n) = Fn^{−(ζ+1)}` satisfies `(1+g)h((1+g)n) = (1−δ)h(n)` for every `n > 0` iff
`ζ = −log(1−δ)/log(1+g)`. -/
theorem pareto_stationary {F g δ ζ : ℝ} (hF : 0 < F) (hg : 0 < g) (hδ1 : δ < 1) :
    (∀ n : ℝ, 0 < n → (1 + g) * (F * ((1 + g) * n) ^ (-(ζ + 1))) =
      (1 - δ) * (F * n ^ (-(ζ + 1)))) ↔ ζ = -Real.log (1 - δ) / Real.log (1 + g) := by
  have h1g : 0 < 1 + g := by linarith
  have hlg : 0 < Real.log (1 + g) := Real.log_pos (by linarith)
  have h1d : 0 < 1 - δ := by linarith
  have key : ∀ n : ℝ, 0 < n → (1 + g) * (F * ((1 + g) * n) ^ (-(ζ + 1))) =
      (1 + g) ^ (-ζ) * (F * n ^ (-(ζ + 1))) := fun n hn => by
    rw [Real.mul_rpow h1g.le hn.le]
    have : (1 + g) * (1 + g) ^ (-(ζ + 1)) = (1 + g) ^ (-ζ) := by
      rw [show (1 + g) * (1 + g) ^ (-(ζ + 1)) = (1 + g) ^ (1 + -(ζ + 1)) by
        rw [Real.rpow_add h1g, Real.rpow_one]]
      ring_nf
    calc (1 + g) * (F * ((1 + g) ^ (-(ζ + 1)) * n ^ (-(ζ + 1))))
        = ((1 + g) * (1 + g) ^ (-(ζ + 1))) * (F * n ^ (-(ζ + 1))) := by ring
      _ = _ := by rw [this]
  have hlog : (1 + g) ^ (-ζ) = 1 - δ ↔ Real.log (1 + g) * (-ζ) = Real.log (1 - δ) := by
    rw [Real.rpow_def_of_pos h1g]
    constructor
    · intro h; rw [← h, Real.log_exp]
    · intro h; rw [h, Real.exp_log h1d]
  have hiff : (1 + g) ^ (-ζ) = 1 - δ ↔ ζ = -Real.log (1 - δ) / Real.log (1 + g) := by
    rw [hlog, eq_div_iff hlg.ne']
    constructor <;> intro h <;> linarith
  rw [← hiff]
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [key 1 one_pos] at h1
    have hpos : 0 < F * (1 : ℝ) ^ (-(ζ + 1)) := by rw [Real.one_rpow]; linarith
    exact mul_right_cancel₀ hpos.ne' h1
  · intro h n hn
    rw [key n hn, h]

/-- AKMM, p. 692: `ζ = −log(1−δ)/log(1+g) > 0`. -/
theorem pareto_zeta_pos {g δ : ℝ} (hg : 0 < g) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < -Real.log (1 - δ) / Real.log (1 + g) := by
  have hlg : 0 < Real.log (1 + g) := Real.log_pos (by linarith)
  have hld : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
  exact div_pos (by linarith) hlg

/-- AKMM, p. 692: **the tail is thick when `δ` is small or `g` large**: `ζ` is increasing in `δ`
and decreasing in `g`. -/
theorem pareto_zeta_mono {g g' δ δ' : ℝ} (hg : 0 < g) (hgg : g ≤ g') (hδ : 0 < δ) (hδδ : δ ≤ δ')
    (hδ1 : δ' < 1) :
    -Real.log (1 - δ) / Real.log (1 + g') ≤ -Real.log (1 - δ) / Real.log (1 + g) ∧
      -Real.log (1 - δ) / Real.log (1 + g) ≤ -Real.log (1 - δ') / Real.log (1 + g) := by
  have hlg : 0 < Real.log (1 + g) := Real.log_pos (by linarith)
  have hlg' : Real.log (1 + g) ≤ Real.log (1 + g') := Real.log_le_log (by linarith) (by linarith)
  have hld : 0 ≤ -Real.log (1 - δ) := by
    have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith); linarith
  have hld' : -Real.log (1 - δ) ≤ -Real.log (1 - δ') := by
    have := Real.log_le_log (by linarith : (0 : ℝ) < 1 - δ') (by linarith : 1 - δ' ≤ 1 - δ)
    linarith
  exact ⟨div_le_div_of_nonneg_left hld hlg hlg', div_le_div_of_nonneg_right hld' hlg.le⟩

/-! ### Transitions of product lines -/

/-- AKMM, p. 896: the binomial probability `P_p(a, b) = C(a,b)p^b(1−p)^{a−b}`. -/
noncomputable def binomP (p : ℝ) (a b : ℕ) : ℝ := (a.choose b : ℝ) * p ^ b * (1 - p) ^ (a - b)

theorem binomP_eq_zero {p : ℝ} {a b : ℕ} (h : a < b) : binomP p a b = 0 := by
  simp [binomP, Nat.choose_eq_zero_of_lt h]

theorem binomP_sum (p : ℝ) (a : ℕ) : ∑ b ∈ Finset.range (a + 1), binomP p a b = 1 := by
  have h := add_pow p (1 - p) a
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun b _ => by unfold binomP; ring

/-- AKMM, App. 22.A.6: the probability that a firm with `j` lines has `k` lines next period: it
loses `ℓ ∼ Bin(j, μ)` and gains `g ∼ Bin(j, η)` lines, independently, and `k = j − ℓ + g`. -/
noncomputable def fsdT (μ η : ℝ) (j k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), ∑ g ∈ Finset.range (j + 1),
    if j - l + g = k then binomP μ j l * binomP η j g else 0

/-- The transition probabilities from `j` lines sum to one. -/
theorem fsd_T_sum (μ η : ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (2 * j + 1), fsdT μ η j k = 1 := by
  unfold fsdT
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (2 * j + 1), ∑ g ∈ Finset.range (j + 1),
      (if j - l + g = k then binomP μ j l * binomP η j g else 0) =
      binomP μ j l * ∑ g ∈ Finset.range (j + 1), binomP η j g := fun l hl => by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range] at hl hg ⊢
    rw [ite_eq_left (by omega)]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, binomP_sum, binomP_sum, one_mul]

/-- The single-sum form: `fsdT j k = Σ_ℓ [j ≤ k + ℓ] P_μ(j, ℓ)P_η(j, k + ℓ − j)`. -/
theorem fsd_T_eq (μ η : ℝ) (j k : ℕ) :
    fsdT μ η j k = ∑ l ∈ Finset.range (j + 1),
      if j ≤ k + l then binomP μ j l * binomP η j (k + l - j) else 0 := by
  unfold fsdT
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_range] at hl
  by_cases hjk : j ≤ k + l
  · rw [ite_eq_left hjk]
    by_cases hg : k + l - j < j + 1
    · rw [Finset.sum_eq_single (k + l - j)]
      · rw [ite_eq_left (by omega)]
      · intro g _ hne; rw [ite_eq_right (by omega)]
      · intro h; exact absurd (Finset.mem_range.mpr hg) h
    · rw [binomP_eq_zero (by omega : j < k + l - j), mul_zero]
      exact Finset.sum_eq_zero fun g hg' => by
        simp only [Finset.mem_range] at hg'; rw [ite_eq_right (by omega)]
  · rw [ite_eq_right hjk]
    exact Finset.sum_eq_zero fun g _ => by rw [ite_eq_right (by omega)]

/-- AKMM, App. 22.A.6, p. 896: **firms that keep `k` lines**:
`fsdT k k = Σ_{i=0}^k P_μ(k,i)P_η(k,i)` (the book's middle term). -/
theorem fsd_stay (μ η : ℝ) (k : ℕ) :
    fsdT μ η k k = ∑ i ∈ Finset.range (k + 1), binomP μ k i * binomP η k i := by
  rw [fsd_T_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ite_eq_left (by omega), show k + i - k = i by omega]

/-- AKMM, App. 22.A.6, p. 896: **firms shrinking from `k + h` to `k` lines**:
`fsdT (k+h) k = Σ_{i=h}^{k+h} P_μ(k+h, i)P_η(k+h, i−h)` (the book's last term). -/
theorem fsd_from_above (μ η : ℝ) (k h : ℕ) :
    fsdT μ η (k + h) k = ∑ i ∈ Finset.Ico h (k + h + 1),
      binomP μ (k + h) i * binomP η (k + h) (i - h) := by
  rw [fsd_T_eq, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le h) (by omega : h ≤ k + h + 1)]
  rw [Finset.sum_eq_zero (fun i hi => by
    simp only [Finset.mem_Ico] at hi; rw [ite_eq_right (by omega)]), zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  rw [ite_eq_left (by omega), show k + i - (k + h) = i - h by omega]

/-- AKMM, App. 22.A.6, p. 896, **corrected**: **firms growing from `k − h` to `k` lines**, for
`1 ≤ h` and `2h ≤ k`: `fsdT (k−h) k = Σ_{i=0}^{k−2h} P_μ(k−h, i)P_η(k−h, i+h)` — lose `i`, gain
`i + h ≤ k − h`; the book prints the bound `⌊k/2 − h⌋`. -/
theorem fsd_from_below (μ η : ℝ) {k h : ℕ} (h2 : 2 * h ≤ k) :
    fsdT μ η (k - h) k = ∑ i ∈ Finset.range (k - 2 * h + 1),
      binomP μ (k - h) i * binomP η (k - h) (i + h) := by
  rw [fsd_T_eq]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega :
    k - 2 * h + 1 ≤ k - h + 1))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [ite_eq_left (by omega), show k + i - (k - h) = i + h by omega]
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    rw [ite_eq_left (by omega), show k + i - (k - h) = i + h by omega,
      binomP_eq_zero (by omega : k - h < i + h), mul_zero]

/-- AKMM, App. 22.A.6, p. 896: a firm with `k − h` lines cannot reach `k` lines when `2h > k`
(it gains at most `k − h < h` lines), which justifies the outer bound `⌊k/2⌋`. -/
theorem fsd_below_zero (μ η : ℝ) {k h : ℕ} (hk : k < 2 * h) (hhk : h ≤ k) :
    fsdT μ η (k - h) k = 0 := by
  rw [fsd_T_eq]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [ite_eq_left (by omega), binomP_eq_zero (by omega : k - h < k + i - (k - h)), mul_zero]

/-- AKMM, App. 22.A.6, p. 896: **the printed inner bound is wrong**. For `k = 4`, `h = 1` the
printed sum runs over `i = 0, …, ⌊4/2 − 1⌋ = 1`, but the transition probability from 3 to 4
lines also contains `i = 2` (lose 2, gain 3), `P_μ(3,2)P_η(3,3) = 3μ²(1−μ)η³ > 0`. -/
theorem fsd_printed_bound_false {μ η : ℝ} (hμ : 0 < μ) (hμ1 : μ < 1) (hη : 0 < η) :
    ∑ i ∈ Finset.range (4 / 2 - 1 + 1), binomP μ 3 i * binomP η 3 (i + 1) <
      fsdT μ η (4 - 1) 4 := by
  rw [fsd_from_below μ η (by norm_num : 2 * 1 ≤ 4)]
  norm_num [Finset.sum_range_succ, binomP]
  have : 0 < 1 - μ := by linarith
  positivity

end AKMM.HeterogeneousFirms
