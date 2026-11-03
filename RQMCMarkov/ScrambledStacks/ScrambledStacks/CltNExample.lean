/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNOwen

/-!
# Non-vacuity of the n-state stacks CLT: uniform chains (post #3)

The CLTs `tendstoInDistribution_occErrN_shift` (code (ii)) and
`tendstoInDistribution_occErrN_owen` (code (iii)) assume `Var ≥ κ log T` along the given times.
This module proves that hypothesis, for BOTH randomisations, on the uniform chains
`P i j = 1/n` with `n` not a power of two (in particular `n = 3`, the REQUIRED example, and
`n = 5`, the number of states of post #3), and every target `s`. Every row has `n − 1` cut points
`j/n` in play, so Owen's tree of paths matters (two cut points share the flips of their common
binary prefix only).

* Poisson data: `H t = 1_{t} − 1/n`, `π = 1/n` (`isPoissonFamily_uniform`). The weights are
  `h_j − h_{j+1} = 1{j = s} − 1{j+1 = s} ∈ {−1, 0, 1}`, total `W ≤ 2`.
* Times `T_k = n Σ_{a<k} 2^{ra}` with spacing `r = 2n + 6` (`uniformTime`), so that
  `⌊T_k π_i⌋ = Σ_{a<k} 2^{ra}` in every row (`chainIdxN_uniformTime`).
* Per level, a row term is an integer minus `θ`, where `θ ≡ 2^m/n (mod 1)` (`rowFrac_uniform`),
  whose fractional part is `(2^m mod n)/n ∈ [1/n, 1 − 1/n]` as `n ∤ 2^m`; the integer variance
  bound gives `Var ≥ (n − 1)/n²` under ANY randomisation (`variance_rowTerm_uniform_ge`); for
  `n = 3` this is the value `2/9` of the brief.
* Rows are independent and levels at distance `d` have covariance `≤ 2W² 2^{-d}`; the spacing makes
  the diagonal dominate: `Var(main term) ≥ k/4` (`variance_levelSumN_uniform_ge`), and then
  `Var(N_s(T_k) − T_k/n) ≥ log₂ T_k / (16 (n + r))` eventually
  (`eventually_variance_occErrN_uniform_shift_ge`, `_owen_ge`).

The values are consistent with simulation (`3·10³` replications, `400` for `k = 3`; spacing `8`
rather than the proof's `2n + 6`): for three states the
per-row variance at `k = 1, 2, 3` levels is `0.22, 0.42, 0.73` (shift) and `0.23, 0.66, 1.02`
(Owen), against the bound `(n − 1)/n² = 2/9` per level; for five states `0.16, 0.32, 0.50` (shift)
and `0.17, 0.66, 1.04` (Owen), against `4/25`. The two randomisations have different variances
(Owen's larger here); only the common lower bound is proved.

**Correction / scope.** For `n` a power of two the cut points are dyadic and there is no CLT at
all (`StackDyadic`); here `n ∤ 2^m` is assumed. Post #3's five-state Farmer–Toda probabilities are
not dyadic-checkable numbers, so the five-state instance is the uniform chain.

## Main results

* `uniformChain`, `uniformPoisson`, `uniformPi`, `uniformSpacing`, `uniformTime`;
  `isStochastic_uniformChain`, `isPoissonFamily_uniform`.
* `variance_levelSumN_uniform_ge` (any coin layout with independent rows).
* `eventually_variance_ge_of_close` (variance lower bounds pass to an `o(√k)` perturbation).
* `eventually_variance_occErrN_uniform_shift_ge`, `eventually_variance_occErrN_uniform_owen_ge`
  (**non-vacuity**), `occErrN_uniform_tendstoInDistribution_shift`, `_owen`.
* Three states, target `1` (REQUIRED): `eventually_variance_occErrN_example_shift_ge`,
  `eventually_variance_occErrN_example_owen_ge`, `occErrN_example_tendstoInDistribution_shift`,
  `occErrN_example_tendstoInDistribution_owen`.
* Five states, target `2`: `occErrN_five_tendstoInDistribution_shift`, `_owen`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-! ### The uniform chain -/

/-- The uniform chain `P i j = 1/n`. -/
noncomputable def uniformChain (n : ℕ) : Fin n → Fin n → ℝ := fun _ _ ↦ 1 / n

/-- Its Poisson functions `H t = 1_{t} − 1/n`. -/
noncomputable def uniformPoisson (n : ℕ) : Fin n → Fin n → ℝ :=
  fun t i ↦ (if i = t then 1 else 0) - 1 / n

/-- Its stationary distribution `π = 1/n`. -/
noncomputable def uniformPi (n : ℕ) : Fin n → ℝ := fun _ ↦ 1 / n

/-- The spacing `r = 2n + 6` of the levels. -/
def uniformSpacing (n : ℕ) : ℕ := 2 * n + 6

/-- The times `T_k = n Σ_{a<k} 2^{ra}`. -/
def uniformTime (n k : ℕ) : ℕ := n * patternR (uniformSpacing n) k

/-- The uniform chain is stochastic. -/
theorem isStochastic_uniformChain (hn : 1 ≤ n) : IsStochastic (uniformChain n) where
  nonneg _ _ := by unfold uniformChain; positivity
  sum_eq_one _ := by
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [uniformChain, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

open Matrix in
/-- `P H_t = 0` for the uniform chain. -/
theorem mulVec_uniformPoisson (hn : 1 ≤ n) (t i : Fin n) :
    (uniformChain n *ᵥ uniformPoisson n t) i = 0 := by
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  change ∑ k, uniformChain n i k * uniformPoisson n t k = 0
  simp only [uniformChain, uniformPoisson, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Poisson data of the uniform chain** for every target. -/
theorem isPoissonFamily_uniform (hn : 1 ≤ n) :
    IsPoissonFamily (uniformChain n) (uniformPoisson n) (uniformPi n) := fun t i ↦ by
  rw [mulVec_uniformPoisson hn, sub_zero]
  rfl

/-- `n_i(T_k) = Σ_{a<k} 2^{ra}` in every row. -/
theorem chainIdxN_uniformTime (hn : 1 ≤ n) (k : ℕ) :
    chainIdxN (uniformPi n) (uniformTime n k) = fun _ ↦ patternR (uniformSpacing n) k := by
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  funext i
  unfold chainIdxN uniformTime uniformPi
  push_cast
  rw [show (n : ℝ) * (patternR (uniformSpacing n) k : ℝ) * (1 / n) =
    (patternR (uniformSpacing n) k : ℝ) by field_simp]
  exact Nat.floor_natCast _

/-- The weights of the uniform chain: `h_j − h_{j+1} = 1{j = s} − 1{j + 1 = s}`. -/
theorem cutWeight_uniform (s : Fin n) {j : ℕ} (hj : j + 1 < n) :
    cutWeight (uniformPoisson n s) j =
      (if j = s.val then 1 else 0) - (if j + 1 = s.val then 1 else 0) := by
  have hj' : j < n := by omega
  unfold cutWeight extendNat
  simp only [hj', hj, dite_true, uniformPoisson, Fin.ext_iff]
  ring

/-- The weights are integers. -/
theorem cutWeight_uniform_int (s : Fin n) :
    ∀ j ∈ range (n - 1), ∃ z : ℤ, cutWeight (uniformPoisson n s) j = z := by
  intro j hj
  have hj' : j + 1 < n := by have := mem_range.1 hj; omega
  refine ⟨(if j = s.val then 1 else 0) - (if j + 1 = s.val then 1 else 0), ?_⟩
  rw [cutWeight_uniform s hj']
  push_cast
  rfl

/-- The total weight is at most `2`. -/
theorem absWeightSum_uniform_le (s : Fin n) :
    absWeightSum n (cutWeight (uniformPoisson n s)) ≤ 2 := by
  unfold absWeightSum
  calc ∑ j ∈ range (n - 1), |cutWeight (uniformPoisson n s) j|
      ≤ ∑ j ∈ range (n - 1), ((if j = s.val then (1 : ℝ) else 0) +
          (if j = s.val - 1 then (1 : ℝ) else 0)) := by
        refine sum_le_sum fun j hj ↦ ?_
        have hj' : j + 1 < n := by have := mem_range.1 hj; omega
        rw [cutWeight_uniform s hj']
        split_ifs <;> first | (norm_num; done) | omega
    _ = (∑ j ∈ range (n - 1), if j = s.val then (1 : ℝ) else 0) +
          ∑ j ∈ range (n - 1), if j = s.val - 1 then (1 : ℝ) else 0 := sum_add_distrib
    _ ≤ 1 + 1 := by
        rw [sum_ite_eq', sum_ite_eq']
        gcongr <;> split_ifs <;> norm_num
    _ = 2 := by norm_num

/-- `{2^m · 1} = 0`. -/
theorem fracPow_one (m : ℕ) : fracPow 1 m = 0 := by
  rw [fracPow, mul_one, show (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) by push_cast; rfl,
    Nat.floor_natCast, sub_self]

/-- For `c ≤ 1`, the cut-point fractional part vanishes at `c = 1`. -/
theorem ite_fracPow_eq {c : ℝ} (hc : c ≤ 1) (m : ℕ) :
    (if c < 1 then fracPow c m else 0) = fracPow c m := by
  by_cases h : c < 1
  · simp [h]
  · have : c = 1 := le_antisymm hc (not_lt.1 h)
    subst this
    simp [fracPow_one]

/-- **The weighted cut points are `1/n` modulo integers** (from Abel summation at `u = 0`). -/
theorem sum_cutWeight_mul_cutPoint_uniform (hn : 1 ≤ n) (s i : Fin n) :
    ∃ z : ℤ, ∑ j ∈ range (n - 1),
      cutWeight (uniformPoisson n s) j * cutPoint (uniformChain n) i j = z + 1 / n := by
  have hP := isStochastic_uniformChain hn
  have h := step_sub_mulVec_eq_sum_cut hP (uniformPoisson n s) i (u := 0) (by norm_num)
  rw [mulVec_uniformPoisson hn, sub_zero] at h
  have h' : ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
      ((if (0 : ℝ) ≤ cutPoint (uniformChain n) i j then 1 else 0) -
        cutPoint (uniformChain n) i j) =
      ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j -
        ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
          cutPoint (uniformChain n) i j := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [(cutPoint_mem_Icc hP i j).1, ite_true]
    ring
  rw [h'] at h
  choose! zw hzw using cutWeight_uniform_int (n := n) s
  have hsum : ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j =
      ((∑ j ∈ range (n - 1), zw j : ℤ) : ℝ) := by
    push_cast
    exact sum_congr rfl fun j hj ↦ hzw j hj
  refine ⟨(∑ j ∈ range (n - 1), zw j) - (if step (uniformChain n) i 0 = s then 1 else 0), ?_⟩
  rw [hsum] at h
  simp only [uniformPoisson] at h
  push_cast at h ⊢
  split_ifs at h ⊢ <;> linarith

/-- **The row fraction of the uniform chain is `2^m/n` modulo integers.** -/
theorem rowFrac_uniform (hn : 1 ≤ n) (s i : Fin n) (m : ℕ) :
    ∃ z : ℤ, rowFrac (cutWeight (uniformPoisson n s)) (cutPoint (uniformChain n)) m i =
      2 ^ m / n + z := by
  have hP := isStochastic_uniformChain hn
  obtain ⟨z, hz⟩ := sum_cutWeight_mul_cutPoint_uniform hn s i
  choose! zw hzw using cutWeight_uniform_int (n := n) s
  refine ⟨2 ^ m * z - ∑ j ∈ range (n - 1), zw j * ⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊, ?_⟩
  have e : rowFrac (cutWeight (uniformPoisson n s)) (cutPoint (uniformChain n)) m i =
      2 ^ m * ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
        cutPoint (uniformChain n) i j -
      ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
        (⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊ : ℝ) := by
    rw [rowFrac, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [ite_fracPow_eq (cutPoint_mem_Icc hP i j).2, fracPow]
    ring
  rw [e, hz]
  push_cast
  have e2 : ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
      (⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊ : ℝ) =
      ∑ j ∈ range (n - 1), (zw j : ℝ) * (⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊ : ℝ) :=
    sum_congr rfl fun j hj ↦ by rw [hzw j hj]
  rw [e2]
  ring

/-- `{2^m / n} = (2^m mod n)/n`, which lies in `[1/n, 1 − 1/n]` when `n ∤ 2^m`. -/
theorem fract_mul_one_sub_ge (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m) (m : ℕ) :
    ((n : ℝ) - 1) / n ^ 2 ≤
      Int.fract ((2 : ℝ) ^ m / n) * (1 - Int.fract ((2 : ℝ) ^ m / n)) := by
  have hfr : Int.fract ((2 : ℝ) ^ m / n) = ((2 ^ m % n : ℕ) : ℝ) / n := by
    have := Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := 2 ^ m) (n := n)
    push_cast at this
    exact this
  set r' := 2 ^ m % n with hr'
  have hr1 : 1 ≤ r' := Nat.pos_of_ne_zero fun h ↦ hnd m (Nat.dvd_of_mod_eq_zero h)
  have hr2 : r' < n := Nat.mod_lt _ (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr1' : (1 : ℝ) ≤ r' := by exact_mod_cast hr1
  have hr2' : (r' : ℝ) + 1 ≤ n := by exact_mod_cast hr2
  rw [hfr, div_le_iff₀ (by positivity)]
  have e : (r' : ℝ) / n * (1 - r' / n) * n ^ 2 = r' * (n - r') := by
    field_simp
  rw [e]
  nlinarith

/-- **Per-level variance** of a row term of the uniform chain (any coin layout): at a set bit,
`Var ≥ (n − 1)/n²` (`2/9` for `n = 3`). -/
theorem variance_rowTerm_uniform_ge {ι : Type*} {γ : Fin n → ℕ → ℕ → ι}
    (hγ : ∀ i j, Function.Injective (γ i j)) (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (s : Fin n) (N : Fin n → ℕ) (m : ℕ) (i : Fin n) (hbit : (N i).testBit m = true) :
    ((n : ℝ) - 1) / n ^ 2 ≤ Var[fun ω ↦ rowTerm (cutWeight (uniformPoisson n s))
      (cutPoint (uniformChain n)) N m (coinsOf γ ω) i; coinMeasure ι] := by
  have hP := isStochastic_uniformChain (n := n) (by omega)
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  refine le_trans ?_ (variance_rowTerm_ge_of_int hγ hcp (cutWeight_uniform_int s) N m i hbit)
  obtain ⟨z, hz⟩ := rowFrac_uniform (by omega) s i m
  rw [hz, Int.fract_add_intCast]
  exact fract_mul_one_sub_ge hn2 hnd m

/-- `ρ = 2^{-(2n+6)}` is small: `4 W² ρ/(1 − ρ) ≤ (n − 1)/(2n²)` for `W ≤ 2`. -/
theorem uniformSpacing_bound (hn2 : 2 ≤ n) {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 2) :
    4 * W ^ 2 * ((1 / 2) ^ uniformSpacing n / (1 - (1 / 2) ^ uniformSpacing n)) ≤
      ((n : ℝ) - 1) / n ^ 2 / 2 := by
  set ρ : ℝ := (1 / 2) ^ uniformSpacing n with hρ
  have hρ0 : 0 < ρ := by positivity
  have hq : ((1 : ℝ) / 2) ^ n * n < 1 := by
    have h1 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    exact h1
  have hρe : ρ = (1 / 64) * ((1 / 2) ^ n) ^ 2 := by
    rw [hρ, uniformSpacing, ← pow_mul, show 2 * n + 6 = n * 2 + 6 by ring, pow_add]
    norm_num
    ring
  have hρ1 : ρ ≤ 1 / 2 := by
    rw [hρ]
    calc ((1 : ℝ) / 2) ^ uniformSpacing n ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold uniformSpacing; omega)
      _ = 1 / 2 := by norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have h64 : 64 * (n : ℝ) ^ 2 * ρ ≤ 1 := by
    rw [hρe]
    have hq0 : 0 ≤ ((1 : ℝ) / 2) ^ n * n := by positivity
    nlinarith
  have hfrac : ρ / (1 - ρ) ≤ 2 * ρ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hW2 : W ^ 2 ≤ 4 := by nlinarith
  calc 4 * W ^ 2 * (ρ / (1 - ρ)) ≤ 4 * 4 * (2 * ρ) := by
        gcongr
        · exact div_nonneg hρ0.le (by linarith)
    _ = 32 * ρ := by ring
    _ ≤ ((n : ℝ) - 1) / n ^ 2 / 2 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        nlinarith

/-- **Variance of the main term of the uniform chain** (any coin layout with independent rows):
along `n_i = Σ_{a<k} 2^{ra}`, `Var(levelSumN) ≥ k/4`. -/
theorem variance_levelSumN_uniform_ge {ι : Type*} (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d)
    (hrows : ∀ i i' j j' d d', i ≠ i' → γ i j d ≠ γ i' j' d') (hn2 : 2 ≤ n)
    (hnd : ∀ m, ¬ n ∣ 2 ^ m) (s : Fin n) {k K : ℕ}
    (hK : ∀ a < k, uniformSpacing n * a < K) :
    (k : ℝ) / 4 ≤ Var[fun ω ↦ levelSumN (cutWeight (uniformPoisson n s))
      (cutPoint (uniformChain n)) (fun _ ↦ patternR (uniformSpacing n) k) K (coinsOf γ ω);
      coinMeasure ι] := by
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  have hP := isStochastic_uniformChain (n := n) (by omega)
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hr : 1 ≤ uniformSpacing n := by unfold uniformSpacing; omega
  have h := variance_levelSumN_pattern_ge lev hlev hrows hcp hr hK
    (N := fun _ ↦ patternR (uniformSpacing n) k) (fun _ ↦ rfl) (a₀ := ((n : ℝ) - 1) / n ^ 2)
    (w := cutWeight (uniformPoisson n s)) fun i a ha ↦
      variance_rowTerm_uniform_ge hγ hn2 hnd s _ _ i
        ((testBit_patternR hr k _).2 ⟨Nat.mul_mod_right _ _, by
          rw [Nat.mul_div_cancel_left _ (by omega)]; exact ha⟩)
  refine le_trans ?_ h
  have hb := uniformSpacing_bound hn2 (absWeightSum_nonneg n (cutWeight (uniformPoisson n s)))
    (absWeightSum_uniform_le s)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkey : (k : ℝ) / 4 ≤ n * k * (((n : ℝ) - 1) / n ^ 2 / 2) := by
    have e : (n : ℝ) * k * (((n : ℝ) - 1) / n ^ 2 / 2) = k * ((n - 1) / (2 * n)) := by
      field_simp
    rw [e]
    have : (1 : ℝ) / 4 ≤ (n - 1) / (2 * n) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    nlinarith
  refine hkey.trans ?_
  gcongr
  linarith

/-! ### From the main term to the occupation error -/

/-- **Variance lower bounds survive an `o(√k)` perturbation**: if `|E_k − M_k| ≤ b_k`,
`Var M_k ≥ c k` eventually and `b_k² / k → 0`, then `Var E_k ≥ c k / 4` eventually. -/
theorem eventually_variance_ge_of_close {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E M : ℕ → Ω → ℝ} {b : ℕ → ℝ} (hE : ∀ k, MemLp (E k) 2 μ)
    (hM : ∀ k, MemLp (M k) 2 μ) (hclose : ∀ k ω, |E k ω - M k ω| ≤ b k) {c : ℝ} (hc : 0 < c)
    (hVM : ∀ᶠ k in atTop, c * k ≤ Var[M k; μ])
    (hb : Tendsto (fun k ↦ b k ^ 2 / k) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, c / 4 * k ≤ Var[E k; μ] := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ (abs_nonneg _).trans (hclose k (Classical.arbitrary Ω))
  have hsmall : ∀ᶠ k in atTop, b k ^ 2 / k ≤ c / 4 :=
    hb.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hVM, hsmall, eventually_ge_atTop 1] with k hk hs hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hσ : |√Var[M k; μ] - √Var[E k; μ]| ≤ b k := by
    refine (abs_sqrt_variance_sub_le (hE k) (hM k)).trans ?_
    refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -b k) (b := b k)
      (Eventually.of_forall fun ω ↦ abs_le.1 (hclose k ω))
      ((hE k).sub (hM k)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
    rw [show (b k - -b k) / 2 = b k by ring, Real.sqrt_sq (hb0 k)]
  set sM := √Var[M k; μ] with hsM
  set sE := √Var[E k; μ] with hsE
  have hsM2 : sM ^ 2 = Var[M k; μ] := Real.sq_sqrt (variance_nonneg _ _)
  have hsE2 : sE ^ 2 = Var[E k; μ] := Real.sq_sqrt (variance_nonneg _ _)
  have hsM0 : 0 ≤ sM := Real.sqrt_nonneg _
  have hb2 : b k ^ 2 ≤ c * k / 4 := by
    rw [div_le_iff₀ hk0] at hs
    linarith
  have hbM : b k ≤ sM / 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith [hb0 k]
  have hsE : sM / 2 ≤ sE := by
    have := (abs_le.1 hσ).2
    linarith
  have h4 : sM ^ 2 / 4 ≤ sE ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hsE 2
    rw [div_pow] at this
    linarith
  rw [← hsE2]
  nlinarith

/-- `2^{ra} ≤ T_k` for `a < k`, so the levels `ra` are below `⌊log₂ T_k⌋ + 1`. -/
theorem uniformSpacing_mul_lt (hn : 1 ≤ n) {k a : ℕ} (ha : a < k) :
    uniformSpacing n * a < Nat.log 2 (uniformTime n k) + 1 := by
  have h1 : 2 ^ (uniformSpacing n * a) ≤ patternR (uniformSpacing n) k :=
    single_le_sum (f := fun a ↦ 2 ^ (uniformSpacing n * a)) (fun _ _ ↦ Nat.zero_le _)
      (mem_range.2 ha)
  have h2 : patternR (uniformSpacing n) k ≤ uniformTime n k := by
    unfold uniformTime
    exact Nat.le_mul_of_pos_left _ (by omega)
  have := Nat.le_log_of_pow_le one_lt_two (h1.trans h2)
  omega

/-- `⌊log₂ T_k⌋ ≤ (n + r) k` for `k ≥ 1`. -/
theorem natLog_uniformTime_le {k : ℕ} (hk : 1 ≤ k) :
    Nat.log 2 (uniformTime n k) ≤ (n + uniformSpacing n) * k := by
  have hr : 1 ≤ uniformSpacing n := by unfold uniformSpacing; omega
  have hlt : uniformTime n k < 2 ^ (n + uniformSpacing n * k) := by
    unfold uniformTime
    rw [pow_add]
    exact Nat.mul_lt_mul'' Nat.lt_two_pow_self (patternR_lt hr k)
  by_cases h0 : uniformTime n k = 0
  · rw [h0, Nat.log_zero_right]
    exact Nat.zero_le _
  have := Nat.log_lt_of_lt_pow h0 hlt
  nlinarith

/-- `T_k → ∞`. -/
theorem tendsto_uniformTime (hn : 1 ≤ n) : Tendsto (uniformTime n) atTop atTop := by
  refine tendsto_atTop_mono (fun k ↦ ?_) tendsto_id
  have h : k ≤ patternR (uniformSpacing n) k := by
    rw [patternR]
    calc k = ∑ _a ∈ range k, 1 := by simp
      _ ≤ ∑ a ∈ range k, 2 ^ (uniformSpacing n * a) :=
          sum_le_sum fun a _ ↦ Nat.one_le_two_pow
  exact h.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- The Anscombe error along the uniform times is `o(√k)`. -/
theorem tendsto_ansBoundN_uniform (hn : 1 ≤ n) (s : Fin n) :
    Tendsto (fun k ↦ ansBoundN (uniformPoisson n) s (uniformTime n k) ^ 2 / k) atTop (𝓝 0) := by
  have h := tendsto_sq_div_natLog_of_le (tendsto_uniformTime hn)
    (fun k ↦ ansBoundN_nonneg (uniformPoisson n) s (uniformTime n k))
    (fun k ↦ ansBoundN_le_log (uniformPoisson n) s (uniformTime n k))
  have hlim := h.const_mul ((n : ℝ) + uniformSpacing n)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hlim
  have hlog : ∀ᶠ k in atTop, 1 ≤ Nat.log 2 (uniformTime n k) :=
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun _ ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      (tendsto_uniformTime hn)).eventually_ge_atTop 1
  filter_upwards [hlog, eventually_ge_atTop 1] with k hl hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < Nat.log 2 (uniformTime n k) := by exact_mod_cast hl
  have hle : (Nat.log 2 (uniformTime n k) : ℝ) ≤ ((n : ℝ) + uniformSpacing n) * k := by
    exact_mod_cast natLog_uniformTime_le hk
  have hb := sq_nonneg (ansBoundN (uniformPoisson n) s (uniformTime n k))
  rw [mul_div_assoc', div_le_div_iff₀ hk0 hl0]
  nlinarith

/-- **Non-vacuity, digital shift** (uniform chain, `n` not a power of two, any target):
`Var(N_s(T_k) − T_k/n) ≥ log₂ T_k / (16 (n + r))` eventually. -/
theorem eventually_variance_occErrN_uniform_shift_ge (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) :
    ∀ᶠ k in atTop, 1 / (16 * ((n : ℝ) + uniformSpacing n)) * Nat.log 2 (uniformTime n k) ≤
      Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s (uniformTime n k);
        shiftMeasure n] := by
  have hn : 1 ≤ n := by omega
  have hP := isStochastic_uniformChain hn
  have hH := isPoissonFamily_uniform hn
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hVM : ∀ᶠ k in atTop, (1 / 4 : ℝ) * k ≤ Var[fun ω ↦ shiftMainTerm (uniformChain n)
      (uniformPoisson n) (uniformPi n) s (uniformTime n k) ω; shiftMeasure n] := by
    refine Eventually.of_forall fun k ↦ ?_
    have h := variance_levelSumN_uniform_ge (fun q : Fin n × ℕ ↦ q.2) (γ := shiftLayout n)
      (fun i j d ↦ rfl) shiftLayout_rows hn2 hnd s (k := k)
      (K := Nat.log 2 (uniformTime n k) + 1) fun a ha ↦ uniformSpacing_mul_lt hn ha
    unfold shiftMainTerm
    rw [chainIdxN_uniformTime hn k]
    linarith
  have hev := eventually_variance_ge_of_close
    (E := fun k ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s (uniformTime n k))
    (M := fun k ω ↦ shiftMainTerm (uniformChain n) (uniformPoisson n) (uniformPi n) s
      (uniformTime n k) ω)
    (fun k ↦ memLp_occErrN_shift _ _ x₀ s _)
    (fun k ↦ memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (fun k ω ↦ abs_occErrN_shift_sub_le hP hH x₀ s _ ω) (by norm_num : (0 : ℝ) < 1 / 4) hVM
    (tendsto_ansBoundN_uniform hn s)
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hle : (Nat.log 2 (uniformTime n k) : ℝ) ≤ ((n : ℝ) + uniformSpacing n) * k := by
    exact_mod_cast natLog_uniformTime_le hk1
  have hpos : (0 : ℝ) < (n : ℝ) + uniformSpacing n := by positivity
  refine le_trans ?_ hk
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Non-vacuity, Owen's scramble** (uniform chain, `n` not a power of two, any target):
`Var(N_s(T_k) − T_k/n) ≥ log₂ T_k / (16 (n + r))` eventually (Owen's own variance). -/
theorem eventually_variance_occErrN_uniform_owen_ge (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) :
    ∀ᶠ k in atTop, 1 / (16 * ((n : ℝ) + uniformSpacing n)) * Nat.log 2 (uniformTime n k) ≤
      Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s (uniformTime n k);
        owenMeasure n] := by
  have hn : 1 ≤ n := by omega
  have hP := isStochastic_uniformChain hn
  have hH := isPoissonFamily_uniform hn
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hMP := measurePreserving_owenRelabel (n := n)
  have hVM : ∀ᶠ k in atTop, (1 / 4 : ℝ) * k ≤ Var[fun ω ↦ owenMainTerm (uniformChain n)
      (uniformPoisson n) (uniformPi n) s (uniformTime n k) (owenRelabel ω); owenMeasure n] := by
    refine Eventually.of_forall fun k ↦ ?_
    have h := variance_levelSumN_uniform_ge (fun q : Fin n × ℕ × ℕ ↦ q.2.1)
      (γ := owenLayout (uniformChain n)) (fun i j d ↦ rfl) (owenLayout_rows _) hn2 hnd s
      (k := k) (K := Nat.log 2 (uniformTime n k) + 1) fun a ha ↦ uniformSpacing_mul_lt hn ha
    unfold owenMainTerm
    rw [hMP.variance_fun_comp (measurable_levelSumN_coins hcp _ _ _).aemeasurable,
      chainIdxN_uniformTime hn k]
    linarith
  have hev := eventually_variance_ge_of_close
    (E := fun k ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s (uniformTime n k))
    (M := fun k ω ↦ owenMainTerm (uniformChain n) (uniformPoisson n) (uniformPi n) s
      (uniformTime n k) (owenRelabel ω))
    (fun k ↦ memLp_occErrN_owen _ _ x₀ s _)
    (fun k ↦ (memLp_levelSumN_coins hcp _ _ (owenLayout _)).comp_measurePreserving hMP)
    (fun k ω ↦ abs_occErrN_owen_sub_le hP hH x₀ s _ ω) (by norm_num : (0 : ℝ) < 1 / 4) hVM
    (tendsto_ansBoundN_uniform hn s)
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hle : (Nat.log 2 (uniformTime n k) : ℝ) ≤ ((n : ℝ) + uniformSpacing n) * k := by
    exact_mod_cast natLog_uniformTime_le hk1
  have hpos : (0 : ℝ) < (n : ℝ) + uniformSpacing n := by positivity
  refine le_trans ?_ hk
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The CLT holds on the uniform chain, digital shift** (`n` not a power of two, any start,
any target), along `T_k = n Σ_{a<k} 2^{ra}`. -/
theorem occErrN_uniform_tendstoInDistribution_shift (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s (uniformTime n k) /
      √Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s
        (uniformTime n k); shiftMeasure n]) atTop Z (fun _ ↦ shiftMeasure n) P' :=
  tendstoInDistribution_occErrN_shift (isStochastic_uniformChain (by omega))
    (isPoissonFamily_uniform (by omega)) x₀ s (tendsto_uniformTime (by omega))
    (by positivity) (eventually_variance_occErrN_uniform_shift_ge hn2 hnd x₀ s) hZ

/-- **The CLT holds on the uniform chain, Owen's scramble** (`n` not a power of two, any start,
any target), along `T_k = n Σ_{a<k} 2^{ra}`. -/
theorem occErrN_uniform_tendstoInDistribution_owen (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s (uniformTime n k) /
      √Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s
        (uniformTime n k); owenMeasure n]) atTop Z (fun _ ↦ owenMeasure n) P' :=
  tendstoInDistribution_occErrN_owen (isStochastic_uniformChain (by omega))
    (isPoissonFamily_uniform (by omega)) x₀ s (tendsto_uniformTime (by omega))
    (by positivity) (eventually_variance_occErrN_uniform_owen_ge hn2 hnd x₀ s) hZ

/-! ### Three states (required) and five states -/

/-- `5 ∤ 2^m`. -/
theorem not_five_dvd_two_pow (m : ℕ) : ¬ 5 ∣ 2 ^ m := fun h ↦ by
  have := Nat.le_of_dvd (by norm_num) (Nat.prime_five.dvd_of_dvd_pow h)
  omega

/-- **Non-vacuity on the three-state uniform chain, target `1`, digital shift**:
`Var(N_1(T_k) − T_k/3) ≥ log₂ T_k / 240` eventually, `T_k = 3 Σ_{a<k} 2^{12a}`. -/
theorem eventually_variance_occErrN_example_shift_ge (x₀ : Fin 3) :
    ∀ᶠ k in atTop, 1 / 240 * Nat.log 2 (uniformTime 3 k) ≤
      Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (shiftFlips ω) 1 (uniformTime 3 k);
        shiftMeasure 3] := by
  have h := eventually_variance_occErrN_uniform_shift_ge (n := 3) (by norm_num)
    not_three_dvd_two_pow x₀ 1
  norm_num [uniformSpacing] at h ⊢
  exact h

/-- **Non-vacuity on the three-state uniform chain, target `1`, Owen's scramble**:
`Var(N_1(T_k) − T_k/3) ≥ log₂ T_k / 240` eventually, `T_k = 3 Σ_{a<k} 2^{12a}`. -/
theorem eventually_variance_occErrN_example_owen_ge (x₀ : Fin 3) :
    ∀ᶠ k in atTop, 1 / 240 * Nat.log 2 (uniformTime 3 k) ≤
      Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (owenTable ω) 1 (uniformTime 3 k);
        owenMeasure 3] := by
  have h := eventually_variance_occErrN_uniform_owen_ge (n := 3) (by norm_num)
    not_three_dvd_two_pow x₀ 1
  norm_num [uniformSpacing] at h ⊢
  exact h

/-- **The CLT on the three-state uniform chain, target `1`, digital shift** (post #3, code (ii)). -/
theorem occErrN_example_tendstoInDistribution_shift (x₀ : Fin 3) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 3) (uniformPi 3) x₀ (shiftFlips ω) 1 (uniformTime 3 k) /
      √Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (shiftFlips ω) 1
        (uniformTime 3 k); shiftMeasure 3]) atTop Z (fun _ ↦ shiftMeasure 3) P' :=
  occErrN_uniform_tendstoInDistribution_shift (by norm_num) not_three_dvd_two_pow x₀ 1 hZ

/-- **The CLT on the three-state uniform chain, target `1`, Owen's scramble** (post #3,
code (iii)). -/
theorem occErrN_example_tendstoInDistribution_owen (x₀ : Fin 3) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 3) (uniformPi 3) x₀ (owenTable ω) 1 (uniformTime 3 k) /
      √Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (owenTable ω) 1
        (uniformTime 3 k); owenMeasure 3]) atTop Z (fun _ ↦ owenMeasure 3) P' :=
  occErrN_uniform_tendstoInDistribution_owen (by norm_num) not_three_dvd_two_pow x₀ 1 hZ

/-- **The CLT on the five-state uniform chain, target `2`, digital shift** (post #3's number of
states, code (ii)). -/
theorem occErrN_five_tendstoInDistribution_shift (x₀ : Fin 5) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 5) (uniformPi 5) x₀ (shiftFlips ω) 2 (uniformTime 5 k) /
      √Var[fun ω ↦ occErrN (uniformChain 5) (uniformPi 5) x₀ (shiftFlips ω) 2
        (uniformTime 5 k); shiftMeasure 5]) atTop Z (fun _ ↦ shiftMeasure 5) P' :=
  occErrN_uniform_tendstoInDistribution_shift (by norm_num) not_five_dvd_two_pow x₀ 2 hZ

/-- **The CLT on the five-state uniform chain, target `2`, Owen's scramble** (post #3's number
of states, code (iii)). -/
theorem occErrN_five_tendstoInDistribution_owen (x₀ : Fin 5) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 5) (uniformPi 5) x₀ (owenTable ω) 2 (uniformTime 5 k) /
      √Var[fun ω ↦ occErrN (uniformChain 5) (uniformPi 5) x₀ (owenTable ω) 2
        (uniformTime 5 k); owenMeasure 5]) atTop Z (fun _ ↦ owenMeasure 5) P' :=
  occErrN_uniform_tendstoInDistribution_owen (by norm_num) not_five_dvd_two_pow x₀ 2 hZ

end RQMCMarkov.ScrambledStacks
