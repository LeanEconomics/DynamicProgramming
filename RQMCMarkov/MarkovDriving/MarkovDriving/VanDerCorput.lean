/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.Koksma
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The van der Corput sequence

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

Post #2 builds QMC point sets from the Sobol sequence. In one dimension the Sobol sequence is the
base-2 van der Corput sequence (radical inverse): write `k = ∑ⱼ bⱼ 2ʲ` in binary and reflect
the digits about the binary point, `φ(k) = ∑ⱼ bⱼ 2^{-(j+1)}` (van der Corput 1935;
Niederreiter 1992, Ch. 3; L'Ecuyer 2016).

**Definition.** `vanDerCorput 0 = 0` and `vanDerCorput k = (k mod 2)/2 + vanDerCorput (k/2)/2`,
which is the radical inverse read off the binary digits.

**Results.**
* `vanDerCorput_mem_Ico`: every term lies in `[0,1)`.
* `card_vanDerCorput_mem_dyadic`: **net property.** Any `2^m` *consecutive* terms
  `φ(a), …, φ(a + 2^m - 1)` put exactly one point in each dyadic interval
  `[j/2^m, (j+1)/2^m)`. This holds for every start `a`, in particular for the aligned blocks
  starting at a multiple of `2^m` (`card_vanDerCorput_mem_dyadic_aligned`).
* `abs_countBelow_vanDerCorput_sub_le`: `|#{i < n : φ(i) < t} - nt| ≤ log₂ n + 1`, by splitting
  `n` along its binary expansion into blocks of `2^m` consecutive terms.
* `starDiscrepancy_vanDerCorput_le`: `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n`, and
  `starDiscrepancy_vanDerCorput_le_log`: `D*ₙ ≤ 2 (log n + 1)/n` (natural log).
* `abs_qmcError_vanDerCorput_le`: by Koksma, the QMC error for `f` of bounded variation is at
  most `V(f) · 2 (log n + 1)/n`.
* `tendsto_sqrt_mul_qmcError_vanDerCorput`: hence `√n · |QMC error| → 0`, i.e. the van der
  Corput QMC error is `o(n^{-1/2})`, faster than the MC root-mean-square error `σ/√n` (post #1,
  post #2 "QMC/RQMC have faster rates of convergence than MC").
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology

/-- The base-2 van der Corput (radical-inverse) sequence: `φ(0) = 0` and
`φ(k) = (k mod 2)/2 + φ(⌊k/2⌋)/2`. -/
noncomputable def vanDerCorput : ℕ → ℝ
  | 0 => 0
  | k + 1 => (((k + 1) % 2 : ℕ) : ℝ) / 2 + vanDerCorput ((k + 1) / 2) / 2
decreasing_by omega

/-- The defining recursion of the van der Corput sequence, for every `k`. -/
theorem vanDerCorput_eq (k : ℕ) :
    vanDerCorput k = ((k % 2 : ℕ) : ℝ) / 2 + vanDerCorput (k / 2) / 2 := by
  cases k with
  | zero =>
    rw [Nat.zero_mod, Nat.zero_div, vanDerCorput.eq_1, Nat.cast_zero]
    ring
  | succ k => rw [vanDerCorput]

/-- `φ(2q + b) = b/2 + φ(q)/2` for a binary digit `b`. -/
theorem vanDerCorput_two_mul_add (q b : ℕ) (hb : b < 2) :
    vanDerCorput (2 * q + b) = (b : ℝ) / 2 + vanDerCorput q / 2 := by
  rw [vanDerCorput_eq, show (2 * q + b) % 2 = b by omega, show (2 * q + b) / 2 = q by omega]

/-- The first terms: `φ(1) = 1/2`, `φ(2) = 1/4`, `φ(3) = 3/4`. -/
theorem vanDerCorput_one_two_three :
    vanDerCorput 1 = 1 / 2 ∧ vanDerCorput 2 = 1 / 4 ∧ vanDerCorput 3 = 3 / 4 := by
  have h0 : vanDerCorput 0 = 0 := vanDerCorput.eq_1
  have h1 : vanDerCorput 1 = 1 / 2 := by
    rw [vanDerCorput_eq, show (1 : ℕ) / 2 = 0 by norm_num, h0]
    norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [vanDerCorput_eq, show (2 : ℕ) / 2 = 1 by norm_num, h1]
    norm_num
  · rw [vanDerCorput_eq, show (3 : ℕ) / 2 = 1 by norm_num, h1]
    norm_num

/-- Every van der Corput point lies in `[0,1)`. -/
theorem vanDerCorput_mem_Ico (k : ℕ) : vanDerCorput k ∈ Set.Ico (0 : ℝ) 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [vanDerCorput.eq_1]
      exact ⟨le_refl 0, zero_lt_one⟩
    · have h := ih (k / 2) (Nat.div_lt_self hk (by norm_num))
      have hb : ((k % 2 : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt k (by norm_num))
      have hb0 : (0 : ℝ) ≤ ((k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [vanDerCorput_eq]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The first `n` van der Corput points lie in `[0,1)`, for every `n`. -/
theorem vanDerCorput_inUnitIco (n : ℕ) : InUnitIco vanDerCorput n :=
  fun i _ => vanDerCorput_mem_Ico i

/-- The `m`-digit index `⌊2^m φ(k)⌋` is below `2^m`. -/
theorem floor_two_pow_mul_vanDerCorput_lt (m k : ℕ) :
    ⌊(2 : ℝ) ^ m * vanDerCorput k⌋₊ < 2 ^ m := by
  have h := vanDerCorput_mem_Ico k
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_lt (mul_nonneg hpos.le h.1), Nat.cast_pow, Nat.cast_ofNat]
  exact mul_lt_of_lt_one_right hpos h.2

/-- The digit recursion: `⌊2^{m+1} φ(k)⌋ = (k mod 2) 2^m + ⌊2^m φ(⌊k/2⌋)⌋`. -/
theorem floor_two_pow_succ_mul_vanDerCorput (m k : ℕ) :
    ⌊(2 : ℝ) ^ (m + 1) * vanDerCorput k⌋₊ =
      k % 2 * 2 ^ m + ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ := by
  have h : (2 : ℝ) ^ (m + 1) * vanDerCorput k =
      (2 : ℝ) ^ m * vanDerCorput (k / 2) + ((k % 2 * 2 ^ m : ℕ) : ℝ) := by
    rw [vanDerCorput_eq k, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [h, Nat.floor_add_natCast (mul_nonneg (pow_nonneg zero_le_two m)
    (vanDerCorput_mem_Ico _).1), add_comm]

/-- The `m`-digit index determines `k mod 2^m`. -/
theorem mod_eq_of_floor_vanDerCorput_eq (m : ℕ) : ∀ {k k' : ℕ},
    ⌊(2 : ℝ) ^ m * vanDerCorput k⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput k'⌋₊ →
      k % 2 ^ m = k' % 2 ^ m := by
  induction m with
  | zero =>
    intro k k' _
    rw [pow_zero, Nat.mod_one, Nat.mod_one]
  | succ m ih =>
    intro k k' h
    rw [floor_two_pow_succ_mul_vanDerCorput, floor_two_pow_succ_mul_vanDerCorput] at h
    have hA := floor_two_pow_mul_vanDerCorput_lt m (k / 2)
    have hA' := floor_two_pow_mul_vanDerCorput_lt m (k' / 2)
    have hbits : k % 2 = k' % 2 ∧ ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ =
        ⌊(2 : ℝ) ^ m * vanDerCorput (k' / 2)⌋₊ := by
      generalize ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ = A at h hA ⊢
      generalize ⌊(2 : ℝ) ^ m * vanDerCorput (k' / 2)⌋₊ = A' at h hA' ⊢
      generalize (2 : ℕ) ^ m = P at h hA hA' ⊢
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
      rcases Nat.mod_two_eq_zero_or_one k' with hk' | hk' <;>
      rw [hk, hk'] at h ⊢ <;> omega
    rw [pow_succ', Nat.mod_mul, Nat.mod_mul, hbits.1, ih hbits.2]

/-- Within any block of `2^m` consecutive terms, the `m`-digit index is injective. -/
theorem floor_vanDerCorput_injOn (m a : ℕ) :
    Set.InjOn (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊)
      (Finset.range (2 ^ m) : Set ℕ) := by
  intro r hr r' hr' h
  have hr1 : r < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hr)
  have hr1' : r' < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hr')
  have hmod : a + r ≡ a + r' [MOD 2 ^ m] := mod_eq_of_floor_vanDerCorput_eq m h
  have := Nat.ModEq.add_left_cancel' a hmod
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr1'] at this

/-- A point `v ≥ 0` lies in the dyadic interval `[j/2^m, (j+1)/2^m)` iff `⌊2^m v⌋ = j`. -/
theorem mem_dyadic_iff_floor (m j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v ∈ Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m) ↔ ⌊(2 : ℝ) ^ m * v⌋₊ = j := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_eq_iff (mul_nonneg hpos.le hv), Set.mem_Ico, div_le_iff₀ hpos, lt_div_iff₀ hpos,
    mul_comm v]

/-- **Net property.** Any `2^m` consecutive van der Corput terms `φ(a), …, φ(a + 2^m - 1)` put
exactly one point in each dyadic interval `[j/2^m, (j+1)/2^m)`, `j < 2^m`. -/
theorem card_vanDerCorput_mem_dyadic (m a j : ℕ) (hj : j < 2 ^ m) :
    ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) ∈
      Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m))).card = 1 := by
  have hmaps : Set.MapsTo (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊)
      (Finset.range (2 ^ m) : Set ℕ) (Finset.range (2 ^ m) : Set ℕ) := fun r _ =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (floor_two_pow_mul_vanDerCorput_lt m (a + r)))
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps (floor_vanDerCorput_injOn m a)
    (le_refl _)
  obtain ⟨r, hr, hrj⟩ := hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
  rw [Finset.card_eq_one]
  refine ⟨r, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · rw [Finset.mem_filter, mem_dyadic_iff_floor m j (vanDerCorput_mem_Ico _).1]
    exact ⟨Finset.mem_coe.mp hr, hrj⟩
  · intro r' hr'
    rw [Finset.mem_filter, mem_dyadic_iff_floor m j (vanDerCorput_mem_Ico _).1] at hr'
    exact floor_vanDerCorput_injOn m a (Finset.mem_coe.mpr hr'.1) hr (hr'.2.trans hrj.symm)

/-- **Net property, aligned blocks.** The block `φ(k 2^m), …, φ(k 2^m + 2^m - 1)` hits each
dyadic interval of length `2^{-m}` exactly once. -/
theorem card_vanDerCorput_mem_dyadic_aligned (m k j : ℕ) (hj : j < 2 ^ m) :
    ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (k * 2 ^ m + r) ∈
      Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m))).card = 1 :=
  card_vanDerCorput_mem_dyadic m (k * 2 ^ m) j hj

/-- A block of `2^m` consecutive van der Corput terms has local counting error at most `1`:
`|#{r < 2^m : φ(a + r) < t} - 2^m t| ≤ 1` for `t ∈ [0,1]`. -/
theorem abs_card_block_vanDerCorput_sub_le (m a : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) -
      2 ^ m * t| ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hmt : 0 ≤ (2 : ℝ) ^ m * t := mul_nonneg hpos.le ht.1
  have hinj := floor_vanDerCorput_injOn m a
  -- upper bound
  have hup : ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card ≤
      ⌊(2 : ℝ) ^ m * t⌋₊ + 1 := by
    have := Finset.card_le_card_of_injOn (t := Finset.range (⌊(2 : ℝ) ^ m * t⌋₊ + 1))
      (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊) ?_
      (hinj.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun r : ℕ => vanDerCorput (a + r) < t) _)))
    · rwa [Finset.card_range] at this
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left hr.2.le hpos.le)
  -- lower bound, through the complement
  have hcompl : ((Finset.range (2 ^ m)).filter (fun r => ¬ vanDerCorput (a + r) < t)).card ≤
      2 ^ m - ⌊(2 : ℝ) ^ m * t⌋₊ := by
    have := Finset.card_le_card_of_injOn (t := Finset.Ico ⌊(2 : ℝ) ^ m * t⌋₊ (2 ^ m))
      (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊) ?_
      (hinj.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun r : ℕ => ¬ vanDerCorput (a + r) < t) _)))
    · rwa [Nat.card_Ico] at this
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Finset.mem_Ico]
    exact ⟨Nat.floor_le_floor (mul_le_mul_of_nonneg_left (not_lt.mp hr.2) hpos.le),
      floor_two_pow_mul_vanDerCorput_lt m (a + r)⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (2 ^ m))
    (fun r : ℕ => vanDerCorput (a + r) < t)
  rw [Finset.card_range] at hsplit
  have hj : ⌊(2 : ℝ) ^ m * t⌋₊ ≤ 2 ^ m := by
    apply Nat.floor_le_of_le
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have := mul_le_mul_of_nonneg_left ht.2 hpos.le
    linarith
  have hlow : ⌊(2 : ℝ) ^ m * t⌋₊ ≤
      ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card := by omega
  have hupR : (((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) ≤
      (⌊(2 : ℝ) ^ m * t⌋₊ : ℝ) + 1 := by exact_mod_cast hup
  have hlowR : (⌊(2 : ℝ) ^ m * t⌋₊ : ℝ) ≤
      (((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) := by
    exact_mod_cast hlow
  have hfl := Nat.floor_le hmt
  have hfl' := Nat.lt_floor_add_one ((2 : ℝ) ^ m * t)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Splitting the counting function: the first `N + M` points are the first `N` points and the
block of `M` points starting at `N`. -/
theorem countBelow_add (x : ℕ → ℝ) (N M : ℕ) (t : ℝ) :
    countBelow x (N + M) t =
      countBelow x N t + ((Finset.range M).filter (fun r => x (N + r) < t)).card := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]

/-- **Counting error of the van der Corput sequence.** For `t ∈ [0,1]`,
`|#{i < n : φ(i) < t} - nt| ≤ ⌊log₂ n⌋ + 1`. -/
theorem abs_countBelow_vanDerCorput_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow vanDerCorput N t : ℝ) - N * t| ≤ Nat.log 2 N + 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [show countBelow vanDerCorput 0 t = 0 from rfl, Nat.cast_zero, zero_mul, sub_zero,
        abs_zero]
      positivity
    · have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
      have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      obtain ⟨N', hN'⟩ : ∃ N', N = N' + 2 ^ Nat.log 2 N := ⟨N - 2 ^ Nat.log 2 N, by omega⟩
      have hN'lt : N' < 2 ^ Nat.log 2 N := by rw [pow_succ] at hlt; omega
      have hblock := abs_card_block_vanDerCorput_sub_le (Nat.log 2 N) N' ht
      have hsplit : (countBelow vanDerCorput N t : ℝ) - N * t =
          ((countBelow vanDerCorput N' t : ℝ) - N' * t) +
          ((((Finset.range (2 ^ Nat.log 2 N)).filter
            (fun r => vanDerCorput (N' + r) < t)).card : ℝ) - 2 ^ Nat.log 2 N * t) := by
        conv_lhs => rw [hN', countBelow_add]
        push_cast
        ring
      have hrest : |(countBelow vanDerCorput N' t : ℝ) - N' * t| ≤ Nat.log 2 N := by
        rcases Nat.eq_zero_or_pos N' with h0 | h0
        · rw [h0, show countBelow vanDerCorput 0 t = 0 from rfl, Nat.cast_zero, zero_mul,
            sub_zero, abs_zero]
          positivity
        · have hlog : Nat.log 2 N' < Nat.log 2 N := Nat.log_lt_of_lt_pow h0.ne' hN'lt
          have hlogR : (Nat.log 2 N' : ℝ) + 1 ≤ Nat.log 2 N := by exact_mod_cast hlog
          exact (ih N' (by omega)).trans hlogR
      rw [hsplit]
      calc _ ≤ |(countBelow vanDerCorput N' t : ℝ) - N' * t| +
            |(((Finset.range (2 ^ Nat.log 2 N)).filter
              (fun r => vanDerCorput (N' + r) < t)).card : ℝ) - 2 ^ Nat.log 2 N * t| :=
            abs_add_le _ _
        _ ≤ _ := by linarith

/-- **Star discrepancy of the van der Corput sequence:** `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n`. -/
theorem starDiscrepancy_vanDerCorput_le {n : ℕ} (hn : 0 < n) :
    starDiscrepancy vanDerCorput n ≤ ((Nat.log 2 n : ℝ) + 1) / n := by
  apply starDiscrepancy_le_of_forall
  intro t ht
  rw [localDiscrepancy_eq_abs_div _ hn.ne' t]
  exact div_le_div_of_nonneg_right (abs_countBelow_vanDerCorput_sub_le n ht) (Nat.cast_nonneg n)

/-- `⌊log₂ n⌋ + 1 ≤ 2 (log n + 1)` for `n ≥ 1` (natural logarithm). -/
theorem natLog_two_add_one_le {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) + 1 ≤ 2 * (Real.log n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  rw [Nat.cast_pow, Nat.cast_ofNat] at hpow
  have hlog := Real.log_le_log (pow_pos two_pos _) hpow
  rw [Real.log_pow] at hlog
  have hl2 := Real.log_two_gt_d9
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

/-- **Star discrepancy of the van der Corput sequence, natural-log form:**
`D*ₙ ≤ 2 (log n + 1)/n`. -/
theorem starDiscrepancy_vanDerCorput_le_log {n : ℕ} (hn : 0 < n) :
    starDiscrepancy vanDerCorput n ≤ 2 * (Real.log n + 1) / n :=
  (starDiscrepancy_vanDerCorput_le hn).trans
    (div_le_div_of_nonneg_right (natLog_two_add_one_le hn) (Nat.cast_nonneg n))

/-- **QMC error of the van der Corput sequence** (Koksma): for `f` of bounded variation on
`[0,1]`, `|(1/n) ∑_{i<n} f(φ(i)) - ∫₀¹ f| ≤ V(f) · 2 (log n + 1)/n`. -/
theorem abs_qmcError_vanDerCorput_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {n : ℕ} (hn : 0 < n) :
    |qmcEstimate f vanDerCorput n - ∫ t in (0 : ℝ)..1, f t| ≤
      totalVariation f * (2 * (Real.log n + 1) / n) :=
  (koksma_boundedVariationOn hf (vanDerCorput_inUnitIco n) hn).trans
    (mul_le_mul_of_nonneg_left (starDiscrepancy_vanDerCorput_le_log hn) ENNReal.toReal_nonneg)

/-- `(log x + 1)/√x → 0`. -/
theorem tendsto_log_add_one_div_sqrt :
    Tendsto (fun x : ℝ => (Real.log x + 1) / Real.sqrt x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr fun x => ?_
  rw [Real.sqrt_eq_rpow, add_div, one_div (x ^ (1 / 2 : ℝ))]

/-- **QMC beats MC (the bound).** `√n · 2 (log n + 1)/n → 0`: the van der Corput discrepancy
bound falls faster than the MC rate `n^{-1/2}`. -/
theorem tendsto_sqrt_mul_vanDerCorput_bound :
    Tendsto (fun n : ℕ => Real.sqrt n * (2 * (Real.log n + 1) / n)) atTop (𝓝 0) := by
  have h := (tendsto_log_add_one_div_sqrt.comp tendsto_natCast_atTop_atTop).const_mul 2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
  simp only [Function.comp_apply]
  calc 2 * ((Real.log n + 1) / Real.sqrt n)
      = 2 * (Real.log n + 1) * Real.sqrt n / (Real.sqrt n * Real.sqrt n) := by
        rw [mul_div_mul_right _ _ hs.ne', mul_div_assoc]
    _ = Real.sqrt n * (2 * (Real.log n + 1) / n) := by
        rw [hsq]
        ring

/-- **QMC beats MC (the error).** For `f` of bounded variation on `[0,1]`, the van der Corput
QMC error is `o(n^{-1/2})`: `√n · |(1/n) ∑_{i<n} f(φ(i)) - ∫₀¹ f| → 0`. MC has root-mean-square
error exactly `σ(f)/√n`, so it is beaten whenever `σ(f) > 0`. -/
theorem tendsto_sqrt_mul_qmcError_vanDerCorput {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => Real.sqrt n * |qmcEstimate f vanDerCorput n - ∫ t in (0 : ℝ)..1, f t|)
      atTop (𝓝 0) := by
  have h := tendsto_sqrt_mul_vanDerCorput_bound.const_mul (totalVariation f)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  have := mul_le_mul_of_nonneg_left (abs_qmcError_vanDerCorput_le hf hn)
    (Real.sqrt_nonneg (n : ℝ))
  calc _ ≤ _ := this
    _ = _ := by ring

end RQMCMarkov.MarkovDriving
