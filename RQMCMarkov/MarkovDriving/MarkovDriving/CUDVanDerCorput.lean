/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.ChentsovConsistency
import MarkovDriving.VanDerCorput

/-! # The van der Corput sequence is uniformly distributed but not CUD

Post #3: "if the QMC method we use is 'completely uniformly distributed' (not a given, using
Sobol sequences would fail this)", and codes (a): "just swapping the random numbers for a Sobol
sequence … fails badly". In one dimension the Sobol sequence is the base-2 van der Corput
sequence `φ` (`MarkovDriving.VanDerCorput`).

**Results.**
* `isUD_of_tendsto_starDiscrepancy`: in one dimension, star discrepancy `D*_N → 0` implies
  uniform distribution (boxes `[a, b)` as differences of anchored boxes `[0, t)`).
* `isUD_vanDerCorput`: `φ` is uniformly distributed in `[0,1)` (`D*_N ≤ 2 (log N + 1)/N`).
* `vanDerCorput_two_mul_add_one`: `φ(2k+1) = φ(2k) + 1/2`, and `vanDerCorput_lt_half_iff`:
  `φ(k) < 1/2 ↔ k` even. Hence consecutive terms alternate between `[0,1/2)` and `[1/2,1)`
  (`vanDerCorput_succ_lt_half_iff`): the pairs `(φ(t), φ(t+1))` avoid `[0,1/2)² ∪ [1/2,1)²`, a set
  of area `1/2`.
* `not_isUD_window_two_vanDerCorput`, `not_isCUD_vanDerCorput`: the pairs are not uniformly
  distributed in `[0,1)²` (no pair lies in `[0,1/2)²`), so `φ` is **not CUD**.
* **Counterexample (codes (a)).** `twoState` has rows `(1/2, 1/2)` and `(1, 0)` (stay
  probability `1/2` in state `0`), stationary distribution `π = (2/3, 1/3)`
  (`twoState_stationary`). Driven by `φ` from any start, the path alternates `0, 1, 0, 1, …` from
  time `3` on (`drivenPath_twoState_vanDerCorput`), so the frequency of state `1` tends to `1/2`
  (`tendsto_occFreq_twoState_vanDerCorput`), not `π₁ = 1/3`
  (`not_tendsto_occFreq_twoState_vanDerCorput`). The chain has a coupling box (column `0` is
  `≥ 1/2`), so for every CUD driving sequence the frequency does tend to `1/3`
  (`tendsto_occFreq_twoState_of_isCUD`): the failure is due to `φ` not being CUD, and one-
  dimensional uniformity, even with discrepancy `O(log N / N)`, is not enough.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

/-- In one dimension the empirical box frequency of `[a, b)` is a difference of two anchored
counts. -/
theorem empAvg_window_one_eq (x : ℕ → ℝ) (a b : Fin 1 → ℝ) (hab : a 0 ≤ b 0) (N : ℕ) :
    empAvg (boxInd fun k => Set.Ico (a k) (b k)) (window x 1) N =
      (countBelow x N (b 0) : ℝ) / N - (countBelow x N (a 0) : ℝ) / N := by
  have hcount : ∀ t, (countBelow x N t : ℝ) = ∑ n ∈ range N, if x n < t then (1 : ℝ) else 0 := by
    intro t
    unfold countBelow
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun n _ => by
      split_ifs
      · exact Nat.cast_one
      · exact Nat.cast_zero
  unfold empAvg
  rw [hcount, hcount, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  classical
  rw [boxInd_eq_ite]
  have hw : ∀ k : Fin 1, window x 1 n k = x n := fun k => by
    rw [Fin.fin_one_eq_zero k]
    rfl
  by_cases h1 : x n < a 0
  · have hn : ¬ ∀ k : Fin 1, window x 1 n k ∈ Set.Ico (a k) (b k) := fun h => by
      have := (h 0).1
      rw [hw 0] at this
      linarith
    have h2 : x n < b 0 := lt_of_lt_of_le h1 hab
    simp only [hn, h1, h2, ↓reduceIte, sub_self]
  · by_cases h2 : x n < b 0
    · have hy : ∀ k : Fin 1, window x 1 n k ∈ Set.Ico (a k) (b k) := fun k => by
        rw [hw k, Fin.fin_one_eq_zero k]
        exact ⟨not_lt.1 h1, h2⟩
      simp only [hy, h1, h2, ↓reduceIte, implies_true, sub_zero]
    · have hn : ¬ ∀ k : Fin 1, window x 1 n k ∈ Set.Ico (a k) (b k) := fun h => by
        have := (h 0).2
        rw [hw 0] at this
        exact h2 this
      simp only [hn, h1, h2, ↓reduceIte, sub_self]

/-- **One-dimensional uniform distribution from discrepancy.** If `x` lies in `[0,1)` and its
star discrepancy tends to `0`, then `x` is uniformly distributed in `[0,1)`. -/
theorem isUD_of_tendsto_starDiscrepancy {x : ℕ → ℝ} (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1)
    (hD : Tendsto (starDiscrepancy x) atTop (𝓝 0)) : IsUD (window x 1) := by
  refine ⟨fun n k => hx (n + k), fun a b hab => ?_⟩
  rw [Fin.prod_univ_one]
  have hb : b 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hab 0).1.trans (hab 0).2.1, (hab 0).2.2⟩
  have ha : a 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hab 0).1, (hab 0).2.1.trans (hab 0).2.2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun N => 2 * starDiscrepancy x N) atTop (𝓝 0) := by
    have := hD.const_mul 2
    rwa [mul_zero] at this
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) h2
  rw [empAvg_window_one_eq x a b (hab 0).2.1 N, Real.norm_eq_abs]
  have hbD := localDiscrepancy_le_starDiscrepancy x N hb
  have haD := localDiscrepancy_le_starDiscrepancy x N ha
  unfold localDiscrepancy at hbD haD
  have e : (countBelow x N (b 0) : ℝ) / N - (countBelow x N (a 0) : ℝ) / N - (b 0 - a 0) =
      ((countBelow x N (b 0) : ℝ) / N - b 0) - ((countBelow x N (a 0) : ℝ) / N - a 0) := by ring
  rw [e]
  calc _ ≤ |(countBelow x N (b 0) : ℝ) / N - b 0| + |(countBelow x N (a 0) : ℝ) / N - a 0| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-- **The van der Corput sequence is uniformly distributed** in `[0,1)`. -/
theorem isUD_vanDerCorput : IsUD (window vanDerCorput 1) := by
  refine isUD_of_tendsto_starDiscrepancy vanDerCorput_mem_Ico ?_
  have hb : Tendsto (fun n : ℕ => 2 * (Real.log n + 1) / n) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_sqrt_mul_vanDerCorput_bound
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : 0 ≤ Real.log n := Real.log_nonneg this
      positivity
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : 0 ≤ Real.log n := Real.log_nonneg h1
      have hs : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact h1
      have hnn : 0 ≤ 2 * (Real.log n + 1) / n := by positivity
      calc 2 * (Real.log n + 1) / n = 1 * (2 * (Real.log n + 1) / n) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hs hnn
  refine squeeze_zero' (Eventually.of_forall fun n => starDiscrepancy_nonneg _ _) ?_ hb
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact starDiscrepancy_vanDerCorput_le_log hn

/-- `φ(2k+1) = φ(2k) + 1/2`: the term after an even-indexed term is shifted by exactly `1/2`. -/
theorem vanDerCorput_two_mul_add_one (k : ℕ) :
    vanDerCorput (2 * k + 1) = vanDerCorput (2 * k) + 1 / 2 := by
  have h1 := vanDerCorput_two_mul_add k 1 (by norm_num)
  have h0 := vanDerCorput_two_mul_add k 0 (by norm_num)
  rw [add_zero] at h0
  rw [h1, h0]
  push_cast
  ring

/-- `φ(k) < 1/2` exactly for even `k`. -/
theorem vanDerCorput_lt_half_iff (k : ℕ) : vanDerCorput k < 1 / 2 ↔ k % 2 = 0 := by
  have h := vanDerCorput_mem_Ico (k / 2)
  rw [vanDerCorput_eq k]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [hk, Nat.cast_zero]
    exact ⟨fun _ => rfl, fun _ => by linarith [h.2]⟩
  · rw [hk, Nat.cast_one]
    exact ⟨fun h' => by linarith [h.1], fun h' => absurd h' (by norm_num)⟩

/-- **Consecutive terms alternate halves:** `φ(t+1) < 1/2 ↔ ¬ φ(t) < 1/2`. -/
theorem vanDerCorput_succ_lt_half_iff (t : ℕ) :
    vanDerCorput (t + 1) < 1 / 2 ↔ ¬ vanDerCorput t < 1 / 2 := by
  rw [vanDerCorput_lt_half_iff, vanDerCorput_lt_half_iff]
  omega

/-- **The van der Corput pairs are not uniformly distributed** in `[0,1)²`: no pair
`(φ(t), φ(t+1))` lies in `[0,1/2)²`, whose area is `1/4`. -/
theorem not_isUD_window_two_vanDerCorput : ¬ IsUD (window vanDerCorput 2) := by
  intro hUD
  have hlim := hUD.2 (fun _ => 0) (fun _ => 1 / 2) fun _ => ⟨le_refl 0, by norm_num, by norm_num⟩
  have hzero : empAvg (boxInd fun _ => Set.Ico (0 : ℝ) (1 / 2)) (window vanDerCorput 2) =
      fun _ => 0 := by
    funext N
    unfold empAvg
    rw [Finset.sum_eq_zero fun t _ => ?_, zero_div]
    classical
    rw [boxInd_eq_ite]
    split_ifs with hall
    · have h0 : vanDerCorput t < 1 / 2 := (hall 0).2
      have h1 : vanDerCorput (t + 1) < 1 / 2 := (hall 1).2
      exact absurd h0 ((vanDerCorput_succ_lt_half_iff t).1 h1)
    · rfl
  rw [hzero] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [Fin.prod_univ_two] at this
  norm_num at this

/-- **The van der Corput sequence is not CUD** (post #3: "using Sobol sequences would fail
this"). -/
theorem not_isCUD_vanDerCorput : ¬ IsCUD vanDerCorput :=
  fun h => not_isUD_window_two_vanDerCorput (h 2)

/-- `φ(k) > 0` for `k ≥ 1`. -/
theorem vanDerCorput_pos {k : ℕ} (hk : 0 < k) : 0 < vanDerCorput k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [vanDerCorput_eq k]
    have h0 := (vanDerCorput_mem_Ico (k / 2)).1
    rcases Nat.mod_two_eq_zero_or_one k with hm | hm
    · have hpos := ih (k / 2) (Nat.div_lt_self hk (by norm_num)) (by omega)
      rw [hm, Nat.cast_zero]
      linarith
    · rw [hm, Nat.cast_one]
      linarith

/-- The two-state chain with rows `(1/2, 1/2)` and `(1, 0)`: from state `0` stay or move with
probability `1/2`; from state `1` always return to `0`. -/
noncomputable def twoState : Fin 2 → Fin 2 → ℝ := fun i j =>
  if (i : ℕ) = 0 then 1 / 2 else if (j : ℕ) = 0 then 1 else 0

/-- `twoState` is stochastic. -/
theorem isStochastic_twoState : IsStochastic twoState := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold twoState
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num [twoState]

/-- The stationary distribution of `twoState` is `(2/3, 1/3)`. -/
theorem twoState_stationary (j : Fin 2) :
    ∑ i, (![2 / 3, 1 / 3] : Fin 2 → ℝ) i * twoState i j = (![2 / 3, 1 / 3] : Fin 2 → ℝ) j := by
  rw [Fin.sum_univ_two]
  fin_cases j <;> norm_num [twoState]

/-- From state `1` every uniform in `(0,1]` leads to state `0`. -/
theorem step_twoState_one {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) : step twoState 1 u = 0 :=
  (step_eq_iff isStochastic_twoState 1 0 hu).2 (by
    unfold cumProb
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [twoState]
    exact ⟨hu.1, hu.2⟩)

/-- From state `0` a uniform in `(0, 1/2]` leads to state `0`. -/
theorem step_twoState_zero_low {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    step twoState 0 u = 0 :=
  (step_eq_iff isStochastic_twoState 0 0 ⟨hu.1, by linarith [hu.2]⟩).2 (by
    unfold cumProb
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [twoState]
    exact ⟨hu.1, hu.2⟩)

/-- From state `0` a uniform in `(1/2, 1]` leads to state `1`. -/
theorem step_twoState_zero_high {u : ℝ} (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    step twoState 0 u = 1 :=
  (step_eq_iff isStochastic_twoState 0 1 ⟨by linarith [hu.1], hu.2⟩).2 (by
    unfold cumProb
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [twoState]
    exact ⟨hu.1, hu.2⟩)

/-- **The van der Corput–driven path alternates.** From any start, the path of `twoState`
driven by `φ` is in state `1` at even times and in state `0` at odd times, from time `3` on. -/
theorem drivenPath_twoState_vanDerCorput (x₀ : Fin 2) (t : ℕ) :
    drivenPath twoState x₀ vanDerCorput (t + 3) = if (t + 3) % 2 = 0 then 1 else 0 := by
  induction t with
  | zero =>
    change step twoState (drivenPath twoState x₀ vanDerCorput 2) (vanDerCorput 2) = _
    have h2 : vanDerCorput 2 = 1 / 4 := vanDerCorput_one_two_three.2.1
    rw [h2]
    have hlow : (1 / 4 : ℝ) ∈ Set.Ioc 0 (1 / 2) := ⟨by norm_num, by norm_num⟩
    have hone : (1 / 4 : ℝ) ∈ Set.Ioc 0 1 := ⟨by norm_num, by norm_num⟩
    have hval : (if (0 + 3) % 2 = 0 then (1 : Fin 2) else 0) = 0 := rfl
    rw [hval]
    generalize drivenPath twoState x₀ vanDerCorput 2 = s
    fin_cases s
    · exact step_twoState_zero_low hlow
    · exact step_twoState_one hone
  | succ t ih =>
    change step twoState (drivenPath twoState x₀ vanDerCorput (t + 3)) (vanDerCorput (t + 3)) = _
    rw [ih]
    have hpos := vanDerCorput_pos (show 0 < t + 3 by omega)
    have hlt := (vanDerCorput_mem_Ico (t + 3)).2
    rcases Nat.mod_two_eq_zero_or_one (t + 3) with hm | hm
    · have h1 : (t + 1 + 3) % 2 = 1 := by omega
      simp only [hm, h1, ↓reduceIte, one_ne_zero]
      exact step_twoState_one ⟨hpos, hlt.le⟩
    · have h1 : (t + 1 + 3) % 2 = 0 := by omega
      simp only [hm, h1, ↓reduceIte, one_ne_zero]
      refine step_twoState_zero_high ⟨?_, hlt.le⟩
      have hodd : ¬ vanDerCorput (t + 3) < 1 / 2 := by
        rw [vanDerCorput_lt_half_iff]
        omega
      have h2 : t + 3 = 2 * ((t + 3) / 2) + 1 := by omega
      have hq : 0 < vanDerCorput ((t + 3) / 2) := vanDerCorput_pos (by omega)
      rw [h2, vanDerCorput_two_mul_add_one]
      have h0 := vanDerCorput_two_mul_add ((t + 3) / 2) 0 (by norm_num)
      rw [add_zero, Nat.cast_zero, zero_div, zero_add] at h0
      rw [h0]
      linarith

/-- The number of even times below `T` is `⌊(T+1)/2⌋`. -/
theorem sum_range_even_indicator (T : ℕ) :
    (∑ t ∈ range T, if t % 2 = 0 then (1 : ℝ) else 0) = (((T + 1) / 2 : ℕ) : ℝ) := by
  induction T with
  | zero =>
    rw [Finset.sum_range_zero]
    norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one T with h | h
    · have e : (T + 1 + 1) / 2 = (T + 1) / 2 + 1 := by omega
      simp only [h, ↓reduceIte, e, Nat.cast_add, Nat.cast_one]
    · have e : (T + 1 + 1) / 2 = (T + 1) / 2 := by omega
      have h' : T % 2 ≠ 0 := by omega
      simp only [h', ↓reduceIte, e, add_zero]

/-- **Codes (a) "fails badly".** Driven by the van der Corput sequence, the frequency of state
`1` of `twoState` tends to `1/2`. -/
theorem tendsto_occFreq_twoState_vanDerCorput (x₀ : Fin 2) :
    Tendsto (fun T => (occCount (drivenPath twoState x₀ vanDerCorput) 1 T : ℝ) / T) atTop
      (𝓝 (1 / 2)) := by
  set x := drivenPath twoState x₀ vanDerCorput with hx
  set E : ℕ → ℝ := fun T => ∑ t ∈ range T, if t % 2 = 0 then (1 : ℝ) else 0 with hE
  -- the occupation count differs from the even count by at most `3`
  have hdiff : ∀ T, |(occCount x 1 T : ℝ) - E T| ≤ 3 := by
    intro T
    rw [occCount_eq_sum, hE]
    dsimp only
    rw [← Finset.sum_sub_distrib]
    set dlt : ℕ → ℝ := fun t => (if x t = 1 then (1 : ℝ) else 0) - if t % 2 = 0 then 1 else 0
    have hvan : ∀ t, 3 ≤ t → dlt t = 0 := by
      intro t ht
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
      change (if x (s + 3) = 1 then (1 : ℝ) else 0) - (if (s + 3) % 2 = 0 then 1 else 0) = 0
      rw [hx, drivenPath_twoState_vanDerCorput]
      rcases Nat.mod_two_eq_zero_or_one (s + 3) with hm | hm
      · simp only [hm, ↓reduceIte, sub_self]
      · simp only [hm, ↓reduceIte, one_ne_zero, zero_ne_one, sub_self]
    have hb : ∀ t, |dlt t| ≤ 1 := fun t => by
      change |(if x t = 1 then (1 : ℝ) else 0) - if t % 2 = 0 then 1 else 0| ≤ 1
      split_ifs <;> norm_num
    calc |∑ t ∈ range T, dlt t| ≤ ∑ t ∈ range T, |dlt t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range T, if t < 3 then (1 : ℝ) else 0 := Finset.sum_le_sum fun t _ => by
          split_ifs with h
          · exact hb t
          · rw [hvan t (not_lt.1 h), abs_zero]
      _ ≤ ∑ t ∈ range 3, (1 : ℝ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun _ _ _ => zero_le_one
          rw [Finset.mem_filter] at ht
          exact Finset.mem_range.2 ht.2
      _ = 3 := by norm_num
  have hEb : ∀ T : ℕ, 0 < T → |E T / T - 1 / 2| ≤ 1 / T := by
    intro T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    rw [hE]
    dsimp only
    rw [sum_range_even_indicator]
    have h1 : (T : ℝ) ≤ 2 * (((T + 1) / 2 : ℕ) : ℝ) := by
      have : T ≤ 2 * ((T + 1) / 2) := by omega
      exact_mod_cast this
    have h2 : 2 * (((T + 1) / 2 : ℕ) : ℝ) ≤ T + 1 := by
      have : 2 * ((T + 1) / 2) ≤ T + 1 := by omega
      exact_mod_cast this
    set c : ℝ := (((T + 1) / 2 : ℕ) : ℝ) with hc
    have key : c / T - 1 / 2 = (2 * c - T) / (2 * T) := by
      rw [div_sub_div _ _ hTR.ne' two_ne_zero]
      congr 1 <;> ring
    rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * T),
      div_le_div_iff₀ (by positivity) hTR]
    have hab : |2 * c - T| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (2 * c - T)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 : Tendsto (fun T : ℕ => 4 / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ h4
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Real.norm_eq_abs]
  have hd : |(occCount x 1 T : ℝ) / T - E T / T| ≤ 3 / T := by
    rw [← sub_div, abs_div, abs_of_pos hTR]
    exact div_le_div_of_nonneg_right (hdiff T) hTR.le
  calc |(occCount x 1 T : ℝ) / T - 1 / 2|
      ≤ |(occCount x 1 T : ℝ) / T - E T / T| + |E T / T - 1 / 2| := abs_sub_le _ _ _
    _ ≤ 3 / T + 1 / T := add_le_add hd (hEb T hT)
    _ = 4 / T := by ring

/-- **Counterexample (post #3 / codes (a)).** Driven by the van der Corput sequence (the
one-dimensional Sobol sequence), the occupation frequency of state `1` of `twoState` does not
converge to its stationary probability `π₁ = 1/3`. -/
theorem not_tendsto_occFreq_twoState_vanDerCorput (x₀ : Fin 2) :
    ¬ Tendsto (fun T => (occCount (drivenPath twoState x₀ vanDerCorput) 1 T : ℝ) / T) atTop
      (𝓝 (1 / 3)) := fun h => by
  have := tendsto_nhds_unique h (tendsto_occFreq_twoState_vanDerCorput x₀)
  norm_num at this

/-- **Contrast: CUD driving is consistent for `twoState`** (Chentsov's theorem, coupling form;
column `0` is bounded below by `1/2`): the frequency of state `1` tends to `π₁ = 1/3`. -/
theorem tendsto_occFreq_twoState_of_isCUD {u : ℕ → ℝ} (hu : IsCUD u) (x₀ : Fin 2) :
    Tendsto (fun T => (occCount (drivenPath twoState x₀ u) 1 T : ℝ) / T) atTop (𝓝 (1 / 3)) := by
  have h := tendsto_occFreq_of_isCUD_of_col_pos isStochastic_twoState hu 0 rfl
    (c := 1 / 2) (by norm_num) (fun i => by fin_cases i <;> norm_num [twoState])
    (π := ![2 / 3, 1 / 3]) twoState_stationary (fun i => by fin_cases i <;> norm_num)
    (by rw [Fin.sum_univ_two]; norm_num) x₀ 1
  exact h

end RQMCMarkov.MarkovDriving
