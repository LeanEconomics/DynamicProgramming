/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.OccupationDiscrepancy
import MarkovDriving.VanDerCorput

/-! # Per-state stacks: departures are balanced (post #3)

Post #3: "with a separate QMC-generated uniform sequence used for the transitions out of each
state … the departures from each state are balanced, so the empirical transition matrix
converges faster than `O(1/√T)`". In the stack representation (`stackPath P x₀ v`) the `k`-th
departure from `i` goes to `step P i (v i k)`, and that departure goes to `j` iff
`v i k ∈ (cs_{i,j−1}, cs_{ij}]` (`step_lt_iff`: `step P i u < m ↔ u ≤ cs_{i,m}`, valid also at
`u = 0`). So the departures from `i` are a one-dimensional QMC sample of the row `P(i, ·)`, and
their error is controlled by the star discrepancy `D*_N` of the first `N = N_i(T)` points of
stack `i` (Niederreiter 1992, Ch. 2; L'Ecuyer 2016).

**Results** (`N = N_i(T)` departures from `i`, stack points in `[0,1)`).
* `abs_card_step_eq_sub_le`, `abs_transCount_stackPath_sub_le`:
  `|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(v i)`.
* `abs_sum_step_sub_le` (discrete Koksma inequality, by summation by parts),
  `abs_departureDiscrepancy_stackPath_le`: `|D_i(g, T)| ≤ V(g) · N · D*_N(v i)`, where
  `V(g) = stateVariation g = Σ_{j < n−1} |g(j+1) − g(j)|` bounds the total variation of the
  step function `u ↦ g(step P i u)` on `[0,1]` (equal to it when every `p_ij > 0`), and
  `stateVariation_le`: `V(g) ≤ 2 (n − 1) ‖g‖∞`.
* `abs_occCount_stackPath_sub_le`: `|N_s(T) − T π_s| ≤ 2‖h‖∞ + Σ_i V(h) N_i D*_{N_i}(v i)`.
* **Van der Corput stacks** (one copy of the van der Corput sequence, the one-dimensional Sobol
  sequence, for each state): with `L = ⌊log₂ T⌋ + 1`,
  - `abs_transCount_vdc_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2L`;
  - `abs_occCount_vdc_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) L ≤ 2M + 2n(n−1) M L`;
  - `abs_occFreq_vdc_sub_le`: occupation frequency error `≤ (2M + n V(h) L)/T`, i.e.
    `O(log T / T)` (`occFreq_vdc_isBigO`);
  - `abs_empiricalTrans_vdc_sub_le`: empirical transition matrix error
    `|N_ij/N_i − p_ij| ≤ 2(⌊log₂ N_i⌋ + 1)/N_i`, and `empiricalTrans_vdc_isBigO`: it is
    `O(log T / T)` for an irreducible chain (`N_i(T) ≥ T π_i / 2` eventually).
  This is the precise form of "faster than `O(1/√T)`" and "QMC's `O(log T / T)`" (post #3).
-/

namespace RQMCMarkov.MarkovDriving

open Finset Matrix Filter Asymptotics

variable {n : ℕ}

/-- **The inverse-CDF rule as a threshold**: for `u ≤ 1` and `m ≥ 1`,
`step P i u < m ↔ u ≤ cumProb P i m` (post #3's `u ≤ cs_{i,m}`). This also covers `u = 0`. -/
theorem step_lt_iff {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) {u : ℝ}
    (hu : u ≤ 1) {m : ℕ} (hm : 1 ≤ m) : (step P i u : ℕ) < m ↔ u ≤ cumProb P i m := by
  have hstep : step P i u = (insert (lastState i)
      (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))).min' (insert_nonempty _ _) := rfl
  constructor
  · intro h
    have hmem := Finset.min'_mem (insert (lastState i)
      (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))) (insert_nonempty _ _)
    rw [← hstep] at hmem
    rcases mem_insert.1 hmem with hl | hf
    · have hnm : n ≤ m := by
        rw [hl] at h
        simp only [lastState] at h
        omega
      rw [cumProb_of_le P i hnm, hP.sum_eq_one i]
      exact hu
    · exact (mem_filter.1 hf).2.trans (cumProb_mono hP.nonneg i (by omega))
  · intro h
    by_cases hmn : m ≤ n
    · have hj : (⟨m - 1, by omega⟩ : Fin n) ∈ insert (lastState i)
          (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) := by
        refine mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, ?_⟩)
        have e : ((⟨m - 1, by omega⟩ : Fin n) : ℕ) + 1 = m := by
          change m - 1 + 1 = m
          omega
        rw [e]
        exact h
      have hle := Finset.min'_le _ _ hj
      rw [← hstep] at hle
      have hle' : (step P i u : ℕ) ≤ m - 1 := hle
      omega
    · exact lt_of_lt_of_le (step P i u).isLt (by omega)

/-- The number of the first `N` points of `v` whose departure from `i` goes to a state `< m`. -/
noncomputable def departuresBelow (P : Fin n → Fin n → ℝ) (i : Fin n) (v : ℕ → ℝ) (N m : ℕ) :
    ℕ :=
  ((range N).filter fun k => (step P i (v k) : ℕ) < m).card

/-- For `m ≥ 1` and points in `[0,1)`, `departuresBelow` is the counting function
`#{k < N : v k ≤ cs_{i,m}}`. -/
theorem departuresBelow_eq_countAtMost {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) {m : ℕ} (hm : 1 ≤ m) :
    departuresBelow P i v N m = countAtMost v N (cumProb P i m) := by
  unfold departuresBelow countAtMost
  congr 1
  refine filter_congr fun k hk => ?_
  exact step_lt_iff hP i (hv k (mem_range.1 hk)).2.le hm

/-- **One threshold**: `|#{k < N : step(v k) < m} − N cs_{i,m}| ≤ N D*_N`. -/
theorem abs_departuresBelow_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (m : ℕ) :
    |(departuresBelow P i v N m : ℝ) - N * cumProb P i m| ≤ N * starDiscrepancy v N := by
  have hD := starDiscrepancy_nonneg v N
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i v N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : departuresBelow P i v 0 m = 0 := by
      unfold departuresBelow
      rw [range_zero, filter_empty, card_empty]
    rw [h0]
    simp only [Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]
  rw [departuresBelow_eq_countAtMost hP i hv hm]
  have ha := cumProb_mem_Icc hP i m
  set a := cumProb P i m with ha_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le ha.2 with ha1 | ha1
  · have hup := countAtMost_div_sub_le_starDiscrepancy v N ha.1 ha1
    have hbelow : countBelow v N a ≤ countAtMost v N a := by
      apply Finset.card_le_card
      intro k hk
      rw [mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.le⟩
    have hloc := localDiscrepancy_le_starDiscrepancy v N ha
    unfold localDiscrepancy at hloc
    have hlow : a - (countBelow v N a : ℝ) / N ≤ starDiscrepancy v N :=
      (neg_le_abs _).trans' (by linarith) |>.trans hloc
    have hb : (countBelow v N a : ℝ) ≤ countAtMost v N a := by exact_mod_cast hbelow
    rw [abs_le]
    constructor
    · have : a - (countAtMost v N a : ℝ) / N ≤ starDiscrepancy v N := by
        have : (countBelow v N a : ℝ) / N ≤ (countAtMost v N a : ℝ) / N :=
          div_le_div_of_nonneg_right hb hNpos.le
        linarith
      have h2 : (N : ℝ) * (a - (countAtMost v N a : ℝ) / N) ≤ N * starDiscrepancy v N :=
        mul_le_mul_of_nonneg_left this hNpos.le
      rw [mul_sub, mul_div_cancel₀ _ hNpos.ne'] at h2
      linarith
    · have h2 : (N : ℝ) * ((countAtMost v N a : ℝ) / N - a) ≤ N * starDiscrepancy v N :=
        mul_le_mul_of_nonneg_left hup hNpos.le
      rw [mul_sub, mul_div_cancel₀ _ hNpos.ne'] at h2
      linarith
  · have hall : countAtMost v N a = N := by
      unfold countAtMost
      rw [filter_true_of_mem fun k hk => ?_, card_range]
      rw [ha1]
      exact (hv k (mem_range.1 hk)).2.le
    rw [hall, ha1, mul_one, sub_self, abs_zero]
    positivity

/-- The count of departures to `j` is a difference of two thresholds. -/
theorem card_step_eq_eq_sub (P : Fin n → Fin n → ℝ) (i : Fin n) (v : ℕ → ℝ) (N : ℕ) (j : Fin n) :
    (((range N).filter fun k => step P i (v k) = j).card : ℝ) =
      departuresBelow P i v N (j + 1) - departuresBelow P i v N j := by
  unfold departuresBelow
  rw [eq_sub_iff_add_eq, ← sum_boole, ← sum_boole, ← sum_boole, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases h1 : step P i (v k) = j
  · rw [h1]
    simp only [lt_irrefl, Nat.lt_add_one, ite_true, ite_false, add_zero]
  · have h1' : (step P i (v k) : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    by_cases h2 : (step P i (v k) : ℕ) < j
    · have h3 : (step P i (v k) : ℕ) < j + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, zero_add]
    · have h3 : ¬ ((step P i (v k) : ℕ) < j + 1) := by omega
      simp only [h1, h2, h3, ite_false, add_zero]

/-- **Balanced departures from one stack**: `|#{k < N : step(v k) = j} − N p_ij| ≤ 2 N D*_N`. -/
theorem abs_card_step_eq_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (j : Fin n) :
    |(((range N).filter fun k => step P i (v k) = j).card : ℝ) - P i j * N| ≤
      2 * (N * starDiscrepancy v N) := by
  rw [card_step_eq_eq_sub]
  have e : (departuresBelow P i v N (j + 1) : ℝ) - departuresBelow P i v N j - P i j * N =
      ((departuresBelow P i v N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i v N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_sub_le hP i hv (j + 1)
  have h2 := abs_departuresBelow_sub_le hP i hv j
  calc _ ≤ |(departuresBelow P i v N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i v N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- A function on the states `Fin n`, extended by `0` to `ℕ`. -/
noncomputable def extendNat (g : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then g ⟨j, h⟩ else 0

/-- The **variation of `g` along the state order** `V(g) = Σ_{j < n−1} |g(j+1) − g(j)|`; it
bounds the total variation on `[0,1]` of the step function `u ↦ g(step P i u)` (with equality
when every `p_ij > 0`). -/
noncomputable def stateVariation (g : Fin n → ℝ) : ℝ :=
  ∑ j ∈ range (n - 1), |extendNat g (j + 1) - extendNat g j|

/-- `0 ≤ V(g)`. -/
theorem stateVariation_nonneg (g : Fin n → ℝ) : 0 ≤ stateVariation g :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- `V(g) ≤ 2 (n − 1) M` when `|g| ≤ M`. -/
theorem stateVariation_le {g : Fin n → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) :
    stateVariation g ≤ 2 * (n - 1 : ℕ) * M := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold stateVariation
    rw [Nat.zero_sub, range_zero, sum_empty, Nat.cast_zero, mul_zero, zero_mul]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ⟨0, hn⟩)
  have hext : ∀ j, |extendNat g j| ≤ M := by
    intro j
    unfold extendNat
    split_ifs with h
    · exact hM _
    · rw [abs_zero]
      exact hM0
  unfold stateVariation
  calc ∑ j ∈ range (n - 1), |extendNat g (j + 1) - extendNat g j|
      ≤ ∑ _j ∈ range (n - 1), 2 * M := sum_le_sum fun j _ => by
        have := abs_sub (extendNat g (j + 1)) (extendNat g j)
        linarith [hext (j + 1), hext j]
    _ = 2 * (n - 1 : ℕ) * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Summation by parts.** If `B 0 = 0` then
`Σ_{j ≤ m} f_j (B_{j+1} − B_j) = f_m B_{m+1} − Σ_{j < m} (f_{j+1} − f_j) B_{j+1}`. -/
theorem sum_mul_sub_eq_abel (f B : ℕ → ℝ) (hB : B 0 = 0) (m : ℕ) :
    ∑ j ∈ range (m + 1), f j * (B (j + 1) - B j) =
      f m * B (m + 1) - ∑ j ∈ range m, (f (j + 1) - f j) * B (j + 1) := by
  induction m with
  | zero => rw [sum_range_one, range_zero, sum_empty, hB, sub_zero, sub_zero]
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- **Discrete Koksma inequality for one stack**:
`|Σ_{k<N} g(step P i (v k)) − N (Pg)(i)| ≤ V(g) · N · D*_N`. -/
theorem abs_sum_step_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (g : Fin n → ℝ) :
    |∑ k ∈ range N, (g (step P i (v k)) - (P *ᵥ g) i)| ≤
      stateVariation g * (N * starDiscrepancy v N) := by
  -- `B m = #{step < m} − N cs_m`
  set B : ℕ → ℝ := fun m => (departuresBelow P i v N m : ℝ) - N * cumProb P i m with hBdef
  have hB0 : B 0 = 0 := by
    have h0 : departuresBelow P i v N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    simp only [hBdef, h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hBn : B n = 0 := by
    have hn : departuresBelow P i v N n = N := by
      unfold departuresBelow
      rw [filter_true_of_mem fun k _ => (step P i (v k)).isLt, card_range]
    simp only [hBdef, hn, cumProb_of_le P i le_rfl, hP.sum_eq_one i, mul_one, sub_self]
  have hBb : ∀ m, |B m| ≤ N * starDiscrepancy v N := abs_departuresBelow_sub_le hP i hv
  -- the sum as `Σ_j g_j (B(j+1) − B(j))`
  have e1 : ∑ k ∈ range N, (g (step P i (v k)) - (P *ᵥ g) i) =
      ∑ j : Fin n, g j * (B (j + 1) - B j) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [← sum_fiberwise (range N) (fun k => step P i (v k))]
    have e2 : ∀ j : Fin n, ∑ k ∈ (range N).filter (fun k => step P i (v k) = j),
        g (step P i (v k)) = g j * (((range N).filter fun k => step P i (v k) = j).card : ℝ) :=
      fun j => by
        rw [sum_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], sum_const, nsmul_eq_mul,
          mul_comm]
    rw [sum_congr rfl fun j _ => e2 j]
    have e3 : (N : ℝ) * (P *ᵥ g) i = ∑ j : Fin n, g j * (P i j * N) := by
      simp only [mulVec, dotProduct, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [e3, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sub, card_step_eq_eq_sub]
    congr 1
    simp only [hBdef]
    rw [cumProb_succ]
    ring
  rw [e1]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [Finset.univ_eq_empty, sum_empty, abs_zero]
    exact mul_nonneg (stateVariation_nonneg g)
      (mul_nonneg (Nat.cast_nonneg _) (starDiscrepancy_nonneg v N))
  -- to `ℕ`-indexed sums, then summation by parts
  have e4 : ∑ j : Fin n, g j * (B (j + 1) - B j) =
      ∑ j ∈ range n, extendNat g j * (B (j + 1) - B j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => extendNat g j * (B (j + 1) - B j)) n]
    refine sum_congr rfl fun j _ => ?_
    simp only [extendNat, j.isLt, ↓reduceDIte, Fin.eta]
  rw [e4]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_mul_sub_eq_abel _ B hB0 m, hBn, mul_zero, zero_sub, abs_neg]
  unfold stateVariation
  rw [Nat.add_sub_cancel, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBb (j + 1)) (abs_nonneg _)

variable {P : Fin n → Fin n → ℝ}

/-- **Stacks balance the transitions** (post #3): in a stack path with stack points in `[0,1)`,
`|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(v i)`, `N = N_i(T)`. -/
theorem abs_transCount_stackPath_sub_le (hP : IsStochastic P) (x₀ : Fin n) {v : Fin n → ℕ → ℝ}
    (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ v) i j T : ℝ) - P i j * occCount (stackPath P x₀ v) i T| ≤
      2 * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) := by
  rw [transCount_stackDrive]
  exact abs_card_step_eq_sub_le hP i (fun k _ => hv i k) j

/-- **Departure discrepancy of a stack path**: `|D_i(g, T)| ≤ V(g) · N · D*_N(v i)`. -/
theorem abs_departureDiscrepancy_stackPath_le (hP : IsStochastic P) (x₀ : Fin n)
    {v : Fin n → ℕ → ℝ} (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) (g : Fin n → ℝ) (i : Fin n)
    (T : ℕ) : |departureDiscrepancy P g (stackPath P x₀ v) i T| ≤
      stateVariation g * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) := by
  exact (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ v i T)).trans_le
    (abs_sum_step_sub_le hP i (fun k _ => hv i k) g)

/-- **Occupation error of a stack path**: `|N_s(T) − T π_s| ≤ 2M + Σ_i V(h) N_i D*_{N_i}(v i)`,
for `h − Ph = 1_{s} − π_s`, `|h| ≤ M`. -/
theorem abs_occCount_stackPath_sub_le (hP : IsStochastic P) (x₀ : Fin n) {v : Fin n → ℕ → ℝ}
    (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ v) s T : ℝ) - T * c| ≤
      2 * M + ∑ i, stateVariation h * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) :=
  (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl
    (sum_le_sum fun i _ => abs_departureDiscrepancy_stackPath_le hP x₀ hv h i T))

/-- `N D*_N(φ) ≤ ⌊log₂ T⌋ + 1` for the van der Corput sequence `φ` and `N ≤ T`. -/
theorem mul_starDiscrepancy_vdc_le {N T : ℕ} (hNT : N ≤ T) :
    N * starDiscrepancy vanDerCorput N ≤ (Nat.log 2 T : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, zero_mul]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := starDiscrepancy_vanDerCorput_le hN
  have h2 : (N : ℝ) * starDiscrepancy vanDerCorput N ≤ (Nat.log 2 N : ℝ) + 1 := by
    rw [le_div_iff₀ hNpos] at h1
    linarith
  have h3 : (Nat.log 2 N : ℝ) ≤ Nat.log 2 T := by exact_mod_cast Nat.log_mono_right hNT
  linarith

/-- **Van der Corput stacks balance the transitions**: `|N_ij(T) − p_ij N_i(T)| ≤
2 (⌊log₂ T⌋ + 1)`. -/
theorem abs_transCount_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ fun _ => vanDerCorput) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  (abs_transCount_stackPath_sub_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) i j T).trans
    (mul_le_mul_of_nonneg_left (mul_starDiscrepancy_vdc_le (occCount_le _ _ _)) zero_le_two)

/-- **Van der Corput stacks: occupation error `O(log T)`**:
`|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`. -/
theorem abs_occCount_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (T : ℕ) :
    |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
  refine (abs_occCount_stackPath_sub_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) hh hM T).trans
    (add_le_add le_rfl ?_)
  calc ∑ i, stateVariation h * (occCount (stackPath P x₀ fun _ => vanDerCorput) i T *
        starDiscrepancy vanDerCorput (occCount (stackPath P x₀ fun _ => vanDerCorput) i T))
      ≤ ∑ _i : Fin n, stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (mul_starDiscrepancy_vdc_le (occCount_le _ _ _)) (stateVariation_nonneg h)
    _ = n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Van der Corput stacks: occupation frequency error `O(log T / T)`** (post #3, "QMC's
`O(log T / T)`"): `|N_s(T)/T − π_s| ≤ (2M + n V(h) (⌊log₂ T⌋ + 1))/T`. -/
theorem abs_occFreq_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) {T : ℕ} (hT : 0 < T) :
    |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) / T - c| ≤
      (2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm c]
  exact abs_occCount_vdc_sub_le hP x₀ hh hM T

/-- **Van der Corput stacks: empirical transition matrix error**:
`|N_ij(T)/N_i(T) − p_ij| ≤ 2 (⌊log₂ T⌋ + 1)/N_i(T)` whenever `N_i(T) > 0`. -/
theorem abs_empiricalTrans_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) {T : ℕ}
    (hN : 0 < occCount (stackPath P x₀ fun _ => vanDerCorput) i T) :
    |(transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) /
        occCount (stackPath P x₀ fun _ => vanDerCorput) i T - P i j| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) / occCount (stackPath P x₀ fun _ => vanDerCorput) i T := by
  set N := occCount (stackPath P x₀ fun _ => vanDerCorput) i T
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos, ← abs_of_pos hNpos, ← abs_mul, abs_of_pos hNpos, sub_mul,
    div_mul_cancel₀ _ hNpos.ne']
  exact abs_transCount_vdc_sub_le hP x₀ i j T

/-- `1 ≤ log x` for `x ≥ 3`. -/
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- `(⌊log₂ T⌋ + 1) / T`-type bounds are `O(log T / T)`: if `|e T| ≤ (A + B (⌊log₂ T⌋ + 1))/T`
for `T > 0`, with `A, B ≥ 0`, then `e = O(log T / T)`. -/
theorem isBigO_log_div_of_le {e : ℕ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : ∀ T : ℕ, 0 < T → |e T| ≤ (A + B * ((Nat.log 2 T : ℝ) + 1)) / T) :
    e =O[atTop] fun T : ℕ => Real.log T / T := by
  refine IsBigO.of_bound (A + 4 * B) ?_
  filter_upwards [eventually_ge_atTop 3] with T hT
  have hTpos : 0 < T := by omega
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog := one_le_log_of_three_le hTR
  have h2 := natLog_two_add_one_le hTpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ Real.log T) (Nat.cast_nonneg T)),
    mul_div_assoc']
  refine (he T hTpos).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have h3 : B * ((Nat.log 2 T : ℝ) + 1) ≤ B * (2 * (Real.log T + 1)) :=
    mul_le_mul_of_nonneg_left h2 hB
  nlinarith [mul_le_mul_of_nonneg_left hlog hA, mul_le_mul_of_nonneg_left hlog hB]

/-- **Van der Corput stacks: the occupation frequencies converge at `O(log T / T)`**
(post #3's "QMC's `O(log T / T)`"). -/
theorem occFreq_vdc_isBigO (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) / T - c) =O[atTop]
      fun T : ℕ => Real.log T / T :=
  isBigO_log_div_of_le (by linarith [(abs_nonneg _).trans (hM s)])
    (mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h))
    fun _ hT => abs_occFreq_vdc_sub_le hP x₀ hh hM hT

/-- **Van der Corput stacks: the empirical transition matrix converges at `O(log T / T)`**, for
a state `i` with `π_i = c > 0` (post #3, "faster than `O(1/√T)`"). The number of departures
`N_i(T)` is at least `T c / 2` eventually, by the occupation bound. -/
theorem empiricalTrans_vdc_isBigO (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {i : Fin n} {c M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c)
    (hM : ∀ k, |h k| ≤ M) (hc : 0 < c) (j : Fin n) :
    (fun T : ℕ => (transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) /
        occCount (stackPath P x₀ fun _ => vanDerCorput) i T - P i j) =O[atTop]
      fun T : ℕ => Real.log T / T := by
  set x := stackPath P x₀ fun _ => vanDerCorput with hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM i)
  set V := stateVariation h
  have hV0 : 0 ≤ (n : ℝ) * V := mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h)
  -- eventually `log T ≤ (c / (8 (n V + 1))) T` and `2M + 2nV ≤ T c / 4`
  have hlogo := (Real.isLittleO_log_id_atTop.bound (c := c / (8 * ((n : ℝ) * V + 1)))
    (by positivity))
  have hlogN : ∀ᶠ T : ℕ in atTop,
      Real.log T ≤ c / (8 * ((n : ℝ) * V + 1)) * T := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogo, eventually_ge_atTop 1]
      with T hT hT1
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hTR),
      abs_of_nonneg (by linarith)] at hT
  have hbig : ∀ᶠ T : ℕ in atTop, 4 * (2 * M + 2 * ((n : ℝ) * V)) / c ≤ T :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine IsBigO.of_bound (16 / c) ?_
  filter_upwards [hlogN, hbig, eventually_ge_atTop 3] with T hlogT hbigT hT3
  have hTpos : 0 < T := by omega
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT3
  have hTR0 : (0 : ℝ) < T := by linarith
  have hlog1 := one_le_log_of_three_le hTR
  have h2 := natLog_two_add_one_le hTpos
  -- the occupation bound gives `N_i(T) ≥ T c / 2`
  have hocc := abs_occCount_vdc_sub_le hP x₀ hh hM T
  have hNlow : T * c / 2 ≤ (occCount x i T : ℝ) := by
    have h4 : (n : ℝ) * V * ((Nat.log 2 T : ℝ) + 1) ≤ (n : ℝ) * V * (2 * (Real.log T + 1)) :=
      mul_le_mul_of_nonneg_left h2 hV0
    have h5 : (n : ℝ) * V * (2 * Real.log T) ≤ T * c / 4 := by
      have h6 : (n : ℝ) * V * Real.log T ≤ ((n : ℝ) * V + 1) * Real.log T :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h7 : ((n : ℝ) * V + 1) * Real.log T ≤
          ((n : ℝ) * V + 1) * (c / (8 * ((n : ℝ) * V + 1)) * T) :=
        mul_le_mul_of_nonneg_left hlogT (by linarith)
      have h8 : ((n : ℝ) * V + 1) * (c / (8 * ((n : ℝ) * V + 1)) * T) = T * c / 8 := by
        field_simp
      linarith
    have h9 : 2 * M + 2 * ((n : ℝ) * V) ≤ T * c / 4 := by
      rw [div_le_iff₀ hc] at hbigT
      linarith
    have := (abs_le.1 hocc).1
    nlinarith
  have hNpos' : (0 : ℝ) < occCount x i T := lt_of_lt_of_le (by positivity) hNlow
  have hNpos : 0 < occCount x i T := by exact_mod_cast hNpos'
  have hb := abs_empiricalTrans_vdc_sub_le hP x₀ i j hNpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hTR0.le)]
  refine hb.trans ?_
  rw [div_le_iff₀ hNpos']
  have h10 : 2 * ((Nat.log 2 T : ℝ) + 1) ≤ 8 * Real.log T := by linarith
  have h11 : 16 / c * (Real.log T / T) * (T * c / 2) = 8 * Real.log T := by
    field_simp
    ring
  have h12 : 0 ≤ 16 / c * (Real.log T / T) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hNlow h12]

end RQMCMarkov.MarkovDriving
