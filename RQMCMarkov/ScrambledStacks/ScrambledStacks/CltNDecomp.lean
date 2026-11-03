/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltVariance

/-!
# n-state stack chains: the occupation error as a sum of level terms (post #3)

Post #3, codes (ii) and (iii), with any number `n` of states: "in the five-state chain
normality cannot be rejected for the per-state Sobol sequences ((ii) and (iii))". This module is
randomisation-free: everything holds for EVERY flip table `f`.

Let `P` be stochastic on `Fin n`, `s` a target state and `h − Ph = 1_{s} − c` (Poisson's
equation). Along the chain driven by the scrambled van der Corput stacks of `f`, the occupation
error `E_T = N_s(T) − T c` is `h(X₀) − h(X_T) + Σ_i D_i(N_i(T))` (`OccupationDiscrepancy`), and by
Abel summation the departure discrepancy of row `i` is a weighted sum of local discrepancies at
the **cut points** `c_{ij} = cumProb P i (j+1)`, `j < n − 1`, with weights `h_j − h_{j+1}`
(`step_sub_mulVec_eq_sum_cut`, `sum_step_sub_eq_sum_segErr`, `occCount_sub_eq_boundary_add_cuts`).

**Reading of `π`.** We take Poisson data for EVERY target (`IsPoissonFamily P H π`:
`H t − P H t = 1_{t} − π_t` for all `t`), which is satisfiable (e.g. `H t = 1_{t} − 1/n`, `π = 1/n`
for the uniform chain, `CltNExample`), and forces `π_t ∈ [0,1]` (`IsPoissonFamily.mem_Icc`).
The occupation error of target `s` is `occErrN = N_s(T) − T π_s`, its Poisson function `H s`.

**Cut points equal to `1`** contribute nothing (all points are `≤ 1`): they are handled, not
assumed away (`cutTerm` is `0` there, `segErr_scrambledVdc_one`).

## Main results

* `cutWeight h j = h_j − h_{j+1}`, `cutPoint P i j = cumProb P i (j + 1)`.
* `occCount_sub_eq_boundary_add_cuts` (**decomposition**):
  `N_s(T) − T c = h(x₀) − h(X_T) + Σ_i Σ_{j<n−1} (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, N_i(T))`.
* `IsPoissonFamily`, `IsPoissonFamily.mem_Icc`, `abs_occCount_sub_pi_le`.
* `abs_occErrN_sub_mainTermN_le` (**n-state deterministic Anscombe**): with
  `mainTermN = Σ_i Σ_j (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, ⌊T π_i⌋)`,
  `|E_T − mainTermN| ≤ ansBoundN = O(log log T)` for every flip table; `ansBoundN_le_log`.
* `tendsto_sq_div_natLog_of_le`: such bounds are `o(√log T)`.
* `segErr_scrambledVdc_eq_sum_cutTerm`, `mainTermN_eq_levelSumN` (**level decomposition**):
  `mainTermN = Σ_{m<K} Σ_i rowTerm … m … i`, where the row term of level `m` collects, over the
  cut points `j`, the terms `w_j 1{bit m of n_i} (1{LevelInd} − {2^m c_{ij}})` of
  `segErr_scrambledVdc_eq_sum_level`, as functions of the path coins of the cut points.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-! ### Abel summation over the cut points -/

/-- The weight `h_j − h_{j+1}` of cut point `j` (the states extended by `0` beyond `n − 1`). -/
noncomputable def cutWeight (h : Fin n → ℝ) (j : ℕ) : ℝ := extendNat h j - extendNat h (j + 1)

/-- Cut point `j` of row `i`: the cumulative probability `cumProb P i (j + 1)`. -/
noncomputable def cutPoint (P : Fin n → Fin n → ℝ) (i : Fin n) (j : ℕ) : ℝ :=
  cumProb P i (j + 1)

/-- Cut points of a stochastic matrix lie in `[0, 1]`. -/
theorem cutPoint_mem_Icc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (j : ℕ) :
    cutPoint P i j ∈ Set.Icc (0 : ℝ) 1 :=
  cumProb_mem_Icc hP i (j + 1)

/-- `extendNat h k = h k` on states. -/
theorem extendNat_fin (h : Fin n → ℝ) (k : Fin n) : extendNat h k = h k := by
  unfold extendNat
  simp [k.isLt]

/-- Summation by parts over the states: if `B 0 = 0`, then
`Σ_{j<n} h_j (B_{j+1} − B_j) = h_{n−1} B_n + Σ_{j<n−1} (h_j − h_{j+1}) B_{j+1}`. -/
theorem sum_extendNat_mul_sub_eq (hn : 1 ≤ n) (h : Fin n → ℝ) (B : ℕ → ℝ) (hB : B 0 = 0) :
    ∑ j ∈ range n, extendNat h j * (B (j + 1) - B j) =
      extendNat h (n - 1) * B n + ∑ j ∈ range (n - 1), cutWeight h j * B (j + 1) := by
  have e := sum_mul_sub_eq_abel (extendNat h) B hB (n - 1)
  rw [Nat.sub_add_cancel hn] at e
  rw [e, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  rw [cutWeight]
  ring

/-- **Abel summation for one departure.** For `u ≤ 1`,
`h(step P i u) − (Ph)(i) = Σ_{j<n−1} (h_j − h_{j+1}) (1{u ≤ c_{ij}} − c_{ij})`. -/
theorem step_sub_mulVec_eq_sum_cut {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (h : Fin n → ℝ) (i : Fin n) {u : ℝ} (hu : u ≤ 1) :
    h (step P i u) - (P *ᵥ h) i = ∑ j ∈ range (n - 1),
      cutWeight h j * ((if u ≤ cutPoint P i j then 1 else 0) - cutPoint P i j) := by
  have hn : 1 ≤ n := by have := i.isLt; omega
  set B : ℕ → ℝ := fun m ↦ if (step P i u : ℕ) < m then 1 else 0 with hBdef
  set C : ℕ → ℝ := fun m ↦ cumProb P i m with hCdef
  have hB0 : B 0 = 0 := by simp [hBdef]
  have hC0 : C 0 = 0 := cumProb_zero P i
  have hBn : B n = 1 := by simp [hBdef, (step P i u).isLt]
  have hCn : C n = 1 := by
    change cumProb P i n = 1
    rw [cumProb_of_le P i le_rfl, hP.sum_eq_one i]
  -- the value as a telescoping sum
  have h1 : h (step P i u) = ∑ j ∈ range n, extendNat h j * (B (j + 1) - B j) := by
    rw [sum_eq_single (step P i u : ℕ)]
    · simp only [hBdef, Nat.lt_succ_self, ite_true, lt_irrefl, ite_false, sub_zero, mul_one]
      rw [extendNat_fin]
    · intro j _ hj
      have : B (j + 1) - B j = 0 := by
        simp only [hBdef]
        rcases lt_or_gt_of_ne hj with h' | h'
        · have h2 : ¬ (step P i u : ℕ) < j + 1 := by omega
          have h3 : ¬ (step P i u : ℕ) < j := by omega
          simp [h2, h3]
        · have h2 : (step P i u : ℕ) < j + 1 := by omega
          have h3 : (step P i u : ℕ) < j := h'
          simp [h2, h3]
      rw [this, mul_zero]
    · intro h'
      exact absurd (mem_range.2 (step P i u).isLt) h'
  have h2 : (P *ᵥ h) i = ∑ j ∈ range n, extendNat h j * (C (j + 1) - C j) := by
    change ∑ k, P i k * h k = _
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ extendNat h j * (C (j + 1) - C j)) n]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [hCdef]
    rw [cumProb_succ, extendNat_fin]
    ring
  rw [h1, h2, sum_extendNat_mul_sub_eq hn h B hB0, sum_extendNat_mul_sub_eq hn h C hC0, hBn, hCn,
    add_sub_add_left_eq_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  have hstep := step_lt_iff hP i hu (m := j + 1) (by omega)
  simp only [hBdef, hCdef, cutPoint]
  by_cases hj : u ≤ cumProb P i (j + 1)
  · have h' := hstep.2 hj
    simp only [h', hj, ite_true]
    ring
  · have h' : ¬ (step P i u : ℕ) < j + 1 := fun h' ↦ hj (hstep.1 h')
    simp only [h', hj, ite_false]
    ring

/-- **Abel summation for a stack**: the departure error of `N` points of a sequence `v ≤ 1` is
`Σ_{j<n−1} (h_j − h_{j+1}) segErr(v, c_{ij}, 0, N)`. -/
theorem sum_step_sub_eq_sum_segErr {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (h : Fin n → ℝ) (i : Fin n) {v : ℕ → ℝ} (hv : ∀ k, v k ≤ 1) (N : ℕ) :
    ∑ k ∈ range N, (h (step P i (v k)) - (P *ᵥ h) i) =
      ∑ j ∈ range (n - 1), cutWeight h j * segErr v (cutPoint P i j) 0 N := by
  rw [sum_congr rfl fun k _ ↦ step_sub_mulVec_eq_sum_cut hP h i (hv k), sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [segErr, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [zero_add]

/-- **Decomposition of the occupation error** (every flip table): if `h − Ph = 1_{s} − c`, then
`N_s(T) − T c = h(x₀) − h(X_T) + Σ_i Σ_{j<n−1} (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, N_i(T))`. -/
theorem occCount_sub_eq_boundary_add_cuts {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool) {h : Fin n → ℝ} {s : Fin n} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (T : ℕ) :
    (occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) - T * c =
      h x₀ - h (stackPath P x₀ (scrambledStack f) T) + ∑ i, ∑ j ∈ range (n - 1),
        cutWeight h j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0
          (occCount (stackPath P x₀ (scrambledStack f)) i T) := by
  rw [occCount_sub_eq_boundary_add P hh (stackPath P x₀ (scrambledStack f)) T]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  refine (departureDiscrepancy_stackDrive P h (step P) x₀ (scrambledStack f) i T).trans ?_
  exact sum_step_sub_eq_sum_segErr hP h i (fun k ↦ (scrambledVdc_mem_Icc (f i) k).2) _

/-! ### Poisson data for every target -/

/-- **Poisson data for every target**: `H t − P H t = 1_{t} − π_t` for every state `t`. -/
def IsPoissonFamily (P : Fin n → Fin n → ℝ) (H : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) : Prop :=
  ∀ t i, H t i - (P *ᵥ H t) i = (if i = t then 1 else 0) - pi t

/-- For a stochastic row, `(P g)(i)` lies between the minimum and maximum of `g`. -/
theorem mulVec_le_of_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {g : Fin n → ℝ} {a : ℝ}
    (hg : ∀ k, g k ≤ a) (i : Fin n) : (P *ᵥ g) i ≤ a := by
  change ∑ k, P i k * g k ≤ a
  calc ∑ k, P i k * g k ≤ ∑ k, P i k * a :=
        sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hg k) (hP.nonneg i k)
    _ = a := by rw [← sum_mul, hP.sum_eq_one i, one_mul]

/-- For a stochastic row, `(P g)(i) ≥ a` when `g ≥ a`. -/
theorem le_mulVec_of_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {g : Fin n → ℝ} {a : ℝ}
    (hg : ∀ k, a ≤ g k) (i : Fin n) : a ≤ (P *ᵥ g) i := by
  change a ≤ ∑ k, P i k * g k
  calc a = ∑ k, P i k * a := by rw [← sum_mul, hP.sum_eq_one i, one_mul]
    _ ≤ ∑ k, P i k * g k :=
        sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hg k) (hP.nonneg i k)

/-- **Poisson data force `π_t ∈ [0, 1]`** (at a maximiser of `H t`, `H t − P H t ≥ 0`; at a
minimiser, `≤ 0`). -/
theorem IsPoissonFamily.mem_Icc {P : Fin n → Fin n → ℝ} {H : Fin n → Fin n → ℝ}
    {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (hP : IsStochastic P) (t : Fin n) :
    pi t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨i₀, -, hmax⟩ := exists_max_image univ (H t) ⟨t, mem_univ t⟩
  obtain ⟨i₁, -, hmin⟩ := exists_min_image univ (H t) ⟨t, mem_univ t⟩
  have h0 := mulVec_le_of_le hP (fun k ↦ hmax k (mem_univ k)) i₀
  have h1 := le_mulVec_of_le hP (fun k ↦ hmin k (mem_univ k)) i₁
  have e0 := hH t i₀
  have e1 := hH t i₁
  have hi0 : (if i₀ = t then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hi1 : (0 : ℝ) ≤ if i₁ = t then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  constructor <;> linarith

/-- A bound `Σ_t Σ_i |H t i|` for all the Poisson functions. -/
noncomputable def poissonSup (H : Fin n → Fin n → ℝ) : ℝ := ∑ t, ∑ i, |H t i|

/-- `|H t i| ≤ poissonSup H`. -/
theorem abs_le_poissonSup (H : Fin n → Fin n → ℝ) (t i : Fin n) : |H t i| ≤ poissonSup H := by
  have h1 : |H t i| ≤ ∑ i', |H t i'| :=
    single_le_sum (f := fun i' ↦ |H t i'|) (fun _ _ ↦ abs_nonneg _) (mem_univ i)
  have h2 : ∑ i', |H t i'| ≤ poissonSup H :=
    single_le_sum (f := fun t' ↦ ∑ i', |H t' i'|) (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
      (mem_univ t)
  exact h1.trans h2

/-- `0 ≤ poissonSup H`. -/
theorem poissonSup_nonneg (H : Fin n → Fin n → ℝ) : 0 ≤ poissonSup H :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The constant `A = ⌈2 M (1 + n²)⌉ + 2` of the occupation bound. -/
noncomputable def anscConstN (H : Fin n → Fin n → ℝ) : ℕ :=
  ⌈2 * poissonSup H * (1 + (n : ℝ) ^ 2)⌉₊ + 2

/-- **Occupation of every state** (every flip table):
`|N_i(T) − T π_i| ≤ A (⌊log₂ T⌋ + 1) − 1`. -/
theorem abs_occCount_sub_pi_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i : Fin n) (T : ℕ) :
    |(occCount (stackPath P x₀ (scrambledStack f)) i T : ℝ) - T * pi i| ≤
      (anscConstN H : ℝ) * (Nat.log 2 T + 1) - 1 := by
  set M := poissonSup H with hM
  have hM0 : 0 ≤ M := poissonSup_nonneg H
  have h1 := abs_occCount_scrambled_sub_le hP x₀ f (h := H i) (s := i) (c := pi i) (M := M)
    (hH i) (fun k ↦ abs_le_poissonSup H i k) T
  have hV : stateVariation (H i) ≤ 2 * (n - 1 : ℕ) * M :=
    stateVariation_le fun k ↦ abs_le_poissonSup H i k
  have hL : (0 : ℝ) ≤ Nat.log 2 T := Nat.cast_nonneg _
  have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hV' : (n : ℝ) * stateVariation (H i) ≤ 2 * (n : ℝ) ^ 2 * M := by
    have := mul_le_mul_of_nonneg_left hV hn0
    have h3 : (n : ℝ) * (2 * ((n - 1 : ℕ) : ℝ) * M) ≤ 2 * (n : ℝ) ^ 2 * M := by
      have : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
  have hA : 2 * M * (1 + (n : ℝ) ^ 2) + 2 ≤ (anscConstN H : ℝ) := by
    rw [anscConstN]
    push_cast
    linarith [Nat.le_ceil (2 * M * (1 + (n : ℝ) ^ 2))]
  have hVn := stateVariation_nonneg (H i)
  calc |(occCount (stackPath P x₀ (scrambledStack f)) i T : ℝ) - T * pi i|
      ≤ 2 * M + n * stateVariation (H i) * ((Nat.log 2 T : ℝ) + 1) := h1
    _ ≤ 2 * M * (Nat.log 2 T + 1) + 2 * (n : ℝ) ^ 2 * M * (Nat.log 2 T + 1) := by
        have : 2 * M ≤ 2 * M * (Nat.log 2 T + 1) := by nlinarith
        have : n * stateVariation (H i) * ((Nat.log 2 T : ℝ) + 1) ≤
            2 * (n : ℝ) ^ 2 * M * (Nat.log 2 T + 1) :=
          mul_le_mul_of_nonneg_right hV' (by linarith)
        linarith
    _ ≤ (anscConstN H : ℝ) * (Nat.log 2 T + 1) - 1 := by nlinarith

/-! ### The deterministic Anscombe theorem -/

/-- The occupation error `N_s(T) − T π_s` of the chain driven by the scrambled stacks of `f`. -/
noncomputable def occErrN (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (s : Fin n) (T : ℕ) : ℝ :=
  occCount (stackPath P x₀ (scrambledStack f)) s T - T * pi s

/-- The deterministic indices `n_i(T) = ⌊T π_i⌋`. -/
noncomputable def chainIdxN (pi : Fin n → ℝ) (T : ℕ) (i : Fin n) : ℕ := ⌊T * pi i⌋₊

/-- **The main term**: `Σ_i Σ_{j<n−1} (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, ⌊T π_i⌋)`, the
departure discrepancies at the deterministic indices. -/
noncomputable def mainTermN (P : Fin n → Fin n → ℝ) (h : Fin n → ℝ) (pi : Fin n → ℝ)
    (f : Fin n → ℕ → ℕ → Bool) (T : ℕ) : ℝ :=
  ∑ i, ∑ j ∈ range (n - 1), cutWeight h j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0
    (chainIdxN pi T i)

/-- The total absolute weight `Σ_{j<n−1} |h_j − h_{j+1}|`. -/
noncomputable def cutWeightSum (h : Fin n → ℝ) : ℝ := ∑ j ∈ range (n - 1), |cutWeight h j|

/-- `0 ≤ cutWeightSum h`. -/
theorem cutWeightSum_nonneg (h : Fin n → ℝ) : 0 ≤ cutWeightSum h :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The Anscombe bound `2M + n W (2⌊log₂ (A (⌊log₂ T⌋ + 1))⌋ + 3)`. -/
noncomputable def ansBoundN (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) : ℝ :=
  2 * poissonSup H + n * cutWeightSum (H s) *
    (2 * (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) + 3)

/-- `n_i(T) ≤ T` (as `π_i ≤ 1`). -/
theorem chainIdxN_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {H : Fin n → Fin n → ℝ}
    {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (T : ℕ) (i : Fin n) : chainIdxN pi T i ≤ T := by
  have h1 := (hH.mem_Icc hP i).2
  have h0 := (hH.mem_Icc hP i).1
  unfold chainIdxN
  refine Nat.floor_le_of_le ?_
  nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]

/-- `n_i(T) < 2^{⌊log₂ T⌋ + 1}`. -/
theorem chainIdxN_lt_two_pow {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (T : ℕ) (i : Fin n) :
    chainIdxN pi T i < 2 ^ (Nat.log 2 T + 1) :=
  lt_of_le_of_lt (chainIdxN_le hP hH T i) (Nat.lt_pow_succ_log_self one_lt_two T)

/-- **Deterministic Anscombe theorem for n-state stack chains** (every flip table):
`|E_T − mainTermN(T)| ≤ ansBoundN = 2M + n W (2⌊log₂ (A (⌊log₂ T⌋ + 1))⌋ + 3)`. -/
theorem abs_occErrN_sub_mainTermN_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (s : Fin n) (T : ℕ) :
    |occErrN P pi x₀ f s T - mainTermN P (H s) pi f T| ≤ ansBoundN H s T := by
  have hid := occCount_sub_eq_boundary_add_cuts hP x₀ f (hH s) T
  set path := stackPath P x₀ (scrambledStack f) with hpath
  set L := (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) with hL
  have hseg : ∀ i, ∀ j ∈ range (n - 1),
      |cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
        cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i)| ≤
        |cutWeight (H s) j| * (2 * L + 3) := by
    intro i j _
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hc := cutPoint_mem_Icc hP i j
    refine (abs_segErr_sub_segErr_le (f i) hc.1 hc.2 _ _).trans ?_
    have hpi := hH.mem_Icc hP i
    have hfl : |T * pi i - (chainIdxN pi T i : ℝ)| < 1 := by
      have hy : 0 ≤ (T : ℝ) * pi i := mul_nonneg (Nat.cast_nonneg T) hpi.1
      rw [chainIdxN, abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy))]
      linarith [Nat.lt_floor_add_one ((T : ℝ) * pi i)]
    have hd := natLog_dist_le (abs_occCount_sub_pi_le hP hH x₀ f i T) hfl
    rw [← hpath] at hd
    have hd' : (Nat.log 2 (occCount path i T - chainIdxN pi T i +
        (chainIdxN pi T i - occCount path i T)) : ℝ) ≤ L := by
      rw [hL]
      exact_mod_cast hd
    linarith
  have hsum : |∑ i, ∑ j ∈ range (n - 1),
      (cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
        cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i))| ≤
      n * cutWeightSum (H s) * (2 * L + 3) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j ∈ range (n - 1),
          (cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
          cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i))|
        ≤ ∑ _i : Fin n, cutWeightSum (H s) * (2 * L + 3) := by
          refine sum_le_sum fun i _ ↦ (abs_sum_le_sum_abs _ _).trans ?_
          rw [cutWeightSum, sum_mul]
          exact sum_le_sum (hseg i)
      _ = n * cutWeightSum (H s) * (2 * L + 3) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hb : |H s x₀ - H s (path T)| ≤ 2 * poissonSup H := by
    have := abs_sub (H s x₀) (H s (path T))
    linarith [abs_le_poissonSup H s x₀, abs_le_poissonSup H s (path T)]
  have e : occErrN P pi x₀ f s T - mainTermN P (H s) pi f T =
      (H s x₀ - H s (path T)) + ∑ i, ∑ j ∈ range (n - 1),
      (cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
        cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i)) := by
    rw [occErrN, hid, mainTermN]
    simp only [sum_sub_distrib]
    ring
  rw [e, ansBoundN]
  exact (abs_add_le _ _).trans (add_le_add hb hsum)

/-- `⌊log₂ (A x)⌋ ≤ ⌊log₂ A⌋ + ⌊log₂ x⌋ + 1`. -/
theorem natLog_mul_le (A x : ℕ) : Nat.log 2 (A * x) ≤ Nat.log 2 A + Nat.log 2 x + 1 := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  refine Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by positivity) ?_)
  have h1 := Nat.lt_pow_succ_log_self one_lt_two A
  have h2 := Nat.lt_pow_succ_log_self one_lt_two x
  rw [Nat.succ_eq_add_one] at h1 h2 ⊢
  rw [show Nat.log 2 A + Nat.log 2 x + 1 + 1 = (Nat.log 2 A + 1) + (Nat.log 2 x + 1) by ring,
    pow_add]
  exact Nat.mul_lt_mul'' h1 h2

/-- The constant `C` of `ansBoundN ≤ C (⌊log₂(⌊log₂ T⌋ + 1)⌋ + 1)`. -/
noncomputable def ansConstN (H : Fin n → Fin n → ℝ) (s : Fin n) : ℝ :=
  2 * poissonSup H + n * cutWeightSum (H s) * (2 * Nat.log 2 (anscConstN H) + 5)

/-- `0 ≤ ansBoundN`. -/
theorem ansBoundN_nonneg (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) : 0 ≤ ansBoundN H s T := by
  have := poissonSup_nonneg H
  have := cutWeightSum_nonneg (H s)
  rw [ansBoundN]
  positivity

/-- `0 ≤ ansConstN`. -/
theorem ansConstN_nonneg (H : Fin n → Fin n → ℝ) (s : Fin n) : 0 ≤ ansConstN H s := by
  have := poissonSup_nonneg H
  have := cutWeightSum_nonneg (H s)
  rw [ansConstN]
  positivity

/-- **The Anscombe bound is `O(log log T)`.** -/
theorem ansBoundN_le_log (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) :
    ansBoundN H s T ≤ ansConstN H s * ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) := by
  have hmul : (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) ≤
      Nat.log 2 (anscConstN H) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by
    exact_mod_cast natLog_mul_le _ _
  have hM := poissonSup_nonneg H
  have hW := cutWeightSum_nonneg (H s)
  have hnW : 0 ≤ (n : ℝ) * cutWeightSum (H s) := mul_nonneg (Nat.cast_nonneg n) hW
  have h0 := (Nat.log 2 (anscConstN H)).cast_nonneg (α := ℝ)
  have h1 := (Nat.log 2 (Nat.log 2 T + 1)).cast_nonneg (α := ℝ)
  rw [ansBoundN, ansConstN]
  have k1 : (n : ℝ) * cutWeightSum (H s) *
      (2 * (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) + 3) ≤
      (n : ℝ) * cutWeightSum (H s) *
        (2 * (Nat.log 2 (anscConstN H) : ℝ) + 2 * Nat.log 2 (Nat.log 2 T + 1) + 5) :=
    mul_le_mul_of_nonneg_left (by linarith) hnW
  have k2 : (n : ℝ) * cutWeightSum (H s) *
      (2 * (Nat.log 2 (anscConstN H) : ℝ) + 2 * Nat.log 2 (Nat.log 2 T + 1) + 5) ≤
      (n : ℝ) * cutWeightSum (H s) * ((2 * (Nat.log 2 (anscConstN H) : ℝ) + 5) *
        ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hnW
  nlinarith

/-- **`O(log log T)` is `o(√log T)`.** If `0 ≤ b k ≤ C (⌊log₂(⌊log₂ T_k⌋ + 1)⌋ + 1)` and
`T_k → ∞`, then `b_k² / log₂ T_k → 0`. -/
theorem tendsto_sq_div_natLog_of_le {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {b : ℕ → ℝ}
    {C : ℝ} (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k, b k ≤ C * ((Nat.log 2 (Nat.log 2 (T k) + 1) : ℝ) + 1)) :
    Tendsto (fun k ↦ b k ^ 2 / Nat.log 2 (T k)) atTop (𝓝 0) := by
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hx : Tendsto (fun k ↦ Nat.log 2 (T k) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ _) hlogT
  have hlim := (tendsto_natLog_pow_six_div.comp hx).const_mul (2 * C ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by have := hb0 k; positivity) ?_ hlim
  have hev : ∀ᶠ k in atTop, 2 ≤ Nat.log 2 (T k) + 1 := hx.eventually_ge_atTop 2
  filter_upwards [hev] with k hk
  set y := (Nat.log 2 (Nat.log 2 (T k) + 1) : ℝ) + 1 with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [(Nat.log 2 (Nat.log 2 (T k) + 1)).cast_nonneg (α := ℝ)]
  have hlog : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast (show 1 ≤ Nat.log 2 (T k) by omega)
  have hy6 : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have hb2 : b k ^ 2 ≤ C ^ 2 * y ^ 6 := by
    have := pow_le_pow_left₀ (hb0 k) (hb k) 2
    rw [mul_pow] at this
    nlinarith
  simp only [Function.comp_apply]
  rw [div_le_iff₀ (by linarith), ← hy]
  have hpos : (0 : ℝ) < ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) := by positivity
  calc b k ^ 2 ≤ C ^ 2 * y ^ 6 := hb2
    _ = 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) *
        (((Nat.log 2 (T k) + 1 : ℕ) : ℝ) / 2) := by field_simp
    _ ≤ 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) * Nat.log 2 (T k) := by
        gcongr
        push_cast
        linarith

/-! ### The level decomposition -/

/-- The level-`m` term of the local discrepancy at a cut point `c` (zero if `c ≥ 1`, where the
local discrepancy vanishes). -/
noncomputable def cutTerm (c : ℝ) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  if c < 1 then coinTerm c N m e else 0

/-- The level-`m` term truncated at depth `L`. -/
noncomputable def cutTermTrunc (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) : ℝ :=
  if c < 1 then coinTermTrunc c N m L e else 0

/-- At the cut point `1` the local discrepancy of points in `[0,1]` vanishes. -/
theorem segErr_scrambledVdc_one (g : ℕ → ℕ → Bool) (N : ℕ) :
    segErr (scrambledVdc g) 1 0 N = 0 := by
  rw [segErr]
  refine sum_eq_zero fun k _ ↦ ?_
  simp only [(scrambledVdc_mem_Icc g _).2, ite_true, sub_self]

/-- **Level decomposition at a cut point in `[0,1]`** (every flip table): for `N < 2^K`,
`segErr(v, c, 0, N) = Σ_{m<K} cutTerm c N m e` with `e` the path coins of `c`. -/
theorem segErr_scrambledVdc_eq_sum_cutTerm (g : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {N K : ℕ} (hN : N < 2 ^ K) :
    segErr (scrambledVdc g) c 0 N =
      ∑ m ∈ range K, cutTerm c N m (pathCoin g (threshDigit c)) := by
  rcases hc1.lt_or_eq with hlt | heq
  · rw [segErr_scrambledVdc_eq_sum_level g hc0 hlt hN, sum_filter]
    refine sum_congr rfl fun m _ ↦ ?_
    simp only [cutTerm, hlt, ite_true, coinTerm]
  · subst heq
    rw [segErr_scrambledVdc_one]
    refine (sum_eq_zero fun m _ ↦ ?_).symm
    simp only [cutTerm, lt_irrefl, ite_false]

/-- The **row term** of level `m`: `Σ_{j<n−1} w_j · cutTerm (c_{ij}) (N_i) m (e_{ij})`, for cut
points `cp`, weights `w`, indices `N` and coin sequences `e i j`. -/
noncomputable def rowTerm (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) : ℝ :=
  ∑ j ∈ range (n - 1), w j * cutTerm (cp i j) (N i) m (e i j)

/-- The row term truncated at depth `L`. -/
noncomputable def rowTermTrunc (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) : ℝ :=
  ∑ j ∈ range (n - 1), w j * cutTermTrunc (cp i j) (N i) m L (e i j)

/-- The **level sum** `Σ_{m<K} Σ_i rowTerm … m … i`. -/
noncomputable def levelSumN (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (K : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : ℝ :=
  ∑ m ∈ range K, ∑ i, rowTerm w cp N m e i

/-- **Level decomposition of the main term** (every flip table): for `n_i(T) < 2^K`,
`mainTermN = levelSumN` with the path coins of the cut points of every row. -/
theorem mainTermN_eq_levelSumN {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (h : Fin n → ℝ)
    (pi : Fin n → ℝ) (f : Fin n → ℕ → ℕ → Bool) (T : ℕ) {K : ℕ}
    (hK : ∀ i, chainIdxN pi T i < 2 ^ K) :
    mainTermN P h pi f T = levelSumN (cutWeight h) (cutPoint P) (chainIdxN pi T) K
      (fun i j ↦ pathCoin (f i) (threshDigit (cutPoint P i j))) := by
  rw [mainTermN, levelSumN]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [rowTerm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  have hc := cutPoint_mem_Icc hP i j
  rw [segErr_scrambledVdc_eq_sum_cutTerm (f i) hc.1 hc.2 (hK i), mul_sum]

end RQMCMarkov.ScrambledStacks
