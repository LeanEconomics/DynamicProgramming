/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackNet

/-!
# Two-state stack chains: the error is a sum of two local discrepancies (post #3)

Post #3, codes (ii) and (iii), two-state chain. Let state `0` leave to `1` iff its stack point
exceeds `c₀ = p₀₀`, and state `1` leave to `0` iff its stack point is `≤ c₁ = p₁₀`. The chain
alternates between `0→1` and `1→0` transitions, so their numbers differ by at most one. With
`N_i(T)` the occupation times and `D_i(N) = #{k < N : v_i(k) ≤ c_i} − N c_i` the local
discrepancies of the two stacks, this gives, for EVERY pair of stacks with values in `[0,1]`,

  `|q (N₀(T) − T π₀) − D₀(N₀(T)) − D₁(N₁(T))| ≤ 1`,  `q = p₀₁ + p₁₀`, `π₀ = p₁₀ / q`.

For scrambled van der Corput stacks (every flip table) the `D_i` are `O(log)` and vary by
`O(log L)` over segments of length `L` (`StackNet`), so the random indices `N_i(T)` may be
replaced by the deterministic `n_i(T) = ⌊T π_i⌋` at a cost `O(log log T)`: a deterministic
Anscombe theorem (here in the form `O(log log T)`, with the logarithm of `⌊log₂ T⌋ + 1`; we
use the segment lemma `abs_segErr_scrambledVdc_log_le` of `StackNet`).

## Main results

* `step_two_eq_zero_iff`: in a two-state chain, `step P i u = 0 ↔ u ≤ p_{i0}` for `u ∈ [0,1]`.
* `abs_two_state_identity`: the identity above, for any stacks in `[0,1]`.
* `abs_occErr_le`: `|N₀(T) − T π₀| ≤ (2⌊log₂ T⌋ + 3)/q` (scrambled stacks, every flip table).
* `abs_segErr_sub_segErr_le`: `|D(N) − D(n)| ≤ 2⌊log₂ |N − n|⌋ + 3` (every flip table).
* `piZero`, `piOne`, `occErr P x₀ f T = N₀(T) − T π₀`, `mainTerm`, `anscConst`, `anscBound`.
* `abs_occErr_sub_mainTerm_le` (**deterministic Anscombe**): with
  `mainTerm = (D₀(⌊Tπ₀⌋) + D₁(⌊Tπ₁⌋))/q`,
  `|N₀(T) − T π₀ − mainTerm| ≤ anscBound P T = (7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q`,
  `A = ⌈3/q⌉ + 1`, for every flip table.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset

/-- In a two-state chain the update goes to state `0` iff `u ≤ p_{i0}` (for `u ∈ [0,1]`). -/
theorem step_two_eq_zero_iff {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (i : Fin 2) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : step P i u = 0 ↔ u ≤ P i 0 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h := step_zero hP.nonneg i
    exact ⟨fun _ ↦ hP.nonneg i 0, fun _ ↦ Fin.ext h⟩
  · have h := step_eq_iff hP i 0 ⟨hpos, hu.2⟩
    have h1 : cumProb P i ((0 : Fin 2) : ℕ) = 0 := cumProb_zero P i
    have h2 : cumProb P i (((0 : Fin 2) : ℕ) + 1) = P i 0 := by
      rw [cumProb_succ, h1, zero_add]
    rw [h1, h2] at h
    exact h.trans ⟨fun h' ↦ h'.2, fun h' ↦ ⟨hpos, h'⟩⟩

/-- The local discrepancy `D(N) = #{k < N : v k ≤ c} − N c`, as `segErr v c 0 N`. -/
theorem segErr_zero_eq_card (v : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    segErr v c 0 N = (((range N).filter fun k ↦ v k ≤ c).card : ℝ) - N * c := by
  rw [segErr_eq_card]
  simp only [zero_add]

/-- **The two-state identity.** For any stacks with values in `[0,1]`,
`|q (N₀ − T π₀) − D₀(N₀) − D₁(N₁)| ≤ 1`, written as `|q N₀ − T p₁₀ − D₀ − D₁| ≤ 1`. -/
theorem abs_two_state_identity {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    {v : Fin 2 → ℕ → ℝ} (hv : ∀ i k, v i k ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    |(P 0 1 + P 1 0) * occCount (stackPath P x₀ v) 0 T - T * P 1 0 -
        segErr (v 0) (P 0 0) 0 (occCount (stackPath P x₀ v) 0 T) -
        segErr (v 1) (P 1 0) 0 (occCount (stackPath P x₀ v) 1 T)| ≤ 1 := by
  classical
  set x := stackPath P x₀ v with hx
  set N0 := occCount x 0 T with hN0
  set N1 := occCount x 1 T with hN1
  have hsum : N0 + N1 = T := by
    have := sum_occCount x T
    rwa [Fin.sum_univ_two] at this
  have hflow := abs_flowBalance_le x 0 T
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hflow
  have h01 : transCount x 0 1 T = N0 - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card := by
    rw [hx, transCount_stackDrive]
    have e : ((range N0).filter fun k ↦ step P 0 (v 0 k) = 1) =
        (range N0).filter fun k ↦ ¬ v 0 k ≤ P 0 0 := by
      refine filter_congr fun k _ ↦ ?_
      rw [← step_two_eq_zero_iff hP 0 (hv 0 k)]
      constructor
      · intro h h0
        rw [h0] at h
        exact absurd h (by decide)
      · intro h
        rcases Fin.exists_fin_two.1 ⟨step P 0 (v 0 k), rfl⟩ with h' | h'
        · exact absurd h' h
        · exact h'
    rw [e, filter_not, card_sdiff_of_subset (filter_subset _ _), card_range]
  have h10 : transCount x 1 0 T = ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card := by
    rw [hx, transCount_stackDrive]
    congr 1
    exact filter_congr fun k _ ↦ step_two_eq_zero_iff hP 1 (hv 1 k)
  have hle : ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card ≤ N0 :=
    (card_filter_le _ _).trans (card_range N0).le
  rw [h01, h10] at hflow
  rw [segErr_zero_eq_card, segErr_zero_eq_card]
  have hT : (T : ℝ) = N0 + N1 := by exact_mod_cast hsum.symm
  have hrow : P 0 0 + P 0 1 = 1 := by
    have := hP.sum_eq_one 0
    rwa [Fin.sum_univ_two] at this
  have hflow' : |((N0 : ℤ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card) -
      ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card| ≤ 1 := by
    have e : ((N0 - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card : ℕ) : ℤ) =
        (N0 : ℤ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card := Nat.cast_sub hle
    simpa [e] using hflow
  have hflowR : |((N0 : ℝ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card) -
      ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card| ≤ 1 := by
    exact_mod_cast hflow'
  rw [hT]
  have e : (P 0 1 + P 1 0) * N0 - (N0 + N1) * P 1 0 -
      (((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card - N0 * P 0 0) -
      (((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card - N1 * P 1 0) =
      ((N0 : ℝ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card) -
        ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card := by
    have : P 0 1 = 1 - P 0 0 := by linarith
    rw [this]
    ring
  rw [e]
  exact hflowR

/-- The stationary probability `π₀ = p₁₀ / (p₀₁ + p₁₀)` of a two-state chain. -/
noncomputable def piZero (P : Fin 2 → Fin 2 → ℝ) : ℝ := P 1 0 / (P 0 1 + P 1 0)

/-- The stationary probability `π₁ = p₀₁ / (p₀₁ + p₁₀)` of a two-state chain. -/
noncomputable def piOne (P : Fin 2 → Fin 2 → ℝ) : ℝ := P 0 1 / (P 0 1 + P 1 0)

/-- The occupation error `N₀(T) − T π₀` of the chain driven by scrambled stacks with flip
table `f`. -/
noncomputable def occErr (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool)
    (T : ℕ) : ℝ :=
  occCount (stackPath P x₀ (scrambledStack f)) 0 T - T * piZero P

/-- The main term `(D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋)) / q`: the local discrepancies of the two stacks at
deterministic indices. -/
noncomputable def mainTerm (P : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) : ℝ :=
  (segErr (scrambledStack f 0) (P 0 0) 0 ⌊T * piZero P⌋₊ +
    segErr (scrambledStack f 1) (P 1 0) 0 ⌊T * piOne P⌋₊) / (P 0 1 + P 1 0)

/-- The constant `A = ⌈3/q⌉ + 1` of the Anscombe bound. -/
noncomputable def anscConst (P : Fin 2 → Fin 2 → ℝ) : ℕ := ⌈3 / (P 0 1 + P 1 0)⌉₊ + 1

/-- The Anscombe bound `(7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q`. -/
noncomputable def anscBound (P : Fin 2 → Fin 2 → ℝ) (T : ℕ) : ℝ :=
  (7 + 4 * (Nat.log 2 (anscConst P * (Nat.log 2 T + 1)) : ℝ)) / (P 0 1 + P 1 0)

/-- Variation of the local discrepancy of a scrambled van der Corput sequence between two
indices: `|D(N) − D(n)| ≤ 2⌊log₂ |N − n|⌋ + 3`. -/
theorem abs_segErr_sub_segErr_le (g : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (N n : ℕ) :
    |segErr (scrambledVdc g) c 0 N - segErr (scrambledVdc g) c 0 n| ≤
      2 * (Nat.log 2 (N - n + (n - N)) : ℝ) + 3 := by
  rcases le_total n N with h | h
  · have e : N = n + (N - n) := by omega
    have := abs_segErr_scrambledVdc_log_le g hc0 hc1 n (N - n)
    rw [e, segErr_add, zero_add, add_sub_cancel_left, show n + (N - n) - n = N - n by omega,
      show n - (n + (N - n)) = 0 by omega, add_zero]
    exact this
  · have e : n = N + (n - N) := by omega
    have := abs_segErr_scrambledVdc_log_le g hc0 hc1 N (n - N)
    rw [e, segErr_add, zero_add, sub_add_cancel_left, abs_neg,
      show N - (N + (n - N)) = 0 by omega, zero_add, show N + (n - N) - N = n - N by omega]
    exact this

/-- `q = p₀₁ + p₁₀` and the stationary identities. -/
theorem piZero_add_piOne {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) :
    piZero P + piOne P = 1 := by
  rw [piZero, piOne, ← add_div, add_comm, div_self hq.ne']

/-- **QMC rate for the two-state stack chain** (every flip table):
`|N₀(T) − T π₀| ≤ (2⌊log₂ T⌋ + 3)/q`. -/
theorem abs_occErr_le {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (hq : 0 < P 0 1 + P 1 0)
    (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    |occErr P x₀ f T| ≤ (2 * (Nat.log 2 T : ℝ) + 3) / (P 0 1 + P 1 0) := by
  have hv : ∀ i k, scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 := scrambledStack_mem_Icc f
  have hid := abs_two_state_identity hP x₀ hv T
  set N0 := occCount (stackPath P x₀ (scrambledStack f)) 0 T
  set N1 := occCount (stackPath P x₀ (scrambledStack f)) 1 T
  have hsum : N0 + N1 = T := by
    have := sum_occCount (stackPath P x₀ (scrambledStack f)) T
    rwa [Fin.sum_univ_two] at this
  have hc00 := hP.nonneg 0 0
  have hc01 : P 0 0 ≤ 1 := by
    have := hP.sum_eq_one 0
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 0 1]
  have hc10 := hP.nonneg 1 0
  have hc11 : P 1 0 ≤ 1 := by
    have := hP.sum_eq_one 1
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 1 1]
  have h0 := abs_segErr_scrambledVdc_zero_le (f 0) hc00 hc01 N0
  have h1 := abs_segErr_scrambledVdc_zero_le (f 1) hc10 hc11 N1
  have hl0 : (Nat.log 2 N0 : ℝ) ≤ Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have hl1 : (Nat.log 2 N1 : ℝ) ≤ Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have e0 : scrambledStack f 0 = scrambledVdc (f 0) := rfl
  have e1 : scrambledStack f 1 = scrambledVdc (f 1) := rfl
  rw [e0, e1] at hid
  have hkey : (P 0 1 + P 1 0) * occErr P x₀ f T =
      (P 0 1 + P 1 0) * N0 - T * P 1 0 := by
    rw [occErr, piZero]
    field_simp
    rfl
  have hm : |occErr P x₀ f T| * (P 0 1 + P 1 0) = |(P 0 1 + P 1 0) * occErr P x₀ f T| := by
    rw [abs_mul, abs_of_pos hq, mul_comm]
  rw [le_div_iff₀ hq, hm, hkey]
  have := abs_sub_abs_le_abs_sub ((P 0 1 + P 1 0) * N0 - T * P 1 0)
    (segErr (scrambledVdc (f 0)) (P 0 0) 0 N0 + segErr (scrambledVdc (f 1)) (P 1 0) 0 N1)
  have e : (P 0 1 + P 1 0) * N0 - T * P 1 0 -
      (segErr (scrambledVdc (f 0)) (P 0 0) 0 N0 + segErr (scrambledVdc (f 1)) (P 1 0) 0 N1) =
      (P 0 1 + P 1 0) * N0 - T * P 1 0 - segErr (scrambledVdc (f 0)) (P 0 0) 0 N0 -
        segErr (scrambledVdc (f 1)) (P 1 0) 0 N1 := by ring
  rw [e] at this
  have habs := abs_add_le (segErr (scrambledVdc (f 0)) (P 0 0) 0 N0)
    (segErr (scrambledVdc (f 1)) (P 1 0) 0 N1)
  linarith

/-- A natural number within real distance `R ≤ A (⌊log₂ T⌋ + 1)` of a real point: the
logarithm of the distance is controlled. -/
theorem natLog_dist_le {N n A T : ℕ} {r : ℝ} (hN : |(N : ℝ) - r| ≤ (A : ℝ) * (Nat.log 2 T + 1) - 1)
    (hn : |r - n| < 1) : Nat.log 2 (N - n + (n - N)) ≤ Nat.log 2 (A * (Nat.log 2 T + 1)) := by
  refine Nat.log_mono_right ?_
  have hd : ((N - n + (n - N) : ℕ) : ℝ) = |(N : ℝ) - n| := by
    rcases le_total n N with h | h
    · rw [show N - n + (n - N) = N - n by omega, Nat.cast_sub h,
        abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ N - n by omega))]
    · rw [show N - n + (n - N) = n - N by omega, Nat.cast_sub h, abs_sub_comm,
        abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ n - N by omega))]
  have h1 : |(N : ℝ) - n| ≤ |(N : ℝ) - r| + |r - n| := abs_sub_le _ _ _
  have h2 : ((N - n + (n - N) : ℕ) : ℝ) ≤ ((A * (Nat.log 2 T + 1) : ℕ) : ℝ) := by
    rw [hd]
    push_cast
    linarith
  exact_mod_cast h2

/-- **Deterministic Anscombe theorem for the two-state stack chain** (every flip table). The
occupation error is the main term `(D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋))/q` up to
`(7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q = O(log log T)`. -/
theorem abs_occErr_sub_mainTerm_le {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P)
    (hq : 0 < P 0 1 + P 1 0) (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    |occErr P x₀ f T - mainTerm P f T| ≤ anscBound P T := by
  have hv : ∀ i k, scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 := scrambledStack_mem_Icc f
  have hid := abs_two_state_identity hP x₀ hv T
  have hocc := abs_occErr_le hP hq x₀ f T
  have e0 : scrambledStack f 0 = scrambledVdc (f 0) := rfl
  have e1 : scrambledStack f 1 = scrambledVdc (f 1) := rfl
  have hz : (P 0 1 + P 1 0) * (T * piZero P) = T * P 1 0 := by
    rw [piZero]
    field_simp
  have hmt : (P 0 1 + P 1 0) * mainTerm P f T =
      segErr (scrambledVdc (f 0)) (P 0 0) 0 ⌊T * piZero P⌋₊ +
        segErr (scrambledVdc (f 1)) (P 1 0) 0 ⌊T * piOne P⌋₊ := by
    rw [mainTerm, e0, e1]
    field_simp
  have hkey : (P 0 1 + P 1 0) * (occErr P x₀ f T - mainTerm P f T) =
      ((P 0 1 + P 1 0) * occCount (stackPath P x₀ (scrambledStack f)) 0 T - T * P 1 0 -
        segErr (scrambledVdc (f 0)) (P 0 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 0 T)
        - segErr (scrambledVdc (f 1)) (P 1 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 1 T))
      + (segErr (scrambledVdc (f 0)) (P 0 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 0 T)
        - segErr (scrambledVdc (f 0)) (P 0 0) 0 ⌊T * piZero P⌋₊)
      + (segErr (scrambledVdc (f 1)) (P 1 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 1 T)
        - segErr (scrambledVdc (f 1)) (P 1 0) 0 ⌊T * piOne P⌋₊) := by
    rw [mul_sub, hmt, occErr, mul_sub, hz]
    ring
  set N0 := occCount (stackPath P x₀ (scrambledStack f)) 0 T with hN0
  set N1 := occCount (stackPath P x₀ (scrambledStack f)) 1 T with hN1
  set n0 := ⌊T * piZero P⌋₊ with hn0
  set n1 := ⌊T * piOne P⌋₊ with hn1
  have hsum : N0 + N1 = T := by
    have := sum_occCount (stackPath P x₀ (scrambledStack f)) T
    rwa [Fin.sum_univ_two] at this
  have hpz : 0 ≤ piZero P := div_nonneg (hP.nonneg 1 0) hq.le
  have hpo : 0 ≤ piOne P := div_nonneg (hP.nonneg 0 1) hq.le
  have hc00 := hP.nonneg 0 0
  have hc01 : P 0 0 ≤ 1 := by
    have := hP.sum_eq_one 0
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 0 1]
  have hc10 := hP.nonneg 1 0
  have hc11 : P 1 0 ≤ 1 := by
    have := hP.sum_eq_one 1
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 1 1]
  -- the constant
  set A := anscConst P with hA
  have hAge : 3 / (P 0 1 + P 1 0) + 1 ≤ (A : ℝ) := by
    rw [hA, anscConst]
    push_cast
    linarith [Nat.le_ceil (3 / (P 0 1 + P 1 0))]
  have hlogT : (0 : ℝ) ≤ Nat.log 2 T := Nat.cast_nonneg _
  have hR : (2 * (Nat.log 2 T : ℝ) + 3) / (P 0 1 + P 1 0) ≤
      (A : ℝ) * (Nat.log 2 T + 1) - 1 := by
    have h1 : (2 * (Nat.log 2 T : ℝ) + 3) / (P 0 1 + P 1 0) ≤
        3 / (P 0 1 + P 1 0) * (Nat.log 2 T + 1) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq]
      linarith
    nlinarith
  -- the two occupation errors
  have hN0r : |(N0 : ℝ) - T * piZero P| ≤ (A : ℝ) * (Nat.log 2 T + 1) - 1 := hocc.trans hR
  have hN1r : |(N1 : ℝ) - T * piOne P| ≤ (A : ℝ) * (Nat.log 2 T + 1) - 1 := by
    have e : (N1 : ℝ) - T * piOne P = -((N0 : ℝ) - T * piZero P) := by
      have hT : (T : ℝ) = N0 + N1 := by exact_mod_cast hsum.symm
      have h1 := piZero_add_piOne hq
      rw [hT]
      linear_combination (-((N0 : ℝ) + N1)) * h1
    rw [e, abs_neg]
    exact hN0r
  have hfl : ∀ y : ℝ, 0 ≤ y → |y - ⌊y⌋₊| < 1 := fun y hy ↦ by
    rw [abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy))]
    linarith [Nat.lt_floor_add_one y]
  have hL0 := natLog_dist_le hN0r (hfl _ (mul_nonneg (Nat.cast_nonneg T) hpz))
  have hL1 := natLog_dist_le hN1r (hfl _ (mul_nonneg (Nat.cast_nonneg T) hpo))
  have hd0 := abs_segErr_sub_segErr_le (f 0) hc00 hc01 N0 n0
  have hd1 := abs_segErr_sub_segErr_le (f 1) hc10 hc11 N1 n1
  have hL0' : (Nat.log 2 (N0 - n0 + (n0 - N0)) : ℝ) ≤ Nat.log 2 (A * (Nat.log 2 T + 1)) := by
    exact_mod_cast hL0
  have hL1' : (Nat.log 2 (N1 - n1 + (n1 - N1)) : ℝ) ≤ Nat.log 2 (A * (Nat.log 2 T + 1)) := by
    exact_mod_cast hL1
  rw [e0, e1] at hid
  -- assemble
  rw [anscBound, le_div_iff₀ hq]
  have hm : |occErr P x₀ f T - mainTerm P f T| * (P 0 1 + P 1 0) =
      |(P 0 1 + P 1 0) * (occErr P x₀ f T - mainTerm P f T)| := by
    rw [abs_mul, abs_of_pos hq, mul_comm]
  rw [hm, hkey]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  linarith

end RQMCMarkov.ScrambledStacks
