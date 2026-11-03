/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.Driving

/-! # The discrepancy-to-occupation inequality (post #3)

Copied from `RQMCMarkov/MarkovDriving` (namespace and imports renamed).

Post #3 ranks the ways of driving a chain by how fast the occupation frequencies `N_s(T)/T` and
the empirical transition matrix converge: MC at `O(1/√T)`, per-state low-discrepancy stacks
"faster than `O(1/√T)`" (`O(log T / T)`), rotors at `O(1/T)`. All three rates come from one
**deterministic** inequality, valid for *any* path `x : ℕ → S`, proved here by telescoping
Poisson's equation (Meyn and Tweedie, Ch. 17; Holroyd and Propp 2010 use the same device).

For a test function `g`, the **departure discrepancy** of state `i` up to time `T` is
`D_i(g, T) = Σ_{t < T, x t = i} (g(x_{t+1}) − (Pg)(i))`: the error of the departures from `i`
as a sample of the row `P(i, ·)`. If `h − Ph = f − c` then

`Σ_{t<T} f(x_t) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`        (`sum_sub_eq_boundary_add`),

so for `f = 1_{s}` and `c = π_s` (`occCount_sub_eq_boundary_add`, `abs_occCount_sub_le`):

`|N_s(T) − T π_s| ≤ 2‖h‖∞ + Σ_i |D_i(h, T)|`  (occupation error ≤ boundary + departure
discrepancies).

The transition counts satisfy the exact identity `N_ij(T) − p_ij N_i(T) = D_i(1_{j}, T)`
(`transCount_sub_eq_departureDiscrepancy`), and hence (`abs_transCount_sub_le`)
`|N_ij(T) − T π_i p_ij| ≤ |D_i(1_{j}, T)| + p_ij (2‖h‖∞ + Σ_k |D_k(h, T)|)`.

For a path built from per-state stacks (`stackDrive`, which covers the QMC stacks of post #3
and the rotor-router), the departures from `i` are the first `N_i(T)` entries of stack `i`
(`sum_filter_occCount_eq`, `departureDiscrepancy_stackDrive`, `transCount_stackDrive`), so the
departure discrepancy is an ordinary one-dimensional sampling error, bounded in `StackBound`
(van der Corput stacks), `RotorRouter` (rotors) and `MCRate` (i.i.d. stacks).

The sup-norm `‖h‖∞` enters through any bound `M` with `∀ i, |h i| ≤ M`.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The **departure discrepancy** of state `i` for the test function `g` up to time `T`:
`Σ_{t < T, x t = i} (g (x (t+1)) − (Pg)(i))`. -/
noncomputable def departureDiscrepancy (P : Matrix S S ℝ) (g : S → ℝ) (x : ℕ → S) (i : S)
    (T : ℕ) : ℝ :=
  ∑ t ∈ (range T).filter (fun t => x t = i), (g (x (t + 1)) - (P *ᵥ g) i)

/-- **The telescoping identity.** If `h − Ph = f − c`, then along any path
`Σ_{t<T} f(x_t) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`. -/
theorem sum_sub_eq_boundary_add (P : Matrix S S ℝ) {f h : S → ℝ} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = f i - c) (x : ℕ → S) (T : ℕ) :
    ∑ t ∈ range T, f (x t) - T * c =
      h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T := by
  have e1 : ∑ t ∈ range T, f (x t) - T * c = ∑ t ∈ range T, (h (x t) - (P *ᵥ h) (x t)) := by
    rw [← card_range T, ← nsmul_eq_mul, ← sum_const, card_range, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => (hh (x t)).symm
  have e2 : ∑ t ∈ range T, (h (x t) - (P *ᵥ h) (x t)) =
      ∑ t ∈ range T, (h (x t) - h (x (t + 1))) +
        ∑ t ∈ range T, (h (x (t + 1)) - (P *ᵥ h) (x t)) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  have e3 : ∑ t ∈ range T, (h (x (t + 1)) - (P *ᵥ h) (x t)) =
      ∑ i, departureDiscrepancy P h x i T := by
    rw [← sum_fiberwise (range T) x]
    refine sum_congr rfl fun i _ => sum_congr rfl fun t ht => ?_
    rw [(mem_filter.1 ht).2]
  rw [e1, e2, e3, sum_range_sub' (fun t => h (x t)) T]

omit [Fintype S] in
/-- `Σ_{t<T} 1_{s}(x_t) = N_s(T)`. -/
theorem sum_indicator_eq_occCount (x : ℕ → S) (s : S) (T : ℕ) :
    ∑ t ∈ range T, (if x t = s then (1 : ℝ) else 0) = occCount x s T := by
  rw [sum_boole]
  rfl

/-- **Occupation identity.** If `h − Ph = 1_{s} − c` (Poisson's equation, with `c = π_s`), then
along any path `N_s(T) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`. -/
theorem occCount_sub_eq_boundary_add (P : Matrix S S ℝ) {h : S → ℝ} {s : S} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (x : ℕ → S) (T : ℕ) :
    (occCount x s T : ℝ) - T * c = h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T := by
  rw [← sum_indicator_eq_occCount]
  exact sum_sub_eq_boundary_add P hh x T

/-- **The discrepancy-to-occupation inequality** (the backbone of post #3's rates): for any path,
`|N_s(T) − T c| ≤ 2M + Σ_i |D_i(h, T)|`, where `h − Ph = 1_{s} − c` and `|h| ≤ M`. -/
theorem abs_occCount_sub_le (P : Matrix S S ℝ) {h : S → ℝ} {s : S} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (x : ℕ → S) (T : ℕ) :
    |(occCount x s T : ℝ) - T * c| ≤ 2 * M + ∑ i, |departureDiscrepancy P h x i T| := by
  rw [occCount_sub_eq_boundary_add P hh x T]
  have hb : |h (x 0) - h (x T)| ≤ 2 * M := by
    have := abs_sub (h (x 0)) (h (x T))
    linarith [hM (x 0), hM (x T)]
  calc |h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T|
      ≤ |h (x 0) - h (x T)| + |∑ i, departureDiscrepancy P h x i T| := abs_add_le _ _
    _ ≤ 2 * M + ∑ i, |departureDiscrepancy P h x i T| :=
        add_le_add hb (abs_sum_le_sum_abs _ _)

/-- `(P 1_{j})(i) = P i j`. -/
theorem mulVec_indicator (P : Matrix S S ℝ) (i j : S) :
    (P *ᵥ fun k => if k = j then (1 : ℝ) else 0) i = P i j := by
  simp only [mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ,
    ite_true]

/-- **Transition identity.** `N_ij(T) − p_ij N_i(T)` is exactly the departure discrepancy of `i`
for the indicator `1_{j}`. -/
theorem transCount_sub_eq_departureDiscrepancy (P : Matrix S S ℝ) (x : ℕ → S) (i j : S)
    (T : ℕ) : (transCount x i j T : ℝ) - P i j * occCount x i T =
      departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T := by
  unfold departureDiscrepancy
  rw [mulVec_indicator, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_comm (P i j), sum_boole,
    filter_filter]
  rfl

/-- **Transition counts against the target `T π_i p_ij`** (post #3's "number of each
transition"): `|N_ij(T) − T c p_ij| ≤ |D_i(1_{j}, T)| + p_ij (2M + Σ_k |D_k(h, T)|)`, where
`h − Ph = 1_{i} − c` and `|h| ≤ M`. -/
theorem abs_transCount_sub_le (P : Matrix S S ℝ) (hP0 : ∀ i j, 0 ≤ P i j) {h : S → ℝ} {i : S}
    {c M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (x : ℕ → S) (j : S) (T : ℕ) :
    |(transCount x i j T : ℝ) - T * c * P i j| ≤
      |departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T| +
        P i j * (2 * M + ∑ k, |departureDiscrepancy P h x k T|) := by
  have e : (transCount x i j T : ℝ) - T * c * P i j =
      departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T +
        P i j * ((occCount x i T : ℝ) - T * c) := by
    rw [← transCount_sub_eq_departureDiscrepancy]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg (hP0 i j)]
  exact mul_le_mul_of_nonneg_left (abs_occCount_sub_le P hh hM x T) (hP0 i j)

omit [Fintype S] in
/-- **Departures are read off in order.** Summing over the visits `t < T` to `i` a function of
the visit index `N_i(t)` is summing over the first `N_i(T)` indices. -/
theorem sum_filter_occCount_eq {R : Type*} [AddCommMonoid R] (x : ℕ → S) (i : S) (φ : ℕ → R)
    (T : ℕ) : ∑ t ∈ (range T).filter (fun t => x t = i), φ (occCount x i t) =
      ∑ k ∈ range (occCount x i T), φ k := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [range_add_one, filter_insert, occCount_succ]
    by_cases hT : x T = i
    · have hnot : T ∉ (range T).filter (fun t => x t = i) := fun hm =>
        lt_irrefl T (mem_range.1 (mem_filter.1 hm).1)
      simp only [hT, ite_true]
      rw [sum_insert hnot, ih, sum_range_succ, add_comm]
    · simp only [hT, ite_false, add_zero]
      exact ih

omit [Fintype S] in
/-- In a stack path, the `t`-th transition out of `i` uses entry `N_i(t)` of stack `i`. -/
theorem stackDrive_succ_of_eq {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) {i : S}
    {t : ℕ} (ht : stackDrive G x₀ v t = i) :
    stackDrive G x₀ v (t + 1) = G i (v i (occCount (stackDrive G x₀ v) i t)) := by
  rw [stackDrive_succ]
  unfold departureIndex
  rw [ht]

/-- **Departure discrepancy of a stack path**: the departures from `i` up to `T` are
`G i (v i k)`, `k < N_i(T)`, so `D_i(g, T) = Σ_{k < N_i(T)} (g(G i (v i k)) − (Pg)(i))`. -/
theorem departureDiscrepancy_stackDrive {α : Type*} (P : Matrix S S ℝ) (g : S → ℝ)
    (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (i : S) (T : ℕ) :
    departureDiscrepancy P g (stackDrive G x₀ v) i T =
      ∑ k ∈ range (occCount (stackDrive G x₀ v) i T), (g (G i (v i k)) - (P *ᵥ g) i) := by
  unfold departureDiscrepancy
  rw [← sum_filter_occCount_eq (stackDrive G x₀ v) i
    (fun k => g (G i (v i k)) - (P *ᵥ g) i) T]
  refine sum_congr rfl fun t ht => ?_
  rw [stackDrive_succ_of_eq G x₀ v (mem_filter.1 ht).2]

omit [Fintype S] in
/-- **Transition counts of a stack path**: `N_ij(T) = #{k < N_i(T) : G i (v i k) = j}`. -/
theorem transCount_stackDrive {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (i j : S)
    (T : ℕ) : transCount (stackDrive G x₀ v) i j T =
      ((range (occCount (stackDrive G x₀ v) i T)).filter fun k => G i (v i k) = j).card := by
  have h1 := sum_filter_occCount_eq (stackDrive G x₀ v) i
    (fun k => if G i (v i k) = j then 1 else 0) T
  simp only [sum_boole, Nat.cast_id] at h1
  have h2 : ∑ t ∈ (range T).filter (fun t => stackDrive G x₀ v t = i),
      (if G i (v i (occCount (stackDrive G x₀ v) i t)) = j then 1 else 0) =
      ∑ t ∈ (range T).filter (fun t => stackDrive G x₀ v t = i),
      (if stackDrive G x₀ v (t + 1) = j then (1 : ℕ) else 0) :=
    sum_congr rfl fun t ht => by rw [stackDrive_succ_of_eq G x₀ v (mem_filter.1 ht).2]
  simp only [sum_boole, Nat.cast_id, filter_filter] at h2
  unfold transCount
  rw [← h1, ← h2, filter_filter]

end RQMCMarkov.ScrambledStacks
