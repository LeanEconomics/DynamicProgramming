/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.OccupationDiscrepancy
import MarkovDriving.OccupationPoisson

/-! # Rotor-router walks: `O(1/T)` occupation error (post #3; Holroyd and Propp 2010)

Post #3: "A rotor is a per-state stack, but instead of a low-discrepancy sequence, each state's
stack is a fixed cycle of next states … The `k`-th departure from state `i` goes to entry `k` of
`i`'s cycle … the error in occupation frequencies is `O(1/T)`, better than QMC's
`O(log T / T)` (Holroyd and Propp, 2010)."

**Setting.** Each state `i` has a cycle of length `L i > 0`, given by its entries
`c i 0, …, c i (L i − 1)`, in which `j` appears exactly `p_ij L i` times (`IsRotorCycle`; this
needs rational `P`, and is a hypothesis). The rotor walk with offsets `θ` (`rotorWalk`) sends
the `k`-th departure from `i` to `c i ((θ i + k) mod L i)`; `θ = 0` is the deterministic rotor
of post #3, a random `θ` is its "randomized rotor-router (each state starts at a random point
of its cycle)". The walk is the stack representation with stacks of next states
(`stackDrive (fun _ j ↦ j)`). The balance of every *stretch* of the cycle, mentioned in post
#3, is not needed for the bounds below: only the counts over a full cycle are used.

**Results.**
* `rotorWalk_succ`, `rotorWalk_shift` (the walk after time `τ` is the rotor walk started from
  the current rotor state: the future depends only on the current state and rotor positions),
  `rotorWalk_congr_mod`.
* `sum_range_eq_sum_range_mod`: partial sums of a periodic sequence with zero full-period sum
  reduce to the last partial cycle; `sum_cycle_eq` (a full cycle samples `P(i, ·)` exactly).
* `departureDiscrepancy_rotorWalk_eq`: `D_i(g, T)` is the sum over the last, incomplete cycle;
  `abs_departureDiscrepancy_rotorWalk_le`, `abs_departureDiscrepancy_rotorWalk_le_two_mul`:
  `|D_i(g, T)| ≤ 2 (L i − 1) ‖g‖∞`, bounded in `T`.
* `abs_transCount_rotorWalk_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ L i − 1 < L i`;
  `transCount_rotorWalk_eq_of_dvd`: **exact** counts `N_ij(T) = p_ij N_i(T)` at the end of
  every full cycle of `i` (`L i ∣ N_i(T)`).
* **Holroyd–Propp** (`abs_occCount_rotorWalk_sub_le`): `|N_s(T) − T π_s| ≤
  2 M (1 + Σ_i (L i − 1))` with `|h| ≤ M` (`h` the Poisson solution for `1_{s}`), independent
  of `T`; `abs_occFreq_rotorWalk_sub_le`, `occFreq_rotorWalk_isBigO`: frequency error `O(1/T)`.
* `abs_transCount_rotorWalk_sub_target_le`: `|N_ij(T) − T π_i p_ij| ≤ (L i − 1) + p_ij C_i`.

**Correction** (post #3: "a by-product of rotors is that we achieve the same exact expected
number of transitions that we did by conditional MC"). The rotor counts are within a constant
(independent of `T`) of conditional MC's targets `T π_i p_ij`, and are exactly `p_ij N_i(T)`
whenever `N_i(T)` is a multiple of `L i`; they cannot be *exactly* `T π_i p_ij` in general,
since that number need not be an integer: `not_transCount_eq_target` (two-state chain with
`p_ii = 7/8`, `π = (1/2, 1/2)`: `N_00(T) = 7T/16` is impossible unless `16 ∣ T`).

**Correction** (randomized rotor). Each single departure of the randomized rotor has the right
law (`card_offset_eq`: for a uniform offset, the `k`-th departure from `i` goes to `j` with
probability exactly `p_ij`), and the pathwise bound gives `|E N_s(T) − T π_s| ≤ C` for any
law of the start and offsets (`abs_expected_occCount_rotorWalk_sub_le`). But the expected
occupation is **not** exactly `T π_s`, even with a stationary start, because successive
departures from a state are dependent: `expected_occCount_ne` is an irreducible two-state chain
(`P = [[1/2, 1/2], [1, 0]]`, `π = (2/3, 1/3)`) with `E N_0(3) = 11/6 ≠ 2 = 3 π_0`.
-/

namespace RQMCMarkov.MarkovDriving

open Finset Matrix Filter Asymptotics

variable {S : Type*} [DecidableEq S]

/-- **The rotor walk**: from `x₀`, the `k`-th departure (`k = 0, 1, …`) from state `i` goes to
`c i ((θ i + k) mod L i)`, entry `k` of `i`'s cycle started at offset `θ i`. -/
def rotorWalk (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) : ℕ → S :=
  stackDrive (fun _ j => j) x₀ (fun i k => c i ((θ i + k) % L i))

/-- The rotor recursion: `x (t+1) = c (x t) ((θ (x t) + N_{x t}(t)) mod L (x t))`. -/
theorem rotorWalk_succ (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) (t : ℕ) :
    rotorWalk L c θ x₀ (t + 1) = c (rotorWalk L c θ x₀ t)
      ((θ (rotorWalk L c θ x₀ t) + occCount (rotorWalk L c θ x₀) (rotorWalk L c θ x₀ t) t) %
        L (rotorWalk L c θ x₀ t)) :=
  stackDrive_succ _ _ _ t

/-- The rotor walk starts at `x₀`. -/
theorem rotorWalk_zero (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) :
    rotorWalk L c θ x₀ 0 = x₀ :=
  rfl

/-- **The rotor walk is a function of the current rotor state**: after time `τ` it is the rotor
walk started at `x τ` with offsets `θ i + N_i(τ)`. -/
theorem rotorWalk_shift (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) (τ t : ℕ) :
    rotorWalk L c θ x₀ (τ + t) = rotorWalk L c (fun i => θ i + occCount (rotorWalk L c θ x₀) i τ)
      (rotorWalk L c θ x₀ τ) t := by
  set x := rotorWalk L c θ x₀ with hx
  have key := (stackDrive_eq_iff (fun _ j => j) (x τ)
    (fun i k => c i ((θ i + occCount x i τ + k) % L i)) (fun t => x (τ + t)) t).2
    ⟨rfl, fun t' _ => ?_⟩
  · exact (key t le_rfl).symm
  · change c (x (τ + t')) ((θ (x (τ + t')) + occCount x (x (τ + t')) τ +
      occCount (fun t => x (τ + t)) (x (τ + t')) t') % L (x (τ + t'))) = x (τ + (t' + 1))
    rw [add_assoc (θ _), ← occCount_add, ← add_assoc τ, hx, rotorWalk_succ]

/-- The rotor walk depends on the offsets only modulo the cycle lengths. -/
theorem rotorWalk_congr_mod (L : S → ℕ) (c : S → ℕ → S) {θ θ' : S → ℕ}
    (h : ∀ i, θ i % L i = θ' i % L i) (x₀ : S) : rotorWalk L c θ x₀ = rotorWalk L c θ' x₀ := by
  funext t
  have key := (stackDrive_eq_iff (fun _ j => j) x₀ (fun i k => c i ((θ i + k) % L i))
    (rotorWalk L c θ' x₀) t).2 ⟨rfl, fun t' _ => ?_⟩
  · exact key t le_rfl
  · change c _ ((θ _ + occCount _ _ t') % L _) = _
    rw [rotorWalk_succ, Nat.add_mod, h, ← Nat.add_mod]

/-- A shift of the summation window of a periodic sequence over one period leaves the sum
unchanged. -/
theorem sum_range_add_periodic {M : Type*} [AddCommGroup M] {F : ℕ → M} {L : ℕ}
    (hF : ∀ k, F (k + L) = F k) (a : ℕ) : ∑ m ∈ range L, F (a + m) = ∑ m ∈ range L, F m := by
  induction a with
  | zero => simp only [zero_add]
  | succ a ih =>
    have h1 := sum_range_succ (fun m => F (a + m)) L
    have h2 := sum_range_succ' (fun m => F (a + m)) L
    beta_reduce at h1 h2
    rw [hF a] at h1
    rw [add_zero] at h2
    have e : ∑ m ∈ range L, F (a + 1 + m) = ∑ m ∈ range L, F (a + (m + 1)) :=
      sum_congr rfl fun m _ => by rw [add_assoc, add_comm 1 m]
    rw [e, ← ih]
    exact (add_right_cancel (h1.symm.trans h2)).symm

/-- **Partial sums of a periodic sequence with zero full-period sum** reduce to the last
incomplete period: `Σ_{k < N} F k = Σ_{k < N mod L} F k`. -/
theorem sum_range_eq_sum_range_mod {M : Type*} [AddCommMonoid M] {F : ℕ → M} {L : ℕ}
    (hF : ∀ k, F (k + L) = F k) (h0 : ∑ m ∈ range L, F m = 0) (N : ℕ) :
    ∑ k ∈ range N, F k = ∑ k ∈ range (N % L), F k := by
  have key : ∀ q r, ∑ k ∈ range (L * q + r), F k = ∑ k ∈ range r, F k := by
    intro q r
    induction q with
    | zero => rw [mul_zero, zero_add]
    | succ q ih =>
      rw [show L * (q + 1) + r = L + (L * q + r) by ring, sum_range_add, h0, zero_add, ← ih]
      exact sum_congr rfl fun k _ => by rw [add_comm L k, hF]
  conv_lhs => rw [← Nat.div_add_mod N L]
  exact key _ _

variable [Fintype S]

/-- **Balanced cycles** (post #3's rotors; needs rational `P`): every cycle has positive length,
and `j` appears exactly `p_ij L i` times in the cycle of `i`. -/
structure IsRotorCycle (P : Matrix S S ℝ) (L : S → ℕ) (c : S → ℕ → S) : Prop where
  len_pos : ∀ i, 0 < L i
  card_eq : ∀ i j, (((range (L i)).filter fun m => c i m = j).card : ℝ) = P i j * L i

/-- **A full cycle samples the row exactly**: `Σ_{m < L i} g (c i m) = L i (Pg)(i)`. -/
theorem sum_cycle_eq {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (g : S → ℝ) (i : S) : ∑ m ∈ range (L i), g (c i m) = L i * (P *ᵥ g) i := by
  rw [← sum_fiberwise (range (L i)) (c i)]
  have e : ∀ j, ∑ m ∈ (range (L i)).filter (fun m => c i m = j), g (c i m) =
      g j * (((range (L i)).filter fun m => c i m = j).card : ℝ) := fun j => by
    rw [sum_congr rfl fun m hm => by rw [(mem_filter.1 hm).2], sum_const, nsmul_eq_mul,
      mul_comm]
  rw [sum_congr rfl fun j _ => e j]
  simp only [hc.card_eq, mulVec, dotProduct, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The **departure sequence** of the rotor at `i`, centred: `F k = g(c i ((θ + k) mod L)) −
(Pg)(i)`. It is `L i`-periodic with zero sum over a period. -/
theorem sum_range_rotor_centred_eq_zero {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (g : S → ℝ) (i : S) (a : ℕ) :
    ∑ m ∈ range (L i), (g (c i ((a + m) % L i)) - (P *ᵥ g) i) = 0 := by
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hper : ∀ k, g (c i ((k + L i) % L i)) = g (c i (k % L i)) := fun k => by
    rw [Nat.add_mod_right]
  rw [sum_range_add_periodic (F := fun m => g (c i (m % L i))) hper a]
  have e : ∑ m ∈ range (L i), g (c i (m % L i)) = ∑ m ∈ range (L i), g (c i m) :=
    sum_congr rfl fun m hm => by rw [Nat.mod_eq_of_lt (mem_range.1 hm)]
  rw [e, sum_cycle_eq hc g i, sub_self]

/-- The departure discrepancy of a rotor walk is the sum over the last, incomplete cycle:
`D_i(g, T) = Σ_{k < N_i(T) mod L i} (g(c i ((θ i + k) mod L i)) − (Pg)(i))`. -/
theorem departureDiscrepancy_rotorWalk_eq {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) (g : S → ℝ) (i : S) (T : ℕ) :
    departureDiscrepancy P g (rotorWalk L c θ x₀) i T =
      ∑ k ∈ range (occCount (rotorWalk L c θ x₀) i T % L i),
        (g (c i ((θ i + k) % L i)) - (P *ᵥ g) i) := by
  unfold rotorWalk
  rw [departureDiscrepancy_stackDrive]
  refine sum_range_eq_sum_range_mod (fun k => ?_) (sum_range_rotor_centred_eq_zero hc g i _) _
  rw [← add_assoc, Nat.add_mod_right]

/-- A sum of `r` terms bounded by `B`, with `r < L`, is at most `(L − 1) B`. -/
theorem abs_sum_range_le_of_lt {F : ℕ → ℝ} {B : ℝ} (hB : ∀ k, |F k| ≤ B) {r L : ℕ}
    (hr : r < L) : |∑ k ∈ range r, F k| ≤ (L - 1 : ℕ) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  calc |∑ k ∈ range r, F k| ≤ ∑ k ∈ range r, |F k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range r, B := sum_le_sum fun k _ => hB k
    _ = r * B := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (L - 1 : ℕ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hB0

/-- **Rotor departure discrepancies are bounded**: if every centred departure value
`g(c i m) − (Pg)(i)` is at most `B` in absolute value, then `|D_i(g, T)| ≤ (L i − 1) B` for
every `T`. -/
theorem abs_departureDiscrepancy_rotorWalk_le {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) {g : S → ℝ} {i : S} {B : ℝ}
    (hB : ∀ m, |g (c i m) - (P *ᵥ g) i| ≤ B) (T : ℕ) :
    |departureDiscrepancy P g (rotorWalk L c θ x₀) i T| ≤ (L i - 1 : ℕ) * B := by
  rw [departureDiscrepancy_rotorWalk_eq hc]
  exact abs_sum_range_le_of_lt (fun k => hB _) (Nat.mod_lt _ (hc.len_pos i))

omit [DecidableEq S] in
/-- For a stochastic `P`, `|g(j) − (Pg)(i)| ≤ 2M` when `|g| ≤ M`. -/
theorem abs_sub_mulVec_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {g : S → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) (i j : S) :
    |g j - (P *ᵥ g) i| ≤ 2 * M := by
  have hPg : |(P *ᵥ g) i| ≤ M := by
    calc |(P *ᵥ g) i| = |∑ k, P i k * g k| := rfl
      _ ≤ ∑ k, |P i k * g k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, P i k * M := sum_le_sum fun k _ => by
          rw [abs_mul, abs_of_nonneg (hP0 i k)]
          exact mul_le_mul_of_nonneg_left (hM k) (hP0 i k)
      _ = M := by rw [← sum_mul, hP1 i, one_mul]
  have := abs_sub (g j) ((P *ᵥ g) i)
  linarith [hM j]

/-- **Rotor departure discrepancy, explicit**: `|D_i(g, T)| ≤ 2 (L i − 1) M` when `|g| ≤ M`. -/
theorem abs_departureDiscrepancy_rotorWalk_le_two_mul {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) {g : S → ℝ} {M : ℝ}
    (hM : ∀ j, |g j| ≤ M) (i : S) (T : ℕ) :
    |departureDiscrepancy P g (rotorWalk L c θ x₀) i T| ≤ (L i - 1 : ℕ) * (2 * M) :=
  abs_departureDiscrepancy_rotorWalk_le hc θ x₀ (fun _ => abs_sub_mulVec_le hP0 hP1 hM i _) T

/-- **Rotor transition counts are within one cycle**: `|N_ij(T) − p_ij N_i(T)| ≤ L i − 1`. -/
theorem abs_transCount_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) (i j : S) (T : ℕ) :
    |(transCount (rotorWalk L c θ x₀) i j T : ℝ) - P i j * occCount (rotorWalk L c θ x₀) i T| ≤
      (L i - 1 : ℕ) := by
  rw [transCount_sub_eq_departureDiscrepancy, ← mul_one ((L i - 1 : ℕ) : ℝ)]
  refine abs_departureDiscrepancy_rotorWalk_le hc θ x₀ (fun m => ?_) T
  rw [mulVec_indicator]
  have hle : P i j ≤ 1 := by
    rw [← hP1 i]
    exact single_le_sum (fun k _ => hP0 i k) (mem_univ j)
  split_ifs
  · rw [abs_of_nonneg (by linarith)]
    linarith [hP0 i j]
  · rw [zero_sub, abs_neg, abs_of_nonneg (hP0 i j)]
    exact hle

omit [Fintype S] in
/-- **Exact counts at full cycles**: if `L i ∣ N_i(T)` then `N_ij(T) = p_ij N_i(T)` exactly, and
every departure discrepancy of `i` vanishes. -/
theorem transCount_rotorWalk_eq_of_dvd [Finite S] {P : Matrix S S ℝ} {L : S → ℕ}
    {c : S → ℕ → S} (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) {i : S} {T : ℕ}
    (hdvd : L i ∣ occCount (rotorWalk L c θ x₀) i T) (j : S) :
    (transCount (rotorWalk L c θ x₀) i j T : ℝ) = P i j * occCount (rotorWalk L c θ x₀) i T := by
  have := Fintype.ofFinite S
  rw [← sub_eq_zero, transCount_sub_eq_departureDiscrepancy,
    departureDiscrepancy_rotorWalk_eq hc, Nat.mod_eq_zero_of_dvd hdvd, range_zero, sum_empty]

/-- **Holroyd–Propp occupation bound** (post #3, "the error in occupation frequencies is
`O(1/T)`"): `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))` for every `T`, where `h − Ph = 1_{s} −
π_s` and `|h| ≤ M`. -/
theorem abs_occCount_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (rotorWalk L c θ x₀) s T : ℝ) - T * μs| ≤
      2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) := by
  refine (abs_occCount_sub_le P hh hM _ T).trans ?_
  have hs := sum_le_sum fun i (_ : i ∈ univ) =>
    abs_departureDiscrepancy_rotorWalk_le_two_mul hP0 hP1 hc θ x₀ hM i T
  rw [← sum_mul] at hs
  have e : 2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) = 2 * M + (∑ i, ((L i - 1 : ℕ) : ℝ)) * (2 * M) :=
    by ring
  rw [e]
  exact add_le_add le_rfl hs

/-- **Rotor occupation frequencies converge at `O(1/T)`**: `|N_s(T)/T − π_s| ≤ C / T`. -/
theorem abs_occFreq_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    {T : ℕ} (hT : 0 < T) : |(occCount (rotorWalk L c θ x₀) s T : ℝ) / T - μs| ≤
      2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm μs]
  exact abs_occCount_rotorWalk_sub_le hP0 hP1 hc θ x₀ hh hM T

/-- **Rotor occupation frequencies are `O(1/T)`** (Holroyd and Propp 2010). -/
theorem occFreq_rotorWalk_isBigO {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (rotorWalk L c θ x₀) s T : ℝ) / T - μs) =O[atTop]
      fun T : ℕ => (1 : ℝ) / T := by
  refine IsBigO.of_bound (2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / T by positivity),
    mul_one_div]
  exact abs_occFreq_rotorWalk_sub_le hP0 hP1 hc θ x₀ hh hM hT

/-- **Rotor transition counts against conditional MC's targets**: `|N_ij(T) − T π_i p_ij| ≤
(L i − 1) + p_ij · 2M (1 + Σ_k (L k − 1))`, bounded in `T` (post #3: rotors give the counts of
conditional MC "as an output"). -/
theorem abs_transCount_rotorWalk_sub_target_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {i : S} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (j : S) (T : ℕ) : |(transCount (rotorWalk L c θ x₀) i j T : ℝ) - T * μi * P i j| ≤
      (L i - 1 : ℕ) + P i j * (2 * M * (1 + ∑ k, ((L k - 1 : ℕ) : ℝ))) := by
  have e : (transCount (rotorWalk L c θ x₀) i j T : ℝ) - T * μi * P i j =
      ((transCount (rotorWalk L c θ x₀) i j T : ℝ) - P i j * occCount (rotorWalk L c θ x₀) i T) +
        P i j * ((occCount (rotorWalk L c θ x₀) i T : ℝ) - T * μi) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add (abs_transCount_rotorWalk_sub_le hP0 hP1 hc θ x₀ i j T)
    ?_)
  rw [abs_mul, abs_of_nonneg (hP0 i j)]
  exact mul_le_mul_of_nonneg_left (abs_occCount_rotorWalk_sub_le hP0 hP1 hc θ x₀ hh hM T)
    (hP0 i j)

omit [Fintype S] in
/-- **The randomized rotor: each departure has the right law.** For an offset uniform on
`{0, …, L i − 1}`, the `k`-th departure from `i` goes to `j` for exactly `p_ij L i` of the `L i`
offsets, i.e. with probability `p_ij`. -/
theorem card_offset_eq {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (i j : S) (k : ℕ) :
    (((range (L i)).filter fun a => c i ((a + k) % L i) = j).card : ℝ) = P i j * L i := by
  have h := sum_range_add_periodic (F := fun m => if c i (m % L i) = j then (1 : ℝ) else 0)
    (L := L i) (fun m => by simp only [Nat.add_mod_right]) k
  rw [← hc.card_eq, ← sum_boole, ← sum_boole]
  have e1 : ∑ a ∈ range (L i), (if c i ((a + k) % L i) = j then (1 : ℝ) else 0) =
      ∑ m ∈ range (L i), (if c i ((k + m) % L i) = j then (1 : ℝ) else 0) :=
    sum_congr rfl fun a _ => by rw [add_comm a k]
  have e2 : ∑ m ∈ range (L i), (if c i (m % L i) = j then (1 : ℝ) else 0) =
      ∑ m ∈ range (L i), (if c i m = j then (1 : ℝ) else 0) :=
    sum_congr rfl fun m hm => by rw [Nat.mod_eq_of_lt (mem_range.1 hm)]
  rw [e1, h, e2]

/-- **Expected occupation under any randomization** of the start and the offsets is within the
Holroyd–Propp constant of `T π_s`: for weights `w ≥ 0` summing to one over finitely many
configurations `(θ, x₀)`, `|Σ w N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))`. -/
theorem abs_expected_occCount_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    {ι : Type*} (A : Finset ι) (w : ι → ℝ) (hw0 : ∀ a ∈ A, 0 ≤ w a) (hw1 : ∑ a ∈ A, w a = 1)
    (θ : ι → S → ℕ) (x₀ : ι → S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |∑ a ∈ A, w a * (occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs| ≤
      2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) := by
  have e : ∑ a ∈ A, w a * ((occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs) =
      ∑ a ∈ A, w a * (occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) -
        (∑ a ∈ A, w a) * (T * μs) := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [hw1, one_mul] at e
  rw [← e]
  calc |∑ a ∈ A, w a * ((occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs)|
      ≤ ∑ a ∈ A, |w a * ((occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, w a * (2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) := sum_le_sum fun a ha => by
        rw [abs_mul, abs_of_nonneg (hw0 a ha)]
        exact mul_le_mul_of_nonneg_left
          (abs_occCount_rotorWalk_sub_le hP0 hP1 hc (θ a) (x₀ a) hh hM T) (hw0 a ha)
    _ = 2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) := by rw [← sum_mul, hw1, one_mul]

/-! ### Counterexamples -/

/-- The two-state chain of post #3 with stay probabilities `7/8` (mean spell length `8`). -/
noncomputable def twoStateStay78 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 7 / 8 else 1 / 8

/-- Its stationary distribution is `(1/2, 1/2)`. -/
theorem isStationaryDistribution_twoStateStay78 :
    IsStationaryDistribution twoStateStay78 (fun _ => 1 / 2) := by
  refine ⟨funext fun j => ?_, fun _ => by norm_num, ?_⟩
  · change ∑ i, (1 / 2 : ℝ) * twoStateStay78 i j = 1 / 2
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp only [twoStateStay78] <;> norm_num
  · rw [Fin.sum_univ_two]
    norm_num

/-- **Correction: rotor counts are not exactly conditional MC's targets.** In the
`7/8`-chain, `T π_0 p_00 = 7T/16`, which no path can match when `16 ∤ T` (transition counts
are integers). -/
theorem not_transCount_eq_target (x : ℕ → Fin 2) {T : ℕ} (hT : ¬ 16 ∣ T) :
    (transCount x 0 0 T : ℝ) ≠ T * (1 / 2) * twoStateStay78 0 0 := by
  intro h
  have h00 : twoStateStay78 0 0 = 7 / 8 := by simp only [twoStateStay78, ite_true]
  rw [h00] at h
  have hR : (16 * transCount x 0 0 T : ℝ) = 7 * T := by linarith
  have hN : 16 * transCount x 0 0 T = 7 * T := by exact_mod_cast hR
  have hdvd : 16 ∣ 7 * T := ⟨_, hN.symm⟩
  exact hT ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hdvd))

/-- The chain of the randomized-rotor counterexample: from state `0` go to `0` or `1` with
probability `1/2`; from state `1` go to `0`. -/
noncomputable def rotorCounterexampleChain : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then 1 / 2 else if j = 0 then 1 else 0

/-- Its stationary distribution `(2/3, 1/3)`. -/
noncomputable def rotorCounterexampleStationary : Fin 2 → ℝ :=
  fun i => if i = 0 then 2 / 3 else 1 / 3

/-- The cycle lengths of the counterexample: `2` at state `0`, `1` at state `1`. -/
def rotorCounterexampleLen : Fin 2 → ℕ := fun i => if i = 0 then 2 else 1

/-- The cycles of the counterexample: `(0, 1)` at state `0`, `(0)` at state `1`. -/
def rotorCounterexampleCycle : Fin 2 → ℕ → Fin 2 :=
  fun i m => if i = 0 then (if m % 2 = 0 then 0 else 1) else 0

/-- The offsets of the counterexample: `a` at state `0` (uniform on `{0, 1}`), `0` at state `1`
(whose cycle has length one). -/
def rotorCounterexampleOffset (a : ℕ) : Fin 2 → ℕ := fun i => if i = 0 then a else 0

/-- **Correction: the randomized rotor is not exactly unbiased for the occupation.** For the
irreducible chain `P = [[1/2, 1/2], [1, 0]]` with stationary distribution `π = (2/3, 1/3)` and
balanced cycles `(0, 1)`, `(0)`, a stationary start `x₀ ∼ π` and an offset uniform on `{0, 1}`
(independent) give `E N_0(3) = 11/6`, not `3 π_0 = 2`. -/
theorem expected_occCount_ne :
    IsStationaryDistribution rotorCounterexampleChain rotorCounterexampleStationary ∧
    (∀ i j, ∃ k, 0 < (rotorCounterexampleChain ^ k) i j) ∧
    IsRotorCycle rotorCounterexampleChain rotorCounterexampleLen rotorCounterexampleCycle ∧
    ∑ x₀ : Fin 2, ∑ a ∈ range 2, rotorCounterexampleStationary x₀ * (1 / 2) *
      (occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset a) x₀) 0 3 : ℝ) = 11 / 6 ∧
    (11 / 6 : ℝ) ≠ 3 * rotorCounterexampleStationary 0 := by
  refine ⟨⟨funext fun j => ?_, fun i => ?_, ?_⟩, fun i j => ?_, ⟨fun i => ?_, fun i j => ?_⟩, ?_,
    ?_⟩
  · change ∑ i, rotorCounterexampleStationary i * rotorCounterexampleChain i j = _
    rw [Fin.sum_univ_two]
    fin_cases j <;>
      simp only [rotorCounterexampleStationary, rotorCounterexampleChain] <;> norm_num
  · fin_cases i <;> simp only [rotorCounterexampleStationary] <;> norm_num
  · rw [Fin.sum_univ_two]
    simp only [rotorCounterexampleStationary]
    norm_num
  · by_cases hij : i = j
    · refine ⟨0, ?_⟩
      subst hij
      rw [pow_zero, one_apply_eq]
      exact one_pos
    · refine ⟨1, ?_⟩
      rw [pow_one]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simp only [rotorCounterexampleChain]
        norm_num
      · simp only [rotorCounterexampleChain]
        norm_num
      · exact absurd rfl hij
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;>
      simp only [rotorCounterexampleLen, rotorCounterexampleChain] <;> norm_num <;> decide +kernel
  · have h00 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 0) 0) 0 3 = 2 := by decide +kernel
    have h01 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 1) 0) 0 3 = 2 := by decide +kernel
    have h10 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 0) 1) 0 3 = 2 := by decide +kernel
    have h11 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 1) 1) 0 3 = 1 := by decide +kernel
    simp only [Fin.sum_univ_two, sum_range_succ, sum_range_zero, zero_add, h00, h01, h10, h11]
    simp only [rotorCounterexampleStationary]
    norm_num
  · simp only [rotorCounterexampleStationary]
    norm_num

end RQMCMarkov.MarkovDriving
