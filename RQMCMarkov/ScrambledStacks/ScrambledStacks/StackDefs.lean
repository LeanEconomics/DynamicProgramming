/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackBound
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

/-! # Per-state scrambled van der Corput stacks: definitions (post #3, codes (ii) and (iii))

Post #3, codes (ii) and (iii): "one Sobol sequence per state + random digital shift" and "one
Sobol sequence per state + Owen scrambling", used as stacks (the `k`-th departure from state `i`
uses point `k` of stack `i`). In one dimension the Sobol sequence is the base-2 van der Corput
sequence, whose point `k` has binary digit `j + 1` equal to bit `j` of `k`.

**Model (Owen's nested uniform scramble of all digits, Owen 1997).** A flip table
`f : ℕ → ℕ → Bool` flips digit `j + 1` of point `k` by `f j (k % 2^j)`: the flip depends on the
original digits `1, …, j` (the node `k % 2^j` of the binary tree). The scrambled point is
`scrambledVdc f k = Σ_j d_j / 2^(j+1)` with `d_j = scrambledDigit f k j = bit_j(k) xor
f j (k % 2^j)`. All digits are scrambled, also those beyond the bit length of `k` (there the node
is `k` itself), so there is no truncation. A **digital shift** is a table `shiftTable e` with
`f j p = e j`. A state space `Fin n` has one table per state, `f : Fin n → ℕ → ℕ → Bool`, and
stacks `scrambledStack f i k = scrambledVdc (f i) k`.

**Probability spaces.** `owenMeasure n` is the product of fair coins (`fairCoin`) on
`Fin n × ℕ × ℕ` (state, depth, node; nodes `p ≥ 2^j` are unused) with table `owenTable ω`;
`shiftMeasure n` is the product of fair coins on `Fin n × ℕ` with table `shiftFlips ω`. The
tables of different states use disjoint coordinates, so the stacks are independent.

## Main results

* `binaryVal b = Σ_j b_j / 2^(j+1)` and `digitPrefix b m` (the first `m` digits as a number):
  `binaryVal_eq_digitPrefix_add`, `digitPrefix_div_le_binaryVal`,
  `binaryVal_le_digitPrefix_add_one_div`
  (each point lies in the closed dyadic cell of its first `m` digits), `digitPrefix_lt`,
  `digitPrefix_eq_iff` (the digits of `digitPrefix` are the `testBit`s), `digitPrefix_congr`,
  `eq_of_digitPrefix_eq`.
* `NotEventuallyConst b`: the digits are not eventually constant. Then the point is in the open
  cell (`digitPrefix_div_lt_binaryVal`, `binaryVal_lt_digitPrefix_add_one_div`) and is not a
  dyadic rational (`binaryVal_ne_dyadic`), in particular not `0` or `1`.
* `scrambledVdc_mem_Icc`: every scrambled point lies in `[0, 1]`, for every flip table.
* `IsGoodTable f`: no stack digit sequence is eventually constant (no stack point is a dyadic
  rational, `scrambledStack_ne_dyadic`). `ae_isGoodTable_owen`, `ae_isGoodTable_shift`: this
  event has probability one under both randomisations.
* `infinitePi_xor_cylinder`: fixing `m` digits `xor (c j) (ω (g j))` (injective `g`) has
  probability `2^{-m}`; `measure_digitPrefix_eq`, `measure_digitPrefix_lt`;
  `map_binaryVal_xor_eq_uniformIco`: such a digit sequence gives a `U[0,1)` point.
* `map_scrambledStack_owen`, `map_scrambledStack_shift` (post #2's requirement (i)): every stack
  point is uniform on `[0,1)` under Owen scrambling and under the digital shift;
  `owen_digitPrefix_eq`, `shift_digitPrefix_eq`: its first `m` scrambled digits are uniform.
* Measurability: `measurable_binaryVal`, `measurable_scrambledStack_owen`,
  `measurable_scrambledStack_shift`, `measurable_stackPath_restrict_of`, `measurable_stackPath_of`,
  `measurable_occCount_of`, `measurable_transCount_of` (the path coordinates and counts are
  random variables for any measurable family of stacks).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory Finset Filter Topology

variable {n : ℕ}

/-! ### Binary expansions -/

/-- The real number `Σ_j b_j / 2^(j+1)` with binary digits `b_0, b_1, …` (digit `j + 1` after
the binary point is `b j`). -/
noncomputable def binaryVal (b : ℕ → Bool) : ℝ := ∑' j, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1)

/-- A digit term is at most `(1/2)^j / 2`. -/
theorem digitTerm_le (b : ℕ → Bool) (j : ℕ) :
    (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) ≤ 1 / 2 / 2 ^ j := by
  have h : (if b j then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  rw [div_le_div_iff₀ h2 (by positivity), pow_succ]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j]

/-- A digit term is nonnegative. -/
theorem digitTerm_nonneg (b : ℕ → Bool) (j : ℕ) :
    0 ≤ (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) := by
  have h : (0 : ℝ) ≤ if b j then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  positivity

/-- The digit series is summable. -/
theorem summable_digitTerm (b : ℕ → Bool) :
    Summable fun j => (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) :=
  Summable.of_nonneg_of_le (digitTerm_nonneg b) (digitTerm_le b) (summable_geometric_two' 1)

/-- `0 ≤ binaryVal b`. -/
theorem binaryVal_nonneg (b : ℕ → Bool) : 0 ≤ binaryVal b :=
  tsum_nonneg (digitTerm_nonneg b)

/-- `binaryVal b ≤ 1`. -/
theorem binaryVal_le_one (b : ℕ → Bool) : binaryVal b ≤ 1 := by
  unfold binaryVal
  calc ∑' j, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) ≤ ∑' j : ℕ, (1 : ℝ) / 2 / 2 ^ j :=
        (summable_digitTerm b).tsum_le_tsum (digitTerm_le b) (summable_geometric_two' 1)
    _ = 1 := tsum_geometric_two' 1

/-- `binaryVal b > 0` if some digit is `1`. -/
theorem binaryVal_pos {b : ℕ → Bool} (h : ∃ j, b j = true) : 0 < binaryVal b := by
  obtain ⟨j, hj⟩ := h
  refine (summable_digitTerm b).tsum_pos (digitTerm_nonneg b) j ?_
  simp only [hj, ite_true]
  positivity

/-- `binaryVal b < 1` if some digit is `0`. -/
theorem binaryVal_lt_one {b : ℕ → Bool} (h : ∃ j, b j = false) : binaryVal b < 1 := by
  obtain ⟨j, hj⟩ := h
  unfold binaryVal
  calc ∑' j, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) < ∑' j : ℕ, (1 : ℝ) / 2 / 2 ^ j := by
        refine (summable_digitTerm b).tsum_lt_tsum (digitTerm_le b) (i := j) ?_
          (summable_geometric_two' 1)
        simp only [hj, Bool.false_eq_true, ite_false, zero_div]
        positivity
    _ = 1 := tsum_geometric_two' 1

/-- The first `m` digits of `b` as a natural number (`b 0` is the most significant):
`digitPrefix b (m + 1) = 2 digitPrefix b m + b_m`. -/
def digitPrefix (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * digitPrefix b m + if b m then 1 else 0

/-- `digitPrefix b m < 2^m`. -/
theorem digitPrefix_lt (b : ℕ → Bool) (m : ℕ) : digitPrefix b m < 2 ^ m := by
  induction m with
  | zero => simp [digitPrefix]
  | succ m ih =>
    have h : (if b m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only [digitPrefix, pow_succ]
    omega

/-- `digitPrefix` depends only on the first `m` digits. -/
theorem digitPrefix_congr {b b' : ℕ → Bool} {m : ℕ} (h : ∀ j < m, b j = b' j) :
    digitPrefix b m = digitPrefix b' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [digitPrefix]
    rw [ih fun j hj => h j (by omega), h m (by omega)]

/-- Equal prefixes have equal digits. -/
theorem eq_of_digitPrefix_eq {b b' : ℕ → Bool} {m : ℕ} (h : digitPrefix b m = digitPrefix b' m) :
    ∀ j < m, b j = b' j := by
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    simp only [digitPrefix] at h
    have hb : (if b m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hb' : (if b' m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h1 : digitPrefix b m = digitPrefix b' m := by omega
    have h2 : (if b m then 1 else 0) = (if b' m then 1 else 0) := by omega
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h1 j hj
    · cases hbj : b j <;> cases hbj' : b' j <;> simp_all

/-- **The digits of `digitPrefix`**: `digitPrefix b m = d` iff `d < 2^m` and the digits
`b 0, …, b (m-1)` are the bits `m - 1, …, 0` of `d`. -/
theorem digitPrefix_eq_iff (b : ℕ → Bool) (m d : ℕ) :
    digitPrefix b m = d ↔ d < 2 ^ m ∧ ∀ j < m, b j = d.testBit (m - 1 - j) := by
  induction m generalizing d with
  | zero =>
    simp only [digitPrefix, pow_zero, Nat.lt_one_iff, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, and_true]
    exact eq_comm
  | succ m ih =>
    have hb : (if b m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hbit : ((if b m then 1 else 0) = d % 2) ↔ b m = d.testBit 0 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one d with h | h <;> cases b m <;> simp [h]
    simp only [digitPrefix]
    constructor
    · intro h
      have hd2 : digitPrefix b m = d / 2 := by omega
      have hm2 : (if b m then 1 else 0) = d % 2 := by omega
      refine ⟨h ▸ digitPrefix_lt b (m + 1), fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · have e : m + 1 - 1 - j = (m - 1 - j) + 1 := by omega
        rw [e, ← Nat.testBit_div_two, ← hd2]
        exact ((ih (digitPrefix b m)).1 rfl).2 j hj
      · have e : j + 1 - 1 - j = 0 := by omega
        rw [e]
        exact hbit.1 hm2
    · rintro ⟨hd, hdig⟩
      have hm2 : (if b m then 1 else 0) = d % 2 := by
        refine hbit.2 ?_
        have := hdig m (by omega)
        rwa [show m + 1 - 1 - m = 0 by omega] at this
      have hd2 : digitPrefix b m = d / 2 := by
        refine (ih (d / 2)).2 ⟨by rw [pow_succ] at hd; omega, fun j hj => ?_⟩
        rw [Nat.testBit_div_two, hdig j (by omega)]
        congr 1
        omega
      rw [hd2, hm2]
      exact Nat.div_add_mod d 2

/-- The first `m` digit terms sum to `digitPrefix b m / 2^m`. -/
theorem sum_digitTerm_eq_digitPrefix (b : ℕ → Bool) (m : ℕ) :
    ∑ j ∈ range m, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) = digitPrefix b m / 2 ^ m := by
  induction m with
  | zero => simp [digitPrefix]
  | succ m ih =>
    rw [sum_range_succ, ih]
    simp only [digitPrefix, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    cases b m <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_zero,
      Nat.cast_one] <;> field_simp <;> ring

/-- **Cell decomposition**: `binaryVal b = (digitPrefix b m + binaryVal (b (· + m))) / 2^m`. -/
theorem binaryVal_eq_digitPrefix_add (b : ℕ → Bool) (m : ℕ) :
    binaryVal b = (digitPrefix b m + binaryVal fun j => b (j + m)) / 2 ^ m := by
  unfold binaryVal
  rw [← (summable_digitTerm b).sum_add_tsum_nat_add m, sum_digitTerm_eq_digitPrefix, add_div]
  congr 1
  rw [← tsum_div_const]
  refine tsum_congr fun j => ?_
  rw [div_div, ← pow_add]
  congr 2
  ring

/-- The point lies above the left end of its level-`m` cell. -/
theorem digitPrefix_div_le_binaryVal (b : ℕ → Bool) (m : ℕ) :
    (digitPrefix b m : ℝ) / 2 ^ m ≤ binaryVal b := by
  rw [binaryVal_eq_digitPrefix_add b m]
  have := binaryVal_nonneg fun j => b (j + m)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The point lies below the right end of its level-`m` cell. -/
theorem binaryVal_le_digitPrefix_add_one_div (b : ℕ → Bool) (m : ℕ) :
    binaryVal b ≤ ((digitPrefix b m : ℝ) + 1) / 2 ^ m := by
  rw [binaryVal_eq_digitPrefix_add b m]
  have := binaryVal_le_one fun j => b (j + m)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The digit sequence `b` is **not eventually constant**: beyond every position there is a
`1` and a `0`. -/
def NotEventuallyConst (b : ℕ → Bool) : Prop :=
  ∀ J, (∃ j, J ≤ j ∧ b j = true) ∧ ∃ j, J ≤ j ∧ b j = false

/-- Shifting the digits keeps them not eventually constant. -/
theorem NotEventuallyConst.shift {b : ℕ → Bool} (hb : NotEventuallyConst b) (m : ℕ) :
    NotEventuallyConst fun j => b (j + m) := by
  intro J
  obtain ⟨⟨j, hj, hbj⟩, ⟨j', hj', hbj'⟩⟩ := hb (J + m)
  refine ⟨⟨j - m, by omega, ?_⟩, ⟨j' - m, by omega, ?_⟩⟩
  · change b (j - m + m) = true
    rw [Nat.sub_add_cancel (by omega)]
    exact hbj
  · change b (j' - m + m) = false
    rw [Nat.sub_add_cancel (by omega)]
    exact hbj'

/-- With digits not eventually constant the point is strictly inside its level-`m` cell (left). -/
theorem digitPrefix_div_lt_binaryVal {b : ℕ → Bool} (hb : NotEventuallyConst b) (m : ℕ) :
    (digitPrefix b m : ℝ) / 2 ^ m < binaryVal b := by
  rw [binaryVal_eq_digitPrefix_add b m]
  obtain ⟨⟨j, -, hj⟩, -⟩ := hb.shift m 0
  have := binaryVal_pos (b := fun j => b (j + m)) ⟨j, hj⟩
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- With digits not eventually constant the point is strictly inside its level-`m` cell
(right). -/
theorem binaryVal_lt_digitPrefix_add_one_div {b : ℕ → Bool} (hb : NotEventuallyConst b) (m : ℕ) :
    binaryVal b < ((digitPrefix b m : ℝ) + 1) / 2 ^ m := by
  rw [binaryVal_eq_digitPrefix_add b m]
  obtain ⟨-, ⟨j, -, hj⟩⟩ := hb.shift m 0
  have := binaryVal_lt_one (b := fun j => b (j + m)) ⟨j, hj⟩
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- **No dyadic rationals**: digits that are not eventually constant never give `a / 2^m`
(in particular never `0` or `1`). -/
theorem binaryVal_ne_dyadic {b : ℕ → Bool} (hb : NotEventuallyConst b) (a : ℤ) (m : ℕ) :
    binaryVal b ≠ a / 2 ^ m := by
  intro h
  have h1 := digitPrefix_div_lt_binaryVal hb m
  have h2 := binaryVal_lt_digitPrefix_add_one_div hb m
  rw [h] at h1 h2
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_div_iff_of_pos_right hp] at h1 h2
  have h1' : ((digitPrefix b m : ℕ) : ℤ) < a := by exact_mod_cast h1
  have h2' : a < ((digitPrefix b m : ℕ) : ℤ) + 1 := by exact_mod_cast h2
  omega

/-! ### Scrambled van der Corput points -/

/-- **Owen-scrambled digit** `j` (digit `j + 1` after the binary point) of the van der Corput
point `k` under the flip table `f`: `bit_j(k) xor f j (k % 2^j)`. -/
def scrambledDigit (f : ℕ → ℕ → Bool) (k j : ℕ) : Bool := xor (k.testBit j) (f j (k % 2 ^ j))

/-- The **scrambled van der Corput point** `k`: `Σ_j scrambledDigit f k j / 2^(j+1)`. -/
noncomputable def scrambledVdc (f : ℕ → ℕ → Bool) (k : ℕ) : ℝ := binaryVal (scrambledDigit f k)

/-- `scrambledVdc` written out as a series. -/
theorem scrambledVdc_eq_tsum (f : ℕ → ℕ → Bool) (k : ℕ) :
    scrambledVdc f k = ∑' j, (if scrambledDigit f k j then (1 : ℝ) else 0) / 2 ^ (j + 1) := rfl

/-- The **digital-shift** flip table: digit `j + 1` is flipped by `e j`, at every node. -/
def shiftTable (e : ℕ → Bool) : ℕ → ℕ → Bool := fun j _ => e j

/-- Under a digital shift, digit `j` is `bit_j(k) xor e j`. -/
theorem scrambledDigit_shiftTable (e : ℕ → Bool) (k j : ℕ) :
    scrambledDigit (shiftTable e) k j = xor (k.testBit j) (e j) := rfl

/-- Every scrambled point lies in `[0, 1]`, for every flip table. -/
theorem scrambledVdc_mem_Icc (f : ℕ → ℕ → Bool) (k : ℕ) : scrambledVdc f k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨binaryVal_nonneg _, binaryVal_le_one _⟩

/-- The **stacks**: stack `i` is the scrambled van der Corput sequence with the table `f i`. -/
noncomputable def scrambledStack (f : Fin n → ℕ → ℕ → Bool) (i : Fin n) (k : ℕ) : ℝ :=
  scrambledVdc (f i) k

/-- Stack points lie in `[0, 1]`. -/
theorem scrambledStack_mem_Icc (f : Fin n → ℕ → ℕ → Bool) (i : Fin n) (k : ℕ) :
    scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 :=
  scrambledVdc_mem_Icc _ _

/-- The **good event**: no digit sequence of any stack point is eventually constant. -/
def IsGoodTable (f : Fin n → ℕ → ℕ → Bool) : Prop :=
  ∀ i k, NotEventuallyConst (scrambledDigit (f i) k)

/-- On the good event no stack point is a dyadic rational (nor `0`, nor `1`). -/
theorem scrambledStack_ne_dyadic {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin n)
    (k : ℕ) (a : ℤ) (m : ℕ) : scrambledStack f i k ≠ a / 2 ^ m :=
  binaryVal_ne_dyadic (hf i k) a m

/-- On the good event every stack point lies in `(0, 1)`. -/
theorem scrambledStack_mem_Ioo {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin n)
    (k : ℕ) : scrambledStack f i k ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 := digitPrefix_div_lt_binaryVal (hf i k) 0
  have h1 := binaryVal_lt_digitPrefix_add_one_div (hf i k) 0
  simp only [digitPrefix, Nat.cast_zero, pow_zero, div_one, zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-! ### The probability spaces -/

/-- A fair coin on `Bool`. -/
noncomputable abbrev fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- Each face of the fair coin has probability `1/2`. -/
theorem fairCoin_singleton (b : Bool) : fairCoin {b} = 2⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  rfl

/-- **Owen's measure**: i.i.d. fair coins indexed by (state, depth, node). -/
noncomputable abbrev owenMeasure (n : ℕ) : Measure (Fin n × ℕ × ℕ → Bool) :=
  Measure.infinitePi fun _ => fairCoin

/-- The flip tables of a realisation `ω` of Owen's coins. -/
def owenTable (ω : Fin n × ℕ × ℕ → Bool) : Fin n → ℕ → ℕ → Bool := fun i j p => ω (i, j, p)

/-- **The digital-shift measure**: i.i.d. fair coins indexed by (state, depth). -/
noncomputable abbrev shiftMeasure (n : ℕ) : Measure (Fin n × ℕ → Bool) :=
  Measure.infinitePi fun _ => fairCoin

/-- The (digital-shift) flip tables of a realisation `ω`. -/
def shiftFlips (ω : Fin n × ℕ → Bool) : Fin n → ℕ → ℕ → Bool :=
  fun i => shiftTable fun j => ω (i, j)

/-- `owenMeasure n` is a probability measure. -/
theorem isProbabilityMeasure_owenMeasure (n : ℕ) : IsProbabilityMeasure (owenMeasure n) :=
  inferInstance

/-- `shiftMeasure n` is a probability measure. -/
theorem isProbabilityMeasure_shiftMeasure (n : ℕ) : IsProbabilityMeasure (shiftMeasure n) :=
  inferInstance

/-- Under Owen's measure, digit `j` of point `k` of stack `i` is `bit_j(k) xor ω (i, j, k % 2^j)`.
-/
theorem scrambledDigit_owenTable (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) (k j : ℕ) :
    scrambledDigit (owenTable ω i) k j = xor (k.testBit j) (ω (i, j, k % 2 ^ j)) := rfl

/-- Under the digital shift, digit `j` of point `k` of stack `i` is `bit_j(k) xor ω (i, j)`. -/
theorem scrambledDigit_shiftFlips (ω : Fin n × ℕ → Bool) (i : Fin n) (k j : ℕ) :
    scrambledDigit (shiftFlips ω i) k j = xor (k.testBit j) (ω (i, j)) := rfl

/-- **Cylinders of an i.i.d. product** (as `infinitePi_setOf_forall_mem` of `MarkovDriving`):
for injective coordinates `c`, `P(w (c t) ∈ B t, t < T) = ∏_{t<T} ν (B t)`. -/
theorem infinitePi_setOf_forall_mem' {ι α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {c : ℕ → ι} (hc : Function.Injective c) {B : ℕ → Set α}
    (hB : ∀ t, MeasurableSet (B t)) (T : ℕ) :
    Measure.infinitePi (fun _ : ι ↦ ν) {w | ∀ t < T, w (c t) ∈ B t} = ∏ t ∈ range T, ν (B t) := by
  classical
  set B' : ι → Set α := fun p ↦ {a | ∀ t < T, c t = p → a ∈ B t} with hB'def
  have hset : {w : ι → α | ∀ t < T, w (c t) ∈ B t} = Set.pi ↑((range T).image c) B' := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_range, hB'def]
    constructor
    · rintro h p ⟨t', ht', rfl⟩ t ht hct
      rw [← hc hct] at ht' ⊢
      exact h t ht
    · intro h t ht
      exact h (c t) ⟨t, ht, rfl⟩ t ht rfl
  have hB'c : ∀ t < T, B' (c t) = B t := by
    intro t ht
    ext a
    simp only [hB'def, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h t ht rfl
    · intro h t' _ hct
      rw [hc hct]
      exact h
  have hmeas : ∀ p, MeasurableSet (B' p) := by
    intro p
    have : B' p = ⋂ (t : ℕ) (_ : t < T) (_ : c t = p), B t := by
      ext a
      simp only [hB'def, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun t ↦ .iInter fun _ ↦ .iInter fun _ ↦ hB t
  rw [hset, Measure.infinitePi_pi (fun _ : ι ↦ ν) fun p _ ↦ hmeas p,
    Finset.prod_image fun a _ b _ h ↦ hc h]
  exact Finset.prod_congr rfl fun t ht ↦ by rw [hB'c t (Finset.mem_range.1 ht)]

/-- Digit cylinders are measurable. -/
theorem measurableSet_xor_cylinder {ι : Type*} (g : ℕ → ι) (c w : ℕ → Bool) (m : ℕ) :
    MeasurableSet {ω : ι → Bool | ∀ j < m, xor (c j) (ω (g j)) = w j} := by
  have : {ω : ι → Bool | ∀ j < m, xor (c j) (ω (g j)) = w j} =
      ⋂ (j : ℕ) (_ : j < m), (fun ω : ι → Bool => ω (g j)) ⁻¹' {xor (c j) (w j)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    cases c j <;> cases w j <;> cases ω (g j) <;> simp
  rw [this]
  exact MeasurableSet.iInter fun j => .iInter fun _ =>
    measurable_pi_apply (g j) (measurableSet_singleton _)

/-- **Digit cylinders have probability `2^{-m}`**: if the digits are `xor (c j) (ω (g j))` with
`g` injective, fixing the first `m` of them has probability `2^{-m}`. -/
theorem infinitePi_xor_cylinder {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g)
    (c w : ℕ → Bool) (m : ℕ) :
    Measure.infinitePi (fun _ : ι => fairCoin) {ω | ∀ j < m, xor (c j) (ω (g j)) = w j} =
      2⁻¹ ^ m := by
  have : {ω : ι → Bool | ∀ j < m, xor (c j) (ω (g j)) = w j} =
      {ω | ∀ j < m, ω (g j) ∈ ({xor (c j) (w j)} : Set Bool)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    cases c j <;> cases w j <;> cases ω (g j) <;> simp
  rw [this, infinitePi_setOf_forall_mem' fairCoin hg (fun t => measurableSet_singleton _) m]
  simp only [fairCoin_singleton, prod_const, card_range]

/-- The event `digitPrefix = d` is a digit cylinder. -/
theorem setOf_digitPrefix_eq {Ω : Type*} (D : Ω → ℕ → Bool) {m d : ℕ} (hd : d < 2 ^ m) :
    {ω | digitPrefix (D ω) m = d} = {ω | ∀ j < m, D ω j = d.testBit (m - 1 - j)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, digitPrefix_eq_iff, hd, true_and]

/-- **Uniform prefixes**: for digits `xor (c j) (ω (g j))` with injective `g`, each value
`d < 2^m` of the first `m` digits has probability `2^{-m}`. -/
theorem measure_digitPrefix_eq {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g) (c : ℕ → Bool)
    {m d : ℕ} (hd : d < 2 ^ m) :
    Measure.infinitePi (fun _ : ι => fairCoin)
      {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} = 2⁻¹ ^ m := by
  have hset : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} =
      {ω | ∀ j < m, xor (c j) (ω (g j)) = d.testBit (m - 1 - j)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, digitPrefix_eq_iff, hd, true_and]
  rw [hset]
  exact infinitePi_xor_cylinder hg c (fun j => d.testBit (m - 1 - j)) m

/-- The prefix events are measurable. -/
theorem measurableSet_digitPrefix_eq {ι : Type*} (g : ℕ → ι) (c : ℕ → Bool) (m d : ℕ) :
    MeasurableSet {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} := by
  by_cases hd : d < 2 ^ m
  · have hset : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} =
        {ω | ∀ j < m, xor (c j) (ω (g j)) = d.testBit (m - 1 - j)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, digitPrefix_eq_iff, hd, true_and]
    rw [hset]
    exact measurableSet_xor_cylinder g c (fun j => d.testBit (m - 1 - j)) m
  · have : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hd (h ▸ digitPrefix_lt _ m)
    rw [this]
    exact MeasurableSet.empty

/-- `P(digitPrefix < a) = a 2^{-m}` for `a ≤ 2^m`. -/
theorem measure_digitPrefix_lt {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g) (c : ℕ → Bool)
    {m a : ℕ} (ha : a ≤ 2 ^ m) :
    Measure.infinitePi (fun _ : ι => fairCoin)
      {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m < a} = a * 2⁻¹ ^ m := by
  have hset : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m < a} =
      ⋃ d ∈ range a, {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_range, exists_prop, exists_eq_right']
  rw [hset, measure_biUnion_finset]
  · rw [sum_congr rfl fun d hd => measure_digitPrefix_eq hg c
      (lt_of_lt_of_le (mem_range.1 hd) ha), sum_const, card_range, nsmul_eq_mul]
  · intro d _ d' _ hdd'
    exact Set.disjoint_left.2 fun ω h h' => hdd' (h.symm.trans h')
  · exact fun d _ => measurableSet_digitPrefix_eq g c m d

/-- `digitPrefix` is a measurable function of the digits. -/
theorem measurable_digitPrefix (m : ℕ) : Measurable fun b : ℕ → Bool => digitPrefix b m := by
  refine measurable_to_countable' fun d => ?_
  have := measurableSet_digitPrefix_eq (ι := ℕ) id (fun _ => false) m d
  simp only [Bool.false_xor, id] at this
  exact this

/-- `binaryVal` is measurable (for the product σ-algebra on `ℕ → Bool`). -/
theorem measurable_binaryVal : Measurable binaryVal := by
  have hf : ∀ m, Measurable fun b : ℕ → Bool => (digitPrefix b m : ℝ) / 2 ^ m := fun m =>
    (measurable_from_nat (f := fun d : ℕ => (d : ℝ) / 2 ^ m)).comp (measurable_digitPrefix m)
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun b => ?_)
  have hlo : ∀ m, binaryVal b - (1 / 2) ^ m ≤ (digitPrefix b m : ℝ) / 2 ^ m := fun m => by
    have := binaryVal_le_digitPrefix_add_one_div b m
    rw [add_div] at this
    rw [one_div_pow]
    linarith
  have hhi : ∀ m, (digitPrefix b m : ℝ) / 2 ^ m ≤ binaryVal b := digitPrefix_div_le_binaryVal b
  have hlim : Tendsto (fun m : ℕ => binaryVal b - (1 / 2 : ℝ) ^ m) atTop (𝓝 (binaryVal b)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_sub (binaryVal b)
    rwa [sub_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hhi

/-- Coordinates `ω ↦ xor (c j) (ω (g j))` give a measurable digit sequence. -/
theorem measurable_xor_digits {ι : Type*} (g : ℕ → ι) (c : ℕ → Bool) :
    Measurable fun ω : ι → Bool => fun j => xor (c j) (ω (g j)) :=
  measurable_pi_iff.2 fun j =>
    (measurable_from_top (f := fun x : Bool => xor (c j) x)).comp (measurable_pi_apply (g j))

/-- **Uniform law of a point with i.i.d. fair digits** (post #2's requirement (i)): if the
digits are `xor (c j) (ω (g j))` with `g` injective, the point `Σ_j d_j / 2^(j+1)` is
`U[0,1)`. Proof: `P(X ≤ x)` is squeezed between `⌊2^m x⌋ 2^{-m}` and `(⌊2^m x⌋ + 1) 2^{-m}`
for every `m`. -/
theorem map_binaryVal_xor_eq_uniformIco {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g)
    (c : ℕ → Bool) :
    (Measure.infinitePi fun _ : ι => fairCoin).map
      (fun ω => binaryVal fun j => xor (c j) (ω (g j))) = uniformIco := by
  set μ := Measure.infinitePi fun _ : ι => fairCoin with hμ
  set X : (ι → Bool) → ℝ := fun ω => binaryVal fun j => xor (c j) (ω (g j)) with hX
  have hXm : Measurable X := measurable_binaryVal.comp (measurable_xor_digits g c)
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hXm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hpre : X ⁻¹' Set.Iic x = {ω | X ω ≤ x} := rfl
  rw [hpre]
  rcases lt_or_ge x 0 with hx0 | hx0
  · have h1 : {ω | X ω ≤ x} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hx0 (binaryVal_nonneg _)
    have h2 : Set.Iic x ∩ Set.Ico (0 : ℝ) 1 = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_empty_iff_false,
        iff_false, not_and, not_lt]
      intro hy hy0
      linarith
    rw [h1, h2, measure_empty, measure_empty]
  rcases le_or_gt 1 x with hx1 | hx1
  · have h1 : {ω | X ω ≤ x} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (binaryVal_le_one _).trans hx1
    have h2 : Set.Iic x ∩ Set.Ico (0 : ℝ) 1 = Set.Ico 0 1 := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, and_iff_right_iff_imp]
      intro hy
      linarith [hy.2]
    rw [h1, h2, measure_univ, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
  have h2 : Set.Iic x ∩ Set.Ico (0 : ℝ) 1 = Set.Icc 0 x := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [h2, Real.volume_Icc, sub_zero]
  -- the squeeze, level by level
  have hfin : μ {ω | X ω ≤ x} ≠ ⊤ := measure_ne_top _ _
  have hbound : ∀ m : ℕ, |(μ {ω | X ω ≤ x}).toReal - x| ≤ (1 / 2) ^ m := by
    intro m
    set a := ⌊(2 : ℝ) ^ m * x⌋₊ with ha
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have ha1 : (a : ℝ) ≤ 2 ^ m * x := Nat.floor_le (by positivity)
    have ha2 : 2 ^ m * x < (a : ℝ) + 1 := Nat.lt_floor_add_one _
    have ham : a < 2 ^ m := by
      have : (a : ℝ) < 2 ^ m := lt_of_le_of_lt ha1 (by nlinarith)
      exact_mod_cast this
    -- `{prefix < a} ⊆ {X ≤ x} ⊆ {prefix < a + 1}`
    have hsub1 : {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m < a} ⊆ {ω | X ω ≤ x} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h := binaryVal_le_digitPrefix_add_one_div (fun j => xor (c j) (ω (g j))) m
      have hk : ((digitPrefix (fun j => xor (c j) (ω (g j))) m : ℕ) : ℝ) + 1 ≤ a := by
        exact_mod_cast hω
      refine h.trans ?_
      rw [div_le_iff₀ hp]
      linarith
    have hsub2 : {ω | X ω ≤ x} ⊆ {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m < a + 1} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      by_contra hcon
      have hk : (a : ℝ) + 1 ≤ ((digitPrefix (fun j => xor (c j) (ω (g j))) m : ℕ) : ℝ) := by
        exact_mod_cast (not_lt.1 hcon)
      have h := digitPrefix_div_le_binaryVal (fun j => xor (c j) (ω (g j))) m
      rw [div_le_iff₀ hp] at h
      have : X ω * 2 ^ m ≤ x * 2 ^ m := mul_le_mul_of_nonneg_right hω hp.le
      have hXω : X ω = binaryVal (fun j => xor (c j) (ω (g j))) := rfl
      rw [← hXω] at h
      nlinarith
    have hlo := measure_mono (μ := μ) hsub1
    have hhi := measure_mono (μ := μ) hsub2
    rw [measure_digitPrefix_lt hg c ham.le] at hlo
    rw [measure_digitPrefix_lt hg c ham] at hhi
    have e : ∀ b : ℕ, ((b : ENNReal) * 2⁻¹ ^ m).toReal = b / 2 ^ m := by
      intro b
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_ofNat, inv_pow, div_eq_mul_inv]
    have hlo' := ENNReal.toReal_mono hfin hlo
    have hhi' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))) hhi
    rw [e] at hlo' hhi'
    push_cast at hhi'
    rw [abs_le, one_div_pow]
    have h3 : (a : ℝ) / 2 ^ m ≤ x := by rw [div_le_iff₀ hp]; linarith
    have h4 : x < ((a : ℝ) + 1) / 2 ^ m := by rw [lt_div_iff₀ hp]; linarith
    rw [add_div] at hhi' h4
    constructor <;> linarith
  have heq : (μ {ω | X ω ≤ x}).toReal = x := by
    by_contra hne
    have hpos : 0 < |(μ {ω | X ω ≤ x}).toReal - x| := abs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
    linarith [hbound m]
  rw [show ENNReal.ofReal x = ENNReal.ofReal (μ {ω | X ω ≤ x}).toReal by rw [heq],
    ENNReal.ofReal_toReal hfin]

/-! ### The stacks under Owen scrambling and the digital shift -/

/-- The Owen coordinates of the digits of point `k` of stack `i` are distinct. -/
theorem owen_coord_injective (i : Fin n) (k : ℕ) :
    Function.Injective fun j : ℕ => (i, j, k % 2 ^ j) :=
  fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).1

/-- The digital-shift coordinates of the digits of a point of stack `i` are distinct. -/
theorem shift_coord_injective (i : Fin n) : Function.Injective fun j : ℕ => (i, j) :=
  fun _ _ h => (Prod.mk.inj h).2

/-- **Each Owen-scrambled stack point is `U[0,1)`** (post #2's requirement (i)). -/
theorem map_scrambledStack_owen (i : Fin n) (k : ℕ) :
    (owenMeasure n).map (fun ω => scrambledStack (owenTable ω) i k) = uniformIco :=
  map_binaryVal_xor_eq_uniformIco (owen_coord_injective i k) fun j => k.testBit j

/-- **Each digitally shifted stack point is `U[0,1)`**. -/
theorem map_scrambledStack_shift (i : Fin n) (k : ℕ) :
    (shiftMeasure n).map (fun ω => scrambledStack (shiftFlips ω) i k) = uniformIco :=
  map_binaryVal_xor_eq_uniformIco (shift_coord_injective i) fun j => k.testBit j

/-- Under Owen's measure, the first `m` scrambled digits of a stack point are uniform. -/
theorem owen_digitPrefix_eq (i : Fin n) (k : ℕ) {m d : ℕ} (hd : d < 2 ^ m) :
    owenMeasure n {ω | digitPrefix (scrambledDigit (owenTable ω i) k) m = d} = 2⁻¹ ^ m :=
  measure_digitPrefix_eq (owen_coord_injective i k) (fun j => k.testBit j) hd

/-- Under the digital shift, the first `m` scrambled digits of a stack point are uniform. -/
theorem shift_digitPrefix_eq (i : Fin n) (k : ℕ) {m d : ℕ} (hd : d < 2 ^ m) :
    shiftMeasure n {ω | digitPrefix (scrambledDigit (shiftFlips ω i) k) m = d} = 2⁻¹ ^ m :=
  measure_digitPrefix_eq (shift_coord_injective i) (fun j => k.testBit j) hd

/-- Owen stack points are measurable. -/
theorem measurable_scrambledStack_owen (i : Fin n) (k : ℕ) :
    Measurable fun ω : Fin n × ℕ × ℕ → Bool => scrambledStack (owenTable ω) i k :=
  measurable_binaryVal.comp (measurable_xor_digits (fun j => (i, j, k % 2 ^ j)) _)

/-- Digitally shifted stack points are measurable. -/
theorem measurable_scrambledStack_shift (i : Fin n) (k : ℕ) :
    Measurable fun ω : Fin n × ℕ → Bool => scrambledStack (shiftFlips ω) i k :=
  measurable_binaryVal.comp (measurable_xor_digits (fun j => (i, j)) _)

/-- **Digits with i.i.d. fair coins beyond every position are a.s. not eventually constant.** -/
theorem ae_notEventuallyConst_xor {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g)
    (c : ℕ → Bool) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ι => fairCoin),
      NotEventuallyConst fun j => xor (c j) (ω (g j)) := by
  set μ := Measure.infinitePi fun _ : ι => fairCoin
  -- for each start `J` and value `b`, `{∀ j ≥ J, digit = b}` is null
  have hnull : ∀ (J : ℕ) (b : Bool),
      μ {ω | ∀ j, J ≤ j → xor (c j) (ω (g j)) = b} = 0 := by
    intro J b
    have hg' : Function.Injective fun j => g (J + j) :=
      fun _ _ h => by have := hg h; omega
    have hle : ∀ M : ℕ, μ {ω | ∀ j, J ≤ j → xor (c j) (ω (g j)) = b} ≤ 2⁻¹ ^ M := by
      intro M
      rw [← infinitePi_xor_cylinder hg' (fun j => c (J + j)) (fun _ => b) M]
      exact measure_mono fun ω hω j _ => hω (J + j) (by omega)
    have hlim : Tendsto (fun M : ℕ => (2⁻¹ : ENNReal) ^ M) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    exact le_antisymm (ge_of_tendsto' hlim hle) (zero_le)
  have hsub : {ω : ι → Bool | ¬ NotEventuallyConst fun j => xor (c j) (ω (g j))} ⊆
      ⋃ (J : ℕ) (b : Bool), {ω | ∀ j, J ≤ j → xor (c j) (ω (g j)) = b} := by
    intro ω hω
    simp only [NotEventuallyConst, Set.mem_ofPred_eq, not_forall, not_and_or, not_exists] at hω
    obtain ⟨J, hJ | hJ⟩ := hω
    · refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨false, fun j hj => ?_⟩⟩
      have := (hJ j).resolve_left (not_not.2 hj)
      simpa using this
    · refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨true, fun j hj => ?_⟩⟩
      have := (hJ j).resolve_left (not_not.2 hj)
      simpa using this
  rw [ae_iff]
  exact measure_mono_null hsub (measure_iUnion_null fun J => measure_iUnion_null fun b =>
    hnull J b)

/-- **The good event has probability one under Owen scrambling.** -/
theorem ae_isGoodTable_owen (n : ℕ) : ∀ᵐ ω ∂owenMeasure n, IsGoodTable (owenTable ω) := by
  unfold IsGoodTable
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro k
  exact ae_notEventuallyConst_xor (owen_coord_injective i k) fun j => k.testBit j

/-- **The good event has probability one under the digital shift.** -/
theorem ae_isGoodTable_shift (n : ℕ) : ∀ᵐ ω ∂shiftMeasure n, IsGoodTable (shiftFlips ω) := by
  unfold IsGoodTable
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro k
  exact ae_notEventuallyConst_xor (shift_coord_injective i) fun j => k.testBit j

/-! ### Measurability of the path -/

/-- The first `T + 1` states of a stack path driven by a measurable family of stacks form a
random vector. -/
theorem measurable_stackPath_restrict_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measurable fun ω => fun t : Fin (T + 1) => stackPath P x₀ (V ω) t := by
  refine measurable_to_countable' fun s => ?_
  set s' : ℕ → Fin n := fun t => s ⟨min t T, by omega⟩ with hs'
  have hset : (fun ω => fun t : Fin (T + 1) => stackPath P x₀ (V ω) t) ⁻¹' {s} =
      {ω | s' 0 = x₀ ∧ ∀ t < T,
        step P (s' t) (V ω (s' t) (departureIndex s' t)) = s' (t + 1)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [← stackDrive_eq_iff]
    constructor
    · intro h t ht
      refine (congrFun h ⟨t, by omega⟩).trans ?_
      simp only [hs']
      congr 1
      ext
      simp only
      omega
    · intro h
      funext t
      refine (h t (by omega)).trans ?_
      simp only [hs']
      congr 1
      ext
      simp only
      omega
  rw [hset, Set.ofPred_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  have : {ω | ∀ t < T, step P (s' t) (V ω (s' t) (departureIndex s' t)) = s' (t + 1)} =
      ⋂ (t : ℕ) (_ : t < T), (fun ω => V ω (s' t) (departureIndex s' t)) ⁻¹'
        {u | step P (s' t) u = s' (t + 1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun t => .iInter fun _ =>
    hV _ _ (measurable_step P (s' t) (measurableSet_singleton _))

/-- Every function of the first `T + 1` states of the path is measurable. -/
theorem measurable_comp_stackPath_of {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {V : Ω → Fin n → ℕ → ℝ} (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ)
    (x₀ : Fin n) (T : ℕ) (F : (Fin (T + 1) → Fin n) → β) :
    Measurable fun ω => F fun t : Fin (T + 1) => stackPath P x₀ (V ω) t :=
  (measurable_of_countable F).comp (measurable_stackPath_restrict_of hV P x₀ T)

/-- **The path coordinates are random variables.** -/
theorem measurable_stackPath_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (t : ℕ) :
    Measurable fun ω => stackPath P x₀ (V ω) t :=
  measurable_comp_stackPath_of hV P x₀ t fun y => y (Fin.last t)

/-- **The occupation counts are random variables.** -/
theorem measurable_occCount_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (i : Fin n)
    (T : ℕ) : Measurable fun ω => occCount (stackPath P x₀ (V ω)) i T := by
  have h := measurable_comp_stackPath_of hV P x₀ T
    fun y => occCount (fun t => y ⟨min t T, by omega⟩) i T
  have e : (fun ω => occCount (stackPath P x₀ (V ω)) i T) = fun ω =>
      occCount (fun t => stackPath P x₀ (V ω) (⟨min t T, by omega⟩ : Fin (T + 1))) i T := by
    funext ω
    refine occCount_congr (fun t ht => ?_) i
    congr 1
    simp only
    omega
  rw [e]
  exact h

/-- **The transition counts are random variables.** -/
theorem measurable_transCount_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n)
    (i j : Fin n) (T : ℕ) : Measurable fun ω => transCount (stackPath P x₀ (V ω)) i j T := by
  have h := measurable_comp_stackPath_of hV P x₀ T
    fun y => transCount (fun t => y ⟨min t T, by omega⟩) i j T
  have e : (fun ω => transCount (stackPath P x₀ (V ω)) i j T) = fun ω =>
      transCount (fun t => stackPath P x₀ (V ω) (⟨min t T, by omega⟩ : Fin (T + 1))) i j T := by
    funext ω
    refine transCount_congr (fun t ht => ?_) i j
    congr 1
    simp only
    omega
  rw [e]
  exact h

end RQMCMarkov.ScrambledStacks
