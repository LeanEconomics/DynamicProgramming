/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackDefs

/-!
# Three states: Owen's scramble and the digital shift give different path laws (post #3)

Post #3 treats codes (ii) (one Sobol sequence per state with a random digital shift) and (iii)
(Owen scrambling) together. For two-state chains their path laws coincide (`CltPathBits`,
`map_owenPathCoins`: one threshold per row, and the path coins of Owen's scramble are i.i.d.
fair). With two thresholds in a row this fails: the two jump paths of the binary tree share the
digital-shift flips at every depth, but use independent Owen flips once they split.

**Counterexample.** The three-state chain with every row `(1/4, 1/2, 1/4)` (`threeChain`),
started in state `0`. The cylinder "stay in `0`, then move to `1`" (`StayThenMove`) uses the
first two points of stack `0`: `x₀ ≤ 1/4` and `1/4 < x₁ ≤ 3/4`.
* Digital shift: `x₁ = x₀ + 1/2` whenever `x₀ < 1/2`, so the event is `{x₀ ≤ 1/4}`:
  probability `1/4` (`shiftMeasure_stayThenMove`).
* Owen: `x₁`'s first digit is the complement of `x₀`'s, its other digits are fresh flips, so the
  event is three fair coins: probability `1/8` (`owenMeasure_stayThenMove`), which is also the
  Markov (MC) probability `p₀₀ p₀₁`.
Hence `owen_ne_shift_stayThenMove`: the path laws of (ii) and (iii) differ for three states.
The values were checked by simulation (4·10⁵ replications: `0.2501` vs `0.1253`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-- The three-state chain whose rows are all `(1/4, 1/2, 1/4)`. -/
noncomputable def threeChain : Fin 3 → Fin 3 → ℝ := fun _ j ↦ if j = 1 then 1 / 2 else 1 / 4

theorem isStochastic_threeChain : IsStochastic threeChain where
  nonneg i j := by unfold threeChain; split_ifs <;> norm_num
  sum_eq_one i := by
    rw [Fin.sum_univ_three]
    simp [threeChain]
    norm_num

/-- `step` for the rows `(1/4, 1/2, 1/4)`: state `0` iff `u ≤ 1/4`. -/
theorem threeChain_step_eq_zero_iff (i : Fin 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    step threeChain i u = 0 ↔ u ≤ 1 / 4 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h := step_zero isStochastic_threeChain.nonneg i
    exact ⟨fun _ ↦ by norm_num, fun _ ↦ Fin.ext h⟩
  · have h := step_eq_iff isStochastic_threeChain i 0 ⟨hpos, hu.2⟩
    have h1 : cumProb threeChain i ((0 : Fin 3) : ℕ) = 0 := cumProb_zero threeChain i
    have h2 : cumProb threeChain i (((0 : Fin 3) : ℕ) + 1) = 1 / 4 := by
      rw [cumProb_succ, h1, zero_add]
      simp [threeChain]
    rw [h1, h2] at h
    exact h.trans ⟨fun h' ↦ h'.2, fun h' ↦ ⟨hpos, h'⟩⟩

/-- `step` for the rows `(1/4, 1/2, 1/4)`: state `1` iff `1/4 < u ≤ 3/4`. -/
theorem threeChain_step_eq_one_iff (i : Fin 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    step threeChain i u = 1 ↔ 1 / 4 < u ∧ u ≤ 3 / 4 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h := step_zero isStochastic_threeChain.nonneg i
    constructor
    · intro h1
      rw [h1] at h
      exact absurd h (by decide)
    · intro h1
      norm_num at h1
  · have h := step_eq_iff isStochastic_threeChain i 1 ⟨hpos, hu.2⟩
    have h1 : cumProb threeChain i ((1 : Fin 3) : ℕ) = 1 / 4 := by
      have := cumProb_succ threeChain i 0
      simp only [Fin.val_zero, zero_add, cumProb_zero] at this
      change cumProb threeChain i 1 = 1 / 4
      rw [this]
      simp [threeChain]
    have h2 : cumProb threeChain i (((1 : Fin 3) : ℕ) + 1) = 3 / 4 := by
      rw [cumProb_succ, h1]
      simp [threeChain]
      norm_num
    rw [h1, h2] at h
    exact h

/-- The cylinder "start in `0`, stay in `0`, then move to `1`". -/
def StayThenMove (f : Fin 3 → ℕ → ℕ → Bool) : Prop :=
  stackPath threeChain 0 (scrambledStack f) 1 = 0 ∧ stackPath threeChain 0 (scrambledStack f) 2 = 1

/-- The cylinder in terms of the first two points of stack `0`. -/
theorem stayThenMove_iff (f : Fin 3 → ℕ → ℕ → Bool) :
    StayThenMove f ↔ scrambledVdc (f 0) 0 ≤ 1 / 4 ∧
      1 / 4 < scrambledVdc (f 0) 1 ∧ scrambledVdc (f 0) 1 ≤ 3 / 4 := by
  set x := stackPath threeChain 0 (scrambledStack f) with hx
  have hv : ∀ i k, scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 := scrambledStack_mem_Icc f
  have h1 : x 1 = step threeChain 0 (scrambledStack f 0 0) := by
    rw [hx]
    change stackDrive (step threeChain) 0 (scrambledStack f) (0 + 1) = _
    rw [stackDrive_succ, stackDrive_zero]
    rfl
  have hd1 : x 1 = 0 → departureIndex x 1 = 1 := fun h ↦ by
    unfold departureIndex
    rw [h, occCount_succ, occCount_zero]
    simp [hx, stackDrive_zero]
  have h2 : x 2 = step threeChain (x 1) (scrambledStack f (x 1) (departureIndex x 1)) := by
    rw [hx]
    change stackDrive (step threeChain) 0 (scrambledStack f) (1 + 1) = _
    rw [stackDrive_succ]
  unfold StayThenMove
  rw [← hx, h1, threeChain_step_eq_zero_iff 0 (hv 0 0)]
  constructor
  · rintro ⟨ha, hb⟩
    have hx1 : x 1 = 0 := by rw [h1, threeChain_step_eq_zero_iff 0 (hv 0 0)]; exact ha
    rw [h2, hx1, hd1 hx1, threeChain_step_eq_one_iff 0 (hv 0 1)] at hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    have hx1 : x 1 = 0 := by rw [h1, threeChain_step_eq_zero_iff 0 (hv 0 0)]; exact ha
    refine ⟨ha, ?_⟩
    rw [h2, hx1, hd1 hx1, threeChain_step_eq_one_iff 0 (hv 0 1)]
    exact hb

/-- For digits that are not eventually constant, `binaryVal d ≤ 1/4` iff the first two digits
are `0`. -/
theorem binaryVal_le_quarter_iff {d : ℕ → Bool} (hd : NotEventuallyConst d) :
    binaryVal d ≤ 1 / 4 ↔ d 0 = false ∧ d 1 = false := by
  have h1 := digitPrefix_div_lt_binaryVal hd 2
  have h2 := binaryVal_lt_digitPrefix_add_one_div hd 2
  have e : digitPrefix d 2 = 2 * (if d 0 then 1 else 0) + (if d 1 then 1 else 0) := by
    change 2 * (2 * 0 + (if d 0 then 1 else 0)) + (if d 1 then 1 else 0) = _
    ring
  rw [e] at h1 h2
  cases h0 : d 0 <;> cases h1' : d 1 <;> simp only [h0, h1'] at h1 h2 <;> norm_num at h1 h2 ⊢ <;>
    linarith

/-- For digits that are not eventually constant with first digit `1`,
`1/4 < binaryVal d ≤ 3/4` iff the second digit is `0`. -/
theorem binaryVal_mem_middle_iff {d : ℕ → Bool} (hd : NotEventuallyConst d) (h0 : d 0 = true) :
    (1 / 4 < binaryVal d ∧ binaryVal d ≤ 3 / 4) ↔ d 1 = false := by
  have h1 := digitPrefix_div_lt_binaryVal hd 2
  have h2 := binaryVal_lt_digitPrefix_add_one_div hd 2
  have e : digitPrefix d 2 = 2 * (if d 0 then 1 else 0) + (if d 1 then 1 else 0) := by
    change 2 * (2 * 0 + (if d 0 then 1 else 0)) + (if d 1 then 1 else 0) = _
    ring
  rw [e, h0] at h1 h2
  cases h1' : d 1
  · simp only [h1', ite_true, Bool.false_eq_true, ite_false] at h1 h2
    norm_num at h1 h2
    simp only [iff_true]
    exact ⟨by linarith, by linarith⟩
  · simp only [h1', ite_true] at h1 h2
    norm_num at h1 h2
    simp only [Bool.true_eq_false, iff_false, not_and, not_le]
    intro _
    linarith

/-- The first digit of point `1` is the complement of that of point `0` (same node), its other
digits use the nodes of prefix `1`. -/
theorem scrambledDigit_one (f : ℕ → ℕ → Bool) (j : ℕ) :
    scrambledDigit f 1 j = if j = 0 then !f 0 0 else f j 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [scrambledDigit]
  · have h1 : (1 : ℕ).testBit j = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hj.ne')
    have h2 : 1 % 2 ^ j = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow hj.ne')
    simp [scrambledDigit, h1, h2, hj.ne']

/-- Point `0` of a stack has the flips at prefix `0` as digits. -/
theorem scrambledDigit_zero (f : ℕ → ℕ → Bool) (j : ℕ) : scrambledDigit f 0 j = f j 0 := by
  simp [scrambledDigit]

/-- On the good event the cylinder is: the digits `0, 1` of point `0` and the digit `1` of
point `1` are `0`, the digit `0` of point `1` being the complement of that of point `0`. -/
theorem stayThenMove_iff_digits {f : Fin 3 → ℕ → ℕ → Bool} (hf : IsGoodTable f) :
    StayThenMove f ↔ f 0 0 0 = false ∧ f 0 1 0 = false ∧ f 0 1 1 = false := by
  rw [stayThenMove_iff]
  have hg0 := hf 0 0
  have hg1 := hf 0 1
  rw [scrambledVdc, binaryVal_le_quarter_iff hg0, scrambledDigit_zero, scrambledDigit_zero]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    have h0 : scrambledDigit (f 0) 1 0 = true := by rw [scrambledDigit_one]; simp [ha]
    have := (binaryVal_mem_middle_iff hg1 h0).1 hc
    rw [scrambledDigit_one] at this
    exact ⟨ha, hb, by simpa using this⟩
  · rintro ⟨ha, hb, hc⟩
    have h0 : scrambledDigit (f 0) 1 0 = true := by rw [scrambledDigit_one]; simp [ha]
    refine ⟨⟨ha, hb⟩, (binaryVal_mem_middle_iff hg1 h0).2 ?_⟩
    rw [scrambledDigit_one]
    simpa using hc

/-- **Owen's scramble**: the cylinder has probability `1/8` (`= p₀₀ p₀₁`, as for i.i.d.
driving). -/
theorem owenMeasure_stayThenMove :
    owenMeasure 3 {ω | StayThenMove (owenTable ω)} = 1 / 8 := by
  classical
  have hae : {ω : Fin 3 × ℕ × ℕ → Bool | StayThenMove (owenTable ω)} =ᵐ[owenMeasure 3]
      Set.pi (({(0, 0, 0), (0, 1, 0), (0, 1, 1)} : Finset (Fin 3 × ℕ × ℕ)) : Set _)
        fun _ ↦ ({false} : Set Bool) := by
    filter_upwards [ae_isGoodTable_owen 3] with ω hω
    simp only [eq_iff_iff]
    rw [stayThenMove_iff_digits hω]
    simp [owenTable]
  rw [measure_congr hae, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const]
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp), card_singleton, one_div,
    ← ENNReal.inv_pow]
  norm_num

/-- **Digital shift**: the cylinder has probability `1/4`. -/
theorem shiftMeasure_stayThenMove :
    shiftMeasure 3 {ω | StayThenMove (shiftFlips ω)} = 1 / 4 := by
  classical
  have hae : {ω : Fin 3 × ℕ → Bool | StayThenMove (shiftFlips ω)} =ᵐ[shiftMeasure 3]
      Set.pi (({(0, 0), (0, 1)} : Finset (Fin 3 × ℕ)) : Set _)
        fun _ ↦ ({false} : Set Bool) := by
    filter_upwards [ae_isGoodTable_shift 3] with ω hω
    simp only [eq_iff_iff]
    rw [stayThenMove_iff_digits hω]
    simp [shiftFlips, shiftTable]
  rw [measure_congr hae, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const]
  rw [card_insert_of_notMem (by simp), card_singleton, one_div, ← ENNReal.inv_pow]
  norm_num

/-- **Correction**: for three states the path laws of codes (ii) and (iii) differ. -/
theorem owen_ne_shift_stayThenMove :
    owenMeasure 3 {ω | StayThenMove (owenTable ω)} ≠
      shiftMeasure 3 {ω | StayThenMove (shiftFlips ω)} := by
  rw [owenMeasure_stayThenMove, shiftMeasure_stayThenMove, one_div, one_div, Ne,
    inv_inj]
  norm_num

end RQMCMarkov.ScrambledStacks
