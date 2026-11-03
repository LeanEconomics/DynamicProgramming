/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackNet
import ScrambledStacks.CltMDependent
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Path coins of a scrambled van der Corput stack (post #3, codes (ii) and (iii))

Post #3 drives a Markov chain by one scrambled Sobol (base-2 van der Corput) sequence per state,
randomised by a digital shift (code (ii)) or by Owen's nested scramble (code (iii)). For a
threshold `c ∈ [0,1)` (a cumulative transition probability) with binary digits `c_j`, the only
randomness that matters for the count `#{k < N : x_k ≤ c}` is carried by the **path coins**
`e_j = f j α_j`: the flips applied at the nodes `α_j` of the binary tree along the path of `c`
(`α_j` is the original `j`-digit prefix that the scramble sends to `c`'s first `j` digits).

## Main results

* `threshDigit c`: the binary digits of `c`; `digitPrefix_threshDigit` (`⌊2^m c⌋`),
  `binaryVal_threshDigit` (`= c`).
* `binaryVal_le_iff_of_firstDiff`, `binaryVal_le_iff_lexLeFrom`: comparing a binary expansion
  with `c` is lexicographic comparison of digits.
* `pathPrefix`, `pathCoin`; `tie_iff_mod_eq_pathPrefix`: the first `j` scrambled digits of point
  `k` equal `c`'s iff `k ≡ α_j (mod 2^j)`.
* `card_block_le_eq` (**per-block jump formula**, every flip table): in an aligned block of
  `2^m` indices, `#{x ≤ c} = ⌊2^m c⌋ + 1{x_{k*} ≤ c}` with `k* = a 2^m + α_m`.
* `LevelInd`, `scrambledVdc_levelPoint_le_iff`: the block term at level `m` is a fixed function
  of the path coins `e_m, e_{m+1}, …` and of the bits of `N` above `m` (tie cascades:
  `levelDigits N m e j = bit_j(levelBase N m) xor e_j`).
* `segErr_scrambledVdc_eq_sum_level` (**level decomposition**, every flip table):
  `#{k < N : x_k ≤ c} − N c = Σ_{m : bit m of N} (1{LevelInd} − {2^m c})` (`levelTerm`).
* `LexLeFromTrunc`, `LevelIndTrunc`, `levelValTrunc`, `LevelTie`,
  `levelVal_eq_trunc_of_not_tie`, `levelValTrunc_congr`: truncating every tie cascade at depth
  `L` changes the level term only on the tie event, and makes it a function of `e_m … e_{m+L-1}`.
* `levelInd_iff_binaryVal_le`: `LevelInd` holds iff the number formed by the level digits from
  depth `m` is `≤ {2^m c}` (so `P(LevelInd) = {2^m c}` under fair coins, `CltVariance`).
* `owenMeasure_pathCoins_cylinder`, `eq_shiftMeasure_of_cylinder` and `map_owenPathCoins`
  (**law equivalence**): the path coins of Owen-scrambled stacks are i.i.d. fair coins, i.e.
  have the law `shiftMeasure n` of the digital-shift flips (one threshold per state, any number
  of states); for the digital shift the path coins ARE the flips (`pathCoin_shiftTable`). Hence
  for chains with one jump per row (two states) the error of (ii) and (iii) is the same function
  of the same coin law, for every `T` (`CltVariance.IsPathCoinModel`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Digits of the threshold -/

/-- The binary digits of `c` (digit `j` is digit `j + 1` after the binary point). -/
noncomputable def threshDigit (c : ℝ) (j : ℕ) : Bool := decide (⌊2 ^ (j + 1) * c⌋₊ % 2 = 1)

/-- The first `m` digits of `c ∈ [0,1)` form `⌊2^m c⌋`. -/
theorem digitPrefix_threshDigit {c : ℝ} (hc1 : c < 1) (m : ℕ) :
    digitPrefix (threshDigit c) m = ⌊2 ^ m * c⌋₊ := by
  induction m with
  | zero =>
      rw [pow_zero, one_mul, Nat.floor_eq_zero.2 hc1]
      rfl
  | succ m ih =>
      change 2 * digitPrefix (threshDigit c) m + (if threshDigit c m then 1 else 0) = _
      rw [ih]
      have hdiv : ⌊2 ^ m * c⌋₊ = ⌊2 ^ (m + 1) * c⌋₊ / 2 := by
        have e : (2 : ℝ) ^ m * c = 2 ^ (m + 1) * c / ((2 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [e, Nat.floor_div_natCast]
      rw [hdiv, threshDigit]
      have h := Nat.div_add_mod ⌊2 ^ (m + 1) * c⌋₊ 2
      rcases Nat.mod_two_eq_zero_or_one ⌊2 ^ (m + 1) * c⌋₊ with h2 | h2
      · simp only [h2, zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
        omega
      · simp only [h2, decide_true, ite_true]
        omega

/-- `⌊2^{m+1} c⌋ = 2⌊2^m c⌋ + c_m`. -/
theorem floor_two_pow_succ_mul {c : ℝ} (hc1 : c < 1) (m : ℕ) :
    ⌊2 ^ (m + 1) * c⌋₊ = 2 * ⌊2 ^ m * c⌋₊ + if threshDigit c m then 1 else 0 := by
  rw [← digitPrefix_threshDigit hc1, ← digitPrefix_threshDigit hc1]
  rfl

/-- The binary expansion of the digits of `c ∈ [0,1)` is `c`. -/
theorem binaryVal_threshDigit {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    binaryVal (threshDigit c) = c := by
  have hb : ∀ m : ℕ, |binaryVal (threshDigit c) - c| ≤ 1 / 2 ^ m := by
    intro m
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have h1 := digitPrefix_div_le_binaryVal (threshDigit c) m
    have h2 := binaryVal_le_digitPrefix_add_one_div (threshDigit c) m
    rw [digitPrefix_threshDigit hc1] at h1 h2
    have h3 : (⌊2 ^ m * c⌋₊ : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
    have h4 : 2 ^ m * c < ⌊2 ^ m * c⌋₊ + 1 := Nat.lt_floor_add_one _
    have h3' : (⌊2 ^ m * c⌋₊ : ℝ) / 2 ^ m ≤ c := by rw [div_le_iff₀ hp]; linarith
    have h4' : c < ((⌊2 ^ m * c⌋₊ : ℝ) + 1) / 2 ^ m := by rw [lt_div_iff₀ hp]; linarith
    rw [abs_le]
    constructor
    · have : ((⌊2 ^ m * c⌋₊ : ℝ) + 1) / 2 ^ m = (⌊2 ^ m * c⌋₊ : ℝ) / 2 ^ m + 1 / 2 ^ m := by
        ring
      linarith
    · have : ((⌊2 ^ m * c⌋₊ : ℝ) + 1) / 2 ^ m = (⌊2 ^ m * c⌋₊ : ℝ) / 2 ^ m + 1 / 2 ^ m := by
        ring
      linarith
  by_contra hne
  have hpos : 0 < |binaryVal (threshDigit c) - c| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  have := hb m
  rw [one_div, ← inv_pow] at this
  rw [one_div] at hm
  linarith

/-- **First difference decides the comparison.** If the digits `d` agree with those of
`c ∈ [0,1)` before `τ` and differ at `τ`, then `binaryVal d ≤ c` iff `c`'s digit `τ` is `1`. -/
theorem binaryVal_le_iff_of_firstDiff {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {d : ℕ → Bool}
    {τ : ℕ} (htie : ∀ i < τ, d i = threshDigit c i) (hne : d τ ≠ threshDigit c τ) :
    binaryVal d ≤ c ↔ threshDigit c τ = true := by
  have hp : (0 : ℝ) < 2 ^ (τ + 1) := by positivity
  set P := digitPrefix (threshDigit c) τ with hPdef
  have hP : digitPrefix d τ = P := digitPrefix_congr htie
  have hF : ⌊2 ^ (τ + 1) * c⌋₊ = 2 * P + if threshDigit c τ then 1 else 0 := by
    rw [floor_two_pow_succ_mul hc1, hPdef, digitPrefix_threshDigit hc1]
  have hdP : digitPrefix d (τ + 1) = 2 * P + if d τ then 1 else 0 := by
    rw [← hP]
    rfl
  have h3 : (⌊2 ^ (τ + 1) * c⌋₊ : ℝ) ≤ 2 ^ (τ + 1) * c := Nat.floor_le (by positivity)
  have h4 : 2 ^ (τ + 1) * c < ⌊2 ^ (τ + 1) * c⌋₊ + 1 := Nat.lt_floor_add_one _
  cases hct : threshDigit c τ with
  | true =>
      have hdτ : d τ = false := by rw [hct] at hne; simpa using hne
      simp only [iff_true]
      have hu := binaryVal_le_digitPrefix_add_one_div d (τ + 1)
      rw [hdP, hdτ] at hu
      rw [hct] at hF
      simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at hu hF
      have e : ((2 * P : ℕ) : ℝ) + 1 = (⌊2 ^ (τ + 1) * c⌋₊ : ℝ) := by
        rw [hF]
        push_cast
        ring
      rw [e] at hu
      refine hu.trans ?_
      rw [div_le_iff₀ hp]
      linarith
  | false =>
      have hdτ : d τ = true := by rw [hct] at hne; simpa using hne
      simp only [Bool.false_eq_true, iff_false, not_le]
      have hl := digitPrefix_div_le_binaryVal d (τ + 1)
      rw [hdP, hdτ] at hl
      rw [hct] at hF
      simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at hl hF
      have e : ((2 * P + 1 : ℕ) : ℝ) = (⌊2 ^ (τ + 1) * c⌋₊ : ℝ) + 1 := by
        rw [hF]
        push_cast
        ring
      rw [e] at hl
      refine lt_of_lt_of_le ?_ hl
      rw [lt_div_iff₀ hp]
      linarith

/-- **Lexicographic order from level `m`**: at the first disagreement (at or after `m`) of `d`
with the digits `cb`, the digit of `cb` is `1` (or there is no disagreement). -/
def LexLeFrom (d cb : ℕ → Bool) (m : ℕ) : Prop :=
  ∀ τ, m ≤ τ → (∀ i, m ≤ i → i < τ → d i = cb i) → d τ ≠ cb τ → cb τ = true

/-- **Comparison is lexicographic.** If `d` agrees with the digits of `c ∈ [0,1)` before `m`,
then `binaryVal d ≤ c` iff `d ≤ c` lexicographically from level `m`. -/
theorem binaryVal_le_iff_lexLeFrom {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {d : ℕ → Bool}
    {m : ℕ} (htie : ∀ i < m, d i = threshDigit c i) :
    binaryVal d ≤ c ↔ LexLeFrom d (threshDigit c) m := by
  classical
  by_cases h : ∃ τ, d τ ≠ threshDigit c τ
  · set τ := Nat.find h with hτ
    have hτne : d τ ≠ threshDigit c τ := Nat.find_spec h
    have hbelow : ∀ i < τ, d i = threshDigit c i := fun i hi ↦ by
      by_contra hc
      exact Nat.find_min h hi hc
    have hmτ : m ≤ τ := by
      by_contra hc
      exact hτne (htie τ (by omega))
    rw [binaryVal_le_iff_of_firstDiff hc0 hc1 hbelow hτne]
    constructor
    · intro hct τ' hmτ' htie' hne'
      have hττ' : τ ≤ τ' := Nat.find_min' h hne'
      rcases hττ'.lt_or_eq with hlt | heq
      · exact absurd (htie' τ hmτ hlt) hτne
      · rw [← heq]
        exact hct
    · intro hlex
      exact hlex τ hmτ (fun i _ hi ↦ hbelow i hi) hτne
  · push Not at h
    have hd : d = threshDigit c := funext h
    rw [hd, binaryVal_threshDigit hc0 hc1]
    exact ⟨fun _ τ _ _ hne ↦ absurd rfl hne, fun _ ↦ le_rfl⟩

/-- `LexLeFrom` only depends on the digits up to the first disagreement. -/
theorem lexLeFrom_congr {d d' cb : ℕ → Bool} {m : ℕ}
    (h : ∀ j, m ≤ j → (∀ i, m ≤ i → i < j → d i = cb i) → d j = d' j) :
    LexLeFrom d cb m ↔ LexLeFrom d' cb m := by
  have htie : ∀ j, (∀ i, m ≤ i → i < j → d i = cb i) ↔ (∀ i, m ≤ i → i < j → d' i = cb i) := by
    intro j
    induction j with
    | zero => exact ⟨fun _ i _ hi ↦ absurd hi (Nat.not_lt_zero _),
        fun _ i _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ j ih =>
        constructor
        · intro hd i hmi hij
          rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
          · exact (ih.1 fun i' hm' hi' ↦ hd i' hm' (by omega)) i hmi hlt
          · subst heq
            rw [← h i hmi fun i' hm' hi' ↦ hd i' hm' (by omega)]
            exact hd i hmi (by omega)
        · intro hd i hmi hij
          rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
          · exact (ih.2 fun i' hm' hi' ↦ hd i' hm' (by omega)) i hmi hlt
          · subst heq
            have hprev : ∀ i', m ≤ i' → i' < i → d i' = cb i' :=
              ih.2 fun i' hm' hi' ↦ hd i' hm' (by omega)
            rw [h i hmi hprev]
            exact hd i hmi (by omega)
  constructor
  · intro hl τ hmτ ht hne
    have ht' := (htie τ).2 ht
    exact hl τ hmτ ht' (by rwa [h τ hmτ ht'])
  · intro hl τ hmτ ht hne
    exact hl τ hmτ ((htie τ).1 ht) (by rwa [← h τ hmτ ht])

/-! ### Path prefixes and path coins -/

/-- `k % 2^{j+1}` adds bit `j` of `k` to `k % 2^j`. -/
theorem mod_two_pow_succ_eq (k j : ℕ) :
    k % 2 ^ (j + 1) = k % 2 ^ j + 2 ^ j * (if k.testBit j then 1 else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ j) with h | h <;> simp [h]

/-- The **path prefix** `α_j`: the original `j`-digit prefix (as the residue `k % 2^j`) of the
indices whose first `j` scrambled digits are the digits `cb` of the threshold. -/
def pathPrefix (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => pathPrefix f cb j + 2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0)

/-- The **path coin** `e_j = f j α_j`: the flip at depth `j` on the path of the threshold. -/
def pathCoin (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (j : ℕ) : Bool := f j (pathPrefix f cb j)

/-- `α_j < 2^j`. -/
theorem pathPrefix_lt (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (j : ℕ) : pathPrefix f cb j < 2 ^ j := by
  induction j with
  | zero => exact Nat.one_pos
  | succ j ih =>
      change pathPrefix f cb j + 2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0)
        < 2 ^ (j + 1)
      rw [pow_succ]
      split_ifs <;> omega

/-- **Ties along the path.** The first `j` scrambled digits of index `k` are the threshold's
digits iff `k ≡ α_j (mod 2^j)`. -/
theorem tie_iff_mod_eq_pathPrefix (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (k : ℕ) (j : ℕ) :
    (∀ i < j, scrambledDigit f k i = cb i) ↔ k % 2 ^ j = pathPrefix f cb j := by
  induction j with
  | zero => exact ⟨fun _ ↦ by rw [pow_zero, Nat.mod_one]; rfl, fun _ i hi ↦ absurd hi (by omega)⟩
  | succ j ih =>
      have hrec := mod_two_pow_succ_eq k j
      have hα := pathPrefix_lt f cb j
      have hsucc : pathPrefix f cb (j + 1) = pathPrefix f cb j +
          2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0) := rfl
      constructor
      · intro h
        have h1 := ih.1 fun i hi ↦ h i (by omega)
        have h2 := h j (by omega)
        rw [scrambledDigit, h1] at h2
        have h3 : k.testBit j = xor (cb j) (f j (pathPrefix f cb j)) := by
          rw [← h2]
          cases k.testBit j <;> cases f j (pathPrefix f cb j) <;> rfl
        rw [hrec, h1, h3, hsucc]
      · intro h
        have hmod : k % 2 ^ j = pathPrefix f cb j := by
          have e1 : k % 2 ^ (j + 1) % 2 ^ j = k % 2 ^ j :=
            Nat.mod_mod_of_dvd k (pow_dvd_pow 2 (Nat.le_succ j))
          rw [h, hsucc] at e1
          rw [← e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hα]
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
        · exact (ih.2 hmod) i hlt
        · subst heq
          rw [hrec, hmod, hsucc] at h
          have hb : (if k.testBit i then 1 else 0) =
              (if xor (cb i) (f i (pathPrefix f cb i)) then 1 else 0) := by
            have hp : 0 < 2 ^ i := Nat.two_pow_pos i
            have := Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel h)
            exact this
          have hb' : k.testBit i = xor (cb i) (f i (pathPrefix f cb i)) := by
            revert hb
            cases k.testBit i <;> cases xor (cb i) (f i (pathPrefix f cb i)) <;> simp
          rw [scrambledDigit, hmod, hb']
          cases cb i <;> cases f i (pathPrefix f cb i) <;> rfl

/-- Points `a 2^m + α_m` lie on the path of the threshold to depth `m`. -/
theorem tie_of_mod {f : ℕ → ℕ → Bool} {cb : ℕ → Bool} {k m : ℕ}
    (hk : k % 2 ^ m = pathPrefix f cb m) : ∀ i < m, scrambledDigit f k i = cb i :=
  (tie_iff_mod_eq_pathPrefix f cb k m).2 hk

/-- `(2^m q + α) % 2^m = α` for `α < 2^m`. -/
theorem two_pow_mul_add_mod {m q α : ℕ} (hα : α < 2 ^ m) : (2 ^ m * q + α) % 2 ^ m = α := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hα]

/-- **Per-block jump formula** (every flip table). In the aligned block of indices
`a 2^m, …, a 2^m + 2^m − 1`, the number of points `≤ c` is `⌊2^m c⌋` plus the indicator of the
block's point `a 2^m + α_m` in the cell of `c`. -/
theorem card_block_le_eq (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (m : ℕ) :
    ∀ a : ℕ, ((range (2 ^ m)).filter fun r ↦ scrambledVdc f (a * 2 ^ m + r) ≤ c).card =
      ⌊2 ^ m * c⌋₊ +
        if scrambledVdc f (a * 2 ^ m + pathPrefix f (threshDigit c) m) ≤ c then 1 else 0 := by
  classical
  set cb := threshDigit c with hcb
  induction m with
  | zero =>
      intro a
      rw [show pathPrefix f cb 0 = 0 from rfl]
      simp only [pow_zero, one_mul, mul_one, Nat.floor_eq_zero.2 hc1, zero_add, range_one,
        filter_singleton, add_zero]
      split_ifs <;> rfl
  | succ m ih =>
      intro a
      set α := pathPrefix f cb m with hαdef
      have hα : α < 2 ^ m := pathPrefix_lt f cb m
      -- split the block into its two halves
      have hsplit : ((range (2 ^ (m + 1))).filter fun r ↦
            scrambledVdc f (a * 2 ^ (m + 1) + r) ≤ c).card =
            ((range (2 ^ m)).filter fun r ↦ scrambledVdc f ((2 * a) * 2 ^ m + r) ≤ c).card +
            ((range (2 ^ m)).filter fun r ↦ scrambledVdc f ((2 * a + 1) * 2 ^ m + r) ≤ c).card := by
        rw [card_filter, card_filter, card_filter, show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by ring,
          sum_range_add]
        congr 1
        · refine sum_congr rfl fun r _ ↦ ?_
          rw [show a * (2 ^ m + 2 ^ m) + r = 2 * a * 2 ^ m + r by ring]
        · refine sum_congr rfl fun r _ ↦ ?_
          rw [show a * (2 ^ m + 2 ^ m) + (2 ^ m + r) = (2 * a + 1) * 2 ^ m + r by ring]
      rw [hsplit, ih (2 * a), ih (2 * a + 1), floor_two_pow_succ_mul hc1, ← hcb]
      -- the two candidate points
      set k0 := 2 * a * 2 ^ m + α with hk0
      set k1 := (2 * a + 1) * 2 ^ m + α with hk1
      have hk0m : k0 % 2 ^ m = α := by
        rw [hk0, mul_comm (2 * a)]
        exact two_pow_mul_add_mod hα
      have hk1m : k1 % 2 ^ m = α := by
        rw [hk1, mul_comm (2 * a + 1)]
        exact two_pow_mul_add_mod hα
      have hb0 : k0.testBit m = false := by
        rw [hk0, mul_comm (2 * a), Nat.testBit_two_pow_mul_add _ hα]
        simp [Nat.testBit_zero]
      have hb1 : k1.testBit m = true := by
        rw [hk1, mul_comm (2 * a + 1), Nat.testBit_two_pow_mul_add _ hα]
        simp [Nat.testBit_zero]
      have hd0 : scrambledDigit f k0 m = f m α := by
        rw [scrambledDigit, hb0, hk0m, Bool.false_xor]
      have hd1 : scrambledDigit f k1 m = !f m α := by
        rw [scrambledDigit, hb1, hk1m, Bool.true_xor]
      have ht0 := tie_of_mod (f := f) (cb := cb) hk0m
      have ht1 := tie_of_mod (f := f) (cb := cb) hk1m
      have hsucc : pathPrefix f cb (m + 1) = α + 2 ^ m * (if xor (cb m) (f m α) then 1 else 0) :=
        rfl
      have hcb : ∀ k, (∀ i < m, scrambledDigit f k i = cb i) → scrambledDigit f k m ≠ cb m →
          (scrambledVdc f k ≤ c ↔ cb m = true) := fun k ht hne ↦
        binaryVal_le_iff_of_firstDiff hc0 hc1 ht hne
      cases hβ : xor (cb m) (f m α) with
      | false =>
          have hcm : cb m = f m α := by revert hβ; cases cb m <;> cases f m α <;> simp
          have hpt : a * 2 ^ (m + 1) + pathPrefix f cb (m + 1) = k0 := by
            rw [hsucc, hβ, hk0]
            simp only [Bool.false_eq_true, ite_false, mul_zero, add_zero]
            ring
          rw [hpt]
          have h1 := hcb k1 ht1 (by rw [hd1, hcm]; cases f m α <;> simp)
          by_cases hc : cb m = true
          · have hx : scrambledVdc f k1 ≤ c := h1.2 hc
            simp only [hx, hc, ite_true]
            omega
          · have hx : ¬ scrambledVdc f k1 ≤ c := fun h ↦ hc (h1.1 h)
            simp only [hx, hc, ite_false, Bool.false_eq_true]
            omega
      | true =>
          have hcm : cb m = !f m α := by revert hβ; cases cb m <;> cases f m α <;> simp
          have hpt : a * 2 ^ (m + 1) + pathPrefix f cb (m + 1) = k1 := by
            rw [hsucc, hβ, hk1]
            simp only [ite_true, mul_one]
            ring
          rw [hpt]
          have h0 := hcb k0 ht0 (by rw [hd0, hcm]; cases f m α <;> simp)
          by_cases hc : cb m = true
          · have hx : scrambledVdc f k0 ≤ c := h0.2 hc
            simp only [hx, hc, ite_true]
            omega
          · have hx : ¬ scrambledVdc f k0 ≤ c := fun h ↦ hc (h0.1 h)
            simp only [hx, hc, ite_false, Bool.false_eq_true]
            omega

/-! ### The level decomposition -/

/-- `N` with its bits `0, …, m` cleared: the start of the aligned block of bit `m` of `N`. -/
def levelBase (N m : ℕ) : ℕ := 2 ^ (m + 1) * (N / 2 ^ (m + 1))

/-- The digits of the level-`m` point beyond depth `m`, as long as it ties with the threshold:
the bits of `levelBase N m` flipped by the path coins `e`. -/
def levelDigits (N m : ℕ) (e : ℕ → Bool) (j : ℕ) : Bool := xor ((levelBase N m).testBit j) (e j)

/-- The level-`m` comparison as a function of the path coins: the block point of bit `m` of `N`
is `≤ c` iff its digits are lexicographically `≤` those of `c` from depth `m` on. -/
def LevelInd (cb : ℕ → Bool) (N m : ℕ) (e : ℕ → Bool) : Prop := LexLeFrom (levelDigits N m e) cb m

open Classical in
/-- The indicator of `LevelInd`, as a real number. -/
noncomputable def levelVal (cb : ℕ → Bool) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  if LevelInd cb N m e then 1 else 0

/-- The level term `1{LevelInd} − {2^m c}` of the local discrepancy. -/
noncomputable def levelTerm (c : ℝ) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  levelVal (threshDigit c) N m e - (2 ^ m * c - ⌊2 ^ m * c⌋₊)

/-- Bits at or above `m` of `levelBase N m + α`, `α < 2^m`, are those of `levelBase N m`. -/
theorem testBit_levelBase_add {N m α j : ℕ} (hα : α < 2 ^ m) (hj : m ≤ j) :
    (levelBase N m + α).testBit j = (levelBase N m).testBit j := by
  have e : levelBase N m = 2 ^ m * (2 * (N / 2 ^ (m + 1))) := by
    rw [levelBase, pow_succ]
    ring
  rw [e, Nat.testBit_two_pow_mul_add _ hα, ← add_zero (2 ^ m * (2 * (N / 2 ^ (m + 1)))),
    Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos m)]
  simp [Nat.not_lt.2 hj]

/-- `levelBase N m` is a multiple of `2^m`, so `(levelBase N m + α) % 2^m = α`. -/
theorem levelBase_add_mod {N m α : ℕ} (hα : α < 2 ^ m) : (levelBase N m + α) % 2 ^ m = α := by
  have e : levelBase N m = 2 ^ m * (2 * (N / 2 ^ (m + 1))) := by
    rw [levelBase, pow_succ]
    ring
  rw [e]
  exact two_pow_mul_add_mod hα

/-- **The level point and the path coins** (every flip table). The block point of bit `m` of `N`
is `≤ c` iff `LevelInd` holds for the path coins. -/
theorem scrambledVdc_levelPoint_le_iff (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (N m : ℕ) :
    scrambledVdc f (levelBase N m + pathPrefix f (threshDigit c) m) ≤ c ↔
      LevelInd (threshDigit c) N m (pathCoin f (threshDigit c)) := by
  set cb := threshDigit c with hcb
  set k := levelBase N m + pathPrefix f cb m with hk
  have hα := pathPrefix_lt f cb m
  have hkm : k % 2 ^ m = pathPrefix f cb m := levelBase_add_mod hα
  have htie := tie_of_mod (f := f) (cb := cb) hkm
  rw [scrambledVdc, binaryVal_le_iff_lexLeFrom hc0 hc1 htie]
  refine lexLeFrom_congr fun j hmj hj ↦ ?_
  have hall : ∀ i < j, scrambledDigit f k i = cb i := fun i hi ↦ by
    rcases lt_or_ge i m with h | h
    · exact htie i h
    · exact hj i h hi
  have hkj := (tie_iff_mod_eq_pathPrefix f cb k j).1 hall
  rw [scrambledDigit, hkj, levelDigits, hk, testBit_levelBase_add hα hmj]
  rfl

/-- `levelBase (2^M + N') m = 2^M + levelBase N' m` for `m < M`. -/
theorem levelBase_two_pow_add {M N' m : ℕ} (hm : m < M) :
    levelBase (2 ^ M + N') m = 2 ^ M + levelBase N' m := by
  have hM : 2 ^ M = 2 ^ (m + 1) * 2 ^ (M - (m + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  unfold levelBase
  rw [hM, Nat.mul_add_div (Nat.two_pow_pos _)]
  ring

/-- `levelBase N M = 0` for `N < 2^{M+1}`. -/
theorem levelBase_eq_zero {N M : ℕ} (hN : N < 2 ^ (M + 1)) : levelBase N M = 0 := by
  rw [levelBase, Nat.div_eq_of_lt hN, mul_zero]

/-- The level decomposition with a base point `B ≡ 0 (mod 2^M)`. -/
theorem segErr_eq_sum_levelPoint (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (M : ℕ) : ∀ B N : ℕ, 2 ^ M ∣ B → N < 2 ^ M →
      segErr (scrambledVdc f) c B N = ∑ m ∈ (range M).filter (fun m ↦ N.testBit m),
        ((if scrambledVdc f (B + levelBase N m + pathPrefix f (threshDigit c) m) ≤ c then 1 else 0)
          - (2 ^ m * c - ⌊2 ^ m * c⌋₊)) := by
  classical
  induction M with
  | zero =>
      intro B N _ hN
      have : N = 0 := by rw [pow_zero] at hN; omega
      subst this
      rw [segErr_zero, range_zero, filter_empty, sum_empty]
  | succ M ih =>
      intro B N hB hN
      have hB' : 2 ^ M ∣ B := dvd_trans (pow_dvd_pow 2 (Nat.le_succ M)) hB
      by_cases hbit : N.testBit M
      · have hge : 2 ^ M ≤ N := by
          by_contra h
          push Not at h
          rw [Nat.testBit_lt_two_pow h] at hbit
          exact absurd hbit (by simp)
        obtain ⟨N', rfl⟩ : ∃ N', N = 2 ^ M + N' := ⟨N - 2 ^ M, by omega⟩
        have hN' : N' < 2 ^ M := by rw [pow_succ] at hN; omega
        rw [segErr_add, ih (B + 2 ^ M) N' (dvd_add hB' dvd_rfl) hN', range_add_one,
          filter_insert]
        simp only [hbit, ite_true]
        rw [sum_insert (by simp)]
        -- the block of the top bit
        have hblk := card_block_le_eq f hc0 hc1 M (B / 2 ^ M)
        rw [Nat.div_mul_cancel hB'] at hblk
        rw [segErr_eq_card, hblk, levelBase_eq_zero hN, add_zero]
        have hfilt : (range M).filter (fun m ↦ (2 ^ M + N').testBit m) =
            (range M).filter (fun m ↦ N'.testBit m) :=
          filter_congr fun m hm ↦ by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hm)]
        rw [hfilt]
        have hsum : ∑ m ∈ (range M).filter (fun m ↦ N'.testBit m),
            ((if scrambledVdc f (B + levelBase (2 ^ M + N') m + pathPrefix f (threshDigit c) m)
              ≤ c then (1 : ℝ) else 0) - (2 ^ m * c - ⌊2 ^ m * c⌋₊)) =
            ∑ m ∈ (range M).filter (fun m ↦ N'.testBit m),
            ((if scrambledVdc f (B + 2 ^ M + levelBase N' m + pathPrefix f (threshDigit c) m)
              ≤ c then (1 : ℝ) else 0) - (2 ^ m * c - ⌊2 ^ m * c⌋₊)) :=
          sum_congr rfl fun m hm ↦ by
            rw [levelBase_two_pow_add (mem_range.1 (mem_filter.1 hm).1), ← add_assoc]
        rw [hsum]
        push_cast
        ring
      · have hlt : N < 2 ^ M := by
          by_contra h
          push Not at h
          obtain ⟨N', rfl⟩ : ∃ N', N = 2 ^ M + N' := ⟨N - 2 ^ M, by omega⟩
          have hN' : N' < 2 ^ M := by rw [pow_succ] at hN; omega
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hN'] at hbit
          exact hbit rfl
        rw [ih B N hB' hlt, range_add_one, filter_insert]
        simp only [hbit, Bool.false_eq_true, ite_false]

/-- **Level decomposition of the local discrepancy** (every flip table). For `N < 2^M`,
`#{k < N : x_k ≤ c} − N c = Σ_{m < M, bit m of N} levelTerm c N m e`, where `e` are the path
coins of the flip table. -/
theorem segErr_scrambledVdc_eq_sum_level (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) {N M : ℕ} (hN : N < 2 ^ M) :
    segErr (scrambledVdc f) c 0 N = ∑ m ∈ (range M).filter (fun m ↦ N.testBit m),
      levelTerm c N m (pathCoin f (threshDigit c)) := by
  rw [segErr_eq_sum_levelPoint f hc0 hc1 M 0 N (dvd_zero _) hN]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [levelTerm, levelVal, zero_add]
  congr 1
  have hiff := scrambledVdc_levelPoint_le_iff f hc0 hc1 N m
  by_cases h : LevelInd (threshDigit c) N m (pathCoin f (threshDigit c))
  · simp only [h, hiff.2 h, ite_true]
  · have h' : ¬ scrambledVdc f (levelBase N m + pathPrefix f (threshDigit c) m) ≤ c :=
      fun h'' ↦ h (hiff.1 h'')
    simp only [h, h', ite_false]

/-! ### Truncated tie cascades -/

/-- `LexLeFrom` truncated at depth `L`: only disagreements in `[m, m + L)` count (no
disagreement there counts as `≤`). -/
def LexLeFromTrunc (d cb : ℕ → Bool) (m L : ℕ) : Prop :=
  ∀ τ, m ≤ τ → τ < m + L → (∀ i, m ≤ i → i < τ → d i = cb i) → d τ ≠ cb τ → cb τ = true

/-- At the first disagreement `τ₀ ≥ m`, `LexLeFrom` is decided by `cb τ₀`. -/
theorem lexLeFrom_iff_of_firstBreak {d cb : ℕ → Bool} {m τ₀ : ℕ} (hm : m ≤ τ₀)
    (ht : ∀ i, m ≤ i → i < τ₀ → d i = cb i) (hb : d τ₀ ≠ cb τ₀) :
    LexLeFrom d cb m ↔ cb τ₀ = true := by
  constructor
  · intro h
    exact h τ₀ hm ht hb
  · intro h τ hmτ htτ hbτ
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · exact absurd (ht τ hmτ hlt) hbτ
    · rwa [heq]
    · exact absurd (htτ τ₀ hm hgt) hb

/-- At the first disagreement `τ₀ ∈ [m, m + L)`, the truncation is decided by `cb τ₀`. -/
theorem lexLeFromTrunc_iff_of_firstBreak {d cb : ℕ → Bool} {m τ₀ L : ℕ} (hm : m ≤ τ₀)
    (hL : τ₀ < m + L) (ht : ∀ i, m ≤ i → i < τ₀ → d i = cb i) (hb : d τ₀ ≠ cb τ₀) :
    LexLeFromTrunc d cb m L ↔ cb τ₀ = true := by
  constructor
  · intro h
    exact h τ₀ hm hL ht hb
  · intro h τ hmτ _ htτ hbτ
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · exact absurd (ht τ hmτ hlt) hbτ
    · rwa [heq]
    · exact absurd (htτ τ₀ hm hgt) hb

/-- A disagreement in `[m, m + L)` has a first one. -/
theorem exists_firstBreak {d cb : ℕ → Bool} {m L : ℕ}
    (h : ¬ ∀ j, m ≤ j → j < m + L → d j = cb j) :
    ∃ τ₀, m ≤ τ₀ ∧ τ₀ < m + L ∧ (∀ i, m ≤ i → i < τ₀ → d i = cb i) ∧ d τ₀ ≠ cb τ₀ := by
  classical
  have hex : ∃ τ, m ≤ τ ∧ τ < m + L ∧ d τ ≠ cb τ := by
    by_contra hc
    push Not at hc
    exact h fun j hm hj ↦ hc j hm hj
  have hex' : ∃ τ, m ≤ τ ∧ d τ ≠ cb τ := let ⟨τ, h1, _, h3⟩ := hex; ⟨τ, h1, h3⟩
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, ?_, fun i hmi hi ↦ ?_, (Nat.find_spec hex').2⟩
  · obtain ⟨τ, h1, h2, h3⟩ := hex
    exact lt_of_le_of_lt (Nat.find_min' hex' ⟨h1, h3⟩) h2
  · by_contra hc
    exact Nat.find_min hex' hi ⟨hmi, hc⟩

/-- **Truncation is exact off the tie event**: if `d` disagrees with `cb` somewhere in
`[m, m + L)`, then `LexLeFrom` and its depth-`L'` truncation agree for every `L' ≥ L`. -/
theorem lexLeFrom_iff_trunc {d cb : ℕ → Bool} {m L L' : ℕ} (hLL : L ≤ L')
    (h : ¬ ∀ j, m ≤ j → j < m + L → d j = cb j) :
    (LexLeFrom d cb m ↔ LexLeFromTrunc d cb m L') ∧
      (LexLeFromTrunc d cb m L ↔ LexLeFromTrunc d cb m L') := by
  obtain ⟨τ₀, hm, hL, ht, hb⟩ := exists_firstBreak h
  rw [lexLeFrom_iff_of_firstBreak hm ht hb, lexLeFromTrunc_iff_of_firstBreak hm (by omega) ht hb,
    lexLeFromTrunc_iff_of_firstBreak hm hL ht hb]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The level comparison truncated at depth `L`. -/
def LevelIndTrunc (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) : Prop :=
  LexLeFromTrunc (levelDigits N m e) cb m L

open Classical in
/-- The indicator of `LevelIndTrunc`. -/
noncomputable def levelValTrunc (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) : ℝ :=
  if LevelIndTrunc cb N m L e then 1 else 0

/-- The level tie event: the level-`m` point ties with the threshold on `[m, m + L)`. -/
def LevelTie (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) : Prop :=
  ∀ j, m ≤ j → j < m + L → levelDigits N m e j = cb j

/-- Off the tie event the truncated and full indicators agree. -/
theorem levelVal_eq_trunc_of_not_tie {cb : ℕ → Bool} {N m L L' : ℕ} {e : ℕ → Bool}
    (hLL : L ≤ L') (h : ¬ LevelTie cb N m L e) :
    levelVal cb N m e = levelValTrunc cb N m L' e ∧
      levelValTrunc cb N m L e = levelValTrunc cb N m L' e := by
  have hh := lexLeFrom_iff_trunc hLL h
  constructor
  · unfold levelVal levelValTrunc LevelInd LevelIndTrunc
    by_cases h1 : LexLeFromTrunc (levelDigits N m e) cb m L'
    · simp only [h1, hh.1.2 h1, ite_true]
    · have h2 : ¬ LexLeFrom (levelDigits N m e) cb m := fun h' ↦ h1 (hh.1.1 h')
      simp only [h1, h2, ite_false]
  · unfold levelValTrunc LevelIndTrunc
    by_cases h1 : LexLeFromTrunc (levelDigits N m e) cb m L'
    · simp only [h1, hh.2.2 h1, ite_true]
    · have h2 : ¬ LexLeFromTrunc (levelDigits N m e) cb m L := fun h' ↦ h1 (hh.2.1 h')
      simp only [h1, h2, ite_false]

/-- The truncated indicator depends only on the coins in `[m, m + L)`. -/
theorem levelValTrunc_congr (cb : ℕ → Bool) (N m L : ℕ) {e e' : ℕ → Bool}
    (h : ∀ j, m ≤ j → j < m + L → e j = e' j) :
    levelValTrunc cb N m L e = levelValTrunc cb N m L e' := by
  have hd : ∀ j, m ≤ j → j < m + L → levelDigits N m e j = levelDigits N m e' j :=
    fun j hm hj ↦ by rw [levelDigits, levelDigits, h j hm hj]
  have hiff : LevelIndTrunc cb N m L e ↔ LevelIndTrunc cb N m L e' := by
    unfold LevelIndTrunc LexLeFromTrunc
    constructor
    · intro h' τ hm hL ht hb
      refine h' τ hm hL (fun i hmi hi ↦ ?_) (by rwa [hd τ hm hL])
      rw [hd i hmi (by omega)]
      exact ht i hmi hi
    · intro h' τ hm hL ht hb
      refine h' τ hm hL (fun i hmi hi ↦ ?_) (by rwa [← hd τ hm hL])
      rw [← hd i hmi (by omega)]
      exact ht i hmi hi
  unfold levelValTrunc
  by_cases h1 : LevelIndTrunc cb N m L e
  · simp only [h1, hiff.1 h1, ite_true]
  · have h2 : ¬ LevelIndTrunc cb N m L e' := fun h' ↦ h1 (hiff.2 h')
    simp only [h1, h2, ite_false]

/-- The level indicator through the value of the shifted digits: `LevelInd` holds iff the
binary number formed by the level digits from depth `m` on is `≤ {2^m c}`. -/
theorem levelInd_iff_binaryVal_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (e : ℕ → Bool) :
    LevelInd (threshDigit c) N m e ↔
      binaryVal (fun j ↦ levelDigits N m e (j + m)) ≤ 2 ^ m * c - ⌊2 ^ m * c⌋₊ := by
  classical
  set d : ℕ → Bool := fun j ↦ if j < m then threshDigit c j else levelDigits N m e j with hd
  have htie : ∀ i < m, d i = threshDigit c i := fun i hi ↦ by simp [hd, hi]
  have h1 := binaryVal_le_iff_lexLeFrom hc0 hc1 htie
  have h2 : LexLeFrom d (threshDigit c) m ↔ LevelInd (threshDigit c) N m e :=
    lexLeFrom_congr fun j hj _ ↦ by simp [hd, Nat.not_lt.2 hj]
  have h3 := binaryVal_eq_digitPrefix_add d m
  have h4 : digitPrefix d m = ⌊2 ^ m * c⌋₊ := by
    rw [digitPrefix_congr htie, digitPrefix_threshDigit hc1]
  have h5 : (fun j ↦ d (j + m)) = fun j ↦ levelDigits N m e (j + m) := by
    funext j
    simp [hd]
  rw [h4, h5] at h3
  rw [← h2, ← h1, h3, div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-! ### The law of the path coins -/

/-- The path prefix recomputed from the path coins. -/
def coinPrefix (cb e : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => coinPrefix cb e j + 2 ^ j * (if xor (cb j) (e j) then 1 else 0)

/-- The path prefix is determined by the earlier path coins. -/
theorem pathPrefix_eq_coinPrefix (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (j : ℕ) :
    pathPrefix f cb j = coinPrefix cb (pathCoin f cb) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change pathPrefix f cb j + 2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0) =
        coinPrefix cb (pathCoin f cb) j + 2 ^ j * (if xor (cb j) (pathCoin f cb j) then 1 else 0)
      rw [← ih]
      rfl

/-- `coinPrefix cb e j` depends only on `e` below `j`. -/
theorem coinPrefix_congr (cb : ℕ → Bool) {e e' : ℕ → Bool} {j : ℕ} (h : ∀ i < j, e i = e' i) :
    coinPrefix cb e j = coinPrefix cb e' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change coinPrefix cb e j + 2 ^ j * (if xor (cb j) (e j) then 1 else 0) =
        coinPrefix cb e' j + 2 ^ j * (if xor (cb j) (e' j) then 1 else 0)
      rw [ih fun i hi ↦ h i (by omega), h j (by omega)]

/-- **Digital shift: the path coins are the flips.** -/
theorem pathCoin_shiftTable (e cb : ℕ → Bool) : pathCoin (shiftTable e) cb = e := rfl

variable {n : ℕ}

/-- The path coins of Owen-scrambled stacks, state `i` with threshold digits `cb i`. -/
def owenPathCoins (cb : Fin n → ℕ → Bool) (ω : Fin n × ℕ × ℕ → Bool) : Fin n × ℕ → Bool :=
  fun p ↦ pathCoin (owenTable ω p.1) (cb p.1) p.2

/-- The Owen coordinates of depth `< M` and prefix `< 2^M`. -/
def owenBox (n M : ℕ) : Finset (Fin n × ℕ × ℕ) := univ ×ˢ (range M ×ˢ range (2 ^ M))

/-- Path prefixes to depth `M` only use coordinates in `owenBox n M`. -/
theorem pathPrefix_owen_congr (cb : ℕ → Bool) (i : Fin n) {M : ℕ} {ω ω' : Fin n × ℕ × ℕ → Bool}
    (h : ∀ q ∈ owenBox n M, ω q = ω' q) :
    ∀ j ≤ M, pathPrefix (owenTable ω i) cb j = pathPrefix (owenTable ω' i) cb j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj' := ih (by omega)
      change pathPrefix (owenTable ω i) cb j +
          2 ^ j * (if xor (cb j) (ω (i, j, pathPrefix (owenTable ω i) cb j)) then 1 else 0) =
        pathPrefix (owenTable ω' i) cb j +
          2 ^ j * (if xor (cb j) (ω' (i, j, pathPrefix (owenTable ω' i) cb j)) then 1 else 0)
      rw [← hj', h (i, j, pathPrefix (owenTable ω i) cb j)]
      simp only [owenBox, mem_product, mem_univ, mem_range, true_and]
      refine ⟨by omega, lt_of_lt_of_le (pathPrefix_lt _ cb j) ?_⟩
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Path coins of depth `< M` only use coordinates in `owenBox n M`. -/
theorem owenPathCoins_congr (cb : Fin n → ℕ → Bool) {M : ℕ} {ω ω' : Fin n × ℕ × ℕ → Bool}
    (h : ∀ q ∈ owenBox n M, ω q = ω' q) (i : Fin n) {j : ℕ} (hj : j < M) :
    owenPathCoins cb ω (i, j) = owenPathCoins cb ω' (i, j) := by
  change ω (i, j, pathPrefix (owenTable ω i) (cb i) j) =
    ω' (i, j, pathPrefix (owenTable ω' i) (cb i) j)
  rw [pathPrefix_owen_congr (cb i) i h j hj.le, h]
  simp only [owenBox, mem_product, mem_univ, mem_range, true_and]
  exact ⟨hj, lt_of_lt_of_le (pathPrefix_lt _ _ j) (Nat.pow_le_pow_right (by norm_num) hj.le)⟩

/-- The Owen path coins are measurable. -/
theorem measurable_owenPathCoins (cb : Fin n → ℕ → Bool) : Measurable (owenPathCoins cb) := by
  refine measurable_pi_iff.2 fun p ↦ ?_
  have hloc : IsLocal (fun ω ↦ owenPathCoins cb ω p) (owenBox n (p.2 + 1)) :=
    fun ω ω' h ↦ owenPathCoins_congr cb h p.1 (Nat.lt_succ_self p.2)
  exact hloc.measurable

/-- Sets depending on disjoint finite sets of coordinates are independent under a product of
probability measures. -/
theorem infinitePi_inter_of_local {ι α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] [Nonempty α] (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    {A B : Set (ι → α)} {S T : Finset ι}
    (hA : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (hB : ∀ ω ω', (∀ i ∈ T, ω i = ω' i) → (ω ∈ B ↔ ω' ∈ B)) (hST : Disjoint S T) :
    Measure.infinitePi ν (A ∩ B) = Measure.infinitePi ν A * Measure.infinitePi ν B := by
  classical
  have hF : IsLocal (fun ω ↦ decide (ω ∈ A)) S := fun ω ω' h ↦ by
    simp only [decide_eq_decide]
    exact hA ω ω' h
  have hG : IsLocal (fun ω ↦ decide (ω ∈ B)) T := fun ω ω' h ↦ by
    simp only [decide_eq_decide]
    exact hB ω ω' h
  have hind := IsLocal.indepFun ν hF hG hST
  have h := hind.measure_inter_preimage_eq_mul {true} {true} (measurableSet_singleton _)
    (measurableSet_singleton _)
  have eA : (fun ω ↦ decide (ω ∈ A)) ⁻¹' {true} = A := by ext ω; simp
  have eB : (fun ω ↦ decide (ω ∈ B)) ⁻¹' {true} = B := by ext ω; simp
  rwa [eA, eB] at h

/-- **Owen path coins: cylinder probabilities.** The first `M` path coins of every state take
any prescribed values with probability `2^{-nM}`. -/
theorem owenMeasure_pathCoins_cylinder (cb : Fin n → ℕ → Bool) (b : Fin n × ℕ → Bool) (M : ℕ) :
    owenMeasure n {ω | ∀ i, ∀ j < M, owenPathCoins cb ω (i, j) = b (i, j)} = 2⁻¹ ^ (n * M) := by
  classical
  induction M with
  | zero =>
      have : {ω : Fin n × ℕ × ℕ → Bool | ∀ i, ∀ j < 0, owenPathCoins cb ω (i, j) = b (i, j)} =
          Set.univ := by
        ext ω
        simp
      rw [this, measure_univ, mul_zero, pow_zero]
  | succ M ih =>
      set a : Fin n → ℕ := fun i ↦ coinPrefix (cb i) (fun j ↦ b (i, j)) M with ha
      set E := {ω : Fin n × ℕ × ℕ → Bool | ∀ i, ∀ j < M, owenPathCoins cb ω (i, j) = b (i, j)}
        with hE
      set T : Finset (Fin n × ℕ × ℕ) := univ.image fun i ↦ (i, M, a i) with hT
      set F := Set.pi (T : Set (Fin n × ℕ × ℕ)) fun q ↦ ({b (q.1, M)} : Set Bool) with hF
      have hsplit : {ω : Fin n × ℕ × ℕ → Bool |
          ∀ i, ∀ j < M + 1, owenPathCoins cb ω (i, j) = b (i, j)} = E ∩ F := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hE, hF, Set.mem_pi, hT, coe_image,
          coe_univ, Set.image_univ, Set.mem_range, forall_exists_index, Set.mem_singleton_iff]
        constructor
        · intro h
          refine ⟨fun i j hj ↦ h i j (by omega), ?_⟩
          rintro q i rfl
          have hpre : pathPrefix (owenTable ω i) (cb i) M = a i := by
            rw [pathPrefix_eq_coinPrefix, ha]
            exact coinPrefix_congr (cb i) fun j hj ↦ h i j (by omega)
          have := h i M (by omega)
          change ω (i, M, pathPrefix (owenTable ω i) (cb i) M) = b (i, M) at this
          rw [hpre] at this
          exact this
        · rintro ⟨hE', hF'⟩ i j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
          · exact hE' i j hlt
          · have hpre : pathPrefix (owenTable ω i) (cb i) j = a i := by
              rw [pathPrefix_eq_coinPrefix, ha]
              exact coinPrefix_congr (cb i) fun j' hj' ↦ hE' i j' hj'
            change ω (i, j, pathPrefix (owenTable ω i) (cb i) j) = b (i, j)
            rw [hpre]
            exact hF' _ i rfl
      have hEloc : ∀ ω ω', (∀ q ∈ owenBox n M, ω q = ω' q) → (ω ∈ E ↔ ω' ∈ E) := by
        intro ω ω' h
        simp only [hE, Set.mem_ofPred_eq]
        constructor
        · intro h' i j hj
          rw [← owenPathCoins_congr cb h i hj]
          exact h' i j hj
        · intro h' i j hj
          rw [owenPathCoins_congr cb h i hj]
          exact h' i j hj
      have hFloc : ∀ ω ω', (∀ q ∈ T, ω q = ω' q) → (ω ∈ F ↔ ω' ∈ F) := by
        intro ω ω' h
        simp only [hF, Set.mem_pi]
        constructor
        · intro h' q hq
          rw [← h q hq]
          exact h' q hq
        · intro h' q hq
          rw [h q hq]
          exact h' q hq
      have hdisj : Disjoint (owenBox n M) T := by
        refine Finset.disjoint_left.2 fun q hq hqT ↦ ?_
        simp only [owenBox, mem_product, mem_univ, mem_range, true_and] at hq
        obtain ⟨i, _, rfl⟩ := mem_image.1 hqT
        exact absurd hq.1 (lt_irrefl M)
      have hFm : owenMeasure n F = 2⁻¹ ^ n := by
        rw [hF, Measure.infinitePi_pi _ fun q _ ↦ measurableSet_singleton _]
        simp only [fairCoin_singleton, prod_const]
        rw [hT, card_image_of_injective _ fun i i' h ↦ by simpa using congrArg Prod.fst h,
          card_univ, Fintype.card_fin]
      have hmul := infinitePi_inter_of_local (fun _ : Fin n × ℕ × ℕ ↦ fairCoin) hEloc hFloc hdisj
      change owenMeasure n _ = _
      rw [hsplit, hmul]
      change owenMeasure n E * owenMeasure n F = _
      rw [ih, hFm, ← pow_add, mul_add, mul_one]

/-- A depth-`M` cylinder of `Fin n × ℕ → Bool` as a box. -/
theorem cylinder_eq_pi (b : Fin n × ℕ → Bool) (M : ℕ) :
    {w : Fin n × ℕ → Bool | ∀ i, ∀ j < M, w (i, j) = b (i, j)} =
      Set.pi ((univ ×ˢ range M : Finset (Fin n × ℕ)) : Set (Fin n × ℕ))
        fun q ↦ ({b q} : Set Bool) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_pi, coe_product, coe_univ, coe_range, Set.mem_prod,
    Set.mem_univ, Set.mem_Iio, true_and, Set.mem_singleton_iff, Prod.forall]

/-- Cylinders are measurable. -/
theorem measurableSet_cylinder (b : Fin n × ℕ → Bool) (M : ℕ) :
    MeasurableSet {w : Fin n × ℕ → Bool | ∀ i, ∀ j < M, w (i, j) = b (i, j)} := by
  rw [cylinder_eq_pi]
  exact MeasurableSet.pi (Set.to_countable _) fun _ _ ↦ measurableSet_singleton _

/-- Cylinder probabilities of the digital-shift flips. -/
theorem shiftMeasure_cylinder (b : Fin n × ℕ → Bool) (M : ℕ) :
    shiftMeasure n {w | ∀ i, ∀ j < M, w (i, j) = b (i, j)} = 2⁻¹ ^ (n * M) := by
  classical
  rw [cylinder_eq_pi, Measure.infinitePi_pi _ fun q _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const, card_product, card_univ, Fintype.card_fin,
    card_range]

/-- A probability measure on `Fin n × ℕ → Bool` whose depth-`M` cylinders all have probability
`2^{-nM}` is the product of fair coins `shiftMeasure n`. -/
theorem eq_shiftMeasure_of_cylinder {μ : Measure (Fin n × ℕ → Bool)} [IsProbabilityMeasure μ]
    (h : ∀ (b : Fin n × ℕ → Bool) (M : ℕ),
      μ {w | ∀ i, ∀ j < M, w (i, j) = b (i, j)} = 2⁻¹ ^ (n * M)) :
    μ = shiftMeasure n := by
  classical
  have hmap : ∀ M, μ.map (Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M)) =
      (shiftMeasure n).map (Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M)) := by
    intro M
    refine Measure.ext_of_singleton fun g ↦ ?_
    rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g),
      Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g)]
    set b : Fin n × ℕ → Bool := fun q ↦
      if hq : q ∈ (univ ×ˢ range M : Finset (Fin n × ℕ)) then g ⟨q, hq⟩ else false with hb
    have e : Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M) ⁻¹'
        ({g} : Set ((univ ×ˢ range M : Finset (Fin n × ℕ)) → Bool)) =
        {w : Fin n × ℕ → Bool | ∀ i, ∀ j < M, w (i, j) = b (i, j)} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl i j hj
        have hq : (i, j) ∈ (univ ×ˢ range M : Finset (Fin n × ℕ)) := by simp [hj]
        simp only [hb, hq, dite_true, Finset.restrict]
      · intro hw
        funext q
        have hq := q.2
        simp only [mem_product, mem_univ, mem_range, true_and] at hq
        have := hw q.1.1 q.1.2 hq
        simp only [hb, q.2, dite_true] at this
        exact this
    rw [e, h b M, shiftMeasure_cylinder]
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  set M := s.sup (fun q ↦ q.2) + 1 with hM
  have hsS : ∀ q ∈ s, q ∈ (univ ×ˢ range M : Finset (Fin n × ℕ)) := fun q hq ↦ by
    simp only [mem_product, mem_univ, mem_range, true_and, hM]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun q : Fin n × ℕ ↦ q.2) hq)
  set E : Set ((univ ×ˢ range M : Finset (Fin n × ℕ)) → Bool) :=
    {g | ∀ q (hq : q ∈ s), g ⟨q, hsS q hq⟩ ∈ t q} with hE
  have hpre : Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M) ⁻¹' E =
      Set.pi (s : Set (Fin n × ℕ)) t := by
    ext w
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, Set.mem_pi, mem_coe, Finset.restrict]
  have hEm : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← hpre, ← Measure.map_apply (Finset.measurable_restrict _) hEm, hmap M,
    Measure.map_apply (Finset.measurable_restrict _) hEm, hpre,
    Measure.infinitePi_pi _ fun q _ ↦ ht q]

/-- **Law equivalence of the path coins.** Under Owen's measure the path coins
`e_{i,j} = f_i j α_{i,j}` of all states form i.i.d. fair coins: their law is the law
`shiftMeasure n` of the digital-shift flips. -/
theorem map_owenPathCoins (cb : Fin n → ℕ → Bool) :
    (owenMeasure n).map (owenPathCoins cb) = shiftMeasure n := by
  refine eq_shiftMeasure_of_cylinder fun b M ↦ ?_
  rw [Measure.map_apply (measurable_owenPathCoins cb) (measurableSet_cylinder b M)]
  exact owenMeasure_pathCoins_cylinder cb b M

end RQMCMarkov.ScrambledStacks
