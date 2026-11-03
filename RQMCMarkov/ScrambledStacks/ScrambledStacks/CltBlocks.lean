/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Aligned dyadic blocks: prefix and segment bounds (for post #3)

Post #3, codes (ii) and (iii): one scrambled base-2 van der Corput (one-dimensional Sobol)
sequence per state drives the chain by the stack rule. The first `2^m` points of any aligned
block of indices `a·2^m, …, (a+1)·2^m − 1` of such a sequence put exactly one point in each
dyadic cell of length `2^{-m}`, for every flip table. Hence, for a threshold `c ∈ [0,1)`, the
block's contribution to the local discrepancy `Σ_k (1{x_k ≤ c} − c)` is
`1{x* ≤ c} − {2^m c}`, where `x*` is the block's point in the cell of `c`: it lies in `[−1, 1]`.

This module is model-free: it works with any real sequence `F : ℕ → ℝ` (the partial sums of the
local discrepancy) whose increments over aligned blocks are bounded by `B`, and with any
sequence `x` with the aligned-block property.

## Main results

* `AlignedBlockBound F B`: `|F((a+1)2^m) − F(a 2^m)| ≤ B` for all `m, a`.
* `abs_sub_alignedPrefix_le`: a prefix of length `r < 2^m` of an aligned block contributes at
  most `B·m` (binary expansion of `r`).
* `abs_sub_le_of_le_add_pow`: `|F N' − F N| ≤ B(2m+1)` when `N ≤ N' ≤ N + 2^m`.
* `abs_sub_le_log` (**segment lemma**): `|F(N+L) − F N| ≤ B(2⌊log₂ L⌋ + 3)`.
* `abs_sub_zero_le_log`: `|F N − F 0| ≤ B(⌊log₂ N⌋ + 1)`.
* `card_le_add_frac_eq` (**per-block jump formula**, abstract): if the `2^m` points
  `x (a 2^m + r)`, `r < 2^m`, lie one in each dyadic cell `[j/2^m, (j+1)/2^m)`, then
  `#{r : x (a 2^m + r) ≤ c} − 2^m c = 1{x* ≤ c} − {2^m c}` with `x*` the point in the cell of
  `c`; `alignedBlockBound_of_cells`: such sequences satisfy `AlignedBlockBound` with `B = 1`.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset

/-- **Aligned-block bound.** The increments of `F` over every aligned dyadic block of indices
`[a 2^m, (a+1) 2^m)` are bounded by `B`. -/
def AlignedBlockBound (F : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ m a : ℕ, |F ((a + 1) * 2 ^ m) - F (a * 2 ^ m)| ≤ B

/-- The block bound is nonnegative. -/
theorem AlignedBlockBound.nonneg {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) : 0 ≤ B :=
  (abs_nonneg _).trans (hF 0 0)

/-- **Prefix of an aligned block.** A prefix of length `r < 2^m` of the aligned block starting at
`a 2^m` changes `F` by at most `B m`. -/
theorem abs_sub_alignedPrefix_le {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (m : ℕ) :
    ∀ a r : ℕ, r < 2 ^ m → |F (a * 2 ^ m + r) - F (a * 2 ^ m)| ≤ B * m := by
  induction m with
  | zero =>
      intro a r hr
      have hr0 : r = 0 := by
        rw [pow_zero] at hr
        omega
      rw [hr0, add_zero, sub_self, abs_zero, Nat.cast_zero, mul_zero]
  | succ m ih =>
      intro a r hr
      have hB := hF.nonneg
      have h2 : a * 2 ^ (m + 1) = (2 * a) * 2 ^ m := by ring
      rw [h2]
      by_cases hrm : r < 2 ^ m
      · refine (ih (2 * a) r hrm).trans ?_
        push_cast
        nlinarith
      · obtain ⟨r', rfl⟩ : ∃ r', r = 2 ^ m + r' := ⟨r - 2 ^ m, by omega⟩
        have hr' : r' < 2 ^ m := by
          rw [pow_succ] at hr
          omega
        have e1 : 2 * a * 2 ^ m + (2 ^ m + r') = (2 * a + 1) * 2 ^ m + r' := by ring
        rw [e1]
        have k1 := ih (2 * a + 1) r' hr'
        have k2 := hF m (2 * a)
        calc |F ((2 * a + 1) * 2 ^ m + r') - F (2 * a * 2 ^ m)|
            = |(F ((2 * a + 1) * 2 ^ m + r') - F ((2 * a + 1) * 2 ^ m)) +
                (F ((2 * a + 1) * 2 ^ m) - F (2 * a * 2 ^ m))| := by ring_nf
          _ ≤ |F ((2 * a + 1) * 2 ^ m + r') - F ((2 * a + 1) * 2 ^ m)| +
                |F ((2 * a + 1) * 2 ^ m) - F (2 * a * 2 ^ m)| := abs_add_le _ _
          _ ≤ B * m + B := add_le_add k1 k2
          _ = B * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Two nearby indices.** If `N ≤ N' ≤ N + 2^m` then `|F N' − F N| ≤ B (2m + 1)`. -/
theorem abs_sub_le_of_le_add_pow {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) {m N N' : ℕ}
    (h1 : N ≤ N') (h2 : N' ≤ N + 2 ^ m) : |F N' - F N| ≤ B * (2 * m + 1) := by
  have hB := hF.nonneg
  have hp : 0 < 2 ^ m := Nat.two_pow_pos m
  set a := N / 2 ^ m with ha
  set r := N % 2 ^ m with hr
  have hN : N = a * 2 ^ m + r := by rw [ha, hr, mul_comm]; exact (Nat.div_add_mod N _).symm
  have hrlt : r < 2 ^ m := Nat.mod_lt _ hp
  have hpre := abs_sub_alignedPrefix_le hF m a r hrlt
  rw [← hN] at hpre
  by_cases hN' : N' < (a + 1) * 2 ^ m
  · have hpre' := abs_sub_alignedPrefix_le hF m a (N' - a * 2 ^ m) (by
      rw [add_mul, one_mul] at hN'
      omega)
    have e : a * 2 ^ m + (N' - a * 2 ^ m) = N' := by omega
    rw [e] at hpre'
    calc |F N' - F N| = |(F N' - F (a * 2 ^ m)) - (F N - F (a * 2 ^ m))| := by ring_nf
      _ ≤ |F N' - F (a * 2 ^ m)| + |F N - F (a * 2 ^ m)| := abs_sub _ _
      _ ≤ B * m + B * m := add_le_add hpre' hpre
      _ ≤ B * (2 * m + 1) := by nlinarith
  · push Not at hN'
    have hlt : N' - (a + 1) * 2 ^ m < 2 ^ m := by
      rw [add_mul, one_mul] at hN' ⊢
      omega
    have hpre' := abs_sub_alignedPrefix_le hF m (a + 1) (N' - (a + 1) * 2 ^ m) hlt
    have e : (a + 1) * 2 ^ m + (N' - (a + 1) * 2 ^ m) = N' := by omega
    rw [e] at hpre'
    have hblk := hF m a
    calc |F N' - F N| = |(F N' - F ((a + 1) * 2 ^ m)) + (F ((a + 1) * 2 ^ m) - F (a * 2 ^ m))
          - (F N - F (a * 2 ^ m))| := by ring_nf
      _ ≤ |F N' - F ((a + 1) * 2 ^ m)| + |F ((a + 1) * 2 ^ m) - F (a * 2 ^ m)|
          + |F N - F (a * 2 ^ m)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ B * m + B + B * m := by gcongr
      _ = B * (2 * m + 1) := by ring

/-- **Segment lemma.** For an aligned-block-bounded `F`, a segment of `L` indices changes `F` by
at most `B (2 ⌊log₂ L⌋ + 3)`. -/
theorem abs_sub_le_log {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (N L : ℕ) :
    |F (N + L) - F N| ≤ B * (2 * Nat.log 2 L + 3) := by
  have hL : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have h := abs_sub_le_of_le_add_pow hF (m := Nat.log 2 L + 1) (N := N) (N' := N + L)
    (Nat.le_add_right N L) (by omega)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- The segment lemma for two indices in either order (`N' - N + (N - N')` is `|N' − N|`). -/
theorem abs_sub_le_log_dist {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (N N' : ℕ) :
    |F N' - F N| ≤ B * (2 * Nat.log 2 (N' - N + (N - N')) + 3) := by
  rcases le_total N N' with h | h
  · have e : N' - N + (N - N') = N' - N := by omega
    have := abs_sub_le_log hF N (N' - N)
    rwa [Nat.add_sub_cancel' h, ← e] at this
  · have e : N' - N + (N - N') = N - N' := by omega
    have := abs_sub_le_log hF N' (N - N')
    rw [Nat.add_sub_cancel' h, abs_sub_comm, ← e] at this
    exact this

/-- **Global bound.** `|F N − F 0| ≤ B (⌊log₂ N⌋ + 1)`. -/
theorem abs_sub_zero_le_log {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (N : ℕ) :
    |F N - F 0| ≤ B * (Nat.log 2 N + 1) := by
  have hN : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h := abs_sub_alignedPrefix_le hF (Nat.log 2 N + 1) 0 N hN
  rw [zero_mul, zero_add] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Per-block jump formula (abstract).** Let the `2^m` points `x (a 2^m + r)`, `r < 2^m`, of
an aligned block lie one in each dyadic cell: `r ↦ ⌊2^m x (a 2^m + r)⌋₊` is a bijection onto
`{0, …, 2^m − 1}`, with all points in `[0,1)`. Let `r*` be the index of the point in the cell of
`c ∈ [0,1)`. Then `#{r < 2^m : x (a 2^m + r) ≤ c} = ⌊2^m c⌋₊ + 1{x(a 2^m + r*) ≤ c}`. -/
theorem card_le_add_frac_eq {x : ℕ → ℝ} {m a rs : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hx0 : ∀ r < 2 ^ m, 0 ≤ x (a * 2 ^ m + r))
    (hinj : ∀ r < 2 ^ m, ∀ r' < 2 ^ m,
      ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ = ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r')⌋₊ → r = r')
    (hlt : ∀ r < 2 ^ m, ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ < 2 ^ m)
    (hrs : rs < 2 ^ m) (hcell : ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + rs)⌋₊ = ⌊(2 : ℝ) ^ m * c⌋₊) :
    ((range (2 ^ m)).filter fun r ↦ x (a * 2 ^ m + r) ≤ c).card =
      ⌊(2 : ℝ) ^ m * c⌋₊ + if x (a * 2 ^ m + rs) ≤ c then 1 else 0 := by
  classical
  set g : ℕ → ℕ := fun r ↦ ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ with hg
  set j0 := ⌊(2 : ℝ) ^ m * c⌋₊ with hj0
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  -- membership: `x ≤ c` iff the cell is below that of `c`, or it is `c`'s cell and `x ≤ c`
  have key : ∀ r < 2 ^ m,
      (x (a * 2 ^ m + r) ≤ c ↔ g r < j0 ∨ (r = rs ∧ x (a * 2 ^ m + rs) ≤ c)) := by
    intro r hr
    have hx := hx0 r hr
    constructor
    · intro hle
      have hmono : g r ≤ j0 := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle hp.le)
      rcases hmono.lt_or_eq with h | h
      · exact Or.inl h
      · right
        have := hinj r hr rs hrs (h.trans hcell.symm)
        exact ⟨this, this ▸ hle⟩
    · rintro (h | ⟨rfl, h⟩)
      · have h1 : (2 : ℝ) ^ m * x (a * 2 ^ m + r) < g r + 1 := Nat.lt_floor_add_one _
        have h2 : ((g r : ℕ) : ℝ) + 1 ≤ j0 := by exact_mod_cast h
        have h3 : (j0 : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
        have : (2 : ℝ) ^ m * x (a * 2 ^ m + r) ≤ 2 ^ m * c := by linarith
        exact le_of_mul_le_mul_left this hp
      · exact h
  have hfilter : (range (2 ^ m)).filter (fun r ↦ x (a * 2 ^ m + r) ≤ c) =
      ((range (2 ^ m)).filter fun r ↦ g r < j0) ∪
        (if x (a * 2 ^ m + rs) ≤ c then {rs} else ∅) := by
    ext r
    simp only [mem_filter, mem_range, mem_union]
    constructor
    · rintro ⟨hr, h⟩
      rcases (key r hr).1 h with h' | ⟨rfl, h'⟩
      · exact Or.inl ⟨hr, h'⟩
      · right
        simp [h']
    · rintro (⟨hr, h⟩ | h)
      · exact ⟨hr, (key r hr).2 (Or.inl h)⟩
      · by_cases hc : x (a * 2 ^ m + rs) ≤ c
        · simp only [hc, ite_true, mem_singleton] at h
          subst h
          exact ⟨hrs, hc⟩
        · simp [hc] at h
  have hdisj : Disjoint ((range (2 ^ m)).filter fun r ↦ g r < j0)
      (if x (a * 2 ^ m + rs) ≤ c then {rs} else ∅) := by
    by_cases hc : x (a * 2 ^ m + rs) ≤ c
    · simp only [hc, ite_true, disjoint_singleton_right, mem_filter, mem_range, not_and,
        not_lt]
      intro _
      rw [hg]
      exact hcell.ge
    · simp [hc]
  -- the cells below `c`'s: `g` is a bijection from `{r : g r < j0}` onto `range j0`
  have hj0lt : j0 < 2 ^ m := by
    have : (2 : ℝ) ^ m * c < 2 ^ m := by nlinarith
    have h := Nat.floor_lt (by positivity : (0 : ℝ) ≤ 2 ^ m * c) |>.2
      (by exact_mod_cast this : (2 : ℝ) ^ m * c < ((2 ^ m : ℕ) : ℝ))
    exact h
  have hcard : ((range (2 ^ m)).filter fun r ↦ g r < j0).card = j0 := by
    have hbij : ((range (2 ^ m)).filter fun r ↦ g r < j0).card = (range j0).card := by
      refine card_bij (fun r _ ↦ g r) ?_ ?_ ?_
      · intro r hr
        simp only [mem_filter] at hr
        exact mem_range.2 hr.2
      · intro r hr r' hr' h
        simp only [mem_filter, mem_range] at hr hr'
        exact hinj r hr.1 r' hr'.1 h
      · -- surjectivity: `g` maps `range (2^m)` injectively into `range (2^m)`, so onto
        intro j hj
        have hsurj : (range (2 ^ m)).image g = range (2 ^ m) := by
          refine eq_of_subset_of_card_le ?_ ?_
          · intro y hy
            obtain ⟨r, hr, rfl⟩ := mem_image.1 hy
            exact mem_range.2 (hlt r (mem_range.1 hr))
          · rw [card_image_of_injOn]
            intro r hr r' hr' h
            exact hinj r (mem_range.1 hr) r' (mem_range.1 hr') h
        have hjm : j ∈ (range (2 ^ m)).image g := by
          rw [hsurj]
          exact mem_range.2 ((mem_range.1 hj).trans hj0lt)
        obtain ⟨r, hr, hrj⟩ := mem_image.1 hjm
        refine ⟨r, ?_, hrj⟩
        simp only [mem_filter]
        exact ⟨hr, hrj ▸ mem_range.1 hj⟩
    rw [hbij, card_range]
  rw [hfilter, card_union_of_disjoint hdisj, hcard]
  by_cases hc : x (a * 2 ^ m + rs) ≤ c
  · simp [hc]
  · simp [hc]

/-- **One point per cell gives the block bound.** If every aligned block of `x` has one point
in each dyadic cell (all points in `[0,1)`), then the local discrepancy partial sums
`F N = #{k < N : x k ≤ c} − N c` satisfy `AlignedBlockBound F 1`. -/
theorem alignedBlockBound_of_cells {x : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hx0 : ∀ k, 0 ≤ x k)
    (hinj : ∀ m a, ∀ r < 2 ^ m, ∀ r' < 2 ^ m,
      ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ = ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r')⌋₊ → r = r')
    (hlt : ∀ m a, ∀ r < 2 ^ m, ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ < 2 ^ m) :
    AlignedBlockBound
      (fun N ↦ (((range N).filter fun k ↦ x k ≤ c).card : ℝ) - N * c) 1 := by
  classical
  intro m a
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  -- the point in the cell of `c`
  have hj0lt : ⌊(2 : ℝ) ^ m * c⌋₊ < 2 ^ m := by
    have : (2 : ℝ) ^ m * c < 2 ^ m := by nlinarith
    exact Nat.floor_lt (by positivity) |>.2 (by exact_mod_cast this)
  have hsurj : (range (2 ^ m)).image (fun r ↦ ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊) =
      range (2 ^ m) := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨r, hr, rfl⟩ := mem_image.1 hy
      exact mem_range.2 (hlt m a r (mem_range.1 hr))
    · rw [card_image_of_injOn]
      intro r hr r' hr' h
      exact hinj m a r (mem_range.1 hr) r' (mem_range.1 hr') h
  obtain ⟨rs, hrs, hcell⟩ := mem_image.1 (hsurj ▸ mem_range.2 hj0lt :
    ⌊(2 : ℝ) ^ m * c⌋₊ ∈ (range (2 ^ m)).image _)
  have hrs' := mem_range.1 hrs
  have hblock := card_le_add_frac_eq hc0 hc1 (fun r _ ↦ hx0 _) (hinj m a) (hlt m a) hrs' hcell
  -- split the count over `[0, (a+1) 2^m)` into `[0, a 2^m)` and the block
  have hsplit : ((range ((a + 1) * 2 ^ m)).filter fun k ↦ x k ≤ c).card =
      ((range (a * 2 ^ m)).filter fun k ↦ x k ≤ c).card +
        ((range (2 ^ m)).filter fun r ↦ x (a * 2 ^ m + r) ≤ c).card := by
    have e : (a + 1) * 2 ^ m = a * 2 ^ m + 2 ^ m := by ring
    rw [e, card_filter, card_filter, card_filter, sum_range_add]
  simp only
  rw [hsplit, hblock]
  push_cast
  have hfl0 : (⌊(2 : ℝ) ^ m * c⌋₊ : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
  have hfl1 : (2 : ℝ) ^ m * c < ⌊(2 : ℝ) ^ m * c⌋₊ + 1 := Nat.lt_floor_add_one _
  have hI0 : (0 : ℝ) ≤ if x (a * 2 ^ m + rs) ≤ c then 1 else 0 := by split_ifs <;> norm_num
  have hI1 : (if x (a * 2 ^ m + rs) ≤ c then 1 else 0 : ℝ) ≤ 1 := by split_ifs <;> norm_num
  rw [abs_le]
  constructor <;> nlinarith

end RQMCMarkov.ScrambledStacks
