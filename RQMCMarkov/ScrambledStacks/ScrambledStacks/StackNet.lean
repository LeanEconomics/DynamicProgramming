/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackDefs

/-! # Scrambled van der Corput stacks are `(0,1)`-sequences: the QMC rate for every scramble

Post #3: "Balancing the departures from each state ((ii)–(iv)) gets the transition counts almost
exactly right". For codes (ii) and (iii) (per-state Sobol = van der Corput stacks, digitally
shifted or Owen-scrambled) this holds **for every realisation** of the randomisation: the
scrambled sequence keeps the net property of the van der Corput sequence (Owen 1997;
Niederreiter 1992, Ch. 4), and the departure counts inherit the QMC rate `O(log T)`.

**Aligned blocks** (`image_digitPrefix_scrambledDigit_block`): for every flip table `f`, the
`2^m` points with indices `a 2^m, …, (a+1) 2^m − 1` have first `m` scrambled digits running over
all of `{0,1}^m` (one point per dyadic cell of length `2^{-m}`): the first `m` scrambled digits
depend only on `k mod 2^m` (`digitPrefix_scrambledDigit_mod`) and determine it
(`mod_eq_of_digitPrefix_scrambledDigit_eq`). Hence (`abs_segErr_scrambledVdc_block_le`) the
counting error `segErr u x N L = #{N ≤ k < N + L : u k ≤ x} − L x` of an aligned block is at most
`1` for every threshold `x ∈ [0,1]`.

**Segments** (generic, for any sequence with per-level block bounds `β m`):
* `abs_segErr_prefix_le`: a prefix of length `L < 2^m` of an aligned `2^m`-block has error
  `≤ Σ_{j<m} β j`;
* `abs_segErr_le_of_block` (**segment lemma**): every segment `[N, N + L)` with `L ≤ 2^m` has
  error `≤ 2 Σ_{j<m} β j + β m` (it is a suffix of one aligned `2^m`-block plus a prefix of the
  next, or a difference of two prefixes).
For scrambled van der Corput points (`β = 1`): `abs_segErr_scrambledVdc_le`:
`|segErr| ≤ 2m + 1` for `L ≤ 2^m`, `abs_segErr_scrambledVdc_log_le`: `≤ 2⌊log₂ L⌋ + 3`, and
`abs_segErr_scrambledVdc_zero_le`: an initial segment `[0, N)` has error `≤ ⌊log₂ N⌋ + 1`.

**Step functions** (`abs_sum_step_sub_le_of_count`, discrete Koksma by summation by parts): if
every threshold count over a finite index set `s` has error `≤ D`, then
`|Σ_{k∈s} (g(step P i (u k)) − (Pg)(i))| ≤ V(g) D`. Hence for every flip table:
* `abs_sum_step_scrambledVdc_segment_le` (exported for the CLT): over any segment of length
  `L ≤ 2^m`, `|Σ_{k<L} φ(u (N + k))| ≤ V(g) (2m + 1)` with `φ(u) = g(step P i u) − (Pg)(i)`;
* `abs_transCount_scrambled_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2 (⌊log₂ T⌋ + 1)`;
* `abs_departureDiscrepancy_scrambled_le`: `|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)`;
* `abs_occCount_scrambled_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`;
* `occFreq_scrambled_isBigO`: occupation frequencies converge at `O(log T / T)`;
* `abs_transCount_owen_sub_le`, `abs_transCount_shift_sub_le`, `abs_occCount_owen_sub_le`,
  `abs_occCount_shift_sub_le`: the same bounds for every realisation `ω` of Owen scrambling and
  of the digital shift. These are the constants of `StackBound` for unscrambled van der Corput
  stacks: no realisation of either randomisation is worse than plain QMC.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset Matrix Filter Asymptotics

variable {n : ℕ}

/-! ### Counting errors of segments -/

/-- The **counting error** of the segment `[N, N + L)` of `u` at the threshold `x`:
`#{N ≤ k < N + L : u k ≤ x} − L x`, as a sum. -/
noncomputable def segErr (u : ℕ → ℝ) (x : ℝ) (N L : ℕ) : ℝ :=
  ∑ k ∈ range L, ((if u (N + k) ≤ x then (1 : ℝ) else 0) - x)

/-- The empty segment has error `0`. -/
theorem segErr_zero (u : ℕ → ℝ) (x : ℝ) (N : ℕ) : segErr u x N 0 = 0 := by
  simp [segErr]

/-- **Additivity**: `[N, N + L₁ + L₂) = [N, N + L₁) ∪ [N + L₁, N + L₁ + L₂)`. -/
theorem segErr_add (u : ℕ → ℝ) (x : ℝ) (N L₁ L₂ : ℕ) :
    segErr u x N (L₁ + L₂) = segErr u x N L₁ + segErr u x (N + L₁) L₂ := by
  unfold segErr
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [add_assoc]

/-- The counting error as a count: `segErr = #{k < L : u (N + k) ≤ x} − L x`. -/
theorem segErr_eq_card (u : ℕ → ℝ) (x : ℝ) (N L : ℕ) :
    segErr u x N L = (((range L).filter fun k => u (N + k) ≤ x).card : ℝ) - L * x := by
  unfold segErr
  rw [sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul]

/-- **Prefixes of aligned blocks.** If every aligned `2^m`-block has error `≤ β m`, a prefix of
length `L < 2^m` of an aligned `2^m`-block has error `≤ Σ_{j<m} β j` (split off the first half
when `L ≥ 2^{m-1}`). -/
theorem abs_segErr_prefix_le {u : ℕ → ℝ} {x : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ m a, |segErr u x (a * 2 ^ m) (2 ^ m)| ≤ β m) (m : ℕ) :
    ∀ a L, L < 2 ^ m → |segErr u x (a * 2 ^ m) L| ≤ ∑ j ∈ range m, β j := by
  induction m with
  | zero =>
    intro a L hL
    have hL0 : L = 0 := by simpa using hL
    rw [hL0, segErr_zero, abs_zero, range_zero, sum_empty]
  | succ m ih =>
    intro a L hL
    have hβm : 0 ≤ β m := (abs_nonneg _).trans (hβ m 0)
    have e : a * 2 ^ (m + 1) = (2 * a) * 2 ^ m := by ring
    rw [e, sum_range_succ]
    by_cases hLm : L < 2 ^ m
    · linarith [ih (2 * a) L hLm]
    · obtain ⟨L', rfl⟩ : ∃ L', L = 2 ^ m + L' := ⟨L - 2 ^ m, by omega⟩
      have hL' : L' < 2 ^ m := by rw [pow_succ] at hL; omega
      rw [segErr_add]
      have e2 : 2 * a * 2 ^ m + 2 ^ m = (2 * a + 1) * 2 ^ m := by ring
      rw [e2]
      have h1 := hβ m (2 * a)
      have h2 := ih (2 * a + 1) L' hL'
      calc |segErr u x (2 * a * 2 ^ m) (2 ^ m) + segErr u x ((2 * a + 1) * 2 ^ m) L'|
          ≤ |segErr u x (2 * a * 2 ^ m) (2 ^ m)| + |segErr u x ((2 * a + 1) * 2 ^ m) L'| :=
            abs_add_le _ _
        _ ≤ ∑ j ∈ range m, β j + β m := by linarith

/-- **The segment lemma.** If every aligned `2^m`-block has error `≤ β m`, every segment
`[N, N + L)` with `L ≤ 2^m` has error `≤ 2 Σ_{j<m} β j + β m`. -/
theorem abs_segErr_le_of_block {u : ℕ → ℝ} {x : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ m a, |segErr u x (a * 2 ^ m) (2 ^ m)| ≤ β m) (N L m : ℕ) (hL : L ≤ 2 ^ m) :
    |segErr u x N L| ≤ 2 * ∑ j ∈ range m, β j + β m := by
  set S := ∑ j ∈ range m, β j with hSdef
  have hS : 0 ≤ S := sum_nonneg fun j _ => (abs_nonneg _).trans (hβ j 0)
  have hβm : 0 ≤ β m := (abs_nonneg _).trans (hβ m 0)
  have hpos : 0 < 2 ^ m := by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ m := ⟨_, rfl⟩
  obtain ⟨a, r, hN, hr⟩ : ∃ a r, N = a * 2 ^ m + r ∧ r < 2 ^ m :=
    ⟨N / 2 ^ m, N % 2 ^ m, by rw [mul_comm]; exact (Nat.div_add_mod N (2 ^ m)).symm,
      Nat.mod_lt _ hpos⟩
  obtain ⟨A, hA⟩ : ∃ A, A = a * 2 ^ m := ⟨_, rfl⟩
  have hpre : ∀ b ℓ, ℓ ≤ 2 ^ m → |segErr u x (b * 2 ^ m) ℓ| ≤ S + β m := by
    intro b ℓ hℓ
    rcases lt_or_eq_of_le hℓ with h | h
    · linarith [abs_segErr_prefix_le hβ m b ℓ h]
    · rw [h]
      linarith [hβ m b]
  by_cases hrL : r + L ≤ 2 ^ m
  · have e : segErr u x N L = segErr u x (a * 2 ^ m) (r + L) - segErr u x (a * 2 ^ m) r := by
      rw [segErr_add, hN]
      ring
    rw [e]
    have h1 := hpre a (r + L) hrL
    have h2 := abs_segErr_prefix_le hβ m a r hr
    calc |segErr u x (a * 2 ^ m) (r + L) - segErr u x (a * 2 ^ m) r|
        ≤ |segErr u x (a * 2 ^ m) (r + L)| + |segErr u x (a * 2 ^ m) r| := abs_sub _ _
      _ ≤ (S + β m) + S := add_le_add h1 h2
      _ = 2 * S + β m := by ring
  · obtain ⟨L', hL'⟩ : ∃ L', L = (2 ^ m - r) + L' := ⟨L - (2 ^ m - r), by omega⟩
    have hL'lt : L' < 2 ^ m := by omega
    have e1 : segErr u x (a * 2 ^ m) (2 ^ m) =
        segErr u x (a * 2 ^ m) r + segErr u x N (2 ^ m - r) := by
      rw [hN, ← segErr_add]
      congr 1
      omega
    have e2 : N + (2 ^ m - r) = (a + 1) * 2 ^ m := by
      rw [add_mul, one_mul, ← hA, hN, ← hA]
      omega
    have e : segErr u x N L = (segErr u x (a * 2 ^ m) (2 ^ m) - segErr u x (a * 2 ^ m) r) +
        segErr u x ((a + 1) * 2 ^ m) L' := by
      rw [hL', segErr_add, e2, e1]
      ring
    rw [e]
    have h1 := hβ m a
    have h2 := abs_segErr_prefix_le hβ m a r hr
    have h3 := abs_segErr_prefix_le hβ m (a + 1) L' hL'lt
    calc |(segErr u x (a * 2 ^ m) (2 ^ m) - segErr u x (a * 2 ^ m) r) +
          segErr u x ((a + 1) * 2 ^ m) L'|
        ≤ |segErr u x (a * 2 ^ m) (2 ^ m) - segErr u x (a * 2 ^ m) r| +
          |segErr u x ((a + 1) * 2 ^ m) L'| := abs_add_le _ _
      _ ≤ (|segErr u x (a * 2 ^ m) (2 ^ m)| + |segErr u x (a * 2 ^ m) r|) +
          |segErr u x ((a + 1) * 2 ^ m) L'| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ (β m + S) + S := add_le_add (add_le_add h1 h2) h3
      _ = 2 * S + β m := by ring

/-! ### Aligned blocks of the scrambled van der Corput sequence -/

/-- Equal low bits give equal residues: if bits `0, …, j-1` of `K` and `K'` agree then
`K % 2^j = K' % 2^j`. -/
theorem mod_two_pow_eq_of_testBit_eq {K K' j : ℕ} (h : ∀ i < j, K.testBit i = K'.testBit i) :
    K % 2 ^ j = K' % 2 ^ j := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < j
  · simp only [hi, decide_true, Bool.true_and]
    exact h i hi
  · simp only [hi, decide_false, Bool.false_and]

/-- If the first `m` scrambled digits of `K` and `K'` agree (same flip table), so do their first
`m` bits: the scramble is a bijection on each level of the binary tree. -/
theorem testBit_eq_of_scrambledDigit_eq {f : ℕ → ℕ → Bool} {K K' m : ℕ}
    (h : ∀ j < m, scrambledDigit f K j = scrambledDigit f K' j) :
    ∀ j < m, K.testBit j = K'.testBit j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hmod : K % 2 ^ j = K' % 2 ^ j :=
      mod_two_pow_eq_of_testBit_eq fun i hi => ih i hi (by omega)
    have hd := h j hj
    unfold scrambledDigit at hd
    rw [hmod] at hd
    cases hK : K.testBit j <;> cases hK' : K'.testBit j <;> cases f j (K' % 2 ^ j) <;>
      simp_all

/-- **The first `m` scrambled digits determine `k mod 2^m`.** -/
theorem mod_eq_of_digitPrefix_scrambledDigit_eq {f : ℕ → ℕ → Bool} {K K' m : ℕ}
    (h : digitPrefix (scrambledDigit f K) m = digitPrefix (scrambledDigit f K') m) :
    K % 2 ^ m = K' % 2 ^ m :=
  mod_two_pow_eq_of_testBit_eq (testBit_eq_of_scrambledDigit_eq (eq_of_digitPrefix_eq h))

/-- **The first `m` scrambled digits depend only on `k mod 2^m`.** -/
theorem digitPrefix_scrambledDigit_mod (f : ℕ → ℕ → Bool) (K m : ℕ) :
    digitPrefix (scrambledDigit f (K % 2 ^ m)) m = digitPrefix (scrambledDigit f K) m := by
  refine digitPrefix_congr fun j hj => ?_
  unfold scrambledDigit
  rw [Nat.testBit_mod_two_pow, Nat.mod_mod_of_dvd K (pow_dvd_pow 2 hj.le)]
  simp only [hj, decide_true, Bool.true_and]

/-- Within the aligned block `[a 2^m, (a+1) 2^m)`, the first `m` scrambled digits of point
`a 2^m + k` are those of point `k`. -/
theorem digitPrefix_scrambledDigit_block (f : ℕ → ℕ → Bool) (a m : ℕ) {k : ℕ} (hk : k < 2 ^ m) :
    digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m = digitPrefix (scrambledDigit f k) m := by
  rw [← digitPrefix_scrambledDigit_mod f (a * 2 ^ m + k), Nat.mul_add_mod',
    Nat.mod_eq_of_lt hk]

/-- `k ↦` (first `m` scrambled digits of point `k`) is injective on `[0, 2^m)`. -/
theorem injOn_digitPrefix_scrambledDigit (f : ℕ → ℕ → Bool) (m : ℕ) :
    Set.InjOn (fun k => digitPrefix (scrambledDigit f k) m) (range (2 ^ m) : Set ℕ) := by
  intro k hk k' hk' h
  have := mod_eq_of_digitPrefix_scrambledDigit_eq h
  rwa [Nat.mod_eq_of_lt (mem_range.1 hk), Nat.mod_eq_of_lt (mem_range.1 hk')] at this

/-- **The aligned-block property** (Owen 1997: scrambling preserves `(0,m,1)`-nets): for every
flip table, the first `m` scrambled digits of the `2^m` points `a 2^m + k`, `k < 2^m`, run over
all of `{0, …, 2^m − 1}`, i.e. there is one point in each dyadic cell of length `2^{-m}`. -/
theorem image_digitPrefix_scrambledDigit_block (f : ℕ → ℕ → Bool) (a m : ℕ) :
    (range (2 ^ m)).image (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m) =
      range (2 ^ m) := by
  have e : (range (2 ^ m)).image (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m) =
      (range (2 ^ m)).image (fun k => digitPrefix (scrambledDigit f k) m) :=
    image_congr fun k hk => digitPrefix_scrambledDigit_block f a m (mem_range.1 hk)
  rw [e]
  refine eq_of_subset_of_card_le (fun d hd => ?_) ?_
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hd
    exact mem_range.2 (digitPrefix_lt _ m)
  · rw [card_image_of_injOn (injOn_digitPrefix_scrambledDigit f m)]

/-- **Counting through the aligned block**: the number of points of an aligned `2^m`-block whose
first `m` scrambled digits satisfy `p` is the number of `d < 2^m` with `p d`. -/
theorem card_filter_digitPrefix_block (f : ℕ → ℕ → Bool) (a m : ℕ) (p : ℕ → Prop)
    [DecidablePred p] :
    ((range (2 ^ m)).filter fun k => p (digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m)).card =
      ((range (2 ^ m)).filter p).card := by
  have hinj : Set.InjOn (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m)
      (range (2 ^ m) : Set ℕ) := by
    intro k hk k' hk' h
    simp only at h
    rw [digitPrefix_scrambledDigit_block f a m (mem_range.1 hk),
      digitPrefix_scrambledDigit_block f a m (mem_range.1 hk')] at h
    exact injOn_digitPrefix_scrambledDigit f m hk hk' h
  rw [← card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _))), ← filter_image,
    image_digitPrefix_scrambledDigit_block]

/-- The number of `d < 2^m` with `d < c` is `min c 2^m`. -/
theorem card_filter_lt_range (c m : ℕ) :
    ((range (2 ^ m)).filter fun d => d < c).card = min c (2 ^ m) := by
  have : (range (2 ^ m)).filter (fun d => d < c) = range (min c (2 ^ m)) := by
    ext d
    simp only [mem_filter, mem_range, lt_min_iff]
    tauto
  rw [this, card_range]

/-- **Aligned blocks of a scrambled van der Corput sequence have counting error `≤ 1`**, at
every threshold `x ∈ [0,1]` and for every flip table. -/
theorem abs_segErr_scrambledVdc_block_le (f : ℕ → ℕ → Bool) (m a : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : |segErr (scrambledVdc f) x (a * 2 ^ m) (2 ^ m)| ≤ 1 := by
  rw [segErr_eq_card]
  set D : ℕ → ℕ := fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m with hD
  set c := ⌊(2 : ℝ) ^ m * x⌋₊ with hc
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hc1 : (c : ℝ) ≤ 2 ^ m * x := Nat.floor_le (by positivity)
  have hc2 : 2 ^ m * x < (c : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcm : (c : ℝ) ≤ 2 ^ m := hc1.trans (by nlinarith)
  have hcount : ∀ c', ((range (2 ^ m)).filter fun k => D k < c').card = min c' (2 ^ m) :=
    fun c' => (card_filter_digitPrefix_block f a m (· < c')).trans (card_filter_lt_range c' m)
  have hsub1 : (range (2 ^ m)).filter (fun k => D k < c) ⊆
      (range (2 ^ m)).filter (fun k => scrambledVdc f (a * 2 ^ m + k) ≤ x) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have h := binaryVal_le_digitPrefix_add_one_div (scrambledDigit f (a * 2 ^ m + k)) m
    have hk2 : ((D k : ℕ) : ℝ) + 1 ≤ c := by exact_mod_cast hk.2
    refine h.trans ?_
    rw [div_le_iff₀ hp]
    change ((D k : ℕ) : ℝ) + 1 ≤ x * 2 ^ m
    linarith
  have hsub2 : (range (2 ^ m)).filter (fun k => scrambledVdc f (a * 2 ^ m + k) ≤ x) ⊆
      (range (2 ^ m)).filter (fun k => D k < c + 1) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    by_contra hcon
    have hk2 : (c : ℝ) + 1 ≤ ((D k : ℕ) : ℝ) := by exact_mod_cast not_lt.1 hcon
    have h := digitPrefix_div_le_binaryVal (scrambledDigit f (a * 2 ^ m + k)) m
    rw [div_le_iff₀ hp] at h
    have h3 : scrambledVdc f (a * 2 ^ m + k) * 2 ^ m ≤ x * 2 ^ m :=
      mul_le_mul_of_nonneg_right hk.2 hp.le
    change ((D k : ℕ) : ℝ) ≤ scrambledVdc f (a * 2 ^ m + k) * 2 ^ m at h
    linarith
  have hlo := card_le_card hsub1
  have hhi := card_le_card hsub2
  rw [hcount] at hlo hhi
  have hcm' : c ≤ 2 ^ m := by exact_mod_cast hcm
  rw [min_eq_left hcm'] at hlo
  have hlo' : (c : ℝ) ≤ ((range (2 ^ m)).filter fun k =>
      scrambledVdc f (a * 2 ^ m + k) ≤ x).card := by exact_mod_cast hlo
  have hhi' : (((range (2 ^ m)).filter fun k =>
      scrambledVdc f (a * 2 ^ m + k) ≤ x).card : ℝ) ≤ c + 1 := by
    exact_mod_cast hhi.trans (min_le_left _ _)
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-- **Segments of a scrambled van der Corput sequence**: for every flip table and threshold
`x ∈ [0,1]`, a segment of length `L ≤ 2^m` has counting error `≤ 2m + 1`. -/
theorem abs_segErr_scrambledVdc_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N L m : ℕ) (hL : L ≤ 2 ^ m) : |segErr (scrambledVdc f) x N L| ≤ 2 * m + 1 := by
  have h := abs_segErr_le_of_block (β := fun _ => 1)
    (fun m a => abs_segErr_scrambledVdc_block_le f m a hx0 hx1) N L m hL
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_one] using h

/-- **Segment lemma, logarithmic form**: `|segErr| ≤ 2 ⌊log₂ L⌋ + 3`. -/
theorem abs_segErr_scrambledVdc_log_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N L : ℕ) : |segErr (scrambledVdc f) x N L| ≤ 2 * (Nat.log 2 L : ℝ) + 3 := by
  have h := abs_segErr_scrambledVdc_le f hx0 hx1 N L (Nat.log 2 L + 1)
    (Nat.lt_pow_succ_log_self (by norm_num) L).le
  push_cast at h
  linarith

/-- **Initial segments**: `|#{k < N : u k ≤ x} − N x| ≤ ⌊log₂ N⌋ + 1`, for every flip table
(the van der Corput bound `N D*_N ≤ ⌊log₂ N⌋ + 1` survives every scramble). -/
theorem abs_segErr_scrambledVdc_zero_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N : ℕ) : |segErr (scrambledVdc f) x 0 N| ≤ (Nat.log 2 N : ℝ) + 1 := by
  have h := abs_segErr_prefix_le (β := fun _ => 1)
    (fun m a => abs_segErr_scrambledVdc_block_le f m a hx0 hx1) (Nat.log 2 N + 1) 0 N
    (Nat.lt_pow_succ_log_self (by norm_num) N)
  simp only [zero_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  push_cast at h
  exact h

/-! ### Step functions: summation by parts on any finite index set -/

/-- The count of departures to `j` is a difference of two thresholds (any index set `s`). -/
theorem card_filter_step_eq_eq_sub (P : Fin n → Fin n → ℝ) (i : Fin n) (u : ℕ → ℝ)
    (s : Finset ℕ) (j : Fin n) :
    ((s.filter fun k => step P i (u k) = j).card : ℝ) =
      ((s.filter fun k => (step P i (u k) : ℕ) < j + 1).card : ℝ) -
        ((s.filter fun k => (step P i (u k) : ℕ) < j).card : ℝ) := by
  rw [eq_sub_iff_add_eq, ← sum_boole, ← sum_boole, ← sum_boole, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases h1 : step P i (u k) = j
  · rw [h1]
    simp only [lt_irrefl, Nat.lt_add_one, ite_true, ite_false, add_zero]
  · have h1' : (step P i (u k) : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    by_cases h2 : (step P i (u k) : ℕ) < j
    · have h3 : (step P i (u k) : ℕ) < j + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, zero_add]
    · have h3 : ¬ ((step P i (u k) : ℕ) < j + 1) := by omega
      simp only [h1, h2, h3, ite_false, add_zero]

/-- **Discrete Koksma inequality on any index set**: if `u k ≤ 1` on `s` and every threshold
count `#{k ∈ s : u k ≤ cs_{i,m}}`, `m ≥ 1`, has error `≤ D`, then
`|Σ_{k∈s} (g(step P i (u k)) − (Pg)(i))| ≤ V(g) D`. -/
theorem abs_sum_step_sub_le_of_count {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {u : ℕ → ℝ} {s : Finset ℕ} (hu : ∀ k ∈ s, u k ≤ 1) {D : ℝ}
    (hD : ∀ m : ℕ, 1 ≤ m →
      |((s.filter fun k => u k ≤ cumProb P i m).card : ℝ) - s.card * cumProb P i m| ≤ D)
    (g : Fin n → ℝ) :
    |∑ k ∈ s, (g (step P i (u k)) - (P *ᵥ g) i)| ≤ stateVariation g * D := by
  set B : ℕ → ℝ := fun m =>
    ((s.filter fun k => (step P i (u k) : ℕ) < m).card : ℝ) - s.card * cumProb P i m with hBdef
  have hB0 : B 0 = 0 := by
    have h0 : (s.filter fun k => (step P i (u k) : ℕ) < 0) = ∅ :=
      filter_eq_empty_iff.2 fun k _ hk => Nat.not_lt_zero _ hk
    simp only [hBdef, h0, card_empty, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hBn : B n = 0 := by
    have hn : (s.filter fun k => (step P i (u k) : ℕ) < n) = s :=
      filter_true_of_mem fun k _ => (step P i (u k)).isLt
    simp only [hBdef, hn, cumProb_of_le P i le_rfl, hP.sum_eq_one i, mul_one, sub_self]
  have hBb : ∀ m, 1 ≤ m → |B m| ≤ D := by
    intro m hm
    have e : (s.filter fun k => (step P i (u k) : ℕ) < m) =
        s.filter fun k => u k ≤ cumProb P i m :=
      filter_congr fun k hk => step_lt_iff hP i (hu k hk) hm
    simp only [hBdef, e]
    exact hD m hm
  have e1 : ∑ k ∈ s, (g (step P i (u k)) - (P *ᵥ g) i) =
      ∑ j : Fin n, g j * (B (j + 1) - B j) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← sum_fiberwise s (fun k => step P i (u k))]
    have e2 : ∀ j : Fin n, ∑ k ∈ s.filter (fun k => step P i (u k) = j),
        g (step P i (u k)) = g j * ((s.filter fun k => step P i (u k) = j).card : ℝ) :=
      fun j => by
        rw [sum_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], sum_const, nsmul_eq_mul,
          mul_comm]
    rw [sum_congr rfl fun j _ => e2 j]
    have e3 : (s.card : ℝ) * (P *ᵥ g) i = ∑ j : Fin n, g j * (P i j * s.card) := by
      simp only [mulVec, dotProduct, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [e3, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sub, card_filter_step_eq_eq_sub]
    congr 1
    simp only [hBdef]
    rw [cumProb_succ]
    ring
  rw [e1]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 1 le_rfl)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [Finset.univ_eq_empty, sum_empty, abs_zero]
    exact mul_nonneg (stateVariation_nonneg g) hD0
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
  exact mul_le_mul_of_nonneg_left (hBb (j + 1) (by omega)) (abs_nonneg _)

/-- Threshold counts of a segment are its counting errors. -/
theorem card_filter_segment_sub_eq_segErr (u : ℕ → ℝ) (x : ℝ) (N L : ℕ) :
    (((range L).filter fun k => u (N + k) ≤ x).card : ℝ) - (range L).card * x =
      segErr u x N L := by
  rw [segErr_eq_card, card_range]

/-- **The segment lemma for step functions** (exported): for every flip table and every
segment of length `L ≤ 2^m`, `|Σ_{k<L} (g(step P i (u (N+k))) − (Pg)(i))| ≤ V(g) (2m + 1)`,
`u = scrambledVdc f`. -/
theorem abs_sum_step_scrambledVdc_segment_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (i : Fin n) (f : ℕ → ℕ → Bool) (g : Fin n → ℝ) (N L m : ℕ) (hL : L ≤ 2 ^ m) :
    |∑ k ∈ range L, (g (step P i (scrambledVdc f (N + k))) - (P *ᵥ g) i)| ≤
      stateVariation g * (2 * m + 1) :=
  abs_sum_step_sub_le_of_count (u := fun k => scrambledVdc f (N + k)) hP i
    (fun k _ => (scrambledVdc_mem_Icc f _).2) (fun m' _ => by
      rw [card_filter_segment_sub_eq_segErr]
      exact abs_segErr_scrambledVdc_le f (cumProb_mem_Icc hP i m').1 (cumProb_mem_Icc hP i m').2
        N L m hL) g

/-- **The segment lemma for step functions, logarithmic form**: `≤ V(g) (2 ⌊log₂ L⌋ + 3)`. -/
theorem abs_sum_step_scrambledVdc_segment_log_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (i : Fin n) (f : ℕ → ℕ → Bool) (g : Fin n → ℝ) (N L : ℕ) :
    |∑ k ∈ range L, (g (step P i (scrambledVdc f (N + k))) - (P *ᵥ g) i)| ≤
      stateVariation g * (2 * (Nat.log 2 L : ℝ) + 3) := by
  have h := abs_sum_step_scrambledVdc_segment_le hP i f g N L (Nat.log 2 L + 1)
    (Nat.lt_pow_succ_log_self (by norm_num) L).le
  push_cast at h
  linarith

/-- **Initial segments of step-function sums**: `|Σ_{k<N} φ(u k)| ≤ V(g) (⌊log₂ N⌋ + 1)`. -/
theorem abs_sum_step_scrambledVdc_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    (f : ℕ → ℕ → Bool) (g : Fin n → ℝ) (N : ℕ) :
    |∑ k ∈ range N, (g (step P i (scrambledVdc f k)) - (P *ᵥ g) i)| ≤
      stateVariation g * ((Nat.log 2 N : ℝ) + 1) :=
  abs_sum_step_sub_le_of_count hP i (fun k _ => (scrambledVdc_mem_Icc f k).2) (fun m' _ => by
    have h := card_filter_segment_sub_eq_segErr (scrambledVdc f) (cumProb P i m') 0 N
    simp only [zero_add] at h
    rw [h]
    exact abs_segErr_scrambledVdc_zero_le f (cumProb_mem_Icc hP i m').1
      (cumProb_mem_Icc hP i m').2 N) g

/-! ### Chains driven by scrambled stacks -/

variable {P : Fin n → Fin n → ℝ}

/-- `|#{k < N : step P i (u k) < m} − N cs_{i,m}| ≤ ⌊log₂ N⌋ + 1` for a scrambled stack. -/
theorem abs_departuresBelow_scrambledVdc_sub_le (hP : IsStochastic P) (i : Fin n)
    (f : ℕ → ℕ → Bool) (N m : ℕ) :
    |(departuresBelow P i (scrambledVdc f) N m : ℝ) - N * cumProb P i m| ≤
      (Nat.log 2 N : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i (scrambledVdc f) N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  have e : departuresBelow P i (scrambledVdc f) N m =
      ((range N).filter fun k => scrambledVdc f (0 + k) ≤ cumProb P i m).card := by
    unfold departuresBelow
    congr 1
    refine filter_congr fun k _ => ?_
    rw [zero_add]
    exact step_lt_iff hP i (scrambledVdc_mem_Icc f k).2 hm
  rw [e]
  have h := card_filter_segment_sub_eq_segErr (scrambledVdc f) (cumProb P i m) 0 N
  rw [card_range] at h
  rw [h]
  exact abs_segErr_scrambledVdc_zero_le f (cumProb_mem_Icc hP i m).1 (cumProb_mem_Icc hP i m).2 N

/-- **Scrambled stacks balance the transitions, for every flip table** (post #3, codes (ii) and
(iii)): `|N_ij(T) − p_ij N_i(T)| ≤ 2 (⌊log₂ T⌋ + 1)`. -/
theorem abs_transCount_scrambled_sub_le (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack f)) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) i T
  rw [transCount_stackDrive]
  have hv : scrambledStack f i = scrambledVdc (f i) := rfl
  rw [hv, card_step_eq_eq_sub]
  have e : (departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) -
        departuresBelow P i (scrambledVdc (f i)) N j - P i j * N =
      ((departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_scrambledVdc_sub_le hP i (f i) N (j + 1)
  have h2 := abs_departuresBelow_scrambledVdc_sub_le hP i (f i) N j
  have hlog : (Nat.log 2 N : ℝ) ≤ Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (occCount_le (stackPath P x₀ (scrambledStack f)) i T)
  calc _ ≤ |(departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Departure discrepancy of a scrambled-stack path, for every flip table**:
`|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)`. -/
theorem abs_departureDiscrepancy_scrambled_le (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (g : Fin n → ℝ) (i : Fin n) (T : ℕ) :
    |departureDiscrepancy P g (stackPath P x₀ (scrambledStack f)) i T| ≤
      stateVariation g * ((Nat.log 2 T : ℝ) + 1) := by
  refine (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ (scrambledStack f) i
    T)).trans_le ((abs_sum_step_scrambledVdc_le hP i (f i) g _).trans ?_)
  have hlog : (Nat.log 2 (occCount (stackPath P x₀ (scrambledStack f)) i T) : ℝ) ≤
      Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (occCount_le (stackPath P x₀ (scrambledStack f)) i T)
  exact mul_le_mul_of_nonneg_left (by linarith) (stateVariation_nonneg g)

/-- **Occupation error of a scrambled-stack path, for every flip table** (post #3, "QMC's
`O(log T / T)`" for codes (ii) and (iii)): `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`,
where `h − Ph = 1_{s} − π_s` and `|h| ≤ M`. -/
theorem abs_occCount_scrambled_sub_le (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
  refine (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl ?_)
  calc ∑ i, |departureDiscrepancy P h (stackPath P x₀ (scrambledStack f)) i T|
      ≤ ∑ _i : Fin n, stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
        sum_le_sum fun i _ => abs_departureDiscrepancy_scrambled_le hP x₀ f h i T
    _ = n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The occupation frequencies of a scrambled-stack path converge at `O(log T / T)`, for
every flip table.** -/
theorem occFreq_scrambled_isBigO (hP : IsStochastic P) (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool)
    {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) / T - c) =O[atTop]
      fun T : ℕ => Real.log T / T := by
  refine isBigO_log_div_of_le (A := 2 * M) (B := n * stateVariation h)
    (by linarith [(abs_nonneg _).trans (hM s)])
    (mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h)) fun T hT => ?_
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm c]
  exact abs_occCount_scrambled_sub_le hP x₀ f hh hM T

/-- Owen scrambling: the transition bound holds for **every** realisation `ω`. -/
theorem abs_transCount_owen_sub_le (hP : IsStochastic P) (x₀ : Fin n)
    (ω : Fin n × ℕ × ℕ → Bool) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack (owenTable ω))) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack (owenTable ω))) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  abs_transCount_scrambled_sub_le hP x₀ (owenTable ω) i j T

/-- Digital shift: the transition bound holds for **every** realisation `ω`. -/
theorem abs_transCount_shift_sub_le (hP : IsStochastic P) (x₀ : Fin n) (ω : Fin n × ℕ → Bool)
    (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  abs_transCount_scrambled_sub_le hP x₀ (shiftFlips ω) i j T

/-- Owen scrambling: the occupation bound holds for **every** realisation `ω`. -/
theorem abs_occCount_owen_sub_le (hP : IsStochastic P) (x₀ : Fin n) (ω : Fin n × ℕ × ℕ → Bool)
    {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
  abs_occCount_scrambled_sub_le hP x₀ (owenTable ω) hh hM T

/-- Digital shift: the occupation bound holds for **every** realisation `ω`. -/
theorem abs_occCount_shift_sub_le (hP : IsStochastic P) (x₀ : Fin n) (ω : Fin n × ℕ → Bool)
    {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
  abs_occCount_scrambled_sub_le hP x₀ (shiftFlips ω) hh hM T

end RQMCMarkov.ScrambledStacks
