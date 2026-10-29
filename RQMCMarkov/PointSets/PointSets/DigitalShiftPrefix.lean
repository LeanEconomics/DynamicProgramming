/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PointSets.DigitalShift

/-! # Digital shift versus random shift for every van der Corput prefix

`DigitalShift` shows that for `n = 2^m` the digitally shifted and the randomly shifted first `n`
van der Corput points are the same point set, and that this fails for general dyadic point sets.
This module proves that the two randomizations agree in law for EVERY prefix length `n`: for
`n ≤ 2^m` the digitally shifted first `n` points (`m`-digit shift) and the randomly shifted first
`n` points `{fract (φ(i) + U)}` have the same law as random point sets.

**Construction.** Write `Sₙ = {⌊2^m φ(i)⌋ : i < n} ⊆ {0, …, 2^m - 1}` for the cell indices of the
first `n` points. `exists_prefix_cellPerm` builds, by induction on `m`, a bijection `τ` of
`{0, …, 2^m - 1}` with `Sₙ XOR a = Sₙ + τ(a) (mod 2^m)` for every `a`. The induction step splits on
the lowest binary digit. With `N = 2^m`, `Sₙ^{(m+1)} = 2 Sₙ^{(m)}` if `n ≤ N`, and
`Sₙ^{(m+1)} = 2 {0, …, N-1} ∪ (2 S_{n-N}^{(m)} + 1)` if `n > N` (`vdcPrefixMem_succ_of_le`,
`vdcPrefixMem_succ_of_gt`). XOR and addition act on the two halves digit by digit; the only carry
is the uniform one from the lowest digit. The new bijection is `τ'(a) = 2 τ(a/2) + (a mod 2)` when
`n ≤ N`; when `n > N` it is `2 τ(a/2)` for even `a` and `2 ((τ(a/2) - 1) mod N) + 1` for odd `a`,
which absorbs the carry. The cell permutation `ψ = cellPerm m τ` then preserves `U[0,1)`
(`measurePreserving_cellPerm`) and moves the digitally shifted set at `u` onto the randomly
shifted set at `ψ(u)`.

**Results.**
* `exists_measurePreserving_digitalShift_prefix`: for `n ≤ 2^m` there is a measure-preserving
  `ψ` with `{φ(i) ⊕ u : i < n} = {fract (φ(i) + ψ(u)) : i < n}` for every `u ∈ [0,1)`; the two
  random point sets have the same law.
* `qmcEstimate_digitalShift_prefix_eq`: the corresponding estimators agree, `Q_D(u) = Q_R(ψ(u))`.
* `map_qmcEstimate_digitalShift_prefix_eq`: hence the two estimators have the same law for every
  measurable `f` (generalising `map_digitalShift_three_eq` and
  `map_qmcEstimate_digitalShift_eq_shiftMod` of `DigitalShift`).
-/

namespace RQMCMarkov.PointSets

open MeasureTheory

/-- The cell index `⌊2^m φ(i)⌋` of the `i`-th van der Corput point at precision `m`. -/
noncomputable def vdcDigit (m i : ℕ) : ℕ := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊

/-- `x` is the cell index of one of the first `n` van der Corput points at precision `m`. -/
def vdcPrefixMem (m n x : ℕ) : Prop := ∃ i < n, vdcDigit m i = x

/-- The digital and the random shift of the cell indices of the first `n` points by `a` and `b`
produce the same set. -/
def PrefixShiftEq (m n a b : ℕ) : Prop :=
  ∀ y, (∃ x, vdcPrefixMem m n x ∧ x ^^^ a = y) ↔ (∃ x, vdcPrefixMem m n x ∧ (x + b) % 2 ^ m = y)

/-- `φ(2^m + i) = φ(i) + 2^{-(m+1)}` for `i < 2^m`. -/
theorem vanDerCorput_two_pow_add (m : ℕ) :
    ∀ i < 2 ^ m, vanDerCorput (2 ^ m + i) = vanDerCorput i + 1 / 2 ^ (m + 1) := by
  induction m with
  | zero =>
    intro i hi
    rw [pow_zero] at hi
    have : i = 0 := by omega
    subst this
    rw [pow_zero, add_zero, vanDerCorput_one_two_three.1, vanDerCorput.eq_1]
    norm_num
  | succ m ih =>
    intro i hi
    have hP : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    rw [vanDerCorput_eq (2 ^ (m + 1) + i), vanDerCorput_eq i,
      show (2 ^ (m + 1) + i) % 2 = i % 2 by omega,
      show (2 ^ (m + 1) + i) / 2 = 2 ^ m + i / 2 by omega, ih (i / 2) (by omega),
      pow_succ (2 : ℝ) (m + 1)]
    ring

/-- The cell index is below `2^m`. -/
theorem vdcDigit_lt (m i : ℕ) : vdcDigit m i < 2 ^ m :=
  floor_two_pow_mul_vanDerCorput_lt m i

/-- Refining the precision doubles the cell index of the first `2^m` points. -/
theorem vdcDigit_succ_of_lt {m i : ℕ} (hi : i < 2 ^ m) :
    vdcDigit (m + 1) i = 2 * vdcDigit m i := by
  have hφ := two_pow_mul_vanDerCorput_eq_floor hi
  unfold vdcDigit
  set d := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ with hd
  rw [pow_succ, mul_comm ((2 : ℝ) ^ m) 2, mul_assoc, hφ,
    show (2 : ℝ) * (d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]

/-- The points `2^m + i`, `i < 2^m`, sit in the odd cells:
`⌊2^{m+1} φ(2^m + i)⌋ = 2 ⌊2^m φ(i)⌋ + 1`. -/
theorem vdcDigit_succ_two_pow_add {m i : ℕ} (hi : i < 2 ^ m) :
    vdcDigit (m + 1) (2 ^ m + i) = 2 * vdcDigit m i + 1 := by
  have hφ := two_pow_mul_vanDerCorput_eq_floor hi
  unfold vdcDigit
  set d := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ with hd
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have h : (2 : ℝ) ^ (m + 1) * vanDerCorput (2 ^ m + i) = ((2 * d + 1 : ℕ) : ℝ) := by
    rw [vanDerCorput_two_pow_add m i hi, mul_add, pow_succ, mul_comm ((2 : ℝ) ^ m) 2, mul_assoc,
      hφ]
    push_cast
    field_simp
  rw [h, Nat.floor_natCast]

/-- Every cell index `x < 2^m` is attained by one of the first `2^m` points. -/
theorem exists_vdcDigit_eq {m x : ℕ} (hx : x < 2 ^ m) : ∃ i < 2 ^ m, vdcDigit m i = x := by
  have hmaps : Set.MapsTo (vdcDigit m) (Finset.range (2 ^ m) : Set ℕ)
      (Finset.range (2 ^ m) : Set ℕ) := fun i _ =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (vdcDigit_lt m i))
  have hinj : Set.InjOn (vdcDigit m) (Finset.range (2 ^ m) : Set ℕ) := fun i hi j hj h =>
    vanDerCorput_digit_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  obtain ⟨i, hi, hix⟩ := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj (le_refl _)
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hx))
  exact ⟨i, Finset.mem_range.mp hi, hix⟩

/-- Low-digit recursion, case `n ≤ 2^m`: the cells at precision `m + 1` are the doubled cells. -/
theorem vdcPrefixMem_succ_of_le {m n : ℕ} (hn : n ≤ 2 ^ m) (x : ℕ) :
    vdcPrefixMem (m + 1) n x ↔
      (x % 2 = 0 ∧ vdcPrefixMem m n (x / 2)) ∨ (x % 2 = 1 ∧ (fun _ : ℕ => False) (x / 2)) := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    left
    rw [vdcDigit_succ_of_lt (by omega)]
    exact ⟨by omega, i, hi, by omega⟩
  · rintro (⟨_, i, hi, hix⟩ | ⟨_, hf⟩)
    · refine ⟨i, hi, ?_⟩
      rw [vdcDigit_succ_of_lt (by omega)]
      omega
    · exact hf.elim

/-- Low-digit recursion, case `2^m < n ≤ 2^{m+1}`: all even cells, and the doubled cells of the
first `n - 2^m` points plus one. -/
theorem vdcPrefixMem_succ_of_gt {m n : ℕ} (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1)) (x : ℕ) :
    vdcPrefixMem (m + 1) n x ↔
      (x % 2 = 0 ∧ (fun z : ℕ => z < 2 ^ m) (x / 2)) ∨
        (x % 2 = 1 ∧ vdcPrefixMem m (n - 2 ^ m) (x / 2)) := by
  have hP : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases lt_or_ge i (2 ^ m) with h | h
    · left
      rw [vdcDigit_succ_of_lt h]
      have := vdcDigit_lt m i
      exact ⟨by omega, by change 2 * vdcDigit m i / 2 < 2 ^ m; omega⟩
    · right
      obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ m + j := ⟨i - 2 ^ m, by omega⟩
      rw [vdcDigit_succ_two_pow_add (by omega)]
      exact ⟨by omega, j, by omega, by omega⟩
  · rintro (⟨_, hx⟩ | ⟨_, j, hj, hjx⟩)
    · obtain ⟨i, hi, hix⟩ := exists_vdcDigit_eq hx
      refine ⟨i, by omega, ?_⟩
      rw [vdcDigit_succ_of_lt hi]
      omega
    · refine ⟨2 ^ m + j, by omega, ?_⟩
      rw [vdcDigit_succ_two_pow_add (by omega)]
      omega

/-- XOR, digit by digit: `x XOR a = y` iff the halves XOR to `y/2` and the lowest digits match. -/
theorem xor_eq_iff_halves (x a y : ℕ) :
    x ^^^ a = y ↔ (x / 2 ^^^ a / 2 = y / 2 ∧ (x % 2 + a % 2) % 2 = y % 2) := by
  have hd : (x ^^^ a) / 2 = x / 2 ^^^ a / 2 := Nat.xor_div_two
  have hm : (x ^^^ a) % 2 = 1 ↔ ¬ (x % 2 = 1 ↔ a % 2 = 1) := Nat.xor_mod_two_eq_one
  constructor
  · rintro rfl
    exact ⟨hd.symm, by omega⟩
  · rintro ⟨h1, h2⟩
    omega

/-- Addition modulo `2N`, digit by digit (with the carry from the lowest digit). -/
theorem add_mod_two_mul_eq_iff (x b y N : ℕ) :
    (x + b) % (2 * N) = y ↔
      ((x / 2 + b / 2 + (x % 2 + b % 2) / 2) % N = y / 2 ∧ (x % 2 + b % 2) % 2 = y % 2) := by
  rw [Nat.mod_mul, show (x + b) / 2 = x / 2 + b / 2 + (x % 2 + b % 2) / 2 by omega]
  omega

/-- XOR-shifting a set given by its even part `A` and odd part `B`. -/
theorem exists_xor_iff_of_decomp {M A B : ℕ → Prop}
    (hM : ∀ x, M x ↔ (x % 2 = 0 ∧ A (x / 2)) ∨ (x % 2 = 1 ∧ B (x / 2))) (a y : ℕ) :
    (∃ x, M x ∧ x ^^^ a = y) ↔
      (y % 2 = a % 2 ∧ ∃ x, A x ∧ x ^^^ (a / 2) = y / 2) ∨
        (y % 2 = (a % 2 + 1) % 2 ∧ ∃ x, B x ∧ x ^^^ (a / 2) = y / 2) := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [xor_eq_iff_halves] at hxy
    rcases (hM x).mp hx with ⟨_, hA⟩ | ⟨_, hB⟩
    · exact Or.inl ⟨by omega, x / 2, hA, hxy.1⟩
    · exact Or.inr ⟨by omega, x / 2, hB, hxy.1⟩
  · rintro (⟨hy, x, hA, hx⟩ | ⟨hy, x, hB, hx⟩)
    · refine ⟨2 * x, (hM _).mpr (Or.inl ⟨by omega, by rwa [show 2 * x / 2 = x by omega]⟩), ?_⟩
      rw [xor_eq_iff_halves, show 2 * x / 2 = x by omega]
      exact ⟨hx, by omega⟩
    · refine ⟨2 * x + 1, (hM _).mpr (Or.inr ⟨by omega, by
        rwa [show (2 * x + 1) / 2 = x by omega]⟩), ?_⟩
      rw [xor_eq_iff_halves, show (2 * x + 1) / 2 = x by omega]
      exact ⟨hx, by omega⟩

/-- Shifting modulo `2N` a set given by its even part `A` and odd part `B`. -/
theorem exists_add_iff_of_decomp {M A B : ℕ → Prop}
    (hM : ∀ x, M x ↔ (x % 2 = 0 ∧ A (x / 2)) ∨ (x % 2 = 1 ∧ B (x / 2))) (b y N : ℕ) :
    (∃ x, M x ∧ (x + b) % (2 * N) = y) ↔
      (y % 2 = b % 2 ∧ ∃ x, A x ∧ (x + b / 2) % N = y / 2) ∨
        (y % 2 = (b % 2 + 1) % 2 ∧ ∃ x, B x ∧ (x + b / 2 + b % 2) % N = y / 2) := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [add_mod_two_mul_eq_iff] at hxy
    rcases (hM x).mp hx with ⟨h0, hA⟩ | ⟨h1, hB⟩
    · refine Or.inl ⟨by omega, x / 2, hA, ?_⟩
      rw [show x / 2 + b / 2 = x / 2 + b / 2 + (x % 2 + b % 2) / 2 by omega]
      exact hxy.1
    · refine Or.inr ⟨by omega, x / 2, hB, ?_⟩
      rw [show x / 2 + b / 2 + b % 2 = x / 2 + b / 2 + (x % 2 + b % 2) / 2 by omega]
      exact hxy.1
  · rintro (⟨hy, x, hA, hx⟩ | ⟨hy, x, hB, hx⟩)
    · refine ⟨2 * x, (hM _).mpr (Or.inl ⟨by omega, by rwa [show 2 * x / 2 = x by omega]⟩), ?_⟩
      rw [add_mod_two_mul_eq_iff,
        show 2 * x / 2 + b / 2 + (2 * x % 2 + b % 2) / 2 = x + b / 2 by omega]
      exact ⟨hx, by omega⟩
    · refine ⟨2 * x + 1, (hM _).mpr (Or.inr ⟨by omega, by
        rwa [show (2 * x + 1) / 2 = x by omega]⟩), ?_⟩
      rw [add_mod_two_mul_eq_iff,
        show (2 * x + 1) / 2 + b / 2 + ((2 * x + 1) % 2 + b % 2) / 2 = x + b / 2 + b % 2 by omega]
      exact ⟨hx, by omega⟩

/-- XOR-shifting the full set `{0, …, 2^m - 1}` gives the full set. -/
theorem exists_lt_xor_iff {m a : ℕ} (ha : a < 2 ^ m) (y : ℕ) :
    (∃ x, (fun z : ℕ => z < 2 ^ m) x ∧ x ^^^ a = y) ↔ y < 2 ^ m := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Nat.xor_lt_two_pow hx ha
  · intro hy
    exact ⟨y ^^^ a, Nat.xor_lt_two_pow hy ha, by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩

/-- Shifting the full set `{0, …, N - 1}` modulo `N` gives the full set. -/
theorem exists_lt_add_mod_iff {N β : ℕ} (hβ : β < N) (y : ℕ) :
    (∃ x, (fun z : ℕ => z < N) x ∧ (x + β) % N = y) ↔ y < N := by
  constructor
  · rintro ⟨x, _, rfl⟩
    exact Nat.mod_lt _ (by omega)
  · intro hy
    refine ⟨(y + N - β) % N, Nat.mod_lt _ (by omega), ?_⟩
    rw [Nat.mod_add_mod, show y + N - β + β = y + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hy]

/-- `(x + ((t + N - 1) mod N) + 1) mod N = (x + t) mod N`. -/
theorem add_pred_mod_add_one (x t N : ℕ) (hN : 0 < N) :
    (x + (t + N - 1) % N + 1) % N = (x + t) % N := by
  have h : x + (t + N - 1) % N + 1 ≡ x + (t + N - 1) + 1 [MOD N] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.add_left x (Nat.mod_modEq (t + N - 1) N))
  rw [h, show x + (t + N - 1) + 1 = x + t + N by omega, Nat.add_mod_right]

/-- An existential with a false first conjunct is false. -/
theorem exists_false_and_iff (p : ℕ → Prop) : (∃ x, (fun _ : ℕ => False) x ∧ p x) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => h, False.elim⟩

/-- **The cell bijection.** For `n ≤ 2^m` there is a bijection `τ` of `{0, …, 2^m - 1}` such
that XOR-shifting the cell indices of the first `n` van der Corput points by `a` gives the same set
as shifting them by `τ(a)` modulo `2^m`. -/
theorem exists_prefix_cellPerm (m : ℕ) :
    ∀ n ≤ 2 ^ m, ∃ τ : ℕ → ℕ, (∀ a < 2 ^ m, τ a < 2 ^ m) ∧
      (∀ a < 2 ^ m, ∀ b < 2 ^ m, τ a = τ b → a = b) ∧
      ∀ a < 2 ^ m, PrefixShiftEq m n a (τ a) := by
  induction m with
  | zero =>
    intro n _
    refine ⟨fun a => a, fun a ha => ha, fun a _ b _ h => h, ?_⟩
    intro a ha y
    rw [pow_zero] at ha
    have ha0 : a = 0 := by omega
    subst ha0
    rw [pow_zero]
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      obtain ⟨i, _, rfl⟩ := hx
      have := vdcDigit_lt 0 i
      rw [pow_zero] at this
      rw [Nat.xor_zero] at hxy
      omega
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      obtain ⟨i, _, rfl⟩ := hx
      have := vdcDigit_lt 0 i
      rw [pow_zero] at this
      rw [Nat.xor_zero]
      omega
  | succ m ih =>
    intro n hn
    have hP : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
    rcases le_or_gt n (2 ^ m) with hle | hgt
    · obtain ⟨τ, hmaps, hinj, heq⟩ := ih n hle
      refine ⟨fun a => 2 * τ (a / 2) + a % 2, ?_, ?_, ?_⟩
      · intro a ha
        have := hmaps (a / 2) (by omega)
        change 2 * τ (a / 2) + a % 2 < 2 ^ (m + 1)
        omega
      · intro a ha b hb h
        change 2 * τ (a / 2) + a % 2 = 2 * τ (b / 2) + b % 2 at h
        have h3 : τ (a / 2) = τ (b / 2) := by omega
        have := hinj (a / 2) (by omega) (b / 2) (by omega) h3
        omega
      · intro a ha y
        have hdec := vdcPrefixMem_succ_of_le hle
        change (∃ x, vdcPrefixMem (m + 1) n x ∧ x ^^^ a = y) ↔
          (∃ x, vdcPrefixMem (m + 1) n x ∧ (x + (2 * τ (a / 2) + a % 2)) % 2 ^ (m + 1) = y)
        rw [exists_xor_iff_of_decomp (A := vdcPrefixMem m n) (B := fun _ => False) hdec, hP,
          exists_add_iff_of_decomp (A := vdcPrefixMem m n) (B := fun _ => False) hdec,
          show (2 * τ (a / 2) + a % 2) % 2 = a % 2 by omega,
          show (2 * τ (a / 2) + a % 2) / 2 = τ (a / 2) by omega,
          heq (a / 2) (by omega) (y / 2), exists_false_and_iff, exists_false_and_iff]
    · obtain ⟨τ, hmaps, hinj, heq⟩ := ih (n - 2 ^ m) (by omega)
      have hdec := vdcPrefixMem_succ_of_gt hgt hn
      refine ⟨fun a => if a % 2 = 0 then 2 * τ (a / 2)
        else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1, ?_, ?_, ?_⟩
      · intro a ha
        have h1 := hmaps (a / 2) (by omega)
        have h2 := Nat.mod_lt (τ (a / 2) + 2 ^ m - 1) hpos
        change (if a % 2 = 0 then 2 * τ (a / 2)
          else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) < 2 ^ (m + 1)
        split_ifs <;> omega
      · intro a ha b hb h
        change (if a % 2 = 0 then 2 * τ (a / 2)
          else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) =
          (if b % 2 = 0 then 2 * τ (b / 2)
          else 2 * ((τ (b / 2) + 2 ^ m - 1) % 2 ^ m) + 1) at h
        have ha2 := hmaps (a / 2) (by omega)
        have hb2 := hmaps (b / 2) (by omega)
        split_ifs at h with h1 h2 h2
        · have := hinj (a / 2) (by omega) (b / 2) (by omega) (by omega)
          omega
        · omega
        · omega
        · have h3 : (τ (a / 2) + 2 ^ m - 1) % 2 ^ m = (τ (b / 2) + 2 ^ m - 1) % 2 ^ m := by
            omega
          have h4 := Nat.ModEq.add_right_cancel' (2 ^ m - 1) (show
            τ (a / 2) + (2 ^ m - 1) ≡ τ (b / 2) + (2 ^ m - 1) [MOD 2 ^ m] by
              unfold Nat.ModEq
              rw [show τ (a / 2) + (2 ^ m - 1) = τ (a / 2) + 2 ^ m - 1 by omega,
                show τ (b / 2) + (2 ^ m - 1) = τ (b / 2) + 2 ^ m - 1 by omega]
              exact h3)
          unfold Nat.ModEq at h4
          rw [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h4
          have := hinj (a / 2) (by omega) (b / 2) (by omega) h4
          omega
      · intro a ha y
        have ha2 := hmaps (a / 2) (by omega)
        change (∃ x, vdcPrefixMem (m + 1) n x ∧ x ^^^ a = y) ↔
          (∃ x, vdcPrefixMem (m + 1) n x ∧ ((x + if a % 2 = 0 then 2 * τ (a / 2)
            else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1)) % 2 ^ (m + 1) = y)
        rw [exists_xor_iff_of_decomp (A := fun z => z < 2 ^ m)
            (B := vdcPrefixMem m (n - 2 ^ m)) hdec, hP,
          exists_add_iff_of_decomp (A := fun z => z < 2 ^ m) (B := vdcPrefixMem m (n - 2 ^ m)) hdec,
          exists_lt_xor_iff (show a / 2 < 2 ^ m by omega), heq (a / 2) (by omega) (y / 2)]
        rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
        · have hc : (if a % 2 = 0 then 2 * τ (a / 2)
              else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) = 2 * τ (a / 2) := by
            simp only [h0, ↓reduceIte]
          rw [hc, show 2 * τ (a / 2) % 2 = 0 by omega,
            show 2 * τ (a / 2) / 2 = τ (a / 2) by omega]
          simp only [add_zero]
          rw [exists_lt_add_mod_iff ha2, h0]
        · have hc : (if a % 2 = 0 then 2 * τ (a / 2)
              else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) =
              2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1 := by
            simp only [h1, one_ne_zero, ↓reduceIte]
          rw [hc,
            show (2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) % 2 = 1 by omega,
            show (2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) / 2 =
              (τ (a / 2) + 2 ^ m - 1) % 2 ^ m by omega,
            exists_lt_add_mod_iff (Nat.mod_lt _ hpos), h1]
          simp only [add_pred_mod_add_one _ (τ (a / 2)) (2 ^ m) hpos]

/-- Cell-index form as Finsets: membership in the cell set of the first `n` points. -/
theorem mem_image_vdcDigit_iff (m n x : ℕ) :
    x ∈ (Finset.range n).image (vdcDigit m) ↔ vdcPrefixMem m n x := by
  simp only [Finset.mem_image, Finset.mem_range, vdcPrefixMem]

/-- **The cell sets coincide**: `Sₙ XOR a = Sₙ + τ(a) (mod 2^m)` as Finsets. -/
theorem image_xor_eq_image_add_mod {m n : ℕ} {a b : ℕ} (h : PrefixShiftEq m n a b) :
    ((Finset.range n).image (vdcDigit m)).image (fun x => x ^^^ a) =
      ((Finset.range n).image (vdcDigit m)).image (fun x => (x + b) % 2 ^ m) := by
  ext y
  rw [Finset.mem_image, Finset.mem_image]
  have := h y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨x', hx', hx'y⟩ := this.mp ⟨x, (mem_image_vdcDigit_iff m n x).mp hx, hxy⟩
    exact ⟨x', (mem_image_vdcDigit_iff m n x').mpr hx', hx'y⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨x', hx', hx'y⟩ := this.mpr ⟨x, (mem_image_vdcDigit_iff m n x).mp hx, hxy⟩
    exact ⟨x', (mem_image_vdcDigit_iff m n x').mpr hx', hx'y⟩

/-- **Same law as random point sets.** For `n ≤ 2^m` there is a measure-preserving map `ψ` of
`U[0,1)` such that for every `u ∈ [0,1)` the digitally shifted first `n` van der Corput points
`{φ(i) ⊕ u}` and the randomly shifted ones `{fract (φ(i) + ψ(u))}` are the same set. -/
theorem exists_measurePreserving_digitalShift_prefix {m n : ℕ} (hn : n ≤ 2 ^ m) :
    ∃ ψ : ℝ → ℝ, MeasurePreserving ψ uniformIco uniformIco ∧
      ∀ u ∈ Set.Ico (0 : ℝ) 1, (Finset.range n).image (digitalShiftSeq m vanDerCorput u) =
        (Finset.range n).image (shiftMod vanDerCorput (ψ u)) := by
  obtain ⟨τ, hmaps, hinj, heq⟩ := exists_prefix_cellPerm m n hn
  refine ⟨cellPerm m τ, measurePreserving_cellPerm m hmaps hinj, fun u hu => ?_⟩
  have ha := floor_two_pow_mul_lt m hu
  have hv : 0 ≤ cellPerm m τ u := by
    unfold cellPerm
    have := Int.fract_nonneg ((2 : ℝ) ^ m * u)
    positivity
  have e1 : (Finset.range n).image (digitalShiftSeq m vanDerCorput u) =
      (((Finset.range n).image (vdcDigit m)).image (fun x => x ^^^ ⌊(2 : ℝ) ^ m * u⌋₊)).image
        (fun j : ℕ => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) := by
    rw [Finset.image_image, Finset.image_image]
    rfl
  have e2 : (Finset.range n).image (shiftMod vanDerCorput (cellPerm m τ u)) =
      (((Finset.range n).image (vdcDigit m)).image
        (fun x => (x + τ ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)).image
        (fun j : ℕ => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) := by
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr fun i hi => ?_
    have hi' : i < 2 ^ m := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_coe.mp hi)) hn
    change Int.fract (vanDerCorput i + cellPerm m τ u) = _
    rw [fract_vanDerCorput_add hi' hv, floor_two_pow_mul_cellPerm, fract_two_pow_mul_cellPerm]
    rfl
  rw [e1, e2, image_xor_eq_image_add_mod (heq _ ha)]

/-- **Same estimator.** With `ψ` as in `exists_measurePreserving_digitalShift_prefix`, the
digitally shifted estimator at `u` equals the randomly shifted estimator at `ψ(u)`, for every `f`.
-/
theorem qmcEstimate_digitalShift_prefix_eq {m n : ℕ} (hn : n ≤ 2 ^ m) :
    ∃ ψ : ℝ → ℝ, MeasurePreserving ψ uniformIco uniformIco ∧ ∀ f : ℝ → ℝ,
      ∀ u ∈ Set.Ico (0 : ℝ) 1, qmcEstimate f (digitalShiftSeq m vanDerCorput u) n =
        qmcEstimate f (shiftMod vanDerCorput (ψ u)) n := by
  obtain ⟨ψ, hψ, hset⟩ := exists_measurePreserving_digitalShift_prefix hn
  refine ⟨ψ, hψ, fun f u hu => ?_⟩
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hD : Set.InjOn (digitalShiftSeq m vanDerCorput u) (Finset.range n : Set ℕ) := by
    intro i hi j hj hij
    have hi' := lt_of_lt_of_le (Finset.mem_range.mp hi) hn
    have hj' := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    have h0 := (div_left_inj' hpos.ne').mp hij
    have h1 : (⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) =
        (⌊(2 : ℝ) ^ m * vanDerCorput j⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) := by
      have h2 := add_right_cancel h0
      exact_mod_cast h2
    rw [Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊, Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊] at h1
    exact vanDerCorput_digit_inj hi' hj' (xor_left_cancel' _ _ _ h1)
  have hcard : ((Finset.range n).image (shiftMod vanDerCorput (ψ u))).card =
      (Finset.range n).card := by
    rw [← hset u hu, Finset.card_image_of_injOn hD]
  have hR : Set.InjOn (shiftMod vanDerCorput (ψ u)) (Finset.range n : Set ℕ) :=
    Finset.card_image_iff.mp hcard
  unfold qmcEstimate
  rw [← Finset.sum_image (f := f) hD, ← Finset.sum_image (f := f) hR, hset u hu]

/-- **Same law of the estimators.** For `n ≤ 2^m` and every measurable `f`, the digitally shifted
and the randomly shifted estimators built on the first `n` van der Corput points have the same
law under `U ~ U[0,1)`. -/
theorem map_qmcEstimate_digitalShift_prefix_eq {f : ℝ → ℝ} (hf : Measurable f) {m n : ℕ}
    (hn : n ≤ 2 ^ m) :
    uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq m vanDerCorput u) n) =
      uniformIco.map (fun u => qmcEstimate f (shiftMod vanDerCorput u) n) := by
  obtain ⟨ψ, hψ, hpt⟩ := qmcEstimate_digitalShift_prefix_eq hn
  have hmR : Measurable fun v => qmcEstimate f (shiftMod vanDerCorput v) n := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact hf.comp (measurable_fract.comp (measurable_const_add _))
  calc uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq m vanDerCorput u) n)
      = uniformIco.map ((fun v => qmcEstimate f (shiftMod vanDerCorput v) n) ∘ ψ) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
        exact hpt f u hu
    _ = _ := by rw [← Measure.map_map hmR hψ.measurable, hψ.map_eq]

end RQMCMarkov.PointSets
