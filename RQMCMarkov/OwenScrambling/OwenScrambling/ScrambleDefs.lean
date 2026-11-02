/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.Unbiased
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Owen's nested uniform scramble: definitions, uniformity, nets, pair law (post #2)

Post #2: "a more powerful but more computationally costly randomization for digital nets is
'Owen Scrambling' which is a 'nested uniform scramble'", and with it "a standard CLT applies"
(Loh 2003). This module sets up the `s`-dimensional objects (base `b ≥ 2`) and proves Owen's three
structural facts (Owen 1995, 1997).

**Digits and boxes.** A coordinate with `D` base-`b` digits is a string `x : Fin D → Fin b`
(digit `0` most significant), with prefix values `prefixVal x r = Σ_{k<r} x_k b^{r-1-k}` and cell
index `cellVal x = prefixVal x D`; `cellFin_bijective` identifies strings with the cells
`0, …, b^D - 1`. The real point with remainder `u` is `digitPoint x u = (cellVal x + u)/b^D`, and
`floor_pow_mul_digitPoint` reads its digits: `⌊b^r · digitPoint x u⌋ = prefixVal x r` for
`u ∈ [0,1)`, `r ≤ D`. The `b`-adic elementary box with levels `r` and index `a` is `elemBox b r a`
(volume `b^{-Σ r_j}`), membership is `boxIndex b r x = a` (`mem_elemBox_iff`), and `IsNet b t m x`
is the `(t,m,s)`-net property (Niederreiter 1992): `b^m` points of `[0,1)^s`, exactly `b^t` in
every elementary box of volume `b^{t-m}`.

**The scramble (reading).** A nested scramble of depth `D` is a family `ρ : Scramble b D` of
permutations of the digits, one for each node (level `k`, prefix `truncDigits k x`) of the
`b`-ary tree; `scramble ρ x` permutes digit `k` of `x` by the permutation of the node of its first
`k` digits. Owen's nested UNIFORM scramble takes `ρ` uniform on the finite set `Scramble b D`
(all node permutations independent and uniform), one independent scramble per coordinate, and
completes the scrambled `D` digits by independent `U[0,1)` remainders: `scrambledPoint ρ d u`. We
read Owen's scramble in this finite-depth form ("on finitely many digits plus uniform
remainders"). For points whose `D`-digit prefixes are distinct in each coordinate (e.g. a
`(0,m,s)`-net and `D ≥ m`, see `injective_coord_net` in `LohCLT`) the digits below depth `D` of the
full (infinite-depth) scramble are permuted at distinct nodes, so they are independent uniform and
the two readings have the same law; this identification is not formalised (the infinite
scramble is not defined here). The law of a random quantity built from `ρ` and the remainders `u`
is the mixture `mixLaw Q Φ = (#R)⁻¹ Σ_ρ Q.map (Φ ρ)`.

## Main results

* `agree_scramble_iff`, `scramble_injective`, `scramble_bijective`: the scramble preserves and
  reflects common prefixes (nested: points of one `b`-adic interval go to one `b`-adic interval).
* **(ii) A scrambled net is a net** (Owen 1995): `isNet_scrambledPoint` — if the digit points form
  a `(t,m,s)`-net, then for EVERY scramble and all remainders in `[0,1)` so do the scrambled
  points.
* **(i) Uniformity** (Owen 1995): `card_scramble_fiber_eq`, `card_scramble_fiber_mul` (each
  string is sent to each string by a fraction `b^{-D}` of the scrambles),
  `sum_map_digitPoint_scramble` (one scrambled coordinate is `U[0,1)`), and
  `mixLaw_scrambledPoint`: every scrambled point is `U[0,1)^s`, whatever the digit point.
  Unbiasedness follows (`ScrambleVariance.integral_scrambledLaw`, via `Unbiased`).
* **(iii) Pair law** (Owen 1997): `card_scramble_pair_eq`, `card_scramble_pair_eq_zero` and
  `card_scramble_pair`: for two strings with exactly `k = commonPrefix x x'` common leading
  digits, the scrambled pair is uniform on the pairs with exactly `k` common leading digits; its
  law `pairKernel k` depends on `(x, x')` only through `k`. The `s`-dimensional version (one
  scramble per coordinate) is `ScrambleHaar.card_scrambleVec_pair`.
* Tools: `card_agree` (`b^{D-r}` strings share a given `r`-digit prefix), `agreeKernel`
  (cell averaging kernels), `sum_pairKernel`, `pairKernel_eq_zero`, `pairKernel_eq_const`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {b D : ℕ}

/-- `Agree r x y`: the base-`b` digit strings `x, y` of length `D` have the same first `r` digits
(digit `0` is the most significant). -/
abbrev Agree (r : ℕ) (x y : Fin D → Fin b) : Prop := ∀ l : Fin D, (l : ℕ) < r → x l = y l

/-- The `k`-digit prefix of a digit string, as a node of the `b`-ary tree: the digits before
position `k`, and `none` from position `k` on. -/
def truncDigits (k : ℕ) (x : Fin D → Fin b) : Fin D → Option (Fin b) :=
  fun l ↦ if (l : ℕ) < k then some (x l) else none

/-- The `k`-th digit of `x` as a natural number (`0` beyond the length `D`). -/
def digitAt (x : Fin D → Fin b) (k : ℕ) : ℕ := if h : k < D then (x ⟨k, h⟩ : ℕ) else 0

/-- The value `Σ_{k<r} x_k b^{r-1-k}` of the first `r` digits of `x`. -/
def prefixVal (x : Fin D → Fin b) : ℕ → ℕ
  | 0 => 0
  | r + 1 => b * prefixVal x r + digitAt x r

/-- The cell index `Σ_{k<D} x_k b^{D-1-k} ∈ [0, b^D)` of a digit string. -/
def cellVal (x : Fin D → Fin b) : ℕ := prefixVal x D

/-- **Owen's nested scramble of depth `D`** (Owen 1995): one permutation `ρ (k, p)` of the `b`
digits for every node `(k, p)` of the `b`-ary tree (level `k`, prefix `p`). -/
abbrev Scramble (b D : ℕ) := Fin D × (Fin D → Option (Fin b)) → Equiv.Perm (Fin b)

/-- The nested scramble applied to a digit string: digit `k` is permuted by the permutation of
the node given by the first `k` digits. -/
def scramble (ρ : Scramble b D) (x : Fin D → Fin b) : Fin D → Fin b :=
  fun k ↦ ρ (k, truncDigits k x) (x k)

/-- Agreement on more digits implies agreement on fewer. -/
theorem agree_mono {r r' : ℕ} (h : r ≤ r') {x y : Fin D → Fin b} (hxy : Agree r' x y) :
    Agree r x y := fun l hl ↦ hxy l (lt_of_lt_of_le hl h)

/-- Agreement is symmetric. -/
theorem agree_symm {r : ℕ} {x y : Fin D → Fin b} (h : Agree r x y) : Agree r y x :=
  fun l hl ↦ (h l hl).symm

/-- Agreement is transitive. -/
theorem agree_trans {r : ℕ} {x y z : Fin D → Fin b} (h : Agree r x y) (h' : Agree r y z) :
    Agree r x z := fun l hl ↦ (h l hl).trans (h' l hl)

/-- Agreement on `D` (or more) digits is equality. -/
theorem agree_iff_eq {r : ℕ} (hr : D ≤ r) {x y : Fin D → Fin b} : Agree r x y ↔ x = y :=
  ⟨fun h ↦ funext fun l ↦ h l (lt_of_lt_of_le l.isLt hr), fun h l _ ↦ by rw [h]⟩

/-- Agreement on `r + 1` digits is agreement on `r` digits and at digit `r`. -/
theorem agree_succ_iff {r : ℕ} (hr : r < D) {x y : Fin D → Fin b} :
    Agree (r + 1) x y ↔ Agree r x y ∧ x ⟨r, hr⟩ = y ⟨r, hr⟩ := by
  constructor
  · intro h
    exact ⟨agree_mono (Nat.le_succ r) h, h ⟨r, hr⟩ (Nat.lt_succ_self r)⟩
  · rintro ⟨h1, h2⟩ l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
    · exact h1 l hl
    · have : l = ⟨r, hr⟩ := Fin.ext hl
      rw [this]
      exact h2

/-- Two `k`-digit prefixes (tree nodes) coincide iff the strings agree on `k` digits. -/
theorem truncDigits_eq_iff {k : ℕ} {x y : Fin D → Fin b} :
    truncDigits k x = truncDigits k y ↔ Agree k x y := by
  constructor
  · intro h l hl
    have := congrFun h l
    simp only [truncDigits, hl, ↓reduceIte, Option.some.injEq] at this
    exact this
  · intro h
    funext l
    by_cases hl : (l : ℕ) < k
    · simp only [truncDigits, hl, ↓reduceIte, h l hl]
    · simp only [truncDigits, hl, ↓reduceIte]

/-- **The nested scramble preserves and reflects common prefixes**: `scramble ρ x` and
`scramble ρ y` agree on their first `r` digits iff `x` and `y` do. -/
theorem agree_scramble_iff (ρ : Scramble b D) (r : ℕ) (x y : Fin D → Fin b) :
    Agree r (scramble ρ x) (scramble ρ y) ↔ Agree r x y := by
  constructor
  · induction r with
    | zero => intro _ l hl; exact absurd hl (Nat.not_lt_zero _)
    | succ r ih =>
      intro h
      have hr := ih (agree_mono (Nat.le_succ r) h)
      by_cases hrD : r < D
      · refine (agree_succ_iff hrD).2 ⟨hr, ?_⟩
        have h2 := h ⟨r, hrD⟩ (Nat.lt_succ_self r)
        have ht : truncDigits r x = truncDigits r y := truncDigits_eq_iff.2 hr
        simp only [scramble] at h2
        rw [ht] at h2
        exact (ρ _).injective h2
      · intro l hl
        exact hr l (lt_of_lt_of_le l.isLt (not_lt.1 hrD))
  · intro h l hl
    have ht : truncDigits l x = truncDigits l y := truncDigits_eq_iff.2 (agree_mono hl.le h)
    simp only [scramble]
    rw [ht, h l hl]

/-- The nested scramble is injective on digit strings. -/
theorem scramble_injective (ρ : Scramble b D) : Function.Injective (scramble ρ) := by
  intro x y h
  have : Agree D (scramble ρ x) (scramble ρ y) := fun l _ ↦ congrFun h l
  exact (agree_iff_eq le_rfl).1 ((agree_scramble_iff ρ D x y).1 this)

/-- The nested scramble is a bijection of the digit strings. -/
theorem scramble_bijective (ρ : Scramble b D) : Function.Bijective (scramble ρ) :=
  Finite.injective_iff_bijective.1 (scramble_injective ρ)

/-- Left-multiplying the scramble by a family `h` of permutations post-composes digit `k` with the
permutation `h` at the node of the original prefix. -/
theorem scramble_mul_apply (h ρ : Scramble b D) (x : Fin D → Fin b) (k : Fin D) :
    scramble (h * ρ) x k = h (k, truncDigits k x) (scramble ρ x k) := rfl

/-- A digit is less than the base. -/
theorem digitAt_lt (hb : 0 < b) (x : Fin D → Fin b) (k : ℕ) : digitAt x k < b := by
  unfold digitAt
  split_ifs with h
  · exact (x ⟨k, h⟩).isLt
  · exact hb

/-- `digitAt` at an index of the string is the digit. -/
theorem digitAt_fin (x : Fin D → Fin b) (l : Fin D) : digitAt x l = (x l : ℕ) := by
  simp only [digitAt, l.isLt, ↓reduceDIte]

/-- The value of an `r`-digit prefix is less than `b^r`. -/
theorem prefixVal_lt (hb : 0 < b) (x : Fin D → Fin b) (r : ℕ) : prefixVal x r < b ^ r := by
  induction r with
  | zero => exact Nat.one_pos
  | succ r ih =>
    change b * prefixVal x r + digitAt x r < b ^ (r + 1)
    have hd := digitAt_lt hb x r
    calc b * prefixVal x r + digitAt x r < b * prefixVal x r + b := by omega
      _ = b * (prefixVal x r + 1) := by ring
      _ ≤ b * b ^ r := Nat.mul_le_mul_left b ih
      _ = b ^ (r + 1) := by ring

/-- Two prefix values agree iff the digits agree. -/
theorem prefixVal_inj_iff (hb : 0 < b) (x y : Fin D → Fin b) (r : ℕ) :
    prefixVal x r = prefixVal y r ↔ ∀ k < r, digitAt x k = digitAt y k := by
  induction r with
  | zero => exact ⟨fun _ k hk ↦ absurd hk (Nat.not_lt_zero _), fun _ ↦ rfl⟩
  | succ r ih =>
    change b * prefixVal x r + digitAt x r = b * prefixVal y r + digitAt y r ↔ _
    have hx := digitAt_lt hb x r
    have hy := digitAt_lt hb y r
    constructor
    · intro h
      have h1 : prefixVal x r = prefixVal y r := by
        have h' : (b * prefixVal x r + digitAt x r) / b = (b * prefixVal y r + digitAt y r) / b :=
          by rw [h]
        rwa [Nat.mul_add_div hb, Nat.mul_add_div hb, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
          add_zero, add_zero] at h'
      have h2 : digitAt x r = digitAt y r := by
        rw [h1] at h
        exact Nat.add_left_cancel h
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact (ih.1 h1) k hk
      · rw [hk]
        exact h2
    · intro h
      rw [ih.2 (fun k hk ↦ h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r)]

/-- For `r ≤ D`, two `r`-digit prefix values agree iff the strings agree on `r` digits. -/
theorem prefixVal_eq_iff_agree (hb : 0 < b) {r : ℕ} (hr : r ≤ D) (x y : Fin D → Fin b) :
    prefixVal x r = prefixVal y r ↔ Agree r x y := by
  rw [prefixVal_inj_iff hb]
  constructor
  · intro h l hl
    have := h l hl
    rw [digitAt_fin, digitAt_fin] at this
    exact Fin.ext this
  · intro h k hk
    have hkD : k < D := lt_of_lt_of_le hk hr
    have := h ⟨k, hkD⟩ hk
    have e1 := digitAt_fin x ⟨k, hkD⟩
    have e2 := digitAt_fin y ⟨k, hkD⟩
    rw [e1, e2, this]

/-- Dropping the last `n - r` digits: `prefixVal x n / b^(n-r) = prefixVal x r`. -/
theorem prefixVal_div (hb : 0 < b) (x : Fin D → Fin b) {r n : ℕ} (h : r ≤ n) :
    prefixVal x n / b ^ (n - r) = prefixVal x r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  clear h
  induction t with
  | zero => rw [add_zero, pow_zero, Nat.div_one]
  | succ t ih =>
    change (b * prefixVal x (r + t) + digitAt x (r + t)) / b ^ (t + 1) = _
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.mul_add_div hb,
      Nat.div_eq_of_lt (digitAt_lt hb x _), add_zero, ih]

/-- The cell index of a string is less than `b^D`. -/
theorem cellVal_lt (hb : 0 < b) (x : Fin D → Fin b) : cellVal x < b ^ D := prefixVal_lt hb x D

/-- The cell index is injective. -/
theorem cellVal_injective (hb : 0 < b) : Function.Injective (cellVal : (Fin D → Fin b) → ℕ) := by
  intro x y h
  exact (agree_iff_eq le_rfl).1 ((prefixVal_eq_iff_agree hb le_rfl x y).1 h)

/-- The cell index as an element of `Fin (b^D)`. -/
def cellFin (hb : 0 < b) (x : Fin D → Fin b) : Fin (b ^ D) := ⟨cellVal x, cellVal_lt hb x⟩

/-- **Digit strings and cells**: `x ↦ cellVal x` is a bijection onto `{0, …, b^D - 1}`. -/
theorem cellFin_bijective (hb : 0 < b) : Function.Bijective (cellFin (D := D) hb) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y h ↦ cellVal_injective hb (congrArg Fin.val h), ?_⟩
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- Every value `a < b^r` (`r ≤ D`) is the `r`-digit prefix value of some string. -/
theorem exists_prefixVal_eq (hb : 0 < b) {r : ℕ} (hr : r ≤ D) {a : ℕ} (ha : a < b ^ r) :
    ∃ x : Fin D → Fin b, prefixVal x r = a := by
  have hlt : a * b ^ (D - r) < b ^ D := by
    calc a * b ^ (D - r) < b ^ r * b ^ (D - r) :=
          Nat.mul_lt_mul_of_pos_right ha (Nat.pow_pos hb)
      _ = b ^ D := by rw [← pow_add, Nat.add_sub_cancel' hr]
  obtain ⟨x, hx⟩ := (cellFin_bijective (D := D) hb).2 ⟨a * b ^ (D - r), hlt⟩
  refine ⟨x, ?_⟩
  have hv : cellVal x = a * b ^ (D - r) := congrArg Fin.val hx
  rw [← prefixVal_div hb x hr]
  change cellVal x / _ = a
  rw [hv, Nat.mul_div_cancel _ (Nat.pow_pos hb)]

/-- The real point of a digit string with remainder `u ∈ [0,1)`: `(cellVal x + u)/b^D`. -/
noncomputable def digitPoint (x : Fin D → Fin b) (u : ℝ) : ℝ :=
  ((cellVal x : ℝ) + u) / (b : ℝ) ^ D

/-- The digit point is `stratumMap (b^D) (cellVal x) u`. -/
theorem digitPoint_eq_stratumMap (x : Fin D → Fin b) (u : ℝ) :
    digitPoint x u = stratumMap (b ^ D) (cellVal x) u := by
  unfold digitPoint stratumMap
  rw [Nat.cast_pow]

/-- **Digits of a digit point**: for `u ∈ [0,1)` and `r ≤ D`,
`⌊b^r · (cellVal x + u)/b^D⌋ = prefixVal x r`. -/
theorem floor_pow_mul_digitPoint (hb : 0 < b) (x : Fin D → Fin b) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) {r : ℕ} (hr : r ≤ D) :
    ⌊(b : ℝ) ^ r * digitPoint x u⌋₊ = prefixVal x r := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have h1 : (b : ℝ) ^ r * digitPoint x u = ((cellVal x : ℝ) + u) / ((b ^ (D - r) : ℕ) : ℝ) := by
    unfold digitPoint
    rw [Nat.cast_pow]
    have hD : (b : ℝ) ^ D = (b : ℝ) ^ r * (b : ℝ) ^ (D - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [hD]
    have : (0 : ℝ) < (b : ℝ) ^ r := pow_pos hb' r
    have : (0 : ℝ) < (b : ℝ) ^ (D - r) := pow_pos hb' _
    field_simp
  rw [h1, Nat.floor_div_natCast, add_comm, Nat.floor_add_natCast hu.1, Nat.floor_eq_zero.2 hu.2,
    zero_add]
  exact prefixVal_div hb x hr

/-- A digit point with remainder in `[0,1)` lies in `[0,1)`. -/
theorem digitPoint_mem_Ico (hb : 0 < b) (x : Fin D → Fin b) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    digitPoint x u ∈ Ico (0 : ℝ) 1 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hpos : (0 : ℝ) < (b : ℝ) ^ D := pow_pos hb' D
  have hc : (cellVal x : ℝ) + 1 ≤ (b : ℝ) ^ D := by
    have := cellVal_lt hb x
    exact_mod_cast this
  unfold digitPoint
  constructor
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) hu.1) hpos.le
  · rw [div_lt_one hpos]
    linarith [hu.2]
/-- The `b`-adic **elementary box** with levels `r` and index `a`:
`Π_j [a_j / b^{r_j}, (a_j + 1) / b^{r_j})`, of volume `b^{-Σ_j r_j}`. -/
def elemBox (b : ℕ) {s : ℕ} (r a : Fin s → ℕ) : Set (Fin s → ℝ) :=
  Set.pi univ fun j ↦ Ico ((a j : ℝ) / (b : ℝ) ^ r j) (((a j : ℝ) + 1) / (b : ℝ) ^ r j)

/-- The index of the level-`r` elementary box containing `x`: `j ↦ ⌊b^{r_j} x_j⌋`. -/
noncomputable def boxIndex (b : ℕ) {s : ℕ} (r : Fin s → ℕ) (x : Fin s → ℝ) : Fin s → ℕ :=
  fun j ↦ ⌊(b : ℝ) ^ r j * x j⌋₊

/-- A point with nonnegative coordinates lies in the elementary box `(r, a)` iff its box index
at levels `r` is `a`. -/
theorem mem_elemBox_iff (hb : 0 < b) {s : ℕ} (r a : Fin s → ℕ) {x : Fin s → ℝ}
    (hx : ∀ j, 0 ≤ x j) : x ∈ elemBox b r a ↔ boxIndex b r x = a := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  unfold elemBox boxIndex
  rw [Set.mem_univ_pi, funext_iff]
  refine forall_congr' fun j ↦ ?_
  have hq : (0 : ℝ) < (b : ℝ) ^ r j := pow_pos hb' _
  rw [Nat.floor_eq_iff (mul_nonneg hq.le (hx j)), mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq,
    mul_comm (x j)]

/-- A **`(t,m,s)`-net in base `b`** (Niederreiter 1992): `n = b^m` points of `[0,1)^s` such that
every elementary box of volume `b^{t-m}` (levels with `Σ_j r_j = m - t`) contains exactly `b^t`
of the points. Box membership is expressed by `boxIndex` (`mem_elemBox_iff`). -/
def IsNet (b t m : ℕ) {s n : ℕ} (x : Fin n → Fin s → ℝ) : Prop :=
  t ≤ m ∧ n = b ^ m ∧ (∀ i j, x i j ∈ Ico (0 : ℝ) 1) ∧
    ∀ r a : Fin s → ℕ, ∑ j, r j = m - t → (∀ j, a j < b ^ r j) →
      (Finset.univ.filter fun i ↦ boxIndex b r (x i) = a).card = b ^ t

/-- The **scrambled point**: coordinate `j` of the digit point `d` is scrambled by the nested
scramble `ρ j` and completed by the remainder `u j`. -/
noncomputable def scrambledPoint {s : ℕ} (ρ : Fin s → Scramble b D) (d : Fin s → Fin D → Fin b)
    (u : Fin s → ℝ) : Fin s → ℝ :=
  fun j ↦ digitPoint (scramble (ρ j) (d j)) (u j)

/-- **A scrambled net is a net** (Owen 1995, item (ii)): if the points
`x_i = (cellVal (d i j) / b^D)_j` form a `(t,m,s)`-net in base `b` with `m - t ≤ D` digits, then
for EVERY nested scramble `ρ` and all remainders `u ∈ [0,1)` the scrambled points form a
`(t,m,s)`-net in base `b`. -/
theorem isNet_scrambledPoint (hb : 0 < b) {t m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m - t ≤ D) (hnet : IsNet b t m fun i j ↦ digitPoint (d i j) 0)
    (ρ : Fin s → Scramble b D) {u : Fin n → Fin s → ℝ} (hu : ∀ i j, u i j ∈ Ico (0 : ℝ) 1) :
    IsNet b t m fun i ↦ scrambledPoint ρ (d i) (u i) := by
  obtain ⟨htm, hn, _, hcount⟩ := hnet
  refine ⟨htm, hn, fun i j ↦ digitPoint_mem_Ico hb _ (hu i j), ?_⟩
  intro r a hr ha
  have hrD : ∀ j, r j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r j)) (Finset.mem_univ j)) hr.le) hmD
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  -- a string whose scramble has prefix value `a j`
  have he : ∀ j, ∃ e : Fin D → Fin b, prefixVal (scramble (ρ j) e) (r j) = a j := by
    intro j
    obtain ⟨w, hw⟩ := exists_prefixVal_eq hb (hrD j) (ha j)
    obtain ⟨e, he⟩ := (scramble_bijective (ρ j)).2 w
    exact ⟨e, by rw [he, hw]⟩
  choose e he using he
  set a' : Fin s → ℕ := fun j ↦ prefixVal (e j) (r j) with ha'
  have ha'lt : ∀ j, a' j < b ^ r j := fun j ↦ prefixVal_lt hb _ _
  have key : ∀ i, boxIndex b r (scrambledPoint ρ (d i) (u i)) = a ↔
      boxIndex b r (fun j ↦ digitPoint (d i j) 0) = a' := by
    intro i
    unfold boxIndex scrambledPoint
    simp only [funext_iff, floor_pow_mul_digitPoint hb _ (hu i _) (hrD _),
      floor_pow_mul_digitPoint hb _ h0 (hrD _)]
    refine forall_congr' fun j ↦ ?_
    rw [← he j, ha', prefixVal_eq_iff_agree hb (hrD j), prefixVal_eq_iff_agree hb (hrD j),
      agree_scramble_iff]
  rw [Finset.filter_congr (fun i _ ↦ key i)]
  exact hcount r a' hr ha'lt

/-- **Uniformity of one scrambled string, combinatorial form**: for a fixed string `x`, the
number of nested scrambles `ρ` with `scramble ρ x = y` does not depend on the target `y`. -/
theorem card_scramble_fiber_eq (x y y' : Fin D → Fin b) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y).card =
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y').card := by
  have key : ∀ y y' : Fin D → Fin b,
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y).card ≤
        (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y').card := by
    intro y y'
    let h : Scramble b D := fun node ↦ Equiv.swap (y node.1) (y' node.1)
    refine Finset.card_le_card_of_injOn (fun ρ ↦ h * ρ) ?_ ?_
    · intro ρ hρ
      rw [Finset.mem_coe, Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, funext fun k ↦ ?_⟩
      rw [scramble_mul_apply, hρ.2]
      exact Equiv.swap_apply_left _ _
    · intro ρ _ ρ' _ hh
      exact mul_left_cancel hh
  exact le_antisymm (key y y') (key y' y)

/-- **Each scrambled string is uniform** (item (i), combinatorial form): exactly a fraction
`b^{-D}` of the nested scrambles send `x` to any given string `y`. -/
theorem card_scramble_fiber_mul (x y : Fin D → Fin b) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y).card * b ^ D =
      Fintype.card (Scramble b D) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := fun ρ : Scramble b D ↦ scramble ρ x) (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
  have hc : Fintype.card (Fin D → Fin b) = b ^ D := by
    simp only [Fintype.card_fun, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun y' _ ↦ card_scramble_fiber_eq x y' y), Finset.sum_const,
    Finset.card_univ, Finset.card_univ, hc, smul_eq_mul] at h
  rw [h, mul_comm]

/-- Summing a function of the scrambled string over all scrambles: each string is hit by
`#Scramble / b^D` scrambles. -/
theorem sum_scramble_eq {M : Type*} [AddCommMonoid M] (x : Fin D → Fin b)
    (G : (Fin D → Fin b) → M) :
    ∑ ρ : Scramble b D, G (scramble ρ x) =
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = x).card • ∑ y, G y := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ρ : Scramble b D ↦ scramble ρ x), Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_congr rfl (fun ρ hρ ↦ by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const,
    card_scramble_fiber_eq x y x]

/-- **A scrambled coordinate is uniform on `[0,1)`** (item (i), one coordinate): averaging over
the nested scrambles, the law of `(cellVal (scramble ρ x) + U)/b^D` with `U ~ U[0,1)` is
`U[0,1)`: `Σ_ρ law = #Scramble • U[0,1)`. -/
theorem sum_map_digitPoint_scramble (hb : 0 < b) (x : Fin D → Fin b) :
    ∑ ρ : Scramble b D, uniformIco.map (digitPoint (scramble ρ x)) =
      (Fintype.card (Scramble b D) : ℝ≥0∞) • uniformIco := by
  have hbD : b ^ D ≠ 0 := (Nat.pow_pos hb).ne'
  rw [sum_scramble_eq x (fun y ↦ uniformIco.map (digitPoint y))]
  have h1 : ∑ y : Fin D → Fin b, uniformIco.map (digitPoint y) =
      ∑ i : Fin (b ^ D), uniformIco.map (stratumMap (b ^ D) i) := by
    rw [← (cellFin_bijective (D := D) hb).sum_comp
      (fun i : Fin (b ^ D) ↦ uniformIco.map (stratumMap (b ^ D) i))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    congr 1
    funext u
    rw [digitPoint_eq_stratumMap]
    rfl
  rw [h1, sum_map_stratumMap hbD, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
    ← card_scramble_fiber_mul x x, Nat.cast_mul]

/-- The law of a random quantity `Φ ρ u` when the scramble `ρ` is uniform on the finite type `R`
and independent of `u ~ Q`: the mixture `(#R)⁻¹ Σ_ρ Q.map (Φ ρ)`. -/
noncomputable def mixLaw {R E F : Type*} [Fintype R] [MeasurableSpace E] [MeasurableSpace F]
    (Q : Measure E) (Φ : R → E → F) : Measure F :=
  (Fintype.card R : ℝ≥0∞)⁻¹ • ∑ ρ, Q.map (Φ ρ)

/-- Measurability of a digit point in its remainder. -/
theorem measurable_digitPoint (x : Fin D → Fin b) : Measurable (digitPoint x) :=
  (measurable_const_add _).div_const _

/-- Measurability of a scrambled point in its remainders. -/
theorem measurable_scrambledPoint {s : ℕ} (ρ : Fin s → Scramble b D)
    (d : Fin s → Fin D → Fin b) : Measurable (scrambledPoint ρ d) :=
  measurable_pi_iff.2 fun j ↦ (measurable_digitPoint _).comp (measurable_pi_apply j)

/-- **Each scrambled point is uniform on `[0,1)^s`** (Owen 1995; item (i)): with independent
uniformly random nested scrambles in the `s` coordinates and independent `U[0,1)^s` remainders,
the scrambled point `scrambledPoint ρ d u` of ANY digit point `d` has law `U[0,1)^s`. -/
theorem mixLaw_scrambledPoint (hb : 0 < b) {s : ℕ} (d : Fin s → Fin D → Fin b) :
    mixLaw (uniformCube s) (fun (ρ : Fin s → Scramble b D) u ↦ scrambledPoint ρ d u) =
      uniformCube s := by
  have := isProbabilityMeasure_uniformIco
  have hmap : ∀ ρ : Fin s → Scramble b D, (uniformCube s).map (scrambledPoint ρ d) =
      Measure.pi fun j ↦ uniformIco.map (digitPoint (scramble (ρ j) (d j))) := fun ρ ↦
    Measure.pi_map_pi (fun j ↦ (measurable_digitPoint _).aemeasurable)
  unfold mixLaw
  simp only [hmap]
  symm
  refine Measure.pi_eq fun S hS ↦ ?_
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have h1 : ∀ ρ : Fin s → Scramble b D,
      (Measure.pi fun j ↦ uniformIco.map (digitPoint (scramble (ρ j) (d j)))) (Set.pi univ S) =
        ∏ j, uniformIco.map (digitPoint (scramble (ρ j) (d j))) (S j) := fun ρ ↦
    Measure.pi_pi _ _
  rw [Finset.sum_congr rfl (fun ρ _ ↦ h1 ρ)]
  rw [← Fintype.prod_sum (fun j (a : Scramble b D) ↦
    uniformIco.map (digitPoint (scramble a (d j))) (S j))]
  have h2 : ∀ j, ∑ a : Scramble b D, uniformIco.map (digitPoint (scramble a (d j))) (S j) =
      (Fintype.card (Scramble b D) : ℝ≥0∞) * uniformIco (S j) := by
    intro j
    rw [← Measure.finsetSum_apply, sum_map_digitPoint_scramble hb, Measure.smul_apply,
      smul_eq_mul]
  rw [Finset.prod_congr rfl (fun j _ ↦ h2 j), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← mul_assoc, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, ENNReal.inv_mul_cancel, one_mul]
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)

/-- Any two distinct digits can be sent to any two distinct digits by a permutation. -/
theorem exists_perm_pair {x x' z z' : Fin b} (hx : x ≠ x') (hz : z ≠ z') :
    ∃ τ : Equiv.Perm (Fin b), τ x = z ∧ τ x' = z' := by
  refine ⟨Equiv.swap (Equiv.swap x z x') z' * Equiv.swap x z, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hz
    intro h
    have : Equiv.swap x z x = Equiv.swap x z x' := by rw [Equiv.swap_apply_left]; exact h
    exact hx ((Equiv.swap x z).injective this)
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- Two strings whose `l`-digit prefixes agree, while they differ at digit `k` (and agree before
it), have `l ≤ k`. -/
theorem le_of_agree_of_ne {k : ℕ} (hk : k < D) {x x' : Fin D → Fin b}
    (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩) {l : ℕ} (hl : Agree l x x') : l ≤ k := by
  by_contra h
  exact hxk (hl ⟨k, hk⟩ (lt_of_not_ge h))

/-- The pair-fibre comparison behind the pair law: for two pairs of targets with the same exact
common prefix `k`, the second fibre is at least as large as the first. -/
theorem card_scramble_pair_le {k : ℕ} (hk : k < D) {x x' y y' z z' : Fin D → Fin b}
    (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩)
    (hy : Agree k y y') (hyk : y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩)
    (hz : Agree k z z') (hzk : z ⟨k, hk⟩ ≠ z' ⟨k, hk⟩) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card ≤
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = z ∧ scramble ρ x' = z').card := by
  obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_pair hyk hzk
  let α : Fin D → Equiv.Perm (Fin b) := fun l ↦
    if (l : ℕ) = k then τ else Equiv.swap (y l) (z l)
  have hα : ∀ l, α l (y l) = z l := by
    intro l
    by_cases hl : (l : ℕ) = k
    · have : l = ⟨k, hk⟩ := Fin.ext hl
      simp only [α, hl, ↓reduceIte]
      rw [this, hτ1]
    · simp only [α, hl, ↓reduceIte]
      exact Equiv.swap_apply_left _ _
  let h : Scramble b D := fun node ↦
    if node.2 = truncDigits node.1 x then α node.1
    else if node.2 = truncDigits node.1 x' then Equiv.swap (y' node.1) (z' node.1) else 1
  refine Finset.card_le_card_of_injOn (fun ρ ↦ h * ρ) ?_ ?_
  · intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter] at hρ ⊢
    obtain ⟨_, h1, h2⟩ := hρ
    refine ⟨Finset.mem_univ _, funext fun l ↦ ?_, funext fun l ↦ ?_⟩
    · rw [scramble_mul_apply, h1]
      simp only [h, ↓reduceIte]
      exact hα l
    · rw [scramble_mul_apply, h2]
      by_cases ht : truncDigits l x' = truncDigits l x
      · simp only [h, ht, ↓reduceIte]
        have hle := le_of_agree_of_ne hk hxk (truncDigits_eq_iff.1 ht.symm)
        rcases lt_or_eq_of_le hle with hlt | heq
        · rw [← hy l hlt, ← hz l hlt]
          exact hα l
        · have : l = ⟨k, hk⟩ := Fin.ext heq
          simp only [α, heq, ↓reduceIte]
          rw [this, hτ2]
      · simp only [h, ht, ↓reduceIte]
        exact Equiv.swap_apply_left _ _
  · intro ρ _ ρ' _ hh
    exact mul_left_cancel hh

/-- **Pair law of a nested scramble, combinatorial form** (Owen 1997, item (iii)): if `x, x'`
differ at digit `k < D`, then the number of scrambles sending `(x, x')` to a
target pair `(y, y')` is the same for every target pair that shares exactly its first `k` digits,
and zero for every other target pair. -/
theorem card_scramble_pair_eq {k : ℕ} (hk : k < D) {x x' : Fin D → Fin b}
    (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩) (y y' z z' : Fin D → Fin b)
    (hy : Agree k y y') (hyk : y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩)
    (hz : Agree k z z') (hzk : z ⟨k, hk⟩ ≠ z' ⟨k, hk⟩) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card =
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = z ∧ scramble ρ x' = z').card :=
  le_antisymm (card_scramble_pair_le hk hxk hy hyk hz hzk)
    (card_scramble_pair_le hk hxk hz hzk hy hyk)

/-- The pair fibre is empty unless the target pair has the same exact common prefix. -/
theorem card_scramble_pair_eq_zero {k : ℕ} (hk : k < D) {x x' : Fin D → Fin b}
    (hx : Agree k x x') (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩) {y y' : Fin D → Fin b}
    (hy : ¬ (Agree k y y' ∧ y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩)) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ρ - ⟨h1, h2⟩
  apply hy
  rw [← h1, ← h2]
  refine ⟨(agree_scramble_iff ρ k x x').2 hx, fun hc ↦ hxk ?_⟩
  have hk1 : Agree (k + 1) (scramble ρ x) (scramble ρ x') :=
    (agree_succ_iff hk).2 ⟨(agree_scramble_iff ρ k x x').2 hx, hc⟩
  exact ((agree_succ_iff hk).1 ((agree_scramble_iff ρ (k + 1) x x').1 hk1)).2

/-- Agreement on `r` digits is agreement on `min r D` digits. -/
theorem agree_min_iff (r : ℕ) (x y : Fin D → Fin b) : Agree (min r D) x y ↔ Agree r x y := by
  constructor
  · intro h l hl
    exact h l (lt_min hl l.isLt)
  · intro h l hl
    exact h l (lt_of_lt_of_le hl (min_le_left _ _))

/-- **Counting a prefix class**: exactly `b^{D-r}` strings share their first `r` digits with a
given string. -/
theorem card_agree (hb : 0 < b) (r : ℕ) (y : Fin D → Fin b) :
    (Finset.univ.filter fun y' : Fin D → Fin b ↦ Agree r y y').card = b ^ (D - min r D) := by
  set r' := min r D with hr'
  have hrD : r' ≤ D := min_le_right _ _
  have hq : 0 < b ^ (D - r') := Nat.pow_pos hb
  have hbD : b ^ D = b ^ r' * b ^ (D - r') := by rw [← pow_add, Nat.add_sub_cancel' hrD]
  set q := b ^ (D - r') with hqdef
  set a := prefixVal y r' with ha
  have hcell : ∀ y' : Fin D → Fin b, Agree r y y' ↔ cellVal y' / q = a := by
    intro y'
    rw [← agree_min_iff, ← hr', ← prefixVal_eq_iff_agree hb hrD, ha, eq_comm, hqdef]
    unfold cellVal
    rw [prefixVal_div hb y' hrD]
  have halt : a < b ^ r' := prefixVal_lt hb y r'
  rw [← Finset.card_range q]
  refine Finset.card_bij (fun y' _ ↦ cellVal y' - a * q) ?_ ?_ ?_
  · intro y' hy'
    rw [Finset.mem_filter, hcell] at hy'
    rw [Finset.mem_range]
    have h1 := Nat.div_add_mod (cellVal y') q
    have h2 := Nat.mod_lt (cellVal y') hq
    rw [hy'.2] at h1
    have : q * a = a * q := mul_comm _ _
    omega
  · intro y₁ h₁ y₂ h₂ h12
    rw [Finset.mem_filter, hcell] at h₁ h₂
    have e1 := Nat.div_add_mod (cellVal y₁) q
    have e2 := Nat.div_add_mod (cellVal y₂) q
    rw [h₁.2] at e1
    rw [h₂.2] at e2
    have : q * a = a * q := mul_comm _ _
    exact cellVal_injective hb (by omega)
  · intro t ht
    rw [Finset.mem_range] at ht
    have hlt : a * q + t < b ^ D := by
      rw [hbD]
      calc a * q + t < a * q + q := by omega
        _ = (a + 1) * q := by ring
        _ ≤ b ^ r' * q := Nat.mul_le_mul_right _ halt
    obtain ⟨y', hy'⟩ := (cellFin_bijective (D := D) hb).2 ⟨a * q + t, hlt⟩
    have hv : cellVal y' = a * q + t := congrArg Fin.val hy'
    refine ⟨y', ?_, ?_⟩
    · rw [Finset.mem_filter, hcell, hv]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, zero_add]
    · simp only [hv, Nat.add_sub_cancel_left]

/-- The number of leading digits common to `x` and `y` (`D` when `x = y`). -/
def commonPrefix (x y : Fin D → Fin b) : ℕ := Nat.findGreatest (fun r ↦ Agree r x y) D

/-- The common prefix length is at most `D`. -/
theorem commonPrefix_le (x y : Fin D → Fin b) : commonPrefix x y ≤ D := Nat.findGreatest_le D

/-- `x` and `y` agree on `r ≤ D` digits iff `r ≤ commonPrefix x y`. -/
theorem agree_iff_le_commonPrefix {r : ℕ} (hr : r ≤ D) (x y : Fin D → Fin b) :
    Agree r x y ↔ r ≤ commonPrefix x y := by
  constructor
  · exact fun h ↦ Nat.le_findGreatest hr h
  · intro h
    have hspec : Agree (commonPrefix x y) x y :=
      Nat.findGreatest_spec (P := fun r ↦ Agree r x y) (Nat.zero_le D)
        (fun l hl ↦ absurd hl (Nat.not_lt_zero _))
    exact agree_mono h hspec

/-- Two strings agree on their common prefix. -/
theorem agree_commonPrefix (x y : Fin D → Fin b) : Agree (commonPrefix x y) x y :=
  (agree_iff_le_commonPrefix (commonPrefix_le x y) x y).2 le_rfl

/-- Two strings differ right after their common prefix. -/
theorem ne_at_commonPrefix {x y : Fin D → Fin b} (h : commonPrefix x y < D) :
    x ⟨commonPrefix x y, h⟩ ≠ y ⟨commonPrefix x y, h⟩ := by
  intro hc
  have := (agree_succ_iff h).2 ⟨agree_commonPrefix x y, hc⟩
  have := (agree_iff_le_commonPrefix (Nat.succ_le_of_lt h) x y).1 this
  omega

/-- The common prefix length of the scrambled strings is that of the strings. -/
theorem commonPrefix_scramble (ρ : Scramble b D) (x y : Fin D → Fin b) :
    commonPrefix (scramble ρ x) (scramble ρ y) = commonPrefix x y := by
  unfold commonPrefix
  congr 1
  funext r
  exact propext (agree_scramble_iff ρ r x y)

/-- The **averaging kernel at level `r`**: `K_r(x, y) = b^{min(r,D)} / b^D` if `x, y` share their
first `r` digits, else `0`. `y ↦ K_r(x, y)` is the uniform law on the level-`r` cell of `x`. -/
noncomputable def agreeKernel (r : ℕ) (x y : Fin D → Fin b) : ℝ :=
  if Agree r x y then (b : ℝ) ^ min r D / (b : ℝ) ^ D else 0

/-- The averaging kernel is symmetric. -/
theorem agreeKernel_comm (r : ℕ) (x y : Fin D → Fin b) :
    agreeKernel r x y = agreeKernel r y x := by
  unfold agreeKernel
  by_cases h : Agree r x y
  · rw [ite_eq_left h, ite_eq_left (agree_symm h)]
  · have h' : ¬ Agree r y x := fun h' ↦ h (agree_symm h')
    rw [ite_eq_right h, ite_eq_right h']

/-- The averaging kernel has row sums `1`. -/
theorem sum_agreeKernel (hb : 0 < b) (r : ℕ) (x : Fin D → Fin b) :
    ∑ y, agreeKernel r x y = 1 := by
  unfold agreeKernel
  rw [← Finset.sum_filter, Finset.sum_const, card_agree hb, nsmul_eq_mul, Nat.cast_pow]
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have : (b : ℝ) ^ (D - min r D) * (b : ℝ) ^ min r D = (b : ℝ) ^ D := by
    rw [← pow_add, Nat.sub_add_cancel (min_le_right _ _)]
  rw [mul_div_assoc', this, div_self (pow_pos hb' D).ne']

/-- The **pair kernel** of `k` common digits: `π_k = (b K_k - K_{k+1}) / ((b - 1) b^D)`. For
`k < D` it is the uniform law on the pairs of strings with exactly `k` common leading digits; for
`k = D` it is the uniform law on the diagonal. -/
noncomputable def pairKernel (k : ℕ) (x y : Fin D → Fin b) : ℝ :=
  ((b : ℝ) * agreeKernel k x y - agreeKernel (k + 1) x y) / (((b : ℝ) - 1) * (b : ℝ) ^ D)

/-- The pair kernel is a probability on pairs. -/
theorem sum_pairKernel (hb : 1 < b) (k : ℕ) :
    ∑ x : Fin D → Fin b, ∑ y, pairKernel k x y = 1 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos (Nat.cast_pos.2 hb0) D
  unfold pairKernel
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_agreeKernel hb0,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]
  rw [div_eq_one_iff_eq (mul_pos hb1 hbD).ne']
  ring

/-- The pair kernel vanishes off the pairs with exactly `k` common digits (`k < D`). -/
theorem pairKernel_eq_zero {k : ℕ} (hk : k < D) {x y : Fin D → Fin b}
    (h : ¬ (Agree k x y ∧ x ⟨k, hk⟩ ≠ y ⟨k, hk⟩)) : pairKernel k x y = 0 := by
  unfold pairKernel agreeKernel
  by_cases h1 : Agree k x y
  · have h2 : Agree (k + 1) x y := (agree_succ_iff hk).2 ⟨h1, not_not.1 fun h' ↦ h ⟨h1, h'⟩⟩
    rw [ite_eq_left h1, ite_eq_left h2,
      min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk), pow_succ]
    ring
  · have h2 : ¬ Agree (k + 1) x y := fun h' ↦ h1 (agree_mono (Nat.le_succ k) h')
    rw [ite_eq_right h1, ite_eq_right h2]
    ring

/-- The pair kernel is constant on the pairs with exactly `k` common digits (`k < D`). -/
theorem pairKernel_eq_const {k : ℕ} (hk : k < D) {x y : Fin D → Fin b}
    (h1 : Agree k x y) (h2 : x ⟨k, hk⟩ ≠ y ⟨k, hk⟩) :
    pairKernel k x y = (b : ℝ) ^ (k + 1) / (((b : ℝ) - 1) * (b : ℝ) ^ D * (b : ℝ) ^ D) := by
  have h3 : ¬ Agree (k + 1) x y := fun h' ↦ h2 ((agree_succ_iff hk).1 h').2
  unfold pairKernel agreeKernel
  rw [ite_eq_left h1, ite_eq_right h3, min_eq_left hk.le,
    pow_succ, sub_zero]
  field_simp

/-- The pair law off the diagonal (`k < D` exact common digits), see `card_scramble_pair`. -/
theorem card_scramble_pair_of_lt (hb : 1 < b) {k : ℕ} (hkD : k < D) {x x' : Fin D → Fin b}
    (hx : Agree k x x') (hxk : x ⟨k, hkD⟩ ≠ x' ⟨k, hkD⟩) (y y' : Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card : ℝ) =
      Fintype.card (Scramble b D) * pairKernel k y y' := by
  set T : (Fin D → Fin b) → (Fin D → Fin b) → Prop :=
    fun y y' ↦ Agree k y y' ∧ y ⟨k, hkD⟩ ≠ y' ⟨k, hkD⟩ with hT
  set c : ℕ := (Finset.univ.filter fun ρ : Scramble b D ↦
    scramble ρ x = x ∧ scramble ρ x' = x').card with hc
  have hfib : ∀ y y', ((Finset.univ.filter fun ρ : Scramble b D ↦
      scramble ρ x = y ∧ scramble ρ x' = y').card : ℝ) = if T y y' then (c : ℝ) else 0 := by
    intro y y'
    by_cases hyy : T y y'
    · simp only [hyy, ↓reduceIte]
      rw [hc, card_scramble_pair_eq hkD hxk y y' x x' hyy.1 hyy.2 hx hxk]
    · simp only [hyy, ↓reduceIte]
      rw [card_scramble_pair_eq_zero hkD hx hxk hyy, Nat.cast_zero]
  set κ : ℝ := (b : ℝ) ^ (k + 1) / (((b : ℝ) - 1) * (b : ℝ) ^ D * (b : ℝ) ^ D) with hκ
  have hker : ∀ y y', pairKernel k y y' = if T y y' then κ else 0 := by
    intro y y'
    by_cases hyy : T y y'
    · simp only [hyy, ↓reduceIte]
      rw [pairKernel_eq_const hkD hyy.1 hyy.2]
    · simp only [hyy, ↓reduceIte]
      rw [pairKernel_eq_zero hkD hyy]
  set NT : ℝ := ∑ y : Fin D → Fin b, ∑ y' : Fin D → Fin b, if T y y' then (1 : ℝ) else 0
  have hsumκ : κ * NT = 1 := by
    rw [← sum_pairKernel hb k (D := D), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    rw [hker y y']
    split_ifs <;> ring
  have hsumc : (c : ℝ) * NT = Fintype.card (Scramble b D) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := fun ρ : Scramble b D ↦ (scramble ρ x, scramble ρ x'))
      (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ] at h
    rw [h, Nat.cast_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    have : (Finset.univ.filter fun ρ : Scramble b D ↦
        (scramble ρ x, scramble ρ x') = (y, y')) =
        (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y') := by
      refine Finset.filter_congr fun ρ _ ↦ ?_
      exact Prod.ext_iff
    rw [this, hfib y y']
    split_ifs <;> ring
  rw [hfib, hker]
  split_ifs
  · rw [← hsumc, mul_assoc, mul_comm NT κ, hsumκ, mul_one]
  · ring

/-- The pair law on the diagonal (`x = x'`), see `card_scramble_pair`. -/
theorem card_scramble_pair_diag (hb : 1 < b) (x y y' : Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x = y').card : ℝ) =
      Fintype.card (Scramble b D) * pairKernel D y y' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hfilter : (Finset.univ.filter fun ρ : Scramble b D ↦
      scramble ρ x = y ∧ scramble ρ x = y') =
      if y = y' then Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y else ∅ := by
    split_ifs with hyy
    · subst hyy
      exact Finset.filter_congr fun ρ _ ↦ and_self_iff
    · rw [Finset.filter_eq_empty_iff]
      rintro ρ - ⟨h1, h2⟩
      exact hyy (h1.symm.trans h2)
  have hfib := card_scramble_fiber_mul x y
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos (Nat.cast_pos.2 hb0) D
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  unfold pairKernel agreeKernel
  rw [hfilter, min_eq_right (Nat.le_succ D), min_self]
  by_cases hyy : y = y'
  · have h1 : Agree D y y' := (agree_iff_eq le_rfl).2 hyy
    have h2 : Agree (D + 1) y y' := (agree_iff_eq (Nat.le_succ D)).2 hyy
    rw [ite_eq_left hyy, ite_eq_left h1, ite_eq_left h2]
    have hc : ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y').card : ℝ) *
        (b : ℝ) ^ D = Fintype.card (Scramble b D) := by
      rw [← hyy]
      exact_mod_cast hfib
    rw [← hc]
    field_simp
    rw [hyy]
  · have h1 : ¬ Agree D y y' := fun h ↦ hyy ((agree_iff_eq le_rfl).1 h)
    have h2 : ¬ Agree (D + 1) y y' := fun h ↦ hyy ((agree_iff_eq (Nat.le_succ D)).1 h)
    rw [ite_eq_right hyy, ite_eq_right h1, ite_eq_right h2,
      Finset.card_empty, Nat.cast_zero]
    ring

/-- **Pair law of a nested scramble** (Owen 1997, item (iii)): if `x, x'` have exactly `k`
common leading digits (`k = commonPrefix x x'`), the fraction of nested scrambles sending
`(x, x')` to `(y, y')` is `pairKernel k y y'`: the scrambled pair is uniform on the pairs with
exactly `k` common leading digits (on the diagonal if `x = x'`). In particular the joint law of
the scrambled pair depends on `(x, x')` only through `k`. -/
theorem card_scramble_pair (hb : 1 < b) (x x' y y' : Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card : ℝ) =
      Fintype.card (Scramble b D) * pairKernel (commonPrefix x x') y y' := by
  rcases lt_or_eq_of_le (commonPrefix_le x x') with hkD | hkD
  · exact card_scramble_pair_of_lt hb hkD (agree_commonPrefix x x') (ne_at_commonPrefix hkD) y y'
  · have h := agree_commonPrefix x x'
    rw [hkD] at h
    have hxx : x = x' := (agree_iff_eq le_rfl).1 h
    subst hxx
    rw [hkD]
    exact card_scramble_pair_diag hb x y y'

end RQMCMarkov.OwenScrambling
