/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PointSets.ShiftedQMC
import PointSets.ShiftLimitLattice

/-! # The random digital shift in one dimension

Post #2: "If we use an RQMC estimator with a digital net and a digital random shift, this is also
not normally distributed (in one dimension it is equivalent to a randomly-shifted lattice)." The
base-2 random digital shift XORs the binary digits of each point with those of one
`U ~ Uniform[0,1)` (L'Ecuyer 2016; Dick-Pillichshammer 2010, Ch. 4).

**Definition and the dyadic ambiguity.** Points of a base-2 digital net with `2^m` points have at
most `m` binary digits: `y = k/2^m`. Write `a = ⌊2^m u⌋` and `w = fract (2^m u)`, so that the first
`m` digits of `u` are the bits of `a` and its remaining digits are those of `w`. XORing digitwise,
the first `m` digits of `y ⊕ u` are the bits of `k XOR a`, and the remaining digits are those of `u`
(the digits of `y` there are `0`):
`digitalShift m y u = ((⌊2^m y⌋ XOR ⌊2^m u⌋) + fract (2^m u)) / 2^m`
(`floor_two_pow_mul_digitalShift`, `testBit_floor_two_pow_mul_digitalShift`,
`fract_two_pow_mul_digitalShift`). For a general `y` it XORs the first `m` digits and replaces the
later ones by those of `u` (an `m`-digit implementation). The digits of `u` are those of its
terminating expansion (`Nat.floor`). A dyadic rational `u` also has an expansion ending in `1`s,
and `digitalShiftUpper` uses that one (`Nat.ceil - 1`). The two can differ, even by leaving
`[0,1)`: `digitalShift_expansion_ambiguity` gives `1/2 ⊕ 1/2 = 0` against `1`. But they agree
unless `2^m u ∈ ℕ` (`digitalShiftUpper_eq_digitalShift`), a Lebesgue-null set
(`volume_two_pow_mul_eq_natCast`), so `digitalShiftUpper_ae_eq`: the choice is immaterial
almost surely.

**Results.**
* (i) `measurePreserving_digitalShift`: each digitally shifted point is marginally `U[0,1)`
  (a cell permutation `measurePreserving_cellPerm` of the `2^m` dyadic cells), hence
  `integral_qmcEstimate_digitalShiftSeq`: the digitally shifted estimator is unbiased.
* (ii) For `n = 2^m` and the first `2^m` van der Corput points (the grid `{k/2^m}`,
  `image_vanDerCorput_digit`): for EVERY `u ∈ [0,1)` the digitally shifted point set and the
  randomly shifted point set `{fract (φ(i) + u)}` are the same set `{(j + fract (2^m u))/2^m}`
  (`image_digitalShift_eq_image_shiftMod_vanDerCorput`), so the estimators coincide pointwise
  (`qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput`) and have the same law for every `f`
  (`map_qmcEstimate_digitalShift_eq_shiftMod`).
* (iii) `digitalShift_ne_shiftMod_counterexample`: the equivalence is a property of the full net.
  For the three points `{0, 1/8, 1/4}` (`m = 3`) and `f = 1_{[0,1/2)}`, the digitally shifted
  estimator never equals `2/3`, while the randomly shifted one equals `2/3` with probability at
  least `1/8`; the two laws differ.
* (iv) `hasLaw_scaled_error_digitalShift_id`: for `n = 2^m` and `f(x) = x`, the scaled error
  `2^m (μ̂ - 1/2)` of the digitally shifted van der Corput estimator is `U[-1/2, 1/2)` for every
  `m`, via `hasLaw_scaled_error_id` (`ShiftLimit`), so it is not normal
  (`scaled_error_digitalShift_ne_gaussianReal`).

**Correction (to the suggested counterexample).** For the first `3` van der Corput points
`{0, 1/2, 1/4}` the two randomizations are NOT different in law: `map_digitalShift_three_eq`
proves that the digitally and randomly shifted estimators have the same law for every measurable
`f`. Both point sets are the four-cell grid shifted by `fract (4u)/4` with one cell removed, and
the removed cell is uniform in both cases. This holds for every prefix length:
`DigitalShiftPrefix.map_qmcEstimate_digitalShift_prefix_eq` proves the equality in law for the
first `n` van der Corput points whenever `n ≤ 2^m`. A counterexample therefore needs a point set
that is not a van der Corput prefix, as in (iii).
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter

/-- The base-2 random digital shift of a point `y` with `m` binary digits by `u`:
`((⌊2^m y⌋ XOR ⌊2^m u⌋) + fract (2^m u)) / 2^m` (terminating expansion of `u`). -/
noncomputable def digitalShift (m : ℕ) (y u : ℝ) : ℝ :=
  (((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m

/-- The digital shift computed with the non-terminating expansion of `u` (the one ending in `1`s
when `u` is dyadic): digits `⌈2^m u⌉ - 1` and tail `2^m u - (⌈2^m u⌉ - 1) ∈ (0,1]`. -/
noncomputable def digitalShiftUpper (m : ℕ) (y u : ℝ) : ℝ :=
  (((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ (⌈(2 : ℝ) ^ m * u⌉₊ - 1) : ℕ) : ℝ) +
    ((2 : ℝ) ^ m * u - ((⌈(2 : ℝ) ^ m * u⌉₊ - 1 : ℕ) : ℝ))) / 2 ^ m

/-- The digitally shifted point sequence `i ↦ x i ⊕ u`. -/
noncomputable def digitalShiftSeq (m : ℕ) (x : ℕ → ℝ) (u : ℝ) : ℕ → ℝ :=
  fun i => digitalShift m (x i) u

/-- The dyadic cell `[a/2^m, (a+1)/2^m)`. -/
def dyadicCell (m a : ℕ) : Set ℝ := Set.Ico ((a : ℝ) / 2 ^ m) (((a : ℝ) + 1) / 2 ^ m)

/-- The cell permutation `u ↦ (σ ⌊2^m u⌋ + fract (2^m u))/2^m`: moves the dyadic cell `a` onto the
cell `σ a` by a translation. -/
noncomputable def cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) : ℝ :=
  (((σ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m

/-- `⌊x⌋₊ + fract x = x` for `x ≥ 0`. -/
theorem natFloor_add_fract {x : ℝ} (hx : 0 ≤ x) : (⌊x⌋₊ : ℝ) + Int.fract x = x := by
  rw [natCast_floor_eq_intCast_floor hx, Int.floor_add_fract]

/-- For `y ∈ [0,1)`, `⌊2^m y⌋ < 2^m`. -/
theorem floor_two_pow_mul_lt (m : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    ⌊(2 : ℝ) ^ m * y⌋₊ < 2 ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_lt (mul_nonneg hpos.le hy.1), Nat.cast_pow, Nat.cast_ofNat]
  exact mul_lt_of_lt_one_right hpos hy.2

/-- XOR with a fixed number is injective. -/
theorem xor_left_cancel' (k a b : ℕ) (h : k ^^^ a = k ^^^ b) : a = b := by
  have := congrArg (fun c => k ^^^ c) h
  rwa [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.zero_xor] at this

/-- `2^m (y ⊕ u) = (⌊2^m y⌋ XOR ⌊2^m u⌋) + fract (2^m u)`. -/
theorem two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) :
    (2 : ℝ) ^ m * digitalShift m y u =
      ((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u) := by
  unfold digitalShift
  field_simp

/-- **The first `m` digits are XORed**: `⌊2^m (y ⊕ u)⌋ = ⌊2^m y⌋ XOR ⌊2^m u⌋`. -/
theorem floor_two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) :
    ⌊(2 : ℝ) ^ m * digitalShift m y u⌋₊ = ⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ := by
  rw [two_pow_mul_digitalShift, add_comm, Nat.floor_add_natCast (Int.fract_nonneg _),
    Nat.floor_eq_zero.mpr (Int.fract_lt_one _), zero_add]

/-- Digitwise: bit `j` of `⌊2^m (y ⊕ u)⌋` (binary digit `m - j` of `y ⊕ u`) is the XOR of the
corresponding bits of `y` and `u`. -/
theorem testBit_floor_two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) (j : ℕ) :
    Nat.testBit ⌊(2 : ℝ) ^ m * digitalShift m y u⌋₊ j =
      (Nat.testBit ⌊(2 : ℝ) ^ m * y⌋₊ j ^^ Nat.testBit ⌊(2 : ℝ) ^ m * u⌋₊ j) := by
  rw [floor_two_pow_mul_digitalShift, Nat.testBit_xor]

/-- **The later digits are those of `u`**: `fract (2^m (y ⊕ u)) = fract (2^m u)`. -/
theorem fract_two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) :
    Int.fract ((2 : ℝ) ^ m * digitalShift m y u) = Int.fract ((2 : ℝ) ^ m * u) := by
  rw [two_pow_mul_digitalShift, Int.fract_natCast_add, Int.fract_fract]

/-- The digital shift of a point of `[0,1)` by `u ∈ [0,1)` lies in `[0,1)`. -/
theorem digitalShift_mem_Ico (m : ℕ) {y u : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Ico (0 : ℝ) 1) : digitalShift m y u ∈ Set.Ico (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hK : ⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ < 2 ^ m :=
    Nat.xor_lt_two_pow (floor_two_pow_mul_lt m hy) (floor_two_pow_mul_lt m hu)
  have hK' : ((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + 1 ≤ 2 ^ m := by
    exact_mod_cast hK
  have hw := Int.fract_lt_one ((2 : ℝ) ^ m * u)
  have hw0 := Int.fract_nonneg ((2 : ℝ) ^ m * u)
  unfold digitalShift
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hpos]
  linarith

/-- **The two expansions agree off the dyadic grid**: if `2^m u ∉ ℕ`, the terminating and the
non-terminating expansions of `u` give the same digital shift. -/
theorem digitalShiftUpper_eq_digitalShift (m : ℕ) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hnd : ∀ k : ℕ, (2 : ℝ) ^ m * u ≠ k) : digitalShiftUpper m y u = digitalShift m y u := by
  have hx : 0 ≤ (2 : ℝ) ^ m * u := mul_nonneg (pow_nonneg zero_le_two m) hu
  have hlt : ((⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) < (2 : ℝ) ^ m * u :=
    lt_of_le_of_ne (Nat.floor_le hx) fun h => hnd _ h.symm
  have hceil : ⌈(2 : ℝ) ^ m * u⌉₊ = ⌊(2 : ℝ) ^ m * u⌋₊ + 1 := by
    rw [Nat.ceil_eq_iff (by omega : ⌊(2 : ℝ) ^ m * u⌋₊ + 1 ≠ 0), Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one]
    exact ⟨hlt, (Nat.lt_floor_add_one _).le⟩
  have htail : (2 : ℝ) ^ m * u - ((⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) = Int.fract ((2 : ℝ) ^ m * u) := by
    have := natFloor_add_fract hx
    linarith
  unfold digitalShiftUpper digitalShift
  rw [hceil, Nat.add_sub_cancel, htail]

/-- The dyadic grid of level `m` is Lebesgue-null: `volume {u : 2^m u ∈ ℕ} = 0`. -/
theorem volume_two_pow_mul_eq_natCast (m : ℕ) :
    volume {u : ℝ | ∃ k : ℕ, (2 : ℝ) ^ m * u = k} = 0 := by
  refine measure_mono_null ?_ ((Set.countable_range fun k : ℕ => (k : ℝ) / 2 ^ m).measure_zero
    volume)
  rintro u ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change (k : ℝ) / 2 ^ m = u
  rw [div_eq_iff (pow_pos two_pos m).ne', ← hk, mul_comm]

/-- **The expansion ambiguity is immaterial almost surely**: under `U ~ U[0,1)` the two digital
shifts agree almost surely. -/
theorem digitalShiftUpper_ae_eq (m : ℕ) (y : ℝ) :
    digitalShiftUpper m y =ᵐ[uniformIco] digitalShift m y := by
  have h0 := measure_eq_zero_iff_ae_notMem.mp (volume_two_pow_mul_eq_natCast m)
  filter_upwards [ae_restrict_mem measurableSet_Ico, ae_restrict_of_ae h0] with u hu hnd
  exact digitalShiftUpper_eq_digitalShift m y hu.1 fun k hk => hnd ⟨k, hk⟩

/-- **The ambiguity is real on the null set**: `1/2 ⊕ 1/2` is `0` with the terminating
expansion `u = 0.1000…` but `1` with `u = 0.0111…` (`m = 1`). -/
theorem digitalShift_expansion_ambiguity :
    digitalShift 1 (1 / 2) (1 / 2) = 0 ∧ digitalShiftUpper 1 (1 / 2) (1 / 2) = 1 := by
  unfold digitalShift digitalShiftUpper
  norm_num

/-- Membership in a dyadic cell is read off the floor: `v ∈ cell a ↔ ⌊2^m v⌋ = a` (`v ≥ 0`). -/
theorem mem_dyadicCell_iff (m a : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v ∈ dyadicCell m a ↔ ⌊(2 : ℝ) ^ m * v⌋₊ = a :=
  mem_dyadic_iff_floor m a hv

/-- Points of dyadic cells are nonnegative. -/
theorem nonneg_of_mem_dyadicCell {m a : ℕ} {v : ℝ} (h : v ∈ dyadicCell m a) : 0 ≤ v :=
  le_trans (by positivity) h.1

/-- On the cell `a`, `fract (2^m v) = 2^m v - a`. -/
theorem fract_eq_of_mem_dyadicCell {m a : ℕ} {v : ℝ} (h : v ∈ dyadicCell m a) :
    Int.fract ((2 : ℝ) ^ m * v) = (2 : ℝ) ^ m * v - a := by
  have hv := nonneg_of_mem_dyadicCell h
  have hfl := (mem_dyadicCell_iff m a hv).mp h
  have := natFloor_add_fract (mul_nonneg (pow_nonneg zero_le_two m) hv)
  rw [hfl] at this
  linarith

/-- Translating by `(b - a)/2^m` moves the cell `a` onto the cell `b`. -/
theorem mem_dyadicCell_add_iff (m a b : ℕ) (v : ℝ) :
    v + ((b : ℝ) - a) / 2 ^ m ∈ dyadicCell m b ↔ v ∈ dyadicCell m a := by
  unfold dyadicCell
  rw [Set.mem_Ico, Set.mem_Ico, sub_div, add_div, add_div]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- `X ∩ [0,1)` is the disjoint union of the `2^m` sets `cell a ∩ X`. -/
theorem inter_Ico_eq_biUnion_dyadicCell (m : ℕ) (X : Set ℝ) :
    X ∩ Set.Ico 0 1 = ⋃ a ∈ Finset.range (2 ^ m), dyadicCell m a ∩ X := by
  ext u
  rw [Set.mem_iUnion₂]
  constructor
  · rintro ⟨hX, hu⟩
    exact ⟨⌊(2 : ℝ) ^ m * u⌋₊, Finset.mem_range.mpr (floor_two_pow_mul_lt m hu),
      (mem_dyadicCell_iff m _ hu.1).mpr rfl, hX⟩
  · rintro ⟨a, ha, hcell, hX⟩
    have ha' : a + 1 ≤ 2 ^ m := Finset.mem_range.mp ha
    have ha'' : (a : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast ha'
    exact ⟨hX, nonneg_of_mem_dyadicCell hcell,
      lt_of_lt_of_le hcell.2 ((div_le_one (pow_pos two_pos m)).mpr ha'')⟩

/-- The sets `cell a ∩ X`, `a < 2^m`, are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicCell_inter (m : ℕ) (X : Set ℝ) :
    (↑(Finset.range (2 ^ m)) : Set ℕ).PairwiseDisjoint fun a => dyadicCell m a ∩ X := by
  intro a _ b _ hab
  change Disjoint (dyadicCell m a ∩ X) (dyadicCell m b ∩ X)
  refine Set.disjoint_left.mpr fun u hu hu' => hab ?_
  have hv := nonneg_of_mem_dyadicCell hu.1
  rw [← (mem_dyadicCell_iff m a hv).mp hu.1, ← (mem_dyadicCell_iff m b hv).mp hu'.1]

/-- A cell permutation is measurable. -/
theorem measurable_cellPerm (m : ℕ) (σ : ℕ → ℕ) : Measurable (cellPerm m σ) := by
  refine Measurable.div_const (Measurable.add ?_ ?_) _
  · exact (measurable_from_nat (f := fun a : ℕ => ((σ a : ℕ) : ℝ))).comp
      (Nat.measurable_floor.comp (measurable_const_mul _))
  · exact measurable_fract.comp (measurable_const_mul _)

/-- On the cell `a`, the cell permutation is the translation by `(σ a - a)/2^m`. -/
theorem cellPerm_of_mem {m a : ℕ} (σ : ℕ → ℕ) {v : ℝ} (h : v ∈ dyadicCell m a) :
    cellPerm m σ v = v + ((σ a : ℝ) - a) / 2 ^ m := by
  have hfl := (mem_dyadicCell_iff m a (nonneg_of_mem_dyadicCell h)).mp h
  unfold cellPerm
  rw [hfl, fract_eq_of_mem_dyadicCell h]
  field_simp
  ring

/-- **A permutation of the dyadic cells preserves `U[0,1)`.** If `σ` maps `{0, …, 2^m - 1}`
injectively into itself, then `u ↦ (σ ⌊2^m u⌋ + fract (2^m u))/2^m` preserves the uniform law. -/
theorem measurePreserving_cellPerm (m : ℕ) {σ : ℕ → ℕ} (hmaps : ∀ a < 2 ^ m, σ a < 2 ^ m)
    (hinj : ∀ a < 2 ^ m, ∀ b < 2 ^ m, σ a = σ b → a = b) :
    MeasurePreserving (cellPerm m σ) uniformIco uniformIco := by
  have hT := measurable_cellPerm m σ
  refine ⟨hT, ?_⟩
  ext S hS
  rw [Measure.map_apply hT hS, Measure.restrict_apply (hT hS), Measure.restrict_apply hS,
    inter_Ico_eq_biUnion_dyadicCell m, inter_Ico_eq_biUnion_dyadicCell m,
    measure_biUnion_finset (pairwiseDisjoint_dyadicCell_inter m _)
      (fun a _ => measurableSet_Ico.inter (hT hS)),
    measure_biUnion_finset (pairwiseDisjoint_dyadicCell_inter m _)
      (fun a _ => measurableSet_Ico.inter hS)]
  have hstep : ∀ a ∈ Finset.range (2 ^ m), volume (dyadicCell m a ∩ cellPerm m σ ⁻¹' S) =
      volume (dyadicCell m (σ a) ∩ S) := by
    intro a _
    have hset : dyadicCell m a ∩ cellPerm m σ ⁻¹' S =
        (fun v => v + ((σ a : ℝ) - a) / 2 ^ m) ⁻¹' (dyadicCell m (σ a) ∩ S) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      rw [mem_dyadicCell_add_iff]
      constructor
      · rintro ⟨hc, hTS⟩
        exact ⟨hc, by rwa [← cellPerm_of_mem σ hc]⟩
      · rintro ⟨hc, hS'⟩
        exact ⟨hc, by rwa [cellPerm_of_mem σ hc]⟩
    rw [hset, measure_preimage_add_right]
  rw [Finset.sum_congr rfl hstep]
  have hmapsTo : Set.MapsTo σ (Finset.range (2 ^ m) : Set ℕ) (Finset.range (2 ^ m) : Set ℕ) :=
    fun a ha => Finset.mem_coe.mpr (Finset.mem_range.mpr
      (hmaps a (Finset.mem_range.mp (Finset.mem_coe.mp ha))))
  have hinjOn : Set.InjOn σ (Finset.range (2 ^ m) : Set ℕ) := fun a ha b hb hab =>
    hinj a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
      (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
  exact Finset.sum_nbij σ (fun a ha => hmapsTo ha) hinjOn
    (Finset.surjOn_of_injOn_of_card_le σ hmapsTo hinjOn (le_refl _)) (fun _ _ => rfl)

/-- **(i) Marginal uniformity.** For `y ∈ [0,1)`, the digitally shifted point `y ⊕ U`,
`U ~ U[0,1)`, is `U[0,1)`. -/
theorem measurePreserving_digitalShift (m : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    MeasurePreserving (digitalShift m y) uniformIco uniformIco :=
  measurePreserving_cellPerm m (σ := fun a => ⌊(2 : ℝ) ^ m * y⌋₊ ^^^ a)
    (fun _ ha => Nat.xor_lt_two_pow (floor_two_pow_mul_lt m hy) ha)
    (fun a _ b _ hab => xor_left_cancel' _ a b hab)

/-- **(i) Unbiasedness of the digitally shifted estimator**: for points in `[0,1)`, `n ≥ 1` and
`f` integrable on `[0,1]`, `E[(1/n) ∑ f(xᵢ ⊕ U)] = ∫₀¹ f`. -/
theorem integral_qmcEstimate_digitalShiftSeq {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (m : ℕ) {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    ∫ u, qmcEstimate f (digitalShiftSeq m x u) n ∂uniformIco = ∫ t in (0 : ℝ)..1, f t := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfU : Integrable f uniformIco := by
    rw [uniformIco_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf
  have hcomp : ∀ i ∈ Finset.range n,
      ∫ u, f (digitalShiftSeq m x u i) ∂uniformIco = ∫ y, f y ∂uniformIco := by
    intro i hi
    have hmp := measurePreserving_digitalShift m (hx i (Finset.mem_range.mp hi))
    change ∫ u, f (digitalShift m (x i) u) ∂uniformIco = _
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hfU.1),
      hmp.map_eq]
  have hint : ∀ i ∈ Finset.range n, Integrable (fun u => f (digitalShiftSeq m x u i)) uniformIco :=
    fun i hi => (measurePreserving_digitalShift m
      (hx i (Finset.mem_range.mp hi))).integrable_comp_of_integrable hfU
  unfold qmcEstimate
  rw [integral_div, integral_finsetSum _ hint, Finset.sum_congr rfl hcomp, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hpos.ne',
    intervalIntegral.integral_of_le zero_le_one, uniformIco_eq_restrict_Ioc]

/-- Reindexing a sum over `{0, …, N-1}` by an injective self-map. -/
theorem sum_range_comp_of_injOn {β : Type*} [AddCommMonoid β] {N : ℕ} {σ : ℕ → ℕ}
    (hmaps : ∀ a < N, σ a < N) (hinj : ∀ a < N, ∀ b < N, σ a = σ b → a = b) (g : ℕ → β) :
    ∑ i ∈ Finset.range N, g (σ i) = ∑ j ∈ Finset.range N, g j := by
  have hmapsTo : Set.MapsTo σ (Finset.range N : Set ℕ) (Finset.range N : Set ℕ) := fun a ha =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (hmaps a (Finset.mem_range.mp (Finset.mem_coe.mp ha))))
  have hinjOn : Set.InjOn σ (Finset.range N : Set ℕ) := fun a ha b hb hab =>
    hinj a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
      (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
  exact Finset.sum_nbij σ (fun a ha => hmapsTo ha) hinjOn
    (Finset.surjOn_of_injOn_of_card_le σ hmapsTo hinjOn (le_refl _)) (fun _ _ => rfl)

/-- The image of `{0, …, N-1}` under `g ∘ σ` is its image under `g`, for an injective self-map
`σ`. -/
theorem image_range_comp_of_injOn {N : ℕ} {σ : ℕ → ℕ} (hmaps : ∀ a < N, σ a < N)
    (hinj : ∀ a < N, ∀ b < N, σ a = σ b → a = b) (g : ℕ → ℝ) :
    (Finset.range N).image (fun i => g (σ i)) = (Finset.range N).image g := by
  have himg : (Finset.range N).image σ = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_range.mpr (hmaps a (Finset.mem_range.mp ha))
    · rw [Finset.card_image_of_injOn fun a ha b hb hab =>
        hinj a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
          (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab]
  have := Finset.image_image (s := Finset.range N) (f := σ) (g := g)
  rw [himg] at this
  exact this.symm

/-- The first `2^m` van der Corput points are multiples of `2^{-m}`. -/
theorem exists_two_pow_mul_vanDerCorput_eq (m : ℕ) :
    ∀ i < 2 ^ m, ∃ k : ℕ, (2 : ℝ) ^ m * vanDerCorput i = k := by
  induction m with
  | zero =>
    intro i hi
    rw [pow_zero] at hi
    have : i = 0 := by omega
    subst this
    exact ⟨0, by rw [vanDerCorput.eq_1, mul_zero, Nat.cast_zero]⟩
  | succ m ih =>
    intro i hi
    obtain ⟨k, hk⟩ := ih (i / 2) (by rw [pow_succ] at hi; omega)
    refine ⟨i % 2 * 2 ^ m + k, ?_⟩
    rw [vanDerCorput_eq i, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ← hk]
    ring

/-- `2^m φ(i) = ⌊2^m φ(i)⌋` for `i < 2^m`. -/
theorem two_pow_mul_vanDerCorput_eq_floor {m i : ℕ} (hi : i < 2 ^ m) :
    (2 : ℝ) ^ m * vanDerCorput i = ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ := by
  obtain ⟨k, hk⟩ := exists_two_pow_mul_vanDerCorput_eq m i hi
  rw [hk, Nat.floor_natCast]

/-- The digit index `i ↦ ⌊2^m φ(i)⌋` is injective on `{0, …, 2^m - 1}`. -/
theorem vanDerCorput_digit_inj {m i j : ℕ} (hi : i < 2 ^ m) (hj : j < 2 ^ m)
    (h : ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput j⌋₊) : i = j :=
  floor_vanDerCorput_injOn m 0 (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) (by
      change ⌊(2 : ℝ) ^ m * vanDerCorput (0 + i)⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput (0 + j)⌋₊
      rw [zero_add, zero_add]
      exact h)

/-- **The first `2^m` van der Corput points form the grid `{k/2^m : k < 2^m}`.** -/
theorem image_vanDerCorput_digit (m : ℕ) :
    (Finset.range (2 ^ m)).image vanDerCorput =
      (Finset.range (2 ^ m)).image fun k : ℕ => (k : ℝ) / 2 ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have h := image_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊)
    (fun i _ => floor_two_pow_mul_vanDerCorput_lt m i)
    (fun a ha b hb hab => vanDerCorput_digit_inj ha hb hab) (fun k : ℕ => (k : ℝ) / 2 ^ m)
  rw [← h]
  refine Finset.image_congr fun i hi => ?_
  rw [← two_pow_mul_vanDerCorput_eq_floor (Finset.mem_range.mp (Finset.mem_coe.mp hi)),
    mul_div_cancel_left₀ _ hpos.ne']

/-- The random shift of a van der Corput point `φ(i)`, `i < 2^m`, in cell coordinates:
`fract (φ(i) + u) = (((⌊2^m φ(i)⌋ + ⌊2^m u⌋) mod 2^m) + fract (2^m u))/2^m`. -/
theorem fract_vanDerCorput_add {m i : ℕ} (hi : i < 2 ^ m) {u : ℝ} (hu : 0 ≤ u) :
    Int.fract (vanDerCorput i + u) =
      ((((⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m : ℕ) : ℝ) +
        Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hφ := two_pow_mul_vanDerCorput_eq_floor hi
  have hu' := natFloor_add_fract (mul_nonneg hpos.le hu)
  set d := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ with hd
  set a := ⌊(2 : ℝ) ^ m * u⌋₊ with ha
  set w := Int.fract ((2 : ℝ) ^ m * u) with hw
  have hdivR : (((d + a) / 2 ^ m : ℕ) : ℝ) * 2 ^ m + (((d + a) % 2 ^ m : ℕ) : ℝ) = d + a := by
    exact_mod_cast Nat.div_add_mod' (d + a) (2 ^ m)
  have hr : ((((d + a) % 2 ^ m : ℕ)) : ℝ) + 1 ≤ 2 ^ m := by
    exact_mod_cast Nat.mod_lt (d + a) (pow_pos two_pos m)
  have hw0 : 0 ≤ w := Int.fract_nonneg _
  have hw1 : w < 1 := Int.fract_lt_one _
  have e1 : vanDerCorput i = (d : ℝ) / 2 ^ m := by
    rw [eq_div_iff hpos.ne', mul_comm]
    exact hφ
  have e2 : u = ((a : ℝ) + w) / 2 ^ m := by
    rw [eq_div_iff hpos.ne', mul_comm, hu']
  rw [Int.fract_eq_iff]
  refine ⟨by positivity, ?_, (((d + a) / 2 ^ m : ℕ) : ℤ), ?_⟩
  · rw [div_lt_one hpos]
    linarith
  · rw [Int.cast_natCast, e1, e2, ← add_div, ← sub_div, div_eq_iff hpos.ne']
    linarith

/-- The digitally shifted first `2^m` van der Corput points, summed: for `u ∈ [0,1)`,
`∑_{i<2^m} f(φ(i) ⊕ u) = ∑_{j<2^m} f((j + fract (2^m u))/2^m)`. -/
theorem sum_digitalShift_vanDerCorput (f : ℝ → ℝ) (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    ∑ i ∈ Finset.range (2 ^ m), f (digitalShiftSeq m vanDerCorput u i) =
      ∑ j ∈ Finset.range (2 ^ m), f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) :=
  sum_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊)
    (fun i _ => Nat.xor_lt_two_pow (floor_two_pow_mul_vanDerCorput_lt m i)
      (floor_two_pow_mul_lt m hu))
    (fun a ha b hb hab => vanDerCorput_digit_inj ha hb (by
      rw [Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊, Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊] at hab
      exact xor_left_cancel' _ _ _ hab))
    (fun j => f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m))

/-- The randomly shifted first `2^m` van der Corput points, summed: for `u ∈ [0,1)`,
`∑_{i<2^m} f(fract (φ(i) + u)) = ∑_{j<2^m} f((j + fract (2^m u))/2^m)`. -/
theorem sum_shiftMod_vanDerCorput (f : ℝ → ℝ) (m : ℕ) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    ∑ i ∈ Finset.range (2 ^ m), f (shiftMod vanDerCorput u i) =
      ∑ j ∈ Finset.range (2 ^ m), f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) := by
  change ∑ i ∈ Finset.range (2 ^ m), f (Int.fract (vanDerCorput i + u)) = _
  rw [Finset.sum_congr rfl fun i hi => congrArg f
    (fract_vanDerCorput_add (Finset.mem_range.mp hi) hu.1)]
  exact sum_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => (⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)
    (fun i _ => Nat.mod_lt _ (pow_pos two_pos m))
    (fun a ha b hb hab => by
      have h1 := Nat.ModEq.add_right_cancel' _ hab
      unfold Nat.ModEq at h1
      rw [Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m a),
        Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m b)] at h1
      exact vanDerCorput_digit_inj ha hb h1)
    (fun j => f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m))

/-- **(ii) Same point set.** For `n = 2^m` and every `u ∈ [0,1)`, the digitally shifted first
`2^m` van der Corput points and the randomly shifted ones form the same set
`{(j + fract (2^m u))/2^m : j < 2^m}`. -/
theorem image_digitalShift_eq_image_shiftMod_vanDerCorput (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    (Finset.range (2 ^ m)).image (digitalShiftSeq m vanDerCorput u) =
      (Finset.range (2 ^ m)).image (shiftMod vanDerCorput u) := by
  have hD := image_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊)
    (fun i _ => Nat.xor_lt_two_pow (floor_two_pow_mul_vanDerCorput_lt m i)
      (floor_two_pow_mul_lt m hu))
    (fun a ha b hb hab => vanDerCorput_digit_inj ha hb (by
      rw [Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊, Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊] at hab
      exact xor_left_cancel' _ _ _ hab))
    (fun j => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m)
  have hR := image_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => (⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)
    (fun i _ => Nat.mod_lt _ (pow_pos two_pos m))
    (fun a ha b hb hab => by
      have h1 := Nat.ModEq.add_right_cancel' _ hab
      unfold Nat.ModEq at h1
      rw [Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m a),
        Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m b)] at h1
      exact vanDerCorput_digit_inj ha hb h1)
    (fun j => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m)
  have hR' : (Finset.range (2 ^ m)).image (shiftMod vanDerCorput u) =
      (Finset.range (2 ^ m)).image (fun i => (fun j : ℕ => ((j : ℝ) +
        Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m)
          ((⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)) :=
    Finset.image_congr fun i hi =>
      fract_vanDerCorput_add (Finset.mem_range.mp (Finset.mem_coe.mp hi)) hu.1
  rw [hR', hR]
  exact hD

/-- **(ii) Same estimator.** For `n = 2^m`, every `f` and every `u ∈ [0,1)`, the digitally
shifted and the randomly shifted van der Corput estimators are equal. -/
theorem qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput (f : ℝ → ℝ) (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    qmcEstimate f (digitalShiftSeq m vanDerCorput u) (2 ^ m) =
      qmcEstimate f (shiftMod vanDerCorput u) (2 ^ m) := by
  unfold qmcEstimate
  rw [sum_digitalShift_vanDerCorput f m hu, sum_shiftMod_vanDerCorput f m hu]

/-- **(ii) Same law.** For `n = 2^m` and every `f`, the digitally shifted and the randomly
shifted van der Corput estimators have the same law under `U ~ U[0,1)` (post #2: "in one
dimension it is equivalent to a randomly-shifted lattice"). -/
theorem map_qmcEstimate_digitalShift_eq_shiftMod (f : ℝ → ℝ) (m : ℕ) :
    uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq m vanDerCorput u) (2 ^ m)) =
      uniformIco.map (fun u => qmcEstimate f (shiftMod vanDerCorput u) (2 ^ m)) := by
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  exact qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput f m hu

/-- **(iv) The scaled error for `f(x) = x` is uniform.** For `n = 2^m`, the digitally shifted
van der Corput estimator satisfies `2^m (μ̂ - 1/2) ~ U[-1/2, 1/2)` for every `m` (through
`hasLaw_scaled_error_id`). -/
theorem hasLaw_scaled_error_digitalShift_id (m : ℕ) :
    HasLaw (fun u => (2 : ℝ) ^ m *
      (qmcEstimate (fun t => t) (digitalShiftSeq m vanDerCorput u) (2 ^ m) - 1 / 2))
      (volume.restrict (Set.Ico (-(1 / 2) : ℝ) (1 / 2))) uniformIco := by
  have hn : (2 : ℕ) ^ m ≠ 0 := pow_ne_zero m two_ne_zero
  have h := hasLaw_scaled_error_id hn
    (hasLaw_fract_natCast_mul hn (HasLaw.id (μ := uniformIco)))
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  unfold qmcEstimate sampleMean
  rw [sum_digitalShift_vanDerCorput (fun t => t) m hu,
    Fin.sum_univ_eq_sum_range (fun k => id (stratumMap (2 ^ m) k
      (Int.fract (((2 ^ m : ℕ) : ℝ) * id u)))) (2 ^ m)]
  simp only [id, stratumMap, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_eq_inv_mul]

/-- **(iv) Not normal.** The law of the scaled error of the digitally shifted van der Corput
estimator for `f(x) = x` is not a non-degenerate Gaussian, for any `m`. -/
theorem scaled_error_digitalShift_ne_gaussianReal (m : ℕ) (μ₀ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    uniformIco.map (fun u => (2 : ℝ) ^ m *
      (qmcEstimate (fun t => t) (digitalShiftSeq m vanDerCorput u) (2 ^ m) - 1 / 2)) ≠
      gaussianReal μ₀ v := by
  rw [(hasLaw_scaled_error_digitalShift_id m).map_eq]
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := 1 / 2) ?_ μ₀ hv
  rw [Measure.restrict_apply measurableSet_Ioi]
  convert measure_empty (μ := (volume : Measure ℝ))
  exact Set.eq_empty_of_forall_notMem fun t ht => absurd ht.2.2 (not_lt.mpr ht.1.le)

/-- A grid point `(j + w)/8` with `w ∈ [0,1)` lies below `1/2` iff `j < 4`. -/
theorem cell_lt_half_iff (j : ℕ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ((j : ℝ) + w) / 2 ^ 3 < 1 / 2 ↔ j < 4 := by
  constructor
  · intro h
    have h' : (j : ℝ) < 4 := by
      have := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 3)).mp h
      norm_num at this
      linarith
    exact_mod_cast h'
  · intro h
    have h' : (j : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ h
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 3)]
    norm_num
    linarith

/-- **(iii) Counterexample: for a point set that is not a net the two randomizations differ.**
For the three points `{0, 1/8, 1/4}` (`m = 3`) and `f = 1_{(-∞,1/2)}`, the digitally shifted
estimator is never `2/3` on `[0,1)`, while the randomly shifted estimator is `2/3` with
probability at least `1/8`; hence the two estimator laws differ. -/
theorem digitalShift_ne_shiftMod_counterexample :
    uniformIco {u | qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (digitalShiftSeq 3 (fun i : ℕ => (i : ℝ) / 8) u) 3 = 2 / 3} = 0 ∧
      0 < uniformIco {u | qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (shiftMod (fun i : ℕ => (i : ℝ) / 8) u) 3 = 2 / 3} ∧
      uniformIco.map (fun u => qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (digitalShiftSeq 3 (fun i : ℕ => (i : ℝ) / 8) u) 3) ≠
      uniformIco.map (fun u => qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (shiftMod (fun i : ℕ => (i : ℝ) / 8) u) 3) := by
  set f : ℝ → ℝ := (Set.Iio (1 / 2 : ℝ)).indicator 1 with hfdef
  set x : ℕ → ℝ := fun i : ℕ => (i : ℝ) / 8 with hxdef
  have hQ : ∀ y : ℕ → ℝ, qmcEstimate f y 3 = (f (y 0) + f (y 1) + f (y 2)) / 3 := by
    intro y
    unfold qmcEstimate
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hfval : ∀ t : ℝ, f t = if t < 1 / 2 then 1 else 0 := by
    intro t
    by_cases ht : t < 1 / 2
    · rw [hfdef, Set.indicator_of_mem (show t ∈ Set.Iio (1 / 2 : ℝ) from ht), Pi.one_apply]
      simp only [ht, ↓reduceIte]
    · rw [hfdef, Set.indicator_of_notMem (show t ∉ Set.Iio (1 / 2 : ℝ) from ht)]
      simp only [ht, ↓reduceIte]
  -- the digital side: all three points lie on the same side of `1/2`
  have hD : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      qmcEstimate f (digitalShiftSeq 3 x u) 3 = 0 ∨
        qmcEstimate f (digitalShiftSeq 3 x u) 3 = 1 := by
    intro u hu
    have ha := floor_two_pow_mul_lt 3 hu
    have hw0 := Int.fract_nonneg ((2 : ℝ) ^ 3 * u)
    have hw1 := Int.fract_lt_one ((2 : ℝ) ^ 3 * u)
    have hpt : ∀ i < 3, f (digitalShiftSeq 3 x u i) =
        if ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4 then 1 else 0 := by
      intro i hi
      have hfl : ⌊(2 : ℝ) ^ 3 * x i⌋₊ = i := by
        rw [hxdef, show (2 : ℝ) ^ 3 * ((i : ℝ) / 8) = i by ring, Nat.floor_natCast]
      have hbit : (i ^^^ ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4) ↔ ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4 := by
        have key : ∀ a < 8, ∀ i < 3, ((i ^^^ a < 4) ↔ a < 4) := by decide
        exact key _ (lt_of_lt_of_eq ha (by norm_num)) i hi
      change f (digitalShift 3 (x i) u) = _
      unfold digitalShift
      rw [hfval, hfl]
      by_cases hlt : ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4
      · have hc := (cell_lt_half_iff _ hw0 hw1).mpr (hbit.mpr hlt)
        simp only [hlt, hc, ↓reduceIte]
      · have hc : ¬ (((i ^^^ ⌊(2 : ℝ) ^ 3 * u⌋₊ : ℕ) : ℝ) +
            Int.fract ((2 : ℝ) ^ 3 * u)) / 2 ^ 3 < 1 / 2 :=
          fun h => hlt (hbit.mp ((cell_lt_half_iff _ hw0 hw1).mp h))
        simp only [hlt, hc, ↓reduceIte]
    rw [hQ, hpt 0 (by norm_num), hpt 1 (by norm_num), hpt 2 (by norm_num)]
    by_cases hlt : ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4
    · right
      simp only [hlt, ↓reduceIte]
      norm_num
    · left
      simp only [hlt, ↓reduceIte]
      norm_num
  -- the random-shift side on `[1/4, 3/8)`
  have hR : ∀ u ∈ Set.Ico (1 / 4 : ℝ) (3 / 8), qmcEstimate f (shiftMod x u) 3 = 2 / 3 := by
    intro u hu
    have h1 := hu.1
    have h2 := hu.2
    have e0 : shiftMod x u 0 = u := by
      change Int.fract ((((0 : ℕ) : ℝ)) / 8 + u) = u
      rw [show (((0 : ℕ) : ℝ)) / 8 + u = u by norm_num]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have e1 : shiftMod x u 1 = 1 / 8 + u := by
      change Int.fract ((((1 : ℕ) : ℝ)) / 8 + u) = 1 / 8 + u
      rw [show (((1 : ℕ) : ℝ)) / 8 + u = 1 / 8 + u by norm_num]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have e2 : shiftMod x u 2 = 1 / 4 + u := by
      change Int.fract ((((2 : ℕ) : ℝ)) / 8 + u) = 1 / 4 + u
      rw [show (((2 : ℕ) : ℝ)) / 8 + u = 1 / 4 + u by norm_num]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have c0 : u < 1 / 2 := by linarith
    have c1 : 1 / 8 + u < 1 / 2 := by linarith
    have c2 : ¬ (1 / 4 + u < 1 / 2) := by intro h; linarith
    rw [hQ, e0, e1, e2, hfval, hfval, hfval]
    simp only [c0, c1, c2, ↓reduceIte]
    norm_num
  have hDzero : uniformIco {u | qmcEstimate f (digitalShiftSeq 3 x u) 3 = 2 / 3} = 0 := by
    rw [Measure.restrict_apply' measurableSet_Ico]
    convert measure_empty (μ := (volume : Measure ℝ))
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have hu1 : qmcEstimate f (digitalShiftSeq 3 x u) 3 = 2 / 3 := hu.1
    rcases hD u hu.2 with h | h
    · rw [h] at hu1
      norm_num at hu1
    · rw [h] at hu1
      norm_num at hu1
  have hRpos : 0 < uniformIco {u | qmcEstimate f (shiftMod x u) 3 = 2 / 3} := by
    have hsub : Set.Ico (1 / 4 : ℝ) (3 / 8) ⊆
        {u | qmcEstimate f (shiftMod x u) 3 = 2 / 3} ∩ Set.Ico 0 1 := fun u hu =>
      ⟨hR u hu, by linarith [hu.1], by linarith [hu.2]⟩
    rw [Measure.restrict_apply' measurableSet_Ico]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  refine ⟨hDzero, hRpos, fun hmap => ?_⟩
  have hfm : Measurable f := measurable_one.indicator measurableSet_Iio
  have hmD : Measurable fun u => qmcEstimate f (digitalShiftSeq 3 x u) 3 := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i hi => ?_) _
    have hxi : x i ∈ Set.Ico (0 : ℝ) 1 := by
      have := Finset.mem_range.mp hi
      have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ this
      exact ⟨by positivity, by rw [hxdef]; change (i : ℝ) / 8 < 1; linarith⟩
    exact hfm.comp (measurePreserving_digitalShift 3 hxi).measurable
  have hmR : Measurable fun u => qmcEstimate f (shiftMod x u) 3 := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact hfm.comp (measurable_fract.comp (measurable_const_add _))
  have h1 := congrArg (fun μ : Measure ℝ => μ {2 / 3}) hmap
  rw [Measure.map_apply hmD (measurableSet_singleton _),
    Measure.map_apply hmR (measurableSet_singleton _)] at h1
  have h2 : (fun u => qmcEstimate f (digitalShiftSeq 3 x u) 3) ⁻¹' {2 / 3} =
      {u | qmcEstimate f (digitalShiftSeq 3 x u) 3 = 2 / 3} := rfl
  have h3 : (fun u => qmcEstimate f (shiftMod x u) 3) ⁻¹' {2 / 3} =
      {u | qmcEstimate f (shiftMod x u) 3 = 2 / 3} := rfl
  rw [h2, h3, hDzero] at h1
  exact (ne_of_lt hRpos) h1

/-- `2^m` times a cell permutation: `σ ⌊2^m u⌋ + fract (2^m u)`. -/
theorem two_pow_mul_cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) :
    (2 : ℝ) ^ m * cellPerm m σ u =
      ((σ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u) := by
  unfold cellPerm
  field_simp

/-- The cell permutation sends the cell `a` to the cell `σ a`: `⌊2^m T(u)⌋ = σ ⌊2^m u⌋`. -/
theorem floor_two_pow_mul_cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) :
    ⌊(2 : ℝ) ^ m * cellPerm m σ u⌋₊ = σ ⌊(2 : ℝ) ^ m * u⌋₊ := by
  rw [two_pow_mul_cellPerm, add_comm, Nat.floor_add_natCast (Int.fract_nonneg _),
    Nat.floor_eq_zero.mpr (Int.fract_lt_one _), zero_add]

/-- The cell permutation keeps the position inside the cell: `fract (2^m T(u)) = fract (2^m u)`. -/
theorem fract_two_pow_mul_cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) :
    Int.fract ((2 : ℝ) ^ m * cellPerm m σ u) = Int.fract ((2 : ℝ) ^ m * u) := by
  rw [two_pow_mul_cellPerm, Int.fract_natCast_add, Int.fract_fract]

/-- The combinatorial core of `map_digitalShift_three_eq`: the cells `{0, 2, 1} XOR a` and
`{0, 2, 1} + τ(a) mod 4`, `τ(a) = (4 - a) mod 4`, are the same multiset for every `a < 4`. -/
theorem sum_xor_eq_sum_add_three (g : ℕ → ℝ) {a : ℕ} (ha : a < 4) :
    g (0 ^^^ a) + g (2 ^^^ a) + g (1 ^^^ a) =
      g ((0 + (4 - a) % 4) % 4) + g ((2 + (4 - a) % 4) % 4) + g ((1 + (4 - a) % 4) % 4) := by
  interval_cases a <;> norm_num <;> ring

/-- **Correction: for the first three van der Corput points the two randomizations agree in
law.** For `{φ(0), φ(1), φ(2)} = {0, 1/2, 1/4}` (digital shift with `m = 2`), the digitally
shifted and the randomly shifted estimators have the same law for every measurable `f`: the
digitally shifted set at `u` is the randomly shifted set at `ψ(u)`, where `ψ` permutes the four
dyadic cells by `τ(a) = (4 - a) mod 4` and so preserves `U[0,1)`. -/
theorem map_digitalShift_three_eq {f : ℝ → ℝ} (hf : Measurable f) :
    uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq 2 vanDerCorput u) 3) =
      uniformIco.map (fun u => qmcEstimate f (shiftMod vanDerCorput u) 3) := by
  have hτmaps : ∀ a < 2 ^ 2, (4 - a) % 4 < 2 ^ 2 := by decide
  have hτinj : ∀ a < 2 ^ 2, ∀ b < 2 ^ 2, (4 - a) % 4 = (4 - b) % 4 → a = b := by decide
  have hψ := measurePreserving_cellPerm 2 (σ := fun a => (4 - a) % 4) hτmaps hτinj
  have hmR : Measurable fun v => qmcEstimate f (shiftMod vanDerCorput v) 3 := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact hf.comp (measurable_fract.comp (measurable_const_add _))
  have h0 : vanDerCorput 0 = 0 := vanDerCorput.eq_1
  obtain ⟨h1, h2, -⟩ := vanDerCorput_one_two_three
  have hd0 : ⌊(2 : ℝ) ^ 2 * vanDerCorput 0⌋₊ = 0 := by rw [h0, mul_zero, Nat.floor_zero]
  have hd1 : ⌊(2 : ℝ) ^ 2 * vanDerCorput 1⌋₊ = 2 := by
    rw [h1, show (2 : ℝ) ^ 2 * (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  have hd2 : ⌊(2 : ℝ) ^ 2 * vanDerCorput 2⌋₊ = 1 := by
    rw [h2, show (2 : ℝ) ^ 2 * (1 / 4) = ((1 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  have hQ : ∀ y : ℕ → ℝ, qmcEstimate f y 3 = (f (y 0) + f (y 1) + f (y 2)) / 3 := by
    intro y
    unfold qmcEstimate
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hpt : ∀ u ∈ Set.Ico (0 : ℝ) 1, qmcEstimate f (digitalShiftSeq 2 vanDerCorput u) 3 =
      qmcEstimate f (shiftMod vanDerCorput (cellPerm 2 (fun a => (4 - a) % 4) u)) 3 := by
    intro u hu
    have hv : 0 ≤ cellPerm 2 (fun a => (4 - a) % 4) u := by
      unfold cellPerm
      have := Int.fract_nonneg ((2 : ℝ) ^ 2 * u)
      positivity
    have hR : ∀ i < 2 ^ 2, shiftMod vanDerCorput (cellPerm 2 (fun a => (4 - a) % 4) u) i =
        ((((⌊(2 : ℝ) ^ 2 * vanDerCorput i⌋₊ + (4 - ⌊(2 : ℝ) ^ 2 * u⌋₊) % 4) % 2 ^ 2 : ℕ) : ℝ) +
          Int.fract ((2 : ℝ) ^ 2 * u)) / 2 ^ 2 := by
      intro i hi
      change Int.fract (vanDerCorput i + cellPerm 2 (fun a => (4 - a) % 4) u) = _
      rw [fract_vanDerCorput_add hi hv, floor_two_pow_mul_cellPerm, fract_two_pow_mul_cellPerm]
    have ha : ⌊(2 : ℝ) ^ 2 * u⌋₊ < 4 := floor_two_pow_mul_lt 2 hu
    have key := sum_xor_eq_sum_add_three
      (fun j : ℕ => f (((j : ℝ) + Int.fract ((2 : ℝ) ^ 2 * u)) / 2 ^ 2)) ha
    rw [hQ, hQ, hR 0 (by norm_num), hR 1 (by norm_num), hR 2 (by norm_num), hd0, hd1, hd2]
    change (f (digitalShift 2 (vanDerCorput 0) u) + f (digitalShift 2 (vanDerCorput 1) u) +
      f (digitalShift 2 (vanDerCorput 2) u)) / 3 = _
    unfold digitalShift
    rw [hd0, hd1, hd2]
    norm_num at key ⊢
    rw [key]
  calc uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq 2 vanDerCorput u) 3)
      = uniformIco.map ((fun v => qmcEstimate f (shiftMod vanDerCorput v) 3) ∘
          cellPerm 2 (fun a => (4 - a) % 4)) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
        exact hpt u hu
    _ = _ := by rw [← Measure.map_map hmR hψ.measurable, hψ.map_eq]

end RQMCMarkov.PointSets
