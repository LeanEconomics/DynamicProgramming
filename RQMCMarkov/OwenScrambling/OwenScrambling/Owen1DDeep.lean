/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.Owen1DCLT

/-!
# The genuine nested scramble to any depth is stratified sampling (post #2)

`Owen1DScramble` scrambles the `(0,m,1)`-net `{k/bᵐ}` at depth `m` (the precision of the net) and
takes the digits below as independent uniform remainders. This module removes that modelling
step. The net point `k/bᵐ` has `M = m + d` base-`b` digits `netWord m d k`: the digits of `k`
followed by `d` zeros (`digitEquiv_netWord_val`: its cell at depth `M` is `k bᵈ`). Owen's nested
scramble to depth `M` permutes each of its `M` digits by the permutation of the node given by the
digits before it, with ALL node permutations independent and uniform (a uniform tree
`T : OwenTree b (m + d)`), and adds an independent uniform remainder below digit `M`:
`deepNet T r k = (cell of owenWord T (netWord m d k) + r k)/b^M`.

## Main results

* `digitEquiv_add_val`: the cell of a word of length `m + d` is
  `(cell of its first m digits) · bᵈ + (cell of its last d digits)`.
* `wordFirst_owenWord`, `wordLast_owenWord_netWord`, `deepNet_eq`: the scrambled point of `k` is
  `(σ_T k + (τ_T k + r k)/bᵈ)/bᵐ`, where `σ_T = deepCell T` is the depth-`m` scramble of the top
  of the tree and `τ_T k = deepTail T k` collects the scrambled zero digits of point `k`.
* `card_filter_deepKey_eq`, `card_filter_deepKey_mul`: for a uniform tree the scrambled zero digits
  `τ_T` are uniform on `(Fin bᵈ)^(bᵐ)` and independent of `σ_T` (equal fibre counts, via the
  involution `swapTail`): distinct net points sit below distinct nodes at every level `≥ m`.
* `sum_measure_preimage_digitShift`: adding independent uniform digits to independent uniform
  remainders gives independent uniform remainders, `Σ_τ ν(H_τ⁻¹ A) = (bᵈ)^n ν(A)`.
* `hasLaw_deepRemainder`, `hasLaw_deepNetSorted` (**the gap closed**): for every depth
  `M = m + d ≥ m`, the genuine scramble of the net, relabelled by depth-`m` cell, has exactly the
  law `stratifiedLaw (bᵐ)`: one independent uniform point in each cell. The law does not depend on
  `M`, so it is also the law of the scramble of all infinitely many digits in the projective sense
  (every finite-depth truncation, with uniform remainder, has it); the depth-`m` model of
  `Owen1DScramble` (`d = 0`) is exact.
* `sampleMean_deepNet`, `variance_deepNet_eq_stratVar`: the genuine scrambled-net estimator is the
  stratified estimator of the relabelled remainders, with variance `stratVar (bᵐ) f`.
* `tendstoInDistribution_deepNet`: `tendstoInDistribution_owenNet` for the genuine scramble, with
  any depths `M_m = m + D m` (e.g. `M_m → ∞`): `(μ̂ₙ − μ)/σₙ ⇒ N(0,1)`.

Unlike the CLT of `Owen1DCLT`, these results use the uniformity of the tree: it is what makes the
scrambled zero digits uniform.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {b : ℕ}

/-- The first `m` digits of a word of length `m + d`. -/
def wordFirst {m d : ℕ} (w : DigitWord b (m + d)) : DigitWord b m :=
  fun l ↦ w (Fin.castAdd d l)

/-- The last `d` digits of a word of length `m + d`. -/
def wordLast {m d : ℕ} (w : DigitWord b (m + d)) : DigitWord b d :=
  fun i ↦ w (Fin.natAdd m i)

/-- **Cells split by digits**: the cell of a word of length `m + d` is
`(cell of the first m digits) · bᵈ + (cell of the last d digits)`. -/
theorem digitEquiv_add_val (m d : ℕ) (w : DigitWord b (m + d)) :
    (digitEquiv b (m + d) w : ℕ) =
      (digitEquiv b m (wordFirst w) : ℕ) * b ^ d + digitEquiv b d (wordLast w) := by
  rw [digitEquiv_apply_val, digitEquiv_apply_val, digitEquiv_apply_val, Fin.sum_univ_add,
    Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl (fun l _ ↦ ?_)
    change (w (Fin.castAdd d l) : ℕ) * b ^ (m + d - ((l : ℕ) + 1)) =
      (w (Fin.castAdd d l) : ℕ) * b ^ (m - ((l : ℕ) + 1)) * b ^ d
    rw [mul_assoc, ← pow_add]
    congr 2
    have := l.isLt
    omega
  · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    change (w (Fin.natAdd m i) : ℕ) * b ^ (m + d - ((m + (i : ℕ)) + 1)) =
      (w (Fin.natAdd m i) : ℕ) * b ^ (d - ((i : ℕ) + 1))
    congr 2
    omega

/-- The first `j` digits of the net point `k/bᵐ`: the digits of `k`, then zeros. -/
def netPrefix [NeZero b] (m j : ℕ) (k : Fin (b ^ m)) : Fin j → Fin b :=
  fun l ↦ if h : (l : ℕ) < m then (digitEquiv b m).symm k ⟨l, h⟩ else 0

/-- The `m + d` digits of the net point `k/bᵐ`. -/
def netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) : DigitWord b (m + d) :=
  netPrefix m (m + d) k

/-- The first `m` digits of the net point are those of `k`. -/
theorem wordFirst_netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) :
    wordFirst (netWord m d k) = (digitEquiv b m).symm k := by
  funext l
  simp only [wordFirst, netWord, netPrefix, Fin.val_castAdd, l.isLt, ↓reduceDIte, Fin.eta]

/-- The last `d` digits of the net point are zero. -/
theorem wordLast_netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) :
    wordLast (netWord m d k) = fun _ ↦ 0 := by
  funext i
  have h : ¬ ((Fin.natAdd m i : Fin (m + d)) : ℕ) < m := by
    rw [Fin.val_natAdd]
    omega
  simp only [wordLast, netWord, netPrefix, h, ↓reduceDIte]

/-- **The net point `k/bᵐ` at depth `m + d`** is the cell `k bᵈ`. -/
theorem digitEquiv_netWord_val [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) :
    (digitEquiv b (m + d) (netWord m d k) : ℕ) = (k : ℕ) * b ^ d := by
  rw [digitEquiv_add_val, wordFirst_netWord, wordLast_netWord, Equiv.apply_symm_apply,
    digitEquiv_apply_val]
  have h0 : ∑ j : Fin d, (((fun _ ↦ (0 : Fin b)) j : Fin b) : ℕ) * b ^ (d - (j + 1)) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by
      change ((0 : Fin b) : ℕ) * _ = 0
      rw [Fin.val_zero, zero_mul]
  rw [h0, add_zero]

/-- The prefix of the net word at level `m + i` is `netPrefix m (m + i) k`. -/
theorem wordPrefix_netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) (i : Fin d) :
    wordPrefix (netWord m d k) (Fin.natAdd m i) = netPrefix m (m + i) k :=
  rfl

/-- The top of a depth-`(m + d)` tree: its permutations at levels `< m`. -/
def topTree {m d : ℕ} (t : OwenTree b (m + d)) : OwenTree b m :=
  fun j p ↦ t (Fin.castAdd d j) p

/-- The first `m` scrambled digits only use the top of the tree. -/
theorem wordFirst_owenWord {m d : ℕ} (t : OwenTree b (m + d)) (w : DigitWord b (m + d)) :
    wordFirst (owenWord t w) = owenWord (topTree t) (wordFirst w) :=
  rfl

/-- The scrambled zero digits of the net point `k`: digit `i` is the image of `0` under the
permutation of the node `netPrefix m (m + i) k`. -/
def tailWord [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (k : Fin (b ^ m)) : DigitWord b d :=
  fun i ↦ t (Fin.natAdd m i) (netPrefix m (m + i) k) 0

/-- The last `d` scrambled digits of the net point are `tailWord`. -/
theorem wordLast_owenWord_netWord [NeZero b] {m d : ℕ} (t : OwenTree b (m + d))
    (k : Fin (b ^ m)) : wordLast (owenWord t (netWord m d k)) = tailWord t k := by
  funext i
  have h := congrFun (wordLast_netWord (b := b) m d k) i
  change t (Fin.natAdd m i) (wordPrefix (netWord m d k) (Fin.natAdd m i))
    (netWord m d k (Fin.natAdd m i)) = _
  change netWord m d k (Fin.natAdd m i) = 0 at h
  rw [h, wordPrefix_netWord]
  rfl

/-- The depth-`m` cell permutation `σ_T` of the deep scramble (its top tree's `owenCell`). -/
noncomputable def deepCell {m d : ℕ} (t : OwenTree b (m + d)) : Equiv.Perm (Fin (b ^ m)) :=
  owenCell (topTree t)

/-- The scrambled zero digits of point `k` as a cell of depth `d`. -/
def deepTail [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (k : Fin (b ^ m)) : Fin (b ^ d) :=
  digitEquiv b d (tailWord t k)

/-- **The genuine scramble to depth `M = m + d` of the net**, with uniform remainders `r` below
digit `M`: `(cell of owenWord t (netWord m d k) + r k)/b^M`. -/
noncomputable def deepNet [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun k ↦ stratumMap (b ^ (m + d)) (digitEquiv b (m + d) (owenWord t (netWord m d k))) (r k)

/-- **The deep scrambled point**: `(σ_T k + (τ_T k + r k)/bᵈ)/bᵐ`. -/
theorem deepNet_eq [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ)
    (k : Fin (b ^ m)) :
    deepNet t r k =
      stratumMap (b ^ m) (deepCell t k) (stratumMap (b ^ d) (deepTail t k) (r k)) := by
  have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne b)
  have hv := digitEquiv_add_val m d (owenWord t (netWord m d k))
  rw [wordFirst_owenWord, wordFirst_netWord, wordLast_owenWord_netWord] at hv
  have hc : (deepCell t k : ℕ) = (digitEquiv b m (owenWord (topTree t) ((digitEquiv b m).symm k))
      : ℕ) := rfl
  simp only [deepNet, stratumMap]
  rw [hv, hc]
  unfold deepTail
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- The remainder of the point in depth-`m` cell `j`: `(τ_T(σ_T⁻¹ j) + r(σ_T⁻¹ j))/bᵈ`. -/
noncomputable def deepRemainder [NeZero b] {m d : ℕ} (t : OwenTree b (m + d))
    (r : Fin (b ^ m) → ℝ) : Fin (b ^ m) → ℝ :=
  fun j ↦ stratumMap (b ^ d) (deepTail t ((deepCell t).symm j)) (r ((deepCell t).symm j))

/-- The deep scrambled net relabelled by depth-`m` cell. -/
noncomputable def deepNetSorted [NeZero b] {m d : ℕ} (t : OwenTree b (m + d))
    (r : Fin (b ^ m) → ℝ) : Fin (b ^ m) → ℝ :=
  fun j ↦ deepNet t r ((deepCell t).symm j)

/-- Relabelled by cell, the deep net is the stratified point set of `deepRemainder`. -/
theorem deepNetSorted_eq [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ) :
    deepNetSorted t r = stratPoints (b ^ m) (deepRemainder t r) := by
  funext j
  simp only [deepNetSorted, deepNet_eq, Equiv.apply_symm_apply]
  rfl

/-- The scrambled-net estimator is the stratified estimator of the relabelled remainders. -/
theorem sampleMean_deepNet [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ)
    (f : ℝ → ℝ) :
    sampleMean (b ^ m) f (deepNet t r) =
      sampleMean (b ^ m) f (stratPoints (b ^ m) (deepRemainder t r)) := by
  rw [← deepNetSorted_eq]
  unfold sampleMean
  congr 1
  exact (Equiv.sum_comp (deepCell t).symm (fun k ↦ f (deepNet t r k))).symm

/-- The cell of depth `m` read off the first `m` digits of a node at level `j ≥ m`. -/
def kOfPrefix {m j : ℕ} (h : m ≤ j) (p : Fin j → Fin b) : Fin (b ^ m) :=
  digitEquiv b m (fun l ↦ p ⟨l, lt_of_lt_of_le l.2 h⟩)

/-- `kOfPrefix` recovers `k` from the net prefix. -/
theorem kOfPrefix_netPrefix [NeZero b] {m j : ℕ} (h : m ≤ j) (k : Fin (b ^ m)) :
    kOfPrefix h (netPrefix m j k) = k := by
  have hf : (fun l : Fin m ↦ netPrefix m j k ⟨l, lt_of_lt_of_le l.2 h⟩) =
      (digitEquiv b m).symm k := by
    funext l
    simp only [netPrefix, l.isLt, ↓reduceDIte, Fin.eta]
  unfold kOfPrefix
  rw [hf, Equiv.apply_symm_apply]

/-- The tail level `j − m` of a level `j ≥ m`. -/
def tailLevel {m d : ℕ} (j : Fin (m + d)) (h : m ≤ (j : ℕ)) : Fin d :=
  ⟨j - m, by have := j.isLt; omega⟩

/-- `tailLevel (m + i) = i`. -/
theorem tailLevel_natAdd {m d : ℕ} (i : Fin d) (h : m ≤ ((Fin.natAdd m i : Fin (m + d)) : ℕ)) :
    tailLevel (Fin.natAdd m i) h = i := by
  refine Fin.ext ?_
  change ((Fin.natAdd m i : Fin (m + d)) : ℕ) - m = i
  rw [Fin.val_natAdd]
  omega

/-- The tree that composes the permutations at the net nodes `netPrefix m (m + i) k` with the
transpositions `(v k i  v' k i)`, and leaves all other nodes alone. -/
def swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) : OwenTree b (m + d) :=
  fun j p ↦ if h : m ≤ (j : ℕ) then
    (if p = netPrefix m j (kOfPrefix h p) then
      Equiv.swap (v (kOfPrefix h p) (tailLevel j h)) (v' (kOfPrefix h p) (tailLevel j h)) * t j p
    else t j p)
  else t j p

/-- `swapTail` is an involution. -/
theorem swapTail_swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) : swapTail v v' (swapTail v v' t) = t := by
  funext j p
  unfold swapTail
  split_ifs with h hp <;> first | exact Equiv.swap_mul_self_mul _ _ _ | rfl

/-- `swapTail` leaves the top of the tree unchanged. -/
theorem topTree_swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) : topTree (swapTail v v' t) = topTree t := by
  funext j p
  have h : ¬ m ≤ ((Fin.castAdd d j : Fin (m + d)) : ℕ) := by
    rw [Fin.val_castAdd]
    have := j.isLt
    omega
  simp only [topTree, swapTail, h, ↓reduceDIte]

/-- `swapTail` swaps the scrambled zero digits. -/
theorem tailWord_swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) (k : Fin (b ^ m)) (i : Fin d) :
    tailWord (swapTail v v' t) k i = Equiv.swap (v k i) (v' k i) (tailWord t k i) := by
  have h : m ≤ ((Fin.natAdd m i : Fin (m + d)) : ℕ) := by
    rw [Fin.val_natAdd]
    omega
  have hk : kOfPrefix h (netPrefix m (m + i) k) = k := kOfPrefix_netPrefix h k
  have hi := tailLevel_natAdd i h
  change swapTail v v' t (Fin.natAdd m i) (netPrefix m (m + i) k) 0 = _
  unfold swapTail
  split_ifs with h1
  · rw [hk, hi]
    rfl
  · exact absurd (by rw [hk]; rfl) h1

/-- The key of a deep tree: its depth-`m` cell permutation and its scrambled zero digits. -/
noncomputable def deepKey [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) :
    Equiv.Perm (Fin (b ^ m)) × (Fin (b ^ m) → Fin (b ^ d)) :=
  (deepCell t, deepTail t)

/-- `swapTail` maps the trees with key `(s, τ)` onto those with key `(s, τ')`. -/
theorem deepKey_swapTail_eq_iff [NeZero b] {m d : ℕ} (s : Equiv.Perm (Fin (b ^ m)))
    (τ τ' : Fin (b ^ m) → Fin (b ^ d)) (t : OwenTree b (m + d)) :
    deepKey (swapTail (fun k ↦ (digitEquiv b d).symm (τ k)) (fun k ↦ (digitEquiv b d).symm (τ' k))
      t) = (s, τ') ↔ deepKey t = (s, τ) := by
  have hcell : deepCell (swapTail (fun k ↦ (digitEquiv b d).symm (τ k))
      (fun k ↦ (digitEquiv b d).symm (τ' k)) t) = deepCell t := by
    unfold deepCell
    rw [topTree_swapTail]
  have htail : ∀ k, deepTail (swapTail (fun k ↦ (digitEquiv b d).symm (τ k))
      (fun k ↦ (digitEquiv b d).symm (τ' k)) t) k = τ' k ↔ deepTail t k = τ k := by
    intro k
    unfold deepTail
    rw [← Equiv.eq_symm_apply, ← Equiv.eq_symm_apply]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      rw [tailWord_swapTail, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hi
      exact hi
    · intro h
      funext i
      rw [tailWord_swapTail, h, Equiv.swap_apply_left]
  unfold deepKey
  rw [hcell, Prod.mk.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun k ↦ (htail k).1 (congrFun h2 k)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun k ↦ (htail k).2 (congrFun h2 k)⟩

/-- **The scrambled zero digits are uniform and independent of `σ_T`**: the number of trees with
key `(s, τ)` does not depend on `τ`. -/
theorem card_filter_deepKey_eq [NeZero b] {m d : ℕ} (s : Equiv.Perm (Fin (b ^ m)))
    (τ τ' : Fin (b ^ m) → Fin (b ^ d)) :
    (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ)).card =
      (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ')).card := by
  set v : Fin (b ^ m) → DigitWord b d := fun k ↦ (digitEquiv b d).symm (τ k)
  set v' : Fin (b ^ m) → DigitWord b d := fun k ↦ (digitEquiv b d).symm (τ' k)
  refine Finset.card_nbij' (swapTail v v') (swapTail v v') (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    (fun t _ ↦ swapTail_swapTail v v' t) (fun t _ ↦ swapTail_swapTail v v' t)
  · rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, (deepKey_swapTail_eq_iff s τ τ' t).2 ht.2⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← deepKey_swapTail_eq_iff s τ τ' (swapTail v v' _), swapTail_swapTail]
    exact ht.2

/-- Summing the fibre counts over all keys counts all trees. -/
theorem sum_card_filter_deepKey [NeZero b] (m d : ℕ) :
    ∑ s : Equiv.Perm (Fin (b ^ m)), ∑ τ : Fin (b ^ m) → Fin (b ^ d),
      (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ)).card =
        Fintype.card (OwenTree b (m + d)) := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := deepKey)
    (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Fintype.sum_prod_type]

/-- On the uniform cube, the coordinatewise maps `H_τ r k = (τ k + r k)/B`. -/
noncomputable def digitShift (B : ℕ) {n : ℕ} (τ : Fin n → Fin B) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun k ↦ stratumMap B (τ k) (r k)

/-- `digitShift` is measurable. -/
theorem measurable_digitShift (B : ℕ) {n : ℕ} (τ : Fin n → Fin B) :
    Measurable (digitShift B τ) :=
  Measurable.of_eval fun k ↦ (measurable_stratumMap B _).comp (measurable_pi_apply k)

/-- **Uniform digits plus uniform remainders are uniform remainders**: averaging the laws of
`(τ k + U k)/B` over all `τ : Fin n → Fin B` gives `U[0,1)ⁿ` again. -/
theorem sum_measure_preimage_digitShift {B n : ℕ} (hB : B ≠ 0) {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) :
    ∑ τ : Fin n → Fin B, uniformCube n (digitShift B τ ⁻¹' A) =
      ((B : ℝ≥0∞) ^ n) * uniformCube n A := by
  have := isProbabilityMeasure_uniformIco
  have hB0 : (B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hB
  have hBt : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top B
  have hBn0 : (B : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n hB0
  have hBnt : (B : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top hBt
  set μ' : Measure (Fin n → ℝ) := (((B : ℝ≥0∞) ^ n)⁻¹) •
    ∑ τ : Fin n → Fin B, (uniformCube n).map (digitShift B τ) with hμ'
  have h1 : ∀ S : Set ℝ, MeasurableSet S →
      ∑ c : Fin B, uniformIco (stratumMap B c ⁻¹' S) = (B : ℝ≥0∞) * uniformIco S := by
    intro S hS
    have h := congrArg (fun μ : Measure ℝ ↦ μ S) (sum_map_stratumMap hB)
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun c _ ↦ ?_)
    rw [Measure.map_apply (measurable_stratumMap B c) hS]
  have heq : uniformCube n = μ' := by
    refine Measure.pi_eq (fun s hs ↦ ?_)
    have hpre : ∀ τ : Fin n → Fin B, digitShift B τ ⁻¹' univ.pi s =
        univ.pi fun k ↦ stratumMap B (τ k) ⁻¹' s k := by
      intro τ
      ext r
      simp only [mem_preimage, mem_univ_pi, digitShift]
    rw [hμ', Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun τ _ ↦ by
      rw [Measure.map_apply (measurable_digitShift B τ) (MeasurableSet.univ_pi hs), hpre τ,
        Measure.pi_pi])]
    rw [← Fintype.prod_sum (fun k (c : Fin B) ↦ uniformIco (stratumMap B c ⁻¹' s k)),
      Finset.prod_congr rfl (fun k _ ↦ h1 (s k) (hs k)), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
      ENNReal.inv_mul_cancel hBn0 hBnt, one_mul]
  have hval := congrArg (fun μ : Measure (Fin n → ℝ) ↦ μ A) heq
  simp only [hμ', Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul] at hval
  rw [hval, ← mul_assoc, ENNReal.mul_inv_cancel hBn0 hBnt, one_mul]
  refine Finset.sum_congr rfl (fun τ _ ↦ ?_)
  rw [Measure.map_apply (measurable_digitShift B τ) hA]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The gap closed: the genuine nested scramble to any depth `M = m + d ≥ m`.** For a uniform
tree `T : OwenTree b (m + d)` independent of the remainders `R ~ U[0,1)^(bᵐ)` below digit `M`,
the remainders of the scrambled net points within their depth-`m` cells, relabelled by cell,
are again `U[0,1)^(bᵐ)`. -/
theorem hasLaw_deepRemainder [NeZero b] {m d : ℕ} {mT : MeasurableSpace (OwenTree b (m + d))}
    [DiscreteMeasurableSpace (OwenTree b (m + d))] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b (m + d)} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T)
    (hR : Measurable R) (hTlaw : HasLaw T (uniformOn univ) P)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ deepRemainder (T ω) (R ω)) (uniformCube (b ^ m)) P := by
  have := isProbabilityMeasure_uniformIco
  have hBd0 : b ^ d ≠ 0 := pow_ne_zero d (NeZero.ne b)
  have hcomp : ∀ t : OwenTree b (m + d), deepRemainder t =
      (fun (r : Fin (b ^ m) → ℝ) j ↦ r ((deepCell t).symm j)) ∘ digitShift (b ^ d) (deepTail t) :=
    fun t ↦ rfl
  have hGm : ∀ t : OwenTree b (m + d), Measurable (deepRemainder t) := fun t ↦ by
    rw [hcomp t]
    exact (measurePreserving_comp_perm (deepCell t)).measurable.comp
      (measurable_digitShift (b ^ d) _)
  have hm := measurable_comp_of_countable hT hR hGm
  refine ⟨hm.aemeasurable, ?_⟩
  ext A hA
  set ν := uniformCube (b ^ m) with hν
  set c : ℝ≥0∞ := (Fintype.card (OwenTree b (m + d)) : ℝ≥0∞)⁻¹ with hc
  set F : Equiv.Perm (Fin (b ^ m)) × (Fin (b ^ m) → Fin (b ^ d)) → ℝ≥0∞ := fun p ↦
    ν (digitShift (b ^ d) p.2 ⁻¹' ((fun (r : Fin (b ^ m) → ℝ) j ↦ r (p.1.symm j)) ⁻¹' A)) with hF
  have hterm : ∀ t, P.map R (deepRemainder t ⁻¹' A) = F (deepKey t) := fun t ↦ by
    rw [hRlaw.map_eq, hcomp t]
    rfl
  -- group the trees by key
  set a : Equiv.Perm (Fin (b ^ m)) → ℕ := fun s ↦
    (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, fun _ ↦ 0)).card with ha
  have hfib : ∀ s τ, (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ)).card =
      a s := fun s τ ↦ card_filter_deepKey_eq s τ _
  have hpres : ∀ s : Equiv.Perm (Fin (b ^ m)),
      ν ((fun (r : Fin (b ^ m) → ℝ) j ↦ r (s.symm j)) ⁻¹' A) = ν A := fun s ↦ by
    rw [← Measure.map_apply (measurePreserving_comp_perm s).measurable hA,
      (measurePreserving_comp_perm s).map_eq]
  have hsumτ : ∀ s : Equiv.Perm (Fin (b ^ m)), ∑ τ : Fin (b ^ m) → Fin (b ^ d), F (s, τ) =
      ((Nat.cast (b ^ d) : ℝ≥0∞) ^ (b ^ m)) * ν A := fun s ↦ by
    rw [hF]
    simp only
    rw [sum_measure_preimage_digitShift hBd0
      ((measurePreserving_comp_perm s).measurable hA), hpres s]
  have htotN : ∑ s : Equiv.Perm (Fin (b ^ m)), a s * (b ^ d) ^ (b ^ m) =
      Fintype.card (OwenTree b (m + d)) := by
    rw [← sum_card_filter_deepKey (b := b) m d]
    refine Finset.sum_congr rfl (fun s _ ↦ ?_)
    rw [Finset.sum_congr rfl (fun τ _ ↦ hfib s τ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul, mul_comm]
  have htot : ∑ s : Equiv.Perm (Fin (b ^ m)),
      (a s : ℝ≥0∞) * ((Nat.cast (b ^ d) : ℝ≥0∞)) ^ (b ^ m) = Fintype.card (OwenTree b (m + d)) := by
    rw [← htotN, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun s _ ↦ ?_)
    rw [Nat.cast_mul, Nat.cast_pow (α := ℝ≥0∞) (b ^ d) (b ^ m)]
  rw [Measure.map_apply hm hA, measure_preimage_comp_of_indepFun hT hR hind hGm hA,
    Finset.sum_congr rfl (fun t _ ↦ by
      rw [measure_preimage_singleton_of_uniform hT hTlaw t, hterm t]),
    ← Finset.sum_fiberwise Finset.univ (fun t : OwenTree b (m + d) ↦ deepKey t)
      (fun t ↦ c * F (deepKey t))]
  have hinner : ∀ p : Equiv.Perm (Fin (b ^ m)) × (Fin (b ^ m) → Fin (b ^ d)),
      ∑ t ∈ Finset.univ with deepKey t = p, c * F (deepKey t) = (a p.1 : ℝ≥0∞) * (c * F p) := by
    intro p
    rw [Finset.sum_congr rfl (fun t ht ↦ by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      nsmul_eq_mul, ← hfib p.1 p.2]
  rw [Finset.sum_congr rfl (fun p _ ↦ hinner p), Fintype.sum_prod_type]
  have hs : ∀ s : Equiv.Perm (Fin (b ^ m)),
      ∑ τ : Fin (b ^ m) → Fin (b ^ d), (a s : ℝ≥0∞) * (c * F (s, τ)) =
        ((a s : ℝ≥0∞) * (Nat.cast (b ^ d) : ℝ≥0∞) ^ (b ^ m)) * (c * ν A) := fun s ↦ by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsumτ s]
    ring
  rw [Finset.sum_congr rfl (fun s _ ↦ hs s), ← Finset.sum_mul, htot, hc, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-- **The genuine scrambled net is independent stratified sampling, at every depth**: relabelled
by depth-`m` cell, the scramble to depth `m + d` of `{k/bᵐ}` has the law `stratifiedLaw (bᵐ)`,
for every `d` (so for the full infinite-digit scramble in the projective sense). -/
theorem hasLaw_deepNetSorted [NeZero b] {m d : ℕ} {mT : MeasurableSpace (OwenTree b (m + d))}
    [DiscreteMeasurableSpace (OwenTree b (m + d))] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b (m + d)} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T)
    (hR : Measurable R) (hTlaw : HasLaw T (uniformOn univ) P)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ deepNetSorted (T ω) (R ω)) (stratifiedLaw (b ^ m)) P := by
  have hV := hasLaw_deepRemainder hT hR hTlaw hRlaw hind
  have hfun : (fun ω ↦ deepNetSorted (T ω) (R ω)) =
      stratPoints (b ^ m) ∘ fun ω ↦ deepRemainder (T ω) (R ω) := by
    funext ω
    rw [Function.comp_apply, deepNetSorted_eq]
  rw [hfun]
  refine ⟨(measurable_stratPoints _).comp_aemeasurable hV.aemeasurable, ?_⟩
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_stratPoints _).aemeasurable
    hV.aemeasurable, hV.map_eq]
  rfl

/-- **The variance of the genuine scrambled net** is `stratVar (bᵐ) f`, at every depth. -/
theorem variance_deepNet_eq_stratVar [NeZero b] {m d : ℕ}
    {mT : MeasurableSpace (OwenTree b (m + d))} [DiscreteMeasurableSpace (OwenTree b (m + d))]
    {f : ℝ → ℝ} (hfm : Measurable f) (hc : ContinuousOn f (Icc 0 1)) {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → OwenTree b (m + d)} {R : Ω → Fin (b ^ m) → ℝ}
    (hT : Measurable T) (hR : Measurable R) (hTlaw : HasLaw T (uniformOn univ) P)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    Var[fun ω ↦ sampleMean (b ^ m) f (deepNet (T ω) (R ω)); P] = stratVar (b ^ m) f := by
  have := isProbabilityMeasure_uniformIco
  have hV := hasLaw_deepRemainder hT hR hTlaw hRlaw hind
  have hfun : (fun ω ↦ sampleMean (b ^ m) f (deepNet (T ω) (R ω))) =
      (fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v)) ∘
        fun ω ↦ deepRemainder (T ω) (R ω) := by
    funext ω
    rw [Function.comp_apply, sampleMean_deepNet]
  have hg : Measurable fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v) :=
    (measurable_sampleMean hfm).comp (measurable_stratPoints _)
  rw [hfun, ← variance_map (hV.map_eq ▸ hg.aemeasurable) hV.aemeasurable, hV.map_eq]
  exact variance_stratified_eq (pow_ne_zero m (NeZero.ne b)) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) (memLp_uniformIco_of_continuousOn hfm hc 2)

/-- **Post #2's CLT for the genuine Owen scramble** (one dimension): let `b ≥ 2` and, for each
`m`, let `T m` be a uniform tree of any depth `m + D m ≥ m` (e.g. `D m → ∞`), independent of the
remainders `R m ~ U[0,1)^(bᵐ)` below its last digit. For measurable `f`, `C¹` and non-constant on
`[0,1]`, the scrambled-net estimator `μ̂ₙ = (1/n) Σₖ f(deepNet (T m) (R m) k)`, `n = bᵐ`,
satisfies `(μ̂ₙ − ∫₀¹ f)/σₙ ⇒ N(0,1)`, with `σₙ² = stratVar n f = Var(μ̂ₙ)`. -/
theorem tendstoInDistribution_deepNet [NeZero b] (hb : 1 < b) (D : ℕ → ℕ)
    {mT : ∀ m, MeasurableSpace (OwenTree b (m + D m))}
    [∀ m, DiscreteMeasurableSpace (OwenTree b (m + D m))] {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {P : Measure Ω} [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b (m + D m)}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ} (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hTlaw : ∀ m, HasLaw (T m) (uniformOn univ) P)
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) f (deepNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) atTop Z (fun _ ↦ P) P' := by
  have hfun : (fun m ω ↦ (sampleMean (b ^ m) f (deepNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) =
      fun m ω ↦ (sampleMean (b ^ m) f (stratPoints (b ^ m) (deepRemainder (T m ω) (R m ω))) -
        ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f) := by
    funext m ω
    rw [sampleMean_deepNet]
  rw [hfun]
  exact tendstoInDistribution_stratified hfm hf hf' hnc (N := fun m ↦ b ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt hb) (Ω := fun _ ↦ Ω) (P := fun _ ↦ P)
    (V := fun m ω ↦ deepRemainder (T m ω) (R m ω))
    (fun m ↦ hasLaw_deepRemainder (hT m) (hR m) (hTlaw m) (hRlaw m) (hind m)) hZ

end RQMCMarkov.OwenScrambling
