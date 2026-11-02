/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.Stratified
import Mathlib.Probability.UniformOn

/-!
# Owen's nested uniform scramble in one dimension is stratified sampling (post #2)

Post #2: "a more powerful but more computationally costly randomization for digital nets is
'Owen Scrambling' which is a 'nested uniform scramble'" (Owen 1995, 1997). In one dimension and
base `b`, the `(0,m,1)`-net is `{k/bᵐ : k < bᵐ}`, one point in each `b`-adic cell
`[k/bᵐ, (k+1)/bᵐ)`.

**The scramble.** A point's first `m` base-`b` digits form a word `w : Fin m → Fin b` (most
significant digit first; `digitEquiv` identifies words with cells `k < bᵐ`, and
`digitEquiv_symm_apply_val` shows that digit `j` of the cell `k` is `⌊k / b^(m-1-j)⌋ mod b`, the
`(j+1)`-th base-`b` digit of `k/bᵐ`). An *Owen tree* `T : OwenTree b m` gives one permutation of
`Fin b` for each node, a level `j < m` together with a prefix of `j` digits. The scrambled word is
`owenWord T w j = T j (w₀ … w_{j-1}) (w j)`: digit `j` is permuted by the permutation attached to
the digits before it (`wordPrefix`). Owen's scramble takes all node permutations independent and
uniform, i.e. `T` uniform on the finite set `OwenTree b m`. Below the `m`-th digit the net points
have digits `0`; distinct cells sit below distinct nodes, so their lower digits are scrambled by
disjoint sets of independent uniform permutations and form independent uniform remainders. We
take this as the definition at depth `m` (`Owen1DDeep` proves it is exact: the genuine scramble
to any depth `M ≥ m` has the same law, `hasLaw_deepNetSorted`): the scrambled net is
`owenNet T r k = (owenCell T k + r k)/bᵐ`, with remainders `r k` i.i.d. `U[0,1)` independent of
`T`, where `owenCell T` is the induced permutation of the cells.

## Main results

* `DigitWord`, `wordPrefix`, `OwenTree`, `owenWord`, `digitEquiv` (`digitEquiv_apply_val`,
  `digitEquiv_symm_apply_val`), `owenCell`, `owenNet`, `owenNetSorted`, `owenRemainder`,
  `stratPoints`, `stratifiedLaw`: the definitions above.
* `wordPrefix_owenWord_eq`: the scramble is *nested*: the first `j` scrambled digits depend only on
  the first `j` digits (points in one `b`-adic interval of length `b^{-j}` go to one interval).
* `owenWord_injective`, `owenWordEquiv`, `owenCell`: for every tree the scramble permutes the words,
  hence the cells.
* `swapTree`, `card_filter_owenWord_eq`, `card_filter_owenWord`, `card_filter_owenCell`:
  `bᵐ · #{T | owenCell T k = j} = #OwenTree`: under a uniform tree each net point lands in each
  cell with probability `b^{-m}`.
* `owenNet_mem_stratum`, `owenNetSorted_apply`: exactly one scrambled point in each cell; relabelled
  by its cell, the point in cell `j` is `(j + r(σ⁻¹ j))/bᵐ`.
* `hasLaw_owenRemainder`, `owenNetSorted_eq_stratPoints`: the relabelled remainders
  `j ↦ R(σ_T⁻¹ j)` are again i.i.d. `U[0,1)`, and the relabelled net is their stratified point set.
* `hasLaw_owenNet` (requirement (i) of posts #1-#2): every scrambled point is `U[0,1)`.
* `hasLaw_owenNetSorted` (the key fact): the scrambled net, relabelled by cell, has EXACTLY the law
  `stratifiedLaw (bᵐ)` of independent stratified sampling, one independent uniform point in each
  cell. (This part uses only that the scramble permutes the cells independently of the
  remainders.)
* Tools: `measurePreserving_comp_perm` (relabelling preserves `U[0,1)ⁿ`),
  `measure_preimage_comp_of_indepFun` (mixing over an independent finite label),
  `measurable_comp_of_countable`, `sum_measure_preimage_singleton_eq_one`,
  `measure_preimage_singleton_of_uniform`, `hasLaw_apply_of_hasLaw_uniformCube`,
  `hasLaw_eval_uniformCube`, `iIndepFun_eval_uniformCube`, `measurable_sampleMean`,
  `sampleMean_owenNet` (relabelling leaves the estimator unchanged).
* `map_sampleMean_owenNet`, `identDistrib_sampleMean_owenNet`: hence the scrambled-net estimator
  has the law of the independent-stratified estimator of `Stratified`;
  `integral_sampleMean_owenNet` (unbiased), `variance_sampleMean_owenNet` (`Var = n⁻² Σᵢ Var(f |
  cell i)`), `variance_sampleMean_owenNet_le_mc` (never worse than MC) and
  `variance_sampleMean_owenNet_le_lipschitz` (`K²/(12 n³)` for `K`-Lipschitz `f`, `n = bᵐ`).

**Reading.** "Nested uniform scramble" is read at depth `m` with independent uniform remainders, as
above; this is exact in law for the net (whose points have distinct `m`-digit prefixes), not for
general point sets (`Owen1DDeep`).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- A base-`b` word of length `m`: the first `m` base-`b` digits of a point, most significant
first. -/
abbrev DigitWord (b m : ℕ) : Type := Fin m → Fin b

/-- The first `j` digits `w₀, …, w_{j-1}` of a word. -/
def wordPrefix {b m : ℕ} (w : DigitWord b m) (j : Fin m) : Fin j → Fin b :=
  fun i ↦ w ⟨i, i.2.trans j.2⟩

/-- An Owen scrambling tree of depth `m`: a permutation of the digits `Fin b` for each node, i.e.
for each level `j < m` and each prefix of `j` digits. -/
abbrev OwenTree (b m : ℕ) : Type := (j : Fin m) → (Fin j → Fin b) → Equiv.Perm (Fin b)

/-- **Owen's nested scramble of a word**: digit `j` is permuted by the permutation of the node
given by the `j` digits before it, `owenWord T w j = T j (w₀ … w_{j-1}) (w j)`. -/
def owenWord {b m : ℕ} (T : OwenTree b m) (w : DigitWord b m) : DigitWord b m :=
  fun j ↦ T j (wordPrefix w j) (w j)

/-- **The scramble is nested**: the first `j` scrambled digits depend only on the first `j`
digits. -/
theorem wordPrefix_owenWord_eq {b m : ℕ} (T : OwenTree b m) {w w' : DigitWord b m} (j : Fin m)
    (h : wordPrefix w j = wordPrefix w' j) :
    wordPrefix (owenWord T w) j = wordPrefix (owenWord T w') j := by
  funext i
  have hi : ∀ i' : Fin m, (i' : ℕ) < j → w i' = w' i' := fun i' hi' ↦
    congrFun h ⟨i', hi'⟩
  have hp : wordPrefix w ⟨i, i.2.trans j.2⟩ = wordPrefix w' ⟨i, i.2.trans j.2⟩ := by
    funext l
    exact hi _ (l.2.trans i.2)
  change T _ (wordPrefix w _) (w _) = T _ (wordPrefix w' _) (w' _)
  rw [hp, hi _ i.2]

/-- **The scramble is injective** on words, for every tree. -/
theorem owenWord_injective {b m : ℕ} (T : OwenTree b m) : Function.Injective (owenWord T) := by
  intro w w' h
  have key : ∀ k : ℕ, ∀ i : Fin m, (i : ℕ) < k → w i = w' i := by
    intro k
    induction k with
    | zero => exact fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
        intro i hi
        have hp : wordPrefix w i = wordPrefix w' i := by
          funext l
          exact ih _ (lt_of_lt_of_le l.2 (Nat.lt_succ_iff.1 hi))
        have hi' := congrFun h i
        change T i (wordPrefix w i) (w i) = T i (wordPrefix w' i) (w' i) at hi'
        rw [hp] at hi'
        exact (T i (wordPrefix w' i)).injective hi'
  funext i
  exact key _ i (Nat.lt_succ_self _)

/-- The scramble as a permutation of the words. -/
noncomputable def owenWordEquiv {b m : ℕ} (T : OwenTree b m) : Equiv.Perm (DigitWord b m) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (owenWord_injective T))

/-- Words of length `m` are the cells `k < bᵐ`: digit `j` has weight `b^(m-1-j)`. -/
def digitEquiv (b m : ℕ) : DigitWord b m ≃ Fin (b ^ m) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl _)).trans finFunctionFinEquiv

/-- The cell of a word: `Σⱼ wⱼ b^(m-1-j)`. -/
theorem digitEquiv_apply_val (b m : ℕ) (w : DigitWord b m) :
    (digitEquiv b m w : ℕ) = ∑ j : Fin m, (w j : ℕ) * b ^ (m - (j + 1)) := by
  change (finFunctionFinEquiv (fun i ↦ w (Fin.revPerm.symm i)) : ℕ) = _
  rw [finFunctionFinEquiv_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i ↦ ?_)
  have h1 : Fin.revPerm.symm i = Fin.revPerm i := rfl
  rw [h1]
  change (w (Fin.rev i) : ℕ) * b ^ (i : ℕ) = (w (Fin.rev i) : ℕ) * b ^ (m - ((Fin.rev i : ℕ) + 1))
  rw [Fin.val_rev]
  congr 2
  omega

/-- **The digits of a cell**: digit `j` (most significant first) of the cell `k < bᵐ` is
`⌊k / b^(m-1-j)⌋ mod b`, the `(j+1)`-th base-`b` digit of the net point `k/bᵐ`. -/
theorem digitEquiv_symm_apply_val (b m : ℕ) (k : Fin (b ^ m)) (j : Fin m) :
    ((digitEquiv b m).symm k j : ℕ) = k / b ^ (m - (j + 1)) % b := by
  change (finFunctionFinEquiv.symm k (Fin.revPerm j) : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val]
  rfl

/-- **The scrambled cell**: the permutation `σ_T` of the cells `k < bᵐ` induced by the scramble,
`σ_T k = digitEquiv (owenWord T (digits of k))`. -/
noncomputable def owenCell {b m : ℕ} (T : OwenTree b m) : Equiv.Perm (Fin (b ^ m)) :=
  ((digitEquiv b m).symm.trans (owenWordEquiv T)).trans (digitEquiv b m)

/-- `σ_T k` is the cell of the scrambled digits of `k`. -/
theorem owenCell_apply {b m : ℕ} (T : OwenTree b m) (k : Fin (b ^ m)) :
    owenCell T k = digitEquiv b m (owenWord T ((digitEquiv b m).symm k)) := rfl

/-- The tree that composes the permutations along the path of `w` with the transpositions
`(v j  v' j)`; it maps the trees scrambling `w` to `v` onto those scrambling `w` to `v'`. -/
def swapTree {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) : OwenTree b m :=
  fun j p ↦ if p = wordPrefix w j then Equiv.swap (v j) (v' j) * T j p else T j p

/-- `swapTree` is an involution. -/
theorem swapTree_swapTree {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) :
    swapTree w v v' (swapTree w v v' T) = T := by
  funext j p
  by_cases h : p = wordPrefix w j
  · simp only [swapTree, h, ite_true]
    exact Equiv.swap_mul_self_mul _ _ _
  · simp only [swapTree, h, ite_false]

/-- `swapTree` swaps the scrambled digits of `w`. -/
theorem owenWord_swapTree {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) (j : Fin m) :
    owenWord (swapTree w v v' T) w j = Equiv.swap (v j) (v' j) (owenWord T w j) := by
  simp only [owenWord, swapTree, ite_true]
  rfl

/-- `swapTree` maps the trees with `owenWord T w = v` to those with `owenWord T w = v'`. -/
theorem owenWord_swapTree_eq_iff {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) :
    owenWord (swapTree w v v' T) w = v' ↔ owenWord T w = v := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    rw [owenWord_swapTree, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hj
    exact hj
  · intro h
    funext j
    rw [owenWord_swapTree, h, Equiv.swap_apply_left]

/-- **All scrambled words are equally likely**: the number of trees scrambling `w` to `v` does not
depend on `v`. -/
theorem card_filter_owenWord_eq {b m : ℕ} (w v v' : DigitWord b m) :
    (Finset.univ.filter fun T : OwenTree b m ↦ owenWord T w = v).card =
      (Finset.univ.filter fun T : OwenTree b m ↦ owenWord T w = v').card := by
  refine Finset.card_nbij' (swapTree w v v') (swapTree w v v') (fun T hT ↦ ?_) (fun T hT ↦ ?_)
    (fun T _ ↦ swapTree_swapTree w v v' T) (fun T _ ↦ swapTree_swapTree w v v' T)
  · rw [Finset.mem_coe, Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_univ _, (owenWord_swapTree_eq_iff w v v' T).2 hT.2⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at hT ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← owenWord_swapTree_eq_iff w v v', swapTree_swapTree]
    exact hT.2

/-- `bᵐ` times the number of trees scrambling `w` to `v` is the number of trees. -/
theorem card_filter_owenWord {b m : ℕ} (w v : DigitWord b m) :
    b ^ m * (Finset.univ.filter fun T : OwenTree b m ↦ owenWord T w = v).card =
      Fintype.card (OwenTree b m) := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun T : OwenTree b m ↦ owenWord T w)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun v' _ ↦ card_filter_owenWord_eq w v' v), Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]

/-- **Each net point lands in each cell equally often**: `bᵐ · #{T | σ_T k = j} = #OwenTree`. -/
theorem card_filter_owenCell {b m : ℕ} (k j : Fin (b ^ m)) :
    b ^ m * (Finset.univ.filter fun T : OwenTree b m ↦ owenCell T k = j).card =
      Fintype.card (OwenTree b m) := by
  have hfilt : (Finset.univ.filter fun T : OwenTree b m ↦ owenCell T k = j) =
      Finset.univ.filter fun T : OwenTree b m ↦
        owenWord T ((digitEquiv b m).symm k) = (digitEquiv b m).symm j := by
    refine Finset.filter_congr (fun T _ ↦ ?_)
    rw [owenCell_apply, ← Equiv.eq_symm_apply]
  rw [hfilt, card_filter_owenWord]

/-- The scrambled net with remainders `r`: the point of cell `k` goes to
`(σ_T k + r k)/bᵐ`. -/
noncomputable def owenNet {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun k ↦ stratumMap (b ^ m) (owenCell T k) (r k)

/-- The scrambled point of net point `k` lies in the scrambled cell `σ_T k`. -/
theorem owenNet_mem_stratum {b m : ℕ} (hb : b ≠ 0) (T : OwenTree b m) {r : Fin (b ^ m) → ℝ}
    (k : Fin (b ^ m)) (hr : r k ∈ Ico (0 : ℝ) 1) :
    owenNet T r k ∈ stratum (b ^ m) (owenCell T k) := by
  have h := stratumMap_preimage_stratum (pow_ne_zero m hb) (owenCell T k)
  have hmem : r k ∈ stratumMap (b ^ m) (owenCell T k) ⁻¹' stratum (b ^ m) (owenCell T k) := by
    rw [h]
    exact hr
  exact hmem

/-- The scrambled net relabelled by cell: the point lying in cell `j`. -/
noncomputable def owenNetSorted {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun j ↦ owenNet T r ((owenCell T).symm j)

/-- The point in cell `j` is `(j + r(σ_T⁻¹ j))/bᵐ`. -/
theorem owenNetSorted_apply {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ)
    (j : Fin (b ^ m)) :
    owenNetSorted T r j = stratumMap (b ^ m) j (r ((owenCell T).symm j)) := by
  simp only [owenNetSorted, owenNet, Equiv.apply_symm_apply]

/-- The stratified points `(i + vᵢ)/n` of `v : Fin n → ℝ`. -/
noncomputable def stratPoints (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ stratumMap n i (v i)

/-- `stratPoints n` is measurable. -/
theorem measurable_stratPoints (n : ℕ) : Measurable (stratPoints n) :=
  Measurable.of_eval fun (i : Fin n) ↦ (measurable_stratumMap n i).comp (measurable_pi_apply i)

/-- **The law of independent stratified sampling**: one independent uniform point `(i + Vᵢ)/n`
in each cell, `V ~ U[0,1)ⁿ`. -/
noncomputable def stratifiedLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (uniformCube n).map (stratPoints n)

/-- Relabelling by a permutation preserves the uniform law on `[0,1)ⁿ`. -/
theorem measurePreserving_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun (r : Fin n → ℝ) j ↦ r (σ.symm j)) (uniformCube n) (uniformCube n) := by
  have := isProbabilityMeasure_uniformIco
  have h := measurePreserving_piCongrLeft (fun _ : Fin n ↦ uniformIco) σ
  have hfun : (fun (r : Fin n → ℝ) j ↦ r (σ.symm j)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) σ) := by
    funext r j
    rw [MeasurableEquiv.coe_piCongrLeft]
    conv_rhs => rw [← σ.apply_symm_apply j]
    rw [Equiv.piCongrLeft_apply_apply]
  rw [hfun]
  exact h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Mixing over a finite independent label.** If `T` takes values in a finite discrete space and
is independent of `R`, then `P(G(T, R) ∈ A) = Σₜ P(T = t) · P(G(t, R) ∈ A)`. -/
theorem measure_preimage_comp_of_indepFun {τ E F : Type*} [Fintype τ] {mτ : MeasurableSpace τ}
    [DiscreteMeasurableSpace τ] {mE : MeasurableSpace E} [MeasurableSpace F]
    {P : Measure Ω} {T : Ω → τ} {R : Ω → E} (hT : Measurable T) (hR : Measurable R)
    (hind : IndepFun T R P) {G : τ → E → F} (hG : ∀ t, Measurable (G t)) {A : Set F}
    (hA : MeasurableSet A) :
    P ((fun ω ↦ G (T ω) (R ω)) ⁻¹' A) = ∑ t, P (T ⁻¹' {t}) * P.map R (G t ⁻¹' A) := by
  have hset : (fun ω ↦ G (T ω) (R ω)) ⁻¹' A = ⋃ t, (T ⁻¹' {t} ∩ R ⁻¹' (G t ⁻¹' A)) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h ↦ ⟨T ω, rfl, h⟩, fun ⟨t, ht, h⟩ ↦ ht ▸ h⟩
  have hmeas : ∀ t, MeasurableSet (T ⁻¹' {t} ∩ R ⁻¹' (G t ⁻¹' A)) := fun t ↦
    (hT (measurableSet_singleton t)).inter (hR ((hG t) hA))
  have hdisj : Pairwise (Function.onFun Disjoint fun t ↦ T ⁻¹' {t} ∩ R ⁻¹' (G t ⁻¹' A)) := by
    intro t t' htt'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact htt' (h1.1.symm.trans h2.1)
  rw [hset, measure_iUnion hdisj hmeas, tsum_fintype]
  refine Finset.sum_congr rfl (fun t _ ↦ ?_)
  rw [hind.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton t) ((hG t) hA),
    Measure.map_apply hR ((hG t) hA)]

/-- `ω ↦ G(T ω, R ω)` is measurable when `T` takes values in a countable discrete space. -/
theorem measurable_comp_of_countable {τ E F : Type*} [Countable τ] {mτ : MeasurableSpace τ}
    [DiscreteMeasurableSpace τ] {mE : MeasurableSpace E} [MeasurableSpace F]
    {T : Ω → τ} {R : Ω → E} (hT : Measurable T) (hR : Measurable R) {G : τ → E → F}
    (hG : ∀ t, Measurable (G t)) : Measurable fun ω ↦ G (T ω) (R ω) :=
  (measurable_from_prod_countable_right (f := fun p : τ × E ↦ G p.1 p.2) hG).comp
    (hT.prodMk hR)

/-- With a finite discrete label, the fibre probabilities sum to one. -/
theorem sum_measure_preimage_singleton_eq_one {τ : Type*} [Fintype τ] {mτ : MeasurableSpace τ}
    [DiscreteMeasurableSpace τ] {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → τ}
    (hT : Measurable T) : ∑ t, P (T ⁻¹' {t}) = 1 := by
  rw [sum_measure_preimage_singleton Finset.univ (fun t _ ↦ hT (measurableSet_singleton t)),
    Finset.coe_univ, preimage_univ, measure_univ]

variable {b m : ℕ} {mT : MeasurableSpace (OwenTree b m)} [DiscreteMeasurableSpace (OwenTree b m)]

/-- **The key fact: the Owen-scrambled net is independent stratified sampling.** Let the tree `T`
(any law) be independent of the remainders `R ~ U[0,1)^(bᵐ)`. Relabelled by cell, the scrambled
net `{(σ_T k + R k)/bᵐ}` has exactly the law `stratifiedLaw (bᵐ)`: one independent uniform point in
each cell `[j/bᵐ, (j+1)/bᵐ)`. -/
theorem hasLaw_owenNetSorted {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ owenNetSorted (T ω) (R ω)) (stratifiedLaw (b ^ m)) P := by
  have hG : ∀ t : OwenTree b m, owenNetSorted t =
      stratPoints (b ^ m) ∘ (fun (r : Fin (b ^ m) → ℝ) j ↦ r ((owenCell t).symm j)) := by
    intro t
    funext r j
    rw [owenNetSorted_apply]
    rfl
  have hGm : ∀ t : OwenTree b m, Measurable (owenNetSorted t) := fun t ↦ by
    rw [hG t]
    exact (measurable_stratPoints _).comp (measurePreserving_comp_perm (owenCell t)).measurable
  have hGlaw : ∀ t : OwenTree b m, (uniformCube (b ^ m)).map (owenNetSorted t) =
      stratifiedLaw (b ^ m) := by
    intro t
    rw [hG t, ← Measure.map_map (measurable_stratPoints _)
      (measurePreserving_comp_perm (owenCell t)).measurable,
      (measurePreserving_comp_perm (owenCell t)).map_eq]
    rfl
  refine ⟨(measurable_comp_of_countable hT hR hGm).aemeasurable, ?_⟩
  ext A hA
  have hA' : ∀ t : OwenTree b m, uniformCube (b ^ m) (owenNetSorted t ⁻¹' A) =
      stratifiedLaw (b ^ m) A := fun t ↦ by
    rw [← Measure.map_apply (hGm t) hA, hGlaw t]
  rw [Measure.map_apply (measurable_comp_of_countable hT hR hGm) hA,
    measure_preimage_comp_of_indepFun hT hR hind hGm hA, hRlaw.map_eq,
    Finset.sum_congr rfl (fun t _ ↦ by rw [hA' t]), ← Finset.sum_mul,
    sum_measure_preimage_singleton_eq_one hT, one_mul]

/-- The remainders relabelled by cell: the remainder of the point lying in cell `j`,
`r(σ_T⁻¹ j)`. -/
noncomputable def owenRemainder {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun j ↦ r ((owenCell T).symm j)

/-- The scrambled net relabelled by cell is the stratified point set of the relabelled
remainders. -/
theorem owenNetSorted_eq_stratPoints {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    owenNetSorted T r = stratPoints (b ^ m) (owenRemainder T r) := by
  funext j
  rw [owenNetSorted_apply]
  rfl

/-- **The relabelled remainders are i.i.d. uniform**: if the tree is independent of
`R ~ U[0,1)^(bᵐ)`, then `j ↦ R(σ_T⁻¹ j)` is again `U[0,1)^(bᵐ)`. -/
theorem hasLaw_owenRemainder {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ owenRemainder (T ω) (R ω)) (uniformCube (b ^ m)) P := by
  have hmp : ∀ t : OwenTree b m, MeasurePreserving (owenRemainder t) (uniformCube (b ^ m))
      (uniformCube (b ^ m)) := fun t ↦ measurePreserving_comp_perm (owenCell t)
  have hGm : ∀ t : OwenTree b m, Measurable (owenRemainder t) := fun t ↦ (hmp t).measurable
  refine ⟨(measurable_comp_of_countable hT hR hGm).aemeasurable, ?_⟩
  ext A hA
  have hA' : ∀ t : OwenTree b m, uniformCube (b ^ m) (owenRemainder t ⁻¹' A) =
      uniformCube (b ^ m) A := fun t ↦ by
    rw [← Measure.map_apply (hGm t) hA, (hmp t).map_eq]
  rw [Measure.map_apply (measurable_comp_of_countable hT hR hGm) hA,
    measure_preimage_comp_of_indepFun hT hR hind hGm hA, hRlaw.map_eq,
    Finset.sum_congr rfl (fun t _ ↦ by rw [hA' t]), ← Finset.sum_mul,
    sum_measure_preimage_singleton_eq_one hT, one_mul]

/-- A uniform tree gives each tree probability `1/#OwenTree`. -/
theorem measure_preimage_singleton_of_uniform {P : Measure Ω} {T : Ω → OwenTree b m}
    (hT : Measurable T) (hTlaw : HasLaw T (uniformOn univ) P) (t : OwenTree b m) :
    P (T ⁻¹' {t}) = (Fintype.card (OwenTree b m) : ℝ≥0∞)⁻¹ := by
  rw [← Measure.map_apply hT (measurableSet_singleton t), hTlaw.map_eq, uniformOn_univ,
    Measure.count_singleton, one_div]

/-- The coordinates of `R ~ U[0,1)ⁿ` are `U[0,1)`. -/
theorem hasLaw_apply_of_hasLaw_uniformCube {n : ℕ} {P : Measure Ω} {R : Ω → Fin n → ℝ}
    (hR : Measurable R) (hRlaw : HasLaw R (uniformCube n) P) (k : Fin n) :
    HasLaw (fun ω ↦ R ω k) uniformIco P := by
  have := isProbabilityMeasure_uniformIco
  refine ⟨((measurable_pi_apply k).comp hR).aemeasurable, ?_⟩
  change Measure.map ((fun f : Fin n → ℝ ↦ f k) ∘ R) P = uniformIco
  rw [← Measure.map_map (measurable_pi_apply k) hR, hRlaw.map_eq]
  exact (measurePreserving_eval (fun _ : Fin n ↦ uniformIco) k).map_eq

/-- **RQMC requirement (i) for the scrambled net** (posts #1-#2): with a uniform tree independent
of the remainders `R ~ U[0,1)^(bᵐ)`, each scrambled point `(σ_T k + R k)/bᵐ` is `U[0,1)`. -/
theorem hasLaw_owenNet (hb : b ≠ 0) {P : Measure Ω} {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hTlaw : HasLaw T (uniformOn univ) P) (hRlaw : HasLaw R (uniformCube (b ^ m)) P)
    (hind : IndepFun T R P) (k : Fin (b ^ m)) :
    HasLaw (fun ω ↦ owenNet (T ω) (R ω) k) uniformIco P := by
  have hn0 : b ^ m ≠ 0 := pow_ne_zero m hb
  set G : OwenTree b m → (Fin (b ^ m) → ℝ) → ℝ :=
    fun t r ↦ stratumMap (b ^ m) (owenCell t k) (r k) with hGdef
  have hGm : ∀ t, Measurable (G t) := fun t ↦
    (measurable_stratumMap (b ^ m) _).comp (measurable_pi_apply k)
  have hm : Measurable fun ω ↦ G (T ω) (R ω) := measurable_comp_of_countable hT hR hGm
  have hRk := hasLaw_apply_of_hasLaw_uniformCube hR hRlaw k
  refine ⟨hm.aemeasurable, ?_⟩
  ext A hA
  set F : Fin (b ^ m) → ℝ≥0∞ := fun j ↦ uniformIco.map (stratumMap (b ^ m) j) A with hF
  have hterm : ∀ t, P.map R (G t ⁻¹' A) = F (owenCell t k) := fun t ↦ by
    have hRkm : Measurable fun ω ↦ R ω k := (measurable_pi_apply k).comp hR
    change P.map R (G t ⁻¹' A) = uniformIco.map (stratumMap (b ^ m) (owenCell t k)) A
    rw [Measure.map_apply hR ((hGm t) hA), ← hRk.map_eq,
      Measure.map_apply (measurable_stratumMap _ _) hA,
      Measure.map_apply hRkm ((measurable_stratumMap _ _) hA)]
    rfl
  set c : ℝ≥0∞ := (Fintype.card (OwenTree b m) : ℝ≥0∞)⁻¹ with hc
  have hfib : ∀ j : Fin (b ^ m),
      ((Finset.univ.filter fun t : OwenTree b m ↦ owenCell t k = j).card : ℝ≥0∞) * c =
        ((b ^ m : ℕ) : ℝ≥0∞)⁻¹ := by
    intro j
    have h := congrArg (Nat.cast : ℕ → ℝ≥0∞) (card_filter_owenCell (b := b) (m := m) k j)
    rw [Nat.cast_mul] at h
    set x : ℝ≥0∞ := ((Finset.univ.filter fun t : OwenTree b m ↦ owenCell t k = j).card : ℝ≥0∞)
    have hcard : (Fintype.card (OwenTree b m) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, mul_zero] at h
      exact hcard h.symm
    have hxt : x ≠ ⊤ := ENNReal.natCast_ne_top _
    have hnt : ((b ^ m : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hn0' : ((b ^ m : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn0
    rw [hc, ← h, ENNReal.mul_inv (Or.inl hn0') (Or.inl hnt), mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel hx0 hxt, mul_one]
  change (P.map fun ω ↦ G (T ω) (R ω)) A = uniformIco A
  rw [Measure.map_apply hm hA, measure_preimage_comp_of_indepFun hT hR hind hGm hA,
    Finset.sum_congr rfl (fun t _ ↦ by
      rw [measure_preimage_singleton_of_uniform hT hTlaw t, hterm t]),
    ← Finset.sum_fiberwise Finset.univ (fun t : OwenTree b m ↦ owenCell t k)
      (fun t ↦ c * F (owenCell t k))]
  have hinner : ∀ j : Fin (b ^ m), ∑ t ∈ Finset.univ with owenCell t k = j, c * F (owenCell t k) =
      ((b ^ m : ℕ) : ℝ≥0∞)⁻¹ * F j := fun j ↦ by
    rw [Finset.sum_congr rfl (fun t ht ↦ by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      nsmul_eq_mul, ← mul_assoc, hfib j]
  rw [Finset.sum_congr rfl (fun j _ ↦ hinner j), ← Finset.mul_sum]
  have hsum : ∑ j : Fin (b ^ m), F j = ((b ^ m : ℕ) : ℝ≥0∞) * uniformIco A := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ A) (sum_map_stratumMap hn0)
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    exact h
  rw [hsum, ← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hn0)
    (ENNReal.natCast_ne_top _), one_mul]

/-- Relabelling does not change the estimator: `μ̂(owenNet) = μ̂(owenNetSorted)`. -/
theorem sampleMean_owenNet (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) (f : ℝ → ℝ) :
    sampleMean (b ^ m) f (owenNet T r) = sampleMean (b ^ m) f (owenNetSorted T r) := by
  unfold sampleMean
  congr 1
  exact (Equiv.sum_comp (owenCell T).symm (fun k ↦ f (owenNet T r k))).symm

/-- The sample mean is a measurable function of the points, for measurable `f`. -/
theorem measurable_sampleMean {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (sampleMean n f) := by
  change Measurable fun x : Fin n → ℝ ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, f (x i)
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum _ (fun (i : Fin n) _ ↦ hf.comp (measurable_pi_apply i))

/-- **The scrambled-net estimator has the law of the independent-stratified estimator**: for
measurable `f`, the law of `(1/bᵐ) Σₖ f(owenNet T R k)` is the law of
`(1/n) Σᵢ f((i + Vᵢ)/n)`, `V ~ U[0,1)ⁿ`, `n = bᵐ`. -/
theorem map_sampleMean_owenNet {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hf : Measurable f) :
    P.map (fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω))) =
      (uniformCube (b ^ m)).map (fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v)) := by
  have hfun : (fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω))) =
      sampleMean (b ^ m) f ∘ (fun ω ↦ owenNetSorted (T ω) (R ω)) :=
    funext fun ω ↦ sampleMean_owenNet (T ω) (R ω) f
  have hL := hasLaw_owenNetSorted hT hR hRlaw hind
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable (measurable_sampleMean hf).aemeasurable
    hL.aemeasurable, hL.map_eq, stratifiedLaw,
    Measure.map_map (measurable_sampleMean hf) (measurable_stratPoints _)]
  rfl

/-- The same statement as an `IdentDistrib`. -/
theorem identDistrib_sampleMean_owenNet {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hf : Measurable f) :
    IdentDistrib (fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)))
      (fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v)) P (uniformCube (b ^ m)) where
  aemeasurable_fst := ((measurable_sampleMean hf).comp
    (measurable_comp_of_countable (G := fun t r ↦ owenNet t r) hT hR fun _ ↦
      Measurable.of_eval fun (k : Fin (b ^ m)) ↦
        (measurable_stratumMap _ _).comp (measurable_pi_apply k))).aemeasurable
  aemeasurable_snd := ((measurable_sampleMean hf).comp (measurable_stratPoints _)).aemeasurable
  map_eq := map_sampleMean_owenNet hT hR hRlaw hind hf

/-- On `U[0,1)ⁿ` the coordinates are i.i.d. `U[0,1)`. -/
theorem hasLaw_eval_uniformCube {n : ℕ} (i : Fin n) :
    HasLaw (fun v : Fin n → ℝ ↦ v i) uniformIco (uniformCube n) := by
  have := isProbabilityMeasure_uniformIco
  exact ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n ↦ uniformIco) i).map_eq⟩

/-- On `U[0,1)ⁿ` the coordinates are independent. -/
theorem iIndepFun_eval_uniformCube (n : ℕ) :
    iIndepFun (fun (i : Fin n) (v : Fin n → ℝ) ↦ v i) (uniformCube n) := by
  have := isProbabilityMeasure_uniformIco
  exact iIndepFun_pi (X := fun _ x ↦ x) (fun _ ↦ aemeasurable_id)

/-- **The scrambled net is unbiased** (post #2): `E[(1/bᵐ) Σₖ f(owenNet T R k)] = ∫₀¹ f`. -/
theorem integral_sampleMean_owenNet (hb : b ≠ 0) {P : Measure Ω} {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hTlaw : HasLaw T (uniformOn univ) P) (hRlaw : HasLaw R (uniformCube (b ^ m)) P)
    (hind : IndepFun T R P) {f : ℝ → ℝ} (hf : Integrable f uniformIco) :
    ∫ ω, sampleMean (b ^ m) f (owenNet (T ω) (R ω)) ∂P = ∫ x, f x ∂uniformIco :=
  integral_sampleMean_iid (pow_ne_zero m hb)
    (fun k ↦ hasLaw_owenNet hb hT hR hTlaw hRlaw hind k) hf

/-- **Exact variance of the scrambled net** (post #2): it is the variance of independent
stratified sampling, `Var = n⁻² Σᵢ Var(f | cell i)`, `n = bᵐ`, for measurable `f ∈ L²`. -/
theorem variance_sampleMean_owenNet (hb : b ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] =
      (((b ^ m : ℕ) : ℝ)⁻¹) ^ 2 *
        ∑ i : Fin (b ^ m), Var[fun u ↦ f (stratumMap (b ^ m) i u); uniformIco] := by
  rw [(identDistrib_sampleMean_owenNet hT hR hRlaw hind hfm).variance_eq]
  exact variance_stratified_eq (pow_ne_zero m hb) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) hf

/-- **The scrambled net never does worse than MC**: `Var ≤ Var_{U[0,1)}(f)/bᵐ`. -/
theorem variance_sampleMean_owenNet_le_mc (hb : b ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] ≤
      Var[f; uniformIco] / (b ^ m : ℕ) := by
  have := isProbabilityMeasure_uniformIco
  rw [(identDistrib_sampleMean_owenNet hT hR hRlaw hind hfm).variance_eq]
  exact variance_stratified_le_mc (pow_ne_zero m hb) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) hf

/-- **The scrambled net, Lipschitz rate `O(n^{-3})`**: for `K`-Lipschitz `f` and `n = bᵐ`,
`Var ≤ K²/(12 n³)`, i.e. RMSE `O(n^{-3/2})`. -/
theorem variance_sampleMean_owenNet_le_lipschitz (hb : b ≠ 0) {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ}
    (hT : Measurable T) (hR : Measurable R) (hRlaw : HasLaw R (uniformCube (b ^ m)) P)
    (hind : IndepFun T R P) {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] ≤
      (K : ℝ) ^ 2 / (12 * ((b ^ m : ℕ) : ℝ) ^ 3) := by
  rw [(identDistrib_sampleMean_owenNet hT hR hRlaw hind hf.continuous.measurable).variance_eq]
  exact variance_stratified_le_lipschitz (pow_ne_zero m hb) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) hf

end RQMCMarkov.OwenScrambling
