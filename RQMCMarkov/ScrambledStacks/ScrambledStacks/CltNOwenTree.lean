/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.CltNCoins

/-!
# Owen's flips relabelled by the scrambled tree (post #3, code (iii), n states)

Under Owen's nested scramble the flip at depth `m` applied to the points of original `m`-digit
prefix `α` is `ω (i, m, α)`. The flips at depths `< m` induce a bijection `σ_m` of the depth-`m`
prefixes (original prefix ↦ scrambled prefix). The path coin of a cut point `c` at depth `m`
is the flip at the node `σ_m⁻¹(⌊2^m c⌋)` (`CltPathBits.pathPrefix`). We **relabel** the flips by
the nodes of the SCRAMBLED tree, `g ω (i, m, p) = ω (i, m, σ_m⁻¹ p)` (`owenRelabel`; the
coordinates with `p ≥ 2^m`, which Owen's scramble never uses, are left alone). Then:

* `pathCoin_owenTable_eq_relabel`: the path coin of `c ∈ [0,1)` at depth `m` is
  `g ω (i, m, ⌊2^m c⌋)` — two cut points share the relabelled coins of their common binary
  prefix, and use different ones from their first differing digit on;
* `measurePreserving_owenRelabel` (**the relabelling preserves Owen's measure**): `σ_m` depends
  only on the flips of depths `< m`, and a bijective relabelling of fresh fair coins is fair;
  proved through rectangle cylinders (`owenMeasure_relabel_rect`, by induction on the depth,
  conditioning on the finitely many flips above) and `eq_owenMeasure_of_box`.

This generalises `map_owenPathCoins` (one threshold per row) to all the nodes of the tree, which
is what the n-state CLT needs (`CltNOwen`). It is NOT a law transfer to the digital shift: under
the shift two cut points of a row share the same flip at every depth (`CltThreeState`).

## Main results

* `prefixDigits`, `owenNode`, `owenRelabel`, `owenRect`.
* `pathPrefix_congr_digits`, `pathPrefix_threshDigit_eq`, `pathCoin_owenTable_eq_relabel`.
* `owenNode_lt`, `owenNode_inj`, `owenNode_congr`, `owenRelabel_congr`, `measurable_owenRelabel`.
* `measure_eq_sum_restrict_preimage`, `coinMeasure_setOf_comp_eq` (cylinder tools).
* `owenMeasure_relabel_rect`, `eq_owenMeasure_of_box`, `measurePreserving_owenRelabel`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-! ### The relabelling -/

/-- The `m` binary digits of `p` (most significant first): digit `j` is bit `m − 1 − j`. -/
def prefixDigits (m p : ℕ) : ℕ → Bool := fun j ↦ p.testBit (m - 1 - j)

/-- The original depth-`m` prefix (a node of Owen's tree) that the scramble of row `i` sends to
the scrambled prefix `p`. -/
def owenNode (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) (m p : ℕ) : ℕ :=
  pathPrefix (owenTable ω i) (prefixDigits m p) m

/-- **Owen's flips relabelled by the scrambled tree**: the flip at depth `m` of the node whose
scrambled prefix is `p < 2^m` (other coordinates unchanged). -/
def owenRelabel (ω : Fin n × ℕ × ℕ → Bool) (q : Fin n × ℕ × ℕ) : Bool :=
  if q.2.2 < 2 ^ q.2.1 then ω (q.1, q.2.1, owenNode ω q.1 q.2.1 q.2.2) else ω q

/-- The rectangle of Owen coordinates of depth `< M` and prefix `< W`. -/
def owenRect (n M W : ℕ) : Finset (Fin n × ℕ × ℕ) := univ ×ˢ (range M ×ˢ range W)

/-- Membership in `owenRect`. -/
theorem mem_owenRect {M W : ℕ} {q : Fin n × ℕ × ℕ} :
    q ∈ owenRect n M W ↔ q.2.1 < M ∧ q.2.2 < W := by
  simp [owenRect]

/-- `owenBox n M = owenRect n M (2^M)`. -/
theorem owenBox_eq_owenRect (n M : ℕ) : owenBox n M = owenRect n M (2 ^ M) := rfl

/-- Path prefixes depend only on the first digits of the threshold. -/
theorem pathPrefix_congr_digits (f : ℕ → ℕ → Bool) {cb cb' : ℕ → Bool} {m : ℕ}
    (h : ∀ j < m, cb j = cb' j) : pathPrefix f cb m = pathPrefix f cb' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have ih' := ih fun j hj ↦ h j (by omega)
      change pathPrefix f cb m + 2 ^ m * (if xor (cb m) (f m (pathPrefix f cb m)) then 1 else 0) =
        pathPrefix f cb' m + 2 ^ m * (if xor (cb' m) (f m (pathPrefix f cb' m)) then 1 else 0)
      rw [ih', h m (by omega)]

/-- The digits of `c ∈ [0,1)` before depth `m` are those of `⌊2^m c⌋`. -/
theorem pathPrefix_threshDigit_eq (f : ℕ → ℕ → Bool) {c : ℝ} (hc1 : c < 1) (m : ℕ) :
    pathPrefix f (threshDigit c) m = pathPrefix f (prefixDigits m ⌊2 ^ m * c⌋₊) m := by
  refine pathPrefix_congr_digits f fun j hj ↦ ?_
  have h := (digitPrefix_eq_iff (threshDigit c) m ⌊2 ^ m * c⌋₊).1 (digitPrefix_threshDigit hc1 m)
  exact h.2 j hj

/-- `⌊2^m c⌋ < 2^m` for `c < 1`. -/
theorem floor_two_pow_mul_lt {c : ℝ} (hc1 : c < 1) (m : ℕ) : ⌊2 ^ m * c⌋₊ < 2 ^ m := by
  rw [← digitPrefix_threshDigit hc1 m]
  exact digitPrefix_lt _ m

/-- **Path coins are relabelled coins**: for `c ∈ [0,1)`, the path coin of `c` at depth `m` is the
relabelled flip at the scrambled node `⌊2^m c⌋`. -/
theorem pathCoin_owenTable_eq_relabel (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) {c : ℝ}
    (hc1 : c < 1) (m : ℕ) :
    pathCoin (owenTable ω i) (threshDigit c) m = owenRelabel ω (i, m, ⌊2 ^ m * c⌋₊) := by
  unfold pathCoin owenRelabel owenNode
  simp only [floor_two_pow_mul_lt hc1 m, ite_true]
  rw [pathPrefix_threshDigit_eq _ hc1 m]
  rfl

/-- `owenNode < 2^m`. -/
theorem owenNode_lt (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) (m p : ℕ) : owenNode ω i m p < 2 ^ m :=
  pathPrefix_lt _ _ m

/-- **The scrambled tree is a bijection**: distinct scrambled prefixes come from distinct
nodes. -/
theorem owenNode_inj (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) {m p p' : ℕ} (hp : p < 2 ^ m)
    (hp' : p' < 2 ^ m) (h : owenNode ω i m p = owenNode ω i m p') : p = p' := by
  have key : ∀ q < 2 ^ m,
      digitPrefix (scrambledDigit (owenTable ω i) (owenNode ω i m q)) m = q := by
    intro q hq
    have hmod : owenNode ω i m q % 2 ^ m = pathPrefix (owenTable ω i) (prefixDigits m q) m :=
      Nat.mod_eq_of_lt (owenNode_lt ω i m q)
    have htie := (tie_iff_mod_eq_pathPrefix (owenTable ω i) (prefixDigits m q)
      (owenNode ω i m q) m).2 hmod
    exact (digitPrefix_eq_iff _ m q).2 ⟨hq, htie⟩
  rw [← key p hp, ← key p' hp', h]

/-- The scrambled tree of depth `m` depends only on the flips of `owenBox n m`. -/
theorem owenNode_congr {ω ω' : Fin n × ℕ × ℕ → Bool} {m : ℕ}
    (h : ∀ q ∈ owenBox n m, ω q = ω' q) (i : Fin n) (p : ℕ) :
    owenNode ω i m p = owenNode ω' i m p :=
  pathPrefix_owen_congr (prefixDigits m p) i h m le_rfl

/-- The relabelled flip at `q = (i, m, p)` depends only on the flips of
`owenRect n (m + 1) (max (p + 1) (2^m))`. -/
theorem owenRelabel_congr {ω ω' : Fin n × ℕ × ℕ → Bool} {q : Fin n × ℕ × ℕ}
    (h : ∀ q' ∈ owenRect n (q.2.1 + 1) (max (q.2.2 + 1) (2 ^ q.2.1)), ω q' = ω' q') :
    owenRelabel ω q = owenRelabel ω' q := by
  obtain ⟨i, m, p⟩ := q
  have hbox : ∀ q' ∈ owenBox n m, ω q' = ω' q' := fun q' hq' ↦ by
    refine h q' (mem_owenRect.2 ?_)
    have := mem_owenRect.1 ((owenBox_eq_owenRect n m) ▸ hq')
    exact ⟨by simp only at this ⊢; omega, by simp only at this ⊢; omega⟩
  unfold owenRelabel
  by_cases hp : p < 2 ^ m
  · simp only [hp, ite_true]
    rw [owenNode_congr hbox i p]
    refine h _ (mem_owenRect.2 ⟨by simp, ?_⟩)
    simp only
    exact lt_of_lt_of_le (owenNode_lt ω' i m p) (le_max_right _ _)
  · simp only [hp, ite_false]
    exact h _ (mem_owenRect.2 ⟨by simp, by simp⟩)

/-- The relabelling is measurable. -/
theorem measurable_owenRelabel : Measurable (owenRelabel (n := n)) := by
  classical
  refine measurable_pi_iff.2 fun q ↦ ?_
  have hloc : IsLocal (fun ω : Fin n × ℕ × ℕ → Bool ↦ owenRelabel ω q)
      (owenRect n (q.2.1 + 1) (max (q.2.2 + 1) (2 ^ q.2.1))) :=
    fun ω ω' h ↦ owenRelabel_congr h
  exact hloc.measurable

/-! ### Cylinder tools -/

/-- A measure on `ι → Bool` is the sum of its pieces on the cells of a finite restriction. -/
theorem measure_eq_sum_restrict_preimage {ι : Type*} [DecidableEq ι] (μ : Measure (ι → Bool))
    (S : Finset ι) (A : Set (ι → Bool)) :
    μ A = ∑ a : S → Bool, μ (A ∩ S.restrict ⁻¹' {a}) := by
  have h := sum_measure_preimage_singleton (μ := μ.restrict A) (univ : Finset (S → Bool))
    (f := S.restrict) fun y _ ↦ Finset.measurable_restrict S (measurableSet_singleton y)
  rw [coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  rw [← h]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Measure.restrict_apply (Finset.measurable_restrict S (measurableSet_singleton a)),
    Set.inter_comm]

/-- **Cylinders of fair coins**: prescribing the coins at `|A|` distinct coordinates has
probability `2^{-|A|}`. -/
theorem coinMeasure_setOf_comp_eq {ι κ : Type*} {c : κ → ι} (hc : Function.Injective c)
    (A : Finset κ) (v : κ → Bool) :
    coinMeasure ι {ω | ∀ t ∈ A, ω (c t) = v t} = 2⁻¹ ^ A.card := by
  classical
  set u : ι → Bool := Function.extend c v fun _ ↦ false with hu
  have e : {ω : ι → Bool | ∀ t ∈ A, ω (c t) = v t} =
      Set.pi ((A.image c : Finset ι) : Set ι) fun q ↦ ({u q} : Set Bool) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, coe_image, Set.mem_image, mem_coe,
      Set.mem_singleton_iff, forall_exists_index, and_imp]
    constructor
    · rintro h q t ht rfl
      rw [hu, hc.extend_apply]
      exact h t ht
    · intro h t ht
      have := h (c t) t ht rfl
      rwa [hu, hc.extend_apply] at this
  rw [e, Measure.infinitePi_pi _ fun q _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const, card_image_of_injective _ hc]

/-! ### The relabelling preserves Owen's measure -/

/-- **Rectangle cylinders of the relabelled flips**: for every depth `M`, width `W` and values
`b`, `P(g ω = b on owenRect n M W) = 2^{-nMW}`. By induction on `M`: conditionally on the flips
of the rows above (finitely many cells), the depth-`M` relabelled flips are a bijective relabelling
of fresh fair coins. -/
theorem owenMeasure_relabel_rect (W : ℕ) (b : Fin n × ℕ × ℕ → Bool) (M : ℕ) :
    owenMeasure n {ω | ∀ q ∈ owenRect n M W, owenRelabel ω q = b q} = 2⁻¹ ^ (n * M * W) := by
  classical
  induction M with
  | zero =>
      have : {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenRect n 0 W, owenRelabel ω q = b q} =
          Set.univ := by
        ext ω
        simp [owenRect]
      rw [this, measure_univ, mul_zero, zero_mul, pow_zero]
  | succ M ih =>
      set R := owenRect n M (max W (2 ^ M)) with hR
      set E := {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenRect n M W, owenRelabel ω q = b q}
        with hE
      set G := {ω : Fin n × ℕ × ℕ → Bool |
        ∀ i : Fin n, ∀ p < W, owenRelabel ω (i, M, p) = b (i, M, p)} with hG
      have hsplit : {ω : Fin n × ℕ × ℕ → Bool |
          ∀ q ∈ owenRect n (M + 1) W, owenRelabel ω q = b q} = E ∩ G := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hE, hG]
        constructor
        · intro h
          refine ⟨fun q hq ↦ h q ?_, fun i p hp ↦ h (i, M, p) ?_⟩
          · have := mem_owenRect.1 hq
            exact mem_owenRect.2 ⟨by omega, this.2⟩
          · exact mem_owenRect.2 ⟨by simp, hp⟩
        · rintro ⟨h1, h2⟩ ⟨i, m, p⟩ hq
          have hq' := mem_owenRect.1 hq
          simp only at hq'
          rcases Nat.lt_succ_iff_lt_or_eq.1 hq'.1 with hm | rfl
          · exact h1 _ (mem_owenRect.2 ⟨hm, hq'.2⟩)
          · exact h2 i p hq'.2
      -- `E` and the depth-`M` tree only see the flips of `R`
      have hER : ∀ ω ω' : Fin n × ℕ × ℕ → Bool, (∀ q ∈ R, ω q = ω' q) →
          (ω ∈ E ↔ ω' ∈ E) := by
        intro ω ω' h
        have hq : ∀ q ∈ owenRect n M W, owenRelabel ω q = owenRelabel ω' q := by
          intro q hq
          refine owenRelabel_congr fun q' hq' ↦ h q' (mem_owenRect.2 ?_)
          have h1 := mem_owenRect.1 hq
          have h2 := mem_owenRect.1 hq'
          have h3 : 2 ^ q.2.1 ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) h1.1.le
          refine ⟨by omega, lt_of_lt_of_le h2.2 ?_⟩
          exact max_le (le_trans (by omega) (le_max_left _ _)) (h3.trans (le_max_right _ _))
        simp only [hE, Set.mem_ofPred_eq]
        constructor
        · intro h' q hq'
          rw [← hq q hq']
          exact h' q hq'
        · intro h' q hq'
          rw [hq q hq']
          exact h' q hq'
      have hNR : ∀ ω ω' : Fin n × ℕ × ℕ → Bool, (∀ q ∈ R, ω q = ω' q) →
          ∀ i p, owenNode ω i M p = owenNode ω' i M p := by
        intro ω ω' h i p
        refine owenNode_congr (fun q hq ↦ h q (mem_owenRect.2 ?_)) i p
        have := mem_owenRect.1 ((owenBox_eq_owenRect n M) ▸ hq)
        exact ⟨this.1, lt_of_lt_of_le this.2 (le_max_right _ _)⟩
      -- the cells of the restriction to `R`
      set ωa : (R → Bool) → Fin n × ℕ × ℕ → Bool := fun a ↦ localExtend R (fun _ ↦ false) a
        with hωa
      have hcell : ∀ (a : R → Bool) (ω : Fin n × ℕ × ℕ → Bool), R.restrict ω = a →
          ∀ q ∈ R, ω q = ωa a q := by
        intro a ω hω q hq
        simp only [hωa, localExtend, hq, dite_true]
        rw [← hω]
        rfl
      set τ : (R → Bool) → Fin n → ℕ → ℕ := fun a i p ↦
        if p < 2 ^ M then owenNode (ωa a) i M p else p with hτ
      have hτinj : ∀ a i, Function.Injective (τ a i) := by
        intro a i p p' h
        simp only [hτ] at h
        by_cases hp : p < 2 ^ M <;> by_cases hp' : p' < 2 ^ M
        · simp only [hp, hp', ite_true] at h
          exact owenNode_inj _ i hp hp' h
        · simp only [hp, hp', ite_true, ite_false] at h
          have := owenNode_lt (ωa a) i M p
          omega
        · simp only [hp, hp', ite_true, ite_false] at h
          have := owenNode_lt (ωa a) i M p'
          omega
        · simp only [hp, hp', ite_false] at h
          exact h
      set c : (R → Bool) → Fin n × ℕ → Fin n × ℕ × ℕ := fun a t ↦ (t.1, M, τ a t.1 t.2) with hc
      have hcinj : ∀ a, Function.Injective (c a) := by
        rintro a ⟨t1, t2⟩ ⟨t1', t2'⟩ h
        simp only [hc, Prod.mk.injEq] at h
        obtain ⟨h1, -, h3⟩ := h
        subst h1
        rw [hτinj a _ h3]
      set Ga : (R → Bool) → Set (Fin n × ℕ × ℕ → Bool) := fun a ↦
        {ω | ∀ t ∈ (univ : Finset (Fin n)) ×ˢ range W, ω (c a t) = b (t.1, M, t.2)} with hGa
      have hGam : ∀ a, owenMeasure n (Ga a) = 2⁻¹ ^ (n * W) := by
        intro a
        have := coinMeasure_setOf_comp_eq (hcinj a) ((univ : Finset (Fin n)) ×ˢ range W)
          (fun t ↦ b (t.1, M, t.2))
        rw [card_product, card_univ, Fintype.card_fin, card_range] at this
        exact this
      have hpiece : ∀ a : R → Bool, (E ∩ G) ∩ R.restrict ⁻¹' ({a} : Set (R → Bool)) =
          if ωa a ∈ E then R.restrict ⁻¹' ({a} : Set (R → Bool)) ∩ Ga a else ∅ := by
        intro a
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨hωE, hωG⟩, hωa'⟩
          have hagree := hcell a ω hωa'
          have hE' : ωa a ∈ E := (hER ω (ωa a) hagree).1 hωE
          simp only [hE', ite_true, Set.mem_inter_iff, Set.mem_preimage]
          refine ⟨hωa', fun t ht ↦ ?_⟩
          have ht' := mem_product.1 ht
          have := hωG t.1 t.2 (mem_range.1 ht'.2)
          unfold owenRelabel at this
          simp only [hc, hτ]
          by_cases hp : t.2 < 2 ^ M
          · simp only [hp, ite_true] at this ⊢
            rw [← hNR ω (ωa a) hagree t.1 t.2]
            exact this
          · simp only [hp, ite_false] at this ⊢
            exact this
        · intro h
          by_cases hE' : ωa a ∈ E
          · simp only [hE', ite_true, Set.mem_inter_iff, Set.mem_preimage] at h
            obtain ⟨hωa', hGa'⟩ := h
            have hagree := hcell a ω hωa'
            refine ⟨⟨(hER ω (ωa a) hagree).2 hE', fun i p hp ↦ ?_⟩, hωa'⟩
            have := hGa' (i, p) (mem_product.2 ⟨mem_univ _, mem_range.2 hp⟩)
            simp only [hc, hτ] at this
            unfold owenRelabel
            by_cases hp' : p < 2 ^ M
            · simp only [hp', ite_true] at this ⊢
              rw [hNR ω (ωa a) hagree i p]
              exact this
            · simp only [hp', ite_false] at this ⊢
              exact this
          · simp only [hE', ite_false, Set.mem_empty_iff_false] at h
      have hEpiece : ∀ a : R → Bool, E ∩ R.restrict ⁻¹' ({a} : Set (R → Bool)) =
          if ωa a ∈ E then R.restrict ⁻¹' ({a} : Set (R → Bool)) else ∅ := by
        intro a
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hωE, hωa'⟩
          have hE' : ωa a ∈ E := (hER ω (ωa a) (hcell a ω hωa')).1 hωE
          simp only [hE', ite_true, Set.mem_preimage]
          exact hωa'
        · intro h
          by_cases hE' : ωa a ∈ E
          · simp only [hE', ite_true, Set.mem_preimage] at h
            exact ⟨(hER ω (ωa a) (hcell a ω h)).2 hE', h⟩
          · simp only [hE', ite_false, Set.mem_empty_iff_false] at h
      have hind : ∀ a : R → Bool, owenMeasure n (R.restrict ⁻¹' ({a} : Set (R → Bool)) ∩ Ga a) =
          owenMeasure n (R.restrict ⁻¹' ({a} : Set (R → Bool))) * owenMeasure n (Ga a) := by
        intro a
        refine infinitePi_inter_of_local (fun _ : Fin n × ℕ × ℕ ↦ fairCoin)
          (S := R) (T := ((univ : Finset (Fin n)) ×ˢ range W).image (c a)) ?_ ?_ ?_
        · intro ω ω' h
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          have e : R.restrict ω = R.restrict ω' := funext fun q ↦ h q q.2
          rw [e]
        · intro ω ω' h
          simp only [hGa, Set.mem_ofPred_eq]
          constructor
          · intro h' t ht
            rw [← h _ (mem_image_of_mem _ ht)]
            exact h' t ht
          · intro h' t ht
            rw [h _ (mem_image_of_mem _ ht)]
            exact h' t ht
        · refine Finset.disjoint_left.2 fun q hq hqT ↦ ?_
          obtain ⟨t, -, rfl⟩ := mem_image.1 hqT
          have := (mem_owenRect.1 hq).1
          simp only [hc] at this
          exact lt_irrefl M this
      change owenMeasure n _ = _
      rw [hsplit, measure_eq_sum_restrict_preimage (owenMeasure n) R (E ∩ G)]
      have hsum : ∀ a : R → Bool, owenMeasure n ((E ∩ G) ∩ R.restrict ⁻¹' ({a} : Set (R → Bool))) =
          owenMeasure n (E ∩ R.restrict ⁻¹' ({a} : Set (R → Bool))) * 2⁻¹ ^ (n * W) := by
        intro a
        rw [hpiece a, hEpiece a]
        by_cases hE' : ωa a ∈ E
        · simp only [hE', ite_true]
          rw [hind a, hGam a]
        · simp only [hE', ite_false, measure_empty, zero_mul]
      rw [sum_congr rfl fun a _ ↦ hsum a, ← sum_mul,
        ← measure_eq_sum_restrict_preimage (owenMeasure n) R E]
      change owenMeasure n {ω : Fin n × ℕ × ℕ → Bool |
        ∀ q ∈ owenRect n M W, owenRelabel ω q = b q} * _ = _
      rw [ih, ← pow_add]
      congr 1
      ring

/-- A probability measure on Owen's flips whose box cylinders all have probability
`2^{-|box|}` is `owenMeasure n`. -/
theorem eq_owenMeasure_of_box {μ : Measure (Fin n × ℕ × ℕ → Bool)} [IsProbabilityMeasure μ]
    (h : ∀ (b : Fin n × ℕ × ℕ → Bool) (M : ℕ),
      μ {ω | ∀ q ∈ owenBox n M, ω q = b q} = 2⁻¹ ^ (owenBox n M).card) :
    μ = owenMeasure n := by
  classical
  have hmap : ∀ M, μ.map (Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M)) =
      (owenMeasure n).map
        (Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M)) := by
    intro M
    refine Measure.ext_of_singleton fun g ↦ ?_
    rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g),
      Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g)]
    set b : Fin n × ℕ × ℕ → Bool := fun q ↦
      if hq : q ∈ owenBox n M then g ⟨q, hq⟩ else false with hb
    have e : Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M) ⁻¹'
        ({g} : Set ((owenBox n M) → Bool)) =
        {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl q hq
        simp only [hb, hq, dite_true, Finset.restrict]
      · intro hω
        funext q
        have := hω q.1 q.2
        simp only [hb, q.2, dite_true] at this
        exact this
    have ho := coinMeasure_setOf_comp_eq (ι := Fin n × ℕ × ℕ) (c := id)
      Function.injective_id (owenBox n M) b
    rw [e, h b M]
    exact ho.symm
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  set M := s.sup (fun q ↦ q.2.1 + q.2.2) + 1 with hM
  have hsS : ∀ q ∈ s, q ∈ owenBox n M := fun q hq ↦ by
    have hle : q.2.1 + q.2.2 ≤ s.sup (fun q ↦ q.2.1 + q.2.2) :=
      Finset.le_sup (f := fun q : Fin n × ℕ × ℕ ↦ q.2.1 + q.2.2) hq
    rw [owenBox_eq_owenRect]
    refine mem_owenRect.2 ⟨by omega, lt_of_lt_of_le (Nat.lt_two_pow_self) ?_⟩
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set E : Set ((owenBox n M) → Bool) := {g | ∀ q (hq : q ∈ s), g ⟨q, hsS q hq⟩ ∈ t q} with hE
  have hpre : Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M) ⁻¹' E =
      Set.pi (s : Set (Fin n × ℕ × ℕ)) t := by
    ext w
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, Set.mem_pi, mem_coe, Finset.restrict]
  have hEm : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← hpre, ← Measure.map_apply (Finset.measurable_restrict _) hEm, hmap M,
    Measure.map_apply (Finset.measurable_restrict _) hEm, hpre,
    Measure.infinitePi_pi _ fun q _ ↦ ht q]

/-- **The relabelling by the scrambled tree preserves Owen's measure**: the relabelled flips
`ω (i, m, σ_m⁻¹ p)` are again i.i.d. fair coins. -/
theorem measurePreserving_owenRelabel :
    MeasurePreserving (owenRelabel (n := n)) (owenMeasure n) (owenMeasure n) := by
  classical
  refine ⟨measurable_owenRelabel, ?_⟩
  refine eq_owenMeasure_of_box fun b M ↦ ?_
  have hm : MeasurableSet {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} := by
    have e : {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} =
        Set.pi ((owenBox n M : Finset (Fin n × ℕ × ℕ)) : Set (Fin n × ℕ × ℕ))
          fun q ↦ ({b q} : Set Bool) := by
      ext ω
      simp [Set.mem_pi]
    rw [e]
    exact MeasurableSet.pi (Set.to_countable _) fun _ _ ↦ measurableSet_singleton _
  rw [Measure.map_apply measurable_owenRelabel hm]
  have e : owenRelabel ⁻¹' {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} =
      {ω | ∀ q ∈ owenRect n M (2 ^ M), owenRelabel ω q = b q} := by
    ext ω
    rfl
  rw [e, owenMeasure_relabel_rect, owenBox_eq_owenRect, owenRect, card_product, card_product,
    card_univ, Fintype.card_fin, card_range, card_range, mul_assoc]

end RQMCMarkov.ScrambledStacks
