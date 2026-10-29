/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.Cycles

/-!
# The chain `Φ_d` on a cycle class is aperiodic (MT Proposition 5.4.6)

Meyn and Tweedie, Proposition 5.4.6, p. 115: if `Φ` has period `d` and `d`-cycle `{Dᵢ}`, then
`Φ_d` (kernel `Pᵈ`) on each `Dᵢ` is aperiodic. The first half of the proposition (each `Dᵢ` is an
absorbing `ψ`-irreducible set for `Pᵈ`) is `proposition_5_4_6` in `Cycles`.

A cycle of `Pᵈ` on `Dᵢ` is a family `E_b ⊆ Dᵢ`, `b ∈ ZMod d'`, of disjoint measurable sets with
`Pᵈ(x, E_{b+1}) = 1` on `E_b` and `ψ(Dᵢ \ ⋃ E_b) = 0`. The book proves aperiodicity by "the
definition of `d` as the largest value for which a cycle exists"; the proof here makes that
explicit by building a `dd'`-cycle of `Φ` from such a family:
`F_{l + d b} = E_b` for `l = 0` and `F_{l + d b} = {x ∈ D_{i+l} : P^{d−l}(x, E_{b+1}) = 1}` for
`0 < l < d`.

* `measure_setOf_eq_one`: if `∫ f dμ = 1` for a probability `μ` and `f ≤ 1`, then `f = 1`
  `μ`-a.s.
* `IsCycle.measure_pos`: for a maximal irreducibility measure every class of a cycle is in
  `B⁺(X)`.
* `zmod_phase_succ`, `zmod_phase_inj`, `zmod_phase_exists`: the decomposition
  `j = l + d b` of `j ∈ ZMod (d d')`.
* `isCycle_liftClass`: the lifted family is a `dd'`-cycle of `Φ`.
* **Proposition 5.4.6**, aperiodicity (`proposition_5_4_6_aperiodic`): every such family has
  `d' = 1`.

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- If `∫ f dμ = 1` for a probability measure `μ` and `f ≤ 1`, then `μ{f = 1} = 1`. -/
theorem measure_setOf_eq_one {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) (h : ∫⁻ x, f x ∂μ = 1) : μ {x | f x = 1} = 1 := by
  have h0 : ∫⁻ x, (1 - f x) ∂μ = 0 := by
    have := lintegral_sub (μ := μ) (f := fun _ => (1 : ℝ≥0∞)) (g := f) hf
      (by rw [h]; exact ENNReal.one_ne_top) (Filter.Eventually.of_forall hf1)
    rw [this, h, lintegral_const, measure_univ, one_mul, tsub_self]
  rw [lintegral_eq_zero_iff (f := fun x => 1 - f x) (measurable_const.sub hf)] at h0
  have hae : ∀ᵐ x ∂μ, f x = 1 := h0.mono fun x hx => le_antisymm (hf1 x)
    (by simpa [tsub_eq_zero_iff_le] using hx)
  rw [← prob_compl_eq_zero_iff (measurableSet_eq_fun hf measurable_const)]
  exact measure_eq_zero_iff_ae_notMem.2 (hae.mono fun x hx h' => h' hx)

/-- For a maximal irreducibility measure, every class of a cycle has positive measure. -/
theorem IsCycle.measure_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {d : ℕ} (hd : 0 < d) {D : ZMod d → Set X}
    (h : IsCycle P ψ d D) (i : ZMod d) : 0 < ψ (D i) := by
  have : NeZero d := ⟨hd.ne'⟩
  by_contra h0
  push Not at h0
  -- the class before a null class is null
  have hback : ∀ j, ψ (D (j + 1)) = 0 → ψ (D j) = 0 := fun j hj => by
    refine measure_mono_null (fun x hx => ?_) (hψ.hitSet_null (h.measurableSet _) hj)
    have h1 := h.step j x hx
    have h2 := pow_le_hitProb P (h.measurableSet (j + 1)) 0 x
    rw [zero_add, pow_one, h1] at h2
    exact one_pos.trans_le h2
  have hall : ∀ n : ℕ, ψ (D (i - n)) = 0 := fun n => by
    induction n with
    | zero => simpa using nonpos_iff_eq_zero.1 h0
    | succ n ih =>
      refine hback _ ?_
      rwa [show i - ((n + 1 : ℕ) : ZMod d) + 1 = i - n by push_cast; ring]
  have hnull : ∀ j, ψ (D j) = 0 := fun j => by
    have := hall (i - j).val
    rwa [ZMod.natCast_zmod_val, sub_sub_cancel] at this
  apply hψ.1
  rw [← Measure.measure_univ_eq_zero]
  refine measure_mono_null (fun x _ => ?_) (measure_union_null (measure_iUnion_null hnull)
    h.null_compl)
  by_cases hx : x ∈ ⋃ j, D j
  · exact Or.inl hx
  · exact Or.inr hx

/-! ### The phase decomposition of `ZMod (d d')` -/

omit [MeasurableSpace X] in
/-- One step in `ZMod (d d')` in terms of the decomposition `j = l + d b`, `l = j mod d`: if
`l + 1 < d` the phase becomes `l + 1` with the same `b`; otherwise it becomes `0` and `b`
increases by one (mod `d'`). -/
theorem zmod_phase_succ {d d' : ℕ} (hd : 0 < d) (hd' : 2 ≤ d') [NeZero (d * d')]
    (j : ZMod (d * d')) :
    (j.val % d + 1 < d → (j + 1).val % d = j.val % d + 1 ∧
      (((j + 1).val / d : ℕ) : ZMod d') = ((j.val / d : ℕ) : ZMod d')) ∧
    (¬ (j.val % d + 1 < d) → (j + 1).val % d = 0 ∧
      (((j + 1).val / d : ℕ) : ZMod d') = ((j.val / d : ℕ) : ZMod d') + 1) := by
  have hN1 : d * d' ≠ 1 := by nlinarith
  have hval : (j + 1).val = (j.val + 1) % (d * d') := by
    rw [ZMod.val_add, ZMod.val_one'' hN1]
  set v := j.val with hv
  have hvlt : v < d * d' := ZMod.val_lt j
  set l := v % d
  set q := v / d
  have hdecomp : d * q + l = v := Nat.div_add_mod v d
  have hl : l < d := Nat.mod_lt v hd
  have hq : q < d' := (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; exact hvlt)
  have hmul : d * (q + 1) ≤ d * d' := Nat.mul_le_mul_left d hq
  have hmul' : d * (q + 1) = d * q + d := by ring
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlt : v + 1 < d * d' := by omega
    rw [hval, Nat.mod_eq_of_lt hlt]
    have hrw : v + 1 = (l + 1) + d * q := by omega
    rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt h, zero_add]
    exact ⟨rfl, rfl⟩
  · have hl1 : l + 1 = d := by omega
    have hrw : v + 1 = 0 + d * (q + 1) := by omega
    rcases Nat.lt_or_ge (q + 1) d' with hq1 | hq1
    · have hlt : v + 1 < d * d' := by
        have := Nat.mul_lt_mul_of_pos_left hq1 hd
        omega
      rw [hval, Nat.mod_eq_of_lt hlt, hrw, Nat.add_mul_mod_self_left, Nat.zero_mod,
        Nat.add_mul_div_left _ _ hd, Nat.zero_div, zero_add]
      exact ⟨rfl, by push_cast; rfl⟩
    · have hq1' : q + 1 = d' := by omega
      have heq : v + 1 = d * d' := by rw [← hq1']; omega
      rw [hval, heq, Nat.mod_self, Nat.zero_mod, Nat.zero_div]
      refine ⟨rfl, ?_⟩
      rw [Nat.cast_zero, show ((q : ℕ) : ZMod d') + 1 = ((q + 1 : ℕ) : ZMod d') by push_cast; ring,
        hq1', ZMod.natCast_self]

omit [MeasurableSpace X] in
/-- The decomposition `j = l + d b` determines `j`. -/
theorem zmod_phase_inj {d d' : ℕ} (hd : 0 < d) [NeZero (d * d')] {j j' : ZMod (d * d')}
    (hl : j.val % d = j'.val % d)
    (hb : ((j.val / d : ℕ) : ZMod d') = ((j'.val / d : ℕ) : ZMod d')) : j = j' := by
  have hq : ∀ k : ZMod (d * d'), k.val / d < d' := fun k =>
    (Nat.div_lt_iff_lt_mul hd).2 ((ZMod.val_lt k).trans_eq (mul_comm d d'))
  have hb' : j.val / d = j'.val / d := by
    have := congrArg ZMod.val hb
    rwa [ZMod.val_cast_of_lt (hq j), ZMod.val_cast_of_lt (hq j')] at this
  refine ZMod.val_injective _ ?_
  rw [← Nat.div_add_mod j.val d, ← Nat.div_add_mod j'.val d, hl, hb']

omit [MeasurableSpace X] in
/-- Every phase `(l, b)` with `l < d` occurs. -/
theorem zmod_phase_exists {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d') [NeZero (d * d')] {l : ℕ}
    (hl : l < d) (b : ZMod d') :
    ∃ j : ZMod (d * d'), j.val % d = l ∧ ((j.val / d : ℕ) : ZMod d') = b := by
  have : NeZero d' := ⟨hd'.ne'⟩
  have hb : b.val < d' := ZMod.val_lt b
  have hlt : l + d * b.val < d * d' := by
    have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hb)
    rw [Nat.mul_succ] at this
    omega
  refine ⟨((l + d * b.val : ℕ) : ZMod (d * d')), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt hlt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [ZMod.val_cast_of_lt hlt, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hl, zero_add,
      ZMod.natCast_zmod_val]

/-! ### Lifting a cycle of `Pᵈ` on `Dᵢ` to a cycle of `P` -/

/-- The set `G_{l, b} = {x ∈ D_{i+l} : P^{d−l}(x, E_{b+1}) = 1}`. -/
def liftPiece (P : Kernel X X) {d d' : ℕ} (D : ZMod d → Set X) (i : ZMod d)
    (E : ZMod d' → Set X) (l : ℕ) (b : ZMod d') : Set X :=
  {x | x ∈ D (i + (l : ZMod d)) ∧ (P ^ (d - l)) x (E (b + 1)) = 1}

/-- The class `F_j`, `j = l + d b`, of the lifted cycle: `E_b` if `l = 0`, `G_{l, b}`
otherwise. -/
noncomputable def liftClass (P : Kernel X X) {d d' : ℕ} (D : ZMod d → Set X) (i : ZMod d)
    (E : ZMod d' → Set X) (j : ZMod (d * d')) : Set X := by
  classical
  exact if j.val % d = 0 then E ((j.val / d : ℕ) : ZMod d')
    else liftPiece P D i E (j.val % d) ((j.val / d : ℕ) : ZMod d')

/-- Two probability-one events have a probability-one intersection. -/
theorem prob_inter_eq_one {μ : Measure X} [IsProbabilityMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (h1 : μ A = 1) (h2 : μ B = 1) :
    μ (A ∩ B) = 1 := by
  rw [← prob_compl_eq_zero_iff (hA.inter hB), compl_inter]
  exact measure_union_null ((prob_compl_eq_zero_iff hA).2 h1) ((prob_compl_eq_zero_iff hB).2 h2)

variable {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d d' : ℕ}
  {D : ZMod d → Set X} {i : ZMod d} {E : ZMod d' → Set X}

omit [IsMarkovKernel P] in
/-- A state of `F_j`, `j = l + d b`, lies in `D_{i+l}` and enters `E_{b+1}` with probability one
after `d − l` steps. -/
theorem mem_liftClass {j : ZMod (d * d')} (hEsub : ∀ b, E b ⊆ D i)
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) {x : X}
    (hx : x ∈ liftClass P D i E j) :
    x ∈ D (i + ((j.val % d : ℕ) : ZMod d)) ∧
      (P ^ (d - j.val % d)) x (E (((j.val / d : ℕ) : ZMod d') + 1)) = 1 := by
  unfold liftClass at hx
  split_ifs at hx with h
  · rw [h, Nat.cast_zero, add_zero, Nat.sub_zero]
    exact ⟨hEsub _ hx, hEstep _ x hx⟩
  · exact hx

/-- The key estimate: for `l < d`, the states of `D_{i+l}` that enter no `E_{b+1}` with
probability one after `d − l` steps form a `ψ`-null set. -/
theorem measure_liftPiece_compl (hψ : IsMaximalIrreducibility P ψ) (hd : 0 < d)
    (hD : IsCycle P ψ d D) (hEm : ∀ b, MeasurableSet (E b)) (hEsub : ∀ b, E b ⊆ D i)
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) (hEnull : ψ (D i \ ⋃ b, E b) = 0)
    (hd' : 0 < d') {l : ℕ} (hld : l < d) :
    ψ (D (i + (l : ZMod d)) \ ⋃ b, liftPiece P D i E l b) = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero d' := ⟨hd'.ne'⟩
  have hGm : ∀ b, MeasurableSet (liftPiece P D i E l b) := fun b =>
    (hD.measurableSet _).inter (measurableSet_eq_fun (Kernel.measurable_coe _ (hEm _))
      measurable_const)
  set B := D (i + (l : ZMod d)) \ ⋃ b, liftPiece P D i E l b with hBdef
  have hBm : MeasurableSet B := (hD.measurableSet _).diff (MeasurableSet.iUnion hGm)
  by_contra hpos
  -- a state of some `E_{b₀}`
  have hψE : 0 < ψ (⋃ b, E b) := by
    have h1 := hD.measure_pos hψ hd i
    have h2 : ψ (D i) ≤ ψ (D i \ ⋃ b, E b) + ψ (⋃ b, E b) := by
      calc ψ (D i) ≤ ψ ((D i \ ⋃ b, E b) ∪ ⋃ b, E b) := measure_mono fun x hx => by
            by_cases h : x ∈ ⋃ b, E b
            · exact Or.inr h
            · exact Or.inl ⟨hx, h⟩
        _ ≤ _ := measure_union_le _ _
    rw [hEnull, zero_add] at h2
    exact h1.trans_le h2
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hψE.ne'
  obtain ⟨b₀, hyb⟩ := mem_iUnion.1 hy
  -- `y` reaches `B` at some time `n + 1 ≡ l (mod d)`
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hBm y).1 (hψ.2.1 B hBm (pos_iff_ne_zero.2 hpos) y)
  have hcast : ((n + 1 : ℕ) : ZMod d) = (l : ZMod d) := by
    by_contra hne
    have h0 := hD.pow_apply_eq_zero (n + 1) (hEsub b₀ hyb) (j := i + (l : ZMod d))
      (fun h => hne (by linear_combination -h))
    exact hn.ne' (measure_mono_null sdiff_subset h0)
  have hmod : (n + 1) % d = l := by
    have := (ZMod.natCast_eq_natCast_iff' (n + 1) l d).1 hcast
    rwa [Nat.mod_eq_of_lt hld] at this
  set s := (n + 1) / d
  have hns : n + 1 = d * s + l := by rw [← hmod]; exact (Nat.div_add_mod (n + 1) d).symm
  -- after `d s` steps the chain is in `E_{b₀+s}`, from which `B` is not reached in `l` steps
  have hEs : (P ^ (d * s)) y (E (b₀ + s)) = 1 := by
    have := isMarkovKernel_pow P d
    rw [pow_mul]
    exact pow_apply_eq_one_of_step (P ^ d) hEm hEstep s b₀ y hyb
  have hzero : ∀ z ∈ E (b₀ + s), (P ^ l) z B = 0 := fun z hz => by
    have := isMarkovKernel_pow P l
    have h1 : (P ^ l) z {w | (P ^ (d - l)) w (E (b₀ + s + 1)) = 1} = 1 := by
      have h2 := hEstep _ z hz
      rw [show d = l + (d - l) by omega, Kernel.pow_add_apply_eq_lintegral P l (d - l) z
        (hEm _)] at h2
      exact measure_setOf_eq_one (Kernel.measurable_coe _ (hEm _))
        (fun w => by have := isMarkovKernel_pow P (d - l); exact prob_le_one) h2
    have h3 := hD.pow_apply l (hEsub _ hz)
    have h4 := prob_inter_eq_one (hD.measurableSet _) (measurableSet_eq_fun
      (Kernel.measurable_coe _ (hEm _)) measurable_const) h3 h1
    rw [← prob_compl_eq_zero_iff ((hD.measurableSet _).inter (measurableSet_eq_fun
      (Kernel.measurable_coe _ (hEm _)) measurable_const))] at h4
    refine measure_mono_null (show B ⊆ (D (i + (l : ZMod d)) ∩
      {w | (P ^ (d - l)) w (E (b₀ + s + 1)) = 1})ᶜ from
        fun w hw hw' => hw.2 (mem_iUnion.2 ⟨b₀ + s, hw'⟩)) h4
  have := isMarkovKernel_pow P (d * s)
  rw [hns, Kernel.pow_add_apply_eq_lintegral P (d * s) l y hBm] at hn
  have hae : ∀ᵐ z ∂(P ^ (d * s)) y, z ∈ E (b₀ + s) :=
    mem_ae_iff.2 ((prob_compl_eq_zero_iff (hEm (b₀ + s))).2 hEs)
  have h0 : ∫⁻ z, (P ^ l) z B ∂(P ^ (d * s)) y = 0 := by
    rw [lintegral_congr_ae (hae.mono fun z hz => hzero z hz), lintegral_zero]
  exact hn.ne' h0

/-- The lifted family `F_{l + d b}` is a `dd'`-cycle of `Φ`. -/
theorem isCycle_liftClass (hψ : IsMaximalIrreducibility P ψ) (hd : 0 < d)
    (hD : IsCycle P ψ d D) (hd' : 2 ≤ d') [NeZero (d * d')] (hEm : ∀ b, MeasurableSet (E b))
    (hEsub : ∀ b, E b ⊆ D i) (hEdisj : ∀ b c, b ≠ c → Disjoint (E b) (E c))
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) (hEnull : ψ (D i \ ⋃ b, E b) = 0) :
    IsCycle P ψ (d * d') (liftClass P D i E) := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero d' := ⟨by omega⟩
  have hGm : ∀ l b, MeasurableSet (liftPiece P D i E l b) := fun l b =>
    (hD.measurableSet _).inter (measurableSet_eq_fun (Kernel.measurable_coe _ (hEm _))
      measurable_const)
  -- the casts `l ↦ (l : ZMod d)` are injective below `d`
  have hcastinj : ∀ l l' : ℕ, l < d → l' < d → (l : ZMod d) = (l' : ZMod d) → l = l' :=
    fun l l' hl hl' h => by
      have := congrArg ZMod.val h
      rwa [ZMod.val_cast_of_lt hl, ZMod.val_cast_of_lt hl'] at this
  refine ⟨fun j => ?_, fun j j' hjj' => ?_, fun j x hx => ?_, ?_⟩
  · unfold liftClass
    split_ifs
    · exact hEm _
    · exact hGm _ _
  · refine Set.disjoint_left.2 fun x hx hx' => hjj' ?_
    obtain ⟨h1, h2⟩ := mem_liftClass hEsub hEstep hx
    obtain ⟨h1', h2'⟩ := mem_liftClass hEsub hEstep hx'
    have hl : j.val % d = j'.val % d := by
      by_contra hne
      refine Set.disjoint_left.1 (hD.disjoint _ _ fun h => hne (hcastinj _ _
        (Nat.mod_lt _ hd) (Nat.mod_lt _ hd) (add_left_cancel h))) h1 h1'
    refine zmod_phase_inj hd hl ?_
    by_contra hne
    rw [hl] at h2
    have := isMarkovKernel_pow P (d - j'.val % d)
    have hdisj : Disjoint (E (((j.val / d : ℕ) : ZMod d') + 1))
        (E (((j'.val / d : ℕ) : ZMod d') + 1)) :=
      hEdisj _ _ fun h => hne (add_right_cancel h)
    have hsum := measure_union (μ := (P ^ (d - j'.val % d)) x) hdisj (hEm _)
    rw [h2, h2'] at hsum
    have hle := prob_le_one (μ := (P ^ (d - j'.val % d)) x)
      (s := E (((j.val / d : ℕ) : ZMod d') + 1) ∪ E (((j'.val / d : ℕ) : ZMod d') + 1))
    rw [hsum] at hle
    norm_num at hle
  · -- the step `F_j → F_{j+1}`
    obtain ⟨h1, h2⟩ := mem_liftClass hEsub hEstep hx
    obtain ⟨hlt, hge⟩ := zmod_phase_succ hd hd' j
    by_cases hc : j.val % d + 1 < d
    · obtain ⟨e1, e2⟩ := hlt hc
      have hF : liftClass P D i E (j + 1) =
          liftPiece P D i E (j.val % d + 1) ((j.val / d : ℕ) : ZMod d') := by
        unfold liftClass
        simp only [e1, e2, Nat.add_one_ne_zero, ite_false]
      rw [hF]
      have hD1 := hD.step _ x h1
      have hreach : P x {y | (P ^ (d - (j.val % d + 1))) y
          (E (((j.val / d : ℕ) : ZMod d') + 1)) = 1} = 1 := by
        rw [show d - j.val % d = 1 + (d - (j.val % d + 1)) by omega,
          Kernel.pow_add_apply_eq_lintegral P 1 _ x (hEm _), pow_one] at h2
        exact measure_setOf_eq_one (Kernel.measurable_coe _ (hEm _))
          (fun y => by have := isMarkovKernel_pow P (d - (j.val % d + 1)); exact prob_le_one) h2
      have := prob_inter_eq_one (hD.measurableSet _) (measurableSet_eq_fun
        (Kernel.measurable_coe _ (hEm _)) measurable_const) hD1 hreach
      have hidx : i + ((j.val % d + 1 : ℕ) : ZMod d) = i + ((j.val % d : ℕ) : ZMod d) + 1 := by
        push_cast; ring
      unfold liftPiece
      rw [hidx]
      exact this
    · obtain ⟨e1, e2⟩ := hge hc
      have hF : liftClass P D i E (j + 1) = E (((j.val / d : ℕ) : ZMod d') + 1) := by
        unfold liftClass
        simp only [e1, e2, ite_true]
      rw [hF]
      have hd1 : d - j.val % d = 1 := by have := Nat.mod_lt j.val hd; omega
      rw [hd1, pow_one] at h2
      exact h2
  · -- the complement of the union is `ψ`-null
    have hcov : (⋃ j, liftClass P D i E j)ᶜ ⊆ (⋃ m, D m)ᶜ ∪ (D i \ ⋃ b, E b) ∪
        ⋃ l : Fin d, (D (i + ((l : ℕ) : ZMod d)) \ ⋃ b, liftPiece P D i E l b) := by
      intro x hx
      by_cases hU : x ∈ ⋃ m, D m
      · obtain ⟨m, hm⟩ := mem_iUnion.1 hU
        set l := (m - i).val with hl
        have hld : l < d := ZMod.val_lt _
        have hm' : m = i + (l : ZMod d) := by rw [hl, ZMod.natCast_zmod_val]; ring
        rw [hm'] at hm
        by_cases hl0 : l = 0
        · refine Or.inl (Or.inr ⟨by simpa [hl0] using hm, fun hE => hx ?_⟩)
          obtain ⟨b, hb⟩ := mem_iUnion.1 hE
          obtain ⟨j, hj1, hj2⟩ := zmod_phase_exists hd (by omega) (l := 0) hd b
          refine mem_iUnion.2 ⟨j, ?_⟩
          unfold liftClass
          simp only [hj1, hj2, ite_true]
          exact hb
        · refine Or.inr (mem_iUnion.2 ⟨⟨l, hld⟩, hm, fun hG => hx ?_⟩)
          obtain ⟨b, hb⟩ := mem_iUnion.1 hG
          obtain ⟨j, hj1, hj2⟩ := zmod_phase_exists hd (by omega) hld b
          refine mem_iUnion.2 ⟨j, ?_⟩
          unfold liftClass
          simp only [hj1, hj2, hl0, ite_false]
          exact hb
      · exact Or.inl (Or.inl hU)
    refine measure_mono_null hcov (measure_union_null (measure_union_null hD.null_compl
      hEnull) (measure_iUnion_null fun l => ?_))
    exact measure_liftPiece_compl hψ hd hD hEm hEsub hEstep hEnull (by omega) l.2

/-- **Proposition 5.4.6**, aperiodicity (MT p. 115). Let `Φ` have period `d` and `d`-cycle `{Dᵢ}`.
Then `Φ_d` on `Dᵢ` is aperiodic: every cycle `E_b ⊆ Dᵢ`, `b ∈ ZMod d'`, of `Pᵈ` (disjoint
measurable sets with `Pᵈ(x, E_{b+1}) = 1` on `E_b` and `ψ(Dᵢ \ ⋃ E_b) = 0`) has `d' = 1`. -/
theorem proposition_5_4_6_aperiodic (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {d : ℕ} (hper : IsPeriod P ψ d) {D : ZMod d → Set X}
    (hD : IsCycle P ψ d D) (i : ZMod d) {d' : ℕ} (hd' : 0 < d') {E : ZMod d' → Set X}
    (hEm : ∀ b, MeasurableSet (E b)) (hEsub : ∀ b, E b ⊆ D i)
    (hEdisj : ∀ b c, b ≠ c → Disjoint (E b) (E c))
    (hEstep : ∀ b, ∀ x ∈ E b, (P ^ d) x (E (b + 1)) = 1) (hEnull : ψ (D i \ ⋃ b, E b) = 0) :
    d' = 1 := by
  obtain ⟨hd, -, hmax⟩ := hper
  by_contra hne
  have hd'2 : 2 ≤ d' := by omega
  have : NeZero (d * d') := ⟨by positivity⟩
  have h := isCycle_liftClass hψ hd hD hd'2 hEm hEsub hEdisj hEstep hEnull
  have := hmax (d * d') _ (by positivity) h
  have : d * d' ≤ d * 1 := by rwa [mul_one]
  have := Nat.le_of_mul_le_mul_left this hd
  omega

end MeynTweedie.GeneralizedDrift
