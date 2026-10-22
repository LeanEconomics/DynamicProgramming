/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.LinkedRenewal
import Ergodicity.PeriodicErgodic

/-!
# The coupling time of two renewal processes (MT Proposition 13.2.1)

Meyn and Tweedie, Proposition 13.2.1, p. 321: for an aperiodic increment law `p` with finite mean
and any delay distributions `a`, `b`, the coupling time `T_ab` (the first common renewal of the two
delayed renewal processes) is almost surely finite. In terms of the linked forward recurrence
time chain `V* = V⁺ ∥ V⁺` of (10.19), a common renewal at time `n` is a visit of `V*` to `(0, 0)`,
and the two delayed processes are `V*` started from `a ⊗ b`.

**Escape probabilities** (any chain, any measurable `A`).
* `tendsto_tabooKernel_univ_sub`: `_APⁿ⁺¹(x, X) → 1 − L(x, A) = P_x(τ_A = ∞)`;
* `one_sub_hitProb_le_lintegral`: `P_x(τ_A = ∞) ≤ ∫ Pᵗ(x, dw) P_w(τ_A = ∞)`;
* `mul_one_sub_hitProb_le`: `_APᵏ⁺¹(x, {y}) P_y(τ_A = ∞) ≤ P_x(τ_A = ∞)` for `y ∉ A`.

**The forward recurrence chain.** `fwdRecSupport p = {r : Σ_{n > r} p(n) > 0}` is absorbing and
contains `0`, so `Pᵗ(i, ·)` is carried by it for `t ≥ i` (`fwdRec_pow_compl_support`).

**Result.**
* **Proposition 13.2.1** (`proposition_13_2_1`): `V*` reaches `(0, 0)` almost surely from every
  state (`linked_hitProb_eq_one`), hence from every initial law, in particular from `a ⊗ b`:
  `P(T_ab < ∞) = 1`. The proof is the book's: `V*` is positive and reaches `(0, 0)` from every
  state; states charged by the invariant probability `π*` are recurrent states of the class of
  `(0, 0)`; every state enters that class after finitely many steps.

**Not formalised.** The coupling identity (13.32)–(13.33) for general delays, which constructs the
coupled process `Z_ab` on a common probability space: the renewal theorems it proves are obtained
analytically (`theorem_13_2_2`), and its special case `a = δ₀`, `b = δ₁` is
`abs_sub_realRenewalSeq_le` in `LinkedRenewal`.

**Corrections.** None.
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

/-! ### Escape probabilities -/

variable {X : Type*} [MeasurableSpace X]

/-- `_APⁿ⁺¹(x, X) → 1 − L(x, A)`. -/
theorem tendsto_tabooKernel_univ_sub (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    Tendsto (fun n => tabooKernel P hA n x univ) atTop (𝓝 (1 - hitProb P A x)) := by
  have hadd : ∀ n, tabooKernel P hA n x univ = 1 - ∑ j ∈ range n, tabooKernel P hA j x A :=
    fun n => by
      have h := tabooSeq_univ_add_sum P hA (Measure.dirac x) n
      simp only [tabooSeq, dirac_kernel, measure_univ] at h
      exact ENNReal.eq_sub_of_add_eq (ENNReal.sum_ne_top.2 fun j _ =>
        ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hA j x A)) h
  simp_rw [hadd]
  have hs : Tendsto (fun n => ∑ j ∈ range n, tabooKernel P hA j x A) atTop
      (𝓝 (hitProb P A x)) := by
    rw [hitProb_eq_tsum P hA x]
    exact ENNReal.tendsto_nat_tsum _
  exact ENNReal.Tendsto.sub tendsto_const_nhds hs (Or.inl ENNReal.one_ne_top)

/-- `(P I_{Aᶜ})ᵗ(x, ·) ≤ Pᵗ(x, ·)`. -/
theorem indComp_pow_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (t : ℕ) : ∀ x, ((indKernel hA.compl ∘ₖ P) ^ t : Kernel X X) x ≤ (P ^ t : Kernel X X) x := by
  induction t with
  | zero => intro x; rw [pow_zero_apply, pow_zero_apply]
  | succ t ih =>
    intro x
    rw [pow_succ, pow_succ]
    change (((indKernel hA.compl ∘ₖ P) ^ t : Kernel X X) ∘ₖ (indKernel hA.compl ∘ₖ P)) x ≤
      ((P ^ t : Kernel X X) ∘ₖ P) x
    rw [Kernel.comp_apply, comp_indKernel_eq_restrict, Kernel.comp_apply]
    refine Measure.le_intro fun B hB _ => ?_
    rw [measure_kernel_apply _ _ hB, measure_kernel_apply _ _ hB]
    calc ∫⁻ y, ((indKernel hA.compl ∘ₖ P) ^ t : Kernel X X) y B ∂(P x).restrict Aᶜ
        ≤ ∫⁻ y, ((indKernel hA.compl ∘ₖ P) ^ t : Kernel X X) y B ∂P x :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ ∫⁻ y, (P ^ t : Kernel X X) y B ∂P x := lintegral_mono fun y => ih y B

/-- `_APⁿ⁺ᵗ⁺¹ = _APⁿ⁺¹ ∘ (P I_{Aᶜ})ᵗ`. -/
theorem tabooKernel_add_eq_comp (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n t : ℕ) :
    tabooKernel P hA (n + t) = tabooKernel P hA n ∘ₖ ((indKernel hA.compl ∘ₖ P) ^ t) := by
  unfold tabooKernel
  rw [add_comm n t, pow_add_eq _ t n]
  simp only [Kernel.comp_assoc]

/-- `P_x(τ_A = ∞) ≤ ∫ Pᵗ(x, dw) P_w(τ_A = ∞)`. -/
theorem one_sub_hitProb_le_lintegral (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (t : ℕ) (x : X) :
    1 - hitProb P A x ≤ ∫⁻ w, (1 - hitProb P A w) ∂(P ^ t : Kernel X X) x := by
  have := isMarkovKernel_pow P t
  have h1 := (tendsto_tabooKernel_univ_sub P hA x).comp (tendsto_add_atTop_nat t)
  have h2 : Tendsto (fun n => ∫⁻ w, tabooKernel P hA n w univ ∂(P ^ t : Kernel X X) x) atTop
      (𝓝 (∫⁻ w, (1 - hitProb P A w) ∂(P ^ t : Kernel X X) x)) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun n => Kernel.measurable_coe _ MeasurableSet.univ)
      (fun n => Eventually.of_forall fun w => tabooKernel_apply_le_one P hA n w univ)
      (by rw [lintegral_one, measure_univ]; exact ENNReal.one_ne_top)
      (Eventually.of_forall fun w => tendsto_tabooKernel_univ_sub P hA w)
  refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
  simp only [Function.comp_apply]
  rw [tabooKernel_add_eq_comp, Kernel.comp_apply, measure_kernel_apply _ _ MeasurableSet.univ]
  exact lintegral_mono' (indComp_pow_le P hA t x) le_rfl

/-- `_APᵏ⁺¹(x, {y}) P_y(τ_A = ∞) ≤ P_x(τ_A = ∞)` for `y ∉ A`. -/
theorem mul_one_sub_hitProb_le [MeasurableSingletonClass X] (P : Kernel X X) [IsMarkovKernel P]
    {A : Set X} (hA : MeasurableSet A) (k : ℕ) (x : X) {y : X} (hy : y ∉ A) :
    tabooKernel P hA k x {y} * (1 - hitProb P A y) ≤ 1 - hitProb P A x := by
  have h1 := (tendsto_tabooKernel_univ_sub P hA x).comp (tendsto_add_atTop_nat (k + 1))
  have h2 := ENNReal.Tendsto.const_mul (a := tabooKernel P hA k x {y})
    (tendsto_tabooKernel_univ_sub P hA y)
    (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hA k x {y})))
  refine le_of_tendsto_of_tendsto' h2 h1 fun n => ?_
  simp only [Function.comp_apply]
  rw [tabooKernel_add_succ P hA k n x, measure_kernel_apply _ _ MeasurableSet.univ]
  calc tabooKernel P hA k x {y} * tabooKernel P hA n y univ
      = ∫⁻ w in {y}, tabooKernel P hA n w univ ∂tabooKernel P hA k x := by
        rw [lintegral_singleton, mul_comm]
    _ ≤ ∫⁻ w in Aᶜ, tabooKernel P hA n w univ ∂tabooKernel P hA k x :=
        lintegral_mono_set (singleton_subset_iff.2 hy)
    _ = ∫⁻ w, tabooKernel P hA n w univ ∂(tabooKernel P hA k x).restrict Aᶜ := rfl

/-! ### The support of the forward recurrence chain -/

/-- `{r : Σ_{n > r} p(n) > 0}`, the states of the forward recurrence chain charged by `π`. -/
def fwdRecSupport (p : ℕ → ℝ) : Set ℕ := {r | 0 < lawMeasure p {n | r < n}}

/-- The support is absorbing. -/
theorem fwdRecSupport_absorbing {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    ∀ r ∈ fwdRecSupport p, fwdRecKernel (lawMeasure p) r (fwdRecSupport p)ᶜ = 0 := by
  have := isProbabilityMeasure_lawMeasure hp
  intro r hr
  rcases r with _ | r
  · change fwdRecMeas (lawMeasure p) 0 _ = 0
    simp only [fwdRecMeas, ite_true]
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    set S := (fun n : ℕ => n - 1) ⁻¹' (fwdRecSupport p)ᶜ
    have hS : S = ⋃ n ∈ S, ({n} : Set ℕ) := (biUnion_of_singleton S).symm
    rw [hS, measure_biUnion_null_iff (Set.to_countable S)]
    intro n hn
    have h0 : lawMeasure p {m | n - 1 < m} = 0 := by
      have : ¬ (0 < lawMeasure p {m | n - 1 < m}) := hn
      exact nonpos_iff_eq_zero.1 (not_lt.1 this)
    rcases n with _ | n
    · exact lawMeasure_zero hp
    · exact nonpos_iff_eq_zero.1 ((measure_mono (singleton_subset_iff.2
        (show n + 1 - 1 < n + 1 by omega))).trans h0.le)
  · rw [fwdRec_succ, Measure.dirac_apply' _ (Set.to_countable _).measurableSet.compl,
      indicator_of_notMem]
    simp only [mem_compl_iff, not_not, fwdRecSupport, mem_ofPred_eq]
    exact lt_of_lt_of_le hr (measure_mono fun n hn => by simp only [mem_ofPred_eq] at hn ⊢; omega)

/-- `0` lies in the support. -/
theorem zero_mem_fwdRecSupport {p : ℕ → ℝ} (hp : IsIncrementLaw p) : 0 ∈ fwdRecSupport p := by
  have := isProbabilityMeasure_lawMeasure hp
  change 0 < lawMeasure p {n | 0 < n}
  have : {n : ℕ | 0 < n} = {0}ᶜ := by ext n; simp [Nat.pos_iff_ne_zero]
  rw [this, prob_compl_eq_one_sub (measurableSet_singleton 0), lawMeasure_zero hp, tsub_zero]
  exact one_pos

/-- `Pᵗ(i, ·)` is carried by the support for `t ≥ i`. -/
theorem fwdRec_pow_compl_support {p : ℕ → ℝ} (hp : IsIncrementLaw p) {i t : ℕ} (hit : i ≤ t) :
    (fwdRecKernel (lawMeasure p) ^ t : Kernel ℕ ℕ) i (fwdRecSupport p)ᶜ = 0 := by
  have := isProbabilityMeasure_lawMeasure hp
  rw [fwdRec_pow_ge hit]
  exact pow_compl_eq_zero_of_absorbing _ (Set.to_countable _).measurableSet
    (fwdRecSupport_absorbing hp) (t - i) 0 (zero_mem_fwdRecSupport hp)

/-! ### Proposition 13.2.1 -/

/-- The linked chain reaches `(0, 0)` almost surely from every state. -/
theorem linked_hitProb_eq_one {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) (z : ℕ × ℕ) :
    haveI := isProbabilityMeasure_lawMeasure hp
    haveI := isMarkovKernel_linkedFwdRec (lawMeasure p)
    hitProb (linkedFwdRec (lawMeasure p)) {((0 : ℕ), (0 : ℕ))} z = 1 := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_linkedFwdRec (lawMeasure p)
  have := isMarkovKernel_fwdRecKernel (lawMeasure p)
  set W := linkedFwdRec (lawMeasure p)
  set α : Set (ℕ × ℕ) := {((0 : ℕ), (0 : ℕ))}
  have hαm : MeasurableSet α := measurableSet_singleton _
  have hφ := linked_isPhiIrreducible hp hap
  have hφ0 : Measure.dirac ((0 : ℕ), (0 : ℕ)) ≠ 0 := by simp
  set ψ := maxIrrMeasure W (Measure.dirac ((0 : ℕ), (0 : ℕ)))
  have hψ := isMaximalIrreducibility_maxIrrMeasure W hφ hφ0
  have hψα : 0 < ψ α := by
    by_contra h0
    have := (hψ.2.2 _ hφ) (nonpos_iff_eq_zero.1 (not_lt.1 h0))
    simp [α] at this
  have hacc : IsAccessibleAtom W ψ α := ⟨isAtom_singleton W _, hψ, hψα⟩
  obtain ⟨hπp, hπi⟩ := linkedInv_spec hp hm
  have hpos : IsPositive W ψ := ⟨hψ, linkedInv p, hπp, hπi⟩
  have hrec := proposition_10_1_1 hpos
  have hrep := eq_smul_atomMeasure_of_accessible hacc hrec (mem_singleton _) hπi
  have hLa : hitProb W α ((0 : ℕ), (0 : ℕ)) = 1 :=
    (hacc.isRecurrentChain_iff (mem_singleton _)).1 hrec
  set R := fwdRecSupport p
  -- states of `R × R` reach `(0, 0)` almost surely
  have hLR : ∀ w : ℕ × ℕ, w.1 ∈ R → w.2 ∈ R → hitProb W α w = 1 := fun w h1 h2 => by
    by_cases hw : w ∈ α
    · rw [mem_singleton_iff.1 hw]; exact hLa
    · have hπw : 0 < linkedInv p {w} := by
        have := isProbabilityMeasure_lawMeasure hp
        have hmean := lintegral_lawMeasure hp hm
        have hnet : (∫⁻ n, (n : ℝ≥0∞) ∂lawMeasure p) ^ 2 ≠ ∞ := by
          rw [hmean]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        rw [linkedInv, Measure.smul_apply, show ({w} : Set (ℕ × ℕ)) = {w.1} ×ˢ {w.2} by simp,
          Measure.prod_prod, fwdRecInv_singleton, fwdRecInv_singleton, smul_eq_mul]
        exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hnet) (ENNReal.mul_pos h1.ne' h2.ne').ne'
      have hμ : atomMeasure W hacc.1.1 ((0 : ℕ), (0 : ℕ)) {w} ≠ 0 := by
        intro h0
        rw [hrep, Measure.smul_apply, h0, smul_zero] at hπw
        exact lt_irrefl 0 hπw
      rw [atomMeasure, tabooPotKernel, Kernel.sum_apply, Measure.sum_apply _
        (measurableSet_singleton _)] at hμ
      obtain ⟨k, hk⟩ : ∃ k, tabooKernel W hacc.1.1 k ((0 : ℕ), (0 : ℕ)) {w} ≠ 0 := by
        by_contra h
        push Not at h
        exact hμ (ENNReal.tsum_eq_zero.2 h)
      have hle := mul_one_sub_hitProb_le W hacc.1.1 k ((0 : ℕ), (0 : ℕ)) hw
      rw [hLa, tsub_self] at hle
      have h0 : 1 - hitProb W α w = 0 := by
        rcases mul_eq_zero.1 (nonpos_iff_eq_zero.1 hle) with h | h
        · exact absurd h hk
        · exact h
      exact le_antisymm (hitProb_le_one _ _ _) (tsub_eq_zero_iff_le.1 h0)
  -- every state enters `R × R` by time `max z₁ z₂`
  set t := max z.1 z.2
  have hcarry : (W ^ t : Kernel (ℕ × ℕ) (ℕ × ℕ)) z (R ×ˢ R)ᶜ = 0 := by
    have hsub : (R ×ˢ R)ᶜ ⊆ (Rᶜ ×ˢ univ) ∪ (univ ×ˢ Rᶜ) := fun w hw => by
      simp only [mem_compl_iff, mem_prod, not_and_or] at hw
      rcases hw with h | h
      · exact Or.inl ⟨h, mem_univ _⟩
      · exact Or.inr ⟨mem_univ _, h⟩
    refine nonpos_iff_eq_zero.1 ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_))
    rw [linkedFwdRec_pow_apply, Measure.prod_prod, Measure.prod_prod,
      fwdRec_pow_compl_support hp (le_max_left _ _), fwdRec_pow_compl_support hp (le_max_right _ _),
      zero_mul, mul_zero, add_zero]
  have hle := one_sub_hitProb_le_lintegral W hαm t z
  have hint : ∫⁻ w, (1 - hitProb W α w) ∂(W ^ t : Kernel (ℕ × ℕ) (ℕ × ℕ)) z = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have : ∀ᵐ w ∂(W ^ t : Kernel (ℕ × ℕ) (ℕ × ℕ)) z, w ∈ R ×ˢ R := by
      rw [ae_iff]; exact hcarry
    filter_upwards [this] with w hw
    rw [hLR w hw.1 hw.2, tsub_self]
  rw [hint] at hle
  exact le_antisymm (hitProb_le_one _ _ _) (tsub_eq_zero_iff_le.1 (nonpos_iff_eq_zero.1 hle))

/-- **Proposition 13.2.1** (MT p. 321): for an aperiodic increment law with finite mean and any
delay distributions `a`, `b` (probabilities on `ℤ₊`), the linked chain started from `a ⊗ b` has a
common renewal (a visit to `(0, 0)`) almost surely: `P(T_ab < ∞) = 1`. -/
theorem proposition_13_2_1 {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) (a b : Measure ℕ) [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] :
    haveI := isProbabilityMeasure_lawMeasure hp
    haveI := isMarkovKernel_linkedFwdRec (lawMeasure p)
    ∫⁻ z, hitProb (linkedFwdRec (lawMeasure p)) {((0 : ℕ), (0 : ℕ))} z ∂a.prod b = 1 := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_linkedFwdRec (lawMeasure p)
  simp_rw [linked_hitProb_eq_one hp hap hm]
  rw [lintegral_one, measure_univ]

end MeynTweedie.Ergodicity
