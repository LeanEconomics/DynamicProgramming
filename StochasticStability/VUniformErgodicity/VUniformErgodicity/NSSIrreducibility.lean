/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.MinimalSets

/-!
# M-irreducibility and ψ-irreducibility of NSS(F) (MT §7.2.2)

Meyn and Tweedie, §7.2.2, pp. 156–157. The state space `X` and the noise space `W` are
finite-dimensional real normed spaces; the noise satisfies (NSS3) and `F` is `C¹`.

* `isTChain_restrictKernel`: the restriction of a T-chain to an absorbing set is a T-chain
  (used for "the NSS(F) model restricted to `M`").
* `controlSet_nonempty`: under (NSS3) the control set is non-empty.
* `exists_forall_isOpen_measure_pos`: a non-zero measure on a second-countable space has a point
  all of whose neighbourhoods are charged (a point of `supp ψ`).
* **Theorem 7.2.4** (p. 156): `theorem_7_2_4_i`, a minimal set is absorbing for NSS(F)
  (`F` continuous suffices); `theorem_7_2_4_ii`, under the rank condition (CM3), NSS(F)
  restricted to `M` is an open set irreducible and `ψ`-irreducible T-chain.
* `isOpenSetIrreducible_of_isMinimal_univ` (MT p. 156): if `X` itself is minimal, NSS(F) is open
  set irreducible and `ψ`-irreducible.
* **Theorem 7.2.6** (p. 157): `theorem_7_2_6`, NSS(F) is `ψ`-irreducible (for a non-zero `ψ`) iff
  CM(F) is M-irreducible. The "only if" half holds for every continuous `F`
  (`theorem_7_2_6_only_if`); the "if" half uses that NSS(F) is a T-chain (Proposition 7.1.5) and
  Proposition 6.2.1 at a globally attracting state, where the book uses an open petite set and
  Proposition 5.5.4.

**Hypotheses.** Forward accessibility is used in the form of the rank condition (CM3),
equivalent to it by Proposition 7.1.4.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-- **Restricting a T-chain** to an absorbing set gives a T-chain: the continuous component
`T(x, B)`, `x ∈ A`, `B ⊆ A`, is still lower semicontinuous on `A` and non-trivial, since `T`
charges no point outside `A`. -/
theorem isTChain_restrictKernel {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {P : Kernel X X} [IsMarkovKernel P] (hP : IsTChain P) {A : Set X} (hA : MeasurableSet A)
    (hAbs : IsAbsorbing P A) : IsTChain (restrictKernel P hA) := by
  obtain ⟨a, T, ha, hT, hpos⟩ := hP
  set TA : Kernel A A :=
    (T.comap Subtype.val measurable_subtype_coe).comapRight (MeasurableEmbedding.subtype_coe hA)
  have hTA : ∀ x B, MeasurableSet B → TA x B = T x (Subtype.val '' B) := fun x B hB => by
    rw [Kernel.comapRight_apply' _ _ _ hB, Kernel.comap_apply]
  have himg : ∀ B : Set A, MeasurableSet B → MeasurableSet (Subtype.val '' B) := fun B hB =>
    (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
  refine ⟨a, TA, ha, ⟨fun x => ?_, fun x => ?_, fun B hB => ?_⟩, fun x => ?_⟩
  · rw [hTA x univ MeasurableSet.univ]
    exact (measure_mono (subset_univ _)).trans (hT.1 x)
  · refine Measure.le_intro fun B hB _ => ?_
    rw [hTA x B hB, sampledKernel_apply _ a x hB]
    simp_rw [restrictKernel_pow_apply P hA hAbs _ x hB]
    rw [← sampledKernel_apply P a x (himg B hB)]
    exact hT.2.1 x _
  · have : (fun x : A => TA x B) = (fun y => T y (Subtype.val '' B)) ∘ Subtype.val :=
      funext fun x => hTA x B hB
    rw [this]
    exact (hT.2.2 _ (himg B hB)).comp continuous_subtype_val
  · rw [hTA x univ MeasurableSet.univ, image_univ, Subtype.range_coe]
    have h0 : T x Aᶜ = 0 := by
      have h1 := hT.2.1 x Aᶜ
      rw [sampledKernel_apply P a x hA.compl] at h1
      simp_rw [hAbs.pow_compl hA _ x.2, mul_zero, tsum_zero] at h1
      exact nonpos_iff_eq_zero.1 h1
    calc 0 < T x univ := hpos x
      _ ≤ T x A + T x Aᶜ := measure_univ_le_add_compl A
      _ = T x A := by rw [h0, add_zero]

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [(volume : Measure W).IsAddHaarMeasure] in
/-- Under (NSS3) with a probability `Γ`, the control set is non-empty. -/
theorem controlSet_nonempty {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) : (controlSet γ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have := measure_compl_controlSet hΓ
  rw [h, compl_empty, measure_univ] at this
  exact one_ne_zero this

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
/-- A non-zero measure on a second-countable space has a point every neighbourhood of which has
positive measure (a point of the support). -/
theorem exists_forall_isOpen_measure_pos [SecondCountableTopology X] {ψ : Measure X}
    (hψ : ψ ≠ 0) : ∃ x, ∀ U, IsOpen U → x ∈ U → 0 < ψ U := by
  by_contra hc
  push Not at hc
  choose U hU hxU hψU using hc
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  have huniv : (⋃ x ∈ S, U x) = univ := hSU.trans (eq_univ_of_forall fun x =>
    mem_iUnion.2 ⟨x, hxU x⟩)
  have h0 : ψ univ = 0 := by
    rw [← huniv]
    exact (measure_biUnion_null_iff hS).2 fun x _ => nonpos_iff_eq_zero.1 (hψU x)
  exact hψ (Measure.measure_univ_eq_zero.1 h0)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- **Theorem 7.2.4 (i)** (MT p. 156): under (NSS3), a minimal set of CM(F) is absorbing for
NSS(F) (`F` continuous). -/
theorem theorem_7_2_4_i {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {M : Set X}
    (hM : IsMinimal F (controlSet γ) M) : IsAbsorbing (nssKernel Γ F) M :=
  (proposition_7_2_2_i hΓ hF hM.2.1).2 hM.2.2.1

/-- **Theorem 7.2.4 (ii)** (MT p. 156): under (NSS3) and the rank condition (CM3) (forward
accessibility) for a `C¹` map `F`, the restriction of NSS(F) to a minimal set `M` is an open set
irreducible T-chain, and so `ψ`-irreducible for a non-zero `ψ`. -/
theorem theorem_7_2_4_ii {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) {M : Set X} (hM : IsMinimal F (controlSet γ) M) :
    let _ := isMarkovKernel_restrictKernel (nssKernel Γ F) hM.2.1.measurableSet
      (theorem_7_2_4_i hΓ hF.continuous hM)
    IsTChain (restrictKernel (nssKernel Γ F) hM.2.1.measurableSet) ∧
      IsOpenSetIrreducible (restrictKernel (nssKernel Γ F) hM.2.1.measurableSet) ∧
      ∃ ψ : Measure M, ψ ≠ 0 ∧
        IsPhiIrreducible (restrictKernel (nssKernel Γ F) hM.2.1.measurableSet) ψ := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  have hAbs := theorem_7_2_4_i hΓ hF.continuous hM
  have hMm := hM.2.1.measurableSet
  let _ := isMarkovKernel_restrictKernel (nssKernel Γ F) hMm hAbs
  have hT : IsTChain (restrictKernel (nssKernel Γ F) hMm) :=
    isTChain_restrictKernel (proposition_7_1_5 hΓ hF hrank).2 hMm hAbs
  have hirr : IsOpenSetIrreducible (restrictKernel (nssKernel Γ F) hMm) := by
    intro x O' hO' hxO' y
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hO'
    have hO'm : MeasurableSet (Subtype.val ⁻¹' U : Set M) := hO'.measurableSet
    rw [potKernel_pos_iff _ hO'm]
    obtain ⟨w, hw⟩ := controlSet_nonempty hΓ
    have hz : F ((y : X), w) ∈ M := isCMInvariant_iff_step.1 hM.2.2.1 y y.2 w hw
    have hcl := ((proposition_7_2_3 (fun w _ => hF.continuous.comp
      (continuous_id.prodMk continuous_const)) ⟨w, hw⟩ hM.1).1.1 hM) _ hz
    have hxcl : (x : X) ∈ closure (reach F (controlSet γ) (F ((y : X), w))) := by
      rw [hcl]; exact x.2
    obtain ⟨z, hzU, hzr⟩ := mem_closure_iff.1 hxcl U hU hxO'
    obtain ⟨k, hk⟩ := mem_reach_iff.1 hzr
    have hk1 : z ∈ reachK F (controlSet γ) (k + 1) y :=
      (mem_reachK_succ' F _ k y z).2 ⟨w, hw, hk⟩
    have hpos := (proposition_7_2_2_ii hΓ hF.continuous hU (k + 1) y).1 ⟨z, hk1, hzU⟩
    refine ⟨k, ?_⟩
    rw [restrictKernel_pow_apply _ hMm hAbs _ _ hO'm, Subtype.image_preimage_coe,
      inter_comm, measure_inter_conull (hAbs.pow_compl hMm _ y.2)]
    exact hpos
  obtain ⟨x₀, hx₀⟩ := hM.1
  have : Nonempty M := ⟨⟨x₀, hx₀⟩⟩
  exact ⟨hT, hirr, proposition_6_2_2 hT hirr⟩

/-- MT p. 156: under the hypotheses of Theorem 7.2.4, if the whole state space is minimal then
NSS(F) itself is open set irreducible, hence `ψ`-irreducible for a non-zero `ψ`. -/
theorem isOpenSetIrreducible_of_isMinimal_univ {Γ : Measure W} [IsProbabilityMeasure Γ]
    {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) (hmin : IsMinimal F (controlSet γ) univ) :
    have := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
    IsOpenSetIrreducible (nssKernel Γ F) ∧
      ∃ ψ : Measure X, ψ ≠ 0 ∧ IsPhiIrreducible (nssKernel Γ F) ψ := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  have hFx : ∀ w ∈ controlSet γ, Continuous fun x => F (x, w) := fun w _ =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨w, hw⟩ := controlSet_nonempty hΓ
  have hirr : IsOpenSetIrreducible (nssKernel Γ F) := by
    intro x U hU hxU y
    rw [potKernel_pos_iff _ hU.measurableSet]
    have hcl := ((proposition_7_2_3 hFx ⟨w, hw⟩ hmin.1).1.1 hmin) (F (y, w)) (mem_univ _)
    have hx : x ∈ closure (reach F (controlSet γ) (F (y, w))) := by rw [hcl]; trivial
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.1 hx U hU hxU
    obtain ⟨k, hk⟩ := mem_reach_iff.1 hz
    exact ⟨k, (proposition_7_2_2_ii hΓ hF.continuous hU (k + 1) y).1
      ⟨z, (mem_reachK_succ' F _ k y z).2 ⟨w, hw, hk⟩, hzU⟩⟩
  have : Nonempty X := ⟨0⟩
  exact ⟨hirr, proposition_6_2_2 (proposition_7_1_5 hΓ hF hrank).2 hirr⟩

/-- **Theorem 7.2.6**, "only if" (MT p. 157): under (NSS3), if NSS(F) is `ψ`-irreducible for a
non-zero `ψ` (`F` continuous), then CM(F) is M-irreducible: every point `x*` of the support of
`ψ` lies in the closure of every `A₊(y)`. -/
theorem theorem_7_2_6_only_if {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {ψ : Measure X}
    (hψ0 : ψ ≠ 0)
    (hψ : have := isMarkovKernel_recursionKernel Γ hF.measurable
      IsPhiIrreducible (nssKernel Γ F) ψ) : IsMIrreducible F (controlSet γ) := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.measurable
  obtain ⟨x, hx⟩ := exists_forall_isOpen_measure_pos hψ0
  refine isMIrreducible_of_forall_mem_closure (fun w _ => hF.comp
    (continuous_id.prodMk continuous_const)) (x := x) fun y => ?_
  rw [mem_closure_iff]
  intro U hU hxU
  have hL := hψ U hU.measurableSet (hx U hU hxU) y
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hU.measurableSet y).1 hL
  obtain ⟨z, hz, hzU⟩ := (proposition_7_2_2_ii hΓ hF hU (n + 1) y).2 hn
  exact ⟨z, hzU, reachK_subset_reach F _ _ y hz⟩

/-- **Theorem 7.2.6** (MT p. 157): under (NSS3) and the rank condition (CM3) (forward
accessibility) for a `C¹` map `F`, NSS(F) is `ψ`-irreducible for some non-zero `ψ` iff CM(F)
is M-irreducible. -/
theorem theorem_7_2_6 {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) :
    have := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
    (∃ ψ : Measure X, ψ ≠ 0 ∧ IsPhiIrreducible (nssKernel Γ F) ψ) ↔
      IsMIrreducible F (controlSet γ) := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  refine ⟨fun ⟨ψ, hψ0, hψ⟩ => theorem_7_2_6_only_if hΓ hF.continuous hψ0 hψ, fun h => ?_⟩
  have hFx : ∀ w ∈ controlSet γ, Continuous fun x => F (x, w) := fun w _ =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨x, hx⟩ := (proposition_7_2_5_i hFx (controlSet_nonempty hΓ)).1 h
  have hreach : IsReachable (nssKernel Γ F) x := by
    intro U hU hxU y
    rw [potKernel_pos_iff _ hU.measurableSet]
    have h1 := mem_iInter₂.1 (hx y) 1 le_rfl
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.1 h1 U hU hxU
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
    rw [reachKSet_singleton] at hzk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact ⟨n, (proposition_7_2_2_ii hΓ hF.continuous hU (n + 1) y).1 ⟨z, hzk, hzU⟩⟩
  obtain ⟨a, T, -, hT, hpos⟩ := (proposition_7_1_5 hΓ hF hrank).2
  refine ⟨T x, fun h0 => ?_, proposition_6_2_1 hT hreach⟩
  have := hpos x
  rw [h0] at this
  simp at this

end MeynTweedie.VUniformErgodicity
