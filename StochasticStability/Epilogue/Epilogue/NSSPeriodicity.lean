/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.PeriodicOrbits
import Epilogue.NSSIrreducibility
import Epilogue.Cycles

/-!
# Periodicity of NSS(F) (MT §7.3.2)

Meyn and Tweedie, §7.3.2, pp. 160–161: the periodic orbits of a minimal set of CM(F) are the
cycles of NSS(F). The setting is that of `NSSIrreducibility`: (NSS3), a `C¹` map `F`, and the rank
condition (CM3).

* `isCycle_of_isPeriodicOrbit`: a periodic orbit `G` with union `M` is a `d`-cycle of NSS(F) for
  every `ψ` that does not charge `Mᶜ`.
* `dvd_of_isCycle`: if `E →ⁿ E` for the return times of an open set `E ⊆ M` lying in a small set,
  then the period `d'` of any cycle of NSS(F) (relative to a `ψ` charging every open set that
  meets `M`) divides every `n`, so divides `d`.
* `orbitClass_ae_eq_of_isCycle`: every `d`-cycle agrees with the orbit up to `ψ`-null sets and a
  relabelling.
* `isGloballyAttracting_of_mem_minimal`: under M-irreducibility every point of the minimal set is
  globally attracting; `isReachable_of_isGloballyAttracting`: such a point is reachable.
* **Theorem 7.3.5** (p. 160): `theorem_7_3_5_i`, for a minimal set `M`, the periodic orbit of
  Theorem 7.3.3, of period `d`, is a `d`-cycle and `d` is the period of NSS(F) for every `ψ`
  carried by `M` and charging every open set meeting `M`, and every `d`-cycle is the orbit up to
  `ψ`-null sets (the orbit is "the" cycle of Theorem 5.4.4); `exists_measure_minimal`, the
  maximal irreducibility measure of the restriction to `M` (Theorem 7.2.4), carried to `X`, is
  such a `ψ`. `theorem_7_3_5_ii`, if CM(F) is M-irreducible with an aperiodic minimal set, then
  NSS(F) is a `ψ`-irreducible aperiodic T-chain (`ψ` maximal).

**Proof differences.** The book shrinks the set `E` of Theorem 7.3.3 to a small set and refers to
the proof of Theorem 5.2.1. Here the cycle property of the orbit comes from Proposition 7.2.2,
and the divisibility `d' ∣ d` from the small set: from two points of the small set lying in
classes `a` and `b` of a `d'`-cycle, the minorizing measure lives on the classes `a + k` and
`b + k`, so `a = b`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- Under (NSS3), if `F(x, w) ∈ C` for all `w ∈ O_w` and `C` is closed, then `P(x, C) = 1`. -/
theorem nssKernel_apply_eq_one {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {C : Set X} (hC : IsClosed C)
    {x : X} (hx : ∀ w ∈ controlSet γ, F (x, w) ∈ C) : nssKernel Γ F x C = 1 := by
  have hM := isMarkovKernel_recursionKernel Γ hF.measurable
  rw [← prob_compl_eq_zero_iff hC.measurableSet]
  by_contra hne
  have key := (proposition_7_2_2_ii hΓ hF hC.isOpen_compl 1 x).2
  rw [pow_one] at key
  obtain ⟨y, hy, hyC⟩ := key (pos_iff_ne_zero.2 hne)
  obtain ⟨y', hy', w, hw, rfl⟩ := (mem_reachK_succ F _ 0 x y).1 hy
  rw [reachK_zero, mem_singleton_iff] at hy'
  subst hy'
  exact hyC (hx w hw)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- **A periodic orbit is a cycle** (MT Theorem 7.3.5 (i)): a periodic orbit of CM(F) with union
`M` is a `d`-cycle of NSS(F) relative to every `ψ` with `ψ(Mᶜ) = 0`. -/
theorem isCycle_of_isPeriodicOrbit {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {d : ℕ} {G : ZMod d → Set X}
    (hG : IsPeriodicOrbit F (controlSet γ) d G) {M : Set X} (hGM : ⋃ i, G i = M)
    {ψ : Measure X} (hψ : ψ Mᶜ = 0) : IsCycle (nssKernel Γ F) ψ d G :=
  ⟨fun i => (hG.isClosed i).measurableSet, hG.disjoint,
    fun i x hx => nssKernel_apply_eq_one hΓ hF (hG.isClosed (i + 1)) fun w hw =>
      hG.step i x hx w hw,
    by rw [hGM]; exact hψ⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
/-- Two points of a `ν`-small set (`ν ≠ 0`) lying in classes `a` and `b` of a cycle force
`a = b`. -/
theorem cycle_class_eq_of_isSmallSet {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    {D : ZMod d → Set X} (hD : IsCycle P ψ d D) {k : ℕ} {ν : Measure X} {N : Set X}
    (hN : IsSmallSet P k ν N) {x y : X} {a b : ZMod d} (hx : x ∈ N) (hxa : x ∈ D a)
    (hy : y ∈ N) (hyb : y ∈ D b) : a = b := by
  by_contra hab
  have := isMarkovKernel_pow P k
  have h1 : ν (D (a + k))ᶜ = 0 := by
    have hp : (P ^ k) x (D (a + k))ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff (hD.measurableSet _)]; exact hD.pow_apply k hxa
    exact nonpos_iff_eq_zero.1 ((hN.le_apply hx _).trans hp.le)
  have h2 : ν (D (b + k))ᶜ = 0 := by
    have hp : (P ^ k) y (D (b + k))ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff (hD.measurableSet _)]; exact hD.pow_apply k hyb
    exact nonpos_iff_eq_zero.1 ((hN.le_apply hy _).trans hp.le)
  have hsub : D (a + k) ⊆ (D (b + k))ᶜ := Set.disjoint_left.1
    (hD.disjoint _ _ fun h => hab (by linear_combination h))
  have h3 : ν (D (a + k)) = 0 := measure_mono_null hsub h2
  apply hN.2.2.1
  rw [← Measure.measure_univ_eq_zero]
  exact nonpos_iff_eq_zero.1 ((measure_univ_le_add_compl _).trans (by rw [h3, h1, add_zero]))

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- **The period of a cycle divides the period of the orbit** (MT Theorem 7.3.5 (i)): if `E`
(from Theorem 7.3.3) lies in a `ν`-small set and `ψ` charges every open set meeting `M`, the
period `d'` of every `d'`-cycle of NSS(F) relative to `ψ` divides `d`. -/
theorem dvd_of_isCycle {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {M E : Set X} {d : ℕ}
    (h : OrbitData F (controlSet γ) M E d) {N : Set X} {k : ℕ} {ν : Measure X}
    (hN : IsSmallSet (nssKernel Γ F) k ν N) (hEN : E ⊆ N) {ψ : Measure X}
    (hψU : ∀ U, IsOpen U → (U ∩ M).Nonempty → 0 < ψ U) {d' : ℕ} {D : ZMod d' → Set X}
    (hD : IsCycle (nssKernel Γ F) ψ d' D) : d' ∣ d := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.measurable
  have : Countable (ZMod d') := by
    rcases d' with _ | n
    · exact (inferInstance : Countable ℤ)
    · infer_instance
  have key : ∀ n ∈ returnTimes F (controlSet γ) E, ((n : ℕ) : ZMod d') = 0 := by
    intro n hn
    obtain ⟨e, he⟩ := h.nonempty
    have hψE : 0 < ψ E := hψU E h.isOpen ⟨e, he, h.subset he⟩
    obtain ⟨a, ha⟩ : ∃ a, 0 < ψ (E ∩ D a) := by
      by_contra hc
      push Not at hc
      have hsub : E ⊆ (⋃ a, E ∩ D a) ∪ (⋃ i, D i)ᶜ := by
        intro x hx
        by_cases hxD : x ∈ ⋃ i, D i
        · obtain ⟨a, ha⟩ := mem_iUnion.1 hxD
          exact Or.inl (mem_iUnion.2 ⟨a, hx, ha⟩)
        · exact Or.inr hxD
      exact hψE.ne' (measure_mono_null hsub (measure_union_null
        (measure_iUnion_null fun a => nonpos_iff_eq_zero.1 (hc a)) hD.null_compl))
    obtain ⟨x, hxE, hxa⟩ := nonempty_of_measure_ne_zero ha.ne'
    have hpos : 0 < (nssKernel Γ F ^ n) x E :=
      (proposition_7_2_2_ii hΓ hF h.isOpen n x).1 ⟨x, hn.2 x hxE hxE, hxE⟩
    have := isMarkovKernel_pow (nssKernel Γ F) n
    have hpos' : 0 < (nssKernel Γ F ^ n) x (E ∩ D (a + n)) := by
      rw [measure_inter_conull]
      · exact hpos
      · rw [prob_compl_eq_zero_iff (hD.measurableSet _)]
        exact hD.pow_apply n hxa
    obtain ⟨y, hyE, hya⟩ := nonempty_of_measure_ne_zero hpos'.ne'
    have := cycle_class_eq_of_isSmallSet hD hN (hEN hxE) hxa (hEN hyE) hya
    linear_combination -this
  obtain ⟨n₀, hn₀⟩ := h.ret
  rw [h.gcd]
  exact dvd_setGcd (returnTimes_isAddClosed _ _ _) hn₀ hn₀.1 fun n hn =>
    (ZMod.natCast_eq_zero_iff n d').1 (key n hn)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- **The orbit is the cycle up to null sets** (MT Theorem 7.3.5 (i)): under the hypotheses of
`dvd_of_isCycle`, every `d`-cycle `D` of NSS(F) agrees with the orbit classes `Gᵢ` up to
`ψ`-null sets after a relabelling `i ↦ c + i`. -/
theorem orbitClass_ae_eq_of_isCycle {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {M E : Set X} {d : ℕ}
    (h : OrbitData F (controlSet γ) M E d) {N : Set X} {k : ℕ} {ν : Measure X}
    (hN : IsSmallSet (nssKernel Γ F) k ν N) (hEN : E ⊆ N) {ψ : Measure X} (hψM : ψ Mᶜ = 0)
    (hψU : ∀ U, IsOpen U → (U ∩ M).Nonempty → 0 < ψ U) {D : ZMod d → Set X}
    (hD : IsCycle (nssKernel Γ F) ψ d D) :
    ∃ c, ∀ i, ψ (symmDiff (orbitClass F (controlSet γ) M E d i) (D (c + i))) = 0 := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.measurable
  have : NeZero d := ⟨h.d_pos.ne'⟩
  obtain ⟨e, he⟩ := h.nonempty
  have hψE : 0 < ψ E := hψU E h.isOpen ⟨e, he, h.subset he⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c, 0 < ψ (E ∩ D c) := by
    by_contra hc
    push Not at hc
    have hsub : E ⊆ (⋃ a, E ∩ D a) ∪ (⋃ i, D i)ᶜ := by
      intro x hx
      by_cases hxD : x ∈ ⋃ i, D i
      · obtain ⟨a, ha⟩ := mem_iUnion.1 hxD
        exact Or.inl (mem_iUnion.2 ⟨a, hx, ha⟩)
      · exact Or.inr hxD
    exact hψE.ne' (measure_mono_null hsub (measure_union_null
      (measure_iUnion_null fun a => nonpos_iff_eq_zero.1 (hc a)) hD.null_compl))
  obtain ⟨e₀, he₀E, he₀D⟩ := nonempty_of_measure_ne_zero hc₀.ne'
  -- every point of `Gᵢ` in a class `D b` has `b = c₀ + i`
  have key : ∀ i, ∀ x ∈ orbitClass F (controlSet γ) M E d i, ∀ b, x ∈ D b → b = c₀ + i := by
    intro i x hx b hxb
    obtain ⟨-, n, hn, hmeet⟩ := hx
    have hpos := (proposition_7_2_2_ii hΓ hF h.isOpen n x).1 hmeet
    have := isMarkovKernel_pow (nssKernel Γ F) n
    have hpos' : 0 < (nssKernel Γ F ^ n) x (E ∩ D (b + n)) := by
      rw [measure_inter_conull]
      · exact hpos
      · rw [prob_compl_eq_zero_iff (hD.measurableSet _)]
        exact hD.pow_apply n hxb
    obtain ⟨y, hyE, hyD⟩ := nonempty_of_measure_ne_zero hpos'.ne'
    have hbc := cycle_class_eq_of_isSmallSet hD hN (hEN hyE) hyD (hEN he₀E) he₀D
    linear_combination hbc - hn
  refine ⟨c₀, fun i => measure_union_null ?_ ?_⟩
  · refine measure_mono_null (fun x hx => ?_) hD.null_compl
    intro hU
    obtain ⟨b, hb⟩ := mem_iUnion.1 hU
    exact hx.2 (key i x hx.1 b hb ▸ hb)
  · refine measure_mono_null (fun x hx => ?_) hψM
    intro hxM
    rw [← h.iUnion_eq] at hxM
    obtain ⟨j, hj⟩ := mem_iUnion.1 hxM
    have hji := key j x hj _ hx.1
    have : j = i := by linear_combination -hji
    exact hx.2 (this ▸ hj)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
/-- Under M-irreducibility every point of a minimal set is globally attracting (from the proof of
MT Proposition 7.2.5). -/
theorem isGloballyAttracting_of_mem_minimal {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (hO : O.Nonempty) (hind : IsIndecomposable F O)
    {M : Set X} (hM : IsMinimal F O M) {x : X} (hx : x ∈ M) : IsGloballyAttracting F O x :=
  fun y => mem_iInter₂.2 fun N _ => by
    obtain ⟨hne, hc, hi⟩ := tail_closure_props hF hO y N
    exact IsMIrreducible.minimal_subset hind hM hne hc hi hx

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- Under (NSS3), a globally attracting state is reachable (MT p. 157). -/
theorem isReachable_of_isGloballyAttracting {Γ : Measure W} [IsProbabilityMeasure Γ]
    {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Continuous F) {x : X}
    (hx : IsGloballyAttracting F (controlSet γ) x) : IsReachable (nssKernel Γ F) x := by
  intro U hU hxU y
  rw [potKernel_pos_iff _ hU.measurableSet]
  have h1 := mem_iInter₂.1 (hx y) 1 le_rfl
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.1 h1 U hU hxU
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
  rw [reachKSet_singleton] at hzk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  exact ⟨n, (proposition_7_2_2_ii hΓ hF hU (n + 1) y).1 ⟨z, hzk, hzU⟩⟩

/-- **Theorem 7.3.5 (i)** (MT p. 160): under (NSS3) and the rank condition (forward
accessibility) for a `C¹` map, a minimal set `M` has a period `d` and a periodic orbit `G` of
period `d` with union `M`, which is a `d`-cycle of NSS(F) whose period is `d`, relative to every
`ψ` carried by `M` and charging every open set meeting `M` (for example the maximal irreducibility
measure of the restriction to `M`, `exists_measure_minimal`); every `d`-cycle agrees with the
orbit up to `ψ`-null sets and a relabelling (the uniqueness of Theorem 5.4.4). -/
theorem theorem_7_3_5_i {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) {M : Set X} (hM : IsMinimal F (controlSet γ) M) :
    ∃ (d : ℕ) (G : ZMod d → Set X), IsPeriodOf F (controlSet γ) M d ∧
      IsPeriodicOrbit F (controlSet γ) d G ∧ ⋃ i, G i = M ∧
      ∀ ψ : Measure X, ψ Mᶜ = 0 → (∀ U, IsOpen U → (U ∩ M).Nonempty → 0 < ψ U) →
        IsCycle (nssKernel Γ F) ψ d G ∧ IsPeriod (nssKernel Γ F) ψ d ∧
        ∀ D : ZMod d → Set X, IsCycle (nssKernel Γ F) ψ d D →
          ∃ c, ∀ i, ψ (symmDiff (G i) (D (c + i))) = 0 := by
  obtain ⟨E, hE⟩ := exists_orbitData hF (isOpen_controlSet hΓ.1) hrank hM
  obtain ⟨x₁, hx₁⟩ := hE.nonempty
  obtain ⟨N, hNo, hxN, m, ν, hN⟩ := (proposition_7_1_5 hΓ hF hrank).1 x₁
  have h' := hE.shrink hNo ⟨x₁, hx₁, hxN⟩
  obtain ⟨hG, hGM, hper, -⟩ := theorem_7_3_3_of_orbitData h'
  refine ⟨_, _, hper, hG, hGM, fun ψ hψM hψU => ?_⟩
  have hcyc := isCycle_of_isPeriodicOrbit hΓ hF.continuous hG hGM hψM
  exact ⟨hcyc, ⟨h'.d_pos, ⟨_, hcyc⟩, fun d' D _ hD => Nat.le_of_dvd h'.d_pos
    (dvd_of_isCycle hΓ hF.continuous h' hN inter_subset_right hψU hD)⟩,
    fun D hD => orbitClass_ae_eq_of_isCycle hΓ hF.continuous h' hN inter_subset_right hψM hψU hD⟩

/-- The measure of Theorem 7.3.5 (i): the maximal irreducibility measure `ψ_M` of NSS(F)
restricted to a minimal set `M` (Theorem 7.2.4), carried to `X`, gives no mass to `Mᶜ` and
charges every open set meeting `M`. -/
theorem exists_measure_minimal {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) {M : Set X} (hM : IsMinimal F (controlSet γ) M) :
    let _ := isMarkovKernel_restrictKernel (nssKernel Γ F) hM.2.1.measurableSet
      (theorem_7_2_4_i hΓ hF.continuous hM)
    ∃ ψM : Measure M,
      IsMaximalIrreducibility (restrictKernel (nssKernel Γ F) hM.2.1.measurableSet) ψM ∧
      (ψM.map Subtype.val) Mᶜ = 0 ∧
      ∀ U, IsOpen U → (U ∩ M).Nonempty → 0 < (ψM.map Subtype.val) U := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  let _ := isMarkovKernel_restrictKernel (nssKernel Γ F) hM.2.1.measurableSet
    (theorem_7_2_4_i hΓ hF.continuous hM)
  obtain ⟨-, hirr, ψ₀, hψ₀0, hψ₀⟩ := theorem_7_2_4_ii hΓ hF hrank hM
  have hmax := isMaximalIrreducibility_maxIrrMeasure _ hψ₀ hψ₀0
  refine ⟨_, hmax, ?_, fun U hU ⟨x, hxU, hxM⟩ => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hM.2.1.measurableSet.compl]
    have : (Subtype.val ⁻¹' Mᶜ : Set M) = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · rw [Measure.map_apply measurable_subtype_coe hU.measurableSet]
    have hsupp := (lemma_6_1_4 hmax ⟨x, hxM⟩).1 (hirr ⟨x, hxM⟩)
    exact (Measure.mem_support_iff_forall _).1 hsupp _
      (continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))

/-- **Theorem 7.3.5 (ii)** (MT p. 160): under (NSS3) and the rank condition (forward
accessibility) for a `C¹` map, if CM(F) is M-irreducible and its minimal set is aperiodic, then
NSS(F) is a `ψ`-irreducible aperiodic T-chain, `ψ` a maximal irreducibility measure. -/
theorem theorem_7_3_5_ii {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (hrank : RankCondition F (controlSet γ)) (hirr : IsMIrreducible F (controlSet γ))
    {M : Set X} (hM : IsMinimal F (controlSet γ) M) (hap : IsPeriodOf F (controlSet γ) M 1) :
    have := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
    ∃ ψ : Measure X, IsMaximalIrreducibility (nssKernel Γ F) ψ ∧
      IsAperiodic (nssKernel Γ F) ψ ∧ IsTChain (nssKernel Γ F) := by
  have hPM := isMarkovKernel_recursionKernel Γ hF.continuous.measurable
  have hFx : ∀ w ∈ controlSet γ, Continuous fun x => F (x, w) := fun w _ =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨ψ₀, hψ₀0, hψ₀⟩ := (theorem_7_2_6 hΓ hF hrank).2 hirr
  have hmax := isMaximalIrreducibility_maxIrrMeasure _ hψ₀ hψ₀0
  set ψ := maxIrrMeasure (nssKernel Γ F) ψ₀
  have hψM : ψ Mᶜ = 0 := proposition_4_2_3_i hmax.2.1 hM.2.1.measurableSet hM.1
    (theorem_7_2_4_i hΓ hF.continuous hM)
  have hψU : ∀ U, IsOpen U → (U ∩ M).Nonempty → 0 < ψ U := by
    rintro U hU ⟨x, hxU, hxM⟩
    have hga := isGloballyAttracting_of_mem_minimal hFx (controlSet_nonempty hΓ) hirr.1 hM hxM
    have hsupp := (lemma_6_1_4 hmax x).1 (isReachable_of_isGloballyAttracting hΓ hF.continuous hga)
    exact (Measure.mem_support_iff_forall _).1 hsupp _ (hU.mem_nhds hxU)
  obtain ⟨d, G, hper, -, -, hcyc⟩ := theorem_7_3_5_i hΓ hF hrank hM
  have hd1 : d = 1 := hper.unique hap
  subst hd1
  exact ⟨ψ, hmax, (hcyc ψ hψM hψU).2.1, (proposition_7_1_5 hΓ hF hrank).2⟩

end MeynTweedie.Epilogue
