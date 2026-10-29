/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.FosterCriterion

/-!
# Positive chains are regular (MT §11.1, Theorem 11.0.1)

Copied for Chapter 13 from the Chapter 11 project
(`DriftRegularity/RegularityConverse.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to this project's modules.

Meyn and Tweedie, §11.1, pp. 257–260, and Theorem 11.0.1, p. 257. `ψ` is a maximal
irreducibility measure; the state space is countably generated where small sets are used.

**Atoms and the converse direction.**
* `IsAtom.meanReturnTime_eq`, `IsAtom.isPetite`; `IsAccessibleAtom.isRegularSet`: an accessible
  atom with `E_a[τ_α] < ∞` is regular.
* `isPositive_of_isRegularSet`: a regular set in `B⁺(X)` makes the chain positive;
  `IsRegularOn.exists_pos`; `IsRegularChain.isPositiveHarris`: a regular chain is positive Harris.

**Results.**
* **Proposition 11.1.1** (`proposition_11_1_1`, p. 258): on a countable space, with `ψ` charging
  every state, positivity and regularity are equivalent.
* (11.7) (`eq_11_7`, p. 258): for a positive chain, `E_x[τ_A] < ∞` for `π`-a.e. `x ∈ A`.
* **Theorem 11.1.2** (p. 258), for an accessible atom `α`: (i) `theorem_11_1_2_i`, a positive
  chain is regular on the full absorbing set `{x : E_x[τ_α] < ∞}`; (ii) `theorem_11_1_2_ii`, the
  chain is regular iff `E_x[τ_α] < ∞` for every `x`.
* The example (11.12) (`nullSet_example`, p. 259): a positive chain on `ℤ₊` whose regular part
  misses `{1, 2, …}`; `nullSet_example_counterexample` (see the correction).
* **Proposition 11.1.3** (`proposition_11_1_3`, p. 259): a positive chain with a minorization on a
  set in `B⁺(X)` is regular on a full absorbing set; the core is
  `exists_regular_of_minorization`, through the split chain and `meanReturnTime_le_split`
  (`E_x[τ_B] ≤ Ě_{x₀}[τ_{B̌}] + Ě_{x₁}[τ_{B̌}]`).
* **Theorem 11.1.4** (`theorem_11_1_4`, p. 260): a `ψ`-irreducible chain is positive iff it is
  regular on a full absorbing set. The key step is `exists_regularSet_of_isPositive`.
* **Theorem 11.0.1** (`theorem_11_0_1`, p. 257): for a Harris chain with invariant measure `π`,
  `π(X) < ∞` iff (11.3) holds for a non-empty petite set iff (V2) holds for a petite set and a
  `V` finite somewhere; `theorem_11_0_1_sublevel`: under (V2) the chain is regular on the full
  absorbing set `{V < ∞}`, and sublevel sets in `B⁺(X)` satisfy (11.3).

**The route to Theorem 11.1.4.** The book passes to an `m`-skeleton with a Nummelin splitting
(Proposition 5.4.5), which needs aperiodicity, and does not say why the absorbing set of the
skeleton is absorbing for `Φ`. Here the proof uses the *lazy chain* `K = ½ (I + P)`
(`lazyKernel`): it has the same invariant probabilities and the same maximal irreducibility
measure as `P` for every power `Kᵐ` (`isMaximalIrreducibility_lazy_pow`, from
`lazy_pow_ge`/`lazy_pow_le`: `2⁻ⁿ Σ_{j≤n} Pʲ ≤ Kⁿ ≤ Σ_{j≤n} Pʲ`), its skeleton `Kᴹ` has a
minorization on any `νᴹ`-small set `C ∈ B⁺(X)` with `ν(C) > 0` (Theorem 5.2.2), and
`E_x[τ_B] ≤ E^K_x[τ_B] ≤ M E^{Kᴹ}_x[τ_B]` (`meanReturnTime_le_lazy`, by minimality of the solutions
of Theorem 11.3.5 (iii), and `meanReturnTime_le_skeleton`, pathwise `τ_B ≤ M τ_B^{(M)}`). So a
regular set of `Kᴹ` is regular for `P`, and Proposition 11.3.13 supplies the absorbing set.

**Corrections.**
* (11.12): the book's condition `Σ_j Π_{k ≤ j} β_k = ∞` for non-regularity is wrong; for `β ≡ 1`
  the sum is infinite but the chain is regular (`nullSet_example_counterexample`). The correct
  condition is `Σ_j Π_{k ≤ j} (1 − β_k) = ∞`, which gives `E_1[τ_0] = ∞` (`nullSet_example`).
* Theorem 11.0.1 (ii) needs `C ≠ ∅` (as for Theorem 10.0.1: `∅` is petite with
  `sup_{x∈∅} E_x[τ_∅] = 0`). The final claim, that every sublevel set of `V` satisfies (11.3),
  needs the sublevel set to be in `B⁺(X)`: `theorem_11_0_1_counterexample` is a positive Harris
  chain on `Bool` (`toFalseKernel`) with a solution of (V2) whose sublevel set `{true}` has
  `E_true[τ_{true}] = ∞`.

**Hypotheses.** Proposition 11.1.3 is stated with a minorization on a set in `B⁺(X)` (strong
aperiodicity with the small set in `B⁺(X)`), as for Propositions 8.2.2 and 10.4.2: the split atom
must be accessible. Theorem 11.1.4 itself needs no aperiodicity.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### Atoms -/

/-- On an atom, `E_y[τ_B]` does not depend on `y ∈ α`. -/
theorem IsAtom.meanReturnTime_eq [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α) {B : Set X}
    (hB : MeasurableSet B) {x y : X} (hx : x ∈ α) (hy : y ∈ α) :
    meanReturnTime P B x = meanReturnTime P B y := by
  obtain ⟨-, ν, hν⟩ := hα
  rw [meanReturnTime_eq_one_add P hB x, meanReturnTime_eq_one_add P hB y, hν x hx, hν y hy]

/-- A non-empty atom is small, hence petite. -/
theorem IsAtom.isPetite [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α) (hne : α.Nonempty) :
    IsPetite P α := by
  obtain ⟨hm, ν, hν⟩ := hα
  obtain ⟨a, ha⟩ := hne
  refine ⟨_, _, proposition_5_5_3 (m := 1) (ν := P a) ⟨hm, one_pos,
    IsProbabilityMeasure.ne_zero _, fun x hx => ?_⟩⟩
  rw [pow_one, hν x hx, hν a ha]

variable [MeasurableSpace.CountablyGenerated X] in
/-- An accessible atom with `E_a[τ_α] < ∞` is a regular set. -/
theorem IsAccessibleAtom.isRegularSet [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) (hfin : meanReturnTime P α a ≠ ∞) :
    IsRegularSet P ψ α :=
  ((theorem_11_3_14 h.2.1).1 ⟨h.1.isPetite ⟨a, ha⟩, ⟨a, ha⟩, _, hfin, fun _ hx =>
    (h.1.meanReturnTime_eq h.1.1 hx ha).le⟩).1

/-! ### Regularity implies positivity -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- A regular set in `B⁺(X)` makes the chain positive (Theorem 10.4.10 (ii)). -/
theorem isPositive_of_isRegularSet [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {R : Set X} (hR : IsRegularSet P ψ R) (hψR : 0 < ψ R) :
    IsPositive P ψ := by
  obtain ⟨M, hM, hbound⟩ := hR.2 R hR.1 hψR
  exact (theorem_10_4_10_ii hψ (proposition_11_3_8 hψ hR) hψR hM hbound).1

/-- If the chain is regular on a full set `S`, some regular set lies in `B⁺(X)`. -/
theorem IsRegularOn.exists_pos [IsMarkovKernel P] {ψ : Measure X} (hψ : ψ ≠ 0) {S : Set X}
    (h : IsRegularOn P ψ S) (hfull : IsFull ψ S) : ∃ R, IsRegularSet P ψ R ∧ 0 < ψ R := by
  obtain ⟨Cs, hCs, hcov⟩ := h
  by_contra hc
  push Not at hc
  apply hψ
  rw [← Measure.measure_univ_eq_zero]
  refine le_antisymm ?_ zero_le
  calc ψ univ ≤ ψ S + ψ Sᶜ := by
        rw [← union_compl_self S]; exact measure_union_le _ _
    _ = 0 := by
      rw [hfull, add_zero, ← hcov]
      exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc _ (hCs n))

variable [MeasurableSpace.CountablyGenerated X] in
/-- A regular chain is positive Harris recurrent. -/
theorem IsRegularChain.isPositiveHarris [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (h : IsRegularChain P ψ) : IsPositiveHarris P ψ := by
  obtain ⟨C, hC, hfin, M, hM, hbound⟩ := (theorem_11_3_15 hψ).2.1 h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
  have hne := nonempty_of_meanReturnTime_ne_top hCm (hfin x₀)
  have hψC := (theorem_8_3_6_i P hψ hC hne fun y _ =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (hfin y)).2
  exact (theorem_10_4_10_ii hψ hC hψC hM hbound).2.2 hfin

/-! ### Theorem 11.1.2: chains with an atom -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.1.2 (i)** (MT p. 258): for an accessible atom `α` of a positive chain, the set
`S = {x : E_x[τ_α] < ∞}` is full and absorbing, and the chain is regular on `S`. -/
theorem theorem_11_1_2_i [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) (hpos : IsPositive P ψ) :
    IsFull ψ {x | meanReturnTime P α x ≠ ∞} ∧ IsAbsorbing P {x | meanReturnTime P α x ≠ ∞} ∧
      IsRegularOn P ψ {x | meanReturnTime P α x ≠ ∞} := by
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
  have hfin := (theorem_10_2_2 h ha).1.1 hpos
  have hreg := h.isRegularSet ha hfin
  have hS : {x | regV P α x ≠ ∞} = {x | meanReturnTime P α x ≠ ∞} := by
    ext x
    simp only [mem_ofPred_eq]
    by_cases hx : x ∈ α
    · rw [regV_of_mem P h.1.1 hx, h.1.meanReturnTime_eq h.1.1 hx ha]
      exact ⟨fun _ => hfin, fun _ => ENNReal.one_ne_top⟩
    · rw [regV, meanHitTime_of_notMem P h.1.1 hx, ENNReal.add_ne_top]
      exact ⟨fun h => h.2, fun h => ⟨ENNReal.one_ne_top, h⟩⟩
  obtain ⟨-, hfull, habs, hon⟩ := proposition_11_3_13 h.2.1 hreg h.2.2
  rw [hS] at hfull habs hon
  exact ⟨hfull, habs, hon⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.1.2 (ii)** (MT p. 258): for an accessible atom `α`, the chain is regular iff
`E_x[τ_α] < ∞` for every `x` (11.9). -/
theorem theorem_11_1_2_ii [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) :
    IsRegularChain P ψ ↔ ∀ x, meanReturnTime P α x ≠ ∞ := by
  constructor
  · rintro ⟨Cs, hCs, hcov⟩ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
    obtain ⟨M, hM, hbound⟩ := (hCs m).2 α h.1.1 h.2.2
    exact ne_top_of_le_ne_top hM (hbound x hm)
  · intro hfin
    obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero h.2.2.ne'
    exact (theorem_11_3_15 h.2.1).2.2 ⟨α, h.1.isPetite ⟨a, ha⟩, hfin, _, hfin a,
      fun x hx => (h.1.meanReturnTime_eq h.1.1 hx ha).le⟩

/-! ### Proposition 11.1.1: countable spaces -/

/-- **Proposition 11.1.1** (MT p. 258): for an irreducible chain on a countable space (a maximal
irreducibility measure charging every state), positive recurrence and regularity are
equivalent. -/
theorem proposition_11_1_1 [Countable X] [MeasurableSingletonClass X] [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hpt : ∀ x, 0 < ψ {x}) :
    IsPositive P ψ ↔ IsRegularChain P ψ := by
  refine ⟨fun hpos => ?_, fun h => (h.isPositiveHarris hψ).2⟩
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
  have hatom : IsAccessibleAtom P ψ {x₀} := ⟨isAtom_singleton P x₀, hψ, hpt x₀⟩
  obtain ⟨hfull, -, hon⟩ := theorem_11_1_2_i hatom hpos
  have huniv : {x | meanReturnTime P {x₀} x ≠ ∞} = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_contra hx
    have : ψ {x} = 0 := measure_mono_null (singleton_subset_iff.2 hx) hfull
    exact (hpt x).ne' this
  rw [huniv] at hon
  exact hon

/-! ### The split chain: Proposition 11.1.3 -/

/-- **Hitting times through the split chain** (proof of Proposition 11.1.3):
`E_x[τ_B] ≤ Ě_{x₀}[τ_{B̌}] + Ě_{x₁}[τ_{B̌}]` with `B̌ = B × {0, 1}`. -/
theorem meanReturnTime_le_split [IsMarkovKernel P] (M : Minorization P) {B : Set X}
    (hB : MeasurableSet B) (x : X) :
    haveI := M.isMarkovKernel_splitKernel
    meanReturnTime P B x ≤ meanReturnTime M.splitKernel (Prod.fst ⁻¹' B) (x, false) +
      meanReturnTime M.splitKernel (Prod.fst ⁻¹' B) (x, true) := by
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_pathKernel M.splitKernel
  have hBs : MeasurableSet (Prod.fst ⁻¹' B : Set (X × Bool)) := measurable_fst hB
  have hm := measurable_meanReturnTime M.splitKernel hBs
  have h1 : meanReturnTime P B x = ∫⁻ z, meanReturnTime M.splitKernel (Prod.fst ⁻¹' B) z
      ∂M.split (Measure.dirac x) := by
    rw [meanReturnTime, ← pathMeasure_dirac,
      ← M.lintegral_split_fst (Measure.dirac x) (measurable_toENNReal_firstReturn hB),
      pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
        (f := fun ω : ℕ → X × Bool => ENat.toENNReal (firstReturn B fun n => (ω n).1))
        (measurable_toENNReal_firstReturn hBs).aemeasurable]
    rfl
  have hF : Measurable fun y : X =>
      (1 - M.splitProb y) * meanReturnTime M.splitKernel (Prod.fst ⁻¹' B) (y, false) +
        M.splitProb y * meanReturnTime M.splitKernel (Prod.fst ⁻¹' B) (y, true) := by
    exact ((measurable_const.sub M.measurable_splitProb).mul
      (hm.comp (measurable_id.prodMk measurable_const))).add
      (M.measurable_splitProb.mul (hm.comp (measurable_id.prodMk measurable_const)))
  rw [h1, M.lintegral_split _ hm, lintegral_dirac' _ hF]
  exact add_le_add (mul_le_of_le_one_left' tsub_le_self)
    (mul_le_of_le_one_left' (M.splitProb_le_one x))

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 11.1.3**, core (MT p. 259): if a positive chain has a minorization on a set
`C ∈ B⁺(X)`, there is a regular set in `B⁺(X)`. The proof splits the chain: the atom `α̌ = C₁`
of `Φ̌` is regular (Kac's theorem and Theorem 11.3.14), `V̌ = V_{α̌}` solves (V2) for `Φ̌`, and the
sets `{x : V̌(x₀) ≤ n}` are regular for `Φ` by `meanReturnTime_le_split`. -/
theorem exists_regular_of_minorization [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hpos : IsPositive P ψ) (M : Minorization P)
    (hψC : 0 < ψ M.C) : ∃ R, IsRegularSet P ψ R ∧ 0 < ψ R := by
  have := M.isMarkovKernel_splitKernel
  have hψs := M.isMaximalIrreducibility_split hψ
  have hαpos : 0 < M.split ψ M.checkAlpha := by
    rw [Minorization.checkAlpha, M.split_apply_true ψ M.measurableSet_C, inter_self]
    exact ENNReal.mul_pos M.δ_pos.ne' hψC.ne'
  have hatom : IsAccessibleAtom M.splitKernel (M.split ψ) M.checkAlpha :=
    ⟨M.isAtom_checkAlpha, hψs, hαpos⟩
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hposs : IsPositive M.splitKernel (M.split ψ) := by
    obtain ⟨-, π, hπ, hinv⟩ := hpos
    exact ⟨hψs, M.split π, M.isProbabilityMeasure_split π, (proposition_10_4_1_ii M).2 hinv⟩
  have hfin := (theorem_10_2_2 hatom ha).1.1 hposs
  have hreg := hatom.isRegularSet ha hfin
  obtain ⟨hpet, b, hb, hdrift, -⟩ := theorem_11_3_11_ii hψs hreg hαpos
  obtain ⟨-, hfull, -, -⟩ := proposition_11_3_13 hψs hreg hαpos
  have hVm := measurable_regV M.splitKernel M.measurableSet_checkAlpha
  -- on the bottom level `V̌` is bounded
  set K₁ := 1 + meanReturnTime M.splitKernel M.checkAlpha (c, true) with hK₁
  have hV1 : ∀ x, regV M.splitKernel M.checkAlpha (x, true) ≤ K₁ := fun x =>
    (regV_le M.splitKernel M.measurableSet_checkAlpha (x, true)).trans (add_le_add le_rfl
      (M.isAtom_bottom.meanReturnTime_eq M.measurableSet_checkAlpha
        ⟨mem_univ _, mem_singleton _⟩ ⟨mem_univ _, mem_singleton _⟩).le)
  have hK₁ne : K₁ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin⟩
  set R : ℕ → Set X := fun n => {x | regV M.splitKernel M.checkAlpha (x, false) ≤ n} with hRdef
  have hV0m : Measurable fun x : X => regV M.splitKernel M.checkAlpha (x, false) :=
    hVm.comp (measurable_id.prodMk measurable_const)
  have hR : ∀ n, IsRegularSet P ψ (R n) := fun n => by
    refine ⟨measurableSet_le hV0m measurable_const, fun B hB hψB => ?_⟩
    have hψBs : 0 < M.split ψ (Prod.fst ⁻¹' B) := by rwa [M.split_fst_preimage ψ hB]
    obtain ⟨c', hc', hbound⟩ := theorem_11_3_11_i hψs hVm hb hpet hdrift (measurable_fst hB) hψBs
    refine ⟨(n + c') + (K₁ + c'), by simp [hc', hK₁ne], fun x hx => ?_⟩
    refine (meanReturnTime_le_split M hB x).trans (add_le_add ?_ ?_)
    · exact (hbound _).trans (add_le_add hx le_rfl)
    · exact (hbound _).trans (add_le_add (hV1 x) le_rfl)
  -- some `R n` lies in `B⁺(X)`
  set A := {x | regV M.splitKernel M.checkAlpha (x, false) = ∞} with hAdef
  have hAm : MeasurableSet A := hV0m (measurableSet_singleton ∞)
  have hA0 : ψ A = 0 := by
    have h1 := M.one_sub_mul_le_split_false ψ hAm
    have h2 : M.split ψ (A ×ˢ {false}) = 0 := measure_mono_null (fun z hz => by
      obtain ⟨hz1, hz2⟩ := hz
      obtain ⟨x, b'⟩ := z
      simp only [mem_singleton_iff] at hz2
      subst hz2
      simp only [mem_compl_iff, mem_ofPred_eq, not_not]
      exact hz1) hfull
    rw [h2, nonpos_iff_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left M.one_sub_δ_ne_zero
  by_contra hcon
  push Not at hcon
  apply hψ.1
  rw [← Measure.measure_univ_eq_zero]
  refine le_antisymm ?_ zero_le
  calc ψ univ ≤ ψ (⋃ n, R n) + ψ A := by
        refine (measure_mono fun x _ => ?_).trans (measure_union_le _ _)
        by_cases hx : regV M.splitKernel M.checkAlpha (x, false) = ∞
        · exact Or.inr hx
        · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
          exact Or.inl (mem_iUnion.2 ⟨n, hn.le⟩)
    _ = 0 := by
        rw [hA0, add_zero]
        exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon _ (hR n))

/-! ### Irreducibility from reachability at some time `j ≥ 0` -/

/-- If every state reaches every `A` with `φ(A) > 0` at some time `j ≥ 0` (time `0` allowed),
the chain is `φ`-irreducible. -/
theorem isPhiIrreducible_of_pow_pos [IsMarkovKernel P] {φ : Measure X}
    (h : ∀ A, MeasurableSet A → 0 < φ A → ∀ x, ∃ j, 0 < (P ^ j) x A) : IsPhiIrreducible P φ := by
  intro A hA hφA x
  have hoff : ∀ y ∉ A, 0 < hitProb P A y := fun y hy => by
    obtain ⟨j, hj⟩ := h A hA hφA y
    rcases j with _ | n
    · rw [pow_zero_apply, Measure.dirac_apply' _ hA, indicator_of_notMem hy] at hj
      exact absurd hj (lt_irrefl 0)
    · exact (hitProb_pos_iff P hA y).2 ⟨n, hj⟩
  by_cases hx : x ∈ A
  · rw [hitProb_first_step P hA x]
    by_cases hPA : 0 < P x A
    · exact lt_of_lt_of_le hPA le_self_add
    · have hPA0 : P x A = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hPA)
      have hL := measurable_hitProb P hA
      refine lt_of_lt_of_le ?_ le_add_self
      rw [lintegral_pos_iff_support hL, Measure.restrict_apply (measurableSet_support hL)]
      have hc : P x Aᶜ = 1 := by rw [prob_compl_eq_one_sub hA, hPA0, tsub_zero]
      calc (0 : ℝ≥0∞) < P x Aᶜ := by rw [hc]; exact one_pos
        _ ≤ _ := measure_mono fun y (hy : y ∈ Aᶜ) =>
          (⟨(hoff y hy).ne', hy⟩ : y ∈ Function.support (hitProb P A) ∩ Aᶜ)
  · exact hoff x hx

/-! ### The lazy chain `½ (I + P)` -/

/-- The weights `½ δ₀ + ½ δ₁` of the lazy chain. -/
noncomputable def lazyWeights (n : ℕ) : ℝ≥0∞ := if n ≤ 1 then 2⁻¹ else 0

/-- The lazy chain `K = ½ (I + P)`: stay put or move by `P`, with probability `½` each. It is the
sampled chain `K_a` with `a = ½ δ₀ + ½ δ₁`. -/
noncomputable abbrev lazyKernel (P : Kernel X X) : Kernel X X := sampledKernel P lazyWeights

/-- `½ δ₀ + ½ δ₁` is a sampling distribution. -/
theorem isSamplingDist_lazyWeights : IsSamplingDist lazyWeights := by
  unfold IsSamplingDist
  rw [tsum_eq_sum (s := Finset.range 2) fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn; simp [lazyWeights]; omega]
  simp [lazyWeights, Finset.sum_range_succ, ENNReal.inv_two_add_inv_two]

/-- The lazy chain is a transition kernel. -/
theorem isMarkovKernel_lazyKernel (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovKernel (lazyKernel P) :=
  isMarkovKernel_sampledKernel P isSamplingDist_lazyWeights

/-- `∫ f dK(x, ·) = ½ f(x) + ½ Pf(x)`. -/
theorem lintegral_lazyKernel (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ∫⁻ y, f y ∂lazyKernel P x = 2⁻¹ * f x + 2⁻¹ * ∫⁻ y, f y ∂P x := by
  rw [lintegral_sampledKernel_eq, tsum_eq_sum (s := Finset.range 2) fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    simp only [lazyWeights, mul_eq_zero, ite_eq_right_iff]
    exact Or.inl fun h => absurd h (by omega)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero_apply,
    pow_one, lintegral_dirac' _ hf]
  simp [lazyWeights]

/-- `Kⁿ⁺¹(x, A) = ½ Kⁿ(x, A) + ½ ∫ P(x, dy) Kⁿ(y, A)`. -/
theorem lazy_pow_succ_apply (P : Kernel X X) (n : ℕ) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    (lazyKernel P ^ (n + 1)) x A =
      2⁻¹ * (lazyKernel P ^ n) x A + 2⁻¹ * ∫⁻ y, (lazyKernel P ^ n) y A ∂P x := by
  rw [pow_succ_apply _ n x hA, lintegral_lazyKernel P (Kernel.measurable_coe _ hA)]

/-- **Lower bound for the lazy chain**: `Kⁿ(x, A) ≥ 2⁻ⁿ Σ_{j ≤ n} Pʲ(x, A)`. -/
theorem lazy_pow_ge (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    2⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (P ^ j) x A ≤ (lazyKernel P ^ n) x A := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [lazy_pow_succ_apply P n x hA]
    have h2 : 2⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (P ^ (j + 1)) x A ≤
        ∫⁻ y, (lazyKernel P ^ n) y A ∂P x := by
      calc 2⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (P ^ (j + 1)) x A
          = ∫⁻ y, 2⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (P ^ j) y A ∂P x := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ =>
              Kernel.measurable_coe _ hA), lintegral_finsetSum _ fun j _ =>
                Kernel.measurable_coe _ hA]
            simp_rw [pow_succ_apply P _ x hA]
        _ ≤ _ := lintegral_mono fun y => ih y
    calc 2⁻¹ ^ (n + 1) * ∑ j ∈ Finset.range (n + 1 + 1), (P ^ j) x A
        ≤ 2⁻¹ ^ (n + 1) * (∑ j ∈ Finset.range (n + 1), (P ^ j) x A +
            ∑ j ∈ Finset.range (n + 1), (P ^ (j + 1)) x A) := by
          refine mul_le_mul' le_rfl ?_
          rw [Finset.sum_range_succ' (fun j => (P ^ j) x A) (n + 1), add_comm]
          exact add_le_add (Finset.single_le_sum (f := fun j => (P ^ j) x A)
            (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.succ_pos n))) le_rfl
      _ = 2⁻¹ * (2⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (P ^ j) x A) +
          2⁻¹ * (2⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (P ^ (j + 1)) x A) := by ring
      _ ≤ _ := add_le_add (mul_le_mul' le_rfl (ih x)) (mul_le_mul' le_rfl h2)

/-- **Upper bound for the lazy chain**: `Kⁿ(x, A) ≤ Σ_{j ≤ n} Pʲ(x, A)`. -/
theorem lazy_pow_le (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (lazyKernel P ^ n) x A ≤ ∑ j ∈ Finset.range (n + 1), (P ^ j) x A := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [lazy_pow_succ_apply P n x hA]
    set S := ∑ j ∈ Finset.range (n + 1 + 1), (P ^ j) x A with hS
    have h1 : ∑ j ∈ Finset.range (n + 1), (P ^ j) x A ≤ S := by
      rw [hS, Finset.sum_range_succ (fun j => (P ^ j) x A) (n + 1)]; exact le_self_add
    have h2 : ∫⁻ y, (lazyKernel P ^ n) y A ∂P x ≤ S := by
      calc ∫⁻ y, (lazyKernel P ^ n) y A ∂P x
          ≤ ∫⁻ y, ∑ j ∈ Finset.range (n + 1), (P ^ j) y A ∂P x := lintegral_mono fun y => ih y
        _ = ∑ j ∈ Finset.range (n + 1), (P ^ (j + 1)) x A := by
            rw [lintegral_finsetSum _ fun j _ => Kernel.measurable_coe _ hA]
            simp_rw [pow_succ_apply P _ x hA]
        _ ≤ S := by
            rw [hS, Finset.sum_range_succ' (fun j => (P ^ j) x A) (n + 1)]; exact le_self_add
    calc 2⁻¹ * (lazyKernel P ^ n) x A + 2⁻¹ * ∫⁻ y, (lazyKernel P ^ n) y A ∂P x
        ≤ 2⁻¹ * S + 2⁻¹ * S := add_le_add (mul_le_mul' le_rfl ((ih x).trans h1))
          (mul_le_mul' le_rfl h2)
      _ = S := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- For `m ≥ 1`, `ψ` is a maximal irreducibility measure for the skeleton `Kᵐ` of the lazy chain. -/
theorem isMaximalIrreducibility_lazy_pow [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {m : ℕ} (hm : 1 ≤ m) :
    haveI := isMarkovKernel_lazyKernel P
    haveI := isMarkovKernel_pow (lazyKernel P) m
    IsMaximalIrreducibility (lazyKernel P ^ m) ψ := by
  have := isMarkovKernel_lazyKernel P
  have := isMarkovKernel_pow (lazyKernel P) m
  -- reachability for `Kᵐ` in terms of `P`
  have hiff : ∀ A, MeasurableSet A → ∀ x n, 0 < ((lazyKernel P ^ m) ^ (n + 1)) x A →
      ∃ j, 0 < (P ^ j) x A := fun A hA x n hpos => by
    rw [← pow_mul] at hpos
    by_contra hc
    push Not at hc
    have := (lazy_pow_le P (m * (n + 1)) x hA).trans_lt' hpos
    rw [Finset.sum_eq_zero fun j _ => nonpos_iff_eq_zero.1 (hc j)] at this
    exact lt_irrefl 0 this
  refine ⟨hψ.1, fun A hA hψA x => ?_, fun φ hφ => hψ.2.2 φ
    (isPhiIrreducible_of_pow_pos fun A hA hφA x => ?_)⟩
  · obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA x).1 (hψ.2.1 A hA hψA x)
    refine (hitProb_pos_iff _ hA x).2 ⟨n, ?_⟩
    rw [← pow_mul]
    refine lt_of_lt_of_le ?_ (lazy_pow_ge P (m * (n + 1)) x hA)
    refine ENNReal.mul_pos (pow_ne_zero _ (by simp)) (lt_of_lt_of_le hn
      (Finset.single_le_sum (f := fun j => (P ^ j) x A) (fun _ _ => zero_le)
        (Finset.mem_range.2 (by nlinarith)))).ne'
  · obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA x).1 (hφ A hA hφA x)
    exact hiff A hA x n hn

/-- A positive chain has a positive lazy skeleton `Kᵐ`, `m ≥ 1`. -/
theorem isPositive_lazy_pow [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ) {m : ℕ}
    (hm : 1 ≤ m) :
    haveI := isMarkovKernel_lazyKernel P
    haveI := isMarkovKernel_pow (lazyKernel P) m
    IsPositive (lazyKernel P ^ m) ψ := by
  obtain ⟨hψ, π, hπ, hinv⟩ := hpos
  exact ⟨isMaximalIrreducibility_lazy_pow hψ hm, π, hπ,
    (hinv.sampledKernel isSamplingDist_lazyWeights).pow m⟩

/-- **Hitting times of the lazy chain**: `E_x[τ_B] ≤ E^K_x[τ_B]`. The proof compares minimal
solutions (Theorem 11.3.5 (iii)): `½ E^K_·[σ_B]` solves `PW + 1 ≤ W` off `B`. -/
theorem meanReturnTime_le_lazy [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B) (x : X) :
    haveI := isMarkovKernel_lazyKernel P
    meanReturnTime P B x ≤ meanReturnTime (lazyKernel P) B x := by
  have := isMarkovKernel_lazyKernel P
  set h := meanHitTime (lazyKernel P) B with hhdef
  have hm : Measurable h := measurable_meanHitTime _ hB
  have hK := (theorem_11_3_5_iii (lazyKernel P) hB).1
  have hW : ∀ y ∉ B, ∫⁻ z, 2⁻¹ * h z ∂P y + 1 ≤ 2⁻¹ * h y := fun y hy => by
    have h1 := hK y hy
    rw [lintegral_lazyKernel P hm] at h1
    rw [lintegral_const_mul _ hm]
    by_cases hinf : h y = ∞
    · rw [hinf, ENNReal.mul_top (by simp)]; exact le_top
    · have hne : 2⁻¹ * h y ≠ ∞ := ENNReal.mul_ne_top (by simp) hinf
      have h2 : 2⁻¹ * h y + (2⁻¹ * ∫⁻ z, h z ∂P y + 1) ≤ 2⁻¹ * h y + 2⁻¹ * h y := by
        rw [← add_assoc, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]; exact h1
      exact (ENNReal.add_le_add_iff_left hne).1 h2
  have hmin := (theorem_11_3_5_iii P hB).2 _ (hm.const_mul _) hW
  rw [meanReturnTime_eq_one_add P hB x, meanReturnTime_eq_one_add _ hB x,
    lintegral_lazyKernel P hm]
  refine add_le_add le_rfl ((lintegral_mono hmin).trans ?_)
  rw [lintegral_const_mul _ hm]
  exact le_add_self

/-! ### Skeletons -/

omit [MeasurableSpace X] in
/-- `ω_{τ_A} ∈ A` when `τ_A < ∞`. -/
theorem mem_of_firstReturn_eq {A : Set X} {ω : ℕ → X} {t : ℕ}
    (h : firstReturn A ω = WithTop.some t) : ω t ∈ A := by
  by_contra hc
  have h1 := (le_firstReturn_iff A ω t).1 (le_of_eq h.symm)
  have h2 : WithTop.some (t + 1) ≤ firstReturn A ω := (le_firstReturn_iff A ω (t + 1)).2
    fun j hj1 hjt => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjt with hj | hj
      · exact h1 j hj1 hj
      · rw [hj]; exact hc
  rw [h] at h2
  exact absurd (WithTop.coe_le_coe.1 h2) (by omega)

omit [MeasurableSpace X] in
/-- `τ_A ≤ j` whenever `Φ_j ∈ A` with `j ≥ 1`. -/
theorem firstReturn_le_of_mem {A : Set X} {ω : ℕ → X} {j : ℕ} (hj : 1 ≤ j) (hA : ω j ∈ A) :
    firstReturn A ω ≤ WithTop.some j := by
  by_contra hc
  have h1 : WithTop.some (j + 1) ≤ firstReturn A ω := by
    cases h : firstReturn A ω with
    | top => exact le_top
    | coe t =>
      rw [h] at hc
      exact WithTop.coe_le_coe.2 (by have := WithTop.coe_lt_coe.1 (not_le.1 hc); omega)
  exact (le_firstReturn_iff A ω (j + 1)).1 h1 j hj (Nat.lt_succ_self j) hA

/-- **Hitting times of a skeleton** (proof of Theorem 11.1.4): `τ_B ≤ m τ_B^{(m)}`, hence
`E_x[τ_B] ≤ m E^{(m)}_x[τ_B]` for the `m`-skeleton `Pᵐ`, `m ≥ 1`. -/
theorem meanReturnTime_le_skeleton [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m) {B : Set X}
    (hB : MeasurableSet B) (x : X) :
    haveI := isMarkovKernel_pow P m
    meanReturnTime P B x ≤ m * meanReturnTime (P ^ m) B x := by
  have := isMarkovKernel_pow P m
  have := isMarkovKernel_pathKernel P
  set s : (ℕ → X) → (ℕ → X) := fun ω n => ω (m * n) with hsdef
  have hs : Measurable s := measurable_pi_iff.2 fun n => measurable_pi_apply (m * n)
  have hpath : ∀ ω, ENat.toENNReal (firstReturn B ω) ≤
      m * ENat.toENNReal (firstReturn B (s ω)) := fun ω => by
    cases h : firstReturn B (s ω) with
    | top =>
      rw [show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top,
        ENNReal.mul_top (by exact_mod_cast (show m ≠ 0 by omega))]
      exact le_top
    | coe t =>
      have ht1 : 1 ≤ t := by
        have := one_le_firstReturn B (s ω)
        rw [h] at this
        exact WithTop.coe_le_coe.1 this
      have hmem : s ω t ∈ B := mem_of_firstReturn_eq h
      have hle := firstReturn_le_of_mem (show 1 ≤ m * t by nlinarith) hmem
      calc ENat.toENNReal (firstReturn B ω) ≤ ENat.toENNReal (WithTop.some (m * t)) :=
            ENat.toENNReal_mono hle
        _ = m * ENat.toENNReal (WithTop.some t) := by
            rw [toENNReal_some, toENNReal_some, Nat.cast_mul]
  have hlaw : (pathKernel P x).map s = pathKernel (P ^ m) x := by
    have h := law_eq_pathMeasure (skeleton P m) (Measure.dirac x)
      (skeleton_isMarkovChain P (Measure.dirac x) m)
    rwa [pathMeasure_dirac, pathMeasure_dirac] at h
  calc meanReturnTime P B x ≤ ∫⁻ ω, m * ENat.toENNReal (firstReturn B (s ω)) ∂pathKernel P x :=
        lintegral_mono hpath
    _ = m * ∫⁻ ω, ENat.toENNReal (firstReturn B ω) ∂(pathKernel P x).map s := by
        rw [lintegral_const_mul _ (f := fun ω => ENat.toENNReal (firstReturn B (s ω)))
          ((measurable_toENNReal_firstReturn hB).comp hs),
          lintegral_map (f := fun ω => ENat.toENNReal (firstReturn B ω))
            (measurable_toENNReal_firstReturn hB) hs]
    _ = m * meanReturnTime (P ^ m) B x := by rw [hlaw]; rfl

/-! ### Theorem 11.1.4 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The key step of Theorem 11.1.4**: a positive chain has a regular set in `B⁺(X)`. The lazy
chain `K = ½ (I + P)` has the same invariant probability and the same irreducibility measures, and
for a small set `C ∈ B⁺(X)` with `Pᴹ ≥ ν` on `C`, `ν(C) > 0` (Theorem 5.2.2), the skeleton `Kᴹ`
has a minorization on `C`; Proposition 11.1.3 gives a regular set for `Kᴹ`, and
`E_x[τ_B] ≤ E^K_x[τ_B] ≤ M E^{Kᴹ}_x[τ_B]`. -/
theorem exists_regularSet_of_isPositive [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) : ∃ R, IsRegularSet P ψ R ∧ 0 < ψ R := by
  have hψ := hpos.1
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hM : 1 ≤ M := hC.2.1
  have := isMarkovKernel_lazyKernel P
  have := isMarkovKernel_pow (lazyKernel P) M
  -- a minorization for `Kᴹ` on `C`
  have hle : ∀ x ∈ C, (2⁻¹ : ℝ≥0∞) ^ M • ν ≤ (lazyKernel P ^ M) x := fun x hx =>
    Measure.le_intro fun A hA _ => by
      rw [Measure.smul_apply, smul_eq_mul]
      calc 2⁻¹ ^ M * ν A ≤ 2⁻¹ ^ M * ∑ j ∈ Finset.range (M + 1), (P ^ j) x A := by
            refine mul_le_mul' le_rfl ((hC.le_apply hx A).trans ?_)
            exact Finset.single_le_sum (f := fun j => (P ^ j) x A) (fun _ _ => zero_le)
              (Finset.mem_range.2 (Nat.lt_succ_self M))
        _ ≤ _ := lazy_pow_ge P M x hA
  have hpos' : 0 < ((2⁻¹ : ℝ≥0∞) ^ M • ν) C := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos (pow_ne_zero _ (by simp)) hνC.ne'
  have hfin' : ((2⁻¹ : ℝ≥0∞) ^ M • ν) C ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ne_top_of_le_ne_top
      ENNReal.one_ne_top ((measure_mono (subset_univ C)).trans
        (hC.measure_univ_le (nonempty_of_measure_ne_zero hνC.ne'))))
  set Mn := Minorization.ofLe hC.1 hle hpos' hfin'
  obtain ⟨R, hR, hψR⟩ := exists_regular_of_minorization (isMaximalIrreducibility_lazy_pow hψ hM)
    (isPositive_lazy_pow hpos hM) Mn hψC
  refine ⟨R, ⟨hR.1, fun B hB hψB => ?_⟩, hψR⟩
  obtain ⟨K, hK, hbound⟩ := hR.2 B hB hψB
  refine ⟨M * K, ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) hK, fun x hx => ?_⟩
  calc meanReturnTime P B x ≤ meanReturnTime (lazyKernel P) B x := meanReturnTime_le_lazy hB x
    _ ≤ M * meanReturnTime (lazyKernel P ^ M) B x := meanReturnTime_le_skeleton hM hB x
    _ ≤ M * K := mul_le_mul' le_rfl (hbound x hx)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.1.4** (MT p. 260): a `ψ`-irreducible chain is positive iff there is a full
absorbing set `S` on which the chain is regular (`X = S ∪ N`, (11.15)). -/
theorem theorem_11_1_4 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    IsPositive P ψ ↔ ∃ S, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧ IsRegularOn P ψ S := by
  constructor
  · intro hpos
    obtain ⟨R, hR, hψR⟩ := exists_regularSet_of_isPositive hpos
    obtain ⟨-, hfull, habs, hon⟩ := proposition_11_3_13 hψ hR hψR
    exact ⟨_, (measurableSet_singleton ∞).compl.preimage (measurable_regV P hR.1), hfull, habs,
      hon⟩
  · rintro ⟨S, -, hfull, -, hon⟩
    obtain ⟨R, hR, hψR⟩ := hon.exists_pos hψ.1 hfull
    exact isPositive_of_isRegularSet hψ hR hψR

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 11.1.3** (MT p. 259): a positive chain with a minorization (5.2) on a set
`C ∈ B⁺(X)` (for instance a strongly aperiodic chain whose `ν₁`-small set lies in `B⁺(X)`) has a
full absorbing set `S` on which it is regular. The proof splits the chain
(`exists_regular_of_minorization`). -/
theorem proposition_11_1_3 [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ)
    (M : Minorization P) (hψC : 0 < ψ M.C) :
    ∃ S, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧ IsRegularOn P ψ S := by
  obtain ⟨R, hR, hψR⟩ := exists_regular_of_minorization hpos.1 hpos M hψC
  obtain ⟨-, hfull, habs, hon⟩ := proposition_11_3_13 hpos.1 hR hψR
  exact ⟨_, (measurableSet_singleton ∞).compl.preimage (measurable_regV P hR.1), hfull, habs, hon⟩

/-! ### (11.7) and Theorem 11.0.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- (11.7), MT p. 258: for a positive chain with invariant probability `π` and a measurable `A`
with `π(A) > 0`, `E_x[τ_A] < ∞` for `π`-almost every `x ∈ A` (from (10.32)). -/
theorem eq_11_7 [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hinv : IsInvariant P π) {A : Set X} (hA : MeasurableSet A)
    (hπA : 0 < π A) : ∀ᵐ x ∂π.restrict A, meanReturnTime P A x ≠ ∞ := by
  have h := theorem_10_4_10_i_forall hpos ⟨inferInstance, hinv.isSubinvariant⟩ hA hπA
  filter_upwards [ae_lt_top (measurable_meanReturnTime P hA) h] with x hx
  exact hx.ne

variable [MeasurableSpace.CountablyGenerated X] in
/-- Under (V2) for a petite set, the chain is regular on the full absorbing set `{V < ∞}`, covered
by the regular sublevel sets `{V ≤ n}`; and a sublevel set in `B⁺(X)` is petite with bounded mean
return times (11.3) (MT Theorem 11.0.1, last assertion, p. 257, and Proposition 11.3.13). -/
theorem theorem_11_0_1_sublevel [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞}
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV2 P V b C) (hx : ∃ x, V x ≠ ∞) :
    IsFull ψ {x | V x ≠ ∞} ∧ IsAbsorbing P {x | V x ≠ ∞} ∧ IsRegularOn P ψ {x | V x ≠ ∞} ∧
      ∀ ℓ : ℝ≥0∞, ℓ ≠ ∞ → 0 < ψ {x | V x ≤ ℓ} →
        IsPetite P {x | V x ≤ ℓ} ∧
          ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ {x | V x ≤ ℓ}, meanReturnTime P {x | V x ≤ ℓ} x ≤ M := by
  have hsub : ∀ ℓ : ℝ≥0∞, ℓ ≠ ∞ → IsRegularSet P ψ {x | V x ≤ ℓ} := fun ℓ hℓ =>
    theorem_11_3_11_i_regular hψ hV hb hC h (measurableSet_le hV measurable_const) hℓ
      fun _ hx => hx
  refine ⟨?_, isAbsorbing_finite_of_driftV2 hV hb h, ⟨fun n => {x | V x ≤ n},
    fun n => hsub n (ENNReal.natCast_ne_top n), ?_⟩, fun ℓ hℓ hψℓ => ?_⟩
  · rcases lemma_11_3_6 hψ.2.1 hV hb h with h' | h'
    · exact h'
    · obtain ⟨x, hx⟩ := hx; exact absurd (h' x) hx
  · ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hn, fun hx => ?_⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact ⟨n, hn.le⟩
  · obtain ⟨hpet, -, hM⟩ := (theorem_11_3_14 hψ).2 ⟨hsub ℓ hℓ, hψℓ⟩
    exact ⟨hpet, hM⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.0.1** (MT p. 257), corrected: for a Harris recurrent chain with a nonzero
invariant measure `π`, the following are equivalent: (i) `π(X) < ∞`; (ii) some non-empty petite
set `C` has `sup_{x ∈ C} E_x[τ_C] < ∞` (11.3); (iii) (V2) holds for a petite set `C` and a
function `V` finite at some state (11.4). -/
theorem theorem_11_0_1 [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {π : Measure X}
    (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) :
    (π univ ≠ ∞ ↔ ∃ C, IsPetite P C ∧ C.Nonempty ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M) ∧
    (π univ ≠ ∞ ↔ ∃ (C : Set X) (V : X → ℝ≥0∞) (b : ℝ≥0∞), IsPetite P C ∧ Measurable V ∧
      b ≠ ∞ ∧ (∃ x, V x ≠ ∞) ∧ DriftV2 P V b C) := by
  have hψ := hH.1
  have h12 : π univ ≠ ∞ → ∃ C, IsPetite P C ∧ C.Nonempty ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M := fun hfin => by
    have h0 : π univ ≠ 0 := fun h => hπ0 (Measure.measure_univ_eq_zero.1 h)
    have hpos : IsPositive P ψ := ⟨hψ, (π univ)⁻¹ • π, ⟨by
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin]⟩, hπ.2.smul _⟩
    obtain ⟨R, hR, hψR⟩ := exists_regularSet_of_isPositive hpos
    exact ⟨R, (theorem_11_3_14 hψ).2 ⟨hR, hψR⟩⟩
  have h21 : (∃ C, IsPetite P C ∧ C.Nonempty ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ C, meanReturnTime P C x ≤ M) → π univ ≠ ∞ := by
    rintro ⟨C, hC, hne, M, hM, hbound⟩
    have hψC := ((theorem_11_3_14 hψ).1 ⟨hC, hne, M, hM, hbound⟩).2
    exact (theorem_10_4_10_ii hψ hC hψC hM hbound).2.1 π hπ.isSubinvariantMeasure
  refine ⟨⟨h12, h21⟩, ⟨fun hfin => ?_, fun ⟨C, V, b, hC, hV, hb, hx, h⟩ => h21 ?_⟩⟩
  · obtain ⟨C, hC, ⟨c, hc⟩, M, hM, hbound⟩ := h12 hfin
    have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
    exact ⟨C, regV P C, M, hC, measurable_regV P hCm, hM,
      ⟨c, by rw [regV_of_mem P hCm hc]; exact ENNReal.one_ne_top⟩, regV_drift P hCm hbound⟩
  · obtain ⟨hfull, -, hon, -⟩ := theorem_11_0_1_sublevel hψ hV hb hC h hx
    obtain ⟨R, hR, hψR⟩ := hon.exists_pos hψ.1 hfull
    exact ⟨R, (theorem_11_3_14 hψ).2 ⟨hR, hψR⟩⟩

/-! ### The counterexample for sublevel sets outside `B⁺(X)` -/

/-- The chain on `Bool` that jumps to `false` from every state: `false` is absorbing and `true`
is transient. -/
noncomputable abbrev toFalseKernel : Kernel Bool Bool := Kernel.const Bool (Measure.dirac false)

/-- `Pⁿ⁺¹(x, ·) = δ_false` for the chain `toFalseKernel`. -/
theorem toFalseKernel_pow_succ (n : ℕ) (x : Bool) {A : Set Bool} (hA : MeasurableSet A) :
    (toFalseKernel ^ (n + 1)) x A = Measure.dirac false A := by
  have := isMarkovKernel_pow toFalseKernel n
  rw [pow_succ_apply' _ n x hA]
  simp only [toFalseKernel, Kernel.const_apply]
  rw [lintegral_const, measure_univ, mul_one]

/-- `δ_false` is a maximal irreducibility measure for `toFalseKernel`, and the chain is Harris
recurrent. -/
theorem toFalseKernel_isHarris : IsHarris toFalseKernel (Measure.dirac false) := by
  have hirr : IsPhiIrreducible toFalseKernel (Measure.dirac false) := fun A hA hψA x =>
    (hitProb_pos_iff _ hA x).2 ⟨0, by rwa [toFalseKernel_pow_succ 0 x hA]⟩
  refine ⟨⟨by simp, hirr, fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩,
    fun A hA hψA => (proposition_9_1_1 _ hA fun x _ => ?_).2⟩
  · by_contra hne
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA true).1 (hφ A hA (pos_iff_ne_zero.2 hne) true)
    rw [toFalseKernel_pow_succ n true hA, h0] at hn
    exact lt_irrefl 0 hn
  · have := isMarkovKernel_pathKernel toFalseKernel
    have hfalse : false ∈ A := by
      by_contra h
      rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hψA
      exact lt_irrefl 0 hψA
    refine le_antisymm (hitProb_le_one _ A x) ?_
    calc (1 : ℝ≥0∞) = (toFalseKernel ^ 1) x A := by
          rw [toFalseKernel_pow_succ 0 x hA, Measure.dirac_apply' _ hA, indicator_of_mem hfalse]
          rfl
      _ = pathKernel toFalseKernel x {ω | ω 1 ∈ A} := (pathKernel_coord_mem _ x 1 hA).symm
      _ ≤ hitProb toFalseKernel A x := measure_mono fun ω hω =>
          ne_top_of_le_ne_top WithTop.coe_ne_top (firstReturn_le_of_mem le_rfl hω)

/-- **The sublevel-set claim of Theorem 11.0.1 needs `B⁺(X)`.** For `toFalseKernel` (Harris
recurrent, with invariant probability `δ_false`), `V(false) = 5`, `V(true) = 1` solves (V2) for
the petite set `X` with `b = 5`, but the sublevel set `{V ≤ 1} = {true}` has
`E_true[τ_{true}] = ∞`, so it does not satisfy (11.3). -/
theorem theorem_11_0_1_counterexample :
    IsHarris toFalseKernel (Measure.dirac false) ∧
      IsInvariant toFalseKernel (Measure.dirac false) ∧ IsPetite toFalseKernel univ ∧
      DriftV2 toFalseKernel (fun x => if x then 1 else 5) 5 univ ∧
      {x : Bool | (if x then (1 : ℝ≥0∞) else 5) ≤ 1} = {true} ∧
      meanReturnTime toFalseKernel {true} true = ∞ := by
  have hm : ∀ A : Set Bool, MeasurableSet A := fun A => (Set.toFinite A).measurableSet
  refine ⟨toFalseKernel_isHarris, ?_, ⟨_, _, proposition_5_5_3 (m := 1)
    (ν := Measure.dirac false) ⟨MeasurableSet.univ, one_pos, by simp, fun x _ => ?_⟩⟩,
    fun x => ?_, ?_, ?_⟩
  · simp [IsInvariant, toFalseKernel]
  · rw [pow_one]; simp [toFalseKernel]
  · simp only [toFalseKernel, Kernel.const_apply, indicator_of_mem (mem_univ x)]
    rw [lintegral_dirac' _ (measurable_of_countable _)]
    cases x <;> norm_num
  · ext x; cases x <;> simp
  · by_contra hfin
    have h1 := hitProb_eq_one_of_meanReturnTime_ne_top (hm {true}) hfin
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (hm {true}) true).1 (by rw [h1]; exact one_pos)
    rw [toFalseKernel_pow_succ n true (hm _)] at hn
    simp at hn

/-! ### The example (11.12): the null set `N` can be non-empty -/

/-- The transition law of the chain (11.12) on `ℤ₊`: `0` is absorbing, and from `j ≥ 1` the chain
jumps to `0` with probability `β_j` and to `j + 1` with probability `1 − β_j`. -/
noncomputable def nullSetMeas (β : ℕ → ℝ≥0∞) (j : ℕ) : Measure ℕ :=
  if j = 0 then Measure.dirac 0 else β j • Measure.dirac 0 + (1 - β j) • Measure.dirac (j + 1)

/-- The chain (11.12), MT p. 259. -/
noncomputable def nullSetKernel (β : ℕ → ℝ≥0∞) : Kernel ℕ ℕ :=
  ⟨nullSetMeas β, measurable_of_countable _⟩

/-- (11.12) is a transition kernel when `β_j ≤ 1`. -/
theorem isMarkovKernel_nullSetKernel {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) :
    IsMarkovKernel (nullSetKernel β) := by
  refine ⟨fun j => ⟨?_⟩⟩
  change nullSetMeas β j univ = 1
  unfold nullSetMeas
  split_ifs
  · simp
  · simp [add_tsub_cancel_of_le (hβ j)]

/-- `∫ f dP(j, ·) = β_j f(0) + (1 − β_j) f(j + 1)` for `j ≥ 1`. -/
theorem lintegral_nullSetKernel (β : ℕ → ℝ≥0∞) {j : ℕ} (hj : j ≠ 0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ i, f i ∂nullSetKernel β j = β j * f 0 + (1 - β j) * f (j + 1) := by
  change ∫⁻ i, f i ∂nullSetMeas β j = _
  simp [nullSetMeas, hj, lintegral_add_measure, lintegral_smul_measure]

/-- For (11.12), `E_j[σ_0] ≥ Σ_{n<N} Π_{k<n} (1 − β_{j+k})` for every `j ≥ 1` and `N`. -/
theorem nullSet_meanHitTime_ge {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) (N : ℕ) :
    haveI := isMarkovKernel_nullSetKernel hβ
    ∀ j, j ≠ 0 → ∑ n ∈ Finset.range N, ∏ k ∈ Finset.range n, (1 - β (j + k)) ≤
      meanHitTime (nullSetKernel β) {0} j := by
  have := isMarkovKernel_nullSetKernel hβ
  have h0 : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  have hstep : ∀ j, j ≠ 0 → meanHitTime (nullSetKernel β) {0} j =
      1 + (1 - β j) * meanHitTime (nullSetKernel β) {0} (j + 1) := fun j hj => by
    rw [meanHitTime_of_notMem _ h0 (by simpa using hj), meanReturnTime_eq_one_add _ h0,
      lintegral_nullSetKernel β hj, meanHitTime_of_mem _ h0 (mem_singleton 0), mul_zero,
      zero_add]
  induction N with
  | zero => intro j _; simp
  | succ N ih =>
    intro j hj
    rw [hstep j hj, Finset.sum_range_succ', Finset.prod_range_zero, add_comm]
    refine add_le_add le_rfl ?_
    calc ∑ n ∈ Finset.range N, ∏ k ∈ Finset.range (n + 1), (1 - β (j + k))
        = (1 - β j) * ∑ n ∈ Finset.range N, ∏ k ∈ Finset.range n, (1 - β (j + 1 + k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.prod_range_succ', add_zero, mul_comm]
          congr 1
          exact Finset.prod_congr rfl fun k _ => by rw [add_assoc, add_comm 1 k]
      _ ≤ _ := mul_le_mul' le_rfl (ih (j + 1) (Nat.succ_ne_zero j))

/-- **The example (11.12)**, corrected (MT p. 259). For `0 < β_j ≤ 1`, the chain is positive
(with invariant probability `δ₀`), `{0}` is a regular set in `B⁺`, and if
`Σ_j Π_{k=1}^{j} (1 − β_k) = ∞` then `E_1[τ_0] = ∞` and the chain is not regular. -/
theorem nullSet_example {β : ℕ → ℝ≥0∞} (hβ : ∀ j, β j ≤ 1) (hβpos : ∀ j, j ≠ 0 → 0 < β j) :
    haveI := isMarkovKernel_nullSetKernel hβ
    IsPositive (nullSetKernel β) (Measure.dirac 0) ∧
      IsRegularSet (nullSetKernel β) (Measure.dirac 0) {0} ∧
      ((∑' n, ∏ k ∈ Finset.range n, (1 - β (k + 1)) = ∞) →
        meanReturnTime (nullSetKernel β) {0} 1 = ∞ ∧
          ¬ IsRegularChain (nullSetKernel β) (Measure.dirac 0)) := by
  have := isMarkovKernel_nullSetKernel hβ
  have h0 : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  have hm : ∀ A : Set ℕ, MeasurableSet A := fun A => measurableSet_of_countable A
  have hP0 : nullSetKernel β 0 = Measure.dirac 0 := by
    change nullSetMeas β 0 = _; simp [nullSetMeas]
  -- reaching `0` in one step
  have hreach : ∀ j, 0 < nullSetKernel β j {0} := fun j => by
    by_cases hj : j = 0
    · subst hj; rw [hP0]; simp
    · change 0 < nullSetMeas β j {0}
      simp only [nullSetMeas, hj, ↓reduceIte, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' _ h0, indicator_of_mem (mem_singleton 0)]
      exact lt_of_lt_of_le (by simpa using hβpos j hj) le_self_add
  -- `δ₀` is a maximal irreducibility measure
  have hirr : IsPhiIrreducible (nullSetKernel β) (Measure.dirac 0) := fun A hA hA0 x => by
    have h0A : (0 : ℕ) ∈ A := by
      by_contra h; rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hA0
      exact lt_irrefl 0 hA0
    refine (hitProb_pos_iff _ hA x).2 ⟨0, ?_⟩
    rw [pow_one]
    exact lt_of_lt_of_le (hreach x) (measure_mono (singleton_subset_iff.2 h0A))
  have hψ : IsMaximalIrreducibility (nullSetKernel β) (Measure.dirac 0) := by
    refine ⟨by simp, hirr, fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_⟩
    by_contra hne
    have h0A : (0 : ℕ) ∉ A := by
      intro h; rw [Measure.dirac_apply' _ hA, indicator_of_mem h] at hA0; simp at hA0
    -- from `0` the chain never leaves `0`
    have hpow : ∀ n, (nullSetKernel β ^ (n + 1)) 0 A = 0 := fun n => by
      induction n with
      | zero => rw [pow_one, hP0, Measure.dirac_apply' _ hA, indicator_of_notMem h0A]
      | succ n ih => rw [pow_succ_apply _ _ _ hA, hP0, lintegral_dirac, ih]
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA 0).1 (hφ A hA (pos_iff_ne_zero.2 hne) 0)
    rw [hpow n] at hn
    exact lt_irrefl 0 hn
  have hatom : IsAccessibleAtom (nullSetKernel β) (Measure.dirac 0) {0} :=
    ⟨isAtom_singleton _ 0, hψ, by simp⟩
  -- `E_0[τ_0] = 1`
  have hE0 : meanReturnTime (nullSetKernel β) {0} 0 = 1 := by
    rw [meanReturnTime_eq_one_add _ h0, hP0, lintegral_dirac,
      meanHitTime_of_mem _ h0 (mem_singleton 0), add_zero]
  have hpos : IsPositive (nullSetKernel β) (Measure.dirac 0) :=
    (theorem_10_2_2 hatom (mem_singleton 0)).1.2 (by rw [hE0]; exact ENNReal.one_ne_top)
  refine ⟨hpos, hatom.isRegularSet (mem_singleton 0) (by rw [hE0]; exact ENNReal.one_ne_top),
    fun hdiv => ?_⟩
  have hinf : meanReturnTime (nullSetKernel β) {0} 1 = ∞ := by
    rw [← meanHitTime_of_notMem _ h0 (by simp), eq_top_iff, ← hdiv, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    have := nullSet_meanHitTime_ge hβ N 1 one_ne_zero
    simp_rw [add_comm 1] at this
    exact this
  exact ⟨hinf, fun hreg => (theorem_11_1_2_ii hatom).1 hreg 1 hinf⟩

/-- **The book's condition for (11.12) is wrong.** MT p. 259 says the chain is not regular when
`Σ_j Π_{k=1}^{j} β_k = ∞`. With `β ≡ 1` this sum is infinite, yet every state reaches `0` in one
step, `E_x[τ_0] < ∞` for every `x`, and the chain is regular. -/
theorem nullSet_example_counterexample :
    haveI := isMarkovKernel_nullSetKernel (β := fun _ => 1) fun _ => le_rfl
    (∑' j : ℕ, ∏ _k ∈ Finset.range j, (1 : ℝ≥0∞)) = ∞ ∧
      IsRegularChain (nullSetKernel fun _ => 1) (Measure.dirac 0) := by
  have := isMarkovKernel_nullSetKernel (β := fun _ => 1) fun _ => le_rfl
  have h0 : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  obtain ⟨hpos, -, -⟩ := nullSet_example (β := fun _ => 1) (fun _ => le_rfl)
    (fun _ _ => one_pos)
  have hatom : IsAccessibleAtom (nullSetKernel fun _ => 1) (Measure.dirac 0) {0} :=
    ⟨isAtom_singleton _ 0, hpos.1, by simp⟩
  refine ⟨by simp, (theorem_11_1_2_ii hatom).2
    fun x => ?_⟩
  rw [meanReturnTime_eq_one_add _ h0]
  by_cases hx : x = 0
  · subst hx
    have hP0 : nullSetKernel (fun _ => (1 : ℝ≥0∞)) 0 = Measure.dirac 0 := by
      change nullSetMeas (fun _ => (1 : ℝ≥0∞)) 0 = _; simp [nullSetMeas]
    rw [hP0, lintegral_dirac, meanHitTime_of_mem _ h0 (mem_singleton 0)]
    simp
  · rw [lintegral_nullSetKernel (fun _ => (1 : ℝ≥0∞)) hx,
      meanHitTime_of_mem _ h0 (mem_singleton 0)]
    simp

end MeynTweedie.GeneralizedDrift
