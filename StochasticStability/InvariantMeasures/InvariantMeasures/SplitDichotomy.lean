/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.Dichotomy

/-!
# The dichotomy through atoms, splitting, resolvents and skeletons (MT §8.2.2–8.2.3)

Meyn and Tweedie, §8.2.2–8.2.3, pp. 179–182. `ψ` is a maximal irreducibility measure.

**Chains with an atom** (§8.2.2).
* `IsAtom.pow_succ_eq`, `IsAtom.potKernel_eq`: `Pⁿ(y, ·)`, `n ≥ 1`, and `U(y, ·)` do not depend
  on `y ∈ α`.
* `IsAtom.potKernel_eq_top_iff` (Proposition 8.1.3 for atoms, p. 179): `U(a, α) = ∞` iff
  `L(a, α) = 1`; `IsAtom.isUniformlyTransient`: if `U(a, α) < ∞` then `U(x, α) ≤ (1 − L(α, α))⁻¹`
  for every `x`.
* **Theorem 8.2.1** (`theorem_8_2_1_i`, `theorem_8_2_1_ii`, p. 179): for an atom `α ∈ B⁺(X)`, if
  `α` is recurrent then `U(x, A) = ∞` for every `x` and `A ∈ B⁺(X)`; if `α` is transient, `X` is
  covered by countably many uniformly transient sets.

**The split chain** (§8.2.3).
* `potKernel_split` (8.28): `U(x, B) = ∫ δ_x*(dy) Ǔ(y, B₀ ∪ B₁)`; `splitKernel_pow_checkAlpha`:
  `P̌ⁿ(y, α̌) = δ P̌ⁿ(y, C₀ ∪ C₁)` for `n ≥ 1`.
* **Proposition 8.2.2** (`proposition_8_2_2`, p. 180): for a minorization on a set `C ∈ B⁺(X)`,
  `Φ` and `Φ̌` are both recurrent or both transient; the proof is the book's, through the atom
  `α̌`, without Theorem 8.3.4. `proposition_8_2_2_stronglyAperiodic`: the book's statement, for a
  strongly aperiodic chain whose `ν₁`-small set lies in `B⁺(X)`.
* `isRecurrentChain_split_of_isRecurrentChain`: `Φ` recurrent makes `Φ̌` recurrent for every
  minorization, and `proposition_8_2_2_general`: with Theorem 8.3.4, `Φ` and `Φ̌` have the same
  classification for every minorization.

**The resolvent.**
* `resolventPowCoeff`, `resolvent_pow_eq`: `K_{a_ε}ⁿ⁺¹ = Σ_k (1 − ε)ⁿ⁺¹ εᵏ C(n + k, k) Pᵏ`;
  `tsum_choose_mul_pow`: `Σₙ C(n + k, k) rⁿ = (1 − r)^{−(k+1)}` in `[0, ∞]`.
* **Lemma 8.2.3** (`lemma_8_2_3`, p. 181): `Σ_{n ≥ 1} K_{a_ε}ⁿ = ((1 − ε)/ε) Σ_{n ≥ 0} Pⁿ`.
* `isMaximalIrreducibility_resolvent`: `ψ` is a maximal irreducibility measure for `K_{a_ε}`.
* **Proposition 8.2.4** (`proposition_8_2_4`, p. 181): `Φ` is transient (recurrent) iff each
  `K_{a_ε}`-chain is.
* **Theorem 8.2.5** (`theorem_8_2_5`, p. 181): on a countably generated space, every
  `ψ`-irreducible chain is recurrent or transient, proved through the split resolvent chain.

**Skeletons.**
* `potKernel_skeleton_le` and `potKernel_le_skeleton` (8.29): `U_m ≤ U` and
  `U(x, A) ≤ m (1 + sup U_m(·, A))`.
* **Theorem 8.2.6** (`theorem_8_2_6_i`, `theorem_8_2_6_ii`, p. 182): for an aperiodic chain on a
  countably generated space, `Φ` is transient (recurrent) iff one, and then every, `m`-skeleton is.

**Corrections.**
* Proposition 8.2.2 as stated assumes only strong aperiodicity. Its proof uses the accessible
  atom `α̌` of the split chain, which needs the small set to lie in `B⁺(X)` (Theorem 5.1.3 (ii));
  this hypothesis is added in `proposition_8_2_2_stronglyAperiodic`. The conclusion itself holds
  for every minorization (`proposition_8_2_2_general`), by a different argument that uses
  Theorem 8.3.4.
* In (8.29) the bound `Σⱼ Pʲ(x, A) ≤ mM` should be `m(2 + M)`: the inner sum includes `j = 0`, and
  `M` bounds `U_m(·, A)` only on `A` (Proposition 8.3.1 (i) extends it to `1 + M`).
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Chains with an atom -/

/-- On an atom, `Pⁿ⁺¹(y, ·)` does not depend on `y ∈ α`. -/
theorem IsAtom.pow_succ_eq {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {y y' : X}
    (hy : y ∈ α) (hy' : y' ∈ α) (n : ℕ) : (P ^ (n + 1)) y = (P ^ (n + 1)) y' := by
  obtain ⟨-, ν, hν⟩ := hα
  rw [pow_succ]
  change ((P ^ n) ∘ₖ P) y = ((P ^ n) ∘ₖ P) y'
  rw [Kernel.comp_apply, Kernel.comp_apply, hν y hy, hν y' hy']

/-- On an atom, `U(y, ·)` does not depend on `y ∈ α`. -/
theorem IsAtom.potKernel_eq {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {y y' : X}
    (hy : y ∈ α) (hy' : y' ∈ α) {A : Set X} (hA : MeasurableSet A) :
    potKernel P y A = potKernel P y' A := by
  rw [potKernel_apply P y hA, potKernel_apply P y' hA]
  exact tsum_congr fun n => by rw [hα.pow_succ_eq hy hy' n]

/-- **Proposition 8.1.3 for an atom** (MT p. 179): for `a ∈ α`, `U(a, α) = ∞` iff
`L(a, α) = 1`. If `L(a, α) < 1`, then `U(x, α) ≤ (1 − L(a, α))⁻¹` for every `x`. -/
theorem IsAtom.potKernel_eq_top_iff {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) : potKernel P a α = ∞ ↔ hitProb P α a = 1 := by
  obtain ⟨hαm, ν, hν⟩ := hα
  constructor
  · intro h
    by_contra hc
    have hlt : hitProb P α a < 1 := lt_of_le_of_ne (hitProb_le_one P α a) hc
    have := proposition_8_3_1_iii P hαm hlt (fun y hy => (hitProb_atom_eq P hν hαm ha hy).le) a
    rw [h, top_le_iff, ENNReal.inv_eq_top, tsub_eq_zero_iff_le] at this
    exact absurd hlt (not_lt.2 this)
  · intro h
    exact proposition_8_3_1_ii P hαm (fun y hy => (hitProb_atom_eq P hν hαm ha hy).trans h) a ha

/-- A transient atom is uniformly transient: if `U(a, α) < ∞` for some `a ∈ α`, then
`L(·, α) < 1` on `α` and `U(x, α) ≤ (1 − L(a, α))⁻¹` for every `x` (MT p. 179). -/
theorem IsAtom.isUniformlyTransient {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (h : potKernel P a α ≠ ∞) :
    IsUniformlyTransient P α := by
  have hL : hitProb P α a < 1 :=
    lt_of_le_of_ne (hitProb_le_one P α a) fun h1 => h ((hα.potKernel_eq_top_iff ha).2 h1)
  obtain ⟨hαm, ν, hν⟩ := hα
  refine ⟨hαm, (1 - hitProb P α a)⁻¹, ENNReal.inv_ne_top.2 (tsub_pos_of_lt hL).ne',
    fun x _ => proposition_8_3_1_iii P hαm hL
      (fun y hy => (hitProb_atom_eq P hν hαm ha hy).le) x⟩

/-- **Theorem 8.2.1 (i)** (MT p. 179): if a `ψ`-irreducible chain has a recurrent atom
`α ∈ B⁺(X)`, then `U(x, A) = ∞` for every `x` and every `A ∈ B⁺(X)`: the chain is recurrent. -/
theorem theorem_8_2_1_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {α : Set X} (hα : IsAtom P α) (hψα : 0 < ψ α)
    (hrec : IsRecurrentSet P α) : IsRecurrentChain P ψ := by
  refine ⟨hψ, fun A hA hψA x => ?_⟩
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero hψα.ne'
  have hUα : potKernel P x α = ∞ :=
    potKernel_eq_top_of_hitProb_pos P hα.1 hrec (hψ.2.1 α hα.1 hψα x)
  obtain ⟨s, hs⟩ := (hitProb_pos_iff P hA a).1 (hψ.2.1 A hA hψA a)
  refine top_le_iff.1 ?_
  calc ∞ = (P ^ (s + 1)) a A * potKernel P x α := by rw [hUα, ENNReal.mul_top hs.ne']
    _ = ∫⁻ _ in α, (P ^ (s + 1)) a A ∂potKernel P x := by rw [setLIntegral_const]
    _ = ∫⁻ y in α, (P ^ (s + 1)) y A ∂potKernel P x :=
        setLIntegral_congr_fun hα.1 fun y hy => by rw [hα.pow_succ_eq hy ha]
    _ ≤ ∫⁻ y, (P ^ (s + 1)) y A ∂potKernel P x := setLIntegral_le_lintegral _ _
    _ ≤ potKernel P x A := by
        have := lemma_5_5_2_iii P (isSamplingDist_diracDist (s + 1)) x hA
        rwa [sampledKernel_diracDist] at this

/-- **Theorem 8.2.1 (ii)** (MT p. 179): if a `ψ`-irreducible chain has a transient atom
`α ∈ B⁺(X)` (`U(a, α) < ∞` for some `a ∈ α`), then `X` is covered by countably many uniformly
transient sets: the chain is transient. -/
theorem theorem_8_2_1_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {α : Set X} (hα : IsAtom P α) (hψα : 0 < ψ α)
    {a : X} (ha : a ∈ α) (h : potKernel P a α ≠ ∞) : IsTransientChain P ψ :=
  isTransientChain_of_uniformlyTransient P hψ (hα.isUniformlyTransient ha h) hψα

/-- An accessible atom is either recurrent or uniformly transient. -/
theorem IsAtom.isRecurrentSet_or_isUniformlyTransient {P : Kernel X X} [IsMarkovKernel P]
    {α : Set X} (hα : IsAtom P α) : IsRecurrentSet P α ∨ IsUniformlyTransient P α := by
  by_cases h : ∃ a ∈ α, potKernel P a α ≠ ∞
  · obtain ⟨a, ha, h⟩ := h
    exact Or.inr (hα.isUniformlyTransient ha h)
  · push Not at h
    exact Or.inl h

/-! ### The split chain -/

namespace Minorization

variable {P : Kernel X X}

/-- (8.28), MT p. 180: `U(x, B) = ∫ δ_x*(dy) Ǔ(y, B₀ ∪ B₁)`. -/
theorem potKernel_split (M : Minorization P) [IsMarkovKernel P] (x : X) {B : Set X}
    (hB : MeasurableSet B) :
    potKernel P x B = ∫⁻ z, potKernel M.splitKernel z (Prod.fst ⁻¹' B)
      ∂M.split (Measure.dirac x) := by
  have hB' : MeasurableSet (Prod.fst ⁻¹' B : Set (X × Bool)) := measurable_fst hB
  simp_rw [potKernel_apply _ _ hB']
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ hB').aemeasurable,
    potKernel_apply P x hB]
  refine tsum_congr fun n => ?_
  have := M.theorem_5_1_3_i (n + 1) (Measure.dirac x) hB
  rwa [lintegral_dirac' _ (Kernel.measurable_coe _ hB)] at this

/-- `P̌ⁿ⁺¹(z, α̌) = δ P̌ⁿ⁺¹(z, C₀ ∪ C₁)`: the coin is tossed independently at each visit to `C`. -/
theorem splitKernel_pow_checkAlpha (M : Minorization P) (n : ℕ) (z : X × Bool) :
    (M.splitKernel ^ (n + 1)) z M.checkAlpha =
      M.δ * (M.splitKernel ^ (n + 1)) z (Prod.fst ⁻¹' M.C) := by
  rw [M.splitKernel_pow_succ_apply, checkAlpha, M.split_apply_true _ M.measurableSet_C,
    M.split_fst_preimage _ M.measurableSet_C, inter_self]

/-- `Ǔ(z, α̌) = δ Ǔ(z, C₀ ∪ C₁)`. -/
theorem potKernel_checkAlpha (M : Minorization P) (z : X × Bool) :
    potKernel M.splitKernel z M.checkAlpha =
      M.δ * potKernel M.splitKernel z (Prod.fst ⁻¹' M.C) := by
  rw [potKernel_apply _ _ M.measurableSet_checkAlpha,
    potKernel_apply _ _ (measurable_fst M.measurableSet_C), ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => M.splitKernel_pow_checkAlpha n z

/-- `ψ*(α̌) = δ ψ(C)`. -/
theorem split_checkAlpha (M : Minorization P) (μ : Measure X) :
    M.split μ M.checkAlpha = M.δ * μ M.C := by
  rw [checkAlpha, M.split_apply_true μ M.measurableSet_C, inter_self]

/-- If the split chain is recurrent, so is the original chain (MT p. 181, from (8.28)). -/
theorem isRecurrentChain_of_split (M : Minorization P) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ)
    (h : haveI := M.isMarkovKernel_splitKernel; IsRecurrentChain M.splitKernel (M.split ψ)) :
    IsRecurrentChain P ψ := by
  have := M.isMarkovKernel_splitKernel
  refine ⟨hψ, fun B hB hψB x => ?_⟩
  have hB' : MeasurableSet (Prod.fst ⁻¹' B : Set (X × Bool)) := measurable_fst hB
  have := M.isProbabilityMeasure_split (Measure.dirac x)
  rw [M.potKernel_split x hB]
  have hU : ∀ z, potKernel M.splitKernel z (Prod.fst ⁻¹' B) = ∞ := fun z =>
    h.2 _ hB' (by rw [M.split_fst_preimage ψ hB]; exact hψB) z
  simp [hU]

/-- If the split atom `α̌` is uniformly transient for `Φ̌`, then `C` is uniformly transient for
`Φ`: `U(x, C) = ∫ δ_x*(dy) Ǔ(y, C₀ ∪ C₁) = δ⁻¹ ∫ δ_x*(dy) Ǔ(y, α̌)`. -/
theorem isUniformlyTransient_C (M : Minorization P) [IsMarkovKernel P]
    (h : haveI := M.isMarkovKernel_splitKernel; IsUniformlyTransient M.splitKernel M.checkAlpha) :
    IsUniformlyTransient P M.C := by
  have := M.isMarkovKernel_splitKernel
  obtain ⟨K, hK, hb⟩ := h.exists_bound
  refine ⟨M.measurableSet_C, K / M.δ, ENNReal.div_ne_top hK M.δ_pos.ne', fun x _ => ?_⟩
  have := M.isProbabilityMeasure_split (Measure.dirac x)
  rw [M.potKernel_split x M.measurableSet_C]
  calc ∫⁻ z, potKernel M.splitKernel z (Prod.fst ⁻¹' M.C) ∂M.split (Measure.dirac x)
      ≤ ∫⁻ _, K / M.δ ∂M.split (Measure.dirac x) := lintegral_mono fun z => by
        rw [ENNReal.le_div_iff_mul_le (Or.inl M.δ_pos.ne') (Or.inl M.δ_ne_top), mul_comm,
          ← M.potKernel_checkAlpha]
        exact hb z
    _ = K / M.δ := by simp

/-- **Proposition 8.2.2** (MT p. 180): if `Φ` is `ψ`-irreducible and `M` is a minorization on a
set `C ∈ B⁺(X)`, then either both `Φ` and its split chain `Φ̌` are recurrent, or both are
transient. The proof goes through the accessible atom `α̌ = C₁` of `Φ̌` (Theorem 8.2.1). -/
theorem proposition_8_2_2 (M : Minorization P) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hC : 0 < ψ M.C) :
    haveI := M.isMarkovKernel_splitKernel
    (IsRecurrentChain P ψ ∧ IsRecurrentChain M.splitKernel (M.split ψ)) ∨
      (IsTransientChain P ψ ∧ IsTransientChain M.splitKernel (M.split ψ)) := by
  have := M.isMarkovKernel_splitKernel
  have hψs := M.isMaximalIrreducibility_split hψ
  have hα := M.isAtom_checkAlpha
  have hψα : 0 < M.split ψ M.checkAlpha := by
    rw [M.split_checkAlpha]; exact ENNReal.mul_pos M.δ_pos.ne' hC.ne'
  rcases hα.isRecurrentSet_or_isUniformlyTransient with hrec | hut
  · have hs := theorem_8_2_1_i M.splitKernel hψs hα hψα hrec
    exact Or.inl ⟨M.isRecurrentChain_of_split hψ hs, hs⟩
  · exact Or.inr ⟨isTransientChain_of_uniformlyTransient P hψ (M.isUniformlyTransient_C hut) hC,
      isTransientChain_of_uniformlyTransient _ hψs hut hψα⟩

/-- If `Φ` is recurrent, so is the split chain, for every minorization: a set `Ǎ ∈ B⁺(X̌)` has
`ψ(Ǎ₀) > 0` or `ψ(Ǎ₁ ∩ C) > 0`, and `Ǔ(z, Ǎ)` dominates `(1 − δ) ∫ Q(z, dy) U(y, Ǎ₀)` and
`δ ∫ Q(z, dy) U(y, Ǎ₁ ∩ C)`. -/
theorem isRecurrentChain_split_of_isRecurrentChain (M : Minorization P) [IsMarkovKernel P]
    {ψ : Measure X} (h : IsRecurrentChain P ψ) :
    haveI := M.isMarkovKernel_splitKernel; IsRecurrentChain M.splitKernel (M.split ψ) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_baseK
  refine ⟨M.isMaximalIrreducibility_split h.1, fun s hs hpos z => ?_⟩
  have h0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have h1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  -- `Σₙ (Q(z, ·) Pⁿ)(B) = ∞` whenever `U(·, B) ≡ ∞`
  have hsum : ∀ B, MeasurableSet B → (∀ y, potKernel P y B = ∞) →
      ∑' n, ((P ^ n : Kernel X X) ∘ₘ M.baseK z) B = ∞ := fun B hB hU => by
    refine top_le_iff.1 ?_
    calc ∞ = ∫⁻ y, potKernel P y B ∂M.baseK z := by simp [hU]
      _ = ∑' n, ((P ^ (n + 1) : Kernel X X) ∘ₘ M.baseK z) B := by
          simp_rw [potKernel_apply P _ hB, Measure.bind_apply hB (Kernel.aemeasurable _)]
          exact lintegral_tsum fun n => (Kernel.measurable_coe _ hB).aemeasurable
      _ ≤ ∑' n, ((P ^ n : Kernel X X) ∘ₘ M.baseK z) B :=
          ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1)
            fun n => ((P ^ n : Kernel X X) ∘ₘ M.baseK z) B
  rw [potKernel_apply _ _ hs]
  simp_rw [M.splitKernel_pow_succ_apply]
  rcases M.split_pos_cases ψ hs hpos with hc | hc
  · have hU := hsum _ h0 (fun y => h.2 _ h0 hc y)
    refine top_le_iff.1 ?_
    calc ∞ = (1 - M.δ) * ∑' n, ((P ^ n : Kernel X X) ∘ₘ M.baseK z)
          ((fun x => (x, false)) ⁻¹' s) := by rw [hU, ENNReal.mul_top M.one_sub_δ_ne_zero]
      _ = ∑' n, (1 - M.δ) * ((P ^ n : Kernel X X) ∘ₘ M.baseK z)
          ((fun x => (x, false)) ⁻¹' s) := ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun n => (M.one_sub_mul_le_split_false _ h0).trans
          (measure_mono (prod_subset_iff.2 fun x hx b hb => by
            rw [mem_singleton_iff.1 hb]; exact hx))
  · have hU := hsum _ (h1.inter M.measurableSet_C) (fun y => h.2 _ (h1.inter M.measurableSet_C)
      hc y)
    refine top_le_iff.1 ?_
    calc ∞ = M.δ * ∑' n, ((P ^ n : Kernel X X) ∘ₘ M.baseK z)
          ((fun x => (x, true)) ⁻¹' s ∩ M.C) := by rw [hU, ENNReal.mul_top M.δ_pos.ne']
      _ = ∑' n, M.δ * ((P ^ n : Kernel X X) ∘ₘ M.baseK z)
          ((fun x => (x, true)) ⁻¹' s ∩ M.C) := ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
          rw [← M.split_apply_true _ h1]
          exact measure_mono (prod_subset_iff.2 fun x hx b hb => by
            rw [mem_singleton_iff.1 hb]; exact hx)

/-- **Proposition 8.2.2, general form**: for every minorization, `Φ` is recurrent iff `Φ̌` is,
and transient iff `Φ̌` is (Theorem 8.3.4 for both chains). -/
theorem proposition_8_2_2_general (M : Minorization P) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    haveI := M.isMarkovKernel_splitKernel
    (IsRecurrentChain P ψ ↔ IsRecurrentChain M.splitKernel (M.split ψ)) ∧
      (IsTransientChain P ψ ↔ IsTransientChain M.splitKernel (M.split ψ)) := by
  have := M.isMarkovKernel_splitKernel
  have hψs := M.isMaximalIrreducibility_split hψ
  have hrec : IsRecurrentChain P ψ ↔ IsRecurrentChain M.splitKernel (M.split ψ) :=
    ⟨M.isRecurrentChain_split_of_isRecurrentChain, M.isRecurrentChain_of_split hψ⟩
  refine ⟨hrec, ?_⟩
  constructor
  · intro h
    rcases theorem_8_3_4 _ hψs with h' | h'
    · exact absurd (hrec.2 h') h.not_isRecurrentChain
    · exact h'
  · intro h
    rcases theorem_8_3_4 P hψ with h' | h'
    · exact absurd (hrec.1 h') h.not_isRecurrentChain
    · exact h'

end Minorization

/-- **Proposition 8.2.2** (MT p. 180), the book's statement: a `ψ`-irreducible strongly aperiodic
chain, whose `ν₁`-small set `A` (with `ν₁(A) > 0`) lies in `B⁺(X)`, has a split chain such that
`Φ` and `Φ̌` are both recurrent or both transient. -/
theorem proposition_8_2_2_stronglyAperiodic (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {ν : Measure X} {A : Set X} (hA : IsSmallSet P 1 ν A)
    (hνA : 0 < ν A) (hψA : 0 < ψ A) :
    ∃ M : Minorization P, M.C = A ∧ M.IsConcentrated ∧
      haveI := M.isMarkovKernel_splitKernel
      ((IsRecurrentChain P ψ ∧ IsRecurrentChain M.splitKernel (M.split ψ)) ∨
        (IsTransientChain P ψ ∧ IsTransientChain M.splitKernel (M.split ψ))) := by
  have hle : ∀ x ∈ A, ν ≤ P x := fun x hx => by
    have := hA.2.2.2 x hx
    rwa [pow_one] at this
  have hfin : ν A ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hνA.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx A).trans prob_le_one)
  set M := Minorization.ofLe hA.1 hle hνA hfin
  have hMC : M.C = A := Minorization.ofLe_C _ _ _ _
  refine ⟨M, hMC, Minorization.ofLe_isConcentrated _ _ _ _, ?_⟩
  exact M.proposition_8_2_2 hψ (hMC ▸ hψA)

/-! ### The resolvent -/

/-- `Σₙ C(n + k, k) rⁿ = (1 − r)^{−(k+1)}` in `[0, ∞]`. -/
theorem tsum_choose_mul_pow (r : ℝ≥0∞) (k : ℕ) :
    ∑' n, ((n + k).choose k : ℝ≥0∞) * r ^ n = ((1 - r)⁻¹) ^ (k + 1) := by
  induction k with
  | zero => simp [ENNReal.tsum_geometric]
  | succ k ih =>
    have h1 : ∀ n, ((n + (k + 1)).choose (k + 1) : ℝ≥0∞) * r ^ n =
        ∑ p ∈ Finset.antidiagonal n, ((p.1 + k).choose k : ℝ≥0∞) * r ^ p.1 * r ^ p.2 :=
      fun n => by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => ((i + k).choose k : ℝ≥0∞) * r ^ i * r ^ j)]
        have : ∀ i ∈ Finset.range n.succ, ((i + k).choose k : ℝ≥0∞) * r ^ i * r ^ (n - i) =
            ((i + k).choose k : ℝ≥0∞) * r ^ n := fun i hi => by
          rw [mul_assoc, ← pow_add, show i + (n - i) = n by
            have := Finset.mem_range.1 hi; omega]
        rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Nat.cast_sum, Nat.succ_eq_add_one,
          Nat.sum_range_add_choose n k, show n + k + 1 = n + (k + 1) by omega]
    simp_rw [h1]
    rw [tsum_sum_antidiagonal (fun p => ((p.1 + k).choose k : ℝ≥0∞) * r ^ p.1 * r ^ p.2)]
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    rw [ENNReal.tsum_mul_right, ih]
    ring

/-- The coefficients of the powers of the resolvent: `b_n(k) = (1 − ε)ⁿ⁺¹ εᵏ C(n + k, k)`. -/
noncomputable def resolventPowCoeff (ε : ℝ≥0∞) (n k : ℕ) : ℝ≥0∞ :=
  (1 - ε) ^ (n + 1) * ε ^ k * ((n + k).choose k : ℝ≥0∞)

/-- `K_{a_ε}ⁿ⁺¹ = Σ_k (1 − ε)ⁿ⁺¹ εᵏ C(n + k, k) Pᵏ` (the convolution powers of `a_ε`). -/
theorem resolvent_pow_eq (P : Kernel X X) (ε : ℝ≥0∞) (n : ℕ) :
    resolvent P ε ^ (n + 1) = sampledKernel P (resolventPowCoeff ε n) := by
  induction n with
  | zero =>
    rw [zero_add, pow_one, resolvent]
    congr 1
    funext k
    simp [resolventPowCoeff]
  | succ n ih =>
    rw [pow_succ, ih]
    change sampledKernel P (resolventPowCoeff ε n) ∘ₖ resolvent P ε = _
    rw [resolvent, ← sampledKernel_sampleConv]
    congr 1
    funext m
    unfold sampleConv resolventPowCoeff
    have : ∀ p ∈ Finset.antidiagonal m, (1 - ε) * ε ^ p.1 * ((1 - ε) ^ (n + 1) * ε ^ p.2 *
        ((n + p.2).choose p.2 : ℝ≥0∞)) =
        (1 - ε) ^ (n + 1 + 1) * ε ^ m * ((p.2 + n).choose n : ℝ≥0∞) := fun p hp => by
      rw [Finset.mem_antidiagonal] at hp
      rw [add_comm n p.2, Nat.choose_symm_add, ← hp, pow_add, pow_succ]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Nat.cast_sum,
      ← Finset.Nat.sum_antidiagonal_swap]
    simp only [Prod.snd_swap]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one,
      Nat.sum_range_add_choose m n, show m + n + 1 = n + 1 + m by omega,
      Nat.choose_symm_add]

/-- `Σₙ bₙ(k) = (1 − ε)/ε` for every `k`, for `0 < ε < 1`. -/
theorem tsum_resolventPowCoeff {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    ∑' n, resolventPowCoeff ε n k = (1 - ε) / ε := by
  unfold resolventPowCoeff
  have : ∀ n, (1 - ε) ^ (n + 1) * ε ^ k * ((n + k).choose k : ℝ≥0∞) =
      ((1 - ε) * ε ^ k) * (((n + k).choose k : ℝ≥0∞) * (1 - ε) ^ n) := fun n => by ring
  simp_rw [this]
  rw [ENNReal.tsum_mul_left, tsum_choose_mul_pow, ENNReal.sub_sub_cancel ENNReal.one_ne_top
    hε1.le, pow_succ, mul_assoc, ← mul_assoc (ε ^ k), ← mul_pow,
    ENNReal.mul_inv_cancel hε0.ne' (hε1.trans ENNReal.one_lt_top).ne, one_pow, one_mul,
    div_eq_mul_inv]

/-- **Lemma 8.2.3** (MT p. 181): for `0 < ε < 1`, `Σ_{n ≥ 1} K_{a_ε}ⁿ = ((1 − ε)/ε) Σ_{n ≥ 0} Pⁿ`,
that is, `U_{K_{a_ε}}(x, A) = ((1 − ε)/ε) Σ_{n ≥ 0} Pⁿ(x, A)`. -/
theorem lemma_8_2_3 (P : Kernel X X) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1) (x : X)
    {A : Set X} (hA : MeasurableSet A) :
    potKernel (resolvent P ε) x A = (1 - ε) / ε * ∑' n, (P ^ n) x A := by
  rw [potKernel_apply _ x hA]
  simp_rw [resolvent_pow_eq P ε, sampledKernel_apply P _ x hA]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [ENNReal.tsum_mul_right, tsum_resolventPowCoeff hε0 hε1]

/-- `Σ_{n ≥ 0} Pⁿ(x, A) = 1_A(x) + U(x, A)`. -/
theorem tsum_pow_eq (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    ∑' n, (P ^ n) x A = Measure.dirac x A + potKernel P x A := by
  rw [tsum_eq_zero_add' ENNReal.summable, pow_zero_apply, potKernel_apply P x hA]

/-- `K_{a_ε}ⁿ⁺¹(x, A) > 0` implies `Pᵏ(x, A) > 0` for some `k`. -/
theorem exists_pow_pos_of_resolvent_pow_pos (P : Kernel X X) (ε : ℝ≥0∞) {n : ℕ} {x : X}
    {A : Set X} (hA : MeasurableSet A) (h : 0 < (resolvent P ε ^ (n + 1)) x A) :
    ∃ k, 0 < (P ^ k) x A := by
  rw [resolvent_pow_eq, sampledKernel_apply P _ x hA] at h
  by_contra hc
  push Not at hc
  have : ∑' k, resolventPowCoeff ε n k * (P ^ k) x A = 0 :=
    ENNReal.tsum_eq_zero.2 fun k => by rw [nonpos_iff_eq_zero.1 (hc k), mul_zero]
  exact (this ▸ h).ne' rfl

/-- `ψ` is a maximal irreducibility measure for the resolvent `K_{a_ε}`, `0 < ε < 1`: the two
chains have the same irreducibility measures. -/
theorem isMaximalIrreducibility_resolvent (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1) :
    haveI := isMarkovKernel_resolvent P hε1; IsMaximalIrreducibility (resolvent P ε) ψ := by
  have := isMarkovKernel_resolvent P hε1
  have hiff : ∀ φ : Measure X, IsPhiIrreducible (resolvent P ε) φ ↔ IsPhiIrreducible P φ := by
    intro φ
    constructor
    · intro h A hA hpos
      refine hitProb_pos_of_compl P hA fun y hy => ?_
      obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA y).1 (h A hA hpos y)
      obtain ⟨k, hk⟩ := exists_pow_pos_of_resolvent_pow_pos P ε hA hn
      rcases k with _ | k
      · rw [pow_zero_apply, Measure.dirac_apply' _ hA, indicator_of_notMem hy] at hk
        exact absurd hk (lt_irrefl 0)
      · exact (hitProb_pos_iff P hA y).2 ⟨k, hk⟩
    · intro h A hA hpos x
      obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA x).1 (h A hA hpos x)
      refine (hitProb_pos_iff _ hA x).2 ⟨0, ?_⟩
      rw [zero_add, pow_one, resolvent_apply P ε x hA]
      refine ENNReal.mul_pos (tsub_pos_of_lt hε1).ne' ?_
      exact (ENNReal.mul_pos (pow_ne_zero _ hε0.ne') hn.ne').trans_le
        (ENNReal.le_tsum (f := fun i => ε ^ i * (P ^ i) x A) (n + 1)) |>.ne'
  exact ⟨hψ.1, (hiff ψ).2 hψ.2.1, fun φ hφ => hψ.2.2 φ ((hiff φ).1 hφ)⟩

/-- **Proposition 8.2.4** (MT p. 181): for `0 < ε < 1`, (i) `Φ` is transient iff the
`K_{a_ε}`-chain is transient; (ii) `Φ` is recurrent iff the `K_{a_ε}`-chain is recurrent. -/
theorem proposition_8_2_4 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1) :
    haveI := isMarkovKernel_resolvent P hε1
    (IsTransientChain P ψ ↔ IsTransientChain (resolvent P ε) ψ) ∧
      (IsRecurrentChain P ψ ↔ IsRecurrentChain (resolvent P ε) ψ) := by
  have := isMarkovKernel_resolvent P hε1
  have hψK := isMaximalIrreducibility_resolvent P hψ hε0 hε1
  set c := (1 - ε) / ε with hc
  have hc0 : c ≠ 0 := ENNReal.div_pos_iff.2 ⟨(tsub_pos_of_lt hε1).ne',
    (hε1.trans ENNReal.one_lt_top).ne⟩ |>.ne'
  have hct : c ≠ ∞ := ENNReal.div_ne_top (by simp) hε0.ne'
  have hU : ∀ x A, MeasurableSet A →
      potKernel (resolvent P ε) x A = c * (Measure.dirac x A + potKernel P x A) :=
    fun x A hA => by rw [lemma_8_2_3 P hε0 hε1 x hA, tsum_pow_eq P x hA]
  have hut : ∀ B, IsUniformlyTransient P B ↔ IsUniformlyTransient (resolvent P ε) B := by
    intro B
    constructor
    · rintro ⟨hB, M, hM, hb⟩
      refine ⟨hB, c * (1 + M), ENNReal.mul_ne_top hct (by simp [hM]), fun x hx => ?_⟩
      rw [hU x B hB]
      exact mul_le_mul' le_rfl (add_le_add prob_le_one (hb x hx))
    · rintro ⟨hB, M, hM, hb⟩
      refine ⟨hB, M / c, ENNReal.div_ne_top hM hc0, fun x hx => ?_⟩
      rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct), mul_comm]
      exact (mul_le_mul' le_rfl le_add_self).trans ((hU x B hB).symm ▸ hb x hx)
  refine ⟨⟨fun ⟨_, B, hB, hcov⟩ => ⟨hψK, B, fun n => (hut (B n)).1 (hB n), hcov⟩,
    fun ⟨_, B, hB, hcov⟩ => ⟨hψ, B, fun n => (hut (B n)).2 (hB n), hcov⟩⟩,
    ⟨fun h => ⟨hψK, fun A hA hpos x => ?_⟩, fun h => ⟨hψ, fun A hA hpos x => ?_⟩⟩⟩
  · rw [hU x A hA, h.2 A hA hpos x, add_top, ENNReal.mul_top hc0]
  · have := h.2 A hA hpos x
    rw [hU x A hA, ENNReal.mul_eq_top] at this
    rcases this with ⟨-, h'⟩ | ⟨h', -⟩
    · rw [ENNReal.add_eq_top] at h'
      rcases h' with h' | h'
      · exact absurd h' (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one)
      · exact h'
    · exact absurd h' hct

/-- **Theorem 8.2.5** (MT p. 181): on a countably generated space, a `ψ`-irreducible chain is
either recurrent or transient. The proof is the book's: the resolvent `K_{a_{1/2}}` satisfies a
minorization on a set of `B⁺(X)` (Theorem 5.2.3), so its split chain has an accessible atom and
Proposition 8.2.2 classifies it; Proposition 8.2.4 passes the classification back to `Φ`. -/
theorem theorem_8_2_5 [MeasurableSpace.CountablyGenerated X] (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    IsRecurrentChain P ψ ∨ IsTransientChain P ψ := by
  have hε0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolvent P hε1
  obtain ⟨M, -, hMC⟩ := theorem_5_2_3_resolvent P hψ hε0 hε1
  have hψK := isMaximalIrreducibility_resolvent P hψ hε0 hε1
  obtain ⟨hT, hR⟩ := proposition_8_2_4 P hψ hε0 hε1
  rcases M.proposition_8_2_2 hψK hMC with h | h
  · exact Or.inl (hR.2 h.1)
  · exact Or.inr (hT.2 h.1)

/-! ### Skeletons -/

/-- `U_m(x, A) = Σⱼ P^{m(j+1)}(x, A) ≤ U(x, A)` for the `m`-skeleton, `m ≥ 1`. -/
theorem potKernel_skeleton_le (P : Kernel X X) {m : ℕ} (hm : 1 ≤ m) (x : X) {A : Set X}
    (hA : MeasurableSet A) : potKernel (P ^ m) x A ≤ potKernel P x A := by
  rw [potKernel_apply _ x hA, potKernel_apply P x hA]
  have : ∀ j, ((P ^ m) ^ (j + 1)) x A = (P ^ ((m * (j + 1) - 1) + 1)) x A := fun j => by
    rw [← pow_mul, show m * (j + 1) - 1 + 1 = m * (j + 1) by
      have : 1 ≤ m * (j + 1) := Nat.mul_pos (by omega) (by omega)
      omega]
  simp_rw [this]
  refine ENNReal.tsum_comp_le_tsum_of_injective (fun a b hab => ?_) fun n => (P ^ (n + 1)) x A
  have h1 : 1 ≤ m * (a + 1) := Nat.mul_pos (by omega) (by omega)
  have h2 : 1 ≤ m * (b + 1) := Nat.mul_pos (by omega) (by omega)
  have : m * (a + 1) = m * (b + 1) := by omega
  have := Nat.eq_of_mul_eq_mul_left (by omega) this
  omega

/-- (8.29): `U(x, A) = Σ_{r=1}^m ∫ Pʳ(x, dy) Σ_{j ≥ 0} P^{jm}(y, A) ≤ m (1 + M)` when
`U_m(y, A) ≤ M` for every `y`. -/
theorem potKernel_le_skeleton (P : Kernel X X) [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m)
    (x : X) {A : Set X} (hA : MeasurableSet A) {M : ℝ≥0∞}
    (hM : ∀ y, potKernel (P ^ m) y A ≤ M) : potKernel P x A ≤ m * (1 + M) := by
  have : NeZero m := ⟨by omega⟩
  rw [potKernel_apply P x hA]
  have hsurj : Function.Surjective fun p : ℕ × Fin m => p.1 * m + (p.2 : ℕ) := fun n =>
    ⟨(n / m, ⟨n % m, Nat.mod_lt n (by omega)⟩), Nat.div_add_mod' n m⟩
  calc ∑' n, (P ^ (n + 1)) x A
      ≤ ∑' p : ℕ × Fin m, (P ^ (p.1 * m + (p.2 : ℕ) + 1)) x A :=
        ENNReal.tsum_le_tsum_comp_of_surjective hsurj fun n => (P ^ (n + 1)) x A
    _ = ∑' r : Fin m, ∑' q, (P ^ (q * m + (r : ℕ) + 1)) x A := by
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ ≤ ∑' _ : Fin m, (1 + M) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        calc ∑' q, (P ^ (q * m + (r : ℕ) + 1)) x A
            = ∫⁻ y, ∑' q, ((P ^ m) ^ q) y A ∂(P ^ ((r : ℕ) + 1)) x := by
              rw [lintegral_tsum fun q => (Kernel.measurable_coe _ hA).aemeasurable]
              refine tsum_congr fun q => ?_
              rw [← pow_mul, show q * m + (r : ℕ) + 1 = ((r : ℕ) + 1) + m * q by ring,
                Kernel.pow_add_apply_eq_lintegral P _ _ x hA]
          _ ≤ ∫⁻ _, 1 + M ∂(P ^ ((r : ℕ) + 1)) x := lintegral_mono fun y => by
              rw [tsum_pow_eq _ y hA]
              exact add_le_add prob_le_one (hM y)
          _ = 1 + M := by
              have := isMarkovKernel_pow P ((r : ℕ) + 1)
              simp
    _ = m * (1 + M) := by rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- A transient `m`-skeleton makes the chain transient (8.29). -/
theorem isTransientSet_of_skeleton (P : Kernel X X) [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m)
    (h : haveI := isMarkovKernel_pow P m; IsTransientSet (P ^ m) univ) :
    IsTransientSet P univ := by
  have := isMarkovKernel_pow P m
  obtain ⟨B, hB, hcov⟩ := h
  refine ⟨B, fun n => ?_, hcov⟩
  obtain ⟨M, hM, hb⟩ := (hB n).exists_bound
  exact ⟨(hB n).1, m * (1 + M), ENNReal.mul_ne_top (by simp) (by simp [hM]), fun x _ =>
    potKernel_le_skeleton P hm x (hB n).1 hb⟩

/-- A transient chain has transient skeletons. -/
theorem isTransientSet_skeleton (P : Kernel X X) [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m)
    (h : IsTransientSet P univ) :
    haveI := isMarkovKernel_pow P m; IsTransientSet (P ^ m) univ := by
  have := isMarkovKernel_pow P m
  obtain ⟨B, hB, hcov⟩ := h
  refine ⟨B, fun n => ?_, hcov⟩
  obtain ⟨hBm, M, hM, hb⟩ := hB n
  exact ⟨hBm, M, hM, fun x hx => (potKernel_skeleton_le P hm x hBm).trans (hb x hx)⟩

/-- **Theorem 8.2.6 (i)** (MT p. 182): for an aperiodic `ψ`-irreducible chain on a countably
generated space, `Φ` is transient iff one `m`-skeleton is transient, iff every `m`-skeleton is. -/
theorem theorem_8_2_6_i [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    (hap : IsAperiodic P ψ) :
    (IsTransientChain P ψ ↔ ∃ m, 1 ≤ m ∧ haveI := isMarkovKernel_pow P m
      IsTransientChain (P ^ m) ψ) ∧
    (IsTransientChain P ψ ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
      IsTransientChain (P ^ m) ψ) := by
  have hsk := (proposition_5_4_5_iii P hψ hap).1
  refine ⟨⟨fun h => ⟨1, le_rfl, (hsk 1 le_rfl).1, isTransientSet_skeleton P le_rfl h.2⟩,
    fun ⟨m, hm, h⟩ => ⟨hψ, isTransientSet_of_skeleton P hm h.2⟩⟩,
    ⟨fun h m hm => ⟨(hsk m hm).1, isTransientSet_skeleton P hm h.2⟩,
    fun h => ⟨hψ, isTransientSet_of_skeleton P le_rfl (h 1 le_rfl).2⟩⟩⟩

/-- **Theorem 8.2.6 (ii)** (MT p. 182): for an aperiodic `ψ`-irreducible chain on a countably
generated space, `Φ` is recurrent iff one `m`-skeleton is recurrent, iff every `m`-skeleton is. -/
theorem theorem_8_2_6_ii [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    (hap : IsAperiodic P ψ) :
    (IsRecurrentChain P ψ ↔ ∃ m, 1 ≤ m ∧ haveI := isMarkovKernel_pow P m
      IsRecurrentChain (P ^ m) ψ) ∧
    (IsRecurrentChain P ψ ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
      IsRecurrentChain (P ^ m) ψ) := by
  have hsk := (proposition_5_4_5_iii P hψ hap).1
  have hall : IsRecurrentChain P ψ → ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m
      IsRecurrentChain (P ^ m) ψ := fun h m hm => by
    have := isMarkovKernel_pow P m
    rcases theorem_8_3_4 (P ^ m) (hsk m hm).1 with h' | h'
    · exact h'
    · exact absurd h (IsTransientChain.not_isRecurrentChain
        ⟨hψ, isTransientSet_of_skeleton P hm h'.2⟩)
  have hone : ∀ m, 1 ≤ m → (haveI := isMarkovKernel_pow P m
      IsRecurrentChain (P ^ m) ψ) → IsRecurrentChain P ψ := fun m hm h => by
    have := isMarkovKernel_pow P m
    exact ⟨hψ, fun A hA hpos x => top_le_iff.1 ((h.2 A hA hpos x).symm.le.trans
      (potKernel_skeleton_le P hm x hA))⟩
  exact ⟨⟨fun h => ⟨1, le_rfl, hall h 1 le_rfl⟩, fun ⟨m, hm, h⟩ => hone m hm h⟩,
    ⟨hall, fun h => hone 1 le_rfl (h 1 le_rfl)⟩⟩

end MeynTweedie.InvariantMeasures
