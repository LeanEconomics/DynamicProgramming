/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.AtomInvariant
import Epilogue.SplitMarginal

/-!
# Invariant measures through splitting and resolvents (MT §10.4.1)

Meyn and Tweedie, §10.4.1, pp. 241–242. `M : Minorization P` is a minorization (5.2) and
`P̌ = M.splitKernel` the split kernel on `X̌ = X × Bool`; `μ* = M.split μ`.

* **Proposition 10.4.1** (p. 241): (i) `proposition_10_4_1_i`, if `π̌` is invariant for `P̌`, then
  its marginal `π(A) = π̌(A₀ ∪ A₁)` (10.26) is invariant for `P` and `π̌ = π*`; (ii)
  `proposition_10_4_1_ii`, if `μ` is subinvariant (invariant) for `P`, then `μ*` is subinvariant
  (invariant) for `P̌`. `sigmaFinite_split`: `μ*` is σ-finite when `μ` is.
* **Proposition 10.4.2** (`proposition_10_4_2`, p. 242): a recurrent chain with a minorization on
  a set `C ∈ B⁺(X)` (in particular a strongly aperiodic chain) has a nonzero invariant measure
  `π` with `π(C) < ∞`, and every subinvariant measure is a finite multiple `c π`. The measure is
  the marginal of `μ°_α̌` for the atom `α̌ = C₁` of the split chain.
* `lintegral_sampledKernel`, `comp_sampledKernel_comp_apply`: `(μK_a)P(B) = Σₙ a(n) μPⁿ⁺¹(B)`.
* **Theorem 10.4.3** (`theorem_10_4_3`, p. 242): for `0 < ε < 1`, a σ-finite measure is invariant
  for `K_{a_ε}` iff it is invariant for `P`.

**Corrections.**
* Proposition 10.4.1 holds for every minorization, not only for strongly aperiodic chains.
* Proposition 10.4.2 needs the split set `C` to lie in `B⁺(X)` (as for Proposition 8.2.2 in
  `SplitDichotomy`): the atom `α̌` must be accessible.
* Theorem 10.4.3 needs `π` to be σ-finite (part of the book's definition of an invariant
  measure): the book's chain of equalities subtracts `π`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### Proposition 10.4.1 -/

/-- **Proposition 10.4.1 (i)** (MT p. 241): if `π̌` is invariant for the split chain, then
`π̌ = π*` for the marginal `π = π̌ ∘ fst⁻¹` (10.26), and `π` is invariant for `Φ`. -/
theorem proposition_10_4_1_i (M : Minorization P) {πs : Measure (X × Bool)}
    (h : IsInvariant M.splitKernel πs) :
    πs = M.split (πs.map Prod.fst) ∧ IsInvariant P (πs.map Prod.fst) := by
  set π0 := M.baseK ∘ₘ πs with hπ0
  have h1 : πs = M.split π0 := by
    conv_lhs => rw [← h]
    rw [Minorization.splitKernel, ← Measure.comp_assoc]
    rfl
  have h2 : πs.map Prod.fst = π0 := by
    conv_lhs => rw [h1]
    exact M.split_map_fst π0
  have h3 : M.split (P ∘ₘ π0) = M.split π0 := by
    rw [← M.split_comp_splitKernel, ← h1]
    exact h
  refine ⟨by rw [h2]; exact h1, ?_⟩
  unfold IsInvariant
  rw [h2, ← M.split_map_fst (P ∘ₘ π0), h3, M.split_map_fst]

/-- **Proposition 10.4.1 (ii)** (MT p. 241): if `μ` is subinvariant for `Φ`, then `μ*` is
subinvariant for `Φ̌`; if `μ` is invariant, so is `μ*`. -/
theorem proposition_10_4_1_ii (M : Minorization P) {μ : Measure X} :
    (IsSubinvariant P μ → IsSubinvariant M.splitKernel (M.split μ)) ∧
      (IsInvariant P μ → IsInvariant M.splitKernel (M.split μ)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold IsSubinvariant at *
    rw [M.split_comp_splitKernel]
    exact comp_le_comp M.splitK h
  · unfold IsInvariant at *
    rw [M.split_comp_splitKernel, h]

/-- `μ*` is σ-finite when `μ` is. -/
theorem sigmaFinite_split (M : Minorization P) (μ : Measure X) [SigmaFinite μ] :
    SigmaFinite (M.split μ) :=
  ⟨⟨{ set := fun n => Prod.fst ⁻¹' spanningSets μ n
      set_mem := fun _ => trivial
      finite := fun n => by
        rw [M.split_fst_preimage μ (measurableSet_spanningSets μ n)]
        exact measure_spanningSets_lt_top μ n
      spanning := by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ] }⟩⟩

/-! ### Proposition 10.4.2 -/

/-- **Proposition 10.4.2** (MT p. 242): a recurrent chain with a minorization on a set
`C ∈ B⁺(X)` has a nonzero invariant measure `π` (σ-finite, with `π(C) < ∞`), and every
subinvariant measure is `c π` for a finite constant `c`. -/
theorem proposition_10_4_2 [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    (M : Minorization P) (hC : 0 < ψ M.C) :
    ∃ π : Measure X, IsInvariantMeasure P π ∧ π ≠ 0 ∧ π M.C ≠ ∞ ∧
      ∀ μ, IsSubinvariantMeasure P μ → ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • π := by
  have := M.isMarkovKernel_splitKernel
  have hψs := M.isMaximalIrreducibility_split hrec.1
  have hrecs := M.isRecurrentChain_split_of_isRecurrentChain hrec
  have hat : IsAccessibleAtom M.splitKernel (M.split ψ) M.checkAlpha :=
    ((M.theorem_5_1_3_ii ψ).2 hrec.1.2.1 hC).2.2 _ hψs
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hC.ne'
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hinv : IsInvariant M.splitKernel (atomMeasure M.splitKernel hat.1.1 (c, true)) :=
    ((theorem_10_2_1_i hat ha).2).2 hrecs
  obtain ⟨hsplit, hπinv⟩ := proposition_10_4_1_i M hinv
  set πs := atomMeasure M.splitKernel hat.1.1 (c, true) with hπs
  set π := πs.map Prod.fst with hπ
  have hα1 : πs M.checkAlpha = 1 := by
    rw [hπs, atomMeasure_self]
    exact (hat.isRecurrentChain_iff ha).1 hrecs
  have hπC : M.δ * π M.C = 1 := by
    have h1 := M.split_apply_true π M.measurableSet_C
    rw [inter_self, ← hsplit] at h1
    rw [← h1]
    exact hα1
  have hπCfin : π M.C ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top M.δ_pos.ne'] at hπC
    exact ENNReal.top_ne_one hπC
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h] at hπC
    simp at hπC
  have hσ : SigmaFinite π :=
    proposition_10_1_2_i hrec.1.2.1 hπinv.isSubinvariant M.measurableSet_C hC hπCfin
  refine ⟨π, ⟨hσ, hπinv⟩, hπ0, hπCfin, fun μ hμ => ?_⟩
  have := hμ.1
  have hμs : IsSubinvariantMeasure M.splitKernel (M.split μ) :=
    ⟨sigmaFinite_split M μ, (proposition_10_4_1_ii M).1 hμ.2⟩
  have he := hμs.eq_smul_atomMeasure hat hrecs ha
  refine ⟨M.split μ M.checkAlpha, (hμs.measure_atom_lt_top hψs hat.1).ne, ?_⟩
  calc μ = (M.split μ).map Prod.fst := (M.split_map_fst μ).symm
    _ = (M.split μ M.checkAlpha • πs).map Prod.fst :=
        congrArg (fun m : Measure (X × Bool) => m.map Prod.fst) he
    _ = M.split μ M.checkAlpha • π := Measure.map_smul _ measurable_fst.aemeasurable

/-! ### Theorem 10.4.3 -/

/-- `∫ f dK_a(x) = Σₙ a(n) ∫ f dPⁿ(x)`. -/
theorem lintegral_sampledKernel (P : Kernel X X) (a : ℕ → ℝ≥0∞) (x : X) (f : X → ℝ≥0∞) :
    ∫⁻ y, f y ∂sampledKernel P a x = ∑' n, a n * ∫⁻ y, f y ∂(P ^ n) x := by
  change ∫⁻ y, f y ∂(Measure.sum fun n => a n • (P ^ n) x) = _
  rw [lintegral_sum_measure]
  exact tsum_congr fun n => lintegral_smul_measure _ _

/-- `(μK_a)P(B) = Σₙ a(n) μPⁿ⁺¹(B)`. -/
theorem comp_sampledKernel_comp_apply (P : Kernel X X) (a : ℕ → ℝ≥0∞) (μ : Measure X)
    {B : Set X} (hB : MeasurableSet B) :
    (P ∘ₘ (sampledKernel P a ∘ₘ μ)) B = ∑' n, a n * ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) B := by
  rw [measure_kernel_apply _ _ hB, Measure.lintegral_bind (Kernel.aemeasurable _)
    (Kernel.measurable_coe _ hB).aemeasurable]
  simp_rw [lintegral_sampledKernel P a _ (fun y => P y B)]
  simp_rw [← pow_succ_apply' P _ _ hB]
  rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hB).const_mul _).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hB), measure_kernel_apply μ _ hB]

/-- Two σ-finite-dominated measures agree if they agree on every measurable set of finite
`π`-measure. -/
theorem eq_of_eq_on_finite {π ν : Measure X} [SigmaFinite π]
    (h : ∀ B, MeasurableSet B → π B ≠ ∞ → ν B = π B) : ν = π := by
  refine (Measure.ext_iff_of_iUnion_eq_univ (iUnion_spanningSets π)).2 fun i => ?_
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
  exact h _ (hB.inter (measurableSet_spanningSets π i))
    (ne_top_of_le_ne_top (measure_spanningSets_lt_top π i).ne (measure_mono inter_subset_right))

/-- **Theorem 10.4.3** (MT p. 242): for `0 < ε < 1`, a σ-finite measure `π` is invariant for the
resolvent `K_{a_ε}` iff it is invariant for `P`. -/
theorem theorem_10_4_3 [IsMarkovKernel P] {ε : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε < 1)
    {π : Measure X} [SigmaFinite π] : IsInvariant (resolvent P ε) π ↔ IsInvariant P π := by
  refine ⟨fun hK => ?_, fun h => h.resolvent hε1⟩
  have hεtop : ε ≠ ∞ := (hε1.trans ENNReal.one_lt_top).ne
  refine eq_of_eq_on_finite fun B hB hfin => ?_
  -- `πP(B) = Σₙ (1 − ε) εⁿ πPⁿ⁺¹(B)`
  have e1 := comp_sampledKernel_comp_apply P (fun n => (1 - ε) * ε ^ n) π hB
  rw [← resolvent] at e1
  unfold IsInvariant at hK
  rw [hK] at e1
  -- `π(B) = (1 − ε) π(B) + ε πP(B)`
  have e2 : π B = (1 - ε) * π B + ε * (P ∘ₘ π) B := by
    conv_lhs => rw [← hK]
    rw [resolvent, sampledKernel_comp_apply P _ π hB, tsum_eq_zero_add' ENNReal.summable,
      e1, ← ENNReal.tsum_mul_left]
    congr 1
    · rw [pow_zero, mul_one, pow_zero]
      exact congrArg _ (congrArg (fun m : Measure X => m B) Measure.id_comp)
    · exact tsum_congr fun n => by rw [pow_succ]; ring
  have e3 : π B = (1 - ε) * π B + ε * π B := by
    rw [← add_mul, tsub_add_cancel_of_le hε1.le, one_mul]
  have e4 : ε * (P ∘ₘ π) B = ε * π B := by
    have := e2.symm.trans e3
    exact (ENNReal.add_right_inj (ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
      hfin)).1 this
  exact (ENNReal.mul_right_inj hε0.ne' hεtop).1 e4

end MeynTweedie.Epilogue
