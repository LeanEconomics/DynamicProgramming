/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.SumsOfTransitions
import GeneralizedDrift.AtomHittingBounds
import GeneralizedDrift.AperiodicErgodic

/-!
# Sums of transition probabilities without an atom (MT Theorem 13.4.4)

Meyn and Tweedie, §13.4.3, p. 333. The state space is countably generated. The book's proof is
three sentences: the split measures of regular measures are regular (from Theorem 11.3.12), the
result passes from the split chain to the chain by (13.57), and Proposition 13.3.2 moves to a
skeleton. Each step is proved here.

**Split chains.**
* `Minorization.lintegral_meanReturnTime_split`: `Ě_{λ*}[τ_{A × {0,1}}] = E_λ[τ_A]`.
* `Minorization.lintegral_meanReturnTime_checkAlpha_ne_top`: for a positive chain with a
  minorization on `C ∈ B⁺(X)` and a regular `λ`, `Ě_{λ*}[τ_{α̌}] < ∞`. The atom `α̌` is regular
  for `Φ̌` (Kac and Theorem 11.3.14), so `V̌ = V_{α̌}` solves (V2) and `Ě_z[τ_{α̌}] ≤ V̌(z) + b`; a
  sublevel set `R = {V̌(·, 0) ≤ n}` lies in `B⁺(X)`, `Ě_z[τ_{α̌}]` is bounded on `R × {0, 1}`, and
  the strong Markov property gives `Ě_{λ*}[τ_{α̌}] ≤ E_λ[τ_R] + const`.
* `tsum_ofReal_tvNorm_comp_le`: Theorem 13.4.3's bound from an initial law,
  `Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ E_λ[τ_α](1 + Var(u)E_α[τ_α])`.
* `exists_tsum_tvNorm_le_split`: the strongly aperiodic case, pointwise:
  `Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖ ≤ G(x) + G(y)` with `λ(G) < ∞` for regular `λ`.

**Skeletons.**
* `IsRegularMeasure.pow`: for a positive aperiodic chain, a regular `λ` is regular for every
  skeleton `Pᵐ`, through a drift function for `Pᵐ` built from `V_C` (Theorem 11.3.12 (ii) for `P`,
  (i) for `Pᵐ`) and a set that is small for `Pᵐ` by aperiodicity. The book does not state or prove
  this ("regularity of skeletons").
* `tsum_comp_div`, `tsum_ofReal_tvNorm_le_skeleton`: Proposition 13.3.2 for sums,
  `Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖ ≤ m (2 + Σₖ ‖Pᵐ⁽ᵏ⁺¹⁾(x, ·) − Pᵐ⁽ᵏ⁺¹⁾(y, ·)‖)`.

**Results.**
* `exists_tsum_tvNorm_le`: the pointwise form for positive aperiodic chains.
* **Theorem 13.4.4** (`theorem_13_4_4`, p. 333), (13.81): for regular `λ`, `μ`,
  `∫ λ(dx) ∫ μ(dy) Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞`.
* `theorem_13_4_4_states`, `theorem_13_4_4_regular`: `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` for regular
  states `x`, `y`, and for all `x`, `y` in a regular chain.

**Hypotheses.** The book assumes a positive Harris chain; positivity and aperiodicity suffice, as
for Theorem 13.4.3. Sums start at `n = 1`, as in the book.

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Regularity of split measures -/

/-- Hitting times of sets `A × {0, 1}` by the split chain are hitting times of `A`:
`Ě_{λ*}[τ_{Ǎ}] = E_λ[τ_A]` with `Ǎ = A × {0, 1}`. -/
theorem Minorization.lintegral_meanReturnTime_split {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {A : Set X} (hA : MeasurableSet A) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ z, meanReturnTime M.splitKernel (Prod.fst ⁻¹' A) z ∂M.split μ =
      ∫⁻ x, meanReturnTime P A x ∂μ := by
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_pathKernel M.splitKernel
  have := isMarkovKernel_pathKernel P
  have hAs : MeasurableSet (Prod.fst ⁻¹' A : Set (X × Bool)) := measurable_fst hA
  calc ∫⁻ z, meanReturnTime M.splitKernel (Prod.fst ⁻¹' A) z ∂M.split μ
      = ∫⁻ ω, ENat.toENNReal (firstReturn A fun n => (ω n).1)
          ∂pathMeasure M.splitKernel (M.split μ) := by
        rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
          (f := fun ω : ℕ → X × Bool => ENat.toENNReal (firstReturn A fun n => (ω n).1))
          (measurable_toENNReal_firstReturn hAs).aemeasurable]
        rfl
    _ = ∫⁻ ω, ENat.toENNReal (firstReturn A ω) ∂pathMeasure P μ :=
        M.lintegral_split_fst μ (measurable_toENNReal_firstReturn hA)
    _ = ∫⁻ x, meanReturnTime P A x ∂μ := by
        rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
          (measurable_toENNReal_firstReturn hA).aemeasurable]
        rfl

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Split measures of regular measures reach the atom in finite mean time** (the step of the
proof of Theorem 13.4.4 that the book derives from Theorem 11.3.12). Let `P` be positive with a
minorization on `C ∈ B⁺(X)` and let `λ` be regular. Then `Ě_{λ*}[τ_{α̌}] < ∞`. -/
theorem Minorization.lintegral_meanReturnTime_checkAlpha_ne_top {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ) (M : Minorization P)
    (hψC : 0 < ψ M.C) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : IsRegularMeasure P ψ μ) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.split μ ≠ ∞ := by
  have := M.isMarkovKernel_splitKernel
  have hψ := hpos.1
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
  obtain ⟨-, b, hb, hdrift, -⟩ := theorem_11_3_11_ii hψs hreg hαpos
  obtain ⟨-, hfull, -, -⟩ := proposition_11_3_13 hψs hreg hαpos
  have hαm := M.measurableSet_checkAlpha
  have hVm := measurable_regV M.splitKernel hαm
  -- `Ě_z[τ_α̌] ≤ V̌(z) + b`
  have hτ : ∀ z, meanReturnTime M.splitKernel M.checkAlpha z ≤
      regV M.splitKernel M.checkAlpha z + b := fun z => by
    refine (theorem_11_3_4 hVm hαm hdrift z).trans (add_le_add le_rfl ?_)
    by_cases hz : z ∈ M.checkAlpha
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]; exact zero_le
  -- on the bottom level `V̌` is bounded
  set K₁ := 1 + meanReturnTime M.splitKernel M.checkAlpha (c, true) with hK₁
  have hV1 : ∀ x, regV M.splitKernel M.checkAlpha (x, true) ≤ K₁ := fun x =>
    (regV_le M.splitKernel hαm (x, true)).trans (add_le_add le_rfl
      (M.isAtom_bottom.meanReturnTime_eq hαm
        ⟨mem_univ _, mem_singleton _⟩ ⟨mem_univ _, mem_singleton _⟩).le)
  have hK₁ne : K₁ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin⟩
  have hV0m : Measurable fun x : X => regV M.splitKernel M.checkAlpha (x, false) :=
    hVm.comp (measurable_id.prodMk measurable_const)
  -- `V̌(·, 0)` is finite `ψ`-a.e.
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
  -- some sublevel set `R = {V̌(·, 0) ≤ n}` lies in `B⁺(X)`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < ψ {x | regV M.splitKernel M.checkAlpha (x, false) ≤ n} := by
    by_contra hcon
    push Not at hcon
    apply hψ.1
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc ψ univ ≤ ψ (⋃ n : ℕ, {x | regV M.splitKernel M.checkAlpha (x, false) ≤ n}) + ψ A := by
          refine (measure_mono fun x _ => ?_).trans (measure_union_le _ _)
          by_cases hx : regV M.splitKernel M.checkAlpha (x, false) = ∞
          · exact Or.inr hx
          · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
            exact Or.inl (mem_iUnion.2 ⟨n, hn.le⟩)
      _ = 0 := by
          rw [hA0, add_zero]
          exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon n)
  set R := {x | regV M.splitKernel M.checkAlpha (x, false) ≤ n} with hRdef
  have hRm : MeasurableSet R := measurableSet_le hV0m measurable_const
  -- from `Ř = R × {0, 1}` the split chain reaches `α̌` in bounded mean time
  have hbound : ∀ z ∈ (Prod.fst ⁻¹' R : Set (X × Bool)),
      meanReturnTime M.splitKernel M.checkAlpha z ≤ (n + K₁) + b := by
    rintro ⟨x, i⟩ hx
    refine (hτ (x, i)).trans (add_le_add ?_ le_rfl)
    cases i
    · exact (hx : regV M.splitKernel M.checkAlpha (x, false) ≤ n).trans le_self_add
    · exact (hV1 x).trans le_add_self
  have hle := meanReturnTime_le_add_of_forall_le (measurable_fst hRm) hαm hbound
  have : IsProbabilityMeasure (M.split μ) := M.isProbabilityMeasure_split μ
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    M.lintegral_meanReturnTime_split hRm μ]
  exact ENNReal.add_ne_top.2 ⟨hμ R hRm hn,
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, hK₁ne⟩, hb⟩⟩

/-! ### The strongly aperiodic case -/

/-- The summability bound of Theorem 13.4.3 from an initial probability `λ`, in `[0, ∞]`:
`Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ E_λ[τ_α](1 + Var(u)E_α[τ_α])`. -/
theorem tsum_ofReal_tvNorm_comp_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hLa : hitProb P α a = 1)
    (hEa : meanReturnTime P α a ≠ ∞) (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a)))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ)
      ((P ^ (n + 1) : Kernel X X) a)) ≤
      (∫⁻ x, meanReturnTime P α x ∂μ) * ENNReal.ofReal (1 + renewalVar (entryLaw P hα.1
        (Measure.dirac a)) * (meanReturnTime P α a).toReal) := by
  have hV : 0 ≤ renewalVar (entryLaw P hα.1 (Measure.dirac a)) :=
    tsum_nonneg fun _ => abs_nonneg _
  have hc : ENNReal.ofReal (1 + renewalVar (entryLaw P hα.1 (Measure.dirac a)) *
      (meanReturnTime P α a).toReal) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  by_cases hx : ∫⁻ x, meanReturnTime P α x ∂μ = ∞
  · rw [hx, ENNReal.top_mul hc]; exact le_top
  · obtain ⟨hs, hle⟩ := summable_tvNorm_atom hα ha hLa hEa hap μ hx
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => tvNorm_nonneg _ _) hs,
      ← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hle

/-- From a bound `s(x, y) ≤ G(x) + G(y)` to `∫ λ(dx) ∫ μ(dy) s(x, y) ≤ λ(G) + μ(G)`. -/
theorem lintegral_lintegral_le_of_le_add {s : X → X → ℝ≥0∞} {G : X → ℝ≥0∞}
    (h : ∀ x y, s x y ≤ G x + G y) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∫⁻ x, ∫⁻ y, s x y ∂ν ∂μ ≤ ∫⁻ x, G x ∂μ + ∫⁻ y, G y ∂ν :=
  calc ∫⁻ x, ∫⁻ y, s x y ∂ν ∂μ ≤ ∫⁻ x, ∫⁻ y, (G x + G y) ∂ν ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => h x y
    _ = ∫⁻ x, (G x + ∫⁻ y, G y ∂ν) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_add_left' measurable_const.aemeasurable, lintegral_const, measure_univ,
          mul_one]
    _ = ∫⁻ x, G x ∂μ + ∫⁻ y, G y ∂ν := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.4.4, the strongly aperiodic case**, pointwise: for a positive chain with a
minorization on `C ∈ B⁺(X)` with `ν(C) > 0` there is a measurable `G` with
`Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖ ≤ G(x) + G(y)` and `λ(G) < ∞` for every regular `λ`. Here
`G(x) = Ě_{x*}[τ_{α̌}] (1 + Var(u) Ě_{α̌}[τ_{α̌}])`: the bound (13.57) passes to the split chain,
where Theorem 13.4.3 applies to its atom `α̌`. -/
theorem exists_tsum_tvNorm_le_split {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C) :
    ∃ G : X → ℝ≥0∞, Measurable G ∧
      (∀ x y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
        ((P ^ (n + 1) : Kernel X X) y)) ≤ G x + G y) ∧
      ∀ μ : Measure X, IsProbabilityMeasure μ → IsRegularMeasure P ψ μ → ∫⁻ x, G x ∂μ ≠ ∞ := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_splitK
  have hψs := M.isMaximalIrreducibility_split hpos.1
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
  have hEa := (theorem_10_2_2 hatom ha).1.1 hposs
  have hLa := hitProb_eq_one_of_meanReturnTime_ne_top M.measurableSet_checkAlpha hEa
  have hap := M.isAperiodicLaw_entryLaw_checkAlpha hνC (c := c)
  set K := ENNReal.ofReal (1 + renewalVar (entryLaw M.splitKernel M.measurableSet_checkAlpha
    (Measure.dirac (c, true))) * (meanReturnTime M.splitKernel M.checkAlpha (c, true)).toReal)
    with hK
  have hm := measurable_meanReturnTime M.splitKernel M.measurableSet_checkAlpha
  have hsd : ∀ x, M.split (Measure.dirac x) = M.splitK x := fun x =>
    Measure.dirac_bind M.splitK.measurable x
  -- the atom bound from `x*`
  have hpt : ∀ x, ∑' n, ENNReal.ofReal (tvNorm
      ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split (Measure.dirac x))
      ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true))) ≤
      (∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.splitK x) * K := fun x => by
    have : IsProbabilityMeasure (M.split (Measure.dirac x)) := M.isProbabilityMeasure_split _
    have h := tsum_ofReal_tvNorm_comp_le M.isAtom_checkAlpha ha hLa hEa hap
      (M.split (Measure.dirac x))
    rw [hsd x] at h ⊢
    exact h
  refine ⟨fun x => (∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.splitK x) * K,
    hm.lintegral_kernel.mul_const K, fun x y => ?_, fun μ hμp hμ => ?_⟩
  · refine le_trans ?_ (add_le_add (hpt x) (hpt y))
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    have := isMarkovKernel_pow P (n + 1)
    have := isMarkovKernel_pow M.splitKernel (n + 1)
    have : IsProbabilityMeasure (M.split (Measure.dirac x)) := M.isProbabilityMeasure_split _
    have : IsProbabilityMeasure (M.split (Measure.dirac y)) := M.isProbabilityMeasure_split _
    rw [← ENNReal.ofReal_add (tvNorm_nonneg _ _) (tvNorm_nonneg _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := tvNorm_le_split M (n + 1) (Measure.dirac x) ((P ^ (n + 1) : Kernel X X) y)
    rw [dirac_kernel, ← dirac_kernel (P ^ (n + 1) : Kernel X X) y,
      ← M.split_comp_splitKernel_pow] at h1
    rw [dirac_kernel] at h1
    calc tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
        ≤ tvNorm ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ
            M.split (Measure.dirac x))
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ
            M.split (Measure.dirac y)) := h1
      _ ≤ tvNorm ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ
            M.split (Measure.dirac x))
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true)) +
          tvNorm ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true))
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ
            M.split (Measure.dirac y)) := tvNorm_triangle _ _ _
      _ = _ := by rw [tvNorm_comm ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool))
            (c, true))]
  · have hb : ∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.split μ =
        ∫⁻ x, ∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.splitK x ∂μ :=
      Measure.lintegral_bind (Kernel.aemeasurable _) hm.aemeasurable
    rw [lintegral_mul_const _ hm.lintegral_kernel, ← hb]
    exact ENNReal.mul_ne_top (M.lintegral_meanReturnTime_checkAlpha_ne_top hpos hψC μ hμ)
      ENNReal.ofReal_ne_top

/-! ### Skeletons -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Regular measures are regular for the skeletons** (used for Theorem 13.4.4 in the general
aperiodic case). Let `P` be positive and aperiodic, `m ≥ 1`, and `λ` a regular probability. By
Theorem 11.3.12 (ii), `V = V_C` solves (V2) for a small regular set `C ∈ B⁺(X)` with `λ(V) < ∞`.
Iterating, `PᵐV + m ≤ V + b Σ_{j<m} Pʲ(·, C)`, so `W = 2V` solves (V2) for `Pᵐ` and the set
`C' = {2m ≤ 2b Σ_{j<m} Pʲ(·, C) + 1}`, which is small for `Pᵐ` by aperiodicity; Theorem 11.3.12 (i)
for `Pᵐ` makes `λ` regular for `Pᵐ`. -/
theorem IsRegularMeasure.pow {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {m : ℕ} (hm : 1 ≤ m) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsRegularMeasure P ψ μ) :
    haveI := isMarkovKernel_pow P m
    IsRegularMeasure (P ^ m : Kernel X X) ψ μ := by
  have := isMarkovKernel_pow P m
  have hψ := hpos.1
  have hψm : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((theorem_10_4_5_positive hψ hap).1.1 hpos m hm).1
  obtain ⟨R, hR, hψR⟩ := exists_regularSet_of_isPositive hpos
  obtain ⟨C, hCR, k, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ hR.1 hψR
  obtain ⟨V, b, hV, hb, hdrift, hμV⟩ := theorem_11_3_12_ii hμ (hR.subset hC.1 hCR) hψC
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  -- (V2) iterated: `PʲV + j ≤ V + b Σ_{i<j} Pⁱ(·, C)`
  have hiter : ∀ j x, ∫⁻ y, V y ∂(P ^ j : Kernel X X) x + j ≤
      V x + b * ∑ i ∈ range j, (P ^ i : Kernel X X) x C := by
    intro j
    induction j with
    | zero =>
      intro x
      rw [pow_zero_apply, lintegral_dirac' _ hV, Nat.cast_zero, add_zero, range_zero, sum_empty,
        mul_zero, add_zero]
    | succ j ih =>
      intro x
      have := isMarkovKernel_pow P j
      have hstep : ∫⁻ y, V y ∂(P ^ (j + 1) : Kernel X X) x + 1 ≤
          ∫⁻ y, V y ∂(P ^ j : Kernel X X) x + b * (P ^ j : Kernel X X) x C := by
        rw [pow_succ']
        change ∫⁻ y, V y ∂(P ∘ₖ (P ^ j : Kernel X X)) x + 1 ≤ _
        rw [Kernel.lintegral_comp _ _ _ hV]
        calc ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ j : Kernel X X) x + 1
            = ∫⁻ y, (∫⁻ z, V z ∂P y + 1) ∂(P ^ j : Kernel X X) x := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ ∫⁻ y, (V y + C.indicator (fun _ => b) y) ∂(P ^ j : Kernel X X) x :=
              lintegral_mono hdrift
          _ = _ := by rw [lintegral_add_left hV, lintegral_indicator_const hC.1]
      calc ∫⁻ y, V y ∂(P ^ (j + 1) : Kernel X X) x + ((j + 1 : ℕ) : ℝ≥0∞)
          = (∫⁻ y, V y ∂(P ^ (j + 1) : Kernel X X) x + 1) + j := by
            rw [Nat.cast_succ]; ring
        _ ≤ (∫⁻ y, V y ∂(P ^ j : Kernel X X) x + b * (P ^ j : Kernel X X) x C) + j :=
            add_le_add hstep le_rfl
        _ = (∫⁻ y, V y ∂(P ^ j : Kernel X X) x + j) + b * (P ^ j : Kernel X X) x C := by ring
        _ ≤ (V x + b * ∑ i ∈ range j, (P ^ i : Kernel X X) x C) +
              b * (P ^ j : Kernel X X) x C := add_le_add (ih x) le_rfl
        _ = V x + b * ∑ i ∈ range (j + 1), (P ^ i : Kernel X X) x C := by
            rw [sum_range_succ, mul_add, add_assoc]
  -- the drift for the skeleton
  set S : X → ℝ≥0∞ := fun x => ∑ i ∈ range m, (P ^ i : Kernel X X) x C with hSdef
  have hSm : Measurable S :=
    Finset.measurable_sum _ fun i _ => Kernel.measurable_coe _ hC.1
  have hSle : ∀ x, S x ≤ m := fun x => by
    calc S x ≤ ∑ _i ∈ range m, (1 : ℝ≥0∞) := sum_le_sum fun i _ => by
          have := isMarkovKernel_pow P i; exact prob_le_one
      _ = m := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
  set C' : Set X := {x | (2 * m : ℝ≥0∞) ≤ 2 * b * S x + 1} with hC'def
  have hC'm : MeasurableSet C' :=
    measurableSet_le measurable_const ((measurable_const.mul hSm).add measurable_const)
  have hm1 : (1 : ℝ≥0∞) ≤ 2 * m := by
    calc (1 : ℝ≥0∞) ≤ 2 * 1 := by norm_num
      _ ≤ 2 * m := mul_le_mul' le_rfl (by exact_mod_cast hm)
  have hW : Measurable fun x => 2 * V x := measurable_const.mul hV
  have hdriftW : DriftV2 (P ^ m : Kernel X X) (fun x => 2 * V x) (2 * b * m) C' := by
    intro x
    have h2 : ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + 2 * m ≤ 2 * V x + 2 * b * S x := by
      calc ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + 2 * m
          = 2 * (∫⁻ y, V y ∂(P ^ m : Kernel X X) x + m) := by
            rw [lintegral_const_mul _ hV]; ring
        _ ≤ 2 * (V x + b * S x) := mul_le_mul' le_rfl (hiter m x)
        _ = 2 * V x + 2 * b * S x := by ring
    by_cases hx : x ∈ C'
    · rw [indicator_of_mem hx]
      calc ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + 1
          ≤ ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + 2 * m := add_le_add le_rfl hm1
        _ ≤ 2 * V x + 2 * b * S x := h2
        _ ≤ 2 * V x + 2 * b * m := add_le_add le_rfl (mul_le_mul' le_rfl (hSle x))
    · rw [indicator_of_notMem hx, add_zero]
      have hx' : ¬ ((2 * m : ℝ≥0∞) ≤ 2 * b * S x + 1) := hx
      have hlt : 2 * b * S x + 1 < 2 * m := not_le.1 hx'
      have hfin : 2 * b * S x ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt le_self_add hlt)
      refine (ENNReal.add_le_add_iff_right hfin).1 ?_
      calc ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + 1 + 2 * b * S x
          = ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + (2 * b * S x + 1) := by ring
        _ ≤ ∫⁻ y, 2 * V y ∂(P ^ m : Kernel X X) x + 2 * m := add_le_add le_rfl hlt.le
        _ ≤ 2 * V x + 2 * b * S x := h2
  -- `C'` is small for the skeleton
  have hNm : N + m ≤ m * (N + 1) := by nlinarith
  have hδ : ∀ j, ∃ δ : ℝ≥0∞, j < m → 0 < δ ∧
      ∀ x ∈ C, δ • ν ≤ (P ^ (m * (N + 1) - j) : Kernel X X) x := fun j => by
    by_cases hj : j < m
    · obtain ⟨-, δ, hδ, hle⟩ := hN (m * (N + 1) - j) (by omega)
      exact ⟨δ, fun _ => ⟨hδ, hle⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose δf hδf using hδ
  set δ := (range m).inf δf with hδdef
  have hδpos : 0 < δ :=
    (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun j hj => (hδf j (mem_range.1 hj)).1
  have hkey : ∀ x, ∀ j < m, ∀ A, MeasurableSet A →
      (P ^ j : Kernel X X) x C * (δ * ν A) ≤ (P ^ (m * (N + 1)) : Kernel X X) x A := by
    intro x j hj A hA
    have hsplit : m * (N + 1) = j + (m * (N + 1) - j) := by omega
    rw [hsplit, pow_add_eq, Kernel.comp_apply' _ _ _ hA]
    calc (P ^ j : Kernel X X) x C * (δ * ν A)
        = ∫⁻ _y in C, δ * ν A ∂(P ^ j : Kernel X X) x := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in C, (P ^ (m * (N + 1) - j) : Kernel X X) y A ∂(P ^ j : Kernel X X) x := by
          refine setLIntegral_mono (Kernel.measurable_coe _ hA) fun y hy => ?_
          have h1 := (hδf j hj).2 y hy A
          rw [Measure.smul_apply, smul_eq_mul] at h1
          exact (mul_le_mul' (Finset.inf_le (mem_range.2 hj)) le_rfl).trans h1
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have h2b : 2 * b ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hb
  have hmne : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  set ν'' : Measure X := ((2 * b)⁻¹ * δ * (m : ℝ≥0∞)⁻¹) • ν with hν''
  have hν''0 : ν'' ≠ 0 := by
    intro h0
    have h1 : ν'' C = 0 := by rw [h0]; rfl
    rw [hν'', Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h1 | h1
      · rcases mul_eq_zero.1 h1 with h1 | h1
        · exact ENNReal.inv_ne_zero.2 h2b h1
        · exact hδpos.ne' h1
      · exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m) h1
    · exact hνC.ne' h1
  have hsmall : IsSmallSet (P ^ m : Kernel X X) (N + 1) ν'' C' := by
    refine ⟨hC'm, Nat.succ_pos N, hν''0, fun x hx => Measure.le_intro fun A hA _ => ?_⟩
    rw [← pow_mul]
    have hx' : (2 * m : ℝ≥0∞) ≤ 2 * b * S x + 1 := hx
    have h1 : (1 : ℝ≥0∞) ≤ 2 * b * S x := by
      refine (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 ?_
      calc (1 : ℝ≥0∞) + 1 = 2 * 1 := by norm_num
        _ ≤ 2 * m := mul_le_mul' le_rfl (by exact_mod_cast hm)
        _ ≤ 2 * b * S x + 1 := hx'
    have hSfin : S x ≠ ∞ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top m) (hSle x)
    have hinv : (2 * b)⁻¹ ≤ S x :=
      (ENNReal.inv_le_iff_le_mul (fun h => absurd h hSfin) (fun h => absurd h h2b)).2 h1
    have hsum : S x * (δ * ν A) ≤ m * (P ^ (m * (N + 1)) : Kernel X X) x A := by
      rw [hSdef, sum_mul]
      calc ∑ i ∈ range m, (P ^ i : Kernel X X) x C * (δ * ν A)
          ≤ ∑ _i ∈ range m, (P ^ (m * (N + 1)) : Kernel X X) x A :=
            sum_le_sum fun i hi => hkey x i (mem_range.1 hi) A hA
        _ = m * (P ^ (m * (N + 1)) : Kernel X X) x A := by
            rw [sum_const, card_range, nsmul_eq_mul]
    rw [hν'', Measure.smul_apply, smul_eq_mul]
    calc (2 * b)⁻¹ * δ * (m : ℝ≥0∞)⁻¹ * ν A = (m : ℝ≥0∞)⁻¹ * ((2 * b)⁻¹ * (δ * ν A)) := by ring
      _ ≤ (m : ℝ≥0∞)⁻¹ * (S x * (δ * ν A)) := mul_le_mul' le_rfl (mul_le_mul' hinv le_rfl)
      _ ≤ (m : ℝ≥0∞)⁻¹ * (m * (P ^ (m * (N + 1)) : Kernel X X) x A) := mul_le_mul' le_rfl hsum
      _ = (P ^ (m * (N + 1)) : Kernel X X) x A := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hmne (ENNReal.natCast_ne_top m), one_mul]
  have hpet : IsPetite (P ^ m : Kernel X X) C' := ⟨_, _, proposition_5_5_3 hsmall⟩
  refine theorem_11_3_12_i hψm hW (ENNReal.mul_ne_top h2b (ENNReal.natCast_ne_top m)) hpet
    hdriftW ?_
  rw [lintegral_const_mul _ hV]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hμV

omit [MeasurableSpace X] in
/-- `Σₙ f(n / m) = m Σ_q f(q)` in `[0, ∞]`. -/
theorem tsum_comp_div (f : ℕ → ℝ≥0∞) {m : ℕ} (hm : 1 ≤ m) :
    ∑' n, f (n / m) = m * ∑' q, f q := by
  have : NeZero m := ⟨by omega⟩
  calc ∑' n, f (n / m) = ∑' p : ℕ × Fin m, f p.1 :=
        (Nat.divModEquiv m).tsum_eq (fun p : ℕ × Fin m => f p.1)
    _ = ∑' q, ∑' _r : Fin m, f q := ENNReal.tsum_prod (f := fun q (_ : Fin m) => f q)
    _ = ∑' q, m * f q := by
        refine tsum_congr fun q => ?_
        rw [tsum_fintype, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = m * ∑' q, f q := ENNReal.tsum_mul_left

/-- **Passing to a skeleton** (Proposition 13.3.2 for sums): since `‖Pⁿ(x, ·) − Pⁿ(y, ·)‖` does
not increase with `n`, `Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖ ≤ m (2 + Σₖ ‖(Pᵐ)ᵏ⁺¹(x, ·) − (Pᵐ)ᵏ⁺¹(y, ·)‖)`,
in `[0, ∞]`. -/
theorem tsum_ofReal_tvNorm_le_skeleton (P : Kernel X X) [IsMarkovKernel P] {m : ℕ}
    (hm : 1 ≤ m) (x y : X) :
    ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)) ≤
      m * (2 + ∑' k, ENNReal.ofReal (tvNorm (((P ^ m) ^ (k + 1) : Kernel X X) x)
        (((P ^ m) ^ (k + 1) : Kernel X X) y))) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ n,
      a n = tvNorm ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) y) := ⟨_, fun _ => rfl⟩
  have hanti : Antitone a := antitone_nat_of_succ_le fun n => by
    have := isMarkovKernel_pow P n
    have h1 : ∀ z, (P ^ (n + 1) : Kernel X X) z = P ∘ₘ (P ^ n : Kernel X X) z := fun z => by
      rw [pow_succ']; rfl
    rw [ha, ha, h1, h1]
    exact tvNorm_comp_le P _ _
  have hg0 : ENNReal.ofReal (a (m * 0)) ≤ 2 := by
    have h := tvNorm_le_add_measureReal (Measure.dirac x) (Measure.dirac y)
    rw [measureReal_def, measureReal_def, measure_univ, measure_univ, ENNReal.toReal_one] at h
    rw [mul_zero, ha, pow_zero_apply, pow_zero_apply]
    calc ENNReal.ofReal (tvNorm (Measure.dirac x) (Measure.dirac y)) ≤ ENNReal.ofReal (1 + 1) :=
          ENNReal.ofReal_le_ofReal h
      _ = 2 := by norm_num
  have hlhs : ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y)) = ∑' n, ENNReal.ofReal (a (n + 1)) :=
    tsum_congr fun n => by rw [ha]
  have hrhs : ∑' k, ENNReal.ofReal (tvNorm (((P ^ m) ^ (k + 1) : Kernel X X) x)
      (((P ^ m) ^ (k + 1) : Kernel X X) y)) = ∑' k, ENNReal.ofReal (a (m * (k + 1))) :=
    tsum_congr fun k => by rw [ha, pow_mul]
  rw [hlhs, hrhs]
  calc ∑' n, ENNReal.ofReal (a (n + 1)) ≤ ∑' n, ENNReal.ofReal (a (m * ((n + 1) / m))) :=
        ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (hanti (Nat.mul_div_le (n + 1) m))
    _ ≤ ∑' n, ENNReal.ofReal (a (m * (n / m))) := by
        rw [tsum_eq_zero_add' (f := fun n => ENNReal.ofReal (a (m * (n / m)))) ENNReal.summable]
        exact le_add_self
    _ = m * ∑' q, ENNReal.ofReal (a (m * q)) :=
        tsum_comp_div (fun q => ENNReal.ofReal (a (m * q))) hm
    _ = m * (ENNReal.ofReal (a (m * 0)) + ∑' k, ENNReal.ofReal (a (m * (k + 1)))) := by
        rw [tsum_eq_zero_add' (f := fun q => ENNReal.ofReal (a (m * q))) ENNReal.summable]
    _ ≤ m * (2 + ∑' k, ENNReal.ofReal (a (m * (k + 1)))) :=
        mul_le_mul' le_rfl (add_le_add hg0 le_rfl)

/-! ### Theorem 13.4.4 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.4.4**, pointwise form: for a positive aperiodic chain there is a measurable `G`
with `Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖ ≤ G(x) + G(y)` and `λ(G) < ∞` for every regular probability
`λ`. The proof passes to a skeleton with a minorization on a set in `B⁺(X)`
(`tsum_ofReal_tvNorm_le_skeleton`), for which regular measures stay regular
(`IsRegularMeasure.pow`), and applies the strongly aperiodic case to it. -/
theorem exists_tsum_tvNorm_le {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) :
    ∃ G : X → ℝ≥0∞, Measurable G ∧
      (∀ x y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
        ((P ^ (n + 1) : Kernel X X) y)) ≤ G x + G y) ∧
      ∀ μ : Measure X, IsProbabilityMeasure μ → IsRegularMeasure P ψ μ → ∫⁻ x, G x ∂μ ≠ ∞ := by
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hpos.1 hap
  have := isMarkovKernel_pow P m
  have hposm : IsPositive (P ^ m : Kernel X X) ψ :=
    (theorem_10_4_5_positive hpos.1 hap).1.1 hpos m hm
  obtain ⟨G, hG, hle, hint⟩ := exists_tsum_tvNorm_le_split hposm M hψC hνC
  refine ⟨fun x => m + m * G x, measurable_const.add (measurable_const.mul hG),
    fun x y => ?_, fun μ hμp hμ => ?_⟩
  · calc _ ≤ m * (2 + ∑' k, ENNReal.ofReal (tvNorm (((P ^ m) ^ (k + 1) : Kernel X X) x)
          (((P ^ m) ^ (k + 1) : Kernel X X) y))) := tsum_ofReal_tvNorm_le_skeleton P hm x y
      _ ≤ m * (2 + (G x + G y)) := mul_le_mul' le_rfl (add_le_add le_rfl (hle x y))
      _ = (m + m * G x) + (m + m * G y) := by ring
  · rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ hG]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top m, ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top m) (hint μ hμp (IsRegularMeasure.pow hpos hap hm μ hμ))⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.4.4** (MT p. 333), (13.81): for a positive aperiodic chain and regular initial
distributions `λ`, `μ`, `∫ λ(dx) ∫ μ(dy) Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞`. -/
theorem theorem_13_4_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsRegularMeasure P ψ μ) (hν : IsRegularMeasure P ψ ν) :
    ∫⁻ x, ∫⁻ y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y)) ∂ν ∂μ ≠ ∞ := by
  obtain ⟨G, -, hle, hint⟩ := exists_tsum_tvNorm_le hpos hap
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hint μ inferInstance hμ,
    hint ν inferInstance hν⟩) (lintegral_lintegral_le_of_le_add hle μ ν)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.4.4** from regular states: if `δ_x` and `δ_y` are regular, then
`Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞`. -/
theorem theorem_13_4_4_states {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {x y : X}
    (hx : IsRegularMeasure P ψ (Measure.dirac x)) (hy : IsRegularMeasure P ψ (Measure.dirac y)) :
    Summable fun n => tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y) := by
  obtain ⟨G, hG, hle, hint⟩ := exists_tsum_tvNorm_le hpos hap
  have hGx := hint _ inferInstance hx
  have hGy := hint _ inferInstance hy
  rw [lintegral_dirac' _ hG] at hGx hGy
  have hfin := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hGx, hGy⟩) (hle x y)
  exact (ENNReal.summable_toReal hfin).congr fun n => ENNReal.toReal_ofReal (tvNorm_nonneg _ _)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.4.4** for a regular chain (the analogue of (13.76) without an atom): for every
`x`, `y`, `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞`. -/
theorem theorem_13_4_4_regular {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) (hreg : IsRegularChain P ψ) (x y : X) :
    Summable fun n => tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y) :=
  theorem_13_4_4_states hpos hap (hreg.isRegularMeasure_dirac x) (hreg.isRegularMeasure_dirac y)

end MeynTweedie.GeneralizedDrift
