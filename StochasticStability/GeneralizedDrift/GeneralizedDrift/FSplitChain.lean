/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.FSkeletons

/-!
# `f`-properties through the split chain (MT §14.2.3, §14.3.1)

Meyn and Tweedie, pp. 348–351. `M : Minorization P` is a minorization `P(x, ·) ≥ δν` on a set
`C ∈ B⁺(X)` with `ν(C) > 0` (strong aperiodicity with the small set in `B⁺(X)`),
`P̌ = M.splitKernel` the split kernel on `X̌ = X × {0, 1}`, `α̌ = C₁` its atom, and
`f̌(x, i) = f(x)`. The state space is countably generated, `P` is positive with invariant
probability `π`, and `π(f) < ∞`.

**The split chain.**
* `Minorization.fSumReturn_split`: `Ě_{λ*}[Σ_{k<τ_{B̌}} f̌(Φ̌_k)] = E_λ[Σ_{k<τ_B} f(Φ_k)]` for
  `B̌ = B × {0, 1}` (the identity (5.9) along paths).
* `Minorization.lintegral_split_comp_fst`: `π*(f̌) = π(f)`; `exists_mem_ne_top_of_lintegral`:
  `f` is finite at some point of `C`; `Minorization.split_positive`: `P̌` is positive with the
  accessible atom `α̌` and invariant probability `π*`.
* `tabooPotFn_eq_of_kernel_eq`: `U_A(z, f)` depends only on `P(z, ·)`; on the bottom level `X₁`
  all points have `P̌(z, ·) = ν*`.

**Results.**
* `Minorization.exists_fRegular_cover`: the strongly aperiodic case of **Theorem 14.2.11**: there
  are `f`-regular sets `S(n)` whose union is full (the book's split chain argument, via
  Proposition 14.1.2 for `P̌`).
* `Minorization.exists_tabooPotFn_le`: there is `R ∈ B⁺(X)` with
  `Ǔ_{α̌}(z, f̌) ≤ Ě_z[Σ_{k<τ_{Ř}} f̌(Φ̌_k)] + K` for every `z`.
* `Minorization.tendsto_fNorm`: **Proposition 14.3.1 (ii)**, the convergence: for every
  probability `λ` with `E_λ[Σ_{k<τ_R} f(Φ_k)] < ∞` (in particular every `f`-regular `λ`),
  `‖λPⁿ − π‖_f → 0`; it holds for positive chains, Harris or not.
* `Minorization.tsum_fNorm_le`: the strongly aperiodic case of **Theorem 14.3.4**, pointwise:
  `Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖_f ≤ A (E_x[Σ_{k<τ_R} f] + E_y[Σ_{k<τ_R} f]) + B`.

**Hypotheses.** The minorization lives on a set in `B⁺(X)` with `ν(C) > 0`, the form in which
Theorem 13.3.1 is proved in Chapter 13 (`theorem_13_3_1_ii`): the atom `α̌` must be accessible and
have an aperiodic return-time law. `f ≥ 1` is used to bound `Ě[τ_{α̌}]` by `Ǔ_{α̌}(·, f̌)`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Sums along the split chain -/

/-- **Sums before hitting `B × {0, 1}` by the split chain**: for a probability `λ`,
`Ě_{λ*}[Σ_{k<τ_{B̌}} f(Φ̌_k.1)] = E_λ[Σ_{k<τ_B} f(Φ_k)]`. -/
theorem Minorization.fSumReturn_split {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    {B : Set X} (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ z, fSumReturn M.splitKernel (Prod.fst ⁻¹' B) (fun z => f z.1) z ∂M.split μ =
      ∫⁻ x, fSumReturn P B f x ∂μ := by
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_pathKernel M.splitKernel
  have := isMarkovKernel_pathKernel P
  have hπ : Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  calc ∫⁻ z, fSumReturn M.splitKernel (Prod.fst ⁻¹' B) (fun z => f z.1) z ∂M.split μ
      = ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => f (ω k)) (fun n => (ω n).1)
          ∂pathMeasure M.splitKernel (M.split μ) := by
        rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
          (f := fun ω : ℕ → X × Bool => sumBefore (firstReturn B) (fun k ω => f (ω k))
            (fun n => (ω n).1)) ((measurable_sumBefore_firstReturn hB hf).comp hπ).aemeasurable]
        rfl
    _ = ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => f (ω k)) ω ∂pathMeasure P μ :=
        M.lintegral_split_fst μ (measurable_sumBefore_firstReturn hB hf)
    _ = ∫⁻ x, fSumReturn P B f x ∂μ := by
        rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
          (measurable_sumBefore_firstReturn hB hf).aemeasurable]
        rfl

/-- The state form: `Ě_{x*}[Σ_{k<τ_{B̌}} f̌(Φ̌_k)] = E_x[Σ_{k<τ_B} f(Φ_k)]`. -/
theorem Minorization.fSumReturn_splitK {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    {B : Set X} (hB : MeasurableSet B) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ z, fSumReturn M.splitKernel (Prod.fst ⁻¹' B) (fun z => f z.1) z ∂M.splitK x =
      fSumReturn P B f x := by
  have h := M.fSumReturn_split hB hf (Measure.dirac x)
  rwa [show M.split (Measure.dirac x) = M.splitK x from Measure.dirac_bind M.splitK.measurable x,
    lintegral_dirac' _ (measurable_fSumReturn P hB hf)] at h

/-- `∫ f̌ d(λ*) = ∫ f dλ`. -/
theorem Minorization.lintegral_split_comp_fst {P : Kernel X X} (M : Minorization P)
    (μ : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z.1 ∂M.split μ = ∫⁻ x, f x ∂μ := by
  rw [M.lintegral_split μ (f := fun z : X × Bool => f z.1) (hf.comp measurable_fst)]
  refine lintegral_congr fun x => ?_
  rw [← add_mul, tsub_add_cancel_of_le (M.splitProb_le_one x), one_mul]

/-- `U_A(z, f)` depends only on `P(z, ·)`: `U_A(z, f) = ∫ P(z, dy) G_A(y, f)`. -/
theorem tabooPotFn_eq_of_kernel_eq {Y : Type*} [MeasurableSpace Y] {Q : Kernel Y Y}
    [IsMarkovKernel Q] {A : Set Y} (hA : MeasurableSet A) {f : Y → ℝ≥0∞} (hf : Measurable f)
    {z z' : Y} (h : Q z = Q z') : tabooPotFn Q A f z = tabooPotFn Q A f z' := by
  rw [← lintegral_gKernelFn Q hA hf z, ← lintegral_gKernelFn Q hA hf z', h]

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a positive chain with invariant probability `π`, `π(f) < ∞` and `ψ(C) > 0`, `f` is finite
at some point of `C`. -/
theorem exists_mem_ne_top_of_lintegral {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hπf : ∫⁻ y, f y ∂π ≠ ∞) {C : Set X} (hC : MeasurableSet C) (hψC : 0 < ψ C) :
    ∃ c ∈ C, f c ≠ ∞ := by
  by_contra hcon
  push Not at hcon
  have hrec := proposition_10_1_1 hpos
  have hequiv := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  have hπC : π C ≠ 0 := fun h0 => hψC.ne' (hequiv.2 h0)
  apply hπf
  refine top_le_iff.1 ?_
  calc ∞ = ∫⁻ _ in C, ∞ ∂π := by rw [setLIntegral_const, ENNReal.top_mul hπC]
    _ ≤ ∫⁻ y in C, f y ∂π := setLIntegral_mono' hC fun y hy => (hcon y hy).ge
    _ ≤ ∫⁻ y, f y ∂π := setLIntegral_le_lintegral _ _

/-- **The split chain of a positive chain** (MT p. 241, Proposition 10.4.1): `P̌` is positive for
`ψ*` with invariant probability `π*`, and `α̌ = C₁` is an accessible atom when `ψ(C) > 0`. -/
theorem Minorization.split_positive {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    haveI := M.isMarkovKernel_splitKernel
    IsPositive M.splitKernel (M.split ψ) ∧
      IsAccessibleAtom M.splitKernel (M.split ψ) M.checkAlpha ∧
      IsProbabilityMeasure (M.split π) ∧ IsInvariant M.splitKernel (M.split π) := by
  have := M.isMarkovKernel_splitKernel
  have hψs := M.isMaximalIrreducibility_split hpos.1
  have hαpos : 0 < M.split ψ M.checkAlpha := by
    rw [Minorization.checkAlpha, M.split_apply_true ψ M.measurableSet_C, inter_self]
    exact ENNReal.mul_pos M.δ_pos.ne' hψC.ne'
  have hπs := M.isProbabilityMeasure_split π
  have hinv := (proposition_10_4_1_ii M).2 hπ
  exact ⟨⟨hψs, M.split π, hπs, hinv⟩, ⟨M.isAtom_checkAlpha, hψs, hαpos⟩, hπs, hinv⟩

/-! ### The bound through a set `R ∈ B⁺(X)` -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The split atom is reached with finite `f`-cost from a set in `B⁺(X)`** (the step of the proof
of Theorem 14.3.4 that the book takes from Theorem 14.2.3): there are `R ∈ B⁺(X)` and `K < ∞`
with `Ǔ_{α̌}(z, f̌) ≤ Ě_z[Σ_{k<τ_{R × {0,1}}} f̌(Φ̌_k)] + K` for every `z ∈ X̌`. -/
theorem Minorization.exists_tabooPotFn_le {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    haveI := M.isMarkovKernel_splitKernel
    ∃ R : Set X, MeasurableSet R ∧ 0 < ψ R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ z,
      tabooPotFn M.splitKernel M.checkAlpha (fun z => f z.1) z ≤
        fSumReturn M.splitKernel (Prod.fst ⁻¹' R) (fun z => f z.1) z + K := by
  have := M.isMarkovKernel_splitKernel
  obtain ⟨hposs, hatom, hπs, hinv⟩ := M.split_positive hpos hψC hπ
  have hfs : Measurable fun z : X × Bool => f z.1 := hf.comp measurable_fst
  have hπfs : ∫⁻ z, f z.1 ∂M.split π ≠ ∞ := by rw [M.lintegral_split_comp_fst π hf]; exact hπf
  obtain ⟨c, hc, hfc⟩ := exists_mem_ne_top_of_lintegral hpos hπ hπf M.measurableSet_C hψC
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  obtain ⟨-, hUa, -, -⟩ := atom_driftV3 hposs hatom ha hinv hfs hπfs
  set U := tabooPotFn M.splitKernel M.checkAlpha (fun z => f z.1) with hU
  set G := gKernelFn M.splitKernel M.checkAlpha (fun z => f z.1) with hG
  obtain ⟨-, -, -, hfull, -⟩ := proposition_14_1_2_ii hposs hatom hinv hfs ⟨(c, true), ha, hfc⟩
    hπfs
  have hGm : Measurable G := measurable_gKernelFn M.measurableSet_checkAlpha hfs
  have hG0m : Measurable fun x : X => G (x, false) :=
    hGm.comp (measurable_id.prodMk measurable_const)
  -- `G(·, 0)` is finite `ψ`-a.e.
  set A := {x | G (x, false) = ∞} with hAdef
  have hAm : MeasurableSet A := hG0m (measurableSet_singleton ∞)
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
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < ψ {x | G (x, false) ≤ n} := by
    by_contra hcon
    push Not at hcon
    apply hpos.1.1
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc ψ univ ≤ ψ (⋃ n : ℕ, {x | G (x, false) ≤ n}) + ψ A := by
          refine (measure_mono fun x _ => ?_).trans (measure_union_le _ _)
          by_cases hx : G (x, false) = ∞
          · exact Or.inr hx
          · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
            exact Or.inl (mem_iUnion.2 ⟨n, hn.le⟩)
      _ = 0 := by
          rw [hA0, add_zero]
          exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hcon n)
  set R := {x | G (x, false) ≤ n} with hRdef
  have hRm : MeasurableSet R := measurableSet_le hG0m measurable_const
  -- on the bottom level `U` is the atom value
  have hUbot : ∀ x, U (x, true) = U (c, true) := fun x =>
    tabooPotFn_eq_of_kernel_eq M.measurableSet_checkAlpha hfs
      (by rw [M.splitKernel_apply_true, M.splitKernel_apply_true])
  have hGle : ∀ z ∈ (Prod.fst ⁻¹' R : Set (X × Bool)), G z ≤ n + U (c, true) := by
    rintro ⟨x, i⟩ hx
    have hx' : G (x, false) ≤ n := hx
    cases i
    · exact hx'.trans le_self_add
    · have hfx : f x ≤ n := (le_of_le_of_eq le_self_add
        (gKernelFn_eq M.splitKernel M.measurableSet_checkAlpha hfs (x, false)).symm).trans hx'
      rw [hG, gKernelFn_eq M.splitKernel M.measurableSet_checkAlpha hfs (x, true)]
      exact add_le_add hfx ((indicator_le_self _ _ _).trans (hUbot x).le)
  refine ⟨R, hRm, hn, n + U (c, true) + U (c, true), ENNReal.add_ne_top.2
    ⟨ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, hUa⟩, hUa⟩, fun z => ?_⟩
  calc U z ≤ G z + U (c, true) := hatom.1.tabooPotFn_le_gKernelFn ha hfs z
    _ ≤ fSumReturn M.splitKernel (Prod.fst ⁻¹' R) (fun z => f z.1) z + (n + U (c, true)) +
          U (c, true) :=
        add_le_add (gKernelFn_le_fSumReturn_add M.measurableSet_checkAlpha (measurable_fst hRm)
          hfs hGle z) le_rfl
    _ = _ := by ring

/-! ### Convergence and summability -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 14.3.1 (ii)**, the convergence (MT p. 349): for a positive chain with a
minorization on `C ∈ B⁺(X)`, `ν(C) > 0`, and `π(f) < ∞`, `f ≥ 1`, there is `R ∈ B⁺(X)` such that
`‖λPⁿ − π‖_f → 0` for every probability `λ` with `E_λ[Σ_{k<τ_R} f(Φ_k)] < ∞` (in particular for
every `f`-regular `λ`). -/
theorem Minorization.tendsto_fNorm {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    ∃ R : Set X, MeasurableSet R ∧ 0 < ψ R ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ],
      ∫⁻ x, fSumReturn P R f x ∂μ ≠ ∞ →
        Tendsto (fun n => fNorm f ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  have := M.isMarkovKernel_splitKernel
  obtain ⟨hposs, hatom, hπs, hinv⟩ := M.split_positive hpos hψC hπ
  have hfs : Measurable fun z : X × Bool => f z.1 := hf.comp measurable_fst
  have hπfs : ∫⁻ z, f z.1 ∂M.split π ≠ ∞ := by rw [M.lintegral_split_comp_fst π hf]; exact hπf
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  obtain ⟨hrep, -, -, -⟩ := atom_driftV3 hposs hatom ha hinv hfs hπfs
  have hEa := meanReturnTime_ne_top_of_rep M.splitKernel M.measurableSet_checkAlpha (c, true) hrep
  have hLa := hitProb_eq_one_of_meanReturnTime_ne_top M.measurableSet_checkAlpha hEa
  have herg := tendsto_atomRenewal_of_aperiodicLaw M.isAtom_checkAlpha ha hrep hLa
    (M.isAperiodicLaw_entryLaw_checkAlpha hνC)
  obtain ⟨R, hRm, hψR, K, hK, hbound⟩ := M.exists_tabooPotFn_le hpos hψC hπ hf hπf
  refine ⟨R, hRm, hψR, fun μ _ hμ => ?_⟩
  have := M.isProbabilityMeasure_split μ
  have hUm := measurable_tabooPotFn M.splitKernel M.measurableSet_checkAlpha hfs
  have hU : ∫⁻ z, tabooPotFn M.splitKernel M.checkAlpha (fun z => f z.1) z ∂M.split μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      M.fSumReturn_split hRm hf μ]
    exact ENNReal.add_ne_top.2 ⟨hμ, hK⟩
  have hE : ∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.split μ ≠ ∞ :=
    ne_top_of_le_ne_top hU (lintegral_mono fun z =>
      meanReturnTime_le_tabooPotFn _ _ (fun z => hf1 z.1) z)
  have hL := lintegral_hitProb_eq_one_of_lintegral_meanReturnTime M.splitKernel
    M.measurableSet_checkAlpha (M.split μ) hE
  have hlim := tendsto_fNorm_of_ergodic_atom M.isAtom_checkAlpha ha hrep herg hfs hπfs
    (M.split μ) hL hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => ?_
  have h1 := fNorm_map_le measurable_fst f
    ((M.splitKernel ^ n : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split μ) (M.split π)
  rwa [split_comp_pow_map_fst, M.split_map_fst] at h1

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.3.4, the strongly aperiodic case**, pointwise (MT p. 351): under the hypotheses
of `Minorization.tendsto_fNorm` there are `R ∈ B⁺(X)` and `A, B < ∞` with
`Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(y, ·)‖_f ≤ A (E_x[Σ_{k<τ_R} f] + E_y[Σ_{k<τ_R} f]) + B` for all `x`, `y`.
The bound (14.14)–(14.15) passes to the split chain, where Theorem 14.1.3 (iii) applies to the
atom `α̌`. -/
theorem Minorization.tsum_fNorm_le {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    ∃ R : Set X, MeasurableSet R ∧ 0 < ψ R ∧ ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧ ∀ x y,
      ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y) ≤
        A * (fSumReturn P R f x + fSumReturn P R f y) + B := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_splitK
  obtain ⟨hposs, hatom, hπs, hinv⟩ := M.split_positive hpos hψC hπ
  have hfs : Measurable fun z : X × Bool => f z.1 := hf.comp measurable_fst
  have hπfs : ∫⁻ z, f z.1 ∂M.split π ≠ ∞ := by rw [M.lintegral_split_comp_fst π hf]; exact hπf
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  obtain ⟨hrep, hUa, -, -⟩ := atom_driftV3 hposs hatom ha hinv hfs hπfs
  have hEa := meanReturnTime_ne_top_of_rep M.splitKernel M.measurableSet_checkAlpha (c, true) hrep
  have hLa := hitProb_eq_one_of_meanReturnTime_ne_top M.measurableSet_checkAlpha hEa
  have hap := M.isAperiodicLaw_entryLaw_checkAlpha hνC (c := c)
  obtain ⟨R, hRm, hψR, K, hK, hbound⟩ := M.exists_tabooPotFn_le hpos hψC hπ hf hπf
  have hπα : M.split π M.checkAlpha ≠ 0 :=
    measure_atom_ne_zero_of_rep M.splitKernel M.measurableSet_checkAlpha (c, true) hrep
  set U := tabooPotFn M.splitKernel M.checkAlpha (fun z => f z.1) with hUdef
  set V := ENNReal.ofReal (renewalVar (entryLaw M.splitKernel M.measurableSet_checkAlpha
    (Measure.dirac (c, true)))) * U (c, true) with hVdef
  have hVne : V ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUa
  have hUm := measurable_tabooPotFn M.splitKernel M.measurableSet_checkAlpha hfs
  have hsd : ∀ x, M.split (Measure.dirac x) = M.splitK x := fun x =>
    Measure.dirac_bind M.splitK.measurable x
  -- `P̌ⁿ⁺¹(α̌, f̌) < ∞`
  have hPa : ∀ n, ∫⁻ z, f z.1 ∂(M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool))
      (c, true) ≠ ∞ := fun n => by
    have h1 := hatom.1.mul_lintegral_pow_le ha hinv hfs n
    intro htop
    rw [htop, ENNReal.mul_top hπα] at h1
    exact hπfs (top_le_iff.1 h1)
  -- the split bound from `x*`
  set H : X → ℝ≥0∞ := fun x => ∑' n, fNorm (fun z : X × Bool => f z.1)
    ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ M.splitK x)
    ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true)) with hH
  have hHle : ∀ x, H x ≤ (1 + V) * (fSumReturn P R f x + K) := fun x => by
    have hUx : ∫⁻ z, U z ∂M.splitK x ≤ fSumReturn P R f x + K := by
      calc ∫⁻ z, U z ∂M.splitK x ≤ ∫⁻ z, (fSumReturn M.splitKernel (Prod.fst ⁻¹' R)
            (fun z => f z.1) z + K) ∂M.splitK x := lintegral_mono hbound
        _ = fSumReturn P R f x + K := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              M.fSumReturn_splitK hRm hf x]
    by_cases hx : ∫⁻ z, U z ∂M.splitK x = ∞
    · have : fSumReturn P R f x + K = ∞ := top_le_iff.1 (hx ▸ hUx)
      rw [this, ENNReal.mul_top (by simp)]; exact le_top
    have hEx : ∫⁻ z, meanReturnTime M.splitKernel M.checkAlpha z ∂M.splitK x ≤
        ∫⁻ z, U z ∂M.splitK x :=
      lintegral_mono fun z => meanReturnTime_le_tabooPotFn _ _ (fun z => hf1 z.1) z
    have : IsProbabilityMeasure (M.split (Measure.dirac x)) := M.isProbabilityMeasure_split _
    have hb := tsum_fNorm_comp_le_atom M.isAtom_checkAlpha ha hLa hEa hap
      (M.split (Measure.dirac x)) (by rw [hsd x]; exact ne_top_of_le_ne_top hx hEx) hfs
    rw [hsd x] at hb
    calc H x ≤ ∫⁻ z, U z ∂M.splitK x + ENNReal.ofReal ((∫⁻ z, meanReturnTime M.splitKernel
          M.checkAlpha z ∂M.splitK x).toReal * renewalVar (entryLaw M.splitKernel
            M.measurableSet_checkAlpha (Measure.dirac (c, true)))) * U (c, true) := hb
      _ ≤ ∫⁻ z, U z ∂M.splitK x + (∫⁻ z, U z ∂M.splitK x) * V := by
          refine add_le_add le_rfl ?_
          rw [hVdef, ← mul_assoc]
          refine mul_le_mul' ?_ le_rfl
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (ne_top_of_le_ne_top hx hEx)]
          exact mul_le_mul' hEx le_rfl
      _ = (1 + V) * ∫⁻ z, U z ∂M.splitK x := by ring
      _ ≤ (1 + V) * (fSumReturn P R f x + K) := mul_le_mul' le_rfl hUx
  refine ⟨R, hRm, hψR, 1 + V, (1 + V) * (K + K), ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hVne⟩,
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hVne⟩)
      (ENNReal.add_ne_top.2 ⟨hK, hK⟩), fun x y => ?_⟩
  calc ∑' n, fNorm f ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
      ≤ ∑' n, (fNorm (fun z : X × Bool => f z.1)
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ M.splitK x)
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true)) +
        fNorm (fun z : X × Bool => f z.1)
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ M.splitK y)
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true))) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        have h1 : fNorm f (((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ
            M.split (Measure.dirac x)).map Prod.fst) (((M.splitKernel ^ (n + 1) :
              Kernel (X × Bool) (X × Bool)) ∘ₘ M.split (Measure.dirac y)).map Prod.fst) ≤
            fNorm (fun z : X × Bool => f z.1) ((M.splitKernel ^ (n + 1) :
              Kernel (X × Bool) (X × Bool)) ∘ₘ M.split (Measure.dirac x))
              ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ
                M.split (Measure.dirac y)) := fNorm_map_le measurable_fst f _ _
        rw [split_comp_pow_map_fst, split_comp_pow_map_fst, dirac_kernel, dirac_kernel, hsd x,
          hsd y] at h1
        refine h1.trans ((fNorm_triangle _ _ _ (hPa n)).trans
          (add_le_add le_rfl (le_of_eq (fNorm_comm _ _ _))))
    _ = H x + H y := ENNReal.tsum_add
    _ ≤ (1 + V) * (fSumReturn P R f x + K) + (1 + V) * (fSumReturn P R f y + K) :=
        add_le_add (hHle x) (hHle y)
    _ = (1 + V) * (fSumReturn P R f x + fSumReturn P R f y) + (1 + V) * (K + K) := by ring

/-! ### The `f`-regular cover from the split chain -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.2.11, the strongly aperiodic case** (MT p. 348): for a positive chain with a
minorization on `C ∈ B⁺(X)` and `π(f) < ∞`, there are `f`-regular sets `S(n)` whose union is
full. The sets are `S(n) = {x : Ě_{x*}[G_{α̌}(·, f̌)] ≤ n}`: Proposition 14.1.2 applies to the split
chain, and `E_x[Σ_{k<τ_B} f] = Ě_{x*}[Σ_{k<τ_{B̌}} f̌] ≤ Ě_{x*}[G_{α̌}] + c(B̌)`. -/
theorem Minorization.exists_fRegular_cover {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞) :
    ∃ S : ℕ → Set X, (∀ n, IsFRegularSet P ψ f (S n)) ∧ IsFull ψ (⋃ n, S n) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_splitK
  obtain ⟨hposs, hatom, hπs, hinv⟩ := M.split_positive hpos hψC hπ
  have hfs : Measurable fun z : X × Bool => f z.1 := hf.comp measurable_fst
  have hπfs : ∫⁻ z, f z.1 ∂M.split π ≠ ∞ := by rw [M.lintegral_split_comp_fst π hf]; exact hπf
  obtain ⟨c, hc, hfc⟩ := exists_mem_ne_top_of_lintegral hpos hπ hπf M.measurableSet_C hψC
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  obtain ⟨-, hUa, hdrift, hpet⟩ := atom_driftV3 hposs hatom ha hinv hfs hπfs
  obtain ⟨-, -, -, hfull, -⟩ := proposition_14_1_2_ii hposs hatom hinv hfs ⟨(c, true), ha, hfc⟩
    hπfs
  set G := gKernelFn M.splitKernel M.checkAlpha (fun z => f z.1) with hG
  have hGm : Measurable G := measurable_gKernelFn M.measurableSet_checkAlpha hfs
  set W : X → ℝ≥0∞ := fun x => ∫⁻ z, G z ∂M.splitK x with hW
  have hWm : Measurable W := hGm.lintegral_kernel
  refine ⟨fun n => {x | W x ≤ n}, fun n => ⟨measurableSet_le hWm measurable_const,
    fun B hB hψB => ?_⟩, ?_⟩
  · have hψsB : 0 < M.split ψ (Prod.fst ⁻¹' B) := by rw [M.split_fst_preimage ψ hB]; exact hψB
    obtain ⟨c', hc', hbound⟩ := theorem_14_2_3_i hposs.1 hGm hfs hUa hpet hdrift
      (measurable_fst hB) hψsB
    refine ⟨n + c', ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, hc'⟩, fun x hx => ?_⟩
    rw [← M.fSumReturn_splitK hB hf x]
    calc ∫⁻ z, fSumReturn M.splitKernel (Prod.fst ⁻¹' B) (fun z => f z.1) z ∂M.splitK x
        ≤ ∫⁻ z, (G z + c') ∂M.splitK x := lintegral_mono hbound
      _ = W x + c' := by rw [lintegral_add_right _ measurable_const, lintegral_const,
          measure_univ, mul_one]
      _ ≤ n + c' := add_le_add hx le_rfl
  · -- `{W = ∞} ⊆ {G(·, 0) = ∞} ∪ ({G(·, 1) = ∞} ∩ C)`, both `ψ`-null
    have hG0m : Measurable fun x : X => G (x, false) :=
      hGm.comp (measurable_id.prodMk measurable_const)
    have hG1m : Measurable fun x : X => G (x, true) :=
      hGm.comp (measurable_id.prodMk measurable_const)
    have hm0 : MeasurableSet {x | G (x, false) = ∞} := hG0m (measurableSet_singleton ∞)
    have hm1 : MeasurableSet {x | G (x, true) = ∞} := hG1m (measurableSet_singleton ∞)
    have hA0 : ψ {x | G (x, false) = ∞} = 0 := by
      have h1 := M.one_sub_mul_le_split_false ψ hm0
      have h2 : M.split ψ ({x | G (x, false) = ∞} ×ˢ {false}) = 0 := measure_mono_null
        (fun z hz => by
          obtain ⟨hz1, hz2⟩ := hz
          obtain ⟨x, b'⟩ := z
          simp only [mem_singleton_iff] at hz2
          subst hz2
          simp only [mem_compl_iff, mem_ofPred_eq, not_not]
          exact hz1) hfull
      rw [h2, nonpos_iff_eq_zero, mul_eq_zero] at h1
      exact h1.resolve_left M.one_sub_δ_ne_zero
    have hA1 : ψ ({x | G (x, true) = ∞} ∩ M.C) = 0 := by
      have h1 := M.split_apply_true ψ hm1
      have h2 : M.split ψ ({x | G (x, true) = ∞} ×ˢ {true}) = 0 := measure_mono_null
        (fun z hz => by
          obtain ⟨hz1, hz2⟩ := hz
          obtain ⟨x, b'⟩ := z
          simp only [mem_singleton_iff] at hz2
          subst hz2
          simp only [mem_compl_iff, mem_ofPred_eq, not_not]
          exact hz1) hfull
      rw [h2] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left M.δ_pos.ne'
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hA0 hA1)
    simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hx
    have hWx : W x = ∞ := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
      exact absurd (hx n) (not_lt.2 hn.le)
    have hWx' : ∫⁻ z, G z ∂M.splitK x = ∞ := hWx
    rw [M.lintegral_splitK x hGm] at hWx'
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, mem_inter_iff, not_or, not_and] at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hr : (1 - M.splitProb x) * G (x, false) ≠ ∞ :=
      ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) h0
    have hr1 : M.splitProb x * G (x, true) ≠ ∞ := by
      by_cases hxC : x ∈ M.C
      · exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
          (M.splitProb_le_one x)) (fun h => h1 h hxC)
      · rw [M.splitProb_of_notMem hxC, zero_mul]; exact ENNReal.zero_ne_top
    exact (ENNReal.add_ne_top.2 ⟨hr, hr1⟩) hWx'

end MeynTweedie.GeneralizedDrift
