/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransienceRecurrence.Splitting

/-!
# Connecting the split and original chains (MT §5.1.2)

Meyn and Tweedie, §5.1.2, pp. 100–101. `M : Minorization P` is a minorization (5.2) and
`P̌ = M.splitKernel` the split kernel on `X̌ = X × Bool`.

* `lintegral_cylFn_split`: the finite-dimensional distributions of the first coordinate of the
  split chain started from `μ*` are those of the original chain started from `μ`, for every
  measure `μ`; the proof is an induction on the length of the cylinder, using (5.10) and the
  fact that splitting commutes with restriction to sets `A × Bool`.
* **Theorem 5.1.3 (i)**, path form (`theorem_5_1_3_i_path`, p. 100): the law of `(Φ̌ₙ.1)ₙ`
  under `P̌_{μ*}` is `P_μ`; `isMarkovChain_split_fst`: the first coordinate of the split chain is
  a Markov chain with kernel `P` and initial law `μ`; `lintegral_split_fst`: hence
  `E_μ[F(Φ)] = Ě_{μ*}[F(Φ̌.1)]` for every measurable `F ≥ 0` on path space, and in particular
  `E_λ[f(Φ_k)] = Ě_{λ*}[f(Φ̌_k)]` (`lintegral_split_coord`, p. 101).
* **Theorem 5.1.3 (ii)** (`theorem_5_1_3_ii`, p. 100): if `Φ̌` is `φ*`-irreducible then `Φ` is
  `φ`-irreducible (`isPhiIrreducible_of_split`); if `Φ` is `φ`-irreducible with `φ(C) > 0` then
  `Φ̌` is `ν*`-irreducible, every state reaches `α̌ = C₁`, and `α̌` is an accessible atom.
* `isPhiIrreducible_split` and `isPhiIrreducible_split_iff`: `Φ` is `φ`-irreducible iff `Φ̌` is
  `φ*`-irreducible, with no condition on `φ(C)`; `isMaximalIrreducibility_split`: if `ψ` is a
  maximal irreducibility measure for `Φ` then `ψ*` is one for `Φ̌`.

**Corrections.** None. Theorem 5.1.3 (ii) is stated by the book for the sets `C₁ ⊆ X₁`; the first
half holds for every minorization, the second needs `φ(C) > 0` as stated.
-/

namespace MeynTweedie.TransienceRecurrence

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace Minorization

variable {P : Kernel X X}

/-! ### The finite-dimensional distributions of the marginal chain -/

/-- The cylinder functions of the split chain on the sets `Aᵢ × Bool` integrate against `μ*` to
the cylinder functions of the original chain against `μ`. -/
theorem lintegral_cylFn_split (M : Minorization P) (n : ℕ) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (μ : Measure X) :
    ∫⁻ z, cylFn M.splitKernel n (fun i => Prod.fst ⁻¹' A i) z ∂M.split μ =
      ∫⁻ x, cylFn P n A x ∂μ := by
  induction n generalizing A μ with
  | zero =>
    simp only [cylFn]
    rw [lintegral_indicator_one (measurable_fst (hA 0)), lintegral_indicator_one (hA 0),
      M.split_fst_preimage μ (hA 0)]
  | succ n ih =>
    simp only [cylFn]
    have hA' : ∀ i, MeasurableSet (A (i + 1)) := fun i => hA (i + 1)
    have hg := measurable_cylFn M.splitKernel n (A := fun i => Prod.fst ⁻¹' A (i + 1))
      fun i => measurable_fst (hA (i + 1))
    rw [lintegral_indicator (measurable_fst (hA 0)), lintegral_indicator (hA 0),
      M.split_restrict_fst μ (hA 0),
      ← Measure.lintegral_bind M.splitKernel.aemeasurable hg.aemeasurable]
    change ∫⁻ w, _ ∂(M.splitKernel ∘ₘ M.split (μ.restrict (A 0))) = _
    rw [split_comp_splitKernel, ih hA',
      Measure.lintegral_bind P.aemeasurable (measurable_cylFn P n hA').aemeasurable]

/-- **Theorem 5.1.3 (i)**, path form (MT p. 100): `Φ` is the marginal chain of `Φ̌`. The law of
the first coordinates `(Φ̌ₙ.1)ₙ` of the split chain started from `μ*` is the law `P_μ` of the
original chain. -/
theorem theorem_5_1_3_i_path (M : Minorization P) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := M.isMarkovKernel_splitKernel
    (pathMeasure M.splitKernel (M.split μ)).map (fun ω n => (ω n).1) = pathMeasure P μ := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_split μ
  have := isProbabilityMeasure_pathMeasure M.splitKernel (M.split μ)
  have hπ : Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  have : IsProbabilityMeasure ((pathMeasure M.splitKernel (M.split μ)).map
      fun ω n => (ω n).1) := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  refine theorem_3_4_1_unique P μ _ fun n A hA => ?_
  rw [Measure.map_apply hπ (measurableSet_boxSet n hA)]
  have hpre : (fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1) ⁻¹' boxSet n A =
      boxSet n (fun i => Prod.fst ⁻¹' A i) := by
    ext ω; simp [boxSet]
  rw [hpre, pathMeasure_boxSet _ _ n fun i => measurable_fst (hA i),
    M.lintegral_cylFn_split n hA μ]

/-- The first coordinate of the split chain is a Markov chain with transition kernel `P` and
initial distribution `μ` (MT p. 96, (i)). -/
theorem isMarkovChain_split_fst (M : Minorization P) [IsMarkovKernel P] (μ : Measure X) :
    haveI := M.isMarkovKernel_splitKernel
    IsMarkovChain P μ (pathMeasure M.splitKernel (M.split μ)) (fun n ω => (ω n).1) := by
  have := M.isMarkovKernel_splitKernel
  refine ⟨fun n => measurable_fst.comp (measurable_pi_apply n), fun n A hA => ?_⟩
  have hpre : {ω : ℕ → X × Bool | ∀ i ≤ n, (ω i).1 ∈ A i} =
      boxSet n (fun i => Prod.fst ⁻¹' A i) := by
    ext ω; simp [boxSet]
  rw [hpre, pathMeasure_boxSet _ _ n fun i => measurable_fst (hA i),
    M.lintegral_cylFn_split n hA μ]

/-- `E_μ[F(Φ)] = Ě_{μ*}[F(Φ̌.1)]` for every measurable `F ≥ 0` on path space. -/
theorem lintegral_split_fst (M : Minorization P) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : (ℕ → X) → ℝ≥0∞} (hF : Measurable F) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ ω, F (fun n => (ω n).1) ∂pathMeasure M.splitKernel (M.split μ) =
      ∫⁻ ω, F ω ∂pathMeasure P μ := by
  have := M.isMarkovKernel_splitKernel
  have hπ : Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  rw [← M.theorem_5_1_3_i_path μ, lintegral_map hF hπ]

/-- MT p. 101: `E_λ[f(Φ_k)] = Ě_{λ*}[f(Φ̌_k)]` for `f` identical on the two copies of `X`. -/
theorem lintegral_split_coord (M : Minorization P) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (k : ℕ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ ω, f (ω k).1 ∂pathMeasure M.splitKernel (M.split μ) = ∫⁻ ω, f (ω k) ∂pathMeasure P μ :=
  M.lintegral_split_fst μ (F := fun ω => f (ω k)) (hf.comp (measurable_pi_apply k))

/-! ### Irreducibility of the split chain -/

/-- `μ*(A₀) ≥ (1 − δ) μ(A)`. -/
theorem one_sub_mul_le_split_false (M : Minorization P) (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : (1 - M.δ) * μ A ≤ M.split μ (A ×ˢ {false}) := by
  rw [M.split_apply_false μ hA, ← measure_inter_add_sdiff A M.measurableSet_C, mul_add,
    sdiff_eq]
  gcongr
  exact mul_le_of_le_one_left' tsub_le_self

omit [MeasurableSpace X] in
/-- A set `s ⊆ X̌` is covered by `s₀ × {0} ∪ s₁ × {1}`, its two sections. -/
theorem subset_sections (s : Set (X × Bool)) :
    s ⊆ ((fun x => (x, false)) ⁻¹' s) ×ˢ {false} ∪ ((fun x => (x, true)) ⁻¹' s) ×ˢ {true} := by
  rintro ⟨x, b⟩ h
  cases b
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- If `μ*(s) > 0` then `μ(s₀) > 0` or `μ(s₁ ∩ C) > 0`. -/
theorem split_pos_cases (M : Minorization P) (μ : Measure X) {s : Set (X × Bool)}
    (hs : MeasurableSet s) (h : 0 < M.split μ s) :
    0 < μ ((fun x => (x, false)) ⁻¹' s) ∨ 0 < μ ((fun x => (x, true)) ⁻¹' s ∩ M.C) := by
  have h0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have h1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  by_contra hc
  push Not at hc
  have hle : M.split μ s ≤ 0 := by
    calc M.split μ s ≤ M.split μ (((fun x => (x, false)) ⁻¹' s) ×ˢ {false} ∪
          ((fun x => (x, true)) ⁻¹' s) ×ˢ {true}) := measure_mono (subset_sections s)
      _ ≤ M.split μ (((fun x => (x, false)) ⁻¹' s) ×ˢ {false}) +
          M.split μ (((fun x => (x, true)) ⁻¹' s) ×ˢ {true}) := measure_union_le _ _
      _ = 0 := by
        rw [M.split_apply_false μ h0, M.split_apply_true μ h1,
          measure_mono_null inter_subset_left (nonpos_iff_eq_zero.1 hc.1),
          measure_mono_null inter_subset_left (nonpos_iff_eq_zero.1 hc.1),
          nonpos_iff_eq_zero.1 hc.2]
        simp
  exact absurd h (not_lt.2 hle)

/-- **Theorem 5.1.3 (ii)**, first part (MT p. 100): if the split chain is `φ*`-irreducible, the
original chain is `φ`-irreducible. -/
theorem isPhiIrreducible_of_split (M : Minorization P) [IsMarkovKernel P] {φ : Measure X}
    (h : haveI := M.isMarkovKernel_splitKernel; IsPhiIrreducible M.splitKernel (M.split φ)) :
    IsPhiIrreducible P φ := by
  have := M.isMarkovKernel_splitKernel
  intro A hA hpos x
  have hA' : MeasurableSet (Prod.fst ⁻¹' A : Set (X × Bool)) := measurable_fst hA
  have h1 := h _ hA' (by rwa [M.split_fst_preimage φ hA]) (x, false)
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA' _).1 h1
  refine (hitProb_pos_iff P hA x).2 ⟨n, ?_⟩
  have h2 := M.theorem_5_1_3_i (n + 1) (Measure.dirac x) hA
  rw [lintegral_dirac' _ (Kernel.measurable_coe _ hA),
    M.lintegral_split _ (Kernel.measurable_coe _ hA'), lintegral_dirac'] at h2
  · rw [h2]
    refine lt_of_lt_of_le ?_ le_self_add
    refine ENNReal.mul_pos ?_ hn.ne'
    exact (tsub_pos_of_lt ((M.splitProb_le x).trans_lt M.δ_lt_one)).ne'
  · exact ((measurable_const.sub M.measurable_splitProb).mul
      ((Kernel.measurable_coe _ hA').comp (measurable_id.prodMk measurable_const))).add
      (M.measurable_splitProb.mul
        ((Kernel.measurable_coe _ hA').comp (measurable_id.prodMk measurable_const)))

/-- If the original chain is `φ`-irreducible, the split chain is `φ*`-irreducible. -/
theorem isPhiIrreducible_split (M : Minorization P) [IsMarkovKernel P] {φ : Measure X}
    (h : IsPhiIrreducible P φ) :
    haveI := M.isMarkovKernel_splitKernel; IsPhiIrreducible M.splitKernel (M.split φ) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_baseK
  intro s hs hpos z
  have hQ : M.baseK z ≠ 0 := IsProbabilityMeasure.ne_zero _
  have h0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have h1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  rw [hitProb_pos_iff _ hs]
  rcases M.split_pos_cases φ hs hpos with hc | hc
  · obtain ⟨m, hm⟩ := exists_pow_comp_pos h hQ h0 hc
    refine ⟨m + 1, ?_⟩
    rw [M.splitKernel_pow_succ_apply]
    refine lt_of_lt_of_le ?_ (measure_mono (show ((fun x => (x, false)) ⁻¹' s) ×ˢ
      ({false} : Set Bool) ⊆ s from prod_subset_iff.2 fun x hx b hb => by
        rw [mem_singleton_iff.1 hb]; exact hx))
    exact (ENNReal.mul_pos M.one_sub_δ_ne_zero hm.ne').trans_le
      (M.one_sub_mul_le_split_false _ h0)
  · obtain ⟨m, hm⟩ := exists_pow_comp_pos h hQ (h1.inter M.measurableSet_C) hc
    refine ⟨m + 1, ?_⟩
    rw [M.splitKernel_pow_succ_apply]
    refine lt_of_lt_of_le ?_ (measure_mono (show ((fun x => (x, true)) ⁻¹' s) ×ˢ
      ({true} : Set Bool) ⊆ s from prod_subset_iff.2 fun x hx b hb => by
        rw [mem_singleton_iff.1 hb]; exact hx))
    rw [M.split_apply_true _ h1]
    exact ENNReal.mul_pos M.δ_pos.ne' hm.ne'

/-- `Φ` is `φ`-irreducible iff `Φ̌` is `φ*`-irreducible. -/
theorem isPhiIrreducible_split_iff (M : Minorization P) [IsMarkovKernel P] (φ : Measure X) :
    IsPhiIrreducible P φ ↔
      haveI := M.isMarkovKernel_splitKernel; IsPhiIrreducible M.splitKernel (M.split φ) :=
  ⟨M.isPhiIrreducible_split, M.isPhiIrreducible_of_split⟩

/-- **Theorem 5.1.3 (ii)** (MT p. 100). (a) If `Φ̌` is `φ*`-irreducible then `Φ` is
`φ`-irreducible. (b) If `Φ` is `φ`-irreducible with `φ(C) > 0`, then `Φ̌` is `ν*`-irreducible,
every state of `X̌` reaches `α̌ = C₁`, and `α̌` is an accessible atom of `Φ̌` for every maximal
irreducibility measure of `Φ̌`. -/
theorem theorem_5_1_3_ii (M : Minorization P) [IsMarkovKernel P] (φ : Measure X) :
    haveI := M.isMarkovKernel_splitKernel
    (IsPhiIrreducible M.splitKernel (M.split φ) → IsPhiIrreducible P φ) ∧
      (IsPhiIrreducible P φ → 0 < φ M.C →
        IsPhiIrreducible M.splitKernel (M.split M.ν) ∧
        (∀ z, 0 < hitProb M.splitKernel M.checkAlpha z) ∧
        ∀ ψ : Measure (X × Bool), IsMaximalIrreducibility M.splitKernel ψ →
          IsAccessibleAtom M.splitKernel ψ M.checkAlpha) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_baseK
  refine ⟨M.isPhiIrreducible_of_split, fun h hC => ?_⟩
  have hreach : ∀ z, ∃ n, 0 < (M.splitKernel ^ n) z M.checkAlpha := fun z => by
    obtain ⟨m, hm⟩ := exists_pow_comp_pos h (IsProbabilityMeasure.ne_zero (M.baseK z))
      M.measurableSet_C hC
    refine ⟨m + 1 + 1, ?_⟩
    rw [M.splitKernel_pow_succ_apply, checkAlpha, M.split_apply_true _ M.measurableSet_C,
      inter_self]
    exact ENNReal.mul_pos M.δ_pos.ne' hm.ne'
  have hν : ∀ y ∈ M.checkAlpha, M.splitKernel y = M.split M.ν := fun y hy => by
    obtain ⟨x, b⟩ := y
    simp only [checkAlpha, mem_prod, mem_singleton_iff] at hy
    rw [hy.2, splitKernel_apply_true]
  exact proposition_5_1_1 M.splitKernel M.measurableSet_checkAlpha hν hreach

/-- If `ψ` is a maximal irreducibility measure for `Φ`, then `ψ*` is a maximal irreducibility
measure for the split chain. -/
theorem isMaximalIrreducibility_split (M : Minorization P) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    haveI := M.isMarkovKernel_splitKernel; IsMaximalIrreducibility M.splitKernel (M.split ψ) := by
  have := M.isMarkovKernel_splitKernel
  refine ⟨fun h0 => hψ.1 ?_, M.isPhiIrreducible_split hψ.2.1, fun φc hφc => ?_⟩
  · rw [← Measure.measure_univ_eq_zero, ← M.split_univ, h0]
    rfl
  -- the marginal of `φc` is an irreducibility measure for `Φ`
  have hmarg : IsPhiIrreducible P (φc.map Prod.fst) := by
    intro A hA hpos x
    have hA' : MeasurableSet (Prod.fst ⁻¹' A : Set (X × Bool)) := measurable_fst hA
    rw [Measure.map_apply measurable_fst hA] at hpos
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA' _).1 (hφc _ hA' hpos (x, false))
    refine (hitProb_pos_iff P hA x).2 ⟨n, ?_⟩
    have h2 := M.theorem_5_1_3_i (n + 1) (Measure.dirac x) hA
    have hm : Measurable fun z : X × Bool => (M.splitKernel ^ (n + 1)) z (Prod.fst ⁻¹' A) :=
      Kernel.measurable_coe _ hA'
    rw [lintegral_dirac' _ (Kernel.measurable_coe _ hA), M.lintegral_split _ hm,
      lintegral_dirac'] at h2
    · rw [h2]
      refine lt_of_lt_of_le ?_ le_self_add
      exact ENNReal.mul_pos (tsub_pos_of_lt ((M.splitProb_le x).trans_lt M.δ_lt_one)).ne' hn.ne'
    · exact ((measurable_const.sub M.measurable_splitProb).mul
        (hm.comp (measurable_id.prodMk measurable_const))).add
        (M.measurable_splitProb.mul (hm.comp (measurable_id.prodMk measurable_const)))
  have hac := hψ.2.2 _ hmarg
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  have hs0 : MeasurableSet ((fun x => (x, false)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  have hs1 : MeasurableSet ((fun x => (x, true)) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  -- `ψ` does not charge the two sections
  have hψ0 : ψ ((fun x => (x, false)) ⁻¹' s) = 0 := by
    have := (M.one_sub_mul_le_split_false ψ hs0).trans
      (measure_mono (μ := M.split ψ) (show ((fun x => (x, false)) ⁻¹' s) ×ˢ
        ({false} : Set Bool) ⊆ s from prod_subset_iff.2 fun x hx b hb => by
          rw [mem_singleton_iff.1 hb]; exact hx))
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left M.one_sub_δ_ne_zero
  have hψ1 : ψ ((fun x => (x, true)) ⁻¹' s ∩ M.C) = 0 := by
    have := measure_mono (μ := M.split ψ) (show ((fun x => (x, true)) ⁻¹' s) ×ˢ {true} ⊆ s from
      prod_subset_iff.2 fun x hx b hb => by rw [mem_singleton_iff.1 hb]; exact hx)
    rw [h0, M.split_apply_true ψ hs1, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left M.δ_pos.ne'
  -- the bottom level outside `C` is never reached
  have hbot : φc (M.Cᶜ ×ˢ {true}) = 0 := by
    by_contra hne
    have hm : MeasurableSet (M.Cᶜ ×ˢ ({true} : Set Bool)) :=
      M.measurableSet_C.compl.prod (measurableSet_singleton true)
    obtain ⟨z, -⟩ := nonempty_of_measure_ne_zero hne
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hm z).1 (hφc _ hm (pos_iff_ne_zero.2 hne) z)
    rw [M.splitKernel_pow_bottom_compl] at hn
    exact lt_irrefl _ hn
  refine measure_mono_null (subset_sections s) (measure_union_null ?_ ?_)
  · refine measure_mono_null (show ((fun x => (x, false)) ⁻¹' s) ×ˢ ({false} : Set Bool) ⊆
      Prod.fst ⁻¹' ((fun x => (x, false)) ⁻¹' s) from fun z hz => hz.1) ?_
    have := hac hψ0
    rwa [Measure.map_apply measurable_fst hs0] at this
  · have hsub : ((fun x => (x, true)) ⁻¹' s) ×ˢ ({true} : Set Bool) ⊆
        Prod.fst ⁻¹' ((fun x => (x, true)) ⁻¹' s ∩ M.C) ∪ M.Cᶜ ×ˢ {true} := by
      rintro ⟨x, b⟩ ⟨hx, hb⟩
      by_cases hc : x ∈ M.C
      · exact Or.inl ⟨hx, hc⟩
      · exact Or.inr ⟨hc, hb⟩
    refine measure_mono_null hsub (measure_union_null ?_ hbot)
    have := hac hψ1
    rwa [Measure.map_apply measurable_fst (hs1.inter M.measurableSet_C)] at this

end Minorization

end MeynTweedie.TransienceRecurrence
