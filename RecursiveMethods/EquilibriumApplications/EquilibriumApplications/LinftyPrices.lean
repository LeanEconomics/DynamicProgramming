/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.Economy

/-!
# Inner product prices on `L∞`: Lemma 15.7

SLP §15.4, pp. 467–468. `(Z, 𝒵, μ)` is a finite measure space (the book: a probability space) and
`S = L∞(Z, 𝒵, μ)` is Mathlib's `Lp ℝ ⊤ μ`.

* `linftyRestrict μ B`: `x ↦ x · 1_B`; `linftyTrunc μ A`: the **truncation over an event**
  `x^A = x · 1_{Z ∖ A}` (p. 468).
* **Lemma 15.7** (`lemma_15_7`, p. 468): every `φ ∈ L∞(μ)*` has a nested decreasing sequence
  `A_n ∈ 𝒵` with `μ(A_n) → 0` and a `ψ ∈ L∞(μ)*` with `ψ(x) = lim_n φ(x^{A_n})` for all `x` and
  `ψ(x) = ∫ p x dμ` for some `p ∈ L¹(μ)`. In addition `‖ψ‖ ≤ ‖φ‖` and `ψ(x^{A_n}) = φ(x^{A_n})`
  for all `n`, so the remainder `φ − ψ` lives on the sets `A_n` (it is the purely finitely
  additive part of `φ`).

The book omits the proof ("follows directly from Theorems 1.22 and 1.24 of Yosida and Hewitt").
The proof here is direct and avoids `L∞* = ba(μ)` and the Yosida–Hewitt decomposition:
1. `W(B) = ‖φ ∘ (· 1_B)‖` (`linftyRestrictNorm`), the variation of `φ` on `B`, is monotone and
   superadditive on disjoint events (`linftyRestrictNorm_add_le`).
2. `s_m = inf {W(Z ∖ A) : μ(A) ≤ 2^{-m}}` increases to `s` (`linftyTailInf`, `linftyTailSup`);
   near-minimisers give nested `A_n` with `μ(A_n) ≤ 2^{-n}` and `s_n ≤ W(Z ∖ A_n) ≤ s + 2^{-n}`
   (`exists_isLinftyTailSeq`).
3. `|φ(x^{A_m}) − φ(x^{A_n})| ≤ ‖x‖ (W(Z ∖ A_m) − W(Z ∖ A_n))`, so `φ(x^{A_n})` is Cauchy and
   `ψ = lim φ(· ^{A_n})` is a continuous linear functional (`IsLinftyTailSeq.limitDual`).
4. If `μ(B) ≤ 2^{-(m+1)}` then `|ψ(x · 1_B)| ≤ ‖x‖ (s − s_m)`
   (`IsLinftyTailSeq.abs_linftyTruncLimit_restrict_le`), so `E ↦ ψ(1_E)` is a countably additive
   signed measure, absolutely continuous with respect to `μ`
   (`IsLinftyTailSeq.limitSignedMeasure`); Radon–Nikodym gives `p`.
5. `ψ` and `x ↦ ∫ p x dμ` agree on indicators, hence everywhere (`linfty_dual_eq_zero`).

**Note.** The statement is correct (as the transcription's NOTE says); it holds for every finite
measure `μ`, not only probability measures. The book treats one good; `Lp ℝ ⊤ μ` is the
one-good space.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- An element of `L∞(μ)` is bounded a.e. by its norm: `|x(z)| ≤ ‖x‖` for `μ`-a.e. `z`. -/
theorem ae_abs_le_norm_linfty (x : Lp ℝ ⊤ μ) : ∀ᵐ z ∂μ, |x z| ≤ ‖x‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := (x : Z → ℝ)) (μ := μ)] with z hz
  have hfin : eLpNorm x ⊤ μ ≠ ⊤ := Lp.eLpNorm_ne_top x
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable x)] at hfin
  rw [← Real.norm_eq_abs, Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable x),
    ← toReal_enorm]
  exact ENNReal.toReal_mono hfin hz

/-- Conversely, an a.e. bound `|x(z)| ≤ C` gives `‖x‖_∞ ≤ C` (finite `μ`). -/
theorem norm_linfty_le_of_ae_abs_le [IsFiniteMeasure μ] {x : Lp ℝ ⊤ μ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ z ∂μ, |x z| ≤ C) : ‖x‖ ≤ C := by
  have := Lp.norm_le_of_ae_bound (f := x) hC (by
    filter_upwards [h] with z hz
    rwa [Real.norm_eq_abs])
  simpa using this

/-- The function `x · 1_B` as an element of `L∞(μ)`, for a measurable `B` (an auxiliary form of
`linftyRestrict`). -/
noncomputable def linftyRestrictFn {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    Lp ℝ ⊤ μ :=
  MemLp.toLp (B.indicator (x : Z → ℝ)) ((Lp.memLp x).indicator hB)

/-- `x · 1_B` agrees a.e. with `1_B x`. -/
theorem coeFn_linftyRestrictFn {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    linftyRestrictFn hB x =ᵐ[μ] B.indicator x :=
  MemLp.coeFn_toLp _

/-- Restriction `x ↦ x · 1_B` to a measurable set `B` as a linear map. -/
noncomputable def linftyRestrictLM {B : Set Z} (hB : MeasurableSet B) :
    Lp ℝ ⊤ μ →ₗ[ℝ] Lp ℝ ⊤ μ where
  toFun := linftyRestrictFn hB
  map_add' x y := by
    apply Lp.ext
    filter_upwards [coeFn_linftyRestrictFn hB (x + y), coeFn_linftyRestrictFn hB x,
      coeFn_linftyRestrictFn hB y, Lp.coeFn_add x y,
      Lp.coeFn_add (linftyRestrictFn hB x) (linftyRestrictFn hB y)] with z h1 h2 h3 h4 h5
    rw [h5, Pi.add_apply, h1, h2, h3]
    by_cases hz : z ∈ B
    · simp only [indicator_of_mem hz, h4, Pi.add_apply]
    · simp only [indicator_of_notMem hz, add_zero]
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [coeFn_linftyRestrictFn hB (c • x), coeFn_linftyRestrictFn hB x,
      Lp.coeFn_smul c x, Lp.coeFn_smul c (linftyRestrictFn hB x)] with z h1 h2 h3 h4
    rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2]
    by_cases hz : z ∈ B
    · simp only [indicator_of_mem hz, h3, Pi.smul_apply]
    · simp only [indicator_of_notMem hz, smul_zero]

/-- Restriction does not increase the `L∞` norm. -/
theorem norm_linftyRestrictFn_le {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    ‖linftyRestrictFn hB x‖ ≤ ‖x‖ := by
  rw [linftyRestrictFn, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top x) (eLpNorm_indicator_le _ hB)

variable (μ) in
/-- **Restriction to an event**: `x ↦ x · 1_B` as a continuous linear map on `L∞(μ)` (for a
non-measurable `B`, the zero map; it is only used for measurable `B`). -/
noncomputable def linftyRestrict (B : Set Z) : Lp ℝ ⊤ μ →L[ℝ] Lp ℝ ⊤ μ := by
  classical
  exact if hB : MeasurableSet B then
    (linftyRestrictLM hB).mkContinuous 1 (fun x => by
      rw [one_mul]
      exact norm_linftyRestrictFn_le hB x)
  else 0

/-- For measurable `B`, `linftyRestrict μ B` is `x ↦ x · 1_B`. -/
theorem linftyRestrict_apply {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ B x = linftyRestrictFn hB x := by
  simp only [linftyRestrict, hB, ↓reduceDIte]
  rfl

/-- For a non-measurable `B`, `linftyRestrict μ B = 0` (a convention). -/
theorem linftyRestrict_of_not_measurable {B : Set Z} (hB : ¬ MeasurableSet B) :
    linftyRestrict μ B = 0 := by
  simp only [linftyRestrict, hB, ↓reduceDIte]

/-- `x · 1_B` agrees a.e. with `1_B x`. -/
theorem coeFn_linftyRestrict {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ B x =ᵐ[μ] B.indicator x := by
  rw [linftyRestrict_apply hB]
  exact coeFn_linftyRestrictFn hB x

/-- `‖x · 1_B‖_∞ ≤ ‖x‖_∞`. -/
theorem norm_linftyRestrict_le (B : Set Z) (x : Lp ℝ ⊤ μ) : ‖linftyRestrict μ B x‖ ≤ ‖x‖ := by
  by_cases hB : MeasurableSet B
  · rw [linftyRestrict_apply hB]
    exact norm_linftyRestrictFn_le hB x
  · simp [linftyRestrict_of_not_measurable hB]

/-- The restriction operator has norm at most `1`. -/
theorem opNorm_linftyRestrict_le (B : Set Z) : ‖linftyRestrict μ B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact norm_linftyRestrict_le B x

/-- `(x · 1_C) · 1_B = x · 1_{B ∩ C}`. -/
theorem linftyRestrict_linftyRestrict {B C : Set Z} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (x : Lp ℝ ⊤ μ) : linftyRestrict μ B (linftyRestrict μ C x) = linftyRestrict μ (B ∩ C) x := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict hB (linftyRestrict μ C x), coeFn_linftyRestrict hC x,
    coeFn_linftyRestrict (hB.inter hC) x] with z h1 h2 h3
  rw [h1, h3]
  by_cases hzB : z ∈ B
  · by_cases hzC : z ∈ C
    · simp [hzB, hzC, h2]
    · simp [hzB, hzC, h2]
  · simp [hzB]

/-- For disjoint measurable `B`, `C`: `x · 1_{B ∪ C} = x · 1_B + x · 1_C`. -/
theorem linftyRestrict_union {B C : Set Z} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hd : Disjoint B C) (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ (B ∪ C) x = linftyRestrict μ B x + linftyRestrict μ C x := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict (hB.union hC) x, coeFn_linftyRestrict hB x,
    coeFn_linftyRestrict hC x, Lp.coeFn_add (linftyRestrict μ B x) (linftyRestrict μ C x)]
    with z h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, indicator_union_of_disjoint hd]

/-- `x · 1_Z = x`. -/
theorem linftyRestrict_univ (x : Lp ℝ ⊤ μ) : linftyRestrict μ univ x = x := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict MeasurableSet.univ x] with z h1
  rw [h1, indicator_univ]

/-- Restriction to a `μ`-null set is `0` in `L∞(μ)`. -/
theorem linftyRestrict_of_null {B : Set Z} (hB : MeasurableSet B) (h : μ B = 0)
    (x : Lp ℝ ⊤ μ) : linftyRestrict μ B x = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict hB x, Lp.coeFn_zero ℝ ⊤ μ,
    measure_eq_zero_iff_ae_notMem.1 h] with z h1 h2 h3
  rw [h1, h2, indicator_of_notMem h3, Pi.zero_apply]

/-- For disjoint `B`, `C`: `‖u · 1_B + v · 1_C‖_∞ ≤ max ‖u‖_∞ ‖v‖_∞`. -/
theorem norm_linftyRestrict_add_le [IsFiniteMeasure μ] {B C : Set Z} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hd : Disjoint B C) (u v : Lp ℝ ⊤ μ) :
    ‖linftyRestrict μ B u + linftyRestrict μ C v‖ ≤ max ‖u‖ ‖v‖ := by
  refine norm_linfty_le_of_ae_abs_le (le_max_of_le_left (norm_nonneg _)) ?_
  filter_upwards [Lp.coeFn_add (linftyRestrict μ B u) (linftyRestrict μ C v),
    coeFn_linftyRestrict hB u, coeFn_linftyRestrict hC v, ae_abs_le_norm_linfty u,
    ae_abs_le_norm_linfty v] with z h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3]
  by_cases hzB : z ∈ B
  · have hzC : z ∉ C := Set.disjoint_left.1 hd hzB
    simp only [indicator_of_mem hzB, indicator_of_notMem hzC, add_zero]
    exact h4.trans (le_max_left _ _)
  · by_cases hzC : z ∈ C
    · simp only [indicator_of_mem hzC, indicator_of_notMem hzB, zero_add]
      exact h5.trans (le_max_right _ _)
    · simp only [indicator_of_notMem hzB, indicator_of_notMem hzC, add_zero, abs_zero]
      exact le_max_of_le_left (norm_nonneg _)

/-! ### The variation `W(B)` of `φ` on an event `B` -/

/-- `W(B) = ‖φ ∘ (x ↦ x · 1_B)‖`, the norm of `φ` on the functions supported in `B`; it is the
total variation `|ν|(B)` of the finitely additive set function `ν(E) = φ(1_E)`. -/
noncomputable def linftyRestrictNorm (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) : ℝ :=
  ‖φ.comp (linftyRestrict μ B)‖

/-- `W(B) ≥ 0`. -/
theorem linftyRestrictNorm_nonneg (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) :
    0 ≤ linftyRestrictNorm φ B :=
  norm_nonneg _

/-- `W(B) ≤ ‖φ‖`. -/
theorem linftyRestrictNorm_le_norm (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) :
    linftyRestrictNorm φ B ≤ ‖φ‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (opNorm_linftyRestrict_le B))

/-- `|φ(x · 1_B)| ≤ W(B) ‖x‖_∞`. -/
theorem abs_apply_linftyRestrict_le (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) (x : Lp ℝ ⊤ μ) :
    |φ (linftyRestrict μ B x)| ≤ linftyRestrictNorm φ B * ‖x‖ :=
  (φ.comp (linftyRestrict μ B)).le_opNorm x

/-- `W` is monotone: `B ⊆ C` implies `W(B) ≤ W(C)`. -/
theorem linftyRestrictNorm_mono (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) {B C : Set Z} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hBC : B ⊆ C) : linftyRestrictNorm φ B ≤ linftyRestrictNorm φ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (linftyRestrictNorm_nonneg φ C) fun x => ?_
  have h : linftyRestrict μ B x = linftyRestrict μ C (linftyRestrict μ B x) := by
    rw [linftyRestrict_linftyRestrict hC hB, inter_eq_right.2 hBC]
  rw [ContinuousLinearMap.comp_apply, h]
  exact (abs_apply_linftyRestrict_le φ C _).trans
    (mul_le_mul_of_nonneg_left (norm_linftyRestrict_le B x) (linftyRestrictNorm_nonneg φ C))

/-- Sign flip: for a functional `g` and `x`, some `x'` with `‖x'‖ = ‖x‖` has `g(x') = |g(x)|`. -/
theorem linfty_exists_apply_eq_abs (g : StrongDual ℝ (Lp ℝ ⊤ μ)) (x : Lp ℝ ⊤ μ) :
    ∃ x' : Lp ℝ ⊤ μ, ‖x'‖ = ‖x‖ ∧ g x' = |g x| := by
  rcases le_total 0 (g x) with h | h
  · exact ⟨x, rfl, (abs_of_nonneg h).symm⟩
  · exact ⟨-x, norm_neg x, by rw [map_neg, abs_of_nonpos h]⟩

/-- `W` is superadditive on disjoint measurable sets: `W(B) + W(C) ≤ W(B ∪ C)` (in fact `W` is
additive, but only this inequality is needed). -/
theorem linftyRestrictNorm_add_le [IsFiniteMeasure μ] (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) {B C : Set Z}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hd : Disjoint B C) :
    linftyRestrictNorm φ B + linftyRestrictNorm φ C ≤ linftyRestrictNorm φ (B ∪ C) := by
  have key : ∀ x y : Lp ℝ ⊤ μ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |φ (linftyRestrict μ B x)| + |φ (linftyRestrict μ C y)| ≤ linftyRestrictNorm φ (B ∪ C) := by
    intro x y hx hy
    obtain ⟨x', hx'n, hx'⟩ := linfty_exists_apply_eq_abs (φ.comp (linftyRestrict μ B)) x
    obtain ⟨y', hy'n, hy'⟩ := linfty_exists_apply_eq_abs (φ.comp (linftyRestrict μ C)) y
    set z := linftyRestrict μ B x' + linftyRestrict μ C y' with hz
    have hzn : ‖z‖ ≤ 1 :=
      (norm_linftyRestrict_add_le hB hC hd x' y').trans (max_le (hx'n ▸ hx) (hy'n ▸ hy))
    have hrz : linftyRestrict μ (B ∪ C) z = z := by
      rw [hz, map_add, linftyRestrict_linftyRestrict (hB.union hC) hB,
        linftyRestrict_linftyRestrict (hB.union hC) hC, union_inter_cancel_left,
        union_inter_cancel_right]
    have h1 := abs_apply_linftyRestrict_le φ (B ∪ C) z
    rw [hrz, hz, map_add] at h1
    simp only [ContinuousLinearMap.comp_apply] at hx' hy'
    rw [hx', hy', ← hz, abs_of_nonneg (by positivity)] at h1
    exact h1.trans (mul_le_of_le_one_right (linftyRestrictNorm_nonneg φ _) hzn)
  have hC' : ∀ y : Lp ℝ ⊤ μ, ‖y‖ = 1 →
      ‖(φ.comp (linftyRestrict μ C)) y‖ ≤
        linftyRestrictNorm φ (B ∪ C) - linftyRestrictNorm φ B := by
    intro y hy
    have hB' : linftyRestrictNorm φ B ≤
        linftyRestrictNorm φ (B ∪ C) - |φ (linftyRestrict μ C y)| := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm ?_ fun x hx => ?_
      · have := key 0 y (by simp) hy.le
        simp only [map_zero, abs_zero, zero_add] at this
        linarith
      · have := key x y hx.le hy.le
        rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
        linarith
    rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
    linarith
  have := ContinuousLinearMap.opNorm_le_of_unit_norm (by
      have := linftyRestrictNorm_mono φ hB (hB.union hC) subset_union_left
      linarith) hC'
  change linftyRestrictNorm φ C ≤ _ at this
  linarith

/-! ### The tail sequence `A_n` and the limit functional `ψ` -/

variable (μ) in
/-- **Truncation over an event** (p. 468): `x^A = x · 1_{Z ∖ A}`, i.e. `x^A(z) = 0` on `A` and
`x(z)` off `A`. -/
noncomputable def linftyTrunc (A : Set Z) : Lp ℝ ⊤ μ →L[ℝ] Lp ℝ ⊤ μ := linftyRestrict μ Aᶜ

/-- `s_m = inf {W(Z ∖ A) : A ∈ 𝒵, μ(A) ≤ 2^{-m}}`: the least mass `φ` can keep after cutting
away an event of probability at most `2^{-m}`. -/
noncomputable def linftyTailInf (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) : ℝ :=
  ⨅ A : {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m}, linftyRestrictNorm φ (A : Set Z)ᶜ

/-- `s_m ≤ W(Z ∖ A)` whenever `μ(A) ≤ 2^{-m}`. -/
theorem linftyTailInf_le (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) {m : ℕ} {A : Set Z} (hA : MeasurableSet A)
    (hμA : μ A ≤ 2⁻¹ ^ m) : linftyTailInf φ m ≤ linftyRestrictNorm φ Aᶜ :=
  ciInf_le (f := fun A : {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m} =>
      linftyRestrictNorm φ (A : Set Z)ᶜ)
    ⟨0, by rintro _ ⟨B, rfl⟩; exact linftyRestrictNorm_nonneg φ _⟩ ⟨A, hA, hμA⟩

/-- `s_m ≥ 0`. -/
theorem linftyTailInf_nonneg (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) : 0 ≤ linftyTailInf φ m := by
  have : Nonempty {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m} :=
    ⟨⟨∅, MeasurableSet.empty, by simp⟩⟩
  exact le_ciInf fun A => linftyRestrictNorm_nonneg φ _

/-- `s_m ≤ ‖φ‖`. -/
theorem linftyTailInf_le_norm (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) : linftyTailInf φ m ≤ ‖φ‖ :=
  (linftyTailInf_le φ MeasurableSet.empty (by simp)).trans (linftyRestrictNorm_le_norm φ _)

/-- `s_m` is increasing in `m`. -/
theorem linftyTailInf_mono (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) : Monotone (linftyTailInf φ) := by
  intro m m' hmm'
  have : Nonempty {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m'} :=
    ⟨⟨∅, MeasurableSet.empty, by simp⟩⟩
  refine le_ciInf fun A => linftyTailInf_le φ A.2.1 (A.2.2.trans ?_)
  exact pow_le_pow_of_le_one zero_le (by norm_num) hmm'

/-- `s = sup_m s_m = lim_m s_m`, the mass of the countably additive part of `φ`. -/
noncomputable def linftyTailSup (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) : ℝ := ⨆ m, linftyTailInf φ m

/-- The `s_m` are bounded above by `‖φ‖`. -/
theorem bddAbove_linftyTailInf (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) : BddAbove (range (linftyTailInf φ)) :=
  ⟨‖φ‖, by rintro _ ⟨m, rfl⟩; exact linftyTailInf_le_norm φ m⟩

/-- `s_m ≤ s`. -/
theorem linftyTailInf_le_linftyTailSup (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) :
    linftyTailInf φ m ≤ linftyTailSup φ :=
  le_ciSup (bddAbove_linftyTailInf φ) m

/-- `s_m → s`. -/
theorem tendsto_linftyTailInf (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) :
    Tendsto (linftyTailInf φ) atTop (𝓝 (linftyTailSup φ)) :=
  tendsto_atTop_ciSup (linftyTailInf_mono φ) (bddAbove_linftyTailInf φ)

/-- A **tail sequence** for `φ`: measurable, nested decreasing `A_n` with `μ(A_n) ≤ 2^{-n}` and
`W(Z ∖ A_n) ≤ s + 2^{-n}` (the sets `A_n` of Lemma 15.7). -/
structure IsLinftyTailSeq (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (A : ℕ → Set Z) : Prop where
  measurableSet : ∀ n, MeasurableSet (A n)
  antitone : Antitone A
  measure_le : ∀ n, μ (A n) ≤ 2⁻¹ ^ n
  linftyRestrictNorm_le : ∀ n, linftyRestrictNorm φ (A n)ᶜ ≤ linftyTailSup φ + 2⁻¹ ^ n

/-- Every `φ ∈ L∞(μ)*` has a tail sequence: choose `A'_n` with `μ(A'_n) ≤ 2^{-(n+1)}` and
`W(Z ∖ A'_n) < s_{n+1} + 2^{-n}`, and put `A_n = ⋃_{k ≥ n} A'_k`. -/
theorem exists_isLinftyTailSeq (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) :
    ∃ A : ℕ → Set Z, IsLinftyTailSeq φ A := by
  have hex : ∀ n : ℕ, ∃ B : {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ (n + 1)},
      linftyRestrictNorm φ (B : Set Z)ᶜ < linftyTailInf φ (n + 1) + 2⁻¹ ^ n := fun n => by
    have : Nonempty {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ (n + 1)} :=
      ⟨⟨∅, MeasurableSet.empty, by simp⟩⟩
    exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ (pow_pos (by norm_num) n))
  choose B hB using hex
  refine ⟨fun n => ⋃ k, (B (n + k) : Set Z),
    ⟨fun n => MeasurableSet.iUnion fun k => (B (n + k)).2.1, ?_, fun n => ?_, fun n => ?_⟩⟩
  · refine antitone_nat_of_succ_le fun n => iUnion_subset fun k => ?_
    refine subset_iUnion_of_subset (k + 1) ?_
    rw [show n + 1 + k = n + (k + 1) by ring]
  · calc μ (⋃ k, (B (n + k) : Set Z)) ≤ ∑' k, μ (B (n + k)) := measure_iUnion_le _
      _ ≤ ∑' k, (2⁻¹ : ENNReal) ^ (n + k + 1) := ENNReal.tsum_le_tsum fun k => (B (n + k)).2.2
      _ = 2⁻¹ ^ n := by
        simp_rw [pow_add, pow_one]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv, mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  · calc linftyRestrictNorm φ (⋃ k, (B (n + k) : Set Z))ᶜ ≤ linftyRestrictNorm φ (B n : Set Z)ᶜ :=
          linftyRestrictNorm_mono φ (MeasurableSet.iUnion fun k => (B (n + k)).2.1).compl
            (B n).2.1.compl (compl_subset_compl.2 (subset_iUnion_of_subset 0 (by simp)))
      _ ≤ linftyTailInf φ (n + 1) + 2⁻¹ ^ n := (hB n).le
      _ ≤ linftyTailSup φ + 2⁻¹ ^ n := by linarith [linftyTailInf_le_linftyTailSup φ (n + 1)]

variable {φ : StrongDual ℝ (Lp ℝ ⊤ μ)} {A : ℕ → Set Z}

/-- Along a tail sequence, `s_n ≤ W(Z ∖ A_n)`. -/
theorem IsLinftyTailSeq.tailInf_le_restrictNorm (hA : IsLinftyTailSeq φ A) (n : ℕ) :
    linftyTailInf φ n ≤ linftyRestrictNorm φ (A n)ᶜ :=
  linftyTailInf_le φ (hA.measurableSet n) (hA.measure_le n)

/-- For `B' ⊆ B`: `x^{B'} − x^B = x · 1_{(Z ∖ B') ∩ B}`. -/
theorem linftyTrunc_sub_linftyTrunc {B B' : Set Z} (hB : MeasurableSet B)
    (hB' : MeasurableSet B') (h : B' ⊆ B) (x : Lp ℝ ⊤ μ) :
    linftyTrunc μ B' x - linftyTrunc μ B x = linftyRestrict μ (B'ᶜ ∩ B) x := by
  have hset : Bᶜ ∪ (B'ᶜ ∩ B) = B'ᶜ := by
    ext z
    simp only [mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · rintro (hz | ⟨hz, -⟩)
      · exact fun hz' => hz (h hz')
      · exact hz
    · intro hz
      by_cases hzB : z ∈ B
      · exact Or.inr ⟨hz, hzB⟩
      · exact Or.inl hzB
  have hd : Disjoint Bᶜ (B'ᶜ ∩ B) := disjoint_left.2 fun z hz hz' => hz hz'.2
  have h2 := linftyRestrict_union hB.compl (hB'.compl.inter hB) hd x
  rw [hset] at h2
  rw [linftyTrunc, linftyTrunc, h2, add_sub_cancel_left]

/-- For `n ≤ m`: `|φ(x^{A_m}) − φ(x^{A_n})| ≤ ‖x‖ (W(Z ∖ A_m) − W(Z ∖ A_n))`. -/
theorem IsLinftyTailSeq.abs_sub_le [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) {n m : ℕ}
    (hnm : n ≤ m) (x : Lp ℝ ⊤ μ) :
    |φ (linftyTrunc μ (A m) x) - φ (linftyTrunc μ (A n) x)| ≤
      ‖x‖ * (linftyRestrictNorm φ (A m)ᶜ - linftyRestrictNorm φ (A n)ᶜ) := by
  have hsub := hA.antitone hnm
  rw [← map_sub, linftyTrunc_sub_linftyTrunc (hA.measurableSet n) (hA.measurableSet m) hsub]
  have hd : Disjoint (A n)ᶜ ((A m)ᶜ ∩ A n) := disjoint_left.2 fun z hz hz' => hz hz'.2
  have hun : (A n)ᶜ ∪ ((A m)ᶜ ∩ A n) = (A m)ᶜ := by
    rw [union_inter_distrib_left, compl_union_self, inter_univ,
      union_eq_right.2 (compl_subset_compl.2 hsub)]
  have h1 := linftyRestrictNorm_add_le φ (hA.measurableSet n).compl
    ((hA.measurableSet m).compl.inter (hA.measurableSet n)) hd
  rw [hun] at h1
  calc _ ≤ linftyRestrictNorm φ ((A m)ᶜ ∩ A n) * ‖x‖ := abs_apply_linftyRestrict_le φ _ x
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg x)

/-- Along a tail sequence, `n ↦ φ(x^{A_n})` is a Cauchy sequence. -/
theorem IsLinftyTailSeq.cauchySeq [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) (x : Lp ℝ ⊤ μ) :
    CauchySeq fun n => φ (linftyTrunc μ (A n) x) := by
  refine cauchySeq_of_le_tendsto_0 (fun N => ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ N - linftyTailInf φ N))
    (fun n m N hn hm => ?_) ?_
  · have key : ∀ n m, N ≤ n → n ≤ m → |φ (linftyTrunc μ (A m) x) - φ (linftyTrunc μ (A n) x)|
        ≤ ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ N - linftyTailInf φ N) := by
      intro n m hn hnm
      refine (hA.abs_sub_le hnm x).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg x))
      have h1 := hA.linftyRestrictNorm_le m
      have h2 := hA.tailInf_le_restrictNorm n
      have h3 : (2⁻¹ : ℝ) ^ m ≤ 2⁻¹ ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (hn.trans hnm)
      have h4 := linftyTailInf_mono φ hn
      linarith
    rw [Real.dist_eq]
    rcases le_total n m with h | h
    · rw [abs_sub_comm]
      exact key n m hn h
    · exact key m n hm h
  · have : Tendsto (fun N : ℕ => ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ N - linftyTailInf φ N)) atTop
        (𝓝 (‖x‖ * (linftyTailSup φ + 0 - linftyTailSup φ))) :=
      ((tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num))).sub (tendsto_linftyTailInf φ)).const_mul _
    simpa using this

/-- `ψ(x) = lim_n φ(x^{A_n})` (Lemma 15.7; the limit exists along a tail sequence). -/
noncomputable def linftyTruncLimit (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (A : ℕ → Set Z)
    (x : Lp ℝ ⊤ μ) : ℝ :=
  limUnder atTop fun n => φ (linftyTrunc μ (A n) x)

/-- `φ(x^{A_n}) → ψ(x)` along a tail sequence. -/
theorem IsLinftyTailSeq.tendsto [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) (x : Lp ℝ ⊤ μ) :
    Tendsto (fun n => φ (linftyTrunc μ (A n) x)) atTop (𝓝 (linftyTruncLimit φ A x)) :=
  (hA.cauchySeq x).tendsto_limUnder

/-- `ψ` as a continuous linear functional, `‖ψ‖ ≤ ‖φ‖`. -/
noncomputable def IsLinftyTailSeq.limitDual [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) :
    StrongDual ℝ (Lp ℝ ⊤ μ) :=
  LinearMap.mkContinuous
    { toFun := linftyTruncLimit φ A
      map_add' := fun x y => tendsto_nhds_unique (hA.tendsto (x + y))
        (by simpa only [map_add] using (hA.tendsto x).add (hA.tendsto y))
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_eq_mul]
        exact tendsto_nhds_unique (hA.tendsto (c • x))
          (by simpa only [map_smul, smul_eq_mul] using (hA.tendsto x).const_mul c) }
    ‖φ‖ fun x => by
      refine le_of_tendsto' (hA.tendsto x).norm fun n => ?_
      exact (φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_linftyRestrict_le _ x) (norm_nonneg φ))

/-- `limitDual` evaluates to `ψ(x) = lim_n φ(x^{A_n})`. -/
theorem IsLinftyTailSeq.limitDual_apply [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A)
    (x : Lp ℝ ⊤ μ) :
    hA.limitDual x = linftyTruncLimit φ A x :=
  rfl

/-- `‖ψ‖ ≤ ‖φ‖`. -/
theorem IsLinftyTailSeq.norm_limitDual_le [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) :
    ‖hA.limitDual‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg φ) _

/-- **Uniform absolute continuity of `ψ`**: if `μ(B) ≤ 2^{-(m+1)}` then
`|ψ(x · 1_B)| ≤ ‖x‖ (s − s_m)`, and `s − s_m → 0`. -/
theorem IsLinftyTailSeq.abs_linftyTruncLimit_restrict_le [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) {B : Set Z} (hB : MeasurableSet B) {m : ℕ}
    (hμB : μ B ≤ 2⁻¹ ^ (m + 1)) (x : Lp ℝ ⊤ μ) :
    |linftyTruncLimit φ A (linftyRestrict μ B x)| ≤
      ‖x‖ * (linftyTailSup φ - linftyTailInf φ m) := by
  have hlim : Tendsto (fun n : ℕ => ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ n - linftyTailInf φ m)) atTop
      (𝓝 (‖x‖ * (linftyTailSup φ - linftyTailInf φ m))) := by
    have := (((tendsto_const_nhds (x := linftyTailSup φ)).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
        (by norm_num))).sub_const (linftyTailInf φ m)).const_mul ‖x‖
    simpa using this
  refine le_of_tendsto_of_tendsto (hA.tendsto _).abs hlim ?_
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn
  have hAn := hA.measurableSet n
  rw [linftyTrunc, linftyRestrict_linftyRestrict hAn.compl hB]
  have hd : Disjoint ((A n)ᶜ ∩ B) ((A n)ᶜ ∩ Bᶜ) :=
    disjoint_left.2 fun z hz hz' => hz'.2 hz.2
  have h1 := linftyRestrictNorm_add_le φ (hAn.compl.inter hB) (hAn.compl.inter hB.compl) hd
  rw [inter_union_compl] at h1
  have h2 := hA.linftyRestrictNorm_le n
  have hμ : μ (A n ∪ B) ≤ 2⁻¹ ^ m :=
    calc μ (A n ∪ B) ≤ μ (A n) + μ B := measure_union_le _ _
      _ ≤ 2⁻¹ ^ (m + 1) + 2⁻¹ ^ (m + 1) :=
        add_le_add ((hA.measure_le n).trans (pow_le_pow_of_le_one zero_le
          (by norm_num) hn)) hμB
      _ = 2⁻¹ ^ m := by
        rw [← two_mul, pow_succ, mul_comm (2⁻¹ ^ m), ← mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have h3 : linftyTailInf φ m ≤ linftyRestrictNorm φ ((A n)ᶜ ∩ Bᶜ) := by
    rw [← compl_union]
    exact linftyTailInf_le φ (hAn.union hB) hμ
  have h4 : (2⁻¹ : ℝ) ^ n ≥ 0 := by positivity
  calc _ ≤ linftyRestrictNorm φ ((A n)ᶜ ∩ B) * ‖x‖ := abs_apply_linftyRestrict_le φ _ x
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg x)

/-- `ψ(x^{A_n}) = φ(x^{A_n})`: the remainder `φ − ψ` vanishes on every function vanishing on
`A_n` (it is concentrated on the sets `A_n`, i.e. it is purely finitely additive). -/
theorem IsLinftyTailSeq.linftyTruncLimit_linftyTrunc [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) (n : ℕ) (x : Lp ℝ ⊤ μ) :
    linftyTruncLimit φ A (linftyTrunc μ (A n) x) = φ (linftyTrunc μ (A n) x) := by
  refine tendsto_nhds_unique (hA.tendsto _) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [linftyTrunc, linftyTrunc, linftyRestrict_linftyRestrict (hA.measurableSet m).compl
    (hA.measurableSet n).compl, inter_eq_right.2 (compl_subset_compl.2 (hA.antitone hm))]

/-- If `μ(B_N) → 0` then `ψ(x · 1_{B_N}) → 0`. -/
theorem IsLinftyTailSeq.tendsto_linftyTruncLimit_restrict [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) {B : ℕ → Set Z} (hB : ∀ N, MeasurableSet (B N))
    (hμ : Tendsto (fun N => μ (B N)) atTop (𝓝 0)) (x : Lp ℝ ⊤ μ) :
    Tendsto (fun N => linftyTruncLimit φ A (linftyRestrict μ (B N) x)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : Tendsto (fun m => ‖x‖ * (linftyTailSup φ - linftyTailInf φ m)) atTop (𝓝 0) := by
    simpa using ((tendsto_linftyTailInf φ).const_sub (linftyTailSup φ)).const_mul ‖x‖
  obtain ⟨m, hm⟩ := (h1.eventually (gt_mem_nhds hε)).exists
  have h2 : ∀ᶠ N in atTop, μ (B N) ≤ 2⁻¹ ^ (m + 1) :=
    hμ.eventually (ge_mem_nhds (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h2
  refine ⟨N₀, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hA.abs_linftyTruncLimit_restrict_le (hB N) (hN₀ N hN) x).trans_lt hm

/-! ### `ψ` is an `L¹` density: the signed measure `E ↦ ψ(1_E)` and Radon–Nikodym -/

variable (μ) in
/-- The constant function `1` in `L∞(μ)`. -/
noncomputable def linftyOne : Lp ℝ ⊤ μ := MemLp.toLp (fun _ => (1 : ℝ)) (memLp_top_const 1)

/-- `1` is a.e. the constant `1`. -/
theorem coeFn_linftyOne : linftyOne μ =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _

/-- `‖1‖_∞ ≤ 1`. -/
theorem norm_linftyOne_le [IsFiniteMeasure μ] : ‖linftyOne μ‖ ≤ 1 :=
  norm_linfty_le_of_ae_abs_le zero_le_one (by
    filter_upwards [coeFn_linftyOne (μ := μ)] with z hz
    simp [hz])

/-- `1 · 1_E` is a.e. the indicator `1_E`. -/
theorem coeFn_linftyRestrict_one {E : Set Z} (hE : MeasurableSet E) :
    linftyRestrict μ E (linftyOne μ) =ᵐ[μ] E.indicator fun _ => (1 : ℝ) := by
  filter_upwards [coeFn_linftyRestrict hE (linftyOne μ), coeFn_linftyOne (μ := μ)] with z h1 h2
  rw [h1]
  by_cases hz : z ∈ E
  · simp [hz, h2]
  · simp [hz]

/-- Finite superadditivity: `Σ_{i<N} W(f_i) ≤ W(⋃_{i<N} f_i)` for disjoint measurable `f_i`. -/
theorem linftyRestrictNorm_sum_le [IsFiniteMeasure μ] (ψ : StrongDual ℝ (Lp ℝ ⊤ μ)) {f : ℕ → Set Z}
    (hf : ∀ i, MeasurableSet (f i)) (hdisj : Pairwise (Function.onFun Disjoint f)) (N : ℕ) :
    ∑ i ∈ Finset.range N, linftyRestrictNorm ψ (f i) ≤
      linftyRestrictNorm ψ (⋃ i ∈ Finset.range N, f i) := by
  induction N with
  | zero => simp [linftyRestrictNorm_nonneg]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hd : Disjoint (⋃ i ∈ Finset.range N, f i) (f N) :=
      disjoint_iUnion_left.2 fun i => disjoint_iUnion_left.2 fun hi =>
        hdisj (Finset.mem_range.1 hi).ne
    exact (add_le_add_left ih _).trans
      (linftyRestrictNorm_add_le ψ (Finset.measurableSet_biUnion _ fun i _ => hf i) (hf N) hd)

/-- Finite additivity of restriction: `x · 1_{⋃_{i<N} f_i} = Σ_{i<N} x · 1_{f_i}`. -/
theorem linftyRestrict_sum [IsFiniteMeasure μ] {f : ℕ → Set Z}
    (hf : ∀ i, MeasurableSet (f i)) (hdisj : Pairwise (Function.onFun Disjoint f)) (N : ℕ)
    (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ (⋃ i ∈ Finset.range N, f i) x =
      ∑ i ∈ Finset.range N, linftyRestrict μ (f i) x := by
  induction N with
  | zero => simp [linftyRestrict_of_null MeasurableSet.empty measure_empty]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hd : Disjoint (⋃ i ∈ Finset.range N, f i) (f N) :=
      disjoint_iUnion_left.2 fun i => disjoint_iUnion_left.2 fun hi =>
        hdisj (Finset.mem_range.1 hi).ne
    rw [linftyRestrict_union (Finset.measurableSet_biUnion _ fun i _ => hf i) (hf N) hd, ih]

/-- The **countably additive** signed measure `E ↦ ψ(1_E)` (countable additivity from
`tendsto_linftyTruncLimit_restrict`, absolute summability from superadditivity of `W`). -/
noncomputable def IsLinftyTailSeq.limitSignedMeasure [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) :
    SignedMeasure Z where
  measureOf' E := hA.limitDual (linftyRestrict μ E (linftyOne μ))
  empty' := by rw [linftyRestrict_of_null MeasurableSet.empty measure_empty, map_zero]
  not_measurable' E hE := by
    rw [linftyRestrict_of_not_measurable hE, zero_apply, map_zero]
  m_iUnion' f hf hdisj := by
    set ψ := hA.limitDual
    have hsum : Summable fun i => ‖ψ (linftyRestrict μ (f i) (linftyOne μ))‖ := by
      refine summable_of_sum_range_le (c := ‖ψ‖) (fun i => norm_nonneg _) fun N => ?_
      calc ∑ i ∈ Finset.range N, ‖ψ (linftyRestrict μ (f i) (linftyOne μ))‖
          ≤ ∑ i ∈ Finset.range N, linftyRestrictNorm ψ (f i) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Real.norm_eq_abs]
            exact (abs_apply_linftyRestrict_le ψ _ _).trans
              (mul_le_of_le_one_right (linftyRestrictNorm_nonneg ψ _) norm_linftyOne_le)
        _ ≤ linftyRestrictNorm ψ (⋃ i ∈ Finset.range N, f i) :=
            linftyRestrictNorm_sum_le ψ hf hdisj N
        _ ≤ ‖ψ‖ := linftyRestrictNorm_le_norm ψ _
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    set T : ℕ → Set Z := fun N => (⋃ i, f i) \ ⋃ i ∈ Finset.range N, f i with hT
    have hTm : ∀ N, MeasurableSet (T N) := fun N =>
      (MeasurableSet.iUnion hf).diff (Finset.measurableSet_biUnion _ fun i _ => hf i)
    have hsplit : ∀ N, ψ (linftyRestrict μ (⋃ i, f i) (linftyOne μ)) =
        ∑ i ∈ Finset.range N, ψ (linftyRestrict μ (f i) (linftyOne μ)) +
          ψ (linftyRestrict μ (T N) (linftyOne μ)) := by
      intro N
      have hun : (⋃ i ∈ Finset.range N, f i) ∪ T N = ⋃ i, f i := by
        rw [hT, union_sdiff_self, union_eq_right]
        exact iUnion₂_subset fun i _ => subset_iUnion f i
      have hd : Disjoint (⋃ i ∈ Finset.range N, f i) (T N) := disjoint_sdiff_right
      rw [← hun, linftyRestrict_union (Finset.measurableSet_biUnion _ fun i _ => hf i) (hTm N) hd,
        linftyRestrict_sum hf hdisj, map_add, map_sum]
    have hTanti : Antitone T := by
      intro N M hNM
      refine sdiff_subset_sdiff_right (iUnion₂_subset fun i hi => ?_)
      exact subset_biUnion_of_mem (Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le hNM))
    have hTinter : (⋂ N, T N) = ∅ := by
      refine eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 hz 0).1
      exact (mem_iInter.1 hz (i + 1)).2 (mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self i)) hi)
    have hμT : Tendsto (fun N => μ (T N)) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hTm N).nullMeasurableSet) hTanti
        ⟨0, measure_ne_top μ _⟩
      rwa [hTinter, measure_empty] at this
    have h0 := (hA.tendsto_linftyTruncLimit_restrict hTm hμT (linftyOne μ))
    have h1 : Tendsto (fun N => ψ (linftyRestrict μ (⋃ i, f i) (linftyOne μ)) -
        ψ (linftyRestrict μ (T N) (linftyOne μ))) atTop
        (𝓝 (ψ (linftyRestrict μ (⋃ i, f i) (linftyOne μ)) - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h1
    refine h1.congr fun N => ?_
    rw [hsplit N, add_sub_cancel_right]

/-- `limitSignedMeasure E = ψ(1_E)`. -/
theorem IsLinftyTailSeq.limitSignedMeasure_apply [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A)
    (E : Set Z) :
    hA.limitSignedMeasure E = hA.limitDual (linftyRestrict μ E (linftyOne μ)) :=
  rfl

/-- `E ↦ ψ(1_E)` is absolutely continuous with respect to `μ`. -/
theorem IsLinftyTailSeq.limitSignedMeasure_absolutelyContinuous [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) : hA.limitSignedMeasure ≪ᵥ μ.toENNRealVectorMeasure := by
  intro E hE
  by_cases hm : MeasurableSet E
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hm] at hE
    rw [hA.limitSignedMeasure_apply, linftyRestrict_of_null hm hE, map_zero]
  · rw [hA.limitSignedMeasure_apply, linftyRestrict_of_not_measurable hm,
      zero_apply, map_zero]

/-- The functional `x ↦ ∫ p x dμ` on `L∞(μ)` for `p ∈ L¹(μ)` (Mathlib's `lpPairing`). -/
noncomputable def linftyL1Pairing (p : Z → ℝ) (hp : Integrable p μ) : StrongDual ℝ (Lp ℝ ⊤ μ) :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ⊤ (hp.toL1 p)

/-- `linftyL1Pairing p x = ∫ p(z) x(z) dμ(z)`. -/
theorem linftyL1Pairing_apply (p : Z → ℝ) (hp : Integrable p μ) (x : Lp ℝ ⊤ μ) :
    linftyL1Pairing p hp x = ∫ z, p z * x z ∂μ := by
  rw [linftyL1Pairing, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hp.coeFn_toL1] with z hz
  rw [ContinuousLinearMap.mul_apply', hz]

/-- A continuous linear functional on `L∞(μ)` vanishing on every indicator `1_E` is zero
(`x` is uniformly approximated by the step functions `⌊k x⌋ / k`). -/
theorem linfty_dual_eq_zero [IsFiniteMeasure μ] {χ : StrongDual ℝ (Lp ℝ ⊤ μ)}
    (h : ∀ E, MeasurableSet E → χ (linftyRestrict μ E (linftyOne μ)) = 0) : χ = 0 := by
  ext x
  rw [zero_apply]
  have key : ∀ k : ℕ, |χ x| ≤ ‖χ‖ * (1 / ((k : ℝ) + 1)) := by
    intro k
    set c : ℝ := k + 1 with hc
    have hcpos : 0 < c := by positivity
    have hfm : Measurable (x : Z → ℝ) := (Lp.stronglyMeasurable x).measurable
    have hgm : Measurable fun z => ⌊c * x z⌋ := (hfm.const_mul c).floor
    set N : ℕ := ⌈c * ‖x‖⌉₊ + 1 with hN
    set E : ℤ → Set Z := fun j => {z | ⌊c * x z⌋ = j} with hEdef
    have hE : ∀ j, MeasurableSet (E j) := fun j => hgm (measurableSet_singleton j)
    set J : Finset ℤ := Finset.Icc (-(N : ℤ)) N
    set y : Lp ℝ ⊤ μ := ∑ j ∈ J, ((j : ℝ) / c) • linftyRestrict μ (E j) (linftyOne μ) with hy
    have hχy : χ y = 0 := by
      simp only [hy, map_sum, map_smul, h _ (hE _), smul_zero, Finset.sum_const_zero]
    have hall : ∀ᵐ z ∂μ, ∀ j : ℤ, (((j : ℝ) / c) • linftyRestrict μ (E j) (linftyOne μ) :
        Lp ℝ ⊤ μ) z = (j : ℝ) / c * (E j).indicator (fun _ => (1 : ℝ)) z := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul ((j : ℝ) / c) (linftyRestrict μ (E j) (linftyOne μ)),
        coeFn_linftyRestrict_one (μ := μ) (hE j)] with z h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hxy : ‖x - y‖ ≤ 1 / c := by
      refine norm_linfty_le_of_ae_abs_le (by positivity) ?_
      filter_upwards [Lp.coeFn_sub x y, Lp.coeFn_fun_finsetSum J
        (fun j => ((j : ℝ) / c) • linftyRestrict μ (E j) (linftyOne μ)), hall,
        ae_abs_le_norm_linfty x] with z h1 h2 h3 h4
      rw [h1, Pi.sub_apply, hy, h2]
      simp only [h3]
      set j₀ := ⌊c * x z⌋ with hj₀
      have hfl1 : (j₀ : ℝ) ≤ c * x z := Int.floor_le _
      have hfl2 : c * x z < j₀ + 1 := Int.lt_floor_add_one _
      have hab := abs_le.1 h4
      have hcl : c * ‖x‖ ≤ (⌈c * ‖x‖⌉₊ : ℝ) := Nat.le_ceil _
      have hcx1 : c * x z ≤ c * ‖x‖ := mul_le_mul_of_nonneg_left hab.2 hcpos.le
      have hcx2 : -(c * ‖x‖) ≤ c * x z := by nlinarith [hab.1]
      have hmem : j₀ ∈ J := by
        rw [Finset.mem_Icc]
        constructor
        · have : ((-(N : ℤ) : ℤ) : ℝ) < j₀ := by
            rw [hN]
            push_cast
            linarith
          exact_mod_cast this.le
        · have : (j₀ : ℝ) ≤ ((N : ℤ) : ℝ) := by
            rw [hN]
            push_cast
            linarith
          exact_mod_cast this
      rw [Finset.sum_eq_single j₀]
      · have hz : z ∈ E j₀ := by simp [hEdef, hj₀]
        rw [indicator_of_mem hz, mul_one]
        have : x z - j₀ / c = (c * x z - j₀) / c := by field_simp
        rw [this, abs_div, abs_of_pos hcpos, div_le_div_iff_of_pos_right hcpos, abs_le]
        constructor <;> linarith
      · intro j _ hj
        have hz : z ∉ E j := by
          simp only [hEdef, mem_ofPred_eq]
          exact fun hz => hj (hz ▸ hj₀ ▸ rfl)
        rw [indicator_of_notMem hz, mul_zero]
      · intro hj
        exact absurd hmem hj
    calc |χ x| = |χ (x - y)| := by rw [map_sub, hχy, sub_zero]
      _ ≤ ‖χ‖ * ‖x - y‖ := χ.le_opNorm _
      _ ≤ ‖χ‖ * (1 / c) := mul_le_mul_of_nonneg_left hxy (norm_nonneg χ)
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ‖χ‖
  rw [mul_zero] at hlim
  exact abs_nonpos_iff.1 (ge_of_tendsto' hlim key)

/-- **Lemma 15.7** (p. 468). For every continuous linear functional `φ` on `L∞(Z, 𝒵, μ)` there is a
nested decreasing sequence `A_1 ⊇ A_2 ⊇ …` in `𝒵` with `μ(A_n) → 0` and a continuous linear
functional `ψ` with `ψ(x) = lim_n φ(x^{A_n})` for all `x`, and `ψ(x) = ∫ p x dμ` for some
`p ∈ L¹(μ)`. Also `‖ψ‖ ≤ ‖φ‖` and `ψ = φ` on every `x^{A_n}`. Proved directly (the book cites
Yosida–Hewitt), for any finite `μ`. -/
theorem lemma_15_7 [IsFiniteMeasure μ] (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) :
    ∃ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) ∧ Antitone A ∧
      Tendsto (fun n => μ (A n)) atTop (𝓝 0) ∧
      ∃ ψ : StrongDual ℝ (Lp ℝ ⊤ μ), ‖ψ‖ ≤ ‖φ‖ ∧
        (∀ x, Tendsto (fun n => φ (linftyTrunc μ (A n) x)) atTop (𝓝 (ψ x))) ∧
        (∀ n x, ψ (linftyTrunc μ (A n) x) = φ (linftyTrunc μ (A n) x)) ∧
        ∃ p : Z → ℝ, Integrable p μ ∧ ∀ x, ψ x = ∫ z, p z * x z ∂μ := by
  obtain ⟨A, hA⟩ := exists_isLinftyTailSeq φ
  refine ⟨A, hA.measurableSet, hA.antitone, ?_, hA.limitDual, hA.norm_limitDual_le, hA.tendsto,
    hA.linftyTruncLimit_linftyTrunc, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 2⁻¹) (by norm_num))
      (fun n => zero_le) hA.measure_le
  · set s := hA.limitSignedMeasure
    set p := s.rnDeriv μ
    have hp : Integrable p μ := SignedMeasure.integrable_rnDeriv s μ
    have hs := SignedMeasure.withDensityᵥ_rnDeriv_eq s μ
      hA.limitSignedMeasure_absolutelyContinuous
    refine ⟨p, hp, fun x => ?_⟩
    have hχ : hA.limitDual - linftyL1Pairing p hp = 0 := by
      refine linfty_dual_eq_zero fun E hE => ?_
      have h1 : s E = ∫ z in E, p z ∂μ := by
        rw [← hs, withDensityᵥ_apply hp hE]
      rw [sub_apply, linftyL1Pairing_apply, sub_eq_zero]
      rw [hA.limitSignedMeasure_apply] at h1
      rw [h1, ← integral_indicator hE]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_linftyRestrict_one (μ := μ) hE] with z hz
      rw [hz]
      by_cases hzE : z ∈ E
      · simp [hzE]
      · simp [hzE]
    have := congrArg (fun χ : StrongDual ℝ (Lp ℝ ⊤ μ) => χ x) hχ
    simp only [sub_apply, zero_apply, sub_eq_zero] at this
    rw [this, linftyL1Pairing_apply]

end StokeyLucasPrescott.EquilibriumApplications
