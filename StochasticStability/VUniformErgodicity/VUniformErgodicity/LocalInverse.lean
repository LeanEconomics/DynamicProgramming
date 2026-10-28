/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.FellerChains
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The change of variables behind the continuous components of MT §7.1

Meyn and Tweedie, proof of Proposition 7.1.2, pp. 149–151, and the "similar but more
complicated" argument for Proposition 7.1.5, p. 153. This module holds the analysis; the kernels
are in `NSSTChain`.

* `lowerSemicontinuous_mul_ennreal`, `lowerSemicontinuous_finset_prod`: products of lower
  semicontinuous `[0, ∞]`-valued functions are lower semicontinuous (for the product density
  `γ(u₁) ⋯ γ(uₖ)`).
* `lowerSemicontinuous_lintegral_of_lsc`: integrating a kernel that is lower semicontinuous in the
  parameter gives a lower semicontinuous function (Fatou's lemma). This replaces the book's
  approximation `rᵢ ↑ q_k` by continuous functions and dominated convergence (p. 151).
* `lintegral_pi_prod`, `pi_withDensity_eq`: the product of `k` copies of `γ · Leb` is
  `(γ(u₁) ⋯ γ(uₖ)) · Leb` (the densities in (7.6)).
* `exists_straightening`: the inverse function theorem with parameters. If `G : X × E → X` is `C¹`
  near `(x₀, u₀)` and `∂G/∂u (x₀, u₀)` is onto, then near `(x₀, u₀)` the map
  `Ψ(x, u) = (x, R G(x, u) + u − R L u)` (with `L = ∂G/∂u (x₀, u₀)` and `R` a right inverse of
  `L`) is a local homeomorphism with `G = L ∘ Ψ₂`, and the Jacobians of `u ↦ Ψ₂(x, u)` are
  bounded by `2`. This is the map `F^k` of p. 149, generalised to `dim X > 1` as in
  Proposition 7.1.5.
* `exists_lsc_minorant` (the core of (7.6)–(7.8)): there is a jointly lower semicontinuous
  `K ≥ 0`, positive at a point above `x₀` when the density is positive at `u₀`, with
  `∫ 1_A(L y) K(x, y) dy ≤ ∫_{(x, u) ∈ V} 1_A(G(x, u)) ρ(u) du` for all `x` and `A`.
* `exists_uniform_reach` (the step of Proposition 7.3.1): an open `B ∋ x₀` and a non-empty open
  `C` with `C ⊆ G(x, V_x)` for every `x ∈ B`.

**Proof differences.** The book's change of variables (7.7) is an equality with the inverse
function `G_k`; here only an inequality is needed, so the Jacobian factor is replaced by the
constant `2⁻¹` (the Jacobian is at most `2` near `(x₀, u₀)`). Lower semicontinuity then needs only
lower semicontinuity of the density, not of `|∂G_k/∂x_k|`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-! ### Lower semicontinuity -/

/-- The product of two lower semicontinuous `[0, ∞]`-valued functions is lower semicontinuous. -/
theorem lowerSemicontinuous_mul_ennreal {Y : Type*} [TopologicalSpace Y] {f g : Y → ℝ≥0∞}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun y => f y * g y := by
  rw [lowerSemicontinuous_iff_le_liminf] at hf hg ⊢
  intro y
  exact (mul_le_mul' (hf y) (hg y)).trans ENNReal.le_liminf_mul

/-- A finite product of lower semicontinuous `[0, ∞]`-valued functions is lower
semicontinuous. -/
theorem lowerSemicontinuous_finset_prod {Y ι : Type*} [TopologicalSpace Y] (s : Finset ι)
    {f : ι → Y → ℝ≥0∞} (hf : ∀ i ∈ s, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun y => ∏ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerSemicontinuous_const
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact lowerSemicontinuous_mul_ennreal (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Fatou's lemma, lower semicontinuous form**: if `h(·, y)` is lower semicontinuous for every
`y` and each `h(x, ·)` is measurable, `x ↦ ∫ h(x, y) μ(dy)` is lower semicontinuous. -/
theorem lowerSemicontinuous_lintegral_of_lsc {Z Y : Type*} [TopologicalSpace Z]
    [FirstCountableTopology Z] [MeasurableSpace Y] (μ : Measure Y) {h : Z → Y → ℝ≥0∞}
    (hm : ∀ x, Measurable (h x)) (hl : ∀ y, LowerSemicontinuous fun x => h x y) :
    LowerSemicontinuous fun x => ∫⁻ y, h x y ∂μ := by
  refine lowerSemicontinuous_of_seq fun x z hz => ?_
  calc ∫⁻ y, h x y ∂μ ≤ ∫⁻ y, atTop.liminf (fun n => h (z n) y) ∂μ :=
        lintegral_mono fun y => le_liminf_seq_of_lsc (hl y) hz
    _ ≤ atTop.liminf fun n => ∫⁻ y, h (z n) y ∂μ := lintegral_liminf_le fun n => hm (z n)

/-! ### Product densities -/

/-- Tonelli for a product of functions of separate coordinates:
`∫ ∏ᵢ gᵢ(uᵢ) d(μ ⊗ ⋯ ⊗ μ) = ∏ᵢ ∫ gᵢ dμ`. -/
theorem lintegral_pi_prod {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    ∀ (k : ℕ) (g : Fin k → α → ℝ≥0∞), (∀ i, Measurable (g i)) →
      ∫⁻ u, ∏ i, g i (u i) ∂(Measure.pi fun _ : Fin k => μ) = ∏ i, ∫⁻ w, g i w ∂μ
  | 0, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul, Measure.pi_univ]
  | k + 1, g, hg => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have hfun : (fun u : Fin (k + 1) → α => ∏ i, g i (u i)) =
        (fun p : α × (Fin k → α) => g 0 p.1 * ∏ i : Fin k, g i.succ (p.2 i)) ∘
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0 := by
      funext u
      simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    rw [hfun]
    change ∫⁻ u, (fun p : α × (Fin k → α) => g 0 p.1 * ∏ i : Fin k, g i.succ (p.2 i))
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0 u)
        ∂(Measure.pi fun _ : Fin (k + 1) => μ) = _
    have hm2 : Measurable fun v : Fin k → α => ∏ i : Fin k, g i.succ (v i) :=
      Finset.measurable_prod _ fun i _ => (hg i.succ).comp (measurable_pi_apply i)
    rw [hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p : α × (Fin k → α) => g 0 p.1 * ∏ i : Fin k, g i.succ (p.2 i)),
      lintegral_prod_mul (hg 0).aemeasurable hm2.aemeasurable,
      lintegral_pi_prod μ k (fun i => g i.succ) fun i => hg i.succ, Fin.prod_univ_succ]

/-- The product of `k` copies of `f · μ` is `(f(u₁) ⋯ f(uₖ)) · μ^{⊗k}`. -/
theorem pi_withDensity_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) [SigmaFinite (μ.withDensity f)] (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ.withDensity f) =
      (Measure.pi fun _ : Fin k => μ).withDensity fun u => ∏ i, f (u i) := by
  refine Measure.pi_eq fun s hs => ?_
  have hG : Measurable fun u : Fin k → α => ∏ i, f (u i) :=
    Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hind : (Set.pi univ s).indicator (fun u : Fin k → α => ∏ i, f (u i)) =
      fun u => ∏ i, (s i).indicator f (u i) := by
    funext u
    by_cases hu : u ∈ Set.pi univ s
    · rw [indicator_of_mem hu]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem (hu i (mem_univ i))]
    · rw [indicator_of_notMem hu]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hu
      obtain ⟨i, hi⟩ := hu
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi f)).symm
  rw [hind, lintegral_pi_prod μ k _ fun i => hf.indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

/-! ### The inverse function theorem with parameters -/

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Straightening a submersion** (the inverse function theorem step of MT pp. 149–150): if
`G : X × E → X` is `C¹` at `p₀` and `∂G/∂u (p₀)` is onto, there are a local homeomorphism `e`
of `X × E` near `p₀`, inside any prescribed neighbourhood `V`, and an onto linear map `L` with
`e(x, u) = (x, Ψ₂(x, u))`, `G = L ∘ Ψ₂` on the source of `e`, and `u ↦ Ψ₂(x, u)` differentiable
with Jacobian determinant at most `2` in absolute value. -/
theorem exists_straightening {G : X × E → X} {p₀ : X × E} (hG : ContDiffAt ℝ 1 G p₀)
    (hsurj : Function.Surjective ((fderiv ℝ G p₀).comp (ContinuousLinearMap.inr ℝ X E)))
    {V : Set (X × E)} (hV : V ∈ 𝓝 p₀) :
    ∃ (e : OpenPartialHomeomorph (X × E) (X × E)) (L : E →L[ℝ] X) (J : X × E → E →L[ℝ] E),
      Function.Surjective L ∧ p₀ ∈ e.source ∧ e.source ⊆ V ∧
      (∀ p, (e p).1 = p.1) ∧ (∀ p ∈ e.source, G p = L (e p).2) ∧
      ∀ p ∈ e.source, HasFDerivAt (fun u => (e (p.1, u)).2) (J p) p.2 ∧ |(J p).det| ≤ 2 := by
  set D := fderiv ℝ G p₀ with hD
  set L : E →L[ℝ] X := D.comp (ContinuousLinearMap.inr ℝ X E) with hL
  obtain ⟨g, hg⟩ := (L : E →ₗ[ℝ] X).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hsurj)
  set R : X →L[ℝ] E := ⟨g, g.continuous_of_finiteDimensional⟩ with hR
  have hLR : ∀ y, L (R y) = y := fun y => LinearMap.congr_fun hg y
  set Ψ : X × E → X × E := fun p => (p.1, R (G p) + p.2 - R (L p.2)) with hΨ
  set M : X →L[ℝ] E := R.comp (D.comp (ContinuousLinearMap.inl ℝ X E)) with hM
  set Φf : (X × E) →L[ℝ] (X × E) :=
    (ContinuousLinearMap.fst ℝ X E).prod
      (M.comp (ContinuousLinearMap.fst ℝ X E) + ContinuousLinearMap.snd ℝ X E) with hΦf
  set Φi : (X × E) →L[ℝ] (X × E) :=
    (ContinuousLinearMap.fst ℝ X E).prod
      (ContinuousLinearMap.snd ℝ X E - M.comp (ContinuousLinearMap.fst ℝ X E)) with hΦi
  have h1 : Function.LeftInverse Φi Φf := fun q => by simp [Φf, Φi]
  have h2 : Function.RightInverse Φi Φf := fun q => by simp [Φf, Φi]
  set Φ' : (X × E) ≃L[ℝ] (X × E) := ContinuousLinearEquiv.equivOfInverse Φf Φi h1 h2
  have hGs : HasStrictFDerivAt G D p₀ := hG.hasStrictFDerivAt one_ne_zero
  have hΨs : HasStrictFDerivAt Ψ (Φ' : (X × E) →L[ℝ] (X × E)) p₀ := by
    have hA : HasStrictFDerivAt (fun p : X × E => p.1) (ContinuousLinearMap.fst ℝ X E) p₀ :=
      hasStrictFDerivAt_fst
    have hB : HasStrictFDerivAt (fun p : X × E => R (G p) + p.2 - R (L p.2))
        (R.comp D + ContinuousLinearMap.snd ℝ X E -
          (R.comp L).comp (ContinuousLinearMap.snd ℝ X E)) p₀ :=
      ((R.hasStrictFDerivAt.comp p₀ hGs).add hasStrictFDerivAt_snd).sub
        ((R.comp L).hasStrictFDerivAt.comp p₀ hasStrictFDerivAt_snd)
    refine (hA.prodMk hB).congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    obtain ⟨a, c⟩ := q
    refine Prod.ext ?_ ?_
    · simp [Φ', Φf]
    · have hDac : D (a, c) = D (a, 0) + L c := by
        rw [hL, ContinuousLinearMap.comp_apply, ← map_add]
        simp
      change R (D (a, c)) + c - R (L c) = M a + c
      rw [hDac, map_add, hM]
      change R (D (a, 0)) + R (L c) + c - R (L c) = R (D (a, 0)) + c
      abel
  set e₀ := hΨs.toOpenPartialHomeomorph Ψ
  set J : X × E → E →L[ℝ] E := fun p =>
    R.comp ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ X E)) +
      ContinuousLinearMap.id ℝ E - R.comp L with hJ
  have hJ0 : J p₀ = ContinuousLinearMap.id ℝ E := by
    simp only [hJ, ← hD, ← hL]
    abel
  have hJc : ContinuousAt (fun p => (J p).det) p₀ := by
    refine ContinuousLinearMap.continuous_det.continuousAt.comp ?_
    have hf := hG.continuousAt_fderiv one_ne_zero
    have hc : ContinuousAt (fun p : X × E =>
        R.comp ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ X E))) p₀ :=
      ((ContinuousLinearMap.compL ℝ E X E R).continuous.comp
        ((ContinuousLinearMap.compL ℝ E (X × E) X).flip
          (ContinuousLinearMap.inr ℝ X E)).continuous).continuousAt.comp hf
    exact (hc.add continuousAt_const).sub continuousAt_const
  have hdet : ∀ᶠ p in 𝓝 p₀, |(J p).det| < 2 := by
    have : |(J p₀).det| < 2 := by
      rw [hJ0, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
      norm_num
    exact (continuous_abs.continuousAt.comp hJc).eventually (gt_mem_nhds this)
  have hdiff : ∀ᶠ p in 𝓝 p₀, DifferentiableAt ℝ G p :=
    (hG.eventually (by simp)).mono fun p hp => hp.differentiableAt one_ne_zero
  set V' := interior (V ∩ {p | DifferentiableAt ℝ G p} ∩ {p | |(J p).det| < 2})
  have hV'0 : p₀ ∈ V' :=
    mem_interior_iff_mem_nhds.2 (inter_mem (inter_mem hV hdiff) hdet)
  set e := e₀.restrOpen V' isOpen_interior
  refine ⟨e, L, J, hsurj, ?_, ?_, fun p => rfl, fun p hp => ?_, fun p hp => ⟨?_, ?_⟩⟩
  · exact ⟨hΨs.mem_toOpenPartialHomeomorph_source, hV'0⟩
  · exact fun p hp => (interior_subset hp.2).1.1
  · change G p = L (R (G p) + p.2 - R (L p.2))
    rw [map_sub, map_add, hLR, hLR]
    abel
  · have hd : DifferentiableAt ℝ G (p.1, p.2) := (interior_subset hp.2).1.2
    have h3 := (hd.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2))
    have h4 := ((R.hasFDerivAt.comp p.2 h3).add (hasFDerivAt_id p.2)).sub
      ((R.comp L).hasFDerivAt (x := p.2))
    refine h4.congr_fderiv ?_
    simp only [hJ, Prod.mk.eta]
  · exact (interior_subset hp.2).2.le

variable [MeasurableSpace E] [BorelSpace E]

/-- **The continuous component of a submersion** (MT (7.6)–(7.8), pp. 150–151, and the
multidimensional version used for Proposition 7.1.5): under the hypotheses of
`exists_straightening` and for a lower semicontinuous density `ρ ≥ 0` on `E` with `ρ(u₀) > 0`,
there are an onto `L : E → X` and a jointly lower semicontinuous `K : X × E → [0, ∞]` with
`K(x₀, y₀) > 0` for some `y₀` and, for every `x` and measurable `A ⊆ X`,
`∫ 1_A(L y) K(x, y) μ(dy) ≤ ∫_{(x, u) ∈ V} 1_A(G(x, u)) ρ(u) μ(du)` (`μ` a Haar measure). -/
theorem exists_lsc_minorant (μ : Measure E) [μ.IsAddHaarMeasure] [MeasurableSpace X]
    [BorelSpace X] {G : X × E → X} {p₀ : X × E} (hG : ContDiffAt ℝ 1 G p₀)
    (hsurj : Function.Surjective ((fderiv ℝ G p₀).comp (ContinuousLinearMap.inr ℝ X E)))
    {V : Set (X × E)} (hV : V ∈ 𝓝 p₀) {ρ : E → ℝ≥0∞} (hρ : LowerSemicontinuous ρ)
    (hρ0 : 0 < ρ p₀.2) :
    ∃ (L : E →L[ℝ] X) (K : X × E → ℝ≥0∞), Function.Surjective L ∧ LowerSemicontinuous K ∧
      (∃ y₀, 0 < K (p₀.1, y₀)) ∧
      ∀ x (A : Set X), MeasurableSet A →
        ∫⁻ y, A.indicator 1 (L y) * K (x, y) ∂μ ≤
          ∫⁻ u in {u | (x, u) ∈ V}, A.indicator 1 (G (x, u)) * ρ u ∂μ := by
  obtain ⟨e, L, J, hLs, hp₀, hsV, he1, heG, heJ⟩ := exists_straightening hG hsurj hV
  set K' : X × E → ℝ≥0∞ := e.target.indicator fun q => ρ (e.symm q).2 with hK'
  have hK'l : LowerSemicontinuous K' := by
    intro q t ht
    by_cases hq : q ∈ e.target
    · have ht' : t < ρ (e.symm q).2 := by simpa [hK', indicator_of_mem hq] using ht
      have hc : ContinuousAt (fun q => (e.symm q).2) q :=
        continuous_snd.continuousAt.comp (e.continuousAt_symm hq)
      have h1 := LowerSemicontinuousAt.comp (g := fun q => (e.symm q).2) (x := q) (hρ _) hc t ht'
      filter_upwards [h1, e.open_target.mem_nhds hq] with q' hq' hq't
      simpa [hK', indicator_of_mem hq't] using hq'
    · simp [hK', indicator_of_notMem hq] at ht
  refine ⟨L, fun q => 2⁻¹ * K' q, hLs, lowerSemicontinuous_const_mul hK'l _, ⟨(e p₀).2, ?_⟩,
    fun x A hA => ?_⟩
  · have hq : (p₀.1, (e p₀).2) = e p₀ := by rw [← he1 p₀]
    have hmem : e p₀ ∈ e.target := e.map_source hp₀
    simp only [hK']
    rw [hq, indicator_of_mem hmem, e.left_inv hp₀]
    exact ENNReal.mul_pos (by simp) hρ0.ne'
  · -- the slices of the source and the target over `x`
    set s : Set E := {u | (x, u) ∈ e.source} with hs
    set ψ : E → E := fun u => (e (x, u)).2 with hψ
    have hsm : MeasurableSet s :=
      (e.open_source.preimage (continuous_const.prodMk continuous_id)).measurableSet
    have hex : ∀ u ∈ s, e (x, u) = (x, ψ u) := fun u _ => by
      rw [hψ]; exact Prod.ext (he1 _) rfl
    have hinj : InjOn ψ s := by
      intro u hu v hv huv
      have := e.injOn hu hv (by rw [hex u hu, hex v hv, huv])
      exact (Prod.ext_iff.1 this).2
    have himage : ψ '' s = {y | (x, y) ∈ e.target} := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [mem_ofPred_eq, ← hex u hu]
        exact e.map_source hu
      · intro hy
        have hsrc := e.map_target hy
        have h1 : (e.symm (x, y)).1 = x := by rw [← he1, e.right_inv hy]
        have hp : (x, (e.symm (x, y)).2) = e.symm (x, y) := Prod.ext h1.symm rfl
        refine ⟨(e.symm (x, y)).2, ?_, ?_⟩
        · change (x, (e.symm (x, y)).2) ∈ e.source
          rw [hp]
          exact hsrc
        · change (e (x, (e.symm (x, y)).2)).2 = y
          rw [hp, e.right_inv hy]
    have hderiv : ∀ u ∈ s, HasFDerivWithinAt ψ (J (x, u)) s u := fun u hu =>
      (heJ (x, u) hu).1.hasFDerivWithinAt
    set g : E → ℝ≥0∞ := fun y => A.indicator 1 (L y) * (2⁻¹ * ρ (e.symm (x, y)).2) with hgdef
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hsm hderiv hinj g
    have hlhs : ∫⁻ y, A.indicator 1 (L y) * (2⁻¹ * K' (x, y)) ∂μ = ∫⁻ y in ψ '' s, g y ∂μ := by
      have hmt : MeasurableSet {y : E | (x, y) ∈ e.target} :=
        (e.open_target.preimage (continuous_const.prodMk continuous_id)).measurableSet
      rw [himage, ← lintegral_indicator hmt]
      refine lintegral_congr fun y => ?_
      by_cases hy : (x, y) ∈ e.target
      · have hy' : y ∈ {y | (x, y) ∈ e.target} := hy
        rw [indicator_of_mem hy', hK', indicator_of_mem hy]
      · have hy' : y ∉ {y | (x, y) ∈ e.target} := hy
        rw [indicator_of_notMem hy', hK', indicator_of_notMem hy]
        simp
    rw [hlhs, hcov]
    refine (setLIntegral_mono' hsm fun u hu => ?_).trans
      (lintegral_mono_set (fun u hu => hsV hu))
    have hsymm : e.symm (x, ψ u) = (x, u) := by rw [← hex u hu, e.left_inv hu]
    have hGu : L (ψ u) = G (x, u) := (heG (x, u) hu).symm
    simp only [hgdef, hsymm, hGu]
    have hJ2 : ENNReal.ofReal |(J (x, u)).det| * 2⁻¹ ≤ 1 := by
      have : ENNReal.ofReal |(J (x, u)).det| ≤ 2 := by
        have := ENNReal.ofReal_le_ofReal (heJ (x, u) hu).2
        simpa using this
      calc ENNReal.ofReal |(J (x, u)).det| * 2⁻¹ ≤ 2 * 2⁻¹ := mul_le_mul_left this _
        _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc ENNReal.ofReal |(J (x, u)).det| * (A.indicator 1 (G (x, u)) * (2⁻¹ * ρ u))
        = (ENNReal.ofReal |(J (x, u)).det| * 2⁻¹) * (A.indicator 1 (G (x, u)) * ρ u) := by ring
      _ ≤ 1 * (A.indicator 1 (G (x, u)) * ρ u) := mul_le_mul_left hJ2 _
      _ = A.indicator 1 (G (x, u)) * ρ u := one_mul _

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Uniform reachability** (the step of MT Proposition 7.3.1, p. 158): under the hypotheses of
`exists_straightening` there are an open `B ∋ x₀` and a non-empty open `C ⊆ X` such that every
`y ∈ C` is `G(x, u)` for some `(x, u) ∈ V`, for every `x ∈ B`. -/
theorem exists_uniform_reach {G : X × E → X} {p₀ : X × E} (hG : ContDiffAt ℝ 1 G p₀)
    (hsurj : Function.Surjective ((fderiv ℝ G p₀).comp (ContinuousLinearMap.inr ℝ X E)))
    {V : Set (X × E)} (hV : V ∈ 𝓝 p₀) :
    ∃ B C : Set X, IsOpen B ∧ p₀.1 ∈ B ∧ IsOpen C ∧ C.Nonempty ∧
      ∀ x ∈ B, ∀ y ∈ C, ∃ u, (x, u) ∈ V ∧ G (x, u) = y := by
  obtain ⟨e, L, J, hLs, hp₀, hsV, he1, heG, -⟩ := exists_straightening hG hsurj hV
  have hmem : e p₀ ∈ e.target := e.map_source hp₀
  obtain ⟨B, C', hB, hC', hxB, hyC', hBC⟩ := isOpen_prod_iff.1 e.open_target _ _ hmem
  have hx₀ : p₀.1 ∈ B := by rw [← he1 p₀]; exact hxB
  refine ⟨B, L '' C', hB, hx₀, L.isOpenMap hLs _ hC', ⟨_, mem_image_of_mem L hyC'⟩, ?_⟩
  rintro x hx _ ⟨y', hy', rfl⟩
  have hq : (x, y') ∈ e.target := hBC (mk_mem_prod hx hy')
  have hsrc := e.map_target hq
  have h1 : (e.symm (x, y')).1 = x := by rw [← he1, e.right_inv hq]
  have hp : (x, (e.symm (x, y')).2) = e.symm (x, y') := Prod.ext h1.symm rfl
  refine ⟨(e.symm (x, y')).2, ?_, ?_⟩
  · rw [hp]
    exact hsV hsrc
  · rw [hp, heG _ hsrc, e.right_inv hq]

end MeynTweedie.VUniformErgodicity
