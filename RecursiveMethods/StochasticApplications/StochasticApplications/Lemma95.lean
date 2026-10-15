/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.Theorem94

/-!
# Lemma 9.5: integration preserves continuity, monotonicity and concavity

SLP §9.2, pp. 260–262 and 268–269. The operator `(Mf)(w, z) = ∫ f(w, z′) Q(z, dz′)` (`mop`) on
functions of an endogenous variable `w` and the shock `z`. **Assumption 9.5** asks that `M` map
bounded continuous functions to continuous ones (`PreservesBC`). **Lemma 9.5** proves this in the
book's two cases:

* (a) `Z` countable with all subsets measurable (`lemma_9_5_discrete`: any `Z` with the discrete
  topology whose open sets are measurable; countability is not needed), by dominated convergence;
* (b) `Z` compact and `Q` Feller (`lemma_9_5_compact`): `|Mf(w′, z′) − Mf(w, z)|` is at most
  `sup_{z″} |f(w′, z″) − f(w, z″)| + |Mf(w, z′) − Mf(w, z)|`; the first term vanishes because
  `w ↦ f(w, ·)` is continuous into `C(Z)` with the sup norm (the book's uniform continuity on
  `D × Z`), the second by the Feller property.

The bound `|Mf| ≤ sup |f|` is `abs_mop_le`; preservation of (strict) monotonicity and concavity is
stated for any combination `θ f(w₀, z′) + (1 − θ) f(w₁, z′) ≤ f(w, z′)` (`lemma_9_5_comb`,
`lemma_9_5_comb_strict`, `lemma_9_5_mono`, `lemma_9_5_strictMono`), the strict versions by
Exercises 7.18 and 7.24 (`integral_lt_integral_of_lt`).

**Lemma 9.5′** (`lemma_9_5'`): with `φ` continuous on `D × Z`, where `D` is the projection of the
graph of `Γ` on `X × Y` (Assumption 9.17), `h(x, y, z) = ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is
continuous on `D × Z`: apply Lemma 9.5 to `ψ(u, z′) = f[φ(u, z′), z′]` on `D × Z`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {W Z : Type*} [MeasurableSpace Z]

/-- The Markov operator on functions of `(w, z)`: `(Mf)(w, z) = ∫ f(w, z′) Q(z, dz′)`. -/
noncomputable def mop (Q : Kernel Z Z) (f : W × Z → ℝ) (p : W × Z) : ℝ := ∫ z', f (p.1, z') ∂Q p.2

/-- **Assumption 9.5** (in the form the proofs use): `M` maps the bounded continuous functions on
`W × Z` into continuous functions. -/
def PreservesBC (W : Type*) [TopologicalSpace W] [TopologicalSpace Z] (Q : Kernel Z Z) : Prop :=
  ∀ f : W × Z → ℝ, Continuous f → (∃ B, ∀ p, |f p| ≤ B) → Continuous (mop Q f)

/-- A bounded measurable function is integrable for a finite measure. -/
theorem integrable_of_abs_le {μ : Measure Z} [IsFiniteMeasure μ] {h : Z → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ z, |h z| ≤ B) : Integrable h μ :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)

/-- **Exercises 7.18 and 7.24.** For a probability measure, `f < g` everywhere implies
`∫ f < ∫ g`. -/
theorem integral_lt_integral_of_lt {μ : Measure Z} [IsProbabilityMeasure μ] {f g : Z → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hlt : ∀ z, f z < g z) :
    ∫ z, f z ∂μ < ∫ z, g z ∂μ := by
  have hpos : 0 < ∫ z, (g z - f z) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun z => (sub_pos.2 (hlt z)).le) (hg.sub hf)]
    have : Function.support (fun z => g z - f z) = univ :=
      eq_univ_of_forall fun z => (sub_pos.2 (hlt z)).ne'
    rw [this, measure_univ]
    exact one_pos
  rw [integral_sub hg hf] at hpos
  linarith

variable [TopologicalSpace W] [TopologicalSpace Z] [OpensMeasurableSpace Z]

omit [TopologicalSpace W] [TopologicalSpace Z] [OpensMeasurableSpace Z] in
theorem abs_mop_le (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} {B : ℝ}
    (hB : ∀ p, |f p| ≤ B) (p : W × Z) : |mop Q f p| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := B) (f := fun z' => f (p.1, z'))
    (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hB _)
  rw [mop]
  simpa [Real.norm_eq_abs, measureReal_def] using this

theorem integrable_section (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) (w : W) (z : Z) : Integrable (fun z' => f (w, z')) (Q z) :=
  integrable_of_abs_le (hf.comp (Continuous.prodMk_right w)).measurable fun _ => hB _

/-- **Lemma 9.5 (a).** If `Z` is discrete (with its subsets measurable), `M` maps bounded
continuous functions to continuous functions. -/
theorem lemma_9_5_discrete [FirstCountableTopology W] [DiscreteTopology Z] (Q : Kernel Z Z)
    [IsMarkovKernel Q] : PreservesBC W Q := by
  rintro f hf ⟨B, hB⟩
  refine continuous_prod_of_discrete_right.2 fun z => ?_
  exact continuous_of_dominated (bound := fun _ => B)
    (fun w => (integrable_section Q hf hB w z).aestronglyMeasurable)
    (fun w => Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hB _)
    (integrable_const B) (Eventually.of_forall fun z' => hf.comp (Continuous.prodMk_left z'))

/-- **Lemma 9.5 (b).** If `Z` is compact and `Q` has the Feller property, `M` maps bounded
continuous functions to continuous functions. -/
theorem lemma_9_5_compact [CompactSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (hQ : IsFeller Q) : PreservesBC W Q := by
  rintro f hf ⟨B, hB⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨w, z⟩
  set g : C(W, C(Z, ℝ)) := (ContinuousMap.mk f hf).curry with hgdef
  set k : Z → ℝ := markovOpR Q fun z' => f (w, z') with hkdef
  have hk : Continuous k :=
    hQ _ (hf.comp (Continuous.prodMk_right w)) ⟨B, fun z' => hB _⟩
  have hdist : Tendsto (fun p : W × Z => dist (g p.1) (g w)) (𝓝 (w, z)) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ((g.continuous.tendsto w).comp continuous_fst.continuousAt)
  have hA : Tendsto (fun p : W × Z => mop Q f p - k p.2) (𝓝 (w, z)) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => ?_) hdist
    rw [mop, hkdef, markovOpR, ← integral_sub (integrable_section Q hf hB p.1 p.2)
      (integrable_section Q hf hB w p.2)]
    have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := dist (g p.1) (g w))
      (f := fun z' => f (p.1, z') - f (w, z')) (Eventually.of_forall fun z' => by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist (f := g p.1) (g := g w) z')
    simpa [measureReal_def] using this
  have hB' : Tendsto (fun p : W × Z => k p.2) (𝓝 (w, z)) (𝓝 (k z)) :=
    (hk.tendsto z).comp continuous_snd.continuousAt
  have hsum := hA.add hB'
  rw [zero_add] at hsum
  have heq : (fun p : W × Z => mop Q f p - k p.2 + k p.2) = mop Q f :=
    funext fun p => sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum

/-- **Lemma 9.5 (combinations).** If `θ f(w₀, z′) + (1 − θ) f(w₁, z′) ≤ f(w, z′)` for all `z′`,
then `θ (Mf)(w₀, z) + (1 − θ) (Mf)(w₁, z) ≤ (Mf)(w, z)`: concavity is preserved. -/
theorem lemma_9_5_comb (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) {w₀ w₁ w : W} {θ : ℝ}
    (hle : ∀ z', θ * f (w₀, z') + (1 - θ) * f (w₁, z') ≤ f (w, z')) (z : Z) :
    θ * mop Q f (w₀, z) + (1 - θ) * mop Q f (w₁, z) ≤ mop Q f (w, z) := by
  have h0 := integrable_section Q hf hB w₀ z
  have h1 := integrable_section Q hf hB w₁ z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul θ)
    (h1.const_mul (1 - θ))]
  exact integral_mono ((h0.const_mul θ).add (h1.const_mul (1 - θ)))
    (integrable_section Q hf hB w z) hle

/-- **Lemma 9.5 (strict combinations).** Strict concavity is preserved. -/
theorem lemma_9_5_comb_strict (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B) {w₀ w₁ w : W} {θ : ℝ}
    (hlt : ∀ z', θ * f (w₀, z') + (1 - θ) * f (w₁, z') < f (w, z')) (z : Z) :
    θ * mop Q f (w₀, z) + (1 - θ) * mop Q f (w₁, z) < mop Q f (w, z) := by
  have h0 := integrable_section Q hf hB w₀ z
  have h1 := integrable_section Q hf hB w₁ z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul θ)
    (h1.const_mul (1 - θ))]
  exact integral_lt_integral_of_lt ((h0.const_mul θ).add (h1.const_mul (1 - θ)))
    (integrable_section Q hf hB w z) hlt

/-- **Lemma 9.5 (monotonicity).** If `f(·, z′)` is nondecreasing for every `z′`, so is
`(Mf)(·, z)`. -/
theorem lemma_9_5_mono [Preorder W] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B) (hmono : ∀ z', Monotone fun w => f (w, z'))
    (z : Z) : Monotone fun w => mop Q f (w, z) := fun _ _ hww' =>
  integral_mono (integrable_section Q hf hB _ z) (integrable_section Q hf hB _ z)
    fun z' => hmono z' hww'

/-- **Lemma 9.5 (strict monotonicity).** -/
theorem lemma_9_5_strictMono [Preorder W] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : W × Z → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : ∀ p, |f p| ≤ B)
    (hmono : ∀ z', StrictMono fun w => f (w, z')) (z : Z) :
    StrictMono fun w => mop Q f (w, z) := fun _ _ hww' =>
  integral_lt_integral_of_lt (integrable_section Q hf hB _ z) (integrable_section Q hf hB _ z)
    fun z' => hmono z' hww'

omit [OpensMeasurableSpace Z] in
/-- **Lemma 9.5′.** Let `D ⊆ X × Y` (the projection of the graph of `Γ`), let `φ` be continuous on
`D × Z` (Assumption 9.17), and let `Q` satisfy Assumption 9.5 on `D × Z`. For bounded continuous
`f` on `X × Z`, `h(x, y, z) = ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on `D × Z`. -/
theorem lemma_9_5' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (D : Set (X × Y))
    {φ : X × Y × Z → X} (hφ : ContinuousOn (fun q : (X × Y) × Z => φ (q.1.1, q.1.2, q.2))
      (D ×ˢ univ)) (Q : Kernel Z Z) (hQ : PreservesBC D Q) {f : X × Z → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) :
    ContinuousOn (fun q : (X × Y) × Z => ∫ z', f (φ (q.1.1, q.1.2, z'), z') ∂Q q.2)
      (D ×ˢ univ) := by
  set ψ : D × Z → ℝ := fun q => f (φ (q.1.1.1, q.1.1.2, q.2), q.2) with hψdef
  have hφ' : Continuous fun q : D × Z => φ (q.1.1.1, q.1.1.2, q.2) := by
    refine hφ.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun q => ⟨q.1.2, mem_univ _⟩
  have hψ : Continuous ψ := hf.comp (hφ'.prodMk continuous_snd)
  have hM := hQ ψ hψ ⟨B, fun _ => hB _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous fun q : (D ×ˢ (univ : Set Z)) => ((⟨q.1.1, q.2.1⟩ : D), q.1.2) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact (hM.comp hmap : _)

end StokeyLucasPrescott.StochasticApplications
