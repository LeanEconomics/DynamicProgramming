/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Contraction operators of the form `(Tf)(x) = ∫ G(x, x', f(x')) π(x, dx')`

SLP §17.2, pp. 508–512: the abstract operator (1), `(Tf)(x) = ∫ G(x, x', f(x')) π(x, dx')`, on
the space `F = olgF X D` of bounded continuous `f : X → D`, and its logarithmic version (3),
`(T̂g)(x) = ln ∫ G(x, x', e^{g(x')}) π(x, dx')`, on `F̂ = olgF X D̂`, `D̂ = ln D`. The Feller
property is `IsFellerKernel`; the hypotheses of Exercise 17.2a are bundled in `OLGOperatorHyp`.

* **Exercise 17.2a**, corrected (`ex_17_2a`, p. 509): for **compact** `X`, `Tf` is continuous with
  values in `D`; `olgTF : F → F`.
* **Exercise 17.2b** (`ex_17_2b`, p. 509): `F` is complete when `D` is closed.
* **Lemma 17.1** (`lemma_17_1`, p. 509): if `|G₃| ≤ β < 1`, `T` is a contraction of modulus `β`
  on `F` (`olgTF_lipschitz`), with a unique fixed point and `‖Tⁿf₀ − f*‖ ≤ βⁿ‖f₀ − f*‖`
  (Mathlib's `ContractingWith.fixedPoint`).
* **Exercise 17.4a**, corrected (`ex_17_4a`, p. 511), `olgThatF : F̂ → F̂`; **Exercise 17.4b**
  (`ex_17_4b`): `F̂` is complete. `olgDhat_eq`: `D̂ = exp⁻¹(D)` for `D ⊆ ℝ₊₊`, so `D̂` is closed
  and convex when `D` is (`olgDhat_isClosed`, `olgDhat_convex`).
* **Lemma 17.2** (`lemma_17_2`, p. 511): if `|y G₃/G| ≤ β < 1`, `T̂` is a contraction of modulus
  `β` on `F̂` (`olgThatF_lipschitz`); `lemma_17_2_fixedPoint` restates the conclusion for `T`:
  exactly one fixed point among bounded continuous `f : X → D`. `olgOpThat_log`:
  `T̂[ln f] = ln(Tf)` (p. 512).

**Correction (Exercises 17.2a and 17.4a).** As stated (general metric `X`, `G` merely
continuous) `T` need not map `F` into `F`, since `Tf` need not be bounded; the manual's "because
`X` is bounded" is not a hypothesis and would not suffice. Counterexamples:
`ex_17_2a_counterexample` (`X = D = ℝ`, `G = x`, `π(x, ·) = δ_x`, `Tf(x) = x`),
`ex_17_2a_counterexample_bounded` (`X = (0, 1]`, `G = 1/x`, `Tf(x) = 1/x`) and
`ex_17_4a_counterexample` (`X = ℝ`, `D = [1, ∞)`, `G = e^{|x|}`, `T̂0(x) = |x|`). The corrected
statements assume `X` compact, as in all of the book's applications; continuity of `Tf` then
follows from the uniform continuity of `G(·, ·, f(·))` on `X × X` and the Feller property.

**Remarks.** Lemmas 17.1–17.2 only need `G(x, x', ·)` differentiable within `D` (continuity of
`G₃` is not used). In the proof of Lemma 17.2 the bound is `β sup |g − h|`, not
`β sup (g − h)` (the book's typo); the weighted-average step is replaced by the equivalent
pointwise inequality `G(e^{g}) ≤ e^{β‖g − h‖} G(e^{h})`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-! ### The setting -/

/-- The **Feller property** of a transition function (SLP §8.1): `x ↦ ∫ f(x') π(x, dx')` is
continuous for every bounded continuous `f`. -/
def IsFellerKernel {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (κ : Kernel X X) :
    Prop :=
  ∀ f : X →ᵇ ℝ, Continuous fun x => ∫ y, f y ∂κ x

/-- The operator of §17.2 (1), `(Tf)(x) = ∫ G(x, x', f(x')) π(x, dx')`. -/
noncomputable def olgOpT {X : Type*} [MeasurableSpace X] (G : X → X → ℝ → ℝ) (κ : Kernel X X)
    (f : X → ℝ) (x : X) : ℝ :=
  ∫ x', G x x' (f x') ∂κ x

/-- The space `F` of bounded continuous functions `f : X → D`, with the sup-norm metric. -/
def olgF (X : Type*) [TopologicalSpace X] (D : Set ℝ) : Set (X →ᵇ ℝ) :=
  {f | ∀ x, f x ∈ D}

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] in
/-- The hypotheses of Exercise 17.2a (p. 509): `D` convex, `G : X × X × D → D` continuous, `π`
Feller. -/
structure OLGOperatorHyp (D : Set ℝ) (G : X → X → ℝ → ℝ) (κ : Kernel X X) : Prop where
  convex : Convex ℝ D
  cont : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) {p | p.2.2 ∈ D}
  mapsTo : ∀ x x', ∀ y ∈ D, G x x' y ∈ D
  feller : IsFellerKernel κ

/-- The identity (Dirac) transition function `π(x, ·) = δ_x` is Feller. -/
theorem isFellerKernel_deterministic_id {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSingletonClass X] :
    IsFellerKernel (Kernel.deterministic (id : X → X) measurable_id) := fun f => by
  simp only [Kernel.deterministic_apply, id, integral_dirac]
  exact f.continuous

/-! ### Exercise 17.2 (a): the book's statement is false -/

/-- **Correction (Exercise 17.2a), unbounded `X`.** With `X = D = ℝ`, `G(x, x', y) = x`
(continuous) and the Feller kernel `π(x, ·) = δ_x`, `(Tf)(x) = x` is unbounded, so `T` does not
map `F = C(ℝ)` into `F`. -/
theorem ex_17_2a_counterexample :
    IsFellerKernel (Kernel.deterministic (id : ℝ → ℝ) measurable_id) ∧
      Continuous (fun p : ℝ × ℝ × ℝ => p.1) ∧
      ¬ ∀ f : ℝ →ᵇ ℝ, ∃ g : ℝ →ᵇ ℝ, ∀ x,
        g x = olgOpT (fun x _ _ => x) (Kernel.deterministic id measurable_id) f x := by
  refine ⟨isFellerKernel_deterministic_id, continuous_fst, fun h => ?_⟩
  obtain ⟨g, hg⟩ := h 0
  have hT : ∀ x, olgOpT (fun x _ _ => x) (Kernel.deterministic id measurable_id)
      (0 : ℝ →ᵇ ℝ) x = x := fun x => by
    simp [olgOpT, Kernel.deterministic_apply]
  have h1 := g.norm_coe_le_norm (‖g‖ + 1)
  rw [hg, hT, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  linarith

/-- **Correction (Exercise 17.2a), bounded `X`.** A bounded state space does not help (contrary
to the manual's "X is bounded"): with `X = (0, 1]`, `D = ℝ`, `G(x, x', y) = 1/x` and
`π(x, ·) = δ_x`, `(Tf)(x) = 1/x` is unbounded. -/
theorem ex_17_2a_counterexample_bounded :
    IsFellerKernel (Kernel.deterministic (id : Ioc (0 : ℝ) 1 → Ioc (0 : ℝ) 1) measurable_id) ∧
      Continuous (fun p : Ioc (0 : ℝ) 1 × Ioc (0 : ℝ) 1 × ℝ => 1 / p.1.1) ∧
      ¬ ∀ f : Ioc (0 : ℝ) 1 →ᵇ ℝ, ∃ g : Ioc (0 : ℝ) 1 →ᵇ ℝ, ∀ x,
        g x = olgOpT (fun x _ _ => 1 / x.1) (Kernel.deterministic id measurable_id) f x := by
  refine ⟨isFellerKernel_deterministic_id, ?_, fun h => ?_⟩
  · refine continuous_const.div (continuous_subtype_val.comp continuous_fst) fun p => ?_
    exact p.1.2.1.ne'
  obtain ⟨g, hg⟩ := h 0
  have hT : ∀ x, olgOpT (fun x _ _ => 1 / x.1) (Kernel.deterministic id measurable_id)
      (0 : Ioc (0 : ℝ) 1 →ᵇ ℝ) x = 1 / x.1 := fun x => by
    simp [olgOpT, Kernel.deterministic_apply]
  have hpos : 0 < ‖g‖ + 2 := by positivity
  have hx : 1 / (‖g‖ + 2) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hpos).2 (by linarith [norm_nonneg g])⟩
  have h1 := g.norm_coe_le_norm ⟨_, hx⟩
  rw [hg, hT, one_div_one_div, Real.norm_eq_abs, abs_of_pos hpos] at h1
  linarith

/-! ### Exercise 17.2 (a), corrected: compact `X` -/

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {D : Set ℝ} {G : X → X → ℝ → ℝ} {κ : Kernel X X}

omit [BorelSpace X] in
/-- The integrand `(x, x') ↦ G(x, x', f(x'))` is continuous. -/
theorem continuous_olgIntegrand (hyp : OLGOperatorHyp D G κ) {f : X → ℝ} (hfc : Continuous f)
    (hf : ∀ x, f x ∈ D) : Continuous fun p : X × X => G p.1 p.2 (f p.2) :=
  hyp.cont.comp_continuous (continuous_fst.prodMk (continuous_snd.prodMk (hfc.comp continuous_snd)))
    fun p => hf p.2

/-- The slice `x' ↦ G(x, x', f(x'))` as a bounded continuous function (compact `X`). -/
noncomputable def olgSection [CompactSpace X] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) (x : X) : X →ᵇ ℝ :=
  mkOfCompact ⟨fun x' => G x x' (f x'),
    (continuous_olgIntegrand hyp hfc hf).comp (continuous_const.prodMk continuous_id)⟩

omit [BorelSpace X] in
/-- Evaluation of `olgSection`. -/
theorem olgSection_apply [CompactSpace X] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) (x x' : X) :
    olgSection hyp hfc hf x x' = G x x' (f x') :=
  rfl

/-- The integrand `x' ↦ G(x, x', f(x'))` is integrable for every finite measure. -/
theorem integrable_olgIntegrand [CompactSpace X] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) (x : X) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (fun x' => G x x' (f x')) μ :=
  (olgSection hyp hfc hf x).integrable μ

/-- **Exercise 17.2a, corrected** (p. 509). If `X` is a compact metric space, `D ⊆ ℝ` is
convex, `G : X × X × D → D` is continuous and `π` is Feller, then for every continuous
`f : X → D` the function `Tf` is continuous (hence bounded) with values in `D`. Continuity uses
the uniform continuity of `G(·, ·, f(·))` on `X × X` together with the Feller property;
`Tf(x) ∈ D` because `Tf(x)` lies between the minimum and maximum of `x' ↦ G(x, x', f(x'))`. -/
theorem ex_17_2a [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) :
    Continuous (olgOpT G κ f) ∧ ∀ x, olgOpT G κ f x ∈ D := by
  have hg := continuous_olgIntegrand hyp hfc hf
  set gx := olgSection hyp hfc hf with hgxdef
  have hT : ∀ x, olgOpT G κ f x = ∫ x', gx x x' ∂κ x := fun _ => rfl
  constructor
  · rw [continuous_iff_continuousAt]
    intro x₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous hg) (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1
      ((hyp.feller (gx x₀)).continuousAt (x := x₀)) (ε / 2) (half_pos hε)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩
    have e : olgOpT G κ f x - olgOpT G κ f x₀ = ∫ x', (gx x x' - gx x₀ x') ∂κ x +
        (∫ x', gx x₀ x' ∂κ x - ∫ x', gx x₀ x' ∂κ x₀) := by
      rw [hT, hT, integral_sub ((gx x).integrable _) ((gx x₀).integrable _)]
      ring
    have b1 : ‖∫ x', (gx x x' - gx x₀ x') ∂κ x‖ ≤ ε / 2 := by
      have := norm_integral_le_of_norm_le_const (μ := κ x) (C := ε / 2)
        (f := fun x' => gx x x' - gx x₀ x') (ae_of_all _ fun x' => by
          have h := h₁ (a := (x, x')) (b := (x₀, x')) (by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
            exact hx.trans_le (min_le_left _ _))
          rw [Real.dist_eq] at h
          rw [Real.norm_eq_abs]
          exact h.le)
      simpa using this
    have b2 := h₂ (hx.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at b2 ⊢
    rw [e]
    rw [Real.norm_eq_abs] at b1
    calc |∫ x', (gx x x' - gx x₀ x') ∂κ x + (∫ x', gx x₀ x' ∂κ x - ∫ x', gx x₀ x' ∂κ x₀)|
        ≤ |∫ x', (gx x x' - gx x₀ x') ∂κ x| +
          |∫ x', gx x₀ x' ∂κ x - ∫ x', gx x₀ x' ∂κ x₀| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt b1 b2
      _ = ε := add_halves ε
  · intro x
    have hne : (univ : Set X).Nonempty := ⟨x, mem_univ x⟩
    obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne (gx x).continuous.continuousOn
    obtain ⟨M, -, hM⟩ := isCompact_univ.exists_isMaxOn hne (gx x).continuous.continuousOn
    have hlow : gx x m ≤ ∫ x', gx x x' ∂κ x := by
      have := integral_mono (integrable_const (gx x m)) ((gx x).integrable (κ x))
        (fun x' => isMinOn_iff.1 hm x' (mem_univ x'))
      simpa using this
    have hup : ∫ x', gx x x' ∂κ x ≤ gx x M := by
      have := integral_mono ((gx x).integrable (κ x)) (integrable_const (gx x M))
        (fun x' => isMaxOn_iff.1 hM x' (mem_univ x'))
      simpa using this
    rw [hT]
    exact hyp.convex.ordConnected.out (hyp.mapsTo _ _ _ (hf m)) (hyp.mapsTo _ _ _ (hf M))
      ⟨hlow, hup⟩

/-- The operator `T : F → F` of (1), for compact `X` (Exercise 17.2a). -/
noncomputable def olgTF [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (f : olgF X D) : olgF X D :=
  ⟨mkOfCompact ⟨olgOpT G κ f.1, (ex_17_2a hyp f.1.continuous f.2).1⟩,
    (ex_17_2a hyp f.1.continuous f.2).2⟩

/-- Evaluation of `olgTF`. -/
theorem olgTF_apply [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (f : olgF X D) (x : X) : (olgTF hyp f).1 x = olgOpT G κ f.1 x :=
  rfl

/-! ### Exercise 17.2 (b) -/

/-- `F` is closed in `C(X)` when `D` is closed. -/
theorem isClosed_olgF {Y : Type*} [TopologicalSpace Y] (hD : IsClosed D) :
    IsClosed (olgF Y D) := by
  have : olgF Y D = ⋂ y, (fun f : Y →ᵇ ℝ => f y) ⁻¹' D := by
    ext f; simp [olgF]
  rw [this]
  exact isClosed_iInter fun y => hD.preimage (continuous_eval_const y)

/-- **Exercise 17.2b** (p. 509). If `D` is closed, `F` with the sup norm is complete. -/
theorem ex_17_2b {Y : Type*} [TopologicalSpace Y] (hD : IsClosed D) :
    CompleteSpace (olgF Y D) :=
  (isClosed_olgF hD).isComplete.completeSpace_coe

/-! ### Lemma 17.1 -/

/-- Under (2), `T` is Lipschitz with constant `β` on `F`. -/
theorem olgTF_lipschitz [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    {G3 : X → X → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |G3 x x' y| ≤ β) :
    LipschitzWith β.toNNReal (olgTF hyp) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  simp only [Subtype.dist_eq]
  rw [Real.coe_toNNReal β hβ0, BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)]
  intro x
  rw [olgTF_apply, olgTF_apply, Real.dist_eq, olgOpT, olgOpT,
    ← integral_sub (integrable_olgIntegrand hyp f.1.continuous f.2 x _)
      (integrable_olgIntegrand hyp g.1.continuous g.2 x _)]
  have hlip : ∀ x', ‖G x x' (f.1 x') - G x x' (g.1 x')‖ ≤ β * dist f.1 g.1 := fun x' => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hG3 x x')
      (fun y hy => by rw [Real.norm_eq_abs]; exact hbound x x' y hy) hyp.convex (g.2 x') (f.2 x')
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs]
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hβ0)
    rw [← Real.dist_eq]
    exact dist_coe_le_dist x'
  have := norm_integral_le_of_norm_le_const (μ := κ x) (ae_of_all _ hlip)
  simpa using this

/-- **Lemma 17.1** (p. 509). Let `X` be compact (see the correction to Exercise 17.2a), `D`
closed, convex and nonempty, `G : X × X × D → D` continuous, `π` Feller, and suppose
`G(x, x', ·)` is differentiable on `D` with `|G₃| ≤ β < 1` (2). Then `T` has a unique fixed
point `f* ∈ F`, and `‖Tⁿ f₀ − f*‖ ≤ βⁿ ‖f₀ − f*‖`. (Continuity of `G₃` is not needed.) -/
theorem lemma_17_1 [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDc : IsClosed D) (hDne : D.Nonempty) {G3 : X → X → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |G3 x x' y| ≤ β) :
    ∃ fstar : olgF X D, olgTF hyp fstar = fstar ∧
      (∀ f : olgF X D, olgTF hyp f = f → f = fstar) ∧
      ∀ (f₀ : olgF X D) (n : ℕ), dist ((olgTF hyp)^[n] f₀) fstar ≤ β ^ n * dist f₀ fstar := by
  have : CompleteSpace (olgF X D) := ex_17_2b hDc
  obtain ⟨y₀, hy₀⟩ := hDne
  have : Nonempty (olgF X D) := ⟨⟨const X y₀, fun _ => hy₀⟩⟩
  have hK : ContractingWith β.toNNReal (olgTF hyp) :=
    ⟨Real.toNNReal_lt_one.2 hβ1, olgTF_lipschitz hyp hβ0 hG3 hbound⟩
  refine ⟨ContractingWith.fixedPoint _ hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun f hf => ContractingWith.fixedPoint_unique hK hf, fun f₀ n => ?_⟩
  have h1 := (hK.2.iterate n).dist_le_mul f₀ (ContractingWith.fixedPoint _ hK)
  rw [((ContractingWith.fixedPoint_isFixedPt hK).iterate n).eq, NNReal.coe_pow,
    Real.coe_toNNReal β hβ0] at h1
  exact h1

/-! ### The logarithmic operator: Exercise 17.4 -/

/-- `D̂ = ln D` (p. 510). -/
def olgDhat (D : Set ℝ) : Set ℝ := Real.log '' D

/-- For `D ⊆ ℝ₊₊`, `D̂ = exp⁻¹(D)`. -/
theorem olgDhat_eq (hDpos : D ⊆ Ioi 0) : olgDhat D = Real.exp ⁻¹' D := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    simp only [mem_preimage, Real.exp_log (hDpos hd)]
    exact hd
  · intro hz
    exact ⟨Real.exp z, hz, Real.log_exp z⟩

/-- `e^z ∈ D` for `z ∈ D̂`. -/
theorem exp_mem_of_mem_olgDhat (hDpos : D ⊆ Ioi 0) {z : ℝ} (hz : z ∈ olgDhat D) :
    Real.exp z ∈ D := by
  rw [olgDhat_eq hDpos] at hz
  exact hz

/-- `D̂` is closed when `D ⊆ ℝ₊₊` is closed. -/
theorem olgDhat_isClosed (hD : IsClosed D) (hDpos : D ⊆ Ioi 0) : IsClosed (olgDhat D) := by
  rw [olgDhat_eq hDpos]
  exact hD.preimage Real.continuous_exp

/-- `D̂` is convex when `D ⊆ ℝ₊₊` is convex. -/
theorem olgDhat_convex (hD : Convex ℝ D) (hDpos : D ⊆ Ioi 0) : Convex ℝ (olgDhat D) := by
  rw [olgDhat_eq hDpos]
  refine Set.OrdConnected.convex ⟨fun a ha b hb z hz => ?_⟩
  exact hD.ordConnected.out ha hb ⟨Real.exp_le_exp.2 hz.1, Real.exp_le_exp.2 hz.2⟩

/-- The logarithmic operator (3), `(T̂g)(x) = ln ∫ G(x, x', e^{g(x')}) π(x, dx')`. -/
noncomputable def olgOpThat {Y : Type*} [MeasurableSpace Y] (G : Y → Y → ℝ → ℝ)
    (κ : Kernel Y Y) (g : Y → ℝ) (x : Y) : ℝ :=
  Real.log (olgOpT G κ (fun x' => Real.exp (g x')) x)

/-- `T̂[ln f] = ln (Tf)` for `f > 0` (p. 512). -/
theorem olgOpThat_log {Y : Type*} [MeasurableSpace Y] (G : Y → Y → ℝ → ℝ) (κ : Kernel Y Y)
    {f : Y → ℝ} (hf : ∀ x, 0 < f x) (x : Y) :
    olgOpThat G κ (fun x' => Real.log (f x')) x = Real.log (olgOpT G κ f x) := by
  simp only [olgOpThat, Real.exp_log (hf _)]

/-- **Correction (Exercise 17.4a).** The same gap as in Exercise 17.2a: with `X = ℝ`,
`D = [1, ∞)` (closed, convex, `⊆ ℝ₊₊`), `G(x, x', y) = e^{|x|}` (continuous, `D`-valued) and
`π(x, ·) = δ_x`, the function `g = 0 ∈ F̂` has `T̂g(x) = |x|`, which is unbounded. -/
theorem ex_17_4a_counterexample :
    IsFellerKernel (Kernel.deterministic (id : ℝ → ℝ) measurable_id) ∧
      Continuous (fun p : ℝ × ℝ × ℝ => Real.exp |p.1|) ∧
      (∀ x : ℝ, Real.exp |x| ∈ Ici (1 : ℝ)) ∧ (0 : ℝ) ∈ olgDhat (Ici 1) ∧
      ¬ ∃ g : ℝ →ᵇ ℝ, ∀ x, g x = olgOpThat (fun x _ _ => Real.exp |x|)
        (Kernel.deterministic id measurable_id) (fun _ => 0) x := by
  refine ⟨isFellerKernel_deterministic_id, by fun_prop, fun x => ?_, ⟨1, mem_Ici.2 le_rfl,
    Real.log_one⟩, fun ⟨g, hg⟩ => ?_⟩
  · exact mem_Ici.2 (Real.one_le_exp (abs_nonneg x))
  have hT : ∀ x, olgOpThat (fun x _ _ => Real.exp |x|) (Kernel.deterministic id measurable_id)
      (fun _ => 0) x = |x| := fun x => by
    simp [olgOpThat, olgOpT, Kernel.deterministic_apply]
  have h1 := g.norm_coe_le_norm (‖g‖ + 1)
  rw [hg, hT, Real.norm_eq_abs, abs_abs, abs_of_pos (by positivity)] at h1
  linarith

/-- **Exercise 17.4a, corrected** (p. 511): for compact `X` and `D ⊆ ℝ₊₊`, `T̂g` is continuous
with values in `D̂` for every continuous `g : X → D̂`. -/
theorem ex_17_4a [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) {g : X → ℝ} (hgc : Continuous g) (hg : ∀ x, g x ∈ olgDhat D) :
    Continuous (olgOpThat G κ g) ∧ ∀ x, olgOpThat G κ g x ∈ olgDhat D := by
  have hf : ∀ x, Real.exp (g x) ∈ D := fun x => exp_mem_of_mem_olgDhat hDpos (hg x)
  obtain ⟨hc, hD⟩ := ex_17_2a hyp (Real.continuous_exp.comp hgc) hf
  exact ⟨hc.log fun x => (hDpos (hD x)).ne', fun x => ⟨_, hD x, rfl⟩⟩

/-- The operator `T̂ : F̂ → F̂` (Exercise 17.4a), for compact `X`. -/
noncomputable def olgThatF [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) (g : olgF X (olgDhat D)) : olgF X (olgDhat D) :=
  ⟨mkOfCompact ⟨olgOpThat G κ g.1, (ex_17_4a hyp hDpos g.1.continuous g.2).1⟩,
    (ex_17_4a hyp hDpos g.1.continuous g.2).2⟩

/-- Evaluation of `olgThatF`. -/
theorem olgThatF_apply [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) (g : olgF X (olgDhat D)) (x : X) :
    (olgThatF hyp hDpos g).1 x = olgOpThat G κ g.1 x :=
  rfl

/-- **Exercise 17.4b** (p. 511). If `D ⊆ ℝ₊₊` is closed, `F̂` is complete. -/
theorem ex_17_4b {Y : Type*} [TopologicalSpace Y] (hD : IsClosed D) (hDpos : D ⊆ Ioi 0) :
    CompleteSpace (olgF Y (olgDhat D)) :=
  ex_17_2b (olgDhat_isClosed hD hDpos)

/-! ### Lemma 17.2 -/

omit [BorelSpace X] in
/-- Under (4), `z ↦ ln G(x, x', e^z)` is `β`-Lipschitz on `D̂` (mean value theorem). -/
theorem abs_log_G_sub_le (hyp : OLGOperatorHyp D G κ) (hDpos : D ⊆ Ioi 0)
    {G3 : X → X → ℝ → ℝ} {β : ℝ}
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) (x x' : X) {z w : ℝ}
    (hz : z ∈ olgDhat D) (hw : w ∈ olgDhat D) :
    |Real.log (G x x' (Real.exp z)) - Real.log (G x x' (Real.exp w))| ≤ β * |z - w| := by
  have hmaps : MapsTo Real.exp (olgDhat D) D := fun _ hu => exp_mem_of_mem_olgDhat hDpos hu
  have hder : ∀ u ∈ olgDhat D, HasDerivWithinAt (fun u => Real.log (G x x' (Real.exp u)))
      (G3 x x' (Real.exp u) * Real.exp u / G x x' (Real.exp u)) (olgDhat D) u := fun u hu => by
    have h1 := (hG3 x x' (Real.exp u) (hmaps hu)).comp u
      (Real.hasDerivAt_exp u).hasDerivWithinAt hmaps
    exact h1.log (hDpos (hyp.mapsTo x x' _ (hmaps hu))).ne'
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder
    (fun u hu => by
      rw [Real.norm_eq_abs, mul_comm]
      exact hbound x x' _ (hmaps hu))
    (olgDhat_convex hyp.convex hDpos) hw hz
  simpa [Real.norm_eq_abs] using this

/-- Under (4), `T̂` is Lipschitz with constant `β` on `F̂`. The book's weighted-average step is
replaced by the equivalent pointwise bound `G(e^{g}) ≤ e^{β‖g−h‖} G(e^{h})`. -/
theorem olgThatF_lipschitz [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) {G3 : X → X → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) :
    LipschitzWith β.toNNReal (olgThatF hyp hDpos) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  simp only [Subtype.dist_eq]
  rw [Real.coe_toNNReal β hβ0, BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)]
  intro x
  set d := dist g.1 h.1
  have hmem : ∀ (k : olgF X (olgDhat D)) x', Real.exp (k.1 x') ∈ D := fun k x' =>
    exp_mem_of_mem_olgDhat hDpos (k.2 x')
  set A : X → ℝ := fun x' => G x x' (Real.exp (g.1 x'))
  set B : X → ℝ := fun x' => G x x' (Real.exp (h.1 x'))
  have hA : ∀ x', 0 < A x' := fun x' => hDpos (hyp.mapsTo _ _ _ (hmem g x'))
  have hB : ∀ x', 0 < B x' := fun x' => hDpos (hyp.mapsTo _ _ _ (hmem h x'))
  have hlog : ∀ x', |Real.log (A x') - Real.log (B x')| ≤ β * d := fun x' =>
    (abs_log_G_sub_le hyp hDpos hG3 hbound x x' (g.2 x') (h.2 x')).trans
      (mul_le_mul_of_nonneg_left (by rw [← Real.dist_eq]; exact dist_coe_le_dist x') hβ0)
  have hAB : ∀ x', A x' ≤ Real.exp (β * d) * B x' := fun x' => by
    have := (abs_sub_le_iff.1 (hlog x')).1
    rw [← Real.exp_log (hA x'), ← Real.exp_log (hB x'), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hBA : ∀ x', B x' ≤ Real.exp (β * d) * A x' := fun x' => by
    have := (abs_sub_le_iff.1 (hlog x')).2
    rw [← Real.exp_log (hA x'), ← Real.exp_log (hB x'), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have iA : Integrable A (κ x) :=
    integrable_olgIntegrand hyp (Real.continuous_exp.comp g.1.continuous) (hmem g) x _
  have iB : Integrable B (κ x) :=
    integrable_olgIntegrand hyp (Real.continuous_exp.comp h.1.continuous) (hmem h) x _
  have pA : 0 < ∫ x', A x' ∂κ x := by
    refine (integral_pos_iff_support_of_nonneg (fun x' => (hA x').le) iA).2 ?_
    rw [show Function.support A = univ from
      eq_univ_of_forall fun x' => Function.mem_support.2 (hA x').ne', measure_univ]
    exact one_pos
  have pB : 0 < ∫ x', B x' ∂κ x := by
    refine (integral_pos_iff_support_of_nonneg (fun x' => (hB x').le) iB).2 ?_
    rw [show Function.support B = univ from
      eq_univ_of_forall fun x' => Function.mem_support.2 (hB x').ne', measure_univ]
    exact one_pos
  have IAB : ∫ x', A x' ∂κ x ≤ Real.exp (β * d) * ∫ x', B x' ∂κ x := by
    rw [← integral_const_mul]
    exact integral_mono iA (iB.const_mul _) hAB
  have IBA : ∫ x', B x' ∂κ x ≤ Real.exp (β * d) * ∫ x', A x' ∂κ x := by
    rw [← integral_const_mul]
    exact integral_mono iB (iA.const_mul _) hBA
  have L1 := Real.log_le_log pA IAB
  have L2 := Real.log_le_log pB IBA
  rw [Real.log_mul (Real.exp_pos _).ne' pB.ne', Real.log_exp] at L1
  rw [Real.log_mul (Real.exp_pos _).ne' pA.ne', Real.log_exp] at L2
  rw [olgThatF_apply, olgThatF_apply, Real.dist_eq, abs_sub_le_iff]
  exact ⟨by simp only [olgOpThat, olgOpT]; linarith, by simp only [olgOpThat, olgOpT]; linarith⟩

/-- **Lemma 17.2** (p. 511). Let `X` be compact, `D ⊆ ℝ₊₊` closed, convex and nonempty,
`G : X × X × D → D` continuous, `π` Feller, `G(x, x', ·)` differentiable on `D`, and
`|y G₃(x, x', y)/G(x, x', y)| ≤ β < 1` (4). Then `T̂` has a unique fixed point `g* ∈ F̂` and
`‖T̂ⁿ g₀ − g*‖ ≤ βⁿ ‖g₀ − g*‖`. -/
theorem lemma_17_2 [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDc : IsClosed D) (hDne : D.Nonempty) (hDpos : D ⊆ Ioi 0) {G3 : X → X → ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) :
    ∃ gstar : olgF X (olgDhat D), olgThatF hyp hDpos gstar = gstar ∧
      (∀ g : olgF X (olgDhat D), olgThatF hyp hDpos g = g → g = gstar) ∧
      ∀ (g₀ : olgF X (olgDhat D)) (n : ℕ),
        dist ((olgThatF hyp hDpos)^[n] g₀) gstar ≤ β ^ n * dist g₀ gstar := by
  have : CompleteSpace (olgF X (olgDhat D)) := ex_17_4b hDc hDpos
  obtain ⟨y₀, hy₀⟩ := hDne
  have : Nonempty (olgF X (olgDhat D)) := ⟨⟨const X (Real.log y₀), fun _ => ⟨y₀, hy₀, rfl⟩⟩⟩
  have hK : ContractingWith β.toNNReal (olgThatF hyp hDpos) :=
    ⟨Real.toNNReal_lt_one.2 hβ1, olgThatF_lipschitz hyp hDpos hβ0 hG3 hbound⟩
  refine ⟨ContractingWith.fixedPoint _ hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun g hg => ContractingWith.fixedPoint_unique hK hg, fun g₀ n => ?_⟩
  have h1 := (hK.2.iterate n).dist_le_mul g₀ (ContractingWith.fixedPoint _ hK)
  rw [((ContractingWith.fixedPoint_isFixedPt hK).iterate n).eq, NNReal.coe_pow,
    Real.coe_toNNReal β hβ0] at h1
  exact h1

/-- **Lemma 17.2, in terms of `T`.** Under the hypotheses of Lemma 17.2, `T` has exactly one
fixed point among the bounded continuous `f : X → D`: `f* = e^{g*}` (`f` is a fixed point of
`T` iff `ln f` is a fixed point of `T̂`). -/
theorem lemma_17_2_fixedPoint [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDc : IsClosed D) (hDne : D.Nonempty) (hDpos : D ⊆ Ioi 0) {G3 : X → X → ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) :
    ∃! f : X →ᵇ ℝ, (∀ x, f x ∈ D) ∧ ∀ x, f x = olgOpT G κ f x := by
  obtain ⟨gs, hfix, huniq, -⟩ := lemma_17_2 hyp hDc hDne hDpos hβ0 hβ1 hG3 hbound
  have hmem : ∀ x, Real.exp (gs.1 x) ∈ D := fun x => exp_mem_of_mem_olgDhat hDpos (gs.2 x)
  let fs : X →ᵇ ℝ := mkOfCompact ⟨fun x => Real.exp (gs.1 x),
    Real.continuous_exp.comp gs.1.continuous⟩
  have hfs : ∀ x, fs x = Real.exp (gs.1 x) := fun _ => rfl
  refine ⟨fs, ⟨fun x => by rw [hfs]; exact hmem x, fun x => ?_⟩, ?_⟩
  · have h1 : (olgThatF hyp hDpos gs).1 x = gs.1 x := by rw [hfix]
    rw [olgThatF_apply, olgOpThat] at h1
    have hpos : 0 < olgOpT G κ (fun x' => Real.exp (gs.1 x')) x :=
      hDpos ((ex_17_2a hyp (Real.continuous_exp.comp gs.1.continuous) hmem).2 x)
    rw [hfs, ← h1, Real.exp_log hpos]
    rfl
  · rintro f ⟨hfD, hfix'⟩
    have hfpos : ∀ x, 0 < f x := fun x => hDpos (hfD x)
    let lf : olgF X (olgDhat D) := ⟨mkOfCompact ⟨fun x => Real.log (f x),
      f.continuous.log fun x => (hfpos x).ne'⟩, fun x => ⟨f x, hfD x, rfl⟩⟩
    have hlf : olgThatF hyp hDpos lf = lf := by
      apply Subtype.ext
      ext x
      rw [olgThatF_apply]
      change olgOpThat G κ (fun x' => Real.log (f x')) x = Real.log (f x)
      rw [olgOpThat_log G κ hfpos x, ← hfix' x]
    have := huniq lf hlf
    ext x
    rw [hfs, ← this]
    change f x = Real.exp (Real.log (f x))
    rw [Real.exp_log (hfpos x)]

end StokeyLucasPrescott.FixedPointArguments
