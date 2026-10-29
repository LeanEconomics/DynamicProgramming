/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearStateSpace.ForwardAccessibility
import NonlinearStateSpace.EChains
import NonlinearStateSpace.LinearTChains
import NonlinearStateSpace.LocalInverse
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Equicontinuity and the nonlinear state space model (MT §7.5)

Meyn and Tweedie, §7.5, pp. 163–165, and the commentary §7.6, p. 166. `X` and `W` are
finite-dimensional real normed spaces with their Borel σ-algebras; the disturbance law `Γ` is any
probability measure (the density condition (NSS3) is not used).

* `continuous_sensitivity`: the sensitivity process `∇Φₖ` of (7.26) (`sensitivity`, built in
  `ForwardAccessibility`, where `hasFDerivAt_controlMap_left` shows `∇Φₖ = dΦₖ/dΦ₀`) is jointly
  continuous for a `C¹` map `F`.
* **Theorem 7.5.1 (i)** (p. 164): `theorem_7_5_1_i`, if on an open convex `N` the sensitivity is
  dominated, almost surely and uniformly on `N`, by an integrable function (7.27) and `Φₖ` is
  integrable from one point of `N`, then `x ↦ Eₓ[Φₖ]` is differentiable on `N` with derivative
  `Eₓ[∇Φₖ]`. `theorem_7_5_1_i_of_bounded` (p. 164): for disturbances carried by a compact set
  (7.27) holds trivially on every open convex `N` with compact closure.
* `isEChain_of_meanLipschitz`: if, locally uniformly in the initial points and uniformly in `k`,
  `E‖Φₖ(x) − Φₖ(y)‖ ≤ K‖x − y‖` (both paths driven by the same disturbances), then NSS(F) is an
  e-chain.
* **Theorem 7.5.1 (ii)** (p. 164): `theorem_7_5_1_ii`, if `sup_{y ∈ C} sup_k E_y[‖∇Φₖ‖] < ∞` for
  every compact `C`, NSS(F) is an e-chain.
* **Proposition 7.5.3** (p. 165): `proposition_7_5_3`, a linear state space model satisfying the
  eigenvalue condition (LSS5) is an e-chain (here `∇Φₖ = Fᵏ`, `sensitivity_linear`).
* **Proposition 7.5.2** (p. 164), in the form `proposition_7_5_2`: if `sup_{x ∈ C} ‖∇Φₖ(x, u)‖`
  grows at most polynomially in the disturbances and `E[exp(ε₀|W₁|)] < ∞`, then
  `E[sup_{x ∈ C} ‖∇Φₖ‖] < ∞`, so Theorem 7.5.1 (i) applies.
* Commentary (p. 166, Duflo's condition): `duflo_isEChain`, if `‖F(x, w) − F(y, w)‖ ≤ α(w)‖x − y‖`
  with `E[α(W)] ≤ 1` (in particular if `E[α(W)ᵐ] ≤ 1` for some `m ≥ 1`), NSS(F) is an e-chain.

**Hypotheses and proof differences.** Theorem 7.5.1 (ii) is proved without the domination
hypothesis (7.27) the book adds: the mean value theorem in integral form and Tonelli give
`E‖Φₖ(x) − Φₖ(y)‖ ≤ sup_{z ∈ [x, y]} E_z‖∇Φₖ‖ · ‖x − y‖`, and a uniformly continuous `f` then
gives the equicontinuity of `Pᵏf` directly (Markov's inequality), without the book's
approximation of `C_c` by `C^∞ ∩ C_c` and its derivative bound in terms of `‖f′‖∞`. In
Theorem 7.5.1 (i) the book implicitly assumes `Eₓ[Φₖ]` exists; integrability from one point
of `N` is assumed here. Proposition 7.5.2 for rational `F` needs a polynomial bound on the
sensitivity of rational maps without real poles (a Łojasiewicz-type inequality), which is taken as
the hypothesis; the book's statement fails for rational `F` with real poles, which are not `C¹`.
-/

namespace MeynTweedie.NonlinearStateSpace

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal Matrix

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W]

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
/-- The sensitivity process is jointly continuous in the initial state and the disturbances. -/
theorem continuous_sensitivity {F : X × W → X} (hF : ContDiff ℝ 1 F) (k : ℕ) :
    Continuous fun p : X × (Fin k → W) => sensitivity F k p.1 p.2 := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    have hcm := (contDiff_controlMap hF k).continuous
    have hfd := hF.continuous_fderiv one_ne_zero
    have hinit : Continuous fun p : X × (Fin (k + 1) → W) => (p.1, Fin.init p.2) :=
      continuous_fst.prodMk ((continuous_pi fun i => continuous_apply _).comp continuous_snd)
    have hdx0 : Continuous fun q : X × W => dxF F q.1 q.2 :=
      (hfd.comp (continuous_fst.prodMk continuous_snd)).clm_comp continuous_const
    have hdx : Continuous fun p : X × (Fin (k + 1) → W) =>
        dxF F (controlMap F k p.1 (Fin.init p.2)) (p.2 (Fin.last k)) :=
      hdx0.comp ((hcm.comp hinit).prodMk ((continuous_apply _).comp continuous_snd))
    exact hdx.clm_comp (ih.comp hinit)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [BorelSpace W] in
/-- `Eₓ[g(Φₖ)] = ∫ g(Fₖ(x, u)) Γ^{⊗k}(du)`. -/
theorem integral_nssKernel_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X} (hF : Measurable F) (k : ℕ) (x : X)
    {g : X → E} (hg : AEStronglyMeasurable g ((nssKernel Γ F ^ k) x)) :
    ∫ y, g y ∂(nssKernel Γ F ^ k) x =
      ∫ u, g (controlMap F k x u) ∂(Measure.pi fun _ : Fin k => Γ) := by
  rw [nssKernel, recursionKernel_pow_apply Γ hF k x] at hg ⊢
  exact integral_map (measurable_controlMap_right hF k x).aemeasurable hg

/-- **Theorem 7.5.1 (i)** (MT p. 164): if `N` is open and convex, the sensitivity `∇Φₖ` is
dominated on `N` by an integrable `b` ((7.27)), and `Φₖ` is integrable from some `x₁ ∈ N`, then
for every `x ∈ N`, `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]`. -/
theorem theorem_7_5_1_i (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : ContDiff ℝ 1 F) (k : ℕ) {N : Set X} (hN : IsOpen N) (hNc : Convex ℝ N)
    {b : (Fin k → W) → ℝ} (hb : Integrable b (Measure.pi fun _ : Fin k => Γ))
    (hbound : ∀ᵐ u ∂(Measure.pi fun _ : Fin k => Γ), ∀ y ∈ N, ‖sensitivity F k y u‖ ≤ b u)
    {x₁ : X} (hx₁ : x₁ ∈ N)
    (hint : Integrable (controlMap F k x₁) (Measure.pi fun _ : Fin k => Γ)) {x : X}
    (hx : x ∈ N) :
    HasFDerivAt (fun y => ∫ z, z ∂(nssKernel Γ F ^ k) y)
      (∫ u, sensitivity F k x u ∂(Measure.pi fun _ : Fin k => Γ)) x := by
  set μ := Measure.pi fun _ : Fin k => Γ
  have hFd := hF.differentiable one_ne_zero
  have hcm := (contDiff_controlMap hF k).continuous
  have hcont : ∀ y, Continuous (controlMap F k y) := fun y =>
    hcm.comp (continuous_const.prodMk continuous_id)
  have hderiv : ∀ u, ∀ y, HasFDerivAt (fun z => controlMap F k z u) (sensitivity F k y u) y :=
    fun u y => hasFDerivAt_controlMap_left hFd k y u
  -- integrability from `x₁` by the mean value theorem
  have hintN : ∀ y ∈ N, Integrable (controlMap F k y) μ := by
    intro y hy
    have hle : ∀ᵐ u ∂μ, ‖controlMap F k y u - controlMap F k x₁ u‖ ≤ b u * ‖y - x₁‖ :=
      hbound.mono fun u hu => hNc.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z _ => (hderiv u z).hasFDerivWithinAt) (fun z hz => hu z hz) hx₁ hy
    have hdiff : Integrable (fun u => controlMap F k y u - controlMap F k x₁ u) μ :=
      (hb.mul_const ‖y - x₁‖).mono' ((hcont y).sub (hcont x₁)).aestronglyMeasurable hle
    refine (hdiff.add hint).congr (Eventually.of_forall fun u => ?_)
    simp
  have hrepr : ∀ y, ∫ z, z ∂(nssKernel Γ F ^ k) y = ∫ u, controlMap F k y u ∂μ := fun y =>
    integral_nssKernel_pow Γ hF.continuous.measurable k y aestronglyMeasurable_id
  simp_rw [hrepr]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (hN.mem_nhds hx)
    (Eventually.of_forall fun y => (hcont y).aestronglyMeasurable) (hintN x hx)
    ((continuous_sensitivity hF k).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    hbound hb (Eventually.of_forall fun u y _ => hderiv u y)

/-- **Bounded disturbances** (MT p. 164): if `Γ` is carried by a compact set `K`, then for every
open convex `N` with compact closure the sensitivity is bounded on `N` for `Γ^{⊗k}`-almost every
disturbance, `Φₖ` is integrable from every point, and so `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]` on `N`
((7.27) holds trivially). -/
theorem theorem_7_5_1_i_of_bounded (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : ContDiff ℝ 1 F) {K : Set W} (hK : IsCompact K) (hΓK : Γ Kᶜ = 0) (k : ℕ)
    {N : Set X} (hN : IsOpen N) (hNc : Convex ℝ N) (hNb : IsCompact (closure N)) {x : X}
    (hx : x ∈ N) :
    HasFDerivAt (fun y => ∫ z, z ∂(nssKernel Γ F ^ k) y)
      (∫ u, sensitivity F k x u ∂(Measure.pi fun _ : Fin k => Γ)) x := by
  set μ := Measure.pi fun _ : Fin k => Γ
  set Kk : Set (Fin k → W) := Set.pi univ fun _ => K
  have hKk : IsCompact Kk := isCompact_univ_pi fun _ => hK
  have hae : ∀ᵐ u ∂μ, u ∈ Kk := by
    have : Kkᶜ = ⋃ i, Function.eval i ⁻¹' Kᶜ := by ext u; simp [Kk]
    rw [ae_iff]
    change μ Kkᶜ = 0
    rw [this]
    exact measure_iUnion_null fun i => Measure.pi_eval_preimage_null _ hΓK
  obtain ⟨C, hC⟩ := (hNb.prod hKk).exists_bound_of_continuousOn
    (continuous_sensitivity hF k).continuousOn
  have hcm := (contDiff_controlMap hF k).continuous
  obtain ⟨C', hC'⟩ := (hNb.prod hKk).exists_bound_of_continuousOn hcm.continuousOn
  have hbound : ∀ᵐ u ∂μ, ∀ y ∈ N, ‖sensitivity F k y u‖ ≤ C :=
    hae.mono fun u hu y hy => hC (y, u) ⟨subset_closure hy, hu⟩
  have hint : Integrable (controlMap F k x) μ :=
    Integrable.of_bound ((hcm.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      C' (hae.mono fun u hu => hC' (x, u) ⟨subset_closure hx, hu⟩)
  exact theorem_7_5_1_i Γ hF k hN hNc (integrable_const C) hbound hx hint hx

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [BorelSpace W] in
/-- **Paths that are Lipschitz in mean give an e-chain**: if every `x₀` has a ball on which
`E‖Φₖ(x₀) − Φₖ(x)‖ ≤ K‖x₀ − x‖` for all `k` (both paths driven by the same disturbances), then
NSS(F) is an e-chain. -/
theorem isEChain_of_meanLipschitz [SecondCountableTopology X] (Γ : Measure W)
    [IsProbabilityMeasure Γ] {F : X × W → X} (hF : Measurable F)
    (h : ∀ x₀ : X, ∃ r > 0, ∃ K : ℝ≥0, ∀ x ∈ ball x₀ r, ∀ k,
      ∫⁻ u, ‖controlMap F k x₀ u - controlMap F k x u‖ₑ ∂(Measure.pi fun _ : Fin k => Γ) ≤
        K * ‖x₀ - x‖ₑ) :
    IsEChain (nssKernel Γ F) := by
  intro f hf hfc C _
  refine Equicontinuous.equicontinuousOn (fun x₀ => ?_) C
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨r, hr, K, hK⟩ := h x₀
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  obtain ⟨B, hB⟩ := (_root_.ofCompactSupport f hf hfc).isBounded_range.exists_norm_le
  have hfB : ∀ y, |f y| ≤ max B 0 := fun y =>
    (hB _ ⟨y, rfl⟩).trans (le_max_left _ _)
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'0 : 0 < B' := by positivity
  set η : ℝ := ε * δ / (4 * B' * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨min r η, lt_min hr hη0, fun x hx k => ?_⟩
  have hxr : x ∈ ball x₀ r := lt_of_lt_of_le hx (min_le_left _ _)
  have hxη : ‖x₀ - x‖ < η := by
    rw [← dist_eq_norm, dist_comm]; exact lt_of_lt_of_le hx (min_le_right _ _)
  set μ := Measure.pi fun _ : Fin k => Γ
  have hm : ∀ z, Measurable (controlMap F k z) := measurable_controlMap_right hF k
  have hrepr : ∀ z, ∫ y, f y ∂(nssKernel Γ F ^ k) z = ∫ u, f (controlMap F k z u) ∂μ :=
    fun z => integral_nssKernel_pow Γ hF k z hf.aestronglyMeasurable
  have hint : ∀ z, Integrable (fun u => f (controlMap F k z u)) μ := fun z =>
    Integrable.of_bound (hf.measurable.comp (hm z)).aestronglyMeasurable (max B 0)
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hfB _)
  set S : Set (Fin k → W) := {u | δ ≤ dist (controlMap F k x₀ u) (controlMap F k x u)}
  have hSm : MeasurableSet S := measurableSet_le measurable_const ((hm x₀).dist (hm x))
  -- Markov's inequality
  have hSμ : μ S ≤ ENNReal.ofReal (K * ‖x₀ - x‖ / δ) := by
    have hmk := meas_ge_le_lintegral_div (μ := μ)
      (f := fun u => ‖controlMap F k x₀ u - controlMap F k x u‖ₑ)
      (((hm x₀).sub (hm x)).enorm.aemeasurable) (ε := ENNReal.ofReal δ)
      (by simpa using hδ) ENNReal.ofReal_ne_top
    refine (measure_mono fun u hu => ?_).trans (hmk.trans ?_)
    · change ENNReal.ofReal δ ≤ ‖controlMap F k x₀ u - controlMap F k x u‖ₑ
      rw [← ofReal_norm, ← dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal hu
    · rw [ENNReal.ofReal_div_of_pos hδ, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ofReal_norm]
      exact ENNReal.div_le_div_right (hK x hxr k) _
  have hSreal : μ.real S ≤ K * ‖x₀ - x‖ / δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hSμ
  have hpt : ∀ u, ‖f (controlMap F k x₀ u) - f (controlMap F k x u)‖ ≤
      ε / 2 + 2 * B' * S.indicator 1 u := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, Pi.one_apply, mul_one, Real.norm_eq_abs]
      have h1 := hfB (controlMap F k x₀ u)
      have h2 := hfB (controlMap F k x u)
      calc |f (controlMap F k x₀ u) - f (controlMap F k x u)|
          ≤ |f (controlMap F k x₀ u)| + |f (controlMap F k x u)| := abs_sub _ _
        _ ≤ ε / 2 + 2 * B' := by linarith
    · rw [indicator_of_notMem hu, mul_zero, add_zero, ← dist_eq_norm]
      exact (hfδ (not_le.1 hu)).le
  have hgint : Integrable (fun u => ε / 2 + 2 * B' * S.indicator 1 u) μ :=
    (integrable_const _).add ((integrable_const 1).indicator hSm |>.const_mul _)
  rw [hrepr, hrepr, dist_eq_norm, ← integral_sub (hint x₀) (hint x)]
  calc ‖∫ u, f (controlMap F k x₀ u) - f (controlMap F k x u) ∂μ‖
      ≤ ∫ u, ε / 2 + 2 * B' * S.indicator 1 u ∂μ :=
        norm_integral_le_of_norm_le hgint (Eventually.of_forall hpt)
    _ = ε / 2 + 2 * B' * μ.real S := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hSm |>.const_mul _),
          integral_const, integral_const_mul, integral_indicator_one hSm, probReal_univ,
          smul_eq_mul, one_mul]
    _ ≤ ε / 2 + 2 * B' * (K * ‖x₀ - x‖ / δ) := by gcongr
    _ < ε := by
        have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
        have h1 : (K : ℝ) * ‖x₀ - x‖ < (K + 1) * η := by
          calc (K : ℝ) * ‖x₀ - x‖ ≤ K * η := mul_le_mul_of_nonneg_left hxη.le hK0
            _ < (K + 1) * η := by nlinarith
        have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
        have h2 : 2 * B' * ((K + 1) * η) / δ = ε / 2 := by
          rw [hη]
          field_simp
          ring
        have h3 : 2 * B' * (K * ‖x₀ - x‖ / δ) < ε / 2 := by
          rw [← h2, mul_div_assoc']
          exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h1 (by positivity)) hδ
        linarith

omit [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
/-- **The mean value theorem along a path**, in integral form:
`‖Fₖ(y, u) − Fₖ(x, u)‖ ≤ ∫₀¹ ‖∇Φₖ(x + t(y − x), u)‖ dt · ‖y − x‖`. -/
theorem enorm_controlMap_sub_le {F : X × W → X} (hF : ContDiff ℝ 1 F) (k : ℕ) (x y : X)
    (u : Fin k → W) :
    ‖controlMap F k y u - controlMap F k x u‖ₑ ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ‖sensitivity F k (x + t • (y - x)) u‖ₑ * ‖y - x‖ₑ := by
  have hFd := hF.differentiable one_ne_zero
  set g : ℝ → X := fun t => controlMap F k (x + t • (y - x)) u
  set g' : ℝ → X := fun t => sensitivity F k (x + t • (y - x)) u (y - x)
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact (hasFDerivAt_controlMap_left hFd k _ u).comp_hasDerivAt t h1
  have hz : Continuous fun t : ℝ => x + t • (y - x) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hcont : Continuous g' := by
    have hs : Continuous fun t : ℝ => sensitivity F k (x + t • (y - x)) u :=
      (continuous_sensitivity hF k).comp (hz.prodMk continuous_const)
    exact hs.clm_apply continuous_const
  have hftc : ∫ t in (0 : ℝ)..1, g' t = g 1 - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
      (hcont.intervalIntegrable 0 1)
  have hg1 : g 1 = controlMap F k y u := by simp [g]
  have hg0 : g 0 = controlMap F k x u := by simp [g]
  rw [← hg1, ← hg0, ← hftc, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => ?_)
  exact ContinuousLinearMap.le_opENorm _ _

/-- **Theorem 7.5.1 (ii)** (MT p. 164): if `F` is `C¹` and for every compact `C`,
`sup_{y ∈ C} sup_k E_y[‖∇Φₖ‖] < ∞`, then NSS(F) is an e-chain. (The domination hypothesis
(7.27) of the book is not needed.) -/
theorem theorem_7_5_1_ii (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : ContDiff ℝ 1 F)
    (hC : ∀ C : Set X, IsCompact C → ∃ K : ℝ≥0, ∀ y ∈ C, ∀ k,
      ∫⁻ u, ‖sensitivity F k y u‖ₑ ∂(Measure.pi fun _ : Fin k => Γ) ≤ K) :
    IsEChain (nssKernel Γ F) := by
  refine isEChain_of_meanLipschitz Γ hF.continuous.measurable fun x₀ => ?_
  obtain ⟨K, hK⟩ := hC (closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  refine ⟨1, one_pos, K, fun x hx k => ?_⟩
  set μ := Measure.pi fun _ : Fin k => Γ
  have hseg : ∀ t ∈ Ioc (0 : ℝ) 1, x + t • (x₀ - x) ∈ closedBall x₀ 1 := fun t ht =>
    (convex_closedBall x₀ 1).add_smul_sub_mem (ball_subset_closedBall hx)
      (mem_closedBall_self zero_le_one) ⟨ht.1.le, ht.2⟩
  have hz : Continuous fun q : (Fin k → W) × ℝ => (x + q.2 • (x₀ - x), q.1) :=
    (continuous_const.add (continuous_snd.smul continuous_const)).prodMk continuous_fst
  have hc : Continuous fun q : (Fin k → W) × ℝ =>
      ‖sensitivity F k (x + q.2 • (x₀ - x)) q.1‖ₑ * ‖x₀ - x‖ₑ :=
    (ENNReal.continuous_mul_const enorm_ne_top).comp ((continuous_sensitivity hF k).comp hz).enorm
  have hmeas : AEMeasurable (Function.uncurry fun (u : Fin k → W) (t : ℝ) =>
      ‖sensitivity F k (x + t • (x₀ - x)) u‖ₑ * ‖x₀ - x‖ₑ)
      (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    hc.measurable.aemeasurable
  calc ∫⁻ u, ‖controlMap F k x₀ u - controlMap F k x u‖ₑ ∂μ
      ≤ ∫⁻ u, (∫⁻ t in Ioc (0 : ℝ) 1,
          ‖sensitivity F k (x + t • (x₀ - x)) u‖ₑ * ‖x₀ - x‖ₑ) ∂μ :=
        lintegral_mono fun u => enorm_controlMap_sub_le hF k x x₀ u
    _ = ∫⁻ t in Ioc (0 : ℝ) 1,
          (∫⁻ u, ‖sensitivity F k (x + t • (x₀ - x)) u‖ₑ * ‖x₀ - x‖ₑ ∂μ) :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, (K : ℝ≥0∞) * ‖x₀ - x‖ₑ := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        rw [lintegral_mul_const' _ _ enorm_ne_top]
        exact mul_le_mul_left (hK _ (hseg t ht) k) _
    _ = K * ‖x₀ - x‖ₑ := by simp

/-! ### Proposition 7.5.3: linear models -/

/-- The sensitivity process of the linear model `F(x, u) = A x + B u` is `∇Φₖ = Aᵏ`
(MT p. 165). -/
theorem sensitivity_linear {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x : Fin n → ℝ) (u : Fin k → Fin p → ℝ) (a : Fin n → ℝ) :
    sensitivity (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) k x u a =
      (A ^ k) *ᵥ a := by
  induction k with
  | zero => simp [sensitivity]
  | succ k ih =>
    change dxF _ _ _ (sensitivity _ k x (Fin.init u) a) = _
    rw [(dxF_duF_linear A B _ _).1, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- **Proposition 7.5.3** (MT p. 165): a linear state space model LSS(F, G) whose matrix `A`
satisfies the eigenvalue condition (LSS5) is an e-chain, for any disturbance law. -/
theorem proposition_7_5_3 {n p : ℕ} (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {A : Matrix (Fin n) (Fin n) ℝ} (B : Matrix (Fin n) (Fin p) ℝ) (hA : IsStableMatrix A) :
    IsEChain (lssMatrixKernel Γ A B) := by
  obtain ⟨C, r, hC, hr0, hr1, hbd⟩ := isStableMatrix_geometric hA
  set F := fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2
  have hF : ContDiff ℝ 1 F :=
    ((LinearMap.toContinuousLinearMap A.mulVecLin).contDiff.comp contDiff_fst).add
      ((LinearMap.toContinuousLinearMap B.mulVecLin).contDiff.comp contDiff_snd)
  have hnorm : ∀ k x u, ‖sensitivity F k x u‖ ≤ C := fun k x u =>
    ContinuousLinearMap.opNorm_le_bound _ hC fun a => by
      rw [sensitivity_linear]
      refine (hbd k a).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact mul_le_of_le_one_right hC (pow_le_one₀ hr0.le hr1.le)
  have := theorem_7_5_1_ii Γ hF fun _ _ => ⟨C.toNNReal, fun y _ k => by
    calc ∫⁻ u, ‖sensitivity F k y u‖ₑ ∂(Measure.pi fun _ : Fin k => Γ)
        ≤ ∫⁻ _, (C.toNNReal : ℝ≥0∞) ∂(Measure.pi fun _ : Fin k => Γ) := lintegral_mono fun u => by
          rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hC]
          exact ENNReal.ofReal_le_ofReal (hnorm k y u)
      _ = C.toNNReal := by simp⟩
  exact this

/-! ### Duflo's condition (commentary, p. 166) -/

/-- Bernoulli's inequality in `[0, ∞]`: `m a ≤ aᵐ + (m − 1)` for `m ≥ 1`. -/
theorem ennreal_bernoulli (a : ℝ≥0∞) {m : ℕ} (hm : 1 ≤ m) : (m : ℝ≥0∞) * a ≤ a ^ m + (m - 1) := by
  rcases eq_or_ne a ∞ with rfl | ha
  · rw [ENNReal.top_pow (by omega)]
    exact le_top.trans (by simp)
  · lift a to ℝ≥0 using ha
    have hm' : (1 : ℝ≥0) ≤ m := by exact_mod_cast hm
    have hNN : (m : ℝ≥0) * a ≤ a ^ m + ((m : ℝ≥0) - 1) := by
      rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub hm']
      have := one_add_mul_le_pow (a := (a : ℝ) - 1) (by linarith [a.coe_nonneg]) m
      simp only [add_sub_cancel] at this
      linarith
    have h1 : ((m : ℝ≥0∞) - 1) = (((m : ℝ≥0) - 1 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_sub]; simp
    rw [h1]
    exact_mod_cast hNN

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [BorelSpace W] in
/-- If `E[α(W)ᵐ] ≤ 1` for some `m ≥ 1` then `E[α(W)] ≤ 1` (Jensen, via Bernoulli). -/
theorem lintegral_le_one_of_lintegral_pow_le_one {Γ : Measure W} [IsProbabilityMeasure Γ]
    {α : W → ℝ≥0∞} (hα : Measurable α) {m : ℕ} (hm : 1 ≤ m) (h : ∫⁻ w, α w ^ m ∂Γ ≤ 1) :
    ∫⁻ w, α w ∂Γ ≤ 1 := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have key : (m : ℝ≥0∞) * ∫⁻ w, α w ∂Γ ≤ m * 1 := by
    rw [← lintegral_const_mul _ hα, mul_one]
    calc ∫⁻ w, (m : ℝ≥0∞) * α w ∂Γ ≤ ∫⁻ w, (α w ^ m + (m - 1)) ∂Γ :=
          lintegral_mono fun w => ennreal_bernoulli (α w) hm
      _ = ∫⁻ w, α w ^ m ∂Γ + (m - 1) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + (m - 1) := by gcongr
      _ = m := by
          rw [add_tsub_cancel_of_le]
          exact_mod_cast hm
  exact (ENNReal.mul_le_mul_iff_right hm0 (ENNReal.natCast_ne_top m)).1 key

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- Under Duflo's condition `‖F(x, w) − F(y, w)‖ ≤ α(w)‖x − y‖`, two paths driven by the same
disturbances satisfy `‖Fₖ(x, u) − Fₖ(y, u)‖ ≤ α(u₁) ⋯ α(uₖ) ‖x − y‖`. -/
theorem enorm_controlMap_sub_le_prod {F : X × W → X} {α : W → ℝ≥0∞}
    (hL : ∀ x y w, ‖F (x, w) - F (y, w)‖ₑ ≤ α w * ‖x - y‖ₑ) (k : ℕ) (x y : X)
    (u : Fin k → W) :
    ‖controlMap F k x u - controlMap F k y u‖ₑ ≤ (∏ i, α (u i)) * ‖x - y‖ₑ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [controlMap_succ, controlMap_succ, Fin.prod_univ_castSucc]
    refine (hL _ _ _).trans ?_
    calc α (u (Fin.last k)) * ‖controlMap F k x (Fin.init u) - controlMap F k y (Fin.init u)‖ₑ
        ≤ α (u (Fin.last k)) * ((∏ i : Fin k, α (Fin.init u i)) * ‖x - y‖ₑ) := by
          gcongr; exact ih _
      _ = (∏ i : Fin k, α (u i.castSucc)) * α (u (Fin.last k)) * ‖x - y‖ₑ := by
          simp only [Fin.init]; ring

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [BorelSpace W] in
/-- **Duflo's condition** (MT commentary, p. 166): if `‖F(x, w) − F(y, w)‖ ≤ α(w)‖x − y‖` with
`E[α(W)ᵐ] ≤ 1` for some `m ≥ 1` (the book: `< 1` for some large `m`), NSS(F) is an e-chain. -/
theorem duflo_isEChain [SecondCountableTopology X] (Γ : Measure W) [IsProbabilityMeasure Γ]
    {F : X × W → X} (hF : Measurable F) {α : W → ℝ≥0∞} (hα : Measurable α)
    (hL : ∀ x y w, ‖F (x, w) - F (y, w)‖ₑ ≤ α w * ‖x - y‖ₑ) {m : ℕ} (hm : 1 ≤ m)
    (hαm : ∫⁻ w, α w ^ m ∂Γ ≤ 1) : IsEChain (nssKernel Γ F) := by
  have h1 := lintegral_le_one_of_lintegral_pow_le_one hα hm hαm
  refine isEChain_of_meanLipschitz Γ hF fun x₀ => ⟨1, one_pos, 1, fun x _ k => ?_⟩
  calc ∫⁻ u, ‖controlMap F k x₀ u - controlMap F k x u‖ₑ ∂(Measure.pi fun _ : Fin k => Γ)
      ≤ ∫⁻ u, (∏ i, α (u i)) * ‖x₀ - x‖ₑ ∂(Measure.pi fun _ : Fin k => Γ) :=
        lintegral_mono fun u => enorm_controlMap_sub_le_prod hL k x₀ x u
    _ = (∫⁻ w, α w ∂Γ) ^ k * ‖x₀ - x‖ₑ := by
        rw [lintegral_mul_const' _ _ enorm_ne_top, lintegral_pi_prod Γ k (fun _ => α) fun _ => hα]
        simp
    _ ≤ 1 * ‖x₀ - x‖ₑ := by
        gcongr
        exact pow_le_one₀ zero_le h1
    _ = (1 : ℝ≥0) * ‖x₀ - x‖ₑ := by simp

/-! ### Proposition 7.5.2: exponential moments -/

omit [MeasurableSpace W] [BorelSpace W] in
/-- `(1 + t)ᵐ ≤ m! ε⁻ᵐ e^ε e^{ε t}` for `t ≥ 0`, `ε > 0`. -/
theorem one_add_pow_le_exp {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (m : ℕ) :
    (1 + t) ^ m ≤ m.factorial / ε ^ m * Real.exp ε * Real.exp (ε * t) := by
  have h := Real.pow_div_factorial_le_exp (x := ε * (1 + t)) (by positivity) m
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  rw [div_le_iff₀ hm, mul_pow] at h
  have heq : (m.factorial : ℝ) / ε ^ m * Real.exp ε * Real.exp (ε * t) =
      m.factorial * Real.exp (ε * (1 + t)) / ε ^ m := by
    rw [mul_add, mul_one, Real.exp_add]; ring
  rw [heq, le_div_iff₀ (by positivity)]
  linarith

/-- **Proposition 7.5.2** (MT p. 164), in the form proved here: if on an open convex `N` the
sensitivity grows at most polynomially in the disturbances,
`‖∇Φₖ(y, u)‖ ≤ c (1 + Σᵢ ‖uᵢ‖)ᵐ` for `y ∈ N`, and `E[exp(ε₀ ‖W₁‖)] < ∞`, then the bound is
integrable (so `E[sup_{Φ₀ ∈ N} ‖∇Φₖ‖] < ∞`), and `d/dx Eₓ[Φₖ] = Eₓ[∇Φₖ]` on `N` (given that
`Φₖ` is integrable from one point of `N`). For rational `F` without real poles the polynomial
bound is the Łojasiewicz-type input the book calls straightforward; it is the hypothesis here. -/
theorem proposition_7_5_2 (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : ContDiff ℝ 1 F) (k : ℕ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hexp : ∫⁻ w, ENNReal.ofReal (Real.exp (ε₀ * ‖w‖)) ∂Γ ≠ ∞) {N : Set X} (hN : IsOpen N)
    (hNc : Convex ℝ N) {c : ℝ} {m : ℕ}
    (hpoly : ∀ y ∈ N, ∀ u : Fin k → W, ‖sensitivity F k y u‖ ≤ c * (1 + ∑ i, ‖u i‖) ^ m)
    {x₁ : X} (hx₁ : x₁ ∈ N) (hint : Integrable (controlMap F k x₁) (Measure.pi fun _ => Γ)) :
    Integrable (fun u : Fin k → W => c * (1 + ∑ i, ‖u i‖) ^ m) (Measure.pi fun _ => Γ) ∧
      ∀ x ∈ N, HasFDerivAt (fun y => ∫ z, z ∂(nssKernel Γ F ^ k) y)
        (∫ u, sensitivity F k x u ∂(Measure.pi fun _ : Fin k => Γ)) x := by
  set μ := Measure.pi fun _ : Fin k => Γ
  set b : (Fin k → W) → ℝ := fun u => c * (1 + ∑ i, ‖u i‖) ^ m
  have hbc : Continuous b :=
    continuous_const.mul ((continuous_const.add (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).norm)).pow m)
  set D : ℝ := |c| * (m.factorial / ε₀ ^ m * Real.exp ε₀)
  have hD : 0 ≤ D := by positivity
  have hpt : ∀ u, ‖b u‖ₑ ≤ ENNReal.ofReal D * ∏ i, ENNReal.ofReal (Real.exp (ε₀ * ‖u i‖)) := by
    intro u
    have ht : 0 ≤ ∑ i, ‖u i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← ENNReal.ofReal_mul hD,
      ← Real.exp_sum, ← Finset.mul_sum, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    change ‖c * (1 + ∑ i, ‖u i‖) ^ m‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ∑ i, ‖u i‖) m)]
    calc |c| * (1 + ∑ i, ‖u i‖) ^ m
        ≤ |c| * (m.factorial / ε₀ ^ m * Real.exp ε₀ * Real.exp (ε₀ * ∑ i, ‖u i‖)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le_exp hε₀ ht m) (abs_nonneg c)
      _ = D * Real.exp (ε₀ * ∑ i, ‖u i‖) := by ring
  have hgm : ∀ i : Fin k, Measurable fun w : W => ENNReal.ofReal (Real.exp (ε₀ * ‖w‖)) :=
    fun _ => (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_norm))).measurable
  have hfin : ∫⁻ u, ‖b u‖ₑ ∂μ < ∞ := by
    calc ∫⁻ u, ‖b u‖ₑ ∂μ
        ≤ ∫⁻ u, ENNReal.ofReal D * ∏ i, ENNReal.ofReal (Real.exp (ε₀ * ‖u i‖)) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal D * (∫⁻ w, ENNReal.ofReal (Real.exp (ε₀ * ‖w‖)) ∂Γ) ^ k := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_pi_prod Γ k (fun _ w => ENNReal.ofReal (Real.exp (ε₀ * ‖w‖))) hgm]
          simp
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hexp.lt_top)
  have hb : Integrable b μ := ⟨hbc.aestronglyMeasurable, hfin⟩
  exact ⟨hb, fun x hx => theorem_7_5_1_i Γ hF k hN hNc hb
    (Eventually.of_forall fun u y hy => hpoly y hy u) hx₁ hint hx⟩

end MeynTweedie.NonlinearStateSpace
