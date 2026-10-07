/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDecisionProcesses.ADP
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Distributional dynamic programming

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.4 (pp. 84–89).

Values are *distributional value functions*: stochastic kernels `η` from `X` to `ℝ` with a
uniformly bounded first moment, ordered pointwise by first-order stochastic dominance `⊴`. For a
policy `σ`, the distributional policy operator `D_σ` maps `η` to the law of `r_σ(x) + βV` with
`V ∼ (P_σ ⊗ η)(x)` (2.21)–(2.23).

* First-order stochastic dominance is a partial order on probability measures on `ℝ`
  (antisymmetry via distribution functions), so `(ℋ, ⊴)` is a poset.
* **Proposition 2.3.2**: each `D_σ` is an order preserving self-map of `(ℋ, ⊴)`, so
  `(ℋ, 𝕋_DDP)` is an ADP; and (2.23), `(D_σ η)(x, h) = ∫∫ h(r_σ(x) + βv) η(x', dv) P_σ(x, dx')`.
* **Exercise 2.3.11**: `D_σ` is a `β`-contraction for the supremum Wasserstein distance:
  `W₁((D_σ η)(x), (D_σ η')(x)) ≤ β sup_{x'} W₁(η(x'), η'(x'))`.
-/

open MeasureTheory ProbabilityTheory Set Function Filter

open scoped ENNReal

namespace SargentStachurski.AbstractDecisionProcesses

/-! ### First-order stochastic dominance -/

/-- `μ ⪯F ν` (§A.5.5): `∫ h dμ ≤ ∫ h dν` for every bounded increasing `h`. -/
def FOSD (μ ν : Measure ℝ) : Prop :=
  ∀ h : ℝ → ℝ, Monotone h → (∃ M, ∀ z, |h z| ≤ M) → ∫ z, h z ∂μ ≤ ∫ z, h z ∂ν

theorem FOSD.refl (μ : Measure ℝ) : FOSD μ μ := fun _ _ _ => le_rfl

theorem FOSD.trans {μ ν ρ : Measure ℝ} (h1 : FOSD μ ν) (h2 : FOSD ν ρ) : FOSD μ ρ :=
  fun h hm hb => (h1 h hm hb).trans (h2 h hm hb)

/-- Stochastic dominance is antisymmetric on probability measures: tails `μ(a, ∞)` determine the
distribution function. -/
theorem FOSD.antisymm {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h1 : FOSD μ ν) (h2 : FOSD ν μ) : μ = ν := by
  have hind : ∀ a, Monotone ((Set.Ioi a).indicator (1 : ℝ → ℝ)) := fun a z z' hzz' => by
    by_cases hz : z ∈ Set.Ioi a
    · have hz' : z' ∈ Set.Ioi a := lt_of_lt_of_le hz hzz'
      simp [indicator_of_mem hz, indicator_of_mem hz']
    · simp only [indicator_of_notMem hz]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hbd : ∀ a, ∃ M, ∀ z, |(Set.Ioi a).indicator (1 : ℝ → ℝ) z| ≤ M := fun a =>
    ⟨1, fun z => by by_cases hz : z ∈ Set.Ioi a <;> simp [hz]⟩
  have htail : ∀ a, μ (Set.Ioi a) = ν (Set.Ioi a) := fun a => by
    have e1 := h1 _ (hind a) (hbd a)
    have e2 := h2 _ (hind a) (hbd a)
    rw [integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Ioi]
      at e1 e2
    have := le_antisymm e1 e2
    rwa [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)] at this
  refine Measure.ext_of_Iic μ ν fun a => ?_
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, htail]

/-! ### Distributional value functions -/

variable {X : Type*} [MeasurableSpace X]

variable (X) in
/-- `ℋ` (§2.3.4.1): stochastic kernels `η` from `X` to `ℝ` with `sup_x ∫ |z| η(x, dz) < ∞`. -/
def DistValue : Type _ :=
  {η : Kernel X ℝ // IsMarkovKernel η ∧ (∀ x, Integrable (fun z : ℝ => z) (η x)) ∧
    ∃ C, ∀ x, ∫ z, |z| ∂(η x) ≤ C}

/-- The pointwise stochastic dominance order `⊴` on `ℋ` (§2.3.4.1). -/
abbrev distOrder : PartialOrder (DistValue X) where
  le η η' := ∀ x, FOSD (η.1 x) (η'.1 x)
  le_refl η x := FOSD.refl _
  le_trans _ _ _ h1 h2 x := (h1 x).trans (h2 x)
  le_antisymm η η' h1 h2 := by
    have := η.2.1
    have := η'.2.1
    exact Subtype.ext (Kernel.ext fun x => FOSD.antisymm (h1 x) (h2 x))

attribute [local instance] distOrder

/-! ### The distributional policy operators -/

variable {A : Type*} [MeasurableSpace A]

/-- A distributional dynamic program (§2.3.4.1): a stochastic kernel `P` from `X × A` to `X`, a
bounded measurable reward `r` and a discount factor `β ∈ [0, 1)`. -/
structure DDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the transition kernel -/
  P : Kernel (X × A) X
  isMarkov : IsMarkovKernel P
  /-- the reward -/
  r : X × A → ℝ
  r_meas : Measurable r
  r_bdd : ∃ M, ∀ p, |r p| ≤ M
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

/-- Measurable policies `σ : X → A`. -/
def DDPPolicy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] : Type _ :=
  {σ : X → A // Measurable σ}

namespace DDP

variable (D : DDP X A)

/-- `P_σ(x, ·) = P(x, σ(x), ·)`. -/
noncomputable def Pσ (σ : DDPPolicy X A) : Kernel X X :=
  D.P.comap (fun x => (x, σ.1 x)) (measurable_id.prodMk σ.2)

theorem isMarkov_Pσ (σ : DDPPolicy X A) : IsMarkovKernel (D.Pσ σ) := by
  have := D.isMarkov
  unfold Pσ
  infer_instance

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : DDPPolicy X A) (x : X) : ℝ := D.r (x, σ.1 x)

theorem measurable_rσ (σ : DDPPolicy X A) : Measurable (D.rσ σ) :=
  D.r_meas.comp (measurable_id.prodMk σ.2)

/-- The distributional policy operator (2.22): `(D_σ η)(x, ·)` is the law of `r_σ(x) + βV` with
`V ∼ (P_σ ⊗ η)(x, ·)` (2.21). -/
noncomputable def Dσ (σ : DDPPolicy X A) (η : Kernel X ℝ) : Kernel X ℝ :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ (η ∘ₖ D.Pσ σ))
    (fun p : X × ℝ => D.rσ σ p.1 + D.β * p.2)

theorem measurable_affine (σ : DDPPolicy X A) :
    Measurable fun p : X × ℝ => D.rσ σ p.1 + D.β * p.2 :=
  (D.measurable_rσ σ).comp measurable_fst |>.add (measurable_const.mul measurable_snd)

/-- `(D_σ η)(x, ·)` is the image of `(P_σ ⊗ η)(x, ·)` under `v ↦ r_σ(x) + βv`. -/
theorem Dσ_apply (σ : DDPPolicy X A) (η : Kernel X ℝ) [IsMarkovKernel η] (x : X) :
    D.Dσ σ η x = ((η ∘ₖ D.Pσ σ) x).map fun v => D.rσ σ x + D.β * v := by
  have := D.isMarkov_Pσ σ
  rw [Dσ, Kernel.map_apply _ (D.measurable_affine σ), Kernel.prod_apply,
    Kernel.deterministic_apply, Measure.dirac_prod, Measure.map_map (D.measurable_affine σ)
      measurable_prodMk_left]
  rfl

theorem measurable_affine_x (σ : DDPPolicy X A) (x : X) :
    Measurable fun v : ℝ => D.rσ σ x + D.β * v :=
  measurable_const.add (measurable_const.mul measurable_id)

/-- (2.23) (p. 85): `(D_σ η)(x, h) = ∫ [∫ h(r_σ(x) + βv) η(x', dv)] P_σ(x, dx')` for every bounded
measurable `h`. -/
theorem integral_Dσ (σ : DDPPolicy X A) (η : Kernel X ℝ) [IsMarkovKernel η] {h : ℝ → ℝ}
    (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) (x : X) :
    ∫ z, h z ∂(D.Dσ σ η x) = ∫ x', ∫ v, h (D.rσ σ x + D.β * v) ∂(η x') ∂(D.Pσ σ x) := by
  have := D.isMarkov_Pσ σ
  rw [D.Dσ_apply σ η x, integral_map (D.measurable_affine_x σ x).aemeasurable
    hh.aestronglyMeasurable]
  refine Kernel.integral_comp ?_
  exact Integrable.of_bound ((hh.comp (D.measurable_affine_x σ x)).aestronglyMeasurable) M
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM _)

/-- (2.23) for an integrable test function. -/
theorem integral_Dσ' (σ : DDPPolicy X A) (η : Kernel X ℝ) [IsMarkovKernel η] {h : ℝ → ℝ}
    (hh : Measurable h) {x : X}
    (hint : Integrable (fun v => h (D.rσ σ x + D.β * v)) ((η ∘ₖ D.Pσ σ) x)) :
    ∫ z, h z ∂(D.Dσ σ η x) = ∫ x', ∫ v, h (D.rσ σ x + D.β * v) ∂(η x') ∂(D.Pσ σ x) := by
  rw [D.Dσ_apply σ η x, integral_map (D.measurable_affine_x σ x).aemeasurable
    hh.aestronglyMeasurable]
  exact Kernel.integral_comp hint

/-- `(P_σ ⊗ η)(x, ·)` has a finite first moment, at most that of `η`. -/
theorem comp_moment (σ : DDPPolicy X A) (η : DistValue X) {C : ℝ}
    (hC : ∀ x, ∫ z, |z| ∂(η.1 x) ≤ C) (x : X) :
    Integrable (fun z : ℝ => z) ((η.1 ∘ₖ D.Pσ σ) x) ∧ ∫ z, |z| ∂((η.1 ∘ₖ D.Pσ σ) x) ≤ C := by
  have := D.isMarkov_Pσ σ
  have := η.2.1
  have hint := η.2.2.1
  have hC0 : 0 ≤ C := (integral_nonneg fun _ => abs_nonneg _).trans (hC x)
  have hlin : ∫⁻ z, ‖z‖ₑ ∂((η.1 ∘ₖ D.Pσ σ) x) ≤ ENNReal.ofReal C := by
    rw [Kernel.lintegral_comp _ _ _ measurable_enorm]
    calc ∫⁻ b, ∫⁻ z, ‖z‖ₑ ∂(η.1 b) ∂(D.Pσ σ x) ≤ ∫⁻ _b, ENNReal.ofReal C ∂(D.Pσ σ x) := by
          refine lintegral_mono fun b => ?_
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hint b)]
          exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC b)
      _ = ENNReal.ofReal C := by simp
  have hI : Integrable (fun z : ℝ => z) ((η.1 ∘ₖ D.Pσ σ) x) :=
    ⟨measurable_id.aestronglyMeasurable, lt_of_le_of_lt hlin ENNReal.ofReal_lt_top⟩
  refine ⟨hI, ?_⟩
  have e := ofReal_integral_norm_eq_lintegral_enorm hI
  rw [← ENNReal.ofReal_le_ofReal_iff hC0]
  simp only [Real.norm_eq_abs] at e
  rw [e]
  exact hlin

/-- **Proposition 2.3.2** (p. 85), self-map: `D_σ` maps `ℋ` into itself; if `|r| ≤ M` and the
first moments of `η` are at most `C`, those of `D_σ η` are at most `M + βC`. -/
noncomputable def Dσℋ (σ : DDPPolicy X A) (η : DistValue X) : DistValue X := by
  have := D.isMarkov_Pσ σ
  have := η.2.1
  refine ⟨D.Dσ σ η.1, ?_, fun x => ?_, ?_⟩
  · unfold Dσ
    exact Kernel.IsMarkovKernel.map _ (D.measurable_affine σ)
  · obtain ⟨hI, -⟩ := D.comp_moment σ η η.2.2.2.choose_spec x
    rw [D.Dσ_apply σ η.1 x]
    have e := integrable_map_measure (μ := (η.1 ∘ₖ D.Pσ σ) x) (g := fun z : ℝ => z)
      (f := fun v => D.rσ σ x + D.β * v) measurable_id.aestronglyMeasurable
      (D.measurable_affine_x σ x).aemeasurable
    rw [e]
    exact (integrable_const _).add (hI.const_mul _)
  · obtain ⟨M, hM⟩ := D.r_bdd
    refine ⟨M + D.β * η.2.2.2.choose, fun x => ?_⟩
    obtain ⟨hI, hle⟩ := D.comp_moment σ η η.2.2.2.choose_spec x
    rw [D.Dσ_apply σ η.1 x, integral_map (D.measurable_affine_x σ x).aemeasurable
      continuous_abs.aestronglyMeasurable]
    calc ∫ v, |D.rσ σ x + D.β * v| ∂((η.1 ∘ₖ D.Pσ σ) x)
        ≤ ∫ v, (M + D.β * |v|) ∂((η.1 ∘ₖ D.Pσ σ) x) := by
          refine integral_mono ((integrable_const _).add (hI.const_mul _)).abs
            ((integrable_const _).add (hI.abs.const_mul _)) fun v => ?_
          refine (abs_add_le _ _).trans (add_le_add (hM _) ?_)
          rw [abs_mul, abs_of_nonneg D.β_nonneg]
      _ = M + D.β * ∫ v, |v| ∂((η.1 ∘ₖ D.Pσ σ) x) := by
          rw [integral_add (integrable_const _) (hI.abs.const_mul _), integral_const,
            integral_const_mul]
          simp
      _ ≤ M + D.β * η.2.2.2.choose := by
          gcongr
          exact D.β_nonneg

theorem Dσℋ_coe (σ : DDPPolicy X A) (η : DistValue X) : (D.Dσℋ σ η).1 = D.Dσ σ η.1 := rfl

/-- **Proposition 2.3.2** (p. 85), order preservation: `η ⊴ η'` implies `D_σ η ⊴ D_σ η'`. -/
theorem Dσℋ_mono (σ : DDPPolicy X A) : Monotone (D.Dσℋ σ) := by
  intro η η' hle x h hmono ⟨M, hM⟩
  have := D.isMarkov_Pσ σ
  have := η.2.1
  have := η'.2.1
  have hmeas : Measurable h := hmono.measurable
  rw [Dσℋ_coe, Dσℋ_coe, D.integral_Dσ σ η.1 hmeas hM, D.integral_Dσ σ η'.1 hmeas hM]
  set g : ℝ → ℝ := fun v => h (D.rσ σ x + D.β * v)
  have hgm : Monotone g := fun v w hvw =>
    hmono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvw D.β_nonneg))
  have hgmeas : Measurable g := hmeas.comp (D.measurable_affine_x σ x)
  have hgb : ∀ v, |g v| ≤ M := fun v => hM _
  have hint : ∀ (κ : Kernel X ℝ), IsMarkovKernel κ →
      Integrable (fun x' => ∫ v, g v ∂(κ x')) (D.Pσ σ x) := fun κ _ =>
    Integrable.of_bound (hgmeas.stronglyMeasurable.integral_kernel (κ := κ)).aestronglyMeasurable
      M (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs]
        have := norm_integral_le_of_norm_le_const (μ := κ x') (f := g) (C := M)
          (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hgb v)
        simpa using this)
  exact integral_mono (hint η.1 η.2.1) (hint η'.1 η'.2.1) fun x' => hle x' g hgm ⟨M, hgb⟩

/-- The distributional ADP `(ℋ, 𝕋_DDP)` (§2.3.4.1), by Proposition 2.3.2. -/
noncomputable def ddpADP [Nonempty A] : ADP (DistValue X) (DDPPolicy X A) where
  T σ := D.Dσℋ σ
  mono σ := D.Dσℋ_mono σ
  nonempty := ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩

/-! ### Exercise 2.3.11 -/

/-- A `1`-Lipschitz `h` is integrable under a measure with finite first moment. -/
theorem integrable_of_lipschitz {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun z : ℝ => z) μ) {h : ℝ → ℝ} {K : NNReal} (hh : LipschitzWith K h) :
    Integrable h μ := by
  refine Integrable.mono' ((integrable_const |h 0|).add (hμ.abs.const_mul K))
    hh.continuous.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have := hh.dist_le_mul z 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  calc |h z| = |h 0 + (h z - h 0)| := by ring_nf
    _ ≤ |h 0| + |h z - h 0| := abs_add_le _ _
    _ ≤ |h 0| + K * |z| := add_le_add le_rfl this

/-- **Exercise 2.3.11** (p. 87), in test-function form: if every `1`-Lipschitz `h` has
`∫ h dη(x') − ∫ h dη'(x') ≤ d` at every `x'`, then every `1`-Lipschitz `h` has
`∫ h d(D_σ η)(x) − ∫ h d(D_σ η')(x) ≤ βd`: the map `v ↦ h(r_σ(x) + βv)` is `β`-Lipschitz. -/
theorem lipschitz_contraction (σ : DDPPolicy X A) (η η' : DistValue X) {d : ℝ}
    (hd : ∀ x' (h : ℝ → ℝ), LipschitzWith 1 h →
      ∫ z, h z ∂(η.1 x') - ∫ z, h z ∂(η'.1 x') ≤ d)
    (x : X) {h : ℝ → ℝ} (hh : LipschitzWith 1 h) :
    ∫ z, h z ∂(D.Dσ σ η.1 x) - ∫ z, h z ∂(D.Dσ σ η'.1 x) ≤ D.β * d := by
  have := D.isMarkov_Pσ σ
  have := η.2.1
  have := η'.2.1
  set g : ℝ → ℝ := fun v => h (D.rσ σ x + D.β * v)
  have hgL : LipschitzWith (Real.toNNReal D.β) g := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ D.β_nonneg]
    have := hh.dist_le_mul (D.rσ σ x + D.β * v) (D.rσ σ x + D.β * w)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
    calc |g v - g w| ≤ |D.rσ σ x + D.β * v - (D.rσ σ x + D.β * w)| := this
      _ = D.β * |v - w| := by
          rw [show D.rσ σ x + D.β * v - (D.rσ σ x + D.β * w) = D.β * (v - w) by ring, abs_mul,
            abs_of_nonneg D.β_nonneg]
  -- the integrable form of (2.23) for `h`
  have hcomp : ∀ ν : DistValue X, ∫ z, h z ∂(D.Dσ σ ν.1 x) =
      ∫ x', ∫ v, g v ∂(ν.1 x') ∂(D.Pσ σ x) := fun ν => by
    have := ν.2.1
    obtain ⟨hI, -⟩ := D.comp_moment σ ν ν.2.2.2.choose_spec x
    exact D.integral_Dσ' σ ν.1 hh.continuous.measurable
      (integrable_of_lipschitz (μ := (ν.1 ∘ₖ D.Pσ σ) x) hI hgL)
  -- `x' ↦ ∫ g dν(x')` is integrable under `P_σ(x, ·)`
  have hout : ∀ ν : DistValue X, Integrable (fun x' => ∫ v, g v ∂(ν.1 x')) (D.Pσ σ x) := by
    intro ν
    have := ν.2.1
    obtain ⟨C, hC⟩ := ν.2.2.2
    refine Integrable.of_bound
      (hgL.continuous.measurable.stronglyMeasurable.integral_kernel (κ := ν.1)).aestronglyMeasurable
      (|g 0| + D.β * C) (Eventually.of_forall fun x' => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    have hgi := integrable_of_lipschitz (ν.2.2.1 x') hgL
    calc ∫ v, |g v| ∂(ν.1 x') ≤ ∫ v, (|g 0| + D.β * |v|) ∂(ν.1 x') := by
          refine integral_mono hgi.abs ((integrable_const _).add
            ((ν.2.2.1 x').abs.const_mul _)) fun v => ?_
          have := hgL.dist_le_mul v 0
          rw [Real.dist_eq, Real.dist_eq, sub_zero, Real.coe_toNNReal _ D.β_nonneg] at this
          calc |g v| = |g 0 + (g v - g 0)| := by ring_nf
            _ ≤ |g 0| + |g v - g 0| := abs_add_le _ _
            _ ≤ |g 0| + D.β * |v| := add_le_add le_rfl this
      _ = |g 0| + D.β * ∫ v, |v| ∂(ν.1 x') := by
          rw [integral_add (integrable_const _) ((ν.2.2.1 x').abs.const_mul _), integral_const,
            integral_const_mul]
          simp
      _ ≤ |g 0| + D.β * C := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hC x') D.β_nonneg)
  rw [hcomp η, hcomp η', ← integral_sub (hout η) (hout η')]
  -- each inner difference is at most `βd`
  have hinner : ∀ x', ∫ v, g v ∂(η.1 x') - ∫ v, g v ∂(η'.1 x') ≤ D.β * d := by
    intro x'
    rcases D.β_nonneg.eq_or_lt with hβ | hβ
    · -- `β = 0`: `g` is constant
      have hg : g = fun _ => h (D.rσ σ x) := by funext v; simp [g, ← hβ]
      simp [hg, ← hβ]
    · -- `g/β` is `1`-Lipschitz
      have hL1 : LipschitzWith 1 fun v => g v / D.β := by
        refine LipschitzWith.of_dist_le_mul fun v w => ?_
        rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← sub_div, abs_div,
          abs_of_pos hβ, div_le_iff₀ hβ]
        have := hgL.dist_le_mul v w
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ D.β_nonneg] at this
        linarith
      have := hd x' _ hL1
      rw [integral_div, integral_div, ← sub_div, div_le_iff₀ hβ] at this
      linarith
  calc ∫ x', (∫ v, g v ∂(η.1 x') - ∫ v, g v ∂(η'.1 x')) ∂(D.Pσ σ x)
      ≤ ∫ _x', D.β * d ∂(D.Pσ σ x) :=
        integral_mono ((hout η).sub (hout η')) (integrable_const _) hinner
    _ = D.β * d := by simp

/-- The Wasserstein-1 distance `W₁(μ, ν) = sup_{‖h‖_Lip ≤ 1} (∫ h dμ − ∫ h dν)` (§2.3.4.2). -/
noncomputable def W1 (μ ν : Measure ℝ) : ℝ :=
  sSup {t | ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧ t = ∫ z, h z ∂μ - ∫ z, h z ∂ν}

/-- **Exercise 2.3.11** (p. 87): `D_σ` is a `β`-contraction for the supremum Wasserstein
distance: if `W₁(η(x'), η'(x')) ≤ d` for all `x'`, then `W₁((D_σ η)(x), (D_σ η')(x)) ≤ βd`. -/
theorem W1_contraction (σ : DDPPolicy X A) (η η' : DistValue X) {d : ℝ}
    (hbdd : ∀ x', BddAbove {t | ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧
      t = ∫ z, h z ∂(η.1 x') - ∫ z, h z ∂(η'.1 x')})
    (hd : ∀ x', W1 (η.1 x') (η'.1 x') ≤ d) (x : X) :
    W1 (D.Dσ σ η.1 x) (D.Dσ σ η'.1 x) ≤ D.β * d := by
  refine csSup_le ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken zero_le_one, by simp⟩ ?_
  rintro _ ⟨h, hh, rfl⟩
  exact D.lipschitz_contraction σ η η' (fun x' h hh =>
    (le_csSup (hbdd x') ⟨h, hh, rfl⟩).trans (hd x')) x hh

end DDP

end SargentStachurski.AbstractDecisionProcesses
