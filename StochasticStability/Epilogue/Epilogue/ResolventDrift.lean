/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.ExponentialErgodic

/-!
# From the generator drift (20.31) to the resolvent chain (MT §20.3, p. 527)

The proof of Theorem 20.3.2 "translates a Lyapunov function for the process to the sampled
chain". With the drift (20.31) in its integrated (Dynkin) form
`PᵗV + β∫₀ᵗ PˢV ds ≤ V + b∫₀ᵗ Pˢ(·, C) ds`, the sampled (resolvent) chain `R_α` satisfies
`(α + β) R_αV ≤ αV + b R_α(·, C)`, a (V4)-type drift for `R_α` with rate `α/(α+β)` (`< 1` when
`β > 0`).

* `lintegral_exp_Ici`, `lintegral_exp_mul_lintegral_Ioc` (the Laplace–Tonelli identity);
* `MarkovSemigroup.lintegral_resolventKernel`: `∫ g dR_α(x, ·) = ∫₀^∞ αe^{−αt} Pᵗg(x) dt`;
* `MarkovSemigroup.resolventKernel_drift`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- `∫_{t ≥ s} αe^{−αt} dt = e^{−αs}` in `[0, ∞]`. -/
theorem lintegral_exp_Ici {α : ℝ} (hα : 0 < α) (s : ℝ) :
    ∫⁻ t in Ici s, ENNReal.ofReal (α * Real.exp (-α * t)) =
      ENNReal.ofReal (Real.exp (-α * s)) := by
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm, ← ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_exp_mul_Ioi (by linarith : -α < 0) s).const_mul α)
    (Eventually.of_forall fun t => (mul_pos hα (Real.exp_pos _)).le), integral_const_mul,
    MarkovSemigroup.integral_exp_neg_Ioi' hα, mul_div_cancel₀ _ hα.ne']

/-- **The Laplace–Tonelli identity**: `∫₀^∞ αe^{−αt} ∫₀ᵗ φ(s) ds dt = ∫₀^∞ e^{−αs} φ(s) ds` for
measurable `φ ≥ 0`. -/
theorem lintegral_exp_mul_lintegral_Ioc {α : ℝ} (hα : 0 < α) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (α * Real.exp (-α * t)) * ∫⁻ s in Ioc 0 t, φ s =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-α * s)) * φ s := by
  have he : Measurable fun t : ℝ => ENNReal.ofReal (α * Real.exp (-α * t)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
  have hinner : ∀ t, ∫⁻ s in Ioc 0 t, φ s = ∫⁻ s in Ioi 0, (Iic t).indicator φ s := fun t => by
    rw [setLIntegral_indicator measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  simp_rw [hinner]
  have hF : Measurable (Function.uncurry fun (t s : ℝ) =>
      ENNReal.ofReal (α * Real.exp (-α * t)) * (Iic t).indicator φ s) := by
    have : (Function.uncurry fun (t s : ℝ) =>
        ENNReal.ofReal (α * Real.exp (-α * t)) * (Iic t).indicator φ s) =
        fun p : ℝ × ℝ => ENNReal.ofReal (α * Real.exp (-α * p.1)) *
          (if p.2 ≤ p.1 then φ p.2 else 0) := by
      funext p; rw [Function.uncurry_apply_pair, indicator_apply]; rfl
    rw [this]
    exact (he.comp measurable_fst).mul (Measurable.ite (measurableSet_le measurable_snd
      measurable_fst) (hφ.comp measurable_snd) measurable_const)
  have hpull : ∀ t, ENNReal.ofReal (α * Real.exp (-α * t)) * ∫⁻ s in Ioi 0, (Iic t).indicator φ s =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (α * Real.exp (-α * t)) * (Iic t).indicator φ s :=
    fun t => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  simp_rw [hpull]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hset : ∀ t, ENNReal.ofReal (α * Real.exp (-α * t)) * (Iic t).indicator φ s =
      (Ici s).indicator (fun t => ENNReal.ofReal (α * Real.exp (-α * t)) * φ s) t := fun t => by
    by_cases h : s ≤ t
    · rw [indicator_of_mem (mem_Iic.2 h), indicator_of_mem (mem_Ici.2 h)]
    · rw [indicator_of_notMem (fun h' => h (mem_Iic.1 h')),
        indicator_of_notMem (fun h' => h (mem_Ici.1 h')), mul_zero]
  simp_rw [hset]
  rw [setLIntegral_indicator measurableSet_Ici, inter_eq_left.2 (Ici_subset_Ioi.2 hs),
    lintegral_mul_const _ he, lintegral_exp_Ici hα]

namespace MarkovSemigroup

/-- `∫ g dR_α(x, ·) = ∫₀^∞ αe^{−αt} Pᵗg(x) dt` for measurable `g ≥ 0`. -/
theorem lintegral_resolventKernel (S : MarkovSemigroup X) {α : ℝ} (hα : 0 < α) {g : X → ℝ≥0∞}
    (hg : Measurable g) (x : X) :
    ∫⁻ y, g y ∂S.resolventKernel α x =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (α * Real.exp (-α * t)) * ∫⁻ y, g y ∂S.K (t, x) := by
  have := isProbabilityMeasure_expLaw hα
  have hK : Measurable fun p : ℝ × X => ∫⁻ y, g y ∂S.K p := hg.lintegral_kernel
  rw [resolventKernel, Kernel.lintegral_comp _ _ _ hg, Kernel.prod_apply, Kernel.const_apply,
    Kernel.id_apply, Measure.prod_dirac, lintegral_map hK (by fun_prop),
    expLaw, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (g := fun t => ∫⁻ y, g y ∂S.K (t, x)) (hK.comp (measurable_id.prodMk measurable_const))]
  rfl

/-- **From the generator drift to the sampled chain** (MT p. 527: "translate a Lyapunov function
... to the sampled chain"): if `V` satisfies the drift (20.31) `AV ≤ −βV + b1_C` in the integrated
(Dynkin) form `PᵗV + β∫₀ᵗ PˢV ds ≤ V + b∫₀ᵗ Pˢ(·, C) ds`, then the resolvent chain satisfies
`(α + β) R_αV ≤ αV + b R_α(·, C)`, hence `R_αV ≤ α/(α+β) V + b/(α+β)`. -/
theorem resolventKernel_drift (S : MarkovSemigroup X) {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    {V : X → ℝ≥0∞} (hV : Measurable V) {b : ℝ≥0∞} {C : Set X} (hC : MeasurableSet C)
    (hdrift : ∀ x t, 0 ≤ t → ∫⁻ y, V y ∂S.K (t, x) +
      ENNReal.ofReal β * ∫⁻ s in Ioc 0 t, ∫⁻ y, V y ∂S.K (s, x) ≤
        V x + b * ∫⁻ s in Ioc 0 t, S.K (s, x) C) (x : X) :
    ENNReal.ofReal (α + β) * ∫⁻ y, V y ∂S.resolventKernel α x ≤
      ENNReal.ofReal α * V x + b * S.resolventKernel α x C := by
  set e : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (α * Real.exp (-α * t)) with he
  have hem : Measurable e := ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
  set h : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, V y ∂S.K (s, x) with hh
  set k : ℝ → ℝ≥0∞ := fun s => S.K (s, x) C with hk
  have hhm : Measurable h :=
    (hV.lintegral_kernel (κ := S.K)).comp (measurable_id.prodMk measurable_const)
  have hkm : Measurable k := (S.K.measurable_coe hC).comp (measurable_id.prodMk measurable_const)
  -- the exponential law has mass one
  have he1 : ∫⁻ t in Ioi 0, e t = 1 := by
    have := lintegral_exp_Ici hα 0
    rwa [mul_zero, Real.exp_zero, ENNReal.ofReal_one, ← setLIntegral_congr Ioi_ae_eq_Ici] at this
  -- the Laplace–Tonelli identity, with `e^{−αs} = α⁻¹ e(s)`
  have hLT : ∀ φ : ℝ → ℝ≥0∞, Measurable φ →
      ∫⁻ t in Ioi 0, e t * ∫⁻ s in Ioc 0 t, φ s =
        ENNReal.ofReal α⁻¹ * ∫⁻ s in Ioi 0, e s * φ s := fun φ hφ => by
    rw [lintegral_exp_mul_lintegral_Ioc hα hφ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [← mul_assoc]
    congr 1
    change _ = ENNReal.ofReal α⁻¹ * ENNReal.ofReal (α * Real.exp (-α * s))
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hα.le), ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
  -- integrate the drift against the exponential law
  have hint : ∫⁻ t in Ioi 0, e t * (h t + ENNReal.ofReal β * ∫⁻ s in Ioc 0 t, h s) ≤
      ∫⁻ t in Ioi 0, e t * (V x + b * ∫⁻ s in Ioc 0 t, k s) :=
    setLIntegral_mono' measurableSet_Ioi fun t ht => mul_le_mul' le_rfl
      (hdrift x t (le_of_lt ht))
  have hIm : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → Measurable fun t => ∫⁻ s in Ioc 0 t, φ s :=
    fun φ hφ => by
      have : (fun t => ∫⁻ s in Ioc 0 t, φ s) = fun t => ∫⁻ s in Ioi 0, (Iic t).indicator φ s :=
        funext fun t => by rw [setLIntegral_indicator measurableSet_Iic, inter_comm, Ioi_inter_Iic]
      rw [this]
      refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
        (Iic p.1).indicator φ p.2) ?_
      have e2 : (fun p : ℝ × ℝ => (Iic p.1).indicator φ p.2) =
          fun p => if p.2 ≤ p.1 then φ p.2 else 0 := funext fun p => by
        rw [indicator_apply]; rfl
      rw [e2]
      exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (hφ.comp measurable_snd)
        measurable_const
  simp_rw [mul_add] at hint
  rw [lintegral_add_left (f := fun t => e t * h t) (hem.mul hhm),
    lintegral_add_left (f := fun t => e t * V x) (hem.mul measurable_const)] at hint
  simp_rw [mul_left_comm (e _) (ENNReal.ofReal β), mul_left_comm (e _) b] at hint
  rw [lintegral_const_mul (f := fun t => e t * ∫⁻ s in Ioc 0 t, h s) _ (hem.mul (hIm h hhm)),
    lintegral_const_mul (f := fun t => e t * ∫⁻ s in Ioc 0 t, k s) _ (hem.mul (hIm k hkm)),
    hLT h hhm, hLT k hkm, lintegral_mul_const _ hem, he1, one_mul] at hint
  rw [S.lintegral_resolventKernel hα hV x, ← lintegral_indicator_one hC,
    S.lintegral_resolventKernel hα (measurable_one.indicator hC) x]
  simp_rw [lintegral_indicator_one hC]
  change ENNReal.ofReal (α + β) * ∫⁻ t in Ioi 0, e t * h t ≤
    ENNReal.ofReal α * V x + b * ∫⁻ t in Ioi 0, e t * k t
  set I := ∫⁻ t in Ioi 0, e t * h t with hI
  set J := ∫⁻ t in Ioi 0, e t * k t with hJ
  have hαα : ENNReal.ofReal α * ENNReal.ofReal α⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hα.le, mul_inv_cancel₀ hα.ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal (α + β) * I = ENNReal.ofReal α * I + ENNReal.ofReal β * I := by
        rw [ENNReal.ofReal_add hα.le hβ, add_mul]
    _ = ENNReal.ofReal α * (I + ENNReal.ofReal β * (ENNReal.ofReal α⁻¹ * I)) := by
        rw [mul_add, mul_left_comm (ENNReal.ofReal α) (ENNReal.ofReal β),
          ← mul_assoc (ENNReal.ofReal α), hαα, one_mul]
    _ ≤ ENNReal.ofReal α * (V x + b * (ENNReal.ofReal α⁻¹ * J)) := mul_le_mul' le_rfl hint
    _ = ENNReal.ofReal α * V x + b * J := by
        rw [mul_add, mul_left_comm (ENNReal.ofReal α) b, ← mul_assoc (ENNReal.ofReal α), hαα,
          one_mul]

end MarkovSemigroup

end MeynTweedie.Epilogue
