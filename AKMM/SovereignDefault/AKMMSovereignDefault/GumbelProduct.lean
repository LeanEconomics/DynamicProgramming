/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import AKMMSovereignDefault.ExtremeValue

/-!
# Logit choice probabilities from independent Gumbel shocks

AKMM, Appendix 24.A.1, Method 3, p. 900: "the `ε` shocks follow an i.i.d. process"; the
probability that the sovereign picks an alternative "depends on `ε_m` taking a sufficiently
larger value relative to the other shocks".

The standard Gumbel law `γ` has density `g(x) = e^{−x} exp(−e^{−x})`; it is a probability
measure with c.d.f. `γ(−∞, a] = exp(−e^{−a})` (`gp_isProbabilityMeasure`, `gp_measure_Iic`).
For finitely many alternatives `k ∈ Fin (n + 1)` with values `v_k` and i.i.d. shocks
`ε ∼ γ^{⊗(n+1)}` (the product measure),
`Pr(v_i + ε_i ≥ v_k + ε_k for all k) = e^{v_i}/Σ_k e^{v_k}` (`ev_logit_of_gumbel`): the
probability is computed by splitting off the coordinate `i` (Mathlib's
`measurePreserving_piFinSuccAbove`), Tonelli, and `∫ e^{−x} exp(−c e^{−x}) dx = 1/c`. This
derives, rather than assumes, the conditioning formula used in `ExtremeValue`.
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology Finset

/-- The standard Gumbel law, with density `ev_gumbelPDF`. -/
noncomputable abbrev ev_gumbel : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (ev_gumbelPDF x)

/-- The Gumbel density is continuous. -/
theorem gp_pdf_continuous : Continuous ev_gumbelPDF := by
  unfold ev_gumbelPDF; fun_prop

/-- The Gumbel density is integrable. -/
theorem gp_pdf_integrable : Integrable ev_gumbelPDF := by
  have h := (ev_integrable one_pos).2.2
  exact (by simpa only [one_mul] using h :
    Integrable fun x => Real.exp (-x) * Real.exp (-Real.exp (-x)))

/-- The Gumbel density is nonnegative. -/
theorem gp_pdf_nonneg (x : ℝ) : 0 ≤ ev_gumbelPDF x :=
  mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- The Gumbel c.d.f. is an antiderivative of the density. -/
theorem gp_hasDerivAt (x : ℝ) : HasDerivAt ev_gumbelCDF (ev_gumbelPDF x) x := by
  have h := ev_hasDerivAt one_pos x
  simp only [one_mul, div_one] at h
  exact h

/-- `∫_{(−∞, a]} g = exp(−e^{−a})`. -/
theorem gp_integral_Iic (a : ℝ) : ∫ x in Set.Iic a, ev_gumbelPDF x = ev_gumbelCDF a := by
  have hbot : Tendsto ev_gumbelCDF atBot (𝓝 0) := by
    have h := (ev_integrable one_pos).1
    exact (by simpa only [one_mul, div_one] using h :
      Tendsto (fun x => Real.exp (-Real.exp (-x))) atBot (𝓝 0))
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => gp_hasDerivAt x)
    gp_pdf_integrable.integrableOn hbot, sub_zero]

/-- The Gumbel law of `(−∞, a]` is `exp(−e^{−a})`. -/
theorem gp_measure_Iic (a : ℝ) : ev_gumbel (Set.Iic a) = ENNReal.ofReal (ev_gumbelCDF a) := by
  rw [withDensity_apply _ measurableSet_Iic, ← gp_integral_Iic,
    ofReal_integral_eq_lintegral_ofReal gp_pdf_integrable.integrableOn
      (Eventually.of_forall gp_pdf_nonneg)]

/-- The Gumbel law is a probability measure. -/
theorem gp_isProbabilityMeasure : IsProbabilityMeasure ev_gumbel := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal gp_pdf_integrable (Eventually.of_forall gp_pdf_nonneg)]
  have h := ev_integral one_pos
  simp only [one_mul, div_one] at h
  rw [show (∫ x, ev_gumbelPDF x) = 1 from h, ENNReal.ofReal_one]

/-- **Logit from i.i.d. Gumbel shocks** (AKMM, p. 900, Method 3). With values `v_k`,
`k ∈ Fin (n + 1)`, and independent standard Gumbel shocks `ε_k` (the product law), the
probability that alternative `i` attains `max_k (v_k + ε_k)` is `e^{v_i}/Σ_k e^{v_k}`. -/
theorem ev_logit_of_gumbel {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => ev_gumbel) {ε | ∀ k, v k + ε k ≤ v i + ε i} =
      ENNReal.ofReal (Real.exp (v i) / ∑ k, Real.exp (v k)) := by
  have hP : IsProbabilityMeasure ev_gumbel := gp_isProbabilityMeasure
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ev_gumbel) i
  set S : Set (ℝ × (Fin n → ℝ)) := {p | ∀ j, v (i.succAbove j) + p.2 j ≤ v i + p.1} with hSdef
  have hS : MeasurableSet S := by
    have : S = ⋂ j, {p : ℝ × (Fin n → ℝ) | v (i.succAbove j) + p.2 j ≤ v i + p.1} := by
      ext p; simp [hSdef]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  have hA : {ε : Fin (n + 1) → ℝ | ∀ k, v k + ε k ≤ v i + ε i} = e ⁻¹' S := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hSdef, e,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Equiv.coe_fn_symm_mk,
      Fin.removeNth]
    rw [Fin.forall_iff_succAbove i]
    simp
  rw [hA, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply hS]
  -- the sections are boxes
  have hsec : ∀ x : ℝ, Prod.mk x ⁻¹' S =
      Set.univ.pi fun j => Set.Iic (v i + x - v (i.succAbove j)) := by
    intro x
    ext p
    simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Iic, true_implies]
    exact forall_congr' fun j => by constructor <;> intro h <;> linarith
  simp only [hsec, Measure.pi_pi, gp_measure_Iic]
  -- move to a real integral
  set c := ∑ k, Real.exp (v k - v i) with hc
  have hcpos : 0 < c := sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  have hpt : ∀ x, ev_gumbelPDF x * ∏ j, ev_gumbelCDF (v i + x - v (i.succAbove j)) =
      Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
    intro x
    unfold ev_gumbelPDF ev_gumbelCDF
    rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hc, Fin.sum_univ_succAbove _ i, sub_self, Real.exp_zero, add_mul, one_mul, sum_mul,
      neg_add, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [← Real.exp_add]
    congr 2
    ring
  have hmeasG : Measurable fun x => ∏ j, ENNReal.ofReal
      (ev_gumbelCDF (v i + x - v (i.succAbove j))) := by
    unfold ev_gumbelCDF; fun_prop
  rw [show ev_gumbel = volume.withDensity (fun x => ENNReal.ofReal (ev_gumbelPDF x)) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ (f := fun x => ENNReal.ofReal (ev_gumbelPDF x))
      gp_pdf_continuous.measurable.ennreal_ofReal.aemeasurable hmeasG.aemeasurable]
  have hfun : ((fun x => ENNReal.ofReal (ev_gumbelPDF x)) * fun x => ∏ j, ENNReal.ofReal
      (ev_gumbelCDF (v i + x - v (i.succAbove j)))) =
      fun x => ENNReal.ofReal (Real.exp (-x) * Real.exp (-(c * Real.exp (-x)))) := by
    funext x
    rw [Pi.mul_apply, ← ENNReal.ofReal_prod_of_nonneg (s := univ)
      (f := fun j => ev_gumbelCDF (v i + x - v (i.succAbove j))) (fun j _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (gp_pdf_nonneg x), hpt x]
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (ev_integrable hcpos).2.2
    (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ev_integral hcpos]
  congr 1
  have hS' : ∑ k, Real.exp (v k - v i) = (∑ k, Real.exp (v k)) / Real.exp (v i) := by
    rw [sum_div]
    exact sum_congr rfl fun k _ => by rw [Real.exp_sub]
  rw [hc, hS', one_div, inv_div]

/-- The derived probability agrees with the conditioning formula of `ExtremeValue`. -/
theorem ev_choiceProb_eq_gumbel {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => ev_gumbel) {ε | ∀ k, v k + ε k ≤ v i + ε i} =
      ENNReal.ofReal (ev_choiceProb v i) := by
  rw [ev_logit_of_gumbel, ev_logit]

end AKMM.SovereignDefault
