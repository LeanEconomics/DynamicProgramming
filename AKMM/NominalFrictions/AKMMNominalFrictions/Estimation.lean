/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Estimating the Phillips curve: instruments and marginal cost

AKMM, §18.5.2, pp. 553–554.

* `gg_rewrite`: Galí–Gertler's rewriting `π_t = κx_t + βπ_{t+1} + ζ_t`,
  `ζ_t = η_t − β(π_{t+1} − E_tπ_{t+1})`.
* `gg_orthogonal`, `gg_cov_zero` (footnote 16): if `E_{t−1}η_t = 0`, any bounded instrument
  `z_{t−1}` known at `t − 1` satisfies `E[z_{t−1}ζ_t] = 0` and `cov(z_{t−1}, ζ_t) = 0`, by the
  law of iterated expectations (`ℱ_{t−1} ≤ ℱ_t`). The footnote expands `E[z(η − β e)]` as
  `E[zη] + βE[z e]`; the sign is `−` (`gg_expand`), harmless because both terms vanish.
* `gg_mpl`, `gg_marginal_cost`: with `Y = A K^{α_K} L^{α_L}` the marginal product of labour is
  `α_L Y/L`, so real marginal cost `w/(∂Y/∂L) = s_L/α_L` with `s_L = wL/Y`, and
  `log mc = log s_L − log α_L` (`gg_log_mc`).
-/

namespace AKMM.NominalFrictions

open MeasureTheory

/-- AKMM, p. 553: replacing expected by realised inflation,
`π_t = κx_t + βE_tπ_{t+1} + η_t` iff `π_t = κx_t + βπ_{t+1} + ζ_t`,
`ζ_t = η_t − β(π_{t+1} − E_tπ_{t+1})`. -/
theorem gg_rewrite {κ β πt πn Eπ x η : ℝ} :
    πt = κ * x + β * Eπ + η ↔ πt = κ * x + β * πn + (η - β * (πn - Eπ)) := by
  constructor <;> intro h <;> linarith

/-- AKMM, footnote 16, p. 553: the correct expansion
`E[z(η − β e)] = E[zη] − βE[z e]` (the footnote prints `+`). -/
theorem gg_expand {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {z η e : Ω → ℝ} (β : ℝ)
    (h1 : Integrable (fun ω => z ω * η ω) μ) (h2 : Integrable (fun ω => z ω * e ω) μ) :
    ∫ ω, z ω * (η ω - β * e ω) ∂μ = ∫ ω, z ω * η ω ∂μ - β * ∫ ω, z ω * e ω ∂μ := by
  have : (fun ω => z ω * (η ω - β * e ω)) = fun ω => z ω * η ω - β * (z ω * e ω) := by
    funext ω; ring
  rw [this, integral_sub h1 (h2.const_mul β), integral_const_mul]

/-- The law of iterated expectations with a known bounded factor: if `z` is bounded and
`m`-measurable, `m ≤ mΩ`, `f` integrable, then `E[z f] = E[z E[f|m]]`. -/
theorem gg_lie {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {z f : Ω → ℝ} {C : ℝ} (hz : StronglyMeasurable[m] z)
    (hzb : ∀ ω, |z ω| ≤ C) (hf : Integrable f μ) :
    ∫ ω, z ω * f ω ∂μ = ∫ ω, z ω * μ[f | m] ω ∂μ := by
  have hzae : AEStronglyMeasurable z μ := (hz.mono hm).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, ‖z ω‖ ≤ C := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hzb ω
  have hzf : Integrable (z * f) μ := hf.bdd_mul hzae hb
  have e : ∫ ω, z ω * f ω ∂μ = ∫ ω, (z * f) ω ∂μ := rfl
  rw [e, ← integral_condExp hm (f := z * f)]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hz hzf hf)

/-- **AKMM, footnote 16, p. 553**: let `ℱ_{t−1} ≤ ℱ_t` be σ-algebras, `z` a bounded
`ℱ_{t−1}`-measurable instrument, `η` and `π_{t+1}` integrable, and `E_{t−1}η = 0`. Then
`E[z ζ] = 0` for `ζ = η − β(π_{t+1} − E_tπ_{t+1})`. -/
theorem gg_orthogonal {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hmm : m ≤ m') (hm' : m' ≤ mΩ) {z η p : Ω → ℝ}
    {β C : ℝ} (hz : StronglyMeasurable[m] z) (hzb : ∀ ω, |z ω| ≤ C) (hη : Integrable η μ)
    (hp : Integrable p μ) (hE : μ[η | m] =ᵐ[μ] 0) :
    ∫ ω, z ω * (η ω - β * (p ω - μ[p | m'] ω)) ∂μ = 0 := by
  have hzae : AEStronglyMeasurable z μ := ((hz.mono hmm).mono hm').aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, ‖z ω‖ ≤ C := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hzb ω
  have he : Integrable (fun ω => p ω - μ[p | m'] ω) μ := hp.sub integrable_condExp
  rw [gg_expand β (hη.bdd_mul hzae hb) (he.bdd_mul hzae hb)]
  have h1 : ∫ ω, z ω * η ω ∂μ = 0 := by
    rw [gg_lie (hmm.trans hm') hz hzb hη]
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by
      filter_upwards [hE] with ω hω
      simp [hω])]
    simp
  have h2 : ∫ ω, z ω * (p ω - μ[p | m'] ω) ∂μ = 0 := by
    have hz' : StronglyMeasurable[m'] z := hz.mono hmm
    have e : (fun ω => z ω * (p ω - μ[p | m'] ω)) =
        fun ω => z ω * p ω - z ω * μ[p | m'] ω := by funext ω; ring
    rw [e, integral_sub (hp.bdd_mul hzae hb) (integrable_condExp.bdd_mul hzae hb),
      gg_lie hm' hz' hzb hp, sub_self]
  rw [h1, h2]; ring

/-- **AKMM, footnote 16, p. 553**: under the assumptions of `gg_orthogonal`,
`cov(z_{t−1}, ζ_t) = E[zζ] − E[z]E[ζ] = 0` (`E[ζ] = 0` is the case `z = 1`). -/
theorem gg_cov_zero {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hmm : m ≤ m') (hm' : m' ≤ mΩ) {z η p : Ω → ℝ}
    {β C : ℝ} (hz : StronglyMeasurable[m] z) (hzb : ∀ ω, |z ω| ≤ C) (hη : Integrable η μ)
    (hp : Integrable p μ) (hE : μ[η | m] =ᵐ[μ] 0) :
    ∫ ω, z ω * (η ω - β * (p ω - μ[p | m'] ω)) ∂μ -
      (∫ ω, z ω ∂μ) * ∫ ω, (η ω - β * (p ω - μ[p | m'] ω)) ∂μ = 0 := by
  have h1 := gg_orthogonal hmm hm' hz hzb hη hp hE (β := β)
  have h0 := gg_orthogonal (z := fun _ => (1 : ℝ)) (C := 1) hmm hm' stronglyMeasurable_const
    (fun _ => by simp) hη hp hE (β := β)
  simp only [one_mul] at h0
  rw [h1, h0]; ring

/-- AKMM, p. 554: with `Y = A K^{α_K} L^{α_L}` (`K` predetermined), the marginal product of
labour is `∂Y/∂L = α_L Y/L`. -/
theorem gg_mpl {A K αK αL L : ℝ} (hL : 0 < L) :
    HasDerivAt (fun l => A * K ^ αK * l ^ αL) (αL * (A * K ^ αK * L ^ αL) / L) L := by
  have h := (Real.hasDerivAt_rpow_const (p := αL) (Or.inl hL.ne')).const_mul (A * K ^ αK)
  convert h using 1
  rw [Real.rpow_sub_one hL.ne']
  field_simp

/-- **AKMM, p. 554**: real marginal cost `mc = w/(∂Y/∂L) = s_L/α_L`, with the labour share
`s_L = wL/Y` (`α_L ≠ 0`, `Y, L > 0`). -/
theorem gg_marginal_cost {w Y L αL : ℝ} (hY : 0 < Y) (hL : 0 < L) (hα : αL ≠ 0) :
    w / (αL * Y / L) = w * L / Y / αL := by
  field_simp

/-- AKMM, p. 554: "the log of real marginal costs are given as the log of the labor share"
(up to the constant `log α_L`): `log mc = log s_L − log α_L` for `w, Y, L, α_L > 0`. -/
theorem gg_log_mc {w Y L αL : ℝ} (hw : 0 < w) (hY : 0 < Y) (hL : 0 < L) (hα : 0 < αL) :
    Real.log (w / (αL * Y / L)) = Real.log (w * L / Y) - Real.log αL := by
  rw [gg_marginal_cost hY hL hα.ne', Real.log_div (by positivity) hα.ne']

end AKMM.NominalFrictions
