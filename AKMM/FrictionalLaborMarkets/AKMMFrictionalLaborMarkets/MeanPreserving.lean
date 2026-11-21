/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.McCall
import AdditionalApplications.ContinuationValues
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mean-preserving spreads, frictional wage dispersion

AKMM, §20.9, pp. 623–625. A mean-preserving spread is Sargent–Stachurski's
`SargentStachurski.AdditionalApplications.IsMPS` (`x̃ = x + z` with `E[z | x] = 0`), exactly the
book's definition.

* `mps_mean`: a mean-preserving spread has the same mean.
* `mps_ibp`: integration by parts, `∫_0^x F(t)dt = ∫max{x − w, 0}dF(w)` for offers in `[0, ∞)`
  (by Fubini); with it, (20.56) reads `∫max{x − w, 0}dG ≥ ∫max{x − w, 0}dF`.
* `eq_20_56_of_mps`: a mean-preserving spread satisfies (20.56) (Jensen, via Sargent–Stachurski's
  `integral_max_le_of_isMPS`); `eq_20_56_not_sufficient`: (20.56) alone does not give a
  mean-preserving spread (point masses at `0` and `1`): the equivalence cited from
  Mas-Colell–Whinston–Green needs equal means.
* `eq_20_57`, `eq_20_58`: `∫_{w > x}(w − x)dF = μ_w − x + ∫max{x − w, 0}dF`, and (20.55) is
  `w* − b − β/(1 − β(1 − σ))(μ_w − w* + ∫_0^{w*}F) = 0`, whose left side is strictly increasing
  (`eq_20_58_strictMono`).
* `mc_mps_reservation`: under a mean-preserving spread of the offer distribution the reservation
  wage rises (p. 624).
* Frictional wage dispersion (pp. 624–625): `mm_formula`: with `λ = 1 − F(w*)`,
  `w^M = ∫_{w > w*} w dF/λ`, `ρ = b/w^M`, the mean–min ratio is
  `Mm = w^M/w* = (1 + βλ/(1 − β(1 − σ)))/(ρ + βλ/(1 − β(1 − σ)))` (`mm_formula_of_bellman` from
  the Bellman equations); `mm_back_of_envelope`: at `β = 0.996`, `σ = 0.034`, `λ = 0.45`,
  `ρ = 0.4` the formula gives `Mm > 1.04`, not the printed `1.031`.

The converse of `eq_20_56_of_mps` (Rothschild–Stiglitz) is cited by the book and not formalised.
-/

namespace AKMM.FrictionalLaborMarkets

open MeasureTheory Filter Topology ProbabilityTheory

/-- AKMM, p. 623: a mean-preserving spread `G` of `F` has the same mean as `F`. -/
theorem mps_mean {ψ φ : Measure ℝ} (h : SargentStachurski.AdditionalApplications.IsMPS ψ φ) :
    ∫ x, x ∂ψ = ∫ x, x ∂φ := by
  obtain ⟨Ω, mΩ, P, _, W, Z, hWm, hZm, hWi, hZi, hW, hWZ, hZ⟩ := h
  have hm : MeasurableSpace.comap W (inferInstance : MeasurableSpace ℝ) ≤ mΩ := hWm.comap_le
  change ∫ x, id x ∂ψ = ∫ x, id x ∂φ
  rw [← hW, ← hWZ, integral_map (hWm.add hZm).aemeasurable aestronglyMeasurable_id,
    integral_map hWm.aemeasurable aestronglyMeasurable_id]
  have hZ0 : ∫ ω, Z ω ∂P = 0 := by
    rw [← integral_condExp hm (μ := P) (f := Z), integral_congr_ae hZ]
    simp
  simp only [id, Pi.add_apply]
  rw [integral_add hWi hZi, hZ0, add_zero]

/-- AKMM, (20.58), p. 624 (**integration by parts**): for offers in `[0, ∞)`,
`∫_0^x F(t)dt = ∫max{x − w, 0}dF(w)` (equivalently `∫_0^x(w − x)dF = −∫_0^x F(w)dw`). -/
theorem mps_ibp {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ w ∂μ, 0 ≤ w) (x : ℝ) :
    ∫ t in Set.Icc 0 x, μ.real (Set.Iic t) = ∫ w, max (x - w) 0 ∂μ := by
  set ν : Measure ℝ := volume.restrict (Set.Icc 0 x) with hν
  have : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.mpr (by simp)
  set f : ℝ → ℝ → ℝ := fun w t ↦ (Set.Ici w).indicator (1 : ℝ → ℝ) t with hf
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have : Function.uncurry f = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (1 : ℝ × ℝ → ℝ) := by
      funext p
      simp only [Function.uncurry, hf, Set.indicator_apply, Set.mem_Ici, Pi.one_apply]
      rfl
    rw [this]
    exact (integrable_const (1 : ℝ)).indicator hS
  have inner_t : ∀ t, ∫ w, f w t ∂μ = μ.real (Set.Iic t) := by
    intro t
    have : (fun w ↦ f w t) = (Set.Iic t).indicator (1 : ℝ → ℝ) := by
      funext w
      simp only [hf, Set.indicator_apply, Set.mem_Ici, Set.mem_Iic, Pi.one_apply]
    rw [this, integral_indicator_one measurableSet_Iic]
  have inner_w : ∀ᵐ w ∂μ, ∫ t, f w t ∂ν = max (x - w) 0 := by
    filter_upwards [hμ] with w hw
    simp only [hf]
    have hset : Set.Ici w ∩ Set.Icc 0 x = Set.Icc w x := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hw.trans h1, h3⟩
    rw [integral_indicator_one measurableSet_Ici, hν, measureReal_restrict_apply measurableSet_Ici,
      hset, Real.volume_real_Icc]
  rw [← integral_congr_ae inner_w, integral_integral_swap hint]
  simp only [inner_t]

/-- AKMM, (20.56), p. 623: a mean-preserving spread `G` of `F` satisfies (20.56), in the form
`∫max{x − w, 0}dG ≥ ∫max{x − w, 0}dF` (which is `∫_0^x G ≥ ∫_0^x F` by `mps_ibp`). -/
theorem eq_20_56_of_mps {ψ φ : Measure ℝ} [IsProbabilityMeasure ψ] [IsProbabilityMeasure φ]
    (hiφ : Integrable id φ) (hiψ : Integrable id ψ)
    (h : SargentStachurski.AdditionalApplications.IsMPS ψ φ) (x : ℝ) :
    ∫ w, max (x - w) 0 ∂φ ≤ ∫ w, max (x - w) 0 ∂ψ := by
  have hmax := SargentStachurski.AdditionalApplications.integral_max_le_of_isMPS h x
  have hmean := mps_mean h
  have e : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → Integrable id μ →
      ∫ w, max (x - w) 0 ∂μ = ∫ w, max w x ∂μ - ∫ w, w ∂μ := by
    intro μ _ hi
    have h1 : Integrable (fun w ↦ max w x) μ := hi.sup (integrable_const x)
    have h2 : Integrable (fun w : ℝ ↦ w) μ := hi
    rw [← integral_sub h1 h2]
    congr 1; funext w
    rcases le_total w x with hw | hw
    · rw [max_eq_left (by linarith), max_eq_right hw]
    · rw [max_eq_right (by linarith), max_eq_left hw]; ring
  rw [e φ inferInstance hiφ, e ψ inferInstance hiψ, hmean]
  linarith

/-- AKMM, p. 623 (correction): (20.56) alone does not make `G` a mean-preserving spread of `F`.
With `F` the point mass at `1` and `G` the point mass at `0`, `∫max{x − w, 0}dG = max{x, 0} ≥
max{x − 1, 0} = ∫max{x − w, 0}dF` for all `x`, but the means differ. -/
theorem eq_20_56_not_sufficient :
    (∀ x : ℝ, ∫ w, max (x - w) 0 ∂(Measure.dirac (1 : ℝ)) ≤
      ∫ w, max (x - w) 0 ∂(Measure.dirac (0 : ℝ))) ∧
    ¬ SargentStachurski.AdditionalApplications.IsMPS (Measure.dirac (0 : ℝ))
      (Measure.dirac (1 : ℝ)) := by
  refine ⟨fun x ↦ ?_, fun h ↦ ?_⟩
  · rw [integral_dirac, integral_dirac]
    exact max_le_max (by linarith) le_rfl
  · have := mps_mean h
    rw [integral_dirac, integral_dirac] at this
    norm_num at this

/-- AKMM, (20.57), p. 624: `∫_{w > x}(w − x)dF = μ_w − x + ∫max{x − w, 0}dF`, `μ_w` the mean. -/
theorem eq_20_57 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable id μ) (x : ℝ) :
    ∫ w in Set.Ioi x, (w - x) ∂μ = ∫ w, w ∂μ - x + ∫ w, max (x - w) 0 ∂μ := by
  rw [Miao.Applications.od_setIntegral_Ioi_eq]
  have e : (fun w ↦ max (w - x) 0) = fun w ↦ (w - x) + max (x - w) 0 := by
    funext w
    rcases le_total w x with hw | hw
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have h1 : Integrable (fun w : ℝ ↦ w) μ := hi
  have h2 : Integrable (fun w : ℝ ↦ w - x) μ := h1.sub (integrable_const x)
  have h3 : Integrable (fun w : ℝ ↦ max (x - w) 0) μ :=
    ((integrable_const x).sub h1).sup (integrable_const 0)
  rw [e, integral_add h2 h3, integral_sub h1 (integrable_const x), integral_const, probReal_univ,
    one_smul]

/-- AKMM, (20.58), p. 624: the reservation-wage equation (20.55) in the form
`w* − b − β/(1 − β(1 − σ))(μ_w − w* + ∫max{w* − w, 0}dF) = 0`. -/
theorem eq_20_58 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable id μ) {b σ β x : ℝ} :
    mcG μ b σ β x =
      x - b - β / (1 - β * (1 - σ)) * (∫ w, w ∂μ - x + ∫ w, max (x - w) 0 ∂μ) := by
  rw [mcG, eq_20_57 hi]

/-- AKMM, p. 624: the left side of (20.58) is strictly increasing in `w*`. -/
theorem eq_20_58_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ] {B b σ β : ℝ}
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) :
    StrictMono (mcG μ b σ β) := by
  have h := Miao.Applications.od_firingψ_strictMono (c := b) hμ hβ0 hβ1 hσ
  intro x y hxy
  rw [mc_G_eq, mc_G_eq]
  exact h hxy

/-- AKMM, p. 624: if the offer distribution `ψ` is a mean-preserving spread of `φ` (both on
`[0, w_u]`), the reservation wage under `ψ` is at least that under `φ`. -/
theorem mc_mps_reservation {φ ψ : Measure ℝ} [IsProbabilityMeasure φ] [IsProbabilityMeasure ψ]
    {B b σ β : ℝ} (hφ : ∀ᵐ z ∂φ, z ∈ Set.Icc 0 B) (hψ : ∀ᵐ z ∂ψ, z ∈ Set.Icc 0 B)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    (h : SargentStachurski.AdditionalApplications.IsMPS ψ φ) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman φ B b σ β V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman ψ B b σ β V₂ W₂ U₂) :
    (1 - β) * U₁ ≤ (1 - β) * U₂ := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  set x₁ := (1 - β) * U₁
  have h1 : mcG φ b σ β x₁ = 0 := by
    rw [mcG]; exact (mc_root_unique hφ hβ0 hβ1 hσ hB₁ x₁).mpr rfl
  have h2 : mcG ψ b σ β ((1 - β) * U₂) = 0 := by
    rw [mcG]; exact (mc_root_unique hψ hβ0 hβ1 hσ hB₂ _).mpr rfl
  -- `I_ψ(x₁) ≥ I_φ(x₁)` by Sargent–Stachurski's (8.18)
  have hI : ∫ w in Set.Ioi x₁, (w - x₁) ∂φ ≤ ∫ w in Set.Ioi x₁, (w - x₁) ∂ψ := by
    rw [Miao.Applications.od_setIntegral_Ioi_eq, Miao.Applications.od_setIntegral_Ioi_eq]
    have hmax := SargentStachurski.AdditionalApplications.integral_max_le_of_isMPS h x₁
    have e : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → (∀ᵐ z ∂μ, z ∈ Set.Icc 0 B) →
        ∫ w, max (w - x₁) 0 ∂μ = ∫ w, max w x₁ ∂μ - x₁ := by
      intro μ _ hμ
      have hint : Integrable (fun w ↦ max w x₁) μ :=
        Miao.Applications.od_integrable_of_continuous hμ (by fun_prop)
      have ef : (fun w ↦ max (w - x₁) 0) = fun w ↦ max w x₁ - x₁ := by
        funext w
        rcases le_total w x₁ with hw | hw
        · rw [max_eq_right (by linarith), max_eq_right hw]; ring
        · rw [max_eq_left (by linarith), max_eq_left hw]
      rw [ef, integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e φ inferInstance hφ, e ψ inferInstance hψ]
    linarith
  have hle : mcG ψ b σ β x₁ ≤ mcG ψ b σ β ((1 - β) * U₂) := by
    rw [h2]; unfold mcG at h1 ⊢
    have : 0 ≤ β / (1 - β * (1 - σ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hI this]
  exact (eq_20_58_strictMono hψ hβ0 hβ1 hσ).le_iff_le.mp hle

/-- AKMM, p. 625: the mean–min ratio. If `w* = b + k(λw^M − λw*)` (which is (20.55) with
`∫_{w > w*}(w − w*)dF = λ(w^M − w*)`, `k = β/(1 − β(1 − σ))`), `w*, w^M > 0` and `kλ ≥ 0`, then
`Mm = w^M/w* = (1 + kλ)/(ρ + kλ)` with `ρ = b/w^M`. -/
theorem mm_formula {b k lam wM ws : ℝ} (hwM : 0 < wM) (hws : 0 < ws) (hkl : 0 ≤ k * lam)
    (h : ws = b + k * (lam * wM - lam * ws)) :
    wM / ws = (1 + k * lam) / (b / wM + k * lam) := by
  have hden : b / wM + k * lam = ws * (1 + k * lam) / wM := by
    rw [eq_div_iff hwM.ne']; field_simp; linarith
  rw [hden]
  have : 0 < 1 + k * lam := by linarith
  field_simp

/-- AKMM, pp. 624–625: from the Bellman equations, with `λ = 1 − F(w*) > 0`,
`w^M = ∫_{w > w*} w dF/λ > 0` and `ρ = b/w^M`, the mean–min ratio is
`w^M/w* = (1 + βλ/(1 − β(1 − σ)))/(ρ + βλ/(1 − β(1 − σ)))`. -/
theorem mm_formula_of_bellman {F : Measure ℝ} [IsProbabilityMeasure F] {B b σ β : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) (hb : 0 < b)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U)
    (hlam : 0 < F.real (Set.Ioi ((1 - β) * U)))
    (hwM : 0 < (∫ w in Set.Ioi ((1 - β) * U), w ∂F) / F.real (Set.Ioi ((1 - β) * U))) :
    (∫ w in Set.Ioi ((1 - β) * U), w ∂F) / F.real (Set.Ioi ((1 - β) * U)) / ((1 - β) * U) =
      (1 + β / (1 - β * (1 - σ)) * F.real (Set.Ioi ((1 - β) * U))) /
        (b / ((∫ w in Set.Ioi ((1 - β) * U), w ∂F) / F.real (Set.Ioi ((1 - β) * U))) +
          β / (1 - β * (1 - σ)) * F.real (Set.Ioi ((1 - β) * U))) := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  set ws := (1 - β) * U with hws
  set lam := F.real (Set.Ioi ws)
  set wM := (∫ w in Set.Ioi ws, w ∂F) / lam with hwMdef
  have hU := mc_U_pos hF hβ0 hβ1 hσ hb hB
  have hwsp : 0 < ws := mul_pos (by linarith) hU.2
  have h55 := eq_20_55 hF hβ0 hβ1 hσ hB
  have hi : Integrable (fun w : ℝ ↦ w) F :=
    Miao.Applications.od_integrable_of_continuous hF continuous_id
  have hsplit : ∫ w in Set.Ioi ws, (w - ws) ∂F = lam * wM - lam * ws := by
    rw [integral_sub hi.integrableOn (integrable_const ws), setIntegral_const, smul_eq_mul,
      hwMdef]
    field_simp
    ring
  rw [hsplit] at h55
  exact mm_formula hwM hwsp (by positivity) h55

/-- AKMM, p. 625: the back-of-the-envelope calculation. With `β = 0.996`, `σ = 0.034`,
`λ = 0.45` and `ρ = 0.4`, the formula gives `Mm > 1.04` (about `1.049`), not the printed
`1.031`. -/
theorem mm_back_of_envelope :
    let k : ℝ := 0.996 / (1 - 0.996 * (1 - 0.034))
    1.04 < (1 + k * 0.45) / (0.4 + k * 0.45) ∧ (1 + k * 0.45) / (0.4 + k * 0.45) ≠ 1.031 := by
  norm_num

end AKMM.FrictionalLaborMarkets
