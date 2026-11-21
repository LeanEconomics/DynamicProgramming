/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.ODMcCall
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The McCall search model

AKMM, §20.9, pp. 620–623. An unemployed worker receives `b` and one wage offer per period, drawn
from `F` on `[0, w_u]`; an employed worker loses the job with probability `σ`; the discount
factor is `β ∈ (0, 1)`. The Bellman equations (20.50), (20.52) are Miao's Exercise 8.2
(`Miao.Applications.od_FiringBellman` with firing probability `α = σ`; the timing is the same:
a worker who loses the job next period is unemployed then and searches the period after), which
is reused for existence, uniqueness, the reservation property and (20.55).

* `eq_20_51`: `(1 − β)U = b + β∫max{W(w) − U, 0}dF`; `eq_20_53`:
  `W(w) = (w + βσU)/(1 − β(1 − σ))`; `mc_W_strictMono`, `mc_U_pos`, `mc_W0_lt`: `W` is increasing
  and `W(0) < U`.
* `mc_exists_unique` (Miao's `ex_8_2`), `mc_reservation`: the reservation wage `w* = (1 − β)U`,
  with `W(w*) = U`; `eq_20_55`: `w* = b + β/(1 − β(1 − σ))∫_{w > w*}(w − w*)dF`, and `w*` is its
  only root (`mc_root_unique`).
* `mc_lambda_antitone`: `λ = 1 − F(w*)` is decreasing in `w*`.
* Comparative statics (p. 622): `mc_cs_b`, `mc_cs_beta`, `mc_cs_sigma`: `w*` increases in `b` and
  `β` and decreases in `σ` (the last is Miao's `ex_8_2_alpha`); `mc_G_partials`:
  `∂G/∂β < 0`, `∂G/∂σ > 0`, `∂G/∂b < 0` (when some offer exceeds `w*`).
* `mc_I_hasDerivAt` (Leibniz's rule): if `F` has no atom at `x`,
  `d/dx∫max{w − x, 0}dF = −(1 − F(x))`; `mc_G_w`: `∂G/∂w* = 1 + β(1 − F(w*))/(1 − β(1 − σ)) > 0`.
* A shift of all offers by `ε` (p. 623): `mc_shift_eq` (the reservation condition of the shifted
  distribution), `mc_shift_bounds`: the reservation wage `R(ε) = w*(ε) + ε` satisfies
  `0 < R(ε₂) − R(ε₁) < ε₂ − ε₁`; `mc_shift_deriv`: `dR/dε = β(1 − F(w*))/(1 − β(1 − σ) +
  β(1 − F(w*))) ∈ (0, 1)`.

Departures: the strict signs need `F(w > w*) > 0` (some offer is accepted), and Leibniz's rule
needs `F` to have no atom at `w*`; the derivative of `R` assumes `R` differentiable, as the book's
use of the implicit function theorem does (the difference bounds need no differentiability).
-/

namespace AKMM.FrictionalLaborMarkets

open MeasureTheory Filter Topology

variable {F : Measure ℝ} [IsProbabilityMeasure F] {B b σ β : ℝ}

/-- The option-value integral `I(x) = ∫max{w − x, 0}dF`. -/
noncomputable def mcI (F : Measure ℝ) (x : ℝ) : ℝ := ∫ w, max (w - x) 0 ∂F

omit [IsProbabilityMeasure F] in
/-- AKMM, (20.53), p. 622: `W(w) = (w + βσU)/(1 − β(1 − σ))` (Miao's `ex_8_2_E`). -/
theorem eq_20_53 (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    ∀ w ∈ Set.Icc 0 B, W w = (w + β * σ * U) / (1 - β * (1 - σ)) := by
  intro w hw
  rw [Miao.Applications.ex_8_2_E hβ0 hβ1 hσ hB w hw]
  congr 1 <;> ring

/-- `1 − β(1 − σ) > 0`. -/
theorem mc_D_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) : 0 < 1 - β * (1 - σ) := by
  nlinarith

/-- AKMM, (20.50)–(20.51), p. 621: `(1 − β)U = b + β∫max{W(w) − U, 0}dF`. -/
theorem eq_20_51 (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    (1 - β) * U = b + β * ∫ w, max (W w - U) 0 ∂F := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  have hW := eq_20_53 hβ0 hβ1 hσ hB
  have hcongr : (fun w ↦ max (W w - U) 0) =ᵐ[F]
      fun w ↦ max ((w + β * σ * U) / (1 - β * (1 - σ)) - U) 0 :=
    hF.mono fun w hw ↦ by simp only [hW w hw]
  have hcongr2 : V =ᵐ[F] fun w ↦ U + max ((w + β * σ * U) / (1 - β * (1 - σ)) - U) 0 :=
    hF.mono fun w hw ↦ by
      simp only [(hB.2 w hw).2, hW w hw]
      rcases le_total ((w + β * σ * U) / (1 - β * (1 - σ))) U with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  have hi : Integrable (fun w ↦ max ((w + β * σ * U) / (1 - β * (1 - σ)) - U) 0) F :=
    Miao.Applications.od_integrable_of_continuous hF (by fun_prop)
  have h1 := hB.1
  rw [integral_congr_ae hcongr2, integral_add (integrable_const U) hi, integral_const,
    probReal_univ, one_smul] at h1
  rw [integral_congr_ae hcongr]
  linarith

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: `W(w)` is strictly increasing in `w`. -/
theorem mc_W_strictMono (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    StrictMonoOn W (Set.Icc 0 B) := by
  intro x hx y hy hxy
  rw [eq_20_53 hβ0 hβ1 hσ hB x hx, eq_20_53 hβ0 hβ1 hσ hB y hy]
  exact div_lt_div_of_pos_right (by linarith) (mc_D_pos hβ0 hβ1 hσ)

/-- AKMM, p. 622: with `b > 0`, `U ≥ b/(1 − β) > 0` (the worker can always reject). -/
theorem mc_U_pos (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    (hb : 0 < b) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) : b / (1 - β) ≤ U ∧ 0 < U := by
  have h := eq_20_51 hF hβ0 hβ1 hσ hB
  have hI : 0 ≤ ∫ w, max (W w - U) 0 ∂F := integral_nonneg fun w ↦ le_max_right _ _
  have h1 : b ≤ (1 - β) * U := by nlinarith
  have h1β : 0 < 1 - β := by linarith
  refine ⟨by rw [div_le_iff₀ h1β]; linarith, ?_⟩
  have : 0 < (1 - β) * U := by linarith
  exact pos_of_mul_pos_right this h1β.le

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: `W(0) = βσU/(1 − β(1 − σ)) < U` (when `U > 0`). -/
theorem mc_W0_lt (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) (hB0 : 0 ≤ B) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) (hU : 0 < U) :
    W 0 = β * σ * U / (1 - β * (1 - σ)) ∧ W 0 < U := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  have h := eq_20_53 hβ0 hβ1 hσ hB 0 ⟨le_rfl, hB0⟩
  rw [zero_add] at h
  refine ⟨h, ?_⟩
  rw [h, div_lt_iff₀ hD]
  nlinarith

/-- AKMM, pp. 621–622: the Bellman equations (20.50), (20.52) have a solution, unique on
`[0, w_u]` (Miao's `ex_8_2`). -/
theorem mc_exists_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 ≤ σ) : ∃ V W U, Miao.Applications.od_FiringBellman F B b σ β V W U ∧
      ∀ V' W' U', Miao.Applications.od_FiringBellman F B b σ β V' W' U' → U' = U ∧
        ∀ w ∈ Set.Icc 0 B, W' w = W w ∧ V' w = V w := by
  obtain ⟨U, -, hB, huniq⟩ := Miao.Applications.ex_8_2 (c := b) hF hβ0 hβ1 hσ
  refine ⟨_, _, U, hB, fun V' W' U' hB' ↦ ?_⟩
  obtain ⟨hU, h⟩ := huniq V' W' U' hB'
  exact ⟨hU, fun w hw ↦ h w hw⟩

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: the reservation wage `w* = (1 − β)U`: the worker accepts `w` (`W(w) ≥ U`) iff
`w ≥ w*`, and `W(w*) = U` (Miao's `ex_8_2_reservation`). -/
theorem mc_reservation (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    (∀ w ∈ Set.Icc 0 B, U ≤ W w ↔ (1 - β) * U ≤ w) ∧
      ((1 - β) * U ∈ Set.Icc 0 B → W ((1 - β) * U) = U) := by
  refine ⟨fun w hw ↦ (Miao.Applications.ex_8_2_reservation hβ0 hβ1 hσ hB w hw).1, fun hw ↦ ?_⟩
  have hD := mc_D_pos hβ0 hβ1 hσ
  rw [eq_20_53 hβ0 hβ1 hσ hB _ hw]
  field_simp; ring

/-- AKMM, (20.54)–(20.55), p. 622: `w* = b + β/(1 − β(1 − σ))∫_{w > w*}(w − w*)dF(w)` (Miao's
`ex_8_2_reservation_eq`). -/
theorem eq_20_55 (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    (1 - β) * U = b + β / (1 - β * (1 - σ)) *
      ∫ w in Set.Ioi ((1 - β) * U), (w - (1 - β) * U) ∂F := by
  have h := Miao.Applications.ex_8_2_reservation_eq hF hβ0 hβ1 hσ hB
  rw [show 1 - β * (1 - σ) = 1 - β + σ * β by ring]
  linarith

/-- AKMM, p. 622: (20.55) has the reservation wage as its only root (Miao's
`ex_8_2_root_unique`). -/
theorem mc_root_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) (x : ℝ) :
    x - b - β / (1 - β * (1 - σ)) * ∫ w in Set.Ioi x, (w - x) ∂F = 0 ↔ x = (1 - β) * U := by
  have h := Miao.Applications.ex_8_2_root_unique hF hβ0 hβ1 hσ hB x
  rw [Miao.Applications.od_firingψ, show 1 - β + σ * β = 1 - β * (1 - σ) by ring] at h
  exact h

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: the job-finding probability `λ = 1 − F(w*) = F(w > w*)` is decreasing in
`w*`. -/
theorem mc_lambda_antitone [IsFiniteMeasure F] : Antitone fun x ↦ F.real (Set.Ioi x) :=
  fun _ _ h ↦ measureReal_mono (Set.Ioi_subset_Ioi h)

/-- The reservation-wage function `G(x) = x − b − β/(1 − β(1 − σ))∫_{w > x}(w − x)dF`. -/
noncomputable def mcG (F : Measure ℝ) (b σ β x : ℝ) : ℝ :=
  x - b - β / (1 - β * (1 - σ)) * ∫ w in Set.Ioi x, (w - x) ∂F

omit [IsProbabilityMeasure F] in
/-- `G` is Miao's `od_firingψ` with `α = σ`. -/
theorem mc_G_eq (x : ℝ) : mcG F b σ β x = Miao.Applications.od_firingψ F b σ β x := by
  rw [mcG, Miao.Applications.od_firingψ, show 1 - β + σ * β = 1 - β * (1 - σ) by ring]

/-- AKMM, p. 622: the reservation wage increases with `b`. -/
theorem mc_cs_b (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {b₁ b₂ : ℝ} (h : b₁ < b₂) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman F B b₁ σ β V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman F B b₂ σ β V₂ W₂ U₂) :
    (1 - β) * U₁ < (1 - β) * U₂ := by
  have h1 := (mc_root_unique hF hβ0 hβ1 hσ hB₁ ((1 - β) * U₁)).mpr rfl
  have h2 := (mc_root_unique hF hβ0 hβ1 hσ hB₂ ((1 - β) * U₂)).mpr rfl
  have hmono := Miao.Applications.od_firingψ_strictMono (c := b₂) hF hβ0 hβ1 hσ
  have hlt : Miao.Applications.od_firingψ F b₂ σ β ((1 - β) * U₁) <
      Miao.Applications.od_firingψ F b₂ σ β ((1 - β) * U₂) := by
    rw [← mc_G_eq, ← mc_G_eq]; unfold mcG; linarith
  exact hmono.lt_iff_lt.mp hlt

/-- AKMM, p. 622: `β/(1 − β(1 − σ))` is strictly increasing in `β ∈ (0, 1)` (for `σ ≥ 0`). -/
theorem mc_coef_strictMono {β₁ β₂ : ℝ} (hσ : 0 ≤ σ) (hβ0 : 0 < β₁) (h : β₁ < β₂)
    (hβ1 : β₂ < 1) : β₁ / (1 - β₁ * (1 - σ)) < β₂ / (1 - β₂ * (1 - σ)) := by
  have hD1 := mc_D_pos hβ0 (h.trans hβ1) hσ
  have hD2 := mc_D_pos (hβ0.trans h) hβ1 hσ
  rw [div_lt_div_iff₀ hD1 hD2]
  nlinarith

/-- AKMM, p. 622: the reservation wage increases with `β`, strictly if some offer above the
lower reservation wage has positive probability. -/
theorem mc_cs_beta (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hσ : 0 ≤ σ) {β₁ β₂ : ℝ} (hβ0 : 0 < β₁)
    (h : β₁ < β₂) (hβ1 : β₂ < 1) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman F B b σ β₁ V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman F B b σ β₂ V₂ W₂ U₂) :
    (1 - β₁) * U₁ ≤ (1 - β₂) * U₂ ∧
      (0 < ∫ w in Set.Ioi ((1 - β₁) * U₁), (w - (1 - β₁) * U₁) ∂F →
        (1 - β₁) * U₁ < (1 - β₂) * U₂) := by
  have hb2 : 0 < β₂ := hβ0.trans h
  have h1 := (mc_root_unique hF hβ0 (h.trans hβ1) hσ hB₁ ((1 - β₁) * U₁)).mpr rfl
  have h2 := (mc_root_unique hF hb2 hβ1 hσ hB₂ ((1 - β₂) * U₂)).mpr rfl
  have hmono := Miao.Applications.od_firingψ_strictMono (c := b) hF hb2 hβ1 hσ
  have hk := mc_coef_strictMono hσ hβ0 h hβ1
  set x₁ := (1 - β₁) * U₁
  set I := ∫ w in Set.Ioi x₁, (w - x₁) ∂F
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun w hw ↦ by
    simp only [Set.mem_Ioi] at hw; linarith
  have hle : Miao.Applications.od_firingψ F b σ β₂ x₁ ≤
      Miao.Applications.od_firingψ F b σ β₂ ((1 - β₂) * U₂) := by
    rw [← mc_G_eq, ← mc_G_eq]; unfold mcG
    nlinarith [mul_le_mul_of_nonneg_right hk.le hI]
  refine ⟨hmono.le_iff_le.mp hle, fun hIpos ↦ ?_⟩
  have hlt : Miao.Applications.od_firingψ F b σ β₂ x₁ <
      Miao.Applications.od_firingψ F b σ β₂ ((1 - β₂) * U₂) := by
    rw [← mc_G_eq, ← mc_G_eq]; unfold mcG
    nlinarith [mul_lt_mul_of_pos_right hk hIpos]
  exact hmono.lt_iff_lt.mp hlt

/-- AKMM, p. 622: the reservation wage decreases with `σ` (Miao's `ex_8_2_alpha`). -/
theorem mc_cs_sigma (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) {σ₁ σ₂ : ℝ}
    (hσ : 0 ≤ σ₁) (h : σ₁ ≤ σ₂) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman F B b σ₁ β V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman F B b σ₂ β V₂ W₂ U₂) :
    (1 - β) * U₂ ≤ (1 - β) * U₁ :=
  Miao.Applications.ex_8_2_alpha hF hβ0 hβ1 hσ h hB₁ hB₂

/-- AKMM, p. 622: with `I = ∫_{w > w*}(w − w*)dF > 0` fixed, `G(w*, β, σ, b) = w* − b −
βI/(1 − β(1 − σ))` has `∂G/∂β = −I/(1 − β(1 − σ))² < 0`, `∂G/∂σ = β²I/(1 − β(1 − σ))² > 0`
and `∂G/∂b = −1 < 0`. -/
theorem mc_G_partials {x I : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) (hI : 0 < I) :
    HasDerivAt (fun β' ↦ x - b - β' / (1 - β' * (1 - σ)) * I)
      (-(I / (1 - β * (1 - σ)) ^ 2)) β ∧ -(I / (1 - β * (1 - σ)) ^ 2) < 0 ∧
    HasDerivAt (fun σ' ↦ x - b - β / (1 - β * (1 - σ')) * I)
      (β ^ 2 * I / (1 - β * (1 - σ)) ^ 2) σ ∧ 0 < β ^ 2 * I / (1 - β * (1 - σ)) ^ 2 ∧
    HasDerivAt (fun b' ↦ x - b' - β / (1 - β * (1 - σ)) * I) (-1) b := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  refine ⟨?_, by have : 0 < I / (1 - β * (1 - σ)) ^ 2 := by positivity
                 linarith, ?_, by positivity, ?_⟩
  · have hden : HasDerivAt (fun β' : ℝ ↦ 1 - β' * (1 - σ)) (-(1 - σ)) β := by
      simpa using ((hasDerivAt_id β).mul_const (1 - σ)).const_sub 1
    have := (((hasDerivAt_id β).div hden hD.ne').mul_const I).const_sub (x - b)
    refine this.congr_deriv ?_
    simp only [id]; field_simp; ring
  · have hden : HasDerivAt (fun σ' : ℝ ↦ 1 - β * (1 - σ')) β σ := by
      simpa using (((hasDerivAt_id σ).const_sub 1).const_mul β).const_sub 1
    have := (((hasDerivAt_const σ β).div hden hD.ne').mul_const I).const_sub (x - b)
    refine this.congr_deriv ?_
    field_simp; ring
  · have := ((hasDerivAt_id b).const_sub x).sub_const (β / (1 - β * (1 - σ)) * I)
    simpa using this

/-- The pointwise estimate behind Leibniz's rule: for all `w`,
`|max{w − y, 0} − max{w − x, 0} + (y − x)1{w > x}| ≤ |y − x|·1{|w − x| ≤ |y − x|}`. -/
theorem mc_pointwise (x y w : ℝ) :
    |max (w - y) 0 - max (w - x) 0 + (y - x) * (Set.Ioi x).indicator 1 w| ≤
      |y - x| * (Set.Icc (x - |y - x|) (x + |y - x|)).indicator 1 w := by
  have h1 := le_abs_self (y - x)
  have h2 := neg_abs_le (y - x)
  by_cases hw : w ∈ Set.Icc (x - |y - x|) (x + |y - x|)
  · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one, abs_le]
    by_cases hx : w ∈ Set.Ioi x
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      simp only [Set.mem_Ioi] at hx
      constructor <;> simp only [max_def] <;> split_ifs <;> linarith
    · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      simp only [Set.mem_Ioi, not_lt] at hx
      obtain ⟨hw1, -⟩ := hw
      constructor <;> simp only [max_def] <;> split_ifs <;> linarith
  · rw [Set.indicator_of_notMem hw, mul_zero]
    simp only [Set.mem_Icc, not_and_or, not_le] at hw
    rcases hw with hw | hw
    · have hx : w ∉ Set.Ioi x := by simp only [Set.mem_Ioi, not_lt]; linarith
      rw [Set.indicator_of_notMem hx, mul_zero, add_zero, max_eq_right (by linarith),
        max_eq_right (by linarith)]
      simp
    · have hx : w ∈ Set.Ioi x := by simp only [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, max_eq_left (by linarith),
        max_eq_left (by linarith)]
      simp

/-- AKMM, p. 622 (**Leibniz's rule**): if the offer distribution has no atom at `x`, then
`d/dx ∫max{w − x, 0}dF(w) = −(1 − F(x)) = −F(w > x)`. -/
theorem mc_I_hasDerivAt (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {x : ℝ} (hx : F {x} = 0) :
    HasDerivAt (mcI F) (-F.real (Set.Ioi x)) x := by
  have hint : ∀ y, Integrable (fun w ↦ max (w - y) 0) F := fun y ↦
    Miao.Applications.od_integrable_of_continuous hF (by fun_prop)
  have hind : ∀ s : Set ℝ, MeasurableSet s → Integrable (s.indicator (1 : ℝ → ℝ)) F :=
    fun s hs ↦ (integrable_const (1 : ℝ)).indicator hs
  -- the global estimate
  have hbound : ∀ y, |mcI F y - mcI F x - (y - x) * -F.real (Set.Ioi x)| ≤
      |y - x| * F.real (Set.Icc (x - |y - x|) (x + |y - x|)) := by
    intro y
    have e : mcI F y - mcI F x - (y - x) * -F.real (Set.Ioi x) = ∫ w,
        (max (w - y) 0 - max (w - x) 0 + (y - x) * (Set.Ioi x).indicator 1 w) ∂F := by
      have ha : Integrable (fun w ↦ max (w - y) 0 - max (w - x) 0) F := (hint y).sub (hint x)
      have hb : Integrable (fun w ↦ (y - x) * (Set.Ioi x).indicator (1 : ℝ → ℝ) w) F :=
        (hind _ measurableSet_Ioi).const_mul _
      rw [integral_add ha hb, integral_sub (hint y) (hint x), integral_const_mul,
        integral_indicator_one measurableSet_Ioi, mcI, mcI]
      ring
    rw [e]
    calc _ ≤ ∫ w, |max (w - y) 0 - max (w - x) 0 + (y - x) * (Set.Ioi x).indicator 1 w| ∂F :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w, |y - x| * (Set.Icc (x - |y - x|) (x + |y - x|)).indicator 1 w ∂F :=
          integral_mono (((hint y).sub (hint x)).add
            ((hind _ measurableSet_Ioi).const_mul _)).abs
            ((hind _ measurableSet_Icc).const_mul _) fun w ↦ mc_pointwise x y w
      _ = _ := by rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
  -- the measure of small intervals around `x` tends to `F {x} = 0`
  have hlim : Tendsto (fun r ↦ F (Metric.cthickening r {x})) (𝓝 0) (𝓝 0) := by
    have := tendsto_measure_cthickening_of_isClosed (μ := F) (s := {x})
      ⟨1, one_pos, measure_ne_top _ _⟩ isClosed_singleton
    rwa [hx] at this
  have hlim' : Tendsto (fun y ↦ F (Metric.cthickening |y - x| {x})) (𝓝 x) (𝓝 0) := by
    refine hlim.comp ?_
    have : Tendsto (fun y : ℝ ↦ |y - x|) (𝓝 x) (𝓝 |x - x|) :=
      ((continuous_id.sub continuous_const).abs).tendsto x
    simpa using this
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hlim'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hc))] with y hy
  rw [Metric.cthickening_singleton _ (abs_nonneg _), Real.closedBall_eq_Icc] at hy
  have hreal : F.real (Set.Icc (x - |y - x|) (x + |y - x|)) ≤ c := by
    rw [measureReal_def]
    exact (ENNReal.toReal_le_of_le_ofReal hc.le hy.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  calc _ ≤ |y - x| * F.real (Set.Icc (x - |y - x|) (x + |y - x|)) := hbound y
    _ ≤ |y - x| * c := mul_le_mul_of_nonneg_left hreal (abs_nonneg _)
    _ = c * |y - x| := mul_comm _ _

/-- AKMM, p. 622: if `F` has no atom at `x`, `∂G/∂w* = 1 + β(1 − F(w*))/(1 − β(1 − σ)) > 0`. -/
theorem mc_G_w (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {x : ℝ} (hx : F {x} = 0) :
    HasDerivAt (mcG F b σ β) (1 + β / (1 - β * (1 - σ)) * F.real (Set.Ioi x)) x ∧
      0 < 1 + β / (1 - β * (1 - σ)) * F.real (Set.Ioi x) := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  have heq : mcG F b σ β = fun y ↦ y - b - β / (1 - β * (1 - σ)) * mcI F y := by
    funext y; rw [mcG, mcI, Miao.Applications.od_setIntegral_Ioi_eq]
  refine ⟨?_, by have : 0 ≤ F.real (Set.Ioi x) := measureReal_nonneg
                 positivity⟩
  rw [heq]
  have := (((hasDerivAt_id x).sub_const b).sub
    ((mc_I_hasDerivAt hF hx).const_mul (β / (1 - β * (1 - σ)))))
  refine this.congr_deriv ?_
  ring

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 623: if every offer is shifted to `w + ε`, the reservation condition (20.55) for the
shifted distribution at `R` reads `G(R − ε, ε) = (R − ε) + ε − b − β/(1 − β(1 − σ))I(R − ε)`,
`I(x) = ∫max{w − x, 0}dF`: it is the book's `G(w*, ε)` with `w* = R − ε`. -/
theorem mc_shift_eq (ε R : ℝ) :
    ∫ w', max (w' - R) 0 ∂(F.map fun w ↦ w + ε) = mcI F (R - ε) := by
  rw [integral_map (measurable_add_const ε).aemeasurable (by fun_prop), mcI]
  congr 1; funext w; congr 1; ring

/-- AKMM, p. 623: with offers `w + ε`, write the reservation wage as `R(ε) = w*(ε) + ε` where
`w*(ε) + ε − b − kI(w*(ε)) = 0`, `k = β/(1 − β(1 − σ))`. If `ε₁ < ε₂` and some offer is at least
`w*(ε₁)` with positive probability, then `0 < R(ε₂) − R(ε₁) < ε₂ − ε₁`: the reservation wage
rises, but by less than the offers. -/
theorem mc_shift_bounds (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {k ε₁ ε₂ x₁ x₂ : ℝ} (hk : 0 < k)
    (h : ε₁ < ε₂) (h₁ : x₁ + ε₁ - b - k * mcI F x₁ = 0) (h₂ : x₂ + ε₂ - b - k * mcI F x₂ = 0)
    (hpos : 0 < F.real (Set.Ici x₁)) :
    0 < (x₂ + ε₂) - (x₁ + ε₁) ∧ (x₂ + ε₂) - (x₁ + ε₁) < ε₂ - ε₁ := by
  have hint : ∀ y, Integrable (fun w ↦ max (w - y) 0) F := fun y ↦
    Miao.Applications.od_integrable_of_continuous hF (by fun_prop)
  -- `I` is antitone with slope at least `F(w ≥ x)`: `I(y) − I(x) ≥ (x − y)F(w ≥ x)` for `y ≤ x`
  have hslope : ∀ y x : ℝ, y ≤ x → (x - y) * F.real (Set.Ici x) ≤ mcI F y - mcI F x := by
    intro y x hyx
    rw [mcI, mcI, ← integral_sub (hint y) (hint x), ← integral_indicator_one measurableSet_Ici,
      ← integral_const_mul]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Ici |>.const_mul _)
      ((hint y).sub (hint x)) fun w ↦ ?_
    by_cases hw : w ∈ Set.Ici x
    · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one]
      simp only [Set.mem_Ici] at hw
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [Set.indicator_of_notMem hw, mul_zero]
      have : max (w - x) 0 ≤ max (w - y) 0 := max_le_max (by linarith) le_rfl
      linarith
  have hanti : ∀ y x : ℝ, y ≤ x → mcI F x ≤ mcI F y := fun y x hyx ↦ by
    have := hslope y x hyx
    have : 0 ≤ (x - y) * F.real (Set.Ici x) := mul_nonneg (by linarith) measureReal_nonneg
    linarith
  -- `x₂ < x₁`
  have hx : x₂ < x₁ := by
    by_contra hc
    have hle := not_lt.mp hc
    have := hanti x₁ x₂ hle
    nlinarith
  have hs := hslope x₂ x₁ hx.le
  constructor
  · -- `ε₂ − ε₁ = (x₁ − x₂) + k(I(x₂) − I(x₁)) ≥ (x₁ − x₂)(1 + kF(w ≥ x₁))`
    have : (x₁ - x₂) * (k * F.real (Set.Ici x₁)) ≤ k * (mcI F x₂ - mcI F x₁) := by
      nlinarith
    have : 0 < (x₁ - x₂) * (k * F.real (Set.Ici x₁)) := by
      have := sub_pos.mpr hx; positivity
    nlinarith
  · linarith

/-- AKMM, p. 623: if the shifted reservation condition `w*(ε) + ε − b − kI(w*(ε)) = 0` holds for
`ε` near `0`, `w*` is differentiable at `0` and `F` has no atom at `w*(0)`, then
`d(w* + ε)/dε = kλ/(1 + kλ) ∈ (0, 1)` with `λ = 1 − F(w*)`; with `k = β/(1 − β(1 − σ))` this is
`β(1 − F(w*))/(1 − β(1 − σ) + β(1 − F(w*)))`. -/
theorem mc_shift_deriv (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 ≤ σ) {xs : ℝ → ℝ} {d : ℝ} (hxs : HasDerivAt xs d 0)
    (hroot : ∀ᶠ ε in 𝓝 0, xs ε + ε - b - β / (1 - β * (1 - σ)) * mcI F (xs ε) = 0)
    (hatom : F {xs 0} = 0) :
    HasDerivAt (fun ε ↦ xs ε + ε)
      (β * F.real (Set.Ioi (xs 0)) / (1 - β * (1 - σ) + β * F.real (Set.Ioi (xs 0)))) 0 ∧
    0 ≤ β * F.real (Set.Ioi (xs 0)) / (1 - β * (1 - σ) + β * F.real (Set.Ioi (xs 0))) ∧
    β * F.real (Set.Ioi (xs 0)) / (1 - β * (1 - σ) + β * F.real (Set.Ioi (xs 0))) < 1 := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  set k := β / (1 - β * (1 - σ)) with hk
  set L := F.real (Set.Ioi (xs 0)) with hL
  have hL0 : 0 ≤ L := measureReal_nonneg
  have hI := mc_I_hasDerivAt hF hatom
  -- differentiate the identity at `0`
  have hcomp : HasDerivAt (fun ε ↦ xs ε + ε - b - k * mcI F (xs ε))
      (d + 1 - k * (-L * d)) 0 := by
    have h1 := (hxs.add (hasDerivAt_id 0)).sub_const b
    have h2 := (hI.comp 0 hxs).const_mul k
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hzero : HasDerivAt (fun ε ↦ xs ε + ε - b - k * mcI F (xs ε)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hroot
  have hd : d + 1 - k * (-L * d) = 0 := hcomp.unique hzero
  have hkL : 0 ≤ k * L := by positivity
  have hd' : d = -1 / (1 + k * L) := by
    rw [eq_div_iff (by linarith)]; linarith
  have hval : d + 1 = β * L / (1 - β * (1 - σ) + β * L) := by
    rw [hd', hk]; field_simp; ring
  refine ⟨(hxs.add (hasDerivAt_id 0)).congr_deriv (by rw [← hval]), ?_, ?_⟩
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

end AKMM.FrictionalLaborMarkets
