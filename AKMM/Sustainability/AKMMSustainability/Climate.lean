/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.Exponential
import DifferenceEquations.LinearSystems

/-!
# The climate system

AKMM, §25.3.1 (pp. 753–755) and the calibration of (25.4)–(25.5) in Appendix 25.A (p. 909).

* (25.1), the energy-balance equation `dT/dt = σ(f − κT)` with constant forcing `f`: the
  path `T(t) = f/κ + (T₀ − f/κ)e^{−σκt}` solves it (`eq_25_1`), is the only solution from
  `T₀` (`eq_25_1_unique`, by the uniqueness of the scalar linear IVP, Sargent–Stachurski
  Example 10.1.1 in `ContinuousTime`), and converges to the steady state `f/κ`
  (`eq_25_1_tendsto`), which is the only rest point (`eq_25_1_steady`).
* (25.2)–(25.3): with Arrhenius forcing `f = (η/log 2) log(S/S₀)`, the steady-state temperature
  is (25.3) (`eq_25_3`); it rises by exactly `η/κ` whenever `S` doubles, from any `S`
  (`climate_ecs_doubling`), and equals the ECS `η/κ` at `S = 2S₀` (`climate_ecs`).
* (25.4)–(25.5), the discretised atmosphere–ocean system for a given `S`: its only steady
  state is `T = Tᴸ = F/κ`, i.e. the value (25.3) (`eq_25_4_steady_iff`); under
  `σ₁, σ₂, σ₃, κ > 0`, `σ₃ ≤ 1` and `σ₁(κ + σ₂) ≤ 1` every path converges to it
  (`climate_twoBox_tendsto`), by a contraction in a weighted max-norm; equivalently the
  iteration matrix is stable in the sense of Miao's Definition 1.4.5
  (`climate_twoBox_isStable`, through `isStableMatrix_iff_tendsto` of `DifferenceEquations`).
  The book's subscript `σ` in (25.1) is the `σ₁` of the text.
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- AKMM, (25.1), p. 754: the solution `T(t) = f/κ + (T₀ − f/κ)e^{−σκt}` of the energy-balance
equation with constant forcing `f`. -/
noncomputable def climateT (σ κ f T₀ t : ℝ) : ℝ := f / κ + (T₀ - f / κ) * Real.exp (-(σ * κ) * t)

/-- AKMM, (25.1), p. 754: `climateT` solves `dT/dt = σ(f − κT)` and starts at `T₀`. -/
theorem eq_25_1 {σ κ f T₀ : ℝ} (hκ : κ ≠ 0) (t : ℝ) :
    HasDerivAt (climateT σ κ f T₀) (σ * (f - κ * climateT σ κ f T₀ t)) t ∧
      climateT σ κ f T₀ 0 = T₀ := by
  refine ⟨?_, by simp [climateT]⟩
  have h := ((((hasDerivAt_id t).const_mul (-(σ * κ))).exp).const_mul (T₀ - f / κ)).const_add
    (f / κ)
  simp only [id, mul_one] at h
  unfold climateT
  convert h using 1
  field_simp
  ring

/-- AKMM, (25.1), p. 754: the solution from `T₀` is unique on `[0, ∞)`. Uses the uniqueness
of the scalar linear IVP `u̇ = ru` (Sargent–Stachurski, Example 10.1.1). -/
theorem eq_25_1_unique {σ κ f T₀ : ℝ} (hκ : κ ≠ 0) {T : ℝ → ℝ} (h0 : T 0 = T₀)
    (hT : ∀ t, 0 ≤ t → HasDerivAt T (σ * (f - κ * T t)) t) {t : ℝ} (ht : 0 ≤ t) :
    T t = climateT σ κ f T₀ t := by
  have hy := SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt (r := -(σ * κ))
    (u₀ := T₀ - f / κ) (y := fun s => T s - f / κ) (by simp [h0])
    (fun s hs => by
      have := (hT s hs).sub_const (f / κ)
      convert this using 1
      field_simp
      ring) ht
  unfold climateT
  linarith

/-- AKMM, p. 754: with `σκ > 0` the temperature converges to the steady state `f/κ`. -/
theorem eq_25_1_tendsto {σ κ f T₀ : ℝ} (hσκ : 0 < σ * κ) :
    Tendsto (climateT σ κ f T₀) atTop (𝓝 (f / κ)) := by
  have h : Tendsto (fun t : ℝ => Real.exp (-(σ * κ) * t)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hσκ)
    refine this.congr fun t => ?_
    simp [neg_mul]
  have := (h.const_mul (T₀ - f / κ)).const_add (f / κ)
  simpa using this.congr (fun t => by simp [climateT])

/-- AKMM, p. 754: "the system eventually reaches a new steady state when `T = f/κ`": the rest
points of (25.1) are exactly `f/κ`. -/
theorem eq_25_1_steady {σ κ f T : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    σ * (f - κ * T) = 0 ↔ T = f / κ := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hσ
    · field_simp; linarith
  · intro h; subst h; field_simp; ring

/-- AKMM, (25.2), p. 754: Arrhenius forcing `f = (η/log 2) log(S/S₀)`. -/
noncomputable def forcing (η S₀ S : ℝ) : ℝ := η / Real.log 2 * Real.log (S / S₀)

/-- AKMM, (25.3), p. 754: the steady-state temperature for a given carbon stock `S`. -/
noncomputable def steadyTemp (η κ S₀ S : ℝ) : ℝ := η / κ * (1 / Real.log 2) * Real.log (S / S₀)

/-- AKMM, (25.3), p. 754: combining the steady state of (25.1) with (25.2) gives (25.3). -/
theorem eq_25_3 {σ κ η S₀ S T : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    σ * (forcing η S₀ S - κ * T) = 0 ↔ T = steadyTemp η κ S₀ S := by
  rw [eq_25_1_steady hσ hκ, forcing, steadyTemp]
  constructor <;> intro h <;> rw [h] <;> ring

/-- AKMM, p. 754: the steady-state temperature rises by exactly `η/κ` when the carbon stock
doubles, whatever its level. -/
theorem climate_ecs_doubling {η κ S₀ S : ℝ} (hS₀ : 0 < S₀) (hS : 0 < S) :
    steadyTemp η κ S₀ (2 * S) - steadyTemp η κ S₀ S = η / κ := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold steadyTemp
  rw [mul_div_assoc, Real.log_mul two_ne_zero (div_pos hS hS₀).ne']
  field_simp
  ring

/-- AKMM, p. 754: the equilibrium climate sensitivity — the steady-state warming from a
doubling of the pre-industrial stock — is `η/κ`. -/
theorem climate_ecs {η κ S₀ : ℝ} (hS₀ : 0 < S₀) : steadyTemp η κ S₀ (2 * S₀) = η / κ := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold steadyTemp
  rw [mul_div_assoc, div_self hS₀.ne', mul_one]
  field_simp

/-- AKMM, (25.4)–(25.5), p. 755: one period of the atmosphere–ocean system for a given carbon
stock, whose forcing is `F = (η/log 2) log(S/S₀)`. -/
noncomputable def twoBoxStep (σ₁ σ₂ σ₃ κ F : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 + σ₁ * (F - κ * x.1 - σ₂ * (x.1 - x.2)), x.2 + σ₃ * (x.1 - x.2))

/-- AKMM, p. 755: "for a given `S`, this system has a steady state that is also given by
(25.3)": the steady states are exactly `T = Tᴸ = F/κ`. -/
theorem eq_25_4_steady_iff {σ₁ σ₂ σ₃ κ F : ℝ} (h₁ : σ₁ ≠ 0) (h₃ : σ₃ ≠ 0) (hκ : κ ≠ 0)
    (x : ℝ × ℝ) : twoBoxStep σ₁ σ₂ σ₃ κ F x = x ↔ x = (F / κ, F / κ) := by
  obtain ⟨T, L⟩ := x
  simp only [twoBoxStep, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    have hTL : T = L := by
      have : σ₃ * (T - L) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h₃
      · linarith
    subst hTL
    have : σ₁ * (F - κ * T) = 0 := by linarith
    have hT := (eq_25_1_steady h₁ hκ).mp this
    exact ⟨hT, hT⟩
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp <;> ring

/-- AKMM, pp. 755: the deviations `(u, w)` of `(T, Tᴸ)` from the steady state follow a linear
system; with `σ₁, σ₂, σ₃, κ > 0`, `σ₃ ≤ 1` and `σ₁(κ + σ₂) ≤ 1` both converge to `0`
(contraction in the max-norm with weights `(1, 1 + κ/(2σ₂))`). -/
theorem climate_dev_tendsto {σ₁ σ₂ σ₃ κ : ℝ} (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) (h₃ : 0 < σ₃)
    (h₃' : σ₃ ≤ 1) (hκ : 0 < κ) (hσκ : σ₁ * (κ + σ₂) ≤ 1) {u w : ℕ → ℝ}
    (hu : ∀ t, u (t + 1) = (1 - σ₁ * κ - σ₁ * σ₂) * u t + σ₁ * σ₂ * w t)
    (hw : ∀ t, w (t + 1) = σ₃ * u t + (1 - σ₃) * w t) :
    Tendsto u atTop (𝓝 0) ∧ Tendsto w atTop (𝓝 0) := by
  set v : ℝ := 1 + κ / (2 * σ₂) with hv
  have hv1 : 1 < v := by have : 0 < κ / (2 * σ₂) := by positivity
                         linarith
  have hv0 : 0 < v := by linarith
  set q : ℝ := max (1 - σ₁ * κ / 2) (1 - σ₃ * κ / (2 * σ₂ + κ)) with hq
  set N : ℕ → ℝ := fun t => max |u t| (|w t| / v) with hN
  have ha : 0 ≤ 1 - σ₁ * κ - σ₁ * σ₂ := by nlinarith
  have hq0 : 0 ≤ q := le_max_of_le_left (by nlinarith)
  have hq1 : q < 1 := by
    have e1 : 0 < σ₁ * κ / 2 := by positivity
    have e2 : 0 < σ₃ * κ / (2 * σ₂ + κ) := by positivity
    exact max_lt (by linarith) (by linarith)
  have hstep : ∀ t, N (t + 1) ≤ q * N t := by
    intro t
    have hu' : |u t| ≤ N t := le_max_left _ _
    have hw' : |w t| ≤ v * N t := by
      have : |w t| / v ≤ N t := le_max_right _ _
      rwa [div_le_iff₀ hv0, mul_comm] at this
    have hN0 : 0 ≤ N t := le_trans (abs_nonneg _) hu'
    refine max_le ?_ ?_
    · rw [hu t]
      calc |(1 - σ₁ * κ - σ₁ * σ₂) * u t + σ₁ * σ₂ * w t|
          ≤ (1 - σ₁ * κ - σ₁ * σ₂) * |u t| + σ₁ * σ₂ * |w t| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos (by positivity : 0 < σ₁ * σ₂)]
        _ ≤ (1 - σ₁ * κ - σ₁ * σ₂) * N t + σ₁ * σ₂ * (v * N t) := by
            gcongr
        _ = (1 - σ₁ * κ / 2) * N t := by rw [hv]; field_simp; ring
        _ ≤ q * N t := by gcongr; exact le_max_left _ _
    · rw [hw t, div_le_iff₀ hv0]
      calc |σ₃ * u t + (1 - σ₃) * w t| ≤ σ₃ * |u t| + (1 - σ₃) * |w t| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_pos h₃, abs_of_nonneg (by linarith : 0 ≤ 1 - σ₃)]
        _ ≤ σ₃ * N t + (1 - σ₃) * (v * N t) := by
            gcongr
        _ = (1 - σ₃ * κ / (2 * σ₂ + κ)) * N t * v := by
            rw [hv]; field_simp; ring
        _ ≤ q * N t * v := by gcongr; exact le_max_right _ _
  have hbound : ∀ t, N t ≤ q ^ t * N 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      calc N (n + 1) ≤ q * N n := hstep n
        _ ≤ q * (q ^ n * N 0) := by gcongr
        _ = q ^ (n + 1) * N 0 := by ring
  have hlim : Tendsto (fun t => q ^ t * N 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (N 0)
  constructor
  · refine squeeze_zero_norm (fun t => ?_) hlim
    exact (le_max_left _ _).trans (hbound t)
  · have hlim' : Tendsto (fun t => v * (q ^ t * N 0)) atTop (𝓝 0) := by
      simpa using hlim.const_mul v
    refine squeeze_zero_norm (fun t => ?_) hlim'
    have : |w t| / v ≤ q ^ t * N 0 := (le_max_right _ _).trans (hbound t)
    rw [Real.norm_eq_abs]
    rwa [div_le_iff₀ hv0, mul_comm] at this

/-- AKMM, p. 755: under `σ₁, σ₂, σ₃, κ > 0`, `σ₃ ≤ 1` and `σ₁(κ + σ₂) ≤ 1`, every path of
(25.4)–(25.5) with constant `S` converges to the steady state `(F/κ, F/κ)` of (25.3). -/
theorem climate_twoBox_tendsto {σ₁ σ₂ σ₃ κ F : ℝ} (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) (h₃ : 0 < σ₃)
    (h₃' : σ₃ ≤ 1) (hκ : 0 < κ) (hσκ : σ₁ * (κ + σ₂) ≤ 1) (x₀ : ℝ × ℝ) :
    Tendsto (fun t => ((twoBoxStep σ₁ σ₂ σ₃ κ F)^[t] x₀).1) atTop (𝓝 (F / κ)) ∧
      Tendsto (fun t => ((twoBoxStep σ₁ σ₂ σ₃ κ F)^[t] x₀).2) atTop (𝓝 (F / κ)) := by
  set X := fun t => (twoBoxStep σ₁ σ₂ σ₃ κ F)^[t] x₀ with hX
  have hsucc : ∀ t, X (t + 1) = twoBoxStep σ₁ σ₂ σ₃ κ F (X t) := fun t => by
    simp only [hX, Function.iterate_succ_apply']
  obtain ⟨hu, hw⟩ := climate_dev_tendsto h₁ h₂ h₃ h₃' hκ hσκ (u := fun t => (X t).1 - F / κ)
    (w := fun t => (X t).2 - F / κ)
    (fun t => by rw [hsucc]; simp only [twoBoxStep]; field_simp; ring)
    (fun t => by rw [hsucc]; simp only [twoBoxStep]; ring)
  refine ⟨?_, ?_⟩
  · simpa using hu.add_const (F / κ)
  · simpa using hw.add_const (F / κ)

/-- AKMM, (25.4)–(25.5), p. 755: the iteration matrix of the deviations from the steady
state. -/
noncomputable def twoBoxMatrix (σ₁ σ₂ σ₃ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - σ₁ * κ - σ₁ * σ₂, σ₁ * σ₂; σ₃, 1 - σ₃]

/-- AKMM, p. 755: under the conditions of `climate_twoBox_tendsto` the iteration matrix of
(25.4)–(25.5) is stable (all eigenvalues inside the unit circle, Miao's Definition 1.4.5). -/
theorem climate_twoBox_isStable {σ₁ σ₂ σ₃ κ : ℝ} (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) (h₃ : 0 < σ₃)
    (h₃' : σ₃ ≤ 1) (hκ : 0 < κ) (hσκ : σ₁ * (κ + σ₂) ≤ 1) :
    Miao.DifferenceEquations.IsStableMatrix ((twoBoxMatrix σ₁ σ₂ σ₃ κ).map Complex.ofRealHom) := by
  rw [Miao.DifferenceEquations.isStableMatrix_iff_tendsto]
  intro v
  set M := twoBoxMatrix σ₁ σ₂ σ₃ κ
  have hsucc : ∀ t, Matrix.mulVec (M ^ (t + 1)) v =
      Matrix.mulVec M (Matrix.mulVec (M ^ t) v) := fun t => by
    rw [pow_succ', Matrix.mulVec_mulVec]
  obtain ⟨hu, hw⟩ := climate_dev_tendsto h₁ h₂ h₃ h₃' hκ hσκ
    (u := fun t => Matrix.mulVec (M ^ t) v 0) (w := fun t => Matrix.mulVec (M ^ t) v 1)
    (fun t => by
      rw [hsucc]
      simp [M, twoBoxMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
    (fun t => by
      rw [hsucc]
      simp [M, twoBoxMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa using hu
  · simpa using hw

end AKMM.Sustainability
