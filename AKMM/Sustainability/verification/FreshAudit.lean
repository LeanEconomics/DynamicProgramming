import RealExchangeRate.CESIndex
import ContinuousTime.Exponential
import DifferenceEquations.LinearSystems
import Mathlib.LinearAlgebra.Matrix.Notation
import OperatorsFixedPoints.NonnegativeMatrices
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Filter.AtTopBot.Archimedean
import DeterministicApplications.CakeEating
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Tangent-line inequalities

Auxiliary inequalities used throughout the chapter's optimisation arguments (AKMM Chapter 25,
pp. 763–782): every optimum in the chapter is verified by a tangent-line (supergradient)
bound rather than by first-order conditions alone.

* `log y ≤ log c + (y − c)/c`, strictly for `y ≠ c` (`sust_log_le_tangent`,
  `sust_log_lt_tangent`);
* for `x ≥ 1`, `c^x + x c^{x−1}(y − c) ≤ y^x` (`sust_tangent_le_rpow`), strictly for `x > 1` and
  `y ≠ c` (`sust_tangent_lt_rpow`);
* for `0 < ν < 1`, `y^ν < c^ν + ν c^{ν−1}(y − c)` when `y ≠ c` (`sust_rpow_lt_tangent`).

The weak concave and negative-power versions are those of `RealExchangeRate.CESIndex`
(Obstfeld–Rogoff, p. 227): `ces_rpow_le_tangent`, `ces_tangent_le_rpow`.
-/

namespace AKMM.Sustainability

open Real

/-- Tangent-line bound for the logarithm: `log y ≤ log c + (y − c)/c`. -/
theorem sust_log_le_tangent {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Real.log y ≤ Real.log c + (y - c) / c := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hc)
  rw [Real.log_div hy.ne' hc.ne'] at h
  have : y / c - 1 = (y - c) / c := by field_simp
  linarith

/-- Strict tangent-line bound for the logarithm away from the tangency point. -/
theorem sust_log_lt_tangent {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (hyc : y ≠ c) :
    Real.log y < Real.log c + (y - c) / c := by
  have hne : y / c ≠ 1 := by
    intro h; exact hyc (by field_simp at h; linarith)
  have h := Real.log_lt_sub_one_of_pos (div_pos hy hc) hne
  rw [Real.log_div hy.ne' hc.ne'] at h
  have : y / c - 1 = (y - c) / c := by field_simp
  linarith

/-- Tangent-line bound for a convex power `x ≥ 1`: `c^x + x c^{x−1}(y − c) ≤ y^x`. -/
theorem sust_tangent_le_rpow {x y c : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    c ^ x + x * c ^ (x - 1) * (y - c) ≤ y ^ x := by
  have hs : -1 ≤ y / c - 1 := by have := div_nonneg hy hc.le; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hx
  rw [add_sub_cancel, div_rpow hy hc.le] at hb
  have hcx := rpow_pos_of_pos hc x
  rw [le_div_iff₀ hcx] at hb
  rw [rpow_sub_one hc.ne']
  calc c ^ x + x * (c ^ x / c) * (y - c) = (1 + x * (y / c - 1)) * c ^ x := by field_simp
    _ ≤ y ^ x := hb

/-- Strict tangent-line bound for a strictly convex power `x > 1` away from the tangency
point. -/
theorem sust_tangent_lt_rpow {x y c : ℝ} (hx : 1 < x) (hy : 0 ≤ y) (hc : 0 < c) (hyc : y ≠ c) :
    c ^ x + x * c ^ (x - 1) * (y - c) < y ^ x := by
  have hs : -1 ≤ y / c - 1 := by have := div_nonneg hy hc.le; linarith
  have hs' : y / c - 1 ≠ 0 := by
    intro h; exact hyc (by field_simp at h; linarith)
  have hb := one_add_mul_self_lt_rpow_one_add hs hs' hx
  rw [add_sub_cancel, div_rpow hy hc.le] at hb
  have hcx := rpow_pos_of_pos hc x
  rw [lt_div_iff₀ hcx] at hb
  rw [rpow_sub_one hc.ne']
  calc c ^ x + x * (c ^ x / c) * (y - c) = (1 + x * (y / c - 1)) * c ^ x := by field_simp
    _ < y ^ x := hb

/-- Strict tangent-line bound for a strictly concave power `0 < ν < 1` away from the tangency
point: `y^ν < c^ν + ν c^{ν−1}(y − c)`. -/
theorem sust_rpow_lt_tangent {ν y c : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hy : 0 ≤ y) (hc : 0 < c)
    (hyc : y ≠ c) : y ^ ν < c ^ ν + ν * c ^ (ν - 1) * (y - c) := by
  have hs : -1 ≤ y / c - 1 := by have := div_nonneg hy hc.le; linarith
  have hs' : y / c - 1 ≠ 0 := by
    intro h; exact hyc (by field_simp at h; linarith)
  have hb := rpow_one_add_lt_one_add_mul_self hs hs' hν0 hν1
  rw [add_sub_cancel, div_rpow hy hc.le] at hb
  have hcx := rpow_pos_of_pos hc ν
  rw [div_lt_iff₀ hcx] at hb
  rw [rpow_sub_one hc.ne']
  calc y ^ ν < (1 + ν * (y / c - 1)) * c ^ ν := hb
    _ = c ^ ν + ν * (c ^ ν / c) * (y - c) := by field_simp

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The carbon cycle

AKMM, §25.3.2 (pp. 755–756) and the carbon accounting of §25.4.2 (p. 770).

* (25.6)–(25.8), corrected. As printed the outflows `φ₁₂S` from the atmosphere and `φ₃₂Sᴸ` from
  the deep ocean carry a plus sign, although (25.7) adds them to the upper reservoir, so total
  carbon grows by `2φ₁₂S + 2φ₃₂Sᴸ + E` (`eq_25_6_printed_total`, `eq_25_6_printed_false`).
  With the signs corrected, total carbon grows by exactly the emissions (`eq_25_6_total`).
* Without emissions the corrected map is a mass-preserving linear map: the transpose of its
  matrix is a Markov matrix in the sense of Sargent–Stachurski (`carbon_isMarkov`), so an
  invariant distribution of carbon exists (`carbon_exists_invariant`, from
  `IsMarkov.exists_stationary`); for positive flows it is unique for each total, with
  `φ₁₂S = φ₂₁Sᵁ` and `φ₂₃Sᵁ = φ₃₂Sᴸ` (`carbon_invariant_iff`, `carbon_invariant_unique`).
* Linearity ("the key feature again is linearity", p. 756): the stocks are the emission-free
  path plus a time-invariant kernel applied to past emissions (`carbon_superposition`), so the
  three-reservoir model is of the form (25.9).
* (25.9)–(25.10): excess carbon `S_t − S₀ = Σ_v (1 − d_{t−v})E_v` (`excessCarbon`), the
  book's lag form (`eq_25_9`), the response of `S_{t+j}` to an emission at `t` is `1 − d_j`
  (`excessCarbon_pulse`); the GHKT kernel (25.10) lies in `[0, 1]`, falls with the lag
  (`ghktKernel_mem_Icc`, `ghktKernel_antitone`) and tends to `φ_L`, the share that stays
  forever (`eq_25_10_tendsto`); the within-period loss is `(1 − φ_L)(1 − φ₀)`, not `1 − φ₀`
  as the text says (`eq_25_10_within_period`); the discounted kernel sum has the closed form
  `φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ))` (`ghktKernel_hasSum`).
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- The flow parameters `(φ₁₂, φ₂₁, φ₂₃, φ₃₂)` of the three-reservoir carbon cycle. -/
structure CarbonFlows where
  /-- atmosphere to upper ocean and biosphere -/
  f12 : ℝ
  /-- upper reservoir to atmosphere -/
  f21 : ℝ
  /-- upper reservoir to deep ocean -/
  f23 : ℝ
  /-- deep ocean to upper reservoir -/
  f32 : ℝ

/-- AKMM, (25.6)–(25.8), p. 755, with the outflow signs corrected: the emission-free part of
the carbon cycle as a linear map of `(S, Sᵁ, Sᴸ)`. -/
def carbonLin (p : CarbonFlows) : ℝ × ℝ × ℝ →ₗ[ℝ] ℝ × ℝ × ℝ where
  toFun x := (x.1 - p.f12 * x.1 + p.f21 * x.2.1,
    x.2.1 + p.f12 * x.1 - (p.f21 + p.f23) * x.2.1 + p.f32 * x.2.2,
    x.2.2 + p.f23 * x.2.1 - p.f32 * x.2.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Prod.smul_mk,
      Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

/-- AKMM, (25.6)–(25.8), p. 755, corrected: one period of the carbon cycle with emissions `E`,
which enter the atmosphere. -/
def carbonStep (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  carbonLin p x + E • ((1 : ℝ), (0 : ℝ), (0 : ℝ))

/-- AKMM, (25.6)–(25.8) as printed, p. 755: `S_t − S_{t−1} = φ₁₂S_{t−1} + φ₂₁Sᵁ_{t−1} + E_{t−1}`
and `Sᴸ_t − Sᴸ_{t−1} = φ₂₃Sᵁ_{t−1} + φ₃₂Sᴸ_{t−1}`. -/
def carbonStepPrinted (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.1 + p.f12 * x.1 + p.f21 * x.2.1 + E,
    x.2.1 + p.f12 * x.1 - (p.f21 + p.f23) * x.2.1 + p.f32 * x.2.2,
    x.2.2 + p.f23 * x.2.1 + p.f32 * x.2.2)

/-- Total carbon in the three reservoirs. -/
def carbonTotal (x : ℝ × ℝ × ℝ) : ℝ := x.1 + x.2.1 + x.2.2

/-- AKMM, (25.6)–(25.8), p. 755, corrected: the cycle only moves carbon between reservoirs, so
total carbon increases by exactly the emissions. -/
theorem eq_25_6_total (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) :
    carbonTotal (carbonStep p E x) = carbonTotal x + E := by
  simp [carbonStep, carbonLin, carbonTotal]
  ring

/-- AKMM, (25.6)–(25.8) as printed, p. 755: total carbon grows by `2φ₁₂S + 2φ₃₂Sᴸ + E`. -/
theorem eq_25_6_printed_total (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) :
    carbonTotal (carbonStepPrinted p E x) = carbonTotal x + 2 * p.f12 * x.1 +
      2 * p.f32 * x.2.2 + E := by
  simp [carbonStepPrinted, carbonTotal]
  ring

/-- AKMM, p. 755: the printed system does not conserve carbon: with Folini et al.'s flows and
one unit of carbon in the atmosphere and no emissions, total carbon rises. -/
theorem eq_25_6_printed_false :
    carbonTotal (carbonStepPrinted ⟨0.053, 0.0536, 0.0042, 0.001422⟩ 0 (1, 0, 0)) ≠
      carbonTotal ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
  rw [eq_25_6_printed_total]
  norm_num

/-- The matrix of `carbonLin` acting on `(S, Sᵁ, Sᴸ)` as a column vector. -/
def carbonMatrix (p : CarbonFlows) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - p.f12, p.f21, 0; p.f12, 1 - p.f21 - p.f23, p.f32; 0, p.f23, 1 - p.f32]

/-- AKMM, p. 755: with flows that are shares (`0 ≤ φ₁₂ ≤ 1`, `φ₂₁, φ₂₃ ≥ 0`,
`φ₂₁ + φ₂₃ ≤ 1`, `0 ≤ φ₃₂ ≤ 1`) the carbon matrix is column-stochastic: its transpose is a
Markov matrix in the sense of Sargent–Stachurski (Vol. 1, p. 71). -/
theorem carbon_isMarkov {p : CarbonFlows} (h12 : 0 ≤ p.f12) (h12' : p.f12 ≤ 1)
    (h21 : 0 ≤ p.f21) (h23 : 0 ≤ p.f23) (h2 : p.f21 + p.f23 ≤ 1) (h32 : 0 ≤ p.f32)
    (h32' : p.f32 ≤ 1) :
    SargentStachurski.OperatorsFixedPoints.IsMarkov (carbonMatrix p).transpose where
  nonneg i j := by
    fin_cases i <;> fin_cases j <;> simp [carbonMatrix] <;> linarith
  rowsum i := by
    fin_cases i <;> (simp [carbonMatrix, Fin.sum_univ_three]; try ring)

/-- AKMM, p. 755: the matrix represents the corrected emission-free cycle. -/
theorem carbonMatrix_mulVec (p : CarbonFlows) (x : ℝ × ℝ × ℝ) :
    Matrix.mulVec (carbonMatrix p) ![x.1, x.2.1, x.2.2] =
      ![(carbonLin p x).1, (carbonLin p x).2.1, (carbonLin p x).2.2] := by
  ext i
  fin_cases i <;> (simp [carbonMatrix, carbonLin, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]; try ring)

/-- AKMM, p. 755: without emissions there is an invariant distribution of carbon across the
reservoirs (Perron–Frobenius, `IsMarkov.exists_stationary` of `OperatorsFixedPoints`). -/
theorem carbon_exists_invariant {p : CarbonFlows} (h12 : 0 ≤ p.f12) (h12' : p.f12 ≤ 1)
    (h21 : 0 ≤ p.f21) (h23 : 0 ≤ p.f23) (h2 : p.f21 + p.f23 ≤ 1) (h32 : 0 ≤ p.f32)
    (h32' : p.f32 ≤ 1) :
    ∃ x : ℝ × ℝ × ℝ, 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2 ∧ carbonTotal x = 1 ∧
      carbonStep p 0 x = x := by
  obtain ⟨ψ, hψ0, hψ1, hψ⟩ := (carbon_isMarkov h12 h12' h21 h23 h2 h32 h32').exists_stationary
  refine ⟨(ψ 0, ψ 1, ψ 2), hψ0 0, hψ0 1, hψ0 2, ?_, ?_⟩
  · simpa [carbonTotal, Fin.sum_univ_three] using hψ1
  · have h0 := congrFun hψ 0
    have h1 := congrFun hψ 1
    have h2' := congrFun hψ 2
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, carbonMatrix] at h0 h1 h2'
    simp only [carbonStep, carbonLin, LinearMap.coe_mk, AddHom.coe_mk, zero_smul, add_zero,
      Prod.mk.injEq]
    refine ⟨by linarith, by linarith, by linarith⟩

/-- AKMM, p. 755: without emissions, a distribution `(S, Sᵁ, Sᴸ)` is invariant iff the flows
balance pairwise: `φ₁₂S = φ₂₁Sᵁ` and `φ₂₃Sᵁ = φ₃₂Sᴸ`. -/
theorem carbon_invariant_iff (p : CarbonFlows) (x : ℝ × ℝ × ℝ) :
    carbonStep p 0 x = x ↔ p.f12 * x.1 = p.f21 * x.2.1 ∧ p.f23 * x.2.1 = p.f32 * x.2.2 := by
  simp only [carbonStep, carbonLin, LinearMap.coe_mk, AddHom.coe_mk, zero_smul, add_zero]
  obtain ⟨a, b, c⟩ := x
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, by linarith⟩

/-- AKMM, p. 755: with positive flows the invariant distribution of a given total is unique. -/
theorem carbon_invariant_unique {p : CarbonFlows} (h12 : 0 < p.f12) (h21 : 0 < p.f21)
    (h23 : 0 < p.f23) (h32 : 0 < p.f32) {x y : ℝ × ℝ × ℝ} (hx : carbonStep p 0 x = x)
    (hy : carbonStep p 0 y = y) (hxy : carbonTotal x = carbonTotal y) : x = y := by
  rw [carbon_invariant_iff] at hx hy
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  simp only [carbonTotal] at hx hy hxy
  -- express everything through the atmospheric stock
  have hb : b = p.f12 / p.f21 * a := by field_simp; linarith [hx.1]
  have hb' : b' = p.f12 / p.f21 * a' := by field_simp; linarith [hy.1]
  have hc : c = p.f23 / p.f32 * b := by field_simp; linarith [hx.2]
  have hc' : c' = p.f23 / p.f32 * b' := by field_simp; linarith [hy.2]
  have hk : 0 < 1 + p.f12 / p.f21 + p.f23 / p.f32 * (p.f12 / p.f21) := by positivity
  have haa : a = a' := by
    rw [hc, hb, hc', hb'] at hxy
    have : (1 + p.f12 / p.f21 + p.f23 / p.f32 * (p.f12 / p.f21)) * (a - a') = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  subst haa
  have hbb : b = b' := by rw [hb, hb']
  subst hbb
  have hcc : c = c' := by rw [hc, hc']
  rw [hcc]

/-- The carbon stocks under an emission path `E`, from initial stocks `x₀`. -/
def carbonPath (p : CarbonFlows) (E : ℕ → ℝ) (x₀ : ℝ × ℝ × ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => x₀
  | t + 1 => carbonStep p (E t) (carbonPath p E x₀ t)

/-- The unit-pulse emission path: one unit at date `0`. -/
def carbonPulse (t : ℕ) : ℝ := if t = 0 then 1 else 0

/-- The response of the stocks to a unit pulse, `j` periods after it is emitted. -/
def carbonResponse (p : CarbonFlows) (j : ℕ) : ℝ × ℝ × ℝ :=
  carbonPath p carbonPulse 0 (j + 1)

/-- AKMM, p. 756, "the key feature again is linearity": the stocks are the emission-free path
plus a time-invariant response kernel applied to past emissions,
`x_t = x_t⁰ + Σ_{v<t} E_v · r_{t−1−v}`. -/
theorem carbon_superposition (p : CarbonFlows) (E : ℕ → ℝ) (x₀ : ℝ × ℝ × ℝ) (t : ℕ) :
    carbonPath p E x₀ t = carbonPath p 0 x₀ t +
      ∑ v ∈ Finset.range t, E v • carbonResponse p (t - 1 - v) := by
  -- the response kernel itself evolves by the emission-free map
  have hresp : ∀ j, carbonResponse p (j + 1) = carbonLin p (carbonResponse p j) := by
    intro j
    simp [carbonResponse, carbonPath, carbonStep, carbonPulse]
  have hresp0 : carbonResponse p 0 = ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    simp [carbonResponse, carbonPath, carbonStep, carbonPulse]
  induction t with
  | zero => simp [carbonPath]
  | succ n ih =>
    rw [carbonPath, ih, carbonPath, Finset.sum_range_succ]
    simp only [carbonStep, map_add, map_sum, map_smul, Pi.zero_apply, zero_smul, add_zero]
    have hsum : ∑ v ∈ Finset.range n, E v • carbonLin p (carbonResponse p (n - 1 - v)) =
        ∑ v ∈ Finset.range n, E v • carbonResponse p (n + 1 - 1 - v) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv' : v < n := Finset.mem_range.mp hv
      have : n + 1 - 1 - v = n - 1 - v + 1 := by omega
      rw [this, hresp]
    rw [hsum, show n + 1 - 1 - n = 0 by omega, hresp0]
    abel

/-- AKMM, (25.10), p. 756: the GHKT kernel `1 − d_s = φ_L + (1 − φ_L)φ₀(1 − φ)^s`. -/
noncomputable def ghktKernel (φL φ0 φ : ℝ) (s : ℕ) : ℝ := φL + (1 - φL) * φ0 * (1 - φ) ^ s

/-- AKMM, p. 756: with `0 < φ < 2` (in particular a depreciation rate `φ ∈ (0, 1]`) the kernel
tends to `φ_L`: the share `φ_L` of an emission stays in the atmosphere forever. -/
theorem eq_25_10_tendsto {φL φ0 φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2) :
    Tendsto (ghktKernel φL φ0 φ) atTop (𝓝 φL) := by
  have hq : |1 - φ| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).const_mul ((1 - φL) * φ0)
  have h2 := this.const_add φL
  rw [mul_zero, add_zero] at h2
  exact h2

/-- AKMM, p. 756: with shares `φ_L, φ₀, φ ∈ [0, 1]` the kernel is a share. -/
theorem ghktKernel_mem_Icc {φL φ0 φ : ℝ} (hL : 0 ≤ φL) (hL1 : φL ≤ 1) (h0 : 0 ≤ φ0)
    (h01 : φ0 ≤ 1) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1) (s : ℕ) :
    ghktKernel φL φ0 φ s ∈ Set.Icc 0 1 := by
  have hp : 0 ≤ (1 - φ) ^ s := pow_nonneg (by linarith) s
  have hp1 : (1 - φ) ^ s ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hm : 0 ≤ (1 - φL) * φ0 := mul_nonneg (by linarith) h0
  constructor
  · unfold ghktKernel; positivity
  · unfold ghktKernel
    nlinarith [mul_le_mul_of_nonneg_left hp1 hm]

/-- AKMM, p. 756: the share remaining in the atmosphere falls with the lag. -/
theorem ghktKernel_antitone {φL φ0 φ : ℝ} (hL1 : φL ≤ 1) (h0 : 0 ≤ φ0) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) : Antitone (ghktKernel φL φ0 φ) := by
  intro s s' hss
  have hm : 0 ≤ (1 - φL) * φ0 := mul_nonneg (by linarith) h0
  unfold ghktKernel
  have := pow_le_pow_of_le_one (by linarith : 0 ≤ 1 - φ) (by linarith) hss
  nlinarith [mul_le_mul_of_nonneg_left this hm]

/-- AKMM, p. 756: the text says "the share that leaves the atmosphere within a period [is]
`1 − φ₀`"; by (25.10) the within-period loss is `d₀ = (1 − φ_L)(1 − φ₀)`: `1 − φ₀` is the share
of the non-permanent part `1 − φ_L` that leaves. The three shares add up to one. -/
theorem eq_25_10_within_period (φL φ0 φ : ℝ) :
    1 - ghktKernel φL φ0 φ 0 = (1 - φL) * (1 - φ0) ∧
      φL + (1 - φL) * (1 - φ0) + (1 - φL) * φ0 = 1 := by
  exact ⟨by simp only [ghktKernel, pow_zero]; ring, by ring⟩

/-- AKMM, p. 756: the within-period loss is `1 − φ₀` only when `φ_L = 0`; with the GHKT
calibration `φ_L = 0.2`, `φ₀ = 0.393` it is `0.4856`, not `0.607`. -/
theorem eq_25_10_within_period_printed_false :
    1 - ghktKernel 0.2 0.393 0.0228 0 ≠ 1 - 0.393 := by
  rw [(eq_25_10_within_period _ _ _).1]
  norm_num

/-- AKMM, (25.32) via (25.10): the discounted kernel sum has the closed form
`Σ_j β^j(1 − d_j) = φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ))`. -/
theorem ghktKernel_hasSum {φL φ0 φ β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) :
    HasSum (fun j => β ^ j * ghktKernel φL φ0 φ j)
      (φL / (1 - β) + (1 - φL) * φ0 / (1 - β * (1 - φ))) := by
  have hq0 : 0 ≤ β * (1 - φ) := mul_nonneg hβ0 (by linarith)
  have hq1 : β * (1 - φ) < 1 := by nlinarith
  have h1 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left φL
  have h2 := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - φL) * φ0)
  convert h1.add h2 using 1
  · funext j; simp only [ghktKernel, mul_pow]; ring
  · field_simp

/-- AKMM, (25.9), p. 756 and p. 770: excess atmospheric carbon at `t` from emissions `E_v` at
dates `v ≤ t`, `S_t − S₀ = Σ_{v ≤ t}(1 − d_{t−v})E_v` (the kernel `k = 1 − d`). -/
def excessCarbon (k E : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ v ∈ Finset.range (t + 1), k (t - v) * E v

/-- AKMM, (25.9), p. 756: in the book's lag form, `S_t − S₀ = Σ_{s ≤ t}(1 − d_s)E_{t−s}` (the
book writes the summation index as `t`; emissions start at date `0`). -/
theorem eq_25_9 (k E : ℕ → ℝ) (t : ℕ) :
    excessCarbon k E t = ∑ s ∈ Finset.range (t + 1), k s * E (t - s) := by
  unfold excessCarbon
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.mp hs
  congr 2; omega

/-- AKMM, p. 770: one more unit of emissions at date `t` raises excess carbon at `t + j` by
`1 − d_j`: `∂S_{t+j}/∂E_t = 1 − d_j`. -/
theorem excessCarbon_pulse (k E : ℕ → ℝ) (t j : ℕ) (h : ℝ) :
    excessCarbon k (fun v => E v + if v = t then h else 0) (t + j) =
      excessCarbon k E (t + j) + h * k j := by
  unfold excessCarbon
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range (t + j + 1)) t]
  simp only [Finset.mem_range, show t < t + j + 1 by omega, ↓reduceIte]
  rw [show t + j - t = j by omega]
  ring

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Damages

AKMM, §25.3.5 (pp. 759–764), the damage functions.

* Nordhaus–Sztorc damages `D(T) = 1 − 1/(1 + aT²)` (p. 763): `D = aT²/(1 + aT²)`
  (`nordhausD_eq`), `0 ≤ D ≤ aT²` and `aT² − D ≤ a²T⁴`, so `aT²` is the approximation near
  `0` (`nordhausD_approx`), which with `a = 0.00267` is `0.02403(T/3)²`, the book's
  "`0.024(T/3)²`" (`nordhausD_coefficient`); `D → 1` (footnote 12, `nordhausD_tendsto`).
  `D` is convex on `[−1/√(3a), 1/√(3a)]` (`nordhausD_convexOn`) but, footnote 12, not convex
  on `[0, ∞)` (`nordhausD_not_convexOn`).
* Adaptation (p. 763): with total damages `(T − a)^x/x + a`, `x > 1`, adaptation `a ∈ [0, T]`:
  for `T ≥ 1` the unique cost-minimising adaptation is `a = T − 1` and the reduced-form damage
  is `T + (1 − x)/x`, linear in `T` whatever `x` (`adaptation_optimal`,
  `adaptation_unique`); for `T < 1` the book's formula does not apply: the minimiser is
  `a = 0` with damage `T^x/x` (`adaptation_low_T`).
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- AKMM, p. 763: Nordhaus and Sztorc's damage share `D(T) = 1 − 1/(1 + aT²)` (`a = 0.00267`). -/
noncomputable def nordhausD (a T : ℝ) : ℝ := 1 - 1 / (1 + a * T ^ 2)

/-- AKMM, p. 763: `D(T) = aT²/(1 + aT²)`. -/
theorem nordhausD_eq {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    nordhausD a T = a * T ^ 2 / (1 + a * T ^ 2) := by
  have : 0 < 1 + a * T ^ 2 := by positivity
  unfold nordhausD
  field_simp
  ring

/-- AKMM, p. 763: near `0`, `D(T) ≈ aT²`: `0 ≤ D ≤ aT²` and the error is at most `a²T⁴`. -/
theorem nordhausD_approx {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    0 ≤ nordhausD a T ∧ nordhausD a T ≤ a * T ^ 2 ∧
      a * T ^ 2 - nordhausD a T ≤ a ^ 2 * T ^ 4 := by
  have hp : 0 ≤ a * T ^ 2 := by positivity
  have hd : 0 < 1 + a * T ^ 2 := by positivity
  rw [nordhausD_eq ha]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hd]; nlinarith
  · have : a * T ^ 2 - a * T ^ 2 / (1 + a * T ^ 2) = (a * T ^ 2) ^ 2 / (1 + a * T ^ 2) := by
      field_simp; ring
    rw [this, div_le_iff₀ hd]
    nlinarith [sq_nonneg (a * T ^ 2)]

/-- AKMM, p. 763: the approximation `0.00267T²` is `0.02403(T/3)²`, the book's
"`0.024(T/3)²`". -/
theorem nordhausD_coefficient (T : ℝ) : (0.00267 : ℝ) * T ^ 2 = 0.02403 * (T / 3) ^ 2 := by
  ring

/-- AKMM, p. 763, footnote 12: "it asymptotes to 1 (all of output is lost) as `T` goes to
infinity". -/
theorem nordhausD_tendsto {a : ℝ} (ha : 0 < a) : Tendsto (nordhausD a) atTop (𝓝 1) := by
  have h : Tendsto (fun T : ℝ => 1 + a * T ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop ha)
  have := (tendsto_inv_atTop_zero.comp h).const_sub 1
  rw [sub_zero] at this
  exact this.congr (fun T => by simp [nordhausD])

/-- AKMM, p. 763, footnote 12: `D` is convex near `0`, on `[−1/√(3a), 1/√(3a)]`, where
`D''(T) = 2a(1 − 3aT²)/(1 + aT²)³ ≥ 0`. -/
theorem nordhausD_convexOn {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Set.Icc (-(1 / Real.sqrt (3 * a))) (1 / Real.sqrt (3 * a))) (nordhausD a) := by
  set r := 1 / Real.sqrt (3 * a) with hr
  have hpos : ∀ T : ℝ, 0 < 1 + a * T ^ 2 := fun T => by positivity
  have hD : ∀ T, HasDerivAt (nordhausD a) (2 * a * T / (1 + a * T ^ 2) ^ 2) T := by
    intro T
    have h1 : HasDerivAt (fun T : ℝ => 1 + a * T ^ 2) (a * (2 * T)) T := by
      simpa using ((hasDerivAt_pow 2 T).const_mul a).const_add 1
    have h2 := (h1.inv (hpos T).ne').const_sub 1
    unfold nordhausD
    simp only [one_div]
    convert h2 using 1
    field_simp
  have hD2 : ∀ T, HasDerivAt (fun T => 2 * a * T / (1 + a * T ^ 2) ^ 2)
      (2 * a * (1 - 3 * a * T ^ 2) / (1 + a * T ^ 2) ^ 3) T := by
    intro T
    have h1 : HasDerivAt (fun T : ℝ => 1 + a * T ^ 2) (a * (2 * T)) T := by
      simpa using ((hasDerivAt_pow 2 T).const_mul a).const_add 1
    have h3 := ((hasDerivAt_id T).const_mul (2 * a)).div (h1.pow 2)
      (pow_ne_zero 2 (hpos T).ne')
    convert h3 using 1
    · funext y; simp [id]
    · have := (hpos T).ne'
      simp only [Pi.pow_apply, id]
      field_simp
      ring
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun T _ => (hD T).continuousAt.continuousWithinAt)
    (fun T _ => (hD T).hasDerivWithinAt) (fun T _ => (hD2 T).hasDerivWithinAt) ?_
  intro T hT
  rw [interior_Icc] at hT
  have h3a : 0 < 3 * a := by positivity
  have hsq : 0 < Real.sqrt (3 * a) := Real.sqrt_pos.mpr h3a
  have hT2 : T ^ 2 < r ^ 2 := by
    have : |T| < r := abs_lt.mpr ⟨hT.1, hT.2⟩
    have hr0 : 0 ≤ r := by positivity
    calc T ^ 2 = |T| ^ 2 := (sq_abs T).symm
      _ < r ^ 2 := by gcongr
  have hr2 : r ^ 2 = 1 / (3 * a) := by
    rw [hr, div_pow, Real.sq_sqrt h3a.le, one_pow]
  rw [hr2] at hT2
  have : 3 * a * T ^ 2 < 1 := by
    rw [lt_div_iff₀ h3a] at hT2; linarith
  have h4 := hpos T
  apply div_nonneg _ (by positivity)
  nlinarith

/-- AKMM, p. 763, footnote 12: "Globally, the damage function is not convex": `D` is not convex
on `[0, ∞)`. A convex function vanishing at `0` and positive at `1` grows at least linearly,
while `D < 1`. -/
theorem nordhausD_not_convexOn {a : ℝ} (ha : 0 < a) : ¬ ConvexOn ℝ (Set.Ici 0) (nordhausD a) := by
  intro hc
  set d := nordhausD a 1 with hd
  have hd0 : 0 < d := by
    rw [hd, nordhausD_eq ha.le]; positivity
  have hlt : ∀ T, nordhausD a T < 1 := fun T => by
    unfold nordhausD
    have : 0 < 1 / (1 + a * T ^ 2) := by positivity
    linarith
  -- at `T = 2/d ≥ 1`, convexity between `0` and `T` forces `D(1) ≤ D(T)/T < 1/T = d/2`
  set T := 2 / d with hT
  have hd1 : d < 1 := hlt 1
  have hT1 : 1 ≤ T := by rw [hT, le_div_iff₀ hd0]; linarith
  have hT0 : 0 < T := by positivity
  have hw1 : 0 ≤ 1 - 1 / T := by rw [sub_nonneg, div_le_one hT0]; exact hT1
  have hw2 : 0 ≤ 1 / T := by positivity
  have hw : (1 - 1 / T) + 1 / T = 1 := by ring
  have h := hc.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0.le) hw1 hw2 hw
  simp only [smul_eq_mul, mul_zero, zero_add, one_div] at h
  have hx : T⁻¹ * T = 1 := inv_mul_cancel₀ hT0.ne'
  rw [hx] at h
  have h0 : nordhausD a 0 = 0 := by simp [nordhausD]
  rw [h0, mul_zero, zero_add] at h
  have hDT := hlt T
  have : d ≤ T⁻¹ * nordhausD a T := h
  have hTinv : T⁻¹ = d / 2 := by rw [hT]; field_simp
  rw [hTinv] at this
  nlinarith

/-- AKMM, p. 763: total damages in output units, `(T − a)^x/x + a`, with adaptation `a`. -/
noncomputable def adaptCost (x T a : ℝ) : ℝ := (T - a) ^ x / x + a

/-- AKMM, p. 763: for `x > 1` and `T ≥ 1` the adaptation `a = T − 1` minimises damages over
`a ∈ [0, T]`, and the reduced-form damage is `D(T) = T + (1 − x)/x`, linear in `T` whatever
`x`. -/
theorem adaptation_optimal {x T : ℝ} (hx : 1 < x) (hT : 1 ≤ T) :
    T - 1 ∈ Set.Icc 0 T ∧ adaptCost x T (T - 1) = T + (1 - x) / x ∧
      ∀ a ∈ Set.Icc 0 T, adaptCost x T (T - 1) ≤ adaptCost x T a := by
  have hx0 : 0 < x := by linarith
  have hval : adaptCost x T (T - 1) = T + (1 - x) / x := by
    simp only [adaptCost, sub_sub_cancel, one_rpow]
    field_simp
    ring
  refine ⟨⟨by linarith, by linarith⟩, hval, fun a ha => ?_⟩
  rw [hval]
  have hb := sust_tangent_le_rpow (y := T - a) hx.le (by linarith [ha.2]) one_pos
  simp only [one_rpow, mul_one] at hb
  unfold adaptCost
  rw [div_add' _ _ _ hx0.ne', le_div_iff₀ hx0]
  have : (T + (1 - x) / x) * x = T * x + 1 - x := by field_simp; ring
  rw [this]
  nlinarith

/-- AKMM, p. 763: the minimiser `a = T − 1` is unique. -/
theorem adaptation_unique {x T a : ℝ} (hx : 1 < x) (ha : a ∈ Set.Icc 0 T)
    (hne : a ≠ T - 1) : adaptCost x T (T - 1) < adaptCost x T a := by
  have hx0 : 0 < x := by linarith
  have hb := sust_tangent_lt_rpow (y := T - a) hx (by linarith [ha.2]) one_pos
    (by intro h; exact hne (by linarith))
  simp only [one_rpow, mul_one] at hb
  unfold adaptCost
  simp only [sub_sub_cancel, one_rpow]
  rw [div_add' _ _ _ hx0.ne', div_add' _ _ _ hx0.ne', div_lt_div_iff_of_pos_right hx0]
  nlinarith

/-- AKMM, p. 763 ("so long as `T ≥ 1`"): for `0 ≤ T ≤ 1` no adaptation is optimal and the
reduced-form damage is `T^x/x`, so the linear form holds only for `T ≥ 1`. -/
theorem adaptation_low_T {x T : ℝ} (hx : 1 ≤ x) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    adaptCost x T 0 = T ^ x / x ∧ ∀ a ∈ Set.Icc 0 T, adaptCost x T 0 ≤ adaptCost x T a := by
  have hx0 : 0 < x := by linarith
  refine ⟨by simp [adaptCost], fun a ha => ?_⟩
  unfold adaptCost
  simp only [sub_zero, add_zero]
  rcases hT0.lt_or_eq with hT | hT
  · have hb := sust_tangent_le_rpow (y := T - a) hx (by linarith [ha.2]) hT
    have hpow : T ^ (x - 1) ≤ 1 := Real.rpow_le_one hT0 hT1 (by linarith)
    have hxa : x * T ^ (x - 1) * a ≤ x * a := by
      have := mul_le_mul_of_nonneg_left hpow hx0.le
      nlinarith [ha.1]
    rw [div_add' _ _ _ hx0.ne', div_le_div_iff_of_pos_right hx0]
    nlinarith
  · subst hT
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    simp [ha0]

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A static one-region integrated assessment model

AKMM, §25.4.1 (pp. 764–767). Output `Y = AE^ν` (25.12), coal at marginal cost `p`, damages
`γE²` (25.14), consumption (25.15). Throughout `A > 0`, `0 < ν < 1`, `p > 0`.

* The market economy: the first-order condition (25.16) has the unique solution
  `E(τ) = (νA/(p + τ))^{1/(1−ν)}` (`eq_25_16`), which is the firm's unique optimum
  (`static_firm_optimal`), strictly decreasing in the tax (`staticE_strictAnti`).
* The planner (25.17)–(25.18): a unique interior optimum `E*` exists (`eq_25_18_exists`), it
  solves (25.18), maximises consumption (`eq_25_17`) and is unique (`eq_25_17_unique`); the
  laissez-faire economy emits too much (`static_laissez_faire_excess`) and the Pigou tax
  `τ = 2γE*` implements `E*` (`static_pigou`).
* "τ = 0 constitutes a maximum" for the private economy, and its derivative there is zero, so a
  small tax has second-order private costs (`static_private_max`,
  `static_private_hasDerivAt`, `static_private_deriv_zero`).
* Prices versus quantities (25.19): a cap at `E*` has the unique equilibrium permit price
  `λ = 2γE*` (`eq_25_19`); a non-binding cap gives `λ = 0` (`static_cap_nonbinding`); a
  binding cap gives `λ = νAĒ^{ν−1} − p > 0` (`static_cap_binding`).
* Two firms (p. 767), with the coal cost `p` the book's planning problem omits: the planner's
  first-order conditions `ν_iAE_i^{ν_i−1} = p + 2γ(E₁ + E₂)` have a solution
  (`static_two_exists`), which is the unique optimum (`static_two_optimal`,
  `static_two_unique`); the tax `2γ(E₁* + E₂*)` implements it (`static_two_pigou`) and so does
  a single aggregate cap, whose permit price equals the tax (`static_two_cap`).
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- AKMM, (25.16), p. 765: the market demand for coal, `E(τ) = (νA/(p + τ))^{1/(1−ν)}`. -/
noncomputable def staticE (ν A p τ : ℝ) : ℝ := (ν * A / (p + τ)) ^ (1 / (1 - ν))

variable {ν A p : ℝ}

/-- `E(τ) > 0`. -/
theorem staticE_pos (hν0 : 0 < ν) (hA : 0 < A) {τ : ℝ} (hpτ : 0 < p + τ) :
    0 < staticE ν A p τ := by
  unfold staticE; positivity

/-- AKMM, (25.16), p. 765: for `E > 0` the firm's first-order condition `νAE^{ν−1} = p + τ`
holds iff `E = E(τ)`. -/
theorem eq_25_16 (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ E : ℝ} (hpτ : 0 < p + τ)
    (hE : 0 < E) : ν * A * E ^ (ν - 1) = p + τ ↔ E = staticE ν A p τ := by
  have hνA : 0 < ν * A := mul_pos hν0 hA
  have hne : ν - 1 ≠ 0 := by linarith
  have h1ν : (1 : ℝ) - ν ≠ 0 := (by linarith : (0 : ℝ) < 1 - ν).ne'
  constructor
  · intro h
    have h1 : E ^ (ν - 1) = (p + τ) / (ν * A) := by field_simp; linarith
    have h2 : E = ((p + τ) / (ν * A)) ^ (ν - 1)⁻¹ := by
      rw [← h1, Real.rpow_rpow_inv hE.le hne]
    rw [h2, staticE, ← inv_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1
    field_simp
    ring
  · intro h
    rw [h, staticE, ← Real.rpow_mul (by positivity)]
    have : 1 / (1 - ν) * (ν - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one]
    field_simp

/-- The marginal product `νAE^{ν−1}` is strictly decreasing in `E > 0`. -/
theorem static_mp_strictAnti (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {E E' : ℝ} (hE : 0 < E)
    (hEE : E < E') : ν * A * E' ^ (ν - 1) < ν * A * E ^ (ν - 1) := by
  have := Real.rpow_lt_rpow_of_neg hE hEE (by linarith : ν - 1 < 0)
  exact mul_lt_mul_of_pos_left this (mul_pos hν0 hA)

/-- `E < E(τ)` iff the marginal product at `E` exceeds `p + τ`. -/
theorem static_lt_staticE_iff (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ E : ℝ}
    (hpτ : 0 < p + τ) (hE : 0 < E) : E < staticE ν A p τ ↔ p + τ < ν * A * E ^ (ν - 1) := by
  have hs := staticE_pos hν0 hA hpτ
  have hfoc := (eq_25_16 hν0 hν1 hA hpτ hs).mpr rfl
  constructor
  · intro h; rw [← hfoc]; exact static_mp_strictAnti hν0 hν1 hA hE h
  · intro h
    by_contra hge
    rw [not_lt] at hge
    rcases hge.lt_or_eq with hlt | heq
    · have := static_mp_strictAnti hν0 hν1 hA hs hlt; linarith
    · rw [← heq] at h; linarith

/-- AKMM, p. 765: "there is direct negative relationship between `E` and `τ`": `E(τ)` is
strictly decreasing on `τ > −p`. -/
theorem staticE_strictAnti (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ τ' : ℝ}
    (hpτ : 0 < p + τ) (hττ : τ < τ') : staticE ν A p τ' < staticE ν A p τ := by
  have hpτ' : 0 < p + τ' := by linarith
  unfold staticE
  apply Real.rpow_lt_rpow (by positivity) _ (by have : 0 < 1 - ν := by linarith
                                                positivity)
  exact div_lt_div_of_pos_left (mul_pos hν0 hA) hpτ (by linarith)

/-- AKMM, (25.13), p. 765: `E(τ)` is the firm's unique optimum: for every `E ≥ 0`,
`AE^ν − (p + τ)E ≤ AE(τ)^ν − (p + τ)E(τ)`, strictly if `E ≠ E(τ)`. -/
theorem static_firm_optimal (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ E : ℝ}
    (hpτ : 0 < p + τ) (hE : 0 ≤ E) :
    A * E ^ ν - (p + τ) * E ≤ A * staticE ν A p τ ^ ν - (p + τ) * staticE ν A p τ ∧
      (E ≠ staticE ν A p τ →
        A * E ^ ν - (p + τ) * E < A * staticE ν A p τ ^ ν - (p + τ) * staticE ν A p τ) := by
  set s := staticE ν A p τ
  have hs := staticE_pos hν0 hA hpτ
  have hfoc := (eq_25_16 hν0 hν1 hA hpτ hs).mpr rfl
  constructor
  · have ht := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent hν0.le hν1.le hE hs
    nlinarith [mul_le_mul_of_nonneg_left ht hA.le]
  · intro hne
    have ht := sust_rpow_lt_tangent hν0 hν1 hE hs hne
    nlinarith [mul_lt_mul_of_pos_left ht hA]

/-- AKMM, (25.17), p. 766: consumption `AE^ν − pE − γE²`. -/
noncomputable def staticW (ν A p γ E : ℝ) : ℝ := A * E ^ ν - p * E - γ * E ^ 2

/-- AKMM, (25.18), p. 766: with `γ > 0` the planner's first-order condition
`νAE^{ν−1} = p + 2γE` has a solution `E* > 0`. -/
theorem eq_25_18_exists (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ : ℝ}
    (hγ : 0 < γ) : ∃ E, 0 < E ∧ ν * A * E ^ (ν - 1) = p + 2 * γ * E := by
  set E0 := staticE ν A p 0
  have hE0 : 0 < E0 := staticE_pos hν0 hA (by linarith)
  set E1 := staticE ν A p (2 * γ * E0)
  have hE1 : 0 < E1 := staticE_pos hν0 hA (by positivity)
  have h10 : E1 < E0 := staticE_strictAnti hν0 hν1 hA (by linarith) (by positivity)
  set g : ℝ → ℝ := fun E => ν * A * E ^ (ν - 1) - p - 2 * γ * E
  have hg1 : 0 < g E1 := by
    have := (eq_25_16 hν0 hν1 hA (by positivity) hE1).mpr rfl
    simp only [g]; nlinarith
  have hg0 : g E0 < 0 := by
    have := (eq_25_16 hν0 hν1 hA (by linarith : (0 : ℝ) < p + 0) hE0).mpr rfl
    simp only [g]; nlinarith
  have hcont : ContinuousOn g (Set.Icc E1 E0) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) (by fun_prop)
    refine ContinuousOn.mul continuousOn_const ?_
    exact continuousOn_id.rpow_const fun x hx =>
      Or.inl (by simp only [id]; exact (lt_of_lt_of_le hE1 hx.1).ne')
  obtain ⟨E, hE, hgE⟩ := intermediate_value_Icc' h10.le hcont ⟨hg0.le, hg1.le⟩
  refine ⟨E, by linarith [hE.1], ?_⟩
  simp only [g] at hgE
  linarith

/-- AKMM, (25.17)–(25.18), p. 766: a solution `E* > 0` of (25.18) maximises consumption over
`E ≥ 0`. -/
theorem eq_25_17 (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {γ Es E : ℝ} (hγ : 0 ≤ γ)
    (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) (hE : 0 ≤ E) :
    staticW ν A p γ E ≤ staticW ν A p γ Es := by
  have ht := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent hν0.le hν1.le hE hEs
  unfold staticW
  nlinarith [mul_le_mul_of_nonneg_left ht hA.le, mul_nonneg hγ (sq_nonneg (E - Es))]

/-- AKMM, p. 766: the planner's optimum is unique. -/
theorem eq_25_17_unique (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {γ Es E : ℝ} (hγ : 0 ≤ γ)
    (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) (hE : 0 ≤ E)
    (hne : E ≠ Es) : staticW ν A p γ E < staticW ν A p γ Es := by
  have ht := sust_rpow_lt_tangent hν0 hν1 hE hEs hne
  unfold staticW
  nlinarith [mul_lt_mul_of_pos_left ht hA, mul_nonneg hγ (sq_nonneg (E - Es))]

/-- AKMM, p. 766: with `γ > 0` and `τ = 0` "emissions will be too high relative to the
efficient level": `E* < E(0)`. -/
theorem static_laissez_faire_excess (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p)
    {γ Es : ℝ} (hγ : 0 < γ) (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) :
    Es < staticE ν A p 0 := by
  rw [static_lt_staticE_iff hν0 hν1 hA (by linarith) hEs, hfoc]
  have : 0 < 2 * γ * Es := by positivity
  linarith

/-- AKMM, p. 766, Pigou's recipe: the tax `τ = 2γE*` implements the optimum, `E(2γE*) = E*`. -/
theorem static_pigou (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ Es : ℝ}
    (hγ : 0 ≤ γ) (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) :
    staticE ν A p (2 * γ * Es) = Es :=
  ((eq_25_16 hν0 hν1 hA (by positivity) hEs).mp hfoc).symm

/-- AKMM, p. 766: the private surplus `AE(τ)^ν − pE(τ)` (consumption ignoring damages). -/
noncomputable def staticPrivate (ν A p τ : ℝ) : ℝ := A * staticE ν A p τ ^ ν - p * staticE ν A p τ

/-- AKMM, p. 766: "For the private economy, i.e., ignoring the externality entirely, `τ = 0`
constitutes a maximum". -/
theorem static_private_max (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {τ : ℝ}
    (hpτ : 0 < p + τ) : staticPrivate ν A p τ ≤ staticPrivate ν A p 0 := by
  have h := (static_firm_optimal hν0 hν1 hA (p := p) (τ := 0) (by linarith)
    (staticE_pos hν0 hA hpτ).le).1
  simp only [add_zero] at h
  exact h

/-- AKMM, p. 766: the private surplus is differentiable with derivative `τE'(τ)`, where
`E'(τ) = −E(τ)/((1 − ν)(p + τ))`. -/
theorem static_private_hasDerivAt (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) {τ : ℝ}
    (hpτ : 0 < p + τ) :
    HasDerivAt (staticPrivate ν A p)
      (τ * (-(staticE ν A p τ) / ((1 - ν) * (p + τ)))) τ := by
  have h1ν : 0 < 1 - ν := by linarith
  -- the derivative of `E(τ)`
  have hb : HasDerivAt (fun t => ν * A / (p + t)) (-(ν * A) / (p + τ) ^ 2) τ := by
    have := ((hasDerivAt_id τ).const_add p).inv hpτ.ne'
    convert this.const_mul (ν * A) using 1
    · funext t; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  have hE : HasDerivAt (staticE ν A p) (-(staticE ν A p τ) / ((1 - ν) * (p + τ))) τ := by
    have := hb.rpow_const (p := 1 / (1 - ν)) (Or.inl (by positivity))
    unfold staticE
    convert this using 1
    rw [Real.rpow_sub_one (by positivity)]
    field_simp
  -- near `τ`, `AE^ν − pE = E((p + t)/ν − p)` by the first-order condition
  have hev : staticPrivate ν A p =ᶠ[𝓝 τ]
      fun t => staticE ν A p t * ((p + t) / ν - p) := by
    filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
      (lt_mem_nhds hpτ)] with t ht
    have ht' : 0 < p + t := by simpa using ht
    have hs := staticE_pos hν0 hA ht'
    have hfoc := (eq_25_16 hν0 hν1 hA ht' hs).mpr rfl
    have hpow : staticE ν A p t ^ ν = staticE ν A p t ^ (ν - 1) * staticE ν A p t := by
      rw [Real.rpow_sub_one hs.ne']; field_simp
    simp only [staticPrivate, hpow]
    have : staticE ν A p t ^ (ν - 1) = (p + t) / (ν * A) := by
      rw [eq_div_iff (by positivity), ← hfoc]; ring
    rw [this]
    field_simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h2 : HasDerivAt (fun t => (p + t) / ν - p) (1 / ν) τ := by
    have := (((hasDerivAt_id τ).const_add p).div_const ν).sub_const p
    simpa using this
  convert hE.mul h2 using 1
  field_simp
  ring

/-- AKMM, p. 766: "the costs for the private economy of modestly raising the global carbon tax
above zero are negligible": the derivative of the private surplus at `τ = 0` is zero. -/
theorem static_private_deriv_zero (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) :
    HasDerivAt (staticPrivate ν A p) 0 0 := by
  have := static_private_hasDerivAt hν0 hν1 hA (τ := 0) (by linarith)
  simpa using this

/-- AKMM, (25.19), p. 767: a competitive equilibrium under an emission cap `Ē` with permits at
price `λ`: the firm's first-order condition, the cap, and `λ = 0` unless the cap binds. -/
def CapEquilibrium (ν A p Ebar E lam : ℝ) : Prop :=
  0 < E ∧ E ≤ Ebar ∧ 0 ≤ lam ∧ lam * (Ebar - E) = 0 ∧ ν * A * E ^ (ν - 1) = p + lam

/-- AKMM, p. 767: "If the quantity is higher than that of the laissez-faire equilibrium, the
restriction will not bind and `λ` will be zero." -/
theorem static_cap_nonbinding (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p)
    {Ebar E lam : ℝ} (hEbar : staticE ν A p 0 ≤ Ebar) :
    CapEquilibrium ν A p Ebar E lam ↔ E = staticE ν A p 0 ∧ lam = 0 := by
  have hE0 := staticE_pos hν0 hA (p := p) (τ := 0) (by linarith)
  constructor
  · rintro ⟨hE, hle, hlam, hcs, hfoc⟩
    have hlam0 : lam = 0 := by
      by_contra hne
      have hlampos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hne)
      have hEq : E = Ebar := by
        rcases mul_eq_zero.mp hcs with h | h
        · exact absurd h hne
        · linarith
      have hlt : E < staticE ν A p 0 :=
        (static_lt_staticE_iff hν0 hν1 hA (by linarith) hE).mpr (by rw [hfoc]; linarith)
      linarith
    subst hlam0
    exact ⟨(eq_25_16 hν0 hν1 hA (by linarith) hE).mp (by simpa using hfoc), rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨hE0, hEbar, le_rfl, by ring, ?_⟩
    simpa using (eq_25_16 hν0 hν1 hA (τ := 0) (by linarith) hE0).mpr rfl

/-- AKMM, p. 767: "If it is lower than that, the restriction will bind and one reads off `λ`
from the firm's first-order condition": the unique equilibrium is `E = Ē`,
`λ = νAĒ^{ν−1} − p > 0`. -/
theorem static_cap_binding (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p)
    {Ebar E lam : ℝ} (hEbar0 : 0 < Ebar) (hEbar : Ebar < staticE ν A p 0) :
    CapEquilibrium ν A p Ebar E lam ↔ E = Ebar ∧ lam = ν * A * Ebar ^ (ν - 1) - p := by
  have hmp : p < ν * A * Ebar ^ (ν - 1) := by
    have := (static_lt_staticE_iff hν0 hν1 hA (τ := 0) (by linarith) hEbar0).mp hEbar
    linarith
  constructor
  · rintro ⟨hE, hle, hlam, hcs, hfoc⟩
    rcases mul_eq_zero.mp hcs with h | h
    · subst h
      have : staticE ν A p 0 = E :=
        ((eq_25_16 hν0 hν1 hA (by linarith) hE).mp (by simpa using hfoc)).symm
      linarith
    · have hEq : E = Ebar := by linarith
      subst hEq
      exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hEbar0, le_rfl, by linarith, by ring, by ring⟩

/-- AKMM, (25.19), p. 767: with the cap set at the optimum `E*`, the equilibrium is unique, with
permit price `λ = 2γE* = τ`: prices and quantities are equivalent. -/
theorem eq_25_19 (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ Es E lam : ℝ}
    (hγ : 0 < γ) (hEs : 0 < Es) (hfoc : ν * A * Es ^ (ν - 1) = p + 2 * γ * Es) :
    CapEquilibrium ν A p Es E lam ↔ E = Es ∧ lam = 2 * γ * Es := by
  rw [static_cap_binding hν0 hν1 hA hp hEs
    (static_laissez_faire_excess hν0 hν1 hA hp hγ hEs hfoc), hfoc]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- AKMM, p. 767: with the cap at the optimum, an equilibrium exists (so `CapEquilibrium` is not
vacuous). -/
theorem static_cap_exists (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A) (hp : 0 < p) {γ : ℝ}
    (hγ : 0 < γ) : ∃ Es lam, CapEquilibrium ν A p Es Es lam := by
  obtain ⟨Es, hEs, hfoc⟩ := eq_25_18_exists hν0 hν1 hA hp hγ
  exact ⟨Es, 2 * γ * Es, (eq_25_19 hν0 hν1 hA hp hγ hEs hfoc).mpr ⟨rfl, rfl⟩⟩

/-- AKMM, p. 767, corrected: the two-firm planner's objective, including the coal cost `p`,
`AE₁^{ν₁} + AE₂^{ν₂} − p(E₁ + E₂) − γ(E₁ + E₂)²`. -/
noncomputable def staticW2 (ν₁ ν₂ A p γ E₁ E₂ : ℝ) : ℝ :=
  A * E₁ ^ ν₁ + A * E₂ ^ ν₂ - p * (E₁ + E₂) - γ * (E₁ + E₂) ^ 2

/-- AKMM, p. 767: a solution of the two first-order conditions
`ν_iAE_i^{ν_i−1} = p + 2γ(E₁ + E₂)` maximises the planner's objective over `E₁, E₂ ≥ 0`. -/
theorem static_two_optimal {ν₁ ν₂ γ E₁ E₂ F₁ F₂ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1)
    (h₂0 : 0 < ν₂) (h₂1 : ν₂ < 1) (hA : 0 < A) (hγ : 0 ≤ γ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) :
    staticW2 ν₁ ν₂ A p γ F₁ F₂ ≤ staticW2 ν₁ ν₂ A p γ E₁ E₂ := by
  have t₁ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₁0.le h₁1.le hF₁ hE₁
  have t₂ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₂0.le h₂1.le hF₂ hE₂
  unfold staticW2
  nlinarith [mul_le_mul_of_nonneg_left t₁ hA.le, mul_le_mul_of_nonneg_left t₂ hA.le,
    mul_nonneg hγ (sq_nonneg (F₁ + F₂ - E₁ - E₂))]

/-- AKMM, p. 767: "which solves uniquely for `{E₁*, E₂*}`": the optimum is unique. -/
theorem static_two_unique {ν₁ ν₂ γ E₁ E₂ F₁ F₂ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1)
    (h₂0 : 0 < ν₂) (h₂1 : ν₂ < 1) (hA : 0 < A) (hγ : 0 ≤ γ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hne : (F₁, F₂) ≠ (E₁, E₂)) :
    staticW2 ν₁ ν₂ A p γ F₁ F₂ < staticW2 ν₁ ν₂ A p γ E₁ E₂ := by
  have t₁ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₁0.le h₁1.le hF₁ hE₁
  have t₂ := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent h₂0.le h₂1.le hF₂ hE₂
  have hor : F₁ ≠ E₁ ∨ F₂ ≠ E₂ := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hne (by rw [h.1, h.2])
  unfold staticW2
  rcases hor with h | h
  · have s₁ := sust_rpow_lt_tangent h₁0 h₁1 hF₁ hE₁ h
    nlinarith [mul_lt_mul_of_pos_left s₁ hA, mul_le_mul_of_nonneg_left t₂ hA.le,
      mul_nonneg hγ (sq_nonneg (F₁ + F₂ - E₁ - E₂))]
  · have s₂ := sust_rpow_lt_tangent h₂0 h₂1 hF₂ hE₂ h
    nlinarith [mul_le_mul_of_nonneg_left t₁ hA.le, mul_lt_mul_of_pos_left s₂ hA,
      mul_nonneg hγ (sq_nonneg (F₁ + F₂ - E₁ - E₂))]

/-- `E(τ)` is continuous in `τ` on `τ > −p`. -/
theorem staticE_continuousOn (hν0 : 0 < ν) (hA : 0 < A) :
    ContinuousOn (staticE ν A p) (Set.Ioi (-p)) := by
  unfold staticE
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl ?_
  · refine continuousOn_const.div (by fun_prop) fun x hx => ?_
    have : -p < x := hx
    linarith
  · have : -p < x := hx
    have : 0 < p + x := by linarith
    positivity

/-- AKMM, p. 767: the two-firm first-order conditions have a solution: the common marginal cost
`p + 2γX` with `X = E₁(2γX) + E₂(2γX)`, found by the intermediate value theorem. -/
theorem static_two_exists {ν₁ ν₂ γ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1) (h₂0 : 0 < ν₂)
    (h₂1 : ν₂ < 1) (hA : 0 < A) (hp : 0 < p) (hγ : 0 ≤ γ) :
    ∃ E₁ E₂, 0 < E₁ ∧ 0 < E₂ ∧ ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂) ∧
      ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂) := by
  set D : ℝ → ℝ := fun X => staticE ν₁ A p (2 * γ * X) + staticE ν₂ A p (2 * γ * X)
  set g : ℝ → ℝ := fun X => X - D X
  set b := D 0
  have hb : 0 < b := add_pos (staticE_pos h₁0 hA (by simpa using hp))
    (staticE_pos h₂0 hA (by simpa using hp))
  have hcontD : ContinuousOn D (Set.Icc 0 b) := by
    have hmaps : Set.MapsTo (fun X => 2 * γ * X) (Set.Icc 0 b) (Set.Ioi (-p)) := by
      intro X hX
      have : 0 ≤ 2 * γ * X := mul_nonneg (by positivity) hX.1
      change -p < 2 * γ * X
      linarith
    exact ((staticE_continuousOn h₁0 hA).comp (by fun_prop) hmaps).add
      ((staticE_continuousOn h₂0 hA).comp (by fun_prop) hmaps)
  have hcont : ContinuousOn g (Set.Icc 0 b) := continuousOn_id.sub hcontD
  have hg0 : g 0 ≤ 0 := by simp only [g]; linarith
  have hgb : 0 ≤ g b := by
    simp only [g]
    -- `E_i(2γb) ≤ E_i(0)` since the tax is nonnegative
    have hmono : ∀ ν' : ℝ, 0 < ν' → ν' < 1 →
        staticE ν' A p (2 * γ * b) ≤ staticE ν' A p (2 * γ * 0) := by
      intro ν' h0 h1
      rcases (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * γ) hb.le).lt_or_eq with hlt | heq
      · exact (staticE_strictAnti h0 h1 hA (by simpa using hp) (by simpa using hlt)).le
      · rw [← heq]; simp
    have := add_le_add (hmono ν₁ h₁0 h₁1) (hmono ν₂ h₂0 h₂1)
    simp only [D, b] at this ⊢
    linarith
  obtain ⟨X, hX, hgX⟩ := intermediate_value_Icc hb.le hcont ⟨hg0, hgb⟩
  have hXD : X = D X := by simp only [g] at hgX; linarith
  have hτ : 0 < p + 2 * γ * X := by
    have : 0 ≤ 2 * γ * X := mul_nonneg (by positivity) hX.1
    linarith
  have hsum : staticE ν₁ A p (2 * γ * X) + staticE ν₂ A p (2 * γ * X) = X := hXD.symm
  refine ⟨staticE ν₁ A p (2 * γ * X), staticE ν₂ A p (2 * γ * X), staticE_pos h₁0 hA hτ,
    staticE_pos h₂0 hA hτ, ?_, ?_⟩
  · rw [hsum]
    exact (eq_25_16 h₁0 h₁1 hA hτ (staticE_pos h₁0 hA hτ)).mpr rfl
  · rw [hsum]
    exact (eq_25_16 h₂0 h₂1 hA hτ (staticE_pos h₂0 hA hτ)).mpr rfl

/-- AKMM, p. 767: the carbon tax `τ = 2γ(E₁* + E₂*)` implements the two-firm optimum, and both
firms face the same price, so `ν₁AE₁^{ν₁−1} = ν₂AE₂^{ν₂−1}`. -/
theorem static_two_pigou {ν₁ ν₂ γ E₁ E₂ : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1) (h₂0 : 0 < ν₂)
    (h₂1 : ν₂ < 1) (hA : 0 < A) (hp : 0 < p) (hγ : 0 ≤ γ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) :
    staticE ν₁ A p (2 * γ * (E₁ + E₂)) = E₁ ∧ staticE ν₂ A p (2 * γ * (E₁ + E₂)) = E₂ ∧
      ν₁ * A * E₁ ^ (ν₁ - 1) = ν₂ * A * E₂ ^ (ν₂ - 1) := by
  have hτ : 0 < p + 2 * γ * (E₁ + E₂) := by positivity
  exact ⟨((eq_25_16 h₁0 h₁1 hA hτ hE₁).mp hf₁).symm, ((eq_25_16 h₂0 h₂1 hA hτ hE₂).mp hf₂).symm,
    by rw [hf₁, hf₂]⟩

/-- AKMM, p. 767: "a mere restriction for total use not to exceed `E₁* + E₂*` would also work (the
equilibrium price of emission rights would again equal the optimal tax)": with `γ > 0`, the
equilibrium under the aggregate cap is unique, it is the optimum, and `λ = 2γ(E₁* + E₂*)`. -/
theorem static_two_cap {ν₁ ν₂ γ E₁ E₂ F₁ F₂ lam : ℝ} (h₁0 : 0 < ν₁) (h₁1 : ν₁ < 1)
    (h₂0 : 0 < ν₂) (h₂1 : ν₂ < 1) (hA : 0 < A) (hp : 0 < p) (hγ : 0 < γ) (hE₁ : 0 < E₁)
    (hE₂ : 0 < E₂) (hf₁ : ν₁ * A * E₁ ^ (ν₁ - 1) = p + 2 * γ * (E₁ + E₂))
    (hf₂ : ν₂ * A * E₂ ^ (ν₂ - 1) = p + 2 * γ * (E₁ + E₂)) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
    (hcap : F₁ + F₂ ≤ E₁ + E₂) (hlam : 0 ≤ lam) (hcs : lam * (E₁ + E₂ - (F₁ + F₂)) = 0)
    (hg₁ : ν₁ * A * F₁ ^ (ν₁ - 1) = p + lam) (hg₂ : ν₂ * A * F₂ ^ (ν₂ - 1) = p + lam) :
    F₁ = E₁ ∧ F₂ = E₂ ∧ lam = 2 * γ * (E₁ + E₂) := by
  set τ := 2 * γ * (E₁ + E₂)
  have hτpos : 0 < τ := by positivity
  have hpl : 0 < p + lam := by linarith
  have hpτ : 0 < p + τ := by linarith
  have hF₁e := (eq_25_16 h₁0 h₁1 hA hpl hF₁).mp hg₁
  have hF₂e := (eq_25_16 h₂0 h₂1 hA hpl hF₂).mp hg₂
  have hE₁e := (eq_25_16 h₁0 h₁1 hA hpτ hE₁).mp hf₁
  have hE₂e := (eq_25_16 h₂0 h₂1 hA hpτ hE₂).mp hf₂
  -- `λ = τ`: if `λ < τ` both firms buy more than at the optimum, breaking the cap; if `λ > τ`
  -- both buy less, so the cap is slack and `λ = 0 < τ`.
  have hlt : ¬ lam < τ := by
    intro h
    have a₁ := staticE_strictAnti h₁0 h₁1 hA hpl h
    have a₂ := staticE_strictAnti h₂0 h₂1 hA hpl h
    rw [← hF₁e, ← hE₁e] at a₁
    rw [← hF₂e, ← hE₂e] at a₂
    linarith
  have hgt : ¬ τ < lam := by
    intro h
    have a₁ := staticE_strictAnti h₁0 h₁1 hA hpτ h
    have a₂ := staticE_strictAnti h₂0 h₂1 hA hpτ h
    rw [← hF₁e, ← hE₁e] at a₁
    rw [← hF₂e, ← hE₂e] at a₂
    have hslack : 0 < E₁ + E₂ - (F₁ + F₂) := by linarith
    rcases mul_eq_zero.mp hcs with h0 | h0
    · linarith
    · linarith
  have heq : lam = τ := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
  subst heq
  exact ⟨by rw [hF₁e, hE₁e], by rw [hF₂e, hE₂e], rfl⟩

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The market equilibrium of the dynamic integrated assessment model

AKMM, §25.4.2 (pp. 768–770) and Appendix 25.A (p. 909).

* **Energy services** (25.22), (25.26)–(25.27), for any finite set of energy sources with
  weights `λ_i > 0`, prices `p_i > 0` and `ρ < 1`, `ρ ≠ 0`: at the demands (25.27)
  `e_i = E(Pλ_i/p_i)^{1/(1−ρ)}` with the price index (25.26), the aggregate equals `E`
  (`eq_25_27_index`), spending is `PE` (`eq_25_27_cost`), and the first-order conditions hold
  with multiplier `P`: `p_i = P λ_i E^{1−ρ}e_i^{ρ−1}` (`eq_25_27_foc`). `P` is the least cost of a
  unit of energy services: any inputs delivering `E` cost at least `PE` (`eq_25_26_least_cost`).
  This is the many-input version of Obstfeld–Rogoff's two-good duality (`RealExchangeRate`).
* (25.28): the final-good firm's condition `P = νÃE^{ν−1}` iff `E = (νÃ/P)^{1/(1−ν)}`
  (`eq_25_28`).
* **The saving rate** (p. 770). With the rebate on factor income, the return on saving made at
  `t` is `(1 + Γ_{t+1})r_{t+1}`, and the Euler equation is equivalent to
  `(1 − s_{t+1})/(1 − s_t) = αβ/(s_t(1 − ν))` (`eq_25_29_saving`). The book prints
  `(1 + Γ_t)` in (25.29) and `(1 + s_{t+1})/(1 + s_t)` in the next display; both are wrong
  (`eq_25_29_printed_false`, `eq_25_29_saving_printed_false`). The constant rate
  `s̄ = αβ/(1 − ν)` solves it (`saving_const`) and is the only fixed point in `(0, 1)`
  (`saving_fixed_iff`); every path from below `s̄` leaves `(0, 1)` (`saving_below`); every path
  from above stays in `(s̄, 1)` and converges to `1` (`saving_above`, `saving_above_tendsto`) —
  it is not explosive, but it violates the transversality condition:
  `β^t K_{t+1}/C_t = β^t s_t/(1 − s_t) → ∞` (`saving_above_tvc`, needs `α + ν < 1`). So
  `s̄` is the only solution consistent with optimality, which is the book's claim made precise.
* **Appendix 25.A**: combining the demands gives
  `λ_o/λ_κ = (e_o/e_κ)^{1−ρ}(p_o/p_κ)` (`eq_25_A_ratio`; the book writes `p_{1,t}` for `p_{o,t}`),
  and with `λ_o + λ_c + λ_g = 1` the weights are pinned down by the two ratios
  (`eq_25_A_normalize`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

variable {ι : Type*} [Fintype ι]

/-- AKMM, (25.22), p. 768: the energy-services aggregate `E = (Σ_i λ_i e_i^ρ)^{1/ρ}`. -/
noncomputable def energyAgg (lam : ι → ℝ) (ρ : ℝ) (e : ι → ℝ) : ℝ :=
  (∑ i, lam i * e i ^ ρ) ^ (1 / ρ)

/-- The sum `D = Σ_i λ_i^{1/(1−ρ)} p_i^{ρ/(ρ−1)}`. -/
noncomputable def energyD (lam p : ι → ℝ) (ρ : ℝ) : ℝ :=
  ∑ i, lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1))

/-- AKMM, (25.26), p. 769: the price index of energy services `P = D^{(ρ−1)/ρ}`. -/
noncomputable def energyPrice (lam p : ι → ℝ) (ρ : ℝ) : ℝ := energyD lam p ρ ^ ((ρ - 1) / ρ)

/-- AKMM, (25.27), p. 769: the demand `e_i = E(Pλ_i/p_i)^{1/(1−ρ)}`. -/
noncomputable def energyDemand (lam p : ι → ℝ) (ρ E : ℝ) (i : ι) : ℝ :=
  E * (energyPrice lam p ρ * lam i / p i) ^ (1 / (1 - ρ))

omit [Fintype ι] in
/-- The demand of each input is positive. -/
theorem energyDemand_pos [Fintype ι] [Nonempty ι] {lam p : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (hE : 0 < E) (i : ι) :
    0 < energyDemand lam p ρ E i := by
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have hP : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
  have := hl i; have := hp i
  unfold energyDemand; positivity

/-- `(Pλ_i/p_i)^{ρ/(1−ρ)} λ_i = λ_i^{1/(1−ρ)}p_i^{ρ/(ρ−1)} P^{ρ/(1−ρ)}` and
`P^{ρ/(1−ρ)} = D^{−1}`: the key exponent bookkeeping. -/
theorem energy_term {lam p P D ρ : ℝ} (hl : 0 < lam) (hp : 0 < p) (hD : 0 < D) (hρ1 : ρ < 1)
    (hρ0 : ρ ≠ 0) (hP : P = D ^ ((ρ - 1) / ρ)) :
    lam * ((P * lam / p) ^ (1 / (1 - ρ))) ^ ρ =
      lam ^ (1 / (1 - ρ)) * p ^ (ρ / (ρ - 1)) / D := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  have hρ1' : ρ - 1 ≠ 0 := by linarith
  have hPpos : 0 < P := by rw [hP]; positivity
  rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hp.le,
    Real.mul_rpow hPpos.le hl.le, hP, ← Real.rpow_mul hD.le]
  have e1 : (ρ - 1) / ρ * (1 / (1 - ρ) * ρ) = -1 := by field_simp; ring
  have e2 : p ^ (1 / (1 - ρ) * ρ) = (p ^ (ρ / (ρ - 1)))⁻¹ := by
    rw [← Real.rpow_neg hp.le]; congr 1; field_simp; ring
  have e3 : lam * lam ^ (1 / (1 - ρ) * ρ) = lam ^ (1 / (1 - ρ)) := by
    rw [← Real.rpow_one_add' hl.le (by
      rw [show (1 : ℝ) + 1 / (1 - ρ) * ρ = 1 / (1 - ρ) by field_simp; ring]
      exact one_div_ne_zero h1ρ)]
    congr 1; field_simp; ring
  rw [e1, Real.rpow_neg_one, e2]
  have hpp : 0 < p ^ (ρ / (ρ - 1)) := by positivity
  calc lam * (D⁻¹ * lam ^ (1 / (1 - ρ) * ρ) / (p ^ (ρ / (ρ - 1)))⁻¹)
      = (lam * lam ^ (1 / (1 - ρ) * ρ)) * p ^ (ρ / (ρ - 1)) / D := by field_simp
    _ = _ := by rw [e3]

omit [Fintype ι] in
/-- AKMM, (25.26)–(25.27), p. 769: at the demands (25.27) the aggregate (25.22) equals `E`. -/
theorem eq_25_27_index [Fintype ι] [Nonempty ι] {lam p : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (hE : 0 < E) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) :
    energyAgg lam ρ (energyDemand lam p ρ E) = E := by
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have hsum : ∑ i, lam i * energyDemand lam p ρ E i ^ ρ = E ^ ρ := by
    have : ∀ i, lam i * energyDemand lam p ρ E i ^ ρ =
        E ^ ρ * (lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1)) / energyD lam p ρ) := by
      intro i
      have hPpos : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
      have := hl i; have := hp i
      rw [energyDemand, Real.mul_rpow hE.le (by positivity),
        ← energy_term (hl i) (hp i) hD hρ1 hρ0 rfl]
      unfold energyPrice
      ring
    rw [sum_congr rfl fun i _ => this i, ← mul_sum, ← sum_div]
    rw [show ∑ i, lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1)) = energyD lam p ρ from rfl,
      div_self hD.ne', mul_one]
  rw [energyAgg, hsum, ← Real.rpow_mul hE.le, mul_one_div_cancel hρ0, Real.rpow_one]

omit [Fintype ι] in
/-- AKMM, p. 769: spending on the demands (25.27) is `Σ_i p_i e_i = PE`. -/
theorem eq_25_27_cost [Fintype ι] [Nonempty ι] {lam p : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (hE : 0 < E) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) :
    ∑ i, p i * energyDemand lam p ρ E i = energyPrice lam p ρ * E := by
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  have hρ1' : ρ - 1 ≠ 0 := by linarith
  have hPpos : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
  set P := energyPrice lam p ρ with hP
  -- `p_i (Pλ_i/p_i)^{1/(1−ρ)} = P^{1/(1−ρ)} λ_i^{1/(1−ρ)} p_i^{ρ/(ρ−1)}`
  have hterm : ∀ i, p i * energyDemand lam p ρ E i =
      E * P ^ (1 / (1 - ρ)) * (lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1))) := by
    intro i
    have := hl i; have := hp i
    rw [energyDemand, Real.div_rpow (by positivity) (hp i).le,
      Real.mul_rpow hPpos.le (hl i).le]
    have : p i / p i ^ (1 / (1 - ρ)) = p i ^ (ρ / (ρ - 1)) := by
      rw [← Real.rpow_one_sub' (hp i).le (by
        rw [show (1 : ℝ) - 1 / (1 - ρ) = -ρ / (1 - ρ) by field_simp; ring]
        exact div_ne_zero (neg_ne_zero.mpr hρ0) h1ρ)]
      congr 1; field_simp; ring
    rw [← this]
    field_simp
  rw [sum_congr rfl fun i _ => hterm i, ← mul_sum,
    show ∑ i, lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1)) = energyD lam p ρ from rfl]
  -- `P^{1/(1−ρ)} D = P`
  have hPD : P ^ (1 / (1 - ρ)) * energyD lam p ρ = P := by
    have hp1 : P ^ (1 / (1 - ρ)) = energyD lam p ρ ^ (-(1 / ρ)) := by
      rw [hP, energyPrice, ← Real.rpow_mul hD.le]; congr 1; field_simp; ring
    rw [hp1, hP, energyPrice, ← Real.rpow_add_one hD.ne']
    congr 1; field_simp; ring
  rw [mul_assoc, hPD]
  ring

/-- AKMM, p. 769: the first-order conditions of the energy-service provider with multiplier
`P`: `p_i = P · ∂E/∂e_i = P λ_i E^{1−ρ} e_i^{ρ−1}` at the demands (25.27). -/
theorem eq_25_27_foc {lam p ρ E P : ℝ} (hl : 0 < lam) (hp : 0 < p) (hE : 0 < E) (hP : 0 < P)
    (hρ1 : ρ < 1) : P * lam * E ^ (1 - ρ) * (E * (P * lam / p) ^ (1 / (1 - ρ))) ^ (ρ - 1) = p := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  rw [Real.mul_rpow hE.le (by positivity), ← Real.rpow_mul (by positivity)]
  have e1 : 1 / (1 - ρ) * (ρ - 1) = -1 := by field_simp; ring
  rw [e1, Real.rpow_neg_one]
  have : E ^ (1 - ρ) * E ^ (ρ - 1) = 1 := by
    rw [← Real.rpow_add hE]; simp
  rw [show P * lam * E ^ (1 - ρ) * (E ^ (ρ - 1) * (P * lam / p)⁻¹) =
    (E ^ (1 - ρ) * E ^ (ρ - 1)) * (P * lam * (P * lam / p)⁻¹) by ring, this, one_mul, inv_div]
  field_simp

omit [Fintype ι] in
/-- AKMM, p. 769, duality ("cost minimization ... delivers that this price index is a CES
function of the different input costs"): any positive inputs `e` delivering at least `E` units
of energy services cost at least `PE`. The proof uses the weights
`ω_i = λ_i e*_i^ρ/E^ρ` and a tangent line of `x ↦ x^ρ` at the weighted mean of `e_i/e*_i`. -/
theorem eq_25_26_least_cost [Fintype ι] [Nonempty ι] {lam p e : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (he : ∀ i, 0 < e i) (hE : 0 < E) (hρ1 : ρ < 1)
    (hρ0 : ρ ≠ 0) (hdel : E ≤ energyAgg lam ρ e) :
    energyPrice lam p ρ * E ≤ ∑ i, p i * e i := by
  set es := energyDemand lam p ρ E with hes
  have hesp : ∀ i, 0 < es i := energyDemand_pos hl hp hE
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have hPpos : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
  set P := energyPrice lam p ρ with hP
  have hidx := eq_25_27_index hl hp hE hρ1 hρ0
  have hcost := eq_25_27_cost hl hp hE hρ1 hρ0
  -- weights and the weighted mean of the ratios
  set ω : ι → ℝ := fun i => lam i * es i ^ ρ / E ^ ρ with hω
  have hsumes : ∑ i, lam i * es i ^ ρ = E ^ ρ := by
    have h := hidx
    rw [energyAgg] at h
    have hpos : 0 < ∑ i, lam i * es i ^ ρ :=
      Finset.sum_pos (fun i _ => by have := hl i; have := hesp i; positivity)
        Finset.univ_nonempty
    calc ∑ i, lam i * es i ^ ρ = ((∑ i, lam i * es i ^ ρ) ^ (1 / ρ)) ^ ρ := by
          rw [← Real.rpow_mul hpos.le, one_div_mul_cancel hρ0, Real.rpow_one]
      _ = E ^ ρ := by rw [h]
  have hω1 : ∑ i, ω i = 1 := by
    rw [hω, ← sum_div, hsumes, div_self (by positivity)]
  set x : ι → ℝ := fun i => e i / es i with hx
  set mbar := ∑ i, ω i * x i with hmbar1
  -- `ω_i x_i = p_i e_i/(PE)` by the first-order conditions
  have hfoc : ∀ i, ω i * x i = p i * e i / (P * E) := by
    intro i
    have hf := eq_25_27_foc (hl i) (hp i) hE hPpos hρ1
    rw [← show es i = E * (P * lam i / p i) ^ (1 / (1 - ρ)) from rfl] at hf
    have := hesp i
    have hes1 : es i ^ ρ = es i ^ (ρ - 1) * es i := by
      rw [Real.rpow_sub_one this.ne']; field_simp
    have hE1 : E ^ (1 - ρ) * E ^ ρ = E := by
      rw [← Real.rpow_add hE]; simp
    have hlam : lam i * es i ^ (ρ - 1) = p i / (P * E ^ (1 - ρ)) := by
      rw [eq_div_iff (by positivity), ← hf]; ring
    calc ω i * x i = lam i * es i ^ (ρ - 1) * e i / E ^ ρ := by
          simp only [hω, hx]; rw [hes1]; field_simp
      _ = p i / (P * E ^ (1 - ρ)) * e i / E ^ ρ := by rw [hlam]
      _ = p i * e i / (P * (E ^ (1 - ρ) * E ^ ρ)) := by field_simp
      _ = p i * e i / (P * E) := by rw [hE1]
  have hmbar : mbar = (∑ i, p i * e i) / (P * E) := by
    rw [hmbar1, sum_congr rfl fun i _ => hfoc i, ← sum_div]
  have hmpos : 0 < mbar := by
    rw [hmbar]
    exact div_pos (Finset.sum_pos (fun i _ => mul_pos (hp i) (he i)) Finset.univ_nonempty)
      (by positivity)
  -- the aggregate relative to `E`: `Σ ω_i x_i^ρ = (energyAgg e / E)^ρ`
  have hagg : ∑ i, ω i * x i ^ ρ = (∑ i, lam i * e i ^ ρ) / E ^ ρ := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    have := hesp i; have := he i
    simp only [hω, hx]
    rw [Real.div_rpow (he i).le (hesp i).le]
    field_simp
  have hsumpos : 0 < ∑ i, lam i * e i ^ ρ :=
    Finset.sum_pos (fun i _ => by have := hl i; have := he i; positivity) Finset.univ_nonempty
  have hωpos : ∀ i, 0 ≤ ω i := fun i => by
    have := hl i; have := hesp i; simp only [hω]; positivity
  have hEsum : ∑ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) = mbar ^ ρ := by
    have : ∀ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) =
        ω i * mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (ω i * x i) - ρ * mbar ^ (ρ - 1) * mbar * ω i :=
      fun i => by ring
    rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, sum_add_distrib, ← sum_mul,
      ← mul_sum, ← mul_sum, hω1, ← hmbar1]
    ring
  -- compare `energyAgg e` with `mbar · E`
  have key : energyAgg lam ρ e ≤ mbar * E := by
    rcases lt_or_gt_of_ne hρ0 with hneg | hpos
    · -- `ρ < 0`: `x^ρ` convex, `Σω x^ρ ≥ m̄^ρ`, and `y ↦ y^{1/ρ}` is decreasing
      have hj : mbar ^ ρ ≤ ∑ i, ω i * x i ^ ρ := by
        have : ∑ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) ≤
            ∑ i, ω i * x i ^ ρ := by
          refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hωpos i)
          exact ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow hneg.le
            (div_pos (he i) (hesp i)) hmpos
        linarith
      rw [hagg] at hj
      have h2 : ((∑ i, lam i * e i ^ ρ) / E ^ ρ) ^ (1 / ρ) ≤ (mbar ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hj (by
          have : 1 / ρ < 0 := one_div_neg.mpr hneg; linarith)
      rw [← Real.rpow_mul hmpos.le, mul_one_div_cancel hρ0, Real.rpow_one,
        Real.div_rpow hsumpos.le (by positivity), ← Real.rpow_mul hE.le,
        mul_one_div_cancel hρ0, Real.rpow_one, div_le_iff₀ hE] at h2
      exact h2
    · -- `0 < ρ < 1`: `x^ρ` concave, `Σω x^ρ ≤ m̄^ρ`, and `y ↦ y^{1/ρ}` is increasing
      have hj : ∑ i, ω i * x i ^ ρ ≤ mbar ^ ρ := by
        have : ∑ i, ω i * x i ^ ρ ≤
            ∑ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) := by
          refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hωpos i)
          exact ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent hpos.le hρ1.le
            (div_pos (he i) (hesp i)).le hmpos
        linarith
      rw [hagg] at hj
      have h2 : ((∑ i, lam i * e i ^ ρ) / E ^ ρ) ^ (1 / ρ) ≤ (mbar ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow (by positivity) hj (by positivity)
      rw [← Real.rpow_mul hmpos.le, mul_one_div_cancel hρ0, Real.rpow_one,
        Real.div_rpow hsumpos.le (by positivity), ← Real.rpow_mul hE.le,
        mul_one_div_cancel hρ0, Real.rpow_one, div_le_iff₀ hE] at h2
      exact h2
  rw [hmbar] at key
  have : E ≤ (∑ i, p i * e i) / (P * E) * E := le_trans hdel key
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-- AKMM, (25.28), p. 770: the final-good firm's condition `P = νÃE^{ν−1}`, with
`Ã = A L^{1−α−ν}K^α`, holds iff `E = (νÃ/P)^{1/(1−ν)}`. -/
theorem eq_25_28 {ν At P E : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < At) (hP : 0 < P)
    (hE : 0 < E) : P = ν * At * E ^ (ν - 1) ↔ E = (ν * At / P) ^ (1 / (1 - ν)) := by
  have := eq_25_16 hν0 hν1 hA (p := P) (τ := 0) (by simpa using hP) hE
  simp only [add_zero] at this
  rw [eq_comm, this, staticE, add_zero]

/-- AKMM, (25.29) corrected, p. 770: with `C_t = (1 − s_t)(1 + Γ_t)Ŷ_t`,
`K_{t+1} = s_t(1 + Γ_t)Ŷ_t`, `Ŷ = (1 − ν)Y` and `r_{t+1} = αY_{t+1}/K_{t+1}`, the Euler equation
`C_{t+1}/C_t = β(1 + Γ_{t+1})r_{t+1}` is equivalent to
`(1 − s_{t+1})/(1 − s_t) = αβ/(s_t(1 − ν))`. -/
theorem eq_25_29_saving {α β ν s s' Γ Γ' Y Y' : ℝ} (hs : 0 < s) (hs1 : s < 1) (hν : ν < 1)
    (hΓ : 0 < 1 + Γ) (hΓ' : 0 < 1 + Γ') (hY : 0 < Y) (hY' : 0 < Y') :
    (1 - s') * (1 + Γ') * ((1 - ν) * Y') / ((1 - s) * (1 + Γ) * ((1 - ν) * Y)) =
        β * (1 + Γ') * (α * Y' / (s * (1 + Γ) * ((1 - ν) * Y))) ↔
      (1 - s') / (1 - s) = α * β / (s * (1 - ν)) := by
  have h1 : (1 : ℝ) - s ≠ 0 := by linarith
  have h2 : (1 : ℝ) - ν ≠ 0 := by linarith
  set k := (1 + Γ') * Y' / ((1 + Γ) * Y) with hk
  have hk0 : 0 < k := by positivity
  have hL : (1 - s') * (1 + Γ') * ((1 - ν) * Y') / ((1 - s) * (1 + Γ) * ((1 - ν) * Y)) =
      (1 - s') / (1 - s) * k := by
    rw [hk]; field_simp
  have hR : β * (1 + Γ') * (α * Y' / (s * (1 + Γ) * ((1 - ν) * Y))) =
      α * β / (s * (1 - ν)) * k := by
    rw [hk]; field_simp
  rw [hL, hR]
  exact ⟨fun h => mul_right_cancel₀ hk0.ne' h, fun h => by rw [h]⟩

/-- AKMM, p. 770: the display after (25.29), `(1 + s_{t+1})/(1 + s_t) = αβ/(s_t(1 − ν))`, is not
what the Euler equation gives: with `α = β = ν = 1/2`, `s_t = 3/4`, `s_{t+1} = 5/6` the correct
equation holds and the printed one fails. -/
theorem eq_25_29_saving_printed_false :
    (1 - (5 / 6 : ℝ)) / (1 - 3 / 4) = (1 / 2) * (1 / 2) / ((3 / 4) * (1 - 1 / 2)) ∧
      (1 + (5 / 6 : ℝ)) / (1 + 3 / 4) ≠ (1 / 2) * (1 / 2) / ((3 / 4) * (1 - 1 / 2)) := by
  constructor <;> norm_num

/-- AKMM, (25.29) as printed, p. 770: with the rebate rate of date `t`, `(1 + Γ_t)`, in place of
the rebate earned on the return, `(1 + Γ_{t+1})`, the constant saving rate `s̄` does not solve the
Euler equation whenever the rebate changes, `Γ_{t+1} ≠ Γ_t`. -/
theorem eq_25_29_printed_false {α β ν Γ Γ' Y Y' : ℝ} (hab : 0 < α * β) (hν : ν < 1)
    (hs1 : α * β / (1 - ν) < 1) (hΓ : 0 < 1 + Γ) (hΓ' : 0 < 1 + Γ') (hY : 0 < Y) (hY' : 0 < Y')
    (hne : Γ' ≠ Γ) :
    (1 - α * β / (1 - ν)) * (1 + Γ') * ((1 - ν) * Y') /
        ((1 - α * β / (1 - ν)) * (1 + Γ) * ((1 - ν) * Y)) ≠
      β * (1 + Γ) * (α * Y' / (α * β / (1 - ν) * (1 + Γ) * ((1 - ν) * Y))) := by
  have h1ν : 0 < 1 - ν := by linarith
  have hs : 0 < 1 - α * β / (1 - ν) := by linarith
  have hb : β ≠ 0 := right_ne_zero_of_mul hab.ne'
  have ha : α ≠ 0 := left_ne_zero_of_mul hab.ne'
  have hne0 : 1 - ν - α * β ≠ 0 := by
    have := (div_lt_one h1ν).mp hs1; exact (by linarith : (0 : ℝ) < 1 - ν - α * β).ne'
  have hL : (1 - α * β / (1 - ν)) * (1 + Γ') * ((1 - ν) * Y') /
      ((1 - α * β / (1 - ν)) * (1 + Γ) * ((1 - ν) * Y)) = (1 + Γ') / (1 + Γ) * (Y' / Y) := by
    field_simp
  have hR : β * (1 + Γ) * (α * Y' / (α * β / (1 - ν) * (1 + Γ) * ((1 - ν) * Y))) = Y' / Y := by
    field_simp
  rw [hL, hR]
  intro h
  apply hne
  have hYY : 0 < Y' / Y := by positivity
  have : (1 + Γ') / (1 + Γ) = 1 := by
    have := mul_right_cancel₀ hYY.ne' (h.trans (one_mul _).symm)
    exact this
  rw [div_eq_one_iff_eq hΓ.ne'] at this
  linarith

/-- The saving-rate map defined by the corrected equation: `s_{t+1} = 1 − s̄(1 − s_t)/s_t`. -/
noncomputable def savingNext (sbar s : ℝ) : ℝ := 1 - sbar * (1 - s) / s

/-- AKMM, p. 770: the constant `s̄ = αβ/(1 − ν)` solves the difference equation. -/
theorem saving_const {sbar : ℝ} (h0 : 0 < sbar) : savingNext sbar sbar = sbar := by
  unfold savingNext; field_simp; ring

/-- AKMM, p. 770: in `(0, 1)` the only rest point of the difference equation is `s̄` (the other
rest point is `s = 1`, zero consumption). -/
theorem saving_fixed_iff {sbar s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    savingNext sbar s = s ↔ s = sbar := by
  unfold savingNext
  constructor
  · intro h
    have h1 : (s - sbar) * (1 - s) = 0 := by field_simp at h; linarith
    rcases mul_eq_zero.mp h1 with h | h
    · linarith
    · linarith
  · rintro rfl; field_simp; ring

/-- AKMM, p. 770: from above `s̄`, the saving rate stays in `(s̄, 1)` and increases. -/
theorem saving_above {sbar : ℝ} (h0 : 0 < sbar) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : sbar < s 0) (hs01 : s 0 < 1) (t : ℕ) :
    sbar < s t ∧ s t < 1 ∧ s t < s (t + 1) := by
  have hstep : ∀ u, sbar < u → u < 1 →
      sbar < savingNext sbar u ∧ savingNext sbar u < 1 ∧ u < savingNext sbar u := by
    intro u hu hu1
    have hu0 : 0 < u := by linarith
    have hd : savingNext sbar u - u = (u - sbar) * (1 - u) / u := by
      unfold savingNext; field_simp; ring
    have hpos : 0 < (u - sbar) * (1 - u) / u := by
      apply div_pos (mul_pos (by linarith) (by linarith)) hu0
    have hlt : savingNext sbar u < 1 := by
      unfold savingNext
      have : 0 < sbar * (1 - u) / u := div_pos (mul_pos h0 (by linarith)) hu0
      linarith
    exact ⟨by linarith, hlt, by linarith⟩
  have hin : ∀ t, sbar < s t ∧ s t < 1 := by
    intro t
    induction t with
    | zero => exact ⟨hs0, hs01⟩
    | succ n ih =>
      rw [hs n]; exact ⟨(hstep _ ih.1 ih.2).1, (hstep _ ih.1 ih.2).2.1⟩
  refine ⟨(hin t).1, (hin t).2, ?_⟩
  rw [hs t]
  exact (hstep _ (hin t).1 (hin t).2).2.2

/-- AKMM, p. 770: from above `s̄` the saving rate converges to `1` (consumption's share of
income vanishes). -/
theorem saving_above_tendsto {sbar : ℝ} (h0 : 0 < sbar) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : sbar < s 0) (hs01 : s 0 < 1) :
    Tendsto s atTop (𝓝 1) := by
  have hab := saving_above h0 hs hs0 hs01
  have hmono : Monotone s := monotone_nat_of_le_succ fun t => (hab t).2.2.le
  have hbdd : BddAbove (Set.range s) := ⟨1, by rintro _ ⟨t, rfl⟩; exact (hab t).2.1.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t, s t with hL
  have hL0 : s 0 ≤ L := le_ciSup hbdd 0
  have hL1 : L ≤ 1 := ciSup_le fun t => (hab t).2.1.le
  have hLpos : 0 < L := by linarith
  -- `L` is a rest point of the continuous map, so `L = 1`
  have hcont : ContinuousAt (savingNext sbar) L := by
    unfold savingNext
    exact continuousAt_const.sub ((continuousAt_const.mul (continuousAt_const.sub
      continuousAt_id)).div continuousAt_id hLpos.ne')
  have h1 : Tendsto (fun t => s (t + 1)) atTop (𝓝 L) := hlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => s (t + 1)) atTop (𝓝 (savingNext sbar L)) := by
    simp only [hs]; exact hcont.tendsto.comp hlim
  have hfix : savingNext sbar L = L := tendsto_nhds_unique h2 h1
  rcases hL1.lt_or_eq with hlt | heq
  · have := (saving_fixed_iff hLpos hlt).mp hfix
    linarith
  · rw [← heq]; exact hlim

/-- AKMM, p. 770: from below `s̄` the saving rate leaves `(0, 1)` in finite time: the solution
is not an equilibrium. -/
theorem saving_below {sbar : ℝ} (h1 : sbar < 1) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : 0 < s 0) (hs0' : s 0 < sbar) :
    ∃ t, s t ≤ 0 := by
  by_contra hcon
  push Not at hcon
  set δ := (sbar - s 0) * (1 - s 0) with hδ
  have hδ0 : 0 < δ := mul_pos (by linarith) (by linarith)
  -- while positive, the rate falls by at least `δ` each period
  have hdec : ∀ t, s t ≤ s 0 - δ * t := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      have hn0 := hcon n
      have hn1 : s n ≤ s 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hn2 : s n < 1 := by linarith
      rw [hs n]
      have hd : savingNext sbar (s n) - s n = (s n - sbar) * (1 - s n) / s n := by
        unfold savingNext; field_simp; ring
      have hb : (s n - sbar) * (1 - s n) / s n ≤ -δ := by
        rw [div_le_iff₀ hn0]
        have k1 : (s n - sbar) ≤ s 0 - sbar := by linarith
        have k2 : 1 - s 0 ≤ 1 - s n := by linarith
        have k3 : (s n - sbar) * (1 - s n) ≤ (s 0 - sbar) * (1 - s 0) := by nlinarith
        have k4 : -δ * s n ≥ -δ := by nlinarith
        nlinarith
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (s 0 / δ)
  have := hdec n
  have := hcon n
  rw [div_lt_iff₀ hδ0] at hn
  nlinarith

/-- AKMM, p. 770, why the paths from above are ruled out: the transversality term
`β^t u'(C_t)K_{t+1} ∝ β^t K_{t+1}/C_t = β^t s_t/(1 − s_t)` diverges along every path from above
`s̄`. With `s̄ = αβ/(1 − ν)` the condition `s̄ < β` used here is `α + ν < 1`. -/
theorem saving_above_tvc {sbar β : ℝ} (h0 : 0 < sbar) (hβ : sbar < β) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : sbar < s 0) (hs01 : s 0 < 1) :
    Tendsto (fun t => β ^ t * (s t / (1 - s t))) atTop atTop := by
  have hab := saving_above h0 hs hs0 hs01
  have hlim := saving_above_tendsto h0 hs hs0 hs01
  -- pick `σ ∈ (s̄/β, 1)`, so that `q = s̄/σ < β`
  set σ := (sbar / β + 1) / 2 with hσ
  have hβ0 : 0 < β := by linarith
  have hsb : sbar / β < 1 := (div_lt_one hβ0).mpr hβ
  have hσ1 : σ < 1 := by rw [hσ]; linarith
  have hσ0 : sbar / β < σ := by rw [hσ]; linarith
  have hσpos : 0 < σ := by have : 0 < sbar / β := div_pos h0 hβ0; linarith
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp (hlim.eventually (Ici_mem_nhds hσ1))
  · -- for `t ≥ T0`: `1 − s_{t+1} ≤ (s̄/σ)(1 − s_t)`
    set q := sbar / σ with hq
    have hq0 : 0 < q := div_pos h0 hσpos
    have hqβ : q < β := by
      rw [hq, div_lt_iff₀ hσpos]
      have := (div_lt_iff₀ hβ0).mp hσ0
      linarith
    have hdec : ∀ n, 1 - s (T0 + n) ≤ q ^ n * (1 - s T0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hge : σ ≤ s (T0 + n) := (hT0 (T0 + n) (by omega) : σ ≤ s (T0 + n))
        have hpos : 0 < s (T0 + n) := by linarith
        rw [← add_assoc, hs, savingNext, pow_succ]
        have h1s : 0 ≤ 1 - s (T0 + n) := by linarith [(hab (T0 + n)).2.1]
        have : sbar * (1 - s (T0 + n)) / s (T0 + n) ≤ q * (1 - s (T0 + n)) := by
          rw [hq, div_le_iff₀ hpos]
          have key : sbar * (1 - s (T0 + n)) * σ ≤ sbar * (1 - s (T0 + n)) * s (T0 + n) :=
            mul_le_mul_of_nonneg_left hge (mul_nonneg h0.le h1s)
          calc sbar * (1 - s (T0 + n)) = sbar * (1 - s (T0 + n)) * σ / σ := by field_simp
            _ ≤ sbar * (1 - s (T0 + n)) * s (T0 + n) / σ := by gcongr
            _ = sbar / σ * (1 - s (T0 + n)) * s (T0 + n) := by ring
        have hq0' : 0 ≤ q := hq0.le
        nlinarith
    -- hence `β^t s_t/(1 − s_t) ≥ c (β/q)^{t−T0}` with `β/q > 1`
    have hc : 0 < 1 - s T0 := by linarith [(hab T0).2.1]
    have hgrow : Tendsto (fun n : ℕ => (β / q) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hq0).mpr hqβ)
    have hlow : ∀ n, β ^ T0 * σ / (1 - s T0) * (β / q) ^ n ≤
        β ^ (T0 + n) * (s (T0 + n) / (1 - s (T0 + n))) := by
      intro n
      have h1 := hdec n
      have hpos1 : 0 < 1 - s (T0 + n) := by linarith [(hab (T0 + n)).2.1]
      have hge : σ ≤ s (T0 + n) := (hT0 (T0 + n) (by omega) : σ ≤ s (T0 + n))
      have hqn : 0 < q ^ n := pow_pos hq0 n
      have hs0' : 0 ≤ s (T0 + n) := by linarith
      have hfrac : σ / (q ^ n * (1 - s T0)) ≤ s (T0 + n) / (1 - s (T0 + n)) :=
        div_le_div₀ hs0' hge hpos1 h1
      have hb0 : 0 ≤ β ^ T0 * β ^ n := by positivity
      calc β ^ T0 * σ / (1 - s T0) * (β / q) ^ n
          = β ^ T0 * β ^ n * (σ / (q ^ n * (1 - s T0))) := by rw [div_pow]; field_simp
        _ ≤ β ^ T0 * β ^ n * (s (T0 + n) / (1 - s (T0 + n))) :=
            mul_le_mul_of_nonneg_left hfrac hb0
        _ = β ^ (T0 + n) * (s (T0 + n) / (1 - s (T0 + n))) := by rw [pow_add]
    have hk : 0 < β ^ T0 * σ / (1 - s T0) := by positivity
    have hshift : Tendsto (fun n => β ^ (T0 + n) * (s (T0 + n) / (1 - s (T0 + n)))) atTop atTop :=
      tendsto_atTop_mono hlow (hgrow.const_mul_atTop hk)
    have h2 : Tendsto (fun n => (fun t => β ^ t * (s t / (1 - s t))) (n + T0)) atTop atTop :=
      hshift.congr fun n => by simp only [add_comm T0 n]
    exact (tendsto_add_atTop_iff_nat T0).mp h2

/-- AKMM, Appendix 25.A, p. 909: combining the demands (25.27) for oil and source `κ`,
`λ_o/λ_κ = (e_o/e_κ)^{1−ρ}(p_o/p_κ)` (the book writes `p_{1,t}` for `p_{o,t}`). -/
theorem eq_25_A_ratio {lo lk po pk E P ρ : ℝ} (hlo : 0 < lo) (hlk : 0 < lk) (hpo : 0 < po)
    (hpk : 0 < pk) (hE : 0 < E) (hP : 0 < P) (hρ1 : ρ < 1) :
    lo / lk = ((E * (P * lo / po) ^ (1 / (1 - ρ))) / (E * (P * lk / pk) ^ (1 / (1 - ρ)))) ^
      (1 - ρ) * (po / pk) := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  rw [mul_div_mul_left _ _ hE.ne', Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    one_div_mul_cancel h1ρ, Real.rpow_one, Real.rpow_one]
  field_simp

/-- AKMM, Appendix 25.A, p. 909: with `λ_o + λ_c + λ_g = 1` and the ratios `λ_o/λ_c = r_c`,
`λ_o/λ_g = r_g`, the weights are `λ_o = 1/(1 + 1/r_c + 1/r_g)`, `λ_c = λ_o/r_c`,
`λ_g = λ_o/r_g`. -/
theorem eq_25_A_normalize {lo lc lg rc rg : ℝ} (hrc : 0 < rc) (hrg : 0 < rg) (hlc : 0 < lc)
    (hlg : 0 < lg) (hsum : lo + lc + lg = 1) (hc : lo / lc = rc) (hg : lo / lg = rg) :
    lo = 1 / (1 + 1 / rc + 1 / rg) ∧ lc = lo / rc ∧ lg = lo / rg := by
  have hlo : lo ≠ 0 := by rintro rfl; simp at hc; linarith
  have hc' : lc = lo / rc := by rw [← hc]; field_simp
  have hg' : lg = lo / rg := by rw [← hg]; field_simp
  refine ⟨?_, hc', hg'⟩
  rw [hc', hg'] at hsum
  have : lo * (1 + 1 / rc + 1 / rg) = 1 := by linear_combination hsum
  have hpos : 0 < 1 + 1 / rc + 1 / rg := by positivity
  rw [eq_div_iff hpos.ne']
  exact this

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cake eating, Hotelling rents and the oil owner

AKMM, §25.5.2 (pp. 775–778) and the oil producer of §25.4.2 (p. 769). Throughout
`0 < β < 1` and the resource stock is `R₀ > 0`.

* **The planner** (p. 775–776): `c_t = (1 − β)β^t R₀` (`cakePath`) exhausts the cake
  (`cake_hasSum`), follows `c_t = (1 − β)R_t`, `R_{t+1} = R_t − c_t` (`cake_policy`), and has
  finite utility `log((1 − β)R₀)/(1 − β) + β log β/(1 − β)²` (`cake_utility_hasSum`: "utility is
  bounded" in this sense, although `log c_t → −∞`). It is optimal: for every positive plan
  with `Σ_{t<T} c_t ≤ R₀`, `Σ_{t<T} β^t log c_t ≤ Σ_{t<T} β^t log c*_t + β^T/(1 − β)`
  (`cake_overtake`), so its utility is the largest (`cake_optimal`) and it is the unique
  optimum (`cake_unique`). Consumption falls over time (`cake_decreasing`). The same plan is the
  optimal plan of Stokey–Lucas Exercise 5.2b (`cake_slp`, reusing
  `DeterministicApplications`).
* **The market** (pp. 776–777): if the owner's sales maximise income, a date with positive
  sales has the highest Arrow–Debreu price, so with sales at all dates the price is constant
  (`hotelling_price_max`, `hotelling_price_const`). At a constant price `p̂ > 0` selling `c*`
  maximises income and buying `c*` maximises utility within the budget, so the planner's
  allocation is a competitive equilibrium (`cake_market_equilibrium`), with
  `p̂_{t+1}/p̂_t = βc_t/c_{t+1}` (`cake_market_foc`). The **Hotelling rent** is positive: no
  consumer optimum exists if some price is `≤ 0` (`hotelling_rent_pos`). With a second good the
  spot price satisfies `p^o_t = (p_{t+1}/p_t)p^o_{t+1}`, i.e. it grows at the real interest
  rate (`hotelling_rule`).
* **Extraction costs** (p. 778): indifference between extracting at `t` and `t + 1`
  (`hotelling_cost_indifference`) gives
  `p_{t+1}/p_t = 1 + r_t + (mc_{t+1} − (1 + r_t)mc_t)/p_t` (`hotelling_cost_rule`).
* **The oil owner** (p. 769): with log utility and any positive prices, the owner extracts
  `e_t = (1 − β)R_t` with `R_{t+1} = βR_t` (`oil_owner_overtake`, `oil_owner_optimal`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- If the partial sums of `f` are eventually below those of `g` up to a vanishing error, the
sums compare. -/
theorem sust_hasSum_le_of_partial {f g : ℕ → ℝ} {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ T in atTop, ∑ t ∈ range T, f t ≤ ∑ t ∈ range T, g t + ε T) : a ≤ b := by
  have := hg.tendsto_sum_nat.add hε
  rw [add_zero] at this
  exact le_of_tendsto_of_tendsto hf.tendsto_sum_nat this h

/-- AKMM, p. 776: the planner's cake path `c_t = (1 − β)β^t R₀`. -/
noncomputable def cakePath (β R₀ : ℝ) (t : ℕ) : ℝ := (1 - β) * β ^ t * R₀

variable {β R₀ : ℝ}

/-- `Σ_{t<T} (1 − β)β^t R₀ = R₀ − β^T R₀`. -/
theorem cake_partial_sum (β R₀ : ℝ) (T : ℕ) :
    ∑ t ∈ range T, cakePath β R₀ t = R₀ - β ^ T * R₀ := by
  induction T with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, cakePath, pow_succ]; ring

/-- AKMM, p. 776: the planner's path exhausts the cake, `Σ_t c_t = R₀`. -/
theorem cake_hasSum (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R₀ : ℝ) : HasSum (cakePath β R₀) R₀ := by
  have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left ((1 - β) * R₀)
  convert this using 1
  · funext t; simp only [cakePath]; ring
  · field_simp [(by linarith : (0 : ℝ) < 1 - β).ne']

/-- AKMM, p. 776: "the solution to the planning problem is `c_t = (1 − β)R_t`, where
`R_{t+1} = R_t − c_t`, so that `c_t = (1 − β)β^t R₀`": with `R_t = β^t R₀`. -/
theorem cake_policy (β R₀ : ℝ) (t : ℕ) :
    cakePath β R₀ t = (1 - β) * (β ^ t * R₀) ∧
      β ^ (t + 1) * R₀ = β ^ t * R₀ - cakePath β R₀ t := by
  constructor <;> simp only [cakePath, pow_succ] <;> ring

/-- AKMM, p. 776: "consumption is higher in the beginning than later, all because of
discounting". -/
theorem cake_decreasing (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) :
    StrictAnti (cakePath β R₀) := by
  refine strictAnti_nat_of_succ_lt fun t => ?_
  simp only [cakePath, pow_succ]
  have : 0 < (1 - β) * β ^ t * R₀ := by
    have : 0 < 1 - β := by linarith
    positivity
  nlinarith

/-- AKMM, p. 776: the planner's utility is finite: `Σ_t β^t log c_t` converges to
`log((1 − β)R₀)/(1 − β) + β log β/(1 − β)²`. -/
theorem cake_utility_hasSum (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) :
    HasSum (fun t => β ^ t * Real.log (cakePath β R₀ t))
      (Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2) := by
  have h1β : 0 < 1 - β := by linarith
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have h1 := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left (Real.log ((1 - β) * R₀))
  have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_right (Real.log β)
  convert h1.add h2 using 1
  · funext t
    have : cakePath β R₀ t = ((1 - β) * R₀) * β ^ t := by simp only [cakePath]; ring
    rw [this, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  · field_simp

/-- AKMM, pp. 775–776: the planner's path is optimal. For every plan with `c_t > 0` and
`Σ_{t<T} c_t ≤ R₀` for all `T`,
`Σ_{t<T} β^t log c_t ≤ Σ_{t<T} β^t log c*_t + β^T/(1 − β)`. The bound comes from
`log c ≤ log c* + (c − c*)/c*` and `β^t/c*_t = 1/((1 − β)R₀)`. -/
theorem cake_overtake (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {c : ℕ → ℝ}
    (hc : ∀ t, 0 < c t) (hsum : ∀ T, ∑ t ∈ range T, c t ≤ R₀) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (c t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) + β ^ T / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith
  have hK : 0 < (1 - β) * R₀ := by positivity
  have hstar : ∀ t, 0 < cakePath β R₀ t := fun t => by unfold cakePath; positivity
  have key : ∀ t ∈ range T, β ^ t * Real.log (c t) ≤
      β ^ t * Real.log (cakePath β R₀ t) + (c t - cakePath β R₀ t) / ((1 - β) * R₀) := by
    intro t _
    have h := sust_log_le_tangent (hc t) (hstar t)
    have hb : 0 < β ^ t := by positivity
    have : β ^ t * ((c t - cakePath β R₀ t) / cakePath β R₀ t) =
        (c t - cakePath β R₀ t) / ((1 - β) * R₀) := by
      simp only [cakePath]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left h hb.le]
  calc ∑ t ∈ range T, β ^ t * Real.log (c t)
      ≤ ∑ t ∈ range T, (β ^ t * Real.log (cakePath β R₀ t) +
          (c t - cakePath β R₀ t) / ((1 - β) * R₀)) := sum_le_sum key
    _ = ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
          (∑ t ∈ range T, c t - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) := by
        rw [sum_add_distrib, ← sum_div, sum_sub_distrib, cake_partial_sum]
    _ ≤ ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
          (R₀ - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) := by
        gcongr
        exact hsum T
    _ = _ := by field_simp; ring

/-- AKMM, pp. 775–776: the planner's path maximises lifetime utility among positive plans that
use at most the cake (`Σ_{t<T} c_t ≤ R₀`) and have summable utility. -/
theorem cake_optimal (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {c : ℕ → ℝ} {U : ℝ}
    (hc : ∀ t, 0 < c t) (hsum : ∀ T, ∑ t ∈ range T, c t ≤ R₀)
    (hU : HasSum (fun t => β ^ t * Real.log (c t)) U) :
    U ≤ Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 := by
  have h1β : 0 < 1 - β := by linarith
  refine sust_hasSum_le_of_partial hU (cake_utility_hasSum hβ0 hβ1 hR)
    (ε := fun T => β ^ T / (1 - β)) ?_
    (Eventually.of_forall fun T => cake_overtake hβ0 hβ1 hR hc hsum T)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)

/-- AKMM, p. 776: the planner's path is the unique optimum: any other positive plan within the
cake has strictly lower utility. -/
theorem cake_unique (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {c : ℕ → ℝ} {U : ℝ}
    (hc : ∀ t, 0 < c t) (hsum : ∀ T, ∑ t ∈ range T, c t ≤ R₀)
    (hU : HasSum (fun t => β ^ t * Real.log (c t)) U) (hne : c ≠ cakePath β R₀) :
    U < Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 := by
  have h1β : 0 < 1 - β := by linarith
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hne
  have hstar : 0 < cakePath β R₀ s := by unfold cakePath; positivity
  set δ := β ^ s * (Real.log (cakePath β R₀ s) + (c s - cakePath β R₀ s) / cakePath β R₀ s -
    Real.log (c s)) with hδ
  have hδ0 : 0 < δ := by
    have := sust_log_lt_tangent (hc s) hstar hs
    have : 0 < β ^ s := by positivity
    rw [hδ]; nlinarith
  -- the tangent bound loses at least `δ` at date `s`
  have hbound : ∀ T, s < T → ∑ t ∈ range T, β ^ t * Real.log (c t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) + β ^ T / (1 - β) - δ := by
    intro T hT
    have hK : 0 < (1 - β) * R₀ := by positivity
    set g : ℕ → ℝ := fun t => β ^ t * Real.log (cakePath β R₀ t) +
      (c t - cakePath β R₀ t) / ((1 - β) * R₀) with hg
    have key : ∀ t, β ^ t * Real.log (c t) ≤ g t := by
      intro t
      have hst : 0 < cakePath β R₀ t := by unfold cakePath; positivity
      have h := sust_log_le_tangent (hc t) hst
      have hb : 0 < β ^ t := by positivity
      have : β ^ t * ((c t - cakePath β R₀ t) / cakePath β R₀ t) =
          (c t - cakePath β R₀ t) / ((1 - β) * R₀) := by
        simp only [cakePath]; field_simp
      simp only [hg]
      nlinarith [mul_le_mul_of_nonneg_left h hb.le]
    have keys : β ^ s * Real.log (c s) = g s - δ := by
      have : β ^ s * ((c s - cakePath β R₀ s) / cakePath β R₀ s) =
          (c s - cakePath β R₀ s) / ((1 - β) * R₀) := by
        simp only [cakePath]; field_simp
      simp only [hg, hδ]; linarith
    have hsT : s ∈ range T := mem_range.mpr hT
    calc ∑ t ∈ range T, β ^ t * Real.log (c t)
        = β ^ s * Real.log (c s) + ∑ t ∈ (range T).erase s, β ^ t * Real.log (c t) :=
          (add_sum_erase _ _ hsT).symm
      _ ≤ (g s - δ) + ∑ t ∈ (range T).erase s, g t := by
          rw [keys]; gcongr with t; exact key t
      _ = ∑ t ∈ range T, g t - δ := by rw [← add_sum_erase _ _ hsT]; ring
      _ = ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
            (∑ t ∈ range T, c t - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) - δ := by
          simp only [hg]
          rw [sum_add_distrib, ← sum_div, sum_sub_distrib, cake_partial_sum]
      _ ≤ ∑ t ∈ range T, β ^ t * Real.log (cakePath β R₀ t) +
            (R₀ - (R₀ - β ^ T * R₀)) / ((1 - β) * R₀) - δ := by
          gcongr
          exact hsum T
      _ = _ := by field_simp; ring
  have hle : U ≤ Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 - δ := by
    have hU' : HasSum (fun t => β ^ t * Real.log (cakePath β R₀ t) - δ * (if t = 0 then 1 else 0))
        (Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 - δ * 1) :=
      (cake_utility_hasSum hβ0 hβ1 hR).sub ((hasSum_ite_eq 0 (1 : ℝ)).mul_left δ)
    rw [mul_one] at hU'
    refine sust_hasSum_le_of_partial hU hU' (ε := fun T => β ^ T / (1 - β)) ?_ ?_
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)
    · filter_upwards [eventually_gt_atTop s] with T hT
      have h0 : 0 ∈ range T := mem_range.mpr (by omega)
      rw [sum_sub_distrib, ← mul_sum, sum_ite_eq' (range T) 0]
      simp only [h0, ↓reduceIte]
      linarith [hbound T hT]
  linarith

/-- AKMM, p. 776, reusing Stokey–Lucas Exercise 5.2b (`DeterministicApplications`): the SLP
cake-eating policy `g(x) = βx` leaves `β^t R₀` after `t` periods, so its consumption is the
book's path, and SLP prove it optimal in their formulation. -/
theorem cake_slp (hβ0 : 0 < β) (hβ1 : β < 1)
    (k₀ : StokeyLucasPrescott.DeterministicApplications.PosR) (t : ℕ) :
    ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[t] k₀).1 =
        β ^ t * k₀.1 ∧
      ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[t] k₀).1 -
        ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[t + 1]
          k₀).1 = cakePath β k₀.1 t ∧
      StokeyLucasPrescott.DeterministicApplications.total
          (StokeyLucasPrescott.DeterministicApplications.logF 1) β
          (fun s => (StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos hβ0)^[s]
            k₀) =
        StokeyLucasPrescott.DeterministicApplications.vstar
          (StokeyLucasPrescott.DeterministicApplications.logΓ 1)
          (StokeyLucasPrescott.DeterministicApplications.logF 1) β k₀ := by
  have hit : ∀ s, ((StokeyLucasPrescott.DeterministicApplications.logPolicy 1 β one_pos
      hβ0)^[s] k₀).1 = β ^ s * k₀.1 := by
    intro s
    induction s with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', StokeyLucasPrescott.DeterministicApplications.cake_policy
        hβ0, ih, pow_succ]
      ring
  refine ⟨hit t, ?_, StokeyLucasPrescott.DeterministicApplications.ex_5_2b_policy hβ0 hβ1 k₀⟩
  rw [hit, hit, cakePath, pow_succ]
  ring

/-- AKMM, p. 776: if the owner's sales `e ≥ 0` (with `Σ e_t = R`) maximise income
`Σ p̂_t e_t` among such sales plans, then a date with positive sales carries the highest
Arrow–Debreu price. -/
theorem hotelling_price_max {p e : ℕ → ℝ} {R I : ℝ} (he : ∀ t, 0 ≤ e t) (hR : HasSum e R)
    (hI : HasSum (fun t => p t * e t) I)
    (hmax : ∀ e' : ℕ → ℝ, (∀ t, 0 ≤ e' t) → HasSum e' R → ∀ I',
      HasSum (fun t => p t * e' t) I' → I' ≤ I) {t : ℕ} (ht : 0 < e t) (s : ℕ) :
    p s ≤ p t := by
  set e' : ℕ → ℝ := fun u => e u + (if u = s then e t else 0) - (if u = t then e t else 0)
  have he' : ∀ u, 0 ≤ e' u := by
    intro u
    simp only [e']
    by_cases hut : u = t
    · subst hut; split_ifs <;> linarith
    · have := he u
      simp only [hut, ↓reduceIte, sub_zero]
      split_ifs <;> linarith
  have hR' : HasSum e' R := by
    have := (hR.add (hasSum_ite_eq s (e t))).sub (hasSum_ite_eq t (e t))
    simpa using this
  have hI' : HasSum (fun u => p u * e' u) (I + p s * e t - p t * e t) := by
    have h1 := (hasSum_ite_eq s (e t)).mul_left (p s)
    have h2 := (hasSum_ite_eq t (e t)).mul_left (p t)
    convert (hI.add h1).sub h2 using 1
    funext u
    simp only [e']
    split_ifs with h1 h2 <;> (try simp_all)
    ring
  have := hmax e' he' hR' _ hI'
  nlinarith

/-- AKMM, p. 776: "the price has to be the same; otherwise the consumer would sell all of the
resource at the date with the highest price": with positive sales at every date the
Arrow–Debreu price is constant. -/
theorem hotelling_price_const {p e : ℕ → ℝ} {R I : ℝ} (he : ∀ t, 0 < e t) (hR : HasSum e R)
    (hI : HasSum (fun t => p t * e t) I)
    (hmax : ∀ e' : ℕ → ℝ, (∀ t, 0 ≤ e' t) → HasSum e' R → ∀ I',
      HasSum (fun t => p t * e' t) I' → I' ≤ I) (s t : ℕ) : p s = p t :=
  le_antisymm (hotelling_price_max (fun u => (he u).le) hR hI hmax (he t) s)
    (hotelling_price_max (fun u => (he u).le) hR hI hmax (he s) t)

/-- AKMM, p. 776: the consumer's first-order conditions at the planner's path:
`β^t/c*_t = 1/((1 − β)R₀)` at every date, so with a constant price the multiplier is constant
and `p̂_{t+1}/p̂_t = βc_t/c_{t+1}` holds with `p̂_{t+1} = p̂_t`. -/
theorem cake_market_foc (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) (t : ℕ) :
    β ^ t / cakePath β R₀ t = 1 / ((1 - β) * R₀) ∧
      β * cakePath β R₀ t / cakePath β R₀ (t + 1) = 1 := by
  have h1β : 0 < 1 - β := by linarith
  constructor
  · simp only [cakePath]; field_simp
  · simp only [cakePath, pow_succ]; field_simp

/-- AKMM, pp. 776: the competitive equilibrium of the cake economy. At a constant Arrow–Debreu
price `p̂ > 0`: (i) every sales plan exhausting the cake earns the same income `p̂R₀`, so selling
the planner's path maximises income; (ii) a consumer with that income who buys any positive plan
within the budget gets at most the planner's utility; (iii) markets clear with `c = e = c*`. So
markets deliver the planner's allocation. -/
theorem cake_market_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {ph : ℝ}
    (hp : 0 < ph) :
    HasSum (fun t => ph * cakePath β R₀ t) (ph * R₀) ∧
      (∀ e' : ℕ → ℝ, HasSum e' R₀ → HasSum (fun t => ph * e' t) (ph * R₀)) ∧
      ∀ (c : ℕ → ℝ) (U : ℝ), (∀ t, 0 < c t) → (∀ T, ∑ t ∈ range T, ph * c t ≤ ph * R₀) →
        HasSum (fun t => β ^ t * Real.log (c t)) U →
        U ≤ Real.log ((1 - β) * R₀) / (1 - β) + β * Real.log β / (1 - β) ^ 2 := by
  refine ⟨(cake_hasSum hβ0.le hβ1 R₀).mul_left ph, fun e' he' => he'.mul_left ph,
    fun c U hc hbud hU => cake_optimal hβ0 hβ1 hR hc (fun T => ?_) hU⟩
  have := hbud T
  rw [← mul_sum] at this
  exact le_of_mul_le_mul_left this hp

/-- AKMM, p. 777: "`p^o_t > 0` for all `t`": the Hotelling rent is positive. If the consumer's
problem — maximise `Σβ^t log c_t` over positive plans with `Σ p̂_t c_t ≤ I` — has a solution
`c`, then every price is positive (otherwise consuming one more unit at a date with
`p̂_t ≤ 0` is affordable and strictly better). -/
theorem hotelling_rent_pos (hβ0 : 0 < β) {p c : ℕ → ℝ} {I B U : ℝ} (hc : ∀ t, 0 < c t)
    (hB : HasSum (fun t => p t * c t) B) (hBI : B ≤ I)
    (hU : HasSum (fun t => β ^ t * Real.log (c t)) U)
    (hopt : ∀ c' : ℕ → ℝ, (∀ t, 0 < c' t) → ∀ B' U', HasSum (fun t => p t * c' t) B' →
      B' ≤ I → HasSum (fun t => β ^ t * Real.log (c' t)) U' → U' ≤ U) (t : ℕ) :
    0 < p t := by
  by_contra hpt
  rw [not_lt] at hpt
  set c' : ℕ → ℝ := fun u => c u + if u = t then 1 else 0
  have hc' : ∀ u, 0 < c' u := fun u => by
    simp only [c']; split_ifs <;> linarith [hc u]
  have hB' : HasSum (fun u => p u * c' u) (B + p t * 1) := by
    convert hB.add ((hasSum_ite_eq t (1 : ℝ)).mul_left (p t)) using 1
    funext u; simp only [c']; split_ifs with h
    · subst h; ring
    · simp
  set gain := β ^ t * (Real.log (c t + 1) - Real.log (c t))
  have hgain : 0 < gain := by
    have : Real.log (c t) < Real.log (c t + 1) :=
      Real.log_lt_log (hc t) (by linarith)
    have : 0 < β ^ t := by positivity
    simp only [gain]; nlinarith
  have hU' : HasSum (fun u => β ^ u * Real.log (c' u)) (U + gain) := by
    convert hU.add ((hasSum_ite_eq t gain)) using 1
    funext u; simp only [c', gain]; split_ifs with h
    · subst h; ring
    · simp
  have := hopt c' hc' _ _ hB' (by linarith) hU'
  linarith

/-- AKMM, p. 776, the Hotelling rule: with Arrow–Debreu prices `p̂_t = p^o_t p_t` constant
(`p_t` the price of a second good), the spot price satisfies `p^o_t = (p_{t+1}/p_t)p^o_{t+1}`,
i.e. `p^o_{t+1} = (1 + r_t)p^o_t` with the gross real rate `1 + r_t = p_t/p_{t+1}`. -/
theorem hotelling_rule {po p : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hconst : ∀ t, po t * p t = po (t + 1) * p (t + 1)) (t : ℕ) :
    po t = p (t + 1) / p t * po (t + 1) ∧ po (t + 1) = p t / p (t + 1) * po t := by
  have h0 := (hp t).ne'
  have h1 := (hp (t + 1)).ne'
  constructor
  · field_simp; linarith [hconst t]
  · field_simp; linarith [hconst t]

/-- AKMM, p. 778: with extraction costs, the owner is indifferent between extracting at `t` and
`t + 1` exactly when `p_t − mc_t = (p_{t+1} − mc_{t+1})/(1 + r_t)`: if the split `(x, y)` of a
given total `x + y = Q` between the two dates maximises discounted profit, with both parts
positive, the condition holds. -/
theorem hotelling_cost_indifference {pt mct pt1 mct1 r x y : ℝ} (hr : 0 < 1 + r) (hx : 0 < x)
    (hy : 0 < y)
    (hmax : ∀ x' y', 0 ≤ x' → 0 ≤ y' → x' + y' = x + y →
      (pt - mct) * x' + (pt1 - mct1) * y' / (1 + r) ≤
        (pt - mct) * x + (pt1 - mct1) * y / (1 + r)) :
    pt - mct = (pt1 - mct1) / (1 + r) := by
  have h1 := hmax 0 (x + y) le_rfl (by linarith) (by ring)
  have h2 := hmax (x + y) 0 (by linarith) le_rfl (by ring)
  have e1 : (pt1 - mct1) * (x + y) / (1 + r) = (pt1 - mct1) * y / (1 + r) +
      (pt1 - mct1) / (1 + r) * x := by field_simp; ring
  have e2 : (pt1 - mct1) * y / (1 + r) = (pt1 - mct1) / (1 + r) * y := by ring
  rw [e1] at h1
  rw [e2] at h1 h2
  simp only [zero_add, mul_zero, zero_div, add_zero] at h1 h2
  have k1 : ((pt1 - mct1) / (1 + r) - (pt - mct)) * x ≤ 0 := by nlinarith
  have k2 : ((pt - mct) - (pt1 - mct1) / (1 + r)) * y ≤ 0 := by nlinarith
  have := nonpos_of_mul_nonpos_left k1 hx
  have := nonpos_of_mul_nonpos_left k2 hy
  linarith

/-- AKMM, p. 778: the indifference condition implies
`p_{t+1}/p_t = 1 + r_t + (mc_{t+1} − (1 + r_t)mc_t)/p_t`. -/
theorem hotelling_cost_rule {pt mct pt1 mct1 r : ℝ} (hr : 0 < 1 + r) (hp : pt ≠ 0)
    (h : pt - mct = (pt1 - mct1) / (1 + r)) :
    pt1 / pt = 1 + r + (mct1 - (1 + r) * mct) / pt := by
  have : pt1 = (1 + r) * (pt - mct) + mct1 := by
    rw [h]; field_simp; ring
  rw [this]
  field_simp
  ring

/-- AKMM, p. 769: the oil owner with log utility and income `p_t e_t` from any positive prices:
the extraction path `e_t = (1 − β)β^t R₀`, i.e. `e_t = (1 − β)R_t`, `R_{t+1} = βR_t`, beats every
positive extraction plan within the stock, up to `β^T/(1 − β)` at every horizon (prices cancel
because `log(p_t e_t) = log p_t + log e_t`). -/
theorem oil_owner_overtake (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {p e : ℕ → ℝ}
    (hp : ∀ t, 0 < p t) (he : ∀ t, 0 < e t) (hsum : ∀ T, ∑ t ∈ range T, e t ≤ R₀) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (p t * e t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (p t * cakePath β R₀ t) + β ^ T / (1 - β) := by
  have hstar : ∀ t, 0 < cakePath β R₀ t := fun t => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  have hsplit : ∀ x : ℕ → ℝ, (∀ t, 0 < x t) → ∑ t ∈ range T, β ^ t * Real.log (p t * x t) =
      ∑ t ∈ range T, β ^ t * Real.log (p t) + ∑ t ∈ range T, β ^ t * Real.log (x t) := by
    intro x hx
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [Real.log_mul (hp t).ne' (hx t).ne']
    ring
  rw [hsplit e he, hsplit _ hstar]
  have := cake_overtake hβ0 hβ1 hR he hsum T
  linarith

/-- AKMM, p. 769: "The maximization of `Σβ^t log(C_{o,t})` subject to this constraint and (25.25)
straightforwardly delivers `e_{o,t} = (1 − β)R_t`": among positive plans within the stock whose
utility converges, the path `(1 − β)β^t R₀` is optimal for the oil owner. -/
theorem oil_owner_optimal (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R₀) {p e : ℕ → ℝ}
    {U Us : ℝ} (hp : ∀ t, 0 < p t) (he : ∀ t, 0 < e t)
    (hsum : ∀ T, ∑ t ∈ range T, e t ≤ R₀)
    (hU : HasSum (fun t => β ^ t * Real.log (p t * e t)) U)
    (hUs : HasSum (fun t => β ^ t * Real.log (p t * cakePath β R₀ t)) Us) : U ≤ Us := by
  have h1β : 0 < 1 - β := by linarith
  refine sust_hasSum_le_of_partial hU hUs (ε := fun T => β ^ T / (1 - β)) ?_
    (Eventually.of_forall fun T => oil_owner_overtake hβ0 hβ1 hR hp he hsum T)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Log utility, Cobb–Douglas output and full depreciation

The common structure of the chapter's dynamic models (AKMM, §25.4.2, pp. 767–771, and §25.5.2,
pp. 777–778): log utility, output `Y_t` with `log Y_t = w_t + α log K_t` for some sequence `w`
(productivity, damages, energy) and the resource constraint `C_t + K_{t+1} = Y_t`.

With the saving rate `s_t = K_{t+1}/Y_t` and `B = 1/(1 − αβ)`, for every horizon `T`
`Σ_{t<T} β^t log C_t = Bα log K₀ + B Σ_{t<T} β^t w_t + Σ_{t<T} β^t φ(s_t) − β^T Bα log K_T`
with `φ(s) = log(1 − s) + αβB log s` (`lg_identity`). `φ` is maximised at `s = αβ`
(`lg_phi_le`). So lifetime utility splits into a saving part, maximised by the constant saving
rate `αβ`, a part linear in the `w_t`, and a terminal term: this is the guess-and-verify
argument behind the closed forms of GHKT and of Dasgupta–Heal, made exact at every finite
horizon (`lg_compare`). The terminal terms vanish under linear growth bounds
(`lg_linear_bound`, `lg_tendsto_linear`, `lg_summable_linear`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- The saving part of the period objective, `φ(s) = log(1 − s) + (αβ/(1 − αβ)) log s`. -/
noncomputable def lgPhi (α β s : ℝ) : ℝ :=
  Real.log (1 - s) + α * β / (1 - α * β) * Real.log s

/-- `φ` is maximised at the saving rate `s = αβ`. -/
theorem lg_phi_le {α β s : ℝ} (hab0 : 0 < α * β) (hab1 : α * β < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    lgPhi α β s ≤ lgPhi α β (α * β) := by
  have h1 : 0 < 1 - α * β := by linarith
  have t1 := sust_log_le_tangent (by linarith : 0 < 1 - s) h1
  have t2 := sust_log_le_tangent hs0 hab0
  have hk : 0 ≤ α * β / (1 - α * β) := by positivity
  have ha : α ≠ 0 := left_ne_zero_of_mul hab0.ne'
  have hb : β ≠ 0 := right_ne_zero_of_mul hab0.ne'
  unfold lgPhi
  have e : (1 - s - (1 - α * β)) / (1 - α * β) +
      α * β / (1 - α * β) * ((s - α * β) / (α * β)) = 0 := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left t2 hk]

/-- The exact finite-horizon decomposition of lifetime utility: with `s_t = K_{t+1}/Y_t`,
`Σ_{t<T} β^t log C_t = (α/(1 − αβ)) log K₀ + (1/(1 − αβ)) Σ_{t<T} β^t w_t
  + Σ_{t<T} β^t φ(s_t) − β^T (α/(1 − αβ)) log K_T`. -/
theorem lg_identity {α β : ℝ} (hab1 : α * β < 1) {K Y C w : ℕ → ℝ} (hK : ∀ t, 0 < K t)
    (hC : ∀ t, 0 < C t) (hres : ∀ t, C t + K (t + 1) = Y t)
    (hY : ∀ t, Real.log (Y t) = w t + α * Real.log (K t)) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (C t) =
      α / (1 - α * β) * Real.log (K 0) + 1 / (1 - α * β) * ∑ t ∈ range T, β ^ t * w t +
        ∑ t ∈ range T, β ^ t * lgPhi α β (K (t + 1) / Y t) -
          β ^ T * (α / (1 - α * β)) * Real.log (K T) := by
  have h1 : (1 : ℝ) - α * β ≠ 0 := (by linarith : (0 : ℝ) < 1 - α * β).ne'
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ]
    have hYp : 0 < Y n := by rw [← hres n]; linarith [hC n, hK (n + 1)]
    have hs1 : Real.log (1 - K (n + 1) / Y n) = Real.log (C n) - Real.log (Y n) := by
      rw [← Real.log_div (hC n).ne' hYp.ne']
      congr 1
      rw [eq_div_iff hYp.ne', sub_mul, one_mul, div_mul_cancel₀ _ hYp.ne']
      linarith [hres n]
    have hs2 : Real.log (K (n + 1) / Y n) = Real.log (K (n + 1)) - Real.log (Y n) :=
      Real.log_div (hK (n + 1)).ne' hYp.ne'
    simp only [lgPhi, hs1, hs2, hY n, pow_succ]
    field_simp
    ring

/-- The comparison of two plans from the same `K₀`, the second with the constant saving rate
`αβ`: at every horizon
`Σ_{t<T} β^t log C_t − Σ_{t<T} β^t log C*_t
  ≤ (1/(1 − αβ)) Σ_{t<T} β^t (w_t − w*_t) − β^T (α/(1 − αβ))(log K_T − log K*_T)`. -/
theorem lg_compare {α β : ℝ} (hab0 : 0 < α * β) (hab1 : α * β < 1) (hβ : 0 < β)
    {K Y C w Ks Ys Cs ws : ℕ → ℝ} (hK : ∀ t, 0 < K t) (hC : ∀ t, 0 < C t)
    (hres : ∀ t, C t + K (t + 1) = Y t) (hY : ∀ t, Real.log (Y t) = w t + α * Real.log (K t))
    (hKs : ∀ t, 0 < Ks t) (hCs : ∀ t, 0 < Cs t) (hress : ∀ t, Cs t + Ks (t + 1) = Ys t)
    (hYs : ∀ t, Real.log (Ys t) = ws t + α * Real.log (Ks t))
    (hsave : ∀ t, Ks (t + 1) = α * β * Ys t) (h0 : K 0 = Ks 0) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (C t) - ∑ t ∈ range T, β ^ t * Real.log (Cs t) ≤
      1 / (1 - α * β) * ∑ t ∈ range T, β ^ t * (w t - ws t) -
        β ^ T * (α / (1 - α * β)) * (Real.log (K T) - Real.log (Ks T)) := by
  rw [lg_identity hab1 hK hC hres hY, lg_identity hab1 hKs hCs hress hYs, h0]
  have hphi : ∑ t ∈ range T, β ^ t * lgPhi α β (K (t + 1) / Y t) ≤
      ∑ t ∈ range T, β ^ t * lgPhi α β (Ks (t + 1) / Ys t) := by
    refine sum_le_sum fun t _ => ?_
    have hYp : 0 < Y t := by rw [← hres t]; linarith [hC t, hK (t + 1)]
    have hYsp : 0 < Ys t := by rw [← hress t]; linarith [hCs t, hKs (t + 1)]
    have hs : Ks (t + 1) / Ys t = α * β := by rw [hsave t]; field_simp
    rw [hs]
    refine mul_le_mul_of_nonneg_left (lg_phi_le hab0 hab1 (div_pos (hK (t + 1)) hYp) ?_)
      (by positivity)
    rw [div_lt_one hYp, ← hres t]; linarith [hC t]
  have e : ∑ t ∈ range T, β ^ t * (w t - ws t) =
      ∑ t ∈ range T, β ^ t * w t - ∑ t ∈ range T, β ^ t * ws t := by
    rw [← sum_sub_distrib]; congr 1; ext t; ring
  rw [e, mul_sub]
  linarith

/-- A linear growth bound for `a_{t+1} = c_t + α a_t` with `|c_t| ≤ M(1 + t)` and `0 ≤ α < 1`:
`|a_t| ≤ |a₀| + (M/(1 − α))t`. -/
theorem lg_linear_bound {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M) {a c : ℕ → ℝ}
    (hc : ∀ t, |c t| ≤ M * (1 + t)) (ha : ∀ t, a (t + 1) = c t + α * a t) (t : ℕ) :
    |a t| ≤ |a 0| + M / (1 - α) * t := by
  have h1 : 0 < 1 - α := by linarith
  set Q := M / (1 - α) with hQ
  have hQM : M ≤ Q := by rw [hQ, le_div_iff₀ h1]; nlinarith
  have hQeq : M + α * Q = Q := by rw [hQ]; field_simp; ring
  induction t with
  | zero => simp
  | succ n ih =>
    rw [ha n]
    have hQ0 : 0 ≤ Q := le_trans hM hQM
    calc |c n + α * a n| ≤ |c n| + α * |a n| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hα0]
      _ ≤ M * (1 + n) + α * (|a 0| + Q * n) := by gcongr; exact hc n
      _ ≤ |a 0| + Q * ((n : ℝ) + 1) := by
          have : 0 ≤ |a 0| := abs_nonneg _
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith [mul_le_mul_of_nonneg_right hQM hn]
      _ = |a 0| + Q * ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- `β^T(P + QT) → 0` for `0 ≤ β < 1`. -/
theorem lg_tendsto_linear {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P Q : ℝ) :
    Tendsto (fun T : ℕ => β ^ T * (P + Q * T)) atTop (𝓝 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const P
  have h2 := (tendsto_self_mul_const_pow_of_lt_one hβ0 hβ1).const_mul Q
  have := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at this
  refine this.congr fun T => ?_
  ring

/-- `Σ_t β^t(P + Qt)` converges for `0 ≤ β < 1`. -/
theorem lg_summable_linear {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P Q : ℝ) :
    Summable (fun t : ℕ => β ^ t * (P + Q * t)) := by
  have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have h1 := (summable_geometric_of_lt_one hβ0 hβ1).mul_left P
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left Q
  refine (h1.add h2).congr fun t => ?_
  simp only [pow_one]
  ring

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The GHKT optimal carbon tax

AKMM, §25.4.2 (pp. 770–771), equations (25.30)–(25.32): the planner's problem with log utility,
Cobb–Douglas production, full depreciation and damages `e^{−γS}`, after Golosov, Hassler,
Krusell and Tsyvinski (2014).

**The planner's economy** (`GHKT`). Output is `Y_t = e^{z_t − γS_t + g(x_t)}K_t^α` and
`C_t + K_{t+1} = Y_t`; the energy choice `x_t ∈ X` enters output through `g` (the log of the
energy and labour terms) and emits `m(x_t) ≥ 0`; atmospheric carbon is
`S_t = S̄_t + Σ_{v≤t}(1 − d_{t−v})m(x_v)` (25.9), with any kernel `0 ≤ 1 − d_j ≤ 1`, and `S̄`
collects `S₀` and legacy carbon. Let `Ψ = Σ_j β^j(1 − d_j)`.

**Optimality** (`ghkt_optimal`). If `e*` maximises `g(x) − γΨm(x)` over `X`, the plan with
`x_t = e*` and the constant saving rate `K_{t+1} = αβY_t` (`ghktOptK`) is feasible
(`ghkt_opt_feasible`), has convergent utility (`ghkt_opt_summable`) and beats every feasible
plan whose utility converges. The proof is the exact finite-horizon decomposition of
`LogGrowth` (`lg_compare`), the exchange of the order of summation in the carbon term
(`ghkt_sum_interchange`), and bounds on the three error terms, which vanish
(`ghkt_overtake`). No first-order condition or transversality condition is assumed.

**The tax** (`ghkt_tax_of_proportional`, `eq_25_31`, `eq_25_32`). `∂F_t/∂S_t / Y_t = −γ`
(25.31); along the optimum `C_t = (1 − αβ)Y_t`, so the marginal externality (25.30) with
`U' = 1/C` and `∂S_{t+j}/∂e_t = 1 − d_j` is `−γY_tΨ`, and the Pigou tax is
`τ_t = Y_t Σ_j β^j γ(1 − d_j)` (25.32); with the kernel (25.10),
`τ_t = γY_t(φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ)))` (`eq_25_32_ghkt`).
Only `C_{t+j}/Y_{t+j}` constant is used.

**Departure.** The book's planner also buys coal and green energy with final goods (25.23), so
that `C/Y` is not constant and (25.32) is not exact there; we prove it in the GHKT benchmark
where energy uses no final goods. The concrete instance (`coalEconomy`) is GHKT's coal sector:
coal produced from labour, `g(x) = ν log x + (1 − α − ν) log(1 − x/χ)`; there `e*` exists
(`ghkt_coal_opt`), the assumptions hold (`ghkt_coal_assumptions`), and the optimal energy use is
the one a firm chooses when emissions are taxed at `τ_t` (`ghkt_coal_pigou`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- The GHKT planner's economy (AKMM, (25.9), (25.20)–(25.23), pp. 768–770). -/
structure GHKT where
  /-- capital share -/
  α : ℝ
  /-- discount factor -/
  β : ℝ
  /-- damage parameter in `e^{−γS}` -/
  γ : ℝ
  /-- carbon kernel `1 − d_j` -/
  k : ℕ → ℝ
  /-- log productivity `z_t` -/
  z : ℕ → ℝ
  /-- carbon not due to the planner's emissions -/
  Sbar : ℕ → ℝ
  /-- the log energy (and labour) term of output -/
  g : ℝ → ℝ
  /-- emissions of an energy choice -/
  m : ℝ → ℝ
  /-- feasible energy choices -/
  X : Set ℝ
  /-- initial capital -/
  K0 : ℝ

/-- The standing assumptions on a GHKT economy. -/
structure GHKTAssumptions (E : GHKT) : Prop where
  α_pos : 0 < E.α
  α_lt : E.α < 1
  β_pos : 0 < E.β
  β_lt : E.β < 1
  γ_nonneg : 0 ≤ E.γ
  k_nonneg : ∀ j, 0 ≤ E.k j
  k_le : ∀ j, E.k j ≤ 1
  z_bdd : ∃ Z, ∀ t, |E.z t| ≤ Z
  Sbar_nonneg : ∀ t, 0 ≤ E.Sbar t
  Sbar_bdd : ∃ S, ∀ t, E.Sbar t ≤ S
  m_nonneg : ∀ x ∈ E.X, 0 ≤ E.m x
  m_bdd : ∃ M, ∀ x ∈ E.X, E.m x ≤ M
  g_bdd : ∃ L, ∀ x ∈ E.X, E.g x ≤ L
  K0_pos : 0 < E.K0

namespace GHKT

variable (E : GHKT)

/-- `Ψ = Σ_j β^j(1 − d_j)`. -/
noncomputable def Psi : ℝ := ∑' j, E.β ^ j * E.k j

/-- Partial sums `Ψ_n = Σ_{j<n} β^j(1 − d_j)`. -/
noncomputable def PsiN (n : ℕ) : ℝ := ∑ j ∈ range n, E.β ^ j * E.k j

/-- AKMM, (25.9), p. 770: atmospheric carbon under the energy path `x`. -/
noncomputable def carbon (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  E.Sbar t + excessCarbon E.k (fun v => E.m (x v)) t

/-- AKMM, (25.21), p. 768: output `Y_t = e^{z_t − γS_t + g(x_t)}K_t^α`. -/
noncomputable def output (K x : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.exp (E.z t - E.γ * E.carbon x t + E.g (x t)) * K t ^ E.α

/-- Consumption from (25.23) with full depreciation: `C_t = Y_t − K_{t+1}`. -/
noncomputable def cons (K x : ℕ → ℝ) (t : ℕ) : ℝ := E.output K x t - K (t + 1)

/-- A feasible plan: initial capital, energy choices in `X`, positive capital and consumption. -/
def Feasible (K x : ℕ → ℝ) : Prop :=
  K 0 = E.K0 ∧ (∀ t, x t ∈ E.X) ∧ (∀ t, 0 < K t) ∧ ∀ t, 0 < E.cons K x t

/-- The candidate optimum: constant energy choice `e*` and saving `K_{t+1} = αβY_t`. -/
noncomputable def optK (es : ℝ) : ℕ → ℝ
  | 0 => E.K0
  | t + 1 => E.α * E.β *
      (Real.exp (E.z t - E.γ * E.carbon (fun _ => es) t + E.g es) * optK es t ^ E.α)

end GHKT

variable {E : GHKT}

/-- The candidate saves `αβ` of output: `K_{t+1} = αβY_t`. -/
theorem ghkt_opt_saving (es : ℝ) (t : ℕ) :
    E.optK es (t + 1) = E.α * E.β * E.output (E.optK es) (fun _ => es) t := rfl

/-- AKMM, p. 770: along the candidate, `C_t = (1 − αβ)Y_t`. -/
theorem ghkt_opt_cons (es : ℝ) (t : ℕ) :
    E.cons (E.optK es) (fun _ => es) t =
      (1 - E.α * E.β) * E.output (E.optK es) (fun _ => es) t := by
  rw [GHKT.cons, ghkt_opt_saving]; ring

/-- `log Y_t = w_t + α log K_t` with `w_t = z_t − γS_t + g(x_t)`. -/
theorem ghkt_log_output {K x : ℕ → ℝ} (t : ℕ) (hK : 0 < K t) :
    Real.log (E.output K x t) =
      (E.z t - E.γ * E.carbon x t + E.g (x t)) + E.α * Real.log (K t) := by
  rw [GHKT.output, Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hK _).ne',
    Real.log_exp, Real.log_rpow hK]

/-- The candidate is feasible. -/
theorem ghkt_opt_feasible (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X) :
    E.Feasible (E.optK es) (fun _ => es) := by
  have hab : 0 < 1 - E.α * E.β := by nlinarith [h.α_pos, h.α_lt, h.β_pos, h.β_lt]
  have hK : ∀ t, 0 < E.optK es t := by
    intro t
    induction t with
    | zero => exact h.K0_pos
    | succ n ih =>
      change 0 < E.α * E.β * (Real.exp _ * E.optK es n ^ E.α)
      have := h.α_pos; have := h.β_pos
      have := Real.rpow_pos_of_pos ih E.α
      positivity
  refine ⟨rfl, fun _ => hes, hK, fun t => ?_⟩
  rw [ghkt_opt_cons]
  have : 0 < E.output (E.optK es) (fun _ => es) t := by
    unfold GHKT.output; have := Real.rpow_pos_of_pos (hK t) E.α; positivity
  positivity

/-- `Σ_j β^j(1 − d_j)` converges to `Ψ`, and its tail beyond `n` lies in `[0, β^n/(1 − β)]`. -/
theorem ghkt_psi (h : GHKTAssumptions E) :
    HasSum (fun j => E.β ^ j * E.k j) E.Psi ∧
      ∀ n, 0 ≤ E.Psi - E.PsiN n ∧ E.Psi - E.PsiN n ≤ E.β ^ n / (1 - E.β) := by
  have hβ0 := h.β_pos.le
  have hs : Summable (fun j => E.β ^ j * E.k j) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0 j) (h.k_nonneg j))
      (fun j => ?_) (summable_geometric_of_lt_one hβ0 h.β_lt)
    have := h.k_le j
    have := pow_nonneg hβ0 j
    nlinarith
  refine ⟨hs.hasSum, fun n => ?_⟩
  have htail : HasSum (fun i => E.β ^ (i + n) * E.k (i + n)) (E.Psi - E.PsiN n) :=
    (hasSum_nat_add_iff' n).mpr hs.hasSum
  have hgeo : HasSum (fun i => E.β ^ (i + n)) (E.β ^ n / (1 - E.β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 h.β_lt).mul_left (E.β ^ n)
    convert this using 1
    · funext i; rw [pow_add]; ring
    · ring
  refine ⟨htail.nonneg fun i => mul_nonneg (pow_nonneg hβ0 _) (h.k_nonneg _),
    hasSum_le (fun i => ?_) htail hgeo⟩
  have := h.k_le (i + n)
  have := pow_nonneg hβ0 (i + n)
  nlinarith

/-- Exchanging the order of summation in the discounted carbon stock:
`Σ_{t<T} β^t Σ_{v≤t}(1 − d_{t−v})d_v = Σ_{v<T} β^v d_v Ψ_{T−v}`. -/
theorem ghkt_sum_interchange (E : GHKT) (d : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ range T, E.β ^ t * excessCarbon E.k d t =
      ∑ v ∈ range T, E.β ^ v * d v * E.PsiN (T - v) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun v => E.β ^ v * d v * E.PsiN (n + 1 - v))]
    have hstep : ∀ v ∈ range n, E.β ^ v * d v * E.PsiN (n + 1 - v) =
        E.β ^ v * d v * E.PsiN (n - v) + E.β ^ n * (E.k (n - v) * d v) := by
      intro v hv
      have hv' : v < n := mem_range.mp hv
      rw [show n + 1 - v = (n - v) + 1 by omega, GHKT.PsiN, sum_range_succ, ← GHKT.PsiN]
      have : E.β ^ v * E.β ^ (n - v) = E.β ^ n := by rw [← pow_add]; congr 1; omega
      linear_combination (d v * E.k (n - v)) * this
    rw [sum_congr rfl hstep, sum_add_distrib, ← mul_sum, excessCarbon, sum_range_succ,
      show n + 1 - n = 1 by omega, Nat.sub_self]
    simp only [GHKT.PsiN, range_one, sum_singleton, pow_zero, one_mul]
    ring

/-- The core estimate behind optimality: for a feasible plan, at every horizon the utility
shortfall against the candidate is at most an error term that vanishes. -/
theorem ghkt_overtake (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X)
    (hopt : ∀ x ∈ E.X, E.g x - E.γ * E.Psi * E.m x ≤ E.g es - E.γ * E.Psi * E.m es)
    {K x : ℕ → ℝ} (hF : E.Feasible K x)
    (hC : Tendsto (fun t => E.β ^ t * Real.log (E.cons K x t)) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ T,
      ∑ t ∈ range T, E.β ^ t * Real.log (E.cons K x t) ≤
        ∑ t ∈ range T, E.β ^ t * Real.log (E.cons (E.optK es) (fun _ => es) t) + err T := by
  obtain ⟨hK0, hX, hKpos, hCpos⟩ := hF
  obtain ⟨Z, hZ⟩ := h.z_bdd
  obtain ⟨Sb, hSb⟩ := h.Sbar_bdd
  obtain ⟨M, hM⟩ := h.m_bdd
  obtain ⟨L, hL⟩ := h.g_bdd
  have hα0 := h.α_pos
  have hβ0 := h.β_pos
  have hβ1 := h.β_lt
  have hγ := h.γ_nonneg
  have hab0 : 0 < E.α * E.β := mul_pos hα0 hβ0
  have hab1 : E.α * E.β < 1 := by nlinarith [h.α_lt]
  have h1ab : 0 < 1 - E.α * E.β := by linarith
  have h1β : 0 < 1 - E.β := by linarith
  have hM0 : 0 ≤ M := le_trans (h.m_nonneg es hes) (hM es hes)
  obtain ⟨hPsi, hTail⟩ := ghkt_psi h
  have hPsi0 : 0 ≤ E.Psi := hPsi.nonneg fun j => mul_nonneg (pow_nonneg hβ0.le j) (h.k_nonneg j)
  set xs : ℕ → ℝ := fun _ => es with hxsdef
  set Ks := E.optK es with hKsdef
  obtain ⟨-, -, hKs, hCs⟩ := ghkt_opt_feasible h hes
  -- carbon stocks are nonnegative and the candidate's grows at most linearly
  have hEC0 : ∀ y : ℕ → ℝ, (∀ t, y t ∈ E.X) → ∀ t,
      0 ≤ excessCarbon E.k (fun v => E.m (y v)) t := by
    intro y hy t
    exact sum_nonneg fun v _ => mul_nonneg (h.k_nonneg _) (h.m_nonneg _ (hy v))
  have hS0 : ∀ t, 0 ≤ E.carbon x t := fun t => add_nonneg (h.Sbar_nonneg t) (hEC0 x hX t)
  have hSs : ∀ t, 0 ≤ E.carbon xs t ∧ E.carbon xs t ≤ Sb + M * (1 + t) := by
    intro t
    refine ⟨add_nonneg (h.Sbar_nonneg t) (hEC0 xs (fun _ => hes) t), ?_⟩
    have : excessCarbon E.k (fun v => E.m (xs v)) t ≤ ∑ v ∈ range (t + 1), M := by
      refine sum_le_sum fun v _ => ?_
      have := h.k_le (t - v); have := h.k_nonneg (t - v)
      have := h.m_nonneg es hes; have := hM es hes
      simp only [xs]; nlinarith
    simp only [sum_const, card_range, nsmul_eq_mul] at this
    unfold GHKT.carbon
    push_cast at this
    linarith [hSb t]
  -- the decomposition of `LogGrowth`
  set w : ℕ → ℝ := fun t => E.z t - E.γ * E.carbon x t + E.g (x t)
  set ws : ℕ → ℝ := fun t => E.z t - E.γ * E.carbon xs t + E.g es
  have hcmp := fun T => lg_compare (β := E.β) hab0 hab1 hβ0 (K := K) (Y := E.output K x)
    (C := E.cons K x) (w := w) (Ks := Ks) (Ys := E.output Ks xs) (Cs := E.cons Ks xs) (ws := ws)
    hKpos hCpos (fun t => by simp [GHKT.cons]) (fun t => ghkt_log_output t (hKpos t))
    hKs hCs (fun t => by simp [GHKT.cons]) (fun t => ghkt_log_output t (hKs t))
    (fun t => ghkt_opt_saving es t) (by rw [hK0]; rfl) T
  -- the energy and carbon term
  have henergy : ∀ T, ∑ t ∈ range T, E.β ^ t * (w t - ws t) ≤
      E.γ * M / (1 - E.β) * (T * E.β ^ T) := by
    intro T
    set dd : ℕ → ℝ := fun v => E.m (x v) - E.m es
    have hsplit : ∀ t, w t - ws t =
        (E.g (x t) - E.g es) - E.γ * excessCarbon E.k dd t := by
      intro t
      simp only [w, ws, GHKT.carbon, excessCarbon, dd, xs, mul_sub, sum_sub_distrib]
      ring
    have hsum : ∑ t ∈ range T, E.β ^ t * (w t - ws t) =
        ∑ v ∈ range T, E.β ^ v * ((E.g (x v) - E.γ * E.Psi * E.m (x v)) -
          (E.g es - E.γ * E.Psi * E.m es)) +
        E.γ * ∑ v ∈ range T, E.β ^ v * dd v * (E.Psi - E.PsiN (T - v)) := by
      have hI := ghkt_sum_interchange E dd T
      have hL : ∑ t ∈ range T, E.β ^ t * (w t - ws t) = ∑ t ∈ range T,
          (E.β ^ t * (E.g (x t) - E.g es) - E.γ * (E.β ^ t * excessCarbon E.k dd t)) :=
        sum_congr rfl fun t _ => by rw [hsplit]; ring
      rw [hL, sum_sub_distrib, ← mul_sum, hI, mul_sum, mul_sum, ← sum_add_distrib,
        ← sum_sub_distrib]
      refine sum_congr rfl fun v _ => ?_
      simp only [dd]
      ring
    rw [hsum]
    have h1 : ∑ v ∈ range T, E.β ^ v * ((E.g (x v) - E.γ * E.Psi * E.m (x v)) -
        (E.g es - E.γ * E.Psi * E.m es)) ≤ 0 :=
      sum_nonpos fun v _ => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0.le v)
        (by linarith [hopt (x v) (hX v)])
    have h2 : ∑ v ∈ range T, E.β ^ v * dd v * (E.Psi - E.PsiN (T - v)) ≤
        ∑ v ∈ range T, M / (1 - E.β) * E.β ^ T := by
      refine sum_le_sum fun v hv => ?_
      have hv' : v < T := mem_range.mp hv
      obtain ⟨t0, t1⟩ := hTail (T - v)
      have hdd : dd v ≤ M := by
        simp only [dd]; linarith [hM (x v) (hX v), h.m_nonneg es hes]
      have hbv := pow_nonneg hβ0.le v
      have hpow : E.β ^ v * E.β ^ (T - v) = E.β ^ T := by rw [← pow_add]; congr 1; omega
      calc E.β ^ v * dd v * (E.Psi - E.PsiN (T - v))
          ≤ E.β ^ v * M * (E.Psi - E.PsiN (T - v)) := by
            have := mul_le_mul_of_nonneg_left hdd hbv
            exact mul_le_mul_of_nonneg_right this t0
        _ ≤ E.β ^ v * M * (E.β ^ (T - v) / (1 - E.β)) :=
            mul_le_mul_of_nonneg_left t1 (mul_nonneg hbv hM0)
        _ = M / (1 - E.β) * E.β ^ T := by rw [← hpow]; field_simp
    simp only [sum_const, card_range, nsmul_eq_mul] at h2
    have := mul_le_mul_of_nonneg_left h2 hγ
    calc _ ≤ 0 + E.γ * (T * (M / (1 - E.β) * E.β ^ T)) := add_le_add h1 this
      _ = _ := by ring
  -- the competitor's terminal capital: `−α log K_T ≤ Z + L − log C_T`
  have hterm : ∀ T, -(E.α * Real.log (K T)) ≤ Z + L - Real.log (E.cons K x T) := by
    intro T
    have hYpos : 0 < E.output K x T := by
      have := hCpos T; have := hKpos (T + 1); unfold GHKT.cons at *; linarith
    have hCY : Real.log (E.cons K x T) ≤ Real.log (E.output K x T) :=
      Real.log_le_log (hCpos T) (by unfold GHKT.cons; linarith [hKpos (T + 1)])
    rw [ghkt_log_output T (hKpos T)] at hCY
    have := (abs_le.mp (hZ T)).2
    have := hL (x T) (hX T)
    have := mul_nonneg hγ (hS0 T)
    linarith
  -- the candidate's capital grows at most linearly in logs
  set cst := |Real.log (E.α * E.β)| + Z + E.γ * (Sb + M) + E.γ * M + |E.g es| with hcst
  have hcst0 : 0 ≤ cst := by
    have : 0 ≤ Sb := le_trans (h.Sbar_nonneg 0) (hSb 0)
    have := mul_nonneg hγ (add_nonneg this hM0)
    have := mul_nonneg hγ hM0
    have := le_trans (abs_nonneg _) (hZ 0)
    rw [hcst]
    linarith [abs_nonneg (Real.log (E.α * E.β)), abs_nonneg (E.g es)]
  have hrec : ∀ t, Real.log (Ks (t + 1)) =
      (Real.log (E.α * E.β) + ws t) + E.α * Real.log (Ks t) := by
    intro t
    rw [hKsdef, ghkt_opt_saving, Real.log_mul hab0.ne' (by
      unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs t) E.α; positivity),
      ghkt_log_output t (hKs t)]
    ring
  have hlin := lg_linear_bound (a := fun t => Real.log (Ks t))
    (c := fun t => Real.log (E.α * E.β) + ws t) hα0.le h.α_lt hcst0 (fun t => by
      obtain ⟨s0, s1⟩ := hSs t
      have hz := abs_le.mp (hZ t)
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hb1 := abs_le.mp (le_refl |Real.log (E.α * E.β)|)
      have hb2 := abs_le.mp (le_refl |E.g es|)
      have hSb0 : 0 ≤ Sb := le_trans (h.Sbar_nonneg 0) (hSb 0)
      have hγS : E.γ * E.carbon xs t ≤ E.γ * (Sb + M * (1 + t)) :=
        mul_le_mul_of_nonneg_left s1 hγ
      have hγS0 : 0 ≤ E.γ * E.carbon xs t := mul_nonneg hγ s0
      rw [abs_le]
      simp only [ws, hcst]
      have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ 0)
      constructor <;> nlinarith [mul_nonneg hγ hM0, mul_nonneg (mul_nonneg hγ hM0) ht,
        abs_nonneg (Real.log (E.α * E.β)), abs_nonneg (E.g es),
        mul_nonneg (abs_nonneg (Real.log (E.α * E.β))) ht, mul_nonneg hZ0 ht,
        mul_nonneg (mul_nonneg hγ (add_nonneg hSb0 hM0)) ht,
        mul_nonneg (abs_nonneg (E.g es)) ht]) hrec
  -- assemble the error term
  set B := 1 / (1 - E.α * E.β) with hB
  have hB0 : 0 ≤ B := by positivity
  set P := |Real.log (Ks 0)| with hP
  set Q := cst / (1 - E.α) with hQ
  refine ⟨fun T => B * (E.γ * M / (1 - E.β) * (T * E.β ^ T)) +
    B * (E.β ^ T * (Z + L) - E.β ^ T * Real.log (E.cons K x T)) +
    B * E.α * (E.β ^ T * (P + Q * T)), ?_, fun T => ?_⟩
  · have t1 := (tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul
      (B * (E.γ * M / (1 - E.β)))
    have t2 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (Z + L)).sub hC
    have t3 := (lg_tendsto_linear hβ0.le hβ1 P Q).const_mul (B * E.α)
    have := (t1.add (t2.const_mul B)).add t3
    simp only [mul_zero, zero_mul, sub_zero, add_zero] at this
    refine this.congr fun T => ?_
    ring
  · have hc := hcmp T
    have he := henergy T
    have ht := hterm T
    have hl : |Real.log (Ks T)| ≤ P + Q * T := hlin T
    have hl' := (abs_le.mp hl).2
    have hbT : 0 ≤ E.β ^ T := pow_nonneg hβ0.le T
    -- bound the terminal term
    have hterm2 : -(E.β ^ T * (E.α / (1 - E.α * E.β)) *
        (Real.log (K T) - Real.log (Ks T))) ≤
        B * (E.β ^ T * (Z + L) - E.β ^ T * Real.log (E.cons K x T)) +
          B * E.α * (E.β ^ T * (P + Q * T)) := by
      have e1 : E.α / (1 - E.α * E.β) = B * E.α := by rw [hB]; ring
      rw [e1]
      have k1 := mul_le_mul_of_nonneg_left ht (mul_nonneg hB0 hbT)
      have k2 := mul_le_mul_of_nonneg_left hl' (mul_nonneg (mul_nonneg hB0 hα0.le) hbT)
      nlinarith
    have hen := mul_le_mul_of_nonneg_left he hB0
    linarith

/-- The candidate's utility converges. -/
theorem ghkt_opt_summable (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X) :
    Summable (fun t => E.β ^ t * Real.log (E.cons (E.optK es) (fun _ => es) t)) := by
  obtain ⟨Z, hZ⟩ := h.z_bdd
  obtain ⟨Sb, hSb⟩ := h.Sbar_bdd
  obtain ⟨M, hM⟩ := h.m_bdd
  have hα0 := h.α_pos
  have hβ0 := h.β_pos
  have hγ := h.γ_nonneg
  have hab0 : 0 < E.α * E.β := mul_pos hα0 hβ0
  have hab1 : E.α * E.β < 1 := by nlinarith [h.α_lt, h.β_lt]
  have hM0 : 0 ≤ M := le_trans (h.m_nonneg es hes) (hM es hes)
  have hSb0 : 0 ≤ Sb := le_trans (h.Sbar_nonneg 0) (hSb 0)
  set xs : ℕ → ℝ := fun _ => es with hxsdef
  set Ks := E.optK es with hKsdef
  obtain ⟨-, -, hKs, hCs⟩ := ghkt_opt_feasible h hes
  have hSs : ∀ t, 0 ≤ E.carbon xs t ∧ E.carbon xs t ≤ Sb + M * (1 + t) := by
    intro t
    refine ⟨add_nonneg (h.Sbar_nonneg t)
      (sum_nonneg fun v _ => mul_nonneg (h.k_nonneg _) (h.m_nonneg _ hes)), ?_⟩
    have : excessCarbon E.k (fun v => E.m (xs v)) t ≤ ∑ v ∈ range (t + 1), M := by
      refine sum_le_sum fun v _ => ?_
      have := h.k_le (t - v); have := h.k_nonneg (t - v)
      have := h.m_nonneg es hes; have := hM es hes
      simp only [xs]; nlinarith
    simp only [sum_const, card_range, nsmul_eq_mul] at this
    unfold GHKT.carbon
    push_cast at this
    linarith [hSb t]
  set ws : ℕ → ℝ := fun t => E.z t - E.γ * E.carbon xs t + E.g es
  set cst := |Real.log (E.α * E.β)| + Z + E.γ * (Sb + M) + E.γ * M + |E.g es| +
    |Real.log (1 - E.α * E.β)| with hcst
  have hcst0 : 0 ≤ cst := by
    have := mul_nonneg hγ (add_nonneg hSb0 hM0)
    have := mul_nonneg hγ hM0
    have := le_trans (abs_nonneg _) (hZ 0)
    rw [hcst]
    linarith [abs_nonneg (Real.log (E.α * E.β)), abs_nonneg (E.g es),
      abs_nonneg (Real.log (1 - E.α * E.β))]
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ 0)
  set c0 := Z + E.γ * (Sb + M) + E.γ * M + |E.g es| with hc0
  have hws : ∀ t, |ws t| ≤ c0 * (1 + t) := by
    intro t
    obtain ⟨s0, s1⟩ := hSs t
    have hz := abs_le.mp (hZ t)
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hγS : E.γ * E.carbon xs t ≤ E.γ * (Sb + M * (1 + t)) :=
      mul_le_mul_of_nonneg_left s1 hγ
    have hγS0 : 0 ≤ E.γ * E.carbon xs t := mul_nonneg hγ s0
    have hb2 := abs_le.mp (le_refl |E.g es|)
    rw [abs_le]
    simp only [ws, hc0]
    constructor <;> nlinarith [mul_nonneg hγ hM0, mul_nonneg (mul_nonneg hγ hM0) ht,
      abs_nonneg (E.g es), mul_nonneg hZ0 ht,
      mul_nonneg (mul_nonneg hγ (add_nonneg hSb0 hM0)) ht,
      mul_nonneg (abs_nonneg (E.g es)) ht]
  have hcst' : cst = |Real.log (E.α * E.β)| + c0 + |Real.log (1 - E.α * E.β)| := by
    rw [hcst, hc0]; ring
  have hc00 : 0 ≤ c0 := by
    rw [hc0]
    have := mul_nonneg hγ (add_nonneg hSb0 hM0)
    have := mul_nonneg hγ hM0
    linarith [abs_nonneg (E.g es)]
  have hrec : ∀ t, Real.log (Ks (t + 1)) =
      (Real.log (E.α * E.β) + ws t) + E.α * Real.log (Ks t) := by
    intro t
    rw [hKsdef, ghkt_opt_saving, Real.log_mul hab0.ne' (by
      unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs t) E.α; positivity),
      ghkt_log_output t (hKs t)]
    ring
  have hlin := lg_linear_bound (a := fun t => Real.log (Ks t))
    (c := fun t => Real.log (E.α * E.β) + ws t) hα0.le h.α_lt hcst0 (fun t => by
      have := hws t
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      calc |Real.log (E.α * E.β) + ws t| ≤ |Real.log (E.α * E.β)| + |ws t| := abs_add_le _ _
        _ ≤ cst * (1 + t) := by
          rw [hcst']
          nlinarith [abs_nonneg (Real.log (1 - E.α * E.β)), abs_nonneg (Real.log (E.α * E.β)),
            mul_nonneg (abs_nonneg (Real.log (1 - E.α * E.β))) ht,
            mul_nonneg (abs_nonneg (Real.log (E.α * E.β))) ht]) hrec
  -- `log C*_t = log(1 − αβ) + w*_t + α log K*_t`
  have hlogC : ∀ t, Real.log (E.cons Ks xs t) =
      Real.log (1 - E.α * E.β) + ws t + E.α * Real.log (Ks t) := by
    intro t
    rw [hKsdef, hxsdef, ghkt_opt_cons, Real.log_mul (by linarith) (by
      unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs t) E.α; positivity),
      ghkt_log_output t (hKs t)]
    ring
  refine Summable.of_norm_bounded (g := fun t : ℕ => E.β ^ t *
    ((cst + E.α * |Real.log (Ks 0)|) + (cst + E.α * (cst / (1 - E.α))) * t))
    (lg_summable_linear hβ0.le h.β_lt _ _) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le t), hlogC]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le t)
  have h1 := hws t
  have h2 := hlin t
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  calc |Real.log (1 - E.α * E.β) + ws t + E.α * Real.log (Ks t)|
      ≤ |Real.log (1 - E.α * E.β)| + |ws t| + E.α * |Real.log (Ks t)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hα0]
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h2 hα0.le
        rw [hcst'] at this ⊢
        nlinarith [abs_nonneg (Real.log (1 - E.α * E.β)), abs_nonneg (Real.log (E.α * E.β)),
          mul_nonneg (abs_nonneg (Real.log (1 - E.α * E.β))) ht,
          mul_nonneg (abs_nonneg (Real.log (E.α * E.β))) ht]

/-- **The GHKT planner's optimum** (AKMM, pp. 770–771). If `e*` maximises `g − γΨm` on `X`,
the plan `x_t = e*`, `K_{t+1} = αβY_t` maximises `Σβ^t log C_t` among all feasible plans whose
utility converges. -/
theorem ghkt_optimal (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X)
    (hopt : ∀ x ∈ E.X, E.g x - E.γ * E.Psi * E.m x ≤ E.g es - E.γ * E.Psi * E.m es)
    {K x : ℕ → ℝ} (hF : E.Feasible K x) {U : ℝ}
    (hU : HasSum (fun t => E.β ^ t * Real.log (E.cons K x t)) U) :
    U ≤ ∑' t, E.β ^ t * Real.log (E.cons (E.optK es) (fun _ => es) t) := by
  obtain ⟨err, herr, hle⟩ := ghkt_overtake h hes hopt hF hU.summable.tendsto_atTop_zero
  exact sust_hasSum_le_of_partial hU (ghkt_opt_summable h hes).hasSum herr
    (Eventually.of_forall hle)

/-- AKMM, (25.31), p. 771: `∂(e^{−γS}Ỹ)/∂S · 1/(e^{−γS}Ỹ) = −γ`: the derivative of output in
the carbon stock is `−γY`. -/
theorem eq_25_31 (z γ g Ka S : ℝ) :
    HasDerivAt (fun S => Real.exp (z - γ * S + g) * Ka)
      (-γ * (Real.exp (z - γ * S + g) * Ka)) S := by
  have := ((((hasDerivAt_id' S).const_mul γ).const_sub z).add_const g).exp.mul_const Ka
  convert this using 1
  ring

/-- AKMM, (25.30), p. 770: the marginal externality with log utility,
`Λ_t = Σ_j β^j (C_t/C_{t+j}) (∂F_{t+j}/∂S_{t+j}) (∂S_{t+j}/∂e_t)`, with `∂F/∂S = −γY` (25.31) and
`∂S_{t+j}/∂e_t = 1 − d_j` (`excessCarbon_pulse`). When consumption is proportional to output
along the path, `Λ_t = −γY_tΨ`. -/
theorem ghkt_tax_of_proportional {β γ c Psi : ℝ} {k Y C : ℕ → ℝ} (hc : c ≠ 0)
    (hY : ∀ t, 0 < Y t) (hCY : ∀ t, C t = c * Y t) (hPsi : HasSum (fun j => β ^ j * k j) Psi)
    (t : ℕ) :
    HasSum (fun j => β ^ j * (C t / C (t + j)) * (-γ * Y (t + j)) * k j) (-(γ * Y t * Psi)) := by
  have := hPsi.mul_left (-(γ * Y t))
  convert this using 1
  · funext j
    rw [hCY, hCY]
    have := (hY (t + j)).ne'
    field_simp
  · ring

/-- **AKMM, (25.30)–(25.32), p. 771: the optimal carbon tax.** Along the planner's optimum the
marginal externality of a unit of emissions at `t` is `−γY_tΨ`, so the Pigou tax is
`τ_t = Y_t Σ_j β^j γ(1 − d_j)`. -/
theorem eq_25_32 (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X) (t : ℕ) :
    HasSum (fun j => E.β ^ j *
        (E.cons (E.optK es) (fun _ => es) t / E.cons (E.optK es) (fun _ => es) (t + j)) *
        (-E.γ * E.output (E.optK es) (fun _ => es) (t + j)) * E.k j)
      (-(E.output (E.optK es) (fun _ => es) t * ∑' j, E.β ^ j * E.γ * E.k j)) := by
  have hab : 1 - E.α * E.β ≠ 0 := by nlinarith [h.α_pos, h.α_lt, h.β_pos, h.β_lt]
  obtain ⟨-, -, hKs, -⟩ := ghkt_opt_feasible h hes
  have hY : ∀ s, 0 < E.output (E.optK es) (fun _ => es) s := fun s => by
    unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs s) E.α; positivity
  have hP := (ghkt_psi h).1
  have := ghkt_tax_of_proportional (γ := E.γ) hab hY (fun s => ghkt_opt_cons es s) hP t
  have htsum : ∑' j, E.β ^ j * E.γ * E.k j = E.γ * E.Psi := by
    rw [GHKT.Psi, ← tsum_mul_left]
    congr 1; funext j; ring
  rw [htsum]
  convert this using 1
  ring

/-- AKMM, (25.32) with the GHKT kernel (25.10): the optimal tax is
`τ_t = γY_t(φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ)))`. -/
theorem eq_25_32_ghkt {β γ φL φ0 φ Yt : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) :
    Yt * ∑' j, β ^ j * γ * ghktKernel φL φ0 φ j =
      γ * Yt * (φL / (1 - β) + (1 - φL) * φ0 / (1 - β * (1 - φ))) := by
  have h := (ghktKernel_hasSum (φL := φL) (φ0 := φ0) hβ0 hβ1 hφ hφ1).mul_left γ
  rw [show (fun j => β ^ j * γ * ghktKernel φL φ0 φ j) =
    fun j => γ * (β ^ j * ghktKernel φL φ0 φ j) from funext fun j => by ring, h.tsum_eq]
  ring

/-- GHKT's coal sector: energy `x` is coal produced from labour at productivity `χ`, so output
has the factor `x^ν(1 − x/χ)^{1−α−ν}`, `g(x) = ν log x + (1 − α − ν) log(1 − x/χ)` on `(0, χ)`,
and coal emits one unit of carbon per unit. -/
noncomputable def coalEconomy (α β γ ν χ K0 : ℝ) (k : ℕ → ℝ) : GHKT where
  α := α
  β := β
  γ := γ
  k := k
  z := fun _ => 0
  Sbar := fun _ => 0
  g := fun x => ν * Real.log x + (1 - α - ν) * Real.log (1 - x / χ)
  m := id
  X := Set.Ioo 0 χ
  K0 := K0

/-- The coal economy satisfies the standing assumptions. -/
theorem ghkt_coal_assumptions {α β γ ν χ K0 : ℝ} {k : ℕ → ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (hαν : α + ν ≤ 1) (hχ : 0 < χ)
    (hK0 : 0 < K0) (hk0 : ∀ j, 0 ≤ k j) (hk1 : ∀ j, k j ≤ 1) :
    GHKTAssumptions (coalEconomy α β γ ν χ K0 k) where
  α_pos := hα0
  α_lt := hα1
  β_pos := hβ0
  β_lt := hβ1
  γ_nonneg := hγ
  k_nonneg := hk0
  k_le := hk1
  z_bdd := ⟨0, fun _ => by simp [coalEconomy]⟩
  Sbar_nonneg := fun _ => le_rfl
  Sbar_bdd := ⟨0, fun _ => le_rfl⟩
  m_nonneg := fun x hx => le_of_lt hx.1
  m_bdd := ⟨χ, fun x hx => le_of_lt hx.2⟩
  g_bdd := ⟨ν * Real.log χ, fun x hx => by
    have hx0 : 0 < x := hx.1
    have h1 : Real.log x ≤ Real.log χ := Real.log_le_log hx0 hx.2.le
    have hxχ : x / χ < 1 := (div_lt_one hχ).mpr hx.2
    have h2 : Real.log (1 - x / χ) ≤ 0 :=
      Real.log_nonpos (by linarith) (by have := div_pos hx0 hχ; linarith)
    have := mul_le_mul_of_nonneg_left h1 hν
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - α - ν) h2
    simp only [coalEconomy]
    linarith⟩
  K0_pos := hK0

/-- In the coal economy, for any marginal damage `c = γΨ` there is an energy choice
`e* ∈ (0, χ)` solving `ν/e − (1 − α − ν)/(χ − e) = c` (by the intermediate value theorem) and it
maximises `g(x) − cx` on `(0, χ)` (tangent-line bounds). -/
theorem ghkt_coal_opt {α ν χ c : ℝ} (hν : 0 < ν) (hαν : α + ν < 1) (hχ : 0 < χ) :
    ∃ es ∈ Set.Ioo 0 χ, ν / es - (1 - α - ν) / (χ - es) = c ∧
      ∀ x ∈ Set.Ioo 0 χ, ν * Real.log x + (1 - α - ν) * Real.log (1 - x / χ) - c * x ≤
        ν * Real.log es + (1 - α - ν) * Real.log (1 - es / χ) - c * es := by
  set f : ℝ → ℝ := fun e => ν * (χ - e) - (1 - α - ν) * e - c * e * (χ - e)
  have hcont : ContinuousOn f (Set.Icc 0 χ) := by fun_prop
  have hf0 : 0 < f 0 := by simp only [f]; nlinarith
  have hfχ : f χ < 0 := by simp only [f]; nlinarith
  obtain ⟨es, hes, hfes⟩ := intermediate_value_Icc' hχ.le hcont ⟨hfχ.le, hf0.le⟩
  have hes0 : 0 < es := by
    rcases hes.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hfes; linarith
  have hesχ : es < χ := by
    rcases hes.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hfes; linarith
  have hχe : 0 < χ - es := by linarith
  have hfoc : ν / es - (1 - α - ν) / (χ - es) = c := by
    simp only [f] at hfes
    field_simp
    linarith
  refine ⟨es, ⟨hes0, hesχ⟩, hfoc, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x / χ := by
    have : x / χ < 1 := (div_lt_one hχ).mpr hx.2; linarith
  have h1e : 0 < 1 - es / χ := by
    have : es / χ < 1 := (div_lt_one hχ).mpr hesχ; linarith
  have t1 := sust_log_le_tangent hx0 hes0
  have t2 := sust_log_le_tangent h1x h1e
  have hzero : ν * ((x - es) / es) + (1 - α - ν) * ((1 - x / χ - (1 - es / χ)) / (1 - es / χ)) -
      c * (x - es) = (x - es) * (ν / es - (1 - α - ν) / (χ - es) - c) := by
    field_simp
    ring
  rw [hfoc, sub_self, mul_zero] at hzero
  have k1 := mul_le_mul_of_nonneg_left t1 hν.le
  have k2 := mul_le_mul_of_nonneg_left t2 (by linarith : 0 ≤ 1 - α - ν)
  nlinarith

/-- AKMM, p. 771, the Pigou principle in the coal economy: the optimal coal use `e*` is the
input a competitive firm chooses when each unit of carbon is taxed at `τ_t = γΨY_t`: its
marginal product net of the labour it displaces equals the tax,
`Y_t(ν/e* − (1 − α − ν)/(χ − e*)) = τ_t`. -/
theorem ghkt_coal_pigou {α ν χ γ Psi es Yt : ℝ}
    (hfoc : ν / es - (1 - α - ν) / (χ - es) = γ * Psi) :
    Yt * (ν / es - (1 - α - ν) / (χ - es)) = γ * Psi * Yt := by
  rw [hfoc]; ring

/-- **The GHKT optimum in the coal economy** (AKMM, pp. 770–771, instance): there is a coal use
`e* ∈ (0, χ)` such that the plan `x_t = e*`, `K_{t+1} = αβY_t` is optimal among all feasible
plans with convergent utility, and it is taxed at (25.32). -/
theorem ghkt_coal_optimal {α β γ ν χ K0 : ℝ} {k : ℕ → ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 ≤ γ) (hν : 0 < ν) (hαν : α + ν < 1) (hχ : 0 < χ)
    (hK0 : 0 < K0) (hk0 : ∀ j, 0 ≤ k j) (hk1 : ∀ j, k j ≤ 1) :
    ∃ es ∈ Set.Ioo 0 χ, ∀ K x : ℕ → ℝ, (coalEconomy α β γ ν χ K0 k).Feasible K x → ∀ U : ℝ,
      HasSum (fun t => β ^ t * Real.log ((coalEconomy α β γ ν χ K0 k).cons K x t)) U →
      U ≤ ∑' t, β ^ t * Real.log ((coalEconomy α β γ ν χ K0 k).cons
        ((coalEconomy α β γ ν χ K0 k).optK es) (fun _ => es) t) := by
  set E := coalEconomy α β γ ν χ K0 k
  have h := ghkt_coal_assumptions (k := k) (K0 := K0) hα0 hα1 hβ0 hβ1 hγ hν.le hαν.le hχ hK0
    hk0 hk1
  obtain ⟨es, hes, -, hmax⟩ := ghkt_coal_opt (α := α) (c := E.γ * E.Psi) hν hαν hχ
  refine ⟨es, hes, fun K x hF U hU => ghkt_optimal (E := E) h hes (fun y hy => ?_) hF hU⟩
  have := hmax y hy
  simpa [E, coalEconomy] using this

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Growth with an exhaustible resource: Dasgupta–Heal

AKMM, §25.5.2, "A production economy" (pp. 777–778). The planner maximises `Σβ^t log c_t`
subject to `c_t + k_{t+1} = Az_t k_t^α e_t^ν` (full depreciation) and `Σ_t e_t ≤ R`, with
`z_t = z₀γ_z^t`, `A, z₀, γ_z > 0`, `0 < α < 1`, `ν ≥ 0`, `0 < β < 1`.

* The optimal plan extracts as in cake eating, `e_t = (1 − β)β^t R` (`e_t = (1 − β)R_t`,
  `R_{t+1} = R_t − e_t`), and saves `k_{t+1} = αβy_t` (`dhK`, `dh_saving`); it is feasible
  (`dh_feasible`), its utility converges (`dh_summable`) and it beats every feasible plan with
  convergent utility (`dh_optimal`): the extraction and saving problems separate exactly
  (`lg_compare` and `cake_overtake`).
* Growth: the gross growth of output `G_t = y_{t+1}/y_t` obeys
  `G_{t+1} = γ_zβ^ν G_t^α` (`dh_growth_rec`), whose unique fixed point is
  `g = (γ_zβ^ν)^{1/(1−α)}`, `g = γ_z g^α β^ν` (`dh_bgp`), and `G_t → g` (`dh_growth_tendsto`).
* Prices: the gross interest rate `1 + r_{t+1} = αy_{t+1}/k_{t+1}` equals `G_t/β`, so
  `1 + r → g/β` (`dh_interest`, `dh_interest_tendsto`); `r > 0` iff `g > β` in the limit
  (`dh_interest_pos_iff`); the resource price `p_t = νy_t/e_t` grows at `1 + r_{t+1}` every period
  — the Hotelling rule (`dh_hotelling`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- AKMM, p. 777: output `y_t = Az₀γ_z^t k_t^α e_t^ν`. -/
noncomputable def dhOut (A z0 γz α ν : ℝ) (k e : ℕ → ℝ) (t : ℕ) : ℝ :=
  A * z0 * γz ^ t * k t ^ α * e t ^ ν

/-- AKMM, p. 777: the planner's capital path `k_{t+1} = αβy_t` with extraction
`e_t = (1 − β)β^t R`. -/
noncomputable def dhK (A z0 γz α β ν K0 R : ℝ) : ℕ → ℝ
  | 0 => K0
  | t + 1 => α * β * (A * z0 * γz ^ t * dhK A z0 γz α β ν K0 R t ^ α * cakePath β R t ^ ν)

variable {A z0 γz α β ν K0 R : ℝ}

/-- AKMM, p. 777: "we find `k_{t+1} = αβAz_t k_t^α e_t^ν`". -/
theorem dh_saving (t : ℕ) :
    dhK A z0 γz α β ν K0 R (t + 1) =
      α * β * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t := by
  simp only [dhK, dhOut]

/-- `log y_t = (log(Az₀) + t log γ_z + ν log e_t) + α log k_t`. -/
theorem dh_log_out (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) {k e : ℕ → ℝ} (t : ℕ)
    (hk : 0 < k t) (he : 0 < e t) :
    Real.log (dhOut A z0 γz α ν k e t) =
      (Real.log (A * z0) + t * Real.log γz + ν * Real.log (e t)) + α * Real.log (k t) := by
  unfold dhOut
  have h1 : 0 < γz ^ t := pow_pos hγ t
  have h2 := Real.rpow_pos_of_pos hk α
  have h3 := Real.rpow_pos_of_pos he ν
  rw [Real.log_mul (by positivity) h3.ne', Real.log_mul (by positivity) h2.ne',
    Real.log_mul (by positivity) h1.ne', Real.log_pow, Real.log_rpow hk, Real.log_rpow he]
  ring

/-- AKMM, p. 777: the planner's plan is feasible: positive capital and consumption
`c_t = (1 − αβ)y_t`. -/
theorem dh_feasible (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (t : ℕ) :
    0 < dhK A z0 γz α β ν K0 R t ∧
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t -
        dhK A z0 γz α β ν K0 R (t + 1) =
        (1 - α * β) * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t ∧
      0 < dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t := by
  have he : ∀ s, 0 < cakePath β R s := fun s => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  have hk : ∀ s, 0 < dhK A z0 γz α β ν K0 R s := by
    intro s
    induction s with
    | zero => exact hK0
    | succ n ih =>
      rw [dh_saving]
      unfold dhOut
      have := Real.rpow_pos_of_pos ih α
      have := Real.rpow_pos_of_pos (he n) ν
      positivity
  refine ⟨hk t, by rw [dh_saving]; ring, ?_⟩
  unfold dhOut
  have := Real.rpow_pos_of_pos (hk t) α
  have := Real.rpow_pos_of_pos (he t) ν
  positivity

/-- `log e*_t = log((1 − β)R) + t log β`. -/
theorem dh_log_cake (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (s : ℕ) :
    Real.log (cakePath β R s) = Real.log ((1 - β) * R) + s * Real.log β := by
  have h1 : 0 < (1 - β) * R := mul_pos (by linarith) hR
  have : cakePath β R s = ((1 - β) * R) * β ^ s := by simp only [cakePath]; ring
  rw [this, Real.log_mul h1.ne' (pow_pos hβ0 s).ne', Real.log_pow]

/-- The planner's log capital grows at most linearly. -/
theorem dh_log_k_bound (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    ∃ P Q : ℝ, ∀ t, |Real.log (dhK A z0 γz α β ν K0 R t)| ≤ P + Q * t := by
  have he : ∀ s, 0 < cakePath β R s := fun s => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set M := |Real.log (α * β)| + |Real.log (A * z0)| + |Real.log γz| +
    |ν| * (|Real.log ((1 - β) * R)| + |Real.log β|) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hlogE : ∀ s : ℕ, Real.log (cakePath β R s) =
      Real.log ((1 - β) * R) + s * Real.log β := dh_log_cake hβ0 hβ1 hR
  refine ⟨|Real.log K0|, M / (1 - α), fun t => ?_⟩
  have h := lg_linear_bound (a := fun s => Real.log (dhK A z0 γz α β ν K0 R s))
    (c := fun s => Real.log (α * β) + (Real.log (A * z0) + s * Real.log γz +
      ν * Real.log (cakePath β R s))) hα0.le hα1 hM0 (fun s => by
      rw [hlogE]
      have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      calc |Real.log (α * β) + (Real.log (A * z0) + s * Real.log γz +
            ν * (Real.log ((1 - β) * R) + s * Real.log β))|
          ≤ |Real.log (α * β)| + (|Real.log (A * z0)| + s * |Real.log γz| +
            |ν| * (|Real.log ((1 - β) * R)| + s * |Real.log β|)) := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [abs_mul, abs_of_nonneg hs]
            · rw [abs_mul]
              refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (abs_nonneg _)
              rw [abs_mul, abs_of_nonneg hs]
        _ ≤ M * (1 + s) := by
            rw [hM]
            nlinarith [abs_nonneg (Real.log (α * β)), abs_nonneg (Real.log (A * z0)),
              abs_nonneg (Real.log γz), abs_nonneg ν, abs_nonneg (Real.log ((1 - β) * R)),
              abs_nonneg (Real.log β), mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log β)),
              mul_nonneg (mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log β))) hs,
              mul_nonneg (abs_nonneg (Real.log (α * β))) hs,
              mul_nonneg (abs_nonneg (Real.log (A * z0))) hs,
              mul_nonneg (mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log ((1 - β) * R)))) hs])
    (fun s => by
      have hk := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR s).1
      rw [dh_saving, Real.log_mul hab.ne' (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR s).2.2.ne',
        dh_log_out hA hz hγ s hk (he s)]
      ring) t
  exact h

/-- AKMM, pp. 777: the planner's utility converges. -/
theorem dh_summable (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    Summable (fun t => β ^ t * Real.log (dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R)
      (cakePath β R) t - dhK A z0 γz α β ν K0 R (t + 1))) := by
  obtain ⟨P, Q, hPQ⟩ := dh_log_k_bound (ν := ν) hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR
  have hab : α * β < 1 := by nlinarith
  have he : ∀ s, 0 < cakePath β R s := fun s => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  set c0 := |Real.log (1 - α * β)| + |Real.log (A * z0)| + |ν| * |Real.log ((1 - β) * R)| +
    α * P with hc0
  set c1 := |Real.log γz| + |ν| * |Real.log β| + α * Q with hc1
  refine Summable.of_norm_bounded (g := fun t : ℕ => β ^ t * (c0 + c1 * t))
    (lg_summable_linear hβ0.le hβ1 _ _) fun t => ?_
  obtain ⟨hk, hc, hy⟩ := dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le t), hc,
    Real.log_mul (by linarith) hy.ne', dh_log_out hA hz hγ t hk (he t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le t)
  have hlogE := dh_log_cake hβ0 hβ1 hR t
  rw [hlogE]
  have hk' := hPQ t
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  calc |Real.log (1 - α * β) + (Real.log (A * z0) + t * Real.log γz +
        ν * (Real.log ((1 - β) * R) + t * Real.log β) + α * Real.log (dhK A z0 γz α β ν K0 R t))|
      ≤ |Real.log (1 - α * β)| + (|Real.log (A * z0)| + t * |Real.log γz| +
        |ν| * (|Real.log ((1 - β) * R)| + t * |Real.log β|) +
          α * |Real.log (dhK A z0 γz α β ν K0 R t)|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul, abs_of_nonneg ht]
          · rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (abs_nonneg _)
            rw [abs_mul, abs_of_nonneg ht]
        · rw [abs_mul, abs_of_pos hα0]
    _ ≤ c0 + c1 * t := by
        have := mul_le_mul_of_nonneg_left hk' hα0.le
        rw [hc0, hc1]
        nlinarith [mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log β))]

/-- **AKMM, p. 777: the Dasgupta–Heal planner's optimum.** The plan `e_t = (1 − β)β^t R`,
`k_{t+1} = αβy_t` maximises `Σβ^t log c_t` among all plans with `k₀` given, `k_t, e_t > 0`,
`Σ_{t<T} e_t ≤ R`, `c_t = y_t − k_{t+1} > 0` and convergent utility. -/
theorem dh_optimal (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) {k e : ℕ → ℝ}
    (hk0 : k 0 = K0) (hk : ∀ t, 0 < k t) (he : ∀ t, 0 < e t)
    (hsum : ∀ T, ∑ t ∈ range T, e t ≤ R) (hc : ∀ t, 0 < dhOut A z0 γz α ν k e t - k (t + 1))
    {U : ℝ} (hU : HasSum (fun t => β ^ t * Real.log (dhOut A z0 γz α ν k e t - k (t + 1))) U) :
    U ≤ ∑' t, β ^ t * Real.log (dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t -
      dhK A z0 γz α β ν K0 R (t + 1)) := by
  have hab0 : 0 < α * β := mul_pos hα0 hβ0
  have hab1 : α * β < 1 := by nlinarith
  have h1ab : 0 < 1 - α * β := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hes : ∀ s, 0 < cakePath β R s := fun s => by unfold cakePath; positivity
  set Ks := dhK A z0 γz α β ν K0 R
  set B := 1 / (1 - α * β) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the finite-horizon comparison
  have hcmp := fun T => lg_compare (β := β) hab0 hab1 hβ0 (K := k)
    (Y := dhOut A z0 γz α ν k e) (C := fun t => dhOut A z0 γz α ν k e t - k (t + 1))
    (w := fun t => Real.log (A * z0) + t * Real.log γz + ν * Real.log (e t)) (Ks := Ks)
    (Ys := dhOut A z0 γz α ν Ks (cakePath β R))
    (Cs := fun t => dhOut A z0 γz α ν Ks (cakePath β R) t - Ks (t + 1))
    (ws := fun t => Real.log (A * z0) + t * Real.log γz + ν * Real.log (cakePath β R t))
    hk hc (fun t => by ring) (fun t => dh_log_out hA hz hγ t (hk t) (he t))
    (fun t => (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR t).1)
    (fun t => by
      have := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t).2
      rw [this.1]; exact mul_pos h1ab this.2)
    (fun t => by ring)
    (fun t => dh_log_out hA hz hγ t (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR t).1 (hes t))
    (fun t => dh_saving t) (by rw [hk0]; rfl) T
  -- the extraction part is the cake-eating comparison
  have hcake := cake_overtake hβ0 hβ1 hR he hsum
  -- terminal terms
  obtain ⟨P, Q, hPQ⟩ := dh_log_k_bound (ν := ν) hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR
  have hCt : Tendsto (fun t => β ^ t * Real.log (dhOut A z0 γz α ν k e t - k (t + 1))) atTop
      (𝓝 0) := hU.summable.tendsto_atTop_zero
  -- `log c_T ≤ log y_T ≤ log(Az₀) + T log γ_z + ν log R + α log k_T`
  have hterm : ∀ T : ℕ, -(α * Real.log (k T)) ≤ |Real.log (A * z0)| + T * |Real.log γz| +
      ν * |Real.log R| - Real.log (dhOut A z0 γz α ν k e T - k (T + 1)) := by
    intro T
    have hy : 0 < dhOut A z0 γz α ν k e T := by linarith [hc T, hk (T + 1)]
    have h1 : Real.log (dhOut A z0 γz α ν k e T - k (T + 1)) ≤
        Real.log (dhOut A z0 γz α ν k e T) :=
      Real.log_le_log (hc T) (by linarith [hk (T + 1)])
    rw [dh_log_out hA hz hγ T (hk T) (he T)] at h1
    have heR : e T ≤ R := by
      have := hsum (T + 1)
      rw [sum_range_succ] at this
      have : 0 ≤ ∑ t ∈ range T, e t := sum_nonneg fun t _ => (he t).le
      linarith
    have h2 : Real.log (e T) ≤ |Real.log R| :=
      (Real.log_le_log (he T) heR).trans (le_abs_self _)
    have h3 : (T : ℝ) * Real.log γz ≤ T * |Real.log γz| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg T)
    have h4 := mul_le_mul_of_nonneg_left h2 hν
    have h5 := le_abs_self (Real.log (A * z0))
    linarith
  set c1 := |Real.log (A * z0)| with hc1
  set c2 := |Real.log γz| with hc2
  set c3 := ν * |Real.log R| with hc3
  refine sust_hasSum_le_of_partial hU (dh_summable hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR).hasSum
    (ε := fun T => B * ν * (β ^ T / (1 - β)) + B * (β ^ T * (c1 + c3 + c2 * T)) -
      B * (β ^ T * Real.log (dhOut A z0 γz α ν k e T - k (T + 1))) +
      B * α * (β ^ T * (P + Q * T))) ?_ (Eventually.of_forall fun T => ?_)
  · have t1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)).const_mul
      (B * ν)
    have t2 := (lg_tendsto_linear hβ0.le hβ1 (c1 + c3) c2).const_mul B
    have t3 := hCt.const_mul B
    have t4 := (lg_tendsto_linear hβ0.le hβ1 P Q).const_mul (B * α)
    have := ((t1.add t2).sub t3).add t4
    simp only [zero_div, mul_zero, add_zero, sub_zero] at this
    exact this
  · have hc := hcmp T
    have hcT := hcake T
    have ht := hterm T
    have hl := (abs_le.mp (hPQ T)).2
    have hbT : 0 ≤ β ^ T := pow_nonneg hβ0.le T
    -- the energy term
    have hw : ∑ t ∈ range T, β ^ t * ((Real.log (A * z0) + t * Real.log γz + ν * Real.log (e t)) -
        (Real.log (A * z0) + t * Real.log γz + ν * Real.log (cakePath β R t))) =
        ν * (∑ t ∈ range T, β ^ t * Real.log (e t) -
          ∑ t ∈ range T, β ^ t * Real.log (cakePath β R t)) := by
      rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      ring
    rw [hw] at hc
    have hen : ν * (∑ t ∈ range T, β ^ t * Real.log (e t) -
        ∑ t ∈ range T, β ^ t * Real.log (cakePath β R t)) ≤ ν * (β ^ T / (1 - β)) :=
      mul_le_mul_of_nonneg_left (by linarith) hν
    have e1 : α / (1 - α * β) = B * α := by rw [hB]; ring
    rw [e1] at hc
    have k1 := mul_le_mul_of_nonneg_left ht (mul_nonneg hB0 hbT)
    have k2 := mul_le_mul_of_nonneg_left hl (mul_nonneg (mul_nonneg hB0 hα0.le) hbT)
    have k3 := mul_le_mul_of_nonneg_left hen hB0
    nlinarith

/-- AKMM, p. 777: along the optimum the gross growth of output `G_t = y_{t+1}/y_t` satisfies
`G_{t+1} = γ_zβ^ν G_t^α`. -/
theorem dh_growth_rec (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (t : ℕ) :
    dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 2) /
        dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) =
      γz * β ^ ν * (dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t) ^ α := by
  have h1β : 0 < 1 - β := by linarith
  set Ks := dhK A z0 γz α β ν K0 R
  have hy : ∀ s, 0 < dhOut A z0 γz α ν Ks (cakePath β R) s :=
    fun s => (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR s).2.2
  have hk : ∀ s, 0 < Ks s := fun s => (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR s).1
  -- `y_{s+1}/y_s = γ_z β^ν (k_{s+1}/k_s)^α`
  have hstep : ∀ s, dhOut A z0 γz α ν Ks (cakePath β R) (s + 1) /
      dhOut A z0 γz α ν Ks (cakePath β R) s = γz * β ^ ν * (Ks (s + 1) / Ks s) ^ α := by
    intro s
    have he : cakePath β R (s + 1) = β * cakePath β R s := by
      simp only [cakePath, pow_succ]; ring
    have hes : 0 < cakePath β R s := by unfold cakePath; positivity
    unfold dhOut
    rw [he, Real.mul_rpow hβ0.le hes.le, Real.div_rpow (hk (s + 1)).le (hk s).le, pow_succ]
    have := Real.rpow_pos_of_pos (hk s) α
    have := Real.rpow_pos_of_pos hes ν
    field_simp
  -- `k_{s+2}/k_{s+1} = y_{s+1}/y_s`
  have hk2 : Ks (t + 2) / Ks (t + 1) = dhOut A z0 γz α ν Ks (cakePath β R) (t + 1) /
      dhOut A z0 γz α ν Ks (cakePath β R) t := by
    rw [show t + 2 = (t + 1) + 1 from rfl,
      show Ks (t + 1 + 1) = α * β * dhOut A z0 γz α ν Ks (cakePath β R) (t + 1) from
        dh_saving (t + 1),
      show Ks (t + 1) = α * β * dhOut A z0 γz α ν Ks (cakePath β R) t from dh_saving t]
    have := hy t; have := hy (t + 1)
    field_simp
  rw [hstep (t + 1), hk2]

/-- AKMM, p. 777: the balanced growth rate `g = (γ_zβ^ν)^{1/(1−α)}` solves `g = γ_z g^α β^ν`, and
it is the only positive solution. -/
theorem dh_bgp (hγ : 0 < γz) (hβ0 : 0 < β) (hα1 : α < 1) {g : ℝ} (hg : 0 < g) :
    g = γz * g ^ α * β ^ ν ↔ g = (γz * β ^ ν) ^ (1 / (1 - α)) := by
  have h1α : (1 : ℝ) - α ≠ 0 := (by linarith : (0 : ℝ) < 1 - α).ne'
  have hc : 0 < γz * β ^ ν := by positivity
  constructor
  · intro h
    have : g ^ (1 - α) = γz * β ^ ν := by
      rw [Real.rpow_sub hg, Real.rpow_one]
      have hga := Real.rpow_pos_of_pos hg α
      field_simp
      linarith
    rw [← this, ← Real.rpow_mul hg.le, mul_one_div_cancel h1α, Real.rpow_one]
  · intro h
    have hga : g ^ (1 - α) = γz * β ^ ν := by
      rw [h, ← Real.rpow_mul hc.le, one_div_mul_cancel h1α, Real.rpow_one]
    rw [Real.rpow_sub hg, Real.rpow_one] at hga
    have := Real.rpow_pos_of_pos hg α
    field_simp at hga
    linarith

/-- AKMM, p. 777: "long-run gross capital growth `g` is constant if `z` grows at a constant
rate": the growth factor of output converges to `g = (γ_zβ^ν)^{1/(1−α)}` (so does that of
capital, `k_{t+1}/k_t = y_t/y_{t−1}`). -/
theorem dh_growth_tendsto (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    Tendsto (fun t => dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t) atTop
      (𝓝 ((γz * β ^ ν) ^ (1 / (1 - α)))) := by
  set G := fun t => dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t with hG
  have hy := fun s => (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR s).2.2
  have hGpos : ∀ t, 0 < G t := fun t => div_pos (hy (t + 1)) (hy t)
  have hc : 0 < γz * β ^ ν := by positivity
  set lg := Real.log (γz * β ^ ν) / (1 - α) with hlg
  -- `log G_{t+1} − lg = α(log G_t − lg)`
  have hrec : ∀ t, Real.log (G (t + 1)) - lg = α * (Real.log (G t) - lg) := by
    intro t
    have h := dh_growth_rec (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t
    have : G (t + 1) = γz * β ^ ν * G t ^ α := h
    rw [this, Real.log_mul hc.ne' (Real.rpow_pos_of_pos (hGpos t) α).ne',
      Real.log_rpow (hGpos t), hlg]
    have : (1 : ℝ) - α ≠ 0 := (by linarith : (0 : ℝ) < 1 - α).ne'
    field_simp
    ring
  have hgeo : ∀ t, Real.log (G t) - lg = α ^ t * (Real.log (G 0) - lg) := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hrec, ih, pow_succ]; ring
  have hlog : Tendsto (fun t => Real.log (G t)) atTop (𝓝 lg) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).mul_const
      (Real.log (G 0) - lg)).add_const lg
    simp only [zero_mul, zero_add] at this
    exact this.congr fun t => by rw [← hgeo t]; ring
  have hexp := (Real.continuous_exp.tendsto lg).comp hlog
  have hlim : Real.exp lg = (γz * β ^ ν) ^ (1 / (1 - α)) := by
    rw [Real.rpow_def_of_pos hc, hlg]; ring_nf
  rw [← hlim]
  exact hexp.congr fun t => by simp [Real.exp_log (hGpos t)]

/-- AKMM, p. 777: the gross interest rate `1 + r_{t+1} = αy_{t+1}/k_{t+1}` (full depreciation)
equals `G_t/β`, consistent with the Euler equation `c_{t+1}/c_t = β(1 + r_{t+1})` and
`c = (1 − αβ)y`. -/
theorem dh_interest (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (t : ℕ) :
    α * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhK A z0 γz α β ν K0 R (t + 1) =
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t / β := by
  have hy := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t).2.2
  rw [dh_saving]
  field_simp

/-- AKMM, p. 777: `1 + r = (γ_zβ^ν)^{1/(1−α)}/β` in the long run. -/
theorem dh_interest_tendsto (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    Tendsto (fun t => α * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhK A z0 γz α β ν K0 R (t + 1)) atTop (𝓝 ((γz * β ^ ν) ^ (1 / (1 - α)) / β)) := by
  have := (dh_growth_tendsto (ν := ν) hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR).div_const β
  exact this.congr fun t => (dh_interest hA hz hγ hα0 hβ0 hβ1 hK0 hR t).symm

/-- AKMM, p. 777: "the net real interest rate is positive if `g > β`". -/
theorem dh_interest_pos_iff (hβ0 : 0 < β) {g : ℝ} : 1 < g / β ↔ β < g := by
  rw [one_lt_div hβ0]

/-- AKMM, p. 777: the resource price `p_t = νy_t/e_t` grows at the gross interest rate every
period: `p_{t+1}/p_t = αy_{t+1}/k_{t+1} = 1 + r_{t+1}` — the Hotelling rule. -/
theorem dh_hotelling (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (hν : ν ≠ 0) (t : ℕ) :
    (ν * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        cakePath β R (t + 1)) /
      (ν * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t / cakePath β R t) =
      α * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhK A z0 γz α β ν K0 R (t + 1) := by
  rw [dh_interest hA hz hγ hα0 hβ0 hβ1 hK0 hR t]
  have hy := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t).2.2
  have h1β : 0 < 1 - β := by linarith
  have hes : 0 < cakePath β R t := by unfold cakePath; positivity
  have he : cakePath β R (t + 1) = β * cakePath β R t := by
    simp only [cakePath, pow_succ]; ring
  rw [he]
  field_simp

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Strong complementarity: the Leontief resource economy

AKMM, §25.5.3, "Strong complementarity" (p. 779). Output is `y_t = min{Ak_t^α, e_t}`,
`c_t + k_{t+1} = y_t`, `Σ_t e_t ≤ R`, `k₀` given, utility `Σβ^t log c_t`. The book argues,
"without fully solving the model", that `Ak_t^α = e_t` at all dates and that `e` first rises
and then falls.

* **No idle capital** (`leontief_no_idle_capital`): if `Ak_t^α > e_t` at some `t ≥ 1`, lowering
  `k_t` to `(e_t/A)^{1/α}` leaves output unchanged and raises `c_{t−1}`; so an optimal plan has
  `Ak_t^α ≤ e_t` for `t ≥ 1` (`leontief_optimal_no_idle`).
* **No waste** (`leontief_no_waste`): cutting `e_t` to `min{e_t, Ak_t^α}` leaves every `c_t`
  unchanged and uses no more of the resource. So from any optimal plan one obtains an optimal
  plan with `e_t = Ak_t^α` for all `t ≥ 1` (`leontief_optimal_tight`) — the book's claim.
* **At date 0** the claim `e₀ = Ak₀^α` needs `R ≥ Ak₀^α` (the book's "`R₀` was high in
  relation to `Ak₀^α`"); otherwise it is infeasible (`leontief_e0_infeasible`).
* **Eventual decline**: along any feasible plan `e_t → 0`, and every `e_t` is followed by a
  smaller one (`leontief_eventually_declines`).
* **Initial rise, abundant resource**: when the resource constraint does not bind the economy
  is the log/Cobb–Douglas growth model, whose optimal policy is `k_{t+1} = αβk_t^α`
  (Stokey–Lucas, reused from `DeterministicApplications`, with `A = 1`); from `k₀` below the
  steady state, capital and resource use `e_t = k_t^α` rise strictly at every date
  (`leontief_abundant`). The full hump-shaped path for finite `R` is asserted, not derived, in
  the book and is not formalised.
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- AKMM, p. 779: Leontief output `y = min{Ak^α, e}`. -/
noncomputable def leontiefY (A α k e : ℝ) : ℝ := min (A * k ^ α) e

/-- Consumption `c_t = y_t − k_{t+1}`. -/
noncomputable def leontiefC (A α : ℝ) (k e : ℕ → ℝ) (t : ℕ) : ℝ :=
  leontiefY A α (k t) (e t) - k (t + 1)

/-- A feasible plan of the Leontief economy. -/
def LeontiefFeasible (A α R K0 : ℝ) (k e : ℕ → ℝ) : Prop :=
  k 0 = K0 ∧ (∀ t, 0 < k t) ∧ (∀ t, 0 < e t) ∧ (∀ T, ∑ t ∈ range T, e t ≤ R) ∧
    ∀ t, 0 < leontiefC A α k e t

/-- A feasible Leontief plan exists (so `LeontiefFeasible` is not vacuous): extract
`e_t = (1/2)^{t+1}R` and save half of output. -/
theorem leontief_feasible_exists {A α R K0 : ℝ} (hA : 0 < A) (hR : 0 < R) (hK0 : 0 < K0) :
    ∃ k e : ℕ → ℝ, LeontiefFeasible A α R K0 k e := by
  set e : ℕ → ℝ := cakePath (1 / 2) R with he
  have he0 : ∀ t, 0 < e t := fun t => by simp only [he, cakePath]; positivity
  set k : ℕ → ℝ := fun t => Nat.rec (motive := fun _ => ℝ) K0
    (fun n kn => leontiefY A α kn (e n) / 2) t with hk
  have hk1 : ∀ t, k (t + 1) = leontiefY A α (k t) (e t) / 2 := fun t => rfl
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hK0
    | succ n ih =>
      rw [hk1]
      have : 0 < leontiefY A α (k n) (e n) :=
        lt_min (by have := Real.rpow_pos_of_pos ih α; positivity) (he0 n)
      positivity
  refine ⟨k, e, rfl, hkpos, he0, fun T => ?_, fun t => ?_⟩
  · rw [he, cake_partial_sum]
    have : 0 ≤ (1 / 2 : ℝ) ^ T * R := by positivity
    linarith
  · unfold leontiefC
    rw [hk1]
    have : 0 < leontiefY A α (k t) (e t) :=
      lt_min (by have := Real.rpow_pos_of_pos (hkpos t) α; positivity) (he0 t)
    linarith

/-- AKMM, p. 779: lowering idle capital. If `Ak_{s+1}^α > e_{s+1}`, replacing `k_{s+1}` by
`(e_{s+1}/A)^{1/α}` gives a feasible plan whose consumption is unchanged except at `s`, where it
is strictly higher. -/
theorem leontief_no_idle_capital {A α R K0 : ℝ} (hA : 0 < A) (hα : 0 < α) {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) {s : ℕ} (hidle : e (s + 1) < A * k (s + 1) ^ α) :
    LeontiefFeasible A α R K0 (Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))) e ∧
      leontiefC A α k e s <
        leontiefC A α (Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))) e s ∧
      ∀ t ≠ s, leontiefC A α (Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))) e t =
        leontiefC A α k e t := by
  obtain ⟨hk0, hk, he, hsum, hc⟩ := hF
  set v := (e (s + 1) / A) ^ (1 / α) with hv
  set k' := Function.update k (s + 1) v with hk'
  have hv0 : 0 < v := by have := he (s + 1); positivity
  have hvα : A * v ^ α = e (s + 1) := by
    rw [hv, ← Real.rpow_mul (by have := he (s + 1); positivity), one_div_mul_cancel hα.ne',
      Real.rpow_one]
    field_simp
  have hvk : v < k (s + 1) := by
    by_contra h
    rw [not_lt] at h
    have : A * k (s + 1) ^ α ≤ A * v ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hk _).le h hα.le) hA.le
    linarith
  have hy1 : leontiefY A α v (e (s + 1)) = leontiefY A α (k (s + 1)) (e (s + 1)) := by
    unfold leontiefY
    rw [hvα, min_self, min_eq_right hidle.le]
  have hcs : leontiefC A α k' e s = leontiefC A α k e s + (k (s + 1) - v) := by
    unfold leontiefC
    rw [hk', Function.update_of_ne (by omega), Function.update_self]
    ring
  have hrest : ∀ t ≠ s, leontiefC A α k' e t = leontiefC A α k e t := by
    intro t ht
    unfold leontiefC
    by_cases h1 : t = s + 1
    · subst h1
      rw [hk', Function.update_self, Function.update_of_ne (by omega), hy1]
    · rw [hk', Function.update_of_ne h1, Function.update_of_ne (by omega)]
  refine ⟨⟨by rw [hk', Function.update_of_ne (by omega)]; exact hk0, fun t => ?_, he, hsum,
    fun t => ?_⟩, by rw [hcs]; linarith, hrest⟩
  · by_cases h1 : t = s + 1
    · subst h1; rw [hk', Function.update_self]; exact hv0
    · rw [hk', Function.update_of_ne h1]; exact hk t
  · by_cases h1 : t = s
    · subst h1; rw [hcs]; linarith [hc t]
    · rw [hrest t h1]; exact hc t

/-- AKMM, p. 779: "a Leontief function implies that `Ak_t^α = e_t` must hold": an optimal plan
(maximal utility among feasible plans with convergent utility) has no idle capital at dates
`t ≥ 1`: `Ak_t^α ≤ e_t`. -/
theorem leontief_optimal_no_idle {A α β R K0 U : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β)
    {k e : ℕ → ℝ} (hF : LeontiefFeasible A α R K0 k e)
    (hU : HasSum (fun t => β ^ t * Real.log (leontiefC A α k e t)) U)
    (hopt : ∀ k' e' : ℕ → ℝ, LeontiefFeasible A α R K0 k' e' → ∀ U',
      HasSum (fun t => β ^ t * Real.log (leontiefC A α k' e' t)) U' → U' ≤ U) (s : ℕ) :
    A * k (s + 1) ^ α ≤ e (s + 1) := by
  by_contra h
  rw [not_le] at h
  obtain ⟨hF', hlt, hrest⟩ := leontief_no_idle_capital hA hα hF h
  set k' := Function.update k (s + 1) ((e (s + 1) / A) ^ (1 / α))
  set gain := β ^ s * (Real.log (leontiefC A α k' e s) - Real.log (leontiefC A α k e s))
  have hgain : 0 < gain := by
    have := Real.log_lt_log (hF.2.2.2.2 s) hlt
    have : 0 < β ^ s := by positivity
    simp only [gain]; nlinarith
  have hU' : HasSum (fun t => β ^ t * Real.log (leontiefC A α k' e t)) (U + gain) := by
    convert hU.add (hasSum_ite_eq s gain) using 1
    funext t
    by_cases ht : t = s
    · subst ht; simp only [gain, ↓reduceIte]; ring
    · simp only [ht, ↓reduceIte, add_zero, hrest t ht]
  have := hopt k' e hF' _ hU'
  linarith

/-- AKMM, p. 779: wasting the resource never helps: with `e'_t = min{e_t, Ak_t^α}` the plan is
feasible, every `c_t` is unchanged, and no more of the resource is used. -/
theorem leontief_no_waste {A α R K0 : ℝ} (hA : 0 < A) {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) :
    LeontiefFeasible A α R K0 k (fun t => min (e t) (A * k t ^ α)) ∧
      ∀ t, leontiefC A α k (fun t => min (e t) (A * k t ^ α)) t = leontiefC A α k e t := by
  obtain ⟨hk0, hk, he, hsum, hc⟩ := hF
  have hsame : ∀ t, leontiefC A α k (fun t => min (e t) (A * k t ^ α)) t =
      leontiefC A α k e t := by
    intro t
    unfold leontiefC leontiefY
    simp only
    rw [min_comm (e t) (A * k t ^ α), ← min_assoc, min_self]
  refine ⟨⟨hk0, hk, fun t => lt_min (he t) (by have := hk t; positivity), fun T => ?_,
    fun t => by rw [hsame]; exact hc t⟩, hsame⟩
  exact le_trans (sum_le_sum fun t _ => min_le_left _ _) (hsum T)

/-- AKMM, p. 779: an optimal plan can be taken with `Ak_t^α = e_t` at every date `t ≥ 1`: the
waste-free version of an optimal plan is feasible, has the same consumption (hence the same
utility) and uses exactly `e_t = Ak_t^α` for `t ≥ 1`. -/
theorem leontief_optimal_tight {A α β R K0 U : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β)
    {k e : ℕ → ℝ} (hF : LeontiefFeasible A α R K0 k e)
    (hU : HasSum (fun t => β ^ t * Real.log (leontiefC A α k e t)) U)
    (hopt : ∀ k' e' : ℕ → ℝ, LeontiefFeasible A α R K0 k' e' → ∀ U',
      HasSum (fun t => β ^ t * Real.log (leontiefC A α k' e' t)) U' → U' ≤ U) :
    LeontiefFeasible A α R K0 k (fun t => min (e t) (A * k t ^ α)) ∧
      HasSum (fun t => β ^ t * Real.log
        (leontiefC A α k (fun t => min (e t) (A * k t ^ α)) t)) U ∧
      ∀ s, min (e (s + 1)) (A * k (s + 1) ^ α) = A * k (s + 1) ^ α := by
  obtain ⟨hF', hsame⟩ := leontief_no_waste hA hF
  refine ⟨hF', by simpa only [hsame] using hU, fun s => ?_⟩
  exact min_eq_right (leontief_optimal_no_idle hA hα hβ hF hU hopt s)

/-- AKMM, p. 779: "At time 0, this means that `e₀` must be given by `Ak₀^α`" requires
`R ≥ Ak₀^α`: if `R < Ak₀^α`, every feasible plan has `e₀ < Ak₀^α`. -/
theorem leontief_e0_infeasible {A α R K0 : ℝ} {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) (hR : R < A * K0 ^ α) : e 0 < A * k 0 ^ α := by
  obtain ⟨hk0, -, -, hsum, -⟩ := hF
  have := hsum 1
  simp only [range_one, sum_singleton] at this
  rw [hk0]
  linarith

/-- AKMM, p. 779: "eventually, `e` will have to decline": along any feasible plan `e_t → 0`, so
after every date there is a later date with strictly smaller resource use. -/
theorem leontief_eventually_declines {A α R K0 : ℝ} {k e : ℕ → ℝ}
    (hF : LeontiefFeasible A α R K0 k e) :
    Tendsto e atTop (𝓝 0) ∧ ∀ t, ∃ s, t < s ∧ e s < e t := by
  obtain ⟨-, -, he, hsum, -⟩ := hF
  have hs : Summable e := summable_of_sum_range_le (fun t => (he t).le) hsum
  have hlim := hs.tendsto_atTop_zero
  refine ⟨hlim, fun t => ?_⟩
  have h1 : ∀ᶠ s in atTop, e s < e t := hlim.eventually (gt_mem_nhds (he t))
  obtain ⟨s, hs1, hs2⟩ := (h1.and (eventually_gt_atTop t)).exists
  exact ⟨s, hs2, hs1⟩

/-- Below the steady state `k̄ = (αβ)^{1/(1−α)}`, the policy `k ↦ αβk^α` raises capital and
stays below `k̄`. -/
theorem leontief_policy_step {α β k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hab : 0 < α * β)
    (hk : 0 < k) (hkb : k < (α * β) ^ (1 / (1 - α))) :
    k < α * β * k ^ α ∧ α * β * k ^ α < (α * β) ^ (1 / (1 - α)) := by
  have h1α : 0 < 1 - α := by linarith
  set kb := (α * β) ^ (1 / (1 - α)) with hkb'
  have hkb0 : 0 < kb := by positivity
  have hkb1 : kb ^ (1 - α) = α * β := by
    rw [hkb', ← Real.rpow_mul hab.le, one_div_mul_cancel h1α.ne', Real.rpow_one]
  have hka := Real.rpow_pos_of_pos hk α
  constructor
  · have h := Real.rpow_lt_rpow hk.le hkb h1α
    rw [hkb1] at h
    have : k = k ^ (1 - α) * k ^ α := by
      rw [← Real.rpow_add hk]; simp
    calc k = k ^ (1 - α) * k ^ α := this
      _ < α * β * k ^ α := mul_lt_mul_of_pos_right h hka
  · have h := Real.rpow_lt_rpow hk.le hkb hα0
    have : kb = kb ^ (1 - α) * kb ^ α := by
      rw [← Real.rpow_add hkb0]; simp
    calc α * β * k ^ α < α * β * kb ^ α := mul_lt_mul_of_pos_left h hab
      _ = kb := by rw [← hkb1, ← this]

/-- AKMM, p. 779: "the optimal allocation would be to accumulate capital over time, i.e.
`k₀ < k₁ < k₂ …`, so that `e_t = Ak_t^α` is increasing over time" — in the limit of an
abundant resource (`A = 1`), where the economy is the Stokey–Lucas log/Cobb–Douglas model. Its
optimal plan (`DeterministicApplications`: `log_policy_optimal`) is `k_{t+1} = αβk_t^α`, and
from `k₀ < (αβ)^{1/(1−α)}` capital and resource use rise strictly at every date. -/
theorem leontief_abundant {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (k₀ : StokeyLucasPrescott.DeterministicApplications.PosR)
    (hk₀ : k₀.1 < (α * β) ^ (1 / (1 - α))) :
    StokeyLucasPrescott.DeterministicApplications.total
        (StokeyLucasPrescott.DeterministicApplications.logF α) β
        (fun t => (StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t] k₀) =
      StokeyLucasPrescott.DeterministicApplications.vstar
        (StokeyLucasPrescott.DeterministicApplications.logΓ α)
        (StokeyLucasPrescott.DeterministicApplications.logF α) β k₀ ∧
    ∀ t, ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t] k₀).1 <
        ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t + 1] k₀).1 ∧
      ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t] k₀).1 ^ α <
        ((StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0)^[t + 1] k₀).1 ^
          α := by
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set g := StokeyLucasPrescott.DeterministicApplications.logPolicy α β hα0 hβ0
  have hg : ∀ x, (g x).1 = α * β * x.1 ^ α := fun x => rfl
  have hbelow : ∀ t, (g^[t] k₀).1 < (α * β) ^ (1 / (1 - α)) := by
    intro t
    induction t with
    | zero => exact hk₀
    | succ n ih =>
      rw [Function.iterate_succ_apply', hg]
      exact (leontief_policy_step hα0 hα1 hab (g^[n] k₀).2 ih).2
  refine ⟨StokeyLucasPrescott.DeterministicApplications.log_policy_optimal hα0 hα1.le hβ0 hβ1 k₀,
    fun t => ?_⟩
  have hstep : (g^[t] k₀).1 < (g^[t + 1] k₀).1 := by
    rw [Function.iterate_succ_apply', hg]
    exact (leontief_policy_step hα0 hα1 hab (g^[t] k₀).2 (hbelow t)).1
  exact ⟨hstep, Real.rpow_lt_rpow (g^[t] k₀).2.le hstep hα0⟩

end AKMM.Sustainability

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Factor-augmenting technology: measurement and directed choice

AKMM, §25.5.3 (pp. 779–782).

* **The CES production function** (p. 779)
  `y = [(1 − ν)X^θ + ν Z^θ]^{1/θ}`, `X = Ak^αl^{1−α}`, `Z = A_e e`, with `θ = (ε − 1)/ε ≠ 0`
  (`cesY`). Differentiating, the cost shares of a competitive firm are
  `e^{share} = ν(A_e e/y)^θ` (`ces_share_e`) and `l^{share} = (1 − α)(1 − ν)(X/y)^θ`
  (`ces_share_l`).
* **(25.33)–(25.34), corrected**: the technologies are recovered as
  `A_e = (y/e)(e^{share}/ν)^{1/θ}` (`eq_25_34`) and
  `A = y/(k^αl^{1−α}) · (l^{share}/((1 − α)(1 − ν)))^{1/θ}` (`eq_25_33`), with
  `1/θ = ε/(ε − 1)` (`ces_exponent`). The printed formulas omit the CES weights `ν` and
  `1 − ν`; they return `ν^{1/θ}A_e` and `(1 − ν)^{1/θ}A` (`eq_25_34_printed`,
  `eq_25_33_printed`), wrong in level (`eq_25_34_printed_false`) though right in growth rates
  (`eq_25_34_printed_growth`).
* **The technology menu** (p. 782, after Leon-Ledesma and Satchi): with
  `f(A_x x, A_y y) = ((A_x x)^ρ + (A_y y)^ρ)^{1/ρ}`, `ρ < 0` (elasticity below one), and the
  CES frontier `A_x^ω + A_y^ω = 1`, `ω > 0`, the best choice of technology gives the
  reduced form `(x^{ρ'} + y^{ρ'})^{1/ρ'}` with `ρ' = ρω/(ω − ρ)` (`menu_reduced_le`,
  `menu_reduced_attained`): a CES whose elasticity `1/(1 − ρ')` exceeds the short-run elasticity
  `1/(1 − ρ)` and stays below one (`menu_elasticity`). The book states the result for a CES
  frontier without specifying the exponent; `ω > 0` (a frontier bowed out) is the hypothesis
  under which it holds as stated.
-/

namespace AKMM.Sustainability

open Real

/-- AKMM, p. 779: the CES production function `[(1 − ν)X^θ + νZ^θ]^{1/θ}`, `θ = (ε − 1)/ε`. -/
noncomputable def cesY (ν θ X Z : ℝ) : ℝ := ((1 - ν) * X ^ θ + ν * Z ^ θ) ^ (1 / θ)

/-- AKMM, p. 780: the exponent of (25.33)–(25.34): `1/θ = ε/(ε − 1)` for `θ = (ε − 1)/ε`. -/
theorem ces_exponent (ε : ℝ) : 1 / ((ε - 1) / ε) = ε / (ε - 1) := by
  rw [one_div_div]

/-- `y^θ = (1 − ν)X^θ + νZ^θ`. -/
theorem cesY_rpow {ν θ X Z : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X) (hZ : 0 < Z)
    (hθ : θ ≠ 0) : cesY ν θ X Z ^ θ = (1 - ν) * X ^ θ + ν * Z ^ θ := by
  have h1 : 0 < 1 - ν := by linarith
  unfold cesY
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ, Real.rpow_one]

/-- AKMM, p. 780: the energy cost share of a competitive firm, `e·(∂y/∂e)/y = ν(A_e e/y)^θ`,
from the derivative of `y` in `e`. -/
theorem ces_share_e {ν θ X Ae e : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X) (hAe : 0 < Ae)
    (he : 0 < e) (hθ : θ ≠ 0) :
    ∃ d, HasDerivAt (fun e => cesY ν θ X (Ae * e)) d e ∧
      e * d / cesY ν θ X (Ae * e) = ν * (Ae * e / cesY ν θ X (Ae * e)) ^ θ := by
  have h1 : 0 < 1 - ν := by linarith
  set S := (1 - ν) * X ^ θ + ν * (Ae * e) ^ θ with hS
  have hSpos : 0 < S := by positivity
  have hin : HasDerivAt (fun e => (1 - ν) * X ^ θ + ν * (Ae ^ θ * e ^ θ))
      (ν * (Ae ^ θ * (θ * e ^ (θ - 1)))) e :=
    (((Real.hasDerivAt_rpow_const (Or.inl he.ne')).const_mul (Ae ^ θ)).const_mul ν).const_add _
  have hfun : (fun e => (1 - ν) * X ^ θ + ν * (Ae ^ θ * e ^ θ)) =ᶠ[nhds e]
      fun e => (1 - ν) * X ^ θ + ν * (Ae * e) ^ θ := by
    filter_upwards [lt_mem_nhds he] with x hx
    rw [Real.mul_rpow hAe.le hx.le]
  have hout := (hin.congr_of_eventuallyEq hfun.symm).rpow_const (p := 1 / θ)
    (Or.inl hSpos.ne')
  refine ⟨_, hout, ?_⟩
  have hy' : cesY ν θ X (Ae * e) = S ^ (1 / θ) := rfl
  have hy0 : 0 < S ^ (1 / θ) := Real.rpow_pos_of_pos hSpos _
  have hyθ : (S ^ (1 / θ)) ^ θ = S := by
    rw [← Real.rpow_mul hSpos.le, one_div_mul_cancel hθ, Real.rpow_one]
  rw [hy', Real.div_rpow (by positivity) hy0.le, hyθ, ← hS, Real.rpow_sub_one hSpos.ne',
    Real.rpow_sub_one he.ne', Real.mul_rpow hAe.le he.le]
  field_simp

/-- AKMM, p. 780: the labour cost share, `l·(∂y/∂l)/y = (1 − α)(1 − ν)(X/y)^θ` with
`X = Ak^αl^{1−α}`. -/
theorem ces_share_l {ν θ α A k Z l : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A)
    (hk : 0 < k) (hZ : 0 < Z) (hl : 0 < l) (hθ : θ ≠ 0) :
    ∃ d, HasDerivAt (fun l => cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) d l ∧
      l * d / cesY ν θ (A * k ^ α * l ^ (1 - α)) Z =
        (1 - α) * (1 - ν) * (A * k ^ α * l ^ (1 - α) / cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^
          θ := by
  have h1 : 0 < 1 - ν := by linarith
  have hka := Real.rpow_pos_of_pos hk α
  set c := (A * k ^ α) ^ θ with hc
  have hc0 : 0 < c := by positivity
  set X := A * k ^ α * l ^ (1 - α) with hX
  have hXpos : 0 < X := by have := Real.rpow_pos_of_pos hl (1 - α); positivity
  set S := (1 - ν) * X ^ θ + ν * Z ^ θ with hS
  have hSpos : 0 < S := by positivity
  have hXθ : ∀ x : ℝ, 0 < x → (A * k ^ α * x ^ (1 - α)) ^ θ = c * x ^ ((1 - α) * θ) := by
    intro x hx
    have := Real.rpow_pos_of_pos hx (1 - α)
    rw [Real.mul_rpow (by positivity) this.le, ← Real.rpow_mul hx.le]
  have hin : HasDerivAt (fun x => (1 - ν) * (c * x ^ ((1 - α) * θ)) + ν * Z ^ θ)
      ((1 - ν) * (c * ((1 - α) * θ * l ^ ((1 - α) * θ - 1)))) l :=
    (((Real.hasDerivAt_rpow_const (Or.inl hl.ne')).const_mul c).const_mul (1 - ν)).add_const _
  have hfun : (fun x => (1 - ν) * (c * x ^ ((1 - α) * θ)) + ν * Z ^ θ) =ᶠ[nhds l]
      fun x => (1 - ν) * (A * k ^ α * x ^ (1 - α)) ^ θ + ν * Z ^ θ := by
    filter_upwards [lt_mem_nhds hl] with x hx
    rw [hXθ x hx]
  have hS' : (1 - ν) * (A * k ^ α * l ^ (1 - α)) ^ θ + ν * Z ^ θ = S := rfl
  have hout := (hin.congr_of_eventuallyEq hfun.symm).rpow_const (p := 1 / θ)
    (Or.inl (by rw [hS']; exact hSpos.ne'))
  refine ⟨_, hout, ?_⟩
  have hy : cesY ν θ X Z = S ^ (1 / θ) := rfl
  rw [hy, Real.div_rpow hXpos.le (by positivity), ← Real.rpow_mul hSpos.le,
    one_div_mul_cancel hθ, Real.rpow_one, hS']
  have hSθ : S ^ (1 / θ - 1) = S ^ (1 / θ) / S := by rw [Real.rpow_sub_one hSpos.ne']
  have hlθ : l ^ ((1 - α) * θ - 1) = l ^ ((1 - α) * θ) / l := by
    rw [Real.rpow_sub_one hl.ne']
  rw [hSθ, hlθ, hX, hXθ l hl]
  have := Real.rpow_pos_of_pos hSpos (1 / θ)
  field_simp

/-- AKMM, (25.34) corrected, p. 780: from the energy share, `A_e = (y/e)(e^{share}/ν)^{1/θ}`. -/
theorem eq_25_34 {ν θ X Ae e : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X) (hAe : 0 < Ae)
    (he : 0 < e) (hθ : θ ≠ 0) {sh : ℝ}
    (hsh : sh = ν * (Ae * e / cesY ν θ X (Ae * e)) ^ θ) :
    Ae = cesY ν θ X (Ae * e) / e * (sh / ν) ^ (1 / θ) := by
  have h1 : 0 < 1 - ν := by linarith
  have hy : 0 < cesY ν θ X (Ae * e) := by unfold cesY; positivity
  rw [hsh, mul_div_cancel_left₀ _ hν0.ne', ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, (25.33) corrected, p. 780: from the labour share,
`A = y/(k^αl^{1−α}) · (l^{share}/((1 − α)(1 − ν)))^{1/θ}`. -/
theorem eq_25_33 {ν θ α A k Z l : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hα1 : α < 1) (hA : 0 < A)
    (hk : 0 < k) (hZ : 0 < Z) (hl : 0 < l) (hθ : θ ≠ 0) {sh : ℝ}
    (hsh : sh = (1 - α) * (1 - ν) *
      (A * k ^ α * l ^ (1 - α) / cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ) :
    A = cesY ν θ (A * k ^ α * l ^ (1 - α)) Z / (k ^ α * l ^ (1 - α)) *
      (sh / ((1 - α) * (1 - ν))) ^ (1 / θ) := by
  have h1 : 0 < 1 - ν := by linarith
  have h2 : 0 < 1 - α := by linarith
  have hka := Real.rpow_pos_of_pos hk α
  have hla := Real.rpow_pos_of_pos hl (1 - α)
  have hy : 0 < cesY ν θ (A * k ^ α * l ^ (1 - α)) Z := by unfold cesY; positivity
  rw [hsh, mul_div_cancel_left₀ _ (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, (25.34) as printed, p. 780: `(y/e)(e^{share})^{1/θ}` equals `ν^{1/θ}A_e`. -/
theorem eq_25_34_printed {ν θ X Ae e : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X)
    (hAe : 0 < Ae) (he : 0 < e) (hθ : θ ≠ 0) :
    cesY ν θ X (Ae * e) / e * (ν * (Ae * e / cesY ν θ X (Ae * e)) ^ θ) ^ (1 / θ) =
      ν ^ (1 / θ) * Ae := by
  have h1 : 0 < 1 - ν := by linarith
  have hy : 0 < cesY ν θ X (Ae * e) := by unfold cesY; positivity
  rw [Real.mul_rpow hν0.le (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, (25.33) as printed, p. 780: `y/(k^αl^{1−α}) · (l^{share}/(1 − α))^{1/θ}` equals
`(1 − ν)^{1/θ}A`. -/
theorem eq_25_33_printed {ν θ α A k Z l : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hα1 : α < 1)
    (hA : 0 < A) (hk : 0 < k) (hZ : 0 < Z) (hl : 0 < l) (hθ : θ ≠ 0) :
    cesY ν θ (A * k ^ α * l ^ (1 - α)) Z / (k ^ α * l ^ (1 - α)) *
      ((1 - α) * (1 - ν) * (A * k ^ α * l ^ (1 - α) /
        cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ / (1 - α)) ^ (1 / θ) =
      (1 - ν) ^ (1 / θ) * A := by
  have h1 : 0 < 1 - ν := by linarith
  have h2 : 0 < 1 - α := by linarith
  have hka := Real.rpow_pos_of_pos hk α
  have hla := Real.rpow_pos_of_pos hl (1 - α)
  have hy : 0 < cesY ν θ (A * k ^ α * l ^ (1 - α)) Z := by unfold cesY; positivity
  have hsimp : (1 - α) * (1 - ν) * (A * k ^ α * l ^ (1 - α) /
      cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ / (1 - α) = (1 - ν) * (A * k ^ α * l ^ (1 - α) /
      cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ := by field_simp
  rw [hsimp, Real.mul_rpow h1.le (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, p. 780: the printed (25.34) is wrong in levels: with `ε = 2` (`θ = 1/2`) and
`ν = 1/4` it returns `A_e/16`. -/
theorem eq_25_34_printed_false {X Ae e : ℝ} (hX : 0 < X) (hAe : 0 < Ae) (he : 0 < e) :
    cesY (1 / 4) (1 / 2) X (Ae * e) / e *
        ((1 / 4) * (Ae * e / cesY (1 / 4) (1 / 2) X (Ae * e)) ^ (1 / 2 : ℝ)) ^ (1 / (1 / 2) : ℝ) ≠
      Ae := by
  rw [eq_25_34_printed (by norm_num) (by norm_num) hX hAe he (by norm_num)]
  have : (1 / 4 : ℝ) ^ (1 / (1 / 2) : ℝ) = 1 / 16 := by
    rw [show (1 / (1 / 2) : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]; norm_num
  rw [this]
  intro h
  linarith

/-- AKMM, p. 780: the printed formulas are off by constant factors, so they give the right
growth rates: the ratio of the printed `A_e` at two dates is the ratio of the true ones. -/
theorem eq_25_34_printed_growth {ν θ : ℝ} (hν0 : 0 < ν) {a b : ℝ} (hb : 0 < b) :
    ν ^ (1 / θ) * a / (ν ^ (1 / θ) * b) = a / b := by
  have := Real.rpow_pos_of_pos hν0 (1 / θ)
  field_simp

/-- The key inequality of the technology menu: for `q < 0`, `a, b > 0` with `a + b = 1` and
`c, d > 0`, `a^q c + b^q d ≥ (c^r + d^r)^{1−q}` with `r = 1/(1 − q)`, with equality at
`a = c^r/(c^r + d^r)`. -/
theorem menu_key {q a b c d : ℝ} (hq : q < 0) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hc : 0 < c) (hd : 0 < d) :
    (c ^ (1 / (1 - q)) + d ^ (1 / (1 - q))) ^ (1 - q) ≤ a ^ q * c + b ^ q * d := by
  have h1q : 0 < 1 - q := by linarith
  set r := 1 / (1 - q) with hr
  set S := c ^ r + d ^ r with hS
  have hcr := Real.rpow_pos_of_pos hc r
  have hdr := Real.rpow_pos_of_pos hd r
  have hS0 : 0 < S := by positivity
  set a0 := c ^ r / S
  set b0 := d ^ r / S
  have ha0 : 0 < a0 := div_pos hcr hS0
  have hb0 : 0 < b0 := div_pos hdr hS0
  have hab0 : a0 + b0 = 1 := by
    simp only [a0, b0]; rw [← add_div, ← hS, div_self hS0.ne']
  -- `c a0^{q−1} = S^{1−q}` since `r(q − 1) = −1`
  have hrq : r * (q - 1) = -1 := by rw [hr]; field_simp; ring
  have hrq' : r * q + 1 = r := by rw [hr]; field_simp; ring
  have key : ∀ x, 0 < x → x * (x ^ r / S) ^ (q - 1) = S ^ (1 - q) := by
    intro x hx
    have hxr := Real.rpow_pos_of_pos hx r
    rw [Real.div_rpow hxr.le hS0.le, ← Real.rpow_mul hx.le, hrq, Real.rpow_neg_one,
      show (1 : ℝ) - q = -(q - 1) by ring, Real.rpow_neg hS0.le]
    field_simp
  have val : ∀ x, 0 < x → (x ^ r / S) ^ q * x = x ^ r * S ^ (-q) := by
    intro x hx
    have hxr := Real.rpow_pos_of_pos hx r
    rw [Real.div_rpow hxr.le hS0.le, ← Real.rpow_mul hx.le, Real.rpow_neg hS0.le]
    have : x ^ (r * q) * x = x ^ r := by
      rw [← Real.rpow_add_one hx.ne', hrq']
    field_simp
    linarith [this]
  have t1 := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow hq.le ha ha0
  have t2 := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow hq.le hb hb0
  have k1 := mul_le_mul_of_nonneg_right t1 hc.le
  have k2 := mul_le_mul_of_nonneg_right t2 hd.le
  have e1 : (a0 ^ q + q * a0 ^ (q - 1) * (a - a0)) * c =
      a0 ^ q * c + q * S ^ (1 - q) * (a - a0) := by rw [← key c hc]; ring
  have e2 : (b0 ^ q + q * b0 ^ (q - 1) * (b - b0)) * d =
      b0 ^ q * d + q * S ^ (1 - q) * (b - b0) := by rw [← key d hd]; ring
  have e3 : a0 ^ q * c + b0 ^ q * d = S ^ (1 - q) := by
    rw [val c hc, val d hd, show (1 - q) = 1 + -q by ring, Real.rpow_add hS0, Real.rpow_one]
    ring
  have hlin : q * S ^ (1 - q) * (a - a0) + q * S ^ (1 - q) * (b - b0) = 0 := by
    have : a - a0 + (b - b0) = 0 := by linarith
    linear_combination (q * S ^ (1 - q)) * this
  nlinarith [k1, k2, e1, e2, e3, hlin]

/-- AKMM, p. 782, the technology menu (Leon-Ledesma–Satchi): for `ρ < 0 < ω`, every technology
on the frontier `A_x^ω + A_y^ω = 1` gives output at most the reduced-form CES
`(x^{ρ'} + y^{ρ'})^{1/ρ'}`, `ρ' = ρω/(ω − ρ)`. -/
theorem menu_reduced_le {ρ ω x y Ax Ay : ℝ} (hρ : ρ < 0) (hω : 0 < ω) (hx : 0 < x) (hy : 0 < y)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hfr : Ax ^ ω + Ay ^ ω = 1) :
    ((Ax * x) ^ ρ + (Ay * y) ^ ρ) ^ (1 / ρ) ≤
      (x ^ (ρ * ω / (ω - ρ)) + y ^ (ρ * ω / (ω - ρ))) ^ (1 / (ρ * ω / (ω - ρ))) := by
  have hωρ : 0 < ω - ρ := by linarith
  set q := ρ / ω with hq
  have hq0 : q < 0 := div_neg_of_neg_of_pos hρ hω
  have hr : 1 / (1 - q) = ω / (ω - ρ) := by rw [hq]; field_simp
  have hcr : ∀ z : ℝ, 0 < z → (z ^ ρ) ^ (1 / (1 - q)) = z ^ (ρ * ω / (ω - ρ)) := by
    intro z hz
    rw [← Real.rpow_mul hz.le, hr]; ring_nf
  have hpow : ∀ A z : ℝ, 0 < A → 0 < z → (A * z) ^ ρ = (A ^ ω) ^ q * z ^ ρ := by
    intro A z hA hz
    rw [Real.mul_rpow hA.le hz.le, ← Real.rpow_mul hA.le, hq]
    congr 2
    field_simp
  have hk := menu_key hq0 (Real.rpow_pos_of_pos hAx ω) (Real.rpow_pos_of_pos hAy ω) hfr
    (Real.rpow_pos_of_pos hx ρ) (Real.rpow_pos_of_pos hy ρ)
  rw [hcr x hx, hcr y hy] at hk
  rw [hpow Ax x hAx hx, hpow Ay y hAy hy]
  set S := x ^ (ρ * ω / (ω - ρ)) + y ^ (ρ * ω / (ω - ρ)) with hS
  have hS0 : 0 < S := by positivity
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) hk (by
    have : 1 / ρ < 0 := one_div_neg.mpr hρ
    linarith)
  rw [← Real.rpow_mul hS0.le] at h2
  have : (1 - q) * (1 / ρ) = 1 / (ρ * ω / (ω - ρ)) := by
    rw [hq]; field_simp
  rw [this] at h2
  exact h2

/-- AKMM, p. 782: the reduced form is attained by the technology
`A_x^ω = x^{ρ'}/(x^{ρ'} + y^{ρ'})`, `A_y^ω = y^{ρ'}/(x^{ρ'} + y^{ρ'})` on the frontier. -/
theorem menu_reduced_attained {ρ ω x y : ℝ} (hρ : ρ < 0) (hω : 0 < ω) (hx : 0 < x)
    (hy : 0 < y) :
    ∃ Ax Ay : ℝ, 0 < Ax ∧ 0 < Ay ∧ Ax ^ ω + Ay ^ ω = 1 ∧
      ((Ax * x) ^ ρ + (Ay * y) ^ ρ) ^ (1 / ρ) =
        (x ^ (ρ * ω / (ω - ρ)) + y ^ (ρ * ω / (ω - ρ))) ^ (1 / (ρ * ω / (ω - ρ))) := by
  have hωρ : 0 < ω - ρ := by linarith
  set ρ' := ρ * ω / (ω - ρ) with hρ'
  set S := x ^ ρ' + y ^ ρ' with hS
  have hxr := Real.rpow_pos_of_pos hx ρ'
  have hyr := Real.rpow_pos_of_pos hy ρ'
  have hS0 : 0 < S := by positivity
  set a0 := x ^ ρ' / S
  set b0 := y ^ ρ' / S
  have ha0 : 0 < a0 := div_pos hxr hS0
  have hb0 : 0 < b0 := div_pos hyr hS0
  refine ⟨a0 ^ (1 / ω), b0 ^ (1 / ω), by positivity, by positivity, ?_, ?_⟩
  · rw [← Real.rpow_mul ha0.le, ← Real.rpow_mul hb0.le, one_div_mul_cancel hω.ne',
      Real.rpow_one, Real.rpow_one]
    simp only [a0, b0]; rw [← add_div, ← hS, div_self hS0.ne']
  · -- `(a0^{1/ω} x)^ρ = a0^{ρ/ω} x^ρ = x^{ρ'} S^{−ρ/ω}`
    have hterm : ∀ z, 0 < z → ((z ^ ρ' / S) ^ (1 / ω) * z) ^ ρ =
        z ^ ρ' * S ^ (-(ρ / ω)) := by
      intro z hz
      have hzr := Real.rpow_pos_of_pos hz ρ'
      have e : ρ' * (ρ / ω) + ρ = ρ' := by rw [hρ']; field_simp; ring
      have hzz : z ^ (ρ' * (ρ / ω)) * z ^ ρ = z ^ ρ' := by rw [← Real.rpow_add hz, e]
      calc ((z ^ ρ' / S) ^ (1 / ω) * z) ^ ρ = (z ^ ρ' / S) ^ (ρ / ω) * z ^ ρ := by
            rw [Real.mul_rpow (by positivity) hz.le, ← Real.rpow_mul (by positivity)]
            congr 2; ring
        _ = z ^ (ρ' * (ρ / ω)) / S ^ (ρ / ω) * z ^ ρ := by
            rw [Real.div_rpow hzr.le hS0.le, ← Real.rpow_mul hz.le]
        _ = (z ^ (ρ' * (ρ / ω)) * z ^ ρ) * S ^ (-(ρ / ω)) := by
            rw [Real.rpow_neg hS0.le]; ring
        _ = z ^ ρ' * S ^ (-(ρ / ω)) := by rw [hzz]
    rw [hterm x hx, hterm y hy, ← add_mul, ← hS, ← Real.rpow_one_add' hS0.le (by
      rw [show 1 + -(ρ / ω) = (ω - ρ) / ω by field_simp; ring]
      exact (div_pos hωρ hω).ne'), ← Real.rpow_mul hS0.le]
    congr 1
    rw [hρ']
    field_simp
    ring

/-- AKMM, p. 782: "a ‘reduced-form’ production function ... with a higher elasticity of
substitution": for `ρ < 0 < ω`, `ρ < ρ' = ρω/(ω − ρ) < 0`, so the long-run elasticity
`1/(1 − ρ')` exceeds the short-run one `1/(1 − ρ)` and is below one. -/
theorem menu_elasticity {ρ ω : ℝ} (hρ : ρ < 0) (hω : 0 < ω) :
    ρ < ρ * ω / (ω - ρ) ∧ ρ * ω / (ω - ρ) < 0 ∧
      1 / (1 - ρ) < 1 / (1 - ρ * ω / (ω - ρ)) ∧ 1 / (1 - ρ * ω / (ω - ρ)) < 1 := by
  have hωρ : 0 < ω - ρ := by linarith
  have h1 : ρ < ρ * ω / (ω - ρ) := by
    rw [lt_div_iff₀ hωρ]; nlinarith
  have h2 : ρ * ω / (ω - ρ) < 0 := div_neg_of_neg_of_pos (by nlinarith) hωρ
  refine ⟨h1, h2, ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]; linarith

end AKMM.Sustainability

set_option linter.style.longLine false
#print axioms AKMM.Sustainability.sust_log_le_tangent
#print axioms AKMM.Sustainability.sust_log_lt_tangent
#print axioms AKMM.Sustainability.sust_tangent_le_rpow
#print axioms AKMM.Sustainability.sust_tangent_lt_rpow
#print axioms AKMM.Sustainability.sust_rpow_lt_tangent
#print axioms AKMM.Sustainability.climateT
#print axioms AKMM.Sustainability.eq_25_1
#print axioms AKMM.Sustainability.eq_25_1_unique
#print axioms AKMM.Sustainability.eq_25_1_tendsto
#print axioms AKMM.Sustainability.eq_25_1_steady
#print axioms AKMM.Sustainability.forcing
#print axioms AKMM.Sustainability.steadyTemp
#print axioms AKMM.Sustainability.eq_25_3
#print axioms AKMM.Sustainability.climate_ecs_doubling
#print axioms AKMM.Sustainability.climate_ecs
#print axioms AKMM.Sustainability.twoBoxStep
#print axioms AKMM.Sustainability.eq_25_4_steady_iff
#print axioms AKMM.Sustainability.climate_dev_tendsto
#print axioms AKMM.Sustainability.climate_twoBox_tendsto
#print axioms AKMM.Sustainability.twoBoxMatrix
#print axioms AKMM.Sustainability.climate_twoBox_isStable
#print axioms AKMM.Sustainability.CarbonFlows
#print axioms AKMM.Sustainability.CarbonFlows.mk
#print axioms AKMM.Sustainability.CarbonFlows.f12
#print axioms AKMM.Sustainability.CarbonFlows.f21
#print axioms AKMM.Sustainability.CarbonFlows.f23
#print axioms AKMM.Sustainability.CarbonFlows.f32
#print axioms AKMM.Sustainability.carbonLin
#print axioms AKMM.Sustainability.carbonStep
#print axioms AKMM.Sustainability.carbonStepPrinted
#print axioms AKMM.Sustainability.carbonTotal
#print axioms AKMM.Sustainability.eq_25_6_total
#print axioms AKMM.Sustainability.eq_25_6_printed_total
#print axioms AKMM.Sustainability.eq_25_6_printed_false
#print axioms AKMM.Sustainability.carbonMatrix
#print axioms AKMM.Sustainability.carbon_isMarkov
#print axioms AKMM.Sustainability.carbonMatrix_mulVec
#print axioms AKMM.Sustainability.carbon_exists_invariant
#print axioms AKMM.Sustainability.carbon_invariant_iff
#print axioms AKMM.Sustainability.carbon_invariant_unique
#print axioms AKMM.Sustainability.carbonPath
#print axioms AKMM.Sustainability.carbonPulse
#print axioms AKMM.Sustainability.carbonResponse
#print axioms AKMM.Sustainability.carbon_superposition
#print axioms AKMM.Sustainability.ghktKernel
#print axioms AKMM.Sustainability.eq_25_10_tendsto
#print axioms AKMM.Sustainability.ghktKernel_mem_Icc
#print axioms AKMM.Sustainability.ghktKernel_antitone
#print axioms AKMM.Sustainability.eq_25_10_within_period
#print axioms AKMM.Sustainability.eq_25_10_within_period_printed_false
#print axioms AKMM.Sustainability.ghktKernel_hasSum
#print axioms AKMM.Sustainability.excessCarbon
#print axioms AKMM.Sustainability.eq_25_9
#print axioms AKMM.Sustainability.excessCarbon_pulse
#print axioms AKMM.Sustainability.nordhausD
#print axioms AKMM.Sustainability.nordhausD_eq
#print axioms AKMM.Sustainability.nordhausD_approx
#print axioms AKMM.Sustainability.nordhausD_coefficient
#print axioms AKMM.Sustainability.nordhausD_tendsto
#print axioms AKMM.Sustainability.nordhausD_convexOn
#print axioms AKMM.Sustainability.nordhausD_not_convexOn
#print axioms AKMM.Sustainability.adaptCost
#print axioms AKMM.Sustainability.adaptation_optimal
#print axioms AKMM.Sustainability.adaptation_unique
#print axioms AKMM.Sustainability.adaptation_low_T
#print axioms AKMM.Sustainability.staticE
#print axioms AKMM.Sustainability.staticE_pos
#print axioms AKMM.Sustainability.eq_25_16
#print axioms AKMM.Sustainability.static_mp_strictAnti
#print axioms AKMM.Sustainability.static_lt_staticE_iff
#print axioms AKMM.Sustainability.staticE_strictAnti
#print axioms AKMM.Sustainability.static_firm_optimal
#print axioms AKMM.Sustainability.staticW
#print axioms AKMM.Sustainability.eq_25_18_exists
#print axioms AKMM.Sustainability.eq_25_17
#print axioms AKMM.Sustainability.eq_25_17_unique
#print axioms AKMM.Sustainability.static_laissez_faire_excess
#print axioms AKMM.Sustainability.static_pigou
#print axioms AKMM.Sustainability.staticPrivate
#print axioms AKMM.Sustainability.static_private_max
#print axioms AKMM.Sustainability.static_private_hasDerivAt
#print axioms AKMM.Sustainability.static_private_deriv_zero
#print axioms AKMM.Sustainability.CapEquilibrium
#print axioms AKMM.Sustainability.static_cap_nonbinding
#print axioms AKMM.Sustainability.static_cap_binding
#print axioms AKMM.Sustainability.eq_25_19
#print axioms AKMM.Sustainability.static_cap_exists
#print axioms AKMM.Sustainability.staticW2
#print axioms AKMM.Sustainability.static_two_optimal
#print axioms AKMM.Sustainability.static_two_unique
#print axioms AKMM.Sustainability.staticE_continuousOn
#print axioms AKMM.Sustainability.static_two_exists
#print axioms AKMM.Sustainability.static_two_pigou
#print axioms AKMM.Sustainability.static_two_cap
#print axioms AKMM.Sustainability.energyAgg
#print axioms AKMM.Sustainability.energyD
#print axioms AKMM.Sustainability.energyPrice
#print axioms AKMM.Sustainability.energyDemand
#print axioms AKMM.Sustainability.energyDemand_pos
#print axioms AKMM.Sustainability.energy_term
#print axioms AKMM.Sustainability.eq_25_27_index
#print axioms AKMM.Sustainability.eq_25_27_cost
#print axioms AKMM.Sustainability.eq_25_27_foc
#print axioms AKMM.Sustainability.eq_25_26_least_cost
#print axioms AKMM.Sustainability.eq_25_28
#print axioms AKMM.Sustainability.eq_25_29_saving
#print axioms AKMM.Sustainability.eq_25_29_saving_printed_false
#print axioms AKMM.Sustainability.eq_25_29_printed_false
#print axioms AKMM.Sustainability.savingNext
#print axioms AKMM.Sustainability.saving_const
#print axioms AKMM.Sustainability.saving_fixed_iff
#print axioms AKMM.Sustainability.saving_above
#print axioms AKMM.Sustainability.saving_above_tendsto
#print axioms AKMM.Sustainability.saving_below
#print axioms AKMM.Sustainability.saving_above_tvc
#print axioms AKMM.Sustainability.eq_25_A_ratio
#print axioms AKMM.Sustainability.eq_25_A_normalize
#print axioms AKMM.Sustainability.sust_hasSum_le_of_partial
#print axioms AKMM.Sustainability.cakePath
#print axioms AKMM.Sustainability.cake_partial_sum
#print axioms AKMM.Sustainability.cake_hasSum
#print axioms AKMM.Sustainability.cake_policy
#print axioms AKMM.Sustainability.cake_decreasing
#print axioms AKMM.Sustainability.cake_utility_hasSum
#print axioms AKMM.Sustainability.cake_overtake
#print axioms AKMM.Sustainability.cake_optimal
#print axioms AKMM.Sustainability.cake_unique
#print axioms AKMM.Sustainability.cake_slp
#print axioms AKMM.Sustainability.hotelling_price_max
#print axioms AKMM.Sustainability.hotelling_price_const
#print axioms AKMM.Sustainability.cake_market_foc
#print axioms AKMM.Sustainability.cake_market_equilibrium
#print axioms AKMM.Sustainability.hotelling_rent_pos
#print axioms AKMM.Sustainability.hotelling_rule
#print axioms AKMM.Sustainability.hotelling_cost_indifference
#print axioms AKMM.Sustainability.hotelling_cost_rule
#print axioms AKMM.Sustainability.oil_owner_overtake
#print axioms AKMM.Sustainability.oil_owner_optimal
#print axioms AKMM.Sustainability.lgPhi
#print axioms AKMM.Sustainability.lg_phi_le
#print axioms AKMM.Sustainability.lg_identity
#print axioms AKMM.Sustainability.lg_compare
#print axioms AKMM.Sustainability.lg_linear_bound
#print axioms AKMM.Sustainability.lg_tendsto_linear
#print axioms AKMM.Sustainability.lg_summable_linear
#print axioms AKMM.Sustainability.GHKT
#print axioms AKMM.Sustainability.GHKT.mk
#print axioms AKMM.Sustainability.GHKT.α
#print axioms AKMM.Sustainability.GHKT.β
#print axioms AKMM.Sustainability.GHKT.γ
#print axioms AKMM.Sustainability.GHKT.k
#print axioms AKMM.Sustainability.GHKT.z
#print axioms AKMM.Sustainability.GHKT.Sbar
#print axioms AKMM.Sustainability.GHKT.g
#print axioms AKMM.Sustainability.GHKT.m
#print axioms AKMM.Sustainability.GHKT.X
#print axioms AKMM.Sustainability.GHKT.K0
#print axioms AKMM.Sustainability.GHKTAssumptions
#print axioms AKMM.Sustainability.GHKTAssumptions.mk
#print axioms AKMM.Sustainability.GHKTAssumptions.α_pos
#print axioms AKMM.Sustainability.GHKTAssumptions.α_lt
#print axioms AKMM.Sustainability.GHKTAssumptions.β_pos
#print axioms AKMM.Sustainability.GHKTAssumptions.β_lt
#print axioms AKMM.Sustainability.GHKTAssumptions.γ_nonneg
#print axioms AKMM.Sustainability.GHKTAssumptions.k_nonneg
#print axioms AKMM.Sustainability.GHKTAssumptions.k_le
#print axioms AKMM.Sustainability.GHKTAssumptions.z_bdd
#print axioms AKMM.Sustainability.GHKTAssumptions.Sbar_nonneg
#print axioms AKMM.Sustainability.GHKTAssumptions.Sbar_bdd
#print axioms AKMM.Sustainability.GHKTAssumptions.m_nonneg
#print axioms AKMM.Sustainability.GHKTAssumptions.m_bdd
#print axioms AKMM.Sustainability.GHKTAssumptions.g_bdd
#print axioms AKMM.Sustainability.GHKTAssumptions.K0_pos
#print axioms AKMM.Sustainability.GHKT.Psi
#print axioms AKMM.Sustainability.GHKT.PsiN
#print axioms AKMM.Sustainability.GHKT.carbon
#print axioms AKMM.Sustainability.GHKT.output
#print axioms AKMM.Sustainability.GHKT.cons
#print axioms AKMM.Sustainability.GHKT.Feasible
#print axioms AKMM.Sustainability.GHKT.optK
#print axioms AKMM.Sustainability.ghkt_opt_saving
#print axioms AKMM.Sustainability.ghkt_opt_cons
#print axioms AKMM.Sustainability.ghkt_log_output
#print axioms AKMM.Sustainability.ghkt_opt_feasible
#print axioms AKMM.Sustainability.ghkt_psi
#print axioms AKMM.Sustainability.ghkt_sum_interchange
#print axioms AKMM.Sustainability.ghkt_overtake
#print axioms AKMM.Sustainability.ghkt_opt_summable
#print axioms AKMM.Sustainability.ghkt_optimal
#print axioms AKMM.Sustainability.eq_25_31
#print axioms AKMM.Sustainability.ghkt_tax_of_proportional
#print axioms AKMM.Sustainability.eq_25_32
#print axioms AKMM.Sustainability.eq_25_32_ghkt
#print axioms AKMM.Sustainability.coalEconomy
#print axioms AKMM.Sustainability.ghkt_coal_assumptions
#print axioms AKMM.Sustainability.ghkt_coal_opt
#print axioms AKMM.Sustainability.ghkt_coal_pigou
#print axioms AKMM.Sustainability.ghkt_coal_optimal
#print axioms AKMM.Sustainability.dhOut
#print axioms AKMM.Sustainability.dhK
#print axioms AKMM.Sustainability.dh_saving
#print axioms AKMM.Sustainability.dh_log_out
#print axioms AKMM.Sustainability.dh_feasible
#print axioms AKMM.Sustainability.dh_log_cake
#print axioms AKMM.Sustainability.dh_log_k_bound
#print axioms AKMM.Sustainability.dh_summable
#print axioms AKMM.Sustainability.dh_optimal
#print axioms AKMM.Sustainability.dh_growth_rec
#print axioms AKMM.Sustainability.dh_bgp
#print axioms AKMM.Sustainability.dh_growth_tendsto
#print axioms AKMM.Sustainability.dh_interest
#print axioms AKMM.Sustainability.dh_interest_tendsto
#print axioms AKMM.Sustainability.dh_interest_pos_iff
#print axioms AKMM.Sustainability.dh_hotelling
#print axioms AKMM.Sustainability.leontiefY
#print axioms AKMM.Sustainability.leontiefC
#print axioms AKMM.Sustainability.LeontiefFeasible
#print axioms AKMM.Sustainability.leontief_feasible_exists
#print axioms AKMM.Sustainability.leontief_no_idle_capital
#print axioms AKMM.Sustainability.leontief_optimal_no_idle
#print axioms AKMM.Sustainability.leontief_no_waste
#print axioms AKMM.Sustainability.leontief_optimal_tight
#print axioms AKMM.Sustainability.leontief_e0_infeasible
#print axioms AKMM.Sustainability.leontief_eventually_declines
#print axioms AKMM.Sustainability.leontief_policy_step
#print axioms AKMM.Sustainability.leontief_abundant
#print axioms AKMM.Sustainability.cesY
#print axioms AKMM.Sustainability.ces_exponent
#print axioms AKMM.Sustainability.cesY_rpow
#print axioms AKMM.Sustainability.ces_share_e
#print axioms AKMM.Sustainability.ces_share_l
#print axioms AKMM.Sustainability.eq_25_34
#print axioms AKMM.Sustainability.eq_25_33
#print axioms AKMM.Sustainability.eq_25_34_printed
#print axioms AKMM.Sustainability.eq_25_33_printed
#print axioms AKMM.Sustainability.eq_25_34_printed_false
#print axioms AKMM.Sustainability.eq_25_34_printed_growth
#print axioms AKMM.Sustainability.menu_key
#print axioms AKMM.Sustainability.menu_reduced_le
#print axioms AKMM.Sustainability.menu_reduced_attained
#print axioms AKMM.Sustainability.menu_elasticity
