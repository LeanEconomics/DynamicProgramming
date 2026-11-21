import BasicNewKeynesianModel.PriceDuration
import BasicNewKeynesianModel.CES
import NewKeynesian.NKHouseholds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import BasicNewKeynesianModel.PriceDispersion
import NewKeynesian.NKEquilibrium
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import DiscretionCommitment.LossAndCostPush
import MonetaryPolicyDesign.Welfare
import BasicNewKeynesianModel.Expectations
import BasicNewKeynesianModel.TaylorRuleSystem
import MonetaryPolicyDesign.OptimalPolicy
import MonetaryPolicyDesign.Ex4_6
import DiscretionCommitment.CommitmentVsDiscretion
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import StickyWagesPrices.WageInflation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The expected time between price changes

AKMM, §18.2, p. 534. Suppose a price changes with probability `1 − θ` each month,
independently of its history. The book writes the expected time between price adjustments as
`∑_{t ≥ 1} (1 − θ) θᵗ t = θ/(1 − θ)`.

The sum is computed correctly (`dur_printed_sum`), but its weights `(1 − θ) θᵗ` (`t ≥ 1`) add up
to `θ`, not to one (`dur_printed_weights_sum`), so it is not an expectation unless `θ = 1`. The
duration of a price (the number of months until the next change, counting the current one) is
`t ≥ 1` with probability `(1 − θ) θ^{t−1}`; its mean is `1/(1 − θ)` (`dur_mean`, from Galí's
`mean_duration`). The printed value `θ/(1 − θ)` is the expected number of months *without* a
change before the change, one less than the duration (`dur_printed_eq_mean_sub_one`), and it
differs from the mean duration (`dur_printed_ne_mean`).
-/

namespace AKMM.NominalFrictions

open Gali.BasicNewKeynesianModel

/-- AKMM, p. 534: the printed weights `(1 − θ)θᵗ`, `t ≥ 1`, sum to `θ` (not to one) for
`θ ∈ [0, 1)`. -/
theorem dur_printed_weights_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (1 - θ) * θ ^ (t + 1) = θ := by
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  simp_rw [pow_succ, ← mul_assoc, mul_comm _ θ]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp

/-- AKMM, p. 534: the printed weights do not form a probability distribution on `t ≥ 1`. -/
theorem dur_printed_weights_ne_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (1 - θ) * θ ^ (t + 1) ≠ 1 := by
  rw [dur_printed_weights_sum h0 h1]; exact ne_of_lt h1

/-- AKMM, p. 534: the printed sum itself is correct,
`∑_{t ≥ 1} (1 − θ) θᵗ t = θ/(1 − θ)` (indexing from `t = 0`, where the term vanishes). -/
theorem dur_printed_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (1 - θ) * θ ^ t * (t : ℝ) = θ / (1 - θ) := by
  have hn : ‖θ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  have hs : ∀ t : ℕ, (1 - θ) * θ ^ t * (t : ℝ) = (1 - θ) * ((t : ℝ) * θ ^ t) := by
    intro t; ring
  simp_rw [hs]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hn]
  field_simp

/-- AKMM, p. 534 (corrected): with reset probability `1 − θ`, a price lasts `t + 1 ≥ 1`
periods with probability `(1 − θ)θᵗ`; these probabilities sum to one (Galí's
`survival_sum`). -/
theorem dur_pmf_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : ∑' t, durationProb θ t = 1 :=
  survival_sum h0 h1

/-- AKMM, p. 534 (corrected): the expected duration of a price is `1/(1 − θ)` (Galí's
`mean_duration`). -/
theorem dur_mean {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, ((t : ℝ) + 1) * durationProb θ t = 1 / (1 - θ) :=
  mean_duration h0 h1

/-- AKMM, p. 534: the printed value `θ/(1 − θ)` is the expected number of periods without a
change, `∑ₜ t (1 − θ) θᵗ`, one less than the mean duration `1/(1 − θ)`. -/
theorem dur_printed_eq_mean_sub_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (t : ℝ) * durationProb θ t = θ / (1 - θ) ∧ θ / (1 - θ) = 1 / (1 - θ) - 1 := by
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  refine ⟨?_, by field_simp; ring⟩
  rw [← dur_printed_sum h0 h1]
  congr 1
  funext t
  unfold durationProb
  ring

/-- AKMM, p. 534: the printed value is not the mean duration. -/
theorem dur_printed_ne_mean {θ : ℝ} (h1 : θ < 1) : θ / (1 - θ) ≠ 1 / (1 - θ) := by
  have h : (0 : ℝ) < 1 - θ := by linarith
  intro he
  rw [div_left_inj' h.ne'] at he
  linarith

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian environment and the household's problem

AKMM, §18.3, pp. 536–539: preferences (18.1), the CES final-goods technology (18.2), the
intermediate technology (18.3), the demand curve (18.4), the price index, the real budget
constraint, and the household's first-order conditions (18.5)–(18.6).

* `env_ces`: on the book's continuum `[0, 1]`, every input bundle producing `Y` costs at least
  `P · Y`; it costs exactly `P · Y` iff it is the demand schedule (18.4); the schedule produces
  `Y` and costs `P Y` (Galí's `unitInterval_expenditure_minimisation`). Hence the cost function
  is `Y ↦ P Y` and `P` is its derivative (footnote 4, `env_cost_deriv`).
* `env_demand_elasticity`: the price elasticity of (18.4) is `−ε`.
* `env_marginal_cost`, `env_profit`: with `y = Aℓ` the real marginal cost is `w/A` and real
  profit is `(p − w/A) p^{−ε} Y`.
* `env_real_budget`, `env_relprice_law`: the budget constraint in real terms and the law
  `p_{t+1} = p_t/(1 + π_{t+1})` for a firm that does not reset.
* `env_labour_foc`, `eq_18_6`: the intratemporal condition `C^{−σ} w = L^ψ` as the first-order
  condition of the labour choice.
* `env_euler_foc`, `eq_18_5`: under perfect foresight, the Euler equation (18.5) as the
  first-order condition of shifting saving by one bond; `eq_18_5_stochastic`: the conditional
  form from the bond first-order condition (Miao's `eq_19_3`).
-/

namespace AKMM.NominalFrictions

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-- AKMM, (18.1), p. 536: period utility `C^{1−σ}/(1 − σ) − L^{1+ψ}/(1 + ψ)`. -/
noncomputable def nfU (σ ψ C L : ℝ) : ℝ := C ^ (1 - σ) / (1 - σ) - L ^ (1 + ψ) / (1 + ψ)

/-- AKMM, (18.2)–(18.4) and p. 537, on the book's continuum `j ∈ [0, 1]`: with positive
intermediate prices `P_j`, (i) every bundle `y_j ≥ 0` costs at least `P · Y`, `Y` the CES
aggregate (18.2) and `P = (∫ P_j^{1−ε})^{1/(1−ε)}`; (ii) it costs exactly `P · Y` iff
`y_j = (P_j/P)^{−ε} Y` (18.4) almost everywhere; (iii) the schedule (18.4) produces `Y`;
(iv) it costs `P Y`. From Galí's `unitInterval_expenditure_minimisation`. -/
theorem env_ces {ε : ℝ} (hε : 1 < ε) {Pj : ℝ → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : IntegrableOn (fun j => Pj j ^ (1 - ε)) (Set.Icc 0 1)) {y : ℝ → ℝ}
    (hy : ∀ j, 0 ≤ y j) (hPy : IntegrableOn (fun j => Pj j * y j) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * cesAgg (volume.restrict (Set.Icc 0 1)) ε y
        ≤ ∫ j in Set.Icc 0 1, Pj j * y j ∧
      (∫ j in Set.Icc 0 1, Pj j * y j
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε y ↔
        ∀ᵐ j ∂(volume.restrict (Set.Icc 0 1)),
          y j = demand (volume.restrict (Set.Icc 0 1)) ε Pj
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε y) j) ∧
      (∀ Y : ℝ, 0 ≤ Y → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Pj Y) = Y) ∧
      ∀ Y : ℝ, ∫ j in Set.Icc 0 1, Pj j * demand (volume.restrict (Set.Icc 0 1)) ε Pj Y j
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Y :=
  unitInterval_expenditure_minimisation hε hP hPi hy hPy

/-- AKMM, p. 537 and footnote 4: by `env_ces` the least cost of producing `Y ≥ 0` is `P Y`
(attained by the demand schedule, and no bundle producing `Y` costs less), so the cost function
is `Y ↦ P Y`; `P` is its derivative with respect to the quantity produced. -/
theorem env_cost_deriv {ε : ℝ} (hε : 1 < ε) {Pj : ℝ → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : IntegrableOn (fun j => Pj j ^ (1 - ε)) (Set.Icc 0 1)) {Y : ℝ} (hY : 0 ≤ Y) :
    (∀ y : ℝ → ℝ, (∀ j, 0 ≤ y j) → IntegrableOn (fun j => Pj j * y j) (Set.Icc 0 1) →
        cesAgg (volume.restrict (Set.Icc 0 1)) ε y = Y →
        priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Y ≤ ∫ j in Set.Icc 0 1, Pj j * y j) ∧
      cesAgg (volume.restrict (Set.Icc 0 1)) ε (demand (volume.restrict (Set.Icc 0 1)) ε Pj Y)
        = Y ∧
      ∫ j in Set.Icc 0 1, Pj j * demand (volume.restrict (Set.Icc 0 1)) ε Pj Y j
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Y ∧
      HasDerivAt (fun Z => priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Z)
        (priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj) Y := by
  refine ⟨fun y hy hPy hYy => ?_, (env_ces hε hP hPi (fun _ => le_refl 0)
    (by simp)).2.2.1 Y hY, (env_ces hε hP hPi (fun _ => le_refl 0) (by simp)).2.2.2 Y, ?_⟩
  · have h := (env_ces hε hP hPi hy hPy).1
    rwa [hYy] at h
  · simpa using (hasDerivAt_id Y).const_mul (priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj)

/-- AKMM, (18.4), p. 537: "the price elasticity of the demand facing an intermediate goods
producer is `ε`": `y(p) = (p/P)^{−ε} Y` has `y'(p) · p / y(p) = −ε`. -/
theorem env_demand_elasticity {ε P Y p : ℝ} (hP : 0 < P) (hY : 0 < Y) (hp : 0 < p) :
    HasDerivAt (fun q => (q / P) ^ (-ε) * Y) (-ε * (p / P) ^ (-ε - 1) * (1 / P) * Y) p ∧
      -ε * (p / P) ^ (-ε - 1) * (1 / P) * Y * p / ((p / P) ^ (-ε) * Y) = -ε := by
  have hq : 0 < p / P := div_pos hp hP
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun q => q / P) (1 / P) p := by
      simpa using (hasDerivAt_id p).div_const P
    have h2 := (h1.rpow_const (p := -ε) (Or.inl hq.ne')).mul_const Y
    convert h2 using 1
    ring
  · have h3 : (p / P) ^ (-ε) = (p / P) ^ (-ε - 1) * (p / P) := by
      rw [← Real.rpow_add_one hq.ne']; ring_nf
    have h4 : 0 < (p / P) ^ (-ε - 1) := Real.rpow_pos_of_pos hq _
    rw [h3]
    field_simp

/-- AKMM, (18.3), p. 536: with `y = Aℓ` the real cost of producing `y` is `w y/A`, so the real
marginal cost is `w/A`, common across firms. -/
theorem env_marginal_cost {w A y : ℝ} : HasDerivAt (fun z => w * (z / A)) (w / A) y := by
  have h := (hasDerivAt_id y).const_mul (w / A)
  simp only [id, mul_one] at h
  convert h using 1
  funext z
  ring

/-- AKMM, p. 539: real profits `m = p y − w ℓ = (p − w/A) y = (p − w/A) p^{−ε} Y`, using
(18.3) for `ℓ` and (18.4) (relative price `p`) for `y`. -/
theorem env_profit {ε p w A Y y ℓ : ℝ} (hA : A ≠ 0) (h3 : y = A * ℓ) (h4 : y = p ^ (-ε) * Y) :
    p * y - w * ℓ = (p - w / A) * y ∧ p * y - w * ℓ = (p - w / A) * p ^ (-ε) * Y := by
  have hl : ℓ = y / A := by rw [h3]; field_simp
  refine ⟨by rw [hl]; field_simp, ?_⟩
  rw [hl, h4]; field_simp

/-- AKMM, p. 538: the budget constraint `B_{t+1} + P_t C_t = P_t w_t L_t + (1 + i_{t−1}) B_t +
P_t m_t` in real terms: with `b_t = B_t/P_{t−1}` and `1 + π_t = P_t/P_{t−1}`,
`b_{t+1} + C_t = w_t L_t + (1 + i_{t−1})/(1 + π_t) b_t + m_t`. -/
theorem env_real_budget {Bn B P Pm C w L i m : ℝ} (hP : 0 < P) (hPm : 0 < Pm) :
    Bn + P * C = P * w * L + (1 + i) * B + P * m ↔
      Bn / P + C = w * L + (1 + i) / (P / Pm) * (B / Pm) + m := by
  have e : (1 + i) / (P / Pm) * (B / Pm) = (1 + i) * B / P := by field_simp
  rw [e]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- AKMM, p. 538: a firm that does not reset its nominal price `P_j` has relative price
`p_{t+1} = P_j/P_{t+1} = p_t/(1 + π_{t+1})`, with `1 + π_{t+1} = P_{t+1}/P_t`. -/
theorem env_relprice_law {Pj P Pn : ℝ} (hP : 0 < P) (hPn : 0 < Pn) :
    Pj / Pn = (Pj / P) / (Pn / P) := by
  field_simp

/-- AKMM, p. 538: the marginal value of labour. Working `L` more hours at real wage `w` with
consumption `C₀ + wL`, the derivative of `nfU σ ψ (C₀ + w L) L` in `L` is
`(C₀ + wL)^{−σ} w − L^ψ`. -/
theorem env_labour_foc {σ ψ C₀ w L : ℝ} (hσ : σ ≠ 1) (hψ : 0 < ψ) (hC : 0 < C₀ + w * L)
    (hL : 0 < L) :
    HasDerivAt (fun l => nfU σ ψ (C₀ + w * l) l) ((C₀ + w * L) ^ (-σ) * w - L ^ ψ) L := by
  have h1 : HasDerivAt (fun l => C₀ + w * l) w L := by
    simpa using ((hasDerivAt_id L).const_mul w).const_add C₀
  have hc := (Miao.NewKeynesian.nk_hasDerivAt_pow_div hσ hC).comp L h1
  have hψ1 : (1 : ℝ) + ψ ≠ 0 := by linarith
  have hl := (Real.hasDerivAt_rpow_const (p := 1 + ψ) (Or.inl hL.ne')).div_const (1 + ψ)
  have e : (1 + ψ) * L ^ (1 + ψ - 1) / (1 + ψ) = L ^ ψ := by
    rw [show 1 + ψ - 1 = ψ by ring]; field_simp
  rw [e] at hl
  exact hc.sub hl

/-- AKMM, (18.6), p. 538: the intratemporal labour-supply condition `C^{−σ} w = L^ψ` is the
first-order condition of the labour choice (`env_labour_foc`). -/
theorem eq_18_6 {σ ψ C₀ w L : ℝ} (hσ : σ ≠ 1) (hψ : 0 < ψ) (hC : 0 < C₀ + w * L) (hL : 0 < L) :
    HasDerivAt (fun l => nfU σ ψ (C₀ + w * l) l) 0 L ↔ (C₀ + w * L) ^ (-σ) * w = L ^ ψ := by
  constructor
  · intro h
    have := (env_labour_foc hσ hψ hC hL).unique h
    linarith
  · intro h
    have := env_labour_foc hσ hψ hC hL
    rwa [h, sub_self] at this

/-- AKMM, p. 538: the marginal value of saving. Buying `b` more real bonds at `t` lowers
`C_t` by `b` and raises `C_{t+1}` by `R b`, `R = (1 + i_t)/(1 + π_{t+1})`; the derivative of
`u(C_t − b) + β u(C_{t+1} + R b)` at `b = 0` is `−C_t^{−σ} + β R C_{t+1}^{−σ}`. -/
theorem env_euler_foc {σ β R C₀ C₁ L₀ L₁ ψ : ℝ} (hσ : σ ≠ 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    HasDerivAt (fun b => nfU σ ψ (C₀ - b) L₀ + β * nfU σ ψ (C₁ + R * b) L₁)
      (-C₀ ^ (-σ) + β * (R * C₁ ^ (-σ))) 0 := by
  have h0 : HasDerivAt (fun b : ℝ => C₀ - b) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub C₀
  have h1 : HasDerivAt (fun b : ℝ => C₁ + R * b) R 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add C₁
  have hu0 := Miao.NewKeynesian.nk_hasDerivAt_pow_div hσ (by simpa using hC₀ : 0 < C₀ - 0)
  have hu1 := Miao.NewKeynesian.nk_hasDerivAt_pow_div hσ (by simpa using hC₁ : 0 < C₁ + R * 0)
  have hA := ((hu0.comp 0 h0).sub_const (L₀ ^ (1 + ψ) / (1 + ψ)))
  have hB := (((hu1.comp 0 h1).sub_const (L₁ ^ (1 + ψ) / (1 + ψ))).const_mul β)
  have h := hA.add hB
  simp only [sub_zero, mul_zero, add_zero] at h
  convert h using 1
  · funext b
    simp only [nfU, Function.comp_apply, Pi.add_apply]
  · ring

/-- AKMM, (18.5), p. 538 (perfect foresight): saving is optimal at the margin iff
`C_t^{−σ} = β (1 + i_t)/(1 + π_{t+1}) C_{t+1}^{−σ}` (`env_euler_foc`). -/
theorem eq_18_5 {σ β i π' C₀ C₁ L₀ L₁ ψ : ℝ} (hσ : σ ≠ 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    HasDerivAt (fun b => nfU σ ψ (C₀ - b) L₀ + β * nfU σ ψ (C₁ + (1 + i) / (1 + π') * b) L₁)
        0 0 ↔ C₀ ^ (-σ) = β * ((1 + i) / (1 + π') * C₁ ^ (-σ)) := by
  have h := env_euler_foc (R := (1 + i) / (1 + π')) (L₀ := L₀) (L₁ := L₁) (ψ := ψ) (β := β)
    hσ hC₀ hC₁
  constructor
  · intro h0
    have := h.unique h0
    linarith
  · intro he
    rwa [he, neg_add_cancel] at h

/-- AKMM, (18.5), p. 538 (under uncertainty): from the bond first-order condition
`C_t^{−σ}/(P_t(1 + i_t)) = E_t[β C_{t+1}^{−σ}/P_{t+1}]`, the Euler equation holds in the form
`1 = β(1 + i_t) E_t[(C_{t+1}/C_t)^{−σ} P_t/P_{t+1}]`, i.e. (18.5) with
`P_t/P_{t+1} = 1/(1 + π_{t+1})` (Miao's `eq_19_3`, `E_t = μ[·|ℱ_t]`). -/
theorem eq_18_5_stochastic {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : MeasurableSpace Ω} {β σ : ℝ} {C P i : ℕ → Ω → ℝ} (t : ℕ) (hC : ∀ s ω, 0 < C s ω)
    (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hB : (fun ω => C t ω ^ (-σ) / (P t ω * (1 + i t ω))) =ᵐ[μ]
      μ[fun ω => β * C (t + 1) ω ^ (-σ) / P (t + 1) ω | ℱ])
    (hmeas : StronglyMeasurable[ℱ] (fun ω => C t ω ^ σ * P t ω))
    (hint1 : Integrable (fun ω => C (t + 1) ω ^ (-σ) / P (t + 1) ω) μ)
    (hint2 : Integrable (fun ω => (C (t + 1) ω / C t ω) ^ (-σ) * (P t ω / P (t + 1) ω)) μ) :
    (fun _ => (1 : ℝ)) =ᵐ[μ] fun ω => β * (1 + i t ω) *
      μ[fun ω => (C (t + 1) ω / C t ω) ^ (-σ) * (P t ω / P (t + 1) ω) | ℱ] ω :=
  Miao.NewKeynesian.eq_19_3 (mΩ := mΩ) (μ := μ) (β := β) (Λ := fun s ω => C s ω ^ (-σ)) t hC hP hi
    (fun _ _ => rfl) hB hmeas hint1 hint2

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The reset price: the firm's Bellman equation, the first-order condition and (18.7)

AKMM, §18.3, pp. 539–540, and Appendix 18.A.1, p. 871. A firm with relative price `p` earns
`u′(C)(p − w/A) p^{−ε} Y` this period; if it cannot reset next period (probability `θ`) its
relative price becomes `p/(1 + π′)`. The envelope condition of the Bellman equation is
(App. 18.A.1)

  `V_p(p, S) = u′(C) Y [p^{−ε} − ε p^{−ε−1}(p − w/A)] + βθ E[V_p(p/(1 + π′), S′)/(1 + π′)]`,

and the reset price solves `V_p(p^R, S) = 0`. We work along a perfect-foresight aggregate path
(dates `n`, `λₙ = u′(Cₙ)Yₙ`, `mₙ = wₙ/Aₙ`, gross inflation `Πₙ = 1 + πₙ`).

* `rp_bracket_deriv`: the bracket is the derivative of `(q − m) q^{−ε}`.
* `rp_iterate`, `rp_series`: iterating the envelope condition `K` times, and in the limit,
  `V_p(p) = ∑_k (βθ)^k λ_{n+k} G_k [·](p G_k)` with `G_k = P_n/P_{n+k}`
  (`rpDefl`), provided the remainder vanishes; `rp_series_envelope`: the series solves the
  envelope condition.
* `rp_term_eq`, `rp_foc_rearranged`, `eq_18_7`: the first-order condition rearranges to
  `p^R ∑ (βθ)^k λ (P_{n+k}/P_n)^{ε−1} = μ ∑ (βθ)^k λ (P_{n+k}/P_n)^ε m`, so `p^R = p^N/p^D`
  with `p^N = μ m λ + θβ (1 + π′)^ε p^N′` and `p^D = λ + θβ (1 + π′)^{ε−1} p^D′`
  (`rp_pN_rec`, `rp_pD_rec`).

**Correction.** The book's combined condition omits the factor `G_k = ∏(1 + π_s)^{−1}` that the
envelope condition produces at each step (the derivative of `p_{t,τ}` with respect to `p^R_t`),
so its rearranged form carries `(P_τ/P_t)^ε` and `(P_τ/P_t)^{1+ε}`, and the recursions (18.7)
carry `(1 + π)^{1+ε}` and `(1 + π)^ε`. The correct exponents are `ε` and `ε − 1`. On a
constant-inflation path the two reset prices coincide iff inflation is zero
(`rp_constant_correct`, `rp_constant_printed`, `rp_printed_ne_iff`); the log-linearisation
(18.A.1) is unaffected, because both conditions agree to first order around zero inflation.
-/

namespace AKMM.NominalFrictions

open Filter Topology Finset

/-- AKMM, p. 539: the bracket `p^{−ε} − ε p^{−ε−1}(p − m)`, the marginal profit per unit of
demand. -/
noncomputable def rpBracket (ε m q : ℝ) : ℝ := q ^ (-ε) - ε * q ^ (-ε - 1) * (q - m)

/-- AKMM, p. 539: the cumulative deflator `G_k = P_n/P_{n+k} = ∏_{s=n+1}^{n+k} (1 + π_s)^{−1}`
along a path of gross inflation rates `Π`. -/
noncomputable def rpDefl (Pi : ℕ → ℝ) (n k : ℕ) : ℝ := ∏ j ∈ range k, (Pi (n + 1 + j))⁻¹

/-- AKMM, App. 18.A.1, p. 871: the `k`-th term of the iterated envelope condition,
`(βθ)^k λ_{n+k} G_k [·](p G_k)`. -/
noncomputable def rpTerm (β θ ε : ℝ) (lam mc Pi : ℕ → ℝ) (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (β * θ) ^ k * lam (n + k) * rpDefl Pi n k * rpBracket ε (mc (n + k)) (p * rpDefl Pi n k)

/-- AKMM, App. 18.A.1, p. 871: the envelope condition of the firm's Bellman equation along a
perfect-foresight path, for a family `Vp n p` of marginal values. -/
def RPEnvelope (β θ ε : ℝ) (lam mc Pi : ℕ → ℝ) (Vp : ℕ → ℝ → ℝ) : Prop :=
  ∀ n p, Vp n p = lam n * rpBracket ε (mc n) p + β * θ * (Vp (n + 1) (p / Pi (n + 1)) / Pi (n + 1))

/-- AKMM, p. 539: the bracket is the derivative of the per-unit-demand profit
`(q − m) q^{−ε}` at `q > 0`. -/
theorem rp_bracket_deriv {ε m q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z => (z - m) * z ^ (-ε)) (rpBracket ε m q) q := by
  have h1 : HasDerivAt (fun z : ℝ => z - m) 1 q := by simpa using (hasDerivAt_id q).sub_const m
  have h2 := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl hq.ne')
  have h := h1.mul h2
  convert h using 1
  unfold rpBracket
  ring

/-- `G_0 = 1`. -/
theorem rp_defl_zero (Pi : ℕ → ℝ) (n : ℕ) : rpDefl Pi n 0 = 1 := by simp [rpDefl]

/-- `G_{k+1} = G_k/(1 + π_{n+1+k})`. -/
theorem rp_defl_succ (Pi : ℕ → ℝ) (n k : ℕ) :
    rpDefl Pi n (k + 1) = rpDefl Pi n k / Pi (n + 1 + k) := by
  rw [rpDefl, rpDefl, prod_range_succ, div_eq_mul_inv]

/-- `G^{(n)}_{k+1} = G^{(n+1)}_k/(1 + π_{n+1})`. -/
theorem rp_defl_succ' (Pi : ℕ → ℝ) (n k : ℕ) :
    rpDefl Pi n (k + 1) = rpDefl Pi (n + 1) k / Pi (n + 1) := by
  rw [rpDefl, prod_range_succ', rpDefl, div_eq_mul_inv]
  simp only [add_zero]
  congr 1
  refine prod_congr rfl fun _ _ => ?_
  congr 2
  ring

/-- `G_k > 0` when inflation factors are positive. -/
theorem rp_defl_pos {Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s) (n k : ℕ) : 0 < rpDefl Pi n k :=
  prod_pos fun _ _ => inv_pos.2 (hPi _)

/-- **AKMM, App. 18.A.1, p. 871**: iterating the envelope condition `K` times,
`V_p(n, p) = ∑_{k<K} (βθ)^k λ_{n+k} G_k [·](p G_k) + (βθ)^K G_K V_p(n + K, p G_K)`. -/
theorem rp_iterate {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} {Vp : ℕ → ℝ → ℝ}
    (hV : RPEnvelope β θ ε lam mc Pi Vp) (n : ℕ) (p : ℝ) (K : ℕ) :
    Vp n p = ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k +
      (β * θ) ^ K * rpDefl Pi n K * Vp (n + K) (p * rpDefl Pi n K) := by
  induction K with
  | zero => simp [rp_defl_zero]
  | succ K ih =>
    rw [ih, hV (n + K) (p * rpDefl Pi n K), sum_range_succ, rp_defl_succ]
    have e1 : n + K + 1 = n + (K + 1) := by ring
    have e2 : n + 1 + K = n + K + 1 := by ring
    rw [e2, e1, add_assoc]
    congr 1
    unfold rpTerm
    rw [mul_div_assoc]
    ring

/-- **AKMM, App. 18.A.1, p. 871**: if the remainder `(βθ)^K G_K V_p(n + K, p G_K)` vanishes
(e.g. bounded marginal values with `βθ G_k` bounded below one), the envelope condition gives
`V_p(n, p) = ∑_{k ≥ 0} (βθ)^k λ_{n+k} G_k [·](p G_k)` as the limit of partial sums. -/
theorem rp_series {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} {Vp : ℕ → ℝ → ℝ}
    (hV : RPEnvelope β θ ε lam mc Pi Vp) (n : ℕ) (p : ℝ)
    (hrem : Tendsto (fun K => (β * θ) ^ K * rpDefl Pi n K * Vp (n + K) (p * rpDefl Pi n K))
      atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop (𝓝 (Vp n p)) := by
  have h : ∀ K, ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k = Vp n p -
      (β * θ) ^ K * rpDefl Pi n K * Vp (n + K) (p * rpDefl Pi n K) := by
    intro K; rw [rp_iterate hV n p K]; ring
  simp_rw [h]
  simpa using (tendsto_const_nhds (x := Vp n p)).sub hrem

/-- AKMM, App. 18.A.1, p. 871: the first `k + 1` terms from date `n` are the date-`n` term and
`βθ/(1 + π_{n+1})` times the terms from date `n + 1` at the price `p/(1 + π_{n+1})`. -/
theorem rp_term_succ {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} (n : ℕ) (p : ℝ) (k : ℕ) :
    rpTerm β θ ε lam mc Pi n p (k + 1) =
      β * θ * (rpTerm β θ ε lam mc Pi (n + 1) (p / Pi (n + 1)) k / Pi (n + 1)) := by
  unfold rpTerm
  rw [rp_defl_succ']
  have e : n + (k + 1) = n + 1 + k := by ring
  rw [e, pow_succ]
  have e2 : p * (rpDefl Pi (n + 1) k / Pi (n + 1)) = p / Pi (n + 1) * rpDefl Pi (n + 1) k := by
    ring
  rw [e2]
  ring

/-- AKMM, App. 18.A.1, p. 871: the series `∑_k (βθ)^k λ G_k [·](p G_k)` (when summable at
every date and price) solves the envelope condition, so `RPEnvelope` has this concrete
instance. -/
theorem rp_series_envelope {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ}
    (hs : ∀ n p, Summable (rpTerm β θ ε lam mc Pi n p)) :
    RPEnvelope β θ ε lam mc Pi (fun n p => ∑' k, rpTerm β θ ε lam mc Pi n p k) := by
  intro n p
  dsimp only
  rw [(hs n p).tsum_eq_zero_add]
  simp_rw [rp_term_succ]
  rw [tsum_mul_left, tsum_div_const]
  unfold rpTerm
  simp [rp_defl_zero]

/-- AKMM, pp. 539–540 (termwise rearrangement): with `μ = ε/(ε − 1)`,
`(βθ)^k λ G [·](p G) = (1 − ε) p^{−ε−1}(p · (βθ)^k λ G^{1−ε} − μ (βθ)^k λ m G^{−ε})`,
where `G^{1−ε} = (P_{n+k}/P_n)^{ε−1}` and `G^{−ε} = (P_{n+k}/P_n)^ε`. -/
theorem rp_term_eq {β θ ε : ℝ} (hε : 1 < ε) {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s)
    (n : ℕ) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    rpTerm β θ ε lam mc Pi n p k = (1 - ε) * p ^ (-ε - 1) *
      (p * ((β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε)) -
        ε / (ε - 1) * ((β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε))) := by
  have hG := rp_defl_pos hPi n k
  set G := rpDefl Pi n k
  have hε1 : ε - 1 ≠ 0 := by linarith
  unfold rpTerm rpBracket
  rw [Real.mul_rpow hp.le hG.le, Real.mul_rpow hp.le hG.le]
  have a1 : p ^ (-ε) = p ^ (-ε - 1) * p := by
    rw [← Real.rpow_add_one hp.ne']; ring_nf
  have a2 : G ^ (1 - ε) = G * G ^ (-ε) := by
    rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add_one hG.ne']; ring
  have a3 : G ^ (-ε) = G ^ (-ε - 1) * G := by
    rw [← Real.rpow_add_one hG.ne']; ring_nf
  rw [a2, a1, a3]
  field_simp
  ring

/-- **AKMM, pp. 539–540 (corrected)**: if the first-order condition holds (the partial sums of
`rpTerm` tend to `V_p = 0`) and the two weighted sums converge to `D` and `N/μ`, then
`p^R D = μ (N/μ)`: `p^R ∑ (βθ)^k λ (P_{n+k}/P_n)^{ε−1} = μ ∑ (βθ)^k λ (P_{n+k}/P_n)^ε m`. -/
theorem rp_foc_rearranged {β θ ε : ℝ} (hε : 1 < ε) {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s)
    (n : ℕ) {p D B : ℝ} (hp : 0 < p)
    (hfoc : Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop (𝓝 0))
    (hD : Tendsto (fun K => ∑ k ∈ range K, (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε))
      atTop (𝓝 D))
    (hB : Tendsto (fun K => ∑ k ∈ range K,
      (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε)) atTop (𝓝 B)) :
    p * D = ε / (ε - 1) * B := by
  have hsum : ∀ K, ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k = (1 - ε) * p ^ (-ε - 1) *
      (p * ∑ k ∈ range K, (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε) -
        ε / (ε - 1) * ∑ k ∈ range K,
          (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε)) := by
    intro K
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun k _ => rp_term_eq hε hPi n hp k
  have hlim : Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop
      (𝓝 ((1 - ε) * p ^ (-ε - 1) * (p * D - ε / (ε - 1) * B))) := by
    simp_rw [hsum]
    exact ((hD.const_mul p).sub (hB.const_mul _)).const_mul _
  have h0 := tendsto_nhds_unique hlim hfoc
  have hc : (1 - ε) * p ^ (-ε - 1) ≠ 0 :=
    mul_ne_zero (by linarith) (Real.rpow_pos_of_pos hp _).ne'
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h hc
  · linarith

/-- AKMM, (18.7), p. 540: the denominator `p^D_n = ∑_k (βθ)^k λ_{n+k} (P_{n+k}/P_n)^{ε−1}`. -/
noncomputable def rpD (β θ ε : ℝ) (lam Pi : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k, (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε)

/-- AKMM, (18.7), p. 540: the numerator
`p^N_n = ∑_k (βθ)^k λ_{n+k} (P_{n+k}/P_n)^ε μ m_{n+k}`, `μ = ε/(ε − 1)`. -/
noncomputable def rpN (β θ ε : ℝ) (lam mc Pi : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k, (β * θ) ^ k * lam (n + k) * (ε / (ε - 1) * mc (n + k)) * rpDefl Pi n k ^ (-ε)

/-- **AKMM, (18.7), p. 540 (corrected)**: under the first-order condition, with summable
weights and `p^D_n ≠ 0`, the reset price is `p^R_n = p^N_n/p^D_n`. -/
theorem eq_18_7 {β θ ε : ℝ} (hε : 1 < ε) {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s)
    (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hfoc : Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop (𝓝 0))
    (hsD : Summable fun k => (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε))
    (hsN : Summable fun k => (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε))
    (hD0 : rpD β θ ε lam Pi n ≠ 0) :
    p = rpN β θ ε lam mc Pi n / rpD β θ ε lam Pi n := by
  have h := rp_foc_rearranged hε hPi n hp hfoc hsD.hasSum.tendsto_sum_nat
    hsN.hasSum.tendsto_sum_nat
  have hN : rpN β θ ε lam mc Pi n = ε / (ε - 1) *
      ∑' k, (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε) := by
    rw [rpN, ← tsum_mul_left]
    congr 1; funext k; ring
  rw [eq_div_iff hD0, hN, rpD]
  exact h

/-- **AKMM, (18.7), p. 540 (corrected)**:
`p^D_n = λ_n + θβ (1 + π_{n+1})^{ε−1} p^D_{n+1}` (the book prints the exponent `ε`). -/
theorem rp_pD_rec {β θ ε : ℝ} {lam Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s) (n : ℕ)
    (hs : Summable fun k => (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε)) :
    rpD β θ ε lam Pi n = lam n + θ * β * Pi (n + 1) ^ (ε - 1) * rpD β θ ε lam Pi (n + 1) := by
  rw [rpD, hs.tsum_eq_zero_add, rpD, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, rp_defl_zero, Real.one_rpow, mul_one]
  congr 1
  congr 1; funext k
  have hG := rp_defl_pos hPi (n + 1) k
  have hP := hPi (n + 1)
  rw [rp_defl_succ', Real.div_rpow hG.le hP.le]
  have e : n + (k + 1) = n + 1 + k := by ring
  rw [e, pow_succ]
  rw [div_eq_mul_inv, ← Real.rpow_neg hP.le, neg_sub]
  ring

/-- **AKMM, (18.7), p. 540 (corrected)**:
`p^N_n = μ m_n λ_n + θβ (1 + π_{n+1})^ε p^N_{n+1}` (the book prints the exponent `1 + ε`). -/
theorem rp_pN_rec {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s) (n : ℕ)
    (hs : Summable fun k =>
      (β * θ) ^ k * lam (n + k) * (ε / (ε - 1) * mc (n + k)) * rpDefl Pi n k ^ (-ε)) :
    rpN β θ ε lam mc Pi n = ε / (ε - 1) * mc n * lam n +
      θ * β * Pi (n + 1) ^ ε * rpN β θ ε lam mc Pi (n + 1) := by
  rw [rpN, hs.tsum_eq_zero_add, rpN, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, rp_defl_zero, Real.one_rpow, mul_one]
  rw [mul_comm (lam n)]
  congr 1
  congr 1; funext k
  have hG := rp_defl_pos hPi (n + 1) k
  have hP := hPi (n + 1)
  rw [rp_defl_succ', Real.div_rpow hG.le hP.le]
  have e : n + (k + 1) = n + 1 + k := by ring
  rw [e, pow_succ]
  rw [Real.rpow_neg hP.le ε, div_inv_eq_mul]
  ring

/-- On a constant-inflation path `Π > 0`, `G_k = Π^{−k}` and `G_k^r = (Π^{−r})^k`. -/
theorem rp_defl_const_rpow {Pc : ℝ} (hP : 0 < Pc) (n k : ℕ) (r : ℝ) :
    rpDefl (fun _ => Pc) n k ^ r = (Pc ^ (-r)) ^ k := by
  have e : rpDefl (fun _ => Pc) n k = (Pc⁻¹) ^ k := by simp [rpDefl]
  rw [e, ← Real.rpow_pow_comm (inv_pos.2 hP).le, Real.inv_rpow hP.le, Real.rpow_neg hP.le]

/-- **AKMM, (18.7), p. 540, constant inflation (corrected)**: with `λ ≡ 1`, `m ≡ m`, gross
inflation `Π`, `a = βθ` and `aΠ^ε < 1`, the correct weights give
`p^R = μ m (1 − aΠ^{ε−1})/(1 − aΠ^ε)`. -/
theorem rp_constant_correct {β θ ε m Pc : ℝ} (hε : 1 < ε) (hP : 0 < Pc) (ha : 0 ≤ β * θ)
    (h1 : β * θ * Pc ^ (ε - 1) < 1) (h2 : β * θ * Pc ^ ε < 1) :
    rpN β θ ε (fun _ => 1) (fun _ => m) (fun _ => Pc) 0 / rpD β θ ε (fun _ => 1) (fun _ => Pc) 0
      = ε / (ε - 1) * m * (1 - β * θ * Pc ^ (ε - 1)) / (1 - β * θ * Pc ^ ε) := by
  have hq1 : 0 ≤ β * θ * Pc ^ (ε - 1) := mul_nonneg ha (Real.rpow_pos_of_pos hP _).le
  have hq2 : 0 ≤ β * θ * Pc ^ ε := mul_nonneg ha (Real.rpow_pos_of_pos hP _).le
  have hD : rpD β θ ε (fun _ => 1) (fun _ => Pc) 0 = (1 - β * θ * Pc ^ (ε - 1))⁻¹ := by
    rw [rpD]
    simp_rw [rp_defl_const_rpow hP, mul_one, neg_sub, ← mul_pow]
    exact tsum_geometric_of_lt_one hq1 h1
  have hN : rpN β θ ε (fun _ => 1) (fun _ => m) (fun _ => Pc) 0 =
      ε / (ε - 1) * m * (1 - β * θ * Pc ^ ε)⁻¹ := by
    rw [rpN]
    simp only [rp_defl_const_rpow hP, neg_neg, mul_one]
    have e : ∀ k : ℕ, (β * θ) ^ k * (ε / (ε - 1) * m) * (Pc ^ ε) ^ k =
        ε / (ε - 1) * m * (β * θ * Pc ^ ε) ^ k := by intro k; rw [mul_pow]; ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq2 h2]
  rw [hD, hN]
  have h1' : 1 - β * θ * Pc ^ (ε - 1) ≠ 0 := by linarith
  have h2' : 1 - β * θ * Pc ^ ε ≠ 0 := by linarith
  field_simp

/-- **AKMM, (18.7), p. 540, as printed, constant inflation**: the printed recursions
`p^N = μ m + θβ Π^{1+ε} p^N`, `p^D = 1 + θβ Π^ε p^D` have the constant solutions
`p^N = μm/(1 − aΠ^{1+ε})`, `p^D = 1/(1 − aΠ^ε)`, so the printed reset price is
`μ m (1 − aΠ^ε)/(1 − aΠ^{1+ε})`. -/
theorem rp_constant_printed {β θ ε m Pc pN pD : ℝ} (h1 : β * θ * Pc ^ (1 + ε) ≠ 1)
    (h2 : β * θ * Pc ^ ε ≠ 1)
    (hN : pN = ε / (ε - 1) * m + θ * β * Pc ^ (1 + ε) * pN)
    (hD : pD = 1 + θ * β * Pc ^ ε * pD) :
    pN / pD = ε / (ε - 1) * m * (1 - β * θ * Pc ^ ε) / (1 - β * θ * Pc ^ (1 + ε)) := by
  have h1' : 1 - β * θ * Pc ^ (1 + ε) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have h2' : 1 - β * θ * Pc ^ ε ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  have eN : pN = ε / (ε - 1) * m / (1 - β * θ * Pc ^ (1 + ε)) := by
    rw [eq_div_iff h1']; linear_combination hN
  have eD : pD = 1 / (1 - β * θ * Pc ^ ε) := by
    rw [eq_div_iff h2']; linear_combination hD
  rw [eN, eD]
  field_simp

/-- **AKMM, (18.7), p. 540 (correction)**: on a constant-inflation path with `βθ > 0`,
`m ≠ 0`, the printed and the correct reset prices coincide iff inflation is zero (`Π = 1`). -/
theorem rp_printed_ne_iff {β θ ε m Pc : ℝ} (hε : 1 < ε) (hP : 0 < Pc) (ha : 0 < β * θ)
    (hm : m ≠ 0) (h1 : β * θ * Pc ^ (1 + ε) < 1) (h2 : β * θ * Pc ^ ε < 1) :
    ε / (ε - 1) * m * (1 - β * θ * Pc ^ (ε - 1)) / (1 - β * θ * Pc ^ ε) =
        ε / (ε - 1) * m * (1 - β * θ * Pc ^ ε) / (1 - β * θ * Pc ^ (1 + ε)) ↔ Pc = 1 := by
  have h1' : 1 - β * θ * Pc ^ (1 + ε) ≠ 0 := by linarith
  have h2' : 1 - β * θ * Pc ^ ε ≠ 0 := by linarith
  have hμ : ε / (ε - 1) ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have eA : Pc ^ ε = Pc ^ (ε - 1) * Pc := by
    rw [← Real.rpow_add_one hP.ne']; ring_nf
  have eB : Pc ^ (1 + ε) = Pc ^ (ε - 1) * Pc ^ 2 := by
    rw [show 1 + ε = (ε - 1) + 2 by ring, Real.rpow_add hP]
    norm_cast
  have hx : 0 < Pc ^ (ε - 1) := Real.rpow_pos_of_pos hP _
  rw [div_eq_div_iff h2' h1']
  constructor
  · intro h
    have key : ε / (ε - 1) * m * (β * θ * Pc ^ (ε - 1) * (Pc - 1) ^ 2) = 0 := by
      rw [eA, eB] at h; linear_combination -h
    have : (Pc - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.1 key with h | h
      · exact absurd h (mul_ne_zero hμ hm)
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h (mul_pos ha hx).ne'
        · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · rintro rfl
    simp

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Calvo aggregation and price dispersion

AKMM, §18.3, pp. 540–542: the price index under Calvo pricing (18.9), inflation and the reset
price (18.10), the aggregate production function with price dispersion (18.11) and the
dispersion recursion (18.12).

The firms that cannot reset at `t` form a set `S` of measure `θ`, and (the book's "firms are
chosen randomly") the law of large numbers `∫_S f = θ ∫ f` holds for the relevant integrand;
both are hypotheses, as in Miao's `eq_19_13` and `eq_19_17`, which we import.

* `eq_18_9`: `P_t = [θP_{t−1}^{1−ε} + (1 − θ)(P^R_t)^{1−ε}]^{1/(1−ε)}`.
* `agg_reset_relprice`, `eq_18_10`: `p^R = [(1 − θ(1 + π)^{ε−1})/(1 − θ)]^{1/(1−ε)}` and
  `1 + π = [(1 − (1 − θ)(p^R)^{1−ε})/θ]^{1/(ε−1)}`.
* `eq_18_11`: `Y = A L/D` with `D = ∫ (P_j/P)^{−ε}`.
* `agg_dispersion_ge_one`, `agg_dispersion_eq_one_iff`: `D ≥ 1`, with equality iff all prices
  equal the index almost everywhere (Galí's Jensen argument, at `α = 0`).
* `eq_18_12`: `D_t = (1 − θ)(p^R_t)^{−ε} + θ(1 + π_t)^ε D_{t−1}`.
-/

namespace AKMM.NominalFrictions

open MeasureTheory Gali.BasicNewKeynesianModel.CES Gali.BasicNewKeynesianModel.PriceDispersion

/-- **AKMM, (18.9), p. 540**: prices at `t` are the old prices `p₀` on the non-adjusters `S`
(`μ(S) = θ`) and the reset price `P^R > 0` elsewhere; with the law of large numbers,
`P_t = [θ P_{t−1}^{1−ε} + (1 − θ)(P^R)^{1−ε}]^{1/(1−ε)}` (from Miao's `eq_19_13`). -/
theorem eq_18_9 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε PR : ℝ} (hε : 1 < ε) (hθ : μ.real S = θ)
    {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j) (hPR : 0 < PR)
    (hI : Integrable (fun j => p₀ j ^ (1 - ε)) μ) (hS1 : ∀ j ∈ S, p₁ j = p₀ j)
    (hSc : ∀ j ∉ S, p₁ j = PR)
    (hLLN : ∫ j in S, p₀ j ^ (1 - ε) ∂μ = θ * ∫ j, p₀ j ^ (1 - ε) ∂μ) :
    Miao.NewKeynesian.nk_priceIndex μ ε p₁ =
      (θ * Miao.NewKeynesian.nk_priceIndex μ ε p₀ ^ (1 - ε) + (1 - θ) * PR ^ (1 - ε)) ^
        (1 / (1 - ε)) := by
  have h := Miao.NewKeynesian.eq_19_13 hS hε hθ hp₀ hPR hI hS1 hSc hLLN
  rw [← h]
  have hpos : 0 ≤ Miao.NewKeynesian.nk_priceIndex μ ε p₁ := by
    change 0 ≤ (∫ j, p₁ j ^ (1 - ε) ∂μ) ^ (1 / (1 - ε))
    refine Real.rpow_nonneg (integral_nonneg fun j => Real.rpow_nonneg ?_ _) _
    by_cases hj : j ∈ S
    · rw [hS1 j hj]; exact (hp₀ j).le
    · rw [hSc j hj]; exact hPR.le
  have h1e : (1 : ℝ) - ε ≠ 0 := by linarith
  rw [← Real.rpow_mul hpos, mul_one_div_cancel h1e, Real.rpow_one]

/-- AKMM, p. 541: dividing (18.9) by `P_t^{1−ε}`, with `1 + π_t = P_t/P_{t−1}` and
`p^R = P^R/P_t`: `1 = θ(1 + π_t)^{ε−1} + (1 − θ)(p^R)^{1−ε}`. -/
theorem agg_index_relative {θ ε P Pm PR : ℝ} (hP : 0 < P) (hPm : 0 < Pm) (hPR : 0 < PR)
    (h9 : P ^ (1 - ε) = θ * Pm ^ (1 - ε) + (1 - θ) * PR ^ (1 - ε)) :
    1 = θ * (P / Pm) ^ (ε - 1) + (1 - θ) * (PR / P) ^ (1 - ε) := by
  have hx : 0 < P ^ (1 - ε) := Real.rpow_pos_of_pos hP _
  have e1 : (P / Pm) ^ (ε - 1) = Pm ^ (1 - ε) / P ^ (1 - ε) := by
    rw [show ε - 1 = -(1 - ε) by ring, Real.rpow_neg (div_pos hP hPm).le,
      Real.div_rpow hP.le hPm.le, inv_div]
  rw [e1, Real.div_rpow hPR.le hP.le]
  field_simp
  linarith

/-- AKMM, p. 541: the relative reset price in terms of inflation,
`p^R = [(1 − θ(1 + π)^{ε−1})/(1 − θ)]^{1/(1−ε)}`. -/
theorem agg_reset_relprice {θ ε Gπ pR : ℝ} (hε : 1 < ε) (hθ : θ < 1) (hpR : 0 < pR)
    (h : 1 = θ * Gπ ^ (ε - 1) + (1 - θ) * pR ^ (1 - ε)) :
    pR = ((1 - θ * Gπ ^ (ε - 1)) / (1 - θ)) ^ (1 / (1 - ε)) := by
  have e : (1 - θ * Gπ ^ (ε - 1)) / (1 - θ) = pR ^ (1 - ε) := by
    rw [div_eq_iff (by linarith)]; linarith
  have h1e : (1 : ℝ) - ε ≠ 0 := by linarith
  rw [e, ← Real.rpow_mul hpR.le, mul_one_div_cancel h1e, Real.rpow_one]

/-- **AKMM, (18.10), p. 541**: `1 + π_t = [(1 − (1 − θ)(p^R_t)^{1−ε})/θ]^{1/(ε−1)}`. -/
theorem eq_18_10 {θ ε Gπ pR : ℝ} (hε : 1 < ε) (hθ : 0 < θ) (hG : 0 < Gπ)
    (h : 1 = θ * Gπ ^ (ε - 1) + (1 - θ) * pR ^ (1 - ε)) :
    Gπ = ((1 - (1 - θ) * pR ^ (1 - ε)) / θ) ^ (1 / (ε - 1)) := by
  have e : (1 - (1 - θ) * pR ^ (1 - ε)) / θ = Gπ ^ (ε - 1) := by
    rw [div_eq_iff hθ.ne']; linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [e, ← Real.rpow_mul hG.le, show (ε - 1) * (1 / (ε - 1)) = 1 by field_simp, Real.rpow_one]

/-- **AKMM, (18.11), p. 541**: with `y_j = A ℓ_j` (18.3), demand `y_j = (P_j/P)^{−ε} Y` (18.4)
and labour-market clearing `L = ∫ ℓ_j`, `Y = A L/D` where `D = ∫ (P_j/P)^{−ε}` (`D > 0`). -/
theorem eq_18_11 {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε A Y P L : ℝ}
    (hA : 0 < A) {Pj ℓ : J → ℝ} (hD : 0 < ∫ j, (Pj j / P) ^ (-ε) ∂μ)
    (hprod : ∀ j, (Pj j / P) ^ (-ε) * Y = A * ℓ j) (hL : L = ∫ j, ℓ j ∂μ) :
    Y = A * L / ∫ j, (Pj j / P) ^ (-ε) ∂μ := by
  have hl : ∀ j, ℓ j = (Pj j / P) ^ (-ε) * (Y / A) := by
    intro j; rw [← mul_div_assoc, hprod j]; field_simp
  have : L = (∫ j, (Pj j / P) ^ (-ε) ∂μ) * (Y / A) := by
    rw [hL]; simp_rw [hl]; rw [integral_mul_const]
  rw [this]
  field_simp

/-- AKMM, p. 541: if all prices are equal, `D = 1` and `Y = A L`. -/
theorem agg_flex_output {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε P : ℝ} (hP : 0 < P) :
    ∫ _j : J, (P / P) ^ (-ε) ∂μ = 1 := by
  simp [div_self hP.ne']

/-- **AKMM, p. 541**: price dispersion `D = ∫ (P_j/P)^{−ε} ≥ 1`, `P` the CES price index
(Galí's `one_le_integral_disp` at `α = 0`). -/
theorem agg_dispersion_ge_one {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {Pj : J → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : Integrable (fun j => Pj j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (Pj j / priceIndex μ ε Pj) ^ (-ε)) μ) :
    1 ≤ ∫ j, (Pj j / priceIndex μ ε Pj) ^ (-ε) ∂μ := by
  have e : -ε / (1 - 0) = -ε := by simp
  have h := one_le_integral_disp (α := 0) hε le_rfl (by norm_num) hP hPi (by rw [e]; exact hD)
  rwa [e] at h

/-- **AKMM, p. 541**: `D = 1` iff every price equals the index almost everywhere, so `D > 1`
whenever prices are dispersed (Galí's `dispersion_eq_zero_iff` at `α = 0`). -/
theorem agg_dispersion_eq_one_iff {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {Pj : J → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : Integrable (fun j => Pj j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (Pj j / priceIndex μ ε Pj) ^ (-ε)) μ) :
    ∫ j, (Pj j / priceIndex μ ε Pj) ^ (-ε) ∂μ = 1 ↔ ∀ᵐ j ∂μ, Pj j = priceIndex μ ε Pj := by
  have e : -ε / (1 - 0) = -ε := by simp
  have h := dispersion_eq_zero_iff (α := 0) hε le_rfl (by norm_num) hP hPi (by rw [e]; exact hD)
  rw [← h, dispersion, e, sub_zero, one_mul]
  have h1 := agg_dispersion_ge_one hε hP hPi hD
  constructor
  · intro h2; rw [h2, Real.log_one]
  · intro h2
    rcases Real.log_eq_zero.1 h2 with h3 | h3 | h3 <;> [linarith; exact h3; linarith]

/-- **AKMM, (18.12), p. 541**: prices at `t` are the old prices `p₀` on the non-adjusters `S`
(`μ(S) = θ`) and `P^R` elsewhere; with the law of large numbers
`∫_S (p₀/P_{t−1})^{−ε} = θ D_{t−1}`,
`D_t = (1 − θ)(P^R/P_t)^{−ε} + θ(1 + π_t)^ε D_{t−1}` (Miao's `eq_19_17` at `α = 0`). -/
theorem eq_18_12 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε PR P₀ P₁ : ℝ} (hθ : μ.real S = θ)
    (hP₀ : 0 < P₀) (hP₁ : 0 < P₁) {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j)
    (hI : Integrable (fun j => (p₀ j / P₀) ^ (-ε)) μ)
    (hS1 : ∀ j ∈ S, p₁ j = p₀ j) (hSc : ∀ j ∉ S, p₁ j = PR)
    (hLLN : ∫ j in S, (p₀ j / P₀) ^ (-ε) ∂μ = θ * ∫ j, (p₀ j / P₀) ^ (-ε) ∂μ) :
    ∫ j, (p₁ j / P₁) ^ (-ε) ∂μ =
      (1 - θ) * (PR / P₁) ^ (-ε) + θ * (P₁ / P₀) ^ ε * ∫ j, (p₀ j / P₀) ^ (-ε) ∂μ := by
  have e1 : -ε / (1 - 0) = -ε := by simp
  have e2 : ε / (1 - 0) = ε := by simp
  have h := Miao.NewKeynesian.eq_19_17 (α := 0) hS hθ hP₀ hP₁ hp₀ (by rw [e1]; exact hI) hS1
    hSc (by rw [Miao.NewKeynesian.nk_dispersion, e1]; exact hLLN)
  simp only [Miao.NewKeynesian.nk_dispersion, e1, e2] at h
  rw [h]
  ring

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The flexible-price equilibrium, the output gap and the interest-rate rule

AKMM, §18.3, pp. 542–543. With flexible prices (`θ = 0`) a firm maximises
`(p − w/A) p^{−ε} Y`, which gives the markup `µ = ε/(ε − 1)` over marginal cost
(`nat_markup_foc`, `nat_markup_max`, footnote 7), so `w^n/A = 1/µ`. The flexible-price
system then gives natural output (18.13), `Y^n = µ^{−1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`
(`nat_output_general`, `eq_18_13`, `eq_18_13_solves`). The output gap is (18.14)
(`nfGap`, `nat_gap_loglinear`, footnote 9). The steady-state intercept of the rule is
`ī = (1 + π*)/β − 1` (`nat_rule_intercept`), and footnote 8's quarterly rescaling of the
output-gap coefficient is `0.5/4 = 0.125` (`nat_quarterly_rule`).
-/

namespace AKMM.NominalFrictions

/-- AKMM, p. 542 and footnote 7: the static first-order condition. For `m = w/A > 0` and
`p > 0`, the derivative of `(p − m) p^{−ε}` vanishes iff `p = µ m`, `µ = ε/(ε − 1)`. -/
theorem nat_markup_foc {ε m p : ℝ} (hε : 1 < ε) (hp : 0 < p) :
    rpBracket ε m p = 0 ↔ p = ε / (ε - 1) * m := by
  have hε1 : ε - 1 ≠ 0 := by linarith
  have e : rpBracket ε m p = p ^ (-ε - 1) * ((1 - ε) * p + ε * m) := by
    unfold rpBracket
    have a1 : p ^ (-ε) = p ^ (-ε - 1) * p := by
      rw [← Real.rpow_add_one hp.ne']; ring_nf
    rw [a1]; ring
  rw [e, mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos hp _).ne']
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **AKMM, p. 542 and footnote 7**: the markup price `µ m` maximises the static profit
`(p − m) p^{−ε}` over `p > 0` (Bernoulli's inequality). -/
theorem nat_markup_max {ε m p : ℝ} (hε : 1 < ε) (hm : 0 < m) (hp : 0 < p) :
    (p - m) * p ^ (-ε) ≤ (ε / (ε - 1) * m - m) * (ε / (ε - 1) * m) ^ (-ε) := by
  set q := ε / (ε - 1) * m with hq
  have hε1 : 0 < ε - 1 := by linarith
  have hq0 : 0 < q := by positivity
  set x := p / q with hx
  have hx0 : 0 < x := div_pos hp hq0
  have hB := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) hε.le
  rw [show 1 + (x - 1) = x by ring] at hB
  have hpx : p = x * q := by rw [hx]; field_simp
  have hmq : m = (ε - 1) / ε * q := by rw [hq]; field_simp
  have hxe : (x * q) ^ (-ε) = x ^ (-ε) * q ^ (-ε) := Real.mul_rpow hx0.le hq0.le
  have hxx : x ^ ε * x ^ (-ε) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hxpos : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
  have hqpos : 0 < q ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  rw [hpx, hxe, hmq]
  have hε0 : 0 < ε := by linarith
  have key : (x - (ε - 1) / ε) * x ^ (-ε) ≤ 1 - (ε - 1) / ε := by
    have h1 : x - (ε - 1) / ε ≤ x ^ ε / ε := by
      have e : (x - (ε - 1) / ε) * ε = ε * x - (ε - 1) := by field_simp
      rw [le_div_iff₀ hε0, e]; linarith
    calc (x - (ε - 1) / ε) * x ^ (-ε) ≤ x ^ ε / ε * x ^ (-ε) :=
          mul_le_mul_of_nonneg_right h1 hxpos.le
      _ = 1 - (ε - 1) / ε := by field_simp; linear_combination hxx
  have := mul_le_mul_of_nonneg_right key (mul_pos hq0 hqpos).le
  calc (x * q - (ε - 1) / ε * q) * (x ^ (-ε) * q ^ (-ε))
      = (x - (ε - 1) / ε) * x ^ (-ε) * (q * q ^ (-ε)) := by ring
    _ ≤ (1 - (ε - 1) / ε) * (q * q ^ (-ε)) := this
    _ = (q - (ε - 1) / ε * q) * q ^ (-ε) := by ring

/-- AKMM, p. 542: the markup `µ = ε/(ε − 1)` exceeds one when `ε > 1`. -/
theorem nat_markup_gt_one {ε : ℝ} (hε : 1 < ε) : 1 < ε / (ε - 1) := by
  rw [lt_div_iff₀ (by linarith)]; linarith

/-- AKMM, p. 542: with the flexible-price reset price `p^R = µ w/A` and `p^R = 1` (all firms
choose the same price), `w^n/A = 1/µ`. -/
theorem nat_wage {ε w A : ℝ} (h : 1 = ε / (ε - 1) * (w / A)) :
    w / A = 1 / (ε / (ε - 1)) := by
  exact eq_one_div_of_mul_eq_one_right h.symm

/-- AKMM, pp. 542 and 545–546: equilibrium output given the wage. From `C = Y`, `Y = A L/D`
and `C^{−σ} w = L^ψ`, `Y = D^{−ψ/(σ+ψ)} (w/A)^{1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`. -/
theorem nat_output_general {σ ψ w A D Y L : ℝ} (hs : 0 < σ + ψ) (hw : 0 < w) (hA : 0 < A)
    (hD : 0 < D) (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L / D)
    (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Y = D ^ (-ψ / (σ + ψ)) * (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
  have hLe : L = D * Y / A := by rw [hprod]; field_simp
  have hlog := congrArg Real.log hlab
  rw [Real.log_mul (Real.rpow_pos_of_pos hY _).ne' hw.ne', Real.log_rpow hY,
    Real.log_rpow hL, hLe, Real.log_div (by positivity) hA.ne',
    Real.log_mul hD.ne' hY.ne'] at hlog
  have hlY : Real.log Y = (-ψ * Real.log D + (Real.log w - Real.log A) +
      (1 + ψ) * Real.log A) / (σ + ψ) := by
    rw [eq_div_iff hs.ne']; linarith
  have hR : 0 < D ^ (-ψ / (σ + ψ)) * (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
    positivity
  refine Real.log_injOn_pos hY hR ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hD, Real.log_rpow (div_pos hw hA), Real.log_rpow hA,
    Real.log_div hw.ne' hA.ne', hlY]
  field_simp

/-- **AKMM, (18.13), p. 542**: the flexible-price equilibrium. If `w^n = A/µ`, `Y^n = C^n`,
`Y^n = A L^n` and `(C^n)^{−σ} w^n = (L^n)^ψ`, then `Y^n = µ^{−1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`. -/
theorem eq_18_13 {σ ψ mu A Y C L w : ℝ} (hs : 0 < σ + ψ) (hmu : 0 < mu) (hA : 0 < A)
    (hY : 0 < Y) (hL : 0 < L) (hw : w = A / mu) (hC : Y = C) (hprod : Y = A * L)
    (hlab : C ^ (-σ) * w = L ^ ψ) :
    Y = mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := nat_output_general (D := 1) (w := w) (Y := Y) (L := L) hs
    (by rw [hw]; positivity) hA one_pos hY hL (by rw [hprod, div_one]) (by rw [hC]; exact hlab)
  rw [Real.one_rpow, one_mul, hw, show A / mu / A = mu⁻¹ by field_simp,
    Real.inv_rpow hmu.le, ← Real.rpow_neg hmu.le] at h
  rw [neg_div]; exact h

/-- AKMM, (18.13), p. 542: conversely, the natural allocation solves the flexible-price
system: with `Y = µ^{−1/(σ+ψ)} A^{(1+ψ)/(σ+ψ)}`, `L = Y/A`, `w = A/µ`, `Y^{−σ} w = L^ψ`. -/
theorem eq_18_13_solves {σ ψ mu A : ℝ} (hs : 0 < σ + ψ) (hmu : 0 < mu) (hA : 0 < A) :
    (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) ^ (-σ) * (A / mu) =
      (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) / A) ^ ψ := by
  have hY : 0 < mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by positivity
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hY, Real.log_rpow
    (div_pos hY hA), Real.log_div hY.ne' hA.ne', Real.log_div hA.ne' hmu.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hmu, Real.log_rpow hA]
  field_simp
  ring

/-- AKMM, (18.14), p. 542: the output gap `x = log Y − log Y^n`. -/
noncomputable def nfGap (Y Yn : ℝ) : ℝ := Real.log Y - Real.log Yn

/-- AKMM, (18.13) and (18.14), footnote 9, p. 543: with `Y^n` from (18.13), hats the log
deviations from the steady state `A = 1` (`Ȳ = µ^{−1/(σ+ψ)}`), the output gap is exactly
`x = Ŷ − (1+ψ)/(σ+ψ) Â`. -/
theorem nat_gap_loglinear {σ ψ mu A Y : ℝ} (hmu : 0 < mu) (hA : 0 < A) :
    nfGap Y (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) =
      (Real.log Y - Real.log (mu ^ (-1 / (σ + ψ)))) - (1 + ψ) / (σ + ψ) * Real.log A := by
  unfold nfGap
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA]
  ring

/-- AKMM, p. 543: in a steady state with constant consumption and inflation `π*`, the Euler
equation (18.5) holds iff `i = ī ≡ (1 + π*)/β − 1`. -/
theorem nat_rule_intercept {β σ C π i : ℝ} (hβ : 0 < β) (hC : 0 < C) (hπ : 0 < 1 + π) :
    C ^ (-σ) = β * ((1 + i) / (1 + π) * C ^ (-σ)) ↔ i = (1 + π) / β - 1 := by
  have hc : 0 < C ^ (-σ) := Real.rpow_pos_of_pos hC _
  constructor
  · intro h
    have h1 : β * ((1 + i) / (1 + π)) = 1 := by
      have := mul_right_cancel₀ hc.ne' (by linarith [h] : 1 * C ^ (-σ) =
        β * ((1 + i) / (1 + π)) * C ^ (-σ))
      linarith
    field_simp at h1 ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, footnote 8, p. 543: with annualised rates `i^a = 4 i^q` and `π^a = 4 π^q` and the
output gap in percent, the rule `i^a = φ_π π^a + φ_x x` reads `i^q = φ_π π^q + (φ_x/4) x`;
Taylor's `φ_x = 0.5` becomes `0.125`. -/
theorem nat_quarterly_rule {φπ φx iq πq x : ℝ} :
    (4 * iq = φπ * (4 * πq) + φx * x ↔ iq = φπ * πq + φx / 4 * x) ∧ (0.5 : ℝ) / 4 = 0.125 := by
  refine ⟨⟨fun h => by linarith, fun h => by rw [h]; ring⟩, by norm_num⟩

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Policy objectives: efficiency, the subsidy and the quadratic loss

AKMM, §18.4.1, pp. 545–547.

* `eff_planner_foc`, `eq_18_19`: the planner's first-order condition and the efficient output
  `Y* = A^{(1+ψ)/(σ+ψ)}`.
* `eff_output_wage`, `eff_output_dispersion`: `Y = (w/A)^{1/(σ+ψ)} Y*` without dispersion and
  `Y = D^{−ψ/(σ+ψ)} (w/A)^{1/(σ+ψ)} Y*` with it (from `nat_output_general`).
* `eff_natural_lt`: with `w/A = 1/µ < 1`, `Y^n = µ^{−1/(σ+ψ)} Y* < Y*`; `eff_dispersion_lowers`:
  dispersion `D > 1` lowers output at a given `w/A`; `eff_marginal_cost_pricing`: pricing at
  nominal marginal cost means `w/A = 1`.
* `eff_welfare_gap`: `x^w = x − log µ/(σ+ψ)`.
* `eff_subsidy`, `eff_subsidy_mem`: the subsidy `τ = 1/ε ∈ (0, 1)` is the unique subsidy with
  flexible-price `w/A = 1`, so that `Y^n = Y*` (`eff_subsidy_natural_eq`).
* (18.20), cited by the book (Woodford 2003): at `α = 0` Galí's second-order approximation of
  period utility around the efficient steady state (`eq_18_20_utility`, from Galí's
  `Welfare.period_utility_normalised`) has gap coefficient `σ + ψ` and dispersion weight `ε`,
  and the welfare loss is `ε/(2λ)` times `π² + (κ/ε) x²` with the book's
  `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ` (`eq_18_20_weight`, `eq_18_20_period`).
-/

namespace AKMM.NominalFrictions

open Asymptotics Filter Topology

/-- AKMM, p. 545: the planner's objective `u(A L) − L^{1+ψ}/(1+ψ)` has derivative
`A (A L)^{−σ} − L^ψ` in `L`. -/
theorem eff_planner_foc {σ ψ A L : ℝ} (hσ : σ ≠ 1) (hψ : 0 < ψ) (hA : 0 < A) (hL : 0 < L) :
    HasDerivAt (fun l => nfU σ ψ (A * l) l) ((A * L) ^ (-σ) * A - L ^ ψ) L := by
  have h := env_labour_foc (C₀ := 0) (w := A) hσ hψ (by positivity) hL
  simpa using h

/-- **AKMM, (18.19), p. 545**: at the planner's optimum (`A (A L)^{−σ} = L^ψ`), efficient output
is `Y* = A L = A^{(1+ψ)/(σ+ψ)}`. -/
theorem eq_18_19 {σ ψ A L : ℝ} (hs : 0 < σ + ψ) (hA : 0 < A) (hL : 0 < L)
    (hfoc : (A * L) ^ (-σ) * A = L ^ ψ) : A * L = A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := nat_output_general (D := 1) (w := A) (Y := A * L) (L := L) hs hA hA one_pos
    (by positivity) hL (by rw [div_one]) hfoc
  rwa [Real.one_rpow, one_mul, div_self hA.ne', Real.one_rpow, one_mul] at h

/-- AKMM, (18.19), p. 545: conversely `Y* = A^{(1+ψ)/(σ+ψ)}` satisfies the first-order
condition (`eq_18_13_solves` with `µ = 1`). -/
theorem eq_18_19_solves {σ ψ A : ℝ} (hs : 0 < σ + ψ) (hA : 0 < A) :
    (A ^ ((1 + ψ) / (σ + ψ))) ^ (-σ) * A = (A ^ ((1 + ψ) / (σ + ψ)) / A) ^ ψ := by
  have h := eq_18_13_solves (mu := 1) hs one_pos hA
  simpa using h

/-- **AKMM, p. 545**: without price dispersion (`Y = A L`), with `C = Y` and (18.6),
`Y = (w/A)^{1/(σ+ψ)} Y*`. -/
theorem eff_output_wage {σ ψ w A Y L : ℝ} (hs : 0 < σ + ψ) (hw : 0 < w) (hA : 0 < A)
    (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L) (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Y = (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := nat_output_general (D := 1) hs hw hA one_pos hY hL (by rw [hprod, div_one]) hlab
  rwa [Real.one_rpow, one_mul] at h

/-- **AKMM, p. 546**: with dispersion (`Y = A L/D`), `C = Y` and (18.6),
`Y = D^{−ψ/(σ+ψ)} (w/A)^{1/(σ+ψ)} Y*`. -/
theorem eff_output_dispersion {σ ψ w A D Y L : ℝ} (hs : 0 < σ + ψ) (hw : 0 < w) (hA : 0 < A)
    (hD : 0 < D) (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L / D)
    (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Y = D ^ (-ψ / (σ + ψ)) * (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) :=
  nat_output_general hs hw hA hD hY hL hprod hlab

/-- **AKMM, p. 546**: in the flexible-price economy `w/A = 1/µ < 1`, so natural output
`Y^n = µ^{−1/(σ+ψ)} Y*` is strictly below the efficient level. -/
theorem eff_natural_lt {σ ψ mu A : ℝ} (hs : 0 < σ + ψ) (hmu : 1 < mu) (hA : 0 < A) :
    mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) < A ^ ((1 + ψ) / (σ + ψ)) := by
  have h1 : mu ^ (-1 / (σ + ψ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hmu (div_neg_of_neg_of_pos (by norm_num) hs)
  have h2 : 0 < A ^ ((1 + ψ) / (σ + ψ)) := by positivity
  nlinarith

/-- AKMM, p. 546: with `ψ > 0`, at a given `w/A`, dispersion `D > 1` strictly lowers output:
`D^{−ψ/(σ+ψ)} < 1`. -/
theorem eff_dispersion_lowers {σ ψ D : ℝ} (hs : 0 < σ + ψ) (hψ : 0 < ψ) (hD : 1 < D) :
    D ^ (-ψ / (σ + ψ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hD (div_neg_of_neg_of_pos (by linarith) hs)

/-- AKMM, p. 546: "if firms set prices equal to nominal marginal cost we would have
`P_t = P_t w_t/A` or `w_t/A_t = 1`". -/
theorem eff_marginal_cost_pricing {P w A : ℝ} (hP : 0 < P) (hA : 0 < A) :
    P = P * w / A ↔ w / A = 1 := by
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    rw [mul_div_assoc, h, mul_one]

/-- **AKMM, p. 546**: the welfare-relevant gap `x^w = log Y − log Y*` equals
`x − log µ/(σ+ψ)`, with `Y^n = µ^{−1/(σ+ψ)} Y*` (18.13), (18.19). -/
theorem eff_welfare_gap {σ ψ mu A Y : ℝ} (hmu : 0 < mu) (hA : 0 < A) :
    Real.log Y - Real.log (A ^ ((1 + ψ) / (σ + ψ))) =
      nfGap Y (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) - Real.log mu / (σ + ψ) := by
  unfold nfGap
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hmu]
  ring

/-- **AKMM, p. 547**: with a production subsidy `τ`, the flexible-price price is the markup over
the subsidised marginal cost, `1 = µ(1 − τ) w/A`; then `w/A = 1` iff `τ = 1/ε`. -/
theorem eff_subsidy {ε τ w A : ℝ} (hε : 1 < ε) (hA : 0 < A)
    (h : 1 = ε / (ε - 1) * ((1 - τ) * w / A)) : w / A = 1 ↔ τ = 1 / ε := by
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  have h' : (ε - 1) * A = ε * ((1 - τ) * w) := by field_simp at h; linarith
  constructor
  · intro hw
    have hw' : w = A := by field_simp at hw; linarith
    rw [hw'] at h'
    have : (ε - 1) = ε * (1 - τ) := by
      have := mul_right_cancel₀ hA.ne' (by linarith : (ε - 1) * A = ε * (1 - τ) * A)
      linarith
    field_simp
    linarith
  · intro hτ
    rw [hτ] at h'
    have : (ε - 1) * A = (ε - 1) * w := by rw [h']; field_simp
    have hw : A = w := mul_left_cancel₀ hε1 this
    rw [hw, div_self (by rw [← hw]; exact hA.ne')]

/-- AKMM, p. 547: the subsidy `τ = 1/ε` lies in `(0, 1)` for `ε > 1`. -/
theorem eff_subsidy_mem {ε : ℝ} (hε : 1 < ε) : 0 < 1 / ε ∧ 1 / ε < 1 :=
  ⟨by positivity, by rw [div_lt_one (by linarith)]; exact hε⟩

/-- AKMM, p. 547: with the subsidy `τ = 1/ε` the flexible-price wage is `w = A`, so the
flexible-price allocation (18.13) with `µ(1 − τ) = 1` is efficient, `Y^n = Y*`. -/
theorem eff_subsidy_natural_eq {σ ψ A Y C L w : ℝ} (hs : 0 < σ + ψ) (hA : 0 < A) (hY : 0 < Y)
    (hL : 0 < L) (hw : w = A) (hC : Y = C) (hprod : Y = A * L) (hlab : C ^ (-σ) * w = L ^ ψ) :
    Y = A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := eq_18_13 (mu := 1) hs one_pos hA hY hL (by rw [hw, div_one]) hC hprod hlab
  simpa using h

/-- **AKMM, (18.20), p. 547 (the weights)**: at `α = 0` (the book's technology (18.3)),
Galí's slope `κ = λ(σ + φ)` with `λ = (1 − θ)(1 − βθ)/θ` is the book's
`κ = (1 − θ)(1 − βθ)(σ + ψ)/θ`, and the relative weight of the output gap in the loss is
`ϑ = κ/ε`. -/
theorem eq_18_20_weight {β θ σ ψ ε : ℝ} :
    Gali.DiscretionCommitment.LossAndCostPush.kappaNK β θ σ ψ 0 ε =
        (1 - θ) * (1 - β * θ) * (σ + ψ) / θ ∧
      Gali.DiscretionCommitment.LossAndCostPush.vartheta β θ σ ψ 0 ε =
        (1 - θ) * (1 - β * θ) * (σ + ψ) / θ / ε := by
  have hk : Gali.DiscretionCommitment.LossAndCostPush.kappaNK β θ σ ψ 0 ε =
      (1 - θ) * (1 - β * θ) * (σ + ψ) / θ := by
    simp only [Gali.DiscretionCommitment.LossAndCostPush.kappaNK,
      Gali.DiscretionCommitment.LossAndCostPush.lambdaNK,
      Gali.DiscretionCommitment.LossAndCostPush.bigTheta,
      Gali.DiscretionCommitment.LossAndCostPush.gapCoeff]
    simp only [sub_zero, add_zero, div_one]
    ring
  refine ⟨hk, ?_⟩
  rw [Gali.DiscretionCommitment.LossAndCostPush.vartheta, hk]

/-- **AKMM, (18.20), p. 547 (the period loss)**: at `α = 0` the second-order welfare loss per
period, `½[(σ + ψ) x² + (ε/λ) π²]`, equals `ε/(2λ)` times the book's `π² + (κ/ε) x²`
(Galí's `periodLoss_eq_scaled`). -/
theorem eq_18_20_period {β θ σ ψ ε : ℝ} (hlam : (1 - θ) * (1 - β * θ) / θ ≠ 0) (hε : ε ≠ 0)
    (x infl : ℝ) :
    ((σ + ψ) * x ^ 2 + ε / ((1 - θ) * (1 - β * θ) / θ) * infl ^ 2) / 2 =
      ε / (2 * ((1 - θ) * (1 - β * θ) / θ)) *
        (infl ^ 2 + (1 - θ) * (1 - β * θ) * (σ + ψ) / θ / ε * x ^ 2) := by
  have hl : Gali.DiscretionCommitment.LossAndCostPush.lambdaNK β θ 0 ε =
      (1 - θ) * (1 - β * θ) / θ := by
    simp [Gali.DiscretionCommitment.LossAndCostPush.lambdaNK,
      Gali.DiscretionCommitment.LossAndCostPush.bigTheta]
  have hg : Gali.DiscretionCommitment.LossAndCostPush.gapCoeff σ ψ 0 = σ + ψ := by
    simp [Gali.DiscretionCommitment.LossAndCostPush.gapCoeff]
  have h := Gali.DiscretionCommitment.LossAndCostPush.periodLoss_eq_scaled (β := β) (θ := θ)
    (σ := σ) (φ := ψ) (α := 0) (ε := ε) (by rw [hl]; exact hlam) hε x infl
  rw [hl, hg, (eq_18_20_weight (β := β) (θ := θ) (σ := σ) (ψ := ψ) (ε := ε)).2] at h
  exact h

/-- **AKMM, (18.20), p. 547 and footnote 11 (the second-order approximation)**: around a steady
state made efficient by the subsidy (`w′(N) N = −u′(C) C`, Galí's condition at `α = 0`), with
first-order log deviations `y, a, z`, a second-order dispersion term `v`, the dispersion
`d = (ε/2) v + O(s³)` and `n = y − a + d`, period utility satisfies
`(U_t − U)/(U_c C) = −½[(σ + ψ)(y − ψ_ya a)² + ε v] + t.i.p. + O(s³)` (Galí's
`Welfare.period_utility_normalised` at `α = 0`). -/
theorem eq_18_20_utility {u w : ℝ → ℝ} {C N σ ψ ε : ℝ} {y n a z d v : ℝ → ℝ}
    (hK : deriv u C * C ≠ 0) (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hψ : iteratedDeriv 2 w N * N = ψ * deriv w N)
    (hEff : deriv w N * N = -(deriv u C * C)) (hden : σ + ψ ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / 2 * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, n s = y s - a s + d s) :
    (fun s => ((u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) -
        (u C + w N)) / (deriv u C * C)
        - (-(1 / 2) * ((σ + ψ) * (y s - (1 + ψ) / (σ + ψ) * a s) ^ 2 + ε * v s) +
          Gali.MonetaryPolicyDesign.Welfare.tip (u C + w N) (deriv u C * C) σ ψ 0 (a s) (z s) /
            (deriv u C * C)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hT : Gali.MonetaryPolicyDesign.Welfare.bigTheta 0 ε = 1 := by
    simp [Gali.MonetaryPolicyDesign.Welfare.bigTheta]
  have h := Gali.MonetaryPolicyDesign.Welfare.period_utility_normalised (α := 0) (ε := ε)
    (y := y) (n := n) (a := a) (z := z) (d := d) (v := v) hK hu hw hσ hψ (by rw [hEff]; ring)
    (by norm_num) (by simpa using hden) hy ha hz hv
    (by rw [hT]; simpa using hd) (fun s => by rw [hn s]; ring)
  have hg : Gali.MonetaryPolicyDesign.Welfare.gapCoeff σ ψ 0 = σ + ψ := by
    simp [Gali.MonetaryPolicyDesign.Welfare.gapCoeff]
  have hp : Gali.MonetaryPolicyDesign.Welfare.psiYA σ ψ 0 = (1 + ψ) / (σ + ψ) := by
    simp [Gali.MonetaryPolicyDesign.Welfare.psiYA]
  rw [hg, hp, hT, div_one] at h
  exact h

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The three-equation model: the IS curve and the New Keynesian Phillips curve

AKMM, §18.3, pp. 543–544, and Appendix 18.A.1, pp. 871–872.

**The IS curve (18.15).** Under perfect foresight the log of the Euler equation (18.5) is exact,
and with `C = Y` and natural output (18.13) it gives
`x_t = x_{t+1} − σ⁻¹(î_t − π̂_{t+1} − r^n_t)` with
`r^n_t = −log β + σ(1+ψ)/(σ+ψ)(log A_{t+1} − log A_t)` (`eq_18_15_exact`). The book prints
`(Â_t − E_tÂ_{t+1})`: that sign is wrong (`rn_printed_iff`: the printed equation holds only when
productivity is expected constant). Under uncertainty, from the log-linear Euler equation
`σ ŷ_t = σ E_t ŷ_{t+1} − (î_t − E_t π_{t+1} + log β)` (logs taken inside `E_t`, footnote 9), the
same algebra gives (18.15) with `r^n_t = −log β + σ(1+ψ)/(σ+ψ)(E_t a_{t+1} − a_t)` for any
expectation system (`eq_18_15`).

**The rule (18.17).** With `î = log(1 + i)` as in (18.15), (18.17) has no intercept, so it is not
consistent with the zero-inflation steady state unless `β = 1` (`rule_18_17_no_steady_state`);
the rule needs the intercept `−log β` (the book's `ī`), as in the rule on p. 543.

**The Phillips curve (18.16).** (18.A.1) in present-value form gives (18.A.2)
(`eq_18_A_2_pv`, `eq_18_A_2`); (18.A.3) is the derivative of (18.10) at zero inflation
(`eq_18_A_3`); combined they give (18.A.4) (`eq_18_A_4`); dispersion drops out to first order
(`eq_18_A_dispersion`, `nk_dispersion_hat_zero`); (18.A.5)–(18.A.6) hold exactly in logs, with
the dispersion term `ψ log D` (`eq_18_A_5_exact`), so `ŵ − Â = (σ+ψ) x` when `D = 1`; and (18.16)
follows (`eq_18_16`), with `κ > 0` decreasing in `θ` (`nk_kappa_pos`, `nk_kappa_antitone`).
-/

namespace AKMM.NominalFrictions

open Filter Topology Finset Gali.BasicNewKeynesianModel

/-- AKMM, (18.16), p. 544: the slope `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ`. -/
noncomputable def nfKappa (β θ σ ψ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) * (σ + ψ) / θ

/-- **AKMM, (18.15), p. 543 (corrected), perfect foresight, exact**: with `C = Y`, the Euler
equation (18.5) and natural output (18.13) at `t` and `t + 1`, the output gap satisfies
`x_t = x_{t+1} − σ⁻¹(log(1+i_t) − log(1+π_{t+1}) − r^n_t)`,
`r^n_t = −log β + σ(1+ψ)/(σ+ψ)(log A_{t+1} − log A_t)`. -/
theorem eq_18_15_exact {β σ ψ mu i π' Y₀ Y₁ A₀ A₁ : ℝ} (hσ : σ ≠ 0) (hβ : 0 < β)
    (hmu : 0 < mu) (hY₀ : 0 < Y₀) (hY₁ : 0 < Y₁) (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hi : 0 < 1 + i) (hπ : 0 < 1 + π')
    (heuler : Y₀ ^ (-σ) = β * ((1 + i) / (1 + π') * Y₁ ^ (-σ))) :
    nfGap Y₀ (mu ^ (-1 / (σ + ψ)) * A₀ ^ ((1 + ψ) / (σ + ψ))) =
      nfGap Y₁ (mu ^ (-1 / (σ + ψ)) * A₁ ^ ((1 + ψ) / (σ + ψ))) -
        σ⁻¹ * (Real.log (1 + i) - Real.log (1 + π') -
          (-Real.log β + σ * (1 + ψ) / (σ + ψ) * (Real.log A₁ - Real.log A₀))) := by
  have hl := congrArg Real.log heuler
  rw [Real.log_rpow hY₀, Real.log_mul hβ.ne' (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_div hi.ne' hπ.ne', Real.log_rpow hY₁] at hl
  rw [nat_gap_loglinear hmu hA₀, nat_gap_loglinear hmu hA₁]
  have hσi : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  have e : σ⁻¹ * (σ * (1 + ψ) / (σ + ψ)) = (1 + ψ) / (σ + ψ) := by
    rw [← mul_div_assoc, ← mul_assoc, hσi, one_mul]
  linear_combination (-σ⁻¹) * hl - (Real.log Y₀ - Real.log Y₁) * hσi -
    (Real.log A₁ - Real.log A₀) * e

/-- **AKMM, p. 543 (the printed natural rate)**: given the exact relation of `eq_18_15_exact`,
the IS equation with the printed `r^n = −log β + σ(1+ψ)/(σ+ψ)(log A_t − log A_{t+1})` also
holds iff `log A_{t+1} = log A_t` (for `σ, 1 + ψ ≠ 0`, `σ + ψ ≠ 0`). -/
theorem rn_printed_iff {β σ ψ x₀ x₁ ii pp a₀ a₁ : ℝ} (hσ : σ ≠ 0) (hψ : 1 + ψ ≠ 0)
    (hs : σ + ψ ≠ 0)
    (hcorr : x₀ = x₁ - σ⁻¹ * (ii - pp - (-Real.log β + σ * (1 + ψ) / (σ + ψ) * (a₁ - a₀)))) :
    x₀ = x₁ - σ⁻¹ * (ii - pp - (-Real.log β + σ * (1 + ψ) / (σ + ψ) * (a₀ - a₁))) ↔ a₁ = a₀ := by
  constructor
  · intro h
    have h2 : σ⁻¹ * (σ * (1 + ψ) / (σ + ψ)) * (2 * (a₁ - a₀)) = 0 := by
      linear_combination h - hcorr
    have hc : σ⁻¹ * (σ * (1 + ψ) / (σ + ψ)) ≠ 0 :=
      mul_ne_zero (inv_ne_zero hσ) (div_ne_zero (mul_ne_zero hσ hψ) hs)
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hc
    · linarith
  · intro h; rw [h] at hcorr ⊢; exact hcorr

/-- **AKMM, (18.15), p. 543 (corrected), under uncertainty**: if
`σ y_t = σ E_t y_{t+1} − (î_t − E_t π_{t+1} + log β)` (the log-linear Euler equation, footnote 9)
and natural output is `y^n = c + ψ_a a` with `ψ_a = (1+ψ)/(σ+ψ)` (18.13), then
`x_t = E_t x_{t+1} − σ⁻¹(î_t − E_t π_{t+1} − r^n_t)` with
`r^n_t = −log β + σψ_a(E_t a_{t+1} − a_t)`. -/
theorem eq_18_15 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ ψ c : ℝ} (hσ : σ ≠ 0)
    {y yn a ii pinf : ℕ → Ω → ℝ} (t : ℕ)
    (heuler : σ • y t = σ • 𝔼.E t (y (t + 1)) - (ii t - 𝔼.E t (pinf (t + 1)) +
      fun _ => Real.log β))
    (hyn : ∀ s, yn s = (fun _ => c) + ((1 + ψ) / (σ + ψ)) • a s) :
    y t - yn t = 𝔼.E t (y (t + 1) - yn (t + 1)) - σ⁻¹ • (ii t - 𝔼.E t (pinf (t + 1)) -
      ((fun _ => -Real.log β) + (σ * ((1 + ψ) / (σ + ψ))) • (𝔼.E t (a (t + 1)) - a t))) := by
  rw [hyn t, hyn (t + 1), map_sub, map_add, 𝔼.const, map_smul]
  funext ω
  have h := congrFun heuler ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  field_simp
  linear_combination h

/-- **AKMM, (18.17), p. 544**: with `î = log(1 + i)` as in (18.15) and `r^n = −log β` (constant
productivity), a zero-inflation, zero-gap steady state with `ω = 0` satisfies (18.15) only if
`î = −log β`, while the printed rule (18.17) gives `î = 0`; both hold only if `β = 1`. -/
theorem rule_18_17_no_steady_state {β σ ii : ℝ} (hβ : 0 < β) (hσ : σ ≠ 0)
    (his : (0 : ℝ) = 0 - σ⁻¹ * (ii - 0 - -Real.log β)) (hrule : ii = 0) : β = 1 := by
  rw [hrule] at his
  have : Real.log β = 0 := by
    have h := his
    field_simp at h
    linarith
  rcases Real.log_eq_zero.1 this with h | h | h <;> [linarith; exact h; linarith]

/-- **AKMM, (18.A.2), p. 871 (from the present value)**: if the reset price satisfies
`p̂^R_t = (1 − βθ) ∑_k (βθ)^k (m_{t+k} + P̂_{t+k} − P̂_t)` (the log-linearised (18.A.1) with
`p̂^R_{t,τ} = p̂^R_t − (P̂_τ − P̂_t)` and `∑ (βθ)^k = 1/(1 − βθ)`) and the series converges, then
`p̂^R_t = (1 − βθ) m_t + βθ (p̂^R_{t+1} + P̂_{t+1} − P̂_t)` (perfect foresight). -/
theorem eq_18_A_2 {β θ : ℝ} {m P pR : ℕ → ℝ} (t : ℕ)
    (hs : ∀ s, Summable fun k => (β * θ) ^ k * (m (s + k) + P (s + k) - P s))
    (hpv : ∀ s, pR s = (1 - β * θ) * ∑' k, (β * θ) ^ k * (m (s + k) + P (s + k) - P s))
    (hs1 : Summable fun k : ℕ => (β * θ) ^ k) :
    pR t = (1 - β * θ) * m t + β * θ * (pR (t + 1) + P (t + 1) - P t) := by
  rw [hpv t, hpv (t + 1), (hs t).tsum_eq_zero_add]
  have e : ∀ k, (β * θ) ^ (k + 1) * (m (t + (k + 1)) + P (t + (k + 1)) - P t) =
      β * θ * ((β * θ) ^ k * (m (t + 1 + k) + P (t + 1 + k) - P (t + 1)) +
        (β * θ) ^ k * (P (t + 1) - P t)) := by
    intro k
    rw [show t + (k + 1) = t + 1 + k by ring, pow_succ]; ring
  simp_rw [e]
  rw [tsum_mul_left, (hs (t + 1)).tsum_add (hs1.mul_right _), tsum_mul_right]
  have hb : ‖β * θ‖ < 1 := summable_geometric_iff_norm_lt_one.1 hs1
  have hb1 : β * θ < 1 := lt_of_abs_lt (by rwa [Real.norm_eq_abs] at hb)
  have h0 : (1 : ℝ) - β * θ ≠ 0 := by linarith
  rw [tsum_geometric_of_norm_lt_one hb]
  simp only [pow_zero, one_mul, add_zero]
  field_simp
  ring

/-- **AKMM, (18.A.2), p. 871, under uncertainty**: the recursive form
`p̂^R_t = (1 − βθ) m_t + βθ E_t(p̂^R_{t+1} + π_{t+1})` as a definition of the reset-price
dynamics for any expectation system (used by `eq_18_A_4`). -/
def ResetRecursion {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β θ : ℝ)
    (m pR infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pR t = (1 - β * θ) • m t + (β * θ) • 𝔼.E t (pR (t + 1) + infl (t + 1))

/-- **AKMM, (18.A.2)–(18.A.3), p. 872 (a concrete instance)**: under perfect foresight, the
geometric paths `p̂^R_t = cρᵗ`, `π_t = (1 − θ)/θ · cρᵗ`, marginal cost
`m_t = cρᵗ(1 − βρ)/(1 − βθ)` and output gap `x_t = m_t/(σ + ψ)` satisfy the reset-price
recursion `ResetRecursion`, the inflation relation (18.A.3) and `m = (σ + ψ)x`: all the
hypotheses of `eq_18_A_4`, `eq_18_16` and `eq_18_23` (`βθ ≠ 1`, `θ ≠ 0`, `σ + ψ ≠ 0`). For
`c ≠ 0` the paths are nonzero. -/
theorem reset_recursion_instance {β θ σ ψ c ρ : ℝ} (hβθ : β * θ ≠ 1) (hθ : θ ≠ 0)
    (hs : σ + ψ ≠ 0) :
    ResetRecursion perfectForesight β θ
        (fun t _ => c * ρ ^ t * (1 - β * ρ) / (1 - β * θ)) (fun t _ => c * ρ ^ t)
        (fun t _ => (1 - θ) / θ * (c * ρ ^ t)) ∧
      (∀ s, (fun _ => (1 - θ) / θ * (c * ρ ^ s) : Unit → ℝ) =
        ((1 - θ) / θ) • (fun _ => c * ρ ^ s : Unit → ℝ)) ∧
      (∀ s, (fun _ => c * ρ ^ s * (1 - β * ρ) / (1 - β * θ) : Unit → ℝ) =
        (σ + ψ) • (fun _ => c * ρ ^ s * (1 - β * ρ) / (1 - β * θ) / (σ + ψ) : Unit → ℝ)) ∧
      (c ≠ 0 → (fun _ => c * ρ ^ 0 : Unit → ℝ) ≠ 0) := by
  have h1 : (1 : ℝ) - β * θ ≠ 0 := sub_ne_zero.2 (Ne.symm hβθ)
  refine ⟨fun t => ?_, fun s => ?_, fun s => ?_, fun hc h => ?_⟩
  · funext ω
    change c * ρ ^ t = (1 - β * θ) * (c * ρ ^ t * (1 - β * ρ) / (1 - β * θ)) +
      β * θ * (c * ρ ^ (t + 1) + (1 - θ) / θ * (c * ρ ^ (t + 1)))
    field_simp
    ring
  · funext ω; simp only [Pi.smul_apply, smul_eq_mul]
  · funext ω; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  · have := congrFun h ()
    simp only [pow_zero, mul_one, Pi.zero_apply] at this
    exact hc this

/-- **AKMM, (18.A.3), p. 872**: the log-linearisation of (18.10). As a function of
`z = log p^R`, `log(1 + π) = (1/(ε − 1)) log((1 − (1 − θ) e^{(1−ε)z})/θ)` has derivative
`(1 − θ)/θ` at the zero-inflation steady state `z = 0`. -/
theorem eq_18_A_3 {θ ε : ℝ} (hθ : 0 < θ) (hε : ε ≠ 1) :
    HasDerivAt (fun z => 1 / (ε - 1) * Real.log ((1 - (1 - θ) * Real.exp ((1 - ε) * z)) / θ))
      ((1 - θ) / θ) 0 := by
  have hε1 : ε - 1 ≠ 0 := sub_ne_zero.2 hε
  have hg : HasDerivAt (fun z => (1 - (1 - θ) * Real.exp ((1 - ε) * z)) / θ)
      (-(1 - θ) * (1 - ε) / θ) 0 := by
    have h1 : HasDerivAt (fun z : ℝ => (1 - ε) * z) (1 - ε) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - ε)
    have h2 := ((h1.exp.const_mul (1 - θ)).const_sub 1).div_const θ
    convert h2 using 1
    simp only [mul_zero, Real.exp_zero, one_mul]
    ring
  have hg0 : (1 - (1 - θ) * Real.exp ((1 - ε) * 0)) / θ = 1 := by
    simp [div_self hθ.ne']
  have hl := (hg.log (by rw [hg0]; norm_num)).const_mul (1 / (ε - 1))
  rw [hg0] at hl
  convert hl using 1
  field_simp
  ring

/-- **AKMM, (18.A.3) and (18.10), p. 872**: (18.A.3) is the derivative of the exact relation
(18.10): for `p^R = e^z`, `log` of the right side of (18.10) is the function of `eq_18_A_3`. -/
theorem eq_18_A_3_exact {θ ε z : ℝ}
    (hpos : 0 < (1 - (1 - θ) * Real.exp z ^ (1 - ε)) / θ) :
    Real.log (((1 - (1 - θ) * Real.exp z ^ (1 - ε)) / θ) ^ (1 / (ε - 1))) =
      1 / (ε - 1) * Real.log ((1 - (1 - θ) * Real.exp ((1 - ε) * z)) / θ) := by
  rw [Real.log_rpow hpos, ← Real.exp_mul, mul_comm z]

/-- **AKMM, (18.A.4), p. 872**: if the reset price follows (18.A.2) and inflation is
`π = (1 − θ)/θ · p̂^R` (18.A.3) at every date, then
`π_t = (1 − θ)(1 − βθ)/θ · m_t + β E_t π_{t+1}` (`θ ∈ (0, 1)`). -/
theorem eq_18_A_4 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β θ : ℝ} (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1)
    {m pR infl : ℕ → Ω → ℝ} (hrec : ResetRecursion 𝔼 β θ m pR infl)
    (h3 : ∀ s, infl s = ((1 - θ) / θ) • pR s) (t : ℕ) :
    infl t = ((1 - θ) * (1 - β * θ) / θ) • m t + β • 𝔼.E t (infl (t + 1)) := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ1)
  have hp : ∀ s, pR s = (θ / (1 - θ)) • infl s := by
    intro s; rw [h3 s, smul_smul, div_mul_div_cancel₀ h1θ, div_self hθ0, one_smul]
  have hsum : pR (t + 1) + infl (t + 1) = (1 / (1 - θ)) • infl (t + 1) := by
    rw [hp (t + 1)]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [h3 t, hrec t, hsum, map_smul]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **AKMM, p. 872 (dispersion to first order)**: the log of the dispersion recursion (18.12),
`log[(1 − θ)(e^{s a})^{−ε} + θ(e^{s b})^ε e^{s c}]`, has derivative
`−ε(1 − θ) a + θ ε b + θ c` at the steady state `s = 0` (`D̄ = p̄^R = 1 + π̄ = 1`). -/
theorem eq_18_A_dispersion (θ ε a b c : ℝ) :
    HasDerivAt (fun s => Real.log ((1 - θ) * (Real.exp (s * a)) ^ (-ε) +
        θ * (Real.exp (s * b)) ^ ε * Real.exp (s * c)))
      (-ε * (1 - θ) * a + θ * ε * b + θ * c) 0 := by
  have e : ∀ s, (1 - θ) * (Real.exp (s * a)) ^ (-ε) + θ * (Real.exp (s * b)) ^ ε *
      Real.exp (s * c) = (1 - θ) * Real.exp (-ε * a * s) + θ * Real.exp ((ε * b + c) * s) := by
    intro s
    rw [← Real.exp_mul, ← Real.exp_mul, mul_assoc θ, ← Real.exp_add]
    congr 3 <;> ring
  simp_rw [e]
  have h1 : HasDerivAt (fun s => (1 - θ) * Real.exp (-ε * a * s) + θ * Real.exp ((ε * b + c) * s))
      ((1 - θ) * (Real.exp (-ε * a * 0) * (-ε * a)) +
        θ * (Real.exp ((ε * b + c) * 0) * (ε * b + c))) 0 := by
    have ha : HasDerivAt (fun s : ℝ => -ε * a * s) (-ε * a) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-ε * a)
    have hb : HasDerivAt (fun s : ℝ => (ε * b + c) * s) (ε * b + c) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (ε * b + c)
    exact (ha.exp.const_mul _).add (hb.exp.const_mul _)
  have h0 : (1 - θ) * Real.exp (-ε * a * 0) + θ * Real.exp ((ε * b + c) * 0) = 1 := by simp
  have hl := h1.log (by rw [h0]; norm_num)
  rw [h0] at hl
  convert hl using 1
  simp
  ring

/-- **AKMM, p. 872**: with (18.A.3), `b = (1 − θ)/θ · a`, the first-order dispersion
recursion is `D̂_t = θ D̂_{t−1}`. -/
theorem nk_dispersion_hat_rec {θ ε a c : ℝ} (hθ : θ ≠ 0) :
    -ε * (1 - θ) * a + θ * ε * ((1 - θ) / θ * a) + θ * c = θ * c := by
  field_simp; ring

/-- **AKMM, p. 872**: `D̂_t = θ D̂_{t−1}` with no initial dispersion gives `D̂_t = 0` for all
`t`: price dispersion does not affect the first-order dynamics. -/
theorem nk_dispersion_hat_zero {θ : ℝ} {D : ℕ → ℝ} (h0 : D 0 = 0)
    (hrec : ∀ t, D (t + 1) = θ * D t) (t : ℕ) : D t = 0 := by
  induction t with
  | zero => exact h0
  | succ t ih => rw [hrec t, ih, mul_zero]

/-- **AKMM, (18.A.5)–(18.A.6), p. 872, exact in logs**: with `C = Y`, (18.6) `C^{−σ} w = L^ψ`,
(18.11) `Y = A L/D` and natural output (18.13),
`log(w/A) + log µ = (σ + ψ)(log Y − log Y^n) + ψ log D`. Around the steady state
`w̄/Ā = 1/µ`, `D̄ = 1`, this is `ŵ − Â = (σ + ψ) x + ψ D̂`, and with `D̂ = 0` to first order
(`nk_dispersion_hat_zero`), `ŵ − Â = (σ + ψ)(Ŷ − Ŷ^n)`. -/
theorem eq_18_A_5_exact {σ ψ mu w A D Y L : ℝ} (hs : σ + ψ ≠ 0) (hmu : 0 < mu) (hw : 0 < w)
    (hA : 0 < A) (hD : 0 < D) (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L / D)
    (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Real.log (w / A) + Real.log mu =
      (σ + ψ) * nfGap Y (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) + ψ * Real.log D := by
  have hLe : L = D * Y / A := by rw [hprod]; field_simp
  have hlog := congrArg Real.log hlab
  rw [Real.log_mul (Real.rpow_pos_of_pos hY _).ne' hw.ne', Real.log_rpow hY,
    Real.log_rpow hL, hLe, Real.log_div (by positivity) hA.ne',
    Real.log_mul hD.ne' hY.ne'] at hlog
  rw [nat_gap_loglinear hmu hA, Real.log_rpow hmu, Real.log_div hw.ne' hA.ne']
  have e1 : (σ + ψ) * (-1 / (σ + ψ) * Real.log mu) = -Real.log mu := by field_simp
  have e2 : (σ + ψ) * ((1 + ψ) / (σ + ψ) * Real.log A) = (1 + ψ) * Real.log A := by field_simp
  linear_combination hlog + e1 + e2

/-- **AKMM, (18.16), p. 544**: from (18.A.4) and `m_t = ŵ_t − Â_t = (σ + ψ) x_t`,
`π_t = κ x_t + β E_t π_{t+1}`, `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ`. -/
theorem eq_18_16 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β θ σ ψ : ℝ} (hθ0 : θ ≠ 0)
    (hθ1 : θ ≠ 1) {m x pR infl : ℕ → Ω → ℝ} (hrec : ResetRecursion 𝔼 β θ m pR infl)
    (h3 : ∀ s, infl s = ((1 - θ) / θ) • pR s) (hm : ∀ s, m s = (σ + ψ) • x s) (t : ℕ) :
    infl t = nfKappa β θ σ ψ • x t + β • 𝔼.E t (infl (t + 1)) := by
  rw [eq_18_A_4 𝔼 hθ0 hθ1 hrec h3 t, hm t, smul_smul, nfKappa]
  congr 2
  ring

/-- AKMM, p. 544: `κ > 0` for `θ ∈ (0, 1)`, `βθ < 1`, `σ + ψ > 0`. -/
theorem nk_kappa_pos {β θ σ ψ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hs : 0 < σ + ψ) : 0 < nfKappa β θ σ ψ := by
  unfold nfKappa
  have : 0 < 1 - β * θ := by linarith
  have : 0 < 1 - θ := by linarith
  positivity

/-- **AKMM, p. 544**: "the slope of the Phillips curve is larger if prices are more flexible
(lower `θ`)": for `0 ≤ β ≤ 1` and `σ + ψ > 0`, `κ` is strictly decreasing in `θ` on `(0, 1)`. -/
theorem nk_kappa_antitone {β σ ψ θ₁ θ₂ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hs : 0 < σ + ψ)
    (h0 : 0 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ < 1) : nfKappa β θ₂ σ ψ < nfKappa β θ₁ σ ψ := by
  unfold nfKappa
  have hθ2 : 0 < θ₂ := by linarith
  have a1 : (1 - θ₂) / θ₂ < (1 - θ₁) / θ₁ := by
    rw [div_lt_div_iff₀ hθ2 h0]; nlinarith
  have a2 : 1 - β * θ₂ ≤ 1 - β * θ₁ := by nlinarith
  have b2 : 0 < 1 - β * θ₂ := by nlinarith
  have c1 : 0 ≤ (1 - θ₂) / θ₂ := div_nonneg (by linarith) hθ2.le
  have e : ∀ θ : ℝ, (1 - θ) * (1 - β * θ) * (σ + ψ) / θ =
      (1 - θ) / θ * (1 - β * θ) * (σ + ψ) := fun θ => by ring
  rw [e, e]
  have := mul_lt_mul_of_pos_of_nonneg' a1 a2 b2 (by
    have : 0 < (1 - θ₁) / θ₁ := div_pos (by linarith) h0
    linarith)
  nlinarith [mul_lt_mul_of_pos_right this hs]

/-- AKMM, p. 544: `κ` is increasing in the elasticity `σ + ψ` of marginal cost to output. -/
theorem nk_kappa_mono_sens {β θ σ ψ σ' ψ' : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (h : σ + ψ < σ' + ψ') : nfKappa β θ σ ψ < nfKappa β θ σ' ψ' := by
  unfold nfKappa
  have : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  rw [div_lt_div_iff_of_pos_right hθ0]
  nlinarith

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Determinacy and the Taylor principle

AKMM, §18.3, p. 544, condition (18.18), and Appendix 18.A.2, p. 873 (Bullard–Mitra by the
Jury criterion).

* `det_system`: substituting the rule into the IS curve and the Phillips curve gives the book's
  system `βσ x_{t+1} = (βσ + βφ_x + κ) x_t + (βφ_π − 1) π_t`, `β π_{t+1} = π_t − κ x_t`.
* `det_inverse`, `det_coeff_eq_AT`: the book's inverse and coefficient matrix; the latter is
  Galí's `A_T`. `det_a1`, `det_a0`: the coefficients `a₁ = −tr`, `a₀ = det` of the
  characteristic polynomial `λ² + a₁λ + a₀`.
* `det_jury_iff`: for `σ > 0`, `κ, φ_π, φ_x ≥ 0` and `0 ≤ β ≤ 1` (the book's assumptions), the Jury
  conditions `|a₀| < 1`, `|a₁| < 1 + a₀` hold iff (18.18), `(1 − β)φ_x + κ(φ_π − 1) > 0`;
  `det_roots_iff`: equivalently both roots lie inside the unit circle (Galí's
  `schurStable_iff_roots`).
* `eq_18_18`: the three-equation model has a unique bounded equilibrium iff (18.18)
  (Galí's `determinate_iff_BM`, for `κ > 0`, `0 < β < 1`).
* `det_taylor_sufficient`, `det_taylor_necessary`: `φ_π > 1` suffices; with `φ_x = 0` it is
  necessary.
* **Correction**: `|a₀| < 1` is not automatic as the book says: at `β = 1` with
  `φ_x = φ_π = 0`, `a₀ = 1` (`det_a0_not_automatic`). It does follow from (18.18), so the
  equivalence stands.
-/

namespace AKMM.NominalFrictions

open Gali.BasicNewKeynesianModel Gali.BasicNewKeynesianModel.TaylorRuleSystem

/-- **AKMM, App. 18.A.2, p. 873**: with the IS curve `x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1})`, the
Phillips curve `π_t = κx_t + βπ_{t+1}` and the rule `i_t = φ_π π_t + φ_x x_t` (deterministic,
`π* = 0`, in deviations from the steady state), `βσ x_{t+1} = (βσ + βφ_x + κ) x_t +
(βφ_π − 1) π_t` and `β π_{t+1} = π_t − κ x_t`. -/
theorem det_system {β σ κ φπ φx x x' π π' i : ℝ} (hσ : σ ≠ 0)
    (his : x = x' - σ⁻¹ * (i - π')) (hpc : π = κ * x + β * π') (hrule : i = φπ * π + φx * x) :
    β * σ * x' = (β * σ + β * φx + κ) * x + (β * φπ - 1) * π ∧ β * π' = π - κ * x := by
  have h1 : σ * x' = σ * x + i - π' := by
    rw [his]; field_simp; ring
  refine ⟨?_, by linarith⟩
  rw [hrule] at h1
  linear_combination β * h1 + hpc

/-- AKMM, p. 873: the matrix on the left of the system, `diag(βσ, β)`. -/
def detM0 (β σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![β * σ, 0; 0, β]

/-- AKMM, p. 873: the matrix on the right, `[[βσ + βφ_x + κ, βφ_π − 1], [−κ, 1]]`. -/
def detM1 (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β * σ + β * φx + κ, β * φπ - 1; -κ, 1]

/-- AKMM, p. 873: the printed inverse,
`(1/(β(σ + φ_x + κφ_π))) [[1, 1 − βφ_π], [κ, βσ + βφ_x + κ]]`. -/
noncomputable def detInv (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (β * (σ + φx + κ * φπ))) • !![1, 1 - β * φπ; κ, β * σ + β * φx + κ]

/-- **AKMM, p. 873**: the printed inverse is the inverse of the right-hand matrix
(`β ≠ 0`, `σ + φ_x + κφ_π ≠ 0`). -/
theorem det_inverse {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hS : σ + φx + κ * φπ ≠ 0) :
    detM1 β σ κ φπ φx * detInv β σ κ φπ φx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [detM1, detInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **AKMM, p. 873**: the coefficient matrix multiplying `(x_{t+1}, π_{t+1})`,
`(1/(σ + φ_x + κφ_π)) [[σ, 1 − βφ_π], [κσ, βσ + βφ_x + κ]]`, is `M₁⁻¹ M₀`, and it is Galí's
`A_T`. -/
theorem det_coeff_eq_AT {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hS : σ + φx + κ * φπ ≠ 0) :
    detInv β σ κ φπ φx * detM0 β σ = AT β σ κ φπ φx ∧
      AT β σ κ φπ φx = (1 / (σ + φx + κ * φπ)) •
        !![σ, 1 - β * φπ; κ * σ, β * σ + β * φx + κ] := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [detM0, detInv, AT, omega, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    all_goals ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [AT, omega, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul,
        Fin.zero_eta, Fin.mk_one] <;> ring

/-- **AKMM, p. 873**: `a₁ = −(σ + βσ + βφ_x + κ)/(σ + φ_x + κφ_π) = −tr A_T`. -/
theorem det_a1 {β σ κ φπ φx : ℝ} (hS : σ + φx + κ * φπ ≠ 0) :
    -tr2 (AT β σ κ φπ φx) = -((σ + β * σ + β * φx + κ) / (σ + φx + κ * φπ)) := by
  rw [tr2_AT hS]; ring

/-- **AKMM, p. 873**: `a₀ = βσ/(σ + φ_x + κφ_π) = det A_T`. -/
theorem det_a0 {β σ κ φπ φx : ℝ} (hS : σ + φx + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φx) = β * σ / (σ + φx + κ * φπ) := by
  rw [det2_AT hS]; ring

/-- **AKMM, (18.18) and App. 18.A.2, p. 873 (Jury)**: for `σ > 0`, `κ, φ_π, φ_x ≥ 0` and
`0 ≤ β ≤ 1`, the Jury conditions `|a₀| < 1` and `|a₁| < 1 + a₀` hold iff
`(1 − β)φ_x + κ(φ_π − 1) > 0`. -/
theorem det_jury_iff {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    SchurStable (tr2 (AT β σ κ φπ φx)) (det2 (AT β σ κ φπ φx)) ↔
      0 < (1 - β) * φx + κ * (φπ - 1) := by
  have hS : 0 < σ + φx + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  unfold SchurStable
  have hT0 : 0 ≤ (σ * (1 + β) + κ + β * φx) / (σ + φx + κ * φπ) := by positivity
  have hD0 : 0 ≤ σ * β / (σ + φx + κ * φπ) := by positivity
  rw [abs_of_nonneg hD0, abs_of_nonneg hT0, div_lt_one hS,
    show 1 + σ * β / (σ + φx + κ * φπ) = (σ + φx + κ * φπ + σ * β) / (σ + φx + κ * φπ) by
      field_simp, div_lt_div_iff_of_pos_right hS]
  constructor
  · rintro ⟨-, h⟩; nlinarith
  · intro h
    refine ⟨by nlinarith [mul_nonneg hβ0 hφx, mul_nonneg (sub_nonneg.2 hβ1) hσ.le], by nlinarith⟩

/-- **AKMM, p. 873 (correction)**: the book says `|a₀| < 1` "holds as we assume `β ∈ [0, 1]`,
all the parameters are weakly positive and `σ` is strictly positive"; at `β = 1`,
`φ_x = φ_π = 0`, `a₀ = 1`. -/
theorem det_a0_not_automatic {σ κ : ℝ} (hσ : 0 < σ) : det2 (AT 1 σ κ 0 0) = 1 := by
  rw [det_a0 (by simpa using hσ.ne')]; simp [hσ.ne']

/-- **AKMM, App. 18.A.2, p. 873**: under the assumptions of `det_jury_iff`, both roots of the
characteristic polynomial `λ² + a₁λ + a₀` of the coefficient matrix lie strictly inside the
unit circle iff (18.18) (Galí's `schurStable_iff_roots`, `T = −a₁`, `D = a₀`). -/
theorem det_roots_iff {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    (‖root₁ (tr2 (AT β σ κ φπ φx)) (det2 (AT β σ κ φπ φx))‖ < 1 ∧
      ‖root₂ (tr2 (AT β σ κ φπ φx)) (det2 (AT β σ κ φπ φx))‖ < 1) ↔
      0 < (1 - β) * φx + κ * (φπ - 1) :=
  (schurStable_iff_roots _ _).symm.trans (det_jury_iff hσ hκ hβ0 hβ1 hφπ hφx)

/-- **AKMM, (18.18), p. 544**: the three-equation model (in Galí's form
`x_t = A_T E_t x_{t+1} + B_T u_t`, `TaylorRuleSystem.equilibrium_iff_solves`) has a unique
bounded equilibrium for every bounded forcing iff `(1 − β)φ_x + κ(φ_π − 1) > 0`
(Galí's `determinate_iff_BM`, `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_x ≥ 0`). -/
theorem eq_18_18 {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {β σ κ φπ φx : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    𝔼.Determinate (AT β σ κ φπ φx) ↔ 0 < (1 - β) * φx + κ * (φπ - 1) := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ0 hβ1 hφπ hφx]
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 544**: "`φ_π > 1` is sufficient for this condition to hold". -/
theorem det_taylor_sufficient {β κ φπ φx : ℝ} (hκ : 0 < κ) (hβ1 : β ≤ 1) (hφx : 0 ≤ φx)
    (h : 1 < φπ) : 0 < (1 - β) * φx + κ * (φπ - 1) := by
  have := mul_nonneg (sub_nonneg.2 hβ1) hφx
  nlinarith

/-- **AKMM, p. 544**: "and necessary if `φ_x = 0`". -/
theorem det_taylor_necessary {β κ φπ : ℝ} (hκ : 0 < κ) :
    0 < (1 - β) * 0 + κ * (φπ - 1) ↔ 1 < φπ := by
  rw [mul_zero, zero_add]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith
  · intro h; nlinarith

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy strategies

AKMM, §18.4.2–18.4.4, pp. 547–550.

* **The divine coincidence** (§18.4.2): a closed output gap at all dates forces zero inflation in
  every bounded equilibrium (`pol_divine_coincidence`, from Galí's `infl_zero_of_gap_zero` and
  `divine_coincidence`).
* **Cost-push shocks** (18.21): with `x ≡ 0`, bounded inflation solves
  `π_t = ∑_{k<K} β^k η_{t+k} + β^K π_{t+K}`; a one-period shock `η₀ ≠ 0` gives `π₀ = η₀ ≠ 0`
  (`pol_costpush_iterate`, `pol_costpush_breaks`).
* **Flexible inflation targeting** (18.22) with `π* = 0`, `λ = κ/ε` is the loss (18.20)
  (`pol_loss_22_eq_20`).
* **Price-level targeting** (§18.4.3): in the log-linear model with the rule
  `i_t = r^n_t + φ_P p̂_t` (the book's rule with `φ_x = 0` and the natural-rate intercept),
  every `φ_P > 0` gives a unique bounded equilibrium (Galí's Exercise 4.6, `pol_price_level_rule`).
* **Discretion** (§18.4.4): after a one-period cost-push shock, the economy is in steady state
  from date 1, `π₀ = κ x₀ + η₀`, and the date-0 problem gives `x₀ = −κη₀/(κ² + λ)`,
  `π₀ = λη₀/(κ² + λ)` (`pol_discretion_date0`); the price level jumps and stays
  (`pol_discretion_price_level`).
* **Commitment** (§18.4.4, Galí's perfect-foresight commitment path): inflation and the output gap
  are smaller in absolute value at date 0 than under discretion, inflation is negative and the gap
  negative afterwards, the price level returns to its initial value (`pol_commitment_path`,
  `pol_commitment_date0`, `pol_commitment_price_level`), commitment strictly beats discretion
  (`pol_commitment_better`), and it is time inconsistent: at date 1 the zero path is feasible with
  zero loss while the commitment continuation has a positive period loss
  (`pol_time_inconsistent`).
-/

namespace AKMM.NominalFrictions

open Filter Topology Finset

/-- **AKMM, §18.4.2, p. 547 (the divine coincidence)**: in Galí's log-linear model (NKPC (18.16)
with any expectation system), if the output gap is zero at every date and inflation is bounded,
inflation is zero at every date (`|β| < 1`); conversely zero inflation forces a zero gap, and then
the nominal rate equals the natural rate (Galí's `divine_coincidence`). -/
theorem pol_divine_coincidence {Ω : Type*} (𝔼 : Gali.MonetaryPolicyDesign.ExpectationSystem Ω)
    {β σ κ : ℝ} (hβ : |β| < 1) (hσ : σ ≠ 0) (hκ : κ ≠ 0) {rn ygap infl i : ℕ → Ω → ℝ}
    (heq : Gali.MonetaryPolicyDesign.OptimalPolicy.Equilibrium 𝔼 β σ κ rn ygap infl i)
    (hb : Gali.MonetaryPolicyDesign.BoundedProc infl) :
    (ygap = 0 ↔ infl = 0) ∧ (ygap = 0 → ∀ t, i t = rn t) :=
  Gali.MonetaryPolicyDesign.OptimalPolicy.divine_coincidence 𝔼 hβ hσ hκ heq hb

/-- AKMM, (18.21), p. 548 (perfect foresight): with `x ≡ 0`,
`π_t = κx_t + βπ_{t+1} + η_t` iterates to `π_t = ∑_{k<K} β^k η_{t+k} + β^K π_{t+K}`. -/
theorem pol_costpush_iterate {β : ℝ} {infl eta : ℕ → ℝ}
    (hpc : ∀ t, infl t = β * infl (t + 1) + eta t) (t K : ℕ) :
    infl t = ∑ k ∈ range K, β ^ k * eta (t + k) + β ^ K * infl (t + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, hpc (t + K), sum_range_succ, show t + K + 1 = t + (K + 1) by ring, pow_succ]
    ring

/-- **AKMM, (18.21), p. 548**: "a policy of setting `x_t = 0` at all dates no longer leads to
`π_t = 0`": with a one-period cost-push shock (`η_t = 0` for `t ≥ 1`), `|β| < 1` and bounded
inflation, `x ≡ 0` gives `π_t = 0` for `t ≥ 1` and `π₀ = η₀`, so `π₀ ≠ 0` when `η₀ ≠ 0`. -/
theorem pol_costpush_breaks {β M : ℝ} (hβ : |β| < 1) {infl eta : ℕ → ℝ}
    (hpc : ∀ t, infl t = β * infl (t + 1) + eta t) (heta : ∀ t, eta (t + 1) = 0)
    (hb : ∀ t, |infl t| ≤ M) : (∀ t, infl (t + 1) = 0) ∧ infl 0 = eta 0 := by
  have hz : ∀ t, infl (t + 1) = 0 := by
    intro t
    have hK : ∀ K, infl (t + 1) = β ^ K * infl (t + 1 + K) := by
      intro K
      rw [pol_costpush_iterate hpc (t + 1) K]
      simp [heta, show ∀ k, t + 1 + k = (t + k) + 1 from fun k => by ring]
    have hg2 : Tendsto (fun K : ℕ => |β| ^ K * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg β) hβ).mul_const M
    have hlim : Tendsto (fun K => β ^ K * infl (t + 1 + K)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun K => ?_) hg2
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (abs_nonneg _) _)
    have he : (fun K => β ^ K * infl (t + 1 + K)) = fun _ => infl (t + 1) :=
      funext fun K => (hK K).symm
    rw [he] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  refine ⟨hz, ?_⟩
  rw [hpc 0, zero_add, hz 0, mul_zero, zero_add]

/-- AKMM, (18.22) and (18.20), p. 548: with `π* = 0` and `λ = κ/ε` the flexible
inflation-targeting loss is the welfare loss (18.20). -/
theorem pol_loss_22_eq_20 {κ ε πt xt πstar lam : ℝ} (hπ : πstar = 0) (hlam : lam = κ / ε) :
    (πt - πstar) ^ 2 + lam * xt ^ 2 = πt ^ 2 + κ / ε * xt ^ 2 := by
  rw [hπ, hlam, sub_zero]

/-- **AKMM, §18.4.3, p. 548 (price-level targeting)**: in the log-linear model (IS (18.15),
NKPC (18.16)), the price-level rule `i_t = r^n_t + φ_P p̂_t` with any `φ_P > 0` yields a unique
bounded equilibrium for every initial price level (Galí's Exercise 4.6, `determinate_of_pos`;
`σ, κ > 0`, `0 < β < 1`). The book states the rule with an output-gap term and a constant
intercept and makes no determinacy claim; this is the case `φ_x = 0` with the natural-rate
intercept. -/
theorem pol_price_level_rule {Ω : Type*} (𝔼 : Gali.MonetaryPolicyDesign.ExpectationSystem Ω)
    {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 0 < φ) :
    Gali.MonetaryPolicyDesign.Ex4_6.Determinate 𝔼 β σ κ φ :=
  Gali.MonetaryPolicyDesign.Ex4_6.determinate_of_pos 𝔼 hσ hκ hβ0 hβ1 hφ

/-- **AKMM, §18.4.4, p. 549 (discretion)**: after a one-period cost-push shock the discretionary
economy is in steady state from date 1, so `π₀ = κ x₀ + η₀`; minimising `π₀² + λ x₀²` gives the
unique minimiser `x₀ = −κη₀/(κ² + λ)`, with `π₀ = λη₀/(κ² + λ)` (`λ > 0`). -/
theorem pol_discretion_date0 {κ lam η x : ℝ} (hlam : 0 < lam) :
    (κ * (-κ * η / (κ ^ 2 + lam)) + η) ^ 2 + lam * (-κ * η / (κ ^ 2 + lam)) ^ 2 ≤
        (κ * x + η) ^ 2 + lam * x ^ 2 ∧
      ((κ * x + η) ^ 2 + lam * x ^ 2 =
          (κ * (-κ * η / (κ ^ 2 + lam)) + η) ^ 2 + lam * (-κ * η / (κ ^ 2 + lam)) ^ 2 ↔
        x = -κ * η / (κ ^ 2 + lam)) ∧
      κ * (-κ * η / (κ ^ 2 + lam)) + η = lam * η / (κ ^ 2 + lam) := by
  have hD : 0 < κ ^ 2 + lam := by positivity
  have key : (κ * x + η) ^ 2 + lam * x ^ 2 = (κ * (-κ * η / (κ ^ 2 + lam)) + η) ^ 2 +
      lam * (-κ * η / (κ ^ 2 + lam)) ^ 2 + (κ ^ 2 + lam) * (x - -κ * η / (κ ^ 2 + lam)) ^ 2 := by
    field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; nlinarith [sq_nonneg (x - -κ * η / (κ ^ 2 + lam))]
  · rw [key]
    constructor
    · intro h
      have : (κ ^ 2 + lam) * (x - -κ * η / (κ ^ 2 + lam)) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1)
    · intro h; rw [h, sub_self]; ring
  · field_simp; ring

/-- AKMM, p. 550: under discretion the price level jumps at date 0 and stays: with `π₀ = π̄`
and `π_t = 0` for `t ≥ 1`, the cumulated inflation `∑_{s ≤ t} π_s` equals `π̄` at every date. -/
theorem pol_discretion_price_level {infl : ℕ → ℝ} (hz : ∀ t, infl (t + 1) = 0) (t : ℕ) :
    ∑ s ∈ range (t + 1), infl s = infl 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, ih, hz t, add_zero]

/-- The one-period cost-push shock `u₀ = η`, `u_t = 0` for `t ≥ 1`, on the perfect-foresight
state space. -/
noncomputable def polShock (η : ℝ) : ℕ → Unit → ℝ := fun t _ => if t = 0 then η else 0

/-- The one-period shock is an AR(1) process with `ρ = 0` under perfect foresight. -/
theorem pol_shock_ar1 (η : ℝ) :
    Gali.DiscretionCommitment.ExpectationSystem.IsAR1 Gali.DiscretionCommitment.perfectForesight 0
      (polShock η) := by
  refine ⟨fun _ => rfl, fun t => ?_⟩
  funext ω
  change polShock η (t + 1) ω = (0 : ℝ) • polShock η t ω
  simp [polShock]

/-- The one-period shock is bounded by `|η|`. -/
theorem pol_shock_bound (η : ℝ) : ∀ t ω, |polShock η t ω| ≤ |η| := by
  intro t ω
  unfold polShock
  split_ifs <;> simp

/-- **AKMM, §18.4.4, pp. 549–550 (the commitment path)**: for a one-period cost-push shock `η`,
Galí's commitment solution has price level `p̂_t = δ^{t+1}η`, inflation
`π_{t+1} = −(1 − δ)δ^{t+1}η` and output gap `x_t = −(κ/λ)δ^{t+1}η`, with `δ ∈ (0, 1)`; under
discretion `π_{t+1} = x_{t+1} = 0` (Galí's `impulse_rho0`; `λ` is the weight in (18.22)). -/
theorem pol_commitment_path {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (t : ℕ) :
    Gali.DiscretionCommitment.Commitment.pHat Gali.DiscretionCommitment.perfectForesight β κ lam
        (polShock η) t () = Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1) * η ∧
      Gali.DiscretionCommitment.Commitment.inflC Gali.DiscretionCommitment.perfectForesight
        β κ lam (polShock η) (t + 1) () =
        -((1 - Gali.DiscretionCommitment.Commitment.del β κ lam) *
          Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1)) * η ∧
      Gali.DiscretionCommitment.Commitment.gapC Gali.DiscretionCommitment.perfectForesight
        β κ lam (polShock η) t () =
        -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1) * η ∧
      0 < Gali.DiscretionCommitment.Commitment.del β κ lam ∧
      Gali.DiscretionCommitment.Commitment.del β κ lam < 1 := by
  obtain ⟨h1, h2, h3, -, -⟩ := Gali.DiscretionCommitment.CommitmentVsDiscretion.impulse_rho0
    Gali.DiscretionCommitment.perfectForesight hβ0 hβ1 hlam hκ.ne' (pol_shock_bound η)
    (pol_shock_ar1 η) (fun t => by funext ω; simp [polShock]) t
  have hd := (Gali.DiscretionCommitment.Commitment.del_mem_Ioo_iff (κ := κ) hβ0 hβ1 hlam
    hκ.le).2 hκ
  refine ⟨?_, ?_, ?_, hd.1, hd.2⟩
  · rw [h1]; simp [polShock]
  · rw [h2]; simp [polShock]
  · rw [h3]; simp [polShock]

/-- **AKMM, §18.4.4, p. 549**: at date 0 commitment gives less inflation and a smaller fall in
output than discretion: for `η > 0`, `0 < π₀^C = δη < λη/(κ² + λ) = π₀^D` and
`x₀^D = −κη/(κ² + λ) < x₀^C = −(κ/λ)δη < 0` (Galí's `commit_coef_lt` at `ρ = 0`). -/
theorem pol_commitment_date0 {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hη : 0 < η) :
    0 < Gali.DiscretionCommitment.Commitment.del β κ lam * η ∧
      Gali.DiscretionCommitment.Commitment.del β κ lam * η < lam * η / (κ ^ 2 + lam) ∧
      -κ * η / (κ ^ 2 + lam) < -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam * η ∧
      -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam * η < 0 := by
  obtain ⟨h0, h1⟩ := Gali.DiscretionCommitment.CommitmentVsDiscretion.commit_coef_lt (ρ := 0)
    (κ := κ) hβ0 hβ1 hlam hκ.ne' (by norm_num)
  simp only [mul_zero, sub_zero, div_one, mul_one,
    Gali.DiscretionCommitment.CommitmentVsDiscretion.psiPi]
    at h0 h1
  set d := Gali.DiscretionCommitment.Commitment.del β κ lam
  have hD : 0 < κ ^ 2 + lam := by positivity
  have h1' : d < lam / (κ ^ 2 + lam) := h1
  refine ⟨mul_pos h0 hη, ?_, ?_, ?_⟩
  · rw [mul_div_right_comm]; exact mul_lt_mul_of_pos_right h1' hη
  · have : d / lam < 1 / (κ ^ 2 + lam) := by
      rw [div_lt_iff₀ hlam]; calc d < lam / (κ ^ 2 + lam) := h1'
        _ = 1 / (κ ^ 2 + lam) * lam := by ring
    have h2 := mul_lt_mul_of_pos_left this (mul_pos hκ hη)
    have e1 : -κ * η / (κ ^ 2 + lam) = -(κ * η * (1 / (κ ^ 2 + lam))) := by ring
    have e2 : -(κ / lam) * d * η = -(κ * η * (d / lam)) := by ring
    rw [e1, e2]; linarith
  · have : 0 < κ / lam * d * η := by positivity
    linarith

/-- **AKMM, p. 550 (the price level under commitment)**: cumulated commitment inflation
`∑_{s ≤ t} π_s = p̂_t = δ^{t+1}η` tends to zero: the long-run price level is unaffected by the
cost-push shock. -/
theorem pol_commitment_price_level {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) :
    (∀ t, ∑ s ∈ range (t + 1), Gali.DiscretionCommitment.Commitment.inflC
        Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) s () =
      Gali.DiscretionCommitment.Commitment.pHat Gali.DiscretionCommitment.perfectForesight
        β κ lam (polShock η) t ()) ∧
    Tendsto (fun t => Gali.DiscretionCommitment.Commitment.pHat
      Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) t ()) atTop (𝓝 0) := by
  refine ⟨fun t => ?_, ?_⟩
  · induction t with
    | zero =>
      simp [Gali.DiscretionCommitment.Commitment.inflC, Gali.DiscretionCommitment.Commitment.inflOf]
    | succ t ih =>
      rw [sum_range_succ, ih]
      simp [Gali.DiscretionCommitment.Commitment.inflC, Gali.DiscretionCommitment.Commitment.inflOf]
  · have hd := (pol_commitment_path (η := η) hβ0 hβ1 hlam hκ 0).2.2.2
    have hp : ∀ t, Gali.DiscretionCommitment.Commitment.pHat
        Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) t () =
        Gali.DiscretionCommitment.Commitment.del β κ lam ^ (t + 1) * η :=
      fun t => (pol_commitment_path hβ0 hβ1 hlam hκ t).1
    simp_rw [hp]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hd.1.le hd.2).comp (tendsto_add_atTop_nat 1)
    simpa using this.mul_const η

/-- **AKMM, §18.4.4, pp. 549–550**: commitment strictly beats discretion: with `η ≠ 0`, the
loss `∑ βᵗ(π_t² + λx_t²)` of the commitment path is strictly below that of the discretionary
path (Galí's `commitment_lt_discretion` under perfect foresight, `ρ = 0`). -/
theorem pol_commitment_better {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hη : η ≠ 0) :
    Gali.DiscretionCommitment.Commitment.expLoss Gali.DiscretionCommitment.perfectForesight β lam
        (Gali.DiscretionCommitment.Commitment.inflC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η))
        (Gali.DiscretionCommitment.Commitment.gapC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η)) () <
      Gali.DiscretionCommitment.Commitment.expLoss Gali.DiscretionCommitment.perfectForesight β lam
        (Gali.DiscretionCommitment.CommitmentVsDiscretion.inflDisc β κ lam 0 (polShock η))
        (Gali.DiscretionCommitment.CommitmentVsDiscretion.gapDisc β κ lam 0 (polShock η)) () :=
  Gali.DiscretionCommitment.CommitmentVsDiscretion.commitment_lt_discretion
    Gali.DiscretionCommitment.perfectForesight
    Gali.DiscretionCommitment.Commitment.perfectForesight_pullOut hβ0 hβ1 hlam hκ.ne'
    (by norm_num) (pol_shock_bound η) (pol_shock_ar1 η) () (by simp [polShock, hη])

/-- **AKMM, p. 550 (time inconsistency)**: at date 1 there is no shock, so the zero path
satisfies the Phillips curve from date 1 with zero loss, whereas the commitment continuation has
a strictly positive period loss at date 1 (`η ≠ 0`): the central bank would like to switch to the
discretionary policy at date 1. -/
theorem pol_time_inconsistent {β κ lam η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hη : η ≠ 0) :
    (∀ t : ℕ, (0 : ℝ) = β * 0 + κ * 0 + polShock η (t + 1) ()) ∧
      0 < Gali.DiscretionCommitment.Commitment.inflC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η) 1 () ^ 2 + lam *
        Gali.DiscretionCommitment.Commitment.gapC Gali.DiscretionCommitment.perfectForesight
          β κ lam (polShock η) 1 () ^ 2 := by
  refine ⟨fun t => by simp [polShock], ?_⟩
  obtain ⟨-, -, h3, hd0, -⟩ := pol_commitment_path (η := η) hβ0 hβ1 hlam hκ 1
  rw [h3]
  have hx : -(κ / lam) * Gali.DiscretionCommitment.Commitment.del β κ lam ^ (1 + 1) * η ≠ 0 := by
    have : 0 < κ / lam := div_pos hκ hlam
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 this.ne') (pow_pos hd0 _).ne') hη
  have := pow_pos (abs_pos.2 hx) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (Gali.DiscretionCommitment.Commitment.inflC
    Gali.DiscretionCommitment.perfectForesight β κ lam (polShock η) 1 ())]

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sticky wages and prices

AKMM, §18.6.1, pp. 556–558, and Appendix 18.A.3, pp. 873–876.

* **Labour aggregation** (18.A.8)–(18.A.9): the labour composite has the same CES structure as
  (18.2), so the cost-minimising demand for type-`i` labour is `(W_i/W)^{−ε} ℓ`, the wage index is
  `W = (∫W_i^{1−ε})^{1/(1−ε)}` and labour income is `W L` (`sw_labour_ces`, from `env_ces`).
* **Wage dispersion**: hours `N = D^W L` with `D^W = ∫ (W_i/W)^{−ε} ≥ 1`, so hours exceed
  effective labour (`sw_hours`, `sw_wage_dispersion_ge_one`).
* **The union's problem**: the derivative of the union's period objective, multiplied by `W^R`,
  is `(1 − ε) u′ w (w^R)^{1−ε} L + ε N^ψ (w^R)^{−ε} L`, and the first-order condition rearranges to
  the book's `∑(βθ^w)^k u′ w (w^R)^{−(ε−1)} L = μ ∑(βθ^w)^k N^ψ (w^R)^{−ε} L`
  (`sw_union_term_deriv`, `sw_union_foc`): here the book's exponents are right.
* **The wage Phillips curve**: with the reset-wage recursion and the Calvo wage index,
  `π^w = βE π^w′ + ξ^w(σĈ + ψN̂ − ŵ)` (Galí's `eq15_iff` with no strategic complementarity,
  `φ = 0`; `sw_wage_pc`), and with `Ĉ = Ŷ`, `N̂ = Ŷ − Â` and (18.13),
  `ξ^w(σĈ + ψN̂ − ŵ) = κ^w x + ξ^w Â − ξ^w ŵ`, `κ^w = ξ^w(σ + ψ)` (`eq_18_24`).
* **The price Phillips curve** (18.23) (`eq_18_23`, from `eq_18_A_4`) and the real-wage identity
  (18.25), exact in logs (`eq_18_25`).
* **Correction (sticky wages only, p. 557)**: with `y = Aℓ`, pricing at marginal cost means
  `P = W_L/A` for the wage `W_L` of the labour bundle, so the real wage is `W_L/P = A`, constant
  only if productivity is (`sw_flexprice_real_wage`, `sw_real_wage_not_constant`); `W/P = 1`
  holds for the book's `W` = the labour cost of one unit of goods.
-/

namespace AKMM.NominalFrictions

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-- **AKMM, (18.A.8)–(18.A.9), p. 874**: on the continuum of unions `i ∈ [0, 1]` with wages
`W_i > 0`, (i) any labour bundle `n_i ≥ 0` costs at least `W L`, `L` the CES composite (18.A.8)
and `W` the wage index (18.A.9); (ii) it costs exactly `W L` iff `n_i = (W_i/W)^{−ε} L`;
(iii) the demand schedule delivers `L`; (iv) labour income is `∫ W_i n_i = W L`
(`env_ces` with wages in place of prices). -/
theorem sw_labour_ces {ε : ℝ} (hε : 1 < ε) {Wi : ℝ → ℝ} (hW : ∀ i, 0 < Wi i)
    (hWi : IntegrableOn (fun i => Wi i ^ (1 - ε)) (Set.Icc 0 1)) {n : ℝ → ℝ}
    (hn : ∀ i, 0 ≤ n i) (hWn : IntegrableOn (fun i => Wi i * n i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Wi * cesAgg (volume.restrict (Set.Icc 0 1)) ε n
        ≤ ∫ i in Set.Icc 0 1, Wi i * n i ∧
      (∫ i in Set.Icc 0 1, Wi i * n i
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Wi *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε n ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          n i = demand (volume.restrict (Set.Icc 0 1)) ε Wi
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε n) i) ∧
      (∀ L : ℝ, 0 ≤ L → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Wi L) = L) ∧
      ∀ L : ℝ, ∫ i in Set.Icc 0 1, Wi i * demand (volume.restrict (Set.Icc 0 1)) ε Wi L i
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Wi * L :=
  env_ces hε hW hWi hn hWn

/-- **AKMM, p. 874**: hours are `N = ∫ n_i = ∫ (W_i/W)^{−ε} L = D^W L`. -/
theorem sw_hours {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε W L : ℝ} {Wi n : J → ℝ}
    (hn : ∀ i, n i = (Wi i / W) ^ (-ε) * L) :
    ∫ i, n i ∂μ = (∫ i, (Wi i / W) ^ (-ε) ∂μ) * L := by
  simp_rw [hn]; rw [integral_mul_const]

/-- **AKMM, p. 874**: wage dispersion `D^W = ∫ (W_i/W)^{−ε} ≥ 1` (`agg_dispersion_ge_one`
with wages), so hours `N = D^W L ≥ L` exceed effective labour for `L ≥ 0`. -/
theorem sw_wage_dispersion_ge_one {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε L : ℝ} (hε : 1 < ε) {Wi : J → ℝ} (hW : ∀ i, 0 < Wi i)
    (hWi : Integrable (fun i => Wi i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (Wi i / priceIndex μ ε Wi) ^ (-ε)) μ) (hL : 0 ≤ L) :
    1 ≤ ∫ i, (Wi i / priceIndex μ ε Wi) ^ (-ε) ∂μ ∧
      L ≤ (∫ i, (Wi i / priceIndex μ ε Wi) ^ (-ε) ∂μ) * L := by
  have h := agg_dispersion_ge_one hε hW hWi hD
  exact ⟨h, by nlinarith⟩

/-- **AKMM, p. 875**: the union's period-`τ` objective
`u′(C_τ) (W^R/P_τ)(W^R/W_τ)^{−ε} L_τ − N_τ^ψ (W^R/W_τ)^{−ε} L_τ` has a derivative `d` in `W^R`
with `W^R d = (1 − ε) u′ w_τ (w^R)^{1−ε} L_τ + ε N_τ^ψ (w^R)^{−ε} L_τ`, `w_τ = W_τ/P_τ`,
`w^R = W^R/W_τ`. -/
theorem sw_union_term_deriv {ε up Nψ P W L X : ℝ} (hP : 0 < P) (hW : 0 < W) (hX : 0 < X) :
    ∃ d, HasDerivAt (fun Y => up * (Y / P) * (Y / W) ^ (-ε) * L - Nψ * (Y / W) ^ (-ε) * L) d X ∧
      X * d = (1 - ε) * (up * (W / P) * (X / W) ^ (1 - ε) * L) +
        ε * (Nψ * (X / W) ^ (-ε) * L) := by
  have hq : 0 < X / W := div_pos hX hW
  have h1 : HasDerivAt (fun Y => Y / W) (1 / W) X := by
    simpa using (hasDerivAt_id X).div_const W
  have h2 := h1.rpow_const (p := -ε) (Or.inl hq.ne')
  have h3 : HasDerivAt (fun Y => Y / P) (1 / P) X := by
    simpa using (hasDerivAt_id X).div_const P
  have h := (((h3.const_mul up).mul h2).mul_const L).sub ((h2.const_mul Nψ).mul_const L)
  refine ⟨_, h, ?_⟩
  have a1 : (X / W) ^ (-ε) = (X / W) ^ (-ε - 1) * (X / W) := by
    rw [← Real.rpow_add_one hq.ne']; ring_nf
  have a2 : (X / W) ^ (1 - ε) = (X / W) * (X / W) ^ (-ε) := by
    rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add_one hq.ne']; ring
  rw [a2, a1]
  field_simp
  ring

/-- **AKMM, p. 875 (the union's first-order condition)**: if `∑_k (βθ^w)^k` of the terms of
`sw_union_term_deriv` (times `W^R`) is zero and the two weighted sums converge to `A` and `B`,
then `A = μ B`: `∑(βθ^w)^k u′ w (w^R)^{−(ε−1)} L = ε/(ε − 1) ∑(βθ^w)^k N^ψ (w^R)^{−ε} L`. -/
theorem sw_union_foc {ε : ℝ} (hε : 1 < ε) {a b : ℕ → ℝ} {A B : ℝ} (ha : HasSum a A)
    (hb : HasSum b B) (hfoc : HasSum (fun k => (1 - ε) * a k + ε * b k) 0) :
    A = ε / (ε - 1) * B := by
  have h := ((ha.mul_left (1 - ε)).add (hb.mul_left ε)).unique hfoc
  have hε1 : ε - 1 ≠ 0 := by linarith
  field_simp
  linarith

/-- **AKMM, p. 875 (the wage Phillips curve)**: with the Calvo wage index
`w_{t+1} = θ_w w_t + (1 − θ_w) w^R_{t+1}` (log levels) and `0 < θ_w < 1`, the reset-wage
recursion `w^R_{t+1} = βθ_w E w^R_{t+2} + (1 − βθ_w)(w_{t+1} − µ̂_{t+1})`, with `µ̂ = ŵ − mrs`
the real wage minus the marginal rate of substitution, holds at every date iff
`π^w_{t+1} = β E π^w_{t+2} − ξ^w µ̂_{t+1}`, `ξ^w = (1 − θ_w)(1 − βθ_w)/θ_w` (Galí's `eq15_iff`
at `φ = 0`: the book's union takes `N^ψ` as given). -/
theorem sw_wage_pc {Ω : Type*} (𝔼 : Gali.StickyWagesPrices.ExpectationSystem Ω) {β θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {wR w μhat : ℕ → Ω → ℝ} (hwa : 𝔼.Adapted w)
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wR (t + 1)) :
    (∀ t, wR (t + 1) = (β * θ) • 𝔼.E (t + 1) (wR (t + 2)) +
        (1 - β * θ) • (w (t + 1) - μhat (t + 1))) ↔
      ∀ t, Gali.StickyWagesPrices.WageInflation.wageInfl w t =
        β • 𝔼.E (t + 1) (Gali.StickyWagesPrices.WageInflation.wageInfl w (t + 1)) -
          ((1 - θ) * (1 - β * θ) / θ) • μhat (t + 1) := by
  have h := Gali.StickyWagesPrices.WageInflation.eq15_iff 𝔼 (ε := ε) (φ := 0) (β := β) hθ0 hθ1
    (by simp) hwa h14 (μhat := μhat)
  simp only [mul_zero, add_zero, inv_one, one_smul] at h
  rw [h]
  simp [Gali.StickyWagesPrices.WageInflation.lambdaW]

/-- **AKMM, (18.24), p. 557 and p. 876**: with `Ĉ = Ŷ`, `N̂ = Ŷ − Â` and the gap
`x = Ŷ − (1+ψ)/(σ+ψ) Â`, `σĈ + ψN̂ = (σ + ψ)Ŷ − ψÂ` and
`ξ^w(σĈ + ψN̂ − ŵ) = κ^w x + ξ^w Â − ξ^w ŵ`, `κ^w = ξ^w(σ + ψ)`. -/
theorem eq_18_24 {σ ψ ξw C N Y A w x : ℝ} (hs : σ + ψ ≠ 0) (hC : C = Y) (hN : N = Y - A)
    (hx : x = Y - (1 + ψ) / (σ + ψ) * A) :
    σ * C + ψ * N = (σ + ψ) * Y - ψ * A ∧
      ξw * (σ * C + ψ * N - w) = ξw * (σ + ψ) * x + ξw * A - ξw * w := by
  refine ⟨by rw [hC, hN]; ring, ?_⟩
  rw [hC, hN, hx]
  field_simp
  ring

/-- **AKMM, (18.23), p. 557**: the price Phillips curve
`π_t = βE_tπ_{t+1} + ξ^p(ŵ_t − Â_t)`, `ξ^p = (1 − βθ)(1 − θ)/θ` (`eq_18_A_4` with marginal
cost `ŵ − Â`). -/
theorem eq_18_23 {Ω : Type*} (𝔼 : Gali.BasicNewKeynesianModel.ExpectationSystem Ω) {β θ : ℝ}
    (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1) {w a pR infl : ℕ → Ω → ℝ}
    (hrec : ResetRecursion 𝔼 β θ (fun s => w s - a s) pR infl)
    (h3 : ∀ s, infl s = ((1 - θ) / θ) • pR s) (t : ℕ) :
    infl t = β • 𝔼.E t (infl (t + 1)) + ((1 - β * θ) * (1 - θ) / θ) • (w t - a t) := by
  rw [eq_18_A_4 𝔼 hθ0 hθ1 hrec h3 t, add_comm]
  congr 2
  ring

/-- **AKMM, (18.25), p. 557**: the log of `w_t = W_t/P_t = (W_{t−1}/P_{t−1})(W_t/W_{t−1})
(P_{t−1}/P_t)`: `log w_t = log w_{t−1} + log(1 + π^w_t) − log(1 + π_t)` (exact). -/
theorem eq_18_25 {W Wm P Pm : ℝ} (hW : 0 < W) (hWm : 0 < Wm) (hP : 0 < P) (hPm : 0 < Pm) :
    Real.log (W / P) = Real.log (Wm / Pm) + Real.log (W / Wm) - Real.log (P / Pm) := by
  rw [Real.log_div hW.ne' hP.ne', Real.log_div hWm.ne' hPm.ne', Real.log_div hW.ne' hWm.ne',
    Real.log_div hP.ne' hPm.ne']
  ring

/-- **AKMM, p. 557 (correction)**: with sticky wages only and `y = Aℓ`, a competitive firm prices
at marginal cost, `P = W_L/A` (`W_L` the wage of the labour bundle); then the real wage is
`W_L/P = A`, while the cost `W = W_L/A` of the labour needed for one unit of goods satisfies
`W/P = 1`. -/
theorem sw_flexprice_real_wage {WL A P : ℝ} (hA : 0 < A) (hWL : 0 < WL) (hP : P = WL / A) :
    WL / P = A ∧ WL / A / P = 1 := by
  rw [hP]
  constructor
  · field_simp
  · field_simp

/-- **AKMM, p. 557 (correction)**: "real wages, which are now constant as `w_t = 1`" fails when
productivity varies: at two dates with `A₁ ≠ A₂`, the marginal-cost real wages differ. -/
theorem sw_real_wage_not_constant {WL₁ WL₂ A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hW₁ : 0 < WL₁) (hW₂ : 0 < WL₂) (hne : A₁ ≠ A₂) :
    WL₁ / (WL₁ / A₁) ≠ WL₂ / (WL₂ / A₂) := by
  rw [(sw_flexprice_real_wage hA₁ hW₁ rfl).1, (sw_flexprice_real_wage hA₂ hW₂ rfl).1]
  exact hne

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Other extensions: habits, adjustment costs and capital

AKMM, §18.6.2, pp. 558–560.

* `ext_habit`: `C_t − γC_{t−1} = (1 − γ)C_t + γ(C_t − C_{t−1})` (habits (18.26)).
* **Adjustment costs** (footnote 24): with `K′ = (1 − δ)K + ξ(I/K)K`, the first-order condition
  for investment gives Tobin's `Q = 1/ξ′(I/K)` (`ext_adj_foc`, `ext_tobin_q`); the deterministic
  steady state `K′ = K` has `ξ(I/K) = δ`, so `ξ(δ) = δ` makes `I/K = δ` a steady state
  (`ext_adj_steady`), and there `Q = 1` iff `ξ′(δ) = 1` (`ext_q_one_iff`).
  **Correction**: the footnote says `ξ(δ) = δ` makes `Q = 1`; it also needs `ξ′(δ) = 1`:
  `ξ(x) = √(δx)` is increasing and concave with `ξ(δ) = δ` but `Q = 2` (`ext_q_counterexample`).
* **Capital** (18.27): the output elasticity of labour is `1 − α` (`ext_labour_elasticity`), so a
  1% increase in output needs `1/(1 − α)`% more labour (`ext_labour_requirement_pct`).
  **Correction**: in units the requirement is `1/MPL = ℓ/((1 − α) y)`, which is `1/(1 − α)` only
  when `y = ℓ` (`ext_labour_requirement_units`, `ext_units_printed_false`).
-/

namespace AKMM.NominalFrictions

/-- AKMM, (18.26), p. 558: the habit term is a weighted average of the level and the change of
consumption, `C_t − γC_{t−1} = (1 − γ)C_t + γ(C_t − C_{t−1})`. -/
theorem ext_habit (γ C Cm : ℝ) : C - γ * Cm = (1 - γ) * C + γ * (C - Cm) := by ring

/-- AKMM, p. 559 and footnote 24: with the shadow value `q` of installed capital, the
derivative of `−I + q((1 − δ)K + ξ(I/K)K)` in `I` is `−1 + q ξ′(I/K)` (`K > 0`). -/
theorem ext_adj_foc {ξ : ℝ → ℝ} {ξ' q δ K I : ℝ} (hK : 0 < K) (hξ : HasDerivAt ξ ξ' (I / K)) :
    HasDerivAt (fun J => -J + q * ((1 - δ) * K + ξ (J / K) * K)) (-1 + q * ξ') I := by
  have h1 : HasDerivAt (fun J => J / K) (1 / K) I := by
    simpa using (hasDerivAt_id I).div_const K
  have h2 := ((hξ.comp I h1).mul_const K).const_add ((1 - δ) * K)
  have h3 := ((h2.const_mul q).const_add 0).add (hasDerivAt_neg I)
  convert h3 using 1
  · funext J; simp only [Function.comp_apply, zero_add, Pi.add_apply]; ring
  · field_simp; ring

/-- **AKMM, footnote 24, p. 559**: optimal investment sets the derivative to zero, so Tobin's
`Q = q = 1/ξ′(I/K)` (`ξ′ ≠ 0`). -/
theorem ext_tobin_q {ξ' q : ℝ} (h : -1 + q * ξ' = 0) : q = 1 / ξ' := by
  have hξ : ξ' ≠ 0 := by rintro rfl; simp at h
  field_simp; linarith

/-- AKMM, p. 559: the deterministic steady state `K′ = K` (`K > 0`) holds iff `ξ(I/K) = δ`. -/
theorem ext_adj_steady {ξ : ℝ → ℝ} {δ K I : ℝ} (hK : 0 < K) :
    (1 - δ) * K + ξ (I / K) * K = K ↔ ξ (I / K) = δ := by
  constructor
  · intro h
    have := mul_right_cancel₀ hK.ne' (by linarith : ξ (I / K) * K = δ * K)
    exact this
  · intro h; rw [h]; ring

/-- **AKMM, footnote 24, p. 559**: at the steady state `I/K = δ`, `Q = 1/ξ′(δ) = 1` iff
`ξ′(δ) = 1`. -/
theorem ext_q_one_iff {ξ'δ : ℝ} : 1 / ξ'δ = 1 ↔ ξ'δ = 1 := by
  constructor
  · intro h
    have hξ : ξ'δ ≠ 0 := by rintro rfl; simp at h
    field_simp at h; linarith
  · intro h; rw [h]; norm_num

/-- **AKMM, footnote 24, p. 559 (correction)**: `ξ(x) = √(δ x)` (`δ > 0`) satisfies `ξ(δ) = δ`
and is increasing and concave, but `ξ′(δ) = 1/2`, so Tobin's `Q = 2 ≠ 1` at the steady state. -/
theorem ext_q_counterexample {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt (δ * δ) = δ ∧ HasDerivAt (fun x => Real.sqrt (δ * x)) (1 / 2) δ ∧
      StrictMonoOn (fun x => Real.sqrt (δ * x)) (Set.Ici 0) ∧
      ConcaveOn ℝ (Set.Ici 0) (fun x => Real.sqrt (δ * x)) ∧ 1 / (1 / 2 : ℝ) = 2 := by
  refine ⟨Real.sqrt_mul_self hδ.le, ?_, ?_, ?_, by norm_num⟩
  · have h1 : HasDerivAt (fun x => δ * x) δ δ := by simpa using (hasDerivAt_id δ).const_mul δ
    have h2 := h1.sqrt (by positivity)
    convert h2 using 1
    rw [Real.sqrt_mul_self hδ.le]
    field_simp
  · intro x hx y hy hxy
    simp only
    exact Real.sqrt_lt_sqrt (mul_nonneg hδ.le hx) (mul_lt_mul_of_pos_left hxy hδ)
  · have hc := Real.strictConcaveOn_sqrt.concaveOn
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have := hc.2 (Set.mem_Ici.2 (mul_nonneg hδ.le hx)) (Set.mem_Ici.2 (mul_nonneg hδ.le hy))
      ha hb hab
    simp only [smul_eq_mul] at this ⊢
    convert this using 2
    ring

/-- **AKMM, (18.27), p. 560**: with `y = A k^α ℓ^{1−α}` and `k` fixed, the elasticity of output
with respect to labour is `1 − α`: `s ↦ log y(e^s)` has derivative `1 − α`. -/
theorem ext_labour_elasticity {A k α s : ℝ} (hA : 0 < A) (hk : 0 < k) :
    HasDerivAt (fun r => Real.log (A * k ^ α * Real.exp r ^ (1 - α))) (1 - α) s := by
  have e : ∀ r, Real.log (A * k ^ α * Real.exp r ^ (1 - α)) =
      Real.log (A * k ^ α) + (1 - α) * r := by
    intro r
    rw [Real.log_mul (by positivity) (by positivity), ← Real.exp_mul, Real.log_exp]
    ring
  simp_rw [e]
  simpa using ((hasDerivAt_id s).const_mul (1 - α)).const_add (Real.log (A * k ^ α))

/-- AKMM, p. 560: in percentages, raising output by `d log y` needs `d log ℓ = d log y/(1 − α)`
more labour, more than `d log y` when `0 < α < 1`. -/
theorem ext_labour_requirement_pct {α dy : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hdy : 0 < dy) :
    (1 - α) * (dy / (1 - α)) = dy ∧ dy < dy / (1 - α) := by
  have h : 0 < 1 - α := by linarith
  refine ⟨by field_simp, ?_⟩
  rw [lt_div_iff₀ h]; nlinarith

/-- **AKMM, p. 560 (correction)**: in units, one more unit of output needs `1/MPL` more labour;
with `y = A k^α ℓ^{1−α}`, `MPL = (1 − α) y/ℓ`, so the requirement is `ℓ/((1 − α) y)`. -/
theorem ext_labour_requirement_units {A k α ℓ : ℝ} (hℓ : 0 < ℓ) (hα : α ≠ 1) (hA : 0 < A)
    (hk : 0 < k) :
    HasDerivAt (fun l => A * k ^ α * l ^ (1 - α))
        ((1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ) ℓ ∧
      1 / ((1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ) =
        ℓ / ((1 - α) * (A * k ^ α * ℓ ^ (1 - α))) := by
  have h1α : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  refine ⟨?_, by rw [one_div_div]⟩
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hℓ.ne')).const_mul (A * k ^ α)
  convert h using 1
  rw [Real.rpow_sub_one hℓ.ne']
  have : 0 < k ^ α := Real.rpow_pos_of_pos hk _
  field_simp

/-- **AKMM, p. 560 (correction)**: the units requirement `ℓ/((1 − α)y)` equals the printed
`1/(1 − α)` iff `y = ℓ` (`α < 1`, `y, ℓ > 0`). -/
theorem ext_units_printed_false {α y ℓ : ℝ} (hα : α < 1) (hy : 0 < y) :
    ℓ / ((1 - α) * y) = 1 / (1 - α) ↔ y = ℓ := by
  have h : 0 < 1 - α := by linarith
  rw [div_eq_div_iff (by positivity) h.ne']
  constructor
  · intro h1
    have := mul_right_cancel₀ h.ne' (by linarith : ℓ * (1 - α) = y * (1 - α))
    exact this.symm
  · intro h1; rw [h1]; ring

end AKMM.NominalFrictions

set_option linter.style.longLine false
#print axioms AKMM.NominalFrictions.dur_printed_weights_sum
#print axioms AKMM.NominalFrictions.dur_printed_weights_ne_one
#print axioms AKMM.NominalFrictions.dur_printed_sum
#print axioms AKMM.NominalFrictions.dur_pmf_sum
#print axioms AKMM.NominalFrictions.dur_mean
#print axioms AKMM.NominalFrictions.dur_printed_eq_mean_sub_one
#print axioms AKMM.NominalFrictions.dur_printed_ne_mean
#print axioms AKMM.NominalFrictions.nfU
#print axioms AKMM.NominalFrictions.env_ces
#print axioms AKMM.NominalFrictions.env_cost_deriv
#print axioms AKMM.NominalFrictions.env_demand_elasticity
#print axioms AKMM.NominalFrictions.env_marginal_cost
#print axioms AKMM.NominalFrictions.env_profit
#print axioms AKMM.NominalFrictions.env_real_budget
#print axioms AKMM.NominalFrictions.env_relprice_law
#print axioms AKMM.NominalFrictions.env_labour_foc
#print axioms AKMM.NominalFrictions.eq_18_6
#print axioms AKMM.NominalFrictions.env_euler_foc
#print axioms AKMM.NominalFrictions.eq_18_5
#print axioms AKMM.NominalFrictions.eq_18_5_stochastic
#print axioms AKMM.NominalFrictions.rpBracket
#print axioms AKMM.NominalFrictions.rpDefl
#print axioms AKMM.NominalFrictions.rpTerm
#print axioms AKMM.NominalFrictions.RPEnvelope
#print axioms AKMM.NominalFrictions.rp_bracket_deriv
#print axioms AKMM.NominalFrictions.rp_defl_zero
#print axioms AKMM.NominalFrictions.rp_defl_succ
#print axioms AKMM.NominalFrictions.rp_defl_succ'
#print axioms AKMM.NominalFrictions.rp_defl_pos
#print axioms AKMM.NominalFrictions.rp_iterate
#print axioms AKMM.NominalFrictions.rp_series
#print axioms AKMM.NominalFrictions.rp_term_succ
#print axioms AKMM.NominalFrictions.rp_series_envelope
#print axioms AKMM.NominalFrictions.rp_term_eq
#print axioms AKMM.NominalFrictions.rp_foc_rearranged
#print axioms AKMM.NominalFrictions.rpD
#print axioms AKMM.NominalFrictions.rpN
#print axioms AKMM.NominalFrictions.eq_18_7
#print axioms AKMM.NominalFrictions.rp_pD_rec
#print axioms AKMM.NominalFrictions.rp_pN_rec
#print axioms AKMM.NominalFrictions.rp_defl_const_rpow
#print axioms AKMM.NominalFrictions.rp_constant_correct
#print axioms AKMM.NominalFrictions.rp_constant_printed
#print axioms AKMM.NominalFrictions.rp_printed_ne_iff
#print axioms AKMM.NominalFrictions.eq_18_9
#print axioms AKMM.NominalFrictions.agg_index_relative
#print axioms AKMM.NominalFrictions.agg_reset_relprice
#print axioms AKMM.NominalFrictions.eq_18_10
#print axioms AKMM.NominalFrictions.eq_18_11
#print axioms AKMM.NominalFrictions.agg_flex_output
#print axioms AKMM.NominalFrictions.agg_dispersion_ge_one
#print axioms AKMM.NominalFrictions.agg_dispersion_eq_one_iff
#print axioms AKMM.NominalFrictions.eq_18_12
#print axioms AKMM.NominalFrictions.nat_markup_foc
#print axioms AKMM.NominalFrictions.nat_markup_max
#print axioms AKMM.NominalFrictions.nat_markup_gt_one
#print axioms AKMM.NominalFrictions.nat_wage
#print axioms AKMM.NominalFrictions.nat_output_general
#print axioms AKMM.NominalFrictions.eq_18_13
#print axioms AKMM.NominalFrictions.eq_18_13_solves
#print axioms AKMM.NominalFrictions.nfGap
#print axioms AKMM.NominalFrictions.nat_gap_loglinear
#print axioms AKMM.NominalFrictions.nat_rule_intercept
#print axioms AKMM.NominalFrictions.nat_quarterly_rule
#print axioms AKMM.NominalFrictions.eff_planner_foc
#print axioms AKMM.NominalFrictions.eq_18_19
#print axioms AKMM.NominalFrictions.eq_18_19_solves
#print axioms AKMM.NominalFrictions.eff_output_wage
#print axioms AKMM.NominalFrictions.eff_output_dispersion
#print axioms AKMM.NominalFrictions.eff_natural_lt
#print axioms AKMM.NominalFrictions.eff_dispersion_lowers
#print axioms AKMM.NominalFrictions.eff_marginal_cost_pricing
#print axioms AKMM.NominalFrictions.eff_welfare_gap
#print axioms AKMM.NominalFrictions.eff_subsidy
#print axioms AKMM.NominalFrictions.eff_subsidy_mem
#print axioms AKMM.NominalFrictions.eff_subsidy_natural_eq
#print axioms AKMM.NominalFrictions.eq_18_20_weight
#print axioms AKMM.NominalFrictions.eq_18_20_period
#print axioms AKMM.NominalFrictions.eq_18_20_utility
#print axioms AKMM.NominalFrictions.nfKappa
#print axioms AKMM.NominalFrictions.eq_18_15_exact
#print axioms AKMM.NominalFrictions.rn_printed_iff
#print axioms AKMM.NominalFrictions.eq_18_15
#print axioms AKMM.NominalFrictions.rule_18_17_no_steady_state
#print axioms AKMM.NominalFrictions.eq_18_A_2
#print axioms AKMM.NominalFrictions.ResetRecursion
#print axioms AKMM.NominalFrictions.reset_recursion_instance
#print axioms AKMM.NominalFrictions.eq_18_A_3
#print axioms AKMM.NominalFrictions.eq_18_A_3_exact
#print axioms AKMM.NominalFrictions.eq_18_A_4
#print axioms AKMM.NominalFrictions.eq_18_A_dispersion
#print axioms AKMM.NominalFrictions.nk_dispersion_hat_rec
#print axioms AKMM.NominalFrictions.nk_dispersion_hat_zero
#print axioms AKMM.NominalFrictions.eq_18_A_5_exact
#print axioms AKMM.NominalFrictions.eq_18_16
#print axioms AKMM.NominalFrictions.nk_kappa_pos
#print axioms AKMM.NominalFrictions.nk_kappa_antitone
#print axioms AKMM.NominalFrictions.nk_kappa_mono_sens
#print axioms AKMM.NominalFrictions.det_system
#print axioms AKMM.NominalFrictions.detM0
#print axioms AKMM.NominalFrictions.detM1
#print axioms AKMM.NominalFrictions.detInv
#print axioms AKMM.NominalFrictions.det_inverse
#print axioms AKMM.NominalFrictions.det_coeff_eq_AT
#print axioms AKMM.NominalFrictions.det_a1
#print axioms AKMM.NominalFrictions.det_a0
#print axioms AKMM.NominalFrictions.det_jury_iff
#print axioms AKMM.NominalFrictions.det_a0_not_automatic
#print axioms AKMM.NominalFrictions.det_roots_iff
#print axioms AKMM.NominalFrictions.eq_18_18
#print axioms AKMM.NominalFrictions.det_taylor_sufficient
#print axioms AKMM.NominalFrictions.det_taylor_necessary
#print axioms AKMM.NominalFrictions.pol_divine_coincidence
#print axioms AKMM.NominalFrictions.pol_costpush_iterate
#print axioms AKMM.NominalFrictions.pol_costpush_breaks
#print axioms AKMM.NominalFrictions.pol_loss_22_eq_20
#print axioms AKMM.NominalFrictions.pol_price_level_rule
#print axioms AKMM.NominalFrictions.pol_discretion_date0
#print axioms AKMM.NominalFrictions.pol_discretion_price_level
#print axioms AKMM.NominalFrictions.polShock
#print axioms AKMM.NominalFrictions.pol_shock_ar1
#print axioms AKMM.NominalFrictions.pol_shock_bound
#print axioms AKMM.NominalFrictions.pol_commitment_path
#print axioms AKMM.NominalFrictions.pol_commitment_date0
#print axioms AKMM.NominalFrictions.pol_commitment_price_level
#print axioms AKMM.NominalFrictions.pol_commitment_better
#print axioms AKMM.NominalFrictions.pol_time_inconsistent
#print axioms AKMM.NominalFrictions.gg_rewrite
#print axioms AKMM.NominalFrictions.gg_expand
#print axioms AKMM.NominalFrictions.gg_lie
#print axioms AKMM.NominalFrictions.gg_orthogonal
#print axioms AKMM.NominalFrictions.gg_cov_zero
#print axioms AKMM.NominalFrictions.gg_mpl
#print axioms AKMM.NominalFrictions.gg_marginal_cost
#print axioms AKMM.NominalFrictions.gg_log_mc
#print axioms AKMM.NominalFrictions.sw_labour_ces
#print axioms AKMM.NominalFrictions.sw_hours
#print axioms AKMM.NominalFrictions.sw_wage_dispersion_ge_one
#print axioms AKMM.NominalFrictions.sw_union_term_deriv
#print axioms AKMM.NominalFrictions.sw_union_foc
#print axioms AKMM.NominalFrictions.sw_wage_pc
#print axioms AKMM.NominalFrictions.eq_18_24
#print axioms AKMM.NominalFrictions.eq_18_23
#print axioms AKMM.NominalFrictions.eq_18_25
#print axioms AKMM.NominalFrictions.sw_flexprice_real_wage
#print axioms AKMM.NominalFrictions.sw_real_wage_not_constant
#print axioms AKMM.NominalFrictions.ext_habit
#print axioms AKMM.NominalFrictions.ext_adj_foc
#print axioms AKMM.NominalFrictions.ext_tobin_q
#print axioms AKMM.NominalFrictions.ext_adj_steady
#print axioms AKMM.NominalFrictions.ext_q_one_iff
#print axioms AKMM.NominalFrictions.ext_q_counterexample
#print axioms AKMM.NominalFrictions.ext_labour_elasticity
#print axioms AKMM.NominalFrictions.ext_labour_requirement_pct
#print axioms AKMM.NominalFrictions.ext_labour_requirement_units
#print axioms AKMM.NominalFrictions.ext_units_printed_false
