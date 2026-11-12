/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.Huggett

/-!
# The production economy: Aiyagari

AKMM, §11.4.2, pp. 320–323, with footnote 27 and the box "The marginal propensity to consume:
models vs data".

The equilibrium of the production economy is Miao's Definition 17.1.1 (`AYStationaryEqm`,
`definition_17_1_1`, reused), with the redundancy of the goods-market condition under constant
returns (`ay_resource_redundant`) and a concrete equilibrium (`ay_example_exists`). The
Cobb–Douglas capital demand is Miao's `ay_Kd A α δ L r = L(αA/(r + δ))^{1/(1−α)}`.

* **Footnote 27, corrected:** with `F = K^αL^{1−α}`, `K(r) = L(α/(δ + r))^{1/(1−α)}` solves
  `F_K = r + δ` (`footnote_27`); the printed `(αL/(δ + r))^{1/(1−α)}` is right only for `L = 1`
  (`footnote_27_printed_false`).
* **`K(r)`** (p. 321) is continuous and strictly decreasing on `(−δ, ∞)`, `K → ∞` as `r ↓ −δ`
  (Miao) and `K → 0` as `r → ∞` (`ai_capital_demand_props`, `ai_Kd_tendsto_zero`).
* **Existence** (p. 321) by the crossing argument (`ai_existence`, Miao's `ay_existence_cd`).
* **Precautionary wealth** (Figure 11.8, p. 322): at any stationary distribution of the household
  problem the rate is below `1/β − 1`, so `K* > K^{CM}` (`ai_precautionary_wealth`).
* **MPC box** (p. 323): in the representative-agent equilibrium `βR* = 1`,
  `MPC = r/(1 + r)`, within `r²` of `r` (`ai_mpc_representative`).
-/

namespace AKMM.Consumption

open Filter Topology Miao.IncompleteMarkets

/-- **AKMM, fn. 27, p. 321, corrected.** With `F(K, L) = K^αL^{1−α}` (`0 < α < 1`, `L > 0`) and
`r > −δ`, the capital demand `K(r) = L(α/(δ + r))^{1/(1−α)}` solves the first-order condition
`F_K(K, L) = r + δ`, and it is the only positive solution. -/
theorem footnote_27 {α δ L r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hL : 0 < L) (hr : -δ < r) :
    ay_cdFK 1 α (L * (α / (δ + r)) ^ (1 / (1 - α))) L = r + δ ∧
      ∀ K, 0 < K → ay_cdFK 1 α K L = r + δ → K = L * (α / (δ + r)) ^ (1 / (1 - α)) := by
  have e : L * (α / (δ + r)) ^ (1 / (1 - α)) = ay_Kd 1 α δ L r := by
    rw [ay_Kd, mul_one, add_comm δ r]
  rw [e]
  exact ⟨ay_Kd_foc one_pos hα0 hα1 hL hr, fun K hK h => ay_Kd_unique one_pos hα0 hα1 hL hr hK h⟩

/-- **Correction to AKMM, fn. 27, p. 321** ("if `F(K, L) = K^αL^{1−α}`, then
`K(r) = (αL/(δ + r))^{1/(1−α)}`"). With `α = 1/2`, `L = 2`, `δ + r = 1/2` the printed formula gives
`K = 4`, where `F_K = (1/2)(4/2)^{−1/2} ≠ 1/2 = r + δ`; the correct demand is `K = 2`. -/
theorem footnote_27_printed_false :
    ((1 / 2 : ℝ) * 2 / (1 / 4 + 1 / 4)) ^ (1 / (1 - 1 / 2 : ℝ)) = 4 ∧
      ay_cdFK 1 (1 / 2) 4 2 ≠ 1 / 4 + 1 / 4 ∧
      (2 : ℝ) * ((1 / 2) / (1 / 4 + 1 / 4)) ^ (1 / (1 - 1 / 2 : ℝ)) = 2 := by
  have h2 : (1 / (1 - 1 / 2 : ℝ)) = 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; norm_num
  · rw [ay_cdFK]
    intro h
    have hlt : ((4 : ℝ) / 2) ^ ((1 / 2 : ℝ) - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    norm_num at h hlt
    linarith
  · rw [h2]; norm_num

/-- **AKMM, p. 321: capital demand.** For `A > 0`, `0 < α < 1`, `L > 0`, `K(r)` is continuous and
strictly decreasing on `(−δ, ∞)` and `K(r) → ∞` as `r ↓ −δ` (Miao's `ay_Kd_continuousOn`,
`ay_Kd_strictAnti`, `ay_Kd_tendsto`). -/
theorem ai_capital_demand_props {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) :
    ContinuousOn (ay_Kd A α δ L) (Set.Ioi (-δ)) ∧ StrictAntiOn (ay_Kd A α δ L) (Set.Ioi (-δ)) ∧
      Tendsto (ay_Kd A α δ L) (𝓝[>] (-δ)) atTop :=
  ⟨ay_Kd_continuousOn hA hα0, ay_Kd_strictAnti hA hα0 hα1 hL, ay_Kd_tendsto hA hα0 hα1 hL⟩

/-- **AKMM, p. 321: "for `r → +∞`, `K → 0`".** -/
theorem ai_Kd_tendsto_zero {A α δ L : ℝ} (hα1 : α < 1) :
    Tendsto (ay_Kd A α δ L) atTop (𝓝 0) := by
  have hp : 0 < 1 / (1 - α) := by rw [one_div_pos]; linarith
  have h1 : Tendsto (fun r : ℝ => α * A / (r + δ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ δ tendsto_id)
  have h2 : Tendsto (fun x : ℝ => x ^ (1 / (1 - α))) (𝓝 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / (1 - α)) (Or.inr hp.le)).tendsto
    rwa [Real.zero_rpow hp.ne'] at this
  have := (h2.comp h1).const_mul L
  rw [mul_zero] at this
  exact this

/-- **AKMM, p. 321: "existence follows from the same conditions".** If the household capital
supply `Ea` is continuous on `(−δ, 1/β − 1)`, bounded above near `−δ`, and tends to `∞` as
`r ↑ 1/β − 1`, it meets the Cobb–Douglas demand at some `r* ∈ (−δ, 1/β − 1)` (Miao's
`ay_existence_cd`). -/
theorem ai_existence {A α δ L β : ℝ} {Ea : ℝ → ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hL : 0 < L) (hEa : ContinuousOn Ea (Set.Ioo (-δ) (ay_rho β)))
    (hlim : Tendsto Ea (𝓝[<] ay_rho β) atTop)
    (hbdd : ∃ r' ∈ Set.Ioo (-δ) (ay_rho β), ∃ B, ∀ r ∈ Set.Ioc (-δ) r', Ea r ≤ B) :
    ∃ r ∈ Set.Ioo (-δ) (ay_rho β), Ea r = ay_Kd A α δ L r :=
  ay_existence_cd hA hα0 hα1 hL hEa hlim hbdd

/-- **AKMM, p. 322 and Figure 11.8: precautionary wealth.** Let the rate `r = R − 1 > −δ` of
Miao's income fluctuation problem admit a stationary distribution of cash on hand, with
nondegenerate income. Then `r < 1/β − 1`, and the capital demanded at `r` exceeds the
complete-markets stock `K^{CM} = K(1/β − 1)`: `K* − K^{CM} > 0` is the precautionary wealth. -/
theorem ai_precautionary_wealth {M : SIModel} (S : M.Solution) {lam : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) {A α δ L : ℝ} (hA : 0 < A) (hα0 : 0 < α)
    (hα1 : α < 1) (hL : 0 < L) (hδ : 0 < δ) (hr : -δ < M.r) :
    M.r < 1 / M.β - 1 ∧ ay_Kd A α δ L (1 / M.β - 1) < ay_Kd A α δ L M.r := by
  have h := (hg_rate_below_cm S hst hnd).2
  exact ⟨h, (ay_overaccumulation hA hα0 hα1 hL hδ hr h).1⟩

/-- **AKMM, p. 323 (MPC box).** In the representative-agent equilibrium `βR* = 1`, the MPC
`1 − R⁻¹(βR)^{1/σ}` of (11.16) is `r/(1 + r)`, and `0 ≤ r − r/(1 + r) ≤ r²` for `r ≥ 0`: the MPC
"roughly equals the real interest rate". -/
theorem ai_mpc_representative {β r σ : ℝ} (hr : 0 ≤ r) (hβR : β * (1 + r) = 1) :
    cd_mpc β (1 + r) σ = r / (1 + r) ∧ 0 ≤ r - r / (1 + r) ∧ r - r / (1 + r) ≤ r ^ 2 := by
  have hR : 0 < 1 + r := by linarith
  have hβ : β = 1 / (1 + r) := by rw [eq_div_iff hR.ne']; exact hβR
  exact ⟨(cd_mpc_betaR_one hR hβR hβ hR).2.2, cd_mpc_approx_rho hr⟩

end AKMM.Consumption
