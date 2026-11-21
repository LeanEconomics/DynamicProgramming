/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.Incidence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The budget locus and the excess cost of taxation

AKMM, §15.3.2–15.3.3, (15.14), pp. 449–451.

No consumption tax (`τ_c = 0`), no transfers, and `G = gy`. Write `ρ = (1 − β)/β`,
`s = α(1 − τ_k)/(ρ + δ(1 − τ_k)) = (k/ℓ)^{1−α}` (`lrS`), `s₀ = α/(ρ + δ)` its no-tax value and
`m = (1 − τ_ℓ)(1 − α)` the workers' after-tax share of output.

* The capital-tax revenue `τ_k(r − δ)k = τ_kρα/(ρ + (1 − τ_k)δ)·y` (`inc_budget_rhs`, `incBud`);
  **(15.14)**: the budget balances iff `τ_ℓ = (g − τ_kρα/(ρ + (1 − τ_k)δ))/(1 − α)` (`eq_15_14`,
  `incTauL`). Along (15.14), `m = 1 − g − (ρ + δ)s` (`inc_m_eq`).
* As `τ_k → 1`, output and the consumption of both types tend to zero
  (`inc_cons_tendsto_zero`).
* The flow-utility identity `c_w − ℓ^{1+1/φ}/(1 + 1/φ) = (1 − α)(1 − τ_ℓ)y/(1 + φ) = c_w/(1 + φ)`
  (`inc_flow_utility`).
* **The excess cost of taxation** `((c_{w,0} − c_w)/(1 + φ) + c_{k,0} − c_k − gy)/(gy)`
  (`incExcessCost`) is strictly positive along (15.14) for every `g > 0`, `0 ≤ τ_k < 1` (with
  `τ_ℓ < 1`), and all `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` (`inc_excess_cost_pos`).
  Analytic proof: consumption-equivalent utility plus public spending is net output minus the
  disutility of work; linearising the (concave) technology and the (convex) disutility at the
  no-tax steady state (`inc_cd_tangent`, Bernoulli) bounds the loss below by `ρ(k₀ − k)`; and the
  after-tax wage is below the no-tax wage (`inc_wage_le`, from `inc_core_ineq`:
  `q^b(1 + b(1 − q)) ≤ 1` on `(0, 1]`), so `k < k₀`.
* "the excess cost of taxation is increasing and convex in the capital tax rate", hence minimal at
  `τ_k = 0`, is **false in general** (`inc_excess_cost_not_min_at_zero`: `α = 1/2`, `β = 2/3`,
  `δ = 1/10`, `φ = 1`, `g = 2/5`, where the excess cost is `37/6` at `τ_k = 0` and smaller at
  `τ_k = 1/5`). At the book's parameters the claim is supported only by Figure 15.6; it is not
  proved here.
* §15.3.3: at the book's parameters (15.14) gives `τ_ℓ ≈ .2529` at `τ_k = .25` and `τ_ℓ ≈ .2985`
  at `τ_k = 0` (`inc_tau_l_025`, `inc_tau_l_0`).
-/

namespace AKMM.FiscalPolicy

open Real

/-- The capital-tax revenue per unit of output, `τ_kρα/(ρ + (1 − τ_k)δ)` (AKMM, p. 450). -/
noncomputable def incBud (α β δ τk : ℝ) : ℝ := τk * lrRho β * α / (lrRho β + (1 - τk) * δ)

/-- The budget-balancing labour tax (15.14). -/
noncomputable def incTauL (α β δ g τk : ℝ) : ℝ := (g - incBud α β δ τk) / (1 - α)

/-- The workers' after-tax share `m = (1 − τ_ℓ)(1 − α)` along (15.14). -/
noncomputable def incM (α β δ g τk : ℝ) : ℝ := (1 - incTauL α β δ g τk) * (1 - α)

/-- AKMM, p. 450: with `r` from (15.8) and `k = sy`, the capital-tax revenue is
`τ_k(r − δ)k = τ_kρα/(ρ + (1 − τ_k)δ)·y`. -/
theorem inc_budget_rhs {α β δ τk y : ℝ} (hτk : τk < 1) :
    τk * (lrRent β δ τk - δ) * (lrS α β δ τk * y) = incBud α β δ τk * y := by
  have h1 : (1 - τk) ≠ 0 := by linarith
  unfold lrRent incBud lrS
  rw [mul_comm δ (1 - τk)]
  by_cases hd : lrRho β + (1 - τk) * δ = 0
  · rw [hd]
    simp
  field_simp
  ring

/-- **(15.14)** (AKMM, p. 450): for `y ≠ 0`, `α ≠ 1`, the steady-state government budget
`gy = τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y` holds iff
`τ_ℓ = (g − τ_kρα/(ρ + (1 − τ_k)δ))/(1 − α)`. -/
theorem eq_15_14 {α β δ g τk τl y : ℝ} (hy : y ≠ 0) (hα : α ≠ 1) :
    g * y = τl * (1 - α) * y + incBud α β δ τk * y ↔ τl = incTauL α β δ g τk := by
  have h1 : (1 - α) ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  unfold incTauL
  constructor
  · intro h
    have : g = τl * (1 - α) + incBud α β δ τk := by
      have := mul_right_cancel₀ hy (show g * y = (τl * (1 - α) + incBud α β δ τk) * y by
        rw [h]; ring)
      exact this
    rw [this]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, p. 450: `ρα/(ρ + (1 − τ_k)δ)·τ_k = α − (ρ + δ)s`, so along (15.14)
`m = (1 − τ_ℓ)(1 − α) = 1 − g − (ρ + δ)s`. -/
theorem inc_m_eq {α β δ g τk : ℝ} (hα : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hτk : τk < 1) :
    incM α β δ g τk = 1 - g - (lrRho β + δ) * lrS α β δ τk := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have h1 : (1 - α) ≠ 0 := by linarith
  have hd : 0 < lrRho β + (1 - τk) * δ := by
    have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
    linarith
  unfold incM incTauL incBud lrS
  rw [mul_comm δ (1 - τk)]
  field_simp
  ring

/-- AKMM, p. 450: "the consumption-equivalent argument of flow utility in equilibrium is
proportional to consumption": with `ℓ^{1/φ} = (1 − τ_ℓ)w`, `c_w = (1 − τ_ℓ)wℓ`, `wℓ = (1 − α)y`,
`c_w − ℓ^{1+1/φ}/(1 + 1/φ) = (1 − α)(1 − τ_ℓ)y/(1 + φ) = c_w/(1 + φ)` (`φ > 0`, `ℓ > 0`). -/
theorem inc_flow_utility {α φ τl w l y cw : ℝ} (hφ : 0 < φ) (hl : 0 < l)
    (hfoc : l ^ (1 / φ) = (1 - τl) * w) (hcw : cw = (1 - τl) * w * l) (hy : w * l = (1 - α) * y) :
    cw - l ^ (1 + 1 / φ) / (1 + 1 / φ) = (1 - α) * (1 - τl) * y / (1 + φ) ∧
      cw - l ^ (1 + 1 / φ) / (1 + 1 / φ) = cw / (1 + φ) := by
  have hp : l ^ (1 + 1 / φ) = l * l ^ (1 / φ) := by
    rw [Real.rpow_add hl, Real.rpow_one]
  rw [hp, hfoc]
  have hφ' : 1 + φ ≠ 0 := by linarith
  have e : l * ((1 - τl) * w) = (1 - τl) * (1 - α) * y := by linear_combination (1 - τl) * hy
  have e2 : cw = (1 - τl) * (1 - α) * y := by rw [hcw]; linear_combination (1 - τl) * hy
  rw [e, e2]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The excess cost of taxation (AKMM, p. 451),
`((c_{w,0} − c_w)/(1 + φ) + c_{k,0} − c_k − gy)/(gy)`, along (15.14) with `τ_c = 0`, where
`c_w = my`, `c_k = ρsy`, `y = m^φs^{α(1+φ)/(1−α)}` (15.13), and the no-tax values have
`m = 1 − α`, `s = s₀`. -/
noncomputable def incExcessCost (α β δ φ g τk : ℝ) : ℝ :=
  let s := lrS α β δ τk
  let s0 := lrS α β δ 0
  let m := incM α β δ g τk
  let y := incOutput α φ m s
  let y0 := incOutput α φ (1 - α) s0
  (((1 - α) * y0 - m * y) / (1 + φ) + lrRho β * s0 * y0 - lrRho β * s * y - g * y) / (g * y)

/-- The key one-variable inequality: for `b > 0` and `0 < q ≤ 1`, `q^b(1 + b(1 − q)) ≤ 1`,
strictly if `q < 1`. -/
theorem inc_core_ineq {b q : ℝ} (hb : 0 < b) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    q ^ b * (1 + b * (1 - q)) ≤ 1 ∧ (q < 1 → q ^ b * (1 + b * (1 - q)) < 1) := by
  have hexp : q ^ b = Real.exp (b * Real.log q) := by
    rw [Real.rpow_def_of_pos hq0, mul_comm]
  have h1 : 1 + b * (1 - q) ≤ Real.exp (b * (1 - q)) := by
    have := Real.add_one_le_exp (b * (1 - q))
    linarith
  have hpos : 0 < 1 + b * (1 - q) := by
    have : 0 ≤ b * (1 - q) := mul_nonneg hb.le (by linarith)
    linarith
  have hprod : Real.exp (b * Real.log q) * Real.exp (b * (1 - q)) =
      Real.exp (b * (Real.log q - (q - 1))) := by
    rw [← Real.exp_add]
    ring_nf
  constructor
  · rw [hexp]
    calc Real.exp (b * Real.log q) * (1 + b * (1 - q))
        ≤ Real.exp (b * Real.log q) * Real.exp (b * (1 - q)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (b * (Real.log q - (q - 1))) := hprod
      _ ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonneg_of_nonpos hb.le
            (by linarith [Real.log_le_sub_one_of_pos hq0])
  · intro hq
    rw [hexp]
    calc Real.exp (b * Real.log q) * (1 + b * (1 - q))
        ≤ Real.exp (b * Real.log q) * Real.exp (b * (1 - q)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (b * (Real.log q - (q - 1))) := hprod
      _ < 1 := by
          rw [Real.exp_lt_one_iff]
          exact mul_neg_of_pos_of_neg hb
            (by linarith [Real.log_lt_sub_one_of_pos hq0 (ne_of_lt hq)])

/-- **The after-tax wage is below the no-tax wage**: for `0 < α < 1`, `ρ + δ > 0`,
`0 < s ≤ s₀ = α/(ρ + δ)`, `(1 − (ρ + δ)s)s^{α/(1−α)} ≤ (1 − α)s₀^{α/(1−α)}`, strictly if
`s < s₀`. (With `g = 0`, `1 − (ρ + δ)s` is the after-tax share `m` of (15.14), and
`s^{α/(1−α)} = (k/ℓ)^α`.) -/
theorem inc_wage_le {α c s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 < c) (hs : 0 < s)
    (hss : s ≤ α / c) :
    (1 - c * s) * s ^ (α / (1 - α)) ≤ (1 - α) * (α / c) ^ (α / (1 - α)) ∧
      (s < α / c → (1 - c * s) * s ^ (α / (1 - α)) < (1 - α) * (α / c) ^ (α / (1 - α))) := by
  have h1α : 0 < 1 - α := by linarith
  have hs0 : 0 < α / c := div_pos hα0 hc
  set q := s / (α / c) with hq
  have hq0 : 0 < q := div_pos hs hs0
  have hq1 : q ≤ 1 := (div_le_one hs0).mpr hss
  have hb : 0 < α / (1 - α) := div_pos hα0 h1α
  have hsq : s = q * (α / c) := by rw [hq]; field_simp
  have hpow : s ^ (α / (1 - α)) = q ^ (α / (1 - α)) * (α / c) ^ (α / (1 - α)) := by
    rw [hsq, Real.mul_rpow hq0.le hs0.le]
  have hlin : 1 - c * s = (1 - α) * (1 + α / (1 - α) * (1 - q)) := by
    rw [hsq]
    field_simp
    ring
  have hA0 : 0 < (α / c) ^ (α / (1 - α)) := Real.rpow_pos_of_pos hs0 _
  obtain ⟨hle, hlt⟩ := inc_core_ineq hb hq0 hq1
  have key : (1 - c * s) * s ^ (α / (1 - α)) =
      (1 - α) * (α / c) ^ (α / (1 - α)) * (q ^ (α / (1 - α)) * (1 + α / (1 - α) * (1 - q))) := by
    rw [hlin, hpow]
    ring
  constructor
  · rw [key]
    exact mul_le_of_le_one_right (by positivity) hle
  · intro hlt'
    rw [key]
    have : q < 1 := (div_lt_one hs0).mpr hlt'
    exact mul_lt_of_lt_one_right (by positivity) (hlt this)

/-- **Concavity of the technology**, linearised at the no-tax steady state: for `0 < α < 1`,
`c > 0`, `s > 0`, `s^{α/(1−α)} ≤ c·s·s^{α/(1−α)} + (1 − α)s₀^{α/(1−α)}` with `s₀ = α/c`; i.e.
`y ≤ (ρ + δ)k + w₀ℓ` per unit of hours. -/
theorem inc_cd_tangent {α c s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 < c) (hs : 0 < s) :
    s ^ (α / (1 - α)) ≤ c * s * s ^ (α / (1 - α)) + (1 - α) * (α / c) ^ (α / (1 - α)) := by
  have h1α : 0 < 1 - α := by linarith
  have hs0 : 0 < α / c := div_pos hα0 hc
  set q := s / (α / c) with hq
  have hq0 : 0 < q := div_pos hs hs0
  have hsq : s = q * (α / c) := by rw [hq]; field_simp
  set t := q ^ (1 / (1 - α)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hq0 _
  have hta : t ^ α = q ^ (α / (1 - α)) := by
    rw [ht, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have htq : t = q * q ^ (α / (1 - α)) := by
    rw [ht]
    conv_lhs => rw [show 1 / (1 - α) = 1 + α / (1 - α) by field_simp; ring]
    rw [Real.rpow_add hq0, Real.rpow_one]
  have hB := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hα0.le hα1.le
  rw [add_sub_cancel, hta] at hB
  have hpow : s ^ (α / (1 - α)) = q ^ (α / (1 - α)) * (α / c) ^ (α / (1 - α)) := by
    rw [hsq, Real.mul_rpow hq0.le hs0.le]
  have hA0 : 0 < (α / c) ^ (α / (1 - α)) := Real.rpow_pos_of_pos hs0 _
  rw [hpow]
  have hcs : c * s = α * q := by rw [hsq]; field_simp
  rw [hcs]
  have := mul_le_mul_of_nonneg_right hB hA0.le
  rw [htq] at this
  nlinarith [this]

/-- The algebraic core of the excess-cost bound. With output `y = AL`, capital `k = sAL`,
no-tax values `y₀ = A₀L₀`, `k₀ = s₀A₀L₀`, `w₀ = (1 − α)A₀`, `(ρ + δ)s₀ = α`, `m = 1 − g −
(ρ + δ)s`, the technology tangent `A ≤ (ρ + δ)sA + w₀` and the disutility tangent
`LmA ≥ L₀w₀ + (1 + 1/φ)w₀(L − L₀)`, the numerator of the excess cost is at least `ρ(k₀ − k)`. -/
theorem inc_ec_core {α ρ δ φ g m s s0 A A0 L L0 : ℝ} (hφ : 0 < φ) (hL : 0 ≤ L)
    (hs0 : (ρ + δ) * s0 = α) (hm : m = 1 - g - (ρ + δ) * s)
    (hT1 : A ≤ (ρ + δ) * s * A + (1 - α) * A0)
    (hT2 : L0 * ((1 - α) * A0) + (1 + 1 / φ) * ((1 - α) * A0) * (L - L0) ≤ L * (m * A)) :
    ρ * (s0 * A0 * L0 - s * A * L) ≤
      ((1 - α) * (A0 * L0) - m * (A * L)) / (1 + φ) + ρ * s0 * (A0 * L0) - ρ * s * (A * L) -
        g * (A * L) := by
  have hφ1 : 0 < 1 + φ := by linarith
  have P1 : 0 ≤ ((ρ + δ) * s * A + (1 - α) * A0 - A) * L := mul_nonneg (by linarith) hL
  have P2 : 0 ≤ L * (m * A) - L0 * ((1 - α) * A0) - (1 + 1 / φ) * ((1 - α) * A0) * (L - L0) := by
    linarith
  have key : ((1 - α) * (A0 * L0) - m * (A * L)) / (1 + φ) + ρ * s0 * (A0 * L0) -
      ρ * s * (A * L) - g * (A * L) - ρ * (s0 * A0 * L0 - s * A * L) =
      ((ρ + δ) * s * A + (1 - α) * A0 - A) * L +
        φ / (1 + φ) * (L * (m * A) - L0 * ((1 - α) * A0) -
          (1 + 1 / φ) * ((1 - α) * A0) * (L - L0)) := by
    rw [hm]
    have hα : α = (ρ + δ) * s0 := hs0.symm
    rw [hα]
    field_simp
    ring
  have : 0 ≤ φ / (1 + φ) * (L * (m * A) - L0 * ((1 - α) * A0) -
      (1 + 1 / φ) * ((1 - α) * A0) * (L - L0)) := mul_nonneg (by positivity) P2
  linarith

/-- Output (15.13) as `y = s^{α/(1−α)}ℓ` with hours `ℓ = (ms^{α/(1−α)})^φ`, i.e. `y = (k/ℓ)^αℓ`. -/
theorem inc_output_eq {α φ m s : ℝ} (hα1 : α < 1) (hm : 0 ≤ m) (hs : 0 < s) :
    incOutput α φ m s = s ^ (α / (1 - α)) * (m * s ^ (α / (1 - α))) ^ φ := by
  have h1α : (1 - α) ≠ 0 := by linarith
  unfold incOutput
  rw [Real.mul_rpow hm (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le,
    show α * (1 + φ) / (1 - α) = α / (1 - α) + α / (1 - α) * φ by field_simp,
    Real.rpow_add hs]
  ring

/-- The disutility tangent (Bernoulli's inequality for `ℓ ↦ ℓ^{1+1/φ}`): with `ℓ = a^φ`,
`ℓ₀ = a₀^φ`, `a, a₀ > 0`, `ℓ₀a₀ + (1 + 1/φ)a₀(ℓ − ℓ₀) ≤ ℓa`. -/
theorem inc_disutil_tangent {φ a a0 : ℝ} (hφ : 0 < φ) (ha : 0 < a) (ha0 : 0 < a0) :
    a0 ^ φ * a0 + (1 + 1 / φ) * a0 * (a ^ φ - a0 ^ φ) ≤ a ^ φ * a := by
  set L := a ^ φ
  set L0 := a0 ^ φ
  have hL : 0 < L := Real.rpow_pos_of_pos ha φ
  have hL0 : 0 < L0 := Real.rpow_pos_of_pos ha0 φ
  have hinv : ∀ x : ℝ, 0 < x → (x ^ φ) ^ (1 / φ) = x := fun x hx => by
    rw [← Real.rpow_mul hx.le, mul_one_div_cancel hφ.ne', Real.rpow_one]
  have hp : ∀ x : ℝ, 0 < x → (x ^ φ) ^ (1 + 1 / φ) = x ^ φ * x := fun x hx => by
    rw [Real.rpow_add (Real.rpow_pos_of_pos hx φ), Real.rpow_one, hinv x hx]
  have hB := one_add_mul_self_le_rpow_one_add (s := L / L0 - 1)
    (by have := div_pos hL hL0; linarith) (p := 1 + 1 / φ)
    (by have : 0 < 1 / φ := by positivity
        linarith)
  rw [add_sub_cancel, Real.div_rpow hL.le hL0.le, hp a ha, hp a0 ha0,
    le_div_iff₀ (mul_pos hL0 ha0)] at hB
  have e : (1 + (1 + 1 / φ) * (L / L0 - 1)) * (L0 * a0) =
      L0 * a0 + (1 + 1 / φ) * a0 * (L - L0) := by
    field_simp
  linarith [e]

/-- **The excess cost of taxation is positive** (AKMM, p. 451: "Clearly, the excess cost of
taxation is always positive"). For `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0`, `g > 0`,
`0 ≤ τ_k < 1`, and the labour tax (15.14) below one (`m > 0`), the excess cost is strictly
positive. -/
theorem inc_excess_cost_pos {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg : 0 < g) (hτ0 : 0 ≤ τk) (hτ1 : τk < 1)
    (hm : 0 < incM α β δ g τk) : 0 < incExcessCost α β δ φ g τk := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  set ρ := lrRho β with hρdef
  set c := ρ + δ with hcdef
  have hc : 0 < c := by linarith
  have h1α : 0 < 1 - α := by linarith
  set s := lrS α β δ τk with hsdef
  set s0 := lrS α β δ 0 with hs0def
  have hs0eq : s0 = α / c := by
    rw [hs0def]
    unfold lrS
    simp [hρdef, hcdef]
  have hs : 0 < s := by
    have : 0 < 1 - τk := by linarith
    rw [hsdef]
    unfold lrS
    positivity
  have hss : s ≤ s0 :=
    (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ).antitoneOn (Set.mem_Iio.mpr one_pos)
      (Set.mem_Iio.mpr hτ1) hτ0
  set m := incM α β δ g τk with hmdef
  have hmeq : m = 1 - g - c * s := by
    rw [hmdef, inc_m_eq hα1 hβ0 hβ1 hδ hτ1]
  set b := α / (1 - α) with hb
  set A := s ^ b with hA
  set A0 := s0 ^ b with hA0
  have hApos : 0 < A := Real.rpow_pos_of_pos hs b
  have hA0pos : 0 < A0 := Real.rpow_pos_of_pos (by linarith) b
  have hAA0 : A ≤ A0 := Real.rpow_le_rpow hs.le hss (div_pos hα0 h1α).le
  set w0 := (1 - α) * A0 with hw0
  have hw0pos : 0 < w0 := mul_pos h1α hA0pos
  -- the tangents and the wage bound
  have hT1 : A ≤ c * s * A + (1 - α) * A0 := by
    have := inc_cd_tangent hα0 hα1 hc hs
    rwa [← hs0eq] at this
  have hW : (1 - c * s) * A ≤ w0 := by
    have := (inc_wage_le hα0 hα1 hc hs (hs0eq ▸ hss)).1
    rwa [← hs0eq] at this
  have hmA : m * A < w0 := by
    have : m * A < (1 - c * s) * A := mul_lt_mul_of_pos_right (by rw [hmeq]; linarith) hApos
    linarith
  have hmApos : 0 < m * A := mul_pos hm hApos
  set L := (m * A) ^ φ with hL
  set L0 := w0 ^ φ with hL0
  have hLpos : 0 < L := Real.rpow_pos_of_pos hmApos φ
  have hLL0 : L < L0 := Real.rpow_lt_rpow hmApos.le hmA hφ
  have hT2 := inc_disutil_tangent hφ hmApos hw0pos
  rw [← hL, ← hL0] at hT2
  -- output
  have hy : incOutput α φ m s = A * L := inc_output_eq hα1 hm.le hs
  have hy0 : incOutput α φ (1 - α) s0 = A0 * L0 := by
    rw [inc_output_eq hα1 h1α.le (by linarith)]
  have hcore := inc_ec_core (α := α) (ρ := ρ) (δ := δ) (φ := φ) (g := g) (m := m) (s := s)
    (s0 := s0) (A := A) (A0 := A0) (L := L) (L0 := L0) hφ hLpos.le
    (by rw [hs0eq, ← hcdef]; field_simp) hmeq hT1 (by linarith [hT2])
  have hk : s * A * L < s0 * A0 * L0 := by
    calc s * A * L < s * A * L0 := mul_lt_mul_of_pos_left hLL0 (mul_pos hs hApos)
      _ ≤ s0 * A0 * L0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hss hAA0 hApos.le (by linarith)) (by positivity)
  unfold incExcessCost
  simp only []
  rw [← hsdef, ← hs0def, ← hmdef, hy, hy0]
  apply div_pos _ (mul_pos hg (mul_pos hApos hLpos))
  nlinarith [mul_pos hρ (sub_pos.mpr hk)]

/-- **The excess cost is not minimal at `τ_k = 0` in general** (AKMM, p. 451: "the excess cost of
taxation is increasing and convex in the capital tax rate"; p. 451: "minimized when `τ_k = 0`").
With `α = 1/2`, `β = 2/3` (`ρ = 1/2`), `δ = 1/10`, `φ = 1`, `g = 2/5` the excess cost is `37/6` at
`τ_k = 0` and `12013321/2706048 < 37/6` at `τ_k = 1/5` (both with `τ_ℓ < 1`). -/
theorem inc_excess_cost_not_min_at_zero :
    incExcessCost (1 / 2) (2 / 3) (1 / 10) 1 (2 / 5) 0 = 37 / 6 ∧
      incExcessCost (1 / 2) (2 / 3) (1 / 10) 1 (2 / 5) (1 / 5) = 12013321 / 2706048 ∧
      (12013321 / 2706048 : ℝ) < 37 / 6 ∧
      0 < incM (1 / 2) (2 / 3) (1 / 10) (2 / 5) 0 ∧
      0 < incM (1 / 2) (2 / 3) (1 / 10) (2 / 5) (1 / 5) := by
  have e : ((1 : ℝ) / 2) * (1 + 1) / (1 - 1 / 2) = 2 := by norm_num
  refine ⟨?_, ?_, by norm_num, ?_, ?_⟩ <;>
    simp only [incExcessCost, incOutput, incM, incTauL, incBud, lrS, lrRho, e, Real.rpow_one,
      Real.rpow_two] <;> norm_num

/-- AKMM, p. 451 (§15.3.3): at `α = .33`, `δ = .07`, `β = .97`, `g = .2`, (15.14) gives
`τ_ℓ = .2529` (to four decimals) at `τ_k = .25`. -/
theorem inc_tau_l_025 :
    (0.25285 : ℝ) < incTauL 0.33 0.97 0.07 0.2 0.25 ∧
      incTauL 0.33 0.97 0.07 0.2 0.25 < 0.25295 := by
  unfold incTauL incBud lrRho
  constructor <;> norm_num

/-- AKMM, p. 451 (§15.3.3): at the same parameters, `τ_ℓ = .2985` (to four decimals) at
`τ_k = 0`. -/
theorem inc_tau_l_0 :
    (0.29845 : ℝ) < incTauL 0.33 0.97 0.07 0.2 0 ∧ incTauL 0.33 0.97 0.07 0.2 0 < 0.29855 := by
  unfold incTauL incBud lrRho
  constructor <;> norm_num

/-- AKMM, p. 450: "Note that as `τ_k → 1`, consumption of both types converges to zero": along
(15.14) (`τ_c = 0`, `0 < g`, `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0`), output
`y`, workers' consumption `c_w = my` and capitalists' consumption `c_k = ρsy` all tend to `0` as
`τ_k → 1⁻`. -/
theorem inc_cons_tendsto_zero {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    Filter.Tendsto (fun τk => incOutput α φ (incM α β δ g τk) (lrS α β δ τk))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) ∧
      Filter.Tendsto (fun τk => incM α β δ g τk * incOutput α φ (incM α β δ g τk) (lrS α β δ τk))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) ∧
      Filter.Tendsto
        (fun τk => lrRho β * lrS α β δ τk * incOutput α φ (incM α β δ g τk) (lrS α β δ τk))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have he : 0 < α * (1 + φ) / (1 - α) := by
    have : 0 < 1 - α := by linarith
    positivity
  set S : ℝ → ℝ := fun τ => α * (1 - τ) / (lrRho β + δ * (1 - τ)) with hS
  set Mf : ℝ → ℝ := fun τ => 1 - g - (lrRho β + δ) * S τ with hM
  have hS1 : S 1 = 0 := by simp [hS]
  have hSc : ContinuousAt S 1 := by
    refine (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.add (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)))
      ?_
    simp [hρ.ne']
  have hMc : ContinuousAt Mf 1 :=
    continuousAt_const.sub (continuousAt_const.mul hSc)
  have hYc : ContinuousAt (fun τ => Mf τ ^ φ * S τ ^ (α * (1 + φ) / (1 - α))) 1 :=
    (hMc.rpow_const (Or.inr hφ.le)).mul (hSc.rpow_const (Or.inr he.le))
  have hY0 : Mf 1 ^ φ * S 1 ^ (α * (1 + φ) / (1 - α)) = 0 := by
    rw [hS1, Real.zero_rpow he.ne', mul_zero]
  have hev : ∀ᶠ τ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      Mf τ ^ φ * S τ ^ (α * (1 + φ) / (1 - α)) =
        incOutput α φ (incM α β δ g τ) (lrS α β δ τ) ∧ Mf τ = incM α β δ g τ ∧
        S τ = lrS α β δ τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : τ < 1 := hτ
    have hSτ : S τ = lrS α β δ τ := rfl
    have hMτ : Mf τ = incM α β δ g τ := by
      rw [inc_m_eq hα1 hβ0 hβ1 hδ hτ', ← hSτ]
    refine ⟨?_, hMτ, hSτ⟩
    unfold incOutput
    rw [hMτ, hSτ]
  have hY : Filter.Tendsto (fun τ => Mf τ ^ φ * S τ ^ (α * (1 + φ) / (1 - α)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    have := hYc.tendsto
    rw [hY0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hYt := hY.congr' (hev.mono fun τ h => h.1)
  have hMt : Filter.Tendsto Mf (nhdsWithin 1 (Set.Iio 1)) (nhds (Mf 1)) :=
    hMc.tendsto.mono_left nhdsWithin_le_nhds
  have hSt : Filter.Tendsto S (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    have := hSc.tendsto
    rw [hS1] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨hYt, ?_, ?_⟩
  · have := (hMt.congr' (hev.mono fun τ h => h.2.1)).mul hYt
    simpa using this
  · have := ((hSt.congr' (hev.mono fun τ h => h.2.2)).const_mul (lrRho β)).mul hYt
    simpa [mul_assoc] using this

end AKMM.FiscalPolicy
