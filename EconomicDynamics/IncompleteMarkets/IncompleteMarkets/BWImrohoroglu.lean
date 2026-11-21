/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.BWHousehold
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exercise 17.6 (Imrohoroglu 1992): the mathematical content

Miao, Exercise 17.6, pp. 584–585. A continuum of households with CRRA utility
`E Σ βᵗ c_t^{1−γ}/(1 − γ)`, a two-state employment process `l ∈ {e, u}` (`true = e`) with
transition `π_{ll′}`, output `y` when employed and `θy` (`0 < θ < 1`) when unemployed, money
balances `m_t`, lump-sum transfers `gM_t`, `M_{t+1} = (1 + g)M_t`, and the budget
`c_t + m_{t+1}/p_t = m_t/p_t + gM_t/p_t + y_t`, `m_{t+1} ≥ 0`.

* `ex_17_6_inflation`: constant real balances `M_{t+1}/p_t = M_t/p_{t−1}` force the inflation rate
  `p_t/p_{t−1} = 1 + g`.
* `ex_17_6_a` (part (a)): in the real balances `q_t = m_t/p_{t−1}`, with `m̄ = M_t/p_{t−1}` and
  `1 + r = 1/(1 + g)`, the budget is `c + q′ = (1 + r)q + y(l) + gm̄/(1 + g)`, `q′ ≥ 0`. The
  household's dynamic programming problem is therefore (17.4) for the economy
  `BWImroParams.toEconomy` with the return `r`, debt limit `0` and income `y(l) + gm̄/(1 + g)`:
  `V(q, l) = max_{q′ ∈ [0, (1+r)q + y(l) + gm̄/(1+g)]} u(c) + β Σ_{l′} π_{ll′} V(q′, l′)`.
* `BWImroEqm` (part (b)): a **stationary equilibrium**: real balances `m̄ > 0`, a solution
  `(V, h)` of the problem in (a), a stationary distribution `λ` on `[0, ∞) × {e, u}` (17.8) and
  money-market clearing `∫ h dλ = m̄`.
* `ex_17_6_b`: an instance (`γ = 1/2`, `β = 1/2`, `y = 2`, `θ = 3/4`, `g = −1/2 = β − 1`, the
  Friedman rule, `π` the identity): `V(q, l) = 4√(q + c_l)`, `h(q, l) = q`, `λ = δ_{(1, e)}`.

Part (c) (computation, welfare cost of inflation) is computational and not formalised.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The primitives of Exercise 17.6. -/
structure BWImroParams where
  β : ℝ
  γ : ℝ
  y : ℝ
  θ : ℝ
  g : ℝ
  trans : Kernel Bool Bool

namespace BWImroParams

/-- The household's economy: CRRA utility, employment chain `π`, output `y` or `θy`. -/
noncomputable def toEconomy (P : BWImroParams) : BWEconomy Bool where
  β := P.β
  u := fun c => c ^ (1 - P.γ) / (1 - P.γ)
  Q := P.trans
  e := fun l => if l then P.y else P.θ * P.y

/-- The real return on money `r = 1/(1 + g) − 1`. -/
noncomputable def rate (P : BWImroParams) : ℝ := 1 / (1 + P.g) - 1

/-- Income including the real transfer: `y(l) + gm̄/(1 + g)`. -/
noncomputable def income (P : BWImroParams) (mbar : ℝ) (l : Bool) : ℝ :=
  P.toEconomy.e l + P.g * mbar / (1 + P.g)

end BWImroParams

/-- **Exercise 17.6** (Miao, p. 585): with `M_{t+1} = (1 + g)M_t` and constant real balances
`M_{t+1}/p_t = M_t/p_{t−1}`, prices grow at the money growth rate, `p_t/p_{t−1} = 1 + g`. -/
theorem ex_17_6_inflation {M M' p p₀ g : ℝ} (hM : 0 < M) (hp : 0 < p) (hp₀ : 0 < p₀)
    (hg : M' = (1 + g) * M) (hreal : M' / p = M / p₀) : p / p₀ = 1 + g := by
  rw [hg, div_eq_div_iff hp.ne' hp₀.ne'] at hreal
  rw [div_eq_iff hp₀.ne']
  have := mul_right_cancel₀ hM.ne' (by linarith : (1 + g) * p₀ * M = p * M)
  linarith

/-- **Exercise 17.6 (a)** (Miao, p. 585): with `p_t = (1 + g)p_{t−1}`, real balances
`q = m_t/p_{t−1}`, `q′ = m_{t+1}/p_t`, `m̄ = M_t/p_{t−1}` and `1 + r = 1/(1 + g)`, the budget
`c + m_{t+1}/p_t = m_t/p_t + gM_t/p_t + y` is `c + q′ = (1 + r)q + y + gm̄/(1 + g)`. -/
theorem ex_17_6_a {m m' M p p₀ g c y : ℝ} (hp₀ : 0 < p₀) (hg : 0 < 1 + g)
    (hp : p = (1 + g) * p₀) :
    c + m' / p = m / p + g * M / p + y ↔
      c + m' / p = (1 + (1 / (1 + g) - 1)) * (m / p₀) + y + g * (M / p₀) / (1 + g) := by
  have e1 : m / p = (1 + (1 / (1 + g) - 1)) * (m / p₀) := by rw [hp]; field_simp; ring
  have e2 : g * M / p = g * (M / p₀) / (1 + g) := by rw [hp]; field_simp
  rw [e1, e2]
  constructor <;> intro h <;> linarith

/-- **Exercise 17.6 (b)** (Miao, p. 585): a **stationary equilibrium** of the Imrohoroglu economy:
constant real balances `m̄ = M_{t+1}/p_t > 0`, the household's value function and money policy
`h(q, l) = m_{t+1}/p_t` solving part (a), a stationary distribution `λ` of `(q, l)` on
`[0, ∞) × {e, u}` and market clearing `∫ h dλ = m̄`. -/
structure BWImroEqm (P : BWImroParams) where
  mbar : ℝ
  V : ℝ → Bool → ℝ
  h : ℝ → Bool → ℝ
  lam : Measure (ℝ × Bool)
  β_pos : 0 < P.β
  β_lt_one : P.β < 1
  γ_pos : 0 < P.γ
  γ_ne_one : P.γ ≠ 1
  y_pos : 0 < P.y
  θ_pos : 0 < P.θ
  θ_lt_one : P.θ < 1
  g_gt : -1 < P.g
  mbar_pos : 0 < mbar
  isProb : IsProbabilityMeasure lam
  supp : lam {q | q.1 < -0} = 0
  bellman : P.toEconomy.Bellman P.rate 0 (P.income mbar) V h
  integrable : Integrable (fun q => h q.1 q.2) lam
  clear : ∫ q, h q.1 q.2 ∂lam = mbar
  stationary : P.toEconomy.Stationary h lam

/-- The parameters of the instance `ex_17_6_b`. -/
noncomputable def bw_imroExample : BWImroParams where
  β := 1 / 2
  γ := 1 / 2
  y := 2
  θ := 3 / 4
  g := -1 / 2
  trans := Kernel.deterministic id measurable_id

theorem bw_imroExample_u (c : ℝ) : bw_imroExample.toEconomy.u c = 2 * Real.sqrt c := by
  simp only [BWImroParams.toEconomy, bw_imroExample]
  rw [Real.sqrt_eq_rpow, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  ring

theorem bw_imroExample_Q (l : Bool) : bw_imroExample.toEconomy.Q l = Measure.dirac l := by
  simp [BWImroParams.toEconomy, bw_imroExample, Kernel.deterministic_apply]

theorem bw_imroExample_rate : bw_imroExample.rate = 1 := by
  norm_num [BWImroParams.rate, bw_imroExample]

theorem bw_imroExample_income (l : Bool) :
    bw_imroExample.income 1 l = if l then 1 else 1 / 2 := by
  cases l <;> norm_num [BWImroParams.income, BWImroParams.toEconomy, bw_imroExample]

/-- `√A + √B ≤ 2√((A + B)/2)` in the form used below. -/
theorem bw_sqrt_add_le {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) (hAB : A + B = 2 * s) :
    2 * Real.sqrt A + 2 * Real.sqrt B ≤ 4 * Real.sqrt s := by
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  have h3 := Real.sq_sqrt hs
  have p1 := Real.sqrt_nonneg A
  have p2 := Real.sqrt_nonneg B
  have p3 := Real.sqrt_nonneg s
  nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B), sq_nonneg (Real.sqrt A + Real.sqrt B -
    2 * Real.sqrt s)]

/-- **Exercise 17.6 (b)** is not vacuous: with `β = γ = 1/2`, `y = 2`, `θ = 3/4`, `g = −1/2` (so
`1 + r = 1/(1 + g) = 1/β`, the Friedman rule) and `π` the identity, `m̄ = 1`,
`V(q, l) = 4√(q + c_l)` (`c_e = 1`, `c_u = 1/2`), `h(q, l) = q` and `λ = δ_{(1, e)}` form a
stationary equilibrium. -/
noncomputable def ex_17_6_b : BWImroEqm bw_imroExample where
  mbar := 1
  V := fun q l => 4 * Real.sqrt (q + if l then 1 else 1 / 2)
  h := fun q _ => q
  lam := Measure.dirac ((1 : ℝ), true)
  β_pos := by norm_num [bw_imroExample]
  β_lt_one := by norm_num [bw_imroExample]
  γ_pos := by norm_num [bw_imroExample]
  γ_ne_one := by norm_num [bw_imroExample]
  y_pos := by norm_num [bw_imroExample]
  θ_pos := by norm_num [bw_imroExample]
  θ_lt_one := by norm_num [bw_imroExample]
  g_gt := by norm_num [bw_imroExample]
  mbar_pos := one_pos
  isProb := inferInstance
  supp := by simp [Measure.dirac_apply]
  bellman := by
    intro q l hq
    rw [neg_zero] at hq
    have hc : 0 < (if l then (1 : ℝ) else 1 / 2) := by cases l <;> norm_num
    simp only [bw_imroExample_Q, integral_dirac, bw_imroExample_u, bw_imroExample_rate,
      bw_imroExample_income]
    have hβ : bw_imroExample.toEconomy.β = 1 / 2 := rfl
    rw [hβ]
    refine ⟨⟨by linarith, by linarith⟩, fun a' _ => Integrable.of_finite, ?_, fun a' ha' => ?_⟩
    · rw [show (1 + 1) * q + (if l then (1 : ℝ) else 1 / 2) - q =
        q + (if l then (1 : ℝ) else 1 / 2) by ring]
      ring
    · obtain ⟨h0, h1⟩ := ha'
      rw [neg_zero] at h0
      have := bw_sqrt_add_le (A := (1 + 1) * q + (if l then (1 : ℝ) else 1 / 2) - a')
        (B := a' + if l then (1 : ℝ) else 1 / 2) (s := q + if l then (1 : ℝ) else 1 / 2)
        (by linarith) (by linarith) (by linarith) (by ring)
      linarith
  integrable := integrable_dirac (by simp)
  clear := by rw [integral_dirac]
  stationary := by
    intro A B _ _
    simp only [lintegral_dirac, bw_imroExample_Q, Measure.dirac_apply]
    by_cases hA : (1 : ℝ) ∈ A <;> by_cases hB : true ∈ B <;>
      simp [Set.indicator, Set.mem_prod, hA, hB]

end Miao.IncompleteMarkets
