import FiscalConstraints.LinearODE
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LifeCycleFiscalPolicy.RicardianEquivalence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.Variance
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Government budget and the dynamics of the debt-to-GDP ratio

AKMM, §15.2, (15.1)–(15.2), pp. 441–444.

The government budget constraint (15.1) `G_t + T_t + i_tB_{t−1} = Rev_t + B_t − B_{t−1}`,
with the primary deficit `D_t = G_t + T_t − Rev_t`, gives `B_t = B_{t−1}(1 + i_t) + D_t`
(`dd_nominal_debt`). Dividing by nominal GDP, which grows by `(1 + γ_t)(1 + π_t)`, gives
`b_t = b_{t−1}(1 + i_t)/((1 + γ_t)(1 + π_t)) + d_t` (`dd_ratio_nominal`), and with the ex post
real rate `1 + r_t = (1 + i_t)/(1 + π_t)`, `b_t = b_{t−1}(1 + r_t)/(1 + γ_t) + d_t`
(`dd_ratio_real`). With constant rates this is Cochrane's discrete debt-to-GDP equation
(`dd_ratio_const`, from `Cochrane.FiscalConstraints.LinearODE.debt_gdp_discrete`).

* With a zero primary deficit the ratio rises iff `r > γ` (`dd_zero_deficit_rises_iff`).
* (15.2): `b_t > b_{t−1}` iff `d_t > (γ_t − r_t)b_{t−1}/(1 + γ_t)` (`eq_15_2`).
* With constant `r, γ, d` and `γ ≠ r` the unique stationary ratio is `b* = d(1 + γ)/(γ − r)`
  (`dd_stationary_iff`); the solution is `b_t − b* = ((1 + r)/(1 + γ))^t(b₀ − b*)`
  (`dd_sub_stationary`); for `−1 < r < γ` every path converges to `b*` (`dd_tendsto_stationary`)
  and for `r > γ`, `d > 0`, `b₀ ≥ 0` the ratio diverges to `+∞` (`dd_tendsto_atTop`).
* The box on p. 444: at `b = 1`, `γ = 0.03`, `r = 0.02` the largest deficit that does not raise
  the ratio is `0.01/1.03 ∈ (0.0097, 0.0098)`, and a 3% deficit is stable at `b* = 3.09`
  (`dd_box_threshold`, `dd_box_309`).

Departures: none. Time-varying `r_t`, `γ_t` are kept where the book keeps them.
-/

namespace AKMM.FiscalPolicy

open Filter Topology

/-- AKMM, (15.1), p. 441: with the primary deficit `D_t = G_t + T_t − Rev_t`, the budget
constraint `G_t + T_t + i_tB_{t−1} = Rev_t + B_t − B_{t−1}` is `B_t = B_{t−1}(1 + i_t) + D_t`
(p. 443). -/
theorem dd_nominal_debt {G T i Bm Rev B : ℝ} (h : G + T + i * Bm = Rev + B - Bm) :
    B = Bm * (1 + i) + (G + T - Rev) := by
  linarith

/-- AKMM, p. 443: dividing `B_t = B_{t−1}(1 + i_t) + D_t` by nominal GDP
`Y_t = (1 + γ_t)(1 + π_t)Y_{t−1}` gives `b_t = b_{t−1}(1 + i_t)/((1 + γ_t)(1 + π_t)) + d_t`. -/
theorem dd_ratio_nominal {Bm B D i γ π' Ym : ℝ} (hY : Ym ≠ 0) (hγ : 1 + γ ≠ 0)
    (hπ : 1 + π' ≠ 0) (hB : B = Bm * (1 + i) + D) :
    B / ((1 + γ) * (1 + π') * Ym) =
      Bm / Ym * ((1 + i) / ((1 + γ) * (1 + π'))) + D / ((1 + γ) * (1 + π') * Ym) := by
  rw [hB]
  field_simp

/-- AKMM, p. 444: with `1 + r_t = (1 + i_t)/(1 + π_t)` the ratio obeys
`b_t = b_{t−1}(1 + r_t)/(1 + γ_t) + d_t`. -/
theorem dd_ratio_real {bm b d i γ π' r : ℝ} (hγ : 1 + γ ≠ 0) (hπ : 1 + π' ≠ 0)
    (hr : 1 + r = (1 + i) / (1 + π')) (hb : b = bm * ((1 + i) / ((1 + γ) * (1 + π'))) + d) :
    b = bm * ((1 + r) / (1 + γ)) + d := by
  rw [hb, hr]
  field_simp

/-- AKMM, p. 444, with constant `r` and `γ`: the debt-to-GDP equation of Cochrane's §6.4.1
(`debt_gdp_discrete`, with surplus `s = −D`) is the book's
`b_{t+1} = b_t(1 + r)/(1 + γ) + d_{t+1}`. -/
theorem dd_ratio_const {B Y D : ℕ → ℝ} {r γ : ℝ}
    (hB : ∀ t, B (t + 1) = B t * (1 + r) + D (t + 1))
    (hY : ∀ t, Y (t + 1) = (1 + γ) * Y t) (hY0 : ∀ t, Y t ≠ 0) (hγ : 1 + γ ≠ 0) (t : ℕ) :
    B (t + 1) / Y (t + 1) = B t / Y t * ((1 + r) / (1 + γ)) + D (t + 1) / Y (t + 1) := by
  have h := Cochrane.FiscalConstraints.LinearODE.debt_gdp_discrete (b := B) (y := Y)
    (s := fun t => -D t) (r := r) (g := γ) (fun t => by rw [hB t]; ring) hY hY0 hγ t
  rw [h, neg_div]
  ring

/-- AKMM, p. 444: "When the primary deficit `d_t` is zero, the debt to GDP ratio will rise when
`r_t > γ_t`, and will fall when `r_t < γ_t`" (for positive debt). -/
theorem dd_zero_deficit_rises_iff {bm r γ : ℝ} (hbm : 0 < bm) (hγ : 0 < 1 + γ) :
    bm < bm * ((1 + r) / (1 + γ)) + 0 ↔ γ < r := by
  rw [add_zero, lt_mul_iff_one_lt_right hbm, one_lt_div hγ]
  constructor <;> intro h <;> linarith

/-- AKMM, (15.2), p. 444: debt rises, `b_t > b_{t−1}`, iff `d_t > (γ_t − r_t)b_{t−1}/(1 + γ_t)`. -/
theorem eq_15_2 {bm d r γ : ℝ} (hγ : 0 < 1 + γ) :
    bm < bm * ((1 + r) / (1 + γ)) + d ↔ (γ - r) / (1 + γ) * bm < d := by
  have : bm * ((1 + r) / (1 + γ)) = bm - (γ - r) / (1 + γ) * bm := by
    field_simp
    ring
  rw [this]
  constructor <;> intro h <;> linarith

/-- The stable debt-to-GDP ratio `b* = d(1 + γ)/(γ − r)` (AKMM, p. 444). -/
noncomputable def ddStationary (d r γ : ℝ) : ℝ := d * (1 + γ) / (γ - r)

/-- AKMM, p. 444: for `γ ≠ r`, `b` is a stationary point of `b ↦ b(1 + r)/(1 + γ) + d` iff
`b = d(1 + γ)/(γ − r)`; so the stationary ratio exists and is unique. -/
theorem dd_stationary_iff {b d r γ : ℝ} (hγ : 1 + γ ≠ 0) (hne : γ ≠ r) :
    b = b * ((1 + r) / (1 + γ)) + d ↔ b = ddStationary d r γ := by
  have hgr : γ - r ≠ 0 := sub_ne_zero.mpr hne
  unfold ddStationary
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, p. 444: along `b_{t+1} = b_t(1 + r)/(1 + γ) + d`, the gap to the stationary ratio
evolves geometrically: `b_t − b* = ((1 + r)/(1 + γ))^t(b₀ − b*)`. -/
theorem dd_sub_stationary {b : ℕ → ℝ} {d r γ : ℝ} (hγ : 1 + γ ≠ 0) (hne : γ ≠ r)
    (hb : ∀ t, b (t + 1) = b t * ((1 + r) / (1 + γ)) + d) (t : ℕ) :
    b t - ddStationary d r γ = ((1 + r) / (1 + γ)) ^ t * (b 0 - ddStationary d r γ) := by
  have hs := (dd_stationary_iff (b := ddStationary d r γ) (d := d) hγ hne).mpr rfl
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hb n, pow_succ]
    have : b n * ((1 + r) / (1 + γ)) + d - ddStationary d r γ =
        (1 + r) / (1 + γ) * (b n - ddStationary d r γ) := by
      linear_combination (-1 : ℝ) * hs
    rw [this, ih]
    ring

/-- AKMM, p. 444, **global stability**: "given constant values for `r` and `γ > r`, any size
primary deficit is consistent with a stable debt to GDP ratio": for `−1 < r < γ` every path of
`b_{t+1} = b_t(1 + r)/(1 + γ) + d` converges to `b* = d(1 + γ)/(γ − r)`. -/
theorem dd_tendsto_stationary {b : ℕ → ℝ} {d r γ : ℝ} (hr : -1 < r) (hrg : r < γ)
    (hb : ∀ t, b (t + 1) = b t * ((1 + r) / (1 + γ)) + d) :
    Tendsto b atTop (𝓝 (ddStationary d r γ)) := by
  have hγ : 0 < 1 + γ := by linarith
  have h0 : 0 ≤ (1 + r) / (1 + γ) := div_nonneg (by linarith) hγ.le
  have h1 : (1 + r) / (1 + γ) < 1 := (div_lt_one hγ).mpr (by linarith)
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const
    (b 0 - ddStationary d r γ)
  rw [zero_mul] at hp
  have hfun : b = fun t => ((1 + r) / (1 + γ)) ^ t * (b 0 - ddStationary d r γ) +
      ddStationary d r γ := by
    funext t
    rw [← dd_sub_stationary hγ.ne' hrg.ne' hb t]
    ring
  rw [hfun]
  simpa using hp.add_const (ddStationary d r γ)

/-- AKMM, p. 444, **divergence**: "once the differential between `γ` and `r` changes sign,
stabilizing the debt to GDP ratio will require primary surpluses": for `r > γ > −1`, a constant
deficit `d > 0` and `b₀ ≥ 0`, the ratio diverges to `+∞`. -/
theorem dd_tendsto_atTop {b : ℕ → ℝ} {d r γ : ℝ} (hγ : -1 < γ) (hrg : γ < r) (hd : 0 < d)
    (hb0 : 0 ≤ b 0) (hb : ∀ t, b (t + 1) = b t * ((1 + r) / (1 + γ)) + d) :
    Tendsto b atTop atTop := by
  have hγ' : 0 < 1 + γ := by linarith
  have h1 : 1 < (1 + r) / (1 + γ) := (one_lt_div hγ').mpr (by linarith)
  have hs : ddStationary d r γ < 0 := by
    unfold ddStationary
    exact div_neg_of_pos_of_neg (by positivity) (by linarith)
  have hgap : 0 < b 0 - ddStationary d r γ := by linarith
  have hp := (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const hgap
  have hfun : b = fun t => ((1 + r) / (1 + γ)) ^ t * (b 0 - ddStationary d r γ) +
      ddStationary d r γ := by
    funext t
    rw [← dd_sub_stationary hγ'.ne' (ne_of_lt hrg) hb t]
    ring
  rw [hfun]
  exact tendsto_atTop_add_const_right _ _ hp

/-- AKMM, p. 444 (box): at `b_{t−1} = 1`, `γ = 0.03`, `r = 0.02`, the largest primary deficit
consistent with debt not rising, `(γ − r)/(1 + γ) = 0.01/1.03`, is "approximately 1 percent":
it lies in `(0.0097, 0.0098)`. -/
theorem dd_box_threshold :
    (0.0097 : ℝ) < (0.03 - 0.02) / (1 + 0.03) * 1 ∧
      (0.03 - 0.02) / (1 + 0.03) * 1 < (0.0098 : ℝ) := by
  constructor <;> norm_num

/-- AKMM, p. 444 (box): with `r = 0.02`, `γ = 0.03`, a 3 percent primary deficit is consistent
with the stable ratio `b* = 3.09`, and `0.03 = (0.01/1.03) × 3.09`. -/
theorem dd_box_309 :
    ddStationary 0.03 0.02 0.03 = 3.09 ∧ (0.03 : ℝ) = (0.03 - 0.02) / (1 + 0.03) * 3.09 := by
  unfold ddStationary
  constructor <;> norm_num

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Competitive equilibrium with distortionary taxes

AKMM, §15.3, Definition 15.1, (15.3)–(15.7), pp. 446–447.

The neoclassical growth model with proportional taxes on consumption, labour income and capital
income net of depreciation. A policy is `{τ_c, τ_k, τ_ℓ, G, T}` (`DTPolicy`); the household
budget is (15.5) (`dtBudget`), the government budget (15.4) (`dtGovBudget`) and the resource
constraint (15.3) (`dtResource`). **Definition 15.1** (`definition_15_1`): the household
maximises `∑βᵗu(c_t, ℓ_t)` (an infinite sum, `tsum`) over plans satisfying (15.5), `k₀ = K₀` and
`k_{t+1} ≥ 0`; firms maximise profits over `k, ℓ ≥ 0`; the government budget balances.

* A two-date perturbation leaves `tsum` changed by exactly the two altered terms
  (`dt_tsum_two_point`), and a utility differentiable at a point is differentiable along curves
  through it (`dt_curve_hasDerivAt`).
* (15.6): at an interior `k_{t+1} > 0`, the household Euler equation
  `((1 + τ_{c,t+1})/(1 + τ_{c,t}))u₁(t)/u₁(t+1) = β[1 + (1 − τ_{k,t+1})(r_{t+1} − δ)]`
  (`eq_15_6`) and the labour condition `−u₂ = ((1 − τ_ℓ)/(1 + τ_c))wu₁` (`dt_labour_foc`).
* Firms: `w = f₂`, `r = f₁` at positive inputs (`dt_firm_foc`).
* (15.7): the planner's Euler equation and labour condition (`dt_planner_euler`, `eq_15_7`),
  and with zero taxes the household's conditions are the planner's (`dt_no_tax_euler`).
* Market clearing is implied: (15.4) and (15.5) give (15.3) (`dt_resource_of_budgets`).
* Non-vacuity: an explicit competitive equilibrium (linear technology `ρk + ℓ`,
  `u = c − ℓ²/2`, zero taxes) satisfies Definition 15.1 (`dt_example_ce`).

Departures: the book leaves the domains of `c` and `ℓ` open; we impose only the borrowing
constraint `k_{t+1} ≥ 0` of Definition 15.1 and let `u` be any function on `ℝ × ℝ`,
differentiable where the first-order conditions are taken. Lifetime utility is the `tsum` of a
summable sequence; the household optimum is over plans with summable utility.
-/

namespace AKMM.FiscalPolicy

open Filter Topology

/-- A government policy `{τ_{c,t}, τ_{k,t}, τ_{ℓ,t}, G_t, T_t}` (AKMM, p. 446). -/
structure DTPolicy where
  τc : ℕ → ℝ
  τk : ℕ → ℝ
  τl : ℕ → ℝ
  G : ℕ → ℝ
  T : ℕ → ℝ

/-- A household plan, or an aggregate allocation, `{c_t, ℓ_t, k_t}`; `k 0` is initial capital. -/
structure DTPlan where
  c : ℕ → ℝ
  l : ℕ → ℝ
  k : ℕ → ℝ

/-- The household budget constraint (15.5), AKMM p. 446:
`(1 + τ_{c,t})c_t + k_{t+1} = (1 − τ_{ℓ,t})w_tℓ_t + k_t + (1 − τ_{k,t})(r_t − δ)k_t + T_t`. -/
def dtBudget (δ : ℝ) (p : DTPolicy) (w r : ℕ → ℝ) (x : DTPlan) (t : ℕ) : Prop :=
  (1 + p.τc t) * x.c t + x.k (t + 1) =
    (1 - p.τl t) * w t * x.l t + x.k t + (1 - p.τk t) * (r t - δ) * x.k t + p.T t

/-- The household's feasible plans (Definition 15.1(i)): (15.5) at every date, `k₀ = K₀` and the
borrowing constraint `k_{t+1} ≥ 0`. -/
def dtFeasible (δ K0 : ℝ) (p : DTPolicy) (w r : ℕ → ℝ) (x : DTPlan) : Prop :=
  x.k 0 = K0 ∧ ∀ t, dtBudget δ p w r x t ∧ 0 ≤ x.k (t + 1)

/-- The discounted utility sequence `βᵗu(c_t, ℓ_t)`. -/
def dtUtil (β : ℝ) (u : ℝ → ℝ → ℝ) (x : DTPlan) (t : ℕ) : ℝ := β ^ t * u (x.c t) (x.l t)

/-- Definition 15.1(i): `x` maximises `∑βᵗu(c_t, ℓ_t)` among feasible plans (with summable
utility). -/
def dtHHOptimal (β : ℝ) (u : ℝ → ℝ → ℝ) (δ K0 : ℝ) (p : DTPolicy) (w r : ℕ → ℝ)
    (x : DTPlan) : Prop :=
  dtFeasible δ K0 p w r x ∧ Summable (dtUtil β u x) ∧
    ∀ y, dtFeasible δ K0 p w r y → Summable (dtUtil β u y) →
      ∑' t, dtUtil β u y t ≤ ∑' t, dtUtil β u x t

/-- Definition 15.1(ii): at each date `(K_t, L_t)` maximises `f(k, ℓ) − w_tℓ − r_tk` over
`k, ℓ ≥ 0`. -/
def dtFirmOptimal (f : ℝ → ℝ → ℝ) (w r : ℕ → ℝ) (x : DTPlan) : Prop :=
  ∀ t k l, 0 ≤ k → 0 ≤ l →
    f k l - w t * l - r t * k ≤ f (x.k t) (x.l t) - w t * x.l t - r t * x.k t

/-- The government budget constraint (15.4), AKMM p. 446:
`G_t + T_t = τ_{c,t}C_t + τ_{ℓ,t}w_tL_t + τ_{k,t}(r_t − δ)K_t`. -/
def dtGovBudget (δ : ℝ) (p : DTPolicy) (w r : ℕ → ℝ) (x : DTPlan) (t : ℕ) : Prop :=
  p.G t + p.T t = p.τc t * x.c t + p.τl t * w t * x.l t + p.τk t * (r t - δ) * x.k t

/-- The resource constraint (15.3), AKMM p. 446:
`C_t + G_t + K_{t+1} = f(K_t, L_t) + (1 − δ)K_t`. -/
def dtResource (f : ℝ → ℝ → ℝ) (δ : ℝ) (G : ℕ → ℝ) (x : DTPlan) (t : ℕ) : Prop :=
  x.c t + G t + x.k (t + 1) = f (x.k t) (x.l t) + (1 - δ) * x.k t

/-- **Definition 15.1** (AKMM, p. 446): a competitive equilibrium given a policy is an allocation
`{C_t, L_t, K_{t+1}}` and prices `{w_t, r_t}` such that (i) the allocation solves the household
problem, (ii) it solves the firms' problem with `ℓ_t = L_t`, `k_t = K_t`, and (iii) the
government budget (15.4) holds at each date. -/
def definition_15_1 (β : ℝ) (u f : ℝ → ℝ → ℝ) (δ K0 : ℝ) (p : DTPolicy) (w r : ℕ → ℝ)
    (x : DTPlan) : Prop :=
  dtHHOptimal β u δ K0 p w r x ∧ dtFirmOptimal f w r x ∧ ∀ t, dtGovBudget δ p w r x t

/-- `u` is differentiable at `(c, ℓ)` with partial derivatives `u₁ = u1`, `u₂ = u2`. -/
def DTPartials (u : ℝ → ℝ → ℝ) (c l u1 u2 : ℝ) : Prop :=
  HasFDerivAt (Function.uncurry u)
    (u1 • ContinuousLinearMap.fst ℝ ℝ ℝ + u2 • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, l)

/-- Chain rule along a curve: if `h, g` have derivatives `h', g'` at `0` with `h 0 = g 0 = 0`,
then `ε ↦ u(c + h ε, ℓ + g ε)` has derivative `u₁h' + u₂g'` at `0`. -/
theorem dt_curve_hasDerivAt {u : ℝ → ℝ → ℝ} {c l u1 u2 : ℝ} (hu : DTPartials u c l u1 u2)
    {h g : ℝ → ℝ} {h' g' : ℝ} (hh : HasDerivAt h h' 0) (hg : HasDerivAt g g' 0) (h0 : h 0 = 0)
    (g0 : g 0 = 0) :
    HasDerivAt (fun ε => u (c + h ε) (l + g ε)) (u1 * h' + u2 * g') 0 := by
  have hγ : HasDerivAt (fun ε => (c + h ε, l + g ε)) (h', g') 0 :=
    (hh.const_add c).prodMk (hg.const_add l)
  have hγ0 : (c, l) = (c + h 0, l + g 0) := by simp [h0, g0]
  have key := hu.comp_hasDerivAt_of_eq 0 hγ hγ0
  refine (key.congr_deriv (by simp)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun z => rfl

/-- A perturbation of a summable sequence at two dates `t, t + 1` is summable, and its sum
changes by exactly the two altered terms. -/
theorem dt_tsum_two_point {U V : ℕ → ℝ} {t : ℕ} (hU : Summable U)
    (hV : ∀ s, s ≠ t → s ≠ t + 1 → V s = U s) :
    Summable V ∧ ∑' s, V s = ∑' s, U s + ((V t - U t) + (V (t + 1) - U (t + 1))) := by
  have hD : ∀ s ∉ ({t, t + 1} : Finset ℕ), V s - U s = 0 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rw [hV s hs.1 hs.2, sub_self]
  have hDs : Summable (fun s => V s - U s) := summable_of_ne_finset_zero hD
  have hVeq : (fun s => U s + (V s - U s)) = V := by
    funext s
    ring
  have hsum : Summable V := hVeq ▸ hU.add hDs
  refine ⟨hsum, ?_⟩
  calc ∑' s, V s = ∑' s, (U s + (V s - U s)) := by simp
    _ = ∑' s, U s + ∑' s, (V s - U s) := hU.tsum_add hDs
    _ = _ := by rw [tsum_eq_sum hD, Finset.sum_pair (by omega : t ≠ t + 1)]

/-- If every small perturbation `y ε` (`|ε| < η`) is feasible, has a summable utility sequence
equal to `x`'s except at `t, t + 1`, then at an optimum the change `g ε` of those two terms has a
local maximum at `0`. -/
theorem dt_local_max {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ}
    {x : DTPlan} (hx : dtHHOptimal β u δ K0 p w r x) {t : ℕ} {η : ℝ} (hη : 0 < η)
    (y : ℝ → DTPlan) (hy : ∀ ε, |ε| < η → dtFeasible δ K0 p w r (y ε))
    (hyu : ∀ ε s, s ≠ t → s ≠ t + 1 → dtUtil β u (y ε) s = dtUtil β u x s)
    (hy0 : ∀ s, dtUtil β u (y 0) s = dtUtil β u x s) :
    IsLocalMax (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
      (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1))) 0 := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < η := by
    have : Metric.ball (0 : ℝ) η ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hη
    filter_upwards [this] with ε hε
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  filter_upwards [hev] with ε hε
  obtain ⟨hs, heq⟩ := dt_tsum_two_point (t := t) hx.2.1 (hyu ε)
  have hle := hx.2.2 (y ε) (hy ε hε) hs
  simp only [hy0, sub_self, add_zero]
  linarith

/-- **(15.6)** (AKMM, p. 446): at a household optimum with `k_{t+1} > 0`, `1 + τ_c > 0` at `t`
and `t + 1`, and `u` differentiable at the optimum with `u₁(t + 1) ≠ 0`,
`((1 + τ_{c,t+1})/(1 + τ_{c,t}))u₁(c_t, ℓ_t)/u₁(c_{t+1}, ℓ_{t+1}) =
β[1 + (1 − τ_{k,t+1})(r_{t+1} − δ)]`. -/
theorem eq_15_6 {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ} {x : DTPlan}
    (hx : dtHHOptimal β u δ K0 p w r x) (t : ℕ) (hk : 0 < x.k (t + 1)) (hβ : 0 < β)
    (hc0 : 0 < 1 + p.τc t) (hc1 : 0 < 1 + p.τc (t + 1)) {a0 b0 a1 b1 : ℝ}
    (hu0 : DTPartials u (x.c t) (x.l t) a0 b0)
    (hu1 : DTPartials u (x.c (t + 1)) (x.l (t + 1)) a1 b1) (ha1 : a1 ≠ 0) :
    (1 + p.τc (t + 1)) / (1 + p.τc t) * (a0 / a1) =
      β * (1 + (1 - p.τk (t + 1)) * (r (t + 1) - δ)) := by
  set R := 1 + (1 - p.τk (t + 1)) * (r (t + 1) - δ) with hR
  set A := 1 / (1 + p.τc t)
  set B := R / (1 + p.τc (t + 1))
  let y : ℝ → DTPlan := fun ε =>
    { c := Function.update (Function.update x.c t (x.c t + (-A) * ε)) (t + 1)
        (x.c (t + 1) + B * ε)
      l := x.l
      k := Function.update x.k (t + 1) (x.k (t + 1) + ε) }
  have ht1 : t ≠ t + 1 := by omega
  have hyc_t : ∀ ε, (y ε).c t = x.c t + (-A) * ε := by
    intro ε
    simp [y]
  have hyc_t1 : ∀ ε, (y ε).c (t + 1) = x.c (t + 1) + B * ε := by
    intro ε
    simp [y]
  have hyc : ∀ ε s, s ≠ t → s ≠ t + 1 → (y ε).c s = x.c s := by
    intro ε s h1 h2
    simp [y, Function.update_of_ne h1, Function.update_of_ne h2]
  have hyk : ∀ ε s, s ≠ t + 1 → (y ε).k s = x.k s := by
    intro ε s h
    simp [y, Function.update_of_ne h]
  have hyk1 : ∀ ε, (y ε).k (t + 1) = x.k (t + 1) + ε := by
    intro ε
    simp [y]
  have hfeas : ∀ ε, |ε| < x.k (t + 1) → dtFeasible δ K0 p w r (y ε) := by
    intro ε hε
    obtain ⟨hk0, hb⟩ := hx.1
    refine ⟨by rw [hyk ε 0 (by omega)]; exact hk0, fun s => ?_⟩
    obtain ⟨hbs, hks⟩ := hb s
    refine ⟨?_, ?_⟩
    · unfold dtBudget at hbs ⊢
      have hyl : (y ε).l = x.l := rfl
      rw [hyl]
      by_cases hs : s = t
      · subst hs
        rw [hyc_t, hyk1, hyk ε s (by omega)]
        have : (1 + p.τc s) * A = 1 := by
          simp only [A]
          field_simp
        linear_combination hbs - this * ε
      · by_cases hs1 : s = t + 1
        · subst hs1
          rw [hyc_t1, hyk1, hyk ε (t + 1 + 1) (by omega)]
          have : (1 + p.τc (t + 1)) * B = R := by
            simp only [B]
            field_simp
          linear_combination hbs + this * ε
        · rw [hyc ε s hs hs1, hyk ε s hs1, hyk ε (s + 1) (by omega)]
          exact hbs
    · by_cases hs : s = t
      · subst hs
        rw [hyk1]
        have := neg_abs_le ε
        linarith
      · rw [hyk ε (s + 1) (by omega)]
        exact hks
  have hmax := dt_local_max (t := t) hx hk y hfeas (fun ε s h1 h2 => by
    simp only [dtUtil, hyc ε s h1 h2]
    rfl) (fun s => by simp [dtUtil, y])
  have hd0 := dt_curve_hasDerivAt (h := fun ε => (-A) * ε) (g := fun _ => 0) hu0
    ((hasDerivAt_id 0).const_mul (-A)) (hasDerivAt_const 0 0) (by simp) rfl
  have hd1 := dt_curve_hasDerivAt (h := fun ε => B * ε) (g := fun _ => 0) hu1
    ((hasDerivAt_id 0).const_mul B) (hasDerivAt_const 0 0) (by simp) rfl
  have hg : HasDerivAt (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
      (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1)))
      (β ^ t * (a0 * (-A * 1) + b0 * 0) + β ^ (t + 1) * (a1 * (B * 1) + b1 * 0)) 0 := by
    have e : (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
        (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1))) =
        fun ε => (β ^ t * u (x.c t + (-A) * ε) (x.l t + 0) - dtUtil β u x t) +
          (β ^ (t + 1) * u (x.c (t + 1) + B * ε) (x.l (t + 1) + 0) - dtUtil β u x (t + 1)) := by
      funext ε
      simp only [dtUtil, hyc_t, hyc_t1, add_zero]
      rfl
    rw [e]
    exact ((hd0.const_mul (β ^ t)).sub_const _).add ((hd1.const_mul (β ^ (t + 1))).sub_const _)
  have hzero := hmax.hasDerivAt_eq_zero hg
  have hβt : 0 < β ^ t := pow_pos hβ t
  have key : a0 * A = β * (a1 * B) := by
    have : β ^ t * (a0 * A - β * (a1 * B)) = 0 := by
      rw [pow_succ] at hzero
      linear_combination -hzero
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hβt.ne'
    · linarith
  simp only [A, B] at key
  field_simp
  field_simp at key
  linear_combination key

/-- **(15.6), labour** (AKMM, p. 446): at a household optimum with `1 + τ_{c,t} ≠ 0` and `u`
differentiable at `(c_t, ℓ_t)`, `−u₂(c_t, ℓ_t) = ((1 − τ_{ℓ,t})/(1 + τ_{c,t}))w_tu₁(c_t, ℓ_t)`. -/
theorem dt_labour_foc {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ}
    {x : DTPlan} (hx : dtHHOptimal β u δ K0 p w r x) (t : ℕ) (hβ : 0 < β)
    (hc0 : 1 + p.τc t ≠ 0) {a0 b0 : ℝ} (hu0 : DTPartials u (x.c t) (x.l t) a0 b0) :
    -b0 = (1 - p.τl t) / (1 + p.τc t) * w t * a0 := by
  set A := (1 - p.τl t) / (1 + p.τc t) * w t
  let y : ℝ → DTPlan := fun ε =>
    { c := Function.update x.c t (x.c t + A * ε)
      l := Function.update x.l t (x.l t + 1 * ε)
      k := x.k }
  have hyc : ∀ ε s, s ≠ t → (y ε).c s = x.c s := by
    intro ε s h
    simp [y, Function.update_of_ne h]
  have hyl : ∀ ε s, s ≠ t → (y ε).l s = x.l s := by
    intro ε s h
    simp [y, Function.update_of_ne h]
  have hfeas : ∀ ε, |ε| < 1 → dtFeasible δ K0 p w r (y ε) := by
    intro ε _
    obtain ⟨hk0, hb⟩ := hx.1
    refine ⟨hk0, fun s => ⟨?_, (hb s).2⟩⟩
    have hbs := (hb s).1
    unfold dtBudget at hbs ⊢
    have hyk : (y ε).k = x.k := rfl
    rw [hyk]
    by_cases hs : s = t
    · subst hs
      have h1 : (y ε).c s = x.c s + A * ε := by simp [y]
      have h2 : (y ε).l s = x.l s + 1 * ε := by simp [y]
      rw [h1, h2]
      have : (1 + p.τc s) * A = (1 - p.τl s) * w s := by
        simp only [A]
        field_simp
      linear_combination hbs + this * ε
    · rw [hyc ε s hs, hyl ε s hs]
      exact hbs
  have hmax := dt_local_max (t := t) hx one_pos y hfeas (fun ε s h1 _ => by
    simp only [dtUtil, hyc ε s h1, hyl ε s h1]) (fun s => by simp [dtUtil, y])
  have hd0 := dt_curve_hasDerivAt (h := fun ε => A * ε) (g := fun ε => 1 * ε) hu0
    ((hasDerivAt_id 0).const_mul A) ((hasDerivAt_id 0).const_mul 1) (by simp) (by simp)
  have hg : HasDerivAt (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
      (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1)))
      (β ^ t * (a0 * (A * 1) + b0 * (1 * 1)) + 0) 0 := by
    have e : (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
        (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1))) =
        fun ε => (β ^ t * u (x.c t + A * ε) (x.l t + 1 * ε) - dtUtil β u x t) + 0 := by
      funext ε
      have h1 : (y ε).c t = x.c t + A * ε := by simp [y]
      have h2 : (y ε).l t = x.l t + 1 * ε := by simp [y]
      simp only [dtUtil, h1, h2, hyc ε (t + 1) (by omega), hyl ε (t + 1) (by omega), sub_self]
    rw [e]
    exact ((hd0.const_mul (β ^ t)).sub_const _).add (hasDerivAt_const 0 0)
  have hzero := hmax.hasDerivAt_eq_zero hg
  have hβt : 0 < β ^ t := pow_pos hβ t
  have : β ^ t * (a0 * A + b0) = 0 := by linear_combination hzero
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hβt.ne'
  · linarith

/-- AKMM, p. 447: the profit-maximisation conditions `w_t = f₂(k_t, ℓ_t)` and
`r_t = f₁(k_t, ℓ_t)` at positive inputs, for `f` with partial derivatives `f₁, f₂` there. -/
theorem dt_firm_foc {f : ℝ → ℝ → ℝ} {w r : ℕ → ℝ} {x : DTPlan} (hx : dtFirmOptimal f w r x)
    (t : ℕ) (hk : 0 < x.k t) (hl : 0 < x.l t) {f1 f2 : ℝ}
    (hf1 : HasDerivAt (fun k => f k (x.l t)) f1 (x.k t))
    (hf2 : HasDerivAt (fun l => f (x.k t) l) f2 (x.l t)) :
    w t = f2 ∧ r t = f1 := by
  constructor
  · have hmax : IsLocalMax (fun l => f (x.k t) l - w t * l - r t * x.k t) (x.l t) := by
      filter_upwards [lt_mem_nhds hl] with l hl'
      exact hx t (x.k t) l hk.le hl'.le
    have hd : HasDerivAt (fun l => f (x.k t) l - w t * l - r t * x.k t) (f2 - w t)
        (x.l t) := by
      have := (hf2.sub ((hasDerivAt_id (x.l t)).const_mul (w t))).sub_const (r t * x.k t)
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun z => by simp
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  · have hmax : IsLocalMax (fun k => f k (x.l t) - w t * x.l t - r t * k) (x.k t) := by
      filter_upwards [lt_mem_nhds hk] with k hk'
      exact hx t k (x.l t) hk'.le hl.le
    have hd : HasDerivAt (fun k => f k (x.l t) - w t * x.l t - r t * k) (f1 - r t)
        (x.k t) := by
      have := (hf1.sub_const (w t * x.l t)).sub ((hasDerivAt_id (x.k t)).const_mul (r t))
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun z => by simp
    have := hmax.hasDerivAt_eq_zero hd
    linarith

/-- AKMM, p. 446, market clearing: with `w = f₂`, `r = f₁` and constant returns
`f = f₁k + f₂ℓ`, the household budget (15.5) and the government budget (15.4) at date `t` imply
the resource constraint (15.3) (Walras' law). -/
theorem dt_resource_of_budgets {f : ℝ → ℝ → ℝ} {δ : ℝ} {p : DTPolicy} {w r : ℕ → ℝ}
    {x : DTPlan} (t : ℕ) (hb : dtBudget δ p w r x t) (hg : dtGovBudget δ p w r x t)
    (hE : f (x.k t) (x.l t) = r t * x.k t + w t * x.l t) :
    dtResource f δ p.G x t := by
  unfold dtBudget at hb
  unfold dtGovBudget at hg
  unfold dtResource
  rw [hE]
  linear_combination hb + hg

/-- The planner's problem (AKMM, p. 447): `x` maximises `∑βᵗu(C_t, L_t)` subject to the
resource constraint (15.3), `K₀` given and `K_{t+1} ≥ 0`. -/
def dtPlannerOptimal (β : ℝ) (u f : ℝ → ℝ → ℝ) (δ K0 : ℝ) (G : ℕ → ℝ) (x : DTPlan) : Prop :=
  (x.k 0 = K0 ∧ ∀ t, dtResource f δ G x t ∧ 0 ≤ x.k (t + 1)) ∧ Summable (dtUtil β u x) ∧
    ∀ y : DTPlan, (y.k 0 = K0 ∧ ∀ t, dtResource f δ G y t ∧ 0 ≤ y.k (t + 1)) →
      Summable (dtUtil β u y) → ∑' t, dtUtil β u y t ≤ ∑' t, dtUtil β u x t

/-- AKMM, p. 447: a two-date perturbation of a planner's optimum gives a local maximum. -/
theorem dt_planner_local_max {β : ℝ} {u f : ℝ → ℝ → ℝ} {δ K0 : ℝ} {G : ℕ → ℝ} {x : DTPlan}
    (hx : dtPlannerOptimal β u f δ K0 G x) {t : ℕ} {η : ℝ} (hη : 0 < η) (y : ℝ → DTPlan)
    (hy : ∀ ε, |ε| < η → (y ε).k 0 = K0 ∧ ∀ s, dtResource f δ G (y ε) s ∧ 0 ≤ (y ε).k (s + 1))
    (hyu : ∀ ε s, s ≠ t → s ≠ t + 1 → dtUtil β u (y ε) s = dtUtil β u x s)
    (hy0 : ∀ s, dtUtil β u (y 0) s = dtUtil β u x s) :
    IsLocalMax (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
      (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1))) 0 := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < η := by
    have : Metric.ball (0 : ℝ) η ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hη
    filter_upwards [this] with ε hε
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  filter_upwards [hev] with ε hε
  obtain ⟨hs, heq⟩ := dt_tsum_two_point (t := t) hx.2.1 (hyu ε)
  have hle := hx.2.2 (y ε) (hy ε hε) hs
  simp only [hy0, sub_self, add_zero]
  linarith

/-- **(15.7), labour** (AKMM, p. 447): at a planner's optimum, with `f` differentiable in `ℓ` at
`(K_t, L_t)` and `u` differentiable at `(C_t, L_t)`, `−u₂(C_t, L_t) = f₂(K_t, L_t)u₁(C_t, L_t)`. -/
theorem eq_15_7 {β : ℝ} {u f : ℝ → ℝ → ℝ} {δ K0 : ℝ} {G : ℕ → ℝ} {x : DTPlan}
    (hx : dtPlannerOptimal β u f δ K0 G x) (t : ℕ) (hβ : 0 < β) {a0 b0 f2 : ℝ}
    (hu0 : DTPartials u (x.c t) (x.l t) a0 b0)
    (hf2 : HasDerivAt (fun l => f (x.k t) l) f2 (x.l t)) :
    -b0 = f2 * a0 := by
  set h : ℝ → ℝ := fun ε => f (x.k t) (x.l t + ε) - f (x.k t) (x.l t)
  let y : ℝ → DTPlan := fun ε =>
    { c := Function.update x.c t (x.c t + h ε)
      l := Function.update x.l t (x.l t + ε)
      k := x.k }
  have hyc : ∀ ε s, s ≠ t → (y ε).c s = x.c s := by
    intro ε s hs
    simp [y, Function.update_of_ne hs]
  have hyl : ∀ ε s, s ≠ t → (y ε).l s = x.l s := by
    intro ε s hs
    simp [y, Function.update_of_ne hs]
  have hyc_t : ∀ ε, (y ε).c t = x.c t + h ε := by intro ε; simp [y]
  have hyl_t : ∀ ε, (y ε).l t = x.l t + ε := by intro ε; simp [y]
  have hfeas : ∀ ε, |ε| < 1 →
      (y ε).k 0 = K0 ∧ ∀ s, dtResource f δ G (y ε) s ∧ 0 ≤ (y ε).k (s + 1) := by
    intro ε _
    obtain ⟨hk0, hb⟩ := hx.1
    refine ⟨hk0, fun s => ⟨?_, (hb s).2⟩⟩
    have hbs := (hb s).1
    unfold dtResource at hbs ⊢
    have hyk : (y ε).k = x.k := rfl
    rw [hyk]
    by_cases hs : s = t
    · subst hs
      rw [hyc_t, hyl_t]
      simp only [h]
      linarith
    · rw [hyc ε s hs, hyl ε s hs]
      exact hbs
  have hmax := dt_planner_local_max (t := t) hx one_pos y hfeas (fun ε s h1 _ => by
    simp only [dtUtil, hyc ε s h1, hyl ε s h1]) (fun s => by simp [dtUtil, y, h])
  have hh : HasDerivAt h f2 0 := by
    have h2 : HasDerivAt (fun l => f (x.k t) l) f2 (x.l t + 0) := by simpa using hf2
    have := (h2.comp_const_add (x.l t) 0).sub_const (f (x.k t) (x.l t))
    simpa [h] using this
  have hd0 := dt_curve_hasDerivAt (g := fun ε => ε) hu0 hh (hasDerivAt_id 0) (by simp [h]) rfl
  have hg : HasDerivAt (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
      (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1)))
      (β ^ t * (a0 * f2 + b0 * 1) + 0) 0 := by
    have e : (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
        (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1))) =
        fun ε => (β ^ t * u (x.c t + h ε) (x.l t + ε) - dtUtil β u x t) + 0 := by
      funext ε
      simp only [dtUtil, hyc_t, hyl_t, hyc ε (t + 1) (by omega), hyl ε (t + 1) (by omega),
        sub_self]
    rw [e]
    exact ((hd0.const_mul (β ^ t)).sub_const _).add (hasDerivAt_const 0 0)
  have hzero := hmax.hasDerivAt_eq_zero hg
  have hβt : 0 < β ^ t := pow_pos hβ t
  have : β ^ t * (a0 * f2 + b0) = 0 := by linear_combination hzero
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hβt.ne'
  · linarith

/-- **(15.7), Euler** (AKMM, p. 447): at a planner's optimum with `K_{t+1} > 0`, `f`
differentiable in `k` at `(K_{t+1}, L_{t+1})` and `u₁(t + 1) ≠ 0`,
`u₁(C_t, L_t)/u₁(C_{t+1}, L_{t+1}) = β[1 + f₁(K_{t+1}, L_{t+1}) − δ]`. -/
theorem dt_planner_euler {β : ℝ} {u f : ℝ → ℝ → ℝ} {δ K0 : ℝ} {G : ℕ → ℝ} {x : DTPlan}
    (hx : dtPlannerOptimal β u f δ K0 G x) (t : ℕ) (hk : 0 < x.k (t + 1)) (hβ : 0 < β)
    {a0 b0 a1 b1 f1 : ℝ} (hu0 : DTPartials u (x.c t) (x.l t) a0 b0)
    (hu1 : DTPartials u (x.c (t + 1)) (x.l (t + 1)) a1 b1) (ha1 : a1 ≠ 0)
    (hf1 : HasDerivAt (fun k => f k (x.l (t + 1))) f1 (x.k (t + 1))) :
    a0 / a1 = β * (1 + f1 - δ) := by
  set h : ℝ → ℝ := fun ε => f (x.k (t + 1) + ε) (x.l (t + 1)) - f (x.k (t + 1)) (x.l (t + 1)) +
    (1 - δ) * ε
  have ht1 : t ≠ t + 1 := by omega
  let y : ℝ → DTPlan := fun ε =>
    { c := Function.update (Function.update x.c t (x.c t + (-1) * ε)) (t + 1)
        (x.c (t + 1) + h ε)
      l := x.l
      k := Function.update x.k (t + 1) (x.k (t + 1) + ε) }
  have hyc_t : ∀ ε, (y ε).c t = x.c t + (-1) * ε := by
    intro ε
    simp [y]
  have hyc_t1 : ∀ ε, (y ε).c (t + 1) = x.c (t + 1) + h ε := by intro ε; simp [y]
  have hyc : ∀ ε s, s ≠ t → s ≠ t + 1 → (y ε).c s = x.c s := by
    intro ε s h1 h2
    simp [y, Function.update_of_ne h1, Function.update_of_ne h2]
  have hyk : ∀ ε s, s ≠ t + 1 → (y ε).k s = x.k s := by
    intro ε s hs
    simp [y, Function.update_of_ne hs]
  have hyk1 : ∀ ε, (y ε).k (t + 1) = x.k (t + 1) + ε := by intro ε; simp [y]
  have hfeas : ∀ ε, |ε| < x.k (t + 1) →
      (y ε).k 0 = K0 ∧ ∀ s, dtResource f δ G (y ε) s ∧ 0 ≤ (y ε).k (s + 1) := by
    intro ε hε
    obtain ⟨hk0, hb⟩ := hx.1
    refine ⟨by rw [hyk ε 0 (by omega)]; exact hk0, fun s => ?_⟩
    obtain ⟨hbs, hks⟩ := hb s
    have hyl : (y ε).l = x.l := rfl
    refine ⟨?_, ?_⟩
    · unfold dtResource at hbs ⊢
      rw [hyl]
      by_cases hs : s = t
      · subst hs
        rw [hyc_t, hyk1, hyk ε s (by omega)]
        linarith
      · by_cases hs1 : s = t + 1
        · subst hs1
          rw [hyc_t1, hyk1, hyk ε (t + 1 + 1) (by omega)]
          simp only [h]
          linarith
        · rw [hyc ε s hs hs1, hyk ε s hs1, hyk ε (s + 1) (by omega)]
          exact hbs
    · by_cases hs : s = t
      · subst hs
        rw [hyk1]
        have := neg_abs_le ε
        linarith
      · rw [hyk ε (s + 1) (by omega)]
        exact hks
  have hmax := dt_planner_local_max (t := t) hx hk y hfeas (fun ε s h1 h2 => by
    simp only [dtUtil, hyc ε s h1 h2]
    rfl) (fun s => by simp [dtUtil, y, h])
  have hh : HasDerivAt h (f1 + (1 - δ)) 0 := by
    have h1' : HasDerivAt (fun k => f k (x.l (t + 1))) f1 (x.k (t + 1) + 0) := by simpa using hf1
    have h1 := (h1'.comp_const_add (x.k (t + 1)) 0).sub_const (f (x.k (t + 1)) (x.l (t + 1)))
    have h2 := (hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)
    have := h1.add h2
    refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun z => by simp [h]
  have hd0 := dt_curve_hasDerivAt (h := fun ε => (-1) * ε) (g := fun _ => 0) hu0
    ((hasDerivAt_id 0).const_mul (-1)) (hasDerivAt_const 0 0) (by simp) rfl
  have hd1 := dt_curve_hasDerivAt (g := fun _ => 0) hu1 hh (hasDerivAt_const 0 0)
    (by simp [h]) rfl
  have hg : HasDerivAt (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
      (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1)))
      (β ^ t * (a0 * (-1 * 1) + b0 * 0) + β ^ (t + 1) * (a1 * (f1 + (1 - δ)) + b1 * 0)) 0 := by
    have e : (fun ε => (dtUtil β u (y ε) t - dtUtil β u x t) +
        (dtUtil β u (y ε) (t + 1) - dtUtil β u x (t + 1))) =
        fun ε => (β ^ t * u (x.c t + (-1) * ε) (x.l t + 0) - dtUtil β u x t) +
          (β ^ (t + 1) * u (x.c (t + 1) + h ε) (x.l (t + 1) + 0) - dtUtil β u x (t + 1)) := by
      funext ε
      simp only [dtUtil, hyc_t, hyc_t1, add_zero]
      rfl
    rw [e]
    exact ((hd0.const_mul (β ^ t)).sub_const _).add ((hd1.const_mul (β ^ (t + 1))).sub_const _)
  have hzero := hmax.hasDerivAt_eq_zero hg
  have hβt : 0 < β ^ t := pow_pos hβ t
  have key : a0 = β * (a1 * (1 + f1 - δ)) := by
    have : β ^ t * (a0 - β * (a1 * (1 + f1 - δ))) = 0 := by
      rw [pow_succ] at hzero
      linear_combination -hzero
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hβt.ne'
    · linarith
  rw [key]
  field_simp

/-- AKMM, p. 447: "Absent taxes, households equate the inter-temporal marginal rate of
substitution … to one plus the marginal product of capital, net of depreciation": with
`τ_c = τ_k = 0` and `r_{t+1} = f₁`, the household's (15.6) is the planner's Euler equation. -/
theorem dt_no_tax_euler {β a0 a1 r1 f1 δ : ℝ} (hr : r1 = f1)
    (h : (1 + 0) / (1 + 0) * (a0 / a1) = β * (1 + (1 - 0) * (r1 - δ))) :
    a0 / a1 = β * (1 + f1 - δ) := by
  rw [← hr]
  simpa [add_sub_assoc] using h

/-! ### A competitive equilibrium (non-vacuity of Definition 15.1) -/

/-- The example economy's utility `u(c, ℓ) = c − ℓ²/2`. -/
noncomputable def dtExU (c l : ℝ) : ℝ := c - l ^ 2 / 2

/-- The example economy's technology `f(k, ℓ) = ρk + ℓ`. -/
def dtExF (ρ k l : ℝ) : ℝ := ρ * k + l

/-- The zero-tax, zero-spending policy. -/
def dtZeroPolicy : DTPolicy := ⟨0, 0, 0, 0, 0⟩

/-- The example equilibrium allocation: `c_t = ρK₀ + 1`, `ℓ_t = 1`, `k_t = K₀`. -/
def dtExPlan (ρ K0 : ℝ) : DTPlan := ⟨fun _ => ρ * K0 + 1, fun _ => 1, fun _ => K0⟩

/-- **Definition 15.1 is not vacuous**: for `0 < β < 1`, `ρ = (1 − β)/β`, `δ = 0`, `K₀ ≥ 0`,
technology `ρk + ℓ` and utility `c − ℓ²/2`, the zero policy with prices `w = 1`, `r = ρ` and the
constant allocation `(ρK₀ + 1, 1, K₀)` is a competitive equilibrium. -/
theorem dt_example_ce {β K0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hK : 0 ≤ K0) :
    definition_15_1 β dtExU (dtExF ((1 - β) / β)) 0 K0 dtZeroPolicy (fun _ => 1)
      (fun _ => (1 - β) / β) (dtExPlan ((1 - β) / β) K0) := by
  set ρ := (1 - β) / β with hρ
  have hβρ : β * (1 + ρ) = 1 := by
    rw [hρ]
    field_simp
    ring
  have hgeo : Summable (fun t : ℕ => β ^ t) :=
    summable_geometric_of_lt_one hβ0.le hβ1
  have hxu : dtUtil β dtExU (dtExPlan ρ K0) = fun t => (ρ * K0 + 1 / 2) * β ^ t := by
    funext t
    simp only [dtUtil, dtExU, dtExPlan]
    ring
  refine ⟨⟨⟨rfl, fun t => ⟨?_, hK⟩⟩, ?_, ?_⟩, ?_, ?_⟩
  · simp only [dtBudget, dtZeroPolicy, dtExPlan, Pi.zero_apply]
    ring
  · rw [hxu]
    exact hgeo.mul_left _
  · intro y ⟨hy0, hy⟩ hys
    rw [hxu, tsum_mul_left, tsum_geometric_of_lt_one hβ0.le hβ1]
    -- the telescoped budget: `∑_{t<T} βᵗ(c_t − ℓ_t) = (1 + ρ)k₀ − βᵀ(1 + ρ)k_T`
    have htel : ∀ T, ∑ t ∈ Finset.range T, β ^ t * (y.c t - y.l t) =
        (1 + ρ) * y.k 0 - β ^ T * (1 + ρ) * y.k T := by
      intro T
      induction T with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have hb := (hy n).1
        simp only [dtBudget, dtZeroPolicy, Pi.zero_apply] at hb
        have hc : y.c n - y.l n = (1 + ρ) * y.k n - y.k (n + 1) := by linarith
        rw [hc, pow_succ]
        linear_combination (β ^ n * y.k (n + 1)) * hβρ
    apply hys.tsum_le_of_sum_range_le
    intro T
    have hsplit : ∑ t ∈ Finset.range T, dtUtil β dtExU y t =
        ∑ t ∈ Finset.range T, β ^ t * (y.c t - y.l t) +
          ∑ t ∈ Finset.range T, β ^ t * (y.l t - y.l t ^ 2 / 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [dtUtil, dtExU]
      ring
    have hl : ∑ t ∈ Finset.range T, β ^ t * (y.l t - y.l t ^ 2 / 2) ≤
        ∑ t ∈ Finset.range T, β ^ t * (1 / 2) := by
      refine Finset.sum_le_sum fun t _ => ?_
      have hbt : 0 ≤ β ^ t := pow_nonneg hβ0.le t
      have : y.l t - y.l t ^ 2 / 2 ≤ 1 / 2 := by nlinarith [sq_nonneg (y.l t - 1)]
      exact mul_le_mul_of_nonneg_left this hbt
    have hgsum : ∑ t ∈ Finset.range T, β ^ t * (1 / 2) ≤ (1 / 2) * (1 - β)⁻¹ := by
      rw [← Finset.sum_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [← tsum_geometric_of_lt_one hβ0.le hβ1]
      exact hgeo.sum_le_tsum _ (fun i _ => pow_nonneg hβ0.le i)
    have hkT : 0 ≤ β ^ T * (1 + ρ) * y.k T := by
      have h1ρ : 0 < 1 + ρ := by
        rw [hρ]
        have : 0 ≤ (1 - β) / β := div_nonneg (by linarith) hβ0.le
        linarith
      have hk : 0 ≤ y.k T := by
        cases T with
        | zero => rw [hy0]; exact hK
        | succ n => exact (hy n).2
      exact mul_nonneg (mul_nonneg (pow_nonneg hβ0.le T) h1ρ.le) hk
    have hρK : (1 + ρ) * K0 = ρ * K0 * (1 - β)⁻¹ := by
      rw [hρ]
      have : (1 - β) ≠ 0 := by linarith
      field_simp
      ring
    rw [hsplit, htel T, hy0]
    nlinarith [hρK]
  · intro t k l _ _
    simp only [dtExF, dtExPlan]
    linarith
  · intro t
    simp only [dtGovBudget, dtZeroPolicy, Pi.zero_apply]
    ring

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Long-run distortions and GHH labour supply

AKMM, §15.3.1, (15.8)–(15.12), pp. 447–448.

* (15.8): in a steady state with constant taxes the Euler equation (15.6) becomes
  `1 = β[1 + (1 − τ_k)(r − δ)]` (`eq_15_8`), and the labour condition (15.9) holds
  (`eq_15_9`). Equivalently `r = δ + ρ/(1 − τ_k)`, `ρ = (1 − β)/β` (`lr_rent_iff`), so "a higher
  capital income tax `τ_k` must increase the steady-state equilibrium rental rate"
  (`lr_rent_strictMonoOn`).
* Cobb–Douglas `f = k^αℓ^{1−α}`: partial derivatives `f₁ = α(k/ℓ)^{α−1}`, `f₂ = (1 − α)(k/ℓ)^α`
  (`lr_cd_hasDerivAt_k`, `lr_cd_hasDerivAt_l`), and (15.11)
  `k/ℓ = (α(1 − τ_k)/(ρ + δ(1 − τ_k)))^{1/(1−α)}` (`eq_15_11`). The ratio is strictly decreasing
  in `τ_k` (`lr_ratio_strictAntiOn`), and so is the wage (15.10) (`lr_wage_strictAntiOn`);
  `r` and `w` depend on `τ_k` only (`lrRent`, `lrWage` take no `τ_ℓ`, `τ_c`).
* GHH utility `log(c − ℓ^{1+1/φ}/(1 + 1/φ))` (`ghhU`) has partials `u₁ = 1/(c − v)`,
  `u₂ = −ℓ^{1/φ}/(c − v)` (`ghh_partials`), so (15.9) gives (15.12)
  `ℓ = ((1 − τ_ℓ)/(1 + τ_c))^φw^φ` (`eq_15_12`): consumption drops out. Hours fall with `τ_ℓ`,
  with `τ_c` and, through `w`, with `τ_k` (`lr_hours_strictAntiOn_labour`,
  `lr_hours_strictAntiOn_cons`, `lr_hours_strictAntiOn_capital`).

Departures: none.
-/

namespace AKMM.FiscalPolicy

open Real

/-- **(15.8)** (AKMM, p. 447): at a household optimum that is a steady state (constant
`c, ℓ, k > 0` and constant `τ_c > −1`, `τ_k`, `r` at dates `0, 1`) with `u` differentiable and
`u₁ ≠ 0`, `1 = β[1 + (1 − τ_k)(r − δ)]`. -/
theorem eq_15_8 {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ} {x : DTPlan}
    (hx : dtHHOptimal β u δ K0 p w r x) (hβ : 0 < β) {c l k τc τk r0 a b : ℝ}
    (hc : x.c 0 = c ∧ x.c 1 = c) (hl : x.l 0 = l ∧ x.l 1 = l) (hk : x.k 1 = k) (hk0 : 0 < k)
    (hτc : p.τc 0 = τc ∧ p.τc 1 = τc) (hτk : p.τk 1 = τk) (hr : r 1 = r0) (hτ : 0 < 1 + τc)
    (hu : DTPartials u c l a b) (ha : a ≠ 0) :
    1 = β * (1 + (1 - τk) * (r0 - δ)) := by
  have h := eq_15_6 hx 0 (by rw [zero_add, hk]; exact hk0) hβ
    (by rw [hτc.1]; exact hτ) (by rw [zero_add, hτc.2]; exact hτ)
    (by rw [hc.1, hl.1]; exact hu) (by rw [zero_add, hc.2, hl.2]; exact hu) ha
  rw [zero_add, hτc.1, hτc.2, hτk, hr, div_self hτ.ne', div_self ha, one_mul] at h
  exact h

/-- **(15.9)** (AKMM, p. 448): in a steady state, `−u₂(c, ℓ) = ((1 − τ_ℓ)/(1 + τ_c))wu₁(c, ℓ)`. -/
theorem eq_15_9 {β : ℝ} {u : ℝ → ℝ → ℝ} {δ K0 : ℝ} {p : DTPolicy} {w r : ℕ → ℝ} {x : DTPlan}
    (hx : dtHHOptimal β u δ K0 p w r x) (hβ : 0 < β) {c l τc τl w0 a b : ℝ}
    (hc : x.c 0 = c) (hl : x.l 0 = l) (hτc : p.τc 0 = τc) (hτl : p.τl 0 = τl) (hw : w 0 = w0)
    (hτ : 1 + τc ≠ 0) (hu : DTPartials u c l a b) :
    -b = (1 - τl) / (1 + τc) * w0 * a := by
  have h := dt_labour_foc hx 0 hβ (by rw [hτc]; exact hτ) (by rw [hc, hl]; exact hu)
  rwa [hτc, hτl, hw] at h

/-- The household's rate of time preference `ρ = (1 − β)/β` (AKMM, p. 448). -/
noncomputable def lrRho (β : ℝ) : ℝ := (1 - β) / β

/-- The steady-state rental rate `r = δ + ρ/(1 − τ_k)` implied by (15.8). -/
noncomputable def lrRent (β δ τk : ℝ) : ℝ := δ + lrRho β / (1 - τk)

/-- AKMM, p. 448: for `β > 0` and `τ_k < 1`, (15.8) holds iff `r = δ + ρ/(1 − τ_k)`. -/
theorem lr_rent_iff {β δ τk r : ℝ} (hβ : 0 < β) (hτ : τk < 1) :
    1 = β * (1 + (1 - τk) * (r - δ)) ↔ r = lrRent β δ τk := by
  have h1 : (1 - τk) ≠ 0 := by linarith
  unfold lrRent lrRho
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, p. 448: "a higher capital income tax `τ_k` must increase the steady-state equilibrium
rental rate for capital `r`" (for `0 < β < 1`). -/
theorem lr_rent_strictMonoOn {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StrictMonoOn (lrRent β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have ha' : 0 < 1 - a := by have := Set.mem_Iio.mp ha; linarith
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  unfold lrRent
  have : lrRho β / (1 - a) < lrRho β / (1 - b) :=
    div_lt_div_of_pos_left hρ hb' (by linarith)
  linarith

/-- AKMM, p. 448: Cobb–Douglas `f(k, ℓ) = k^αℓ^{1−α}` has `f₁ = α(k/ℓ)^{α−1}` at `k, ℓ > 0`. -/
theorem lr_cd_hasDerivAt_k {α k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    HasDerivAt (fun k => k ^ α * l ^ (1 - α)) (α * (k / l) ^ (α - 1)) k := by
  have h := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).mul_const (l ^ (1 - α))
  convert h using 1
  rw [Real.div_rpow hk.le hl.le, div_eq_mul_inv, ← Real.rpow_neg hl.le, neg_sub]
  ring

/-- AKMM, (15.10), p. 448: Cobb–Douglas has `f₂ = (1 − α)(k/ℓ)^α` at `k, ℓ > 0`. -/
theorem lr_cd_hasDerivAt_l {α k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    HasDerivAt (fun l => k ^ α * l ^ (1 - α)) ((1 - α) * (k / l) ^ α) l := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hl.ne')).const_mul (k ^ α)
  convert h using 1
  rw [Real.div_rpow hk.le hl.le, div_eq_mul_inv, ← Real.rpow_neg hl.le,
    show (1 - α - 1) = -α by ring]
  ring

/-- `s(τ_k) = α(1 − τ_k)/(ρ + δ(1 − τ_k))`, the base of (15.11), equal to `(k/ℓ)^{1−α}`. -/
noncomputable def lrS (α β δ τk : ℝ) : ℝ := α * (1 - τk) / (lrRho β + δ * (1 - τk))

/-- The steady-state capital–labour ratio (15.11). -/
noncomputable def lrRatio (α β δ τk : ℝ) : ℝ := lrS α β δ τk ^ (1 / (1 - α))

/-- The steady-state wage `w = (1 − α)(k/ℓ)^α` (15.10). -/
noncomputable def lrWage (α β δ τk : ℝ) : ℝ := (1 - α) * lrRatio α β δ τk ^ α

/-- AKMM, p. 448: `s(τ_k) = α/r` with `r = δ + ρ/(1 − τ_k)` from (15.8). -/
theorem lr_s_eq {α β δ τk : ℝ} (hτ : τk < 1) (hr : 0 < lrRent β δ τk) :
    lrS α β δ τk = α / lrRent β δ τk := by
  have h1 : (1 - τk) ≠ 0 := by linarith
  have h2 : lrRho β + δ * (1 - τk) ≠ 0 := by
    have : lrRent β δ τk = (lrRho β + δ * (1 - τk)) / (1 - τk) := by
      unfold lrRent
      field_simp
      ring
    intro h
    rw [this, h, zero_div] at hr
    exact lt_irrefl 0 hr
  unfold lrS lrRent
  field_simp
  ring

/-- **(15.11)** (AKMM, p. 448): with Cobb–Douglas `r = α(k/ℓ)^{α−1}` and (15.8), the
steady-state capital–labour ratio is `k/ℓ = (α(1 − τ_k)/(ρ + δ(1 − τ_k)))^{1/(1−α)}`
(for `0 < α < 1`, `0 < β`, `τ_k < 1`, `k/ℓ > 0`). -/
theorem eq_15_11 {α β δ τk x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hτ : τk < 1)
    (hx : 0 < x) (h158 : 1 = β * (1 + (1 - τk) * (α * x ^ (α - 1) - δ))) :
    x = lrRatio α β δ τk := by
  have hr := (lr_rent_iff hβ hτ).mp h158
  have hrpos : 0 < lrRent β δ τk := by rw [← hr]; positivity
  unfold lrRatio
  rw [lr_s_eq hτ hrpos, ← hr]
  have : α / (α * x ^ (α - 1)) = x ^ (1 - α) := by
    rw [div_mul_eq_div_div, div_self hα0.ne', one_div, ← Real.rpow_neg hx.le, neg_sub]
  rw [this, ← Real.rpow_mul hx.le, mul_one_div_cancel (by linarith), Real.rpow_one]

/-- AKMM, p. 448: `s(τ_k)` is strictly decreasing in `τ_k < 1` (for `ρ > 0`, `δ ≥ 0`, `α > 0`). -/
theorem lr_s_strictAntiOn {α β δ : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) :
    StrictAntiOn (lrS α β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have ha' : 0 < 1 - a := by have := Set.mem_Iio.mp ha; linarith
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  unfold lrS
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hα hρ]

/-- AKMM, p. 448: "a higher `τ_k` depresses the steady-state capital-labor ratio". -/
theorem lr_ratio_strictAntiOn {α β δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : StrictAntiOn (lrRatio α β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hsb : 0 < lrS α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    unfold lrS
    positivity
  unfold lrRatio
  exact Real.rpow_lt_rpow hsb.le (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ ha hb hab)
    (by have : 0 < 1 - α := by linarith
        positivity)

/-- AKMM, p. 448: a higher `τ_k` "will depress the steady-state wage `w`". -/
theorem lr_wage_strictAntiOn {α β δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : StrictAntiOn (lrWage α β δ) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hxb : 0 < lrRatio α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    unfold lrRatio lrS
    positivity
  unfold lrWage
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow hxb.le (lr_ratio_strictAntiOn hα0 hα1 hβ0 hβ1 hδ ha hb hab) hα0)
    (by linarith)

/-- GHH utility `u(c, ℓ) = log(c − ℓ^{1+1/φ}/(1 + 1/φ))` (AKMM, p. 448). -/
noncomputable def ghhU (φ c l : ℝ) : ℝ := Real.log (c - l ^ (1 + 1 / φ) / (1 + 1 / φ))

/-- The GHH disutility of hours `v(ℓ) = ℓ^{1+1/φ}/(1 + 1/φ)`. -/
noncomputable def ghhV (φ l : ℝ) : ℝ := l ^ (1 + 1 / φ) / (1 + 1 / φ)

/-- AKMM, p. 448: for `φ > 0`, `ℓ > 0` and `c > v(ℓ)`, GHH utility is differentiable with
`u₁ = 1/(c − v(ℓ))` and `u₂ = −ℓ^{1/φ}/(c − v(ℓ))`. -/
theorem ghh_partials {φ c l : ℝ} (hφ : 0 < φ) (hl : 0 < l) (hc : ghhV φ l < c) :
    DTPartials (ghhU φ) c l (1 / (c - ghhV φ l)) (-(l ^ (1 / φ)) / (c - ghhV φ l)) := by
  have hpos : 0 < c - ghhV φ l := by linarith
  have ha : 0 < 1 + 1 / φ := by positivity
  have hψ : HasDerivAt (fun l => l ^ (1 + 1 / φ) / (1 + 1 / φ))
      ((1 + 1 / φ) * l ^ (1 + 1 / φ - 1) / (1 + 1 / φ)) l :=
    (Real.hasDerivAt_rpow_const (p := 1 + 1 / φ) (Or.inl hl.ne')).div_const _
  have h2 := hψ.comp_hasFDerivAt (c, l) (hasFDerivAt_snd (𝕜 := ℝ) (p := (c, l)))
  have h3 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (c, l))).sub h2
  have hlog : HasDerivAt Real.log (c - ghhV φ l)⁻¹ (c - ghhV φ l) :=
    Real.hasDerivAt_log hpos.ne'
  have h4 := hlog.comp_hasFDerivAt (c, l) h3
  unfold DTPartials
  refine (h4.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q => rfl)
  ext
  · simp [ghhV]
  · simp
    field_simp

/-- **(15.12)** (AKMM, p. 448): with GHH utility, the labour condition (15.9) at `ℓ > 0`,
`c > v(ℓ)`, `(1 − τ_ℓ)/(1 + τ_c) > 0`, `w > 0` gives `ℓ = ((1 − τ_ℓ)/(1 + τ_c))^φw^φ`; consumption
does not enter. -/
theorem eq_15_12 {φ c l τl τc w : ℝ} (hφ : 0 < φ) (hl : 0 < l) (hc : ghhV φ l < c)
    (hθ : 0 < (1 - τl) / (1 + τc)) (hw : 0 < w)
    (h159 : -(-(l ^ (1 / φ)) / (c - ghhV φ l)) = (1 - τl) / (1 + τc) * w * (1 / (c - ghhV φ l))) :
    l = ((1 - τl) / (1 + τc)) ^ φ * w ^ φ := by
  have hpos : 0 < c - ghhV φ l := by linarith
  have h1 : l ^ (1 / φ) = (1 - τl) / (1 + τc) * w := by
    field_simp at h159
    rw [h159]
    ring
  rw [← Real.mul_rpow hθ.le hw.le, ← h1, ← Real.rpow_mul hl.le, one_div_mul_cancel hφ.ne',
    Real.rpow_one]

/-- GHH steady-state hours (15.12) as a function of the taxes and the wage. -/
noncomputable def ghhHours (φ τl τc w : ℝ) : ℝ := ((1 - τl) / (1 + τc)) ^ φ * w ^ φ

/-- AKMM, p. 448: "Higher labor income … taxes depress hours worked" (for `τ_c > −1`, `w > 0`,
`φ > 0`, on `τ_ℓ < 1`). -/
theorem lr_hours_strictAntiOn_labour {φ τc w : ℝ} (hφ : 0 < φ) (hτc : 0 < 1 + τc) (hw : 0 < w) :
    StrictAntiOn (fun τl => ghhHours φ τl τc w) (Set.Iio 1) := by
  intro a _ b hb hab
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  simp only [ghhHours]
  refine mul_lt_mul_of_pos_right ?_ (Real.rpow_pos_of_pos hw φ)
  exact Real.rpow_lt_rpow (by positivity) (div_lt_div_of_pos_right (by linarith) hτc) hφ

/-- AKMM, p. 448: "Higher … consumption taxes depress hours worked" (for `τ_ℓ < 1`, `w > 0`,
on `τ_c > −1`). -/
theorem lr_hours_strictAntiOn_cons {φ τl w : ℝ} (hφ : 0 < φ) (hτl : τl < 1) (hw : 0 < w) :
    StrictAntiOn (fun τc => ghhHours φ τl τc w) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  have ha' : 0 < 1 + a := by have := Set.mem_Ioi.mp ha; linarith
  have hb' : 0 < 1 + b := by have := Set.mem_Ioi.mp hb; linarith
  simp only [ghhHours]
  refine mul_lt_mul_of_pos_right ?_ (Real.rpow_pos_of_pos hw φ)
  have hl : 0 < 1 - τl := by linarith
  exact Real.rpow_lt_rpow (by positivity) (div_lt_div_of_pos_left hl ha' (by linarith)) hφ

/-- AKMM, p. 448: "Higher capital income taxes also depress hours, via their negative impact on
`w`": steady-state GHH hours at the wage (15.10) are strictly decreasing in `τ_k < 1`. -/
theorem lr_hours_strictAntiOn_capital {α β δ φ τl τc : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hθ : 0 < (1 - τl) / (1 + τc)) :
    StrictAntiOn (fun τk => ghhHours φ τl τc (lrWage α β δ τk)) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hwb : 0 < lrWage α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    have : 0 < 1 - α := by linarith
    unfold lrWage lrRatio lrS
    positivity
  simp only [ghhHours]
  refine mul_lt_mul_of_pos_left ?_ (Real.rpow_pos_of_pos hθ φ)
  exact Real.rpow_lt_rpow hwb.le (lr_wage_strictAntiOn hα0 hα1 hβ0 hβ1 hδ ha hb hab) hφ

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Tax incidence

AKMM, §15.3.2, (15.13), p. 449, footnote 2.

Steady states of the GHH economy with Cobb–Douglas technology. Write `s = (k/ℓ)^{1−α}` for the
base of (15.11) (`lrS`), `θ = (1 − τ_ℓ)/(1 + τ_c)` and `ρ = (1 − β)/β`.

* **Worker–capitalist equivalence** (p. 449, footnote 2): the representative-agent steady state
  and the worker–capitalist steady state impose the same conditions on `(k, ℓ, r, w)`, and any
  aggregate consumption of the one is split between workers and capitalists in the other
  (`inc_wk_iff_ra`).
* Hours in terms of the capital–labour ratio, `ℓ = (θ(1 − α)(k/ℓ)^α)^φ` (`inc_hours_ratio`), and
  **(15.13)** `y = (θ(1 − α))^φ s^{α(1+φ)/(1−α)}` (`eq_15_13`, `incOutput`). Output is strictly
  decreasing in `τ_ℓ`, `τ_c` and `τ_k` (`inc_output_strictAntiOn_labour`,
  `inc_output_strictAntiOn_cons`, `inc_output_strictAntiOn_capital`).
* Consumption of workers `c_w = θ(1 − α)y` and capitalists `c_k = ρ/(1 + τ_c)·α(1 − τ_k)/(ρ +
  (1 − τ_k)δ)·y` (`inc_cw`, `inc_ck`).
* `k = sy` (`inc_ratio_eq`).

The budget locus (15.14), the flow-utility identity and the excess cost of taxation are in
`ExcessCost`.

Departures: none.
-/

namespace AKMM.FiscalPolicy

open Real

/-! ### Worker–capitalist equivalence (footnote 2) -/

/-- The steady-state conditions common to both decentralisations of the GHH economy, with
Cobb–Douglas technology (AKMM, pp. 448–449): `r = α(k/ℓ)^{α−1}`, `w = (1 − α)(k/ℓ)^α`, (15.8),
and the GHH hours condition `ℓ^{1/φ} = θw`. -/
def incSSCore (α β δ φ τl τc τk k l r w : ℝ) : Prop :=
  r = α * (k / l) ^ (α - 1) ∧ w = (1 - α) * (k / l) ^ α ∧
    1 = β * (1 + (1 - τk) * (r - δ)) ∧ l ^ (1 / φ) = (1 - τl) / (1 + τc) * w

/-- The representative-agent steady state: the core conditions and the steady-state budget
`(1 + τ_c)C = (1 − τ_ℓ)wℓ + (1 − τ_k)(r − δ)k + T`. -/
def incRASteady (α β δ φ τl τc τk T k l r w C : ℝ) : Prop :=
  incSSCore α β δ φ τl τc τk k l r w ∧
    (1 + τc) * C = (1 - τl) * w * l + (1 - τk) * (r - δ) * k + T

/-- The worker–capitalist steady state: the core conditions (the capitalists' Euler equation is
(15.8), the workers' hours condition is GHH) and the two budgets
`(1 + τ_c)c_w = (1 − τ_ℓ)wℓ + T_w`, `(1 + τ_c)c_k = (1 − τ_k)(r − δ)k + T_k`. -/
def incWKSteady (α β δ φ τl τc τk Tw Tk k l r w cw ck : ℝ) : Prop :=
  incSSCore α β δ φ τl τc τk k l r w ∧ (1 + τc) * cw = (1 - τl) * w * l + Tw ∧
    (1 + τc) * ck = (1 - τk) * (r - δ) * k + Tk

/-- AKMM, p. 449 and footnote 2: "the steady state of the representative agent model … is
identical, at the aggregate level, to … workers … and capitalists": `(k, ℓ, r, w, C)` is a
representative-agent steady state iff it is a worker–capitalist steady state for some split
`C = c_w + c_k` of consumption and `T = T_w + T_k` of transfers. Consumption appears in neither
condition of `incSSCore`. -/
theorem inc_wk_iff_ra {α β δ φ τl τc τk T k l r w C : ℝ} (hτc : 1 + τc ≠ 0) :
    incRASteady α β δ φ τl τc τk T k l r w C ↔
      ∃ cw ck Tw Tk, cw + ck = C ∧ Tw + Tk = T ∧
        incWKSteady α β δ φ τl τc τk Tw Tk k l r w cw ck := by
  constructor
  · rintro ⟨hcore, hb⟩
    refine ⟨((1 - τl) * w * l + T) / (1 + τc), (1 - τk) * (r - δ) * k / (1 + τc), T, 0,
      ?_, by ring, hcore, by field_simp, by field_simp; ring⟩
    field_simp
    linarith
  · rintro ⟨cw, ck, Tw, Tk, hC, hT, hcore, hw, hk⟩
    refine ⟨hcore, ?_⟩
    rw [← hC, ← hT]
    linear_combination hw + hk

/-! ### Output and consumption, (15.13) -/

/-- Steady-state output (15.13) as a function of `θ(1 − α)` (`m`) and `s = (k/ℓ)^{1−α}`:
`y = m^φ s^{α(1+φ)/(1−α)}`. -/
noncomputable def incOutput (α φ m s : ℝ) : ℝ := m ^ φ * s ^ (α * (1 + φ) / (1 - α))

/-- AKMM, p. 449: from (15.10) and (15.12), `ℓ = (θ(1 − α)(k/ℓ)^α)^φ`. -/
theorem inc_hours_ratio {α φ θ x l : ℝ} (hα : α < 1) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hl : l = θ ^ φ * ((1 - α) * x ^ α) ^ φ) : l = (θ * (1 - α) * x ^ α) ^ φ := by
  have h1 : 0 ≤ (1 - α) * x ^ α := mul_nonneg (by linarith) (Real.rpow_nonneg hx α)
  rw [hl, ← Real.mul_rpow hθ h1, mul_assoc]

/-- **(15.13)** (AKMM, p. 449): with `k/ℓ = s^{1/(1−α)}` (15.11) and hours (15.12) at the
wage (15.10), steady-state output is `y = (k/ℓ)^αℓ = (θ(1 − α))^φ s^{α(1+φ)/(1−α)}`
(`α < 1`, `θ ≥ 0`, `s > 0`). -/
theorem eq_15_13 {α φ θ s l : ℝ} (hα1 : α < 1) (hθ : 0 ≤ θ) (hs : 0 < s)
    (hl : l = θ ^ φ * ((1 - α) * (s ^ (1 / (1 - α))) ^ α) ^ φ) :
    (s ^ (1 / (1 - α))) ^ α * l = incOutput α φ (θ * (1 - α)) s := by
  have h1α : 0 < 1 - α := by linarith
  have hxa : (s ^ (1 / (1 - α))) ^ α = s ^ (α / (1 - α)) := by
    rw [← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [hl, hxa, ← Real.mul_rpow hθ (mul_nonneg h1α.le (Real.rpow_nonneg hs.le _))]
  unfold incOutput
  rw [← mul_assoc, Real.mul_rpow (mul_nonneg hθ h1α.le) (Real.rpow_nonneg hs.le _),
    ← Real.rpow_mul hs.le]
  have : α * (1 + φ) / (1 - α) = α / (1 - α) + α / (1 - α) * φ := by ring
  rw [this, Real.rpow_add hs]
  ring

/-- AKMM, p. 449: output (15.13) is strictly increasing in `m = θ(1 − α) > 0` and in `s > 0`. -/
theorem inc_output_lt {α φ m m' s s' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hφ : 0 < φ)
    (hm : 0 < m) (hmm : m ≤ m') (hs : 0 < s) (hss : s ≤ s') (hne : m < m' ∨ s < s') :
    incOutput α φ m s < incOutput α φ m' s' := by
  have he : 0 < α * (1 + φ) / (1 - α) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hm' : 0 < m' := by linarith
  unfold incOutput
  rcases hne with h | h
  · calc m ^ φ * s ^ (α * (1 + φ) / (1 - α)) < m' ^ φ * s ^ (α * (1 + φ) / (1 - α)) :=
          mul_lt_mul_of_pos_right (Real.rpow_lt_rpow hm.le h hφ) (Real.rpow_pos_of_pos hs _)
      _ ≤ m' ^ φ * s' ^ (α * (1 + φ) / (1 - α)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hss he.le)
            (Real.rpow_nonneg hm'.le _)
  · calc m ^ φ * s ^ (α * (1 + φ) / (1 - α)) < m ^ φ * s' ^ (α * (1 + φ) / (1 - α)) :=
          mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hs.le h he) (Real.rpow_pos_of_pos hm _)
      _ ≤ m' ^ φ * s' ^ (α * (1 + φ) / (1 - α)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le hmm hφ.le)
            (Real.rpow_nonneg (by linarith) _)

/-- AKMM, p. 449: "the level of output is decreasing in each tax rate": in the labour tax
(`τ_c > −1`, on `τ_ℓ < 1`, for `s > 0`). -/
theorem inc_output_strictAntiOn_labour {α φ τc s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hφ : 0 < φ)
    (hτc : 0 < 1 + τc) (hs : 0 < s) :
    StrictAntiOn (fun τl => incOutput α φ ((1 - τl) / (1 + τc) * (1 - α)) s) (Set.Iio 1) := by
  intro a _ b hb hab
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  have h1α : 0 < 1 - α := by linarith
  refine inc_output_lt hα0 hα1 hφ (by positivity) ?_ hs le_rfl (Or.inl ?_)
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hτc.le) h1α.le
  · exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (by linarith) hτc) h1α

/-- AKMM, p. 449: output is decreasing in the consumption tax (`τ_ℓ < 1`, on `τ_c > −1`). -/
theorem inc_output_strictAntiOn_cons {α φ τl s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hφ : 0 < φ)
    (hτl : τl < 1) (hs : 0 < s) :
    StrictAntiOn (fun τc => incOutput α φ ((1 - τl) / (1 + τc) * (1 - α)) s) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  have ha' : 0 < 1 + a := by have := Set.mem_Ioi.mp ha; linarith
  have hb' : 0 < 1 + b := by have := Set.mem_Ioi.mp hb; linarith
  have h1α : 0 < 1 - α := by linarith
  have hl : 0 < 1 - τl := by linarith
  refine inc_output_lt hα0 hα1 hφ (by positivity) ?_ hs le_rfl (Or.inl ?_)
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hl.le ha' (by linarith)) h1α.le
  · exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_left hl ha' (by linarith)) h1α

/-- AKMM, p. 449: output is decreasing in the capital tax (through `s`, for `0 < β < 1`,
`δ ≥ 0`, `θ > 0`, on `τ_k < 1`). -/
theorem inc_output_strictAntiOn_capital {α β δ φ θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hθ : 0 < θ) :
    StrictAntiOn (fun τk => incOutput α φ (θ * (1 - α)) (lrS α β δ τk)) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hsb : 0 < lrS α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    unfold lrS
    positivity
  have h1α : 0 < 1 - α := by linarith
  have hlt := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ ha hb hab
  exact inc_output_lt hα0 hα1 hφ (by positivity) le_rfl hsb hlt.le (Or.inr hlt)

/-- AKMM, p. 449: workers consume `c_w = θwℓ = θ(1 − α)y`, using `wℓ = (1 − α)(k/ℓ)^αℓ`. -/
theorem inc_cw {α θ x l : ℝ} :
    θ * ((1 - α) * x ^ α) * l = θ * (1 - α) * (x ^ α * l) := by
  ring

/-- `s^{1/(1−α)} = s·(s^{1/(1−α)})^α`, i.e. `k/ℓ = s(k/ℓ)^α`, so `k = sy`. -/
theorem inc_ratio_eq {α s : ℝ} (hα1 : α < 1) (hs : 0 < s) :
    s ^ (1 / (1 - α)) = s * (s ^ (1 / (1 - α))) ^ α := by
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [← Real.rpow_mul hs.le]
  conv_lhs => rw [show 1 / (1 - α) = 1 + 1 / (1 - α) * α by field_simp; ring]
  rw [Real.rpow_add hs, Real.rpow_one]

/-- AKMM, p. 449: capitalists consume `c_k = (1 − τ_k)(r − δ)k/(1 + τ_c)
= (ρ/(1 + τ_c))·α(1 − τ_k)/(ρ + (1 − τ_k)δ)·y`, with `r` from (15.8), `k = (k/ℓ)ℓ`,
`k/ℓ = s^{1/(1−α)}` (15.11) and `y = (k/ℓ)^αℓ`. -/
theorem inc_ck {α β δ τk τc l : ℝ} (hα1 : α < 1) (hτk : τk < 1) (hs : 0 < lrS α β δ τk) :
    (1 - τk) * (lrRent β δ τk - δ) * (lrS α β δ τk ^ (1 / (1 - α)) * l) / (1 + τc) =
      lrRho β / (1 + τc) * (α * (1 - τk) / (lrRho β + (1 - τk) * δ)) *
        ((lrS α β δ τk ^ (1 / (1 - α))) ^ α * l) := by
  have h1τ : (1 - τk) ≠ 0 := by linarith
  have hr : (1 - τk) * (lrRent β δ τk - δ) = lrRho β := by
    unfold lrRent
    field_simp
    ring
  have hS : α * (1 - τk) / (lrRho β + (1 - τk) * δ) = lrS α β δ τk := by
    unfold lrS
    rw [mul_comm δ]
  rw [hr, hS]
  nth_rewrite 1 [inc_ratio_eq hα1 hs]
  ring

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Figure 15.6: the labour tax and the two types' consumption along (15.14)

AKMM, §15.3.2, Figure 15.6, Panels A–C, p. 450.

No consumption tax, no transfers, `G = gy`, and the labour tax adjusts by (15.14). Write
`ρ = (1 − β)/β`, `c = ρ + δ`, `s = α(1 − τ_k)/(ρ + δ(1 − τ_k))` (`lrS`), `s₀ = α/c` its value at
`τ_k = 0`, `m = (1 − τ_ℓ)(1 − α) = 1 − g − cs` (`inc_m_eq`) and `e = α(1 + φ)/(1 − α)`, so that
`y = m^φs^e` (15.13), `c_w = my = m^{1+φ}s^e` (`fig156Cw`) and `c_k = ρsy = ρm^φs^{1+e}`
(`fig156Ck`). All results hold for every `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` (and the
stated ranges of `g`), not only at the figure's calibration.

* **Panel A.** `τ_ℓ` is strictly decreasing in `τ_k` on `τ_k < 1` (`fig156_tauL_strictAntiOn`),
  concave (`fig156_tauL_concaveOn`), strictly concave when `δ > 0`
  (`fig156_tauL_strictConcaveOn`); it equals `g/(1 − α)` at `τ_k = 0` and `(g − α)/(1 − α)` at
  `τ_k = 1` (`fig156_tauL_endpoints`), and for `0 < g < α` it changes sign exactly at
  `τ_k = g(ρ + δ)/(ρα + gδ) ∈ (0, 1)` (`fig156_tauL_neg_iff`).
* **The one-variable lemma.** `h(s) = (K − cs)^a s^b` (`fig156Hump`) is strictly increasing on
  `(0, s̄]` and strictly decreasing on `[s̄, K/c)`, `s̄ = bK/((a + b)c)`
  (`fig156_hump_strictMonoOn`, `fig156_hump_strictAntiOn`); `s(τ_k) = Ks₀` exactly at
  `τ_k = (1 − K)(ρ + δ)/(ρ + δ(1 − K))` (`fig156_s_eq`).
* **Panel B: `c_w` is hump-shaped.** For `0 < g < 1 − α` (`τ_ℓ(0) < 1`), `c_w` is strictly
  increasing on `[0, τ_w]` and strictly decreasing on `[τ_w, 1)`, with
  `τ_w = g(ρ + δ)/(ρ + δg) ∈ (0, 1)` (`fig156_cw_hump`); the peak is a strict global maximum on
  `[0, 1)` (`fig156_cw_isMaxOn`) and is where `τ_ℓ = g`, i.e. labour and capital income are taxed
  at the same average rate `g` (`fig156_cw_peak_tauL`).
* **Panel C: `c_k` is maximal at `τ_k = 0` iff `g ≤ (1 − α)/(1 + αφ)`.** Under this condition
  `c_k` is strictly decreasing on `[0, 1)` (`fig156_ck_strictAntiOn`). For
  `(1 − α)/(1 + αφ) < g < 1 − α` it is hump-shaped instead, rising on `[0, τ_c]` and falling on
  `[τ_c, 1)`, `τ_c = (1 − K)(ρ + δ)/(ρ + δ(1 − K)) ∈ (0, 1)`, `K = (1 + αφ)(1 − g)/((1 + φ)α)`
  (`fig156_ck_hump`), so `c_k(τ_c) > c_k(0)`. Hence the exact statement
  (`fig156_ck_max_at_zero_iff`). The book's claim holds at its parameters (`g = .2` is below
  `.67/1.33`), but not in general: at the parameters of the counterexample to the minimality of
  the excess cost (`inc_excess_cost_not_min_at_zero`: `α = 1/2`, `β = 2/3`, `δ = 1/10`, `φ = 1`,
  `g = 2/5 > 1/3`), `c_k(1/5) > c_k(0)` (`fig156_ck_not_max_at_zero`).

Departures: the book states the claims at its calibration; the hump of `c_w` needs `g > 0` and
`τ_ℓ(0) < 1`, and the maximality of `c_k` at `τ_k = 0` needs `g ≤ (1 − α)/(1 + αφ)` (correction
8 in `docs/corrections.md`).
-/

namespace AKMM.FiscalPolicy

open Real Set

/-! ### Panel A: the labour tax along (15.14) -/

/-- AKMM, p. 450, Figure 15.6, Panel A: along (15.14), `τ_ℓ = (g − α + (ρ + δ)s)/(1 − α)`. -/
theorem fig156_tauL_eq {α β δ g τk : ℝ} (hα : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hτk : τk < 1) :
    incTauL α β δ g τk = (g - α + (lrRho β + δ) * lrS α β δ τk) / (1 - α) := by
  have h := inc_m_eq (g := g) hα hβ0 hβ1 hδ hτk
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold incM at h
  rw [eq_div_iff h1]
  linear_combination (-1 : ℝ) * h

/-- AKMM, p. 450, Figure 15.6, Panel A: the budget-balancing labour tax is strictly decreasing
in the capital tax on `τ_k < 1`. -/
theorem fig156_tauL_strictAntiOn {α β δ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : StrictAntiOn (incTauL α β δ g) (Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ ha hb hab
  rw [fig156_tauL_eq hα1 hβ0 hβ1 hδ ha, fig156_tauL_eq hα1 hβ0 hβ1 hδ hb]
  have h1 : 0 < 1 - α := by linarith
  apply div_lt_div_of_pos_right _ h1
  nlinarith

/-- The convexity gap of `τ ↦ τ/(ρ + δ − δτ)`: for `E(τ) = ρ + δ − δτ`,
`a f(x) + b f(y) − f(ax + by) = (ρ + δ)abδ(x − y)²/(E(x)E(y)E(ax + by))` when `a + b = 1`. -/
theorem fig156_gap {ρ δ a b x y : ℝ} (hab : a + b = 1) (hx : ρ + δ - δ * x ≠ 0)
    (hy : ρ + δ - δ * y ≠ 0) (hz : ρ + δ - δ * (a * x + b * y) ≠ 0) :
    a * (x / (ρ + δ - δ * x)) + b * (y / (ρ + δ - δ * y)) -
        (a * x + b * y) / (ρ + δ - δ * (a * x + b * y)) =
      (ρ + δ) * a * b * δ * (x - y) ^ 2 /
        ((ρ + δ - δ * x) * (ρ + δ - δ * y) * (ρ + δ - δ * (a * x + b * y))) := by
  obtain rfl : b = 1 - a := by linarith
  rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ hx hy, div_sub_div _ _ (mul_ne_zero hx hy) hz,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hx hy) hz) (mul_ne_zero (mul_ne_zero hx hy) hz)]
  ring

/-- `τ_ℓ` in terms of `f(τ) = τ/(ρ + δ − δτ)`: `τ_ℓ = (g − ραf(τ))/(1 − α)`. -/
theorem fig156_tauL_f {α β δ g τk : ℝ} :
    incTauL α β δ g τk =
      (g - lrRho β * α * (τk / (lrRho β + δ - δ * τk))) / (1 - α) := by
  unfold incTauL incBud
  congr 1
  rw [show lrRho β + (1 - τk) * δ = lrRho β + δ - δ * τk by ring]
  ring

/-- AKMM, p. 450, Figure 15.6, Panel A: `τ_ℓ` is concave in `τ_k` on `τ_k < 1` (for `δ ≥ 0`;
it is affine when `δ = 0`). -/
theorem fig156_tauL_concaveOn {α β δ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) : ConcaveOn ℝ (Iio 1) (incTauL α β δ g) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  refine ⟨convex_Iio 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : x < 1 := hx
  have hy' : y < 1 := hy
  have hz' : a * x + b * y < 1 := by
    have := (convex_Iio (1 : ℝ)) hx hy ha hb hab
    simpa [smul_eq_mul] using this
  have hE : ∀ t : ℝ, t < 1 → 0 < lrRho β + δ - δ * t := fun t ht => by nlinarith
  have hEx := hE x hx'
  have hEy := hE y hy'
  have hEz := hE _ hz'
  have hgap := fig156_gap (ρ := lrRho β) (δ := δ) hab hEx.ne' hEy.ne' hEz.ne'
  have hnn : 0 ≤ (lrRho β + δ) * a * b * δ * (x - y) ^ 2 /
      ((lrRho β + δ - δ * x) * (lrRho β + δ - δ * y) * (lrRho β + δ - δ * (a * x + b * y))) := by
    have : 0 ≤ lrRho β + δ := by linarith
    positivity
  simp only [smul_eq_mul]
  rw [fig156_tauL_f, fig156_tauL_f, fig156_tauL_f]
  have h1 : 0 < 1 - α := by linarith
  rw [← sub_nonneg]
  have e : (g - lrRho β * α * ((a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y)))) / (1 - α) -
      (a * ((g - lrRho β * α * (x / (lrRho β + δ - δ * x))) / (1 - α)) +
        b * ((g - lrRho β * α * (y / (lrRho β + δ - δ * y))) / (1 - α))) =
      lrRho β * α / (1 - α) * (a * (x / (lrRho β + δ - δ * x)) + b * (y / (lrRho β + δ - δ * y))
        - (a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y))) := by
    obtain rfl : b = 1 - a := by linarith
    field_simp
    ring
  rw [e, hgap]
  positivity

/-- AKMM, p. 450, Figure 15.6, Panel A: for `δ > 0`, `τ_ℓ` is strictly concave in `τ_k` on
`τ_k < 1`, as the panel shows. -/
theorem fig156_tauL_strictConcaveOn {α β δ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 < δ) : StrictConcaveOn ℝ (Iio 1) (incTauL α β δ g) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  refine ⟨convex_Iio 1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hx' : x < 1 := hx
  have hy' : y < 1 := hy
  have hz' : a * x + b * y < 1 := by
    have := (convex_Iio (1 : ℝ)) hx hy ha.le hb.le hab
    simpa [smul_eq_mul] using this
  have hE : ∀ t : ℝ, t < 1 → 0 < lrRho β + δ - δ * t := fun t ht => by nlinarith
  have hEx := hE x hx'
  have hEy := hE y hy'
  have hEz := hE _ hz'
  have hgap := fig156_gap (ρ := lrRho β) (δ := δ) hab hEx.ne' hEy.ne' hEz.ne'
  have hxy2 : 0 < (x - y) ^ 2 := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  have hpos : 0 < (lrRho β + δ) * a * b * δ * (x - y) ^ 2 /
      ((lrRho β + δ - δ * x) * (lrRho β + δ - δ * y) * (lrRho β + δ - δ * (a * x + b * y))) := by
    have : 0 < lrRho β + δ := by linarith
    positivity
  simp only [smul_eq_mul]
  rw [fig156_tauL_f, fig156_tauL_f, fig156_tauL_f]
  have h1 : 0 < 1 - α := by linarith
  rw [← sub_pos]
  have e : (g - lrRho β * α * ((a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y)))) / (1 - α) -
      (a * ((g - lrRho β * α * (x / (lrRho β + δ - δ * x))) / (1 - α)) +
        b * ((g - lrRho β * α * (y / (lrRho β + δ - δ * y))) / (1 - α))) =
      lrRho β * α / (1 - α) * (a * (x / (lrRho β + δ - δ * x)) + b * (y / (lrRho β + δ - δ * y))
        - (a * x + b * y) / (lrRho β + δ - δ * (a * x + b * y))) := by
    obtain rfl : b = 1 - a := by linarith
    field_simp
    ring
  rw [e, hgap]
  positivity

/-- AKMM, p. 450, Figure 15.6, Panel A: the endpoints, `τ_ℓ = g/(1 − α)` at `τ_k = 0` and
`τ_ℓ = (g − α)/(1 − α)` at `τ_k = 1` (negative iff `g < α`, as in the panel). -/
theorem fig156_tauL_endpoints {α β δ g : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    incTauL α β δ g 0 = g / (1 - α) ∧ incTauL α β δ g 1 = (g - α) / (1 - α) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  unfold incTauL incBud
  constructor
  · simp
  · congr 1
    rw [show lrRho β + (1 - 1) * δ = lrRho β by ring]
    field_simp

/-- AKMM, p. 450, Figure 15.6, Panel A: for `0 < g < α`, the labour tax turns into a subsidy
exactly beyond `τ̂ = g(ρ + δ)/(ρα + gδ) ∈ (0, 1)`: on `τ_k < 1`, `τ_ℓ < 0 ↔ τ_k > τ̂` and
`τ_ℓ = 0 ↔ τ_k = τ̂`. -/
theorem fig156_tauL_neg_iff {α β δ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hg0 : 0 < g) (hgα : g < α) (hτk : τk < 1) :
    0 < g * (lrRho β + δ) / (lrRho β * α + g * δ) ∧
      g * (lrRho β + δ) / (lrRho β * α + g * δ) < 1 ∧
      (incTauL α β δ g τk < 0 ↔ g * (lrRho β + δ) / (lrRho β * α + g * δ) < τk) ∧
      (incTauL α β δ g τk = 0 ↔ τk = g * (lrRho β + δ) / (lrRho β * α + g * δ)) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hD : 0 < lrRho β * α + g * δ := by positivity
  have hE : 0 < lrRho β + δ - δ * τk := by nlinarith
  have h1 : 0 < 1 - α := by linarith
  rw [fig156_tauL_f]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_one hD]
    nlinarith
  · rw [div_neg_iff, div_lt_iff₀ hD]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · rw [sub_neg, mul_div_assoc', lt_div_iff₀ hE] at h
        nlinarith
    · intro h
      refine Or.inr ⟨?_, h1⟩
      rw [sub_neg, mul_div_assoc', lt_div_iff₀ hE]
      nlinarith
  · rw [div_eq_zero_iff, sub_eq_zero, mul_div_assoc', eq_div_iff hE.ne']
    constructor
    · rintro (h | h)
      · rw [eq_div_iff hD.ne']
        linarith
      · linarith
    · intro h
      left
      rw [eq_div_iff hD.ne'] at h
      linarith

/-! ### The one-variable hump -/

/-- `h(s) = (K − cs)^a s^b`, the common form of `c_w` and `c_k` as functions of `s`. -/
noncomputable def fig156Hump (K c a b s : ℝ) : ℝ := (K - c * s) ^ a * s ^ b

/-- The derivative of `h(s) = (K − cs)^a s^b` at `s > 0` with `K − cs > 0`:
`h(s)(b/s − ac/(K − cs))`. -/
theorem fig156_hump_hasDerivAt {K c a b s : ℝ} (hs : 0 < s) (hm : 0 < K - c * s) :
    HasDerivAt (fig156Hump K c a b)
      ((K - c * s) ^ a * s ^ b * (b / s - a * c / (K - c * s))) s := by
  have h1 : HasDerivAt (fun x => K - c * x) (-c) s := by
    simpa using ((hasDerivAt_id s).const_mul c).const_sub K
  have h2 := (h1.rpow_const (p := a) (Or.inl hm.ne')).mul
    (Real.hasDerivAt_rpow_const (p := b) (Or.inl hs.ne'))
  refine h2.congr_deriv ?_
  rw [Real.rpow_sub_one hm.ne', Real.rpow_sub_one hs.ne']
  field_simp
  ring

/-- `h(s) = (K − cs)^a s^b` (`a, b, c > 0`) is strictly increasing on `(0, bK/((a + b)c)]`. -/
theorem fig156_hump_strictMonoOn {K c a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hK : 0 < K) : StrictMonoOn (fig156Hump K c a b) (Ioc 0 (b * K / ((a + b) * c))) := by
  have hab : 0 < (a + b) * c := by positivity
  have hm : ∀ x ∈ Ioc 0 (b * K / ((a + b) * c)), 0 < K - c * x := by
    intro x hx
    have h := (le_div_iff₀ hab).mp hx.2
    nlinarith [hx.1]
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro x hx
    exact (fig156_hump_hasDerivAt hx.1 (hm x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hmx := hm x (Ioo_subset_Ioc_self hx)
    rw [(fig156_hump_hasDerivAt hx.1 hmx).deriv]
    have hlt := (lt_div_iff₀ hab).mp hx.2
    have hx0 := hx.1
    apply mul_pos (mul_pos (Real.rpow_pos_of_pos hmx _) (Real.rpow_pos_of_pos hx0 _))
    rw [div_sub_div _ _ hx0.ne' hmx.ne']
    apply div_pos _ (mul_pos hx0 hmx)
    nlinarith

/-- `h(s) = (K − cs)^a s^b` (`a, b, c > 0`) is strictly decreasing on `[bK/((a + b)c), K/c)`. -/
theorem fig156_hump_strictAntiOn {K c a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hK : 0 < K) : StrictAntiOn (fig156Hump K c a b) (Ico (b * K / ((a + b) * c)) (K / c)) := by
  have hab : 0 < (a + b) * c := by positivity
  have hpos : ∀ x ∈ Ico (b * K / ((a + b) * c)) (K / c), 0 < x ∧ 0 < K - c * x := by
    intro x hx
    have h0 : 0 < b * K / ((a + b) * c) := by positivity
    refine ⟨by linarith [hx.1], ?_⟩
    have := (lt_div_iff₀ hc).mp hx.2
    linarith
  apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
  · intro x hx
    have h := hpos x hx
    exact (fig156_hump_hasDerivAt h.1 h.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have h := hpos x (Ioo_subset_Ico_self hx)
    rw [(fig156_hump_hasDerivAt h.1 h.2).deriv]
    have hlt := (div_lt_iff₀ hab).mp hx.1
    apply mul_neg_of_pos_of_neg
      (mul_pos (Real.rpow_pos_of_pos h.2 _) (Real.rpow_pos_of_pos h.1 _))
    rw [div_sub_div _ _ h.1.ne' h.2.ne']
    apply div_neg_of_neg_of_pos _ (mul_pos h.1 h.2)
    nlinarith

/-! ### `s` along the capital tax -/

/-- `s(0) = s₀ = α/(ρ + δ)`. -/
theorem fig156_s0 {α β δ : ℝ} : lrS α β δ 0 = α / (lrRho β + δ) := by
  unfold lrS
  simp

/-- `s(τ_k) = Ks₀` at `τ_k = (1 − K)(ρ + δ)/(ρ + δ(1 − K))`, which lies in `(0, 1)` when
`0 < K < 1` (and `(-∞, 1)` for `0 < K`). -/
theorem fig156_s_eq {α β δ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hK0 : 0 < K)
    (hK1 : K < 1) :
    lrS α β δ ((1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K))) = K * lrS α β δ 0 ∧
      0 < (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) ∧
      (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) < 1 := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hD : 0 < lrRho β + δ * (1 - K) := by
    have : 0 ≤ δ * (1 - K) := mul_nonneg hδ (by linarith)
    linarith
  have hc : 0 < lrRho β + δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [fig156_s0]
    unfold lrS
    have e : 1 - (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) =
        lrRho β * K / (lrRho β + δ * (1 - K)) := by
      rw [eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
      ring
    rw [e]
    field_simp
    ring
  · have : 0 < 1 - K := by linarith
    positivity
  · rw [div_lt_one hD]
    nlinarith

/-- `0 < s(τ_k) ≤ s₀` for `0 ≤ τ_k < 1`, strictly below for `τ_k > 0`. -/
theorem fig156_s_bounds {α β δ τk : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hτ0 : 0 ≤ τk) (hτ1 : τk < 1) : 0 < lrS α β δ τk ∧ lrS α β δ τk ≤ lrS α β δ 0 := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  refine ⟨?_, ?_⟩
  · have : 0 < 1 - τk := by linarith
    unfold lrS
    positivity
  · exact (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ).antitoneOn (Set.mem_Iio.mpr one_pos)
      (Set.mem_Iio.mpr hτ1) hτ0

/-- Transfer of a hump in `s` to a hump in `τ_k`: if `h` is strictly increasing on `(0, ŝ]` and
strictly decreasing on `[ŝ, U)`, with `s₀ < U` and `s(τ̂) = ŝ`, `0 ≤ τ̂ < 1`, then `h ∘ s` is
strictly increasing on `[0, τ̂]` and strictly decreasing on `[τ̂, 1)`. -/
theorem fig156_comp_hump {α β δ U τh : ℝ} {h : ℝ → ℝ} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hU : lrS α β δ 0 < U) (hτh0 : 0 ≤ τh) (hτh1 : τh < 1)
    (hinc : StrictMonoOn h (Ioc 0 (lrS α β δ τh)))
    (hdec : StrictAntiOn h (Ico (lrS α β δ τh) U)) :
    StrictMonoOn (fun τ => h (lrS α β δ τ)) (Icc 0 τh) ∧
      StrictAntiOn (fun τ => h (lrS α β δ τ)) (Ico τh 1) := by
  have hanti := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ
  constructor
  · intro x hx y hy hxy
    have hx1 : x < 1 := by linarith [hx.2]
    have hy1 : y < 1 := by linarith [hy.2]
    have hsx := fig156_s_bounds hα0 hβ0 hβ1 hδ hx.1 hx1
    have hsy := fig156_s_bounds hα0 hβ0 hβ1 hδ hy.1 hy1
    have hlt : lrS α β δ y < lrS α β δ x := hanti hx1 hy1 hxy
    have hyh : lrS α β δ τh ≤ lrS α β δ y :=
      hanti.antitoneOn (Set.mem_Iio.mpr hy1) (Set.mem_Iio.mpr hτh1) hy.2
    exact hdec ⟨hyh, by linarith⟩ ⟨by linarith, by linarith⟩ hlt
  · intro x hx y hy hxy
    have hx1 : x < 1 := hx.2
    have hy1 : y < 1 := hy.2
    have hsy := fig156_s_bounds hα0 hβ0 hβ1 hδ (by linarith [hy.1]) hy1
    have hlt : lrS α β δ y < lrS α β δ x := hanti hx1 hy1 hxy
    have hxh : lrS α β δ x ≤ lrS α β δ τh :=
      hanti.antitoneOn (Set.mem_Iio.mpr hτh1) (Set.mem_Iio.mpr hx1) hx.1
    exact hinc ⟨hsy.1, by linarith⟩ ⟨by linarith, hxh⟩ hlt

/-! ### Panel B: workers' consumption -/

/-- Workers' consumption along (15.14), `c_w = my` (AKMM, p. 449, `τ_c = 0`). -/
noncomputable def fig156Cw (α β δ φ g τk : ℝ) : ℝ :=
  incM α β δ g τk * incOutput α φ (incM α β δ g τk) (lrS α β δ τk)

/-- Capitalists' consumption along (15.14), `c_k = ρsy` (AKMM, p. 449, `τ_c = 0`). -/
noncomputable def fig156Ck (α β δ φ g τk : ℝ) : ℝ :=
  lrRho β * lrS α β δ τk * incOutput α φ (incM α β δ g τk) (lrS α β δ τk)

/-- `c_w = h(s)` with `K = 1 − g`, `c = ρ + δ`, `a = 1 + φ`, `b = e`, for `0 ≤ τ_k < 1` and
`g < 1 − α`. -/
theorem fig156_cw_eq {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hg : g < 1 - α) (hτ0 : 0 ≤ τk) (hτ1 : τk < 1) :
    fig156Cw α β δ φ g τk =
      fig156Hump (1 - g) (lrRho β + δ) (1 + φ) (α * (1 + φ) / (1 - α)) (lrS α β δ τk) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs := fig156_s_bounds hα0 hβ0 hβ1 hδ hτ0 hτ1
  have hm := inc_m_eq (g := g) hα1 hβ0 hβ1 hδ hτ1
  have hmpos : 0 < 1 - g - (lrRho β + δ) * lrS α β δ τk := by
    rw [fig156_s0] at hs
    have := (le_div_iff₀ (show 0 < lrRho β + δ by linarith)).mp hs.2
    nlinarith
  unfold fig156Cw fig156Hump incOutput
  rw [hm, ← mul_assoc, Real.rpow_add hmpos, Real.rpow_one]

/-- `c_k = ρh(s)` with `K = 1 − g`, `c = ρ + δ`, `a = φ`, `b = 1 + e`, for `0 ≤ τ_k < 1` and
`g < 1 − α`. -/
theorem fig156_ck_eq {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hτ0 : 0 ≤ τk) (hτ1 : τk < 1) :
    fig156Ck α β δ φ g τk = lrRho β *
      fig156Hump (1 - g) (lrRho β + δ) φ (1 + α * (1 + φ) / (1 - α)) (lrS α β δ τk) := by
  have hs := fig156_s_bounds hα0 hβ0 hβ1 hδ hτ0 hτ1
  have hm := inc_m_eq (g := g) hα1 hβ0 hβ1 hδ hτ1
  unfold fig156Ck fig156Hump incOutput
  rw [hm, Real.rpow_add hs.1, Real.rpow_one]
  ring

/-- **Figure 15.6, Panel B** (AKMM, p. 450: "consumption of workers is a hump-shaped function of
`τ_k`"). For `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` and `0 < g < 1 − α` (`τ_ℓ(0) < 1`),
`τ_w = g(ρ + δ)/(ρ + δg)` lies in `(0, 1)`, and `c_w` is strictly increasing on `[0, τ_w]` and
strictly decreasing on `[τ_w, 1)`. -/
theorem fig156_cw_hump {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg0 : 0 < g) (hg : g < 1 - α) :
    0 < g * (lrRho β + δ) / (lrRho β + δ * g) ∧ g * (lrRho β + δ) / (lrRho β + δ * g) < 1 ∧
      StrictMonoOn (fig156Cw α β δ φ g) (Icc 0 (g * (lrRho β + δ) / (lrRho β + δ * g))) ∧
      StrictAntiOn (fig156Cw α β δ φ g) (Ico (g * (lrRho β + δ) / (lrRho β + δ * g)) 1) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨hsτ, hτ0, hτ1⟩ := fig156_s_eq (α := α) hβ0 hβ1 hδ (K := 1 - g) (by linarith)
    (by linarith)
  have eτ : (1 - (1 - g)) * (lrRho β + δ) / (lrRho β + δ * (1 - (1 - g))) =
      g * (lrRho β + δ) / (lrRho β + δ * g) := by ring_nf
  rw [eτ] at hsτ hτ0 hτ1
  set τw := g * (lrRho β + δ) / (lrRho β + δ * g)
  have hb : 0 < α * (1 + φ) / (1 - α) := by positivity
  -- the peak of `h` in `s`
  have hpeak : α * (1 + φ) / (1 - α) * (1 - g) / ((1 + φ + α * (1 + φ) / (1 - α)) *
      (lrRho β + δ)) = lrS α β δ τw := by
    rw [hsτ, fig156_s0]
    field_simp
    ring
  have hU : lrS α β δ 0 < (1 - g) / (lrRho β + δ) := by
    rw [fig156_s0]
    exact div_lt_div_of_pos_right (by linarith) hc
  have hinc := fig156_hump_strictMonoOn (by linarith : (0 : ℝ) < 1 + φ) hb hc
    (by linarith : (0 : ℝ) < 1 - g)
  have hdec := fig156_hump_strictAntiOn (by linarith : (0 : ℝ) < 1 + φ) hb hc
    (by linarith : (0 : ℝ) < 1 - g)
  rw [hpeak] at hinc hdec
  obtain ⟨hA, hB⟩ := fig156_comp_hump hα0 hβ0 hβ1 hδ hU hτ0.le hτ1 hinc hdec
  refine ⟨hτ0, hτ1, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg hx.1 (by linarith [hx.2]),
      fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg hy.1 (by linarith [hy.2])]
    exact hA hx hy hxy
  · intro x hx y hy hxy
    rw [fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg (by linarith [hx.1]) hx.2,
      fig156_cw_eq hα0 hα1 hβ0 hβ1 hδ hg (by linarith [hy.1]) hy.2]
    exact hB hx hy hxy

/-- **Figure 15.6, Panel B**, the peak: under the hypotheses of `fig156_cw_hump`, `c_w` attains
its strict maximum over `[0, 1)` at `τ_w = g(ρ + δ)/(ρ + δg)`. -/
theorem fig156_cw_isMaxOn {α β δ φ g τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg0 : 0 < g) (hg : g < 1 - α) (hτ0 : 0 ≤ τk)
    (hτ1 : τk < 1) (hne : τk ≠ g * (lrRho β + δ) / (lrRho β + δ * g)) :
    fig156Cw α β δ φ g τk < fig156Cw α β δ φ g (g * (lrRho β + δ) / (lrRho β + δ * g)) := by
  obtain ⟨h0, h1, hA, hB⟩ := fig156_cw_hump hα0 hα1 hβ0 hβ1 hδ hφ hg0 hg
  rcases lt_or_gt_of_ne hne with h | h
  · exact hA ⟨hτ0, h.le⟩ ⟨h0.le, le_rfl⟩ h
  · exact hB ⟨le_rfl, h1⟩ ⟨h.le, hτ1⟩ h

/-- **Figure 15.6, Panel B**, where the peak is: at `τ_w = g(ρ + δ)/(ρ + δg)` the budget-balancing
labour tax (15.14) equals `g`, so the capital-tax revenue `τ_k(r − δ)k = gy − g(1 − α)y = gαy`:
labour income and capital income are taxed at the same average rate `g`. -/
theorem fig156_cw_peak_tauL {α β δ g : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hg0 : 0 < g) (hg1 : g < 1) :
    incTauL α β δ g (g * (lrRho β + δ) / (lrRho β + δ * g)) = g ∧
      incBud α β δ (g * (lrRho β + δ) / (lrRho β + δ * g)) = g * α := by
  obtain ⟨hsτ, _, hτ1⟩ := fig156_s_eq (α := α) hβ0 hβ1 hδ (K := 1 - g) (by linarith)
    (by linarith)
  have eτ : (1 - (1 - g)) * (lrRho β + δ) / (lrRho β + δ * (1 - (1 - g))) =
      g * (lrRho β + δ) / (lrRho β + δ * g) := by ring_nf
  rw [eτ] at hsτ hτ1
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : (1 - α) ≠ 0 := by linarith
  have hT : incTauL α β δ g (g * (lrRho β + δ) / (lrRho β + δ * g)) = g := by
    rw [fig156_tauL_eq hα1 hβ0 hβ1 hδ hτ1, hsτ, fig156_s0]
    field_simp
    ring
  refine ⟨hT, ?_⟩
  unfold incTauL at hT
  rw [div_eq_iff h1α] at hT
  linarith

/-! ### Panel C: capitalists' consumption -/

/-- **Figure 15.6, Panel C**, the book's claim under its exact condition (AKMM, p. 450: "When
`τ_k` is restricted to be non-negative, steady-state consumption of capitalists is maximized at
`τ_k = 0`"). For `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0` and `g ≤ (1 − α)/(1 + αφ)`, `c_k`
is strictly decreasing on `[0, 1)`. -/
theorem fig156_ck_strictAntiOn {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg : g ≤ (1 - α) / (1 + α * φ)) :
    StrictAntiOn (fig156Ck α β δ φ g) (Ico 0 1) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαφ : 0 < 1 + α * φ := by positivity
  have hg' : g * (1 + α * φ) ≤ 1 - α := (le_div_iff₀ hαφ).mp hg
  have hgl : g < 1 - α := by nlinarith [mul_pos hα0 hφ]
  have hb : 0 < 1 + α * (1 + φ) / (1 - α) := by positivity
  have hinc := fig156_hump_strictMonoOn hφ hb hc (by linarith : (0 : ℝ) < 1 - g)
  have hpk : lrS α β δ 0 ≤ (1 + α * (1 + φ) / (1 - α)) * (1 - g) /
      ((φ + (1 + α * (1 + φ) / (1 - α))) * (lrRho β + δ)) := by
    rw [fig156_s0]
    have e : (1 + α * (1 + φ) / (1 - α)) * (1 - g) /
        ((φ + (1 + α * (1 + φ) / (1 - α))) * (lrRho β + δ)) =
        (1 + α * φ) * (1 - g) / ((1 + φ) * (lrRho β + δ)) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hc (by positivity)]
    nlinarith
  intro x hx y hy hxy
  rw [fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hx.1 hx.2, fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hy.1 hy.2]
  have hsx := fig156_s_bounds hα0 hβ0 hβ1 hδ hx.1 hx.2
  have hsy := fig156_s_bounds hα0 hβ0 hβ1 hδ hy.1 hy.2
  have hlt := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ hx.2 hy.2 hxy
  exact mul_lt_mul_of_pos_left (hinc ⟨hsy.1, by linarith⟩ ⟨hsx.1, by linarith⟩ hlt) hρ

/-- **Figure 15.6, Panel C, the other case** (correcting AKMM, p. 450). For
`(1 − α)/(1 + αφ) < g < 1 − α`, put `K = (1 + αφ)(1 − g)/((1 + φ)α) ∈ (0, 1)` and
`τ_c = (1 − K)(ρ + δ)/(ρ + δ(1 − K)) ∈ (0, 1)`: `c_k` is strictly increasing on `[0, τ_c]` and
strictly decreasing on `[τ_c, 1)`, so it is maximal at `τ_c > 0`, not at `0`. -/
theorem fig156_ck_hump {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg0 : (1 - α) / (1 + α * φ) < g)
    (hg : g < 1 - α) :
    let K := (1 + α * φ) * (1 - g) / ((1 + φ) * α)
    0 < K ∧ K < 1 ∧
      0 < (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) ∧
      (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)) < 1 ∧
      StrictMonoOn (fig156Ck α β δ φ g)
        (Icc 0 ((1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K)))) ∧
      StrictAntiOn (fig156Ck α β δ φ g)
        (Ico ((1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K))) 1) := by
  intro K
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hc : 0 < lrRho β + δ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαφ : 0 < 1 + α * φ := by positivity
  have hg' : 1 - α < g * (1 + α * φ) := (div_lt_iff₀ hαφ).mp hg0
  have hK0 : 0 < K := by
    have : 0 < 1 - g := by linarith
    positivity
  have hK1 : K < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hsτ, hτ0, hτ1⟩ := fig156_s_eq (α := α) hβ0 hβ1 hδ hK0 hK1
  set τc := (1 - K) * (lrRho β + δ) / (lrRho β + δ * (1 - K))
  have hb : 0 < 1 + α * (1 + φ) / (1 - α) := by positivity
  have hpeak : (1 + α * (1 + φ) / (1 - α)) * (1 - g) /
      ((φ + (1 + α * (1 + φ) / (1 - α))) * (lrRho β + δ)) = lrS α β δ τc := by
    rw [hsτ, fig156_s0]
    simp only [K]
    field_simp
    ring
  have hU : lrS α β δ 0 < (1 - g) / (lrRho β + δ) := by
    rw [fig156_s0]
    exact div_lt_div_of_pos_right (by linarith) hc
  have hinc := fig156_hump_strictMonoOn hφ hb hc (by linarith : (0 : ℝ) < 1 - g)
  have hdec := fig156_hump_strictAntiOn hφ hb hc (by linarith : (0 : ℝ) < 1 - g)
  rw [hpeak] at hinc hdec
  obtain ⟨hA, hB⟩ := fig156_comp_hump hα0 hβ0 hβ1 hδ hU hτ0.le hτ1 hinc hdec
  refine ⟨hK0, hK1, hτ0, hτ1, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hx.1 (by linarith [hx.2]),
      fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ hy.1 (by linarith [hy.2])]
    exact mul_lt_mul_of_pos_left (hA hx hy hxy) hρ
  · intro x hx y hy hxy
    rw [fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ (by linarith [hx.1]) hx.2,
      fig156_ck_eq hα0 hα1 hβ0 hβ1 hδ (by linarith [hy.1]) hy.2]
    exact mul_lt_mul_of_pos_left (hB hx hy hxy) hρ

/-- **Figure 15.6, Panel C, the exact statement** (correcting AKMM, p. 450). For `0 < α < 1`,
`0 < β < 1`, `δ ≥ 0`, `φ > 0` and `g < 1 − α` (so that `τ_ℓ(0) < 1`), capitalists' consumption
on `0 ≤ τ_k < 1` is maximal at `τ_k = 0` if and only if `g ≤ (1 − α)/(1 + αφ)`, i.e.
`τ_ℓ(0) = g/(1 − α) ≤ 1/(1 + αφ)`. -/
theorem fig156_ck_max_at_zero_iff {α β δ φ g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hg : g < 1 - α) :
    (∀ τk ∈ Ico (0 : ℝ) 1, fig156Ck α β δ φ g τk ≤ fig156Ck α β δ φ g 0) ↔
      g ≤ (1 - α) / (1 + α * φ) := by
  constructor
  · intro h
    by_contra hc
    replace hc := not_le.mp hc
    obtain ⟨_, _, hτ0, hτ1, hA, _⟩ := fig156_ck_hump hα0 hα1 hβ0 hβ1 hδ hφ hc hg
    have := hA ⟨le_rfl, hτ0.le⟩ ⟨hτ0.le, le_rfl⟩ hτ0
    linarith [h _ ⟨hτ0.le, hτ1⟩]
  · intro hg' τk hτ
    exact (fig156_ck_strictAntiOn hα0 hα1 hβ0 hβ1 hδ hφ hg').antitoneOn ⟨le_rfl, one_pos⟩ hτ
      hτ.1

/-- **Counterexample to "consumption of capitalists is maximized at `τ_k = 0`"** (AKMM, p. 450),
at the parameters of `inc_excess_cost_not_min_at_zero`: `α = 1/2`, `β = 2/3` (`ρ = 1/2`),
`δ = 1/10`, `φ = 1`, `g = 2/5` (> `(1 − α)/(1 + αφ) = 1/3`, `τ_ℓ < 1`). Then `c_k = 25/864` at
`τ_k = 0` and `21600/707281 > 25/864` at `τ_k = 1/5`. -/
theorem fig156_ck_not_max_at_zero :
    fig156Ck (1 / 2) (2 / 3) (1 / 10) 1 (2 / 5) 0 = 25 / 864 ∧
      fig156Ck (1 / 2) (2 / 3) (1 / 10) 1 (2 / 5) (1 / 5) = 21600 / 707281 ∧
      (25 / 864 : ℝ) < 21600 / 707281 := by
  have e : ((1 : ℝ) / 2) * (1 + 1) / (1 - 1 / 2) = 2 := by norm_num
  refine ⟨?_, ?_, by norm_num⟩ <;>
    simp only [fig156Ck, incOutput, incM, incTauL, incBud, lrS, lrRho, e, Real.rpow_one,
      Real.rpow_two] <;> norm_num

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Laffer curve

AKMM, §15.3.4, pp. 453–454, footnote 6.

Steady-state revenue in the GHH economy with `τ_c = 0` is
`R(τ_ℓ, τ_k) = τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y`, with `y` from (15.13) (`lafRevenue`).
Writing `z = (1 − τ_ℓ)(1 − α)` and `K = 1 − (ρ + δ)s`, `R = (K − z)z^φ(s^{α/(1−α)})^{1+φ}`
(`laf_revenue_eq`).

* `(K − z)z^φ ≤ φ^φ(K/(1 + φ))^{1+φ}` for `z ≥ 0`, with equality at `z = φK/(1 + φ)` (weighted
  AM–GM; `laf_amgm`, `laf_amgm_eq`).
* Footnote 6: for each `τ_k`, revenue is maximised over `τ_ℓ ≤ 1` at
  `τ_ℓ = (1 − τ_kρφα/((1 − α)(ρ + (1 − τ_k)δ)))/(1 + φ)` (`footnote_6`).
* **The revenue-maximising pair** over `τ_ℓ ∈ [0, 1]`, `τ_k ∈ [0, 1)` is `(1/(1 + φ), 0)`
  (`laf_isMaxOn`), and any positive `τ_k` raises strictly less (`laf_lt_of_pos`); this is the
  global form of footnote 6's "tax revenue is declining in `τ_k` at `τ_k = 0`". The proof uses
  the wage bound `inc_wage_le`.
* The revenue-maximising labour tax `1/(1 + φ)` falls as the Frisch elasticity `φ` rises
  (`laf_rate_strictAntiOn`).
* The Laffer curve at `τ_k = 0` is hump-shaped: zero at `τ_ℓ = 0` and `τ_ℓ = 1`, positive in
  between (`laf_hump`); at `τ_ℓ = 1` hours are zero (`laf_hours_zero`).

Departures: none. (The book asks for "positive" tax rates; we use `τ_ℓ, τ_k ≥ 0`.)
-/

namespace AKMM.FiscalPolicy

open Real

/-- Steady-state tax revenue `τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y` (AKMM, fn. 6, p. 454),
with `y` from (15.13) at `τ_c = 0`. -/
noncomputable def lafRevenue (α β δ φ τl τk : ℝ) : ℝ :=
  (τl * (1 - α) + incBud α β δ τk) * incOutput α φ ((1 - τl) * (1 - α)) (lrS α β δ τk)

/-- `τ_kρα/(ρ + (1 − τ_k)δ) = α − (ρ + δ)s` (for `τ_k < 1`, `ρ > 0`, `δ ≥ 0`). -/
theorem laf_bud_eq {α β δ τk : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hτk : τk < 1) :
    incBud α β δ τk = α - (lrRho β + δ) * lrS α β δ τk := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hd : 0 < lrRho β + (1 - τk) * δ := by
    have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
    linarith
  unfold incBud lrS
  rw [mul_comm δ (1 - τk)]
  field_simp
  ring

/-- AKMM, fn. 6: `R = (K − z)z^φ(s^{α/(1−α)})^{1+φ}` with `z = (1 − τ_ℓ)(1 − α)`,
`K = 1 − (ρ + δ)s`. -/
theorem laf_revenue_eq {α β δ φ τl τk : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hτk : τk < 1) (hs : 0 < lrS α β δ τk) :
    lafRevenue α β δ φ τl τk =
      ((1 - (lrRho β + δ) * lrS α β δ τk) - (1 - τl) * (1 - α)) *
        ((1 - τl) * (1 - α)) ^ φ * (lrS α β δ τk ^ (α / (1 - α))) ^ (1 + φ) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  unfold lafRevenue incOutput
  rw [laf_bud_eq hβ0 hβ1 hδ hτk, ← Real.rpow_mul hs.le,
    show α / (1 - α) * (1 + φ) = α * (1 + φ) / (1 - α) by ring]
  ring

/-- Weighted AM–GM: for `φ > 0`, `K ≥ 0`, `z ≥ 0`, `(K − z)z^φ ≤ φ^φ(K/(1 + φ))^{1+φ}`. -/
theorem laf_amgm {φ K z : ℝ} (hφ : 0 < φ) (hK : 0 ≤ K) (hz : 0 ≤ z) :
    (K - z) * z ^ φ ≤ φ ^ φ * (K / (1 + φ)) ^ (1 + φ) := by
  have hφ1 : 0 < 1 + φ := by linarith
  have hR : 0 ≤ φ ^ φ * (K / (1 + φ)) ^ (1 + φ) := by positivity
  by_cases hKz : K ≤ z
  · have : (K - z) * z ^ φ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hz φ)
    linarith
  push Not at hKz
  have hw1 : 0 ≤ 1 / (1 + φ) := by positivity
  have hw2 : 0 ≤ φ / (1 + φ) := by positivity
  have hw : 1 / (1 + φ) + φ / (1 + φ) = 1 := by field_simp
  have hp1 : 0 ≤ K - z := by linarith
  have hp2 : 0 ≤ z / φ := by positivity
  have hG := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hp1 hp2 hw
  have harith : 1 / (1 + φ) * (K - z) + φ / (1 + φ) * (z / φ) = K / (1 + φ) := by
    field_simp
    ring
  rw [harith] at hG
  have hlhs : 0 ≤ (K - z) ^ (1 / (1 + φ)) * (z / φ) ^ (φ / (1 + φ)) := by positivity
  have hpow := Real.rpow_le_rpow hlhs hG hφ1.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hp1,
    ← Real.rpow_mul hp2, one_div_mul_cancel hφ1.ne', div_mul_cancel₀ _ hφ1.ne',
    Real.rpow_one, Real.div_rpow hz hφ.le] at hpow
  have hφφ : 0 < φ ^ φ := Real.rpow_pos_of_pos hφ φ
  have : (K - z) * z ^ φ = φ ^ φ * ((K - z) * (z ^ φ / φ ^ φ)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hpow hφφ.le

/-- The AM–GM bound is attained at `z = φK/(1 + φ)`. -/
theorem laf_amgm_eq {φ K : ℝ} (hφ : 0 < φ) (hK : 0 ≤ K) :
    (K - φ * K / (1 + φ)) * (φ * K / (1 + φ)) ^ φ = φ ^ φ * (K / (1 + φ)) ^ (1 + φ) := by
  have hφ1 : 0 < 1 + φ := by linarith
  have hKφ : 0 ≤ K / (1 + φ) := by positivity
  rw [show φ * K / (1 + φ) = φ * (K / (1 + φ)) by ring, Real.mul_rpow hφ.le hKφ,
    Real.rpow_add' hKφ (by linarith), Real.rpow_one,
    show K - φ * (K / (1 + φ)) = K / (1 + φ) by field_simp; ring]
  ring

/-- **Footnote 6** (AKMM, p. 454): for given `τ_k ∈ [0, 1)` the revenue-maximising labour tax
(over `τ_ℓ ≤ 1`) is `τ_ℓ = (1 − τ_kρφα/((1 − α)(ρ + (1 − τ_k)δ)))/(1 + φ)`. -/
theorem footnote_6 {α β δ φ τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) (hτ0 : 0 ≤ τk) (hτk : τk < 1) :
    IsMaxOn (fun τl => lafRevenue α β δ φ τl τk) (Set.Iic 1)
      ((1 - τk * lrRho β / (1 - α) * φ * (α / (lrRho β + (1 - τk) * δ))) / (1 + φ)) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have h1α : 0 < 1 - α := by linarith
  have hφ1 : 0 < 1 + φ := by linarith
  have hs : 0 < lrS α β δ τk := by
    have : 0 < 1 - τk := by linarith
    unfold lrS
    positivity
  set K := 1 - (lrRho β + δ) * lrS α β δ τk with hK
  have hKpos : 0 ≤ K := by
    have hb : 0 ≤ incBud α β δ τk := by
      have : 0 < lrRho β + (1 - τk) * δ := by
        have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
        linarith
      unfold incBud
      positivity
    have := laf_bud_eq hβ0 hβ1 hδ hτk (α := α)
    linarith
  have hA : 0 ≤ (lrS α β δ τk ^ (α / (1 - α))) ^ (1 + φ) := by positivity
  set τs := (1 - τk * lrRho β / (1 - α) * φ * (α / (lrRho β + (1 - τk) * δ))) / (1 + φ)
  have hzs : (1 - τs) * (1 - α) = φ * K / (1 + φ) := by
    have hb := laf_bud_eq hβ0 hβ1 hδ hτk (α := α)
    unfold incBud at hb
    have hd : 0 < lrRho β + (1 - τk) * δ := by
      have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
      linarith
    rw [hK]
    have : (lrRho β + δ) * lrS α β δ τk = α - τk * lrRho β * α / (lrRho β + (1 - τk) * δ) := by
      linarith
    rw [this]
    simp only [τs]
    field_simp
    ring
  intro τl hτl
  simp only [Set.mem_ofPred_eq]
  have hz : 0 ≤ (1 - τl) * (1 - α) := mul_nonneg (by linarith [Set.mem_Iic.mp hτl]) h1α.le
  rw [laf_revenue_eq hα1 hβ0 hβ1 hδ hτk hs, laf_revenue_eq hα1 hβ0 hβ1 hδ hτk hs, ← hK, hzs,
    laf_amgm_eq hφ hKpos]
  exact mul_le_mul_of_nonneg_right (laf_amgm hφ hKpos hz) hA

/-- The no-tax value `s₀ = α/(ρ + δ)` of `s`. -/
theorem laf_s0 {α β δ : ℝ} : lrS α β δ 0 = α / (lrRho β + δ) := by
  unfold lrS
  simp

/-- AKMM, fn. 6 (global form): for `τ_ℓ ∈ [0, 1]` and `τ_k ∈ [0, 1)`,
`R(τ_ℓ, τ_k) ≤ φ^φ((1 − α)s₀^{α/(1−α)}/(1 + φ))^{1+φ}`, strictly if `τ_k > 0`. -/
theorem laf_bound {α β δ φ τl τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) (hτl : τl ≤ 1) (hτ0 : 0 ≤ τk) (hτk : τk < 1) :
    lafRevenue α β δ φ τl τk ≤
      φ ^ φ * ((1 - α) * lrS α β δ 0 ^ (α / (1 - α)) / (1 + φ)) ^ (1 + φ) ∧
    (0 < τk → lafRevenue α β δ φ τl τk <
      φ ^ φ * ((1 - α) * lrS α β δ 0 ^ (α / (1 - α)) / (1 + φ)) ^ (1 + φ)) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have h1α : 0 < 1 - α := by linarith
  have hφ1 : 0 < 1 + φ := by linarith
  have hc : 0 < lrRho β + δ := by linarith
  set s := lrS α β δ τk with hsdef
  have hs : 0 < s := by
    have : 0 < 1 - τk := by linarith
    rw [hsdef]
    unfold lrS
    positivity
  have hss : s ≤ α / (lrRho β + δ) := by
    rw [← laf_s0]
    exact (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ).antitoneOn (Set.mem_Iio.mpr one_pos)
      (Set.mem_Iio.mpr hτk) hτ0
  set K := 1 - (lrRho β + δ) * s with hK
  set A := s ^ (α / (1 - α)) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos hs _
  have hKpos : 0 ≤ K := by
    have : (lrRho β + δ) * s ≤ α := by
      have := mul_le_mul_of_nonneg_left hss hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    linarith
  obtain ⟨hW, hWs⟩ := inc_wage_le hα0 hα1 hc hs hss
  rw [← hK, ← hA, ← laf_s0] at hW hWs
  have hz : 0 ≤ (1 - τl) * (1 - α) := mul_nonneg (by linarith) h1α.le
  have hR : lafRevenue α β δ φ τl τk ≤ φ ^ φ * (K * A / (1 + φ)) ^ (1 + φ) := by
    rw [laf_revenue_eq hα1 hβ0 hβ1 hδ hτk hs, ← hsdef, ← hK, ← hA]
    have := mul_le_mul_of_nonneg_right (laf_amgm hφ hKpos hz)
      (Real.rpow_nonneg hApos.le (1 + φ))
    calc (K - (1 - τl) * (1 - α)) * ((1 - τl) * (1 - α)) ^ φ * A ^ (1 + φ)
        ≤ φ ^ φ * (K / (1 + φ)) ^ (1 + φ) * A ^ (1 + φ) := this
      _ = φ ^ φ * (K * A / (1 + φ)) ^ (1 + φ) := by
          rw [mul_assoc, ← Real.mul_rpow (by positivity) hApos.le]
          ring_nf
  have hφφ : 0 < φ ^ φ := Real.rpow_pos_of_pos hφ φ
  constructor
  · refine hR.trans (mul_le_mul_of_nonneg_left ?_ hφφ.le)
    exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hW hφ1.le) hφ1.le
  · intro hpos
    have hlt : s < lrS α β δ 0 := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ (Set.mem_Iio.mpr one_pos)
        (Set.mem_Iio.mpr hτk) hpos
    refine hR.trans_lt (mul_lt_mul_of_pos_left ?_ hφφ)
    exact Real.rpow_lt_rpow (by positivity) (div_lt_div_of_pos_right (hWs hlt) hφ1) hφ1

/-- The bound of `laf_bound` is attained at `(τ_ℓ, τ_k) = (1/(1 + φ), 0)`. -/
theorem laf_value_at_max {α β δ φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    lafRevenue α β δ φ (1 / (1 + φ)) 0 =
      φ ^ φ * ((1 - α) * lrS α β δ 0 ^ (α / (1 - α)) / (1 + φ)) ^ (1 + φ) := by
  have h1α : 0 < 1 - α := by linarith
  have hφ1 : 0 < 1 + φ := by linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs : 0 < lrS α β δ 0 := by
    rw [laf_s0]
    exact div_pos hα0 (by linarith)
  rw [laf_revenue_eq hα1 hβ0 hβ1 hδ (by norm_num) hs]
  have hK : 1 - (lrRho β + δ) * lrS α β δ 0 = 1 - α := by
    rw [laf_s0]
    field_simp
  have hz : (1 - 1 / (1 + φ)) * (1 - α) = φ * (1 - α) / (1 + φ) := by
    field_simp
    ring
  rw [hK, hz, laf_amgm_eq hφ h1α.le, mul_assoc,
    ← Real.mul_rpow (by positivity) (Real.rpow_nonneg hs.le _)]
  ring_nf

/-- **The revenue-maximising tax rates** (AKMM, p. 453): over `τ_ℓ ∈ [0, 1]`, `τ_k ∈ [0, 1)`,
steady-state revenue is maximised at `τ_ℓ = 1/(1 + φ)`, `τ_k = 0`. -/
theorem laf_isMaxOn {α β δ φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    IsMaxOn (fun p : ℝ × ℝ => lafRevenue α β δ φ p.1 p.2) (Set.Icc 0 1 ×ˢ Set.Ico 0 1)
      (1 / (1 + φ), 0) := by
  intro p hp
  simp only [Set.mem_ofPred_eq]
  obtain ⟨⟨_, h1⟩, ⟨h2, h3⟩⟩ := hp
  rw [laf_value_at_max hα0 hα1 hβ0 hβ1 hδ hφ]
  exact (laf_bound hα0 hα1 hβ0 hβ1 hδ hφ h1 h2 h3).1

/-- AKMM, fn. 6: any positive capital tax raises strictly less than the maximum. -/
theorem laf_lt_of_pos {α β δ φ τl τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hτl : τl ≤ 1) (hτ0 : 0 < τk) (hτk : τk < 1) :
    lafRevenue α β δ φ τl τk < lafRevenue α β δ φ (1 / (1 + φ)) 0 := by
  rw [laf_value_at_max hα0 hα1 hβ0 hβ1 hδ hφ]
  exact (laf_bound hα0 hα1 hβ0 hβ1 hδ hφ hτl hτ0.le hτk).2 hτ0

/-- AKMM, p. 454: "the higher is the Frisch elasticity of labor supply, `φ`, the lower is the
revenue-maximizing labor tax rate". -/
theorem laf_rate_strictAntiOn : StrictAntiOn (fun φ : ℝ => 1 / (1 + φ)) (Set.Ioi 0) := by
  intro a ha b _ hab
  have ha' : 0 < a := ha
  simp only
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- AKMM, p. 454: at `τ_ℓ = 1` hours `((1 − τ_ℓ)w)^φ` are zero. -/
theorem laf_hours_zero {φ w : ℝ} (hφ : 0 < φ) : ghhHours φ 1 0 w = 0 := by
  simp [ghhHours, Real.zero_rpow hφ.ne']

/-- AKMM, p. 454: "Revenue is hump-shaped in the tax rate": at `τ_k = 0`, revenue is zero at
`τ_ℓ = 0` and at `τ_ℓ = 1`, and positive for `0 < τ_ℓ < 1`. -/
theorem laf_hump {α β δ φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    lafRevenue α β δ φ 0 0 = 0 ∧ lafRevenue α β δ φ 1 0 = 0 ∧
      ∀ τl, 0 < τl → τl < 1 → 0 < lafRevenue α β δ φ τl 0 := by
  have h1α : 0 < 1 - α := by linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs : 0 < lrS α β δ 0 := by
    rw [laf_s0]
    exact div_pos hα0 (by linarith)
  have hb : incBud α β δ 0 = 0 := by simp [incBud]
  refine ⟨?_, ?_, ?_⟩
  · simp [lafRevenue, hb]
  · simp [lafRevenue, hb, incOutput, Real.zero_rpow hφ.ne']
  · intro τl h0 h1
    unfold lafRevenue incOutput
    rw [hb, add_zero]
    have : 0 < (1 - τl) * (1 - α) := mul_pos (by linarith) h1α
    positivity

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theories of government spending

AKMM, §15.3.5, pp. 454–455.

* Public goods: with utility `u(c, g)` and lump-sum finance, the first best splits resources
  `c + g = Y` so that `u₁(c, g) = u₂(c, g)` (`tg_first_best`).
* Public capital: `f(k, k_g, ℓ) = Ak^αℓ^{1−α}k_g^θ` (`tgF`) is homogeneous of degree `1 + θ`
  (`tg_homogeneous`): constant returns in `(k, ℓ)` (`tg_crs_private`) and increasing returns
  overall when `θ > 0` (`tg_irs`). The law of motion `k_{g,t+1} = i_{g,t} + (1 − δ_g)k_{g,t}` is
  `tgLaw`.
* With non-distortionary finance, the planner's split of a given amount of saving between private
  and public capital equates the net marginal products, `f_k − δ = f_g − δ_g`
  (`tg_net_returns_equal`).

Departures: the last item is stated for the split of next period's capital stocks with a fixed
total (the margin on which the two Euler equations of the planner differ); the full dynamic
planner is not restated.
-/

namespace AKMM.FiscalPolicy

open Real

/-- AKMM, p. 454: "The first best solution … prescribes equating the marginal utility of
private consumption to the marginal utility of public consumption": if `(c, g)` maximises
`u` on `{c + g = Y}` and `u` is differentiable there, `u₁(c, g) = u₂(c, g)`. -/
theorem tg_first_best {u : ℝ → ℝ → ℝ} {c g Y u1 u2 : ℝ} (hcg : c + g = Y)
    (hmax : ∀ c' g', c' + g' = Y → u c' g' ≤ u c g) (hu : DTPartials u c g u1 u2) :
    u1 = u2 := by
  have hd := dt_curve_hasDerivAt (h := fun ε => ε) (g := fun ε => -ε) hu (hasDerivAt_id 0)
    ((hasDerivAt_id 0).neg) rfl (by simp)
  have hloc : IsLocalMax (fun ε => u (c + ε) (g + -ε)) 0 :=
    Filter.Eventually.of_forall fun ε => by
      simp only [add_zero, neg_zero]
      exact hmax _ _ (by linarith)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- Output with public capital `f(k, k_g, ℓ) = Ak^αℓ^{1−α}k_g^θ` (AKMM, p. 455). -/
noncomputable def tgF (A α θ k kg l : ℝ) : ℝ := A * k ^ α * l ^ (1 - α) * kg ^ θ

/-- The law of motion of public capital `k_{g,t+1} = i_{g,t} + (1 − δ_g)k_{g,t}` (AKMM, p. 455). -/
def tgLaw (δg : ℝ) (ig kg : ℕ → ℝ) : Prop := ∀ t, kg (t + 1) = ig t + (1 - δg) * kg t

/-- AKMM, p. 455: `f(λk, λk_g, λℓ) = λ^{1+θ}f(k, k_g, ℓ)` for `λ, k, k_g, ℓ ≥ 0`. -/
theorem tg_homogeneous {A α θ k kg l lam : ℝ} (hlam : 0 ≤ lam) (hk : 0 ≤ k) (hkg : 0 ≤ kg)
    (hl : 0 ≤ l) (hlam0 : 0 < lam) :
    tgF A α θ (lam * k) (lam * kg) (lam * l) = lam ^ (1 + θ) * tgF A α θ k kg l := by
  unfold tgF
  rw [Real.mul_rpow hlam hk, Real.mul_rpow hlam hl, Real.mul_rpow hlam hkg,
    Real.rpow_add hlam0, Real.rpow_one]
  have : lam ^ α * lam ^ (1 - α) = lam := by
    rw [← Real.rpow_add hlam0]
    simp
  linear_combination (A * k ^ α * l ^ (1 - α) * kg ^ θ * lam ^ θ) * this

/-- AKMM, p. 455: constant returns in the private inputs `(k, ℓ)`. -/
theorem tg_crs_private {A α θ k kg l lam : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) (hlam0 : 0 < lam) :
    tgF A α θ (lam * k) kg (lam * l) = lam * tgF A α θ k kg l := by
  unfold tgF
  rw [Real.mul_rpow hlam0.le hk, Real.mul_rpow hlam0.le hl]
  have : lam ^ α * lam ^ (1 - α) = lam := by
    rw [← Real.rpow_add hlam0]
    simp
  linear_combination (A * k ^ α * l ^ (1 - α) * kg ^ θ) * this

/-- AKMM, p. 455: "If `θ > 0`, there are increasing returns to scale": scaling all inputs by
`λ > 1` multiplies positive output by more than `λ`. -/
theorem tg_irs {A α θ k kg l lam : ℝ} (hθ : 0 < θ) (hlam : 1 < lam) (hk : 0 ≤ k)
    (hkg : 0 ≤ kg) (hl : 0 ≤ l) (hf : 0 < tgF A α θ k kg l) :
    lam * tgF A α θ k kg l < tgF A α θ (lam * k) (lam * kg) (lam * l) := by
  have hlam0 : 0 < lam := by linarith
  rw [tg_homogeneous hlam0.le hk hkg hl hlam0]
  refine mul_lt_mul_of_pos_right ?_ hf
  calc lam = lam ^ (1 : ℝ) := (Real.rpow_one lam).symm
    _ < lam ^ (1 + θ) := Real.rpow_lt_rpow_of_exponent_lt hlam (by linarith)

/-- AKMM, p. 455: "If revenue can be raised in a non-distortionary way, then it is optimal to
equate the marginal products of private and public capital, net of depreciation": if
`(k', k_g')` maximises next period's resources `f(k', k_g') + (1 − δ)k' + (1 − δ_g)k_g'` among
splits with `k' + k_g'` fixed, and `f` (at the given hours) is differentiable there with partials
`f_k`, `f_g`, then `f_k − δ = f_g − δ_g`. -/
theorem tg_net_returns_equal {f : ℝ → ℝ → ℝ} {k kg S δ δg fk fg : ℝ} (hS : k + kg = S)
    (hmax : ∀ k' kg', k' + kg' = S →
      f k' kg' + (1 - δ) * k' + (1 - δg) * kg' ≤ f k kg + (1 - δ) * k + (1 - δg) * kg)
    (hf : DTPartials f k kg fk fg) :
    fk - δ = fg - δg := by
  have hd := dt_curve_hasDerivAt (h := fun ε => ε) (g := fun ε => -ε) hf (hasDerivAt_id 0)
    ((hasDerivAt_id 0).neg) rfl (by simp)
  have hd2 : HasDerivAt (fun ε => f (k + ε) (kg + -ε) + (1 - δ) * (k + ε) + (1 - δg) * (kg + -ε))
      (fk * 1 + fg * -1 + (1 - δ) * 1 + (1 - δg) * -1) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_add k).const_mul (1 - δ)
    have h2 := ((hasDerivAt_id (0 : ℝ)).neg.const_add kg).const_mul (1 - δg)
    exact (hd.add h1).add h2
  have hloc : IsLocalMax
      (fun ε => f (k + ε) (kg + -ε) + (1 - δ) * (k + ε) + (1 - δg) * (kg + -ε)) 0 :=
    Filter.Eventually.of_forall fun ε => by
      simp only [add_zero, neg_zero]
      exact hmax _ _ (by linarith)
  have := hloc.hasDerivAt_eq_zero hd2
  linarith

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ricardian equivalence in two periods

AKMM, §15.4, pp. 455–456.

The household chooses `(c₀, ℓ₀, c₁, ℓ₁)` and bonds `b₀` subject to `c₀ + b₀ = w₀ℓ₀ + T₀` and
`c₁ = w₁ℓ₁ + (1 + r₁)b₀ − τ₁` (`ricFlow`). The government issues `B₀ = T₀` and repays with
`τ₁ = (1 + r₁)B₀` (`ricGov`).

* The flow constraints hold for some `b₀` iff the present-value constraint
  `c₀ + c₁/(1 + r₁) = w₀ℓ₀ + w₁ℓ₁/(1 + r₁) + T₀ − τ₁/(1 + r₁)` holds (`ric_pv_iff`); `b₀` drops out.
* With `τ₁ = (1 + r₁)T₀` the tax and transfer terms sum to zero (`ric_taxes_cancel`), so the
  budget set equals the one with `T₀ = τ₁ = B₀ = 0` (`ric_budgetSet_eq`): **for any preferences**
  a plan is optimal with the transfer iff it is optimal without (`ric_optimal_iff`), and the
  household finances an unchanged allocation by saving exactly `T₀` more (`ric_saving`), which
  matches the extra bonds and pays the tax (`ric_market_clears`).
* With labour fixed, this is Obstfeld–Rogoff's two-period timing neutrality, imported from
  `LifeCycleFiscalPolicy` (`ric_obstfeld_rogoff`).

Correction: p. 456 writes "zero taxes and transfers (`T₀ = τ₁ = B₁ = 0`)"; the debt in the
two-period model is `B₀` (`ricGov`).
-/

namespace AKMM.FiscalPolicy

/-- The household's flow budget constraints (AKMM, p. 455) for plan
`x = (c₀, ℓ₀, c₁, ℓ₁)` and bond purchases `b₀`. -/
def ricFlow (w0 w1 r1 T0 τ1 : ℝ) (x : ℝ × ℝ × ℝ × ℝ) (b0 : ℝ) : Prop :=
  x.1 + b0 = w0 * x.2.1 + T0 ∧ x.2.2.1 = w1 * x.2.2.2 + (1 + r1) * b0 - τ1

/-- The household's budget set: plans financed by some bond position. -/
def ricBudgetSet (w0 w1 r1 T0 τ1 : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | ∃ b0, ricFlow w0 w1 r1 T0 τ1 x b0}

/-- The government's policy (AKMM, p. 455): the transfer `T₀` is financed by debt `B₀ = T₀`,
repaid by the lump-sum tax `τ₁ = (1 + r₁)B₀`. -/
def ricGov (r1 T0 B0 τ1 : ℝ) : Prop := B0 = T0 ∧ τ1 = (1 + r1) * B0

/-- AKMM, p. 455: the flow constraints hold for some `b₀` iff the present-value constraint holds;
"the value for debt purchases, `b₀`, drops out". -/
theorem ric_pv_iff {w0 w1 r1 T0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (x : ℝ × ℝ × ℝ × ℝ) :
    x ∈ ricBudgetSet w0 w1 r1 T0 τ1 ↔
      x.1 + x.2.2.1 / (1 + r1) = w0 * x.2.1 + w1 * x.2.2.2 / (1 + r1) + T0 - τ1 / (1 + r1) := by
  constructor
  · rintro ⟨b0, h0, h1⟩
    rw [h1]
    field_simp
    linear_combination (1 + r1) * h0
  · intro h
    refine ⟨w0 * x.2.1 + T0 - x.1, by ring, ?_⟩
    field_simp at h
    linear_combination h

/-- AKMM, p. 455: with `τ₁ = (1 + r₁)B₀ = (1 + r₁)T₀`, "the tax and transfer terms in the present
value budget constraint must sum to zero, regardless of the size of the initial transfer". -/
theorem ric_taxes_cancel {r1 T0 B0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (hg : ricGov r1 T0 B0 τ1) :
    T0 - τ1 / (1 + r1) = 0 := by
  obtain ⟨hB, hτ⟩ := hg
  rw [hτ, hB]
  field_simp
  ring

/-- AKMM, p. 456: the budget set with the debt-financed transfer equals the budget set with
`T₀ = τ₁ = B₀ = 0`. -/
theorem ric_budgetSet_eq {w0 w1 r1 T0 B0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (hg : ricGov r1 T0 B0 τ1) :
    ricBudgetSet w0 w1 r1 T0 τ1 = ricBudgetSet w0 w1 r1 0 0 := by
  ext x
  rw [ric_pv_iff hr, ric_pv_iff hr]
  have h := ric_taxes_cancel hr hg
  constructor <;> intro h' <;> simp only [zero_div, sub_zero, add_zero] at h' ⊢ <;> linarith

/-- **Ricardian equivalence** (AKMM, p. 456): "the household's optimal allocation of consumption
and hours must be identical to that in the case of zero taxes and transfers", for any utility
`U` over `(c₀, ℓ₀, c₁, ℓ₁)`. -/
theorem ric_optimal_iff {w0 w1 r1 T0 B0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (hg : ricGov r1 T0 B0 τ1)
    (U : ℝ × ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ × ℝ) :
    (x ∈ ricBudgetSet w0 w1 r1 T0 τ1 ∧ ∀ y ∈ ricBudgetSet w0 w1 r1 T0 τ1, U y ≤ U x) ↔
      (x ∈ ricBudgetSet w0 w1 r1 0 0 ∧ ∀ y ∈ ricBudgetSet w0 w1 r1 0 0, U y ≤ U x) := by
  rw [ric_budgetSet_eq hr hg]

/-- AKMM, p. 456: "The household must therefore respond to the initial transfer `T₀` by increasing
savings by exactly `T₀`": a plan financed by `b₀` without the policy is financed by `b₀ + T₀` with
it. -/
theorem ric_saving {w0 w1 r1 T0 B0 τ1 b0 : ℝ} (hg : ricGov r1 T0 B0 τ1) (x : ℝ × ℝ × ℝ × ℝ)
    (h : ricFlow w0 w1 r1 0 0 x b0) : ricFlow w0 w1 r1 T0 τ1 x (b0 + T0) := by
  obtain ⟨hB, hτ⟩ := hg
  obtain ⟨h0, h1⟩ := h
  constructor
  · linarith
  · rw [hτ, hB, h1]
    ring

/-- AKMM, p. 456: the extra saving "(i) exactly match[es] the additional supply of government
bonds issued, and (ii) provide[s] exactly enough second period income to pay the expected
lump-sum tax". -/
theorem ric_market_clears {r1 T0 B0 τ1 b0 : ℝ} (hg : ricGov r1 T0 B0 τ1) :
    (b0 + T0) - b0 = B0 ∧ (1 + r1) * ((b0 + T0) - b0) = τ1 := by
  obtain ⟨hB, hτ⟩ := hg
  constructor
  · rw [hB]
    ring
  · rw [hτ, hB]
    ring

/-- With hours fixed, AKMM's neutrality is Obstfeld–Rogoff's (O&R (3.1), p. 130): the private
budget set with taxes `(−T₀, (1 + r₁)T₀)` on endowments `(w₀ℓ₀, w₁ℓ₁)` equals the one without
taxes (`ObstfeldRogoff…two_period_budgetSet_eq_of_pv_eq`). -/
theorem ric_obstfeld_rogoff {w0 w1 l0 l1 r1 T0 : ℝ} (hr : 1 + r1 ≠ 0) :
    ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.twoPeriodBudgetSet r1
        (w0 * l0) (w1 * l1) (-T0) ((1 + r1) * T0) =
      ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.twoPeriodBudgetSet r1
        (w0 * l0) (w1 * l1) 0 0 := by
  apply ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.two_period_budgetSet_eq_of_pv_eq
  field_simp
  ring

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ramsey taxation: the primal approach

AKMM, §15.5–15.5.1, (15.15)–(15.18), pp. 456–461.

Two periods, `y_t = A_tℓ_t`, `w_t = A_t` (15.15), storage at the exogenous rate `r`, government
spending `g₀, g₁`, a tax plan `(τ₀, τ₁, τ_{b,1})`. The marginal utilities at the allocation are
the numbers `u_{c,t}`, `u_{ℓ,t}`.

* A competitive equilibrium given the plan (`rmCE`) is, as on p. 459, the three household
  first-order conditions (15.16), the wages (15.15), and the household and government budgets.
  In a competitive equilibrium (15.18) holds (`eq_15_18`), and multiplying by `u_{c,0}` gives the
  implementability condition (`rmIC`).
* **The primal approach** (p. 459): an allocation is a competitive equilibrium for some tax plan
  iff it satisfies the resource constraint (15.17) (`rmRC`) and the implementability condition
  (`rm_primal`). The government's date-1 budget is implied by the others and (15.17) (Walras'
  law, `rm_walras`).
* The Lagrangian (`rmLagrangian`) and its four partial derivatives, which are the printed
  first-order conditions (`rm_foc_c0`, `rm_foc_l0`, `rm_foc_c1`, `rm_foc_l1`).
* Separable CRRA `u = c^{1−σ}/(1 − σ) − ℓ^{1+1/φ}/(1 + 1/φ)` (`rmU`): `u_c = c^{−σ}`,
  `u_ℓ = −ℓ^{1/φ}`, `u_{cc}c = −σu_c`, `u_{ℓℓ}ℓ = u_ℓ/φ` and no cross terms (`rm_crra_derivs`);
  the first-order conditions simplify as printed (`rm_crra_focs`); at a solution
  `β(1 + r)u_{c,1} = u_{c,0}` and `u_{c,t}A_t(1 + µ − µσ)/(1 + µ + µ/φ) = −u_{ℓ,t}`
  (`rm_crra_euler`, `rm_crra_labour`). Comparing with (15.16): `τ_{b,1} = 0` and
  `τ₀ = τ₁ = µ(σ + 1/φ)/(1 + µ + µ/φ)` (`rm_ramsey_taxes`).
* Sign of the tax (p. 461: positive "as long as either `g₀` or `g₁` is strictly positive"): from
  the government's budget, `τ` has the sign of the present value of spending when the present
  value of output is positive (`rm_tax_pos`); then `µ ≠ 0`, and `µ > 0` when
  `1 + µ + µ/φ > 0` or `σ ≥ 1` (`rm_mu_pos`).

Departures: the competitive equilibrium is characterised by first-order conditions, as the book
does on p. 459 (for concave `u` these are also sufficient for the household optimum, which we
do not restate). The existence of the multipliers `λ, µ` at a Ramsey optimum (a constraint
qualification) is assumed, as in the book: the Ramsey results are stated for allocations that
satisfy the printed first-order conditions with some `λ, µ`, with the interiority conditions
`1 + µ − µσ ≠ 0`, `1 + µ + µ/φ ≠ 0` explicit.
-/

namespace AKMM.FiscalPolicy

/-- The resource constraint (15.17), AKMM p. 459:
`c₀ + g₀ + (c₁ + g₁)/(1 + r) = A₀ℓ₀ + A₁ℓ₁/(1 + r)`. -/
def rmRC (A0 A1 r g0 g1 c0 l0 c1 l1 : ℝ) : Prop :=
  c0 + g0 + (c1 + g1) / (1 + r) = A0 * l0 + A1 * l1 / (1 + r)

/-- The implementability condition, AKMM p. 459:
`u_{c,0}c₀ + βu_{c,1}c₁ = −u_{ℓ,0}ℓ₀ − βu_{ℓ,1}ℓ₁`. -/
def rmIC (β uc0 ul0 uc1 ul1 c0 l0 c1 l1 : ℝ) : Prop :=
  uc0 * c0 + β * uc1 * c1 = -ul0 * l0 - β * ul1 * l1

/-- A competitive equilibrium given the tax plan `(τ₀, τ₁, τ_{b,1})` (AKMM, pp. 457–459): household
saving `b₀`, government saving `b_{g,0}`, the household budgets, the first-order conditions
(15.16) with wages `w_t = A_t` (15.15), and the government budgets. -/
def rmCE (β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0 : ℝ) : Prop :=
  c0 = (1 - τ0) * A0 * l0 - b0 ∧ c1 = (1 - τ1) * A1 * l1 + (1 + r * (1 - τb)) * b0 ∧
    uc0 * A0 * (1 - τ0) = -ul0 ∧ uc1 * A1 * (1 - τ1) = -ul1 ∧
    uc0 = β * (1 + r * (1 - τb)) * uc1 ∧
    g0 + bg0 = τ0 * A0 * l0 ∧ g1 = τ1 * A1 * l1 + τb * r * b0 + (1 + r) * bg0

/-- AKMM, p. 459, **Walras' law**: the household budgets, the government's date-0 budget and the
resource constraint (15.17) imply the government's date-1 budget. -/
theorem rm_walras {A0 A1 r g0 g1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0 : ℝ} (hr : 1 + r ≠ 0)
    (h0 : c0 = (1 - τ0) * A0 * l0 - b0)
    (h1 : c1 = (1 - τ1) * A1 * l1 + (1 + r * (1 - τb)) * b0)
    (hg0 : g0 + bg0 = τ0 * A0 * l0) (hRC : rmRC A0 A1 r g0 g1 c0 l0 c1 l1) :
    g1 = τ1 * A1 * l1 + τb * r * b0 + (1 + r) * bg0 := by
  unfold rmRC at hRC
  field_simp at hRC
  linear_combination hRC - (1 + r) * h0 - h1 - (1 + r) * hg0

/-- **(15.18)** (AKMM, p. 459): in a competitive equilibrium,
`c₀ + c₁/(u_{c,0}/(βu_{c,1})) =
−(u_{ℓ,0}/u_{c,0})ℓ₀ − (u_{ℓ,1}/u_{c,1})ℓ₁/(u_{c,0}/(βu_{c,1}))`, and
multiplying through by `u_{c,0}` gives the implementability condition. -/
theorem eq_15_18 {β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0 : ℝ}
    (hβ : β ≠ 0) (huc0 : uc0 ≠ 0) (huc1 : uc1 ≠ 0)
    (h : rmCE β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0) :
    c0 + c1 / (uc0 / (β * uc1)) = -(ul0 / uc0) * l0 - ul1 / uc1 * l1 / (uc0 / (β * uc1)) ∧
      rmIC β uc0 ul0 uc1 ul1 c0 l0 c1 l1 := by
  obtain ⟨h0, h1, hf0, hf1, he, -, -⟩ := h
  have hR : 1 + r * (1 - τb) = uc0 / (β * uc1) := by
    rw [he]
    field_simp
  have hw0 : (1 - τ0) * A0 = -(ul0 / uc0) := by
    field_simp
    linear_combination hf0
  have hw1 : (1 - τ1) * A1 = -(ul1 / uc1) := by
    field_simp
    linear_combination hf1
  have hpv : c0 + c1 / (1 + r * (1 - τb)) =
      (1 - τ0) * A0 * l0 + (1 - τ1) * A1 * l1 / (1 + r * (1 - τb)) := by
    have hRne : 1 + r * (1 - τb) ≠ 0 := by
      rw [hR]
      exact div_ne_zero huc0 (mul_ne_zero hβ huc1)
    rw [h1, h0]
    field_simp
    ring
  have h18 : c0 + c1 / (uc0 / (β * uc1)) =
      -(ul0 / uc0) * l0 - ul1 / uc1 * l1 / (uc0 / (β * uc1)) := by
    rw [← hR, hpv, hw0, hw1]
    ring
  refine ⟨h18, ?_⟩
  unfold rmIC
  field_simp at h18
  linear_combination h18

/-- **The primal approach** (AKMM, p. 459): "any allocation that satisfies the resource constraint
and the implementability condition can be implemented by some feasible tax plan", and
conversely. For `β, r, 1 + r, A₀, A₁, u_{c,0}, u_{c,1} ≠ 0`, an allocation `(c₀, ℓ₀, c₁, ℓ₁)` with
marginal utilities `u_{c,t}, u_{ℓ,t}` is a competitive equilibrium for some tax plan
`(τ₀, τ₁, τ_{b,1})` (and savings `b₀, b_{g,0}`) iff it satisfies (15.17) and the implementability
condition. -/
theorem rm_primal {β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 : ℝ} (hβ : β ≠ 0) (hr : r ≠ 0)
    (hr1 : 1 + r ≠ 0) (hA0 : A0 ≠ 0) (hA1 : A1 ≠ 0) (huc0 : uc0 ≠ 0) (huc1 : uc1 ≠ 0) :
    (∃ τ0 τ1 τb b0 bg0, rmCE β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0) ↔
      rmRC A0 A1 r g0 g1 c0 l0 c1 l1 ∧ rmIC β uc0 ul0 uc1 ul1 c0 l0 c1 l1 := by
  constructor
  · rintro ⟨τ0, τ1, τb, b0, bg0, h⟩
    refine ⟨?_, (eq_15_18 hβ huc0 huc1 h).2⟩
    obtain ⟨h0, h1, -, -, -, hg0, hg1⟩ := h
    unfold rmRC
    field_simp
    linear_combination (1 + r) * h0 + h1 + (1 + r) * hg0 + hg1
  · rintro ⟨hRC, hIC⟩
    set τ0 := 1 + ul0 / (uc0 * A0)
    set τ1 := 1 + ul1 / (uc1 * A1)
    set τb := 1 - (uc0 / (β * uc1) - 1) / r
    set b0 := (1 - τ0) * A0 * l0 - c0
    set bg0 := τ0 * A0 * l0 - g0
    have hR : 1 + r * (1 - τb) = uc0 / (β * uc1) := by
      simp only [τb]
      field_simp
      ring
    have hw0 : (1 - τ0) * A0 = -(ul0 / uc0) := by
      simp only [τ0]
      field_simp
      ring
    have hw1 : (1 - τ1) * A1 = -(ul1 / uc1) := by
      simp only [τ1]
      field_simp
      ring
    have h0 : c0 = (1 - τ0) * A0 * l0 - b0 := by simp only [b0]; ring
    have h1 : c1 = (1 - τ1) * A1 * l1 + (1 + r * (1 - τb)) * b0 := by
      simp only [b0]
      rw [hR, hw0, hw1]
      unfold rmIC at hIC
      field_simp
      linear_combination hIC
    have hg0 : g0 + bg0 = τ0 * A0 * l0 := by simp only [bg0]; ring
    refine ⟨τ0, τ1, τb, b0, bg0, h0, h1, ?_, ?_, ?_, hg0, rm_walras hr1 h0 h1 hg0 hRC⟩
    · rw [show uc0 * A0 * (1 - τ0) = uc0 * ((1 - τ0) * A0) by ring, hw0]
      field_simp
    · rw [show uc1 * A1 * (1 - τ1) = uc1 * ((1 - τ1) * A1) by ring, hw1]
      field_simp
    · rw [hR]
      field_simp

/-- The Lagrangian of the Ramsey problem (AKMM, p. 459), with marginal-utility functions
`uc`, `ul`. -/
noncomputable def rmLagrangian (u uc ul : ℝ → ℝ → ℝ) (β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 : ℝ) :
    ℝ :=
  u c0 l0 + β * u c1 l1 + lam * (A0 * l0 + A1 * l1 / (1 + r) - c0 - g0 - (c1 + g1) / (1 + r)) +
    mu * (uc c0 l0 * c0 + β * uc c1 l1 * c1 + ul c0 l0 * l0 + β * ul c1 l1 * l1)

/-- AKMM, p. 460, first-order condition in `c₀`: `∂ℒ/∂c₀ = u_{c,0} − λ + µu_{c,0} + µu_{cc,0}c₀ +
µu_{ℓc,0}ℓ₀`. -/
theorem rm_foc_c0 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucc ulc : ℝ}
    (hu : HasDerivAt (fun c => u c l0) (uc c0 l0) c0)
    (hucc : HasDerivAt (fun c => uc c l0) ucc c0) (hulc : HasDerivAt (fun c => ul c l0) ulc c0) :
    HasDerivAt (fun c => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c l0 c1 l1)
      (uc c0 l0 - lam + mu * uc c0 l0 + mu * ucc * c0 + mu * ulc * l0) c0 := by
  unfold rmLagrangian
  have h1 := (hu.add_const (β * u c1 l1)).add
    (((hasDerivAt_id c0).const_sub (A0 * l0 + A1 * l1 / (1 + r))).sub_const
      (g0 + (c1 + g1) / (1 + r)) |>.const_mul lam)
  have h2 := (((hucc.mul (hasDerivAt_id c0)).add_const (β * uc c1 l1 * c1)).add
    ((hulc.mul_const l0))).add_const (β * ul c1 l1 * l1) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- AKMM, p. 460, first-order condition in `ℓ₀`: `∂ℒ/∂ℓ₀ = u_{ℓ,0} + λA₀ + µu_{ℓ,0} + µu_{cℓ,0}c₀ +
µu_{ℓℓ,0}ℓ₀`. -/
theorem rm_foc_l0 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucl ull : ℝ}
    (hu : HasDerivAt (fun l => u c0 l) (ul c0 l0) l0)
    (hucl : HasDerivAt (fun l => uc c0 l) ucl l0) (hull : HasDerivAt (fun l => ul c0 l) ull l0) :
    HasDerivAt (fun l => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c0 l c1 l1)
      (ul c0 l0 + lam * A0 + mu * ul c0 l0 + mu * ucl * c0 + mu * ull * l0) l0 := by
  unfold rmLagrangian
  have h1 := (hu.add_const (β * u c1 l1)).add
    ((((hasDerivAt_id l0).const_mul A0).add_const (A1 * l1 / (1 + r))).sub_const
      (c0 + g0 + (c1 + g1) / (1 + r)) |>.const_mul lam)
  have h2 := (((hucl.mul_const c0).add_const (β * uc c1 l1 * c1)).add
    ((hull.mul (hasDerivAt_id l0)))).add_const (β * ul c1 l1 * l1) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun l => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- AKMM, p. 460, first-order condition in `c₁`: `∂ℒ/∂c₁ = βu_{c,1} − λ/(1 + r) + βµu_{c,1} +
βµu_{cc,1}c₁ + βµu_{ℓc,1}ℓ₁`. -/
theorem rm_foc_c1 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucc ulc : ℝ}
    (hu : HasDerivAt (fun c => u c l1) (uc c1 l1) c1)
    (hucc : HasDerivAt (fun c => uc c l1) ucc c1) (hulc : HasDerivAt (fun c => ul c l1) ulc c1) :
    HasDerivAt (fun c => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c0 l0 c l1)
      (β * uc c1 l1 - lam / (1 + r) + β * mu * uc c1 l1 + β * mu * ucc * c1 +
        β * mu * ulc * l1) c1 := by
  unfold rmLagrangian
  have h1 := ((hu.const_mul β).const_add (u c0 l0)).add
    ((((hasDerivAt_id c1).add_const g1).div_const (1 + r)).const_sub
      (A0 * l0 + A1 * l1 / (1 + r) - c0 - g0) |>.const_mul lam)
  have h2 := ((((hucc.mul (hasDerivAt_id c1)).const_mul β).const_add (uc c0 l0 * c0)).add
    ((hulc.mul_const l1).const_mul β)).const_add (ul c0 l0 * l0) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- AKMM, p. 460, first-order condition in `ℓ₁`: `∂ℒ/∂ℓ₁ = βu_{ℓ,1} + λA₁/(1 + r) + βµu_{ℓ,1} +
βµu_{cℓ,1}c₁ + βµu_{ℓℓ,1}ℓ₁`. -/
theorem rm_foc_l1 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucl ull : ℝ}
    (hu : HasDerivAt (fun l => u c1 l) (ul c1 l1) l1)
    (hucl : HasDerivAt (fun l => uc c1 l) ucl l1) (hull : HasDerivAt (fun l => ul c1 l) ull l1) :
    HasDerivAt (fun l => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c0 l0 c1 l)
      (β * ul c1 l1 + lam * A1 / (1 + r) + β * mu * ul c1 l1 + β * mu * ucl * c1 +
        β * mu * ull * l1) l1 := by
  unfold rmLagrangian
  have h1 := ((hu.const_mul β).const_add (u c0 l0)).add
    (((((hasDerivAt_id l1).const_mul A1).div_const (1 + r)).const_add (A0 * l0)).sub_const
      (c0 + g0 + (c1 + g1) / (1 + r)) |>.const_mul lam)
  have h2 := ((((hucl.mul_const c1).const_mul β).const_add (uc c0 l0 * c0)).add
    ((hull.mul (hasDerivAt_id l1)).const_mul β)).const_add (ul c0 l0 * l0) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun l => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- Separable CRRA utility `c^{1−σ}/(1 − σ) − ℓ^{1+1/φ}/(1 + 1/φ)` (AKMM, p. 460). -/
noncomputable def rmU (σ φ c l : ℝ) : ℝ := c ^ (1 - σ) / (1 - σ) - l ^ (1 + 1 / φ) / (1 + 1 / φ)

/-- Its marginal utility of consumption `u_c = c^{−σ}`. -/
noncomputable def rmUc (σ : ℝ) (c _l : ℝ) : ℝ := c ^ (-σ)

/-- Its marginal utility of hours `u_ℓ = −ℓ^{1/φ}`. -/
noncomputable def rmUl (φ : ℝ) (_c l : ℝ) : ℝ := -l ^ (1 / φ)

/-- AKMM, p. 460: for separable CRRA at `c, ℓ > 0` (`σ ≠ 1`, `φ > 0`): `u_c = c^{−σ}`,
`u_ℓ = −ℓ^{1/φ}`, `u_{cc}c = −σu_c`, `u_{ℓℓ}ℓ = u_ℓ/φ`, and the cross derivatives vanish. -/
theorem rm_crra_derivs {σ φ c l : ℝ} (hσ : σ ≠ 1) (hφ : 0 < φ) (hc : 0 < c) (hl : 0 < l) :
    HasDerivAt (fun c => rmU σ φ c l) (rmUc σ c l) c ∧
      HasDerivAt (fun l => rmU σ φ c l) (rmUl φ c l) l ∧
      HasDerivAt (fun c => rmUc σ c l) (-σ * rmUc σ c l / c) c ∧
      HasDerivAt (fun l => rmUl φ c l) (rmUl φ c l / φ / l) l ∧
      HasDerivAt (fun l => rmUc σ c l) 0 l ∧ HasDerivAt (fun c => rmUl φ c l) 0 c := by
  have h1σ : (1 - σ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  have hp : (1 + 1 / φ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_, hasDerivAt_const _ _, hasDerivAt_const _ _⟩
  · have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).div_const
      (1 - σ)).sub_const (l ^ (1 + 1 / φ) / (1 + 1 / φ))
    refine h.congr_deriv ?_
    unfold rmUc
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  · have h := ((Real.hasDerivAt_rpow_const (p := 1 + 1 / φ) (Or.inl hl.ne')).div_const
      (1 + 1 / φ)).const_sub (c ^ (1 - σ) / (1 - σ))
    refine h.congr_deriv ?_
    unfold rmUl
    rw [show 1 + 1 / φ - 1 = 1 / φ by ring]
    field_simp
  · have h := Real.hasDerivAt_rpow_const (p := -σ) (x := c) (Or.inl hc.ne')
    refine h.congr_deriv ?_
    unfold rmUc
    rw [Real.rpow_sub_one hc.ne']
    ring
  · have h := (Real.hasDerivAt_rpow_const (p := 1 / φ) (x := l) (Or.inl hl.ne')).neg
    refine h.congr_deriv ?_
    unfold rmUl
    rw [Real.rpow_sub_one hl.ne']
    ring

/-- AKMM, p. 460: with `u_{cc,t}c_t = −σu_{c,t}`, `u_{ℓℓ,t}ℓ_t = u_{ℓ,t}/φ` and no cross terms,
the four first-order conditions become `u_{c,0}(1 + µ − µσ) = λ`,
`u_{ℓ,0}(1 + µ + µ/φ) = −λA₀`, `βu_{c,1}(1 + µ − µσ) = λ/(1 + r)` and
`βu_{ℓ,1}(1 + µ + µ/φ) = −λA₁/(1 + r)`. -/
theorem rm_crra_focs {β A0 A1 r lam mu σ φ uc0 ul0 uc1 ul1 ucc0c0 ull0l0 ucc1c1 ull1l1 : ℝ}
    (hc0 : ucc0c0 = -σ * uc0) (hl0 : ull0l0 = ul0 / φ) (hc1 : ucc1c1 = -σ * uc1)
    (hl1 : ull1l1 = ul1 / φ)
    (f1 : uc0 - lam + mu * uc0 + mu * ucc0c0 + mu * 0 = 0)
    (f2 : ul0 + lam * A0 + mu * ul0 + mu * 0 + mu * ull0l0 = 0)
    (f3 : β * uc1 - lam / (1 + r) + β * mu * uc1 + β * mu * ucc1c1 + β * mu * 0 = 0)
    (f4 : β * ul1 + lam * A1 / (1 + r) + β * mu * ul1 + β * mu * 0 + β * mu * ull1l1 = 0) :
    uc0 * (1 + mu - mu * σ) = lam ∧ ul0 * (1 + mu + mu / φ) = -lam * A0 ∧
      β * uc1 * (1 + mu - mu * σ) = lam / (1 + r) ∧
      β * ul1 * (1 + mu + mu / φ) = -(lam * A1 / (1 + r)) := by
  subst hc0 hl0 hc1 hl1
  refine ⟨by linear_combination f1, by linear_combination f2, by linear_combination f3,
    by linear_combination f4⟩

/-- AKMM, p. 460: "Comparing the first and the third, it is immediate that, at an optimum
`β(1 + r)u_{c,1} = u_{c,0}`" (for `1 + µ − µσ ≠ 0`). -/
theorem rm_crra_euler {β r lam mu σ uc0 uc1 : ℝ} (hr : 1 + r ≠ 0) (hN : 1 + mu - mu * σ ≠ 0)
    (f1 : uc0 * (1 + mu - mu * σ) = lam) (f3 : β * uc1 * (1 + mu - mu * σ) = lam / (1 + r)) :
    β * (1 + r) * uc1 = uc0 := by
  have e : β * uc1 * (1 + mu - mu * σ) * (1 + r) = lam := by
    rw [f3]
    field_simp
  have : (β * (1 + r) * uc1 - uc0) * (1 + mu - mu * σ) = 0 := by
    linear_combination e - f1
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hN

/-- AKMM, p. 460: "Comparing the first and the second, … `u_{c,0}A₀(1 + µ − µσ)/(1 + µ + µ/φ) =
−u_{ℓ,0}`"; similarly the third and fourth give the date-1 condition (for `1 + µ + µ/φ ≠ 0`,
`1 + r ≠ 0`, `β ≠ 0`). -/
theorem rm_crra_labour {β A0 A1 r lam mu σ φ uc0 ul0 uc1 ul1 : ℝ} (hβ : β ≠ 0)
    (hD : 1 + mu + mu / φ ≠ 0)
    (f1 : uc0 * (1 + mu - mu * σ) = lam) (f2 : ul0 * (1 + mu + mu / φ) = -lam * A0)
    (f3 : β * uc1 * (1 + mu - mu * σ) = lam / (1 + r))
    (f4 : β * ul1 * (1 + mu + mu / φ) = -(lam * A1 / (1 + r))) :
    uc0 * A0 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul0 ∧
      uc1 * A1 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul1 := by
  constructor
  · field_simp
    linear_combination A0 * f1 + f2
  · have : β * (uc1 * A1 * (1 + mu - mu * σ) + ul1 * (1 + mu + mu / φ)) = 0 := by
      have e1 : β * uc1 * (1 + mu - mu * σ) * A1 = lam / (1 + r) * A1 := by rw [f3]
      have e2 : lam / (1 + r) * A1 = lam * A1 / (1 + r) := by ring
      linear_combination e1 + f4 - e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hβ
    · field_simp
      linear_combination h

/-- **The Ramsey taxes** (AKMM, p. 461): if the Ramsey allocation satisfies the household's
conditions (15.16) for the plan `(τ₀, τ₁, τ_{b,1})` and the CRRA conclusions
`β(1 + r)u_{c,1} = u_{c,0}`, `u_{c,t}A_t(1 + µ − µσ)/(1 + µ + µ/φ) = −u_{ℓ,t}`, then
`τ_{b,1} = 0` and `τ₀ = τ₁ = 1 − (1 + µ − µσ)/(1 + µ + µ/φ) = µ(σ + 1/φ)/(1 + µ + µ/φ)`
(for `r, β ≠ 0`, `u_{c,t}A_t ≠ 0`, `1 + µ + µ/φ ≠ 0`). -/
theorem rm_ramsey_taxes {β A0 A1 r mu σ φ uc0 ul0 uc1 ul1 τ0 τ1 τb : ℝ} (hr : r ≠ 0)
    (hβ : β ≠ 0) (h0 : uc0 * A0 ≠ 0) (h1 : uc1 * A1 ≠ 0) (huc1 : uc1 ≠ 0)
    (hD : 1 + mu + mu / φ ≠ 0)
    (e0 : uc0 * A0 * (1 - τ0) = -ul0) (e1 : uc1 * A1 * (1 - τ1) = -ul1)
    (eb : uc0 = β * (1 + r * (1 - τb)) * uc1) (eR : β * (1 + r) * uc1 = uc0)
    (l0 : uc0 * A0 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul0)
    (l1 : uc1 * A1 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul1) :
    τb = 0 ∧ τ0 = mu * (σ + 1 / φ) / (1 + mu + mu / φ) ∧
      τ1 = mu * (σ + 1 / φ) / (1 + mu + mu / φ) ∧
      1 - (1 + mu - mu * σ) / (1 + mu + mu / φ) = mu * (σ + 1 / φ) / (1 + mu + mu / φ) := by
  have hform : 1 - (1 + mu - mu * σ) / (1 + mu + mu / φ) =
      mu * (σ + 1 / φ) / (1 + mu + mu / φ) := by
    rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    ring
  refine ⟨?_, ?_, ?_, hform⟩
  · have : β * uc1 * (r * τb) = 0 := by linear_combination eR + eb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hβ huc1)
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr
      · exact h'
  · rw [← hform]
    have : uc0 * A0 * ((1 - τ0) - (1 + mu - mu * σ) / (1 + mu + mu / φ)) = 0 := by
      linear_combination e0 - l0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · linarith
  · rw [← hform]
    have : uc1 * A1 * ((1 - τ1) - (1 + mu - mu * σ) / (1 + mu + mu / φ)) = 0 := by
      linear_combination e1 - l1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h1
    · linarith

/-- AKMM, p. 461: "the labor tax rate … will be positive as long as either `g₀` or `g₁` is
strictly positive": with `τ_{b,1} = 0` and `τ₀ = τ₁ = τ`, the government budgets give
`g₀ + g₁/(1 + r) = τ(A₀ℓ₀ + A₁ℓ₁/(1 + r))`, so if the present value of output is positive,
`τ > 0` iff the present value of spending is positive (`1 + r > 0`). -/
theorem rm_tax_pos {A0 A1 r g0 g1 l0 l1 τ b0 bg0 : ℝ} (hr : 0 < 1 + r)
    (hg0 : g0 + bg0 = τ * A0 * l0) (hg1 : g1 = τ * A1 * l1 + 0 * r * b0 + (1 + r) * bg0)
    (hY : 0 < A0 * l0 + A1 * l1 / (1 + r)) :
    g0 + g1 / (1 + r) = τ * (A0 * l0 + A1 * l1 / (1 + r)) ∧
      (0 < g0 + g1 / (1 + r) ↔ 0 < τ) := by
  have hpv : g0 + g1 / (1 + r) = τ * (A0 * l0 + A1 * l1 / (1 + r)) := by
    rw [hg1]
    field_simp
    linear_combination (1 + r) * hg0
  refine ⟨hpv, ?_⟩
  rw [hpv]
  exact ⟨fun h => pos_of_mul_pos_left h hY.le, fun h => mul_pos h hY⟩

/-- AKMM, p. 461, the sign of the multiplier: if the Ramsey tax
`τ = µ(σ + 1/φ)/(1 + µ + µ/φ)` lies in `(0, 1)` (positive by `rm_tax_pos`, below one by (15.16)
with `u_c > 0 > u_ℓ`), with `σ + 1/φ > 0`, then `µ ≠ 0`, and `µ > 0` if `1 + µ + µ/φ > 0` or
`σ ≥ 1`. -/
theorem rm_mu_pos {mu σ φ τ : ℝ} (hs : 0 < σ + 1 / φ) (hD : 1 + mu + mu / φ ≠ 0)
    (hτ : τ = mu * (σ + 1 / φ) / (1 + mu + mu / φ)) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    mu ≠ 0 ∧ (0 < 1 + mu + mu / φ ∨ 1 ≤ σ → 0 < mu) := by
  have hne : mu ≠ 0 := by
    rintro rfl
    rw [hτ] at hτ0
    simp at hτ0
  refine ⟨hne, ?_⟩
  rintro (hDpos | hσ)
  · rw [hτ, lt_div_iff₀ hDpos, zero_mul] at hτ0
    exact pos_of_mul_pos_left hτ0 hs.le
  · by_contra hmu
    push Not at hmu
    have hmu' : mu < 0 := lt_of_le_of_ne hmu hne
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    · -- `1 − τ = (1 + µ − µσ)/(1 + µ + µ/φ)` and `1 + µ − µσ ≥ 1`
      have h1 : 1 - τ = (1 + mu - mu * σ) / (1 + mu + mu / φ) := by
        rw [hτ, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
        ring
      have hN : 1 ≤ 1 + mu - mu * σ := by nlinarith
      have : (1 + mu - mu * σ) / (1 + mu + mu / φ) < 0 := div_neg_of_pos_of_neg (by linarith) hDneg
      linarith
    · rw [hτ, lt_div_iff₀ hDpos, zero_mul] at hτ0
      have : mu * (σ + 1 / φ) < 0 := mul_neg_of_neg_of_pos hmu' hs
      linarith

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Time consistency of the Ramsey plan

AKMM, §15.5.2, pp. 461–462.

* "One parameter configuration that would deliver [saving] is `β(1 + r) = 1` … and `A₀ > A₁`": with
  CRRA the Ramsey Euler equation gives `c₀ = c₁` (`tc_cons_equal`); the Ramsey labour condition
  gives `A₀ℓ₀ > A₁ℓ₁` (`tc_output_order`); and then the household saves,
  `b₀ = (1 − τ)(A₀ℓ₀ − A₁ℓ₁)/(2 + r) > 0` (`tc_saves`).
* Re-optimisation at date 1, with the household's wealth `b₀` and the government's `b_{g,0}`
  given. Every date-1 competitive equilibrium lies on the resource line
  `c = A₁ℓ + (1 + r)(b₀ + b_{g,0}) − g₁` (`tc_ce_on_line`). Setting `τ₁ = 0` and
  `τ_{b,1} = (g₁ − (1 + r)b_{g,0})/(rb₀)` balances the budget and makes the household's budget line
  that resource line (`tc_household_line`): the tax on income from wealth is lump-sum. A
  maximiser on the line satisfies `−u_ℓ = A₁u_c` (`tc_foc_on_line`). So if the Ramsey plan has
  `τ₁ ≠ 0`, its date-1 allocation is strictly worse than what the re-optimising planner obtains
  with `τ₁ = 0` (`tc_time_inconsistent`): the plan is time inconsistent.

Correction: p. 461 says "household wealth `b₁` is already determined"; in the two-period model the
wealth carried into date 1 is `b₀`.
-/

namespace AKMM.FiscalPolicy

/-- AKMM, p. 461: with `β(1 + r) = 1`, the Ramsey Euler equation `β(1 + r)u_{c,1} = u_{c,0}` with
`u_c = c^{−σ}` (`σ > 0`) gives `c₀ = c₁`. -/
theorem tc_cons_equal {β r σ c0 c1 : ℝ} (hσ : 0 < σ) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (hβr : β * (1 + r) = 1) (hE : β * (1 + r) * c1 ^ (-σ) = c0 ^ (-σ)) : c0 = c1 := by
  rw [hβr, one_mul] at hE
  have key : ∀ c : ℝ, 0 < c → (c ^ (-σ)) ^ (-(1 / σ)) = c := fun c hc => by
    rw [← Real.rpow_mul hc.le, show -σ * -(1 / σ) = 1 by field_simp, Real.rpow_one]
  rw [← key c0 hc0, ← key c1 hc1, hE]

/-- AKMM, p. 461: with `c₀ = c₁` (so `u_{c,0} = u_{c,1} = q > 0`), the Ramsey labour condition
`ℓ_t^{1/φ} = qA_tκ` (`κ = (1 + µ − µσ)/(1 + µ + µ/φ) > 0`) and `A₀ > A₁ > 0` give
`A₀ℓ₀ > A₁ℓ₁`. -/
theorem tc_output_order {φ q κ A0 A1 l0 l1 : ℝ} (hφ : 0 < φ) (hq : 0 < q) (hκ : 0 < κ)
    (hA1 : 0 < A1) (hA : A1 < A0) (hl0 : 0 < l0) (hl1 : 0 < l1)
    (h0 : l0 ^ (1 / φ) = q * A0 * κ) (h1 : l1 ^ (1 / φ) = q * A1 * κ) : A1 * l1 < A0 * l0 := by
  have key : ∀ l : ℝ, 0 < l → (l ^ (1 / φ)) ^ φ = l := fun l hl => by
    rw [← Real.rpow_mul hl.le, one_div_mul_cancel hφ.ne', Real.rpow_one]
  have hlt : l1 < l0 := by
    rw [← key l0 hl0, ← key l1 hl1, h0, h1]
    exact Real.rpow_lt_rpow (by positivity)
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hA hq) hκ) hφ
  exact mul_lt_mul hA hlt.le hl1 (by linarith)

/-- AKMM, p. 461: "the household saves in period 0": with `c₀ = c₁`, `τ_{b,1} = 0`,
`τ₀ = τ₁ = τ < 1`, `2 + r > 0` and the household budgets, `b₀ = (1 − τ)(A₀ℓ₀ − A₁ℓ₁)/(2 + r)`,
positive when `A₀ℓ₀ > A₁ℓ₁`. -/
theorem tc_saves {A0 A1 r τ c0 c1 l0 l1 b0 : ℝ} (hr : 0 < 2 + r) (hτ : τ < 1)
    (hc : c0 = c1) (h0 : c0 = (1 - τ) * A0 * l0 - b0)
    (h1 : c1 = (1 - τ) * A1 * l1 + (1 + r * (1 - 0)) * b0) :
    b0 = (1 - τ) * (A0 * l0 - A1 * l1) / (2 + r) ∧ (A1 * l1 < A0 * l0 → 0 < b0) := by
  have hb : b0 = (1 - τ) * (A0 * l0 - A1 * l1) / (2 + r) := by
    rw [eq_div_iff hr.ne']
    linear_combination h0 - h1 - hc
  refine ⟨hb, fun h => ?_⟩
  rw [hb]
  exact div_pos (mul_pos (by linarith) (by linarith)) hr

/-- AKMM, p. 461: at date 1, with `b₀`, `b_{g,0}` given, any household budget
`c = (1 − τ₁)A₁ℓ + (1 + r(1 − τ_{b,1}))b₀` and government budget
`g₁ = τ₁A₁ℓ + τ_{b,1}rb₀ + (1 + r)b_{g,0}` put the allocation on the resource line
`c = A₁ℓ + (1 + r)(b₀ + b_{g,0}) − g₁`. -/
theorem tc_ce_on_line {A1 r g1 b0 bg0 τ1 τb c l : ℝ}
    (hh : c = (1 - τ1) * A1 * l + (1 + r * (1 - τb)) * b0)
    (hg : g1 = τ1 * A1 * l + τb * r * b0 + (1 + r) * bg0) :
    c = A1 * l + ((1 + r) * (b0 + bg0) - g1) := by
  rw [hh, hg]
  ring

/-- AKMM, p. 461: "such a planner would set `τ₁ = 0` and `τ_{b,1}` as high as necessary to fund
required government purchases": with `rb₀ ≠ 0`, `τ_{b,1} = (g₁ − (1 + r)b_{g,0})/(rb₀)` balances
the date-1 budget with `τ₁ = 0`, and the household's date-1 budget line is then exactly the
resource line (the wealth tax is lump-sum). -/
theorem tc_household_line {A1 r g1 b0 bg0 : ℝ} (hrb : r * b0 ≠ 0) :
    g1 = 0 * A1 * 1 + (g1 - (1 + r) * bg0) / (r * b0) * r * b0 + (1 + r) * bg0 ∧
      ∀ c l : ℝ, c = (1 - 0) * A1 * l + (1 + r * (1 - (g1 - (1 + r) * bg0) / (r * b0))) * b0 ↔
        c = A1 * l + ((1 + r) * (b0 + bg0) - g1) := by
  have hb : b0 ≠ 0 := right_ne_zero_of_mul hrb
  have hr : r ≠ 0 := left_ne_zero_of_mul hrb
  constructor
  · field_simp
    ring
  · intro c l
    have : (1 - 0) * A1 * l + (1 + r * (1 - (g1 - (1 + r) * bg0) / (r * b0))) * b0 =
        A1 * l + ((1 + r) * (b0 + bg0) - g1) := by
      field_simp
      ring
    rw [this]

/-- AKMM, p. 461: a maximiser of `u` on the resource line `c = A₁ℓ + M`, at which `u` is
differentiable, satisfies the undistorted condition `−u_ℓ = A₁u_c`. -/
theorem tc_foc_on_line {u : ℝ → ℝ → ℝ} {A1 M c l uc ul : ℝ} (hcl : c = A1 * l + M)
    (hmax : ∀ c' l', c' = A1 * l' + M → u c' l' ≤ u c l) (hu : DTPartials u c l uc ul) :
    -ul = A1 * uc := by
  have hd := dt_curve_hasDerivAt (h := fun ε => A1 * ε) (g := fun ε => ε) hu
    ((hasDerivAt_id 0).const_mul A1) (hasDerivAt_id 0) (by simp) rfl
  have hloc : IsLocalMax (fun ε => u (c + A1 * ε) (l + ε)) 0 :=
    Filter.Eventually.of_forall fun ε => by
      simp only [mul_zero, add_zero]
      exact hmax _ _ (by rw [hcl]; ring)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **Time inconsistency** (AKMM, p. 461): if the Ramsey plan has `τ₁ ≠ 0`, its date-1 allocation
`(c₁, ℓ₁)` (on the resource line, with the household condition `u_{c,1}A₁(1 − τ₁) = −u_{ℓ,1}`,
`u_{c,1}, A₁ ≠ 0`, `u` differentiable there) is strictly worse than the household's optimum
`(c*, ℓ*)` under the re-optimised plan `τ₁ = 0` (whose budget line is the resource line). -/
theorem tc_time_inconsistent {u : ℝ → ℝ → ℝ} {A1 M c1 l1 uc1 ul1 τ1 cs ls : ℝ}
    (hline : c1 = A1 * l1 + M) (hfoc : uc1 * A1 * (1 - τ1) = -ul1) (hτ : τ1 ≠ 0)
    (huc : uc1 ≠ 0) (hA : A1 ≠ 0) (hu : DTPartials u c1 l1 uc1 ul1)
    (hopt : ∀ c l, c = A1 * l + M → u c l ≤ u cs ls) : u c1 l1 < u cs ls := by
  rcases (hopt c1 l1 hline).lt_or_eq with h | h
  · exact h
  · exfalso
    have hmax : ∀ c' l', c' = A1 * l' + M → u c' l' ≤ u c1 l1 := fun c' l' hc' => by
      rw [h]
      exact hopt c' l' hc'
    have := tc_foc_on_line hline hmax hu
    have h0 : uc1 * A1 * τ1 = 0 := by linear_combination -hfoc - this
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact mul_ne_zero huc hA h'
    · exact hτ h'

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Debt and pensions with overlapping generations

AKMM, §15.6, (15.19)–(15.24), pp. 462–463, footnote 10.

A small open two-period OLG economy with exogenous `r`: cohorts `N_t = (1 + n)^t`, only the
young work, earning `y_t = (1 + γ)^tω`; PAYG pensions financed by the tax `τ_p`, public goods
`G_t = gY_t`, a flat tax `τ_t` and one-period debt.

* The young share `N_t/(N_t + N_{t−1}) = (1 + n)/(2 + n)` (`olg_young_share`); the balanced PAYG
  pension `p_t = (1 + n)τ_py_t` (`olg_pension`); the budget in ratios
  `g + (1 + r)b_{t−1}/((1 + n)(1 + γ)) = τ_t + b_t` (`olg_budget_ratio`).
* (15.21): the flow budgets (15.19)–(15.20) hold for some saving iff the lifetime budget holds
  (`eq_15_21`); (15.22): the Euler equation at an interior optimum (`eq_15_22`); with log utility
  `c_y = W/(1 + β)`, `c_o = β(1 + r)W/(1 + β)` (`olg_log_consumption`).
* **PAYG is implicit debt** (15.23)–(15.24): with `b_{p,t} = τ_py_t` and
  `1 + r_p = (1 + n)(1 + γ)` the two budget sets coincide (`olg_payg_eq_debt`).
* The present value of the young's income rises with `τ_p` iff `(1 + n)(1 + γ) > 1 + r`
  (`olg_pv_hasDerivAt`, `olg_pv_increasing_iff`). The book's "iff `γ + n > r`" uses
  `(1 + n)(1 + γ) ≈ 1 + n + γ` and is not exact (`olg_pv_approx_false`).
* **Pareto improvement under dynamic inefficiency**: if `(1 + n)(1 + γ) > 1 + r`, introducing
  `τ_p > 0` gives the initial old a positive pension and strictly enlarges every young cohort's
  budget set (`olg_payg_pareto`); if `(1 + n)(1 + γ) < 1 + r` it strictly shrinks it
  (`olg_payg_tax_on_young`).
* **The tax holiday** (zero initial debt, `τ_t = 0`, `B_t = gY_t`, repaid at `t + 1`): debt ratio
  `b_t = g` and `τ_{t+1} = g(1 + (1 + r)/((1 + n)(1 + γ)))` (`olg_holiday_taxes`); with log
  utility generation `t` consumes more in both periods and generation `t + 1` less; so aggregate
  consumption rises at `t` and falls at `t + 2` (`olg_holiday_aggregate`).

Departures: §15.6 is a small open economy; the closed-economy dynamic-inefficiency results of the
`OverlappingGenerations` dependency (Miao Ch. 16) have a different model and are not used. The
aggregate-consumption claims are proved for log utility (consumption proportional to lifetime
income); the book argues for general utility.
-/

namespace AKMM.FiscalPolicy

/-- AKMM, p. 462: with `N_t = (1 + n)^t`, the young share is `N_t/(N_t + N_{t−1}) = (1 + n)/(2 + n)`
(`n > −1`). -/
theorem olg_young_share {n : ℝ} (hn : -1 < n) (t : ℕ) :
    (1 + n) ^ (t + 1) / ((1 + n) ^ (t + 1) + (1 + n) ^ t) = (1 + n) / (2 + n) := by
  have h1 : 0 < 1 + n := by linarith
  have hp : 0 < (1 + n) ^ t := pow_pos h1 t
  rw [div_eq_div_iff (by positivity) (by linarith), pow_succ]
  ring

/-- AKMM, p. 462: a balanced PAYG system `p_tN_{t−1} = τ_py_tN_t` with `N_t = (1 + n)N_{t−1}` pays
`p_t = (1 + n)τ_py_t`. -/
theorem olg_pension {n τp yt Nm pt : ℝ} (hN : Nm ≠ 0) (h : pt * Nm = τp * yt * ((1 + n) * Nm)) :
    pt = (1 + n) * τp * yt := by
  have := mul_right_cancel₀ hN (show pt * Nm = (1 + n) * τp * yt * Nm by rw [h]; ring)
  exact this

/-- AKMM, p. 462: dividing the budget `G_t + p_tN_{t−1} + (1 + r)B_{t−1} = (τ_p + τ_t)Y_t + B_t` by
`Y_t = (1 + n)(1 + γ)Y_{t−1}`, with `G_t = gY_t` and the pension self-financing
(`p_tN_{t−1} = τ_pY_t`), gives `g + (1 + r)b_{t−1}/((1 + n)(1 + γ)) = τ_t + b_t`. -/
theorem olg_budget_ratio {g r n γ τp τt Ym Bm B P : ℝ} (hY : Ym ≠ 0)
    (hng : (1 + n) * (1 + γ) ≠ 0) (hP : P = τp * ((1 + n) * (1 + γ) * Ym))
    (h : g * ((1 + n) * (1 + γ) * Ym) + P + (1 + r) * Bm =
      (τp + τt) * ((1 + n) * (1 + γ) * Ym) + B) :
    g + (1 + r) / ((1 + n) * (1 + γ)) * (Bm / Ym) = τt + B / ((1 + n) * (1 + γ) * Ym) := by
  rw [hP] at h
  have hn1 : 1 + n ≠ 0 := left_ne_zero_of_mul hng
  have hγ1 : 1 + γ ≠ 0 := right_ne_zero_of_mul hng
  have key : g * ((1 + n) * (1 + γ) * Ym) + (1 + r) * Bm =
      τt * ((1 + n) * (1 + γ) * Ym) + B := by linarith
  have e1 : g + (1 + r) / ((1 + n) * (1 + γ)) * (Bm / Ym) =
      (g * ((1 + n) * (1 + γ) * Ym) + (1 + r) * Bm) / ((1 + n) * (1 + γ) * Ym) := by
    field_simp
  have e2 : τt + B / ((1 + n) * (1 + γ) * Ym) =
      (τt * ((1 + n) * (1 + γ) * Ym) + B) / ((1 + n) * (1 + γ) * Ym) := by
    field_simp
  rw [e1, e2, key]

/-- **(15.21)** (AKMM, p. 462): the budgets (15.19) `c_y + a = (1 − τ_t − τ_p)y_t` and (15.20)
`c_o = (1 + r)a + p_{t+1}` with `p_{t+1} = (1 + n)(1 + γ)τ_py_t` hold for some saving `a` iff
`c_y + c_o/(1 + r) = (1 − τ_t − τ_p + (1 + n)(1 + γ)τ_p/(1 + r))y_t`. -/
theorem eq_15_21 {r n γ τt τp yt cy co : ℝ} (hr : 1 + r ≠ 0) :
    (∃ a, cy + a = (1 - τt - τp) * yt ∧ co = (1 + r) * a + (1 + n) * (1 + γ) * τp * yt) ↔
      cy + co / (1 + r) = (1 - τt - τp + (1 + n) * (1 + γ) / (1 + r) * τp) * yt := by
  constructor
  · rintro ⟨a, h1, h2⟩
    rw [h2]
    field_simp
    linear_combination (1 + r) * h1
  · intro h
    refine ⟨(1 - τt - τp) * yt - cy, by ring, ?_⟩
    field_simp at h
    linear_combination h

/-- **(15.22)** (AKMM, p. 463): if `c_y` maximises `u(c_y) + βu((1 + r)(W − c_y))` (the lifetime
budget (15.21) with wealth `W`) and `u` is differentiable at `c_y` and `c_o = (1 + r)(W − c_y)` with
`u′(c_y) ≠ 0`, then `1 = (1 + r)βu′(c_o)/u′(c_y)`. -/
theorem eq_15_22 {u : ℝ → ℝ} {β r W cy u'y u'o : ℝ} (hu'y : u'y ≠ 0)
    (hmax : ∀ c, u c + β * u ((1 + r) * (W - c)) ≤ u cy + β * u ((1 + r) * (W - cy)))
    (hy : HasDerivAt u u'y cy) (ho : HasDerivAt u u'o ((1 + r) * (W - cy))) :
    1 = (1 + r) * β * u'o / u'y := by
  have hin : HasDerivAt (fun c => (1 + r) * (W - c)) ((1 + r) * (0 - 1)) cy :=
    ((hasDerivAt_const cy W).sub (hasDerivAt_id cy)).const_mul (1 + r)
  have hd := hy.add ((ho.comp cy hin).const_mul β)
  have hloc : IsLocalMax (fun c => u c + β * u ((1 + r) * (W - c))) cy :=
    Filter.Eventually.of_forall hmax
  have := hloc.hasDerivAt_eq_zero hd
  field_simp
  linear_combination this

/-- AKMM, p. 463, with log utility: the Euler equation (15.22) and the lifetime budget give
`c_y = W/(1 + β)` and `c_o = β(1 + r)W/(1 + β)` (`β > 0`, `c_y > 0`). -/
theorem olg_log_consumption {β r W cy co : ℝ} (hβ : 0 < β) (hcy : cy ≠ 0) (hco : co ≠ 0)
    (hr : 1 + r ≠ 0) (hE : 1 = (1 + r) * β * (1 / co) / (1 / cy)) (hW : cy + co / (1 + r) = W) :
    cy = W / (1 + β) ∧ co = β * (1 + r) * W / (1 + β) := by
  have hco' : co = β * (1 + r) * cy := by
    field_simp at hE
    linarith
  have h1β : (1 + β) ≠ 0 := by linarith
  rw [hco'] at hW
  field_simp at hW
  constructor
  · rw [← hW]
    field_simp
  · rw [hco', ← hW]
    field_simp

/-- **PAYG is implicit debt** (AKMM, p. 463): with forced bond purchases `b_{p,t} = τ_py_t` at
`1 + r_p = (1 + n)(1 + γ)`, the budgets (15.23)–(15.24) are equivalent to (15.19)–(15.20). -/
theorem olg_payg_eq_debt {r n γ τt τp yt cy a co : ℝ} :
    (cy + a = (1 - τt - τp) * yt ∧ co = (1 + r) * a + (1 + n) * (1 + γ) * τp * yt) ↔
      (cy + a + τp * yt = (1 - τt) * yt ∧ co = (1 + r) * a + (1 + n) * (1 + γ) * (τp * yt)) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by linarith, by rw [h2]; ring⟩

/-- The present value of the young's lifetime income (the right side of (15.21)). -/
noncomputable def olgPV (r n γ τt yt τp : ℝ) : ℝ :=
  (1 - τt - τp + (1 + n) * (1 + γ) / (1 + r) * τp) * yt

/-- AKMM, p. 463: `∂/∂τ_p` of the right side of (15.21) is `((1 + n)(1 + γ)/(1 + r) − 1)y_t`. -/
theorem olg_pv_hasDerivAt {r n γ τt yt τp : ℝ} :
    HasDerivAt (olgPV r n γ τt yt) (((1 + n) * (1 + γ) / (1 + r) - 1) * yt) τp := by
  have h := ((hasDerivAt_id τp).mul_const (((1 + n) * (1 + γ) / (1 + r) - 1) * yt)).const_add
    ((1 - τt) * yt)
  refine (h.congr_deriv (one_mul _)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [olgPV, id]
  ring

/-- AKMM, p. 463: "the pension system increases the present value of household income for the
young if and only if wage growth exceeds the interest rate": for `y_t > 0`, `1 + r > 0`, the
derivative is positive iff `(1 + n)(1 + γ) > 1 + r`. -/
theorem olg_pv_increasing_iff {r n γ yt : ℝ} (hy : 0 < yt) (hr : 0 < 1 + r) :
    0 < ((1 + n) * (1 + γ) / (1 + r) - 1) * yt ↔ 1 + r < (1 + n) * (1 + γ) := by
  rw [mul_pos_iff_of_pos_right hy, sub_pos, one_lt_div hr]

/-- AKMM, p. 463: the printed criterion "iff `γ + n > r`" is the approximation
`(1 + n)(1 + γ) ≈ 1 + n + γ`; it is not exact: at `n = γ = 1/10`, `r = 41/200`, the pension raises
the young's present value (`(1 + n)(1 + γ) = 1.21 > 1.205`) although `γ + n = 0.2 < r`. -/
theorem olg_pv_approx_false :
    (1 + (41 / 200 : ℝ)) < (1 + 1 / 10) * (1 + 1 / 10) ∧ (1 / 10 + 1 / 10 : ℝ) < 41 / 200 := by
  constructor <;> norm_num

/-- The young's budget set at pension tax `τ_p`: `c_y + c_o/(1 + r) ≤ PV(τ_p)`. -/
def olgBudgetSet (r n γ τt yt τp : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 + x.2 / (1 + r) ≤ olgPV r n γ τt yt τp}

/-- **Pareto improvement** (AKMM, p. 463): "if the interest rate is lower than the wage growth
rate … introducing a PAYG pension system is Pareto improving": with `(1 + n)(1 + γ) > 1 + r`,
`τ_p > 0`, `y > 0`, the initial old receive a positive pension `(1 + n)τ_py₀` and every young
cohort's budget set strictly grows. -/
theorem olg_payg_pareto {r n γ τt τp y0 : ℝ} (hr : 0 < 1 + r) (hn : -1 < n)
    (hdi : 1 + r < (1 + n) * (1 + γ)) (hτ : 0 < τp) (hy0 : 0 < y0) :
    0 < (1 + n) * τp * y0 ∧
      ∀ yt, 0 < yt → olgBudgetSet r n γ τt yt 0 ⊂ olgBudgetSet r n γ τt yt τp := by
  refine ⟨mul_pos (mul_pos (by linarith) hτ) hy0, fun yt hyt => ?_⟩
  have hgt : olgPV r n γ τt yt 0 < olgPV r n γ τt yt τp := by
    unfold olgPV
    have : 0 < ((1 + n) * (1 + γ) / (1 + r) - 1) * τp * yt :=
      mul_pos (mul_pos (by rw [sub_pos, one_lt_div hr]; exact hdi) hτ) hyt
    nlinarith
  refine ⟨fun x hx => le_trans hx hgt.le, fun hsub => ?_⟩
  have hmem : (olgPV r n γ τt yt τp, (0 : ℝ)) ∈ olgBudgetSet r n γ τt yt τp := by
    simp [olgBudgetSet]
  have := hsub hmem
  simp only [olgBudgetSet, Set.mem_ofPred_eq, zero_div, add_zero] at this
  linarith

/-- AKMM, p. 463: "if the interest rate is larger than the growth rate of output … the pension
system is effectively a tax on the young generation": with `(1 + n)(1 + γ) < 1 + r`, `τ_p > 0`,
`y_t > 0`, the young's budget set strictly shrinks. -/
theorem olg_payg_tax_on_young {r n γ τt τp yt : ℝ} (hr : 0 < 1 + r)
    (hde : (1 + n) * (1 + γ) < 1 + r) (hτ : 0 < τp) (hyt : 0 < yt) :
    olgBudgetSet r n γ τt yt τp ⊂ olgBudgetSet r n γ τt yt 0 := by
  have hlt : olgPV r n γ τt yt τp < olgPV r n γ τt yt 0 := by
    unfold olgPV
    have : ((1 + n) * (1 + γ) / (1 + r) - 1) * τp * yt < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (by rw [sub_neg, div_lt_one hr]; exact hde) hτ) hyt
    nlinarith
  refine ⟨fun x hx => le_trans hx hlt.le, fun hsub => ?_⟩
  have hmem : (olgPV r n γ τt yt 0, (0 : ℝ)) ∈ olgBudgetSet r n γ τt yt 0 := by
    simp [olgBudgetSet]
  have := hsub hmem
  simp only [olgBudgetSet, Set.mem_ofPred_eq, zero_div, add_zero] at this
  linarith

/-- AKMM, p. 463, **the tax holiday**: with zero initial debt, `τ_t = 0` and the deficit financed
by `b_t`, the budget in ratios gives `b_t = g`; repaying at `t + 1` (`b_{t+1} = 0`) requires
`τ_{t+1} = g(1 + (1 + r)/((1 + n)(1 + γ)))`, against `τ = g` without the holiday. -/
theorem olg_holiday_taxes {g r n γ bt τ1 : ℝ}
    (h0 : g + (1 + r) / ((1 + n) * (1 + γ)) * 0 = 0 + bt)
    (h1 : g + (1 + r) / ((1 + n) * (1 + γ)) * bt = τ1 + 0) :
    bt = g ∧ τ1 = g * (1 + (1 + r) / ((1 + n) * (1 + γ))) := by
  have hb : bt = g := by linarith
  refine ⟨hb, ?_⟩
  rw [hb] at h1
  linarith

/-- AKMM, p. 463, **aggregate consumption after the tax holiday** (log utility, consumption
`κ_yW`, `κ_oW` proportional to lifetime income with `κ_y, κ_o > 0`, cohorts `N > 0`): generation
`t` gains lifetime income (its tax falls from `g > 0` to `0`) and generation `t + 1` loses (its tax
rises by `g(1 + r)/((1 + n)(1 + γ)) > 0`); the old at `t` and the young at `t + 2` are unaffected.
Hence `C_t = c_{y,t}N_t + c_{o,t}N_{t−1}` rises and `C_{t+2} = c_{y,t+2}N_{t+2} + c_{o,t+2}N_{t+1}`
falls. -/
theorem olg_holiday_aggregate {κy κo W0 Wt Wt1 W2 g d yt yt1 Nm Nt Nt1 Nt2 : ℝ}
    (hκy : 0 < κy) (hκo : 0 < κo) (hg : 0 < g) (hd : 0 < d) (hyt : 0 < yt) (hyt1 : 0 < yt1)
    (hNt : 0 < Nt) (hNt1 : 0 < Nt1) :
    κy * Wt * Nt + κo * W0 * Nm < κy * (Wt + g * yt) * Nt + κo * W0 * Nm ∧
      κy * W2 * Nt2 + κo * (Wt1 - d * yt1) * Nt1 < κy * W2 * Nt2 + κo * Wt1 * Nt1 := by
  constructor
  · nlinarith [mul_pos (mul_pos (mul_pos hκy hg) hyt) hNt]
  · nlinarith [mul_pos (mul_pos (mul_pos hκo hd) hyt1) hNt1]

end AKMM.FiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Progressivity: the HSV tax and transfer system, and wealth effects

AKMM, §15.7–15.7.1, (15.25)–(15.27), pp. 464–466, and Appendix 15.A.2, p. 869.

* (15.25): `y − T(y) = λy^{1−τ}` (`hsvT`). For `λ, y > 0`, `T′(y) − T(y)/y = λτy^{−τ}`
  (`hsv_marginal_sub_average`), so the system is progressive (`T′ > T/y`) iff `τ > 0`, regressive
  iff `τ < 0`, and flat with `T′ = T/y = 1 − λ` when `τ = 0` (`eq_15_25`).
* The static model: `max log c − ℓ^{1+1/φ}/(1 + 1/φ)` with `c = λ(wℓ)^{1−τ}`. For `τ < 1` the
  unique maximiser over `ℓ > 0` is `ℓ* = (1 − τ)^{1/(1+1/φ)}` (`hsv_hours_optimal`), proved
  globally from `log x ≤ x − 1`; so (15.26) `log ℓ = log(1 − τ)/(1 + 1/φ)` (`eq_15_26`) and
  (15.27) `log c = log λ + (1 − τ)log(1 − τ)/(1 + 1/φ) + (1 − τ)log w` (`eq_15_27`). Hours do not
  depend on `w`, fall with `τ` (`hsv_hours_strictAntiOn`) and vanish as `τ → 1`
  (`hsv_hours_tendsto`).
* `Var(log c) = (1 − τ)²Var(log w)` for any distribution of wages (`hsv_var_log_c`).
* Appendix 15.A.2: with `u = ln c − ℓ^{1+1/φ}/(1 + 1/φ)` and hand-to-mouth workers
  `c_w = ((1 − τ_ℓ)/(1 + τ_c))wℓ`, labour supply is `ℓ = 1` whatever the taxes
  (`app_15_A_2`, `app_15_A_2_foc`).
-/

namespace AKMM.FiscalPolicy

open Real Filter Topology

/-- The HSV net tax `T(y) = y − λy^{1−τ}` (AKMM, (15.25), p. 465). -/
noncomputable def hsvT (lam τ y : ℝ) : ℝ := y - lam * y ^ (1 - τ)

/-- AKMM, p. 465: `T′(y) = 1 − λ(1 − τ)y^{−τ}` at `y > 0`. -/
theorem hsv_hasDerivAt {lam τ y : ℝ} (hy : 0 < y) :
    HasDerivAt (hsvT lam τ) (1 - lam * (1 - τ) * y ^ (-τ)) y := by
  have h := (hasDerivAt_id y).sub
    ((Real.hasDerivAt_rpow_const (p := 1 - τ) (Or.inl hy.ne')).const_mul lam)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)
  rw [show 1 - τ - 1 = -τ by ring]
  ring

/-- AKMM, p. 465: `T′(y) − T(y)/y = λτy^{−τ}` (`y > 0`). -/
theorem hsv_marginal_sub_average {lam τ y : ℝ} (hy : 0 < y) :
    (1 - lam * (1 - τ) * y ^ (-τ)) - hsvT lam τ y / y = lam * τ * y ^ (-τ) := by
  unfold hsvT
  have : y ^ (1 - τ) = y * y ^ (-τ) := by
    rw [show 1 - τ = 1 + -τ by ring, Real.rpow_add hy, Real.rpow_one]
  rw [this]
  field_simp
  ring

/-- **(15.25)** (AKMM, p. 465), for `λ, y > 0`: "when `0 < τ < 1`, the tax system is progressive in
the sense that the marginal tax rate `T′(y)` is larger than the average tax rate `T(y)/y`"
(indeed iff `τ > 0`); "when `τ < 0`, … `T′(y) < T(y)/y`"; "when `τ = 0`, …
`T′(y) = T(y)/y = 1 − λ`". -/
theorem eq_15_25 {lam τ y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    (hsvT lam τ y / y < 1 - lam * (1 - τ) * y ^ (-τ) ↔ 0 < τ) ∧
      (1 - lam * (1 - τ) * y ^ (-τ) < hsvT lam τ y / y ↔ τ < 0) ∧
      (τ = 0 → 1 - lam * (1 - τ) * y ^ (-τ) = 1 - lam ∧ hsvT lam τ y / y = 1 - lam) := by
  have h := hsv_marginal_sub_average (lam := lam) (τ := τ) hy
  have hp : 0 < lam * y ^ (-τ) := mul_pos hlam (Real.rpow_pos_of_pos hy _)
  refine ⟨⟨fun h' => ?_, fun h' => ?_⟩, ⟨fun h' => ?_, fun h' => ?_⟩, fun h0 => ?_⟩
  · have : 0 < lam * τ * y ^ (-τ) := by linarith
    have : 0 < τ * (lam * y ^ (-τ)) := by linarith
    exact pos_of_mul_pos_left this hp.le
  · have : 0 < lam * τ * y ^ (-τ) := by
      have := mul_pos h' hp
      linarith
    linarith
  · have : lam * τ * y ^ (-τ) < 0 := by linarith
    have : τ * (lam * y ^ (-τ)) < 0 := by linarith
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.mpr (mul_nonneg hc hp.le))
  · have : lam * τ * y ^ (-τ) < 0 := by
      have := mul_neg_of_neg_of_pos h' hp
      linarith
    linarith
  · subst h0
    constructor
    · simp
    · unfold hsvT
      simp only [sub_zero, Real.rpow_one]
      field_simp

/-- The worker's utility in the HSV economy as a function of hours (AKMM, p. 466):
`log(λ(wℓ)^{1−τ}) − ℓ^{1+1/φ}/(1 + 1/φ)`. -/
noncomputable def hsvObj (lam τ φ w l : ℝ) : ℝ :=
  Real.log (lam * (w * l) ^ (1 - τ)) - l ^ (1 + 1 / φ) / (1 + 1 / φ)

/-- The optimal hours `ℓ* = (1 − τ)^{1/(1+1/φ)}`. -/
noncomputable def hsvHours (τ φ : ℝ) : ℝ := (1 - τ) ^ (1 / (1 + 1 / φ))

/-- AKMM, p. 466: for `λ, w, φ > 0` and `τ < 1`, `ℓ* = (1 − τ)^{1/(1+1/φ)}` maximises the worker's
utility over `ℓ > 0`, uniquely. -/
theorem hsv_hours_optimal {lam τ φ w : ℝ} (hlam : 0 < lam) (hw : 0 < w) (hφ : 0 < φ)
    (hτ : τ < 1) :
    0 < hsvHours τ φ ∧ ∀ l, 0 < l → l ≠ hsvHours τ φ →
      hsvObj lam τ φ w l < hsvObj lam τ φ w (hsvHours τ φ) := by
  set p := 1 + 1 / φ with hp
  have hp0 : 0 < p := by positivity
  have h1τ : 0 < 1 - τ := by linarith
  have hs : 0 < hsvHours τ φ := Real.rpow_pos_of_pos h1τ _
  refine ⟨hs, fun l hl hne => ?_⟩
  have hsp : hsvHours τ φ ^ p = 1 - τ := by
    unfold hsvHours
    rw [← hp, ← Real.rpow_mul h1τ.le, one_div_mul_cancel hp0.ne', Real.rpow_one]
  -- the objective at `ℓ` equals `log λ + (1 − τ)log w + ((1 − τ)/p)log(ℓ^p) − ℓ^p/p`
  have hform : ∀ x, 0 < x → hsvObj lam τ φ w x =
      Real.log lam + (1 - τ) * Real.log w + (1 - τ) / p * Real.log (x ^ p) - x ^ p / p := by
    intro x hx
    unfold hsvObj
    rw [← hp, Real.log_mul hlam.ne' (Real.rpow_pos_of_pos (mul_pos hw hx) _).ne',
      Real.log_rpow (mul_pos hw hx), Real.log_mul hw.ne' hx.ne', Real.log_rpow hx]
    field_simp
    ring
  rw [hform l hl, hform _ hs, hsp]
  -- with `x = ℓ^p/(1 − τ) ≠ 1`, the gap is `((1 − τ)/p)(log x − (x − 1)) < 0`
  set x := l ^ p / (1 - τ) with hx
  have hx0 : 0 < x := div_pos (Real.rpow_pos_of_pos hl p) h1τ
  have hx1 : x ≠ 1 := by
    intro h1
    apply hne
    have : l ^ p = 1 - τ := by
      rw [hx, div_eq_one_iff_eq h1τ.ne'] at h1
      exact h1
    have key : ∀ z : ℝ, 0 < z → (z ^ p) ^ (1 / p) = z := fun z hz => by
      rw [← Real.rpow_mul hz.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
    rw [← key l hl, this, ← hsp, key _ hs]
  have hlog : Real.log (l ^ p) = Real.log x + Real.log (1 - τ) := by
    rw [hx, Real.log_div (Real.rpow_pos_of_pos hl p).ne' h1τ.ne', sub_add_cancel]
  have hlp : l ^ p = x * (1 - τ) := by
    rw [hx]
    field_simp
  rw [hlog, hlp]
  have hlt := Real.log_lt_sub_one_of_pos hx0 hx1
  have hc : 0 < (1 - τ) / p := div_pos h1τ hp0
  have key : (1 - τ) / p * (Real.log x + Real.log (1 - τ)) - x * (1 - τ) / p -
      ((1 - τ) / p * Real.log (1 - τ) - (1 - τ) / p) =
      (1 - τ) / p * (Real.log x - (x - 1)) := by
    field_simp
    ring
  have : (1 - τ) / p * (Real.log x - (x - 1)) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
  linarith

/-- **(15.26)** (AKMM, p. 466): `log ℓ = log(1 − τ)/(1 + 1/φ)`. -/
theorem eq_15_26 {τ φ : ℝ} (hτ : τ < 1) :
    Real.log (hsvHours τ φ) = Real.log (1 - τ) / (1 + 1 / φ) := by
  unfold hsvHours
  rw [Real.log_rpow (by linarith)]
  ring

/-- **(15.27)** (AKMM, p. 466): `log c = log λ + (1 − τ)log(1 − τ)/(1 + 1/φ) + (1 − τ)log w` at the
optimal hours, with `c = λ(wℓ)^{1−τ}`. -/
theorem eq_15_27 {lam τ φ w : ℝ} (hlam : 0 < lam) (hw : 0 < w) (hτ : τ < 1) :
    Real.log (lam * (w * hsvHours τ φ) ^ (1 - τ)) =
      Real.log lam + (1 - τ) * (Real.log (1 - τ) / (1 + 1 / φ)) + (1 - τ) * Real.log w := by
  have hs : 0 < hsvHours τ φ := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.log_mul hlam.ne' (Real.rpow_pos_of_pos (mul_pos hw hs) _).ne',
    Real.log_rpow (mul_pos hw hs), Real.log_mul hw.ne' hs.ne', eq_15_26 hτ]
  ring

/-- AKMM, p. 466: "Hours worked are falling in `τ`" (on `τ < 1`, `φ > 0`). -/
theorem hsv_hours_strictAntiOn {φ : ℝ} (hφ : 0 < φ) :
    StrictAntiOn (fun τ => hsvHours τ φ) (Set.Iio 1) := by
  intro a _ b hb hab
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  exact Real.rpow_lt_rpow hb'.le (by linarith) (by positivity)

/-- AKMM, p. 466: "In the limit as `τ → 1` … hours will shrink to zero". -/
theorem hsv_hours_tendsto {φ : ℝ} (hφ : 0 < φ) :
    Tendsto (fun τ => hsvHours τ φ) (𝓝[<] 1) (𝓝 0) := by
  have he : 0 < 1 / (1 + 1 / φ) := by positivity
  have h1 : Tendsto (fun τ : ℝ => 1 - τ) (𝓝[<] 1) (𝓝[>] 0) := by
    have hc : Tendsto (fun τ : ℝ => 1 - τ) (𝓝 1) (𝓝 0) := by
      have := (continuous_sub_left (1 : ℝ)).tendsto 1
      simpa using this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact sub_pos.mpr (Set.mem_Iio.mp hτ)
  have h2 : Tendsto (fun x : ℝ => x ^ (1 / (1 + 1 / φ))) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / (1 + 1 / φ)) (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h2.comp h1

/-- AKMM, p. 466: "the variance of log consumption is `(1 − τ)²Var(log w)`": if
`log c_i = a + (1 − τ)log w_i` across individuals (15.27), for any probability distribution of
`i` under which `log w` is a.e. strongly measurable. -/
theorem hsv_var_log_c {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {logw : Ω → ℝ}
    (hX : MeasureTheory.AEStronglyMeasurable logw μ) (a τ : ℝ) :
    ProbabilityTheory.variance (fun i => a + (1 - τ) * logw i) μ =
      (1 - τ) ^ 2 * ProbabilityTheory.variance logw μ := by
  have h := ProbabilityTheory.variance_add_const (hX.const_mul (1 - τ)) a
  rw [← ProbabilityTheory.variance_const_mul]
  rw [← h]
  congr 1
  funext i
  ring

/-- **Appendix 15.A.2** (AKMM, p. 869): with `u = ln c − ℓ^{1+1/φ}/(1 + 1/φ)` and hand-to-mouth
workers `c_w = θwℓ`, `θ = (1 − τ_ℓ)/(1 + τ_c) > 0`, labour supply is `ℓ = 1` whatever the taxes:
`ℓ = 1` is the unique maximiser over `ℓ > 0` (the HSV problem with `τ = 0`, `λ = θ`). -/
theorem app_15_A_2 {θ φ w : ℝ} (hθ : 0 < θ) (hw : 0 < w) (hφ : 0 < φ) :
    ∀ l, 0 < l → l ≠ 1 →
      Real.log (θ * (w * l)) - l ^ (1 + 1 / φ) / (1 + 1 / φ) <
        Real.log (θ * (w * 1)) - (1 : ℝ) ^ (1 + 1 / φ) / (1 + 1 / φ) := by
  intro l hl hne
  have h := (hsv_hours_optimal (τ := 0) hθ hw hφ (by norm_num)).2 l hl
  have h1 : hsvHours 0 φ = 1 := by simp [hsvHours]
  rw [h1] at h
  have := h hne
  simpa [hsvObj] using this

/-- **Appendix 15.A.2, the first-order condition** (AKMM, p. 869):
`ℓ^{1/φ} = ((1 − τ_ℓ)/(1 + τ_c))w/c_w` with `c_w = ((1 − τ_ℓ)/(1 + τ_c))wℓ` gives `ℓ = 1`
(`ℓ > 0`, `θw ≠ 0`). The printed `c_w = ((1 − τ_ℓ)/(1 + τ_c))w` omits `ℓ`. -/
theorem app_15_A_2_foc {θ φ w l : ℝ} (hφ : 0 < φ) (hl : 0 < l) (hθw : θ * w ≠ 0)
    (h : l ^ (1 / φ) = θ * w * (1 / (θ * w * l))) : l = 1 := by
  have hθ : θ ≠ 0 := left_ne_zero_of_mul hθw
  have hw : w ≠ 0 := right_ne_zero_of_mul hθw
  have h1 : l ^ (1 / φ) * l = 1 := by
    rw [h]
    field_simp
  have h2 : l ^ (1 + 1 / φ) = 1 := by
    rw [Real.rpow_add hl, Real.rpow_one, mul_comm]
    exact h1
  have hp : 0 < 1 + 1 / φ := by positivity
  have := congrArg (fun z => z ^ (1 / (1 + 1 / φ))) h2
  simp only [Real.one_rpow] at this
  rwa [← Real.rpow_mul hl.le, mul_one_div_cancel hp.ne', Real.rpow_one] at this

end AKMM.FiscalPolicy

set_option linter.style.longLine false
#print axioms AKMM.FiscalPolicy.dd_nominal_debt
#print axioms AKMM.FiscalPolicy.dd_ratio_nominal
#print axioms AKMM.FiscalPolicy.dd_ratio_real
#print axioms AKMM.FiscalPolicy.dd_ratio_const
#print axioms AKMM.FiscalPolicy.dd_zero_deficit_rises_iff
#print axioms AKMM.FiscalPolicy.eq_15_2
#print axioms AKMM.FiscalPolicy.ddStationary
#print axioms AKMM.FiscalPolicy.dd_stationary_iff
#print axioms AKMM.FiscalPolicy.dd_sub_stationary
#print axioms AKMM.FiscalPolicy.dd_tendsto_stationary
#print axioms AKMM.FiscalPolicy.dd_tendsto_atTop
#print axioms AKMM.FiscalPolicy.dd_box_threshold
#print axioms AKMM.FiscalPolicy.dd_box_309
#print axioms AKMM.FiscalPolicy.DTPolicy
#print axioms AKMM.FiscalPolicy.DTPolicy.mk
#print axioms AKMM.FiscalPolicy.DTPolicy.τc
#print axioms AKMM.FiscalPolicy.DTPolicy.τk
#print axioms AKMM.FiscalPolicy.DTPolicy.τl
#print axioms AKMM.FiscalPolicy.DTPolicy.G
#print axioms AKMM.FiscalPolicy.DTPolicy.T
#print axioms AKMM.FiscalPolicy.DTPlan
#print axioms AKMM.FiscalPolicy.DTPlan.mk
#print axioms AKMM.FiscalPolicy.DTPlan.c
#print axioms AKMM.FiscalPolicy.DTPlan.l
#print axioms AKMM.FiscalPolicy.DTPlan.k
#print axioms AKMM.FiscalPolicy.dtBudget
#print axioms AKMM.FiscalPolicy.dtFeasible
#print axioms AKMM.FiscalPolicy.dtUtil
#print axioms AKMM.FiscalPolicy.dtHHOptimal
#print axioms AKMM.FiscalPolicy.dtFirmOptimal
#print axioms AKMM.FiscalPolicy.dtGovBudget
#print axioms AKMM.FiscalPolicy.dtResource
#print axioms AKMM.FiscalPolicy.definition_15_1
#print axioms AKMM.FiscalPolicy.DTPartials
#print axioms AKMM.FiscalPolicy.dt_curve_hasDerivAt
#print axioms AKMM.FiscalPolicy.dt_tsum_two_point
#print axioms AKMM.FiscalPolicy.dt_local_max
#print axioms AKMM.FiscalPolicy.eq_15_6
#print axioms AKMM.FiscalPolicy.dt_labour_foc
#print axioms AKMM.FiscalPolicy.dt_firm_foc
#print axioms AKMM.FiscalPolicy.dt_resource_of_budgets
#print axioms AKMM.FiscalPolicy.dtPlannerOptimal
#print axioms AKMM.FiscalPolicy.dt_planner_local_max
#print axioms AKMM.FiscalPolicy.eq_15_7
#print axioms AKMM.FiscalPolicy.dt_planner_euler
#print axioms AKMM.FiscalPolicy.dt_no_tax_euler
#print axioms AKMM.FiscalPolicy.dtExU
#print axioms AKMM.FiscalPolicy.dtExF
#print axioms AKMM.FiscalPolicy.dtZeroPolicy
#print axioms AKMM.FiscalPolicy.dtExPlan
#print axioms AKMM.FiscalPolicy.dt_example_ce
#print axioms AKMM.FiscalPolicy.eq_15_8
#print axioms AKMM.FiscalPolicy.eq_15_9
#print axioms AKMM.FiscalPolicy.lrRho
#print axioms AKMM.FiscalPolicy.lrRent
#print axioms AKMM.FiscalPolicy.lr_rent_iff
#print axioms AKMM.FiscalPolicy.lr_rent_strictMonoOn
#print axioms AKMM.FiscalPolicy.lr_cd_hasDerivAt_k
#print axioms AKMM.FiscalPolicy.lr_cd_hasDerivAt_l
#print axioms AKMM.FiscalPolicy.lrS
#print axioms AKMM.FiscalPolicy.lrRatio
#print axioms AKMM.FiscalPolicy.lrWage
#print axioms AKMM.FiscalPolicy.lr_s_eq
#print axioms AKMM.FiscalPolicy.eq_15_11
#print axioms AKMM.FiscalPolicy.lr_s_strictAntiOn
#print axioms AKMM.FiscalPolicy.lr_ratio_strictAntiOn
#print axioms AKMM.FiscalPolicy.lr_wage_strictAntiOn
#print axioms AKMM.FiscalPolicy.ghhU
#print axioms AKMM.FiscalPolicy.ghhV
#print axioms AKMM.FiscalPolicy.ghh_partials
#print axioms AKMM.FiscalPolicy.eq_15_12
#print axioms AKMM.FiscalPolicy.ghhHours
#print axioms AKMM.FiscalPolicy.lr_hours_strictAntiOn_labour
#print axioms AKMM.FiscalPolicy.lr_hours_strictAntiOn_cons
#print axioms AKMM.FiscalPolicy.lr_hours_strictAntiOn_capital
#print axioms AKMM.FiscalPolicy.incSSCore
#print axioms AKMM.FiscalPolicy.incRASteady
#print axioms AKMM.FiscalPolicy.incWKSteady
#print axioms AKMM.FiscalPolicy.inc_wk_iff_ra
#print axioms AKMM.FiscalPolicy.incOutput
#print axioms AKMM.FiscalPolicy.inc_hours_ratio
#print axioms AKMM.FiscalPolicy.eq_15_13
#print axioms AKMM.FiscalPolicy.inc_output_lt
#print axioms AKMM.FiscalPolicy.inc_output_strictAntiOn_labour
#print axioms AKMM.FiscalPolicy.inc_output_strictAntiOn_cons
#print axioms AKMM.FiscalPolicy.inc_output_strictAntiOn_capital
#print axioms AKMM.FiscalPolicy.inc_cw
#print axioms AKMM.FiscalPolicy.inc_ratio_eq
#print axioms AKMM.FiscalPolicy.inc_ck
#print axioms AKMM.FiscalPolicy.incBud
#print axioms AKMM.FiscalPolicy.incTauL
#print axioms AKMM.FiscalPolicy.incM
#print axioms AKMM.FiscalPolicy.inc_budget_rhs
#print axioms AKMM.FiscalPolicy.eq_15_14
#print axioms AKMM.FiscalPolicy.inc_m_eq
#print axioms AKMM.FiscalPolicy.inc_flow_utility
#print axioms AKMM.FiscalPolicy.incExcessCost
#print axioms AKMM.FiscalPolicy.inc_core_ineq
#print axioms AKMM.FiscalPolicy.inc_wage_le
#print axioms AKMM.FiscalPolicy.inc_cd_tangent
#print axioms AKMM.FiscalPolicy.inc_ec_core
#print axioms AKMM.FiscalPolicy.inc_output_eq
#print axioms AKMM.FiscalPolicy.inc_disutil_tangent
#print axioms AKMM.FiscalPolicy.inc_excess_cost_pos
#print axioms AKMM.FiscalPolicy.inc_excess_cost_not_min_at_zero
#print axioms AKMM.FiscalPolicy.inc_tau_l_025
#print axioms AKMM.FiscalPolicy.inc_tau_l_0
#print axioms AKMM.FiscalPolicy.inc_cons_tendsto_zero
#print axioms AKMM.FiscalPolicy.fig156_tauL_eq
#print axioms AKMM.FiscalPolicy.fig156_tauL_strictAntiOn
#print axioms AKMM.FiscalPolicy.fig156_gap
#print axioms AKMM.FiscalPolicy.fig156_tauL_f
#print axioms AKMM.FiscalPolicy.fig156_tauL_concaveOn
#print axioms AKMM.FiscalPolicy.fig156_tauL_strictConcaveOn
#print axioms AKMM.FiscalPolicy.fig156_tauL_endpoints
#print axioms AKMM.FiscalPolicy.fig156_tauL_neg_iff
#print axioms AKMM.FiscalPolicy.fig156Hump
#print axioms AKMM.FiscalPolicy.fig156_hump_hasDerivAt
#print axioms AKMM.FiscalPolicy.fig156_hump_strictMonoOn
#print axioms AKMM.FiscalPolicy.fig156_hump_strictAntiOn
#print axioms AKMM.FiscalPolicy.fig156_s0
#print axioms AKMM.FiscalPolicy.fig156_s_eq
#print axioms AKMM.FiscalPolicy.fig156_s_bounds
#print axioms AKMM.FiscalPolicy.fig156_comp_hump
#print axioms AKMM.FiscalPolicy.fig156Cw
#print axioms AKMM.FiscalPolicy.fig156Ck
#print axioms AKMM.FiscalPolicy.fig156_cw_eq
#print axioms AKMM.FiscalPolicy.fig156_ck_eq
#print axioms AKMM.FiscalPolicy.fig156_cw_hump
#print axioms AKMM.FiscalPolicy.fig156_cw_isMaxOn
#print axioms AKMM.FiscalPolicy.fig156_cw_peak_tauL
#print axioms AKMM.FiscalPolicy.fig156_ck_strictAntiOn
#print axioms AKMM.FiscalPolicy.fig156_ck_hump
#print axioms AKMM.FiscalPolicy.fig156_ck_max_at_zero_iff
#print axioms AKMM.FiscalPolicy.fig156_ck_not_max_at_zero
#print axioms AKMM.FiscalPolicy.lafRevenue
#print axioms AKMM.FiscalPolicy.laf_bud_eq
#print axioms AKMM.FiscalPolicy.laf_revenue_eq
#print axioms AKMM.FiscalPolicy.laf_amgm
#print axioms AKMM.FiscalPolicy.laf_amgm_eq
#print axioms AKMM.FiscalPolicy.footnote_6
#print axioms AKMM.FiscalPolicy.laf_s0
#print axioms AKMM.FiscalPolicy.laf_bound
#print axioms AKMM.FiscalPolicy.laf_value_at_max
#print axioms AKMM.FiscalPolicy.laf_isMaxOn
#print axioms AKMM.FiscalPolicy.laf_lt_of_pos
#print axioms AKMM.FiscalPolicy.laf_rate_strictAntiOn
#print axioms AKMM.FiscalPolicy.laf_hours_zero
#print axioms AKMM.FiscalPolicy.laf_hump
#print axioms AKMM.FiscalPolicy.tg_first_best
#print axioms AKMM.FiscalPolicy.tgF
#print axioms AKMM.FiscalPolicy.tgLaw
#print axioms AKMM.FiscalPolicy.tg_homogeneous
#print axioms AKMM.FiscalPolicy.tg_crs_private
#print axioms AKMM.FiscalPolicy.tg_irs
#print axioms AKMM.FiscalPolicy.tg_net_returns_equal
#print axioms AKMM.FiscalPolicy.ricFlow
#print axioms AKMM.FiscalPolicy.ricBudgetSet
#print axioms AKMM.FiscalPolicy.ricGov
#print axioms AKMM.FiscalPolicy.ric_pv_iff
#print axioms AKMM.FiscalPolicy.ric_taxes_cancel
#print axioms AKMM.FiscalPolicy.ric_budgetSet_eq
#print axioms AKMM.FiscalPolicy.ric_optimal_iff
#print axioms AKMM.FiscalPolicy.ric_saving
#print axioms AKMM.FiscalPolicy.ric_market_clears
#print axioms AKMM.FiscalPolicy.ric_obstfeld_rogoff
#print axioms AKMM.FiscalPolicy.rmRC
#print axioms AKMM.FiscalPolicy.rmIC
#print axioms AKMM.FiscalPolicy.rmCE
#print axioms AKMM.FiscalPolicy.rm_walras
#print axioms AKMM.FiscalPolicy.eq_15_18
#print axioms AKMM.FiscalPolicy.rm_primal
#print axioms AKMM.FiscalPolicy.rmLagrangian
#print axioms AKMM.FiscalPolicy.rm_foc_c0
#print axioms AKMM.FiscalPolicy.rm_foc_l0
#print axioms AKMM.FiscalPolicy.rm_foc_c1
#print axioms AKMM.FiscalPolicy.rm_foc_l1
#print axioms AKMM.FiscalPolicy.rmU
#print axioms AKMM.FiscalPolicy.rmUc
#print axioms AKMM.FiscalPolicy.rmUl
#print axioms AKMM.FiscalPolicy.rm_crra_derivs
#print axioms AKMM.FiscalPolicy.rm_crra_focs
#print axioms AKMM.FiscalPolicy.rm_crra_euler
#print axioms AKMM.FiscalPolicy.rm_crra_labour
#print axioms AKMM.FiscalPolicy.rm_ramsey_taxes
#print axioms AKMM.FiscalPolicy.rm_tax_pos
#print axioms AKMM.FiscalPolicy.rm_mu_pos
#print axioms AKMM.FiscalPolicy.tc_cons_equal
#print axioms AKMM.FiscalPolicy.tc_output_order
#print axioms AKMM.FiscalPolicy.tc_saves
#print axioms AKMM.FiscalPolicy.tc_ce_on_line
#print axioms AKMM.FiscalPolicy.tc_household_line
#print axioms AKMM.FiscalPolicy.tc_foc_on_line
#print axioms AKMM.FiscalPolicy.tc_time_inconsistent
#print axioms AKMM.FiscalPolicy.olg_young_share
#print axioms AKMM.FiscalPolicy.olg_pension
#print axioms AKMM.FiscalPolicy.olg_budget_ratio
#print axioms AKMM.FiscalPolicy.eq_15_21
#print axioms AKMM.FiscalPolicy.eq_15_22
#print axioms AKMM.FiscalPolicy.olg_log_consumption
#print axioms AKMM.FiscalPolicy.olg_payg_eq_debt
#print axioms AKMM.FiscalPolicy.olgPV
#print axioms AKMM.FiscalPolicy.olg_pv_hasDerivAt
#print axioms AKMM.FiscalPolicy.olg_pv_increasing_iff
#print axioms AKMM.FiscalPolicy.olg_pv_approx_false
#print axioms AKMM.FiscalPolicy.olgBudgetSet
#print axioms AKMM.FiscalPolicy.olg_payg_pareto
#print axioms AKMM.FiscalPolicy.olg_payg_tax_on_young
#print axioms AKMM.FiscalPolicy.olg_holiday_taxes
#print axioms AKMM.FiscalPolicy.olg_holiday_aggregate
#print axioms AKMM.FiscalPolicy.hsvT
#print axioms AKMM.FiscalPolicy.hsv_hasDerivAt
#print axioms AKMM.FiscalPolicy.hsv_marginal_sub_average
#print axioms AKMM.FiscalPolicy.eq_15_25
#print axioms AKMM.FiscalPolicy.hsvObj
#print axioms AKMM.FiscalPolicy.hsvHours
#print axioms AKMM.FiscalPolicy.hsv_hours_optimal
#print axioms AKMM.FiscalPolicy.eq_15_26
#print axioms AKMM.FiscalPolicy.eq_15_27
#print axioms AKMM.FiscalPolicy.hsv_hours_strictAntiOn
#print axioms AKMM.FiscalPolicy.hsv_hours_tendsto
#print axioms AKMM.FiscalPolicy.hsv_var_log_c
#print axioms AKMM.FiscalPolicy.app_15_A_2
#print axioms AKMM.FiscalPolicy.app_15_A_2_foc
