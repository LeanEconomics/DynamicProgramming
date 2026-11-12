/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

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
