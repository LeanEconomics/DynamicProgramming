/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.AYHousehold
import IncompleteMarkets.AYFirm
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §17.1.3: stationary recursive competitive equilibrium (Definition 17.1.1)

Miao, §17.1.3, pp. 562–563.

* `AYEconomy`: the primitives `(β, δ, b, l_min, l_max, u, F, Q)`.
* `AYStationaryEqm`: **Definition 17.1.1**, a value function `V`, policies `g` and `c`, the
  firm's choices `K`, `L`, prices `r`, `w` and a stationary measure `λ*` such that (i) `V`, `g`
  solve the household's Bellman equation (17.4) (with `c = (1 + r)a + wl − g` on the state space
  `a ≥ −φ`, `l ∈ [l_min, l_max]`, which carries `λ*`), (ii) `(K, L)` maximises profits, (iii)
  `L = ∫ l dλ*`, (iv) `K = ∫ g dλ*`, (v) `∫ c dλ* + δK = F(K, L)`, (vi) (17.7).
* `definition_17_1_1`: the conditions in the book's form: (17.5)–(17.6) (when `F` is
  differentiable at `(K, L)`), `c ≥ 0` on the state space, (iii)–(v), and (17.7) as invariance
  `λ* = λ*P`.
* `ay_resource_redundant`: "the resource constraint is redundant given the other equilibrium
  conditions" (p. 563), for CRS technologies (Euler's theorem gives zero profits).
* `ay_labor_iid`: "aggregate labor is ... determined by the mean of `l_t`" (p. 563) for iid
  shocks.
* `ay_exampleEconomy`, `ay_exampleEqm`, `ay_example_exists`: a concrete stationary equilibrium
  (so the definition is not vacuous): linear utility, `F(K, L) = √(KL)`, `β = 1/2`, `δ = 1/8`,
  `l ≡ 1`, `b = −4` (a saving requirement `a ≥ 4`), `r = 1/8`, `w = 1`, `K = 4`, `L = 1`,
  `V(a, l) = 9a/8 − 3/2`, `g ≡ 4`, `λ* = δ_{(4, 1)}`.

**Departures.** (1) Condition (i) is read as: `V`, `g` solve the Bellman equation (17.4) with
the maximum attained at `g` (the book's dynamic programming formulation of the household's
problem). (2) Condition (ii) is profit maximisation over `K, L ≥ 0`; the first-order conditions
(17.5)–(17.6) follow at the interior optimum when `F` is differentiable (`definition_17_1_1`).
(3) The redundancy of (v) needs the integrability of `a`, `l`, `g` under `λ*` and constant
returns to scale (the book's standing assumption on `F`).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The primitives of the Aiyagari economy of Miao §17.1 (pp. 560–563). -/
structure AYEconomy where
  β : ℝ
  δ : ℝ
  b : ℝ
  lmin : ℝ
  lmax : ℝ
  u : ℝ → ℝ
  F : ℝ × ℝ → ℝ
  Q : Kernel ℝ ℝ
  Q_markov : IsMarkovKernel Q

/-- **Definition 17.1.1** (Miao, p. 563): a **stationary recursive competitive equilibrium**. -/
structure AYStationaryEqm (E : AYEconomy) where
  V : ℝ × ℝ → ℝ
  g : ℝ × ℝ → ℝ
  c : ℝ × ℝ → ℝ
  K : ℝ
  L : ℝ
  r : ℝ
  w : ℝ
  lam : Measure (ℝ × ℝ)
  lam_prob : IsProbabilityMeasure lam
  g_meas : Measurable g
  supp : ∀ᵐ p ∂lam, -ay_phi E.b w E.lmin r ≤ p.1 ∧ p.2 ∈ Set.Icc E.lmin E.lmax
  household : ay_Bellman E.u E.β r w (ay_phi E.b w E.lmin r) E.lmin E.lmax E.Q V g
  cons_eq : ∀ p, c p = (1 + r) * p.1 + w * p.2 - g p
  K_pos : 0 < K
  L_pos : 0 < L
  firm : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → ay_profit E.F r E.δ w q ≤ ay_profit E.F r E.δ w (K, L)
  labor : L = ∫ p, p.2 ∂lam
  asset : K = ∫ p, g p ∂lam
  resource : ∫ p, c p ∂lam + E.δ * K = E.F (K, L)
  stationary : ay_Stationary E.Q g lam

/-- **Definition 17.1.1** (Miao, p. 563), in the book's form: in a stationary recursive
competitive equilibrium (with `F` differentiable at `(K, L)`), (17.5) `F_K = r + δ` and (17.6)
`F_L = w` hold; `c ≥ 0` on the state space; the labour market, asset market and resource
constraints hold; and `λ*` is invariant under the transition function (17.7). -/
theorem definition_17_1_1 {E : AYEconomy} (e : AYStationaryEqm E) {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hF : HasFDerivAt E.F F' (e.K, e.L)) :
    (F' (1, 0) = e.r + E.δ ∧ F' (0, 1) = e.w) ∧
      (∀ p : ℝ × ℝ, -ay_phi E.b e.w E.lmin e.r ≤ p.1 → p.2 ∈ Set.Icc E.lmin E.lmax →
        0 ≤ e.c p) ∧
      e.L = ∫ p, p.2 ∂e.lam ∧ e.K = ∫ p, e.g p ∂e.lam ∧
      ∫ p, e.c p ∂e.lam + E.δ * e.K = E.F (e.K, e.L) ∧
      e.lam.bind (ay_P E.Q e.g e.g_meas) = e.lam := by
  have := E.Q_markov
  have := e.lam_prob
  refine ⟨eq_17_5_17_6 hF (ay_isLocalMax_of_max e.K_pos e.L_pos e.firm), fun p ha hl => ?_,
    e.labor, e.asset, e.resource, (eq_17_7 E.Q e.g_meas e.lam).1 e.stationary⟩
  have := ((e.household p ha hl).1).2
  rw [e.cons_eq]
  linarith

/-- Miao, p. 563: "the resource constraint is redundant given the other equilibrium
conditions": with constant returns to scale and the first-order conditions (17.5)–(17.6), the
budget `c = (1 + r)a + wl − g`, labour and asset market clearing and stationarity (17.7) imply
`∫ c dλ* + δK = F(K, L)`. -/
theorem ay_resource_redundant {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {Q : Kernel ℝ ℝ}
    [IsMarkovKernel Q] {r δ w K L : ℝ} {g c : ℝ × ℝ → ℝ} {lam : Measure (ℝ × ℝ)}
    (hcrs : ay_CRS F) (hK : 0 < K) (hL : 0 < L) (hF : HasFDerivAt F F' (K, L))
    (h5 : F' (1, 0) = r + δ) (h6 : F' (0, 1) = w) (hg : Measurable g)
    (hst : ay_Stationary Q g lam) (hlab : L = ∫ p, p.2 ∂lam) (hass : K = ∫ p, g p ∂lam)
    (hc : ∀ p, c p = (1 + r) * p.1 + w * p.2 - g p)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1) lam) (h2 : Integrable (fun p : ℝ × ℝ => p.2) lam)
    (h3 : Integrable g lam) :
    ∫ p, c p ∂lam + δ * K = F (K, L) := by
  have hmean : ∫ p, p.1 ∂lam = K := by rw [ay_Ea_eq_mean hg hst, ay_Ea, hass]
  have hcint : ∫ p, c p ∂lam = (1 + r) * K + w * L - K := by
    have hA : Integrable (fun p : ℝ × ℝ => (1 + r) * p.1 + w * p.2) lam :=
      (h1.const_mul _).add (h2.const_mul _)
    calc ∫ p, c p ∂lam = ∫ p, ((1 + r) * p.1 + w * p.2) ∂lam - ∫ p, g p ∂lam := by
          simp only [hc]; exact integral_sub hA h3
      _ = (1 + r) * K + w * L - K := by
          rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul,
            integral_const_mul, hmean, ← hlab, ← hass]
  have hzero := ay_zero_profit hcrs hK hL hF h5 h6
  simp only [ay_profit] at hzero
  rw [hcint]
  linarith

/-- Miao, p. 563: with iid shocks `Q(·, l) = ν`, aggregate labour in a stationary equilibrium is
the mean of `l_t`: `L = ∫ l dν`. -/
theorem ay_labor_iid {E : AYEconomy} (e : AYStationaryEqm E) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hQ : E.Q = Kernel.const ℝ ν) : e.L = ∫ l, l ∂ν := by
  have := e.lam_prob
  have hst := e.stationary
  rw [hQ] at hst
  rw [e.labor]
  exact (ay_stationary_snd_iid hst).2

/-- The concrete economy of `ay_exampleEqm`: `u(c) = c`, `F(K, L) = √(KL)`, `β = 1/2`,
`δ = 1/8`, `b = −4`, `l ≡ 1`. -/
noncomputable def ay_exampleEconomy : AYEconomy where
  β := 1 / 2
  δ := 1 / 8
  b := -4
  lmin := 1
  lmax := 1
  u := fun c => c
  F := fun p => Real.sqrt (p.1 * p.2)
  Q := Kernel.const ℝ (Measure.dirac 1)
  Q_markov := inferInstance

theorem ay_example_phi : ay_phi (-4) 1 1 (1 / 8) = -4 := by
  rw [ay_phi]
  norm_num

/-- A concrete **stationary recursive competitive equilibrium** (Definition 17.1.1):
`r = 1/8`, `w = 1`, `K = 4`, `L = 1`, `V(a, l) = 9a/8 − 3/2`, `g ≡ 4`,
`c(a, l) = 9a/8 + l − 4`, `λ* = δ_{(4, 1)}`. -/
noncomputable def ay_exampleEqm : AYStationaryEqm ay_exampleEconomy where
  V := fun p => 9 / 8 * p.1 - 3 / 2
  g := fun _ => 4
  c := fun p => (1 + 1 / 8) * p.1 + 1 * p.2 - 4
  K := 4
  L := 1
  r := 1 / 8
  w := 1
  lam := Measure.dirac (4, 1)
  lam_prob := inferInstance
  g_meas := measurable_const
  supp := by
    rw [ae_dirac_eq]
    simp only [ay_exampleEconomy, ay_example_phi, Filter.eventually_pure]
    norm_num
  household := by
    intro p ha hl
    simp only [ay_exampleEconomy, ay_example_phi] at ha hl ⊢
    have hl1 : p.2 = 1 := le_antisymm hl.2 hl.1
    simp only [Kernel.const_apply, integral_const, probReal_univ, one_smul]
    refine ⟨⟨by norm_num, by rw [hl1]; linarith⟩, by rw [hl1]; ring, fun a' ha' => ?_⟩
    have := ha'.1
    rw [hl1]
    linarith
  cons_eq := fun _ => rfl
  K_pos := by norm_num
  L_pos := by norm_num
  firm := by
    intro q hq1 hq2
    simp only [ay_profit, ay_exampleEconomy]
    have h4 : Real.sqrt (4 * 1) = 2 := by
      rw [show (4 : ℝ) * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hq : Real.sqrt (q.1 * q.2) ≤ q.1 / 4 + q.2 :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (q.1 / 4 - q.2)]⟩
    rw [h4]
    linarith
  labor := by rw [integral_dirac]
  asset := by rw [integral_dirac]
  resource := by
    simp only [ay_exampleEconomy]
    rw [integral_dirac, show (4 : ℝ) * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  stationary := by
    intro A B hA hB
    simp only [ay_exampleEconomy, Kernel.const_apply]
    rw [lintegral_dirac, Measure.dirac_apply' _ (hA.prod hB), Set.indicator_prod_one,
      Measure.dirac_apply' _ hB]

/-- Definition 17.1.1 is not vacuous: the example economy has a stationary recursive competitive
equilibrium, with interest rate `r = 1/8 < ρ = 1/β − 1 = 1`. -/
theorem ay_example_exists :
    Nonempty (AYStationaryEqm ay_exampleEconomy) ∧
      ay_exampleEqm.r < 1 / ay_exampleEconomy.β - 1 := by
  refine ⟨⟨ay_exampleEqm⟩, ?_⟩
  simp only [ay_exampleEqm, ay_exampleEconomy]
  norm_num

end Miao.IncompleteMarkets
