/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.AYEquilibrium

/-!
# Exercise 17.4: the Aiyagari model with endogenous leisure

Miao, §17.4, Exercise 4, p. 584: "Introduce endogenous leisure in the Aiyagari (1994) model and
define a stationary equilibrium."

The household chooses hours `n ∈ [0, 1]` (leisure `1 − n`) and assets: utility `u(c, 1 − n)`,
budget `c + a′ = (1 + r)a + wln`, `a′ ≥ −φ`.

* `ay_BellmanLeisure`: the household's Bellman equation
  `V(a, l) = max_{a′ ≥ −φ, n ∈ [0,1]} u((1 + r)a + wln − a′, 1 − n) + β ∫ V(a′, l′) Q(dl′, l)`.
* `ex_17_4_foc`: the intratemporal first-order condition at an interior hours choice with
  positive consumption: `wl u_c(c, 1 − n) = u_{1−n}(c, 1 − n)` (marginal rate of substitution
  between leisure and consumption equals the effective wage).
* `AYLeisureEconomy`, `AYLeisureEqm`: the stationary recursive competitive equilibrium of
  Definition 17.1.1 with endogenous leisure; the labour market clears in efficiency units,
  `L = ∫ l n(a, l) dλ*`.
* `ex_17_4_firm`: the firm's conditions (17.5)–(17.6) carry over unchanged.
* `ex_17_4`: the definition is not vacuous: a concrete equilibrium with
  `u(c, h) = c − (1 − h)²/2`, `F(K, L) = √(KL)`, `β = 1/2`, `δ = 1/4`, `l ≡ 1`, `b = −1/2`,
  `r = 1/4`, `w = 1/2`, `n ≡ 1/2`, `K = L = 1/2`, where the first-order condition
  `wl = n` holds.

**Departures.** The book only asks for the definition; the first-order condition and the
example are added. The borrowing limit `φ` is that of (17.3b).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- **Exercise 17.4** (Miao, p. 584): the household's Bellman equation with endogenous hours
`n(a, l) ∈ [0, 1]`: `V(a, l) = max u((1 + r)a + wln − a′, 1 − n) + β ∫ V(a′, l′) Q(dl′, l)`
over `n ∈ [0, 1]` and `a′ ∈ [−φ, (1 + r)a + wln]`, attained at `(g, n)`. -/
def ay_BellmanLeisure (u : ℝ × ℝ → ℝ) (β r w φ lmin lmax : ℝ) (Q : Kernel ℝ ℝ)
    (V g n : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, -φ ≤ p.1 → p.2 ∈ Set.Icc lmin lmax →
    n p ∈ Set.Icc 0 1 ∧ g p ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2 * n p) ∧
    V p = u ((1 + r) * p.1 + w * p.2 * n p - g p, 1 - n p) + β * ∫ l', V (g p, l') ∂Q p.2 ∧
    ∀ h a', h ∈ Set.Icc 0 1 → a' ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2 * h) →
      u ((1 + r) * p.1 + w * p.2 * h - a', 1 - h) + β * ∫ l', V (a', l') ∂Q p.2 ≤ V p

/-- **Exercise 17.4** (Miao, p. 584): the intratemporal first-order condition. At a state with
interior hours `n ∈ (0, 1)` and positive consumption `c`, if `u` is differentiable at
`(c, 1 − n)` with derivative `u′`, then `wl·u_c = u_{1−n}`, where `u_c = u′(1, 0)` and
`u_{1−n} = u′(0, 1)`. -/
theorem ex_17_4_foc {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {β r w φ lmin lmax : ℝ}
    {Q : Kernel ℝ ℝ} {V g n : ℝ × ℝ → ℝ} (hB : ay_BellmanLeisure u β r w φ lmin lmax Q V g n)
    {p : ℝ × ℝ} (ha : -φ ≤ p.1) (hl : p.2 ∈ Set.Icc lmin lmax) (hn : n p ∈ Set.Ioo 0 1)
    (hc : 0 < (1 + r) * p.1 + w * p.2 * n p - g p)
    (hu : HasFDerivAt u u' ((1 + r) * p.1 + w * p.2 * n p - g p, 1 - n p)) :
    w * p.2 * u' (1, 0) = u' (0, 1) := by
  obtain ⟨-, hg, hV, hmax⟩ := hB p ha hl
  set f : ℝ → ℝ × ℝ := fun h => ((1 + r) * p.1 + w * p.2 * h - g p, 1 - h) with hf
  have hfd : HasDerivAt f (w * p.2, -1) (n p) := by
    have h1 : HasDerivAt (fun h : ℝ => (1 + r) * p.1 + w * p.2 * h - g p) (w * p.2) (n p) := by
      simpa using (((hasDerivAt_id (n p)).const_mul (w * p.2)).const_add
        ((1 + r) * p.1)).sub_const (g p)
    have h2 : HasDerivAt (fun h : ℝ => 1 - h) (-1) (n p) := by
      simpa using (hasDerivAt_id (n p)).const_sub 1
    exact h1.prodMk h2
  have hcomp := hu.comp_hasDerivAt (n p) hfd
  have hcont : Continuous fun h : ℝ => (1 + r) * p.1 + w * p.2 * h - g p := by fun_prop
  have hloc : IsLocalMax (u ∘ f) (n p) := by
    filter_upwards [Ioo_mem_nhds hn.1 hn.2, hcont.continuousAt.eventually (lt_mem_nhds hc)]
      with h hh hch
    have := hmax h (g p) ⟨hh.1.le, hh.2.le⟩ ⟨hg.1, by linarith⟩
    rw [hV] at this
    simp only [Function.comp_apply, hf]
    linarith
  have h0 := hloc.hasDerivAt_eq_zero hcomp
  have hdec : ((w * p.2, -1) : ℝ × ℝ) =
      (w * p.2) • ((1 : ℝ), (0 : ℝ)) + (-1 : ℝ) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0
  linarith

/-- The primitives of the Aiyagari economy with endogenous leisure (Exercise 17.4):
utility `u(c, 1 − n)` of consumption and leisure. -/
structure AYLeisureEconomy where
  β : ℝ
  δ : ℝ
  b : ℝ
  lmin : ℝ
  lmax : ℝ
  u : ℝ × ℝ → ℝ
  F : ℝ × ℝ → ℝ
  Q : Kernel ℝ ℝ
  Q_markov : IsMarkovKernel Q

/-- **Exercise 17.4** (Miao, p. 584): a **stationary recursive competitive equilibrium with
endogenous leisure**: value function `V`, policies `g` (assets), `n` (hours), `c`
(consumption), firm's choices `K`, `L`, prices `r`, `w` and a stationary measure `λ*` such that
(i) `(V, g, n)` solve the household's problem, `c = (1 + r)a + wln − g`; (ii) `(K, L)`
maximises profits; (iii) the labour market clears in efficiency units, `L = ∫ l n dλ*`;
(iv) `K = ∫ g dλ*`; (v) `∫ c dλ* + δK = F(K, L)`; (vi) (17.7). -/
structure AYLeisureEqm (E : AYLeisureEconomy) where
  V : ℝ × ℝ → ℝ
  g : ℝ × ℝ → ℝ
  n : ℝ × ℝ → ℝ
  c : ℝ × ℝ → ℝ
  K : ℝ
  L : ℝ
  r : ℝ
  w : ℝ
  lam : Measure (ℝ × ℝ)
  lam_prob : IsProbabilityMeasure lam
  g_meas : Measurable g
  supp : ∀ᵐ p ∂lam, -ay_phi E.b w E.lmin r ≤ p.1 ∧ p.2 ∈ Set.Icc E.lmin E.lmax
  household : ay_BellmanLeisure E.u E.β r w (ay_phi E.b w E.lmin r) E.lmin E.lmax E.Q V g n
  cons_eq : ∀ p, c p = (1 + r) * p.1 + w * p.2 * n p - g p
  K_pos : 0 < K
  L_pos : 0 < L
  firm : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 → ay_profit E.F r E.δ w q ≤ ay_profit E.F r E.δ w (K, L)
  labor : L = ∫ p, p.2 * n p ∂lam
  asset : K = ∫ p, g p ∂lam
  resource : ∫ p, c p ∂lam + E.δ * K = E.F (K, L)
  stationary : ay_Stationary E.Q g lam

/-- **Exercise 17.4** (Miao, p. 584): in an equilibrium with endogenous leisure the firm's
first-order conditions (17.5)–(17.6) hold, and `λ*` is invariant under the transition
function. -/
theorem ex_17_4_firm {E : AYLeisureEconomy} (e : AYLeisureEqm E) {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hF : HasFDerivAt E.F F' (e.K, e.L)) :
    (F' (1, 0) = e.r + E.δ ∧ F' (0, 1) = e.w) ∧
      e.lam.bind (ay_P E.Q e.g e.g_meas) = e.lam := by
  have := E.Q_markov
  have := e.lam_prob
  exact ⟨eq_17_5_17_6 hF (ay_isLocalMax_of_max e.K_pos e.L_pos e.firm),
    (eq_17_7 E.Q e.g_meas e.lam).1 e.stationary⟩

/-- The concrete economy of `ay_leisureEqm`: `u(c, h) = c − (1 − h)²/2`, `F(K, L) = √(KL)`,
`β = 1/2`, `δ = 1/4`, `b = −1/2`, `l ≡ 1`. -/
noncomputable def ay_leisureEconomy : AYLeisureEconomy where
  β := 1 / 2
  δ := 1 / 4
  b := -(1 / 2)
  lmin := 1
  lmax := 1
  u := fun p => p.1 - (1 - p.2) ^ 2 / 2
  F := fun p => Real.sqrt (p.1 * p.2)
  Q := Kernel.const ℝ (Measure.dirac 1)
  Q_markov := inferInstance

theorem ay_leisure_phi : ay_phi (-(1 / 2)) (1 / 2) 1 (1 / 4) = -(1 / 2) := by
  rw [ay_phi]
  norm_num

/-- A concrete stationary equilibrium with endogenous leisure: `r = 1/4`, `w = 1/2`,
`K = L = 1/2`, `n ≡ 1/2`, `g ≡ 1/2`, `V(a, l) = 5a/4 − 1/8`, `λ* = δ_{(1/2, 1)}`. -/
noncomputable def ay_leisureEqm : AYLeisureEqm ay_leisureEconomy where
  V := fun p => 5 / 4 * p.1 - 1 / 8
  g := fun _ => 1 / 2
  n := fun _ => 1 / 2
  c := fun p => (1 + 1 / 4) * p.1 + 1 / 2 * p.2 * (1 / 2) - 1 / 2
  K := 1 / 2
  L := 1 / 2
  r := 1 / 4
  w := 1 / 2
  lam := Measure.dirac (1 / 2, 1)
  lam_prob := inferInstance
  g_meas := measurable_const
  supp := by
    rw [ae_dirac_eq]
    simp only [ay_leisureEconomy, ay_leisure_phi, Filter.eventually_pure]
    norm_num
  household := by
    intro p ha hl
    simp only [ay_leisureEconomy, ay_leisure_phi] at ha hl ⊢
    have hl1 : p.2 = 1 := le_antisymm hl.2 hl.1
    simp only [Kernel.const_apply, integral_const, probReal_univ, one_smul]
    refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by rw [hl1]; linarith⟩,
      by rw [hl1]; ring, fun h a' hh ha' => ?_⟩
    have := ha'.1
    rw [hl1]
    nlinarith [sq_nonneg (h - 1 / 2)]
  cons_eq := fun _ => rfl
  K_pos := by norm_num
  L_pos := by norm_num
  firm := by
    intro q hq1 hq2
    simp only [ay_profit, ay_leisureEconomy]
    have h4 : Real.sqrt (1 / 2 * (1 / 2)) = 1 / 2 := by
      rw [show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hq : Real.sqrt (q.1 * q.2) ≤ (q.1 + q.2) / 2 :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (q.1 - q.2)]⟩
    rw [h4]
    linarith
  labor := by rw [integral_dirac]; norm_num
  asset := by rw [integral_dirac]
  resource := by
    simp only [ay_leisureEconomy]
    rw [integral_dirac, show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  stationary := by
    intro A B hA hB
    simp only [ay_leisureEconomy, Kernel.const_apply]
    rw [lintegral_dirac, Measure.dirac_apply' _ (hA.prod hB), Set.indicator_prod_one,
      Measure.dirac_apply' _ hB]

/-- **Exercise 17.4** (Miao, p. 584): the equilibrium with endogenous leisure is not vacuous,
and in the example the intratemporal condition `wl·u_c = u_{1−n}` holds: `u_c = 1`,
`u_{1−n} = 1 − (1 − n) = n = 1/2 = wl`. -/
theorem ex_17_4 :
    Nonempty (AYLeisureEqm ay_leisureEconomy) ∧
      ay_leisureEqm.w * 1 * 1 = 1 - (1 - ay_leisureEqm.n (1 / 2, 1)) := by
  refine ⟨⟨ay_leisureEqm⟩, ?_⟩
  simp only [ay_leisureEqm]
  norm_num

end Miao.IncompleteMarkets
