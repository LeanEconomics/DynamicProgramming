/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OPDiamond
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dynamic efficiency in the Diamond model

Miao, §16.2, pp. 549–551.

* The aggregate resource constraint per worker, `k_t + f(k_t) = g_nk_{t+1} + c_t^t + g_n⁻¹c_t^{t−1}`
  (`op_resource_per_worker`), and in a steady state (16.17)
  `c_y + g_n⁻¹c_o = f(k) − (g_n − 1)k` (`eq_16_17`).
* The golden rule `f′(k_G) = g_n − 1` maximises steady-state consumption per worker
  (`op_golden_rule_max`, strictly: `op_golden_rule_strict`); `k_G` exists and is unique
  (`op_golden_rule_exists`, `op_golden_rule_unique`).
* The planner's steady-state problem: the partial derivatives of the Lagrangian
  (`op_planner_lagrangian`) and the first-order conditions (`op_planner_foc`); with `λ₀ = 0`,
  `θ = 0` and the golden rule (`op_planner_golden_rule`). **Correction:** the printed conditions
  `u′(c_y)/(βu′(c_o)) = g_n` and `f′(k) = g_n − 1 + θ/µ` hold only for `θ = 0`; in general
  `u′(c_y)/(βu′(c_o)) = g_n(1 + θ/µ)` and `f′(k) = g_n − 1 + g_nθ/µ`
  (`op_planner_foc_printed`). The conclusion `f′(k) ≥ g_n − 1` stands.
* Dynamic inefficiency: a steady state with `k* > k_G` is Pareto dominated: lowering capital to
  `k_G` makes every generation strictly better off and leaves the initial old as well off
  (`OPFeasible`, `OPParetoDominates`, `op_dynamic_inefficiency`).
* A competitive steady state with `k* < k_G` (`f′(k*) > g_n − 1`) is Pareto optimal
  (`op_pareto_optimal_of_lt_golden`), by a present-value argument at the prices `(g_n/R)ᵗ`.
* The Cass–Balasko–Shell criterion at a steady state: `Σ g_n⁻ᵗ ∏_{s ≤ t} R_{s+1} = ∞` iff
  `R ≥ g_n` iff `k* ≤ k_G` (`op_cass_steady_state`, `op_cass_corollary`).

Not formalised: the general Cass (1972) / Balasko–Shell (1980) theorem (cited, not proved, in
the text), and Pareto optimality of the golden-rule steady state `k* = k_G` itself.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, p. 550: dividing the aggregate resource constraint
`K_t + F(K_t, N_t) = K_{t+1} + N_tc_t^t + N_{t−1}c_t^{t−1}` (with `F(K, N) = Nf(K/N)`) by `N_t`
gives `k_t + f(k_t) = g_nk_{t+1} + c_t^t + g_n⁻¹c_t^{t−1}`. -/
theorem op_resource_per_worker {f : ℝ → ℝ} {K K' N Nm N' gn cy co : ℝ} (hgn : 0 < gn)
    (hNm : 0 < Nm) (hN : N = gn * Nm) (hN' : N' = gn * N)
    (h : K + N * f (K / N) = K' + N * cy + Nm * co) :
    K / N + f (K / N) = gn * (K' / N') + cy + co / gn := by
  have hN0 : 0 < N := by rw [hN]; positivity
  rw [hN'] at *
  rw [hN] at h hN0 ⊢
  field_simp
  field_simp at h
  linarith

/-- Miao, (16.17), p. 550: in a steady state the resource constraint is
`c_y + g_n⁻¹c_o = f(k) − (g_n − 1)k`. -/
theorem eq_16_17 {f : ℝ → ℝ} {gn k cy co : ℝ} :
    k + f k = gn * k + cy + co / gn ↔ cy + co / gn = f k - (gn - 1) * k := by
  constructor <;> intro h <;> linarith

/-- Miao, p. 551: the golden rule `f′(k_G) = g_n − 1` maximises steady-state consumption per
worker `f(k) − (g_n − 1)k`. -/
theorem op_golden_rule_max {f : ℝ → ℝ} {gn kG : ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hkG : 0 ≤ kG) (hfG : HasDerivAt f (gn - 1) kG) {k : ℝ} (hk : 0 ≤ k) :
    f k - (gn - 1) * k ≤ f kG - (gn - 1) * kG := by
  have := op_concave_tangent hconc (Set.mem_Ici.2 hkG) (Set.mem_Ici.2 hk) hfG
  linarith

/-- The golden rule is the unique maximiser for strictly concave `f`. -/
theorem op_golden_rule_strict {f : ℝ → ℝ} {gn kG : ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hkG : 0 ≤ kG) (hfG : HasDerivAt f (gn - 1) kG) {k : ℝ} (hk : 0 ≤ k) (hne : k ≠ kG) :
    f k - (gn - 1) * k < f kG - (gn - 1) * kG := by
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hkG) (Set.mem_Ici.2 hk) hne hfG
  linarith

/-- The golden rule capital stock is unique (`f′` strictly decreasing). -/
theorem op_golden_rule_unique {fp : ℝ → ℝ} {gn k1 k2 : ℝ} (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hk1 : 0 < k1) (hk2 : 0 < k2) (h1 : fp k1 = gn - 1) (h2 : fp k2 = gn - 1) : k1 = k2 :=
  hanti.injOn hk1 hk2 (by rw [h1, h2])

/-- The golden rule exists when `g_n > 1`, `f′` is continuous, `f′(0+) = ∞` and `f′(∞) = 0`. -/
theorem op_golden_rule_exists {fp : ℝ → ℝ} {gn : ℝ} (hgn : 1 < gn)
    (hfpc : ContinuousOn fp (Set.Ioi 0)) (hinada : Tendsto fp (𝓝[>] 0) atTop)
    (hinf : Tendsto fp atTop (𝓝 0)) : ∃ kG, 0 < kG ∧ fp kG = gn - 1 := by
  obtain ⟨ε, hε, hl⟩ := op_inada_small hinada (gn - 1)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hinf.eventually (eventually_lt_nhds
    (show (0 : ℝ) < gn - 1 by linarith)))
  set a := ε / 2 with ha_def
  set b := max M (a + 1)
  have hab : a ≤ b := le_trans (by linarith) (le_max_right _ _)
  have ha : 0 < a := by positivity
  obtain ⟨k, hk, hfk⟩ := intermediate_value_Icc' hab
    (hfpc.mono fun x hx => lt_of_lt_of_le ha hx.1)
    ⟨(hM b (le_max_left _ _)).le, (hl a ha (by linarith)).le⟩
  exact ⟨k, lt_of_lt_of_le ha hk.1, hfk⟩

/-! ### The planner's steady-state problem -/

/-- Miao, pp. 550–551: the Lagrangian of the planner's steady-state problem,
`λ₀u(c₁⁰) + λ₁[u(c_y) + βu(c_o)] + µ[f(k) − (g_n − 1)k − c_y − g_n⁻¹c_o]
 + θ[f(k₁) + k₁ − g_nk − c_y − g_n⁻¹c₁⁰]`. -/
noncomputable def opLagrangian (u f : ℝ → ℝ) (lam0 lam1 β gn μ θ k1 cy co c01 k : ℝ) : ℝ :=
  lam0 * u c01 + lam1 * (u cy + β * u co) + μ * (f k - (gn - 1) * k - cy - co / gn) +
    θ * (f k1 + k1 - gn * k - cy - c01 / gn)

/-- The partial derivatives of the planner's Lagrangian in `c_y`, `c_o`, `c₁⁰` and `k`. -/
theorem op_planner_lagrangian {u up f fp : ℝ → ℝ} {lam0 lam1 β gn μ θ k1 cy co c01 k : ℝ}
    (hcy : HasDerivAt u (up cy) cy) (hco : HasDerivAt u (up co) co)
    (hc01 : HasDerivAt u (up c01) c01) (hk : HasDerivAt f (fp k) k) :
    HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 x co c01 k)
        (lam1 * up cy - μ - θ) cy ∧
      HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 cy x c01 k)
        (lam1 * β * up co - μ / gn) co ∧
      HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 cy co x k)
        (lam0 * up c01 - θ / gn) c01 ∧
      HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 cy co c01 x)
        (μ * (fp k - (gn - 1)) - θ * gn) k := by
  unfold opLagrangian
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((((hcy.add_const (β * u co)).const_mul lam1).const_add (lam0 * u c01)).add
      ((((hasDerivAt_id' cy).const_sub (f k - (gn - 1) * k)).sub_const (co / gn)).const_mul
        μ)).add ((((hasDerivAt_id' cy).const_sub (f k1 + k1 - gn * k)).sub_const
        (c01 / gn)).const_mul θ)
    convert h using 1
    ring
  · have h := (((((hco.const_mul β).const_add (u cy)).const_mul lam1).const_add
      (lam0 * u c01)).add ((((hasDerivAt_id' co).div_const gn).const_sub
        (f k - (gn - 1) * k - cy)).const_mul μ)).add_const
      (θ * (f k1 + k1 - gn * k - cy - c01 / gn))
    convert h using 1
    ring
  · have h := (((hc01.const_mul lam0).add_const (lam1 * (u cy + β * u co))).add
      ((((hasDerivAt_id' c01).div_const gn).const_sub (f k1 + k1 - gn * k - cy)).const_mul
        θ)).add_const (μ * (f k - (gn - 1) * k - cy - co / gn))
    convert h using 1
    · ext x; simp only [Pi.add_apply]; ring
    · ring
  · have h := ((((hk.sub ((hasDerivAt_id' k).const_mul (gn - 1))).sub_const
      (cy + co / gn)).const_mul μ).add (((((hasDerivAt_id' k).const_mul gn).const_sub
        (f k1 + k1)).sub_const (cy + c01 / gn)).const_mul θ)).const_add
      (lam0 * u c01 + lam1 * (u cy + β * u co))
    convert h using 1
    · ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · ring

/-- Miao, p. 551: the first-order conditions of the planner's problem. From the stationarity
of the Lagrangian with `µ > 0`, `θ ≥ 0`: `u′(c_y)/(βu′(c_o)) = g_n(1 + θ/µ)`,
`λ₀u′(c₁⁰) = θ/g_n`, and `f′(k) = g_n − 1 + g_nθ/µ ≥ g_n − 1`. -/
theorem op_planner_foc {up : ℝ → ℝ} {lam0 lam1 β gn μ θ cy co c01 fpk : ℝ} (hgn : 0 < gn)
    (hβ : 0 < β) (hμ : 0 < μ) (hθ : 0 ≤ θ) (hup : 0 < up co)
    (h1 : lam1 * up cy - μ - θ = 0) (h2 : lam1 * β * up co - μ / gn = 0)
    (h3 : lam0 * up c01 - θ / gn = 0) (h4 : μ * (fpk - (gn - 1)) - θ * gn = 0) :
    up cy / (β * up co) = gn * (1 + θ / μ) ∧ lam0 * up c01 = θ / gn ∧
      fpk = gn - 1 + gn * θ / μ ∧ gn - 1 ≤ fpk := by
  have hlam1 : lam1 * (β * up co) = μ / gn := by linarith
  have hlam1pos : 0 < lam1 := by
    by_contra h
    push Not at h
    have : lam1 * (β * up co) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    have : 0 < μ / gn := div_pos hμ hgn
    linarith
  have hfpk : fpk = gn - 1 + gn * θ / μ := by
    field_simp
    linarith
  refine ⟨?_, by linarith, hfpk, ?_⟩
  · rw [div_eq_iff (by positivity)]
    have hcy : lam1 * up cy = μ + θ := by linarith
    have : lam1 * (up cy - gn * (1 + θ / μ) * (β * up co)) = 0 := by
      have e : lam1 * (gn * (1 + θ / μ) * (β * up co)) = gn * (1 + θ / μ) * (μ / gn) := by
        rw [← hlam1]; ring
      have e2 : gn * (1 + θ / μ) * (μ / gn) = μ + θ := by field_simp
      linarith [mul_sub lam1 (up cy) (gn * (1 + θ / μ) * (β * up co))]
    have := (mul_eq_zero.1 this).resolve_left hlam1pos.ne'
    linarith
  · rw [hfpk]
    have : 0 ≤ gn * θ / μ := by positivity
    linarith

/-- Miao, p. 551: "When the planner does not consider the initial old, `λ₀ = 0`, so that
`θ = 0`": then `u′(c_y)/(βu′(c_o)) = g_n` and `f′(k) = g_n − 1`, the golden rule. -/
theorem op_planner_golden_rule {up : ℝ → ℝ} {lam1 β gn μ θ cy co c01 fpk : ℝ} (hgn : 0 < gn)
    (hβ : 0 < β) (hμ : 0 < μ) (hθ : 0 ≤ θ) (hup : 0 < up co)
    (h1 : lam1 * up cy - μ - θ = 0) (h2 : lam1 * β * up co - μ / gn = 0)
    (h3 : 0 * up c01 - θ / gn = 0) (h4 : μ * (fpk - (gn - 1)) - θ * gn = 0) :
    θ = 0 ∧ up cy / (β * up co) = gn ∧ fpk = gn - 1 := by
  obtain ⟨ha, -, hc, -⟩ := op_planner_foc hgn hβ hμ hθ hup h1 h2 h3 h4
  have hθ0 : θ = 0 := by
    have : θ / gn = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hgn.ne'
  rw [hθ0] at ha hc
  refine ⟨hθ0, by simpa using ha, by simpa using hc⟩

/-- **Correction** (Miao, p. 551): with `θ > 0` the printed first-order conditions fail:
`u′(c_y)/(βu′(c_o)) ≠ g_n`, and `f′(k) ≠ g_n − 1 + θ/µ` unless `g_n = 1`. -/
theorem op_planner_foc_printed {up : ℝ → ℝ} {lam0 lam1 β gn μ θ cy co c01 fpk : ℝ}
    (hgn : 0 < gn) (hβ : 0 < β) (hμ : 0 < μ) (hθ : 0 < θ) (hup : 0 < up co)
    (h1 : lam1 * up cy - μ - θ = 0) (h2 : lam1 * β * up co - μ / gn = 0)
    (h3 : lam0 * up c01 - θ / gn = 0) (h4 : μ * (fpk - (gn - 1)) - θ * gn = 0) :
    up cy / (β * up co) ≠ gn ∧ (gn ≠ 1 → fpk ≠ gn - 1 + θ / μ) := by
  obtain ⟨ha, -, hc, -⟩ := op_planner_foc hgn hβ hμ hθ.le hup h1 h2 h3 h4
  have hθμ : 0 < θ / μ := div_pos hθ hμ
  refine ⟨fun h => ?_, fun hg h => ?_⟩
  · rw [ha] at h
    have : gn * (θ / μ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · rw [hc] at h
    have : (gn - 1) * (θ / μ) = 0 := by
      have e : gn * θ / μ = gn * (θ / μ) := by ring
      linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact hg (by linarith)
    · linarith

/-! ### Feasible allocations and Pareto dominance -/

/-- A feasible allocation (Miao, p. 550), indexed from the book's `t = 1` as `t = 0`: capital
`k_t ≥ 0`, consumption of the young `y_t > 0` and of the old `o_t > 0` (`o₀ = c₁⁰`, the
initial old), with `k_t + f(k_t) = g_nk_{t+1} + y_t + o_t/g_n`. -/
def OPFeasible (f : ℝ → ℝ) (gn : ℝ) (k y o : ℕ → ℝ) : Prop :=
  ∀ t, 0 ≤ k t ∧ 0 < y t ∧ 0 < o t ∧ k t + f (k t) = gn * k (t + 1) + y t + o t / gn

/-- The allocation `(k, y, o)` starting from `k₀ = k*` Pareto dominates the steady state
`(k*, c_y, c_o)`: the initial old and every generation `t` (utility `u(y_t) + βu(o_{t+1})`) are
at least as well off, and someone is strictly better off. -/
def OPParetoDominates (u : ℝ → ℝ) (β : ℝ) (f : ℝ → ℝ) (gn kstar cy co : ℝ)
    (k y o : ℕ → ℝ) : Prop :=
  OPFeasible f gn k y o ∧ k 0 = kstar ∧ u co ≤ u (o 0) ∧
    (∀ t, u cy + β * u co ≤ u (y t) + β * u (o (t + 1))) ∧
    (u co < u (o 0) ∨ ∃ t, u cy + β * u co < u (y t) + β * u (o (t + 1)))

/-- The steady-state allocation is feasible. -/
theorem op_steady_feasible {f : ℝ → ℝ} {gn kstar cy co : ℝ} (hks : 0 ≤ kstar) (hcy : 0 < cy)
    (hco : 0 < co) (hss : kstar + f kstar = gn * kstar + cy + co / gn) :
    OPFeasible f gn (fun _ => kstar) (fun _ => cy) (fun _ => co) :=
  fun _ => ⟨hks, hcy, hco, hss⟩

/-- Miao, p. 551: "When the marginal product of capital is smaller than the population growth
rate, the economy accumulates too much capital `k* > k_G` and hence it is dynamically
inefficient. A planner can reduce saving from `k*` to `k_G` and makes everyone better off."
The allocation `k₀ = k*`, `k_t = k_G` (`t ≥ 1`), `y₀ = c_y + g_n(k* − k_G)`,
`y_t = c_y + Δ` with `Δ = [f(k_G) − (g_n − 1)k_G] − [f(k*) − (g_n − 1)k*] > 0`, `o_t = c_o`
Pareto dominates the steady state: every generation is strictly better off. -/
theorem op_dynamic_inefficiency {u f : ℝ → ℝ} {β gn kstar kG cy co : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hkG : 0 ≤ kG) (hfG : HasDerivAt f (gn - 1) kG)
    (hks : kG < kstar) (hcy : 0 < cy) (hco : 0 < co)
    (hss : kstar + f kstar = gn * kstar + cy + co / gn) (hu : StrictMonoOn u (Set.Ioi 0)) :
    ∃ k y o : ℕ → ℝ, OPParetoDominates u β f gn kstar cy co k y o ∧
      ∀ t, cy < y t ∧ o t = co := by
  set Δ := (f kG - (gn - 1) * kG) - (f kstar - (gn - 1) * kstar) with hΔ
  have hΔpos : 0 < Δ := by
    have := op_golden_rule_strict hconc hkG hfG (by linarith : (0 : ℝ) ≤ kstar) hks.ne'
    rw [hΔ]; linarith
  set k : ℕ → ℝ := fun t => if t = 0 then kstar else kG
  set y : ℕ → ℝ := fun t => if t = 0 then cy + gn * (kstar - kG) else cy + Δ
  set o : ℕ → ℝ := fun _ => co
  have hy : ∀ t, cy < y t := by
    intro t
    rcases t with _ | t
    · simp only [y, ↓reduceIte]; nlinarith
    · simp only [y, Nat.add_one_ne_zero, ↓reduceIte]; linarith
  have hgain : ∀ t, u cy + β * u co < u (y t) + β * u (o (t + 1)) := by
    intro t
    have := hu (show cy ∈ Set.Ioi 0 from hcy) (show y t ∈ Set.Ioi 0 from
      lt_trans hcy (hy t)) (hy t)
    simp only [o]
    linarith
  refine ⟨k, y, o, ⟨?_, by simp [k], le_rfl, fun t => (hgain t).le, Or.inr ⟨0, hgain 0⟩⟩,
    fun t => ⟨hy t, rfl⟩⟩
  intro t
  refine ⟨?_, lt_trans hcy (hy t), hco, ?_⟩
  · rcases t with _ | t
    · simp only [k, ↓reduceIte]; linarith
    · simp only [k, Nat.add_one_ne_zero, ↓reduceIte]; exact hkG
  · rcases t with _ | t
    · simp only [k, y, o, ↓reduceIte, zero_add, one_ne_zero]
      linarith
    · simp only [k, y, o, Nat.add_one_ne_zero, ↓reduceIte]
      rw [hΔ]
      linarith

/-- Miao, p. 551 (the efficient half of the steady-state corollary): a competitive steady state
with `f′(k*) > g_n − 1` (`k* < k_G`) is Pareto optimal. Here `c_y, c_o` satisfy the Euler
equation `u′(c_y) = βRu′(c_o)`, `R = 1 + f′(k*)`, with `u` concave and strictly increasing and
`f` concave. No feasible allocation from `k₀ = k*` Pareto dominates it. -/
theorem op_pareto_optimal_of_lt_golden {u up f : ℝ → ℝ} {β gn kstar cy co fps : ℝ}
    (hgn : 0 < gn) (hβ : 0 < β) (huc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hum : StrictMonoOn u (Set.Ioi 0)) (hucy : HasDerivAt u (up cy) cy)
    (huco : HasDerivAt u (up co) co) (hupco : 0 < up co)
    (heul : up cy = β * (1 + fps) * up co) (hfc : ConcaveOn ℝ (Set.Ici 0) f)
    (hks : 0 < kstar) (hfd : HasDerivAt f fps kstar) (heff : gn - 1 < fps) (hcy : 0 < cy)
    (hco : 0 < co) (hss : kstar + f kstar = gn * kstar + cy + co / gn) :
    ¬ ∃ k y o : ℕ → ℝ, OPParetoDominates u β f gn kstar cy co k y o := by
  rintro ⟨k, y, o, hfeas, hk0, hold, hgen, hstrict⟩
  set R := 1 + fps with hR
  have hRgn : gn < R := by rw [hR]; linarith
  have hR0 : 0 < R := lt_trans hgn hRgn
  set ρ := gn / R with hρ
  have hρ0 : 0 < ρ := div_pos hgn hR0
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hR0]; exact hRgn
  have hρR : ρ * R = gn := by rw [hρ]; field_simp
  -- the one-period resource inequality
  have hres : ∀ t, gn * (k (t + 1) - kstar) + (y t - cy) + (o t - co) / gn ≤
      R * (k t - kstar) := by
    intro t
    obtain ⟨hkt, -, -, he⟩ := hfeas t
    have := op_concave_tangent hfc (Set.mem_Ici.2 hks.le) (Set.mem_Ici.2 hkt) hfd
    have e : (o t - co) / gn = o t / gn - co / gn := by ring
    rw [e, hR]
    nlinarith
  -- the value gain of each generation at the prices `(1, 1/R)`
  have hD : ∀ t, u cy + β * u co ≤ u (y t) + β * u (o (t + 1)) →
      β * up co * (R * (y t - cy) + (o (t + 1) - co)) ≥
        u (y t) + β * u (o (t + 1)) - (u cy + β * u co) := by
    intro t _
    have h1 := op_concave_tangent huc (show cy ∈ Set.Ioi 0 from hcy)
      (show y t ∈ Set.Ioi 0 from (hfeas t).2.1) hucy
    have h2 := op_concave_tangent huc (show co ∈ Set.Ioi 0 from hco)
      (show o (t + 1) ∈ Set.Ioi 0 from (hfeas (t + 1)).2.2.1) huco
    have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
    rw [heul] at h1
    nlinarith
  have hβu : 0 < β * up co := mul_pos hβ hupco
  set D : ℕ → ℝ := fun t => (y t - cy) + (o (t + 1) - co) / R with hDdef
  have hDnn : ∀ t, 0 ≤ D t := by
    intro t
    have := hD t (hgen t)
    have h0 : 0 ≤ R * (y t - cy) + (o (t + 1) - co) := by
      by_contra h
      push Not at h
      have := mul_neg_of_pos_of_neg hβu h
      linarith [hgen t]
    simp only [hDdef]
    have : (y t - cy) + (o (t + 1) - co) / R = (R * (y t - cy) + (o (t + 1) - co)) / R := by
      field_simp
    rw [this]
    exact div_nonneg h0 hR0.le
  have ho0 : co ≤ o 0 := by
    by_contra h
    push Not at h
    have := hum (show o 0 ∈ Set.Ioi 0 from (hfeas 0).2.2.1) (show co ∈ Set.Ioi 0 from hco) h
    linarith
  -- the telescoped present-value inequality
  have hP : ∀ T, (o 0 - co) / gn + (∑ t ∈ Finset.range T, ρ ^ t * D t) + ρ ^ T * (y T - cy) +
      ρ ^ (T + 1) * R * (k (T + 1) - kstar) ≤ 0 := by
    intro T
    induction T with
    | zero =>
      have := hres 0
      rw [hk0, sub_self, mul_zero] at this
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add, pow_one]
      rw [hρR]
      linarith
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have hstep := hres (T + 1)
      have hpow : 0 ≤ ρ ^ (T + 1) := pow_nonneg hρ0.le _
      have hm := mul_le_mul_of_nonneg_left hstep hpow
      have e : ρ ^ T * D T + ρ ^ (T + 1) * (y (T + 1) - cy) +
          ρ ^ (T + 1 + 1) * R * (k (T + 1 + 1) - kstar) - ρ ^ T * (y T - cy) -
          ρ ^ (T + 1) * R * (k (T + 1) - kstar) =
          ρ ^ (T + 1) * (gn * (k (T + 1 + 1) - kstar) + (y (T + 1) - cy) +
            (o (T + 1) - co) / gn - R * (k (T + 1) - kstar)) := by
        simp only [hDdef, pow_succ]
        field_simp
        rw [← hρR]
        ring
      linarith
  -- the right-hand side vanishes
  have hbound : ∀ T, (o 0 - co) / gn + (∑ t ∈ Finset.range T, ρ ^ t * D t) ≤
      ρ ^ T * (cy + gn * kstar) := by
    intro T
    have h := hP T
    have hy : -cy ≤ y T - cy := by linarith [(hfeas T).2.1]
    have hk : -kstar ≤ k (T + 1) - kstar := by linarith [(hfeas (T + 1)).1]
    have hpT : 0 ≤ ρ ^ T := pow_nonneg hρ0.le _
    have h1 := mul_le_mul_of_nonneg_left hy hpT
    have h2 := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ ρ ^ (T + 1) * R)
    have e : ρ ^ (T + 1) * R * -kstar = -(ρ ^ T * gn * kstar) := by
      rw [pow_succ]; linear_combination (-(ρ ^ T) * kstar) * hρR
    nlinarith
  -- someone gains strictly
  obtain ⟨c, hc, m, hlow⟩ : ∃ c > 0, ∃ m : ℕ, ∀ T, m < T →
      c ≤ (o 0 - co) / gn + ∑ t ∈ Finset.range T, ρ ^ t * D t := by
    have hsum : ∀ T, 0 ≤ ∑ t ∈ Finset.range T, ρ ^ t * D t := fun T =>
      Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hρ0.le _) (hDnn t)
    rcases hstrict with h | ⟨m, hm⟩
    · have ho : co < o 0 := by
        by_contra h'
        push Not at h'
        rcases h'.lt_or_eq with h'' | h''
        · have := hum (show o 0 ∈ Set.Ioi 0 from (hfeas 0).2.2.1)
            (show co ∈ Set.Ioi 0 from hco) h''
          linarith
        · rw [h''] at h; linarith
      refine ⟨(o 0 - co) / gn, div_pos (by linarith) hgn, 0, fun T _ => ?_⟩
      linarith [hsum T]
    · have hDm : 0 < D m := by
        have := hD m (hgen m)
        have h0 : 0 < R * (y m - cy) + (o (m + 1) - co) := by
          by_contra h
          push Not at h
          have := mul_nonpos_of_nonneg_of_nonpos hβu.le h
          linarith
        simp only [hDdef]
        have : (y m - cy) + (o (m + 1) - co) / R = (R * (y m - cy) + (o (m + 1) - co)) / R := by
          field_simp
        rw [this]
        exact div_pos h0 hR0
      refine ⟨ρ ^ m * D m, mul_pos (pow_pos hρ0 _) hDm, m, fun T hT => ?_⟩
      have := Finset.single_le_sum (f := fun t => ρ ^ t * D t)
        (fun t _ => mul_nonneg (pow_nonneg hρ0.le _) (hDnn t)) (Finset.mem_range.2 hT)
      have : 0 ≤ (o 0 - co) / gn := div_nonneg (by linarith) hgn.le
      linarith
  have hlim : Tendsto (fun T => ρ ^ T * (cy + gn * kstar)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const (cy + gn * kstar)
    rwa [zero_mul] at this
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hc))
  have h1 := hlow (max T0 (m + 1)) (lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _))
  have h2 := hbound (max T0 (m + 1))
  have h3 := hT0 (max T0 (m + 1)) (le_max_left _ _)
  linarith

/-! ### The Cass–Balasko–Shell criterion at a steady state -/

/-- Miao, p. 551: at a steady state `R_t = R`, the Cass–Balasko–Shell sum
`Σ_t g_n⁻ᵗ ∏_{s=1}^t R_{s+1}` diverges iff `R ≥ g_n`. -/
theorem op_cass_steady_state {gn R : ℝ} {Rs : ℕ → ℝ} (hgn : 0 < gn) (hR : 0 < R)
    (hRs : ∀ s, Rs s = R) :
    ¬ Summable (fun t : ℕ => gn⁻¹ ^ t * ∏ s ∈ Finset.range t, Rs (s + 1)) ↔ gn ≤ R := by
  have e : (fun t : ℕ => gn⁻¹ ^ t * ∏ s ∈ Finset.range t, Rs (s + 1)) =
      fun t : ℕ => (R / gn) ^ t := by
    ext t
    simp only [hRs, Finset.prod_const, Finset.card_range]
    rw [div_eq_mul_inv, mul_pow, mul_comm]
  rw [e, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_pos (div_pos hR hgn), div_lt_one hgn, not_lt]

/-- Miao, p. 551: "a steady state equilibrium is Pareto optimal (or dynamically efficient) if
and only if `k* ≤ k_G` or `f′(k*) ≥ g_n − 1`": the Cass–Balasko–Shell sum at the steady state
with `R = 1 + f′(k*)` diverges iff `f′(k*) ≥ g_n − 1` iff `k* ≤ k_G`. (The Pareto optimality
halves are `op_pareto_optimal_of_lt_golden` and `op_dynamic_inefficiency`.) -/
theorem op_cass_corollary {fp : ℝ → ℝ} {gn kstar kG : ℝ} {Rs : ℕ → ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hfp : 0 < fp kstar) (hks : 0 < kstar) (hkG : 0 < kG)
    (hG : fp kG = gn - 1) (hRs : ∀ s, Rs s = 1 + fp kstar) :
    (¬ Summable (fun t : ℕ => gn⁻¹ ^ t * ∏ s ∈ Finset.range t, Rs (s + 1)) ↔
      gn - 1 ≤ fp kstar) ∧ (gn - 1 ≤ fp kstar ↔ kstar ≤ kG) := by
  refine ⟨?_, ?_⟩
  · rw [op_cass_steady_state hgn (by linarith) hRs]
    constructor <;> intro h <;> linarith
  · rw [← hG]
    exact hanti.le_iff_ge hkG hks

end Miao.OverlappingGenerations
