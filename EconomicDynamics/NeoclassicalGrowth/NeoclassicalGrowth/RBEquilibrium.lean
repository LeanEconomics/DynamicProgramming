/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBPlanner

/-!
# The decentralised equilibrium of the basic RBC model

Miao, §14.2, p. 472: "In a decentralized equilibrium in which households own capital and make
real investment, the rental rate and the wage rate are given by
`R_kt = αz_tK_t^{α−1}N_t^{1−α}` and `w_t = (1 − α)z_tK_t^αN_t^{−α}`", and "our previous analysis
regarding Pareto optimality and decentralized competitive equilibrium still applies to the
stochastic case" (the sequential equilibrium of §14.1, pp. 460–461, with population and
technology growth switched off).

* The household's budget `c_t + k_{t+1} = (R_kt + 1 − δ)k_t + w_tn_t + Π_t`
  (`rb_IsHHFeasible`), its Euler equation `1/c_t = E_t[β(R_{k,t+1} + 1 − δ)/c_{t+1}]`
  (`rb_HHEuler`) and labour supply (14.36) `χc_t/(1 − n_t) = w_t`.
* **Household sufficiency** (`rb_household_suff`, `rb_household_optimal`): with transversality,
  these conditions make the plan optimal for the household at the given prices.
* A sequential competitive equilibrium (`rb_IsSCE`): the household conditions, the firm's
  profit maximisation at every date and state, and profits paid to the household; markets clear
  with a unit population, so the firm's inputs are `(k_t, n_t)`.
* **Equivalence** (`rb_sce_iff`): a positive allocation with prices `(R_k, w, Π)` is a sequential
  competitive equilibrium iff the prices are the marginal products with zero profits and the
  allocation satisfies the planner's conditions: feasibility, (14.26) and (14.27). Hence an
  equilibrium allocation satisfying transversality is optimal for the planner
  (`rb_sce_optimal`, first welfare theorem), and the planner's allocation decentralises
  (second welfare theorem, the `←` direction).
* Non-vacuity: the full-depreciation solution with marginal-product prices is an equilibrium
  (`rb_bm_sce`).
-/

open MeasureTheory Filter Topology

namespace Miao.NeoclassicalGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The household's feasible plans (Miao, p. 460): `c_t > 0`, `0 ≤ n_t < 1`, `k_t ≥ 0` and the
budget `c_t + k_{t+1} = (R_kt + 1 − δ)k_t + w_tn_t + Π_t` (investment eliminated). -/
def rb_IsHHFeasible (δ : ℝ) (Rk w Pr c n k : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 0 < c t ω ∧ 0 ≤ n t ω ∧ n t ω < 1 ∧ 0 ≤ k t ω ∧
    c t ω + k (t + 1) ω = (Rk t ω + 1 - δ) * k t ω + w t ω * n t ω + Pr t ω

/-- The household's Euler equation `1/c_t = E_t[β(R_{k,t+1} + 1 − δ)/c_{t+1}]` (a.e.). -/
def rb_HHEuler (μ : Measure Ω) (ℱ : Filtration ℕ m0) (β δ : ℝ) (Rk c : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => 1 / c t ω) =ᵐ[μ] μ[fun ω => β * ((Rk (t + 1) ω + 1 - δ) / c (t + 1) ω) | ℱ t]

/-- The household's one-period inequality: with labour supply `χc/(1 − n) = w`,
`u(c', n') − u(c, n) ≤ (R_k + 1 − δ)/c·(k' − k) − (k'_1 − k_1)/c`. -/
theorem rb_household_pointwise {δ χ Rk w Pr c n k c' n' k' k₁ k₁' : ℝ} (hχ : 0 ≤ χ)
    (hc : 0 < c) (hn1 : n < 1) (hc' : 0 < c') (hn1' : n' < 1)
    (hb : c + k₁ = (Rk + 1 - δ) * k + w * n + Pr)
    (hb' : c' + k₁' = (Rk + 1 - δ) * k' + w * n' + Pr) (hls : χ * c / (1 - n) = w) :
    rb_u χ c' n' - rb_u χ c n ≤ (Rk + 1 - δ) / c * (k' - k) - 1 / c * (k₁' - k₁) := by
  have ht := rb_u_tangent hχ hc hn1 hc' hn1'
  have h1n : 0 < 1 - n := by linarith
  have hw : χ * ((n' - n) / (1 - n)) = w * (n' - n) / c := by
    rw [← hls]
    field_simp
  have : (c' - c) / c = (Rk + 1 - δ) / c * (k' - k) + w * (n' - n) / c - 1 / c * (k₁' - k₁) := by
    have hcc : c' - c = (Rk + 1 - δ) * (k' - k) + w * (n' - n) - (k₁' - k₁) := by linarith
    rw [hcc]
    field_simp
  linarith

/-- **Household sufficiency** (Miao, p. 460 and p. 472): a feasible plan with `n_t > 0`,
`k_{t+1}` `ℱ_t`-measurable, labour supply (14.36) and the household Euler equation satisfies,
against every feasible adapted alternative with the same `k_0`,
`∑_{t≤T} βᵗE[u'_t] ≤ ∑_{t≤T} βᵗE[u_t] + βᵀE[k_{T+1}/c_T]`. -/
theorem rb_household_suff (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {β δ χ : ℝ} (hβ : 0 ≤ β) (hχ : 0 ≤ χ) {Rk w Pr c n k c' n' k' : ℕ → Ω → ℝ}
    (hF : rb_IsHHFeasible δ Rk w Pr c n k)
    (hls : ∀ t ω, χ * c t ω / (1 - n t ω) = w t ω) (heul : rb_HHEuler μ ℱ β δ Rk c)
    (hkm : ∀ t, StronglyMeasurable[ℱ t] (k (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (c t ω) (n t ω)) μ)
    (hAi : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω) μ)
    (hAk : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k t ω) μ)
    (hBk : ∀ t, Integrable (fun ω => k (t + 1) ω / c t ω) μ)
    (hF' : rb_IsHHFeasible δ Rk w Pr c' n' k') (h0 : ∀ ω, k' 0 ω = k 0 ω)
    (hkm' : ∀ t, StronglyMeasurable[ℱ t] (k' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (c' t ω) (n' t ω)) μ)
    (hAk' : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k' t ω) μ)
    (hBk' : ∀ t, Integrable (fun ω => k' (t + 1) ω / c t ω) μ) (T : ℕ) :
    rb_value μ β χ c' n' T ≤
      rb_value μ β χ c n T + β ^ T * ∫ ω, k (T + 1) ω / c T ω ∂μ := by
  set d : ℕ → Ω → ℝ := fun t ω => rb_u χ (c' t ω) (n' t ω) - rb_u χ (c t ω) (n t ω)
  set Δ : ℕ → Ω → ℝ := fun t ω => k' t ω - k t ω
  set A : ℕ → Ω → ℝ := fun t ω => (Rk t ω + 1 - δ) / c t ω
  set B : ℕ → Ω → ℝ := fun t ω => 1 / c t ω
  have hBΔ : ∀ t, Integrable (fun ω => B t ω * Δ (t + 1) ω) μ := fun t =>
    ((hBk' t).sub (hBk t)).congr (Eventually.of_forall fun ω => by
      simp only [B, Δ, Pi.sub_apply]; ring)
  have hcore := rb_suff_core μ ℱ hβ d A B Δ
    (fun t ω => by
      obtain ⟨hc, -, hn1, -, hb⟩ := hF t ω
      obtain ⟨hc', -, hn1', -, hb'⟩ := hF' t ω
      exact rb_household_pointwise hχ hc hn1 hc' hn1' hb hb' (hls t ω))
    (fun ω => by simp [Δ, h0]) (fun t => (hkm' t).sub (hkm t))
    (fun t => heul t) (fun t => (hui' t).sub (hui t))
    (fun t => ((hAk' t).sub (hAk t)).congr (Eventually.of_forall fun ω => by
      simp only [A, Δ, Pi.sub_apply]; ring)) hBΔ hAi T
  have hsplit : ∀ t, ∫ ω, d t ω ∂μ =
      ∫ ω, rb_u χ (c' t ω) (n' t ω) ∂μ - ∫ ω, rb_u χ (c t ω) (n t ω) ∂μ :=
    fun t => integral_sub (hui' t) (hui t)
  have hlast : -β ^ T * ∫ ω, B T ω * Δ (T + 1) ω ∂μ ≤
      β ^ T * ∫ ω, k (T + 1) ω / c T ω ∂μ := by
    have hint : ∫ ω, B T ω * Δ (T + 1) ω ∂μ =
        ∫ ω, k' (T + 1) ω / c T ω ∂μ - ∫ ω, k (T + 1) ω / c T ω ∂μ := by
      rw [← integral_sub (hBk' T) (hBk T)]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [B, Δ]; ring)
    have hpos : 0 ≤ ∫ ω, k' (T + 1) ω / c T ω ∂μ :=
      integral_nonneg fun ω => div_nonneg (hF' (T + 1) ω).2.2.2.1 (hF T ω).1.le
    rw [hint]
    have := pow_nonneg hβ T
    nlinarith
  simp only [hsplit] at hcore
  unfold rb_value
  have hs : ∑ t ∈ Finset.range (T + 1), β ^ t * (∫ ω, rb_u χ (c' t ω) (n' t ω) ∂μ -
      ∫ ω, rb_u χ (c t ω) (n t ω) ∂μ) =
      ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (c' t ω) (n' t ω) ∂μ -
        ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (c t ω) (n t ω) ∂μ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hs] at hcore
  linarith

/-- **Household optimality**: under the hypotheses of `rb_household_suff` and the
transversality condition `βᵀE[k_{T+1}/c_T] → 0`, if the expected discounted utilities converge
(to `V`, `V'`), then `V' ≤ V`. -/
theorem rb_household_optimal (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {β δ χ : ℝ} (hβ : 0 ≤ β) (hχ : 0 ≤ χ) {Rk w Pr c n k c' n' k' : ℕ → Ω → ℝ}
    (hF : rb_IsHHFeasible δ Rk w Pr c n k)
    (hls : ∀ t ω, χ * c t ω / (1 - n t ω) = w t ω) (heul : rb_HHEuler μ ℱ β δ Rk c)
    (htvc : rb_TVC μ β c k) (hkm : ∀ t, StronglyMeasurable[ℱ t] (k (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (c t ω) (n t ω)) μ)
    (hAi : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω) μ)
    (hAk : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k t ω) μ)
    (hBk : ∀ t, Integrable (fun ω => k (t + 1) ω / c t ω) μ)
    (hF' : rb_IsHHFeasible δ Rk w Pr c' n' k') (h0 : ∀ ω, k' 0 ω = k 0 ω)
    (hkm' : ∀ t, StronglyMeasurable[ℱ t] (k' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (c' t ω) (n' t ω)) μ)
    (hAk' : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k' t ω) μ)
    (hBk' : ∀ t, Integrable (fun ω => k' (t + 1) ω / c t ω) μ) {V V' : ℝ}
    (hV : Tendsto (rb_value μ β χ c n) atTop (𝓝 V))
    (hV' : Tendsto (rb_value μ β χ c' n') atTop (𝓝 V')) : V' ≤ V := by
  have hlim : Tendsto (fun T => rb_value μ β χ c n T + β ^ T * ∫ ω, k (T + 1) ω / c T ω ∂μ)
      atTop (𝓝 (V + 0)) := hV.add htvc
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' hV' hlim fun T =>
    rb_household_suff μ ℱ hβ hχ hF hls heul hkm hui hAi hAk hBk hF' h0 hkm' hui' hAk' hBk' T

/-- A sequential competitive equilibrium of the basic RBC model (Miao, pp. 460–461 and
p. 472): the household's budget, labour supply (14.36) and Euler equation hold, the firm
maximises profit `z_tK^αN^{1−α} − R_ktK − w_tN` at `(k_t, n_t)` over all `K, N ≥ 0`, and the
household receives the profit `Π_t`. -/
def rb_IsSCE (μ : Measure Ω) (ℱ : Filtration ℕ m0) (α β δ χ : ℝ)
    (z c n k Rk w Pr : ℕ → Ω → ℝ) : Prop :=
  rb_IsHHFeasible δ Rk w Pr c n k ∧ (∀ t ω, χ * c t ω / (1 - n t ω) = w t ω) ∧
    rb_HHEuler μ ℱ β δ Rk c ∧
    (∀ t ω K' N', 0 ≤ K' → 0 ≤ N' → rb_profit α (z t ω) (Rk t ω) (w t ω) K' N' ≤
      rb_profit α (z t ω) (Rk t ω) (w t ω) (k t ω) (n t ω)) ∧
    (∀ t ω, Pr t ω = rb_profit α (z t ω) (Rk t ω) (w t ω) (k t ω) (n t ω))

/-- **Equivalence of the decentralised equilibrium and the planner's conditions** (Miao,
p. 472). For a positive allocation (`k_t, n_t > 0`), `(c, n, k)` with prices `(R_k, w, Π)` is a
sequential competitive equilibrium iff `R_kt = αz_tk_t^{α−1}n_t^{1−α}`,
`w_t = (1 − α)z_tk_t^αn_t^{−α}`, `Π_t = 0`, and the allocation is feasible for the planner and
satisfies (14.26) and (14.27). -/
theorem rb_sce_iff (μ : Measure Ω) (ℱ : Filtration ℕ m0) {α β δ χ : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {z c n k Rk w Pr : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω)
    (hk : ∀ t ω, 0 < k t ω) (hn : ∀ t ω, 0 < n t ω) :
    rb_IsSCE μ ℱ α β δ χ z c n k Rk w Pr ↔
      ((∀ t ω, Rk t ω = rb_MPK α (z t ω) (k t ω) (n t ω)) ∧
        (∀ t ω, w t ω = rb_MPL α (z t ω) (k t ω) (n t ω)) ∧ (∀ t ω, Pr t ω = 0)) ∧
      rb_IsFeasible α δ z c n k ∧ (∀ t ω, eq_14_27 α χ (z t ω) (k t ω) (c t ω) (n t ω)) ∧
      eq_14_26 μ ℱ α β δ z c n k := by
  constructor
  · rintro ⟨hb, hls, heul, hfirm, hpr⟩
    have hp : ∀ t ω, Rk t ω = rb_MPK α (z t ω) (k t ω) (n t ω) ∧
        w t ω = rb_MPL α (z t ω) (k t ω) (n t ω) := fun t ω =>
      rb_firm_foc (hk t ω) (hn t ω) (hfirm t ω)
    have hRk : Rk = fun t ω => rb_MPK α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => (hp t ω).1
    have hw : w = fun t ω => rb_MPL α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => (hp t ω).2
    subst hRk hw
    have hPr : ∀ t ω, Pr t ω = 0 := fun t ω => by
      rw [hpr t ω]
      exact (rb_firm_optimal hα0 hα1 (hz t ω) (hk t ω) (hn t ω)).1
    refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl, hPr⟩, fun t ω => ?_, fun t ω => hls t ω,
      fun t => heul t⟩
    obtain ⟨hc, hn0, hn1, hk0, hbud⟩ := hb t ω
    refine ⟨hc, hn0, hn1, hk0, ?_⟩
    rw [hbud, hPr t ω, ← rb_euler_thm α (z t ω) (hk t ω) (hn t ω)]
    ring
  · rintro ⟨⟨hRk, hw, hPr⟩, hF, hfoc, heul⟩
    have hRk' : Rk = fun t ω => rb_MPK α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => hRk t ω
    have hw' : w = fun t ω => rb_MPL α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => hw t ω
    subst hRk' hw'
    refine ⟨fun t ω => ?_, fun t ω => hfoc t ω, fun t => heul t, fun t ω K' N' hK' hN' => ?_,
      fun t ω => ?_⟩
    · obtain ⟨hc, hn0, hn1, hk0, hres⟩ := hF t ω
      refine ⟨hc, hn0, hn1, hk0, ?_⟩
      rw [hres, hPr t ω, ← rb_euler_thm α (z t ω) (hk t ω) (hn t ω)]
      ring
    · obtain ⟨h1, h2⟩ := rb_firm_optimal hα0 hα1 (hz t ω) (hk t ω) (hn t ω)
      rw [h1]
      exact h2 K' N' hK' hN'
    · rw [hPr t ω, (rb_firm_optimal hα0 hα1 (hz t ω) (hk t ω) (hn t ω)).1]

/-- **First welfare theorem** (Miao, p. 472): an equilibrium allocation with positive capital
and hours satisfying transversality (and the integrability hypotheses) is optimal for the
planner. -/
theorem rb_sce_optimal (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {α β δ χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hχ : 0 ≤ χ)
    {z c n k Rk w Pr C' N' K' : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω)
    (hk : ∀ t ω, 0 < k t ω) (hn : ∀ t ω, 0 < n t ω)
    (hE : rb_IsSCE μ ℱ α β δ χ z c n k Rk w Pr) (htvc : rb_TVC μ β c k)
    (hkm : ∀ t, StronglyMeasurable[ℱ t] (k (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (c t ω) (n t ω)) μ)
    (hAi : ∀ t, Integrable (rb_A α δ z c n k t) μ)
    (hAK : ∀ t, Integrable (fun ω => rb_A α δ z c n k t ω * k t ω) μ)
    (hBK : ∀ t, Integrable (fun ω => k (t + 1) ω / c t ω) μ)
    (hF' : rb_IsFeasible α δ z C' N' K') (h0 : ∀ ω, K' 0 ω = k 0 ω)
    (hKm' : ∀ t, StronglyMeasurable[ℱ t] (K' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (C' t ω) (N' t ω)) μ)
    (hAK' : ∀ t, Integrable (fun ω => rb_A α δ z c n k t ω * K' t ω) μ)
    (hBK' : ∀ t, Integrable (fun ω => K' (t + 1) ω / c t ω) μ) {V V' : ℝ}
    (hV : Tendsto (rb_value μ β χ c n) atTop (𝓝 V))
    (hV' : Tendsto (rb_value μ β χ C' N') atTop (𝓝 V')) : V' ≤ V := by
  obtain ⟨-, hF, hfoc, heul⟩ := (rb_sce_iff μ ℱ hα0 hα1 hz hk hn).1 hE
  exact rb_planner_optimal μ ℱ hα0 hα1 hβ hχ hz hF hk hn hfoc heul htvc hkm hui hAi hAK hBK
    hF' h0 hKm' hui' hAK' hBK' hV hV'

/-- Non-vacuity of `rb_IsSCE`: the full-depreciation solution of `rb_bm_solution` with the
marginal-product prices and zero profit is a sequential competitive equilibrium. -/
theorem rb_bm_sce (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hχ : 0 < χ)
    {zs : ℕ → ℝ} (hzs : ∀ t, 0 < zs t) {k0 : ℝ} (hk0 : 0 < k0) :
    rb_IsSCE μ ℱ α β 1 χ (fun t _ => zs t) (fun t _ => rb_bmC α β χ zs k0 t)
      (fun _ _ => rb_bmN α β χ) (fun t _ => rb_bmK α β χ zs k0 t)
      (fun t _ => rb_MPK α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ))
      (fun t _ => rb_MPL α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)) (fun _ _ => 0) := by
  obtain ⟨hF, hK, hN, hfoc, heul, -⟩ :=
    rb_bm_solution (Ω := Ω) μ ℱ hα0 hα1 hβ0 hβ1 hχ hzs hk0
  exact (rb_sce_iff μ ℱ hα0 hα1 (fun t _ => (hzs t).le) hK hN).2
    ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, hF, hfoc, heul⟩

end Miao.NeoclassicalGrowth
