/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.Mangasarian
import RamseyCassKoopmans.Stationary

/-!
# The neoclassical growth model in continuous time: the planner

AKMM, §9.3.2 (pp. 253–255) and Appendix 9.A.4 (pp. 846–848).

* (9.35): with CRRA utility the first-order conditions give `ċ/c = (f'(k) − (δ + ρ))/σ`
  (`eq_9_35`, from `eq_9_26` with `r = f'(k) − δ`).
* Figure 9.2: `k̇ > 0` iff `c < f(k) − δk`, and `ċ > 0` iff `k < k**`
  (`ramseyPlanner_phase_signs`); the modified golden rule `f'(k**) = δ + ρ` has a unique
  positive solution, below the golden rule `f'(k_gold) = δ`, which maximizes steady-state
  consumption (footnote 3; `ramseyPlanner_modified_golden_rule`, from EconomicGrowth's
  `existsUnique_stationary_capital_of_inada`, `stationary_capital_lt_golden_rule_of_strictConcave`
  and `golden_rule_strictly_maximizes_consumption`).
* A path converging to the steady state satisfies the TVC (9.34)
  (`ramseyPlanner_tvc_of_convergent`); a path reaching `k = 0` with positive consumption becomes
  infeasible immediately (`ramseyPlanner_zero_capital_infeasible`).
* Appendix 9.A.4: from (9.A.1)–(9.A.2), (9.A.3)–(9.A.4)
  `u'(c(T)) = u'(c(0))exp(−∫_0^T (f'(k) − (δ + ρ)))` and (9.A.5) ⇔ (9.A.6)
  (`appendix_9A4_marginal_utility`, `appendix_9A4_tvc_iff`); on the saddle path
  `∫_0^T (f'(k) − δ) → ∞` and (9.A.6) holds (`appendix_9A4_saddle_tvc`); a path that enters
  the region `f'(k) < δ` for good while `k` stays away from zero violates it
  (`appendix_9A4_below_saddle_violates_tvc`, instance `appendix_9A4_below_saddle_instance`).
  That a path starting below the saddle path does enter that region is read off the phase
  diagram in the book; it is proved in `RamseyPhase` (`ramseyPhase_below_saddle`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.35), p. 254: with CRRA utility (`u'(c) = c^{−σ}`), the first-order conditions
`μ = e^{−ρt}c^{−σ}` and `μ̇ + μ(f'(k) − δ) = 0` give the Euler equation
`ċ/c = (f'(k) − (δ + ρ))/σ`. -/
theorem eq_9_35 {ρ σ δ t cdot μdot fk : ℝ} {c μ : ℝ → ℝ} (hσ : σ ≠ 0) (hc0 : 0 < c t)
    (hc : HasDerivAt c cdot t) (hμ : μ =ᶠ[𝓝 t] fun s => Real.exp (-ρ * s) * c s ^ (-σ))
    (hμd : HasDerivAt μ μdot t) (hfoc : (fk - δ) * μ t + μdot = 0) :
    cdot / c t = (fk - (δ + ρ)) / σ := by
  have hu' : HasDerivAt (fun x : ℝ => x ^ (-σ)) (-σ * c t ^ (-σ - 1)) (c t) :=
    Real.hasDerivAt_rpow_const (Or.inl hc0.ne')
  have h := (eq_9_26 (u' := fun x => x ^ (-σ)) hc hu' hμ hμd hfoc
    (Real.rpow_pos_of_pos hc0 _).ne' hc0.ne').2.2.2
  rw [continuousHamiltonian_crra_relative_risk_aversion hc0] at h
  rw [eq_div_iff hσ]
  linarith

/-- AKMM, p. 254, Figure 9.2: the phase-diagram signs. `k̇ = f(k) − δk − c > 0` iff
`c < f(k) − δk`; and with `f'` strictly decreasing, `σ > 0`, `c > 0` and `f'(k**) = δ + ρ`, the
consumption drift `c(f'(k) − (δ + ρ))/σ` is positive iff `k < k**` and zero iff `k = k**`. -/
theorem ramseyPlanner_phase_signs {f fp : ℝ → ℝ} {δ ρ σ kss k c : ℝ}
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hσ : 0 < σ) (hc : 0 < c) (hk : 0 < k)
    (hkss : 0 < kss) (hss : fp kss = δ + ρ) :
    (0 < f k - δ * k - c ↔ c < f k - δ * k) ∧
      (0 < c * (fp k - (δ + ρ)) / σ ↔ k < kss) ∧ (c * (fp k - (δ + ρ)) / σ = 0 ↔ k = kss) := by
  refine ⟨by constructor <;> intro h <;> linarith, ?_, ?_⟩
  · rw [div_pos_iff_of_pos_right hσ, mul_pos_iff_of_pos_left hc, sub_pos, ← hss]
    exact hanti.lt_iff_gt hkss hk
  · rw [div_eq_zero_iff, mul_eq_zero, sub_eq_zero, ← hss]
    simp only [hc.ne', hσ.ne', false_or, or_false]
    exact hanti.injOn.eq_iff hk hkss

/-- AKMM, p. 255 and footnote 3: for a strictly concave neoclassical `f` and `δ, ρ > 0`, the
modified golden rule `f'(k**) = δ + ρ` has a unique positive solution; it lies strictly below
any golden-rule stock `f'(k_gold) = δ`; and the golden rule strictly maximizes steady-state
consumption `f(k) − δk` over `k ≥ 0`. -/
theorem ramseyPlanner_modified_golden_rule {f : ℝ → ℝ} {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hcont : ContinuousOn (deriv f) (Set.Ioi 0))
    (h0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop) (htop : Tendsto (deriv f) atTop (𝓝 0)) :
    (∃! kss : ℝ, 0 < kss ∧ deriv f kss = ρ + δ) ∧
      (∀ kss kgold : ℝ, 0 < kss → 0 < kgold → deriv f kss = ρ + δ → deriv f kgold = δ →
        kss < kgold ∧ ∀ k, 0 ≤ k → k ≠ kgold → f k - δ * k < f kgold - δ * kgold) := by
  refine ⟨RamseyCassKoopmans.existsUnique_stationary_capital_of_inada f ρ δ (by linarith) hconc
    hdiff hcont h0 htop, fun kss kgold hkss hkg hss hg => ⟨?_, fun k hk hne => ?_⟩⟩
  · exact RamseyCassKoopmans.stationary_capital_lt_golden_rule_of_strictConcave f kss kgold ρ δ
      hconc hdiff hkss hkg hρ hss hg
  · exact RamseyCassKoopmans.golden_rule_strictly_maximizes_consumption f kgold k δ hconc hkg hk
      hne (hdiff kgold hkg) hg

/-- AKMM, p. 255: "this dynamic also satisfies the TVC (9.34), because `k(t)` and `c(t)` become
constant in the long run": if `k → k̄`, `c → c̄ > 0`, `u'` is continuous at `c̄` and `ρ > 0`, then
`e^{−ρT}u'(c(T))k(T) → 0`. -/
theorem ramseyPlanner_tvc_of_convergent {ρ kbar cbar : ℝ} {u' k c : ℝ → ℝ} (hρ : 0 < ρ)
    (hk : Tendsto k atTop (𝓝 kbar)) (hc : Tendsto c atTop (𝓝 cbar))
    (hu' : ContinuousAt u' cbar) :
    Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0) := by
  have h := ((mangasarian_exp_neg_tendsto hρ).mul (hu'.tendsto.comp hc)).mul hk
  simpa using h

/-- AKMM, p. 255: a path along which capital reaches `k(T) = 0` while consumption `c(T) > 0`
(with `f(0) = 0`) has `k̇(T) = −c(T) < 0`, so capital is negative immediately after `T`: such a
path, with `c` following the Euler equation, is not feasible. -/
theorem ramseyPlanner_zero_capital_infeasible {f : ℝ → ℝ} {δ T : ℝ} {k c : ℝ → ℝ}
    (hf0 : f 0 = 0) (hkT : k T = 0) (hcT : 0 < c T)
    (hk : HasDerivAt k (f (k T) - δ * k T - c T) T) :
    ∀ᶠ t in 𝓝[>] T, k t < 0 := by
  rw [hkT, hf0, mul_zero, sub_zero, zero_sub] at hk
  have hs := (hasDerivAt_iff_tendsto_slope.mp hk).mono_left
    (nhdsWithin_mono T fun x (hx : T < x) => ne_of_gt hx)
  have hneg : ∀ᶠ t in 𝓝[>] T, (t - T)⁻¹ • (k t - k T) < 0 := by
    have := hs.eventually (gt_mem_nhds (neg_lt_zero.mpr hcT))
    filter_upwards [this] with t ht
    rwa [slope_def_module] at ht
  filter_upwards [hneg, self_mem_nhdsWithin] with t h1 h2
  have h2' : 0 < t - T := sub_pos.mpr h2
  rw [smul_eq_mul, hkT, sub_zero] at h1
  have := (mul_neg_iff.mp h1).resolve_right (fun h => (not_lt.mpr (inv_pos.mpr h2').le) h.1)
  exact this.2

/-- AKMM, (9.A.1)–(9.A.4), pp. 846–847: if `μ = e^{−ρt}u'(c)` (9.A.1) and
`μ̇ = −μ r(t)` with `r(t) = f'(k(t)) − δ` (9.A.2), `r` continuous, then
`μ(T) = μ(0)exp(−∫_0^T r)` and, with `A = u'(c(0))`,
(9.A.4) `u'(c(T)) = A exp(−∫_0^T (r − ρ))`; taking logs, (9.A.3)
`log u'(c(T)) − log u'(c(0)) = −∫_0^T (r − ρ)` when `u'(c) > 0`. -/
theorem appendix_9A4_marginal_utility {ρ : ℝ} {r μ u' c : ℝ → ℝ} (hr : Continuous r)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * r t)) t) {T : ℝ} (hT : 0 ≤ T) :
    μ T = μ 0 * Real.exp (-∫ s in (0 : ℝ)..T, r s) ∧
      u' (c T) = u' (c 0) * Real.exp (-∫ s in (0 : ℝ)..T, (r s - ρ)) ∧
      (0 < u' (c 0) → Real.log (u' (c T)) - Real.log (u' (c 0)) =
        -∫ s in (0 : ℝ)..T, (r s - ρ)) := by
  have hR : ∀ t, HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, r s) (r t) t := fun t =>
    (hr.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℝ := fun t => μ t * Real.exp (∫ s in (0 : ℝ)..t, r s)
  have hg : ∀ t, 0 ≤ t → HasDerivAt g 0 t := fun t ht => by
    have := (h9A2 t ht).mul (hR t).exp
    convert this using 1
    ring
  have hcont : ContinuousOn g (Set.Icc 0 T) := fun t ht =>
    (hg t ht.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun t ht => (hg t ht.1).hasDerivWithinAt
  have h := hconst T ⟨hT, le_rfl⟩
  simp only [g, intervalIntegral.integral_same, Real.exp_zero, mul_one] at h
  have h1 : μ T = μ 0 * Real.exp (-∫ s in (0 : ℝ)..T, r s) := by
    rw [← h, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hsub : ∫ s in (0 : ℝ)..T, (r s - ρ) = (∫ s in (0 : ℝ)..T, r s) - ρ * T := by
    rw [intervalIntegral.integral_sub (hr.intervalIntegrable 0 T)
      (intervalIntegrable_const (μ := MeasureTheory.volume))]
    simp [mul_comm]
  have h2 : u' (c T) = u' (c 0) * Real.exp (-∫ s in (0 : ℝ)..T, (r s - ρ)) := by
    have e1 := h9A1 T hT
    have e0 := h9A1 0 le_rfl
    simp only [mul_zero, Real.exp_zero, one_mul] at e0
    rw [h1, e0] at e1
    rw [hsub]
    have hE := Real.exp_pos (-ρ * T)
    have : u' (c T) = Real.exp (ρ * T) * (u' (c 0) * Real.exp (-∫ s in (0 : ℝ)..T, r s)) := by
      rw [e1, ← mul_assoc, ← Real.exp_add]
      simp
    rw [this, show -((∫ s in (0 : ℝ)..T, r s) - ρ * T) = ρ * T + -∫ s in (0 : ℝ)..T, r s by ring,
      Real.exp_add]
    ring
  refine ⟨h1, h2, fun hpos => ?_⟩
  rw [h2, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- AKMM, (9.A.5)–(9.A.6), p. 847: under (9.A.1)–(9.A.2) and `u'(c(0)) > 0`, the TVC (9.A.5)
`lim e^{−ρT}u'(c(T))k(T) = 0` is equivalent to (9.A.6) `lim exp(−∫_0^T (f'(k) − δ))k(T) = 0`. -/
theorem appendix_9A4_tvc_iff {ρ : ℝ} {r μ u' c k : ℝ → ℝ} (hr : Continuous r)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * r t)) t) (hA : 0 < u' (c 0)) :
    Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0) ↔
      Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) atTop (𝓝 0) := by
  have e : ∀ T, 0 ≤ T → Real.exp (-ρ * T) * u' (c T) * k T =
      u' (c 0) * (Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) := fun T hT => by
    rw [← h9A1 T hT, (appendix_9A4_marginal_utility hr h9A1 h9A2 hT).1, h9A1 0 le_rfl]
    simp only [mul_zero, Real.exp_zero, one_mul]
    ring
  have hev : ∀ᶠ T in atTop, Real.exp (-ρ * T) * u' (c T) * k T =
      u' (c 0) * (Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) :=
    (eventually_ge_atTop 0).mono e
  rw [tendsto_congr' hev]
  constructor
  · intro h
    have := h.const_mul (u' (c 0))⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hA.ne'] using this
  · intro h
    simpa using h.const_mul (u' (c 0))

/-- AKMM, Appendix 9.A.4, p. 847, on the saddle path: if `r(t) = f'(k(t)) − δ → ρ > 0` (because
`k → k̄` with `f'(k̄) = δ + ρ`) and `k(T) → k̄`, then `∫_0^T r → ∞` and (9.A.6) holds. -/
theorem appendix_9A4_saddle_tvc {ρ kbar : ℝ} {r k : ℝ → ℝ} (hρ : 0 < ρ) (hr : Continuous r)
    (hrlim : Tendsto r atTop (𝓝 ρ)) (hk : Tendsto k atTop (𝓝 kbar)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, r s) atTop atTop ∧
      Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) atTop (𝓝 0) := by
  obtain ⟨that, hthat⟩ := eventually_atTop.mp (hrlim.eventually (lt_mem_nhds (half_lt_self hρ)))
  have hlow : ∀ T, max that 0 ≤ T → (∫ s in (0 : ℝ)..max that 0, r s) + ρ / 2 * (T - max that 0)
      ≤ ∫ s in (0 : ℝ)..T, r s := by
    intro T hT
    rw [← intervalIntegral.integral_add_adjacent_intervals (hr.intervalIntegrable 0 (max that 0))
      (hr.intervalIntegrable (max that 0) T)]
    have hm : ρ / 2 * (T - max that 0) ≤ ∫ s in max that 0..T, r s := by
      have := intervalIntegral.integral_mono_on hT
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := ρ / 2))
        (hr.intervalIntegrable _ _) fun s hs => (hthat s ((le_max_left _ _).trans hs.1)).le
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    linarith
  have htop : Tendsto (fun T => ∫ s in (0 : ℝ)..T, r s) atTop atTop := by
    refine tendsto_atTop_mono' atTop ((eventually_ge_atTop (max that 0)).mono hlow) ?_
    have h1 : Tendsto (fun T : ℝ => ρ / 2 * (T - max that 0)) atTop atTop :=
      ((tendsto_atTop_add_const_right atTop (-max that 0) tendsto_id).const_mul_atTop
        (half_pos hρ)).congr fun T => by simp [sub_eq_add_neg]
    exact tendsto_atTop_add_const_left atTop _ h1
  refine ⟨htop, ?_⟩
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop).mul hk
  simpa using this

/-- AKMM, Appendix 9.A.4, pp. 847–848, below the saddle path: if after some `t̄` the path stays
in the region `r(t) = f'(k(t)) − δ ≤ 0` (capital above the golden rule) and capital stays
above some `κ > 0`, then `exp(−∫_0^T r)k(T) ≥ exp(−∫_0^{t̄} r)κ > 0` for `T ≥ t̄`, so (9.A.6), and
hence the TVC, fails. -/
theorem appendix_9A4_below_saddle_violates_tvc {tbar κ : ℝ} {r k : ℝ → ℝ} (hr : Continuous r)
    (hneg : ∀ t, tbar ≤ t → r t ≤ 0) (hκ : 0 < κ) (hk : ∀ t, tbar ≤ t → κ ≤ k t) :
    (∀ T, tbar ≤ T → Real.exp (-∫ s in (0 : ℝ)..tbar, r s) * κ ≤
      Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) ∧
      ¬ Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) atTop (𝓝 0) := by
  have hbound : ∀ T, tbar ≤ T → Real.exp (-∫ s in (0 : ℝ)..tbar, r s) * κ ≤
      Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T := by
    intro T hT
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hr.intervalIntegrable (μ := MeasureTheory.volume) 0 tbar)
      (hr.intervalIntegrable (μ := MeasureTheory.volume) tbar T)
    have hle : ∫ s in tbar..T, r s ≤ 0 := by
      have := intervalIntegral.integral_mono_on hT (hr.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (0 : ℝ)))
        fun s hs => hneg s hs.1
      simpa using this
    have hexp : Real.exp (-∫ s in (0 : ℝ)..tbar, r s) ≤ Real.exp (-∫ s in (0 : ℝ)..T, r s) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul hexp (hk T hT) hκ.le (Real.exp_pos _).le
  refine ⟨hbound, fun hlim => ?_⟩
  have hpos : 0 < Real.exp (-∫ s in (0 : ℝ)..tbar, r s) * κ := mul_pos (Real.exp_pos _) hκ
  obtain ⟨T, hT⟩ := ((hlim.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop tbar)).exists
  linarith [hbound T hT.2]

/-- AKMM, Appendix 9.A.4: the hypotheses of `appendix_9A4_below_saddle_violates_tvc` are
satisfiable: `r ≡ −1` (a capital stock above the golden rule) and `k ≡ 1`. -/
theorem appendix_9A4_below_saddle_instance :
    ¬ Tendsto (fun T => Real.exp (-∫ _ in (0 : ℝ)..T, (-1 : ℝ)) * (1 : ℝ)) atTop (𝓝 0) :=
  (appendix_9A4_below_saddle_violates_tvc (tbar := 0) (k := fun _ => 1) continuous_const
    (fun _ _ => by norm_num) one_pos fun _ _ => le_rfl).2

end AKMM.ContinuousTime
