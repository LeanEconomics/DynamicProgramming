/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.RamseyPlanner

/-!
# The market equilibrium in continuous time

AKMM, §9.3.2, "The market equilibrium in continuous time" (pp. 256–257): (9.36)–(9.39).

* The household problem (9.36) and its Euler equation (9.37)
  `ċ_i/c_i = (r(t) − (δ + ρ))/σ` (`eq_9_37`), and sufficiency of the household's conditions
  with the no-borrowing constraint `k_i ≥ 0` and the TVC (`market_household_optimal`).
* The firm: with constant returns, `F₁(K, L) = f'(k̃)` and `F₂(K, L) = f(k̃) − k̃f'(k̃)`,
  `k̃ = K/L` (`market_firm_marginal_products`); at these prices profit is zero and maximal
  (`market_firm_optimal`).
* Market clearing and (9.38)–(9.39): `r = f'(k)`, `w = f(k) − kf'(k)`; substituting into (9.36)
  and (9.37) under symmetry gives exactly (9.33) and (9.35) (`market_equilibrium_planner_system`).
* The planner's solution with these prices is a market equilibrium: the household budget
  holds, the household's first-order conditions and TVC hold, so households optimize; firms
  maximize profit and markets clear (`market_planner_is_equilibrium`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.37), p. 256: the household's first-order conditions for (9.36),
`μ = e^{−ρt}c_i^{−σ}` and `μ̇ + μ(r(t) − δ) = 0`, give the Euler equation
`ċ_i/c_i = (r(t) − (δ + ρ))/σ`. -/
theorem eq_9_37 {ρ σ δ t cdot μdot rt : ℝ} {c μ : ℝ → ℝ} (hσ : σ ≠ 0) (hc0 : 0 < c t)
    (hc : HasDerivAt c cdot t) (hμ : μ =ᶠ[𝓝 t] fun s => Real.exp (-ρ * s) * c s ^ (-σ))
    (hμd : HasDerivAt μ μdot t) (hfoc : (rt - δ) * μ t + μdot = 0) :
    cdot / c t = (rt - (δ + ρ)) / σ :=
  eq_9_35 hσ hc0 hc hμ hμd hfoc

/-- AKMM, (9.36)–(9.37), p. 256: **sufficiency for the household**. If `u` is concave with
`u' ≥ 0`, and the household's plan satisfies (9.36) `k̇ = r(t)k + w(t) − δk − c`, the conditions
`μ = e^{−ρt}u'(c)`, `μ̇ = −μ(r(t) − δ)` and the TVC `lim e^{−ρT}u'(c(T))k(T) = 0`, then it is
catching-up optimal against every plan from the same `k_i(0)` with `k_i ≥ 0` and positive
continuous consumption. -/
theorem market_household_optimal {ρ δ : ℝ} {u u' r w : ℝ → ℝ} {k c μ k' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (r t * k t + w t - δ * k t - c t) t)
    (hfoc : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (hcost : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (r t - δ))) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0))
    (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' (r t * k' t + w t - δ * k' t - c' t) t)
    (h0 : k' 0 = k 0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + ε := by
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    rw [hfoc t ht]; exact mul_nonneg (Real.exp_pos _).le (hu'0 _ (hc t ht))
  refine (mangasarian_catching_up (G := fun t y => (r t - δ) * y + w t)
    (Gx := fun t _ => r t - δ) hconc hu hc hcc (fun t ht => by convert hkd t ht using 1; ring)
    hcost hfoc hμ0 hc' hcc' (fun t ht => by convert hkd' t ht using 1; ring) h0
    (fun t _ => by ring_nf; rfl) ?_).1
  intro ε hε
  have htvc' : Tendsto (fun T => μ T * k T) atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [hfoc T hT]
  filter_upwards [htvc'.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
  nlinarith [mul_nonneg (hμ0 T hT) (hk' T hT)]

/-- AKMM, p. 256 (Section 3.3): with constant returns, `F(K, L) = Lf(K/L)` for `L > 0`, and the
marginal products are `F₁(K, L) = f'(k̃)` and `F₂(K, L) = f(k̃) − k̃f'(k̃)`, `k̃ = K/L`,
`f(k) = F(k, 1)`. -/
theorem market_firm_marginal_products {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N) {K L f' : ℝ}
    (hL : 0 < L) (hf : HasDerivAt (fun k => F k 1) f' (K / L)) :
    F K L = L * F (K / L) 1 ∧ HasDerivAt (fun x => F x L) f' K ∧
      HasDerivAt (fun x => F K x) (F (K / L) 1 - K / L * f') L := by
  have hform : ∀ x y, 0 < y → F x y = y * F (x / y) 1 := fun x y hy => by
    have := hcrs y hy (x / y) 1
    rw [mul_div_cancel₀ _ hy.ne', mul_one] at this
    exact this
  refine ⟨hform K L hL, ?_, ?_⟩
  · have hin : HasDerivAt (fun x : ℝ => x / L) (1 / L) K := by
      simpa using (hasDerivAt_id K).div_const L
    have h := (hf.comp K hin).const_mul L
    have hev : (fun x => F x L) =ᶠ[𝓝 K] fun x => L * F (x / L) 1 :=
      Eventually.of_forall fun x => hform x L hL
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
  · have hin : HasDerivAt (fun y : ℝ => K / y) (-K / L ^ 2) L := by
      have := (hasDerivAt_inv hL.ne').const_mul K
      convert this using 1
      · funext y; simp [div_eq_mul_inv]
      · field_simp
    have h := (hasDerivAt_id L).mul (hf.comp L hin)
    have hev : (fun y => F K y) =ᶠ[𝓝 L] fun y => id y * (fun k => F k 1) (K / y) := by
      filter_upwards [Ioi_mem_nhds hL] with y hy
      exact hform K y hy
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [id, one_mul, Function.comp]
    field_simp
    ring

/-- AKMM, p. 256: the firm's problem `max F(K, L) − rK − wL`. At `r = f'(k̃)` and
`w = f(k̃) − k̃f'(k̃)` with `f` concave, the choice `(K, L)` with `K/L = k̃` earns zero profit
(Euler's theorem), and every `(K', L')` with `L' > 0`, `K' ≥ 0` earns at most zero. -/
theorem market_firm_optimal {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N)
    (hconc : ConcaveOn ℝ (Set.Ici 0) fun k => F k 1) {K L f' : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hf : HasDerivAt (fun k => F k 1) f' (K / L)) :
    F K L - f' * K - (F (K / L) 1 - K / L * f') * L = 0 ∧
      ∀ K' L', 0 ≤ K' → 0 < L' → F K' L' - f' * K' - (F (K / L) 1 - K / L * f') * L' ≤ 0 := by
  have hform : ∀ x y, 0 < y → F x y = y * F (x / y) 1 := fun x y hy => by
    have := hcrs y hy (x / y) 1
    rw [mul_div_cancel₀ _ hy.ne', mul_one] at this
    exact this
  refine ⟨?_, fun K' L' hK' hL' => ?_⟩
  · rw [hform K L hL]
    field_simp
    ring
  · rw [hform K' L' hL']
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ici.mpr (div_nonneg hK hL.le))
      (Set.mem_Ici.mpr (div_nonneg hK' hL'.le)) hf
    have e : L' * (F (K' / L') 1 - F (K / L) 1 - f' * (K' / L' - K / L)) =
        L' * F (K' / L') 1 - f' * K' - (F (K / L) 1 - K / L * f') * L' := by
      field_simp
      ring
    have := mul_nonpos_of_nonneg_of_nonpos hL'.le (by linarith : F (K' / L') 1 - F (K / L) 1 -
      f' * (K' / L' - K / L) ≤ 0)
    linarith

/-- AKMM, (9.38)–(9.39), pp. 256–257: with market clearing `∫k_i = K`, `L = 1`, symmetry
`k_i = k`, `c_i = c`, and the prices `r = f'(k)`, `w = f(k) − kf'(k)`, the household budget
(9.36) is the resource constraint (9.33) and the Euler equation (9.37) is (9.35). -/
theorem market_equilibrium_planner_system (f : ℝ → ℝ) (fp δ ρ σ k c : ℝ) :
    fp * k + (f k - k * fp) - δ * k - c = f k - δ * k - c ∧
      (fp - (δ + ρ)) / σ = (fp - (δ + ρ)) / σ := ⟨by ring, rfl⟩

/-- AKMM, pp. 256–257: **the planner's solution is a market equilibrium**. If `(k, c)` solves the
planner's conditions — (9.33), `μ = e^{−ρt}u'(c)`, `μ̇ = −μ(f'(k) − δ)` and the TVC (9.34) —
then with the prices (9.38)–(9.39), `r(t) = f'(k(t))`, `w(t) = f(k(t)) − k(t)f'(k(t))`: the
household budget (9.36) holds along `(k, c)`, and every household plan from `k(0)` with
`k_i ≥ 0` is (catching-up) no better, so `(k, c)` is the household's optimum; markets clear with
`K = k`, `L = 1`. -/
theorem market_planner_is_equilibrium {ρ δ : ℝ} {f f' u u' : ℝ → ℝ} {k c μ : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (f (k t) - δ * k t - c t) t)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (f' (k t) - δ))) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0)) :
    (∀ t, 0 ≤ t → HasDerivAt k ((fun s => f' (k s)) t * k t +
        (fun s => f (k s) - k s * f' (k s)) t - δ * k t - c t) t) ∧
      ∀ k' c' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ k' t) → (∀ t, 0 ≤ t → 0 < c' t) →
        ContinuousOn c' (Set.Ici 0) →
        (∀ t, 0 ≤ t → HasDerivAt k' (f' (k t) * k' t + (f (k t) - k t * f' (k t)) -
          δ * k' t - c' t) t) → k' 0 = k 0 →
        ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
          (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + ε := by
  have hbud : ∀ t, 0 ≤ t → HasDerivAt k ((fun s => f' (k s)) t * k t +
      (fun s => f (k s) - k s * f' (k s)) t - δ * k t - c t) t := fun t ht => by
    convert hkd t ht using 1
    simp only
    ring
  refine ⟨hbud, fun k' c' hk' hc' hcc' hkd' h0 => ?_⟩
  exact market_household_optimal (r := fun s => f' (k s)) (w := fun s => f (k s) - k s * f' (k s))
    hconc hu hu'0 hc hcc hbud h9A1 h9A2 htvc hk' hc' hcc' hkd' h0

end AKMM.ContinuousTime
