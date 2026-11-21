/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.RamseyPlanner
import RamseyCassKoopmans.CassGeneral
import RamseyCassKoopmans.CassPolicy
import RamseyCassKoopmans.CassRate
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The saddle path of the planner's problem

AKMM, §9.3.2 (p. 255): "Starting from `k(0)`, the social planner has to choose the value of
initial consumption `c(0)` that is on the saddle path … On the saddle path, `(k(t), c(t))`
gradually approaches the steady state … This dynamic also satisfies the TVC (9.34)".

EconomicGrowth's `RamseyCassKoopmans` library constructs, for every `k(0) > 0`, the unique
optimum of Cass's problem, in which gross investment is irreversible (`f(k) − c ≥ 0`), with a
price certificate. The book's planner may disinvest. `ramseySaddle_path` shows that whenever
the Cass optimum invests strictly throughout (in particular for every `0 < k(0) ≤ k**`), it is
the book's saddle path: it converges to `(k**, f(k**) − δk**)`, satisfies the first-order
conditions (9.A.1)–(9.A.2) with `μ = e^{−ρt}u'(c)`, the Euler equation in the form
`ċ = −(u'/u'')(c)(f'(k) − (δ + ρ))` (which is (9.35) for CRRA), and the TVC (9.34), and by
`mangasarian_planner` it is catching-up optimal against every feasible path of the book's
problem, including paths that disinvest.

`ramseySaddle_primitives` proves that the book's model, Cobb–Douglas `f(k) = k^α` with CRRA
utility, satisfies the library's assumptions (`CassPrimitives`), and
`ramseySaddle_crra_cobbDouglas` states the result for it, with (9.35) itself.
-/

namespace AKMM.ContinuousTime

open Filter Topology RamseyCassKoopmans

/-- The derivative of the power function `A y^p + B` at `y > 0`. -/
theorem ramseySaddle_power_hasDerivAt (A B p : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => A * x ^ p + B) (A * p * y ^ (p - 1)) y := by
  have h := ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hy.ne')).const_mul A).add_const B
  convert h using 1
  ring

/-- The first and second derivatives of `A y^p + B` on `(0, ∞)`, as functions near `x > 0`. -/
theorem ramseySaddle_power_derivs (A B p : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => A * y ^ p + B) =ᶠ[𝓝 x] (fun y => A * p * y ^ (p - 1)) ∧
      HasDerivAt (deriv fun y : ℝ => A * y ^ p + B) (A * p * (p - 1) * x ^ (p - 1 - 1)) x ∧
      deriv (deriv fun y : ℝ => A * y ^ p + B) x = A * p * (p - 1) * x ^ (p - 1 - 1) := by
  have hev : deriv (fun y : ℝ => A * y ^ p + B) =ᶠ[𝓝 x] (fun y => A * p * y ^ (p - 1)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (ramseySaddle_power_hasDerivAt A B p hy).deriv
  have hd : HasDerivAt (fun y : ℝ => A * p * y ^ (p - 1))
      (A * p * (p - 1) * x ^ (p - 1 - 1)) x := by
    have h := ramseySaddle_power_hasDerivAt (A * p) 0 (p - 1) hx
    simp only [add_zero] at h
    convert h using 1
  have hd' := hd.congr_of_eventuallyEq hev
  exact ⟨hev, hd', hd'.deriv⟩

/-- Analytic properties of `G(y) = A y^p + B` with `Ap > 0` and `p < 1` on `(0, ∞)`: positive
decreasing marginal value with continuous first and second derivatives, Inada limits, strict
concavity. -/
theorem ramseySaddle_power_props (A B p : ℝ) (hAp : 0 < A * p) (hp : p < 1) :
    (∀ y, 0 < y → DifferentiableAt ℝ (fun x : ℝ => A * x ^ p + B) y) ∧
      ContinuousOn (deriv fun x : ℝ => A * x ^ p + B) (Set.Ioi 0) ∧
      (∀ y, 0 < y → 0 < deriv (fun x : ℝ => A * x ^ p + B) y) ∧
      (∀ y, 0 < y → DifferentiableAt ℝ (deriv fun x : ℝ => A * x ^ p + B) y) ∧
      ContinuousOn (deriv (deriv fun x : ℝ => A * x ^ p + B)) (Set.Ioi 0) ∧
      (∀ y, 0 < y → deriv (deriv fun x : ℝ => A * x ^ p + B) y < 0) ∧
      Tendsto (deriv fun x : ℝ => A * x ^ p + B) (𝓝[>] (0 : ℝ)) atTop ∧
      Tendsto (deriv fun x : ℝ => A * x ^ p + B) atTop (𝓝 0) ∧
      StrictConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => A * x ^ p + B) := by
  set G : ℝ → ℝ := fun x => A * x ^ p + B
  have hD : ∀ y, 0 < y → deriv G y = A * p * y ^ (p - 1) := fun y hy =>
    (ramseySaddle_power_hasDerivAt A B p hy).deriv
  have hD2 : ∀ y, 0 < y → deriv (deriv G) y = A * p * (p - 1) * y ^ (p - 1 - 1) := fun y hy =>
    (ramseySaddle_power_derivs A B p hy).2.2
  have hneg2 : ∀ y, 0 < y → deriv (deriv G) y < 0 := fun y hy => by
    rw [hD2 y hy]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hAp (by linarith))
      (Real.rpow_pos_of_pos hy _)
  have hp1 : p - 1 < 0 := by linarith
  refine ⟨fun y hy => (ramseySaddle_power_hasDerivAt A B p hy).differentiableAt,
    fun y hy => ((ramseySaddle_power_derivs A B p hy).2.1).continuousAt.continuousWithinAt,
    fun y hy => by rw [hD y hy]; exact mul_pos hAp (Real.rpow_pos_of_pos hy _),
    fun y hy => ((ramseySaddle_power_derivs A B p hy).2.1).differentiableAt, ?_, hneg2, ?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun y : ℝ => A * p * (p - 1) * y ^ (p - 1 - 1)) (Set.Ioi 0) :=
      fun y hy => ((ramseySaddle_power_hasDerivAt (A * p * (p - 1)) 0 (p - 1 - 1) hy).congr_deriv
        rfl |>.continuousAt.congr (by filter_upwards with z; simp)).continuousWithinAt
    exact hc.congr fun y hy => hD2 y hy
  · have h := (tendsto_rpow_neg_nhdsGT_zero hp1).const_mul_atTop hAp
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hD y hy).symm
  · have h := (tendsto_rpow_neg_atTop (y := 1 - p) (by linarith)).const_mul (A * p)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [hD y hy, neg_sub]
  · refine strictConcaveOn_of_deriv2_neg (convex_Ioi 0) (fun y hy =>
      (ramseySaddle_power_hasDerivAt A B p hy).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Ioi] at hy
    simpa [Function.iterate_succ] using hneg2 y hy

/-- AKMM, p. 254: the book's model, Cobb–Douglas `f(k) = k^α` (`0 < α < 1`) with CRRA utility
`u(c) = (c^{1−σ} − 1)/(1 − σ)` (`σ > 0`, `σ ≠ 1`), `ρ, δ > 0`, satisfies the assumptions of
EconomicGrowth's Ramsey–Cass–Koopmans library. -/
theorem ramseySaddle_primitives {α σ ρ δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hσ1 : σ ≠ 1) (hρ : 0 < ρ) (hδ : 0 < δ) :
    CassPrimitives (fun k : ℝ => k ^ α) (crraUtility σ) ρ δ := by
  have hf : (fun k : ℝ => k ^ α) = fun x : ℝ => 1 * x ^ α + 0 := by funext x; ring
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : crraUtility σ = fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [crraUtility]; ring
  obtain ⟨fd, fpc, fpp, fs, fsc, -, fi0, fit, -⟩ :=
    ramseySaddle_power_props 1 0 α (by linarith) hα1
  obtain ⟨ud, -, upp, us, usc, usn, ui0, -, uconc⟩ :=
    ramseySaddle_power_props (1 / (1 - σ)) (-(1 / (1 - σ))) (1 - σ)
      (by rw [one_div, inv_mul_cancel₀ h1σ]; exact one_pos) (by linarith)
  rw [← hf] at fd fpc fpp fs fsc fi0 fit
  rw [← hu] at ud upp us usc usn ui0 uconc
  exact ⟨hρ, hδ, Real.strictConcaveOn_rpow hα0 hα1, Real.zero_rpow hα0.ne', fd, fpc, fpp, fs,
    fsc, fi0, fit, uconc, ud, upp, us, usc, usn, ui0⟩

/-- AKMM, §9.3.2, p. 255 and Appendix 9.A.4: **the saddle path**. Under EconomicGrowth's
assumptions `P` (gross output `f`, utility `u`, discount `ρ`, depreciation `δ`), if the certified
Cass optimum from `k(0) > 0` invests strictly throughout (which holds for `k(0) ≤ k**`, see
`ramseySaddle_path`), then it converges to `(k**, f(k**) − δk**)` with `f'(k**) = ρ + δ`,
satisfies (9.A.1) `μ = e^{−ρt}u'(c)`, (9.A.2) `μ̇ = −μ(f'(k) − δ)` and the TVC (9.34), and is
catching-up optimal in the book's problem (9.33): against every path from `k(0)` with `k ≥ 0`
and positive continuous consumption, disinvestment allowed. -/
theorem ramseySaddle_of_interior {f U : ℝ → ℝ} {ρ δ : ℝ} (P : CassPrimitives f U ρ δ)
    {a : FeasiblePath f δ} {q : ℝ → ℝ} (hc : CassCertificate f U ρ δ a q)
    (hint : ∀ t, 0 ≤ t → 0 < a.investment t) :
    deriv f (cassSteady P) = ρ + δ ∧
      Tendsto a.capital atTop (𝓝 (cassSteady P)) ∧
      Tendsto a.consumption atTop (𝓝 (f (cassSteady P) - δ * cassSteady P)) ∧
      (∀ t, 0 ≤ t → discount ρ t * q t = Real.exp (-ρ * t) * deriv U (a.consumption t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt (fun s => discount ρ s * q s)
        (-(discount ρ t * q t * (deriv f (a.capital t) - δ))) t) ∧
      Tendsto (fun T => Real.exp (-ρ * T) * deriv U (a.consumption T) * a.capital T) atTop
        (𝓝 0) ∧
      ∀ k' c' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ k' t) → (∀ t, 0 ≤ t → 0 < c' t) →
        ContinuousOn c' (Set.Ici 0) →
        (∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) → k' 0 = a.capital 0 →
        ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (c' t) ≤
          (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (a.consumption t)) + ε := by
  obtain ⟨hk, hcon, -, -, -⟩ := hc.dynamics P
  have hqU : ∀ t, 0 ≤ t → q t = deriv U (a.consumption t) := fun t ht => by
    rcases mul_eq_zero.mp (hc.slack t ht) with h | h
    · linarith
    · exact absurd h (hint t ht).ne'
  have h9A1 : ∀ t, 0 ≤ t → discount ρ t * q t = Real.exp (-ρ * t) * deriv U (a.consumption t) :=
    fun t ht => by rw [hqU t ht]; rfl
  have h9A2 : ∀ t, 0 ≤ t → HasDerivAt (fun s => discount ρ s * q s)
      (-(discount ρ t * q t * (deriv f (a.capital t) - δ))) t := fun t ht => by
    have h := hasDerivAt_discounted_costate (d := ρ) (m := δ) (mu := deriv U (a.consumption t))
      (mp := deriv f (a.capital t)) (hc.costate t ht)
    convert h using 1
    rw [← hqU t ht]
    ring
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * deriv U (a.consumption T) * a.capital T)
      atTop (𝓝 0) := by
    have h := hc.transversality.mul hk
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [← h9A1 T hT]
  refine ⟨(cassSteady_spec P).2, hk, hcon, h9A1, h9A2, htvc, ?_⟩
  intro k' c' hk' hc' hcc' hkd' h0
  exact (mangasarian_planner (f' := deriv f) (μ := fun s => discount ρ s * q s)
    P.f_conc.concaveOn P.U_conc.concaveOn (fun y hy => (P.U_diff y hy).hasDerivAt)
    (fun y hy => (P.U_prime_pos y hy).le) hc.capital_pos
    (fun t ht => (P.f_diff _ (hc.capital_pos t ht)).hasDerivAt) a.consumption_pos
    a.consumption_continuous (fun t ht => a.hasDerivAt_capital' ht) h9A1 h9A2 htvc hk' hc'
    hcc' hkd' h0).1

/-- AKMM, §9.3.2, p. 255: **the saddle path from `k(0) ≤ k**`**. For every `0 < k(0) ≤ k**`
the certified Cass optimum invests strictly, so it is the book's saddle path: it converges to
the steady state, satisfies (9.A.1), (9.A.2), (9.34), the Euler equation
`ċ = −(u'/u'')(c)(f'(k) − (ρ + δ))` (for `k(0) < k**`, `t > 0`), and is catching-up optimal in
the book's problem (`ramseySaddle_of_interior`). -/
theorem ramseySaddle_path {f U : ℝ → ℝ} {ρ δ k₀ : ℝ} (P : CassPrimitives f U ρ δ)
    (hk₀ : 0 < k₀) (hle : k₀ ≤ cassSteady P) :
    ∃ a : FeasiblePath f δ, ∃ q : ℝ → ℝ, a.capital 0 = k₀ ∧ CassCertificate f U ρ δ a q ∧
      (∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k₀ < cassSteady P → ∀ t, 0 < t → HasDerivAt a.consumption
        (-(deriv U (a.consumption t)) / deriv (deriv U) (a.consumption t) *
          (deriv f (a.capital t) - (ρ + δ))) t) := by
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk₀
  set a := optimalPath P hk₀
  have hint : ∀ t, 0 ≤ t → 0 < a.investment t := by
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨ks, hks, hstat, b, Jb, hb0, -, -, -, -, -, -, -, hbinv, -, -, -, hbuniq⟩ :=
        cass_general_dynamic f U ρ δ k₀ P.d_pos P.m_pos hk₀ P.f_conc P.f_zero P.f_diff
          P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont P.f_inada0 P.f_inadaTop
          P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont P.U_second_neg P.U_inada0
      have hks' : cassSteady P = ks := cassSteady_eq P hks hstat
      obtain ⟨J, hJ⟩ := hc.welfare
      have huniq := (hbuniq a J (hc.isCassOptimal P hJ) h0).2
      intro t ht
      rw [(huniq t ht).2.2]
      exact hbinv (hks' ▸ hlt) t ht
    · intro t ht
      have hconst := (hc.dynamics P).2.2.2.2 (h0.trans heq) t ht
      have hr := a.resource t ht
      rw [hconst.1, hconst.2] at hr
      have : a.investment t = δ * cassSteady P := by linarith
      rw [this]
      exact mul_pos P.m_pos (cassSteady_spec P).1
  refine ⟨a, q, h0, hc, hint, fun hlt t ht => ?_⟩
  have h := hc.hasDerivAt_consumption P (by rw [h0]; exact hlt.ne) le_rfl
    (fun s hs => hint s hs) ht
  exact h

/-- AKMM, (9.35) and p. 255, **for the book's model**: Cobb–Douglas `f(k) = k^α` and CRRA
utility. For `0 < k(0) ≤ k**` there is a path that converges to the steady state, invests
strictly, satisfies the CRRA Euler equation (9.35) `ċ/c = (f'(k) − (δ + ρ))/σ` (when
`k(0) < k**`, `t > 0`), and is optimal in the book's problem with the properties of
`ramseySaddle_of_interior`. -/
theorem ramseySaddle_crra_cobbDouglas {α σ ρ δ k₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hk₀ : 0 < k₀)
    (hle : k₀ ≤ cassSteady (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ)) :
    ∃ a : FeasiblePath (fun k : ℝ => k ^ α) δ, ∃ q : ℝ → ℝ, a.capital 0 = k₀ ∧
      CassCertificate (fun k : ℝ => k ^ α) (crraUtility σ) ρ δ a q ∧
      (∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k₀ < cassSteady (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ) → ∀ t, 0 < t →
        ∃ cdot, HasDerivAt a.consumption cdot t ∧
          cdot / a.consumption t = (α * a.capital t ^ (α - 1) - (δ + ρ)) / σ) := by
  set P := ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ
  obtain ⟨a, q, h0, hc, hint, heul⟩ := ramseySaddle_path P hk₀ hle
  refine ⟨a, q, h0, hc, hint, fun hlt t ht => ⟨_, heul hlt t ht, ?_⟩⟩
  have hct := a.consumption_pos t ht.le
  have hkt := hc.capital_pos t ht.le
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : crraUtility σ = fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [crraUtility]; ring
  have hU1 : deriv (crraUtility σ) (a.consumption t) = a.consumption t ^ (-σ) := by
    rw [hu, (ramseySaddle_power_hasDerivAt _ _ _ hct).deriv]
    field_simp
    ring_nf
  have hU2 : deriv (deriv (crraUtility σ)) (a.consumption t) =
      -σ * a.consumption t ^ (-σ - 1) := by
    rw [hu, (ramseySaddle_power_derivs _ _ _ hct).2.2]
    field_simp
    ring_nf
  have hF1 : deriv (fun k : ℝ => k ^ α) (a.capital t) = α * a.capital t ^ (α - 1) := by
    exact (Real.hasDerivAt_rpow_const (Or.inl hkt.ne')).deriv
  rw [hU1, hU2, hF1]
  have hsplit : a.consumption t ^ (-σ - 1) * a.consumption t = a.consumption t ^ (-σ) := by
    rw [Real.rpow_sub_one hct.ne']
    field_simp
  have hpos := Real.rpow_pos_of_pos hct (-σ)
  have hpos1 := Real.rpow_pos_of_pos hct (-σ - 1)
  rw [div_eq_div_iff hct.ne' hσ.ne']
  rw [← hsplit]
  field_simp
  ring

end AKMM.ContinuousTime
