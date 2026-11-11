/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OPHousehold
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Card

/-!
# The Diamond (1965) model: equilibrium law of motion and steady states

Miao, §16.2, pp. 544–549. Technology `f(k) = F(k, 1)` with `f(0) = 0`, `f′ > 0`, `f` strictly
concave, `f′(∞) = 0`; no depreciation; population `N_{t+1} = g_n N_t`.

* Firms: (16.14) `w = f(k) − kf′(k)` and (16.15) `R = 1 + f′(k)` are the first-order conditions
  of profit maximisation with `F(K, N) = Nf(K/N)` (`eq_16_14`, `eq_16_15`, `op_F_hasDerivAt_K`,
  `op_F_hasDerivAt_N`), and factor payments exhaust output (`op_euler_identity`).
* Capital-market clearing `K_{t+1} = N_t s_t` gives `g_n k_{t+1} = s_t`
  (`op_capital_market`), and the equilibrium law (16.16) (`OPIsDiamondEqm`, `eq_16_16`).
* The wage: positive, strictly increasing, `w(0+) = 0`, `w(k)/k = f(k)/k − f′(k) → 0`
  (`op_wage_pos`, `op_wage_strictMono`, `op_wage_tendsto_zero`, `op_f_div_tendsto_zero`,
  `op_wage_div_tendsto_zero`).
* With `s_R ≥ 0`, (16.16) has a unique solution `k_{t+1} = G(k_t)` (`op_temporary_eqm`,
  `op_G_exists`); `G` is increasing (`op_G_strictMono`), `G(0+) = 0` (`op_G_tendsto_zero`),
  `G(k)/k → 0` (`op_G_div_tendsto_zero`), so `G` eventually lies below the diagonal
  (`op_G_eventually_below`).
* The slope `dk_{t+1}/dk_t = −s_w kf″(k)/(g_n − s_R f″(k_{t+1}))` by implicit differentiation
  (`op_G_slope`, `op_G_slope_pos`, `op_G_slope_steady`).
* Steady states: `G′(0) > 1` gives at least one positive steady state (`op_exists_fixed`,
  `op_above_diag_of_deriv`). **Correction:** "odd" and "even" numbers of positive steady states
  are false in general: functions with all the listed properties and `G′(0) = 2` resp. `1/2`
  have exactly two resp. one positive steady states (`op_odd_counterexample`,
  `op_even_counterexample`).
* The Diamond conditions: **correction** — condition (ii) must read `G′(0) > 1`; with the
  printed `G′(0) < 1` together with (iii) there is no positive steady state at all
  (`op_diamond_conditions_printed`). With `G′(0) > 1` and `G′(k*) < 1` at every positive steady
  state there is exactly one positive steady state `k_D` (`op_diamond_conditions`), it is
  globally stable for increasing `G` (`op_fixed_signs`, `op_global_convergence`), and
  `|G′(k*)| < 1` gives local stability (`op_local_stability`).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The competitive wage (16.14): `w(k) = f(k) − kf′(k)`. -/
def opWage (f fp : ℝ → ℝ) (k : ℝ) : ℝ := f k - k * fp k

/-- The gross interest rate (16.15): `R(k) = 1 + f′(k)` (no depreciation). -/
def opRate (fp : ℝ → ℝ) (k : ℝ) : ℝ := 1 + fp k

/-! ### Firms -/

/-- `∂F/∂K = f′(K/N)` for `F(K, N) = Nf(K/N)`. -/
theorem op_F_hasDerivAt_K {f fp : ℝ → ℝ} {K N : ℝ} (hN : N ≠ 0)
    (hf : HasDerivAt f (fp (K / N)) (K / N)) :
    HasDerivAt (fun K' => N * f (K' / N)) (fp (K / N)) K := by
  have h1 : HasDerivAt (fun K' => K' / N) (1 / N) K := (hasDerivAt_id K).div_const N
  have := (hf.comp K h1).const_mul N
  simp only [Function.comp_def] at this
  convert this using 1
  field_simp

/-- `∂F/∂N = f(k) − kf′(k)` with `k = K/N`, for `F(K, N) = Nf(K/N)`. -/
theorem op_F_hasDerivAt_N {f fp : ℝ → ℝ} {K N : ℝ} (hN : N ≠ 0)
    (hf : HasDerivAt f (fp (K / N)) (K / N)) :
    HasDerivAt (fun N' => N' * f (K / N')) (opWage f fp (K / N)) N := by
  have h1 : HasDerivAt (fun N' => K / N') (-(K / N ^ 2)) N := by
    have := (hasDerivAt_inv hN).const_mul K
    convert this using 1
    · ext x; simp [div_eq_mul_inv]
    · ring
  have := (hasDerivAt_id' N).mul (hf.comp N h1)
  simp only [Function.comp_def] at this
  convert this using 1
  simp only [opWage]
  field_simp
  ring

/-- Miao, (16.15), p. 545: if the capital input `K` maximises profit
`Nf(K′/N) − (R − 1)K′` over `K′ > 0`, then `R = 1 + f′(k)`. -/
theorem eq_16_15 {f fp : ℝ → ℝ} {K N R : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hf : HasDerivAt f (fp (K / N)) (K / N))
    (hmax : ∀ K' > 0, N * f (K' / N) - (R - 1) * K' ≤ N * f (K / N) - (R - 1) * K) :
    R = opRate fp (K / N) := by
  have hloc : IsLocalMax (fun K' => N * f (K' / N) - (R - 1) * K') K :=
    Filter.eventually_of_mem (Ioi_mem_nhds hK) hmax
  have hd := (op_F_hasDerivAt_K hN.ne' hf).sub ((hasDerivAt_id K).const_mul (R - 1))
  have := hloc.hasDerivAt_eq_zero hd
  simp only [opRate]
  simp only [mul_one] at this
  linarith

/-- Miao, (16.14), p. 545: if the labour input `N` maximises profit `N′f(K/N′) − wN′` over
`N′ > 0`, then `w = f(k) − kf′(k)`. -/
theorem eq_16_14 {f fp : ℝ → ℝ} {K N w : ℝ} (hN : 0 < N)
    (hf : HasDerivAt f (fp (K / N)) (K / N))
    (hmax : ∀ N' > 0, N' * f (K / N') - w * N' ≤ N * f (K / N) - w * N) :
    w = opWage f fp (K / N) := by
  have hloc : IsLocalMax (fun N' => N' * f (K / N') - w * N') N :=
    Filter.eventually_of_mem (Ioi_mem_nhds hN) hmax
  have hd := (op_F_hasDerivAt_N hN.ne' hf).sub ((hasDerivAt_id N).const_mul w)
  have := hloc.hasDerivAt_eq_zero hd
  simp only [mul_one] at this
  linarith

/-- Factor payments exhaust output: `Nf(K/N) = f′(k)K + w(k)N` (constant returns). -/
theorem op_euler_identity (f fp : ℝ → ℝ) {K N : ℝ} (hN : N ≠ 0) :
    N * f (K / N) = fp (K / N) * K + opWage f fp (K / N) * N := by
  simp only [opWage]; field_simp; ring

/-! ### Capital-market equilibrium and (16.16) -/

/-- Miao, p. 546: `K_{t+1} = N_t s_t`, `K_t = k_tN_t` and `N_{t+1} = g_nN_t` give
`g_nk_{t+1} = s_t`. -/
theorem op_capital_market {K k N s : ℕ → ℝ} {gn : ℝ} (t : ℕ) (hKs : K (t + 1) = N t * s t)
    (hk : ∀ t, K t = k t * N t) (hN : N (t + 1) = gn * N t) (hN0 : N t ≠ 0) :
    gn * k (t + 1) = s t := by
  have h := hk (t + 1)
  rw [hKs, hN] at h
  have : N t * (gn * k (t + 1) - s t) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hN0
  linarith

/-- The Diamond equilibrium (16.16): `k_t > 0` and
`k_{t+1} = s(f(k_t) − k_tf′(k_t), 1 + f′(k_{t+1}))/g_n` for all `t`. -/
def OPIsDiamondEqm (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn : ℝ) (k : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ k (t + 1) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) / gn

/-- Miao, (16.16), p. 546: optimal saving `s_t = s(w_t, R_{t+1})`, the factor prices
(16.14)–(16.15) and capital-market clearing `g_nk_{t+1} = s_t` characterise the Diamond
equilibrium. -/
theorem eq_16_16 {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn) {k w R sv : ℕ → ℝ}
    (hk : ∀ t, 0 < k t) (hw : ∀ t, w t = opWage f fp (k t)) (hR : ∀ t, R t = opRate fp (k t))
    (hsv : ∀ t, sv t = s (w t) (R (t + 1))) (hcm : ∀ t, gn * k (t + 1) = sv t) :
    OPIsDiamondEqm s f fp gn k := by
  intro t
  refine ⟨hk t, ?_⟩
  rw [eq_div_iff hgn.ne', mul_comm, hcm t, hsv t, hw t, hR (t + 1)]

/-- Conversely, a Diamond equilibrium satisfies capital-market clearing with optimal saving. -/
theorem op_diamondEqm_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    {k : ℕ → ℝ} : OPIsDiamondEqm s f fp gn k ↔
      ∀ t, 0 < k t ∧ gn * k (t + 1) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) := by
  refine forall_congr' fun t => and_congr_right fun _ => ?_
  rw [eq_div_iff hgn.ne', mul_comm]

/-! ### Properties of the technology and the wage -/

/-- Strict concavity makes `f′` strictly decreasing. -/
theorem op_fp_strictAnti {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) : StrictAntiOn fp (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (le_of_lt hx)
  have hy' : y ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (le_of_lt hy)
  have h1 := hconc.slope_lt_of_hasDerivAt hx' hy' hxy (hfd x hx)
  have h2 := hconc.lt_slope_of_hasDerivAt hx' hy' hxy (hfd y hy)
  linarith

/-- The wage is positive: `f(k) − kf′(k) > 0` for `k > 0` (strict concavity, `f(0) = 0`). -/
theorem op_wage_pos {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    {k : ℝ} (hk : 0 < k) (hd : HasDerivAt f (fp k) k) : 0 < opWage f fp k := by
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 le_rfl)
    hk.ne hd
  rw [hf0] at this
  simp only [opWage]
  linarith

/-- The wage is strictly increasing in `k` (Miao, p. 546: "an increase in the capital stock in
period `t` increases the wage"). -/
theorem op_wage_strictMono {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) : StrictMonoOn (opWage f fp) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have h1 := op_strictConcave_tangent hconc (Set.mem_Ici.2 hy'.le) (Set.mem_Ici.2 hx'.le)
    hxy.ne (hfd y hy')
  have h2 := op_fp_strictAnti hconc hfd hx hy hxy
  simp only [opWage]
  nlinarith

/-- `w(k) < f(k)` when `f′(k) > 0`. -/
theorem op_wage_lt {f fp : ℝ → ℝ} {k : ℝ} (hk : 0 < k) (hfp : 0 < fp k) :
    opWage f fp k < f k := by
  simp only [opWage]; nlinarith

/-- `w(0+) = 0`: the wage tends to `0` as `k → 0`. -/
theorem op_wage_tendsto_zero {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : f 0 = 0) (hfc : ContinuousWithinAt f (Set.Ioi 0) 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k) :
    Tendsto (opWage f fp) (𝓝[>] 0) (𝓝 0) := by
  have hf : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have := hfc.tendsto; rwa [hf0] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (op_wage_pos hconc hf0 hk (hfd k hk)).le
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (op_wage_lt hk (hfp k hk)).le

/-- `w(k)/k = f(k)/k − f′(k)`. -/
theorem op_wage_div_eq (f fp : ℝ → ℝ) {k : ℝ} (hk : k ≠ 0) :
    opWage f fp k / k = f k / k - fp k := by
  simp only [opWage]; field_simp

/-- `f(k)/k → 0` as `k → ∞`, from `f′(∞) = 0` and concavity. -/
theorem op_f_div_tendsto_zero {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : f 0 = 0) (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k)
    (hfp : ∀ k, 0 < k → 0 < fp k) (hinf : Tendsto fp atTop (𝓝 0)) :
    Tendsto (fun k => f k / k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 (hinf.eventually (eventually_lt_nhds (half_pos hε)))
  set K := max K1 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfK : fp K < ε / 2 := hK1 K (le_max_left _ _)
  refine ⟨max (K + 1) (2 * |f K| / ε + 1), fun n hn => ?_⟩
  have hn1 : K + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 * |f K| / ε + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by linarith
  have htan := op_concave_tangent hconc.concaveOn (Set.mem_Ici.2 hK.le)
    (Set.mem_Ici.2 hn0.le) (hfd K hK)
  have hfn : 0 < f n := by
    have := op_wage_pos hconc hf0 hn0 (hfd n hn0)
    have := hfp n hn0
    simp only [opWage] at *
    nlinarith
  have hfKp := hfp K hK
  have hb : f n < |f K| + ε / 2 * n := by
    have : fp K * (n - K) ≤ fp K * n := by nlinarith
    have : fp K * n < ε / 2 * n := by nlinarith
    linarith [le_abs_self (f K)]
  have h2 : 2 * |f K| / ε < n := by linarith
  rw [div_lt_iff₀ hε] at h2
  rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hfn hn0), div_lt_iff₀ hn0]
  nlinarith

/-- `w(k)/k → 0` as `k → ∞`. -/
theorem op_wage_div_tendsto_zero {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : f 0 = 0) (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k)
    (hfp : ∀ k, 0 < k → 0 < fp k) (hinf : Tendsto fp atTop (𝓝 0)) :
    Tendsto (fun k => opWage f fp k / k) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (op_f_div_tendsto_zero hconc hf0 hfd hfp hinf) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (div_pos (op_wage_pos hconc hf0 hk (hfd k hk)) hk).le
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact div_le_div_of_nonneg_right (op_wage_lt hk (hfp k hk)).le hk.le

/-! ### The temporary equilibrium `k_{t+1} = G(k_t)` -/

/-- Miao, p. 546: "If `s_R > 0` ... we can solve for `k_{t+1}` as a function of `k_t`". Given
the wage `w > 0`, if `x ↦ S(x) = s(w, R(x))` is continuous, nonincreasing (`s_R ≥ 0` and `R`
decreasing) and `0 < S < w`, then `g_n x = S(x)` has exactly one solution `x > 0`. -/
theorem op_temporary_eqm {S : ℝ → ℝ} {gn w : ℝ} (hgn : 0 < gn)
    (hpos : ∀ x, 0 < x → 0 < S x) (hlt : ∀ x, 0 < x → S x < w)
    (hanti : AntitoneOn S (Set.Ioi 0)) (hcont : ContinuousOn S (Set.Ioi 0)) :
    ∃! x, 0 < x ∧ gn * x = S x := by
  have hw : 0 < w := lt_trans (hpos 1 one_pos) (hlt 1 one_pos)
  set xb := w / gn with hxb
  have hxb0 : 0 < xb := div_pos hw hgn
  have hgxb : gn * xb = w := by rw [hxb]; field_simp
  set x0 := S xb / gn with hx0
  have hx00 : 0 < x0 := div_pos (hpos xb hxb0) hgn
  have hgx0 : gn * x0 = S xb := by rw [hx0]; field_simp
  have hx0xb : x0 < xb := by
    have := hlt xb hxb0
    nlinarith
  set h : ℝ → ℝ := fun x => gn * x - S x with hh
  have hcont' : ContinuousOn h (Set.Icc x0 xb) :=
    (continuousOn_const.mul continuousOn_id).sub
      (hcont.mono fun x hx => lt_of_lt_of_le hx00 hx.1)
  have h0 : h x0 ≤ 0 := by
    simp only [hh]
    have := hanti hx00 hxb0 hx0xb.le
    linarith
  have h1 : 0 ≤ h xb := by
    simp only [hh]
    linarith [hlt xb hxb0]
  obtain ⟨x, hx, hx'⟩ := intermediate_value_Icc hx0xb.le hcont' ⟨h0, h1⟩
  refine ⟨x, ⟨lt_of_lt_of_le hx00 hx.1, by simp only [hh] at hx'; linarith⟩, ?_⟩
  rintro y ⟨hy0, hy⟩
  have hx0' : 0 < x := lt_of_lt_of_le hx00 hx.1
  have hxe : gn * x = S x := by simp only [hh] at hx'; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · have := hanti hy0 hx0' hlt'.le
    nlinarith
  · have := hanti hx0' hy0 hlt'.le
    nlinarith

/-- `s_R ≥ 0` and `f′` decreasing make `x ↦ s(w, R(x))` nonincreasing. -/
theorem op_S_antitone {s : ℝ → ℝ → ℝ} {fp : ℝ → ℝ} {w : ℝ}
    (hmonoR : MonotoneOn (s w) (Set.Ioi 1)) (hfanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) :
    AntitoneOn (fun x => s w (opRate fp x)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have h1 : fp y ≤ fp x := hfanti.antitoneOn hx hy hxy
  exact hmonoR (show opRate fp y ∈ Set.Ioi 1 by simp [opRate, hfp y hy'])
    (show opRate fp x ∈ Set.Ioi 1 by simp [opRate, hfp x hx']) (by simp [opRate]; linarith)

/-- Miao, p. 546: with `s_R ≥ 0` the equilibrium law (16.16) defines a function
`k_{t+1} = G(k_t)` on `k > 0`. -/
theorem op_G_exists {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hfpc : ContinuousOn fp (Set.Ioi 0))
    (hpos : ∀ w, 0 < w → ∀ R, 1 < R → 0 < s w R) (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hmonoR : ∀ w, 0 < w → MonotoneOn (s w) (Set.Ioi 1))
    (hcontR : ∀ w, 0 < w → ContinuousOn (s w) (Set.Ioi 1)) :
    ∃ G : ℝ → ℝ, ∀ k, 0 < k →
      0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k)) := by
  have hfanti := op_fp_strictAnti hconc hfd
  have H : ∀ k, 0 < k → ∃ x, 0 < x ∧ gn * x = s (opWage f fp k) (opRate fp x) := by
    intro k hk
    have hw := op_wage_pos hconc hf0 hk (hfd k hk)
    have hR : ∀ x, 0 < x → 1 < opRate fp x := fun x hx => by simp [opRate, hfp x hx]
    obtain ⟨x, hx, -⟩ := op_temporary_eqm (S := fun x => s (opWage f fp k) (opRate fp x))
      (w := opWage f fp k) hgn (fun x hx => hpos _ hw _ (hR x hx))
      (fun x hx => hlt _ hw _ (hR x hx)) (op_S_antitone (hmonoR _ hw) hfanti hfp)
      ((hcontR _ hw).comp (continuousOn_const.add hfpc) fun x hx => hR x hx)
    exact ⟨x, hx⟩
  choose! G hG using H
  exact ⟨G, hG⟩

/-- Miao, p. 546: "`G` is an increasing function". If saving rises strictly with the wage and
`s_R ≥ 0`, any solution `G` of (16.16) is strictly increasing. -/
theorem op_G_strictMono {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hsw : ∀ w w' R, 0 < w → w < w' → 1 < R → s w R < s w' R)
    (hmonoR : ∀ w, 0 < w → MonotoneOn (s w) (Set.Ioi 1))
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    StrictMonoOn G (Set.Ioi 0) := by
  intro k hk k' hk' hkk
  have hk0 : (0 : ℝ) < k := hk
  have hk0' : (0 : ℝ) < k' := hk'
  obtain ⟨hG1, hE1⟩ := hG k hk0
  obtain ⟨hG2, hE2⟩ := hG k' hk0'
  have hw := op_wage_pos hconc hf0 hk0 (hfd k hk0)
  have hww := op_wage_strictMono hconc hfd hk hk' hkk
  have hanti := op_S_antitone (hmonoR _ (lt_trans hw hww)) (op_fp_strictAnti hconc hfd) hfp
  by_contra h
  push Not at h
  have h1 : s (opWage f fp k) (opRate fp (G k)) < s (opWage f fp k') (opRate fp (G k)) :=
    hsw _ _ _ hw hww (by simp [opRate, hfp _ hG1])
  have h2 := hanti (show G k' ∈ Set.Ioi 0 from hG2) (show G k ∈ Set.Ioi 0 from hG1) h
  nlinarith

/-- `G(k) < w(k)/g_n`: the capital stock is bounded by the wage bill (Miao, p. 546,
`g_nk_{t+1}/k_t ≤ w_t/k_t`). -/
theorem op_G_lt_wage {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k)))
    {k : ℝ} (hk : 0 < k) : gn * G k < opWage f fp k := by
  obtain ⟨hG1, hE⟩ := hG k hk
  rw [hE]
  exact hlt _ (op_wage_pos hconc hf0 hk (hfd k hk)) _ (by simp [opRate, hfp _ hG1])

/-- Miao, p. 546: `G(0) = 0`, as the limit `G(k) → 0` as `k → 0+`. -/
theorem op_G_tendsto_zero {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfc : ContinuousWithinAt f (Set.Ioi 0) 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    Tendsto G (𝓝[>] 0) (𝓝 0) := by
  have hw := (op_wage_tendsto_zero hconc hf0 hfc hfd hfp).div_const gn
  rw [zero_div] at hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (hG k hk).1.le
  · filter_upwards [self_mem_nhdsWithin] with k hk
    rw [le_div_iff₀ hgn, mul_comm]
    exact (op_G_lt_wage hconc hf0 hfd hfp hlt hG hk).le

/-- Miao, p. 546: `lim_{k→∞} G(k)/k = 0`. -/
theorem op_G_div_tendsto_zero {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hinf : Tendsto fp atTop (𝓝 0)) (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    Tendsto (fun k => G k / k) atTop (𝓝 0) := by
  have hw := (op_wage_div_tendsto_zero hconc hf0 hfd hfp hinf).div_const gn
  rw [zero_div] at hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (div_pos (hG k hk).1 hk).le
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have := op_G_lt_wage hconc hf0 hfd hfp hlt hG hk
    rw [div_div, le_div_iff₀ (mul_pos hk hgn)]
    have : G k / k * (k * gn) = gn * G k := by field_simp
    linarith

/-- Miao, p. 547: "`k_{t+1}/k_t = G(k_t)/k_t < 1` for `k_t` sufficiently large": the graph of `G`
eventually falls below the diagonal. -/
theorem op_G_eventually_below {G : ℝ → ℝ} (hG : Tendsto (fun k => G k / k) atTop (𝓝 0)) :
    ∃ M, ∀ k, M < k → G k < k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((hG.eventually (eventually_lt_nhds one_pos)).and
    (eventually_gt_atTop 0))
  refine ⟨M, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hM k hk.le
  rwa [div_lt_one h2] at h1

/-! ### The slope of `G` -/

/-- The derivative of the wage: `w′(k) = −kf″(k)`. -/
theorem op_wage_hasDerivAt {f fp fpp : ℝ → ℝ} {k : ℝ} (hf : HasDerivAt f (fp k) k)
    (hfp : HasDerivAt fp (fpp k) k) : HasDerivAt (opWage f fp) (-k * fpp k) k := by
  have := hf.sub ((hasDerivAt_id' k).mul hfp)
  unfold opWage
  convert this using 1
  ring

/-- Miao, p. 546: implicit differentiation of (16.16). If `G` solves
`g_nG(k) = s(w(k), R(G(k)))` near `k`, with `s` differentiable at `(w(k), R(G(k)))` with partial
derivatives `s_w, s_R`, then `G′(k)(g_n − s_R f″(G(k))) = −s_w kf″(k)`. -/
theorem op_G_slope {s : ℝ → ℝ → ℝ} {f fp fpp G : ℝ → ℝ} {gn k G' sw sR : ℝ}
    (hG : ∀ᶠ x in 𝓝 k, gn * G x = s (opWage f fp x) (opRate fp (G x)))
    (hGd : HasDerivAt G G' k)
    (hs : HasFDerivAt (fun p : ℝ × ℝ => s p.1 p.2)
      (sw • ContinuousLinearMap.fst ℝ ℝ ℝ + sR • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (opWage f fp k, opRate fp (G k)))
    (hf : HasDerivAt f (fp k) k) (hfpk : HasDerivAt fp (fpp k) k)
    (hfpG : HasDerivAt fp (fpp (G k)) (G k)) :
    G' * (gn - sR * fpp (G k)) = -sw * k * fpp k := by
  have hw := op_wage_hasDerivAt hf hfpk
  have hR : HasDerivAt (fun x => opRate fp (G x)) (fpp (G k) * G') k := by
    have := (hfpG.comp k hGd).const_add 1
    unfold opRate
    exact this
  have hg := hs.comp_hasDerivAt k (hw.prodMk hR)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at hg
  have hl : HasDerivAt (fun x => gn * G x) (gn * G') k := hGd.const_mul gn
  have hl' : HasDerivAt (fun x => s (opWage f fp x) (opRate fp (G x))) (gn * G') k :=
    hl.congr_of_eventuallyEq (hG.mono fun x hx => hx.symm)
  have := hl'.unique hg
  linarith

/-- Miao, p. 546: "if `s_R > 0`, then the denominator is positive", and the numerator
`−s_wkf″(k)` is positive, so `G′(k) = −s_wkf″(k)/(g_n − s_Rf″(G(k))) > 0`. -/
theorem op_G_slope_pos {gn k G' sw sR fppk fppG : ℝ} (hgn : 0 < gn) (hk : 0 < k)
    (hsw : 0 < sw) (hsR : 0 ≤ sR) (hk2 : fppk < 0) (hG2 : fppG < 0)
    (h : G' * (gn - sR * fppG) = -sw * k * fppk) :
    0 < gn - sR * fppG ∧ 0 < -sw * k * fppk ∧ G' = -sw * k * fppk / (gn - sR * fppG) ∧
      0 < G' := by
  have hd : 0 < gn - sR * fppG := by nlinarith
  have hn : 0 < -sw * k * fppk := by
    have : 0 < sw * k := mul_pos hsw hk
    nlinarith
  have hG' : G' = -sw * k * fppk / (gn - sR * fppG) := by
    rw [eq_div_iff hd.ne']; exact h
  exact ⟨hd, hn, hG', by rw [hG']; exact div_pos hn hd⟩

/-- Miao, p. 549: at a positive steady state `G(k*) = k*` the slope is
`G′(k*) = −s_wk*f″(k*)/(g_n − s_Rf″(k*))`. -/
theorem op_G_slope_steady {gn kstar G' sw sR fpp : ℝ} (hden : gn - sR * fpp ≠ 0)
    (h : G' * (gn - sR * fpp) = -sw * kstar * fpp) :
    G' = -sw * kstar * fpp / (gn - sR * fpp) := by
  rw [eq_div_iff hden]; exact h

/-! ### Steady states of `k_{t+1} = G(k_t)` -/

/-- Intermediate values for `G − id`, upward crossing. -/
theorem op_ivt_up {G : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn G (Set.Ioi 0)) (ha : 0 < a)
    (hab : a < b) (hA : G a < a) (hB : b < G b) : ∃ z, a < z ∧ z < b ∧ G z = z := by
  have hcont : ContinuousOn (fun x => G x - x) (Set.Icc a b) :=
    (hc.mono fun x hx => lt_of_lt_of_le ha hx.1).sub continuousOn_id
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hab.le hcont
    (show (0 : ℝ) ∈ Set.Ioo (G a - a) (G b - b) from ⟨by linarith, by linarith⟩)
  exact ⟨z, hz.1, hz.2, by simp only at hz0; linarith⟩

/-- Intermediate values for `G − id`, downward crossing. -/
theorem op_ivt_down {G : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn G (Set.Ioi 0)) (ha : 0 < a)
    (hab : a < b) (hA : a < G a) (hB : G b < b) : ∃ z, a < z ∧ z < b ∧ G z = z := by
  have hcont : ContinuousOn (fun x => G x - x) (Set.Icc a b) :=
    (hc.mono fun x hx => lt_of_lt_of_le ha hx.1).sub continuousOn_id
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hab.le hcont
    (show (0 : ℝ) ∈ Set.Ioo (G b - b) (G a - a) from ⟨by linarith, by linarith⟩)
  exact ⟨z, hz.1, hz.2, by simp only at hz0; linarith⟩

/-- A steady state with `G′(k*) < 1` is crossed from above: `G > id` just left of `k*` and
`G < id` just right of it. -/
theorem op_slope_lt_one {G : ℝ → ℝ} {c d : ℝ} (hd : HasDerivAt G d c) (hfix : G c = c)
    (hd1 : d < 1) :
    ∃ δ > 0, ∀ y, c - δ < y → y < c + δ → (c < y → G y < y) ∧ (y < c → y < G y) := by
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  have hev := h.eventually (eventually_lt_nhds hd1)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ, hδ, fun y hy1 hy2 => ⟨fun hcy => ?_, fun hyc => ?_⟩⟩
  · have hdist : dist y c < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hdist (show y ∈ ({c} : Set ℝ)ᶜ from by simp; linarith)
    rw [slope_def_field, hfix, div_lt_iff₀ (by linarith)] at this
    linarith
  · have hdist : dist y c < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hdist (show y ∈ ({c} : Set ℝ)ᶜ from by simp; linarith)
    rw [slope_def_field, hfix, div_lt_iff_of_neg (by linarith)] at this
    linarith

/-- The least steady state in `[a, b]`, when `b` is one. -/
theorem op_least_fixed {G : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn G (Set.Ioi 0)) (ha : 0 < a)
    (hab : a ≤ b) (hb : G b = b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ G c = c ∧ ∀ z, a ≤ z → z < c → G z ≠ z := by
  set A := Set.Icc a b ∩ (fun x => G x - x) ⁻¹' {0} with hA
  have hcl : IsClosed A :=
    ((hc.mono fun x hx => lt_of_lt_of_le ha hx.1).sub continuousOn_id).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hbA : b ∈ A := ⟨⟨hab, le_rfl⟩, by simp [hb]⟩
  have hbdd : BddBelow A := ⟨a, fun x hx => hx.1.1⟩
  have hcA := hcl.csInf_mem ⟨b, hbA⟩ hbdd
  refine ⟨sInf A, hcA.1.1, hcA.1.2, by have := hcA.2; simp at this; linarith, ?_⟩
  intro z hz hzc hGz
  have hzA : z ∈ A := ⟨⟨hz, by linarith [hcA.1.2]⟩, by simp [hGz]⟩
  exact absurd (csInf_le hbdd hzA) (not_le.2 hzc)

/-- If `G < id` at `y₁ < c` and `c` is a steady state with `G′(c) < 1`, there is a steady state
strictly between them. -/
theorem op_fixed_below {G : ℝ → ℝ} {y1 c d : ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hy1 : 0 < y1) (hlt : y1 < c) (hG1 : G y1 < y1) (hfix : G c = c) (hd : HasDerivAt G d c)
    (hd1 : d < 1) : ∃ z, y1 < z ∧ z < c ∧ G z = z := by
  obtain ⟨δ, hδ, hloc⟩ := op_slope_lt_one hd hfix hd1
  set y2 := max (c - δ / 2) ((y1 + c) / 2)
  have hy2c : y2 < c := max_lt (by linarith) (by linarith)
  have hy2a : c - δ < y2 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hy2b : y1 < y2 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hG2 : y2 < G y2 := (hloc y2 hy2a (by linarith)).2 hy2c
  obtain ⟨z, hz1, hz2, hz⟩ := op_ivt_up hc hy1 hy2b hG1 hG2
  exact ⟨z, hz1, by linarith, hz⟩

/-- `G′(0) > 1` in the sense of a right derivative at `0` with `G(0) = 0`: then `G(k) > k` for
small `k > 0`. -/
theorem op_above_diag_of_deriv {G : ℝ → ℝ} {d : ℝ} (hG0 : G 0 = 0)
    (hd : HasDerivWithinAt G d (Set.Ioi 0) 0) (hd1 : 1 < d) :
    ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hd
  obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (h.eventually (eventually_gt_nhds hd1))
  refine ⟨ε, hε, fun k hk hkε => ?_⟩
  have := hsub ⟨hk, hkε⟩
  simp only [Set.mem_ofPred_eq, slope_def_field, hG0, sub_zero] at this
  rwa [lt_div_iff₀ hk, one_mul] at this

/-- `G′(0) < 1`: then `G(k) < k` for small `k > 0`. -/
theorem op_below_diag_of_deriv {G : ℝ → ℝ} {d : ℝ} (hG0 : G 0 = 0)
    (hd : HasDerivWithinAt G d (Set.Ioi 0) 0) (hd1 : d < 1) :
    ∃ ε > 0, ∀ k, 0 < k → k < ε → G k < k := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hd
  obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (h.eventually (eventually_lt_nhds hd1))
  refine ⟨ε, hε, fun k hk hkε => ?_⟩
  have := hsub ⟨hk, hkε⟩
  simp only [Set.mem_ofPred_eq, slope_def_field, hG0, sub_zero] at this
  rwa [div_lt_iff₀ hk, one_mul] at this

/-- Miao, p. 547: "If `G′(0) > 1`, then [there are] positive steady states": `G` continuous on
`(0, ∞)`, above the diagonal near `0` and below it for large `k` has a positive steady
state. -/
theorem op_exists_fixed {G : ℝ → ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k) (hhigh : ∃ M, ∀ k, M < k → G k < k) :
    ∃ k, 0 < k ∧ G k = k := by
  obtain ⟨ε, hε, hl⟩ := hlow
  obtain ⟨M, hM⟩ := hhigh
  set b := max (M + 1) ε
  have hb : ε / 2 < b := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨z, hz, -, hfz⟩ := op_ivt_down hc (by linarith) hb (hl _ (by linarith) (by linarith))
    (hM b (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
  exact ⟨z, by linarith, hfz⟩

/-- Miao, p. 549, the Diamond conditions, corrected: with `G′(0) > 1` (`G > id` near `0`), `G`
below the diagonal for large `k`, and `G′(k*) < 1` at every positive steady state, there is
exactly one positive steady state `k_D` (the Diamond steady state). -/
theorem op_diamond_conditions {G : ℝ → ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k) (hhigh : ∃ M, ∀ k, M < k → G k < k)
    (hslope : ∀ k, 0 < k → G k = k → ∃ d, HasDerivAt G d k ∧ d < 1) :
    ∃! k, 0 < k ∧ G k = k := by
  obtain ⟨k0, hk0, hfix0⟩ := op_exists_fixed hc hlow hhigh
  refine ⟨k0, ⟨hk0, hfix0⟩, ?_⟩
  have key : ∀ k1 k2, 0 < k1 → G k1 = k1 → k1 < k2 → G k2 = k2 → False := by
    intro k1 k2 hk1 hf1 h12 hf2
    obtain ⟨d1, hd1, hd11⟩ := hslope k1 hk1 hf1
    obtain ⟨δ, hδ, hloc⟩ := op_slope_lt_one hd1 hf1 hd11
    have hk2δ : k1 + δ ≤ k2 := by
      by_contra h
      push Not at h
      have := (hloc k2 (by linarith) h).1 h12
      linarith
    obtain ⟨c, hac, hcb, hfc, hleast⟩ :=
      op_least_fixed hc (a := k1 + δ / 2) (b := k2) (by linarith) (by linarith) hf2
    have hy1 : G (k1 + δ / 4) < k1 + δ / 4 := (hloc _ (by linarith) (by linarith)).1 (by linarith)
    obtain ⟨dc, hdc, hdc1⟩ := hslope c (by linarith) hfc
    obtain ⟨z, hz1, hz2, hz⟩ :=
      op_fixed_below hc (by linarith) (by linarith) hy1 hfc hdc hdc1
    by_cases hzδ : z < k1 + δ
    · have := (hloc z (by linarith) hzδ).1 (by linarith)
      linarith
    · exact hleast z (by push Not at hzδ; linarith) hz2 hz
  rintro k ⟨hk, hfk⟩
  rcases lt_trichotomy k k0 with h | h | h
  · exact (key k k0 hk hfk h hfix0).elim
  · exact h
  · exact (key k0 k hk0 hfix0 h hfk).elim

/-- **Correction to the Diamond conditions** (Miao, p. 549). As printed, condition (ii) is
`G′(0) < 1`, i.e. `G < id` near `0`. Together with (iii), `G′(k*) < 1` at every positive steady
state, this leaves NO positive steady state, so there is no Diamond steady state `k_D`; the
condition must be `G′(0) > 1` (`op_diamond_conditions`). -/
theorem op_diamond_conditions_printed {G : ℝ → ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → G k < k)
    (hslope : ∀ k, 0 < k → G k = k → ∃ d, HasDerivAt G d k ∧ d < 1) :
    ¬ ∃ k, 0 < k ∧ G k = k := by
  rintro ⟨k2, hk2, hf2⟩
  obtain ⟨ε, hε, hl⟩ := hlow
  set a := min (ε / 2) k2
  have ha : 0 < a := lt_min (by linarith) hk2
  have haε : a < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨c, hac, hcb, hfc, hleast⟩ := op_least_fixed hc ha (min_le_right _ _) hf2
  have hy1 : G (a / 2) < a / 2 := hl _ (by linarith) (by linarith)
  obtain ⟨dc, hdc, hdc1⟩ := hslope c (by linarith) hfc
  obtain ⟨z, hz1, hz2, hz⟩ := op_fixed_below hc (by linarith) (by linarith) hy1 hfc hdc hdc1
  by_cases hzε : z < ε
  · have := hl z (by linarith) hzε
    linarith
  · exact hleast z (by push Not at hzε; linarith) hz2 hz

/-- With a unique positive steady state `k*`, `G > id` near `0` and `G < id` for large `k`:
`G(k) > k` on `(0, k*)` and `G(k) < k` on `(k*, ∞)` (the configuration of Figure 16.10). -/
theorem op_fixed_signs {G : ℝ → ℝ} {kstar : ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hks : 0 < kstar) (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k)
    (hhigh : ∃ M, ∀ k, M < k → G k < k) (huniq : ∀ k, 0 < k → G k = k → k = kstar) :
    (∀ k, 0 < k → k < kstar → k < G k) ∧ (∀ k, kstar < k → G k < k) := by
  obtain ⟨ε, hε, hl⟩ := hlow
  obtain ⟨M, hM⟩ := hhigh
  constructor
  · intro k hk hkk
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · set y := min (ε / 2) (k / 2)
      have hy : 0 < y := lt_min (by linarith) (by linarith)
      have hyk : y < k := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hyε : y < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      obtain ⟨z, hz1, hz2, hz⟩ := op_ivt_down hc hy hyk (hl y hy hyε) h
      have := huniq z (by linarith) hz
      linarith
    · have := huniq k hk h
      linarith
  · intro k hk
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · set b := max (M + 1) (k + 1)
      have hb : k < b := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      obtain ⟨z, hz1, hz2, hz⟩ := op_ivt_down hc (by linarith) hb h
        (hM b (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
      have := huniq z (by linarith) hz
      linarith
    · have := huniq k (by linarith) h.symm
      linarith

/-- Miao, p. 549 and Figure 16.10: under the Diamond conditions the unique positive steady state
is globally stable: for increasing `G` with `G > id` on `(0, k*)` and `G < id` on `(k*, ∞)`,
`k_t → k*` from every `k₁ > 0`. -/
theorem op_global_convergence {G : ℝ → ℝ} {kstar k1 : ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hmono : MonotoneOn G (Set.Ioi 0)) (hks : 0 < kstar) (hfix : G kstar = kstar)
    (hbelow : ∀ k, 0 < k → k < kstar → k < G k) (habove : ∀ k, kstar < k → G k < k)
    (hk1 : 0 < k1) : Tendsto (fun t => G^[t] k1) atTop (𝓝 kstar) := by
  set x : ℕ → ℝ := fun t => G^[t] k1 with hx
  have hxs : ∀ t, x (t + 1) = G (x t) := fun t => by
    simp only [hx]; rw [Function.iterate_succ_apply']
  have hlim : ∀ L, 0 < L → Tendsto x atTop (𝓝 L) → G L = L := by
    intro L hL hxL
    have h1 : Tendsto (fun t => G (x t)) atTop (𝓝 (G L)) :=
      ((hc.continuousAt (Ioi_mem_nhds hL)).tendsto).comp hxL
    have h2 : Tendsto (fun t => G (x t)) atTop (𝓝 L) := by
      have := hxL.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun t => ?_
      simp only [Function.comp_apply, hxs]
    exact tendsto_nhds_unique h1 h2
  rcases le_or_gt k1 kstar with hle | hgt
  · have hb : ∀ t, 0 < x t ∧ x t ≤ kstar := by
      intro t
      induction t with
      | zero => exact ⟨hk1, hle⟩
      | succ t ih =>
        rw [hxs]
        rcases ih.2.lt_or_eq with h | h
        · exact ⟨lt_trans ih.1 (hbelow _ ih.1 h), by
            have := hmono ih.1 (show kstar ∈ Set.Ioi 0 from hks) ih.2; rwa [hfix] at this⟩
        · rw [h, hfix]; exact ⟨hks, le_rfl⟩
    have hm : Monotone x := by
      refine monotone_nat_of_le_succ fun t => ?_
      rw [hxs]
      rcases (hb t).2.lt_or_eq with h | h
      · exact (hbelow _ (hb t).1 h).le
      · rw [h, hfix]
    have hbdd : BddAbove (Set.range x) := ⟨kstar, by rintro _ ⟨t, rfl⟩; exact (hb t).2⟩
    have hT := tendsto_atTop_ciSup hm hbdd
    set L := ⨆ t, x t
    have hL0 : 0 < L := lt_of_lt_of_le (hb 0).1 (le_ciSup hbdd 0)
    have hLk : L ≤ kstar := ciSup_le fun t => (hb t).2
    have hGL := hlim L hL0 hT
    rcases hLk.lt_or_eq with h | h
    · have := hbelow L hL0 h; linarith
    · rwa [h] at hT
  · have hb : ∀ t, kstar ≤ x t := by
      intro t
      induction t with
      | zero => exact hgt.le
      | succ t ih =>
        rw [hxs]
        have := hmono (show kstar ∈ Set.Ioi 0 from hks)
          (show x t ∈ Set.Ioi 0 from lt_of_lt_of_le hks ih) ih
        rwa [hfix] at this
    have hm : Antitone x := by
      refine antitone_nat_of_succ_le fun t => ?_
      rw [hxs]
      rcases (hb t).lt_or_eq with h | h
      · exact (habove _ h).le
      · rw [← h, hfix]
    have hbdd : BddBelow (Set.range x) := ⟨kstar, by rintro _ ⟨t, rfl⟩; exact hb t⟩
    have hT := tendsto_atTop_ciInf hm hbdd
    set L := ⨅ t, x t
    have hLk : kstar ≤ L := le_ciInf hb
    have hGL := hlim L (lt_of_lt_of_le hks hLk) hT
    rcases hLk.lt_or_eq with h | h
    · have := habove L h; linarith
    · rwa [← h] at hT

/-- Miao, p. 549: "the condition for the stability of a positive steady state is `G′(k*) < 1`".
A steady state with `|G′(k*)| < 1` is locally asymptotically stable (for increasing `G`,
`G′ ≥ 0`, so this is `G′(k*) < 1`). -/
theorem op_local_stability {G : ℝ → ℝ} {c d : ℝ} (hd : HasDerivAt G d c) (hfix : G c = c)
    (hd1 : |d| < 1) :
    ∃ δ > 0, ∀ k1, |k1 - c| < δ → Tendsto (fun t => G^[t] k1) atTop (𝓝 c) := by
  set q := (|d| + 1) / 2 with hq
  have hq0 : 0 < q := by have := abs_nonneg d; rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hdq : |d| < q := by rw [hq]; linarith
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  have hev : ∀ᶠ z in 𝓝[≠] c, |slope G c z| < q := by
    have hb : ∀ᶠ z in 𝓝 d, |z| < q := by
      filter_upwards [Metric.ball_mem_nhds d (show 0 < q - |d| by linarith)] with z hz
      rw [Metric.mem_ball, Real.dist_eq] at hz
      have := abs_sub_abs_le_abs_sub z d
      linarith
    exact h.eventually hb
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  have hcontr : ∀ y, |y - c| < δ → |G y - c| ≤ q * |y - c| := by
    intro y hy
    by_cases hyc : y = c
    · rw [hyc, hfix]; simp
    · have := hball (by rwa [Real.dist_eq]) hyc
      rw [slope_def_field, hfix, abs_div, div_lt_iff₀ (abs_pos.2 (sub_ne_zero.2 hyc))] at this
      linarith
  refine ⟨δ, hδ, fun k1 hk1 => ?_⟩
  have hbound : ∀ t, |G^[t] k1 - c| ≤ q ^ t * |k1 - c| := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hlt : |G^[t] k1 - c| < δ := by
        have : q ^ t ≤ 1 := pow_le_one₀ hq0.le hq1.le
        have : q ^ t * |k1 - c| ≤ |k1 - c| := by
          have := abs_nonneg (k1 - c); nlinarith
        linarith
      calc |G (G^[t] k1) - c| ≤ q * |G^[t] k1 - c| := hcontr _ hlt
        _ ≤ q * (q ^ t * |k1 - c|) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = q ^ (t + 1) * |k1 - c| := by ring
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const |k1 - c|
  rw [zero_mul] at hz
  exact squeeze_zero (fun t => abs_nonneg _) hbound hz

/-! ### The number of steady states: counterexamples to "odd" and "even" -/

/-- A continuous, strictly increasing map with `G(0) = 0`, `G′(0) = 2 > 1` and `G(k)/k → 0`:
`G(k) = max(min(2k, 2 + √k), min(2k − 9, 3√k))`. -/
noncomputable def opOddG (k : ℝ) : ℝ :=
  max (min (2 * k) (2 + Real.sqrt k)) (min (2 * k - 9) (3 * Real.sqrt k))

/-- The analogue with `G′(0) = 1/2 < 1`: `G(k) = max(min(k/2, √k), min(2k − 9, 3√k))`. -/
noncomputable def opEvenG (k : ℝ) : ℝ :=
  max (min (k / 2) (Real.sqrt k)) (min (2 * k - 9) (3 * Real.sqrt k))

/-- `max` of strictly increasing functions is strictly increasing. -/
theorem op_strictMonoOn_max {f g : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S)
    (hg : StrictMonoOn g S) : StrictMonoOn (fun x => max (f x) (g x)) S :=
  fun _ ha _ hb hab => max_lt (lt_max_of_lt_left (hf ha hb hab))
    (lt_max_of_lt_right (hg ha hb hab))

/-- `min` of strictly increasing functions is strictly increasing. -/
theorem op_strictMonoOn_min {f g : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S)
    (hg : StrictMonoOn g S) : StrictMonoOn (fun x => min (f x) (g x)) S :=
  fun _ ha _ hb hab => lt_min (lt_of_le_of_lt (min_le_left _ _) (hf ha hb hab))
    (lt_of_le_of_lt (min_le_right _ _) (hg ha hb hab))

/-- `√` is strictly increasing on `[0, ∞)`. -/
theorem op_sqrt_strictMonoOn : StrictMonoOn Real.sqrt (Set.Ici 0) :=
  fun _ ha _ _ hab => Real.sqrt_lt_sqrt ha hab

/-- `3√k/k → 0`. -/
theorem op_three_sqrt_div_tendsto : Tendsto (fun k => 3 * Real.sqrt k / k) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul 3
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hs := Real.sqrt_pos.2 hk
  have hss := Real.mul_self_sqrt hk.le
  simp only [Function.comp_apply]
  field_simp
  linarith

theorem op_sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem op_sqrt_nine : Real.sqrt 9 = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The properties of `opOddG` listed by the text: continuous, strictly increasing on
`[0, ∞)`, `G(0) = 0`, `G(k) = 2k` on `(0, 1]` (so `G′(0) = 2 > 1`), `G(k)/k → 0`. -/
theorem op_oddG_props : Continuous opOddG ∧ StrictMonoOn opOddG (Set.Ici 0) ∧ opOddG 0 = 0 ∧
    (∀ k, 0 < k → k ≤ 1 → opOddG k = 2 * k) ∧
    HasDerivWithinAt opOddG 2 (Set.Ioi 0) 0 ∧
    Tendsto (fun k => opOddG k / k) atTop (𝓝 0) := by
  have hsmall : ∀ k, 0 < k → k ≤ 1 → opOddG k = 2 * k := by
    intro k hk hk1
    have hs := Real.sqrt_nonneg k
    unfold opOddG
    rw [min_eq_left (by linarith), max_eq_left (le_trans (min_le_left _ _) (by linarith))]
  refine ⟨?_, ?_, ?_, hsmall, ?_, ?_⟩
  · unfold opOddG; fun_prop
  · have h1 : StrictMonoOn (fun k : ℝ => 2 * k) (Set.Ici 0) := fun _ _ _ _ h => by linarith
    have h2 : StrictMonoOn (fun k => 2 + Real.sqrt k) (Set.Ici 0) := fun _ ha _ hb h => by
      have := op_sqrt_strictMonoOn ha hb h; simp only; linarith
    have h3 : StrictMonoOn (fun k : ℝ => 2 * k - 9) (Set.Ici 0) := fun _ _ _ _ h => by linarith
    have h4 : StrictMonoOn (fun k => 3 * Real.sqrt k) (Set.Ici 0) := fun _ ha _ hb h => by
      have := op_sqrt_strictMonoOn ha hb h; simp only; linarith
    exact op_strictMonoOn_max (op_strictMonoOn_min h1 h2) (op_strictMonoOn_min h3 h4)
  · unfold opOddG; norm_num
  · have hd : HasDerivWithinAt (fun k : ℝ => 2 * k) 2 (Set.Ioi 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).hasDerivWithinAt
    refine hd.congr_of_eventuallyEq ?_ (by unfold opOddG; norm_num)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact hsmall k hk.1 hk.2.le
  · refine op_three_sqrt_div_tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop 9] with k hk
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ k by linarith)
    have hs3 : 3 ≤ Real.sqrt k := by rw [← op_sqrt_nine]; exact Real.sqrt_le_sqrt hk
    unfold opOddG
    rw [min_eq_right (show 3 * Real.sqrt k ≤ 2 * k - 9 by nlinarith),
      max_eq_right (le_trans (min_le_right _ _) (by linarith))]

/-- The positive steady states of `opOddG` are exactly `4` and `9`. -/
theorem op_oddG_fixed : {k : ℝ | 0 < k ∧ opOddG k = k} = {4, 9} := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hk, hG⟩
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt hk.le
    set t := Real.sqrt k
    unfold opOddG at hG
    rcases le_total (min (2 * k) (2 + t)) (min (2 * k - 9) (3 * t)) with hm | hm
    · rw [max_eq_right hm] at hG
      rcases le_total (2 * k - 9) (3 * t) with hn | hn
      · rw [min_eq_left hn] at hG; right; linarith
      · rw [min_eq_right hn] at hG
        have : t * (t - 3) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · rw [h] at hss; linarith
        · right; have : t = 3 := by linarith
          rw [this] at hss; linarith
    · rw [max_eq_left hm] at hG
      rcases le_total (2 * k) (2 + t) with hn | hn
      · rw [min_eq_left hn] at hG; linarith
      · rw [min_eq_right hn] at hG
        have : (t - 2) * (t + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; have : t = 2 := by linarith
          rw [this] at hss; linarith
        · linarith
  · rintro (rfl | rfl)
    · refine ⟨by norm_num, ?_⟩
      unfold opOddG; rw [op_sqrt_four]; norm_num
    · refine ⟨by norm_num, ?_⟩
      unfold opOddG; rw [op_sqrt_nine]; norm_num

/-- **Correction** (Miao, p. 547): "If `G′(0) > 1`, then an odd number of positive steady states
exist" is false. `opOddG` has every property the text derives for `G` (`op_oddG_props`) and
`G′(0) = 2`, but exactly two positive steady states. -/
theorem op_odd_counterexample :
    Set.ncard {k : ℝ | 0 < k ∧ opOddG k = k} = 2 ∧
      ¬ Odd (Set.ncard {k : ℝ | 0 < k ∧ opOddG k = k}) := by
  rw [op_oddG_fixed, Set.ncard_pair (by norm_num)]
  exact ⟨rfl, by decide⟩

/-- The properties of `opEvenG`: continuous, strictly increasing on `[0, ∞)`, `G(0) = 0`,
`G(k) = k/2` on `(0, 1]` (so `G′(0) = 1/2 < 1`), `G(k)/k → 0`. -/
theorem op_evenG_props : Continuous opEvenG ∧ StrictMonoOn opEvenG (Set.Ici 0) ∧
    opEvenG 0 = 0 ∧ (∀ k, 0 < k → k ≤ 1 → opEvenG k = k / 2) ∧
    HasDerivWithinAt opEvenG (1 / 2) (Set.Ioi 0) 0 ∧
    Tendsto (fun k => opEvenG k / k) atTop (𝓝 0) := by
  have hsmall : ∀ k, 0 < k → k ≤ 1 → opEvenG k = k / 2 := by
    intro k hk hk1
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt hk.le
    have hsk : k / 2 ≤ Real.sqrt k := by nlinarith
    unfold opEvenG
    rw [min_eq_left hsk, max_eq_left (le_trans (min_le_left _ _) (by linarith))]
  refine ⟨?_, ?_, ?_, hsmall, ?_, ?_⟩
  · unfold opEvenG; fun_prop
  · have h1 : StrictMonoOn (fun k : ℝ => k / 2) (Set.Ici 0) := fun _ _ _ _ h => by
      simp only; linarith
    have h3 : StrictMonoOn (fun k : ℝ => 2 * k - 9) (Set.Ici 0) := fun _ _ _ _ h => by linarith
    have h4 : StrictMonoOn (fun k => 3 * Real.sqrt k) (Set.Ici 0) := fun _ ha _ hb h => by
      have := op_sqrt_strictMonoOn ha hb h; simp only; linarith
    exact op_strictMonoOn_max (op_strictMonoOn_min h1 op_sqrt_strictMonoOn)
      (op_strictMonoOn_min h3 h4)
  · unfold opEvenG; norm_num
  · have hd : HasDerivWithinAt (fun k : ℝ => k / 2) (1 / 2) (Set.Ioi 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).hasDerivWithinAt
    refine hd.congr_of_eventuallyEq ?_ (by unfold opEvenG; norm_num)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact hsmall k hk.1 hk.2.le
  · refine op_three_sqrt_div_tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop 9] with k hk
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ k by linarith)
    have hs3 : 3 ≤ Real.sqrt k := by rw [← op_sqrt_nine]; exact Real.sqrt_le_sqrt hk
    unfold opEvenG
    rw [min_eq_right (show 3 * Real.sqrt k ≤ 2 * k - 9 by nlinarith),
      max_eq_right (le_trans (min_le_right _ _) (by linarith))]

/-- The only positive steady state of `opEvenG` is `9`. -/
theorem op_evenG_fixed : {k : ℝ | 0 < k ∧ opEvenG k = k} = {9} := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hk, hG⟩
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt hk.le
    set t := Real.sqrt k
    unfold opEvenG at hG
    rcases le_total (min (k / 2) t) (min (2 * k - 9) (3 * t)) with hm | hm
    · rw [max_eq_right hm] at hG
      rcases le_total (2 * k - 9) (3 * t) with hn | hn
      · rw [min_eq_left hn] at hG; linarith
      · rw [min_eq_right hn] at hG
        have : t * (t - 3) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · rw [h] at hss; linarith
        · have : t = 3 := by linarith
          rw [this] at hss; linarith
    · rw [max_eq_left hm] at hG
      rcases le_total (k / 2) t with hn | hn
      · rw [min_eq_left hn] at hG; linarith
      · rw [min_eq_right hn] at hG
        nlinarith
  · rintro rfl
    refine ⟨by norm_num, ?_⟩
    unfold opEvenG; rw [op_sqrt_nine]; norm_num

/-- **Correction** (Miao, p. 547): "If `G′(0) < 1`, then an even number of positive steady states
exist" is false. `opEvenG` has the listed properties and `G′(0) = 1/2`, but exactly one positive
steady state (a tangency at `k = 9`). -/
theorem op_even_counterexample :
    Set.ncard {k : ℝ | 0 < k ∧ opEvenG k = k} = 1 ∧
      ¬ Even (Set.ncard {k : ℝ | 0 < k ∧ opEvenG k = k}) := by
  rw [op_evenG_fixed, Set.ncard_singleton]
  exact ⟨rfl, by decide⟩

end Miao.OverlappingGenerations
