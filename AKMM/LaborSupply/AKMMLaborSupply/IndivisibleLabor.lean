/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.TaxesCycles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Indivisible labour, heterogeneity, and intensive and extensive margins

AKMM, §12.8, pp. 359–367.

* **Lotteries** (§12.8.1): with `U = u(c) − ψv(ℓ)`, the lottery objective
  `eU(c, ℓ̄) + (1 − e)U(c, 0) = u(c) − ψ̃e − ψv(0)` with `ψ̃ = ψ(v(ℓ̄) − v(0))` (the book drops
  `ψ`), linear in `e` (`il_lottery`); equal consumption is optimal for concave `u`
  (`il_full_insurance`); an interior `e*` with `u′(Aℓ̄e*)Aℓ̄ = ψ̃` solves the planner's problem
  (`il_planner`). **The aggregate Frisch elasticity is infinite**: with `λ` fixed, employment
  jumps from `0` to `1` at the wage `ψ̃/(λℓ̄)` (`il_frisch_infinite`); at `e* = 1` small wage
  changes leave it unchanged (fn. 16).
* **Decentralisation without lotteries** (§12.8.2, Ljungqvist–Sargent), in a finite version
  with `N` equal periods, no discounting and `r = 0`: pointwise maximisation of the Lagrangian
  with a common multiplier is sufficient (`il_lagrange_suff`); with `u′(c*)Aℓ̄ = ψ̃`, every
  work schedule `e_t ∈ {0, 1}` with `Σe_t = Ne*` and `c_t = c*` is optimal — only the total
  matters, not the timing (`il_ljungqvist_sargent`).
* **Heterogeneous `ψ`** (§12.8.3): `ṽ(e) = ∫₀^{F⁻¹(e)} ψf(ψ)dψ` has `ṽ′(e) = F⁻¹(e)`
  (`il_vtilde_deriv`) and is strictly convex (`il_vtilde_convex`), with the uniform example
  `ṽ(e) = e²/2` (`il_vtilde_uniform`); with `λ` fixed the aggregate Frisch elasticity is
  `xf(x)/F(x)`, `x = λwℓ̄`, determined by the distribution (`il_hetero_frisch`).
* **Intensive and extensive margins** (§12.8.4): (12.44) `ℓ_e = max(0, ℓ − ℓ_f)`; with a
  fixed cost or `ℓ_e = ℓ^θ` (`θ > 1`) splitting hours lowers efficiency units (the 25 + 25
  versus 50 example) (`il_concentrate`), and hours in `(0, ℓ_f]` are dominated by `ℓ = 0`
  (`il_small_hours`). **Rogerson–Wallenius**: for the pointwise problem
  `max_ℓ a·max(0, ℓ − ℓ_f) − ψℓ^{1+1/γ}/(1 + 1/γ)`, `a = μwz`, there is a threshold
  `a* = ψ((1 + γ)ℓ_f)^{1/γ}`: below it `ℓ = 0` is the unique optimum, above it `ℓ = (a/ψ)^γ`
  is, and these hours are increasing in `a` and jump from `0` to `(1 + γ)ℓ_f` at the threshold
  (`il_rw_threshold`); over the life cycle hours are positive exactly when `z(t) > z*`
  (`il_rw_life_cycle`), and with `r = 0` and no discounting pointwise optimality with
  `μ = u′(c)` gives the lifetime optimum (`il_lagrange_suff`).

Departures: the continuous-time problems of §12.8.2 and §12.8.4 are formalised with `N` equal
periods (the book uses continuous time "to avoid the integer constraint"); the
Ljungqvist–Sargent result therefore assumes `Ne*` is an integer.
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Lotteries -/

/-- AKMM, p. 360, **the lottery objective**: with `U = u(c) − ψv(ℓ)`,
`eU(c, ℓ̄) + (1 − e)U(c, 0) = u(c) − ψ̃e − ψv(0)` with `ψ̃ = ψ(v(ℓ̄) − v(0))`, linear in `e`. -/
theorem il_lottery (u v : ℝ → ℝ) (ψ c e lbar : ℝ) :
    e * (u c - ψ * v lbar) + (1 - e) * (u c - ψ * v 0) =
      u c - ψ * (v lbar - v 0) * e - ψ * v 0 := by ring

/-- AKMM, p. 360: with separable utility and concave `u`, giving everyone the same consumption
is optimal: `eu(c₁) + (1 − e)u(c₀) ≤ u(ec₁ + (1 − e)c₀)`. -/
theorem il_full_insurance {u : ℝ → ℝ} {e c₀ c₁ : ℝ} (hu : ConcaveOn ℝ (Set.Ioi 0) u)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    e * u c₁ + (1 - e) * u c₀ ≤ u (e * c₁ + (1 - e) * c₀) := by
  have := hu.2 (Set.mem_Ioi.2 hc₁) (Set.mem_Ioi.2 hc₀) he0 (by linarith : 0 ≤ 1 - e)
    (by ring)
  simpa [smul_eq_mul] using this

/-- AKMM, p. 360, **the planner with indivisible labour**: if `u` has supergradient `μ` at
`c* = Aℓ̄e*` (as a concave differentiable `u` does with `μ = u′(c*)`) and `μAℓ̄ = ψ̃`, then `e*`
maximises `u(Aℓ̄e) − ψ̃e` over `e ∈ (0, 1]`. -/
theorem il_planner {u : ℝ → ℝ} {A lbar ψt μ es : ℝ}
    (hsup : ∀ x, 0 < x → u x ≤ u (A * lbar * es) + μ * (x - A * lbar * es))
    (hfoc : μ * (A * lbar) = ψt) (hpos : 0 < A * lbar) :
    ∀ e, 0 < e → u (A * lbar * e) - ψt * e ≤ u (A * lbar * es) - ψt * es := by
  intro e he
  have := hsup (A * lbar * e) (mul_pos hpos he)
  rw [← hfoc]
  nlinarith

/-- AKMM, p. 361, **the aggregate Frisch elasticity is infinite**: with `λ > 0` fixed, the
aggregate supply problem `max_{e ∈ [0, 1]} (λwℓ̄ − ψ̃)e` has the unique solution `e = 1` when
`w > ψ̃/(λℓ̄)` and `e = 0` when `w < ψ̃/(λℓ̄)`, and every `e` is optimal at the threshold: an
arbitrarily small wage change around it moves employment from `0` to `1`. When `e = 1` is
optimal at `w`, it stays optimal at all nearby wages, so the elasticity is then zero (fn. 16). -/
theorem il_frisch_infinite {lam lbar ψt : ℝ} (hlam : 0 < lam) (hlbar : 0 < lbar) :
    (∀ w, ψt / (lam * lbar) < w → ∀ e, e < 1 →
      (lam * w * lbar - ψt) * e < (lam * w * lbar - ψt) * 1) ∧
    (∀ w, w < ψt / (lam * lbar) → ∀ e, 0 < e →
      (lam * w * lbar - ψt) * e < (lam * w * lbar - ψt) * 0) ∧
    (∀ e, (lam * (ψt / (lam * lbar)) * lbar - ψt) * e = 0) ∧
    (∀ w, ψt / (lam * lbar) < w → ∀ᶠ w' in 𝓝 w, ψt / (lam * lbar) < w') := by
  have hk : 0 < lam * lbar := mul_pos hlam hlbar
  refine ⟨fun w hw e he => ?_, fun w hw e he => ?_, fun e => ?_, fun w hw => lt_mem_nhds hw⟩
  · have : 0 < lam * w * lbar - ψt := by
      rw [div_lt_iff₀ hk] at hw; linarith
    nlinarith
  · have : lam * w * lbar - ψt < 0 := by
      rw [lt_div_iff₀ hk] at hw; linarith
    nlinarith
  · field_simp; ring

/-! ### Decentralisation: Ljungqvist and Sargent -/

/-- AKMM, pp. 361–362 and 366–367, **pointwise maximisation is sufficient** (no discounting,
`r = 0`, `N` periods). Let `u` have supergradient `μ` at `c` (`u(x) ≤ u(c) + μ(x − c)`), let the
plan consume `c` in every period and choose `x_t` with `Nc = Σ_t y_t(x_t)`, and let each `x_t`
maximise `μy_t(x) − d_t(x)` over `S_t`. Then for every plan `(c′, x′)` with `x′_t ∈ S_t` and
`Σc′_t = Σy_t(x′_t)`, `Σ_t [u(c′_t) − d_t(x′_t)] ≤ Σ_t [u(c) − d_t(x_t)]`. -/
theorem il_lagrange_suff {X : Type*} {N : ℕ} {u : ℝ → ℝ} {c μ : ℝ} {y d : Fin N → X → ℝ}
    {S : Fin N → Set X} {x : Fin N → X}
    (hsup : ∀ z, 0 < z → u z ≤ u c + μ * (z - c))
    (hbud : N * c = ∑ t, y t (x t))
    (hpt : ∀ t, ∀ z ∈ S t, μ * y t z - d t z ≤ μ * y t (x t) - d t (x t))
    {c' : Fin N → ℝ} {x' : Fin N → X} (hc' : ∀ t, 0 < c' t) (hx' : ∀ t, x' t ∈ S t)
    (hbud' : ∑ t, c' t = ∑ t, y t (x' t)) :
    ∑ t, (u (c' t) - d t (x' t)) ≤ ∑ t, (u c - d t (x t)) := by
  have h1 : ∑ t, (u (c' t) - d t (x' t)) ≤
      ∑ t, (u c + μ * (c' t - c) - d t (x' t)) :=
    Finset.sum_le_sum fun t _ => by linarith [hsup (c' t) (hc' t)]
  have h2 : ∑ t, (u c + μ * (c' t - c) - d t (x' t)) =
      ∑ _t : Fin N, (u c - μ * c) + ∑ t, (μ * y t (x' t) - d t (x' t)) := by
    rw [← Finset.sum_add_distrib]
    have : ∑ t, μ * (c' t - c) = ∑ t, μ * y t (x' t) - ∑ _t : Fin N, μ * c := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hbud']
    have e1 : ∑ t, (u c + μ * (c' t - c) - d t (x' t)) =
        ∑ t : Fin N, u c + ∑ t, μ * (c' t - c) - ∑ t, d t (x' t) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [e1, this]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have h3 : ∑ t, (μ * y t (x' t) - d t (x' t)) ≤ ∑ t, (μ * y t (x t) - d t (x t)) :=
    Finset.sum_le_sum fun t _ => hpt t (x' t) (hx' t)
  have h4 : ∑ _t : Fin N, (u c - μ * c) + ∑ t, (μ * y t (x t) - d t (x t)) =
      ∑ t, (u c - d t (x t)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, ← hbud]
    ring
  linarith

/-- AKMM, p. 362, **Ljungqvist–Sargent: indifference over timing**. With `N` equal periods,
no discounting, `r = 0`, wage `A`, `U(c, eℓ̄) = u(c) − ψv(eℓ̄)`, `e_t ∈ {0, 1}`: if `u` has
supergradient `μ` at `c*` with `μAℓ̄ = ψ(v(ℓ̄) − v(0))` (the planner's condition), then every
schedule `e` with `Nc* = Σ_t e_tℓ̄A` — whatever the timing — together with `c_t = c*` is optimal
among all plans satisfying the lifetime budget `Σc′_t = Σe′_tℓ̄A`. -/
theorem il_ljungqvist_sargent {N : ℕ} {u v : ℝ → ℝ} {ψ A lbar cs μ : ℝ}
    (hsup : ∀ z, 0 < z → u z ≤ u cs + μ * (z - cs))
    (hfoc : μ * (A * lbar) = ψ * (v lbar - v 0)) {e : Fin N → ℝ}
    (he : ∀ t, e t = 0 ∨ e t = 1) (hbud : N * cs = ∑ t, e t * lbar * A)
    {c' e' : Fin N → ℝ} (hc' : ∀ t, 0 < c' t) (he' : ∀ t, e' t = 0 ∨ e' t = 1)
    (hbud' : ∑ t, c' t = ∑ t, e' t * lbar * A) :
    ∑ t, (u (c' t) - ψ * v (e' t * lbar)) ≤ ∑ t, (u cs - ψ * v (e t * lbar)) := by
  refine il_lagrange_suff (S := fun _ => {z : ℝ | z = 0 ∨ z = 1}) (y := fun _ z => z * lbar * A)
    (d := fun _ z => ψ * v (z * lbar)) hsup hbud ?_ hc' he' hbud'
  intro t z hz
  -- `μ·zℓ̄A − ψv(zℓ̄)` is the same for `z = 0` and `z = 1`
  have hval : ∀ z : ℝ, z = 0 ∨ z = 1 → μ * (z * lbar * A) - ψ * v (z * lbar) = -(ψ * v 0) := by
    intro z hz
    rcases hz with rfl | rfl
    · simp only [zero_mul, mul_zero, zero_sub]
    · simp only [one_mul]; linear_combination hfoc
  rw [hval z hz, hval (e t) (he t)]

/-! ### Heterogeneity in the disutility of work -/

/-- AKMM, p. 363, **`ṽ′(e) = F⁻¹(e)`**: let `F` have density `f` (continuous), `Q` a local
inverse of `F` near `e` continuous at `e`, with `f(Q(e)) > 0`. Then
`ṽ(e) = ∫₀^{Q(e)} ψf(ψ)dψ` has derivative `Q(e)` at `e`. -/
theorem il_vtilde_deriv {F f Q : ℝ → ℝ} {e : ℝ} (hf : Continuous f) (hQ : ContinuousAt Q e)
    (hF : HasDerivAt F (f (Q e)) (Q e)) (hfpos : f (Q e) ≠ 0)
    (hFQ : ∀ᶠ y in 𝓝 e, F (Q y) = y) :
    HasDerivAt (fun y => ∫ x in (0 : ℝ)..Q y, x * f x) (Q e) e := by
  have hQd : HasDerivAt Q (f (Q e))⁻¹ e := HasDerivAt.of_local_left_inverse hQ hF hfpos hFQ
  have hI := ((continuous_id.mul hf).integral_hasStrictDerivAt 0 (Q e)).hasDerivAt
  have := hI.comp e hQd
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, id_eq]
  field_simp

/-- AKMM, p. 363, **`ṽ` is strictly convex**: if on `(0, 1)` `ṽ` has derivative `Q(e)` and `Q`
(the quantile function `F⁻¹`) is strictly increasing, then `ṽ` is strictly convex there. -/
theorem il_vtilde_convex {vt Q : ℝ → ℝ} (hd : ∀ e ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt vt (Q e) e)
    (hQ : StrictMonoOn Q (Set.Ioo 0 1)) : StrictConvexOn ℝ (Set.Ioo 0 1) vt := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioo 0 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro x hx y hy hxy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    exact hQ hx hy hxy

/-- AKMM, p. 363: the uniform distribution on `[0, 1]` (`F = f·id`, `f ≡ 1`, `Q = id`)
satisfies the hypotheses of `il_vtilde_deriv`, and `ṽ(e) = e²/2`, strictly convex. -/
theorem il_vtilde_uniform (e : ℝ) :
    HasDerivAt (fun y => ∫ x in (0 : ℝ)..id y, x * (fun _ => (1 : ℝ)) x) (id e) e ∧
      (∫ x in (0 : ℝ)..e, x * (fun _ => (1 : ℝ)) x) = e ^ 2 / 2 ∧
      StrictConvexOn ℝ (Set.Ioo 0 1) (fun y => ∫ x in (0 : ℝ)..id y, x * (fun _ => (1 : ℝ)) x) := by
  have hd : ∀ e, HasDerivAt (fun y => ∫ x in (0 : ℝ)..id y, x * (fun _ => (1 : ℝ)) x) (id e) e :=
    fun e => il_vtilde_deriv (F := id) continuous_const continuousAt_id
      (by simpa using hasDerivAt_id (id e)) one_ne_zero (Eventually.of_forall fun _ => rfl)
  refine ⟨hd e, by simp [integral_id], ?_⟩
  exact il_vtilde_convex (fun e _ => hd e) (strictMono_id.strictMonoOn _)

/-- AKMM, p. 363: **the aggregate Frisch elasticity with heterogeneity** is finite and set by
the distribution: with `λ` fixed, the planner employs everyone with `ψ < λwℓ̄`, so `e = F(λwℓ̄)`,
and along `w(s) = we^s`, `d log e/d log w = xf(x)/F(x)`, `x = λwℓ̄`. -/
theorem il_hetero_frisch {F f : ℝ → ℝ} {lam w lbar : ℝ}
    (hF : HasDerivAt F (f (lam * w * lbar)) (lam * w * lbar)) (hFpos : 0 < F (lam * w * lbar)) :
    HasDerivAt (fun s => Real.log (F (lam * (w * Real.exp s) * lbar)))
      (lam * w * lbar * f (lam * w * lbar) / F (lam * w * lbar)) 0 := by
  have hin : HasDerivAt (fun s => lam * (w * Real.exp s) * lbar) (lam * w * lbar) 0 := by
    have := ((st_exp_path w).const_mul lam).mul_const lbar
    exact this.congr_deriv (by ring)
  have h0 : lam * (w * Real.exp 0) * lbar = lam * w * lbar := by rw [Real.exp_zero, mul_one]
  have hF' : HasDerivAt F (f (lam * w * lbar)) (lam * (w * Real.exp 0) * lbar) := by
    rw [h0]; exact hF
  have hFpos' : (F ∘ fun s => lam * (w * Real.exp s) * lbar) 0 ≠ 0 := by
    simp only [Function.comp_apply, h0]; exact hFpos.ne'
  have := (hF'.comp 0 hin).log hFpos'
  refine this.congr_deriv ?_
  simp only [Function.comp_apply, h0]
  ring

/-! ### Intensive and extensive margins -/

/-- AKMM, (12.44), p. 365: efficiency units with a fixed time cost, `max(0, ℓ − ℓ_f)`. -/
noncomputable def effHours (lf l : ℝ) : ℝ := max 0 (l - lf)

/-- AKMM, pp. 365–366, **concentrating hours**: with a fixed cost `ℓ_f > 0`, splitting `ℓ > ℓ_f`
into two halves gives fewer efficiency units; with `ℓ_e = ℓ^θ`, `θ > 1`, so does any split
`2(ℓ/2)^θ < ℓ^θ`, e.g. `2·25^θ < 50^θ`. -/
theorem il_concentrate {lf l θ : ℝ} (hlf : 0 < lf) (hl : lf < l) (hθ : 1 < θ) :
    2 * effHours lf (l / 2) < effHours lf l ∧ 2 * (l / 2) ^ θ < l ^ θ ∧
      2 * (25 : ℝ) ^ θ < (50 : ℝ) ^ θ := by
  have hpow : ∀ x : ℝ, 0 < x → 2 * (x / 2) ^ θ < x ^ θ := by
    intro x hx
    rw [Real.div_rpow hx.le (by norm_num)]
    have h2 : (2 : ℝ) < 2 ^ θ := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hθ
      simpa using this
    have hxp : 0 < x ^ θ := Real.rpow_pos_of_pos hx _
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨?_, hpow l (by linarith), ?_⟩
  · unfold effHours
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ l - lf)]
    rcases le_or_gt (l / 2 - lf) 0 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  · have := hpow 50 (by norm_num)
    norm_num at this ⊢
    exact this

/-- AKMM, pp. 365–366: with a fixed cost, hours `ℓ ∈ (0, ℓ_f]` produce no efficiency units and
are strictly worse than not working, for strictly increasing disutility `v`. -/
theorem il_small_hours {u v : ℝ → ℝ} {I w z lf l : ℝ} (hv : StrictMono v) (hl0 : 0 < l)
    (hl : l ≤ lf) : u (I + w * z * effHours lf l) - v l < u (I + w * z * effHours lf 0) - v 0 := by
  unfold effHours
  rw [max_eq_left (by linarith : l - lf ≤ 0), max_eq_left (by linarith : (0 : ℝ) - lf ≤ 0)]
  have := hv hl0
  linarith

/-- AKMM, p. 366–367, **the Rogerson–Wallenius threshold**. For the pointwise problem
`J(a, ℓ) = a·max(0, ℓ − ℓ_f) − ψℓ^{1+1/γ}/(1 + 1/γ)` (`a = μwz > 0`), with
`a* = ψ((1 + γ)ℓ_f)^{1/γ}`: if `a < a*`, `ℓ = 0` is the unique maximiser over `ℓ ≥ 0`; if
`a > a*`, `ℓ(a) = (a/ψ)^γ > ℓ_f` is; and `ℓ(a*) = (1 + γ)ℓ_f`, so hours jump at the threshold
(extensive margin) and increase with `a` above it (intensive margin). -/
theorem il_rw_threshold {ψ γ lf a : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hlf : 0 < lf) (ha : 0 < a) :
    (a < ψ * ((1 + γ) * lf) ^ (1 / γ) → ∀ l, 0 < l →
      a * effHours lf l - disutil ψ γ l < a * effHours lf 0 - disutil ψ γ 0) ∧
    (ψ * ((1 + γ) * lf) ^ (1 / γ) < a → lf < (a / ψ) ^ γ ∧ ∀ l, 0 ≤ l → l ≠ (a / ψ) ^ γ →
      a * effHours lf l - disutil ψ γ l < a * effHours lf ((a / ψ) ^ γ) -
        disutil ψ γ ((a / ψ) ^ γ)) ∧
    ((ψ * ((1 + γ) * lf) ^ (1 / γ) / ψ) ^ γ = (1 + γ) * lf) ∧
    StrictMonoOn (fun a => (a / ψ) ^ γ) (Set.Ioi 0) := by
  set la := (a / ψ) ^ γ with hla
  have hk : 0 < a / ψ := by positivity
  have hlapos : 0 < la := Real.rpow_pos_of_pos hk _
  obtain ⟨hfoc, hval⟩ := fr_opt_facts hψ hγ ha
  rw [← hla] at hfoc hval
  have hγ' : 0 < 1 / γ := by positivity
  have hd0 : disutil ψ γ 0 = 0 := by
    unfold disutil
    have hp0 : (1 + 1 / γ) ≠ 0 := by positivity
    rw [Real.zero_rpow hp0]
    simp
  have heff0 : effHours lf 0 = 0 := by unfold effHours; simp; linarith
  have hdpos : ∀ l, 0 < l → 0 < disutil ψ γ l := fun l hl => by
    unfold disutil; have : 0 < 1 + 1 / γ := by positivity
    have := Real.rpow_pos_of_pos hl (1 + 1 / γ); positivity
  -- the tangent inequality: `v(ℓ) ≥ v(ℓ_a) + a(ℓ − ℓ_a)`, strict for `ℓ ≠ ℓ_a`
  have htan : ∀ l, 0 ≤ l → l ≠ la → disutil ψ γ la + a * (l - la) < disutil ψ γ l := by
    intro l hl hne
    have hp : 1 < 1 + 1 / γ := by linarith
    have ht := fr_rpow_tangent hp hl hlapos hne
    rw [show 1 + 1 / γ - 1 = 1 / γ by ring] at ht
    unfold disutil
    have hg : 0 < 1 + 1 / γ := by linarith
    rw [div_add' _ _ _ hg.ne', div_lt_div_iff_of_pos_right hg, ← hfoc]
    nlinarith [mul_lt_mul_of_pos_left ht hψ]
  -- the value of working: `W(a) = aℓ_a/(1 + γ) − aℓ_f`
  have hW : a * (la - lf) - disutil ψ γ la = a * la / (1 + γ) - a * lf := by linarith
  -- `ℓ_a > (1 + γ)ℓ_f` iff `a > a*`
  have hthr : ∀ b, 0 < b → (ψ * ((1 + γ) * lf) ^ (1 / γ) < b ↔ (1 + γ) * lf < (b / ψ) ^ γ) := by
    intro b hb
    have hq : 0 < (1 + γ) * lf := by positivity
    constructor
    · intro h
      have h1 : ((1 + γ) * lf) ^ (1 / γ) < b / ψ := by rw [lt_div_iff₀ hψ]; linarith
      have := Real.rpow_lt_rpow (Real.rpow_nonneg hq.le _) h1 hγ
      rwa [← Real.rpow_mul hq.le, one_div_mul_cancel hγ.ne', Real.rpow_one] at this
    · intro h
      have := Real.rpow_lt_rpow hq.le h (by positivity : 0 < 1 / γ)
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hγ.ne', Real.rpow_one,
        lt_div_iff₀ hψ] at this
      linarith
  refine ⟨fun hlow l hl => ?_, fun hhigh => ?_, ?_, ?_⟩
  · rw [heff0, hd0, mul_zero, sub_zero]
    rcases le_or_gt l lf with h | h
    · unfold effHours; rw [max_eq_left (by linarith)]
      simp only [mul_zero, zero_sub, neg_lt_zero]; exact hdpos l hl
    · unfold effHours; rw [max_eq_right (by linarith)]
      have hla' : la ≤ (1 + γ) * lf := by
        by_contra hc; exact absurd ((hthr a ha).2 (not_le.1 hc)) (not_lt.2 hlow.le)
      have hWneg : a * la / (1 + γ) - a * lf ≤ 0 := by
        rw [div_sub' (by positivity), div_nonpos_iff]
        right; constructor <;> nlinarith
      rcases eq_or_ne l la with heq | hne
      · rw [heq]
        have : a * la / (1 + γ) - a * lf < 0 ∨ a * la / (1 + γ) - a * lf = 0 :=
          lt_or_eq_of_le hWneg
        rcases this with h' | h'
        · linarith
        · -- `W(a) = 0` means `ℓ_a = (1 + γ)ℓ_f`, i.e. `a = a*`, excluded
          exfalso
          have : la = (1 + γ) * lf := by
            have hγ1 : (0 : ℝ) < 1 + γ := by linarith
            field_simp at h'
            nlinarith
          have hle := (hthr a ha).1
          have : ψ * ((1 + γ) * lf) ^ (1 / γ) = a := by
            rw [← this, hla, ← Real.rpow_mul hk.le, mul_one_div_cancel hγ.ne', Real.rpow_one]
            field_simp
          linarith
      · have := htan l hl.le hne
        linarith
  · have hla_gt : (1 + γ) * lf < la := (hthr a ha).1 hhigh
    have hlf : lf < la := by nlinarith
    refine ⟨hlf, fun l hl hne => ?_⟩
    have heffa : effHours lf la = la - lf := by unfold effHours; rw [max_eq_right (by linarith)]
    rw [heffa, hW]
    have hWpos : 0 < a * la / (1 + γ) - a * lf := by
      rw [div_sub' (by positivity)]
      apply div_pos _ (by positivity)
      nlinarith
    rcases le_or_gt l lf with h | h
    · unfold effHours; rw [max_eq_left (by linarith)]
      rcases eq_or_lt_of_le hl with h0 | h0
      · rw [← h0, hd0]; linarith
      · have := hdpos l h0; linarith
    · unfold effHours; rw [max_eq_right (by linarith)]
      have := htan l hl hne
      linarith
  · have hq : 0 < (1 + γ) * lf := by positivity
    rw [mul_div_cancel_left₀ _ hψ.ne', ← Real.rpow_mul hq.le, one_div_mul_cancel hγ.ne',
      Real.rpow_one]
  · intro x hx y hy hxy
    exact Real.rpow_lt_rpow (div_pos hx hψ).le (div_lt_div_of_pos_right hxy hψ) hγ

/-- AKMM, pp. 366–367, **the life-cycle profile** of Rogerson–Wallenius: with productivity
`z(t) ≥ 0`, multiplier `μ > 0` and wage `w > 0`, put `z* = a*/(μw)`. At every date with
`z(t) < z*` the unique optimal hours are `0`; at every date with `z(t) > z*` they are
`(μwz(t)/ψ)^γ > ℓ_f`, increasing in `z(t)`. In particular hours are zero at `t = 0` and `t = T`
when `z(0) = z(T) = 0`. -/
theorem il_rw_life_cycle {ψ γ lf μ w : ℝ} {z : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hlf : 0 < lf)
    (hμ : 0 < μ) (hw : 0 < w) (t : ℝ) (hz : 0 < z t) :
    (z t < ψ * ((1 + γ) * lf) ^ (1 / γ) / (μ * w) → ∀ l, 0 < l →
      μ * w * z t * effHours lf l - disutil ψ γ l < μ * w * z t * effHours lf 0 - disutil ψ γ 0) ∧
    (ψ * ((1 + γ) * lf) ^ (1 / γ) / (μ * w) < z t → lf < (μ * w * z t / ψ) ^ γ ∧
      ∀ l, 0 ≤ l → l ≠ (μ * w * z t / ψ) ^ γ →
        μ * w * z t * effHours lf l - disutil ψ γ l <
          μ * w * z t * effHours lf ((μ * w * z t / ψ) ^ γ) -
            disutil ψ γ ((μ * w * z t / ψ) ^ γ)) := by
  have hmw : 0 < μ * w := mul_pos hμ hw
  have ha : 0 < μ * w * z t := mul_pos hmw hz
  obtain ⟨h1, h2, -, -⟩ := il_rw_threshold hψ hγ hlf ha
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [lt_div_iff₀ hmw] at h; linarith
  · rw [div_lt_iff₀ hmw] at h; linarith

end AKMM.LaborSupply
