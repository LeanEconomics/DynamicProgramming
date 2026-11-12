/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.ISTCPredictions
import AKMMContinuousTime.Mangasarian
import AKMMContinuousTime.RamseySaddle

/-!
# Optimality of the balanced growth path

AKMM, §13.3 (pp. 377–379) and Appendix 13.A.1–13.A.2 (pp. 850–851). Mathlib has no Pontryagin
maximum principle; the book's first-order conditions are shown to be *sufficient* using the
Mangasarian–Arrow theorem of AKMM Chapter 9 (`AKMM.ContinuousTime.mangasarian_catching_up`).

The planner's problem (13.A.12) is written in per-capita wealth `a = Ke^{−γ_x t}/(A_x e^{nt})`
(capital per head valued in consumption units, which is the household's wealth under
asset-market clearing): `ȧ = Θe^{(1−α)g_c t}a^α − (δ + γ_x + n)a − c` with
`Θ = A_x^α(A_y h)^{1−α}` (`istc_capital_to_wealth`, from `istc_budget_reduced`), discount rate
`ρ − n`, and `r − n = ∂ȧ/∂a` (`istc_return_reduced`).

* `istc_optimal`: a path with the budget, the Euler equation (13.A.7) and the TVC
  `e^{−(ρ−n)T}c(T)^{−σ}a(T) → 0` ((13.A.11)) is catching-up optimal against every feasible path
  with `a ≥ 0` from the same initial wealth, for any concave `u` with `u'(c) = c^{−σ}` (CRRA for
  `σ ≠ 1`, log for `σ = 1`: `istc_crra_concave`, `istc_log_concave`).
* `istc_bgp_optimal`: under (13.8), the balanced growth path (13.14)–(13.15) from
  `K(0) = k̃*` is optimal; hence it is also the equilibrium (planner = equilibrium, p. 851).
* `istc_closed_form_optimal`: for `σ = α` the closed-form transition (p. 381) is optimal from
  every `K(0) > 0`.
-/

namespace AKMM.Growth

open Real Filter Topology

/-- CRRA utility `(c^{1−σ} − 1)/(1 − σ)` (AKMM (13.4)) is concave on `(0, ∞)` with
`u'(c) = c^{−σ}`, for `0 < σ ≠ 1`. -/
theorem istc_crra_concave {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    ConcaveOn ℝ (Set.Ioi 0) (AKMM.ContinuousTime.crraUtility σ) ∧
      ∀ y, 0 < y → HasDerivAt (AKMM.ContinuousTime.crraUtility σ) (y ^ (-σ)) y := by
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : AKMM.ContinuousTime.crraUtility σ =
      fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [AKMM.ContinuousTime.crraUtility]; ring
  have hp := AKMM.ContinuousTime.ramseySaddle_power_props (1 / (1 - σ)) (-(1 / (1 - σ)))
    (1 - σ) (by rw [one_div, inv_mul_cancel₀ h1σ]; exact one_pos) (by linarith)
  refine ⟨?_, fun y hy => (AKMM.ContinuousTime.continuousHamiltonian_crra_derivs hσ1 hy).1⟩
  rw [hu]
  exact hp.2.2.2.2.2.2.2.2.concaveOn

/-- Log utility (the case `σ = 1` of (13.4)) is concave on `(0, ∞)` with `u'(c) = c^{−1}`. -/
theorem istc_log_concave :
    ConcaveOn ℝ (Set.Ioi 0) Real.log ∧ ∀ y : ℝ, 0 < y → HasDerivAt Real.log (y ^ (-(1 : ℝ))) y :=
  ⟨strictConcaveOn_log_Ioi.concaveOn, fun y hy => by
    rw [Real.rpow_neg_one]; exact Real.hasDerivAt_log hy.ne'⟩

/-- The tangent-line inequality for `y^α`, `0 < α < 1`: `y^α ≤ x^α + αx^{α−1}(y − x)` for
`x > 0`, `y ≥ 0`. -/
theorem istc_rpow_tangent {α x y : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hy : 0 ≤ y) :
    y ^ α ≤ x ^ α + α * x ^ (α - 1) * (y - x) := by
  have hb := rpow_one_add_le_one_add_mul_self (s := y / x - 1) (by
    have : 0 ≤ y / x := div_nonneg hy hx.le
    linarith) hα0.le hα1.le
  rw [show 1 + (y / x - 1) = y / x by ring, Real.div_rpow hy hx.le] at hb
  have hxa : 0 < x ^ α := by positivity
  rw [div_le_iff₀ hxa] at hb
  rw [Real.rpow_sub_one hx.ne']
  have e : (1 + α * (y / x - 1)) * x ^ α = x ^ α + α * (x ^ α / x) * (y - x) := by
    field_simp
  linarith

/-- AKMM, (13.A.8) and p. 851: **the planner's constraint in per-capita wealth**. If capital
satisfies `K̇ = A_x e^{γ_x t}(K^α(A_y e^{γ_y t}e^{nt}h)^{1−α} − e^{nt}c) − δK` and
`K = A_x e^{(γ_x+n)t}a` with `a > 0`, then
`ȧ = A_x^α(A_y h)^{1−α}e^{(1−α)g_c t}a^α − (δ + γ_x + n)a − c`. -/
theorem istc_capital_to_wealth {α Ax Ay h δ γx γy n t c : ℝ} {K a : ℝ → ℝ} (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (ha : 0 < a t)
    (hKa : K = fun s => Ax * Real.exp ((γx + n) * s) * a s)
    (hK : HasDerivAt K (Ax * Real.exp (γx * t) * (K t ^ α * (Ay * Real.exp (γy * t) *
      (Real.exp (n * t) * h)) ^ (1 - α) - Real.exp (n * t) * c) - δ * K t) t) :
    HasDerivAt a (Ax ^ α * (Ay * h) ^ (1 - α) * Real.exp ((1 - α) * istcGc α γx γy * t) *
      a t ^ α - (δ + γx + n) * a t - c) t := by
  have hEp := Real.exp_pos ((γx + n) * t)
  have haK : a = fun s => K s * (Real.exp (-(γx + n) * s) / Ax) := by
    funext s
    rw [hKa]
    have : Real.exp ((γx + n) * s) * Real.exp (-(γx + n) * s) = 1 := by
      rw [← Real.exp_add, show (γx + n) * s + -(γx + n) * s = 0 by ring, Real.exp_zero]
    rw [mul_div_assoc', eq_div_iff hAx.ne']
    linear_combination (-(a s * Ax)) * this
  have hd := hK.mul (((hasDerivAt_id' t).const_mul (-(γx + n))).exp.div_const Ax)
  have hKt : K t = Ax * Real.exp ((γx + n) * t) * a t := by rw [hKa]
  have hat : K t * (Real.exp (-(γx + n) * t) / Ax) = a t := by
    rw [haK]
  rw [haK]
  convert hd using 1
  beta_reduce
  rw [hat]
  have hout := istc_output_reduced (Ax := Ax) (Ay := Ay) (h := h) (γx := γx) (γy := γy) (n := n)
    (t := t) hα1 hAx hAy hh ha
  rw [← hKt] at hout
  rw [← hout]
  have hE1 : Real.exp (-(γx + n) * t) = (Real.exp ((γx + n) * t))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  have h1 : Ax * Ax⁻¹ = 1 := mul_inv_cancel₀ hAx.ne'
  have h2 : Real.exp (γx * t) * Real.exp (-(γx + n) * t) = Real.exp (-n * t) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-n * t) * Real.exp (n * t) = 1 := by rw [← Real.exp_add]; simp
  have h4 : K t * Real.exp (-(γx + n) * t) * Ax⁻¹ = a t := by
    rw [hKt, hE1]; field_simp
  set Y := K t ^ α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^ (1 - α)
  set E := Real.exp (-(γx + n) * t)
  linear_combination (-(Real.exp (γx * t) * E * Y)) * h1 + (-Y) * h2 +
    (Real.exp (γx * t) * E * Real.exp (n * t) * c) * h1 + (c * Real.exp (n * t)) * h2 + c * h3 +
    (δ + γx + n) * h4

/-- AKMM, (13.A.4)–(13.A.12), pp. 850–851: **sufficiency of the first-order conditions**. Let
`u` be concave on `(0, ∞)` with `u'(c) = c^{−σ}`, `Θ > 0`, and write
`G(t, a) = Θe^{(1−α)g_c t}a^α − (δ + γ_x + n)a` and `r(t) − n = ∂G/∂a(t, a(t))`
(`istc_return_reduced`). If `(a, c)` has `a, c > 0`, `c` continuous, the budget `ȧ = G − c`,
the Euler equation `ċ = c(r − ρ)/σ` (13.A.7) and the TVC
`e^{−(ρ−n)T}c(T)^{−σ}a(T) → 0` (13.A.11), then it is catching-up optimal for
`∫e^{−(ρ−n)t}u(c)` against every path `(a', c')` from `a(0)` with `a' ≥ 0`, `c' > 0`
continuous and `ȧ' = G − c'`. -/
theorem istc_optimal {α σ ρ δ γx γy n Θ : ℝ} {u : ℝ → ℝ} {a c a' c' : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ) (hΘ : 0 < Θ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (ha : ∀ t, 0 ≤ t → 0 < a t) (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hbud : ∀ t, 0 ≤ t → HasDerivAt a (Θ * Real.exp ((1 - α) * istcGc α γx γy * t) * a t ^ α -
      (δ + γx + n) * a t - c t) t)
    (heuler : ∀ t, 0 ≤ t → HasDerivAt c (c t * ((α * (Θ * Real.exp ((1 - α) * istcGc α γx γy *
      t)) * a t ^ (α - 1) - (δ + γx + n) + n) - ρ) / σ) t)
    (htvc : Tendsto (fun T => Real.exp (-(ρ - n) * T) * c T ^ (-σ) * a T) atTop (𝓝 0))
    (ha' : ∀ t, 0 ≤ t → 0 ≤ a' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hbud' : ∀ t, 0 ≤ t → HasDerivAt a' (Θ * Real.exp ((1 - α) * istcGc α γx γy * t) *
      a' t ^ α - (δ + γx + n) * a' t - c' t) t) (h0 : a' 0 = a 0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c t)) + ε := by
  set E := fun t : ℝ => Θ * Real.exp ((1 - α) * istcGc α γx γy * t)
  have hE : ∀ t, 0 < E t := fun t => by positivity
  set μ := fun t => Real.exp (-(ρ - n) * t) * c t ^ (-σ)
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    have := hc t ht; positivity
  have hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (α * E t * a t ^ (α - 1) - (δ + γx + n)))) t :=
    fun t ht => by
      have h := istc_costate_of_euler (n := n) hσ (hc t ht) (heuler t ht)
      convert h using 1
      ring
  have hG : ∀ t, 0 ≤ t → E t * a' t ^ α - (δ + γx + n) * a' t ≤
      E t * a t ^ α - (δ + γx + n) * a t + (α * E t * a t ^ (α - 1) - (δ + γx + n)) *
        (a' t - a t) := fun t ht => by
    have htan := istc_rpow_tangent hα0 hα1 (ha t ht) (ha' t ht)
    have := mul_le_mul_of_nonneg_left htan (hE t).le
    nlinarith
  refine (AKMM.ContinuousTime.mangasarian_catching_up (ρ := ρ - n) (u' := fun y => y ^ (-σ))
    (G := fun t y => E t * y ^ α - (δ + γx + n) * y)
    (Gx := fun t y => α * E t * y ^ (α - 1) - (δ + γx + n)) (μ := μ)
    hconc hu hc hcc hbud hμ (fun t _ => rfl) hμ0 hc' hcc' hbud' h0 hG ?_).1
  intro ε hε
  filter_upwards [htvc.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
  have := mul_nonneg (hμ0 T hT) (ha' T hT)
  have e : μ T * (a T - a' T) = Real.exp (-(ρ - n) * T) * c T ^ (-σ) * a T - μ T * a' T := by
    simp only [μ]; ring
  rw [e]
  linarith

/-- AKMM, (13.14)–(13.15) and p. 379: **the balanced growth path is optimal**. Under (13.8)
and `g_K + δ > 0`, the path `a(t) = (k̃*/A_x)e^{g_c t}`, `c(t) = c̃*e^{g_c t}` (that is,
`K = k̃*e^{g_K t}`) satisfies the budget, the Euler equation and the TVC, so by `istc_optimal`
it is catching-up optimal for the planner's problem (13.A.12) from `K(0) = k̃*`. -/
theorem istc_bgp_optimal {α σ ρ δ Ax Ay h γx γy n : ℝ} {u : ℝ → ℝ} {a' c' : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ) (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h)
    (hgK : 0 < istcGK α γx γy n + δ) (h138 : istcBound α σ ρ n γx γy < 0)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (ha' : ∀ t, 0 ≤ t → 0 ≤ a' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hbud' : ∀ t, 0 ≤ t → HasDerivAt a' (Ax ^ α * (Ay * h) ^ (1 - α) *
      Real.exp ((1 - α) * istcGc α γx γy * t) * a' t ^ α - (δ + γx + n) * a' t - c' t) t)
    (h0 : a' 0 = istcKStar α σ ρ δ Ax Ay h γx γy / Ax) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u (istcCStar α σ ρ δ Ax Ay h γx γy n * Real.exp (istcGc α γx γy * t))) + ε := by
  obtain ⟨hks, hcs⟩ := istc_steady_pos hα0 hα1 hAx hAy hh hgK h138
  have hD : 0 < istcD α σ ρ δ γx γy := hgK.trans (istc_D_pos (δ := δ) hα1 h138)
  set ks := istcKStar α σ ρ δ Ax Ay h γx γy
  set cs := istcCStar α σ ρ δ Ax Ay h γx γy n
  set g := istcGc α γx γy
  set Θ := Ax ^ α * (Ay * h) ^ (1 - α)
  have hΘ : 0 < Θ := by positivity
  have hAh : 0 < Ay * h := by positivity
  set ab := ks / Ax
  have hab : 0 < ab := by positivity
  -- the two stationary equations in wealth units
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  have hΘa : Θ * ab ^ (α - 1) = Ax * (Ay * h / ks) ^ (1 - α) := by
    simp only [Θ, ab]
    rw [Real.div_rpow hks.le hAx.le, Real.div_rpow hAh.le hks.le, Real.rpow_sub_one hks.ne',
      Real.rpow_sub_one hAx.ne', show (1 - α) = -(α - 1) by ring, Real.rpow_neg hks.le,
      Real.rpow_neg hAh.le, Real.rpow_sub_one hks.ne', Real.rpow_sub_one hAh.ne']
    have : 0 < Ax ^ α := by positivity
    have : 0 < ks ^ α := by positivity
    have : 0 < (Ay * h) ^ α := by positivity
    field_simp
  have hcs_eq : cs = Θ * ab ^ α - (δ + istcGK α γx γy n) * ab := by
    have e : Θ * ab ^ α = ab * (Θ * ab ^ (α - 1)) := by
      rw [Real.rpow_sub_one hab.ne']; field_simp
    rw [e, hΘa]
    simp only [cs, istcCStar, ab]
    rw [istc_cd_eq hks hAh]
    field_simp
    ring
  have heul : (α * (Θ * ab ^ (α - 1)) - (δ + γx + n) + n - ρ) / σ = g := by
    rw [hΘa, hmpk, istc_D_eq]
    field_simp
    ring
  have hgK : istcGK α γx γy n = g + γx + n := istc_gK_eq _ _ _ _ hα1
  set a := fun t => ab * Real.exp (g * t)
  set c := fun t => cs * Real.exp (g * t)
  have hEg : ∀ t, Θ * Real.exp ((1 - α) * g * t) * a t ^ α =
      Real.exp (g * t) * (Θ * ab ^ α) := fun t => by
    simp only [a]
    rw [Real.mul_rpow hab.le (Real.exp_pos _).le, ← Real.exp_mul]
    have : Real.exp ((1 - α) * g * t) * Real.exp (g * t * α) = Real.exp (g * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  have hEg1 : ∀ t, Θ * Real.exp ((1 - α) * g * t) * a t ^ (α - 1) = Θ * ab ^ (α - 1) :=
    fun t => by
      simp only [a]
      rw [Real.mul_rpow hab.le (Real.exp_pos _).le, ← Real.exp_mul]
      have : Real.exp ((1 - α) * g * t) * Real.exp (g * t * (α - 1)) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      rw [show Θ * Real.exp ((1 - α) * g * t) * (ab ^ (α - 1) * Real.exp (g * t * (α - 1))) =
        Θ * ab ^ (α - 1) * (Real.exp ((1 - α) * g * t) * Real.exp (g * t * (α - 1))) by ring,
        this, mul_one]
  have hcont : ContinuousOn c (Set.Ici 0) := by
    simp only [c]; fun_prop
  refine istc_optimal (a := a) (c := c) hα0 hα1 hσ hΘ hconc hu (fun t _ => by positivity)
    (fun t _ => by positivity) hcont (fun t _ => ?_) (fun t _ => ?_) ?_ ha' hc' hcc' hbud' ?_
  · have hd := ((hasDerivAt_id' t).const_mul g).exp.const_mul ab
    convert hd using 1
    rw [hEg]
    simp only [a, c]
    rw [hcs_eq, hgK]
    ring
  · have hd := ((hasDerivAt_id' t).const_mul g).exp.const_mul cs
    convert hd using 1
    rw [mul_assoc α, hEg1, mul_div_assoc, heul]
    simp only [c]
    ring
  · have e : ∀ T, Real.exp (-(ρ - n) * T) * c T ^ (-σ) * a T =
        cs ^ (-σ) * ab * Real.exp (istcBound α σ ρ n γx γy * T) := fun T => by
      simp only [a, c]
      rw [Real.mul_rpow hcs.le (Real.exp_pos _).le, ← Real.exp_mul, istc_bound_eq]
      have : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -σ) * Real.exp (g * T) =
          Real.exp ((n - ρ + (1 - σ) * g) * T) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [← this]; ring
    simp only [e]
    exact (istc_exp_tendsto_zero_iff (by positivity)).mpr h138
  · rw [h0]
    simp [a]

/-- AKMM, p. 381: **the closed-form transition is optimal** (`σ = α`). Under (13.8) and
`φ > 0`, from any `K(0) = k̃_0 > 0` the path `k̃(t)` of `istc_closed_form_path` with
`c̃ = φk̃` — in wealth units `a(t) = k̃(t)e^{g_c t}/A_x`, `c(t) = φk̃(t)e^{g_c t}` — satisfies the
budget, the Euler equation and the TVC, so it is catching-up optimal for the planner's problem
(13.A.12) against every feasible path with `a ≥ 0`. -/
theorem istc_closed_form_optimal {α ρ δ Ax Ay h γx γy n k0 : ℝ} {u : ℝ → ℝ} {a' c' : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hk0 : 0 < k0)
    (hD : 0 < istcD α α ρ δ γx γy) (hφ : 0 < istcPhi α ρ δ Ax γx n)
    (h138 : istcBound α α ρ n γx γy < 0)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-α)) y)
    (ha' : ∀ t, 0 ≤ t → 0 ≤ a' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hbud' : ∀ t, 0 ≤ t → HasDerivAt a' (Ax ^ α * (Ay * h) ^ (1 - α) *
      Real.exp ((1 - α) * istcGc α γx γy * t) * a' t ^ α - (δ + γx + n) * a' t - c' t) t)
    (h0 : a' 0 = k0 / Ax) :
    let zs := istcKStar α α ρ δ Ax Ay h γx γy ^ (1 - α)
    let lam := (1 - α) * (istcD α α ρ δ γx γy / α)
    let k := fun s => (zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * s)) ^ (1 / (1 - α))
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u (istcPhi α ρ δ Ax γx n * k t * Real.exp (istcGc α γx γy * t))) + ε := by
  intro zs lam k
  have h1α : 0 < 1 - α := by linarith
  set φ := istcPhi α ρ δ Ax γx n
  set g := istcGc α γx γy
  set Θ := Ax ^ α * (Ay * h) ^ (1 - α)
  have hΘ : 0 < Θ := by positivity
  have hAh : 0 < Ay * h := by positivity
  have hpath := fun t (ht : 0 ≤ t) => istc_closed_form_path (n := n) (k0 := k0) (t := t)
    hα0 hα1 hAx hAy hh hk0 hD ht
  have hkpos : ∀ t, 0 ≤ t → 0 < k t := fun t ht => (hpath t ht).2.1
  have hkd : ∀ t, 0 ≤ t → HasDerivAt k (k t * (Ax * ((Ay * h / k t) ^ (1 - α) -
      φ * k t / k t) - δ - istcGK α γx γy n)) t := fun t ht => (hpath t ht).2.2
  set a := fun t => k t * Real.exp (g * t) / Ax
  set c := fun t => φ * k t * Real.exp (g * t)
  have hgK : istcGK α γx γy n = g + γx + n := istc_gK_eq _ _ _ _ hα1
  -- the two output identities in wealth units
  have hout : ∀ t, 0 ≤ t → Θ * Real.exp ((1 - α) * g * t) * a t ^ α =
      Real.exp (g * t) * (k t * (Ay * h / k t) ^ (1 - α)) := fun t ht => by
    have hk := hkpos t ht
    simp only [a]
    rw [Real.div_rpow (by positivity) hAx.le, Real.mul_rpow hk.le (Real.exp_pos _).le,
      ← Real.exp_mul, ← istc_cd_eq hk hAh]
    have : Real.exp ((1 - α) * g * t) * Real.exp (g * t * α) = Real.exp (g * t) := by
      rw [← Real.exp_add]; ring_nf
    have hAxa : 0 < Ax ^ α := by positivity
    simp only [Θ]
    field_simp
    rw [← this]
    ring
  have hmpk : ∀ t, 0 ≤ t → Θ * Real.exp ((1 - α) * g * t) * a t ^ (α - 1) =
      Ax * (Ay * h / k t) ^ (1 - α) := fun t ht => by
    have hk := hkpos t ht
    have ha : 0 < a t := by simp only [a]; positivity
    have e := hout t ht
    rw [Real.rpow_sub_one ha.ne', ← mul_div_assoc, e]
    simp only [a]
    field_simp
  have hcd : ∀ t, 0 ≤ t → HasDerivAt c (c t * ((α * (Θ * Real.exp ((1 - α) * g * t)) *
      a t ^ (α - 1) - (δ + γx + n) + n) - ρ) / α) t := fun t ht => by
    have hk := hkpos t ht
    have h1 := ((hkd t ht).const_mul φ).fun_mul ((hasDerivAt_id' t).const_mul g).exp
    have hrhs := istc_closed_form_rhs (Ay := Ay) (h := h) (γy := γy) (ρ := ρ) (δ := δ)
      (γx := γx) (n := n) hα0 hα1 hAx hk
    simp only [c]
    convert h1 using 1
    rw [mul_assoc α, hmpk t ht]
    rw [hrhs]
    field_simp
    ring
  have hbud : ∀ t, 0 ≤ t → HasDerivAt a (Θ * Real.exp ((1 - α) * g * t) * a t ^ α -
      (δ + γx + n) * a t - c t) t := fun t ht => by
    have hk := hkpos t ht
    have h1 := ((hkd t ht).fun_mul ((hasDerivAt_id' t).const_mul g).exp).div_const Ax
    convert h1 using 1
    rw [hout t ht, hgK]
    simp only [a, c]
    field_simp
    ring
  have hcont : ContinuousOn c (Set.Ici 0) := fun t ht =>
    (hcd t ht).continuousAt.continuousWithinAt
  have hzs : 0 < zs := by
    have : 0 < istcKStar α α ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
    positivity
  have hpow : ∀ t, 0 ≤ t → k t ^ (1 - α) = zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * t) :=
    fun t ht => by
      have hu' : 0 < zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * t) := by
        have hlam : 0 < lam := by positivity
        have hE : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have hE0 := Real.exp_pos (-lam * t)
        have hk0p : 0 < k0 ^ (1 - α) := by positivity
        nlinarith
      simp only [k]
      rw [← Real.rpow_mul hu'.le, one_div_mul_cancel h1α.ne', Real.rpow_one]
  have htvc : Tendsto (fun T => Real.exp (-(ρ - n) * T) * c T ^ (-α) * a T) atTop (𝓝 0) := by
    have hlam : 0 < lam := by positivity
    have hU : Tendsto (fun T => zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * T)) atTop
        (𝓝 zs) := by
      have hE := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hlam)
      have := (hE.const_mul (k0 ^ (1 - α) - zs)).const_add zs
      simp only [mul_zero, add_zero] at this
      refine this.congr fun T => ?_
      simp [neg_mul]
    have hX := (istc_exp_tendsto_zero_iff (C := 1) one_pos).mpr h138
    have hprod := (hU.mul hX).const_mul (φ ^ (-α) / Ax)
    rw [mul_zero, mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hk := hkpos T hT
    simp only [a, c]
    rw [← hpow T hT, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.mul_rpow hφ.le hk.le, ← Real.exp_mul, Real.rpow_sub hk, Real.rpow_one, istc_bound_eq]
    have : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -α) * Real.exp (g * T) =
        Real.exp ((n - ρ + (1 - α) * g) * T) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [← this]
    have : 0 < k T ^ α := by positivity
    field_simp
    rw [Real.rpow_neg hk.le]
    field_simp
  have h := istc_optimal (a := a) (c := c) hα0 hα1 hα0 hΘ hconc hu (fun t ht => by
    have := hkpos t ht; simp only [a]; positivity) (fun t ht => by
    have := hkpos t ht; simp only [c]; positivity) hcont hbud hcd htvc ha' hc' hcc' hbud'
    (by
      have hk00 : k 0 = k0 := (hpath 0 le_rfl).1
      rw [h0]; simp only [a]; rw [hk00]; simp)
  exact h

end AKMM.Growth
