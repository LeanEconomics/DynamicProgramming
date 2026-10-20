/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.IndustryInvestmentResults

/-!
# Industry investment under uncertainty: first-order conditions

SLP §10.4, Exercise 10.4d–f, pp. 295–296. Let `v` be the fixed point of (2′)
(`IndustryInvestmentResults`), `g` its policy, `β = 1/(1 + r)` and
`W_z(y) = ∫ v(y, z′) Q(z, dz′)` (`indW`). The extra hypotheses, stated where used, are:
`U(·, z)` differentiable on `(0, ∞)` (`U_x = D`) and `c` differentiable on `(0, ∞)` (the book's
`c ∈ C¹`); strict convexity of `c` on `[1 − δ, ∞)` and strict concavity of `U(·, z)` are already
in `IndHyp`, and the optimum is interior (`ind_policy`, `ind_rhs_le`).

* `indW_strictConcaveOn`, `indW_strictMonoOn`, `indW_hasDerivAt`: `W_z` is strictly concave,
  strictly increasing and differentiable, `W_z′(y) = ∫ v_x(y, z′) Q(z, dz′)` (differentiation
  under the integral sign).
* `ind_foc`: the first-order condition `c′(g(x, z)/x) = β W_z′(g(x, z))`.
* `ind_policy_gt`: gross investment is always strictly positive, `g(x, z) > (1 − δ)x`, as soon as
  `c` is differentiable at `1 − δ`.
* **Exercise 10.4d** (`ind_policy_strictMono_x`, `ind_policy_ratio_lt`, `ind_policy_slope_lt`):
  `g(·, z)` is strictly increasing, `g(x, z)/x` is strictly decreasing, and
  `g(x′, z) − g(x, z) < [g(x, z)/x](x′ − x)` for `x < x′`, so the slope is below one wherever
  `g(x, z) ≤ x`.
* **Exercise 10.4e** (`ind_v_incDiff`, `ex_10_4e`): for `Q` monotone and `U` with increasing
  differences in `(x, z)` (`D` increasing in `z`), `v` has increasing differences in `(x, z)`
  (a closed property preserved by `T̃`, by Topkis's argument), and so `g(x, ·)` is nondecreasing.
  `ex_10_4e_strict`: strict increase where `W_z′(g) < W_ẑ′(g)`.
* **Exercise 10.4f** (`ex_10_4f_stationary`): under i.i.d. shocks every optimal path converges to
  the same `x̂ ≥ 0`, whatever `x₀` and the shock path (`ex_10_4f_limit_eq`); if `x̂ > 0` it is
  the unique positive stationary point (`ind_limit_stationary`, `ind_stationary_unique`); and
  `x̂ > 0` if `U_x(y₀, z) > (1 + r)c′(1)` for all `z` at some `y₀ > 0` (`ind_policy_gt_self`,
  `ex_10_4f_limit_pos`), the manual's condition `(1 + r)c′(1) < D(0, z)` moved off `0`.

## Corrections

* **Exercise 10.4d, p. 295.** "`g(·, z)` has slope strictly less than one" is false
  (`ex_10_4d_slope_counterexample`): with `U(q, z) = 10zq/(1 + q)`,
  `c(a) = max{a − ½, 0}²`, `δ = ½`, `δ′ = ¾`, `r = 1`, `M = 200`, `Z = [1, 2]` (`ind0_hyp`) and
  any Feller `Q`, `g(x, z) > x` on `(0, ½]` but `g(x, z) − x → 0` as `x → 0`. The manual itself
  notes that slope below one does not give `g/x` decreasing; what holds is
  `ind_policy_slope_lt`.
* **Exercise 10.4e, p. 295; manual p. 179.** The manual's step "`D` increasing in `z` implies
  `v_x` increasing in `z`" ignores that `g(x, z)` depends on `z`; it is replaced by the Topkis
  argument above. The strict claim ("strictly increasing where gross investment is positive") is
  false (`ex_10_4e_strict_counterexample`): with i.i.d. shocks (`indQ0`, monotone and Feller)
  `g` does not depend on `z`, while gross investment is always positive (`ind_policy_gt`).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction Metric

variable {U : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {δ δ' M r A z₁ z₂ : ℝ}

/-- The expected continuation value `W_z(t) = ∫ v(t, z′) Q(z, dz′)`, extended by `0` to
`t ≤ 0`. -/
noncomputable def indW (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ)
    (z : Icc z₁ z₂) (t : ℝ) : ℝ :=
  ∫ z', liftS (fun u => v (u, z')) t ∂Q z

/-- At `t > 0` the lifted section of `v` is `v(t, ·)`. -/
theorem ind_liftS_of_pos (v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    (fun z' : Icc z₁ z₂ => liftS (fun u => v (u, z')) t) = fun z' => v (⟨t, ht⟩, z') := by
  funext z'
  exact liftS_of_mem _ ht

/-- `W_z(t) = ∫ v(t, z′) Q(z, dz′)` for `t > 0`. -/
theorem indW_of_pos (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ)
    (z : Icc z₁ z₂) {t : ℝ} (ht : 0 < t) : indW Q v z t = ∫ z', v (⟨t, ht⟩, z') ∂Q z := by
  unfold indW
  rw [ind_liftS_of_pos v ht]

/-- The right side of (2) in terms of `W`. -/
theorem ind_rhs_W (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) (v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ)
    (x : Ioi (0 : ℝ)) (z : Icc z₁ z₂) (w : Ioi (0 : ℝ)) :
    rhs (indModel Q U c δ' M r) v (x, z) w =
      U x.1 z.1 - x.1 * c (w.1 / x.1) + 1 / (1 + r) * indW Q v z w.1 := by
  rw [ind_rhs, indW_of_pos Q v z w.2]
  rfl

/-- At the fixed point, no `y > 0` beats the value. -/
theorem ind_rhs_le_v (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (s : Ioi (0 : ℝ) × Icc z₁ z₂) (w : Ioi (0 : ℝ)) :
    rhs (indModel Q U c δ' M r) v s w ≤ v s := by
  have hvm := (ind_strictMono_x h Q hQ hv).2
  have := ind_rhs_le h Q hQ (ind_strictMono_x h Q hQ hv).1 (fun z => (hvm z).monotone) s w
  rwa [hv] at this

/-- `W_z` is strictly increasing on `(0, ∞)`. -/
theorem indW_strictMonoOn (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) (z : Icc z₁ z₂) :
    StrictMonoOn (indW Q v z) (Ioi 0) := by
  intro a ha b hb hab
  rw [indW_of_pos Q v z ha, indW_of_pos Q v z hb]
  exact integral_lt_integral_of_lt (integrable_ind (Q := Q) v _ z)
    (integrable_ind (Q := Q) v _ z) fun z' =>
      (ind_strictMono_x h Q hQ hv).2 z' (show (⟨a, ha⟩ : Ioi (0 : ℝ)) < ⟨b, hb⟩ from hab)

/-- `W_z` is strictly concave on `(0, ∞)`. -/
theorem indW_strictConcaveOn (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) (z : Icc z₁ z₂) :
    StrictConcaveOn ℝ (Ioi 0) (indW Q v z) := by
  refine ⟨convex_Ioi 0, fun a ha b hb hne θ η hθ hη hθη => ?_⟩
  obtain rfl : η = 1 - θ := by linarith
  have hθ1 : θ < 1 := by linarith
  have hm : (0 : ℝ) < θ • a + (1 - θ) • b := (convex_Ioi (0 : ℝ)) ha hb hθ.le hη.le hθη
  simp only [smul_eq_mul] at hm ⊢
  rw [indW_of_pos Q v z ha, indW_of_pos Q v z hb, indW_of_pos Q v z hm,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_ind (Q := Q) v _ z).const_mul _)
      ((integrable_ind (Q := Q) v _ z).const_mul _)]
  refine integral_lt_integral_of_lt (((integrable_ind (Q := Q) v _ z).const_mul _).add
    ((integrable_ind (Q := Q) v _ z).const_mul _)) (integrable_ind (Q := Q) v _ z) fun z' => ?_
  have := ind_strictConcave h Q hQ hv z' ⟨a, ha⟩ ⟨b, hb⟩
    (fun he => hne (congrArg Subtype.val he)) θ hθ hθ1
  convert this using 2
  exact Prod.ext (Subtype.ext (by simp [cmb])) rfl

/-- Fermat's rule for `c`: `c′(a) = 0` for `0 < a ≤ 1 − δ`, where `c` attains its minimum `0`. -/
theorem ind_c_deriv_eq_zero (h : IndHyp U c δ δ' M r A z₁ z₂) {a c' : ℝ} (ha : 0 < a)
    (ha' : a ≤ 1 - δ) (hc : HasDerivAt c c' a) : c' = 0 := by
  have hmin : IsLocalMin c a := by
    filter_upwards [Ioi_mem_nhds ha] with t ht
    rw [h.c_zero a ha.le ha']
    exact h.c_nonneg (le_of_lt ht)
  exact hmin.hasDerivAt_eq_zero hc

/-- `c′` is nondecreasing on `(0, ∞)`. -/
theorem ind_c_deriv_mono (h : IndHyp U c δ δ' M r A z₁ z₂) {a b ca cb : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hca : HasDerivAt c ca a) (hcb : HasDerivAt c cb b) : ca ≤ cb := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact (hca.unique hcb).le
  · exact (h.c_conv.le_slope_of_hasDerivAt (mem_Ici.2 ha.le) (mem_Ici.2 (ha.le.trans hlt.le))
      hlt hca).trans (h.c_conv.slope_le_of_hasDerivAt (mem_Ici.2 ha.le)
      (mem_Ici.2 (ha.le.trans hlt.le)) hlt hcb)

/-- `c′` is strictly increasing on `[1 − δ, ∞)`. -/
theorem ind_c_deriv_strict (h : IndHyp U c δ δ' M r A z₁ z₂) {a b ca cb : ℝ} (ha : 1 - δ ≤ a)
    (hab : a < b) (hca : HasDerivAt c ca a) (hcb : HasDerivAt c cb b) : ca < cb :=
  (h.c_sconv.lt_slope_of_hasDerivAt (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab hca).trans_le
    (h.c_sconv.convexOn.slope_le_of_hasDerivAt (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab
      hcb)

/-- The tangent line of `c` at `a > 0` passes below `c(0) = 0`: `c(a) ≤ a c′(a)`. So the term
`a c′(a) − c(a)` of `v_x` (10.4c) is nonnegative. -/
theorem ind_c_le_mul_deriv (h : IndHyp U c δ δ' M r A z₁ z₂) {a ca : ℝ} (ha : 0 < a)
    (hca : HasDerivAt c ca a) : c a ≤ a * ca := by
  have hz : c 0 = 0 := h.c_zero 0 le_rfl h.one_sub_δ_nonneg
  have := h.c_conv.slope_le_of_hasDerivAt (mem_Ici.2 le_rfl) (mem_Ici.2 ha.le) ha hca
  rw [slope_def_field, hz, sub_zero, sub_zero, div_le_iff₀ ha] at this
  linarith


/-- **The first-order condition** (manual, Exercise 10.4d). If `y` is optimal at `(x, z)`, `c` has
derivative `c′` at `y/x` and `W_z` has derivative `w` at `y`, then `c′(y/x) = (1 + r)⁻¹ w`. The
optimum is interior: `y` maximizes the right side of (2) over all of `(0, ∞)`. -/
theorem ind_foc (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) {x y : Ioi (0 : ℝ)} {z : Icc z₁ z₂}
    (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z)) {c' w : ℝ}
    (hc : HasDerivAt c c' (y.1 / x.1)) (hW : HasDerivAt (indW Q v z) w y.1) :
    c' = 1 / (1 + r) * w := by
  have hx : 0 < x.1 := x.2
  set φ : ℝ → ℝ := fun t => U x.1 z.1 - x.1 * c (t / x.1) + 1 / (1 + r) * indW Q v z t
  have hdiv : HasDerivAt (fun t => t / x.1) (1 / x.1) y.1 := (hasDerivAt_id y.1).div_const x.1
  have hφ : HasDerivAt φ (-(x.1 * (c' * (1 / x.1))) + 1 / (1 + r) * w) y.1 :=
    ((((hc.comp y.1 hdiv).const_mul x.1).const_sub (U x.1 z.1)).add
      (hW.const_mul (1 / (1 + r))))
  have hmax : IsLocalMax φ y.1 := by
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    have h1 := ind_rhs_le_v h Q hQ hv (x, z) ⟨t, ht⟩
    rw [ind_rhs_W, hy.2, ind_rhs_W] at h1
    exact h1
  have h0 := hmax.hasDerivAt_eq_zero hφ
  have e : x.1 * (c' * (1 / x.1)) = c' := by field_simp
  linarith

/-- **Gross investment is strictly positive**: `g(x, z) > (1 − δ)x` whenever `c` is
differentiable at `1 − δ` (so `c′(1 − δ) = 0`). Raising `y` above `(1 − δ)x` by `ε` costs `o(ε)`
but raises `W_z` by at least `ε [W_z(y + 1) − W_z(y)] > 0`, by concavity. In particular the
qualifier "where gross investment is strictly positive" of Exercise 10.4e is always met. -/
theorem ind_policy_gt (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (hc0 : DifferentiableAt ℝ c (1 - δ))
    {x y : Ioi (0 : ℝ)} {z : Icc z₁ z₂} (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z)) :
    (1 - δ) * x.1 < y.1 := by
  have hx : 0 < x.1 := x.2
  have hy0 : 0 < y.1 := y.2
  have hlow := ((ind_policy h Q hQ hv).2.2 _ y hy).1
  by_contra hle
  push Not at hle
  have hyx : y.1 = (1 - δ) * x.1 := le_antisymm hle hlow
  have hd : HasDerivAt c 0 (1 - δ) := by
    have := hc0.hasDerivAt
    rwa [ind_c_deriv_eq_zero h h.one_sub_δ_pos le_rfl this] at this
  have hc1 : c (1 - δ) = 0 := h.c_zero _ h.one_sub_δ_nonneg le_rfl
  set W := indW Q v z with hWdef
  have hβ : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  set κ := W (y.1 + 1) - W y.1 with hκdef
  have hκ : 0 < κ := sub_pos.2 (indW_strictMonoOn h Q hQ hv z hy0
    (show 0 < y.1 + 1 by linarith) (by linarith))
  -- `c(1 − δ + s) ≤ (βκ/2)|s|` for small `s`
  have hη : 0 < 1 / (1 + r) * κ / 2 := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hasDerivAt_iff_isLittleO.1 hd).def hη)
  set ε := min 1 (ρ * x.1 / 2) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ ρ * x.1 / 2 := min_le_right _ _
  have hdist : dist (1 - δ + ε / x.1) (1 - δ) < ρ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (div_pos hε0 hx), div_lt_iff₀ hx]
    nlinarith
  have hcε := hball hdist
  rw [hc1, smul_zero, sub_zero, sub_zero, add_sub_cancel_left, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (div_pos hε0 hx)] at hcε
  have hcε' : c (1 - δ + ε / x.1) ≤ 1 / (1 + r) * κ / 2 * (ε / x.1) := (le_abs_self _).trans hcε
  -- concavity: `W(y + ε) ≥ W(y) + εκ`
  have hWc : W y.1 + ε * κ ≤ W (y.1 + ε) := by
    have := (indW_strictConcaveOn h Q hQ hv z).concaveOn.2 (show (0 : ℝ) < y.1 from hy0)
      (show (0 : ℝ) < y.1 + 1 by linarith) (by linarith : (0 : ℝ) ≤ 1 - ε) hε0.le (by ring)
    simp only [smul_eq_mul] at this
    rw [show (1 - ε) * y.1 + ε * (y.1 + 1) = y.1 + ε by ring] at this
    rw [hκdef]
    linarith
  -- the deviation to `y + ε` beats `y`
  have hdev := ind_rhs_le_v h Q hQ hv (x, z) ⟨y.1 + ε, mem_Ioi.2 (by linarith)⟩
  rw [ind_rhs_W, hy.2, ind_rhs_W] at hdev
  simp only at hdev
  rw [show (y.1 + ε) / x.1 = 1 - δ + ε / x.1 by rw [hyx]; field_simp,
    show y.1 / x.1 = 1 - δ by rw [hyx]; field_simp, hc1] at hdev
  have hcost : x.1 * c (1 - δ + ε / x.1) ≤ 1 / (1 + r) * κ / 2 * ε := by
    have := mul_le_mul_of_nonneg_left hcε' hx.le
    rwa [show x.1 * (1 / (1 + r) * κ / 2 * (ε / x.1)) = 1 / (1 + r) * κ / 2 * ε by
      field_simp] at this
  have hgain := mul_le_mul_of_nonneg_left hWc hβ.le
  nlinarith [mul_pos hβ (mul_pos hε0 hκ)]

/-- **Differentiating `W_z`.** If `U(·, z′)` is differentiable on `(0, ∞)` for every `z′` and `c`
is differentiable on `(0, ∞)`, then each `v(·, z′)` is differentiable (Exercise 10.4c,
`ind_hasDerivAt_x`), with derivative `D(z′)` at `y`, and `W_z′(y) = ∫ D(z′) Q(z, dz′)`. The
integral is differentiated under the integral sign: on `(y/2, 3y/2)` each `v(·, z′)` is concave
and bounded by `‖v‖`, hence Lipschitz with a common constant. -/
theorem indW_hasDerivAt (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) (z : Icc z₁ z₂) {y : ℝ} (hy : 0 < y) :
    ∃ D : Icc z₁ z₂ → ℝ, (∀ z', HasDerivAt (liftS fun u => v (u, z')) (D z') y) ∧
      Integrable D (Q z) ∧ HasDerivAt (indW Q v z) (∫ z', D z' ∂Q z) y := by
  have hdiff : ∀ z' : Icc z₁ z₂, DifferentiableAt ℝ (liftS fun u => v (u, z')) y := by
    intro z'
    obtain ⟨⟨y', hy', hval⟩, -, -⟩ := ind_max h Q hQ hv (⟨y, hy⟩, z')
    exact (ind_hasDerivAt_x h Q hQ hv (x₀ := ⟨y, hy⟩) ⟨hy', hval⟩ (hUd z' y hy).hasDerivAt
      (hcd _ (div_pos y'.2 hy)).hasDerivAt).differentiableAt
  set D : Icc z₁ z₂ → ℝ := fun z' => deriv (liftS fun u => v (u, z')) y with hDdef
  have hD : ∀ z', HasDerivAt (liftS fun u => v (u, z')) (D z') y :=
    fun z' => (hdiff z').hasDerivAt
  -- `D` is measurable: a pointwise limit of continuous difference quotients
  have hpos : ∀ n : ℕ, y + 1 / ((n : ℝ) + 1) ∈ Ioi (0 : ℝ) := fun n =>
    mem_Ioi.2 (by positivity)
  have hDm : Measurable D := by
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (z' : Icc z₁ z₂) =>
      (1 / ((n : ℝ) + 1))⁻¹ • (liftS (fun u => v (u, z')) (y + 1 / ((n : ℝ) + 1)) -
        liftS (fun u => v (u, z')) y)) (fun n => ?_) (tendsto_pi_nhds.2 fun z' => ?_)
    · have e : (fun z' : Icc z₁ z₂ => (1 / ((n : ℝ) + 1))⁻¹ • (liftS (fun u => v (u, z'))
          (y + 1 / ((n : ℝ) + 1)) - liftS (fun u => v (u, z')) y)) = fun z' =>
          (1 / ((n : ℝ) + 1))⁻¹ • (v (⟨_, hpos n⟩, z') - v (⟨y, hy⟩, z')) := by
        funext z'
        rw [liftS_of_mem _ (hpos n), liftS_of_mem _ (mem_Ioi.2 hy)]
      have hc1 : Continuous fun z' : Icc z₁ z₂ => v (⟨_, hpos n⟩, z') :=
        v.continuous.comp (Continuous.prodMk_right _)
      have hc2 : Continuous fun z' : Icc z₁ z₂ => v (⟨y, hy⟩, z') :=
        v.continuous.comp (Continuous.prodMk_right _)
      rw [e]
      exact ((hc1.sub hc2).const_smul (1 / ((n : ℝ) + 1))⁻¹).measurable
    · have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
      exact (hD z').tendsto_slope_zero_right.comp hseq
  -- dominated differentiation, as in Exercise 10.6c
  set F : ℝ → Icc z₁ z₂ → ℝ := fun t z' => liftS (fun u => v (u, z')) t with hFdef
  have hsub : ball y y ⊆ Ioi 0 := fun t ht => by
    rw [mem_ball, Real.dist_eq] at ht
    exact mem_Ioi.2 (by linarith [neg_abs_le (t - y)])
  have hconc : ∀ z', ConcaveOn ℝ (ball y y) (F · z') := fun z' =>
    (concaveOn_liftS (ind_strictConcave h Q hQ hv z').isConcaveS).subset hsub (convex_ball y y)
  have hbd : ∀ z' t, dist t y < y → |F t z'| ≤ ‖v‖ := fun z' t ht => by
    have htp : t ∈ Ioi (0 : ℝ) := hsub (mem_ball.2 ht)
    simp only [F]
    rw [liftS_of_mem _ htp, ← Real.norm_eq_abs]
    exact v.norm_coe_le_norm _
  have hy2 : (0 : ℝ) < y / 2 := by positivity
  have hlip : ∀ z', LipschitzOnWith (Real.nnabs (2 * ‖v‖ / (y / 2))) (F · z')
      (ball y (y - y / 2)) := fun z' => by
    rw [Real.nnabs_of_nonneg (by positivity)]
    exact (hconc z').lipschitzOnWith_of_abs_le hy2 fun a ha => hbd z' a ha
  have hball : ball y (y - y / 2) ∈ 𝓝 y := ball_mem_nhds y (by linarith)
  have hmeas : ∀ t ∈ ball y y, AEStronglyMeasurable (F t) (Q z) := by
    intro t ht
    have htp : 0 < t := hsub ht
    have : F t = fun z' => v (⟨t, htp⟩, z') := ind_liftS_of_pos v htp
    rw [this]
    exact (v.continuous.comp (Continuous.prodMk_right _)).aestronglyMeasurable
  have hFy : F y = fun z' => v (⟨y, hy⟩, z') := ind_liftS_of_pos v hy
  obtain ⟨hint, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip (μ := Q z)
    (F := F) (F' := D) (bound := fun _ => 2 * ‖v‖ / (y / 2)) hball
    (eventually_of_mem (ball_mem_nhds y hy) hmeas)
    (by rw [hFy]; exact integrable_ind (Q := Q) v _ z)
    hDm.aestronglyMeasurable (Eventually.of_forall hlip) (integrable_const _)
    (Eventually.of_forall hD)
  exact ⟨D, hD, hint, hderiv⟩

/-- `W_z′` is strictly decreasing: `W_z` is strictly concave. -/
theorem indW_deriv_lt (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v) (z : Icc z₁ z₂) {y y' w w' : ℝ} (hy : 0 < y)
    (hyy : y < y') (hw : HasDerivAt (indW Q v z) w y) (hw' : HasDerivAt (indW Q v z) w' y') :
    w' < w :=
  ((indW_strictConcaveOn h Q hQ hv z).lt_slope_of_hasDerivAt (mem_Ioi.2 hy)
    (mem_Ioi.2 (hy.trans hyy)) hyy hw').trans
    ((indW_strictConcaveOn h Q hQ hv z).slope_lt_of_hasDerivAt (mem_Ioi.2 hy)
      (mem_Ioi.2 (hy.trans hyy)) hyy hw)

/-- **Exercise 10.4d** (strict monotonicity in `x`). With `U(·, z)` and `c` differentiable on
`(0, ∞)`, `x < x′` implies `g(x, z) < g(x′, z)`. If `g(x, z) = g(x′, z) = y`, the first-order
conditions give `c′(y/x) = (1 + r)⁻¹ W_z′(y) = c′(y/x′)`; but `y/x′ < y/x`, and
`y/x′ > 1 − δ` (`ind_policy_gt`), where `c′` is strictly increasing. -/
theorem ind_policy_strictMono_x (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {x x' y y' : Ioi (0 : ℝ)}
    (hxx : x.1 < x'.1) (z : Icc z₁ z₂) (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hy' : y' ∈ policy (indModel Q U c δ' M r) v (x', z)) : y.1 < y'.1 := by
  rcases (ex_10_4d h Q hQ hv hxx.le z hy hy').lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hx : 0 < x.1 := x.2
  have hy0 : 0 < y.1 := y.2
  obtain ⟨D, -, -, hW⟩ := indW_hasDerivAt h Q hQ hv hUd hcd z hy0
  have hc := (hcd _ (div_pos hy0 hx)).hasDerivAt
  have hc' := (hcd _ (div_pos y'.2 x'.2)).hasDerivAt
  have e1 := ind_foc h Q hQ hv hy hc hW
  have hW' : HasDerivAt (indW Q v z) (∫ z', D z' ∂Q z) y'.1 := by rw [← heq]; exact hW
  have e2 := ind_foc h Q hQ hv hy' hc' hW'
  have hgt := ind_policy_gt h Q hQ hv (hcd _ h.one_sub_δ_pos) hy'
  have h1 : 1 - δ ≤ y'.1 / x'.1 := by rw [le_div_iff₀ x'.2]; linarith
  have h2 : y'.1 / x'.1 < y.1 / x.1 := by rw [← heq]; exact div_lt_div_of_pos_left hy0 hx hxx
  have := ind_c_deriv_strict h h1 h2 hc' hc
  linarith

/-- **Exercise 10.4d** (the growth rate). With `U(·, z)` and `c` differentiable on `(0, ∞)`,
`g(x, z)/x` is strictly decreasing in `x`. If `x < x′` and `g(x′, z)/x′ ≥ g(x, z)/x`, then
`c′(g(x′, z)/x′) ≥ c′(g(x, z)/x)`, while `g(x′, z) > g(x, z)` and `W_z′` is strictly
decreasing, so the first-order conditions give the reverse strict inequality. -/
theorem ind_policy_ratio_lt (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {x x' y y' : Ioi (0 : ℝ)}
    (hxx : x.1 < x'.1) (z : Icc z₁ z₂) (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hy' : y' ∈ policy (indModel Q U c δ' M r) v (x', z)) : y'.1 / x'.1 < y.1 / x.1 := by
  by_contra hge
  push Not at hge
  have hlt := ind_policy_strictMono_x h Q hQ hv hUd hcd hxx z hy hy'
  obtain ⟨D, -, -, hW⟩ := indW_hasDerivAt h Q hQ hv hUd hcd z y.2
  obtain ⟨D', -, -, hW'⟩ := indW_hasDerivAt h Q hQ hv hUd hcd z y'.2
  have hc := (hcd _ (div_pos y.2 x.2)).hasDerivAt
  have hc' := (hcd _ (div_pos y'.2 x'.2)).hasDerivAt
  have e1 := ind_foc h Q hQ hv hy hc hW
  have e2 := ind_foc h Q hQ hv hy' hc' hW'
  have hmono := ind_c_deriv_mono h (div_pos y.2 x.2) hge hc hc'
  have hanti := indW_deriv_lt h Q hQ hv z y.2 hlt hW hW'
  have hβ : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  nlinarith [mul_lt_mul_of_pos_left hanti hβ]

/-- The growth rate is nonincreasing: `x ≤ x′` implies `g(x′, z)/x′ ≤ g(x, z)/x`. -/
theorem ind_policy_ratio_le (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {x x' y y' : Ioi (0 : ℝ)}
    (hxx : x.1 ≤ x'.1) (z : Icc z₁ z₂) (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hy' : y' ∈ policy (indModel Q U c δ' M r) v (x', z)) : y'.1 / x'.1 ≤ y.1 / x.1 := by
  rcases hxx.lt_or_eq with hlt | heq
  · exact (ind_policy_ratio_lt h Q hQ hv hUd hcd hlt z hy hy').le
  · have hx : x = x' := Subtype.ext heq
    subst hx
    have hpol := (ind_policy h Q hQ hv).2.1
    rw [(ind_policy h Q hQ hv).1.unique (x, z) y (hpol (x, z) ▸ hy) y' (hpol (x, z) ▸ hy')]

/-- **Exercise 10.4d** (the slope). For `x < x′`,
`g(x′, z) − g(x, z) < [g(x, z)/x](x′ − x)`: the slope of `g(·, z)` is below the growth rate.
In particular the slope is below one wherever `g(x, z) ≤ x`. That the slope is below one
everywhere is false (`ex_10_4d_slope_counterexample`). -/
theorem ind_policy_slope_lt (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {x x' y y' : Ioi (0 : ℝ)}
    (hxx : x.1 < x'.1) (z : Icc z₁ z₂) (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hy' : y' ∈ policy (indModel Q U c δ' M r) v (x', z)) :
    y'.1 - y.1 < y.1 / x.1 * (x'.1 - x.1) := by
  have hr := ind_policy_ratio_lt h Q hQ hv hUd hcd hxx z hy hy'
  have hx : 0 < x.1 := x.2
  have hx' : 0 < x'.1 := x'.2
  rw [div_lt_iff₀ hx'] at hr
  have e : y.1 / x.1 * (x'.1 - x.1) = y.1 / x.1 * x'.1 - y.1 := by field_simp
  rw [e]
  linarith

/-! ### Exercise 10.4e: monotonicity in the demand shock -/

/-- `f` has increasing differences in `(x, z)`: `f(x′, z) − f(x, z) ≤ f(x′, ẑ) − f(x, ẑ)` for
`x ≤ x′` and `z ≤ ẑ`. -/
def IndIncDiff (f : Ioi (0 : ℝ) × Icc z₁ z₂ → ℝ) : Prop :=
  ∀ (x x' : Ioi (0 : ℝ)) (z zh : Icc z₁ z₂), x.1 ≤ x'.1 → z.1 ≤ zh.1 →
    f (x', z) - f (x, z) ≤ f (x', zh) - f (x, zh)

/-- Increasing differences is a closed condition. -/
theorem isClosed_indIncDiff :
    IsClosed {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ | IndIncDiff (z₁ := z₁) (z₂ := z₂) f} := by
  simp only [IndIncDiff, ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_iInter fun z =>
    isClosed_iInter fun zh => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le ((continuous_eval_const _).sub (continuous_eval_const _))
        ((continuous_eval_const _).sub (continuous_eval_const _))

/-- With `Q` monotone, the expected value `∫ f(y, z′) Q(z, dz′)` of a function with increasing
differences has increasing differences in `(y, z)`. -/
theorem ind_E_incDiff (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q]
    (hQm : IsMonotoneTF Q) {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hf : IndIncDiff f)
    {y y' : Ioi (0 : ℝ)} (hyy : y.1 ≤ y'.1) {z zh : Icc z₁ z₂} (hzz : z ≤ zh) :
    ∫ z', f (y', z') ∂Q z - ∫ z', f (y, z') ∂Q z ≤
      ∫ z', f (y', z') ∂Q zh - ∫ z', f (y, z') ∂Q zh := by
  rw [← integral_sub (integrable_ind (Q := Q) f y' z) (integrable_ind (Q := Q) f y z),
    ← integral_sub (integrable_ind (Q := Q) f y' zh) (integrable_ind (Q := Q) f y zh)]
  have hm : Measurable fun z' : Icc z₁ z₂ => f (y', z') - f (y, z') :=
    ((f.continuous.comp (Continuous.prodMk_right y')).sub
      (f.continuous.comp (Continuous.prodMk_right y))).measurable
  refine hQm (fun z' => f (y', z') - f (y, z')) hm ⟨2 * ‖f‖, fun z' => ?_⟩
    (fun a b hab => ?_) hzz
  · have h1 := f.norm_coe_le_norm (y', z')
    have h2 := f.norm_coe_le_norm (y, z')
    rw [Real.norm_eq_abs] at h1 h2
    exact (abs_sub _ _).trans (by linarith)
  · have := hf y y' a b hyy hab
    simp only
    linarith

/-- `T̃` preserves increasing differences in `(x, z)` (Topkis). Let `y₁` be optimal at
`(x′, z)` and `y₂` at `(x, ẑ)`. If `y₁ ≤ y₂`, use `y₂` at `(x′, ẑ)` and `y₁` at `(x, z)`: the
cost `x c(y/x)` has decreasing differences in `(x, y)`. If `y₂ < y₁`, use `y₁` at `(x′, ẑ)` and
`y₂` at `(x, z)`: the continuation value has increasing differences in `(y, z)`. In both cases
`U` has increasing differences in `(x, z)`. -/
theorem ind_T_incDiff (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) (hQm : IsMonotoneTF Q)
    (hUid : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → z₁ ≤ z → z ≤ zh → zh ≤ z₂ →
      U x' z - U x z ≤ U x' zh - U x zh)
    {f : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hfR : ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r)))
    (hfm : ∀ z, Monotone fun x => f (x, z)) (hf : IndIncDiff f) :
    IndIncDiff (truncT (h.upperDP Q hQ) f) := by
  intro x x' z zh hxx hzz
  have hd := h.upperDP Q hQ
  have hx : 0 < x.1 := x.2
  have hβ : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  obtain ⟨y₁, -, hv₁, -⟩ := trunc_bellman_argmax hd hfR (x', z)
  obtain ⟨y₂, -, hv₂, -⟩ := trunc_bellman_argmax hd hfR (x, zh)
  have hU := hUid x.1 x'.1 z.1 zh.1 hx hxx z.2.1 hzz zh.2.2
  rw [hv₁, hv₂]
  rcases le_or_gt y₁.1 y₂.1 with h12 | h21
  · have hA := ind_rhs_le h Q hQ hfR hfm (x', zh) y₂
    have hB := ind_rhs_le h Q hQ hfR hfm (x, z) y₁
    have hcost : x'.1 * (c (y₂.1 / x'.1) - c (y₁.1 / x'.1)) ≤
        x.1 * (c (y₂.1 / x.1) - c (y₁.1 / x.1)) := by
      rcases h12.lt_or_eq with hlt | heq
      · exact ind_cost_submod h hx hxx y₁.2 hlt
      · rw [heq]; simp
    simp only [ind_rhs] at hA hB ⊢
    simp only [indF] at hA hB ⊢
    linarith
  · have hA := ind_rhs_le h Q hQ hfR hfm (x', zh) y₁
    have hB := ind_rhs_le h Q hQ hfR hfm (x, z) y₂
    have hE := ind_E_incDiff Q hQm hf h21.le (show z ≤ zh from hzz)
    simp only [ind_rhs] at hA hB ⊢
    simp only [indF] at hA hB ⊢
    nlinarith [mul_le_mul_of_nonneg_left hE hβ.le]

/-- **`v` has increasing differences in `(x, z)`** when `Q` is monotone and `U` has increasing
differences (the book's `D = U_x` increasing in `z`): `v(x′, z) − v(x, z) ≤ v(x′, ẑ) − v(x, ẑ)`.
The set of functions with values in `[0, R]`, nondecreasing in `x`, with increasing differences,
is closed and mapped into itself by `T̃` (`ind_T_incDiff`). This replaces the manual's claim that
`v_x` is increasing in `z`, which ignores that `g(x, z)` moves with `z`. -/
theorem ind_v_incDiff (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) (hQm : IsMonotoneTF Q)
    (hUid : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → z₁ ≤ z → z ≤ zh → zh ≤ z₂ →
      U x' z - U x z ≤ U x' zh - U x zh)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v) : IndIncDiff v := by
  have hd := h.upperDP Q hQ
  have hb := truncModel_boundedDP hd (truncK_pos hd).le
  set B : Set (Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ) :=
    {f | (∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - 1 / (1 + r))) ∧ ∀ z, Monotone fun x => f (x, z)}
  set S' := B ∩ {f | IndIncDiff (z₁ := z₁) (z₂ := z₂) f}
  have hclosed : IsClosed S' :=
    ((isClosed_bounds _).inter isClosed_monoX).inter isClosed_indIncDiff
  have hmaps : MapsTo (truncT hd) S' S' := fun f hf =>
    ⟨⟨truncT_mapsTo hd hf.1.1, fun z => (ind_T_strictMono_x h Q hQ hf.1.1 hf.1.2 z).monotone⟩,
      ind_T_incDiff h Q hQ hQm hUid hf.1.1 hf.1.2 hf.2⟩
  exact (corollary_1 (S' := S') (S'' := S') (bellman_contraction _ hb) hv
    ⟨0, ⟨fun _ => ⟨le_rfl, div_nonneg hd.A_nonneg (by linarith [hd.β_lt])⟩,
      fun _ _ _ _ => le_rfl⟩, fun _ _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1.2

/-- **Exercise 10.4e** (monotonicity in `z`). If `Q` is monotone and `U` has increasing
differences in `(x, z)` (as when `D = U_x` is increasing in `z`), then `g(x, ·)` is
nondecreasing: `z ≤ ẑ` implies `g(x, z) ≤ g(x, ẑ)`. By `ind_v_incDiff` and monotonicity of `Q`,
the objective `−x c(y/x) + β∫v(y, z′)Q(z, dz′)` has increasing differences in `(y, z)`, so if
`g(x, ẑ) < g(x, z)` then `g(x, z)` is also optimal at `ẑ`, contradicting uniqueness. -/
theorem ex_10_4e (h : IndHyp U c δ δ' M r A z₁ z₂) (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂))
    [IsMarkovKernel Q] (hQ : IsFeller Q) (hQm : IsMonotoneTF Q)
    (hUid : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → z₁ ≤ z → z ≤ zh → zh ≤ z₂ →
      U x' z - U x z ≤ U x' zh - U x zh)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    {x y yh : Ioi (0 : ℝ)} {z zh : Icc z₁ z₂} (hzz : z.1 ≤ zh.1)
    (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hyh : yh ∈ policy (indModel Q U c δ' M r) v (x, zh)) : y.1 ≤ yh.1 := by
  by_contra hlt
  push Not at hlt
  have hβ : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  have hE := ind_E_incDiff Q hQm (ind_v_incDiff h Q hQ hQm hUid hv) (y := yh) (y' := y) hlt.le
    (show z ≤ zh from hzz)
  have h0 := ((ind_mem_policy_iff h Q hQ hv _ _).1 hy).2 yh hyh.1
  have hopt : y ∈ policy (indModel Q U c δ' M r) v (x, zh) := by
    refine (ind_mem_policy_iff h Q hQ hv _ _).2 ⟨hy.1, fun w hw => ?_⟩
    refine (((ind_mem_policy_iff h Q hQ hv _ _).1 hyh).2 w hw).trans ?_
    simp only [ind_rhs] at h0 ⊢
    simp only [indF] at h0 ⊢
    nlinarith [mul_le_mul_of_nonneg_left hE hβ.le]
  have hpol := (ind_policy h Q hQ hv).2.1
  have := (ind_policy h Q hQ hv).1.unique (x, zh) y (hpol (x, zh) ▸ hopt) yh
    (hpol (x, zh) ▸ hyh)
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-- **Exercise 10.4e**, strict form, corrected. If moreover the expected marginal value of
capital at `y = g(x, z)` is strictly higher under `ẑ`, `W_z′(y) < W_ẑ′(y)`, then
`g(x, z) < g(x, ẑ)`: equality would make both first-order conditions read `c′(y/x)`. Without
such a condition strict monotonicity fails (`ex_10_4e_strict_counterexample`). -/
theorem ex_10_4e_strict (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q)
    (hUid : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → z₁ ≤ z → z ≤ zh → zh ≤ z₂ →
      U x' z - U x z ≤ U x' zh - U x zh)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    {x y yh : Ioi (0 : ℝ)} {z zh : Icc z₁ z₂} (hzz : z.1 ≤ zh.1)
    (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z))
    (hyh : yh ∈ policy (indModel Q U c δ' M r) v (x, zh)) (hcd : DifferentiableAt ℝ c (y.1 / x.1))
    {w wh : ℝ} (hw : HasDerivAt (indW Q v z) w y.1) (hwh : HasDerivAt (indW Q v zh) wh y.1)
    (hwwh : w < wh) : y.1 < yh.1 := by
  rcases (ex_10_4e h Q hQ hQm hUid hv hzz hy hyh).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hβ : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  have e1 := ind_foc h Q hQ hv hy hcd.hasDerivAt hw
  have hc' : HasDerivAt c (deriv c (y.1 / x.1)) (yh.1 / x.1) := by rw [← heq]; exact hcd.hasDerivAt
  have hwh' : HasDerivAt (indW Q v zh) wh yh.1 := by rw [← heq]; exact hwh
  have e2 := ind_foc h Q hQ hv hyh hc' hwh'
  nlinarith [mul_lt_mul_of_pos_left hwwh hβ]

/-! ### Exercise 10.4f: the stationary point -/

/-- **Growth from small capacity.** Suppose that for some `y₀ > 0` the marginal surplus
`U_x(y₀, z′)` exceeds `(1 + r)c′(1)` for every `z′` (the condition of the manual,
`(1 + r)c′(1) < D(0, z)`, at a positive capacity). Then `g(x, z) > x` for `0 < x ≤ y₀`, for any
`Q`. Otherwise `a = g(x, z)/x ≤ 1`, so `c′(a) ≤ c′(1)`; but by the envelope condition
`v_x(y, z′) = U_x(y, z′) + a′c′(a′) − c(a′) ≥ U_x(y, z′) ≥ U_x(y₀, z′)` at `y = g(x, z) ≤ y₀`,
so the first-order condition gives `c′(a) = (1 + r)⁻¹ ∫ v_x(y, z′) Q(z, dz′) > c′(1)`. -/
theorem ind_policy_gt_self (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hpos : ∀ z' : Icc z₁ z₂, (1 + r) * deriv c 1 < deriv (fun q => U q z'.1) y₀)
    {x y : Ioi (0 : ℝ)} (hxy₀ : x.1 ≤ y₀) {z : Icc z₁ z₂}
    (hy : y ∈ policy (indModel Q U c δ' M r) v (x, z)) : x.1 < y.1 := by
  by_contra hle
  push Not at hle
  have hx : 0 < x.1 := x.2
  have hy0 : 0 < y.1 := y.2
  obtain ⟨D, hD, hDi, hW⟩ := indW_hasDerivAt h Q hQ hv hUd hcd z hy0
  have hc := (hcd _ (div_pos hy0 hx)).hasDerivAt
  have e1 := ind_foc h Q hQ hv hy hc hW
  have hDlow : ∀ z', (1 + r) * deriv c 1 < D z' := by
    intro z'
    obtain ⟨⟨y', hy', hval⟩, -, -⟩ := ind_max h Q hQ hv (y, z')
    have hca := (hcd _ (div_pos y'.2 hy0)).hasDerivAt
    have hUa := (hUd z' y.1 hy0).hasDerivAt
    have hDeq := (hD z').unique (ind_hasDerivAt_x h Q hQ hv (x₀ := y) ⟨hy', hval⟩ hUa hca)
    have htan := ind_c_le_mul_deriv h (div_pos y'.2 hy0) hca
    have hUmono : deriv (fun q => U q z'.1) y₀ ≤ deriv (fun q => U q z'.1) y.1 := by
      rcases (hle.trans hxy₀).lt_or_eq with hlt | heq
      · have hconc := (h.U_conc z'.1 z'.2).concaveOn
        exact (hconc.le_slope_of_hasDerivAt (mem_Ici.2 hy0.le) (mem_Ici.2 hy₀.le) hlt
          (hUd z' y₀ hy₀).hasDerivAt).trans
          (hconc.slope_le_of_hasDerivAt (mem_Ici.2 hy0.le) (mem_Ici.2 hy₀.le) hlt hUa)
      · rw [heq]
    linarith [hpos z']
  have hint : (1 + r) * deriv c 1 < ∫ z', D z' ∂Q z := by
    have := integral_lt_integral_of_lt (integrable_const ((1 + r) * deriv c 1)) hDi hDlow
    simpa using this
  have hmono := ind_c_deriv_mono h (div_pos hy0 hx) ((div_le_one hx).2 hle) hc
    (hcd 1 one_pos).hasDerivAt
  have hβ : 0 < 1 / (1 + r) := one_div_pos.2 (by linarith [h.r_pos])
  have e2 : 1 / (1 + r) * ((1 + r) * deriv c 1) = deriv c 1 := by
    field_simp [show (1 + r) ≠ 0 by linarith [h.r_pos]]
  nlinarith [mul_lt_mul_of_pos_left hint hβ]

/-- A positive sequence that rises whenever it is below some `b > 0` does not tend to `0`. -/
theorem ind_not_tendsto_zero (xs : ℕ → Ioi (0 : ℝ)) {b : ℝ} (hb : 0 < b)
    (hgrow : ∀ t, (xs t).1 < b → (xs t).1 < (xs (t + 1)).1) :
    ¬ Tendsto (fun t => (xs t).1) atTop (𝓝 0) := by
  intro hlim
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hb))
  have hup : ∀ t ≥ T, (xs T).1 ≤ (xs t).1 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih => exact ih.trans (hgrow t (hT t ht)).le
  have := ge_of_tendsto hlim (eventually_atTop.2 ⟨T, hup⟩)
  linarith [(xs T).2.out]

/-- **Uniqueness of the positive stationary point** of `g(·, z)`: if `p = g(p, z)` and
`p′ = g(p′, z)` then `p = p′`, because `g(x, z)/x` is strictly decreasing
(`ind_policy_ratio_lt`). -/
theorem ind_stationary_unique (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {p p' : Ioi (0 : ℝ)} {z : Icc z₁ z₂}
    (hp : p ∈ policy (indModel Q U c δ' M r) v (p, z))
    (hp' : p' ∈ policy (indModel Q U c δ' M r) v (p', z)) : p = p' := by
  have hp0 : 0 < p.1 := p.2
  have hp0' : 0 < p'.1 := p'.2
  rcases lt_trichotomy p.1 p'.1 with hlt | heq | hgt
  · have := ind_policy_ratio_lt h Q hQ hv hUd hcd hlt z hp hp'
    rw [div_self hp0.ne', div_self hp0'.ne'] at this
    exact absurd this (lt_irrefl 1)
  · exact Subtype.ext heq
  · have := ind_policy_ratio_lt h Q hQ hv hUd hcd hgt z hp' hp
    rw [div_self hp0.ne', div_self hp0'.ne'] at this
    exact absurd this (lt_irrefl 1)

/-- **A positive limit is stationary.** Under i.i.d. shocks, if an optimal path converges to
`L > 0` then `L = g(L)`. For `x` near `L`, `g(x)` lies between `g(L)` and `g(L)x/L` (`g` is
nondecreasing and `g(x)/x` nonincreasing), so `g(xₜ) → g(L)`. -/
theorem ind_limit_stationary (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hiid : ∀ z z', Q z = Q z') {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) (xs : ℕ → Ioi (0 : ℝ))
    (zs : ℕ → Icc z₁ z₂) (hseq : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs t))
    {L : ℝ} (hL : 0 < L) (hlim : Tendsto (fun t => (xs t).1) atTop (𝓝 L)) (z : Icc z₁ z₂) :
    (⟨L, hL⟩ : Ioi (0 : ℝ)) ∈ policy (indModel Q U c δ' M r) v (⟨L, hL⟩, z) := by
  set pL : Ioi (0 : ℝ) := ⟨L, hL⟩
  obtain ⟨⟨yh, hyh, hval⟩, -, -⟩ := ind_max h Q hQ hv (pL, z)
  have hyhp : yh ∈ policy (indModel Q U c δ' M r) v (pL, z) := ⟨hyh, hval⟩
  have hmove : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, z) :=
    fun t => ex_10_4f h Q hQ hiid hv (xs t) (zs t) z ▸ hseq t
  have hyh0 : 0 < yh.1 := yh.2
  -- the sandwich
  have hlow : ∀ t, min yh.1 (yh.1 * (xs t).1 / L) ≤ (xs (t + 1)).1 := by
    intro t
    have hx : 0 < (xs t).1 := (xs t).2
    rcases le_total (xs t).1 L with hle | hge
    · refine min_le_of_right_le ?_
      have := ind_policy_ratio_le h Q hQ hv hUd hcd (x := xs t) (x' := pL) hle z (hmove t) hyhp
      rw [div_le_div_iff₀ hL hx] at this
      rw [div_le_iff₀ hL]
      linarith
    · exact min_le_of_left_le (ex_10_4d h Q hQ hv (x := pL) (x' := xs t) hge z hyhp (hmove t))
  have hup : ∀ t, (xs (t + 1)).1 ≤ max yh.1 (yh.1 * (xs t).1 / L) := by
    intro t
    have hx : 0 < (xs t).1 := (xs t).2
    rcases le_total (xs t).1 L with hle | hge
    · exact le_max_of_le_left (ex_10_4d h Q hQ hv (x := xs t) (x' := pL) hle z (hmove t) hyhp)
    · refine le_max_of_le_right ?_
      have := ind_policy_ratio_le h Q hQ hv hUd hcd (x := pL) (x' := xs t) hge z hyhp (hmove t)
      rw [div_le_div_iff₀ hx hL] at this
      rw [le_div_iff₀ hL]
      linarith
  have hscaled : Tendsto (fun t => yh.1 * (xs t).1 / L) atTop (𝓝 yh.1) := by
    have := (hlim.const_mul yh.1).div_const L
    rwa [mul_div_assoc, div_self hL.ne', mul_one] at this
  have hnext : Tendsto (fun t => (xs (t + 1)).1) atTop (𝓝 yh.1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds (x := yh.1)).min hscaled)
      (by simpa using (tendsto_const_nhds (x := yh.1)).max hscaled) hlow hup
  have heq : yh.1 = L := tendsto_nhds_unique hnext ((tendsto_add_atTop_iff_nat 1).2 hlim)
  have : yh = pL := Subtype.ext heq
  rwa [this] at hyhp

/-- **Exercise 10.4f** (the limit does not depend on `x₀`). Under i.i.d. shocks, with `U(·, z)`
and `c` differentiable, any two optimal capacity paths, from any `x₀, x₀′ > 0` and along any
shock paths, have the same limit. Positive limits are stationary (`ind_limit_stationary`) and
the positive stationary point is unique (`ind_stationary_unique`); and no path tends to `0` if
a positive stationary point `p` exists, since `g(x) > x` for `x < p`. -/
theorem ex_10_4f_limit_eq (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hiid : ∀ z z', Q z = Q z') {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) (xs xs' : ℕ → Ioi (0 : ℝ))
    (zs zs' : ℕ → Icc z₁ z₂)
    (hseq : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs t))
    (hseq' : ∀ t, xs' (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs' t, zs' t)) {L L' : ℝ}
    (hL : Tendsto (fun t => (xs t).1) atTop (𝓝 L))
    (hL' : Tendsto (fun t => (xs' t).1) atTop (𝓝 L')) : L = L' := by
  have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (xs t).2.out.le)
  have hL0' : 0 ≤ L' := ge_of_tendsto hL' (Eventually.of_forall fun t => (xs' t).2.out.le)
  set z := zs 0
  -- a path cannot tend to `0` when a positive stationary point exists
  have key : ∀ (ys : ℕ → Ioi (0 : ℝ)) (ws : ℕ → Icc z₁ z₂),
      (∀ t, ys (t + 1) ∈ policy (indModel Q U c δ' M r) v (ys t, ws t)) →
      ∀ p : Ioi (0 : ℝ), p ∈ policy (indModel Q U c δ' M r) v (p, z) →
      ¬ Tendsto (fun t => (ys t).1) atTop (𝓝 0) := by
    intro ys ws hys p hp
    refine ind_not_tendsto_zero ys p.2 fun t ht => ?_
    have hmv : ys (t + 1) ∈ policy (indModel Q U c δ' M r) v (ys t, z) :=
      ex_10_4f h Q hQ hiid hv (ys t) (ws t) z ▸ hys t
    have := ind_policy_ratio_lt h Q hQ hv hUd hcd (x := ys t) (x' := p) ht z hmv hp
    rw [div_self (ne_of_gt p.2), lt_div_iff₀ (ys t).2] at this
    linarith
  rcases hL0.lt_or_eq with hpos | hzero <;> rcases hL0'.lt_or_eq with hpos' | hzero'
  · exact congrArg Subtype.val (ind_stationary_unique h Q hQ hv hUd hcd
      (ind_limit_stationary h Q hQ hiid hv hUd hcd xs zs hseq hpos hL z)
      (ind_limit_stationary h Q hQ hiid hv hUd hcd xs' zs' hseq' hpos' hL' z))
  · exact absurd (hzero' ▸ hL') (key xs' zs' hseq' _
      (ind_limit_stationary h Q hQ hiid hv hUd hcd xs zs hseq hpos hL z))
  · exact absurd (hzero ▸ hL) (key xs zs hseq _
      (ind_limit_stationary h Q hQ hiid hv hUd hcd xs' zs' hseq' hpos' hL' z))
  · rw [← hzero, ← hzero']

/-- **Exercise 10.4f** (positivity). If `U_x(y₀, z′) > (1 + r)c′(1)` for all `z′` at some
`y₀ > 0`, every convergent optimal path has a positive limit: below `y₀` capacity grows
(`ind_policy_gt_self`). This holds for any `Q`. -/
theorem ex_10_4f_limit_pos (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ} (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hpos : ∀ z' : Icc z₁ z₂, (1 + r) * deriv c 1 < deriv (fun q => U q z'.1) y₀)
    (xs : ℕ → Ioi (0 : ℝ)) (zs : ℕ → Icc z₁ z₂)
    (hseq : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs t)) {L : ℝ}
    (hL : Tendsto (fun t => (xs t).1) atTop (𝓝 L)) : 0 < L := by
  have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (xs t).2.out.le)
  rcases hL0.lt_or_eq with hpos' | hzero
  · exact hpos'
  · exact absurd (hzero ▸ hL) (ind_not_tendsto_zero xs hy₀ fun t ht =>
      ind_policy_gt_self h Q hQ hv hUd hcd hy₀ hpos ht.le (hseq t))

/-- **Exercise 10.4f.** Under i.i.d. shocks, with `U(·, z)` and `c` differentiable on `(0, ∞)`,
there is `x̂ ≥ 0` such that every optimal capacity path, from any `x₀ > 0` and along any shock
path, converges to `x̂`; if `x̂ > 0` it is the unique positive stationary point,
`x̂ = g(x̂, z)` for all `z`; and if `U_x(y₀, z′) > (1 + r)c′(1)` for all `z′` at some
`y₀ > 0`, then `x̂ > 0`. Without such a condition `x̂` may be `0`, where capacity dies out. -/
theorem ex_10_4f_stationary (h : IndHyp U c δ δ' M r A z₁ z₂)
    (Q : Kernel (Icc z₁ z₂) (Icc z₁ z₂)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hiid : ∀ z z', Q z = Q z') {v : Ioi (0 : ℝ) × Icc z₁ z₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP Q hQ) v = v)
    (hUd : ∀ (z : Icc z₁ z₂) (q : ℝ), 0 < q → DifferentiableAt ℝ (fun q => U q z.1) q)
    (hcd : ∀ a : ℝ, 0 < a → DifferentiableAt ℝ c a) :
    ∃ xh : ℝ, 0 ≤ xh ∧
      (∀ (xs : ℕ → Ioi (0 : ℝ)) (zs : ℕ → Icc z₁ z₂),
        (∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, zs t)) →
        Tendsto (fun t => (xs t).1) atTop (𝓝 xh)) ∧
      (∀ hxh : 0 < xh, ∀ z,
        (⟨xh, hxh⟩ : Ioi (0 : ℝ)) ∈ policy (indModel Q U c δ' M r) v (⟨xh, hxh⟩, z)) ∧
      ∀ y₀ : ℝ, 0 < y₀ →
        (∀ z' : Icc z₁ z₂, (1 + r) * deriv c 1 < deriv (fun q => U q z'.1) y₀) → 0 < xh := by
  -- a reference path from `x₀ = 1` under the shock `z₁`
  have z0 : Icc z₁ z₂ := ⟨z₁, le_rfl, h.z_le⟩
  have hex : ∀ x : Ioi (0 : ℝ), ∃ y, y ∈ policy (indModel Q U c δ' M r) v (x, z0) := fun x => by
    obtain ⟨⟨y, hy, hval⟩, -, -⟩ := ind_max h Q hQ hv (x, z0)
    exact ⟨y, hy, hval⟩
  set xs : ℕ → Ioi (0 : ℝ) := fun t =>
    Nat.rec (motive := fun _ => Ioi (0 : ℝ)) ⟨1, mem_Ioi.2 one_pos⟩ (fun _ x => (hex x).choose) t
  have hseq : ∀ t, xs (t + 1) ∈ policy (indModel Q U c δ' M r) v (xs t, z0) :=
    fun t => (hex (xs t)).choose_spec
  obtain ⟨L, hL⟩ := ex_10_4f_tendsto h Q hQ hiid hv xs (fun _ => z0) hseq
  have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (xs t).2.out.le)
  refine ⟨L, hL0, fun xs' zs' hseq' => ?_, fun hxh z =>
    ind_limit_stationary h Q hQ hiid hv hUd hcd xs (fun _ => z0) hseq hxh hL z,
    fun y₀ hy₀ hpos => ex_10_4f_limit_pos h Q hQ hv hUd hcd hy₀ hpos xs (fun _ => z0) hseq hL⟩
  obtain ⟨L', hL'⟩ := ex_10_4f_tendsto h Q hQ hiid hv xs' zs' hseq'
  rwa [ex_10_4f_limit_eq h Q hQ hiid hv hUd hcd xs xs' (fun _ => z0) zs' hseq hseq' hL hL']

/-! ### Counterexamples -/

/-- Consumers' surplus `U(q, z) = 10 z q/(1 + q)`, from the demand curve
`D(q, z) = 10z/(1 + q)²`, which is continuous, strictly decreasing in `q` and strictly increasing
in `z`. -/
noncomputable def indU0 (q z : ℝ) : ℝ := 10 * z * (q / (1 + q))

/-- `U_x(q, z) = 10z/(1 + q)²`. -/
theorem hasDerivAt_indU0 (z : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (fun q => indU0 q z) (10 * z / (1 + q) ^ 2) q := by
  have h1 : (1 + q) ≠ 0 := by linarith
  have := ((hasDerivAt_id' q).fun_div ((hasDerivAt_id' q).const_add 1) h1).const_mul (10 * z)
  convert this using 1
  · rfl
  · rw [show 1 * (1 + q) - q * 1 = (1 : ℝ) by ring]
    ring

/-- `c(a) = max{a − ½, 0}²` has derivative `2 max{a − ½, 0}` everywhere. -/
theorem hasDerivAt_cq (a : ℝ) : HasDerivAt cq (2 * max (a - 1 / 2) 0) a := by
  have hsq : HasDerivAt (fun t : ℝ => (t - 1 / 2) ^ 2) (2 * (a - 1 / 2)) a := by
    have := ((hasDerivAt_id' a).sub_const (1 / 2)).fun_pow 2
    convert this using 1
    norm_num
  rcases lt_trichotomy a (1 / 2) with hlt | heq | hgt
  · have hev : cq =ᶠ[𝓝 a] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [cq, max_eq_right (by linarith [mem_Iio.1 ht] : t - 1 / 2 ≤ 0)]
      norm_num
    rw [max_eq_right (by linarith), mul_zero]
    exact (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq hev
  · subst heq
    rw [sub_self, max_self, mul_zero]
    have hR : HasDerivWithinAt cq 0 (Ici (1 / 2)) (1 / 2) := by
      have := hsq.hasDerivWithinAt (s := Ici (1 / 2))
      rw [sub_self, mul_zero] at this
      refine this.congr (fun t ht => ?_) ?_
      · simp only [cq, max_eq_left (by linarith [mem_Ici.1 ht] : (0 : ℝ) ≤ t - 1 / 2)]
      · simp [cq]
    have hL : HasDerivWithinAt cq 0 (Iic (1 / 2)) (1 / 2) := by
      refine (hasDerivAt_const (1 / 2 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr (fun t ht => ?_) ?_
      · simp only [cq, max_eq_right (by linarith [mem_Iic.1 ht] : t - 1 / 2 ≤ 0)]
        norm_num
      · simp [cq]
    have := hL.union hR
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hev : cq =ᶠ[𝓝 a] fun t => (t - 1 / 2) ^ 2 := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [cq, max_eq_left (by linarith [mem_Ioi.1 ht] : (0 : ℝ) ≤ t - 1 / 2)]
    rw [max_eq_left (by linarith)]
    exact hsq.congr_of_eventuallyEq hev

/-- The parameters `U = indU0`, `c = cq`, `δ = ½`, `δ′ = ¾`, `M = 200`, `r = 1`, `A = 20`,
`Z = [1, 2]` satisfy the hypotheses of §10.4. -/
theorem ind0_hyp : IndHyp indU0 cq (1 / 2) (3 / 4) 200 1 20 1 2 := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := cq_props
  have hfrac : ∀ q : ℝ, 0 ≤ q → q / (1 + q) ≤ 1 := fun q hq =>
    (div_le_one (by linarith)).2 (by linarith)
  refine ⟨one_pos, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_,
    ?_, ?_, ?_, hc1, hc2, hc3, hc4, hc5, ?_⟩
  · refine ((continuous_const.mul continuous_snd).continuousOn).mul
      (continuous_fst.continuousOn.div (continuous_const.add continuous_fst).continuousOn
        fun p hp => ?_)
    have := mem_Ici.1 hp.1
    linarith
  · intro q z hq hz
    have := hz.1
    unfold indU0
    positivity
  · intro q z hq hz
    unfold indU0
    have h1 := hfrac q hq
    have h2 : 0 ≤ q / (1 + q) := by positivity
    nlinarith [hz.1, hz.2]
  · intro z hz a ha b hb hab
    simp only [indU0]
    have ha' := mem_Ici.1 ha
    have hz1 := hz.1
    have : a / (1 + a) < b / (1 + b) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    nlinarith
  · intro z hz
    refine ⟨convex_Ici 0, fun a ha b hb hne θ η hθ hη hθη => ?_⟩
    have ha' := mem_Ici.1 ha
    have hb' := mem_Ici.1 hb
    have hz1 := hz.1
    simp only [smul_eq_mul, indU0]
    set m := θ * a + η * b
    have hm : 0 ≤ m := by positivity
    have e : ∀ q : ℝ, 0 ≤ q → q / (1 + q) = 1 - 1 / (1 + q) := fun q hq => by
      field_simp
      ring
    rw [e a ha', e b hb', e m hm]
    have key : 1 / (1 + m) < θ / (1 + a) + η / (1 + b) := by
      have hab : 0 < (a - b) ^ 2 := by
        have : a - b ≠ 0 := sub_ne_zero.2 hne
        positivity
      rw [div_add_div _ _ (by linarith) (by linarith), div_lt_div_iff₀ (by linarith)
        (by positivity)]
      have hη' : η = 1 - θ := by linarith
      simp only [m]
      rw [hη'] at hη ⊢
      nlinarith [mul_pos (mul_pos hθ hη) hab]
    have : θ * (1 - 1 / (1 + a)) + η * (1 - 1 / (1 + b)) = 1 - (θ / (1 + a) + η / (1 + b)) := by
      rw [show θ * (1 - 1 / (1 + a)) = θ - θ / (1 + a) by ring,
        show η * (1 - 1 / (1 + b)) = η - η / (1 + b) by ring]
      linarith
    have h10 : 0 < 10 * z := by linarith
    nlinarith [mul_lt_mul_of_pos_left key h10]
  · intro q hq a ha b hb hab
    simp only [indU0]
    have : 0 < q / (1 + q) := by positivity
    nlinarith
  · norm_num [cq]

/-- The i.i.d. kernel `Q(z, ·) = δ₁` on `Z = [1, 2]`. -/
noncomputable abbrev indQ0 : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2) :=
  Kernel.const _ (Measure.dirac ⟨1, by norm_num, by norm_num⟩)

/-- `indQ0` is Feller, monotone and i.i.d. -/
theorem indQ0_props : IsFeller indQ0 ∧ IsMonotoneTF indQ0 ∧ ∀ z z', indQ0 z = indQ0 z' :=
  ⟨isFeller_const _, fun f _ _ _ a b _ => by simp [markovOpR, Kernel.const_apply],
    fun _ _ => rfl⟩

/-- `indU0` has increasing differences in `(x, z)`: `D = U_x` is increasing in `z`. -/
theorem indU0_incDiff : ∀ x x' z zh : ℝ, 0 < x → x ≤ x' → 1 ≤ z → z ≤ zh → zh ≤ 2 →
    indU0 x' z - indU0 x z ≤ indU0 x' zh - indU0 x zh := by
  intro x x' z zh hx hxx hz hzz _
  simp only [indU0]
  have : x / (1 + x) ≤ x' / (1 + x') := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  nlinarith

/-- `U(·, z)` is differentiable on `(0, ∞)` and `c` on all of `ℝ`, for the parameters
`ind0_hyp`. -/
theorem ind0_diff : (∀ (z : Icc (1 : ℝ) 2) (q : ℝ), 0 < q →
    DifferentiableAt ℝ (fun q => indU0 q z.1) q) ∧ ∀ a : ℝ, 0 < a → DifferentiableAt ℝ cq a :=
  ⟨fun z _ hq => (hasDerivAt_indU0 z.1 hq.le).differentiableAt,
    fun a _ => (hasDerivAt_cq a).differentiableAt⟩

/-- **Exercise 10.4e: strict monotonicity in `z` fails.** The book claims that `g(x, ·)` is
strictly increasing where gross investment is positive. With the parameters `ind0_hyp`, the
monotone Feller i.i.d. kernel `indQ0` (`indQ0_props`) and `D` increasing in `z`
(`indU0_incDiff`), every hypothesis of 10.4e holds, gross investment is positive everywhere
(`ind_policy_gt`), but `g(x, z)` does not depend on `z` (`ex_10_4f`). -/
theorem ex_10_4e_strict_counterexample {v : Ioi (0 : ℝ) × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : truncT (ind0_hyp.upperDP indQ0 indQ0_props.1) v = v) :
    ¬ ∀ (x y yh : Ioi (0 : ℝ)) (z zh : Icc (1 : ℝ) 2), z.1 < zh.1 →
      y ∈ policy (indModel indQ0 indU0 cq (3 / 4) 200 1) v (x, z) →
      yh ∈ policy (indModel indQ0 indU0 cq (3 / 4) 200 1) v (x, zh) →
      (1 - 1 / 2) * x.1 < y.1 → y.1 < yh.1 := by
  intro hclaim
  set x : Ioi (0 : ℝ) := ⟨1, mem_Ioi.2 one_pos⟩
  set z : Icc (1 : ℝ) 2 := ⟨1, by norm_num, by norm_num⟩
  set zh : Icc (1 : ℝ) 2 := ⟨2, by norm_num, by norm_num⟩
  obtain ⟨⟨y, hy, hval⟩, -, -⟩ := ind_max ind0_hyp indQ0 indQ0_props.1 hv (x, z)
  have hyp : y ∈ policy (indModel indQ0 indU0 cq (3 / 4) 200 1) v (x, z) := ⟨hy, hval⟩
  have hyh : y ∈ policy (indModel indQ0 indU0 cq (3 / 4) 200 1) v (x, zh) :=
    ex_10_4f ind0_hyp indQ0 indQ0_props.1 indQ0_props.2.2 hv x z zh ▸ hyp
  have hgt := ind_policy_gt ind0_hyp indQ0 indQ0_props.1 hv (ind0_diff.2 _ (by norm_num)) hyp
  exact lt_irrefl _ (hclaim x y y z zh (by norm_num [z, zh]) hyp hyh hgt)

/-- **Exercise 10.4d: the slope of `g(·, z)` can exceed one.** With the parameters `ind0_hyp`
(and any Feller `Q`), for every `z` there are `x < x′` with
`g(x′, z) − g(x, z) > x′ − x`. Here `U_x(½, z′) ≥ 40/9 > 2 = (1 + r)c′(1)`, so `g(x, z) > x`
for `x ≤ ½` (`ind_policy_gt_self`); but `x c(g/x) ≤ βR = 20` forces
`(g(x, z) − x/2)² ≤ 20x`, so `g(x, z) − x → 0` as `x → 0`. Hence `g(x, z) − x` is not
decreasing on `(0, ½]`. What holds is `ind_policy_slope_lt`: the slope is below the growth rate
`g(x, z)/x`. -/
theorem ex_10_4d_slope_counterexample (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Ioi (0 : ℝ) × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : truncT (ind0_hyp.upperDP Q hQ) v = v) (z : Icc (1 : ℝ) 2) :
    ∃ x x' y y' : Ioi (0 : ℝ), x.1 < x'.1 ∧
      y ∈ policy (indModel Q indU0 cq (3 / 4) 200 1) v (x, z) ∧
      y' ∈ policy (indModel Q indU0 cq (3 / 4) 200 1) v (x', z) ∧ x'.1 - x.1 < y'.1 - y.1 := by
  have h := ind0_hyp
  obtain ⟨hUd, hcd⟩ := ind0_diff
  have hpos : ∀ z' : Icc (1 : ℝ) 2,
      (1 + 1) * deriv cq 1 < deriv (fun q => indU0 q z'.1) (1 / 2) := by
    intro z'
    rw [(hasDerivAt_cq 1).deriv, (hasDerivAt_indU0 z'.1 (by norm_num)).deriv,
      max_eq_left (by norm_num), lt_div_iff₀ (by norm_num)]
    nlinarith [z'.2.1]
  set x' : Ioi (0 : ℝ) := ⟨1 / 2, mem_Ioi.2 (by norm_num)⟩
  obtain ⟨⟨y', hy', hval'⟩, -, -⟩ := ind_max h Q hQ hv (x', z)
  have hy'p : y' ∈ policy (indModel Q indU0 cq (3 / 4) 200 1) v (x', z) := ⟨hy', hval'⟩
  have hgrow : (1 / 2 : ℝ) < y'.1 :=
    ind_policy_gt_self h Q hQ hv hUd hcd (y₀ := 1 / 2) (by norm_num) hpos (x := x') le_rfl hy'p
  set d := y'.1 - 1 / 2 with hddef
  have hd : 0 < d := by linarith
  set t := min (1 / 4) (d ^ 2 / 40) with htdef
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 4 := min_le_left _ _
  have ht2 : t ≤ d ^ 2 / 40 := min_le_right _ _
  set x : Ioi (0 : ℝ) := ⟨t, mem_Ioi.2 ht⟩
  obtain ⟨⟨y, hy, hval⟩, -, -⟩ := ind_max h Q hQ hv (x, z)
  have hyp : y ∈ policy (indModel Q indU0 cq (3 / 4) 200 1) v (x, z) := ⟨hy, hval⟩
  have hlow : (1 - 1 / 2) * t ≤ y.1 := ((ind_policy h Q hQ hv).2.2 _ y hyp).1
  -- the value of `y` beats the free choice `(1 − δ)x`
  have hvR := (ind_strictMono_x h Q hQ hv).1
  have e1 : v (x, z) = indU0 t z.1 - t * cq (y.1 / t) + 1 / (1 + 1) * ∫ z', v (y, z') ∂Q z :=
    hyp.2
  have hsafe := ind_rhs_le_v h Q hQ hv (x, z) (h.safeY x)
  rw [ind_rhs, (h.safe_mem x z).2] at hsafe
  have hE0 : 0 ≤ ∫ z', v (h.safeY x, z') ∂Q z := integral_nonneg fun z' => (hvR _).1
  have hE1 : ∫ z', v (y, z') ∂Q z ≤ 20 / (1 - 1 / (1 + 1)) := by
    have := integral_mono (integrable_ind (Q := Q) v y z)
      (integrable_const (20 / (1 - 1 / (1 + 1) : ℝ))) fun z' => (hvR _).2
    simpa using this
  have hcost : t * cq (y.1 / t) ≤ 20 := by
    simp only at hsafe
    norm_num at hE1 hsafe e1 ⊢
    nlinarith
  have hyt : 1 / 2 ≤ y.1 / t := by rw [le_div_iff₀ ht]; linarith
  have hsq : (y.1 - t / 2) ^ 2 ≤ 20 * t := by
    rw [cq, max_eq_left (by linarith)] at hcost
    have e : (y.1 - t / 2) ^ 2 = t * (t * (y.1 / t - 1 / 2) ^ 2) := by field_simp
    rw [e]
    nlinarith
  have hyd : y.1 < t + d := by
    by_contra hge
    push Not at hge
    have h1 : d ≤ y.1 - t / 2 := by linarith
    have h2 : d ^ 2 ≤ (y.1 - t / 2) ^ 2 := pow_le_pow_left₀ hd.le h1 2
    nlinarith
  refine ⟨x, x', y, y', ?_, hyp, hy'p, ?_⟩
  · change t < 1 / 2
    linarith
  · change 1 / 2 - t < y'.1 - y.1
    linarith
end StokeyLucasPrescott.StochasticApplications
