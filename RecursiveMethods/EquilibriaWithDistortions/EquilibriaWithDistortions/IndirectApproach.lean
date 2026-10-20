/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# An indirect approach to equilibria with distortions

SLP §18.1, pp. 543–547. An individual with own capital `x` facing a given aggregate capital path
`k_t` consumes `c_t = a_t + b_t x_t − x_{t+1}`, where the intercept `a_t` (wages, rebates) and the
slope `b_t` (after-tax return on own capital) are determined by `k_t`:

* untaxed economy (§18.1 (2)): `a_t = f(k_t) − k_t f′(k_t)`, `b_t = f′(k_t)`;
* capital-income tax `θ` with lump-sum rebate (§18.1 (3)): `a_t = f(k_t) − (1 − θ) k_t f′(k_t)`,
  `b_t = (1 − θ) f′(k_t)`;
* Exercise 18.2 (tax `α` on all income thrown away, tax `θ` on capital income rebated):
  `a_t = (1 − α) f(k_t) − (1 − α − θ) k_t f′(k_t)`, `b_t = (1 − α − θ) f′(k_t)`.

The individual's problem is a concave sequence problem whose return depends on time through the
given path. The book's and the manual's arguments rest on the sufficiency of the Euler equation and
the transversality condition for such a problem (a non-stationary version of Theorem 4.15), which
is proved here first:

* `euler_telescope`: the telescoping identity behind Theorem 4.15.
* `euler_partial_sum_le`: the finite-horizon bound.
* `euler_tvc_optimal`, `euler_tvc_strict`, `euler_tvc_unique`, `euler_tvc_isGreatest`:
  Euler + transversality ⇒ optimal; with strict concavity, the unique optimum.
* `tvc_of_bounded`: the transversality condition holds along bounded paths (`0 ≤ β < 1`).

Results of §18.1.

* **Exercise 18.1** (`ex_18_1`, p. 544): the planner's path `k_{t+1} = g(k_t)`, satisfying the
  planner's Euler equation and transversality condition, is the unique optimum of the individual
  who starts with `x_0 = k_0` and expects aggregate capital to follow `g`. So
  `G(k, k; g) = g(k)` (`x_1 = g(k_0)`) and `V(k, k; g) = v(k)` (the individual's maximal value
  is the planner's value).
* `budget_rebate` (p. 545): wages + after-tax capital income + rebate
  `= f(k) + (1 − θ)(x − k) f′(k)`.
* `pseudo_economy_solves_6_7` (p. 546): if `w`, `ĥ` satisfy §18.1 (9)–(10) with
  `β̂ = (1 − θ)β`, then `φ = (1 − θ) w′`, `h = ĥ` satisfy §18.1 (6)–(7).
* `indirect_equilibrium` (p. 546): the pseudo-planner's path is the unique optimum of an
  individual of the taxed economy, provided the individual's transversality condition holds.
* **Exercise 18.2** (`ex_18_2_budget`, `ex_18_2_foc`, `ex_18_2`, p. 547): the economy with
  both taxes behaves like an untaxed economy with production function `(1 − α) f` and discount
  factor `β̂ = β(1 − α − θ)/(1 − α)`.

**Corrections.**
* (NOTE 18.1-A, p. 544.) The domain of the individual's problem is not stated. Here: `x_t ≥ 0`
  (no borrowing) and `c_t ≥ 0`, with `x_0` given (`IndivFeasible`); values are infinite sums
  assumed to exist (`HasSum`). The problem is posed as a sequence problem, not through the
  functional equation (2), whose unique solvability on the non-compact state space would need
  further hypotheses.
* (NOTE 18.1-B, manual Ex. 18.1.) The manual's argument uses the *sufficiency* of Euler +
  transversality for the individual's time-varying problem and the *uniqueness* of his optimum.
  Both are proved here (`euler_tvc_optimal`, `euler_tvc_unique`); they need `b_t ≥ 0`
  (i.e. `f′(k_t) ≥ 0`), `U′ ≥ 0` and, for uniqueness, strict concavity of `U`. Verified.
* (NOTE 18.1-C, p. 546.) A solution of (6)–(7) is only a candidate: the identification
  `h = ĥ` needs the individual's transversality condition, with his own discount factor `β`,
  `β^t (1 − θ) f′(k_t) U′(c_t) k_t → 0`. The pseudo-planner's condition uses `β̂^t`. The
  individual's condition implies the pseudo-planner's (`tvc_indiv_imp_pseudo`) but not
  conversely (`tvc_pseudo_not_imp_indiv_counterexample`). The individual's condition holds
  along bounded paths (`tvc_of_bounded`), e.g. paths converging to an interior steady state.
  Verified; `indirect_equilibrium` assumes the individual's condition.
* (NOTE 18.1-D, manual Ex. 18.2.) The manual's `β̂ = (1 − α − θ)/(1 − α)` omits the factor
  `β`. With it the first-order condition fails whenever `β < 1`
  (`ex_18_2_manual_counterexample`); the correct value is `β(1 − α − θ)/(1 − α)`. Verified.
* (NOTE 18.1-E, p. 547.) (i) Exercise 18.2 needs `α + θ < 1`: otherwise `β̂ ≤ 0`
  (`ex_18_2_requires_sum_lt_one`). (ii) The stated answer is for the additive reading (capital
  income taxed at `α + θ`). Under the sequential reading (the `θ`-tax levied on capital income
  net of the `α`-tax) the budget is `(1 − α) f(k) + (1 − α)(1 − θ)(x − k) f′(k)`
  (`ex_18_2_sequential_budget`) and the Euler equation is that of the pseudo-economy with
  discount factor `β(1 − θ)` (`ex_18_2_sequential_euler`), which differs from the book's value
  when `α, θ > 0` (`ex_18_2_sequential_ne`). Verified.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- Consumption at date `t` of an individual with capital path `x`, budget intercepts `a` and
after-tax returns `b`: `c_t = a_t + b_t x_t − x_{t+1}`. -/
def consPath (a b x : ℕ → ℝ) (t : ℕ) : ℝ := a t + b t * x t - x (t + 1)

/-- A capital path `x` is feasible for the individual starting from `x₀`: `x_0 = x₀`, capital
and consumption nonnegative at every date. -/
def IndivFeasible (a b : ℕ → ℝ) (x₀ : ℝ) (x : ℕ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∀ t, 0 ≤ x t ∧ 0 ≤ consPath a b x t

/-- The set of attainable lifetime utilities `∑ β^t U(c_t)` of feasible paths from `x₀`. -/
def indivValues (U : ℝ → ℝ) (β : ℝ) (a b : ℕ → ℝ) (x₀ : ℝ) : Set ℝ :=
  {S | ∃ x, IndivFeasible a b x₀ x ∧ HasSum (fun t => β ^ t * U (consPath a b x t)) S}

/-! ### Sufficiency of Euler + transversality for the individual's problem -/

/-- Tangent-line inequality for a concave function on `[0, ∞)` differentiable at `d`. -/
theorem concave_le_tangent {U : ℝ → ℝ} (hU : ConcaveOn ℝ (Ici 0) U) {c d : ℝ} (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hUd : DifferentiableAt ℝ U d) : U c ≤ U d + deriv U d * (c - d) := by
  rcases lt_trichotomy c d with h | rfl | h
  · have h1 := hU.deriv_le_slope (mem_Ici.2 hc) (mem_Ici.2 hd) h hUd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    nlinarith
  · simp
  · have h1 := hU.slope_le_deriv (mem_Ici.2 hd) (mem_Ici.2 hc) h hUd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
    linarith

/-- Strict tangent-line inequality for a strictly concave function at `c ≠ d`. -/
theorem strictConcave_lt_tangent {U : ℝ → ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ≠ d) (hUd : DifferentiableAt ℝ U d) :
    U c < U d + deriv U d * (c - d) := by
  rcases lt_or_gt_of_ne hcd with h | h
  · have h1 := hU.deriv_lt_slope (mem_Ici.2 hc) (mem_Ici.2 hd) h hUd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h1
    nlinarith
  · have h1 := hU.slope_lt_deriv (mem_Ici.2 hd) (mem_Ici.2 hc) h hUd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h1
    linarith

/-- **Telescoping identity** (proof of Theorem 4.15). If the path `xs` satisfies the Euler
equation `U′(c*_t) = β b_{t+1} U′(c*_{t+1})` and `x_0 = xs_0`, then
`∑_{t<T} β^t U′(c*_t)(c_t − c*_t) = β^T b_T U′(c*_T)(xs_T − x_T)`. -/
theorem euler_telescope (U : ℝ → ℝ) (β : ℝ) (a b xs x : ℕ → ℝ)
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (h0 : x 0 = xs 0) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * (deriv U (consPath a b xs t) *
        (consPath a b x t - consPath a b xs t)) =
      β ^ T * b T * deriv U (consPath a b xs T) * (xs T - x T) := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [sum_range_succ, ih, heul T]
    generalize deriv U (consPath a b xs (T + 1)) = D
    simp only [consPath]
    ring

/-- **Finite-horizon bound.** Along a path `xs` with nonnegative consumption satisfying the Euler
equation, every feasible path `x` from `xs_0` has
`∑_{t<T} β^t U(c_t) ≤ ∑_{t<T} β^t U(c*_t) + β^T b_T U′(c*_T)(xs_T − x_T)`. -/
theorem euler_partial_sum_le {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (hx : IndivFeasible a b (xs 0) x) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * (xs T - x T) := by
  rw [← euler_telescope U β a b xs x heul hx.1 T, ← sum_add_distrib]
  refine sum_le_sum fun t _ => ?_
  have h := concave_le_tangent hU (hx.2 t).2 (hxs t) (hUd t)
  have hb : 0 ≤ β ^ t := pow_nonneg hβ t
  nlinarith

/-- **Euler + transversality are sufficient** (non-stationary Theorem 4.15). Let `U` be concave
on `[0, ∞)`, `0 ≤ β`, and let the path `xs` have nonnegative consumption, satisfy the Euler
equation and the transversality condition `β^T b_T U′(c*_T) xs_T → 0`, with
`b_t U′(c*_t) ≥ 0`. Then no feasible path from `xs_0` has a larger value. -/
theorem euler_tvc_optimal {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') : S ≤ S' := by
  have key : ∀ T, ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * xs T := by
    intro T
    refine (euler_partial_sum_le hU hβ hUd hxs heul hx T).trans ?_
    have h1 : 0 ≤ β ^ T * (b T * deriv U (consPath a b xs T)) :=
      mul_nonneg (pow_nonneg hβ T) (hp T)
    have h2 := (hx.2 T).1
    nlinarith
  have hlim := hS'.tendsto_sum_nat.add htvc
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' hS.tendsto_sum_nat hlim key

/-- **Strict version.** If moreover `U` is strictly concave, `β > 0`, and the feasible path `x`
has a different consumption from `xs` at some date, then its value is strictly smaller. -/
theorem euler_tvc_strict {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S')
    {t₀ : ℕ} (ht₀ : consPath a b x t₀ ≠ consPath a b xs t₀) : S < S' := by
  set r : ℕ → ℝ := fun t => β ^ t * (U (consPath a b xs t) + deriv U (consPath a b xs t) *
    (consPath a b x t - consPath a b xs t) - U (consPath a b x t)) with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => by
    have h := concave_le_tangent hU.concaveOn (hx.2 t).2 (hxs t) (hUd t)
    exact mul_nonneg (pow_nonneg hβ.le t) (by linarith)
  have hrt₀ : 0 < r t₀ := by
    have h := strictConcave_lt_tangent hU (hx.2 t₀).2 (hxs t₀) ht₀ (hUd t₀)
    exact mul_pos (pow_pos hβ t₀) (by linarith)
  have key : ∀ T, t₀ < T → ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * xs T - r t₀ := by
    intro T hT
    have htel := euler_telescope U β a b xs x heul hx.1 T
    have hsum : ∑ t ∈ range T, β ^ t * U (consPath a b x t) =
        ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
          ∑ t ∈ range T, β ^ t * (deriv U (consPath a b xs t) *
            (consPath a b x t - consPath a b xs t)) - ∑ t ∈ range T, r t := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      simp only [hr]
      ring
    have hle : r t₀ ≤ ∑ t ∈ range T, r t :=
      single_le_sum (fun t _ => hr0 t) (mem_range.2 hT)
    have h1 : 0 ≤ β ^ T * (b T * deriv U (consPath a b xs T)) :=
      mul_nonneg (pow_nonneg hβ.le T) (hp T)
    have h2 := (hx.2 T).1
    rw [hsum, htel]
    nlinarith
  have hlim := (hS'.tendsto_sum_nat.add htvc).sub_const (r t₀)
  rw [add_zero] at hlim
  have hle : S ≤ S' - r t₀ :=
    le_of_tendsto_of_tendsto hS.tendsto_sum_nat hlim
      (eventually_atTop.2 ⟨t₀ + 1, fun T hT => key T (by omega)⟩)
  linarith

/-- **Uniqueness of the optimum.** Under the hypotheses of `euler_tvc_strict`, a feasible path
from `xs_0` whose value is at least that of `xs` coincides with `xs`. -/
theorem euler_tvc_unique {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') (hge : S' ≤ S) : x = xs := by
  have hc : ∀ t, consPath a b x t = consPath a b xs t := fun t => by
    by_contra h
    have := euler_tvc_strict hU hβ hUd hxs hp heul htvc hx hS hS' h
    linarith
  funext t
  induction t with
  | zero => exact hx.1
  | succ t ih =>
    have h := hc t
    simp only [consPath] at h
    rw [ih] at h
    linarith

/-- **The optimal value.** Under the hypotheses of `euler_tvc_optimal`, if `xs` is feasible from
`xs_0` with value `S'`, then `S'` is the greatest attainable value. -/
theorem euler_tvc_isGreatest {U : ℝ → ℝ} {β : ℝ} {a b xs : ℕ → ℝ} {S' : ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hfeas : IndivFeasible a b (xs 0) xs)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') :
    IsGreatest (indivValues U β a b (xs 0)) S' :=
  ⟨⟨xs, hfeas, hS'⟩, fun _ ⟨_, hx, hS⟩ =>
    euler_tvc_optimal hU hβ hUd (fun t => (hfeas.2 t).2) hp heul htvc hx hS hS'⟩

/-- **Transversality along bounded paths.** If `0 ≤ β < 1` and `z` is bounded, `β^t z_t → 0`;
e.g. `z_t = b_t U′(c_t) x_t` along a path converging to an interior steady state. -/
theorem tvc_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {z : ℕ → ℝ} {M : ℝ}
    (hz : ∀ t, |z t| ≤ M) : Tendsto (fun t => β ^ t * z t) atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  refine squeeze_zero_norm (fun t => ?_) (by simpa using hpow.mul_const M)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  exact mul_le_mul_of_nonneg_left (hz t) (pow_nonneg hβ0 t)

/-! ### Exercise 18.1 -/

/-- **Exercise 18.1** (p. 544). Let `U` be strictly concave on `[0, ∞)`, differentiable with
`U′ ≥ 0` there, `β > 0`, and let `k_{t+1} = g(k_t)` be a path with nonnegative capital and
consumption, `f′(k_t) ≥ 0`, satisfying the planner's Euler equation
`U′[f(k_t) − k_{t+1}] = β U′[f(k_{t+1}) − k_{t+2}] f′(k_{t+1})` and transversality condition
`β^t U′[f(k_t) − k_{t+1}] f′(k_t) k_t → 0`, with value `v = ∑ β^t U[f(k_t) − k_{t+1}]`.
For the individual with budget (2) given the aggregate path `k` (`a_t = f(k_t) − k_t f′(k_t)`,
`b_t = f′(k_t)`) starting from `x_0 = k_0`:
(i) the path `x = k` is feasible and its consumption is `f(k_t) − k_{t+1}`;
(ii) `v` is the greatest attainable value (`V(k_0, k_0; g) = v(k_0)`);
(iii) every optimal path equals `k`, so its first choice is `x_1 = g(k_0)`
(`G(k_0, k_0; g) = g(k_0)`). -/
theorem ex_18_1 {U f g : ℝ → ℝ} {β v : ℝ} {k : ℕ → ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hg : ∀ t, k (t + 1) = g (k t)) (hk : ∀ t, 0 ≤ k t) (hc : ∀ t, 0 ≤ f (k t) - k (t + 1))
    (hf' : ∀ t, 0 ≤ deriv f (k t))
    (heul : ∀ t, deriv U (f (k t) - k (t + 1)) =
      β * deriv U (f (k (t + 1)) - k (t + 2)) * deriv f (k (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * deriv U (f (k t) - k (t + 1)) * deriv f (k t) * k t)
      atTop (𝓝 0))
    (hv : HasSum (fun t => β ^ t * U (f (k t) - k (t + 1))) v) :
    (∀ t, consPath (fun t => f (k t) - k t * deriv f (k t)) (fun t => deriv f (k t)) k t =
        f (k t) - k (t + 1)) ∧
      IsGreatest (indivValues U β (fun t => f (k t) - k t * deriv f (k t))
        (fun t => deriv f (k t)) (k 0)) v ∧
      ∀ x S, IndivFeasible (fun t => f (k t) - k t * deriv f (k t)) (fun t => deriv f (k t))
          (k 0) x →
        HasSum (fun t => β ^ t * U (consPath (fun t => f (k t) - k t * deriv f (k t))
          (fun t => deriv f (k t)) x t)) S → v ≤ S → x = k ∧ x 1 = g (k 0) := by
  set a : ℕ → ℝ := fun t => f (k t) - k t * deriv f (k t) with ha
  set b : ℕ → ℝ := fun t => deriv f (k t) with hb
  have hcons : ∀ t, consPath a b k t = f (k t) - k (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have hfeas : IndivFeasible a b (k 0) k := ⟨rfl, fun t => ⟨hk t, (hcons t).symm ▸ hc t⟩⟩
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b k t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b k t) := fun t =>
    mul_nonneg (hf' t) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b k t) =
      β * b (t + 1) * deriv U (consPath a b k (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b k T) * k T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
    ring
  have hv' : HasSum (fun t => β ^ t * U (consPath a b k t)) v := by
    simpa only [hcons] using hv
  refine ⟨hcons, euler_tvc_isGreatest hU.concaveOn hβ.le hUd' hp heul' htvc' hfeas hv',
    fun x S hx hS hge => ?_⟩
  have hxk := euler_tvc_unique hU hβ hUd' (fun t => (hfeas.2 t).2) hp heul' htvc' hx hS hv' hge
  exact ⟨hxk, by rw [hxk, hg 0]⟩

/-! ### Capital-income tax with rebate: the pseudo-economy -/

/-- **Budget with rebate** (p. 545): wages `f(k) − k f′(k)`, after-tax capital income
`(1 − θ) x f′(k)` and the lump-sum rebate `θ k f′(k)` add up to
`f(k) + (1 − θ)(x − k) f′(k)`. -/
theorem budget_rebate (θ fk f'k x k : ℝ) :
    (fk - k * f'k) + (1 - θ) * x * f'k + θ * k * f'k = fk + (1 - θ) * (x - k) * f'k := by
  ring

/-- **Pseudo-economy** (p. 546). If `w′`, `ĥ` satisfy §18.1 (9)–(10),
`U′[f(k) − ĥ(k)] = β̂ w′[ĥ(k)]` and `w′(k) = f′(k) U′[f(k) − ĥ(k)]` with `β̂ = (1 − θ)β`, then
`φ = (1 − θ) w′` and `h = ĥ` satisfy §18.1 (6)–(7):
`U′[f(k) − h(k)] = β φ[h(k)]` and `φ(k) = (1 − θ) f′(k) U′[f(k) − h(k)]`. -/
theorem pseudo_economy_solves_6_7 {U' f f' w' hhat : ℝ → ℝ} {β θ : ℝ}
    (h9 : ∀ k, U' (f k - hhat k) = (1 - θ) * β * w' (hhat k))
    (h10 : ∀ k, w' k = f' k * U' (f k - hhat k)) :
    (∀ k, U' (f k - hhat k) = β * ((1 - θ) * w' (hhat k))) ∧
      ∀ k, (1 - θ) * w' k = (1 - θ) * f' k * U' (f k - hhat k) := by
  refine ⟨fun k => by rw [h9]; ring, fun k => by rw [h10]; ring⟩

/-- **The indirect method gives an equilibrium** (p. 546, with NOTE 18.1-C). Let the path `k`
(nonnegative capital and consumption, `f′(k_t) ≥ 0`) satisfy the Euler equation of the
pseudo-economy with discount factor `β̂ = (1 − θ)β`,
`U′[f(k_t) − k_{t+1}] = β̂ U′[f(k_{t+1}) − k_{t+2}] f′(k_{t+1})`, and the *individual's*
transversality condition `β^t (1 − θ) f′(k_t) U′[f(k_t) − k_{t+1}] k_t → 0`. Then for an
individual of the taxed economy (3) facing the aggregate path `k`, with `x_0 = k_0`, the path
`x = k` is the unique optimum (so `H(k, k; ĥ) = ĥ(k)`), with value `v`. -/
theorem indirect_equilibrium {U f : ℝ → ℝ} {β θ v : ℝ} {k : ℕ → ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β) (hθ : θ < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hk : ∀ t, 0 ≤ k t) (hc : ∀ t, 0 ≤ f (k t) - k (t + 1)) (hf' : ∀ t, 0 ≤ deriv f (k t))
    (heul : ∀ t, deriv U (f (k t) - k (t + 1)) =
      (1 - θ) * β * deriv U (f (k (t + 1)) - k (t + 2)) * deriv f (k (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (k t)) *
      deriv U (f (k t) - k (t + 1)) * k t) atTop (𝓝 0))
    (hv : HasSum (fun t => β ^ t * U (f (k t) - k (t + 1))) v) :
    IsGreatest (indivValues U β (fun t => f (k t) - (1 - θ) * k t * deriv f (k t))
        (fun t => (1 - θ) * deriv f (k t)) (k 0)) v ∧
      ∀ x S, IndivFeasible (fun t => f (k t) - (1 - θ) * k t * deriv f (k t))
          (fun t => (1 - θ) * deriv f (k t)) (k 0) x →
        HasSum (fun t => β ^ t * U (consPath (fun t => f (k t) - (1 - θ) * k t * deriv f (k t))
          (fun t => (1 - θ) * deriv f (k t)) x t)) S → v ≤ S → x = k := by
  set a : ℕ → ℝ := fun t => f (k t) - (1 - θ) * k t * deriv f (k t) with ha
  set b : ℕ → ℝ := fun t => (1 - θ) * deriv f (k t) with hb
  have hcons : ∀ t, consPath a b k t = f (k t) - k (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have hfeas : IndivFeasible a b (k 0) k := ⟨rfl, fun t => ⟨hk t, (hcons t).symm ▸ hc t⟩⟩
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b k t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b k t) := fun t =>
    mul_nonneg (mul_nonneg (by linarith) (hf' t)) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b k t) =
      β * b (t + 1) * deriv U (consPath a b k (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b k T) * k T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
  have hv' : HasSum (fun t => β ^ t * U (consPath a b k t)) v := by
    simpa only [hcons] using hv
  exact ⟨euler_tvc_isGreatest hU.concaveOn hβ.le hUd' hp heul' htvc' hfeas hv',
    fun x S hx hS hge => euler_tvc_unique hU hβ hUd' (fun t => (hfeas.2 t).2) hp heul' htvc' hx
      hS hv' hge⟩

/-- **The individual's transversality condition implies the pseudo-planner's** (NOTE 18.1-C):
if `β^t (1 − θ) z_t → 0` with `0 ≤ θ < 1` then `((1 − θ)β)^t z_t → 0`. -/
theorem tvc_indiv_imp_pseudo {β θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {z : ℕ → ℝ}
    (h : Tendsto (fun t => β ^ t * ((1 - θ) * z t)) atTop (𝓝 0)) :
    Tendsto (fun t => ((1 - θ) * β) ^ t * z t) atTop (𝓝 0) := by
  have hpos : 0 < 1 - θ := by linarith
  have hb : ∀ t, |(1 - θ) ^ t / (1 - θ)| ≤ 1 / (1 - θ) := fun t => by
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hpos.le t) hpos.le)]
    exact div_le_div_of_nonneg_right (pow_le_one₀ hpos.le (by linarith)) hpos.le
  refine squeeze_zero_norm (a := fun t => 1 / (1 - θ) * |β ^ t * ((1 - θ) * z t)|)
    (fun t => ?_) ?_
  · have e : ((1 - θ) * β) ^ t * z t = (1 - θ) ^ t / (1 - θ) * (β ^ t * ((1 - θ) * z t)) := by
      rw [mul_pow]
      field_simp
    rw [e, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
  · simpa using (h.abs).const_mul (1 / (1 - θ))

/-- **The converse fails** (NOTE 18.1-C): for `β ∈ (0, 1)`, `θ ∈ (0, 1)` the nonnegative
sequence `z_t = β^{−t}` has `((1 − θ)β)^t z_t → 0` but `β^t (1 − θ) z_t ↛ 0`; so the
pseudo-planner's transversality condition does not imply the individual's. -/
theorem tvc_pseudo_not_imp_indiv_counterexample {β θ : ℝ} (hβ : 0 < β) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ z : ℕ → ℝ, (∀ t, 0 ≤ z t) ∧ Tendsto (fun t => ((1 - θ) * β) ^ t * z t) atTop (𝓝 0) ∧
      ¬ Tendsto (fun t => β ^ t * ((1 - θ) * z t)) atTop (𝓝 0) := by
  refine ⟨fun t => (β ^ t)⁻¹, fun t => inv_nonneg.2 (pow_nonneg hβ.le t), ?_, ?_⟩
  · have e : (fun t : ℕ => ((1 - θ) * β) ^ t * (β ^ t)⁻¹) = fun t => (1 - θ) ^ t := by
      funext t
      rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero t hβ.ne'), mul_one]
    rw [e]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  · have e : (fun t : ℕ => β ^ t * ((1 - θ) * (β ^ t)⁻¹)) = fun _ => 1 - θ := by
      funext t
      field_simp
    rw [e]
    intro h
    have := tendsto_nhds_unique h tendsto_const_nhds
    linarith

/-! ### Exercise 18.2 -/

/-- **Exercise 18.2, budget** (manual p. 285). Wages taxed at `α`, capital income taxed at
`α + θ` (additive reading), rebate `θ k f′(k)`:
`(1 − α)[f(k) − k f′(k)] + (1 − α − θ) x f′(k) + θ k f′(k)
  = (1 − α) f(k) + (1 − α − θ)(x − k) f′(k)`. -/
theorem ex_18_2_budget (α θ fk f'k x k : ℝ) :
    (1 - α) * (fk - k * f'k) + (1 - α - θ) * x * f'k + θ * k * f'k =
      (1 - α) * fk + (1 - α - θ) * (x - k) * f'k := by
  ring

/-- **Exercise 18.2, first-order conditions.** Let `α < 1` and let `w′`, `ĥ` satisfy (9)–(10)
for the pseudo-economy with production function `F = (1 − α) f` and discount factor
`β̂ = β(1 − α − θ)/(1 − α)`. Then `h = ĥ` and `φ = [(1 − α − θ)/(1 − α)] w′` satisfy the
equilibrium conditions `U′[(1 − α) f(k) − h(k)] = β φ(h(k))` and
`φ(k) = (1 − α − θ) f′(k) U′[(1 − α) f(k) − h(k)]`. -/
theorem ex_18_2_foc {U' f f' w' hhat : ℝ → ℝ} {α β θ : ℝ} (hα : α < 1)
    (h9 : ∀ k, U' ((1 - α) * f k - hhat k) = β * (1 - α - θ) / (1 - α) * w' (hhat k))
    (h10 : ∀ k, w' k = (1 - α) * f' k * U' ((1 - α) * f k - hhat k)) :
    (∀ k, U' ((1 - α) * f k - hhat k) = β * ((1 - α - θ) / (1 - α) * w' (hhat k))) ∧
      ∀ k, (1 - α - θ) / (1 - α) * w' k = (1 - α - θ) * f' k * U' ((1 - α) * f k - hhat k) := by
  have hne : (1 - α) ≠ 0 := by linarith
  refine ⟨fun k => by rw [h9]; ring, fun k => ?_⟩
  rw [h10]
  field_simp

/-- **Exercise 18.2** (p. 547). Let `α < 1`, `α + θ ≤ 1`, and let the path `k` (nonnegative
capital and consumption, `f′(k_t) ≥ 0`) satisfy the Euler equation of the untaxed economy with
production function `F = (1 − α) f` and discount factor `β̂ = β(1 − α − θ)/(1 − α)`,
`U′[F(k_t) − k_{t+1}] = β̂ U′[F(k_{t+1}) − k_{t+2}] F′(k_{t+1})`, and the individual's
transversality condition. Then for an individual of the doubly taxed economy facing `k`, with
`x_0 = k_0`, the path `x = k` is the unique optimum, with value `v`. -/
theorem ex_18_2 {U f : ℝ → ℝ} {α β θ v : ℝ} {k : ℕ → ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β) (hα : α < 1) (hαθ : α + θ ≤ 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hk : ∀ t, 0 ≤ k t) (hc : ∀ t, 0 ≤ (1 - α) * f (k t) - k (t + 1))
    (hf' : ∀ t, 0 ≤ deriv f (k t))
    (heul : ∀ t, deriv U ((1 - α) * f (k t) - k (t + 1)) =
      β * (1 - α - θ) / (1 - α) * deriv U ((1 - α) * f (k (t + 1)) - k (t + 2)) *
        deriv (fun y => (1 - α) * f y) (k (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * ((1 - α - θ) * deriv f (k t)) *
      deriv U ((1 - α) * f (k t) - k (t + 1)) * k t) atTop (𝓝 0))
    (hv : HasSum (fun t => β ^ t * U ((1 - α) * f (k t) - k (t + 1))) v) :
    IsGreatest (indivValues U β (fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t))
        (fun t => (1 - α - θ) * deriv f (k t)) (k 0)) v ∧
      ∀ x S, IndivFeasible (fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t))
          (fun t => (1 - α - θ) * deriv f (k t)) (k 0) x →
        HasSum (fun t => β ^ t * U (consPath
          (fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t))
          (fun t => (1 - α - θ) * deriv f (k t)) x t)) S → v ≤ S → x = k := by
  set a : ℕ → ℝ := fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t) with ha
  set b : ℕ → ℝ := fun t => (1 - α - θ) * deriv f (k t) with hb
  have hne : (1 - α) ≠ 0 := by linarith
  have hcons : ∀ t, consPath a b k t = (1 - α) * f (k t) - k (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have hfeas : IndivFeasible a b (k 0) k := ⟨rfl, fun t => ⟨hk t, (hcons t).symm ▸ hc t⟩⟩
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b k t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b k t) := fun t =>
    mul_nonneg (mul_nonneg (by linarith) (hf' t)) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b k t) =
      β * b (t + 1) * deriv U (consPath a b k (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb, deriv_const_mul_field']
    field_simp
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b k T) * k T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
  have hv' : HasSum (fun t => β ^ t * U (consPath a b k t)) v := by
    simpa only [hcons] using hv
  exact ⟨euler_tvc_isGreatest hU.concaveOn hβ.le hUd' hp heul' htvc' hfeas hv',
    fun x S hx hS hge => euler_tvc_unique hU hβ hUd' (fun t => (hfeas.2 t).2) hp heul' htvc' hx
      hS hv' hge⟩

/-- **The manual's `β̂` is wrong** (NOTE 18.1-D). With the manual's value
`β̂ₘ = (1 − α − θ)/(1 − α)` in (9), the equilibrium condition `U′ = β φ(h)` with
`φ = [(1 − α − θ)/(1 − α)] w′` fails whenever `β < 1`, `α + θ < 1` and `w′(ĥ(k)) > 0`. -/
theorem ex_18_2_manual_counterexample {α β θ U'c w'h : ℝ} (hβ : β < 1) (hα : α < 1)
    (hαθ : α + θ < 1) (hw : 0 < w'h) (h9 : U'c = (1 - α - θ) / (1 - α) * w'h) :
    U'c ≠ β * ((1 - α - θ) / (1 - α) * w'h) := by
  have hc : 0 < (1 - α - θ) / (1 - α) := div_pos (by linarith) (by linarith)
  rw [h9]
  intro h
  have h1 : (1 - β) * ((1 - α - θ) / (1 - α) * w'h) = 0 := by linarith
  rcases mul_eq_zero.1 h1 with h2 | h2
  · linarith
  · exact (mul_pos hc hw).ne' h2

/-- **Exercise 18.2 needs `α + θ < 1`** (NOTE 18.1-E (i)): if `β > 0`, `α < 1` and
`α + θ ≥ 1`, then `β̂ = β(1 − α − θ)/(1 − α) ≤ 0`, not a discount factor. -/
theorem ex_18_2_requires_sum_lt_one {α β θ : ℝ} (hβ : 0 < β) (hα : α < 1) (hαθ : 1 ≤ α + θ) :
    β * (1 - α - θ) / (1 - α) ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
    (by linarith)

/-- **Sequential reading, budget** (NOTE 18.1-E (ii)): if the `θ`-tax is levied on capital
income net of the `α`-tax and its proceeds `θ(1 − α) k f′(k)` are rebated, the budget is
`(1 − α) f(k) + (1 − α)(1 − θ)(x − k) f′(k)`. -/
theorem ex_18_2_sequential_budget (α θ fk f'k x k : ℝ) :
    (1 - α) * (fk - k * f'k) + (1 - θ) * ((1 - α) * x * f'k) + θ * (1 - α) * k * f'k =
      (1 - α) * fk + (1 - α) * (1 - θ) * (x - k) * f'k := by
  ring

/-- **Sequential reading, Euler equation.** With after-tax return `(1 − α)(1 − θ) f′`, the
individual's Euler equation `U′(c_t) = β (1 − α)(1 − θ) f′(k_{t+1}) U′(c_{t+1})` is that of the
pseudo-economy with production function `F = (1 − α) f` and discount factor `β(1 − θ)`. -/
theorem ex_18_2_sequential_euler {α β θ U't U't1 f'k1 : ℝ} :
    U't = β * ((1 - α) * (1 - θ) * f'k1) * U't1 ↔
      U't = β * (1 - θ) * U't1 * ((1 - α) * f'k1) := by
  constructor <;> intro h <;> rw [h] <;> ring

/-- **The two readings differ** (NOTE 18.1-E (ii)): for `β > 0`, `0 < α < 1`, `θ > 0`,
`β(1 − θ) ≠ β(1 − α − θ)/(1 − α)`. -/
theorem ex_18_2_sequential_ne {α β θ : ℝ} (hβ : 0 < β) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : 0 < θ) : β * (1 - θ) ≠ β * (1 - α - θ) / (1 - α) := by
  have hne : (1 - α) ≠ 0 := by linarith
  intro h
  field_simp at h
  nlinarith [mul_pos hβ (mul_pos hα0 hθ)]

end StokeyLucasPrescott.EquilibriaWithDistortions
