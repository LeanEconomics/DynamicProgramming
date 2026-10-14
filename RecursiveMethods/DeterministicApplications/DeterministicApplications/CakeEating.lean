/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.GrowthDifferentiability
import DeterministicApplications.LogModel

/-!
# A cake-eating problem

SLP §5.2, p. 105: the model of Section 5.1 with `f(k) = k`.

* `ex_5_2a_technology`, `ex_5_2a_not_T2`, `ex_5_2a`: `f(k) = k` satisfies (T1) and (T3)–(T5),
  but not the second half of (T2); any `x̄ > 0` defines `X = [0, x̄]`, because `[0, x̄]` is
  invariant (`GrowthHyp U id β x̄` holds), and feasible paths only fall (`cake_path_le`).
* `ex_5_2b`: for `U = ln`, `v(x) = ln x/(1 − β) + [ln(1 − β) + β ln β/(1 − β)]/(1 − β)`, and the
  policy `g(x) = βx` generates the optimal plan. This is the case `α = 1` of the unit-elastic
  model (`LogModel`), with state space `(0, ∞)` and `Γ(x) = (0, x)`.
* `ex_5_2c`: in general, on `[0, x̄]`, `v` is the supremum function, strictly increasing and
  strictly concave, and the policy is a continuous function (Exercise 5.1 with a weakly concave
  `f`, `ex_5_1c_weak`); under the Inada condition consumption and saving are both positive, and
  `v'(x) = U'(x − g(x))`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {U : ℝ → ℝ} {β xbar : ℝ}

/-- **Exercise 5.2a.** `f(k) = k` satisfies (T1) and (T3)–(T5). -/
theorem ex_5_2a_technology :
    Continuous (id : ℝ → ℝ) ∧ StrictMono (id : ℝ → ℝ) ∧ ConcaveOn ℝ (Ici 0) (id : ℝ → ℝ) ∧
      ContDiff ℝ 1 (id : ℝ → ℝ) :=
  ⟨continuous_id, strictMono_id, concaveOn_id (convex_Ici 0), contDiff_id⟩

/-- **Exercise 5.2a.** `f(k) = k` fails the second half of (T2): there is no `x̄` beyond which
`f(x) < x`. -/
theorem ex_5_2a_not_T2 : ¬ ∃ xbar : ℝ, ∀ x, xbar < x → (id : ℝ → ℝ) x < x := by
  rintro ⟨xbar, h⟩
  exact lt_irrefl _ (h (xbar + 1) (by linarith))

/-- **Exercise 5.2a.** Any `x̄ > 0` can be used to define `X`: (U1)–(U3) give the hypotheses of
Section 5.1 with `f(k) = k` on `[0, x̄]`. -/
theorem ex_5_2a (hβ0 : 0 < β) (hβ1 : β < 1) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) (hx : 0 < xbar) : GrowthHyp U id β xbar :=
  ⟨hβ0, hβ1, hUc, hUm, continuous_id.continuousOn, rfl, hx,
    fun _ hx' => ⟨le_rfl, hx'.2⟩, strictMono_id.strictMonoOn _⟩

/-- Feasible cake paths fall: `x_t ≤ x₀`, so `[0, x₀]` contains the whole path. -/
theorem cake_path_le {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) ≤ x t) (t : ℕ) : x t ≤ x 0 := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (hx t).trans ih

/-- `Γ(x) = (0, x)` when `α = 1`. -/
theorem cake_logΓ (k : PosR) : logΓ 1 k = {y | y.1 < k.1} := by
  ext y; simp [logΓ, Real.rpow_one]

/-- `F(x, y) = ln(x − y)` when `α = 1`. -/
theorem cake_logF (k y : PosR) : logF 1 k y = Real.log (k.1 - y.1) := by
  simp [logF, Real.rpow_one]

/-- The policy `g(x) = βx` (`αβk^α` with `α = 1`). -/
theorem cake_policy (hβ0 : 0 < β) (k : PosR) : (logPolicy 1 β one_pos hβ0 k).1 = β * k.1 := by
  simp [logPolicy, Real.rpow_one]

/-- **Exercise 5.2b.** With `U = ln`,
`v(x) = ln x/(1 − β) + [ln(1 − β) + β ln β/(1 − β)]/(1 − β)`. -/
theorem ex_5_2b (hβ0 : 0 < β) (hβ1 : β < 1) :
    vstar (logΓ 1) (logF 1) β = fun k : PosR =>
      (((Real.log (1 - β) + β / (1 - β) * Real.log β) / (1 - β) +
        Real.log k.1 / (1 - β) : ℝ) : EReal) := by
  rw [log_vstar one_pos le_rfl hβ0 hβ1]
  funext k
  simp only [affineLog, coefB, coefC, one_mul]
  congr 1
  ring

/-- **Exercise 5.2b.** The policy `g(x) = βx` generates an optimal plan. -/
theorem ex_5_2b_policy (hβ0 : 0 < β) (hβ1 : β < 1) (k₀ : PosR) :
    total (logF 1) β (fun t => (logPolicy 1 β one_pos hβ0)^[t] k₀) =
      vstar (logΓ 1) (logF 1) β k₀ :=
  log_policy_optimal one_pos le_rfl hβ0 hβ1 k₀

/-- **Exercise 5.2c.** For any `U` satisfying (U1)–(U4), on `[0, x̄]`: `v` is the supremum
function, strictly increasing and strictly concave, and the policy is a continuous function. -/
theorem ex_5_2c [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U id β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    (fun x => (v x : EReal)) = vstar (growthΓ id xbar) (curryF (growthF U id xbar)) β ∧
      StrictMono v ∧ IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ id xbar) (obj (growthF U id xbar) β v) ∧
      Continuous (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v)) := by
  obtain ⟨u, -, huniq, hvs, hmono, -⟩ := ex_5_1ab h
  have hvu := huniq v hv
  subst hvu
  obtain ⟨h1, h2, h3⟩ := ex_5_1c_weak h hU (concaveOn_id (convex_Ici 0)) hv
  exact ⟨hvs, hmono, h1, h2, h3⟩

/-- **Exercise 5.2c.** Under the Inada condition `U'(0+) = ∞`, for `x > 0` the cake is neither
eaten at once nor left untouched: `0 < g(x) < x`. -/
theorem ex_5_2c_interior [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U id β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hinada : Tendsto (deriv U) (𝓝[>] 0) atTop) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    {x : Icc (0 : ℝ) xbar} (hx : 0 < x.1) :
    0 < (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v) x).1 ∧
      (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v) x).1 < x.1 :=
  ex_5_1d_interior h hU (concaveOn_id (convex_Ici 0)) hUd hinada hv hx

/-- **Exercise 5.2c.** Where saving is interior, `v'(x) = U'(x − g(x))`. -/
theorem ex_5_2c_deriv [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U id β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x₀ : Icc (0 : ℝ) xbar}
    (hx₀ : x₀.1 ∈ Ioo 0 xbar)
    (hgf : (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v) x₀).1 < x₀.1) {U' : ℝ}
    (hU' : HasDerivAt U U' (x₀.1 - (argmaxFn (growthΓ id xbar)
      (obj (growthF U id xbar) β v) x₀).1)) :
    HasDerivAt (liftR xbar v) U' x₀.1 := by
  have := ex_5_1d h hU (concaveOn_id (convex_Ici 0)) hv hx₀ hgf hU' (hasDerivAt_id x₀.1)
  simpa using this

end StokeyLucasPrescott.DeterministicApplications
