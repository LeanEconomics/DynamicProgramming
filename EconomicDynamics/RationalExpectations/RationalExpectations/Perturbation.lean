/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Basics
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Nonlinear rational expectations models: the perturbation method

Miao, §2.4, pp. 64–69: the nonlinear model (2.27) `E_t f(y_{t+1}, y_t, x_{t+1}, x_t) = 0` and
the second-order perturbation method of Schmitt-Grohé and Uribe. Following the book ("we
consider the scalar case only"), `x`, `y`, `σ` are real; `f : ℝ⁴ → ℝ` is one equation (the
`2 × 2` systems are in `PerturbationSystem`), with arguments ordered `(y', y, x', x)`.

* Partial derivatives: `pertP f j v` (`j = 0, 1, 2, 3` for `y', y, x', x`), `pertDx`, `pertDs`
  (Fréchet derivative applied to a coordinate direction); `f_{jk} = pertP (pertP f j) k`, the
  derivative of `f_j` in direction `k`; `pertRow` is the bracket `[f_{jy'}w₁ + … + f_{jx}w₄]`.
* The chain rule along curves (`pert_hasDerivAt_two`, `pert_hasDerivAt_four`), and along the
  policy (2.29) `y = g(x, σ)`, `x' = h(x, σ) + ησε'` (`pertPsi`, `pertPhi`, `pert_psi_x`, …).
* `pertF`: `F(x, σ)` of (2.30); `pertF_Dx`, `pertF_Ds` (first partials at every point).
* At the steady state (`pertPsi_ss`, `pertPhi_ss`): `eq_F_x` (p. 68), `eq_F_sigma_E` (the first
  printed line for `F_σ`, with `ε'` terms) and `eq_F_sigma` (the second; the `ε'` terms vanish
  since `Eε' = 0`), `eq_F_xx` (p. 68), `eq_F_sigma_x` and `eq_F_sigma_sigma` (p. 69), all
  computed by the chain rule.

**Departures.** The shock has a finite distribution (`IsFiniteShock`: values `ε i` with weights
`p i ≥ 0`, `∑ p i = 1`, `∑ p i ε i = 0`), so `E` is a finite sum; the book has "IID with bounded
support". `f`, `g`, `h` are `C²` on all of `ℝ⁴`, `ℝ²`. The existence and smoothness of the policy
functions `g`, `h` is an assumption of the method (not proved in the book, nor here).

**Corrections.**
* `F_xx` (p. 68): the first term of the display is printed `f_{y'y}g_xh_x`; it is
  `f_{y'y'}g_xh_x` (`eq_F_xx`; counterexample `eq_F_xx_printed_false`).
* `F_σσ` (p. 69): the printed `I` must be `E[ε'²]` (the book does not normalise the variance);
  the display (and `F_σx`) also uses `g_σ = h_σ = 0`, which `eq_F_sigma_sigma` and
  `eq_F_sigma_x` take as hypotheses (`eq_F_sigma_sigma_printed_false`).
-/

namespace Miao.RationalExpectations

/-! ### Partial derivatives -/

/-- The coordinate directions of `(y', y, x', x) ∈ ℝ⁴` (the argument order of `f` in (2.27)). -/
def pertE4 : Fin 4 → ℝ × ℝ × ℝ × ℝ :=
  ![(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]

/-- The partial derivative `∂f/∂v_j` of `f : ℝ⁴ → ℝ` at `v` (`j = 0, 1, 2, 3` for
`y', y, x', x`): `f_{y'} = pertP f 0`, and `f_{jk} = pertP (pertP f j) k` is the derivative of
`f_j` in the direction `k`. -/
noncomputable def pertP (f : ℝ × ℝ × ℝ × ℝ → ℝ) (j : Fin 4) (v : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ f v (pertE4 j)

/-- The partial derivative `G_x` of `G(x, σ)`. -/
noncomputable def pertDx (G : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := fderiv ℝ G q (1, 0)

/-- The partial derivative `G_σ` of `G(x, σ)`. -/
noncomputable def pertDs (G : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := fderiv ℝ G q (0, 1)

/-- The chain rule along a curve in `ℝ²`. -/
theorem pert_hasDerivAt_two {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) {a b : ℝ → ℝ}
    {a' b' t : ℝ} (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => G (a s, b s)) (pertDx G (a t, b t) * a' + pertDs G (a t, b t) * b') t := by
  have := (hG (a t, b t)).hasFDerivAt.comp_hasDerivAt t (ha.prodMk hb)
  refine this.congr_deriv ?_
  have e : ((a', b') : ℝ × ℝ) = a' • ((1, 0) : ℝ × ℝ) + b' • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, pertDx, pertDs]
  ring

/-- The chain rule along a curve in `ℝ⁴`. -/
theorem pert_hasDerivAt_four {K : ℝ × ℝ × ℝ × ℝ → ℝ} (hK : Differentiable ℝ K)
    {a b c d : ℝ → ℝ} {a' b' c' d' t : ℝ} (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t)
    (hc : HasDerivAt c c' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun s => K (a s, b s, c s, d s))
      (pertP K 0 (a t, b t, c t, d t) * a' + pertP K 1 (a t, b t, c t, d t) * b' +
        pertP K 2 (a t, b t, c t, d t) * c' + pertP K 3 (a t, b t, c t, d t) * d') t := by
  have := (hK (a t, b t, c t, d t)).hasFDerivAt.comp_hasDerivAt t
    (ha.prodMk (hb.prodMk (hc.prodMk hd)))
  refine this.congr_deriv ?_
  have e : ((a', b', c', d') : ℝ × ℝ × ℝ × ℝ) =
      a' • pertE4 0 + b' • pertE4 1 + c' • pertE4 2 + d' • pertE4 3 := by
    ext <;> simp [pertE4]
  rw [e, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, pertP, pertP, pertP, pertP]
  ring

/-- Along the `x`-line. -/
theorem pert_line_x {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (x σ : ℝ) :
    HasDerivAt (fun t => G (t, σ)) (pertDx G (x, σ)) x :=
  (pert_hasDerivAt_two hG (hasDerivAt_id x) (hasDerivAt_const x σ)).congr_deriv (by
    simp only [id, mul_one, mul_zero, add_zero])

/-- Along the `σ`-line. -/
theorem pert_line_s {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (x σ : ℝ) :
    HasDerivAt (fun s => G (x, s)) (pertDs G (x, σ)) σ :=
  (pert_hasDerivAt_two hG (hasDerivAt_const σ x) (hasDerivAt_id σ)).congr_deriv (by
    simp only [id, mul_one, mul_zero, zero_add])

/-- A partial derivative `G_x` is the derivative along the `x`-line. -/
theorem pert_Dx_eq {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) {x σ d : ℝ}
    (h : HasDerivAt (fun t => G (t, σ)) d x) : pertDx G (x, σ) = d :=
  (pert_line_x hG x σ).unique h

/-- A partial derivative `G_σ` is the derivative along the `σ`-line. -/
theorem pert_Ds_eq {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) {x σ d : ℝ}
    (h : HasDerivAt (fun s => G (x, s)) d σ) : pertDs G (x, σ) = d :=
  (pert_line_s hG x σ).unique h

/-- The partial derivatives of a `C²` function are differentiable. -/
theorem pert_diff_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ 2 G) (w : E) : Differentiable ℝ fun q => fderiv ℝ G q w :=
  ((hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
    (by norm_num)

/-! ### The policy functions and `F` of (2.30) -/

/-- The argument `(h(x, σ) + ησε', σ)` of `g` in `g(x', σ)` (Miao, (2.29)–(2.30)). -/
def pertPsi (h : ℝ × ℝ → ℝ) (η e : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (h q + η * q.2 * e, q.2)

/-- `(y', y, x', x)` under the policy (2.29) when `ε' = e`:
`(g(h(x, σ) + ησe, σ), g(x, σ), h(x, σ) + ησe, x)`. -/
def pertPhi (g h : ℝ × ℝ → ℝ) (η e : ℝ) (q : ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (g (pertPsi h η e q), g q, h q + η * q.2 * e, q.1)

/-- `F(x, σ) = E f(g(h(x, σ) + ησε', σ), g(x, σ), h(x, σ) + ησε', x)` (Miao, (2.30)), for a shock
`ε'` taking the value `ε i` with probability `p i`. -/
def pertF (f : ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ)
    (q : ℝ × ℝ) : ℝ :=
  ∑ i, p i * f (pertPhi g h η (ε i) q)

theorem pert_psi_x {G h : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (hh : Differentiable ℝ h)
    (η e x σ : ℝ) :
    HasDerivAt (fun t => G (pertPsi h η e (t, σ)))
      (pertDx G (pertPsi h η e (x, σ)) * pertDx h (x, σ)) x := by
  have ha : HasDerivAt (fun t => h (t, σ) + η * σ * e) (pertDx h (x, σ)) x :=
    (pert_line_x hh x σ).add_const _
  exact (pert_hasDerivAt_two hG ha (hasDerivAt_const x σ)).congr_deriv (by
    simp only [mul_zero, add_zero]; rfl)

theorem pert_psi_s {G h : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (hh : Differentiable ℝ h)
    (η e x σ : ℝ) :
    HasDerivAt (fun s => G (pertPsi h η e (x, s)))
      (pertDx G (pertPsi h η e (x, σ)) * (pertDs h (x, σ) + η * e) +
        pertDs G (pertPsi h η e (x, σ))) σ := by
  have ha : HasDerivAt (fun s => h (x, s) + η * s * e) (pertDs h (x, σ) + η * e) σ := by
    refine (pert_line_s hh x σ).add ?_
    simpa using ((hasDerivAt_id σ).const_mul η).mul_const e
  exact (pert_hasDerivAt_two hG ha (hasDerivAt_id σ)).congr_deriv (by
    simp only [id, mul_one]; rfl)

theorem pert_phi_x {K : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hK : Differentiable ℝ K)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (η e x σ : ℝ) :
    HasDerivAt (fun t => K (pertPhi g h η e (t, σ)))
      (pertP K 0 (pertPhi g h η e (x, σ)) * (pertDx g (pertPsi h η e (x, σ)) * pertDx h (x, σ)) +
        pertP K 1 (pertPhi g h η e (x, σ)) * pertDx g (x, σ) +
        pertP K 2 (pertPhi g h η e (x, σ)) * pertDx h (x, σ) +
        pertP K 3 (pertPhi g h η e (x, σ))) x := by
  have hc : HasDerivAt (fun t => h (t, σ) + η * σ * e) (pertDx h (x, σ)) x :=
    (pert_line_x hh x σ).add_const _
  exact (pert_hasDerivAt_four hK (pert_psi_x hg hh η e x σ) (pert_line_x hg x σ) hc
    (hasDerivAt_id x)).congr_deriv (by simp only [mul_one]; rfl)

theorem pert_phi_s {K : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hK : Differentiable ℝ K)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (η e x σ : ℝ) :
    HasDerivAt (fun s => K (pertPhi g h η e (x, s)))
      (pertP K 0 (pertPhi g h η e (x, σ)) * (pertDx g (pertPsi h η e (x, σ)) *
          (pertDs h (x, σ) + η * e) + pertDs g (pertPsi h η e (x, σ))) +
        pertP K 1 (pertPhi g h η e (x, σ)) * pertDs g (x, σ) +
        pertP K 2 (pertPhi g h η e (x, σ)) * (pertDs h (x, σ) + η * e)) σ := by
  have hc : HasDerivAt (fun s => h (x, s) + η * s * e) (pertDs h (x, σ) + η * e) σ := by
    refine (pert_line_s hh x σ).add ?_
    simpa using ((hasDerivAt_id σ).const_mul η).mul_const e
  exact (pert_hasDerivAt_four hK (pert_psi_s hg hh η e x σ) (pert_line_s hg x σ) hc
    (hasDerivAt_const σ x)).congr_deriv (by simp only [mul_zero, add_zero]; rfl)

theorem pertF_contDiff {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) :
    ContDiff ℝ 2 (pertF f g h η p ε) := by
  unfold pertF pertPhi pertPsi
  fun_prop

/-- A shock `ε'` with a finite distribution: value `ε i` with probability `p i`, mean zero
(Miao, p. 66: "IID with bounded support"; here finitely supported). -/
structure IsFiniteShock {N : ℕ} (p ε : Fin N → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1
  mean_zero : ∑ i, p i * ε i = 0

theorem pert_sum_lin {N : ℕ} {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {φ : Fin N → ℝ}
    {A : ℝ} (B : ℝ) (hφ : ∀ i, φ i = A + B * ε i) : ∑ i, p i * φ i = A := by
  simp only [hφ, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hp.sum_one, one_mul,
    show ∑ i, p i * (B * ε i) = B * ∑ i, p i * ε i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    hp.mean_zero, mul_zero, add_zero]

theorem pert_sum_quad {N : ℕ} {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {φ : Fin N → ℝ}
    (A B C : ℝ) (hφ : ∀ i, φ i = A + B * ε i + C * ε i ^ 2) :
    ∑ i, p i * φ i = A + C * ∑ i, p i * ε i ^ 2 := by
  have e : ∀ i, p i * φ i = p i * (A + B * ε i) + C * (p i * ε i ^ 2) := fun i => by
    rw [hφ]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [pert_sum_lin hp B fun i => rfl]

/-- At the deterministic steady state, `(h(x̄, 0) + η·0·e, 0) = (x̄, 0)`. -/
theorem pertPsi_ss {h : ℝ × ℝ → ℝ} {xb : ℝ} (hx : h (xb, 0) = xb) (η e : ℝ) :
    pertPsi h η e (xb, 0) = (xb, 0) := by
  simp [pertPsi, hx]

/-- At the deterministic steady state, `Φ(x̄, 0) = (ȳ, ȳ, x̄, x̄)`. -/
theorem pertPhi_ss {g h : ℝ × ℝ → ℝ} {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (η e : ℝ) : pertPhi g h η e (xb, 0) = (yb, yb, xb, xb) := by
  simp [pertPhi, pertPsi_ss hx, hx, hy]

/-- `F_x(x, σ)` by the chain rule, at every `(x, σ)`. -/
theorem pertF_Dx {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) (x σ : ℝ) :
    pertDx (pertF f g h η p ε) (x, σ) = ∑ i, p i *
      (pertP f 0 (pertPhi g h η (ε i) (x, σ)) *
          (pertDx g (pertPsi h η (ε i) (x, σ)) * pertDx h (x, σ)) +
        pertP f 1 (pertPhi g h η (ε i) (x, σ)) * pertDx g (x, σ) +
        pertP f 2 (pertPhi g h η (ε i) (x, σ)) * pertDx h (x, σ) +
        pertP f 3 (pertPhi g h η (ε i) (x, σ))) :=
  pert_Dx_eq ((pertF_contDiff hf hg hh η p ε).differentiable (by norm_num))
    (HasDerivAt.fun_sum fun i _ => (pert_phi_x (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) (hh.differentiable (by norm_num)) η (ε i) x σ).const_mul
        (p i))

/-- `F_σ(x, σ)` by the chain rule, at every `(x, σ)`. -/
theorem pertF_Ds {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) (x σ : ℝ) :
    pertDs (pertF f g h η p ε) (x, σ) = ∑ i, p i *
      (pertP f 0 (pertPhi g h η (ε i) (x, σ)) * (pertDx g (pertPsi h η (ε i) (x, σ)) *
          (pertDs h (x, σ) + η * ε i) + pertDs g (pertPsi h η (ε i) (x, σ))) +
        pertP f 1 (pertPhi g h η (ε i) (x, σ)) * pertDs g (x, σ) +
        pertP f 2 (pertPhi g h η (ε i) (x, σ)) * (pertDs h (x, σ) + η * ε i)) :=
  pert_Ds_eq ((pertF_contDiff hf hg hh η p ε).differentiable (by norm_num))
    (HasDerivAt.fun_sum fun i _ => (pert_phi_s (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) (hh.differentiable (by norm_num)) η (ε i) x σ).const_mul
        (p i))

/-- Miao, p. 68: `F_x(x̄, 0) = f_{y'}g_xh_x + f_yg_x + f_{x'}h_x + f_x` (as printed), all
derivatives at the steady state. -/
theorem eq_F_x {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertF f g h η p ε) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDx h (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDx g (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDx h (xb, 0) + pertP f 3 (yb, yb, xb, xb) := by
  rw [pertF_Dx hf hg hh]
  simp only [pertPsi_ss hx, pertPhi_ss hx hy]
  exact pert_sum_lin hp 0 fun i => by ring

/-- Miao, p. 67: `F_σ(x̄, 0) = E{f_{y'}[g_x(h_σ + ηε') + g_σ] + f_yg_σ + f_{x'}(h_σ + ηε')}`
(the first printed line, with `E` the finite sum over the values of `ε'`). -/
theorem eq_F_sigma_E {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDs (pertF f g h η p ε) (xb, 0) = ∑ i, p i *
      (pertP f 0 (yb, yb, xb, xb) * (pertDx g (xb, 0) * (pertDs h (xb, 0) + η * ε i) +
          pertDs g (xb, 0)) + pertP f 1 (yb, yb, xb, xb) * pertDs g (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * (pertDs h (xb, 0) + η * ε i)) := by
  rw [pertF_Ds hf hg hh]
  simp only [pertPsi_ss hx, pertPhi_ss hx hy]

/-- Miao, p. 67: `F_σ(x̄, 0) = f_{y'}[g_xh_σ + g_σ] + f_yg_σ + f_{x'}h_σ` (the second printed
line): the `ε'` terms of the first line vanish because `Eε' = 0`. -/
theorem eq_F_sigma {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDs (pertF f g h η p ε) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * (pertDx g (xb, 0) * pertDs h (xb, 0) + pertDs g (xb, 0)) +
        pertP f 1 (yb, yb, xb, xb) * pertDs g (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDs h (xb, 0) := by
  rw [eq_F_sigma_E hf hg hh η p ε hx hy]
  exact pert_sum_lin hp (pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * η +
    pertP f 2 (yb, yb, xb, xb) * η) fun i => by ring

/-- The bracket `[f_{jy'}w₁ + f_{jy}w₂ + f_{jx'}w₃ + f_{jx}w₄]` of the printed second-order
displays (Miao, p. 68): the derivative of `f_j` in the direction `w`, at `v`. -/
noncomputable def pertRow (f : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (j : Fin 4)
    (w₁ w₂ w₃ w₄ : ℝ) : ℝ :=
  pertP (pertP f j) 0 v * w₁ + pertP (pertP f j) 1 v * w₂ + pertP (pertP f j) 2 v * w₃ +
    pertP (pertP f j) 3 v * w₄

/-- Miao, p. 68, `F_xx(x̄, 0)`, computed by the chain rule. With `w = (g_xh_x, g_x, h_x, 1)` and
`S = (ȳ, ȳ, x̄, x̄)`:
`F_xx = [f_{y'y'}g_xh_x + f_{y'y}g_x + f_{y'x'}h_x + f_{y'x}]g_xh_x + f_{y'}g_xxh_xh_x +
f_{y'}g_xh_xx + [f_{yy'}g_xh_x + …]g_x + f_yg_xx + [f_{x'y'}g_xh_x + …]h_x + f_{x'}h_xx +
f_{xy'}g_xh_x + f_{xy}g_x + f_{xx'}h_x + f_{xx}`.
This is the printed display except for its first term, printed `f_{y'y}g_xh_x`: it must be
`f_{y'y'}g_xh_x` (`eq_F_xx_printed_false`). -/
theorem eq_F_xx {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertDx (pertF f g h η p ε)) (xb, 0) =
      pertRow f (yb, yb, xb, xb) 0 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 * (pertDx g (xb, 0) * pertDx h (xb, 0)) +
        pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) * pertDx h (xb, 0) *
          pertDx h (xb, 0) +
        pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDx (pertDx h) (xb, 0) +
        pertRow f (yb, yb, xb, xb) 1 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 * pertDx g (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) +
        pertRow f (yb, yb, xb, xb) 2 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 * pertDx h (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDx (pertDx h) (xb, 0) +
        pertRow f (yb, yb, xb, xb) 3 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 := by
  have hg' := hg.differentiable (by norm_num)
  have hh' := hh.differentiable (by norm_num)
  have hfj : ∀ j, Differentiable ℝ (pertP f j) := fun j => pert_diff_fderiv hf (pertE4 j)
  have hgx : Differentiable ℝ (pertDx g) := pert_diff_fderiv hg _
  have hhx : Differentiable ℝ (pertDx h) := pert_diff_fderiv hh _
  have hDF : Differentiable ℝ (pertDx (pertF f g h η p ε)) :=
    pert_diff_fderiv (pertF_contDiff hf hg hh η p ε) _
  have key := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((((pert_phi_x (hfj 0) hg' hh' η (ε i) xb 0).mul
      ((pert_psi_x hgx hh' η (ε i) xb 0).mul (pert_line_x hhx xb 0))).add
      ((pert_phi_x (hfj 1) hg' hh' η (ε i) xb 0).mul (pert_line_x hgx xb 0))).add
      ((pert_phi_x (hfj 2) hg' hh' η (ε i) xb 0).mul (pert_line_x hhx xb 0))).add
      (pert_phi_x (hfj 3) hg' hh' η (ε i) xb 0)).const_mul (p i)
  rw [pert_Dx_eq hDF (key.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => pertF_Dx hf hg hh η p ε t 0))]
  simp only [Pi.mul_apply, pertPsi_ss hx, pertPhi_ss hx hy]
  refine pert_sum_lin hp 0 fun i => ?_
  simp only [pertRow]
  ring

/-- Miao, p. 69, `F_σx(x̄, 0)`, given `g_σ = h_σ = 0` (which the book has established at this
point, `theorem_g_sigma_zero`): `F_σx = f_{y'}g_xh_σx + f_{y'}g_σxh_x + f_yg_σx + f_{x'}h_σx`,
as printed (`g_σx`, `h_σx` are the `σ`-derivatives of `g_x`, `h_x`). The `D²f` terms and the
`g_xx` term carry a factor `ε'` and vanish in expectation. Without `g_σ = h_σ = 0` there are
further, inhomogeneous terms (e.g. `f_{y'}g_xxh_σh_x`). -/
theorem eq_F_sigma_x {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDx (pertF f g h η p ε)) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDs (pertDx h) (xb, 0) +
        pertP f 0 (yb, yb, xb, xb) * pertDs (pertDx g) (xb, 0) * pertDx h (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDs (pertDx g) (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDs (pertDx h) (xb, 0) := by
  have hg' := hg.differentiable (by norm_num)
  have hh' := hh.differentiable (by norm_num)
  have hfj : ∀ j, Differentiable ℝ (pertP f j) := fun j => pert_diff_fderiv hf (pertE4 j)
  have hgx : Differentiable ℝ (pertDx g) := pert_diff_fderiv hg _
  have hhx : Differentiable ℝ (pertDx h) := pert_diff_fderiv hh _
  have hDF : Differentiable ℝ (pertDx (pertF f g h η p ε)) :=
    pert_diff_fderiv (pertF_contDiff hf hg hh η p ε) _
  have key := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((((pert_phi_s (hfj 0) hg' hh' η (ε i) xb 0).mul
      ((pert_psi_s hgx hh' η (ε i) xb 0).mul (pert_line_s hhx xb 0))).add
      ((pert_phi_s (hfj 1) hg' hh' η (ε i) xb 0).mul (pert_line_s hgx xb 0))).add
      ((pert_phi_s (hfj 2) hg' hh' η (ε i) xb 0).mul (pert_line_s hhx xb 0))).add
      (pert_phi_s (hfj 3) hg' hh' η (ε i) xb 0)).const_mul (p i)
  rw [pert_Ds_eq hDF (key.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => pertF_Dx hf hg hh η p ε xb s))]
  simp only [Pi.mul_apply, pertPsi_ss hx, pertPhi_ss hx hy, hgs, hhs]
  refine pert_sum_lin hp
    (η * (pertRow f (yb, yb, xb, xb) 0 (pertDx g (xb, 0)) 0 1 0 * pertDx g (xb, 0) *
        pertDx h (xb, 0) + pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) *
        pertDx h (xb, 0) + pertRow f (yb, yb, xb, xb) 1 (pertDx g (xb, 0)) 0 1 0 *
        pertDx g (xb, 0) + pertRow f (yb, yb, xb, xb) 2 (pertDx g (xb, 0)) 0 1 0 *
        pertDx h (xb, 0) + pertRow f (yb, yb, xb, xb) 3 (pertDx g (xb, 0)) 0 1 0)) fun i => ?_
  simp only [pertRow]
  ring

/-- Miao, p. 69, `F_σσ(x̄, 0)`, given `g_σ = h_σ = 0`:
`F_σσ = f_{y'}g_xh_σσ + f_{y'y'}g_xηg_xηE[ε'²] + f_{y'x'}ηg_xηE[ε'²] + f_{y'}g_xxηηE[ε'²] +
f_{y'}g_σσ + f_yg_σσ + f_{x'}h_σσ + f_{x'y'}g_xηηE[ε'²] + f_{x'x'}ηηE[ε'²]`.
The printed display has `I` where `E[ε'²]` stands: the book never normalises the shock variance
(`ε` is only "IID with bounded support"), so the printed formula holds only when `E[ε'²] = 1`
(`eq_F_sigma_sigma_printed_false`). The cross terms `f_{y'}(g_σx + g_xσ)ηε'` vanish in
expectation. -/
theorem eq_F_sigma_sigma {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDs (pertF f g h η p ε)) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDs (pertDs h) (xb, 0) +
        pertP (pertP f 0) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * η * pertDx g (xb, 0) * η *
          ∑ i, p i * ε i ^ 2 +
        pertP (pertP f 0) 2 (yb, yb, xb, xb) * η * pertDx g (xb, 0) * η * ∑ i, p i * ε i ^ 2 +
        pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) * η * η * ∑ i, p i * ε i ^ 2 +
        pertP f 0 (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDs (pertDs h) (xb, 0) +
        pertP (pertP f 2) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * η * η * ∑ i, p i * ε i ^ 2 +
        pertP (pertP f 2) 2 (yb, yb, xb, xb) * η * η * ∑ i, p i * ε i ^ 2 := by
  have hg' := hg.differentiable (by norm_num)
  have hh' := hh.differentiable (by norm_num)
  have hfj : ∀ j, Differentiable ℝ (pertP f j) := fun j => pert_diff_fderiv hf (pertE4 j)
  have hgx : Differentiable ℝ (pertDx g) := pert_diff_fderiv hg _
  have hgs' : Differentiable ℝ (pertDs g) := pert_diff_fderiv hg _
  have hhs' : Differentiable ℝ (pertDs h) := pert_diff_fderiv hh _
  have hDF : Differentiable ℝ (pertDs (pertF f g h η p ε)) :=
    pert_diff_fderiv (pertF_contDiff hf hg hh η p ε) _
  have key := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((((pert_phi_s (hfj 0) hg' hh' η (ε i) xb 0).mul
      (((pert_psi_s hgx hh' η (ε i) xb 0).mul ((pert_line_s hhs' xb 0).add_const (η * ε i))).add
        (pert_psi_s hgs' hh' η (ε i) xb 0))).add
      ((pert_phi_s (hfj 1) hg' hh' η (ε i) xb 0).mul (pert_line_s hgs' xb 0))).add
      ((pert_phi_s (hfj 2) hg' hh' η (ε i) xb 0).mul
        ((pert_line_s hhs' xb 0).add_const (η * ε i)))).const_mul (p i)
  rw [pert_Ds_eq hDF (key.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => pertF_Ds hf hg hh η p ε xb s))]
  simp only [Pi.mul_apply, Pi.add_apply, pertPsi_ss hx, pertPhi_ss hx hy, hgs, hhs]
  rw [pert_sum_quad hp
    (pertP f 0 (yb, yb, xb, xb) * (pertDx g (xb, 0) * pertDs (pertDs h) (xb, 0) +
      pertDs (pertDs g) (xb, 0)) + pertP f 1 (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
      pertP f 2 (yb, yb, xb, xb) * pertDs (pertDs h) (xb, 0))
    (pertP f 0 (yb, yb, xb, xb) * η *
      (pertDs (pertDx g) (xb, 0) + pertDx (pertDs g) (xb, 0)))
    (η * η * ((pertP (pertP f 0) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) +
      pertP (pertP f 0) 2 (yb, yb, xb, xb)) * pertDx g (xb, 0) +
      pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) +
      pertP (pertP f 2) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) +
      pertP (pertP f 2) 2 (yb, yb, xb, xb))) fun i => by ring]
  ring

end Miao.RationalExpectations
