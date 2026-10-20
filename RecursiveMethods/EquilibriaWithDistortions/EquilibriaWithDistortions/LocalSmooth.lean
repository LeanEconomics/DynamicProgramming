/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.LocalContraction

/-!
# Smoothness of `H` and the slope of the local equilibrium at `k*`

SLP §18.2, pp. 549 and 553.

**The implicit function `H` is `C¹`** (p. 549). Mathlib's implicit function theorem for a curried
bivariate function (`implicitFunctionOfBivariate`) is applied to `((x, z), y) ↦ F(x, y, z)` at
any point `((x₀, z₀), H(x₀, z₀))` where `F₂ ≠ 0` (`bivImplicit`). The resulting implicit
function agrees with the `H` of `LocalSolution` near `(x₀, z₀)` (`eventuallyEq_bivImplicit`),
so `H` is strictly differentiable there with derivative
`(a, b) ↦ −(F₁ a + F₃ b)/F₂` (`Hderiv`, `LocalSolution.hasStrictFDerivAt`). In particular
(`LocalSolution.hasStrictFDerivAt_center`, `hasDerivAt_H_left`, `hasDerivAt_H_right`)
`H₁(k*, k*) = −F₁*/F₂*` and `H₂(k*, k*) = −F₃*/F₂*` are genuine partial derivatives, and `H` is
`C¹` on a neighbourhood of `(k*, k*)` (`LocalSolution.contDiffAt`, `eventually_contDiffAt`).

**The slope of the equilibrium at `k*`** (derived remark after Proposition 18.3, p. 553). If
`g ∈ D_λ(I_ε)` is a strictly increasing fixed point of `T` (as given by `prop_18_3_fixedPoint`),
then `g` is differentiable at `k*` with `g′(k*) = λ*`, the stable root of the characteristic
polynomial (`hasDerivAt_fixedPoint_lamStar`, `prop_18_3_deriv`). Differentiability is not
assumed: writing `s(k) = (g(k) − k*)/(k − k*)` and `e = s − λ*`, the identity
`g(k) = H(k, g(g(k)))`, the derivative of `H` at `(k*, k*)` and `λ* = H₁* + H₂* λ*²` give
`|e(k)| ≤ c |e(g(k))| + τ'` near `k*` with `c = H₂*λ*/(1 − H₂*λ) < 1` and `τ'` arbitrarily
small, and iterating the bound squeezes `e` to `0`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-! ### Continuity of the partial derivatives of `F` -/

/-- `F₁` is continuous. -/
theorem continuous_F1f {θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun p : ℝ × ℝ => F1f θ U f p.1 p.2 := by
  have := continuous_deriv2_of_C2 hU
  have := (differentiable_of_C2 hf).continuous
  have := continuous_deriv_of_C2 hf
  have := continuous_deriv2_of_C2 hf
  simp only [F1f, psi, dpsi]
  fun_prop

/-- `F₂` is continuous. -/
theorem continuous_F2f {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun p : ℝ × ℝ × ℝ => F2f β θ U f p.1 p.2.1 p.2.2 := by
  have := continuous_deriv_of_C2 hU
  have := continuous_deriv2_of_C2 hU
  have := (differentiable_of_C2 hf).continuous
  have := continuous_deriv_of_C2 hf
  have := continuous_deriv2_of_C2 hf
  simp only [F2f, psi, dpsi]
  fun_prop

/-- `F₃` is continuous. -/
theorem continuous_F3f {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun p : ℝ × ℝ => F3f β θ U f p.1 p.2 := by
  have := continuous_deriv2_of_C2 hU
  have := (differentiable_of_C2 hf).continuous
  have := continuous_deriv_of_C2 hf
  simp only [F3f, psi]
  fun_prop

/-! ### The bivariate set-up `((x, z), y) ↦ F(x, y, z)` -/

/-- The partial derivative of `F` with respect to `(x, z)`:
`(a, b) ↦ F₁(x, y) a + F₃(y, z) b`. -/
noncomputable def Fxz (β θ : ℝ) (U f : ℝ → ℝ) (w : ℝ × ℝ) (y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  F1f θ U f w.1 y • ContinuousLinearMap.fst ℝ ℝ ℝ +
    F3f β θ U f y w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The partial derivative of `F` with respect to `y`, as a linear map: `b ↦ F₂ b`. -/
noncomputable def Fyy (β θ : ℝ) (U f : ℝ → ℝ) (w : ℝ × ℝ) (y : ℝ) : ℝ →L[ℝ] ℝ :=
  F2f β θ U f w.1 y w.2 • ContinuousLinearMap.id ℝ ℝ

/-- `∂F/∂(x, z) = Fxz`. -/
theorem hasFDerivAt_Feq_xz {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (v : (ℝ × ℝ) × ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => Feq β θ U f w.1 v.2 w.2) (Fxz β θ U f v.1 v.2) v.1 := by
  obtain ⟨⟨x0, z0⟩, y⟩ := v
  have h1 := (hasDerivAt_Feq_x (β := β) (θ := θ) hU hf x0 y z0).comp_hasFDerivAt (x0, z0)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((x0, z0) : ℝ × ℝ)))
  have h3 := (hasDerivAt_Feq_z (β := β) (θ := θ) (f := f) hU x0 y z0).comp_hasFDerivAt (x0, z0)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((x0, z0) : ℝ × ℝ)))
  have e : (fun w : ℝ × ℝ => Feq β θ U f w.1 y w.2) = fun w =>
      ((fun x => Feq β θ U f x y z0) ∘ Prod.fst) w +
        (((fun z => Feq β θ U f x0 y z) ∘ Prod.snd) w - Feq β θ U f x0 y z0) := by
    funext w
    simp only [Function.comp, Feq]
    ring
  rw [e]
  exact h1.add (h3.sub_const _)

/-- `∂F/∂y = Fyy`. -/
theorem hasFDerivAt_Feq_yy {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (v : (ℝ × ℝ) × ℝ) :
    HasFDerivAt (fun y => Feq β θ U f v.1.1 y v.1.2) (Fyy β θ U f v.1 v.2) v.2 := by
  refine (hasDerivAt_Feq_y (β := β) (θ := θ) hU hf v.1.1 v.2 v.1.2).hasFDerivAt.congr_fderiv ?_
  ext
  simp [Fyy]

/-- `Fxz` is continuous in `((x, z), y)`. -/
theorem continuous_Fxz {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun v : (ℝ × ℝ) × ℝ => Fxz β θ U f v.1 v.2 := by
  have c1 := continuous_F1f (θ := θ) hU hf
  have c3 := continuous_F3f (β := β) (θ := θ) hU hf
  refine ((c1.comp (continuous_fst.fst.prodMk continuous_snd)).smul continuous_const).add
    ((c3.comp (continuous_snd.prodMk continuous_fst.snd)).smul continuous_const)

/-- `Fyy` is continuous in `((x, z), y)`. -/
theorem continuous_Fyy {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun v : (ℝ × ℝ) × ℝ => Fyy β θ U f v.1 v.2 :=
  ((continuous_F2f (β := β) (θ := θ) hU hf).comp
    (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))).smul continuous_const

/-- The equivalence `b ↦ c b` of `ℝ` for `c ≠ 0`. -/
noncomputable def mulEquiv' (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)

/-- `Fyy` is the linear map `b ↦ F₂ b`, invertible when `F₂ ≠ 0`. -/
theorem Fyy_eq_mulEquiv' {β θ : ℝ} {U f : ℝ → ℝ} (w : ℝ × ℝ) (y : ℝ)
    (hc : F2f β θ U f w.1 y w.2 ≠ 0) :
    Fyy β θ U f w y = (mulEquiv' _ hc : ℝ →L[ℝ] ℝ) := by
  ext
  simp [Fyy, mulEquiv', ContinuousLinearEquiv.unitsEquivAut_apply]

/-- `Fyy` is invertible when `F₂ ≠ 0`. -/
theorem Fyy_isInvertible {β θ : ℝ} {U f : ℝ → ℝ} {w : ℝ × ℝ} {y : ℝ}
    (hc : F2f β θ U f w.1 y w.2 ≠ 0) : (Fyy β θ U f w y).IsInvertible :=
  ⟨mulEquiv' _ hc, (Fyy_eq_mulEquiv' w y hc).symm⟩

/-- **Mathlib's implicit function** for `F(x, y, z) = F(x₀, y₀, z₀)` near `((x₀, z₀), y₀)`,
solving for `y` as a function of `(x, z)`, when `F₂(x₀, y₀, z₀) ≠ 0`. -/
noncomputable def bivImplicit {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 2 f) (u : (ℝ × ℝ) × ℝ) (hc : F2f β θ U f u.1.1 u.2 u.1.2 ≠ 0) :
    ℝ × ℝ → ℝ :=
  implicitFunctionOfBivariate (f := fun w y => Feq β θ U f w.1 y w.2) (u := u)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_xz hU hf v)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_yy hU hf v)
    (continuous_Fxz hU hf).continuousAt (continuous_Fyy hU hf).continuousAt
    (Fyy_isInvertible hc)

/-- The derivative of `H`: `(a, b) ↦ −(F₁ a + F₃ b)/F₂` at `(x, H(x, z), z)`. -/
noncomputable def Hderiv (β θ : ℝ) (U f : ℝ → ℝ) (w : ℝ × ℝ) (y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (-F1f θ U f w.1 y / F2f β θ U f w.1 y w.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (-F3f β θ U f y w.2 / F2f β θ U f w.1 y w.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- **Implicit function theorem** (Mathlib) for `F`: `bivImplicit` is strictly differentiable at
`(x₀, z₀)` with derivative `Hderiv`, and near `((x₀, z₀), y₀)` the equation
`F(x, y, z) = F(x₀, y₀, z₀)` holds iff `y = bivImplicit (x, z)`. -/
theorem bivImplicit_spec {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (u : (ℝ × ℝ) × ℝ) (hc : F2f β θ U f u.1.1 u.2 u.1.2 ≠ 0) :
    HasStrictFDerivAt (bivImplicit hU hf u hc) (Hderiv β θ U f u.1 u.2) u.1 ∧
      ∀ᶠ v in 𝓝 u, (Feq β θ U f v.1.1 v.2 v.1.2 = Feq β θ U f u.1.1 u.2 u.1.2 ↔
        bivImplicit hU hf u hc v.1 = v.2) := by
  refine ⟨?_, eventually_apply_eq_iff_implicitFunctionOfBivariate
    (f := fun w y => Feq β θ U f w.1 y w.2) (u := u)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_xz hU hf v)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_yy hU hf v)
    (continuous_Fxz hU hf).continuousAt (continuous_Fyy hU hf).continuousAt
    (Fyy_isInvertible hc)⟩
  have h := hasStrictFDerivAt_implicitFunctionOfBivariate
    (f := fun w y => Feq β θ U f w.1 y w.2) (u := u)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_xz hU hf v)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_yy hU hf v)
    (continuous_Fxz hU hf).continuousAt (continuous_Fyy hU hf).continuousAt
    (Fyy_isInvertible hc)
  refine h.congr_fderiv ?_
  rw [Fyy_eq_mulEquiv' u.1 u.2 hc, ContinuousLinearMap.inverse_equiv]
  ext
  · simp [Hderiv, Fxz, mulEquiv', ContinuousLinearEquiv.unitsEquivAut_apply_symm]
    ring
  · simp [Hderiv, Fxz, mulEquiv', ContinuousLinearEquiv.unitsEquivAut_apply_symm]
    ring

/-! ### `H` is `C¹` near `(k*, k*)` -/

/-- **`H` agrees with Mathlib's implicit function.** If `(x₀, z₀)` lies in the open square
`(k* − ε₀, k* + ε₀)²` and `F₂(x₀, H(x₀, z₀), z₀) ≠ 0`, then `H = bivImplicit` near `(x₀, z₀)`. -/
theorem eventuallyEq_bivImplicit {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {x₀ z₀ : ℝ}
    (hx : |x₀ - ks| < ε₀) (hz : |z₀ - ks| < ε₀)
    (hc : F2f β θ U f x₀ (H x₀ z₀) z₀ ≠ 0) :
    (fun q : ℝ × ℝ => H q.1 q.2) =ᶠ[𝓝 (x₀, z₀)]
      bivImplicit L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc := by
  obtain ⟨-, hiff⟩ := bivImplicit_spec L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc
  have hHc : Continuous fun q : ℝ × ℝ => ((q.1, q.2), H q.1 q.2) :=
    (continuous_fst.prodMk continuous_snd).prodMk hH.continuous
  have h1 : ∀ᶠ q in 𝓝 ((x₀, z₀) : ℝ × ℝ), (Feq β θ U f q.1 (H q.1 q.2) q.2 =
      Feq β θ U f x₀ (H x₀ z₀) z₀ ↔ bivImplicit L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc
        (q.1, q.2) = H q.1 q.2) :=
    have ht : Tendsto (fun q : ℝ × ℝ => ((q.1, q.2), H q.1 q.2)) (𝓝 (x₀, z₀))
        (𝓝 ((x₀, z₀), H x₀ z₀)) := hHc.tendsto (x₀, z₀)
    ht.eventually hiff
  have hbox : ∀ᶠ q in 𝓝 ((x₀, z₀) : ℝ × ℝ), |q.1 - ks| < ε₀ ∧ |q.2 - ks| < ε₀ := by
    have c1 : Continuous fun q : ℝ × ℝ => |q.1 - ks| := by fun_prop
    have c2 : Continuous fun q : ℝ × ℝ => |q.2 - ks| := by fun_prop
    exact (c1.continuousAt.eventually (gt_mem_nhds hx)).and
      (c2.continuousAt.eventually (gt_mem_nhds hz))
  have hx₀ : x₀ ∈ Jint ks ε₀ := mem_Jint_iff.2 hx.le
  have hz₀ : z₀ ∈ Jint ks ε₀ := mem_Jint_iff.2 hz.le
  filter_upwards [h1, hbox] with q hq hb
  have e1 := hH.eq7 q.1 (mem_Jint_iff.2 hb.1.le) q.2 (mem_Jint_iff.2 hb.2.le)
  have e0 := hH.eq7 x₀ hx₀ z₀ hz₀
  exact (hq.1 (by rw [e1, e0])).symm

/-- **`H` is strictly differentiable** at every `(x₀, z₀)` of the open square
`(k* − ε₀, k* + ε₀)²` with `F₂(x₀, H(x₀, z₀), z₀) ≠ 0`, with derivative
`(a, b) ↦ −(F₁ a + F₃ b)/F₂` (`Hderiv`). -/
theorem LocalSolution.hasStrictFDerivAt {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {x₀ z₀ : ℝ}
    (hx : |x₀ - ks| < ε₀) (hz : |z₀ - ks| < ε₀)
    (hc : F2f β θ U f x₀ (H x₀ z₀) z₀ ≠ 0) :
    HasStrictFDerivAt (fun q : ℝ × ℝ => H q.1 q.2) (Hderiv β θ U f (x₀, z₀) (H x₀ z₀))
      (x₀, z₀) :=
  ((bivImplicit_spec L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc).1).congr_of_eventuallyEq
    (eventuallyEq_bivImplicit L hH hx hz hc).symm

/-- At the steady state, `Hderiv` is `(a, b) ↦ H₁* a + H₂* b` with `H₁* = −F₁*/F₂*`,
`H₂* = −F₃*/F₂*`. -/
theorem Hderiv_center {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    Hderiv β θ U f (ks, ks) ks =
      (-F1s β θ U f ks / F2s β θ U f ks) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-F3s U θ f ks / F2s β θ U f ks) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp only [Hderiv, F1f_star L.beta_pos L.euler, F2f_star L.beta_pos L.euler,
    F3f_star L.euler]

/-- **`H` at the steady state** (p. 549): `H` is strictly differentiable at `(k*, k*)` with
derivative `(a, b) ↦ H₁* a + H₂* b`, `H₁* = −F₁*/F₂*`, `H₂* = −F₃*/F₂*`; and `H` coincides
near `(k*, k*)` with Mathlib's implicit function. -/
theorem LocalSolution.hasStrictFDerivAt_center {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ}
    {H : ℝ → ℝ → ℝ} (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    HasStrictFDerivAt (fun q : ℝ × ℝ => H q.1 q.2)
      ((-F1s β θ U f ks / F2s β θ U f ks) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-F3s U θ f ks / F2s β θ U f ks) • ContinuousLinearMap.snd ℝ ℝ ℝ) (ks, ks) := by
  have hc : F2f β θ U f ks (H ks ks) ks ≠ 0 := by
    rw [hH.center, F2f_star L.beta_pos L.euler]
    exact L.F2s_pos.ne'
  have h := hH.hasStrictFDerivAt L (x₀ := ks) (z₀ := ks) (by simpa using hH.eps_pos)
    (by simpa using hH.eps_pos) hc
  rw [hH.center, Hderiv_center L] at h
  exact h

/-- **`H₁(k*, k*) = −F₁*/F₂*`** as a genuine partial derivative. -/
theorem hasDerivAt_H_left {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    HasDerivAt (fun x => H x ks) (-F1s β θ U f ks / F2s β θ U f ks) ks := by
  have hg : HasFDerivAt (fun x : ℝ => ((x, ks) : ℝ × ℝ))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) ks :=
    (hasFDerivAt_id ks).prodMk (hasFDerivAt_const ks ks)
  have h := HasFDerivAt.comp (f := fun x : ℝ => ((x, ks) : ℝ × ℝ)) ks
    (hH.hasStrictFDerivAt_center L).hasFDerivAt hg
  exact h.hasDerivAt.congr_deriv (by simp)

/-- **`H₂(k*, k*) = −F₃*/F₂*`** as a genuine partial derivative. -/
theorem hasDerivAt_H_right {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    HasDerivAt (fun z => H ks z) (-F3s U θ f ks / F2s β θ U f ks) ks := by
  have hg : HasFDerivAt (fun z : ℝ => ((ks, z) : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) ks :=
    (hasFDerivAt_const ks ks).prodMk (hasFDerivAt_id ks)
  have h := (hH.hasStrictFDerivAt_center L).hasFDerivAt.comp ks hg
  exact h.hasDerivAt.congr_deriv (by simp)

/-- **`H` is `C¹` at `(k*, k*)`** (the book's "`C¹` function `H`", p. 549), with derivative
`Hderiv` on a neighbourhood. -/
theorem LocalSolution.contDiffAt {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => H q.1 q.2) (ks, ks) := by
  have cF2 := continuous_F2f (β := β) (θ := θ) L.U_contDiff L.f_contDiff
  have cG : Continuous fun q : ℝ × ℝ => F2f β θ U f q.1 (H q.1 q.2) q.2 :=
    cF2.comp (continuous_fst.prodMk (hH.continuous.prodMk continuous_snd))
  have hc0 : F2f β θ U f ks (H ks ks) ks ≠ 0 := by
    rw [hH.center, F2f_star L.beta_pos L.euler]
    exact L.F2s_pos.ne'
  set u : Set (ℝ × ℝ) := {q | |q.1 - ks| < ε₀ ∧ |q.2 - ks| < ε₀ ∧
    F2f β θ U f q.1 (H q.1 q.2) q.2 ≠ 0} with hu
  have huo : IsOpen u := by
    refine (isOpen_lt (f := fun q : ℝ × ℝ => |q.1 - ks|) (by fun_prop) continuous_const).inter
      ((isOpen_lt (f := fun q : ℝ × ℝ => |q.2 - ks|) (by fun_prop) continuous_const).inter
        (isOpen_ne_fun cG continuous_const))
  have hku : ((ks, ks) : ℝ × ℝ) ∈ u := ⟨by simpa using hH.eps_pos, by simpa using hH.eps_pos, hc0⟩
  refine contDiffAt_one_iff.2 ⟨fun q => Hderiv β θ U f q (H q.1 q.2), u, huo.mem_nhds hku,
    ?_, fun q hq => (hH.hasStrictFDerivAt L hq.1 hq.2.1 hq.2.2).hasFDerivAt⟩
  have c1 : Continuous fun q : ℝ × ℝ => F1f θ U f q.1 (H q.1 q.2) :=
    (continuous_F1f L.U_contDiff L.f_contDiff).comp (continuous_fst.prodMk hH.continuous)
  have c3 : Continuous fun q : ℝ × ℝ => F3f β θ U f (H q.1 q.2) q.2 :=
    (continuous_F3f L.U_contDiff L.f_contDiff).comp (hH.continuous.prodMk continuous_snd)
  refine (((c1.continuousOn.neg.div cG.continuousOn fun q hq => hq.2.2).smul
    continuousOn_const).add ((c3.continuousOn.neg.div cG.continuousOn fun q hq => hq.2.2).smul
    continuousOn_const))

/-- `H` is `C¹` on a neighbourhood of `(k*, k*)`. -/
theorem LocalSolution.eventually_contDiffAt {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    ∀ᶠ q in 𝓝 ((ks, ks) : ℝ × ℝ), ContDiffAt ℝ 1 (fun q : ℝ × ℝ => H q.1 q.2) q :=
  (hH.contDiffAt L).eventually (by simp)

/-! ### The slope of the equilibrium at `k*` -/

/-- `λ*` solves `λ = H₁* + H₂* λ²` (equivalently `P(λ*) = 0`). -/
theorem LocalHyp.lamStar_eq {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    lamStar β θ U f ks = -F1s β θ U f ks / F2s β θ U f ks +
      -F3s U θ f ks / F2s β θ U f ks * lamStar β θ U f ks ^ 2 := by
  obtain ⟨-, hfac, -⟩ := L.charPoly_roots
  have h0 : charPoly β θ U f ks (lamStar β θ U f ks) = 0 := by rw [hfac]; ring
  simp only [charPoly] at h0
  have hF2 := L.F2s_pos.ne'
  field_simp
  linarith

/-- **The slope of the local equilibrium at `k*` is `λ*`** (derived remark, p. 553). Let
`λ ∈ (λ*, 1)`, `0 < ε ≤ ε₀`, and let `g ∈ D_λ(I_ε)` be strictly increasing on `I_ε` with
`g(k) = H(k, g(g(k)))` on `I_ε`. Then `g` is differentiable at `k*` and `g′(k*) = λ*`, the root of
`P` in `(0, 1)`. No differentiability of `g` is assumed. -/
theorem hasDerivAt_fixedPoint_lamStar {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε)
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) {g : ℝ → ℝ} (hg : g ∈ Dlam ks ε lam)
    (hfix : ∀ k ∈ Jint ks ε, Top H g k = g k) (hsm : StrictMonoOn g (Jint ks ε)) :
    HasDerivAt g (lamStar β θ U f ks) ks := by
  set ls := lamStar β θ U f ks with hls
  set H1 := -F1s β θ U f ks / F2s β θ U f ks with hH1
  set H2 := -F3s U θ f ks / F2s β θ U f ks with hH2
  obtain ⟨-, -, hls0, hls1, -⟩ := L.charPoly_roots
  have hH2p : 0 < H2 := L.H2s_pos
  have hlpos : 0 < lam := hls0.trans hl
  have hK : H2 * (1 + lam) < 1 := L.H2s_mul_lt_one hl1.le
  have hden : 0 < 1 - H2 * lam := by nlinarith
  have hroot : ls = H1 + H2 * ls ^ 2 := L.lamStar_eq
  set c := H2 * ls / (1 - H2 * lam) with hc
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hden.le
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hden]
    nlinarith
  have hksJ : ks ∈ Jint ks ε := center_mem_Jint hε.le
  have hmaps := Dlam_mapsTo hg hl1.le
  have hgks : g ks = ks := hg.1
  have hgne : ∀ k ∈ Jint ks ε, k ≠ ks → g k ≠ ks := fun k hk hne h =>
    hne (hsm.injOn hk hksJ (h.trans hgks.symm))
  set s : ℝ → ℝ := fun k => (g k - ks) / (k - ks) with hs
  have hsk : ∀ k, k ≠ ks → g k - ks = s k * (k - ks) := fun k hk => by
    simp only [hs]
    field_simp [sub_ne_zero.2 hk]
  have hspos : ∀ k ∈ Jint ks ε, k ≠ ks → 0 < s k := by
    intro k hk hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hsm hk hksJ h
      rw [hgks] at this
      exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · have := hsm hksJ hk h
      rw [hgks] at this
      exact div_pos (by linarith) (by linarith)
  have hsle : ∀ k ∈ Jint ks ε, k ≠ ks → s k ≤ lam := by
    intro k hk hne
    have h1 := hg.2 k hk ks hksJ
    rw [hgks, hsk k hne, abs_mul] at h1
    have hd : 0 < |k - ks| := abs_pos.2 (sub_ne_zero.2 hne)
    have := le_of_mul_le_mul_right h1 hd
    exact (le_abs_self _).trans this
  -- the derivative of `H` at `(k*, k*)`
  have hD := (hH.hasStrictFDerivAt_center L).hasFDerivAt
  -- the key estimate, for a given `τ > 0`
  have key : ∀ τ > 0, ∃ δ > 0, ∀ k ∈ Jint ks ε, k ≠ ks → |k - ks| < δ →
      |s k - ls| ≤ c * |s (g k) - ls| + τ / (1 - H2 * lam) := by
    intro τ hτ
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hD.isLittleO.def hτ)
    refine ⟨δ, hδ, fun k hk hne hkd => ?_⟩
    have hgk := hmaps k hk
    have hggk := hmaps _ hgk
    have hgkne := hgne k hk hne
    have hd : 0 < |k - ks| := abs_pos.2 (sub_ne_zero.2 hne)
    have hlip1 : |g k - ks| ≤ |k - ks| := by
      have := hg.2 k hk ks hksJ
      rw [hgks] at this
      nlinarith [abs_nonneg (k - ks)]
    have hlip2 : |g (g k) - ks| ≤ |k - ks| := by
      have := hg.2 _ hgk ks hksJ
      rw [hgks] at this
      nlinarith [abs_nonneg (g k - ks)]
    have hq : dist ((k, g (g k)) : ℝ × ℝ) (ks, ks) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt hkd (lt_of_le_of_lt hlip2 hkd)
    have hb := hball hq
    have hn : ‖((k, g (g k)) : ℝ × ℝ) - (ks, ks)‖ ≤ |k - ks| := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
      exact max_le le_rfl hlip2
    have hval : H (k, g (g k)).1 (k, g (g k)).2 = g k := hfix k hk
    simp only [hval, hH.center, Real.norm_eq_abs] at hb
    have hlin : ((-F1s β θ U f ks / F2s β θ U f ks) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-F3s U θ f ks / F2s β θ U f ks) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (((k, g (g k)) : ℝ × ℝ) - (ks, ks)) = H1 * (k - ks) + H2 * (g (g k) - ks) := by
      simp [hH1, hH2]
    rw [hlin] at hb
    have hb2 : |g k - ks - (H1 * (k - ks) + H2 * (g (g k) - ks))| ≤ τ * |k - ks| :=
      hb.trans (mul_le_mul_of_nonneg_left hn hτ.le)
    -- express in terms of slopes
    have e1 := hsk k hne
    have e2 : g (g k) - ks = s (g k) * (s k * (k - ks)) := by
      rw [hsk (g k) hgkne, e1]
    rw [e1, e2] at hb2
    have e3 : s k * (k - ks) - (H1 * (k - ks) + H2 * (s (g k) * (s k * (k - ks)))) =
        (s k - H1 - H2 * s (g k) * s k) * (k - ks) := by ring
    rw [e3, abs_mul] at hb2
    have hb3 : |s k - H1 - H2 * s (g k) * s k| ≤ τ := le_of_mul_le_mul_right hb2 hd
    have e4 : (1 - H2 * s (g k)) * (s k - ls) =
        (s k - H1 - H2 * s (g k) * s k) + H2 * ls * (s (g k) - ls) := by
      linear_combination (-1 : ℝ) * hroot
    have hs' := hsle _ hgk hgkne
    have hs'p := hspos _ hgk hgkne
    have h5 : 0 < 1 - H2 * s (g k) := by nlinarith
    have h6 : (1 - H2 * lam) * |s k - ls| ≤ (1 - H2 * s (g k)) * |s k - ls| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    have h7 : (1 - H2 * s (g k)) * |s k - ls| ≤ τ + H2 * ls * |s (g k) - ls| := by
      have e5 : |(1 - H2 * s (g k)) * (s k - ls)| = (1 - H2 * s (g k)) * |s k - ls| := by
        rw [abs_mul, abs_of_pos h5]
      rw [← e5, e4]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (by positivity : 0 < H2 * ls)]
      linarith
    rw [hc, show H2 * ls / (1 - H2 * lam) * |s (g k) - ls| + τ / (1 - H2 * lam) =
      (H2 * ls * |s (g k) - ls| + τ) / (1 - H2 * lam) by ring, le_div_iff₀ hden]
    linarith
  -- squeeze
  have hsmall : ∀ η > 0, ∃ δ > 0, ∀ k ∈ Jint ks ε, k ≠ ks → |k - ks| < δ → |s k - ls| ≤ η := by
    intro η hη
    set τ := η * (1 - H2 * lam) * (1 - c) with hτ
    have hτp : 0 < τ := by
      have : 0 < 1 - c := by linarith
      positivity
    obtain ⟨δ, hδ, hkey⟩ := key τ hτp
    set δ' := min δ ε with hδ'
    have hδ'p : 0 < δ' := lt_min hδ hε
    refine ⟨δ', hδ'p, fun k hk hne hkd => ?_⟩
    have hτ' : τ / (1 - H2 * lam) = η * (1 - c) := by
      rw [hτ]
      field_simp
    have hbound : ∀ n : ℕ, ∀ k ∈ Jint ks ε, k ≠ ks → |k - ks| < δ' →
        |s k - ls| ≤ c ^ n * 2 + η := by
      intro n
      induction n with
      | zero =>
        intro k hk hne _
        have h1 := hspos k hk hne
        have h2 := hsle k hk hne
        rw [pow_zero, one_mul, abs_le]
        constructor <;> linarith
      | succ n ih =>
        intro k hk hne hkd
        have hgk := hmaps k hk
        have hgkne := hgne k hk hne
        have hlip : |g k - ks| < δ' := by
          have := hg.2 k hk ks hksJ
          rw [hgks] at this
          nlinarith [abs_nonneg (k - ks)]
        have h1 := hkey k hk hne (lt_of_lt_of_le hkd (min_le_left _ _))
        have h2 := ih (g k) hgk hgkne hlip
        rw [hτ'] at h1
        have h3 := mul_le_mul_of_nonneg_left h2 hc0
        rw [pow_succ]
        nlinarith
    have hlim : Tendsto (fun n : ℕ => c ^ n * 2 + η) atTop (𝓝 η) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const 2).add_const η
    exact ge_of_tendsto' hlim fun n => hbound n k hk hne hkd
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ, hδ, hsm'⟩ := hsmall (η / 2) (by linarith)
  refine ⟨min δ ε, lt_min hδ hε, fun {k} hk hkd => ?_⟩
  have hne : k ≠ ks := hk
  rw [Real.dist_eq] at hkd ⊢
  have hkJ : k ∈ Jint ks ε := mem_Jint_iff.2 (lt_of_lt_of_le hkd (min_le_right _ _)).le
  have h := hsm' k hkJ hne (lt_of_lt_of_le hkd (min_le_left _ _))
  have e : slope g ks k = s k := by
    rw [slope_def_field, hgks]
  rw [e]
  linarith

/-- **Proposition 18.3 with the slope** (p. 553): for every `λ ∈ (λ*, 1)` the unique fixed point
`g ∈ D_λ(I_ε)` of Proposition 18.3 is differentiable at `k*` with `g′(k*) = λ*`. -/
theorem prop_18_3_deriv {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∃ g : ℝ → ℝ, g ∈ Dlam ks ε lam ∧
      (∀ k ∈ Jint ks ε, Top H g k = g k) ∧ HasDerivAt g (lamStar β θ U f ks) ks := by
  obtain ⟨ε, hε, hεε₀, g, hg, hfix, -, -, hsm, -⟩ := prop_18_3_fixedPoint L hH hl hl1
  exact ⟨ε, hε, hεε₀, g, hg, hfix, hasDerivAt_fixedPoint_lamStar L hH hε hl hl1 hg hfix hsm⟩

end StokeyLucasPrescott.EquilibriaWithDistortions
