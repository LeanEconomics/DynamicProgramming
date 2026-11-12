/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.ISTCPredictions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Local dynamics around the balanced growth path

AKMM, §13.3 (p. 381) and Appendix 13.A.3 (pp. 851–852). Write the detrended system
(13.12)–(13.13) as `c̃̇ = F_c(c̃, k̃)`, `k̃̇ = F_k(c̃, k̃)` (`istcFc`, `istcFk`).

* The partial derivatives at `(c̃*, k̃*)` are the entries of the Jacobian (13.A.14)
  (`eq_13_A_14`).
* The characteristic equation `det(A − zI) = 0` is (13.A.15) (`eq_13_A_15`).
* Under (13.8) the right side of (13.A.15) is positive and the second zero of its left side is
  positive; both roots are real, one strictly negative and one strictly positive, and the stable
  root is the printed `½b(1 − √(1 + 4Q/b²))` (`istc_eigenvalues`, `istc_stable_root`,
  `istc_saddle`).
* The half-life of a deviation decaying at `e^{zt}` is `ln(1/2)/z` (`istc_half_life`).
-/

namespace AKMM.Growth

open Real

/-- AKMM, (13.12): `c̃̇ = F_c(c̃, k̃) = c̃((αA_x(A_y h)^{1−α}k̃^{α−1} − δ − γ_x − ρ)/σ − g_c)`. -/
noncomputable def istcFc (α σ ρ δ Ax Ay h γx γy c k : ℝ) : ℝ :=
  c * ((α * Ax * (Ay * h) ^ (1 - α) * k ^ (α - 1) - δ - γx - ρ) / σ - istcGc α γx γy)

/-- AKMM, (13.13): `k̃̇ = F_k(c̃, k̃) = A_x(A_y h)^{1−α}k̃^α − A_x c̃ − (δ + g_K)k̃`. -/
noncomputable def istcFk (α δ Ax Ay h γx γy n c k : ℝ) : ℝ :=
  Ax * (Ay * h) ^ (1 - α) * k ^ α - Ax * c - (δ + istcGK α γx γy n) * k

/-- `F_c` and `F_k` are (13.12)–(13.13) multiplied by `c̃` and `k̃`. -/
theorem istc_F_eq {α σ ρ δ Ax Ay h γx γy n c k : ℝ} (hk : 0 < k) (hAy : 0 < Ay) (hh : 0 < h) :
    istcFc α σ ρ δ Ax Ay h γx γy c k =
        c * ((α * Ax * (Ay * h / k) ^ (1 - α) - δ - γx - ρ) / σ - istcGc α γx γy) ∧
      istcFk α δ Ax Ay h γx γy n c k =
        k * (Ax * ((Ay * h / k) ^ (1 - α) - c / k) - δ - istcGK α γx γy n) := by
  have hAh : 0 < Ay * h := by positivity
  have e : (Ay * h) ^ (1 - α) * k ^ (α - 1) = (Ay * h / k) ^ (1 - α) := by
    rw [mul_comm, istc_rpow_ratio hk hAh]
  constructor
  · unfold istcFc
    rw [mul_assoc (α * Ax), e]
  · unfold istcFk
    have e2 : (Ay * h) ^ (1 - α) * k ^ α = k * (Ay * h / k) ^ (1 - α) := by
      rw [mul_comm, istc_cd_eq hk hAh]
    rw [mul_assoc Ax, e2]
    field_simp
    ring

/-- AKMM, (13.A.14), p. 851: **the Jacobian at the balanced growth path**. At `(c̃*, k̃*)`:
`∂F_c/∂c̃ = 0`, `∂F_c/∂k̃ = −(1−α)αA_x(A_y h)^{1−α}k̃*^{α−2}c̃*/σ`, `∂F_k/∂c̃ = −A_x` and
`∂F_k/∂k̃ = ρ − n − γ_xα(1−σ)/(1−α) − γ_y(1−σ)`. -/
theorem eq_13_A_14 {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) :
    let ks := istcKStar α σ ρ δ Ax Ay h γx γy
    let cs := istcCStar α σ ρ δ Ax Ay h γx γy n
    HasDerivAt (fun c => istcFc α σ ρ δ Ax Ay h γx γy c ks) 0 cs ∧
      HasDerivAt (fun k => istcFc α σ ρ δ Ax Ay h γx γy cs k)
        (-((1 - α) * α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 2) * cs / σ)) ks ∧
      HasDerivAt (fun c => istcFk α δ Ax Ay h γx γy n c ks) (-Ax) cs ∧
      HasDerivAt (fun k => istcFk α δ Ax Ay h γx γy n cs k)
        (ρ - n - γx * (α * (1 - σ) / (1 - α)) - γy * (1 - σ)) ks := by
  intro ks cs
  have hks : 0 < ks := by simp only [ks, istcKStar]; positivity
  have hAh : 0 < Ay * h := by positivity
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  have hmpk' : α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 1) = istcD α σ ρ δ γx γy := by
    have e : (Ay * h) ^ (1 - α) * ks ^ (α - 1) = (Ay * h / ks) ^ (1 - α) := by
      rw [mul_comm, istc_rpow_ratio hks hAh]
    rw [mul_assoc (α * Ax), e, mul_assoc, hmpk]
    field_simp
  have hzero : (α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 1) - δ - γx - ρ) / σ -
      istcGc α γx γy = 0 := by
    rw [hmpk', istc_D_eq]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (hasDerivAt_id' cs).mul_const ((α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 1) - δ -
      γx - ρ) / σ - istcGc α γx γy)
    unfold istcFc
    convert h using 1
    rw [hzero]
    ring
  · have h1 := (Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hks.ne'))
    have h2 := ((((h1.const_mul (α * Ax * (Ay * h) ^ (1 - α))).sub_const δ).sub_const γx).sub_const
      ρ).div_const σ
    have h3 := (h2.sub_const (istcGc α γx γy)).const_mul cs
    unfold istcFc
    convert h3 using 1
    rw [show α - 1 - 1 = α - 2 by ring]
    ring
  · have h := ((hasDerivAt_id' cs).const_mul Ax).const_sub (Ax * (Ay * h) ^ (1 - α) * ks ^ α)
    have h2 := h.sub_const ((δ + istcGK α γx γy n) * ks)
    unfold istcFk
    convert h2 using 1
    ring
  · have h1 := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hks.ne')).const_mul
      (Ax * (Ay * h) ^ (1 - α))).sub_const (Ax * cs)
    have h2 := h1.sub ((hasDerivAt_id' ks).const_mul (δ + istcGK α γx γy n))
    unfold istcFk
    convert h2 using 1
    have e : Ax * (Ay * h) ^ (1 - α) * (α * ks ^ (α - 1)) = istcD α σ ρ δ γx γy := by
      rw [← hmpk']; ring
    rw [mul_one, e]
    have := istc_D_sub_gK α σ ρ δ γx γy n hα1
    unfold istcBound at this
    linarith

/-- AKMM, (13.A.15), p. 852: **the characteristic equation**. For the Jacobian
`[[0, −P], [−A_x, b]]` of (13.A.14), `det(A − zI) = 0` iff `−z(b − z) = A_x P`. -/
theorem eq_13_A_15 {Ax P b z : ℝ} :
    Matrix.det !![0 - z, -P; -Ax, b - z] = 0 ↔ -z * (b - z) = Ax * P := by
  rw [Matrix.det_fin_two_of]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 852: **the eigenvalues**. If `b > 0` and `Q > 0`, the roots of
`−z(b − z) = Q` are `z_± = (b ± √(b² + 4Q))/2`, and `z_− < 0 < z_+`. -/
theorem istc_eigenvalues {b Q z : ℝ} (hb : 0 < b) (hQ : 0 < Q) :
    (-z * (b - z) = Q ↔ z = (b + √(b ^ 2 + 4 * Q)) / 2 ∨ z = (b - √(b ^ 2 + 4 * Q)) / 2) ∧
      (b - √(b ^ 2 + 4 * Q)) / 2 < 0 ∧ 0 < (b + √(b ^ 2 + 4 * Q)) / 2 := by
  have hs : 0 ≤ b ^ 2 + 4 * Q := by positivity
  have hsq := Real.sq_sqrt hs
  have hgt : b < √(b ^ 2 + 4 * Q) := by
    rw [Real.lt_sqrt hb.le]
    linarith
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by linarith, by positivity⟩
  · have hfac : (z - (b + √(b ^ 2 + 4 * Q)) / 2) * (z - (b - √(b ^ 2 + 4 * Q)) / 2) = 0 := by
      nlinarith [hsq]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rcases h with h1 | h1 <;> rw [h1] <;> nlinarith [hsq]

/-- AKMM, p. 852: the stable root in the printed form,
`(b − √(b² + 4Q))/2 = ½b(1 − √(1 + 4Q/b²))` for `b > 0`. -/
theorem istc_stable_root {b Q : ℝ} (hb : 0 < b) (hQ : 0 < Q) :
    (b - √(b ^ 2 + 4 * Q)) / 2 = 1 / 2 * b * (1 - √(1 + 4 * Q / b ^ 2)) := by
  have hb2 : 0 < b ^ 2 := by positivity
  have e : √(b ^ 2 + 4 * Q) = b * √(1 + 4 * Q / b ^ 2) := by
    rw [show b ^ 2 + 4 * Q = b ^ 2 * (1 + 4 * Q / b ^ 2) by field_simp,
      Real.sqrt_mul hb2.le, Real.sqrt_sq hb.le]
  rw [e]
  ring

/-- AKMM, App. 13.A.3, p. 852: **saddle-path stability**. Under (13.8) and `g_K + δ > 0`, at the
balanced growth path the constant `Q = (1−α)αA_x²(A_y h)^{1−α}k̃*^{α−2}c̃*/σ` on the right of
(13.A.15) is positive, the second zero `b = ρ − n − γ_xα(1−σ)/(1−α) − γ_y(1−σ)` of its left side
is positive, and so the Jacobian has one strictly negative and one strictly positive real
eigenvalue. -/
theorem istc_saddle {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ)
    (h138 : istcBound α σ ρ n γx γy < 0) :
    let b := ρ - n - γx * (α * (1 - σ) / (1 - α)) - γy * (1 - σ)
    let Q := (1 - α) * α * Ax ^ 2 * (Ay * h) ^ (1 - α) *
      istcKStar α σ ρ δ Ax Ay h γx γy ^ (α - 2) * istcCStar α σ ρ δ Ax Ay h γx γy n / σ
    0 < b ∧ 0 < Q ∧
      ∃ zm zp, zm < 0 ∧ 0 < zp ∧ ∀ z,
        Matrix.det !![0 - z, -((1 - α) * α * Ax * (Ay * h) ^ (1 - α) *
          istcKStar α σ ρ δ Ax Ay h γx γy ^ (α - 2) * istcCStar α σ ρ δ Ax Ay h γx γy n / σ);
          -Ax, b - z] = 0 ↔ z = zp ∨ z = zm := by
  intro b Q
  have hpos := istc_steady_pos hα0 hα1 hAx hAy hh hgK h138
  have hb : 0 < b := by
    have : b = -istcBound α σ ρ n γx γy := by
      simp only [b, istcBound]; ring
    linarith
  have h1α : 0 < 1 - α := by linarith
  have hQ : 0 < Q := by
    have := hpos.1; have := hpos.2
    simp only [Q]; positivity
  refine ⟨hb, hQ, (b - √(b ^ 2 + 4 * Q)) / 2, (b + √(b ^ 2 + 4 * Q)) / 2,
    (istc_eigenvalues (z := 0) hb hQ).2.1, (istc_eigenvalues (z := 0) hb hQ).2.2, fun z => ?_⟩
  rw [eq_13_A_15, ← (istc_eigenvalues (z := z) hb hQ).1]
  have e : Ax * ((1 - α) * α * Ax * (Ay * h) ^ (1 - α) * istcKStar α σ ρ δ Ax Ay h γx γy ^ (α - 2) *
      istcCStar α σ ρ δ Ax Ay h γx γy n / σ) = Q := by
    simp only [Q]; ring
  rw [e]

/-- AKMM, p. 852: **the half-life**. A deviation decaying as `e^{zt}` with `z < 0` halves at
`τ` iff `τ = ln(1/2)/z`, and `τ > 0`; the speed of convergence is `−z > 0`. -/
theorem istc_half_life {z τ : ℝ} (hz : z < 0) :
    (Real.exp (z * τ) = 1 / 2 ↔ τ = Real.log (1 / 2) / z) ∧ 0 < Real.log (1 / 2) / z := by
  have hlog : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, div_pos_of_neg_of_neg hlog hz⟩
  · have := congrArg Real.log h
    rw [Real.log_exp] at this
    rw [eq_div_iff hz.ne, ← this]
    ring
  · rw [h, mul_div_cancel₀ _ hz.ne, Real.exp_log (by norm_num)]

end AKMM.Growth
