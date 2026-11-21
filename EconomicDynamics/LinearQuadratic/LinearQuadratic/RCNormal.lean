/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.RCRobustLQ
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The worst-case normal distribution and relative entropy of normals

Miao, §9.6, pp. 321–324. The standard normal density is `rcStdPdf` and the normal density with
mean `w` and covariance `Σ` is `rcGaussPdf w Σ`. Expectations under a law with mean `w` and
covariance `Σ` use only these two moments (`RCMoments`).

* `rc_worst_ratio` (p. 321): `m*(ε) ∝ exp(ε'C'PCε/(2θ) + ε'C'P(Ax + Bu)/θ)`;
  `rc_worst_exponent`: `π(ε)m*(ε) ∝ exp(−½ε'Kε + ε'K(θI − C'PC)⁻¹C'P(Ax + Bu))`,
  `K = I − θ⁻¹C'PC`; `rc_worst_density`: `π m*` is proportional to the normal density with mean
  `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` and covariance `K⁻¹`.
* `rc_nonsingular_not_enough` (correction): the book requires only that `K` be nonsingular; it must
  be positive definite. With `K = −1` the worst-case kernel is not integrable.
* `rc_llr_normal` (p. 323): `ln(π̂/π) = ½(−(ε − w)'Σ⁻¹(ε − w) + ε'ε − ln det Σ)`.
* `rc_moment_quad`, `rc_moment_trace_inv` (p. 323): `∫(ε − w)'Σ⁻¹(ε − w)π̂ = tr(I)`, so
  `−½∫(ε − w)'Σ⁻¹(ε − w)π̂ = −½ tr(I)` (`rc_moment_half`); the book prints `+½ tr(I)`
  (`rc_moment_sign_misprint`).
* `rc_half_sq_split`, `rc_half_sq_moment` (pp. 323–324): `½ε'ε = ½w'w + ½(ε − w)'(ε − w) +
  w'(ε − w)` and `½∫ε'επ̂ = ½w'w + ½ tr Σ`.
* **(9.56)** (`eq_9_56`): `∫π̂ ln(π̂/π) = ½w'w − ½ ln det Σ + ½ tr(Σ − I)`.
* `rc_R_first_line` (p. 322): computing `R(V)` from the first line of (9.48),
  `∫V π* + θ∫π* ln(π*/π) = −½y'D(P)y − d/2 − (θ/2) ln det K⁻¹`, and `rc_R_lines_agree`: it agrees
  with the second line (`rc_R_quad`).

Departure: "`π̂` is normal with mean `w` and covariance `Σ`" enters through the explicit density in
the log-likelihood ratio and through the two moments of the law integrated against.
-/

open Matrix MeasureTheory Real

namespace Miao.LinearQuadratic

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- The normal density with mean `w` and covariance `Σ` on `ℝ^{nε}`. -/
noncomputable def rcGaussPdf (w : E → ℝ) (Sg : Matrix E E ℝ) (e : E → ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) ^ Fintype.card E)⁻¹ * (Real.sqrt Sg.det)⁻¹ *
    exp (-(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))))

omit [DecidableEq E] in
/-- The standard normal density `π`. -/
noncomputable def rcStdPdf (e : E → ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) ^ Fintype.card E)⁻¹ * exp (-(1 / 2) * (e ⬝ᵥ e))

/-- `π` is the normal density with mean `0` and covariance `I`. -/
theorem rcStdPdf_eq (e : E → ℝ) : rcStdPdf e = rcGaussPdf 0 1 e := by
  simp [rcStdPdf, rcGaussPdf]

/-- Miao, p. 323: the log likelihood ratio of normals,
`ln(π̂(ε)/π(ε)) = ½(−(ε − w)'Σ⁻¹(ε − w) + ε'ε − ln det Σ)`. -/
theorem rc_llr_normal {Sg : Matrix E E ℝ} (hS : Sg.PosDef) (w e : E → ℝ) :
    log (rcGaussPdf w Sg e / rcStdPdf e) =
      1 / 2 * (-((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + e ⬝ᵥ e - log Sg.det) := by
  have hdet := hS.det_pos
  have hs : 0 < Real.sqrt Sg.det := Real.sqrt_pos.2 hdet
  have hc : 0 < (Real.sqrt (2 * Real.pi) ^ Fintype.card E)⁻¹ := by positivity
  have h : rcGaussPdf w Sg e / rcStdPdf e = (Real.sqrt Sg.det)⁻¹ *
      exp (-(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) - -(1 / 2) * (e ⬝ᵥ e)) := by
    rw [rcGaussPdf, rcStdPdf, exp_sub]
    field_simp
  rw [h, Real.log_mul (inv_pos.2 hs).ne' (exp_pos _).ne', Real.log_inv, Real.log_sqrt hdet.le,
    log_exp]
  ring

/-- A law on `ℝ^{nε}` with mean `w` and covariance `Σ` (integrable second moments). -/
structure RCMoments (ν : Measure (E → ℝ)) (w : E → ℝ) (Sg : Matrix E E ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  int1 : ∀ k, Integrable (fun e : E → ℝ => e k) ν
  int2 : ∀ k l, Integrable (fun e : E → ℝ => e k * e l) ν
  mean : ∀ k, ∫ e, e k ∂ν = w k
  cov : ∀ k l, ∫ e, (e k - w k) * (e l - w l) ∂ν = Sg k l

omit [DecidableEq E] in
/-- `E(z + C(ε − w))'P(z + C(ε − w)) = z'Pz + tr(C'PCΣ)` under a law with mean `w` and covariance
`Σ`. -/
theorem rc_moment_quad {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) (z : X → ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Integrable (fun e : E → ℝ => (z + C *ᵥ (e - w)) ⬝ᵥ (P *ᵥ (z + C *ᵥ (e - w)))) ν ∧
      ∫ e, (z + C *ᵥ (e - w)) ⬝ᵥ (P *ᵥ (z + C *ᵥ (e - w))) ∂ν =
        z ⬝ᵥ (P *ᵥ z) + trace (Cᵀ * P * C * Sg) := by
  have := hν.prob
  simp only [ls_quad_shock_expand]
  have i1 : ∀ k, Integrable (fun e : E → ℝ => (e - w) k) ν := fun k =>
    (hν.int1 k).sub (integrable_const (w k))
  have i2 : ∀ k l, Integrable (fun e : E → ℝ => (e - w) k * (e - w) l) ν := fun k l => by
    have h : (fun e : E → ℝ => (e - w) k * (e - w) l) = fun e => e k * e l - w l * e k -
        w k * e l + w k * w l := by
      funext e; simp only [Pi.sub_apply]; ring
    rw [h]
    exact (((hν.int2 k l).sub ((hν.int1 k).const_mul _)).sub ((hν.int1 l).const_mul _)).add
      (integrable_const _)
  have m1 : ∀ k, ∫ e, (e - w) k ∂ν = 0 := fun k => by
    simp only [Pi.sub_apply]
    rw [integral_sub (hν.int1 k) (integrable_const _), hν.mean, integral_const, probReal_univ,
      one_smul, sub_self]
  have m2 : ∀ k l, ∫ e, (e - w) k * (e - w) l ∂ν = Sg k l := fun k l => by
    simp only [Pi.sub_apply]
    exact hν.cov k l
  have hSs : ∀ k l, Sg l k = Sg k l := fun k l => by
    rw [← m2, ← m2]; congr 1; funext e; ring
  set cf := z ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ z)
  have hlin : Integrable (fun e : E → ℝ => ∑ k, cf k * (e - w) k) ν :=
    integrable_finsetSum _ fun k _ => (i1 k).const_mul _
  have hq : Integrable (fun e : E → ℝ => ∑ k, ∑ l, (Cᵀ * P * C) k l * ((e - w) k * (e - w) l))
      ν := integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (i2 k l).const_mul _
  have hcl : Integrable (fun e : E → ℝ => z ⬝ᵥ (P *ᵥ z) + ∑ k, cf k * (e - w) k) ν :=
    (integrable_const _).add hlin
  refine ⟨hcl.add hq, ?_⟩
  have hlin0 : ∫ e, ∑ k, cf k * (e - w) k ∂ν = 0 := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => cf k * (e - w) k) _
      fun k _ => (i1 k).const_mul _]
    simp only [integral_const_mul, m1, mul_zero, Finset.sum_const_zero]
  have hrow : ∀ k, ∫ e, ∑ l, (Cᵀ * P * C) k l * ((e - w) k * (e - w) l) ∂ν =
      ∑ l, (Cᵀ * P * C) k l * Sg l k := by
    intro k
    rw [integral_finsetSum (f := fun l (e : E → ℝ) => (Cᵀ * P * C) k l *
      ((e - w) k * (e - w) l)) _ fun l _ => (i2 k l).const_mul _]
    simp only [integral_const_mul, m2, hSs]
  have hq0 : ∫ e, ∑ k, ∑ l, (Cᵀ * P * C) k l * ((e - w) k * (e - w) l) ∂ν =
      trace (Cᵀ * P * C * Sg) := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => ∑ l, (Cᵀ * P * C) k l *
      ((e - w) k * (e - w) l)) _ fun k _ => integrable_finsetSum _ fun l _ =>
        (i2 k l).const_mul _]
    simp only [hrow]
    rfl
  rw [integral_add hcl hq, integral_add (integrable_const _) hlin, integral_const, hlin0, hq0,
    probReal_univ, one_smul, add_zero]

/-- Miao, p. 323: `∫(ε − w)'Σ⁻¹(ε − w)π̂(ε)dε = tr(I)`. -/
theorem rc_moment_trace_inv {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) (hSu : IsUnit Sg.det) :
    Integrable (fun e : E → ℝ => (e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) ν ∧
      ∫ e, (e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w)) ∂ν = trace (1 : Matrix E E ℝ) := by
  have h := rc_moment_quad hν (0 : E → ℝ) (1 : Matrix E E ℝ) Sg⁻¹
  simp only [zero_add, one_mulVec, mulVec_zero, dotProduct_zero, transpose_one,
    Matrix.one_mul, Matrix.mul_one, nonsing_inv_mul _ hSu] at h
  exact h

/-- Miao, p. 323 (corrected sign): `−½∫(ε − w)'Σ⁻¹(ε − w)π̂(ε)dε = −½ tr(I)`. -/
theorem rc_moment_half {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) (hSu : IsUnit Sg.det) :
    -∫ e, 1 / 2 * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) ∂ν = -(1 / 2) * trace (1 : Matrix E E ℝ) := by
  rw [integral_const_mul, (rc_moment_trace_inv hν hSu).2]
  ring

omit [Fintype E] in
/-- The sign printed on p. 323 (`+½ tr(I)`) is wrong whenever `nε ≥ 1`. -/
theorem rc_moment_sign_misprint [Fintype E] [Nonempty E] :
    -(1 / 2) * trace (1 : Matrix E E ℝ) ≠ 1 / 2 * trace (1 : Matrix E E ℝ) := by
  rw [trace_one]
  have : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  intro h
  linarith

omit [Fintype E] [DecidableEq E] in
/-- Miao, p. 323: `½ε'ε = ½w'w + ½(ε − w)'(ε − w) + w'(ε − w)`. -/
theorem rc_half_sq_split [Fintype E] (w e : E → ℝ) :
    1 / 2 * (e ⬝ᵥ e) = 1 / 2 * (w ⬝ᵥ w) + 1 / 2 * ((e - w) ⬝ᵥ (e - w)) + w ⬝ᵥ (e - w) := by
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm w e]
  ring

omit [DecidableEq E] in
/-- Miao, p. 324: `½∫ε'επ̂(ε)dε = ½w'w + ½ tr(Σ)`. -/
theorem rc_half_sq_moment {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) :
    Integrable (fun e : E → ℝ => e ⬝ᵥ e) ν ∧
      ∫ e, 1 / 2 * (e ⬝ᵥ e) ∂ν = 1 / 2 * (w ⬝ᵥ w) + 1 / 2 * trace Sg := by
  classical
  have h := rc_moment_quad hν w (1 : Matrix E E ℝ) (1 : Matrix E E ℝ)
  simp only [one_mulVec, add_sub_cancel, transpose_one, Matrix.one_mul] at h
  refine ⟨h.1, ?_⟩
  rw [integral_const_mul, h.2]
  ring

/-- **(9.56)** (Miao, p. 324): for the standard normal `π` and the normal `π̂` with mean `w` and
covariance `Σ > 0`, `∫π̂ ln(π̂/π) = ½w'w − ½ ln det Σ + ½ tr(Σ − I)` (the integral taken against
any law with mean `w` and covariance `Σ`, in particular `N(w, Σ)`). -/
theorem eq_9_56 {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ} (hν : RCMoments ν w Sg)
    (hS : Sg.PosDef) :
    ∫ e, log (rcGaussPdf w Sg e / rcStdPdf e) ∂ν =
      1 / 2 * (w ⬝ᵥ w) - 1 / 2 * log Sg.det + 1 / 2 * trace (Sg - 1) := by
  have := hν.prob
  have hSu := (isUnit_iff_isUnit_det _).1 hS.isUnit
  obtain ⟨i1, h1⟩ := rc_moment_trace_inv hν hSu
  obtain ⟨i2, h2⟩ := rc_half_sq_moment hν
  simp only [rc_llr_normal hS]
  have e1 : ∀ e : E → ℝ, 1 / 2 * (-((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + e ⬝ᵥ e - log Sg.det) =
      -(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + 1 / 2 * (e ⬝ᵥ e) - 1 / 2 * log Sg.det :=
    fun e => by ring
  simp only [e1]
  rw [integral_sub (f := fun e => -(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + 1 / 2 * (e ⬝ᵥ e))
      ((i1.const_mul _).add (i2.const_mul _)) (integrable_const _),
    integral_add (f := fun e => -(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))))
      (i1.const_mul _) (i2.const_mul _), integral_const_mul, h1, h2, integral_const,
    probReal_univ, one_smul, trace_sub]
  ring

omit [DecidableEq E] in
/-- Miao, p. 321: the worst-case likelihood ratio for `V = −½z'Pz − d/2`:
`exp(−V(y + Cε)/θ) = exp((y'Py + d)/(2θ)) exp(ε'C'PCε/(2θ) + ε'C'Py/θ)`. -/
theorem rc_worst_ratio {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (y : X → ℝ) (d : ℝ) (e : E → ℝ) :
    exp (-rcV P d (y + C *ᵥ e) / θ) = exp ((y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ)) *
      exp (1 / (2 * θ) * (e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e)) + θ⁻¹ * (e ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)))) := by
  rw [← exp_add, rc_exponent hθ hP, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, dotProduct_comm (Cᵀ *ᵥ (P *ᵥ y)) e]
  congr 1
  field_simp
  ring

/-- Miao, p. 321: the exponent of `π m*`,
`−½ε'ε + ε'C'PCε/(2θ) + ε'C'Py/θ = −½ε'Kε + ε'K(θI − C'PC)⁻¹C'Py`, `K = I − θ⁻¹C'PC`. -/
theorem rc_worst_exponent {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hH : IsUnit (rcH θ C P).det) (y : X → ℝ) (e : E → ℝ) :
    -(1 / 2) * (e ⬝ᵥ e) + 1 / (2 * θ) * (e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e)) +
        θ⁻¹ * (e ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y))) =
      -(1 / 2) * (e ⬝ᵥ (rcK θ C P *ᵥ e)) + e ⬝ᵥ (rcK θ C P *ᵥ rcWstar θ C P y) := by
  have hKw : rcK θ C P *ᵥ rcWstar θ C P y = θ⁻¹ • (Cᵀ *ᵥ (P *ᵥ y)) := by
    rw [rcK_eq_smul hθ, smul_mulVec, rcWstar, mulVec_mulVec, mul_nonsing_inv _ hH, one_mulVec]
  rw [hKw, rcK, sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- Miao, p. 321: the worst-case distorted density `π*(ε) = π(ε)m*(ε)` is proportional to the
normal density with mean `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` and covariance `(I − θ⁻¹C'PC)⁻¹`
(here `y = Ax + Bu`), when `θI − C'PC > 0`. -/
theorem rc_worst_density {θ : ℝ} (hθ : 0 < θ) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ) (d : ℝ) :
    ∃ k : ℝ, 0 < k ∧ ∀ e, rcStdPdf e * exp (-rcV P d (y + C *ᵥ e) / θ) =
      k * rcGaussPdf (rcWstar θ C P y) (rcK θ C P)⁻¹ e := by
  have hK := (rcK_posDef_iff hθ C P).2 hH
  have hKu := (isUnit_iff_isUnit_det _).1 hK.isUnit
  have hKs := (SS.LQProblem.posDef_iff_real.1 hK).1
  have hHu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hdet : 0 < (rcK θ C P)⁻¹.det := hK.inv.det_pos
  set ws := rcWstar θ C P y
  set c0 := (y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ)
  refine ⟨exp (1 / 2 * (ws ⬝ᵥ (rcK θ C P *ᵥ ws)) + c0) * Real.sqrt (rcK θ C P)⁻¹.det,
    mul_pos (exp_pos _) (Real.sqrt_pos.2 hdet), fun e => ?_⟩
  have hq : (e - ws) ⬝ᵥ (rcK θ C P *ᵥ (e - ws)) = e ⬝ᵥ (rcK θ C P *ᵥ e) -
      2 * (e ⬝ᵥ (rcK θ C P *ᵥ ws)) + ws ⬝ᵥ (rcK θ C P *ᵥ ws) := by
    rw [sub_eq_add_neg, SS.LQProblem.quad_add hKs]
    simp only [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
    rw [SS.LQProblem.dotProduct_mulVec_comm_of_symm hKs ws e]
    ring
  have hexp : -(1 / 2) * (e ⬝ᵥ e) + -rcV P d (y + C *ᵥ e) / θ =
      -(1 / 2) * ((e - ws) ⬝ᵥ (rcK θ C P *ᵥ (e - ws))) +
        (1 / 2 * (ws ⬝ᵥ (rcK θ C P *ᵥ ws)) + c0) := by
    have h1 := rc_worst_exponent hθ.ne' hHu y e
    have h2 : -rcV P d (y + C *ᵥ e) / θ = 1 / (2 * θ) * (e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e)) +
        θ⁻¹ * (e ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y))) + c0 := by
      simp only [c0]
      rw [rc_exponent hθ.ne' hP, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        smul_eq_mul, dotProduct_comm (Cᵀ *ᵥ (P *ᵥ y)) e]
      field_simp
    rw [h2, hq]
    linear_combination h1
  have hs : 0 < Real.sqrt (rcK θ C P)⁻¹.det := Real.sqrt_pos.2 hdet
  rw [rcStdPdf, rcGaussPdf, nonsing_inv_nonsing_inv _ hKu, mul_assoc, ← exp_add, hexp, exp_add]
  field_simp

/-- Correction to p. 321: nonsingularity of `I − θ⁻¹C'PC` is not enough. With `θ = 1`, `C = 1`,
`P = 2` (scalar), `I − θ⁻¹C'PC = −1` is nonsingular, but the worst-case kernel
`π(ε) exp(−V(Cε)/θ) ∝ exp(−ε²/2) exp(ε²)` is not integrable: the minimising agent drives the
objective to `−∞` (the breakdown point); `I − θ⁻¹C'PC` must be positive definite. -/
theorem rc_nonsingular_not_enough :
    (1 : ℝ) - 1⁻¹ * 2 ≠ 0 ∧
      ¬ Integrable (fun e : ℝ => exp (-(1 / 2) * e ^ 2) * exp (e ^ 2)) volume := by
  refine ⟨by norm_num, ?_⟩
  have h : (fun e : ℝ => exp (-(1 / 2) * e ^ 2) * exp (e ^ 2)) =
      fun e => exp (-(-(1 / 2)) * e ^ 2) := by
    funext e
    rw [← exp_add]
    ring_nf
  rw [h, integrable_exp_neg_mul_sq_iff]
  norm_num

/-- Miao, p. 322: `R(V)` from the first line of (9.48). Under the worst-case law `π*` (mean
`w* = (θI − C'PC)⁻¹C'Py`, covariance `K⁻¹`), `∫V(y + Cε)π* + θ∫π* ln(π*/π) =
−½y'D(P)y − d/2 − (θ/2) ln det K⁻¹`. -/
theorem rc_R_first_line {ν : Measure (E → ℝ)} {θ : ℝ} (hθ : 0 < θ) {C : Matrix X E ℝ}
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ) (d : ℝ)
    (hν : RCMoments ν (rcWstar θ C P y) (rcK θ C P)⁻¹) :
    ∫ e, rcV P d (y + C *ᵥ e) ∂ν +
        θ * ∫ e, log (rcGaussPdf (rcWstar θ C P y) (rcK θ C P)⁻¹ e / rcStdPdf e) ∂ν =
      -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) - d / 2 - θ / 2 * log (rcK θ C P)⁻¹.det := by
  have := hν.prob
  have hK := (rcK_posDef_iff hθ C P).2 hH
  have hKu := (isUnit_iff_isUnit_det _).1 hK.isUnit
  have hHu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  set ws := rcWstar θ C P y
  have hy : ∀ e : E → ℝ, y + C *ᵥ e = (y + C *ᵥ ws) + C *ᵥ (e - ws) := fun e => by
    rw [mulVec_sub]; abel
  obtain ⟨hi, hq⟩ := rc_moment_quad hν (y + C *ᵥ ws) C P
  have hV : ∫ e, rcV P d (y + C *ᵥ e) ∂ν = -(1 / 2) * ((y + C *ᵥ ws) ⬝ᵥ (P *ᵥ (y + C *ᵥ ws)) +
      trace (Cᵀ * P * C * (rcK θ C P)⁻¹)) - d / 2 := by
    have hfun : (fun e => rcV P d (y + C *ᵥ e)) = fun e =>
        -(1 / 2) * (((y + C *ᵥ ws) + C *ᵥ (e - ws)) ⬝ᵥ (P *ᵥ ((y + C *ᵥ ws) + C *ᵥ (e - ws)))) -
          d / 2 := funext fun e => by rw [rcV, hy e]
    rw [hfun, integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul, hq,
      integral_const, probReal_univ, one_smul]
  have hCPC : Cᵀ * P * C = θ • (1 - rcK θ C P) := by
    rw [rcK, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
  have htr : trace (Cᵀ * P * C * (rcK θ C P)⁻¹) =
      θ * (trace (rcK θ C P)⁻¹ - trace (1 : Matrix E E ℝ)) := by
    rw [hCPC, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, mul_nonsing_inv _ hKu, trace_smul,
      trace_sub, smul_eq_mul]
  have hmce := rc_mce_decomp (θ := θ) (C := C) hP hHu y ws
  rw [sub_self, mulVec_zero, dotProduct_zero, mul_zero, add_zero] at hmce
  rw [hV, eq_9_56 hν hK.inv, htr, trace_sub]
  linear_combination hmce

/-- The two lines of (9.48) agree for the quadratic value function (Miao, p. 322, "Alternatively,
we can compute this adjustment directly using the expression in the second line"). -/
theorem rc_R_lines_agree {ν ν' : Measure (E → ℝ)} (hν : RCGaussian ν) {θ : ℝ} (hθ : 0 < θ)
    {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ)
    (d : ℝ) (hν' : RCMoments ν' (rcWstar θ C P y) (rcK θ C P)⁻¹) :
    ∫ e, rcV P d (y + C *ᵥ e) ∂ν' +
        θ * ∫ e, log (rcGaussPdf (rcWstar θ C P y) (rcK θ C P)⁻¹ e / rcStdPdf e) ∂ν' =
      rcR ν (fun e => rcV P d (y + C *ᵥ e)) θ := by
  rw [rc_R_first_line hθ hP hH y d hν', (rc_R_quad hν hθ hP hH y d).2]

end Miao.LinearQuadratic
