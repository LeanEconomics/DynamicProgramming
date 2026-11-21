/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSFiniteHorizon
import LinearQuadratic.RCGibbs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix

/-!
# The linear-quadratic robust control problem

Miao, §9.6, pp. 321–325 ("Linear Quadratic Model with Gaussian Disturbances" and "Modified
Certainty Equivalence Principle"). The data are those of §9.3 (`LSProblem`: `A, B, C, Q, R, S, β`)
in the normalisation of §9.6: the return is `r(x, u) = −½(x'Qx + u'Ru + 2x'Su) = −½ loss` and the
value function is `V(x) = −½x'Px − d/2` (9.50) (`rcV`). For `θ > 0` set

* `H = θI − C'PC` (`rcH`) and `K = I − θ⁻¹C'PC = θ⁻¹H` (`rcK`);
* the operator `D(P) = P + PC(θI − C'PC)⁻¹C'P` (`rcD`);
* the worst-case mean distortion `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` (`rcWstar`);
* `d = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'PC)⁻¹` (9.55) (`rcd`).

Results.

* `rc_mce_decomp`, `rc_mce` (p. 324, the deterministic minimisation of the modified certainty
  equivalence principle): `−½(y + Cw)'P(y + Cw) + (θ/2)w'w = −½y'D(P)y + ½(w − w*)'H(w − w*)`,
  so for `H > 0` the minimum over `w` is `−½y'D(P)y`, uniquely at `w = w*`.
* `rc_breakdown` (p. 319, the breakdown point): if `H` has a direction of negative curvature the
  minimising agent pushes the objective to `−∞`.
* `RCGaussian`: the Gaussian moment generating identity
  `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)` for `I − K > 0`, which the
  standard normal shock satisfies; `rc_R_quad` (p. 322): for quadratic `V`,
  `R(V)(x, u) = −½(Ax + Bu)'D(P)(Ax + Bu) − d/2 − (θ/2) ln det(I − θ⁻¹C'PC)⁻¹`.
* `rc_robObj_eq` (p. 322): substituting into (9.49), the objective is
  `−½x'T(D(P))x − ½(u + Fx)'G(u + Fx) − βd/2 − (βθ/2) ln det K⁻¹` with `T` the operator (9.54) =
  (9.11) and `F` the gain (9.52).
* `eq_9_51_9_55`: if `P = T(D(P))` (9.53) and `d` is (9.55) then `V` solves the robust Bellman
  equation (9.49), with the unique maximiser `u = −Fx` (9.51)–(9.52); `rc_bellman_converse`:
  conversely (matching coefficients) the Bellman equation forces (9.53) and (9.55);
  `rc_robust_bellman`: with Gibbs' principle the inner problem is the minimisation over all
  likelihood ratios.
* `rc_modified_ce` (pp. 324–325): the deterministic robust problem with distorted mean `w` has the
  same `P` and the same decision rule; `rc_C_matters`: unlike the standard problem, `C` changes
  both `P` and the rule (a scalar example).

The results are stated for any shock law satisfying `RCGaussian`; the IID standard normal shock
satisfies it (`rc_gaussian_std` in `RCGaussianStd`, with the corollaries `eq_9_51_9_55_std`,
`rc_robust_bellman_std`).
-/

open Matrix MeasureTheory Real

namespace Miao.LinearQuadratic

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- `H = θI − C'PC`. -/
def rcH (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : Matrix E E ℝ := θ • 1 - Cᵀ * P * C

/-- `K = I − θ⁻¹C'PC`. -/
noncomputable def rcK (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : Matrix E E ℝ :=
  1 - θ⁻¹ • (Cᵀ * P * C)

/-- The operator `D(P) = P + PC(θI − C'PC)⁻¹C'P` (Miao, p. 322). -/
noncomputable def rcD (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  P + P * C * (rcH θ C P)⁻¹ * Cᵀ * P

/-- The worst-case mean distortion `w* = (θI − C'PC)⁻¹C'Py` (Miao, pp. 321, 324). -/
noncomputable def rcWstar (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) (y : X → ℝ) : E → ℝ :=
  (rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y))

/-- The quadratic value function (9.50): `V(x) = −½x'Px − d/2`. -/
noncomputable def rcV (P : Matrix X X ℝ) (d : ℝ) (x : X → ℝ) : ℝ :=
  -(1 / 2) * (x ⬝ᵥ (P *ᵥ x)) - d / 2

/-- The constant (9.55): `d = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'PC)⁻¹`. -/
noncomputable def rcd (β θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : ℝ :=
  (1 - β)⁻¹ * (β * θ * log (rcK θ C P)⁻¹.det)

omit [Fintype E] in
theorem rcH_transpose {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (rcH θ C P)ᵀ = rcH θ C P := by
  simp [rcH, transpose_sub, transpose_smul, transpose_one, transpose_mul, hP, Matrix.mul_assoc]

omit [Fintype E] in
theorem rcK_eq_smul {θ : ℝ} (hθ : θ ≠ 0) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    rcK θ C P = θ⁻¹ • rcH θ C P := by
  simp [rcK, rcH, smul_sub, smul_smul, inv_mul_cancel₀ hθ]

omit [Fintype E] in
theorem rcH_eq_smul {θ : ℝ} (hθ : θ ≠ 0) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    rcH θ C P = θ • rcK θ C P := by
  rw [rcK_eq_smul hθ, smul_smul, mul_inv_cancel₀ hθ, one_smul]

omit [Fintype E] in
theorem rcK_posDef_iff {θ : ℝ} (hθ : 0 < θ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    (rcK θ C P).PosDef ↔ (rcH θ C P).PosDef :=
  ⟨fun h => by rw [rcH_eq_smul hθ.ne']; exact h.smul hθ,
    fun h => by rw [rcK_eq_smul hθ.ne']; exact h.smul (inv_pos.2 hθ)⟩

theorem rcK_inv {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hH : IsUnit (rcH θ C P).det) : (rcK θ C P)⁻¹ = θ • (rcH θ C P)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [rcK_eq_smul hθ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hθ, one_smul,
    nonsing_inv_mul _ hH]

theorem rcD_transpose {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (rcD θ C P)ᵀ = rcD θ C P := by
  simp [rcD, transpose_add, transpose_mul, transpose_nonsing_inv, rcH_transpose hP, hP,
    Matrix.mul_assoc]

/-- `y'D(P)y = y'Py + (C'Py)'(θI − C'PC)⁻¹(C'Py)`. -/
theorem rcD_quad {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (y : X → ℝ) :
    y ⬝ᵥ (rcD θ C P *ᵥ y) = y ⬝ᵥ (P *ᵥ y) +
      (Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y))) := by
  rw [rcD, add_mulVec, dotProduct_add]
  congr 1
  simp only [← mulVec_mulVec]
  rw [SS.LQProblem.dotProduct_mulVec_comm_of_symm hP, SS.LQProblem.mulVec_dotProduct,
    dotProduct_comm]

/-- `D(P) ≥ 0` for `P ≥ 0` and `θI − C'PC > 0`. -/
theorem rcD_posSemidef {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hH : (rcH θ C P).PosDef) : (rcD θ C P).PosSemidef := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP)
  have hHi := SS.LQProblem.posSemidef_iff_real.1 hH.inv.posSemidef
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨rcD_transpose hPs.1, fun y => ?_⟩
  rw [rcD_quad hPs.1]
  exact add_nonneg (hPs.2 y) (hHi.2 _)

/-- Expanding the deterministic robust objective:
`−½(y + Cw)'P(y + Cw) + (θ/2)w'w = −½y'Py − w'C'Py + ½w'(θI − C'PC)w`. -/
theorem rc_mce_expand {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (y : X → ℝ) (w : E → ℝ) :
    -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w) =
      -(1 / 2) * (y ⬝ᵥ (P *ᵥ y)) - w ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)) +
        1 / 2 * (w ⬝ᵥ (rcH θ C P *ᵥ w)) := by
  have e1 := SS.LQProblem.quad_add hP y (C *ᵥ w)
  have e2 : (C *ᵥ w) ⬝ᵥ (P *ᵥ y) = w ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)) :=
    SS.LQProblem.mulVec_dotProduct C w (P *ᵥ y)
  have e3 : (C *ᵥ w) ⬝ᵥ (P *ᵥ (C *ᵥ w)) = w ⬝ᵥ ((Cᵀ * P * C) *ᵥ w) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul C P w).symm
  have e4 : w ⬝ᵥ (rcH θ C P *ᵥ w) = θ * (w ⬝ᵥ w) - w ⬝ᵥ ((Cᵀ * P * C) *ᵥ w) := by
    rw [rcH, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [e1, e2, e3, e4]
  ring

/-- Miao, p. 324: completing the square in the distortion,
`−½(y + Cw)'P(y + Cw) + (θ/2)w'w = −½y'D(P)y + ½(w − w*)'(θI − C'PC)(w − w*)`. -/
theorem rc_mce_decomp {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (hH : IsUnit (rcH θ C P).det) (y : X → ℝ) (w : E → ℝ) :
    -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w) =
      -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) +
        1 / 2 * ((w - rcWstar θ C P y) ⬝ᵥ (rcH θ C P *ᵥ (w - rcWstar θ C P y))) := by
  set a := Cᵀ *ᵥ (P *ᵥ y) with ha
  have hsq := LSProblem.ls_sq_complete (rcH_transpose (θ := θ) (C := C) hP) hH w (-a)
  have e5 : w + (rcH θ C P)⁻¹ *ᵥ (-a) = w - rcWstar θ C P y := by
    rw [mulVec_neg, ← sub_eq_add_neg, rcWstar]
  have e6 : (-a) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (-a)) = a ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ a) := by
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [e5, e6, dotProduct_neg] at hsq
  rw [rc_mce_expand hP, rcD_quad hP, ← ha]
  linear_combination (1 / 2) * hsq

/-- **Modified certainty equivalence** (Miao, p. 324): for `θI − C'PC > 0` the minimum of
`−½(y + Cw)'P(y + Cw) + (θ/2)w'w` over `w` is `−½y'D(P)y`, attained exactly at
`w* = (θI − C'PC)⁻¹C'Py`, the mean of the worst-case normal distribution. -/
theorem rc_mce {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (hH : (rcH θ C P).PosDef) (y : X → ℝ) :
    IsLeast (Set.range fun w : E → ℝ =>
        -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w))
        (-(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y))) ∧
      ∀ w, -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w) =
          -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) ↔ w = rcWstar θ C P y := by
  have hu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hH' := SS.LQProblem.posDef_iff_real.1 hH
  have hq := (SS.LQProblem.posSemidef_iff_real.1 hH.posSemidef).2
  refine ⟨⟨⟨rcWstar θ C P y, ?_⟩, ?_⟩, fun w => ?_⟩
  · simp only
    rw [rc_mce_decomp hP hu, sub_self, mulVec_zero, dotProduct_zero, mul_zero, add_zero]
  · rintro _ ⟨w, rfl⟩
    simp only
    rw [rc_mce_decomp hP hu]
    linarith [hq (w - rcWstar θ C P y)]
  · rw [rc_mce_decomp hP hu, add_eq_left, mul_eq_zero]
    constructor
    · rintro (h | h)
      · norm_num at h
      · by_contra hne
        exact absurd h (hH'.2 (sub_ne_zero.2 hne)).ne'
    · rintro rfl
      right
      rw [sub_self, mulVec_zero, dotProduct_zero]

/-- The breakdown point (Miao, p. 319): if `θI − C'PC` has a direction `v` of negative curvature,
the minimising agent can push `−½(y + Cw)'P(y + Cw) + (θ/2)w'w` to `−∞`. -/
theorem rc_breakdown {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (y : X → ℝ)
    {v : E → ℝ} (hv : v ⬝ᵥ (rcH θ C P *ᵥ v) < 0) :
    ¬ BddBelow (Set.range fun w : E → ℝ =>
        -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w)) := by
  rintro ⟨b, hb⟩
  set c0 := -(1 / 2) * (y ⬝ᵥ (P *ᵥ y))
  set c1 := -(v ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)))
  set c2 := 1 / 2 * (v ⬝ᵥ (rcH θ C P *ᵥ v))
  have hc2 : c2 < 0 := by simp only [c2]; linarith
  have hval : ∀ t : ℝ, -(1 / 2) * ((y + C *ᵥ (t • v)) ⬝ᵥ (P *ᵥ (y + C *ᵥ (t • v)))) +
      θ / 2 * ((t • v) ⬝ᵥ (t • v)) = c0 + c1 * t + c2 * t ^ 2 := by
    intro t
    rw [rc_mce_expand hP]
    simp only [c0, c1, c2, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  set S := |c0| + |c1| + |b| + 1
  set M := S / (-c2) + 1
  have hS : 0 < S := by positivity
  have hMdef : M = S / (-c2) + 1 := rfl
  have hM1 : 1 ≤ M := by
    have : 0 ≤ S / (-c2) := div_nonneg hS.le (by linarith)
    rw [hMdef]
    linarith
  have hcM : -c2 * M ≥ S := by
    have h1 : -c2 * (S / (-c2)) = S := mul_div_cancel₀ S (by linarith)
    rw [hMdef, mul_add, h1]
    linarith
  have hc2M : c2 * M ^ 2 ≤ -S * M := by nlinarith
  have h0 : c0 ≤ |c0| * M := (le_abs_self c0).trans (le_mul_of_one_le_right (abs_nonneg _) hM1)
  have h1 : c1 * M ≤ |c1| * M := mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith)
  have hlt : c0 + c1 * M + c2 * M ^ 2 < b := by
    have : c0 + c1 * M + c2 * M ^ 2 ≤ -(|b| + 1) * M := by
      simp only [S] at hc2M
      nlinarith
    have hbM : -(|b| + 1) * M ≤ -(|b| + 1) := by nlinarith [abs_nonneg b]
    linarith [neg_abs_le b]
  have h' : b ≤ c0 + c1 * M + c2 * M ^ 2 := by
    have := hb ⟨M • v, rfl⟩
    simpa only [hval] using this
  linarith

/-- The Gaussian moment generating identity of the standard normal shock: for symmetric `K` with
`I − K > 0`, `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)`. -/
structure RCGaussian (ν : Measure (E → ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  integrable : ∀ (K : Matrix E E ℝ) (b : E → ℝ), Kᵀ = K → (1 - K).PosDef →
    Integrable (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ν
  mgf : ∀ (K : Matrix E E ℝ) (b : E → ℝ), Kᵀ = K → (1 - K).PosDef →
    ∫ e, exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e) ∂ν =
      (Real.sqrt (1 - K).det)⁻¹ * exp (1 / 2 * (b ⬝ᵥ ((1 - K)⁻¹ *ᵥ b)))

omit [DecidableEq E] in
/-- The exponent of the worst-case likelihood ratio (Miao, p. 321): for `V = −½z'Pz − d/2`,
`−V(y + Cε)/θ = ½ε'(θ⁻¹C'PC)ε + (θ⁻¹C'Py)'ε + (y'Py + d)/(2θ)`. -/
theorem rc_exponent {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (y : X → ℝ) (d : ℝ) (e : E → ℝ) :
    -rcV P d (y + C *ᵥ e) / θ = 1 / 2 * (e ⬝ᵥ ((θ⁻¹ • (Cᵀ * P * C)) *ᵥ e)) +
      (θ⁻¹ • (Cᵀ *ᵥ (P *ᵥ y))) ⬝ᵥ e + (y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ) := by
  have e1 := SS.LQProblem.quad_add hP y (C *ᵥ e)
  have e2 : (C *ᵥ e) ⬝ᵥ (P *ᵥ y) = (Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ e := by
    rw [SS.LQProblem.mulVec_dotProduct, dotProduct_comm]
  have e3 : (C *ᵥ e) ⬝ᵥ (P *ᵥ (C *ᵥ e)) = e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul C P e).symm
  rw [rcV, e1, e2, e3, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- Miao, p. 322: for the quadratic value function and Gaussian shocks, `E exp(−V(f)/θ) < ∞` and
`R(V)(x, u) = −½y'D(P)y − d/2 − (θ/2) ln det(I − θ⁻¹C'PC)⁻¹`, `y = Ax + Bu` (computed from the
second line of (9.48)). -/
theorem rc_R_quad {ν : Measure (E → ℝ)} (hν : RCGaussian ν) {θ : ℝ} (hθ : 0 < θ)
    {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ)
    (d : ℝ) :
    Integrable (fun e => exp (-rcV P d (y + C *ᵥ e) / θ)) ν ∧
      rcR ν (fun e => rcV P d (y + C *ᵥ e)) θ =
        -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) - d / 2 - θ / 2 * log (rcK θ C P)⁻¹.det := by
  set K' : Matrix E E ℝ := θ⁻¹ • (Cᵀ * P * C)
  set b : E → ℝ := θ⁻¹ • (Cᵀ *ᵥ (P *ᵥ y))
  set c0 : ℝ := (y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ)
  have hK's : K'ᵀ = K' := by
    simp [K', transpose_smul, transpose_mul, hP, Matrix.mul_assoc]
  have h1K : 1 - K' = rcK θ C P := rfl
  have hpos : (1 - K').PosDef := by rw [h1K]; exact (rcK_posDef_iff hθ C P).2 hH
  have hpt : (fun e => exp (-rcV P d (y + C *ᵥ e) / θ)) =
      fun e => exp c0 * exp (1 / 2 * (e ⬝ᵥ (K' *ᵥ e)) + b ⬝ᵥ e) := by
    funext e
    rw [rc_exponent hθ.ne' hP, ← exp_add]
    congr 1
    ring
  have hint := hν.integrable K' b hK's hpos
  refine ⟨by rw [hpt]; exact hint.const_mul _, ?_⟩
  have hdet : 0 < (rcK θ C P).det := ((rcK_posDef_iff hθ C P).2 hH).det_pos
  have hu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hb : b ⬝ᵥ ((1 - K')⁻¹ *ᵥ b) =
      θ⁻¹ * ((Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y)))) := by
    rw [h1K, rcK_inv hθ.ne' hu]
    simp only [b, smul_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
  have hZ : rcZ ν (fun e => rcV P d (y + C *ᵥ e)) θ =
      exp c0 * ((Real.sqrt (rcK θ C P).det)⁻¹ *
        exp (1 / 2 * (θ⁻¹ * ((Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y))))))) := by
    rw [rcZ, hpt, integral_const_mul, hν.mgf K' b hK's hpos, hb, h1K]
  have hsq : 0 < Real.sqrt (rcK θ C P).det := Real.sqrt_pos.2 hdet
  have hinvdet : (rcK θ C P)⁻¹.det = ((rcK θ C P).det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv']
  rw [rcR, hZ, Real.log_mul (exp_pos _).ne' (mul_pos (inv_pos.2 hsq) (exp_pos _)).ne',
    Real.log_mul (inv_pos.2 hsq).ne' (exp_pos _).ne', log_exp, log_exp, Real.log_inv,
    Real.log_sqrt hdet.le, hinvdet, Real.log_inv, rcD_quad hP]
  simp only [c0]
  field_simp
  ring

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The robust Bellman objective (9.49) with the quadratic value (9.50):
`r(x, u) + βR(V)(x, u)`, `r = −½ loss`. -/
noncomputable def rcRobObj (L : LSProblem X U E) (ν : Measure (E → ℝ)) (θ : ℝ)
    (P : Matrix X X ℝ) (d : ℝ) (x : X → ℝ) (u : U → ℝ) : ℝ :=
  -(1 / 2) * L.loss x u + L.β * rcR ν (fun e => rcV P d (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ

/-- The outer step: `−½r(x, u) − (β/2)(Ax + Bu)'D(P)(Ax + Bu) =
−½x'T(D(P))x − ½(u + Fx)'G(u + Fx)` with `F = F(D(P))` (9.52), `G = G(D(P))`. -/
theorem rc_outer_eq (L : LSProblem X U E) (hRs : L.Rᵀ = L.R) {θ : ℝ} {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (hG : IsUnit (L.G (rcD θ L.C P)).det) (x : X → ℝ) (u : U → ℝ) :
    -(1 / 2) * L.loss x u + L.β * (-(1 / 2) * ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ
        (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u)))) =
      -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) -
        1 / 2 * ((u + L.F (rcD θ L.C P) *ᵥ x) ⬝ᵥ
          (L.G (rcD θ L.C P) *ᵥ (u + L.F (rcD θ L.C P) *ᵥ x))) := by
  have h := L.loss_add_cont hRs (rcD_transpose hP) hG x u
  linear_combination (-1 / 2) * h

/-- Miao, p. 322: substituting (9.50) and `R(V)` into (9.49),
`r(x, u) + βR(V)(x, u) = −½x'T(D(P))x − ½(u + Fx)'G(u + Fx) − βd/2 − (βθ/2) ln det K⁻¹`. -/
theorem rc_robObj_eq (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hRs : L.Rᵀ = L.R) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (hH : (rcH θ L.C P).PosDef) (hG : IsUnit (L.G (rcD θ L.C P)).det) (d : ℝ) (x : X → ℝ)
    (u : U → ℝ) :
    rcRobObj L ν θ P d x u = -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) -
        1 / 2 * ((u + L.F (rcD θ L.C P) *ᵥ x) ⬝ᵥ
          (L.G (rcD θ L.C P) *ᵥ (u + L.F (rcD θ L.C P) *ᵥ x))) -
        L.β * (d / 2) - L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) := by
  rw [rcRobObj, (rc_R_quad hν hθ hP hH (L.A *ᵥ x + L.B *ᵥ u) d).2]
  have h := rc_outer_eq L hRs hP hG x u
  linear_combination h

/-- The maximum of the robust Bellman objective: `−½x'T(D(P))x − βd/2 − (βθ/2) ln det K⁻¹`,
attained exactly at `u = −F(D(P))x`. -/
theorem rc_robObj_max (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef) (d : ℝ) (x : X → ℝ) :
    IsGreatest (Set.range (rcRobObj L ν θ P d x))
        (-(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) - L.β * (d / 2) -
          L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det)) ∧
      ∀ u, rcRobObj L ν θ P d x u = -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) -
          L.β * (d / 2) - L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) ↔
        u = -(L.F (rcD θ L.C P) *ᵥ x) := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hGp := L.G_posDef hR (rcD_posSemidef hP hH) hβ
  have hG := (isUnit_iff_isUnit_det _).1 hGp.isUnit
  have hG' := SS.LQProblem.posDef_iff_real.1 hGp
  have hq := (SS.LQProblem.posSemidef_iff_real.1 hGp.posSemidef).2
  refine ⟨⟨⟨-(L.F (rcD θ L.C P) *ᵥ x), ?_⟩, ?_⟩, fun u => ?_⟩
  · rw [rc_robObj_eq L hν hRs hθ hPs hH hG, neg_add_cancel, mulVec_zero, dotProduct_zero]
    ring
  · rintro _ ⟨u, rfl⟩
    rw [rc_robObj_eq L hν hRs hθ hPs hH hG]
    linarith [hq (u + L.F (rcD θ L.C P) *ᵥ x)]
  · rw [rc_robObj_eq L hν hRs hθ hPs hH hG]
    constructor
    · intro h
      by_contra hne
      have : u + L.F (rcD θ L.C P) *ᵥ x ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      linarith [hG'.2 this]
    · rintro rfl
      rw [neg_add_cancel, mulVec_zero, dotProduct_zero]
      ring

/-- **(9.51)–(9.55)** (Miao, pp. 322–323): if `P ≥ 0` solves the robust Riccati equation
`P = T(D(P))` (9.53), with `T` the operator (9.54) of (9.11), and `d` is (9.55), then
`V(x) = −½x'Px − d/2` solves the robust Bellman equation (9.49) for Gaussian shocks, and the
robust decision rule `u = −Fx` (9.51), `F = (R + βB'D(P)B)⁻¹(S' + βB'D(P)A)` (9.52), is the unique
maximiser. -/
theorem eq_9_51_9_55 (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef) (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    IsGreatest (Set.range (rcRobObj L ν θ P (rcd L.β θ L.C P) x)) (rcV P (rcd L.β θ L.C P) x) ∧
      ∀ u, rcRobObj L ν θ P (rcd L.β θ L.C P) x u = rcV P (rcd L.β θ L.C P) x ↔
        u = -(L.F (rcD θ L.C P) *ᵥ x) := by
  have h := rc_robObj_max L hν hR hβ hθ hP hH (rcd L.β θ L.C P) x
  have hval : -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) - L.β * (rcd L.β θ L.C P / 2) -
      L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) = rcV P (rcd L.β θ L.C P) x := by
    have h1 : (1 - L.β) ≠ 0 := by linarith
    rw [hfix, rcV, rcd]
    field_simp
    ring
  rw [hval] at h
  exact h

/-- Matching coefficients (Miao, p. 322): if `V(x) = −½x'Px − d/2` solves the robust Bellman
equation for every `x`, then `P = T(D(P))` (9.53) and `d` is (9.55). -/
theorem rc_bellman_converse (L : LSProblem X U E) {ν : Measure (E → ℝ)}
    (hν : RCGaussian ν) (hQ : L.Qᵀ = L.Q) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1)
    {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    {d : ℝ} (hV : ∀ x, IsGreatest (Set.range (rcRobObj L ν θ P d x)) (rcV P d x)) :
    L.T (rcD θ L.C P) = P ∧ d = rcd L.β θ L.C P := by
  classical
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have heq : ∀ x, rcV P d x = -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) - L.β * (d / 2) -
      L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) :=
    fun x => (hV x).unique (rc_robObj_max L hν hR hβ hθ hP hH d x).1
  have h0 := heq 0
  simp only [rcV, mulVec_zero, dotProduct_zero, mul_zero] at h0
  have hd : d = rcd L.β θ L.C P := by
    have h1 : (1 - L.β) ≠ 0 := by linarith
    rw [rcd]
    field_simp
    linarith
  refine ⟨?_, hd⟩
  have hquad : ∀ x, x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := by
    intro x
    have := heq x
    simp only [rcV] at this
    linarith
  have hTs : (L.T (rcD θ L.C P))ᵀ = L.T (rcD θ L.C P) := L.T_transpose hQ hRs (rcD_transpose hPs)
  ext i j
  rw [ls_entry_eq_polar hTs, ls_entry_eq_polar hPs, hquad, hquad, hquad]

omit [DecidableEq E] in
theorem rcV_comp_measurable (P : Matrix X X ℝ) (d : ℝ) (y : X → ℝ) (C : Matrix X E ℝ) :
    Measurable fun e : E → ℝ => rcV P d (y + C *ᵥ e) := by
  have : Continuous fun e : E → ℝ => rcV P d (y + C *ᵥ e) := by
    unfold rcV
    fun_prop
  exact this.measurable

/-- **The robust Bellman equation** (Miao, pp. 320–323): under (9.53) and (9.55), for every `x`
the inner problem `min_m ∫(m V(Ax + Bu + Cε) + θ m ln m) π dε` over all likelihood ratios has a
value `w(u)` (namely `R(V)(x, u)`), and `V(x) = max_u {r(x, u) + βw(u)}`. -/
theorem rc_robust_bellman (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef) (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    ∃ w : (U → ℝ) → ℝ,
      (∀ u, IsLeast
        (rcObj ν (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ ''
          rcAdm ν (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ)
        (w u)) ∧
      IsGreatest (Set.range fun u => -(1 / 2) * L.loss x u + L.β * w u)
        (rcV P (rcd L.β θ L.C P) x) := by
  have := hν.prob
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  exact (eq_9_49 ν (fun x u => -(1 / 2) * L.loss x u)
    (fun x u e => L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) (rcV P (rcd L.β θ L.C P)) hθ
    (fun x u => rcV_comp_measurable _ _ _ _)
    (fun x u => (rc_R_quad hν hθ hPs hH (L.A *ᵥ x + L.B *ᵥ u) _).1) x).1
    (eq_9_51_9_55 L hν hR hβ hβ1 hθ hP hH hfix x).1

/-- **Modified certainty equivalence** (Miao, pp. 324–325): the deterministic robust problem
`V(x) = max_u min_w {r(x, u) + β(V(Ax + Bu + Cw) + (θ/2)w'w)}` with `V = −½x'Px` has the inner
value `−½(Ax + Bu)'D(P)(Ax + Bu)` at `w = w*`, and if `P = T(D(P))` the outer maximum is
`−½x'Px`, attained exactly at the same robust rule `u = −F(D(P))x` as the stochastic problem;
the worst-case covariance and the constant `d` play no role. -/
theorem rc_modified_ce (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {θ : ℝ}
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    (∀ u, IsLeast (Set.range fun w : E → ℝ =>
        rcV P 0 (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ w) + θ / 2 * (w ⬝ᵥ w))
        (-(1 / 2) * ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))))) ∧
      IsGreatest (Set.range fun u => -(1 / 2) * L.loss x u + L.β * (-(1 / 2) *
        ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))))) (rcV P 0 x) ∧
      ∀ u, -(1 / 2) * L.loss x u + L.β * (-(1 / 2) *
          ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u)))) = rcV P 0 x ↔
        u = -(L.F (rcD θ L.C P) *ᵥ x) := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hGp := L.G_posDef hR (rcD_posSemidef hP hH) hβ
  have hG := (isUnit_iff_isUnit_det _).1 hGp.isUnit
  have hG' := SS.LQProblem.posDef_iff_real.1 hGp
  have hq := (SS.LQProblem.posSemidef_iff_real.1 hGp.posSemidef).2
  have hV0 : ∀ z, rcV P 0 z = -(1 / 2) * (z ⬝ᵥ (P *ᵥ z)) := fun z => by simp [rcV]
  refine ⟨fun u => ?_, ⟨⟨-(L.F (rcD θ L.C P) *ᵥ x), ?_⟩, ?_⟩, fun u => ?_⟩
  · simp only [hV0]
    exact (rc_mce hPs hH _).1
  · simp only
    rw [rc_outer_eq L hRs hPs hG, neg_add_cancel, mulVec_zero, dotProduct_zero, hfix, hV0]
    ring
  · rintro _ ⟨u, rfl⟩
    simp only
    rw [rc_outer_eq L hRs hPs hG, hfix, hV0]
    linarith [hq (u + L.F (rcD θ L.C P) *ᵥ x)]
  · rw [rc_outer_eq L hRs hPs hG, hfix, hV0]
    constructor
    · intro h
      by_contra hne
      have : u + L.F (rcD θ L.C P) *ᵥ x ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      linarith [hG'.2 this]
    · rintro rfl
      rw [neg_add_cancel, mulVec_zero, dotProduct_zero]
      ring

/-- The inverse of a `1 × 1` matrix. -/
theorem rc_inv_fin_one (a : ℝ) : (!![a] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![a⁻¹] := by
  rw [Matrix.inv_def, adjugate_fin_one, det_fin_one_of, Ring.inverse_eq_inv']
  ext i j
  fin_cases i; fin_cases j
  simp

/-- The scalar problem of `rc_C_matters`: `A = B = R = 1`, `Q = 3/2`, `S = 0`, `β = 1/2`,
shock loading `c`. -/
noncomputable def rcScalarProblem (c : ℝ) : LSProblem (Fin 1) (Fin 1) (Fin 1) :=
  ⟨!![1], !![1], !![c], !![3 / 2], !![1], 0, 1 / 2⟩

/-- Miao, p. 325: unlike the standard problem, the volatility matrix `C` affects both the decision
rule and `P` in the robust problem. In the scalar problem `rcScalarProblem c` with `θ = 52/11`:
for `c = 0`, `D(P) = P`, the robust equation is the standard Riccati equation, solved by `P = 2`
with gain `F = 1/2`; for `c = 1`, `P = 13/6` solves `P = T(D(P))` with gain `F = 2/3`, while
`P = 2` does not. -/
theorem rc_C_matters :
    (∀ P, rcD (52 / 11) (rcScalarProblem 0).C P = P) ∧
      (rcScalarProblem 0).T !![2] = !![2] ∧ (rcScalarProblem 0).F !![2] = !![1 / 2] ∧
      (rcScalarProblem 1).T (rcD (52 / 11) (rcScalarProblem 1).C !![13 / 6]) = !![13 / 6] ∧
      (rcScalarProblem 1).F (rcD (52 / 11) (rcScalarProblem 1).C !![13 / 6]) = !![2 / 3] ∧
      (rcScalarProblem 1).T (rcD (52 / 11) (rcScalarProblem 1).C !![2]) ≠ !![2] := by
  have hC0 : (rcScalarProblem 0).C = 0 := by
    ext i j; fin_cases i; fin_cases j; simp [rcScalarProblem]
  have hD : ∀ p : ℝ, rcD (52 / 11) (rcScalarProblem 1).C !![p] =
      !![p + p ^ 2 / (52 / 11 - p)] := by
    intro p
    have hH : rcH (52 / 11) (rcScalarProblem 1).C !![p] = !![52 / 11 - p] := by
      ext i j; fin_cases i; fin_cases j
      simp [rcH, rcScalarProblem, Matrix.mul_apply]
    rw [rcD, hH, rc_inv_fin_one]
    ext i j; fin_cases i; fin_cases j
    simp [rcScalarProblem, Matrix.mul_apply, vecMul, dotProduct]
    ring
  have hG : ∀ (c p : ℝ), (rcScalarProblem c).G !![p] = !![1 + p / 2] := by
    intro c p
    ext i j; fin_cases i; fin_cases j
    simp [LSProblem.G, rcScalarProblem, Matrix.mul_apply]
    ring
  have hN : ∀ (c p : ℝ), (rcScalarProblem c).N !![p] = !![p / 2] := by
    intro c p
    ext i j; fin_cases i; fin_cases j
    simp [LSProblem.N, rcScalarProblem, Matrix.mul_apply]
    ring
  have hT : ∀ (c p : ℝ), (rcScalarProblem c).T !![p] =
      !![3 / 2 + p / 2 - (p / 2) ^ 2 / (1 + p / 2)] := by
    intro c p
    rw [LSProblem.T, hG, hN, rc_inv_fin_one]
    ext i j; fin_cases i; fin_cases j
    simp [rcScalarProblem, Matrix.mul_apply]
    ring
  have hF : ∀ (c p : ℝ), (rcScalarProblem c).F !![p] = !![(p / 2) / (1 + p / 2)] := by
    intro c p
    rw [LSProblem.F, hG, hN, rc_inv_fin_one]
    ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
    ring
  refine ⟨fun P => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rcD, hC0]
  · rw [hT]; norm_num
  · rw [hF]; norm_num
  · rw [hD, hT]; norm_num
  · rw [hD, hF]; norm_num
  · rw [hD, hT]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

end Miao.LinearQuadratic
