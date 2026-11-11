/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.RCNormal
import LinearQuadratic.LSInfiniteHorizon
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Exercise 9.3: the multiplier problem as `θ → ∞`

Miao, §9.7, Exercise 9.3, p. 325: as `θ → ∞` the solution of the multiplier problem (9.52)–(9.55)
converges to the solution of the standard control problem.

* `rc_log_det_bounds`: for `Y ≥ 0` with `I − Y > 0` and `tr Y < 1`,
  `tr Y ≤ −ln det(I − Y) ≤ tr Y/(1 − tr Y)` (via the eigenvalues of `I − Y`).
* `rc_D_tendsto`: along any family `P_θ → P` (with `P_θ ≥ 0`), `D_θ(P_θ) → P`; in particular
  `D_θ(P) → P` for fixed `P`.
* `rc_d_tendsto`: `d_θ(P_θ) = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'P_θC)⁻¹ → (1 − β)⁻¹β tr(PCC')`, the
  constant of the standard problem (§9.3, (9.16)).
* `rc_T_tendsto`, `rc_F_tendsto`: continuity of `T` and of the gain at `P ≥ 0`.
* **Exercise 9.3** (`ex_9_3`): if `P_θ ≥ 0` solve `P_θ = T(D_θ(P_θ))` (9.53) with
  `θI − C'P_θC > 0` and `P_θ → P` as `θ → ∞`, then `P ≥ 0` solves the standard Riccati equation
  `P = T(P)` (9.12), the robust gain (9.52) converges to the standard gain `F(P)` (9.17), and
  `d_θ` (9.55) converges to the standard constant; `ex_9_3_unique`: under the hypotheses of
  Proposition 9.3.1 the limit is the unique positive semidefinite solution of (9.12).

Departure: the exercise asks to show convergence; we assume that the robust solutions converge
(as they do along the monotone value iteration when it is bounded) and identify the limit, and we
prove the convergence of the constant, of `D_θ` and of the gain.
-/

open Matrix Filter Topology Real

namespace Miao.LinearQuadratic

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- `tr Y ≤ −ln det(I − Y) ≤ tr Y/(1 − tr Y)` for `Y ≥ 0`, `I − Y > 0`, `tr Y < 1`. -/
theorem rc_log_det_bounds {Y : Matrix E E ℝ} (hY : Y.PosSemidef) (hK : (1 - Y).PosDef)
    (htr : trace Y < 1) :
    trace Y ≤ -log (1 - Y).det ∧ -log (1 - Y).det ≤ trace Y / (1 - trace Y) := by
  have hKh : (1 - Y).IsHermitian := hK.isHermitian
  have hdet : (1 - Y).det = ∏ i, hKh.eigenvalues i := by
    simpa using hKh.det_eq_prod_eigenvalues
  have htrK : trace (1 - Y) = ∑ i, hKh.eigenvalues i := by
    simpa using hKh.trace_eq_sum_eigenvalues
  have hpos : ∀ i, 0 < hKh.eigenvalues i := hK.eigenvalues_pos
  have hYq := (SS.LQProblem.posSemidef_iff_real.1 hY).2
  have hle : ∀ i, hKh.eigenvalues i ≤ 1 := by
    intro i
    set v := (hKh.eigenvectorBasis i).ofLp
    have hmv : (1 - Y) *ᵥ v = hKh.eigenvalues i • v := hKh.mulVec_eigenvectorBasis i
    have hv0 : v ≠ 0 := by
      simpa [v] using hKh.eigenvectorBasis.orthonormal.ne_zero i
    have hvv : 0 < v ⬝ᵥ v := by
      have h0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
      refine lt_of_le_of_ne h0 fun h => hv0 ?_
      exact dotProduct_self_eq_zero.1 h.symm
    have h1 : v ⬝ᵥ ((1 - Y) *ᵥ v) = v ⬝ᵥ v - v ⬝ᵥ (Y *ᵥ v) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]
    rw [hmv, dotProduct_smul, smul_eq_mul] at h1
    have := hYq v
    by_contra hgt
    push Not at hgt
    nlinarith
  have hlog : log (1 - Y).det = ∑ i, log (hKh.eigenvalues i) := by
    rw [hdet, Real.log_prod]
    intro i _
    exact (hpos i).ne'
  have htrY : trace Y = ∑ i, (1 - hKh.eigenvalues i) := by
    rw [Finset.sum_sub_distrib, ← htrK, trace_sub, trace_one]
    simp
  have hδ : ∀ i, 1 - hKh.eigenvalues i ≤ trace Y := by
    intro i
    rw [htrY]
    exact Finset.single_le_sum (f := fun j => 1 - hKh.eigenvalues j)
      (fun j _ => by linarith [hle j]) (Finset.mem_univ i)
  refine ⟨?_, ?_⟩
  · rw [hlog, htrY, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    linarith [Real.log_le_sub_one_of_pos (hpos i)]
  · rw [hlog, ← Finset.sum_neg_distrib, htrY, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hk := hpos i
    have h1 : -log (hKh.eigenvalues i) ≤ (1 - hKh.eigenvalues i) / hKh.eigenvalues i := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hk)
      rw [Real.log_inv] at this
      rw [sub_div, div_self hk.ne']
      linarith [one_div (hKh.eigenvalues i)]
    refine h1.trans ?_
    have hlow : 1 - trace Y ≤ hKh.eigenvalues i := by linarith [hδ i]
    rw [← htrY]
    exact div_le_div_of_nonneg_left (by linarith [hle i]) (by linarith) hlow

/-- Matrix multiplication is continuous along any filter. -/
theorem rc_tendsto_mul {α : Type*} {l : Filter α} {m n p : Type*} [Fintype n]
    {f : α → Matrix m n ℝ} {g : α → Matrix n p ℝ} {a : Matrix m n ℝ} {b : Matrix n p ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun s => f s * g s) l (𝓝 (a * b)) :=
  ((Continuous.matrix_mul continuous_fst continuous_snd).tendsto (a, b)).comp (hf.prodMk_nhds hg)

/-- Inversion is continuous at an invertible matrix, along any filter. -/
theorem rc_tendsto_inv {α : Type*} {l : Filter α} {f : α → Matrix E E ℝ} {a : Matrix E E ℝ}
    (ha : IsUnit a.det) (hf : Tendsto f l (𝓝 a)) : Tendsto (fun s => (f s)⁻¹) l (𝓝 a⁻¹) := by
  have h : ContinuousAt Ring.inverse a.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ha.ne_zero
  exact (continuousAt_matrix_inv a h).tendsto.comp hf

omit [DecidableEq E] in
theorem rc_tendsto_smul {α : Type*} {l : Filter α} {m n : Type*} {c : α → ℝ} {f : α → Matrix m n ℝ}
    {c₀ : ℝ} {a : Matrix m n ℝ} (hc : Tendsto c l (𝓝 c₀)) (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun s => c s • f s) l (𝓝 (c₀ • a)) := hc.smul hf

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for `c ≠ 0`. -/
theorem rc_inv_smul {c : ℝ} (hc : c ≠ 0) (A : Matrix E E ℝ) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_smul' _ (Units.mk0 c hc) h
  · have h' : ¬ IsUnit (c • A).det := by
      rw [det_smul]
      exact fun hu => h (isUnit_of_mul_isUnit_right hu)
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', smul_zero]

/-- Exercise 9.3: `D_θ(P_θ) = P_θ + P_θC(θI − C'P_θC)⁻¹C'P_θ → P` as `θ → ∞` when `P_θ → P`. -/
theorem rc_D_tendsto {C : Matrix X E ℝ} {Pθ : ℝ → Matrix X X ℝ} {P : Matrix X X ℝ}
    (hlim : Tendsto Pθ atTop (𝓝 P)) :
    Tendsto (fun θ => rcD θ C (Pθ θ)) atTop (𝓝 P) := by
  have hX : Tendsto (fun θ => Cᵀ * Pθ θ * C) atTop (𝓝 (Cᵀ * P * C)) :=
    rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds hlim) tendsto_const_nhds
  have hK : Tendsto (fun θ => rcK θ C (Pθ θ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Matrix E E ℝ))).sub
      (rc_tendsto_smul (tendsto_inv_atTop_zero (𝕜 := ℝ)) hX)
    rw [zero_smul, sub_zero] at this
    exact this
  have hKi : Tendsto (fun θ => (rcK θ C (Pθ θ))⁻¹) atTop (𝓝 1) := by
    simpa using rc_tendsto_inv (by simp) hK
  have hHi : Tendsto (fun θ => (rcH θ C (Pθ θ))⁻¹) atTop (𝓝 0) := by
    have h := rc_tendsto_smul (tendsto_inv_atTop_zero (𝕜 := ℝ)) hKi
    rw [zero_smul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    rw [rcH_eq_smul hθ.ne', rc_inv_smul hθ.ne']
  have h := rc_tendsto_mul (rc_tendsto_mul (rc_tendsto_mul (rc_tendsto_mul hlim
    (tendsto_const_nhds (x := C))) hHi) (tendsto_const_nhds (x := Cᵀ))) hlim
  simpa [rcD] using hlim.add h

/-- Exercise 9.3: the constant (9.55) converges to the constant of the standard problem,
`d_θ(P_θ) = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'P_θC)⁻¹ → (1 − β)⁻¹β tr(PCC')`. -/
theorem rc_d_tendsto (β : ℝ) {C : Matrix X E ℝ} {Pθ : ℝ → Matrix X X ℝ} {P : Matrix X X ℝ}
    (hpsd : ∀ᶠ θ in atTop, (Pθ θ).PosSemidef) (hH : ∀ᶠ θ in atTop, (rcH θ C (Pθ θ)).PosDef)
    (hlim : Tendsto Pθ atTop (𝓝 P)) :
    Tendsto (fun θ => rcd β θ C (Pθ θ)) atTop (𝓝 ((1 - β)⁻¹ * (β * trace (P * C * Cᵀ)))) := by
  have hX : Tendsto (fun θ => Cᵀ * Pθ θ * C) atTop (𝓝 (Cᵀ * P * C)) :=
    rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds hlim) tendsto_const_nhds
  have htrX : Tendsto (fun θ => trace (Cᵀ * Pθ θ * C)) atTop (𝓝 (trace (Cᵀ * P * C))) :=
    ((continuous_id.matrix_trace).tendsto _).comp hX
  have htrY : Tendsto (fun θ : ℝ => θ⁻¹ * trace (Cᵀ * Pθ θ * C)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul htrX
  have hup : Tendsto (fun θ : ℝ => trace (Cᵀ * Pθ θ * C) / (1 - θ⁻¹ * trace (Cᵀ * Pθ θ * C)))
      atTop (𝓝 (trace (Cᵀ * P * C))) := by
    have := htrX.div ((tendsto_const_nhds (x := (1 : ℝ))).sub htrY) (by norm_num)
    rw [sub_zero, div_one] at this
    exact this
  have hg : Tendsto (fun θ => θ * log (rcK θ C (Pθ θ))⁻¹.det) atTop
      (𝓝 (trace (Cᵀ * P * C))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htrX hup ?_ ?_
    · filter_upwards [hpsd, hH, eventually_gt_atTop 0, htrY.eventually (gt_mem_nhds one_pos)]
        with θ hP hHθ hθ hlt
      have hY : (θ⁻¹ • (Cᵀ * Pθ θ * C)).PosSemidef :=
        (SS.LQProblem.posSemidef_transpose_mul_mul hP C).smul (inv_nonneg.2 hθ.le)
      have hK : (1 - θ⁻¹ • (Cᵀ * Pθ θ * C)).PosDef := (rcK_posDef_iff hθ C _).2 hHθ
      have htr : trace (θ⁻¹ • (Cᵀ * Pθ θ * C)) < 1 := by rw [trace_smul, smul_eq_mul]; exact hlt
      have hb := (rc_log_det_bounds hY hK htr).1
      rw [trace_smul, smul_eq_mul] at hb
      rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
      have := mul_le_mul_of_nonneg_left hb hθ.le
      rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul] at this
      exact this
    · filter_upwards [hpsd, hH, eventually_gt_atTop 0, htrY.eventually (gt_mem_nhds one_pos)]
        with θ hP hHθ hθ hlt
      have hY : (θ⁻¹ • (Cᵀ * Pθ θ * C)).PosSemidef :=
        (SS.LQProblem.posSemidef_transpose_mul_mul hP C).smul (inv_nonneg.2 hθ.le)
      have hK : (1 - θ⁻¹ • (Cᵀ * Pθ θ * C)).PosDef := (rcK_posDef_iff hθ C _).2 hHθ
      have htr : trace (θ⁻¹ • (Cᵀ * Pθ θ * C)) < 1 := by rw [trace_smul, smul_eq_mul]; exact hlt
      have hb := (rc_log_det_bounds hY hK htr).2
      rw [trace_smul, smul_eq_mul] at hb
      rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
      have := mul_le_mul_of_nonneg_left hb hθ.le
      refine this.trans_eq ?_
      have h1 : 1 - θ⁻¹ * trace (Cᵀ * Pθ θ * C) ≠ 0 := by linarith
      field_simp
  have htr : trace (Cᵀ * P * C) = trace (P * C * Cᵀ) := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [← htr]
  refine (hg.const_mul β).const_mul (1 - β)⁻¹ |>.congr fun θ => ?_
  rw [rcd]
  ring

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype E] [DecidableEq E] in
/-- The gain map `P ↦ F(P)` and the Riccati operator `T` are continuous at `P ≥ 0`
(`R > 0`, `β ≥ 0`). -/
theorem rc_T_F_tendsto (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {α : Type*}
    {l : Filter α} {Pn : α → Matrix X X ℝ} {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (h : Tendsto Pn l (𝓝 P)) :
    Tendsto (fun s => L.T (Pn s)) l (𝓝 (L.T P)) ∧ Tendsto (fun s => L.F (Pn s)) l (𝓝 (L.F P)) := by
  have hG : Tendsto (fun s => L.G (Pn s)) l (𝓝 (L.G P)) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have hGi := rc_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.G_posDef hR hP hβ).isUnit) hG
  have hN : Tendsto (fun s => L.N (Pn s)) l (𝓝 (L.N P)) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have hF : Tendsto (fun s => L.F (Pn s)) l (𝓝 (L.F P)) := rc_tendsto_mul hGi hN
  refine ⟨?_, hF⟩
  have h1 : Tendsto (fun s => L.Q + L.β • (L.Aᵀ * Pn s * L.A)) l
      (𝓝 (L.Q + L.β • (L.Aᵀ * P * L.A))) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have h2 : Tendsto (fun s => L.S + L.β • (L.Aᵀ * Pn s * L.B)) l
      (𝓝 (L.S + L.β • (L.Aᵀ * P * L.B))) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have h3 := h1.sub (rc_tendsto_mul h2 hF)
  simp only [← LSProblem.T_eq_sub] at h3
  exact h3

omit [Fintype X] in
/-- A limit of positive semidefinite matrices is positive semidefinite. -/
theorem rc_posSemidef_of_tendsto [Finite X] {α : Type*} {l : Filter α} [l.NeBot]
    {Pn : α → Matrix X X ℝ} {P : Matrix X X ℝ} (hpsd : ∀ᶠ s in l, (Pn s).PosSemidef)
    (h : Tendsto Pn l (𝓝 P)) : P.PosSemidef := by
  cases nonempty_fintype X
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun x => ?_⟩
  · have ht : Tendsto (fun s => (Pn s)ᵀ) l (𝓝 Pᵀ) :=
      ((continuous_id.matrix_transpose).tendsto _).comp h
    refine tendsto_nhds_unique_of_eventuallyEq ht h ?_
    filter_upwards [hpsd] with s hs
    exact (SS.LQProblem.posSemidef_iff_real.1 hs).1
  · have hq : Tendsto (fun s => x ⬝ᵥ (Pn s *ᵥ x)) l (𝓝 (x ⬝ᵥ (P *ᵥ x))) :=
      ((continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).tendsto
        _).comp h
    refine ge_of_tendsto hq ?_
    filter_upwards [hpsd] with s hs
    exact (SS.LQProblem.posSemidef_iff_real.1 hs).2 x

/-- **Exercise 9.3** (Miao, p. 325): as `θ → ∞` the solution of the multiplier problem
(9.52)–(9.55) converges to the solution of the standard problem. If `P_θ ≥ 0` solve the robust
Riccati equation `P_θ = T(D_θ(P_θ))` (9.53) with `θI − C'P_θC > 0` and `P_θ → P`, then `P ≥ 0`
solves the standard Riccati equation `P = T(P)` (9.12); `D_θ(P_θ) → P`; the robust gain (9.52)
converges to the standard gain `F(P)` (9.17); and `d_θ` (9.55) converges to the standard constant
`(1 − β)⁻¹β tr(PCC')`. -/
theorem ex_9_3 (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {Pθ : ℝ → Matrix X X ℝ}
    {P : Matrix X X ℝ} (hpsd : ∀ᶠ θ in atTop, (Pθ θ).PosSemidef)
    (hH : ∀ᶠ θ in atTop, (rcH θ L.C (Pθ θ)).PosDef)
    (hfix : ∀ᶠ θ in atTop, L.T (rcD θ L.C (Pθ θ)) = Pθ θ) (hlim : Tendsto Pθ atTop (𝓝 P)) :
    P.PosSemidef ∧ L.T P = P ∧ Tendsto (fun θ => rcD θ L.C (Pθ θ)) atTop (𝓝 P) ∧
      Tendsto (fun θ => L.F (rcD θ L.C (Pθ θ))) atTop (𝓝 (L.F P)) ∧
      Tendsto (fun θ => rcd L.β θ L.C (Pθ θ)) atTop
        (𝓝 ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)))) := by
  have hP := rc_posSemidef_of_tendsto hpsd hlim
  have hD := rc_D_tendsto (C := L.C) hlim
  obtain ⟨hT, hF⟩ := rc_T_F_tendsto L hR hβ hP hD
  refine ⟨hP, ?_, hD, hF, rc_d_tendsto L.β hpsd hH hlim⟩
  exact tendsto_nhds_unique_of_eventuallyEq hT hlim hfix

/-- **Exercise 9.3**, the limit is the standard solution: under the hypotheses of
Proposition 9.3.1 (`S = 0`, `Q > 0`, `R > 0`, `(√βA, √βB)` controllable or stabilizable), the
limit `P` of the robust solutions is the unique positive semidefinite solution of (9.12). -/
theorem ex_9_3_unique [Nonempty X] [DecidableEq X] (L : LSProblem X U E) (hS : L.S = 0)
    (hQ : L.Q.PosDef) (hR : L.R.PosDef) (hβ : 0 ≤ L.β)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B))
    {Pθ : ℝ → Matrix X X ℝ} {P : Matrix X X ℝ} (hpsd : ∀ᶠ θ in atTop, (Pθ θ).PosSemidef)
    (hH : ∀ᶠ θ in atTop, (rcH θ L.C (Pθ θ)).PosDef)
    (hfix : ∀ᶠ θ in atTop, L.T (rcD θ L.C (Pθ θ)) = Pθ θ) (hlim : Tendsto Pθ atTop (𝓝 P)) :
    ∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P := by
  obtain ⟨hP, hfixP, -⟩ := ex_9_3 L hR hβ hpsd hH hfix hlim
  obtain ⟨Ps, -, huniq, -⟩ := L.proposition_9_3_1 hS hQ hR hβ hstab
  intro P' hP' hfix'
  rw [huniq P' hP' hfix', huniq P hP hfixP]

end Miao.LinearQuadratic
