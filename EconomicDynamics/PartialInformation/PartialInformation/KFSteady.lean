/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFFilter
import PartialInformation.LSInfiniteLimits
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The stationary Kalman filter

Miao, §10.1.1, pp. 332–334. The time-invariant system (`KFSystem.const`: `A_t = A`, …, `D_t = D`)
and the "long-run stationary Kalman filter in which `Σ_t → Σ` and `K_t → K`" (p. 334).

* Step 1 (p. 332), the stationary initialisation: for stable `A`, `x̂₀ = Ax̂₀` forces `x̂₀ = 0`
  (`kf_step1_mean`), and `Σ₀ = AΣ₀A' + Q` has exactly one solution, given in vectorised form by
  `vec Σ₀ = (I − A ⊗ A)⁻¹ vec Q` (`kf_step1_cov`). The book's `Q` (undefined there) is the state
  noise covariance `CC'`.
* Duality (`kf_dual`, `kf_dual_T`): when the state and measurement noises are uncorrelated
  (`CD' = 0`, the case "often considered in applications", p. 328), the covariance recursion
  `Σ_{t+1|t} = AΣ_{t|t}A' + CC'` is the Riccati operator (9.11) of the dual LQ problem
  `(Â, B̂, Q̂, R̂, Ŝ, β) = (A', G', CC', DD', 0, 1)` of Chapter 9 (`LSProblem.T`).
* `kf_steady_state`: if `CD' = 0`, `DD' > 0`, `(A, G)` is detectable (Definition 9.1.4) and
  `(A, C)` is stabilizable (Definition 9.1.1), the steady-state Riccati equation
  `Σ = AΣA' + CC' − AΣG'(GΣG' + DD')⁻¹GΣA'` has a unique positive semidefinite solution `Σ`; from
  every positive semidefinite `Σ₀` the filter covariances `Σ_{t|t−1} → Σ` and gains `K_t → K =
  ΣG'(GΣG' + DD')⁻¹`; and the error matrix `A − AKG` of (9.3) is stable. This is Proposition 9.3.2
  (`LSProblem.ls_discounted_main`) applied to the dual problem: detectability of `(A, G)` is
  stabilizability of `(A', G')`, stabilizability of `(A, C)` is detectability of `(A', C')`.
* `kf_steady_fixed`: started at the steady state, the filter covariance stays there.

The book gives no conditions for the convergence `Σ_t → Σ`; the conditions above are the dual of
those of Propositions 9.3.1–9.3.2. The correlated case `CD' ≠ 0` is not covered by the stated
theorem (the dual problem then has a cross term).
-/

open Filter Topology Matrix

open scoped MatrixOrder Kronecker

namespace Miao.PartialInformation

variable {X U Y E : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y]

/-- The time-invariant system: `A_t = A`, …, `D_t = D` (Miao, p. 333). -/
def KFSystem.const (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ)
    (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ) (S0 : Matrix X X ℝ) :
    KFSystem X U Y E :=
  ⟨fun _ => A, fun _ => B, fun _ => C, fun _ => G, fun _ => H, fun _ => D, xbar0, S0⟩

omit [Fintype Y] [Fintype E] [DecidableEq Y] in
/-- Step 1 (Miao, p. 332): for stable `A`, the stationary mean `x̂₀ = Ax̂₀` is `0`. -/
theorem kf_step1_mean {A : Matrix X X ℝ} (hA : ls_Stable A) {m : X → ℝ} (hm : A *ᵥ m = m) :
    m = 0 := by
  have h := (ls_stable_iff_tendsto A).1 hA m
  have hc : ∀ t : ℕ, (A ^ t) *ᵥ m = m := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← mulVec_mulVec, hm, ih]
  simp only [hc] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

omit [Fintype Y] [Fintype E] [DecidableEq Y] in
/-- Step 1 (Miao, p. 332): for stable `A`, the stationary covariance `Σ₀ = AΣ₀A' + Q` exists and
is unique (`var_lyapSol`, Chapter 2), and in vectorised form it is
`vec Σ₀ = (I − A ⊗ A)⁻¹ vec Q`, `I − A ⊗ A` being invertible. -/
theorem kf_step1_cov {A : Matrix X X ℝ} (hA : ls_Stable A) (Q : Matrix X X ℝ) :
    var_lyapSol A Q = A * var_lyapSol A Q * Aᵀ + Q ∧
      (∀ S0 : Matrix X X ℝ, S0 = A * S0 * Aᵀ + Q → S0 = var_lyapSol A Q) ∧
      IsUnit (1 - A ⊗ₖ A) ∧ ∀ S0 : Matrix X X ℝ, S0 = A * S0 * Aᵀ + Q →
        vec S0 = (1 - A ⊗ₖ A)⁻¹ *ᵥ vec Q := by
  have hfix := lyap_fixed A hA Q
  have huniq : ∀ S0 : Matrix X X ℝ, S0 = A * S0 * Aᵀ + Q → S0 = var_lyapSol A Q :=
    fun S0 h => lyap_unique A hA Q S0 h.symm
  have hvec : ∀ V : Matrix X X ℝ, (1 - A ⊗ₖ A) *ᵥ vec V = vec (V - A * V * Aᵀ) := by
    intro V
    rw [sub_mulVec, one_mulVec, kronecker_mulVec_vec, vec_sub]
  have hunit : IsUnit (1 - A ⊗ₖ A) := by
    refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
    obtain ⟨V, rfl⟩ := vec_bijective.2 v
    obtain ⟨W, rfl⟩ := vec_bijective.2 w
    rw [hvec, hvec, vec_inj] at hvw
    have h0 : ∀ Z : Matrix X X ℝ, Z = A * Z * Aᵀ + 0 → Z = var_lyapSol A 0 :=
      fun Z h => lyap_unique A hA 0 Z h.symm
    have hVW : V - W = A * (V - W) * Aᵀ + 0 := by
      calc V - W = (V - A * V * Aᵀ) - (W - A * W * Aᵀ) + (A * V * Aᵀ - A * W * Aᵀ) := by abel
        _ = A * (V - W) * Aᵀ + 0 := by
          rw [hvw, sub_self, zero_add, add_zero, Matrix.mul_sub, Matrix.sub_mul]
    have hz : (0 : Matrix X X ℝ) = A * 0 * Aᵀ + 0 := by simp
    rw [← sub_eq_zero, ← vec_sub, h0 _ hVW, ← h0 0 hz, vec_zero]
  refine ⟨hfix.symm, huniq, hunit, fun S0 h => ?_⟩
  have h1 : (1 - A ⊗ₖ A) *ᵥ vec S0 = vec Q := by
    rw [hvec, sub_eq_iff_eq_add'.2 h]
  rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit), one_mulVec]

/-- The dual LQ problem of the filter (Miao, pp. 333–334, with Chapter 9):
`(Â, B̂, Ĉ, Q̂, R̂, Ŝ, β) = (A', G', C, CC', DD', 0, 1)`. -/
def kf_dual (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ) (D : Matrix Y E ℝ) :
    LSProblem X Y E :=
  ⟨Aᵀ, Gᵀ, C, C * Cᵀ, D * Dᵀ, 0, 1⟩

omit [DecidableEq X] in
/-- Duality (uncorrelated noise, `CℓD' = 0`): `AΣ_{t|t}A' + CC' = T̂(Σ_{t|t−1})`, the Riccati
operator (9.11) of the dual problem: `T̂(P) = CC' + APA' − APG'(DD' + GPG')⁻¹GPA'`. -/
theorem kf_dual_T [DecidableEq X] (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) {Cl : Matrix X E ℝ} (hCD : Cl * Dᵀ = 0) (P : Matrix X X ℝ) :
    A * kf_filtCov G D Cl P * Aᵀ + C * Cᵀ = (kf_dual A G C D).T P := by
  have hDC : D * Clᵀ = 0 := by
    rw [← transpose_transpose (D * Clᵀ), transpose_mul, transpose_transpose, hCD,
      transpose_zero]
  have hΩ : kf_Om G D Cl P = D * Dᵀ + G * P * Gᵀ := by
    rw [kf_Om, Matrix.mul_assoc G Cl, hCD, hDC]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    abel
  simp only [kf_filtCov, kf_gain, kf_Mx, hCD, add_zero, hΩ, LSProblem.T, kf_dual, LSProblem.G,
    LSProblem.N, one_smul, transpose_transpose, transpose_zero, zero_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc, hDC, Matrix.mul_zero, sub_zero]
  abel

/-- The steady-state gain `K = ΣG'(GΣG' + DD')⁻¹`. -/
noncomputable def kf_steadyGain (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (P : Matrix X X ℝ) :
    Matrix X Y ℝ :=
  P * Gᵀ * (G * P * Gᵀ + D * Dᵀ)⁻¹

omit [Fintype U] in
/-- With `CD' = 0`, the time-invariant filter covariances follow the dual Riccati operator:
`Σ_{t+1|t} = T̂(Σ_{t|t−1})`, hence `Σ_{t|t−1} = T̂ᵗ(Σ₀)`; and `K_t = Σ_{t|t−1}G'(GΣ_{t|t−1}G' +
DD')⁻¹`. -/
theorem kf_const_Spred (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (S0 : Matrix X X ℝ) (hCD : C * Dᵀ = 0) (t : ℕ) :
    (KFSystem.const A B C G H D xbar0 S0).Spred t = (kf_dual A G C D).T^[t] S0 ∧
      (KFSystem.const A B C G H D xbar0 S0).K t =
        kf_steadyGain G D ((KFSystem.const A B C G H D xbar0 S0).Spred t) := by
  set S := KFSystem.const A B C G H D xbar0 S0
  have hCl : ∀ t, S.Cl t * Dᵀ = 0 := by
    intro t
    cases t with
    | zero => exact Matrix.zero_mul _
    | succ t => exact hCD
  have hClD : ∀ t, D * (S.Cl t)ᵀ = 0 := by
    intro t
    rw [← transpose_transpose (D * (S.Cl t)ᵀ), transpose_mul, transpose_transpose, hCl t,
      transpose_zero]
  refine ⟨?_, ?_⟩
  · induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih]
      exact kf_dual_T A G C D (hCl t) (S.Spred t)
  · simp only [KFSystem.K, kf_gain, kf_Mx, kf_Om, kf_steadyGain]
    rw [show S.G t = G from rfl, show S.D t = D from rfl, Matrix.mul_assoc G (S.Cl t), hCl t,
      hClD t]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

omit [Fintype U] in
/-- **The stationary Kalman filter** (Miao, pp. 333–334), uncorrelated case `CD' = 0`, via
Proposition 9.3.2 for the dual LQ problem. If `DD' > 0`, `(A, G)` is detectable and `(A, C)` is
stabilizable, then the steady-state Riccati equation
`Σ = AΣA' + CC' − AΣG'(GΣG' + DD')⁻¹GΣA'` has a positive semidefinite solution `Σ`, unique among
positive semidefinite matrices; from every positive semidefinite `Σ₀` the filter covariances
converge, `Σ_{t|t−1} → Σ`, and so do the gains, `K_t → K = ΣG'(GΣG' + DD')⁻¹`; and `A − AKG` is
stable. -/
theorem kf_steady_state [Nonempty X] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (hCD : C * Dᵀ = 0) (hR : (D * Dᵀ).PosDef) (hdet : ls_Detectable A G)
    (hstab : ls_Stabilizable A C) :
    ∃ P : Matrix X X ℝ, P.PosSemidef ∧
      P = A * P * Aᵀ + C * Cᵀ - A * P * Gᵀ * (G * P * Gᵀ + D * Dᵀ)⁻¹ * G * P * Aᵀ ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef →
        P' = A * P' * Aᵀ + C * Cᵀ - A * P' * Gᵀ * (G * P' * Gᵀ + D * Dᵀ)⁻¹ * G * P' * Aᵀ →
          P' = P) ∧
      (∀ S0 : Matrix X X ℝ, S0.PosSemidef →
        Tendsto (fun t => (KFSystem.const A B C G H D xbar0 S0).Spred t) atTop (𝓝 P) ∧
        Tendsto (fun t => (KFSystem.const A B C G H D xbar0 S0).K t) atTop
          (𝓝 (kf_steadyGain G D P))) ∧
      ls_Stable (A - A * kf_steadyGain G D P * G) := by
  set L := kf_dual A G C D
  have hQ : L.Q.PosSemidef := by
    simpa [L, kf_dual, conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose C
  have hS : L.S = 0 := rfl
  have hβ : (0 : ℝ) ≤ L.β := zero_le_one
  have hsq : Real.sqrt L.β = 1 := Real.sqrt_one
  have hstab' : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) := by
    right
    obtain ⟨J, hJ⟩ := hdet
    refine ⟨-Jᵀ, ?_⟩
    rw [hsq, one_smul, one_smul, ← ls_stable_transpose]
    convert hJ using 1
    simp [L, kf_dual, transpose_mul, sub_eq_add_neg]
  have hD : ∀ F, ls_Detects (L.toSS hQ hR) F := by
    intro F
    refine ls_detects_of_detectable (L.toSS hQ hR) (Lm := Cᵀ) ?_ ?_ F
    · simp [LSProblem.toSS, L, kf_dual]
    · obtain ⟨Hm, hH⟩ := hstab
      refine ⟨-Hmᵀ, ?_⟩
      rw [← ls_stable_transpose]
      convert hH using 1
      simp [LSProblem.toSS, L, kf_dual, transpose_mul, sub_eq_add_neg]
  obtain ⟨P, hP, hfix, huniq, hconv, hst, -⟩ := L.ls_discounted_main hS hβ hQ hR hstab' hD
  have hT : ∀ P' : Matrix X X ℝ, L.T P' =
      A * P' * Aᵀ + C * Cᵀ - A * P' * Gᵀ * (G * P' * Gᵀ + D * Dᵀ)⁻¹ * G * P' * Aᵀ := by
    intro P'
    simp only [L, LSProblem.T, kf_dual, LSProblem.G, LSProblem.N, one_smul, transpose_transpose,
      transpose_zero, zero_add, Matrix.mul_assoc]
    rw [add_comm (D * Dᵀ)]
    abel
  have hGP : (G * P * Gᵀ + D * Dᵀ).PosDef := by
    have := L.G_posDef hR hP hβ
    simpa [L, LSProblem.G, kf_dual, add_comm, Matrix.mul_assoc] using this
  refine ⟨P, hP, by rw [← hT, hfix], fun P' hP' h' => huniq P' hP' (by rw [hT]; exact h'.symm),
    fun S0 hS0 => ?_, ?_⟩
  · have hlim : Tendsto (fun t => (KFSystem.const A B C G H D xbar0 S0).Spred t) atTop (𝓝 P) :=
      (hconv S0 hS0).congr fun t => (kf_const_Spred A B C G H D xbar0 S0 hCD t).1.symm
    refine ⟨hlim, ?_⟩
    have hK : (fun t => (KFSystem.const A B C G H D xbar0 S0).K t) =
        fun t => kf_steadyGain G D ((KFSystem.const A B C G H D xbar0 S0).Spred t) :=
      funext fun t => (kf_const_Spred A B C G H D xbar0 S0 hCD t).2
    rw [hK]
    exact ls_tendsto_mul (ls_tendsto_mul hlim tendsto_const_nhds)
      (ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 hGP.isUnit)
        ((ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds hlim) tendsto_const_nhds).add
          tendsto_const_nhds))
  · rw [hsq, one_smul, ← ls_stable_transpose] at hst
    convert hst using 1
    have hsym : ((G * P * Gᵀ + D * Dᵀ)⁻¹)ᵀ = (G * P * Gᵀ + D * Dᵀ)⁻¹ := by
      rw [transpose_nonsing_inv, transpose_add, transpose_mul, transpose_mul, transpose_transpose,
        transpose_mul, transpose_transpose, (SS.LQProblem.posSemidef_iff_real.1 hP).1]
      simp [Matrix.mul_assoc]
    have hsym2 : ((G * (P * Gᵀ) + D * Dᵀ)⁻¹)ᵀ = (G * (P * Gᵀ) + D * Dᵀ)⁻¹ := by
      rw [← Matrix.mul_assoc]; exact hsym
    simp only [L, kf_dual, LSProblem.F, LSProblem.G, LSProblem.N, kf_steadyGain, one_smul,
      transpose_zero, zero_add, transpose_sub, transpose_mul, transpose_transpose,
      (SS.LQProblem.posSemidef_iff_real.1 hP).1, Matrix.mul_assoc]
    rw [add_comm (D * Dᵀ), hsym2]

omit [Fintype U] in
/-- Started at the steady state (Step 1 with `Σ₀ = Σ`), the time-invariant filter covariance stays
there: `Σ_{t|t−1} = Σ` and `K_t = K` for all `t` (uncorrelated case). -/
theorem kf_steady_fixed (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (hCD : C * Dᵀ = 0) {P : Matrix X X ℝ} (hfix : (kf_dual A G C D).T P = P) (t : ℕ) :
    (KFSystem.const A B C G H D xbar0 P).Spred t = P ∧
      (KFSystem.const A B C G H D xbar0 P).K t = kf_steadyGain G D P := by
  have h1 := (kf_const_Spred A B C G H D xbar0 P hCD t)
  rw [Function.iterate_fixed hfix] at h1
  rw [h1.2, h1.1]
  exact ⟨rfl, rfl⟩

end Miao.PartialInformation
