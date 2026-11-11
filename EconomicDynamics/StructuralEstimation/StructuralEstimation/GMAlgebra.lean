/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMBasic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The deterministic algebra of GMM (Miao, §12.1, pp. 388–395)

Miao, pp. 388–395. Everything here is exact (finite-sample) algebra and calculus.

* `gm_foc_line`, `eq_12_2` — the first-order condition (12.2) `(∂g_T/∂θ)' W_T g_T(θ̂_T) = 0` at
  an interior minimiser, for symmetric `W_T` (only partial derivatives are needed).
* `eq_12_3_counterexample` — the mean value form (12.3) with a single `θ̄_T` is false for
  vector-valued `g` (`g(θ) = (cos θ, sin θ)` on `[0, 2π]`); `eq_12_3` proves the correct
  row-by-row version (a separate `θ̄_{T,i}` on the segment for each moment `i`).
* `gm_linearization` — the step after (12.3): from the first-order condition and the expansion,
  `θ̂_T − θ₀ = −M_T g_T(θ₀)` with `M_T = (Ĝ'W_TḠ)⁻¹Ĝ'W_T`, hence
  `√T(θ̂_T − θ₀) = −M_T √T g_T(θ₀)` (`gm_linearization_sqrt`).
* `gm_M`, `gm_M_mul`, `gm_asymVar_eq` — `M = (G₀'WG₀)⁻¹G₀'W` (Theorem 12.1.2) and
  `MSM' = (G₀'WG₀)⁻¹G₀'WSWG₀(G₀'WG₀)⁻¹`.
* `gm_efficient_var` — with `W = S⁻¹`, `MSM' = (G₀'S⁻¹G₀)⁻¹` (p. 392);
  `gm_efficiency` — `(G'WG)⁻¹G'WSWG(G'WG)⁻¹ − (G'S⁻¹G)⁻¹` is positive semidefinite for every
  positive definite `W` (efficient GMM, the Loewner order).
* `gm_proj_*`, `eq_12_4_algebra` — the J statistic (12.4): with `S = CC'` and `H = C⁻¹G`,
  `P = H(H'H)⁻¹H'` is a symmetric idempotent of trace `k`, `I − P` one of trace `q − k`, and the
  residual moment `ĝ = (I − G(G'S⁻¹G)⁻¹G'S⁻¹)g₀` satisfies `ĝ'S⁻¹ĝ = z'(I − P)z`, `z = C⁻¹g₀`.
* `gm_linear_*`, `gm_exactly_identified`, `gm_nls_foc` — "for linear models, these conditions
  could be solved to obtain a closed-form solution" (p. 388) and the OLS / IV / NLS moment
  conditions of p. 395.
-/

namespace Miao.StructuralEstimation

open Filter Topology

/-! ### The first-order condition (12.2) -/

/-- The Jacobian matrix `(∂g_i/∂θ_j)` of a family of row derivatives `Dg i`. -/
noncomputable def gm_jacobian {k q : ℕ} (Dg : Fin q → (Fin k → ℝ) →L[ℝ] ℝ) :
    Matrix (Fin q) (Fin k) ℝ :=
  Matrix.of fun i j => Dg i (Pi.single j 1)

/-- A continuous linear functional on `ℝ^k` in coordinates: `L d = Σ_j L(e_j) d_j`. -/
theorem gm_clm_apply_eq_sum {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (d : Fin k → ℝ) :
    L d = ∑ j, L (Pi.single j 1) * d j := by
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (d j) : Fin k → ℝ) = d j • Pi.single j 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- Miao, (12.2), p. 388, along a line: if `t ↦ v(t)'Wv(t)` has a local minimum at `0`, `W` is
symmetric and `v'(0) = G`, then `G'Wv(0) = 0`. -/
theorem gm_foc_line {q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.IsSymm)
    {v : ℝ → Fin q → ℝ} {G : Fin q → ℝ} (hv : ∀ i, HasDerivAt (fun t => v t i) (G i) 0)
    (hmin : IsLocalMin (fun t => gm_quadForm W (v t)) 0) :
    G ⬝ᵥ W.mulVec (v 0) = 0 := by
  have hD : HasDerivAt (fun t => gm_quadForm W (v t))
      (∑ i, ∑ j, (G i * W i j * v 0 j + v 0 i * W i j * G j)) 0 := by
    unfold gm_quadForm
    exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      ((hv i).mul_const (W i j)).mul (hv j)
  have h0 := hmin.hasDerivAt_eq_zero hD
  have hs : ∑ i, ∑ j, v 0 i * W i j * G j = ∑ i, ∑ j, G i * W i j * v 0 j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hW.apply i j]
    ring
  simp only [Finset.sum_add_distrib, hs] at h0
  have he : G ⬝ᵥ W.mulVec (v 0) = ∑ i, ∑ j, G i * W i j * v 0 j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [he]
  linarith

/-- **(12.2)** (first-order conditions, Miao, p. 388). If `θ̂` is a local (e.g. interior)
minimiser of `Q(θ) = g(θ)'Wg(θ)`, `W` is symmetric and each `g_i` is differentiable at `θ̂`, then
`(∂g/∂θ(θ̂))' W g(θ̂) = 0`. -/
theorem eq_12_2 {k q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.IsSymm)
    {g : (Fin k → ℝ) → Fin q → ℝ} {Dg : Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θh : Fin k → ℝ}
    (hd : ∀ i, HasFDerivAt (fun θ => g θ i) (Dg i) θh)
    (hmin : IsLocalMin (fun θ => gm_quadForm W (g θ)) θh) :
    (gm_jacobian Dg).transpose.mulVec (W.mulVec (g θh)) = 0 := by
  funext j
  set e : Fin k → ℝ := Pi.single j 1 with he
  have hl : HasDerivAt (fun t : ℝ => θh + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add θh
  have hline : ∀ i, HasDerivAt (fun t : ℝ => g (θh + t • e) i) (Dg i e) 0 := fun i =>
    (hd i).comp_hasDerivAt_of_eq 0 hl (by simp)
  have hmin' : IsLocalMin (fun θ => gm_quadForm W (g θ)) (θh + (0 : ℝ) • e) := by
    simpa using hmin
  have hlm := hmin'.comp_continuous (g := fun t : ℝ => θh + t • e) (by fun_prop)
  have h := gm_foc_line hW hline hlm
  simp only [zero_smul, add_zero] at h
  rw [Matrix.mulVec_transpose]
  simpa [Matrix.vecMul, dotProduct, gm_jacobian, he, mul_comm] using h

/-! ### The mean value expansion (12.3) -/

/-- Miao, (12.3), p. 390: the single-`θ̄` mean value form is **false** for vector-valued moments.
For `g(θ) = (cos θ, sin θ)` (with derivative `(−sin θ, cos θ)`, `gm_circle_hasDerivAt`),
`θ₀ = 0`, `θ̂ = 2π`, no `θ̄ = λθ₀ + (1 − λ)θ̂`, `λ ∈ [0, 1]`, satisfies
`g(θ̂) = g(θ₀) + ∂g(θ̄)(θ̂ − θ₀)`. -/
theorem eq_12_3_counterexample : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ¬ (![Real.cos (2 * Real.pi), Real.sin (2 * Real.pi)] =
      ![Real.cos 0, Real.sin 0] + (2 * Real.pi - 0) •
        ![-Real.sin (lam * 0 + (1 - lam) * (2 * Real.pi)),
          Real.cos (lam * 0 + (1 - lam) * (2 * Real.pi))]) := by
  intro lam _ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero, mul_zero,
    zero_add, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at h0 h1
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  set θb := (1 - lam) * (2 * Real.pi)
  have hs : Real.sin θb = 0 := by
    have : 2 * Real.pi * -Real.sin θb = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hpi
    · linarith
  have hc : Real.cos θb = 0 := by
    have : 2 * Real.pi * Real.cos θb = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hpi
    · exact h'
  have := Real.sin_sq_add_cos_sq θb
  rw [hs, hc] at this
  norm_num at this

/-- The derivative used in `eq_12_3_counterexample`: `(cos θ, sin θ)' = (−sin θ, cos θ)`. -/
theorem gm_circle_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t => ![Real.cos t, Real.sin t]) ![-Real.sin θ, Real.cos θ] θ := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa using Real.hasDerivAt_cos θ
  · simpa using Real.hasDerivAt_sin θ

/-- **(12.3)** corrected (row-wise mean value theorem, Miao, p. 390). If each `g_i` is
differentiable on the segment `[θ₀, θ̂]`, then for each moment `i` there is a point
`θ̄_i = θ₀ + s_i(θ̂ − θ₀)`, `s_i ∈ (0, 1)`, with
`g_i(θ̂) = g_i(θ₀) + Σ_j ∂g_i/∂θ_j(θ̄_i) (θ̂ − θ₀)_j`. (The book's `θ̄_T = λθ₀ + (1 − λ)θ̂_T` is
`s = 1 − λ`.) -/
theorem eq_12_3 {k q : ℕ} {g : (Fin k → ℝ) → Fin q → ℝ}
    {Dg : (Fin k → ℝ) → Fin q → (Fin k → ℝ) →L[ℝ] ℝ} {θ₀ θh : Fin k → ℝ}
    (hd : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt (fun θ => g θ i) (Dg (θ₀ + s • (θh - θ₀)) i) (θ₀ + s • (θh - θ₀)))
    (i : Fin q) :
    ∃ s ∈ Set.Ioo (0 : ℝ) 1, g θh i = g θ₀ i +
      ∑ j, gm_jacobian (Dg (θ₀ + s • (θh - θ₀))) i j * (θh - θ₀) j := by
  set φ : ℝ → ℝ := fun s => g (θ₀ + s • (θh - θ₀)) i with hφdef
  have hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (Dg (θ₀ + s • (θh - θ₀)) i (θh - θ₀)) s := by
    intro s hs
    have h1 : HasDerivAt (fun t : ℝ => θ₀ + t • (θh - θ₀)) (θh - θ₀) s := by
      simpa using ((hasDerivAt_id s).smul_const (θh - θ₀)).const_add θ₀
    exact (hd i s hs).comp_hasDerivAt_of_eq s h1 rfl
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope φ
    (fun s => Dg (θ₀ + s • (θh - θ₀)) i (θh - θ₀)) zero_lt_one
    (fun s hs => (hφ s hs).continuousAt.continuousWithinAt)
    (fun s hs => hφ s (Set.Ioo_subset_Icc_self hs))
  refine ⟨c, hc, ?_⟩
  simp only [hφdef, one_smul, zero_smul, add_zero, add_sub_cancel, sub_zero, div_one] at hceq
  have hsum : ∑ j, gm_jacobian (Dg (θ₀ + c • (θh - θ₀))) i j * (θh - θ₀) j =
      Dg (θ₀ + c • (θh - θ₀)) i (θh - θ₀) := by
    rw [gm_clm_apply_eq_sum]
    rfl
  rw [hsum, hceq]
  ring

/-! ### The linearisation and the asymptotic variance -/

/-- Miao, p. 390: from the first-order condition `Ĝ'V g(θ̂) = 0` and the expansion
`g(θ̂) = g(θ₀) + Ḡ(θ̂ − θ₀)`, if `Ĝ'VḠ` is invertible then
`θ̂ − θ₀ = −(Ĝ'VḠ)⁻¹Ĝ'V g(θ₀)`. -/
theorem gm_linearization {k q : ℕ} {A B : Matrix (Fin q) (Fin k) ℝ}
    {V : Matrix (Fin q) (Fin q) ℝ} {g₀ g₁ : Fin q → ℝ} {d : Fin k → ℝ}
    (hfoc : A.transpose.mulVec (V.mulVec g₁) = 0) (hexp : g₁ = g₀ + B.mulVec d)
    (hinv : IsUnit (A.transpose * V * B).det) :
    d = -(((A.transpose * V * B)⁻¹ * A.transpose * V).mulVec g₀) := by
  have h1 : (A.transpose * V * B).mulVec d = -((A.transpose * V).mulVec g₀) := by
    rw [hexp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at hfoc
    exact eq_neg_of_add_eq_zero_right hfoc
  calc d = ((A.transpose * V * B)⁻¹ * (A.transpose * V * B)).mulVec d := by
        rw [Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]
    _ = (A.transpose * V * B)⁻¹.mulVec ((A.transpose * V * B).mulVec d) := by
        rw [Matrix.mulVec_mulVec]
    _ = _ := by
        rw [h1, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]

/-- Miao, p. 390: `√T(θ̂_T − θ₀) = −M_T √T g_T(θ₀)`, `M_T = (Ĝ'W_TḠ)⁻¹Ĝ'W_T`. -/
theorem gm_linearization_sqrt {k q : ℕ} {A B : Matrix (Fin q) (Fin k) ℝ}
    {V : Matrix (Fin q) (Fin q) ℝ} {g₀ g₁ : Fin q → ℝ} {d : Fin k → ℝ}
    (hfoc : A.transpose.mulVec (V.mulVec g₁) = 0) (hexp : g₁ = g₀ + B.mulVec d)
    (hinv : IsUnit (A.transpose * V * B).det) (c : ℝ) :
    c • d = -(((A.transpose * V * B)⁻¹ * A.transpose * V).mulVec (c • g₀)) := by
  rw [gm_linearization hfoc hexp hinv, Matrix.mulVec_smul, smul_neg]

/-- Miao, Theorem 12.1.2 (p. 391): `M = (G₀'WG₀)⁻¹G₀'W`. -/
noncomputable def gm_M {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) (W : Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin k) (Fin q) ℝ :=
  (G.transpose * W * G)⁻¹ * G.transpose * W

/-- `MG₀ = I` when `G₀'WG₀` is invertible. -/
theorem gm_M_mul {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hinv : IsUnit (G.transpose * W * G).det) : gm_M G W * G = 1 := by
  rw [gm_M, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc G.transpose,
    Matrix.nonsing_inv_mul _ hinv]

/-- Miao, p. 391 (rank condition): if `W > 0` and `G₀` has full column rank (`G₀x = 0 ⇒ x = 0`)
then `G₀'WG₀` is positive definite, hence invertible. -/
theorem gm_posDef_GWG {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosDef) (hG : Function.Injective G.mulVec) :
    (G.transpose * W * G).PosDef := by
  have := hW.conjTranspose_mul_mul_same hG
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem gm_isUnit_det_GWG {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ}
    {W : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef) (hG : Function.Injective G.mulVec) :
    IsUnit (G.transpose * W * G).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (gm_posDef_GWG hW hG).isUnit

/-- `G'WG` is symmetric when `W` is. -/
theorem gm_isSymm_GWG {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.IsSymm) : (G.transpose * W * G).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hW.eq,
    Matrix.mul_assoc]

/-- The inverse of a symmetric matrix is symmetric. -/
theorem gm_inv_transpose_of_isSymm {k : ℕ} {N : Matrix (Fin k) (Fin k) ℝ} (hN : N.IsSymm) :
    (N⁻¹).transpose = N⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hN.eq]

/-- `M' = WG₀(G₀'WG₀)⁻¹` for symmetric `W`. -/
theorem gm_M_transpose {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.IsSymm) : (gm_M G W).transpose = W * G * (G.transpose * W * G)⁻¹ := by
  rw [gm_M, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hW.eq,
    gm_inv_transpose_of_isSymm (gm_isSymm_GWG G hW)]
  simp only [Matrix.mul_assoc]

/-- Miao, Theorem 12.1.2 (p. 391): the asymptotic variance
`MSM' = (G₀'WG₀)⁻¹G₀'WSWG₀(G₀'WG₀)⁻¹`. -/
theorem gm_asymVar_eq {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ) {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.IsSymm) (S : Matrix (Fin q) (Fin q) ℝ) :
    gm_M G W * S * (gm_M G W).transpose =
      (G.transpose * W * G)⁻¹ * (G.transpose * W * S * W * G) * (G.transpose * W * G)⁻¹ := by
  rw [gm_M_transpose G hW, gm_M]
  simp only [Matrix.mul_assoc]

/-- Miao, p. 392: with the optimal weighting matrix `W = S⁻¹`,
`MSM' = (G₀'S⁻¹G₀)⁻¹`. -/
theorem gm_efficient_var {k q : ℕ} (G : Matrix (Fin q) (Fin k) ℝ)
    {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosDef)
    (hinv : IsUnit (G.transpose * S⁻¹ * G).det) :
    gm_M G S⁻¹ * S * (gm_M G S⁻¹).transpose = (G.transpose * S⁻¹ * G)⁻¹ := by
  have hSi : S⁻¹.IsSymm := hS.inv.isHermitian.isSymm
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  rw [gm_asymVar_eq G hSi S]
  have h1 : G.transpose * S⁻¹ * S * S⁻¹ * G = G.transpose * S⁻¹ * G := by
    rw [Matrix.mul_assoc (G.transpose * S⁻¹) S, Matrix.mul_nonsing_inv _ hSdet, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv, Matrix.mul_one]

/-- **Efficient GMM** (Miao, p. 392). For every positive definite `W`, positive definite `S` and
full-column-rank `G`, the asymptotic variance with weighting matrix `W` exceeds the one with
`W = S⁻¹` in the Loewner order:
`(G'WG)⁻¹G'WSWG(G'WG)⁻¹ − (G'S⁻¹G)⁻¹` is positive semidefinite. -/
theorem gm_efficiency {k q : ℕ} {G : Matrix (Fin q) (Fin k) ℝ} (hG : Function.Injective G.mulVec)
    {W S : Matrix (Fin q) (Fin q) ℝ} (hW : W.PosDef) (hS : S.PosDef) :
    (gm_M G W * S * (gm_M G W).transpose - (G.transpose * S⁻¹ * G)⁻¹).PosSemidef := by
  set A := gm_M G W with hA
  set B := gm_M G S⁻¹ with hB
  set I := (G.transpose * S⁻¹ * G)⁻¹ with hI
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  have hSs : S.IsSymm := hS.isHermitian.isSymm
  have hSi : S⁻¹.IsSymm := hS.inv.isHermitian.isSymm
  have hWinv := gm_isUnit_det_GWG hW hG
  have hNinv := gm_isUnit_det_GWG hS.inv hG
  have hIs : I.transpose = I := gm_inv_transpose_of_isSymm (gm_isSymm_GWG G hSi)
  have hAG : A * G = 1 := gm_M_mul hWinv
  have hBG : B * G = 1 := gm_M_mul hNinv
  have hBS : B * S = I * G.transpose := by
    rw [hB, gm_M, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSdet, Matrix.mul_one]
  have hBSB : B * S * B.transpose = I := by
    rw [hBS, Matrix.mul_assoc, ← Matrix.transpose_mul, hBG, Matrix.transpose_one,
      Matrix.mul_one]
  have hBSA : B * S * A.transpose = I := by
    rw [hBS, Matrix.mul_assoc, ← Matrix.transpose_mul, hAG, Matrix.transpose_one,
      Matrix.mul_one]
  have hASB : A * S * B.transpose = I := by
    have : S * B.transpose = (B * S).transpose := by
      rw [Matrix.transpose_mul, hSs.eq]
    rw [Matrix.mul_assoc, this, hBS, Matrix.transpose_mul, Matrix.transpose_transpose, hIs,
      ← Matrix.mul_assoc, hAG, Matrix.one_mul]
  have key : (A - B) * S * (A - B).transpose = A * S * A.transpose - I := by
    simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    rw [hBSB, hBSA, hASB]
    abel
  rw [← key]
  have := hS.posSemidef.mul_mul_conjTranspose_same (A - B)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-! ### The J statistic (12.4) -/

/-- Miao, (12.4), p. 394: `J_T = T g_T(θ̂_T)' Ŝ_T⁻¹ g_T(θ̂_T)` (the book prints `Ŝ_T`; the
weighting by the inverse is Hansen's statistic). -/
noncomputable def gm_J {q : ℕ} (T : ℕ) (g : Fin q → ℝ) (S : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  T * (g ⬝ᵥ S⁻¹.mulVec g)

/-- The orthogonal projection `P = H(H'H)⁻¹H'` onto the columns of `H`. -/
noncomputable def gm_proj {q k : ℕ} (H : Matrix (Fin q) (Fin k) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  H * (H.transpose * H)⁻¹ * H.transpose

theorem gm_proj_transpose {q k : ℕ} (H : Matrix (Fin q) (Fin k) ℝ) :
    (gm_proj H).transpose = gm_proj H := by
  have hs : (H.transpose * H).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [gm_proj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    gm_inv_transpose_of_isSymm hs, Matrix.mul_assoc]

theorem gm_proj_mul_self {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) : gm_proj H * H = H := by
  rw [gm_proj, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]

/-- `P` is idempotent. -/
theorem gm_proj_idem {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) : gm_proj H * gm_proj H = gm_proj H := by
  simp only [gm_proj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc H.transpose H, ← Matrix.mul_assoc (H.transpose * H)⁻¹,
    Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

/-- `tr P = k`. -/
theorem gm_proj_trace {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) : (gm_proj H).trace = k := by
  rw [gm_proj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h,
    Matrix.trace_one, Fintype.card_fin]

/-- `I − P` is a symmetric idempotent of trace `q − k` (the degrees of freedom of the J test). -/
theorem gm_resid_proj {q k : ℕ} {H : Matrix (Fin q) (Fin k) ℝ}
    (h : IsUnit (H.transpose * H).det) :
    (1 - gm_proj H).transpose = 1 - gm_proj H ∧
      (1 - gm_proj H) * (1 - gm_proj H) = 1 - gm_proj H ∧
      (1 - gm_proj H).trace = (q : ℝ) - k ∧ (1 - gm_proj H) * H = 0 := by
  refine ⟨by rw [Matrix.transpose_sub, Matrix.transpose_one, gm_proj_transpose], ?_, ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, gm_proj_idem h, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
    abel
  · rw [Matrix.trace_sub, Matrix.trace_one, gm_proj_trace h, Fintype.card_fin]
  · rw [Matrix.sub_mul, gm_proj_mul_self h, Matrix.one_mul, sub_self]

/-- Miao, (12.4), p. 394, the algebra behind `J_T → χ²(q − k)`: write `S = CC'` (for
positive definite `S`, e.g. Cholesky; the identity holds for any `C`) and `H = C⁻¹G`.
The efficient-GMM residual moment `ĝ = (I − G(G'S⁻¹G)⁻¹G'S⁻¹)g₀`
satisfies `ĝ'S⁻¹ĝ = z'(I − P)z` with `z = C⁻¹g₀` and `P = H(H'H)⁻¹H'` (so that, when
`√T z →d N(0, I)`, `J_T` is asymptotically a quadratic form in a symmetric idempotent of rank
`q − k`, `gm_resid_proj`). -/
theorem eq_12_4_algebra {q k : ℕ} {G : Matrix (Fin q) (Fin k) ℝ}
    {S C : Matrix (Fin q) (Fin q) ℝ} (hSC : S = C * C.transpose)
    (g₀ : Fin q → ℝ) :
    let ĝ := (1 - G * (G.transpose * S⁻¹ * G)⁻¹ * G.transpose * S⁻¹).mulVec g₀
    ĝ ⬝ᵥ S⁻¹.mulVec ĝ =
      C⁻¹.mulVec g₀ ⬝ᵥ (1 - gm_proj (C⁻¹ * G)).mulVec (C⁻¹.mulVec g₀) := by
  intro ĝ
  have hSinv : S⁻¹ = C⁻¹.transpose * C⁻¹ := by
    rw [hSC, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  have hN : G.transpose * S⁻¹ * G = (C⁻¹ * G).transpose * (C⁻¹ * G) := by
    rw [hSinv, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hmat : C⁻¹ * (1 - G * (G.transpose * S⁻¹ * G)⁻¹ * G.transpose * S⁻¹) =
      (1 - gm_proj (C⁻¹ * G)) * C⁻¹ := by
    rw [hN, gm_proj, hSinv, Matrix.transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have hz : C⁻¹.mulVec ĝ = (1 - gm_proj (C⁻¹ * G)).mulVec (C⁻¹.mulVec g₀) := by
    simp only [ĝ, Matrix.mulVec_mulVec, hmat]
  have hdot : ĝ ⬝ᵥ S⁻¹.mulVec ĝ = C⁻¹.mulVec ĝ ⬝ᵥ C⁻¹.mulVec ĝ := by
    rw [hSinv, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hdot, hz]
  set R := 1 - gm_proj (C⁻¹ * G)
  set z := C⁻¹.mulVec g₀
  have hRt : R.transpose = R := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, gm_proj_transpose]
  have hRR : R * R = R := by
    change (1 - gm_proj (C⁻¹ * G)) * (1 - gm_proj (C⁻¹ * G)) = 1 - gm_proj (C⁻¹ * G)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul]
    have hP : gm_proj (C⁻¹ * G) * gm_proj (C⁻¹ * G) = gm_proj (C⁻¹ * G) := by
      by_cases hd : IsUnit ((C⁻¹ * G).transpose * (C⁻¹ * G)).det
      · exact gm_proj_idem hd
      · have h0 : gm_proj (C⁻¹ * G) = 0 := by
          simp only [gm_proj, Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.mul_zero,
            Matrix.zero_mul]
        rw [h0, Matrix.zero_mul]
    rw [hP]
    abel
  clear_value R z
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRt, Matrix.mulVec_mulVec, hRR,
    dotProduct_comm]

/-! ### Linear models, OLS, IV and NLS (pp. 388, 395) -/

/-- Miao, p. 388 and p. 395 (OLS / IV): for the linear moment `h_t(β) = z_t(y_t − x_t'β)`,
`g_T(β) = b − Aβ` with `A = (1/T) Σ z_t x_t'` and `b = (1/T) Σ z_t y_t`. -/
theorem gm_linear_sampleMoment {q k : ℕ} (z : ℕ → Fin q → ℝ) (x : ℕ → Fin k → ℝ) (y : ℕ → ℝ)
    (T : ℕ) (β : Fin k → ℝ) :
    (fun i => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, z t i * (y t - x t ⬝ᵥ β)) =
      (fun i => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, z t i * y t) -
        (Matrix.of fun i j => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, z t i * x t j).mulVec β := by
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Miao, p. 388 ("for linear models, these conditions could be solved to obtain a closed-form
solution"): with `g(β) = b − Aβ`, symmetric `W` and invertible `A'WA`, the first-order
condition `A'W(b − Aβ) = 0` holds iff `β = (A'WA)⁻¹A'Wb` (linear GMM; 2SLS for `W` the inverse
instrument moment matrix). -/
theorem gm_linear_foc_iff {q k : ℕ} {A : Matrix (Fin q) (Fin k) ℝ}
    {W : Matrix (Fin q) (Fin q) ℝ} (hinv : IsUnit (A.transpose * W * A).det)
    (b : Fin q → ℝ) (β : Fin k → ℝ) :
    A.transpose.mulVec (W.mulVec (b - A.mulVec β)) = 0 ↔
      β = ((A.transpose * W * A)⁻¹ * A.transpose * W).mulVec b := by
  constructor
  · intro hfoc
    have h := gm_linearization (B := A) (g₀ := b) (d := -β) hfoc
      (by rw [Matrix.mulVec_neg, sub_eq_add_neg]) hinv
    exact neg_inj.1 h
  · intro hβ
    have hM : A.transpose * W * A * (A.transpose * W * A)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hinv
    rw [hβ]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hM, Matrix.one_mul,
      sub_self]

/-- Miao, p. 388: for positive semidefinite `W`, any `β*` satisfying the first-order condition
minimises the linear GMM objective `Q(β) = (b − Aβ)'W(b − Aβ)`. -/
theorem gm_linear_min {q k : ℕ} {A : Matrix (Fin q) (Fin k) ℝ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hW : W.PosSemidef) {b : Fin q → ℝ} {βs : Fin k → ℝ}
    (hfoc : A.transpose.mulVec (W.mulVec (b - A.mulVec βs)) = 0) (β : Fin k → ℝ) :
    gm_quadForm W (b - A.mulVec βs) ≤ gm_quadForm W (b - A.mulVec β) := by
  have hWs : W.IsSymm := hW.isHermitian.isSymm
  set r := b - A.mulVec βs with hr
  set u := A.mulVec (β - βs) with hu
  have hb : b - A.mulVec β = r - u := by
    simp only [r, u, Matrix.mulVec_sub]
    abel
  clear_value r u
  have hur : u ⬝ᵥ W.mulVec r = 0 := by
    rw [hu, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hfoc,
      zero_dotProduct]
  have hru : r ⬝ᵥ W.mulVec u = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hWs.eq, dotProduct_comm, hur]
  have hpsd := hW.dotProduct_mulVec_nonneg u
  simp only [star_trivial] at hpsd
  rw [hb, gm_quadForm_eq, gm_quadForm_eq, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, hur, hru]
  linarith

/-- Miao, p. 395 (OLS and exactly identified IV, `q = k`): if `A` and `W` are invertible the
GMM solution `(A'WA)⁻¹A'Wb = A⁻¹b` does not depend on `W`. -/
theorem gm_exactly_identified {k : ℕ} {A W : Matrix (Fin k) (Fin k) ℝ} (hA : IsUnit A.det)
    (hW : IsUnit W.det) : (A.transpose * W * A)⁻¹ * A.transpose * W = A⁻¹ := by
  have hAt : IsUnit A.transpose.det := by rwa [Matrix.det_transpose]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc W⁻¹, ← Matrix.mul_assoc A.transpose⁻¹, Matrix.nonsing_inv_mul _ hAt,
    Matrix.one_mul, Matrix.nonsing_inv_mul _ hW, Matrix.mul_one]

/-- Miao, p. 395 (NLS): at a local minimiser `β̂` of the sum of squared residuals
`Σ_t (y_t − m_t(β))²`, the NLS moment condition `Σ_t m_t'(β̂)(y_t − m_t(β̂)) = 0` holds. -/
theorem gm_nls_foc {T : ℕ} {m : ℕ → ℝ → ℝ} {m' : ℕ → ℝ} {y : ℕ → ℝ} {βh : ℝ}
    (hd : ∀ t, HasDerivAt (m t) (m' t) βh)
    (hmin : IsLocalMin (fun β => ∑ t ∈ Finset.range T, (y t - m t β) ^ 2) βh) :
    ∑ t ∈ Finset.range T, m' t * (y t - m t βh) = 0 := by
  have hD : HasDerivAt (fun β => ∑ t ∈ Finset.range T, (y t - m t β) ^ 2)
      (∑ t ∈ Finset.range T, 2 * (y t - m t βh) * (-m' t)) βh :=
    HasDerivAt.fun_sum fun t _ => by
      simpa using ((hasDerivAt_const βh (y t)).fun_sub (hd t)).fun_pow 2
  have h0 := hmin.hasDerivAt_eq_zero hD
  have : ∑ t ∈ Finset.range T, 2 * (y t - m t βh) * (-m' t) =
      -2 * ∑ t ∈ Finset.range T, m' t * (y t - m t βh) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [this] at h0
  linarith

end Miao.StructuralEstimation
