/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import NumericalMethods.NIChebInterp
import NumericalMethods.NICubicSpline

/-!
# Exercise 11.1 (Miao, p. 383)

The exercise asks for the CompEcon toolbox to construct the 5- and 20-degree approximants of
`f(x) = |x|^{0.6}` and `f(x) = (1 + 2x²)^{−1}` on `[−1, 1]` by (a) monomial interpolation on a
uniform grid, (b) Chebyshev interpolation at the Chebyshev nodes, (c) linear splines and (d) cubic
splines on uniform nodes, and to plot the approximation errors. The computation and the plots are
not formalised. The mathematical facts behind the exercise are:

* `ex_11_1_f1_not_differentiable`, `ex_11_1_f1_continuous`: `|x|^{0.6}` is continuous but not
  differentiable at `0`, so Theorem 11.3.1 (which needs `k ≥ 1` derivatives) does not apply to it;
* `ex_11_1_f2_smooth`: `(1 + 2x²)^{−1}` is `C^∞`;
* `ex_11_1`: for every `N ≥ 3` (in particular the degrees `5` and `20` of the exercise) and every
  `f`, the four approximants are well defined: (a) the monomial interpolant on the uniform grid
  `xᵢ = −1 + 2i/N` exists and is unique; (b) the Chebyshev interpolant interpolates `f` at the
  Chebyshev nodes; (c) the linear spline on the uniform nodes exists and is unique on `[−1, 1]`;
  (d) the cubic spline with the not-a-knot end condition (CompEcon's default) exists and is unique.
-/

open Polynomial Real

namespace Miao.NumericalMethods

/-- **Exercise 11.1** (Miao, p. 383): `|x|^{0.6}` is not differentiable at `0`. -/
theorem ex_11_1_f1_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x : ℝ => |x| ^ (0.6 : ℝ)) 0 := by
  intro h
  set y := deriv (fun x : ℝ => |x| ^ (0.6 : ℝ)) 0
  have ht : Filter.Tendsto (fun t : ℝ => t ^ ((0.6 : ℝ) - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_right
    intro x (hx : 0 < x)
    simp only [zero_add, abs_zero, smul_eq_mul, abs_of_pos hx]
    rw [Real.zero_rpow (by norm_num), sub_zero]
    field_simp
    nth_rw 1 [← add_sub_cancel 1 (0.6 : ℝ), Real.rpow_add hx]
    simp
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_rpow_neg_nhdsGT_zero (by norm_num)) y ht

/-- **Exercise 11.1** (Miao, p. 383): `|x|^{0.6}` is continuous. -/
theorem ex_11_1_f1_continuous : Continuous (fun x : ℝ => |x| ^ (0.6 : ℝ)) :=
  continuous_abs.rpow_const fun _ => Or.inr (by norm_num)

/-- **Exercise 11.1** (Miao, p. 383): `(1 + 2x²)^{−1}` is `C^∞`. -/
theorem ex_11_1_f2_smooth : ContDiff ℝ ⊤ (fun x : ℝ => (1 + 2 * x ^ 2)⁻¹) :=
  ContDiff.inv (by fun_prop) fun x => by positivity

/-- The uniform grid `xᵢ = −1 + 2i/N` on `[−1, 1]`. -/
noncomputable def ni_uniformGrid (N : ℕ) (i : ℕ) : ℝ := -1 + 2 * i / N

theorem ni_uniformGrid_strictMono {N : ℕ} (hN : 0 < N) : StrictMono (ni_uniformGrid N) := by
  intro a b hab
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : (a : ℝ) < b := by exact_mod_cast hab
  unfold ni_uniformGrid
  have : 2 * (a : ℝ) / N < 2 * b / N := by
    apply div_lt_div_of_pos_right _ hN'
    linarith
  linarith

theorem ni_uniformGrid_ends {N : ℕ} (hN : 0 < N) :
    ni_uniformGrid N 0 = -1 ∧ ni_uniformGrid N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨by simp [ni_uniformGrid], ?_⟩
  unfold ni_uniformGrid
  field_simp
  ring

/-- **Exercise 11.1** (Miao, p. 383): for `N ≥ 3` (the exercise uses `N = 5` and `N = 20`) and any
`f`, (a) the monomial interpolant on the uniform grid exists uniquely, (b) the Chebyshev
interpolant matches `f` at the Chebyshev nodes, (c) the linear spline on the uniform nodes exists
and is unique on `[−1, 1]`, and (d) the not-a-knot cubic spline on the uniform nodes exists
uniquely. -/
theorem ex_11_1 (N : ℕ) (hN : 3 ≤ N) (f : ℝ → ℝ) :
    (∃! c : Fin (N + 1) → ℝ, ∀ i : Fin (N + 1),
        ni_fhat ni_monomial c (ni_uniformGrid N i) = f (ni_uniformGrid N i)) ∧
    (∀ k ∈ Finset.Icc 1 (N + 1),
        (ni_chebInterp N f).eval (ni_chebNode (N + 1) k) = f (ni_chebNode (N + 1) k)) ∧
    (ni_IsSpline 2 N (ni_uniformGrid N) (ni_linSpline N (ni_uniformGrid N)
        (fun i => f (ni_uniformGrid N i))) ∧
      (∀ i ≤ N, ni_linSpline N (ni_uniformGrid N) (fun i => f (ni_uniformGrid N i))
        (ni_uniformGrid N i) = f (ni_uniformGrid N i)) ∧
      ∀ φ, ni_IsSpline 2 N (ni_uniformGrid N) φ →
        (∀ i ≤ N, φ (ni_uniformGrid N i) = f (ni_uniformGrid N i)) →
        ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          φ t = ni_linSpline N (ni_uniformGrid N) (fun i => f (ni_uniformGrid N i)) t) ∧
    (∃! q : Fin N → Fin 4 → ℝ,
        ni_CubicInterp (ni_uniformGrid N) (fun i => f (ni_uniformGrid N i)) q ∧
        ni_CubicSmooth (ni_uniformGrid N) q ∧
        ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
          ni_cub3 (ni_piece q (N - 2)) = ni_cub3 (ni_piece q (N - 1))) := by
  have hN0 : 0 < N := by omega
  have hmono := ni_uniformGrid_strictMono hN0
  obtain ⟨hlo, hhi⟩ := ni_uniformGrid_ends hN0
  have hlin := ni_linear_spline_exists hN0 hmono (fun i => f (ni_uniformGrid N i))
  refine ⟨?_, (ni_chebInterp_spec N f).2, ⟨hlin.1, hlin.2, fun φ hφ hφi t ht => ?_⟩,
    ni_notAKnot_spline_existsUnique hN hmono _⟩
  · refine ni_monomial_interp_existsUnique _ ?_ _
    intro a b hab
    exact Fin.ext (by exact_mod_cast hmono.injective hab)
  · refine ni_linear_spline_unique hN0 hφ hlin.1 (fun i hi => ?_) t ?_
    · rw [hφi i hi, hlin.2 i hi]
    · rwa [hlo, hhi]

end Miao.NumericalMethods
