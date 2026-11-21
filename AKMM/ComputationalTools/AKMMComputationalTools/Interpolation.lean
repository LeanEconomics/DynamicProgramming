/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NICubicSpline
import NumericalMethods.NIInterpolation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Approximating a function

AKMM, §10.1, pp. 261–263.

* Linear interpolation: `f̂(x) = f(xᵢ) + (f(x_{i+1}) − f(xᵢ))/(x_{i+1} − xᵢ)·(x − xᵢ)` is the line
  through `(xᵢ, f(xᵢ))` and `(x_{i+1}, f(x_{i+1}))` (`linInterp_left`, `linInterp_right`,
  `linInterp_unique`). Its error for `C²` `f` with `|f″| ≤ M` is at most
  `M(x − xᵢ)(x_{i+1} − x)/2 ≤ M(x_{i+1} − xᵢ)²/8` (`linInterp_error`, `linInterp_error_h`): small
  for nearly linear `f`, possibly large for "highly nonlinear" `f`.
* The interpolant is not differentiable at a grid point where the slopes of the two adjacent
  pieces differ (`linInterp_kink_not_differentiable`), and it is differentiable there when they
  agree (`linInterp_kink_differentiable_of_eq`): the book's claim (ii) holds at kinks.
* Cubic spline interpolation: with natural end conditions there is exactly one `C²` piecewise
  cubic through the data (`cubic_spline_existsUnique`, Miao's `ni_natural_spline_existsUnique`).
* (10.1): with `m = n` points the weights solve a square linear system, with a unique solution
  for all data iff the matrix `[φᵢ(xⱼ)]` is invertible (`eq_10_1_unique_iff`, "generically"); for
  polynomials, distinct nodes suffice (`eq_10_1_poly`, Miao's `ni_poly_interp_unique`).
-/

namespace AKMM.ComputationalTools

open Set Filter Topology
open scoped Matrix

/-- AKMM, p. 262, step 2: the linear interpolant on `[xᵢ, x_{i+1}]`. -/
noncomputable def linInterp (xi xi1 fi fi1 x : ℝ) : ℝ := fi + (fi1 - fi) / (xi1 - xi) * (x - xi)

/-- The interpolant passes through `(xᵢ, f(xᵢ))`. -/
theorem linInterp_left (xi xi1 fi fi1 : ℝ) : linInterp xi xi1 fi fi1 xi = fi := by
  simp [linInterp]

/-- The interpolant passes through `(x_{i+1}, f(x_{i+1}))`. -/
theorem linInterp_right {xi xi1 : ℝ} (h : xi ≠ xi1) (fi fi1 : ℝ) :
    linInterp xi xi1 fi fi1 xi1 = fi1 := by
  have : xi1 - xi ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  unfold linInterp
  field_simp
  ring

/-- AKMM, p. 262: "this formula provides the line that connects `(xᵢ, f(xᵢ))` and
`(x_{i+1}, f(x_{i+1}))`": it is the only affine function through the two points. -/
theorem linInterp_unique {xi xi1 : ℝ} (h : xi ≠ xi1) {fi fi1 c d : ℝ}
    (h1 : c * xi + d = fi) (h2 : c * xi1 + d = fi1) (x : ℝ) :
    c * x + d = linInterp xi xi1 fi fi1 x := by
  have hd : xi1 - xi ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have hc : c = (fi1 - fi) / (xi1 - xi) := by
    rw [eq_div_iff hd]; linarith
  unfold linInterp
  rw [← hc]
  linarith

/-- AKMM, p. 262, the interpolation error: for `C²` `f` with `|f″| ≤ M` on `[a, b]`, `a < b`,
`|f(x) − f̂(x)| ≤ M(x − a)(b − x)/2` for every `x ∈ [a, b]`. -/
theorem linInterp_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ} (hab : a < b)
    (hM : ∀ x ∈ Icc a b, |deriv (deriv f) x| ≤ M) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - linInterp a b (f a) (f b) x| ≤ M / 2 * ((x - a) * (b - x)) := by
  obtain ⟨hdiff, -, hd1⟩ := contDiff_succ_iff_deriv.1 (by exact hf : ContDiff ℝ (1 + 1) f)
  have hdd : Differentiable ℝ (deriv f) := hd1.differentiable (by norm_num)
  set s := (f b - f a) / (b - a)
  -- `ψ_σ(x) = σ(f(x) − f̂(x)) − M(x − a)(b − x)/2` is convex for `σ = ±1`
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      σ * (f x - linInterp a b (f a) (f b) x) ≤ M / 2 * ((x - a) * (b - x)) := by
    intro σ hσ
    set ψ : ℝ → ℝ := fun y => σ * (f y - (f a + s * (y - a))) - M / 2 * ((y - a) * (b - y))
    have hψd : ∀ y, HasDerivAt ψ (σ * (deriv f y - s) - M / 2 * (a + b - 2 * y)) y := by
      intro y
      have h1 := (((hdiff y).hasDerivAt.sub (((hasDerivAt_id y).sub_const a).const_mul s
        |>.const_add (f a))).const_mul σ)
      have h2 := (((hasDerivAt_id y).sub_const a).mul ((hasDerivAt_id y).const_sub b)).const_mul
        (M / 2)
      refine (h1.sub h2).congr_deriv ?_
      simp only [id]
      ring
    have hψ' : deriv ψ = fun y => σ * (deriv f y - s) - M / 2 * (a + b - 2 * y) :=
      funext fun y => (hψd y).deriv
    have hψdd : ∀ y, HasDerivAt (deriv ψ) (σ * deriv (deriv f) y + M) y := by
      intro y
      rw [hψ']
      have h := (((hdd y).hasDerivAt.sub_const s).const_mul σ).sub
        (((hasDerivAt_id y).const_mul 2 |>.const_sub (a + b)).const_mul (M / 2))
      refine h.congr_deriv ?_
      ring
    have hψ2 : ∀ y, deriv^[2] ψ y = σ * deriv (deriv f) y + M := by
      intro y
      exact (hψdd y).deriv
    have hconv : ConvexOn ℝ (Icc a b) ψ := by
      refine convexOn_of_deriv2_nonneg (convex_Icc a b)
        (fun y _ => (hψd y).continuousAt.continuousWithinAt)
        (fun y _ => (hψd y).differentiableAt.differentiableWithinAt) ?_ ?_
      · intro y _
        exact (hψdd y).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [hψ2]
        have := hM y (Ioo_subset_Icc_self hy)
        rcases hσ with rfl | rfl
        · linarith [neg_abs_le (deriv (deriv f) y)]
        · linarith [le_abs_self (deriv (deriv f) y)]
    have hle := hconv.le_on_segment (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
      (by rwa [segment_eq_Icc hab.le])
    have hψa : ψ a = 0 := by simp [ψ]
    have hψb : ψ b = 0 := by
      simp only [ψ, s]
      have : b - a ≠ 0 := by linarith
      field_simp
      ring
    rw [hψa, hψb, max_self] at hle
    simp only [ψ] at hle
    unfold linInterp
    linarith
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-- AKMM, p. 262: on a grid with spacing `h = x_{i+1} − xᵢ` the error is at most `Mh²/8`
("the approximation error can be large if the underlying function is highly nonlinear"). -/
theorem linInterp_error_h {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ} (hab : a < b)
    (hM : ∀ x ∈ Icc a b, |deriv (deriv f) x| ≤ M) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - linInterp a b (f a) (f b) x| ≤ M * (b - a) ^ 2 / 8 := by
  have h := linInterp_error hf hab hM hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a (left_mem_Icc.2 hab.le))
  calc _ ≤ M / 2 * ((x - a) * (b - x)) := h
    _ ≤ M / 2 * ((b - a) ^ 2 / 4) := by
        gcongr
        nlinarith [sq_nonneg (x - a - (b - x))]
    _ = M * (b - a) ^ 2 / 8 := by ring

/-- Two linear pieces meeting at the grid point `c` with slopes `s₁` (left) and `s₂` (right). -/
noncomputable def kink (v s₁ s₂ c x : ℝ) : ℝ := if x ≤ c then v + s₁ * (x - c) else v + s₂ * (x - c)

/-- AKMM, p. 262, disadvantage (ii): "the approximated function is not differentiable at the grid
points" — at a grid point where the slopes of the adjacent pieces differ. -/
theorem linInterp_kink_not_differentiable {v s₁ s₂ c : ℝ} (hs : s₁ ≠ s₂) :
    ¬ DifferentiableAt ℝ (kink v s₁ s₂ c) c := by
  intro hd
  have hl : HasDerivWithinAt (kink v s₁ s₂ c) s₁ (Iic c) c := by
    have h := (((hasDerivAt_id c).sub_const c).const_mul s₁).const_add v
    refine (h.hasDerivWithinAt.congr (fun y hy => ?_) ?_).congr_deriv (by simp)
    · simp [kink, show y ≤ c from hy]
    · simp [kink]
  have hr : HasDerivWithinAt (kink v s₁ s₂ c) s₂ (Ici c) c := by
    have h := (((hasDerivAt_id c).sub_const c).const_mul s₂).const_add v
    refine (h.hasDerivWithinAt.congr (fun y hy => ?_) ?_).congr_deriv (by simp)
    · rcases eq_or_lt_of_le (show c ≤ y from hy) with rfl | hlt
      · simp [kink]
      · simp [kink, not_le.2 hlt]
    · simp [kink]
  have e1 := (uniqueDiffWithinAt_Iic c).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hl
  have e2 := (uniqueDiffWithinAt_Ici c).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hr
  exact hs (e1.symm.trans e2)

/-- When the two slopes agree there is no kink and the interpolant is differentiable, so the
book's claim (ii) needs the slopes to differ. -/
theorem linInterp_kink_differentiable_of_eq (v s c : ℝ) :
    DifferentiableAt ℝ (kink v s s c) c := by
  have : kink v s s c = fun x => v + s * (x - c) := by
    funext x; unfold kink; split_ifs <;> rfl
  rw [this]
  fun_prop

/-- AKMM, p. 263 (cubic spline interpolation): for nodes `x₀ < ⋯ < xₙ` and any values, there is
exactly one piecewise cubic, with continuous first and second derivatives at the interior nodes
and the boundary conditions `f̂″(x₀) = f̂″(xₙ) = 0`, interpolating the values ("we can compute
[the second derivatives] by imposing continuity of the first derivatives at each grid point
(plus some boundary conditions)"). -/
theorem cubic_spline_existsUnique {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, Miao.NumericalMethods.ni_CubicInterp x y q ∧
      Miao.NumericalMethods.ni_CubicSmooth x q ∧
      Miao.NumericalMethods.ni_cub2 (Miao.NumericalMethods.ni_piece q 0) (x 0) = 0 ∧
      Miao.NumericalMethods.ni_cub2 (Miao.NumericalMethods.ni_piece q (n - 1)) (x n) = 0 :=
  Miao.NumericalMethods.ni_natural_spline_existsUnique hn hx y

/-- AKMM, (10.1), p. 263: with `m = n` points, the weights `aᵢ` with
`∑ᵢ aᵢφᵢ(xⱼ) = f(xⱼ)` for all `j` exist and are unique for all data exactly when the matrix
`Φ = [φᵢ(xⱼ)]` is invertible ("generically a unique set of `aᵢ`s solve (10.1)"). -/
theorem eq_10_1_unique_iff {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ) :
    (∀ y : Fin n → ℝ, ∃! a : Fin n → ℝ, Φ *ᵥ a = y) ↔ IsUnit Φ :=
  ⟨fun h => Matrix.mulVec_surjective_iff_isUnit.1 fun y => (h y).exists,
    fun h y => by
      obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 h y
      exact ⟨a, ha, fun b hb => Matrix.mulVec_injective_iff_isUnit.2 h (hb.trans ha.symm)⟩⟩

/-- AKMM, (10.1), p. 263, for the polynomial basis `φᵢ(x) = x^{i−1}`: at `n` distinct points
there is exactly one polynomial of degree `< n` matching `f`. -/
theorem eq_10_1_poly {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (y : Fin n → ℝ) :
    ∃! p : Polynomial ℝ, p.degree < n ∧ ∀ i, p.eval (x i) = y i :=
  Miao.NumericalMethods.ni_poly_interp_unique x hx y

end AKMM.ComputationalTools
