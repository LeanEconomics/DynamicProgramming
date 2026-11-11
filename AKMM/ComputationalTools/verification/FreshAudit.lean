import NumericalMethods.NICubicSpline
import NumericalMethods.NIInterpolation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import NumericalMethods.NQAR1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import JobSearch.Contractions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import RationalExpectations.ScalarRE
import DifferenceEquations.Nonsingular
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bisection

AKMM, §10.2–10.2.1, pp. 263–265. The bisection method for `f(x) = 0`:

1. bracketing: `sign(f a) ≠ sign(f b)`; for continuous `f` there is a root in `[a, b]`
   (`bisect_bracket_root`);
2. the step: with `c = (a + b)/2`, replace `a` by `c` if `sign(f c) = sign(f a)`, otherwise
   replace `b` by `c` (`bisectStep`, `bisect_sign_eq_iff`);
3. stop when `b − a` is below the tolerance.

Proved: each step halves the bracket (`bisect_length`), the sign change is kept
(`bisect_bracket`), the endpoints converge to a root of a continuous `f` and `f(a_k) → 0`
(`bisect_converges`); the number of steps needed for a tolerance `ε` is any `k > log₂((b−a)/ε)`
(`bisect_iteration_count`), and 10 steps reach `10⁻³` on `[0, 1]` where 9 do not
(`bisect_ten_steps`). The procedure ends even when no root exists: a discontinuous bracketing
function with no zero (`bisect_discontinuous_no_root`).

Departure: the step tests `0 < f a · f c` instead of `sign(f c) = sign(f a)`; the two agree
whenever `f a ≠ 0` (`bisect_sign_eq_iff`), which holds at the start of the book's bracket.
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- AKMM, p. 264, the comparison in step 2: when `f a ≠ 0`, `sign(f c) = sign(f a)` exactly
when `f a · f c > 0`. -/
theorem bisect_sign_eq_iff {x y : ℝ} (hx : x ≠ 0) :
    SignType.sign y = SignType.sign x ↔ 0 < x * y := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_trichotomy y 0 with h' | h' | h'
  · simp [sign_neg h, sign_neg h', mul_pos_of_neg_of_neg h h']
  · simp [sign_neg h, h']
  · simp only [sign_neg h, sign_pos h']
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; nlinarith
  · simp only [sign_pos h, sign_neg h']
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; nlinarith
  · simp [sign_pos h, h']
  · simp [sign_pos h, sign_pos h', mul_pos h h']

/-- AKMM, p. 264, step 2: one bisection step on the bracket `(a, b)`, with midpoint
`c = (a + b)/2`; `a` moves to `c` when `f a` and `f c` have the same (nonzero) sign, otherwise
`b` moves to `c`. -/
noncomputable def bisectStep (f : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  if 0 < f ab.1 * f ((ab.1 + ab.2) / 2) then ((ab.1 + ab.2) / 2, ab.2)
  else (ab.1, (ab.1 + ab.2) / 2)

/-- AKMM, p. 264, step 3: the bracket after `k` bisection steps from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | k + 1 => bisectStep f (bisect f a b k)

/-- The step either keeps `b` and moves `a` to the midpoint or keeps `a` and moves `b`. -/
theorem bisectStep_cases (f : ℝ → ℝ) (ab : ℝ × ℝ) :
    (bisectStep f ab = ((ab.1 + ab.2) / 2, ab.2) ∧ 0 < f ab.1 * f ((ab.1 + ab.2) / 2)) ∨
      (bisectStep f ab = (ab.1, (ab.1 + ab.2) / 2) ∧ ¬ 0 < f ab.1 * f ((ab.1 + ab.2) / 2)) := by
  unfold bisectStep
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

/-- AKMM, p. 264: "each iteration cuts the interval in half": `b_k − a_k = (b − a)/2ᵏ`. -/
theorem bisect_length (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    (bisect f a b k).2 - (bisect f a b k).1 = (b - a) / 2 ^ k := by
  induction k with
  | zero => simp [bisect]
  | succ k ih =>
    simp only [bisect]
    rcases bisectStep_cases f (bisect f a b k) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      · simp only [pow_succ]
        rw [div_mul_eq_div_div, ← ih]
        ring

/-- The left endpoint never decreases and the right endpoint never increases. -/
theorem bisect_mono (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    (bisect f a b k).1 ≤ (bisect f a b (k + 1)).1 ∧
      (bisect f a b (k + 1)).2 ≤ (bisect f a b k).2 := by
  have hl := bisect_length f a b k
  have hpos : 0 ≤ (b - a) / 2 ^ k := div_nonneg (by linarith) (by positivity)
  simp only [bisect]
  rcases bisectStep_cases f (bisect f a b k) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    constructor <;> dsimp only <;> linarith

/-- AKMM, p. 264: bisection keeps the bracket: if `f a · f b ≤ 0` then `f a_k · f b_k ≤ 0`. -/
theorem bisect_bracket (f : ℝ → ℝ) {a b : ℝ} (hfab : f a * f b ≤ 0) (k : ℕ) :
    f (bisect f a b k).1 * f (bisect f a b k).2 ≤ 0 := by
  induction k with
  | zero => simpa [bisect] using hfab
  | succ k ih =>
    simp only [bisect]
    set p := bisect f a b k
    rcases bisectStep_cases f p with ⟨h, hpos⟩ | ⟨h, hneg⟩ <;> rw [h]
    · dsimp only
      by_contra hc
      rw [not_le] at hc
      have h1 : 0 < (f p.1 * f ((p.1 + p.2) / 2)) * (f ((p.1 + p.2) / 2) * f p.2) :=
        mul_pos hpos hc
      have h2 : (f p.1 * f ((p.1 + p.2) / 2)) * (f ((p.1 + p.2) / 2) * f p.2) =
          (f p.1 * f p.2) * (f ((p.1 + p.2) / 2)) ^ 2 := by ring
      rw [h2] at h1
      nlinarith [sq_nonneg (f ((p.1 + p.2) / 2))]
    · dsimp only
      exact not_lt.mp hneg

/-- The bracket stays inside `[a, b]` and ordered. -/
theorem bisect_mem (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    a ≤ (bisect f a b k).1 ∧ (bisect f a b k).1 ≤ (bisect f a b k).2 ∧
      (bisect f a b k).2 ≤ b := by
  induction k with
  | zero => simp [bisect, hab]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := bisect_mono f hab k
    have hl := bisect_length f a b (k + 1)
    have hpos : 0 ≤ (b - a) / 2 ^ (k + 1) := div_nonneg (by linarith) (by positivity)
    refine ⟨ih.1.trans h1, by linarith, h2.trans ih.2.2⟩

/-- AKMM, p. 264, step 1 (bracketing): "if `f` is continuous, this condition implies that at
least one solution to `f(x) = 0` exists in the bracket `[a, b]`". -/
theorem bisect_bracket_root {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfab : f a * f b ≤ 0) :
    ∃ x ∈ Set.Icc a b, f x = 0 := by
  rcases lt_trichotomy (f a) 0 with ha | ha | ha
  · have hb : 0 ≤ f b := by nlinarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
    exact ⟨x, hx, hfx⟩
  · exact ⟨a, ⟨le_rfl, hab⟩, ha⟩
  · have hb : f b ≤ 0 := by nlinarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hf ⟨hb, ha.le⟩
    exact ⟨x, hx, hfx⟩

/-- AKMM, pp. 264–265: for continuous `f` with `f a · f b ≤ 0`, both endpoints of the bisection
bracket converge to a root `x ∈ [a, b]`, with `|a_k − x| ≤ (b − a)/2ᵏ`, and `f(a_k) → 0`
("check that `f(a)` is close to zero, and use `a` as the solution"). -/
theorem bisect_converges {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfab : f a * f b ≤ 0) :
    ∃ x ∈ Set.Icc a b, f x = 0 ∧
      Tendsto (fun k => (bisect f a b k).1) atTop (𝓝 x) ∧
      Tendsto (fun k => (bisect f a b k).2) atTop (𝓝 x) ∧
      (∀ k, |(bisect f a b k).1 - x| ≤ (b - a) / 2 ^ k) ∧
      Tendsto (fun k => f (bisect f a b k).1) atTop (𝓝 0) := by
  set A : ℕ → ℝ := fun k => (bisect f a b k).1
  set B : ℕ → ℝ := fun k => (bisect f a b k).2
  have hAmono : Monotone A := monotone_nat_of_le_succ fun k => (bisect_mono f hab k).1
  have hBanti : Antitone B := antitone_nat_of_succ_le fun k => (bisect_mono f hab k).2
  have hAb : ∀ k, A k ≤ b := fun k => ((bisect_mem f hab k).2.1).trans (bisect_mem f hab k).2.2
  have hbdd : BddAbove (Set.range A) := ⟨b, by rintro _ ⟨k, rfl⟩; exact hAb k⟩
  set x := ⨆ k, A k
  have hA : Tendsto A atTop (𝓝 x) := tendsto_atTop_ciSup hAmono hbdd
  have hlen : Tendsto (fun k : ℕ => (b - a) / 2 ^ k) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (b - a)
    simpa [div_eq_mul_inv, one_div, inv_pow] using h
  have hBeq : B = fun k => A k + (b - a) / 2 ^ k := by
    funext k
    have := bisect_length f a b k
    simp only [A, B]
    linarith
  have hB : Tendsto B atTop (𝓝 x) := by
    rw [hBeq]
    simpa using hA.add hlen
  have hAx : ∀ k, A k ≤ x := fun k => le_ciSup hbdd k
  have hxB : ∀ k, x ≤ B k := fun k =>
    le_of_tendsto hB (eventually_atTop.2 ⟨k, fun _ hj => hBanti hj⟩)
  have hxmem : x ∈ Set.Icc a b :=
    ⟨(bisect_mem f hab 0).1.trans (hAx 0), (hxB 0).trans (bisect_mem f hab 0).2.2⟩
  have hAmem : ∀ k, A k ∈ Set.Icc a b := fun k =>
    ⟨(bisect_mem f hab k).1, hAb k⟩
  have hBmem : ∀ k, B k ∈ Set.Icc a b := fun k =>
    ⟨(bisect_mem f hab k).1.trans (bisect_mem f hab k).2.1, (bisect_mem f hab k).2.2⟩
  have hfA : Tendsto (fun k => f (A k)) atTop (𝓝 (f x)) :=
    (hf x hxmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hA, Eventually.of_forall hAmem⟩)
  have hfB : Tendsto (fun k => f (B k)) atTop (𝓝 (f x)) :=
    (hf x hxmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hB, Eventually.of_forall hBmem⟩)
  have hprod : f x * f x ≤ 0 :=
    le_of_tendsto (hfA.mul hfB) (Eventually.of_forall fun k => bisect_bracket f hfab k)
  have hfx : f x = 0 := by nlinarith [mul_self_nonneg (f x)]
  refine ⟨x, hxmem, hfx, hA, hB, fun k => ?_, hfx ▸ hfA⟩
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hAx k))]
  have := bisect_length f a b k
  have := hxB k
  simp only [A, B] at *
  linarith

/-- AKMM, p. 265: "we know how many iterations it requires to shrink the starting interval down
the tolerance level": after any `k > log₂((b − a)/ε)` steps the bracket is shorter than `ε`. -/
theorem bisect_iteration_count (f : ℝ → ℝ) {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {k : ℕ}
    (hk : Real.logb 2 ((b - a) / ε) < k) :
    (bisect f a b k).2 - (bisect f a b k).1 < ε := by
  rw [bisect_length]
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos (by linarith) hε),
    Real.rpow_natCast] at hk
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hk
  linarith

/-- AKMM, p. 265: "it always ends after a finite number of steps": for every tolerance `ε > 0`
some number of steps brings the bracket below `ε`. -/
theorem bisect_terminates (f : ℝ → ℝ) {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∃ k : ℕ, (bisect f a b k).2 - (bisect f a b k).1 < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.logb 2 ((b - a) / ε))
  exact ⟨k, bisect_iteration_count f hab hε hk⟩

/-- AKMM, p. 265: on `[0, 1]` with accuracy `10⁻³`, "only 10 evaluations in the case of
bisection (because `(1/2)¹⁰ = 1/1024`)": ten steps suffice and nine do not. -/
theorem bisect_ten_steps (f : ℝ → ℝ) :
    (bisect f 0 1 10).2 - (bisect f 0 1 10).1 < 1 / 1000 ∧
      ¬ (bisect f 0 1 9).2 - (bisect f 0 1 9).1 < 1 / 1000 := by
  rw [bisect_length, bisect_length]
  norm_num

/-- The step function of the counterexample: `−1` left of `1/2`, `1` from `1/2` on. -/
noncomputable def bisectJump (x : ℝ) : ℝ := if x < 1 / 2 then -1 else 1

/-- AKMM, p. 265: "the procedure always ends, even when no solutions exist, for example, because
`f(x)` is not continuous": the jump function brackets on `[0, 1]`, has no zero, and the
bisection bracket still shrinks to length `2⁻ᵏ`. -/
theorem bisect_discontinuous_no_root :
    bisectJump 0 * bisectJump 1 < 0 ∧ (∀ x, bisectJump x ≠ 0) ∧
      ∀ k : ℕ, (bisect bisectJump 0 1 k).2 - (bisect bisectJump 0 1 k).1 = 1 / 2 ^ k := by
  refine ⟨by norm_num [bisectJump], fun x => ?_, fun k => by rw [bisect_length]; ring⟩
  unfold bisectJump
  split_ifs <;> norm_num

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Newton–Raphson, Newton's method for optimisation, and finite differences

AKMM, §10.2.2, pp. 265–266, §10.3.2–10.3.3, pp. 267–269.

* (10.2): `x̂ = x₀ − f(x₀)/f′(x₀)` is the root of the tangent line (`eq_10_2`), so the
  Newton–Raphson step is exact for affine `f` (`newton_affine_exact`).
* Local quadratic convergence: for `C²` `f` with `f(x*) = 0` and `f′(x*) ≠ 0` there are `δ > 0`
  and `C` with `|N(x) − x*| ≤ C|x − x*|²` and `|N(x) − x*| ≤ |x − x*|/2` on `|x − x*| < δ`
  (`newton_local_quadratic`), and from any such start the iterates converge to `x*`, at least
  geometrically and quadratically (`newton_converges`). The book only says that the method is
  faster "if `x₀` is close to the true solution"; Mathlib has no Newton convergence theorem for
  real functions, so this is proved here by the mean value inequality and the local Lipschitz
  property of `f′`.
* The central difference `(f(x+h) − f(x−h))/(2h) → f′(x)` as `h → 0` (`central_difference_tendsto`),
  exact for quadratics (`central_difference_quadratic`).
* (10.3): `x̂ = x₀ − F′(x₀)/F″(x₀)` is the critical point of the quadratic model of `F`, its
  maximiser when `F″(x₀) < 0` (`eq_10_3`, `eq_10_3_max`); the method is exact for quadratic `F`
  (`newtonOpt_quadratic_exact`); and Newton's method for `max F` is Newton–Raphson applied to
  `F′ = 0` (`newtonOpt_eq_newtonStep_deriv`, §10.3.3).
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- AKMM, (10.2) and step 2, p. 265–266: the Newton–Raphson step `x ↦ x − f(x)/f′(x)`. -/
noncomputable def newtonStep (f : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / deriv f x

/-- AKMM, (10.2), p. 265: when `f′(x₀) ≠ 0`, `x̂ = x₀ − f(x₀)/f′(x₀)` is the unique root of the
linear approximation `f(x₀) + f′(x₀)(x − x₀)`. -/
theorem eq_10_2 (f : ℝ → ℝ) {x₀ : ℝ} (hd : deriv f x₀ ≠ 0) (x : ℝ) :
    f x₀ + deriv f x₀ * (x - x₀) = 0 ↔ x = newtonStep f x₀ := by
  unfold newtonStep
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- AKMM, p. 265: "If `f(x)` is indeed linear, `x̂` delivers the solution in one step": for
`f(x) = cx + d` with `c ≠ 0`, `N(x₀) = −d/c` from every `x₀`, and `f(−d/c) = 0`. -/
theorem newton_affine_exact {c d : ℝ} (hc : c ≠ 0) (x₀ : ℝ) :
    newtonStep (fun x => c * x + d) x₀ = -d / c ∧ c * (-d / c) + d = 0 := by
  have hderiv : deriv (fun x => c * x + d) x₀ = c := by
    have := ((hasDerivAt_id x₀).const_mul c).add_const d
    simp only [id, mul_one] at this
    exact this.deriv
  refine ⟨?_, by field_simp; ring⟩
  unfold newtonStep
  rw [hderiv]
  field_simp
  ring

/-- AKMM, p. 266 (local quadratic convergence of Newton–Raphson, which the book describes as
"much faster than bisection" when "`x₀` is close to the true solution"): for `C²` `f` with a
simple root `x*` (`f(x*) = 0`, `f′(x*) ≠ 0`) there are `δ > 0` and `C ≥ 0` such that every
`x` with `|x − x*| < δ` has `|N(x) − x*| ≤ C|x − x*|²` and `|N(x) − x*| ≤ |x − x*|/2`. -/
theorem newton_local_quadratic {f : ℝ → ℝ} {xs : ℝ} (hf : ContDiff ℝ 2 f) (hroot : f xs = 0)
    (hd : deriv f xs ≠ 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ x, |x - xs| < δ →
      |newtonStep f x - xs| ≤ C * |x - xs| ^ 2 ∧ |newtonStep f x - xs| ≤ |x - xs| / 2 := by
  obtain ⟨hdiff, -, hd1⟩ := contDiff_succ_iff_deriv.1 (by exact hf : ContDiff ℝ (1 + 1) f)
  obtain ⟨K, t, ht, hK⟩ := (hd1.contDiffAt (x := xs)).exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ht
  set m := |deriv f xs| / 2 with hm_def
  have hm : 0 < m := by positivity
  obtain ⟨r2, hr2, hr2'⟩ := Metric.continuousAt_iff.1 hd1.continuous.continuousAt m hm
  set δ := min (min r r2) (m / (2 * ((K : ℝ) + 1))) with hδ_def
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hδ : 0 < δ := lt_min (lt_min hr hr2) (by positivity)
  refine ⟨δ, hδ, K / m, by positivity, fun x hx => ?_⟩
  have hxr : |x - xs| < r := hx.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hxr2 : |x - xs| < r2 := hx.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hxm : |x - xs| < m / (2 * ((K : ℝ) + 1)) := hx.trans_le (min_le_right _ _)
  -- the derivative stays away from zero
  have hfx : m < |deriv f x| := by
    have h1 := hr2' (by rw [Real.dist_eq]; exact hxr2)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (deriv f xs) (deriv f x)
    rw [abs_sub_comm] at h1
    linarith
  have hfx0 : deriv f x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hfx
    linarith
  -- the segment between `x` and `x*` lies in the Lipschitz neighbourhood
  set s := Set.uIcc x xs
  have hseg : ∀ y ∈ s, |y - x| ≤ |x - xs| ∧ y ∈ t := by
    intro y hy
    have hy' := Set.mem_uIcc.1 hy
    have h1 : |y - x| ≤ |x - xs| := by
      rcases hy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith
    have h2 : |y - xs| ≤ |x - xs| := by
      rcases hy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    refine ⟨h1, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact h2.trans_lt hxr
  have hxt : x ∈ t := (hseg x Set.left_mem_uIcc).2
  -- the mean value inequality for `g(y) = f(y) − f′(x) y`
  have hg : ∀ y ∈ s, HasDerivWithinAt (fun y => f y - deriv f x * y)
      (deriv f y - deriv f x) s y := by
    intro y _
    have h' : HasDerivAt (fun y => f y - deriv f x * y) (deriv f y - deriv f x * 1) y :=
      (hdiff y).hasDerivAt.sub ((hasDerivAt_id y).const_mul (deriv f x))
    rw [mul_one] at h'
    exact h'.hasDerivWithinAt
  have hbound : ∀ y ∈ s, ‖deriv f y - deriv f x‖ ≤ K * |x - xs| := by
    intro y hy
    obtain ⟨h1, h2⟩ := hseg y hy
    have := hK.dist_le_mul y h2 x hxt
    rw [Real.dist_eq, Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.trans (mul_le_mul_of_nonneg_left h1 hK0)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound (convex_uIcc x xs)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs, hroot] at hmvt
  have hkey : newtonStep f x - xs =
      (0 - deriv f x * xs - (f x - deriv f x * x)) / deriv f x := by
    unfold newtonStep
    field_simp
    ring
  have hmain : |newtonStep f x - xs| ≤ K / m * |x - xs| ^ 2 := by
    rw [hkey, abs_div]
    have hpos : 0 < |deriv f x| := by linarith
    rw [div_le_iff₀ hpos]
    have h3 : |xs - x| = |x - xs| := abs_sub_comm _ _
    rw [h3] at hmvt
    calc |0 - deriv f x * xs - (f x - deriv f x * x)| ≤ K * |x - xs| * |x - xs| := hmvt
      _ = K / m * |x - xs| ^ 2 * m := by field_simp
      _ ≤ K / m * |x - xs| ^ 2 * |deriv f x| := by
          apply mul_le_mul_of_nonneg_left hfx.le; positivity
  refine ⟨hmain, hmain.trans ?_⟩
  have habs : 0 ≤ |x - xs| := abs_nonneg _
  have hc : K / m * |x - xs| ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    have := mul_le_mul_of_nonneg_left hxm.le hK0
    calc (K : ℝ) * |x - xs| ≤ K * (m / (2 * (K + 1))) := this
      _ ≤ 1 / 2 * m := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  calc K / m * |x - xs| ^ 2 = (K / m * |x - xs|) * |x - xs| := by ring
    _ ≤ 1 / 2 * |x - xs| := mul_le_mul_of_nonneg_right hc habs
    _ = |x - xs| / 2 := by ring

/-- AKMM, p. 266, step 3 (iterating `x_{i+1} = N(x_i)`): from any start within `δ` of a simple
root of a `C²` function the Newton–Raphson iterates stay within `δ`, satisfy
`|x_n − x*| ≤ |x₀ − x*|/2ⁿ` and `|x_{n+1} − x*| ≤ C|x_n − x*|²`, and converge to `x*`. -/
theorem newton_converges {f : ℝ → ℝ} {xs : ℝ} (hf : ContDiff ℝ 2 f) (hroot : f xs = 0)
    (hd : deriv f xs ≠ 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ x₀, |x₀ - xs| < δ →
      (∀ n, |(newtonStep f)^[n] x₀ - xs| ≤ |x₀ - xs| / 2 ^ n) ∧
      (∀ n, |(newtonStep f)^[n + 1] x₀ - xs| ≤ C * |(newtonStep f)^[n] x₀ - xs| ^ 2) ∧
      Tendsto (fun n => (newtonStep f)^[n] x₀) atTop (𝓝 xs) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := newton_local_quadratic hf hroot hd
  refine ⟨δ, hδ, C, hC, fun x₀ hx₀ => ?_⟩
  have hgeo : ∀ n, |(newtonStep f)^[n] x₀ - xs| ≤ |x₀ - xs| / 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt : |(newtonStep f)^[n] x₀ - xs| < δ :=
        ih.trans_lt ((div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))).trans_lt hx₀)
      rw [Function.iterate_succ_apply']
      calc |newtonStep f ((newtonStep f)^[n] x₀) - xs| ≤ |(newtonStep f)^[n] x₀ - xs| / 2 :=
            (h _ hlt).2
        _ ≤ |x₀ - xs| / 2 ^ n / 2 := by gcongr
        _ = |x₀ - xs| / 2 ^ (n + 1) := by rw [pow_succ, div_div]
  refine ⟨hgeo, fun n => ?_, ?_⟩
  · have hlt : |(newtonStep f)^[n] x₀ - xs| < δ :=
      (hgeo n).trans_lt ((div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))).trans_lt hx₀)
    rw [Function.iterate_succ_apply']
    exact (h _ hlt).1
  · rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq]
    refine squeeze_zero (fun _ => abs_nonneg _) hgeo ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul |x₀ - xs|
    simpa [div_eq_mul_inv, inv_pow] using this

/-- AKMM, p. 266: the central finite-difference derivative
`(f(x + h) − f(x − h))/(2h)` tends to `f′(x)` as `h → 0` ("in principle, a smaller `h` would
provide a better approximation"). -/
theorem central_difference_tendsto {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    Tendsto (fun h => (f (x + h) - f (x - h)) / (2 * h)) (𝓝[≠] 0) (𝓝 (deriv f x)) := by
  have h1 := hasDerivAt_iff_tendsto_slope_zero.1 hf.hasDerivAt
  have hg : HasDerivAt (fun t => f (x - t)) (deriv f x * (-1)) 0 := by
    have h2 : HasDerivAt f (deriv f x) (x - id 0) := by simpa using hf.hasDerivAt
    exact h2.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_sub x)
  have h3 := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have h4 := (h1.sub h3).const_mul (1 / 2)
  have heq : (1 / 2 : ℝ) * (deriv f x - deriv f x * (-1)) = deriv f x := by ring
  rw [heq] at h4
  refine h4.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  have ht' : t ≠ 0 := ht
  simp only [smul_eq_mul, zero_add, sub_zero]
  field_simp
  ring

/-- AKMM, p. 266: the central difference is exact for quadratics: for
`f(x) = ax² + bx + c`, `(f(x + h) − f(x − h))/(2h) = 2ax + b = f′(x)` for every `h ≠ 0`. -/
theorem central_difference_quadratic (a b c x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ((a * (x + h) ^ 2 + b * (x + h) + c) - (a * (x - h) ^ 2 + b * (x - h) + c)) / (2 * h) =
      2 * a * x + b := by
  field_simp
  ring

/-- AKMM, (10.3) and step 2, p. 268: Newton's step for maximising `F`,
`x ↦ x − F′(x)/F″(x)`. -/
noncomputable def newtonOptStep (F : ℝ → ℝ) (x : ℝ) : ℝ := x - deriv F x / deriv (deriv F) x

/-- AKMM, §10.3.3, p. 269: "Newton's method for optimization is simply Newton–Raphson applied
to the first-order condition": the update for `max F` is the Newton–Raphson step for `F′`. -/
theorem newtonOpt_eq_newtonStep_deriv (F : ℝ → ℝ) : newtonOptStep F = newtonStep (deriv F) :=
  rfl

/-- AKMM, (10.3), p. 268: the quadratic model `q(x) = F(x₀) + F′(x₀)(x − x₀) + ½F″(x₀)(x − x₀)²`
satisfies `q(x) = q(x̂) + ½F″(x₀)(x − x̂)²` with `x̂ = x₀ − F′(x₀)/F″(x₀)`, so `x̂` is its
unique critical point ("taking the first-order condition … we obtain (10.3)"). -/
theorem eq_10_3 (F : ℝ → ℝ) {x₀ : ℝ} (hd : deriv (deriv F) x₀ ≠ 0) (x : ℝ) :
    F x₀ + deriv F x₀ * (x - x₀) + 1 / 2 * deriv (deriv F) x₀ * (x - x₀) ^ 2 =
      (F x₀ + deriv F x₀ * (newtonOptStep F x₀ - x₀) +
        1 / 2 * deriv (deriv F) x₀ * (newtonOptStep F x₀ - x₀) ^ 2) +
      1 / 2 * deriv (deriv F) x₀ * (x - newtonOptStep F x₀) ^ 2 := by
  unfold newtonOptStep
  field_simp
  ring

/-- AKMM, (10.3), p. 268: when `F″(x₀) < 0`, `x̂` maximises the quadratic model of `F`. -/
theorem eq_10_3_max (F : ℝ → ℝ) {x₀ : ℝ} (hd : deriv (deriv F) x₀ < 0) (x : ℝ) :
    F x₀ + deriv F x₀ * (x - x₀) + 1 / 2 * deriv (deriv F) x₀ * (x - x₀) ^ 2 ≤
      F x₀ + deriv F x₀ * (newtonOptStep F x₀ - x₀) +
        1 / 2 * deriv (deriv F) x₀ * (newtonOptStep F x₀ - x₀) ^ 2 := by
  rw [eq_10_3 F hd.ne x]
  have : 1 / 2 * deriv (deriv F) x₀ * (x - newtonOptStep F x₀) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- AKMM, p. 268: "If `F(x)` is indeed quadratic, `x̂` delivers the solution in one step": for
`F(x) = ax² + bx + c` with `a ≠ 0`, Newton's step from any `x₀` lands on `−b/(2a)`, where
`F′ = 0`. -/
theorem newtonOpt_quadratic_exact {a b c : ℝ} (ha : a ≠ 0) (x₀ : ℝ) :
    newtonOptStep (fun x => a * x ^ 2 + b * x + c) x₀ = -b / (2 * a) ∧
      deriv (fun x => a * x ^ 2 + b * x + c) (-b / (2 * a)) = 0 := by
  have hF : deriv (fun x => a * x ^ 2 + b * x + c) = fun x => 2 * a * x + b := by
    funext x
    have h1 : HasDerivAt (fun x => a * x ^ 2 + b * x + c) (a * (↑2 * x ^ (2 - 1)) + b * 1) x :=
      (((hasDerivAt_pow 2 x).const_mul a).add ((hasDerivAt_id x).const_mul b)).add_const c
    rw [h1.deriv]
    norm_num
    ring
  have hF2 : deriv (fun x => 2 * a * x + b) = fun _ => 2 * a := by
    funext x
    have := ((hasDerivAt_id x).const_mul (2 * a)).add_const b
    simp only [id, mul_one] at this
    exact this.deriv
  unfold newtonOptStep
  rw [hF, hF2]
  constructor
  · field_simp
    ring
  · field_simp
    ring

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Golden-section search

AKMM, §10.3.1, pp. 266–267, and §10.3.3, p. 269. A bracket `a < b < c` with `F(a) ≤ F(b)` and
`F(c) ≤ F(b)` contains an interior maximiser of a continuous `F` on `[a, c]`, a local maximum
(`golden_bracket_max`). The step puts `x` in the longer segment at relative distance
`ω* = (3 − √5)/2` from `b` and keeps `(a, x, b)` if `F(x) > F(b)`, else `(x, b, c)` (and the
mirror image when the right segment is longer) (`goldenStep`). Proved:

* `ω*` satisfies `ω*² − 3ω* + 1 = 0`, `ω* = (1 − ω*)²`, `0.38196 < ω* < 0.38197`, and
  `(1 − ω*)/ω*` is the golden ratio `(1 + √5)/2 ≈ 1.61803` (`golden_omega_sq`,
  `golden_omega_bounds`, `golden_ratio_eq`);
* starting from `(c − b)/(c − a) = ω*`, every step keeps the ratio `ω*` (self-similarity),
  keeps the bracket property, and multiplies the bracket length by `1 − ω*`
  (`goldenStep_spec`); after `n` steps the length is `(1 − ω*)ⁿ(c − a)` (`golden_length`,
  correcting the printed `(1 − ω*)ⁿ(c − b)`: `golden_printed_length_counterexample`), so the
  search ends after a pre-set number of steps (`golden_terminates`) and every bracket contains
  a local maximiser (`golden_iterate_max`);
* footnote 3: `ω*` is the only `ω ∈ (0, 1)` for which both outcomes of the step leave brackets
  of the same length (`golden_fn3_unique`);
* §10.3.3: each step removes the fraction `ω* ≈ 0.38` of the bracket, less than bisection's
  one half (`golden_removed_fraction`).
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- AKMM, p. 267: the constant `ω* = (3 − √5)/2`. -/
noncomputable def omegaStar : ℝ := (3 - √5) / 2

/-- `ω*` is a root of `ω² − 3ω + 1`. -/
theorem golden_omega_sq : omegaStar ^ 2 = 3 * omegaStar - 1 := by
  unfold omegaStar
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- `ω* = (1 − ω*)²`. -/
theorem golden_omega_eq_sq : omegaStar = (1 - omegaStar) ^ 2 := by
  have := golden_omega_sq
  nlinarith

/-- AKMM, p. 267: `ω* ≈ 0.38197`: `0.38196 < ω* < 0.38197`; in particular `0 < ω* < 1/2`. -/
theorem golden_omega_bounds : 0.38196 < omegaStar ∧ omegaStar < 0.38197 := by
  unfold omegaStar
  have h1 : (2.23606 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < (2.23608 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

theorem golden_omega_pos : 0 < omegaStar := by linarith [golden_omega_bounds.1]

theorem golden_omega_lt_half : omegaStar < 1 / 2 := by linarith [golden_omega_bounds.2]

/-- AKMM, p. 267: "the ratio `(1 − ω*)/ω* ≈ 1.61803` is often called the golden ratio": it is
`(1 + √5)/2`. -/
theorem golden_ratio_eq : (1 - omegaStar) / omegaStar = Real.goldenRatio := by
  have hpos := golden_omega_pos
  rw [div_eq_iff hpos.ne']
  unfold omegaStar Real.goldenRatio
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- A bracket `(a, b, c)` for golden-section search. -/
structure GoldenBracket where
  /-- the left end `a` -/
  a : ℝ
  /-- the middle point `b` -/
  b : ℝ
  /-- the right end `c` -/
  c : ℝ

/-- AKMM, p. 266, step 1: the bracket property `a < b < c`, `F(a) ≤ F(b)`, `F(c) ≤ F(b)`
(weak inequalities, so that it is kept by step 2 when `F(x) = F(b)`). -/
def GoldenBracket.IsBracket (F : ℝ → ℝ) (p : GoldenBracket) : Prop :=
  p.a < p.b ∧ p.b < p.c ∧ F p.a ≤ F p.b ∧ F p.c ≤ F p.b

/-- AKMM, p. 267: the bracket is in golden proportion: its shorter segment is the fraction
`ω*` of its length. -/
def GoldenBracket.IsGolden (p : GoldenBracket) : Prop :=
  p.c - p.b = omegaStar * (p.c - p.a) ∨ p.b - p.a = omegaStar * (p.c - p.a)

/-- AKMM, p. 267, step 2: one golden-section step. If `[a, b]` is the longer segment, take
`x = b − ω*(b − a)` and keep `(a, x, b)` if `F(x) > F(b)`, otherwise `(x, b, c)`; if `[b, c]` is
the longer one, take `x = b + ω*(c − b)` and keep `(b, x, c)` if `F(x) > F(b)`, else
`(a, b, x)`. -/
noncomputable def goldenStep (F : ℝ → ℝ) (p : GoldenBracket) : GoldenBracket :=
  if p.c - p.b < p.b - p.a then
    if F p.b < F (p.b - omegaStar * (p.b - p.a)) then ⟨p.a, p.b - omegaStar * (p.b - p.a), p.b⟩
    else ⟨p.b - omegaStar * (p.b - p.a), p.b, p.c⟩
  else
    if F p.b < F (p.b + omegaStar * (p.c - p.b)) then ⟨p.b, p.b + omegaStar * (p.c - p.b), p.c⟩
    else ⟨p.a, p.b, p.b + omegaStar * (p.c - p.b)⟩

/-- AKMM, p. 267: one step from a golden bracket gives a golden bracket inside the old one, of
length `(1 − ω*)(c − a)`, still with the bracket property ("every time, we can remove the `ω*`
fraction of the segment"). -/
theorem goldenStep_spec (F : ℝ → ℝ) {p : GoldenBracket} (hb : p.IsBracket F)
    (hg : p.IsGolden) :
    (goldenStep F p).IsBracket F ∧ (goldenStep F p).IsGolden ∧
      (goldenStep F p).c - (goldenStep F p).a = (1 - omegaStar) * (p.c - p.a) ∧
      p.a ≤ (goldenStep F p).a ∧ (goldenStep F p).c ≤ p.c := by
  obtain ⟨hab, hbc, hFa, hFc⟩ := hb
  have hω := golden_omega_sq
  have hω0 := golden_omega_pos
  have hω1 := golden_omega_lt_half
  unfold GoldenBracket.IsGolden at hg ⊢
  unfold goldenStep
  generalize omegaStar = ω at *
  obtain ⟨L, hL⟩ : ∃ L, L = p.c - p.a := ⟨_, rfl⟩
  rw [← hL] at hg ⊢
  have hLpos : 0 < L := by linarith
  have hc' : p.c = p.a + L := by linarith
  rcases hg with hg | hg
  · -- the right segment is the short one: `[a, b]` is longer
    have hb' : p.b = p.a + (1 - ω) * L := by linarith
    have hlong : p.c - p.b < p.b - p.a := by rw [hb', hc']; nlinarith
    simp only [hlong, ↓reduceIte]
    split_ifs with hx
    · refine ⟨⟨?_, ?_, ?_, hx.le⟩, Or.inl ?_, ?_, le_rfl, ?_⟩ <;> dsimp only
      · rw [hb']; nlinarith
      · rw [hb']; nlinarith
      · linarith
      · ring
      · rw [hb']; ring
      · linarith
    · rw [not_lt] at hx
      refine ⟨⟨?_, ?_, hx, hFc⟩, Or.inr ?_, ?_, ?_, le_rfl⟩ <;> dsimp only
      · rw [hb']; nlinarith
      · linarith
      · rw [hb', hc']; linear_combination (ω * L) * hω
      · rw [hb', hc']; linear_combination (-L) * hω
      · rw [hb']; nlinarith
  · -- the left segment is the short one: `[b, c]` is longer (or equal)
    have hb' : p.b = p.a + ω * L := by linarith
    have hlong : ¬ p.c - p.b < p.b - p.a := by
      rw [not_lt, hb', hc']; nlinarith
    simp only [hlong, ↓reduceIte]
    split_ifs with hx
    · refine ⟨⟨?_, ?_, ?_, ?_⟩, Or.inr ?_, ?_, ?_, le_rfl⟩ <;> dsimp only
      · rw [hb', hc']; nlinarith
      · rw [hb', hc']; nlinarith
      · exact hx.le
      · linarith
      · ring
      · rw [hb', hc']; ring
      · linarith
    · rw [not_lt] at hx
      refine ⟨⟨?_, ?_, hFa, hx⟩, Or.inl ?_, ?_, le_rfl, ?_⟩ <;> dsimp only
      · linarith
      · rw [hb', hc']; nlinarith
      · rw [hb', hc']; linear_combination (ω * L) * hω
      · rw [hb', hc']; linear_combination (-L) * hω
      · rw [hb', hc']; nlinarith

/-- AKMM, p. 267, step 3: after `n` golden-section steps from a golden bracket, the bracket
is golden, has the bracket property, lies inside the original one and has length
`(1 − ω*)ⁿ(c − a)`. -/
theorem golden_length (F : ℝ → ℝ) {p : GoldenBracket} (hb : p.IsBracket F) (hg : p.IsGolden)
    (n : ℕ) :
    ((goldenStep F)^[n] p).IsBracket F ∧ ((goldenStep F)^[n] p).IsGolden ∧
      ((goldenStep F)^[n] p).c - ((goldenStep F)^[n] p).a = (1 - omegaStar) ^ n * (p.c - p.a) ∧
      p.a ≤ ((goldenStep F)^[n] p).a ∧ ((goldenStep F)^[n] p).c ≤ p.c := by
  induction n with
  | zero => exact ⟨hb, hg, by simp, le_rfl, le_rfl⟩
  | succ n ih =>
    obtain ⟨hb', hg', hl, ha, hc⟩ := ih
    obtain ⟨hb'', hg'', hl', ha', hc'⟩ := goldenStep_spec F hb' hg'
    rw [Function.iterate_succ_apply']
    refine ⟨hb'', hg'', by rw [hl', hl]; ring, ha.trans ha', hc'.trans hc⟩

/-- AKMM, p. 267: printed "the length of the remaining bracket … is `(1 − ω*)ⁿ(c − b)`". From
`(c − b)/(c − a) = ω*` the length after `n` steps is `(1 − ω*)ⁿ(c − a)` (`golden_length`), which
is strictly larger than the printed value for every `n`. -/
theorem golden_printed_length_counterexample {a b c : ℝ} (hac : a < c)
    (hg : c - b = omegaStar * (c - a)) (n : ℕ) :
    (1 - omegaStar) ^ n * (c - b) < (1 - omegaStar) ^ n * (c - a) := by
  have h1 := golden_omega_lt_half
  have hpos : 0 < (1 - omegaStar) ^ n := pow_pos (by linarith) n
  rw [hg]
  apply mul_lt_mul_of_pos_left _ hpos
  have h2 : 0 < c - a := by linarith
  nlinarith

/-- AKMM, p. 267: golden-section search "ends in a pre-set number of iterations": for every
tolerance `ε > 0` there is `n` with `(1 − ω*)ⁿ(c − a) < ε`. -/
theorem golden_terminates {a c ε : ℝ} (hac : a < c) (hε : 0 < ε) :
    ∃ n : ℕ, (1 - omegaStar) ^ n * (c - a) < ε := by
  have h0 := golden_omega_pos
  have h1 := golden_omega_lt_half
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : 0 < c - a))
    (by linarith : 1 - omegaStar < 1)
  refine ⟨n, ?_⟩
  rwa [lt_div_iff₀ (by linarith)] at hn

/-- AKMM, p. 266, step 1: "These properties mean that a (local) maximum point exists between `a`
and `c`": for continuous `F` on `[a, c]` with the bracket property, some `x ∈ (a, c)`
maximises `F` on `[a, c]`, and it is a local maximum of `F`. -/
theorem golden_bracket_max {F : ℝ → ℝ} {p : GoldenBracket} (hb : p.IsBracket F)
    (hF : ContinuousOn F (Set.Icc p.a p.c)) :
    ∃ x ∈ Set.Ioo p.a p.c, IsMaxOn F (Set.Icc p.a p.c) x ∧ IsLocalMax F x := by
  obtain ⟨hab, hbc, hFa, hFc⟩ := hb
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨p.a, Set.left_mem_Icc.2 (hab.trans hbc).le⟩ hF
  have key : ∃ y ∈ Set.Ioo p.a p.c, IsMaxOn F (Set.Icc p.a p.c) y := by
    by_cases hxi : x ∈ Set.Ioo p.a p.c
    · exact ⟨x, hxi, hmax⟩
    · have hxe : x = p.a ∨ x = p.c := by
        rcases hx with ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le h2 with h' | h'
        · exact Or.inr h'
        · exact absurd ⟨h, h'⟩ hxi
      have hFx : F x ≤ F p.b := by rcases hxe with rfl | rfl <;> assumption
      exact ⟨p.b, ⟨hab, hbc⟩, fun y hy => (hmax hy).trans hFx⟩
  obtain ⟨y, hy, hymax⟩ := key
  exact ⟨y, hy, hymax, hymax.isLocalMax (Icc_mem_nhds hy.1 hy.2)⟩

/-- AKMM, pp. 266–267: every bracket produced by golden-section search for a continuous `F`
contains a local maximiser of `F`, within `(1 − ω*)ⁿ(c − a)` of every point of the bracket. -/
theorem golden_iterate_max {F : ℝ → ℝ} {p : GoldenBracket} (hb : p.IsBracket F)
    (hg : p.IsGolden) (hF : ContinuousOn F (Set.Icc p.a p.c)) (n : ℕ) :
    ∃ x ∈ Set.Ioo ((goldenStep F)^[n] p).a ((goldenStep F)^[n] p).c, IsLocalMax F x ∧
      ∀ y ∈ Set.Icc ((goldenStep F)^[n] p).a ((goldenStep F)^[n] p).c,
        |y - x| ≤ (1 - omegaStar) ^ n * (p.c - p.a) := by
  obtain ⟨hbn, -, hl, ha, hc⟩ := golden_length F hb hg n
  obtain ⟨x, hx, -, hloc⟩ :=
    golden_bracket_max hbn (hF.mono (Set.Icc_subset_Icc ha hc))
  refine ⟨x, hx, hloc, fun y hy => ?_⟩
  rw [← hl, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- AKMM, p. 267, the two possible new brackets: if `c − b = ω(c − a)` and
`x = b − ω(b − a)`, the bracket `(a, x, b)` has length `(1 − ω)(c − a)` and the bracket
`(x, b, c)` has length `ω(2 − ω)(c − a)`. -/
theorem golden_two_lengths {a b c ω : ℝ} (hg : c - b = ω * (c - a)) :
    b - a = (1 - ω) * (c - a) ∧ c - (b - ω * (b - a)) = ω * (2 - ω) * (c - a) := by
  have hb : b = c - ω * (c - a) := by linarith
  subst hb
  constructor <;> ring

/-- AKMM, p. 267, fn. 3: "this result is guaranteed only with this particular value of `ω*`":
for `ω ∈ (0, 1)` the two possible new brackets have the same length (`golden_two_lengths`)
exactly when `ω = ω*`. -/
theorem golden_fn3_unique {ω : ℝ} (h0 : 0 < ω) (h1 : ω < 1) :
    1 - ω = ω * (2 - ω) ↔ ω = omegaStar := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 2 < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  constructor
  · intro h
    have hq : (ω - (3 - √5) / 2) * (ω - (3 + √5) / 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 hq with hq | hq
    · unfold omegaStar; linarith
    · nlinarith
  · rintro rfl
    have := golden_omega_sq
    nlinarith

/-- AKMM, §10.3.3, p. 269: golden-section search "gets rid of about one-third of the interval in
each iteration, as opposed to half": each step removes the fraction `ω* ≈ 0.382` of the
bracket, which lies between one third and one half. -/
theorem golden_removed_fraction :
    1 - (1 - omegaStar) = omegaStar ∧ 1 / 3 < omegaStar ∧ omegaStar < 1 / 2 := by
  refine ⟨by ring, ?_, golden_omega_lt_half⟩
  linarith [golden_omega_bounds.1]

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 1: root finding and optimisation in the labour–leisure choice

AKMM, §10.3.3, Example 1, pp. 269–270. The consumer maximises `ln c − (ω/γ)ℓ^γ` subject to
`c = ℓ^α + x`, i.e. (10.4) `F(ℓ) = ln(ℓ^α + x) − (ω/γ)ℓ^γ`, with first-order condition (10.5)
`αℓ^{α−1}/(ℓ^α + x) − ωℓ^{γ−1} = 0`.

* (10.5) is `F′(ℓ) = 0` (`eq_10_5`), and for `α ∈ (0, 1)`, `x > 0`, `ω > 0`, `γ ≥ 1` its left
  side is strictly decreasing on `(0, ∞)` (`ex1_foc_strictAnti`), so it has at most one root,
  and a root is the unique maximiser of (10.4) on `(0, ∞)` (`ex1_root_isMax`): maximising
  (10.4) and solving (10.5) are the same problem, as §10.3.3 says.
* For the book's parameters `α = 1/3`, `x = 0.5`, `ω = 1`, `γ = 2`, (10.5) has exactly one root, and
  it lies in `(1/8, 1)` ⊂ `[0, 1]` (`ex1_unique_root`), which is what the bisection, Newton and
  golden-section codes compute.
-/

namespace AKMM.ComputationalTools

open Set Real

/-- AKMM, (10.4), p. 270: the objective `ln(ℓ^α + x) − (ω/γ)ℓ^γ`. -/
noncomputable def ex1Obj (α x ω γ ℓ : ℝ) : ℝ := Real.log (ℓ ^ α + x) - ω / γ * ℓ ^ γ

/-- AKMM, (10.5), p. 270: the left side of the first-order condition. -/
noncomputable def ex1Foc (α x ω γ ℓ : ℝ) : ℝ := α * ℓ ^ (α - 1) / (ℓ ^ α + x) - ω * ℓ ^ (γ - 1)

/-- AKMM, (10.5), p. 270: the first-order condition is the derivative of (10.4) (for `ℓ > 0`,
`x ≥ 0`, `γ ≠ 0`). -/
theorem eq_10_5 {α x ω γ ℓ : ℝ} (hx : 0 ≤ x) (hγ : γ ≠ 0) (hℓ : 0 < ℓ) :
    HasDerivAt (ex1Obj α x ω γ) (ex1Foc α x ω γ ℓ) ℓ := by
  have h1 : HasDerivAt (fun l => l ^ α) (α * ℓ ^ (α - 1)) ℓ :=
    Real.hasDerivAt_rpow_const (Or.inl hℓ.ne')
  have h2 : HasDerivAt (fun l => l ^ γ) (γ * ℓ ^ (γ - 1)) ℓ :=
    Real.hasDerivAt_rpow_const (Or.inl hℓ.ne')
  have hpos : 0 < ℓ ^ α + x := by have := Real.rpow_pos_of_pos hℓ α; linarith
  have h := ((h1.add_const x).log hpos.ne').sub (h2.const_mul (ω / γ))
  refine h.congr_deriv ?_
  unfold ex1Foc
  field_simp

/-- AKMM, Example 1: for `α ∈ (0, 1)`, `x > 0`, `ω > 0`, `γ ≥ 1` the left side of (10.5) is
strictly decreasing on `(0, ∞)`. -/
theorem ex1_foc_strictAnti {α x ω γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hω : 0 < ω)
    (hγ : 1 ≤ γ) : StrictAntiOn (ex1Foc α x ω γ) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have hn : b ^ (α - 1) < a ^ (α - 1) := Real.rpow_lt_rpow_of_neg ha' hab (by linarith)
  have hn0 : 0 < b ^ (α - 1) := Real.rpow_pos_of_pos hb' _
  have hd : a ^ α < b ^ α := Real.rpow_lt_rpow ha'.le hab hα0
  have hd0 : 0 < a ^ α := Real.rpow_pos_of_pos ha' _
  have hg : a ^ (γ - 1) ≤ b ^ (γ - 1) := Real.rpow_le_rpow ha'.le hab.le (by linarith)
  have hfirst : α * b ^ (α - 1) / (b ^ α + x) < α * a ^ (α - 1) / (a ^ α + x) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    have e1 : α * b ^ (α - 1) * (a ^ α + x) < α * a ^ (α - 1) * (a ^ α + x) := by
      apply mul_lt_mul_of_pos_right _ (by linarith)
      exact mul_lt_mul_of_pos_left hn hα0
    have e2 : α * a ^ (α - 1) * (a ^ α + x) ≤ α * a ^ (α - 1) * (b ^ α + x) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      exact (mul_pos hα0 (hn0.trans hn)).le
    linarith
  unfold ex1Foc
  have := mul_le_mul_of_nonneg_left hg hω.le
  linarith

/-- AKMM, §10.3.3 and Example 1: with the hypotheses of `ex1_foc_strictAnti`, a root `ℓ*` of
(10.5) is the unique maximiser of (10.4) on `(0, ∞)`. -/
theorem ex1_root_isMax {α x ω γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hω : 0 < ω)
    (hγ : 1 ≤ γ) {ls : ℝ} (hls : 0 < ls) (hroot : ex1Foc α x ω γ ls = 0) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hne : ℓ ≠ ls) : ex1Obj α x ω γ ℓ < ex1Obj α x ω γ ls := by
  have hγ0 : γ ≠ 0 := by linarith
  have hanti := ex1_foc_strictAnti hα0 hα1 hx hω hγ
  have hderiv : ∀ y, 0 < y → deriv (ex1Obj α x ω γ) y = ex1Foc α x ω γ y :=
    fun y hy => (eq_10_5 hx.le hγ0 hy).deriv
  have hcont : ContinuousOn (ex1Obj α x ω γ) (Ioi 0) := fun y hy =>
    (eq_10_5 hx.le hγ0 hy).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- increasing on `(0, ℓ*]`
    have hmono : StrictMonoOn (ex1Obj α x ω γ) (Ioc 0 ls) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 ls) (hcont.mono Ioc_subset_Ioi_self)
        fun y hy => ?_
      rw [interior_Ioc] at hy
      rw [hderiv y hy.1, ← hroot]
      exact hanti hy.1 hls hy.2
    exact hmono ⟨hℓ, hlt.le⟩ ⟨hls, le_rfl⟩ hlt
  · -- decreasing on `[ℓ*, ∞)`
    have hmono : StrictAntiOn (ex1Obj α x ω γ) (Ici ls) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici ls)
        (hcont.mono fun y hy => lt_of_lt_of_le hls hy) fun y hy => ?_
      rw [interior_Ici] at hy
      have hy0 : 0 < y := hls.trans hy
      rw [hderiv y hy0, ← hroot]
      exact hanti hls hy0 hy
    exact hmono (le_refl ls) hgt.le hgt

/-- `(1/8)^{1/3} = 1/2`. -/
theorem ex1_cbrt_eighth : (1 / 8 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by
  rw [show (1 / 8 : ℝ) = (1 / 2) ^ (3 : ℕ) by norm_num,
    show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (by norm_num)
    (by norm_num)]

/-- AKMM, Example 1, p. 270: with `α = 1/3`, `x = 0.5`, `ω = 1`, `γ = 2`, the first-order
condition (10.5) has exactly one root in `(0, ∞)`; it lies in `(1/8, 1)`, and it maximises
(10.4). -/
theorem ex1_unique_root :
    ∃! ls, 0 < ls ∧ ex1Foc (1 / 3) (1 / 2) 1 2 ls = 0 ∧ ls ∈ Ioo (1 / 8) 1 ∧
      ∀ ℓ, 0 < ℓ → ℓ ≠ ls → ex1Obj (1 / 3) (1 / 2) 1 2 ℓ < ex1Obj (1 / 3) (1 / 2) 1 2 ls := by
  have hanti := ex1_foc_strictAnti (α := 1 / 3) (x := 1 / 2) (ω := 1) (γ := 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : 0 < ex1Foc (1 / 3) (1 / 2) 1 2 (1 / 8) := by
    unfold ex1Foc
    rw [show (1 / 3 : ℝ) - 1 = (1 / 3) * (-2) by norm_num, Real.rpow_mul (by norm_num),
      ex1_cbrt_eighth, show (2 : ℝ) - 1 = (1 : ℕ) by norm_num, Real.rpow_natCast]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have h1 : ex1Foc (1 / 3) (1 / 2) 1 2 1 < 0 := by
    unfold ex1Foc
    simp only [Real.one_rpow]
    norm_num
  have hcont : ContinuousOn (ex1Foc (1 / 3) (1 / 2) 1 2) (Icc (1 / 8) 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
    have c1 : ContinuousAt (fun l : ℝ => l ^ ((1 : ℝ) / 3 - 1)) y :=
      Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')
    have c2 : ContinuousAt (fun l : ℝ => l ^ ((1 : ℝ) / 3)) y :=
      Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')
    have c3 : ContinuousAt (fun l : ℝ => l ^ ((2 : ℝ) - 1)) y :=
      Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')
    have hden : y ^ ((1 : ℝ) / 3) + 1 / 2 ≠ 0 := by
      have := Real.rpow_pos_of_pos hy0 ((1 : ℝ) / 3); linarith
    exact ((((c1.const_mul _).div (c2.add continuousAt_const) hden)).sub
      (c3.const_mul _)).continuousWithinAt
  obtain ⟨ls, hls, hroot⟩ := intermediate_value_Icc' (by norm_num : (1 / 8 : ℝ) ≤ 1) hcont
    ⟨h1.le, h8.le⟩
  have hls0 : 0 < ls := lt_of_lt_of_le (by norm_num) hls.1
  have hlsI : ls ∈ Ioo (1 / 8 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hls.1 ?_, lt_of_le_of_ne hls.2 ?_⟩
    · rintro rfl; rw [hroot] at h8; exact lt_irrefl _ h8
    · rintro rfl; rw [hroot] at h1; exact lt_irrefl _ h1
  refine ⟨ls, ⟨hls0, hroot, hlsI, fun ℓ hℓ hne => ex1_root_isMax (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hls0 hroot hℓ hne⟩, ?_⟩
  rintro l ⟨hl0, hlroot, -, -⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti hl0 hls0 h; rw [hlroot, hroot] at this; exact lt_irrefl _ this
  · have := hanti hls0 hl0 h; rw [hlroot, hroot] at this; exact lt_irrefl _ this

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discretising an AR(1) process: the Tauchen method

AKMM, §10.4–10.4.1, pp. 270–271. The AR(1) `z_{t+1} = ρz_t + ε_{t+1}` with `0 < ρ < 1` has
unconditional variance `σ_z² = σ_ε²/(1 − ρ²)` (`ar1_uncond_var`, from Miao's
`nq_ar1_variance_fixed`). Tauchen's matrix on an equally spaced grid with spacing `ω`, for any
distribution function `F` of the normalised shock (`F` nondecreasing with values in `[0, 1]`),
assigns to each interior point the probability of `[z̄ʲ − ω/2, z̄ʲ + ω/2]` and to the end
points the tails (`tauchenProb`); every row is a probability vector (`tauchen_stochastic`).

The interior entries are printed as `F((z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε) − F((z̄ʲ − ρz̄ⁱ + ω/2)/σ_ε)`, the
negative of the probability of the interval: for strictly increasing `F` they are negative and
the rows sum to `1 + 2(F(u₁) − F(u_{N−1})) ≠ 1` (`tauchen_printed_neg`,
`tauchen_printed_row_sum`), with the Cauchy distribution function as a concrete strictly
increasing `F` (`tauchenCauchyCdf_strictMono`). Miao's Gaussian version, with the cells as
measurable sets, is `Miao.NumericalMethods.nq_tauchen_stochastic`.
-/

namespace AKMM.ComputationalTools

open Finset

/-- AKMM, p. 270: "this specification implies the unconditional variance of `z_t` is
`σ_z² = σ_ε²/(1 − ρ²)`": it is the only stationary variance `s = ρ²s + σ_ε²`. -/
theorem ar1_uncond_var {ρ σε s : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    s = ρ ^ 2 * s + σε ^ 2 ↔ s = σε ^ 2 / (1 - ρ ^ 2) :=
  Miao.NumericalMethods.nq_ar1_variance_fixed (by rw [abs_of_pos hρ0]; exact hρ1)

/-- AKMM, p. 270, step 1: the equally spaced grid `z̄ʲ = z̄¹ + (j − 1)ω`, indexed here from
`j = 0`. -/
def tauchenGrid (z₁ ω : ℝ) (j : ℕ) : ℝ := z₁ + j * ω

/-- AKMM, p. 270: with `z̄¹ = −mσ_z` and `ω = 2mσ_z/(N − 1)`, the last point is `z̄ᴺ = mσ_z`. -/
theorem tauchenGrid_last {N : ℕ} (hN : 2 ≤ N) (m σz : ℝ) :
    tauchenGrid (-(m * σz)) (2 * m * σz / (N - 1 : ℕ)) (N - 1) = m * σz := by
  have h : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ N - 1 := by omega
    positivity
  unfold tauchenGrid
  field_simp
  ring

/-- The normalised upper end `(z̄ʲ − ρz̄ⁱ + ω/2)/σ_ε` of the cell of `z̄ʲ`. -/
noncomputable def tauchenUpper (ρ σε z₁ ω zi : ℝ) (j : ℕ) : ℝ :=
  (tauchenGrid z₁ ω j - ρ * zi + ω / 2) / σε

/-- The normalised lower end `(z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε` of the cell of `z̄ʲ`. -/
noncomputable def tauchenLower (ρ σε z₁ ω zi : ℝ) (j : ℕ) : ℝ :=
  (tauchenGrid z₁ ω j - ρ * zi - ω / 2) / σε

/-- Adjacent cells share their boundary: the lower end of `j + 1` is the upper end of `j`. -/
theorem tauchen_lower_succ (ρ σε z₁ ω zi : ℝ) (j : ℕ) :
    tauchenLower ρ σε z₁ ω zi (j + 1) = tauchenUpper ρ σε z₁ ω zi j := by
  unfold tauchenLower tauchenUpper tauchenGrid
  push_cast
  ring

/-- AKMM, p. 271, step 2 (corrected): Tauchen's transition probability from the state with value
`zi` to the grid point `j ∈ {0, …, N − 1}`: `F(u₀)` for the first point, `1 − F(l_{N−1})` for the
last, and `F(u_j) − F(l_j)` in between. -/
noncomputable def tauchenProb (F : ℝ → ℝ) (ρ σε z₁ ω : ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then F (tauchenUpper ρ σε z₁ ω zi 0)
  else if j = N - 1 then 1 - F (tauchenLower ρ σε z₁ ω zi j)
  else F (tauchenUpper ρ σε z₁ ω zi j) - F (tauchenLower ρ σε z₁ ω zi j)

/-- AKMM, p. 271: each row of Tauchen's matrix is a probability vector, for any distribution
function `F` (nondecreasing, values in `[0, 1]`), spacing `ω ≥ 0`, `σ_ε > 0` and `N ≥ 2`. -/
theorem tauchen_stochastic {F : ℝ → ℝ} (hF : Monotone F) (hF0 : ∀ x, 0 ≤ F x)
    (hF1 : ∀ x, F x ≤ 1) {ρ σε z₁ ω : ℝ} (hσ : 0 < σε) (hω : 0 ≤ ω) {N : ℕ} (hN : 2 ≤ N)
    (zi : ℝ) :
    (∀ j, 0 ≤ tauchenProb F ρ σε z₁ ω N zi j) ∧
      ∑ j ∈ range N, tauchenProb F ρ σε z₁ ω N zi j = 1 := by
  constructor
  · intro j
    unfold tauchenProb
    split_ifs
    · exact hF0 _
    · linarith [hF1 (tauchenLower ρ σε z₁ ω zi j)]
    · refine sub_nonneg.2 (hF ?_)
      unfold tauchenUpper tauchenLower
      gcongr
      linarith
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
    set u : ℕ → ℝ := fun j => F (tauchenUpper ρ σε z₁ ω zi j)
    rw [sum_range_succ, sum_range_succ']
    have hlast : tauchenProb F ρ σε z₁ ω (M + 2) zi (M + 1) = 1 - u M := by
      unfold tauchenProb
      rw [show M + 2 - 1 = M + 1 by omega]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, tauchen_lower_succ, u]
    have hfirst : tauchenProb F ρ σε z₁ ω (M + 2) zi 0 = u 0 := by
      simp [tauchenProb, u]
    have hmid : ∀ k ∈ range M, tauchenProb F ρ σε z₁ ω (M + 2) zi (k + 1) = u (k + 1) - u k := by
      intro k hk
      have hk' := mem_range.1 hk
      unfold tauchenProb
      simp only [Nat.add_one_ne_zero, show k + 1 ≠ M + 2 - 1 by omega, ↓reduceIte,
        tauchen_lower_succ, u]
    rw [sum_congr rfl hmid, sum_range_sub, hlast, hfirst]
    ring

/-- AKMM, p. 271, the interior entries as printed: `F((z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε) − F((z̄ʲ − ρz̄ⁱ +
ω/2)/σ_ε)`. -/
noncomputable def tauchenPrinted (F : ℝ → ℝ) (ρ σε z₁ ω : ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then F (tauchenUpper ρ σε z₁ ω zi 0)
  else if j = N - 1 then 1 - F (tauchenLower ρ σε z₁ ω zi j)
  else F (tauchenLower ρ σε z₁ ω zi j) - F (tauchenUpper ρ σε z₁ ω zi j)

/-- AKMM, p. 271: the printed interior entries are negative for a strictly increasing `F` and a
grid with positive spacing. -/
theorem tauchen_printed_neg {F : ℝ → ℝ} (hF : StrictMono F) {ρ σε z₁ ω : ℝ} (hσ : 0 < σε)
    (hω : 0 < ω) {N j : ℕ} (hj0 : j ≠ 0) (hjN : j ≠ N - 1) (zi : ℝ) :
    tauchenPrinted F ρ σε z₁ ω N zi j < 0 := by
  unfold tauchenPrinted
  simp only [hj0, hjN, ↓reduceIte, sub_neg]
  apply hF
  unfold tauchenUpper tauchenLower
  gcongr
  linarith

/-- AKMM, p. 271: with the printed interior entries the rows of an `N = M + 2`-point grid sum
to `1 + 2(F(u₀) − F(u_M))`, which differs from `1` whenever `M ≥ 1` and `F` is strictly
increasing. -/
theorem tauchen_printed_row_sum {F : ℝ → ℝ} (hF : StrictMono F) {ρ σε z₁ ω : ℝ} (hσ : 0 < σε)
    (hω : 0 < ω) {M : ℕ} (hM : 1 ≤ M) (zi : ℝ) :
    ∑ j ∈ range (M + 2), tauchenPrinted F ρ σε z₁ ω (M + 2) zi j =
        1 + 2 * (F (tauchenUpper ρ σε z₁ ω zi 0) - F (tauchenUpper ρ σε z₁ ω zi M)) ∧
      ∑ j ∈ range (M + 2), tauchenPrinted F ρ σε z₁ ω (M + 2) zi j < 1 := by
  set u : ℕ → ℝ := fun j => F (tauchenUpper ρ σε z₁ ω zi j)
  have hsum : ∑ j ∈ range (M + 2), tauchenPrinted F ρ σε z₁ ω (M + 2) zi j =
      1 + 2 * (u 0 - u M) := by
    rw [sum_range_succ, sum_range_succ']
    have hlast : tauchenPrinted F ρ σε z₁ ω (M + 2) zi (M + 1) = 1 - u M := by
      unfold tauchenPrinted
      rw [show M + 2 - 1 = M + 1 by omega]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, tauchen_lower_succ, u]
    have hfirst : tauchenPrinted F ρ σε z₁ ω (M + 2) zi 0 = u 0 := by
      simp [tauchenPrinted, u]
    have hmid : ∀ k ∈ range M,
        tauchenPrinted F ρ σε z₁ ω (M + 2) zi (k + 1) = -(u (k + 1) - u k) := by
      intro k hk
      have hk' := mem_range.1 hk
      unfold tauchenPrinted
      simp only [Nat.add_one_ne_zero, show k + 1 ≠ M + 2 - 1 by omega, ↓reduceIte,
        tauchen_lower_succ, u]
      ring
    rw [sum_congr rfl hmid, sum_neg_distrib, sum_range_sub, hlast, hfirst]
    ring
  refine ⟨hsum, ?_⟩
  rw [hsum]
  have : u 0 < u M := by
    apply hF
    unfold tauchenUpper tauchenGrid
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    gcongr
    nlinarith
  linarith

/-- The Cauchy distribution function `1/2 + arctan(x)/π`, a concrete strictly increasing
distribution function with values in `[0, 1]` for the counterexamples. -/
noncomputable def tauchenCauchyCdf (x : ℝ) : ℝ := 1 / 2 + Real.arctan x / Real.pi

/-- The Cauchy distribution function is strictly increasing with values in `[0, 1]`. -/
theorem tauchenCauchyCdf_strictMono :
    StrictMono tauchenCauchyCdf ∧ ∀ x, 0 ≤ tauchenCauchyCdf x ∧ tauchenCauchyCdf x ≤ 1 := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · unfold tauchenCauchyCdf
    have := Real.arctan_strictMono h
    have hpi := Real.pi_pos
    gcongr
  · unfold tauchenCauchyCdf
    have h1 := Real.neg_pi_div_two_lt_arctan x
    have h2 := Real.arctan_lt_pi_div_two x
    have hpi := Real.pi_pos
    constructor
    · rw [← sub_nonneg]
      have : Real.arctan x / Real.pi > -(1 / 2) := by
        rw [gt_iff_lt, lt_div_iff₀ hpi]; linarith
      linarith
    · have : Real.arctan x / Real.pi < 1 / 2 := by
        rw [div_lt_iff₀ hpi]; linarith
      linarith

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Rouwenhorst method

AKMM, §10.4.2, p. 271. The Rouwenhorst matrix `Π_N` is defined by the recursion of p. 271,
indexed here by `n = N − 1`: `Π_1 = [1]` (which gives the book's `Π_2`, `rouwenhorst_two`), and
`Π_{n+1}` is `p[Π 0; 0′ 0] + (1 − p)[0 Π; 0 0′] + (1 − p)[0′ 0; Π 0] + p[0 0′; 0 Π]` with all but
the top and bottom rows divided by two (`rouwenhorst`).

The book prints the weights of the last two matrices as `p` and `1 − p`; with those weights the
method does not work (`rouwenhorst_printed_counterexample`: for `N = 3`, `p = 3/4` the binomial
law is not invariant and the conditional mean at the top state is `0`, not `ρz`). With the
weights `1 − p`, `p` (Rouwenhorst 1995; Kopecky–Suen 2010) everything holds:

* row `i` of `Π_{n+1}` has generating polynomial `(p + (1 − p)X)^{n−i}((1 − p) + pX)^i`
  (`rouwenhorst_eq_coeff`), so `Π_N` is a Markov matrix (`rouwenhorst_nonneg`,
  `rouwenhorst_row_sum`);
* the conditional mean of the index is `(n − i)(1 − p) + ip` (`rouwenhorst_cond_mean_index`),
  hence on the grid `z̄_j = ψ(j − n/2)`, `E[z′ | z̄ᵢ] = (2p − 1)z̄ᵢ = ρz̄ᵢ` for `p = (1 + ρ)/2`
  (`rouwenhorst_cond_mean`);
* the invariant distribution is binomial, `λ_j = C(n, j)/2ⁿ` (`rouwenhorst_invariant`), with mean
  `0` and variance `ψ²n/4 = m²σ_z²/(N − 1)` on the grid from `−mσ_z` to `mσ_z`
  (`rouwenhorst_stationary_mean`, `rouwenhorst_stationary_var`);
* so `p = (1 + ρ)/2` and `m = √(N − 1)` match the AR(1) mean `0`, variance `σ_z²` and first-order
  autocorrelation `ρ` (`rouwenhorst_matches_ar1`).

The convergence of the invariant law to a normal distribution as `N → ∞` (de Moivre–Laplace) is
cited by the book and not formalised.
-/

namespace AKMM.ComputationalTools

open Polynomial Finset

/-- AKMM, p. 271: the Rouwenhorst matrix `Π_{n+1}` (`N = n + 1` states), as a function of the
row `i` and column `j` (zero outside `0 ≤ i, j ≤ n`), by the recursion with the weights
`p, 1 − p, 1 − p, p` on the four padded copies of `Π_n`, and the rows `0 < i < n` halved. -/
noncomputable def rouwenhorst (p : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun i j => if i = 0 ∧ j = 0 then 1 else 0
  | n + 1 => fun i j =>
      if n + 1 < i then 0 else
      (p * rouwenhorst p n i j
        + (1 - p) * (if j = 0 then 0 else rouwenhorst p n i (j - 1))
        + (1 - p) * (if i = 0 then 0 else rouwenhorst p n (i - 1) j)
        + p * (if i = 0 ∨ j = 0 then 0 else rouwenhorst p n (i - 1) (j - 1)))
      / (if i = 0 ∨ i = n + 1 then 1 else 2)

/-- AKMM, p. 271, step 1: the recursion starts from `Π_2 = [p, 1 − p; 1 − p, p]`. -/
theorem rouwenhorst_two (p : ℝ) :
    rouwenhorst p 1 0 0 = p ∧ rouwenhorst p 1 0 1 = 1 - p ∧ rouwenhorst p 1 1 0 = 1 - p ∧
      rouwenhorst p 1 1 1 = p := by
  simp [rouwenhorst]

/-- Rows below the last are zero. -/
theorem rouwenhorst_row_zero (p : ℝ) {n i : ℕ} (hi : n < i) (j : ℕ) :
    rouwenhorst p n i j = 0 := by
  cases n with
  | zero =>
    have : i ≠ 0 := by omega
    simp [rouwenhorst, this]
  | succ n =>
    simp only [rouwenhorst, hi, ↓reduceIte]

/-- AKMM, p. 271: the entries of `Π_N` are nonnegative for `p ∈ [0, 1]`. -/
theorem rouwenhorst_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n i j : ℕ) :
    0 ≤ rouwenhorst p n i j := by
  induction n generalizing i j with
  | zero =>
    simp only [rouwenhorst]
    split_ifs <;> norm_num
  | succ n ih =>
    simp only [rouwenhorst]
    have hq : 0 ≤ 1 - p := by linarith
    split_ifs <;> first
      | exact le_rfl
      | positivity
      | (apply div_nonneg _ (by norm_num)
         have := ih i j; have := ih i (j - 1); have := ih (i - 1) j; have := ih (i - 1) (j - 1)
         positivity)

/-- The generating polynomial `p + (1 − p)X` of a state that stays low. -/
noncomputable def rwLow (p : ℝ) : ℝ[X] := C (1 - p) * X + C p

/-- The generating polynomial `(1 − p) + pX` of a state that stays high. -/
noncomputable def rwHigh (p : ℝ) : ℝ[X] := C p * X + C (1 - p)

/-- The generating polynomial of row `i` of `Π_{n+1}`: `(p + (1 − p)X)^{n−i}((1 − p) + pX)^i`. -/
noncomputable def rwRow (p : ℝ) (n i : ℕ) : ℝ[X] := rwLow p ^ (n - i) * rwHigh p ^ i

/-- Multiplying by `C v * X + C u` mixes neighbouring coefficients. -/
theorem rw_coeff_linear_mul (u v : ℝ) (Q : ℝ[X]) (j : ℕ) :
    ((C v * X + C u) * Q).coeff j = u * Q.coeff j + v * (if j = 0 then 0 else Q.coeff (j - 1)) := by
  rw [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_C_mul]
  cases j with
  | zero => simp
  | succ j => simp [coeff_X_mul]; ring

/-- AKMM, p. 271 (Kopecky–Suen): the entries of `Π_{n+1}` are the coefficients of the row
polynomials, `π_{ij} = [Xʲ](p + (1 − p)X)^{n−i}((1 − p) + pX)^i`. -/
theorem rouwenhorst_eq_coeff (p : ℝ) (n : ℕ) {i : ℕ} (hi : i ≤ n) (j : ℕ) :
    rouwenhorst p n i j = (rwRow p n i).coeff j := by
  induction n generalizing i j with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp only [rouwenhorst, rwRow, Nat.sub_self, pow_zero, mul_one, true_and, coeff_one]
  | succ n ih =>
    simp only [rouwenhorst, show ¬ n + 1 < i by omega, ↓reduceIte]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · -- the top row
      have hrow : rwRow p (n + 1) 0 = rwLow p * rwRow p n 0 := by
        simp only [rwRow, Nat.sub_zero, pow_zero, mul_one, pow_succ]; ring
      rw [hrow, rwLow, rw_coeff_linear_mul]
      simp only [true_or, ↓reduceIte, mul_zero, add_zero, div_one]
      rw [ih (by omega) j]
      split_ifs
      · ring
      · rw [ih (by omega) (j - 1)]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or,
        ↓reduceIte]
      have hhigh : rwRow p (n + 1) (k + 1) = rwHigh p * rwRow p n k := by
        simp only [rwRow, pow_succ, show n + 1 - (k + 1) = n - k by omega]; ring
      rcases Nat.lt_or_ge k n with hk | hk
      · -- an interior row: both copies contribute, and the row is halved
        have hlow : rwRow p (n + 1) (k + 1) = rwLow p * rwRow p n (k + 1) := by
          simp only [rwRow, show n + 1 - (k + 1) = n - (k + 1) + 1 by omega, pow_succ]; ring
        have hne : k + 1 ≠ n + 1 := by omega
        simp only [hne, ↓reduceIte]
        have e1 := congrArg (fun Q => Q.coeff j) hlow
        have e2 := congrArg (fun Q => Q.coeff j) hhigh
        simp only [rwLow, rwHigh, rw_coeff_linear_mul] at e1 e2
        rw [ih (by omega) j, ih (by omega) j]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp only [↓reduceIte, mul_zero, add_zero] at e1 e2 ⊢
          rw [div_eq_iff (by norm_num)]
          linarith
        · have hj0 : j ≠ 0 := by omega
          simp only [hj0, ↓reduceIte] at e1 e2 ⊢
          rw [ih (by omega) (j - 1), ih (by omega) (j - 1), div_eq_iff (by norm_num)]
          linarith
      · -- the bottom row: only the shifted copy contributes
        obtain rfl : k = n := by omega
        simp only [↓reduceIte, div_one]
        rw [rouwenhorst_row_zero p (by omega : k < k + 1),
          rouwenhorst_row_zero p (by omega : k < k + 1), hhigh, rwHigh, rw_coeff_linear_mul,
          ih le_rfl j]
        split_ifs
        · ring
        · rw [ih le_rfl (j - 1)]; ring

/-- The row polynomials have degree at most `n`. -/
theorem rwRow_natDegree_le (p : ℝ) {n i : ℕ} (hi : i ≤ n) : (rwRow p n i).natDegree ≤ n := by
  have hl : (rwLow p).natDegree ≤ 1 := by unfold rwLow; exact natDegree_linear_le
  have hh : (rwHigh p).natDegree ≤ 1 := by unfold rwHigh; exact natDegree_linear_le
  unfold rwRow
  calc (rwLow p ^ (n - i) * rwHigh p ^ i).natDegree
      ≤ (rwLow p ^ (n - i)).natDegree + (rwHigh p ^ i).natDegree := natDegree_mul_le
    _ ≤ (n - i) * 1 + i * 1 := by
        gcongr
        · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hl)
        · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hh)
    _ = n := by omega

/-- A sum of coefficients times powers is an evaluation. -/
theorem rw_sum_coeff_pow {Q : ℝ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) (x : ℝ) :
    ∑ j ∈ range (n + 1), Q.coeff j * x ^ j = Q.eval x :=
  (eval_eq_sum_range' (by omega) x).symm

/-- A sum of coefficients times indices is the derivative at `1`. -/
theorem rw_sum_coeff_mul_index {Q : ℝ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) :
    ∑ j ∈ range (n + 1), Q.coeff j * j = (derivative Q).eval 1 := by
  rw [derivative_eval, sum_over_range' Q (fun k => by simp) (n + 1) (by omega)]
  simp

/-- AKMM, p. 271: "divide all but the top and the bottom rows by two so that the elements in each
row are equal to one": every row of `Π_{n+1}` sums to one. -/
theorem rouwenhorst_row_sum (p : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), rouwenhorst p n i j = 1 := by
  have h := rw_sum_coeff_pow (rwRow_natDegree_le p hi) 1
  simp only [one_pow, mul_one] at h
  rw [sum_congr rfl fun j _ => rouwenhorst_eq_coeff p n hi j, h]
  simp [rwRow, rwLow, rwHigh]

/-- AKMM, p. 271: the conditional mean of the next index from row `i` is
`(n − i)(1 − p) + ip` (each of the `n − i` low coins turns high with probability `1 − p`, each of
the `i` high coins stays high with probability `p`). -/
theorem rouwenhorst_cond_mean_index (p : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), rouwenhorst p n i j * j = ((n - i : ℕ) : ℝ) * (1 - p) + i * p := by
  rw [sum_congr rfl fun j _ => by rw [rouwenhorst_eq_coeff p n hi j],
    rw_sum_coeff_mul_index (rwRow_natDegree_le p hi)]
  simp [rwRow, rwLow, rwHigh, derivative_mul, derivative_pow]

/-- The polynomial `(X + 1)ⁿ` is the binomial combination of the row polynomials. -/
theorem rw_binomial_rows (p : ℝ) (n : ℕ) :
    (X + 1 : ℝ[X]) ^ n = ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ[X]) * rwRow p n i := by
  have hsum : rwHigh p + rwLow p = X + 1 := by
    simp only [rwHigh, rwLow]
    rw [show C p * X + C (1 - p) + (C (1 - p) * X + C p) =
        C (p + (1 - p)) * X + C ((1 - p) + p) by simp only [C_add]; ring]
    simp
  rw [← hsum, add_pow]
  refine sum_congr rfl fun i _ => ?_
  unfold rwRow
  ring

/-- AKMM, p. 271: the invariant distribution of `Π_{n+1}` is the binomial law
`λ_j = C(n, j)/2ⁿ`, for every `p`. -/
theorem rouwenhorst_invariant (p : ℝ) (n j : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rouwenhorst p n i j =
      (n.choose j : ℝ) / 2 ^ n := by
  have h := congrArg (fun Q => Q.coeff j) (rw_binomial_rows p n)
  simp only [coeff_X_add_one_pow, finsetSum_coeff, coeff_natCast_mul] at h
  rw [h, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [rouwenhorst_eq_coeff p n (by simpa [Nat.lt_succ_iff] using hi) j]
  ring

/-- The binomial weights sum to `2ⁿ`, with first moment `n2ⁿ/2` and second moment
`n(n + 1)2ⁿ/4`. -/
theorem rw_binomial_moments (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) = 2 ^ n ∧
      ∑ j ∈ range (n + 1), (j : ℝ) * n.choose j = n * 2 ^ n / 2 ∧
      ∑ j ∈ range (n + 1), (j : ℝ) ^ 2 * n.choose j = n * (n + 1) * 2 ^ n / 4 := by
  have h0 : ∑ j ∈ range (n + 1), (n.choose j : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have h1 : ∀ m : ℕ, ∑ j ∈ range (m + 1), (j : ℝ) * m.choose j = m * 2 ^ m / 2 := by
    intro m
    have := Nat.sum_range_mul_choose m
    have hc : ∑ j ∈ range (m + 1), (j : ℝ) * m.choose j = ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by
      rw [← this]; push_cast; rfl
    rw [hc]
    cases m with
    | zero => simp
    | succ m => push_cast; rw [pow_succ]; ring
  refine ⟨h0, h1 n, ?_⟩
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ']
    have hterm : ∀ k ∈ range (m + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * ((m + 1).choose (k + 1) : ℝ) =
        (m + 1) * ((k : ℝ) * m.choose k + m.choose k) := by
      intro k _
      have := Nat.add_one_mul_choose_eq m k
      have hc : ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) =
          ((m + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hc ⊢
      nlinarith [hc]
    rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib, h1 m,
      (by exact_mod_cast Nat.sum_range_choose m : ∑ j ∈ range (m + 1), (m.choose j : ℝ) = 2 ^ m)]
    push_cast
    rw [pow_succ]
    ring

/-- AKMM, p. 271: the equally spaced grid `z̄_j = ψ(j − n/2)`, `j = 0, …, n`; with
`ψ = 2mσ_z/n` it runs from `−mσ_z` to `mσ_z`. -/
noncomputable def rwGrid (ψ : ℝ) (n j : ℕ) : ℝ := ψ * (j - n / 2)

/-- The grid runs from `−mσ_z` to `mσ_z` when `ψ = 2mσ_z/n`. -/
theorem rwGrid_ends {n : ℕ} (hn : 0 < n) (m σz : ℝ) :
    rwGrid (2 * m * σz / n) n 0 = -(m * σz) ∧ rwGrid (2 * m * σz / n) n n = m * σz := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold rwGrid
  constructor <;> field_simp <;> ring

/-- AKMM, p. 271: on the grid, the conditional mean is `E[z′ | z̄ᵢ] = (2p − 1)z̄ᵢ`. -/
theorem rouwenhorst_cond_mean (p ψ : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j = (2 * p - 1) * rwGrid ψ n i := by
  have h1 := rouwenhorst_row_sum p hi
  have h2 := rouwenhorst_cond_mean_index p hi
  have hsub : ((n - i : ℕ) : ℝ) = n - i := by push_cast [hi]; ring
  unfold rwGrid
  have : ∀ j ∈ range (n + 1), rouwenhorst p n i j * (ψ * (j - n / 2)) =
      ψ * (rouwenhorst p n i j * j) - ψ * n / 2 * rouwenhorst p n i j := fun j _ => by ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum, h1, h2, hsub]
  ring

/-- AKMM, p. 271: the stationary mean of the grid under the binomial law is `0`. -/
theorem rouwenhorst_stationary_mean (ψ : ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j = 0 := by
  obtain ⟨h0, h1, -⟩ := rw_binomial_moments n
  unfold rwGrid
  have : ∀ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * (ψ * (j - n / 2)) =
      ψ / 2 ^ n * ((j : ℝ) * n.choose j) - ψ * n / 2 / 2 ^ n * (n.choose j : ℝ) :=
    fun j _ => by ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum, h0, h1]
  field_simp
  ring

/-- AKMM, p. 271: the stationary variance of the grid under the binomial law is `ψ²n/4`. -/
theorem rouwenhorst_stationary_var (ψ : ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j ^ 2 = ψ ^ 2 * n / 4 := by
  obtain ⟨h0, h1, h2⟩ := rw_binomial_moments n
  unfold rwGrid
  have : ∀ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * (ψ * (j - n / 2)) ^ 2 =
      ψ ^ 2 / 2 ^ n * ((j : ℝ) ^ 2 * n.choose j) - ψ ^ 2 * n / 2 ^ n * ((j : ℝ) * n.choose j) +
        ψ ^ 2 * n ^ 2 / 4 / 2 ^ n * (n.choose j : ℝ) := fun j _ => by ring
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    h0, h1, h2]
  field_simp
  ring

/-- AKMM, p. 271: the stationary first-order autocovariance is `(2p − 1)` times the variance. -/
theorem rouwenhorst_stationary_autocov (p ψ : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rwGrid ψ n i *
        ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j =
      (2 * p - 1) * (ψ ^ 2 * n / 4) := by
  rw [← rouwenhorst_stationary_var ψ n, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [rouwenhorst_cond_mean p ψ (by simpa [Nat.lt_succ_iff] using hi)]
  ring

/-- AKMM, p. 271: "We can set `p` and `m` by `p = (1 + ρ)/2` and `m = √(N − 1)`. Then … the
unconditional mean and unconditional variance of the Markov chain are the same as those of the
original AR(1) process": with `N = n + 1 ≥ 2` states on the grid from `−mσ_z` to `mσ_z`, the
chain is stochastic, its invariant law is binomial with mean `0` and variance `σ_z²`, the
conditional mean is `ρz̄ᵢ`, and the first-order autocovariance is `ρσ_z²`. -/
theorem rouwenhorst_matches_ar1 {ρ σz : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (hn : 0 < n) :
    let p := (1 + ρ) / 2
    let ψ := 2 * √n * σz / n
    (∀ i j, 0 ≤ rouwenhorst p n i j) ∧
    (∀ i ≤ n, ∑ j ∈ range (n + 1), rouwenhorst p n i j = 1) ∧
    rwGrid ψ n 0 = -(√n * σz) ∧ rwGrid ψ n n = √n * σz ∧
    (∀ j, ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rouwenhorst p n i j =
      (n.choose j : ℝ) / 2 ^ n) ∧
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j = 0 ∧
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j ^ 2 = σz ^ 2 ∧
    (∀ i ≤ n, ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j = ρ * rwGrid ψ n i) ∧
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rwGrid ψ n i *
        ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j = ρ * σz ^ 2 := by
  intro p ψ
  have hp0 : 0 ≤ p := by simp only [p]; linarith
  have hp1 : p ≤ 1 := by simp only [p]; linarith
  have hρ : 2 * p - 1 = ρ := by simp only [p]; ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hvar : ψ ^ 2 * n / 4 = σz ^ 2 := by
    simp only [ψ]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hn'.le]
    field_simp
    ring
  obtain ⟨he0, he1⟩ := rwGrid_ends hn (√n) σz
  refine ⟨rouwenhorst_nonneg hp0 hp1 n, fun i hi => rouwenhorst_row_sum p hi, he0, he1,
    rouwenhorst_invariant p n, rouwenhorst_stationary_mean ψ n, ?_, fun i hi => ?_, ?_⟩
  · rw [rouwenhorst_stationary_var, hvar]
  · rw [rouwenhorst_cond_mean p ψ hi, hρ]
  · rw [rouwenhorst_stationary_autocov, hvar, hρ]

/-- AKMM, p. 271, the recursion as printed: from the book's `Π_2` (`n = 1`), the weights of
`[0′ 0; Π 0]` and `[0 0′; 0 Π]` are `p` and `1 − p` (instead of `1 − p` and `p`). -/
noncomputable def rouwenhorstPrinted (p : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun i j => if i = 0 ∧ j = 0 then 1 else 0
  | 1 => fun i j => if 1 < i ∨ 1 < j then 0 else if i = j then p else 1 - p
  | n + 2 => fun i j =>
      if n + 2 < i then 0 else
      (p * rouwenhorstPrinted p (n + 1) i j
        + (1 - p) * (if j = 0 then 0 else rouwenhorstPrinted p (n + 1) i (j - 1))
        + p * (if i = 0 then 0 else rouwenhorstPrinted p (n + 1) (i - 1) j)
        + (1 - p) * (if i = 0 ∨ j = 0 then 0 else rouwenhorstPrinted p (n + 1) (i - 1) (j - 1)))
      / (if i = 0 ∨ i = n + 2 then 1 else 2)

/-- AKMM, p. 271: the printed recursion fails. For `N = 3` and `p = 3/4` (`ρ = 1/2`) its matrix
has rows `(9/16, 6/16, 1/16)`, `(3/8, 1/2, 1/8)`, `(3/16, 10/16, 3/16)`: the binomial law
`(1/4, 1/2, 1/4)` is not invariant (column `0` gives `3/8`), and from the top state `z̄ = 1` of
the grid `z̄_j = j − 1` the conditional mean is `0`, not `ρz̄ = 1/2`. The corrected recursion
has `(1/4, 1/2, 1/4)` invariant and conditional mean `ρz̄` (`rouwenhorst_invariant`,
`rouwenhorst_cond_mean`). -/
theorem rouwenhorst_printed_counterexample :
    ∑ i ∈ range 3, ((2 : ℕ).choose i : ℝ) / 2 ^ 2 * rouwenhorstPrinted (3 / 4) 2 i 0 = 3 / 8 ∧
      ((2 : ℕ).choose 0 : ℝ) / 2 ^ 2 = 1 / 4 ∧
      ∑ j ∈ range 3, rouwenhorstPrinted (3 / 4) 2 2 j * rwGrid 1 2 j = 0 ∧
      (2 * (3 / 4 : ℝ) - 1) * rwGrid 1 2 2 = 1 / 2 := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp [sum_range_succ, rouwenhorstPrinted, Nat.choose]
    norm_num
  · simp [sum_range_succ, rouwenhorstPrinted, rwGrid]
    norm_num
  · simp [rwGrid]
    norm_num

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Value-function iteration on a grid

AKMM, §10.5, pp. 272–275. The algorithm of p. 272 fixes a grid, represents `V_i` by its values
on the grid, and computes `V_{i+1} = TV_i` with (10.7), `TV(k) = max_{k′} {F(k, k′) + βV(k′)}`,
the choice `k′` restricted to the grid (grid search, Examples 3–4). Here the state space is any
finite set `X` (a grid, or a grid times the exogenous states of §10.5.2), the feasible choices
from `x` a nonempty finite set, and the continuation value an expectation under a transition
`P(x, a, ·)` (`GridDP`, `GridDP.T`): the deterministic case has `P(x, a, ·)` a point mass, the
stochastic cake and growth problems a Markov chain on the shocks.

Proved: `T` is a contraction of modulus `β` in the sup norm (`GridDP.contraction`, through
Sargent–Stachurski's `IsContractionOn`), so (10.6) has a unique solution on the grid, and
`V_i = Tⁱ V₀` converges to it from every `V₀` with `‖V_i − V‖ ≤ βⁱ‖V₀ − V‖` (`GridDP.vfi`);
the stopping rule `max_j |V_{i+1}(a_j) − V_i(a_j)| < ε` bounds the error by `βε/(1 − β)`
(`GridDP.stopping_rule`). Concrete instances: the grid cake-eating problem of §10.5.1
(`cakeGrid`) and the two-state stochastic cake of §10.5.2 (`stochCakeGrid`).
-/

namespace AKMM.ComputationalTools

open Finset

/-- AKMM, §10.5, (10.6)–(10.7) on a finite state space: states `X`, choices `A`, feasible sets
`Γ(x)`, return `F(x, a)`, transition `P(x, a, x′)` to the next state, discount `β ∈ [0, 1)`. -/
structure GridDP (X A : Type*) [Fintype X] where
  /-- the feasible choices from each state -/
  feasible : X → Finset A
  feasible_nonempty : ∀ x, (feasible x).Nonempty
  /-- the current return `F(x, a)` -/
  ret : X → A → ℝ
  /-- the probability of moving to `x′` after choosing `a` in `x` -/
  trans : X → A → X → ℝ
  trans_nonneg : ∀ x a x', 0 ≤ trans x a x'
  trans_sum : ∀ x a, ∑ x', trans x a x' = 1
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace GridDP

variable {X A : Type*} [Fintype X] (M : GridDP X A)

/-- The expected continuation value `E[V(x′) | x, a]`. -/
def cont (V : X → ℝ) (x : X) (a : A) : ℝ := ∑ x', M.trans x a x' * V x'

/-- AKMM, (10.7), p. 272: the Bellman operator `TV(x) = max_{a ∈ Γ(x)} {F(x, a) + βE[V(x′)]}`. -/
def T (V : X → ℝ) (x : X) : ℝ :=
  (M.feasible x).sup' (M.feasible_nonempty x) fun a => M.ret x a + M.β * M.cont V x a

/-- The continuation value moves by at most the sup-distance of the value functions. -/
theorem cont_sub_le (V U : X → ℝ) (x : X) (a : A) : |M.cont V x a - M.cont U x a| ≤ ‖V - U‖ := by
  unfold cont
  rw [← sum_sub_distrib]
  calc |∑ x', (M.trans x a x' * V x' - M.trans x a x' * U x')|
      ≤ ∑ x', |M.trans x a x' * V x' - M.trans x a x' * U x'| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', M.trans x a x' * ‖V - U‖ := by
        refine sum_le_sum fun x' _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (M.trans_nonneg x a x')]
        refine mul_le_mul_of_nonneg_left ?_ (M.trans_nonneg x a x')
        have := norm_le_pi_norm (V - U) x'
        rwa [Real.norm_eq_abs] at this
    _ = ‖V - U‖ := by rw [← sum_mul, M.trans_sum, one_mul]

/-- The maximum over the same finite set moves by at most the largest change. -/
theorem sup'_sub_le {s : Finset A} (hs : s.Nonempty) (f g : A → ℝ) {c : ℝ}
    (h : ∀ a ∈ s, |f a - g a| ≤ c) : |s.sup' hs f - s.sup' hs g| ≤ c := by
  rw [abs_le]
  constructor
  · have : s.sup' hs g ≤ s.sup' hs f + c := by
      refine sup'_le hs _ fun a ha => ?_
      have h1 := (abs_le.1 (h a ha)).2
      have h2 := le_sup' f ha
      have h3 := (abs_le.1 (h a ha)).1
      linarith
    linarith
  · have : s.sup' hs f ≤ s.sup' hs g + c := by
      refine sup'_le hs _ fun a ha => ?_
      have h1 := (abs_le.1 (h a ha)).2
      have h2 := le_sup' g ha
      linarith
    linarith

/-- AKMM, p. 272: `T` is a contraction of modulus `β` in the sup norm (the contraction mapping
theorem of Chapter 4 applies). -/
theorem contraction : SargentStachurski.JobSearch.IsContractionOn M.T Set.univ M.β where
  mapsTo := fun _ _ => Set.mem_univ _
  nonneg := M.β_nonneg
  lt_one := M.β_lt_one
  norm_sub_le := fun V _ U _ => by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold T
    refine sup'_sub_le _ _ _ fun a _ => ?_
    have := M.cont_sub_le V U x a
    calc |M.ret x a + M.β * M.cont V x a - (M.ret x a + M.β * M.cont U x a)|
        = M.β * |M.cont V x a - M.cont U x a| := by
          rw [← abs_of_nonneg M.β_nonneg, ← abs_mul, abs_of_nonneg M.β_nonneg]; ring_nf
      _ ≤ M.β * ‖V - U‖ := mul_le_mul_of_nonneg_left this M.β_nonneg

/-- AKMM, p. 272: "The contraction mapping theorem guarantees `V_i(k)` approaches the true value
function `V(k)` for (10.6) as `i → ∞`, regardless of the starting value function `V₀(k)`": the
Bellman equation `V = TV` has a unique solution, and `‖TⁱV₀ − V‖ ≤ βⁱ‖V₀ − V‖`. -/
theorem vfi : ∃ V : X → ℝ, M.T V = V ∧ (∀ W, M.T W = W → W = V) ∧
    ∀ V₀ : X → ℝ, ∀ i : ℕ, ‖M.T^[i] V₀ - V‖ ≤ M.β ^ i * ‖V₀ - V‖ := by
  obtain ⟨V, -, hV, huniq, hrate⟩ :=
    M.contraction.banach_pi isClosed_univ Set.univ_nonempty
  exact ⟨V, hV, fun W hW => huniq W (Set.mem_univ _) hW,
    fun V₀ i => hrate V₀ (Set.mem_univ _) i⟩

/-- AKMM, p. 273, step 4: "stop when `max_j |V_{i+1}(a_j) − V_i(a_j)| < ε`": then `V_{i+1}` is
within `βε/(1 − β)` of the solution `V` of the Bellman equation. -/
theorem stopping_rule {V W : X → ℝ} (hV : M.T V = V) {ε : ℝ} (h : ‖M.T W - W‖ ≤ ε) :
    ‖M.T W - V‖ ≤ M.β * ε / (1 - M.β) := by
  have hc := M.contraction.norm_sub_le W (Set.mem_univ _) V (Set.mem_univ _)
  rw [hV] at hc
  have htri : ‖W - V‖ ≤ ‖M.T W - W‖ + ‖M.T W - V‖ := by
    calc ‖W - V‖ = ‖-(M.T W - W) + (M.T W - V)‖ := by congr 1; abel
      _ ≤ ‖-(M.T W - W)‖ + ‖M.T W - V‖ := norm_add_le _ _
      _ = ‖M.T W - W‖ + ‖M.T W - V‖ := by rw [norm_neg]
  have h1 := M.β_lt_one
  rw [le_div_iff₀ (by linarith)]
  nlinarith [M.β_nonneg, norm_nonneg (M.T W - V)]

end GridDP

/-- AKMM, §10.5.1, p. 273, steps 1 and 3 (grid search): the cake-eating problem on the grid
`a_j = j·a₀/n`, `j = 0, …, n`, with the choice `a′` restricted to grid points `a_k ≤ a_j` and
return `√(a_j − a_k)`; the next state is `a_k` for sure. -/
noncomputable def cakeGrid (n : ℕ) (a₀ β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GridDP (Fin (n + 1)) (Fin (n + 1)) where
  feasible j := univ.filter fun k => k ≤ j
  feasible_nonempty j := ⟨0, by simp⟩
  ret j k := √(j * a₀ / n - k * a₀ / n)
  trans _ k k' := if k' = k then 1 else 0
  trans_nonneg _ _ _ := by split_ifs <;> norm_num
  trans_sum _ k := by simp
  β := β
  β_nonneg := hβ0
  β_lt_one := hβ1

/-- AKMM, Example 3, p. 274 (grid search, `β = 0.98`, `a₀ = 10`): value-function iteration on the
cake grid converges to the unique solution of the grid Bellman equation. -/
theorem cakeGrid_vfi (n : ℕ) :
    ∃ V : Fin (n + 1) → ℝ, (cakeGrid n 10 0.98 (by norm_num) (by norm_num)).T V = V ∧
      ∀ V₀ : Fin (n + 1) → ℝ, ∀ i : ℕ,
        ‖(cakeGrid n 10 0.98 (by norm_num) (by norm_num)).T^[i] V₀ - V‖ ≤
          0.98 ^ i * ‖V₀ - V‖ := by
  obtain ⟨V, hV, -, hrate⟩ := (cakeGrid n 10 0.98 (by norm_num) (by norm_num)).vfi
  exact ⟨V, hV, hrate⟩

/-- AKMM, §10.5.2, pp. 273–274: the stochastic cake on the grid. States are pairs (grid point
`a_j`, shock `s ∈ {L, H}` with cake arrival `z_s ≥ 0`); the choice is a grid point `a_k` with
`a_k ≤ a_j + z_s`, the return `√(a_j − a_k + z_s)`, and the next state `(a_k, s′)` with
probability `π_{ss′}` (`Pz`). -/
noncomputable def stochCakeGrid (n : ℕ) (amax : ℝ) (z : Fin 2 → ℝ) (hz : ∀ s, 0 ≤ z s)
    (Pz : Fin 2 → Fin 2 → ℝ) (hP0 : ∀ s s', 0 ≤ Pz s s') (hP1 : ∀ s, ∑ s', Pz s s' = 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hamax : 0 ≤ amax) :
    GridDP (Fin (n + 1) × Fin 2) (Fin (n + 1)) where
  feasible x := univ.filter fun k => (k : ℝ) * amax / n ≤ x.1 * amax / n + z x.2
  feasible_nonempty x := ⟨0, by
    simp only [mem_filter, mem_univ, true_and, Fin.val_zero, Nat.cast_zero, zero_mul, zero_div]
    have : 0 ≤ (x.1 : ℝ) * amax / n := by positivity
    linarith [hz x.2]⟩
  ret x k := √(x.1 * amax / n - k * amax / n + z x.2)
  trans x k y := if y.1 = k then Pz x.2 y.2 else 0
  trans_nonneg x k y := by split_ifs <;> simp [hP0]
  trans_sum x k := by
    rw [Fintype.sum_prod_type]
    simp [hP1]
  β := β
  β_nonneg := hβ0
  β_lt_one := hβ1

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The deterministic cake-eating problem

AKMM, §10.5.1, pp. 273–274: an infinitely lived consumer with a cake `a₀`, utility
`∑ βᵗ√c_t`, and `a_{t+1} = a_t − c_t`; the Bellman equation is
`V(a) = max_{0 ≤ a′ ≤ a} √(a − a′) + βV(a′)`.

The book solves it numerically (Example 3). The problem has the closed form
`V(a) = √(a/(1 − β²))` with policy `a′ = β²a` (`c = (1 − β²)a`): it satisfies the Bellman
equation with the maximum attained at `β²a` (`cake_bellman`), the maximiser is unique
(`cake_policy_unique`), and it is the only solution bounded on `[0, ā]` (`cake_bellman_unique`,
the contraction argument of p. 272 on the continuous state space). The policy's consumption path
`c_t = (1 − β²)β^{2t}a₀` attains `V(a₀)` (`cake_path_value`). The value function is concave
(`cake_concave`), as the book notes ("the properties of a contraction mapping ensure the value
function is concave in this particular case").
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- The closed-form value `V(a) = √(a/(1 − β²))` of the cake-eating problem. -/
noncomputable def cakeV (β a : ℝ) : ℝ := √(a / (1 - β ^ 2))

/-- The right-hand side `√(a − a′) + βV(a′)` of the Bellman equation for a value `W`. -/
noncomputable def cakeRhs (β : ℝ) (W : ℝ → ℝ) (a a' : ℝ) : ℝ := √(a - a') + β * W a'

/-- The Cauchy–Schwarz bound behind the Bellman equation: for `k ≥ 0` with `k + β² = 1`,
`√k·u + βv ≤ √(u² + v²)` for all real `u`, `v`. -/
theorem cake_cauchy_schwarz {k β : ℝ} (hk : 0 ≤ k) (hkb : k + β ^ 2 = 1) (u v : ℝ) :
    √k * u + β * v ≤ √(u ^ 2 + v ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have hs : √k ^ 2 = k := Real.sq_sqrt hk
  nlinarith [sq_nonneg (β * u - √k * v)]

/-- AKMM, §10.5.1, p. 273: `V(a) = √(a/(1 − β²))` solves the Bellman equation
`V(a) = max_{0 ≤ a′ ≤ a} √(a − a′) + βV(a′)` for `0 ≤ β < 1`, `a ≥ 0`, and the maximum is
attained at `a′ = β²a`, i.e. consumption `c = (1 − β²)a`. -/
theorem cake_bellman {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a : ℝ} (ha : 0 ≤ a) :
    IsGreatest (cakeRhs β (cakeV β) a '' Set.Icc 0 a) (cakeV β a) ∧
      cakeRhs β (cakeV β) a (β ^ 2 * a) = cakeV β a := by
  set k := 1 - β ^ 2 with hk_def
  have hk : 0 < k := by nlinarith
  have hsk : 0 < √k := Real.sqrt_pos.2 hk
  have hV : ∀ x, 0 ≤ x → cakeV β x = √x / √k := fun x _ => by
    unfold cakeV; rw [Real.sqrt_div' _ hk.le]
  have hβ2 : β ^ 2 ≤ 1 := by nlinarith
  have hattain : cakeRhs β (cakeV β) a (β ^ 2 * a) = cakeV β a := by
    unfold cakeRhs
    rw [hV _ (by positivity), hV _ ha]
    have h1 : a - β ^ 2 * a = k * a := by rw [hk_def]; ring
    rw [h1, Real.sqrt_mul hk.le, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ0]
    field_simp
    have hs : √k ^ 2 = k := Real.sq_sqrt hk.le
    rw [hk_def] at hs ⊢
    rw [hs]
    ring
  refine ⟨⟨⟨β ^ 2 * a, ⟨by positivity, by nlinarith⟩, hattain⟩, ?_⟩, hattain⟩
  rintro _ ⟨a', ⟨ha'0, ha'a⟩, rfl⟩
  unfold cakeRhs
  rw [hV _ ha'0, hV _ ha, le_div_iff₀ hsk]
  have hcs := cake_cauchy_schwarz (β := β) hk.le (by rw [hk_def]; ring) (√(a - a')) (√a')
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt ha'0, show a - a' + a' = a by ring] at hcs
  calc (√(a - a') + β * (√a' / √k)) * √k = √k * √(a - a') + β * √a' := by field_simp
    _ ≤ √a := hcs

/-- AKMM, §10.5.1: the maximiser `a′ = β²a` is unique (for `a > 0`, `0 < β < 1`): any `a′` that
attains `V(a)` equals `β²a`. -/
theorem cake_policy_unique {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a a' : ℝ} (ha : 0 < a)
    (ha' : a' ∈ Set.Icc 0 a) (h : cakeRhs β (cakeV β) a a' = cakeV β a) : a' = β ^ 2 * a := by
  set k := 1 - β ^ 2 with hk_def
  have hk : 0 < k := by nlinarith
  have hsk : 0 < √k := Real.sqrt_pos.2 hk
  have hs : √k ^ 2 = k := Real.sq_sqrt hk.le
  unfold cakeRhs cakeV at h
  rw [Real.sqrt_div' _ hk.le, Real.sqrt_div' _ hk.le] at h
  -- `√k·u + βv = √(u² + v²)` with `u = √(a − a′)`, `v = √a′` forces `βu = √k v`
  set u := √(a - a') with hu
  set v := √a' with hv
  have hu2 : u ^ 2 = a - a' := Real.sq_sqrt (by linarith [ha'.2])
  have hv2 : v ^ 2 = a' := Real.sq_sqrt ha'.1
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have heq : √k * u + β * v = √a := by
    field_simp at h
    linarith
  have hsq : (√k * u + β * v) ^ 2 = a := by rw [heq, Real.sq_sqrt ha.le]
  have hzero : (β * u - √k * v) ^ 2 = 0 := by
    have : (β * u - √k * v) ^ 2 = (k + β ^ 2) * (u ^ 2 + v ^ 2) - (√k * u + β * v) ^ 2 := by
      nlinarith [hs]
    rw [this, hsq, hu2, hv2, hk_def]
    ring
  have hlin : β * u = √k * v := by nlinarith [sq_nonneg (β * u - √k * v)]
  have h2 : β ^ 2 * (a - a') = k * a' := by
    have := congrArg (· ^ 2) hlin
    simp only [mul_pow] at this
    rw [hu2, hv2, hs] at this
    exact this
  rw [hk_def] at h2
  nlinarith

/-- One step of the contraction argument: two solutions of the Bellman equation that differ by
at most `B` on `[0, ā]` differ by at most `βB` there. -/
theorem cake_bellman_step {β : ℝ} (hβ0 : 0 ≤ β) {abar B : ℝ} {U W : ℝ → ℝ}
    (hU : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β U a '' Set.Icc 0 a) (U a))
    (hW : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β W a '' Set.Icc 0 a) (W a))
    (hB : ∀ a ∈ Set.Icc 0 abar, |U a - W a| ≤ B) :
    ∀ a ∈ Set.Icc 0 abar, |U a - W a| ≤ β * B := by
  have key : ∀ {U W : ℝ → ℝ},
      (∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β U a '' Set.Icc 0 a) (U a)) →
      (∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β W a '' Set.Icc 0 a) (W a)) →
      (∀ a ∈ Set.Icc 0 abar, |U a - W a| ≤ B) → ∀ a ∈ Set.Icc 0 abar, U a ≤ W a + β * B := by
    intro U W hU hW hB a ha
    refine (hU a ha).2 ?_
    rintro _ ⟨a', ha', rfl⟩
    have ha'' : a' ∈ Set.Icc 0 abar := ⟨ha'.1, ha'.2.trans ha.2⟩
    have h1 : cakeRhs β W a a' ≤ W a := (hW a ha).1 ⟨a', ha', rfl⟩
    have h2 := (abs_le.1 (hB a' ha'')).2
    unfold cakeRhs at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h2 hβ0]
  intro a ha
  rw [abs_le]
  constructor
  · have := key hW hU (fun x hx => by rw [abs_sub_comm]; exact hB x hx) a ha
    linarith
  · have := key hU hW hB a ha
    linarith

/-- AKMM, p. 272 and §10.5.1: the Bellman equation has only one solution bounded on `[0, ā]`
(the contraction mapping theorem on the continuous state space): every bounded `W` with
`W(a) = sup_{0 ≤ a′ ≤ a} √(a − a′) + βW(a′)` on `[0, ā]` equals `√(a/(1 − β²))` there. -/
theorem cake_bellman_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {abar : ℝ} {W : ℝ → ℝ}
    (hW : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β W a '' Set.Icc 0 a) (W a))
    (hWb : ∃ C, ∀ a ∈ Set.Icc 0 abar, |W a| ≤ C) :
    ∀ a ∈ Set.Icc 0 abar, W a = cakeV β a := by
  have hV : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β (cakeV β) a '' Set.Icc 0 a) (cakeV β a) :=
    fun a ha => (cake_bellman hβ0 hβ1 ha.1).1.isLUB
  obtain ⟨C, hC⟩ := hWb
  set B := C + cakeV β abar
  have hVmono : ∀ a ∈ Set.Icc 0 abar, |cakeV β a| ≤ cakeV β abar := by
    intro a ha
    unfold cakeV
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hk : 0 < 1 - β ^ 2 := by nlinarith
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ha.2 hk.le)
  have hB : ∀ a ∈ Set.Icc 0 abar, |W a - cakeV β a| ≤ B := fun a ha =>
    (abs_sub _ _).trans (add_le_add (hC a ha) (hVmono a ha))
  have hiter : ∀ n : ℕ, ∀ a ∈ Set.Icc 0 abar, |W a - cakeV β a| ≤ β ^ n * B := by
    intro n
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      intro a ha
      have := cake_bellman_step hβ0 hW hV ih a ha
      calc |W a - cakeV β a| ≤ β * (β ^ n * B) := this
        _ = β ^ (n + 1) * B := by ring
  intro a ha
  have hlim : Tendsto (fun n : ℕ => β ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const B
  have h0 : |W a - cakeV β a| ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => hiter n a ha)
  have := abs_nonpos_iff.1 h0
  linarith

/-- AKMM, §10.5.1: the optimal path `a_t = β^{2t}a₀`, `c_t = (1 − β²)β^{2t}a₀` satisfies
`a_{t+1} = a_t − c_t` and attains lifetime utility `∑ βᵗ√c_t = √(a₀/(1 − β²)) = V(a₀)`. -/
theorem cake_path_value {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a₀ : ℝ) :
    (∀ t : ℕ, β ^ (2 * (t + 1)) * a₀ = β ^ (2 * t) * a₀ - (1 - β ^ 2) * β ^ (2 * t) * a₀) ∧
      HasSum (fun t : ℕ => β ^ t * √((1 - β ^ 2) * β ^ (2 * t) * a₀)) (cakeV β a₀) := by
  have hk : 0 < 1 - β ^ 2 := by nlinarith
  refine ⟨fun t => by ring, ?_⟩
  have hterm : ∀ t : ℕ, β ^ t * √((1 - β ^ 2) * β ^ (2 * t) * a₀) =
      √((1 - β ^ 2) * a₀) * (β ^ 2) ^ t := by
    intro t
    rw [show (1 - β ^ 2) * β ^ (2 * t) * a₀ = (β ^ t) ^ 2 * ((1 - β ^ 2) * a₀) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hβ0 t)]
    ring
  simp only [hterm]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg β) (by nlinarith : β ^ 2 < 1)).mul_left
    (√((1 - β ^ 2) * a₀))
  convert hg using 1
  unfold cakeV
  rw [Real.sqrt_mul hk.le, Real.sqrt_div' _ hk.le]
  have hs : √(1 - β ^ 2) ^ 2 = 1 - β ^ 2 := Real.sq_sqrt hk.le
  have hsk : 0 < √(1 - β ^ 2) := Real.sqrt_pos.2 hk
  field_simp
  rw [hs]

/-- AKMM, p. 273: the value function `V(a) = √(a/(1 − β²))` is concave on `[0, ∞)`. -/
theorem cake_concave {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ConcaveOn ℝ (Set.Ici 0) (cakeV β) := by
  have hk : 0 < 1 - β ^ 2 := by nlinarith
  have h := (Real.strictConcaveOn_sqrt.concaveOn).smul (c := (√(1 - β ^ 2))⁻¹)
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  refine h.congr fun a _ => ?_
  simp only [smul_eq_mul, cakeV]
  rw [Real.sqrt_div' _ hk.le, div_eq_inv_mul]

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The log-linearised stochastic growth model with labour

AKMM, §10.5.2, (10.12), p. 275, and §10.6, (10.13)–(10.17), (10.27), pp. 277–281.

* (10.12): the first-order condition of the static labour choice has at most one root in `H`
  (its left side is strictly decreasing), so `H(z, K, K′)` is well defined (`labour_foc_unique`).
* Log-linearisation (variables `x_t = log(X_t/X̄)`): output
  `e^zK^αH^{1−α} = K̄^αH̄^{1−α}e^{z+αk+(1−α)h}`
  (`rbc_output_exp`); the first-order expansions of (10.9), of the labour supply condition (10.14)
  and of the Euler equation (10.13) at the steady state (`loglin_resource`, `loglin_labour`,
  `loglin_euler`, the last using `β(1 − δ + αK̄^{α−1}H̄^{1−α}) = 1` and, as in fn. 7, certainty
  equivalence).
* (10.15): `h_t = θ(z_t + αk_t − c_t)` with `θ = (1 − H̄)/(H̄(1 − α) + α)` (`eq_10_15`).
* (10.16) (`eq_10_16`) and (10.17), corrected: the coefficient of `z_t` is
  `βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ` (`eq_10_17`); the printed coefficient lacks the factor `α`
  (`eq_10_17_printed_counterexample`), and so does the second entry of `E` in (10.27)
  (`eq_10_27`).
-/

namespace AKMM.ComputationalTools

open Real

/-! ### (10.12): the static labour choice -/

/-- AKMM, (10.12), p. 275: the derivative in `H` of
`(1 − φ)log(AH^{1−α} + R) + φlog(1 − H)`, with `A = e^zK^α` and `R = (1 − δ)K − K′`. -/
noncomputable def labourFoc (φ α A R H : ℝ) : ℝ :=
  (1 - φ) * ((1 - α) * A * H ^ (-α)) / (A * H ^ (1 - α) + R) - φ / (1 - H)

/-- AKMM, (10.12), p. 275: "the solution to this problem can be written as `H(z, K, K′)`": on the
set of `H ∈ (0, 1)` with positive consumption, the first-order condition is strictly decreasing
in `H`, so it has at most one root. -/
theorem labour_foc_unique {φ α A R : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) {H₁ H₂ : ℝ} (h1 : H₁ ∈ Set.Ioo 0 1) (h2 : H₂ ∈ Set.Ioo 0 1)
    (hc1 : 0 < A * H₁ ^ (1 - α) + R) (hlt : H₁ < H₂) :
    labourFoc φ α A R H₂ < labourFoc φ α A R H₁ := by
  have hc2 : A * H₁ ^ (1 - α) + R < A * H₂ ^ (1 - α) + R := by
    have := Real.rpow_lt_rpow h1.1.le hlt (by linarith : 0 < 1 - α)
    nlinarith
  have hp : H₂ ^ (-α) < H₁ ^ (-α) := Real.rpow_lt_rpow_of_neg h1.1 hlt (by linarith)
  have hp0 : 0 < H₂ ^ (-α) := Real.rpow_pos_of_pos h2.1 _
  have hfirst : (1 - φ) * ((1 - α) * A * H₂ ^ (-α)) / (A * H₂ ^ (1 - α) + R) <
      (1 - φ) * ((1 - α) * A * H₁ ^ (-α)) / (A * H₁ ^ (1 - α) + R) := by
    have hk : 0 < (1 - φ) * ((1 - α) * A) := by
      have : 0 < 1 - φ := by linarith
      have : 0 < 1 - α := by linarith
      positivity
    rw [show (1 - φ) * ((1 - α) * A * H₂ ^ (-α)) = (1 - φ) * ((1 - α) * A) * H₂ ^ (-α) by ring,
      show (1 - φ) * ((1 - α) * A * H₁ ^ (-α)) = (1 - φ) * ((1 - α) * A) * H₁ ^ (-α) by ring]
    rw [div_lt_div_iff₀ (hc1.trans hc2) hc1]
    have := mul_lt_mul_of_pos_left hp hk
    nlinarith [mul_pos hk hp0]
  have hsecond : φ / (1 - H₁) < φ / (1 - H₂) := by
    apply div_lt_div_of_pos_left hφ0 (by linarith [h2.2]) (by linarith)
  unfold labourFoc
  linarith

/-! ### Log-linearisation -/

/-- AKMM, p. 277: output in log deviations,
`e^z(K̄e^k)^α(H̄e^h)^{1−α} = K̄^αH̄^{1−α}e^{z+αk+(1−α)h}`. -/
theorem rbc_output_exp {α Kbar Hbar : ℝ} (hK : 0 < Kbar) (hH : 0 < Hbar) (z k h : ℝ) :
    exp z * (Kbar * exp k) ^ α * (Hbar * exp h) ^ (1 - α) =
      Kbar ^ α * Hbar ^ (1 - α) * exp (z + α * k + (1 - α) * h) := by
  rw [Real.mul_rpow hK.le (exp_pos k).le, Real.mul_rpow hH.le (exp_pos h).le,
    ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, Real.exp_add]
  ring_nf

/-- Derivative at `0` of `ε ↦ c·e^{εx}`. -/
theorem loglin_exp_deriv (c x : ℝ) : HasDerivAt (fun ε => c * exp (ε * x)) (c * x) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const x).exp.const_mul c
  simpa using h

/-- AKMM, p. 277, the first log-linearised equation: along any direction
`(k′, c, z, k, h)` of log deviations, the resource constraint (10.9),
`K̄e^{k′} + C̄e^c − K̄^αH̄^{1−α}e^{z+αk+(1−α)h} − (1 − δ)K̄e^k`, has derivative
`K̄k′ + C̄c − K̄^αH̄^{1−α}(z + αk + (1 − α)h) − (1 − δ)K̄k` at the steady state. -/
theorem loglin_resource (α δ Kbar Hbar Cbar k' c z k h : ℝ) :
    HasDerivAt (fun ε => Kbar * exp (ε * k') + Cbar * exp (ε * c) -
        Kbar ^ α * Hbar ^ (1 - α) * exp (ε * (z + α * k + (1 - α) * h)) -
        (1 - δ) * Kbar * exp (ε * k))
      (Kbar * k' + Cbar * c - Kbar ^ α * Hbar ^ (1 - α) * (z + α * k + (1 - α) * h) -
        (1 - δ) * Kbar * k) 0 :=
  (((loglin_exp_deriv Kbar k').add (loglin_exp_deriv Cbar c)).sub
    (loglin_exp_deriv _ _)).sub (loglin_exp_deriv _ _)

/-- AKMM, p. 277, the labour supply condition (10.14) in logs: the term `−log(1 − H̄e^{εh})` has
derivative `H̄h/(1 − H̄)` at `ε = 0` (the other terms of the log of (10.14) are linear in the log
deviations). -/
theorem loglin_labour {Hbar : ℝ} (hH1 : Hbar < 1) (h : ℝ) :
    HasDerivAt (fun ε => -Real.log (1 - Hbar * exp (ε * h))) (Hbar * h / (1 - Hbar)) 0 := by
  have hd := (loglin_exp_deriv Hbar h).const_sub 1
  have hpos : (1 - Hbar * exp (0 * h)) ≠ 0 := by simp; linarith
  have := (hd.log hpos).neg
  convert this using 1
  simp
  ring

/-- AKMM, p. 277, the Euler equation (10.13) in logs (certainty equivalence, fn. 7): the term
`log(1 − δ + R̄e^{εx})`, with `R̄ = αK̄^{α−1}H̄^{1−α}` and `x = z′ + (α − 1)k′ + (1 − α)h′`, has
derivative `βR̄x` at the steady state `β(1 − δ + R̄) = 1`. -/
theorem loglin_euler {β δ Rbar : ℝ} (hss : β * (1 - δ + Rbar) = 1) (x : ℝ) :
    HasDerivAt (fun ε => Real.log (1 - δ + Rbar * exp (ε * x))) (β * Rbar * x) 0 := by
  have hd := (loglin_exp_deriv Rbar x).const_add (1 - δ)
  have hne : 1 - δ + Rbar ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hss; exact zero_ne_one hss
  have hpos : (1 - δ + Rbar * exp (0 * x)) ≠ 0 := by simpa using hne
  have := hd.log hpos
  convert this using 1
  simp only [zero_mul, exp_zero, mul_one]
  have hβ : β = (1 - δ + Rbar)⁻¹ := eq_inv_of_mul_eq_one_left hss
  rw [hβ]
  field_simp

/-- AKMM, p. 277: `θ ≡ (1 − H̄)/(H̄(1 − α) + α)`. -/
noncomputable def theta (α Hbar : ℝ) : ℝ := (1 - Hbar) / (Hbar * (1 - α) + α)

/-- AKMM, (10.15), p. 277: the log-linearised labour supply condition
`−c + z + αk − αh = (H̄/(1 − H̄))h` is equivalent to `h = θ(z + αk − c)`. -/
theorem eq_10_15 {α Hbar : ℝ} (hα0 : 0 < α) (hH0 : 0 < Hbar) (hH1 : Hbar < 1)
    (z k c h : ℝ) :
    -c + z + α * k - α * h = Hbar / (1 - Hbar) * h ↔ h = theta α Hbar * (z + α * k - c) := by
  have h1 : 0 < 1 - Hbar := by linarith
  have h2 : 0 < Hbar * (1 - α) + α := by nlinarith
  unfold theta
  rw [div_mul_eq_mul_div, eq_div_iff h1.ne', div_mul_eq_mul_div, eq_comm, eq_div_iff h2.ne']
  constructor <;> intro h <;> linarith

/-- AKMM, (10.16), p. 277: substituting (10.15) into the log-linearised resource constraint. -/
theorem eq_10_16 {α δ Kbar Hbar Cbar θ k' c z k h : ℝ}
    (hres : Kbar * k' + Cbar * c =
      Kbar ^ α * Hbar ^ (1 - α) * (z + α * k + (1 - α) * h) + (1 - δ) * Kbar * k)
    (hh : h = θ * (z + α * k - c)) :
    Kbar * k' = Kbar ^ α * Hbar ^ (1 - α) * (1 + θ * (1 - α)) * z +
      (Kbar ^ α * Hbar ^ (1 - α) * α * (1 + θ * (1 - α)) + (1 - δ) * Kbar) * k -
      (Kbar ^ α * Hbar ^ (1 - α) * θ * (1 - α) + Cbar) * c := by
  subst hh
  linear_combination hres

/-- AKMM, (10.17), p. 278, corrected: substituting `h′ = θ(z′ + αk′ − c′)` into the log-linearised
Euler equation `−c = βαK̄^{α−1}H̄^{1−α}(z′ + (α − 1)k′ + (1 − α)h′) − c′`, with expectations
`E_t c′` and `E_t z′ = ρz` (the equation is linear, so it holds for the expectations), gives
`βαK̄^{α−1}H̄^{1−α}(1 − α)(1 − θα)k′ + (βαθ(1 − α)K̄^{α−1}H̄^{1−α} + 1)E_t c′
 = βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρz + c`. -/
theorem eq_10_17 {α β ρ Kbar Hbar θ k' Ec' Eh' z c : ℝ}
    (heul : -c = β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) *
      (ρ * z + (α - 1) * k' + (1 - α) * Eh') - Ec')
    (hh : Eh' = θ * (ρ * z + α * k' - Ec')) :
    β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) * (1 - α) * (1 - θ * α) * k' +
        (β * α * θ * (1 - α) * Kbar ^ (α - 1) * Hbar ^ (1 - α) + 1) * Ec' =
      β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ * z + c := by
  subst hh
  linear_combination heul

/-- AKMM, (10.17), p. 278, as printed: the coefficient of `z_t` is printed
`β(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ`; it differs from the derived `βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ`
(`eq_10_17`) whenever `α ≠ 1` and the other factors are nonzero (in particular for
`α ∈ (0, 1)`, `β, ρ, K̄, H̄ > 0`, `θ ≥ 0`). -/
theorem eq_10_17_printed_counterexample {α β ρ Kbar Hbar θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hρ : 0 < ρ) (hK : 0 < Kbar) (hH : 0 < Hbar) (hθ : 0 ≤ θ) :
    β * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ ≠
      β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ := by
  have h1 : 0 < 1 + θ * (1 - α) := by nlinarith
  have hK' : 0 < Kbar ^ (α - 1) := Real.rpow_pos_of_pos hK _
  have hH' : 0 < Hbar ^ (1 - α) := Real.rpow_pos_of_pos hH _
  have hpos : 0 < β * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ := by positivity
  intro h
  have : β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ =
      α * (β * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ) := by ring
  rw [this] at h
  nlinarith

/-- AKMM, (10.27), pp. 280–281: the matrices `B`, `A` and (corrected) `E` of the log-linearised
growth model, with `Y = K̄^αH̄^{1−α}` and `Q = βαK̄^{α−1}H̄^{1−α}`. -/
noncomputable def rbcB (α β Kbar Hbar θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kbar, 0;
    β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) * (1 - α) * (1 - θ * α),
      β * α * θ * (1 - α) * Kbar ^ (α - 1) * Hbar ^ (1 - α) + 1]

/-- The matrix `A` of (10.27). -/
noncomputable def rbcA (α δ Kbar Hbar Cbar θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kbar ^ α * Hbar ^ (1 - α) * α * (1 + θ * (1 - α)) + (1 - δ) * Kbar,
      -(Kbar ^ α * Hbar ^ (1 - α) * θ * (1 - α) + Cbar);
    0, 1]

/-- The vector `E` of (10.27), with the factor `α` restored in its second entry. -/
noncomputable def rbcE (α β ρ Kbar Hbar θ : ℝ) : Fin 2 → ℝ :=
  ![Kbar ^ α * Hbar ^ (1 - α) * (1 + θ * (1 - α)),
    β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ]

/-- AKMM, (10.27), p. 281: "In matrix form, (10.16) and (10.17) can be expressed as
`B[k_{t+1}; E_t c_{t+1}] = A[k_t; c_t] + Ez_t`" (with `E` corrected). -/
theorem eq_10_27 (α β δ ρ Kbar Hbar Cbar θ k' Ec' k c z : ℝ) :
    (rbcB α β Kbar Hbar θ).mulVec ![k', Ec'] =
        (rbcA α δ Kbar Hbar Cbar θ).mulVec ![k, c] + z • rbcE α β ρ Kbar Hbar θ ↔
      (Kbar * k' = Kbar ^ α * Hbar ^ (1 - α) * (1 + θ * (1 - α)) * z +
        (Kbar ^ α * Hbar ^ (1 - α) * α * (1 + θ * (1 - α)) + (1 - δ) * Kbar) * k -
        (Kbar ^ α * Hbar ^ (1 - α) * θ * (1 - α) + Cbar) * c) ∧
      (β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) * (1 - α) * (1 - θ * α) * k' +
        (β * α * θ * (1 - α) * Kbar ^ (α - 1) * Hbar ^ (1 - α) + 1) * Ec' =
      β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ * z + c) := by
  rw [funext_iff, Fin.forall_fin_two]
  simp only [rbcB, rbcA, rbcE, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end AKMM.ComputationalTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Blanchard–Kahn condition

AKMM, §10.6.1, pp. 278–283.

* One jump variable, (10.18)–(10.20): `y_{t+1} = λy_t` with `λ = 1/φ`; `y_{t+T} = λᵀy_t`; for
  `λ > 1` the only path that does not blow up is `y ≡ 0`, for `0 < λ ≤ 1` every path stays
  bounded (`eq_10_19`, `eq_10_20`, `bk_scalar_indeterminate`).
* With a shock, (10.21)–(10.23), with conditional expectations `E_t` (Miao's `CondExpSystem`):
  `E_t[y_{t+T}] = λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)·z_t` (`bk_forecast`, fn. 8, and the book's form
  `bk_forecast_book`); for `λ > 1` the forecasts stay bounded iff `y_t = −z_t/(λ − ρ)`
  (`eq_10_23`); for `0 < λ ≤ 1` they stay bounded for every `y_t` (`bk_fn8`), and there are
  many bounded solutions (`bk_indeterminate`). The bounded adapted solution is unique
  (`eq_10_23_unique`, from Miao's (2.3)).
* Guess and verify, (10.24)–(10.25): `A = −1/(λ − ρ)` (`eq_10_25`).
* The general case, (10.26)–(10.31): the transformed system (`eq_10_30`), the solution
  `ỹ_t = ΛΓ₂a_t` of the unstable block (`bk_tilde_solution`), the policy
  `y_t = −H̃₂₂⁻¹H̃₂₁x_t + H̃₂₂⁻¹ΛΓ₂a_t` (`bk_y_solution`) and the law of motion of `x`
  (`bk_x_solution`); and the Blanchard–Kahn condition `h = m` (number of unstable eigenvalues =
  number of jump variables, with `H̃₂₂` invertible) giving a unique non-explosive solution
  (`bk_condition`, Miao's Theorem 1.4.2 for `[x_{t+1}; y_{t+1}] = F[x_t; y_t] + Ga_t`).
-/

namespace AKMM.ComputationalTools

open Finset Miao.RationalExpectations
open scoped Matrix

/-! ### One non-predetermined variable -/

/-- AKMM, (10.18)–(10.19), p. 278: `y_t = φy_{t+1}` with `φ > 0` is `y_{t+1} = λy_t`,
`λ = 1/φ`. -/
theorem eq_10_19 {φ : ℝ} (hφ : 0 < φ) (y y' : ℝ) : y = φ * y' ↔ y' = φ⁻¹ * y := by
  constructor
  · rintro rfl; field_simp
  · rintro rfl; field_simp

/-- AKMM, p. 278: "Applying (10.19) repeatedly, `y_{t+T} = λᵀy_t`". -/
theorem bk_scalar_iterate {lam : ℝ} {y : ℕ → ℝ} (h : ∀ t, y (t + 1) = lam * y t) (t T : ℕ) :
    y (t + T) = lam ^ T * y t := by
  induction T with
  | zero => simp
  | succ T ih => rw [← add_assoc, h, ih, pow_succ]; ring

/-- AKMM, (10.20), p. 278: for `λ > 1` the only path of `y_{t+1} = λy_t` along which `y_{t+T}`
remains bounded is `y_t = 0` for all `t`. -/
theorem eq_10_20 {lam : ℝ} (hl : 1 < lam) {y : ℕ → ℝ} (h : ∀ t, y (t + 1) = lam * y t) :
    (∃ M, ∀ t, |y t| ≤ M) ↔ ∀ t, y t = 0 := by
  constructor
  · rintro ⟨M, hM⟩ t
    by_contra hne
    have hpos : 0 < |y t| := abs_pos.2 hne
    obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt (M / |y t|) hl
    have h1 := hM (t + T)
    rw [bk_scalar_iterate h, abs_mul, abs_of_pos (by positivity : 0 < lam ^ T)] at h1
    rw [div_lt_iff₀ hpos] at hT
    linarith
  · intro h0
    exact ⟨0, fun t => by rw [h0 t, abs_zero]⟩

/-- AKMM, p. 278: "When `λ ≤ 1`, any value of `y_t` is consistent with `lim y_{t+T}` being
finite" (indeterminacy): for `0 < λ ≤ 1` every path is bounded by `|y₀|`. -/
theorem bk_scalar_indeterminate {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) {y : ℕ → ℝ}
    (h : ∀ t, y (t + 1) = lam * y t) (t : ℕ) : |y t| ≤ |y 0| := by
  have := bk_scalar_iterate h 0 t
  rw [zero_add] at this
  rw [this, abs_mul, abs_of_pos (pow_pos hl0 t)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hl0.le hl1)

/-! ### A jump variable driven by an AR(1) shock -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- AKMM, p. 279 and fn. 8: from (10.21) `E_t[y_{t+1}] = λy_t + z_t` and (10.22)
`E_t[z_{t+1}] = ρz_t`, the law of iterated expectations gives
`E_t[y_{t+T}] = λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)·z_t` (`λ ≠ ρ`). -/
theorem bk_forecast (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hne : lam ≠ ρ) {y z : ℕ → V}
    (hy : sre_IsAdapted E y) (hz : sre_IsAdapted E z)
    (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t T : ℕ) :
    E.E t (y (t + T)) = lam ^ T • y t + ((lam ^ T - ρ ^ T) / (lam - ρ)) • z t := by
  have hd : lam - ρ ≠ 0 := sub_ne_zero.2 hne
  induction T with
  | zero => simp [hy t]
  | succ T ih =>
    rw [← add_assoc, ← E.tower_le_apply (Nat.le_add_right t T), h21, map_add, map_smul, ih,
      sre_iter E hz h22 T t, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
    congr 1
    · rw [pow_succ, mul_comm]
    · congr 1
      field_simp
      ring

/-- AKMM, p. 279: the printed form `E_t[y_{t+T}] = λᵀ[y_t + (1/λ)(1 + ρ/λ + ⋯ + (ρ/λ)^{T−1})z_t]
= λᵀy_t + (1 − (ρ/λ)ᵀ)/(λ − ρ)·λᵀz_t` agrees with `bk_forecast` (`λ ≠ 0`). -/
theorem bk_forecast_book {lam ρ : ℝ} (hl : lam ≠ 0) (hne : lam ≠ ρ) (T : ℕ) :
    (lam ^ T - ρ ^ T) / (lam - ρ) = lam ^ T * ((1 - (ρ / lam) ^ T) / (lam - ρ)) ∧
      lam ^ T * (1 / lam * ∑ j ∈ range T, (ρ / lam) ^ j) =
        lam ^ T * ((1 - (ρ / lam) ^ T) / (lam - ρ)) := by
  have hd : lam - ρ ≠ 0 := sub_ne_zero.2 hne
  have hq : ρ / lam ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hl] at h; exact hne h.symm
  refine ⟨by rw [div_pow]; field_simp, ?_⟩
  rw [geom_sum_eq hq]
  congr 1
  have h1 : ρ / lam - 1 ≠ 0 := sub_ne_zero.2 hq
  field_simp
  ring

/-- AKMM, (10.23), p. 279: for `λ > 1` and `0 ≤ ρ < 1`, the forecasts `E_t[y_{t+T}]` remain
bounded as `T → ∞` exactly when `y_t = −z_t/(λ − ρ)`. -/
theorem eq_10_23 (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hl : 1 < lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {y z : ℕ → V} (hy : sre_IsAdapted E y) (hz : sre_IsAdapted E z)
    (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    (∃ M, ∀ T, ‖E.E t (y (t + T))‖ ≤ M) ↔ y t = -(lam - ρ)⁻¹ • z t := by
  have hd : 0 < lam - ρ := by linarith
  have hform : ∀ T, E.E t (y (t + T)) =
      lam ^ T • (y t + (lam - ρ)⁻¹ • z t) - (ρ ^ T / (lam - ρ)) • z t := by
    intro T
    rw [bk_forecast E (by linarith) hy hz h21 h22, smul_add, smul_smul, sub_div, sub_smul,
      div_eq_mul_inv]
    abel
  have hρT : ∀ T : ℕ, ‖(ρ ^ T / (lam - ρ)) • z t‖ ≤ ‖z t‖ / (lam - ρ) := by
    intro T
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_of_nonneg (pow_nonneg hρ0 T)]
    rw [div_mul_eq_mul_div]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le)
  constructor
  · rintro ⟨M, hM⟩
    set w := y t + (lam - ρ)⁻¹ • z t
    have hw : w = 0 := by
      by_contra hne
      have hpos : 0 < ‖w‖ := norm_pos_iff.2 hne
      obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt ((M + ‖z t‖ / (lam - ρ)) / ‖w‖) hl
      have h1 : lam ^ T * ‖w‖ ≤ M + ‖z t‖ / (lam - ρ) := by
        have := hM T
        rw [hform T] at this
        have h2 := norm_sub_norm_le (lam ^ T • w) ((ρ ^ T / (lam - ρ)) • z t)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < lam ^ T)] at h2
        linarith [hρT T]
      rw [div_lt_iff₀ hpos] at hT
      linarith
    have : y t = w - (lam - ρ)⁻¹ • z t := by simp only [w]; abel
    rw [this, hw, zero_sub, neg_smul]
  · intro hyt
    refine ⟨‖z t‖ / (lam - ρ), fun T => ?_⟩
    have hw : y t + (lam - ρ)⁻¹ • z t = 0 := by rw [hyt, neg_smul, neg_add_cancel]
    rw [hform T, hw, smul_zero, zero_sub, norm_neg]
    exact hρT T

/-- AKMM, p. 279, fn. 8: for `0 < λ ≤ 1` (and `0 ≤ ρ < 1`, `λ ≠ ρ`) the forecasts
`λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)·z_t` stay bounded for every value of `y_t` ("indeterminacy"). -/
theorem bk_fn8 (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hne : lam ≠ ρ) {y z : ℕ → V} (hy : sre_IsAdapted E y)
    (hz : sre_IsAdapted E z) (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    ∃ M, ∀ T, ‖E.E t (y (t + T))‖ ≤ M := by
  have hd : 0 < |lam - ρ| := abs_pos.2 (sub_ne_zero.2 hne)
  refine ⟨‖y t‖ + 2 / |lam - ρ| * ‖z t‖, fun T => ?_⟩
  rw [bk_forecast E hne hy hz h21 h22]
  have hl : lam ^ T ≤ 1 := pow_le_one₀ hl0.le hl1
  have hr : ρ ^ T ≤ 1 := pow_le_one₀ hρ0 hρ1.le
  have hlp : 0 ≤ lam ^ T := pow_nonneg hl0.le T
  have hrp : 0 ≤ ρ ^ T := pow_nonneg hρ0 T
  calc ‖lam ^ T • y t + ((lam ^ T - ρ ^ T) / (lam - ρ)) • z t‖
      ≤ ‖lam ^ T • y t‖ + ‖((lam ^ T - ρ ^ T) / (lam - ρ)) • z t‖ := norm_add_le _ _
    _ ≤ ‖y t‖ + 2 / |lam - ρ| * ‖z t‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlp,
          abs_div]
        gcongr
        · exact mul_le_of_le_one_left (norm_nonneg _) hl
        · rw [abs_le]; constructor <;> linarith

/-- AKMM, p. 279: "When `λ ≤ 1`, indeterminacy exists, because many values of `y_t` can keep
`lim E_t[y_{t+T}]` finite": for `|λ| ≤ 1`, adding to any solution `y` of (10.21) the bubble
`λᵗX` (with `X` known at date `0`) gives another solution, bounded if `y` is. -/
theorem bk_indeterminate (E : CondExpSystem ℝ V) {lam : ℝ} (hl : |lam| ≤ 1) {y z : ℕ → V}
    (hy : sre_IsAdapted E y) (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t) {X : V}
    (hX : E.E 0 X = X) :
    sre_IsAdapted E (fun t => y t + lam ^ t • X) ∧
      (∀ t, E.E t (y (t + 1) + lam ^ (t + 1) • X) = lam • (y t + lam ^ t • X) + z t) ∧
      (sre_IsBounded y → sre_IsBounded (fun t => y t + lam ^ t • X)) := by
  have hXt : ∀ t, E.E t X = X := fun t => by
    rw [← hX, E.tower_ge_apply (Nat.zero_le t)]
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · simp only [map_add, map_smul, hy t, hXt t]
  · rw [map_add, map_smul, h21, hXt, smul_add, smul_smul, pow_succ, mul_comm (lam ^ t)]
    abel
  · rintro ⟨M, hM⟩
    refine ⟨M + ‖X‖, fun t => ?_⟩
    refine (norm_add_le _ _).trans (add_le_add (hM t) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hl)

/-- AKMM, (10.23), p. 279, uniqueness among bounded solutions: for `|λ| > 1`, `|ρ| < |λ|` and a
bounded adapted shock with `E_t[z_{t+1}] = ρz_t`, every bounded adapted solution of (10.21) is
`y_t = −z_t/(λ − ρ)` (Miao's (2.3) and its uniqueness, `eq_2_3_unique`, `sre_fwd_ar1`). -/
theorem eq_10_23_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {lam ρ : ℝ}
    (hl : 1 < |lam|) (hρ : |ρ| < |lam|) {y z : ℕ → V} (hy : sre_IsAdapted E y)
    (hyb : sre_IsBounded y) (hz : sre_IsAdapted E z) (hzb : sre_IsBounded z)
    (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    y t = -(lam - ρ)⁻¹ • z t := by
  rw [eq_2_3_unique E hl hz hzb hy hyb h21, sre_fwd_ar1 E hρ hz h22 t, neg_inv, neg_sub]

/-- AKMM, (10.24)–(10.25), p. 280 (guess and verify): `y_t = Az_t` solves (10.21) for every
`z_t` iff `Aρ = λA + 1`, i.e. `A = −1/(λ − ρ)`; and then `E_t[Az_{t+1}] = λAz_t + z_t`. -/
theorem eq_10_25 {lam ρ A : ℝ} (hne : lam ≠ ρ) :
    A * ρ = lam * A + 1 ↔ A = -1 / (lam - ρ) := by
  have hd : lam - ρ ≠ 0 := sub_ne_zero.2 hne
  rw [eq_div_iff hd]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 280 ("verify"): with `A = −1/(λ − ρ)`, `y_t = Az_t` satisfies (10.21). -/
theorem eq_10_24_verify (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hne : lam ≠ ρ) {z : ℕ → V}
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    E.E t ((-1 / (lam - ρ)) • z (t + 1)) = lam • ((-1 / (lam - ρ)) • z t) + z t := by
  have hA := (eq_10_25 (A := -1 / (lam - ρ)) hne).2 rfl
  rw [map_smul, h22, smul_smul, smul_smul, hA, add_smul, one_smul]

/-! ### `m` non-predetermined and `n + k` predetermined variables -/

/-- AKMM, (10.28)–(10.30), p. 281: if `F = HJH⁻¹`, multiplying
`[x_{t+1}; E_t y_{t+1}] = F[x_t; y_t] + Ga_t` by `H⁻¹` gives
`H⁻¹[x_{t+1}; E_t y_{t+1}] = JH⁻¹[x_t; y_t] + H⁻¹Ga_t`. -/
theorem eq_10_30 {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι]
    {F H Hinv J : Matrix ι ι ℝ} (G : Matrix ι σ ℝ) (hH : Hinv * H = 1)
    (hF : F = H * J * Hinv) {w w' : ι → ℝ} {a : σ → ℝ} (h : w' = F *ᵥ w + G *ᵥ a) :
    Hinv *ᵥ w' = J *ᵥ (Hinv *ᵥ w) + (Hinv * G) *ᵥ a := by
  rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hF, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, Matrix.one_mul]

/-- AKMM, p. 282: the unstable block `E_t[ỹ_{t+1}] = J₂ỹ_t + Γ₂a_t`, with `J₂ = diag(λᵢ)` and
`E_t a_{t+1} = ρa_t`, is solved by `ỹ_t = ΛΓ₂a_t` with `Λ = diag(−1/(λᵢ − ρ))`: for every
value `g = Γ₂a_t`, `Λ(ρg) = J₂(Λg) + g`, componentwise (10.23). -/
theorem bk_tilde_solution {κ : Type*} [Fintype κ] [DecidableEq κ] {lamv : κ → ℝ} {ρ : ℝ}
    (hne : ∀ i, lamv i ≠ ρ) (g : κ → ℝ) :
    Matrix.diagonal (fun i => -1 / (lamv i - ρ)) *ᵥ (ρ • g) =
      Matrix.diagonal lamv *ᵥ (Matrix.diagonal (fun i => -1 / (lamv i - ρ)) *ᵥ g) + g := by
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  have hd : lamv i - ρ ≠ 0 := sub_ne_zero.2 (hne i)
  field_simp
  ring

/-- AKMM, p. 283: from `ΛΓ₂a_t = H̃₂₁x_t + H̃₂₂y_t` (10.31) and `H̃₂₂` invertible (left inverse
`Q`), "the solution for `y_t` is `y_t = −H̃₂₂⁻¹H̃₂₁x_t + H̃₂₂⁻¹ΛΓ₂a_t`". -/
theorem bk_y_solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {H21 : Matrix κ ι ℝ}
    {H22 Q : Matrix κ κ ℝ} (hQ : Q * H22 = 1) {x : ι → ℝ} {y r : κ → ℝ}
    (h : r = H21 *ᵥ x + H22 *ᵥ y) : y = -((Q * H21) *ᵥ x) + Q *ᵥ r := by
  rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  abel

/-- AKMM, p. 283: "From (10.28), `x_{t+1} = F₁₁x_t + F₁₂y_t + G₁a_t =
(F₁₁ − F₁₂H̃₂₂⁻¹H̃₂₁)x_t + (G₁ + F₁₂H̃₂₂⁻¹ΛΓ₂)a_t`". -/
theorem bk_x_solution {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    {F11 : Matrix ι ι ℝ} {F12 : Matrix ι κ ℝ} {G1 : Matrix ι σ ℝ} {H21 : Matrix κ ι ℝ}
    {Q : Matrix κ κ ℝ} {LG : Matrix κ σ ℝ} {x x' : ι → ℝ} {y : κ → ℝ} {a : σ → ℝ}
    (hx : x' = F11 *ᵥ x + F12 *ᵥ y + G1 *ᵥ a) (hy : y = -((Q * H21) *ᵥ x) + (Q * LG) *ᵥ a) :
    x' = (F11 - F12 * Q * H21) *ᵥ x + (G1 + F12 * Q * LG) *ᵥ a := by
  rw [hx, hy, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

/-- AKMM, p. 281 (Blanchard and Kahn 1980): "the equilibrium (i.e. the solutions for `x_t` and
`y_t` that don't blow up in the future) is unique if `h = m`". For
`[x_{t+1}; y_{t+1}] = F[x_t; y_t] + Ga_t` (the certainty-equivalent form of (10.28)) with a real
block split of `F` into `n` stable and `h` unstable directions (`P = H⁻¹` with the stable rows
first), `h = m` and `H̃₂₂ = P_{uy}` invertible, there is exactly one bounded solution for every
initial `x₀` and every bounded `a` (Miao's Theorem 1.4.2 with `A = I`). -/
theorem bk_condition {κ υ σ τ m : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ]
    [DecidableEq υ] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [Fintype m]
    (F : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (G : Matrix (κ ⊕ υ) m ℝ)
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : Miao.DifferenceEquations.IsRealBlockSplit F P R Js Ju)
    (hhm : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (x₀ : κ → ℝ) (a : ℕ → m → ℝ)
    (ha : Miao.DifferenceEquations.IsStableSeq a) :
    ∃! w : ℕ → κ ⊕ υ → ℝ, (∀ t, w (t + 1) = F *ᵥ w t + G *ᵥ a t) ∧ w 0 ∘ Sum.inl = x₀ ∧
      Miao.DifferenceEquations.IsStableSeq w := by
  have hS' : Miao.DifferenceEquations.IsRealBlockSplit ((1 : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ)⁻¹ * F)
      P R Js Ju := by rwa [inv_one, Matrix.one_mul]
  have h := Miao.DifferenceEquations.theorem_1_4_2 1 F G (by simp) hS' hhm Q hQ x₀ a ha
  simpa [Miao.DifferenceEquations.IsSolution, Matrix.one_mulVec] using h

end AKMM.ComputationalTools

set_option linter.style.longLine false
#print axioms AKMM.ComputationalTools.linInterp
#print axioms AKMM.ComputationalTools.linInterp_left
#print axioms AKMM.ComputationalTools.linInterp_right
#print axioms AKMM.ComputationalTools.linInterp_unique
#print axioms AKMM.ComputationalTools.linInterp_error
#print axioms AKMM.ComputationalTools.linInterp_error_h
#print axioms AKMM.ComputationalTools.kink
#print axioms AKMM.ComputationalTools.linInterp_kink_not_differentiable
#print axioms AKMM.ComputationalTools.linInterp_kink_differentiable_of_eq
#print axioms AKMM.ComputationalTools.cubic_spline_existsUnique
#print axioms AKMM.ComputationalTools.eq_10_1_unique_iff
#print axioms AKMM.ComputationalTools.eq_10_1_poly
#print axioms AKMM.ComputationalTools.bisect_sign_eq_iff
#print axioms AKMM.ComputationalTools.bisectStep
#print axioms AKMM.ComputationalTools.bisect
#print axioms AKMM.ComputationalTools.bisectStep_cases
#print axioms AKMM.ComputationalTools.bisect_length
#print axioms AKMM.ComputationalTools.bisect_mono
#print axioms AKMM.ComputationalTools.bisect_bracket
#print axioms AKMM.ComputationalTools.bisect_mem
#print axioms AKMM.ComputationalTools.bisect_bracket_root
#print axioms AKMM.ComputationalTools.bisect_converges
#print axioms AKMM.ComputationalTools.bisect_iteration_count
#print axioms AKMM.ComputationalTools.bisect_terminates
#print axioms AKMM.ComputationalTools.bisect_ten_steps
#print axioms AKMM.ComputationalTools.bisectJump
#print axioms AKMM.ComputationalTools.bisect_discontinuous_no_root
#print axioms AKMM.ComputationalTools.newtonStep
#print axioms AKMM.ComputationalTools.eq_10_2
#print axioms AKMM.ComputationalTools.newton_affine_exact
#print axioms AKMM.ComputationalTools.newton_local_quadratic
#print axioms AKMM.ComputationalTools.newton_converges
#print axioms AKMM.ComputationalTools.central_difference_tendsto
#print axioms AKMM.ComputationalTools.central_difference_quadratic
#print axioms AKMM.ComputationalTools.newtonOptStep
#print axioms AKMM.ComputationalTools.newtonOpt_eq_newtonStep_deriv
#print axioms AKMM.ComputationalTools.eq_10_3
#print axioms AKMM.ComputationalTools.eq_10_3_max
#print axioms AKMM.ComputationalTools.newtonOpt_quadratic_exact
#print axioms AKMM.ComputationalTools.omegaStar
#print axioms AKMM.ComputationalTools.golden_omega_sq
#print axioms AKMM.ComputationalTools.golden_omega_eq_sq
#print axioms AKMM.ComputationalTools.golden_omega_bounds
#print axioms AKMM.ComputationalTools.golden_omega_pos
#print axioms AKMM.ComputationalTools.golden_omega_lt_half
#print axioms AKMM.ComputationalTools.golden_ratio_eq
#print axioms AKMM.ComputationalTools.GoldenBracket
#print axioms AKMM.ComputationalTools.GoldenBracket.mk
#print axioms AKMM.ComputationalTools.GoldenBracket.a
#print axioms AKMM.ComputationalTools.GoldenBracket.b
#print axioms AKMM.ComputationalTools.GoldenBracket.c
#print axioms AKMM.ComputationalTools.GoldenBracket.IsBracket
#print axioms AKMM.ComputationalTools.GoldenBracket.IsGolden
#print axioms AKMM.ComputationalTools.goldenStep
#print axioms AKMM.ComputationalTools.goldenStep_spec
#print axioms AKMM.ComputationalTools.golden_length
#print axioms AKMM.ComputationalTools.golden_printed_length_counterexample
#print axioms AKMM.ComputationalTools.golden_terminates
#print axioms AKMM.ComputationalTools.golden_bracket_max
#print axioms AKMM.ComputationalTools.golden_iterate_max
#print axioms AKMM.ComputationalTools.golden_two_lengths
#print axioms AKMM.ComputationalTools.golden_fn3_unique
#print axioms AKMM.ComputationalTools.golden_removed_fraction
#print axioms AKMM.ComputationalTools.ex1Obj
#print axioms AKMM.ComputationalTools.ex1Foc
#print axioms AKMM.ComputationalTools.eq_10_5
#print axioms AKMM.ComputationalTools.ex1_foc_strictAnti
#print axioms AKMM.ComputationalTools.ex1_root_isMax
#print axioms AKMM.ComputationalTools.ex1_cbrt_eighth
#print axioms AKMM.ComputationalTools.ex1_unique_root
#print axioms AKMM.ComputationalTools.ar1_uncond_var
#print axioms AKMM.ComputationalTools.tauchenGrid
#print axioms AKMM.ComputationalTools.tauchenGrid_last
#print axioms AKMM.ComputationalTools.tauchenUpper
#print axioms AKMM.ComputationalTools.tauchenLower
#print axioms AKMM.ComputationalTools.tauchen_lower_succ
#print axioms AKMM.ComputationalTools.tauchenProb
#print axioms AKMM.ComputationalTools.tauchen_stochastic
#print axioms AKMM.ComputationalTools.tauchenPrinted
#print axioms AKMM.ComputationalTools.tauchen_printed_neg
#print axioms AKMM.ComputationalTools.tauchen_printed_row_sum
#print axioms AKMM.ComputationalTools.tauchenCauchyCdf
#print axioms AKMM.ComputationalTools.tauchenCauchyCdf_strictMono
#print axioms AKMM.ComputationalTools.rouwenhorst
#print axioms AKMM.ComputationalTools.rouwenhorst_two
#print axioms AKMM.ComputationalTools.rouwenhorst_row_zero
#print axioms AKMM.ComputationalTools.rouwenhorst_nonneg
#print axioms AKMM.ComputationalTools.rwLow
#print axioms AKMM.ComputationalTools.rwHigh
#print axioms AKMM.ComputationalTools.rwRow
#print axioms AKMM.ComputationalTools.rw_coeff_linear_mul
#print axioms AKMM.ComputationalTools.rouwenhorst_eq_coeff
#print axioms AKMM.ComputationalTools.rwRow_natDegree_le
#print axioms AKMM.ComputationalTools.rw_sum_coeff_pow
#print axioms AKMM.ComputationalTools.rw_sum_coeff_mul_index
#print axioms AKMM.ComputationalTools.rouwenhorst_row_sum
#print axioms AKMM.ComputationalTools.rouwenhorst_cond_mean_index
#print axioms AKMM.ComputationalTools.rw_binomial_rows
#print axioms AKMM.ComputationalTools.rouwenhorst_invariant
#print axioms AKMM.ComputationalTools.rw_binomial_moments
#print axioms AKMM.ComputationalTools.rwGrid
#print axioms AKMM.ComputationalTools.rwGrid_ends
#print axioms AKMM.ComputationalTools.rouwenhorst_cond_mean
#print axioms AKMM.ComputationalTools.rouwenhorst_stationary_mean
#print axioms AKMM.ComputationalTools.rouwenhorst_stationary_var
#print axioms AKMM.ComputationalTools.rouwenhorst_stationary_autocov
#print axioms AKMM.ComputationalTools.rouwenhorst_matches_ar1
#print axioms AKMM.ComputationalTools.rouwenhorstPrinted
#print axioms AKMM.ComputationalTools.rouwenhorst_printed_counterexample
#print axioms AKMM.ComputationalTools.GridDP
#print axioms AKMM.ComputationalTools.GridDP.mk
#print axioms AKMM.ComputationalTools.GridDP.feasible
#print axioms AKMM.ComputationalTools.GridDP.feasible_nonempty
#print axioms AKMM.ComputationalTools.GridDP.ret
#print axioms AKMM.ComputationalTools.GridDP.trans
#print axioms AKMM.ComputationalTools.GridDP.trans_nonneg
#print axioms AKMM.ComputationalTools.GridDP.trans_sum
#print axioms AKMM.ComputationalTools.GridDP.β
#print axioms AKMM.ComputationalTools.GridDP.β_nonneg
#print axioms AKMM.ComputationalTools.GridDP.β_lt_one
#print axioms AKMM.ComputationalTools.GridDP.cont
#print axioms AKMM.ComputationalTools.GridDP.T
#print axioms AKMM.ComputationalTools.GridDP.cont_sub_le
#print axioms AKMM.ComputationalTools.GridDP.sup'_sub_le
#print axioms AKMM.ComputationalTools.GridDP.contraction
#print axioms AKMM.ComputationalTools.GridDP.vfi
#print axioms AKMM.ComputationalTools.GridDP.stopping_rule
#print axioms AKMM.ComputationalTools.cakeGrid
#print axioms AKMM.ComputationalTools.cakeGrid_vfi
#print axioms AKMM.ComputationalTools.stochCakeGrid
#print axioms AKMM.ComputationalTools.cakeV
#print axioms AKMM.ComputationalTools.cakeRhs
#print axioms AKMM.ComputationalTools.cake_cauchy_schwarz
#print axioms AKMM.ComputationalTools.cake_bellman
#print axioms AKMM.ComputationalTools.cake_policy_unique
#print axioms AKMM.ComputationalTools.cake_bellman_step
#print axioms AKMM.ComputationalTools.cake_bellman_unique
#print axioms AKMM.ComputationalTools.cake_path_value
#print axioms AKMM.ComputationalTools.cake_concave
#print axioms AKMM.ComputationalTools.labourFoc
#print axioms AKMM.ComputationalTools.labour_foc_unique
#print axioms AKMM.ComputationalTools.rbc_output_exp
#print axioms AKMM.ComputationalTools.loglin_exp_deriv
#print axioms AKMM.ComputationalTools.loglin_resource
#print axioms AKMM.ComputationalTools.loglin_labour
#print axioms AKMM.ComputationalTools.loglin_euler
#print axioms AKMM.ComputationalTools.theta
#print axioms AKMM.ComputationalTools.eq_10_15
#print axioms AKMM.ComputationalTools.eq_10_16
#print axioms AKMM.ComputationalTools.eq_10_17
#print axioms AKMM.ComputationalTools.eq_10_17_printed_counterexample
#print axioms AKMM.ComputationalTools.rbcB
#print axioms AKMM.ComputationalTools.rbcA
#print axioms AKMM.ComputationalTools.rbcE
#print axioms AKMM.ComputationalTools.eq_10_27
#print axioms AKMM.ComputationalTools.eq_10_19
#print axioms AKMM.ComputationalTools.bk_scalar_iterate
#print axioms AKMM.ComputationalTools.eq_10_20
#print axioms AKMM.ComputationalTools.bk_scalar_indeterminate
#print axioms AKMM.ComputationalTools.bk_forecast
#print axioms AKMM.ComputationalTools.bk_forecast_book
#print axioms AKMM.ComputationalTools.eq_10_23
#print axioms AKMM.ComputationalTools.bk_fn8
#print axioms AKMM.ComputationalTools.bk_indeterminate
#print axioms AKMM.ComputationalTools.eq_10_23_unique
#print axioms AKMM.ComputationalTools.eq_10_25
#print axioms AKMM.ComputationalTools.eq_10_24_verify
#print axioms AKMM.ComputationalTools.eq_10_30
#print axioms AKMM.ComputationalTools.bk_tilde_solution
#print axioms AKMM.ComputationalTools.bk_y_solution
#print axioms AKMM.ComputationalTools.bk_x_solution
#print axioms AKMM.ComputationalTools.bk_condition
