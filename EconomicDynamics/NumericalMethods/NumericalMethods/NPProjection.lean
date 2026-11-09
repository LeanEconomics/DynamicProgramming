/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Projection methods: residuals and weighted-residual conditions

Miao, *Economic Dynamics in Discrete Time*, §11.5 (pp. 370–373).

A functional equation `F(f) = 0` is approximated by `f̂(x; c) = ∑ⱼ cⱼ φⱼ(x)`;
the residual is `R(x; c) = F̂(f̂(·; c))(x)` and the projections are
`Pᵢ(c) = ⟨R(·; c), pᵢ⟩`. We formalise the four choices of projection
directions `pᵢ` and the relations the text asserts between them.

* Collocation (p. 371): with the point-evaluation (quadrature) inner product,
  the projection conditions are exactly `R(xᵢ; c) = 0` (`np_collocation_iff`).
  As printed, the directions are indicator functions of points; under an
  integral inner product these give `Pᵢ ≡ 0` for every `c`
  (`np_collocation_integral_degenerate`), so the book's derivation needs the
  discrete inner product.
* Least squares (p. 372): `pᵢ = ∂R/∂cᵢ` (the book prints `∂cⱼ`). The
  projection conditions are the first-order conditions of `min_c ⟨R, R⟩`
  (`np_ls_hasFDerivAt`, `np_ls_foc`); they are equivalent to minimisation when
  `R` is affine in `c` (`np_ls_affine_iff`), but not in general
  (`np_ls_not_sufficient`).
* Galerkin (p. 372): `pᵢ = φᵢ`; the conditions say `R ⊥ span{φᵢ}`
  (`np_galerkin_iff_orthogonal`), and for `F(f) = f − h` Galerkin and least
  squares coincide: both characterise the best approximation of `h`
  (`np_galerkin_iff_ls`).
* Method of moments (p. 373): `pᵢ = x^{i−1}`.
* Quadrature-based projections are "weighted collocation methods" (p. 373):
  with a quadrature inner product the projections depend on `R` only through
  its values at the nodes (`np_quadrature_proj_eq`), and when there are as many
  nodes as coefficients and the direction matrix `(pᵢ(y_k))` is nonsingular the
  projection conditions are equivalent to collocation at the nodes
  (`np_quadrature_iff_collocation`); this applies to the method of moments at
  distinct nodes (`np_moments_iff_collocation`, Vandermonde). Discrete least
  squares fitting ("regression") with as many nodes as coefficients and a
  nonsingular basis matrix is interpolation (`np_regression_iff_interpolation`).
-/

namespace Miao.NumericalMethods.NP

open Finset Filter Topology Matrix
open scoped InnerProductSpace

/-! ### The projection framework -/

/-- Miao, p. 370: the approximation `f̂(x; c) = ∑ⱼ cⱼ φⱼ(x)`. -/
def np_approx {D : Type*} {n : ℕ} (φ : Fin n → D → ℝ) (c : Fin n → ℝ) : D → ℝ :=
  fun x => ∑ j, c j * φ j x

/-- Miao, p. 371, Step 3: the residual `R(x; c) = F̂(f̂(·; c))(x)`. -/
def np_residual {D : Type*} {n : ℕ} (Fh : (D → ℝ) → D → ℝ) (φ : Fin n → D → ℝ)
    (c : Fin n → ℝ) : D → ℝ :=
  Fh (np_approx φ c)

/-- Miao, p. 371, Step 4: the projections `Pᵢ(c) = ⟨R(·; c), pᵢ⟩` for an inner product `ip`. -/
def np_proj {D : Type*} {n : ℕ} (ip : (D → ℝ) → (D → ℝ) → ℝ) (R : D → ℝ) (p : Fin n → D → ℝ)
    (i : Fin n) : ℝ :=
  ip R (p i)

/-- A quadrature (discrete) inner product `⟨f, g⟩ = ∑_k w_k f(y_k) g(y_k)` with nodes `y_k` and
weights `w_k` (Miao, p. 373). -/
def np_quadIP {D : Type*} {m : ℕ} (y : Fin m → D) (w : Fin m → ℝ) (f g : D → ℝ) : ℝ :=
  ∑ k, w k * f (y k) * g (y k)

/-- Miao, p. 371: the collocation directions `pᵢ(x) = 1` if `x = xᵢ`, `0` otherwise. -/
noncomputable def np_collocDir {D : Type*} {n : ℕ} (x : Fin n → D) (i : Fin n) : D → ℝ := by
  classical
  exact fun z => if z = x i then 1 else 0

/-- Miao, p. 373: the method-of-moments directions `pᵢ(x) = x^{i−1}` (indexed from `0`). -/
def np_momentDir {n : ℕ} (i : Fin n) : ℝ → ℝ := fun x => x ^ (i : ℕ)

/-! ### Collocation -/

/-- **Collocation** (Miao, p. 371): with a quadrature inner product whose (distinct) nodes `y`
include the collocation points `xᵢ = y(ιᵢ)`, the projection on the `i`-th collocation direction
is `w_{ιᵢ} R(xᵢ; c)`. -/
theorem np_collocation_proj {D : Type*} {m n : ℕ} {y : Fin m → D} (hy : Function.Injective y)
    (w : Fin m → ℝ) (ι : Fin n → Fin m) (R : D → ℝ) (i : Fin n) :
    np_proj (np_quadIP y w) R (np_collocDir (y ∘ ι)) i = w (ι i) * R (y (ι i)) := by
  classical
  simp only [np_proj, np_quadIP, np_collocDir, Function.comp_apply, hy.eq_iff, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (ι i)]
  simp

/-- **Collocation** (Miao, p. 371): the projection conditions `Pᵢ(c) = 0` are exactly
`R(xᵢ; c) = 0`, `i = 1, …, n` (nonzero weights at the collocation nodes). -/
theorem np_collocation_iff {D : Type*} {m n : ℕ} {y : Fin m → D} (hy : Function.Injective y)
    {w : Fin m → ℝ} (hw : ∀ k, w k ≠ 0) (ι : Fin n → Fin m) (R : D → ℝ) :
    (∀ i, np_proj (np_quadIP y w) R (np_collocDir (y ∘ ι)) i = 0) ↔ ∀ i, R (y (ι i)) = 0 := by
  simp only [np_collocation_proj hy, mul_eq_zero, hw, false_or]

/-- Correction to Miao, p. 371: under the integral inner product `⟨f, g⟩ = ∫ f g dx` on `ℝ` the
book's collocation directions (indicators of points) give `Pᵢ(c) = 0` for every residual, so the
projection conditions carry no information; collocation needs point evaluation. -/
theorem np_collocation_integral_degenerate {n : ℕ} (x : Fin n → ℝ) (R : ℝ → ℝ) (i : Fin n) :
    ∫ z, R z * np_collocDir x i z = 0 := by
  classical
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  have h : ∀ᵐ z ∂MeasureTheory.volume, z ≠ x i := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h] with z hz
  simp [np_collocDir, hz]

/-! ### Least squares -/

/-- Miao, p. 372, the least squares method: the gradient of `c ↦ ⟨R(·; c), R(·; c)⟩ = ‖R(c)‖²` is
`2⟨R(c), DR(c) ·⟩`; its `i`-th component is `2⟨R, ∂R/∂cᵢ⟩`. -/
theorem np_ls_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    {R : (Fin n → ℝ) → E} {DR : (Fin n → ℝ) →L[ℝ] E} {c : Fin n → ℝ} (hR : HasFDerivAt R DR c) :
    HasFDerivAt (fun c => ⟪R c, R c⟫_ℝ) ((2 : ℕ) • (innerSL ℝ (R c)).comp DR) c ∧
      ∀ i, ((2 : ℕ) • (innerSL ℝ (R c)).comp DR) (Pi.single i 1) =
        2 * ⟪R c, DR (Pi.single i 1)⟫_ℝ := by
  refine ⟨?_, fun i => ?_⟩
  · have h := hR.norm_sq
    have he : (fun c => ⟪R c, R c⟫_ℝ) = fun c => ‖R c‖ ^ 2 := by
      funext c
      exact real_inner_self_eq_norm_sq (R c)
    rw [he]
    exact h
  · simp [two_smul, two_mul]

/-- Miao, p. 372: at a (local) minimiser of `⟨R(·; c), R(·; c)⟩` the least squares projection
conditions `⟨R(·; c), ∂R(·; c)/∂cᵢ⟩ = 0` hold. -/
theorem np_ls_foc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    {R : (Fin n → ℝ) → E} {DR : (Fin n → ℝ) →L[ℝ] E} {c : Fin n → ℝ} (hR : HasFDerivAt R DR c)
    (hmin : IsLocalMin (fun c => ⟪R c, R c⟫_ℝ) c) (i : Fin n) :
    ⟪R c, DR (Pi.single i 1)⟫_ℝ = 0 := by
  obtain ⟨hd, hcomp⟩ := np_ls_hasFDerivAt hR
  have h0 := hmin.hasFDerivAt_eq_zero hd
  have h2 : (2 : ℝ) * ⟪R c, DR (Pi.single i 1)⟫_ℝ = 0 := by
    rw [← hcomp i, h0]
    simp
  linarith

/-- Miao, p. 372 ("it is equivalent to solving `min_c ⟨R, R⟩`"), the case where the equivalence
holds: if the residual is affine in the coefficients, `R(c) = r₀ + Lc`, then the least squares
projection conditions `⟨R(c), ∂R/∂cᵢ⟩ = ⟨R(c), L eᵢ⟩ = 0` hold iff `c` minimises `‖R‖`. -/
theorem np_ls_affine_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (r0 : E) (L : (Fin n → ℝ) →ₗ[ℝ] E) (c : Fin n → ℝ) :
    (∀ i, ⟪r0 + L c, L (Pi.single i 1)⟫_ℝ = 0) ↔ ∀ c', ‖r0 + L c‖ ≤ ‖r0 + L c'‖ := by
  constructor
  · intro h c'
    have horth : ∀ d, ⟪r0 + L c, L d⟫_ℝ = 0 := by
      intro d
      rw [LinearMap.pi_apply_eq_sum_univ L d, inner_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hs : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [inner_smul_right, hs, h i, mul_zero]
    have hdecomp : r0 + L c' = (r0 + L c) + L (c' - c) := by
      rw [map_sub]
      abel
    have hsq : ‖r0 + L c‖ ^ 2 ≤ ‖r0 + L c'‖ ^ 2 := by
      rw [hdecomp, norm_add_sq_real (r0 + L c) (L (c' - c)), horth]
      nlinarith [sq_nonneg ‖L (c' - c)‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  · intro h i
    let L' : (Fin n → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap L
    have hR : HasFDerivAt (fun c => r0 + L c) L' c := by
      have : HasFDerivAt (fun c => r0 + L' c) L' c := L'.hasFDerivAt.const_add r0
      exact this
    have hmin : IsLocalMin (fun c => ⟪r0 + L c, r0 + L c⟫_ℝ) c := by
      refine Filter.Eventually.of_forall fun c' => ?_
      simp only [real_inner_self_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (h c') 2
    exact np_ls_foc hR hmin i

/-- Correction to Miao, p. 372: for a residual that is not affine in `c`, the least squares
projection conditions do not imply minimisation. With `R(c) = c² − 1` (one coefficient), at
`c = 0` the derivative is `0`, so `⟨R, ∂R/∂c⟩ = 0`, yet `‖R(0)‖ = 1 > 0 = ‖R(1)‖`. -/
theorem np_ls_not_sufficient :
    ∃ (R : (Fin 1 → ℝ) → ℝ) (DR : (Fin 1 → ℝ) →L[ℝ] ℝ) (c : Fin 1 → ℝ),
      HasFDerivAt R DR c ∧ (∀ i, ⟪R c, DR (Pi.single i 1)⟫_ℝ = 0) ∧
        ¬ ∀ c', ‖R c‖ ≤ ‖R c'‖ := by
  refine ⟨fun c => c 0 ^ 2 - 1, 0, 0, ?_, fun i => by simp, ?_⟩
  · have h0 : HasFDerivAt (fun c : Fin 1 → ℝ => c 0) (ContinuousLinearMap.proj 0) 0 :=
      hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (0 : Fin 1 → ℝ)
    have h1 := (h0.pow 2).sub_const 1
    convert h1 using 1
    simp
  · intro h
    have := h fun _ => 1
    norm_num at this

/-! ### Galerkin -/

/-- **Galerkin** (Miao, p. 372): the conditions `⟨R, φᵢ⟩ = 0`, `i = 1, …, n`, say that the
residual is orthogonal to the span of the basis functions. -/
theorem np_galerkin_iff_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (φ : Fin n → E) (R : E) :
    (∀ i, ⟪R, φ i⟫_ℝ = 0) ↔ R ∈ (Submodule.span ℝ (Set.range φ))ᗮ := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [real_inner_comm]
      exact h i
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  · intro h i
    rw [real_inner_comm]
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Galerkin and least squares coincide for `F(f) = f − h` (Miao, p. 372): the residual is
`R(c) = ∑ⱼ cⱼ φⱼ − h`, so `∂R/∂cᵢ = φᵢ`; the Galerkin conditions hold iff `c` minimises
`‖R(c)‖`, i.e. `∑ⱼ cⱼ φⱼ` is the best approximation of `h` in `span{φⱼ}`. -/
theorem np_galerkin_iff_ls {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (φ : Fin n → E) (h : E) (c : Fin n → ℝ) :
    (∀ i, ⟪∑ j, c j • φ j - h, φ i⟫_ℝ = 0) ↔
      ∀ c' : Fin n → ℝ, ‖∑ j, c j • φ j - h‖ ≤ ‖∑ j, c' j • φ j - h‖ := by
  classical
  have hL : ∀ d : Fin n → ℝ, Fintype.linearCombination ℝ φ d = ∑ j, d j • φ j :=
    fun d => Fintype.linearCombination_apply ℝ φ d
  have hR : ∀ d : Fin n → ℝ, ∑ j, d j • φ j - h = -h + Fintype.linearCombination ℝ φ d := by
    intro d
    rw [hL]
    abel
  have hsingle : ∀ i, Fintype.linearCombination ℝ φ (Pi.single i 1) = φ i := by
    intro i
    rw [Fintype.linearCombination_apply_single, one_smul]
  have := np_ls_affine_iff (-h) (Fintype.linearCombination ℝ φ) c
  simp only [hsingle] at this
  simp only [hR]
  exact this

/-! ### Quadrature-based projections are weighted collocation -/

/-- Miao, p. 373: with a quadrature inner product, `Pᵢ(c) = ∑_k pᵢ(y_k) (w_k R(y_k; c))`; the
projections use the residual only at the quadrature nodes ("weighted collocation"). -/
theorem np_quadrature_proj_eq {D : Type*} {m n : ℕ} (y : Fin m → D) (w : Fin m → ℝ)
    (R : D → ℝ) (p : Fin n → D → ℝ) (i : Fin n) :
    np_proj (np_quadIP y w) R p i =
      ((Matrix.of fun i k => p i (y k)) *ᵥ fun k => w k * R (y k)) i := by
  simp only [np_proj, np_quadIP, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Miao, p. 373: quadrature-based projection conditions depend on `R` only through its values at
the nodes. -/
theorem np_quadrature_proj_congr {D : Type*} {m n : ℕ} (y : Fin m → D) (w : Fin m → ℝ)
    {R R' : D → ℝ} (h : ∀ k, R (y k) = R' (y k)) (p : Fin n → D → ℝ) (i : Fin n) :
    np_proj (np_quadIP y w) R p i = np_proj (np_quadIP y w) R' p i := by
  simp only [np_proj, np_quadIP, h]

/-- Miao, p. 373, "quadrature-based projection techniques are essentially weighted collocation
methods": with `n` nodes, nonzero weights and a nonsingular direction matrix `(pᵢ(y_k))`, the
projection conditions `Pᵢ(c) = 0` hold iff `R(y_k; c) = 0` at every node. -/
theorem np_quadrature_iff_collocation {D : Type*} {n : ℕ} (y : Fin n → D) {w : Fin n → ℝ}
    (hw : ∀ k, w k ≠ 0) (R : D → ℝ) (p : Fin n → D → ℝ)
    (hdet : (Matrix.of fun i k => p i (y k)).det ≠ 0) :
    (∀ i, np_proj (np_quadIP y w) R p i = 0) ↔ ∀ k, R (y k) = 0 := by
  simp only [np_quadrature_proj_eq]
  constructor
  · intro h k
    have hv := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext h)
    have := congrFun hv k
    simp only [Pi.zero_apply, mul_eq_zero, hw k, false_or] at this
    exact this
  · intro h i
    have : (fun k => w k * R (y k)) = 0 := funext fun k => by simp [h k]
    rw [this, Matrix.mulVec_zero, Pi.zero_apply]

/-- **Method of moments** (Miao, p. 373) with a quadrature at `n` distinct nodes and nonzero
weights: the moment conditions `⟨R, x^{i−1}⟩ = 0` hold iff `R` vanishes at the nodes (the
direction matrix is a Vandermonde matrix). -/
theorem np_moments_iff_collocation {n : ℕ} {y : Fin n → ℝ} (hy : Function.Injective y)
    {w : Fin n → ℝ} (hw : ∀ k, w k ≠ 0) (R : ℝ → ℝ) :
    (∀ i, np_proj (np_quadIP y w) R (np_momentDir (n := n)) i = 0) ↔ ∀ k, R (y k) = 0 := by
  refine np_quadrature_iff_collocation y hw R np_momentDir ?_
  have h : (Matrix.of fun i k => np_momentDir (n := n) i (y k)) = (Matrix.vandermonde y).transpose
    := by
    ext i k
    simp [np_momentDir, Matrix.vandermonde_apply]
  rw [h, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.2 hy

/-- **Galerkin with quadrature** (Miao, pp. 372–373): with `n` nodes, nonzero weights and a
nonsingular basis matrix `(φᵢ(y_k))`, the Galerkin conditions `⟨R, φᵢ⟩ = 0` are equivalent to
collocation at the nodes. -/
theorem np_galerkin_quadrature_iff_collocation {D : Type*} {n : ℕ} (y : Fin n → D)
    {w : Fin n → ℝ} (hw : ∀ k, w k ≠ 0) (R : D → ℝ) (φ : Fin n → D → ℝ)
    (hdet : (Matrix.of fun i k => φ i (y k)).det ≠ 0) :
    (∀ i, np_proj (np_quadIP y w) R φ i = 0) ↔ ∀ k, R (y k) = 0 :=
  np_quadrature_iff_collocation y hw R φ hdet

/-- Discrete least squares ("regression") with as many nodes as coefficients is interpolation
(Miao, pp. 372–373): if the basis matrix `(φⱼ(y_k))` is nonsingular and the weights are positive,
`c` minimises `∑_k w_k (f̂(y_k; c) − h(y_k))²` iff `f̂(y_k; c) = h(y_k)` at every node. -/
theorem np_regression_iff_interpolation {D : Type*} {n : ℕ} (y : Fin n → D) {w : Fin n → ℝ}
    (hw : ∀ k, 0 < w k) (φ : Fin n → D → ℝ) (h : D → ℝ)
    (hdet : (Matrix.of fun k j => φ j (y k)).det ≠ 0) (c : Fin n → ℝ) :
    (∀ c', ∑ k, w k * (np_approx φ c (y k) - h (y k)) ^ 2 ≤
        ∑ k, w k * (np_approx φ c' (y k) - h (y k)) ^ 2) ↔
      ∀ k, np_approx φ c (y k) = h (y k) := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => φ j (y k) with hM
  have happrox : ∀ d k, np_approx φ d (y k) = (M *ᵥ d) k := by
    intro d k
    simp only [np_approx, hM, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  constructor
  · intro hmin
    -- the interpolating coefficients `c* = M⁻¹ h` give objective `0`
    have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
    set cs := M⁻¹ *ᵥ (fun k => h (y k)) with hcs
    have hcs' : ∀ k, np_approx φ cs (y k) = h (y k) := by
      intro k
      rw [happrox, hcs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have h0 := hmin cs
    simp only [hcs', sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero] at h0
    have hterm : ∀ k ∈ Finset.univ, 0 ≤ w k * (np_approx φ c (y k) - h (y k)) ^ 2 :=
      fun k _ => mul_nonneg (hw k).le (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 (le_antisymm h0
      (Finset.sum_nonneg hterm))
    intro k
    have := hz k (Finset.mem_univ k)
    rw [mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 (hw k).ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  · intro hint c'
    simp only [hint, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k).le (sq_nonneg _)

end Miao.NumericalMethods.NP
