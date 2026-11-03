import Mathlib
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.LocallyConvex
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# There is no C¹ retraction of the closed ball onto its boundary sphere

Foundation for the Brouwer fixed-point theorem of SLP §17.3 (Theorem 17.3, p. 517), which the
book quotes without proof. Mathlib has no Brouwer theorem; this module proves the analytic core of
the argument of Milnor in the form given by C. A. Rogers, *A less strange version of Milnor's proof
of Brouwer's fixed-point theorem*, Amer. Math. Monthly 87 (1980).

`E` is a finite-dimensional real normed space and `B` its closed unit ball.

* `exists_polynomial_det_id_add_smul`: `s ↦ det (id + s • A)` is a polynomial of degree at most
  `dim E`.
* `integral_eq_of_polynomial_of_eq_on_Ioc`: if `φ x s` is a polynomial in `s` of bounded degree
  and `∫ φ x s dμ(x) = c` for all `s ∈ (0, δ]`, then `∫ φ x r dμ(x) = c` for every `r`
  (Lagrange interpolation).
* `no_C1_retraction` (Rogers' lemma): there is no map `g`, C¹ on an open neighbourhood of `B`,
  with `‖g x‖ = 1` on `B` and `g x = x` on the unit sphere.

Proof of `no_C1_retraction`. Put `f_t x = x + t (g x − x)` and `V(t) = ∫_{B°} det D f_t`.
For small `t > 0`, `f_t` is injective on the open ball `B°` (since `g − id` is Lipschitz there),
`det D f_t > 0`, and `f_t(B°) = B°`: the image lies in `B°`, is open (inverse function theorem),
and is relatively closed in `B°` because `f_t` fixes the sphere. By the change of variables formula
`V(t) = vol(B°)`. `V` is a polynomial, so `V(1) = vol(B°) > 0`; but `D f_1 = D g` is singular on
`B°` (otherwise `g` would map a neighbourhood onto a neighbourhood of a point of the sphere), so
`V(1) = 0`.
-/

namespace DPExtensions.SetValuedFixedPoints

open Polynomial MeasureTheory Metric Set Filter Topology Module

/-- For a continuous linear endomorphism `A` of a finite-dimensional real normed space `E`, the
function `s ↦ det (id + s • A)` is a polynomial of degree at most `dim E`. -/
theorem exists_polynomial_det_id_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    ∃ p : ℝ[X], p.natDegree ≤ finrank ℝ E ∧
      ∀ s : ℝ, p.eval s = (ContinuousLinearMap.id ℝ E + s • A).det := by
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C +
    (1 : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ).map C), ?_, fun s => ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · rw [← coe_evalRingHom, RingHom.map_det, ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [M, hij] <;> ring

/-- Lagrange interpolation under the integral. Let `φ x s` be, for every `x`, a polynomial in `s`
of degree at most `N`, integrable in `x` for every `s`. If `∫ φ x s dμ(x) = c` for all
`s ∈ (0, δ]`, then `∫ φ x r dμ(x) = c` for every `r`. -/
theorem integral_eq_of_polynomial_of_eq_on_Ioc {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {φ : X → ℝ → ℝ} {N : ℕ} (hpoly : ∀ x, ∃ p : ℝ[X], p.natDegree ≤ N ∧ ∀ s, p.eval s = φ x s)
    (hint : ∀ s, Integrable (fun x => φ x s) μ) {δ c : ℝ} (hδ : 0 < δ)
    (hc : ∀ s ∈ Ioc 0 δ, ∫ x, φ x s ∂μ = c) (r : ℝ) : ∫ x, φ x r ∂μ = c := by
  let v : ℕ → ℝ := fun j => δ / (j + 1)
  let S : Finset ℕ := Finset.range (N + 1)
  have hinj : Set.InjOn v S := by
    intro i _ j _ h
    have hi : (0 : ℝ) < i + 1 := by positivity
    have hj : (0 : ℝ) < j + 1 := by positivity
    simp only [v] at h
    rw [div_eq_div_iff hi.ne' hj.ne'] at h
    have : (j : ℝ) + 1 = i + 1 := mul_left_cancel₀ hδ.ne' h
    exact_mod_cast (by linarith : (i : ℝ) = j)
  have hv : ∀ j, v j ∈ Ioc 0 δ := by
    intro j
    have hj : (1 : ℝ) ≤ j + 1 := by have := j.cast_nonneg (α := ℝ); linarith
    exact ⟨by positivity, div_le_self hδ.le hj⟩
  have key : ∀ x, φ x r = ∑ j ∈ S, φ x (v j) * (Lagrange.basis S v j).eval r := by
    intro x
    obtain ⟨p, hpN, hp⟩ := hpoly x
    have hdeg : p.degree < S.card := by
      refine (degree_le_natDegree).trans_lt ?_
      simp only [S, Finset.card_range]
      exact_mod_cast Nat.lt_succ_of_le hpN
    rw [← hp r]
    conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
    simp [Lagrange.interpolate_apply, eval_finsetSum, hp]
  calc ∫ x, φ x r ∂μ = ∫ x, ∑ j ∈ S, φ x (v j) * (Lagrange.basis S v j).eval r ∂μ := by
        simp_rw [← key]
    _ = ∑ j ∈ S, (∫ x, φ x (v j) ∂μ) * (Lagrange.basis S v j).eval r := by
        rw [integral_finsetSum _ fun j _ => (hint (v j)).mul_const _]
        exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
    _ = c * (∑ j ∈ S, Lagrange.basis S v j).eval r := by
        simp [hc _ (hv _), eval_finsetSum, Finset.mul_sum]
    _ = c := by
        rw [Lagrange.sum_basis hinj ⟨0, by simp [S]⟩]
        simp

/-- A linear map `id + s • A` with `s ‖A‖ < 1` is injective, hence (in finite dimensions) has
nonzero determinant and full range. -/
theorem isUnit_id_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} {s : ℝ} (hs : 0 ≤ s) (hA : s * ‖A‖ < 1) :
    IsUnit ((ContinuousLinearMap.id ℝ E + s • A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv' : v = -(s • A v) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa using hv
  have h1 : ‖v‖ ≤ s * ‖A‖ * ‖v‖ := by
    calc ‖v‖ = ‖-(s • A v)‖ := by rw [← hv']
      _ = s * ‖A v‖ := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hs]
      _ ≤ s * (‖A‖ * ‖v‖) := mul_le_mul_of_nonneg_left (A.le_opNorm v) hs
      _ = s * ‖A‖ * ‖v‖ := by ring
  have h2 : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.1 h2

/-- **Rogers' lemma** (no C¹ retraction of the ball onto the sphere). Let `E` be a
finite-dimensional real normed space. There is no map `g : E → E` that is C¹ on an open set
`U ⊇ closedBall 0 1`, takes values of norm `1` on the closed unit ball, and fixes every point of
the unit sphere. -/
theorem no_C1_retraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} {U : Set E} (hU : IsOpen U)
    (hBU : closedBall (0 : E) 1 ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (hsph : ∀ x ∈ closedBall (0 : E) 1, ‖g x‖ = 1) (hid : ∀ x : E, ‖x‖ = 1 → g x = x) :
    False := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  set B := closedBall (0 : E) 1 with hB
  set Bo := ball (0 : E) 1 with hBo
  have hBoB : Bo ⊆ B := ball_subset_closedBall
  set g' := fderiv ℝ g
  have hstrict : ∀ x ∈ U, HasStrictFDerivAt g (g' x) x := fun x hx =>
    (hg.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt one_ne_zero
  have hg'c : ContinuousOn g' U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  set A : E → E →L[ℝ] E := fun x => g' x - ContinuousLinearMap.id ℝ E with hAdef
  have hAc : ContinuousOn A U := hg'c.sub continuousOn_const
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn (hAc.mono hBU)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 (mem_closedBall_self zero_le_one))
  -- `g − id` is `L`-Lipschitz on the open ball
  have hlip : ∀ x ∈ Bo, ∀ y ∈ Bo, ‖(g y - y) - (g x - x)‖ ≤ L * ‖y - x‖ := by
    intro x hx y hy
    refine (convex_ball (0 : E) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => g z - z) (f' := A) (fun z hz => ?_) (fun z hz => hL z (hBoB hz)) hx hy
    exact ((hstrict z (hBU (hBoB hz))).hasFDerivAt.sub (hasFDerivAt_id z)).hasFDerivWithinAt
  have hgc : ContinuousOn g B := hg.continuousOn.mono hBU
  set δ : ℝ := 1 / (L + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  -- the volume integral of the Jacobian of `x ↦ x + t (g x − x)`
  have hc : ∀ t ∈ Ioc 0 δ, ∫ x in Bo, (ContinuousLinearMap.id ℝ E + t • A x).det ∂μ
      = μ.real Bo := by
    rintro t ⟨ht0, htδ⟩
    have htL : t * L < 1 := by
      calc t * L ≤ δ * L := mul_le_mul_of_nonneg_right htδ hL0
        _ < 1 := by rw [hδ, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
    have ht1 : t < 1 := by
      calc t ≤ δ := htδ
        _ < 1 := by rw [hδ, div_lt_one (by linarith)]; linarith
    set F : E → E := fun x => x + t • (g x - x) with hFdef
    have hF' : ∀ x ∈ U, HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E + t • A x) x :=
      fun x hx => (hasStrictFDerivAt_id x).add
        (((hstrict x hx).sub (hasStrictFDerivAt_id x)).const_smul t)
    have hunit : ∀ x ∈ B, ∀ s ∈ Icc 0 t,
        IsUnit ((ContinuousLinearMap.id ℝ E + s • A x : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      rintro x hx s ⟨hs0, hst⟩
      refine isUnit_id_add_smul hs0 ?_
      calc s * ‖A x‖ ≤ t * L := mul_le_mul hst (hL x hx) (norm_nonneg _) ht0.le
        _ < 1 := htL
    have hdetpos : ∀ x ∈ B, 0 < (ContinuousLinearMap.id ℝ E + t • A x).det := by
      intro x hx
      by_contra hneg
      rw [not_lt] at hneg
      set φ : ℝ → ℝ := fun s => (ContinuousLinearMap.id ℝ E + s • A x).det
      have hφc : ContinuousOn φ (Icc 0 t) :=
        (ContinuousLinearMap.continuous_det.comp
          (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
      have hφ0 : φ 0 = 1 := by
        simp only [φ, zero_smul, add_zero, ContinuousLinearMap.det, ContinuousLinearMap.coe_id]
        exact LinearMap.det_id
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht0.le hφc
        ⟨hneg, by rw [hφ0]; exact zero_le_one⟩
      exact ((LinearMap.isUnit_iff_isUnit_det _).1 (hunit x hx s hs)).ne_zero hs0
    have hFB : ∀ x ∈ Bo, F x ∈ Bo := by
      intro x hx
      rw [hBo, mem_ball_zero_iff] at hx ⊢
      have hFx : F x = (1 - t) • x + t • g x := by
        simp only [hFdef, smul_sub, sub_smul, one_smul]
        abel
      rw [hFx]
      calc ‖(1 - t) • x + t • g x‖ ≤ ‖(1 - t) • x‖ + ‖t • g x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖g x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg ht0.le]
        _ < 1 := by
          rw [hsph x (hBoB (mem_ball_zero_iff.2 hx))]
          nlinarith
    have hFS : ∀ x ∈ B, x ∉ Bo → F x = x := by
      intro x hx hxo
      have hx1 : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.1 hx)
        (not_lt.1 fun h => hxo (mem_ball_zero_iff.2 h))
      simp [hFdef, hid x hx1]
    have hFcont : ContinuousOn F B := continuousOn_id.add (continuousOn_const.smul (hgc.sub
      continuousOn_id))
    have hopen : IsOpen (F '' Bo) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hsurj : (ContinuousLinearMap.id ℝ E + t • A x).range = ⊤ :=
        (LinearMap.isUnit_iff_range_eq_top _).1 (hunit x (hBoB hx) t ⟨ht0.le, le_rfl⟩)
      rw [← (hF' x (hBU (hBoB hx))).map_nhds_eq_of_surj hsurj]
      exact image_mem_map (isOpen_ball.mem_nhds hx)
    have hcpt : IsCompact (F '' B) := (isCompact_closedBall (0 : E) 1).image_of_continuousOn hFcont
    have himage : F '' Bo = Bo := by
      refine Subset.antisymm (image_subset_iff.2 hFB) ?_
      refine (convex_ball (0 : E) 1).isPreconnected.subset_left_of_subset_union hopen
        hcpt.isClosed.isOpen_compl
        (Set.disjoint_compl_right_iff_subset.2 (image_mono hBoB)) ?_ ?_
      · intro y hy
        by_cases h : y ∈ F '' B
        · left
          obtain ⟨x, hxB, rfl⟩ := h
          by_cases hxo : x ∈ Bo
          · exact ⟨x, hxo, rfl⟩
          · rw [hFS x hxB hxo] at hy
            exact absurd hy hxo
        · exact Or.inr h
      · exact ⟨F 0, hFB 0 (mem_ball_self one_pos), 0, mem_ball_self one_pos, rfl⟩
    have hinjF : InjOn F Bo := by
      intro x hx y hy hxy
      have h1 := hlip y hy x hx
      have h2 : x - y = t • ((g y - y) - (g x - x)) := by
        simp only [hFdef] at hxy
        rw [smul_sub]
        linear_combination (norm := module) hxy
      have h3 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
        calc ‖x - y‖ = t * ‖(g y - y) - (g x - x)‖ := by
              rw [h2, norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ t * (L * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact h1) ht0.le
          _ = t * L * ‖x - y‖ := by ring
      have h4 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h4)
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_ball
      (fun x hx => (hF' x (hBU (hBoB hx))).hasFDerivAt.hasFDerivWithinAt) hinjF
      (fun _ => (1 : ℝ))
    rw [himage] at hcov
    simp only [smul_eq_mul, mul_one, setIntegral_const, smul_eq_mul, mul_one] at hcov
    rw [hcov]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    exact (abs_of_pos (hdetpos x (hBoB hx))).symm
  have hint : ∀ s : ℝ,
      Integrable (fun x => (ContinuousLinearMap.id ℝ E + s • A x).det) (μ.restrict Bo) := by
    intro s
    refine IntegrableOn.mono_set ?_ hBoB
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add ((hAc.mono hBU).const_smul s))).integrableOn_compact
      (isCompact_closedBall 0 1)
  have h1 := integral_eq_of_polynomial_of_eq_on_Ioc (μ := μ.restrict Bo)
    (fun x => exists_polynomial_det_id_add_smul (A x)) hint hδ0 hc 1
  have hzero : ∀ x ∈ Bo, (ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x).det = 0 := by
    intro x hx
    have hxU : x ∈ U := hBU (hBoB hx)
    have hA1 : ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x = g' x := by
      simp [hAdef]
    rw [hA1]
    by_contra hdet
    have hsurj : (g' x).range = ⊤ :=
      (LinearMap.isUnit_iff_range_eq_top _).1
        ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet))
    have hmap := (hstrict x hxU).map_nhds_eq_of_surj hsurj
    have hmem : sphere (0 : E) 1 ∈ 𝓝 (g x) := by
      rw [← hmap, mem_map]
      refine mem_of_superset (isOpen_ball.mem_nhds hx) fun y hy => ?_
      simp [hsph y (hBoB hy)]
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hmem
    have hgx : ‖g x‖ = 1 := hsph x (hBoB hx)
    have hy : g x + (r / 2) • g x ∈ ball (g x) r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hgx, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have hy1 := hrs hy
    rw [mem_sphere_zero_iff_norm] at hy1
    have : ‖g x + (r / 2) • g x‖ = 1 + r / 2 := by
      rw [← one_smul ℝ (g x), smul_smul, mul_one, ← add_smul, norm_smul, hgx, mul_one,
        Real.norm_of_nonneg (by positivity)]
    linarith
  rw [setIntegral_congr_fun measurableSet_ball hzero, integral_zero] at h1
  have hpos : 0 < μ.real Bo :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

end DPExtensions.SetValuedFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Brouwer fixed-point theorem for the closed unit ball

SLP §17.3 (Theorem 17.3, p. 517) quotes the Brouwer fixed-point theorem without proof. This
module proves it for the closed unit ball of a finite-dimensional real inner product space, on top
of Rogers' lemma `no_C1_retraction` (no C¹ retraction of the ball onto the sphere).

* `C1Restrictions K`: the subalgebra of `C(K, ℝ)` of restrictions of C¹ functions `E → ℝ`.
* `exists_C1_approx_real` (Stone–Weierstrass): a real function continuous on a compact `K` is a
  uniform limit on `K` of C¹ functions.
* `exists_C1_approx`: the same for maps `K → E` with `E` finite-dimensional (approximate each
  coordinate in a basis).
* `brouwer_closedBall`: a map continuous on the closed unit ball of a finite-dimensional real inner
  product space and mapping it into itself has a fixed point.
* `brouwer_ball`: the special case `E = ℝⁿ = EuclideanSpace ℝ (Fin n)`.

Proof of `brouwer_closedBall`. If `f` had no fixed point on the ball `B`, then
`ε = min_B ‖f x − x‖ > 0`. A C¹ approximation `q₀` of `f` to within `η = ε/4`, rescaled to
`q = q₀/(1 + η)`, maps `B` into `B` and has no fixed point on `B`. With `u = x − q x`, the point
`g x = x + λ(x) u` where `λ(x) = (−⟨x, u⟩ + √D(x))/‖u‖²` and
`D(x) = ⟨x, u⟩² − ‖u‖²(‖x‖² − 1)` solves `‖g x‖ = 1`. On `B`, `‖u‖ > 0` and `D > 0` (in the
interior because `‖x‖ < 1`; on the sphere because `2⟨x, u⟩ = 1 − ‖q x‖² + ‖u‖² > 0`), so `g` is
C¹ on the open set `{‖u‖² > 0, D > 0} ⊇ B`; on the sphere `λ = 0` and `g x = x`. This contradicts
`no_C1_retraction`.
-/

namespace DPExtensions.SetValuedFixedPoints

open Metric Set Filter Topology Module
open scoped RealInnerProductSpace

/-- The subalgebra of `C(K, ℝ)` consisting of the restrictions to `K` of C¹ functions `E → ℝ`. -/
def C1Restrictions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) :
    Subalgebra ℝ C(K, ℝ) where
  carrier := {φ | ∃ F : E → ℝ, ContDiff ℝ 1 F ∧ ∀ x : K, φ x = F x}
  mul_mem' := by
    rintro φ ψ ⟨F, hF, hφ⟩ ⟨G, hG, hψ⟩
    exact ⟨fun x => F x * G x, hF.mul hG, fun x => by simp [hφ, hψ]⟩
  add_mem' := by
    rintro φ ψ ⟨F, hF, hφ⟩ ⟨G, hG, hψ⟩
    exact ⟨fun x => F x + G x, hF.add hG, fun x => by simp [hφ, hψ]⟩
  algebraMap_mem' r := ⟨fun _ => r, contDiff_const, fun x => by simp⟩

/-- **Stone–Weierstrass approximation by C¹ functions.** A real function continuous on a compact
subset `K` of a real normed space is uniformly approximable on `K` by C¹ functions. -/
theorem exists_C1_approx_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) {f : E → ℝ} (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : E → ℝ, ContDiff ℝ 1 F ∧ ∀ x ∈ K, |F x - f x| < ε := by
  have _ : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let φ : C(K, ℝ) := ⟨K.domRestrict f, hf.domRestrict⟩
  have hsep : (C1Restrictions K).SeparatesPoints := by
    intro x y hxy
    obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ)
      (Subtype.coe_injective.ne hxy)
    exact ⟨_, ⟨⟨fun z => ℓ z, ℓ.continuous.comp continuous_subtype_val⟩,
      ⟨ℓ, ℓ.contDiff, fun z => rfl⟩, rfl⟩, hℓ⟩
  have hdense := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hmem : φ ∈ closure (C1Restrictions K : Set C(K, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, hdense]
    trivial
  obtain ⟨ψ, ⟨F, hF, hψ⟩, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  refine ⟨F, hF, fun x hx => ?_⟩
  have h := (ContinuousMap.dist_apply_le_dist (f := φ) (g := ψ) ⟨x, hx⟩).trans_lt hdist
  rw [hψ] at h
  have h' : dist (f x) (F x) < ε := h
  rw [Real.dist_eq, abs_sub_comm] at h'
  exact h'

/-- **C¹ approximation of maps into a finite-dimensional space.** A map `f : E → E`, continuous on
a compact `K ⊆ E` with `E` finite-dimensional, is uniformly approximable on `K` by C¹ maps. -/
theorem exists_C1_approx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) {f : E → E} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) : ∃ F : E → E, ContDiff ℝ 1 F ∧ ∀ x ∈ K, ‖F x - f x‖ < ε := by
  let b := Module.finBasis ℝ E
  set Cb := ∑ i, ‖b i‖ with hCb
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun i _ => norm_nonneg _
  set η := ε / (Cb + 1) with hη
  have hη0 : 0 < η := by positivity
  have hcoord : ∀ i, ContinuousOn (fun x => b.repr (f x) i) K := fun i =>
    (b.coord i).continuous_of_finiteDimensional.comp_continuousOn hf
  choose F hF happrox using fun i => exists_C1_approx_real hK (hcoord i) hη0
  refine ⟨fun x => ∑ i, F i x • b i, ContDiff.sum fun i _ => (hF i).smul contDiff_const, ?_⟩
  intro x hx
  calc ‖∑ i, F i x • b i - f x‖ = ‖∑ i, (F i x - b.repr (f x) i) • b i‖ := by
        conv_lhs => rw [← b.sum_repr (f x)]
        rw [← Finset.sum_sub_distrib]
        simp only [sub_smul]
    _ ≤ ∑ i, |F i x - b.repr (f x) i| * ‖b i‖ :=
        norm_sum_le_of_le _ fun i _ => by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, η * ‖b i‖ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (happrox i x hx).le (norm_nonneg _)
    _ = η * Cb := by rw [hCb, Finset.mul_sum]
    _ < ε := by
        rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Brouwer fixed-point theorem for the closed unit ball** of a finite-dimensional real inner
product space: a map continuous on the closed unit ball and mapping it into itself has a fixed
point there. -/
theorem brouwer_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  by_contra hcon
  have hne : ∀ x ∈ closedBall (0 : E) 1, f x ≠ x := fun x hx h => hcon ⟨x, hx, h⟩
  set B := closedBall (0 : E) 1 with hB
  have hBc : IsCompact B := isCompact_closedBall 0 1
  obtain ⟨x0, hx0B, hx0min⟩ := hBc.exists_isMinOn (nonempty_closedBall.2 zero_le_one)
    ((hf.sub continuousOn_id).norm)
  set ε := ‖f x0 - x0‖ with hεdef
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hne x0 hx0B))
  have hεle : ∀ x ∈ B, ε ≤ ‖f x - x‖ := fun x hx => hx0min hx
  set η := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨q0, hq0, hq0approx⟩ := exists_C1_approx hBc hf hη0
  set q : E → E := fun x => (1 + η)⁻¹ • q0 x with hqdef
  have hqC : ContDiff ℝ 1 q := contDiff_const.smul hq0
  have hfB : ∀ x ∈ B, ‖f x‖ ≤ 1 := fun x hx => mem_closedBall_zero_iff.1 (hmaps hx)
  have hq0B : ∀ x ∈ B, ‖q0 x‖ ≤ 1 + η := by
    intro x hx
    calc ‖q0 x‖ = ‖(q0 x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖q0 x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ η + 1 := add_le_add (hq0approx x hx).le (hfB x hx)
      _ = 1 + η := add_comm _ _
  have hqB : ∀ x ∈ B, ‖q x‖ ≤ 1 := by
    intro x hx
    rw [hqdef, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity),
      mul_one]
    exact hq0B x hx
  have hqne : ∀ x ∈ B, q x ≠ x := by
    intro x hx hqx
    have h1 : q x - q0 x = (-(η / (1 + η))) • q0 x := by
      have h1η : (1 : ℝ) + η ≠ 0 := by positivity
      have hcoef : (-(η / (1 + η))) = (1 + η)⁻¹ - 1 := by field_simp; ring
      simp only [hqdef]
      rw [hcoef, sub_smul, one_smul]
    have h2 : ‖q x - q0 x‖ ≤ η := by
      rw [h1, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
      calc η / (1 + η) * ‖q0 x‖ ≤ η / (1 + η) * (1 + η) :=
            mul_le_mul_of_nonneg_left (hq0B x hx) (by positivity)
        _ = η := by field_simp
    have h3 : ‖f x - x‖ < ε := by
      calc ‖f x - x‖ = ‖-((q x - q0 x) + (q0 x - f x))‖ := by
            rw [hqx]
            congr 1
            abel
        _ ≤ ‖q x - q0 x‖ + ‖q0 x - f x‖ := by rw [norm_neg]; exact norm_add_le _ _
        _ < η + η := add_lt_add_of_le_of_lt h2 (hq0approx x hx)
        _ < ε := by linarith
    exact absurd (hεle x hx) (not_le.2 h3)
  -- the retraction
  set u : E → E := fun x => x - q x with hudef
  set a : E → ℝ := fun x => ⟪u x, u x⟫ with hadef
  set bb : E → ℝ := fun x => ⟪x, u x⟫ with hbbdef
  set c : E → ℝ := fun x => ⟪x, x⟫ - 1 with hcdef
  set D : E → ℝ := fun x => bb x ^ 2 - a x * c x with hDdef
  set lam : E → ℝ := fun x => (-bb x + Real.sqrt (D x)) / a x with hlamdef
  set g : E → E := fun x => x + lam x • u x with hgdef
  set U : Set E := {x | 0 < a x} ∩ {x | 0 < D x} with hUdef
  have huC : ContDiff ℝ 1 u := contDiff_id.sub hqC
  have haC : ContDiff ℝ 1 a := huC.inner ℝ huC
  have hbbC : ContDiff ℝ 1 bb := contDiff_id.inner ℝ huC
  have hcC : ContDiff ℝ 1 c := (contDiff_id.inner ℝ contDiff_id).sub contDiff_const
  have hDC : ContDiff ℝ 1 D := (hbbC.pow 2).sub (haC.mul hcC)
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const haC.continuous).inter (isOpen_lt continuous_const hDC.continuous)
  -- the identity `2 ⟨x, u⟩ = ‖x‖² − ‖q x‖² + ‖u‖²`
  have hrel : ∀ x, 2 * bb x = ‖x‖ ^ 2 - ‖q x‖ ^ 2 + a x := by
    intro x
    simp only [hbbdef, hadef, hudef, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm x (q x)]
    ring
  have haB : ∀ x ∈ B, 0 < a x := by
    intro x hx
    simp only [hadef, real_inner_self_eq_norm_sq]
    have : u x ≠ 0 := sub_ne_zero.2 (hqne x hx).symm
    positivity
  have hBU : B ⊆ U := by
    intro x hx
    refine ⟨haB x hx, ?_⟩
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hq1 := hqB x hx
    have ha := haB x hx
    have hr := hrel x
    have hcx : c x = ‖x‖ ^ 2 - 1 := by simp [hcdef]
    change 0 < bb x ^ 2 - a x * c x
    rw [hcx]
    rcases hx1.lt_or_eq with hlt | heq
    · have : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (bb x)]
    · rw [heq] at hr ⊢
      have : 0 < bb x := by nlinarith [norm_nonneg (q x)]
      nlinarith
  have hgC : ContDiffOn ℝ 1 g U := by
    intro x hx
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (D y)) x := hDC.contDiffAt.sqrt hx.2.ne'
    have hlam : ContDiffAt ℝ 1 lam x :=
      (hbbC.contDiffAt.neg.add hsq).div haC.contDiffAt hx.1.ne'
    exact (contDiffAt_id.add (hlam.smul huC.contDiffAt)).contDiffWithinAt
  have hsph : ∀ x ∈ B, ‖g x‖ = 1 := by
    intro x hx
    have ha := haB x hx
    have hD := (hBU hx).2
    set s := Real.sqrt (D x) with hs
    have hs2 : s ^ 2 = bb x ^ 2 - a x * c x := Real.sq_sqrt hD.le
    have h1 : lam x * a x = s - bb x := by
      simp only [hlamdef]
      field_simp
      ring
    have hinner : ⟪g x, g x⟫ = ⟪x, x⟫ + 2 * lam x * bb x + lam x ^ 2 * a x := by
      simp only [hgdef, hbbdef, hadef, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, real_inner_comm x (u x)]
      simp only [RCLike.conj_to_real]
      ring
    have hkey : a x * (2 * lam x * bb x + lam x ^ 2 * a x + c x) = 0 := by
      linear_combination (lam x * a x + s + bb x) * h1 + hs2
    have hkey' : 2 * lam x * bb x + lam x ^ 2 * a x + c x = 0 :=
      (mul_eq_zero.1 hkey).resolve_left ha.ne'
    have hgg : ⟪g x, g x⟫ = 1 := by
      rw [hinner]
      simp only [hcdef] at hkey'
      linarith
    rw [real_inner_self_eq_norm_sq] at hgg
    have := norm_nonneg (g x)
    nlinarith
  have hid : ∀ x : E, ‖x‖ = 1 → g x = x := by
    intro x hx1
    have hx : x ∈ B := mem_closedBall_zero_iff.2 hx1.le
    have hc0 : c x = 0 := by simp [hcdef, hx1]
    have hbb0 : 0 ≤ bb x := by
      have hr := hrel x
      have hq1 := hqB x hx
      rw [hx1] at hr
      nlinarith [norm_nonneg (q x), haB x hx]
    have hlam0 : lam x = 0 := by
      simp only [hlamdef, hDdef, hc0, mul_zero, sub_zero, Real.sqrt_sq hbb0, neg_add_cancel,
        zero_div]
    simp [hgdef, hlam0]
  exact no_C1_retraction hUo hBU hgC hsph hid

/-- **Brouwer fixed-point theorem for the closed unit ball of `ℝⁿ`.** Every map
`f : ℝⁿ → ℝⁿ` continuous on the closed unit ball and mapping it into itself has a fixed point in
the ball. -/
theorem brouwer_ball (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = x :=
  brouwer_closedBall hf hmaps

end DPExtensions.SetValuedFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Brouwer fixed-point theorem

SLP §17.3, Theorem 17.3 (p. 517), quoted in the book without proof: a continuous self-map of a
nonempty, closed, bounded, convex subset of a finite-dimensional normed space has a fixed point.
The ball case is `brouwer_closedBall`; this module reduces the general case to it.

* `exists_lipschitz_retraction`: a nonempty complete convex subset `K` of a real inner product
  space is a 1-Lipschitz retract of the whole space (nearest-point projection).
* `brouwer_inner`: Brouwer for compact convex `K` in a finite-dimensional real inner product space
  (extend `f` by `f ∘ P_K` and rescale `K` into the unit ball).
* `brouwer`: Brouwer for a nonempty compact convex `K` in any finite-dimensional
  real normed space (transport to Euclidean space along `toEuclidean`).
* `brouwer_subtype`: the same for a continuous self-map `f : K → K` of the subtype.
* `theorem_17_3` (**Theorem 17.3**, p. 517): the book's form, for `F` nonempty, closed, bounded
  and convex (compact by Heine–Borel in finite dimensions) and `T : F → F` continuous.
-/

namespace DPExtensions.SetValuedFixedPoints

open Metric Set Filter Topology Module
open scoped RealInnerProductSpace

/-- **Nearest-point retraction.** A nonempty complete convex subset `K` of a real inner product
space is a retract of the whole space by a 1-Lipschitz (in particular continuous) map. -/
theorem exists_lipschitz_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcpl : IsComplete K) (hconv : Convex ℝ K) :
    ∃ P : E → E, LipschitzWith 1 P ∧ (∀ x, P x ∈ K) ∧ ∀ x ∈ K, P x = x := by
  choose P hPK hPmin using exists_norm_eq_iInf_of_complete_convex hne hcpl hconv
  have hvar : ∀ x, ∀ w ∈ K, ⟪x - P x, w - P x⟫ ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hPK x)).1 (hPmin x)
  refine ⟨P, LipschitzWith.of_dist_le_mul fun x y => ?_, hPK, fun x hx => ?_⟩
  · rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have h1 := hvar x (P y) (hPK y)
    have h2 := hvar y (P x) (hPK x)
    have h3 : ‖P x - P y‖ ^ 2 ≤ ⟪x - y, P x - P y⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      have e1 : ⟪x - P x, P y - P x⟫ = ⟪x - y, P y - P x⟫ + ⟪y - P y, P y - P x⟫ +
          ⟪P y - P x, P y - P x⟫ := by
        rw [← inner_add_left, ← inner_add_left]
        congr 1
        abel
      have e2 : ⟪y - P y, P x - P y⟫ = -⟪y - P y, P y - P x⟫ := by
        rw [← inner_neg_right, neg_sub]
      have e3 : ⟪x - y, P x - P y⟫ = -⟪x - y, P y - P x⟫ := by
        rw [← inner_neg_right, neg_sub]
      have e4 : ⟪P x - P y, P x - P y⟫ = ⟪P y - P x, P y - P x⟫ := by
        rw [← inner_neg_neg, neg_sub]
      linarith
    have h4 : ⟪x - y, P x - P y⟫ ≤ ‖x - y‖ * ‖P x - P y‖ := real_inner_le_norm _ _
    nlinarith [norm_nonneg (P x - P y), norm_nonneg (x - y)]
  · have h := hvar x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- **Brouwer fixed-point theorem in a finite-dimensional real inner product space.** A map
continuous on a nonempty compact convex set `K` and mapping `K` into itself has a fixed point
in `K`. -/
theorem brouwer_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K) (hmaps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  obtain ⟨P, hPlip, hPK, hPid⟩ := exists_lipschitz_retraction hne hK.isComplete hconv
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall 0
  set R := max R0 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0' : 0 < R := by linarith
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx =>
    (mem_closedBall_zero_iff.1 (hR0 hx)).trans (le_max_left _ _)
  set h : E → E := fun y => R⁻¹ • f (P (R • y)) with hhdef
  have hcont : ContinuousOn h (closedBall 0 1) := by
    refine continuousOn_const.smul (hf.comp ?_ fun y _ => hPK _)
    exact (hPlip.continuous.comp (continuous_const.smul continuous_id)).continuousOn
  have hmapsB : MapsTo h (closedBall 0 1) (closedBall 0 1) := by
    intro y _
    rw [mem_closedBall_zero_iff, hhdef, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ hR0', mul_one]
    exact hKR _ (hmaps (hPK _))
  obtain ⟨y, -, hy⟩ := brouwer_closedBall hcont hmapsB
  have hfx : f (P (R • y)) = R • y := by
    have h1 := congrArg (fun z => R • z) hy
    simp only [hhdef, smul_smul, mul_inv_cancel₀ hR0'.ne', one_smul] at h1
    exact h1
  have hxK : R • y ∈ K := hfx ▸ hmaps (hPK _)
  refine ⟨R • y, hxK, ?_⟩
  calc f (R • y) = f (P (R • y)) := by rw [hPid _ hxK]
    _ = R • y := hfx

/-- **Brouwer fixed-point theorem.** Let `K` be a nonempty compact convex
subset of a finite-dimensional real normed space `E`, and `f` a map continuous on `K` with
`f(K) ⊆ K`. Then `f` has a fixed point in `K`. -/
theorem brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E}
    (hf : ContinuousOn f K) (hmaps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  set e := (toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))) with he
  set K' := e '' K with hK'
  set f' := fun y => e (f (e.symm y)) with hf'
  have hmapsK' : MapsTo e.symm K' K := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hK'c : IsCompact K' := hK.image e.continuous
  have hK'conv : Convex ℝ K' := by
    simpa [hK'] using hconv.linear_image e.toLinearEquiv.toLinearMap
  have hf'c : ContinuousOn f' K' :=
    e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn hmapsK')
  have hf'm : MapsTo f' K' K' := fun y hy => ⟨_, hmaps (hmapsK' hy), rfl⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := brouwer_inner hK'c hK'conv (hne.image e) hf'c hf'm
  refine ⟨x, hx, e.injective ?_⟩
  simpa [hf'] using hy

/-- **Brouwer fixed-point theorem, subtype form.** A continuous self-map of a nonempty compact
convex subset `K` of a finite-dimensional real normed space has a fixed point. -/
theorem brouwer_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : K → K} (hf : Continuous f) : ∃ x : K, f x = x := by
  classical
  set F : E → E := fun x => if h : x ∈ K then (f ⟨x, h⟩ : E) else x with hFdef
  have hFK : ∀ x : K, F x = f x := fun x => by simp [hFdef, x.2]
  have hFc : ContinuousOn F K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict F = fun x : K => (f x : E) := funext hFK
    rw [this]
    exact continuous_subtype_val.comp hf
  have hFm : MapsTo F K K := fun x hx => by
    rw [hFK ⟨x, hx⟩]
    exact (f _).2
  obtain ⟨x, hx, hFx⟩ := brouwer hK hconv hne hFc hFm
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hFK ⟨x, hx⟩]
  exact hFx

/-- **Theorem 17.3 (Brouwer fixed-point theorem)**, p. 517. Let `F` be a nonempty, closed,
bounded, convex subset of a finite-dimensional real normed space. Every continuous `T : F → F`
has a fixed point. -/
theorem theorem_17_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Set E} (hne : F.Nonempty) (hcl : IsClosed F)
    (hbdd : Bornology.IsBounded F) (hconv : Convex ℝ F) {T : F → F} (hT : Continuous T) :
    ∃ f : F, T f = f :=
  brouwer_subtype (Metric.isCompact_of_isClosed_isBounded hcl hbdd) hconv hne hT

end DPExtensions.SetValuedFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Schauder fixed-point theorem

SLP §17.4 (Theorem 17.4, p. 520) quotes a version of Schauder's theorem for spaces of bounded
continuous functions without proof. This module proves the general theorem for real normed
spaces, from the Brouwer theorem `brouwer`; the book's form is `theorem_17_4` in
`FixedPointArguments.SchauderBoundedContinuous`.

* `exists_approx_fixed_point`: a continuous self-map `f` of a compact convex set `K` has
  `ε`-approximate fixed points for every `ε > 0`. Take a finite `ε`-net `{y_i} ⊆ K`, the Schauder
  projection `P x = Σ μ_i(x) y_i / Σ μ_i(x)` with `μ_i(x) = max(0, ε − ‖x − y_i‖)` (continuous on
  `K`, into `conv{y_i}`, with `‖P x − x‖ ≤ ε`), and a Brouwer fixed point of `P ∘ f` on the compact
  convex set `conv{y_i}` inside the finite-dimensional span of the `y_i`.
* `schauder`: a continuous self-map of a nonempty compact convex subset of a real normed space has
  a fixed point (approximate fixed points plus compactness).
* `schauder_subtype`: the same for `f : K → K`.
* `schauder_closed`: in a real Banach space, a map `T` continuous on a nonempty closed convex set
  `F`, with `T(F) ⊆ F` and `T(F)` relatively compact, has a fixed point (apply `schauder` to the
  closed convex hull of `T(F)`, compact by Mazur's theorem `TotallyBounded.convexHull`).
* `schauder_closed_subtype`: the same for `T : F → F`.
-/

namespace DPExtensions.SetValuedFixedPoints

open Metric Set Filter Topology Module

/-- **Approximate fixed points.** A map `f` continuous on a compact convex set `K` of a real
normed space, with `f(K) ⊆ K`, has for every `ε > 0` a point `x ∈ K` with `‖f x − x‖ ≤ ε`. -/
theorem exists_approx_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E}
    (hf : ContinuousOn f K) (hmaps : MapsTo f K K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, ‖f x - x‖ ≤ ε := by
  classical
  obtain ⟨t, htK, htfin, hcov⟩ := finite_approx_of_totallyBounded hK.totallyBounded ε hε
  set s : Finset E := htfin.toFinset with hs
  have hsK : (s : Set E) ⊆ K := by simpa [hs] using htK
  have hcov' : ∀ x ∈ K, ∃ y ∈ s, ‖x - y‖ < ε := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hx)
    exact ⟨y, by simpa [hs] using hy, by rwa [mem_ball, dist_eq_norm] at hxy⟩
  -- the Schauder projection
  set μ : E → E → ℝ := fun y x => max 0 (ε - ‖x - y‖) with hμ
  have hμ0 : ∀ y x, 0 ≤ μ y x := fun y x => le_max_left _ _
  have hμc : ∀ y, Continuous (μ y) := fun y =>
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  set P : E → E := fun x => (∑ y ∈ s, μ y x)⁻¹ • ∑ y ∈ s, μ y x • y with hP
  have hsum : ∀ x ∈ K, 0 < ∑ y ∈ s, μ y x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcov' x hx
    refine Finset.sum_pos' (fun z _ => hμ0 z x) ⟨y, hy, ?_⟩
    exact lt_max_of_lt_right (by linarith)
  have hPc : ContinuousOn P K := by
    refine ContinuousOn.smul ?_ ?_
    · exact (continuous_finsetSum _ fun y _ => hμc y).continuousOn.inv₀
        fun x hx => (hsum x hx).ne'
    · exact (continuous_finsetSum _ fun y _ => (hμc y).smul continuous_const).continuousOn
  set C : Set E := convexHull ℝ (s : Set E) with hC
  have hPC : ∀ x ∈ K, P x ∈ C := fun x hx =>
    s.centerMass_mem_convexHull (fun y _ => hμ0 y x) (hsum x hx) fun y hy => hy
  have hPclose : ∀ x ∈ K, ‖P x - x‖ ≤ ε := by
    intro x hx
    have hS := hsum x hx
    have hPx : P x - x = (∑ y ∈ s, μ y x)⁻¹ • ∑ y ∈ s, μ y x • (y - x) := by
      simp only [hP, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      rw [smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
    rw [hPx, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS.le), inv_mul_le_iff₀ hS]
    calc ‖∑ y ∈ s, μ y x • (y - x)‖ ≤ ∑ y ∈ s, μ y x * ε := by
          refine norm_sum_le_of_le _ fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (hμ0 y x)]
          by_cases hxy : ‖x - y‖ ≤ ε
          · rw [norm_sub_rev]
            exact mul_le_mul_of_nonneg_left hxy (hμ0 y x)
          · have : μ y x = 0 := max_eq_left (by linarith)
            simp [this]
      _ = (∑ y ∈ s, μ y x) * ε := by rw [Finset.sum_mul]
  -- Brouwer inside the span of the net
  set V : Submodule ℝ E := Submodule.span ℝ (s : Set E) with hV
  have hCV : C ⊆ V := convexHull_min Submodule.subset_span V.convex
  have hPV : ∀ x, P x ∈ V := fun x =>
    V.smul_mem _ (V.sum_mem fun y hy => V.smul_mem _ (Submodule.subset_span hy))
  set C' : Set V := (Subtype.val : V → E) ⁻¹' C with hC'
  have hC'img : (Subtype.val : V → E) '' C' = C := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hCV hx⟩, hx, rfl⟩
  have hCK : C ⊆ K := convexHull_min hsK hconv
  have hC'c : IsCompact C' := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, hC'img]
    exact s.finite_toSet.isCompact_convexHull ℝ
  have hC'conv : Convex ℝ C' :=
    Convex.linear_preimage (𝕜 := ℝ) (convex_convexHull ℝ (s : Set E)) V.subtype
  have hsne : (s : Set E).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := hcov' x hx
    exact ⟨y, hy⟩
  have hC'ne : C'.Nonempty := by
    obtain ⟨y, hy⟩ := hsne
    exact ⟨⟨y, Submodule.subset_span hy⟩, subset_convexHull ℝ _ hy⟩
  set h : V → V := fun v => ⟨P (f v), hPV _⟩ with hh
  have hhc : ContinuousOn h C' := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine hPc.comp (hf.comp continuous_subtype_val.continuousOn fun v hv => hCK hv) ?_
    exact fun v hv => hmaps (hCK hv)
  have hhm : MapsTo h C' C' := fun v hv => hPC _ (hmaps (hCK hv))
  obtain ⟨v, hvC, hv⟩ := brouwer hC'c hC'conv hC'ne hhc hhm
  have hvK : (v : E) ∈ K := hCK hvC
  refine ⟨v, hvK, ?_⟩
  have hPv : P (f v) = v := congrArg Subtype.val hv
  calc ‖f v - v‖ = ‖P (f v) - f v‖ := by rw [hPv, norm_sub_rev]
    _ ≤ ε := hPclose _ (hmaps hvK)

/-- **Schauder fixed-point theorem.** A map continuous on a nonempty compact convex subset `K`
of a real normed space and mapping `K` into itself has a fixed point in `K`. -/
theorem schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E}
    (hf : ContinuousOn f K) (hmaps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  by_contra hcon
  have hne' : ∀ x ∈ K, f x ≠ x := fun x hx h => hcon ⟨x, hx, h⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne ((hf.sub continuousOn_id).norm)
  have hδ : 0 < ‖f x0 - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne' x0 hx0))
  obtain ⟨x, hx, hxε⟩ := exists_approx_fixed_point hK hconv hne hf hmaps (half_pos hδ)
  have : ‖f x0 - x0‖ ≤ ‖f x - x‖ := hmin hx
  linarith

/-- **Schauder fixed-point theorem, subtype form.** A continuous self-map of a nonempty compact
convex subset `K` of a real normed space has a fixed point. -/
theorem schauder_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : K → K} (hf : Continuous f) :
    ∃ x : K, f x = x := by
  classical
  set F : E → E := fun x => if h : x ∈ K then (f ⟨x, h⟩ : E) else x with hFdef
  have hFK : ∀ x : K, F x = f x := fun x => by simp [hFdef, x.2]
  have hFc : ContinuousOn F K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict F = fun x : K => (f x : E) := funext hFK
    rw [this]
    exact continuous_subtype_val.comp hf
  have hFm : MapsTo F K K := fun x hx => by
    rw [hFK ⟨x, hx⟩]
    exact (f _).2
  obtain ⟨x, hx, hFx⟩ := schauder hK hconv hne hFc hFm
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hFK ⟨x, hx⟩]
  exact hFx

/-- **Schauder fixed-point theorem, closed convex form.** In a real Banach space, let `F` be
nonempty, closed and convex, and `T` continuous on `F` with `T(F) ⊆ F` and `T(F)` relatively
compact. Then `T` has a fixed point in `F`. -/
theorem schauder_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Set E} (hcl : IsClosed F) (hconv : Convex ℝ F) (hne : F.Nonempty) {T : E → E}
    (hT : ContinuousOn T F) (hmaps : MapsTo T F F) (hcpt : IsCompact (closure (T '' F))) :
    ∃ x ∈ F, T x = x := by
  set K := closure (convexHull ℝ (T '' F)) with hKdef
  have hTB : TotallyBounded (T '' F) := hcpt.totallyBounded.subset subset_closure
  have hKc : IsCompact K := hTB.convexHull.closure.isCompact_of_isClosed isClosed_closure
  have hKF : K ⊆ F := closure_minimal (convexHull_min (image_subset_iff.2 hmaps) hconv) hcl
  have hKconv : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hKne : K.Nonempty := ((hne.image T).convexHull).closure
  have hKm : MapsTo T K K := fun x hx =>
    subset_closure (subset_convexHull ℝ _ (mem_image_of_mem T (hKF hx)))
  obtain ⟨x, hx, hTx⟩ := schauder hKc hKconv hKne (hT.mono hKF) hKm
  exact ⟨x, hKF hx, hTx⟩

/-- **Schauder fixed-point theorem, closed convex subtype form.** In a real Banach space, a
continuous self-map `T` of a nonempty closed convex set `F` whose range has compact closure has a
fixed point. -/
theorem schauder_closed_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : Set E} (hcl : IsClosed F) (hconv : Convex ℝ F) (hne : F.Nonempty)
    {T : F → F} (hT : Continuous T) (hcpt : IsCompact (closure (range fun x => (T x : E)))) :
    ∃ x : F, T x = x := by
  classical
  set G : E → E := fun x => if h : x ∈ F then (T ⟨x, h⟩ : E) else x with hGdef
  have hGF : ∀ x : F, G x = T x := fun x => by simp [hGdef, x.2]
  have hGc : ContinuousOn G F := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : F.domRestrict G = fun x : F => (T x : E) := funext hGF
    rw [this]
    exact continuous_subtype_val.comp hT
  have hGm : MapsTo G F F := fun x hx => by
    rw [hGF ⟨x, hx⟩]
    exact (T _).2
  have himg : G '' F = range fun x => (T x : E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hGF ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hGF x⟩
  obtain ⟨x, hx, hGx⟩ := schauder_closed hcl hconv hne hGc hGm (himg ▸ hcpt)
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hGF ⟨x, hx⟩]
  exact hGx

end DPExtensions.SetValuedFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Kakutani's fixed-point theorem in normed spaces

Kakutani (1941) proved that an upper hemicontinuous correspondence with nonempty convex values
from a simplex into itself has a fixed point; Bohnenblust and Karlin (1950) and Glicksberg (1952)
extended it beyond finite dimensions. This module proves the theorem for a nonempty compact convex
subset `K` of any real normed space, with the hypothesis in its closed-graph form: `F x` nonempty
and convex and inside `K` for `x ∈ K`, and the graph of `F` over `K` closed. It includes the
finite-dimensional theorem as the case `FiniteDimensional ℝ E`.

The proof reduces to Schauder's theorem `schauder` by approximate continuous selections (Cellina):

* `exists_approx_fixedPoint`: for every `ε > 0` there is `x ∈ K` lying in the convex hull of the
  values of `F` at points of `K` within `ε` of `x`. Take a finite `ε`-net `{cᵢ} ⊆ K`, a point
  `yᵢ ∈ F cᵢ`, the tent weights `wᵢ(x) = max(0, ε − ‖x − cᵢ‖)`, and the continuous map
  `g x = Σ wᵢ(x) yᵢ / Σ wᵢ(x)` of `K` into itself; a Schauder fixed point of `g` is the point.
* `exists_uhc`: a closed graph into a compact set makes `F` upper hemicontinuous, in the form
  `F x' ⊆ thickening δ (F a)` for `x'` near `a`.
* `kakutani`: approximate fixed points at `ε = 1/(n+1)` have a limit `a ∈ K`; for each `δ > 0`
  they eventually lie in the convex set `thickening δ (F a)`, so `a` lies in every
  `cthickening δ (F a)`, hence in the closed set `F a`.
-/

namespace DPExtensions.SetValuedFixedPoints

open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The graph of a correspondence `F` over a set `K`. -/
def graphOn (K : Set E) (F : E → Set E) : Set (E × E) := {p | p.1 ∈ K ∧ p.2 ∈ F p.1}

/-- The tent weight of the point `x` at the centre `c` with radius `ε`. -/
noncomputable def tent (ε : ℝ) (c x : E) : ℝ := max 0 (ε - ‖x - c‖)

omit [NormedSpace ℝ E] in
theorem tent_nonneg (ε : ℝ) (c x : E) : 0 ≤ tent ε c x := le_max_left _ _

omit [NormedSpace ℝ E] in
theorem tent_pos_iff {ε : ℝ} {c x : E} : 0 < tent ε c x ↔ dist x c < ε := by
  rw [tent, lt_max_iff, dist_eq_norm, sub_pos]
  exact ⟨fun h => h.resolve_left (lt_irrefl 0), Or.inr⟩

omit [NormedSpace ℝ E] in
theorem continuous_tent (ε : ℝ) (c : E) : Continuous (tent ε c) :=
  continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)

omit [NormedSpace ℝ E] in
/-- The values of a correspondence with a closed graph over `K` are closed at points of `K`. -/
theorem isClosed_apply_of_isClosed_graphOn {K : Set E} {F : E → Set E}
    (hgraph : IsClosed (graphOn K F)) {a : E} (ha : a ∈ K) : IsClosed (F a) := by
  have h : F a = (fun y => (a, y)) ⁻¹' graphOn K F := by
    ext y
    simp [graphOn, ha]
  rw [h]
  exact hgraph.preimage (continuous_const.prodMk continuous_id)

/-- **Approximate fixed points.** For every `ε > 0` some `x ∈ K` lies in the convex hull of the
values of `F` at points of `K` within `ε` of `x`. -/
theorem exists_approx_fixedPoint {K : Set E} {F : E → Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty)
    (hFK : ∀ x ∈ K, F x ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x ε, F x') := by
  classical
  obtain ⟨t, htK, htf, hcover⟩ := hK.finite_cover_balls hε
  set T := htf.toFinset with hT
  choose! y hy using hFne
  set g : E → E := fun x => T.centerMass (fun c => tent ε c x) y with hg
  have hsum : ∀ x ∈ K, 0 < ∑ c ∈ T, tent ε c x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover hx)
    exact Finset.sum_pos' (fun c _ => tent_nonneg ε c x)
      ⟨c, htf.mem_toFinset.2 hc, tent_pos_iff.2 (mem_ball.1 hxc)⟩
  have hgmem : ∀ x ∈ K, g x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x ε, F x') := by
    intro x hx
    have hfil : ∑ c ∈ T with tent ε c x ≠ 0, tent ε c x = ∑ c ∈ T, tent ε c x :=
      Finset.sum_filter_ne_zero T
    change T.centerMass (fun c => tent ε c x) y ∈ _
    rw [← Finset.centerMass_filter_ne_zero y]
    refine Finset.centerMass_mem_convexHull _ (fun c _ => tent_nonneg ε c x)
      (hfil ▸ hsum x hx) ?_
    intro c hc
    obtain ⟨hcT, hpos⟩ := Finset.mem_filter.1 hc
    have hcK : c ∈ K := htK (htf.mem_toFinset.1 hcT)
    refine mem_iUnion₂.2 ⟨c, ⟨hcK, ?_⟩, hy c hcK⟩
    rw [mem_ball, dist_comm]
    exact tent_pos_iff.1 (lt_of_le_of_ne (tent_nonneg ε c x) (Ne.symm hpos))
  have hgK : MapsTo g K K := fun x hx =>
    convexHull_min (iUnion₂_subset fun x' hx' => hFK x' hx'.1) hconv (hgmem x hx)
  have hgc : ContinuousOn g K := by
    have hs : ContinuousOn (fun x => ∑ c ∈ T, tent ε c x) K :=
      (continuous_finsetSum T fun c _ => continuous_tent ε c).continuousOn
    have hv : ContinuousOn (fun x => ∑ c ∈ T, tent ε c x • y c) K :=
      (continuous_finsetSum T fun c _ => (continuous_tent ε c).smul continuous_const).continuousOn
    exact (hs.inv₀ fun x hx => (hsum x hx).ne').smul hv
  obtain ⟨x, hx, hfx⟩ := schauder hK hconv hne hgc hgK
  have h := hgmem x hx
  rw [hfx] at h
  exact ⟨x, hx, h⟩

omit [NormedSpace ℝ E] in
/-- **A closed graph into a compact set is upper hemicontinuous**: for every `δ > 0`, the values
of `F` at points of `K` near `a` lie in the `δ`-thickening of `F a`. -/
theorem exists_uhc {K : Set E} {F : E → Set E} (hK : IsCompact K) (hFK : ∀ x ∈ K, F x ⊆ K)
    (hgraph : IsClosed (graphOn K F)) {a : E} (hFa : (F a).Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x' ∈ K, dist x' a < η → F x' ⊆ thickening δ (F a) := by
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ x' ∈ K, dist x' a < 1 / ((n : ℝ) + 1) ∧
      ∃ y ∈ F x', δ ≤ infDist y (F a) := by
    intro n
    by_contra hn
    refine hcon ⟨1 / ((n : ℝ) + 1), by positivity, fun x' hx' hd y hy => ?_⟩
    rw [mem_thickening_iff_infDist_lt hFa]
    by_contra hy'
    exact hn ⟨x', hx', hd, y, hy, not_lt.1 hy'⟩
  choose x' hx'K hx'd y hyF hyd using hseq
  obtain ⟨b, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n => hFK _ (hx'K n) (hyF n)
  have hxlim : Tendsto (x' ∘ φ) atTop (𝓝 a) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => (hx'd (φ n)).le) ?_)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hgr : (a, b) ∈ graphOn K F :=
    hgraph.mem_of_tendsto (hxlim.prodMk_nhds hlim)
      (Eventually.of_forall fun n => ⟨hx'K (φ n), hyF (φ n)⟩)
  have h1 : δ ≤ infDist b (F a) :=
    ge_of_tendsto (((continuous_infDist_pt (F a)).tendsto b).comp hlim)
      (Eventually.of_forall fun n => hyd (φ n))
  rw [infDist_zero_of_mem hgr.2] at h1
  linarith

/-- **Kakutani's fixed-point theorem** (Kakutani 1941; Bohnenblust–Karlin 1950; Glicksberg 1952).
Let `K` be a nonempty compact convex subset of a real normed space and `F` a correspondence with
nonempty convex values in `K` at points of `K` and a closed graph over `K`. Then `F` has a fixed
point: some `x ∈ K` with `x ∈ F x`. -/
theorem kakutani {K : Set E} {F : E → Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty) (hFconv : ∀ x ∈ K, Convex ℝ (F x))
    (hFK : ∀ x ∈ K, F x ⊆ K) (hgraph : IsClosed (graphOn K F)) : ∃ x ∈ K, x ∈ F x := by
  have happ : ∀ n : ℕ, ∃ x ∈ K,
      x ∈ convexHull ℝ (⋃ x' ∈ K ∩ ball x (1 / ((n : ℝ) + 1)), F x') :=
    fun n => exists_approx_fixedPoint hK hconv hne hFne hFK (by positivity)
  choose x hxK hxhull using happ
  obtain ⟨a, haK, φ, hφ, hlim⟩ := hK.tendsto_subseq hxK
  refine ⟨a, haK, ?_⟩
  rw [← (isClosed_apply_of_isClosed_graphOn hgraph haK).closure_eq,
    closure_eq_iInter_cthickening]
  refine mem_iInter₂.2 fun δ hδ => ?_
  obtain ⟨η, hη, huhc⟩ := exists_uhc hK hFK hgraph (hFne a haK) hδ
  have h1 : ∀ᶠ n in atTop, dist ((x ∘ φ) n) a < η / 2 :=
    Metric.tendsto_nhds.1 hlim (η / 2) (half_pos hη)
  have h2 : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < η / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually
      (gt_mem_nhds (half_pos hη))
  have hev : ∀ᶠ n in atTop, (x ∘ φ) n ∈ thickening δ (F a) := by
    filter_upwards [h1, h2] with n hn1 hn2
    refine convexHull_min ?_ ((hFconv a haK).thickening δ) (hxhull (φ n))
    refine iUnion₂_subset fun x' hx' => huhc x' hx'.1 ?_
    calc dist x' a ≤ dist x' (x (φ n)) + dist (x (φ n)) a := dist_triangle _ _ _
      _ < η / 2 + η / 2 := add_lt_add ((mem_ball.1 hx'.2).trans hn2) hn1
      _ = η := add_halves η
  exact closure_thickening_subset_cthickening δ _ (mem_closure_of_tendsto hlim hev)

/-- **Kakutani's theorem in `ℝⁿ`**, the form in which it is usually quoted. -/
theorem kakutani_euclidean {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hFne : ∀ x ∈ K, (F x).Nonempty)
    (hFconv : ∀ x ∈ K, Convex ℝ (F x)) (hFK : ∀ x ∈ K, F x ⊆ K)
    (hgraph : IsClosed (graphOn K F)) : ∃ x ∈ K, x ∈ F x :=
  kakutani hK hconv hne hFne hFconv hFK hgraph

end DPExtensions.SetValuedFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Schauder–Tychonoff fixed-point theorem

Tychonoff (1935) extended Schauder's theorem from normed spaces to locally convex spaces: a
continuous self-map of a nonempty compact convex subset `K` of a locally convex Hausdorff
topological vector space has a fixed point. This is the form used on spaces of measures with the
weak topology, which are not normable. The module proves it from the Brouwer theorem `brouwer`,
with gauges of convex neighbourhoods of zero in place of the norm of `schauder`.

* `exists_approx_fixedPoint_nhds`: in any real topological vector space, for every convex
  neighbourhood `U` of zero there is `x ∈ K` with `x − f x ∈ U`. Cover `K` by finitely many sets
  `{z | p (yᵢ − z) < 1}` with `yᵢ ∈ K`, where `p` is the gauge of `U` (continuous because `U` is a
  convex neighbourhood of zero). The weights `μᵢ(z) = max(0, 1 − p (yᵢ − z))` normalise to a
  continuous map from `K` into the standard simplex of `ℝ^{yᵢ}`, and composing with
  `λ ↦ Σ λᵢ yᵢ` and `f` gives a continuous self-map of the simplex. A Brouwer fixed point `λ`
  gives `x = Σ λᵢ yᵢ ∈ K` with `x − f x = Σ λᵢ (yᵢ − f x)`, a convex combination of points
  `yᵢ − f x` with `p (yᵢ − f x) < 1`, which lie in `U`.
* `schauderTychonoff`: in a locally convex Hausdorff space the closed sets
  `{x ∈ K | x − f x ∈ closure U}` have the finite intersection property (a finite intersection of
  convex neighbourhoods of zero is one), so by compactness some `x ∈ K` has `x − f x` in the
  closure of every convex neighbourhood of zero. Closed neighbourhoods of zero form a basis and
  convex ones lie inside each of them, so `x − f x = 0`.
* `schauderTychonoff_subtype`: the same for `f : K → K`.

The simplex is written out as a set rather than through Mathlib's `stdSimplex`, which is
deprecated in the pinned Mathlib.
-/

namespace DPExtensions.SetValuedFixedPoints

open Set Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Approximate fixed points in a topological vector space.** A map `f` continuous on a
nonempty compact convex subset `K` of a real topological vector space, with `f(K) ⊆ K`, has for
every convex neighbourhood `U` of zero a point `x ∈ K` with `x − f x ∈ U`. -/
theorem exists_approx_fixedPoint_nhds {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K) (hmaps : MapsTo f K K) {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (hUc : Convex ℝ U) : ∃ x ∈ K, x - f x ∈ U := by
  classical
  set p : E → ℝ := gauge U with hpdef
  have hp : Continuous p := continuous_gauge hUc hU
  have hpU : ∀ v, p v < 1 → v ∈ U := by
    intro v hv
    have hint : v ∈ interior U := by
      rw [← setOfPred_gauge_lt_one_eq_interior hUc hU]
      exact hv
    exact interior_subset hint
  -- a finite cover of `K` by gauge balls centred in `K`
  obtain ⟨s, hsK, hcov⟩ := hK.elim_nhds_subcover (fun y => {z | p (y - z) < 1}) fun y _ => by
    refine IsOpen.mem_nhds (isOpen_lt (hp.comp (continuous_const.sub continuous_id))
      continuous_const) ?_
    change p (y - y) < 1
    rw [sub_self, hpdef, gauge_zero]
    exact one_pos
  -- the weights
  set μ : E → E → ℝ := fun y z => max 0 (1 - p (y - z)) with hμ
  have hμ0 : ∀ y z, 0 ≤ μ y z := fun y z => le_max_left _ _
  have hμc : ∀ y, Continuous (μ y) := fun y =>
    continuous_const.max (continuous_const.sub (hp.comp (continuous_const.sub continuous_id)))
  have hμU : ∀ y z, 0 < μ y z → y - z ∈ U := by
    intro y z hyz
    rcases lt_max_iff.1 hyz with h | h
    · exact absurd h (lt_irrefl 0)
    · exact hpU _ (by linarith)
  have hsum : ∀ z ∈ K, 0 < ∑ i : s, μ i z := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov hz)
    refine Finset.sum_pos' (fun i _ => hμ0 i z) ⟨⟨y, hy⟩, Finset.mem_univ _, ?_⟩
    exact lt_max_of_lt_right (by simpa using hzy)
  -- the simplex on the cover and the maps through it
  set S : Set (s → ℝ) := {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1} with hS
  set L : (s → ℝ) → E := fun l => ∑ i : s, l i • (i : E) with hL
  have hLc : Continuous L :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hLK : MapsTo L S K := fun l hl =>
    hconv.sum_mem (fun i _ => hl.1 i) hl.2 fun i _ => hsK i i.2
  set w : E → (s → ℝ) := fun z i => μ i z / ∑ j : s, μ j z with hw
  have hwc : ContinuousOn w K := by
    refine continuousOn_pi.2 fun i => ?_
    exact (hμc i).continuousOn.div
      (continuous_finsetSum Finset.univ fun (j : s) _ => hμc (j : E)).continuousOn
      fun z hz => (hsum z hz).ne'
  have hwS : MapsTo w K S := by
    intro z hz
    refine ⟨fun i => div_nonneg (hμ0 i z) (hsum z hz).le, ?_⟩
    simp only [hw]
    rw [← Finset.sum_div, div_self (hsum z hz).ne']
  have hSc : IsCompact S := by
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ : s => (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))) ?_ ?_
    · rw [hS, ofPred_and, ofPred_forall]
      refine IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const
        (continuous_apply i)) (isClosed_eq ?_ continuous_const)
      exact continuous_finsetSum _ fun i _ => continuous_apply i
    · intro l hl i _
      refine ⟨hl.1 i, ?_⟩
      rw [← hl.2]
      exact Finset.single_le_sum (fun j _ => hl.1 j) (Finset.mem_univ i)
  have hSconv : Convex ℝ S := by
    intro l hl m hm a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hl.1 i)) (mul_nonneg hb (hm.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hl.2, hm.2, mul_one, hab]
  obtain ⟨z0, hz0⟩ := hne
  have hSne : S.Nonempty := ⟨w z0, hwS hz0⟩
  set h : (s → ℝ) → (s → ℝ) := fun l => w (f (L l)) with hh
  have hhc : ContinuousOn h S :=
    hwc.comp (hf.comp hLc.continuousOn hLK) fun l hl => hmaps (hLK hl)
  have hhm : MapsTo h S S := fun l hl => hwS (hmaps (hLK hl))
  obtain ⟨l, hl, hfix⟩ := brouwer hSc hSconv hSne hhc hhm
  -- the fixed point of the simplex map is an approximate fixed point of `f`
  set z := f (L l) with hz
  refine ⟨L l, hLK hl, ?_⟩
  have hpos : ∀ i, 0 < l i → (i : E) - z ∈ U := by
    intro i hi
    have hwi : 0 < w z i := by
      have := congrFun hfix i
      simp only [hh] at this
      rw [← hz] at this
      rw [this]
      exact hi
    exact hμU _ _ ((div_pos_iff_of_pos_right (hsum z (hmaps (hLK hl)))).1 hwi)
  have hdiff : L l - z = ∑ i : s, l i • ((i : E) - z) := by
    simp only [hL, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hl.2, one_smul]
  have h0U : (0 : E) ∈ U := mem_of_mem_nhds hU
  have hterm : ∀ i : s, l i • ((i : E) - z) = l i • (if 0 < l i then (i : E) - z else 0) := by
    intro i
    split_ifs with hi
    · rfl
    · rw [le_antisymm (not_lt.1 hi) (hl.1 i), zero_smul, zero_smul]
  rw [hdiff, Finset.sum_congr rfl fun i _ => hterm i]
  refine hUc.sum_mem (fun i _ => hl.1 i) hl.2 fun i _ => ?_
  split_ifs with hi
  · exact hpos i hi
  · exact h0U

/-- **Schauder–Tychonoff fixed-point theorem.** A map continuous on a nonempty compact convex
subset `K` of a real locally convex Hausdorff topological vector space and mapping `K` into
itself has a fixed point in `K`. -/
theorem schauderTychonoff [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K)
    (hmaps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  classical
  set ι := {U : Set E // U ∈ 𝓝 (0 : E) ∧ Convex ℝ U}
  set t : ι → Set E := fun U => K ∩ (fun x => x - f x) ⁻¹' closure U.1 with ht
  have htc : ∀ U, IsClosed (t U) := fun U =>
    (continuousOn_id.sub hf).preimage_isClosed_of_isClosed hK.isClosed isClosed_closure
  have hst : ∀ u : Finset ι, (K ∩ ⋂ U ∈ u, t U).Nonempty := by
    intro u
    set W : Set E := ⋂ U ∈ u, U.1 with hW
    have hWn : W ∈ 𝓝 (0 : E) := (Filter.biInter_finset_mem u).2 fun U _ => U.2.1
    have hWc : Convex ℝ W := convex_iInter₂ fun U _ => U.2.2
    obtain ⟨x, hx, hxW⟩ := exists_approx_fixedPoint_nhds hK hconv hne hf hmaps hWn hWc
    refine ⟨x, hx, mem_iInter₂.2 fun U hU => ⟨hx, ?_⟩⟩
    exact subset_closure (mem_iInter₂.1 hxW U hU)
  obtain ⟨x, hx, hxt⟩ := hK.inter_iInter_nonempty t htc hst
  refine ⟨x, hx, ?_⟩
  by_contra hne'
  have hv : x - f x ≠ 0 := sub_ne_zero.2 (Ne.symm hne')
  have hcompl : ({x - f x}ᶜ : Set E) ∈ 𝓝 (0 : E) :=
    isOpen_compl_singleton.mem_nhds (Ne.symm hv)
  obtain ⟨C, ⟨hCn, hCcl⟩, hCsub⟩ := (closed_nhds_basis (0 : E)).mem_iff.1 hcompl
  obtain ⟨U, ⟨hUn, hUc⟩, hUC⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hCn
  have hxU := (mem_iInter.1 hxt ⟨U, hUn, hUc⟩).2
  exact hCsub (closure_minimal hUC hCcl hxU) rfl

/-- **Schauder–Tychonoff fixed-point theorem, subtype form.** A continuous self-map of a
nonempty compact convex subset `K` of a real locally convex Hausdorff topological vector space
has a fixed point. -/
theorem schauderTychonoff_subtype [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) {f : K → K}
    (hf : Continuous f) : ∃ x : K, f x = x := by
  classical
  set F : E → E := fun x => if h : x ∈ K then (f ⟨x, h⟩ : E) else x with hFdef
  have hFK : ∀ x : K, F x = f x := fun x => by simp [hFdef, x.2]
  have hFc : ContinuousOn F K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict F = fun x : K => (f x : E) := funext hFK
    rw [this]
    exact continuous_subtype_val.comp hf
  have hFm : MapsTo F K K := fun x hx => by
    rw [hFK ⟨x, hx⟩]
    exact (f _).2
  obtain ⟨x, hx, hFx⟩ := schauderTychonoff hK hconv hne hFc hFm
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← hFK ⟨x, hx⟩]
  exact hFx

end DPExtensions.SetValuedFixedPoints

set_option linter.style.longLine false
#print axioms DPExtensions.SetValuedFixedPoints.exists_polynomial_det_id_add_smul
#print axioms DPExtensions.SetValuedFixedPoints.integral_eq_of_polynomial_of_eq_on_Ioc
#print axioms DPExtensions.SetValuedFixedPoints.isUnit_id_add_smul
#print axioms DPExtensions.SetValuedFixedPoints.no_C1_retraction
#print axioms DPExtensions.SetValuedFixedPoints.C1Restrictions
#print axioms DPExtensions.SetValuedFixedPoints.exists_C1_approx_real
#print axioms DPExtensions.SetValuedFixedPoints.exists_C1_approx
#print axioms DPExtensions.SetValuedFixedPoints.brouwer_closedBall
#print axioms DPExtensions.SetValuedFixedPoints.brouwer_ball
#print axioms DPExtensions.SetValuedFixedPoints.exists_lipschitz_retraction
#print axioms DPExtensions.SetValuedFixedPoints.brouwer_inner
#print axioms DPExtensions.SetValuedFixedPoints.brouwer
#print axioms DPExtensions.SetValuedFixedPoints.brouwer_subtype
#print axioms DPExtensions.SetValuedFixedPoints.theorem_17_3
#print axioms DPExtensions.SetValuedFixedPoints.exists_approx_fixed_point
#print axioms DPExtensions.SetValuedFixedPoints.schauder
#print axioms DPExtensions.SetValuedFixedPoints.schauder_subtype
#print axioms DPExtensions.SetValuedFixedPoints.schauder_closed
#print axioms DPExtensions.SetValuedFixedPoints.schauder_closed_subtype
#print axioms DPExtensions.SetValuedFixedPoints.graphOn
#print axioms DPExtensions.SetValuedFixedPoints.tent
#print axioms DPExtensions.SetValuedFixedPoints.tent_nonneg
#print axioms DPExtensions.SetValuedFixedPoints.tent_pos_iff
#print axioms DPExtensions.SetValuedFixedPoints.continuous_tent
#print axioms DPExtensions.SetValuedFixedPoints.isClosed_apply_of_isClosed_graphOn
#print axioms DPExtensions.SetValuedFixedPoints.exists_approx_fixedPoint
#print axioms DPExtensions.SetValuedFixedPoints.exists_uhc
#print axioms DPExtensions.SetValuedFixedPoints.kakutani
#print axioms DPExtensions.SetValuedFixedPoints.kakutani_euclidean
#print axioms DPExtensions.SetValuedFixedPoints.exists_approx_fixedPoint_nhds
#print axioms DPExtensions.SetValuedFixedPoints.schauderTychonoff
#print axioms DPExtensions.SetValuedFixedPoints.schauderTychonoff_subtype
