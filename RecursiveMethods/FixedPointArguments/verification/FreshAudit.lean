import Mathlib
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

namespace StokeyLucasPrescott.FixedPointArguments

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

end StokeyLucasPrescott.FixedPointArguments

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

namespace StokeyLucasPrescott.FixedPointArguments

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

end StokeyLucasPrescott.FixedPointArguments

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

namespace StokeyLucasPrescott.FixedPointArguments

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

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Applications of the Brouwer fixed-point theorem (SLP §17.3)

SLP §17.3, pp. 516–519, together with the parts of the overlapping-generations set-up of §17.1
(pp. 502–508) that Propositions 3 and 4 use. Brouwer's theorem itself is `theorem_17_3`
(`FixedPointArguments.Brouwer`).

**OLG primitives (§17.1).** `FPAssumption17_1` is **Assumption 17.1** (p. 503): `H : [0, L) → ℝ₊`
is `C²` (derivatives `H'`, `H''` taken within `[0, L)`, so one-sided at `0`), strictly increasing
and strictly convex with `H'(0) = 0` and `H'(l) → ∞` as `l → L`; `V : ℝ₊ → ℝ₊` is `C²`
(derivatives within `[0, ∞)`), strictly increasing and strictly concave. The names carry the
prefix `fp` to keep them apart from the §17.1 module.
* `fpZeta` `ζ(l) = l H'(l)` and `fpPhi` `φ(y) = y V'(y)` (p. 504); `fpZetaInv` is `ζ⁻¹`.
* `fpZeta_strictMonoOn`, `fpZeta_surjOn`, `fpZetaInv_strictMonoOn`, `fpZetaInv_continuousOn`
  (p. 507): `ζ` is a continuous increasing bijection `[0, L) → ℝ₊` and `ζ⁻¹ : ℝ₊ → [0, L)` is
  continuous and strictly increasing.
* `fp_bounds` (the bounds (7) of Proposition 2, used again in Propositions 3 and 4): for
  `X ⊆ [a, b] ⊂ ℝ₊₊` there are `0 < ε < B` with `0 ≤ φ(x′ζ⁻¹(y)) ≤ B` for all `y ≥ 0` and
  `ε < φ(x′ζ⁻¹(y))` for all `y ≥ ε`. The book takes `ε = ε_K = min {ε > 0 : ζ⁻¹(ε) = Kε}` with
  `K > 1/(aV′(bL))`; any `ε = ζ(l)` with `H′(l) < aV′(bL)` does the same job, which is what we use.

**§17.3.**
* `brouwer_finite_state` (p. 517): for a stochastic matrix `Π`, a nonempty closed bounded convex
  `D ⊆ ℝ` and `G(xᵢ, xⱼ, ·) : D → D` continuous, `(Tf)ᵢ = Σⱼ G(xᵢ, xⱼ, fⱼ) πᵢⱼ` has a fixed point
  in `Dᵐ`.
* `brouwer_log_transform_fixedPoint_iff`, `log_image_isCompact_convex`, `exp_image_log_image`
  (p. 518, "logarithms do not help"): for `D ⊆ ℝ₊₊`, `f` is a fixed point of `T` iff `ln f` is a
  fixed point of `T̂`, and `ln D` is compact and convex whenever `D` is (with `exp (ln D) = D`).
* `proposition_3` (**Proposition 3**, p. 518): with finitely many states `X ⊂ ℝ₊₊`, a stochastic
  matrix and Assumption 17.1, there is `f* ∈ ℝᵐ₊₊` with `f*ᵢ = Σⱼ φ[xⱼ ζ⁻¹(f*ⱼ)] πᵢⱼ`.
* `proposition_3_zero_fixedPoint` (p. 518 remark): `f ≡ 0` always solves the same system
  (`φ(0) = 0 = ζ⁻¹(0)`), which is why Proposition 3 must, and does, ask for a strictly positive
  solution.

No correction to the book is needed in §17.3: Proposition 3 is true as stated (the proof's
`F = [ε_K, B]ᵐ` excludes the trivial fixed point).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Set Filter Topology

/-! ### Assumption 17.1 and the functions `ζ`, `φ`, `ζ⁻¹` -/

/-- **Assumption 17.1** (p. 503). `H : [0, L) → ℝ₊` is twice continuously differentiable
(derivatives `H'`, `H''` within `[0, L)`), strictly increasing and strictly convex, with
`H'(0) = 0` and `H'(l) → +∞` as `l → L`; `V : ℝ₊ → ℝ₊` is twice continuously differentiable
(derivatives `V'`, `V''` within `[0, ∞)`), strictly increasing and strictly concave; and labour
lies in `[0, L)` with `0 < L < ∞`. -/
structure FPAssumption17_1 (L : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) : Prop where
  L_pos : 0 < L
  H_nonneg : ∀ l ∈ Ico 0 L, 0 ≤ H l
  H_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H (H' l) (Ico 0 L) l
  H'_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H' (H'' l) (Ico 0 L) l
  H''_cont : ContinuousOn H'' (Ico 0 L)
  H_mono : StrictMonoOn H (Ico 0 L)
  H_conv : StrictConvexOn ℝ (Ico 0 L) H
  H'_zero : H' 0 = 0
  H'_tendsto : Tendsto H' (𝓝[<] L) atTop
  V_nonneg : ∀ y, 0 ≤ y → 0 ≤ V y
  V_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V (V' y) (Ici 0) y
  V'_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V' (V'' y) (Ici 0) y
  V''_cont : ContinuousOn V'' (Ici 0)
  V_mono : StrictMonoOn V (Ici 0)
  V_conc : StrictConcaveOn ℝ (Ici 0) V

/-- `ζ(l) = l H'(l)` (p. 504). -/
def fpZeta (H' : ℝ → ℝ) (l : ℝ) : ℝ := l * H' l

/-- `φ(y) = y V'(y)` (p. 504). -/
def fpPhi (V' : ℝ → ℝ) (y : ℝ) : ℝ := y * V' y

/-- `ζ⁻¹ : ℝ₊ → [0, L)`, the inverse of `ζ` on `[0, L)` (p. 507). -/
noncomputable def fpZetaInv (L : ℝ) (H' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Function.invFunOn (fpZeta H') (Ico 0 L) y

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- `H'` is strictly increasing on `[0, L)` (strict convexity of `H`). -/
theorem fpA_H'_strictMonoOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictMonoOn H' (Ico 0 L) := fun _ hx _ hy hxy =>
  (hA.H_conv.lt_slope_of_hasDerivWithinAt hx hy hxy (hA.H_deriv _ hx)).trans
    (hA.H_conv.slope_lt_of_hasDerivWithinAt hx hy hxy (hA.H_deriv _ hy))

/-- `H'(l) > 0` for `0 < l < L`. -/
theorem fpA_H'_pos (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ioo 0 L) :
    0 < H' l := by
  have := fpA_H'_strictMonoOn hA (left_mem_Ico.2 hA.L_pos) (Ioo_subset_Ico_self hl) hl.1
  rwa [hA.H'_zero] at this

/-- `H' ≥ 0` on `[0, L)`. -/
theorem fpA_H'_nonneg (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ico 0 L) :
    0 ≤ H' l := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, hA.H'_zero]
  · exact (fpA_H'_pos hA ⟨h, hl.2⟩).le

/-- `H'` is continuous on `[0, L)`. -/
theorem fpA_H'_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn H' (Ico 0 L) := fun l hl => (hA.H'_deriv l hl).continuousWithinAt

/-- `V'(y) > 0` for `y ≥ 0`. -/
theorem fpA_V'_pos (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := hy
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h1 := hA.V_conc.slope_lt_of_hasDerivWithinAt hy' hy1 (by linarith) (hA.V_deriv y hy)
  have h2 : 0 < slope V y (y + 1) := by
    rw [slope_def_field]
    exact div_pos (sub_pos.2 (hA.V_mono hy' hy1 (by linarith))) (by linarith)
  linarith

/-- `V'` is strictly decreasing on `[0, ∞)` (strict concavity of `V`). -/
theorem fpA_V'_strictAntiOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictAntiOn V' (Ici 0) := fun _ hx _ hy hxy =>
  (hA.V_conc.slope_lt_of_hasDerivWithinAt hx hy hxy (hA.V_deriv _ hx)).trans'
    (hA.V_conc.lt_slope_of_hasDerivWithinAt hx hy hxy (hA.V_deriv _ hy))

/-- `V'` is continuous on `[0, ∞)`. -/
theorem fpA_V'_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn V' (Ici 0) := fun y hy => (hA.V'_deriv y hy).continuousWithinAt

/-- `ζ(0) = 0`. -/
theorem fpZeta_zero : fpZeta H' 0 = 0 := by simp [fpZeta]

/-- `ζ ≥ 0` on `[0, L)`. -/
theorem fpZeta_nonneg (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ico 0 L) :
    0 ≤ fpZeta H' l :=
  mul_nonneg hl.1 (fpA_H'_nonneg hA hl)

/-- `ζ` is strictly increasing on `[0, L)` (p. 505, step 1 of Proposition 1). -/
theorem fpZeta_strictMonoOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictMonoOn (fpZeta H') (Ico 0 L) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have h1 : H' l₁ < H' l₂ := fpA_H'_strictMonoOn hA hl₁ hl₂ hlt
  have h2 : 0 < H' l₂ := fpA_H'_pos hA ⟨hl₁.1.trans_lt hlt, hl₂.2⟩
  have h3 : l₁ * H' l₁ ≤ l₁ * H' l₂ := mul_le_mul_of_nonneg_left h1.le hl₁.1
  have h4 : l₁ * H' l₂ < l₂ * H' l₂ := mul_lt_mul_of_pos_right hlt h2
  simp only [fpZeta]
  linarith

/-- `ζ` is continuous on `[0, L)`. -/
theorem fpZeta_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn (fpZeta H') (Ico 0 L) :=
  continuousOn_id.mul (fpA_H'_continuousOn hA)

/-- `ζ` is unbounded on `[0, L)`: for every `y` some `l ∈ (0, L)` has `y < ζ(l)`. -/
theorem fpZeta_exists_gt (hA : FPAssumption17_1 L H H' H'' V V' V'') (y : ℝ) :
    ∃ l ∈ Ioo 0 L, y < fpZeta H' l := by
  have hL := hA.L_pos
  have h1 : ∀ᶠ l in 𝓝[<] L, 2 * |y| / L < H' l :=
    hA.H'_tendsto.eventually (eventually_gt_atTop _)
  have h2 : ∀ᶠ l in 𝓝[<] L, l ∈ Ioo (L / 2) L := Ioo_mem_nhdsLT (by linarith)
  obtain ⟨l, hl1, hl2⟩ := (h1.and h2).exists
  have hl0 : 0 < l := by linarith [hl2.1]
  refine ⟨l, ⟨hl0, hl2.2⟩, ?_⟩
  have hH : 0 < H' l := lt_of_le_of_lt (by positivity) hl1
  have e1 : L / 2 * H' l < l * H' l := mul_lt_mul_of_pos_right hl2.1 hH
  have e2 : L / 2 * (2 * |y| / L) ≤ L / 2 * H' l :=
    mul_le_mul_of_nonneg_left hl1.le (by linarith)
  have e3 : L / 2 * (2 * |y| / L) = |y| := by field_simp
  simp only [fpZeta]
  linarith [le_abs_self y]

/-- `ζ` maps `[0, L)` onto `ℝ₊` (p. 507). -/
theorem fpZeta_surjOn (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    ∃ l ∈ Ico 0 L, fpZeta H' l = y := by
  obtain ⟨l₁, hl₁, hgt⟩ := fpZeta_exists_gt hA y
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun z hz => ⟨hz.1, hz.2.trans_lt hl₁.2⟩
  have := intermediate_value_Icc hl₁.1.le ((fpZeta_continuousOn hA).mono hsub)
  obtain ⟨l, hl, hly⟩ := this ⟨by rw [fpZeta_zero]; exact hy, hgt.le⟩
  exact ⟨l, hsub hl, hly⟩

/-- `ζ⁻¹(y) ∈ [0, L)` for `y ≥ 0`. -/
theorem fpZetaInv_mem (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    fpZetaInv L H' y ∈ Ico 0 L := by
  obtain ⟨l, hl, hly⟩ := fpZeta_surjOn hA hy
  exact Function.invFunOn_mem ⟨l, hl, hly⟩

/-- `ζ(ζ⁻¹(y)) = y` for `y ≥ 0`. -/
theorem fpZeta_zetaInv (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    fpZeta H' (fpZetaInv L H' y) = y := by
  obtain ⟨l, hl, hly⟩ := fpZeta_surjOn hA hy
  exact Function.invFunOn_eq ⟨l, hl, hly⟩

/-- `ζ⁻¹(ζ(l)) = l` for `l ∈ [0, L)`. -/
theorem fpZetaInv_zeta (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ico 0 L) :
    fpZetaInv L H' (fpZeta H' l) = l :=
  (fpZeta_strictMonoOn hA).injOn (fpZetaInv_mem hA (fpZeta_nonneg hA hl)) hl
    (fpZeta_zetaInv hA (fpZeta_nonneg hA hl))

/-- `ζ⁻¹(0) = 0`. -/
theorem fpZetaInv_zero (hA : FPAssumption17_1 L H H' H'' V V' V'') : fpZetaInv L H' 0 = 0 := by
  have := fpZetaInv_zeta hA (left_mem_Ico.2 hA.L_pos)
  rwa [fpZeta_zero] at this

/-- `ζ⁻¹` is strictly increasing on `ℝ₊` (p. 507). -/
theorem fpZetaInv_strictMonoOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictMonoOn (fpZetaInv L H') (Ici 0) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  by_contra hle
  have := (fpZeta_strictMonoOn hA).monotoneOn (fpZetaInv_mem hA hy₂) (fpZetaInv_mem hA hy₁)
    (not_lt.1 hle)
  rw [fpZeta_zetaInv hA hy₁, fpZeta_zetaInv hA hy₂] at this
  linarith

/-- `ζ⁻¹` is continuous on `ℝ₊` (p. 507): extended by the identity on `(−∞, 0)` it is monotone
on `ℝ` with image the open set `(−∞, L)`. -/
theorem fpZetaInv_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn (fpZetaInv L H') (Ici 0) := by
  classical
  set ψ : ℝ → ℝ := fun y => if 0 ≤ y then fpZetaInv L H' y else y with hψ
  have hmono : MonotoneOn ψ univ := by
    intro y₁ _ y₂ _ hle
    simp only [hψ]
    by_cases h₁ : 0 ≤ y₁
    · have h₂ : 0 ≤ y₂ := h₁.trans hle
      simp only [h₁, h₂, ↓reduceIte]
      exact (fpZetaInv_strictMonoOn hA).monotoneOn h₁ h₂ hle
    · by_cases h₂ : 0 ≤ y₂
      · simp only [h₁, h₂, ↓reduceIte]
        exact (lt_of_not_ge h₁).le.trans (fpZetaInv_mem hA h₂).1
      · simp only [h₁, h₂, ↓reduceIte]
        exact hle
  have himg : ψ '' univ = Iio L := by
    ext z
    constructor
    · rintro ⟨y, -, rfl⟩
      simp only [hψ]
      by_cases h : 0 ≤ y
      · simp only [h, ↓reduceIte]
        exact (fpZetaInv_mem hA h).2
      · simp only [h, ↓reduceIte, mem_Iio]
        linarith [hA.L_pos, lt_of_not_ge h]
    · intro hz
      by_cases h : 0 ≤ z
      · refine ⟨fpZeta H' z, mem_univ _, ?_⟩
        have h0 : 0 ≤ fpZeta H' z := fpZeta_nonneg hA ⟨h, hz⟩
        simp only [hψ, h0, ↓reduceIte]
        exact fpZetaInv_zeta hA ⟨h, hz⟩
      · exact ⟨z, mem_univ _, by simp only [hψ, h, ↓reduceIte]⟩
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun y => by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono univ_mem ?_
    have hy : ψ y ∈ ψ '' univ := ⟨y, mem_univ _, rfl⟩
    rw [himg] at hy ⊢
    exact Iio_mem_nhds hy
  refine hcont.continuousOn.congr fun y hy => ?_
  have hy' : (0 : ℝ) ≤ y := hy
  simp only [hψ, hy', ↓reduceIte]

/-- `φ` is continuous on `ℝ₊`. -/
theorem fpPhi_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn (fpPhi V') (Ici 0) :=
  continuousOn_id.mul (fpA_V'_continuousOn hA)

/-- `φ(0) = 0`. -/
theorem fpPhi_zero : fpPhi V' 0 = 0 := by simp [fpPhi]

/-- `φ ≥ 0` on `ℝ₊`. -/
theorem fpPhi_nonneg (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ fpPhi V' y :=
  mul_nonneg hy (fpA_V'_pos hA hy).le

/-- `y ↦ φ(x′ ζ⁻¹(y))` is continuous on `ℝ₊` for `x′ ≥ 0`. -/
theorem fpPhi_comp_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') {x' : ℝ}
    (hx' : 0 ≤ x') : ContinuousOn (fun y => fpPhi V' (x' * fpZetaInv L H' y)) (Ici 0) :=
  (fpPhi_continuousOn hA).comp (continuousOn_const.mul (fpZetaInv_continuousOn hA))
    fun _ hy => mul_nonneg hx' (fpZetaInv_mem hA hy).1

/-- **The bounds of Propositions 2–4** ((7) on p. 514, (4)–(5) on p. 523). For states in
`[a, b] ⊂ ℝ₊₊` there are `0 < ε < B` with `0 ≤ φ(x′ζ⁻¹(y)) ≤ B` for all `y ≥ 0` and
`ε < φ(x′ζ⁻¹(y))` for all `y ≥ ε`. -/
theorem fp_bounds (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∃ ε > 0, ∃ B, ε < B ∧
      (∀ x' ∈ Icc a b, ∀ y, 0 ≤ y →
        0 ≤ fpPhi V' (x' * fpZetaInv L H' y) ∧ fpPhi V' (x' * fpZetaInv L H' y) ≤ B) ∧
      ∀ x' ∈ Icc a b, ∀ y, ε ≤ y → ε < fpPhi V' (x' * fpZetaInv L H' y) := by
  have hL := hA.L_pos
  have hb : 0 < b := ha.trans_le hab
  have hbL : 0 ≤ b * L := by positivity
  set c := a * V' (b * L) with hc
  have hc0 : 0 < c := mul_pos ha (fpA_V'_pos hA hbL)
  -- a small `l > 0` with `H'(l) < a V'(bL)`
  have hcw : ContinuousWithinAt H' (Ico 0 L) 0 :=
    fpA_H'_continuousOn hA 0 (left_mem_Ico.2 hL)
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico 0 L] 0 :=
    nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsGT hL) Ioo_subset_Ico_self)
  have hev : ∀ᶠ l in 𝓝[>] (0 : ℝ), H' l < c := by
    have := hcw.eventually (gt_mem_nhds (by rw [hA.H'_zero]; exact hc0))
    exact hle this
  obtain ⟨l, hl1, hl2⟩ := (hev.and (Ioo_mem_nhdsGT hL)).exists
  set ε := fpZeta H' l with hε
  have hε0 : 0 < ε := mul_pos hl2.1 (fpA_H'_pos hA hl2)
  -- the upper bound `B`
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hbL)
    ((fpPhi_continuousOn hA).mono fun z hz => hz.1)
  set B := fpPhi V' y₀ with hB
  have hup : ∀ x' ∈ Icc a b, ∀ y, 0 ≤ y →
      0 ≤ fpPhi V' (x' * fpZetaInv L H' y) ∧ fpPhi V' (x' * fpZetaInv L H' y) ≤ B := by
    intro x' hx' y hy
    have hn := fpZetaInv_mem hA hy
    have hx'0 : 0 ≤ x' := ha.le.trans hx'.1
    have hmem : x' * fpZetaInv L H' y ∈ Icc 0 (b * L) :=
      ⟨mul_nonneg hx'0 hn.1, mul_le_mul hx'.2 hn.2.le hn.1 hb.le⟩
    exact ⟨fpPhi_nonneg hA hmem.1, hmax hmem⟩
  have hlow : ∀ x' ∈ Icc a b, ∀ y, ε ≤ y → ε < fpPhi V' (x' * fpZetaInv L H' y) := by
    intro x' hx' y hy
    have hy0 : 0 ≤ y := hε0.le.trans hy
    have hn := fpZetaInv_mem hA hy0
    have hnl : l ≤ fpZetaInv L H' y := by
      have := (fpZetaInv_strictMonoOn hA).monotoneOn (mem_Ici.2 hε0.le) (mem_Ici.2 hy0) hy
      rwa [hε, fpZetaInv_zeta hA (Ioo_subset_Ico_self hl2)] at this
    have hx'0 : 0 ≤ x' := ha.le.trans hx'.1
    set n := fpZetaInv L H' y
    have hxn : a * l ≤ x' * n := mul_le_mul hx'.1 hnl hl2.1.le hx'0
    have hxnb : x' * n ≤ b * L := mul_le_mul hx'.2 hn.2.le hn.1 hb.le
    have hV : V' (b * L) ≤ V' (x' * n) :=
      (fpA_V'_strictAntiOn hA).antitoneOn (mem_Ici.2 (mul_nonneg hx'0 hn.1)) (mem_Ici.2 hbL)
        hxnb
    have hVpos : 0 < V' (b * L) := fpA_V'_pos hA hbL
    have h1 : a * l * V' (b * L) ≤ x' * n * V' (x' * n) :=
      mul_le_mul hxn hV hVpos.le (mul_nonneg hx'0 hn.1)
    have h2 : l * H' l < l * c := mul_lt_mul_of_pos_left hl1 hl2.1
    have h3 : a * l * V' (b * L) = l * c := by rw [hc]; ring
    simp only [fpPhi, hε, fpZeta]
    linarith
  refine ⟨ε, hε0, B, ?_, hup, hlow⟩
  have h1 := hlow a ⟨le_rfl, hab⟩ ε le_rfl
  have h2 := (hup a ⟨le_rfl, hab⟩ ε hε0.le).2
  linarith

/-! ### Brouwer for finite-state functional equations (p. 517) -/

/-- **Finite-state application of Brouwer** (p. 517). Let `Π = [πᵢⱼ]` be an `m × m` stochastic
matrix, `D ⊆ ℝ` nonempty, closed, bounded and convex, and `G(xᵢ, xⱼ, ·) : D → D` continuous.
Then `(Tf)ᵢ = Σⱼ G(xᵢ, xⱼ, fⱼ) πᵢⱼ` has a fixed point in `F = Dᵐ`. -/
theorem brouwer_finite_state {m : ℕ} (π : Fin m → Fin m → ℝ) (hπ0 : ∀ i j, 0 ≤ π i j)
    (hπ1 : ∀ i, ∑ j, π i j = 1) {D : Set ℝ} (hDne : D.Nonempty) (hDcl : IsClosed D)
    (hDb : Bornology.IsBounded D) (hDc : Convex ℝ D) (G : Fin m → Fin m → ℝ → ℝ)
    (hG : ∀ i j, ContinuousOn (G i j) D) (hGD : ∀ i j y, y ∈ D → G i j y ∈ D) :
    ∃ f : Fin m → ℝ, (∀ i, f i ∈ D) ∧ ∀ i, f i = ∑ j, G i j (f j) * π i j := by
  set K : Set (Fin m → ℝ) := univ.pi fun _ => D with hK
  set T : (Fin m → ℝ) → Fin m → ℝ := fun f i => ∑ j, G i j (f j) * π i j with hT
  have hKc : IsCompact K :=
    isCompact_univ_pi fun _ => Metric.isCompact_of_isClosed_isBounded hDcl hDb
  have hKconv : Convex ℝ K := convex_pi fun _ _ => hDc
  have hKne : K.Nonempty := by
    obtain ⟨d, hd⟩ := hDne
    exact ⟨fun _ => d, fun _ _ => hd⟩
  have hTc : ContinuousOn T K := by
    refine continuousOn_pi.2 fun i => ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact ((hG i j).comp (continuous_apply j).continuousOn
      fun f (hf : f ∈ K) => hf j (mem_univ j)).mul
      continuousOn_const
  have hTm : MapsTo T K K := by
    intro f hf i _
    have := hDc.sum_mem (t := Finset.univ) (w := fun j => π i j) (z := fun j => G i j (f j))
      (fun j _ => hπ0 i j) (hπ1 i) fun j _ => hGD i j _ (hf j (mem_univ j))
    simpa only [hT, smul_eq_mul, mul_comm] using this
  obtain ⟨f, hf, hTf⟩ := brouwer hKc hKconv hKne hTc hTm
  exact ⟨f, fun i => hf i (mem_univ i), fun i => (congrFun hTf i).symm⟩

/-- **Logarithms do not help with Brouwer** (p. 518), fixed points. For `D ⊆ ℝ₊₊` convex and
`G(xᵢ, xⱼ, ·) : D → D`, a vector `f ∈ Dᵐ` is a fixed point of `T` iff `g = ln f` is a fixed
point of `(T̂g)ᵢ = ln Σⱼ G(xᵢ, xⱼ, e^{gⱼ}) πᵢⱼ`. -/
theorem brouwer_log_transform_fixedPoint_iff {m : ℕ} (π : Fin m → Fin m → ℝ)
    (hπ0 : ∀ i j, 0 ≤ π i j) (hπ1 : ∀ i, ∑ j, π i j = 1) {D : Set ℝ} (hDpos : D ⊆ Ioi 0)
    (hDc : Convex ℝ D) (G : Fin m → Fin m → ℝ → ℝ) (hGD : ∀ i j y, y ∈ D → G i j y ∈ D)
    {f : Fin m → ℝ} (hf : ∀ j, f j ∈ D) :
    (∀ i, f i = ∑ j, G i j (f j) * π i j) ↔
      ∀ i, Real.log (f i) = Real.log (∑ j, G i j (Real.exp (Real.log (f j))) * π i j) := by
  have hexp : ∀ j, Real.exp (Real.log (f j)) = f j := fun j => Real.exp_log (hDpos (hf j))
  simp only [hexp]
  have hTpos : ∀ i, (0 : ℝ) < ∑ j, G i j (f j) * π i j := by
    intro i
    have := hDc.sum_mem (t := Finset.univ) (w := fun j => π i j) (z := fun j => G i j (f j))
      (fun j _ => hπ0 i j) (hπ1 i) fun j _ => hGD i j _ (hf j)
    have h2 : 0 < ∑ j, π i j • G i j (f j) := hDpos this
    simpa only [smul_eq_mul, mul_comm] using h2
  refine forall_congr' fun i => ⟨fun h => by rw [← h], fun h => ?_⟩
  exact Real.log_injOn_pos (hDpos (hf i)) (hTpos i) h

/-- **Logarithms do not help with Brouwer** (p. 518), sets. If `D ⊆ ℝ₊₊` is compact and convex,
so is `D̂ = ln D`. -/
theorem log_image_isCompact_convex {D : Set ℝ} (hDpos : D ⊆ Ioi 0) (hDk : IsCompact D)
    (hDc : Convex ℝ D) : IsCompact (Real.log '' D) ∧ Convex ℝ (Real.log '' D) := by
  have hlog : ContinuousOn Real.log D :=
    Real.continuousOn_log.mono fun y hy => (ne_of_gt (hDpos hy))
  refine ⟨hDk.image_of_continuousOn hlog, ?_⟩
  rw [convex_iff_ordConnected, ← isPreconnected_iff_ordConnected]
  exact (isPreconnected_iff_ordConnected.2 (convex_iff_ordConnected.1 hDc)).image _ hlog

/-- `exp` maps `ln D` back onto `D` for `D ⊆ ℝ₊₊`, so `F` and `F̂` determine each other. -/
theorem exp_image_log_image {D : Set ℝ} (hDpos : D ⊆ Ioi 0) :
    Real.exp '' (Real.log '' D) = D := by
  rw [image_image]
  conv_rhs => rw [← image_id D]
  exact image_congr fun y hy => Real.exp_log (hDpos hy)

/-! ### Proposition 3 -/

/-- Finitely many strictly positive states lie in some `[a, b] ⊂ ℝ₊₊`. -/
theorem fp_finite_states_bounds {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 < x i) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ i, x i ∈ Icc a b := by
  classical
  set s : Finset ℝ := insert 1 (Finset.univ.image x) with hs
  have hne : s.Nonempty := Finset.insert_nonempty _ _
  have hmem : ∀ i, x i ∈ s := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem x (Finset.mem_univ i))
  refine ⟨s.min' hne, s.max' hne, ?_, Finset.min'_le _ _ (Finset.max'_mem _ _),
    fun i => ⟨Finset.min'_le _ _ (hmem i), Finset.le_max' _ _ (hmem i)⟩⟩
  have h := Finset.min'_mem s hne
  rcases Finset.mem_insert.1 h with h | h
  · rw [h]; exact one_pos
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
  rw [← hi]; exact hx i

/-- **Proposition 3** (p. 518). Let `X = {x₁, …, x_m} ⊂ ℝ₊₊`, `Π = [πᵢⱼ]` a stochastic matrix and
`H`, `V` satisfy Assumption 17.1. Then some strictly positive `f* ∈ ℝᵐ₊₊` satisfies
`f*ᵢ = Σⱼ φ[xⱼ ζ⁻¹(f*ⱼ)] πᵢⱼ` for all `i`. -/
theorem proposition_3 (hA : FPAssumption17_1 L H H' H'' V V' V'') {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (π : Fin m → Fin m → ℝ) (hπ0 : ∀ i j, 0 ≤ π i j)
    (hπ1 : ∀ i, ∑ j, π i j = 1) :
    ∃ f : Fin m → ℝ, (∀ i, 0 < f i) ∧
      ∀ i, f i = ∑ j, fpPhi V' (x j * fpZetaInv L H' (f j)) * π i j := by
  obtain ⟨a, b, ha, hab, hxab⟩ := fp_finite_states_bounds x hx
  obtain ⟨ε, hε, B, hεB, hup, hlow⟩ := fp_bounds hA ha hab
  have hGc : ∀ (_ : Fin m) (j : Fin m),
      ContinuousOn (fun y => fpPhi V' (x j * fpZetaInv L H' y)) (Icc ε B) :=
    fun _ j => (fpPhi_comp_continuousOn hA (hx j).le).mono fun y hy => hε.le.trans hy.1
  have hGD : ∀ (i j : Fin m) y, y ∈ Icc ε B → fpPhi V' (x j * fpZetaInv L H' y) ∈ Icc ε B :=
    fun _ j y hy => ⟨(hlow (x j) (hxab j) y hy.1).le, (hup (x j) (hxab j) y
      (hε.le.trans hy.1)).2⟩
  obtain ⟨f, hfD, hf⟩ := brouwer_finite_state π hπ0 hπ1 (nonempty_Icc.2 hεB.le) isClosed_Icc
    (Metric.isBounded_Icc ε B) (convex_Icc ε B)
    (fun (_ : Fin m) (j : Fin m) (y : ℝ) => fpPhi V' (x j * fpZetaInv L H' y))
    hGc hGD
  exact ⟨f, fun i => hε.trans_le (hfD i).1, hf⟩

/-- **The trivial solution** (p. 518 remark). Under Assumption 17.1 the zero vector solves the
system of Proposition 3, since `ζ⁻¹(0) = 0` and `φ(0) = 0`; Proposition 3 is about strictly
positive solutions. -/
theorem proposition_3_zero_fixedPoint (hA : FPAssumption17_1 L H H' H'' V V' V'') {m : ℕ}
    (x : Fin m → ℝ) (π : Fin m → Fin m → ℝ) (i : Fin m) :
    (0 : ℝ) = ∑ j, fpPhi V' (x j * fpZetaInv L H' 0) * π i j := by
  simp [fpZetaInv_zero hA, fpPhi_zero]

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fixed points of monotone operators: Lemma 17.6, Theorem 17.7 and its Corollary

SLP §17.5, pp. 525–529. `C(X)` is the space of bounded continuous functions on `X` with the sup
norm, Mathlib's `X →ᵇ ℝ`, ordered pointwise. In the book `X ⊆ ℝˡ` is bounded; the only property
of `X` the proofs use is that it is totally bounded, so the results are stated for a pseudometric
space `X` with `TotallyBounded (univ : Set X)`. `totallyBounded_univ_of_isBounded` supplies this
for a bounded subset of `ℝˡ` (or of any proper space), seen as a subtype.

The book's equicontinuity of a family (p. 520: one `δ` for all `x, x'` and all members) is
Mathlib's `UniformEquicontinuous`; "`T(F)` is equicontinuous" is
`UniformEquicontinuous fun f : F => ⇑(T f)`. The operator is a map `T : C(X) → C(X)` with
`MapsTo T F F` and `ContinuousOn T F`; its values off `F` play no role.

* `isMonotoneOperator` (definition, p. 528) and `isMonotoneOperator_iff_monotoneOn`.
* `cauchySeq_of_uniformEquicontinuous`: on a totally bounded space a uniformly equicontinuous,
  pointwise Cauchy sequence in `C(X)` is Cauchy in the sup norm (the core of the proof of
  Lemma 17.6).
* **Lemma 17.6** (`lemma_17_6`, p. 526): `F` closed, `T : F → F` continuous, `T(F)`
  equicontinuous; if `Tⁿf₀` converges pointwise, it converges in the sup norm to a fixed point
  of `T` in `F`.
* **Theorem 17.7** (`theorem_17_7`, p. 528), with the two one-sided versions
  `theorem_17_7_of_le` (`f₀ ≤ Tf₀`, increasing iterates) and `theorem_17_7_of_ge`
  (`Tf₀ ≤ f₀`, decreasing iterates): `F` closed and bounded, `T` continuous and monotone on `F`,
  `T(F)` equicontinuous. Then `Tⁿf₀` converges in `C(X)` to a fixed point in `F`.
* **Corollary** (p. 529): `corollary_17_7_least` (iterating from a least element of `F` gives
  the least fixed point), `corollary_17_7_greatest` (from a greatest element, the greatest),
  `corollary_17_7` (every fixed point `h ∈ F` satisfies `f ≤ h ≤ g`) and
  `corollary_17_7_unique` (if the two limits coincide, it is the only fixed point in `F`).
* `theorem_17_7_of_isBounded`: Theorem 17.7 for a bounded `X ⊆ E`, `E` proper (e.g. `ℝˡ`).

**Remark (p. 528).** Theorem 17.7 is not Tarski's theorem: `F` need not be a complete lattice.
It is a monotone-iteration theorem: monotone bounded real sequences converge, and Lemma 17.6
turns pointwise convergence into convergence in `C(X)`. No convexity is used.

**Correction (proof of Lemma 17.6, (4), (8b), (9), p. 527; trivial).** Letting `Δ → 0` in
`|f(x') − f(x)| < ε + Δ` gives `≤ ε`, not `< ε`, so (9) is `≤ 3ε`. The proof here organises the
book's argument as a Cauchy estimate: `|fₙ(x) − fₘ(x)| ≤ |fₙ(x) − fₙ(xᵢ)| + |fₙ(xᵢ) − fₘ(xᵢ)| +
|fₘ(xᵢ) − fₘ(x)|` for a point `xᵢ` of a finite `δ`-net, which avoids step 1 (uniform continuity of
the limit) altogether; the limit exists because `C(X)` is complete.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Filter Topology Set BoundedContinuousFunction

variable {X : Type*} [PseudoMetricSpace X]

/-- The order on `C(X)` is pointwise: `f ≤ g` iff `f x ≤ g x` for all `x` (p. 528). -/
theorem bcf_le_iff {f g : X →ᵇ ℝ} : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl

/-- SLP p. 528: `T : F → F` is a *monotone operator* if `f, g ∈ F` and `f ≥ g` imply `Tf ≥ Tg`,
where `f ≥ g` means `f(x) ≥ g(x)` for all `x`. -/
def isMonotoneOperator (F : Set (X →ᵇ ℝ)) (T : (X →ᵇ ℝ) → (X →ᵇ ℝ)) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F, (∀ x, g x ≤ f x) → ∀ x, (T g) x ≤ (T f) x

/-- The book's monotone operators are Mathlib's `MonotoneOn T F` for the pointwise order. -/
theorem isMonotoneOperator_iff_monotoneOn {F : Set (X →ᵇ ℝ)} {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)} :
    isMonotoneOperator F T ↔ MonotoneOn T F :=
  ⟨fun h _ hg _ hf hgf => h _ hf _ hg hgf, fun h _ hf _ hg hgf => h hg hf hgf⟩

/-- On a totally bounded space, a uniformly equicontinuous sequence in `C(X)` that is Cauchy at
every point is Cauchy in the sup norm. This is the heart of the proof of Lemma 17.6, steps 1–2:
a finite `δ`-net reduces uniform estimates to finitely many points. -/
theorem cauchySeq_of_uniformEquicontinuous (hX : TotallyBounded (univ : Set X))
    {u : ℕ → X →ᵇ ℝ} (hequi : UniformEquicontinuous fun n => ⇑(u n))
    (hpt : ∀ x, CauchySeq fun n => u n x) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformEquicontinuous_iff.1 hequi (ε / 4) (by positivity)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hX δ hδ
  have hN : ∀ y ∈ t, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m y) (u n y) < ε / 4 :=
    fun y _ => Metric.cauchySeq_iff.1 (hpt y) _ (by positivity)
  choose! N hN using hN
  refine ⟨ht.toFinset.sup N, fun m hm n hn => ?_⟩
  have key : dist (u m) (u n) ≤ 3 * (ε / 4) := by
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ Metric.ball y δ := by
      simpa using hcover (mem_univ x)
    have hNy : N y ≤ ht.toFinset.sup N := Finset.le_sup (ht.mem_toFinset.2 hy)
    have hxy' : dist x y < δ := hxy
    have h1 := hu x y hxy' m
    have h2 := hN y hy m (le_trans hNy hm) n (le_trans hNy hn)
    have h3 := hu x y hxy' n
    calc dist (u m x) (u n x)
        ≤ dist (u m x) (u m y) + dist (u m y) (u n y) + dist (u n y) (u n x) :=
          dist_triangle4 _ _ _ _
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by
          rw [dist_comm (u n y)]
          gcongr
      _ = 3 * (ε / 4) := by ring
  linarith

/-- **Lemma 17.6** (SLP p. 526). Let `X` be totally bounded (e.g. a bounded subset of `ℝˡ`),
`F ⊆ C(X)` closed, `T : F → F` continuous with `T(F)` an equicontinuous family. If for some
`f₀ ∈ F` the sequence `Tⁿf₀` converges pointwise, then it converges in the sup norm to some
`f ∈ F`, and `f` is a fixed point of `T`. (No boundedness or convexity of `F` is needed.) -/
theorem lemma_17_6 (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)} (hF : IsClosed F)
    {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)} (hT : MapsTo T F F) (hTc : ContinuousOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (hpt : ∀ x, ∃ c, Tendsto (fun n => (T^[n] f₀) x) atTop (𝓝 c)) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := by
  have hmem : ∀ n, T^[n] f₀ ∈ F := fun n => hT.iterate n hf₀
  set u : ℕ → X →ᵇ ℝ := fun n => T^[n + 1] f₀ with hu_def
  have hu : ∀ n, u n = T (T^[n] f₀) := fun n => Function.iterate_succ_apply' T n f₀
  have hequi' : UniformEquicontinuous fun n => ⇑(u n) := by
    have := hequi.comp fun n => (⟨T^[n] f₀, hmem n⟩ : F)
    convert this using 2 with n
    simp [hu n]
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_uniformEquicontinuous hX hequi' fun x => ?_
    obtain ⟨c, hc⟩ := hpt x
    exact ((tendsto_add_atTop_iff_nat 1).2 hc).cauchySeq
  obtain ⟨f, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim' : Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := (tendsto_add_atTop_iff_nat 1).1 hlim
  have hfF : f ∈ F := hF.mem_of_tendsto hlim' (Eventually.of_forall hmem)
  have hT' : Tendsto (fun n => T (T^[n] f₀)) atTop (𝓝 (T f)) :=
    (hTc f hfF).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim', Eventually.of_forall hmem⟩)
  refine ⟨f, hfF, ?_, hlim'⟩
  have hlim2 : Tendsto (fun n => T (T^[n] f₀)) atTop (𝓝 f) := by
    have e : u = fun n => T (T^[n] f₀) := funext hu
    rwa [e] at hlim
  exact tendsto_nhds_unique hT' hlim2

/-- Monotone iteration: if `T` is monotone on `F`, `T` maps `F` to itself, `f₀ ∈ F` and
`f₀ ≤ Tf₀`, then `n ↦ Tⁿf₀` is increasing (proof of Theorem 17.7, p. 528). -/
theorem monotone_iterate_of_le {F : Set (X →ᵇ ℝ)} {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hmono : MonotoneOn T F) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀) : Monotone fun n => T^[n] f₀ := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => simpa using h
  | succ n ih =>
    calc T^[n + 1] f₀ = T (T^[n] f₀) := Function.iterate_succ_apply' T n f₀
      _ ≤ T (T^[n + 1] f₀) := hmono (hT.iterate n hf₀) (hT.iterate (n + 1) hf₀) ih
      _ = T^[n + 1 + 1] f₀ := (Function.iterate_succ_apply' T (n + 1) f₀).symm

/-- Monotone iteration downwards: if `Tf₀ ≤ f₀` then `n ↦ Tⁿf₀` is decreasing. -/
theorem antitone_iterate_of_ge {F : Set (X →ᵇ ℝ)} {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hmono : MonotoneOn T F) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : T f₀ ≤ f₀) : Antitone fun n => T^[n] f₀ := by
  refine antitone_nat_of_succ_le fun n => ?_
  induction n with
  | zero => simpa using h
  | succ n ih =>
    calc T^[n + 1 + 1] f₀ = T (T^[n + 1] f₀) := Function.iterate_succ_apply' T (n + 1) f₀
      _ ≤ T (T^[n] f₀) := hmono (hT.iterate (n + 1) hf₀) (hT.iterate n hf₀) ih
      _ = T^[n + 1] f₀ := (Function.iterate_succ_apply' T n f₀).symm

/-- A bounded set of `C(X)` is uniformly bounded pointwise. -/
theorem exists_abs_le_of_isBounded {F : Set (X →ᵇ ℝ)} (hFb : Bornology.IsBounded F) :
    ∃ C, ∀ f ∈ F, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hFb.exists_norm_le
  exact ⟨C, fun f hf x => (Real.norm_eq_abs _ ▸ f.norm_coe_le_norm x).trans (hC f hf)⟩

/-- **Theorem 17.7**, increasing case (SLP p. 528): `f₀ ≤ Tf₀`. The iterates `Tⁿf₀` increase
and converge in `C(X)` to a fixed point `f ∈ F` of `T`. -/
theorem theorem_17_7_of_le (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := by
  refine lemma_17_6 hX hF hT hTc hequi hf₀ fun x => ?_
  obtain ⟨C, hC⟩ := exists_abs_le_of_isBounded hFb
  have hm : Monotone fun n => (T^[n] f₀) x :=
    fun m n hmn => monotone_iterate_of_le hT hmono hf₀ h hmn x
  exact ⟨_, tendsto_atTop_ciSup hm ⟨C, by
    rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (hC _ (hT.iterate n hf₀) x)⟩⟩

/-- **Theorem 17.7**, decreasing case (SLP p. 528): `Tf₀ ≤ f₀`. -/
theorem theorem_17_7_of_ge (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : T f₀ ≤ f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := by
  refine lemma_17_6 hX hF hT hTc hequi hf₀ fun x => ?_
  obtain ⟨C, hC⟩ := exists_abs_le_of_isBounded hFb
  have hm : Antitone fun n => (T^[n] f₀) x :=
    fun m n hmn => antitone_iterate_of_ge hT hmono hf₀ h hmn x
  exact ⟨_, tendsto_atTop_ciInf hm ⟨-C, by
    rintro _ ⟨n, rfl⟩
    exact neg_le_of_abs_le (hC _ (hT.iterate n hf₀) x)⟩⟩

/-- **Theorem 17.7** (SLP p. 528). Let `X` be totally bounded (e.g. a bounded subset of `ℝˡ`),
`F ⊆ C(X)` closed and bounded, `T : F → F` continuous and monotone, with `T(F)` an equicontinuous
family. If `f₀ ∈ F` satisfies `f₀ ≤ Tf₀` or `f₀ ≥ Tf₀`, then `f = lim Tⁿf₀` exists (in the sup
norm), `f ∈ F`, and `Tf = f`. -/
theorem theorem_17_7 (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀ ∨ T f₀ ≤ f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) :=
  h.elim (theorem_17_7_of_le hX hF hFb hT hTc hmono hequi hf₀)
    (theorem_17_7_of_ge hX hF hFb hT hTc hmono hequi hf₀)

/-- A limit in `C(X)` of functions lying below `h` lies below `h`. -/
theorem le_of_tendsto_bcf {u : ℕ → X →ᵇ ℝ} {f h : X →ᵇ ℝ} (hlim : Tendsto u atTop (𝓝 f))
    (hle : ∀ n, u n ≤ h) : f ≤ h := fun x =>
  le_of_tendsto' (((continuous_eval_const x).tendsto f).comp hlim) fun n => hle n x

/-- A limit in `C(X)` of functions lying above `h` lies above `h`. -/
theorem ge_of_tendsto_bcf {u : ℕ → X →ᵇ ℝ} {f h : X →ᵇ ℝ} (hlim : Tendsto u atTop (𝓝 f))
    (hle : ∀ n, h ≤ u n) : h ≤ f := fun x =>
  ge_of_tendsto' (((continuous_eval_const x).tendsto f).comp hlim) fun n => hle n x

/-- **Corollary to Theorem 17.7**, least element (SLP p. 529). Under the hypotheses of
Theorem 17.7, if `f₀` is a least element of `F` then `f = lim Tⁿf₀` exists, is a fixed point in
`F`, and `f ≤ h` for every fixed point `h ∈ F` of `T`: `f` is the least fixed point in `F`. -/
theorem corollary_17_7_least (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : IsLeast F f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) ∧
      ∀ h ∈ F, T h = h → f ≤ h := by
  obtain ⟨f, hfF, hfix, hlim⟩ := theorem_17_7_of_le hX hF hFb hT hTc hmono hequi hf₀.1
    (hf₀.2 (hT hf₀.1))
  refine ⟨f, hfF, hfix, hlim, fun h hh hTh => le_of_tendsto_bcf hlim fun n => ?_⟩
  induction n with
  | zero => exact hf₀.2 hh
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hTh]
    exact hmono (hT.iterate n hf₀.1) hh ih

/-- **Corollary to Theorem 17.7**, greatest element (SLP p. 529): iterating from a greatest
element `g₀` of `F` converges to the greatest fixed point of `T` in `F`. -/
theorem corollary_17_7_greatest (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {g₀ : X →ᵇ ℝ}
    (hg₀ : IsGreatest F g₀) :
    ∃ g ∈ F, T g = g ∧ Tendsto (fun n => T^[n] g₀) atTop (𝓝 g) ∧
      ∀ h ∈ F, T h = h → h ≤ g := by
  obtain ⟨g, hgF, hfix, hlim⟩ := theorem_17_7_of_ge hX hF hFb hT hTc hmono hequi hg₀.1
    (hg₀.2 (hT hg₀.1))
  refine ⟨g, hgF, hfix, hlim, fun h hh hTh => ge_of_tendsto_bcf hlim fun n => ?_⟩
  induction n with
  | zero => exact hg₀.2 hh
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hTh]
    exact hmono hh (hT.iterate n hg₀.1) ih

/-- **Corollary to Theorem 17.7** (SLP p. 529). With `f₀` least and `g₀` greatest in `F`, the
limits `f = lim Tⁿf₀` and `g = lim Tⁿg₀` exist, are fixed points in `F`, and every fixed point
`h ∈ F` of `T` satisfies `f ≤ h ≤ g`. -/
theorem corollary_17_7 (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ g₀ : X →ᵇ ℝ}
    (hf₀ : IsLeast F f₀) (hg₀ : IsGreatest F g₀) :
    ∃ f ∈ F, ∃ g ∈ F, T f = f ∧ T g = g ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) ∧
      Tendsto (fun n => T^[n] g₀) atTop (𝓝 g) ∧ ∀ h ∈ F, T h = h → f ≤ h ∧ h ≤ g := by
  obtain ⟨f, hfF, hf, hfl, hfh⟩ := corollary_17_7_least hX hF hFb hT hTc hmono hequi hf₀
  obtain ⟨g, hgF, hg, hgl, hgh⟩ := corollary_17_7_greatest hX hF hFb hT hTc hmono hequi hg₀
  exact ⟨f, hfF, g, hgF, hf, hg, hfl, hgl, fun h hh hTh => ⟨hfh h hh hTh, hgh h hh hTh⟩⟩

/-- **Corollary to Theorem 17.7**, uniqueness test (SLP p. 529). If the iterates from the least
and from the greatest element of `F` have the same limit `f`, then `f` is the unique fixed point
of `T` in `F`. -/
theorem corollary_17_7_unique (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ g₀ f : X →ᵇ ℝ}
    (hf₀ : IsLeast F f₀) (hg₀ : IsGreatest F g₀)
    (hfl : Tendsto (fun n => T^[n] f₀) atTop (𝓝 f))
    (hgl : Tendsto (fun n => T^[n] g₀) atTop (𝓝 f)) :
    f ∈ F ∧ T f = f ∧ ∀ h ∈ F, T h = h → h = f := by
  obtain ⟨f', hf'F, g', hg'F, hf', hg', hf'l, hg'l, hbetween⟩ :=
    corollary_17_7 hX hF hFb hT hTc hmono hequi hf₀ hg₀
  have e1 : f' = f := tendsto_nhds_unique hf'l hfl
  have e2 : g' = f := tendsto_nhds_unique hg'l hgl
  subst e1
  subst e2
  exact ⟨hf'F, hf', fun h hh hTh => le_antisymm (hbetween h hh hTh).2 (hbetween h hh hTh).1⟩

/-- A bounded subset of a proper space (e.g. a bounded `X ⊆ ℝˡ`), seen as a subtype, is totally
bounded. This is what the book's hypothesis "`X ⊆ ℝˡ` bounded" provides. -/
theorem totallyBounded_univ_of_isBounded {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {S : Set E} (hS : Bornology.IsBounded S) : TotallyBounded (univ : Set S) := by
  have h : TotallyBounded S := hS.isCompact_closure.totallyBounded.subset subset_closure
  simpa using totallyBounded_preimage (isUniformInducing_val S) h

/-- **Theorem 17.7** with the book's hypothesis on the state space: `X` a bounded subset of a
proper space (e.g. `ℝˡ`), and `C(X) = X →ᵇ ℝ` on the subtype. -/
theorem theorem_17_7_of_isBounded {E : Type*} [PseudoMetricSpace E] [ProperSpace E] {S : Set E}
    (hS : Bornology.IsBounded S) {F : Set (S →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : S →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀ ∨ T f₀ ≤ f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) :=
  theorem_17_7 (totallyBounded_univ_of_isBounded hS) hF hFb hT hTc hmono hequi hf₀ h

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Total-variation continuity of a transition function (Assumption 17.3) and its consequences

SLP §17.4, pp. 520–522, as used in §17.5 (general application, p. 529, and Proposition 5,
p. 530). These are the facts about operators `(Tf)(x) = ∫ G[x, x', f(x')] π(x, dx')` that the
monotone-operator results of §17.5 need; they are proved here from scratch so that the §17.5
modules are self-contained.

* `IsFinMeasPartition`, `TVDistLE`: `‖μ − ν‖_TV ≤ ε` in the book's sense (p. 521, as in
  §11.3): `Σᵢ |μ(Aᵢ) − ν(Aᵢ)| ≤ ε` for every finite measurable partition `{Aᵢ}` of `X`.
* **Assumption 17.3** (`MonoAssumption17_3`, pp. 520–521): `x ↦ π(x, ·)` is uniformly
  continuous in the total-variation norm. (The book's `< ε` for all `ε` is equivalent to
  `≤ ε` for all `ε`; the boundedness of `X` is imposed separately where it is used.)
* `abs_integral_sub_le_of_tvDistLE`: `|∫ h dμ − ∫ h dν| ≤ c ‖μ − ν‖_TV` for `|h| ≤ c` measurable,
  the inequality `|∫ h dλ| ≤ sup|h| · ‖λ‖_TV` quoted on p. 521. The proof uses the Hahn
  decomposition: the two-set partition `{s, sᶜ}` already attains the bound.
* `uniformEquicontinuous_integral`: under Assumption 17.3, `{x ↦ ∫ g_i dπ(x, ·)}` is uniformly
  equicontinuous for any uniformly bounded family of measurable `g_i`
  (Lemma 17.5 with `G` independent of `x`); `continuous_integral_of_assumption17_3` for one `g`.
* **Lemma 17.5** (`kernelIntegral_uniformEquicontinuous`, p. 521): the family `T(F)` is
  equicontinuous when `G` is continuous on `X × X × D`, bounded on it, and uniformly continuous
  in its first argument.
* **Exercise 17.6** (`kernelIntegral_dist_le`, p. 522): if moreover `G` is uniformly continuous in
  its third argument (uniformly over `(x, x')`), `f ↦ Tf` is uniformly continuous in the sup
  norm on `F`.
* `kernelOp`: the operator `T` as a map `C(X) → C(X)`; `kernelOp_apply` (the formula on `F`) and
  `kernelOp_apply_of_continuous`.
* **General application of Theorem 17.7** (`kernelOp_monotone_fixedPoints`, p. 529): for
  `D = [c, d]`, `G : X × X × D → D` continuous, uniformly continuous in its first and third
  arguments and nondecreasing in its third, `F = {f : X → D}` is closed and bounded, `T` maps `F`
  to itself continuously and monotonically, `T(F)` is equicontinuous, and iterating from the
  constants `c` and `d` gives the least and greatest fixed points of `T` in `F`.

The facts of this file overlap the §17.4 modules (Lemma 17.5, Exercise 17.6 there); they are
reproved here, with their own names, so that the §17.5 modules do not depend on §17.4.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

/-- A finite measurable partition `A₀, …, A_{n-1}` of `X`. -/
def IsFinMeasPartition {n : ℕ} (A : Fin n → Set X) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧ (⋃ i, A i) = univ

/-- `‖μ − ν‖_TV ≤ ε` for the book's total-variation norm (SLP p. 521, §11.3): every finite
measurable partition `{Aᵢ}` of `X` has `Σᵢ |μ(Aᵢ) − ν(Aᵢ)| ≤ ε`. -/
def TVDistLE (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀ (n : ℕ) (A : Fin n → Set X), IsFinMeasPartition A →
    ∑ i, |μ.real (A i) - ν.real (A i)| ≤ ε

/-- **Assumption 17.3** (SLP pp. 520–521): for every `ε > 0` there is `δ > 0` such that
`d(x, x̂) < δ` implies `‖π(x, ·) − π(x̂, ·)‖_TV ≤ ε`. -/
def MonoAssumption17_3 [PseudoMetricSpace X] (π : Kernel X X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x x', dist x x' < δ → TVDistLE (π x) (π x') ε

/-- A two-set partition `{s, sᶜ}` of `X`. -/
theorem isFinMeasPartition_pair {s : Set X} (hs : MeasurableSet s) :
    IsFinMeasPartition ![s, sᶜ] := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · fin_cases i
    · exact hs
    · exact hs.compl
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact absurd rfl hij
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hx : x ∈ s
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hx⟩

/-- If `ν ≤ μ` are finite measures and `|h| ≤ c`, then
`|∫ h dμ − ∫ h dν| ≤ c (μ(X) − ν(X))`. -/
theorem abs_integral_sub_le_of_le {μ ν : Measure X} [IsFiniteMeasure μ] (hνμ : ν ≤ μ)
    {h : X → ℝ} (hm : Measurable h) {c : ℝ} (hc : ∀ x, |h x| ≤ c) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ c * (μ.real univ - ν.real univ) := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνμ
  have e : μ - ν + ν = μ := Measure.sub_add_cancel_of_le hνμ
  have hint : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable h ρ := fun ρ _ =>
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hc x)
  have hsplit : ∫ x, h x ∂μ = ∫ x, h x ∂(μ - ν) + ∫ x, h x ∂ν := by
    conv_lhs => rw [← e]
    exact integral_add_measure (hint _ inferInstance) (hint _ inferInstance)
  have hreal : μ.real univ = (μ - ν).real univ + ν.real univ := by
    conv_lhs => rw [← e]
    exact measureReal_add_apply
  rw [hsplit, add_sub_cancel_right, hreal, add_sub_cancel_right, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hc x)

/-- `|∫ h dμ − ∫ h dν| ≤ c ‖μ − ν‖_TV` for measurable `h` with `|h| ≤ c` and finite `μ, ν`
(SLP p. 521: `|∫ h dλ| ≤ sup|h| · ‖λ‖_TV`). -/
theorem abs_integral_sub_le_of_tvDistLE {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {h : X → ℝ} (hm : Measurable h) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, |h x| ≤ c) {ε : ℝ} (hTV : TVDistLE μ ν ε) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ c * ε := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsm := hs.measurableSet
  have hint : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable h ρ := fun ρ _ =>
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hc x)
  have h1 := abs_integral_sub_le_of_le hs.le_on hm hc
  have h2 := abs_integral_sub_le_of_le hs.ge_on_compl hm hc
  rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ] at h1 h2
  have hpart := hTV 2 ![s, sᶜ] (isFinMeasPartition_pair hsm)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hpart
  have hsplit : ∫ x, h x ∂μ - ∫ x, h x ∂ν = -(∫ x in s, h x ∂ν - ∫ x in s, h x ∂μ) +
      (∫ x in sᶜ, h x ∂μ - ∫ x in sᶜ, h x ∂ν) := by
    rw [← integral_add_compl hsm (hint μ inferInstance),
      ← integral_add_compl hsm (hint ν inferInstance)]
    ring
  rw [hsplit]
  calc |-(∫ x in s, h x ∂ν - ∫ x in s, h x ∂μ) + (∫ x in sᶜ, h x ∂μ - ∫ x in sᶜ, h x ∂ν)|
      ≤ |∫ x in s, h x ∂ν - ∫ x in s, h x ∂μ| + |∫ x in sᶜ, h x ∂μ - ∫ x in sᶜ, h x ∂ν| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ c * (ν.real s - μ.real s) + c * (μ.real sᶜ - ν.real sᶜ) := add_le_add h1 h2
    _ ≤ c * (|μ.real s - ν.real s| + |μ.real sᶜ - ν.real sᶜ|) := by
        rw [mul_add]
        gcongr
        · rw [abs_sub_comm]; exact le_abs_self _
        · exact le_abs_self _
    _ ≤ c * ε := by gcongr

variable [PseudoMetricSpace X]

/-- Under Assumption 17.3, for any family of measurable functions `gᵢ` with `|gᵢ| ≤ c`, the
conditional expectations `x ↦ ∫ gᵢ(x') π(x, dx')` form a uniformly equicontinuous family
(Lemma 17.5 for a kernel `G` not depending on `x`). -/
theorem uniformEquicontinuous_integral {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {ι : Type*} {g : ι → X → ℝ} (hg : ∀ i, Measurable (g i))
    {c : ℝ} (hc : ∀ i x, |g i x| ≤ c) :
    UniformEquicontinuous fun i x => ∫ x', g i x' ∂(π x) := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hc' : 0 < |c| + 1 := by positivity
  obtain ⟨δ, hδ, hπδ⟩ := hπ (ε / (|c| + 1)) (by positivity)
  refine ⟨δ, hδ, fun x y hxy i => ?_⟩
  rw [Real.dist_eq]
  calc |∫ x', g i x' ∂(π x) - ∫ x', g i x' ∂(π y)|
      ≤ |c| * (ε / (|c| + 1)) :=
        abs_integral_sub_le_of_tvDistLE (hg i) (abs_nonneg c)
          (fun x => (hc i x).trans (le_abs_self c)) (hπδ x y hxy)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hc']
        nlinarith [abs_nonneg c]

/-- Under Assumption 17.3, `x ↦ ∫ g(x') π(x, dx')` is continuous for bounded measurable `g`. -/
theorem continuous_integral_of_assumption17_3 {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) : Continuous fun x => ∫ x', g x' ∂(π x) := by
  have := uniformEquicontinuous_integral hπ (ι := Unit) (g := fun _ => g) (fun _ => hg)
    (fun _ => hc)
  exact (this.uniformContinuous ()).continuous

/-- **Lemma 17.5** (SLP p. 521). Let `π` satisfy Assumption 17.3, `D ⊆ ℝ`, and
`F = {f ∈ C(X) : f(X) ⊆ D}`. Let `G : X × X × D → ℝ` be continuous, bounded by `B`, and
uniformly continuous in its first argument (uniformly in `x', y`). Then the family of functions
`x ↦ ∫ G[x, x', f(x')] π(x, dx')`, `f ∈ F`, is uniformly equicontinuous. -/
theorem kernelIntegral_uniformEquicontinuous [OpensMeasurableSpace X] {π : Kernel X X}
    [IsMarkovKernel π] (hπ : MonoAssumption17_3 π) {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {B : ℝ} (hGb : ∀ x x' y, y ∈ D → |G x x' y| ≤ B)
    (hG1 : ∀ ε > 0, ∃ δ > 0, ∀ x z, dist x z < δ → ∀ x' y, y ∈ D →
      |G x x' y - G z x' y| < ε) :
    UniformEquicontinuous fun f : {f : X →ᵇ ℝ // ∀ x, f x ∈ D} =>
      fun x => ∫ x', G x x' (f.1 x') ∂(π x) := by
  have hmeas : ∀ (f : {f : X →ᵇ ℝ // ∀ x, f x ∈ D}) (x : X),
      Measurable fun x' => G x x' (f.1 x') := by
    intro f x
    refine (hGc.comp_continuous (f := fun x' => (x, x', f.1 x'))
      (continuous_const.prodMk (continuous_id.prodMk f.1.continuous)) fun x' => ?_).measurable
    exact ⟨mem_univ _, mem_univ _, f.2 x'⟩
  have hint : ∀ (f : {f : X →ᵇ ℝ // ∀ x, f x ∈ D}) (x z : X),
      Integrable (fun x' => G x x' (f.1 x')) (π z) := fun f x z =>
    Integrable.of_bound (hmeas f x).aestronglyMeasurable B (Eventually.of_forall fun x' => by
      rw [Real.norm_eq_abs]; exact hGb _ _ _ (f.2 x'))
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hG1δ⟩ := hG1 (ε / 2) (by positivity)
  have hB : 0 < |B| + 1 := by positivity
  obtain ⟨δ₂, hδ₂, hπδ⟩ := hπ (ε / (2 * (|B| + 1))) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x y hxy f => ?_⟩
  rw [Real.dist_eq]
  have e1 : |∫ x', G x x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π x)| ≤ ε / 2 := by
    rw [← integral_sub (hint f x x) (hint f y x), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 2)
      (Eventually.of_forall fun x' => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    exact (hG1δ x y (lt_of_lt_of_le hxy (min_le_left _ _)) x' _ (f.2 x')).le
  have e2 : |∫ x', G y x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π y)| ≤
      |B| * (ε / (2 * (|B| + 1))) :=
    abs_integral_sub_le_of_tvDistLE (hmeas f y) (abs_nonneg B)
      (fun x' => (hGb _ _ _ (f.2 x')).trans (le_abs_self B))
      (hπδ x y (lt_of_lt_of_le hxy (min_le_right _ _)))
  have e3 : |B| * (ε / (2 * (|B| + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [abs_nonneg B]
  calc |∫ x', G x x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π y)|
      ≤ |∫ x', G x x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π x)| +
        |∫ x', G y x' (f.1 x') ∂(π x) - ∫ x', G y x' (f.1 x') ∂(π y)| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt e1 (e2.trans_lt e3)
    _ = ε := add_halves ε

/-- Integrands `x' ↦ G[x, x', f(x')]` are measurable for `f ∈ F` when `G` is continuous on
`X × X × D`. -/
theorem measurable_kernelIntegrand [OpensMeasurableSpace X] {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {f : X →ᵇ ℝ} (hf : ∀ x, f x ∈ D) (x : X) : Measurable fun x' => G x x' (f x') :=
  (hGc.comp_continuous (f := fun x' => (x, x', f x'))
    (continuous_const.prodMk (continuous_id.prodMk f.continuous))
    fun x' => ⟨mem_univ _, mem_univ _, hf x'⟩).measurable

/-- **Exercise 17.6** (SLP p. 522). If in addition `G` is uniformly continuous in its third
argument, uniformly over `(x, x')`, then `f ↦ Tf` is uniformly continuous on `F` for the sup norm:
`‖f − g‖ < δ` implies `|(Tf)(x) − (Tg)(x)| ≤ ε` for all `x`. -/
theorem kernelIntegral_dist_le [OpensMeasurableSpace X] {π : Kernel X X} [IsMarkovKernel π]
    {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {B : ℝ} (hGb : ∀ x x' y, y ∈ D → |G x x' y| ≤ B)
    (hG3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ D → y' ∈ D → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ f g : X →ᵇ ℝ, (∀ x, f x ∈ D) → (∀ x, g x ∈ D) → dist f g < δ →
      ∀ x, |∫ x', G x x' (f x') ∂(π x) - ∫ x', G x x' (g x') ∂(π x)| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hG3δ⟩ := hG3 ε hε
  refine ⟨δ, hδ, fun f g hf hg hfg x => ?_⟩
  have hint : ∀ {k : X →ᵇ ℝ}, (∀ x, k x ∈ D) → Integrable (fun x' => G x x' (k x')) (π x) :=
    fun {k} hk => Integrable.of_bound (measurable_kernelIntegrand hGc hk x).aestronglyMeasurable
      B (Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hGb _ _ _ (hk x'))
  rw [← integral_sub (hint hf) (hint hg), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ε) (Eventually.of_forall fun x' => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]
  refine (hG3δ x x' _ _ (hf x') (hg x') ?_).le
  rw [← Real.dist_eq]
  exact lt_of_le_of_lt (dist_coe_le_dist x') hfg

open Classical in
/-- The operator `(Tf)(x) = ∫ G[x, x', f(x')] π(x, dx')` of SLP §17.4 (1) and p. 529, as a map
`C(X) → C(X)`. Where the right side is not a bounded continuous function of `x` (which can
happen only off the set `F` of the book), the value is `0`; the book's `T` is defined only on
`F`, where `kernelOp_apply` shows that the formula holds. -/
noncomputable def kernelOp (π : Kernel X X) (G : X → X → ℝ → ℝ) (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  if h : Continuous (fun x => ∫ x', G x x' (f x') ∂(π x)) ∧
      ∃ C, ∀ x y, dist (∫ x', G x x' (f x') ∂(π x)) (∫ x', G y x' (f x') ∂(π y)) ≤ C then
    BoundedContinuousFunction.mkOfBound ⟨_, h.1⟩ h.2.choose h.2.choose_spec
  else 0

/-- `kernelOp` is given by its formula whenever the formula defines a continuous function
bounded by `B`. -/
theorem kernelOp_apply_of_continuous {π : Kernel X X} {G : X → X → ℝ → ℝ} {f : X →ᵇ ℝ}
    (hc : Continuous fun x => ∫ x', G x x' (f x') ∂(π x)) {B : ℝ}
    (hb : ∀ x, |∫ x', G x x' (f x') ∂(π x)| ≤ B) (x : X) :
    kernelOp π G f x = ∫ x', G x x' (f x') ∂(π x) := by
  have h : Continuous (fun x => ∫ x', G x x' (f x') ∂(π x)) ∧
      ∃ C, ∀ x y, dist (∫ x', G x x' (f x') ∂(π x)) (∫ x', G y x' (f x') ∂(π y)) ≤ C :=
    ⟨hc, 2 * B, fun x y => by
      rw [Real.dist_eq]
      linarith [abs_sub (∫ x', G x x' (f x') ∂(π x)) (∫ x', G y x' (f x') ∂(π y)), hb x, hb y]⟩
  simp only [kernelOp, h]
  rfl

/-- Under Assumption 17.3, for `f ∈ F` the operator `kernelOp` is given by its formula. -/
theorem kernelOp_apply [OpensMeasurableSpace X] {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    {B : ℝ} (hGb : ∀ x x' y, y ∈ D → |G x x' y| ≤ B)
    (hG1 : ∀ ε > 0, ∃ δ > 0, ∀ x z, dist x z < δ → ∀ x' y, y ∈ D →
      |G x x' y - G z x' y| < ε) {f : X →ᵇ ℝ} (hf : ∀ x, f x ∈ D) (x : X) :
    kernelOp π G f x = ∫ x', G x x' (f x') ∂(π x) := by
  have heq := kernelIntegral_uniformEquicontinuous hπ hGc hGb hG1
  refine kernelOp_apply_of_continuous ((heq.uniformContinuous ⟨f, hf⟩).continuous) (B := B)
    (fun x => ?_) x
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun x' => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]
  exact hGb _ _ _ (hf x')

/-- **General application of Theorem 17.7** (SLP p. 529). Let `X` be totally bounded, `π`
satisfy Assumption 17.3, `D = [c, d]`, `F = {f ∈ C(X) : f(X) ⊆ D}`, and
`G : X × X × D → D` continuous, uniformly continuous in its first and third arguments and weakly
increasing in its third argument. Then `T = kernelOp π G` maps `F` into itself, is continuous and
monotone on `F`, and `T(F)` is equicontinuous; `F` is closed and bounded, with least element
`c` and greatest element `d`. Hence (Theorem 17.7 and its Corollary) `Tⁿc → f` and `Tⁿd → g` in
`C(X)`, `f` and `g` are fixed points in `F`, and every fixed point `h ∈ F` has `f ≤ h ≤ g`. -/
theorem kernelOp_monotone_fixedPoints [OpensMeasurableSpace X]
    (hX : TotallyBounded (univ : Set X)) {π : Kernel X X} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {c d : ℝ} (hcd : c ≤ d) {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ Icc c d))
    (hGD : ∀ x x' y, y ∈ Icc c d → G x x' y ∈ Icc c d)
    (hG1 : ∀ ε > 0, ∃ δ > 0, ∀ x z, dist x z < δ → ∀ x' y, y ∈ Icc c d →
      |G x x' y - G z x' y| < ε)
    (hG3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ Icc c d → y' ∈ Icc c d → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε)
    (hGmono : ∀ x x' y y', y ∈ Icc c d → y' ∈ Icc c d → y ≤ y' → G x x' y ≤ G x x' y') :
    let F : Set (X →ᵇ ℝ) := {f | ∀ x, f x ∈ Icc c d}
    IsClosed F ∧ Bornology.IsBounded F ∧ MapsTo (kernelOp π G) F F ∧
      ContinuousOn (kernelOp π G) F ∧ MonotoneOn (kernelOp π G) F ∧
      UniformEquicontinuous (fun f : F => ⇑(kernelOp π G f)) ∧
      IsLeast F (const X c) ∧ IsGreatest F (const X d) ∧
      ∃ f ∈ F, ∃ g ∈ F, kernelOp π G f = f ∧ kernelOp π G g = g ∧
        Tendsto (fun n => (kernelOp π G)^[n] (const X c)) atTop (𝓝 f) ∧
        Tendsto (fun n => (kernelOp π G)^[n] (const X d)) atTop (𝓝 g) ∧
        ∀ h ∈ F, kernelOp π G h = h → f ≤ h ∧ h ≤ g := by
  intro F
  set B := max |c| |d| with hB
  have hGb : ∀ x x' y, y ∈ Icc c d → |G x x' y| ≤ B := fun x x' y hy => by
    have := hGD x x' y hy
    exact abs_le.2 ⟨by rw [hB]; linarith [neg_abs_le c, le_max_left |c| |d|, this.1],
      by rw [hB]; linarith [le_abs_self d, le_max_right |c| |d|, this.2]⟩
  have happ : ∀ f ∈ F, ∀ x, kernelOp π G f x = ∫ x', G x x' (f x') ∂(π x) :=
    fun f hf x => kernelOp_apply hπ hGc hGb hG1 hf x
  have hint : ∀ f ∈ F, ∀ x, Integrable (fun x' => G x x' (f x')) (π x) := fun f hf x =>
    Integrable.of_bound (measurable_kernelIntegrand hGc hf x).aestronglyMeasurable B
      (Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hGb _ _ _ (hf x'))
  have hFc : IsClosed F := by
    have : F = ⋂ x, (fun f : X →ᵇ ℝ => f x) ⁻¹' Icc c d := by ext f; simp [F]
    rw [this]
    exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)
  have hFb : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨B, fun f hf => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg c) (le_max_left _ _))).2
      fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [neg_abs_le c, le_max_left |c| |d|, (hf x).1],
      by linarith [le_abs_self d, le_max_right |c| |d|, (hf x).2]⟩
  have hmaps : MapsTo (kernelOp π G) F F := fun f hf x => by
    rw [happ f hf x]
    constructor
    · calc c = ∫ _, c ∂(π x) := by simp
        _ ≤ _ := integral_mono (integrable_const c) (hint f hf x) fun x' => (hGD _ _ _ (hf x')).1
    · calc ∫ x', G x x' (f x') ∂(π x) ≤ ∫ _, d ∂(π x) :=
            integral_mono (hint f hf x) (integrable_const d) fun x' => (hGD _ _ _ (hf x')).2
        _ = d := by simp
  have hcont : ContinuousOn (kernelOp π G) F := by
    rw [Metric.continuousOn_iff]
    intro f hf ε hε
    obtain ⟨δ, hδ, hδ'⟩ := kernelIntegral_dist_le (π := π) hGc hGb hG3 (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun g hg hgf => ?_⟩
    refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_)
      (half_lt_self hε)
    rw [happ g hg, happ f hf, Real.dist_eq]
    exact hδ' g f hg hf hgf x
  have hmono : MonotoneOn (kernelOp π G) F := fun f hf g hg hfg x => by
    change kernelOp π G f x ≤ kernelOp π G g x
    rw [happ f hf, happ g hg]
    exact integral_mono (hint f hf x) (hint g hg x) fun x' =>
      hGmono _ _ _ _ (hf x') (hg x') (hfg x')
  have hequi : UniformEquicontinuous (fun f : F => ⇑(kernelOp π G f)) := by
    have e : (fun f : F => ⇑(kernelOp π G f)) =
        fun f : F => fun x => ∫ x', G x x' (f.1 x') ∂(π x) := by
      funext f x
      exact happ f.1 f.2 x
    rw [e]
    exact kernelIntegral_uniformEquicontinuous hπ hGc hGb hG1
  have hleast : IsLeast F (const X c) :=
    ⟨fun x => ⟨le_rfl, hcd⟩, fun f hf x => (hf x).1⟩
  have hgreatest : IsGreatest F (const X d) :=
    ⟨fun x => ⟨hcd, le_rfl⟩, fun f hf x => (hf x).2⟩
  exact ⟨hFc, hFb, hmaps, hcont, hmono, hequi, hleast, hgreatest,
    corollary_17_7 hX hFc hFb hmaps hcont hmono hequi hleast hgreatest⟩

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The OLG model by monotone iteration: Assumption 17.4 and Proposition 5

SLP §17.1 (pp. 502–507) and §17.5 (pp. 529–531).

* **Assumption 17.1** (p. 503): `MonoAssumption17_1H` (disutility of labour `H` on `[0, L)`),
  `MonoAssumption17_1V` (utility `V` on `ℝ₊`), bundled in `MonoAssumption17_1`. Derivatives are
  given explicitly (`H', H''`, `V', V''`), one-sided at `0`.
* `monoZeta` (`ζ(l) = l H'(l)`), `monoPhi` (`φ(y) = y V'(y)`) and `monoZetaInv` (`ζ⁻¹`, p. 507),
  with (all `MonoAssumption17_1H.*`): `ζ` continuous, strictly increasing from `[0, L)` onto `ℝ₊`
  (`surjOn_zeta`); `ζ⁻¹` continuous and increasing (`zetaInv_continuous`, `zetaInv_monotone`);
  `ζ⁻¹(y)/y → ∞` as `y ↓ 0` (`exists_lt_zetaInv`).
* `monoEpsK` (`ε_K = min{ε > 0 : ζ⁻¹(ε) = Kε}`, proof of Proposition 2, p. 514) with
  `MonoAssumption17_1H.epsK_spec`: the minimum exists, and `ζ⁻¹(y) > Ky` on `(0, ε_K)`.
  `monoB` (`B = max φ` on `[aζ⁻¹(ε_K), bL]`, proof of Proposition 4, p. 523).
* **Assumption 17.4** (`MonoAssumption17_4`, p. 530): `−yV″(y)/V′(y) ≤ 1` on `ℝ₊`; under
  Assumption 17.1 it makes `φ` nondecreasing (`MonoAssumption17_1V.monotoneOn_phi`).
* `monoOLGOp` : `C(X) → C(X)`, `(Tf)(x) = ∫ φ[x' ζ⁻¹(f(x'))] π(x, dx')` on `X = [a, b]`
  (§17.1 (9)), with `monoOLGOp_apply` (the formula, for every `f`, under Assumptions 17.1 and
  17.3).
* **Proposition 5** (`proposition_5`, p. 530): with `F = {f : ε_K ≤ f ≤ B}`, the iterates of `T`
  from `f₀ ≡ ε_K` and `g₀ ≡ B` converge in `C(X)` to fixed points `f ≤ g` in `F` that bracket
  every fixed point in `F`; if `f = g` it is the only fixed point of `T` in `F`.
* `monoOLGOp_zero` and `proposition_5_literal_false`: the zero function is always a fixed point,
  so the book's "this function is the unique fixed point of `T`" is false whenever `f = g`.
* `monoOLG_fixedPoint_mem` and `proposition_5_corrected`, `proposition_5_corrected'`: every
  fixed point with `inf h > 0` (equivalently, every strictly positive continuous fixed point)
  lies in `F`; so if `f = g`, `f` is the unique fixed point with `inf > 0`.

The concrete instance showing that `f = g` does occur (so the literal claim is genuinely false,
not vacuous) is in `FixedPointArguments.MonotoneOLGExamples`.

**Correction (Proposition 5, "at least one fixed point" / "the unique fixed point of T",
p. 530).** (i) `T` is not defined on all of `C(X)`, since `ζ⁻¹` is defined only on `ℝ₊`; here
`ζ⁻¹(y) := ζ⁻¹(max y 0)`, which leaves `T` unchanged on nonnegative functions. (ii) Since
`φ(0) = 0` and `ζ⁻¹(0) = 0`, `T0 = 0` (`monoOLGOp_zero`): "at least one fixed point" is trivial,
and when `f = g` the zero function is a second fixed point, so `f` is not "the unique fixed point
of `T`" (`proposition_5_literal_false`). The proof only gives uniqueness in `F`. Corrected
statement (`proposition_5_corrected`): if `f = g`, then `f` is the unique fixed point `h` of `T`
with `inf h > 0`. The proof: with `m = inf h`, `ζ⁻¹(y) > Ky` on `(0, ε_K)` and `φ ≥ KCε_K` above
`ε_K` give `m ≥ KC min(m, ε_K)`, and `KC > 1` forces `m ≥ ε_K`; then `h ≤ B`, so `h ∈ F`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-! ### Assumption 17.1 -/

/-- **Assumption 17.1**, labour (SLP p. 503): `H : [0, L) → ℝ₊` is twice continuously
differentiable (one-sided at `0`), strictly increasing and strictly convex, with `H'(0) = 0` and
`H'(l) → +∞` as `l → L`; `0 < L < ∞`. -/
structure MonoAssumption17_1H (H H' H'' : ℝ → ℝ) (L : ℝ) : Prop where
  L_pos : 0 < L
  hasDeriv_H : ∀ l ∈ Ico 0 L, HasDerivWithinAt H (H' l) (Ici 0) l
  hasDeriv_H' : ∀ l ∈ Ico 0 L, HasDerivWithinAt H' (H'' l) (Ici 0) l
  continuousOn_H'' : ContinuousOn H'' (Ico 0 L)
  nonneg : ∀ l ∈ Ico 0 L, 0 ≤ H l
  strictMonoOn : StrictMonoOn H (Ico 0 L)
  strictConvexOn : StrictConvexOn ℝ (Ico 0 L) H
  deriv_zero : H' 0 = 0
  tendsto_deriv : Tendsto H' (𝓝[<] L) atTop

/-- **Assumption 17.1**, utility (SLP p. 503): `V : ℝ₊ → ℝ₊` is twice continuously
differentiable (one-sided at `0`), strictly increasing and strictly concave. -/
structure MonoAssumption17_1V (V V' V'' : ℝ → ℝ) : Prop where
  hasDeriv_V : ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt V (V' y) (Ici 0) y
  hasDeriv_V' : ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt V' (V'' y) (Ici 0) y
  continuousOn_V'' : ContinuousOn V'' (Ici 0)
  nonneg : ∀ y ∈ Ici (0 : ℝ), 0 ≤ V y
  strictMonoOn : StrictMonoOn V (Ici 0)
  strictConcaveOn : StrictConcaveOn ℝ (Ici 0) V

/-- **Assumption 17.1** (SLP p. 503), both halves. -/
structure MonoAssumption17_1 (H H' H'' V V' V'' : ℝ → ℝ) (L : ℝ) : Prop where
  hH : MonoAssumption17_1H H H' H'' L
  hV : MonoAssumption17_1V V V' V''

/-- `ζ(l) = l H'(l)` (SLP p. 504). -/
def monoZeta (H' : ℝ → ℝ) (l : ℝ) : ℝ := l * H' l

/-- `φ(y) = y V'(y)` (SLP p. 504). -/
def monoPhi (V' : ℝ → ℝ) (y : ℝ) : ℝ := y * V' y

/-- `ζ⁻¹ : ℝ₊ → [0, L)` (SLP p. 507), extended to `ℝ` by `ζ⁻¹(y) = ζ⁻¹(max y 0)`. -/
noncomputable def monoZetaInv (H' : ℝ → ℝ) (L y : ℝ) : ℝ :=
  Function.invFunOn (monoZeta H') (Ico 0 L) (max y 0)

/-- Relative risk aversion `−yV″(y)/V′(y)`. -/
noncomputable def monoRRA (V' V'' : ℝ → ℝ) (y : ℝ) : ℝ := -y * V'' y / V' y

/-- **Assumption 17.4** (SLP p. 530): `−yV″(y)/V′(y) ≤ 1` for all `y ∈ ℝ₊`. -/
def MonoAssumption17_4 (V' V'' : ℝ → ℝ) : Prop := ∀ y, 0 ≤ y → monoRRA V' V'' y ≤ 1

/-! ### Consequences of Assumption 17.1 for `H` and `ζ` -/

variable {H H' H'' : ℝ → ℝ} {L : ℝ}

/-- `H'` is continuous on `[0, L)`. -/
theorem MonoAssumption17_1H.continuousOn_H' (hA : MonoAssumption17_1H H H' H'' L) :
    ContinuousOn H' (Ico 0 L) := fun l hl =>
  ((hA.hasDeriv_H' l hl).continuousWithinAt).mono Ico_subset_Ici_self

/-- `H'` is strictly increasing on `[0, L)` (strict convexity). -/
theorem MonoAssumption17_1H.strictMonoOn_H' (hA : MonoAssumption17_1H H H' H'' L) :
    StrictMonoOn H' (Ico 0 L) := fun x hx y hy hxy =>
  (hA.strictConvexOn.lt_slope_of_hasDerivWithinAt hx hy hxy
    ((hA.hasDeriv_H x hx).mono Ico_subset_Ici_self)).trans
    (hA.strictConvexOn.slope_lt_of_hasDerivWithinAt hx hy hxy
      ((hA.hasDeriv_H y hy).mono Ico_subset_Ici_self))

/-- `H'(l) > 0` for `l ∈ (0, L)`. -/
theorem MonoAssumption17_1H.H'_pos (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ioo 0 L) : 0 < H' l := by
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hA.L_pos⟩
  have hl' : l ∈ Ico 0 L := Ioo_subset_Ico_self hl
  refine lt_trans ?_ (hA.strictConvexOn.slope_lt_of_hasDerivWithinAt h0 hl' hl.1
    ((hA.hasDeriv_H l hl').mono Ico_subset_Ici_self))
  rw [slope_def_field]
  exact div_pos (sub_pos.2 (hA.strictMonoOn h0 hl' hl.1)) (sub_pos.2 hl.1)

/-- `H' ≥ 0` on `[0, L)`. -/
theorem MonoAssumption17_1H.H'_nonneg (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ico 0 L) : 0 ≤ H' l := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, hA.deriv_zero]
  · exact (hA.H'_pos ⟨h, hl.2⟩).le

/-- `ζ(0) = 0`. -/
theorem monoZeta_zero : monoZeta H' 0 = 0 := by simp [monoZeta]

/-- `ζ` is continuous on `[0, L)`. -/
theorem MonoAssumption17_1H.continuousOn_zeta (hA : MonoAssumption17_1H H H' H'' L) :
    ContinuousOn (monoZeta H') (Ico 0 L) :=
  continuousOn_id.mul hA.continuousOn_H'

/-- `ζ` is strictly increasing on `[0, L)` (SLP p. 505, step 1). -/
theorem MonoAssumption17_1H.strictMonoOn_zeta (hA : MonoAssumption17_1H H H' H'' L) :
    StrictMonoOn (monoZeta H') (Ico 0 L) := fun x hx y hy hxy => by
  have hy0 : 0 < y := lt_of_le_of_lt hx.1 hxy
  calc monoZeta H' x = x * H' x := rfl
    _ ≤ x * H' y := mul_le_mul_of_nonneg_left (hA.strictMonoOn_H' hx hy hxy).le hx.1
    _ < y * H' y := mul_lt_mul_of_pos_right hxy (hA.H'_pos ⟨hy0, hy.2⟩)
    _ = monoZeta H' y := rfl

/-- `ζ ≥ 0` on `[0, L)`. -/
theorem MonoAssumption17_1H.zeta_nonneg (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ico 0 L) : 0 ≤ monoZeta H' l :=
  mul_nonneg hl.1 (hA.H'_nonneg hl)

/-- `ζ` maps `[0, L)` onto `ℝ₊` (SLP p. 507). -/
theorem MonoAssumption17_1H.surjOn_zeta (hA : MonoAssumption17_1H H H' H'' L) :
    SurjOn (monoZeta H') (Ico 0 L) (Ici 0) := by
  intro y hy
  have ht : Tendsto (monoZeta H') (𝓝[<] L) atTop :=
    Tendsto.pos_mul_atTop hA.L_pos (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      hA.tendsto_deriv
  obtain ⟨l₁, hl₁, hl₁'⟩ :=
    ((ht.eventually (eventually_ge_atTop y)).and (Ioo_mem_nhdsLT hA.L_pos)).exists
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hl₁'.2⟩
  obtain ⟨l, hl, hly⟩ := intermediate_value_Icc hl₁'.1.le (hA.continuousOn_zeta.mono hsub)
    ⟨by rw [monoZeta_zero]; exact hy, hl₁⟩
  exact ⟨l, hsub hl, hly⟩

/-! ### `ζ⁻¹` -/

/-- `ζ⁻¹(y) ∈ [0, L)` for every `y`. -/
theorem MonoAssumption17_1H.zetaInv_mem (hA : MonoAssumption17_1H H H' H'' L) (y : ℝ) :
    monoZetaInv H' L y ∈ Ico 0 L :=
  Function.invFunOn_mem (hA.surjOn_zeta (le_max_right y 0 : (0 : ℝ) ≤ max y 0))

/-- `ζ(ζ⁻¹(y)) = y` for `y ≥ 0`. -/
theorem MonoAssumption17_1H.zeta_zetaInv (hA : MonoAssumption17_1H H H' H'' L) {y : ℝ}
    (hy : 0 ≤ y) : monoZeta H' (monoZetaInv H' L y) = y := by
  have := Function.invFunOn_eq (hA.surjOn_zeta (le_max_right y 0 : (0 : ℝ) ≤ max y 0))
  rw [monoZetaInv, this, max_eq_left hy]

/-- `ζ⁻¹(ζ(l)) = l` for `l ∈ [0, L)`. -/
theorem MonoAssumption17_1H.zetaInv_zeta (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ico 0 L) : monoZetaInv H' L (monoZeta H' l) = l :=
  hA.strictMonoOn_zeta.injOn (hA.zetaInv_mem _) hl (hA.zeta_zetaInv (hA.zeta_nonneg hl))

/-- `ζ⁻¹(y) = 0` for `y ≤ 0`; in particular `ζ⁻¹(0) = 0`. -/
theorem MonoAssumption17_1H.zetaInv_of_nonpos (hA : MonoAssumption17_1H H H' H'' L) {y : ℝ}
    (hy : y ≤ 0) : monoZetaInv H' L y = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hA.L_pos⟩
  have := hA.zetaInv_zeta h0
  rw [monoZeta_zero] at this
  rw [← this, monoZetaInv, monoZetaInv, max_eq_right hy, max_self]

/-- `ζ⁻¹` is nondecreasing on `ℝ`. -/
theorem MonoAssumption17_1H.zetaInv_monotone (hA : MonoAssumption17_1H H H' H'' L) :
    Monotone (monoZetaInv H' L) := fun y₁ y₂ h => by
  have e : ∀ y, monoZetaInv H' L y = monoZetaInv H' L (max y 0) := fun y => by
    simp [monoZetaInv]
  rw [e y₁, e y₂, ← hA.strictMonoOn_zeta.le_iff_le (hA.zetaInv_mem _) (hA.zetaInv_mem _),
    hA.zeta_zetaInv (le_max_right _ _), hA.zeta_zetaInv (le_max_right _ _)]
  exact max_le_max h le_rfl

/-- `ζ⁻¹` is strictly increasing on `ℝ₊`. -/
theorem MonoAssumption17_1H.zetaInv_strictMonoOn (hA : MonoAssumption17_1H H H' H'' L) :
    StrictMonoOn (monoZetaInv H' L) (Ici 0) := fun y₁ h₁ y₂ h₂ h => by
  rw [← hA.strictMonoOn_zeta.lt_iff_lt (hA.zetaInv_mem _) (hA.zetaInv_mem _),
    hA.zeta_zetaInv h₁, hA.zeta_zetaInv h₂]
  exact h

/-- `ζ⁻¹` is continuous (SLP p. 507). -/
theorem MonoAssumption17_1H.zetaInv_continuous (hA : MonoAssumption17_1H H H' H'' L) :
    Continuous (monoZetaInv H' L) := by
  set g : ℝ → ℝ := fun y => if y < 0 then y else monoZetaInv H' L y with hg
  have hgm : Monotone g := fun y₁ y₂ h => by
    simp only [hg]
    split_ifs with h1 h2 h2
    · exact h
    · exact h1.le.trans (hA.zetaInv_mem _).1
    · exact absurd (lt_of_le_of_lt h h2) h1
    · exact hA.zetaInv_monotone h
  have hglt : ∀ y, g y < L := fun y => by
    simp only [hg]
    split_ifs with h1
    · exact h1.trans hA.L_pos
    · exact (hA.zetaInv_mem y).2
  have himg : Iio L ⊆ g '' univ := fun t ht => by
    rcases lt_or_ge t 0 with h | h
    · exact ⟨t, mem_univ _, by simp [hg, h]⟩
    · refine ⟨monoZeta H' t, mem_univ _, ?_⟩
      have hz := hA.zeta_nonneg ⟨h, ht⟩
      simp only [hg, not_lt.2 hz, ↓reduceIte]
      exact hA.zetaInv_zeta ⟨h, ht⟩
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun y =>
    continuousAt_of_monotoneOn_of_image_mem_nhds (hgm.monotoneOn univ) univ_mem
      (mem_of_superset (Iio_mem_nhds (hglt y)) himg)
  have e : monoZetaInv H' L = fun y => max (g y) 0 := by
    funext y
    simp only [hg]
    split_ifs with h
    · rw [hA.zetaInv_of_nonpos h.le, max_eq_right h.le]
    · rw [max_eq_left (hA.zetaInv_mem y).1]
  rw [e]
  exact hgc.max continuous_const

/-- `ζ⁻¹(y)/y → ∞` as `y ↓ 0`: for every `K > 0` there is `ε₀ > 0` with `Ky < ζ⁻¹(y)` on
`(0, ε₀]` (from `H'(0) = 0`; SLP p. 514, Figure 17.2). -/
theorem MonoAssumption17_1H.exists_lt_zetaInv (hA : MonoAssumption17_1H H H' H'' L) {K : ℝ}
    (hK : 0 < K) : ∃ ε₀ > 0, ∀ y ∈ Ioc 0 ε₀, K * y < monoZetaInv H' L y := by
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hA.L_pos⟩
  have hc : Tendsto H' (𝓝[≥] 0) (𝓝 0) := by
    have := (hA.hasDeriv_H' 0 h0).continuousWithinAt.tendsto
    rwa [hA.deriv_zero] at this
  have h1 : ∀ᶠ l in 𝓝[≥] (0 : ℝ), H' l < 1 / K :=
    hc.eventually_lt_const (by positivity)
  obtain ⟨l₀, hl₀, hl₀'⟩ :=
    ((h1.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)).and
      (Ioo_mem_nhdsGT hA.L_pos)).exists
  have hl₀m : l₀ ∈ Ico 0 L := Ioo_subset_Ico_self hl₀'
  refine ⟨monoZeta H' l₀, mul_pos hl₀'.1 (hA.H'_pos hl₀'), fun y hy => ?_⟩
  set l := monoZetaInv H' L y with hl_def
  have hlm : l ∈ Ico 0 L := hA.zetaInv_mem y
  have hyl : monoZeta H' l = y := hA.zeta_zetaInv hy.1.le
  have hll₀ : l ≤ l₀ := by
    have := hA.zetaInv_monotone hy.2
    rwa [hA.zetaInv_zeta hl₀m] at this
  have hlpos : 0 < l := by
    rcases hlm.1.eq_or_lt with h | h
    · rw [← h, monoZeta_zero] at hyl; exact absurd hyl hy.1.ne
    · exact h
  have hH'l : H' l ≤ H' l₀ := (hA.strictMonoOn_H'.monotoneOn) hlm hl₀m hll₀
  have : y < l * (1 / K) := by
    rw [← hyl]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hH'l hlpos.le)
      (mul_lt_mul_of_pos_left hl₀ hlpos)
  rw [mul_one_div, lt_div_iff₀ hK] at this
  linarith

/-! ### `ε_K` and `B` -/

/-- `ε_K = min{ε > 0 : ζ⁻¹(ε) = Kε}` (SLP p. 514, proof of Proposition 2, used again in
Propositions 4 and 5). -/
noncomputable def monoEpsK (H' : ℝ → ℝ) (L K : ℝ) : ℝ :=
  sInf {ε | 0 < ε ∧ monoZetaInv H' L ε = K * ε}

/-- The minimum defining `ε_K` exists (SLP p. 514, "well defined"): `ε_K > 0`,
`ζ⁻¹(ε_K) = Kε_K`, and `ζ⁻¹(y) > Ky` for `y ∈ (0, ε_K)`. -/
theorem MonoAssumption17_1H.epsK_spec (hA : MonoAssumption17_1H H H' H'' L) {K : ℝ}
    (hK : 0 < K) :
    0 < monoEpsK H' L K ∧ monoZetaInv H' L (monoEpsK H' L K) = K * monoEpsK H' L K ∧
      ∀ y ∈ Ioo 0 (monoEpsK H' L K), K * y < monoZetaInv H' L y := by
  obtain ⟨ε₀, hε₀, hε₀'⟩ := hA.exists_lt_zetaInv hK
  set S := {ε | 0 < ε ∧ monoZetaInv H' L ε = K * ε} with hS
  set h : ℝ → ℝ := fun y => monoZetaInv H' L y - K * y with hh
  have hhc : Continuous h := hA.zetaInv_continuous.sub (continuous_const.mul continuous_id)
  have hpos0 : 0 < h ε₀ := by simp only [hh]; linarith [hε₀' ε₀ ⟨hε₀, le_rfl⟩]
  have hLK : 0 < L / K := div_pos hA.L_pos hK
  have hneg : h (L / K) < 0 := by
    simp only [hh, mul_div_cancel₀ _ hK.ne']
    linarith [(hA.zetaInv_mem (L / K)).2]
  have hle : ε₀ ≤ L / K := by
    refine le_of_not_gt fun hc => ?_
    have := hε₀' (L / K) ⟨hLK, hc.le⟩
    rw [mul_div_cancel₀ _ hK.ne'] at this
    linarith [(hA.zetaInv_mem (L / K)).2]
  have hSsub : S = Icc ε₀ (L / K) ∩ h ⁻¹' {0} := by
    ext ε
    simp only [hS, hh, mem_ofPred_eq, mem_inter_iff, mem_Icc, mem_preimage, mem_singleton_iff,
      sub_eq_zero]
    constructor
    · rintro ⟨hε, he⟩
      refine ⟨⟨?_, ?_⟩, he⟩
      · refine le_of_not_gt fun hc => ?_
        linarith [hε₀' ε ⟨hε, hc.le⟩]
      · have := (hA.zetaInv_mem ε).2
        rw [he] at this
        rw [le_div_iff₀ hK]
        linarith
    · rintro ⟨⟨h1, _⟩, he⟩
      exact ⟨lt_of_lt_of_le hε₀ h1, he⟩
  have hScpt : IsCompact S := by
    rw [hSsub]
    exact isCompact_Icc.inter_right (isClosed_singleton.preimage hhc)
  have hSne : S.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle hhc.continuousOn ⟨hneg.le, hpos0.le⟩
    refine ⟨c, ?_⟩
    rw [hSsub]
    exact ⟨hc, hc0⟩
  have hmem : monoEpsK H' L K ∈ S := hScpt.sInf_mem hSne
  refine ⟨hmem.1, hmem.2, fun y hy => lt_of_not_ge fun hc => ?_⟩
  have hy0 : h y ≤ 0 := by simp only [hh]; linarith
  have hyε : ε₀ < y := by
    refine lt_of_not_ge fun hc' => ?_
    linarith [hε₀' y ⟨hy.1, hc'⟩]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hyε.le hhc.continuousOn ⟨hy0, hpos0.le⟩
  have hcS : c ∈ S := ⟨lt_of_lt_of_le hε₀ hc.1, by
    have : h c = 0 := hc0
    simp only [hh, sub_eq_zero] at this
    exact this⟩
  have : monoEpsK H' L K ≤ c := csInf_le ⟨0, fun ε hε => hε.1.le⟩ hcS
  linarith [hc.2, hy.2]

/-! ### Consequences of Assumption 17.1 for `V` and `φ`; Assumption 17.4 -/

variable {V V' V'' : ℝ → ℝ}

/-- `V'` is continuous on `ℝ₊`. -/
theorem MonoAssumption17_1V.continuousOn_V' (hV : MonoAssumption17_1V V V' V'') :
    ContinuousOn V' (Ici 0) := fun y hy => (hV.hasDeriv_V' y hy).continuousWithinAt

/-- `V'(y) > 0` for `y ≥ 0` (SLP p. 503, derived consequence of Assumption 17.1). -/
theorem MonoAssumption17_1V.V'_pos (hV : MonoAssumption17_1V V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := hy
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by rw [mem_Ici]; linarith
  refine lt_trans ?_ (hV.strictConcaveOn.slope_lt_of_hasDerivWithinAt hy' hy1 (lt_add_one y)
    (hV.hasDeriv_V y hy'))
  rw [slope_def_field]
  exact div_pos (sub_pos.2 (hV.strictMonoOn hy' hy1 (lt_add_one y))) (by linarith)

/-- `V'` is strictly decreasing on `ℝ₊` (strict concavity). -/
theorem MonoAssumption17_1V.strictAntiOn_V' (hV : MonoAssumption17_1V V V' V'') :
    StrictAntiOn V' (Ici 0) := fun x hx y hy hxy =>
  (hV.strictConcaveOn.lt_slope_of_hasDerivWithinAt hx hy hxy (hV.hasDeriv_V y hy)).trans
    (hV.strictConcaveOn.slope_lt_of_hasDerivWithinAt hx hy hxy (hV.hasDeriv_V x hx))

/-- `φ(0) = 0`. -/
theorem monoPhi_zero : monoPhi V' 0 = 0 := by simp [monoPhi]

/-- `φ` is continuous on `ℝ₊`. -/
theorem MonoAssumption17_1V.continuousOn_phi (hV : MonoAssumption17_1V V V' V'') :
    ContinuousOn (monoPhi V') (Ici 0) :=
  continuousOn_id.mul hV.continuousOn_V'

/-- Under Assumption 17.1, Assumption 17.4 makes `φ(y) = yV'(y)` nondecreasing on `ℝ₊`
(SLP p. 530: `φ'(y) = V'(y)[1 − (−yV''(y)/V'(y))] ≥ 0`). -/
theorem MonoAssumption17_1V.monotoneOn_phi (hV : MonoAssumption17_1V V V' V'')
    (h4 : MonoAssumption17_4 V' V'') : MonotoneOn (monoPhi V') (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => V' y + y * V'' y) (convex_Ici 0)
    hV.continuousOn_phi (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ici] at hy
    have hd : HasDerivAt V' (V'' y) y :=
      (hV.hasDeriv_V' y (mem_Ici.2 (le_of_lt hy))).hasDerivAt (Ici_mem_nhds hy)
    have : HasDerivAt (monoPhi V') (V' y + y * V'' y) y := by
      have h' := (hasDerivAt_id' y).mul hd
      rw [one_mul] at h'
      exact h'
    exact this.hasDerivWithinAt
  · rw [interior_Ici] at hy
    have hpos := hV.V'_pos hy.le
    have := h4 y hy.le
    simp only [monoRRA] at this
    rw [div_le_iff₀ hpos] at this
    linarith

/-! ### The operator `T` of (9) on `X = [a, b]` -/

variable {a b : ℝ}

/-- The kernel `G[x, x', y] = φ[x' ζ⁻¹(y)]` of the OLG operator (SLP §17.1 (9)). -/
noncomputable def monoOLGKernel (H' V' : ℝ → ℝ) (L a b : ℝ) : Icc a b → Icc a b → ℝ → ℝ :=
  fun _ x' y => monoPhi V' (x'.1 * monoZetaInv H' L y)

/-- The OLG operator `(Tf)(x) = ∫ φ[x' ζ⁻¹(f(x'))] π(x, dx')` (SLP §17.1 (9) and §17.5,
Proposition 5) as a map `C(X) → C(X)` on `X = [a, b]`. -/
noncomputable def monoOLGOp (π : Kernel (Icc a b) (Icc a b)) (H' V' : ℝ → ℝ) (L : ℝ) :
    (Icc a b →ᵇ ℝ) → (Icc a b →ᵇ ℝ) :=
  kernelOp π (monoOLGKernel H' V' L a b)

/-- `B = max{φ(y) : y ∈ [aζ⁻¹(ε_K), bL]}` (SLP p. 523, proof of Proposition 4). -/
noncomputable def monoB (a b : ℝ) (H' V' : ℝ → ℝ) (L K : ℝ) : ℝ :=
  sSup (monoPhi V' '' Icc (a * monoZetaInv H' L (monoEpsK H' L K)) (b * L))

/-- The set `F = {f ∈ C(X) : ε_K ≤ f ≤ B}` of Propositions 4 and 5. -/
def monoF (a b : ℝ) (H' V' : ℝ → ℝ) (L K : ℝ) : Set (Icc a b →ᵇ ℝ) :=
  {f | ∀ x, f x ∈ Icc (monoEpsK H' L K) (monoB a b H' V' L K)}

/-- The argument `x' ζ⁻¹(y)` of `φ` lies in `[0, bL]`. -/
theorem MonoAssumption17_1H.arg_mem (hA : MonoAssumption17_1H H H' H'' L) (ha : 0 < a)
    (x' : Icc a b) (y : ℝ) : x'.1 * monoZetaInv H' L y ∈ Icc 0 (b * L) :=
  ⟨mul_nonneg (ha.le.trans x'.2.1) (hA.zetaInv_mem y).1,
    mul_le_mul x'.2.2 (hA.zetaInv_mem y).2.le (hA.zetaInv_mem y).1
      ((ha.le.trans x'.2.1).trans x'.2.2)⟩

/-- `φ` is bounded on `[0, bL]`. -/
theorem MonoAssumption17_1V.exists_bound_phi (hV : MonoAssumption17_1V V V' V'') (c : ℝ) :
    ∃ M, ∀ t ∈ Icc 0 c, |monoPhi V' t| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hV.continuousOn_phi.mono Icc_subset_Ici_self)
  exact ⟨M, fun t ht => by rw [← Real.norm_eq_abs]; exact hM t ht⟩

/-- The integrand `x' ↦ φ[x' ζ⁻¹(f(x'))]` is continuous for every `f ∈ C(X)`. -/
theorem monoOLG_integrand_continuous (hA : MonoAssumption17_1 H H' H'' V V' V'' L)
    (ha : 0 < a) (f : Icc a b →ᵇ ℝ) :
    Continuous fun x' : Icc a b => monoPhi V' (x'.1 * monoZetaInv H' L (f x')) :=
  hA.hV.continuousOn_phi.comp_continuous
    (continuous_subtype_val.mul (hA.hH.zetaInv_continuous.comp f.continuous))
    fun x' => (hA.hH.arg_mem ha x' (f x')).1

/-- Under Assumptions 17.1 and 17.3, `T` is given by its formula on all of `C(X)`. -/
theorem monoOLGOp_apply (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π] (hπ : MonoAssumption17_3 π)
    (f : Icc a b →ᵇ ℝ) (x : Icc a b) :
    monoOLGOp π H' V' L f x = ∫ x', monoPhi V' (x'.1 * monoZetaInv H' L (f x')) ∂(π x) := by
  obtain ⟨M, hM⟩ := hA.hV.exists_bound_phi (b * L)
  have hb : ∀ x', |monoPhi V' (x'.1 * monoZetaInv H' L (f x'))| ≤ M :=
    fun x' => hM _ (hA.hH.arg_mem ha x' (f x'))
  refine kernelOp_apply_of_continuous (G := monoOLGKernel H' V' L a b)
    (continuous_integral_of_assumption17_3 hπ (monoOLG_integrand_continuous hA ha f).measurable
      hb) (B := M) (fun x => ?_) x
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := M) (Eventually.of_forall fun x' => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]
  exact hb x'

/-- **The zero function is a fixed point of `T`** (NOTE to Proposition 5, p. 530):
`φ(0) = 0` and `ζ⁻¹(0) = 0`. -/
theorem monoOLGOp_zero (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π] (hπ : MonoAssumption17_3 π) :
    monoOLGOp π H' V' L 0 = 0 := by
  ext x
  rw [monoOLGOp_apply hA ha hπ]
  simp [hA.hH.zetaInv_of_nonpos le_rfl, monoPhi]

/-- The bounds (4)–(5) of the proof of Proposition 4 (SLP p. 523): for `x' ∈ [a, b]` and
`y ≥ ε_K`, `x' ζ⁻¹(y) ∈ [aζ⁻¹(ε_K), bL]`, `φ[x'ζ⁻¹(y)] ≥ KCε_K` with `C = aV'(bL)`, and
`φ[x'ζ⁻¹(y)] ≤ B`. -/
theorem monoOLG_bounds (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    {K : ℝ} (hK : 0 < K) {t y : ℝ} (ht : t ∈ Icc a b) (hy : monoEpsK H' L K ≤ y) :
    t * monoZetaInv H' L y ∈ Icc (a * monoZetaInv H' L (monoEpsK H' L K)) (b * L) ∧
      K * (a * V' (b * L)) * monoEpsK H' L K ≤ monoPhi V' (t * monoZetaInv H' L y) ∧
      monoPhi V' (t * monoZetaInv H' L y) ≤ monoB a b H' V' L K := by
  obtain ⟨hε, hεK, -⟩ := hA.hH.epsK_spec hK
  have hmono := hA.hH.zetaInv_monotone hy
  have hmemy := hA.hH.zetaInv_mem y
  have hmemε := hA.hH.zetaInv_mem (monoEpsK H' L K)
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have hlow : a * monoZetaInv H' L (monoEpsK H' L K) ≤ t * monoZetaInv H' L y :=
    mul_le_mul ht.1 hmono hmemε.1 ht0.le
  have hup : t * monoZetaInv H' L y ≤ b * L :=
    mul_le_mul ht.2 hmemy.2.le hmemy.1 (ht0.le.trans ht.2)
  have hs0 : 0 ≤ t * monoZetaInv H' L y := mul_nonneg ht0.le hmemy.1
  refine ⟨⟨hlow, hup⟩, ?_, ?_⟩
  · have hbL : (0 : ℝ) ≤ b * L := hs0.trans hup
    have hV'le : V' (b * L) ≤ V' (t * monoZetaInv H' L y) :=
      hA.hV.strictAntiOn_V'.antitoneOn hs0 hbL hup
    have hVpos := hA.hV.V'_pos hbL
    calc K * (a * V' (b * L)) * monoEpsK H' L K
        = (a * monoZetaInv H' L (monoEpsK H' L K)) * V' (b * L) := by rw [hεK]; ring
      _ ≤ (t * monoZetaInv H' L y) * V' (b * L) := mul_le_mul_of_nonneg_right hlow hVpos.le
      _ ≤ (t * monoZetaInv H' L y) * V' (t * monoZetaInv H' L y) :=
          mul_le_mul_of_nonneg_left hV'le hs0
      _ = monoPhi V' (t * monoZetaInv H' L y) := rfl
  · have hbdd : BddAbove (monoPhi V' '' Icc (a * monoZetaInv H' L (monoEpsK H' L K)) (b * L)) :=
      (isCompact_Icc.image_of_continuousOn (hA.hV.continuousOn_phi.mono fun s hs =>
        (mul_nonneg ha.le hmemε.1).trans hs.1)).bddAbove
    exact le_csSup hbdd ⟨_, ⟨hlow, hup⟩, rfl⟩

/-- `K > 0` follows from `KC > 1`, `C = aV'(bL)`. -/
theorem monoOLG_K_pos (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {K : ℝ} (hK : 1 < K * (a * V' (b * L))) : 0 < K := by
  have hC : 0 < a * V' (b * L) :=
    mul_pos ha (hA.hV.V'_pos (mul_nonneg (ha.le.trans hab) hA.hH.L_pos.le))
  by_contra h
  have : K * (a * V' (b * L)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hC.le
  linarith

/-- **Proposition 5** (SLP p. 530). Let `X = [a, b] ⊂ ℝ₊₊`, `π` satisfy Assumption 17.3, and
`H, V` satisfy Assumptions 17.1 and 17.4. Let `K C > 1` with `C = aV'(bL)`, `ε_K`, `B` as in
Proposition 4, and `F = {f ∈ C(X) : ε_K ≤ f ≤ B}`. Then `F` is closed and bounded, `T` maps `F`
into itself and is continuous and monotone there, and `T(F)` is equicontinuous. The iterates
`Tⁿf₀`, `f₀ ≡ ε_K`, and `Tⁿg₀`, `g₀ ≡ B`, converge in `C(X)` to fixed points `f ≤ g` in `F`
(so `T` has a fixed point), every fixed point `h ∈ F` satisfies `f ≤ h ≤ g`, and if `f = g` it
is the unique fixed point of `T` **in `F`** (see `proposition_5_literal_false` for why "in `F`"
cannot be dropped, and `proposition_5_corrected` for the correct global statement). -/
theorem proposition_5 (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a) (hab : a ≤ b)
    {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π] (hπ : MonoAssumption17_3 π)
    (h4 : MonoAssumption17_4 V' V'') {K : ℝ} (hK : 1 < K * (a * V' (b * L))) :
    0 < monoEpsK H' L K ∧ monoEpsK H' L K ≤ monoB a b H' V' L K ∧
      IsClosed (monoF a b H' V' L K) ∧ Bornology.IsBounded (monoF a b H' V' L K) ∧
      MapsTo (monoOLGOp π H' V' L) (monoF a b H' V' L K) (monoF a b H' V' L K) ∧
      ContinuousOn (monoOLGOp π H' V' L) (monoF a b H' V' L K) ∧
      MonotoneOn (monoOLGOp π H' V' L) (monoF a b H' V' L K) ∧
      UniformEquicontinuous (fun f : monoF a b H' V' L K => ⇑(monoOLGOp π H' V' L f)) ∧
      ∃ f ∈ monoF a b H' V' L K, ∃ g ∈ monoF a b H' V' L K,
        monoOLGOp π H' V' L f = f ∧ monoOLGOp π H' V' L g = g ∧
        Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop
          (𝓝 f) ∧
        Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
          (𝓝 g) ∧
        (∀ h ∈ monoF a b H' V' L K, monoOLGOp π H' V' L h = h → f ≤ h ∧ h ≤ g) ∧
        (f = g → ∀ h ∈ monoF a b H' V' L K, monoOLGOp π H' V' L h = h → h = f) := by
  have hK0 := monoOLG_K_pos hA ha hab hK
  obtain ⟨hε, -, -⟩ := hA.hH.epsK_spec hK0
  set ε := monoEpsK H' L K with hε_def
  set B := monoB a b H' V' L K with hB_def
  have hεKC : ε ≤ K * (a * V' (b * L)) * ε := by nlinarith
  have hb := fun {t y : ℝ} (ht : t ∈ Icc a b) (hy : ε ≤ y) => monoOLG_bounds hA ha hK0 ht hy
  have hεB : ε ≤ B := hεKC.trans ((hb ⟨le_rfl, hab⟩ le_rfl).2.1.trans (hb ⟨le_rfl, hab⟩ le_rfl).2.2)
  have hX : TotallyBounded (univ : Set (Icc a b)) := isCompact_univ.totallyBounded
  set Φ : ℝ × ℝ → ℝ := fun q => monoPhi V' (q.1 * monoZetaInv H' L q.2) with hΦ
  have hΦc : ContinuousOn Φ (Icc a b ×ˢ Icc ε B) :=
    hA.hV.continuousOn_phi.comp (continuous_fst.mul
      (hA.hH.zetaInv_continuous.comp continuous_snd)).continuousOn fun q hq =>
        mul_nonneg (ha.le.trans hq.1.1) (hA.hH.zetaInv_mem _).1
  have hGc : ContinuousOn (fun p : Icc a b × Icc a b × ℝ =>
      monoOLGKernel H' V' L a b p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ Icc ε B) :=
    (hA.hV.continuousOn_phi.comp_continuous
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).mul
        (hA.hH.zetaInv_continuous.comp (continuous_snd.comp continuous_snd)))
      fun p => (hA.hH.arg_mem ha p.2.1 p.2.2).1).continuousOn
  have hGD : ∀ x x' y, y ∈ Icc ε B → monoOLGKernel H' V' L a b x x' y ∈ Icc ε B :=
    fun x x' y hy => ⟨hεKC.trans (hb x'.2 hy.1).2.1, (hb x'.2 hy.1).2.2⟩
  have hG1 : ∀ e > 0, ∃ δ > 0, ∀ x z : Icc a b, dist x z < δ → ∀ x' y, y ∈ Icc ε B →
      |monoOLGKernel H' V' L a b x x' y - monoOLGKernel H' V' L a b z x' y| < e :=
    fun e he => ⟨1, one_pos, fun x z _ x' y _ => by simpa [monoOLGKernel] using he⟩
  have hG3 : ∀ e > 0, ∃ δ > 0, ∀ x x' y y', y ∈ Icc ε B → y' ∈ Icc ε B → |y - y'| < δ →
      |monoOLGKernel H' V' L a b x x' y - monoOLGKernel H' V' L a b x x' y'| < e := by
    intro e he
    have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hΦc
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc e he
    refine ⟨δ, hδ, fun x x' y y' hy hy' hyy => ?_⟩
    have := hδ' (x'.1, y) ⟨x'.2, hy⟩ (x'.1, y') ⟨x'.2, hy'⟩ (by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]; exact hyy)
    rwa [Real.dist_eq] at this
  have hGmono : ∀ x x' y y', y ∈ Icc ε B → y' ∈ Icc ε B → y ≤ y' →
      monoOLGKernel H' V' L a b x x' y ≤ monoOLGKernel H' V' L a b x x' y' :=
    fun x x' y y' _ _ hyy => (hA.hV.monotoneOn_phi h4) (hA.hH.arg_mem ha x' y).1
      (hA.hH.arg_mem ha x' y').1
      (mul_le_mul_of_nonneg_left (hA.hH.zetaInv_monotone hyy) (ha.le.trans x'.2.1))
  obtain ⟨hFc, hFb, hmaps, hcont, hmono, hequi, -, -, f, hf, g, hg, hTf, hTg, hfl, hgl, hbr⟩ :=
    kernelOp_monotone_fixedPoints hX hπ hεB hGc hGD hG1 hG3 hGmono
  refine ⟨hε, hεB, hFc, hFb, hmaps, hcont, hmono, hequi, f, hf, g, hg, hTf, hTg, hfl, hgl, hbr,
    fun hfg h hh hTh => ?_⟩
  subst hfg
  exact le_antisymm (hbr h hh hTh).2 (hbr h hh hTh).1

/-- **Every fixed point bounded away from zero lies in `F`** (NOTE to Proposition 5, p. 530;
derived). If `Th = h` and `h ≥ m > 0`, then `ε_K ≤ h ≤ B`. With `m₀ = inf h`: on `(0, ε_K)`
`ζ⁻¹(y) > Ky`, so `φ[x'ζ⁻¹(y)] ≥ KCy`; above `ε_K`, `φ[x'ζ⁻¹(y)] ≥ KCε_K`. Hence
`m₀ ≥ KC min(m₀, ε_K)`, and `KC > 1` forces `m₀ ≥ ε_K`; then `h ≤ B` by (5) of §17.4. -/
theorem monoOLG_fixedPoint_mem (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {K : ℝ} (hK : 1 < K * (a * V' (b * L)))
    {h : Icc a b →ᵇ ℝ} (hfix : monoOLGOp π H' V' L h = h) (hpos : ∃ m > 0, ∀ x, m ≤ h x) :
    h ∈ monoF a b H' V' L K := by
  have hK0 := monoOLG_K_pos hA ha hab hK
  obtain ⟨hε, -, hbelow⟩ := hA.hH.epsK_spec hK0
  have hbL : (0 : ℝ) ≤ b * L := mul_nonneg (ha.le.trans hab) hA.hH.L_pos.le
  have hVpos := hA.hV.V'_pos hbL
  obtain ⟨m, hm, hmh⟩ := hpos
  have hne : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have hbdd : BddBelow (range h) := ⟨m, by rintro _ ⟨x, rfl⟩; exact hmh x⟩
  have hm₀le : ∀ x, ⨅ x, h x ≤ h x := fun x => ciInf_le hbdd x
  have hm₀pos : 0 < ⨅ x, h x := lt_of_lt_of_le hm (le_ciInf hmh)
  have hfixx : ∀ x, h x = ∫ x', monoPhi V' (x'.1 * monoZetaInv H' L (h x')) ∂(π x) :=
    fun x => by
      conv_lhs => rw [← hfix]
      exact monoOLGOp_apply hA ha hπ h x
  obtain ⟨M, hM⟩ := hA.hV.exists_bound_phi (b * L)
  have hint : ∀ x, Integrable (fun x' => monoPhi V' (x'.1 * monoZetaInv H' L (h x'))) (π x) :=
    fun x => Integrable.of_bound
      (monoOLG_integrand_continuous hA ha h).measurable.aestronglyMeasurable
      M (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs]; exact hM _ (hA.hH.arg_mem ha x' _))
  have hKC : 0 < K * (a * V' (b * L)) := by linarith
  have hlow : ∀ x' : Icc a b, K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K) ≤
      monoPhi V' (x'.1 * monoZetaInv H' L (h x')) := by
    intro x'
    rcases le_or_gt (monoEpsK H' L K) (h x') with hy | hy
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hKC.le).trans
        (monoOLG_bounds hA ha hK0 x'.2 hy).2.1
    · have hy0 : 0 < h x' := lt_of_lt_of_le hm₀pos (hm₀le x')
      have hz := hbelow (h x') ⟨hy0, hy⟩
      have ht := hA.hH.arg_mem ha x' (h x')
      have hV'le : V' (b * L) ≤ V' (x'.1 * monoZetaInv H' L (h x')) :=
        hA.hV.strictAntiOn_V'.antitoneOn ht.1 hbL ht.2
      calc K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K)
          ≤ K * (a * V' (b * L)) * h x' :=
            mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (hm₀le x')) hKC.le
        _ = (a * (K * h x')) * V' (b * L) := by ring
        _ ≤ (x'.1 * monoZetaInv H' L (h x')) * V' (b * L) :=
            mul_le_mul_of_nonneg_right (mul_le_mul x'.2.1 hz.le (by positivity)
              (ha.le.trans x'.2.1)) hVpos.le
        _ ≤ (x'.1 * monoZetaInv H' L (h x')) * V' (x'.1 * monoZetaInv H' L (h x')) :=
            mul_le_mul_of_nonneg_left hV'le ht.1
        _ = monoPhi V' (x'.1 * monoZetaInv H' L (h x')) := rfl
  have hm₀ge : K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K) ≤ ⨅ x, h x :=
    le_ciInf fun x => by
      rw [hfixx x]
      calc K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K)
          = ∫ _, K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K) ∂(π x) := by simp
        _ ≤ _ := integral_mono (integrable_const _) (hint x) hlow
  have hεm : monoEpsK H' L K ≤ ⨅ x, h x := by
    refine le_of_not_gt fun hc => ?_
    rw [min_eq_left hc.le] at hm₀ge
    nlinarith
  intro x
  refine ⟨hεm.trans (hm₀le x), ?_⟩
  rw [hfixx x]
  calc ∫ x', monoPhi V' (x'.1 * monoZetaInv H' L (h x')) ∂(π x)
      ≤ ∫ _, monoB a b H' V' L K ∂(π x) :=
        integral_mono (hint x) (integrable_const _) fun x' =>
          (monoOLG_bounds hA ha hK0 x'.2 (hεm.trans (hm₀le x'))).2.2
    _ = monoB a b H' V' L K := by simp

/-- **Proposition 5, corrected** (SLP p. 530; see the NOTE). If the iterates from `f₀ ≡ ε_K` and
from `g₀ ≡ B` have the same limit `f`, then `f` is a fixed point of `T` with `f ≥ ε_K > 0`, and
it is the unique fixed point `h` of `T` with `inf h > 0`. -/
theorem proposition_5_corrected (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) (h4 : MonoAssumption17_4 V' V'') {K : ℝ}
    (hK : 1 < K * (a * V' (b * L))) {f : Icc a b →ᵇ ℝ}
    (hfl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop (𝓝 f))
    (hgl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
      (𝓝 f)) :
    monoOLGOp π H' V' L f = f ∧ f ∈ monoF a b H' V' L K ∧
      ∀ h, monoOLGOp π H' V' L h = h → (∃ m > 0, ∀ x, m ≤ h x) → h = f := by
  obtain ⟨-, -, -, -, -, -, -, -, f', hf', g', -, hTf', -, hf'l, hg'l, -, huniq⟩ :=
    proposition_5 hA ha hab hπ h4 hK
  have e1 : f' = f := tendsto_nhds_unique hf'l hfl
  have e2 : g' = f := tendsto_nhds_unique hg'l hgl
  subst e1
  subst e2
  exact ⟨hTf', hf', fun h hTh hpos =>
    huniq rfl h (monoOLG_fixedPoint_mem hA ha hab hπ hK hTh hpos) hTh⟩

/-- **Proposition 5, corrected**, strictly positive form: on the compact `X = [a, b]`, if
`f = g` then `f` is the unique strictly positive (continuous) fixed point of `T`. -/
theorem proposition_5_corrected' (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) (h4 : MonoAssumption17_4 V' V'') {K : ℝ}
    (hK : 1 < K * (a * V' (b * L))) {f : Icc a b →ᵇ ℝ}
    (hfl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop (𝓝 f))
    (hgl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
      (𝓝 f)) {h : Icc a b →ᵇ ℝ} (hTh : monoOLGOp π H' V' L h = h) (hpos : ∀ x, 0 < h x) :
    h = f := by
  have hne : (univ : Set (Icc a b)).Nonempty := ⟨⟨a, le_rfl, hab⟩, mem_univ _⟩
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn hne h.continuous.continuousOn
  exact (proposition_5_corrected hA ha hab hπ h4 hK hfl hgl).2.2 h hTh
    ⟨h x₀, hpos x₀, fun x => hx₀ (mem_univ x)⟩

/-- **Proposition 5 as stated is false whenever its hypothesis `f = g` holds** (SLP p. 530):
if `Tⁿε_K → f` and `TⁿB → f`, then `f` is *not* the unique fixed point of `T`, because the
zero function is another one. (`proposition_5_counterexample`, in `MonotoneOLGExamples`, shows
that the hypothesis `f = g` is satisfied in a concrete economy.) -/
theorem proposition_5_literal_false (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) (h4 : MonoAssumption17_4 V' V'') {K : ℝ}
    (hK : 1 < K * (a * V' (b * L))) {f : Icc a b →ᵇ ℝ}
    (hfl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop (𝓝 f))
    (hgl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
      (𝓝 f)) :
    ¬ ∀ h, monoOLGOp π H' V' L h = h → h = f := by
  intro H
  have h0 := H 0 (monoOLGOp_zero hA ha hπ)
  obtain ⟨-, hf, -⟩ := proposition_5_corrected hA ha hab hπ h4 hK hfl hgl
  obtain ⟨hε, -, -⟩ := hA.hH.epsK_spec (monoOLG_K_pos hA ha hab hK)
  have := (hf ⟨a, le_rfl, hab⟩).1
  rw [← h0] at this
  simp only [coe_zero, Pi.zero_apply] at this
  linarith

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A concrete OLG economy for §17.5: the counterexample to Proposition 5 as stated

SLP p. 530. The economy:

* labour disutility `H(l) = −l − log(1 − l)` on `[0, 1)` (`L = 1`), so `H'(l) = l/(1 − l)`,
  `H''(l) = 1/(1 − l)²` and `ζ(l) = l²/(1 − l)`;
* utility `V(y) = log(1 + y)`, so `V'(y) = 1/(1 + y)`, `V''(y) = −1/(1 + y)²`,
  `φ(y) = y/(1 + y)` and relative risk aversion `y/(1 + y) ≤ 1`;
* the one-point state space `X = [1, 1]` with `π(x, ·) = δ₁`; `K = 3` (`KC = 3/2 > 1`).

Results:

* `monoCexH_assumption17_1H`, `monoCexV_assumption17_1V`, `monoCex_assumption17_1`: Assumption 17.1.
* `monoCexV_assumption17_4`: Assumption 17.4. `monoCexπ_assumption17_3`: Assumption 17.3.
* `monoCex_fixedPoint_unique_pos`: the fixed points of `T` with `h > 0` are all equal (they solve
  `ζ(n) = φ(n)`, i.e. `n² + 2n − 1 = 0`).
* **`proposition_5_counterexample`**: in this economy all hypotheses of Proposition 5 hold, the
  iterates from `ε_K` and from `B` converge to the same `f` (the book's condition `f = g`), and yet
  `f` is not the unique fixed point of `T` (the zero function is another). So the book's
  conclusion "this function is the unique fixed point of `T`" is false, not merely vacuous.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-- `H(l) = −l − log(1 − l)`. -/
noncomputable def monoCexH (l : ℝ) : ℝ := -l - Real.log (1 - l)

/-- `H'(l) = l/(1 − l)`. -/
noncomputable def monoCexH' (l : ℝ) : ℝ := l / (1 - l)

/-- `H''(l) = 1/(1 − l)²`. -/
noncomputable def monoCexH'' (l : ℝ) : ℝ := 1 / (1 - l) ^ 2

/-- `V(y) = log(1 + y)`. -/
noncomputable def monoCexV (y : ℝ) : ℝ := Real.log (1 + y)

/-- `V'(y) = 1/(1 + y)`. -/
noncomputable def monoCexV' (y : ℝ) : ℝ := (1 + y)⁻¹

/-- `V''(y) = −1/(1 + y)²`. -/
noncomputable def monoCexV'' (y : ℝ) : ℝ := -((1 + y) ^ 2)⁻¹

/-- `H' = l/(1 − l)` is the derivative of `H`. -/
theorem hasDerivAt_monoCexH {l : ℝ} (hl : l < 1) : HasDerivAt monoCexH (monoCexH' l) l := by
  have h1 : (1 : ℝ) - l ≠ 0 := by linarith
  have h := (hasDerivAt_id' l).neg.sub (((hasDerivAt_id' l).const_sub 1).log h1)
  refine h.congr_deriv ?_
  rw [monoCexH']
  field_simp
  ring

/-- `H'' = 1/(1 − l)²` is the derivative of `H'`. -/
theorem hasDerivAt_monoCexH' {l : ℝ} (hl : l < 1) : HasDerivAt monoCexH' (monoCexH'' l) l := by
  have h1 : (1 : ℝ) - l ≠ 0 := by linarith
  have h := (hasDerivAt_id' l).div ((hasDerivAt_id' l).const_sub 1) h1
  refine h.congr_deriv ?_
  rw [monoCexH'']
  field_simp
  ring

/-- `H(l) = −l − log(1 − l)` satisfies the labour half of **Assumption 17.1** with `L = 1`. -/
theorem monoCexH_assumption17_1H : MonoAssumption17_1H monoCexH monoCexH' monoCexH'' 1 := by
  have hd : ∀ l ∈ Ico (0 : ℝ) 1, HasDerivAt monoCexH (monoCexH' l) l :=
    fun l hl => hasDerivAt_monoCexH hl.2
  have hcont : ContinuousOn monoCexH (Ico 0 1) := fun l hl =>
    (hd l hl).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Ico (0 : ℝ) 1), deriv monoCexH x = monoCexH' x :=
    fun x hx => by
    rw [interior_Ico] at hx
    exact (hd x (Ioo_subset_Ico_self hx)).deriv
  refine ⟨one_pos, fun l hl => (hd l hl).hasDerivWithinAt,
    fun l hl => (hasDerivAt_monoCexH' hl.2).hasDerivWithinAt, ?_, ?_, ?_, ?_,
    by simp [monoCexH'], ?_⟩
  · refine ContinuousOn.div continuousOn_const (by fun_prop) fun l hl => ?_
    have : (1 : ℝ) - l ≠ 0 := by linarith [hl.2]
    positivity
  · intro l hl
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - l by linarith [hl.2])
    rw [monoCexH]
    linarith
  · refine strictMonoOn_of_deriv_pos (convex_Ico 0 1) hcont fun x hx => ?_
    rw [hderiv x hx, monoCexH']
    rw [interior_Ico] at hx
    exact div_pos hx.1 (by linarith [hx.2])
  · refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ico 0 1) hcont fun x hx y hy hxy => ?_
    rw [hderiv x hx, hderiv y hy, monoCexH', monoCexH']
    rw [interior_Ico] at hx hy
    rw [div_lt_div_iff₀ (by linarith [hx.2]) (by linarith [hy.2])]
    nlinarith
  · have h1 : Tendsto (fun l : ℝ => 1 - l) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun l : ℝ => 1 - l) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      · filter_upwards [self_mem_nhdsWithin] with l hl
        exact sub_pos.2 (mem_Iio.1 hl)
    have h2 : Tendsto (fun l : ℝ => (1 - l)⁻¹) (𝓝[<] 1) atTop :=
      tendsto_inv_nhdsGT_zero.comp h1
    have := Tendsto.pos_mul_atTop one_pos (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) h2
    refine this.congr fun l => ?_
    simp [monoCexH', div_eq_mul_inv]

/-- `V' = 1/(1 + y)` is the derivative of `V`. -/
theorem hasDerivAt_monoCexV {y : ℝ} (hy : 0 ≤ y) : HasDerivAt monoCexV (monoCexV' y) y := by
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith
  have h := ((hasDerivAt_id' y).const_add 1).log h1
  refine h.congr_deriv ?_
  rw [monoCexV']
  field_simp

/-- `V'' = −1/(1 + y)²` is the derivative of `V'`. -/
theorem hasDerivAt_monoCexV' {y : ℝ} (hy : 0 ≤ y) : HasDerivAt monoCexV' (monoCexV'' y) y := by
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith
  have h := ((hasDerivAt_id' y).const_add 1).inv h1
  refine h.congr_deriv ?_
  rw [monoCexV'']
  field_simp

/-- `V(y) = log(1 + y)` satisfies the utility half of **Assumption 17.1**. -/
theorem monoCexV_assumption17_1V : MonoAssumption17_1V monoCexV monoCexV' monoCexV'' := by
  have hcont : ContinuousOn monoCexV (Ici 0) := fun y hy =>
    (hasDerivAt_monoCexV hy).continuousAt.continuousWithinAt
  refine ⟨fun y hy => (hasDerivAt_monoCexV hy).hasDerivWithinAt,
    fun y hy => (hasDerivAt_monoCexV' hy).hasDerivWithinAt, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_)
    have : (1 : ℝ) + y ≠ 0 := by linarith [mem_Ici.1 hy]
    positivity
  · intro y hy
    exact Real.log_nonneg (by linarith [mem_Ici.1 hy])
  · intro x hx y hy hxy
    exact Real.log_lt_log (by linarith [mem_Ici.1 hx]) (by linarith)
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hcont fun x hx y hy hxy => ?_
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_monoCexV (le_of_lt hx)).deriv, (hasDerivAt_monoCexV (le_of_lt hy)).deriv,
      monoCexV',
      monoCexV']
    exact inv_strictAntiOn (by rw [mem_Ioi]; linarith [mem_Ioi.1 hx])
      (by rw [mem_Ioi]; linarith [mem_Ioi.1 hy]) (by linarith)

/-- The economy satisfies **Assumption 17.1**. -/
theorem monoCex_assumption17_1 :
    MonoAssumption17_1 monoCexH monoCexH' monoCexH'' monoCexV monoCexV' monoCexV'' 1 :=
  ⟨monoCexH_assumption17_1H, monoCexV_assumption17_1V⟩

/-- Relative risk aversion of `log(1 + y)` is `y/(1 + y)`. -/
theorem monoRRA_monoCexV {y : ℝ} (hy : 0 ≤ y) :
    monoRRA monoCexV' monoCexV'' y = y / (1 + y) := by
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith
  rw [monoRRA, monoCexV', monoCexV'']
  field_simp

/-- `V(y) = log(1 + y)` satisfies **Assumption 17.4** (relative risk aversion `y/(1+y) ≤ 1`). -/
theorem monoCexV_assumption17_4 : MonoAssumption17_4 monoCexV' monoCexV'' := fun y hy => by
  rw [monoRRA_monoCexV hy, div_le_one (by linarith)]
  linarith

/-- The one-point state space `X = [1, 1]`. -/
abbrev monoCexX : Type := Icc (1 : ℝ) 1

/-- The unique point of `X`. -/
def monoCexX₁ : monoCexX := ⟨1, le_rfl, le_rfl⟩

/-- `π(x, ·) = δ₁`. -/
noncomputable abbrev monoCexπ : Kernel monoCexX monoCexX :=
  Kernel.const monoCexX (Measure.dirac monoCexX₁)

/-- `π(x, ·) = δ₁` satisfies **Assumption 17.3** (`π(x, ·)` does not depend on `x`). -/
theorem monoCexπ_assumption17_3 : MonoAssumption17_3 monoCexπ := fun ε hε =>
  ⟨1, one_pos, fun x x' _ n A _ => by simp [monoCexπ, hε.le]⟩

/-- In the example, a fixed point `h > 0` of `T` has `h(1) = ζ(n)` with `n² + 2n − 1 = 0`,
`n ∈ (0, 1)`. -/
theorem monoCex_fixedPoint_root {h : monoCexX →ᵇ ℝ}
    (hfix : monoOLGOp monoCexπ monoCexH' monoCexV' 1 h = h)
    (hpos : 0 < h monoCexX₁) :
    let n := monoZetaInv monoCexH' 1 (h monoCexX₁)
    n ∈ Ioo 0 1 ∧ n ^ 2 + 2 * n - 1 = 0 ∧ monoZeta monoCexH' n = h monoCexX₁ := by
  intro n
  have hA := monoCex_assumption17_1
  have hn := hA.hH.zetaInv_mem (h monoCexX₁)
  have hζ : monoZeta monoCexH' n = h monoCexX₁ := hA.hH.zeta_zetaInv hpos.le
  have hn0 : 0 < n := by
    rcases hn.1.eq_or_lt with e | e
    · have : monoZeta monoCexH' n = 0 := by rw [show n = 0 from e.symm, monoZeta_zero]
      linarith
    · exact e
  have happ := monoOLGOp_apply hA one_pos monoCexπ_assumption17_3 h monoCexX₁
  rw [hfix] at happ
  simp only [monoCexπ, Kernel.const_apply, integral_dirac] at happ
  have hx1 : (monoCexX₁ : ℝ) = 1 := rfl
  rw [hx1, one_mul] at happ
  -- `ζ(n) = φ(n)`
  have heq : monoZeta monoCexH' n = monoPhi monoCexV' n := hζ.trans happ
  have h1n : (1 : ℝ) - n ≠ 0 := by linarith [hn.2]
  have h1n' : (1 : ℝ) + n ≠ 0 := by linarith
  simp only [monoZeta, monoPhi, monoCexH', monoCexV'] at heq
  field_simp at heq
  exact ⟨⟨hn0, hn.2⟩, by linear_combination heq, hζ⟩

/-- In the example, all fixed points of `T` with `h(1) > 0` coincide. -/
theorem monoCex_fixedPoint_unique_pos {h k : monoCexX →ᵇ ℝ}
    (hh : monoOLGOp monoCexπ monoCexH' monoCexV' 1 h = h)
    (hk : monoOLGOp monoCexπ monoCexH' monoCexV' 1 k = k)
    (hhpos : 0 < h monoCexX₁) (hkpos : 0 < k monoCexX₁) : h = k := by
  obtain ⟨hn, hroot, hζ⟩ := monoCex_fixedPoint_root hh hhpos
  obtain ⟨kn, kroot, kζ⟩ := monoCex_fixedPoint_root hk hkpos
  have e : monoZetaInv monoCexH' 1 (h monoCexX₁) = monoZetaInv monoCexH' 1 (k monoCexX₁) := by
    have : (monoZetaInv monoCexH' 1 (h monoCexX₁) - monoZetaInv monoCexH' 1 (k monoCexX₁)) *
        (monoZetaInv monoCexH' 1 (h monoCexX₁) + monoZetaInv monoCexH' 1 (k monoCexX₁) + 2) = 0 :=
          by
      linear_combination hroot - kroot
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · linarith [hn.1, kn.1]
  have : h monoCexX₁ = k monoCexX₁ := by rw [← hζ, ← kζ, e]
  ext x
  have hx : x = monoCexX₁ := Subsingleton.elim _ _
  rw [hx, this]

/-- **Counterexample to Proposition 5 as stated** (SLP p. 530). In the economy above all the
hypotheses of Proposition 5 hold (Assumptions 17.1, 17.3, 17.4; `KC = 3/2 > 1` for `K = 3`),
the iterates of `T` from `f₀ ≡ ε_K` and from `g₀ ≡ B` converge to one and the same function
`f`
(the book's hypothesis `f = g`), and yet `f` is *not* the unique fixed point of `T`. -/
theorem proposition_5_counterexample :
    MonoAssumption17_1 monoCexH monoCexH' monoCexH'' monoCexV monoCexV' monoCexV'' 1 ∧
      MonoAssumption17_3 monoCexπ ∧
      MonoAssumption17_4 monoCexV' monoCexV'' ∧ 1 < 3 * (1 * monoCexV' (1 * 1)) ∧
      ∃ f : monoCexX →ᵇ ℝ,
        Tendsto (fun n => (monoOLGOp monoCexπ monoCexH' monoCexV' 1)^[n]
          (const _ (monoEpsK monoCexH' 1 3))) atTop (𝓝 f) ∧
        Tendsto (fun n => (monoOLGOp monoCexπ monoCexH' monoCexV' 1)^[n]
          (const _ (monoB 1 1 monoCexH' monoCexV' 1 3))) atTop (𝓝 f) ∧
        ¬ ∀ h, monoOLGOp monoCexπ monoCexH' monoCexV' 1 h = h → h = f := by
  have hA := monoCex_assumption17_1
  have hK : 1 < 3 * (1 * monoCexV' (1 * 1)) := by norm_num [monoCexV']
  obtain ⟨hε, -, -, -, -, -, -, -, f, hf, g, hg, hTf, hTg, hfl, hgl, -, -⟩ :=
    proposition_5 hA one_pos le_rfl monoCexπ_assumption17_3 monoCexV_assumption17_4 hK
  have hfg : f = g := monoCex_fixedPoint_unique_pos hTf hTg
    (lt_of_lt_of_le hε (hf monoCexX₁).1) (lt_of_lt_of_le hε (hg monoCexX₁).1)
  rw [← hfg] at hgl
  exact ⟨hA, monoCexπ_assumption17_3, monoCexV_assumption17_4, hK, f, hfl, hgl,
    proposition_5_literal_false hA one_pos le_rfl monoCexπ_assumption17_3
      monoCexV_assumption17_4 hK
      hfl hgl⟩

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Relative risk aversion: the claims on pp. 515, 530 and 541

SLP §17.2 (p. 515), §17.5 (p. 530) and §17.6 (p. 541) compare the restrictions on the relative
risk aversion `−yV″(y)/V′(y)` (`monoRRA`) used for the Contraction Mapping Theorem
(Assumption 17.2) and for monotone operators (Assumption 17.4).

* `monoRRA_zero`: `−yV″/V′ = 0` at `y = 0`, for any `V`.
* **pp. 515 and 530** ("strict monotonicity and concavity imply `0 < −yV″(y)/V′(y)` for all
  `y ∈ ℝ₊`"): false. `monoRRA_pos_counterexample` (`V = log(1 + y)`, ratio `0` at `y = 0`) and
  `monoRRA_interior_zero_counterexample` (`V(y) = 3 − e^{−y}(y² + 2y + 3)`, which satisfies
  Assumption 17.1 and has `V″(1) = 0`, so the ratio is `0` at the interior point `y = 1`).
  Corrected statement: `MonoAssumption17_1V.rra_nonneg` (the ratio is `≥ 0` on `ℝ₊`) and
  `MonoAssumption17_1V.exists_rra_pos` (it is `> 0` somewhere in every open interval, i.e. off a
  set with empty interior).
* **Assumption 17.2** (`MonoAssumption17_2`, p. 513): `1 − β ≤ −yV″/V′ ≤ 1 + β` on `ℝ₊` for some
  `β ∈ [0, 1)`. `not_monoAssumption17_2`: no `V` at all satisfies it (the ratio is `0` at `0`).
* **p. 541** ("Assumption 17.2 is a very mild strengthening of Assumption 17.4"): as literally
  stated, 17.2 implies 17.4 only vacuously (`monoAssumption17_2_imp_17_4`), while 17.4 does not
  imply 17.2 (`assumption17_4_not_imp_17_2_counterexample`). On `ℝ₊₊` (the repair of
  Assumption 17.2 with `V` smooth only on `ℝ₊₊`; `MonoAssumption17_2Pos`, `MonoAssumption17_4Pos`)
  **neither implies the other**: `V(y) = 2 arctan √y` has relative risk aversion
  `(1 + 3y)/(2(1 + y)) ∈ [1/2, 3/2)`, so it satisfies 17.2 with `β = 1/2` but violates 17.4
  (`assumption17_2Pos_not_imp_17_4Pos_counterexample`, with `monoArcV_repaired_utility`), and
  `V(y) = log(1 + y)` satisfies 17.4 but not 17.2
  (`assumption17_4Pos_not_imp_17_2Pos_counterexample`). Corrected statement
  (`monoAssumption17_2Pos_of_17_4Pos`): 17.4 plus a uniform lower bound `ε ≤ −yV″/V′` implies
  17.2 with `β = 1 − ε`.

**Correction (pp. 515, 530).** Assumption 17.1 gives only `−yV″/V′ ≥ 0`, with equality at
`y = 0` always and possibly at isolated `y > 0`.

**Correction (p. 541).** Assumptions 17.2 and 17.4 are not nested; what holds is
"17.4 + a uniform positive lower bound on relative risk aversion ⇒ 17.2".
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Filter Topology Set

/-- Relative risk aversion vanishes at `y = 0`, whatever `V` is. -/
theorem monoRRA_zero (V' V'' : ℝ → ℝ) : monoRRA V' V'' 0 = 0 := by simp [monoRRA]

/-- No `V` has strictly positive relative risk aversion at every `y ∈ ℝ₊`. -/
theorem monoRRA_not_forall_pos (V' V'' : ℝ → ℝ) : ¬ ∀ y, 0 ≤ y → 0 < monoRRA V' V'' y :=
  fun h => by simpa [monoRRA_zero] using h 0 le_rfl

/-- **Counterexample (SLP pp. 515 and 530).** `V(y) = log(1 + y)` satisfies the utility half of
Assumption 17.1, yet `0 < −yV″(y)/V′(y)` fails (at `y = 0`). -/
theorem monoRRA_pos_counterexample :
    MonoAssumption17_1V monoCexV monoCexV' monoCexV'' ∧
      ¬ ∀ y, 0 ≤ y → 0 < monoRRA monoCexV' monoCexV'' y :=
  ⟨monoCexV_assumption17_1V, monoRRA_not_forall_pos _ _⟩

/-- `W(y) = 3 − e^{−y}(y² + 2y + 3)`. -/
noncomputable def monoCexW (y : ℝ) : ℝ := 3 - Real.exp (-y) * (y ^ 2 + 2 * y + 3)

/-- `W'(y) = e^{−y}(1 + y²)`. -/
noncomputable def monoCexW' (y : ℝ) : ℝ := Real.exp (-y) * (1 + y ^ 2)

/-- `W''(y) = −e^{−y}(y − 1)²`. -/
noncomputable def monoCexW'' (y : ℝ) : ℝ := -(Real.exp (-y) * (y - 1) ^ 2)

/-- `W'` is the derivative of `W`. -/
theorem hasDerivAt_monoCexW (y : ℝ) : HasDerivAt monoCexW (monoCexW' y) y := by
  have h := ((hasDerivAt_neg y).exp.mul (((hasDerivAt_pow 2 y).add
    ((hasDerivAt_id' y).const_mul 2)).add_const 3)).const_sub 3
  refine h.congr_deriv ?_
  rw [monoCexW']
  simp only [Pi.add_apply]
  push_cast
  ring

/-- `W''` is the derivative of `W'`. -/
theorem hasDerivAt_monoCexW' (y : ℝ) : HasDerivAt monoCexW' (monoCexW'' y) y := by
  have h := (hasDerivAt_neg y).exp.mul ((hasDerivAt_pow 2 y).const_add 1)
  refine h.congr_deriv ?_
  rw [monoCexW'']
  push_cast
  ring

/-- `W'` is strictly decreasing on `ℝ₊` (its derivative `−e^{−y}(y − 1)²` vanishes only at `1`). -/
theorem monoCexW'_strictAntiOn : StrictAntiOn monoCexW' (Ici 0) := by
  have hc : Continuous monoCexW' := by unfold monoCexW'; fun_prop
  have hneg : ∀ x, x ≠ 1 → deriv monoCexW' x < 0 := fun x hx => by
    rw [(hasDerivAt_monoCexW' x).deriv, monoCexW'', neg_lt_zero]
    exact mul_pos (Real.exp_pos _) (by positivity)
  have h1 : StrictAntiOn monoCexW' (Icc 0 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 1) hc.continuousOn fun x hx => by
      rw [interior_Icc] at hx; exact hneg x hx.2.ne
  have h2 : StrictAntiOn monoCexW' (Ici 1) :=
    strictAntiOn_of_deriv_neg (convex_Ici 1) hc.continuousOn fun x hx => by
      rw [interior_Ici] at hx; exact hneg x (ne_of_gt hx)
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · exact h1 ⟨hx, hxy.le.trans hy1⟩ ⟨hy, hy1⟩ hxy
  rcases le_or_gt 1 x with hx1 | hx1
  · exact h2 hx1 (hx1.trans hxy.le) hxy
  · exact (h2 (le_refl (1 : ℝ)) hy1.le hy1).trans (h1 ⟨hx, hx1.le⟩ ⟨zero_le_one, le_rfl⟩ hx1)

/-- `W(y) = 3 − e^{−y}(y² + 2y + 3)` satisfies the utility half of **Assumption 17.1**. -/
theorem monoCexW_assumption17_1V : MonoAssumption17_1V monoCexW monoCexW' monoCexW'' := by
  have hc : Continuous monoCexW := by unfold monoCexW; fun_prop
  have hmono : StrictMonoOn monoCexW (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn fun x _ => by
      rw [(hasDerivAt_monoCexW x).deriv, monoCexW']
      positivity
  refine ⟨fun y _ => (hasDerivAt_monoCexW y).hasDerivWithinAt,
    fun y _ => (hasDerivAt_monoCexW' y).hasDerivWithinAt,
    (by unfold monoCexW''; fun_prop : Continuous monoCexW'').continuousOn, fun y hy => ?_, hmono,
    ?_⟩
  · have h0 : monoCexW 0 = 0 := by simp [monoCexW]
    rw [← h0]
    exact hmono.monotoneOn (mem_Ici.2 le_rfl) hy hy
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hc.continuousOn
      fun x hx y hy hxy => ?_
    rw [(hasDerivAt_monoCexW x).deriv, (hasDerivAt_monoCexW y).deriv]
    exact monoCexW'_strictAntiOn (interior_subset hx) (interior_subset hy) hxy

/-- **Counterexample (SLP pp. 515 and 530), interior point.** `W(y) = 3 − e^{−y}(y² + 2y + 3)`
satisfies the utility half of Assumption 17.1 and its relative risk aversion vanishes at the
interior point `y = 1` (`W″(1) = 0`): strict concavity does not give `V″ < 0`. -/
theorem monoRRA_interior_zero_counterexample :
    MonoAssumption17_1V monoCexW monoCexW' monoCexW'' ∧ monoRRA monoCexW' monoCexW'' 1 = 0 :=
  ⟨monoCexW_assumption17_1V, by simp [monoRRA, monoCexW'']⟩

variable {V V' V'' : ℝ → ℝ}

/-- **Corrected claim (pp. 515, 530).** Under Assumption 17.1, relative risk aversion is
nonnegative on `ℝ₊`. -/
theorem MonoAssumption17_1V.rra_nonneg (hV : MonoAssumption17_1V V V' V'') {y : ℝ}
    (hy : 0 ≤ y) : 0 ≤ monoRRA V' V'' y := by
  have hV'' : V'' y ≤ 0 := by
    have := (hV.strictAntiOn_V'.antitoneOn).derivWithin_nonpos (x := y)
    rwa [(hV.hasDeriv_V' y hy).derivWithin (uniqueDiffOn_Ici 0 y hy)] at this
  rw [monoRRA]
  exact div_nonneg (by nlinarith) (hV.V'_pos hy).le

/-- **Corrected claim (pp. 515, 530).** Under Assumption 17.1, relative risk aversion is
strictly positive somewhere in every open interval of `ℝ₊` (so it vanishes only on a set with
empty interior). -/
theorem MonoAssumption17_1V.exists_rra_pos (hV : MonoAssumption17_1V V V' V'') {u w : ℝ}
    (hu : 0 ≤ u) (huw : u < w) : ∃ y ∈ Ioo u w, 0 < monoRRA V' V'' y := by
  by_contra hcon
  have hzero : ∀ y ∈ Ioo u w, V'' y = 0 := fun y hy => by
    have hy0 : 0 < y := lt_of_le_of_lt hu hy.1
    have h1 : monoRRA V' V'' y ≤ 0 := le_of_not_gt fun h => hcon ⟨y, hy, h⟩
    have h2 := hV.rra_nonneg hy0.le
    have h3 : monoRRA V' V'' y = 0 := le_antisymm h1 h2
    rw [monoRRA, div_eq_zero_iff] at h3
    rcases h3 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (neg_eq_zero.1 h4) hy0.ne'
      · exact h4
    · exact absurd h3 (hV.V'_pos hy0.le).ne'
  set u' := (2 * u + w) / 3
  set w' := (u + 2 * w) / 3
  have hu' : u < u' := by simp only [u']; linarith
  have hw' : w' < w := by simp only [w']; linarith
  have huw' : u' < w' := by simp only [u', w']; linarith
  have hconst := constant_of_has_deriv_right_zero (f := V') (a := u') (b := w')
    (hV.continuousOn_V'.mono fun x hx => mem_Ici.2 (hu.trans (hu'.le.trans hx.1)))
    (fun x hx => by
      have hx0 : 0 ≤ x := hu.trans (hu'.le.trans hx.1)
      have := (hV.hasDeriv_V' x hx0).mono (Ici_subset_Ici.2 hx0)
      rwa [hzero x ⟨hu'.trans_le hx.1, hx.2.trans hw'⟩] at this)
    w' ⟨huw'.le, le_rfl⟩
  have := hV.strictAntiOn_V' (mem_Ici.2 (hu.trans hu'.le)) (mem_Ici.2 (hu.trans (hu'.trans
    huw').le)) huw'
  linarith

/-! ### Assumption 17.2 versus Assumption 17.4 (p. 541) -/

/-- **Assumption 17.2** (SLP p. 513): for some `β ∈ [0, 1)`,
`1 − β ≤ −yV″(y)/V′(y) ≤ 1 + β` for all `y ∈ ℝ₊`. -/
def MonoAssumption17_2 (V' V'' : ℝ → ℝ) : Prop :=
  ∃ β, 0 ≤ β ∧ β < 1 ∧ ∀ y, 0 ≤ y → 1 - β ≤ monoRRA V' V'' y ∧ monoRRA V' V'' y ≤ 1 + β

/-- Assumption 17.2 as stated (on `ℝ₊`) is never satisfied: the ratio is `0` at `y = 0`. -/
theorem not_monoAssumption17_2 (V' V'' : ℝ → ℝ) : ¬ MonoAssumption17_2 V' V'' := by
  rintro ⟨β, -, hβ, h⟩
  have := (h 0 le_rfl).1
  rw [monoRRA_zero] at this
  linarith

/-- As stated, Assumption 17.2 implies Assumption 17.4, but only vacuously. -/
theorem monoAssumption17_2_imp_17_4 (h : MonoAssumption17_2 V' V'') :
    MonoAssumption17_4 V' V'' :=
  absurd h (not_monoAssumption17_2 V' V'')

/-- **Counterexample (p. 541), literal version.** `V = log(1 + y)` satisfies Assumptions 17.1
and 17.4 but not Assumption 17.2: 17.4 does not imply 17.2. -/
theorem assumption17_4_not_imp_17_2_counterexample :
    MonoAssumption17_1V monoCexV monoCexV' monoCexV'' ∧ MonoAssumption17_4 monoCexV' monoCexV'' ∧
      ¬ MonoAssumption17_2 monoCexV' monoCexV'' :=
  ⟨monoCexV_assumption17_1V, monoCexV_assumption17_4, not_monoAssumption17_2 _ _⟩

/-- Assumption 17.2 on `ℝ₊₊` (the repair, with `V` twice differentiable only on `ℝ₊₊`). -/
def MonoAssumption17_2Pos (V' V'' : ℝ → ℝ) : Prop :=
  ∃ β, 0 ≤ β ∧ β < 1 ∧ ∀ y, 0 < y → 1 - β ≤ monoRRA V' V'' y ∧ monoRRA V' V'' y ≤ 1 + β

/-- Assumption 17.4 on `ℝ₊₊`. -/
def MonoAssumption17_4Pos (V' V'' : ℝ → ℝ) : Prop := ∀ y, 0 < y → monoRRA V' V'' y ≤ 1

/-- **Corrected claim (p. 541).** Assumption 17.4 together with a uniform positive lower bound
`ε ≤ −yV″/V′` implies Assumption 17.2 (with `β = 1 − ε`). -/
theorem monoAssumption17_2Pos_of_17_4Pos (h4 : MonoAssumption17_4Pos V' V'') {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlow : ∀ y, 0 < y → ε ≤ monoRRA V' V'' y) :
    MonoAssumption17_2Pos V' V'' :=
  ⟨1 - ε, by linarith, by linarith, fun y hy =>
    ⟨by linarith [hlow y hy], by linarith [h4 y hy]⟩⟩

/-- **Counterexample (p. 541), repaired version.** `V = log(1 + y)` satisfies Assumption 17.4
on `ℝ₊₊` but not Assumption 17.2 on `ℝ₊₊` (its relative risk aversion `y/(1 + y) → 0`). -/
theorem assumption17_4Pos_not_imp_17_2Pos_counterexample :
    MonoAssumption17_4Pos monoCexV' monoCexV'' ∧ ¬ MonoAssumption17_2Pos monoCexV' monoCexV'' := by
  refine ⟨fun y hy => monoCexV_assumption17_4 y hy.le, ?_⟩
  rintro ⟨β, -, hβ, h⟩
  have hy : (0 : ℝ) < (1 - β) / 2 := by linarith
  have := (h _ hy).1
  rw [monoRRA_monoCexV hy.le, le_div_iff₀ (by linarith)] at this
  nlinarith

/-- `V(y) = 2 arctan √y`. -/
noncomputable def monoArcV (y : ℝ) : ℝ := 2 * Real.arctan (√y)

/-- `V'(y) = 1/(√y (1 + y))` for `y > 0`. -/
noncomputable def monoArcV' (y : ℝ) : ℝ := (√y * (1 + y))⁻¹

/-- `V''(y)` for `y > 0`. -/
noncomputable def monoArcV'' (y : ℝ) : ℝ :=
  -(1 / (2 * √y) * (1 + y) + √y * 1) / (√y * (1 + y)) ^ 2

/-- `V'` is the derivative of `V = 2 arctan √y` on `ℝ₊₊`. -/
theorem hasDerivAt_monoArcV {y : ℝ} (hy : 0 < y) : HasDerivAt monoArcV (monoArcV' y) y := by
  have hs : 0 < √y := Real.sqrt_pos.2 hy
  have h := ((Real.hasDerivAt_sqrt hy.ne').arctan).const_mul 2
  refine h.congr_deriv ?_
  rw [monoArcV', Real.sq_sqrt hy.le]
  field_simp

/-- `V''` is the derivative of `V'` on `ℝ₊₊`. -/
theorem hasDerivAt_monoArcV' {y : ℝ} (hy : 0 < y) : HasDerivAt monoArcV' (monoArcV'' y) y := by
  have hs : 0 < √y := Real.sqrt_pos.2 hy
  have hne : √y * (1 + y) ≠ 0 := by positivity
  exact ((Real.hasDerivAt_sqrt hy.ne').mul ((hasDerivAt_id' y).const_add 1)).inv hne

/-- `V = 2 arctan √y` is a utility function in the repaired sense of Assumption 17.1: continuous
on `ℝ₊` with `V(0) = 0`, `V ≥ 0`, strictly increasing and strictly concave on `ℝ₊`, and twice
continuously differentiable on `ℝ₊₊` (with `V'(0+) = +∞`). -/
theorem monoArcV_repaired_utility :
    ContinuousOn monoArcV (Ici 0) ∧ monoArcV 0 = 0 ∧ (∀ y, 0 ≤ y → 0 ≤ monoArcV y) ∧
      StrictMonoOn monoArcV (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) monoArcV ∧
      (∀ y, 0 < y → HasDerivAt monoArcV (monoArcV' y) y) ∧
      (∀ y, 0 < y → HasDerivAt monoArcV' (monoArcV'' y) y) ∧ ContinuousOn monoArcV'' (Ioi 0) := by
  have hc : Continuous monoArcV := by unfold monoArcV; fun_prop
  have hmono : StrictMonoOn monoArcV (Ici 0) := fun x hx y _ hxy => by
    have := Real.arctan_strictMono (Real.sqrt_lt_sqrt (mem_Ici.1 hx) hxy)
    simp only [monoArcV]
    linarith
  refine ⟨hc.continuousOn, by simp [monoArcV], fun y hy => ?_, hmono, ?_,
    fun y hy => hasDerivAt_monoArcV hy, fun y hy => hasDerivAt_monoArcV' hy, ?_⟩
  · have := Real.arctan_strictMono.monotone (Real.sqrt_nonneg y)
    rw [Real.arctan_zero] at this
    simp only [monoArcV]
    linarith
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hc.continuousOn
      fun x hx y hy hxy => ?_
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_monoArcV hx).deriv, (hasDerivAt_monoArcV hy).deriv, monoArcV', monoArcV']
    have hsx : 0 < √x := Real.sqrt_pos.2 hx
    have hsy : 0 < √y := Real.sqrt_pos.2 hy
    have hsxy : √x < √y := Real.sqrt_lt_sqrt (le_of_lt hx) hxy
    rw [inv_lt_inv₀ (mul_pos hsy (by linarith [mem_Ioi.1 hy]))
      (mul_pos hsx (by linarith [mem_Ioi.1 hx]))]
    exact mul_lt_mul'' hsxy (by linarith) hsx.le (by linarith [mem_Ioi.1 hx])
  · intro y hy
    have hs : 0 < √y := Real.sqrt_pos.2 hy
    have hne : √y * (1 + y) ≠ 0 := (mul_pos hs (by linarith [mem_Ioi.1 hy])).ne'
    refine ContinuousAt.continuousWithinAt ?_
    unfold monoArcV''
    have hsq : ContinuousAt (fun x : ℝ => √x) y := Real.continuous_sqrt.continuousAt
    exact ((((continuousAt_const.div (continuousAt_const.mul hsq) (mul_pos two_pos hs).ne').mul
      (continuousAt_const.add continuousAt_id)).add (hsq.mul continuousAt_const)).neg).div
      ((hsq.mul (continuousAt_const.add continuousAt_id)).pow 2) (pow_ne_zero 2 hne)

/-- Relative risk aversion of `2 arctan √y` is `(1 + 3y)/(2(1 + y))` on `ℝ₊₊`. -/
theorem monoRRA_monoArcV {y : ℝ} (hy : 0 < y) :
    monoRRA monoArcV' monoArcV'' y = (1 + 3 * y) / (2 * (1 + y)) := by
  have hs : 0 < √y := Real.sqrt_pos.2 hy
  have hy' : y = √y ^ 2 := (Real.sq_sqrt hy.le).symm
  rw [monoRRA, monoArcV', monoArcV'']
  set s := √y
  rw [hy']
  field_simp
  ring

/-- **Counterexample (p. 541), repaired version.** `V = 2 arctan √y` satisfies Assumption 17.2
on `ℝ₊₊` (with `β = 1/2`: relative risk aversion lies in `[1/2, 3/2]`) but violates
Assumption 17.4 (relative risk aversion `7/6 > 1` at `y = 2`): 17.2 does not imply 17.4, so it
is not a "strengthening" of 17.4. -/
theorem assumption17_2Pos_not_imp_17_4Pos_counterexample :
    MonoAssumption17_2Pos monoArcV' monoArcV'' ∧ ¬ MonoAssumption17_4Pos monoArcV' monoArcV'' := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num, fun y hy => ?_⟩, fun h => ?_⟩
  · rw [monoRRA_monoArcV hy, le_div_iff₀ (by linarith), div_le_iff₀ (by linarith)]
    constructor <;> nlinarith
  · have := h 2 two_pos
    rw [monoRRA_monoArcV two_pos] at this
    norm_num at this

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contraction operators of the form `(Tf)(x) = ∫ G(x, x', f(x')) π(x, dx')`

SLP §17.2, pp. 508–512: the abstract operator (1), `(Tf)(x) = ∫ G(x, x', f(x')) π(x, dx')`, on
the space `F = olgF X D` of bounded continuous `f : X → D`, and its logarithmic version (3),
`(T̂g)(x) = ln ∫ G(x, x', e^{g(x')}) π(x, dx')`, on `F̂ = olgF X D̂`, `D̂ = ln D`. The Feller
property is `IsFellerKernel`; the hypotheses of Exercise 17.2a are bundled in `OLGOperatorHyp`.

* **Exercise 17.2a**, corrected (`ex_17_2a`, p. 509): for **compact** `X`, `Tf` is continuous with
  values in `D`; `olgTF : F → F`.
* **Exercise 17.2b** (`ex_17_2b`, p. 509): `F` is complete when `D` is closed.
* **Lemma 17.1** (`lemma_17_1`, p. 509): if `|G₃| ≤ β < 1`, `T` is a contraction of modulus `β`
  on `F` (`olgTF_lipschitz`), with a unique fixed point and `‖Tⁿf₀ − f*‖ ≤ βⁿ‖f₀ − f*‖`
  (Mathlib's `ContractingWith.fixedPoint`).
* **Exercise 17.4a**, corrected (`ex_17_4a`, p. 511), `olgThatF : F̂ → F̂`; **Exercise 17.4b**
  (`ex_17_4b`): `F̂` is complete. `olgDhat_eq`: `D̂ = exp⁻¹(D)` for `D ⊆ ℝ₊₊`, so `D̂` is closed
  and convex when `D` is (`olgDhat_isClosed`, `olgDhat_convex`).
* **Lemma 17.2** (`lemma_17_2`, p. 511): if `|y G₃/G| ≤ β < 1`, `T̂` is a contraction of modulus
  `β` on `F̂` (`olgThatF_lipschitz`); `lemma_17_2_fixedPoint` restates the conclusion for `T`:
  exactly one fixed point among bounded continuous `f : X → D`. `olgOpThat_log`:
  `T̂[ln f] = ln(Tf)` (p. 512).

**Correction (Exercises 17.2a and 17.4a).** As stated (general metric `X`, `G` merely
continuous) `T` need not map `F` into `F`, since `Tf` need not be bounded; the manual's "because
`X` is bounded" is not a hypothesis and would not suffice. Counterexamples:
`ex_17_2a_counterexample` (`X = D = ℝ`, `G = x`, `π(x, ·) = δ_x`, `Tf(x) = x`),
`ex_17_2a_counterexample_bounded` (`X = (0, 1]`, `G = 1/x`, `Tf(x) = 1/x`) and
`ex_17_4a_counterexample` (`X = ℝ`, `D = [1, ∞)`, `G = e^{|x|}`, `T̂0(x) = |x|`). The corrected
statements assume `X` compact, as in all of the book's applications; continuity of `Tf` then
follows from the uniform continuity of `G(·, ·, f(·))` on `X × X` and the Feller property.

**Remarks.** Lemmas 17.1–17.2 only need `G(x, x', ·)` differentiable within `D` (continuity of
`G₃` is not used). In the proof of Lemma 17.2 the bound is `β sup |g − h|`, not
`β sup (g − h)` (the book's typo); the weighted-average step is replaced by the equivalent
pointwise inequality `G(e^{g}) ≤ e^{β‖g − h‖} G(e^{h})`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-! ### The setting -/

/-- The **Feller property** of a transition function (SLP §8.1): `x ↦ ∫ f(x') π(x, dx')` is
continuous for every bounded continuous `f`. -/
def IsFellerKernel {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (κ : Kernel X X) :
    Prop :=
  ∀ f : X →ᵇ ℝ, Continuous fun x => ∫ y, f y ∂κ x

/-- The operator of §17.2 (1), `(Tf)(x) = ∫ G(x, x', f(x')) π(x, dx')`. -/
noncomputable def olgOpT {X : Type*} [MeasurableSpace X] (G : X → X → ℝ → ℝ) (κ : Kernel X X)
    (f : X → ℝ) (x : X) : ℝ :=
  ∫ x', G x x' (f x') ∂κ x

/-- The space `F` of bounded continuous functions `f : X → D`, with the sup-norm metric. -/
def olgF (X : Type*) [TopologicalSpace X] (D : Set ℝ) : Set (X →ᵇ ℝ) :=
  {f | ∀ x, f x ∈ D}

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] in
/-- The hypotheses of Exercise 17.2a (p. 509): `D` convex, `G : X × X × D → D` continuous, `π`
Feller. -/
structure OLGOperatorHyp (D : Set ℝ) (G : X → X → ℝ → ℝ) (κ : Kernel X X) : Prop where
  convex : Convex ℝ D
  cont : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) {p | p.2.2 ∈ D}
  mapsTo : ∀ x x', ∀ y ∈ D, G x x' y ∈ D
  feller : IsFellerKernel κ

/-- The identity (Dirac) transition function `π(x, ·) = δ_x` is Feller. -/
theorem isFellerKernel_deterministic_id {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSingletonClass X] :
    IsFellerKernel (Kernel.deterministic (id : X → X) measurable_id) := fun f => by
  simp only [Kernel.deterministic_apply, id, integral_dirac]
  exact f.continuous

/-! ### Exercise 17.2 (a): the book's statement is false -/

/-- **Correction (Exercise 17.2a), unbounded `X`.** With `X = D = ℝ`, `G(x, x', y) = x`
(continuous) and the Feller kernel `π(x, ·) = δ_x`, `(Tf)(x) = x` is unbounded, so `T` does not
map `F = C(ℝ)` into `F`. -/
theorem ex_17_2a_counterexample :
    IsFellerKernel (Kernel.deterministic (id : ℝ → ℝ) measurable_id) ∧
      Continuous (fun p : ℝ × ℝ × ℝ => p.1) ∧
      ¬ ∀ f : ℝ →ᵇ ℝ, ∃ g : ℝ →ᵇ ℝ, ∀ x,
        g x = olgOpT (fun x _ _ => x) (Kernel.deterministic id measurable_id) f x := by
  refine ⟨isFellerKernel_deterministic_id, continuous_fst, fun h => ?_⟩
  obtain ⟨g, hg⟩ := h 0
  have hT : ∀ x, olgOpT (fun x _ _ => x) (Kernel.deterministic id measurable_id)
      (0 : ℝ →ᵇ ℝ) x = x := fun x => by
    simp [olgOpT, Kernel.deterministic_apply]
  have h1 := g.norm_coe_le_norm (‖g‖ + 1)
  rw [hg, hT, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  linarith

/-- **Correction (Exercise 17.2a), bounded `X`.** A bounded state space does not help (contrary
to the manual's "X is bounded"): with `X = (0, 1]`, `D = ℝ`, `G(x, x', y) = 1/x` and
`π(x, ·) = δ_x`, `(Tf)(x) = 1/x` is unbounded. -/
theorem ex_17_2a_counterexample_bounded :
    IsFellerKernel (Kernel.deterministic (id : Ioc (0 : ℝ) 1 → Ioc (0 : ℝ) 1) measurable_id) ∧
      Continuous (fun p : Ioc (0 : ℝ) 1 × Ioc (0 : ℝ) 1 × ℝ => 1 / p.1.1) ∧
      ¬ ∀ f : Ioc (0 : ℝ) 1 →ᵇ ℝ, ∃ g : Ioc (0 : ℝ) 1 →ᵇ ℝ, ∀ x,
        g x = olgOpT (fun x _ _ => 1 / x.1) (Kernel.deterministic id measurable_id) f x := by
  refine ⟨isFellerKernel_deterministic_id, ?_, fun h => ?_⟩
  · refine continuous_const.div (continuous_subtype_val.comp continuous_fst) fun p => ?_
    exact p.1.2.1.ne'
  obtain ⟨g, hg⟩ := h 0
  have hT : ∀ x, olgOpT (fun x _ _ => 1 / x.1) (Kernel.deterministic id measurable_id)
      (0 : Ioc (0 : ℝ) 1 →ᵇ ℝ) x = 1 / x.1 := fun x => by
    simp [olgOpT, Kernel.deterministic_apply]
  have hpos : 0 < ‖g‖ + 2 := by positivity
  have hx : 1 / (‖g‖ + 2) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hpos).2 (by linarith [norm_nonneg g])⟩
  have h1 := g.norm_coe_le_norm ⟨_, hx⟩
  rw [hg, hT, one_div_one_div, Real.norm_eq_abs, abs_of_pos hpos] at h1
  linarith

/-! ### Exercise 17.2 (a), corrected: compact `X` -/

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {D : Set ℝ} {G : X → X → ℝ → ℝ} {κ : Kernel X X}

omit [BorelSpace X] in
/-- The integrand `(x, x') ↦ G(x, x', f(x'))` is continuous. -/
theorem continuous_olgIntegrand (hyp : OLGOperatorHyp D G κ) {f : X → ℝ} (hfc : Continuous f)
    (hf : ∀ x, f x ∈ D) : Continuous fun p : X × X => G p.1 p.2 (f p.2) :=
  hyp.cont.comp_continuous (continuous_fst.prodMk (continuous_snd.prodMk (hfc.comp continuous_snd)))
    fun p => hf p.2

/-- The slice `x' ↦ G(x, x', f(x'))` as a bounded continuous function (compact `X`). -/
noncomputable def olgSection [CompactSpace X] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) (x : X) : X →ᵇ ℝ :=
  mkOfCompact ⟨fun x' => G x x' (f x'),
    (continuous_olgIntegrand hyp hfc hf).comp (continuous_const.prodMk continuous_id)⟩

omit [BorelSpace X] in
/-- Evaluation of `olgSection`. -/
theorem olgSection_apply [CompactSpace X] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) (x x' : X) :
    olgSection hyp hfc hf x x' = G x x' (f x') :=
  rfl

/-- The integrand `x' ↦ G(x, x', f(x'))` is integrable for every finite measure. -/
theorem integrable_olgIntegrand [CompactSpace X] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) (x : X) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (fun x' => G x x' (f x')) μ :=
  (olgSection hyp hfc hf x).integrable μ

/-- **Exercise 17.2a, corrected** (p. 509). If `X` is a compact metric space, `D ⊆ ℝ` is
convex, `G : X × X × D → D` is continuous and `π` is Feller, then for every continuous
`f : X → D` the function `Tf` is continuous (hence bounded) with values in `D`. Continuity uses
the uniform continuity of `G(·, ·, f(·))` on `X × X` together with the Feller property;
`Tf(x) ∈ D` because `Tf(x)` lies between the minimum and maximum of `x' ↦ G(x, x', f(x'))`. -/
theorem ex_17_2a [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ) {f : X → ℝ}
    (hfc : Continuous f) (hf : ∀ x, f x ∈ D) :
    Continuous (olgOpT G κ f) ∧ ∀ x, olgOpT G κ f x ∈ D := by
  have hg := continuous_olgIntegrand hyp hfc hf
  set gx := olgSection hyp hfc hf with hgxdef
  have hT : ∀ x, olgOpT G κ f x = ∫ x', gx x x' ∂κ x := fun _ => rfl
  constructor
  · rw [continuous_iff_continuousAt]
    intro x₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous hg) (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1
      ((hyp.feller (gx x₀)).continuousAt (x := x₀)) (ε / 2) (half_pos hε)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩
    have e : olgOpT G κ f x - olgOpT G κ f x₀ = ∫ x', (gx x x' - gx x₀ x') ∂κ x +
        (∫ x', gx x₀ x' ∂κ x - ∫ x', gx x₀ x' ∂κ x₀) := by
      rw [hT, hT, integral_sub ((gx x).integrable _) ((gx x₀).integrable _)]
      ring
    have b1 : ‖∫ x', (gx x x' - gx x₀ x') ∂κ x‖ ≤ ε / 2 := by
      have := norm_integral_le_of_norm_le_const (μ := κ x) (C := ε / 2)
        (f := fun x' => gx x x' - gx x₀ x') (ae_of_all _ fun x' => by
          have h := h₁ (a := (x, x')) (b := (x₀, x')) (by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
            exact hx.trans_le (min_le_left _ _))
          rw [Real.dist_eq] at h
          rw [Real.norm_eq_abs]
          exact h.le)
      simpa using this
    have b2 := h₂ (hx.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at b2 ⊢
    rw [e]
    rw [Real.norm_eq_abs] at b1
    calc |∫ x', (gx x x' - gx x₀ x') ∂κ x + (∫ x', gx x₀ x' ∂κ x - ∫ x', gx x₀ x' ∂κ x₀)|
        ≤ |∫ x', (gx x x' - gx x₀ x') ∂κ x| +
          |∫ x', gx x₀ x' ∂κ x - ∫ x', gx x₀ x' ∂κ x₀| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt b1 b2
      _ = ε := add_halves ε
  · intro x
    have hne : (univ : Set X).Nonempty := ⟨x, mem_univ x⟩
    obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne (gx x).continuous.continuousOn
    obtain ⟨M, -, hM⟩ := isCompact_univ.exists_isMaxOn hne (gx x).continuous.continuousOn
    have hlow : gx x m ≤ ∫ x', gx x x' ∂κ x := by
      have := integral_mono (integrable_const (gx x m)) ((gx x).integrable (κ x))
        (fun x' => isMinOn_iff.1 hm x' (mem_univ x'))
      simpa using this
    have hup : ∫ x', gx x x' ∂κ x ≤ gx x M := by
      have := integral_mono ((gx x).integrable (κ x)) (integrable_const (gx x M))
        (fun x' => isMaxOn_iff.1 hM x' (mem_univ x'))
      simpa using this
    rw [hT]
    exact hyp.convex.ordConnected.out (hyp.mapsTo _ _ _ (hf m)) (hyp.mapsTo _ _ _ (hf M))
      ⟨hlow, hup⟩

/-- The operator `T : F → F` of (1), for compact `X` (Exercise 17.2a). -/
noncomputable def olgTF [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (f : olgF X D) : olgF X D :=
  ⟨mkOfCompact ⟨olgOpT G κ f.1, (ex_17_2a hyp f.1.continuous f.2).1⟩,
    (ex_17_2a hyp f.1.continuous f.2).2⟩

/-- Evaluation of `olgTF`. -/
theorem olgTF_apply [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (f : olgF X D) (x : X) : (olgTF hyp f).1 x = olgOpT G κ f.1 x :=
  rfl

/-! ### Exercise 17.2 (b) -/

/-- `F` is closed in `C(X)` when `D` is closed. -/
theorem isClosed_olgF {Y : Type*} [TopologicalSpace Y] (hD : IsClosed D) :
    IsClosed (olgF Y D) := by
  have : olgF Y D = ⋂ y, (fun f : Y →ᵇ ℝ => f y) ⁻¹' D := by
    ext f; simp [olgF]
  rw [this]
  exact isClosed_iInter fun y => hD.preimage (continuous_eval_const y)

/-- **Exercise 17.2b** (p. 509). If `D` is closed, `F` with the sup norm is complete. -/
theorem ex_17_2b {Y : Type*} [TopologicalSpace Y] (hD : IsClosed D) :
    CompleteSpace (olgF Y D) :=
  (isClosed_olgF hD).isComplete.completeSpace_coe

/-! ### Lemma 17.1 -/

/-- Under (2), `T` is Lipschitz with constant `β` on `F`. -/
theorem olgTF_lipschitz [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    {G3 : X → X → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |G3 x x' y| ≤ β) :
    LipschitzWith β.toNNReal (olgTF hyp) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  simp only [Subtype.dist_eq]
  rw [Real.coe_toNNReal β hβ0, BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)]
  intro x
  rw [olgTF_apply, olgTF_apply, Real.dist_eq, olgOpT, olgOpT,
    ← integral_sub (integrable_olgIntegrand hyp f.1.continuous f.2 x _)
      (integrable_olgIntegrand hyp g.1.continuous g.2 x _)]
  have hlip : ∀ x', ‖G x x' (f.1 x') - G x x' (g.1 x')‖ ≤ β * dist f.1 g.1 := fun x' => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hG3 x x')
      (fun y hy => by rw [Real.norm_eq_abs]; exact hbound x x' y hy) hyp.convex (g.2 x') (f.2 x')
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs]
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hβ0)
    rw [← Real.dist_eq]
    exact dist_coe_le_dist x'
  have := norm_integral_le_of_norm_le_const (μ := κ x) (ae_of_all _ hlip)
  simpa using this

/-- **Lemma 17.1** (p. 509). Let `X` be compact (see the correction to Exercise 17.2a), `D`
closed, convex and nonempty, `G : X × X × D → D` continuous, `π` Feller, and suppose
`G(x, x', ·)` is differentiable on `D` with `|G₃| ≤ β < 1` (2). Then `T` has a unique fixed
point `f* ∈ F`, and `‖Tⁿ f₀ − f*‖ ≤ βⁿ ‖f₀ − f*‖`. (Continuity of `G₃` is not needed.) -/
theorem lemma_17_1 [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDc : IsClosed D) (hDne : D.Nonempty) {G3 : X → X → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |G3 x x' y| ≤ β) :
    ∃ fstar : olgF X D, olgTF hyp fstar = fstar ∧
      (∀ f : olgF X D, olgTF hyp f = f → f = fstar) ∧
      ∀ (f₀ : olgF X D) (n : ℕ), dist ((olgTF hyp)^[n] f₀) fstar ≤ β ^ n * dist f₀ fstar := by
  have : CompleteSpace (olgF X D) := ex_17_2b hDc
  obtain ⟨y₀, hy₀⟩ := hDne
  have : Nonempty (olgF X D) := ⟨⟨const X y₀, fun _ => hy₀⟩⟩
  have hK : ContractingWith β.toNNReal (olgTF hyp) :=
    ⟨Real.toNNReal_lt_one.2 hβ1, olgTF_lipschitz hyp hβ0 hG3 hbound⟩
  refine ⟨ContractingWith.fixedPoint _ hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun f hf => ContractingWith.fixedPoint_unique hK hf, fun f₀ n => ?_⟩
  have h1 := (hK.2.iterate n).dist_le_mul f₀ (ContractingWith.fixedPoint _ hK)
  rw [((ContractingWith.fixedPoint_isFixedPt hK).iterate n).eq, NNReal.coe_pow,
    Real.coe_toNNReal β hβ0] at h1
  exact h1

/-! ### The logarithmic operator: Exercise 17.4 -/

/-- `D̂ = ln D` (p. 510). -/
def olgDhat (D : Set ℝ) : Set ℝ := Real.log '' D

/-- For `D ⊆ ℝ₊₊`, `D̂ = exp⁻¹(D)`. -/
theorem olgDhat_eq (hDpos : D ⊆ Ioi 0) : olgDhat D = Real.exp ⁻¹' D := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    simp only [mem_preimage, Real.exp_log (hDpos hd)]
    exact hd
  · intro hz
    exact ⟨Real.exp z, hz, Real.log_exp z⟩

/-- `e^z ∈ D` for `z ∈ D̂`. -/
theorem exp_mem_of_mem_olgDhat (hDpos : D ⊆ Ioi 0) {z : ℝ} (hz : z ∈ olgDhat D) :
    Real.exp z ∈ D := by
  rw [olgDhat_eq hDpos] at hz
  exact hz

/-- `D̂` is closed when `D ⊆ ℝ₊₊` is closed. -/
theorem olgDhat_isClosed (hD : IsClosed D) (hDpos : D ⊆ Ioi 0) : IsClosed (olgDhat D) := by
  rw [olgDhat_eq hDpos]
  exact hD.preimage Real.continuous_exp

/-- `D̂` is convex when `D ⊆ ℝ₊₊` is convex. -/
theorem olgDhat_convex (hD : Convex ℝ D) (hDpos : D ⊆ Ioi 0) : Convex ℝ (olgDhat D) := by
  rw [olgDhat_eq hDpos]
  refine Set.OrdConnected.convex ⟨fun a ha b hb z hz => ?_⟩
  exact hD.ordConnected.out ha hb ⟨Real.exp_le_exp.2 hz.1, Real.exp_le_exp.2 hz.2⟩

/-- The logarithmic operator (3), `(T̂g)(x) = ln ∫ G(x, x', e^{g(x')}) π(x, dx')`. -/
noncomputable def olgOpThat {Y : Type*} [MeasurableSpace Y] (G : Y → Y → ℝ → ℝ)
    (κ : Kernel Y Y) (g : Y → ℝ) (x : Y) : ℝ :=
  Real.log (olgOpT G κ (fun x' => Real.exp (g x')) x)

/-- `T̂[ln f] = ln (Tf)` for `f > 0` (p. 512). -/
theorem olgOpThat_log {Y : Type*} [MeasurableSpace Y] (G : Y → Y → ℝ → ℝ) (κ : Kernel Y Y)
    {f : Y → ℝ} (hf : ∀ x, 0 < f x) (x : Y) :
    olgOpThat G κ (fun x' => Real.log (f x')) x = Real.log (olgOpT G κ f x) := by
  simp only [olgOpThat, Real.exp_log (hf _)]

/-- **Correction (Exercise 17.4a).** The same gap as in Exercise 17.2a: with `X = ℝ`,
`D = [1, ∞)` (closed, convex, `⊆ ℝ₊₊`), `G(x, x', y) = e^{|x|}` (continuous, `D`-valued) and
`π(x, ·) = δ_x`, the function `g = 0 ∈ F̂` has `T̂g(x) = |x|`, which is unbounded. -/
theorem ex_17_4a_counterexample :
    IsFellerKernel (Kernel.deterministic (id : ℝ → ℝ) measurable_id) ∧
      Continuous (fun p : ℝ × ℝ × ℝ => Real.exp |p.1|) ∧
      (∀ x : ℝ, Real.exp |x| ∈ Ici (1 : ℝ)) ∧ (0 : ℝ) ∈ olgDhat (Ici 1) ∧
      ¬ ∃ g : ℝ →ᵇ ℝ, ∀ x, g x = olgOpThat (fun x _ _ => Real.exp |x|)
        (Kernel.deterministic id measurable_id) (fun _ => 0) x := by
  refine ⟨isFellerKernel_deterministic_id, by fun_prop, fun x => ?_, ⟨1, mem_Ici.2 le_rfl,
    Real.log_one⟩, fun ⟨g, hg⟩ => ?_⟩
  · exact mem_Ici.2 (Real.one_le_exp (abs_nonneg x))
  have hT : ∀ x, olgOpThat (fun x _ _ => Real.exp |x|) (Kernel.deterministic id measurable_id)
      (fun _ => 0) x = |x| := fun x => by
    simp [olgOpThat, olgOpT, Kernel.deterministic_apply]
  have h1 := g.norm_coe_le_norm (‖g‖ + 1)
  rw [hg, hT, Real.norm_eq_abs, abs_abs, abs_of_pos (by positivity)] at h1
  linarith

/-- **Exercise 17.4a, corrected** (p. 511): for compact `X` and `D ⊆ ℝ₊₊`, `T̂g` is continuous
with values in `D̂` for every continuous `g : X → D̂`. -/
theorem ex_17_4a [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) {g : X → ℝ} (hgc : Continuous g) (hg : ∀ x, g x ∈ olgDhat D) :
    Continuous (olgOpThat G κ g) ∧ ∀ x, olgOpThat G κ g x ∈ olgDhat D := by
  have hf : ∀ x, Real.exp (g x) ∈ D := fun x => exp_mem_of_mem_olgDhat hDpos (hg x)
  obtain ⟨hc, hD⟩ := ex_17_2a hyp (Real.continuous_exp.comp hgc) hf
  exact ⟨hc.log fun x => (hDpos (hD x)).ne', fun x => ⟨_, hD x, rfl⟩⟩

/-- The operator `T̂ : F̂ → F̂` (Exercise 17.4a), for compact `X`. -/
noncomputable def olgThatF [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) (g : olgF X (olgDhat D)) : olgF X (olgDhat D) :=
  ⟨mkOfCompact ⟨olgOpThat G κ g.1, (ex_17_4a hyp hDpos g.1.continuous g.2).1⟩,
    (ex_17_4a hyp hDpos g.1.continuous g.2).2⟩

/-- Evaluation of `olgThatF`. -/
theorem olgThatF_apply [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) (g : olgF X (olgDhat D)) (x : X) :
    (olgThatF hyp hDpos g).1 x = olgOpThat G κ g.1 x :=
  rfl

/-- **Exercise 17.4b** (p. 511). If `D ⊆ ℝ₊₊` is closed, `F̂` is complete. -/
theorem ex_17_4b {Y : Type*} [TopologicalSpace Y] (hD : IsClosed D) (hDpos : D ⊆ Ioi 0) :
    CompleteSpace (olgF Y (olgDhat D)) :=
  ex_17_2b (olgDhat_isClosed hD hDpos)

/-! ### Lemma 17.2 -/

omit [BorelSpace X] in
/-- Under (4), `z ↦ ln G(x, x', e^z)` is `β`-Lipschitz on `D̂` (mean value theorem). -/
theorem abs_log_G_sub_le (hyp : OLGOperatorHyp D G κ) (hDpos : D ⊆ Ioi 0)
    {G3 : X → X → ℝ → ℝ} {β : ℝ}
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) (x x' : X) {z w : ℝ}
    (hz : z ∈ olgDhat D) (hw : w ∈ olgDhat D) :
    |Real.log (G x x' (Real.exp z)) - Real.log (G x x' (Real.exp w))| ≤ β * |z - w| := by
  have hmaps : MapsTo Real.exp (olgDhat D) D := fun _ hu => exp_mem_of_mem_olgDhat hDpos hu
  have hder : ∀ u ∈ olgDhat D, HasDerivWithinAt (fun u => Real.log (G x x' (Real.exp u)))
      (G3 x x' (Real.exp u) * Real.exp u / G x x' (Real.exp u)) (olgDhat D) u := fun u hu => by
    have h1 := (hG3 x x' (Real.exp u) (hmaps hu)).comp u
      (Real.hasDerivAt_exp u).hasDerivWithinAt hmaps
    exact h1.log (hDpos (hyp.mapsTo x x' _ (hmaps hu))).ne'
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder
    (fun u hu => by
      rw [Real.norm_eq_abs, mul_comm]
      exact hbound x x' _ (hmaps hu))
    (olgDhat_convex hyp.convex hDpos) hw hz
  simpa [Real.norm_eq_abs] using this

/-- Under (4), `T̂` is Lipschitz with constant `β` on `F̂`. The book's weighted-average step is
replaced by the equivalent pointwise bound `G(e^{g}) ≤ e^{β‖g−h‖} G(e^{h})`. -/
theorem olgThatF_lipschitz [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDpos : D ⊆ Ioi 0) {G3 : X → X → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) :
    LipschitzWith β.toNNReal (olgThatF hyp hDpos) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  simp only [Subtype.dist_eq]
  rw [Real.coe_toNNReal β hβ0, BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)]
  intro x
  set d := dist g.1 h.1
  have hmem : ∀ (k : olgF X (olgDhat D)) x', Real.exp (k.1 x') ∈ D := fun k x' =>
    exp_mem_of_mem_olgDhat hDpos (k.2 x')
  set A : X → ℝ := fun x' => G x x' (Real.exp (g.1 x'))
  set B : X → ℝ := fun x' => G x x' (Real.exp (h.1 x'))
  have hA : ∀ x', 0 < A x' := fun x' => hDpos (hyp.mapsTo _ _ _ (hmem g x'))
  have hB : ∀ x', 0 < B x' := fun x' => hDpos (hyp.mapsTo _ _ _ (hmem h x'))
  have hlog : ∀ x', |Real.log (A x') - Real.log (B x')| ≤ β * d := fun x' =>
    (abs_log_G_sub_le hyp hDpos hG3 hbound x x' (g.2 x') (h.2 x')).trans
      (mul_le_mul_of_nonneg_left (by rw [← Real.dist_eq]; exact dist_coe_le_dist x') hβ0)
  have hAB : ∀ x', A x' ≤ Real.exp (β * d) * B x' := fun x' => by
    have := (abs_sub_le_iff.1 (hlog x')).1
    rw [← Real.exp_log (hA x'), ← Real.exp_log (hB x'), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hBA : ∀ x', B x' ≤ Real.exp (β * d) * A x' := fun x' => by
    have := (abs_sub_le_iff.1 (hlog x')).2
    rw [← Real.exp_log (hA x'), ← Real.exp_log (hB x'), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have iA : Integrable A (κ x) :=
    integrable_olgIntegrand hyp (Real.continuous_exp.comp g.1.continuous) (hmem g) x _
  have iB : Integrable B (κ x) :=
    integrable_olgIntegrand hyp (Real.continuous_exp.comp h.1.continuous) (hmem h) x _
  have pA : 0 < ∫ x', A x' ∂κ x := by
    refine (integral_pos_iff_support_of_nonneg (fun x' => (hA x').le) iA).2 ?_
    rw [show Function.support A = univ from
      eq_univ_of_forall fun x' => Function.mem_support.2 (hA x').ne', measure_univ]
    exact one_pos
  have pB : 0 < ∫ x', B x' ∂κ x := by
    refine (integral_pos_iff_support_of_nonneg (fun x' => (hB x').le) iB).2 ?_
    rw [show Function.support B = univ from
      eq_univ_of_forall fun x' => Function.mem_support.2 (hB x').ne', measure_univ]
    exact one_pos
  have IAB : ∫ x', A x' ∂κ x ≤ Real.exp (β * d) * ∫ x', B x' ∂κ x := by
    rw [← integral_const_mul]
    exact integral_mono iA (iB.const_mul _) hAB
  have IBA : ∫ x', B x' ∂κ x ≤ Real.exp (β * d) * ∫ x', A x' ∂κ x := by
    rw [← integral_const_mul]
    exact integral_mono iB (iA.const_mul _) hBA
  have L1 := Real.log_le_log pA IAB
  have L2 := Real.log_le_log pB IBA
  rw [Real.log_mul (Real.exp_pos _).ne' pB.ne', Real.log_exp] at L1
  rw [Real.log_mul (Real.exp_pos _).ne' pA.ne', Real.log_exp] at L2
  rw [olgThatF_apply, olgThatF_apply, Real.dist_eq, abs_sub_le_iff]
  exact ⟨by simp only [olgOpThat, olgOpT]; linarith, by simp only [olgOpThat, olgOpT]; linarith⟩

/-- **Lemma 17.2** (p. 511). Let `X` be compact, `D ⊆ ℝ₊₊` closed, convex and nonempty,
`G : X × X × D → D` continuous, `π` Feller, `G(x, x', ·)` differentiable on `D`, and
`|y G₃(x, x', y)/G(x, x', y)| ≤ β < 1` (4). Then `T̂` has a unique fixed point `g* ∈ F̂` and
`‖T̂ⁿ g₀ − g*‖ ≤ βⁿ ‖g₀ − g*‖`. -/
theorem lemma_17_2 [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDc : IsClosed D) (hDne : D.Nonempty) (hDpos : D ⊆ Ioi 0) {G3 : X → X → ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) :
    ∃ gstar : olgF X (olgDhat D), olgThatF hyp hDpos gstar = gstar ∧
      (∀ g : olgF X (olgDhat D), olgThatF hyp hDpos g = g → g = gstar) ∧
      ∀ (g₀ : olgF X (olgDhat D)) (n : ℕ),
        dist ((olgThatF hyp hDpos)^[n] g₀) gstar ≤ β ^ n * dist g₀ gstar := by
  have : CompleteSpace (olgF X (olgDhat D)) := ex_17_4b hDc hDpos
  obtain ⟨y₀, hy₀⟩ := hDne
  have : Nonempty (olgF X (olgDhat D)) := ⟨⟨const X (Real.log y₀), fun _ => ⟨y₀, hy₀, rfl⟩⟩⟩
  have hK : ContractingWith β.toNNReal (olgThatF hyp hDpos) :=
    ⟨Real.toNNReal_lt_one.2 hβ1, olgThatF_lipschitz hyp hDpos hβ0 hG3 hbound⟩
  refine ⟨ContractingWith.fixedPoint _ hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun g hg => ContractingWith.fixedPoint_unique hK hg, fun g₀ n => ?_⟩
  have h1 := (hK.2.iterate n).dist_le_mul g₀ (ContractingWith.fixedPoint _ hK)
  rw [((ContractingWith.fixedPoint_isFixedPt hK).iterate n).eq, NNReal.coe_pow,
    Real.coe_toNNReal β hβ0] at h1
  exact h1

/-- **Lemma 17.2, in terms of `T`.** Under the hypotheses of Lemma 17.2, `T` has exactly one
fixed point among the bounded continuous `f : X → D`: `f* = e^{g*}` (`f` is a fixed point of
`T` iff `ln f` is a fixed point of `T̂`). -/
theorem lemma_17_2_fixedPoint [CompactSpace X] [IsMarkovKernel κ] (hyp : OLGOperatorHyp D G κ)
    (hDc : IsClosed D) (hDne : D.Nonempty) (hDpos : D ⊆ Ioi 0) {G3 : X → X → ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hG3 : ∀ x x', ∀ y ∈ D, HasDerivWithinAt (G x x') (G3 x x' y) D y)
    (hbound : ∀ x x', ∀ y ∈ D, |y * G3 x x' y / G x x' y| ≤ β) :
    ∃! f : X →ᵇ ℝ, (∀ x, f x ∈ D) ∧ ∀ x, f x = olgOpT G κ f x := by
  obtain ⟨gs, hfix, huniq, -⟩ := lemma_17_2 hyp hDc hDne hDpos hβ0 hβ1 hG3 hbound
  have hmem : ∀ x, Real.exp (gs.1 x) ∈ D := fun x => exp_mem_of_mem_olgDhat hDpos (gs.2 x)
  let fs : X →ᵇ ℝ := mkOfCompact ⟨fun x => Real.exp (gs.1 x),
    Real.continuous_exp.comp gs.1.continuous⟩
  have hfs : ∀ x, fs x = Real.exp (gs.1 x) := fun _ => rfl
  refine ⟨fs, ⟨fun x => by rw [hfs]; exact hmem x, fun x => ?_⟩, ?_⟩
  · have h1 : (olgThatF hyp hDpos gs).1 x = gs.1 x := by rw [hfix]
    rw [olgThatF_apply, olgOpThat] at h1
    have hpos : 0 < olgOpT G κ (fun x' => Real.exp (gs.1 x')) x :=
      hDpos ((ex_17_2a hyp (Real.continuous_exp.comp gs.1.continuous) hmem).2 x)
    rw [hfs, ← h1, Real.exp_log hpos]
    rfl
  · rintro f ⟨hfD, hfix'⟩
    have hfpos : ∀ x, 0 < f x := fun x => hDpos (hfD x)
    let lf : olgF X (olgDhat D) := ⟨mkOfCompact ⟨fun x => Real.log (f x),
      f.continuous.log fun x => (hfpos x).ne'⟩, fun x => ⟨f x, hfD x, rfl⟩⟩
    have hlf : olgThatF hyp hDpos lf = lf := by
      apply Subtype.ext
      ext x
      rw [olgThatF_apply]
      change olgOpThat G κ (fun x' => Real.log (f x')) x = Real.log (f x)
      rw [olgOpThat_log G κ hfpos x, ← hfix' x]
    have := huniq lf hlf
    ext x
    rw [hfs, ← this]
    change f x = Real.exp (Real.log (f x))
    rw [Real.exp_log (hfpos x)]

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An overlapping-generations model

SLP §17.1, pp. 502–508.

SLP §17.1, pp. 502–508. The state space is `X = [a, b]` with `0 < a`, a transition function is
a Markov kernel `π : Kernel X X`, and the derivatives `H'`, `H''`, `V'`, `V''` are explicit
functions (derivatives within `[0, L)` and `[0, ∞)`, so one-sided at `0`).

* **Assumption 17.1** (`Assumption17_1`, p. 503), split into a labour part `Assumption17_1H`
  and a utility part `Assumption17_1V`, with the derived facts used throughout (`H'` strictly
  increasing and positive on `(0, L)`, `H'' ≥ 0`, `V' > 0` strictly decreasing, continuity).
* **Exercise 17.1** (`ex_17_1`, p. 504): for a measurable price `p ≥ pmin > 0` the young agent's
  problem has a unique solution `n(x) ∈ (0, L)`, characterised by the first-order condition. The
  abstract form is `consumer_problem` (differentiation under the integral sign:
  `hasDerivAt_utility`; the first-order condition has a unique root: `exists_unique_foc`).
* **Stationary equilibrium** (`IsStationaryEqm`, p. 503) and its reduction to (3) (p. 504):
  `eq3_of_isStationaryEqm` (equilibrium ⇒ (3), `p = M/(x n)`) and `isStationaryEqm_of_eq3`
  (the book's claim: a measurable `n : X → (0, L)` solving (3) is an equilibrium with
  `p = M/(x n)`); `eq3_iff_eq4` restates (3) as (4) with `ζ = olgZeta`, `φ = olgPhi`.
* **Proposition 1** (`proposition_1`, p. 505): with serially independent shocks (5) has exactly
  one solution in `(0, L)`.
* `olgZetaInv`, the inverse `ζ⁻¹ : ℝ₊ → [0, L)` (p. 507), continuous and strictly increasing,
  differentiable on `(0, ∞)` with `(ζ⁻¹)' = 1/ζ'(ζ⁻¹)`; `eq8_iff_eq4`: the change of variable
  `f = ζ ∘ n` turns (4) into the fixed-point equation (8).

**Correction (Proposition 1, step 4).** The case `φ(0) > 0` cannot occur under Assumption 17.1:
`φ(0) = 0 · V'(0) = 0` (`proposition_1_phi_zero_counterexample`). Only the book's second case
is relevant, and it is what `exists_unique_foc` proves.

**Correction (Proposition 1, (6)).** The elasticity `l ζ'(l)/ζ(l) = (H' + l H'')/H'` is `≥ 1`
on `(0, L)` (`zeta_elasticity_ge_one`) but **not** "`> 1` except at `0`": strict convexity allows
`H''(l₀) = 0`. Counterexample `proposition_1_elasticity_counterexample`, with
`olgExH(l) = l − 2 log(2 − l) + 6(2 − l) − 3(2 − l)² + (2/3)(2 − l)³` on `[0, 2)`, which satisfies
Assumption 17.1 (`olgExH_assumption`) and has elasticity exactly `1` at `l = 1`. The uniqueness
step is repaired as in the transcription's NOTE: the log-ratio `log ζ(l) − log ∫ φ(x' l) dμ` is
strictly increasing (`proposition_1_logRatio_strictMonoOn`), because it equals
`log H'(l) − log ∫ x' V'(x' l) dμ`.

**Correction (p. 515).** "Strict monotonicity and strict concavity imply `−y V''/V' > 0` on
`ℝ₊`" is false at `y = 0`, where the ratio is `0` (`rra_pos_counterexample`).

**Hypothesis made explicit (p. 504).** The converse "(3) ⇒ equilibrium" needs `n < L` (so that
`H'(n)` is defined and `p = M/(xn) ≥ M/(bL) > 0`, as Exercise 17.1 requires); the book says only
"strictly positive".
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### Assumption 17.1 -/

/-- **Assumption 17.1, labour part** (p. 503). The disutility of labour `H : [0, L) → ℝ₊` is
twice continuously differentiable (derivatives `H'`, `H''`, taken within `[0, L)`, so one-sided
at `0`), strictly increasing and strictly convex, with `H'(0) = 0` and `H'(l) → +∞` as `l → L`. -/
structure Assumption17_1H (L : ℝ) (H H' H'' : ℝ → ℝ) : Prop where
  L_pos : 0 < L
  H_nonneg : ∀ l ∈ Ico 0 L, 0 ≤ H l
  H_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H (H' l) (Ico 0 L) l
  H'_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H' (H'' l) (Ico 0 L) l
  H''_cont : ContinuousOn H'' (Ico 0 L)
  H_mono : StrictMonoOn H (Ico 0 L)
  H_conv : StrictConvexOn ℝ (Ico 0 L) H
  H'_zero : H' 0 = 0
  H'_tendsto : Tendsto H' (𝓝[<] L) atTop

/-- **Assumption 17.1, utility part** (p. 503). The utility of consumption `V : ℝ₊ → ℝ₊` is
twice continuously differentiable on `ℝ₊ = [0, ∞)` (derivatives `V'`, `V''` within `[0, ∞)`),
strictly increasing and strictly concave. -/
structure Assumption17_1V (V V' V'' : ℝ → ℝ) : Prop where
  V_nonneg : ∀ y, 0 ≤ y → 0 ≤ V y
  V_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V (V' y) (Ici 0) y
  V'_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V' (V'' y) (Ici 0) y
  V''_cont : ContinuousOn V'' (Ici 0)
  V_mono : StrictMonoOn V (Ici 0)
  V_conc : StrictConcaveOn ℝ (Ici 0) V

/-- **Assumption 17.1** (p. 503): labour lies in `[0, L)` with `L < ∞`, and `H`, `V` satisfy
`Assumption17_1H` and `Assumption17_1V`. -/
structure Assumption17_1 (L : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) : Prop where
  hH : Assumption17_1H L H H' H''
  hV : Assumption17_1V V V' V''

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-! ### Consequences of Assumption 17.1 -/

namespace Assumption17_1H

variable (hH : Assumption17_1H L H H' H'')
include hH

/-- `H'` is strictly increasing on `[0, L)` (strict convexity of `H`). -/
theorem H'_strictMonoOn : StrictMonoOn H' (Ico 0 L) := fun _ hx _ hy hxy =>
  (hH.H_conv.lt_slope_of_hasDerivWithinAt hx hy hxy (hH.H_deriv _ hx)).trans
    (hH.H_conv.slope_lt_of_hasDerivWithinAt hx hy hxy (hH.H_deriv _ hy))

/-- `H'(l) > 0` for `0 < l < L`. -/
theorem H'_pos {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 < H' l := by
  have := hH.H'_strictMonoOn (left_mem_Ico.2 hH.L_pos) (Ioo_subset_Ico_self hl) hl.1
  rwa [hH.H'_zero] at this

/-- `H' ≥ 0` on `[0, L)`. -/
theorem H'_nonneg {l : ℝ} (hl : l ∈ Ico 0 L) : 0 ≤ H' l := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, hH.H'_zero]
  · exact (hH.H'_pos ⟨h, hl.2⟩).le

/-- `H` is continuous on `[0, L)`. -/
theorem H_continuousOn : ContinuousOn H (Ico 0 L) := fun l hl =>
  (hH.H_deriv l hl).continuousWithinAt

/-- `H'` is continuous on `[0, L)`. -/
theorem H'_continuousOn : ContinuousOn H' (Ico 0 L) := fun l hl =>
  (hH.H'_deriv l hl).continuousWithinAt

/-- At interior points the derivative of `H` is two-sided. -/
theorem H_hasDerivAt {l : ℝ} (hl : l ∈ Ioo 0 L) : HasDerivAt H (H' l) l :=
  (hH.H_deriv l (Ioo_subset_Ico_self hl)).hasDerivAt (Ico_mem_nhds hl.1 hl.2)

/-- At interior points the derivative of `H'` is two-sided. -/
theorem H'_hasDerivAt {l : ℝ} (hl : l ∈ Ioo 0 L) : HasDerivAt H' (H'' l) l :=
  (hH.H'_deriv l (Ioo_subset_Ico_self hl)).hasDerivAt (Ico_mem_nhds hl.1 hl.2)

/-- `H'' ≥ 0` on `(0, L)` (`H'` is increasing). -/
theorem H''_nonneg {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 ≤ H'' l := by
  have h := (hH.H'_hasDerivAt hl).deriv
  rw [← h, ← derivWithin_of_mem_nhds (Ico_mem_nhds hl.1 hl.2)]
  exact hH.H'_strictMonoOn.monotoneOn.derivWithin_nonneg

/-- For every `M` there is `l ∈ (0, L)` with `M < H' l`. -/
theorem exists_H'_gt (M : ℝ) : ∃ l ∈ Ioo 0 L, M < H' l := by
  have h1 : ∀ᶠ l in 𝓝[<] L, M < H' l := hH.H'_tendsto.eventually (eventually_gt_atTop M)
  have h2 : ∀ᶠ l in 𝓝[<] L, l ∈ Ioo 0 L := Ioo_mem_nhdsLT hH.L_pos
  obtain ⟨l, hl1, hl2⟩ := (h1.and h2).exists
  exact ⟨l, hl2, hl1⟩

end Assumption17_1H

namespace Assumption17_1V

variable (hV : Assumption17_1V V V' V'')
include hV

/-- `V'(y) > 0` for `y ≥ 0`: the derivative at the left end of a secant of a strictly
concave function exceeds the (positive) slope. -/
theorem V'_pos {y : ℝ} (hy : 0 ≤ y) : 0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := hy
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h1 := hV.V_conc.slope_lt_of_hasDerivWithinAt hy' hy1 (by linarith) (hV.V_deriv y hy)
  have h2 : 0 < slope V y (y + 1) := by
    rw [slope_def_field]
    exact div_pos (sub_pos.2 (hV.V_mono hy' hy1 (by linarith))) (by linarith)
  linarith

/-- `V'` is strictly decreasing on `[0, ∞)` (strict concavity of `V`). -/
theorem V'_strictAntiOn : StrictAntiOn V' (Ici 0) := fun _ hx _ hy hxy =>
  (hV.V_conc.slope_lt_of_hasDerivWithinAt hx hy hxy (hV.V_deriv _ hx)).trans'
    (hV.V_conc.lt_slope_of_hasDerivWithinAt hx hy hxy (hV.V_deriv _ hy))

/-- `V` is continuous on `[0, ∞)`. -/
theorem V_continuousOn : ContinuousOn V (Ici 0) := fun y hy =>
  (hV.V_deriv y hy).continuousWithinAt

/-- `V'` is continuous on `[0, ∞)`. -/
theorem V'_continuousOn : ContinuousOn V' (Ici 0) := fun y hy =>
  (hV.V'_deriv y hy).continuousWithinAt

/-- At `y > 0` the derivative of `V` is two-sided. -/
theorem V_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt V (V' y) y :=
  (hV.V_deriv y hy.le).hasDerivAt (Ici_mem_nhds hy)

/-- `V'(y) ≤ V'(0)` for `y ≥ 0`. -/
theorem V'_le_V'_zero {y : ℝ} (hy : 0 ≤ y) : V' y ≤ V' 0 :=
  hV.V'_strictAntiOn.antitoneOn (mem_Ici.2 le_rfl) hy hy

end Assumption17_1V

/-! ### The consumer's problem (Exercise 17.1)

For a fixed current state the young agent's problem is `max_{l ∈ [0, L)} −H(l) + ∫ V(l c) dμ`,
where `μ = π(x, ·)` and `c(x') = x p(x)/p(x')` is the (random) real return on money. We treat
a general probability space `Ω`, a measurable `c` with `0 < c ≤ C`. -/

/-- A function continuous on `[0, ∞)` composed with a nonnegative measurable function is
measurable. -/
theorem measurable_comp_of_continuousOn_Ici {Ω : Type*} [MeasurableSpace Ω] {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) :
    Measurable fun ω => g (f ω) := by
  have hc : Continuous fun y : ℝ => g (max y 0) :=
    hg.comp_continuous (continuous_id.max continuous_const) fun y => le_max_right y 0
  have := hc.measurable.comp hf
  convert this using 1
  funext ω
  simp [max_eq_left (hf0 ω)]

/-- The integral of a strictly positive integrable function against a probability measure is
strictly positive. -/
theorem integral_pos_of_forall_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hpos : ∀ ω, 0 < f ω) :
    0 < ∫ ω, f ω ∂μ := by
  refine (integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hf).2 ?_
  have : Function.support f = univ :=
    eq_univ_of_forall fun ω => Function.mem_support.2 (hpos ω).ne'
  rw [this, measure_univ]
  exact one_pos

/-- Expected marginal utility of labour, `l ↦ ∫ c V'(l c) dμ`. -/
noncomputable def margUtil {Ω : Type*} [MeasurableSpace Ω] (V' : ℝ → ℝ) (μ : Measure Ω)
    (c : Ω → ℝ) (l : ℝ) : ℝ :=
  ∫ ω, c ω * V' (l * c ω) ∂μ

/-- The young agent's objective, `l ↦ −H(l) + ∫ V(l c) dμ`. -/
noncomputable def consumerObj {Ω : Type*} [MeasurableSpace Ω] (H V : ℝ → ℝ) (μ : Measure Ω)
    (c : Ω → ℝ) (l : ℝ) : ℝ :=
  -H l + ∫ ω, V (l * c ω) ∂μ

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
  {C : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The marginal-utility integrand is integrable and bounded by `C V'(0)`. -/
theorem integrable_margUtil (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun ω => c ω * V' (l * c ω)) μ := by
  have hm : Measurable fun ω => c ω * V' (l * c ω) :=
    hc.mul (measurable_comp_of_continuousOn_Ici hV.V'_continuousOn (measurable_const.mul hc)
      fun ω => mul_nonneg hl (hcpos ω).le)
  refine Integrable.mono' (integrable_const (C * V' 0)) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ l * c ω := mul_nonneg hl (hcpos ω).le
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hcpos ω) (hV.V'_pos h0))]
  exact mul_le_mul (hcle ω) (hV.V'_le_V'_zero h0) (hV.V'_pos h0).le
    ((hcpos ω).le.trans (hcle ω))

omit [IsProbabilityMeasure μ] in
/-- `l ↦ ∫ c V'(l c) dμ` is continuous on `[0, ∞)` (dominated convergence). -/
theorem continuousOn_margUtil (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] :
    ContinuousOn (margUtil V' μ c) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => C * V' 0)
    (fun l hl => (integrable_margUtil hV hc hcpos hcle hl).aestronglyMeasurable)
    (fun l hl => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
  · have h0 : 0 ≤ l * c ω := mul_nonneg hl (hcpos ω).le
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hcpos ω) (hV.V'_pos h0))]
    exact mul_le_mul (hcle ω) (hV.V'_le_V'_zero h0) (hV.V'_pos h0).le
      ((hcpos ω).le.trans (hcle ω))
  · exact continuousOn_const.mul (hV.V'_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun l hl => mul_nonneg hl (hcpos ω).le)

/-- `l ↦ ∫ c V'(l c) dμ` is strictly decreasing on `[0, ∞)`. -/
theorem margUtil_strictAntiOn (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) : StrictAntiOn (margUtil V' μ c) (Ici 0) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have hl₁' : (0 : ℝ) ≤ l₁ := hl₁
  have hl₂' : (0 : ℝ) ≤ l₂ := hl₂
  rw [← sub_pos, margUtil, margUtil, ← integral_sub (integrable_margUtil hV hc hcpos hcle hl₁')
    (integrable_margUtil hV hc hcpos hcle hl₂')]
  refine integral_pos_of_forall_pos ((integrable_margUtil hV hc hcpos hcle hl₁').sub
    (integrable_margUtil hV hc hcpos hcle hl₂')) fun ω => ?_
  rw [← mul_sub]
  refine mul_pos (hcpos ω) (sub_pos.2 (hV.V'_strictAntiOn ?_ ?_ ?_))
  · exact mul_nonneg hl₁' (hcpos ω).le
  · exact mul_nonneg hl₂' (hcpos ω).le
  · exact mul_lt_mul_of_pos_right hlt (hcpos ω)

/-- `∫ c V'(0) dμ > 0`. -/
theorem margUtil_zero_pos (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) : 0 < margUtil V' μ c 0 :=
  integral_pos_of_forall_pos (integrable_margUtil hV hc hcpos hcle le_rfl) fun ω =>
    mul_pos (hcpos ω) (hV.V'_pos (by rw [zero_mul]))

/-- `∫ c V'(l c) dμ ≤ C V'(0)`. -/
theorem margUtil_le (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) {l : ℝ} (hl : 0 ≤ l) :
    margUtil V' μ c l ≤ C * V' 0 := by
  have h := integral_mono (integrable_margUtil (μ := μ) hV hc hcpos hcle hl)
    (integrable_const (C * V' 0))
    (fun ω => mul_le_mul (hcle ω) (hV.V'_le_V'_zero (mul_nonneg hl (hcpos ω).le))
      (hV.V'_pos (mul_nonneg hl (hcpos ω).le)).le ((hcpos ω).le.trans (hcle ω)))
  simpa [margUtil] using h

/-- **The first-order condition has exactly one root.** `H'(n) = ∫ c V'(n c) dμ` has a unique
solution `n ∈ [0, L)`, and it lies in `(0, L)`. -/
theorem exists_unique_foc (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1V V V' V'')
    (hc : Measurable c) (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) :
    ∃ n ∈ Ioo 0 L, H' n = margUtil V' μ c n ∧
      ∀ m ∈ Ico 0 L, H' m = margUtil V' μ c m → m = n := by
  set foc : ℝ → ℝ := fun l => H' l - margUtil V' μ c l with hfoc
  have hmono : StrictMonoOn foc (Ico 0 L) := fun x hx y hy hxy => by
    have h1 := hH.H'_strictMonoOn hx hy hxy
    have h2 := margUtil_strictAntiOn (μ := μ) hV hc hcpos hcle (Ico_subset_Ici_self hx)
      (Ico_subset_Ici_self hy) hxy
    simp only [hfoc]
    linarith
  have hcont : ContinuousOn foc (Ico 0 L) :=
    hH.H'_continuousOn.sub ((continuousOn_margUtil (μ := μ) hV hc hcpos hcle).mono
      Ico_subset_Ici_self)
  obtain ⟨l₁, hl₁, hl₁M⟩ := hH.exists_H'_gt (C * V' 0)
  have h0 : foc 0 < 0 := by
    simp only [hfoc, hH.H'_zero, zero_sub, neg_neg_iff_pos]
    exact margUtil_zero_pos hV hc hcpos hcle
  have h1 : 0 < foc l₁ := by
    have := margUtil_le (μ := μ) hV hc hcpos hcle hl₁.1.le
    simp only [hfoc]
    linarith
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun y hy => ⟨hy.1, hy.2.trans_lt hl₁.2⟩
  obtain ⟨n, hn, hn0⟩ := intermediate_value_Icc hl₁.1.le (hcont.mono hsub) ⟨h0.le, h1.le⟩
  have hnpos : 0 < n := by
    rcases hn.1.eq_or_lt with h | h
    · rw [← h] at hn0; linarith
    · exact h
  refine ⟨n, ⟨hnpos, hn.2.trans_lt hl₁.2⟩, by simpa [hfoc, sub_eq_zero] using hn0, ?_⟩
  intro m hm hfm
  have hfm' : foc m = foc n := by simp only [hfoc]; rw [hfm, sub_self]; exact hn0.symm
  exact hmono.injOn hm (hsub hn) hfm'

omit [IsProbabilityMeasure μ] in
/-- The utility integrand `V(l c)` is integrable. -/
theorem integrable_utility (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun ω => V (l * c ω)) μ := by
  have hm : Measurable fun ω => V (l * c ω) :=
    measurable_comp_of_continuousOn_Ici hV.V_continuousOn (measurable_const.mul hc)
      fun ω => mul_nonneg hl (hcpos ω).le
  refine Integrable.mono' (integrable_const (V (l * C))) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ l * c ω := mul_nonneg hl (hcpos ω).le
  rw [Real.norm_eq_abs, abs_of_nonneg (hV.V_nonneg _ h0)]
  exact hV.V_mono.monotoneOn h0 (mul_nonneg hl ((hcpos ω).le.trans (hcle ω)))
    (mul_le_mul_of_nonneg_left (hcle ω) hl)

omit [IsProbabilityMeasure μ] in
/-- `l ↦ ∫ V(l c) dμ` is continuous on `[0, B]`. -/
theorem continuousOn_utility (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] (B : ℝ) :
    ContinuousOn (fun l => ∫ ω, V (l * c ω) ∂μ) (Icc 0 B) := by
  refine continuousOn_of_dominated (bound := fun _ => V (B * C))
    (fun l hl => (integrable_utility hV hc hcpos hcle hl.1).aestronglyMeasurable)
    (fun l hl => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
  · have h0 : 0 ≤ l * c ω := mul_nonneg hl.1 (hcpos ω).le
    rw [Real.norm_eq_abs, abs_of_nonneg (hV.V_nonneg _ h0)]
    have hC : 0 ≤ C := (hcpos ω).le.trans (hcle ω)
    exact hV.V_mono.monotoneOn h0 (mul_nonneg (hl.1.trans hl.2) hC)
      (mul_le_mul hl.2 (hcle ω) (hcpos ω).le (hl.1.trans hl.2))
  · exact hV.V_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun l hl => mul_nonneg hl.1 (hcpos ω).le

omit [IsProbabilityMeasure μ] in
/-- Differentiation under the integral sign: for `l > 0`,
`d/dl ∫ V(l c) dμ = ∫ c V'(l c) dμ`. -/
theorem hasDerivAt_utility (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) [IsFiniteMeasure μ] {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun l => ∫ ω, V (l * c ω) ∂μ) (margUtil V' μ c l) l := by
  have hs : Ioi (l / 2) ∈ 𝓝 l := Ioi_mem_nhds (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun l ω => V (l * c ω)) (F' := fun l ω => c ω * V' (l * c ω))
    (bound := fun _ => C * V' 0) hs
    (Filter.mem_of_superset hs fun x hx =>
      (integrable_utility hV hc hcpos hcle (by simp only [mem_Ioi] at hx; linarith)
        ).aestronglyMeasurable)
    (integrable_utility hV hc hcpos hcle hl.le)
    (integrable_margUtil hV hc hcpos hcle hl.le).aestronglyMeasurable
    (ae_of_all _ fun ω x hx => by
      have hx0 : 0 ≤ x * c ω := mul_nonneg (by simp only [mem_Ioi] at hx; linarith) (hcpos ω).le
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hcpos ω) (hV.V'_pos hx0))]
      exact mul_le_mul (hcle ω) (hV.V'_le_V'_zero hx0) (hV.V'_pos hx0).le
        ((hcpos ω).le.trans (hcle ω)))
    (integrable_const _)
    (ae_of_all _ fun ω x hx => by
      have hx0 : 0 < x * c ω := mul_pos (by simp only [mem_Ioi] at hx; linarith) (hcpos ω)
      have h1 : HasDerivAt (fun y => y * c ω) (c ω) x := by
        simpa using (hasDerivAt_id x).mul_const (c ω)
      have := (hV.V_hasDerivAt hx0).comp x h1
      rw [mul_comm] at this
      exact this)
  exact key.2

/-- **The consumer's problem** (Exercise 17.1, abstract form). With `0 < c ≤ C` measurable, the
problem `max_{l ∈ [0, L)} −H(l) + ∫ V(l c) dμ` has a unique solution `n`; it is strictly
positive and is the unique root in `[0, L)` of the first-order condition
`H'(n) = ∫ c V'(n c) dμ`. -/
theorem consumer_problem (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1V V V' V'')
    (hc : Measurable c) (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) :
    ∃ n ∈ Ioo 0 L, H' n = margUtil V' μ c n ∧
      (∀ l ∈ Ico 0 L, l ≠ n → consumerObj H V μ c l < consumerObj H V μ c n) ∧
      ∀ m ∈ Ico 0 L, H' m = margUtil V' μ c m → m = n := by
  obtain ⟨n, hn, hfoc, huniq⟩ := exists_unique_foc (μ := μ) hH hV hc hcpos hcle
  refine ⟨n, hn, hfoc, ?_, huniq⟩
  have hcont : ContinuousOn (consumerObj H V μ c) (Ico 0 L) :=
    hH.H_continuousOn.neg.add ((continuousOn_utility hV hc hcpos hcle L).mono
      Ico_subset_Icc_self)
  have hderiv : ∀ x ∈ Ioo 0 L,
      HasDerivAt (consumerObj H V μ c) (-H' x + margUtil V' μ c x) x := fun x hx =>
    (hH.H_hasDerivAt hx).neg.add (hasDerivAt_utility hV hc hcpos hcle hx.1)
  have hstrict : StrictMonoOn (fun l => H' l - margUtil V' μ c l) (Ico 0 L) :=
    fun x hx y hy hxy => by
      have h1 := hH.H'_strictMonoOn hx hy hxy
      have h2 := margUtil_strictAntiOn (μ := μ) hV hc hcpos hcle (Ico_subset_Ici_self hx)
        (Ico_subset_Ici_self hy) hxy
      linarith
  have hn' : n ∈ Ico 0 L := Ioo_subset_Ico_self hn
  have hfn : H' n - margUtil V' μ c n = 0 := by rw [hfoc, sub_self]
  have hup : StrictMonoOn (consumerObj H V μ c) (Icc 0 n) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 n)
      (hcont.mono fun y hy => ⟨hy.1, hy.2.trans_lt hn.2⟩) fun x hx => ?_
    rw [interior_Icc] at hx
    have hxL : x ∈ Ioo 0 L := ⟨hx.1, hx.2.trans hn.2⟩
    rw [(hderiv x hxL).deriv]
    have := hstrict (Ioo_subset_Ico_self hxL) hn' hx.2
    simp only [hfn] at this
    linarith
  have hdown : StrictAntiOn (consumerObj H V μ c) (Ico n L) := by
    refine strictAntiOn_of_deriv_neg (convex_Ico n L)
      (hcont.mono fun y hy => ⟨hn.1.le.trans hy.1, hy.2⟩) fun x hx => ?_
    rw [interior_Ico] at hx
    have hxL : x ∈ Ioo 0 L := ⟨hn.1.trans hx.1, hx.2⟩
    rw [(hderiv x hxL).deriv]
    have := hstrict hn' (Ioo_subset_Ico_self hxL) hx.1
    simp only [hfn] at this
    linarith
  intro l hl hln
  rcases lt_or_gt_of_ne hln with h | h
  · exact hup ⟨hl.1, h.le⟩ ⟨hn.1.le, le_rfl⟩ h
  · exact hdown ⟨le_rfl, hn.2⟩ ⟨h.le, hl.2⟩ h

/-! ### Exercise 17.1 and the equilibrium conditions -/

/-- **Exercise 17.1** (p. 504). Let `p : X → ℝ` be a measurable price function bounded away from
zero (`p ≥ pmin > 0`; no upper bound is needed). For each `x ∈ X = [a, b]` the young agent's
problem `max_{l ∈ [0, L)} −H(l) + ∫ V(x l p(x)/p(x')) π(x, dx')` has a unique solution `n`
(any other `l` does strictly worse), `n > 0`, `n` satisfies the first-order condition
`H'(n) = ∫ (x p(x)/p(x')) V'(x n p(x)/p(x')) π(x, dx')`, and `n` is the only root of that
condition in `[0, L)`. -/
theorem ex_17_1 {a b : ℝ} (ha : 0 < a) (hA : Assumption17_1 L H H' H'' V V' V'')
    (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ] {p : Icc a b → ℝ} (hp : Measurable p)
    {pmin : ℝ} (hpmin : 0 < pmin) (hpge : ∀ x, pmin ≤ p x) (x : Icc a b) :
    ∃ n ∈ Ioo 0 L,
      (∀ l ∈ Ico 0 L, l ≠ n → -H l + ∫ x', V (x.1 * l * p x / p x') ∂κ x <
        -H n + ∫ x', V (x.1 * n * p x / p x') ∂κ x) ∧
      H' n = ∫ x', x.1 * p x / p x' * V' (x.1 * n * p x / p x') ∂κ x ∧
      ∀ m ∈ Ico 0 L, H' m = ∫ x', x.1 * p x / p x' * V' (x.1 * m * p x / p x') ∂κ x → m = n := by
  set c : Icc a b → ℝ := fun x' => x.1 * p x / p x' with hcdef
  have hx : 0 < x.1 := ha.trans_le x.2.1
  have hppos : ∀ x', 0 < p x' := fun x' => hpmin.trans_le (hpge x')
  have hc : Measurable c := measurable_const.div hp
  have hcpos : ∀ x', 0 < c x' := fun x' => div_pos (mul_pos hx (hppos x)) (hppos x')
  have hcle : ∀ x', c x' ≤ x.1 * p x / pmin := fun x' =>
    div_le_div_of_nonneg_left (mul_pos hx (hppos x)).le hpmin (hpge x')
  have e : ∀ (l : ℝ) (x' : Icc a b), x.1 * l * p x / p x' = l * c x' := fun l x' => by
    simp only [hcdef]; ring
  obtain ⟨n, hn, hfoc, hmax, huniq⟩ :=
    consumer_problem (μ := κ x) hA.hH hA.hV hc hcpos hcle
  refine ⟨n, hn, ?_, ?_, ?_⟩
  · intro l hl hln
    simpa only [e, consumerObj] using hmax l hl hln
  · simpa only [e, margUtil] using hfoc
  · intro m hm hfm
    exact huniq m hm (by simpa only [e, margUtil] using hfm)

variable {a b : ℝ} (κ : Kernel (Icc a b) (Icc a b)) in
/-- A **stationary competitive equilibrium with valued money** (p. 503): a strictly positive
measurable price function `p` and a labour supply `n : X → [0, L)` such that (1) `n(x)`
maximises `−H(l) + ∫ V(x l p(x)/p(x')) π(x, dx')` over `l ∈ [0, L)`, and (2) the goods market
clears, `x n(x) = M/p(x)`. -/
structure IsStationaryEqm (L M : ℝ) (H V : ℝ → ℝ) (p n : Icc a b → ℝ) : Prop where
  p_pos : ∀ x, 0 < p x
  p_meas : Measurable p
  n_mem : ∀ x, n x ∈ Ico 0 L
  optimal : ∀ x, ∀ l ∈ Ico 0 L, -H l + ∫ x', V (x.1 * l * p x / p x') ∂κ x ≤
    -H (n x) + ∫ x', V (x.1 * n x * p x / p x') ∂κ x
  clearing : ∀ x, x.1 * n x = M / p x

/-- **Equilibrium implies (3)** (p. 504). In a stationary equilibrium `0 < n(x) < L`,
`p(x) = M/(x n(x))`, and `n` satisfies
`n(x) H'(n(x)) = ∫ x' n(x') V'(x' n(x')) π(x, dx')`. The price is automatically bounded away
from zero (`p ≥ M/(bL)`), so Exercise 17.1 applies. -/
theorem eq3_of_isStationaryEqm {a b M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hA : Assumption17_1 L H H' H'' V V' V'') {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    {p n : Icc a b → ℝ} (h : IsStationaryEqm κ L M H V p n) :
    (∀ x, n x ∈ Ioo 0 L) ∧ (∀ x, p x = M / (x.1 * n x)) ∧
      ∀ x, n x * H' (n x) = ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x := by
  have hxpos : ∀ x : Icc a b, 0 < x.1 := fun x => ha.trans_le x.2.1
  have hnpos : ∀ x, 0 < n x := fun x => by
    have h1 : 0 < x.1 * n x := by rw [h.clearing x]; exact div_pos hM (h.p_pos x)
    exact pos_of_mul_pos_right h1 (hxpos x).le
  have hnmem : ∀ x, n x ∈ Ioo 0 L := fun x => ⟨hnpos x, (h.n_mem x).2⟩
  have hpeq : ∀ x, p x = M / (x.1 * n x) := fun x => by
    rw [h.clearing x, div_div_cancel₀ hM.ne']
  have hbL : ∀ x : Icc a b, x.1 * n x ≤ b * L := fun x =>
    mul_le_mul x.2.2 (h.n_mem x).2.le (hnpos x).le ((hxpos x).le.trans x.2.2)
  refine ⟨hnmem, hpeq, fun x => ?_⟩
  have hb : 0 < b := (hxpos x).trans_le x.2.2
  have hpmin : ∀ x', M / (b * L) ≤ p x' := fun x' => by
    rw [hpeq x']
    exact div_le_div_of_nonneg_left hM.le (mul_pos (hxpos x') (hnpos x')) (hbL x')
  obtain ⟨n₀, hn₀, hmax, hfoc, -⟩ :=
    ex_17_1 ha hA κ h.p_meas (div_pos hM (mul_pos hb hA.hH.L_pos)) hpmin x
  have heq : n x = n₀ := by
    by_contra hne
    have h1 := hmax (n x) (h.n_mem x) hne
    have h2 := h.optimal x n₀ (Ioo_subset_Ico_self hn₀)
    linarith
  rw [← heq] at hfoc
  rw [hfoc, ← integral_const_mul]
  congr 1
  funext x'
  have hk : x.1 * n x * p x / p x' = x'.1 * n x' := by
    rw [h.clearing x, h.clearing x', div_mul_cancel₀ M (h.p_pos x).ne']
  have e : n x * (x.1 * p x / p x' * V' (x.1 * n x * p x / p x')) =
      (x.1 * n x * p x / p x') * V' (x.1 * n x * p x / p x') := by ring
  rw [e, hk]

/-- **(3) implies equilibrium** (p. 504, the book's claim). If `n : X → (0, L)` is measurable
and satisfies `n(x) H'(n(x)) = ∫ x' n(x') V'(x' n(x')) π(x, dx')`, then `p(x) = M/(x n(x))`
and `n` form a stationary competitive equilibrium. (The book says only "strictly positive";
`n < L` is needed for `H'(n)` to be defined, and gives `p ≥ M/(bL) > 0`.) -/
theorem isStationaryEqm_of_eq3 {a b M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hA : Assumption17_1 L H H' H'' V V' V'') {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    {n : Icc a b → ℝ} (hn : Measurable n) (hnmem : ∀ x, n x ∈ Ioo 0 L)
    (h3 : ∀ x, n x * H' (n x) = ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x) :
    IsStationaryEqm κ L M H V (fun x => M / (x.1 * n x)) n := by
  have hxpos : ∀ x : Icc a b, 0 < x.1 := fun x => ha.trans_le x.2.1
  have hxn : ∀ x, 0 < x.1 * n x := fun x => mul_pos (hxpos x) (hnmem x).1
  have hppos : ∀ x : Icc a b, 0 < M / (x.1 * n x) := fun x => div_pos hM (hxn x)
  have hpm : Measurable fun x : Icc a b => M / (x.1 * n x) :=
    measurable_const.div (measurable_subtype_coe.mul hn)
  refine ⟨hppos, hpm, fun x => Ioo_subset_Ico_self (hnmem x), fun x l hl => ?_, fun x => ?_⟩
  · have hb : 0 < b := (hxpos x).trans_le x.2.2
    have hbL : ∀ x' : Icc a b, x'.1 * n x' ≤ b * L := fun x' =>
      mul_le_mul x'.2.2 (hnmem x').2.le (hnmem x').1.le hb.le
    have hpmin : ∀ x' : Icc a b, M / (b * L) ≤ M / (x'.1 * n x') := fun x' =>
      div_le_div_of_nonneg_left hM.le (hxn x') (hbL x')
    obtain ⟨n₀, -, hmax, -, huniq⟩ :=
      ex_17_1 ha hA κ hpm (div_pos hM (mul_pos hb hA.hH.L_pos)) hpmin x
    have hk : ∀ x' : Icc a b, x.1 * (M / (x.1 * n x)) / (M / (x'.1 * n x')) =
        (n x)⁻¹ * (x'.1 * n x') := fun x' => by
      have := (hxpos x).ne'; have := (hnmem x).1.ne'; have := (hxn x').ne'
      field_simp
    have hk2 : ∀ x' : Icc a b, x.1 * n x * (M / (x.1 * n x)) / (M / (x'.1 * n x')) =
        x'.1 * n x' := fun x' => by
      have e1 : x.1 * n x * (M / (x.1 * n x)) = M := by
        have := (hxn x).ne'
        rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self this, mul_one]
      rw [e1, div_div_cancel₀ hM.ne']
    have hint : ∫ x', x.1 * (M / (x.1 * n x)) / (M / (x'.1 * n x')) *
        V' (x.1 * n x * (M / (x.1 * n x)) / (M / (x'.1 * n x'))) ∂κ x =
        (n x)⁻¹ * ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x := by
      rw [← integral_const_mul]
      congr 1
      funext x'
      rw [hk, hk2]
      ring
    have heq : n x = n₀ := by
      refine huniq (n x) (Ioo_subset_Ico_self (hnmem x)) ?_
      rw [hint, ← h3 x, inv_mul_cancel_left₀ (hnmem x).1.ne']
    rcases eq_or_ne l (n x) with rfl | hne
    · exact le_rfl
    · have := hmax l hl (heq ▸ hne)
      rw [← heq] at this
      exact this.le
  · rw [div_div_cancel₀ hM.ne']

/-! ### Equation (4) and Proposition 1 -/

/-- `ζ(l) = l H'(l)` (p. 504). -/
def olgZeta (H' : ℝ → ℝ) (l : ℝ) : ℝ := l * H' l

/-- `φ(y) = y V'(y)` (p. 504). -/
def olgPhi (V' : ℝ → ℝ) (y : ℝ) : ℝ := y * V' y

/-- Equation (3) is equation (4), `ζ(n(x)) = ∫ φ(x' n(x')) π(x, dx')` (p. 504). -/
theorem eq3_iff_eq4 {a b : ℝ} (κ : Kernel (Icc a b) (Icc a b)) (n : Icc a b → ℝ) (x : Icc a b) :
    n x * H' (n x) = ∫ x', x'.1 * n x' * V' (x'.1 * n x') ∂κ x ↔
      olgZeta H' (n x) = ∫ x', olgPhi V' (x'.1 * n x') ∂κ x :=
  Iff.rfl

/-- `∫ c V'(l c) dμ > 0` for `l ≥ 0`. -/
theorem margUtil_pos (hV : Assumption17_1V V V' V'') (hc : Measurable c)
    (hcpos : ∀ ω, 0 < c ω) (hcle : ∀ ω, c ω ≤ C) {l : ℝ} (hl : 0 ≤ l) :
    0 < margUtil V' μ c l :=
  integral_pos_of_forall_pos (integrable_margUtil hV hc hcpos hcle hl) fun ω =>
    mul_pos (hcpos ω) (hV.V'_pos (mul_nonneg hl (hcpos ω).le))

/-- With serially independent shocks, `∫ φ(x' l) dμ = l ∫ x' V'(l x') dμ`. -/
theorem integral_olgPhi {a b : ℝ} (μ : Measure (Icc a b)) (l : ℝ) :
    ∫ x', olgPhi V' (x'.1 * l) ∂μ = l * margUtil V' μ (fun x' => x'.1) l := by
  rw [margUtil, ← integral_const_mul]
  congr 1
  funext x'
  simp only [olgPhi]
  rw [mul_comm x'.1 l]
  ring

/-- **Proposition 1** (p. 505). With serially independent shocks (`π(x, ·) = μ` a probability
measure on `X = [a, b]`, `a > 0`) and Assumption 17.1, equation (5),
`ζ(n) = ∫ φ(x' n) μ(dx')`, has exactly one solution `n ∈ (0, L)`. For `n > 0`, (5) is the
first-order condition `H'(n) = ∫ x' V'(x' n) dμ`, whose left side is strictly increasing and
right side strictly decreasing (`exists_unique_foc`). -/
theorem proposition_1 {a b : ℝ} (ha : 0 < a) (hA : Assumption17_1 L H H' H'' V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    ∃! n, n ∈ Ioo 0 L ∧ olgZeta H' n = ∫ x', olgPhi V' (x'.1 * n) ∂μ := by
  have hc : Measurable fun x' : Icc a b => x'.1 := measurable_subtype_coe
  have hcpos : ∀ x' : Icc a b, 0 < x'.1 := fun x' => ha.trans_le x'.2.1
  have hcle : ∀ x' : Icc a b, x'.1 ≤ b := fun x' => x'.2.2
  have hiff : ∀ l, 0 < l → (olgZeta H' l = ∫ x', olgPhi V' (x'.1 * l) ∂μ ↔
      H' l = margUtil V' μ (fun x' => x'.1) l) := fun l hl => by
    rw [integral_olgPhi, olgZeta]
    exact ⟨fun h => mul_left_cancel₀ hl.ne' h, fun h => by rw [h]⟩
  obtain ⟨n, hn, hfoc, huniq⟩ := exists_unique_foc (μ := μ) hA.hH hA.hV hc hcpos hcle
  exact ⟨n, ⟨hn, (hiff n hn.1).2 hfoc⟩, fun m hm =>
    huniq m (Ioo_subset_Ico_self hm.1) ((hiff m hm.1.1).1 hm.2)⟩

/-- **The NOTE's repair of the uniqueness step of Proposition 1.** The log-ratio
`h(l) = log ζ(l) − log ∫ φ(x' l) dμ` is strictly increasing on `(0, L)`, so the two curves of
Figure 17.1 cross at most once. (Indeed `h(l) = log H'(l) − log ∫ x' V'(x' l) dμ`.) The book's
pointwise "crosses from below" argument through the elasticities (6)–(7) is not needed. -/
theorem proposition_1_logRatio_strictMonoOn {a b : ℝ} (ha : 0 < a)
    (hA : Assumption17_1 L H H' H'' V V' V'') (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    StrictMonoOn (fun l => Real.log (olgZeta H' l) - Real.log (∫ x', olgPhi V' (x'.1 * l) ∂μ))
      (Ioo 0 L) := by
  have hc : Measurable fun x' : Icc a b => x'.1 := measurable_subtype_coe
  have hcpos : ∀ x' : Icc a b, 0 < x'.1 := fun x' => ha.trans_le x'.2.1
  have hcle : ∀ x' : Icc a b, x'.1 ≤ b := fun x' => x'.2.2
  intro x hx y hy hxy
  simp only [integral_olgPhi, olgZeta]
  have hHx := hA.hH.H'_pos hx
  have hHy := hA.hH.H'_pos hy
  have hmx := margUtil_pos (μ := μ) hA.hV hc hcpos hcle hx.1.le
  have hmy := margUtil_pos (μ := μ) hA.hV hc hcpos hcle hy.1.le
  rw [Real.log_mul hx.1.ne' hHx.ne', Real.log_mul hx.1.ne' hmx.ne', Real.log_mul hy.1.ne' hHy.ne',
    Real.log_mul hy.1.ne' hmy.ne']
  have h1 := Real.log_lt_log hHx (hA.hH.H'_strictMonoOn (Ioo_subset_Ico_self hx)
    (Ioo_subset_Ico_self hy) hxy)
  have h2 := Real.log_lt_log hmy (margUtil_strictAntiOn (μ := μ) hA.hV hc hcpos hcle
    (mem_Ici.2 hx.1.le) (mem_Ici.2 hy.1.le) hxy)
  linarith

/-- **Correction (Proposition 1, step 4).** Under Assumption 17.1, `φ(0) = 0 · V'(0) = 0`, so the
first case of the existence argument (`φ(0) > 0`, top panel of Figure 17.1) cannot occur. -/
theorem proposition_1_phi_zero_counterexample : ¬ 0 < olgPhi V' 0 := by
  simp [olgPhi]

/-- **Correction (p. 515).** Strict monotonicity and strict concavity of `V` do not make the
relative risk aversion `−y V''(y)/V'(y)` strictly positive on all of `ℝ₊`: it is `0` at
`y = 0` (for every `V`, in particular every `V` satisfying Assumption 17.1). -/
theorem rra_pos_counterexample :
    ¬ ∀ y : ℝ, 0 ≤ y → 0 < -(y * V'' y) / V' y := fun h => by
  have := h 0 le_rfl
  simp at this

/-! ### The elasticity of `ζ` (equation (6)) -/

/-- The counterexample disutility `H(l) = l − 2 log(2 − l) + 6(2 − l) − 3(2 − l)² + (2/3)(2 − l)³`
on `[0, 2)`. -/
noncomputable def olgExH (l : ℝ) : ℝ :=
  l - 2 * Real.log (2 - l) + 6 * (2 - l) - 3 * (2 - l) ^ 2 + 2 / 3 * (2 - l) ^ 3
/-- Its derivative `H'(l) = 1 + 2(l − 1)³/(2 − l)`. -/
noncomputable def olgExH1 (l : ℝ) : ℝ := 1 + 2 * (l - 1) ^ 3 / (2 - l)
/-- Its second derivative `H''(l) = 2(l − 1)²(5 − 2l)/(2 − l)²`, which vanishes at `l = 1`. -/
noncomputable def olgExH2 (l : ℝ) : ℝ := 2 * (l - 1) ^ 2 * (5 - 2 * l) / (2 - l) ^ 2

/-- `H' ` is the derivative of the counterexample `H`. -/
theorem olgExH_hasDerivAt {l : ℝ} (hl : l < 2) : HasDerivAt olgExH (olgExH1 l) l := by
  have h2 : (2 - l) ≠ 0 := by linarith
  have hd : HasDerivAt (fun l : ℝ => 2 - l) (-1) l := by
    simpa using (hasDerivAt_id' l).const_sub (2 : ℝ)
  have := ((((hasDerivAt_id' l).sub ((hd.log h2).const_mul 2)).add (hd.const_mul 6)).sub
    ((hd.pow 2).const_mul 3)).add ((hd.pow 3).const_mul (2 / 3))
  convert this using 1
  · funext y
    simp only [olgExH, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
  · simp only [olgExH1]
    field_simp
    ring

/-- `H''` is the derivative of the counterexample `H'`. -/
theorem olgExH1_hasDerivAt {l : ℝ} (hl : l < 2) : HasDerivAt olgExH1 (olgExH2 l) l := by
  have h2 : (2 - l) ≠ 0 := by linarith
  have hd : HasDerivAt (fun l : ℝ => 2 - l) (-1) l := by
    simpa using (hasDerivAt_id' l).const_sub (2 : ℝ)
  have hn : HasDerivAt (fun l : ℝ => (l - 1) ^ 3) (3 * (l - 1) ^ 2) l := by
    convert ((hasDerivAt_id' l).sub_const 1).pow 3 using 1
    norm_num
  have := (hasDerivAt_const l (1:ℝ)).add ((hn.const_mul 2).div hd h2)
  convert this using 1
  · funext y
    simp only [olgExH1, Pi.add_apply, Pi.div_apply]
  · simp only [olgExH2]
    field_simp
    ring

/-- The counterexample `H'` is positive on `(0, 2)`. -/
theorem olgExH1_pos {l : ℝ} (h0 : 0 < l) (hl : l < 2) : 0 < olgExH1 l := by
  simp only [olgExH1]
  have h2 : 0 < 2 - l := by linarith
  have : 0 < (2 - l) + 2 * (l - 1) ^ 3 := by
    rcases le_or_gt 1 l with h | h
    · nlinarith [pow_nonneg (sub_nonneg.2 h) 3]
    · nlinarith [mul_pos h0 h0, mul_pos (sub_pos.2 h) (sub_pos.2 h)]
  have e : 1 + 2 * (l - 1) ^ 3 / (2 - l) = ((2 - l) + 2 * (l - 1) ^ 3) / (2 - l) := by
    field_simp
  rw [e]
  exact div_pos this h2

/-- The counterexample `H''` is positive on `(−∞, 2)` except at `1`. -/
theorem olgExH2_pos {l : ℝ} (hl : l < 2) (h1 : l ≠ 1) : 0 < olgExH2 l := by
  simp only [olgExH2]
  have h2 : 0 < 2 - l := by linarith
  have : 0 < (l - 1) ^ 2 := by positivity
  apply div_pos _ (by positivity)
  have : 0 < 5 - 2 * l := by linarith
  positivity

/-- The counterexample `H'` tends to `+∞` at `2⁻`. -/
theorem olgExH1_tendsto : Tendsto olgExH1 (𝓝[<] 2) atTop := by
  have h1 : Tendsto (fun l : ℝ => 2 * (l - 1) ^ 3) (𝓝[<] 2) (𝓝 2) := by
    have : Tendsto (fun l : ℝ => 2 * (l - 1) ^ 3) (𝓝 2) (𝓝 (2 * (2 - 1) ^ 3)) :=
      ((continuous_const.mul ((continuous_id.sub continuous_const).pow 3)).tendsto 2)
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun l : ℝ => (2 - l)⁻¹) (𝓝[<] 2) atTop := by
    have : Tendsto (fun l : ℝ => 2 - l) (𝓝[<] 2) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun l : ℝ => 2 - l) (𝓝 2) (𝓝 (2 - 2)) :=
          (continuous_const.sub continuous_id).tendsto 2
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with l hl
        simp only [mem_Ioi, sub_pos]; exact hl
    exact tendsto_inv_nhdsGT_zero.comp this
  have := tendsto_atTop_add_const_left _ 1 (h1.pos_mul_atTop (by norm_num) h2)
  refine this.congr fun l => ?_
  simp only [olgExH1, div_eq_mul_inv]

/-- The counterexample `H'` is strictly increasing on `(−∞, 2)` (although `H''(1) = 0`). -/
theorem olgExH1_strictMonoOn : StrictMonoOn olgExH1 (Iio 2) := by
  have hc : ∀ s ⊆ Iio (2 : ℝ), ContinuousOn olgExH1 s := fun s hs l hl =>
    (olgExH1_hasDerivAt (hs hl)).continuousAt.continuousWithinAt
  have h1 : StrictMonoOn olgExH1 (Iic 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic 1) (hc _ fun l hl => ?_) fun l hl => ?_
    · exact lt_of_le_of_lt (mem_Iic.1 hl) (by norm_num)
    · rw [interior_Iic] at hl
      have hl2 : l < 2 := lt_trans hl (by norm_num)
      rw [(olgExH1_hasDerivAt hl2).deriv]
      exact olgExH2_pos hl2 (ne_of_lt hl)
  have h2 : StrictMonoOn olgExH1 (Ico 1 2) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 1 2) (hc _ fun l hl => hl.2) fun l hl => ?_
    rw [interior_Ico] at hl
    rw [(olgExH1_hasDerivAt hl.2).deriv]
    exact olgExH2_pos hl.2 (ne_of_gt hl.1)
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · exact h1 (mem_Iic.2 (hxy.le.trans hy1)) (mem_Iic.2 hy1) hxy
  rcases le_or_gt 1 x with hx1 | hx1
  · exact h2 ⟨hx1, hx⟩ ⟨hx1.trans hxy.le, hy⟩ hxy
  · exact (h1 (mem_Iic.2 hx1.le) (mem_Iic.2 le_rfl) hx1).trans
      (h2 ⟨le_rfl, by norm_num⟩ ⟨hy1.le, hy⟩ hy1)

/-- The counterexample satisfies the labour part of Assumption 17.1 with `L = 2`. -/
theorem olgExH_assumption : Assumption17_1H 2 olgExH olgExH1 olgExH2 := by
  have hcont : ContinuousOn olgExH (Ico 0 2) := fun l hl =>
    (olgExH_hasDerivAt hl.2).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn olgExH (Ico 0 2) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 2) hcont fun l hl => ?_
    rw [interior_Ico] at hl
    rw [(olgExH_hasDerivAt hl.2).deriv]
    exact olgExH1_pos hl.1 hl.2
  refine ⟨by norm_num, fun l hl => ?_, fun l hl => (olgExH_hasDerivAt hl.2).hasDerivWithinAt,
    fun l hl => (olgExH1_hasDerivAt hl.2).hasDerivWithinAt, ?_, hmono, ?_, by norm_num [olgExH1],
    olgExH1_tendsto⟩
  · have h0 : 0 < olgExH 0 := by
      simp only [olgExH]
      have := Real.log_two_lt_d9
      norm_num
      linarith
    exact h0.le.trans (hmono.monotoneOn (left_mem_Ico.2 (by norm_num)) hl hl.1)
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun l hl => ?_
    have : (2 : ℝ) - l ≠ 0 := by linarith [hl.2]
    exact pow_ne_zero 2 this
  · refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ico 0 2) hcont ?_
    rw [interior_Ico]
    intro x hx y hy hxy
    rw [(olgExH_hasDerivAt hx.2).deriv, (olgExH_hasDerivAt hy.2).deriv]
    exact olgExH1_strictMonoOn hx.2 hy.2 hxy

/-- **Correction (Proposition 1, (6)).** The book says the elasticity
`l ζ'(l)/ζ(l) = (H'(l) + l H''(l))/H'(l)` is `≥ 1` "with equality only at `l = 0`". This is
false: strict convexity allows `H''(l₀) = 0` at `l₀ > 0`. For `olgExH` (Assumption 17.1 with
`L = 2`) the elasticity equals `1` at `l = 1`. -/
theorem proposition_1_elasticity_counterexample :
    ¬ ∀ (L : ℝ) (H H' H'' : ℝ → ℝ), Assumption17_1H L H H' H'' →
      ∀ l ∈ Ioo 0 L, 1 < l * (H' l + l * H'' l) / olgZeta H' l := fun h => by
  have := h 2 olgExH olgExH1 olgExH2 olgExH_assumption 1 ⟨by norm_num, by norm_num⟩
  norm_num [olgExH1, olgExH2, olgZeta] at this

/-- **Equation (6), corrected.** For `l ∈ (0, L)` the elasticity of `ζ` is at least one. -/
theorem zeta_elasticity_ge_one (hH : Assumption17_1H L H H' H'') {l : ℝ} (hl : l ∈ Ioo 0 L) :
    1 ≤ l * (H' l + l * H'' l) / olgZeta H' l := by
  have hz : 0 < olgZeta H' l := mul_pos hl.1 (hH.H'_pos hl)
  rw [le_div_iff₀ hz, one_mul, olgZeta]
  have := mul_nonneg (mul_nonneg hl.1.le hl.1.le) (hH.H''_nonneg hl)
  nlinarith

/-! ### The inverse of `ζ` (p. 507) -/

/-- `ζ⁻¹ : ℝ₊ → [0, L)`, the inverse of `ζ(l) = l H'(l)` on `[0, L)` (p. 507). -/
noncomputable def olgZetaInv (L : ℝ) (H' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Function.invFunOn (olgZeta H') (Ico 0 L) y

namespace Assumption17_1H

variable (hH : Assumption17_1H L H H' H'')
include hH

/-- `ζ` is strictly increasing on `[0, L)`. -/
theorem zeta_strictMonoOn : StrictMonoOn (olgZeta H') (Ico 0 L) := by
  intro x hx y hy hxy
  have hy0 : 0 < y := hx.1.trans_lt hxy
  have h1 : H' x < H' y := hH.H'_strictMonoOn hx hy hxy
  have h2 : 0 < H' y := hH.H'_pos ⟨hy0, hy.2⟩
  simp only [olgZeta]
  nlinarith [hx.1]

/-- `ζ` is continuous on `[0, L)`. -/
theorem zeta_continuousOn : ContinuousOn (olgZeta H') (Ico 0 L) :=
  continuousOn_id.mul hH.H'_continuousOn

/-- `ζ(l) ≥ 0` on `[0, L)`, with equality only at `0`. -/
theorem zeta_pos {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 < olgZeta H' l :=
  mul_pos hl.1 (hH.H'_pos hl)

/-- `ζ` maps `[0, L)` onto `ℝ₊`. -/
theorem zeta_surj {y : ℝ} (hy : 0 ≤ y) : ∃ l ∈ Ico 0 L, olgZeta H' l = y := by
  have hL := hH.L_pos
  have h1 : ∀ᶠ l in 𝓝[<] L, 2 * y / L < H' l :=
    hH.H'_tendsto.eventually (eventually_gt_atTop _)
  have h2 : ∀ᶠ l in 𝓝[<] L, l ∈ Ioo (L / 2) L := Ioo_mem_nhdsLT (by linarith)
  obtain ⟨l₁, hl₁, hl₁'⟩ := (h1.and h2).exists
  have hz : y ≤ olgZeta H' l₁ := by
    simp only [olgZeta]
    have : 2 * y / L * (L / 2) = y := by field_simp
    have h3 : 0 ≤ 2 * y / L := by positivity
    nlinarith [hl₁'.1]
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun z hz => ⟨hz.1, hz.2.trans_lt hl₁'.2⟩
  obtain ⟨l, hl, hly⟩ := intermediate_value_Icc (by linarith [hl₁'.1] : (0 : ℝ) ≤ l₁)
    (hH.zeta_continuousOn.mono hsub) ⟨by simp [olgZeta, hy], hz⟩
  exact ⟨l, hsub hl, hly⟩

/-- `ζ⁻¹(y) ∈ [0, L)` for `y ≥ 0`. -/
theorem zetaInv_mem {y : ℝ} (hy : 0 ≤ y) : olgZetaInv L H' y ∈ Ico 0 L :=
  Function.invFunOn_mem (hH.zeta_surj hy)

/-- `ζ(ζ⁻¹(y)) = y` for `y ≥ 0`. -/
theorem zeta_zetaInv {y : ℝ} (hy : 0 ≤ y) : olgZeta H' (olgZetaInv L H' y) = y :=
  Function.invFunOn_eq (hH.zeta_surj hy)

/-- `ζ⁻¹(ζ(l)) = l` for `l ∈ [0, L)`. -/
theorem zetaInv_zeta {l : ℝ} (hl : l ∈ Ico 0 L) : olgZetaInv L H' (olgZeta H' l) = l := by
  have h0 : 0 ≤ olgZeta H' l := mul_nonneg hl.1 (hH.H'_nonneg hl)
  exact hH.zeta_strictMonoOn.injOn (hH.zetaInv_mem h0) hl (hH.zeta_zetaInv h0)

/-- `ζ⁻¹(0) = 0`. -/
theorem zetaInv_zero : olgZetaInv L H' 0 = 0 := by
  have := hH.zetaInv_zeta (left_mem_Ico.2 hH.L_pos)
  simpa [olgZeta] using this

/-- `ζ⁻¹` is strictly increasing on `ℝ₊`. -/
theorem zetaInv_strictMonoOn : StrictMonoOn (olgZetaInv L H') (Ici 0) := by
  intro x hx y hy hxy
  by_contra h
  have h' := hH.zeta_strictMonoOn.monotoneOn (hH.zetaInv_mem hy) (hH.zetaInv_mem hx)
    (not_lt.1 h)
  rw [hH.zeta_zetaInv hx, hH.zeta_zetaInv hy] at h'
  linarith

/-- `ζ⁻¹(y) > 0` for `y > 0`. -/
theorem zetaInv_pos {y : ℝ} (hy : 0 < y) : 0 < olgZetaInv L H' y := by
  have := hH.zetaInv_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy
  rwa [hH.zetaInv_zero] at this

/-- `ζ⁻¹` maps `ℝ₊` onto `[0, L)`. -/
theorem zetaInv_image_Ici : olgZetaInv L H' '' Ici 0 = Ico 0 L := by
  refine Subset.antisymm (image_subset_iff.2 fun y hy => hH.zetaInv_mem hy) fun l hl => ?_
  exact ⟨olgZeta H' l, mul_nonneg hl.1 (hH.H'_nonneg hl), hH.zetaInv_zeta hl⟩

/-- `ζ⁻¹` maps `(0, ∞)` onto `(0, L)`. -/
theorem zetaInv_image_Ioi : olgZetaInv L H' '' Ioi 0 = Ioo 0 L := by
  refine Subset.antisymm (image_subset_iff.2 fun y hy =>
    ⟨hH.zetaInv_pos hy, (hH.zetaInv_mem (le_of_lt hy)).2⟩) fun l hl => ?_
  exact ⟨olgZeta H' l, hH.zeta_pos hl, hH.zetaInv_zeta (Ioo_subset_Ico_self hl)⟩

/-- `ζ⁻¹` is continuous on `ℝ₊` (p. 507). -/
theorem zetaInv_continuousOn : ContinuousOn (olgZetaInv L H') (Ici 0) := by
  intro y hy
  rcases (mem_Ici.1 hy).eq_or_lt with h | h
  · rw [← h]
    refine continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin
      hH.zetaInv_strictMonoOn.monotoneOn self_mem_nhdsWithin ?_
    rw [hH.zetaInv_image_Ici, hH.zetaInv_zero]
    exact Ico_mem_nhdsGE hH.L_pos
  · refine (continuousAt_of_monotoneOn_of_image_mem_nhds
      (hH.zetaInv_strictMonoOn.monotoneOn.mono Ioi_subset_Ici_self) (Ioi_mem_nhds h)
      ?_).continuousWithinAt
    rw [hH.zetaInv_image_Ioi]
    exact Ioo_mem_nhds (hH.zetaInv_pos h) (hH.zetaInv_mem h.le).2

/-- `ζ'(l) = H'(l) + l H''(l)` on `(0, L)`. -/
theorem zeta_hasDerivAt {l : ℝ} (hl : l ∈ Ioo 0 L) :
    HasDerivAt (olgZeta H') (H' l + l * H'' l) l := by
  have h := (hasDerivAt_id' l).mul (hH.H'_hasDerivAt hl)
  exact h.congr_deriv (by ring)

/-- `ζ'(l) > 0` on `(0, L)`. -/
theorem zeta_deriv_pos {l : ℝ} (hl : l ∈ Ioo 0 L) : 0 < H' l + l * H'' l :=
  add_pos_of_pos_of_nonneg (hH.H'_pos hl) (mul_nonneg hl.1.le (hH.H''_nonneg hl))

/-- `ζ⁻¹` is differentiable at `y > 0`, with `(ζ⁻¹)'(y) = 1/ζ'(ζ⁻¹(y))`. -/
theorem zetaInv_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (olgZetaInv L H')
      (H' (olgZetaInv L H' y) + olgZetaInv L H' y * H'' (olgZetaInv L H' y))⁻¹ y := by
  have hl : olgZetaInv L H' y ∈ Ioo 0 L := ⟨hH.zetaInv_pos hy, (hH.zetaInv_mem hy.le).2⟩
  refine HasDerivAt.of_local_left_inverse
    ((hH.zetaInv_continuousOn y (mem_Ici.2 hy.le)).continuousAt (Ici_mem_nhds hy))
    (hH.zeta_hasDerivAt hl) (hH.zeta_deriv_pos hl).ne' ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  exact hH.zeta_zetaInv (le_of_lt hz)

end Assumption17_1H

/-! ### The change of variable `f = ζ ∘ n` (p. 507) -/

/-- **(8) ⇔ (4)** (p. 507). For `n : X → [0, L)`, `n` satisfies (4) iff `f = ζ ∘ n` satisfies
(8), `f(x) = ∫ φ[x' ζ⁻¹(f(x'))] π(x, dx')`; i.e. iff `f` is a fixed point of the operator (9). -/
theorem eq8_iff_eq4 (hH : Assumption17_1H L H H' H'') {a b : ℝ} (κ : Kernel (Icc a b) (Icc a b))
    (n : Icc a b → ℝ) (hn : ∀ x, n x ∈ Ico 0 L) :
    (∀ x, olgZeta H' (n x) = ∫ x', olgPhi V' (x'.1 * n x') ∂κ x) ↔
      ∀ x, olgZeta H' (n x) =
        ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' (olgZeta H' (n x'))) ∂κ x := by
  have h : ∀ x', olgZetaInv L H' (olgZeta H' (n x')) = n x' := fun x' => hH.zetaInv_zeta (hn x')
  simp only [h]

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Proposition 2: the OLG model by the contraction mapping theorem

SLP §17.2, pp. 510–516: Exercise 17.3, Assumption 17.2 and Proposition 2.

* **Exercise 17.3** (`ex_17_3`, p. 510): under Assumption 17.1, `G(x, x', y) = φ[x' ζ⁻¹(y)]`
  violates condition (2) of Lemma 17.1 on `D = ℝ₊` (no derivative bound `|G₃| ≤ β < 1`).
* **Assumption 17.2** as stated (`Assumption17_2`, p. 513) and repaired (`Assumption17_2R`, the
  bounds (5) for `y > 0` only); the repaired utility assumption `Assumption17_1VR` (`V`
  continuous on `ℝ₊`, `C²` on `(0, ∞)`).
* `crra_assumption17_1VR`, `crra_assumption17_2R`: `V(y) = y^{1−σ}/(1 − σ)`, `0 < σ < 1`,
  satisfies both repaired assumptions (relative risk aversion `≡ σ`, `β = 1 − σ`);
  `repaired_assumptions_nonvacuous`.
* `proposition_1_repaired`: Proposition 1 still holds under the repaired utility assumption
  (`V'(0+) = ∞` allowed), as the transcription's NOTE claims.
* **Proposition 2** (`proposition_2`, p. 513), under the repaired assumptions: exactly one
  bounded continuous strictly positive solution `f*` of (6). Proof steps: `olgG_ge` ((7)),
  `olgG_hyp` (step 4), `olgG_hasDerivAt`, `olgG_elasticity_le` (step 5, condition (4)), then
  `lemma_17_2_fixedPoint`.

**Correction (Assumption 17.2 contradicts Assumption 17.1).** At `y = 0` the middle term of (5)
is `0 < 1 − β`, so Assumption 17.2 never holds (`assumption17_2_counterexample`) and Proposition
2 as stated is vacuous. Restricting (5) to `y > 0` does not help under Assumption 17.1: the lower
bound forces `V'(0+) = ∞` (`assumption17_2R_inconsistent`). The repair (NOTE in the
transcription): `V` only `C²` on `(0, ∞)` and (5) only for `y > 0`; Proposition 2 is proved
under it.

**Correction (Proposition 2, zero fixed point and uniqueness).** `f ≡ 0` also solves (6)
(`proposition_2_zero_fixedPoint`), so uniqueness holds only among strictly positive solutions
(`proposition_2_nonneg_counterexample`). The book's "any `K > 1/C` could have been used" needs
`ε_k → 0`, which it does not state; it is true (`epsK_exists`, `epsK_tendsto_zero`:
`ζ⁻¹(ε_k) = k ε_k < L`). `proposition_2` uses instead the sets `[ζ(l), ∞)`, `0 < l ≤ l₀`, which
exhaust `(0, ∞)` as `l → 0`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- For every `C > 0` there is `l ∈ (0, L)` with `H'(l) < C` (`H'` is continuous with
`H'(0) = 0`). -/
theorem Assumption17_1H.exists_H'_lt (hH : Assumption17_1H L H H' H'') {C : ℝ} (hC : 0 < C) :
    ∃ l ∈ Ioo 0 L, H' l < C := by
  have hcont := hH.H'_continuousOn 0 (left_mem_Ico.2 hH.L_pos)
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, h⟩ := hcont C hC
  set l := min (δ / 2) (L / 2) with hl
  have hl0 : 0 < l := lt_min (half_pos hδ) (half_pos hH.L_pos)
  have hlL : l < L := (min_le_right _ _).trans_lt (half_lt_self hH.L_pos)
  have hlδ : l < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨l, ⟨hl0, hlL⟩, ?_⟩
  have := h ⟨hl0.le, hlL⟩ (by rw [Real.dist_eq, sub_zero, abs_of_pos hl0]; exact hlδ)
  rw [Real.dist_eq, hH.H'_zero, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-! ### Exercise 17.3 -/

/-- **Exercise 17.3** (p. 510). Under Assumption 17.1, with `X = [a, b]` (`0 < a ≤ b`),
`D = ℝ₊` and `G(x, x', y) = φ[x' ζ⁻¹(y)]`, condition (2) of Lemma 17.1 fails: there is no
`β < 1` and no derivative `G₃` of `G(x, x', ·)` on `ℝ₊` with `|G₃| ≤ β`. Indeed (2) would make
`G(x, x', ·)` `β`-Lipschitz, but `G(x, x', 0) = 0` while `G(x, x', ζ(l)) ≥ a l V'(aL) > ζ(l)`
for small `l > 0`. (The manual writes `1/ζ'(y)` for `(ζ⁻¹)'(y) = 1/ζ'(ζ⁻¹(y))`.) -/
theorem ex_17_3 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hA : Assumption17_1 L H H' H'' V V' V'') :
    ¬ ∃ β < 1, ∃ G3 : Icc a b → Icc a b → ℝ → ℝ,
      (∀ x x', ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt (fun y => olgPhi V' (x'.1 * olgZetaInv L H' y))
        (G3 x x' y) (Ici 0) y) ∧ ∀ x x', ∀ y ∈ Ici (0 : ℝ), |G3 x x' y| ≤ β := by
  rintro ⟨β, hβ, G3, hder, hbd⟩
  have hH := hA.hH
  have hV := hA.hV
  set x₀ : Icc a b := ⟨a, le_rfl, hab⟩
  have hC : 0 < a * V' (a * L) := mul_pos ha (hV.V'_pos (mul_pos ha hH.L_pos).le)
  obtain ⟨l, hl, hlC⟩ := hH.exists_H'_lt hC
  have hy : 0 ≤ olgZeta H' l := (hH.zeta_pos hl).le
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hder x₀ x₀)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hbd x₀ x₀ y hy) (convex_Ici 0)
    (mem_Ici.2 le_rfl) (mem_Ici.2 hy)
  rw [hH.zetaInv_zeta (Ioo_subset_Ico_self hl), hH.zetaInv_zero, mul_zero, sub_zero,
    Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hx0 : (x₀ : ℝ) = a := rfl
  simp only [olgPhi, zero_mul, sub_zero, hx0] at hmvt
  have hal : 0 < a * l := mul_pos ha hl.1
  have hV'le : V' (a * L) ≤ V' (a * l) :=
    hV.V'_strictAntiOn.antitoneOn (mem_Ici.2 hal.le) (mem_Ici.2 (mul_pos ha hH.L_pos).le)
      (mul_le_mul_of_nonneg_left hl.2.le ha.le)
  have hpos : 0 < a * l * V' (a * l) := mul_pos hal (hV.V'_pos hal.le)
  rw [abs_of_pos hpos, abs_of_nonneg hy] at hmvt
  have h1 : olgZeta H' l < a * l * V' (a * l) := by
    simp only [olgZeta]
    have : l * H' l < l * (a * V' (a * L)) := mul_lt_mul_of_pos_left hlC hl.1
    nlinarith
  have h2 : β * olgZeta H' l ≤ olgZeta H' l := by
    rcases le_or_gt β 0 with h | h
    · nlinarith
    · nlinarith
  linarith

/-! ### Assumption 17.2 and its inconsistency with Assumption 17.1 -/

/-- **Assumption 17.2** (p. 513), as stated: for some `β ∈ [0, 1)`,
`1 − β ≤ −y V''(y)/V'(y) ≤ 1 + β` for all `y ∈ ℝ₊`. -/
structure Assumption17_2 (β : ℝ) (V' V'' : ℝ → ℝ) : Prop where
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  lower : ∀ y, 0 ≤ y → 1 - β ≤ -(y * V'' y) / V' y
  upper : ∀ y, 0 ≤ y → -(y * V'' y) / V' y ≤ 1 + β

/-- **Assumption 17.2, repaired**: the bounds (5) only for `y > 0`. -/
structure Assumption17_2R (β : ℝ) (V' V'' : ℝ → ℝ) : Prop where
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  lower : ∀ y, 0 < y → 1 - β ≤ -(y * V'' y) / V' y
  upper : ∀ y, 0 < y → -(y * V'' y) / V' y ≤ 1 + β

/-- **Correction (Assumption 17.2).** As stated, Assumption 17.2 can never hold: at `y = 0`
the middle term of (5) is `−0 · V''(0)/V'(0) = 0 < 1 − β`. Hence no `(H, V)` satisfies
Assumptions 17.1 and 17.2, and Proposition 2 as stated is vacuous. -/
theorem assumption17_2_counterexample {β : ℝ} : ¬ Assumption17_2 β V' V'' := fun h => by
  have := h.lower 0 le_rfl
  simp only [zero_mul, neg_zero, zero_div] at this
  linarith [h.β_lt_one]

/-- **Correction (Assumption 17.2), continued.** Restricting (5) to `y > 0` does not reconcile it
with Assumption 17.1 either: the lower bound forces `V'(y) ≥ V'(1) y^{−(1−β)} → ∞` as `y ↓ 0`,
while under Assumption 17.1 `V'` is bounded by `V'(0)`. Proof: `u(t) = ln V'(t) + (1 − β) ln t`
is nonincreasing on `(0, ∞)`. -/
theorem assumption17_2R_inconsistent (hV : Assumption17_1V V V' V'') {β : ℝ} :
    ¬ Assumption17_2R β V' V'' := fun h => by
  have hβ : 0 < 1 - β := sub_pos.2 h.β_lt_one
  set u : ℝ → ℝ := fun t => Real.log (V' t) + (1 - β) * Real.log t with hu
  have hderiv : ∀ t, 0 < t → HasDerivAt u (V'' t / V' t + (1 - β) * t⁻¹) t := fun t ht => by
    have h1 : HasDerivAt V' (V'' t) t := (hV.V'_deriv t ht.le).hasDerivAt (Ici_mem_nhds ht)
    exact (h1.log (hV.V'_pos ht.le).ne').add ((Real.hasDerivAt_log ht.ne').const_mul (1 - β))
  have hanti : AntitoneOn u (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (fun t ht =>
      (hderiv t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ioi] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at ht
      rw [(hderiv t ht).deriv]
      have hl := h.lower t ht
      have hVp := hV.V'_pos ht.le
      rw [le_div_iff₀ hVp] at hl
      rw [div_add' _ _ _ hVp.ne', div_nonpos_iff]
      right
      refine ⟨?_, hVp.le⟩
      have : (1 - β) * t⁻¹ * V' t ≤ -V'' t := by
        rw [mul_comm (1 - β), mul_assoc, ← le_div_iff₀' (inv_pos.2 ht), div_inv_eq_mul]
        nlinarith
      linarith
  have hV0 := hV.V'_pos (le_refl (0 : ℝ))
  have hV1 := hV.V'_pos (zero_le_one' ℝ)
  have hle : V' 1 ≤ V' 0 := hV.V'_le_V'_zero zero_le_one
  set M := (Real.log (V' 0) - Real.log (V' 1) + 1) / (1 - β) with hM
  have hMpos : 0 < M := div_pos (by linarith [Real.log_le_log hV1 hle]) hβ
  set t := Real.exp (-M)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have key := hanti (mem_Ioi.2 ht) (mem_Ioi.2 one_pos) ht1
  simp only [hu, Real.log_one, mul_zero, add_zero] at key
  have hlt : Real.log t = -M := Real.log_exp _
  have e : (1 - β) * -M = -(Real.log (V' 0) - Real.log (V' 1) + 1) := by
    rw [hM]; field_simp
  rw [hlt, e] at key
  have hVt : V' t ≤ V' 0 := hV.V'_le_V'_zero ht.le
  have := Real.log_le_log (hV.V'_pos ht.le) hVt
  linarith

/-! ### Repaired Assumption 17.1 -/

/-- **Assumption 17.1, utility part, repaired**: `V : ℝ₊ → ℝ₊` continuous, strictly increasing
and strictly concave, and twice continuously differentiable on `ℝ₊₊ = (0, ∞)` only (so
`V'(0+) = +∞` is allowed). -/
structure Assumption17_1VR (V V' V'' : ℝ → ℝ) : Prop where
  V_nonneg : ∀ y, 0 ≤ y → 0 ≤ V y
  V_cont : ContinuousOn V (Ici 0)
  V_deriv : ∀ y, 0 < y → HasDerivAt V (V' y) y
  V'_deriv : ∀ y, 0 < y → HasDerivAt V' (V'' y) y
  V''_cont : ContinuousOn V'' (Ioi 0)
  V_mono : StrictMonoOn V (Ici 0)
  V_conc : StrictConcaveOn ℝ (Ici 0) V

namespace Assumption17_1VR

variable (hV : Assumption17_1VR V V' V'')
include hV

/-- `V'(y) > 0` for `y > 0`. -/
theorem V'_pos {y : ℝ} (hy : 0 < y) : 0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := mem_Ici.2 hy.le
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h1 := hV.V_conc.slope_lt_of_hasDerivWithinAt hy' hy1 (by linarith)
    (hV.V_deriv y hy).hasDerivWithinAt
  have h2 : 0 < slope V y (y + 1) := by
    rw [slope_def_field]
    exact div_pos (sub_pos.2 (hV.V_mono hy' hy1 (by linarith))) (by linarith)
  linarith

/-- `V'` is strictly decreasing on `(0, ∞)`. -/
theorem V'_strictAntiOn : StrictAntiOn V' (Ioi 0) := fun x hx y hy hxy =>
  (hV.V_conc.slope_lt_of_hasDerivWithinAt (mem_Ici.2 (le_of_lt hx)) (mem_Ici.2 (le_of_lt hy))
    hxy (hV.V_deriv x hx).hasDerivWithinAt).trans'
    (hV.V_conc.lt_slope_of_hasDerivWithinAt (mem_Ici.2 (le_of_lt hx)) (mem_Ici.2 (le_of_lt hy))
      hxy (hV.V_deriv y hy).hasDerivWithinAt)

/-- `V'` is continuous on `(0, ∞)`. -/
theorem V'_continuousOn : ContinuousOn V' (Ioi 0) := fun y hy =>
  (hV.V'_deriv y hy).continuousAt.continuousWithinAt

/-- `φ(y) = y V'(y)` is continuous on `(0, ∞)`. -/
theorem phi_continuousOn : ContinuousOn (olgPhi V') (Ioi 0) :=
  continuousOn_id.mul hV.V'_continuousOn

/-- `φ'(y) = V'(y) + y V''(y)` for `y > 0`. -/
theorem phi_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (olgPhi V') (V' y + y * V'' y) y :=
  ((hasDerivAt_id' y).mul (hV.V'_deriv y hy)).congr_deriv (by ring)

end Assumption17_1VR

/-- **Example satisfying the repaired assumptions.** For `0 < σ < 1`,
`V(y) = y^{1−σ}/(1 − σ)` (with `V'(y) = y^{−σ}`, `V''(y) = −σ y^{−σ−1}`) satisfies the
repaired utility part of Assumption 17.1. -/
theorem crra_assumption17_1VR {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Assumption17_1VR (fun y => y ^ (1 - σ) / (1 - σ)) (fun y => y ^ (-σ))
      (fun y => -σ * y ^ (-σ - 1)) := by
  have hc : 0 < 1 - σ := sub_pos.2 hσ1
  refine ⟨fun y hy => div_nonneg (Real.rpow_nonneg hy _) hc.le,
    ((Real.continuous_rpow_const hc.le).div_const _).continuousOn, fun y hy => ?_,
    fun y hy => ?_, ?_, fun x hx y hy hxy => ?_, ?_⟩
  · have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hy.ne')).div_const (1 - σ)
    convert this using 1
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  · have := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hy.ne')
    exact this
  · intro y hy
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const y _
      (Or.inl (ne_of_gt hy)))).continuousWithinAt
  · exact div_lt_div_of_pos_right (Real.rpow_lt_rpow hx hxy hc) hc
  · refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (Real.strictConcaveOn_rpow hc (by linarith : 1 - σ < 1)).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    calc a * (x ^ (1 - σ) / (1 - σ)) + b * (y ^ (1 - σ) / (1 - σ))
        = (a * x ^ (1 - σ) + b * y ^ (1 - σ)) / (1 - σ) := by ring
      _ < (a * x + b * y) ^ (1 - σ) / (1 - σ) := div_lt_div_of_pos_right this hc

/-- The CRRA example has constant relative risk aversion `σ` and satisfies the repaired
Assumption 17.2 with `β = 1 − σ`. -/
theorem crra_assumption17_2R {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Assumption17_2R (1 - σ) (fun y => y ^ (-σ)) (fun y => -σ * y ^ (-σ - 1)) := by
  have hrra : ∀ y : ℝ, 0 < y → -(y * (-σ * y ^ (-σ - 1))) / y ^ (-σ) = σ := fun y hy => by
    have h1 : y * y ^ (-σ - 1) = y ^ (-σ) := by
      rw [Real.rpow_sub_one hy.ne', mul_div_cancel₀ _ hy.ne']
    have h2 : 0 < y ^ (-σ) := Real.rpow_pos_of_pos hy _
    rw [show -(y * (-σ * y ^ (-σ - 1))) = σ * (y * y ^ (-σ - 1)) by ring, h1,
      mul_div_assoc, div_self h2.ne', mul_one]
  refine ⟨by linarith, by linarith, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hrra y hy]; linarith
  · rw [hrra y hy]; linarith

/-- The repaired assumptions are not vacuous: `olgExH` (with `L = 2`) and the CRRA utility with
`σ = 1/2` satisfy all of them. -/
theorem repaired_assumptions_nonvacuous :
    ∃ (L : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) (β : ℝ), Assumption17_1H L H H' H'' ∧
      Assumption17_1VR V V' V'' ∧ Assumption17_2R β V' V'' :=
  ⟨2, olgExH, olgExH1, olgExH2, _, _, _, _, olgExH_assumption,
    crra_assumption17_1VR (σ := 1 / 2) (by norm_num) (by norm_num),
    crra_assumption17_2R (σ := 1 / 2) (by norm_num) (by norm_num)⟩

/-! ### Proposition 1 survives the repair -/

/-- Under the repaired Assumption 17.1, `x' ↦ x' V'(l x')` is a bounded continuous function on
`X = [a, b]` for `l > 0`. -/
noncomputable def olgMargBCF {a b : ℝ} (ha : 0 < a) (hV : Assumption17_1VR V V' V'') {l : ℝ}
    (hl : 0 < l) : Icc a b →ᵇ ℝ :=
  mkOfCompact ⟨fun x' => x'.1 * V' (l * x'.1), continuous_subtype_val.mul
    (hV.V'_continuousOn.comp_continuous (continuous_const.mul continuous_subtype_val)
      fun x' => mul_pos hl (ha.trans_le x'.2.1))⟩

/-- Under the repaired Assumption 17.1, `l ↦ ∫ x' V'(l x') dμ` is continuous on `(0, ∞)`. -/
theorem continuousOn_margUtil_R {a b : ℝ} (ha : 0 < a) (hV : Assumption17_1VR V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    ContinuousOn (margUtil V' μ (fun x' : Icc a b => x'.1)) (Ioi 0) := by
  intro l₀ hl₀
  have hl₀' : 0 < l₀ := hl₀
  have hs : Ioi (l₀ / 2) ∈ 𝓝 l₀ := Ioi_mem_nhds (by linarith)
  refine (ContinuousOn.continuousAt ?_ hs).continuousWithinAt
  refine continuousOn_of_dominated (bound := fun _ => b * V' (l₀ / 2 * a))
    (fun l hl => (olgMargBCF ha hV (lt_trans (half_pos hl₀') hl)).integrable μ
      |>.aestronglyMeasurable) (fun l hl => ae_of_all _ fun x' => ?_) (integrable_const _)
    (ae_of_all _ fun x' => ?_)
  · have hl' : l₀ / 2 < l := hl
    have hx : 0 < x'.1 := ha.trans_le x'.2.1
    have hlx : 0 < l * x'.1 := mul_pos (lt_trans (half_pos hl₀') hl') hx
    have h1 : l₀ / 2 * a ≤ l * x'.1 := mul_le_mul hl'.le x'.2.1 ha.le (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hx (hV.V'_pos hlx))]
    exact mul_le_mul x'.2.2 (hV.V'_strictAntiOn.antitoneOn (mul_pos (half_pos hl₀') ha) hlx h1)
      (hV.V'_pos hlx).le ((ha.trans_le x'.2.1).le.trans x'.2.2)
  · have hx : 0 < x'.1 := ha.trans_le x'.2.1
    exact continuousOn_const.mul (hV.V'_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun l hl => mul_pos (lt_trans (half_pos hl₀') hl) hx)

/-- Under the repaired Assumption 17.1, `l ↦ ∫ x' V'(l x') dμ` is strictly decreasing on
`(0, ∞)`. -/
theorem margUtil_R_strictAntiOn {a b : ℝ} (ha : 0 < a) (hV : Assumption17_1VR V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    StrictAntiOn (margUtil V' μ (fun x' : Icc a b => x'.1)) (Ioi 0) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have i1 : Integrable (fun x' : Icc a b => x'.1 * V' (l₁ * x'.1)) μ :=
    (olgMargBCF ha hV hl₁).integrable μ
  have i2 : Integrable (fun x' : Icc a b => x'.1 * V' (l₂ * x'.1)) μ :=
    (olgMargBCF ha hV hl₂).integrable μ
  rw [← sub_pos, margUtil, margUtil, ← integral_sub i1 i2]
  refine integral_pos_of_forall_pos (i1.sub i2) fun x' => ?_
  have hx : 0 < x'.1 := ha.trans_le x'.2.1
  change 0 < x'.1 * V' (l₁ * x'.1) - x'.1 * V' (l₂ * x'.1)
  rw [← mul_sub]
  exact mul_pos hx (sub_pos.2 (hV.V'_strictAntiOn (mul_pos hl₁ hx) (mul_pos hl₂ hx)
    (mul_lt_mul_of_pos_right hlt hx)))

/-- **Proposition 1 under the repaired assumptions** (the transcription's NOTE: Proposition 1
survives the repair). With `V` only `C²` on `(0, ∞)` (so `V'(0+) = ∞` is allowed), (5) still
has exactly one solution in `(0, L)`; existence now uses `∫ x' V'(x' l) dμ ≥ a V'(bL)` on
`(0, L)` while `H'(l) → 0` as `l → 0`. -/
theorem proposition_1_repaired {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (μ : Measure (Icc a b)) [IsProbabilityMeasure μ] :
    ∃! n, n ∈ Ioo 0 L ∧ olgZeta H' n = ∫ x', olgPhi V' (x'.1 * n) ∂μ := by
  have hb : 0 < b := ha.trans_le hab
  set m := margUtil V' μ (fun x' : Icc a b => x'.1)
  have hiff : ∀ l, 0 < l → (olgZeta H' l = ∫ x', olgPhi V' (x'.1 * l) ∂μ ↔ H' l = m l) :=
    fun l hl => by
      rw [integral_olgPhi, olgZeta]
      exact ⟨fun h => mul_left_cancel₀ hl.ne' h, fun h => by rw [h]⟩
  have hfoc : StrictMonoOn (fun l => H' l - m l) (Ioo 0 L) := fun x hx y hy hxy => by
    have h1 := hH.H'_strictMonoOn (Ioo_subset_Ico_self hx) (Ioo_subset_Ico_self hy) hxy
    have h2 := margUtil_R_strictAntiOn ha hV μ (mem_Ioi.2 hx.1) (mem_Ioi.2 hy.1) hxy
    linarith
  have hlow : ∀ l ∈ Ioo 0 L, a * V' (b * L) ≤ m l := fun l hl => by
    have i : Integrable (fun x' : Icc a b => x'.1 * V' (l * x'.1)) μ :=
      (olgMargBCF ha hV hl.1).integrable μ
    have h := integral_mono (integrable_const (a * V' (b * L))) i fun x' => by
        have hx : 0 < x'.1 := ha.trans_le x'.2.1
        have hlx : 0 < l * x'.1 := mul_pos hl.1 hx
        change a * V' (b * L) ≤ x'.1 * V' (l * x'.1)
        exact mul_le_mul x'.2.1 (hV.V'_strictAntiOn.antitoneOn hlx
          (mem_Ioi.2 (mul_pos hb hH.L_pos))
          (by rw [mul_comm b L]; exact mul_le_mul hl.2.le x'.2.2 hx.le hH.L_pos.le))
          (hV.V'_pos (mul_pos hb hH.L_pos)).le hx.le
    simpa [m, margUtil] using h
  obtain ⟨l₀, hl₀, hl₀C⟩ := hH.exists_H'_lt (mul_pos ha (hV.V'_pos (mul_pos hb hH.L_pos)))
  obtain ⟨l₁, hl₁, hl₁M⟩ := hH.exists_H'_gt (m l₀)
  have h0 : H' l₀ - m l₀ < 0 := by linarith [hlow l₀ hl₀]
  have hlt : l₀ < l₁ := by
    by_contra h
    have := hH.H'_strictMonoOn.monotoneOn (Ioo_subset_Ico_self hl₁) (Ioo_subset_Ico_self hl₀)
      (not_lt.1 h)
    linarith [hlow l₀ hl₀]
  have h1 : 0 < H' l₁ - m l₁ := by
    have := margUtil_R_strictAntiOn ha hV μ (mem_Ioi.2 hl₀.1) (mem_Ioi.2 hl₁.1) hlt
    linarith
  have hsub : Icc l₀ l₁ ⊆ Ioo 0 L := fun y hy => ⟨hl₀.1.trans_le hy.1, hy.2.trans_lt hl₁.2⟩
  have hcont : ContinuousOn (fun l => H' l - m l) (Icc l₀ l₁) :=
    (hH.H'_continuousOn.mono (hsub.trans Ioo_subset_Ico_self)).sub
      ((continuousOn_margUtil_R ha hV μ).mono fun y hy => (hsub hy).1)
  obtain ⟨n, hn, hn0⟩ := intermediate_value_Icc hlt.le hcont ⟨h0.le, h1.le⟩
  have hnL := hsub hn
  refine ⟨n, ⟨hnL, (hiff n hnL.1).2 (by linarith [hn0])⟩, fun k hk => ?_⟩
  have hk' := (hiff k hk.1.1).1 hk.2
  refine hfoc.injOn hk.1 hnL ?_
  rw [hk', sub_self]
  exact hn0.symm

/-! ### Proposition 2 -/

/-- The kernel function `G(x, x', y) = φ[x' ζ⁻¹(y)]` of the OLG operator (9) (p. 509). -/
noncomputable def olgG {a b : ℝ} (L : ℝ) (H' V' : ℝ → ℝ) (_x x' : Icc a b) (y : ℝ) : ℝ :=
  olgPhi V' (x'.1 * olgZetaInv L H' y)

/-- **Step 2 of the proof of Proposition 2, (7).** Let `C = a V'(bL)` and `H'(l₀) < C`. For
`0 < l ≤ l₀` and `y ≥ ζ(l)`, `G(x, x', y) ≥ a l V'(bL) > ζ(l)`, so `G` maps `[ζ(l), ∞)` into
itself. -/
theorem olgG_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {l₀ : ℝ} (hl₀ : l₀ ∈ Ioo 0 L)
    (hC : H' l₀ < a * V' (b * L)) {l : ℝ} (hl : l ∈ Ioc 0 l₀) {y : ℝ}
    (hy : olgZeta H' l ≤ y) (x x' : Icc a b) : olgZeta H' l ≤ olgG L H' V' x x' y := by
  have hb : 0 < b := ha.trans_le hab
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hl₀.2⟩
  have hzl := hH.zeta_pos hl'
  have hy0 : 0 < y := hzl.trans_le hy
  set m := olgZetaInv L H' y
  have hm : m ∈ Ico 0 L := hH.zetaInv_mem hy0.le
  have hlm : l ≤ m := by
    have := hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 hzl.le) (mem_Ici.2 hy0.le) hy
    rwa [hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
  have hx' : a ≤ x'.1 := x'.2.1
  have hz1 : a * l ≤ x'.1 * m := mul_le_mul hx' hlm hl.1.le (ha.le.trans hx')
  have hz0 : 0 < x'.1 * m := (mul_pos ha hl.1).trans_le hz1
  have hz2 : x'.1 * m < b * L :=
    (mul_le_mul_of_nonneg_right x'.2.2 hm.1).trans_lt (mul_lt_mul_of_pos_left hm.2 hb)
  have hV' : V' (b * L) ≤ V' (x'.1 * m) :=
    hV.V'_strictAntiOn.antitoneOn hz0 (mem_Ioi.2 (mul_pos hb hH.L_pos)) hz2.le
  have hVbL := hV.V'_pos (mul_pos hb hH.L_pos)
  have hH'l : H' l ≤ H' l₀ := hH.H'_strictMonoOn.monotoneOn (Ioo_subset_Ico_self hl')
    (Ioo_subset_Ico_self hl₀) hl.2
  simp only [olgG, olgPhi, olgZeta]
  calc l * H' l ≤ l * (a * V' (b * L)) := mul_le_mul_of_nonneg_left (hH'l.trans hC.le) hl.1.le
    _ = a * l * V' (b * L) := by ring
    _ ≤ x'.1 * m * V' (x'.1 * m) := mul_le_mul hz1 hV' hVbL.le hz0.le

/-- **Step 4 of the proof of Proposition 2.** The hypotheses of Exercise 17.2a hold for `G` on
`D = [ζ(l), ∞)`, `0 < l ≤ l₀`. -/
theorem olgG_hyp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {l₀ : ℝ} (hl₀ : l₀ ∈ Ioo 0 L)
    (hC : H' l₀ < a * V' (b * L)) {l : ℝ} (hl : l ∈ Ioc 0 l₀) {κ : Kernel (Icc a b) (Icc a b)}
    (hκ : IsFellerKernel κ) : OLGOperatorHyp (Ici (olgZeta H' l)) (olgG L H' V') κ := by
  have hzl := hH.zeta_pos ⟨hl.1, hl.2.trans_lt hl₀.2⟩
  refine ⟨convex_Ici _, ?_, fun x x' y hy => olgG_ge ha hab hH hV hl₀ hC hl hy x x', hκ⟩
  have hin : ContinuousOn (fun p : Icc a b × Icc a b × ℝ => p.2.1.1 * olgZetaInv L H' p.2.2)
      {p | p.2.2 ∈ Ici (olgZeta H' l)} :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).continuousOn.mul
      (hH.zetaInv_continuousOn.comp (continuous_snd.comp continuous_snd).continuousOn
        fun p hp => mem_Ici.2 (hzl.le.trans hp))
  exact hV.phi_continuousOn.comp hin fun p hp =>
    mul_pos (ha.trans_le p.2.1.2.1) (hH.zetaInv_pos (hzl.trans_le hp))

/-- **Step 4, differentiability.** For `y > 0`, `G(x, x', ·)` has derivative
`G₃ = φ'(x' ζ⁻¹(y)) · x' / ζ'(ζ⁻¹(y))`. -/
theorem olgG_hasDerivAt {a b : ℝ} (ha : 0 < a) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') (x x' : Icc a b) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (olgG L H' V' x x')
      ((V' (x'.1 * olgZetaInv L H' y) + x'.1 * olgZetaInv L H' y *
          V'' (x'.1 * olgZetaInv L H' y)) *
        (x'.1 * (H' (olgZetaInv L H' y) + olgZetaInv L H' y * H'' (olgZetaInv L H' y))⁻¹)) y := by
  have hz : 0 < x'.1 * olgZetaInv L H' y := mul_pos (ha.trans_le x'.2.1) (hH.zetaInv_pos hy)
  exact (hV.phi_hasDerivAt hz).comp y ((hH.zetaInv_hasDerivAt hy).const_mul x'.1)

/-- **Step 5 of the proof of Proposition 2.** Under the repaired Assumption 17.2, the elasticity
bound (4) holds: `|y G₃/G| = |x'ζ⁻¹ φ'/φ| · |y (ζ⁻¹)'/ζ⁻¹| ≤ β · 1` for `y > 0`. -/
theorem olgG_elasticity_le {a b : ℝ} (ha : 0 < a) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {β : ℝ} (h2 : Assumption17_2R β V' V'') (x x' : Icc a b)
    {y : ℝ} (hy : 0 < y) :
    |y * ((V' (x'.1 * olgZetaInv L H' y) + x'.1 * olgZetaInv L H' y *
          V'' (x'.1 * olgZetaInv L H' y)) *
        (x'.1 * (H' (olgZetaInv L H' y) + olgZetaInv L H' y * H'' (olgZetaInv L H' y))⁻¹)) /
      olgG L H' V' x x' y| ≤ β := by
  set m := olgZetaInv L H' y with hmdef
  have hm : m ∈ Ioo 0 L := ⟨hH.zetaInv_pos hy, (hH.zetaInv_mem hy.le).2⟩
  have hx' : 0 < x'.1 := ha.trans_le x'.2.1
  set z := x'.1 * m with hzdef
  have hz : 0 < z := mul_pos hx' hm.1
  have hVz := hV.V'_pos hz
  have hH'm := hH.H'_pos hm
  have hH''m := hH.H''_nonneg hm
  have hζ' := hH.zeta_deriv_pos hm
  have hyz : y = m * H' m := (hH.zeta_zetaInv hy.le).symm
  have e : y * ((V' z + z * V'' z) * (x'.1 * (H' m + m * H'' m)⁻¹)) / olgG L H' V' x x' y =
      (H' m / (H' m + m * H'' m)) * (1 - -(z * V'' z) / V' z) := by
    simp only [olgG, olgPhi]
    rw [← hmdef, ← hzdef, hyz]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (div_pos hH'm hζ')]
  have hle1 : H' m / (H' m + m * H'' m) ≤ 1 :=
    (div_le_one hζ').2 (le_add_of_nonneg_right (mul_nonneg hm.1.le hH''m))
  have hr : |1 - -(z * V'' z) / V' z| ≤ β := by
    rw [abs_le]
    constructor <;> linarith [h2.lower z hz, h2.upper z hz]
  calc H' m / (H' m + m * H'' m) * |1 - -(z * V'' z) / V' z|
      ≤ 1 * β := mul_le_mul hle1 hr (abs_nonneg _) zero_le_one
    _ = β := one_mul β

/-- **Proposition 2** (p. 513), under the repaired assumptions (see
`assumption17_2_counterexample`, `assumption17_2R_inconsistent`). Let `X = [a, b]`,
`0 < a ≤ b`, `π` a Feller transition function, `H` as in Assumption 17.1, `V` as in the
repaired Assumption 17.1 (`Assumption17_1VR`) and the repaired Assumption 17.2. Then there is
exactly one bounded continuous strictly positive `f* : X → ℝ₊₊` with
`f*(x) = ∫ φ[x' ζ⁻¹(f*(x'))] π(x, dx')` (6).

The proof applies Lemma 17.2 on `D = [ζ(l), ∞)`. The book's `ε_K` (any `K > 1/C`) is replaced
by `ζ(l)` for `0 < l ≤ l₀`, where `H'(l₀) < C = a V'(bL)`; since `ζ(l) → 0` as `l → 0`, every
strictly positive continuous solution (whose minimum on compact `X` is positive) lies in some
such `D`, where the fixed point is unique. -/
theorem proposition_2 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') {β : ℝ} (h2 : Assumption17_2R β V' V'')
    (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ] (hκ : IsFellerKernel κ) :
    ∃! f : Icc a b →ᵇ ℝ, (∀ x, 0 < f x) ∧
      ∀ x, f x = ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' (f x')) ∂κ x := by
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 < a * V' (b * L) := mul_pos ha (hV.V'_pos (mul_pos hb hH.L_pos))
  obtain ⟨l₀, hl₀, hl₀C⟩ := hH.exists_H'_lt hC
  have hfix : ∀ l ∈ Ioc 0 l₀, ∃! f : Icc a b →ᵇ ℝ, (∀ x, f x ∈ Ici (olgZeta H' l)) ∧
      ∀ x, f x = olgOpT (olgG L H' V') κ f x := fun l hl => by
    have hzl := hH.zeta_pos ⟨hl.1, hl.2.trans_lt hl₀.2⟩
    exact lemma_17_2_fixedPoint (olgG_hyp ha hab hH hV hl₀ hl₀C hl hκ) isClosed_Ici
      nonempty_Ici (fun y hy => hzl.trans_le hy) h2.β_nonneg h2.β_lt_one
      (fun x x' y hy => (olgG_hasDerivAt ha hH hV x x' (hzl.trans_le hy)).hasDerivWithinAt)
      (fun x x' y hy => olgG_elasticity_le ha hH hV h2 x x' (hzl.trans_le hy))
  obtain ⟨f₀, ⟨hf₀D, hf₀fix⟩, -⟩ := hfix l₀ ⟨hl₀.1, le_rfl⟩
  have hz0 := hH.zeta_pos hl₀
  refine ⟨f₀, ⟨fun x => hz0.trans_le (hf₀D x), hf₀fix⟩, ?_⟩
  rintro f ⟨hfpos, hffix⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨a, le_rfl, hab⟩ : Icc a b), mem_univ _⟩ f.continuous.continuousOn
  set l := min l₀ (olgZetaInv L H' (f m))
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hl₀.1 (hH.zetaInv_pos (hfpos m)), min_le_left _ _⟩
  have hlL : l ∈ Ico 0 L := ⟨hl.1.le, hl.2.trans_lt hl₀.2⟩
  have hzl : olgZeta H' l ≤ f m :=
    calc olgZeta H' l ≤ olgZeta H' (olgZetaInv L H' (f m)) :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
  have hzl0 : olgZeta H' l ≤ olgZeta H' l₀ :=
    hH.zeta_strictMonoOn.monotoneOn hlL (Ioo_subset_Ico_self hl₀) (min_le_left _ _)
  obtain ⟨g, -, hg⟩ := hfix l hl
  have e1 := hg f ⟨fun x => hzl.trans (isMinOn_iff.1 hm x (mem_univ x)), hffix⟩
  have e2 := hg f₀ ⟨fun x => hzl0.trans (hf₀D x), hf₀fix⟩
  rw [e1, e2]

/-- **Correction (Proposition 2: the zero fixed point).** `f ≡ 0` also satisfies (6), since
`ζ⁻¹(0) = 0` and `φ(0) = 0`; this is why uniqueness must be stated among strictly positive
`f` (the book's `F` excludes it through `D = [ε_K, ∞)`). -/
theorem proposition_2_zero_fixedPoint (hH : Assumption17_1H L H H' H'') {a b : ℝ}
    (κ : Kernel (Icc a b) (Icc a b)) (x : Icc a b) :
    (0 : Icc a b →ᵇ ℝ) x =
      ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' ((0 : Icc a b →ᵇ ℝ) x')) ∂κ x := by
  simp [hH.zetaInv_zero, olgPhi]

/-- **Correction (Proposition 2), continued.** Among nonnegative bounded continuous `f`, the
solution of (6) is *not* unique: both `0` and the strictly positive `f*` solve it. -/
theorem proposition_2_nonneg_counterexample {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hκ : IsFellerKernel κ) :
    ¬ ∃! f : Icc a b →ᵇ ℝ, (∀ x, 0 ≤ f x) ∧
      ∀ x, f x = ∫ x', olgPhi V' (x'.1 * olgZetaInv L H' (f x')) ∂κ x := by
  rintro ⟨g, -, hg⟩
  obtain ⟨f, ⟨hfpos, hffix⟩, -⟩ := proposition_2 ha hab hH hV h2 κ hκ
  have e1 := hg f ⟨fun x => (hfpos x).le, hffix⟩
  have e2 := hg 0 ⟨fun _ => le_rfl, proposition_2_zero_fixedPoint hH κ⟩
  have := hfpos ⟨a, le_rfl, hab⟩
  rw [e1, ← e2] at this
  simp at this

/-! ### The NOTE on `ε_k` (step 6 of the proof of Proposition 2) -/

/-- The book's `ε_k`: for every `k > 0` the equation `ζ⁻¹(ε) = k ε` has a solution `ε > 0`. -/
theorem epsK_exists (hH : Assumption17_1H L H H' H'') {k : ℝ} (hk : 0 < k) :
    ∃ ε > 0, olgZetaInv L H' ε = k * ε := by
  obtain ⟨l₁, hl₁, hl₁k⟩ := hH.exists_H'_lt (inv_pos.2 hk)
  set ε₁ := olgZeta H' l₁
  have hε₁ := hH.zeta_pos hl₁
  have h1 : olgZetaInv L H' ε₁ = l₁ := hH.zetaInv_zeta (Ioo_subset_Ico_self hl₁)
  have hkε₁ : k * ε₁ < l₁ := by
    have := mul_lt_mul_of_pos_left hl₁k hk
    rw [mul_inv_cancel₀ hk.ne'] at this
    simp only [ε₁, olgZeta]
    nlinarith [hl₁.1]
  have hLk : ε₁ ≤ L / k := by
    rw [le_div_iff₀ hk, mul_comm]
    linarith [hl₁.2]
  have hcont : ContinuousOn (fun e => olgZetaInv L H' e - k * e) (Icc ε₁ (L / k)) :=
    (hH.zetaInv_continuousOn.mono fun e he => mem_Ici.2 (hε₁.le.trans he.1)).sub
      (continuousOn_const.mul continuousOn_id)
  have hA : 0 < olgZetaInv L H' ε₁ - k * ε₁ := by rw [h1]; linarith
  have hB : olgZetaInv L H' (L / k) - k * (L / k) < 0 := by
    rw [mul_div_cancel₀ _ hk.ne']
    linarith [(hH.zetaInv_mem (div_pos hH.L_pos hk).le).2]
  obtain ⟨e, he, he0⟩ := intermediate_value_Icc' hLk hcont ⟨hB.le, hA.le⟩
  exact ⟨e, hε₁.trans_le he.1, by linarith⟩

/-- **The NOTE's gap in step 6 of Proposition 2, closed.** Any positive `ε_k` with
`ζ⁻¹(ε_k) = (k + 1) ε_k` satisfies `ε_k < L/(k + 1)`, so `ε_k → 0`. (The proof of
`proposition_2` uses the equivalent `ζ(l) → 0` directly.) -/
theorem epsK_tendsto_zero (hH : Assumption17_1H L H H' H'') {ε : ℕ → ℝ}
    (hpos : ∀ k, 0 < ε k) (heq : ∀ k, olgZetaInv L H' (ε k) = (k + 1) * ε k) :
    Tendsto ε atTop (𝓝 0) := by
  have hbound : ∀ k : ℕ, ε k ≤ L / ((k : ℝ) + 1) := fun k => by
    rw [le_div_iff₀ (by positivity), mul_comm, ← heq k]
    exact (hH.zetaInv_mem (hpos k).le).2.le
  have hlim : Tendsto (fun k : ℕ => L / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat L).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun k => ?_
    simp [Nat.cast_add, Nat.cast_one]
  exact squeeze_zero (fun k => (hpos k).le) hbound hlim

end StokeyLucasPrescott.FixedPointArguments

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

namespace StokeyLucasPrescott.FixedPointArguments

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

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Schauder's theorem for spaces of bounded continuous functions (SLP Theorem 17.4)

SLP §17.4, p. 520. `X` is a bounded subset of `ℝˡ` and `C(X)` the space of bounded continuous
real functions on `X` with the sup norm (`X →ᵇ ℝ`). A family `G ⊆ C(X)` is *equicontinuous* in
the book's sense (p. 520) if for every `ε > 0` there is `δ > 0` with `|g x − g y| < ε` whenever
`|x − y| < δ`, for all `g ∈ G` (uniform equicontinuity).

* `totallyBounded_of_equicontinuous` (Arzelà–Ascoli, the half needed): on a totally bounded
  metric space `X`, a bounded equicontinuous family in `X →ᵇ ℝ` is totally bounded. Proof: for a
  finite `δ`-net `P ⊆ X`, the evaluation map at `P` sends the family to a bounded, hence totally
  bounded, subset of `ℝ^P`; two members whose values at `P` are `ε/4`-close are `3ε/4`-close
  everywhere.
* `theorem_17_4` (**Theorem 17.4**, Schauder): for `F ⊆ C(X)` nonempty, closed, bounded and convex
  and `T : F → F` continuous with `T(F)` equicontinuous, `T` has a fixed point. The image `T(F)` is
  totally bounded by the lemma above, so relatively compact in the Banach space `C(X)`, and
  `schauder_closed_subtype` applies.

The book's statement is correct as given: `X` need not be closed or compact, because boundedness of
`X ⊆ ℝˡ` already makes `X` totally bounded, which is all the argument uses. (Boundedness of `F` is
used only to bound `T(F)`.)
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Metric Set Filter Topology BoundedContinuousFunction

/-- **Arzelà–Ascoli (total boundedness).** On a totally bounded pseudometric space `X`, a bounded
family `S` of bounded continuous real functions that is equicontinuous in the sense of SLP p. 520
(a single `δ` for each `ε`, uniformly over `S` and over `X`) is totally bounded in the sup norm. -/
theorem totallyBounded_of_equicontinuous {X : Type*} [PseudoMetricSpace X]
    (hX : TotallyBounded (univ : Set X)) {S : Set (X →ᵇ ℝ)} (hS : Bornology.IsBounded S)
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ g ∈ S, |g x - g y| < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set ε' := ε / 4 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδε⟩ := heq ε' hε'0
  obtain ⟨P, -, hPfin, hPcov⟩ := finite_approx_of_totallyBounded hX δ hδ
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hS
  have _ : Fintype P := hPfin.fintype
  set Φ : (X →ᵇ ℝ) → (P → ℝ) := fun g p => g p with hΦ
  have hΦS : TotallyBounded (Φ '' S) := by
    have hb : Bornology.IsBounded (Φ '' S) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨max R 0, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun p => ?_
      exact (g.norm_coe_le_norm p).trans ((hR g hg).trans (le_max_left _ _))
    exact hb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨u, huS, hufin, hucov⟩ := finite_approx_of_totallyBounded hΦS ε' hε'0
  have hchoice : ∀ y, ∃ g : X →ᵇ ℝ, y ∈ Φ '' S → g ∈ S ∧ Φ g = y := by
    intro y
    by_cases hy : y ∈ Φ '' S
    · obtain ⟨g, hg, rfl⟩ := hy
      exact ⟨g, fun _ => ⟨hg, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose G hG using hchoice
  refine ⟨G '' u, hufin.image G, fun g hg => ?_⟩
  obtain ⟨y, hyu, hgy⟩ := mem_iUnion₂.1 (hucov ⟨g, hg, rfl⟩)
  obtain ⟨hGS, hGy⟩ := hG y (huS hyu)
  refine mem_iUnion₂.2 ⟨G y, mem_image_of_mem G hyu, ?_⟩
  rw [mem_ball]
  have hpt : ∀ p : P, |g p - G y p| < ε' := by
    intro p
    have h1 : dist (Φ g) (Φ (G y)) < ε' := by
      rw [hGy]
      exact hgy
    have h2 := (dist_le_pi_dist (Φ g) (Φ (G y)) p).trans_lt h1
    rwa [Real.dist_eq] at h2
  have hle : dist g (G y) ≤ 3 * ε' := by
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
    obtain ⟨p, hpP, hxp⟩ := mem_iUnion₂.1 (hPcov (mem_univ x))
    have h1 := hδε x p hxp g hg
    have h2 := hδε x p hxp (G y) hGS
    have h3 := hpt ⟨p, hpP⟩
    rw [Real.dist_eq]
    calc |g x - G y x| ≤ |g x - g p| + |g p - G y p| + |G y p - G y x| := by
          have := abs_sub_le (g x) (g p) (G y x)
          have := abs_sub_le (g p) (G y p) (G y x)
          linarith
      _ ≤ 3 * ε' := by
          rw [abs_sub_comm (G y p)]
          linarith
  linarith

/-- **Theorem 17.4 (Schauder fixed-point theorem)**, p. 520. Let `X` be a bounded subset of `ℝˡ`
and `C(X) = X →ᵇ ℝ` with the sup norm. Let `F ⊆ C(X)` be nonempty, closed, bounded and convex,
and `T : F → F` continuous with `T(F)` equicontinuous. Then `T` has a fixed point in `F`. -/
theorem theorem_17_4 {l : ℕ} {X : Set (EuclideanSpace ℝ (Fin l))} (hX : Bornology.IsBounded X)
    {F : Set (X →ᵇ ℝ)} (hne : F.Nonempty) (hcl : IsClosed F) (hbdd : Bornology.IsBounded F)
    (hconv : Convex ℝ F) {T : F → F} (hT : Continuous T)
    (hequi : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ →
      ∀ f : F, |(T f : X →ᵇ ℝ) x - (T f : X →ᵇ ℝ) y| < ε) :
    ∃ f : F, T f = f := by
  have hXtb : TotallyBounded (univ : Set X) := by
    have h := totallyBounded_preimage
      (isUniformEmbedding_subtype_val (p := fun x => x ∈ X)).isUniformInducing
      (hX.isCompact_closure.totallyBounded.subset subset_closure)
    rwa [Subtype.coe_preimage_self] at h
  set S : Set (X →ᵇ ℝ) := range fun f => (T f : X →ᵇ ℝ) with hS
  have hSF : S ⊆ F := by
    rintro _ ⟨f, rfl⟩
    exact (T f).2
  have heqS : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ g ∈ S, |g x - g y| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi ε hε
    refine ⟨δ, hδ, fun x y hxy => ?_⟩
    rintro _ ⟨f, rfl⟩
    exact h x y hxy f
  have htb := totallyBounded_of_equicontinuous hXtb (hbdd.subset hSF) heqS
  exact schauder_closed_subtype hcl hconv hne hT
    (htb.closure.isCompact_of_isClosed isClosed_closure)

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 17.5: Peano-type existence via Schauder

SLP §17.4, Exercise 17.5, p. 520: the initial-value problem `x′(t) = f(x(t))`, `x(0) = c`.

* `fpOdeOp` the integral operator `(Tx)(t) = c + ∫₀ᵗ f(x(s)) ds` on `C[0, t₀]`, and
  `fp_ode_exists`: if `|f| ≤ M` on `[c − δ, c + δ]` and `t₀ M ≤ δ`, Schauder's theorem on the
  closed `δ`-ball about the constant `c` in `C[0, t₀]` gives a solution on `[0, t₀]` (the manual's
  argument; total boundedness of `T(D)` is `totallyBounded_of_equicontinuous`, the half of
  Arzelà–Ascoli behind `theorem_17_4`).
* `ex_17_5a_local` (**Exercise 17.5a, corrected**): for continuous `f` there is `t₀ ∈ (0, 1]` and
  a solution on `[0, t₀]`.
* `ex_17_5a_of_bounded` (**Exercise 17.5a, corrected**): for continuous bounded `f` there is a
  solution on all of `[0, 1]`.
* `ex_17_5a_counterexample`, `ex_17_5a_false`: the book's claim is false.
* `ex_17_5a_blowup_solution`: `x(t) = 2/(1 − 2t)` is the local solution for `f(x) = x²`, `c = 2`.
* `ex_17_5b` (**Exercise 17.5b**): `x ≡ 0` and `x(t) = t²/4` both solve `x′ = √x`, `x(0) = 0`
  on `[0, 1]`; `ex_17_5b_family`: so does `((t − s)⁺)²/4` for every `s ∈ [0, 1]`.
* `ex_17_5b_manual_counterexample`: the manual's `t²/2` is not a solution.
* `ex_17_5c` (**Exercise 17.5c**): `√·` is not Lipschitz on `ℝ₊`, which is the hypothesis of
  Exercise 3.10 that the equation violates.

**Corrections.**
* Exercise 17.5a is false as stated: continuity of `f` gives only local existence.
  `ex_17_5a_counterexample`: for `f(x) = x²`, `c = 2` there is no solution on `[0, 1]`, even with
  one-sided derivatives at the end points (`t + 1/x(t)` would be constant, forcing
  `1/x(1/2) = 0`). Corrected statements: `ex_17_5a_local` (the manual's local result) and
  `ex_17_5a_of_bounded`.
* The manual's ball `D` must be centred at the constant function `c`, not at `0`
  (`fp_ode_exists` uses the ball about `c`).
* The manual's second solution to 17.5b, `t²/2`, is wrong (`ex_17_5b_manual_counterexample`); the
  correct one is `t²/4`, and there are infinitely many (`ex_17_5b_family`).
* In 17.5c the book's "Exercise 3.8" should be "Exercise 3.10" (the Lipschitz ODE exercise,
  p. 53).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Set Filter Topology Metric BoundedContinuousFunction

/-! ### The integral operator and local existence -/

/-- The integral operator of Exercise 17.5, `(Tx)(t) = c + ∫₀ᵗ f(x(s)) ds`, on `C[0, t₀]`. The
function `x` on `[0, t₀]` is extended to `ℝ` by constants (`IccExtend`). -/
noncomputable def fpOdeOp (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) {t₀ : ℝ} (h0 : 0 ≤ t₀)
    (x : Icc (0 : ℝ) t₀ →ᵇ ℝ) : Icc (0 : ℝ) t₀ →ᵇ ℝ :=
  mkOfCompact
    ⟨fun t => c + ∫ s in (0 : ℝ)..(t : ℝ), f (IccExtend h0 x s),
      continuous_const.add <| (continuous_iff_continuousAt.2 fun u =>
        ((hf.comp (Continuous.Icc_extend' (h := h0) x.continuous)).integral_hasStrictDerivAt
          0 u).hasDerivAt.continuousAt).comp continuous_subtype_val⟩

/-- **Existence on `[0, t₀]` via Schauder** (manual, Exercise 17.5a). If `f` is continuous,
`|f| ≤ M` on `[c − δ, c + δ]` and `t₀ M ≤ δ`, then `x′ = f(x)`, `x(0) = c` has a solution on
`[0, t₀]`. -/
theorem fp_ode_exists {f : ℝ → ℝ} (hf : Continuous f) {c δ M t₀ : ℝ} (ht₀ : 0 < t₀)
    (hδ : 0 ≤ δ) (hM : ∀ z, |z - c| ≤ δ → |f z| ≤ M) (htM : t₀ * M ≤ δ) :
    ∃ x : ℝ → ℝ, x 0 = c ∧ ∀ t ∈ Icc 0 t₀, HasDerivAt x (f (x t)) t := by
  have h0 : (0 : ℝ) ≤ t₀ := ht₀.le
  set D : Set (Icc (0 : ℝ) t₀ →ᵇ ℝ) := closedBall (const _ c) δ with hD
  set T := fpOdeOp f hf c h0 with hT
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (by simpa using hδ))
  have hval : ∀ x ∈ D, ∀ s : ℝ, |IccExtend h0 x s - c| ≤ δ := by
    intro x hx s
    rw [IccExtend_apply]
    have h1 := dist_coe_le_dist (f := x) (g := const _ c) (projIcc 0 t₀ h0 s)
    rw [Real.dist_eq, const_apply] at h1
    exact h1.trans (mem_closedBall.1 hx)
  have hg : ∀ x : Icc (0 : ℝ) t₀ →ᵇ ℝ, Continuous fun s => f (IccExtend h0 x s) := fun x =>
    hf.comp (Continuous.Icc_extend' (h := h0) x.continuous)
  have hTapp : ∀ (x : Icc (0 : ℝ) t₀ →ᵇ ℝ) (t : Icc (0 : ℝ) t₀),
      T x t = c + ∫ s in (0 : ℝ)..(t : ℝ), f (IccExtend h0 x s) := fun _ _ => rfl
  have hfb : ∀ x ∈ D, ∀ s : ℝ, ‖f (IccExtend h0 x s)‖ ≤ M := fun x hx s => by
    rw [Real.norm_eq_abs]
    exact hM _ (hval x hx s)
  -- `T(D) ⊆ D`
  have hmaps : MapsTo T D D := by
    intro x hx
    rw [mem_closedBall]
    refine (BoundedContinuousFunction.dist_le hδ).2 fun t => ?_
    rw [hTapp, const_apply, Real.dist_eq, add_sub_cancel_left]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (C := M) (f := fun s => f (IccExtend h0 x s)) fun s _ => hfb x hx s
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.2.1] at this
    calc _ ≤ M * t := this
      _ ≤ M * t₀ := mul_le_mul_of_nonneg_left t.2.2 hM0
      _ ≤ δ := by linarith
  -- `T(D)` is equicontinuous
  have hequi : ∀ ε > 0, ∃ η > 0, ∀ t t' : Icc (0 : ℝ) t₀, dist t t' < η →
      ∀ g ∈ T '' D, |g t - g t'| < ε := by
    intro ε hε
    refine ⟨ε / (M + 1), by positivity, fun t t' htt' => ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hTapp, hTapp, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      ((hg x).intervalIntegrable _ _) ((hg x).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (t' : ℝ)) (b := (t : ℝ))
      (C := M) (f := fun s => f (IccExtend h0 x s)) fun s _ => hfb x hx s
    rw [Real.norm_eq_abs] at this
    have hd : |(t : ℝ) - t'| < ε / (M + 1) := by rwa [Subtype.dist_eq, Real.dist_eq] at htt'
    have hlt : M * (ε / (M + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ M * |(t : ℝ) - t'| := this
      _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hd.le hM0
      _ < ε := hlt
  -- `T` is continuous on `D`
  have hcont : ContinuousOn T D := by
    have huc := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := c - δ) (b := c + δ)).uniformContinuousOn_of_continuous
        hf.continuousOn)
    refine Metric.continuousOn_iff.2 fun y hy ε hε => ?_
    obtain ⟨η, hη, hηf⟩ := huc (ε / (2 * (t₀ + 1))) (by positivity)
    refine ⟨η, hη, fun x hx hxy => ?_⟩
    have hpt : ∀ s : ℝ,
        ‖f (IccExtend h0 x s) - f (IccExtend h0 y s)‖ ≤ ε / (2 * (t₀ + 1)) := by
      intro s
      have hxs := abs_le.1 (hval x hx s)
      have hys := abs_le.1 (hval y hy s)
      have hmx : IccExtend h0 x s ∈ Icc (c - δ) (c + δ) := ⟨by linarith, by linarith⟩
      have hmy : IccExtend h0 y s ∈ Icc (c - δ) (c + δ) := ⟨by linarith, by linarith⟩
      have hd : dist (IccExtend h0 x s) (IccExtend h0 y s) < η := by
        rw [IccExtend_apply, IccExtend_apply]
        exact (dist_coe_le_dist _).trans_lt hxy
      have := hηf _ hmx _ hmy hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
    have hle : dist (T x) (T y) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t => ?_
      rw [hTapp, hTapp, Real.dist_eq, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        ((hg x).intervalIntegrable _ _) ((hg y).intervalIntegrable _ _)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
        (C := ε / (2 * (t₀ + 1)))
        (f := fun s => f (IccExtend h0 x s) - f (IccExtend h0 y s)) fun s _ => hpt s
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.2.1] at this
      calc _ ≤ ε / (2 * (t₀ + 1)) * t := this
        _ ≤ ε / (2 * (t₀ + 1)) * (t₀ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [t.2.2]) (by positivity)
        _ = ε / 2 := by field_simp
    linarith
  -- Schauder
  have hXtb : TotallyBounded (univ : Set (Icc (0 : ℝ) t₀)) :=
    (isCompact_iff_isCompact_univ.1 isCompact_Icc).totallyBounded
  have hbdd : Bornology.IsBounded (T '' D) := isBounded_closedBall.subset hmaps.image_subset
  have htb := totallyBounded_of_equicontinuous hXtb hbdd hequi
  obtain ⟨x, -, hTx⟩ := schauder_closed isClosed_closedBall (convex_closedBall _ _)
    (nonempty_closedBall.2 hδ) hcont hmaps (htb.closure.isCompact_of_isClosed isClosed_closure)
  refine ⟨fun u => c + ∫ s in (0 : ℝ)..u, f (IccExtend h0 x s), by simp, fun t ht => ?_⟩
  have hd := ((hg x).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c
  have hxt : c + ∫ s in (0 : ℝ)..t, f (IccExtend h0 x s) = IccExtend h0 x t := by
    have := congrArg (fun g : Icc (0 : ℝ) t₀ →ᵇ ℝ => g ⟨t, ht⟩) hTx
    rw [hTapp] at this
    rw [IccExtend_of_mem _ _ ht, ← this]
  simp only
  rw [hxt]
  exact hd

/-- **Exercise 17.5a, corrected: local existence** (the manual's result). If `f` is continuous,
there is `t₀ ∈ (0, 1]` such that `x′ = f(x)`, `x(0) = c` has a solution on `[0, t₀]`. -/
theorem ex_17_5a_local {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    ∃ t₀ ∈ Ioc (0 : ℝ) 1, ∃ x : ℝ → ℝ, x 0 = c ∧ ∀ t ∈ Icc 0 t₀, HasDerivAt x (f (x t)) t := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hf c 1 one_pos
  set M := |f c| + 1 with hMdef
  have hM0 : 0 < M := by positivity
  have hM : ∀ z, |z - c| ≤ δ / 2 → |f z| ≤ M := fun z hz => by
    have h1 := hδf z (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (f z) (f c)
    linarith
  have ht₀ : 0 < min 1 (δ / 2 / M) := lt_min one_pos (by positivity)
  refine ⟨min 1 (δ / 2 / M), ⟨ht₀, min_le_left _ _⟩,
    fp_ode_exists hf ht₀ (by positivity) hM ?_⟩
  calc min 1 (δ / 2 / M) * M ≤ δ / 2 / M * M :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hM0.le
    _ = δ / 2 := by field_simp

/-- **Exercise 17.5a, corrected: bounded `f`.** If `f` is continuous and bounded, then
`x′ = f(x)`, `x(0) = c` has a solution on all of `[0, 1]`. -/
theorem ex_17_5a_of_bounded {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (c : ℝ) : ∃ x : ℝ → ℝ, x 0 = c ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (f (x t)) t :=
  fp_ode_exists hf one_pos ((abs_nonneg _).trans (hM 0)) (fun z _ => hM z) (by rw [one_mul])

/-! ### The counterexample to Exercise 17.5a -/

/-- **Counterexample to Exercise 17.5a.** For `f(x) = x²` and `c = 2` there is no solution of
`x′ = x²`, `x(0) = 2` on `[0, 1]`, even allowing one-sided derivatives at the end points. -/
theorem ex_17_5a_counterexample :
    ¬ ∃ x : ℝ → ℝ, x 0 = 2 ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (x t ^ 2) (Icc 0 1) t := by
  rintro ⟨x, hx0, hx⟩
  have hcont : ContinuousOn x (Icc 0 1) := fun t ht => (hx t ht).continuousWithinAt
  have hmono : MonotoneOn x (Icc 0 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
      (fun t ht => (hx t (interior_subset ht)).mono interior_subset) fun t _ => sq_nonneg _
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 2 ≤ x t := fun t ht => by
    rw [← hx0]
    exact hmono (left_mem_Icc.2 zero_le_one) ht ht.1
  -- `g(t) = t + 1/x(t)` has derivative `0`
  set g : ℝ → ℝ := fun t => t + (x t)⁻¹ with hg
  have hgd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g 0 (Icc 0 1) t := by
    intro t ht
    have hxt : x t ≠ 0 := by linarith [hpos t ht]
    have := (hasDerivWithinAt_id t (Icc 0 1)).add ((hx t ht).inv hxt)
    have h0 : (1 : ℝ) + -(x t ^ 2) / x t ^ 2 = 0 := by field_simp; ring
    rw [h0] at this
    exact this
  have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc 0 1 := Icc_subset_Icc_right (by norm_num)
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := 1 / 2)
    (fun t ht => (hgd t (hsub ht)).continuousWithinAt.mono hsub) fun t ht =>
      (hgd t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, by linarith [ht.2]⟩)
  have h := hconst (1 / 2) (right_mem_Icc.2 (by norm_num))
  simp only [hg, hx0] at h
  have h2 := hpos (1 / 2) (hsub (right_mem_Icc.2 (by norm_num)))
  have h3 : (x (1 / 2))⁻¹ = 0 := by linarith
  rw [inv_eq_zero] at h3
  linarith

/-- **Exercise 17.5a is false**: not every continuous `f` gives a solution on `[0, 1]`. -/
theorem ex_17_5a_false :
    ¬ ∀ f : ℝ → ℝ, Continuous f → ∀ c : ℝ, ∃ x : ℝ → ℝ, x 0 = c ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t := fun h =>
  ex_17_5a_counterexample (h (fun y => y ^ 2) (continuous_pow 2) 2)

/-- The local solution of `x′ = x²`, `x(0) = 2` is `x(t) = 2/(1 − 2t)`, which blows up as
`t ↑ 1/2`. -/
theorem ex_17_5a_blowup_solution {t : ℝ} (ht : t < 1 / 2) :
    HasDerivAt (fun t : ℝ => 2 / (1 - 2 * t)) ((2 / (1 - 2 * t)) ^ 2) t := by
  have hne : 1 - 2 * t ≠ 0 := by linarith
  have := (hasDerivAt_const t (2 : ℝ)).div (((hasDerivAt_id' t).const_mul 2).const_sub 1) hne
  convert this using 1
  field_simp
  ring

/-! ### Exercise 17.5b and 17.5c -/

/-- **Exercise 17.5b.** `x ≡ 0` and `x(t) = t²/4` are two different solutions of `x′ = √x`,
`x(0) = 0` on `[0, 1]`. -/
theorem ex_17_5b :
    ∃ x₁ x₂ : ℝ → ℝ, x₁ 0 = 0 ∧ x₂ 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x₁ (√(x₁ t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x₂ (√(x₂ t)) t) ∧ x₁ 1 ≠ x₂ 1 := by
  refine ⟨fun _ => 0, fun t => t ^ 2 / 4, rfl, by norm_num, fun t _ => ?_, fun t ht => ?_,
    by norm_num⟩
  · simpa using hasDerivAt_const t (0 : ℝ)
  · have h1 : √(t ^ 2 / 4) = t / 2 := by
      rw [show t ^ 2 / 4 = (t / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by linarith [ht.1])
    rw [h1]
    have := (hasDerivAt_pow 2 t).div_const 4
    convert this using 1
    norm_num
    ring

/-- **Exercise 17.5b, all solutions of this shape.** For every `s ∈ [0, 1]`,
`xₛ(t) = ((t − s)⁺)²/4` solves `x′ = √x`, `x(0) = 0` (on all of `ℝ`). -/
theorem ex_17_5b_family {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun t : ℝ => max (t - s) 0 ^ 2 / 4) 0 = 0 ∧
      ∀ t : ℝ, HasDerivAt (fun t : ℝ => max (t - s) 0 ^ 2 / 4) (√(max (t - s) 0 ^ 2 / 4)) t := by
  refine ⟨by simp [hs.1], fun t => ?_⟩
  have hsq : √(max (t - s) 0 ^ 2 / 4) = max (t - s) 0 / 2 := by
    rw [show max (t - s) 0 ^ 2 / 4 = (max (t - s) 0 / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have hq : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t - s) ^ 2 / 4) ((u - s) / 2) u := fun u => by
    have := (((hasDerivAt_id' u).sub_const s).pow 2).div_const 4
    convert this using 1
    norm_num
    ring
  rcases lt_trichotomy t s with h | h | h
  · have hev : (fun t : ℝ => max (t - s) 0 ^ 2 / 4) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with u hu
      simp [max_eq_right (by linarith [mem_Iio.1 hu] : u - s ≤ 0)]
    rw [max_eq_right (by linarith : t - s ≤ 0), zero_div]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    rw [sub_self, max_self, zero_div]
    have h1 : HasDerivWithinAt (fun u : ℝ => max (u - t) 0 ^ 2 / 4) 0 (Ici t) t := by
      have := (hq t).hasDerivWithinAt (s := Ici t)
      rw [sub_self, zero_div] at this
      refine this.congr (fun u hu => ?_) (by simp)
      simp [max_eq_left (by linarith [mem_Ici.1 hu] : 0 ≤ u - t)]
    have h2 : HasDerivWithinAt (fun u : ℝ => max (u - t) 0 ^ 2 / 4) 0 (Iic t) t := by
      refine (hasDerivWithinAt_const t (Iic t) (0 : ℝ)).congr (fun u hu => ?_) (by simp)
      simp [max_eq_right (by linarith [mem_Iic.1 hu] : u - t ≤ 0)]
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hev : (fun t : ℝ => max (t - s) 0 ^ 2 / 4) =ᶠ[𝓝 t] fun t => (t - s) ^ 2 / 4 := by
      filter_upwards [Ioi_mem_nhds h] with u hu
      simp [max_eq_left (by linarith [mem_Ioi.1 hu] : 0 ≤ u - s)]
    rw [max_eq_left (by linarith : 0 ≤ t - s)]
    exact (hq t).congr_of_eventuallyEq hev

/-- **The manual's answer to Exercise 17.5b is wrong**: `x(t) = t²/2` does not solve `x′ = √x` on
`[0, 1]` (at `t = 1`, `x′(1) = 1 ≠ √(1/2)`). -/
theorem ex_17_5b_manual_counterexample :
    ¬ ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => t ^ 2 / 2) (√(t ^ 2 / 2)) (Icc 0 1) t := by
  intro h
  have h1 := h 1 (right_mem_Icc.2 zero_le_one)
  have h2 : HasDerivWithinAt (fun t : ℝ => t ^ 2 / 2) 1 (Icc 0 1) 1 := by
    have := (hasDerivAt_pow 2 (1 : ℝ)).div_const 2
    convert this.hasDerivWithinAt using 1
    norm_num
  have := (uniqueDiffOn_Icc zero_lt_one 1 (right_mem_Icc.2 zero_le_one)).eq_deriv _ h1 h2
  rw [Real.sqrt_eq_one] at this
  norm_num at this

/-- **Exercise 17.5c.** The equation `x′ = √x` violates the Lipschitz condition of Exercise 3.10
(the book says "Exercise 3.8"): there is no `B` with `|√y − √z| ≤ B|y − z|` on `ℝ₊`. -/
theorem ex_17_5c : ¬ ∃ B : ℝ, ∀ y z : ℝ, 0 ≤ y → 0 ≤ z → |√y - √z| ≤ B * |y - z| := by
  rintro ⟨B, hB⟩
  set k := |B| + 1 with hk
  have hk0 : 0 < k := by positivity
  have h := hB ((1 / k) ^ 2) 0 (by positivity) le_rfl
  rw [Real.sqrt_sq (by positivity), Real.sqrt_zero, sub_zero, sub_zero,
    abs_of_pos (by positivity), abs_of_pos (by positivity)] at h
  have h2 : k ≤ B := by
    have h3 : 1 / k * k ^ 2 ≤ B * (1 / k) ^ 2 * k ^ 2 :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have e1 : 1 / k * k ^ 2 = k := by field_simp
    have e2 : B * (1 / k) ^ 2 * k ^ 2 = B := by field_simp
    linarith
  linarith [le_abs_self B]

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Applications of the Schauder fixed-point theorem (SLP §17.4)

SLP §17.4, pp. 519–525. Schauder's theorem itself is `theorem_17_4`
(`FixedPointArguments.SchauderBoundedContinuous`); Exercise 17.5 is in
`FixedPointArguments.SchauderAppODE`. The OLG primitives `FPAssumption17_1`, `fpZeta`, `fpPhi`,
`fpZetaInv` and the bounds `fp_bounds` are from `FixedPointArguments.BrouwerApplication`.

**Total variation** (§11.3). `fpTVNorm μ ν` is `‖μ − ν‖_TV = sup Σᵢ |μ(Aᵢ) − ν(Aᵢ)|` over finite
measurable partitions `{Aᵢ}` (`FPIsFinPartition`). `fp_abs_integral_sub_le`: for measurable `h`
with `|h| ≤ C`, `|∫ h dμ − ∫ h dν| ≤ C ‖μ − ν‖_TV` (proved with the Hahn decomposition).

**Results.**
* `FPAssumption17_3` (**Assumption 17.3**, pp. 520–521): `x ↦ π(x, ·)` is uniformly continuous
  into probability measures with the total-variation norm. `fpAssumption17_3_const`: a constant
  (i.i.d.) kernel satisfies it.
* `fpIntOp` the operator `(Tf)(x) = ∫ G[x, x′, f(x′)] π(x, dx′)` ((1), p. 521).
* `lemma_17_5` (**Lemma 17.5**, p. 521): `T(F)` is bounded and equicontinuous.
* `ex_17_6` (**Exercise 17.6**, p. 522): if `G` is also uniformly continuous in its third
  argument (uniformly over `(x, x′)`), `T` is (uniformly) continuous in the sup norm.
* `fp_exists_fixedPoint_intOp` (the combination described on p. 522 and pp. 524–525): with `D`
  nonempty, closed, bounded and convex and `X` totally bounded (e.g. bounded in `ℝˡ`), `T` maps
  `F` into itself and has a fixed point (Schauder, via `totallyBounded_of_equicontinuous` and
  `schauder_closed`).
* `proposition_4` (**Proposition 4**, p. 522): for `X = [a, b] ⊂ ℝ₊₊`, `π` satisfying
  Assumption 17.3 and Assumption 17.1, there is a continuous `f*` bounded away from zero with
  `f*(x) = ∫ φ[x′ζ⁻¹(f*(x′))] π(x, dx′)`. `proposition_4_zero_fixedPoint`: `f ≡ 0` is also a
  solution.
* `fpLabourOp` the operator of Exercise 17.7, `(Sn)(x) = ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]`.
  `ex_17_7_zero` (`S0 = 0`), `ex_17_7_why_of_f`, `ex_17_7_why_of_n` (the "Why?": `n* = ζ⁻¹ ∘ f*`
  and `f* = ζ ∘ n*`), `ex_17_7` (**Exercise 17.7**, corrected): `S` has a continuous fixed point
  bounded away from `0` (and below `L`).

**Corrections.**
* Exercise 17.7 as stated ("the operator has a fixed point") is trivial: `n ≡ 0` is always a
  fixed point (`ex_17_7_zero`, since `φ(0) = 0 = ζ⁻¹(0)`), so the claim needs no Schauder argument;
  the manual's Schauder set `D ⊆ [0, L)` contains `0` and does not exclude it. The meaningful
  statement is existence of a fixed point bounded away from zero, proved as `ex_17_7` (here
  from Proposition 4 through the correspondence `n* = ζ⁻¹ ∘ f*`, which is also the answer to the
  book's "Why?").
* Proposition 4's proof says `Tf` is continuous because `π` is Feller; Lemma 17.5 (whose
  equicontinuity makes each `Tf` uniformly continuous) gives this directly, which is what we use.
* Exercise 17.6 does not need Assumption 17.3 (only that each `π(x, ·)` is a probability
  measure), and "uniformly continuous in its third argument" is read, as in the manual, as
  uniform over `(x, x′)`.
* Lemma 17.5 uses joint continuity of `G` only to make `x′ ↦ G[x, x′, f(x′)]` measurable, and only
  boundedness of `D`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Set Filter Topology Metric MeasureTheory BoundedContinuousFunction

/-! ### The total-variation norm -/

/-- A finite measurable partition of `X`: finitely many pairwise disjoint measurable sets whose
union is `X`. -/
def FPIsFinPartition {X : Type*} [MeasurableSpace X] (P : Finset (Set X)) : Prop :=
  (∀ A ∈ P, MeasurableSet A) ∧ (P : Set (Set X)).PairwiseDisjoint id ∧ ⋃ A ∈ P, A = univ

/-- The total-variation norm `‖μ − ν‖_TV = sup Σᵢ |μ(Aᵢ) − ν(Aᵢ)|` over finite measurable
partitions `{Aᵢ}` of `X` (§11.3). -/
noncomputable def fpTVNorm {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ℝ :=
  ⨆ P : {P : Finset (Set X) // FPIsFinPartition P}, ∑ A ∈ P.1, |μ.real A - ν.real A|

variable {X : Type*}

/-- `{X}` is a finite measurable partition. -/
theorem fpIsFinPartition_univ [MeasurableSpace X] :
    FPIsFinPartition ({univ} : Finset (Set X)) :=
  ⟨by simp, by simp, by simp⟩

/-- The partition sums are bounded by `μ(X) + ν(X)`. -/
theorem fpTVNorm_bddAbove [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    BddAbove (range fun P : {P : Finset (Set X) // FPIsFinPartition P} =>
      ∑ A ∈ P.1, |μ.real A - ν.real A|) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨⟨P, hm, hd, hu⟩, rfl⟩
  have h1 := measureReal_biUnion_finset (μ := μ) (f := id) hd hm
  have h2 := measureReal_biUnion_finset (μ := ν) (f := id) hd hm
  simp only [id] at h1 h2
  rw [hu] at h1 h2
  calc ∑ A ∈ P, |μ.real A - ν.real A| ≤ ∑ A ∈ P, (μ.real A + ν.real A) :=
        Finset.sum_le_sum fun A _ => abs_sub_le_iff.2
          ⟨by linarith [measureReal_nonneg (μ := ν) (s := A)],
            by linarith [measureReal_nonneg (μ := μ) (s := A)]⟩
    _ = μ.real univ + ν.real univ := by rw [Finset.sum_add_distrib, h1, h2]

/-- `‖μ − ν‖_TV ≥ 0`. -/
theorem fpTVNorm_nonneg [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : 0 ≤ fpTVNorm μ ν :=
  le_ciSup_of_le (fpTVNorm_bddAbove μ ν) ⟨{univ}, fpIsFinPartition_univ⟩
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The two-set partition `{s, sᶜ}` bounds `‖μ − ν‖_TV` from below. -/
theorem fp_le_tvNorm_pair [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| + |μ.real sᶜ - ν.real sᶜ| ≤ fpTVNorm μ ν := by
  classical
  by_cases hss : s = sᶜ
  · have he : ∀ x : X, False := fun x => by
      have h : x ∈ s ↔ x ∈ sᶜ := Iff.of_eq (congrArg (x ∈ ·) hss)
      rw [mem_compl_iff] at h
      exact iff_not_self h
    have : IsEmpty X := ⟨he⟩
    rw [Set.eq_empty_of_isEmpty sᶜ, Set.eq_empty_of_isEmpty s]
    simp only [measureReal_empty, sub_self, abs_zero, add_zero]
    exact fpTVNorm_nonneg μ ν
  · refine le_ciSup_of_le (fpTVNorm_bddAbove μ ν) ⟨{s, sᶜ}, ?_, ?_, ?_⟩ ?_
    · intro A hA
      rcases Finset.mem_insert.1 hA with rfl | hA
      · exact hs
      · rw [Finset.mem_singleton.1 hA]
        exact hs.compl
    · rw [Finset.coe_pair]
      exact pairwise_pair.2 fun _ => ⟨disjoint_compl_right, disjoint_compl_left⟩
    · simp
    · simp only
      rw [Finset.sum_pair hss]

/-- If `ν ≤ μ` are finite measures and `|h| ≤ C`, then
`|∫ h dμ − ∫ h dν| ≤ C (μ(X) − ν(X))`. -/
theorem fp_abs_integral_sub_le_of_le [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hle : ν ≤ μ) {h : X → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ C * (μ.real univ - ν.real univ) := by
  have : IsFiniteMeasure (μ - ν) := isFiniteMeasure_of_le μ Measure.sub_le
  have hρ : μ - ν + ν = μ := Measure.sub_add_cancel_of_le hle
  have hint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable h ρ := fun ρ _ =>
    (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have h1 : ∫ x, h x ∂μ = ∫ x, h x ∂(μ - ν) + ∫ x, h x ∂ν := by
    conv_lhs => rw [← hρ]
    exact integral_add_measure (hint _) (hint _)
  have h2 : μ.real univ = (μ - ν).real univ + ν.real univ := by
    conv_lhs => rw [← hρ]
    exact measureReal_add_apply
  rw [h1, add_sub_cancel_right, h2, add_sub_cancel_right]
  have := norm_integral_le_of_norm_le_const (μ := μ - ν) (f := h) (C := C)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  rwa [Real.norm_eq_abs] at this

/-- **Integrals and the total-variation norm.** For finite measures `μ`, `ν` and measurable `h`
with `|h| ≤ C`, `|∫ h dμ − ∫ h dν| ≤ C ‖μ − ν‖_TV` (§11.3, used in (2) on p. 522). -/
theorem fp_abs_integral_sub_le [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |h x| ≤ C) : |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ C * fpTVNorm μ ν := by
  obtain ⟨s, hs, hpos, hneg⟩ := hahn_decomposition μ ν
  have hint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable h ρ := fun ρ _ =>
    (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hle1 : ν.restrict s ≤ μ.restrict s := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hpos _ (ht.inter hs) inter_subset_right
  have hle2 : μ.restrict sᶜ ≤ ν.restrict sᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hneg _ (ht.inter hs.compl) inter_subset_right
  have e1 := fp_abs_integral_sub_le_of_le hle1 hm hC
  have e2 := fp_abs_integral_sub_le_of_le hle2 hm hC
  rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ] at e1 e2
  have hsplit : ∫ x, h x ∂μ - ∫ x, h x ∂ν = (∫ x in s, h x ∂μ - ∫ x in s, h x ∂ν) -
      (∫ x in sᶜ, h x ∂ν - ∫ x in sᶜ, h x ∂μ) := by
    rw [← integral_add_compl hs (hint μ), ← integral_add_compl hs (hint ν)]
    ring
  have hTV := fp_le_tvNorm_pair μ ν hs
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  calc |∫ x, h x ∂μ - ∫ x, h x ∂ν|
      ≤ |∫ x in s, h x ∂μ - ∫ x in s, h x ∂ν| + |∫ x in sᶜ, h x ∂ν - ∫ x in sᶜ, h x ∂μ| := by
        rw [hsplit]; exact hsub _ _
    _ ≤ C * (μ.real s - ν.real s) + C * (ν.real sᶜ - μ.real sᶜ) := add_le_add e1 e2
    _ ≤ C * (|μ.real s - ν.real s| + |μ.real sᶜ - ν.real sᶜ|) := by
        rw [mul_add]
        refine add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hC0)
          (mul_le_mul_of_nonneg_left ?_ hC0)
        rw [abs_sub_comm]
        exact le_abs_self _
    _ ≤ C * fpTVNorm μ ν := mul_le_mul_of_nonneg_left hTV hC0

/-! ### Assumption 17.3 and Lemma 17.5 -/

/-- **Assumption 17.3** (pp. 520–521). For every `ε > 0` there is `δ > 0` with
`‖π(x, ·) − π(x̂, ·)‖_TV < ε` whenever `|x − x̂| < δ`. (Each `π(x, ·)` is a probability measure;
this is assumed separately.) -/
def FPAssumption17_3 [PseudoMetricSpace X] [MeasurableSpace X] (π : X → Measure X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → fpTVNorm (π x) (π xh) < ε

/-- A constant (serially independent) transition function satisfies Assumption 17.3. -/
theorem fpAssumption17_3_const [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) :
    FPAssumption17_3 (fun _ : X => μ) := by
  intro ε hε
  refine ⟨1, one_pos, fun _ _ _ => ?_⟩
  have : Nonempty {P : Finset (Set X) // FPIsFinPartition P} :=
    ⟨⟨{univ}, fpIsFinPartition_univ⟩⟩
  simp only [fpTVNorm, sub_self, abs_zero, Finset.sum_const_zero, ciSup_const]
  exact hε

/-- The operator `(Tf)(x) = ∫ G[x, x′, f(x′)] π(x, dx′)` ((1), p. 521). -/
noncomputable def fpIntOp [MeasurableSpace X] (π : X → Measure X) (G : X → X → ℝ → ℝ)
    (f : X → ℝ) (x : X) : ℝ :=
  ∫ x', G x x' (f x') ∂(π x)

/-- The integrand `x′ ↦ G[x, x′, f(x′)]` is continuous when `G` is jointly continuous on
`X × X × D` and `f` is continuous with values in `D`. -/
theorem fp_integrand_continuous [TopologicalSpace X] {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (x : X) {f : X → ℝ} (hf : Continuous f) (hfD : ∀ x', f x' ∈ D) :
    Continuous fun x' => G x x' (f x') :=
  hGc.comp_continuous (continuous_const.prodMk (continuous_id.prodMk hf)) fun x' =>
    ⟨mem_univ _, mem_univ _, hfD x'⟩

/-- A `D`-valued `G` with `D` bounded is bounded by some `B ≥ 0`. -/
theorem fp_G_bound {D : Set ℝ} (hD : Bornology.IsBounded D) {G : X → X → ℝ → ℝ}
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D) :
    ∃ B, 0 ≤ B ∧ (∀ y ∈ D, |y| ≤ B) ∧ ∀ x x' y, y ∈ D → |G x x' y| ≤ B := by
  obtain ⟨C, hC⟩ := hD.exists_norm_le
  have hyB : ∀ y ∈ D, |y| ≤ max C 0 := fun y hy => by
    have := hC y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  exact ⟨max C 0, le_max_right _ _, hyB, fun x x' y hy => hyB _ (hGD x x' y hy)⟩

/-- **Lemma 17.5** (p. 521). Let `π` satisfy Assumption 17.3, `D ⊆ ℝ` be bounded,
`F` the bounded continuous `D`-valued functions on `X`, and `G : X × X × D → D` continuous and
uniformly continuous in its first argument (uniformly in `(x′, y)`). Then the family
`T(F) = {Tf : f ∈ F}` is bounded and equicontinuous. -/
theorem lemma_17_5 [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {π : X → Measure X} (hπ : ∀ x, IsProbabilityMeasure (π x)) (hA : FPAssumption17_3 π)
    {D : Set ℝ} (hD : Bornology.IsBounded D) {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D)
    (hGu : ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → ∀ x', ∀ y ∈ D,
      |G x x' y - G xh x' y| < ε) :
    (∃ B, ∀ f : X →ᵇ ℝ, (∀ x', f x' ∈ D) → ∀ x, |fpIntOp π G f x| ≤ B) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → ∀ f : X →ᵇ ℝ, (∀ x', f x' ∈ D) →
        |fpIntOp π G f x - fpIntOp π G f xh| < ε := by
  obtain ⟨B, hB0, -, hGB⟩ := fp_G_bound hD hGD
  have hint : ∀ (x x₀ : X) (f : X →ᵇ ℝ), (∀ x', f x' ∈ D) →
      Integrable (fun x' => G x x' (f x')) (π x₀) := fun x x₀ f hf =>
    (integrable_const B).mono'
      (fp_integrand_continuous hGc x f.continuous hf).measurable.aestronglyMeasurable
      (ae_of_all _ fun x' => by
        rw [Real.norm_eq_abs]; exact hGB _ _ _ (hf x'))
  refine ⟨⟨B, fun f hf x => ?_⟩, fun ε hε => ?_⟩
  · have := norm_integral_le_of_norm_le_const (μ := π x) (C := B)
      (f := fun x' => G x x' (f x'))
      (ae_of_all _ fun x' => by rw [Real.norm_eq_abs]; exact hGB _ _ _ (hf x'))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  · obtain ⟨δ₁, hδ₁, h₁⟩ := hGu (ε / 3) (by positivity)
    obtain ⟨δ₂, hδ₂, h₂⟩ := hA (ε / (3 * (B + 1))) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x xh hxx f hf => ?_⟩
    have e1 : |∫ x', G x x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π x)| ≤ ε / 3 := by
      rw [← integral_sub (hint x x f hf) (hint xh x f hf)]
      have := norm_integral_le_of_norm_le_const (μ := π x) (C := ε / 3)
        (f := fun x' => G x x' (f x') - G xh x' (f x'))
        (ae_of_all _ fun x' => by
          rw [Real.norm_eq_abs]
          exact (h₁ x xh (lt_of_lt_of_le hxx (min_le_left _ _)) x' _ (hf x')).le)
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have e2 : |∫ x', G xh x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π xh)| ≤
        B * fpTVNorm (π x) (π xh) :=
      fp_abs_integral_sub_le _ _ (fp_integrand_continuous hGc xh f.continuous hf).measurable hB0
        fun x' => hGB _ _ _ (hf x')
    have e3 : B * fpTVNorm (π x) (π xh) ≤ ε / 3 := by
      have hTV := h₂ x xh (lt_of_lt_of_le hxx (min_le_right _ _))
      calc B * fpTVNorm (π x) (π xh) ≤ B * (ε / (3 * (B + 1))) :=
            mul_le_mul_of_nonneg_left hTV.le hB0
        _ ≤ ε / 3 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    have habs := abs_add_le (∫ x', G x x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π x))
      (∫ x', G xh x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π xh))
    simp only [fpIntOp]
    rw [sub_add_sub_cancel] at habs
    linarith

/-- **Exercise 17.6** (p. 522). Under the hypotheses of Lemma 17.5 (only boundedness of `D` and
`π(x, ·)` being probability measures are used), if `G` is uniformly continuous in its third
argument, uniformly in `(x, x′)`, then `T` is (uniformly) continuous in the sup norm. -/
theorem ex_17_6 [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {π : X → Measure X} (hπ : ∀ x, IsProbabilityMeasure (π x)) {D : Set ℝ}
    (hD : Bornology.IsBounded D) {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D)
    (hGu3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ D → y' ∈ D → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ f g : X →ᵇ ℝ, (∀ x', f x' ∈ D) → (∀ x', g x' ∈ D) → dist f g < δ →
      ∀ x, |fpIntOp π G f x - fpIntOp π G g x| < ε := by
  obtain ⟨B, -, -, hGB⟩ := fp_G_bound hD hGD
  have hint : ∀ (x x₀ : X) (f : X →ᵇ ℝ), (∀ x', f x' ∈ D) →
      Integrable (fun x' => G x x' (f x')) (π x₀) := fun x x₀ f hf =>
    (integrable_const B).mono'
      (fp_integrand_continuous hGc x f.continuous hf).measurable.aestronglyMeasurable
      (ae_of_all _ fun x' => by
        rw [Real.norm_eq_abs]; exact hGB _ _ _ (hf x'))
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hGu3 (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun f g hf hg hfg x => ?_⟩
  have hpt : ∀ x', |G x x' (f x') - G x x' (g x')| < ε / 2 := fun x' => by
    have := (dist_coe_le_dist (f := f) (g := g) x').trans_lt hfg
    rw [Real.dist_eq] at this
    exact h x x' _ _ (hf x') (hg x') this
  simp only [fpIntOp]
  rw [← integral_sub (hint x x f hf) (hint x x g hg)]
  have := norm_integral_le_of_norm_le_const (μ := π x) (C := ε / 2)
    (f := fun x' => G x x' (f x') - G x x' (g x'))
    (ae_of_all _ fun x' => by rw [Real.norm_eq_abs]; exact (hpt x').le)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  linarith

/-- **Schauder for the operator (1)** (pp. 522, 524–525). Let `X` be totally bounded (e.g. a
bounded subset of `ℝˡ`), `π` satisfy Assumption 17.3, `D ⊆ ℝ` be nonempty, closed, bounded and
convex, and `G : X × X × D → D` be continuous, uniformly continuous in its first argument and
uniformly continuous in its third. Then `T` maps `F` (the continuous `D`-valued functions) into
itself and has a fixed point in `F`. -/
theorem fp_exists_fixedPoint_intOp [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (hX : TotallyBounded (univ : Set X)) {π : X → Measure X}
    (hπ : ∀ x, IsProbabilityMeasure (π x)) (hA : FPAssumption17_3 π) {D : Set ℝ}
    (hDne : D.Nonempty) (hDcl : IsClosed D) (hDb : Bornology.IsBounded D) (hDc : Convex ℝ D)
    {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D)
    (hGu : ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → ∀ x', ∀ y ∈ D,
      |G x x' y - G xh x' y| < ε)
    (hGu3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ D → y' ∈ D → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε) :
    ∃ f : X →ᵇ ℝ, (∀ x, f x ∈ D) ∧ ∀ x, f x = fpIntOp π G f x := by
  classical
  obtain ⟨⟨B, hB⟩, hequi⟩ := lemma_17_5 hπ hA hDb hGc hGD hGu
  have hT6 := ex_17_6 hπ hDb hGc hGD hGu3
  obtain ⟨B', hB'0, hDB', hGB'⟩ := fp_G_bound hDb hGD
  set F : Set (X →ᵇ ℝ) := {f | ∀ x, f x ∈ D} with hF
  have hTc : ∀ f ∈ F, Continuous (fpIntOp π G f) := fun f hf =>
    Metric.continuous_iff.2 fun x ε hε => by
      obtain ⟨δ, hδ, h⟩ := hequi ε hε
      refine ⟨δ, hδ, fun xh hxx => ?_⟩
      rw [Real.dist_eq]
      exact h xh x hxx f hf
  set T : (X →ᵇ ℝ) → (X →ᵇ ℝ) := fun f => if hf : f ∈ F then
    ofNormedAddCommGroup (fpIntOp π G f) (hTc f hf) B
      (fun x => by rw [Real.norm_eq_abs]; exact hB f hf x) else f with hT
  have hTF : ∀ f ∈ F, ⇑(T f) = fpIntOp π G f := fun f hf => by
    simp only [hT, hf, ↓reduceDIte, coe_ofNormedAddCommGroup]
  -- the set `F`
  have hFcl : IsClosed F := by
    have : F = ⋂ x, (fun f : X →ᵇ ℝ => f x) ⁻¹' D := by
      ext f
      simp [hF]
    rw [this]
    exact isClosed_iInter fun x => hDcl.preimage ((continuous_apply x).comp continuous_coe)
  have hFconv : Convex ℝ F := by
    intro f hf g hg a b ha hb hab x
    simpa using hDc (hf x) (hg x) ha hb hab
  have hFb : Bornology.IsBounded F := isBounded_iff_forall_norm_le.2
    ⟨B', fun f hf => (norm_le hB'0).2 fun x => by
      rw [Real.norm_eq_abs]; exact hDB' _ (hf x)⟩
  have hFne : F.Nonempty := by
    obtain ⟨d, hd⟩ := hDne
    exact ⟨const X d, fun _ => hd⟩
  -- `T(F) ⊆ F`
  have hmaps : MapsTo T F F := by
    intro f hf x
    rw [hTF f hf]
    have := hπ x
    refine hDc.integral_mem hDcl (ae_of_all _ fun x' => hGD _ _ _ (hf x')) ?_
    exact (integrable_const B').mono'
      (fp_integrand_continuous hGc x f.continuous hf).measurable.aestronglyMeasurable
      (ae_of_all _ fun x' => by rw [Real.norm_eq_abs]; exact hGB' _ _ _ (hf x'))
  -- `T` is continuous on `F`
  have hcont : ContinuousOn T F := by
    refine Metric.continuousOn_iff.2 fun g hg ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hT6 (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun f hf hfg => ?_⟩
    have hle : dist (T f) (T g) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
      rw [hTF f hf, hTF g hg, Real.dist_eq]
      exact (h f g hf hg hfg x).le
    linarith
  -- `T(F)` is relatively compact
  have hequiS : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ g ∈ T '' F, |g x - g y| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi ε hε
    refine ⟨δ, hδ, fun x y hxy => ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rw [hTF f hf]
    exact h x y hxy f hf
  have htb := totallyBounded_of_equicontinuous hX (hFb.subset hmaps.image_subset) hequiS
  obtain ⟨f, hf, hTf⟩ := schauder_closed hFcl hFconv hFne hcont hmaps
    (htb.closure.isCompact_of_isClosed isClosed_closure)
  refine ⟨f, hf, fun x => ?_⟩
  have := congrArg (fun g : X →ᵇ ℝ => g x) hTf
  rw [← this, hTF f hf]

/-! ### Proposition 4 -/

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- **Proposition 4** (p. 522). Let `X = [a, b] ⊂ ℝ₊₊`, `π` a transition function on `X`
satisfying Assumption 17.3, and `H`, `V` satisfy Assumption 17.1. Then there is a continuous,
strictly positive (indeed bounded away from zero) `f* : X → ℝ₊₊` with
`f*(x) = ∫ φ[x′ ζ⁻¹(f*(x′))] π(x, dx′)` for all `x ∈ X`. -/
theorem proposition_4 (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {π : Icc a b → Measure (Icc a b)} (hπ : ∀ x, IsProbabilityMeasure (π x))
    (hA3 : FPAssumption17_3 π) :
    ∃ f : Icc a b →ᵇ ℝ, (∃ ε > 0, ∀ x, ε ≤ f x) ∧
      ∀ x, f x = ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (f x')) ∂(π x) := by
  obtain ⟨ε, hε, B, hεB, hup, hlow⟩ := fp_bounds hA ha hab
  set G : Icc a b → Icc a b → ℝ → ℝ := fun _ x' y => fpPhi V' ((x' : ℝ) * fpZetaInv L H' y)
    with hG
  have hX : TotallyBounded (univ : Set (Icc a b)) :=
    (isCompact_iff_isCompact_univ.1 isCompact_Icc).totallyBounded
  -- joint continuity of `(x′, y) ↦ φ(x′ ζ⁻¹(y))` on `[a, b] × [ε, B]`
  have hc2 : ContinuousOn (fun q : ℝ × ℝ => fpPhi V' (q.1 * fpZetaInv L H' q.2))
      (Icc a b ×ˢ Icc ε B) :=
    (fpPhi_continuousOn hA).comp (continuous_fst.continuousOn.mul
      ((fpZetaInv_continuousOn hA).comp continuous_snd.continuousOn
        fun q hq => hε.le.trans hq.2.1))
      fun q hq => mul_nonneg (ha.le.trans hq.1.1) (fpZetaInv_mem hA (hε.le.trans hq.2.1)).1
  have hGc : ContinuousOn (fun p : Icc a b × Icc a b × ℝ => G p.1 p.2.1 p.2.2)
      (univ ×ˢ univ ×ˢ Icc ε B) :=
    hc2.comp ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)).continuousOn
      fun p hp => ⟨p.2.1.2, hp.2.2⟩
  have hGD : ∀ x x' y, y ∈ Icc ε B → G x x' y ∈ Icc ε B := fun _ x' y hy =>
    ⟨(hlow x' x'.2 y hy.1).le, (hup x' x'.2 y (hε.le.trans hy.1)).2⟩
  have hGu : ∀ ε' > 0, ∃ δ > 0, ∀ x xh : Icc a b, dist x xh < δ → ∀ x', ∀ y ∈ Icc ε B,
      |G x x' y - G xh x' y| < ε' := fun ε' hε' =>
    ⟨1, one_pos, fun _ _ _ _ _ _ => by simp only [hG, sub_self, abs_zero]; exact hε'⟩
  have hGu3 : ∀ ε' > 0, ∃ δ > 0, ∀ x x' y y', y ∈ Icc ε B → y' ∈ Icc ε B → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε' := by
    intro ε' hε'
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc2) ε' hε'
    refine ⟨δ, hδ, fun _ x' y y' hy hy' hyy => ?_⟩
    have hd : dist ((x' : ℝ), y) ((x' : ℝ), y') < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
      exact hyy
    have := h ((x' : ℝ), y) ⟨x'.2, hy⟩ ((x' : ℝ), y') ⟨x'.2, hy'⟩ hd
    rwa [Real.dist_eq] at this
  obtain ⟨f, hfD, hf⟩ := fp_exists_fixedPoint_intOp hX hπ hA3 (nonempty_Icc.2 hεB.le)
    isClosed_Icc (Metric.isBounded_Icc ε B) (convex_Icc ε B) hGc hGD hGu hGu3
  exact ⟨f, ⟨ε, hε, fun x => (hfD x).1⟩, hf⟩

/-- **The trivial solution of Proposition 4's equation.** `f ≡ 0` solves
`f(x) = ∫ φ[x′ ζ⁻¹(f(x′))] π(x, dx′)`, since `ζ⁻¹(0) = 0` and `φ(0) = 0`. -/
theorem proposition_4_zero_fixedPoint (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ}
    (π : Icc a b → Measure (Icc a b)) (x : Icc a b) :
    (0 : ℝ) = ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' 0) ∂(π x) := by
  simp [fpZetaInv_zero hA, fpPhi_zero]

/-! ### Exercise 17.7 -/

/-- The operator of Exercise 17.7, `(Sn)(x) = ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]` (p. 525). -/
noncomputable def fpLabourOp {a b : ℝ} (π : Icc a b → Measure (Icc a b)) (L : ℝ)
    (H' V' : ℝ → ℝ) (n : Icc a b → ℝ) (x : Icc a b) : ℝ :=
  fpZetaInv L H' (∫ x', fpPhi V' ((x' : ℝ) * n x') ∂(π x))

/-- **Exercise 17.7 is trivial as stated**: `n ≡ 0` is always a fixed point of `S`. -/
theorem ex_17_7_zero (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ}
    (π : Icc a b → Measure (Icc a b)) : fpLabourOp π L H' V' (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [fpLabourOp, fpPhi_zero, fpZetaInv_zero hA]

/-- **Exercise 17.7, "Why?" (from `f*` to `n*`).** If `f*` solves (8) of §17.1, then
`n* = ζ⁻¹ ∘ f*` is a fixed point of `S`. -/
theorem ex_17_7_why_of_f {a b : ℝ} (π : Icc a b → Measure (Icc a b)) {f : Icc a b → ℝ}
    (hf : ∀ x, f x = ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (f x')) ∂(π x)) (x : Icc a b) :
    fpZetaInv L H' (f x) = fpLabourOp π L H' V' (fun x => fpZetaInv L H' (f x)) x := by
  simp only [fpLabourOp]
  rw [← hf x]

/-- **Exercise 17.7, "Why?" (from `n*` to `f*`).** If `n* : X → [0, L)` is a fixed point of `S`,
then `f* = ζ ∘ n*` solves (8) of §17.1. -/
theorem ex_17_7_why_of_n (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 ≤ a)
    (π : Icc a b → Measure (Icc a b)) {n : Icc a b → ℝ} (hn : ∀ x, n x ∈ Ico 0 L)
    (hfix : ∀ x, n x = fpLabourOp π L H' V' n x) (x : Icc a b) :
    fpZeta H' (n x) =
      ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (fpZeta H' (n x'))) ∂(π x) := by
  have hI : ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (fpZeta H' (n x'))) ∂(π x) =
      ∫ x', fpPhi V' ((x' : ℝ) * n x') ∂(π x) := by
    congr 1
    funext x'
    rw [fpZetaInv_zeta hA (hn x')]
  rw [hI, hfix x, fpLabourOp]
  exact fpZeta_zetaInv hA (integral_nonneg fun x' =>
    fpPhi_nonneg hA (mul_nonneg (ha.trans x'.2.1) (hn x').1))

/-- **Exercise 17.7, corrected** (p. 525). Under the hypotheses of Proposition 4, the operator
`(Sn)(x) = ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]` has a continuous fixed point `n* : X → (0, L)` that is
bounded away from zero (so it is not the trivial fixed point `0`). -/
theorem ex_17_7 (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {π : Icc a b → Measure (Icc a b)} (hπ : ∀ x, IsProbabilityMeasure (π x))
    (hA3 : FPAssumption17_3 π) :
    ∃ n : Icc a b →ᵇ ℝ, (∃ η > 0, ∀ x, η ≤ n x) ∧ (∀ x, n x < L) ∧
      ∀ x, n x = fpLabourOp π L H' V' n x := by
  obtain ⟨f, ⟨ε, hε, hfε⟩, hf⟩ := proposition_4 hA ha hab hπ hA3
  have hf0 : ∀ x, 0 ≤ f x := fun x => hε.le.trans (hfε x)
  have hcont : Continuous fun x => fpZetaInv L H' (f x) :=
    (fpZetaInv_continuousOn hA).comp_continuous f.continuous hf0
  set n : Icc a b →ᵇ ℝ := ofNormedAddCommGroup (fun x => fpZetaInv L H' (f x)) hcont L
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fpZetaInv_mem hA (hf0 x)).1]
      exact (fpZetaInv_mem hA (hf0 x)).2.le) with hn
  have hncoe : ⇑n = fun x => fpZetaInv L H' (f x) := coe_ofNormedAddCommGroup _ _ _ _
  refine ⟨n, ⟨fpZetaInv L H' ε, ?_, fun x => ?_⟩, fun x => ?_, fun x => ?_⟩
  · have := fpZetaInv_strictMonoOn hA (mem_Ici.2 le_rfl) (mem_Ici.2 hε.le) hε
    rwa [fpZetaInv_zero hA] at this
  · rw [hncoe]
    exact (fpZetaInv_strictMonoOn hA).monotoneOn (mem_Ici.2 hε.le) (mem_Ici.2 (hf0 x)) (hfε x)
  · rw [hncoe]
    exact (fpZetaInv_mem hA (hf0 x)).2
  · rw [hncoe]
    exact ex_17_7_why_of_f π hf x

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: the information structure

SLP §17.6, pp. 531–537: the islands model with monetary shocks `x ∈ X = [x̲, x̄]` and real
shocks `θ ∈ Θ = [θ̲, θ̄]`, independent with densities `ψ`, `g`, and the ratio
`z = x/θ ∈ Z = [x̲/θ̄, x̄/θ̲]`.
Densities are functions on `ℝ` vanishing off `X`, `Θ`; integrals are Lebesgue integrals on `ℝ`.

* **Assumption 17.5** (`ShocksAssumption17_5`, p. 532). `shocksPi` is the density
  `π(z) = ∫ g(θ) θ ψ(zθ) dθ` of `z` (p. 534; `integral_pi`: it integrates to `1`).
* `shocksA`, `shocksB`: `a(z) = max{x̲/z, θ̲}`, `b(z) = min{x̄/z, θ̄}` ((5), p. 536);
  `mem_Icc_shocksA_shocksB_iff`: `θ ∈ Θ ∧ zθ ∈ X ↔ θ ∈ [a(z), b(z)]`.
* **Exercise 17.8a**, corrected. `ShocksAssumption17_5.joint`: the joint density of `(θ, z)` is
  `g(θ) θ ψ(zθ)` (change of variables `x = zθ` and Fubini). `ex_17_8a_disintegration`:
  `E h(θ, z) = ∫ π(z) ∫ h(θ, z) g(θ|z) dθ dz` with `g(θ|z) = g(θ) θ ψ(zθ)/π(z)`
  (`shocksCondDens`), so `g(·|z)` is the conditional density; `ex_17_8a`: where `π(z) > 0` it is a
  probability density vanishing off `[a(z), b(z)]` and continuous on `[a(z), b(z)]`.
* `shocksCondLaw`: the conditional law `G(·|z)` (density `g(·|z)` on `int Z`, `δ_{θ̄}` at `z̲`,
  `δ_{θ̲}` at `z̄`). `ShocksAssumption17_5.pi_pos`: `π > 0` on `int Z` if `ψ > 0` on `X` and
  `g > 0` on `Θ`.
* **Exercise 17.8b** (`ShocksAssumption17_5.ex_17_8b`): if `π > 0` on `int Z`, `z ↦ G(·|z)` is
  weakly continuous on `Z` (dominated convergence inside, shrinking supports at the endpoints).
* **Exercise 17.10** (`ex_17_10`, p. 536; no answer in the manual): `G(·|z_n) → G(·|z̲)` weakly but
  `‖G(·|z_n) − G(·|z̲)‖_TV ≥ 1`, and `G(·|z_n)` has no total-variation limit at all.
* **Assumption 17.6** (uniform `Ψ`, `G`): `shocksUnif`, `shocksUnif_assumption17_5`.
* **Exercise 17.12, corrected** (`ex_17_12`): under Assumption 17.6, `g(θ|z) = 2θ/(b(z)² − a(z)²)`
  on `[a(z), b(z)]`.
* The NOTE on p. 533: `p533_ratio_of_price` (what the argument proves) and `p533_counterexample`.

**Correction (Exercise 17.12 is false).** Under Assumption 17.6 the conditional law of `θ` given
`z` has density proportional to `θ` on `[a(z), b(z)]` (the Jacobian of `x = zθ`; the book's own
`π(z)` contains it), not the uniform density. `ex_17_12_counterexample`: with `x ~ U[1, 2]`,
`θ ~ U[1, 3/2]`, the uniform family does not disintegrate the joint law (for
`h = θ·1{z ∈ [1, 4/3]}` it gives `25/48` instead of `19/36`). The manual's "proof" treats `x` as
uniform along the null set `{x = zθ}` (a Borel–Kolmogorov-type error). The support `[a(z), b(z)]`
in (5) is correct. Consequently the weights in (6a), (7) and in `J` of Proposition 8 must be
`2θ/(b² − a²)`; Proposition 7 and Exercise 17.14d are proved with these weights in
`FixedPointArguments.ShocksSchauder` and `FixedPointArguments.ShocksMonotone`.

**Correction (manual, Exercise 17.8a).** The manual's density `g(θ)ψ(θz)/π(z)` omits the factor
`θ` and does not integrate to `1` (`ex_17_8a_manual_counterexample`: `4/5` in the example at
`z = 1`).

**Correction (Exercise 17.8a, hypotheses).** (i) `g(·|z)` needs `π(z) > 0`, which Assumption 17.5
does not guarantee at interior points: `ex_17_8a_pi_zero_counterexample` (`π(3/4) = 0` with
`Z = [2/3, 2]`); positivity of `ψ` on `X` and `g` on `Θ` suffices (`pi_pos`). (ii) "`G(·|z)` has a
continuous density" is false when, as Assumption 17.6 requires, the densities are continuous only on
`X` and `Θ`: `ex_17_8a_continuity_counterexample` (in the example at `z = 4/5`, `g(·|z)` jumps at
`a(z) = 5/4 ∈ int Θ`, and no function continuous on `Θ` equals it a.e.). The density is continuous
on `[a(z), b(z)]`. (iii) Part (b) needs the endpoint convention `G(·|z̲) = δ_{θ̄}`,
`G(·|z̄) = δ_{θ̲}` (the only possible weak limits).

**Correction (p. 533).** The argument shows only that equal prices imply equal ratios `x/θ`
(`p533_ratio_of_price`); it does not show that an equilibrium price is a function `ρ(x/θ)`:
`p533_counterexample` satisfies every premise used there, yet the price is not a function of
`x/θ`. The existence results that follow concern equilibria of the form `ρ(x/θ)` only. For
continuous prices the conclusion is true (`islands_eqm_price_of_ratio` in
`FixedPointArguments.ShocksRevelation`); for discontinuous prices it is not settled.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

/-- **Assumption 17.5** (p. 532). The monetary shock `x` lies in `X = [x̲, x̄]`, `0 < x̲ < x̄`, and
the real shock `θ` in `Θ = [θ̲, θ̄]`, `0 < θ̲ < θ̄ < 2`; `x` and `θ` are independent with densities
`ψ` and `g` (taken on all of `ℝ`, zero off `X` and `Θ`), continuous on `X` and `Θ`. -/
structure ShocksAssumption17_5 (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) : Prop where
  xlo_pos : 0 < xlo
  xlo_lt : xlo < xhi
  θlo_pos : 0 < θlo
  θlo_lt : θlo < θhi
  θhi_lt : θhi < 2
  ψ_nonneg : ∀ x, 0 ≤ ψ x
  g_nonneg : ∀ θ, 0 ≤ g θ
  ψ_zero : ∀ x ∉ Icc xlo xhi, ψ x = 0
  g_zero : ∀ θ ∉ Icc θlo θhi, g θ = 0
  ψ_cont : ContinuousOn ψ (Icc xlo xhi)
  g_cont : ContinuousOn g (Icc θlo θhi)
  ψ_int : ∫ x, ψ x = 1
  g_int : ∫ θ, g θ = 1

/-- The density of `z = x/θ` (p. 534): `π(z) = ∫ g(θ) θ ψ(zθ) dθ`. -/
noncomputable def shocksPi (ψ g : ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ, g θ * θ * ψ (z * θ)

/-- The lower end `a(z) = max{x̲/z, θ̲}` of the support of `G(·|z)` ((5), p. 536). -/
noncomputable def shocksA (xlo θlo z : ℝ) : ℝ := max (xlo / z) θlo

/-- The upper end `b(z) = min{x̄/z, θ̄}` of the support of `G(·|z)` ((5), p. 536). -/
noncomputable def shocksB (xhi θhi z : ℝ) : ℝ := min (xhi / z) θhi

/-- The conditional density `g(θ|z) = g(θ) θ ψ(zθ)/π(z)` of `θ` given `z = x/θ` (Exercise 17.8a,
corrected: the factor `θ` is the Jacobian of `x = zθ`). -/
noncomputable def shocksCondDens (ψ g : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  g θ * θ * ψ (z * θ) / shocksPi ψ g z

/-- The conditional law `G(·|z)` of `θ` given `z = x/θ`: density `g(θ|z)` for `z ∈ int Z`, and the
endpoint convention `G(·|z̲) = δ_{θ̄}`, `G(·|z̄) = δ_{θ̲}` (the weak limits, Exercise 17.8b). -/
noncomputable def shocksCondLaw (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) (z : ℝ) : Measure ℝ :=
  if xlo / θhi < z ∧ z < xhi / θlo then
    volume.withDensity fun θ => ENNReal.ofReal (shocksCondDens ψ g z θ)
  else if z ≤ xlo / θhi then Measure.dirac θhi else Measure.dirac θlo

variable {xlo xhi θlo θhi : ℝ} {ψ g : ℝ → ℝ}

/-- For `z > 0`: `θ ∈ Θ` and `zθ ∈ X` iff `θ ∈ [a(z), b(z)]`. -/
theorem mem_Icc_shocksA_shocksB_iff {z θ : ℝ} (hz : 0 < z) :
    (θ ∈ Icc θlo θhi ∧ z * θ ∈ Icc xlo xhi) ↔ θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z) := by
  simp only [shocksA, shocksB, mem_Icc, max_le_iff, le_min_iff, div_le_iff₀ hz,
    le_div_iff₀ hz]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, h1⟩, by linarith, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h2, h4⟩, by linarith, by linarith⟩

/-- A function continuous on `[a, b]` and zero off it is measurable. -/
theorem shocks_measurable_of_zero_off {a b : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∉ Icc a b, f x = 0) : Measurable f := by
  classical
  have : f = (Icc a b).piecewise f (fun _ => 0) := by
    ext x
    by_cases hx : x ∈ Icc a b
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [this]
  exact hc.measurable_piecewise continuousOn_const measurableSet_Icc

/-- A function continuous on `[a, b]` and zero off it is bounded. -/
theorem shocks_exists_bound_of_zero_off {a b : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∉ Icc a b, f x = 0) : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc a b
  · exact (Real.norm_eq_abs _ ▸ hC x hx).trans (le_max_left _ _)
  · rw [h0 x hx, abs_zero]; exact le_max_right _ _

/-- On `int Z`, `z > 0` and `a(z) < b(z)`. -/
theorem shocksA_lt_shocksB (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo) :
    0 < z ∧ shocksA xlo θlo z < shocksB xhi θhi z := by
  have hz0 : 0 < z := (div_pos hx0 (hθ0.trans hθ)).trans hzZ.1
  refine ⟨hz0, ?_⟩
  simp only [shocksA, shocksB, max_lt_iff, lt_min_iff]
  refine ⟨⟨div_lt_div_of_pos_right hx hz0, ?_⟩, ?_, hθ⟩
  · rw [lt_div_iff₀ hz0]; rw [lt_div_iff₀ hθ0] at hzZ
    linarith [hzZ.2]
  · rw [div_lt_iff₀ hz0]; rw [div_lt_iff₀ (hθ0.trans hθ)] at hzZ
    linarith [hzZ.1]

namespace ShocksAssumption17_5

variable (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
include hA

/-- `ψ` is measurable. -/
theorem ψ_meas : Measurable ψ := shocks_measurable_of_zero_off hA.ψ_cont hA.ψ_zero
/-- `g` is measurable. -/
theorem g_meas : Measurable g := shocks_measurable_of_zero_off hA.g_cont hA.g_zero

/-- If `θ ∈ Θ` and `zθ ∈ X` then `z ∈ Z = [x̲/θ̄, x̄/θ̲]`. -/
theorem mem_Z_of {θ z : ℝ} (hθ : θ ∈ Icc θlo θhi) (hx : z * θ ∈ Icc xlo xhi) :
    z ∈ Icc (xlo / θhi) (xhi / θlo) := by
  have hθ0 : 0 < θ := hA.θlo_pos.trans_le hθ.1
  have hz : z = z * θ / θ := by field_simp
  have hzθ : 0 < z * θ := hA.xlo_pos.trans_le hx.1
  rw [hz]
  exact ⟨div_le_div₀ hzθ.le hx.1 hθ0 hθ.2, div_le_div₀ (hA.xlo_pos.trans hA.xlo_lt).le hx.2
    hA.θlo_pos hθ.1⟩

/-- The joint density of `(θ, z)` is integrable when multiplied by a bounded measurable `h`. -/
theorem integrable_joint {h : ℝ × ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ p, |h p| ≤ C) :
    Integrable (fun p : ℝ × ℝ => h p * (g p.1 * p.1 * ψ (p.2 * p.1)))
      (volume.prod volume) := by
  obtain ⟨Cg, hCg0, hCg⟩ := shocks_exists_bound_of_zero_off hA.g_cont hA.g_zero
  obtain ⟨Cψ, hCψ0, hCψ⟩ := shocks_exists_bound_of_zero_off hA.ψ_cont hA.ψ_zero
  set S : Set (ℝ × ℝ) := Icc θlo θhi ×ˢ Icc (xlo / θhi) (xhi / θlo)
  have hS : volume.prod volume S < ⊤ := by
    rw [Measure.prod_prod]
    simp only [Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hmeas : Measurable (fun p : ℝ × ℝ => h p * (g p.1 * p.1 * ψ (p.2 * p.1))) :=
    hm.mul ((hA.g_meas.comp measurable_fst).mul measurable_fst |>.mul
      (hA.ψ_meas.comp (measurable_snd.mul measurable_fst)))
  refine (integrableOn_const (C := C * (Cg * θhi * Cψ)) hS.ne).integrable_indicator
    (measurableSet_Icc.prod measurableSet_Icc) |>.mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  by_cases hp : p ∈ S
  · rw [indicator_of_mem hp]
    have hθ := hp.1
    have h1 : 0 ≤ p.1 := hA.θlo_pos.le.trans hθ.1
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h1]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p)
    exact mul_le_mul (hC p) (mul_le_mul (mul_le_mul (hCg _) hθ.2 h1 hCg0) (hCψ _)
      (abs_nonneg _) (mul_nonneg hCg0 (hA.θlo_pos.le.trans hA.θlo_lt.le)))
      (by positivity) hC0
  · rw [indicator_of_notMem hp]
    simp only [S, mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · simp [hA.g_zero _ hp]
    · by_cases hθ : p.1 ∈ Icc θlo θhi
      · have : p.2 * p.1 ∉ Icc xlo xhi := fun hx => hp (hA.mem_Z_of hθ hx)
        simp [hA.ψ_zero _ this]
      · simp [hA.g_zero _ hθ]

/-- Change of variables `x = zθ` for fixed `θ` (the Jacobian is `θ`). -/
theorem inner_change {h : ℝ × ℝ → ℝ} (θ : ℝ) :
    g θ * ∫ x, ψ x * h (θ, x / θ) = ∫ z, h (θ, z) * (g θ * θ * ψ (z * θ)) := by
  by_cases hθ : θ ∈ Icc θlo θhi
  · have hθ0 : 0 < θ := hA.θlo_pos.trans_le hθ.1
    have e : ∫ x, ψ x * h (θ, x / θ) = θ * ∫ z, ψ (z * θ) * h (θ, z) := by
      have := Measure.integral_comp_div (fun z => ψ (z * θ) * h (θ, z)) θ
      simp only [div_mul_cancel₀ _ hθ0.ne', abs_of_pos hθ0, smul_eq_mul] at this
      exact this
    rw [e, ← mul_assoc,
      ← integral_const_mul]
    congr 1
    ext z
    ring
  · simp [hA.g_zero θ hθ]

/-- **Exercise 17.8a, joint law.** -/
theorem joint {h : ℝ × ℝ → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ p, |h p| ≤ C) :
    ∫ θ, g θ * ∫ x, ψ x * h (θ, x / θ) = ∫ z, ∫ θ, h (θ, z) * (g θ * θ * ψ (z * θ)) := by
  simp_rw [hA.inner_change]
  exact integral_integral_swap (hA.integrable_joint hm hC)

/-- The joint density `g(θ) θ ψ(zθ)` is bounded by a constant times the indicator of `Θ`. -/
theorem exists_joint_bound : ∃ K, 0 ≤ K ∧ ∀ z θ,
    |g θ * θ * ψ (z * θ)| ≤ (Icc θlo θhi).indicator (fun _ => K) θ := by
  obtain ⟨Cg, hCg0, hCg⟩ := shocks_exists_bound_of_zero_off hA.g_cont hA.g_zero
  obtain ⟨Cψ, hCψ0, hCψ⟩ := shocks_exists_bound_of_zero_off hA.ψ_cont hA.ψ_zero
  refine ⟨Cg * θhi * Cψ, by positivity [(hA.θlo_pos.trans hA.θlo_lt).le], fun z θ => ?_⟩
  by_cases hθ : θ ∈ Icc θlo θhi
  · rw [indicator_of_mem hθ]
    have h1 : 0 ≤ θ := hA.θlo_pos.le.trans hθ.1
    rw [abs_mul, abs_mul, abs_of_nonneg h1]
    exact mul_le_mul (mul_le_mul (hCg _) hθ.2 h1 hCg0) (hCψ _) (abs_nonneg _)
      (mul_nonneg hCg0 (hA.θlo_pos.le.trans hA.θlo_lt.le))
  · rw [indicator_of_notMem hθ]
    simp [hA.g_zero _ hθ]

/-- The joint density is measurable in `θ`. -/
theorem measurable_joint (z : ℝ) : Measurable (fun θ => g θ * θ * ψ (z * θ)) :=
  (hA.g_meas.mul measurable_id).mul (hA.ψ_meas.comp (measurable_const.mul measurable_id))

/-- For fixed `z`, `θ ↦ k(θ) g(θ) θ ψ(zθ)` is integrable for bounded measurable `k`. -/
theorem integrable_slice {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ θ, |k θ| ≤ C)
    (z : ℝ) : Integrable (fun θ => k θ * (g θ * θ * ψ (z * θ))) := by
  obtain ⟨K, hK0, hK⟩ := hA.exists_joint_bound
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (integrableOn_const (s := Icc θlo θhi) (C := C * K)
    (by simp)).integrable_indicator measurableSet_Icc |>.mono'
    (hk.mul (hA.measurable_joint z)).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hθ : θ ∈ Icc θlo θhi
  · rw [indicator_of_mem hθ]
    have := hK z θ
    rw [indicator_of_mem hθ] at this
    exact mul_le_mul (hC θ) this (abs_nonneg _) hC0
  · rw [indicator_of_notMem hθ]
    simp [hA.g_zero _ hθ]

/-- The joint density is integrable in `θ`. -/
theorem integrable_joint_slice (z : ℝ) : Integrable (fun θ => g θ * θ * ψ (z * θ)) :=
  (hA.integrable_slice (k := fun _ => 1) measurable_const (C := 1) (fun _ => by simp) z).congr
    (ae_of_all _ fun θ => by simp)

/-- The joint density `g(θ) θ ψ(zθ)` is nonnegative. -/
theorem joint_nonneg (z θ : ℝ) : 0 ≤ g θ * θ * ψ (z * θ) := by
  by_cases hθ : θ ∈ Icc θlo θhi
  · exact mul_nonneg (mul_nonneg (hA.g_nonneg θ) (hA.θlo_pos.le.trans hθ.1)) (hA.ψ_nonneg _)
  · simp [hA.g_zero _ hθ]

/-- The joint density vanishes off `[a(z), b(z)]` (for `z > 0`). -/
theorem joint_eq_zero {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∉ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)) : g θ * θ * ψ (z * θ) = 0 := by
  rw [← mem_Icc_shocksA_shocksB_iff hz, not_and_or] at hθ
  rcases hθ with h | h
  · simp [hA.g_zero _ h]
  · simp [hA.ψ_zero _ h]

/-- `π(z) ≥ 0`. -/
theorem pi_nonneg (z : ℝ) : 0 ≤ shocksPi ψ g z :=
  integral_nonneg fun θ => hA.joint_nonneg z θ

/-- **`π` is a probability density** (p. 534): `∫ π = 1`. -/
theorem integral_pi : ∫ z, shocksPi ψ g z = 1 := by
  have h := hA.joint (h := fun _ => 1) measurable_const (C := 1) (fun _ => by simp)
  simp only [one_mul, mul_one, hA.ψ_int, hA.g_int] at h
  exact h.symm

/-- `π(z) > 0` forces `z > 0`. -/
theorem pos_of_pi_pos {z : ℝ} (hz : 0 < shocksPi ψ g z) : 0 < z := by
  by_contra h
  push Not at h
  have : shocksPi ψ g z = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun θ => ?_)
    by_cases hθ : θ ∈ Icc θlo θhi
    · have : z * θ ∉ Icc xlo xhi := fun hx => by
        have := mul_nonpos_of_nonpos_of_nonneg h (hA.θlo_pos.le.trans hθ.1)
        linarith [hx.1, hA.xlo_pos]
      simp [hA.ψ_zero _ this]
    · simp [hA.g_zero _ hθ]
  linarith

/-- The conditional density is measurable in `θ`. -/
theorem measurable_condDens (z : ℝ) : Measurable (shocksCondDens ψ g z) :=
  ((hA.g_meas.mul measurable_id).mul (hA.ψ_meas.comp (measurable_const.mul
    measurable_id))).div_const _

/-- **Exercise 17.8a** (p. 534), corrected. Where `π(z) > 0`, `G(·|z)` has the density
`g(θ|z) = g(θ) θ ψ(zθ)/π(z)`: it is nonnegative, integrates to `1`, vanishes off
`[a(z), b(z)]` and is continuous on `[a(z), b(z)]`. (It is the conditional density by
`ex_17_8a_disintegration`.) -/
theorem ex_17_8a {z : ℝ} (hz : 0 < shocksPi ψ g z) :
    (∀ θ, 0 ≤ shocksCondDens ψ g z θ) ∧ ∫ θ, shocksCondDens ψ g z θ = 1 ∧
      (∀ θ ∉ Icc (shocksA xlo θlo z) (shocksB xhi θhi z), shocksCondDens ψ g z θ = 0) ∧
      ContinuousOn (shocksCondDens ψ g z) (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)) := by
  have hz0 := hA.pos_of_pi_pos hz
  refine ⟨fun θ => div_nonneg (hA.joint_nonneg z θ) hz.le, ?_, fun θ hθ => ?_, ?_⟩
  · simp only [shocksCondDens]
    rw [integral_div]
    exact div_self hz.ne'
  · simp [shocksCondDens, hA.joint_eq_zero hz0 hθ]
  · have hsub : ∀ θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z),
        θ ∈ Icc θlo θhi ∧ z * θ ∈ Icc xlo xhi := fun θ hθ =>
      (mem_Icc_shocksA_shocksB_iff hz0).2 hθ
    refine ContinuousOn.div_const (((hA.g_cont.mono fun θ hθ => (hsub θ hθ).1).mul
      continuousOn_id).mul (hA.ψ_cont.comp (continuousOn_const.mul continuousOn_id)
        fun θ hθ => (hsub θ hθ).2)) _

/-- **Exercise 17.8a, disintegration.** `E[h(θ, z)] = ∫ π(z) ∫ h(θ, z) g(θ|z) dθ dz` for bounded
measurable `h`: `g(·|z)` is the conditional density of `θ` given `z`. -/
theorem ex_17_8a_disintegration {h : ℝ × ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ p, |h p| ≤ C) :
    ∫ θ, g θ * ∫ x, ψ x * h (θ, x / θ) =
      ∫ z, shocksPi ψ g z * ∫ θ, h (θ, z) * shocksCondDens ψ g z θ := by
  rw [hA.joint hm hC]
  congr 1
  ext z
  have hint : Integrable (fun θ => h (θ, z) * (g θ * θ * ψ (z * θ))) :=
    hA.integrable_slice (hm.comp (measurable_id.prodMk measurable_const)) (fun θ => hC _) z
  by_cases hz : shocksPi ψ g z = 0
  · rw [hz, zero_mul]
    have h0 : (fun θ => g θ * θ * ψ (z * θ)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun θ => hA.joint_nonneg z θ)
        (hA.integrable_joint_slice z)).1 hz
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with θ hθ
    simp only [Pi.zero_apply] at hθ ⊢
    rw [hθ, mul_zero]
  · simp only [shocksCondDens, mul_div_assoc']
    rw [integral_div, mul_div_cancel₀ _ hz]

/-- On `int Z` with `π(z) > 0`, `G(·|z)` is a probability measure. -/
theorem isProbabilityMeasure_condLaw {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo)
    (hz : 0 < shocksPi ψ g z) :
    IsProbabilityMeasure (shocksCondLaw xlo xhi θlo θhi ψ g z) := by
  obtain ⟨hnn, h1, -, -⟩ := hA.ex_17_8a hz
  constructor
  simp only [shocksCondLaw, hzZ, and_self, ↓reduceIte]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ hnn), h1, ENNReal.ofReal_one]
  exact (hA.integrable_joint_slice z).div_const (shocksPi ψ g z)

/-- On `int Z`, integrals against `G(·|z)` are integrals against `g(·|z)`. -/
theorem integral_condLaw {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo)
    (hz : 0 < shocksPi ψ g z) (k : ℝ → ℝ) :
    ∫ θ, k θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z = ∫ θ, k θ * shocksCondDens ψ g z θ := by
  obtain ⟨hnn, -, -, -⟩ := hA.ex_17_8a hz
  simp only [shocksCondLaw, hzZ, and_self, ↓reduceIte]
  rw [integral_withDensity_eq_integral_toReal_smul (hA.measurable_condDens z).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  ext θ
  rw [ENNReal.toReal_ofReal (hnn θ), smul_eq_mul, mul_comm]

/-- With `ψ > 0` on `X` and `g > 0` on `Θ`, `π(z) > 0` on `int Z` (the hypothesis missing from
Exercise 17.8a). -/
theorem pi_pos (hψ : ∀ x ∈ Icc xlo xhi, 0 < ψ x) (hg : ∀ θ ∈ Icc θlo θhi, 0 < g θ) {z : ℝ}
    (hzZ : xlo / θhi < z ∧ z < xhi / θlo) : 0 < shocksPi ψ g z := by
  obtain ⟨hz0, hab⟩ := shocksA_lt_shocksB hA.xlo_pos hA.xlo_lt hA.θlo_pos hA.θlo_lt hzZ
  refine (integral_pos_iff_support_of_nonneg (fun θ => hA.joint_nonneg z θ)
    (hA.integrable_joint_slice z)).2 ?_
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (shocksA xlo θlo z) (shocksB xhi θhi z))
    fun θ hθ => ?_)
  · simp [hab]
  · have h := (mem_Icc_shocksA_shocksB_iff hz0).2 (Ioo_subset_Icc_self hθ)
    exact (mul_pos (mul_pos (hg θ h.1) (hA.θlo_pos.trans_le h.1.1)) (hψ _ h.2)).ne'

/-- `ψ` is continuous at every point other than `x̲`, `x̄`. -/
theorem ψ_continuousAt {y : ℝ} (h1 : y ≠ xlo) (h2 : y ≠ xhi) : ContinuousAt ψ y := by
  by_cases hy : y ∈ Icc xlo xhi
  · exact hA.ψ_cont.continuousAt (Icc_mem_nhds (lt_of_le_of_ne hy.1 (Ne.symm h1))
      (lt_of_le_of_ne hy.2 h2))
  · have : ψ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hy] with x hx
      exact hA.ψ_zero x hx
    exact continuousAt_const.congr this.symm

/-- `z ↦ ∫ k(θ) g(θ) θ ψ(zθ) dθ` is continuous at `z₀ > 0` (dominated convergence; the
integrand is continuous in `z` except at the two values `θ = x̲/z₀, x̄/z₀`). -/
theorem continuousAt_slice {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ θ, |k θ| ≤ C)
    {z₀ : ℝ} (hz₀ : 0 < z₀) :
    ContinuousAt (fun z => ∫ θ, k θ * (g θ * θ * ψ (z * θ))) z₀ := by
  obtain ⟨K, hK0, hK⟩ := hA.exists_joint_bound
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine continuousAt_of_dominated
    (bound := (Icc θlo θhi).indicator (fun _ => C * K))
    (Eventually.of_forall fun z => (hk.mul (hA.measurable_joint z)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ae_of_all _ fun θ => ?_)
    ((integrableOn_const (s := Icc θlo θhi) (C := C * K) (by simp)).integrable_indicator
      measurableSet_Icc) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hθ : θ ∈ Icc θlo θhi
    · rw [indicator_of_mem hθ]
      have := hK z θ
      rw [indicator_of_mem hθ] at this
      exact mul_le_mul (hC θ) this (abs_nonneg _) hC0
    · rw [indicator_of_notMem hθ]
      simp [hA.g_zero _ hθ]
  · have hfin : volume ({xlo / z₀, xhi / z₀} : Set ℝ) = 0 :=
      (Set.toFinite _).measure_zero volume
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfin] with θ hθ
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hθ
    have h1 : z₀ * θ ≠ xlo := fun h => hθ.1 (by rw [← h]; field_simp)
    have h2 : z₀ * θ ≠ xhi := fun h => hθ.2 (by rw [← h]; field_simp)
    exact continuousAt_const.mul (continuousAt_const.mul
      (ContinuousAt.comp (g := ψ) (f := fun x => x * θ) (hA.ψ_continuousAt h1 h2)
        (continuousAt_id.mul continuousAt_const)))

/-- If `h` is within `ε` of `h(θ₀)` on `[a(z), b(z)]`, then `∫ h g(·|z)` is within `ε` of
`h(θ₀)`. -/
theorem abs_integral_condDens_sub_le {z : ℝ} (hz : 0 < shocksPi ψ g z) (h : ℝ →ᵇ ℝ)
    (θ₀ : ℝ) {ε : ℝ}
    (hh : ∀ θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z), |h θ - h θ₀| ≤ ε) :
    |(∫ θ, h θ * shocksCondDens ψ g z θ) - h θ₀| ≤ ε := by
  obtain ⟨hnn, h1, h0, -⟩ := hA.ex_17_8a hz
  have hcd : Integrable (shocksCondDens ψ g z) := (hA.integrable_joint_slice z).div_const _
  have hint : Integrable (fun θ => h θ * shocksCondDens ψ g z θ) :=
    hcd.bdd_mul (c := ‖h‖) h.continuous.aestronglyMeasurable
      (ae_of_all _ fun θ => h.norm_coe_le_norm θ)
  have e : (∫ θ, h θ * shocksCondDens ψ g z θ) - h θ₀ =
      ∫ θ, (h θ - h θ₀) * shocksCondDens ψ g z θ := by
    simp_rw [sub_mul]
    rw [integral_sub hint (hcd.const_mul _), integral_const_mul, h1, mul_one]
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hcd.const_mul ε) (ae_of_all _ fun θ => ?_)).trans
    (by rw [integral_const_mul, h1, mul_one])
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn θ)]
  by_cases hθ : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
  · exact mul_le_mul_of_nonneg_right (hh θ hθ) (hnn θ)
  · rw [h0 θ hθ]; simp

/-- **Exercise 17.8b** (p. 534), with the hypothesis `π > 0` on `int Z` (see `pi_pos`) and the
endpoint convention of `shocksCondLaw`: if `z_n → z` in `Z` then `G(·|z_n) → G(·|z)` weakly,
i.e. `z ↦ ∫ h dG(·|z)` is continuous on `Z` for every bounded continuous `h`. At interior points
this is dominated convergence; at `z̲` (resp. `z̄`) the support `[a(z), b(z)]` of `G(·|z)` lies in
`[x̲/z, θ̄]` (resp. `[θ̲, x̄/z]`), which shrinks to `{θ̄}` (resp. `{θ̲}`). -/
theorem ex_17_8b (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (h : ℝ →ᵇ ℝ) :
    ContinuousOn (fun z => ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z)
      (Icc (xlo / θhi) (xhi / θlo)) := by
  set zlo := xlo / θhi
  set zhi := xhi / θlo
  have hθhi : 0 < θhi := hA.θlo_pos.trans hA.θlo_lt
  have hzlo : 0 < zlo := div_pos hA.xlo_pos hθhi
  have hZ : zlo < zhi := div_lt_div₀ hA.xlo_lt hA.θlo_lt.le (hA.xlo_pos.trans hA.xlo_lt).le
    hA.θlo_pos
  -- the value of the integral on the interior
  have hint : ∀ z, zlo < z ∧ z < zhi → ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z =
      (∫ θ, h θ * (g θ * θ * ψ (z * θ))) / shocksPi ψ g z := fun z hz => by
    rw [hA.integral_condLaw hz (hπ z hz)]
    simp only [shocksCondDens, mul_div_assoc']
    exact integral_div _ _
  have hlo : ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g zlo = h θhi := by
    have h1 : ¬ (xlo / θhi < zlo ∧ zlo < xhi / θlo) := fun h => lt_irrefl _ h.1
    simp only [shocksCondLaw, h1, ↓reduceIte, le_refl, integral_dirac, zlo]
  have hhi : ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g zhi = h θlo := by
    have h1 : ¬ (xlo / θhi < zhi ∧ zhi < xhi / θlo) := fun h => lt_irrefl _ h.2
    have h2 : ¬ zhi ≤ xlo / θhi := not_le.mpr hZ
    simp only [shocksCondLaw, h1, h2, ↓reduceIte, integral_dirac]
  intro z₀ hz₀
  rcases eq_or_lt_of_le hz₀.1 with h1 | h1
  · -- the lower endpoint
    rw [← h1]
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hh⟩ := Metric.continuousAt_iff.1 (h.continuous.continuousAt (x := θhi))
      (ε / 2) (half_pos hε)
    have hc : ContinuousAt (fun z => xlo / z) zlo := continuousAt_const.div continuousAt_id
      hzlo.ne'
    obtain ⟨δ₂, hδ₂, hd⟩ := Metric.continuousAt_iff.1 hc δ₁ hδ₁
    refine ⟨min δ₂ (zhi - zlo), lt_min hδ₂ (sub_pos.2 hZ), fun z hz hdist => ?_⟩
    rw [hlo]
    rcases eq_or_lt_of_le hz.1 with h2 | h2
    · rw [← h2, hlo, dist_self]; exact hε
    have hzhi : z < zhi := by
      have := (abs_lt.1 (Real.dist_eq _ _ ▸ hdist)).2
      linarith [min_le_right δ₂ (zhi - zlo)]
    have hzz : zlo < z ∧ z < zhi := ⟨h2, hzhi⟩
    rw [Real.dist_eq, hA.integral_condLaw hzz (hπ z hzz)]
    have hxz : dist (xlo / z) (xlo / zlo) < δ₁ := hd (hdist.trans_le (min_le_left _ _))
    have hθ' : xlo / zlo = θhi := by simp only [zlo]; field_simp [hA.xlo_pos.ne']
    rw [hθ'] at hxz
    refine (hA.abs_integral_condDens_sub_le (hπ z hzz) h θhi
      fun θ hθ => ?_).trans_lt (half_lt_self hε)
    refine (le_of_lt (Real.dist_eq _ _ ▸ hh ?_))
    rw [Real.dist_eq, abs_lt]
    have ha : xlo / z ≤ θ := (le_max_left _ _).trans hθ.1
    have hb : θ ≤ θhi := hθ.2.trans (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at hxz
    constructor <;> linarith
  rcases eq_or_lt_of_le hz₀.2 with h3 | h3
  · -- the upper endpoint
    rw [h3]
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hh⟩ := Metric.continuousAt_iff.1 (h.continuous.continuousAt (x := θlo))
      (ε / 2) (half_pos hε)
    have hc : ContinuousAt (fun z => xhi / z) zhi := continuousAt_const.div continuousAt_id
      (hzlo.trans hZ).ne'
    obtain ⟨δ₂, hδ₂, hd⟩ := Metric.continuousAt_iff.1 hc δ₁ hδ₁
    refine ⟨min δ₂ (zhi - zlo), lt_min hδ₂ (sub_pos.2 hZ), fun z hz hdist => ?_⟩
    rw [hhi]
    rcases eq_or_lt_of_le hz.2 with h2 | h2
    · rw [h2, hhi, dist_self]; exact hε
    have hzlo' : zlo < z := by
      have := (abs_lt.1 (Real.dist_eq _ _ ▸ hdist)).1
      linarith [min_le_right δ₂ (zhi - zlo)]
    have hzz : zlo < z ∧ z < zhi := ⟨hzlo', h2⟩
    rw [Real.dist_eq, hA.integral_condLaw hzz (hπ z hzz)]
    have hxz : dist (xhi / z) (xhi / zhi) < δ₁ := hd (hdist.trans_le (min_le_left _ _))
    have hθ' : xhi / zhi = θlo := by
      simp only [zhi]; field_simp [(hA.xlo_pos.trans hA.xlo_lt).ne']
    rw [hθ'] at hxz
    refine (hA.abs_integral_condDens_sub_le (hπ z hzz) h θlo
      fun θ hθ => ?_).trans_lt (half_lt_self hε)
    refine (le_of_lt (Real.dist_eq _ _ ▸ hh ?_))
    rw [Real.dist_eq, abs_lt]
    have ha : θlo ≤ θ := (le_max_right _ _).trans hθ.1
    have hb : θ ≤ xhi / z := hθ.2.trans (min_le_left _ _)
    rw [Real.dist_eq, abs_lt] at hxz
    constructor <;> linarith
  · -- interior points
    have hzz : zlo < z₀ ∧ z₀ < zhi := ⟨h1, h3⟩
    have hk1 : ContinuousAt (fun z => ∫ θ, h θ * (g θ * θ * ψ (z * θ))) z₀ :=
      hA.continuousAt_slice h.continuous.measurable (C := ‖h‖) (fun θ => by
        rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm θ) (hzlo.trans h1)
    have hk2 : ContinuousAt (shocksPi ψ g) z₀ := by
      have := hA.continuousAt_slice (k := fun _ => 1) measurable_const (C := 1)
        (fun _ => by simp) (hzlo.trans h1)
      simp only [one_mul] at this
      exact this
    refine ((hk1.div hk2 (hπ z₀ hzz).ne').congr ?_).continuousWithinAt
    filter_upwards [Ioo_mem_nhds h1 h3] with z hz
    exact (hint z hz).symm

/-- Every `G(·|z)` is a probability measure (given `π > 0` on `int Z`). -/
theorem isProbabilityMeasure_condLaw' (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo →
    0 < shocksPi ψ g z) (z : ℝ) :
    IsProbabilityMeasure (shocksCondLaw xlo xhi θlo θhi ψ g z) := by
  by_cases h : xlo / θhi < z ∧ z < xhi / θlo
  · exact hA.isProbabilityMeasure_condLaw h (hπ z h)
  · simp only [shocksCondLaw, h, ↓reduceIte]
    split_ifs <;> exact Measure.dirac.isProbabilityMeasure

end ShocksAssumption17_5

/-! ### Assumption 17.6: uniform shocks -/

/-- The uniform density on `[a, b]`. -/
noncomputable def shocksUnif (a b : ℝ) : ℝ → ℝ := (Icc a b).indicator fun _ => (b - a)⁻¹

/-- `∫_{[a, b]} θ dθ = (b² − a²)/2`. -/
theorem shocks_setIntegral_Icc_id {a b : ℝ} (hab : a ≤ b) :
    ∫ θ in Icc a b, θ = (b ^ 2 - a ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_id]

/-- **Assumption 17.6** (p. 536) is compatible with Assumption 17.5: uniform `Ψ` and `G`
satisfy Assumption 17.5. -/
theorem shocksUnif_assumption17_5 {xlo xhi θlo θhi : ℝ} (hx0 : 0 < xlo) (hx : xlo < xhi)
    (hθ0 : 0 < θlo) (hθ : θlo < θhi) (hθ2 : θhi < 2) :
    ShocksAssumption17_5 xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) := by
  have key : ∀ a b : ℝ, a < b → (∀ x, 0 ≤ shocksUnif a b x) ∧
      (∀ x ∉ Icc a b, shocksUnif a b x = 0) ∧ ContinuousOn (shocksUnif a b) (Icc a b) ∧
      ∫ x, shocksUnif a b x = 1 := fun a b hab => by
    refine ⟨fun x => indicator_nonneg (fun _ _ => (inv_pos.2 (sub_pos.2 hab)).le) x,
      fun x hx => indicator_of_notMem hx _,
      continuousOn_const.congr fun x hx => indicator_of_mem hx _, ?_⟩
    rw [shocksUnif, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
      Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_pos.2 hab).le,
      mul_inv_cancel₀ (sub_pos.2 hab).ne']
  obtain ⟨a1, a2, a3, a4⟩ := key xlo xhi hx
  obtain ⟨b1, b2, b3, b4⟩ := key θlo θhi hθ
  exact ⟨hx0, hx, hθ0, hθ, hθ2, a1, b1, a2, b2, a3, b3, a4, b4⟩

/-- Under Assumption 17.6 the joint density of `(θ, z)` is `θ/((θ̄ − θ̲)(x̄ − x̲))` on
`[a(z), b(z)]` (`z > 0`). -/
theorem shocksUnif_joint {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    shocksUnif θlo θhi θ * θ * shocksUnif xlo xhi (z * θ) =
      (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => (θhi - θlo)⁻¹ * (xhi - xlo)⁻¹ * θ) θ := by
  by_cases h : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
  · obtain ⟨h1, h2⟩ := (mem_Icc_shocksA_shocksB_iff hz).2 h
    rw [indicator_of_mem h, shocksUnif, shocksUnif, indicator_of_mem h1, indicator_of_mem h2]
    ring
  · rw [indicator_of_notMem h]
    rw [← mem_Icc_shocksA_shocksB_iff hz, not_and_or] at h
    rcases h with h | h
    · simp [shocksUnif, indicator_of_notMem h]
    · simp [shocksUnif, indicator_of_notMem h]

/-- Under Assumption 17.6, `π(z) = (b² − a²)/(2(θ̄ − θ̲)(x̄ − x̲))` where `a(z) ≤ b(z)`. -/
theorem shocksUnif_pi {z : ℝ} (hz : 0 < z) (hab : shocksA xlo θlo z ≤ shocksB xhi θhi z) :
    shocksPi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z =
      (θhi - θlo)⁻¹ * (xhi - xlo)⁻¹ *
        ((shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2) / 2) := by
  simp only [shocksPi]
  simp_rw [shocksUnif_joint hz]
  rw [integral_indicator measurableSet_Icc, integral_const_mul, shocks_setIntegral_Icc_id hab]

/-- **Exercise 17.12, corrected** (p. 536). Under Assumptions 17.5 and 17.6, for `z ∈ int Z`
the conditional density of `θ` given `z` is `2θ/(b(z)² − a(z)²)` on `[a(z), b(z)]` (and `0`
elsewhere): **not** uniform. -/
theorem ex_17_12 (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi) {z : ℝ}
    (hzZ : xlo / θhi < z ∧ z < xhi / θlo) (θ : ℝ) :
    shocksCondDens (shocksUnif xlo xhi) (shocksUnif θlo θhi) z θ =
      (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => 2 * θ / (shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2)) θ := by
  obtain ⟨hz0, hab⟩ := shocksA_lt_shocksB hx0 hx hθ0 hθ hzZ
  have ha0 : 0 < shocksA xlo θlo z := hθ0.trans_le (le_max_right _ _)
  have hd : 0 < shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2 := by nlinarith
  rw [shocksCondDens, shocksUnif_joint hz0, shocksUnif_pi hz0 hab.le]
  by_cases h : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
  · rw [indicator_of_mem h, indicator_of_mem h]
    have h1 : 0 < θhi - θlo := sub_pos.2 hθ
    have h2 : 0 < xhi - xlo := sub_pos.2 hx
    field_simp
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_div]

/-! ### The example economy `x ~ U[1, 2]`, `θ ~ U[1, 3/2]` -/

/-- The example economy satisfies Assumptions 17.5 and 17.6. -/
theorem shocksEx_assumption :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) :=
  shocksUnif_assumption17_5 one_pos one_lt_two one_pos (by norm_num) (by norm_num)

/-- In the example, `a(z) = 1` and `b(z) = 3/2` for `z ∈ [1, 4/3]`. -/
theorem shocksEx_ab {z : ℝ} (hz : z ∈ Icc (1 : ℝ) (4 / 3)) :
    shocksA 1 1 z = 1 ∧ shocksB 2 (3 / 2) z = 3 / 2 := by
  have hz0 : 0 < z := one_pos.trans_le hz.1
  refine ⟨max_eq_right ?_, min_eq_right ?_⟩
  · rw [div_le_one hz0]; exact hz.1
  · rw [le_div_iff₀ hz0]; linarith [hz.2]

/-- In the example, `π(z) = 5/4` for `z ∈ [1, 4/3]`. -/
theorem shocksEx_pi {z : ℝ} (hz : z ∈ Icc (1 : ℝ) (4 / 3)) :
    shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z = 5 / 4 := by
  have hz0 : 0 < z := one_pos.trans_le hz.1
  obtain ⟨ha, hb⟩ := shocksEx_ab hz
  rw [shocksUnif_pi hz0 (by rw [ha, hb]; norm_num), ha, hb]
  norm_num

/-- **Correction (manual, Exercise 17.8a).** The manual's density `g(θ)ψ(θz)/π(z)` omits the
Jacobian factor `θ` and does not integrate to `1`: in the example at `z = 1` it integrates to
`4/5`. -/
theorem ex_17_8a_manual_counterexample :
    ∫ θ, shocksUnif 1 (3 / 2) θ * shocksUnif 1 2 (θ * 1) /
      shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) 1 = 4 / 5 := by
  rw [shocksEx_pi ⟨le_rfl, by norm_num⟩, integral_div]
  have e : (fun θ : ℝ => shocksUnif 1 (3 / 2) θ * shocksUnif 1 2 (θ * 1)) =
      (Icc (1 : ℝ) (3 / 2)).indicator fun _ => 2 := by
    ext θ
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · have h' : θ * 1 ∈ Icc (1 : ℝ) 2 := by rw [mul_one]; exact ⟨h.1, by linarith [h.2]⟩
      simp only [shocksUnif, indicator_of_mem h, indicator_of_mem h']
      norm_num
    · simp [shocksUnif, indicator_of_notMem h]
  rw [e, integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- **Correction (Exercise 17.12 is false).** The book's claim, that `G(·|z)` is the uniform
distribution on `[a(z), b(z)]`, fails in the example: the uniform family does not disintegrate
the joint law of `(θ, z)`. With `h(θ, z) = θ·1{z ∈ [1, 4/3]}` (on `θ ∈ [1, 3/2]`) the true
expectation is `19/36` while the uniform family gives `25/48`. -/
theorem ex_17_12_counterexample : ¬ ∀ h : ℝ × ℝ → ℝ, Measurable h → (∃ C, ∀ p, |h p| ≤ C) →
    ∫ θ, shocksUnif 1 (3 / 2) θ * ∫ x, shocksUnif 1 2 x * h (θ, x / θ) =
      ∫ z, shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z *
        ((shocksB 2 (3 / 2) z - shocksA 1 1 z)⁻¹ *
          ∫ θ in Icc (shocksA 1 1 z) (shocksB 2 (3 / 2) z), h (θ, z)) := by
  intro H
  set h₀ : ℝ × ℝ → ℝ := fun p =>
    (Icc (1 : ℝ) (4 / 3)).indicator (fun _ => 1) p.2 * (Icc (1 : ℝ) (3 / 2)).indicator id p.1
  have hm : Measurable h₀ :=
    ((measurable_const.indicator measurableSet_Icc).comp measurable_snd).mul
      ((measurable_id.indicator measurableSet_Icc).comp measurable_fst)
  have hb : ∀ p, |h₀ p| ≤ 3 / 2 := fun p => by
    simp only [h₀]
    by_cases h1 : p.2 ∈ Icc (1 : ℝ) (4 / 3)
    · by_cases h2 : p.1 ∈ Icc (1 : ℝ) (3 / 2)
      · rw [indicator_of_mem h1, indicator_of_mem h2, one_mul, id, abs_of_pos
          (one_pos.trans_le h2.1)]
        exact h2.2
      · rw [indicator_of_notMem h2]; norm_num
    · rw [indicator_of_notMem h1]; norm_num
  have key := H h₀ hm ⟨3 / 2, hb⟩
  rw [shocksEx_assumption.joint hm hb] at key
  have L : ∀ z, ∫ θ, h₀ (θ, z) * (shocksUnif 1 (3 / 2) θ * θ * shocksUnif 1 2 (z * θ)) =
      (Icc (1 : ℝ) (4 / 3)).indicator (fun _ => 19 / 12) z := fun z => by
    by_cases hz : z ∈ Icc (1 : ℝ) (4 / 3)
    · have hz0 : 0 < z := one_pos.trans_le hz.1
      obtain ⟨ha, hb'⟩ := shocksEx_ab hz
      have e : (fun θ => h₀ (θ, z) * (shocksUnif 1 (3 / 2) θ * θ * shocksUnif 1 2 (z * θ))) =
          (Icc (1 : ℝ) (3 / 2)).indicator fun θ => 2 * θ ^ 2 := by
        ext θ
        rw [shocksUnif_joint hz0, ha, hb']
        by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
        · simp only [h₀, indicator_of_mem hz, indicator_of_mem h, id]
          norm_num
          ring
        · simp [h₀, indicator_of_notMem h]
      rw [e, indicator_of_mem hz, integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    · simp [h₀, indicator_of_notMem hz]
  have R : ∀ z, shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z *
      ((shocksB 2 (3 / 2) z - shocksA 1 1 z)⁻¹ *
        ∫ θ in Icc (shocksA 1 1 z) (shocksB 2 (3 / 2) z), h₀ (θ, z)) =
      (Icc (1 : ℝ) (4 / 3)).indicator (fun _ => 25 / 16) z := fun z => by
    by_cases hz : z ∈ Icc (1 : ℝ) (4 / 3)
    · obtain ⟨ha, hb'⟩ := shocksEx_ab hz
      rw [shocksEx_pi hz, ha, hb', indicator_of_mem hz,
        setIntegral_congr_fun measurableSet_Icc (g := id) fun θ hθ => by
          simp [h₀, indicator_of_mem hz, indicator_of_mem hθ]]
      rw [show (fun x : ℝ => id x) = fun x => x from rfl, shocks_setIntegral_Icc_id (by norm_num)]
      norm_num
    · simp [h₀, indicator_of_notMem hz]
  simp_rw [L, R] at key
  rw [integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
    setIntegral_const, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by norm_num)] at key
  norm_num at key

/-- A property holding a.e. on `[p, q]` holds at some point of every measurable `S ⊆ [p, q]` of
positive measure. -/
theorem shocks_exists_mem_of_ae_restrict_Icc {p q : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ x ∂volume.restrict (Icc p q), P x) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Icc p q) (hpos : volume S ≠ 0) : ∃ x ∈ S, P x := by
  have h' : ∀ᵐ x ∂volume.restrict S, P x := ae_restrict_of_ae_restrict_of_subset hS h
  have hmem : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hSm
  have : (ae (volume.restrict S)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
  obtain ⟨x, hx1, hx2⟩ := (h'.and hmem).exists
  exact ⟨x, hx2, hx1⟩

/-- In the example, at `z = 4/5` the conditional density is `(32/11) θ` on `[5/4, 3/2]`. -/
theorem shocksEx_condDens_four_fifths (θ : ℝ) :
    shocksCondDens (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (4 / 5) θ =
      (Icc (5 / 4 : ℝ) (3 / 2)).indicator (fun θ => 32 / 11 * θ) θ := by
  rw [ex_17_12 one_pos one_lt_two one_pos (by norm_num) (by norm_num) θ]
  have ha : shocksA 1 1 (4 / 5) = 5 / 4 := by norm_num [shocksA]
  have hb : shocksB 2 (3 / 2) (4 / 5) = 3 / 2 := by norm_num [shocksB]
  rw [ha, hb]
  congr 1
  ext θ
  ring

/-- **Correction (Exercise 17.8a, "continuous density").** Under Assumption 17.5 the densities are
continuous on `X` and `Θ` only (Assumption 17.6, uniform densities, is the book's own example),
and then `G(·|z)` need **not** have a density continuous on `Θ`: in the example, at
`z = 4/5 ∈ int Z`, `g(·|z)` jumps from `0` to `40/11` at `θ = a(z) = 5/4 ∈ int Θ`, and no
function continuous on `Θ` agrees with it a.e. (The density is continuous on `[a(z), b(z)]`,
`ex_17_8a`.) -/
theorem ex_17_8a_continuity_counterexample : ¬ ∃ c : ℝ → ℝ, ContinuousOn c (Icc 1 (3 / 2)) ∧
    ∀ᵐ θ ∂volume.restrict (Icc 1 (3 / 2)),
      c θ = shocksCondDens (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (4 / 5) θ := by
  rintro ⟨c, hc, hae⟩
  have hcont : ContinuousAt c (5 / 4) :=
    hc.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousAt_iff.1 hcont (20 / 11) (by norm_num)
  set δ' := min δ (1 / 4)
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' ≤ 1 / 4 := min_le_right _ _
  obtain ⟨θ₁, hθ₁, e₁⟩ := shocks_exists_mem_of_ae_restrict_Icc hae (S := Ioo (5 / 4 - δ') (5 / 4))
    measurableSet_Ioo (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    (by simp [hδ'])
  obtain ⟨θ₂, hθ₂, e₂⟩ := shocks_exists_mem_of_ae_restrict_Icc hae (S := Ioo (5 / 4) (5 / 4 + δ'))
    measurableSet_Ioo (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    (by simp [hδ'])
  rw [shocksEx_condDens_four_fifths, indicator_of_notMem (fun h => by linarith [h.1, hθ₁.2])]
    at e₁
  rw [shocksEx_condDens_four_fifths, indicator_of_mem
    (show θ₂ ∈ Icc (5 / 4 : ℝ) (3 / 2) from ⟨hθ₂.1.le, by linarith [hθ₂.2]⟩)] at e₂
  have d₁ := hcδ (x := θ₁) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hθ₁.1, hθ₁.2, min_le_left δ (1 / 4)])
  have d₂ := hcδ (x := θ₂) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hθ₂.1, hθ₂.2, min_le_left δ (1 / 4)])
  rw [Real.dist_eq, e₁, abs_lt] at d₁
  rw [Real.dist_eq, e₂, abs_lt] at d₂
  linarith [hθ₂.1]

/-- The unnormalised density of the example with `π = 0` on part of `int Z`. -/
noncomputable def shocksExG0 (θ : ℝ) : ℝ :=
  (Icc (1 : ℝ) (3 / 2)).indicator (fun θ => max 0 ((θ - 1) * (5 / 4 - θ))) θ

/-- A continuous density on `Θ = [1, 3/2]` vanishing on `[5/4, 3/2]`. -/
noncomputable def shocksExG (θ : ℝ) : ℝ := shocksExG0 θ / ∫ t, shocksExG0 t

/-- The normalising constant of `shocksExG` is positive. -/
theorem shocksExG0_integral_pos : 0 < ∫ t, shocksExG0 t := by
  have hc : ContinuousOn (fun θ : ℝ => max 0 ((θ - 1) * (5 / 4 - θ))) (Icc 1 (3 / 2)) :=
    Continuous.continuousOn (by fun_prop)
  have hint : Integrable shocksExG0 :=
    (hc.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  refine (integral_pos_iff_support_of_nonneg (fun θ => indicator_nonneg
    (fun _ _ => le_max_left _ _) θ) hint).2 ?_
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo 1 (5 / 4)) fun θ hθ => ?_)
  · simp only [Real.volume_Ioo]
    norm_num
  · rw [Function.mem_support]
    change (Icc (1 : ℝ) (3 / 2)).indicator _ θ ≠ 0
    rw [indicator_of_mem
      (show θ ∈ Icc (1 : ℝ) (3 / 2) from ⟨hθ.1.le, by linarith [hθ.2]⟩)]
    exact (lt_max_of_lt_right (mul_pos (by linarith [hθ.1]) (by linarith [hθ.2]))).ne'

/-- **Correction (Exercise 17.8a, missing hypothesis `π(z) > 0`).** Assumption 17.5 allows `π`
to vanish at interior points of `Z`, where the formula for `g(·|z)` is `0/0` and `G(·|z)` is not
determined by the joint law: with `x ~ U[1, 2]` and `g ∝ max{0, (θ − 1)(5/4 − θ)}` on
`Θ = [1, 3/2]`, the joint density `g(θ) θ ψ(zθ)` vanishes identically at `z = 3/4 ∈ int Z`. -/
theorem ex_17_8a_pi_zero_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExG ∧
      (1 / (3 / 2) : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 2 / 1 ∧
      (∀ θ, shocksExG θ * θ * shocksUnif 1 2 (3 / 4 * θ) = 0) ∧
      shocksPi (shocksUnif 1 2) shocksExG (3 / 4) = 0 := by
  have hpos := shocksExG0_integral_pos
  have hU := shocksUnif_assumption17_5 (xlo := 1) (xhi := 2) (θlo := 1) (θhi := 3 / 2) one_pos
    one_lt_two one_pos (by norm_num) (by norm_num)
  have hzero : ∀ θ, shocksExG θ * θ * shocksUnif 1 2 (3 / 4 * θ) = 0 := fun θ => by
    by_cases h : θ ∈ Ioo (1 : ℝ) (5 / 4)
    · have : 3 / 4 * θ ∉ Icc (1 : ℝ) 2 := fun h' => by linarith [h'.1, h.2]
      simp [shocksUnif, indicator_of_notMem this]
    · have : shocksExG0 θ = 0 := by
        by_cases h' : θ ∈ Icc (1 : ℝ) (3 / 2)
        · simp only [shocksExG0, indicator_of_mem h']
          refine max_eq_left ?_
          simp only [mem_Ioo, not_and_or, not_lt] at h
          rcases h with h | h
          · nlinarith [h'.1]
          · nlinarith [h'.2]
        · simp [shocksExG0, indicator_of_notMem h']
      simp [shocksExG, this]
  refine ⟨⟨one_pos, one_lt_two, one_pos, by norm_num, by norm_num, hU.ψ_nonneg,
    fun θ => div_nonneg (indicator_nonneg (fun _ _ => le_max_left _ _) θ) hpos.le,
    hU.ψ_zero, fun θ hθ => by simp [shocksExG, shocksExG0, indicator_of_notMem hθ],
    hU.ψ_cont, ?_, hU.ψ_int, ?_⟩, by norm_num, by norm_num, hzero, ?_⟩
  · refine ContinuousOn.div_const ?_ _
    refine (Continuous.continuousOn (f := fun θ : ℝ => max 0 ((θ - 1) * (5 / 4 - θ)))
      (by fun_prop)).congr fun θ hθ => ?_
    simp [shocksExG0, indicator_of_mem hθ]
  · simp only [shocksExG]
    rw [integral_div, div_self hpos.ne']
  · simp only [shocksPi, hzero, integral_zero]

/-! ### Exercise 17.10 -/

/-- In the example, `π > 0` on `int Z`. -/
theorem shocksEx_pi_pos (z : ℝ) (hz : 1 / (3 / 2) < z ∧ z < 2 / 1) :
    0 < shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z :=
  shocksEx_assumption.pi_pos (fun x hx => by rw [shocksUnif, indicator_of_mem hx]; norm_num)
    (fun θ hθ => by rw [shocksUnif, indicator_of_mem hθ]; norm_num) hz

/-- The sequence `z_n = 2/3 + 1/(3(n + 1)) ↓ z̲ = 2/3` of Exercise 17.10. -/
noncomputable def shocksExSeq (n : ℕ) : ℝ := 2 / 3 + 1 / ((n : ℝ) + 1) / 3

/-- `z_n ∈ int Z = (2/3, 2)`. -/
theorem shocksExSeq_mem (n : ℕ) : 1 / (3 / 2) < shocksExSeq n ∧ shocksExSeq n < 2 / 1 := by
  have h1 : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  have h2 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg :
    (0 : ℝ) ≤ n)])
  simp only [shocksExSeq, one_div]
  constructor <;> norm_num <;> linarith

/-- `z_n → 2/3`. -/
theorem shocksExSeq_tendsto : Tendsto shocksExSeq atTop (𝓝 (2 / 3)) := by
  have := (tendsto_const_nhds (x := (2 / 3 : ℝ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 3)
  change Tendsto (fun n : ℕ => 2 / 3 + 1 / ((n : ℝ) + 1) / 3) atTop (𝓝 (2 / 3))
  simpa using this

/-- In the example, `G(·|z_n)` gives mass `0` to every set on which its density vanishes. -/
theorem shocksEx_condLaw_seq_eq_zero (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : ∀ θ ∈ s, θ ∉ Icc (shocksA 1 1 (shocksExSeq n)) (shocksB 2 (3 / 2) (shocksExSeq n))) :
    shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (shocksExSeq n) s = 0 := by
  have hm := shocksExSeq_mem n
  obtain ⟨-, -, hz, -⟩ := shocksEx_assumption.ex_17_8a (shocksEx_pi_pos _ hm)
  simp only [shocksCondLaw, hm, and_self, ↓reduceIte]
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 0) fun θ hθ => by
    rw [hz θ (h0 θ hθ), ENNReal.ofReal_zero]]
  simp

/-- **Exercise 17.10** (p. 536; no answer in the manual). With `x ~ U[1, 2]`, `θ ~ U[1, 3/2]`
(so `Z = [2/3, 2]`) and `z_n ↓ z̲ = 2/3`: `G(·|z_n) → G(·|z̲) = δ_{3/2}` weakly
(Exercise 17.8b), but `‖G(·|z_n) − G(·|z̲)‖_TV ≥ 1` for all `n` (each `G(·|z_n)` has a density, so
gives `{3/2}` mass `0`); indeed `G(·|z_n)` has **no** limit in total variation. So the analogue of
Assumption 17.3 fails. -/
theorem ex_17_10 :
    (∀ n, shocksExSeq n ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1)) ∧
      Tendsto shocksExSeq atTop (𝓝 (1 / (3 / 2))) ∧
      (∀ h : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ θ, h θ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2)
        (shocksUnif 1 (3 / 2)) (shocksExSeq n)) atTop
        (𝓝 (∫ θ, h θ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
          (1 / (3 / 2))))) ∧
      (∀ n, 1 ≤ fpTVNorm (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
        (shocksExSeq n)) (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
          (1 / (3 / 2)))) ∧
      ¬ ∃ ν₀ : Measure ℝ, IsFiniteMeasure ν₀ ∧ Tendsto (fun n => fpTVNorm (shocksCondLaw 1 2 1
        (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (shocksExSeq n)) ν₀) atTop (𝓝 0) := by
  set ν := shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
  have hA := shocksEx_assumption
  have hprob : ∀ z, IsProbabilityMeasure (ν z) := hA.isProbabilityMeasure_condLaw' shocksEx_pi_pos
  have hmem : ∀ n, shocksExSeq n ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1) := fun n =>
    ⟨(shocksExSeq_mem n).1.le, (shocksExSeq_mem n).2.le⟩
  have hlim : Tendsto shocksExSeq atTop (𝓝 (1 / (3 / 2))) := by
    convert shocksExSeq_tendsto using 2; norm_num
  have hνlo : ν (1 / (3 / 2)) = Measure.dirac (3 / 2) := by
    have h1 : ¬ ((1 : ℝ) / (3 / 2) < 1 / (3 / 2) ∧ (1 : ℝ) / (3 / 2) < 2 / 1) :=
      fun h => lt_irrefl _ h.1
    simp only [ν, shocksCondLaw, h1, ↓reduceIte, le_refl]
  have hsing : ∀ n, ν (shocksExSeq n) {3 / 2} = 0 := fun n => by
    simp only [ν, shocksCondLaw, shocksExSeq_mem n, and_self, ↓reduceIte]
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  refine ⟨hmem, hlim, fun h => ?_, fun n => ?_, ?_⟩
  · have hc := hA.ex_17_8b shocksEx_pi_pos h
    exact (hc _ ⟨le_rfl, by norm_num⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
  · have := fp_le_tvNorm_pair (ν (shocksExSeq n)) (ν (1 / (3 / 2)))
      (measurableSet_singleton (3 / 2 : ℝ))
    rw [Measure.real, Measure.real, hsing n, hνlo,
      Measure.dirac_apply_of_mem (mem_singleton _)] at this
    simp only [ENNReal.toReal_zero, ENNReal.toReal_one, zero_sub, abs_neg, abs_one] at this
    rw [hνlo]
    linarith [abs_nonneg ((ν (shocksExSeq n)).real {3 / 2}ᶜ -
      (Measure.dirac (3 / 2 : ℝ)).real {3 / 2}ᶜ)]
  · rintro ⟨ν₀, hν₀, hTV⟩
    -- setwise convergence
    have hset : ∀ s, MeasurableSet s →
        Tendsto (fun n => (ν (shocksExSeq n)).real s) atTop (𝓝 (ν₀.real s)) := fun s hs => by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hTV
      rw [Real.norm_eq_abs]
      have := fp_le_tvNorm_pair (ν (shocksExSeq n)) ν₀ hs
      linarith [abs_nonneg ((ν (shocksExSeq n)).real sᶜ - ν₀.real sᶜ)]
    have hzero : ∀ s, MeasurableSet s → (∀ᶠ n in atTop, ν (shocksExSeq n) s = 0) →
        ν₀ s = 0 := fun s hs hev => by
      have h1 := hset s hs
      have h2 : Tendsto (fun n => (ν (shocksExSeq n)).real s) atTop (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun n hn => by simp [measureReal_def, hn])
      have := tendsto_nhds_unique h1 h2
      rwa [measureReal_eq_zero_iff] at this
    have hone : ν₀.real univ = 1 := by
      have h1 := hset univ MeasurableSet.univ
      simp only [probReal_univ] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hS : ν₀ {3 / 2} = 0 := hzero _ (measurableSet_singleton _)
      (Eventually.of_forall hsing)
    have hI : ν₀ (Ioi (3 / 2)) = 0 := hzero _ measurableSet_Ioi (Eventually.of_forall fun n =>
      shocksEx_condLaw_seq_eq_zero n measurableSet_Ioi fun θ hθ h => by
        linarith [h.2.trans (min_le_right _ _), mem_Ioi.1 hθ])
    have hinv : Tendsto (fun n => 1 / shocksExSeq n) atTop (𝓝 (3 / 2)) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).div shocksExSeq_tendsto (by norm_num)
      convert this using 2; norm_num
    have hL : ∀ k : ℕ, ν₀ (Iio (3 / 2 - 1 / ((k : ℝ) + 1))) = 0 := fun k => by
      have hk : 3 / 2 - 1 / ((k : ℝ) + 1) < 3 / 2 := by
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      refine hzero _ measurableSet_Iio ?_
      filter_upwards [hinv.eventually (eventually_gt_nhds hk)] with n hn
      exact shocksEx_condLaw_seq_eq_zero n measurableSet_Iio fun θ hθ h => by
        linarith [(le_max_left _ _).trans h.1, mem_Iio.1 hθ]
    have hIio : ν₀ (Iio (3 / 2)) = 0 := by
      have : Iio (3 / 2 : ℝ) = ⋃ k : ℕ, Iio (3 / 2 - 1 / ((k : ℝ) + 1)) := by
        ext θ
        simp only [mem_Iio, mem_iUnion]
        constructor
        · intro hθ
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hθ)
          exact ⟨k, by linarith⟩
        · rintro ⟨k, hk⟩
          have : 0 < 1 / ((k : ℝ) + 1) := by positivity
          linarith
      rw [this]
      exact measure_iUnion_null hL
    have huniv : ν₀ univ = 0 := by
      have : (univ : Set ℝ) = Iio (3 / 2) ∪ {3 / 2} ∪ Ioi (3 / 2) := by
        ext θ
        simp only [mem_univ, mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, true_iff]
        rcases lt_trichotomy θ (3 / 2) with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      rw [this]
      exact measure_union_null (measure_union_null hIio hS) hI
    rw [measureReal_def, huniv] at hone
    norm_num at hone

/-! ### The NOTE on p. 533 -/

/-- **What p. 533 proves.** If labour depends on the state only through the price
(`n = N ∘ p`, from (1)) and the market clears ((2): `n p = x/θ`), then equal prices imply equal
ratios: `z = x/θ` is a function of the price. -/
theorem p533_ratio_of_price {S : Type*} (p n z : S → ℝ) (N : ℝ → ℝ) (hn : ∀ s, n s = N (p s))
    (h2 : ∀ s, n s * p s = z s) {s s' : S} (hp : p s = p s') : z s = z s' := by
  rw [← h2, ← h2, hn, hn, hp]

/-- **Correction (p. 533).** The converse, "any equilibrium price is of the form `ρ(x/θ)`", does
not follow from those premises: on `X × Θ = [1, 2] × [1, 3/2]`,
`p(x, θ) = x/θ + 10·1{θ > 5/4}` and `n = (x/θ)/p` satisfy `n = N ∘ p` and (2), yet `p` is not a
function of `x/θ` (the price reveals more than `z`). (A continuous equilibrium price is always a
function of `x/θ`, `islands_eqm_price_of_ratio`; whether a discontinuous `p` such as this one can
also satisfy (1) is not settled.) -/
theorem p533_counterexample : ∃ (p n : ℝ × ℝ → ℝ) (N : ℝ → ℝ),
    (∀ s ∈ Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2), 0 < p s ∧ 0 < n s ∧ n s = N (p s) ∧
      n s * p s = s.1 / s.2) ∧
    ¬ ∃ ρ : ℝ → ℝ, ∀ s ∈ Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2), p s = ρ (s.1 / s.2) := by
  classical
  set p : ℝ × ℝ → ℝ := fun s => s.1 / s.2 + if 5 / 4 < s.2 then 10 else 0
  set N : ℝ → ℝ := fun q => (q - if 5 < q then 10 else 0) / q
  refine ⟨p, fun s => N (p s), N, fun s hs => ?_, ?_⟩
  · have hx : 0 < s.1 := one_pos.trans_le hs.1.1
    have hθ : 0 < s.2 := one_pos.trans_le hs.2.1
    have hz : s.1 / s.2 ≤ 2 := by
      rw [div_le_iff₀ hθ]; nlinarith [hs.1.2, hs.2.1]
    have hz0 : 0 < s.1 / s.2 := div_pos hx hθ
    have hp0 : 0 < p s := by simp only [p]; split_ifs <;> linarith
    have hN : N (p s) = s.1 / s.2 / p s := by
      simp only [N, p]
      split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | ring
    refine ⟨hp0, show 0 < N (p s) by rw [hN]; positivity, rfl,
      show N (p s) * p s = _ by rw [hN, div_mul_cancel₀ _ hp0.ne']⟩
  · rintro ⟨ρ, hρ⟩
    have h1 := hρ (6 / 5, 6 / 5) ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    have h2 := hρ (7 / 5, 7 / 5) ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    simp only [p] at h1 h2
    norm_num at h1 h2
    rw [← h1] at h2
    norm_num at h2

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: Proposition 6 by the contraction mapping theorem

SLP §17.6, pp. 534–535: the operator (4) and Proposition 6 (Exercise 17.9). The OLG primitives
(`Assumption17_1H`, the repaired `Assumption17_1VR` and `Assumption17_2R`, `olgZeta`, `olgPhi`,
`olgZetaInv`, the kernel `olgG` and its bounds) are from `FixedPointArguments.OLGModel` and
`FixedPointArguments.OLGProposition2`; the information structure from
`FixedPointArguments.ShocksModel`.

**The operator (4).** By the NOTE on p. 535, `∫_Z ∫_Θ h(θ′, z′) G(dθ′|z′) π(dz′)` is the expectation
of `h` under the joint law `μ` of `(θ′, z′)`, so (4) reads
`(Tf)(z) = ∫ φ_f(θ̃) G(dθ̃|z)`, `φ_f(θ̃) = ∫ φ[(θ′/θ̃) ζ⁻¹(f(z′))] dμ(θ′, z′)`
(`shocksOpT`, `shocksPhiF`, `shocksIntegrand`). Here `Z` is any compact metric space, `μ` any
probability measure on `ℝ × Z` and `ν z = G(·|z)` any weakly continuous family of probability
measures on `ℝ`; `θ′`, `θ̃` are clamped to `Θ` (`shocksClamp`), which changes nothing on the
supports. The ratio `θ′/θ̃ ∈ [θ̲/θ̄, θ̄/θ̲]` (`shocksRatio_mem`) plays the role of `x′` in §17.2, so
the integrand is the OLG kernel `olgG` at `x′ = θ′/θ̃` (`shocksIntegrand_eq_olgG`).

* `ShocksBounds`: the standing hypotheses, with `l₀` such that `H'(l₀) < C = (θ̲/θ̄)V'((θ̄/θ̲)L)`
  (the manual's `C`); `shocksBounds_exists`.
* Step 1 of Exercise 17.9 (and Steps 1–2 of Exercise 17.11): `ShocksBounds.integrand_ge`,
  `ShocksBounds.exists_integrand_le`, `ShocksBounds.opT_mem` (`T` maps continuous `f ≥ ζ(l)` to
  continuous `ζ(l) ≤ Tf ≤ B`; continuity of `Tf` is the weak continuity of `G(·|z)`).
* **Exercise 17.9** (`ShocksBounds.ex_17_9`, p. 535): `T̂g = ln T(e^g)` is a contraction of
  modulus `β` (mean value theorem: `ShocksBounds.abs_log_integrand_sub_le`; integrated:
  `ShocksBounds.opT_exp_le`); `ShocksBounds.unique_fixedPoint_ge`.
* **Proposition 6** (`proposition_6`, p. 535), corrected: exactly one strictly positive continuous
  fixed point; `proposition_6_islands`: the same for the islands model with `μ` the joint law
  (`shocksJointLaw`) and `G(·|z)` the conditional law of `FixedPointArguments.ShocksModel`.

**Correction (Proposition 6, "a unique fixed point in `C(Z)`").** `T0 = 0`
(`shocksOpT_zero`, `proposition_6_zero_fixedPoint`), so `T` has two fixed points in `C(Z)`
(`proposition_6_counterexample`); `T` is also not defined on functions with negative values.
The proof gives uniqueness among strictly positive (equivalently, by compactness, bounded away
from zero) fixed points, via the sets `[ζ(l), ∞)`, `l ↓ 0`, as in `proposition_2`.

**Correction (Proposition 6, hypotheses).** Assumption 17.2 contradicts Assumption 17.1
(`assumption17_2_counterexample`, `assumption17_2R_inconsistent` in
`FixedPointArguments.OLGProposition2`), so Proposition 6 as stated is vacuous; it is proved here
under the repaired assumptions. The continuity of `Tf` needs Exercise 17.8b, including the
endpoints of `Z` (the convention `G(·|z̲) = δ_{θ̄}`, `G(·|z̄) = δ_{θ̲}`) and `π > 0` on `int Z`.

**Correction (manual, Exercise 17.9).** The final inequalities drop `β`
("`(T̂g)(z) − (T̂h)(z) ≤ β sup{g(z) − h(z)} ≤ ‖g − h‖`") and write `sup(g − h)` for
`sup|g − h|`; the mean value theorem is applied at `z′`. The manual's weights `w` are replaced
by the equivalent pointwise bound `φ[⋯e^{g}⋯] ≤ e^{β‖g − h‖} φ[⋯e^{h}⋯]`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-- Clamping to `Θ = [θ̲, θ̄]`: `t ↦ max θ̲ (min t θ̄)`. -/
def shocksClamp (θlo θhi t : ℝ) : ℝ := max θlo (min t θhi)

variable {θlo θhi : ℝ}

/-- The clamp lands in `Θ`. -/
theorem shocksClamp_mem (hθ : θlo ≤ θhi) (t : ℝ) : shocksClamp θlo θhi t ∈ Icc θlo θhi :=
  ⟨le_max_left _ _, max_le hθ (min_le_right _ _)⟩

/-- The clamp is the identity on `Θ`. -/
theorem shocksClamp_of_mem {t : ℝ} (ht : t ∈ Icc θlo θhi) : shocksClamp θlo θhi t = t := by
  simp [shocksClamp, ht.1, ht.2]

/-- The clamp is continuous. -/
theorem continuous_shocksClamp : Continuous (shocksClamp θlo θhi) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The ratio `θ′/θ̃` (both clamped to `Θ`). -/
noncomputable def shocksRatio (θlo θhi θ' θt : ℝ) : ℝ :=
  shocksClamp θlo θhi θ' / shocksClamp θlo θhi θt

/-- `θ′/θ̃ ∈ [θ̲/θ̄, θ̄/θ̲]`. -/
theorem shocksRatio_mem (h0 : 0 < θlo) (hθ : θlo ≤ θhi) (θ' θt : ℝ) :
    shocksRatio θlo θhi θ' θt ∈ Icc (θlo / θhi) (θhi / θlo) := by
  have h1 := shocksClamp_mem hθ θ'
  have h2 := shocksClamp_mem hθ θt
  have h3 : 0 < shocksClamp θlo θhi θt := h0.trans_le h2.1
  exact ⟨div_le_div₀ (h0.le.trans h1.1) h1.1 h3 h2.2,
    div_le_div₀ (h0.le.trans hθ) h1.2 h0 h2.1⟩

/-- `θ′/θ̃` is continuous in `(θ′, θ̃)`. -/
theorem continuous_shocksRatio (h0 : 0 < θlo) :
    Continuous fun p : ℝ × ℝ => shocksRatio θlo θhi p.1 p.2 :=
  (continuous_shocksClamp.comp continuous_fst).div (continuous_shocksClamp.comp continuous_snd)
    fun _ => (h0.trans_le (le_max_left _ _)).ne'

variable {Z : Type*} {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- The integrand of (4), `φ[(θ′/θ̃) ζ⁻¹(f(z′))]`, at `θ̃` and `ω = (θ′, z′)`. -/
noncomputable def shocksIntegrand (L : ℝ) (H' V' : ℝ → ℝ) (θlo θhi : ℝ) (f : Z → ℝ) (θt : ℝ)
    (ω : ℝ × Z) : ℝ :=
  olgPhi V' (shocksRatio θlo θhi ω.1 θt * olgZetaInv L H' (f ω.2))

/-- `φ_f(θ̃) = ∫ φ[(θ′/θ̃) ζ⁻¹(f(z′))] dμ(θ′, z′)` (p. 537), `μ` the law of `(θ′, z′)`. -/
noncomputable def shocksPhiF [MeasurableSpace Z] (L : ℝ) (H' V' : ℝ → ℝ) (θlo θhi : ℝ)
    (μ : Measure (ℝ × Z))
    (f : Z → ℝ) (θt : ℝ) : ℝ :=
  ∫ ω, shocksIntegrand L H' V' θlo θhi f θt ω ∂μ

/-- The operator (4), `(Tf)(z) = ∫ φ_f(θ̃) G(dθ̃|z)`, with `ν z = G(·|z)`. -/
noncomputable def shocksOpT [MeasurableSpace Z] (L : ℝ) (H' V' : ℝ → ℝ) (θlo θhi : ℝ)
    (μ : Measure (ℝ × Z))
    (ν : Z → Measure ℝ) (f : Z → ℝ) (z : Z) : ℝ :=
  ∫ θt, shocksPhiF L H' V' θlo θhi μ f θt ∂ν z

/-- The integrand is the OLG kernel `olgG` at the ratio `r = θ′/θ̃ ∈ [θ̲/θ̄, θ̄/θ̲]`. -/
theorem shocksIntegrand_eq_olgG (h0 : 0 < θlo) (hθ : θlo ≤ θhi) (f : Z → ℝ) (θt : ℝ)
    (ω : ℝ × Z) :
    shocksIntegrand L H' V' θlo θhi f θt ω =
      olgG L H' V' (⟨_, shocksRatio_mem h0 hθ ω.1 θt⟩ : Icc (θlo / θhi) (θhi / θlo))
        ⟨_, shocksRatio_mem h0 hθ ω.1 θt⟩ (f ω.2) :=
  rfl

variable [MeasurableSpace Z] in
/-- **The zero fixed point.** `T0 = 0`, since `ζ⁻¹(0) = 0` and `φ(0) = 0`. -/
theorem shocksOpT_zero (hH : Assumption17_1H L H H' H'') (μ : Measure (ℝ × Z))
    (ν : Z → Measure ℝ) (z : Z) : shocksOpT L H' V' θlo θhi μ ν (fun _ => 0) z = 0 := by
  simp [shocksOpT, shocksPhiF, shocksIntegrand, hH.zetaInv_zero, olgPhi]

/-- The standing hypotheses for §17.6: `0 < θ̲ ≤ θ̄`, `H` as in Assumption 17.1, `V` as in the
repaired Assumption 17.1 (`V` continuous on `ℝ₊`, `C²` on `ℝ₊₊`), and `l₀ ∈ (0, L)` with
`H'(l₀) < C = (θ̲/θ̄) V'((θ̄/θ̲) L)` (the manual's constant `C`, Exercise 17.9). -/
structure ShocksBounds (L θlo θhi l₀ : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) : Prop where
  θlo_pos : 0 < θlo
  θlo_le : θlo ≤ θhi
  hH : Assumption17_1H L H H' H''
  hV : Assumption17_1VR V V' V''
  l₀_mem : l₀ ∈ Ioo 0 L
  l₀_lt : H' l₀ < θlo / θhi * V' (θhi / θlo * L)

/-- A suitable `l₀` always exists. -/
theorem shocksBounds_exists (h0 : 0 < θlo) (hθ : θlo ≤ θhi) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') : ∃ l₀, ShocksBounds L θlo θhi l₀ H H' H'' V V' V'' := by
  have hC : 0 < θlo / θhi * V' (θhi / θlo * L) :=
    mul_pos (div_pos h0 (h0.trans_le hθ)) (hV.V'_pos (mul_pos (div_pos (h0.trans_le hθ) h0)
      hH.L_pos))
  obtain ⟨l₀, hl₀, hlt⟩ := hH.exists_H'_lt hC
  exact ⟨l₀, h0, hθ, hH, hV, hl₀, hlt⟩

namespace ShocksBounds

variable {l₀ l : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'')
include hS

/-- `0 < θ̲/θ̄ ≤ θ̄/θ̲`. -/
theorem ratio_bounds : 0 < θlo / θhi ∧ θlo / θhi ≤ θhi / θlo := by
  have h1 : 0 < θhi := hS.θlo_pos.trans_le hS.θlo_le
  refine ⟨div_pos hS.θlo_pos h1, ?_⟩
  rw [div_le_div_iff₀ h1 hS.θlo_pos]
  nlinarith [hS.θlo_pos, hS.θlo_le]

/-- `ζ(l) > 0` for `l ∈ (0, l₀]`. -/
theorem zeta_pos (hl : l ∈ Ioc 0 l₀) : 0 < olgZeta H' l :=
  hS.hH.zeta_pos ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩

/-- **(7) for §17.6** (Exercise 17.9). If `f(z′) ≥ ζ(l)`, `0 < l ≤ l₀`, then the integrand is
`≥ ζ(l)`. -/
theorem integrand_ge (hl : l ∈ Ioc 0 l₀) {f : Z → ℝ} {θt : ℝ} {ω : ℝ × Z}
    (hf : olgZeta H' l ≤ f ω.2) : olgZeta H' l ≤ shocksIntegrand L H' V' θlo θhi f θt ω := by
  rw [shocksIntegrand_eq_olgG hS.θlo_pos hS.θlo_le]
  exact olgG_ge hS.ratio_bounds.1 hS.ratio_bounds.2 hS.hH hS.hV hS.l₀_mem hS.l₀_lt hl hf _ _

/-- The integrand is bounded above on `{f ≥ ζ(l)}`: its argument lies in
`[(θ̲/θ̄) l, (θ̄/θ̲) L]`. -/
theorem exists_integrand_le (hl : l ∈ Ioc 0 l₀) : ∃ B, 0 < B ∧ ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩
  have hK : IsCompact (Icc (θlo / θhi * l) (θhi / θlo * L)) := isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hS.hV.phi_continuousOn.mono
    fun y hy => (mul_pos ha hl.1).trans_le hy.1)
  have hBpos : 0 < max B (olgZeta H' l) + 1 := by
    have := le_max_right B (olgZeta H' l)
    linarith [hS.zeta_pos hl]
  refine ⟨max B (olgZeta H' l) + 1, hBpos, fun f θt ω hf => ?_⟩
  have hy0 : 0 ≤ f ω.2 := (hS.zeta_pos hl).le.trans hf
  have hm := hS.hH.zetaInv_mem hy0
  have hlm : l ≤ olgZetaInv L H' (f ω.2) := by
    have := hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hS.zeta_pos hl).le)
      (mem_Ici.2 hy0) hf
    rwa [hS.hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
  have hr := shocksRatio_mem hS.θlo_pos hS.θlo_le ω.1 θt
  have hmem : shocksRatio θlo θhi ω.1 θt * olgZetaInv L H' (f ω.2) ∈
      Icc (θlo / θhi * l) (θhi / θlo * L) :=
    ⟨mul_le_mul hr.1 hlm hl.1.le (ha.le.trans hr.1),
      mul_le_mul hr.2 hm.2.le hm.1 (ha.le.trans hab)⟩
  have := hB _ hmem
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans ((le_max_left _ _).trans (le_add_of_nonneg_right
    zero_le_one)))

variable [TopologicalSpace Z] in
/-- The integrand is jointly continuous in `(θ̃, θ′, z′)` for continuous `f > 0`. -/
theorem continuous_integrand {f : Z → ℝ} (hfc : Continuous f) (hf : ∀ z, 0 < f z) :
    Continuous fun p : ℝ × (ℝ × Z) => shocksIntegrand L H' V' θlo θhi f p.1 p.2 := by
  have h1 : Continuous fun p : ℝ × (ℝ × Z) => shocksRatio θlo θhi p.2.1 p.1 :=
    (continuous_shocksRatio hS.θlo_pos).comp ((continuous_fst.comp continuous_snd).prodMk
      continuous_fst)
  have h2 : Continuous fun p : ℝ × (ℝ × Z) => olgZetaInv L H' (f p.2.2) :=
    hS.hH.zetaInv_continuousOn.comp_continuous (hfc.comp (continuous_snd.comp continuous_snd))
      fun p => mem_Ici.2 (hf _).le
  refine hS.hV.phi_continuousOn.comp_continuous (h1.mul h2) fun p => ?_
  exact mul_pos (hS.ratio_bounds.1.trans_le (shocksRatio_mem hS.θlo_pos hS.θlo_le _ _).1)
    (hS.hH.zetaInv_pos (hf _))

variable [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] {B : ℝ}
  {f : Z → ℝ}

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- With `0 < l ≤ l₀` and `f ≥ ζ(l)`, `|integrand| ≤ B`. -/
theorem abs_integrand_le (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (θt : ℝ) (ω : ℝ × Z) :
    |shocksIntegrand L H' V' θlo θhi f θt ω| ≤ B := by
  rw [abs_of_pos ((hS.zeta_pos hl).trans_le (hS.integrand_ge hl (hfl ω.2)))]
  exact hB f θt ω (hfl ω.2)

/-- The integrand is integrable in `ω` for every finite `μ`. -/
theorem integrable_integrand (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsFiniteMeasure μ] (θt : ℝ) :
    Integrable (fun ω => shocksIntegrand L H' V' θlo θhi f θt ω) μ := by
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  refine (integrable_const B).mono' ?_ (ae_of_all _ fun ω => ?_)
  · exact ((hS.continuous_integrand hfc hpos).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hS.abs_integrand_le hl hB hfl θt ω

/-- `ζ(l) ≤ φ_f ≤ B`. -/
theorem phiF_mem (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (θt : ℝ) :
    shocksPhiF L H' V' θlo θhi μ f θt ∈ Icc (olgZeta H' l) B := by
  have hi := hS.integrable_integrand hl hB hfc hfl μ θt
  constructor
  · have := integral_mono (integrable_const (olgZeta H' l)) hi fun ω =>
      hS.integrand_ge hl (hfl ω.2) (θt := θt)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  · have := integral_mono hi (integrable_const B) fun ω => hB f θt ω (hfl ω.2)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this

/-- `φ_f` is continuous (dominated convergence). -/
theorem continuous_phiF (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] :
    Continuous (shocksPhiF L H' V' θlo θhi μ f) := by
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  have hc := hS.continuous_integrand hfc hpos
  refine continuous_of_dominated (bound := fun _ => B) (fun θt => ?_) (fun θt => ae_of_all _
    fun ω => ?_) (integrable_const B) (ae_of_all _ fun ω => ?_)
  · exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hS.abs_integrand_le hl hB hfl θt ω
  · exact hc.comp (continuous_id.prodMk continuous_const)

/-- `φ_f` as a bounded continuous function. -/
noncomputable def phiFBCF (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] : ℝ →ᵇ ℝ :=
  ofNormedAddCommGroup (shocksPhiF L H' V' θlo θhi μ f) (hS.continuous_phiF hl hB hfc hfl μ) B
    fun θt => by
      have h := hS.phiF_mem hl hB hfc hfl μ θt
      rw [Real.norm_eq_abs, abs_of_pos ((hS.zeta_pos hl).trans_le h.1)]
      exact h.2

/-- Evaluation of `phiFBCF`. -/
theorem phiFBCF_apply (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (θt : ℝ) :
    hS.phiFBCF hl hB hfc hfl μ θt = shocksPhiF L H' V' θlo θhi μ f θt :=
  rfl

/-- **Exercise 17.11, steps 1–2** (and the first step of Exercise 17.9): with
`D = [ζ(l), B]`, `0 < l ≤ l₀`, `T` maps continuous `D`-valued `f` to continuous `D`-valued `Tf`
(continuity from the weak continuity of `z ↦ G(·|z)`, Exercise 17.8b). -/
theorem opT_mem (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    Continuous (shocksOpT L H' V' θlo θhi μ ν f) ∧
      ∀ z, shocksOpT L H' V' θlo θhi μ ν f z ∈ Icc (olgZeta H' l) B := by
  refine ⟨hν (hS.phiFBCF hl hB hfc hfl μ), fun z => ⟨?_, ?_⟩⟩
  · have := integral_mono (integrable_const (olgZeta H' l))
      ((hS.phiFBCF hl hB hfc hfl μ).integrable (ν z)) fun θt =>
        (hS.phiF_mem hl hB hfc hfl μ θt).1
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  · have := integral_mono ((hS.phiFBCF hl hB hfc hfl μ).integrable (ν z))
      (integrable_const B) fun θt => (hS.phiF_mem hl hB hfc hfl μ θt).2
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- **Exercise 17.9, the mean-value step.** Under the repaired Assumption 17.2, for
`e^g, e^h ≥ ζ(l)` the log-integrand is `β`-Lipschitz in the log-argument:
`|ln φ[(θ′/θ̃) ζ⁻¹(e^{g(z′)})] − ln φ[(θ′/θ̃) ζ⁻¹(e^{h(z′)})]| ≤ β |g(z′) − h(z′)|`. -/
theorem abs_log_integrand_sub_le {β : ℝ} (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    {g h : Z → ℝ} (hg : ∀ z, olgZeta H' l ≤ Real.exp (g z))
    (hh : ∀ z, olgZeta H' l ≤ Real.exp (h z)) (θt : ℝ) (ω : ℝ × Z) :
    |Real.log (shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (g z)) θt ω) -
      Real.log (shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (h z)) θt ω)| ≤
        β * |g ω.2 - h ω.2| := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hzl := hS.zeta_pos hl
  have hyp := olgG_hyp ha hab hS.hH hS.hV hS.l₀_mem hS.l₀_lt hl
    (κ := Kernel.deterministic (id : Icc (θlo / θhi) (θhi / θlo) → _) measurable_id)
    isFellerKernel_deterministic_id
  rw [shocksIntegrand_eq_olgG hS.θlo_pos hS.θlo_le, shocksIntegrand_eq_olgG hS.θlo_pos hS.θlo_le]
  exact abs_log_G_sub_le hyp (fun y hy => hzl.trans_le hy)
    (fun x x' y hy => (olgG_hasDerivAt ha hS.hH hS.hV x x' (hzl.trans_le hy)).hasDerivWithinAt)
    (fun x x' y hy => olgG_elasticity_le ha hS.hH hS.hV h2 x x' (hzl.trans_le hy)) _ _
    ⟨_, hg ω.2, Real.log_exp _⟩ ⟨_, hh ω.2, Real.log_exp _⟩

/-- **Exercise 17.9, integrated.** If `|g − h| ≤ d` then
`T(e^g) ≤ e^{βd} T(e^h)` pointwise. (This is the book's weighted-average step; the weights `w`
of the manual are not needed.) -/
theorem opT_exp_le {β : ℝ} (hβ : 0 ≤ β) (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    {g h : Z → ℝ} (hgc : Continuous g) (hhc : Continuous h)
    (hg : ∀ z, olgZeta H' l ≤ Real.exp (g z)) (hh : ∀ z, olgZeta H' l ≤ Real.exp (h z))
    {d : ℝ} (hd : ∀ z, |g z - h z| ≤ d) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] (z : Z) :
    shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g z)) z ≤
      Real.exp (β * d) * shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (h z)) z := by
  have hzl := hS.zeta_pos hl
  have hegc : Continuous fun z => Real.exp (g z) := Real.continuous_exp.comp hgc
  have hehc : Continuous fun z => Real.exp (h z) := Real.continuous_exp.comp hhc
  have hpt : ∀ θt ω, shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (g z)) θt ω ≤
      Real.exp (β * d) * shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (h z)) θt ω :=
    fun θt ω => by
      have hA := hzl.trans_le (hS.integrand_ge hl (f := fun z => Real.exp (g z)) (hg ω.2)
        (θt := θt))
      have hB' := hzl.trans_le (hS.integrand_ge hl (f := fun z => Real.exp (h z)) (hh ω.2)
        (θt := θt))
      have := (abs_sub_le_iff.1 (hS.abs_log_integrand_sub_le h2 hl hg hh θt ω)).1
      have h3 : β * |g ω.2 - h ω.2| ≤ β * d := mul_le_mul_of_nonneg_left (hd ω.2) hβ
      rw [← Real.exp_log hA, ← Real.exp_log hB', ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
  have hφ : ∀ θt, shocksPhiF L H' V' θlo θhi μ (fun z => Real.exp (g z)) θt ≤
      Real.exp (β * d) * shocksPhiF L H' V' θlo θhi μ (fun z => Real.exp (h z)) θt := fun θt => by
    simp only [shocksPhiF]
    rw [← integral_const_mul]
    exact integral_mono (hS.integrable_integrand hl hB hegc hg μ θt)
      ((hS.integrable_integrand hl hB hehc hh μ θt).const_mul _) (hpt θt)
  simp only [shocksOpT]
  rw [← integral_const_mul]
  exact integral_mono ((hS.phiFBCF hl hB hegc hg μ).integrable (ν z))
    (((hS.phiFBCF hl hB hehc hh μ).integrable (ν z)).const_mul _) hφ

end ShocksBounds

/-! ### Proposition 6 by the contraction mapping theorem -/

namespace ShocksBounds

variable {l₀ l B : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'')
  [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
include hS

/-- `T(e^g) ∈ [ζ(l), B]` and is continuous for `g ∈ F̂`. -/
theorem opT_exp_mem (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z)
    (g : olgF Z (olgDhat (Ici (olgZeta H' l)))) :
    Continuous (shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z))) ∧
      ∀ z, shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z)) z ∈
        Icc (olgZeta H' l) B :=
  hS.opT_mem hl hB (f := fun z => Real.exp (g.1 z)) (Real.continuous_exp.comp g.1.continuous)
    (fun z => exp_mem_of_mem_olgDhat (fun _ hy => (hS.zeta_pos hl).trans_le hy) (g.2 z)) μ ν hν

variable [CompactSpace Z]

/-- The logarithmic operator `T̂g = ln T(e^g)` of Exercise 17.9, on
`F̂ = {g ∈ C(Z) : e^g ≥ ζ(l)}` (`D = [ζ(l), ∞)`, `0 < l ≤ l₀`). -/
noncomputable def opThat (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z)
    (g : olgF Z (olgDhat (Ici (olgZeta H' l)))) : olgF Z (olgDhat (Ici (olgZeta H' l))) :=
  ⟨mkOfCompact ⟨fun z => Real.log (shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z)) z),
    (hS.opT_exp_mem hl hB μ ν hν g).1.log fun z =>
      ((hS.zeta_pos hl).trans_le ((hS.opT_exp_mem hl hB μ ν hν g).2 z).1).ne'⟩,
    fun z => ⟨_, ((hS.opT_exp_mem hl hB μ ν hν g).2 z).1, rfl⟩⟩

/-- Evaluation of `opThat`. -/
theorem opThat_apply (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z)
    (g : olgF Z (olgDhat (Ici (olgZeta H' l)))) (z : Z) :
    (hS.opThat hl hB μ ν hν g).1 z =
      Real.log (shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z)) z) :=
  rfl

/-- **Exercise 17.9** (p. 535): under the repaired Assumption 17.2, `T̂` is a contraction of
modulus `β` on `F̂`. (The manual's final lines drop `β` and write `sup(g − h)` for
`sup|g − h|`.) -/
theorem ex_17_9 {β : ℝ} (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    LipschitzWith β.toNNReal (hS.opThat hl hB μ ν hν) := by
  have hβ := h2.β_nonneg
  have hDpos : Ici (olgZeta H' l) ⊆ Ioi 0 := fun y hy => (hS.zeta_pos hl).trans_le hy
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  simp only [Subtype.dist_eq]
  rw [Real.coe_toNNReal β hβ, BoundedContinuousFunction.dist_le (mul_nonneg hβ dist_nonneg)]
  intro z
  have hg : ∀ z, olgZeta H' l ≤ Real.exp (g.1 z) := fun z => exp_mem_of_mem_olgDhat hDpos (g.2 z)
  have hh : ∀ z, olgZeta H' l ≤ Real.exp (h.1 z) := fun z => exp_mem_of_mem_olgDhat hDpos (h.2 z)
  have hd1 : ∀ z, |g.1 z - h.1 z| ≤ dist g.1 h.1 := fun z => by
    rw [← Real.dist_eq]; exact dist_coe_le_dist z
  have hd2 : ∀ z, |h.1 z - g.1 z| ≤ dist g.1 h.1 := fun z => by
    rw [abs_sub_comm]; exact hd1 z
  have hTg := ((hS.opT_exp_mem hl hB μ ν hν g).2 z).1
  have hTh := ((hS.opT_exp_mem hl hB μ ν hν h).2 z).1
  have hpg := (hS.zeta_pos hl).trans_le hTg
  have hph := (hS.zeta_pos hl).trans_le hTh
  have e1 := hS.opT_exp_le hβ h2 hl hB g.1.continuous h.1.continuous hg hh hd1 μ ν z
  have e2 := hS.opT_exp_le hβ h2 hl hB h.1.continuous g.1.continuous hh hg hd2 μ ν z
  have L1 := Real.log_le_log hpg e1
  have L2 := Real.log_le_log hph e2
  rw [Real.log_mul (Real.exp_pos _).ne' hph.ne', Real.log_exp] at L1
  rw [Real.log_mul (Real.exp_pos _).ne' hpg.ne', Real.log_exp] at L2
  rw [opThat_apply, opThat_apply, Real.dist_eq, abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Lemma 17.2 for §17.6**: for `0 < l ≤ l₀`, `T` has exactly one fixed point among the
continuous `f ≥ ζ(l)`. -/
theorem unique_fixedPoint_ge {β : ℝ} (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) [Nonempty Z] :
    ∃! f : Z →ᵇ ℝ, (∀ z, olgZeta H' l ≤ f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le (Z := Z) hl
  have hDpos : Ici (olgZeta H' l) ⊆ Ioi 0 := fun y hy => (hS.zeta_pos hl).trans_le hy
  have : CompleteSpace (olgF Z (olgDhat (Ici (olgZeta H' l)))) := ex_17_4b isClosed_Ici hDpos
  have : Nonempty (olgF Z (olgDhat (Ici (olgZeta H' l)))) :=
    ⟨⟨const Z (Real.log (olgZeta H' l)), fun _ => ⟨_, mem_Ici.2 le_rfl, rfl⟩⟩⟩
  have hK : ContractingWith β.toNNReal (hS.opThat hl hB μ ν hν) :=
    ⟨Real.toNNReal_lt_one.2 h2.β_lt_one, hS.ex_17_9 h2 hl hB μ ν hν⟩
  set gs := ContractingWith.fixedPoint _ hK
  have hfix : hS.opThat hl hB μ ν hν gs = gs := ContractingWith.fixedPoint_isFixedPt hK
  have hmem : ∀ z, olgZeta H' l ≤ Real.exp (gs.1 z) := fun z =>
    exp_mem_of_mem_olgDhat hDpos (gs.2 z)
  let fs : Z →ᵇ ℝ := mkOfCompact ⟨fun z => Real.exp (gs.1 z),
    Real.continuous_exp.comp gs.1.continuous⟩
  have hfs : ∀ z, fs z = Real.exp (gs.1 z) := fun _ => rfl
  refine ⟨fs, ⟨fun z => by rw [hfs]; exact hmem z, fun z => ?_⟩, ?_⟩
  · have h1 : (hS.opThat hl hB μ ν hν gs).1 z = gs.1 z := by rw [hfix]
    rw [opThat_apply] at h1
    have hpos : 0 < shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (gs.1 z)) z :=
      (hS.zeta_pos hl).trans_le ((hS.opT_mem hl hB (f := fun z => Real.exp (gs.1 z))
        (Real.continuous_exp.comp gs.1.continuous)
        hmem μ ν hν).2 z).1
    rw [hfs, ← h1, Real.exp_log hpos]
    rfl
  · rintro f ⟨hfD, hfix'⟩
    have hfpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfD z)
    let lf : olgF Z (olgDhat (Ici (olgZeta H' l))) := ⟨mkOfCompact ⟨fun z => Real.log (f z),
      f.continuous.log fun z => (hfpos z).ne'⟩, fun z => ⟨f z, hfD z, rfl⟩⟩
    have hexp : (fun z => Real.exp (lf.1 z)) = ⇑f := by
      ext z; exact Real.exp_log (hfpos z)
    have hlf : hS.opThat hl hB μ ν hν lf = lf := by
      apply Subtype.ext
      ext z
      rw [opThat_apply, hexp, ← hfix' z]
      rfl
    have : lf = gs := ContractingWith.fixedPoint_unique hK hlf
    ext z
    rw [hfs, ← this]
    change f z = Real.exp (Real.log (f z))
    rw [Real.exp_log (hfpos z)]

end ShocksBounds

/-- **Proposition 6** (p. 535), corrected. Let `H` satisfy Assumption 17.1, `V` the repaired
Assumptions 17.1 and 17.2 (`Assumption17_1VR`, `Assumption17_2R`), `0 < θ̲ ≤ θ̄`, `Z` a compact
metric space, `μ` any probability law of `(θ′, z′)` and `z ↦ ν z = G(·|z)` weakly continuous
probability measures (Exercise 17.8b). Then `T` of (4) has exactly one **strictly positive**
continuous fixed point. (By `proposition_6_zero_fixedPoint` the zero function is another fixed
point, so "a unique fixed point in `C(Z)`" is false; see `proposition_6_counterexample`.)

The uniqueness among strictly positive fixed points uses the sets `[ζ(l), ∞)`, `0 < l ≤ l₀`, as
in `proposition_2`: a positive continuous fixed point has a positive minimum on compact `Z`. -/
theorem proposition_6 [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [Nonempty Z] (h0 : 0 < θlo) (hθ : θlo ≤ θhi)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    ∃! f : Z →ᵇ ℝ, (∀ z, 0 < f z) ∧ ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  obtain ⟨l₀, hS⟩ := shocksBounds_exists h0 hθ hH hV
  obtain ⟨f₀, ⟨hf₀D, hf₀fix⟩, -⟩ := hS.unique_fixedPoint_ge h2 ⟨hS.l₀_mem.1, le_rfl⟩ μ ν hν
  have hz0 := hS.zeta_pos ⟨hS.l₀_mem.1, le_rfl⟩
  refine ⟨f₀, ⟨fun z => hz0.trans_le (hf₀D z), hf₀fix⟩, ?_⟩
  rintro f ⟨hfpos, hffix⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn univ_nonempty f.continuous.continuousOn
  set l := min l₀ (olgZetaInv L H' (f m))
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hS.l₀_mem.1 (hH.zetaInv_pos (hfpos m)), min_le_left _ _⟩
  have hlL : l ∈ Ico 0 L := ⟨hl.1.le, hl.2.trans_lt hS.l₀_mem.2⟩
  have hzl : olgZeta H' l ≤ f m :=
    calc olgZeta H' l ≤ olgZeta H' (olgZetaInv L H' (f m)) :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
  have hzl0 : olgZeta H' l ≤ olgZeta H' l₀ :=
    hH.zeta_strictMonoOn.monotoneOn hlL (Ioo_subset_Ico_self hS.l₀_mem) (min_le_left _ _)
  obtain ⟨g, -, hg⟩ := hS.unique_fixedPoint_ge h2 hl μ ν hν
  have e1 := hg f ⟨fun z => hzl.trans (isMinOn_iff.1 hm z (mem_univ z)), hffix⟩
  have e2 := hg f₀ ⟨fun z => hzl0.trans (hf₀D z), hf₀fix⟩
  rw [e1, e2]

/-- **Correction (Proposition 6: the zero fixed point).** `f ≡ 0` solves (4). -/
theorem proposition_6_zero_fixedPoint [TopologicalSpace Z] [MeasurableSpace Z]
    (hH : Assumption17_1H L H H' H'') (μ : Measure (ℝ × Z)) (ν : Z → Measure ℝ) (z : Z) :
    (0 : Z →ᵇ ℝ) z = shocksOpT L H' V' θlo θhi μ ν (0 : Z →ᵇ ℝ) z := by
  have := shocksOpT_zero (θlo := θlo) (θhi := θhi) (V' := V') hH μ ν z
  rw [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  exact this.symm

/-- **Correction (Proposition 6, "a unique fixed point in `C(Z)`" is false).** Under the
hypotheses of `proposition_6`, `T` has (at least) two fixed points in `C(Z)`: `0` and the
strictly positive `f*`. -/
theorem proposition_6_counterexample [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [Nonempty Z] (h0 : 0 < θlo) (hθ : θlo ≤ θhi)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    ¬ ∃! f : Z →ᵇ ℝ, ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  rintro ⟨g, -, hg⟩
  obtain ⟨f, ⟨hfpos, hffix⟩, -⟩ := proposition_6 h0 hθ hH hV h2 μ ν hν
  have e1 := hg f hffix
  have e2 := hg 0 (proposition_6_zero_fixedPoint hH μ ν)
  obtain ⟨z⟩ := ‹Nonempty Z›
  have := hfpos z
  rw [e1, ← e2] at this
  simp at this

/-! ### Proposition 6 for the islands model -/

/-- The joint law of `(θ′, z′)`, `z′ = x′/θ′` (projected onto `Z`), when `x′ ~ ψ` and `θ′ ~ g`
are independent. -/
noncomputable def shocksJointLaw (xlo xhi θlo θhi : ℝ) (hZ : xlo / θhi ≤ xhi / θlo)
    (ψ g : ℝ → ℝ) : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo)) :=
  Measure.map (fun p : ℝ × ℝ => (p.2, projIcc (xlo / θhi) (xhi / θlo) hZ (p.1 / p.2)))
    ((volume.withDensity fun x => ENNReal.ofReal (ψ x)).prod
      (volume.withDensity fun θ => ENNReal.ofReal (g θ)))

variable {xlo xhi : ℝ} {ψ g : ℝ → ℝ}

/-- A probability density gives a probability measure. -/
theorem shocks_isProbabilityMeasure_withDensity {ρ : ℝ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρ1 : ∫ x, ρ x = 1) :
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one]

/-- A function continuous on `[a, b]` and zero off it is integrable. -/
theorem shocks_integrable_of_zero_off {a b : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∉ Icc a b, f x = 0) : Integrable f := by
  have : f = (Icc a b).indicator f := by
    ext x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h0 x hx]
  rw [this]
  exact (hc.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc

/-- The joint law is a probability measure. -/
theorem isProbabilityMeasure_shocksJointLaw (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
    (hZ : xlo / θhi ≤ xhi / θlo) :
    IsProbabilityMeasure (shocksJointLaw xlo xhi θlo θhi hZ ψ g) := by
  have h1 := shocks_isProbabilityMeasure_withDensity hA.ψ_nonneg
    (shocks_integrable_of_zero_off hA.ψ_cont hA.ψ_zero) hA.ψ_int
  have h2 := shocks_isProbabilityMeasure_withDensity hA.g_nonneg
    (shocks_integrable_of_zero_off hA.g_cont hA.g_zero) hA.g_int
  exact (Measure.isProbabilityMeasure_map_iff (measurable_snd.prodMk
    (continuous_projIcc.measurable.comp (measurable_fst.div measurable_snd))).aemeasurable).2
    inferInstance

/-- **Proposition 6 for the islands model** (p. 535), corrected: under Assumption 17.1 for `H`,
the repaired Assumptions 17.1 and 17.2 for `V`, Assumption 17.5 with `ψ > 0` on `X` and `g > 0`
on `Θ` (so that `π > 0` on `int Z` and Exercise 17.8b applies), the operator (4) on `C(Z)`, with
`μ` the joint law of `(θ′, z′)` and `G(·|z)` the conditional law of `θ̃` given `z`, has exactly one
strictly positive continuous fixed point. -/
theorem proposition_6_islands (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
    (hψ : ∀ x ∈ Icc xlo xhi, 0 < ψ x) (hg : ∀ θ ∈ Icc θlo θhi, 0 < g θ)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (hZ : xlo / θhi ≤ xhi / θlo) :
    ∃! f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z := by
  have hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z :=
    fun z hz => hA.pi_pos hψ hg hz
  have := isProbabilityMeasure_shocksJointLaw hA hZ
  have : ∀ z : Icc (xlo / θhi) (xhi / θlo),
      IsProbabilityMeasure (shocksCondLaw xlo xhi θlo θhi ψ g z.1) := fun z =>
    hA.isProbabilityMeasure_condLaw' hπ z.1
  have : Nonempty (Icc (xlo / θhi) (xhi / θlo)) := ⟨⟨_, left_mem_Icc.2 hZ⟩⟩
  exact proposition_6 hA.θlo_pos hA.θlo_lt.le hH hV h2 _ _
    fun h => (hA.ex_17_8b hπ h).domRestrict

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: Proposition 7 (Schauder), (7), and finite `Z` (Brouwer)

SLP §17.6, pp. 535–539: Assumption 17.6, Proposition 7, Exercises 17.11 and 17.13 and the
equicontinuity argument (Step 4), **with the correct conditional weights** `2θ/(b² − a²)`
(Exercise 17.12 is false, `ex_17_12_counterexample` in `FixedPointArguments.ShocksModel`).
The operator `shocksOpT` and the bounds `ShocksBounds` are from
`FixedPointArguments.ShocksContraction`; Schauder's theorem is `schauder_closed`, Brouwer's
`theorem_17_3`.

* `shocksWAvg φ a b`: the `θ`-weighted average of `φ` over `[a, b]` (`φ(a)` if `a = b`), with
  `shocksWAvg_extend_right`, `shocksWAvg_extend_left`, `abs_sub_shocksWAvg_le`, and the direct
  Lipschitz bound `shocksWAvg_lipschitz`: if `φ` is `B`-Lipschitz on `[c, d]`, `0 < c`, then
  `|wavg(a, b) − wavg(a′, b′)| ≤ (d/c) B (|a − a′| + |b − b′|)`.
* `shocksA_lipschitz`, `shocksB_lipschitz`, `shocksA_shocksB_mem`: `a`, `b` are Lipschitz on `Z`
  and `θ̲ ≤ a ≤ b ≤ θ̄`.
* **(6a)–(6b), corrected** (`shocksUnif_integral_condLaw`, p. 537): under Assumptions 17.5–17.6,
  `∫ k dG(·|z) = wavg(k; a(z), b(z))` for all `z ∈ Z` (degenerate at `z̲`, `z̄`).
* **Exercise 17.11** (p. 536): Steps 1–2 are `ShocksBounds.opT_mem`
  (`FixedPointArguments.ShocksContraction`), Step 3 is `ShocksBounds.ex_17_11_step3`; as the book
  says, they need neither Assumption 17.6 nor any property of `μ` beyond being a probability.
* **Exercise 17.13** (`ShocksBounds.ex_17_13`, p. 537), in Lipschitz form: all `φ_f`, `f ∈ F`,
  are `K`-Lipschitz on `Θ` with one `K` (the derivative form is in
  `FixedPointArguments.ShocksMonotone`).
* **Step 4** (`shocksUnif_opT_lipschitz`, pp. 537–539): every `Tf`, `f ∈ F`, is Lipschitz on `Z`
  with the common constant `(θ̄/θ̲) K (x̲ + x̄)/z̲²`, so `T(F)` is equicontinuous.
* **(7), corrected** (`eq7_corrected`, p. 537): on `Ẑ` (interior points off the kinks
  `x̲/z = θ̲`, `x̄/z = θ̄`), `W(z) = wavg(φ; a(z), b(z))` (`= Tf(z)` by (6a)) is differentiable with
  `W′ = [b b′(φ(b) − W) − a a′(φ(a) − W)]/((b² − a²)/2)`, for every continuous `φ` (in particular
  `φ_f`); from the abstract `shocksWAvg_hasDerivAt` and the one-sided pieces
  `shocksA_hasDerivAt`, `shocksB_hasDerivAt` (`a′ = −x̲/z²` or `0`, `b′ = −x̄/z²` or `0`).
* **Finite `Z`** (`shocks_finite_Z`, p. 539): with finitely many values of `z`, for any `μ` and
  any conditional laws, `T` has a fixed point bounded away from zero, by Brouwer
  (`theorem_17_3`) using Steps 1–3 only.
* **Proposition 7** (`proposition_7`, p. 536), corrected: a continuous fixed point bounded away
  from `0`, for every law `μ` of `(θ′, z′)`; `proposition_7_islands`: under the book's
  Assumption 17.1 (`shocks_assumption17_1VR_of_V`) with `μ` the joint law.

**Correction (Exercise 17.12 and (6a), (7)).** The conditional law in (6a) is the `θ`-weighted
one; (6a) becomes `Tf(z) = ∫_a^b φ_f(θ) θ dθ / ((b² − a²)/2)` (`shocksUnif_integral_condLaw`) and
(7) becomes `(Tf)' = [b b′(φ_f(b) − Tf) − a a′(φ_f(a) − Tf)]/((b² − a²)/2)` on `Ẑ`
(`eq7_corrected`; the proof of Proposition 7 here does not need it). Proposition 7 still holds.

**Correction (Step 4: the L'Hôpital argument).** The book solves `L = φ_f′(θ̄) a′(z̲) − L` for
`L = lim (Tf)′`, presupposing that the limit exists, and a limit value is not a uniform bound.
We use instead the direct uniform estimate `shocksWAvg_lipschitz` (from
`|φ_f(θ) − Tf(z)| ≤ K (b − a)` and `∫_a^b θ dθ ≥ θ̲ (b − a)`), which also covers the kinks
`x̲/θ̲`, `x̄/θ̄` of `a`, `b` and needs no differentiability. Typos in Step 4 (high confidence, not
formalised): (7) holds on `Ẑ`, not on all of `Z`; "`z → x̲/z̄`" should be "`z → x̲/θ̄`";
"the numerator in (8)" should be "(7)"; the left-derivative formula at `x̲/θ̲` lost a minus sign.

**Correction (Proposition 7, "a fixed point in `C(Z)`").** `T0 = 0`
(`proposition_6_zero_fixedPoint`), so the statement as written is trivial; the substantive
claim, proved here, is a fixed point bounded away from zero.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

/-! ### `θ`-weighted averages over intervals -/

/-- The `θ`-weighted average `∫_a^b θ φ(θ) dθ / ∫_a^b θ dθ` of `φ` over `[a, b]` (`φ(a)` if
`a = b`): the expectation of `φ(θ)` when `θ` has density `2θ/(b² − a²)` on `[a, b]`. -/
noncomputable def shocksWAvg (φ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a < b then (∫ θ in a..b, θ * φ θ) / ∫ θ in a..b, θ else φ a

variable {φ : ℝ → ℝ} {a b c d : ℝ}

/-- The weighted average on a nondegenerate interval. -/
theorem shocksWAvg_of_lt (h : a < b) :
    shocksWAvg φ a b = (∫ θ in a..b, θ * φ θ) / ∫ θ in a..b, θ := by
  simp [shocksWAvg, h]

/-- `∫_a^b θ dθ = (b² − a²)/2`. -/
theorem shocks_integral_id (a b : ℝ) : ∫ θ in a..b, θ = (b ^ 2 - a ^ 2) / 2 := integral_id

/-- `∫_a^b θ dθ ≥ a (b − a)` for `0 ≤ a ≤ b`. -/
theorem shocks_integral_id_ge (_ha : 0 ≤ a) (hab : a ≤ b) : a * (b - a) ≤ ∫ θ in a..b, θ := by
  rw [shocks_integral_id]; nlinarith

/-- `∫_a^b θ φ(θ) dθ = wavg · ∫_a^b θ dθ` for `0 < a ≤ b`. -/
theorem shocksWAvg_mul_eq (ha : 0 < a) (hab : a ≤ b) :
    ∫ θ in a..b, θ * φ θ = shocksWAvg φ a b * ∫ θ in a..b, θ := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  · have hW : 0 < ∫ θ in a..b, θ := by
      rw [shocks_integral_id]; nlinarith
    rw [shocksWAvg_of_lt h, div_mul_cancel₀ _ hW.ne']

/-- Interval integrability of `θ ↦ θ (φ(θ) − M)` for `φ` continuous on `[c, d] ⊇ [a, b]`. -/
theorem shocks_intervalIntegrable (hφ : ContinuousOn φ (Icc c d)) (hca : c ≤ a) (hab : a ≤ b)
    (hbd : b ≤ d) (M : ℝ) : IntervalIntegrable (fun θ => θ * (φ θ - M)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact continuousOn_id.mul ((hφ.mono (Icc_subset_Icc hca hbd)).sub continuousOn_const)

/-- If `φ` is within `K` of `φ(t)` on `[a, b]`, then so is its weighted average. -/
theorem abs_sub_shocksWAvg_le (hφ : ContinuousOn φ (Icc a b)) (ha : 0 < a) (hab : a ≤ b)
    {t K : ℝ} (hK : ∀ θ ∈ Icc a b, |φ t - φ θ| ≤ K) : |φ t - shocksWAvg φ a b| ≤ K := by
  rcases hab.eq_or_lt with h | h
  · subst h
    simpa [shocksWAvg] using hK a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, h.le⟩)
  have i1 : IntervalIntegrable (fun θ => φ t * θ) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => θ * φ θ) volume a b :=
    (continuousOn_id.mul hφ).intervalIntegrable_of_Icc h.le
  have e : φ t - shocksWAvg φ a b =
      (∫ θ in a..b, θ * (φ t - φ θ)) / ∫ θ in a..b, θ := by
    have h1 : ∫ θ in a..b, θ * (φ t - φ θ) = φ t * (∫ θ in a..b, θ) - ∫ θ in a..b, θ * φ θ := by
      have : (fun θ => θ * (φ t - φ θ)) = fun θ => φ t * θ - θ * φ θ := by ext θ; ring
      rw [this, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
    rw [h1, shocksWAvg_mul_eq ha h.le]
    field_simp
  rw [e, abs_div, abs_of_pos hW, div_le_iff₀ hW]
  have := intervalIntegral.norm_integral_le_of_norm_le h.le (g := fun θ => θ * K)
    (f := fun θ => θ * (φ t - φ θ)) (μ := volume)
    (ae_of_all _ fun θ hθ => by
      have h1 := hK θ (Ioc_subset_Icc_self hθ)
      have h2 : 0 < θ := ha.trans hθ.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos h2]
      nlinarith [abs_nonneg (φ t - φ θ)])
    ((continuous_id.mul continuous_const).intervalIntegrable _ _)
  rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const] at this
  linarith

/-- Extending `[a, b]` to the right:
`wavg(a, b') − wavg(a, b) = ∫_b^{b'} θ(φ − wavg(a, b)) / W(a, b')`. -/
theorem shocksWAvg_extend_right (hφ : ContinuousOn φ (Icc a d)) (ha : 0 < a) (hab : a ≤ b)
    {b' : ℝ} (hbb : b ≤ b') (hbd : b' ≤ d) (hab' : a < b') :
    shocksWAvg φ a b' - shocksWAvg φ a b =
      (∫ θ in b..b', θ * (φ θ - shocksWAvg φ a b)) / ∫ θ in a..b', θ := by
  set M := shocksWAvg φ a b
  have hW : 0 < ∫ θ in a..b', θ := by rw [shocks_integral_id]; nlinarith
  have i1 : IntervalIntegrable (fun θ => θ * φ θ) volume a b :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc le_rfl
      (hbb.trans hbd)))).intervalIntegrable_of_Icc hab
  have i2 : IntervalIntegrable (fun θ => θ * φ θ) volume b b' :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc hab hbd))).intervalIntegrable_of_Icc hbb
  have eS := intervalIntegral.integral_add_adjacent_intervals i1 i2
  have eW := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegral.intervalIntegrable_id (a := a) (b := b) (μ := volume))
    (intervalIntegral.intervalIntegrable_id (a := b) (b := b') (μ := volume))
  have e2 : ∫ θ in b..b', θ * (φ θ - M) = (∫ θ in b..b', θ * φ θ) - M * ∫ θ in b..b', θ := by
    have : (fun θ => θ * (φ θ - M)) = fun θ => θ * φ θ - M * θ := by ext θ; ring
    rw [this, intervalIntegral.integral_sub i2 (intervalIntegral.intervalIntegrable_id.const_mul _),
      intervalIntegral.integral_const_mul]
  have hS := shocksWAvg_mul_eq (φ := φ) ha hab
  rw [shocksWAvg_of_lt hab', e2, eq_div_iff hW.ne', sub_mul, div_mul_cancel₀ _ hW.ne', ← eS,
    ← eW, hS]
  ring

/-- Extending `[a, b]` to the left:
`wavg(A, b) − wavg(a, b) = ∫_A^a θ(φ − wavg(a, b)) / W(A, b)`. -/
theorem shocksWAvg_extend_left (hφ : ContinuousOn φ (Icc c b)) {A : ℝ} (hA : 0 < A) (hcA : c ≤ A)
    (hAa : A ≤ a) (hab : a ≤ b) (hAb : A < b) :
    shocksWAvg φ A b - shocksWAvg φ a b =
      (∫ θ in A..a, θ * (φ θ - shocksWAvg φ a b)) / ∫ θ in A..b, θ := by
  set M := shocksWAvg φ a b
  have ha : 0 < a := hA.trans_le hAa
  have hW : 0 < ∫ θ in A..b, θ := by rw [shocks_integral_id]; nlinarith
  have i1 : IntervalIntegrable (fun θ => θ * φ θ) volume A a :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc hcA (hab)))).intervalIntegrable_of_Icc hAa
  have i2 : IntervalIntegrable (fun θ => θ * φ θ) volume a b :=
    (continuousOn_id.mul (hφ.mono (Icc_subset_Icc (hcA.trans hAa)
      le_rfl))).intervalIntegrable_of_Icc hab
  have eS := intervalIntegral.integral_add_adjacent_intervals i1 i2
  have eW := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegral.intervalIntegrable_id (a := A) (b := a) (μ := volume))
    (intervalIntegral.intervalIntegrable_id (a := a) (b := b) (μ := volume))
  have e2 : ∫ θ in A..a, θ * (φ θ - M) = (∫ θ in A..a, θ * φ θ) - M * ∫ θ in A..a, θ := by
    have : (fun θ => θ * (φ θ - M)) = fun θ => θ * φ θ - M * θ := by ext θ; ring
    rw [this, intervalIntegral.integral_sub i1 (intervalIntegral.intervalIntegrable_id.const_mul _),
      intervalIntegral.integral_const_mul]
  have hS := shocksWAvg_mul_eq (φ := φ) ha hab
  rw [shocksWAvg_of_lt hAb, e2, eq_div_iff hW.ne', sub_mul, div_mul_cancel₀ _ hW.ne', ← eS,
    ← eW, hS]
  ring

/-- The algebra of the extension bound: if `|N| ≤ d K |e|`, `W ≥ c w > 0` and `K = B w`, then
`|N/W| ≤ (d/c) B |e|`. -/
theorem shocks_abs_div_le {N W K e w B : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hw : 0 < w)
    (hB : 0 ≤ B) (hK : K = B * w) (hN : |N| ≤ d * K * |e|) (hW : c * w ≤ W) :
    |N / W| ≤ d / c * B * |e| := by
  have hW0 : 0 < W := (mul_pos hc hw).trans_le hW
  rw [abs_div, abs_of_pos hW0, div_le_iff₀ hW0]
  calc |N| ≤ d * K * |e| := hN
    _ = d / c * B * |e| * (c * w) := by rw [hK]; field_simp
    _ ≤ d / c * B * |e| * W := mul_le_mul_of_nonneg_left hW (by positivity)

/-- **Lipschitz in the right endpoint.** If `φ` is `B`-Lipschitz on `[c, d]`, `0 < c`, then for
`c ≤ a ≤ b ≤ b' ≤ d`: `|wavg(a, b') − wavg(a, b)| ≤ (d/c) B (b' − b)`. -/
theorem shocksWAvg_lip_right (hc : 0 < c) (hφc : ContinuousOn φ (Icc c d)) {B : ℝ}
    (hφ : ∀ s ∈ Icc c d, ∀ t ∈ Icc c d, |φ s - φ t| ≤ B * |s - t|) (hca : c ≤ a) (hab : a ≤ b)
    {b' : ℝ} (hbb : b ≤ b') (hbd : b' ≤ d) :
    |shocksWAvg φ a b' - shocksWAvg φ a b| ≤ d / c * B * (b' - b) := by
  rcases (hab.trans hbb).eq_or_lt with h | hab'
  · have h1 : b = b' := le_antisymm hbb (h ▸ hab)
    subst h1; simp
  have ha : 0 < a := hc.trans_le hca
  have hd : 0 ≤ d := ha.le.trans (hab.trans (hbb.trans hbd))
  have hB : 0 ≤ B := by
    have := hφ b' ⟨hca.trans (hab.trans hbb), hbd⟩ a ⟨hca, (hab.trans hbb).trans hbd⟩
    rw [abs_of_pos (sub_pos.2 hab')] at this
    nlinarith [abs_nonneg (φ b' - φ a)]
  rw [shocksWAvg_extend_right (hφc.mono (Icc_subset_Icc hca le_rfl)) ha hab hbb hbd hab']
  have hdev : ∀ θ ∈ Icc b b', |φ θ - shocksWAvg φ a b| ≤ B * (b' - a) := fun θ hθ =>
    abs_sub_shocksWAvg_le (hφc.mono (Icc_subset_Icc hca (hbb.trans hbd))) ha hab fun s hs => by
      refine (hφ θ ⟨hca.trans (hab.trans hθ.1), hθ.2.trans hbd⟩ s
        ⟨hca.trans hs.1, hs.2.trans (hbb.trans hbd)⟩).trans (mul_le_mul_of_nonneg_left ?_ hB)
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hθ.1, hθ.2]
  have hN : |∫ θ in b..b', θ * (φ θ - shocksWAvg φ a b)| ≤ d * (B * (b' - a)) * |b' - b| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le hbb] at hθ
    have h0 : 0 < θ := ha.trans_le (hab.trans hθ.1.le)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h0]
    exact mul_le_mul (hθ.2.trans hbd) (hdev θ (Ioc_subset_Icc_self hθ)) (abs_nonneg _) hd
  have := shocks_abs_div_le hc hd (sub_pos.2 hab') hB rfl hN
    ((mul_le_mul_of_nonneg_right hca (sub_pos.2 hab').le).trans
      (shocks_integral_id_ge ha.le hab'.le))
  rwa [abs_of_nonneg (sub_nonneg.2 hbb)] at this

/-- **Lipschitz in the left endpoint.** If `φ` is `B`-Lipschitz on `[c, d]`, `0 < c`, then for
`c ≤ A ≤ a ≤ b ≤ d`: `|wavg(A, b) − wavg(a, b)| ≤ (d/c) B (a − A)`. -/
theorem shocksWAvg_lip_left (hc : 0 < c) (hφc : ContinuousOn φ (Icc c d)) {B : ℝ}
    (hφ : ∀ s ∈ Icc c d, ∀ t ∈ Icc c d, |φ s - φ t| ≤ B * |s - t|) {A : ℝ} (hcA : c ≤ A)
    (hAa : A ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    |shocksWAvg φ A b - shocksWAvg φ a b| ≤ d / c * B * (a - A) := by
  rcases (hAa.trans hab).eq_or_lt with h | hAb
  · have h1 : A = a := le_antisymm hAa (h ▸ hab)
    subst h1; simp
  have hA : 0 < A := hc.trans_le hcA
  have ha : 0 < a := hA.trans_le hAa
  have hd : 0 ≤ d := ha.le.trans (hab.trans hbd)
  have hB : 0 ≤ B := by
    have := hφ b ⟨hcA.trans (hAa.trans hab), hbd⟩ A ⟨hcA, (hAa.trans hab).trans hbd⟩
    rw [abs_of_pos (sub_pos.2 hAb)] at this
    nlinarith [abs_nonneg (φ b - φ A)]
  rw [shocksWAvg_extend_left (hφc.mono (Icc_subset_Icc le_rfl hbd)) hA hcA hAa hab hAb]
  have hdev : ∀ θ ∈ Icc A a, |φ θ - shocksWAvg φ a b| ≤ B * (b - A) := fun θ hθ =>
    abs_sub_shocksWAvg_le (hφc.mono (Icc_subset_Icc (hcA.trans hAa) hbd)) ha hab fun s hs => by
      refine (hφ θ ⟨hcA.trans hθ.1, hθ.2.trans (hab.trans hbd)⟩ s
        ⟨hcA.trans (hAa.trans hs.1), hs.2.trans hbd⟩).trans (mul_le_mul_of_nonneg_left ?_ hB)
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hθ.1, hθ.2]
  have hN : |∫ θ in A..a, θ * (φ θ - shocksWAvg φ a b)| ≤ d * (B * (b - A)) * |a - A| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le hAa] at hθ
    have h0 : 0 < θ := hA.trans hθ.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h0]
    exact mul_le_mul (hθ.2.trans (hab.trans hbd)) (hdev θ (Ioc_subset_Icc_self hθ)) (abs_nonneg _)
      hd
  have := shocks_abs_div_le hc hd (sub_pos.2 hAb) hB rfl hN
    ((mul_le_mul_of_nonneg_right hcA (sub_pos.2 hAb).le).trans
      (shocks_integral_id_ge hA.le hAb.le))
  rwa [abs_of_nonneg (sub_nonneg.2 hAa)] at this

/-- **The weighted average is Lipschitz in both endpoints.** If `φ` is `B`-Lipschitz on `[c, d]`,
`0 < c`, then `|wavg(a, b) − wavg(a', b')| ≤ (d/c) B (|a − a'| + |b − b'|)` for subintervals
`[a, b]`, `[a', b']` of `[c, d]`. (This is the direct uniform bound replacing the book's
L'Hôpital argument in Step 4 of Proposition 7.) -/
theorem shocksWAvg_lipschitz (hc : 0 < c) (hφc : ContinuousOn φ (Icc c d)) {B : ℝ}
    (hφ : ∀ s ∈ Icc c d, ∀ t ∈ Icc c d, |φ s - φ t| ≤ B * |s - t|) {a' b' : ℝ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hca' : c ≤ a') (hab' : a' ≤ b') (hbd' : b' ≤ d) :
    |shocksWAvg φ a b - shocksWAvg φ a' b'| ≤ d / c * B * (|a - a'| + |b - b'|) := by
  set A := min a a'
  set E := max b b'
  have hcA : c ≤ A := le_min hca hca'
  have hEd : E ≤ d := max_le hbd hbd'
  have h1 := shocksWAvg_lip_right hc hφc hφ hca hab (le_max_left b b') hEd
  have h2 := shocksWAvg_lip_left hc hφc hφ hcA (min_le_left a a') (hab.trans (le_max_left b b'))
    hEd
  have h3 := shocksWAvg_lip_right hc hφc hφ hca' hab' (le_max_right b b') hEd
  have h4 := shocksWAvg_lip_left hc hφc hφ hcA (min_le_right a a')
    (hab'.trans (le_max_right b b')) hEd
  have e1 : (E - b) + (E - b') = |b - b'| := by
    simp only [E]; rcases le_total b b' with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.2 h)]; ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.2 h)]; ring
  have e2 : (a - A) + (a' - A) = |a - a'| := by
    simp only [A]; rcases le_total a a' with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
  rw [← e1, ← e2]
  set K := d / c * B
  have k1 := abs_le.1 h1
  have k2 := abs_le.1 h2
  have k3 := abs_le.1 h3
  have k4 := abs_le.1 h4
  rw [abs_le]
  constructor <;> nlinarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2, k4.1, k4.2]

/-! ### The uniform model: (6a)–(6b) with the correct weights -/

variable {xlo xhi θlo θhi : ℝ}

/-- `a(z)` is Lipschitz on `z ≥ z₀ > 0` with constant `x̲/z₀²`. -/
theorem shocksA_lipschitz {z₀ z z' : ℝ} (hx : 0 ≤ xlo) (hz₀ : 0 < z₀) (hz : z₀ ≤ z)
    (hz' : z₀ ≤ z') : |shocksA xlo θlo z - shocksA xlo θlo z'| ≤ xlo / z₀ ^ 2 * |z - z'| := by
  have h0 : 0 < z := hz₀.trans_le hz
  have h0' : 0 < z' := hz₀.trans_le hz'
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [div_sub_div _ _ h0.ne' h0'.ne', abs_div, abs_of_pos (mul_pos h0 h0'),
    show xlo * z' - z * xlo = xlo * (z' - z) by ring, abs_mul, abs_of_nonneg hx, abs_sub_comm,
    div_le_iff₀ (mul_pos h0 h0')]
  have h1 : z₀ ^ 2 ≤ z * z' := by nlinarith
  calc xlo * |z - z'| = xlo / z₀ ^ 2 * |z - z'| * z₀ ^ 2 := by field_simp
    _ ≤ xlo / z₀ ^ 2 * |z - z'| * (z * z') :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `b(z)` is Lipschitz on `z ≥ z₀ > 0` with constant `x̄/z₀²`. -/
theorem shocksB_lipschitz {z₀ z z' : ℝ} (hx : 0 ≤ xhi) (hz₀ : 0 < z₀) (hz : z₀ ≤ z)
    (hz' : z₀ ≤ z') : |shocksB xhi θhi z - shocksB xhi θhi z'| ≤ xhi / z₀ ^ 2 * |z - z'| := by
  have h0 : 0 < z := hz₀.trans_le hz
  have h0' : 0 < z' := hz₀.trans_le hz'
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
  rw [div_sub_div _ _ h0.ne' h0'.ne', abs_div, abs_of_pos (mul_pos h0 h0'),
    show xhi * z' - z * xhi = xhi * (z' - z) by ring, abs_mul, abs_of_nonneg hx, abs_sub_comm,
    div_le_iff₀ (mul_pos h0 h0')]
  have h1 : z₀ ^ 2 ≤ z * z' := by nlinarith
  calc xhi * |z - z'| = xhi / z₀ ^ 2 * |z - z'| * z₀ ^ 2 := by field_simp
    _ ≤ xhi / z₀ ^ 2 * |z - z'| * (z * z') :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- On `Z`, `θ̲ ≤ a(z) ≤ b(z) ≤ θ̄`. -/
theorem shocksA_shocksB_mem (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) :
    θlo ≤ shocksA xlo θlo z ∧ shocksA xlo θlo z ≤ shocksB xhi θhi z ∧
      shocksB xhi θhi z ≤ θhi := by
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hz0 : 0 < z := (div_pos hx0 hθhi).trans_le hz.1
  refine ⟨le_max_right _ _, max_le (le_min (div_le_div_of_nonneg_right hx.le hz0.le) ?_)
    (le_min ?_ hθ.le), min_le_right _ _⟩
  · rw [div_le_iff₀ hz0]; have := (div_le_iff₀ hθhi).1 hz.1; linarith
  · rw [le_div_iff₀ hz0]; have := (le_div_iff₀ hθ0).1 hz.2; linarith

/-- **(6a)–(6b), corrected** (p. 537). Under Assumptions 17.5 and 17.6, for every `z ∈ Z` and
every `k`, `∫ k dG(·|z)` is the `θ`-weighted average of `k` over `[a(z), b(z)]` (at `z̲`, `z̄`
the interval degenerates to `{θ̄}`, `{θ̲}`, which is (6b)). The book's (6a) has the unweighted
average `(b − a)⁻¹ ∫_a^b`, which is wrong (`ex_17_12_counterexample`). -/
theorem shocksUnif_integral_condLaw (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo)
    (hθ : θlo < θhi) (hθ2 : θhi < 2) {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo))
    (k : ℝ → ℝ) :
    ∫ θ, k θ ∂shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z =
      shocksWAvg k (shocksA xlo θlo z) (shocksB xhi θhi z) := by
  have hA := shocksUnif_assumption17_5 hx0 hx hθ0 hθ hθ2
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hxhi : 0 < xhi := hx0.trans hx
  by_cases hzZ : xlo / θhi < z ∧ z < xhi / θlo
  · have hπ := hA.pi_pos (fun x hx' => by rw [shocksUnif, indicator_of_mem hx']; simp [hx])
      (fun θ hθ' => by rw [shocksUnif, indicator_of_mem hθ']; simp [hθ]) hzZ
    obtain ⟨-, hab⟩ := shocksA_lt_shocksB hx0 hx hθ0 hθ hzZ
    have ha0 : 0 < shocksA xlo θlo z := hθ0.trans_le (le_max_right _ _)
    rw [hA.integral_condLaw hzZ hπ]
    simp_rw [ex_17_12 hx0 hx hθ0 hθ hzZ]
    have e : (fun θ => k θ * (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => 2 * θ / (shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2)) θ) =
        (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => 2 / (shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2) * (θ * k θ)) := by
      ext θ
      by_cases h : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
      · rw [indicator_of_mem h, indicator_of_mem h]; ring
      · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_const_mul,
      shocksWAvg_of_lt hab, shocks_integral_id]
    field_simp
  · rcases eq_or_lt_of_le hz.1 with h | h
    · subst h
      have h1 : shocksA xlo θlo (xlo / θhi) = θhi := by
        simp only [shocksA]; rw [div_div_cancel₀ hx0.ne']; exact max_eq_left hθ.le
      have h2 : shocksB xhi θhi (xlo / θhi) = θhi := by
        simp only [shocksB]; refine min_eq_right ?_
        rw [le_div_iff₀ (div_pos hx0 hθhi), mul_div_assoc', div_le_iff₀ hθhi]
        nlinarith
      simp only [shocksCondLaw, lt_irrefl, false_and, ↓reduceIte, le_refl, integral_dirac, h1,
        h2, shocksWAvg]
    · have h3 : z = xhi / θlo := by
        by_contra h3
        exact hzZ ⟨h, lt_of_le_of_ne hz.2 h3⟩
      subst h3
      have hZ : xlo / θhi < xhi / θlo := h
      have h1 : shocksA xlo θlo (xhi / θlo) = θlo := by
        simp only [shocksA]; refine max_eq_right ?_
        rw [div_le_iff₀ (div_pos hxhi hθ0), mul_div_assoc', le_div_iff₀ hθ0]
        nlinarith
      have h2 : shocksB xhi θhi (xhi / θlo) = θlo := by
        simp only [shocksB]; rw [div_div_cancel₀ hxhi.ne']; exact min_eq_left hθ.le
      simp only [shocksCondLaw, lt_irrefl, and_false, ↓reduceIte, not_le.mpr hZ, integral_dirac,
        h1, h2, shocksWAvg]

/-! ### Exercises 17.11 and 17.13 -/

variable {Z : Type*} {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- The book's Assumption 17.1 for `V` implies the repaired one, so results proved under
`Assumption17_1VR` hold under Assumption 17.1 as stated. -/
theorem shocks_assumption17_1VR_of_V (hV : Assumption17_1V V V' V'') :
    Assumption17_1VR V V' V'' :=
  ⟨hV.V_nonneg, hV.V_continuousOn, fun _ hy => hV.V_hasDerivAt hy,
    fun y hy => (hV.V'_deriv y hy.le).hasDerivAt (Ici_mem_nhds hy),
    hV.V''_cont.mono Ioi_subset_Ici_self, hV.V_mono, hV.V_conc⟩

namespace ShocksBounds

variable {l₀ l : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'')
include hS

/-- `φ` is Lipschitz on `[(θ̲/θ̄) l, (θ̄/θ̲) L]` (mean value theorem; `φ' = V' + yV''` is
continuous on `ℝ₊₊`). -/
theorem exists_phi_lipschitz (hl : l ∈ Ioc 0 l₀) : ∃ M, 0 ≤ M ∧
    ∀ y ∈ Icc (θlo / θhi * l) (θhi / θlo * L), ∀ y' ∈ Icc (θlo / θhi * l) (θhi / θlo * L),
      |olgPhi V' y - olgPhi V' y'| ≤ M * |y - y'| := by
  obtain ⟨ha, -⟩ := hS.ratio_bounds
  have hpos : ∀ y ∈ Icc (θlo / θhi * l) (θhi / θlo * L), 0 < y := fun y hy =>
    (mul_pos ha hl.1).trans_le hy.1
  have hc : ContinuousOn (fun y => V' y + y * V'' y) (Icc (θlo / θhi * l) (θhi / θlo * L)) :=
    (hS.hV.V'_continuousOn.mono fun y hy => hpos y hy).add
      (continuousOn_id.mul (hS.hV.V''_cont.mono fun y hy => hpos y hy))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun y hy y' hy' => ?_⟩
  have := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := olgPhi V') (f' := fun y => V' y + y * V'' y)
    (fun x hx => (hS.hV.phi_hasDerivAt (hpos x hx)).hasDerivWithinAt)
    (fun x hx => (hM x hx).trans (le_max_left M 0)) hy' hy
  simpa only [Real.norm_eq_abs] using this

/-- **Exercise 17.13** (p. 537), in Lipschitz form: there is `K` such that every `φ_f`,
`f ∈ F = {f : ζ(l) ≤ f}`, is `K`-Lipschitz on `Θ`, for every law `μ` of `(θ′, z′)`
(`K = M L θ̄/θ̲²`, `M` a bound for `|φ'|` on `[(θ̲/θ̄) l, (θ̄/θ̲) L]`; the manual's
`(θ̄/θ̲²) L max|φ'|`). -/
theorem ex_17_13 [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (hl : l ∈ Ioc 0 l₀) : ∃ K, 0 ≤ K ∧ ∀ (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
      (f : Z → ℝ), Continuous f → (∀ z, olgZeta H' l ≤ f z) →
      ∀ s ∈ Icc θlo θhi, ∀ t ∈ Icc θlo θhi,
        |shocksPhiF L H' V' θlo θhi μ f s - shocksPhiF L H' V' θlo θhi μ f t| ≤ K * |s - t| := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  obtain ⟨M, hM0, hM⟩ := hS.exists_phi_lipschitz hl
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le (Z := Z) hl
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩
  have hθ0 := hS.θlo_pos
  have hθhi : 0 < θhi := hθ0.trans_le hS.θlo_le
  refine ⟨M * (L * θhi / θlo ^ 2), mul_nonneg hM0 (by have := hS.hH.L_pos; positivity),
    fun μ _ f hfc hfl s hs t ht => ?_⟩
  have hpt : ∀ ω : ℝ × Z, |shocksIntegrand L H' V' θlo θhi f s ω -
      shocksIntegrand L H' V' θlo θhi f t ω| ≤ M * (L * θhi / θlo ^ 2) * |s - t| := fun ω => by
    have hy0 : 0 ≤ f ω.2 := (hS.zeta_pos hl).le.trans (hfl ω.2)
    have hm := hS.hH.zetaInv_mem hy0
    set m := olgZetaInv L H' (f ω.2)
    have hlm : l ≤ m := by
      have := hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hS.zeta_pos hl).le)
        (mem_Ici.2 hy0) (hfl ω.2)
      rwa [hS.hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
    have hmem : ∀ u, shocksRatio θlo θhi ω.1 u * m ∈ Icc (θlo / θhi * l) (θhi / θlo * L) :=
      fun u => by
        have hr := shocksRatio_mem hθ0 hS.θlo_le ω.1 u
        exact ⟨mul_le_mul hr.1 hlm hl.1.le (ha.le.trans hr.1),
          mul_le_mul hr.2 hm.2.le hm.1 (ha.le.trans hab)⟩
    refine (hM _ (hmem s) _ (hmem t)).trans ?_
    have hc := shocksClamp_mem hS.θlo_le ω.1
    have hs0 : 0 < s := hθ0.trans_le hs.1
    have ht0 : 0 < t := hθ0.trans_le ht.1
    have e : shocksRatio θlo θhi ω.1 s * m - shocksRatio θlo θhi ω.1 t * m =
        shocksClamp θlo θhi ω.1 * m * (t - s) / (s * t) := by
      simp only [shocksRatio, shocksClamp_of_mem hs, shocksClamp_of_mem ht]
      field_simp
    suffices hd : |shocksRatio θlo θhi ω.1 s * m - shocksRatio θlo θhi ω.1 t * m| ≤
        L * θhi / θlo ^ 2 * |s - t| by
      calc M * |shocksRatio θlo θhi ω.1 s * m - shocksRatio θlo θhi ω.1 t * m|
          ≤ M * (L * θhi / θlo ^ 2 * |s - t|) := mul_le_mul_of_nonneg_left hd hM0
        _ = M * (L * θhi / θlo ^ 2) * |s - t| := by ring
    rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hs0 ht0), abs_of_nonneg (mul_nonneg
      (hθ0.le.trans hc.1) hm.1), abs_sub_comm t s]
    rw [div_le_iff₀ (mul_pos hs0 ht0)]
    have h1 : θlo ^ 2 ≤ s * t := by nlinarith [hs.1, ht.1]
    have h2 : shocksClamp θlo θhi ω.1 * m ≤ θhi * L :=
      mul_le_mul hc.2 hm.2.le hm.1 hθhi.le
    calc shocksClamp θlo θhi ω.1 * m * |s - t| ≤ θhi * L * |s - t| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ = L * θhi / θlo ^ 2 * |s - t| * θlo ^ 2 := by field_simp
      _ ≤ L * θhi / θlo ^ 2 * |s - t| * (s * t) :=
          mul_le_mul_of_nonneg_left h1 (by have := hS.hH.L_pos; positivity)
  simp only [shocksPhiF]
  rw [← integral_sub (hS.integrable_integrand hl hB hfc hfl μ s)
    (hS.integrable_integrand hl hB hfc hfl μ t), ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := M * (L * θhi / θlo ^ 2) * |s - t|)
    (f := fun ω => shocksIntegrand L H' V' θlo θhi f s ω - shocksIntegrand L H' V' θlo θhi f t ω)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
  simpa using this

/-- **Exercise 17.11, Step 3** (p. 536): `T` is uniformly continuous on
`F = {f ∈ C(Z) : ζ(l) ≤ f ≤ B}`, uniformly over the laws `μ`, `ν` (uniform continuity of
`(r, y) ↦ φ(r ζ⁻¹(y))` on the compact `[θ̲/θ̄, θ̄/θ̲] × [ζ(l), B]`, as in Exercise 17.6). -/
theorem ex_17_11_step3 [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (hl : l ∈ Ioc 0 l₀) {B : ℝ} (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) :
    ∀ ε > 0, ∃ δ > 0, ∀ f g : Z → ℝ, Continuous f → Continuous g →
      (∀ z, olgZeta H' l ≤ f z ∧ f z ≤ B) → (∀ z, olgZeta H' l ≤ g z ∧ g z ≤ B) →
      (∀ z, |f z - g z| < δ) → ∀ (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
        (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] (z : Z),
        |shocksOpT L H' V' θlo θhi μ ν f z - shocksOpT L H' V' θlo θhi μ ν g z| ≤ ε := by
  intro ε hε
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hzl := hS.zeta_pos hl
  set K : Set (ℝ × ℝ) := Icc (θlo / θhi) (θhi / θlo) ×ˢ Icc (olgZeta H' l) B
  have hcont : ContinuousOn (fun p : ℝ × ℝ => olgPhi V' (p.1 * olgZetaInv L H' p.2)) K := by
    refine hS.hV.phi_continuousOn.comp (continuousOn_fst.mul
      (hS.hH.zetaInv_continuousOn.comp continuousOn_snd fun p hp => mem_Ici.2
        (hzl.le.trans hp.2.1))) fun p hp => ?_
    exact mul_pos (ha.trans_le hp.1.1) (hS.hH.zetaInv_pos (hzl.trans_le hp.2.1))
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨δ, hδ, fun f g hfc hgc hf hg hfg μ _ ν _ z => ?_⟩
  have hfl : ∀ z, olgZeta H' l ≤ f z := fun z => (hf z).1
  have hgl : ∀ z, olgZeta H' l ≤ g z := fun z => (hg z).1
  have hpt : ∀ θt (ω : ℝ × Z), |shocksIntegrand L H' V' θlo θhi f θt ω -
      shocksIntegrand L H' V' θlo θhi g θt ω| ≤ ε := fun θt ω => by
    have hr := shocksRatio_mem hS.θlo_pos hS.θlo_le ω.1 θt
    have := hu (shocksRatio θlo θhi ω.1 θt, f ω.2) ⟨hr, hf ω.2⟩
      (shocksRatio θlo θhi ω.1 θt, g ω.2) ⟨hr, hg ω.2⟩ (by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        exact max_lt hδ (hfg ω.2))
    rw [Real.dist_eq] at this
    exact this.le
  have hφ : ∀ θt, |shocksPhiF L H' V' θlo θhi μ f θt - shocksPhiF L H' V' θlo θhi μ g θt| ≤ ε :=
    fun θt => by
      simp only [shocksPhiF]
      rw [← integral_sub (hS.integrable_integrand hl hB hfc hfl μ θt)
        (hS.integrable_integrand hl hB hgc hgl μ θt), ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := μ) (C := ε)
        (f := fun ω => shocksIntegrand L H' V' θlo θhi f θt ω -
          shocksIntegrand L H' V' θlo θhi g θt ω)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt θt ω)
      simpa using this
  have i1 : Integrable (shocksPhiF L H' V' θlo θhi μ f) (ν z) :=
    (hS.phiFBCF hl hB hfc hfl μ).integrable (ν z)
  have i2 : Integrable (shocksPhiF L H' V' θlo θhi μ g) (ν z) :=
    (hS.phiFBCF hl hB hgc hgl μ).integrable (ν z)
  simp only [shocksOpT]
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := ν z) (C := ε)
    (f := fun θt => shocksPhiF L H' V' θlo θhi μ f θt - shocksPhiF L H' V' θlo θhi μ g θt)
    (ae_of_all _ fun θt => by rw [Real.norm_eq_abs]; exact hφ θt)
  simpa using this

end ShocksBounds

/-! ### Proposition 7 by Schauder's theorem -/

/-- **Step 4 of Proposition 7, with the correct weights** (pp. 537–539). Under Assumptions 17.5
and 17.6, if every `φ_f` is `K`-Lipschitz on `Θ` (Exercise 17.13), then every `Tf` is
Lipschitz on `Z` with the common constant `(θ̄/θ̲) K (x̲ + x̄)/z̲²`. This replaces the book's
piecewise derivative bound and its circular L'Hôpital step at `z̲`, `z̄` by the direct estimate
`shocksWAvg_lipschitz` (valid across the kinks of `a`, `b` and at the endpoints). -/
theorem shocksUnif_opT_lipschitz (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo)
    (hθ : θlo < θhi) (hθ2 : θhi < 2) (μ : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo)))
    (f : Icc (xlo / θhi) (xhi / θlo) → ℝ) {K : ℝ}
    (hφc : ContinuousOn (shocksPhiF L H' V' θlo θhi μ f) (Icc θlo θhi))
    (hφ : ∀ s ∈ Icc θlo θhi, ∀ t ∈ Icc θlo θhi,
      |shocksPhiF L H' V' θlo θhi μ f s - shocksPhiF L H' V' θlo θhi μ f t| ≤ K * |s - t|)
    (z z' : Icc (xlo / θhi) (xhi / θlo)) :
    |shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi)
        (shocksUnif θlo θhi) z.1) f z -
      shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi)
        (shocksUnif θlo θhi) z.1) f z'| ≤
      θhi / θlo * K * ((xlo + xhi) / (xlo / θhi) ^ 2) * dist z z' := by
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hzlo : 0 < xlo / θhi := div_pos hx0 hθhi
  have hK : 0 ≤ K := by
    have := hφ θhi ⟨hθ.le, le_rfl⟩ θlo ⟨le_rfl, hθ.le⟩
    rw [abs_of_pos (sub_pos.2 hθ)] at this
    nlinarith [abs_nonneg (shocksPhiF L H' V' θlo θhi μ f θhi -
      shocksPhiF L H' V' θlo θhi μ f θlo)]
  simp only [shocksOpT]
  rw [shocksUnif_integral_condLaw hx0 hx hθ0 hθ hθ2 z.2,
    shocksUnif_integral_condLaw hx0 hx hθ0 hθ hθ2 z'.2]
  obtain ⟨h1, h2, h3⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ z.2
  obtain ⟨h1', h2', h3'⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ z'.2
  refine (shocksWAvg_lipschitz hθ0 hφc hφ h1 h2 h3 h1' h2' h3').trans ?_
  have ha := shocksA_lipschitz (θlo := θlo) hx0.le hzlo z.2.1 z'.2.1
  have hb := shocksB_lipschitz (θhi := θhi) (hx0.trans hx).le hzlo z.2.1 z'.2.1
  rw [Subtype.dist_eq, Real.dist_eq]
  have hC : 0 ≤ θhi / θlo * K := by positivity
  calc θhi / θlo * K * (|shocksA xlo θlo z - shocksA xlo θlo z'| +
        |shocksB xhi θhi z - shocksB xhi θhi z'|)
      ≤ θhi / θlo * K * (xlo / (xlo / θhi) ^ 2 * |z.1 - z'.1| +
        xhi / (xlo / θhi) ^ 2 * |z.1 - z'.1|) := mul_le_mul_of_nonneg_left (add_le_add ha hb) hC
    _ = θhi / θlo * K * ((xlo + xhi) / (xlo / θhi) ^ 2) * |z.1 - z'.1| := by ring

/-- **Proposition 7** (p. 536), corrected. Let `H` satisfy Assumption 17.1 and `V` the (repaired,
weaker) utility part of Assumption 17.1, `Ψ`, `G` uniform on `X = [x̲, x̄]`, `Θ = [θ̲, θ̄]`
(Assumptions 17.5, 17.6), `G(·|z)` the correct conditional law (density `2θ/(b² − a²)` on
`[a(z), b(z)]`, Exercise 17.12 corrected) and `μ` any probability law of `(θ′, z′)` (e.g. their
joint law, `shocksJointLaw`). Then `T` has a continuous fixed point bounded away from zero.
(The book's "a fixed point in `C(Z)`" is trivial: `T0 = 0`, `proposition_6_zero_fixedPoint`.)

Proof (Schauder, `schauder_closed`): `F = {f : ζ(l₀) ≤ f ≤ B}` is closed, bounded, convex and
nonempty; `T(F) ⊆ F` (`ShocksBounds.opT_mem`, Exercise 17.11 Steps 1–2); `T` is continuous
(`ShocksBounds.ex_17_11_step3`); `T(F)` is uniformly Lipschitz (`ShocksBounds.ex_17_13` and
`shocksUnif_opT_lipschitz`), hence equicontinuous. -/
theorem proposition_7 (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    (hθ2 : θhi < 2) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (μ : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo))) [IsProbabilityMeasure μ] :
    ∃ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∃ ε > 0, ∀ z, ε ≤ f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi
        (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1) f z := by
  classical
  set ν : Icc (xlo / θhi) (xhi / θlo) → Measure ℝ := fun z =>
    shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1
  have hA := shocksUnif_assumption17_5 hx0 hx hθ0 hθ hθ2
  have hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo →
      0 < shocksPi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z := fun z hz =>
    hA.pi_pos (fun x hx' => by rw [shocksUnif, indicator_of_mem hx']; simp [hx])
      (fun θ hθ' => by rw [shocksUnif, indicator_of_mem hθ']; simp [hθ]) hz
  have hνp : ∀ z : Icc (xlo / θhi) (xhi / θlo), IsProbabilityMeasure (ν z) := fun z =>
    hA.isProbabilityMeasure_condLaw' hπ z.1
  have hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z : Icc (xlo / θhi) (xhi / θlo) => ∫ θ, h θ ∂ν z :=
    fun h => (hA.ex_17_8b hπ h).domRestrict
  obtain ⟨l₀, hS⟩ := shocksBounds_exists hθ0 hθ.le hH hV
  have hl : l₀ ∈ Ioc 0 l₀ := ⟨hS.l₀_mem.1, le_rfl⟩
  obtain ⟨B, hB0, hB⟩ := hS.exists_integrand_le (Z := Icc (xlo / θhi) (xhi / θlo)) hl
  obtain ⟨K, -, hK⟩ := hS.ex_17_13 (Z := Icc (xlo / θhi) (xhi / θlo)) hl
  have hzl := hS.zeta_pos hl
  set F : Set (Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) :=
    {f | ∀ z, f z ∈ Icc (olgZeta H' l₀) B} with hF
  have hTc : ∀ f ∈ F, Continuous (shocksOpT L H' V' θlo θhi μ ν f) := fun f hf =>
    (hS.opT_mem hl hB f.continuous (fun z => (hf z).1) μ ν hν).1
  have hTb : ∀ f ∈ F, ∀ z, ‖shocksOpT L H' V' θlo θhi μ ν f z‖ ≤ B := fun f hf z => by
    have h := (hS.opT_mem hl hB f.continuous (fun z => (hf z).1) μ ν hν).2 z
    rw [Real.norm_eq_abs, abs_of_pos (hzl.trans_le h.1)]
    exact h.2
  set T : (Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) → (Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) :=
    fun f => if hf : f ∈ F then
      ofNormedAddCommGroup (shocksOpT L H' V' θlo θhi μ ν f) (hTc f hf) B (hTb f hf) else f
  have hTF : ∀ f ∈ F, ⇑(T f) = shocksOpT L H' V' θlo θhi μ ν f := fun f hf => by
    simp only [T, hf, ↓reduceDIte, coe_ofNormedAddCommGroup]
  have hFcl : IsClosed F := by
    have : F = ⋂ z, (fun f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ => f z) ⁻¹'
        Icc (olgZeta H' l₀) B := by
      ext f; simp [hF]
    rw [this]
    exact isClosed_iInter fun z => isClosed_Icc.preimage ((continuous_apply z).comp
      continuous_coe)
  have hFconv : Convex ℝ F := fun f hf g hg a b ha hb hab z => by
    simpa using (convex_Icc _ _) (hf z) (hg z) ha hb hab
  have hFb : Bornology.IsBounded F := isBounded_iff_forall_norm_le.2
    ⟨B, fun f hf => (norm_le hB0.le).2 fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hzl.trans_le (hf z).1)]; exact (hf z).2⟩
  have hz₀ : xlo / θhi ∈ Icc (xlo / θhi) (xhi / θlo) :=
    left_mem_Icc.2 (div_le_div₀ (hx0.trans hx).le hx.le hθ0 hθ.le)
  have hFne : F.Nonempty := ⟨const _ (olgZeta H' l₀), fun _ =>
    ⟨le_rfl, (hS.integrand_ge hl (f := fun _ : Icc (xlo / θhi) (xhi / θlo) => olgZeta H' l₀)
      (θt := 0) (ω := (0, ⟨_, hz₀⟩)) le_rfl).trans (hB _ _ _ le_rfl)⟩⟩
  have hmaps : MapsTo T F F := fun f hf z => by
    rw [hTF f hf]
    exact (hS.opT_mem hl hB f.continuous (fun z => (hf z).1) μ ν hν).2 z
  have hcont : ContinuousOn T F := by
    refine Metric.continuousOn_iff.2 fun g hg ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hS.ex_17_11_step3 (Z := Icc (xlo / θhi) (xhi / θlo)) hl hB (ε / 2)
      (half_pos hε)
    refine ⟨δ, hδ, fun f hf hfg => ?_⟩
    have hle : dist (T f) (T g) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun z => ?_
      rw [hTF f hf, hTF g hg, Real.dist_eq]
      exact h f g f.continuous g.continuous hf hg (fun z => by
        rw [← Real.dist_eq]; exact (dist_coe_le_dist z).trans_lt hfg) μ ν z
    linarith
  have hequi : ∀ ε > 0, ∃ δ > 0, ∀ x y : Icc (xlo / θhi) (xhi / θlo), dist x y < δ →
      ∀ g ∈ T '' F, |g x - g y| < ε := by
    intro ε hε
    set C := θhi / θlo * K * ((xlo + xhi) / (xlo / θhi) ^ 2)
    refine ⟨ε / (|C| + 1), by positivity, fun x y hxy => ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rw [hTF f hf]
    have hfl : ∀ z, olgZeta H' l₀ ≤ f z := fun z => (hf z).1
    have h := shocksUnif_opT_lipschitz hx0 hx hθ0 hθ hθ2 μ f
      ((hS.continuous_phiF hl hB f.continuous hfl μ).continuousOn)
      (hK μ f f.continuous hfl) x y
    calc _ ≤ C * dist x y := h
      _ ≤ |C| * dist x y := mul_le_mul_of_nonneg_right (le_abs_self C) dist_nonneg
      _ ≤ |C| * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left hxy.le (abs_nonneg _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg C]
  have htb := totallyBounded_of_equicontinuous isCompact_univ.totallyBounded
    (hFb.subset hmaps.image_subset) hequi
  obtain ⟨f, hf, hTf⟩ := schauder_closed hFcl hFconv hFne hcont hmaps
    (htb.closure.isCompact_of_isClosed isClosed_closure)
  refine ⟨f, ⟨olgZeta H' l₀, hzl, fun z => (hf z).1⟩, fun z => ?_⟩
  have := congrArg (fun g : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ => g z) hTf
  rw [← this, hTF f hf]

/-- **Proposition 7 for the islands model**, under the book's Assumption 17.1 and uniform
`Ψ`, `G`, with `μ` the joint law of `(θ′, z′)`: `T` has a continuous fixed point bounded away from
zero. -/
theorem proposition_7_islands (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    (hθ2 : θhi < 2) (hA1 : Assumption17_1 L H H' H'' V V' V'') (hZ : xlo / θhi ≤ xhi / θlo) :
    ∃ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∃ ε > 0, ∀ z, ε ≤ f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi
        (shocksJointLaw xlo xhi θlo θhi hZ (shocksUnif xlo xhi) (shocksUnif θlo θhi))
        (fun z => shocksCondLaw xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1)
        f z := by
  have := isProbabilityMeasure_shocksJointLaw (shocksUnif_assumption17_5 hx0 hx hθ0 hθ hθ2) hZ
  exact proposition_7 hx0 hx hθ0 hθ hθ2 hA1.hH (shocks_assumption17_1VR_of_V hA1.hV) _

/-! ### (7), corrected -/

/-- **(7), corrected, abstract form.** If `φ` is continuous, `A`, `B` are differentiable at `z`
with `0 < A(z) < B(z)`, and `W(w) = wavg(φ; A(w), B(w))` (the `θ`-weighted average), then
`W'(z) = [B B′ (φ(B) − W) − A A′ (φ(A) − W)] / ((B² − A²)/2)`, all at `z`. -/
theorem shocksWAvg_hasDerivAt {φ : ℝ → ℝ} (hφ : Continuous φ) {A Bf : ℝ → ℝ} {z a' b' : ℝ}
    (ha : HasDerivAt A a' z) (hb : HasDerivAt Bf b' z) (ha0 : 0 < A z) (hab : A z < Bf z) :
    HasDerivAt (fun w => shocksWAvg φ (A w) (Bf w))
      ((Bf z * b' * (φ (Bf z) - shocksWAvg φ (A z) (Bf z)) -
          A z * a' * (φ (A z) - shocksWAvg φ (A z) (Bf z))) / ((Bf z ^ 2 - A z ^ 2) / 2)) z := by
  have hc : Continuous fun θ : ℝ => θ * φ θ := continuous_id.mul hφ
  set G : ℝ → ℝ := fun u => ∫ θ in (0 : ℝ)..u, θ * φ θ
  have hG : ∀ u, HasDerivAt G (u * φ u) u := fun u => (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hS : HasDerivAt (fun w => G (Bf w) - G (A w))
      (Bf z * φ (Bf z) * b' - A z * φ (A z) * a') z :=
    ((hG (Bf z)).comp z hb).sub ((hG (A z)).comp z ha)
  have hN : HasDerivAt (fun w => (Bf w ^ 2 - A w ^ 2) / 2) (Bf z * b' - A z * a') z := by
    have := ((hb.pow 2).sub (ha.pow 2)).div_const 2
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hN0 : (Bf z ^ 2 - A z ^ 2) / 2 ≠ 0 := by nlinarith
  have hq := hS.div hN hN0
  have hev : (fun w => shocksWAvg φ (A w) (Bf w)) =ᶠ[𝓝 z]
      fun w => (G (Bf w) - G (A w)) / ((Bf w ^ 2 - A w ^ 2) / 2) := by
    have hlt : ∀ᶠ w in 𝓝 z, A w < Bf w :=
      ha.continuousAt.eventually_lt hb.continuousAt hab
    filter_upwards [hlt] with w hw
    rw [shocksWAvg_of_lt hw, shocks_integral_id]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hW : shocksWAvg φ (A z) (Bf z) = (G (Bf z) - G (A z)) / ((Bf z ^ 2 - A z ^ 2) / 2) :=
    hev.eq_of_nhds
  rw [hW]
  have hD : Bf z ^ 2 - A z ^ 2 ≠ 0 := by nlinarith
  generalize G (Bf z) - G (A z) = S at *
  generalize Bf z ^ 2 - A z ^ 2 = D at *
  field_simp
  ring

/-- `x/w` has derivative `−x/z²` at `z ≠ 0`. -/
theorem shocks_hasDerivAt_const_div (x : ℝ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun w => x / w) (-x / z ^ 2) z := by
  have := (hasDerivAt_inv hz).const_mul x
  convert this using 1
  · ext w; rw [div_eq_mul_inv]
  · field_simp

/-- Off the kink `x̲/z = θ̲`, `a` is differentiable: `a′(z) = −x̲/z²` if `x̲/z > θ̲` and `0` if
`x̲/z < θ̲`. -/
theorem shocksA_hasDerivAt {z : ℝ} (hz : 0 < z) (hk : xlo / z ≠ θlo) :
    HasDerivAt (shocksA xlo θlo) (if θlo < xlo / z then -xlo / z ^ 2 else 0) z := by
  have hc : ContinuousAt (fun w => xlo / w) z := continuousAt_const.div continuousAt_id hz.ne'
  rcases lt_or_gt_of_ne hk with h | h
  · simp only [not_lt.2 h.le, ↓reduceIte]
    refine (hasDerivAt_const z θlo).congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually_lt continuousAt_const h] with w hw
    exact max_eq_right hw.le
  · simp only [h, ↓reduceIte]
    refine (shocks_hasDerivAt_const_div xlo hz.ne').congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hc h] with w hw
    exact max_eq_left hw.le

/-- Off the kink `x̄/z = θ̄`, `b` is differentiable: `b′(z) = −x̄/z²` if `x̄/z < θ̄` and `0` if
`x̄/z > θ̄`. -/
theorem shocksB_hasDerivAt {z : ℝ} (hz : 0 < z) (hk : xhi / z ≠ θhi) :
    HasDerivAt (shocksB xhi θhi) (if xhi / z < θhi then -xhi / z ^ 2 else 0) z := by
  have hc : ContinuousAt (fun w => xhi / w) z := continuousAt_const.div continuousAt_id hz.ne'
  rcases lt_or_gt_of_ne hk with h | h
  · simp only [h, ↓reduceIte]
    refine (shocks_hasDerivAt_const_div xhi hz.ne').congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually_lt continuousAt_const h] with w hw
    exact min_eq_left hw.le
  · simp only [not_lt.2 h.le, ↓reduceIte]
    refine (hasDerivAt_const z θhi).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hc h] with w hw
    exact min_eq_right hw.le

/-- **(7), corrected** (p. 537). Under Assumptions 17.5–17.6, by (6a) corrected
(`shocksUnif_integral_condLaw`) `(Tf)(w) = W(w) := wavg(φ_f; a(w), b(w))` for `w ∈ Z`. At every
`z ∈ Ẑ` (i.e. `z ∈ int Z` with `x̲/z ≠ θ̲` and `x̄/z ≠ θ̄`, the points where `a` and `b` are
differentiable) and for every continuous `φ` (e.g. `φ_f`, `ShocksBounds.continuous_phiF`),
`W'(z) = [b b′(φ(b) − W) − a a′(φ(a) − W)] / ((b² − a²)/2)` with `a′`, `b′` as in
`shocksA_hasDerivAt`, `shocksB_hasDerivAt`. The book's (7) has the uniform weights (denominator
`b − a` and no factors `a`, `b`) and is claimed "for all `z ∈ Z`"; at `z̲`, `z̄` the denominator
vanishes and at the kinks `a`, `b` are not differentiable. -/
theorem eq7_corrected (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo)
    (hka : xlo / z ≠ θlo) (hkb : xhi / z ≠ θhi) :
    HasDerivAt (fun w => shocksWAvg φ (shocksA xlo θlo w) (shocksB xhi θhi w))
      ((shocksB xhi θhi z * (if xhi / z < θhi then -xhi / z ^ 2 else 0) *
          (φ (shocksB xhi θhi z) - shocksWAvg φ (shocksA xlo θlo z) (shocksB xhi θhi z)) -
        shocksA xlo θlo z * (if θlo < xlo / z then -xlo / z ^ 2 else 0) *
          (φ (shocksA xlo θlo z) - shocksWAvg φ (shocksA xlo θlo z) (shocksB xhi θhi z))) /
        ((shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2) / 2)) z := by
  obtain ⟨hz0, hab⟩ := shocksA_lt_shocksB hx0 hx hθ0 hθ hzZ
  exact shocksWAvg_hasDerivAt hφ (shocksA_hasDerivAt hz0 hka) (shocksB_hasDerivAt hz0 hkb)
    (hθ0.trans_le (le_max_right _ _)) hab

/-! ### Finite `Z` (p. 539): Brouwer -/

/-- **The finite-`Z` remark** (p. 539). If `z` takes finitely many values (`Z` a finite metric
space, e.g. a finite subset of `ℝ`), then for **any** law `μ` of `(θ′, z′)` and **any**
conditional laws `G(·|z)` (no continuity in `z` and no Assumption 17.6 needed), `T` has a fixed
point bounded away from zero. As the book says, only Steps 1–3 are needed: `T` maps the compact
convex `F = {f : Z → [ζ(l₀), B]}` ⊂ `ℝ^Z` continuously into itself (`ShocksBounds.opT_mem`,
`ShocksBounds.ex_17_11_step3`), and Brouwer's theorem (`theorem_17_3`) applies. -/
theorem shocks_finite_Z {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ} {Z : Type*} [MetricSpace Z]
    [Finite Z] [Nonempty Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (hθ0 : 0 < θlo) (hθ : θlo ≤ θhi) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] :
    ∃ f : Z → ℝ, (∃ ε > 0, ∀ z, ε ≤ f z) ∧ ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  have := Fintype.ofFinite Z
  obtain ⟨l₀, hS⟩ := shocksBounds_exists hθ0 hθ hH hV
  have hl : l₀ ∈ Ioc 0 l₀ := ⟨hS.l₀_mem.1, le_rfl⟩
  obtain ⟨B, hB0, hB⟩ := hS.exists_integrand_le (Z := Z) hl
  have hzl := hS.zeta_pos hl
  have hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z := fun _ =>
    continuous_of_discreteTopology
  set F : Set (Z → ℝ) := {f | ∀ z, f z ∈ Icc (olgZeta H' l₀) B} with hF
  have hmem : ∀ f : F, ∀ z, shocksOpT L H' V' θlo θhi μ ν f.1 z ∈ Icc (olgZeta H' l₀) B :=
    fun f => (hS.opT_mem hl hB continuous_of_discreteTopology (fun z => (f.2 z).1) μ ν hν).2
  let T : F → F := fun f => ⟨shocksOpT L H' V' θlo θhi μ ν f.1, hmem f⟩
  have hFne : F.Nonempty := ⟨fun _ => olgZeta H' l₀, fun _ => ⟨le_rfl,
    (hS.integrand_ge hl (f := fun _ : Z => olgZeta H' l₀) (θt := 0)
      (ω := (0, Classical.arbitrary Z)) le_rfl).trans (hB _ _ _ le_rfl)⟩⟩
  have hFcl : IsClosed F := by
    have : F = ⋂ z, (fun f : Z → ℝ => f z) ⁻¹' Icc (olgZeta H' l₀) B := by ext f; simp [hF]
    rw [this]
    exact isClosed_iInter fun z => isClosed_Icc.preimage (continuous_apply z)
  have hFb : Bornology.IsBounded F := isBounded_iff_forall_norm_le.2
    ⟨B, fun f hf => (pi_norm_le_iff_of_nonneg hB0.le).2 fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (hzl.trans_le (hf z).1)]; exact (hf z).2⟩
  have hFconv : Convex ℝ F := fun f hf g hg a b ha hb hab z => by
    simpa using (convex_Icc _ _) (hf z) (hg z) ha hb hab
  have hTc : Continuous T := by
    refine Metric.continuous_iff.2 fun g ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hS.ex_17_11_step3 (Z := Z) hl hB (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun f hfg => ?_⟩
    have hle : dist (T f) (T g) ≤ ε / 2 := by
      rw [Subtype.dist_eq]
      refine (dist_pi_le_iff (half_pos hε).le).2 fun z => ?_
      rw [Real.dist_eq]
      exact h f.1 g.1 continuous_of_discreteTopology continuous_of_discreteTopology f.2 g.2
        (fun z => by
          rw [← Real.dist_eq]
          exact (dist_le_pi_dist f.1 g.1 z).trans_lt (by rwa [Subtype.dist_eq] at hfg)) μ ν z
    linarith
  obtain ⟨f, hf⟩ := theorem_17_3 hFne hFcl hFb hFconv hTc
  refine ⟨f.1, ⟨olgZeta H' l₀, hzl, fun z => (f.2 z).1⟩, fun z => ?_⟩
  have := congrArg (fun g : F => g.1 z) hf
  exact this.symm

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: monotonicity, Proposition 8 and Exercise 17.14

SLP §17.6, pp. 539–541. Assumption 17.4 is `MonoAssumption17_4Pos` (relative risk aversion
`≤ 1` on `ℝ₊₊`) from `FixedPointArguments.MonotoneRRA`; the operator and weighted averages are
from `FixedPointArguments.ShocksContraction` and `FixedPointArguments.ShocksSchauder`.

* **Exercise 17.14c** (p. 540): `ex_17_14c_phi` (`0 ≤ yφ'(y)/φ(y) ≤ 1`, via `shocks_V''_nonpos`)
  and `ex_17_14c` (`−1 ≤ θξ'(θ)/ξ(θ) ≤ 0` for `ξ = φ_f` on `int Θ`, by differentiating under the
  integral, `ShocksBounds.ex_17_13_deriv`, which is also **Exercise 17.13** in derivative form);
  monotone forms `ShocksBounds.phiF_antitoneOn` (`ξ` nonincreasing) and
  `ShocksBounds.phiF_mul_monotoneOn` (`θξ(θ)` nondecreasing, the book's hint for (d)).
* `shocks_phi_monotoneOn`, `ShocksBounds.opT_monotone`: under Assumption 17.4 `φ` is
  nondecreasing and `T` is monotone (p. 539).
* **Exercise 17.14a** (`ex_17_14a_deriv`, `ex_17_14a`) and the counterexample to its "only if"
  (`ex_17_14a_counterexample`).
* **Exercise 17.14b** (`ex_17_14b`, with `ex_17_14b_chain`; weak form `ex_17_14b_le`).
* **Exercise 17.14d, corrected** (`ex_17_14d`, monotone form; `ex_17_14d_deriv`, derivative form):
  with the correct weights, `J(z)/z` is nonincreasing on `Z`. Tools: `shocksWAvg_mono`,
  `shocksWAvg_right_antitone`, `shocksWAvg_left_antitone`, and the change of variables
  `shocksWAvg_div` (`θ = x/z`).
* **Proposition 8, corrected** (`proposition_8`, p. 540): under Assumptions 17.1, 17.4, 17.5 **and
  17.6**, for every strictly positive fixed point `f` of `T`, `ρ(z) = z/ζ⁻¹(f(z))` is strictly
  increasing on `Z`.
* `proposition_8_general_counterexample`: under Assumption 17.5 alone the step (d) fails.

**Correction (Proposition 8, missing Assumption 17.6).** The book's `J` is the uniform-weights
formula of Exercise 17.12, valid (with the corrected weights `2θ/(b² − a²)`) only under
Assumption 17.6, which Proposition 8 omits. Under Assumption 17.5 alone the conclusion of
Exercise 17.14d fails (`proposition_8_general_counterexample`: a bimodal `g` and `ξ = 1/θ` give
`J(4/3)/(4/3) = 3/5 < 21/31 = J(10/7)/(10/7)`). This refutes the proof; the proposition itself
is refuted in `FixedPointArguments.ShocksProposition8` (`proposition_8_false`, an actual fixed
point of `T` in the same economy). The corrected theorem `proposition_8` assumes Assumption 17.6
and uses the correct weights.

**Correction (Exercise 17.14a, "if and only if").** `ρ` strictly increasing does not imply
`zη'/η < 1` everywhere: `ρ(z) = 1 + (z − 1)³` (`ex_17_14a_counterexample`) has `zη'/η = 1` at
`z = 1`. True: `zη'/η < 1` ⇒ `ρ` strictly increasing (`ex_17_14a`); and differentiability of `η`
is an assumption (the book does not show it).

**Correction (Exercise 17.14, (d) gives `≤ 1` but (b) needs `< 1`).** (b) is true as stated with
`ηζ'/ζ ≥ 1` (the manual's `> 1` fails where `H'' = 0`, `proposition_1_elasticity_counterexample`),
but (d) delivers only `zJ'/J ≤ 1`, so the chain (d) ⇒ (b) ⇒ (a) does not close. We close it
without derivatives: `J(z)/z = (η/z) H'(η)` nonincreasing and `H'` strictly increasing force
`η(z)/z` strictly decreasing (`proposition_8`).

**Correction (Exercise 17.14d with the correct weights).** The manual's four-case computation uses
the uniform weights; with the correct weights (d) still holds (`ex_17_14d`), as the transcription's
NOTE claims; our proof is the single monotonicity argument after `θ = x/z`.

**p. 541** ("Assumption 17.2 is a very mild strengthening of Assumption 17.4"): neither implies the
other; see `assumption17_2Pos_not_imp_17_4Pos_counterexample`,
`assumption17_4Pos_not_imp_17_2Pos_counterexample` and `monoAssumption17_2Pos_of_17_4Pos` in
`FixedPointArguments.MonotoneRRA` (17.4 plus a uniform positive lower bound on relative risk
aversion implies 17.2).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-! ### Exercise 17.14 (c): elasticity of `φ` -/

/-- Under the (repaired) Assumption 17.1, `V'' ≤ 0` on `ℝ₊₊` (`V'` is decreasing). -/
theorem shocks_V''_nonpos (hV : Assumption17_1VR V V' V'') {y : ℝ} (hy : 0 < y) : V'' y ≤ 0 := by
  refine (hV.V'_deriv y hy).hasDerivWithinAt.nonpos_of_antitoneOn ?_ hV.V'_strictAntiOn.antitoneOn
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨y + min (ε / 2) y, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (lt_min (half_pos hε) hy)]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  · exact mem_Ioi.2 (by have := lt_min (half_pos hε) hy; linarith)
  · have := lt_min (half_pos hε) hy; linarith

/-- **Exercise 17.14c, first part** (p. 540). Under Assumptions 17.1 (repaired) and 17.4 (on
`ℝ₊₊`), `0 ≤ y φ'(y)/φ(y) ≤ 1` for `y > 0`, where `φ'(y) = V'(y) + y V''(y)`: indeed
`y φ'/φ = 1 − (−yV''/V')` and `0 ≤ −yV''/V' ≤ 1`. -/
theorem ex_17_14c_phi (hV : Assumption17_1VR V V' V'') (h4 : MonoAssumption17_4Pos V' V'')
    {y : ℝ} (hy : 0 < y) :
    0 ≤ y * (V' y + y * V'' y) / olgPhi V' y ∧ y * (V' y + y * V'' y) / olgPhi V' y ≤ 1 := by
  have hV' := hV.V'_pos hy
  have hφ : 0 < olgPhi V' y := mul_pos hy hV'
  have h1 := h4 y hy
  have h2 := shocks_V''_nonpos hV hy
  simp only [monoRRA] at h1
  rw [div_le_iff₀ hV'] at h1
  constructor
  · apply div_nonneg _ hφ.le
    nlinarith
  · rw [div_le_one hφ, olgPhi]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) h2]

/-- The pointwise form of Exercise 17.14c: `0 ≤ y φ'(y) ≤ φ(y)` for `y > 0`. -/
theorem shocks_phi_elasticity (hV : Assumption17_1VR V V' V'') (h4 : MonoAssumption17_4Pos V' V'')
    {y : ℝ} (hy : 0 < y) :
    0 ≤ y * (V' y + y * V'' y) ∧ y * (V' y + y * V'' y) ≤ olgPhi V' y := by
  have hφ : 0 < olgPhi V' y := mul_pos hy (hV.V'_pos hy)
  obtain ⟨h1, h2⟩ := ex_17_14c_phi hV h4 hy
  refine ⟨?_, (div_le_one hφ).1 h2⟩
  have := mul_nonneg h1 hφ.le
  rwa [div_mul_cancel₀ _ hφ.ne'] at this

/-- Under Assumptions 17.1 and 17.4, `φ` is nondecreasing on `ℝ₊₊`. -/
theorem shocks_phi_monotoneOn (hV : Assumption17_1VR V V' V'') (h4 : MonoAssumption17_4Pos V' V'') :
    MonotoneOn (olgPhi V') (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hV.phi_continuousOn
    (fun y hy => (hV.phi_hasDerivAt (interior_subset hy)).differentiableAt.differentiableWithinAt)
    fun y hy => ?_
  rw [interior_Ioi] at hy
  rw [(hV.phi_hasDerivAt hy).deriv]
  have := (shocks_phi_elasticity hV h4 hy).1
  exact nonneg_of_mul_nonneg_right (by linarith) hy

/-! ### Exercise 17.14 (a) and (b) -/

/-- **Exercise 17.14a, the derivative** (manual): `ρ(z) = z/η(z)` has
`ρ'(z) = (1/η)(1 − zη'/η)`; so `ρ'(z) > 0 ↔ zη'(z)/η(z) < 1` pointwise. -/
theorem ex_17_14a_deriv {η : ℝ → ℝ} {z η' : ℝ} (hη : HasDerivAt η η' z) (hpos : 0 < η z) :
    HasDerivAt (fun w => w / η w) (1 / η z * (1 - z * η' / η z)) z := by
  have := (hasDerivAt_id' z).div hη hpos.ne'
  convert this using 1
  field_simp

/-- **Exercise 17.14a, the true direction.** If `zη'/η < 1` on `[p, q]` (`η > 0` differentiable),
then `ρ = z/η` is strictly increasing there. -/
theorem ex_17_14a {η η' : ℝ → ℝ} {p q : ℝ} (hη : ∀ z ∈ Icc p q, HasDerivAt η (η' z) z)
    (hpos : ∀ z ∈ Icc p q, 0 < η z) (hlt : ∀ z ∈ Icc p q, z * η' z / η z < 1) :
    StrictMonoOn (fun w => w / η w) (Icc p q) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc p q) (fun z hz =>
    (ex_17_14a_deriv (hη z hz) (hpos z hz)).continuousAt.continuousWithinAt) fun z hz => ?_
  have hz := interior_subset hz
  rw [(ex_17_14a_deriv (hη z hz) (hpos z hz)).deriv]
  exact mul_pos (one_div_pos.2 (hpos z hz)) (sub_pos.2 (hlt z hz))

/-- The counterexample of Exercise 17.14a: `η(z) = z/(1 + (z − 1)³)`. -/
noncomputable def shocksEtaEx (z : ℝ) : ℝ := z / (1 + (z - 1) ^ 3)

/-- **Correction (Exercise 17.14a, "only if").** `ρ(z) = z/η(z) = 1 + (z − 1)³` is strictly
increasing on `[1/2, 3/2]` with `η > 0` differentiable, yet at `z = 1`, `zη'/η = 1`, not `< 1`.
Correct statements: `ex_17_14a` (`zη'/η < 1` ⇒ `ρ` strictly increasing) and, conversely, `ρ`
increasing ⇒ `zη'/η ≤ 1` (from `ex_17_14a_deriv`). -/
theorem ex_17_14a_counterexample :
    StrictMonoOn (fun w => w / shocksEtaEx w) (Icc (1 / 2) (3 / 2)) ∧
      (∀ z ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < shocksEtaEx z) ∧ HasDerivAt shocksEtaEx 1 1 ∧
      ¬ (1 * 1 / shocksEtaEx 1 < 1) := by
  have hρpos : ∀ z ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < 1 + (z - 1) ^ 3 := fun z hz => by
    nlinarith [hz.1, hz.2, sq_nonneg (z - 1)]
  have heq : ∀ z ∈ Icc (1 / 2 : ℝ) (3 / 2), z / shocksEtaEx z = 1 + (z - 1) ^ 3 := fun z hz => by
    have hz0 : 0 < z := by linarith [hz.1]
    simp only [shocksEtaEx]
    field_simp [(hρpos z hz).ne', hz0.ne']
  refine ⟨fun x hx y hy hxy => ?_, fun z hz => div_pos (by linarith [hz.1]) (hρpos z hz), ?_, ?_⟩
  · simp only
    rw [heq x hx, heq y hy]
    have := Odd.strictMono_pow (R := ℝ) (n := 3) ⟨1, rfl⟩ (sub_lt_sub_right hxy 1)
    linarith
  · have h1 : HasDerivAt (fun z : ℝ => 1 + (z - 1) ^ 3) (3 * (1 - 1) ^ 2) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).sub_const 1).pow 3
      simpa using this.const_add 1
    have h2 : HasDerivAt shocksEtaEx ((1 * (1 + (1 - 1) ^ 3) - 1 * (3 * (1 - 1) ^ 2)) /
        (1 + (1 - 1) ^ 3) ^ 2) 1 := (hasDerivAt_id' (1 : ℝ)).div h1 (by norm_num)
    norm_num at h2
    exact h2
  · norm_num [shocksEtaEx]

/-- The chain rule for `J = ζ ∘ η`: `J'(z) = ζ'(η(z)) η'(z)`. -/
theorem ex_17_14b_chain (hH : Assumption17_1H L H H' H'') {η : ℝ → ℝ} {z η' : ℝ}
    (hη : HasDerivAt η η' z) (hηL : η z ∈ Ioo 0 L) :
    HasDerivAt (fun w => olgZeta H' (η w)) ((H' (η z) + η z * H'' (η z)) * η') z :=
  (hH.zeta_hasDerivAt hηL).comp z hη

/-- **Exercise 17.14b** (p. 540), true as stated. With `J = ζ ∘ η`, `J' = ζ'(η) η'`,
`zJ'/J = (ηζ'(η)/ζ(η)) (zη'/η)` and `ηζ'/ζ ≥ 1` (`zeta_elasticity_ge_one`), so `zJ'/J < 1`
implies `zη'/η < 1`. (The manual claims `ηζ'/ζ > 1`, which fails where `H'' = 0`:
`proposition_1_elasticity_counterexample`; `≥ 1` suffices.) -/
theorem ex_17_14b (hH : Assumption17_1H L H H' H'') {η : ℝ → ℝ} {z η' : ℝ} (hz : 0 < z)
    (hηL : η z ∈ Ioo 0 L)
    (hJ : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) < 1) :
    z * η' / η z < 1 := by
  have hE := zeta_elasticity_ge_one hH hηL
  have hζ : 0 < olgZeta H' (η z) := hH.zeta_pos hηL
  have e : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) =
      η z * (H' (η z) + η z * H'' (η z)) / olgZeta H' (η z) * (z * η' / η z) := by
    field_simp [hηL.1.ne']
  rw [e] at hJ
  by_contra h
  push Not at h
  nlinarith

/-- **Exercise 17.14b, weak version** (what Exercise 17.14d feeds it): `zJ'/J ≤ 1` implies
`zη'/η ≤ 1`. -/
theorem ex_17_14b_le (hH : Assumption17_1H L H H' H'') {η : ℝ → ℝ} {z η' : ℝ} (hz : 0 < z)
    (hηL : η z ∈ Ioo 0 L)
    (hJ : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) ≤ 1) :
    z * η' / η z ≤ 1 := by
  have hE := zeta_elasticity_ge_one hH hηL
  have e : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) =
      η z * (H' (η z) + η z * H'' (η z)) / olgZeta H' (η z) * (z * η' / η z) := by
    field_simp [hηL.1.ne']
  rw [e] at hJ
  by_contra h
  push Not at h
  nlinarith

/-! ### Exercise 17.14 (c): `ξ = φ_f` is nonincreasing and `θ ξ(θ)` nondecreasing -/

variable {θlo θhi : ℝ}

/-- `t ↦ clamp(t)/t` is nonincreasing on `ℝ₊₊`: it equals `max(θ̲/t, min(1, θ̄/t))`. -/
theorem shocksClamp_div_antitoneOn (h0 : 0 < θlo) (hθ : θlo ≤ θhi) :
    AntitoneOn (fun t => shocksClamp θlo θhi t / t) (Ioi 0) := by
  have e : ∀ t, 0 < t → shocksClamp θlo θhi t / t = max (θlo / t) (min 1 (θhi / t)) :=
    fun t ht => by
      rw [shocksClamp, ← max_div_div_right ht.le, ← min_div_div_right ht.le, div_self ht.ne']
  intro s hs t ht hst
  simp only
  rw [e s hs, e t ht]
  exact max_le_max (div_le_div_of_nonneg_left h0.le hs hst)
    (min_le_min le_rfl (div_le_div_of_nonneg_left (h0.le.trans hθ) hs hst))

/-- The derivative of the integrand in `θ̃` (on `int Θ`). -/
noncomputable def shocksIntegrandDeriv {Z : Type*} (L : ℝ) (H' V' V'' : ℝ → ℝ) (θlo θhi : ℝ)
    (f : Z → ℝ)
    (θ : ℝ) (ω : ℝ × Z) : ℝ :=
  (V' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ) +
      shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ *
        V'' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ)) *
    (-(shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)) / θ ^ 2)

/-- The clamp is monotone. -/
theorem shocksClamp_monotone : Monotone (shocksClamp θlo θhi) := fun _ _ h =>
  max_le_max le_rfl (min_le_min_right _ h)

namespace ShocksBounds

variable {Z : Type*} {l₀ l : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'') {f : Z → ℝ}
include hS

/-- The integrand is nonincreasing in `θ̃` (Assumption 17.4: `φ` nondecreasing). -/
theorem integrand_antitone (h4 : MonoAssumption17_4Pos V' V'') (hf : ∀ z, 0 < f z)
    (ω : ℝ × Z) : Antitone fun θt => shocksIntegrand L H' V' θlo θhi f θt ω := by
  intro s t hst
  have hc := shocksClamp_mem hS.θlo_le ω.1
  have hm := hS.hH.zetaInv_pos (hf ω.2)
  have hcs := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le s).1
  have hct := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le t).1
  have hc0 := hS.θlo_pos.trans_le hc.1
  refine shocks_phi_monotoneOn hS.hV h4 (mem_Ioi.2 (mul_pos (div_pos hc0 hct) hm))
    (mem_Ioi.2 (mul_pos (div_pos hc0 hcs) hm)) ?_
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hc0.le hcs
    (shocksClamp_monotone hst)) hm.le

/-- `θ̃ ↦ θ̃ φ[(θ′/θ̃) ζ⁻¹(f(z′))]` is nondecreasing on `ℝ₊₊`: it equals
`c V'(c/clamp θ̃) / (clamp θ̃/θ̃)`, `c = clamp θ′ · ζ⁻¹(f(z′))`, with `V'` decreasing. -/
theorem integrand_mul_monotoneOn (hf : ∀ z, 0 < f z) (ω : ℝ × Z) :
    MonotoneOn (fun θt => θt * shocksIntegrand L H' V' θlo θhi f θt ω) (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  have hc := shocksClamp_mem hS.θlo_le ω.1
  have hm := hS.hH.zetaInv_pos (hf ω.2)
  have hcs := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le s).1
  have hct := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le t).1
  have hc0 := hS.θlo_pos.trans_le hc.1
  set c := shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)
  have hcpos : 0 < c := mul_pos hc0 hm
  have e : ∀ u, 0 < u → u * shocksIntegrand L H' V' θlo θhi f u ω =
      c * V' (c / shocksClamp θlo θhi u) / (shocksClamp θlo θhi u / u) := fun u hu => by
    have hcu := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le u).1
    simp only [shocksIntegrand, olgPhi, shocksRatio]
    rw [show shocksClamp θlo θhi ω.1 / shocksClamp θlo θhi u * olgZetaInv L H' (f ω.2) =
      c / shocksClamp θlo θhi u by simp only [c]; ring]
    field_simp
  simp only
  rw [e s hs0, e t ht0]
  have hV : V' (c / shocksClamp θlo θhi s) ≤ V' (c / shocksClamp θlo θhi t) :=
    hS.hV.V'_strictAntiOn.antitoneOn (div_pos hcpos hct) (div_pos hcpos hcs)
      (div_le_div_of_nonneg_left hcpos.le hcs (shocksClamp_monotone hst))
  exact div_le_div₀ (mul_nonneg hcpos.le (hS.hV.V'_pos (div_pos hcpos hct)).le)
    (mul_le_mul_of_nonneg_left hV hcpos.le) (div_pos hct ht0)
    (shocksClamp_div_antitoneOn hS.θlo_pos hS.θlo_le hs ht hst)

variable [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] {B : ℝ}

/-- **Exercise 17.14c, second part, monotone form** (p. 540): under Assumption 17.4,
`ξ = φ_f` is nonincreasing on `ℝ₊₊`. -/
theorem phiF_antitoneOn (h4 : MonoAssumption17_4Pos V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (hfc : Continuous f) (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z))
    [IsProbabilityMeasure μ] : Antitone (shocksPhiF L H' V' θlo θhi μ f) := fun s t hst =>
  integral_mono (hS.integrable_integrand hl hB hfc hfl μ t)
    (hS.integrable_integrand hl hB hfc hfl μ s) fun ω =>
      hS.integrand_antitone h4 (fun z => (hS.zeta_pos hl).trans_le (hfl z)) ω hst

/-- **Exercise 17.14c, second part, monotone form**: `θ ↦ θ ξ(θ)` is nondecreasing on `ℝ₊₊`
(the book's hint for (d)). -/
theorem phiF_mul_monotoneOn (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (hfc : Continuous f) (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z))
    [IsProbabilityMeasure μ] :
    MonotoneOn (fun θ => θ * shocksPhiF L H' V' θlo θhi μ f θ) (Ioi 0) := by
  intro s hs t ht hst
  simp only [shocksPhiF]
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_mono ((hS.integrable_integrand hl hB hfc hfl μ s).const_mul s)
    ((hS.integrable_integrand hl hB hfc hfl μ t).const_mul t) fun ω =>
      hS.integrand_mul_monotoneOn (fun z => (hS.zeta_pos hl).trans_le (hfl z)) ω hs ht hst

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- On `int Θ` the integrand is `φ(c/θ̃)`, `c = clamp θ′ · ζ⁻¹(f(z′))`, with derivative
`φ'(c/θ̃) · (−c/θ̃²)`. -/
theorem integrand_hasDerivAt (hf : ∀ z, 0 < f z) (ω : ℝ × Z) {θ : ℝ}
    (hθ : θ ∈ Ioo θlo θhi) :
    HasDerivAt (fun θt => shocksIntegrand L H' V' θlo θhi f θt ω)
      ((V' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ) +
          shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ *
            V'' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ)) *
        (-(shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)) / θ ^ 2)) θ := by
  set c := shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)
  have hθ0 : 0 < θ := hS.θlo_pos.trans hθ.1
  have hc : 0 < c := mul_pos (hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le ω.1).1)
    (hS.hH.zetaInv_pos (hf ω.2))
  have h1 : HasDerivAt (fun t => c / t) (-c / θ ^ 2) θ := by
    have := (hasDerivAt_inv hθ0.ne').const_mul c
    convert this using 1
    · ext t; rw [div_eq_mul_inv]
    · field_simp
  have h2 := (hS.hV.phi_hasDerivAt (div_pos hc hθ0)).comp θ h1
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  simp only [Function.comp, shocksIntegrand, shocksRatio,
    shocksClamp_of_mem (Ioo_subset_Icc_self ht), c]
  ring_nf

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- On `int Θ`, `|∂_θ̃ integrand| ≤ M θ̄ L/θ̲²` and `θ̃ ∂_θ̃ integrand = −y φ'(y)`, `y = c/θ̃`. -/
theorem integrandDeriv_bound (hl : l ∈ Ioc 0 l₀) : ∃ K, 0 ≤ K ∧
    ∀ (f : Z → ℝ), (∀ z, olgZeta H' l ≤ f z) → ∀ θ ∈ Icc θlo θhi, ∀ ω : ℝ × Z,
      |shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω| ≤ K := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hpos : ∀ y ∈ Icc (θlo / θhi * l) (θhi / θlo * L), 0 < y := fun y hy =>
    (mul_pos ha hl.1).trans_le hy.1
  have hc : ContinuousOn (fun y => V' y + y * V'' y) (Icc (θlo / θhi * l) (θhi / θlo * L)) :=
    (hS.hV.V'_continuousOn.mono fun y hy => hpos y hy).add
      (continuousOn_id.mul (hS.hV.V''_cont.mono fun y hy => hpos y hy))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩
  have hθ0 := hS.θlo_pos
  have hθhi : 0 < θhi := hθ0.trans_le hS.θlo_le
  refine ⟨max M 0 * (θhi * L / θlo ^ 2), mul_nonneg (le_max_right _ _)
    (by have := hS.hH.L_pos; positivity), fun f hfl θ hθ ω => ?_⟩
  have hy0 : 0 ≤ f ω.2 := (hS.zeta_pos hl).le.trans (hfl ω.2)
  have hm := hS.hH.zetaInv_mem hy0
  have hlm : l ≤ olgZetaInv L H' (f ω.2) := by
    have := hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hS.zeta_pos hl).le)
      (mem_Ici.2 hy0) (hfl ω.2)
    rwa [hS.hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
  have hcm := shocksClamp_mem hS.θlo_le ω.1
  have hθpos : 0 < θ := hθ0.trans_le hθ.1
  have hr : shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ =
      shocksRatio θlo θhi ω.1 θ * olgZetaInv L H' (f ω.2) := by
    simp only [shocksRatio, shocksClamp_of_mem hθ]; ring
  have hrm := shocksRatio_mem hθ0 hS.θlo_le ω.1 θ
  have hmem : shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ ∈
      Icc (θlo / θhi * l) (θhi / θlo * L) := by
    rw [hr]
    exact ⟨mul_le_mul hrm.1 hlm hl.1.le (ha.le.trans hrm.1),
      mul_le_mul hrm.2 hm.2.le hm.1 (ha.le.trans hab)⟩
  have h1 := (hM _ hmem).trans (le_max_left M 0)
  rw [Real.norm_eq_abs] at h1
  simp only [shocksIntegrandDeriv]
  rw [abs_mul]
  refine mul_le_mul h1 ?_ (abs_nonneg _) (le_max_right _ _)
  rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg (hθ0.le.trans hcm.1) hm.1),
    abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : θlo ^ 2 ≤ θ ^ 2 := by nlinarith [hθ.1]
  have h3 : shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) ≤ θhi * L :=
    mul_le_mul hcm.2 hm.2.le hm.1 hθhi.le
  nlinarith [mul_le_mul h3 h2 (by positivity) (by have := hS.hH.L_pos; positivity)]

/-- **Exercise 17.13, derivative form** (p. 537), and the derivative of `ξ = φ_f`: on `int Θ`,
`φ_f` is differentiable (under the integral sign), with `φ_f'(θ̃) = ∫ ∂_θ̃ integrand dμ`, and
`|φ_f'| ≤ K` with `K` independent of `f ∈ F` and of `μ`. -/
theorem ex_17_13_deriv (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (f : Z → ℝ),
      Continuous f → (∀ z, olgZeta H' l ≤ f z) → ∀ θ ∈ Ioo θlo θhi,
        Integrable (shocksIntegrandDeriv L H' V' V'' θlo θhi f θ) μ ∧
        HasDerivAt (shocksPhiF L H' V' θlo θhi μ f)
          (∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ) θ ∧
        |∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := hS.integrandDeriv_bound (Z := Z) hl
  refine ⟨K, hK0, fun μ _ f hfc hfl θ hθ => ?_⟩
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  have hcont := hS.continuous_integrand hfc hpos
  have hθ0 : 0 < θ := hS.θlo_pos.trans hθ.1
  have hF'c : Continuous (shocksIntegrandDeriv L H' V' V'' θlo θhi f θ) := by
    have hcc : Continuous fun ω : ℝ × Z => shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) :=
      (continuous_shocksClamp.comp continuous_fst).mul
        (hS.hH.zetaInv_continuousOn.comp_continuous (hfc.comp continuous_snd)
          fun ω => mem_Ici.2 (hpos _).le)
    have hcpos : ∀ ω : ℝ × Z, 0 < shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ :=
      fun ω => div_pos (mul_pos (hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le ω.1).1)
        (hS.hH.zetaInv_pos (hpos ω.2))) hθ0
    have hy : Continuous fun ω : ℝ × Z => shocksClamp θlo θhi ω.1 *
        olgZetaInv L H' (f ω.2) / θ := hcc.div_const θ
    exact ((hS.hV.V'_continuousOn.comp_continuous hy hcpos).add
      (hy.mul (hS.hV.V''_cont.comp_continuous hy hcpos))).mul (hcc.neg.div_const _)
  obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun θt ω => shocksIntegrand L H' V' θlo θhi f θt ω)
    (F' := shocksIntegrandDeriv L H' V' V'' θlo θhi f) (bound := fun _ => K)
    (Ioo_mem_nhds hθ.1 hθ.2)
    (Eventually.of_forall fun t =>
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (hS.integrable_integrand hl hB hfc hfl μ θ) hF'c.aestronglyMeasurable
    (ae_of_all _ fun ω t ht => by
      rw [Real.norm_eq_abs]; exact hK f hfl t (Ioo_subset_Icc_self ht) ω)
    (integrable_const K)
    (ae_of_all _ fun ω t ht => hS.integrand_hasDerivAt hpos ω ht)
  refine ⟨hint, hder, ?_⟩
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := K)
    (f := shocksIntegrandDeriv L H' V' V'' θlo θhi f θ)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hK f hfl θ (Ioo_subset_Icc_self hθ) ω)
  simpa using this

/-- **Exercise 17.14c, second part** (p. 540): under Assumptions 17.1 and 17.4, on `int Θ`,
`−1 ≤ θ ξ'(θ)/ξ(θ) ≤ 0` for `ξ = φ_f`, since `θ ξ'(θ) = −∫ y φ'(y) dμ` with
`0 ≤ y φ'(y) ≤ φ(y)` (`shocks_phi_elasticity`). -/
theorem ex_17_14c (h4 : MonoAssumption17_4Pos V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) {θ : ℝ} (hθ : θ ∈ Ioo θlo θhi) :
    ∃ ξ', HasDerivAt (shocksPhiF L H' V' θlo θhi μ f) ξ' θ ∧
      -1 ≤ θ * ξ' / shocksPhiF L H' V' θlo θhi μ f θ ∧
      θ * ξ' / shocksPhiF L H' V' θlo θhi μ f θ ≤ 0 := by
  obtain ⟨K, -, hK⟩ := hS.ex_17_13_deriv (Z := Z) hl hB
  obtain ⟨hint, hder, -⟩ := hK μ f hfc hfl θ hθ
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  have hθ0 : 0 < θ := hS.θlo_pos.trans hθ.1
  have hξ := hS.zeta_pos hl |>.trans_le (hS.phiF_mem hl hB hfc hfl μ θ).1
  -- pointwise: `θ ∂ = −y φ'(y)` with `0 ≤ y φ'(y) ≤ φ(y)`
  have hpt : ∀ ω : ℝ × Z, -shocksIntegrand L H' V' θlo θhi f θ ω ≤
      θ * shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∧
      θ * shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ≤ 0 := fun ω => by
    set c := shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)
    have hc : 0 < c := mul_pos (hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le ω.1).1)
      (hS.hH.zetaInv_pos (hpos ω.2))
    have hy : 0 < c / θ := div_pos hc hθ0
    obtain ⟨e1, e2⟩ := shocks_phi_elasticity hS.hV h4 hy
    have e : θ * shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω =
        -(c / θ * (V' (c / θ) + c / θ * V'' (c / θ))) := by
      simp only [shocksIntegrandDeriv, c]; field_simp
    have e' : shocksIntegrand L H' V' θlo θhi f θ ω = olgPhi V' (c / θ) := by
      simp only [shocksIntegrand, shocksRatio, shocksClamp_of_mem (Ioo_subset_Icc_self hθ), c]
      ring_nf
    rw [e, e']
    constructor <;> linarith
  have hlow : -shocksPhiF L H' V' θlo θhi μ f θ ≤
      θ * ∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ := by
    rw [← integral_const_mul, shocksPhiF, ← integral_neg]
    exact integral_mono (hS.integrable_integrand hl hB hfc hfl μ θ).neg (hint.const_mul θ)
      fun ω => (hpt ω).1
  have hup : θ * ∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ ≤ 0 := by
    rw [← integral_const_mul]
    exact integral_nonpos fun ω => (hpt ω).2
  refine ⟨_, hder, ?_, ?_⟩
  · rw [le_div_iff₀ hξ]; linarith
  · exact div_nonpos_of_nonpos_of_nonneg hup hξ.le

/-- **Monotonicity of `T`** (p. 539): under Assumption 17.4, `f ≤ g` implies `Tf ≤ Tg` (on
`F = {f ≥ ζ(l)}`), as in §17.5, since `ζ⁻¹` is increasing and `φ` nondecreasing. -/
theorem opT_monotone (h4 : MonoAssumption17_4Pos V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] {g : Z → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) (hfl : ∀ z, olgZeta H' l ≤ f z)
    (hfg : ∀ z, f z ≤ g z) (z : Z) :
    shocksOpT L H' V' θlo θhi μ ν f z ≤ shocksOpT L H' V' θlo θhi μ ν g z := by
  have hgl : ∀ z, olgZeta H' l ≤ g z := fun z => (hfl z).trans (hfg z)
  have hzl := hS.zeta_pos hl
  have hpt : ∀ θt (ω : ℝ × Z), shocksIntegrand L H' V' θlo θhi f θt ω ≤
      shocksIntegrand L H' V' θlo θhi g θt ω := fun θt ω => by
    have hr := shocksRatio_mem hS.θlo_pos hS.θlo_le ω.1 θt
    have hr0 : 0 < shocksRatio θlo θhi ω.1 θt := hS.ratio_bounds.1.trans_le hr.1
    have hf0 := hzl.trans_le (hfl ω.2)
    have hg0 := hzl.trans_le (hgl ω.2)
    exact shocks_phi_monotoneOn hS.hV h4 (mem_Ioi.2 (mul_pos hr0 (hS.hH.zetaInv_pos hf0)))
      (mem_Ioi.2 (mul_pos hr0 (hS.hH.zetaInv_pos hg0))) (mul_le_mul_of_nonneg_left
        (hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 hf0.le) (mem_Ici.2 hg0.le) (hfg ω.2))
        hr0.le)
  have hφ : ∀ θt, shocksPhiF L H' V' θlo θhi μ f θt ≤ shocksPhiF L H' V' θlo θhi μ g θt :=
    fun θt => integral_mono (hS.integrable_integrand hl hB hfc hfl μ θt)
      (hS.integrable_integrand hl hB hgc hgl μ θt) (hpt θt)
  exact integral_mono ((hS.phiFBCF hl hB hfc hfl μ).integrable (ν z))
    ((hS.phiFBCF hl hB hgc hgl μ).integrable (ν z)) hφ

end ShocksBounds

/-! ### Monotonicity of weighted averages -/

variable {q q₁ q₂ : ℝ → ℝ} {a b c d : ℝ}

/-- If `q ≤ C` on `[a, b]`, then `wavg(q; a, b) ≤ C` (`0 < a ≤ b`, `q` continuous). -/
theorem shocksWAvg_le_of_le (hq : ContinuousOn q (Icc a b)) (ha : 0 < a) (hab : a ≤ b)
    {C : ℝ} (hC : ∀ θ ∈ Icc a b, q θ ≤ C) : shocksWAvg q a b ≤ C := by
  rcases hab.eq_or_lt with h | h
  · subst h; simpa [shocksWAvg] using hC a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  rw [shocksWAvg_of_lt h, div_le_iff₀ hW, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on h.le
    ((continuousOn_id.mul hq).intervalIntegrable_of_Icc h.le)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _) fun θ hθ => ?_
  have := hC θ hθ
  have h0 : 0 < θ := ha.trans_le hθ.1
  nlinarith

/-- If `C ≤ q` on `[a, b]`, then `C ≤ wavg(q; a, b)`. -/
theorem le_shocksWAvg_of_le (hq : ContinuousOn q (Icc a b)) (ha : 0 < a) (hab : a ≤ b)
    {C : ℝ} (hC : ∀ θ ∈ Icc a b, C ≤ q θ) : C ≤ shocksWAvg q a b := by
  rcases hab.eq_or_lt with h | h
  · subst h; simpa [shocksWAvg] using hC a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  rw [shocksWAvg_of_lt h, le_div_iff₀ hW, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on h.le
    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((continuousOn_id.mul hq).intervalIntegrable_of_Icc h.le) fun θ hθ => ?_
  have := hC θ hθ
  have h0 : 0 < θ := ha.trans_le hθ.1
  nlinarith

/-- The weighted average is monotone in the function. -/
theorem shocksWAvg_mono (hq₁ : ContinuousOn q₁ (Icc a b)) (hq₂ : ContinuousOn q₂ (Icc a b))
    (ha : 0 < a) (hab : a ≤ b) (h : ∀ θ ∈ Icc a b, q₁ θ ≤ q₂ θ) :
    shocksWAvg q₁ a b ≤ shocksWAvg q₂ a b := by
  rcases hab.eq_or_lt with h' | h'
  · subst h'; simpa [shocksWAvg] using h a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  rw [shocksWAvg_of_lt h', shocksWAvg_of_lt h']
  refine div_le_div_of_nonneg_right ?_ hW.le
  refine intervalIntegral.integral_mono_on h'.le
    ((continuousOn_id.mul hq₁).intervalIntegrable_of_Icc h'.le)
    ((continuousOn_id.mul hq₂).intervalIntegrable_of_Icc h'.le) fun θ hθ => ?_
  exact mul_le_mul_of_nonneg_left (h θ hθ) (ha.trans_le hθ.1).le

/-- For nonincreasing `q`, extending the interval to the right lowers the average. -/
theorem shocksWAvg_right_antitone (hq : ContinuousOn q (Icc a d)) (hqa : AntitoneOn q (Icc a d))
    (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb : b ≤ b') (hbd : b' ≤ d) :
    shocksWAvg q a b' ≤ shocksWAvg q a b := by
  rcases (hab.trans hbb).eq_or_lt with h | hab'
  · have h1 : b = b' := le_antisymm hbb (h ▸ hab)
    subst h1; exact le_rfl
  have hW : 0 < ∫ θ in a..b', θ := by rw [shocks_integral_id]; nlinarith
  have hsub : Icc a b ⊆ Icc a d := Icc_subset_Icc le_rfl (hbb.trans hbd)
  have hM : q b ≤ shocksWAvg q a b := le_shocksWAvg_of_le (hq.mono hsub) ha hab fun θ hθ =>
    hqa (hsub hθ) (hsub ⟨hab, le_rfl⟩) hθ.2
  have hdiff := shocksWAvg_extend_right hq ha hab hbb hbd hab'
  have hnum : ∫ θ in b..b', θ * (q θ - shocksWAvg q a b) ≤ 0 := by
    have := intervalIntegral.integral_mono_on (f := fun θ => θ * (q θ - shocksWAvg q a b))
      (g := fun _ => (0 : ℝ)) hbb (shocks_intervalIntegrable hq hab hbb hbd _)
      intervalIntegrable_const fun θ hθ => by
        have h0 : 0 < θ := ha.trans_le (hab.trans hθ.1)
        have : q θ ≤ q b := hqa ⟨hab, hbb.trans hbd⟩ ⟨hab.trans hθ.1, hθ.2.trans hbd⟩ hθ.1
        nlinarith
    simpa using this
  have : shocksWAvg q a b' - shocksWAvg q a b ≤ 0 := by
    rw [hdiff]; exact div_nonpos_of_nonpos_of_nonneg hnum hW.le
  linarith

/-- For nonincreasing `q`, extending the interval to the left raises the average. -/
theorem shocksWAvg_left_antitone (hq : ContinuousOn q (Icc c b)) (hqa : AntitoneOn q (Icc c b))
    {A : ℝ} (hA : 0 < A) (hcA : c ≤ A) (hAa : A ≤ a) (hab : a ≤ b) :
    shocksWAvg q a b ≤ shocksWAvg q A b := by
  rcases (hAa.trans hab).eq_or_lt with h | hAb
  · have h1 : A = a := le_antisymm hAa (h ▸ hab)
    subst h1; exact le_rfl
  have ha : 0 < a := hA.trans_le hAa
  have hW : 0 < ∫ θ in A..b, θ := by rw [shocks_integral_id]; nlinarith
  have hsub : Icc a b ⊆ Icc c b := Icc_subset_Icc (hcA.trans hAa) le_rfl
  have hM : shocksWAvg q a b ≤ q a := shocksWAvg_le_of_le (hq.mono hsub) ha hab fun θ hθ =>
    hqa (hsub ⟨le_rfl, hab⟩) (hsub hθ) hθ.1
  have hdiff := shocksWAvg_extend_left hq hA hcA hAa hab hAb
  have hnum : 0 ≤ ∫ θ in A..a, θ * (q θ - shocksWAvg q a b) := by
    have := intervalIntegral.integral_mono_on (g := fun θ => θ * (q θ - shocksWAvg q a b))
      (f := fun _ => (0 : ℝ)) hAa intervalIntegrable_const
      (shocks_intervalIntegrable hq hcA hAa hab _) fun θ hθ => by
        have h0 : 0 < θ := hA.trans_le hθ.1
        have : q a ≤ q θ := hqa ⟨hcA.trans hθ.1, hθ.2.trans hab⟩ ⟨hcA.trans hAa, hab⟩ hθ.2
        nlinarith
    simpa using this
  have : 0 ≤ shocksWAvg q A b - shocksWAvg q a b := by
    rw [hdiff]; exact div_nonneg hnum hW.le
  linarith

/-- **Change of variables `θ = x/z`** in the weighted average:
`wavg(ξ; a, b)/z = wavg(x ↦ ξ(x/z)/z; za, zb)` (`z > 0`, `0 < a ≤ b`). -/
theorem shocksWAvg_div {ξ : ℝ → ℝ} (hξ : ContinuousOn ξ (Icc a b)) {z : ℝ} (hz : 0 < z)
    (ha : 0 < a) (hab : a ≤ b) :
    shocksWAvg ξ a b / z = shocksWAvg (fun x => ξ (x / z) / z) (z * a) (z * b) := by
  rcases hab.eq_or_lt with h | h
  · subst h
    simp [shocksWAvg, mul_div_cancel_left₀ _ hz.ne']
  have hzab : z * a < z * b := mul_lt_mul_of_pos_left h hz
  rw [shocksWAvg_of_lt h, shocksWAvg_of_lt hzab, shocks_integral_id, shocks_integral_id]
  have e : ∫ x in z * a..z * b, x * (ξ (x / z) / z) = z * ∫ θ in a..b, θ * ξ θ := by
    have h1 := intervalIntegral.integral_comp_div (f := fun θ => θ * ξ θ) (a := z * a)
      (b := z * b) hz.ne'
    rw [mul_div_cancel_left₀ _ hz.ne', mul_div_cancel_left₀ _ hz.ne', smul_eq_mul] at h1
    rw [← h1]
    congr 1
    ext x
    ring
  rw [e]
  have hW : 0 < b ^ 2 - a ^ 2 := by nlinarith
  field_simp

/-! ### Exercise 17.14 (d) and Proposition 8 (uniform shocks, correct weights) -/

variable {xlo xhi : ℝ}

/-- `z a(z) = max{x̲, z θ̲}` for `z > 0`. -/
theorem mul_shocksA {z : ℝ} (hz : 0 < z) : z * shocksA xlo θlo z = max xlo (z * θlo) := by
  rw [shocksA, mul_max_of_nonneg _ _ hz.le, mul_div_cancel₀ _ hz.ne']

/-- `z b(z) = min{x̄, z θ̄}` for `z > 0`. -/
theorem mul_shocksB {z : ℝ} (hz : 0 < z) : z * shocksB xhi θhi z = min xhi (z * θhi) := by
  rw [shocksB, mul_min_of_nonneg _ _ hz.le, mul_div_cancel₀ _ hz.ne']

/-- **Exercise 17.14d, corrected (monotone form)** (p. 540). Under Assumptions 17.5–17.6, with the
correct weights, let `J(z) = wavg(ξ; a(z), b(z)) = E[ξ(θ) | z]`. If `ξ` is continuous and
nonincreasing on `ℝ₊₊` and `θ ↦ θ ξ(θ)` is nondecreasing there (Exercise 17.14c), then `J(z)/z`
is nonincreasing on `Z`, i.e. "`zJ'/J ≤ 1`" (`ex_17_14d_deriv`). Proof: substituting `θ = x/z`,
`J(z)/z = wavg(x ↦ ξ(x/z)/z; max{x̲, zθ̲}, min{x̄, zθ̄})`, the integrand is nonincreasing in `x`
and in `z`, and both endpoints are nondecreasing in `z`. -/
theorem ex_17_14d (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {ξ : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi 0)) (hξa : AntitoneOn ξ (Ioi 0))
    (hu : MonotoneOn (fun θ => θ * ξ θ) (Ioi 0)) :
    AntitoneOn (fun z => shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z) / z)
      (Icc (xlo / θhi) (xhi / θlo)) := by
  intro z hz z' hz' hzz
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hz0 : 0 < z := (div_pos hx0 hθhi).trans_le hz.1
  have hz0' : 0 < z' := hz0.trans_le hzz
  obtain ⟨h1, h2, h3⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ hz
  obtain ⟨h1', h2', h3'⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ hz'
  have ha0 : 0 < shocksA xlo θlo z := hθ0.trans_le h1
  have ha0' : 0 < shocksA xlo θlo z' := hθ0.trans_le h1'
  simp only
  rw [shocksWAvg_div (hξc.mono fun θ hθ => ha0.trans_le hθ.1) hz0 ha0 h2,
    shocksWAvg_div (hξc.mono fun θ hθ => ha0'.trans_le hθ.1) hz0' ha0' h2',
    mul_shocksA hz0, mul_shocksB hz0, mul_shocksA hz0', mul_shocksB hz0']
  set α := max xlo (z * θlo)
  set β := min xhi (z * θhi)
  set α' := max xlo (z' * θlo)
  set β' := min xhi (z' * θhi)
  have hα0 : 0 < α := hx0.trans_le (le_max_left _ _)
  have hαα : α ≤ α' := max_le_max le_rfl (mul_le_mul_of_nonneg_right hzz hθ0.le)
  have hββ : β ≤ β' := min_le_min le_rfl (mul_le_mul_of_nonneg_right hzz hθhi.le)
  have hαβ : α ≤ β := by
    have := mul_le_mul_of_nonneg_left h2 hz0.le
    rwa [mul_shocksA hz0, mul_shocksB hz0] at this
  have hαβ' : α' ≤ β' := by
    have := mul_le_mul_of_nonneg_left h2' hz0'.le
    rwa [mul_shocksA hz0', mul_shocksB hz0'] at this
  have hqc : ∀ w, 0 < w → ContinuousOn (fun x => ξ (x / w) / w) (Ioi 0) := fun w hw =>
    (hξc.comp (continuousOn_id.div_const w) fun x hx => div_pos hx hw).div_const w
  have hqa : AntitoneOn (fun x => ξ (x / z) / z) (Ioi 0) := fun x hx y hy hxy =>
    div_le_div_of_nonneg_right (hξa (div_pos hx hz0) (div_pos hy hz0)
      (div_le_div_of_nonneg_right hxy hz0.le)) hz0.le
  have hsub : Icc α β' ⊆ Ioi 0 := fun x hx => hα0.trans_le hx.1
  calc shocksWAvg (fun x => ξ (x / z') / z') α' β'
      ≤ shocksWAvg (fun x => ξ (x / z) / z) α' β' := by
        refine shocksWAvg_mono ((hqc z' hz0').mono fun x hx => hα0.trans_le (hαα.trans hx.1))
          ((hqc z hz0).mono fun x hx => hα0.trans_le (hαα.trans hx.1)) (hα0.trans_le hαα)
          hαβ' fun x hx => ?_
        have hx0' : 0 < x := hα0.trans_le (hαα.trans hx.1)
        have hu' := hu (div_pos hx0' hz0') (div_pos hx0' hz0)
          (div_le_div_of_nonneg_left hx0'.le hz0 hzz)
        simp only at hu'
        rw [div_le_div_iff₀ hz0' hz0]
        have e1 : x / z' * ξ (x / z') = x * (ξ (x / z') / z') := by ring
        have e2 : x / z * ξ (x / z) = x * (ξ (x / z) / z) := by ring
        rw [e1, e2] at hu'
        have := le_of_mul_le_mul_left hu' hx0'
        rw [div_le_div_iff₀ hz0' hz0] at this
        exact this
    _ ≤ shocksWAvg (fun x => ξ (x / z) / z) α β' :=
        shocksWAvg_left_antitone ((hqc z hz0).mono hsub) (hqa.mono hsub) hα0 le_rfl hαα hαβ'
    _ ≤ shocksWAvg (fun x => ξ (x / z) / z) α β :=
        shocksWAvg_right_antitone ((hqc z hz0).mono hsub) (hqa.mono hsub) hα0 hαβ hββ le_rfl

/-- Interior points of `[p, q]` are accumulation points of `[p, q]`. -/
theorem shocks_accPt_Icc {p r z : ℝ} (hz : z ∈ Ioo p r) : AccPt z (𝓟 (Icc p r)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hd : 0 < min (ε / 2) ((r - z) / 2) := lt_min (half_pos hε) (by linarith [hz.2])
  refine ⟨z + min (ε / 2) ((r - z) / 2), ⟨hball ?_, ?_, ?_⟩, by linarith⟩
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  · linarith [hz.1]
  · linarith [min_le_right (ε / 2) ((r - z) / 2)]

/-- **Exercise 17.14d, derivative form**: wherever `J` is differentiable in `int Z`,
`zJ'(z)/J(z) ≤ 1` (from `ex_17_14d`). This is `≤ 1`, not the strict `< 1` that Exercise 17.14b
assumes; the chain is closed in `proposition_8` without derivatives. -/
theorem ex_17_14d_deriv (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {ξ : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi 0)) (hξa : AntitoneOn ξ (Ioi 0))
    (hu : MonotoneOn (fun θ => θ * ξ θ) (Ioi 0)) {z J' : ℝ}
    (hz : z ∈ Ioo (xlo / θhi) (xhi / θlo))
    (hJ : HasDerivAt (fun w => shocksWAvg ξ (shocksA xlo θlo w) (shocksB xhi θhi w)) J' z)
    (hJpos : 0 < shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z)) :
    z * J' / shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z) ≤ 1 := by
  have hz0 : 0 < z := (div_pos hx0 (hθ0.trans hθ)).trans hz.1
  have hd := hJ.div (hasDerivAt_id' z) hz0.ne'
  have := hd.hasDerivWithinAt.nonpos_of_antitoneOn (shocks_accPt_Icc hz)
    (ex_17_14d hx0 hx hθ0 hθ hξc hξa hu)
  rw [div_le_iff₀ hJpos, one_mul]
  have hz2 : 0 < z ^ 2 := by positivity
  rw [div_nonpos_iff] at this
  rcases this with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · nlinarith

/-- **Proposition 8, corrected** (p. 540). Let `H` satisfy Assumption 17.1, `V` the (repaired)
Assumption 17.1 and Assumption 17.4, and let `Ψ`, `G` be **uniform** (Assumptions 17.5 **and
17.6**), with the correct conditional law `G(·|z)` and any law `μ` of `(θ′, z′)`. If `f > 0` is a
continuous fixed point of `T` (equivalently `η = ζ⁻¹ ∘ f` solves (3)), then the price function
`ρ(z) = z/η(z)` is strictly increasing on `Z`.

Proof (no derivatives): by `ex_17_14c` (monotone form) `ξ = φ_f` is nonincreasing and `θξ(θ)`
nondecreasing, so by `ex_17_14d` `J(z)/z = ζ(η(z))/z = (η(z)/z) H'(η(z))` is nonincreasing; if
`z < z'` but `η(z')/z' ≥ η(z)/z`, then `η(z') > η(z)`, so `H'(η(z')) > H'(η(z))` (strict
convexity) and `J(z')/z' > J(z)/z`, a contradiction. This closes the gap between Exercise 17.14d
(`≤ 1`) and 17.14b (`< 1`) noted in the transcription, without needing `H'' > 0`. -/
theorem proposition_8 (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    (hθ2 : θhi < 2) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (h4 : MonoAssumption17_4Pos V' V'') (μ : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo)))
    [IsProbabilityMeasure μ] (f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi
      (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1) f z) :
    StrictMono fun z : Icc (xlo / θhi) (xhi / θlo) => (z : ℝ) / olgZetaInv L H' (f z) := by
  obtain ⟨l₀, hS⟩ := shocksBounds_exists hθ0 hθ.le hH hV
  have hne : (univ : Set (Icc (xlo / θhi) (xhi / θlo))).Nonempty :=
    ⟨⟨_, left_mem_Icc.2 (div_le_div₀ (hx0.trans hx).le hx.le hθ0 hθ.le)⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne f.continuous.continuousOn
  set l := min l₀ (olgZetaInv L H' (f m))
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hS.l₀_mem.1 (hH.zetaInv_pos (hfpos m)), min_le_left _ _⟩
  have hlL : l ∈ Ico 0 L := ⟨hl.1.le, hl.2.trans_lt hS.l₀_mem.2⟩
  have hfl : ∀ z, olgZeta H' l ≤ f z := fun z =>
    calc olgZeta H' l ≤ olgZeta H' (olgZetaInv L H' (f m)) :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
      _ ≤ f z := isMinOn_iff.1 hm z (mem_univ z)
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le (Z := Icc (xlo / θhi) (xhi / θlo)) hl
  set ξ := shocksPhiF L H' V' θlo θhi μ f
  have hJ := ex_17_14d hx0 hx hθ0 hθ (ξ := ξ)
    (hS.continuous_phiF hl hB f.continuous hfl μ).continuousOn
    ((hS.phiF_antitoneOn h4 hl hB f.continuous hfl μ).antitoneOn _)
    (hS.phiF_mul_monotoneOn hl hB f.continuous hfl μ)
  have hfJ : ∀ z : Icc (xlo / θhi) (xhi / θlo),
      f z = shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z) := fun z => by
    rw [hfix z]
    exact shocksUnif_integral_condLaw hx0 hx hθ0 hθ hθ2 z.2 ξ
  have hη : ∀ z, olgZetaInv L H' (f z) ∈ Ioo 0 L := fun z =>
    ⟨hH.zetaInv_pos (hfpos z), (hH.zetaInv_mem (hfpos z).le).2⟩
  have hζ : ∀ z, f z = olgZetaInv L H' (f z) * H' (olgZetaInv L H' (f z)) := fun z =>
    (hH.zeta_zetaInv (hfpos z).le).symm
  have hθhi : 0 < θhi := hθ0.trans hθ
  intro z z' hzz'
  have hzz : (z : ℝ) < z' := hzz'
  have hz0 : 0 < (z : ℝ) := (div_pos hx0 hθhi).trans_le z.2.1
  have hz0' : 0 < (z' : ℝ) := hz0.trans hzz
  simp only
  by_contra hcon
  push Not at hcon
  have hηp := (hη z).1
  have hηp' := (hη z').1
  rw [div_le_div_iff₀ hηp' hηp] at hcon
  -- `z' η ≤ z η'`, hence `η < η'`
  have hlt : olgZetaInv L H' (f z) < olgZetaInv L H' (f z') := by
    by_contra h
    push Not at h
    have h1 := mul_lt_mul_of_pos_right hzz hηp
    have h2 := mul_le_mul_of_nonneg_left h hz0.le
    linarith
  have hH' : H' (olgZetaInv L H' (f z)) < H' (olgZetaInv L H' (f z')) :=
    hH.H'_strictMonoOn (Ioo_subset_Ico_self (hη z)) (Ioo_subset_Ico_self (hη z')) hlt
  have hH'0 : 0 < H' (olgZetaInv L H' (f z)) := hH.H'_pos (hη z)
  have hanti := hJ z.2 z'.2 hzz.le
  simp only at hanti
  rw [← hfJ z, ← hfJ z', hζ z, hζ z', div_le_div_iff₀ hz0' hz0] at hanti
  have h3 := mul_le_mul_of_nonneg_right hcon hH'0.le
  have h4 := mul_lt_mul_of_pos_left hH' (mul_pos hz0 hηp')
  nlinarith

/-! ### Without Assumption 17.6 the step (d) fails -/

/-- `∫_p^q (c₀ + c₁ θ + c₂ θ²) dθ`. -/
theorem shocks_integral_quad (c₀ c₁ c₂ p r : ℝ) :
    ∫ θ in p..r, (c₀ + c₁ * θ + c₂ * θ ^ 2) =
      c₀ * (r - p) + c₁ * ((r ^ 2 - p ^ 2) / 2) + c₂ * ((r ^ 3 - p ^ 3) / 3) := by
  have i1 : IntervalIntegrable (fun θ : ℝ => c₀ + c₁ * θ) volume p r :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => c₂ * θ ^ 2) volume p r :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ : ℝ => c₁ * θ) volume p r :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add intervalIntegrable_const
    i3, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow, smul_eq_mul]
  norm_num
  ring

/-- `∫ 1_{[p, r]} F = ∫_p^r F`. -/
theorem shocks_integral_indicator_Icc {p r : ℝ} (hpr : p ≤ r) (F : ℝ → ℝ) :
    ∫ θ, (Icc p r).indicator F θ = ∫ θ in p..r, F θ := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hpr]

/-- The two bumps of the bimodal density. -/
noncomputable def shocksExBump1 (θ : ℝ) : ℝ :=
  (Icc (1 : ℝ) (11 / 10)).indicator (fun θ => 11 / 10 - θ) θ

/-- The second bump. -/
noncomputable def shocksExBump2 (θ : ℝ) : ℝ :=
  (Icc (7 / 5 : ℝ) (3 / 2)).indicator (fun θ => θ - 7 / 5) θ

/-- A bimodal density on `Θ = [1, 3/2]`, `g = 100 (bump₁ + bump₂)`, continuous on `Θ`. -/
noncomputable def shocksExBimodal (θ : ℝ) : ℝ := 100 * (shocksExBump1 θ + shocksExBump2 θ)

/-- Integrals of `k(θ) × bump` reduce to interval integrals. -/
theorem shocksExBump_integrals :
    ∫ θ, shocksExBump1 θ = 1 / 200 ∧ ∫ θ, shocksExBump2 θ = 1 / 200 ∧
      ∫ θ, shocksExBump1 θ * θ = 31 / 6000 ∧ ∫ θ, shocksExBump2 θ * θ = 44 / 6000 := by
  have e1 : (fun θ => shocksExBump1 θ * θ) = (Icc (1 : ℝ) (11 / 10)).indicator
      (fun θ => 0 + 11 / 10 * θ + -1 * θ ^ 2) := by
    ext θ; simp only [shocksExBump1]
    by_cases h : θ ∈ Icc (1 : ℝ) (11 / 10)
    · rw [indicator_of_mem h, indicator_of_mem h]; ring
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  have e2 : (fun θ => shocksExBump2 θ * θ) = (Icc (7 / 5 : ℝ) (3 / 2)).indicator
      (fun θ => 0 + -(7 / 5) * θ + 1 * θ ^ 2) := by
    ext θ; simp only [shocksExBump2]
    by_cases h : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
    · rw [indicator_of_mem h, indicator_of_mem h]; ring
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  have e3 : (fun θ : ℝ => 11 / 10 - θ) = fun θ => 11 / 10 + -1 * θ + 0 * θ ^ 2 := by
    ext θ; ring
  have e4 : (fun θ : ℝ => θ - 7 / 5) = fun θ => -(7 / 5) + 1 * θ + 0 * θ ^ 2 := by
    ext θ; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [shocksExBump1]
    rw [shocks_integral_indicator_Icc (by norm_num), e3, shocks_integral_quad]; norm_num
  · simp only [shocksExBump2]
    rw [shocks_integral_indicator_Icc (by norm_num), e4, shocks_integral_quad]; norm_num
  · rw [e1, shocks_integral_indicator_Icc (by norm_num), shocks_integral_quad]; norm_num
  · rw [e2, shocks_integral_indicator_Icc (by norm_num), shocks_integral_quad]; norm_num

/-- The bimodal example satisfies Assumption 17.5 (with `x ~ U[1, 2]`). -/
theorem shocksExBimodal_assumption :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal := by
  have hU := shocksUnif_assumption17_5 (xlo := 1) (xhi := 2) (θlo := 1) (θhi := 3 / 2) one_pos
    one_lt_two one_pos (by norm_num) (by norm_num)
  have hb1 : ∀ θ, 0 ≤ shocksExBump1 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have hb2 : ∀ θ, 0 ≤ shocksExBump2 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have i1 : Integrable shocksExBump1 :=
    (continuousOn_const.sub continuousOn_id |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i2 : Integrable shocksExBump2 :=
    (continuousOn_id.sub continuousOn_const |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  obtain ⟨j1, j2, -, -⟩ := shocksExBump_integrals
  refine ⟨one_pos, one_lt_two, one_pos, by norm_num, by norm_num, hU.ψ_nonneg,
    fun θ => mul_nonneg (by norm_num) (add_nonneg (hb1 θ) (hb2 θ)), hU.ψ_zero,
    fun θ hθ => ?_, hU.ψ_cont, ?_, hU.ψ_int, ?_⟩
  · have h1 : θ ∉ Icc (1 : ℝ) (11 / 10) := fun h => hθ ⟨h.1, by linarith [h.2]⟩
    have h2 : θ ∉ Icc (7 / 5 : ℝ) (3 / 2) := fun h => hθ ⟨by linarith [h.1], h.2⟩
    simp [shocksExBimodal, shocksExBump1, shocksExBump2, indicator_of_notMem h1,
      indicator_of_notMem h2]
  · refine (Continuous.continuousOn (f := fun θ : ℝ => 100 * (max (11 / 10 - θ) 0 +
      max (θ - 7 / 5) 0)) (by fun_prop)).congr fun θ hθ => ?_
    simp only [shocksExBimodal, shocksExBump1, shocksExBump2]
    by_cases h1 : θ ≤ 11 / 10
    · rw [indicator_of_mem (show θ ∈ Icc (1 : ℝ) (11 / 10) from ⟨hθ.1, h1⟩),
        indicator_of_notMem (show θ ∉ Icc (7 / 5 : ℝ) (3 / 2) from fun h => by linarith [h.1]),
        max_eq_left (by linarith), max_eq_right (by linarith)]
    · by_cases h2 : 7 / 5 ≤ θ
      · rw [indicator_of_notMem (show θ ∉ Icc (1 : ℝ) (11 / 10) from fun h => h1 h.2),
          indicator_of_mem (show θ ∈ Icc (7 / 5 : ℝ) (3 / 2) from ⟨h2, hθ.2⟩),
          max_eq_right (by linarith), max_eq_left (by linarith)]
      · rw [indicator_of_notMem (show θ ∉ Icc (1 : ℝ) (11 / 10) from fun h => h1 h.2),
          indicator_of_notMem (show θ ∉ Icc (7 / 5 : ℝ) (3 / 2) from fun h => h2 h.1),
          max_eq_right (by linarith), max_eq_right (by linarith)]
  · simp only [shocksExBimodal]
    rw [integral_const_mul, integral_add i1 i2, j1, j2]
    norm_num

/-- In the bimodal example, `E[θ⁻¹ | z] = ∫ g ψ(z·) / π(z)`. -/
theorem shocksExBimodal_integral_inv {z : ℝ} (hzZ : 1 / (3 / 2) < z ∧ z < 2 / 1)
    (hπ : 0 < shocksPi (shocksUnif 1 2) shocksExBimodal z) :
    ∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z =
      (∫ θ, shocksExBimodal θ * shocksUnif 1 2 (z * θ)) /
        shocksPi (shocksUnif 1 2) shocksExBimodal z := by
  rw [shocksExBimodal_assumption.integral_condLaw hzZ hπ, ← integral_div]
  congr 1
  ext θ
  by_cases h : θ = 0
  · subst h
    have : shocksExBimodal 0 = 0 :=
      shocksExBimodal_assumption.g_zero 0 (fun h => by linarith [h.1])
    simp [shocksCondDens, this]
  · simp only [shocksCondDens]
    field_simp

/-- **Correction (Proposition 8 needs Assumption 17.6; NOTE verified).** Without Assumption 17.6
the key step (d) fails for the true conditional law. Take `x ~ U[1, 2]` and the bimodal density
`g = 100 (bump on [1, 11/10] + bump on [7/5, 3/2])` (Assumption 17.5 holds), and `ξ(θ) = 1/θ`
(nonincreasing with `θξ(θ) = 1` nondecreasing, i.e. `θξ'/ξ = −1`, allowed by Exercise 17.14c).
Then `J(z) = E[ξ(θ) | z]` has `J(4/3)/(4/3) = 3/5 < 21/31 = J(10/7)/(10/7)`: `J(z)/z` is not
nonincreasing, so the conclusion of Exercise 17.14d (monotone form; `zJ'/J ≤ 1` cannot hold
throughout `(4/3, 10/7)` where `J` is differentiable): as `z` rises from `4/3` to `10/7`, the
support `[θ̲, x̄/z]` of `G(·|z)` loses the upper bump. This refutes the proof strategy under
Assumption 17.5 alone. (`ξ = 1/θ` corresponds to the limiting linear `V`; an actual fixed point
of `T` in this economy refuting Proposition 8 itself is `proposition_8_counterexample` in
`FixedPointArguments.ShocksProposition8`.) -/
theorem proposition_8_general_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal ∧
      AntitoneOn (fun θ : ℝ => θ⁻¹) (Ioi 0) ∧ MonotoneOn (fun θ : ℝ => θ * θ⁻¹) (Ioi 0) ∧
      (1 : ℝ) / (3 / 2) < 4 / 3 ∧ (4 / 3 : ℝ) < 10 / 7 ∧ (10 / 7 : ℝ) < 2 / 1 ∧
      (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (4 / 3)) / (4 / 3) <
        (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (10 / 7)) /
          (10 / 7) := by
  have hA := shocksExBimodal_assumption
  obtain ⟨j1, j2, j3, j4⟩ := shocksExBump_integrals
  have i1 : Integrable shocksExBump1 :=
    (continuousOn_const.sub continuousOn_id |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i2 : Integrable shocksExBump2 :=
    (continuousOn_id.sub continuousOn_const |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i3 : Integrable fun θ => shocksExBump1 θ * θ := by
    have : (fun θ => shocksExBump1 θ * θ) =
        (Icc (1 : ℝ) (11 / 10)).indicator fun θ => (11 / 10 - θ) * θ := by
      ext θ; simp only [shocksExBump1]
      by_cases h : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i4 : Integrable fun θ => shocksExBump2 θ * θ := by
    have : (fun θ => shocksExBump2 θ * θ) =
        (Icc (7 / 5 : ℝ) (3 / 2)).indicator fun θ => (θ - 7 / 5) * θ := by
      ext θ; simp only [shocksExBump2]
      by_cases h : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hψ1 : ∀ x ∈ Icc (1 : ℝ) 2, shocksUnif 1 2 x = 1 := fun x hx => by
    rw [shocksUnif, indicator_of_mem hx]; norm_num
  have hψ0 : ∀ x, 2 < x → shocksUnif 1 2 x = 0 := fun x hx => by
    rw [shocksUnif, indicator_of_notMem fun h => by linarith [h.2]]
  have hgΘ : ∀ θ, θ ∉ Icc (1 : ℝ) (3 / 2) → shocksExBimodal θ = 0 := hA.g_zero
  -- at `z₁ = 4/3`, `ψ(z₁θ) = 1` on `Θ`
  have a1 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = shocksExBimodal θ := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one]
    · rw [hgΘ θ h, zero_mul]
  have b1 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (4 / 3 * θ) =
      100 * (shocksExBump1 θ * θ + shocksExBump2 θ * θ) := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one, shocksExBimodal]; ring
    · have h1 : θ ∉ Icc (1 : ℝ) (11 / 10) := fun h' => h ⟨h'.1, by linarith [h'.2]⟩
      have h2 : θ ∉ Icc (7 / 5 : ℝ) (3 / 2) := fun h' => h ⟨by linarith [h'.1], h'.2⟩
      simp [hgΘ θ h, shocksExBump1, shocksExBump2, indicator_of_notMem h1,
        indicator_of_notMem h2]
  -- at `z₂ = 10/7`, only the lower bump is seen
  have a2 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 100 * shocksExBump1 θ :=
    fun θ => by
      simp only [shocksExBimodal, shocksExBump1, shocksExBump2]
      by_cases h1 : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h => by linarith [h.1, h1.2]),
          hψ1 _ ⟨by linarith [h1.1], by linarith [h1.2]⟩]
        ring
      · rw [indicator_of_notMem h1]
        by_cases h2 : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
        · rw [indicator_of_mem h2]
          rcases h2.1.eq_or_lt with h3 | h3
          · rw [← h3]; ring
          · rw [hψ0 _ (by linarith)]; ring
        · rw [indicator_of_notMem h2]; ring
  have b2 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
      100 * (shocksExBump1 θ * θ) := fun θ => by
    have := a2 θ
    calc shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
        shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) * θ := by ring
      _ = 100 * (shocksExBump1 θ * θ) := by rw [this]; ring
  have π1 : shocksPi (shocksUnif 1 2) shocksExBimodal (4 / 3) = 5 / 4 := by
    simp only [shocksPi]
    simp_rw [b1]
    rw [integral_const_mul, integral_add i3 i4, j3, j4]; norm_num
  have π2 : shocksPi (shocksUnif 1 2) shocksExBimodal (10 / 7) = 31 / 60 := by
    simp only [shocksPi]
    simp_rw [b2]
    rw [integral_const_mul, j3]; norm_num
  have N1 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = 1 := by
    simp_rw [a1]; exact hA.g_int
  have N2 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 1 / 2 := by
    simp_rw [a2]; rw [integral_const_mul, j1]; norm_num
  refine ⟨hA, fun x hx y hy hxy => inv_anti₀ hx hxy, fun x hx y hy _ => by
    simp only; rw [mul_inv_cancel₀ (ne_of_gt hx), mul_inv_cancel₀ (ne_of_gt hy)],
    by norm_num, by norm_num, by norm_num, ?_⟩
  rw [shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π1]; norm_num),
    shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π2]; norm_num), π1, π2,
    N1, N2]
  norm_num

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: Proposition 8 is false without Assumption 17.6

SLP §17.6, p. 540. Proposition 8 claims that under Assumptions 17.1, 17.4 and 17.5 every solution
`η` of (3) has a strictly increasing price function `ρ(z) = z/η(z)`. The corrected
`proposition_8` (`FixedPointArguments.ShocksMonotone`) adds Assumption 17.6 (uniform `Ψ`, `G`);
`proposition_8_general_counterexample` there shows only that the book's proof step (Exercise
17.14d) fails under Assumption 17.5. Here the proposition itself is refuted: an economy satisfying
all its hypotheses has a strictly positive continuous fixed point of (4) whose price function is
not invertible.

**The economy.** `x ~ U[1, 2]`, `θ` with the bimodal density `shocksExBimodal` on
`Θ = [1, 3/2]` (bumps on `[1, 11/10]` and `[7/5, 3/2]`), so `Z = [2/3, 2]`;
`H(l) = −l − log(1 − l)` on `[0, 1)`; `V(y) = A y^{1−σ}/(1 − σ)` with `A = 1/60000`, `σ = 1/20`
(`shocksP8V`).

* `monoCexH_assumption17_1H'`, `shocksP8V_assumptions`: Assumption 17.1 for `H`; the repaired
  Assumption 17.1, the repaired Assumption 17.2 (`β = 1 − σ`) and Assumption 17.4 for `V`
  (`Assumption17_1VR.const_mul`, `Assumption17_2R.const_mul`, `MonoAssumption17_4Pos.const_mul`,
  `crra_monoAssumption17_4Pos`).
* `shocksExBimodal_pi_pos`: `π > 0` on `int Z` (although `g` vanishes on `(11/10, 7/5)`), so
  Exercise 17.8b applies; `shocksP8_existsUnique_fixedPoint`: by Proposition 6, `T` has exactly
  one strictly positive continuous fixed point.
* `shocksP8_opT_eq`: with CRRA utility (4) separates, `Tf(z) = A M(f) K(z)` with
  `K(z) = E[θ^{σ−1} | z]`, since `φ(θ′η/θ̃) = A θ̃^{σ−1} (θ′η)^{1−σ}`.
* `shocksExBimodal_integral_inv_values`: `E[θ⁻¹ | z = 4/3] = 4/5`, `E[θ⁻¹ | z = 10/7] = 30/31`;
  `shocksP8_clamp_bounds`: `θ⁻¹ ≤ θ^{σ−1} ≤ (103/100) θ⁻¹` on `Θ`;
  `shocksExBimodal_condLaw_eq`: `G(·|z)` is the same for all `z ∈ [1, 4/3]`.
* `shocksP8_rho_ineq`: for **every** strictly positive fixed point, `ρ(10/7) < ρ(4/3)` and
  `ρ(1) < ρ(4/3)`. The a priori bound `η ≤ 1/200` (from `M ≤ 3/2`, `K ≤ 1` and the small `A`)
  makes `ζ(l) = l²/(1 − l)` nearly quadratic, and `K(10/7)/K(4/3) ≥ (30/31)/((103/100)(4/5))`
  exceeds `(15/14)²/(1 − 15/2800)`, the most that `ρ(4/3) ≤ ρ(10/7)` would allow.
* `shocksP8_not_injective`, **`proposition_8_counterexample`**: `ρ` is neither strictly
  increasing nor injective (intermediate value theorem on `[1, 4/3]` and `[4/3, 10/7]`).
  `proposition_8_assumption17_5_false`: the statement of `proposition_8` without
  Assumption 17.6 is false.
* **The book's Assumption 17.1.** The CRRA `V` has `V'(0) = ∞`, so it satisfies only the repaired
  Assumption 17.1. `shocksP8W y₀` agrees with it on `[y₀, ∞)` and is quadratic below `y₀`
  (`shocks_hasDerivAt_ite` glues the branches); `shocksP8W_assumptions`: it satisfies the book's
  Assumption 17.1 (`C²` on `ℝ₊`) and Assumption 17.4; `shocksP8W_opT_eq`: on fixed points with
  `η ≥ (3/2) y₀` the two operators (4) coincide. **`proposition_8_counterexample_book`**,
  **`proposition_8_false`**: Proposition 8 is false under its own hypotheses.

**Correction (Proposition 8, p. 540, is false).** Under Assumptions 17.1, 17.4 and 17.5 a solution
of (3) need not have an increasing (or even invertible) price function: in the economy above the
unique strictly positive solution under CRRA utility, and a strictly positive solution under a
utility satisfying the book's Assumption 17.1, has `ρ` rising on `[1, 4/3]` and falling from `4/3`
to `10/7`. As `z` rises past `x̄/θ = 10/7`, the conditional law of `θ` given `z` loses the upper
bump of `g`, so `E[θ^{σ−1} | z]` (hence `η`) jumps up faster than `z`. The proposition needs
Assumption 17.6 (`proposition_8`) or a monotone-likelihood condition on `G(·|z)`. Since the
operator also satisfies the hypotheses of Proposition 6, the economy has no equilibrium of the
form `p = ρ(x/θ)` with `ρ` continuous, positive and invertible.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

variable {V V' V'' : ℝ → ℝ}

/-- The repaired Assumption 17.1 is preserved by scaling `V` by `A > 0`. -/
theorem Assumption17_1VR.const_mul (hV : Assumption17_1VR V V' V'') {A : ℝ} (hA : 0 < A) :
    Assumption17_1VR (fun y => A * V y) (fun y => A * V' y) (fun y => A * V'' y) := by
  refine ⟨fun y hy => mul_nonneg hA.le (hV.V_nonneg y hy), continuousOn_const.mul hV.V_cont,
    fun y hy => (hV.V_deriv y hy).const_mul A, fun y hy => (hV.V'_deriv y hy).const_mul A,
    continuousOn_const.mul hV.V''_cont, fun x hx y hy hxy => mul_lt_mul_of_pos_left
    (hV.V_mono hx hy hxy) hA, ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩⟩
  have := hV.V_conc.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  nlinarith

/-- The repaired Assumption 17.2 is preserved by scaling `V` by `A > 0` (relative risk aversion
is unchanged). -/
theorem Assumption17_2R.const_mul {β : ℝ} (h : Assumption17_2R β V' V'') {A : ℝ} (hA : 0 < A) :
    Assumption17_2R β (fun y => A * V' y) (fun y => A * V'' y) := by
  have e : ∀ y, -(y * (A * V'' y)) / (A * V' y) = -(y * V'' y) / V' y := fun y => by
    rw [show -(y * (A * V'' y)) = A * -(y * V'' y) by ring, mul_div_mul_left _ _ hA.ne']
  exact ⟨h.β_nonneg, h.β_lt_one, fun y hy => by rw [e]; exact h.lower y hy,
    fun y hy => by rw [e]; exact h.upper y hy⟩

/-- Assumption 17.4 (on `ℝ₊₊`) is preserved by scaling `V` by `A > 0`. -/
theorem MonoAssumption17_4Pos.const_mul (h : MonoAssumption17_4Pos V' V'') {A : ℝ} (hA : 0 < A) :
    MonoAssumption17_4Pos (fun y => A * V' y) (fun y => A * V'' y) := by
  intro y hy
  have := h y hy
  simp only [monoRRA] at this ⊢
  rwa [show -y * (A * V'' y) = A * (-y * V'' y) by ring, mul_div_mul_left _ _ hA.ne']

/-- CRRA utility with `0 < σ < 1` satisfies Assumption 17.4 (relative risk aversion `σ ≤ 1`). -/
theorem crra_monoAssumption17_4Pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    MonoAssumption17_4Pos (fun y => y ^ (-σ)) (fun y => -σ * y ^ (-σ - 1)) := by
  intro y hy
  have h := (crra_assumption17_2R hσ0 hσ1).upper y hy
  simp only [monoRRA]
  have e : -y * (-σ * y ^ (-σ - 1)) / y ^ (-σ) = -(y * (-σ * y ^ (-σ - 1))) / y ^ (-σ) := by ring
  rw [e]
  have h1 : y * y ^ (-σ - 1) = y ^ (-σ) := by
    rw [Real.rpow_sub_one hy.ne', mul_div_cancel₀ _ hy.ne']
  have h2 : 0 < y ^ (-σ) := Real.rpow_pos_of_pos hy _
  rw [show -(y * (-σ * y ^ (-σ - 1))) = σ * (y * y ^ (-σ - 1)) by ring, h1,
    mul_div_assoc, div_self h2.ne', mul_one]
  linarith

/-- `H(l) = −l − log(1 − l)` satisfies Assumption 17.1 for `H` with `L = 1`. -/
theorem monoCexH_assumption17_1H' : Assumption17_1H 1 monoCexH monoCexH' monoCexH'' := by
  have h := monoCexH_assumption17_1H
  exact ⟨h.L_pos, h.nonneg, fun l hl => (h.hasDeriv_H l hl).mono Ico_subset_Ici_self,
    fun l hl => (h.hasDeriv_H' l hl).mono Ico_subset_Ici_self, h.continuousOn_H'',
    h.strictMonoOn, h.strictConvexOn, h.deriv_zero, h.tendsto_deriv⟩

/-- In the bimodal example `π(z) > 0` on `int Z = (2/3, 2)`: near `θ = 3/2` (upper bump) for
`z < 10/7`, near `θ = 1` (lower bump) for `z ≥ 10/7`. -/
theorem shocksExBimodal_pi_pos {z : ℝ} (hz : 1 / (3 / 2) < z ∧ z < 2 / 1) :
    0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := by
  have hA := shocksExBimodal_assumption
  have hz0 : 0 < z := lt_trans (by norm_num) hz.1
  have hψ1 : ∀ x ∈ Icc (1 : ℝ) 2, shocksUnif 1 2 x = 1 := fun x hx => by
    rw [shocksUnif, indicator_of_mem hx]; norm_num
  have hb1 : ∀ θ, 0 ≤ shocksExBump1 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have hb2 : ∀ θ, 0 ≤ shocksExBump2 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have key : ∀ a b : ℝ, a < b → (∀ θ ∈ Ioo a b,
      0 < shocksExBimodal θ * θ * shocksUnif 1 2 (z * θ)) →
      0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := fun a b hab hpos => by
    refine (integral_pos_iff_support_of_nonneg (fun θ => hA.joint_nonneg z θ)
      (hA.integrable_joint_slice z)).2 ?_
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo a b) fun θ hθ => (hpos θ hθ).ne')
    simp [hab]
  rcases lt_or_ge z (10 / 7) with h | h
  · refine key (max (7 / 5) (1 / z)) (min (3 / 2) (2 / z)) ?_ fun θ hθ => ?_
    · refine max_lt (lt_min (by norm_num) ?_) (lt_min ?_ ?_)
      · rw [lt_div_iff₀ hz0]; linarith
      · rw [div_lt_iff₀ hz0]; linarith [hz.1]
      · exact div_lt_div_of_pos_right (by norm_num) hz0
    · obtain ⟨h1, h2⟩ := hθ
      rw [max_lt_iff] at h1
      rw [lt_min_iff] at h2
      have hθ0 : 0 < θ := lt_trans (by norm_num) h1.1
      have e1 : 1 < z * θ := by rw [div_lt_iff₀ hz0] at h1; linarith [h1.2]
      have e2 : z * θ < 2 := by rw [lt_div_iff₀ hz0] at h2; linarith [h2.2]
      rw [hψ1 _ ⟨e1.le, e2.le⟩, mul_one]
      refine mul_pos ?_ hθ0
      have : shocksExBump2 θ = θ - 7 / 5 := by
        rw [shocksExBump2, indicator_of_mem
          (show θ ∈ Icc (7 / 5 : ℝ) (3 / 2) from ⟨h1.1.le, h2.1.le⟩)]
      simp only [shocksExBimodal]
      linarith [hb1 θ, h1.1]
  · refine key 1 (min (11 / 10) (2 / z)) (lt_min (by norm_num) ?_) fun θ hθ => ?_
    · rw [lt_div_iff₀ hz0]; linarith [hz.2]
    · obtain ⟨h1, h2⟩ := hθ
      rw [lt_min_iff] at h2
      have hθ0 : 0 < θ := lt_trans one_pos h1
      have e1 : 1 < z * θ := by nlinarith
      have e2 : z * θ < 2 := by rw [lt_div_iff₀ hz0] at h2; linarith [h2.2]
      rw [hψ1 _ ⟨e1.le, e2.le⟩, mul_one]
      refine mul_pos ?_ hθ0
      have : shocksExBump1 θ = 11 / 10 - θ := by
        rw [shocksExBump1, indicator_of_mem (show θ ∈ Icc (1 : ℝ) (11 / 10) from ⟨h1.le, h2.1.le⟩)]
      simp only [shocksExBimodal]
      linarith [hb2 θ, h2.1]

/-- In the bimodal example, `E[θ⁻¹ | z = 4/3] = 4/5` and `E[θ⁻¹ | z = 10/7] = 30/31`
(the computation of `proposition_8_general_counterexample`). -/
theorem shocksExBimodal_integral_inv_values :
    (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (4 / 3)) = 4 / 5 ∧
      (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (10 / 7)) =
        30 / 31 := by
  have hA := shocksExBimodal_assumption
  obtain ⟨j1, j2, j3, j4⟩ := shocksExBump_integrals
  have i3 : Integrable fun θ => shocksExBump1 θ * θ := by
    have : (fun θ => shocksExBump1 θ * θ) =
        (Icc (1 : ℝ) (11 / 10)).indicator fun θ => (11 / 10 - θ) * θ := by
      ext θ; simp only [shocksExBump1]
      by_cases h : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i4 : Integrable fun θ => shocksExBump2 θ * θ := by
    have : (fun θ => shocksExBump2 θ * θ) =
        (Icc (7 / 5 : ℝ) (3 / 2)).indicator fun θ => (θ - 7 / 5) * θ := by
      ext θ; simp only [shocksExBump2]
      by_cases h : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hψ1 : ∀ x ∈ Icc (1 : ℝ) 2, shocksUnif 1 2 x = 1 := fun x hx => by
    rw [shocksUnif, indicator_of_mem hx]; norm_num
  have hψ0 : ∀ x, 2 < x → shocksUnif 1 2 x = 0 := fun x hx => by
    rw [shocksUnif, indicator_of_notMem fun h => by linarith [h.2]]
  have hgΘ : ∀ θ, θ ∉ Icc (1 : ℝ) (3 / 2) → shocksExBimodal θ = 0 := hA.g_zero
  have a1 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = shocksExBimodal θ := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one]
    · rw [hgΘ θ h, zero_mul]
  have b1 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (4 / 3 * θ) =
      100 * (shocksExBump1 θ * θ + shocksExBump2 θ * θ) := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one, shocksExBimodal]; ring
    · have h1 : θ ∉ Icc (1 : ℝ) (11 / 10) := fun h' => h ⟨h'.1, by linarith [h'.2]⟩
      have h2 : θ ∉ Icc (7 / 5 : ℝ) (3 / 2) := fun h' => h ⟨by linarith [h'.1], h'.2⟩
      simp [hgΘ θ h, shocksExBump1, shocksExBump2, indicator_of_notMem h1,
        indicator_of_notMem h2]
  have a2 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 100 * shocksExBump1 θ :=
    fun θ => by
      simp only [shocksExBimodal, shocksExBump1, shocksExBump2]
      by_cases h1 : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h => by linarith [h.1, h1.2]),
          hψ1 _ ⟨by linarith [h1.1], by linarith [h1.2]⟩]
        ring
      · rw [indicator_of_notMem h1]
        by_cases h2 : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
        · rw [indicator_of_mem h2]
          rcases h2.1.eq_or_lt with h3 | h3
          · rw [← h3]; ring
          · rw [hψ0 _ (by linarith)]; ring
        · rw [indicator_of_notMem h2]; ring
  have b2 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
      100 * (shocksExBump1 θ * θ) := fun θ => by
    have := a2 θ
    calc shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
        shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) * θ := by ring
      _ = 100 * (shocksExBump1 θ * θ) := by rw [this]; ring
  have π1 : shocksPi (shocksUnif 1 2) shocksExBimodal (4 / 3) = 5 / 4 := by
    simp only [shocksPi]
    simp_rw [b1]
    rw [integral_const_mul, integral_add i3 i4, j3, j4]; norm_num
  have π2 : shocksPi (shocksUnif 1 2) shocksExBimodal (10 / 7) = 31 / 60 := by
    simp only [shocksPi]
    simp_rw [b2]
    rw [integral_const_mul, j3]; norm_num
  have N1 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = 1 := by
    simp_rw [a1]; exact hA.g_int
  have N2 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 1 / 2 := by
    simp_rw [a2]; rw [integral_const_mul, j1]; norm_num
  rw [shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π1]; norm_num),
    shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π2]; norm_num), π1, π2,
    N1, N2]
  norm_num

/-- Against `G(·|z)`, the clamp is invisible. -/
theorem shocksExBimodal_integral_clamp {z : ℝ} (hz : 1 / (3 / 2) < z ∧ z < 2 / 1)
    (k : ℝ → ℝ) :
    ∫ θ, k (shocksClamp 1 (3 / 2) θ) ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2)
      shocksExBimodal z =
      ∫ θ, k θ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z := by
  have hA := shocksExBimodal_assumption
  rw [hA.integral_condLaw hz (shocksExBimodal_pi_pos hz),
    hA.integral_condLaw hz (shocksExBimodal_pi_pos hz)]
  congr 1
  ext θ
  by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
  · rw [shocksClamp_of_mem h]
  · simp [shocksCondDens, hA.g_zero θ h]

/-- The utility `V(y) = A y^{1−σ}/(1 − σ)` with `A = 1/60000`, `σ = 1/20`. -/
noncomputable def shocksP8V (y : ℝ) : ℝ := 1 / 60000 * (y ^ (1 - 1 / 20 : ℝ) / (1 - 1 / 20))

/-- `V'(y) = A y^{−σ}`. -/
noncomputable def shocksP8V' (y : ℝ) : ℝ := 1 / 60000 * y ^ (-(1 / 20) : ℝ)

/-- `V''(y) = −A σ y^{−σ−1}`. -/
noncomputable def shocksP8V'' (y : ℝ) : ℝ := 1 / 60000 * (-(1 / 20) * y ^ (-(1 / 20) - 1 : ℝ))

/-- `shocksP8V` satisfies the repaired Assumption 17.1, the repaired Assumption 17.2 with
`β = 1 − σ`, and Assumption 17.4. -/
theorem shocksP8V_assumptions : Assumption17_1VR shocksP8V shocksP8V' shocksP8V'' ∧
    Assumption17_2R (1 - 1 / 20) shocksP8V' shocksP8V'' ∧
    MonoAssumption17_4Pos shocksP8V' shocksP8V'' :=
  ⟨(crra_assumption17_1VR (σ := 1 / 20) (by norm_num) (by norm_num)).const_mul (by norm_num),
    (crra_assumption17_2R (σ := 1 / 20) (by norm_num) (by norm_num)).const_mul (by norm_num),
    (crra_monoAssumption17_4Pos (σ := 1 / 20) (by norm_num) (by norm_num)).const_mul
      (by norm_num)⟩

/-- `φ(y) = A y^{1−σ}`, split at `y = (c′/c̃) e`. -/
theorem shocksP8_phi_eq {c' ct e : ℝ} (hc' : 0 < c') (hct : 0 < ct) (he : 0 < e) :
    olgPhi shocksP8V' (c' / ct * e) =
      1 / 60000 * (ct ^ (1 - 1 / 20 : ℝ))⁻¹ * (c' * e) ^ (1 - 1 / 20 : ℝ) := by
  have hy : 0 < c' / ct * e := mul_pos (div_pos hc' hct) he
  simp only [olgPhi, shocksP8V']
  have h1 : c' / ct * e * (c' / ct * e) ^ (-(1 / 20) : ℝ) = (c' / ct * e) ^ (1 - 1 / 20 : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add hy, Real.rpow_one]
  rw [show c' / ct * e * (1 / 60000 * (c' / ct * e) ^ (-(1 / 20) : ℝ)) =
    1 / 60000 * (c' / ct * e * (c' / ct * e) ^ (-(1 / 20) : ℝ)) by ring, h1,
    show c' / ct * e = c' * e / ct by ring, Real.div_rpow (mul_pos hc' he).le hct.le]
  ring

variable {Z : Type*} [MeasurableSpace Z] {L : ℝ} {H H' H'' : ℝ → ℝ}

/-- With this utility, (4) separates: `Tf(z) = A M(f) K(z)`. -/
theorem shocksP8_opT_eq (hH : Assumption17_1H L H H' H'') (μ : Measure (ℝ × Z))
    (ν : Z → Measure ℝ) (f : Z → ℝ) (hf : ∀ z, 0 < f z) (z : Z) :
    shocksOpT L H' shocksP8V' 1 (3 / 2) μ ν f z =
      1 / 60000 * (∫ ω, (shocksClamp 1 (3 / 2) ω.1 * olgZetaInv L H' (f ω.2)) ^
        (1 - 1 / 20 : ℝ) ∂μ) * ∫ θ, (shocksClamp 1 (3 / 2) θ ^ (1 - 1 / 20 : ℝ))⁻¹ ∂ν z := by
  have hc : ∀ t, 0 < shocksClamp 1 (3 / 2) t := fun t =>
    one_pos.trans_le (shocksClamp_mem (by norm_num) t).1
  have hphi : ∀ θt, shocksPhiF L H' shocksP8V' 1 (3 / 2) μ f θt =
      (1 / 60000 * (shocksClamp 1 (3 / 2) θt ^ (1 - 1 / 20 : ℝ))⁻¹) *
        ∫ ω, (shocksClamp 1 (3 / 2) ω.1 * olgZetaInv L H' (f ω.2)) ^ (1 - 1 / 20 : ℝ) ∂μ := by
    intro θt
    rw [← integral_const_mul]
    simp only [shocksPhiF, shocksIntegrand, shocksRatio]
    congr 1
    ext ω
    exact shocksP8_phi_eq (hc _) (hc _) (hH.zetaInv_pos (hf ω.2))
  simp only [shocksOpT]
  simp_rw [hphi]
  rw [integral_mul_const, integral_const_mul]
  ring

/-- `Z = [x̲/θ̄, x̄/θ̲] = [2/3, 2]` is nonempty. -/
theorem shocksP8_hZ : (1 : ℝ) / (3 / 2) ≤ 2 / 1 := by norm_num

/-- For `z ∈ [1, 4/3]` the conditional law of `θ` does not depend on `z`. -/
theorem shocksExBimodal_condLaw_eq {z : ℝ} (hz : z ∈ Icc (1 : ℝ) (4 / 3)) :
    shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z =
      shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal 1 := by
  have hA := shocksExBimodal_assumption
  have e : ∀ w ∈ Icc (1 : ℝ) (4 / 3), ∀ θ,
      shocksExBimodal θ * θ * shocksUnif 1 2 (w * θ) = shocksExBimodal θ * θ := by
    intro w hw θ
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [shocksUnif, indicator_of_mem (show w * θ ∈ Icc (1 : ℝ) 2 from
        ⟨by nlinarith [hw.1, h.1], by nlinarith [hw.2, h.2, hw.1, h.1]⟩)]
      norm_num
    · rw [hA.g_zero θ h]; ring
  have hd : ∀ w ∈ Icc (1 : ℝ) (4 / 3), shocksCondDens (shocksUnif 1 2) shocksExBimodal w =
      fun θ => shocksExBimodal θ * θ / ∫ t, shocksExBimodal t * t := by
    intro w hw
    ext θ
    simp only [shocksCondDens, shocksPi]
    rw [e w hw θ]
    simp_rw [e w hw]
  have hz' : 1 / (3 / 2) < z ∧ z < 2 / 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have h1 : (1 : ℝ) / (3 / 2) < 1 ∧ (1 : ℝ) < 2 / 1 := ⟨by norm_num, by norm_num⟩
  simp only [shocksCondLaw, hz', h1, and_self, ↓reduceIte]
  rw [hd z hz, hd 1 ⟨le_rfl, by norm_num⟩]

/-- Bounds on the clamp's power: `c⁻¹ ≤ (c^{1−σ})⁻¹ ≤ min(1, (103/100) c⁻¹)`. -/
theorem shocksP8_clamp_bounds (t : ℝ) :
    0 ≤ (shocksClamp 1 (3 / 2) t)⁻¹ ∧
    (shocksClamp 1 (3 / 2) t)⁻¹ ≤ (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹ ∧
    (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹ ≤ 1 ∧
    (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹ ≤ 103 / 100 * (shocksClamp 1 (3 / 2) t)⁻¹ := by
  obtain ⟨h1, h2⟩ := shocksClamp_mem (θlo := (1 : ℝ)) (θhi := 3 / 2) (by norm_num) t
  set c := shocksClamp 1 (3 / 2) t
  have hc : 0 < c := one_pos.trans_le h1
  have hp : 0 < c ^ (1 - 1 / 20 : ℝ) := Real.rpow_pos_of_pos hc _
  have hσ : c ^ (1 / 20 : ℝ) ≤ 103 / 100 := by
    have h3 : c ^ (1 / 20 : ℝ) ≤ (3 / 2 : ℝ) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow hc.le h2 (by norm_num)
    have h4 : (3 / 2 : ℝ) ^ (1 / 20 : ℝ) ≤ ((103 / 100 : ℝ) ^ (20 : ℕ)) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h4
    norm_num at h4
    exact h3.trans h4
  have hσ0 : 0 < c ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hc _
  have e : c ^ (1 - 1 / 20 : ℝ) = c / c ^ (1 / 20 : ℝ) := by
    rw [Real.rpow_sub hc, Real.rpow_one]
  refine ⟨inv_nonneg.2 hc.le, inv_anti₀ hp ?_, inv_le_one_of_one_le₀ ?_, ?_⟩
  · calc c ^ (1 - 1 / 20 : ℝ) ≤ c ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = c := Real.rpow_one c
  · exact Real.one_le_rpow h1 (by norm_num)
  · rw [e, inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hσ (inv_nonneg.2 hc.le)

/-- The functions `c(t)⁻¹` and `(c(t)^{1−σ})⁻¹` are continuous. -/
theorem shocksP8_continuous :
    Continuous (fun t => (shocksClamp 1 (3 / 2) t)⁻¹) ∧
      Continuous (fun t => (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹) := by
  have hc : ∀ t, 0 < shocksClamp 1 (3 / 2) t := fun t =>
    one_pos.trans_le (shocksClamp_mem (by norm_num) t).1
  exact ⟨continuous_shocksClamp.inv₀ fun t => (hc t).ne',
    (continuous_shocksClamp.rpow_const fun _ => Or.inr (by norm_num)).inv₀
      fun t => (Real.rpow_pos_of_pos (hc t) _).ne'⟩

/-- `ζ(y) = y²/(1 − y)` for `H'(l) = l/(1 − l)`. -/
theorem shocksP8_zeta_eq {y F : ℝ} (hy : y < 1) (h : olgZeta monoCexH' y = F) :
    F * (1 - y) = y ^ 2 := by
  have h1 : 1 - y ≠ 0 := (sub_pos.2 hy).ne'
  rw [← h]
  simp only [olgZeta, monoCexH']
  field_simp

/-- **The key estimate.** For every strictly positive fixed point `f` of `T` in the bimodal economy,
with `η = ζ⁻¹ ∘ f` and `ρ(z) = z/η(z)`: `ρ(10/7) < ρ(4/3)` and `ρ(1) < ρ(4/3)`. -/
theorem shocksP8_rho_ineq (f : Icc (1 / (3 / 2) : ℝ) (2 / 1) → ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) :
    (10 / 7 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨10 / 7, by norm_num, by norm_num⟩) <
        (4 / 3 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨4 / 3, by norm_num, by norm_num⟩) ∧
      (1 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨1, by norm_num, by norm_num⟩) <
        (4 / 3 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨4 / 3, by norm_num, by norm_num⟩) := by
  have hH := monoCexH_assumption17_1H'
  have hA := shocksExBimodal_assumption
  have hπ : ∀ z : ℝ, 1 / (3 / 2) < z ∧ z < 2 / 1 →
      0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := fun z hz => shocksExBimodal_pi_pos hz
  have := isProbabilityMeasure_shocksJointLaw hA shocksP8_hZ
  have hν : ∀ z : ℝ, IsProbabilityMeasure
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) :=
    hA.isProbabilityMeasure_condLaw' hπ
  obtain ⟨hcon1, hcon2⟩ := shocksP8_continuous
  set μ := shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal
  set η := fun z => olgZetaInv 1 monoCexH' (f z) with hηdef
  set M := ∫ ω, (shocksClamp 1 (3 / 2) ω.1 * η ω.2) ^ (1 - 1 / 20 : ℝ) ∂μ with hMdef
  set K := fun z : ℝ => ∫ θ, (shocksClamp 1 (3 / 2) θ ^ (1 - 1 / 20 : ℝ))⁻¹
    ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z with hKdef
  have hfK : ∀ z, f z = 1 / 60000 * M * K z := fun z => by
    rw [hfix z, shocksP8_opT_eq hH μ _ f hfpos z]
  have hηmem : ∀ z, η z ∈ Ioo 0 1 := fun z =>
    ⟨hH.zetaInv_pos (hfpos z), (hH.zetaInv_mem (hfpos z).le).2⟩
  have hζ : ∀ z, f z * (1 - η z) = η z ^ 2 := fun z =>
    shocksP8_zeta_eq (hηmem z).2 (hH.zeta_zetaInv (hfpos z).le)
  -- bounds on `M` and `K`
  have hc : ∀ t, shocksClamp 1 (3 / 2) t ∈ Icc (1 : ℝ) (3 / 2) := shocksClamp_mem (by norm_num)
  have hM0 : 0 ≤ M := integral_nonneg fun ω => Real.rpow_nonneg
    (mul_nonneg (one_pos.trans_le (hc ω.1).1).le (hηmem ω.2).1.le) _
  have hM1 : M ≤ 3 / 2 := by
    have : M ≤ ∫ _ω, (3 / 2 : ℝ) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun ω => Real.rpow_nonneg
        (mul_nonneg (one_pos.trans_le (hc ω.1).1).le (hηmem ω.2).1.le) _) (integrable_const _)
        (ae_of_all _ fun ω => ?_)
      have h1 := hc ω.1
      have h2 := hηmem ω.2
      have h3 : shocksClamp 1 (3 / 2) ω.1 * η ω.2 ≤ 3 / 2 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
      calc (shocksClamp 1 (3 / 2) ω.1 * η ω.2) ^ (1 - 1 / 20 : ℝ)
          ≤ (3 / 2 : ℝ) ^ (1 - 1 / 20 : ℝ) :=
            Real.rpow_le_rpow (mul_nonneg (by linarith [h1.1]) h2.1.le) h3 (by norm_num)
        _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 / 2 := Real.rpow_one _
    rwa [integral_const, probReal_univ, one_smul] at this
  have hK0 : ∀ z, 0 ≤ K z := fun z => integral_nonneg fun θ =>
    le_trans (shocksP8_clamp_bounds θ).1 (shocksP8_clamp_bounds θ).2.1
  have hK1 : ∀ z, K z ≤ 1 := fun z => by
    have : K z ≤ ∫ _θ, (1 : ℝ) ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z :=
      integral_mono_of_nonneg (ae_of_all _ fun θ =>
        le_trans (shocksP8_clamp_bounds θ).1 (shocksP8_clamp_bounds θ).2.1) (integrable_const _)
        (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).2.2.1)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hint : ∀ z, Integrable (fun t => (shocksClamp 1 (3 / 2) t)⁻¹)
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) := fun z =>
    Integrable.of_bound hcon1.aestronglyMeasurable 1 (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (shocksP8_clamp_bounds t).1]
      exact (shocksP8_clamp_bounds t).2.1.trans (shocksP8_clamp_bounds t).2.2.1)
  have hint' : ∀ z, Integrable (fun t => (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹)
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) := fun z =>
    Integrable.of_bound hcon2.aestronglyMeasurable 1 (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((shocksP8_clamp_bounds t).1.trans
        (shocksP8_clamp_bounds t).2.1)]
      exact (shocksP8_clamp_bounds t).2.2.1)
  obtain ⟨v1, v2⟩ := shocksExBimodal_integral_inv_values
  have hK2 : 30 / 31 ≤ K (10 / 7) := by
    rw [← v2, ← shocksExBimodal_integral_clamp ⟨by norm_num, by norm_num⟩ fun t => t⁻¹]
    exact integral_mono_of_nonneg (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).1) (hint' _)
      (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).2.1)
  have hK43 : K (4 / 3) ≤ 103 / 100 * (4 / 5) := by
    rw [← v1, ← shocksExBimodal_integral_clamp ⟨by norm_num, by norm_num⟩ fun t => t⁻¹,
      ← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun θ =>
      (shocksP8_clamp_bounds θ).1.trans (shocksP8_clamp_bounds θ).2.1) ((hint _).const_mul _)
      (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).2.2.2)
  have hKeq : K 1 = K (4 / 3) := by
    simp only [hKdef]
    rw [shocksExBimodal_condLaw_eq (z := 4 / 3) ⟨by norm_num, by norm_num⟩]
  -- `η ≤ 1/200`
  have hηle : ∀ z, η z ≤ 1 / 200 := fun z => by
    have h1 : f z ≤ 1 / 40000 := by
      rw [hfK z]
      have := mul_le_mul hM1 (hK1 z) (hK0 z) (by norm_num)
      nlinarith
    have h2 := hζ z
    have h3 := hηmem z
    nlinarith [h3.1, h3.2, hfpos z]
  -- the comparison
  set z₁ : Icc (1 / (3 / 2) : ℝ) (2 / 1) := ⟨4 / 3, by norm_num, by norm_num⟩
  set z₂ : Icc (1 / (3 / 2) : ℝ) (2 / 1) := ⟨10 / 7, by norm_num, by norm_num⟩
  set z₀ : Icc (1 / (3 / 2) : ℝ) (2 / 1) := ⟨1, by norm_num, by norm_num⟩
  have hP : 0 < 1 / 60000 * M := by
    by_contra h
    push Not at h
    have := hfpos z₁
    rw [hfK z₁] at this
    nlinarith [hK0 (4 / 3)]
  have hη1 := hηmem z₁
  have hη2 := hηmem z₂
  refine ⟨?_, ?_⟩
  · rw [div_lt_div_iff₀ hη2.1 hη1.1]
    by_contra hcon
    push Not at hcon
    -- `η₂ ≤ s = (15/14) η₁`
    set s := 15 / 14 * η z₁
    have hs : η z₂ ≤ s := by simp only [s]; linarith
    have hs1 : s ≤ 15 / 2800 := by simp only [s]; linarith [hηle z₁]
    have e1 := hζ z₁
    have e2 := hζ z₂
    have hf2 := hfpos z₂
    have hf1 := hfpos z₁
    have step1 : f z₂ * (1 - 15 / 2800) ≤ f z₂ * (1 - η z₂) :=
      mul_le_mul_of_nonneg_left (by linarith) hf2.le
    have step2 : η z₂ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hη2.1.le hs 2
    have step3 : s ^ 2 = 225 / 196 * (f z₁ * (1 - η z₁)) := by rw [e1]; simp only [s]; ring
    have step4 : f z₁ * (1 - η z₁) ≤ f z₁ := by nlinarith [hη1.1]
    have key : f z₂ * (1 - 15 / 2800) ≤ 225 / 196 * f z₁ := by nlinarith
    rw [hfK z₁, hfK z₂] at key
    have key' : (1 / 60000 * M) * (K (10 / 7) * (1 - 15 / 2800)) ≤
        (1 / 60000 * M) * (225 / 196 * K (4 / 3)) := by
      have : (1 / 60000 * M) * (K (10 / 7) * (1 - 15 / 2800)) =
          1 / 60000 * M * K (10 / 7) * (1 - 15 / 2800) := by ring
      rw [this]
      linarith
    have := le_of_mul_le_mul_left key' hP
    linarith
  · have hf : f z₀ = f z₁ := by
      rw [hfK z₀, hfK z₁]
      change 1 / 60000 * M * K 1 = 1 / 60000 * M * K (4 / 3)
      rw [hKeq]
    have he : η z₀ = η z₁ := by simp only [hηdef, hf]
    change (1 : ℝ) / η z₀ < (4 / 3 : ℝ) / η z₁
    rw [he]
    exact div_lt_div_of_pos_right (by norm_num) hη1.1

/-- The bimodal economy has exactly one strictly positive continuous fixed point of `T`
(Proposition 6 applies: the CRRA utility satisfies the repaired Assumption 17.2). -/
theorem shocksP8_existsUnique_fixedPoint :
    ∃! f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) ∧
      ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
        (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
        (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z := by
  have hA := shocksExBimodal_assumption
  have hπ : ∀ z : ℝ, 1 / (3 / 2) < z ∧ z < 2 / 1 →
      0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := fun z hz => shocksExBimodal_pi_pos hz
  have := isProbabilityMeasure_shocksJointLaw hA shocksP8_hZ
  have : ∀ z : Icc (1 / (3 / 2) : ℝ) (2 / 1),
      IsProbabilityMeasure (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) :=
    fun z => hA.isProbabilityMeasure_condLaw' hπ z.1
  have : Nonempty (Icc (1 / (3 / 2) : ℝ) (2 / 1)) := ⟨⟨_, left_mem_Icc.2 shocksP8_hZ⟩⟩
  exact proposition_6 hA.θlo_pos hA.θlo_lt.le monoCexH_assumption17_1H' shocksP8V_assumptions.1
    shocksP8V_assumptions.2.1 _ _ fun h => (hA.ex_17_8b hπ h).domRestrict

/-- For every strictly positive continuous fixed point of `T` in the bimodal economy, the price
function `ρ(z) = z/ζ⁻¹(f(z))` is not invertible (it rises on `[1, 4/3]` and falls between `4/3`
and `10/7`), and in particular not strictly increasing. -/
theorem shocksP8_not_injective (f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) :
    ¬ Function.Injective (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
        (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) ∧
      ¬ StrictMono (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
        (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) := by
  have hH := monoCexH_assumption17_1H'
  obtain ⟨h1, h2⟩ := shocksP8_rho_ineq f hfpos hfix
  set r := fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) => (z : ℝ) / olgZetaInv 1 monoCexH' (f z)
    with hrdef
  refine ⟨fun hinj => ?_, fun hmono => ?_⟩
  · have hr : Continuous r := continuous_subtype_val.div
      (hH.zetaInv_continuousOn.comp_continuous f.continuous fun z => (hfpos z).le)
      fun z => (hH.zetaInv_pos (hfpos z)).ne'
    set R : ℝ → ℝ := fun t => r (projIcc _ _ shocksP8_hZ t) with hRdef
    have hR : Continuous R := hr.comp continuous_projIcc
    have hRv : ∀ t (ht : t ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1)), R t = r ⟨t, ht⟩ := fun t ht => by
      simp only [hRdef, projIcc_of_mem _ ht]
    have e0 := hRv 1 ⟨by norm_num, by norm_num⟩
    have e1 := hRv (4 / 3) ⟨by norm_num, by norm_num⟩
    have e2 := hRv (10 / 7) ⟨by norm_num, by norm_num⟩
    have h1' : R (10 / 7) < R (4 / 3) := by rw [e1, e2]; exact h1
    have h2' : R 1 < R (4 / 3) := by rw [e0, e1]; exact h2
    obtain ⟨v, hvdef⟩ : ∃ v, v = (max (R 1) (R (10 / 7)) + R (4 / 3)) / 2 := ⟨_, rfl⟩
    have hv : max (R 1) (R (10 / 7)) < R (4 / 3) := max_lt h2' h1'
    have hv1 : v ∈ Icc (R 1) (R (4 / 3)) :=
      ⟨by linarith [le_max_left (R 1) (R (10 / 7))], by linarith⟩
    have hv2 : v ∈ Icc (R (10 / 7)) (R (4 / 3)) :=
      ⟨by linarith [le_max_right (R 1) (R (10 / 7))], by linarith⟩
    obtain ⟨t1, ht1, hRt1⟩ :=
      intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 4 / 3) hR.continuousOn hv1
    obtain ⟨t2, ht2, hRt2⟩ :=
      intermediate_value_Icc' (by norm_num : (4 / 3 : ℝ) ≤ 10 / 7) hR.continuousOn hv2
    have hne : t1 ≠ 4 / 3 := fun h => by rw [h] at hRt1; linarith
    have hlt : t1 < t2 := lt_of_lt_of_le (lt_of_le_of_ne ht1.2 hne) ht2.1
    have heq := hinj (a₁ := projIcc _ _ shocksP8_hZ t1) (a₂ := projIcc _ _ shocksP8_hZ t2)
      (by change R t1 = R t2; rw [hRt1, hRt2])
    have hm1 : t1 ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1) := by
      constructor <;> norm_num <;> linarith [ht1.1, ht1.2]
    have hm2 : t2 ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1) := by
      constructor <;> norm_num <;> linarith [ht2.1, ht2.2]
    rw [projIcc_of_mem _ hm1, projIcc_of_mem _ hm2] at heq
    exact hlt.ne (Subtype.mk.inj heq)
  · have := hmono (a := ⟨4 / 3, by norm_num, by norm_num⟩) (b := ⟨10 / 7, by norm_num, by norm_num⟩)
      (by change (4 / 3 : ℝ) < 10 / 7; norm_num)
    exact absurd this (not_lt.2 h1.le)

/-- **Proposition 8 under Assumption 17.5 alone: counterexample.** In the economy
`x ~ U[1, 2]`, `θ` with the bimodal density `shocksExBimodal` on `Θ = [1, 3/2]` (Assumption 17.5),
`H(l) = −l − log(1 − l)` on `[0, 1)` (Assumption 17.1) and
`V(y) = A y^{1−σ}/(1 − σ)`, `A = 1/60000`, `σ = 1/20` (the repaired Assumption 17.1, the repaired
Assumption 17.2 with `β = 1 − σ`, and Assumption 17.4), the operator (4) has exactly one strictly
positive continuous fixed point (Proposition 6), and for it, as for every strictly positive fixed
point, the price function `ρ(z) = z/ζ⁻¹(f(z))` is neither strictly increasing nor even
invertible. So the fixed point does not describe an equilibrium. -/
theorem proposition_8_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal ∧
      Assumption17_1H 1 monoCexH monoCexH' monoCexH'' ∧
      Assumption17_1VR shocksP8V shocksP8V' shocksP8V'' ∧
      Assumption17_2R (1 - 1 / 20) shocksP8V' shocksP8V'' ∧
      MonoAssumption17_4Pos shocksP8V' shocksP8V'' ∧
      (∃! f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) ∧
        ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
          (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) ∧
      ∀ f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) →
        (∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
          (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) →
        ¬ Function.Injective (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
          (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) :=
  ⟨shocksExBimodal_assumption, monoCexH_assumption17_1H', shocksP8V_assumptions.1,
    shocksP8V_assumptions.2.1, shocksP8V_assumptions.2.2, shocksP8_existsUnique_fixedPoint,
    fun f hfpos hfix => (shocksP8_not_injective f hfpos hfix).1⟩

/-- **Correction (Proposition 8 is false under Assumption 17.5 alone).** The statement of
`proposition_8` without Assumption 17.6 (uniform `Ψ`, `G`) fails: see
`proposition_8_counterexample`. -/
theorem proposition_8_assumption17_5_false :
    ¬ ∀ (xlo xhi θlo θhi : ℝ) (hZ : xlo / θhi ≤ xhi / θlo) (ψ g : ℝ → ℝ) (L : ℝ)
      (H H' H'' V V' V'' : ℝ → ℝ), ShocksAssumption17_5 xlo xhi θlo θhi ψ g →
      Assumption17_1H L H H' H'' → Assumption17_1VR V V' V'' → MonoAssumption17_4Pos V' V'' →
      ∀ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) →
      (∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z) →
      StrictMono fun z : Icc (xlo / θhi) (xhi / θlo) => (z : ℝ) / olgZetaInv L H' (f z) := by
  intro h
  obtain ⟨f, ⟨hfpos, hfix⟩, -⟩ := shocksP8_existsUnique_fixedPoint
  exact (shocksP8_not_injective f hfpos hfix).2 (h 1 2 1 (3 / 2) shocksP8_hZ _ _ 1 _ _ _ _ _ _
    shocksExBimodal_assumption monoCexH_assumption17_1H' shocksP8V_assumptions.1
    shocksP8V_assumptions.2.2 f hfpos hfix)

/-! ### The book's Assumption 17.1: a utility with `V'(0) < ∞` -/

/-- Gluing two differentiable branches at `y₀` with matching values and derivatives. -/
theorem shocks_hasDerivAt_ite {g h : ℝ → ℝ} {y₀ y d : ℝ} (hg : y₀ ≤ y → HasDerivAt g d y)
    (hh : y ≤ y₀ → HasDerivAt h d y) (heq : g y₀ = h y₀) :
    HasDerivAt (fun t => if y₀ ≤ t then g t else h t) d y := by
  rcases lt_trichotomy y y₀ with hy | hy | hy
  · refine (hh hy.le).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hy] with t ht
    simp [not_le.2 (mem_Iio.1 ht)]
  · subst hy
    have h1 : HasDerivWithinAt (fun t => if y ≤ t then g t else h t) d (Ici y) y :=
      (hg le_rfl).hasDerivWithinAt.congr (fun t ht => by simp [mem_Ici.1 ht]) (by simp)
    have h2 : HasDerivWithinAt (fun t => if y ≤ t then g t else h t) d (Iic y) y := by
      refine (hh le_rfl).hasDerivWithinAt.congr (fun t ht => ?_) (by simp [heq])
      rcases (mem_Iic.1 ht).eq_or_lt with h' | h'
      · subst h'; simp [heq]
      · simp [not_le.2 h']
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · refine (hg hy.le).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with t ht
    simp [(mem_Ioi.1 ht).le]

/-- The utility `W = V` on `[y₀, ∞)` (the CRRA utility `shocksP8V`, shifted to be continuous),
and below `y₀` the quadratic with `W(0) = 0` whose derivative continues `V'` linearly. -/
noncomputable def shocksP8W (y₀ y : ℝ) : ℝ :=
  if y₀ ≤ y then shocksP8V y - shocksP8V y₀ +
    1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * ((1 + 1 / 20) * y₀ - 1 / 20 * y₀ ^ 2 / (2 * y₀))
  else 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * ((1 + 1 / 20) * y - 1 / 20 * y ^ 2 / (2 * y₀))

/-- `W' = V'` on `[y₀, ∞)`, linear below `y₀`. -/
noncomputable def shocksP8W' (y₀ y : ℝ) : ℝ :=
  if y₀ ≤ y then shocksP8V' y else 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * y / y₀)

/-- `W'' = V''` on `[y₀, ∞)`, constant below `y₀`. -/
noncomputable def shocksP8W'' (y₀ y : ℝ) : ℝ :=
  1 / 60000 * (-(1 / 20) * max y y₀ ^ (-(1 / 20) - 1 : ℝ))

variable {y₀ : ℝ}

/-- `W' = dW/dy`. -/
theorem shocksP8W_hasDerivAt (hy₀ : 0 < y₀) (y : ℝ) :
    HasDerivAt (shocksP8W y₀) (shocksP8W' y₀ y) y := by
  have hV := shocksP8V_assumptions.1
  have hl : ∀ t, HasDerivAt (fun t => 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) *
      ((1 + 1 / 20) * t - 1 / 20 * t ^ 2 / (2 * y₀)))
      (1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * t / y₀)) t := fun t => by
    have := (((hasDerivAt_id t).const_mul (1 + 1 / 20 : ℝ)).sub
      (((hasDerivAt_pow 2 t).const_mul (1 / 20 : ℝ)).div_const (2 * y₀))).const_mul
      (1 / 60000 * y₀ ^ (-(1 / 20) : ℝ))
    refine this.congr_deriv ?_
    field_simp
    ring
  refine shocks_hasDerivAt_ite (fun h => ?_) (fun h => ?_) ?_
  · simp only [shocksP8W', h, ↓reduceIte]
    exact ((hV.V_deriv y (hy₀.trans_le h)).sub_const _).add_const _
  · rcases h.eq_or_lt with h' | h'
    · subst h'
      simp only [shocksP8W', le_refl, ↓reduceIte]
      convert hl y using 1
      simp only [shocksP8V']
      field_simp
      ring
    · simp only [shocksP8W', not_le.2 h', ↓reduceIte]
      exact hl y
  · ring

/-- `W'' = dW'/dy`. -/
theorem shocksP8W'_hasDerivAt (hy₀ : 0 < y₀) (y : ℝ) :
    HasDerivAt (shocksP8W' y₀) (shocksP8W'' y₀ y) y := by
  have hV := shocksP8V_assumptions.1
  have e : y₀ ^ (-(1 / 20) - 1 : ℝ) = y₀ ^ (-(1 / 20) : ℝ) / y₀ := Real.rpow_sub_one hy₀.ne' _
  refine shocks_hasDerivAt_ite (fun h => ?_) (fun h => ?_) ?_
  · rw [shocksP8W'', max_eq_left h]
    exact hV.V'_deriv y (hy₀.trans_le h)
  · rw [shocksP8W'', max_eq_right h, e]
    have := ((((hasDerivAt_id y).const_mul (1 / 20 : ℝ)).div_const y₀).const_sub
      (1 + 1 / 20 : ℝ)).const_mul (1 / 60000 * y₀ ^ (-(1 / 20) : ℝ))
    refine this.congr_deriv ?_
    field_simp
  · simp only [shocksP8V']
    field_simp
    ring

/-- `W' > 0`. -/
theorem shocksP8W'_pos (hy₀ : 0 < y₀) (y : ℝ) : 0 < shocksP8W' y₀ y := by
  simp only [shocksP8W']
  split_ifs with h
  · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (hy₀.trans_le h) _)
  · have h1 : y / y₀ < 1 := (div_lt_one hy₀).2 (not_le.1 h)
    have h2 : 1 / 20 * y / y₀ = 1 / 20 * (y / y₀) := by ring
    refine mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hy₀ _)) ?_
    rw [h2]
    linarith

/-- `W'' < 0`. -/
theorem shocksP8W''_neg (hy₀ : 0 < y₀) (y : ℝ) : shocksP8W'' y₀ y < 0 := by
  have := Real.rpow_pos_of_pos (hy₀.trans_le (le_max_right y y₀)) (-(1 / 20) - 1 : ℝ)
  simp only [shocksP8W'']
  nlinarith

/-- **`W` satisfies the book's Assumption 17.1** (`V` twice continuously differentiable on
`ℝ₊ = [0, ∞)`, `V'(0) < ∞`, strictly increasing and strictly concave) **and Assumption 17.4**
(relative risk aversion `≤ 1` on `ℝ₊`). -/
theorem shocksP8W_assumptions (hy₀ : 0 < y₀) :
    Assumption17_1V (shocksP8W y₀) (shocksP8W' y₀) (shocksP8W'' y₀) ∧
      MonoAssumption17_4 (shocksP8W' y₀) (shocksP8W'' y₀) := by
  have hd := shocksP8W_hasDerivAt hy₀
  have hd' := shocksP8W'_hasDerivAt hy₀
  have hc : Continuous (shocksP8W y₀) := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hc' : Continuous (shocksP8W' y₀) :=
    continuous_iff_continuousAt.2 fun y => (hd' y).continuousAt
  have hmono : StrictMonoOn (shocksP8W y₀) (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn fun x hx => by
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact shocksP8W'_pos hy₀ x
  have hanti : StrictAnti (shocksP8W' y₀) := by
    have := strictAntiOn_of_deriv_neg convex_univ hc'.continuousOn fun x _ => by
      rw [(hd' x).deriv]
      exact shocksP8W''_neg hy₀ x
    exact fun a b hab => this (mem_univ a) (mem_univ b) hab
  have hderiv : deriv (shocksP8W y₀) = shocksP8W' y₀ := funext fun y => (hd y).deriv
  have h0 : shocksP8W y₀ 0 = 0 := by simp [shocksP8W, not_le.2 hy₀]
  refine ⟨⟨fun y hy => ?_, fun y _ => (hd y).hasDerivWithinAt,
    fun y _ => (hd' y).hasDerivWithinAt, ?_, hmono, ?_⟩, fun y hy => ?_⟩
  · rw [← h0]
    exact hmono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
  · refine Continuous.continuousOn (continuous_const.mul (continuous_const.mul ?_))
    exact (continuous_id.max continuous_const).rpow_const fun y =>
      Or.inl (hy₀.trans_le (le_max_right y y₀)).ne'
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hc.continuousOn ?_
    rw [hderiv]
    exact fun a _ b _ hab => hanti hab
  · -- relative risk aversion
    have hW := shocksP8W'_pos hy₀ y
    simp only [monoRRA]
    rw [div_le_one hW]
    simp only [shocksP8W'', shocksP8W']
    split_ifs with h
    · rw [max_eq_left h]
      have hy0 : 0 < y := hy₀.trans_le h
      have e : y * y ^ (-(1 / 20) - 1 : ℝ) = y ^ (-(1 / 20) : ℝ) := by
        rw [Real.rpow_sub_one hy0.ne', mul_div_cancel₀ _ hy0.ne']
      have hp := Real.rpow_pos_of_pos hy0 (-(1 / 20) : ℝ)
      simp only [shocksP8V']
      have : -y * (1 / 60000 * (-(1 / 20) * y ^ (-(1 / 20) - 1 : ℝ))) =
          1 / 60000 * (1 / 20) * (y * y ^ (-(1 / 20) - 1 : ℝ)) := by ring
      rw [this, e]
      nlinarith
    · have hlt : y < y₀ := not_le.1 h
      rw [max_eq_right hlt.le, Real.rpow_sub_one hy₀.ne']
      have hp := Real.rpow_pos_of_pos hy₀ (-(1 / 20) : ℝ)
      have hq : y / y₀ < 1 := (div_lt_one hy₀).2 hlt
      have hq0 : 0 ≤ y / y₀ := div_nonneg hy hy₀.le
      have e1 : -y * (1 / 60000 * (-(1 / 20) * (y₀ ^ (-(1 / 20) : ℝ) / y₀))) =
          1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 / 20 * (y / y₀)) := by
        field_simp
      have e2 : 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * y / y₀) =
          1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * (y / y₀)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- On functions whose `η = ζ⁻¹ ∘ f` stays above `(3/2) y₀`, the operators (4) built from `W`
and from the CRRA utility coincide: all arguments of `φ` are `≥ (θ̲/θ̄)(3/2) y₀ = y₀`. -/
theorem shocksP8W_opT_eq {Z : Type*} [MeasurableSpace Z] {L : ℝ} {H' : ℝ → ℝ} (hy₀ : 0 < y₀)
    (μ : Measure (ℝ × Z)) (ν : Z → Measure ℝ) (f : Z → ℝ)
    (hη : ∀ z, 3 / 2 * y₀ ≤ olgZetaInv L H' (f z)) (z : Z) :
    shocksOpT L H' (shocksP8W' y₀) 1 (3 / 2) μ ν f z =
      shocksOpT L H' shocksP8V' 1 (3 / 2) μ ν f z := by
  have e : ∀ θt (ω : ℝ × Z), shocksIntegrand L H' (shocksP8W' y₀) 1 (3 / 2) f θt ω =
      shocksIntegrand L H' shocksP8V' 1 (3 / 2) f θt ω := fun θt ω => by
    have h1 := (shocksRatio_mem (θlo := (1 : ℝ)) (θhi := 3 / 2) one_pos (by norm_num) ω.1 θt).1
    have h2 := hη ω.2
    have hle : y₀ ≤ shocksRatio 1 (3 / 2) ω.1 θt * olgZetaInv L H' (f ω.2) := by
      nlinarith [h1, h2, hy₀]
    simp only [shocksIntegrand, olgPhi, shocksP8W', hle, ↓reduceIte]
  simp only [shocksOpT, shocksPhiF, e]

/-- **Proposition 8 under Assumption 17.5 alone: counterexample satisfying the book's
Assumption 17.1.** In the bimodal economy of `proposition_8_counterexample`, replace the CRRA
utility below a small `y₀ > 0` by `shocksP8W y₀` (so that `V'(0) < ∞`): `H` and `V` satisfy the
book's Assumption 17.1 (with `V` twice continuously differentiable on all of `ℝ₊`) and
Assumption 17.4, the strictly positive fixed point of `T` for the CRRA utility is still a fixed
point (all arguments of `φ` exceed `y₀`), and its price function `ρ(z) = z/ζ⁻¹(f(z))` is not
invertible. -/
theorem proposition_8_counterexample_book :
    ∃ y₀ : ℝ, 0 < y₀ ∧
      Assumption17_1 1 monoCexH monoCexH' monoCexH'' (shocksP8W y₀) (shocksP8W' y₀)
        (shocksP8W'' y₀) ∧ MonoAssumption17_4 (shocksP8W' y₀) (shocksP8W'' y₀) ∧
      ∃ f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) ∧
        (∀ z, f z = shocksOpT 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2)
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
          (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) ∧
        ¬ Function.Injective (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
          (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) := by
  have hH := monoCexH_assumption17_1H'
  obtain ⟨f, ⟨hfpos, hfix⟩, -⟩ := shocksP8_existsUnique_fixedPoint
  have hne : (univ : Set (Icc (1 / (3 / 2) : ℝ) (2 / 1))).Nonempty :=
    ⟨⟨_, left_mem_Icc.2 shocksP8_hZ⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne f.continuous.continuousOn
  have hy₀ : 0 < 2 / 3 * olgZetaInv 1 monoCexH' (f m) :=
    mul_pos (by norm_num) (hH.zetaInv_pos (hfpos m))
  have hη : ∀ z, 3 / 2 * (2 / 3 * olgZetaInv 1 monoCexH' (f m)) ≤
      olgZetaInv 1 monoCexH' (f z) := fun z => by
    rw [← mul_assoc, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, one_mul]
    exact hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hfpos m).le) (mem_Ici.2 (hfpos z).le)
      (isMinOn_iff.1 hm z (mem_univ z))
  exact ⟨_, hy₀, ⟨hH, (shocksP8W_assumptions hy₀).1⟩, (shocksP8W_assumptions hy₀).2, f, hfpos,
    fun z => by rw [shocksP8W_opT_eq hy₀ _ _ f hη z]; exact hfix z,
    (shocksP8_not_injective f hfpos hfix).1⟩

/-- **Correction (Proposition 8, p. 540, is false as stated).** Under the book's hypotheses
(Assumptions 17.1 and 17.4 for `H`, `V`; Assumption 17.5 for the shocks), a strictly positive
continuous solution of (3) (a fixed point of (4)) can have a price function `ρ(z) = z/η(z)` that is
not strictly increasing: `proposition_8_counterexample_book`. -/
theorem proposition_8_false :
    ¬ ∀ (xlo xhi θlo θhi : ℝ) (hZ : xlo / θhi ≤ xhi / θlo) (ψ g : ℝ → ℝ) (L : ℝ)
      (H H' H'' V V' V'' : ℝ → ℝ), ShocksAssumption17_5 xlo xhi θlo θhi ψ g →
      Assumption17_1 L H H' H'' V V' V'' → MonoAssumption17_4 V' V'' →
      ∀ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) →
      (∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z) →
      StrictMono fun z : Icc (xlo / θhi) (xhi / θlo) => (z : ℝ) / olgZetaInv L H' (f z) := by
  intro h
  obtain ⟨y₀, -, h1, h4, f, hfpos, hfix, hinj⟩ := proposition_8_counterexample_book
  exact hinj (h 1 2 1 (3 / 2) shocksP8_hZ _ _ 1 _ _ _ _ _ _ shocksExBimodal_assumption h1 h4 f
    hfpos hfix).injective

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: continuous equilibrium prices reveal exactly `x/θ`

SLP §17.6, pp. 532–533. The book argues that two states with the same price are
indistinguishable to the young, so (by strict concavity of (1)) they get the same labour supply,
and then (2) forces the same ratio `x/θ`; it concludes that "any equilibrium must be of the form
`p(x, θ) = ρ(x/θ)`". The argument proves only "equal prices ⇒ equal ratios"
(`p533_ratio_of_price`), and `p533_counterexample` (`FixedPointArguments.ShocksModel`) shows the
conclusion does not follow from those premises for a discontinuous `p`. Here the islands economy's
equilibrium conditions are formalised and the conclusion is proved for continuous prices, the
class in which the book looks for equilibria (`ρ` continuous on `Z`).

* `ShocksStates`: the state space `X × Θ`. `islandsObj`: the objective in (1), with the
  young agent's beliefs `κ(P)` about the current state given the price `P` and the law `ν` of next
  period's shocks. **`IslandsEqm`** (p. 532): conditions (1) (optimality given the price) and (2)
  (market clearing `n p = x/θ`); `IslandsEqm.p_pos`: equilibrium prices are positive.
* `islandsObj_max_unique` (p. 533, "(1) is strictly concave in `l`"): under Assumption 17.1 the
  maximiser in (1) is unique, so `n` is a function of `p`.
* `shocks_const_on_rays` (topology): a function continuous on `X × Θ` whose level sets lie in
  the rays `x/θ = z` is constant on each ray (intermediate value theorem on the convex ray
  segments `shocks_convex_ray`, and on nearby rays, `shocks_exists_ray_approx`).
* **`islands_eqm_price_of_ratio`** (p. 533, settled for continuous prices): every equilibrium with
  `p` continuous on `X × Θ` has `p(x, θ) = ρ(x/θ)`, `n(x, θ) = (x/θ)/ρ(x/θ)` with `ρ` continuous
  and strictly monotone (hence invertible) on `Z`. This holds for **every** price-indexed belief
  family `κ`, in particular for rational expectations. So no continuous price reveals more than
  `x/θ`, and every continuous equilibrium price reveals `x/θ` (the invertibility that the book
  imposes on `ρ` is automatic).
* `islands_eqm_not_injOn`: no continuous equilibrium price is fully revealing.

**Correction (p. 533), completed.** For continuous prices the book's conclusion is true but its
argument is incomplete: the missing step "equal ratios ⇒ equal prices" is the topological
`shocks_const_on_rays`, which uses continuity essentially (`p533_counterexample`). Whether a
*discontinuous* price revealing more than `x/θ` can satisfy (1) with rational-expectations beliefs
is not settled here.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology

variable {xlo xhi θlo θhi : ℝ}

/-- A point `u = (x, θ) ≠ (x̄, θ̲)` of the ray `x = zθ` in `X × Θ` is the limit, as `w ↓ z`, of
points of the rays `x = wθ` in `X × Θ`. -/
theorem shocks_exists_ray_approx (hθ0 : 0 < θlo) {z : ℝ} (hz : 0 < z) {u : ℝ × ℝ}
    (hu : u ∈ Icc xlo xhi ×ˢ Icc θlo θhi) (huz : u.1 = z * u.2) (hne : u ≠ (xhi, θlo)) :
    ∃ γ : ℝ → ℝ × ℝ, Tendsto γ (𝓝[>] z) (𝓝 u) ∧
      ∀ᶠ w in 𝓝[>] z, γ w ∈ Icc xlo xhi ×ˢ Icc θlo θhi ∧ (γ w).1 = w * (γ w).2 := by
  obtain ⟨⟨hx1, hx2⟩, hθ1, hθ2⟩ := hu
  have hev : ∀ᶠ w in 𝓝[>] z, z < w := self_mem_nhdsWithin
  rcases hx2.lt_or_eq with hlt | heq
  · -- move `x` up
    refine ⟨fun w => (u.1 * (w / z), u.2), ?_, ?_⟩
    · have : Tendsto (fun w => (u.1 * (w / z), u.2)) (𝓝 z) (𝓝 (u.1 * (z / z), u.2)) :=
        ((continuous_const.mul (continuous_id.div_const z)).prodMk continuous_const).tendsto z
      rw [div_self hz.ne', mul_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · have ht : Tendsto (fun w => u.1 * (w / z)) (𝓝[>] z) (𝓝 u.1) := by
        have : Tendsto (fun w => u.1 * (w / z)) (𝓝 z) (𝓝 (u.1 * (z / z))) :=
          ((continuous_const.mul (continuous_id.div_const z))).tendsto z
        rw [div_self hz.ne', mul_one] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      filter_upwards [hev, ht.eventually (gt_mem_nhds hlt)] with w hw h1
      have hx0 : 0 ≤ u.1 := by rw [huz]; exact mul_nonneg hz.le (by linarith)
      refine ⟨⟨⟨?_, h1.le⟩, hθ1, hθ2⟩, ?_⟩
      · have : 1 ≤ w / z := (one_le_div hz).2 hw.le
        nlinarith
      · rw [huz]
        field_simp
  · -- `x = x̄`: move `θ` down
    have hθlt : θlo < u.2 := by
      rcases hθ1.lt_or_eq with h | h
      · exact h
      · exact absurd (Prod.ext heq h.symm) hne
    have ht : Tendsto (fun w => u.2 * (z / w)) (𝓝[>] z) (𝓝 u.2) := by
      have : Tendsto (fun w => u.2 * (z / w)) (𝓝 z) (𝓝 (u.2 * (z / z))) :=
        (continuousAt_const.mul (continuousAt_const.div continuousAt_id hz.ne')).tendsto
      rw [div_self hz.ne', mul_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine ⟨fun w => (u.1, u.2 * (z / w)), tendsto_const_nhds.prodMk_nhds ht, ?_⟩
    filter_upwards [hev, ht.eventually (lt_mem_nhds hθlt)] with w hw h1
    have hw0 : 0 < w := hz.trans hw
    refine ⟨⟨⟨hx1, hx2⟩, h1.le, ?_⟩, ?_⟩
    · have : z / w ≤ 1 := (div_le_one hw0).2 hw.le
      have h0 : 0 ≤ u.2 := by linarith
      calc u.2 * (z / w) ≤ u.2 * 1 := mul_le_mul_of_nonneg_left this h0
        _ ≤ θhi := by linarith
    · rw [huz]
      field_simp

/-- The part of the ray `x = wθ` in `X × Θ` is convex. -/
theorem shocks_convex_ray (w : ℝ) :
    Convex ℝ {u ∈ Icc xlo xhi ×ˢ Icc θlo θhi | u.1 = w * u.2} := by
  rintro a ⟨haS, haz⟩ b ⟨hbS, hbz⟩ α β hα hβ hαβ
  refine ⟨(convex_Icc xlo xhi).prod (convex_Icc θlo θhi) haS hbS hα hβ hαβ, ?_⟩
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [haz, hbz]
  ring

/-- **Continuous prices are functions of `x/θ`.** If `p` is continuous on `X × Θ` and equal
prices imply equal ratios `x/θ` (what the argument on p. 533 proves, `p533_ratio_of_price`), then
`p` is constant on each ray `x/θ = z`. Otherwise `p` takes a value `m` strictly between two of its
values on one ray; by continuity it takes values on both sides of `m` on every nearby ray, hence
(intermediate value theorem on the convex ray segments) the value `m` itself, on two different
rays. -/
theorem shocks_const_on_rays (hx0 : 0 < xlo) (hθ0 : 0 < θlo) {p : ℝ × ℝ → ℝ}
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    (hsep : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ t ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = p t → s.1 / s.2 = t.1 / t.2)
    {s t : ℝ × ℝ} (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) (ht : t ∈ Icc xlo xhi ×ˢ Icc θlo θhi)
    (hst : s.1 / s.2 = t.1 / t.2) : p s = p t := by
  by_contra hne
  wlog h : p s < p t generalizing s t
  · exact this ht hs hst.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne))
  set S := Icc xlo xhi ×ˢ Icc θlo θhi with hSdef
  have hpos : ∀ u ∈ S, 0 < u.2 := fun u hu => hθ0.trans_le hu.2.1
  set z := s.1 / s.2 with hzdef
  have hz : 0 < z := div_pos (hx0.trans_le hs.1.1) (hpos s hs)
  have hsz : s.1 = z * s.2 := by rw [hzdef, div_mul_cancel₀ _ (hpos s hs).ne']
  have htz : t.1 = z * t.2 := by rw [hst, div_mul_cancel₀ _ (hpos t ht).ne']
  -- neither point is the corner `(x̄, θ̲)`, else the ray meets `X × Θ` only there
  have hcorner : ∀ u ∈ S, ∀ v ∈ S, u.1 = z * u.2 → v.1 = z * v.2 → u = (xhi, θlo) → v = u := by
    intro u hu v hv huz hvz hu0
    rw [hu0] at huz
    simp only at huz
    have h1 : xhi ≤ v.1 := by
      rw [hvz, huz]
      exact mul_le_mul_of_nonneg_left hv.2.1 hz.le
    have hv1 : v.1 = xhi := le_antisymm hv.1.2 h1
    have hv2 : v.2 = θlo := by
      have h2 : z * v.2 ≤ z * θlo := by rw [← hvz, ← huz]; exact hv.1.2
      exact le_antisymm (le_of_mul_le_mul_left h2 hz) hv.2.1
    rw [hu0]
    exact Prod.ext hv1 hv2
  have hs0 : s ≠ (xhi, θlo) := fun h0 => hne (by rw [hcorner s hs t ht hsz htz h0])
  have ht0 : t ≠ (xhi, θlo) := fun h0 => hne (by rw [hcorner t ht s hs htz hsz h0])
  -- the value `m` is taken on the ray `z`
  obtain ⟨m, hm⟩ : ∃ m, m = (p s + p t) / 2 := ⟨_, rfl⟩
  obtain ⟨u, ⟨huS, huz⟩, hum⟩ := (shocks_convex_ray (xlo := xlo) (xhi := xhi) (θlo := θlo)
    (θhi := θhi) z).isPreconnected.intermediate_value ⟨hs, hsz⟩ ⟨ht, htz⟩
    (hp.mono fun _ h => h.1) (show m ∈ Icc (p s) (p t) from ⟨by linarith, by linarith⟩)
  -- nearby rays
  obtain ⟨γs, hγs, hγsS⟩ := shocks_exists_ray_approx hθ0 hz hs hsz hs0
  obtain ⟨γt, hγt, hγtS⟩ := shocks_exists_ray_approx hθ0 hz ht htz ht0
  have hps : Tendsto (fun w => p (γs w)) (𝓝[>] z) (𝓝 (p s)) :=
    (hp s hs).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγs, hγsS.mono fun _ h => h.1⟩)
  have hpt : Tendsto (fun w => p (γt w)) (𝓝[>] z) (𝓝 (p t)) :=
    (hp t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγt, hγtS.mono fun _ h => h.1⟩)
  obtain ⟨w, hw, hγsw, hγtw, h1, h2⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[>] z, w ∈ Ioi z).and
    (hγsS.and (hγtS.and ((hps.eventually (gt_mem_nhds (show p s < m by linarith))).and
    (hpt.eventually (lt_mem_nhds (show m < p t by linarith))))))).exists
  obtain ⟨v, ⟨hvS, hvw⟩, hvm⟩ := (shocks_convex_ray (xlo := xlo) (xhi := xhi) (θlo := θlo)
    (θhi := θhi) w).isPreconnected.intermediate_value hγsw hγtw (hp.mono fun _ h => h.1)
    (show m ∈ Icc (p (γs w)) (p (γt w)) from ⟨h1.le, h2.le⟩)
  have := hsep v hvS u huS (by rw [hvm, hum])
  rw [hvw, huz, mul_div_cancel_right₀ _ (hpos v hvS).ne',
    mul_div_cancel_right₀ _ (hpos u huS).ne'] at this
  exact (ne_of_gt (mem_Ioi.1 hw)) this

/-! ### The islands economy: equilibrium conditions (1)–(2) -/

/-- The state space `X × Θ`, as a subtype of `ℝ × ℝ`. -/
abbrev ShocksStates (xlo xhi θlo θhi : ℝ) : Type := ↥(Icc xlo xhi ×ˢ Icc θlo θhi)

/-- The objective in (1) (p. 532) of a young agent who observes the price `P` and supplies `l`:
`−H(l) + E_{(x̂, θ̂) ~ κ(P)} E_{(x′, θ′) ~ ν} V[x′ l p(x̂, θ̂)/(x̂ p(x′, θ′))]`. Here `κ(P)` is the
agent's belief about the current state given the price `P` (in the book, the conditional law of
`(x, θ)` given `p(x, θ) = P`) and `ν` is the law of next period's shocks. -/
noncomputable def islandsObj {xlo xhi θlo θhi : ℝ} (H V : ℝ → ℝ) (p : ℝ × ℝ → ℝ)
    (κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi)) (ν : Measure (ShocksStates xlo xhi θlo θhi))
    (P l : ℝ) : ℝ :=
  -H l + ∫ sh, ∫ s', V (s'.1.1 * l * p sh.1 / (sh.1.1 * p s'.1)) ∂ν ∂κ P

variable (L : ℝ) (H V : ℝ → ℝ) (p n : ℝ × ℝ → ℝ) (κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi))
  (ν : Measure (ShocksStates xlo xhi θlo θhi)) in
/-- **Stationary equilibrium of the islands economy** (p. 532): a price function `p` and labour
supply `n` on `X × Θ` such that (1) at every state `n(x, θ) ∈ [0, L)` maximises the objective
`islandsObj` given the observed price `p(x, θ)`, and (2) `n(x, θ) p(x, θ) = x/θ`. The beliefs `κ`
are an arbitrary family indexed by the price (the agent sees only the price); the results below
hold for every such family, in particular for the rational-expectations one. -/
structure IslandsEqm : Prop where
  n_mem : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, n s ∈ Ico 0 L
  opt : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ l ∈ Ico 0 L,
    islandsObj H V p κ ν (p s) l ≤ islandsObj H V p κ ν (p s) (n s)
  clear : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, n s * p s = s.1 / s.2

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ} {p n : ℝ × ℝ → ℝ}
  {κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi)} {ν : Measure (ShocksStates xlo xhi θlo θhi)}

/-- In equilibrium prices are strictly positive (from (2), since `n ≥ 0` and `x/θ > 0`). -/
theorem IslandsEqm.p_pos (he : IslandsEqm L H V p n κ ν) (hx0 : 0 < xlo) (hθ0 : 0 < θlo)
    {s : ℝ × ℝ} (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) : 0 < p s := by
  have h2 := he.clear s hs
  have hz : 0 < s.1 / s.2 := div_pos (hx0.trans_le hs.1.1) (hθ0.trans_le hs.2.1)
  have hn := (he.n_mem s hs).1
  by_contra h
  push Not at h
  nlinarith

/-- **The maximiser in (1) is unique** (p. 533: "(1) is strictly concave in `l`"). Under
Assumption 17.1 (`H` strictly convex; `V` continuous and concave on `ℝ₊`), for continuous
positive `p` and finite measures `κ(P)`, `ν`, the objective `islandsObj` at the price `P` has at
most one maximiser on `[0, L)`. -/
theorem islandsObj_max_unique (hx0 : 0 < xlo) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    (hppos : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < p s) [IsFiniteMeasure ν]
    [∀ P, IsFiniteMeasure (κ P)] (P : ℝ) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ico 0 L) (hm₂ : m₂ ∈ Ico 0 L)
    (h₁ : ∀ l ∈ Ico 0 L, islandsObj H V p κ ν P l ≤ islandsObj H V p κ ν P m₁)
    (h₂ : ∀ l ∈ Ico 0 L, islandsObj H V p κ ν P l ≤ islandsObj H V p κ ν P m₂) : m₁ = m₂ := by
  have : CompactSpace (ShocksStates xlo xhi θlo θhi) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  by_contra hne
  set Ω := ShocksStates xlo xhi θlo θhi
  have hpc : Continuous fun s : Ω => p s.1 := hp.comp_continuous continuous_subtype_val
    fun s => s.2
  have hxpos : ∀ s : Ω, 0 < s.1.1 := fun s => hx0.trans_le s.2.1.1
  have hppos' : ∀ s : Ω, 0 < p s.1 := fun s => hppos s.1 s.2
  -- the integrand and its continuity
  set F : ℝ → Ω × Ω → ℝ := fun l q => V (q.2.1.1 * l * p q.1.1 / (q.1.1.1 * p q.2.1))
  have harg : ∀ l, Continuous fun q : Ω × Ω => q.2.1.1 * l * p q.1.1 / (q.1.1.1 * p q.2.1) :=
    fun l => (((continuous_subtype_val.fst.comp continuous_snd).mul continuous_const).mul
      (hpc.comp continuous_fst)).div ((continuous_subtype_val.fst.comp continuous_fst).mul
      (hpc.comp continuous_snd)) fun q => (mul_pos (hxpos q.1) (hppos' q.2)).ne'
  have hargnn : ∀ l, 0 ≤ l → ∀ q : Ω × Ω, 0 ≤ q.2.1.1 * l * p q.1.1 / (q.1.1.1 * p q.2.1) :=
    fun l hl q => div_nonneg (mul_nonneg (mul_nonneg (hxpos q.2).le hl) (hppos' q.1).le)
      (mul_pos (hxpos q.1) (hppos' q.2)).le
  have hF : ∀ l, 0 ≤ l → Continuous (F l) := fun l hl =>
    hV.V_cont.comp_continuous (harg l) fun q => mem_Ici.2 (hargnn l hl q)
  have hFi : ∀ l, 0 ≤ l → ∀ sh : Ω, Integrable (fun s' => F l (sh, s')) ν := fun l hl sh =>
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun s' => F l (sh, s'), (hF l hl).comp (continuous_const.prodMk continuous_id)⟩).integrable ν
  have hG : ∀ l, 0 ≤ l → Continuous fun sh : Ω => ∫ s', F l (sh, s') ∂ν := fun l hl => by
    have := continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun sh s' => F l (sh, s')) (hF l hl) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hGi : ∀ l, 0 ≤ l → Integrable (fun sh : Ω => ∫ s', F l (sh, s') ∂ν) (κ P) := fun l hl =>
    (BoundedContinuousFunction.mkOfCompact ⟨_, hG l hl⟩).integrable (κ P)
  -- midpoint concavity of the expected-utility term
  set m := (m₁ + m₂) / 2 with hmdef
  have hm : m ∈ Ico 0 L := ⟨by linarith [hm₁.1, hm₂.1], by linarith [hm₁.2, hm₂.2]⟩
  have hpt : ∀ q : Ω × Ω, (F m₁ q + F m₂ q) / 2 ≤ F m q := fun q => by
    have := hV.V_conc.concaveOn.2 (mem_Ici.2 (hargnn m₁ hm₁.1 q)) (mem_Ici.2 (hargnn m₂ hm₂.1 q))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hmid : q.2.1.1 * m * p q.1.1 / (q.1.1.1 * p q.2.1) =
        1 / 2 * (q.2.1.1 * m₁ * p q.1.1 / (q.1.1.1 * p q.2.1)) +
          1 / 2 * (q.2.1.1 * m₂ * p q.1.1 / (q.1.1.1 * p q.2.1)) := by rw [hmdef]; ring
    calc (F m₁ q + F m₂ q) / 2 = 1 / 2 * F m₁ q + 1 / 2 * F m₂ q := by ring
      _ ≤ F m q := by simp only [F]; rw [hmid]; exact this
  have hE : (∫ sh, ∫ s', F m₁ (sh, s') ∂ν ∂κ P + ∫ sh, ∫ s', F m₂ (sh, s') ∂ν ∂κ P) / 2 ≤
      ∫ sh, ∫ s', F m (sh, s') ∂ν ∂κ P := by
    rw [← integral_add (hGi m₁ hm₁.1) (hGi m₂ hm₂.1), ← integral_div]
    refine integral_mono (((hGi m₁ hm₁.1).add (hGi m₂ hm₂.1)).div_const 2) (hGi m hm.1)
      fun sh => ?_
    simp only
    rw [← integral_add (hFi m₁ hm₁.1 sh) (hFi m₂ hm₂.1 sh), ← integral_div]
    exact integral_mono (((hFi m₁ hm₁.1 sh).add (hFi m₂ hm₂.1 sh)).div_const 2) (hFi m hm.1 sh)
      fun s' => hpt (sh, s')
  -- strict convexity of `H`
  have hHc := hH.H_conv.2 hm₁ hm₂ hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hHc
  rw [show 1 / 2 * m₁ + 1 / 2 * m₂ = m by rw [hmdef]; ring] at hHc
  have e1 := h₁ m₂ hm₂
  have e2 := h₂ m₁ hm₁
  have e3 := h₁ m hm
  simp only [islandsObj] at e1 e2 e3
  change -H m₁ + ∫ sh, ∫ s', F m₁ (sh, s') ∂ν ∂κ P ≤ _ at e2
  linarith

/-- The end `(z a(z), a(z))`, `a(z) = max{x̲/z, θ̲}`, of the ray `x/θ = z` lies in `X × Θ` for
`z ∈ Z`. -/
theorem shocks_rayPoint_mem (hx0 : 0 < xlo) (hxx : xlo ≤ xhi) (hθ0 : 0 < θlo) (hθθ : θlo ≤ θhi)
    {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) :
    (z * shocksA xlo θlo z, shocksA xlo θlo z) ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
  have hθhi : 0 < θhi := hθ0.trans_le hθθ
  have hz0 : 0 < z := (div_pos hx0 hθhi).trans_le hz.1
  refine ⟨⟨?_, ?_⟩, le_max_right _ _, max_le ?_ hθθ⟩
  · rw [mul_shocksA hz0]; exact le_max_left _ _
  · rw [mul_shocksA hz0]
    refine max_le hxx ?_
    have := hz.2
    rwa [le_div_iff₀ hθ0] at this
  · rw [div_le_iff₀ hz0]
    have := hz.1
    rwa [div_le_iff₀ hθhi, mul_comm] at this

/-- The ratio `x/θ` of a state lies in `Z = [x̲/θ̄, x̄/θ̲]`. -/
theorem shocks_ratio_mem_Z (hx0 : 0 < xlo) (hθ0 : 0 < θlo) {s : ℝ × ℝ}
    (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) : s.1 / s.2 ∈ Icc (xlo / θhi) (xhi / θlo) :=
  ⟨div_le_div₀ (hx0.trans_le hs.1.1).le hs.1.1 (hθ0.trans_le hs.2.1) hs.2.2,
    div_le_div₀ (hx0.le.trans (hs.1.1.trans hs.1.2)) hs.1.2 hθ0 hs.2.1⟩

/-- **The p. 533 claim, for continuous prices.** Under Assumption 17.1 (`H` as in the book, `V`
continuous and concave on `ℝ₊`, as in the repaired Assumption 17.1), every stationary
equilibrium `(p, n)` of the islands economy (`IslandsEqm`, conditions (1)–(2)) with `p` continuous
on `X × Θ` has the form `p(x, θ) = ρ(x/θ)`, `n(x, θ) = (x/θ)/ρ(x/θ)` with `ρ` continuous and
strictly monotone on `Z`, whatever the price-indexed beliefs `κ`. So a continuous price never
reveals more than `x/θ`, and it always reveals `x/θ`.

Proof: the maximiser in (1) is unique (`islandsObj_max_unique`), so `n` is a function of `p`;
(2) then gives "equal prices ⇒ equal ratios" (`p533_ratio_of_price`); continuity upgrades this
to "equal ratios ⇒ equal prices" (`shocks_const_on_rays`). Continuity cannot be dropped from the
last step (`p533_counterexample`). -/
theorem islands_eqm_price_of_ratio (hx0 : 0 < xlo) (hxx : xlo ≤ xhi) (hθ0 : 0 < θlo)
    (hθθ : θlo ≤ θhi) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    [IsFiniteMeasure ν] [∀ P, IsFiniteMeasure (κ P)] (he : IslandsEqm L H V p n κ ν)
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi)) :
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Icc (xlo / θhi) (xhi / θlo)) ∧
      (StrictMonoOn ρ (Icc (xlo / θhi) (xhi / θlo)) ∨
        StrictAntiOn ρ (Icc (xlo / θhi) (xhi / θlo))) ∧
      ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, p s = ρ (s.1 / s.2) ∧ n s = s.1 / s.2 / ρ (s.1 / s.2) := by
  have hppos := fun s hs => he.p_pos hx0 hθ0 (s := s) hs
  -- `n` is a function of `p`
  have hn : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ t ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = p t → n s = n t := fun s hs t ht hst =>
    islandsObj_max_unique hx0 hH hV hp hppos (p s) (he.n_mem s hs) (he.n_mem t ht) (he.opt s hs)
      (by rw [hst]; exact he.opt t ht)
  have hsep : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ t ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = p t → s.1 / s.2 = t.1 / t.2 := fun s hs t ht hst => by
    rw [← he.clear s hs, ← he.clear t ht, hn s hs t ht hst, hst]
  have hconst := fun s hs t ht hst =>
    shocks_const_on_rays hx0 hθ0 hp hsep (s := s) (t := t) hs ht hst
  -- the ray point and its ratio
  have hA0 : ∀ z, 0 < shocksA xlo θlo z := fun z => hθ0.trans_le (le_max_right _ _)
  have hratio : ∀ z, (z * shocksA xlo θlo z) / shocksA xlo θlo z = z := fun z =>
    mul_div_cancel_right₀ _ (hA0 z).ne'
  have hA : ContinuousOn (shocksA xlo θlo) (Icc (xlo / θhi) (xhi / θlo)) := by
    have h1 : ContinuousOn (fun z : ℝ => xlo / z) (Icc (xlo / θhi) (xhi / θlo)) :=
      continuousOn_const.div continuousOn_id fun z hz =>
        ((div_pos hx0 (hθ0.trans_le hθθ)).trans_le hz.1).ne'
    exact h1.sup continuousOn_const
  refine ⟨fun z => p (z * shocksA xlo θlo z, shocksA xlo θlo z), ?_, ?_, fun s hs => ?_⟩
  · -- continuity
    exact hp.comp ((continuousOn_id.mul hA).prodMk hA) fun z hz =>
      shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz
  · -- injectivity, hence strict monotonicity
    refine ContinuousOn.strictMonoOn_of_injOn_Icc'
      (div_le_div₀ (hx0.le.trans hxx) hxx hθ0 hθθ) ?_ fun z hz w hw hzw => ?_
    · exact hp.comp ((continuousOn_id.mul hA).prodMk hA) fun z hz =>
        shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz
    · have := hsep _ (shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz) _
        (shocks_rayPoint_mem hx0 hxx hθ0 hθθ hw) hzw
      simpa only [hratio] using this
  · have hz := shocks_ratio_mem_Z hx0 hθ0 hs
    have hu := shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz
    have hps : p s = p (s.1 / s.2 * shocksA xlo θlo (s.1 / s.2), shocksA xlo θlo (s.1 / s.2)) :=
      hconst s hs _ hu (by simp only [hratio])
    refine ⟨hps, ?_⟩
    dsimp only
    rw [← hps, eq_div_iff (hppos s hs).ne']
    exact he.clear s hs

/-- **No continuous equilibrium price is fully revealing.** If `X` and `Θ` are nondegenerate, a
continuous equilibrium price cannot be injective on `X × Θ` (it is constant on rays
`x/θ = z`, which contain more than one state). -/
theorem islands_eqm_not_injOn (hx0 : 0 < xlo) (hxx : xlo < xhi) (hθ0 : 0 < θlo)
    (hθθ : θlo < θhi) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    [IsFiniteMeasure ν] [∀ P, IsFiniteMeasure (κ P)] (he : IslandsEqm L H V p n κ ν)
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi)) :
    ¬ InjOn p (Icc xlo xhi ×ˢ Icc θlo θhi) := by
  obtain ⟨ρ, -, -, hρ⟩ := islands_eqm_price_of_ratio hx0 hxx.le hθ0 hθθ.le hH hV he hp
  intro hinj
  set r := min (xhi / xlo) (θhi / θlo)
  have hr1 : 1 < r := lt_min ((one_lt_div hx0).2 hxx) ((one_lt_div hθ0).2 hθθ)
  have hs : ((xlo, θlo) : ℝ × ℝ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi :=
    ⟨⟨le_rfl, hxx.le⟩, le_rfl, hθθ.le⟩
  have ht : ((xlo * r, θlo * r) : ℝ × ℝ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
    refine ⟨⟨by nlinarith, ?_⟩, by nlinarith, ?_⟩
    · calc xlo * r ≤ xlo * (xhi / xlo) := mul_le_mul_of_nonneg_left (min_le_left _ _) hx0.le
        _ = xhi := by field_simp
    · calc θlo * r ≤ θlo * (θhi / θlo) := mul_le_mul_of_nonneg_left (min_le_right _ _) hθ0.le
        _ = θhi := by field_simp
  have heq : ((xlo, θlo) : ℝ × ℝ) = (xlo * r, θlo * r) := by
    refine hinj hs ht ?_
    rw [(hρ _ hs).1, (hρ _ ht).1]
    simp only
    rw [mul_div_mul_right _ _ (by linarith : r ≠ 0)]
  have := congrArg Prod.fst heq
  simp only at this
  nlinarith

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partially observed shocks: equilibria of the islands economy and fixed points of (4)

SLP §17.6, pp. 532–535. The equilibrium conditions (1)–(2) are `IslandsEqm`
(`FixedPointArguments.ShocksRevelation`). This module derives (3) from (1), proves the converse
(p. 535: a fixed point of (4) with invertible price function is an equilibrium), and turns the
failure of Proposition 8 (`FixedPointArguments.ShocksProposition8`) into a statement about
equilibria.

* `shocks_concave_tangent`, `shocks_convex_tangent`: tangent-line inequalities for `V` and `H`.
  `islands_factor_continuous`: the consumption factor `c = x′ p(ŝ)/(x̂ p(s′))` of (1).
* **(3) from (1)** (`islands_foc`, p. 534): in an equilibrium with continuous `p`, at every state
  `n H'(n) = E[φ(c n)]`, the expectation under the agent's beliefs and `ν`. The proof bounds the
  difference quotients of the expected utility by `E[c V'(c l)]` (concavity) and uses continuity
  of parametric integrals; no differentiation under the integral sign is needed.
* **Rational expectations.** `islandsShockLaw` (`x ~ ψ`, `θ ~ g` independent),
  `islandsNextLaw` (the true law `ν` of next period's state), `islandsREBeliefs` (at the price of
  the ray `x/θ = z` the state is `(zθ̂, θ̂)` with `θ̂ ~ G(·|z)`, `shocksCondLaw`);
  `islandsREBeliefs_eq`, `islandsShockLaw_ae_mem`, `condLaw_ae_ray`, `integral_islandsNextLaw`,
  `integral_rayBelief`, `isProbabilityMeasure_islandsShockLaw`, `islands_isFiniteMeasure_comap`,
  `isFiniteMeasure_islandsREBeliefs`.
* `islands_RE_phi_eq`: with these beliefs and `p = z/η(z)`, `η = ζ⁻¹ ∘ f`, the right side of the
  first-order condition at `η(z)` is `(Tf)(z)` of (4).
* **The converse (p. 535)** (`islands_eqm_of_fixedPoint`): a strictly positive continuous fixed
  point `f` of (4) with `z ↦ z/ζ⁻¹(f(z))` injective gives an equilibrium `p = ρ(x/θ)`,
  `n = ζ⁻¹(f(x/θ))` with rational-expectations beliefs (optimality by concavity and the
  first-order condition). As the book says, `π > 0` on `int Z` is needed (Exercise 17.8).
* **Equilibrium ⇒ fixed point** (`islands_fixedPoint_of_eqm`): every equilibrium with continuous
  `p` and rational-expectations beliefs comes from a strictly positive continuous fixed point of
  (4) with invertible price function. So, for continuous prices, equilibria and such fixed points
  correspond exactly.
* **Proposition 8 as a statement about equilibria.** `shocksP8_no_continuous_eqm`: the bimodal
  CRRA economy of `proposition_8_counterexample` has no equilibrium with a continuous price
  function. `shocksP8W'_ge`, `shocksP8W_eta_ge` (an a priori lower bound `η ≥ A/3` on fixed points
  for the utility `shocksP8W y₀`), `shocksP8W_no_continuous_eqm` and
  **`proposition_8_eqm_counterexample`**: the same economy with the utility
  `shocksP8W (1/300000)`, which satisfies the book's Assumptions 17.1 and 17.4, satisfies every
  hypothesis of Proposition 8 and has no equilibrium with a continuous price function at all.

**Correction (Proposition 8, p. 540).** Under Assumptions 17.1, 17.4 and 17.5 an islands economy
can fail to have any equilibrium with a continuous price function (with rational-expectations
beliefs); the unique positive solution of (3) has a non-invertible price function and so is not an
equilibrium. The regularity assumed is continuity of the price function, the class in which the
book looks for equilibria; discontinuous prices are not treated.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

variable {xlo xhi θlo θhi L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- The tangent line of a concave `V` at `y₀ > 0` lies above `V` on `ℝ₊`. -/
theorem shocks_concave_tangent (hV : Assumption17_1VR V V' V'') {y₀ y : ℝ} (hy₀ : 0 < y₀)
    (hy : 0 ≤ y) : V y ≤ V y₀ + V' y₀ * (y - y₀) := by
  have hc := hV.V_conc.concaveOn
  rcases lt_trichotomy y y₀ with h | h | h
  · have := hc.le_slope_of_hasDerivAt (mem_Ici.2 hy) (mem_Ici.2 hy₀.le) h (hV.V_deriv y₀ hy₀)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    nlinarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivAt (mem_Ici.2 hy₀.le) (mem_Ici.2 hy) h (hV.V_deriv y₀ hy₀)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    nlinarith

/-- The tangent line of the convex `H` at an interior `m` lies below `H` on `[0, L)`. -/
theorem shocks_convex_tangent (hH : Assumption17_1H L H H' H'') {m l : ℝ} (hm : m ∈ Ioo 0 L)
    (hl : l ∈ Ico 0 L) : H m + H' m * (l - m) ≤ H l := by
  have hc := hH.H_conv.convexOn
  have hm' : m ∈ Ico 0 L := Ioo_subset_Ico_self hm
  rcases lt_trichotomy l m with h | h | h
  · have := hc.slope_le_of_hasDerivAt hl hm' h (hH.H_hasDerivAt hm)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    nlinarith
  · subst h; simp
  · have := hc.le_slope_of_hasDerivAt hm' hl h (hH.H_hasDerivAt hm)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    nlinarith

variable {p n : ℝ × ℝ → ℝ} {κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi)}
  {ν : Measure (ShocksStates xlo xhi θlo θhi)}

/-- The consumption factor `c(ŝ, s′) = x′ p(ŝ)/(x̂ p(s′))` of (1) (consumption is `c l`) is
continuous and positive on `(X × Θ)²` for continuous positive `p`. -/
theorem islands_factor_continuous (hx0 : 0 < xlo)
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    (hppos : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < p s) :
    Continuous (fun q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi =>
        q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1)) ∧
      ∀ q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi,
        0 < q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1) := by
  have hpc : Continuous fun s : ShocksStates xlo xhi θlo θhi => p s.1 :=
    hp.comp_continuous continuous_subtype_val fun s => s.2
  have hxpos : ∀ s : ShocksStates xlo xhi θlo θhi, 0 < s.1.1 := fun s => hx0.trans_le s.2.1.1
  refine ⟨((continuous_subtype_val.fst.comp continuous_snd).mul (hpc.comp continuous_fst)).div
    ((continuous_subtype_val.fst.comp continuous_fst).mul (hpc.comp continuous_snd))
    fun q => (mul_pos (hxpos q.1) (hppos _ q.2.2)).ne', fun q => ?_⟩
  exact div_pos (mul_pos (hxpos q.2) (hppos _ q.1.2)) (mul_pos (hxpos q.1) (hppos _ q.2.2))

/-- **The first-order condition of (1)** (p. 534). In an equilibrium with continuous `p`, at
every state `s` the labour supply `n = n(s) ∈ (0, L)` satisfies
`n H'(n) = E[φ(c n)]`, `φ(y) = y V'(y)`, the expectation over `ŝ ~ κ(p(s))` and `s′ ~ ν`.
No differentiation under the integral sign is needed: concavity of `V` bounds the difference
quotients of the expected utility by `E[c V'(c l)]`, which is continuous in `l > 0`. -/
theorem islands_foc (hx0 : 0 < xlo) (hθ0 : 0 < θlo) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') [IsFiniteMeasure ν] [∀ P, IsFiniteMeasure (κ P)]
    (he : IslandsEqm L H V p n κ ν) (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    {s : ℝ × ℝ} (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) :
    olgZeta H' (n s) =
      ∫ sh, ∫ s', olgPhi V' (s'.1.1 * p sh.1 / (sh.1.1 * p s'.1) * n s) ∂ν ∂κ (p s) := by
  have : CompactSpace (ShocksStates xlo xhi θlo θhi) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hppos := fun s hs => he.p_pos hx0 hθ0 (s := s) hs
  obtain ⟨hc, hcpos⟩ := islands_factor_continuous hx0 hp hppos
  set c := fun q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi =>
    q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1) with hcdef
  set m := n s with hmdef
  have hm : m ∈ Ioo 0 L := by
    refine ⟨?_, (he.n_mem s hs).2⟩
    have h2 := he.clear s hs
    have hz : 0 < s.1 / s.2 := div_pos (hx0.trans_le hs.1.1) (hθ0.trans_le hs.2.1)
    by_contra h
    push Not at h
    nlinarith [hppos s hs]
  set μP := (κ (p s)).prod ν
  have hint : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
      Continuous F → Integrable F μP := fun F hF =>
    (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable μP
  have hprod : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
      Continuous F → ∫ q, F q ∂μP = ∫ sh, ∫ s', F (sh, s') ∂ν ∂κ (p s) := fun F hF =>
    integral_prod F (hint F hF)
  have hVc : ∀ l, 0 ≤ l → Continuous fun q => V (c q * l) := fun l hl =>
    hV.V_cont.comp_continuous (hc.mul continuous_const) fun q =>
      mem_Ici.2 (mul_nonneg (hcpos q).le hl)
  have hV'c : ∀ l, 0 < l → Continuous fun q => c q * V' (c q * l) := fun l hl =>
    hc.mul (hV.V'_continuousOn.comp_continuous (hc.mul continuous_const) fun q =>
      mem_Ioi.2 (mul_pos (hcpos q) hl))
  -- the objective in product form
  have hobj : ∀ l, 0 ≤ l → islandsObj H V p κ ν (p s) l = -H l + ∫ q, V (c q * l) ∂μP :=
    fun l hl => by
      rw [hprod _ (hVc l hl), islandsObj]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun sh => integral_congr_ae (ae_of_all _
        fun s' => ?_))
      simp only [hcdef]
      ring_nf
  set D := fun l => ∫ q, c q * V' (c q * l) ∂μP with hDdef
  -- the difference-quotient bound
  have hkey : ∀ l ∈ Ioo 0 L, (l - m) * D l ≤ H l - H m := fun l hl => by
    have hopt := he.opt s hs l (Ioo_subset_Ico_self hl)
    rw [hobj l hl.1.le, hobj m hm.1.le] at hopt
    have hpt : ∀ q, V (c q * m) ≤ V (c q * l) - (l - m) * (c q * V' (c q * l)) := fun q => by
      have := shocks_concave_tangent hV (mul_pos (hcpos q) hl.1)
        (mul_nonneg (hcpos q).le hm.1.le)
      nlinarith
    have hmono : ∫ q, V (c q * m) ∂μP ≤
        ∫ q, (V (c q * l) - (l - m) * (c q * V' (c q * l))) ∂μP :=
      integral_mono (hint _ (hVc m hm.1.le))
        ((hint _ (hVc l hl.1.le)).sub ((hint _ (hV'c l hl.1)).const_mul (l - m))) hpt
    rw [integral_sub (hint _ (hVc l hl.1.le)) ((hint _ (hV'c l hl.1)).const_mul (l - m)),
      integral_const_mul] at hmono
    simp only [hDdef]
    linarith
  -- continuity of `D` at `m`
  set Dδ := fun l => ∫ q, c q * V' (c q * max l (m / 2)) ∂μP with hDδdef
  have hDδc : Continuous Dδ := by
    have hF : Continuous (Function.uncurry fun (l : ℝ)
        (q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi) =>
          c q * V' (c q * max l (m / 2))) :=
      (hc.comp continuous_snd).mul (hV.V'_continuousOn.comp_continuous
        ((hc.comp continuous_snd).mul (continuous_fst.max continuous_const)) fun x =>
          mem_Ioi.2 (mul_pos (hcpos x.2) (lt_max_of_lt_right (by linarith [hm.1]))))
    have := continuous_parametric_integral_of_continuous (μ := μP) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hDδ : ∀ l, m / 2 ≤ l → Dδ l = D l := fun l hl => by
    simp only [hDδdef, hDdef, max_eq_left hl]
  have hslope := hasDerivAt_iff_tendsto_slope.1 (hH.H_hasDerivAt hm)
  have hup : Dδ m ≤ H' m := by
    refine le_of_tendsto_of_tendsto (hDδc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hslope.mono_left (nhdsWithin_mono _ fun x hx => (mem_Ioi.1 hx).ne')) ?_
    filter_upwards [Ioo_mem_nhdsGT hm.2] with l hl
    rw [hDδ l (by linarith [hl.1, hm.1]), slope_def_field, le_div_iff₀ (sub_pos.2 hl.1)]
    have := hkey l ⟨hm.1.trans hl.1, hl.2⟩
    linarith
  have hlo : H' m ≤ Dδ m := by
    refine le_of_tendsto_of_tendsto
      (hslope.mono_left (nhdsWithin_mono _ fun x hx => (mem_Iio.1 hx).ne))
      (hDδc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsLT (show m / 2 < m by linarith [hm.1])] with l hl
    rw [hDδ l hl.1.le, slope_def_field, div_le_iff_of_neg (sub_neg.2 hl.2)]
    have := hkey l ⟨by linarith [hl.1, hm.1], hl.2.trans hm.2⟩
    linarith
  have hD : D m = H' m := by
    rw [← hDδ m (by linarith [hm.1])]
    exact le_antisymm hup hlo
  -- conclusion
  have hφc : Continuous fun q => olgPhi V' (c q * m) :=
    hV.phi_continuousOn.comp_continuous (hc.mul continuous_const) fun q =>
      mem_Ioi.2 (mul_pos (hcpos q) hm.1)
  rw [← hprod _ hφc]
  have e : ∀ q, olgPhi V' (c q * m) = m * (c q * V' (c q * m)) := fun q => by
    simp only [olgPhi]; ring
  simp_rw [e]
  rw [integral_const_mul]
  change m * H' m = m * D m
  rw [hD]

/-! ### Rational-expectations beliefs and the true law of next period's shocks -/

/-- The law of the shocks `(x, θ)`: `x ~ ψ` and `θ ~ g` independent. -/
noncomputable def islandsShockLaw (ψ g : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (volume.withDensity fun x => ENNReal.ofReal (ψ x)).prod
    (volume.withDensity fun θ => ENNReal.ofReal (g θ))

/-- The true law `ν` of next period's state `(x′, θ′)`, as a measure on `X × Θ`. -/
noncomputable def islandsNextLaw (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) :
    Measure (ShocksStates xlo xhi θlo θhi) :=
  (islandsShockLaw ψ g).comap Subtype.val

open scoped Classical in
/-- **Rational-expectations beliefs** for a price function `p` that depends on the state through
`z = x/θ`: a young agent who sees the price `P = p(z a(z), a(z))` believes the current state is
`(z θ̂, θ̂)` with `θ̂ ~ G(·|z)`, the conditional law of `θ` given `x/θ = z` (`shocksCondLaw`). (At
prices that never occur the belief is the zero measure; it is never used.) -/
noncomputable def islandsREBeliefs (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) (p : ℝ × ℝ → ℝ)
    (P : ℝ) : Measure (ShocksStates xlo xhi θlo θhi) :=
  if h : ∃ z ∈ Icc (xlo / θhi) (xhi / θlo), p (z * shocksA xlo θlo z, shocksA xlo θlo z) = P then
    (Measure.map (fun θ => (h.choose * θ, θ))
      (shocksCondLaw xlo xhi θlo θhi ψ g h.choose)).comap Subtype.val
  else 0

variable {ψ g : ℝ → ℝ}

/-- When `z ↦ p(z a(z), a(z))` is injective on `Z`, the belief at the price of the ray `z` is
the conditional law along that ray. -/
theorem islandsREBeliefs_eq {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo))
    (hinj : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = p (z * shocksA xlo θlo z, shocksA xlo θlo z) →
      w = z) :
    islandsREBeliefs xlo xhi θlo θhi ψ g p (p (z * shocksA xlo θlo z, shocksA xlo θlo z)) =
      (Measure.map (fun θ => (z * θ, θ))
        (shocksCondLaw xlo xhi θlo θhi ψ g z)).comap Subtype.val := by
  have h : ∃ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = p (z * shocksA xlo θlo z, shocksA xlo θlo z) :=
    ⟨z, hz, rfl⟩
  have hc : h.choose = z := hinj _ h.choose_spec.1 h.choose_spec.2
  simp only [islandsREBeliefs, h, ↓reduceDIte, hc]

variable (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
include hA

/-- The shocks lie in `X × Θ` almost surely. -/
theorem islandsShockLaw_ae_mem : ∀ᵐ q ∂islandsShockLaw ψ g, q ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
  have hx : ∀ᵐ x ∂(volume.withDensity fun x => ENNReal.ofReal (ψ x)), x ∈ Icc xlo xhi := by
    refine (ae_withDensity_iff (f := fun x => ENNReal.ofReal (ψ x))
      (ENNReal.measurable_ofReal.comp hA.ψ_meas)).2 (ae_of_all _ fun x hx => ?_)
    by_contra h
    exact hx (by rw [hA.ψ_zero x h, ENNReal.ofReal_zero])
  have hθ : ∀ᵐ θ ∂(volume.withDensity fun θ => ENNReal.ofReal (g θ)), θ ∈ Icc θlo θhi := by
    refine (ae_withDensity_iff (f := fun θ => ENNReal.ofReal (g θ))
      (ENNReal.measurable_ofReal.comp hA.g_meas)).2 (ae_of_all _ fun θ hθ => ?_)
    by_contra h
    exact hθ (by rw [hA.g_zero θ h, ENNReal.ofReal_zero])
  exact ((Measure.quasiMeasurePreserving_fst.ae hx).and
    (Measure.quasiMeasurePreserving_snd.ae hθ)).mono fun q hq => ⟨hq.1, hq.2⟩

/-- Integrals against the true law of next period's state. -/
theorem integral_islandsNextLaw (k : ℝ × ℝ → ℝ) :
    ∫ s' : ShocksStates xlo xhi θlo θhi, k s'.1 ∂islandsNextLaw xlo xhi θlo θhi ψ g =
      ∫ q, k q ∂islandsShockLaw ψ g := by
  rw [islandsNextLaw, integral_subtype_comap (measurableSet_Icc.prod measurableSet_Icc),
    Measure.restrict_eq_self_of_ae_mem (islandsShockLaw_ae_mem hA)]

/-- `G(·|z)` lives on the ray: `(zθ, θ) ∈ X × Θ` for `G(·|z)`-a.e. `θ`, `z ∈ Z`. -/
theorem condLaw_ae_ray (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z) {z : ℝ}
    (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) :
    ∀ᵐ θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z, (z * θ, θ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
  have hθhi : 0 < θhi := hA.θlo_pos.trans hA.θlo_lt
  have hz0 : 0 < z := (div_pos hA.xlo_pos hθhi).trans_le hz.1
  have hmeas : MeasurableSet {θ : ℝ | (z * θ, θ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi} :=
    (measurableSet_Icc.prod measurableSet_Icc).preimage
      ((measurable_const.mul measurable_id).prodMk measurable_id)
  by_cases hint : xlo / θhi < z ∧ z < xhi / θlo
  · simp only [shocksCondLaw, hint, and_self, ↓reduceIte]
    rw [ae_withDensity_iff (hA.measurable_condDens z).ennreal_ofReal]
    refine ae_of_all _ fun θ hθ => ?_
    have hmem : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z) := by
      by_contra h
      exact hθ (by rw [(hA.ex_17_8a (hπ z hint)).2.2.1 θ h, ENNReal.ofReal_zero])
    have := (mem_Icc_shocksA_shocksB_iff hz0).2 hmem
    exact ⟨this.2, this.1⟩
  · simp only [shocksCondLaw, hint, ↓reduceIte]
    split_ifs with h1
    · rw [ae_dirac_iff hmeas]
      have : z = xlo / θhi := le_antisymm h1 hz.1
      have e : z * θhi = xlo := by rw [this, div_mul_cancel₀ _ hθhi.ne']
      exact ⟨⟨e.symm.le, e.le.trans hA.xlo_lt.le⟩, hA.θlo_lt.le, le_rfl⟩
    · rw [ae_dirac_iff hmeas]
      have hz2 : z = xhi / θlo := by
        by_contra h2
        exact hint ⟨lt_of_not_ge h1, lt_of_le_of_ne hz.2 h2⟩
      have e : z * θlo = xhi := by rw [hz2, div_mul_cancel₀ _ hA.θlo_pos.ne']
      exact ⟨⟨hA.xlo_lt.le.trans e.symm.le, e.le⟩, le_rfl, hA.θlo_lt.le⟩

/-- Integrals against the rational-expectations belief along the ray `z`. -/
theorem integral_rayBelief (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) (k : ℝ × ℝ → ℝ) :
    ∫ sh : ShocksStates xlo xhi θlo θhi, k sh.1 ∂(Measure.map (fun θ => (z * θ, θ))
      (shocksCondLaw xlo xhi θlo θhi ψ g z)).comap Subtype.val =
      ∫ θ, k (z * θ, θ) ∂shocksCondLaw xlo xhi θlo θhi ψ g z := by
  have hS : MeasurableSet (Icc xlo xhi ×ˢ Icc θlo θhi) := measurableSet_Icc.prod measurableSet_Icc
  have hm : Measurable fun θ : ℝ => (z * θ, θ) := (measurable_const.mul measurable_id).prodMk
    measurable_id
  have hemb : MeasurableEmbedding fun θ : ℝ => (z * θ, θ) := by
    refine MeasurableEmbedding.of_measurable_inverse hm ?_ measurable_snd fun θ => rfl
    have : range (fun θ : ℝ => (z * θ, θ)) = {q : ℝ × ℝ | q.1 = z * q.2} := by
      ext q
      constructor
      · rintro ⟨θ, rfl⟩; rfl
      · intro h; exact ⟨q.2, Prod.ext h.symm rfl⟩
    rw [this]
    exact measurableSet_eq_fun measurable_fst (measurable_const.mul measurable_snd)
  have hae : ∀ᵐ q ∂(Measure.map (fun θ => (z * θ, θ)) (shocksCondLaw xlo xhi θlo θhi ψ g z)),
      q ∈ Icc xlo xhi ×ˢ Icc θlo θhi :=
    (ae_map_iff hm.aemeasurable hS).2 (condLaw_ae_ray hA hπ hz)
  rw [integral_subtype_comap hS, Measure.restrict_eq_self_of_ae_mem hae, hemb.integral_map]

/-- **The bridge to (4).** Let `p(x, θ) = z/η(z)`, `z = x/θ`, with `η = ζ⁻¹ ∘ f` for a continuous
positive `f` on `Z`. Under the true law `ν` of next period's state and the rational-expectations
belief along the ray `z`, the right side of the first-order condition at labour `η(z)` is
`(Tf)(z)` of (4): `E[φ(c η(z))] = ∫∫ φ((θ′/θ̂) η(z′)) dμ(θ′, z′) G(dθ̂|z)`, since
`c η(z) = (θ′/θ̂) η(z′)` on the ray. -/
theorem islands_RE_phi_eq (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (hZ : xlo / θhi ≤ xhi / θlo) (f : Icc (xlo / θhi) (xhi / θlo) → ℝ) (hfc : Continuous f)
    (hfpos : ∀ z, 0 < f z)
    (hp : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))))
    (z : Icc (xlo / θhi) (xhi / θlo)) :
    ∫ sh, ∫ s', olgPhi V' (s'.1.1 * p sh.1 / (sh.1.1 * p s'.1) * olgZetaInv L H' (f z))
      ∂islandsNextLaw xlo xhi θlo θhi ψ g
      ∂((Measure.map (fun θ => (z.1 * θ, θ)) (shocksCondLaw xlo xhi θlo θhi ψ g z.1)).comap
        Subtype.val : Measure (ShocksStates xlo xhi θlo θhi)) =
      shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z := by
  have hθ0 := hA.θlo_pos
  have hθ := hA.θlo_lt.le
  have hx0 := hA.xlo_pos
  have hη : ∀ w, 0 < olgZetaInv L H' (f w) := fun w => hH.zetaInv_pos (hfpos w)
  have h1 := integral_rayBelief hA hπ z.2 (fun qh => ∫ s', olgPhi V'
    (s'.1.1 * p qh / (qh.1 * p s'.1) * olgZetaInv L H' (f z)) ∂islandsNextLaw xlo xhi θlo θhi ψ g)
  simp only at h1
  rw [h1, shocksOpT]
  refine integral_congr_ae ((condLaw_ae_ray hA hπ z.2).mono fun θ hθS => ?_)
  have hθpos : 0 < θ := hθ0.trans_le hθS.2.1
  have h2 := integral_islandsNextLaw hA (fun q => olgPhi V'
    (q.1 * p (z.1 * θ, θ) / ((z.1 * θ, θ).1 * p q) * olgZetaInv L H' (f z)))
  simp only at h2
  beta_reduce
  rw [h2, shocksPhiF, shocksJointLaw]
  have hmap : Measurable fun q : ℝ × ℝ => (q.2, projIcc (xlo / θhi) (xhi / θlo) hZ (q.1 / q.2)) :=
    measurable_snd.prodMk (continuous_projIcc.measurable.comp (measurable_fst.div measurable_snd))
  have hcont : Continuous fun ω : ℝ × Icc (xlo / θhi) (xhi / θlo) =>
      shocksIntegrand L H' V' θlo θhi f θ ω := by
    have e1 : Continuous fun ω : ℝ × Icc (xlo / θhi) (xhi / θlo) => shocksRatio θlo θhi ω.1 θ :=
      (continuous_shocksRatio hθ0).comp (continuous_fst.prodMk continuous_const)
    have e2 : Continuous fun ω : ℝ × Icc (xlo / θhi) (xhi / θlo) => olgZetaInv L H' (f ω.2) :=
      hH.zetaInv_continuousOn.comp_continuous (hfc.comp continuous_snd) fun ω =>
        mem_Ici.2 (hfpos _).le
    refine hV.phi_continuousOn.comp_continuous (e1.mul e2) fun ω => ?_
    exact mul_pos ((div_pos hθ0 (hθ0.trans_le hθ)).trans_le
      (shocksRatio_mem hθ0 hθ ω.1 θ).1) (hη _)
  rw [integral_map hmap.aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae ((islandsShockLaw_ae_mem hA).mono fun q hq => ?_)
  have hq2 : 0 < q.2 := hθ0.trans_le hq.2.1
  have hq1 : 0 < q.1 := hx0.trans_le hq.1.1
  have hz0 : 0 < z.1 := (div_pos hx0 (hθ0.trans_le hθ)).trans_le z.2.1
  simp only [shocksIntegrand, shocksRatio, shocksClamp_of_mem hq.2, shocksClamp_of_mem hθS.2]
  congr 1
  rw [hp _ hθS, hp q hq]
  simp only
  rw [mul_div_cancel_right₀ _ hθpos.ne', projIcc_val]
  have := hη z
  have := hη (projIcc (xlo / θhi) (xhi / θlo) hZ (q.1 / q.2))
  field_simp

/-- The law of the shocks is a probability measure. -/
theorem isProbabilityMeasure_islandsShockLaw : IsProbabilityMeasure (islandsShockLaw ψ g) := by
  have h1 := shocks_isProbabilityMeasure_withDensity hA.ψ_nonneg
    (shocks_integrable_of_zero_off hA.ψ_cont hA.ψ_zero) hA.ψ_int
  have h2 := shocks_isProbabilityMeasure_withDensity hA.g_nonneg
    (shocks_integrable_of_zero_off hA.g_cont hA.g_zero) hA.g_int
  rw [islandsShockLaw]
  infer_instance

omit hA in
/-- The restriction of a finite measure on `ℝ × ℝ` to `X × Θ` is finite. -/
theorem islands_isFiniteMeasure_comap (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap Subtype.val : Measure (ShocksStates xlo xhi θlo θhi)) := by
  constructor
  rw [Measure.comap_apply _ Subtype.val_injective
    (fun _ hs => (measurableSet_Icc.prod measurableSet_Icc).subtype_image hs) _
    MeasurableSet.univ]
  exact measure_lt_top _ _

/-- **The converse (p. 535).** Let `f` be a strictly positive continuous fixed point of (4)
(with `μ` the joint law and `G(·|z)` the conditional law) whose price function
`ρ(z) = z/ζ⁻¹(f(z))` is injective on `Z`. Then `p(x, θ) = ρ(x/θ)` and `n(x, θ) = ζ⁻¹(f(x/θ))`
form an equilibrium (`IslandsEqm`) of the islands economy with rational-expectations beliefs and
the true law of next period's shocks. Optimality in (1) follows from the fixed-point equation
(which is the first-order condition, `islands_RE_phi_eq`) and concavity of the objective. -/
theorem islands_eqm_of_fixedPoint (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (hZ : xlo / θhi ≤ xhi / θlo) (f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
      (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z)
    (hinj : InjOn (fun z => z / olgZetaInv L H' (f (projIcc _ _ hZ z)))
      (Icc (xlo / θhi) (xhi / θlo)))
    (hp : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))))
    (hn : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      n s = olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2)))) :
    IslandsEqm L H V p n (islandsREBeliefs xlo xhi θlo θhi ψ g p)
      (islandsNextLaw xlo xhi θlo θhi ψ g) := by
  have : CompactSpace (ShocksStates xlo xhi θlo θhi) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hθ0 := hA.θlo_pos
  have hx0 := hA.xlo_pos
  have hθθ := hA.θlo_lt.le
  have hxx := hA.xlo_lt.le
  set η := fun z : ℝ => olgZetaInv L H' (f (projIcc _ _ hZ z)) with hηdef
  have hηmem : ∀ z, η z ∈ Ioo 0 L := fun z =>
    ⟨hH.zetaInv_pos (hfpos _), (hH.zetaInv_mem (hfpos _).le).2⟩
  have hηc : Continuous η := hH.zetaInv_continuousOn.comp_continuous
    (f.continuous.comp continuous_projIcc) fun z => mem_Ici.2 (hfpos _).le
  have hpos2 : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < s.2 := fun s hs => hθ0.trans_le hs.2.1
  have hppos : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < p s := fun s hs => by
    rw [hp s hs]
    exact div_pos (div_pos (hx0.trans_le hs.1.1) (hpos2 s hs)) (hηmem _).1
  have hpc : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi) := by
    have hr : ContinuousOn (fun s : ℝ × ℝ => s.1 / s.2) (Icc xlo xhi ×ˢ Icc θlo θhi) :=
      continuous_fst.continuousOn.div continuous_snd.continuousOn fun s hs => (hpos2 s hs).ne'
    refine (hr.div (hηc.comp_continuousOn hr) fun s _ => (hηmem _).1.ne').congr fun s hs => ?_
    exact hp s hs
  have := isProbabilityMeasure_islandsShockLaw hA
  have hν : IsFiniteMeasure (islandsNextLaw xlo xhi θlo θhi ψ g) :=
    islands_isFiniteMeasure_comap _
  -- the price of a ray
  have hray : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = w / η w := fun w hw => by
    have hA0 : shocksA xlo θlo w ≠ 0 := (hθ0.trans_le (le_max_right _ _)).ne'
    rw [hp _ (shocks_rayPoint_mem hx0 hxx hθ0 hθθ hw)]
    simp only
    rw [mul_div_cancel_right₀ _ hA0]
  refine ⟨fun s hs => by rw [hn s hs]; exact Ioo_subset_Ico_self (hηmem _),
    fun s hs l hl => ?_, fun s hs => ?_⟩
  · -- (1)
    set z₀ := s.1 / s.2 with hz₀def
    have hz₀ := shocks_ratio_mem_Z hx0 hθ0 hs
    have hps : p s = p (z₀ * shocksA xlo θlo z₀, shocksA xlo θlo z₀) := by
      rw [hray z₀ hz₀, hp s hs]
    have hbel := islandsREBeliefs_eq (p := p) (ψ := ψ) (g := g) hz₀ fun w hw hpw => by
      rw [hray w hw, hray z₀ hz₀] at hpw
      exact hinj hw hz₀ hpw
    rw [hps]
    simp only [islandsObj]
    rw [hbel, hn s hs]
    set κ₀ : Measure (ShocksStates xlo xhi θlo θhi) := (Measure.map (fun θ => (z₀ * θ, θ))
      (shocksCondLaw xlo xhi θlo θhi ψ g z₀)).comap Subtype.val with hκ₀
    have := hA.isProbabilityMeasure_condLaw' hπ z₀
    have hκfin : IsFiniteMeasure κ₀ := islands_isFiniteMeasure_comap _
    obtain ⟨hc, hcpos⟩ := islands_factor_continuous hx0 hpc hppos
    set c := fun q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi =>
      q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1) with hcdef
    set μP := κ₀.prod (islandsNextLaw xlo xhi θlo θhi ψ g)
    have hint : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
        Continuous F → Integrable F μP := fun F hF =>
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable μP
    have hprod : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
        Continuous F → ∫ q, F q ∂μP =
          ∫ sh, ∫ s', F (sh, s') ∂islandsNextLaw xlo xhi θlo θhi ψ g ∂κ₀ := fun F hF =>
      integral_prod F (hint F hF)
    have hVc : ∀ l, 0 ≤ l → Continuous fun q => V (c q * l) := fun l hl =>
      hV.V_cont.comp_continuous (hc.mul continuous_const) fun q =>
        mem_Ici.2 (mul_nonneg (hcpos q).le hl)
    have hobj : ∀ l, 0 ≤ l → ∫ sh, ∫ s', V (s'.1.1 * l * p sh.1 / (sh.1.1 * p s'.1))
        ∂islandsNextLaw xlo xhi θlo θhi ψ g ∂κ₀ = ∫ q, V (c q * l) ∂μP := fun l hl => by
      rw [hprod _ (hVc l hl)]
      refine integral_congr_ae (ae_of_all _ fun sh => integral_congr_ae (ae_of_all _
        fun s' => ?_))
      simp only [hcdef]
      ring_nf
    set zs := projIcc _ _ hZ z₀ with hzsdef
    set η₀ := olgZetaInv L H' (f zs) with hη₀def
    have hη₀ : η₀ ∈ Ioo 0 L := hηmem z₀
    rw [hobj l hl.1, hobj η₀ hη₀.1.le]
    -- the first-order condition holds at `η₀`
    have hφc : Continuous fun q => olgPhi V' (c q * η₀) :=
      hV.phi_continuousOn.comp_continuous (hc.mul continuous_const) fun q =>
        mem_Ioi.2 (mul_pos (hcpos q) hη₀.1)
    have hzs : (zs : ℝ) = z₀ := by rw [hzsdef, projIcc_of_mem _ hz₀]
    have hb := islands_RE_phi_eq hA hπ hH hV hZ f f.continuous hfpos hp zs
    rw [hzs] at hb
    have hφ : ∫ q, olgPhi V' (c q * η₀) ∂μP = f zs :=
      calc ∫ q, olgPhi V' (c q * η₀) ∂μP = shocksOpT L H' V' θlo θhi
            (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
            (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f zs := by
            rw [hprod _ hφc]; exact hb
        _ = f zs := (hfix zs).symm
    have hζ : f zs = η₀ * H' η₀ := (hH.zeta_zetaInv (hfpos zs).le).symm
    -- concavity
    have hpt : ∀ q, V (c q * l) ≤ V (c q * η₀) + (l - η₀) / η₀ * olgPhi V' (c q * η₀) :=
      fun q => by
        have h := shocks_concave_tangent hV (mul_pos (hcpos q) hη₀.1)
          (mul_nonneg (hcpos q).le hl.1)
        have e : (l - η₀) / η₀ * olgPhi V' (c q * η₀) = V' (c q * η₀) * (c q * l - c q * η₀) := by
          simp only [olgPhi]
          field_simp [hη₀.1.ne']
        rw [e]
        exact h
    have hmono : ∫ q, V (c q * l) ∂μP ≤
        ∫ q, (V (c q * η₀) + (l - η₀) / η₀ * olgPhi V' (c q * η₀)) ∂μP :=
      integral_mono (hint _ (hVc l hl.1)) ((hint _ (hVc η₀ hη₀.1.le)).add
        ((hint _ hφc).const_mul _)) hpt
    rw [integral_add (hint _ (hVc η₀ hη₀.1.le)) ((hint _ hφc).const_mul _),
      integral_const_mul, hφ, hζ] at hmono
    have e2 : (l - η₀) / η₀ * (η₀ * H' η₀) = H' η₀ * (l - η₀) := by
      field_simp [hη₀.1.ne']
    have htan := shocks_convex_tangent hH hη₀ hl
    linarith
  · -- (2)
    rw [hn s hs, hp s hs, mul_div_cancel₀ _ (hηmem _).1.ne']

/-- Rational-expectations beliefs are finite measures. -/
theorem isFiniteMeasure_islandsREBeliefs
    (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z) (p : ℝ × ℝ → ℝ) (P : ℝ) :
    IsFiniteMeasure (islandsREBeliefs xlo xhi θlo θhi ψ g p P) := by
  rw [islandsREBeliefs]
  split_ifs with h
  · have := hA.isProbabilityMeasure_condLaw' hπ h.choose
    exact islands_isFiniteMeasure_comap _
  · infer_instance

/-- **Equilibrium ⇒ fixed point of (4)** (p. 535, the direction the book uses implicitly). Every
equilibrium of the islands economy with a continuous price function, rational-expectations
beliefs and the true law of next period's shocks comes from a strictly positive continuous fixed
point `f = ζ(η)` of (4) whose price function `z/ζ⁻¹(f(z))` is invertible:
`p(x, θ) = (x/θ)/ζ⁻¹(f(x/θ))`. (By `islands_eqm_price_of_ratio`, `p = ρ(x/θ)` with `ρ`
continuous and strictly monotone; the first-order condition `islands_foc` along each ray is
`f = Tf` by `islands_RE_phi_eq`.) -/
theorem islands_fixedPoint_of_eqm (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (hZ : xlo / θhi ≤ xhi / θlo)
    (he : IslandsEqm L H V p n (islandsREBeliefs xlo xhi θlo θhi ψ g p)
      (islandsNextLaw xlo xhi θlo θhi ψ g))
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi)) :
    ∃ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) ∧
      (∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z) ∧
      Function.Injective (fun z : Icc (xlo / θhi) (xhi / θlo) =>
        (z : ℝ) / olgZetaInv L H' (f z)) ∧
      ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
        p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))) := by
  have hθ0 := hA.θlo_pos
  have hx0 := hA.xlo_pos
  have hθθ := hA.θlo_lt.le
  have hxx := hA.xlo_lt.le
  have := isProbabilityMeasure_islandsShockLaw hA
  have hν : IsFiniteMeasure (islandsNextLaw xlo xhi θlo θhi ψ g) :=
    islands_isFiniteMeasure_comap _
  have hκ := isFiniteMeasure_islandsREBeliefs hA hπ p
  obtain ⟨ρ, hρc, hρm, hρ⟩ := islands_eqm_price_of_ratio hx0 hxx hθ0 hθθ hH hV he hp
  have hray : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      (w * shocksA xlo θlo w, shocksA xlo θlo w) ∈ Icc xlo xhi ×ˢ Icc θlo θhi ∧
        (w * shocksA xlo θlo w) / shocksA xlo θlo w = w := fun w hw =>
    ⟨shocks_rayPoint_mem hx0 hxx hθ0 hθθ hw,
      mul_div_cancel_right₀ _ (hθ0.trans_le (le_max_right (xlo / w) θlo)).ne'⟩
  have hpρ : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = ρ w := fun w hw => by
    rw [(hρ _ (hray w hw).1).1, (hray w hw).2]
  have hnρ : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      n (w * shocksA xlo θlo w, shocksA xlo θlo w) = w / ρ w := fun w hw => by
    rw [(hρ _ (hray w hw).1).2, (hray w hw).2]
  have hinjρ : InjOn ρ (Icc (xlo / θhi) (xhi / θlo)) := by
    rcases hρm with h | h
    · exact h.injOn
    · exact h.injOn
  have hηmem : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo), w / ρ w ∈ Ioo 0 L := fun w hw => by
    have h1 := he.n_mem _ (hray w hw).1
    have h2 := he.clear _ (hray w hw).1
    have h3 := he.p_pos hx0 hθ0 (hray w hw).1
    rw [hnρ w hw] at h1 h2
    rw [(hray w hw).2] at h2
    refine ⟨?_, h1.2⟩
    have hw0 : 0 < w := (div_pos hx0 (hθ0.trans_le hθθ)).trans_le hw.1
    rw [hpρ w hw] at h3
    exact div_pos hw0 h3
  have hηc : ContinuousOn (fun w => w / ρ w) (Icc (xlo / θhi) (xhi / θlo)) :=
    continuousOn_id.div hρc fun w hw => by
      have := he.p_pos hx0 hθ0 (hray w hw).1
      rw [hpρ w hw] at this
      exact this.ne'
  have hfc : Continuous fun z : Icc (xlo / θhi) (xhi / θlo) => olgZeta H' ((z : ℝ) / ρ z) :=
    hH.zeta_continuousOn.comp_continuous (hηc.comp_continuous continuous_subtype_val
      fun z => z.2) fun z => Ioo_subset_Ico_self (hηmem z.1 z.2)
  set f := BoundedContinuousFunction.mkOfCompact ⟨_, hfc⟩ with hfdef
  have hfz : ∀ z : Icc (xlo / θhi) (xhi / θlo), f z = olgZeta H' ((z : ℝ) / ρ z) := fun z => rfl
  have hfinv : ∀ z : Icc (xlo / θhi) (xhi / θlo), olgZetaInv L H' (f z) = (z : ℝ) / ρ z :=
    fun z => by rw [hfz]; exact hH.zetaInv_zeta (Ioo_subset_Ico_self (hηmem z.1 z.2))
  have hfpos : ∀ z, 0 < f z := fun z => by rw [hfz]; exact hH.zeta_pos (hηmem z.1 z.2)
  have hp' : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))) := fun s hs => by
    have hz := shocks_ratio_mem_Z hx0 hθ0 hs
    rw [hfinv, projIcc_of_mem _ hz, (hρ s hs).1]
    simp only
    have hρ0 : 0 < ρ (s.1 / s.2) := by
      have := he.p_pos hx0 hθ0 hs
      rwa [(hρ s hs).1] at this
    have hs1 : s.1 ≠ 0 := (hx0.trans_le hs.1.1).ne'
    have hs2 : s.2 ≠ 0 := (hθ0.trans_le hs.2.1).ne'
    field_simp
  refine ⟨f, hfpos, fun z => ?_, fun z w hzw => ?_, hp'⟩
  · -- the first-order condition along the ray `z` is `f = Tf`
    have hs := (hray z.1 z.2).1
    have hfoc := islands_foc hx0 hθ0 hH hV he hp hs
    have hbel := islandsREBeliefs_eq (p := p) (ψ := ψ) (g := g) z.2 fun w hw hpw => by
      rw [hpρ w hw, hpρ z.1 z.2] at hpw
      exact hinjρ hw z.2 hpw
    have hns : n (z.1 * shocksA xlo θlo z.1, shocksA xlo θlo z.1) = olgZetaInv L H' (f z) := by
      rw [hnρ z.1 z.2, hfinv]
    rw [hbel, hns, hH.zeta_zetaInv (hfpos z).le] at hfoc
    rw [hfoc]
    exact islands_RE_phi_eq hA hπ hH hV hZ f f.continuous hfpos hp' z
  · -- the price function is invertible
    simp only [hfinv] at hzw
    have h1 : ρ z = ρ w := by
      have hz0 : 0 < (z : ℝ) := (div_pos hx0 (hθ0.trans_le hθθ)).trans_le z.2.1
      have hw0 : 0 < (w : ℝ) := (div_pos hx0 (hθ0.trans_le hθθ)).trans_le w.2.1
      have hρz : 0 < ρ z := by
        have := (hηmem z.1 z.2).1
        exact (div_pos_iff_of_pos_left hz0).1 this
      have hρw : 0 < ρ w := by
        have := (hηmem w.1 w.2).1
        exact (div_pos_iff_of_pos_left hw0).1 this
      rw [div_div_cancel₀ hz0.ne', div_div_cancel₀ hw0.ne'] at hzw
      exact hzw
    exact Subtype.ext (hinjρ z.2 w.2 h1)

/-! ### Proposition 8 fails as a statement about equilibria -/

omit hA in
/-- **No equilibrium in the bimodal CRRA economy.** In the economy of
`proposition_8_counterexample` (Assumptions 17.1, 17.2 (repaired), 17.4 and 17.5 hold) there is
no equilibrium of the islands economy with a continuous price function, rational-expectations
beliefs and the true law of next period's shocks: it would give a positive fixed point of (4)
with invertible price function (`islands_fixedPoint_of_eqm`), and every positive fixed point has
a non-invertible one (`shocksP8_not_injective`). -/
theorem shocksP8_no_continuous_eqm :
    ¬ ∃ p n : ℝ × ℝ → ℝ, ContinuousOn p (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2)) ∧
      IslandsEqm 1 monoCexH shocksP8V p n
        (islandsREBeliefs 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal p)
        (islandsNextLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal) := by
  rintro ⟨p, n, hp, he⟩
  obtain ⟨f, hfpos, hfix, hinj, -⟩ := islands_fixedPoint_of_eqm shocksExBimodal_assumption
    (fun z hz => shocksExBimodal_pi_pos hz) monoCexH_assumption17_1H' shocksP8V_assumptions.1
    shocksP8_hZ he hp
  exact (shocksP8_not_injective f hfpos hfix).1 hinj

omit hA in
/-- `W'(y) ≥ A = 1/60000` on `(0, 1]` when `y₀ ≤ 1`. -/
theorem shocksP8W'_ge {y₀ y : ℝ} (hy₀ : 0 < y₀) (hy₀1 : y₀ ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    1 / 60000 ≤ shocksP8W' y₀ y := by
  simp only [shocksP8W', shocksP8V']
  split_ifs with h
  · have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by norm_num : (-(1 / 20) : ℝ) ≤ 0)
    nlinarith
  · have h1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy₀ hy₀1
      (by norm_num : (-(1 / 20) : ℝ) ≤ 0)
    have h2 : y / y₀ < 1 := (div_lt_one hy₀).2 (not_le.1 h)
    have e : 1 / 20 * y / y₀ = 1 / 20 * (y / y₀) := by ring
    rw [e]
    nlinarith

omit hA in
/-- **An a priori lower bound** for the utility `shocksP8W y₀`, `y₀ ≤ 1`: every strictly positive
continuous fixed point of (4) in the bimodal economy has `η = ζ⁻¹ ∘ f ≥ 1/180000 = A/3`, since
`φ_W(y) ≥ A y` on `(0, 1]` and the arguments of `φ` are at least `(2/3) min η`. -/
theorem shocksP8W_eta_ge {y₀ : ℝ} (hy₀ : 0 < y₀) (hy₀1 : y₀ ≤ 1)
    (f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) :
    ∀ z, 1 / 180000 ≤ olgZetaInv 1 monoCexH' (f z) := by
  have hH := monoCexH_assumption17_1H'
  have hV := shocks_assumption17_1VR_of_V (shocksP8W_assumptions hy₀).1
  have h4 : MonoAssumption17_4Pos (shocksP8W' y₀) (shocksP8W'' y₀) := fun y hy =>
    (shocksP8W_assumptions hy₀).2 y hy.le
  have hφm := shocks_phi_monotoneOn hV h4
  have hA := shocksExBimodal_assumption
  have := isProbabilityMeasure_shocksJointLaw hA shocksP8_hZ
  have hν : ∀ z : ℝ, IsProbabilityMeasure
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) :=
    hA.isProbabilityMeasure_condLaw' fun z hz => shocksExBimodal_pi_pos hz
  obtain ⟨l₀, hS⟩ := shocksBounds_exists one_pos (by norm_num : (1 : ℝ) ≤ 3 / 2) hH hV
  have hne : (univ : Set (Icc (1 / (3 / 2) : ℝ) (2 / 1))).Nonempty :=
    ⟨⟨_, left_mem_Icc.2 shocksP8_hZ⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne f.continuous.continuousOn
  set ηm := olgZetaInv 1 monoCexH' (f m) with hηmdef
  have hηm : ηm ∈ Ioo 0 1 := ⟨hH.zetaInv_pos (hfpos m), (hH.zetaInv_mem (hfpos m).le).2⟩
  have hle : ∀ z, ηm ≤ olgZetaInv 1 monoCexH' (f z) := fun z =>
    hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hfpos m).le) (mem_Ici.2 (hfpos z).le)
      (isMinOn_iff.1 hm z (mem_univ z))
  set l := min l₀ ηm
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hS.l₀_mem.1 hηm.1, min_le_left _ _⟩
  have hlL : l ∈ Ico 0 1 := ⟨hl.1.le, hl.2.trans_lt hS.l₀_mem.2⟩
  have hfl : ∀ z, olgZeta monoCexH' l ≤ f z := fun z =>
    calc olgZeta monoCexH' l ≤ olgZeta monoCexH' ηm :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
      _ ≤ f z := isMinOn_iff.1 hm z (mem_univ z)
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le hl
  -- the integrand is at least `c = (2/3) ηm A`
  set c := 2 / 3 * ηm * (1 / 60000) with hcdef
  have hpt : ∀ θt (ω : ℝ × Icc (1 / (3 / 2) : ℝ) (2 / 1)),
      c ≤ shocksIntegrand 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2) f θt ω := fun θt ω => by
    have hr := (shocksRatio_mem (θlo := (1 : ℝ)) (θhi := 3 / 2) one_pos (by norm_num) ω.1 θt).1
    have hη' := hle ω.2
    have hy1 : 0 < 2 / 3 * ηm := by linarith [hηm.1]
    have hy : 2 / 3 * ηm ≤ shocksRatio 1 (3 / 2) ω.1 θt * olgZetaInv 1 monoCexH' (f ω.2) := by
      have hr' : (2 : ℝ) / 3 ≤ shocksRatio 1 (3 / 2) ω.1 θt :=
        (by norm_num : (2 : ℝ) / 3 = 1 / (3 / 2)).trans_le hr
      nlinarith [hηm.1]
    have h1 := hφm (mem_Ioi.2 hy1) (mem_Ioi.2 (hy1.trans_le hy)) hy
    have h2 := shocksP8W'_ge hy₀ hy₀1 hy1 (by linarith [hηm.2])
    simp only [shocksIntegrand]
    refine le_trans ?_ h1
    simp only [olgPhi, hcdef]
    nlinarith
  have hphi : ∀ θt, c ≤ shocksPhiF 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal) f θt :=
    fun θt => by
      have := integral_mono (integrable_const c)
        (hS.integrable_integrand hl hB f.continuous hfl
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal) θt)
        fun ω => hpt θt ω
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
      exact this
  have hfm : c ≤ f m := by
    rw [hfix m]
    have := integral_mono (integrable_const c)
      ((hS.phiFBCF hl hB f.continuous hfl
        (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)).integrable
        (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal m.1)) fun θt => hphi θt
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  have hζ := shocksP8_zeta_eq hηm.2 (hH.zeta_zetaInv (hfpos m).le)
  have key : ηm * ((1 - ηm) / 90000) ≤ ηm * ηm := by
    have h1m : 0 < 1 - ηm := by linarith [hηm.2]
    have := mul_le_mul_of_nonneg_right hfm h1m.le
    simp only [hcdef] at this
    nlinarith
  have := le_of_mul_le_mul_left key hηm.1
  intro z
  linarith [hle z]

omit hA in
/-- **No equilibrium under the book's hypotheses.** With the utility `shocksP8W (1/300000)`
(the book's Assumption 17.1, `V'(0) < ∞`, and Assumption 17.4; `H` as in Assumption 17.1) the
bimodal economy has no equilibrium with a continuous price function, rational-expectations
beliefs and the true law of next period's shocks. A positive fixed point of (4) for this `V` has
`η ≥ A/3 > (3/2) y₀` (`shocksP8W_eta_ge`), so it is also a fixed point for the CRRA utility
(`shocksP8W_opT_eq`), whose price function is not invertible. -/
theorem shocksP8W_no_continuous_eqm :
    ¬ ∃ p n : ℝ × ℝ → ℝ, ContinuousOn p (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2)) ∧
      IslandsEqm 1 monoCexH (shocksP8W (1 / 300000)) p n
        (islandsREBeliefs 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal p)
        (islandsNextLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal) := by
  rintro ⟨p, n, hp, he⟩
  have hy : (0 : ℝ) < 1 / 300000 := by norm_num
  obtain ⟨f, hfpos, hfix, hinj, -⟩ := islands_fixedPoint_of_eqm shocksExBimodal_assumption
    (fun z hz => shocksExBimodal_pi_pos hz) monoCexH_assumption17_1H'
    (shocks_assumption17_1VR_of_V (shocksP8W_assumptions hy).1) shocksP8_hZ he hp
  have hη := shocksP8W_eta_ge hy (by norm_num) f hfpos hfix
  have hfix' : ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z :=
    fun z => (hfix z).trans (shocksP8W_opT_eq hy _ _ f (fun w => by linarith [hη w]) z)
  exact (shocksP8_not_injective f hfpos hfix').1 hinj

omit hA in
/-- **Proposition 8 (p. 540) fails for equilibria.** The bimodal economy with the utility
`shocksP8W (1/300000)` satisfies all hypotheses of Proposition 8 (the book's Assumptions 17.1 and
17.4, and Assumption 17.5), yet it has no equilibrium with a continuous price function at all,
let alone one with an increasing price function. -/
theorem proposition_8_eqm_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal ∧
      Assumption17_1 1 monoCexH monoCexH' monoCexH'' (shocksP8W (1 / 300000))
        (shocksP8W' (1 / 300000)) (shocksP8W'' (1 / 300000)) ∧
      MonoAssumption17_4 (shocksP8W' (1 / 300000)) (shocksP8W'' (1 / 300000)) ∧
      ¬ ∃ p n : ℝ × ℝ → ℝ, ContinuousOn p (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2)) ∧
        IslandsEqm 1 monoCexH (shocksP8W (1 / 300000)) p n
          (islandsREBeliefs 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal p)
          (islandsNextLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal) :=
  ⟨shocksExBimodal_assumption, ⟨monoCexH_assumption17_1H',
    (shocksP8W_assumptions (by norm_num)).1⟩, (shocksP8W_assumptions (by norm_num)).2,
    shocksP8W_no_continuous_eqm⟩

end StokeyLucasPrescott.FixedPointArguments

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_polynomial_det_id_add_smul
#print axioms StokeyLucasPrescott.FixedPointArguments.integral_eq_of_polynomial_of_eq_on_Ioc
#print axioms StokeyLucasPrescott.FixedPointArguments.isUnit_id_add_smul
#print axioms StokeyLucasPrescott.FixedPointArguments.no_C1_retraction
#print axioms StokeyLucasPrescott.FixedPointArguments.C1Restrictions
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_C1_approx_real
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_C1_approx
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer_closedBall
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer_ball
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_lipschitz_retraction
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer_inner
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer_subtype
#print axioms StokeyLucasPrescott.FixedPointArguments.theorem_17_3
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.L_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H'_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H''_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H_mono
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H_conv
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H'_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.H'_tendsto
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.V_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.V_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.V'_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.V''_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.V_mono
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_1.V_conc
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta
#print axioms StokeyLucasPrescott.FixedPointArguments.fpPhi
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_H'_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_H'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_H'_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_H'_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_V'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_V'_strictAntiOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpA_V'_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_exists_gt
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_surjOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZetaInv_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZeta_zetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZetaInv_zeta
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZetaInv_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZetaInv_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpZetaInv_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpPhi_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fpPhi_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.fpPhi_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.fpPhi_comp_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_bounds
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer_finite_state
#print axioms StokeyLucasPrescott.FixedPointArguments.brouwer_log_transform_fixedPoint_iff
#print axioms StokeyLucasPrescott.FixedPointArguments.log_image_isCompact_convex
#print axioms StokeyLucasPrescott.FixedPointArguments.exp_image_log_image
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_finite_states_bounds
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_3
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_3_zero_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.bcf_le_iff
#print axioms StokeyLucasPrescott.FixedPointArguments.isMonotoneOperator
#print axioms StokeyLucasPrescott.FixedPointArguments.isMonotoneOperator_iff_monotoneOn
#print axioms StokeyLucasPrescott.FixedPointArguments.cauchySeq_of_uniformEquicontinuous
#print axioms StokeyLucasPrescott.FixedPointArguments.lemma_17_6
#print axioms StokeyLucasPrescott.FixedPointArguments.monotone_iterate_of_le
#print axioms StokeyLucasPrescott.FixedPointArguments.antitone_iterate_of_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_abs_le_of_isBounded
#print axioms StokeyLucasPrescott.FixedPointArguments.theorem_17_7_of_le
#print axioms StokeyLucasPrescott.FixedPointArguments.theorem_17_7_of_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.theorem_17_7
#print axioms StokeyLucasPrescott.FixedPointArguments.le_of_tendsto_bcf
#print axioms StokeyLucasPrescott.FixedPointArguments.ge_of_tendsto_bcf
#print axioms StokeyLucasPrescott.FixedPointArguments.corollary_17_7_least
#print axioms StokeyLucasPrescott.FixedPointArguments.corollary_17_7_greatest
#print axioms StokeyLucasPrescott.FixedPointArguments.corollary_17_7
#print axioms StokeyLucasPrescott.FixedPointArguments.corollary_17_7_unique
#print axioms StokeyLucasPrescott.FixedPointArguments.totallyBounded_univ_of_isBounded
#print axioms StokeyLucasPrescott.FixedPointArguments.theorem_17_7_of_isBounded
#print axioms StokeyLucasPrescott.FixedPointArguments.IsFinMeasPartition
#print axioms StokeyLucasPrescott.FixedPointArguments.TVDistLE
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_3
#print axioms StokeyLucasPrescott.FixedPointArguments.isFinMeasPartition_pair
#print axioms StokeyLucasPrescott.FixedPointArguments.abs_integral_sub_le_of_le
#print axioms StokeyLucasPrescott.FixedPointArguments.abs_integral_sub_le_of_tvDistLE
#print axioms StokeyLucasPrescott.FixedPointArguments.uniformEquicontinuous_integral
#print axioms StokeyLucasPrescott.FixedPointArguments.continuous_integral_of_assumption17_3
#print axioms StokeyLucasPrescott.FixedPointArguments.kernelIntegral_uniformEquicontinuous
#print axioms StokeyLucasPrescott.FixedPointArguments.measurable_kernelIntegrand
#print axioms StokeyLucasPrescott.FixedPointArguments.kernelIntegral_dist_le
#print axioms StokeyLucasPrescott.FixedPointArguments.kernelOp
#print axioms StokeyLucasPrescott.FixedPointArguments.kernelOp_apply_of_continuous
#print axioms StokeyLucasPrescott.FixedPointArguments.kernelOp_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.kernelOp_monotone_fixedPoints
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.L_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.hasDeriv_H
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.hasDeriv_H'
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.continuousOn_H''
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.strictConvexOn
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.deriv_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.tendsto_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.hasDeriv_V
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.hasDeriv_V'
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.continuousOn_V''
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.strictConcaveOn
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1.hH
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1.hV
#print axioms StokeyLucasPrescott.FixedPointArguments.monoZeta
#print axioms StokeyLucasPrescott.FixedPointArguments.monoPhi
#print axioms StokeyLucasPrescott.FixedPointArguments.monoZetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_4
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.continuousOn_H'
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.strictMonoOn_H'
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.H'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.H'_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.monoZeta_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.continuousOn_zeta
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.strictMonoOn_zeta
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zeta_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.surjOn_zeta
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zetaInv_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zeta_zetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zetaInv_zeta
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zetaInv_of_nonpos
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zetaInv_monotone
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zetaInv_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.zetaInv_continuous
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.exists_lt_zetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.monoEpsK
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.epsK_spec
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.continuousOn_V'
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.V'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.strictAntiOn_V'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoPhi_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.continuousOn_phi
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.monotoneOn_phi
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLGKernel
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLGOp
#print axioms StokeyLucasPrescott.FixedPointArguments.monoB
#print axioms StokeyLucasPrescott.FixedPointArguments.monoF
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1H.arg_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.exists_bound_phi
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLG_integrand_continuous
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLGOp_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLGOp_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLG_bounds
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLG_K_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_5
#print axioms StokeyLucasPrescott.FixedPointArguments.monoOLG_fixedPoint_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_5_corrected
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_5_corrected'
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_5_literal_false
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexH
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexH'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexH''
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexV
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexV'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexV''
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoCexH
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoCexH'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexH_assumption17_1H
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoCexV
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoCexV'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexV_assumption17_1V
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCex_assumption17_1
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA_monoCexV
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexV_assumption17_4
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexX
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexX₁
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexπ
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexπ_assumption17_3
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCex_fixedPoint_root
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCex_fixedPoint_unique_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_5_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA_not_forall_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA_pos_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexW
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexW'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexW''
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoCexW
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoCexW'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexW'_strictAntiOn
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexW_assumption17_1V
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA_interior_zero_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.rra_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_1V.exists_rra_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_2
#print axioms StokeyLucasPrescott.FixedPointArguments.not_monoAssumption17_2
#print axioms StokeyLucasPrescott.FixedPointArguments.monoAssumption17_2_imp_17_4
#print axioms StokeyLucasPrescott.FixedPointArguments.assumption17_4_not_imp_17_2_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_2Pos
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_4Pos
#print axioms StokeyLucasPrescott.FixedPointArguments.monoAssumption17_2Pos_of_17_4Pos
#print axioms StokeyLucasPrescott.FixedPointArguments.assumption17_4Pos_not_imp_17_2Pos_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.monoArcV
#print axioms StokeyLucasPrescott.FixedPointArguments.monoArcV'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoArcV''
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoArcV
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_monoArcV'
#print axioms StokeyLucasPrescott.FixedPointArguments.monoArcV_repaired_utility
#print axioms StokeyLucasPrescott.FixedPointArguments.monoRRA_monoArcV
#print axioms StokeyLucasPrescott.FixedPointArguments.assumption17_2Pos_not_imp_17_4Pos_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.IsFellerKernel
#print axioms StokeyLucasPrescott.FixedPointArguments.olgOpT
#print axioms StokeyLucasPrescott.FixedPointArguments.olgF
#print axioms StokeyLucasPrescott.FixedPointArguments.OLGOperatorHyp
#print axioms StokeyLucasPrescott.FixedPointArguments.OLGOperatorHyp.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.OLGOperatorHyp.convex
#print axioms StokeyLucasPrescott.FixedPointArguments.OLGOperatorHyp.cont
#print axioms StokeyLucasPrescott.FixedPointArguments.OLGOperatorHyp.mapsTo
#print axioms StokeyLucasPrescott.FixedPointArguments.OLGOperatorHyp.feller
#print axioms StokeyLucasPrescott.FixedPointArguments.isFellerKernel_deterministic_id
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_2a_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_2a_counterexample_bounded
#print axioms StokeyLucasPrescott.FixedPointArguments.continuous_olgIntegrand
#print axioms StokeyLucasPrescott.FixedPointArguments.olgSection
#print axioms StokeyLucasPrescott.FixedPointArguments.olgSection_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.integrable_olgIntegrand
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_2a
#print axioms StokeyLucasPrescott.FixedPointArguments.olgTF
#print axioms StokeyLucasPrescott.FixedPointArguments.olgTF_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.isClosed_olgF
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_2b
#print axioms StokeyLucasPrescott.FixedPointArguments.olgTF_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.lemma_17_1
#print axioms StokeyLucasPrescott.FixedPointArguments.olgDhat
#print axioms StokeyLucasPrescott.FixedPointArguments.olgDhat_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.exp_mem_of_mem_olgDhat
#print axioms StokeyLucasPrescott.FixedPointArguments.olgDhat_isClosed
#print axioms StokeyLucasPrescott.FixedPointArguments.olgDhat_convex
#print axioms StokeyLucasPrescott.FixedPointArguments.olgOpThat
#print axioms StokeyLucasPrescott.FixedPointArguments.olgOpThat_log
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_4a_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_4a
#print axioms StokeyLucasPrescott.FixedPointArguments.olgThatF
#print axioms StokeyLucasPrescott.FixedPointArguments.olgThatF_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_4b
#print axioms StokeyLucasPrescott.FixedPointArguments.abs_log_G_sub_le
#print axioms StokeyLucasPrescott.FixedPointArguments.olgThatF_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.lemma_17_2
#print axioms StokeyLucasPrescott.FixedPointArguments.lemma_17_2_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.L_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H''_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H_mono
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H_conv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_tendsto
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V'_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V''_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V_mono
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V_conc
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1.hH
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1.hV
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H'_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.H''_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.exists_H'_gt
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V'_strictAntiOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V'_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1V.V'_le_V'_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.measurable_comp_of_continuousOn_Ici
#print axioms StokeyLucasPrescott.FixedPointArguments.integral_pos_of_forall_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.margUtil
#print axioms StokeyLucasPrescott.FixedPointArguments.consumerObj
#print axioms StokeyLucasPrescott.FixedPointArguments.integrable_margUtil
#print axioms StokeyLucasPrescott.FixedPointArguments.continuousOn_margUtil
#print axioms StokeyLucasPrescott.FixedPointArguments.margUtil_strictAntiOn
#print axioms StokeyLucasPrescott.FixedPointArguments.margUtil_zero_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.margUtil_le
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_unique_foc
#print axioms StokeyLucasPrescott.FixedPointArguments.integrable_utility
#print axioms StokeyLucasPrescott.FixedPointArguments.continuousOn_utility
#print axioms StokeyLucasPrescott.FixedPointArguments.hasDerivAt_utility
#print axioms StokeyLucasPrescott.FixedPointArguments.consumer_problem
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_1
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm.p_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm.p_meas
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm.n_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm.optimal
#print axioms StokeyLucasPrescott.FixedPointArguments.IsStationaryEqm.clearing
#print axioms StokeyLucasPrescott.FixedPointArguments.eq3_of_isStationaryEqm
#print axioms StokeyLucasPrescott.FixedPointArguments.isStationaryEqm_of_eq3
#print axioms StokeyLucasPrescott.FixedPointArguments.olgZeta
#print axioms StokeyLucasPrescott.FixedPointArguments.olgPhi
#print axioms StokeyLucasPrescott.FixedPointArguments.eq3_iff_eq4
#print axioms StokeyLucasPrescott.FixedPointArguments.margUtil_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.integral_olgPhi
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_1
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_1_logRatio_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_1_phi_zero_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.rra_pos_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH1
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH2
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH1_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH1_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH2_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH1_tendsto
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH1_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.olgExH_assumption
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_1_elasticity_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.zeta_elasticity_ge_one
#print axioms StokeyLucasPrescott.FixedPointArguments.olgZetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_surj
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_zetaInv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_zeta
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_strictMonoOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_image_Ici
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_image_Ioi
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zeta_deriv_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.zetaInv_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.eq8_iff_eq4
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1H.exists_H'_lt
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_3
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2.β_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2.β_lt_one
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2.lower
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2.upper
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R.β_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R.β_lt_one
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R.lower
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R.upper
#print axioms StokeyLucasPrescott.FixedPointArguments.assumption17_2_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.assumption17_2R_inconsistent
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V'_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V''_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V_mono
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V_conc
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V'_strictAntiOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.V'_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.phi_continuousOn
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.phi_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.crra_assumption17_1VR
#print axioms StokeyLucasPrescott.FixedPointArguments.crra_assumption17_2R
#print axioms StokeyLucasPrescott.FixedPointArguments.repaired_assumptions_nonvacuous
#print axioms StokeyLucasPrescott.FixedPointArguments.olgMargBCF
#print axioms StokeyLucasPrescott.FixedPointArguments.continuousOn_margUtil_R
#print axioms StokeyLucasPrescott.FixedPointArguments.margUtil_R_strictAntiOn
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_1_repaired
#print axioms StokeyLucasPrescott.FixedPointArguments.olgG
#print axioms StokeyLucasPrescott.FixedPointArguments.olgG_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.olgG_hyp
#print axioms StokeyLucasPrescott.FixedPointArguments.olgG_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.olgG_elasticity_le
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_2
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_2_zero_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_2_nonneg_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.epsK_exists
#print axioms StokeyLucasPrescott.FixedPointArguments.epsK_tendsto_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.exists_approx_fixed_point
#print axioms StokeyLucasPrescott.FixedPointArguments.schauder
#print axioms StokeyLucasPrescott.FixedPointArguments.schauder_subtype
#print axioms StokeyLucasPrescott.FixedPointArguments.schauder_closed
#print axioms StokeyLucasPrescott.FixedPointArguments.schauder_closed_subtype
#print axioms StokeyLucasPrescott.FixedPointArguments.totallyBounded_of_equicontinuous
#print axioms StokeyLucasPrescott.FixedPointArguments.theorem_17_4
#print axioms StokeyLucasPrescott.FixedPointArguments.fpOdeOp
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_ode_exists
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5a_local
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5a_of_bounded
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5a_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5a_false
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5a_blowup_solution
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5b
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5b_family
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5b_manual_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_5c
#print axioms StokeyLucasPrescott.FixedPointArguments.FPIsFinPartition
#print axioms StokeyLucasPrescott.FixedPointArguments.fpTVNorm
#print axioms StokeyLucasPrescott.FixedPointArguments.fpIsFinPartition_univ
#print axioms StokeyLucasPrescott.FixedPointArguments.fpTVNorm_bddAbove
#print axioms StokeyLucasPrescott.FixedPointArguments.fpTVNorm_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_le_tvNorm_pair
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_abs_integral_sub_le_of_le
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_abs_integral_sub_le
#print axioms StokeyLucasPrescott.FixedPointArguments.FPAssumption17_3
#print axioms StokeyLucasPrescott.FixedPointArguments.fpAssumption17_3_const
#print axioms StokeyLucasPrescott.FixedPointArguments.fpIntOp
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_integrand_continuous
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_G_bound
#print axioms StokeyLucasPrescott.FixedPointArguments.lemma_17_5
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_6
#print axioms StokeyLucasPrescott.FixedPointArguments.fp_exists_fixedPoint_intOp
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_4
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_4_zero_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.fpLabourOp
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_7_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_7_why_of_f
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_7_why_of_n
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_7
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.xlo_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.xlo_lt
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.θlo_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.θlo_lt
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.θhi_lt
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ψ_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.g_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ψ_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.g_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ψ_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.g_cont
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ψ_int
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.g_int
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksPi
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksA
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksB
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksCondDens
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksCondLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.mem_Icc_shocksA_shocksB_iff
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_measurable_of_zero_off
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_exists_bound_of_zero_off
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksA_lt_shocksB
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ψ_meas
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.g_meas
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.mem_Z_of
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.integrable_joint
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.inner_change
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.joint
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.exists_joint_bound
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.measurable_joint
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.integrable_slice
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.integrable_joint_slice
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.joint_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.joint_eq_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.pi_nonneg
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.integral_pi
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.pos_of_pi_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.measurable_condDens
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ex_17_8a
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ex_17_8a_disintegration
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.isProbabilityMeasure_condLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.integral_condLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.pi_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ψ_continuousAt
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.continuousAt_slice
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.abs_integral_condDens_sub_le
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.ex_17_8b
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksAssumption17_5.isProbabilityMeasure_condLaw'
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksUnif
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_setIntegral_Icc_id
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksUnif_assumption17_5
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksUnif_joint
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksUnif_pi
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_12
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEx_assumption
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEx_ab
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEx_pi
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_8a_manual_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_12_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_exists_mem_of_ae_restrict_Icc
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEx_condDens_four_fifths
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_8a_continuity_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExG0
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExG
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExG0_integral_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_8a_pi_zero_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEx_pi_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExSeq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExSeq_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExSeq_tendsto
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEx_condLaw_seq_eq_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_10
#print axioms StokeyLucasPrescott.FixedPointArguments.p533_ratio_of_price
#print axioms StokeyLucasPrescott.FixedPointArguments.p533_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksClamp
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksClamp_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksClamp_of_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.continuous_shocksClamp
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksRatio
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksRatio_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.continuous_shocksRatio
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksIntegrand
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksPhiF
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksOpT
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksIntegrand_eq_olgG
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksOpT_zero
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.θlo_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.θlo_le
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.hH
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.hV
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.l₀_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.l₀_lt
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksBounds_exists
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.ratio_bounds
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.zeta_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.integrand_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.exists_integrand_le
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.continuous_integrand
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.abs_integrand_le
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.integrable_integrand
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.phiF_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.continuous_phiF
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.phiFBCF
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.phiFBCF_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.opT_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.abs_log_integrand_sub_le
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.opT_exp_le
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.opT_exp_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.opThat
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.opThat_apply
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.ex_17_9
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.unique_fixedPoint_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_6
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_6_zero_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_6_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksJointLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_isProbabilityMeasure_withDensity
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_integrable_of_zero_off
#print axioms StokeyLucasPrescott.FixedPointArguments.isProbabilityMeasure_shocksJointLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_6_islands
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_of_lt
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_integral_id
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_integral_id_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_mul_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_intervalIntegrable
#print axioms StokeyLucasPrescott.FixedPointArguments.abs_sub_shocksWAvg_le
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_extend_right
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_extend_left
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_abs_div_le
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_lip_right
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_lip_left
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksA_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksB_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksA_shocksB_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksUnif_integral_condLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_assumption17_1VR_of_V
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.exists_phi_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.ex_17_13
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.ex_17_11_step3
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksUnif_opT_lipschitz
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_7
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_7_islands
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_hasDerivAt_const_div
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksA_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksB_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.eq7_corrected
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_finite_Z
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_V''_nonpos
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14c_phi
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_phi_elasticity
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_phi_monotoneOn
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14a_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14a
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksEtaEx
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14a_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14b_chain
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14b
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14b_le
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksClamp_div_antitoneOn
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksIntegrandDeriv
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksClamp_monotone
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.integrand_antitone
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.integrand_mul_monotoneOn
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.phiF_antitoneOn
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.phiF_mul_monotoneOn
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.integrand_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.integrandDeriv_bound
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.ex_17_13_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.ex_17_14c
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksBounds.opT_monotone
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_le_of_le
#print axioms StokeyLucasPrescott.FixedPointArguments.le_shocksWAvg_of_le
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_mono
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_right_antitone
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_left_antitone
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksWAvg_div
#print axioms StokeyLucasPrescott.FixedPointArguments.mul_shocksA
#print axioms StokeyLucasPrescott.FixedPointArguments.mul_shocksB
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14d
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_accPt_Icc
#print axioms StokeyLucasPrescott.FixedPointArguments.ex_17_14d_deriv
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_integral_quad
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_integral_indicator_Icc
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBump1
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBump2
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBump_integrals
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal_assumption
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal_integral_inv
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8_general_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_1VR.const_mul
#print axioms StokeyLucasPrescott.FixedPointArguments.Assumption17_2R.const_mul
#print axioms StokeyLucasPrescott.FixedPointArguments.MonoAssumption17_4Pos.const_mul
#print axioms StokeyLucasPrescott.FixedPointArguments.crra_monoAssumption17_4Pos
#print axioms StokeyLucasPrescott.FixedPointArguments.monoCexH_assumption17_1H'
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal_pi_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal_integral_inv_values
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal_integral_clamp
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8V
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8V'
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8V''
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8V_assumptions
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_phi_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_opT_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_hZ
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksExBimodal_condLaw_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_clamp_bounds
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_continuous
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_zeta_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_rho_ineq
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_existsUnique_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_not_injective
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8_counterexample
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8_assumption17_5_false
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_hasDerivAt_ite
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W'
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W''
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W'_hasDerivAt
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W'_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W''_neg
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W_assumptions
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W_opT_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8_counterexample_book
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8_false
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_exists_ray_approx
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_convex_ray
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_const_on_rays
#print axioms StokeyLucasPrescott.FixedPointArguments.ShocksStates
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsObj
#print axioms StokeyLucasPrescott.FixedPointArguments.IslandsEqm
#print axioms StokeyLucasPrescott.FixedPointArguments.IslandsEqm.mk
#print axioms StokeyLucasPrescott.FixedPointArguments.IslandsEqm.n_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.IslandsEqm.opt
#print axioms StokeyLucasPrescott.FixedPointArguments.IslandsEqm.clear
#print axioms StokeyLucasPrescott.FixedPointArguments.IslandsEqm.p_pos
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsObj_max_unique
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_rayPoint_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_ratio_mem_Z
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_eqm_price_of_ratio
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_eqm_not_injOn
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_concave_tangent
#print axioms StokeyLucasPrescott.FixedPointArguments.shocks_convex_tangent
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_factor_continuous
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_foc
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsShockLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsNextLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsREBeliefs
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsREBeliefs_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.islandsShockLaw_ae_mem
#print axioms StokeyLucasPrescott.FixedPointArguments.integral_islandsNextLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.condLaw_ae_ray
#print axioms StokeyLucasPrescott.FixedPointArguments.integral_rayBelief
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_RE_phi_eq
#print axioms StokeyLucasPrescott.FixedPointArguments.isProbabilityMeasure_islandsShockLaw
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_isFiniteMeasure_comap
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_eqm_of_fixedPoint
#print axioms StokeyLucasPrescott.FixedPointArguments.isFiniteMeasure_islandsREBeliefs
#print axioms StokeyLucasPrescott.FixedPointArguments.islands_fixedPoint_of_eqm
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8_no_continuous_eqm
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W'_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W_eta_ge
#print axioms StokeyLucasPrescott.FixedPointArguments.shocksP8W_no_continuous_eqm
#print axioms StokeyLucasPrescott.FixedPointArguments.proposition_8_eqm_counterexample
