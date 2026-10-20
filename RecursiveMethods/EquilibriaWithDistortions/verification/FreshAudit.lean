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

namespace StokeyLucasPrescott.EquilibriaWithDistortions

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

end StokeyLucasPrescott.EquilibriaWithDistortions

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

namespace StokeyLucasPrescott.EquilibriaWithDistortions

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

end StokeyLucasPrescott.EquilibriaWithDistortions

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

namespace StokeyLucasPrescott.EquilibriaWithDistortions

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

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The crossing point of an Euler equation (the construction behind SLP §18.3 (7) and (9))

SLP §18.3, pp. 556–560, defines the operator `T` by "`(Th)(k)` is the `y` solving"
  `U′[ψ(k) − y] = (right-hand side in y)`,
where the left side is increasing in `y` and blows up at `y = ψ(k)`, and the right side is
nonincreasing in `y` and equals `+∞` wherever a next-period consumption is zero (Inada condition
of Assumption 18.2). This file isolates that one-dimensional construction, so that the
deterministic operator (7) and the stochastic operator (9) are two instances of it.

The right side is described abstractly on `[0, B]` by a predicate `Z y` ("some next-period
consumption is zero at `y`", where the right side is `+∞`) and a real function `R y` (its value
when `¬ Z y`). `IsEulerRHS B Z R` records that the extended-real function `Z, R` is
nonincreasing, continuous where finite and tends to `+∞` at the points where it is infinite.
For `P > 0` (current resources, `P = ψ(k)`) the *crossing point* is
  `eulerCross u Z R P := sup {y ∈ [0, P) : Z y ∨ u (P − y) < R y}`,
the supremum of the points where the left side lies strictly below the right side. It is the
extended-real reading of "the `y` solving (7)" (NOTE 18.3-E of the transcription).

* `eulerCross_spec`: if the left side is below the right side at `y = 0`, then **either** the
  crossing point is `< P`, both consumptions there are positive and the Euler equation holds,
  **or** the crossing point is `P` and the right side is `+∞` on all of `[0, P)` (no interior
  solution exists; the agent consumes nothing).
* `eulerCross_unique`: an interior solution of the Euler equation is the crossing point.
* `eulerCross_mono`, `eulerCross_le_add_sub` (more resources raise the crossing point, by at
  most the increase in resources) and `eulerCross_mono_rhs` (a larger right side raises it):
  the order properties behind Exercises 18.5 and 18.7.
* `eventually_abs_eulerCross_sub_le`: if right sides converge pointwise in the extended sense,
  the crossing points converge (the pointwise step of Exercise 18.6, done by the monotone
  crossing argument instead of the manual's Implicit Function Theorem).

Nothing here is in the book in this form; it is the common core of the proofs of
Exercises 18.5–18.8.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- The properties of the marginal utility `u = U′` used in §18.3: positive, strictly
decreasing and continuous on `(0, ∞)`, with the Inada condition `u(c) → ∞` as `c → 0⁺`
(Assumption 18.2). -/
structure IsMarginalUtility (u : ℝ → ℝ) : Prop where
  pos : ∀ c, 0 < c → 0 < u c
  strictAnti : StrictAntiOn u (Ioi 0)
  cont : ContinuousOn u (Ioi 0)
  inada : Tendsto u (𝓝[>] 0) atTop

/-- An extended-real "right side of the Euler equation" on `[0, B]`: it is `+∞` where `Z` holds
and `R y` otherwise. It is nonincreasing (`zero_anti`, `anti`), continuous where finite
(`cont`), and tends to `+∞` at the points where it is infinite (`blowup`). -/
structure IsEulerRHS (B : ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) : Prop where
  zero_anti : ∀ y y', 0 ≤ y' → y' ≤ y → y ≤ B → Z y → Z y'
  anti : ∀ y y', 0 ≤ y' → y' ≤ y → y ≤ B → ¬ Z y' → R y ≤ R y'
  cont : ∀ y ∈ Icc 0 B, ¬ Z y →
    (∀ᶠ y' in 𝓝[Icc 0 B] y, ¬ Z y') ∧ ContinuousWithinAt R (Icc 0 B) y
  blowup : ∀ y ∈ Icc 0 B, Z y → ∀ M : ℝ, ∀ᶠ y' in 𝓝[Icc 0 B] y, Z y' ∨ M < R y'

/-- The left side `u (P − y)` of the Euler equation lies strictly below the right side at `y`
(the right side being `+∞` if `Z y`). -/
def EulerBelow (u : ℝ → ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) (P y : ℝ) : Prop :=
  Z y ∨ u (P - y) < R y

/-- The points `y ∈ [0, P)` at which the left side is strictly below the right side. -/
def eulerSet (u : ℝ → ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) (P : ℝ) : Set ℝ :=
  {y | 0 ≤ y ∧ y < P ∧ EulerBelow u Z R P y}

/-- The crossing point of the Euler equation: the supremum of `eulerSet`. -/
noncomputable def eulerCross (u : ℝ → ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) (P : ℝ) : ℝ :=
  sSup (eulerSet u Z R P)

variable {u : ℝ → ℝ} {Z : ℝ → Prop} {R : ℝ → ℝ} {B P : ℝ}

/-- Moving `y` down while the current consumption `P − y` does not fall keeps the left side
below the right side (left side increasing, right side nonincreasing in `y`). -/
theorem eulerBelow_of_le (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' y y' : ℝ}
    (hy' : 0 ≤ y') (hyy : y' ≤ y) (hyB : y ≤ B) (hc : 0 < P - y) (hcc : P - y ≤ P' - y')
    (h : EulerBelow u Z R P y) : EulerBelow u Z R P' y' := by
  rcases h with h | h
  · exact Or.inl (hR.zero_anti y y' hy' hyy hyB h)
  · by_cases hz : Z y'
    · exact Or.inl hz
    · right
      have h1 : u (P' - y') ≤ u (P - y) :=
        hu.strictAnti.antitoneOn (mem_Ioi.2 hc) (mem_Ioi.2 (hc.trans_le hcc)) hcc
      exact h1.trans_lt (h.trans_le (hR.anti y y' hy' hyy hyB hz))

/-- `eulerSet` is bounded above by `P`. -/
theorem bddAbove_eulerSet : BddAbove (eulerSet u Z R P) :=
  ⟨P, fun _ hy => hy.2.1.le⟩

/-- The crossing point is nonnegative. -/
theorem eulerCross_nonneg : 0 ≤ eulerCross u Z R P :=
  Real.sSup_nonneg fun _ hy => hy.1

/-- The crossing point is at most the current resources `P`. -/
theorem eulerCross_le (hP : 0 ≤ P) : eulerCross u Z R P ≤ P :=
  Real.sSup_le (fun _ hy => hy.2.1.le) hP

/-- Every point of `eulerSet` lies below the crossing point. -/
theorem le_eulerCross_of_mem {y : ℝ} (hy : y ∈ eulerSet u Z R P) : y ≤ eulerCross u Z R P :=
  le_csSup bddAbove_eulerSet hy

/-- `eulerSet` is an initial segment: every `y ∈ [0, eulerCross)` belongs to it. -/
theorem mem_eulerSet_of_lt (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hPB : P ≤ B)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < eulerCross u Z R P) : y ∈ eulerSet u Z R P := by
  have hne : (eulerSet u Z R P).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : eulerCross u Z R P = 0 := by rw [eulerCross, hne, Real.sSup_empty]
    linarith
  obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne hy
  refine ⟨hy0, hyz.trans hz.2.1, ?_⟩
  exact eulerBelow_of_le hu hR hy0 hyz.le (hz.2.1.le.trans hPB) (by linarith [hz.2.1])
    (by linarith) hz.2.2

/-- If the left side is not below the right side at `z ∈ [0, P)`, the crossing point is at
most `z`. -/
theorem eulerCross_le_of_not_below (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R)
    (hPB : P ≤ B) {z : ℝ} (hz0 : 0 ≤ z) (hnb : ¬ EulerBelow u Z R P z) :
    eulerCross u Z R P ≤ z := by
  refine Real.sSup_le (fun y hy => ?_) hz0
  by_contra hzy
  have hzy := lt_of_not_ge hzy
  exact hnb (eulerBelow_of_le hu hR hz0 hzy.le (hy.2.1.le.trans hPB) (by linarith [hy.2.1])
    (by linarith) hy.2.2)

/-- If every `y ∈ [0, z)` lies in `eulerSet`, then `z` is at most the crossing point. -/
theorem le_eulerCross_of_forall {z : ℝ} (h : ∀ y, 0 ≤ y → y < z → y ∈ eulerSet u Z R P) :
    z ≤ eulerCross u Z R P := by
  refine le_of_forall_lt fun c hc => ?_
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact hc0.trans_le eulerCross_nonneg
  · have hy : (c + z) / 2 ∈ eulerSet u Z R P := h _ (by linarith) (by linarith)
    exact (show c < (c + z) / 2 by linarith).trans_le (le_eulerCross_of_mem hy)

/-- More current resources raise the crossing point (`k ↦ (Th)(k)` is nondecreasing). -/
theorem eulerCross_mono (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPP : P ≤ P') (hPB : P' ≤ B) (h0 : (eulerSet u Z R P).Nonempty) :
    eulerCross u Z R P ≤ eulerCross u Z R P' := by
  refine csSup_le_csSup bddAbove_eulerSet h0 fun y hy => ⟨hy.1, hy.2.1.trans_le hPP, ?_⟩
  exact eulerBelow_of_le hu hR hy.1 le_rfl ((hy.2.1.trans_le hPP).le.trans hPB)
    (by linarith [hy.2.1]) (by linarith) hy.2.2

/-- An increase `P' − P` of current resources raises the crossing point by at most `P' − P`
(`ψ − Th` is nondecreasing). -/
theorem eulerCross_le_add_sub (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPP : P ≤ P') (hPB : P' ≤ B) :
    eulerCross u Z R P' ≤ eulerCross u Z R P + (P' - P) := by
  have h0 : 0 ≤ eulerCross u Z R P := eulerCross_nonneg
  refine Real.sSup_le (fun y hy => ?_) (by linarith)
  rcases le_or_gt y (P' - P) with hyl | hyl
  · linarith
  · have hmem : y - (P' - P) ∈ eulerSet u Z R P := by
      refine ⟨by linarith, by linarith [hy.2.1], ?_⟩
      exact eulerBelow_of_le hu hR (by linarith) (by linarith) (hy.2.1.le.trans hPB)
        (by linarith [hy.2.1]) (by linarith) hy.2.2
    linarith [le_eulerCross_of_mem hmem]

/-- A larger right side raises the crossing point (the monotonicity of `T`, Exercise 18.7). -/
theorem eulerCross_mono_rhs {Z' : ℝ → Prop} {R' : ℝ → ℝ}
    (hZ : ∀ y, 0 ≤ y → y < P → Z y → Z' y)
    (hRR : ∀ y, 0 ≤ y → y < P → ¬ Z y → ¬ Z' y → R y ≤ R' y)
    (h0 : (eulerSet u Z R P).Nonempty) :
    eulerCross u Z R P ≤ eulerCross u Z' R' P := by
  refine csSup_le_csSup bddAbove_eulerSet h0 fun y hy => ⟨hy.1, hy.2.1, ?_⟩
  rcases hy.2.2 with h | h
  · exact Or.inl (hZ y hy.1 hy.2.1 h)
  · by_cases hz' : Z' y
    · exact Or.inl hz'
    · by_cases hz : Z y
      · exact Or.inl (hZ y hy.1 hy.2.1 hz)
      · exact Or.inr (h.trans_le (hRR y hy.1 hy.2.1 hz hz'))

/-- **The crossing point solves the Euler equation, or there is no interior solution.** If the
left side lies below the right side at `y = 0`, then either the crossing point `y*` is `< P`,
the next-period consumption at `y*` is positive (`¬ Z y*`) and `u (P − y*) = R y*`; or `y* = P`
and the right side is `+∞` on all of `[0, P)`. -/
theorem eulerCross_spec (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hP : 0 < P)
    (hPB : P ≤ B) (h0 : EulerBelow u Z R P 0) :
    (eulerCross u Z R P < P ∧ ¬ Z (eulerCross u Z R P) ∧
      u (P - eulerCross u Z R P) = R (eulerCross u Z R P)) ∨
    (eulerCross u Z R P = P ∧ ∀ y, 0 ≤ y → y < P → Z y) := by
  set y := eulerCross u Z R P with hydef
  have hne : (eulerSet u Z R P).Nonempty := ⟨0, le_rfl, hP, h0⟩
  have hy0 : 0 ≤ y := eulerCross_nonneg
  have hyP : y ≤ P := eulerCross_le hP.le
  rcases hyP.lt_or_eq with hlt | heq
  · left
    have hyB : y ∈ Icc 0 B := ⟨hy0, hlt.le.trans hPB⟩
    -- a point `y'` slightly above `y` that would lie in `eulerSet`
    have key : ∀ δ > 0, ∃ y', y < y' ∧ y' < P ∧ y' ∈ Metric.ball y δ ∩ Icc 0 B ∧
        P - (y + P) / 2 ≤ P - y' := by
      intro δ hδ
      refine ⟨y + min (δ / 2) ((P - y) / 2), ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · have : 0 < min (δ / 2) ((P - y) / 2) := lt_min (by linarith) (by linarith)
        linarith
      · linarith [min_le_right (δ / 2) ((P - y) / 2)]
      · rw [Metric.mem_ball, Real.dist_eq]
        have h1 : 0 < min (δ / 2) ((P - y) / 2) := lt_min (by linarith) (by linarith)
        rw [abs_of_pos (by linarith)]
        linarith [min_le_left (δ / 2) ((P - y) / 2)]
      · have : 0 < min (δ / 2) ((P - y) / 2) := lt_min (by linarith) (by linarith)
        linarith
      · linarith [min_le_right (δ / 2) ((P - y) / 2)]
      · linarith [min_le_right (δ / 2) ((P - y) / 2)]
    have hZ : ¬ Z y := by
      intro hz
      have hev := hR.blowup y hyB hz (u (P - (y + P) / 2))
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      obtain ⟨y', hyy', hy'P, hy'm, hc⟩ := key δ hδ
      have hmem : y' ∈ eulerSet u Z R P := by
        refine ⟨by linarith, hy'P, ?_⟩
        rcases hball hy'm with h | h
        · exact Or.inl h
        · right
          exact (hu.strictAnti.antitoneOn (mem_Ioi.2 (by linarith))
            (mem_Ioi.2 (by linarith)) hc).trans_lt h
      linarith [le_eulerCross_of_mem hmem]
    refine ⟨hlt, hZ, ?_⟩
    have hcont := (hR.cont y hyB hZ).2
    have hcu : ContinuousWithinAt (fun z => u (P - z)) (Icc 0 B) y :=
      ((hu.cont.continuousAt (Ioi_mem_nhds (by linarith : (0 : ℝ) < P - y))).comp
        (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
    rcases lt_trichotomy (u (P - y)) (R y) with hl | he | hg
    · exfalso
      have hev : ∀ᶠ z in 𝓝[Icc 0 B] y, u (P - z) < R z := hcu.eventually_lt hcont hl
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      obtain ⟨y', hyy', hy'P, hy'm, -⟩ := key δ hδ
      have hmem : y' ∈ eulerSet u Z R P := ⟨by linarith, hy'P, Or.inr (hball hy'm)⟩
      linarith [le_eulerCross_of_mem hmem]
    · exact he
    · exfalso
      have hev : ∀ᶠ z in 𝓝[Icc 0 B] y, ¬ Z z ∧ R z < u (P - z) :=
        (hR.cont y hyB hZ).1.and (hcont.eventually_lt hcu hg)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (show y - δ < y by linarith)
      have hzy : z ≤ y := le_eulerCross_of_mem hz
      have hzm : z ∈ Metric.ball y δ ∩ Icc 0 B := by
        refine ⟨?_, hz.1, hz.2.1.le.trans hPB⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      obtain ⟨hnz, hlt'⟩ := hball hzm
      rcases hz.2.2 with h | h
      · exact hnz h
      · linarith
  · right
    refine ⟨heq, fun y0 hy00 hy0P => ?_⟩
    by_contra hnz
    obtain ⟨ε, hε, hεu⟩ : ∃ ε > 0, ∀ c, 0 < c → c < ε → R y0 < u c := by
      have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), R y0 < u c := hu.inada.eventually_gt_atTop (R y0)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      refine ⟨ε, hε, fun c hc0 hcε => hball ⟨?_, hc0⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc0]
      exact hcε
    set y1 := max y0 (P - ε / 2)
    have hy1P : y1 < P := max_lt hy0P (by linarith)
    have hy01 : y0 ≤ y1 := le_max_left _ _
    have hnz1 : ¬ Z y1 := fun h =>
      hnz (hR.zero_anti y1 y0 hy00 hy01 (hy1P.le.trans hPB) h)
    have hnb : ¬ EulerBelow u Z R P y1 := by
      rintro (h | h)
      · exact hnz1 h
      · have h1 : R y1 ≤ R y0 := hR.anti y1 y0 hy00 hy01 (hy1P.le.trans hPB) hnz
        have h2 : R y0 < u (P - y1) :=
          hεu _ (by linarith) (by linarith [le_max_right y0 (P - ε / 2)])
        linarith
    have := eulerCross_le_of_not_below hu hR hPB (hy00.trans hy01) hnb
    linarith

/-- If the left side is not below the right side at `0`, then `eulerSet` is empty and the
crossing point is `0`. -/
theorem eulerCross_eq_zero_of_not_below (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R)
    (hPB : P ≤ B) (h0 : ¬ EulerBelow u Z R P 0) : eulerCross u Z R P = 0 := by
  have hempty : eulerSet u Z R P = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y hy => h0 ?_
    exact eulerBelow_of_le hu hR le_rfl hy.1 (hy.2.1.le.trans hPB) (by linarith [hy.2.1])
      (by linarith [hy.1]) hy.2.2
  rw [eulerCross, hempty, Real.sSup_empty]

/-- **Kuhn–Tucker form of `eulerCross_spec`** (no interiority assumption at `0`). Exactly one of:
an interior solution of the Euler equation; a corner with zero consumption (`y* = P`, the right
side `+∞` on `[0, P)`); or a corner with zero saving (`y* = 0`, with `R 0 ≤ u P`: the Euler
equation holds as the inequality of a Kuhn–Tucker condition). -/
theorem eulerCross_spec_KT (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hP : 0 < P)
    (hPB : P ≤ B) :
    (eulerCross u Z R P < P ∧ ¬ Z (eulerCross u Z R P) ∧
      u (P - eulerCross u Z R P) = R (eulerCross u Z R P)) ∨
    (eulerCross u Z R P = P ∧ ∀ y, 0 ≤ y → y < P → Z y) ∨
    (eulerCross u Z R P = 0 ∧ ¬ Z 0 ∧ R 0 ≤ u P) := by
  by_cases h0 : EulerBelow u Z R P 0
  · rcases eulerCross_spec hu hR hP hPB h0 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨eulerCross_eq_zero_of_not_below hu hR hPB h0, fun h => h0 (Or.inl h),
      ?_⟩)
    by_contra hlt
    exact h0 (Or.inr (by simpa using lt_of_not_ge hlt))

/-- `eulerCross_mono` without the nonemptiness assumption. -/
theorem eulerCross_mono' (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPP : P ≤ P') (hPB : P' ≤ B) : eulerCross u Z R P ≤ eulerCross u Z R P' := by
  rcases (eulerSet u Z R P).eq_empty_or_nonempty with h | h
  · rw [eulerCross, h, Real.sSup_empty]; exact eulerCross_nonneg
  · exact eulerCross_mono hu hR hPP hPB h

/-- `eulerCross_mono_rhs` without the nonemptiness assumption. -/
theorem eulerCross_mono_rhs' {Z' : ℝ → Prop} {R' : ℝ → ℝ}
    (hZ : ∀ y, 0 ≤ y → y < P → Z y → Z' y)
    (hRR : ∀ y, 0 ≤ y → y < P → ¬ Z y → ¬ Z' y → R y ≤ R' y) :
    eulerCross u Z R P ≤ eulerCross u Z' R' P := by
  rcases (eulerSet u Z R P).eq_empty_or_nonempty with h | h
  · rw [eulerCross, h, Real.sSup_empty]; exact eulerCross_nonneg
  · exact eulerCross_mono_rhs hZ hRR h

/-- The crossing point is `1`-Lipschitz in the current resources `P` (for a fixed right side). -/
theorem abs_eulerCross_sub_le (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPB : P ≤ B) (hP'B : P' ≤ B) :
    |eulerCross u Z R P' - eulerCross u Z R P| ≤ |P' - P| := by
  rcases le_total P P' with h | h
  · have h1 := eulerCross_mono' hu hR h hP'B
    have h2 := eulerCross_le_add_sub hu hR h hP'B
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have h1 := eulerCross_mono' hu hR h hPB
    have h2 := eulerCross_le_add_sub hu hR h hPB
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- **Uniqueness.** An interior solution `y ∈ [0, P)` of the Euler equation with positive
next-period consumption is the crossing point. -/
theorem eulerCross_unique (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hPB : P ≤ B)
    {y : ℝ} (hy0 : 0 ≤ y) (hyP : y < P) (hZ : ¬ Z y) (heq : u (P - y) = R y) :
    eulerCross u Z R P = y := by
  refine le_antisymm (eulerCross_le_of_not_below hu hR hPB hy0 ?_) ?_
  · rintro (h | h)
    · exact hZ h
    · exact h.ne heq
  · refine le_eulerCross_of_forall fun z hz0 hzy => ⟨hz0, hzy.trans hyP, ?_⟩
    by_cases hz : Z z
    · exact Or.inl hz
    · right
      have h1 : u (P - z) < u (P - y) :=
        hu.strictAnti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
      exact h1.trans_le (heq.trans_le (hR.anti y z hz0 hzy.le (hyP.le.trans hPB) hz))

/-- Pointwise convergence of a family of right sides `(Zs a, Rs a)` to `(Z, R)` at the point
`y`, in the extended-real sense: if `Z y` (the limit is `+∞`) the right sides eventually exceed
every bound, and otherwise they are eventually finite and converge to `R y`. -/
def RHSConvergesAt {α : Type*} (l : Filter α) (Zs : α → ℝ → Prop) (Rs : α → ℝ → ℝ)
    (Z : ℝ → Prop) (R : ℝ → ℝ) (y : ℝ) : Prop :=
  (Z y → ∀ M : ℝ, ∀ᶠ a in l, Zs a y ∨ M < Rs a y) ∧
    (¬ Z y → (∀ᶠ a in l, ¬ Zs a y) ∧ Tendsto (fun a => Rs a y) l (𝓝 (R y)))

/-- **Pointwise continuity of the crossing point** (the pointwise step of Exercise 18.6). If the
right sides `(Zs a, Rs a)` converge to `(Z, R)` at every `y ∈ [0, P)` and each of them lies
above the left side at `0`, then the crossing points converge. -/
theorem eventually_abs_eulerCross_sub_le {α : Type*} {l : Filter α} {Zs : α → ℝ → Prop}
    {Rs : α → ℝ → ℝ} (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R)
    (hRs : ∀ a, IsEulerRHS B (Zs a) (Rs a)) (hP : 0 < P) (hPB : P ≤ B)
    (hconv : ∀ y, 0 ≤ y → y < P → RHSConvergesAt l Zs Rs Z R y) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a in l, |eulerCross u (Zs a) (Rs a) P - eulerCross u Z R P| ≤ η := by
  set y := eulerCross u Z R P
  have hy0 : 0 ≤ y := eulerCross_nonneg
  have hyP : y ≤ P := eulerCross_le hP.le
  -- lower bound
  have hlow : ∀ᶠ a in l, y - η ≤ eulerCross u (Zs a) (Rs a) P := by
    rcases le_or_gt y η with hyη | hyη
    · refine Eventually.of_forall fun a => ?_
      have : 0 ≤ eulerCross u (Zs a) (Rs a) P := eulerCross_nonneg
      linarith
    · have hz : y - η ∈ eulerSet u Z R P :=
        mem_eulerSet_of_lt hu hR hPB (by linarith) (by linarith)
      have hzP : y - η < P := hz.2.1
      have hc := hconv (y - η) hz.1 hzP
      have hev : ∀ᶠ a in l, EulerBelow u (Zs a) (Rs a) P (y - η) := by
        rcases hz.2.2 with h | h
        · exact (hc.1 h (u (P - (y - η)))).mono fun a ha => ha
        · by_cases hZz : Z (y - η)
          · exact (hc.1 hZz (u (P - (y - η)))).mono fun a ha => ha
          · exact ((hc.2 hZz).2.eventually_const_lt h).mono fun a ha => Or.inr ha
      exact hev.mono fun a ha => le_eulerCross_of_mem ⟨hz.1, hzP, ha⟩
  -- upper bound
  have hup : ∀ᶠ a in l, eulerCross u (Zs a) (Rs a) P ≤ y + η := by
    rcases le_or_gt P (y + η) with hPη | hPη
    · exact Eventually.of_forall fun a => (eulerCross_le hP.le).trans hPη
    · have hz'nb : ¬ EulerBelow u Z R P (y + η / 2) := by
        intro h
        have := le_eulerCross_of_mem (show y + η / 2 ∈ eulerSet u Z R P from
          ⟨by linarith, by linarith, h⟩)
        linarith
      have hnZ' : ¬ Z (y + η / 2) := fun h => hz'nb (Or.inl h)
      have hR' : R (y + η / 2) ≤ u (P - (y + η / 2)) := not_lt.1 fun h => hz'nb (Or.inr h)
      have hnZ : ¬ Z (y + η) := fun h =>
        hnZ' (hR.zero_anti _ _ (by linarith) (by linarith) (hPη.le.trans hPB) h)
      have hRz : R (y + η) < u (P - (y + η)) := by
        have h1 := hR.anti (y + η) (y + η / 2) (by linarith) (by linarith) (hPη.le.trans hPB)
          hnZ'
        have h2 : u (P - (y + η / 2)) < u (P - (y + η)) :=
          hu.strictAnti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
        linarith
      have hc := (hconv (y + η) (by linarith) hPη).2 hnZ
      have hev : ∀ᶠ a in l, ¬ EulerBelow u (Zs a) (Rs a) P (y + η) :=
        (hc.1.and (hc.2.eventually_lt_const hRz)).mono fun a ha => by
          rintro (h | h)
          · exact ha.1 h
          · linarith [ha.2]
      exact hev.mono fun a ha =>
        eulerCross_le_of_not_below hu (hRs a) hPB (by linarith) ha
  filter_upwards [hlow, hup] with a h1 h2
  rw [abs_le]
  constructor <;> linarith

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A global approach based on first-order conditions: set-up (SLP §18.3, pp. 554–558)

The one-sector growth model with a flat tax `θ` on capital income whose proceeds are thrown
away. After-tax income is `ψ(k) = f(k) − θ k f′(k)` and a (continuous) competitive equilibrium is
a savings function `g` with (§18.3 (1), p. 554)
  `U′[ψ(k) − g(k)] = β(1 − θ) f′[g(k)] U′{ψ[g(k)] − g[g(k)]}`  for `k ∈ K = [0, k̄]`.

* `assumption_18_2_contradiction` (**Correction**, p. 554): Assumption 18.1b (U twice
  continuously differentiable on `ℝ₊ = [0, ∞)`) and the Inada condition of Assumption 18.2
  (`U′(c) → ∞` as `c → 0`) are inconsistent: a `C²` (indeed `C¹`) function on `[0, ∞)` has a
  finite one-sided derivative at `0` which is the limit of `U′(c)`.
* `GlobalModel`: Assumptions 18.1 and 18.2 in the corrected reading — `U` and `f` are continuous
  on `[0, ∞)` and `C²` on `(0, ∞)`; `f′(0) = A` is the (finite) limit of `f′(k)` as `k → 0`
  (the first half of Assumption 18.2) and `U′(c) → ∞` as `c → 0⁺` (the second half).
* Derived facts (pp. 547–548, 555): `f′ > 0` and strictly decreasing, `U′` is a marginal utility
  in the sense of `IsMarginalUtility`, `ψ` is continuous and strictly increasing with
  `ψ(0) = f(0) > 0` and `ψ(k̄) = k̄`, there is a unique `k* ∈ (0, k̄)` with `β(1 − θ)f′(k*) = 1`
  (`exists_kstar`, `kstar_unique`), and `ψ(b) − ψ(a) > b − a` for `0 ≤ a < b ≤ k*`
  (`sub_lt_psi_sub`, the book's "`ψ′ > 1/β > 1` on `[0, k*]`").
* `F` (p. 555): the continuous `h` on `K` with (2) `0 ≤ h ≤ ψ`, (3) `h` and `ψ − h`
  nondecreasing, (4) `h(k) ≥ k` for `k < k*`, (5) `h(k*) = k*`, (6) `h(k) ≤ k` for `k > k*`.
  `F_nonempty`, `F_isClosed`, `F_isBounded`, `F_convex` (p. 556).
* **Proposition 18.5** (`prop_18_5`, p. 557): `F` is equicontinuous.
* The least element `h_` of `F` (`isLeast_low`, p. 558) and the greatest element `ū`
  (`isGreatest_up`), with the explicit formula `up_eq_of_le_kstar`, `up_eq_of_kstar_le`.
* `not_isInF_hbar`, `hbar_not_mem_F` (**Correction**, p. 558): the book's maximal element `h̄`
  is not in `F`.

**Correction (Assumption 18.2 vs 18.1b, p. 554).** As printed the two assumptions contradict
each other (`assumption_18_2_contradiction`); 18.1b and 18.1d are read as "continuous on
`[0, ∞)`, `C²` on `(0, ∞)`", which is the reading under which the Inada condition makes sense and
the first half of 18.2 (`f′(0) < ∞`) is not redundant.

**Correction (p. 555, minor).** "`ψ′(k) > (1 − θ) f′(k)` for all `k ∈ K`" fails at `k = 0`; only
`≥` holds. Nothing here uses derivatives of `ψ`: `psi_sub_gt` is the difference-quotient
inequality `ψ(b) − ψ(a) > (1 − θ)(b − a) f′(b)` for `0 ≤ a < b`, proved from strict concavity of
`f` alone.

**Correction (Proposition 18.5's proof, p. 557).** The proof bounds `|ψ(k′) − ψ(k)|` by
`A |k′ − k|` with `A = f′(0)`; this is false (counterexample `prop_18_5_bound_counterexample` in
`GlobalExamples`), because `ψ′ = (1 − θ)f′ − θ k f″` contains the term `−θ k f″ ≥ 0`, which
`f′(0)` does not control. The proposition is true: `prop_18_5` uses only uniform continuity of
`ψ` on the compact `K` together with `|h(k′) − h(k)| ≤ |ψ(k′) − ψ(k)|`.

**Correction (p. 558, the maximal element).** The book's
`h̄(k) = min{ψ(k), k*}` (`k ≤ k*`), `h̄(k) = min{k, ψ(k) − [ψ(k*) − k*]}` (`k > k*`) is an upper
bound for `F` but is not in `F`: `ψ − h̄` is not nondecreasing (`not_isInF_hbar`). The greatest
element of `F` is `ū(k) = ψ(k) − max_{0 ≤ j ≤ k} [ψ(j) − min{ψ(j), max(j, k*)}]`, which equals
`min{ψ(k), k*}` for `k ≤ k*` (`up_eq_of_le_kstar`) and `ψ(k) − max_{k* ≤ j ≤ k} [ψ(j) − j]` for
`k ≥ k*` (`up_eq_of_kstar_le`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

/-- **Correction to Assumptions 18.1b and 18.2** (p. 554). If `U` is twice continuously
differentiable on `[0, ∞)` (Assumption 18.1b as printed) then its derivative cannot tend to `∞`
at `0` (the Inada condition of Assumption 18.2). -/
theorem assumption_18_2_contradiction {U U' : ℝ → ℝ} (hU : ContDiffOn ℝ 2 U (Ici 0))
    (hU' : ∀ c, 0 < c → HasDerivAt U (U' c) c) : ¬ Tendsto U' (𝓝[>] 0) atTop := by
  have hc : ContinuousOn (derivWithin U (Ici 0)) (Ici 0) :=
    hU.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
  have h1 : Tendsto (derivWithin U (Ici 0)) (𝓝[>] 0) (𝓝 (derivWithin U (Ici 0) 0)) :=
    (hc 0 (mem_Ici.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : derivWithin U (Ici 0) =ᶠ[𝓝[>] 0] U' := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (hU' c hc).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 0 c (mem_Ici.2 (mem_Ioi.1 hc).le))
  exact not_tendsto_atTop_of_tendsto_nhds (h1.congr' h2)

/-- **Assumptions 18.1 and 18.2** (pp. 547–548, 554), in the corrected reading of
`assumption_18_2_contradiction`. `U'` and `f'` are the derivatives of `U` and `f` on `(0, ∞)`;
`f' 0` is the value `A = f′(0)` of Assumption 18.2, the limit of `f′(k)` as `k → 0`
(`f'_contAt_zero`).
* (a) `0 < β < 1`;
* (b) `U` continuous on `[0, ∞)`, `C²` on `(0, ∞)`, strictly increasing and strictly concave;
* (c) `0 < θ < 1`;
* (d) `f` continuous on `[0, ∞)`, `C²` on `(0, ∞)`, strictly increasing and strictly concave,
  `f(0) > 0` and `f′(0) > 1/[β(1 − θ)]`;
* (e) `ψ(k) − k > 0` on `(0, k̄)` and `< 0` on `(k̄, ∞)`, where `ψ(k) = f(k) − θ k f′(k)`;
* (18.2) `f′(0) = lim_{k → 0} f′(k)` is finite, and `U′(c) → ∞` as `c → 0⁺`. -/
structure GlobalModel where
  β : ℝ
  θ : ℝ
  U : ℝ → ℝ
  U' : ℝ → ℝ
  f : ℝ → ℝ
  f' : ℝ → ℝ
  kbar : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_contDiff : ContDiffOn ℝ 2 U (Ioi 0)
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  U_deriv : ∀ c, 0 < c → HasDerivAt U (U' c) c
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  f_cont : ContinuousOn f (Ici 0)
  f_contDiff : ContDiffOn ℝ 2 f (Ioi 0)
  f_strictMono : StrictMonoOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_deriv : ∀ k, 0 < k → HasDerivAt f (f' k) k
  f_zero_pos : 0 < f 0
  f'_zero : 1 / (β * (1 - θ)) < f' 0
  kbar_pos : 0 < kbar
  psi_gt : ∀ k, 0 < k → k < kbar → k < f k - θ * k * f' k
  psi_lt : ∀ k, kbar < k → f k - θ * k * f' k < k
  f'_contAt_zero : ContinuousWithinAt f' (Ici 0) 0
  U'_inada : Tendsto U' (𝓝[>] 0) atTop

namespace GlobalModel

variable (M : GlobalModel)

/-- After-tax income `ψ(k) = f(k) − θ k f′(k)` (p. 547). -/
noncomputable def psi (k : ℝ) : ℝ := M.f k - M.θ * k * M.f' k

/-- `f′` is the derivative of `f` on `(0, ∞)`. -/
theorem deriv_f_eq {k : ℝ} (hk : 0 < k) : deriv M.f k = M.f' k := (M.f_deriv k hk).deriv

/-- `U′` is the derivative of `U` on `(0, ∞)`. -/
theorem deriv_U_eq {c : ℝ} (hc : 0 < c) : deriv M.U c = M.U' c := (M.U_deriv c hc).deriv

/-- `f′` is strictly decreasing on `(0, ∞)` (strict concavity). -/
theorem f'_strictAntiOn_Ioi : StrictAntiOn M.f' (Ioi 0) := by
  have h := (M.f_strictConcave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    (fun x hx => (M.f_deriv x hx).differentiableAt)
  intro a ha b hb hab
  have := h ha hb hab
  rwa [M.deriv_f_eq ha, M.deriv_f_eq hb] at this

/-- `f′` is continuous on `(0, ∞)` (`f` is `C²` there). -/
theorem f'_continuousOn_Ioi : ContinuousOn M.f' (Ioi 0) :=
  (M.f_contDiff.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).congr
    fun _ hk => (M.deriv_f_eq hk).symm

/-- `f′` is continuous on `[0, ∞)`. -/
theorem f'_continuousOn : ContinuousOn M.f' (Ici 0) := by
  intro k hk
  rcases (mem_Ici.1 hk).eq_or_lt with h | h
  · subst h
    exact M.f'_contAt_zero
  · exact (M.f'_continuousOn_Ioi.continuousAt (Ioi_mem_nhds h)).continuousWithinAt

/-- `f′` is strictly decreasing on `[0, ∞)`. -/
theorem f'_strictAntiOn : StrictAntiOn M.f' (Ici 0) := by
  intro a ha b hb hab
  rcases (mem_Ici.1 ha).eq_or_lt with h | h
  · subst h
    have hb0 : 0 < b := hab
    have hlim : Tendsto M.f' (𝓝[>] 0) (𝓝 (M.f' 0)) :=
      M.f'_contAt_zero.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hge : M.f' (b / 2) ≤ M.f' 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < b / 2)] with x hx
      exact (M.f'_strictAntiOn_Ioi hx.1 (by simp; linarith) hx.2).le
    exact (M.f'_strictAntiOn_Ioi (by simp; linarith) hb0 (by linarith)).trans_le hge
  · exact M.f'_strictAntiOn_Ioi h (lt_trans h hab) hab

/-- `f′ > 0` on `[0, ∞)` (`f` strictly increasing and strictly concave). -/
theorem f'_pos {k : ℝ} (hk : 0 ≤ k) : 0 < M.f' k := by
  have h1 : 0 < M.f' (k + 1) := by
    have hs := M.f_strictConcave.slope_lt_of_hasDerivAt (x := k + 1) (y := k + 2)
      (by simp; linarith) (by simp; linarith) (by linarith) (M.f_deriv _ (by linarith))
    have hm := M.f_strictMono (show k + 1 ∈ Ici 0 by simp; linarith)
      (show k + 2 ∈ Ici 0 by simp; linarith) (by linarith : k + 1 < k + 2)
    rw [slope_def_field] at hs
    have : 0 < (M.f (k + 2) - M.f (k + 1)) / (k + 2 - (k + 1)) :=
      div_pos (by linarith) (by linarith)
    linarith
  exact h1.trans (M.f'_strictAntiOn hk (show k + 1 ∈ Ici 0 by simp; linarith) (by linarith))

/-- `U′ > 0` on `(0, ∞)`. -/
theorem U'_pos {c : ℝ} (hc : 0 < c) : 0 < M.U' c := by
  have hs := M.U_strictConcave.slope_lt_of_hasDerivAt (x := c) (y := c + 1)
    (by simp; linarith) (by simp; linarith) (by linarith) (M.U_deriv _ hc)
  have hm := M.U_strictMono (show c ∈ Ici 0 by simp; linarith)
    (show c + 1 ∈ Ici 0 by simp; linarith) (by linarith : c < c + 1)
  rw [slope_def_field] at hs
  have : 0 < (M.U (c + 1) - M.U c) / (c + 1 - c) := div_pos (by linarith) (by linarith)
  linarith

/-- `U′` is strictly decreasing on `(0, ∞)`. -/
theorem U'_strictAntiOn : StrictAntiOn M.U' (Ioi 0) := by
  have h := (M.U_strictConcave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    (fun x hx => (M.U_deriv x hx).differentiableAt)
  intro a ha b hb hab
  have := h ha hb hab
  rwa [M.deriv_U_eq ha, M.deriv_U_eq hb] at this

/-- `U′` is continuous on `(0, ∞)`. -/
theorem U'_continuousOn : ContinuousOn M.U' (Ioi 0) :=
  (M.U_contDiff.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).congr
    fun _ hc => (M.deriv_U_eq hc).symm

/-- `U′` is a marginal utility in the sense of `IsMarginalUtility` (Assumptions 18.1b, 18.2). -/
theorem isMarginalUtility : IsMarginalUtility M.U' :=
  ⟨fun _ hc => M.U'_pos hc, M.U'_strictAntiOn, M.U'_continuousOn, M.U'_inada⟩

/-- Strict concavity of `f`: `f′(b)(b − a) < f(b) − f(a)` for `0 ≤ a < b`. -/
theorem f'_mul_lt_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    M.f' b * (b - a) < M.f b - M.f a := by
  have hs := M.f_strictConcave.lt_slope_of_hasDerivAt (mem_Ici.2 ha)
    (mem_Ici.2 (ha.trans hab.le)) hab (M.f_deriv b (lt_of_le_of_lt ha hab))
  rw [slope_def_field, lt_div_iff₀ (by linarith)] at hs
  exact hs

/-- `k f′(k) < f(k)` for `k > 0`. -/
theorem mul_f'_lt_f {k : ℝ} (hk : 0 < k) : k * M.f' k < M.f k := by
  have := M.f'_mul_lt_sub le_rfl hk
  have := M.f_zero_pos
  nlinarith

/-- The difference-quotient form of "`ψ′ ≥ (1 − θ) f′`" (p. 555): for `0 ≤ a < b`,
`ψ(b) − ψ(a) > (1 − θ)(b − a) f′(b)`. -/
theorem psi_sub_gt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (1 - M.θ) * (b - a) * M.f' b < M.psi b - M.psi a := by
  have h1 := M.f'_mul_lt_sub ha hab
  have h2 : M.f' b < M.f' a := M.f'_strictAntiOn (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab
  have h3 : a * M.f' b ≤ a * M.f' a := mul_le_mul_of_nonneg_left h2.le ha
  have h4 : 0 ≤ M.θ * (a * M.f' a - a * M.f' b) :=
    mul_nonneg M.θ_pos.le (sub_nonneg.2 h3)
  have : M.psi b - M.psi a - (1 - M.θ) * (b - a) * M.f' b =
      (M.f b - M.f a - M.f' b * (b - a)) + M.θ * (a * M.f' a - a * M.f' b) := by
    unfold psi; ring
  linarith

/-- `ψ` is strictly increasing on `[0, ∞)` (p. 555). -/
theorem psi_strictMonoOn : StrictMonoOn M.psi (Ici 0) := by
  intro a ha b hb hab
  have h := M.psi_sub_gt (mem_Ici.1 ha) hab
  have : 0 < (1 - M.θ) * (b - a) * M.f' b :=
    mul_pos (mul_pos (by linarith [M.θ_lt_one]) (by linarith)) (M.f'_pos (mem_Ici.1 hb))
  linarith

/-- `ψ` is continuous on `[0, ∞)`. -/
theorem psi_continuousOn : ContinuousOn M.psi (Ici 0) :=
  M.f_cont.sub ((continuousOn_const.mul continuousOn_id).mul M.f'_continuousOn)

/-- `ψ(0) = f(0)`. -/
theorem psi_zero : M.psi 0 = M.f 0 := by simp [psi]

/-- `ψ > 0` on `[0, ∞)`. -/
theorem psi_pos {k : ℝ} (hk : 0 ≤ k) : 0 < M.psi k := by
  rcases hk.eq_or_lt with h | h
  · subst h; rw [psi_zero]; exact M.f_zero_pos
  · have := M.psi_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk) h
    rw [psi_zero] at this
    linarith [M.f_zero_pos]

/-- `k < ψ(k)` on `[0, k̄)` (Assumption 18.1e). -/
theorem lt_psi {k : ℝ} (h0 : 0 ≤ k) (hk : k < M.kbar) : k < M.psi k := by
  rcases h0.eq_or_lt with h | h
  · subst h; exact M.psi_pos le_rfl
  · exact M.psi_gt k h hk

/-- `ψ(k̄) = k̄` (continuity and Assumption 18.1e). -/
theorem psi_kbar : M.psi M.kbar = M.kbar := by
  have hc : ContinuousAt (fun k => M.psi k - k) M.kbar :=
    ((M.psi_continuousOn.continuousAt (Ici_mem_nhds M.kbar_pos)).sub continuousAt_id)
  have h1 : M.psi M.kbar - M.kbar ≤ 0 := by
    refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi M.kbar))) ?_
    filter_upwards [self_mem_nhdsWithin] with k (hk : M.kbar < k)
    linarith [M.psi_lt k hk, show M.psi k = M.f k - M.θ * k * M.f' k from rfl]
  have h2 : 0 ≤ M.psi M.kbar - M.kbar := by
    refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio M.kbar))) ?_
    filter_upwards [Ioo_mem_nhdsLT M.kbar_pos] with k hk
    linarith [M.lt_psi hk.1.le hk.2]
  linarith

/-- `ψ` maps `[0, k̄]` into `(0, k̄]` (p. 548). -/
theorem psi_le_kbar {k : ℝ} (hk : k ∈ Icc 0 M.kbar) : M.psi k ≤ M.kbar := by
  rcases hk.2.eq_or_lt with h | h
  · rw [h, psi_kbar]
  · have := M.psi_strictMonoOn (mem_Ici.2 hk.1) (mem_Ici.2 M.kbar_pos.le) h
    rw [psi_kbar] at this
    exact this.le

/-- `(1 − θ) f′(k̄) ≤ 1` (from Assumption 18.1e and `k f′(k) < f(k)`). -/
theorem one_sub_mul_f'_kbar_le : (1 - M.θ) * M.f' M.kbar ≤ 1 := by
  have hc : ContinuousAt (fun k => (1 - M.θ) * M.f' k) M.kbar :=
    continuousAt_const.mul (M.f'_continuousOn_Ioi.continuousAt (Ioi_mem_nhds M.kbar_pos))
  refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi M.kbar))) ?_
  filter_upwards [self_mem_nhdsWithin] with k (hk : M.kbar < k)
  have hk0 : 0 < k := M.kbar_pos.trans hk
  have h1 := M.psi_lt k hk
  have h2 := M.mul_f'_lt_f hk0
  have h3 : (1 - M.θ) * M.f' k * k < 1 * k := by nlinarith [M.θ_pos]
  exact le_of_lt (lt_of_mul_lt_mul_right h3 hk0.le)

/-- `β(1 − θ) f′(k̄) < 1` (fact (F3) of the transcription). -/
theorem euler_kbar_lt_one : M.β * (1 - M.θ) * M.f' M.kbar < 1 := by
  have h := M.one_sub_mul_f'_kbar_le
  have : M.β * ((1 - M.θ) * M.f' M.kbar) ≤ M.β * 1 :=
    mul_le_mul_of_nonneg_left h M.β_pos.le
  nlinarith [M.β_lt_one]

/-- `β(1 − θ) f′(0) > 1` (Assumption 18.1d). -/
theorem one_lt_euler_zero : 1 < M.β * (1 - M.θ) * M.f' 0 := by
  have h := M.f'_zero
  have hpos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])
  rw [div_lt_iff₀ hpos] at h
  linarith

/-- **Existence of the steady state `k*`** (§18.2 (5), p. 549): some `k* ∈ (0, k̄)` has
`β(1 − θ) f′(k*) = 1`. -/
theorem exists_kstar : ∃ k ∈ Ioo 0 M.kbar, M.β * (1 - M.θ) * M.f' k = 1 := by
  have hc : ContinuousOn (fun k => M.β * (1 - M.θ) * M.f' k) (Icc 0 M.kbar) :=
    continuousOn_const.mul (M.f'_continuousOn.mono Icc_subset_Ici_self)
  obtain ⟨k, hk, hk1⟩ := intermediate_value_Icc' M.kbar_pos.le hc
    ⟨M.euler_kbar_lt_one.le, M.one_lt_euler_zero.le⟩
  refine ⟨k, ⟨?_, ?_⟩, hk1⟩
  · rcases hk.1.eq_or_lt with h | h
    · subst h; linarith [M.one_lt_euler_zero]
    · exact h
  · rcases hk.2.eq_or_lt with h | h
    · simp only at hk1; rw [h] at hk1; linarith [M.euler_kbar_lt_one]
    · exact h

/-- The steady state `k*`: `β(1 − θ) f′(k*) = 1` (§18.2 (5)). -/
noncomputable def kstar : ℝ := Classical.choose M.exists_kstar

/-- `0 < k*`. -/
theorem kstar_pos : 0 < M.kstar := (Classical.choose_spec M.exists_kstar).1.1

/-- `k* < k̄`. -/
theorem kstar_lt_kbar : M.kstar < M.kbar := (Classical.choose_spec M.exists_kstar).1.2

/-- `β(1 − θ) f′(k*) = 1`. -/
theorem euler_kstar : M.β * (1 - M.θ) * M.f' M.kstar = 1 :=
  (Classical.choose_spec M.exists_kstar).2

/-- `k*` lies in `K = [0, k̄]`. -/
theorem kstar_mem : M.kstar ∈ Icc 0 M.kbar := ⟨M.kstar_pos.le, M.kstar_lt_kbar.le⟩

/-- `β(1 − θ) f′(k) > 1` for `0 ≤ k < k*`. -/
theorem one_lt_euler {k : ℝ} (h0 : 0 ≤ k) (hk : k < M.kstar) :
    1 < M.β * (1 - M.θ) * M.f' k := by
  have h := M.f'_strictAntiOn (mem_Ici.2 h0) (mem_Ici.2 M.kstar_pos.le) hk
  have hpos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])
  have := mul_lt_mul_of_pos_left h hpos
  linarith [M.euler_kstar]

/-- `β(1 − θ) f′(k) < 1` for `k > k*`. -/
theorem euler_lt_one {k : ℝ} (hk : M.kstar < k) : M.β * (1 - M.θ) * M.f' k < 1 := by
  have h := M.f'_strictAntiOn (mem_Ici.2 M.kstar_pos.le) (mem_Ici.2 (M.kstar_pos.le.trans hk.le)) hk
  have hpos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])
  have := mul_lt_mul_of_pos_left h hpos
  linarith [M.euler_kstar]

/-- `k*` is the only `k ≥ 0` with `β(1 − θ) f′(k) = 1` (Proposition 18.1, p. 549). -/
theorem kstar_unique {k : ℝ} (h0 : 0 ≤ k) (hk : M.β * (1 - M.θ) * M.f' k = 1) : k = M.kstar := by
  rcases lt_trichotomy k M.kstar with h | h | h
  · linarith [M.one_lt_euler h0 h]
  · exact h
  · linarith [M.euler_lt_one h]

/-- "`ψ′ > 1/β > 1` on `[0, k*]`" (p. 555), as a difference quotient: `ψ(b) − ψ(a) > b − a`
for `0 ≤ a < b ≤ k*`. -/
theorem sub_lt_psi_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.kstar) :
    b - a < M.psi b - M.psi a := by
  have h1 := M.psi_sub_gt ha hab
  have h2 : 1 ≤ M.β * (1 - M.θ) * M.f' b := by
    rcases hb.lt_or_eq with h | h
    · exact (M.one_lt_euler (ha.trans hab.le) h).le
    · rw [h, M.euler_kstar]
  have hx : 1 < (1 - M.θ) * M.f' b := by
    have hpos : 0 < (1 - M.θ) * M.f' b :=
      mul_pos (by linarith [M.θ_lt_one]) (M.f'_pos (ha.trans hab.le))
    by_contra hle
    push Not at hle
    have : M.β * ((1 - M.θ) * M.f' b) ≤ M.β * 1 := mul_le_mul_of_nonneg_left hle M.β_pos.le
    nlinarith [M.β_lt_one]
  nlinarith

/-- `k < ψ(k)` for `0 ≤ k ≤ k*`; in particular `ψ(k*) > k*` (p. 555). -/
theorem lt_psi_of_le_kstar {k : ℝ} (h0 : 0 ≤ k) (hk : k ≤ M.kstar) : k < M.psi k :=
  M.lt_psi h0 (hk.trans_lt M.kstar_lt_kbar)

/-! ### The set `F` (p. 555) -/

/-- Conditions (2)–(6) of p. 555 on a function `g : ℝ → ℝ`, read on `K = [0, k̄]`, together
with continuity on `K`: (2) `0 ≤ g ≤ ψ`; (3) `g` and `ψ − g` nondecreasing; (4) `g(k) ≥ k` for
`k < k*`; (5) `g(k*) = k*`; (6) `g(k) ≤ k` for `k > k*`. -/
structure IsInF (g : ℝ → ℝ) : Prop where
  cont : ContinuousOn g (Icc 0 M.kbar)
  nonneg : ∀ k ∈ Icc 0 M.kbar, 0 ≤ g k
  le_psi : ∀ k ∈ Icc 0 M.kbar, g k ≤ M.psi k
  mono : MonotoneOn g (Icc 0 M.kbar)
  mono_sub : MonotoneOn (fun k => M.psi k - g k) (Icc 0 M.kbar)
  ge_self : ∀ k ∈ Icc 0 M.kbar, k < M.kstar → k ≤ g k
  at_kstar : g M.kstar = M.kstar
  le_self : ∀ k ∈ Icc 0 M.kbar, M.kstar < k → g k ≤ k

/-- The extension of `h ∈ C(K)` to `ℝ`, constant outside `K` (`Set.IccExtend`). -/
noncomputable def ext (h : Icc 0 M.kbar →ᵇ ℝ) : ℝ → ℝ := IccExtend M.kbar_pos.le h

/-- `ext h` agrees with `h` on `K`. -/
theorem ext_apply (h : Icc 0 M.kbar →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.ext h k = h ⟨k, hk⟩ :=
  IccExtend_of_mem _ _ hk

/-- **The set `F`** (p. 555): the `h ∈ C(K)` satisfying (2)–(6). -/
def F : Set (Icc 0 M.kbar →ᵇ ℝ) := {h | M.IsInF (M.ext h)}

/-- A continuous function on `K`, as an element of `C(K)`. -/
noncomputable def toBCF (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 M.kbar)) :
    Icc 0 M.kbar →ᵇ ℝ :=
  mkOfCompact ⟨(Icc 0 M.kbar).domRestrict g, hg.domRestrict⟩

/-- `toBCF g` evaluates as `g`. -/
theorem toBCF_apply (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 M.kbar)) (k : Icc 0 M.kbar) :
    M.toBCF g hg k = g k := rfl

/-- `ext (toBCF g)` agrees with `g` on `K`. -/
theorem ext_toBCF (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 M.kbar)) {k : ℝ}
    (hk : k ∈ Icc 0 M.kbar) : M.ext (M.toBCF g hg) k = g k := by
  rw [ext_apply _ _ hk, toBCF_apply]

variable {M}

/-- `IsInF` only depends on the values on `K`. -/
theorem IsInF.congr {g g' : ℝ → ℝ} (hg : M.IsInF g) (heq : EqOn g g' (Icc 0 M.kbar)) :
    M.IsInF g' where
  cont := hg.cont.congr fun k hk => (heq hk).symm
  nonneg k hk := heq hk ▸ hg.nonneg k hk
  le_psi k hk := heq hk ▸ hg.le_psi k hk
  mono a ha b hb hab := by rw [← heq ha, ← heq hb]; exact hg.mono ha hb hab
  mono_sub a ha b hb hab := by
    simp only
    rw [← heq ha, ← heq hb]; exact hg.mono_sub ha hb hab
  ge_self k hk hk' := heq hk ▸ hg.ge_self k hk hk'
  at_kstar := by rw [← heq M.kstar_mem]; exact hg.at_kstar
  le_self k hk hk' := heq hk ▸ hg.le_self k hk hk'

/-- `toBCF g ∈ F` when `g` satisfies (2)–(6). -/
theorem toBCF_mem_F {g : ℝ → ℝ} (hg : M.IsInF g) : M.toBCF g hg.cont ∈ M.F :=
  hg.congr fun _ hk => (M.ext_toBCF g hg.cont hk).symm

/-- On `K`, members of `F` change by at most the change in `ψ`: `|h(k′) − h(k)| ≤ |ψ(k′) − ψ(k)|`
(from (3)). -/
theorem IsInF.abs_sub_le {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) : |g a - g b| ≤ |M.psi a - M.psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hg.mono ha hb hab
    have h2 : M.psi a - g a ≤ M.psi b - g b := hg.mono_sub ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hg.mono hb ha hab
    have h2 : M.psi b - g b ≤ M.psi a - g a := hg.mono_sub hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- Members of `F` lie in `K`. -/
theorem IsInF.le_kbar {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ≤ M.kbar :=
  (hg.le_psi k hk).trans (M.psi_le_kbar hk)

/-- Members of `F` map `K` into `K`. -/
theorem IsInF.mem_Icc {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ∈ Icc 0 M.kbar :=
  ⟨hg.nonneg k hk, hg.le_kbar hk⟩

/-- Convex combinations of functions satisfying (2)–(6) satisfy (2)–(6). -/
theorem IsInF.convex_comb {g₁ g₂ : ℝ → ℝ} (h₁ : M.IsInF g₁) (h₂ : M.IsInF g₂) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    M.IsInF (fun k => a * g₁ k + b * g₂ k) where
  cont := (continuousOn_const.mul h₁.cont).add (continuousOn_const.mul h₂.cont)
  nonneg k hk := add_nonneg (mul_nonneg ha (h₁.nonneg k hk)) (mul_nonneg hb (h₂.nonneg k hk))
  le_psi k hk := by
    have := mul_le_mul_of_nonneg_left (h₁.le_psi k hk) ha
    have := mul_le_mul_of_nonneg_left (h₂.le_psi k hk) hb
    have : M.psi k = a * M.psi k + b * M.psi k := by rw [← add_mul, hab, one_mul]
    linarith
  mono x hx y hy hxy := by
    have := mul_le_mul_of_nonneg_left (h₁.mono hx hy hxy) ha
    have := mul_le_mul_of_nonneg_left (h₂.mono hx hy hxy) hb
    simp only
    linarith
  mono_sub x hx y hy hxy := by
    have e1 : M.psi x - g₁ x ≤ M.psi y - g₁ y := h₁.mono_sub hx hy hxy
    have e2 : M.psi x - g₂ x ≤ M.psi y - g₂ y := h₂.mono_sub hx hy hxy
    have := mul_le_mul_of_nonneg_left e1 ha
    have := mul_le_mul_of_nonneg_left e2 hb
    have ex : M.psi x = a * M.psi x + b * M.psi x := by rw [← add_mul, hab, one_mul]
    have ey : M.psi y = a * M.psi y + b * M.psi y := by rw [← add_mul, hab, one_mul]
    simp only
    nlinarith
  ge_self k hk hk' := by
    have := mul_le_mul_of_nonneg_left (h₁.ge_self k hk hk') ha
    have := mul_le_mul_of_nonneg_left (h₂.ge_self k hk hk') hb
    have : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    linarith
  at_kstar := by
    simp only [h₁.at_kstar, h₂.at_kstar]
    rw [← add_mul, hab, one_mul]
  le_self k hk hk' := by
    have := mul_le_mul_of_nonneg_left (h₁.le_self k hk hk') ha
    have := mul_le_mul_of_nonneg_left (h₂.le_self k hk hk') hb
    have : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    linarith

variable (M)

/-- The least element `h_` of `F` (p. 558): `h_(k) = k` for `k ≤ k*`, `h_(k) = k*` for `k > k*`,
i.e. `h_(k) = min{k, k*}`. -/
noncomputable def low (k : ℝ) : ℝ := min k M.kstar

/-- `h_` satisfies (2)–(6). -/
theorem isInF_low : M.IsInF M.low where
  cont := ContinuousOn.inf continuousOn_id continuousOn_const
  nonneg k hk := le_min hk.1 M.kstar_pos.le
  le_psi k hk := by
    rcases le_total k M.kstar with h | h
    · exact (min_le_left _ _).trans (M.lt_psi_of_le_kstar hk.1 h).le
    · refine (min_le_right _ _).trans ?_
      rcases h.eq_or_lt with h' | h'
      · rw [← h']; exact (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).le
      · exact (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).le.trans
          (M.psi_strictMonoOn (mem_Ici.2 M.kstar_pos.le) (mem_Ici.2 hk.1) h').le
  mono _ _ _ _ hxy := min_le_min_right _ hxy
  mono_sub x hx y hy hxy := by
    simp only [low]
    rcases le_total y M.kstar with hyk | hyk
    · rw [min_eq_left (hxy.trans hyk), min_eq_left hyk]
      rcases hxy.eq_or_lt with h | h
      · rw [h]
      · linarith [M.sub_lt_psi_sub hx.1 h hyk]
    · rw [min_eq_right hyk]
      rcases le_total x M.kstar with hxk | hxk
      · rw [min_eq_left hxk]
        have h1 : M.psi x - x ≤ M.psi M.kstar - M.kstar := by
          rcases hxk.eq_or_lt with h | h
          · rw [h]
          · linarith [M.sub_lt_psi_sub hx.1 h le_rfl]
        have h2 : M.psi M.kstar ≤ M.psi y := M.psi_strictMonoOn.monotoneOn
          (mem_Ici.2 M.kstar_pos.le) (mem_Ici.2 hy.1) hyk
        linarith
      · rw [min_eq_right hxk]
        have := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
        linarith
  ge_self k _ hk := (min_eq_left hk.le).ge
  at_kstar := min_self _
  le_self _ _ _ := min_le_left _ _

variable {M} in
/-- Every member of `F` lies above `h_` (p. 558). -/
theorem IsInF.low_le {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.low k ≤ g k := by
  rcases lt_trichotomy k M.kstar with h | h | h
  · exact (min_le_left _ _).trans (hg.ge_self k hk h)
  · rw [h, low, min_self, hg.at_kstar]
  · rw [low, min_eq_right h.le, ← hg.at_kstar]
    exact hg.mono M.kstar_mem hk h.le

/-- The pointwise upper bound `b(k) = min{ψ(k), max(k, k*)}` implied by (2), (3), (5), (6). -/
noncomputable def bnd (k : ℝ) : ℝ := min (M.psi k) (max k M.kstar)

variable {M} in
/-- Every member of `F` lies below `b`. -/
theorem IsInF.le_bnd {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ≤ M.bnd k := by
  refine le_min (hg.le_psi k hk) ?_
  rcases le_or_gt k M.kstar with h | h
  · rw [max_eq_right h, ← hg.at_kstar]
    exact hg.mono hk M.kstar_mem h
  · exact (hg.le_self k hk h).trans (le_max_left _ _)

/-- `b` is nondecreasing on `K`. -/
theorem bnd_mono : MonotoneOn M.bnd (Icc 0 M.kbar) := fun _ hx _ hy hxy =>
  min_le_min (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy)
    (max_le_max_right _ hxy)

/-- `b` is continuous on `K`. -/
theorem bnd_continuousOn : ContinuousOn M.bnd (Icc 0 M.kbar) :=
  ContinuousOn.inf (M.psi_continuousOn.mono Icc_subset_Ici_self)
    (ContinuousOn.sup continuousOn_id continuousOn_const)

/-! ### Running suprema -/

/-- The running supremum `k ↦ sup_{0 ≤ j ≤ k} φ(j)`. -/
noncomputable def runSup (φ : ℝ → ℝ) (k : ℝ) : ℝ := sSup (φ '' Icc 0 k)

omit M in
/-- A value of `φ` on `[0, k]` is below the running supremum. -/
theorem le_runSup {φ : ℝ → ℝ} {b k j : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) (hk : k ≤ b)
    (hj : j ∈ Icc 0 k) : φ j ≤ runSup φ k :=
  le_csSup ((isCompact_Icc.image_of_continuousOn
    (hφ.mono (Icc_subset_Icc_right hk))).bddAbove) (mem_image_of_mem φ hj)

omit M in
/-- The running supremum is the least bound of `φ` on `[0, k]`. -/
theorem runSup_le {φ : ℝ → ℝ} {k c : ℝ} (hk : 0 ≤ k) (h : ∀ j ∈ Icc 0 k, φ j ≤ c) :
    runSup φ k ≤ c :=
  csSup_le ((nonempty_Icc.2 hk).image φ) (forall_mem_image.2 h)

omit M in
/-- The running supremum is nondecreasing. -/
theorem runSup_mono {φ : ℝ → ℝ} {b : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) :
    MonotoneOn (runSup φ) (Icc 0 b) := fun _ hx _ hy hxy =>
  runSup_le hx.1 fun _ hj => le_runSup hφ hy.2 ⟨hj.1, hj.2.trans hxy⟩

omit M in
/-- The running supremum of a continuous function is continuous. -/
theorem runSup_continuousOn {φ : ℝ → ℝ} {b : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) :
    ContinuousOn (runSup φ) (Icc 0 b) := by
  have hu := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ)
  rw [Metric.continuousOn_iff]
  intro k0 hk0 ε hε
  obtain ⟨δ, hδ, hφδ⟩ := hu (ε / 2) (by linarith)
  have key : ∀ a ∈ Icc 0 b, ∀ c ∈ Icc 0 b, a ≤ c → c - a < δ →
      runSup φ a ≤ runSup φ c ∧ runSup φ c ≤ runSup φ a + ε / 2 := by
    intro a ha c hc hac hca
    refine ⟨runSup_mono hφ ha hc hac, runSup_le hc.1 fun j hj => ?_⟩
    rcases le_or_gt j a with hja | hja
    · linarith [le_runSup hφ ha.2 ⟨hj.1, hja⟩]
    · have hjb : j ∈ Icc 0 b := ⟨hj.1, hj.2.trans hc.2⟩
      have h1 := hφδ j hjb a ha (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [hj.2])
      rw [Real.dist_eq] at h1
      have h2 := le_runSup hφ ha.2 (show a ∈ Icc 0 a from ⟨ha.1, le_rfl⟩)
      linarith [(abs_lt.1 h1).2]
  refine ⟨δ, hδ, fun k hk hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  rcases le_total k k0 with h | h
  · obtain ⟨h1, h2⟩ := key k hk k0 hk0 h (by linarith [(abs_lt.1 hdist).1])
    rw [abs_lt]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := key k0 hk0 k hk h (by linarith [(abs_lt.1 hdist).2])
    rw [abs_lt]; constructor <;> linarith

/-! ### The greatest element of `F` -/

/-- The gap `ψ − b` whose running supremum defines the greatest element. -/
noncomputable def gap (j : ℝ) : ℝ := M.psi j - M.bnd j

/-- The gap is continuous on `K`. -/
theorem gap_continuousOn : ContinuousOn M.gap (Icc 0 M.kbar) :=
  (M.psi_continuousOn.mono Icc_subset_Ici_self).sub M.bnd_continuousOn

/-- **The greatest element `ū` of `F`** (corrected p. 558):
`ū(k) = ψ(k) − max_{0 ≤ j ≤ k} [ψ(j) − b(j)]`, the largest function below `b` with `ψ − ū`
nondecreasing. -/
noncomputable def up (k : ℝ) : ℝ := M.psi k - runSup M.gap k

variable {M} in
/-- Maximality: every member of `F` lies below `ū`. -/
theorem IsInF.le_up {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    g k ≤ M.up k := by
  have : runSup M.gap k ≤ M.psi k - g k := by
    refine runSup_le hk.1 fun j hj => ?_
    have hjK : j ∈ Icc 0 M.kbar := ⟨hj.1, hj.2.trans hk.2⟩
    have h1 : M.psi j - g j ≤ M.psi k - g k := hg.mono_sub hjK hk hj.2
    have h2 := hg.le_bnd hjK
    simp only [gap]
    linarith
  simp only [up]
  linarith

/-- `ū ≤ b` on `K`. -/
theorem up_le_bnd {k : ℝ} (hk : k ∈ Icc 0 M.kbar) : M.up k ≤ M.bnd k := by
  have := le_runSup M.gap_continuousOn hk.2 (show k ∈ Icc 0 k from ⟨hk.1, le_rfl⟩)
  simp only [up, gap] at this ⊢
  linarith

/-- `ū` satisfies (2)–(6). -/
theorem isInF_up : M.IsInF M.up where
  cont := (M.psi_continuousOn.mono Icc_subset_Ici_self).sub
    (runSup_continuousOn M.gap_continuousOn)
  nonneg k hk := (le_min hk.1 M.kstar_pos.le).trans (M.isInF_low.le_up hk)
  le_psi k hk := (M.up_le_bnd hk).trans (min_le_left _ _)
  mono x hx y hy hxy := by
    have : runSup M.gap y ≤ runSup M.gap x + (M.psi y - M.psi x) := by
      refine runSup_le hy.1 fun j hj => ?_
      have hjK : j ∈ Icc 0 M.kbar := ⟨hj.1, hj.2.trans hy.2⟩
      have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
      rcases le_or_gt j x with hjx | hjx
      · linarith [le_runSup M.gap_continuousOn hx.2 ⟨hj.1, hjx⟩]
      · have h1 := M.bnd_mono hx hjK hjx.le
        have h2 := M.up_le_bnd hx
        have h3 := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hj.1) (mem_Ici.2 hy.1) hj.2
        simp only [up, gap] at h2 ⊢
        linarith
    simp only [up]
    linarith
  mono_sub x hx y hy hxy := by
    simp only [up, sub_sub_cancel]
    exact runSup_mono M.gap_continuousOn hx hy hxy
  ge_self k hk hk' := by
    have := M.isInF_low.le_up hk
    rwa [low, min_eq_left hk'.le] at this
  at_kstar := by
    refine le_antisymm ?_ ?_
    · refine (M.up_le_bnd M.kstar_mem).trans ?_
      rw [bnd, max_self]
      exact min_le_right _ _
    · have := M.isInF_low.le_up M.kstar_mem
      rwa [low, min_self] at this
  le_self k hk hk' := by
    refine (M.up_le_bnd hk).trans ((min_le_right _ _).trans ?_)
    rw [max_eq_left hk'.le]

/-- `ū(k) = min{ψ(k), k*}` for `0 ≤ k ≤ k*` (the formula of p. 558 on `[0, k*]`). -/
theorem up_eq_of_le_kstar {k : ℝ} (h0 : 0 ≤ k) (hk : k ≤ M.kstar) :
    M.up k = min (M.psi k) M.kstar := by
  have hkK : k ∈ Icc 0 M.kbar := ⟨h0, hk.trans M.kstar_lt_kbar.le⟩
  refine le_antisymm ?_ ?_
  · have := M.up_le_bnd hkK
    rwa [bnd, max_eq_right hk] at this
  · have : runSup M.gap k ≤ M.psi k - min (M.psi k) M.kstar := by
      refine runSup_le h0 fun j hj => ?_
      have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hj.1) (mem_Ici.2 h0) hj.2
      simp only [gap, bnd, max_eq_right (hj.2.trans hk)]
      rcases le_total (M.psi j) M.kstar with h1 | h1 <;>
        rcases le_total (M.psi k) M.kstar with h2 | h2 <;>
        simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith
    simp only [up]
    linarith

/-- `ū(k) = ψ(k) − max_{k* ≤ j ≤ k} [ψ(j) − j]` for `k* ≤ k ≤ k̄` (the corrected formula of
NOTE 18.3-H; the book's `h̄` has `min{k, ψ(k) − [ψ(k*) − k*]}` instead). -/
theorem up_eq_of_kstar_le {k : ℝ} (hk : M.kstar ≤ k) (hkb : k ≤ M.kbar) :
    M.up k = M.psi k - sSup ((fun j => M.psi j - j) '' Icc M.kstar k) := by
  have hcont : ContinuousOn (fun j => M.psi j - j) (Icc M.kstar k) :=
    ((M.psi_continuousOn.mono fun j hj => mem_Ici.2 (M.kstar_pos.le.trans hj.1)).sub
      continuousOn_id)
  have hbdd : BddAbove ((fun j => M.psi j - j) '' Icc M.kstar k) :=
    (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  have hne : ((fun j => M.psi j - j) '' Icc M.kstar k).Nonempty :=
    (nonempty_Icc.2 hk).image _
  -- on `[k*, k]` the gap is `ψ(j) − j`
  have hgap : ∀ j ∈ Icc M.kstar k, M.gap j = M.psi j - j := by
    intro j hj
    have hj0 : 0 ≤ j := M.kstar_pos.le.trans hj.1
    have hjpsi : j ≤ M.psi j := by
      rcases (hj.2.trans hkb).lt_or_eq with h | h
      · exact (M.lt_psi hj0 h).le
      · rw [h, psi_kbar]
    simp only [gap, bnd, max_eq_left hj.1, min_eq_right hjpsi]
  simp only [up]
  congr 1
  refine le_antisymm (runSup_le (M.kstar_pos.le.trans hk) fun j hj => ?_) ?_
  · rcases le_or_gt j M.kstar with hjk | hjk
    · -- on `[0, k*]` the gap is at most `ψ(k*) − k*`
      have h1 : M.gap j ≤ M.psi M.kstar - M.kstar := by
        have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hj.1) (mem_Ici.2 M.kstar_pos.le) hjk
        have hk' := M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl
        simp only [gap, bnd, max_eq_right hjk]
        rcases le_total (M.psi j) M.kstar with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
      exact h1.trans (le_csSup hbdd ⟨M.kstar, ⟨le_rfl, hk⟩, rfl⟩)
    · rw [hgap j ⟨hjk.le, hj.2⟩]
      exact le_csSup hbdd ⟨j, ⟨hjk.le, hj.2⟩, rfl⟩
  · refine csSup_le hne (forall_mem_image.2 fun j hj => ?_)
    rw [← hgap j hj]
    exact le_runSup M.gap_continuousOn hkb ⟨M.kstar_pos.le.trans hj.1, hj.2⟩

/-! ### The book's `h̄` is not in `F` -/

/-- The book's candidate maximal element (p. 558): `h̄(k) = min{ψ(k), k*}` for `k ≤ k*` and
`h̄(k) = min{k, ψ(k) − [ψ(k*) − k*]}` for `k > k*`. -/
noncomputable def hbar (k : ℝ) : ℝ :=
  if k ≤ M.kstar then min (M.psi k) M.kstar else min k (M.psi k - (M.psi M.kstar - M.kstar))

/-- Just to the right of `k*`, `ψ(k) − k` exceeds its value `ψ(k*) − k*` at `k*` (because
`(1 − θ) f′(k*) = 1/β > 1`). -/
theorem exists_gap_gt : ∃ k, M.kstar < k ∧ k < M.kbar ∧
    M.psi M.kstar - M.kstar < M.psi k - k := by
  have h1 : 1 < (1 - M.θ) * M.f' M.kstar := by
    have h := M.euler_kstar
    have hpos : 0 < (1 - M.θ) * M.f' M.kstar :=
      mul_pos (by linarith [M.θ_lt_one]) (M.f'_pos M.kstar_pos.le)
    by_contra hle
    push Not at hle
    have : M.β * ((1 - M.θ) * M.f' M.kstar) ≤ M.β * 1 :=
      mul_le_mul_of_nonneg_left hle M.β_pos.le
    nlinarith [M.β_lt_one]
  have hc : ContinuousWithinAt (fun k => (1 - M.θ) * M.f' k) (Ici 0) M.kstar :=
    continuousWithinAt_const.mul (M.f'_continuousOn _ (mem_Ici.2 M.kstar_pos.le))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hc.eventually_const_lt h1)
  set k := M.kstar + min (δ / 2) ((M.kbar - M.kstar) / 2)
  have hm : 0 < min (δ / 2) ((M.kbar - M.kstar) / 2) :=
    lt_min (by linarith) (by linarith [M.kstar_lt_kbar])
  have hk1 : M.kstar < k := by linarith
  have hk2 : k < M.kbar := by linarith [min_le_right (δ / 2) ((M.kbar - M.kstar) / 2)]
  have hkf : 1 < (1 - M.θ) * M.f' k := by
    refine hball ⟨?_, mem_Ici.2 (by linarith [M.kstar_pos])⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith [min_le_left (δ / 2) ((M.kbar - M.kstar) / 2)]
  refine ⟨k, hk1, hk2, ?_⟩
  have h2 := M.psi_sub_gt M.kstar_pos.le hk1
  have h3 : (k - M.kstar) < (1 - M.θ) * (k - M.kstar) * M.f' k := by nlinarith
  linarith

/-- **Correction (p. 558).** The book's `h̄` violates (3): `ψ − h̄` is not nondecreasing on `K`,
so `h̄` does not satisfy (2)–(6). -/
theorem not_isInF_hbar : ¬ M.IsInF M.hbar := by
  intro hh
  obtain ⟨k, hk1, hk2, hgap⟩ := M.exists_gap_gt
  have hc : 0 < M.psi M.kstar - M.kstar := by
    linarith [M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl]
  have hhk : M.hbar k = k := by
    have hn : ¬ k ≤ M.kstar := not_le.2 hk1
    simp only [hbar, hn, ↓reduceIte]
    exact min_eq_left (by linarith)
  have hhb : M.hbar M.kbar = M.kbar - (M.psi M.kstar - M.kstar) := by
    have hn : ¬ M.kbar ≤ M.kstar := not_le.2 M.kstar_lt_kbar
    simp only [hbar, hn, ↓reduceIte, psi_kbar]
    exact min_eq_right (by linarith)
  have hmono : M.psi k - M.hbar k ≤ M.psi M.kbar - M.hbar M.kbar :=
    hh.mono_sub ⟨by linarith [M.kstar_pos], hk2.le⟩ ⟨M.kbar_pos.le, le_rfl⟩ hk2.le
  rw [hhk, hhb, psi_kbar] at hmono
  linarith

/-- **Correction (p. 558).** No member of `F` equals the book's `h̄` on `K`; in particular `h̄`
is not the greatest element of `F` (that is `ū`, `isGreatest_up`). -/
theorem hbar_not_mem_F (h : Icc 0 M.kbar →ᵇ ℝ) (hh : h ∈ M.F) :
    ∃ k : Icc 0 M.kbar, h k ≠ M.hbar k := by
  by_contra hall
  push Not at hall
  exact M.not_isInF_hbar (IsInF.congr hh fun k hk => by rw [ext_apply _ _ hk, hall ⟨k, hk⟩])

/-! ### Properties of `F` used by Schauder's Theorem (p. 556) -/

/-- `F` is nonempty (it contains `h_`). -/
theorem F_nonempty : M.F.Nonempty := ⟨_, toBCF_mem_F M.isInF_low⟩

/-- Every `h ∈ F` has `‖h‖ ≤ k̄`. -/
theorem norm_le_of_mem_F {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) : ‖h‖ ≤ M.kbar := by
  refine (norm_le M.kbar_pos.le).2 fun k => ?_
  have h1 := (hh : M.IsInF (M.ext h)).nonneg k k.2
  have h2 := (hh : M.IsInF (M.ext h)).le_kbar k.2
  rw [ext_apply _ _ k.2] at h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

/-- `F` is bounded. -/
theorem F_isBounded : Bornology.IsBounded M.F :=
  (Metric.isBounded_iff_subset_closedBall 0).2 ⟨M.kbar, fun h hh => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact M.norm_le_of_mem_F hh⟩

/-- `F` is convex. -/
theorem F_convex : Convex ℝ M.F := by
  intro h₁ hh₁ h₂ hh₂ a b ha hb hab
  refine (IsInF.convex_comb hh₁ hh₂ ha hb hab).congr fun k hk => ?_
  simp only [ext_apply _ _ hk, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul]

/-- `F` is closed in `C(K)`. -/
theorem F_isClosed : IsClosed M.F := by
  refine isClosed_of_closure_subset fun h hh => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hh
  have hev : ∀ k (hk : k ∈ Icc 0 M.kbar),
      Tendsto (fun n => M.ext (u n) k) atTop (𝓝 (M.ext h k)) := by
    intro k hk
    simp only [ext_apply _ _ hk]
    exact ((continuous_eval_const _).tendsto _).comp hlim
  have hu' : ∀ n, M.IsInF (M.ext (u n)) := hu
  exact
  { cont := (continuous_IccExtend_iff.2 h.continuous).continuousOn
    nonneg := fun k hk => ge_of_tendsto' (hev k hk) fun n => (hu' n).nonneg k hk
    le_psi := fun k hk => le_of_tendsto' (hev k hk) fun n => (hu' n).le_psi k hk
    mono := fun x hx y hy hxy =>
      le_of_tendsto_of_tendsto' (hev x hx) (hev y hy) fun n => (hu' n).mono hx hy hxy
    mono_sub := fun x hx y hy hxy =>
      le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub (hev x hx))
        (tendsto_const_nhds.sub (hev y hy)) fun n => (hu' n).mono_sub hx hy hxy
    ge_self := fun k hk hk' => ge_of_tendsto' (hev k hk) fun n => (hu' n).ge_self k hk hk'
    at_kstar := tendsto_nhds_unique (hev _ M.kstar_mem)
      (tendsto_const_nhds.congr fun n => ((hu' n).at_kstar).symm)
    le_self := fun k hk hk' => le_of_tendsto' (hev k hk) fun n => (hu' n).le_self k hk hk' }

/-- **Proposition 18.5** (p. 557): `F` is an equicontinuous family. The proof uses only the
uniform continuity of `ψ` on the compact `K` and `|h(k′) − h(k)| ≤ |ψ(k′) − ψ(k)|` (the book's
Lipschitz constant `A = f′(0)` is wrong; see `prop_18_5_bound_counterexample`). -/
theorem prop_18_5 : UniformEquicontinuous fun h : M.F => ⇑(h : Icc 0 M.kbar →ᵇ ℝ) := by
  have hu := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := M.kbar)).uniformContinuousOn_of_continuous
      (M.psi_continuousOn.mono Icc_subset_Ici_self))
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hψ⟩ := hu ε hε
  refine ⟨δ, hδ, fun x y hxy h => ?_⟩
  have h1 := (h.2 : M.IsInF (M.ext h)).abs_sub_le x.2 y.2
  rw [ext_apply _ _ x.2, ext_apply _ _ y.2] at h1
  rw [Real.dist_eq]
  have h2 := hψ x x.2 y y.2 hxy
  rw [Real.dist_eq] at h2
  exact h1.trans_lt h2

/-- **Proposition 18.5** in the book's `ε`–`δ` form (p. 520): one `δ` for all members of `F`. -/
theorem prop_18_5' : ∀ ε > 0, ∃ δ > 0, ∀ x y : Icc 0 M.kbar, dist x y < δ →
    ∀ h ∈ M.F, |h x - h y| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.uniformEquicontinuous_iff.1 M.prop_18_5 ε hε
  exact ⟨δ, hδ, fun x y hxy h hF => by
    have := hh x y hxy ⟨h, hF⟩
    rwa [Real.dist_eq] at this⟩

/-- `h_` is the least element of `F` (p. 558). -/
theorem isLeast_low : IsLeast M.F (M.toBCF M.low M.isInF_low.cont) := by
  refine ⟨toBCF_mem_F M.isInF_low, fun h hh k => ?_⟩
  have := (hh : M.IsInF (M.ext h)).low_le k.2
  rw [ext_apply _ _ k.2] at this
  exact this

/-- `ū` is the greatest element of `F` (corrected p. 558; the book's `h̄` is not in `F`). -/
theorem isGreatest_up : IsGreatest M.F (M.toBCF M.up M.isInF_up.cont) := by
  refine ⟨toBCF_mem_F M.isInF_up, fun h hh k => ?_⟩
  have := (hh : M.IsInF (M.ext h)).le_up k.2
  rw [ext_apply _ _ k.2] at this
  exact this

end GlobalModel

end StokeyLucasPrescott.EquilibriaWithDistortions

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
`EquilibriaWithDistortions.SchauderBoundedContinuous`.

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

namespace StokeyLucasPrescott.EquilibriaWithDistortions

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

end StokeyLucasPrescott.EquilibriaWithDistortions

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

namespace StokeyLucasPrescott.EquilibriaWithDistortions

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

end StokeyLucasPrescott.EquilibriaWithDistortions

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

namespace StokeyLucasPrescott.EquilibriaWithDistortions

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

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The operator `T` of SLP §18.3 (7): Exercises 18.5–18.7 and existence (pp. 556–558)

For `h ∈ F`, `(Th)(k)` is "the `y` solving" (§18.3 (7))
  `U′[ψ(k) − y] = β(1 − θ) f′(y) U′[ψ(y) − h(y)]`.
Here `(Th)(k)` is the crossing point `eulerCross` of `GlobalCrossing` with right side `+∞` where
`ψ(y) − h(y) = 0` (Inada condition) and `β(1 − θ) f′(y) U′[ψ(y) − h(y)]` otherwise.

* `ex_18_5_wellDefined` (**Exercise 18.5**, first half, corrected): for `h ∈ F` and `k ∈ K`,
  either `(Th)(k) < ψ(k)` is the unique solution of (7) with positive consumption in both
  periods, or there is no such solution, `h = ψ` on `[0, ψ(k))` and `(Th)(k) = ψ(k)`.
* `ex_18_5` (**Exercise 18.5**, second half): `T(F) ⊆ F`.
* `ex_18_5_counterexample_of` (**Correction**, NOTE 18.3-E): if `ψ(ψ(0)) ≤ k*`, the member
  `h(k) = min{ψ(k), k*}` of `F` makes (7) at `k = 0` have no solution; a concrete model with
  `ψ(ψ(0)) ≤ k*` is `GlobalExamples.ex_18_5_counterexample`.
* `ex_18_6` (**Exercise 18.6**): `T` is continuous on `F`.
* `ex_18_7` (**Exercise 18.7**): `T` is monotone on `F`.
* `exists_equilibrium` (p. 558): Schauder's Theorem gives a fixed point of `T` in `F`.
* `isFixedPt_iff_euler`: the fixed points of `T` in `F` are exactly the `g ∈ F` solving the
  Euler equation (1) at every `k ∈ K` with positive consumption in both periods.
* `least_greatest_equilibria` (p. 558): iterating `T` from the least element `h_` and from the
  greatest element `ū` of `F` (Theorem 17.7 and its Corollary) converges to the least and the
  greatest fixed points of `T` in `F`; `unique_equilibrium_of_tendsto` gives uniqueness when
  the two limits coincide.

**Correction (Exercise 18.5, manual pp. 287–289).** (i) As an equation, (7) need not have a
solution for every `h ∈ F` (`ex_18_5_counterexample_of`); `T` is defined by the extended-real
convention `(Th)(k) = ψ(k)` when the right side is `+∞` on `[0, ψ(k))`. (ii) The manual proves
continuity of `Th` "by the Implicit Function Theorem", which does not apply since `h` is only
continuous. Here `0 ≤ (Th)(k₂) − (Th)(k₁) ≤ ψ(k₂) − ψ(k₁)` for `k₁ ≤ k₂` (`Tval_mono`,
`Tval_sub_le`) gives continuity with the modulus of continuity of `ψ`. (iii) The manual's
"`RHS(y) → ∞` as `y → 0`" is false (`manual_rhs_limit_counterexample`); only
`RHS(0) > LHS(0)` is needed (`eulerBelow_zero`).

**Correction (Exercise 18.6, manual pp. 289–290).** The manual's pointwise step replaces
`h(y)` by `h(k)` ("`ψ(y) − x` with `x̂ = g(k)`") and uses the Implicit Function Theorem for a
non-differentiable `h`. The proof here (`eventually_abs_Tval_sub_le`) is the monotone crossing
argument `eventually_abs_eulerCross_sub_le` with `h` evaluated at `y`; the passage to uniform
convergence uses equicontinuity of `T(F)` and a finite net of `K`, as in the manual.

**Correction (p. 558).** Theorem 17.7 is applied from `ū` (`GlobalApproach.isGreatest_up`),
not from the book's `h̄`, which is not in `F`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

namespace GlobalModel

variable (M : GlobalModel)

/-- Zero next-period consumption at `y`: `ψ(y) − g(y) ≤ 0` (the right side of (7) is `+∞`). -/
def Zd (g : ℝ → ℝ) (y : ℝ) : Prop := M.psi y - g y ≤ 0

/-- The right side of (7) where it is finite: `β(1 − θ) f′(y) U′[ψ(y) − g(y)]`. -/
noncomputable def Rd (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y)

/-- **The operator (7)**, pointwise: `(Tg)(k)` is the crossing point of
`y ↦ U′[ψ(k) − y]` and `y ↦ β(1 − θ) f′(y) U′[ψ(y) − g(y)]` on `[0, ψ(k)]`. -/
noncomputable def Tval (g : ℝ → ℝ) (k : ℝ) : ℝ := eulerCross M.U' (M.Zd g) (M.Rd g) (M.psi k)

/-- `β(1 − θ) > 0`. -/
theorem euler_coef_pos : 0 < M.β * (1 - M.θ) := mul_pos M.β_pos (by linarith [M.θ_lt_one])

variable {M}

/-- For `g` satisfying (2)–(6) the right side of (7) is an `IsEulerRHS` on `[0, k̄]`:
nonincreasing (by (3)), continuous where finite, and tending to `+∞` where next-period
consumption vanishes (Inada). -/
theorem IsInF.isEulerRHS {g : ℝ → ℝ} (hg : M.IsInF g) :
    IsEulerRHS M.kbar (M.Zd g) (M.Rd g) where
  zero_anti y y' hy' hyy hyB hz := by
    have h := hg.mono_sub ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    simp only at h
    exact h.trans hz
  anti y y' hy' hyy hyB hz := by
    have hc' : 0 < M.psi y' - g y' := lt_of_not_ge hz
    have hcc : M.psi y' - g y' ≤ M.psi y - g y :=
      hg.mono_sub ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    have hU : M.U' (M.psi y - g y) ≤ M.U' (M.psi y' - g y') :=
      M.U'_strictAntiOn.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : M.f' y ≤ M.f' y' :=
      M.f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 (hy'.trans hyy)) hyy
    have hUpos : 0 < M.U' (M.psi y - g y) := M.U'_pos (hc'.trans_le hcc)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf M.euler_coef_pos.le) hU hUpos.le
      (mul_pos M.euler_coef_pos (M.f'_pos hy')).le
  cont y hy hz := by
    have hc : 0 < M.psi y - g y := lt_of_not_ge hz
    have hcw : ContinuousWithinAt (fun z => M.psi z - g z) (Icc 0 M.kbar) y :=
      ((M.psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub (hg.cont y hy)
    refine ⟨(hcw.eventually_const_lt hc).mono fun z hz => not_le.2 hz, ?_⟩
    exact (continuousWithinAt_const.mul ((M.f'_continuousOn.mono Icc_subset_Ici_self) y hy)).mul
      ((M.U'_continuousOn.continuousAt (Ioi_mem_nhds hc)).comp_continuousWithinAt
        (f := fun z => M.psi z - g z) hcw)
  blowup y hy hz M0 := by
    have hcw : ContinuousWithinAt (fun z => M.psi z - g z) (Icc 0 M.kbar) y :=
      ((M.psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub (hg.cont y hy)
    set m := M.β * (1 - M.θ) * M.f' M.kbar
    have hm : 0 < m := mul_pos M.euler_coef_pos (M.f'_pos M.kbar_pos.le)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (M.U'_inada.eventually_gt_atTop (|M0| / m))
    have hlt : M.psi y - g y < ε := lt_of_le_of_lt hz hε
    filter_upwards [hcw.eventually_lt_const hlt, self_mem_nhdsWithin] with z hz1 hzK
    by_cases hz0 : M.psi z - g z ≤ 0
    · exact Or.inl hz0
    · right
      have hc : 0 < M.psi z - g z := lt_of_not_ge hz0
      have hU : |M0| / m < M.U' (M.psi z - g z) := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact hz1, hc⟩
      have hf : M.f' M.kbar ≤ M.f' z :=
        M.f'_strictAntiOn.antitoneOn (mem_Ici.2 hzK.1) (mem_Ici.2 M.kbar_pos.le) hzK.2
      have h1 : m ≤ M.β * (1 - M.θ) * M.f' z := mul_le_mul_of_nonneg_left hf M.euler_coef_pos.le
      have h2 : |M0| < m * M.U' (M.psi z - g z) := by
        rwa [div_lt_iff₀ hm, mul_comm] at hU
      have h3 : m * M.U' (M.psi z - g z) ≤ M.β * (1 - M.θ) * M.f' z * M.U' (M.psi z - g z) :=
        mul_le_mul_of_nonneg_right h1 (M.U'_pos hc).le
      have h4 := le_abs_self M0
      simp only [Rd]
      linarith

/-- The left side of (7) is below the right side at `y = 0`: if `ψ(0) − h(0) > 0`, then
`RHS(0) = β(1 − θ) f′(0) U′[ψ(0) − h(0)] > U′[ψ(0)] ≥ U′[ψ(k)] = LHS(0)` (Assumption 18.1d). This
replaces the manual's false claim `RHS(y) → ∞` as `y → 0`. -/
theorem IsInF.eulerBelow_zero {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    EulerBelow M.U' (M.Zd g) (M.Rd g) (M.psi k) 0 := by
  by_cases hz : M.psi 0 - g 0 ≤ 0
  · exact Or.inl hz
  · right
    have hc : 0 < M.psi 0 - g 0 := lt_of_not_ge hz
    have h0K : (0 : ℝ) ∈ Icc 0 M.kbar := ⟨le_rfl, M.kbar_pos.le⟩
    have hψ := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have hc0 : M.psi 0 - g 0 ≤ M.psi 0 := by linarith [hg.nonneg 0 h0K]
    have h1 : M.U' (M.psi k) ≤ M.U' (M.psi 0) :=
      M.U'_strictAntiOn.antitoneOn (M.psi_pos le_rfl) (M.psi_pos hk.1) hψ
    have h2 : M.U' (M.psi 0) ≤ M.U' (M.psi 0 - g 0) :=
      M.U'_strictAntiOn.antitoneOn hc (M.psi_pos le_rfl) hc0
    have h3 : M.U' (M.psi 0 - g 0) < M.β * (1 - M.θ) * M.f' 0 * M.U' (M.psi 0 - g 0) :=
      lt_mul_left (M.U'_pos hc) M.one_lt_euler_zero
    simp only [Rd, sub_zero]
    linarith

/-- **Correction to the manual's Exercise 18.5** (NOTE 18.3-D): the claim
"`RHS(y) = β(1 − θ) f′(y) U′[ψ(y) − h(y)] → ∞` as `y → 0`" is false for `h = h_ ∈ F` in every
model: there `ψ(0) − h_(0) = f(0) > 0`, and the right side is continuous at `0`. -/
theorem manual_rhs_limit_counterexample (M : GlobalModel) :
    ¬ Tendsto (M.Rd M.low) (𝓝[>] 0) atTop := by
  have h0K : (0 : ℝ) ∈ Icc 0 M.kbar := ⟨le_rfl, M.kbar_pos.le⟩
  have hz : ¬ M.Zd M.low 0 := by
    simp only [Zd, GlobalModel.low, min_eq_left M.kstar_pos.le, sub_zero, not_le]
    exact M.psi_pos le_rfl
  have hc := (M.isInF_low.isEulerRHS.cont 0 h0K hz).2
  have hlim : Tendsto (M.Rd M.low) (𝓝[>] 0) (𝓝 (M.Rd M.low 0)) := by
    refine hc.tendsto.mono_left (le_inf nhdsWithin_le_nhds ?_)
    rw [le_principal_iff]
    filter_upwards [Ioo_mem_nhdsGT M.kbar_pos] with y hy
    exact ⟨hy.1.le, hy.2.le⟩
  exact not_tendsto_atTop_of_tendsto_nhds hlim

/-- `0 ≤ (Tg)(k) ≤ ψ(k)`. -/
theorem Tval_mem_Icc (g : ℝ → ℝ) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.Tval g k ∈ Icc 0 (M.psi k) :=
  ⟨eulerCross_nonneg, eulerCross_le (M.psi_pos hk.1).le⟩

/-- **Exercise 18.5, existence and uniqueness (corrected).** For `g` satisfying (2)–(6) and
`k ∈ K`, either `y = (Tg)(k) < ψ(k)`, both consumptions `ψ(k) − y` and `ψ(y) − g(y)` are
positive, (7) holds at `y`, and `y` is its only solution with positive consumptions; or (7) has
no solution with positive consumptions, `g = ψ` on `[0, ψ(k))`, and `(Tg)(k) = ψ(k)` (the
extended-real convention: zero consumption, `∞ = ∞`). -/
theorem IsInF.Tval_spec {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    (M.Tval g k < M.psi k ∧ 0 < M.psi (M.Tval g k) - g (M.Tval g k) ∧
      M.U' (M.psi k - M.Tval g k) = M.β * (1 - M.θ) * M.f' (M.Tval g k) *
        M.U' (M.psi (M.Tval g k) - g (M.Tval g k)) ∧
      ∀ y, 0 ≤ y → y < M.psi k → 0 < M.psi y - g y →
        M.U' (M.psi k - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y) →
        y = M.Tval g k) ∨
    (M.Tval g k = M.psi k ∧ ∀ y, 0 ≤ y → y < M.psi k → g y = M.psi y) := by
  have hP := M.psi_pos hk.1
  have hPB := M.psi_le_kbar hk
  rcases eulerCross_spec M.isMarginalUtility hg.isEulerRHS hP hPB (hg.eulerBelow_zero hk) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, lt_of_not_ge h2, h3, fun y hy0 hyP hc heq => ?_⟩
    exact (eulerCross_unique M.isMarginalUtility hg.isEulerRHS hPB hy0 hyP
      (not_le.2 hc) heq).symm
  · refine Or.inr ⟨h1, fun y hy0 hyP => ?_⟩
    have := h2 y hy0 hyP
    have h' := hg.le_psi y ⟨hy0, hyP.le.trans hPB⟩
    simp only [Zd] at this
    linarith

/-- `k ↦ (Tg)(k)` is nondecreasing on `K`. -/
theorem IsInF.Tval_mono {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) (hab : a ≤ b) : M.Tval g a ≤ M.Tval g b :=
  eulerCross_mono M.isMarginalUtility hg.isEulerRHS
    (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab) (M.psi_le_kbar hb)
    ⟨0, le_rfl, M.psi_pos ha.1, hg.eulerBelow_zero ha⟩

/-- `ψ − Tg` is nondecreasing on `K`: `(Tg)(b) − (Tg)(a) ≤ ψ(b) − ψ(a)` for `a ≤ b`. -/
theorem IsInF.Tval_sub_le {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) (hab : a ≤ b) :
    M.Tval g b ≤ M.Tval g a + (M.psi b - M.psi a) :=
  eulerCross_le_add_sub M.isMarginalUtility hg.isEulerRHS
    (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab) (M.psi_le_kbar hb)

/-- `|(Tg)(a) − (Tg)(b)| ≤ |ψ(a) − ψ(b)|` on `K`. -/
theorem IsInF.abs_Tval_sub_le {g : ℝ → ℝ} (hg : M.IsInF g) {a b : ℝ} (ha : a ∈ Icc 0 M.kbar)
    (hb : b ∈ Icc 0 M.kbar) : |M.Tval g a - M.Tval g b| ≤ |M.psi a - M.psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hg.Tval_mono ha hb hab
    have h2 := hg.Tval_sub_le ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hg.Tval_mono hb ha hab
    have h2 := hg.Tval_sub_le hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- (4)–(5) for `Tg`, lower half: if `k ≤ k*` and `g(k) ≥ k` then `(Tg)(k) ≥ k`
(the manual's argument, with `β(1 − θ) f′ > 1` below `k*`). -/
theorem IsInF.le_Tval {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar)
    (hks : k ≤ M.kstar) (hgk : k ≤ g k) : k ≤ M.Tval g k := by
  have hkψ : k < M.psi k := M.lt_psi_of_le_kstar hk.1 hks
  refine le_eulerCross_of_forall fun y hy0 hyk => ⟨hy0, hyk.trans hkψ, ?_⟩
  by_cases hz : M.psi y - g y ≤ 0
  · exact Or.inl hz
  · right
    have hc : 0 < M.psi y - g y := lt_of_not_ge hz
    have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyk.le.trans hk.2⟩
    have h1 : M.psi y - g y ≤ M.psi k - g k := hg.mono_sub hyK hk hyk.le
    have h2 : M.psi y - g y ≤ M.psi k - y := by linarith
    have h3 : M.U' (M.psi k - y) ≤ M.U' (M.psi y - g y) :=
      M.U'_strictAntiOn.antitoneOn hc (hc.trans_le h2) h2
    have h4 : M.U' (M.psi y - g y) < M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y) :=
      lt_mul_left (M.U'_pos hc) (M.one_lt_euler hy0 (hyk.trans_le hks))
    simp only [Rd]
    linarith

/-- (5)–(6) for `Tg`, upper half: if `k ≥ k*` and `g(k) ≤ k` then `(Tg)(k) ≤ k`. -/
theorem IsInF.Tval_le {g : ℝ → ℝ} (hg : M.IsInF g) {k : ℝ} (hk : k ∈ Icc 0 M.kbar)
    (hks : M.kstar ≤ k) (hgk : g k ≤ k) : M.Tval g k ≤ k := by
  refine Real.sSup_le (fun y hy => ?_) hk.1
  by_contra hyk
  have hyk := lt_of_not_ge hyk
  have hyK : y ∈ Icc 0 M.kbar := ⟨hy.1, hy.2.1.le.trans (M.psi_le_kbar hk)⟩
  have hyb : y < M.kbar := hy.2.1.trans_le (M.psi_le_kbar hk)
  have hgy : g y ≤ y := hg.le_self y hyK (hks.trans_lt hyk)
  have hψy : y < M.psi y := M.lt_psi hy.1 hyb
  have h1 : M.psi k - g k ≤ M.psi y - g y := hg.mono_sub hk hyK hyk.le
  rcases hy.2.2 with h | h
  · simp only [Zd] at h
    linarith
  · have hc : 0 < M.psi k - y := by linarith [hy.2.1]
    have h2 : M.psi k - y ≤ M.psi y - g y := by linarith
    have h3 : M.U' (M.psi y - g y) ≤ M.U' (M.psi k - y) :=
      M.U'_strictAntiOn.antitoneOn hc (hc.trans_le h2) h2
    have hUp : 0 < M.U' (M.psi y - g y) := M.U'_pos (hc.trans_le h2)
    have h4 : M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - g y) < M.U' (M.psi y - g y) :=
      mul_lt_of_lt_one_left hUp (M.euler_lt_one (hks.trans_lt hyk))
    simp only [Rd] at h
    linarith

/-- **Exercise 18.5, `T : F → F`** (pointwise form): if `g` satisfies (2)–(6) so does `Tg`. -/
theorem IsInF.isInF_Tval {g : ℝ → ℝ} (hg : M.IsInF g) : M.IsInF (M.Tval g) where
  cont := by
    rw [Metric.continuousOn_iff]
    intro k0 hk0 ε hε
    obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1
      (M.psi_continuousOn.mono (Icc_subset_Ici_self : Icc (0 : ℝ) M.kbar ⊆ Ici 0)) k0 hk0 ε hε
    refine ⟨δ, hδ, fun k hk hd => ?_⟩
    rw [Real.dist_eq]
    have := hψ k hk hd
    rw [Real.dist_eq] at this
    exact (hg.abs_Tval_sub_le hk hk0).trans_lt this
  nonneg k hk := (M.Tval_mem_Icc g hk).1
  le_psi k hk := (M.Tval_mem_Icc g hk).2
  mono a ha b hb hab := hg.Tval_mono ha hb hab
  mono_sub a ha b hb hab := by
    have := hg.Tval_sub_le ha hb hab
    simp only
    linarith
  ge_self k hk hks := hg.le_Tval hk hks.le (hg.ge_self k hk hks)
  at_kstar := le_antisymm (hg.Tval_le M.kstar_mem le_rfl hg.at_kstar.le)
    (hg.le_Tval M.kstar_mem le_rfl hg.at_kstar.ge)
  le_self k hk hks := hg.Tval_le hk hks.le (hg.le_self k hk hks)

variable (M)

open Classical in
/-- **The operator `T`** on `C(K)` (§18.3 (7)): `T h = (k ↦ (T(ext h))(k))` for `h ∈ F`; off `F`
it is the identity (its values there play no role). -/
noncomputable def T (h : Icc 0 M.kbar →ᵇ ℝ) : Icc 0 M.kbar →ᵇ ℝ :=
  if hh : h ∈ M.F then M.toBCF (M.Tval (M.ext h)) (IsInF.isInF_Tval hh).cont else h

variable {M}

/-- `T h` evaluates pointwise as `Tval`. -/
theorem T_apply {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) (k : Icc 0 M.kbar) :
    M.T h k = M.Tval (M.ext h) k := by
  simp only [T, hh, ↓reduceDIte, toBCF_apply]

/-- `ext (T h)` agrees with `Tval (ext h)` on `K`. -/
theorem ext_T {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.ext (M.T h) k = M.Tval (M.ext h) k := by
  rw [ext_apply _ _ hk, T_apply hh]

variable (M)

/-- **Exercise 18.5** (p. 556): `T` maps `F` into `F`. -/
theorem ex_18_5 : MapsTo M.T M.F M.F := fun _ hh =>
  (IsInF.isInF_Tval hh).congr fun _ hk => (ext_T hh hk).symm

/-- **Exercise 18.5** (p. 556), well-definedness in the corrected sense: for `h ∈ F` and
`k ∈ K`, either `(Th)(k)` is the unique solution of (7) with positive consumption in both
periods, or (7) has no such solution, `h = ψ` on `[0, ψ(k))` and `(Th)(k) = ψ(k)`. -/
theorem ex_18_5_wellDefined {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) (k : Icc 0 M.kbar) :
    (M.T h k < M.psi k ∧ 0 < M.psi (M.T h k) - M.ext h (M.T h k) ∧
      M.U' (M.psi k - M.T h k) = M.β * (1 - M.θ) * M.f' (M.T h k) *
        M.U' (M.psi (M.T h k) - M.ext h (M.T h k)) ∧
      ∀ y, 0 ≤ y → y < M.psi k → 0 < M.psi y - M.ext h y →
        M.U' (M.psi k - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - M.ext h y) →
        y = M.T h k) ∨
    (M.T h k = M.psi k ∧ ∀ y, 0 ≤ y → y < M.psi k → M.ext h y = M.psi y) := by
  rw [T_apply hh]
  exact IsInF.Tval_spec hh k.2

/-- **Exercise 18.7** (p. 558): `T` is monotone on `F`: `h ≤ ĥ` implies `Th ≤ Tĥ`. -/
theorem ex_18_7 : MonotoneOn M.T M.F := by
  intro h hh h' hh' hle k
  change M.T h k ≤ M.T h' k
  rw [T_apply hh, T_apply hh']
  have hk := k.2
  refine eulerCross_mono_rhs (fun y hy0 hyP hz => ?_) (fun y hy0 hyP hz hz' => ?_)
    ⟨0, le_rfl, M.psi_pos hk.1, IsInF.eulerBelow_zero hh hk⟩
  · have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyP.le.trans (M.psi_le_kbar hk)⟩
    have : h ⟨y, hyK⟩ ≤ h' ⟨y, hyK⟩ := hle ⟨y, hyK⟩
    simp only [Zd, ext_apply _ _ hyK] at hz ⊢
    linarith
  · have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyP.le.trans (M.psi_le_kbar hk)⟩
    have hle' : h ⟨y, hyK⟩ ≤ h' ⟨y, hyK⟩ := hle ⟨y, hyK⟩
    simp only [Zd, ext_apply _ _ hyK] at hz hz'
    have hc' : 0 < M.psi y - h' ⟨y, hyK⟩ := lt_of_not_ge hz'
    have hcc : M.psi y - h' ⟨y, hyK⟩ ≤ M.psi y - h ⟨y, hyK⟩ := by linarith
    have hU := M.U'_strictAntiOn.antitoneOn hc' (hc'.trans_le hcc) hcc
    simp only [Rd, ext_apply _ _ hyK]
    exact mul_le_mul_of_nonneg_left hU (mul_pos M.euler_coef_pos (M.f'_pos hy0)).le

/-- The pointwise step of **Exercise 18.6**: if `h' → h` in `F` then `(Th')(k) → (Th)(k)`
for every `k ∈ K` (the monotone crossing argument, with `h` evaluated at the unknown `y`). -/
theorem eventually_abs_Tval_sub_le {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) {k : ℝ}
    (hk : k ∈ Icc 0 M.kbar) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h' : M.F in 𝓝 ⟨h, hh⟩, |M.Tval (M.ext h') k - M.Tval (M.ext h) k| ≤ η := by
  have hP : 0 < M.psi k := M.psi_pos hk.1
  have hPB := M.psi_le_kbar hk
  refine eventually_abs_eulerCross_sub_le (Zs := fun h' : M.F => M.Zd (M.ext h'))
    (Rs := fun h' : M.F => M.Rd (M.ext h')) M.isMarginalUtility (IsInF.isEulerRHS hh)
    (fun h' => IsInF.isEulerRHS h'.2) hP hPB (fun y hy0 hyP => ?_) hη
  have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, hyP.le.trans hPB⟩
  have hcont : Tendsto (fun h' : M.F => M.ext h' y) (𝓝 ⟨h, hh⟩) (𝓝 (M.ext h y)) := by
    simp only [ext_apply _ _ hyK]
    exact ((continuous_eval_const _).comp continuous_subtype_val).tendsto _
  have hm : 0 < M.β * (1 - M.θ) * M.f' y := mul_pos M.euler_coef_pos (M.f'_pos hy0)
  constructor
  · intro hz M0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (M.U'_inada.eventually_gt_atTop (|M0| / (M.β * (1 - M.θ) * M.f' y)))
    filter_upwards [Metric.tendsto_nhds.1 hcont ε hε] with h' hd
    rw [Real.dist_eq] at hd
    simp only [Zd] at hz ⊢
    by_cases hz0 : M.psi y - M.ext h' y ≤ 0
    · exact Or.inl hz0
    · right
      have hc : 0 < M.psi y - M.ext h' y := lt_of_not_ge hz0
      have hU := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]
        linarith [(abs_lt.1 hd).1], hc⟩
      simp only [mem_ofPred_eq] at hU
      rw [div_lt_iff₀ hm] at hU
      simp only [Rd]
      linarith [le_abs_self M0]
  · intro hz
    have hc : 0 < M.psi y - M.ext h y := lt_of_not_ge hz
    have hcon : Tendsto (fun h' : M.F => M.psi y - M.ext h' y) (𝓝 ⟨h, hh⟩)
        (𝓝 (M.psi y - M.ext h y)) := tendsto_const_nhds.sub hcont
    refine ⟨(hcon.eventually_const_lt hc).mono fun h' hh' => not_le.2 hh', ?_⟩
    exact tendsto_const_nhds.mul
      ((M.U'_continuousOn.continuousAt (Ioi_mem_nhds hc)).tendsto.comp hcon)

/-- **Exercise 18.6** (p. 558): `T` is continuous on `F` (sup norm). Pointwise convergence
(`eventually_abs_Tval_sub_le`) becomes uniform because `T(F) ⊆ F` is equicontinuous and `K` is
covered by finitely many small balls. -/
theorem ex_18_6 : ContinuousOn M.T M.F := by
  rw [continuousOn_iff_continuous_domRestrict, Metric.continuous_iff']
  rintro ⟨h, hh⟩ ε hε
  obtain ⟨δ, hδ, hψ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := M.kbar)).uniformContinuousOn_of_continuous
      (M.psi_continuousOn.mono Icc_subset_Ici_self)) (ε / 4) (by linarith)
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := M.kbar)) hδ
  have hev : ∀ᶠ h' : M.F in 𝓝 ⟨h, hh⟩, ∀ i ∈ t,
      |M.Tval (M.ext h') i - M.Tval (M.ext h) i| ≤ ε / 4 :=
    (htfin.eventually_all).2 fun i hi => M.eventually_abs_Tval_sub_le hh (htK hi) (by linarith)
  filter_upwards [hev] with h' hh'
  change dist (M.T (h' : Icc 0 M.kbar →ᵇ ℝ)) (M.T h) < ε
  refine lt_of_le_of_lt ((dist_le (by linarith)).2 fun k => ?_) (by linarith : 3 * ε / 4 < ε)
  obtain ⟨i, hi, hki⟩ := mem_iUnion₂.1 (hcover k.2)
  have hiK := htK hi
  have hd : dist (M.psi k) (M.psi i) < ε / 4 := hψ k k.2 i hiK hki
  rw [Real.dist_eq] at hd
  have e1 := (IsInF.isInF_Tval h'.2).abs_sub_le k.2 hiK
  have e2 := (IsInF.isInF_Tval hh).abs_sub_le hiK k.2
  have e3 := hh' i hi
  rw [abs_sub_comm (M.psi i)] at e2
  rw [Real.dist_eq, T_apply h'.2, T_apply hh]
  calc |M.Tval (M.ext h') k - M.Tval (M.ext h) k|
      ≤ |M.Tval (M.ext h') k - M.Tval (M.ext h') i| +
          |M.Tval (M.ext h') i - M.Tval (M.ext h) i| +
          |M.Tval (M.ext h) i - M.Tval (M.ext h) k| := by
        have := abs_sub_le (M.Tval (M.ext h') k) (M.Tval (M.ext h') i) (M.Tval (M.ext h) k)
        have := abs_sub_le (M.Tval (M.ext h') i) (M.Tval (M.ext h) i) (M.Tval (M.ext h) k)
        linarith
    _ ≤ 3 * ε / 4 := by linarith

/-- `F` is compact (closed, and totally bounded by Arzelà–Ascoli and Proposition 18.5). -/
theorem F_isCompact : IsCompact M.F :=
  (totallyBounded_of_equicontinuous isCompact_univ.totallyBounded M.F_isBounded
    M.prop_18_5').isCompact_of_isClosed M.F_isClosed

/-- **Existence of an equilibrium** (p. 558, Schauder's Theorem): `T` has a fixed point in `F`,
i.e. a continuous `g ∈ F` solving (1). -/
theorem exists_equilibrium : ∃ g ∈ M.F, M.T g = g :=
  schauder M.F_isCompact M.F_convex M.F_nonempty M.ex_18_6 M.ex_18_5

variable {M} in
/-- At a fixed point of `T` in `F` consumption is positive everywhere: `(Tg)(k) < ψ(k)` for
all `k ∈ K`. (If consumption were zero at some `k`, then `g = ψ` on `[0, ψ(k))`, and since
fixed points propagate zero consumption upward, `g = ψ` up to `k*`, contradicting
`g(k*) = k* < ψ(k*)`.) -/
theorem IsInF.Tval_lt_psi_of_fixed {g : ℝ → ℝ} (hg : M.IsInF g)
    (hfix : ∀ k ∈ Icc 0 M.kbar, M.Tval g k = g k) {k : ℝ} (hk : k ∈ Icc 0 M.kbar) :
    M.Tval g k < M.psi k := by
  by_contra hcon
  have hTk : M.Tval g k = M.psi k := le_antisymm (M.Tval_mem_Icc g hk).2 (not_lt.1 hcon)
  -- `A`: the `z ∈ [0, k̄]` with `g = ψ` on `[0, z)`
  set A := {z : ℝ | 0 ≤ z ∧ z ≤ M.kbar ∧ ∀ y, 0 ≤ y → y < z → g y = M.psi y}
  have hcase : ∀ z ∈ Icc 0 M.kbar, M.Tval g z = M.psi z → M.psi z ∈ A := by
    intro z hz hTz
    rcases hg.Tval_spec hz with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · exact ⟨(M.psi_pos hz.1).le, M.psi_le_kbar hz, h2⟩
  have hkA : M.psi k ∈ A := hcase k hk hTk
  have hgk : g M.kstar ≠ M.psi M.kstar := by
    rw [hg.at_kstar]; exact (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).ne
  have hAle : ∀ z ∈ A, z ≤ M.kstar := fun z hz => by
    by_contra hzk
    exact hgk (hz.2.2 M.kstar M.kstar_pos.le (lt_of_not_ge hzk))
  have hAne : A.Nonempty := ⟨_, hkA⟩
  have hAbdd : BddAbove A := ⟨M.kstar, hAle⟩
  set s := sSup A
  have hs0 : 0 < s := (M.psi_pos hk.1).trans_le (le_csSup hAbdd hkA)
  have hsk : s ≤ M.kstar := csSup_le hAne hAle
  -- every `y ∈ [0, s)` has `g y = ψ y`, hence `ψ y ∈ A`, hence `ψ y ≤ s`
  have hbelow : ∀ y, 0 ≤ y → y < s → M.psi y ≤ s := by
    intro y hy0 hys
    obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hAne hys
    have hyK : y ∈ Icc 0 M.kbar := ⟨hy0, (hyz.trans_le hz.2.1).le⟩
    have hgy : g y = M.psi y := hz.2.2 y hy0 hyz
    exact le_csSup hAbdd (hcase y hyK ((hfix y hyK).trans hgy))
  have hψs : M.psi s ≤ s := by
    have hc : ContinuousAt M.psi s := M.psi_continuousOn.continuousAt (Ici_mem_nhds hs0)
    refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio s))) ?_
    filter_upwards [Ioo_mem_nhdsLT hs0] with y hy
    exact hbelow y hy.1.le hy.2
  linarith [M.lt_psi_of_le_kstar hs0.le hsk]

/-- **Fixed points of `T` are the equilibria** (p. 556): `h ∈ F` is a fixed point of `T` iff the
Euler equation (1) holds at every `k ∈ K`, with positive consumption `ψ(k) − h(k)` today and
`ψ(h(k)) − h(h(k))` tomorrow. -/
theorem isFixedPt_iff_euler {h : Icc 0 M.kbar →ᵇ ℝ} (hh : h ∈ M.F) :
    M.T h = h ↔ ∀ k ∈ Icc 0 M.kbar, 0 < M.psi k - M.ext h k ∧
      0 < M.psi (M.ext h k) - M.ext h (M.ext h k) ∧
      M.U' (M.psi k - M.ext h k) =
        M.β * (1 - M.θ) * M.f' (M.ext h k) * M.U' (M.psi (M.ext h k) - M.ext h (M.ext h k)) := by
  have hg : M.IsInF (M.ext h) := hh
  constructor
  · intro hfix
    have hfix' : ∀ k ∈ Icc 0 M.kbar, M.Tval (M.ext h) k = M.ext h k := fun k hk => by
      rw [← ext_T hh hk, hfix]
    intro k hk
    rcases hg.Tval_spec hk with ⟨h1, h2, h3, -⟩ | ⟨h1, -⟩
    · rw [hfix' k hk] at h1 h2 h3
      exact ⟨by linarith, h2, h3⟩
    · exact absurd h1 (hg.Tval_lt_psi_of_fixed hfix' hk).ne
  · intro heq
    ext k
    rw [T_apply hh, ← ext_apply _ _ k.2]
    obtain ⟨h1, h2, h3⟩ := heq k k.2
    rcases hg.Tval_spec k.2 with ⟨-, -, -, huniq⟩ | ⟨-, h5⟩
    · exact (huniq _ (hg.nonneg k k.2) (by linarith) h2 h3).symm
    · exact absurd (h5 _ (hg.nonneg k k.2) (by linarith)) (by linarith)

/-- `T(F)` is equicontinuous (it is contained in `F`, Proposition 18.5). -/
theorem T_equicontinuous : UniformEquicontinuous fun h : M.F => ⇑(M.T h) :=
  M.prop_18_5.comp fun h : M.F => (⟨M.T h, M.ex_18_5 h.2⟩ : M.F)

/-- **Least and greatest equilibria** (p. 558, Exercise 18.7 with Theorem 17.7 and its
Corollary, corrected): `Tⁿh_` converges in `C(K)` to the least fixed point of `T` in `F`, and
`Tⁿū` (not `Tⁿh̄`, since `h̄ ∉ F`) converges to the greatest one; every fixed point lies between
them. -/
theorem least_greatest_equilibria :
    ∃ f ∈ M.F, ∃ g ∈ M.F, M.T f = f ∧ M.T g = g ∧
      Tendsto (fun n => M.T^[n] (M.toBCF M.low M.isInF_low.cont)) atTop (𝓝 f) ∧
      Tendsto (fun n => M.T^[n] (M.toBCF M.up M.isInF_up.cont)) atTop (𝓝 g) ∧
      ∀ h ∈ M.F, M.T h = h → f ≤ h ∧ h ≤ g :=
  corollary_17_7 isCompact_univ.totallyBounded M.F_isClosed M.F_isBounded M.ex_18_5 M.ex_18_6
    M.ex_18_7 M.T_equicontinuous M.isLeast_low M.isGreatest_up

/-- **Uniqueness test** (p. 558): if the iterates from `h_` and from `ū` have the same limit,
that limit is the only fixed point of `T` in `F`. -/
theorem unique_equilibrium_of_tendsto {f : Icc 0 M.kbar →ᵇ ℝ}
    (hl : Tendsto (fun n => M.T^[n] (M.toBCF M.low M.isInF_low.cont)) atTop (𝓝 f))
    (hu : Tendsto (fun n => M.T^[n] (M.toBCF M.up M.isInF_up.cont)) atTop (𝓝 f)) :
    f ∈ M.F ∧ M.T f = f ∧ ∀ h ∈ M.F, M.T h = h → h = f :=
  corollary_17_7_unique isCompact_univ.totallyBounded M.F_isClosed M.F_isBounded M.ex_18_5
    M.ex_18_6 M.ex_18_7 M.T_equicontinuous M.isLeast_low M.isGreatest_up hl hu

/-- The iterates `Tⁿh_` increase (the computational algorithm of p. 554). -/
theorem monotone_iterate_low : Monotone fun n => M.T^[n] (M.toBCF M.low M.isInF_low.cont) :=
  monotone_iterate_of_le M.ex_18_5 M.ex_18_7 M.isLeast_low.1
    (M.isLeast_low.2 (M.ex_18_5 M.isLeast_low.1))

/-- The iterates `Tⁿū` decrease. -/
theorem antitone_iterate_up : Antitone fun n => M.T^[n] (M.toBCF M.up M.isInF_up.cont) :=
  antitone_iterate_of_ge M.ex_18_5 M.ex_18_7 M.isGreatest_up.1
    (M.isGreatest_up.2 (M.ex_18_5 M.isGreatest_up.1))

/-! ### NOTE 18.3-E: (7) need not have a solution -/

/-- The member `h(k) = min{ψ(k), k*}` of `F` used in NOTE 18.3-E (it equals the book's `h̄` on
`[0, k*]` and is `k*` beyond). -/
noncomputable def hE (k : ℝ) : ℝ := min (M.psi k) M.kstar

/-- `hE` satisfies (2)–(6). -/
theorem isInF_hE : M.IsInF M.hE where
  cont := ContinuousOn.inf (M.psi_continuousOn.mono Icc_subset_Ici_self) continuousOn_const
  nonneg k hk := le_min (M.psi_pos hk.1).le M.kstar_pos.le
  le_psi _ _ := min_le_left _ _
  mono x hx y hy hxy :=
    min_le_min_right _ (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy)
  mono_sub x hx y hy hxy := by
    have := M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
    simp only [hE]
    rcases le_total (M.psi x) M.kstar with h1 | h1 <;>
      rcases le_total (M.psi y) M.kstar with h2 | h2 <;>
      simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith
  ge_self k hk hks := le_min (M.lt_psi_of_le_kstar hk.1 hks.le).le hks.le
  at_kstar := min_eq_right (M.lt_psi_of_le_kstar M.kstar_pos.le le_rfl).le
  le_self _ _ hks := (min_le_right _ _).trans hks.le

/-- **Correction to Exercise 18.5** (NOTE 18.3-E): if `ψ(ψ(0)) ≤ k*`, then for the member
`hE = min{ψ, k*}` of `F` the equation (7) at `k = 0` has no solution `y ∈ [0, ψ(0))` with
positive next-period consumption (the right side is `+∞` on all of `[0, ψ(0)]`), and the operator
takes the extended-real value `(T hE)(0) = ψ(0)`. -/
theorem ex_18_5_counterexample_of (hψψ : M.psi (M.psi 0) ≤ M.kstar) :
    M.IsInF M.hE ∧
      (¬ ∃ y, 0 ≤ y ∧ y < M.psi 0 ∧ 0 < M.psi y - M.hE y ∧
        M.U' (M.psi 0 - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - M.hE y)) ∧
      M.Tval M.hE 0 = M.psi 0 := by
  have hzero : ∀ y, 0 ≤ y → y < M.psi 0 → M.psi y - M.hE y = 0 := by
    intro y hy0 hy
    have : M.psi y ≤ M.kstar :=
      (M.psi_strictMonoOn.monotoneOn (mem_Ici.2 hy0) (mem_Ici.2 (M.psi_pos le_rfl).le)
        hy.le).trans hψψ
    simp only [hE, min_eq_left this, sub_self]
  refine ⟨M.isInF_hE, ?_, ?_⟩
  · rintro ⟨y, hy0, hy, hc, -⟩
    rw [hzero y hy0 hy] at hc
    exact lt_irrefl _ hc
  · rcases M.isInF_hE.Tval_spec ⟨le_rfl, M.kbar_pos.le⟩ with ⟨h1, h2, -⟩ | ⟨h1, -⟩
    · exact absurd (hzero _ (M.Tval_mem_Icc _ ⟨le_rfl, M.kbar_pos.le⟩).1 h1) h2.ne'
    · exact h1

end GlobalModel

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 18.9: a continuum of shocks (SLP p. 560)

Exercise 18.9 asks how the assumptions or arguments must be modified when the shock space `Ξ`
is a closed bounded interval. Here `Ξ` is any nonempty compact metric space with its Borel
σ-algebra (a closed bounded interval is one). The modified assumptions (`ContModel`) are:
* each shock `ξ` has a technology `tech ξ` satisfying Assumptions 18.1 and 18.2 (a
  `GlobalModel`), with common `β`, `θ`, `U`, and `k̄(ξ) ≤ B`;
* `ψ(k, ξ)` and `f′(k, ξ)` are **jointly continuous** on `[0, B] × Ξ`;
* the transition `κ(ξ, ·)` is a probability measure with the **Feller property**:
  `ξ ↦ ∫ g dκ(ξ)` is continuous for every continuous `g`.

The sum in (9) becomes an integral,
  `RHS_ξ(y) = β(1 − θ) ∫ f′(y, ξ′) U′[ψ(y, ξ′) − h(ξ′, y)] κ(ξ, dξ′)`,
and the set `F` is modified to `F₊` (`IsInFc`): `h` is jointly continuous on `[0, B] × Ξ`,
`0 ≤ h < ψ`, and `h(ξ, ·)` and `ψ(·, ξ) − h(ξ, ·)` are nondecreasing.

* `IsInFc.isEulerRHS`: for `h ∈ F₊` the right side is finite and continuous in `y`.
* `ex_18_9_spec_KT`: `T` is well defined (in Kuhn–Tucker form); `(Th)(k, ξ)` is an interior
  solution of the integral Euler equation or a zero-saving corner.
* `ex_18_9_spec`: under the integral cross-state condition `CrossState` the corner is excluded,
  and `(Th)(k, ξ)` is the unique interior solution.
* `ex_18_9` (**Exercise 18.9**): `T` maps `F₊` into `F₊`. Joint continuity of `Th` in `(k, ξ)`
  uses the Feller property and the continuity of the crossing point (`GlobalCrossing`).
* `ex_18_9_mono`: `T` is monotone on `F₊`.

**Why `F₊` (strictly positive consumption) instead of `0 ≤ h ≤ ψ`.** With a finite shock
space, zero consumption in a reachable state makes the right side of (9) infinite. With a
continuum this fails: if `ψ(y, ·) − h(·, y)` vanishes only on a null set, the integral can stay
finite (for `U = √`, `U′(c) = c^{-1/2}` is integrable near a simple zero). The Inada blow-up
that drives the finite-shock argument then breaks. Excluding zero consumption also excludes the
degenerate fixed point `h = ψ` of the finite case (`StochModel.Ts_psi`).

**Not proved.** Existence of a fixed point in the continuum case: `F₊` is not closed, and no
invariant closed convex subset bounded away from zero consumption has been found (the same
obstacle as for finite `Ξ`, `GlobalStochasticEquilibrium`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology MeasureTheory

variable (Ξ : Type) [MetricSpace Ξ] [CompactSpace Ξ] [Nonempty Ξ] [MeasurableSpace Ξ]
  [BorelSpace Ξ] in
/-- **The continuum-shock model** (Exercise 18.9): per-shock technologies satisfying
Assumptions 18.1 and 18.2, jointly continuous `ψ` and `f′`, and a Feller probability
transition `κ`. -/
structure ContModel where
  tech : Ξ → GlobalModel
  β : ℝ
  θ : ℝ
  U : ℝ → ℝ
  U' : ℝ → ℝ
  B : ℝ
  κ : Ξ → Measure Ξ
  tech_β : ∀ ξ, (tech ξ).β = β
  tech_θ : ∀ ξ, (tech ξ).θ = θ
  tech_U : ∀ ξ, (tech ξ).U = U
  tech_U' : ∀ ξ, (tech ξ).U' = U'
  kbar_le : ∀ ξ, (tech ξ).kbar ≤ B
  κ_prob : ∀ ξ, IsProbabilityMeasure (κ ξ)
  κ_feller : ∀ g : Ξ → ℝ, Continuous g → Continuous fun ξ => ∫ x, g x ∂(κ ξ)
  psi_cont : ContinuousOn (fun p : ℝ × Ξ => (tech p.2).psi p.1) (Icc 0 B ×ˢ univ)
  f'_cont : ContinuousOn (fun p : ℝ × Ξ => (tech p.2).f' p.1) (Icc 0 B ×ˢ univ)

namespace ContModel

variable {Ξ : Type} [MetricSpace Ξ] [CompactSpace Ξ] [Nonempty Ξ] [MeasurableSpace Ξ]
  [BorelSpace Ξ] (C : ContModel Ξ)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `B > 0`. -/
theorem B_pos : 0 < C.B :=
  (C.tech (Classical.arbitrary Ξ)).kbar_pos.trans_le (C.kbar_le _)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The common marginal utility is a marginal utility. -/
theorem isMarginalUtility : IsMarginalUtility C.U' := by
  rw [← C.tech_U' (Classical.arbitrary Ξ)]; exact (C.tech _).isMarginalUtility

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `β(1 − θ) > 0`. -/
theorem coef_pos : 0 < C.β * (1 - C.θ) := by
  rw [← C.tech_β (Classical.arbitrary Ξ), ← C.tech_θ (Classical.arbitrary Ξ)]
  exact (C.tech _).euler_coef_pos

omit [CompactSpace Ξ] [BorelSpace Ξ] [Nonempty Ξ] in
/-- `ψ(·, ξ)` maps `[0, B]` into `(0, B]`. -/
theorem psi_le_B (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) : (C.tech ξ).psi k ≤ C.B := by
  rcases le_or_gt k (C.tech ξ).kbar with h | h
  · exact ((C.tech ξ).psi_le_kbar ⟨hk.1, h⟩).trans (C.kbar_le ξ)
  · exact ((C.tech ξ).psi_lt k h).le.trans hk.2

/-- **The set `F₊`** (`F` of p. 559 with positive consumption): `h` jointly continuous on
`[0, B] × Ξ`, `0 ≤ h < ψ`, `h(ξ, ·)` and `ψ(·, ξ) − h(ξ, ·)` nondecreasing. -/
structure IsInFc (h : Ξ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × Ξ => h p.2 p.1) (Icc 0 C.B ×ˢ univ)
  nonneg : ∀ ξ, ∀ k ∈ Icc 0 C.B, 0 ≤ h ξ k
  lt_psi : ∀ ξ, ∀ k ∈ Icc 0 C.B, h ξ k < (C.tech ξ).psi k
  mono : ∀ ξ, MonotoneOn (h ξ) (Icc 0 C.B)
  mono_sub : ∀ ξ, MonotoneOn (fun k => (C.tech ξ).psi k - h ξ k) (Icc 0 C.B)

/-- The integrand of the right side of the Euler equation: `f′(y, x) U′[ψ(y, x) − h(x, y)]`. -/
noncomputable def G (h : Ξ → ℝ → ℝ) (y : ℝ) (x : Ξ) : ℝ :=
  (C.tech x).f' y * C.U' ((C.tech x).psi y - h x y)

/-- The right side of the Euler equation with a continuum of shocks:
`β(1 − θ) ∫ f′(y, x) U′[ψ(y, x) − h(x, y)] κ(ξ, dx)`. -/
noncomputable def Rc (h : Ξ → ℝ → ℝ) (ξ : Ξ) (y : ℝ) : ℝ :=
  C.β * (1 - C.θ) * ∫ x, C.G h y x ∂(C.κ ξ)

/-- **The operator `T`** with a continuum of shocks: the crossing point of `y ↦ U′[ψ(k, ξ) − y]`
and `Rc h ξ` (the right side is finite on `F₊`, so `Z ≡ False`). -/
noncomputable def Tc (h : Ξ → ℝ → ℝ) (ξ : Ξ) (k : ℝ) : ℝ :=
  eulerCross C.U' (fun _ => False) (C.Rc h ξ) ((C.tech ξ).psi k)

variable {C}

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The integrand is jointly continuous on `[0, B] × Ξ` for `h ∈ F₊`. -/
theorem IsInFc.G_continuousOn {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) :
    ContinuousOn (fun p : ℝ × Ξ => C.G h p.1 p.2) (Icc 0 C.B ×ˢ univ) := by
  have hc : ContinuousOn (fun p : ℝ × Ξ => (C.tech p.2).psi p.1 - h p.2 p.1)
      (Icc 0 C.B ×ˢ univ) := C.psi_cont.sub hh.cont
  have hU : ContinuousOn (fun p : ℝ × Ξ => C.U' ((C.tech p.2).psi p.1 - h p.2 p.1))
      (Icc 0 C.B ×ˢ univ) :=
    C.isMarginalUtility.cont.comp hc fun p hp => by
      simp only [mem_Ioi, sub_pos]
      exact hh.lt_psi p.2 p.1 hp.1
  exact C.f'_cont.mul hU

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- For fixed `y ∈ [0, B]` the integrand is continuous in the shock. -/
theorem IsInFc.G_continuous {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) {y : ℝ} (hy : y ∈ Icc 0 C.B) :
    Continuous fun x => C.G h y x :=
  hh.G_continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨hy, mem_univ _⟩

/-- For fixed `y ∈ [0, B]` the integrand is integrable. -/
theorem IsInFc.G_integrable {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) {y : ℝ} (hy : y ∈ Icc 0 C.B)
    (ξ : Ξ) : Integrable (fun x => C.G h y x) (C.κ ξ) := by
  have := C.κ_prob ξ
  exact (hh.G_continuous hy).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The right side is continuous in `y` on `[0, B]` (continuity of a parametric integral over the
compact `Ξ`). -/
theorem IsInFc.Rc_continuousOn {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) :
    ContinuousOn (C.Rc h ξ) (Icc 0 C.B) := by
  have := C.κ_prob ξ
  have hB := C.B_pos.le
  set g : ℝ → Ξ → ℝ := fun y x => C.G h (projIcc 0 C.B hB y) x
  have hg : Continuous (Function.uncurry g) :=
    hh.G_continuousOn.comp_continuous
      ((continuous_subtype_val.comp ((continuous_projIcc (h := hB)).comp continuous_fst)).prodMk
        continuous_snd) fun p => ⟨(projIcc 0 C.B hB p.1).2, mem_univ _⟩
  have hi := continuous_parametric_integral_of_continuous (μ := C.κ ξ) hg isCompact_univ
  have hc : Continuous fun y => C.β * (1 - C.θ) * ∫ x in univ, g y x ∂(C.κ ξ) :=
    continuous_const.mul hi
  refine hc.continuousOn.congr fun y hy => ?_
  simp only [Rc, g, Measure.restrict_univ, projIcc_of_mem hB hy]

/-- For `h ∈ F₊` the right side of the integral Euler equation is an `IsEulerRHS` on `[0, B]`
(finite, nonincreasing and continuous). -/
theorem IsInFc.isEulerRHS {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) :
    IsEulerRHS C.B (fun _ => False) (C.Rc h ξ) where
  zero_anti _ _ _ _ _ hz := hz
  anti y y' hy' hyy hyB _ := by
    have hyK : y ∈ Icc 0 C.B := ⟨hy'.trans hyy, hyB⟩
    have hy'K : y' ∈ Icc 0 C.B := ⟨hy', hyy.trans hyB⟩
    refine mul_le_mul_of_nonneg_left (integral_mono (hh.G_integrable hyK ξ)
      (hh.G_integrable hy'K ξ) fun x => ?_) C.coef_pos.le
    have hc' : 0 < (C.tech x).psi y' - h x y' := by linarith [hh.lt_psi x y' hy'K]
    have hcc : (C.tech x).psi y' - h x y' ≤ (C.tech x).psi y - h x y :=
      hh.mono_sub x hy'K hyK hyy
    have hU := C.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : (C.tech x).f' y ≤ (C.tech x).f' y' :=
      (C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 hyK.1) hyy
    exact mul_le_mul hf hU (C.isMarginalUtility.pos _ (hc'.trans_le hcc)).le
      ((C.tech x).f'_pos hy').le
  cont y hy _ := ⟨Eventually.of_forall fun _ hz => hz, hh.Rc_continuousOn ξ y hy⟩
  blowup _ _ hz := hz.elim

/-- **Exercise 18.9, Kuhn–Tucker form.** For `h ∈ F₊`, a current shock `ξ` and `k ∈ [0, B]`,
either `y = (Th)(k, ξ) < ψ(k, ξ)` solves the integral Euler equation, or `y = 0` is a zero-saving
corner with `RHS(0) ≤ U′(ψ(k, ξ))`. -/
theorem ex_18_9_spec_KT {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) {k : ℝ}
    (hk : k ∈ Icc 0 C.B) :
    (C.Tc h ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.Tc h ξ k) = C.Rc h ξ (C.Tc h ξ k)) ∨
    (C.Tc h ξ k = 0 ∧ C.Rc h ξ 0 ≤ C.U' ((C.tech ξ).psi k)) := by
  have hP := (C.tech ξ).psi_pos hk.1
  rcases eulerCross_spec_KT C.isMarginalUtility (hh.isEulerRHS ξ) hP (C.psi_le_B ξ hk) with
    ⟨h1, -, h3⟩ | ⟨-, h2⟩ | ⟨h1, -, h3⟩
  · exact Or.inl ⟨h1, h3⟩
  · exact (h2 0 le_rfl hP).elim
  · exact Or.inr ⟨h1, h3⟩

variable (C)

/-- The integral **cross-state condition**:
`U′(ψ(0, ξ)) < β(1 − θ) ∫ f′(0, x) U′(ψ(0, x)) κ(ξ, dx)` for every `ξ`. -/
def CrossState : Prop :=
  ∀ ξ, C.U' ((C.tech ξ).psi 0) <
    C.β * (1 - C.θ) * ∫ x, (C.tech x).f' 0 * C.U' ((C.tech x).psi 0) ∂(C.κ ξ)

omit [CompactSpace Ξ] [BorelSpace Ξ] [Nonempty Ξ] in
/-- The least element `h ≡ 0` of `F₊`. -/
theorem isInFc_zero : C.IsInFc fun _ _ => 0 where
  cont := continuousOn_const
  nonneg _ _ _ := le_rfl
  lt_psi ξ k hk := (C.tech ξ).psi_pos hk.1
  mono _ := fun _ _ _ _ _ => le_rfl
  mono_sub ξ := fun a ha b hb hab => by
    simp only [sub_zero]
    exact (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab

variable {C}

/-- **Exercise 18.9, equation form.** Under the cross-state condition, `(Th)(k, ξ)` is the
unique `y ∈ [0, ψ(k, ξ))` solving the integral Euler equation. -/
theorem ex_18_9_spec (hCS : C.CrossState) {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) {k : ℝ}
    (hk : k ∈ Icc 0 C.B) :
    C.Tc h ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.Tc h ξ k) = C.Rc h ξ (C.Tc h ξ k) ∧
      ∀ y, 0 ≤ y → y < (C.tech ξ).psi k →
        C.U' ((C.tech ξ).psi k - y) = C.Rc h ξ y → y = C.Tc h ξ k := by
  have hP := (C.tech ξ).psi_pos hk.1
  have hPB := C.psi_le_B ξ hk
  have h0K : (0 : ℝ) ∈ Icc 0 C.B := ⟨le_rfl, C.B_pos.le⟩
  have h0 : EulerBelow C.U' (fun _ => False) (C.Rc h ξ) ((C.tech ξ).psi k) 0 := by
    right
    have := C.κ_prob ξ
    have hz : (fun x => (C.tech x).f' 0 * C.U' ((C.tech x).psi 0)) =
        fun x => C.G (fun _ _ => 0) 0 x := by
      funext x; simp [G]
    have hint : Integrable (fun x => (C.tech x).f' 0 * C.U' ((C.tech x).psi 0)) (C.κ ξ) := by
      rw [hz]; exact (C.isInFc_zero).G_integrable h0K ξ
    have hle : ∫ x, (C.tech x).f' 0 * C.U' ((C.tech x).psi 0) ∂(C.κ ξ) ≤
        ∫ x, C.G h 0 x ∂(C.κ ξ) := by
      refine integral_mono hint (hh.G_integrable h0K ξ) fun x => ?_
      have hc : 0 < (C.tech x).psi 0 - h x 0 := by linarith [hh.lt_psi x 0 h0K]
      have hle' : (C.tech x).psi 0 - h x 0 ≤ (C.tech x).psi 0 := by
        linarith [hh.nonneg x 0 h0K]
      exact mul_le_mul_of_nonneg_left
        (C.isMarginalUtility.strictAnti.antitoneOn hc ((C.tech x).psi_pos le_rfl) hle')
        ((C.tech x).f'_pos le_rfl).le
    have hψ := (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have h2 : C.U' ((C.tech ξ).psi k) ≤ C.U' ((C.tech ξ).psi 0) :=
      C.isMarginalUtility.strictAnti.antitoneOn ((C.tech ξ).psi_pos le_rfl)
        ((C.tech ξ).psi_pos hk.1) hψ
    have h3 := mul_le_mul_of_nonneg_left hle C.coef_pos.le
    have h4 := hCS ξ
    simp only [Rc, sub_zero]
    linarith
  rcases eulerCross_spec C.isMarginalUtility (hh.isEulerRHS ξ) hP hPB h0 with
    ⟨h1, -, h3⟩ | ⟨-, h2⟩
  · exact ⟨h1, h3, fun y hy0 hyP heq =>
      (eulerCross_unique C.isMarginalUtility (hh.isEulerRHS ξ) hPB hy0 hyP (fun hz => hz)
        heq).symm⟩
  · exact (h2 0 le_rfl hP).elim

/-- **Exercise 18.9: `T` maps `F₊` into `F₊`.** Joint continuity of `Th` in `(k, ξ)` comes from
the Feller property (the right side moves continuously with the current shock) and the
`1`-Lipschitz dependence of the crossing point on current resources `ψ(k, ξ)`. -/
theorem ex_18_9 {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) : C.IsInFc fun ξ k => C.Tc h ξ k where
  cont := by
    intro p hp
    have hk : p.1 ∈ Icc 0 C.B := hp.1
    set P0 := (C.tech p.2).psi p.1 with hP0def
    have hP0 : 0 < P0 := (C.tech p.2).psi_pos hk.1
    have hP0B : P0 ≤ C.B := C.psi_le_B p.2 hk
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hev := eventually_abs_eulerCross_sub_le (u := C.U') (l := 𝓝 p.2)
      (Zs := fun _ _ => False) (Rs := fun ξ => C.Rc h ξ) C.isMarginalUtility
      (hh.isEulerRHS p.2) (fun ξ => hh.isEulerRHS ξ) hP0 hP0B
      (fun y hy0 hyP => ⟨fun hz => hz.elim, fun _ => ⟨Eventually.of_forall fun _ hz => hz,
        tendsto_const_nhds.mul ((C.κ_feller _
          (hh.G_continuous ⟨hy0, hyP.le.trans hP0B⟩)).tendsto p.2)⟩⟩) (half_pos hε)
    obtain ⟨δ1, hδ1, hball⟩ := Metric.mem_nhds_iff.1 hev
    obtain ⟨δ2, hδ2, hψ⟩ := Metric.continuousWithinAt_iff.1 (C.psi_cont p hp) (ε / 2)
      (half_pos hε)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun q hq hd => ?_⟩
    have hqp : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hd2 : dist q.2 p.2 < δ1 := lt_of_le_of_lt hqp (hd.trans_le (min_le_left _ _))
    have e1 : |eulerCross C.U' (fun _ => False) (C.Rc h q.2) P0 - C.Tc h p.2 p.1| ≤ ε / 2 :=
      hball hd2
    have e2 := hψ hq (hd.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at e2
    have e3 := abs_eulerCross_sub_le C.isMarginalUtility (hh.isEulerRHS q.2) hP0B
      (C.psi_le_B q.2 hq.1)
    rw [Real.dist_eq]
    change |C.Tc h q.2 q.1 - C.Tc h p.2 p.1| < ε
    have := abs_sub_le (C.Tc h q.2 q.1) (eulerCross C.U' (fun _ => False) (C.Rc h q.2) P0)
      (C.Tc h p.2 p.1)
    simp only [Tc, ← hP0def] at this e1 e3 ⊢
    linarith
  nonneg ξ k hk := eulerCross_nonneg
  lt_psi ξ k hk := by
    rcases ex_18_9_spec_KT hh ξ hk with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · rw [h1]; exact (C.tech ξ).psi_pos hk.1
  mono ξ a ha b hb hab := eulerCross_mono' C.isMarginalUtility (hh.isEulerRHS ξ)
    ((C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab)
    (C.psi_le_B ξ hb)
  mono_sub ξ a ha b hb hab := by
    have := eulerCross_le_add_sub C.isMarginalUtility (hh.isEulerRHS ξ)
      ((C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab)
      (C.psi_le_B ξ hb)
    simp only [Tc] at this ⊢
    linarith

/-- **`T` is monotone on `F₊`** with a continuum of shocks (the analogue of Exercise 18.7). -/
theorem ex_18_9_mono {h h' : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (hh' : C.IsInFc h')
    (hle : ∀ ξ, ∀ k ∈ Icc 0 C.B, h ξ k ≤ h' ξ k) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.Tc h ξ k ≤ C.Tc h' ξ k := by
  have hPB := C.psi_le_B ξ hk
  refine eulerCross_mono_rhs' (fun _ _ _ hz => hz) (fun y hy0 hyP _ _ => ?_)
  have hyK : y ∈ Icc 0 C.B := ⟨hy0, hyP.le.trans hPB⟩
  refine mul_le_mul_of_nonneg_left (integral_mono (hh.G_integrable hyK ξ)
    (hh'.G_integrable hyK ξ) fun x => ?_) C.coef_pos.le
  have hc' : 0 < (C.tech x).psi y - h' x y := by linarith [hh'.lt_psi x y hyK]
  have hcc : (C.tech x).psi y - h' x y ≤ (C.tech x).psi y - h x y := by
    linarith [hle x y hyK]
  exact mul_le_mul_of_nonneg_left
    (C.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc)
    ((C.tech x).f'_pos hy0).le

end ContModel

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Concrete models for SLP §18.3: the corrected assumptions are consistent, and two of the book's
claims fail

All models use `U(c) = √c` (continuous on `[0, ∞)`, `C²` on `(0, ∞)`, `U′(c) = 1/(2√c) → ∞`), so
they satisfy Assumptions 18.1 and 18.2 in the corrected reading of `GlobalModel` — the reading
forced by `assumption_18_2_contradiction`.

* `ratModel`: technologies `f(k) = b + a k/(1 + k)`, with
  `ψ(k) − k = (k̄ − k)(k² + p k + q)/(1 + k)²` whenever the coefficients match
  (`ratTech_psi_sub`). This gives Assumption 18.1e with an explicit `k̄`.
* `modelE` (`b = 1/50`, `a = 891/250`, `θ = 1/2`, `β = 9/10`, `k̄ = 2`): `ψ(ψ(0)) ≤ k*`.
* `ex_18_5_counterexample` (**Correction**, NOTE 18.3-E): in `modelE` the member
  `min{ψ, k*}` of `F` makes (7) at `k = 0` have no solution with positive consumption, so `T`
  is not well defined on `F` as "the `y` solving (7)".
* `modelL` (`f(k) = 3 + 4 ∫₀ᵏ ds/(1 + s⁸)`, `θ = 1/2`, `β = 9/10`, `k̄` the root of `ψ(k) = k` in
  `(2, 20)`).
* `prop_18_5_bound_counterexample` (**Correction**, proof of Proposition 18.5, p. 557): in
  `modelL`, `ψ(1) − ψ(9/10) > f′(0) · (1 − 9/10)`, so the book's bound
  `|ψ(k′) − ψ(k)| ≤ A |k′ − k|` with `A = f′(0)` fails.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

/-! ### The utility `U(c) = √c` -/

/-- `√` is `C²` on `(0, ∞)`. -/
theorem sqrt_contDiffOn : ContDiffOn ℝ 2 (fun c : ℝ => √c) (Ioi 0) :=
  fun _ hx => (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt

/-- `√` is strictly increasing on `[0, ∞)`. -/
theorem sqrt_strictMonoOn : StrictMonoOn (fun c : ℝ => √c) (Ici 0) :=
  fun _ hx _ _ hxy => Real.sqrt_lt_sqrt hx hxy

/-- The derivative of `√` on `(0, ∞)` is `1/(2√c)`. -/
theorem sqrt_hasDerivAt {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun c : ℝ => √c) (1 / (2 * √c)) c :=
  Real.hasDerivAt_sqrt hc.ne'

/-- The Inada condition for `U = √`: `1/(2√c) → ∞` as `c → 0⁺`. -/
theorem sqrt_inada : Tendsto (fun c : ℝ => 1 / (2 * √c)) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun c : ℝ => 2 * √c) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun c : ℝ => 2 * √c) (𝓝 0) (𝓝 (2 * √0)) :=
        (continuous_const.mul Real.continuous_sqrt).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact mul_pos two_pos (Real.sqrt_pos.2 hc)
  exact (tendsto_inv_nhdsGT_zero.comp h1).congr fun c => by simp [one_div]

/-! ### Rational technologies `f(k) = b + a k/(1 + k)` -/

/-- The derivative of `b + a k/(1 + k)` is `a/(1 + k)²` (for `k > −1`). -/
theorem ratTech_hasDerivAt (a b : ℝ) {k : ℝ} (hk : -1 < k) :
    HasDerivAt (fun k => b + a * k / (1 + k)) (a / (1 + k) ^ 2) k := by
  have h1 : HasDerivAt (fun k => a * k) a k := by simpa using (hasDerivAt_id k).const_mul a
  have h2 : HasDerivAt (fun k => 1 + k) 1 k := by simpa using (hasDerivAt_id k).const_add 1
  have h3 := (h1.div h2 (by linarith : (1 + k) ≠ 0)).const_add b
  convert h3 using 1
  field_simp
  ring

/-- `ψ(k) − k` for a rational technology, as a quotient of polynomials. -/
theorem ratTech_psi_sub {a b θ kbar p q : ℝ} (h1 : b = kbar * q) (h2 : kbar - p = b + a - 2)
    (h3 : kbar * p - q = 2 * b + a * (1 - θ) - 1) {k : ℝ} (hk : 0 ≤ k) :
    (b + a * k / (1 + k)) - θ * k * (a / (1 + k) ^ 2) - k =
      (kbar - k) * (k ^ 2 + p * k + q) / (1 + k) ^ 2 := by
  have hpoly : b * (1 + k) ^ 2 + a * k * (1 + k) - θ * k * a - k * (1 + k) ^ 2 =
      (kbar - k) * (k ^ 2 + p * k + q) := by
    linear_combination (-k ^ 2) * h2 + (-k) * h3 + h1
  rw [← hpoly]
  have : (1 + k) ≠ 0 := by linarith
  field_simp

/-- **A model with a rational technology.** `U = √`, `f(k) = b + a k/(1 + k)`, with coefficients
making `ψ(k) − k = (k̄ − k)(k² + p k + q)/(1 + k)²`. -/
noncomputable def ratModel (β θ a b kbar p q : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (ha : 1 / (β * (1 - θ)) < a) (hb : 0 < b) (hkbar : 0 < kbar) (hp : 0 ≤ p)
    (hq : 0 < q) (h1 : b = kbar * q) (h2 : kbar - p = b + a - 2)
    (h3 : kbar * p - q = 2 * b + a * (1 - θ) - 1) : GlobalModel where
  β := β
  θ := θ
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  f := fun k => b + a * k / (1 + k)
  f' := fun k => a / (1 + k) ^ 2
  kbar := kbar
  β_pos := hβ0
  β_lt_one := hβ1
  U_cont := Real.continuous_sqrt.continuousOn
  U_contDiff := sqrt_contDiffOn
  U_strictMono := sqrt_strictMonoOn
  U_strictConcave := Real.strictConcaveOn_sqrt
  U_deriv _ hc := sqrt_hasDerivAt hc
  θ_pos := hθ0
  θ_lt_one := hθ1
  f_cont := continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div
    (continuousOn_const.add continuousOn_id) fun k hk => by simp at hk ⊢; linarith)
  f_contDiff := contDiffOn_const.add ((contDiffOn_const.mul contDiffOn_id).div
    (contDiffOn_const.add contDiffOn_id) fun k hk => by simp at hk ⊢; linarith)
  f_strictMono := by
    have ha0 : 0 < a := lt_trans (by positivity) ha
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    simp only [add_lt_add_iff_left]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  f_strictConcave := by
    have ha0 : 0 < a := lt_trans (by positivity) ha
    refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
      (continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div
        (continuousOn_const.add continuousOn_id) fun k hk => by simp at hk ⊢; linarith)) ?_
    rw [interior_Ici]
    intro x hx y hy hxy
    simp only [mem_Ioi] at hx hy
    rw [(ratTech_hasDerivAt a b (by linarith)).deriv, (ratTech_hasDerivAt a b (by linarith)).deriv]
    exact div_lt_div_of_pos_left ha0 (by positivity) (by nlinarith)
  f_deriv _ hk := ratTech_hasDerivAt a b (by linarith)
  f_zero_pos := by simpa using hb
  f'_zero := by simpa using ha
  kbar_pos := hkbar
  psi_gt k hk0 hk := by
    have := ratTech_psi_sub h1 h2 h3 hk0.le
    have hpos : 0 < (kbar - k) * (k ^ 2 + p * k + q) / (1 + k) ^ 2 :=
      div_pos (mul_pos (by linarith) (by positivity)) (by positivity)
    linarith
  psi_lt k hk := by
    have hk0 : 0 ≤ k := (hkbar.trans hk).le
    have := ratTech_psi_sub h1 h2 h3 hk0
    have hneg : (kbar - k) * (k ^ 2 + p * k + q) / (1 + k) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by positivity)) (by positivity)
    linarith
  f'_contAt_zero := (continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
    fun k hk => by
      simp only [Pi.pow_apply, Pi.add_apply, id_eq, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, mem_Ici] at hk ⊢
      linarith) 0 (mem_Ici.2 le_rfl)
  U'_inada := sqrt_inada

/-! ### NOTE 18.3-E: a model in which (7) has no solution for some `h ∈ F` -/

/-- The model of NOTE 18.3-E: `U = √`, `f(k) = 1/50 + (891/250) k/(1 + k)`, `θ = 1/2`,
`β = 9/10`; then `ψ(k) − k = (2 − k)(k² + (52/125) k + 1/100)/(1 + k)²`, so `k̄ = 2`. -/
noncomputable def modelE : GlobalModel :=
  ratModel (9 / 10) (1 / 2) (891 / 250) (1 / 50) 2 (52 / 125) (1 / 100) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- After-tax income in `modelE`. -/
theorem modelE_psi (k : ℝ) :
    modelE.psi k = 1 / 50 + 891 / 250 * k / (1 + k) - 1 / 2 * k * (891 / 250 / (1 + k) ^ 2) :=
  rfl

/-- The marginal product in `modelE`. -/
theorem modelE_f' (k : ℝ) : modelE.f' k = 891 / 250 / (1 + k) ^ 2 := rfl

/-- The discount factor in `modelE`. -/
theorem modelE_β : modelE.β = 9 / 10 := rfl

/-- The tax rate in `modelE`. -/
theorem modelE_θ : modelE.θ = 1 / 2 := rfl

/-- In `modelE`, `ψ(ψ(0)) ≤ k*`: after-tax income from the capital stock `ψ(0)` is still below
the steady state. -/
theorem modelE_psi_psi_le : modelE.psi (modelE.psi 0) ≤ modelE.kstar := by
  have hψ0 : modelE.psi 0 = 1 / 50 := by rw [modelE_psi]; norm_num
  rw [hψ0]
  set x := modelE.psi (1 / 50) with hxdef
  have hx : x ≤ 1 / 10 := by rw [hxdef, modelE_psi]; norm_num
  have hx0 : 0 ≤ x := (modelE.psi_pos (by norm_num)).le
  by_contra hlt
  have h := modelE.euler_lt_one (lt_of_not_ge hlt)
  rw [modelE_β, modelE_θ, modelE_f'] at h
  have hsq : (1 + x) ^ 2 ≤ 121 / 100 := by nlinarith
  have hpos : 0 < (1 + x) ^ 2 := by positivity
  set z := 891 / 250 / (1 + x) ^ 2 with hz
  have h2 : 891 / 250 / (121 / 100) ≤ z := div_le_div_of_nonneg_left (by norm_num) hpos hsq
  norm_num at h2
  linarith

/-- **Correction to Exercise 18.5** (NOTE 18.3-E). The book's claim that (7) defines `T` on `F`
— for every `h ∈ F` and `k ∈ K` there is a `y ∈ [0, ψ(k))` with positive next-period consumption
solving (7) — is false: in `modelE` it fails for `h = min{ψ, k*} ∈ F` at `k = 0`. -/
theorem ex_18_5_counterexample :
    ¬ ∀ (M : GlobalModel) (h : Icc 0 M.kbar →ᵇ ℝ), h ∈ M.F → ∀ k : Icc 0 M.kbar,
      ∃ y, 0 ≤ y ∧ y < M.psi k ∧ 0 < M.psi y - M.ext h y ∧
        M.U' (M.psi k - y) = M.β * (1 - M.θ) * M.f' y * M.U' (M.psi y - M.ext h y) := by
  intro hall
  obtain ⟨-, hno, -⟩ := modelE.ex_18_5_counterexample_of modelE_psi_psi_le
  have hmem := GlobalModel.toBCF_mem_F modelE.isInF_hE
  obtain ⟨y, hy0, hyP, hc, heq⟩ := hall modelE _ hmem ⟨0, le_rfl, modelE.kbar_pos.le⟩
  have hyK : y ∈ Icc 0 modelE.kbar :=
    ⟨hy0, hyP.le.trans (modelE.psi_le_kbar ⟨le_rfl, modelE.kbar_pos.le⟩)⟩
  rw [GlobalModel.ext_toBCF _ _ _ hyK] at hc heq
  exact hno ⟨y, hy0, hyP, hc, heq⟩

/-! ### The proof of Proposition 18.5: `A = f′(0)` is not a Lipschitz constant for `ψ` -/

/-- The integrand `φ(s) = 1/(1 + s⁸)`: flat near `0`, then dropping steeply around `s = 1`. -/
noncomputable def phiL (s : ℝ) : ℝ := 1 / (1 + s ^ 8)

/-- `Φ(k) = ∫₀ᵏ φ`. -/
noncomputable def PhiL (k : ℝ) : ℝ := ∫ s in (0 : ℝ)..k, phiL s

/-- The technology `f(k) = 3 + 4 Φ(k)` of `modelL`. -/
noncomputable def fL (k : ℝ) : ℝ := 3 + 4 * PhiL k

/-- After-tax income `ψ(k) = f(k) − (1/2) k f′(k)` of `modelL`. -/
noncomputable def psiL (k : ℝ) : ℝ := fL k - 1 / 2 * k * (4 * phiL k)

/-- `φ > 0`. -/
theorem phiL_pos (s : ℝ) : 0 < phiL s := by unfold phiL; positivity

/-- `φ ≤ 1`. -/
theorem phiL_le_one (s : ℝ) : phiL s ≤ 1 := by
  unfold phiL
  rw [div_le_one (by positivity)]
  nlinarith [pow_nonneg (sq_nonneg s) 4]

/-- `φ` is continuous. -/
theorem continuous_phiL : Continuous phiL :=
  continuous_const.div (continuous_const.add (continuous_pow 8)) fun s => by positivity

/-- `φ` is strictly decreasing on `[0, ∞)`. -/
theorem phiL_strictAntiOn : StrictAntiOn phiL (Ici 0) := by
  intro x hx y _ hxy
  have h : x ^ 8 < y ^ 8 := pow_lt_pow_left₀ hxy (mem_Ici.1 hx) (by norm_num)
  unfold phiL
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- `Φ′ = φ`. -/
theorem hasDerivAt_PhiL (k : ℝ) : HasDerivAt PhiL (phiL k) k :=
  (continuous_phiL.integral_hasStrictDerivAt 0 k).hasDerivAt

/-- `f′ = 4 φ`. -/
theorem hasDerivAt_fL (k : ℝ) : HasDerivAt fL (4 * phiL k) k := by
  have := ((hasDerivAt_PhiL k).const_mul 4).const_add 3
  exact this

/-- `φ′(k) = −8k⁷/(1 + k⁸)²`. -/
theorem hasDerivAt_phiL (k : ℝ) : HasDerivAt phiL (-(8 * k ^ 7) / (1 + k ^ 8) ^ 2) k := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 8) (8 * k ^ 7) k := by
    simpa using (hasDerivAt_pow 8 k).const_add 1
  have h2 := (hasDerivAt_const k (1 : ℝ)).div h1 (by positivity : (1 + k ^ 8) ≠ 0)
  convert h2 using 1
  · ext s; simp [phiL]
  · ring

/-- `ψ′(k) = 2/(1 + k⁸) + 16k⁸/(1 + k⁸)²` in `modelL`. -/
theorem hasDerivAt_psiL (k : ℝ) :
    HasDerivAt psiL (2 / (1 + k ^ 8) + 16 * k ^ 8 / (1 + k ^ 8) ^ 2) k := by
  have h1 := hasDerivAt_fL k
  have h2 := (((hasDerivAt_id k).const_mul (1 / 2 : ℝ)).mul
    ((hasDerivAt_phiL k).const_mul (4 : ℝ)))
  have h3 := h1.sub h2
  convert h3 using 1
  · ext x; simp [psiL]
  · simp only [phiL, id]
    field_simp
    ring

/-- `ψ` is continuous in `modelL`. -/
theorem continuous_psiL : Continuous psiL :=
  continuous_iff_continuousAt.2 fun k => (hasDerivAt_psiL k).continuousAt

/-- `Φ(k) ≥ k φ(k)` for `k ≥ 0` (`φ` is decreasing). -/
theorem mul_phiL_le_PhiL {k : ℝ} (hk : 0 ≤ k) : k * phiL k ≤ PhiL k := by
  have h := intervalIntegral.integral_mono_on hk (intervalIntegrable_const (c := phiL k))
    (continuous_phiL.intervalIntegrable (μ := MeasureTheory.volume) 0 k) fun x hx =>
      phiL_strictAntiOn.antitoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hk) hx.2
  simpa [intervalIntegral.integral_const, PhiL] using h

/-- `ψ(k) ≥ 3` for `k ≥ 0` in `modelL`. -/
theorem three_le_psiL {k : ℝ} (hk : 0 ≤ k) : 3 ≤ psiL k := by
  have h1 := mul_phiL_le_PhiL hk
  have h2 : 0 ≤ k * phiL k := mul_nonneg hk (phiL_pos k).le
  simp only [psiL, fL]
  nlinarith

/-- `ψ(20) < 20` in `modelL`. -/
theorem psiL_twenty_lt : psiL 20 < 20 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable phiL MeasureTheory.volume a b :=
    continuous_phiL.intervalIntegrable
  have h1 : ∫ s in (0 : ℝ)..2, phiL s ≤ ∫ s in (0 : ℝ)..2, (1 : ℝ) :=
    intervalIntegral.integral_mono_on (by norm_num) (hi 0 2) intervalIntegrable_const
      fun s _ => phiL_le_one s
  have h2 : ∫ s in (2 : ℝ)..20, phiL s ≤ ∫ s in (2 : ℝ)..20, (1 / 257 : ℝ) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hi 2 20) intervalIntegrable_const
      fun s hs => ?_
    have : (2 : ℝ) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by norm_num) hs.1 8
    unfold phiL
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at this ⊢
    linarith
  have h3 := intervalIntegral.integral_add_adjacent_intervals (hi 0 2) (hi 2 20)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
  have h4 : 0 ≤ 20 * phiL 20 := mul_nonneg (by norm_num) (phiL_pos 20).le
  simp only [psiL, fL, PhiL]
  rw [← h3]
  nlinarith

/-- `ψ(k) − k` is strictly decreasing on `[2, ∞)` in `modelL` (`ψ′ < 1` there). -/
theorem psiL_sub_strictAntiOn : StrictAntiOn (fun k => psiL k - k) (Ici 2) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 2)
    (continuous_psiL.sub continuous_id).continuousOn fun x hx => ?_
  rw [interior_Ici] at hx
  have hd : HasDerivAt (fun k => psiL k - k)
      (2 / (1 + x ^ 8) + 16 * x ^ 8 / (1 + x ^ 8) ^ 2 - 1) x :=
    (hasDerivAt_psiL x).sub (hasDerivAt_id' x)
  rw [hd.deriv]
  have ht : (2 : ℝ) ^ 8 ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) (le_of_lt hx) 8
  set t := x ^ 8
  have hpos : 0 < 1 + t := by positivity
  have : 2 / (1 + t) + 16 * t / (1 + t) ^ 2 = (2 * (1 + t) + 16 * t) / (1 + t) ^ 2 := by
    field_simp
  rw [this, sub_neg, div_lt_one (by positivity)]
  norm_num at ht
  nlinarith

/-- `ψ(k) = k` has a root in `[2, 20]` in `modelL`. -/
theorem exists_kbarL : ∃ k ∈ Icc (2 : ℝ) 20, psiL k - k = 0 := by
  have h := intermediate_value_Icc' (by norm_num : (2 : ℝ) ≤ 20)
    (continuous_psiL.sub continuous_id).continuousOn
  have h2 : 0 ∈ Icc (psiL 20 - 20) (psiL 2 - 2) :=
    ⟨by linarith [psiL_twenty_lt], by linarith [three_le_psiL (by norm_num : (0 : ℝ) ≤ 2)]⟩
  obtain ⟨k, hk, hk0⟩ := h h2
  exact ⟨k, hk, hk0⟩

/-- The capital stock `k̄ ∈ [2, 20]` of `modelL`. -/
noncomputable def kbarL : ℝ := Classical.choose exists_kbarL

/-- `2 ≤ k̄ ≤ 20` in `modelL`. -/
theorem kbarL_mem : kbarL ∈ Icc (2 : ℝ) 20 := (Classical.choose_spec exists_kbarL).1

/-- `ψ(k̄) = k̄` in `modelL`. -/
theorem psiL_kbarL : psiL kbarL - kbarL = 0 := (Classical.choose_spec exists_kbarL).2

/-- The `C²` property of the technology of `modelL`. -/
theorem contDiff_fL : ContDiff ℝ 2 fL := by
  have hd : deriv fL = fun k => 4 * (1 / (1 + k ^ 8)) :=
    funext fun k => (hasDerivAt_fL k).deriv
  have h1 : ContDiff ℝ 1 (fun k : ℝ => 4 * (1 / (1 + k ^ 8))) :=
    contDiff_const.mul (contDiff_const.div (contDiff_const.add (contDiff_id.pow 8))
      fun x => by positivity)
  change ContDiff ℝ (1 + 1) fL
  exact contDiff_succ_iff_deriv.2 ⟨fun k => (hasDerivAt_fL k).differentiableAt,
    fun h => absurd h (by simp), hd ▸ h1⟩

/-- **The model `modelL`.** `U = √`, `f(k) = 3 + 4 ∫₀ᵏ ds/(1 + s⁸)` (so `f′(k) = 4/(1 + k⁸)`,
`A = f′(0) = 4`), `θ = 1/2`, `β = 9/10`, `k̄ ∈ [2, 20]` the root of `ψ(k) = k`. -/
noncomputable def modelL : GlobalModel where
  β := 9 / 10
  θ := 1 / 2
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  f := fL
  f' := fun k => 4 * phiL k
  kbar := kbarL
  β_pos := by norm_num
  β_lt_one := by norm_num
  U_cont := Real.continuous_sqrt.continuousOn
  U_contDiff := sqrt_contDiffOn
  U_strictMono := sqrt_strictMonoOn
  U_strictConcave := Real.strictConcaveOn_sqrt
  U_deriv _ hc := sqrt_hasDerivAt hc
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  f_cont := contDiff_fL.continuous.continuousOn
  f_contDiff := contDiff_fL.contDiffOn
  f_strictMono := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) contDiff_fL.continuous.continuousOn
      fun x _ => ?_
    rw [(hasDerivAt_fL x).deriv]
    exact mul_pos (by norm_num) (phiL_pos x)
  f_strictConcave := by
    refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
      contDiff_fL.continuous.continuousOn ?_
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [(hasDerivAt_fL x).deriv, (hasDerivAt_fL y).deriv]
    exact mul_lt_mul_of_pos_left (phiL_strictAntiOn (mem_Ici.2 (le_of_lt hx))
      (mem_Ici.2 (le_of_lt hy)) hxy) (by norm_num)
  f_deriv k _ := hasDerivAt_fL k
  f_zero_pos := by simp [fL, PhiL]
  f'_zero := by simp [phiL]; norm_num
  kbar_pos := by linarith [kbarL_mem.1]
  psi_gt k hk0 hk := by
    change k < psiL k
    rcases le_or_gt k 2 with h2 | h2
    · linarith [three_le_psiL hk0.le]
    · have := psiL_sub_strictAntiOn (mem_Ici.2 h2.le) (mem_Ici.2 kbarL_mem.1) hk
      simp only at this
      linarith [psiL_kbarL]
  psi_lt k hk := by
    change psiL k < k
    have := psiL_sub_strictAntiOn (mem_Ici.2 kbarL_mem.1) (mem_Ici.2 (kbarL_mem.1.trans hk.le)) hk
    simp only at this
    linarith [psiL_kbarL]
  f'_contAt_zero := (continuous_const.mul continuous_phiL).continuousWithinAt
  U'_inada := sqrt_inada

/-- **Correction to the proof of Proposition 18.5** (p. 557). The book bounds
`|ψ(k′) − ψ(k)| ≤ A |k′ − k|` on `K` with `A = f′(0)` (Assumption 18.2). This is false: in
`modelL`, `A = 4` but `ψ(1) − ψ(9/10) > 4 · (1 − 9/10)`, because `ψ′ = (1 − θ) f′ − θ k f″` and
`−θ k f″` is large where `f′` drops steeply. -/
theorem prop_18_5_bound_counterexample :
    ¬ ∀ (M : GlobalModel) (k k' : ℝ), k ∈ Icc 0 M.kbar → k' ∈ Icc 0 M.kbar →
      |M.psi k' - M.psi k| ≤ M.f' 0 * |k' - k| := by
  intro hall
  have hkb := kbarL_mem.1
  have h := hall modelL (9 / 10) 1 ⟨by norm_num, by change (9 / 10 : ℝ) ≤ kbarL; linarith⟩
    ⟨by norm_num, by change (1 : ℝ) ≤ kbarL; linarith⟩
  change |psiL 1 - psiL (9 / 10)| ≤ 4 * phiL 0 * |1 - 9 / 10| at h
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope psiL
    (fun k => 2 / (1 + k ^ 8) + 16 * k ^ 8 / (1 + k ^ 8) ^ 2) (by norm_num : (9 / 10 : ℝ) < 1)
    continuous_psiL.continuousOn fun x _ => hasDerivAt_psiL x
  have ht1 : (9 / 10 : ℝ) ^ 8 < c ^ 8 := pow_lt_pow_left₀ hc.1 (by norm_num) (by norm_num)
  have ht2 : c ^ 8 < 1 := pow_lt_one₀ (by linarith [hc.1]) hc.2 (by norm_num)
  set t := c ^ 8
  have hpos : 0 < 1 + t := by positivity
  have hgt : 4 < 2 / (1 + t) + 16 * t / (1 + t) ^ 2 := by
    have : 2 / (1 + t) + 16 * t / (1 + t) ^ 2 = (2 * (1 + t) + 16 * t) / (1 + t) ^ 2 := by
      field_simp
    rw [this, lt_div_iff₀ (by positivity)]
    norm_num at ht1
    nlinarith
  rw [hslope] at hgt
  have hφ : phiL 0 = 1 := by simp [phiL]
  rw [hφ] at h
  rw [lt_div_iff₀ (by norm_num)] at hgt
  have := le_abs_self (psiL 1 - psiL (9 / 10))
  norm_num at h
  linarith

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stochastic extension of §18.3: Exercises 18.8 and 18.9 (pp. 558–560)

Shocks `ξ ∈ Ξ = {ξ_j}` (a finite type `ι`) follow a Markov chain with transition matrix `π`; the
technology is `f(·, ξ_j)`, with after-tax income `ψ_j(k) = f(k, ξ_j) − θ k f′(k, ξ_j)`. Parts (d),
(e) of Assumption 18.1 and Assumption 18.2 hold "for each `ξ_j`" (`StochModel.tech j` is a
`GlobalModel`), and `K = [0, B]`, `B = max_j k̄_j`. An equilibrium is `g : K × Ξ → K` with
(§18.3 (8))
  `U′[ψ_i(k) − g_i(k)] = β(1 − θ) Σ_j π_ij f′_j[g_i(k)] U′{ψ_j[g_i(k)] − g_j[g_i(k)]}`,
and `F` is the set of `h` with `0 ≤ h_j ≤ ψ_j` and `h_j`, `ψ_j − h_j` nondecreasing (p. 559).
The operator `T` of (9) is again a crossing point (`Ts`, built from `eulerCross`).

* `ex_18_8_counterexample` (**Correction**, Exercise 18.8 is false as posed, NOTE 18.3-J(i)):
  in a two-shock model with log-like utility `U = √` satisfying every per-shock assumption,
  (9) has no solution for `h ≡ 0 ∈ F` at `(k, ξ) = (0, ξ_2)` — the agent wants a corner `y = 0`.
  The general mechanism is `no_solution_of_crossState_fails`.
* `Ts_psi`, `no_solution_at_psi` (**Correction**, NOTE 18.3-J(ii)): `h = ψ` belongs to `F`, the
  right side of (9) is `+∞` everywhere for it, so (9) has no solution at any `(k, ξ_i)`; with the
  extended-real convention `Tψ = ψ`, so the greatest element of `F` is a degenerate fixed point
  (zero consumption forever). The book's "existence follows from Schauder's Theorem" therefore
  produces nothing in the stochastic case without a smaller `F`.
* `ex_18_8_spec_KT` (corrected Exercise 18.8, Kuhn–Tucker form, no extra assumption): for every
  `h ∈ F` and `(k, ξ_i)`, `(Th)_i(k)` is an interior solution of (9), or a zero-consumption corner,
  or a zero-saving corner at which (9) holds as `RHS ≤ LHS`; and `ex_18_8`: `T : F → F`.
* `ex_18_8_spec` (corrected Exercise 18.8, equation form): under the cross-state condition
  `CrossState` — `U′(ψ_i(0)) < β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0))` for every `i`, which for one
  shock is exactly `β(1 − θ) f′(0) > 1` of Assumption 18.1d — the zero-saving corner cannot occur.
* `ex_18_8_mono`: `T` is monotone on `F` (the analogue of Exercise 18.7).

**Correction (p. 560, cross-reference).** "the proof of Proposition 6" should read
"Proposition 5" (Proposition 18.5, `GlobalModel.prop_18_5`); Chapter 18 has no Proposition 6.

**Exercise 18.9** (p. 560, `Ξ` a closed bounded interval) is treated in `GlobalContinuum`:
with jointly continuous technologies, a Feller transition, and `F` restricted to strictly
positive consumption, `T` is well defined, maps `F₊` into `F₊` and is monotone. Continuity,
equicontinuity and the least and greatest fixed points in the finite case are in
`GlobalStochasticEquilibrium`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- **The stochastic model** of p. 558. `tech j` is the economy with technology `f(·, ξ_j)`; all
share `β`, `θ`, `U`, `U′`. `B = max_j k̄_j` and `π` is a transition matrix. -/
structure StochModel (ι : Type) [Fintype ι] where
  tech : ι → GlobalModel
  β : ℝ
  θ : ℝ
  U : ℝ → ℝ
  U' : ℝ → ℝ
  B : ℝ
  π : ι → ι → ℝ
  tech_β : ∀ j, (tech j).β = β
  tech_θ : ∀ j, (tech j).θ = θ
  tech_U : ∀ j, (tech j).U = U
  tech_U' : ∀ j, (tech j).U' = U'
  kbar_le : ∀ j, (tech j).kbar ≤ B
  B_eq : ∃ j, (tech j).kbar = B
  π_nonneg : ∀ i j, 0 ≤ π i j
  π_sum : ∀ i, ∑ j, π i j = 1

namespace StochModel

variable {ι : Type} [Fintype ι] (S : StochModel ι)

/-- `B > 0`. -/
theorem B_pos : 0 < S.B := by
  obtain ⟨j, hj⟩ := S.B_eq
  rw [← hj]; exact (S.tech j).kbar_pos

/-- The common marginal utility is a marginal utility. -/
theorem isMarginalUtility : IsMarginalUtility S.U' := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_U' j]; exact (S.tech j).isMarginalUtility

/-- `β(1 − θ) > 0`. -/
theorem coef_pos : 0 < S.β * (1 - S.θ) := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_β j, ← S.tech_θ j]; exact (S.tech j).euler_coef_pos

/-- `ψ_j` maps `[0, B]` into `(0, B]`. -/
theorem psi_le_B (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : (S.tech j).psi k ≤ S.B := by
  rcases le_or_gt k (S.tech j).kbar with h | h
  · exact ((S.tech j).psi_le_kbar ⟨hk.1, h⟩).trans (S.kbar_le j)
  · exact ((S.tech j).psi_lt k h).le.trans hk.2

/-- **The set `F`** of p. 559: for each `j`, `h_j` is continuous on `K = [0, B]`,
`0 ≤ h_j ≤ ψ_j`, and `h_j`, `ψ_j − h_j` are nondecreasing. -/
structure IsInFs (h : ι → ℝ → ℝ) : Prop where
  cont : ∀ j, ContinuousOn (h j) (Icc 0 S.B)
  nonneg : ∀ j, ∀ k ∈ Icc 0 S.B, 0 ≤ h j k
  le_psi : ∀ j, ∀ k ∈ Icc 0 S.B, h j k ≤ (S.tech j).psi k
  mono : ∀ j, MonotoneOn (h j) (Icc 0 S.B)
  mono_sub : ∀ j, MonotoneOn (fun k => (S.tech j).psi k - h j k) (Icc 0 S.B)

/-- Some next-period consumption reachable from state `i` is zero at `y` (right side `+∞`). -/
def Zs (h : ι → ℝ → ℝ) (i : ι) (y : ℝ) : Prop :=
  ∃ j, 0 < S.π i j ∧ (S.tech j).psi y - h j y ≤ 0

/-- The right side of (9): `β(1 − θ) Σ_j π_ij f′_j(y) U′[ψ_j(y) − h_j(y)]`. -/
noncomputable def Rs (h : ι → ℝ → ℝ) (i : ι) (y : ℝ) : ℝ :=
  S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' y * S.U' ((S.tech j).psi y - h j y))

/-- **The operator (9)**: `(Th)_i(k)` is the crossing point of `y ↦ U′[ψ_i(k) − y]` and the right
side of (9). -/
noncomputable def Ts (h : ι → ℝ → ℝ) (i : ι) (k : ℝ) : ℝ :=
  eulerCross S.U' (S.Zs h i) (S.Rs h i) ((S.tech i).psi k)

variable {S}

/-- One term of the right side of (9) is nonincreasing in `y`. -/
theorem IsInFs.term_anti {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i j : ι) {y y' : ℝ} (hy' : 0 ≤ y')
    (hyy : y' ≤ y) (hyB : y ≤ S.B) (hz : ¬ S.Zs h i y') :
    S.π i j * ((S.tech j).f' y * S.U' ((S.tech j).psi y - h j y)) ≤
      S.π i j * ((S.tech j).f' y' * S.U' ((S.tech j).psi y' - h j y')) := by
  rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hc' : 0 < (S.tech j).psi y' - h j y' := lt_of_not_ge fun hle => hz ⟨j, hpos, hle⟩
    have hcc : (S.tech j).psi y' - h j y' ≤ (S.tech j).psi y - h j y :=
      hh.mono_sub j ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    have hU : S.U' ((S.tech j).psi y - h j y) ≤ S.U' ((S.tech j).psi y' - h j y') :=
      S.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : (S.tech j).f' y ≤ (S.tech j).f' y' :=
      (S.tech j).f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 (hy'.trans hyy)) hyy
    have hUpos := S.isMarginalUtility.pos _ (hc'.trans_le hcc)
    exact mul_le_mul_of_nonneg_left (mul_le_mul hf hU hUpos.le
      ((S.tech j).f'_pos hy').le) hpos.le

/-- Every term of the right side of (9) is nonnegative where no next-period consumption is
zero. -/
theorem IsInFs.term_nonneg (i j : ι) {h : ι → ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hz : ¬ S.Zs h i y) :
    0 ≤ S.π i j * ((S.tech j).f' y * S.U' ((S.tech j).psi y - h j y)) := by
  rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hc : 0 < (S.tech j).psi y - h j y := lt_of_not_ge fun hle => hz ⟨j, hpos, hle⟩
    exact mul_nonneg hpos.le (mul_nonneg ((S.tech j).f'_pos hy).le
      (S.isMarginalUtility.pos _ hc).le)

/-- For `h ∈ F` the right side of (9) is an `IsEulerRHS` on `[0, B]`. -/
theorem IsInFs.isEulerRHS {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) :
    IsEulerRHS S.B (S.Zs h i) (S.Rs h i) where
  zero_anti y y' hy' hyy hyB hz := by
    obtain ⟨j, hj, hc⟩ := hz
    refine ⟨j, hj, ?_⟩
    have := hh.mono_sub j ⟨hy', hyy.trans hyB⟩ ⟨hy'.trans hyy, hyB⟩ hyy
    simp only at this
    linarith
  anti y y' hy' hyy hyB hz :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hh.term_anti i j hy' hyy hyB hz)
      S.coef_pos.le
  cont y hy hz := by
    have hpos : ∀ j, 0 < S.π i j → 0 < (S.tech j).psi y - h j y :=
      fun j hj => lt_of_not_ge fun hle => hz ⟨j, hj, hle⟩
    have hcw : ∀ j, ContinuousWithinAt (fun z => (S.tech j).psi z - h j z) (Icc 0 S.B) y :=
      fun j => (((S.tech j).psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub
        (hh.cont j y hy)
    refine ⟨?_, ?_⟩
    · have : ∀ᶠ z in 𝓝[Icc 0 S.B] y, ∀ j, 0 < S.π i j → 0 < (S.tech j).psi z - h j z := by
        refine eventually_all.2 fun j => ?_
        by_cases hj : 0 < S.π i j
        · exact ((hcw j).eventually_const_lt (hpos j hj)).mono fun z hz _ => hz
        · exact Eventually.of_forall fun z hj' => absurd hj' hj
      exact this.mono fun z hz ⟨j, hj, hle⟩ => absurd (hz j hj) (not_lt.2 hle)
    · refine continuousWithinAt_const.mul ?_
      refine tendsto_finsetSum _ fun j _ => ?_
      rcases (S.π_nonneg i j).eq_or_lt with h0 | hj
      · rw [← h0]; simpa using tendsto_const_nhds
      · refine tendsto_const_nhds.mul (Tendsto.mul
          (((S.tech j).f'_continuousOn.mono Icc_subset_Ici_self) y hy) ?_)
        exact ((S.isMarginalUtility.cont.continuousAt
          (Ioi_mem_nhds (hpos j hj))).comp_continuousWithinAt
          (f := fun z => (S.tech j).psi z - h j z) (hcw j))
  blowup y hy hz M0 := by
    obtain ⟨j0, hj0, hc0⟩ := hz
    have hcw : ContinuousWithinAt (fun z => (S.tech j0).psi z - h j0 z) (Icc 0 S.B) y :=
      (((S.tech j0).psi_continuousOn.mono Icc_subset_Ici_self) y hy).sub (hh.cont j0 y hy)
    set m := S.β * (1 - S.θ) * S.π i j0 * (S.tech j0).f' S.B
    have hm : 0 < m := mul_pos (mul_pos S.coef_pos hj0) ((S.tech j0).f'_pos S.B_pos.le)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (S.isMarginalUtility.inada.eventually_gt_atTop (|M0| / m))
    filter_upwards [hcw.eventually_lt_const (lt_of_le_of_lt hc0 hε), self_mem_nhdsWithin]
      with z hz1 hzK
    by_cases hZ : S.Zs h i z
    · exact Or.inl hZ
    · right
      have hc : 0 < (S.tech j0).psi z - h j0 z := lt_of_not_ge fun hle => hZ ⟨j0, hj0, hle⟩
      have hU : |M0| / m < S.U' ((S.tech j0).psi z - h j0 z) := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact hz1, hc⟩
      rw [div_lt_iff₀ hm] at hU
      have hf : (S.tech j0).f' S.B ≤ (S.tech j0).f' z :=
        (S.tech j0).f'_strictAntiOn.antitoneOn (mem_Ici.2 hzK.1) (mem_Ici.2 S.B_pos.le) hzK.2
      have hsingle := Finset.single_le_sum (f := fun j => S.π i j * ((S.tech j).f' z *
        S.U' ((S.tech j).psi z - h j z))) (fun j _ => IsInFs.term_nonneg i j hzK.1 hZ)
        (Finset.mem_univ j0)
      have hUp := S.isMarginalUtility.pos _ hc
      have h1 : m * S.U' ((S.tech j0).psi z - h j0 z) ≤ S.β * (1 - S.θ) *
          (S.π i j0 * ((S.tech j0).f' z * S.U' ((S.tech j0).psi z - h j0 z))) := by
        have : m = S.β * (1 - S.θ) * S.π i j0 * (S.tech j0).f' S.B := rfl
        rw [this]
        have := mul_le_mul_of_nonneg_left hf (mul_pos S.coef_pos hj0).le
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left hsingle S.coef_pos.le
      simp only [Rs]
      linarith [le_abs_self M0]

/-- `0 ≤ (Th)_i(k) ≤ ψ_i(k)`. -/
theorem Ts_mem_Icc (h : ι → ℝ → ℝ) (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.Ts h i k ∈ Icc 0 ((S.tech i).psi k) :=
  ⟨eulerCross_nonneg, eulerCross_le ((S.tech i).psi_pos hk.1).le⟩

/-- **Corrected Exercise 18.8, Kuhn–Tucker form.** For `h ∈ F`, a state `i` and `k ∈ K`,
exactly one of: `y = (Th)_i(k)` is an interior solution of (9) with positive consumption today
and in every reachable state tomorrow; or there is zero consumption today (`y = ψ_i(k)`, the
right side of (9) being `+∞` on `[0, ψ_i(k))`); or there is zero saving (`y = 0`) and (9) holds
as the Kuhn–Tucker inequality `RHS(0) ≤ U′(ψ_i(k))`. No assumption beyond the per-shock ones is
needed. -/
theorem ex_18_8_spec_KT {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    (S.Ts h i k < (S.tech i).psi k ∧ ¬ S.Zs h i (S.Ts h i k) ∧
      S.U' ((S.tech i).psi k - S.Ts h i k) = S.Rs h i (S.Ts h i k)) ∨
    (S.Ts h i k = (S.tech i).psi k ∧ ∀ y, 0 ≤ y → y < (S.tech i).psi k → S.Zs h i y) ∨
    (S.Ts h i k = 0 ∧ ¬ S.Zs h i 0 ∧ S.Rs h i 0 ≤ S.U' ((S.tech i).psi k)) :=
  eulerCross_spec_KT S.isMarginalUtility (hh.isEulerRHS i) ((S.tech i).psi_pos hk.1)
    (S.psi_le_B i hk)

variable (S)

/-- The **cross-state condition** that replaces Assumption 18.1d's `β(1 − θ) f′(0) > 1` in the
stochastic case: `U′(ψ_i(0)) < β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0))` for every state `i`. -/
def CrossState : Prop :=
  ∀ i, S.U' ((S.tech i).psi 0) <
    S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0))

variable {S}

/-- Under the cross-state condition the left side of (9) lies below the right side at `y = 0`. -/
theorem IsInFs.eulerBelow_zero (hCS : S.CrossState) {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι)
    {k : ℝ} (hk : k ∈ Icc 0 S.B) : EulerBelow S.U' (S.Zs h i) (S.Rs h i) ((S.tech i).psi k) 0 := by
  by_cases hz : S.Zs h i 0
  · exact Or.inl hz
  · right
    have h0B : (0 : ℝ) ∈ Icc 0 S.B := ⟨le_rfl, S.B_pos.le⟩
    have hterm : ∀ j, S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0)) ≤
        S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0 - h j 0)) := by
      intro j
      rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hc : 0 < (S.tech j).psi 0 - h j 0 := lt_of_not_ge fun hle => hz ⟨j, hpos, hle⟩
        have hle : (S.tech j).psi 0 - h j 0 ≤ (S.tech j).psi 0 := by
          linarith [hh.nonneg j 0 h0B]
        have hU := S.isMarginalUtility.strictAnti.antitoneOn hc
          ((S.tech j).psi_pos le_rfl) hle
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU
          ((S.tech j).f'_pos le_rfl).le) hpos.le
    have h1 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j) S.coef_pos.le
    have hψ := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have h2 : S.U' ((S.tech i).psi k) ≤ S.U' ((S.tech i).psi 0) :=
      S.isMarginalUtility.strictAnti.antitoneOn ((S.tech i).psi_pos le_rfl)
        ((S.tech i).psi_pos hk.1) hψ
    have h3 := hCS i
    simp only [Rs, sub_zero]
    linarith

/-- **Corrected Exercise 18.8, equation form.** Under the cross-state condition, for `h ∈ F`
either `(Th)_i(k)` solves (9) with positive consumptions (and is its unique such solution), or
(9) has no such solution and `(Th)_i(k) = ψ_i(k)`. -/
theorem ex_18_8_spec (hCS : S.CrossState) {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    (S.Ts h i k < (S.tech i).psi k ∧ ¬ S.Zs h i (S.Ts h i k) ∧
      S.U' ((S.tech i).psi k - S.Ts h i k) = S.Rs h i (S.Ts h i k) ∧
      ∀ y, 0 ≤ y → y < (S.tech i).psi k → ¬ S.Zs h i y →
        S.U' ((S.tech i).psi k - y) = S.Rs h i y → y = S.Ts h i k) ∨
    (S.Ts h i k = (S.tech i).psi k ∧ ∀ y, 0 ≤ y → y < (S.tech i).psi k → S.Zs h i y) := by
  have hPB := S.psi_le_B i hk
  rcases eulerCross_spec S.isMarginalUtility (hh.isEulerRHS i) ((S.tech i).psi_pos hk.1) hPB
    (hh.eulerBelow_zero hCS i hk) with ⟨h1, h2, h3⟩ | h'
  · exact Or.inl ⟨h1, h2, h3, fun y hy0 hyP hz heq =>
      (eulerCross_unique S.isMarginalUtility (hh.isEulerRHS i) hPB hy0 hyP hz heq).symm⟩
  · exact Or.inr h'

/-- `|(Th)_i(a) − (Th)_i(b)| ≤ |ψ_i(a) − ψ_i(b)|`, with `(Th)_i` and `ψ_i − (Th)_i`
nondecreasing on `K`. -/
theorem IsInFs.Ts_mono {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {a b : ℝ}
    (ha : a ∈ Icc 0 S.B) (hb : b ∈ Icc 0 S.B) (hab : a ≤ b) :
    S.Ts h i a ≤ S.Ts h i b ∧ S.Ts h i b ≤ S.Ts h i a + ((S.tech i).psi b - (S.tech i).psi a) := by
  have hψ := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
  exact ⟨eulerCross_mono' S.isMarginalUtility (hh.isEulerRHS i) hψ (S.psi_le_B i hb),
    eulerCross_le_add_sub S.isMarginalUtility (hh.isEulerRHS i) hψ (S.psi_le_B i hb)⟩

/-- **Corrected Exercise 18.8: `T : F → F`** (with the Kuhn–Tucker reading of (9); no extra
assumption). -/
theorem ex_18_8 {h : ι → ℝ → ℝ} (hh : S.IsInFs h) : S.IsInFs (fun i k => S.Ts h i k) where
  cont i := by
    rw [Metric.continuousOn_iff]
    intro k0 hk0 ε hε
    obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1 ((S.tech i).psi_continuousOn.mono
      (Icc_subset_Ici_self : Icc (0 : ℝ) S.B ⊆ Ici 0)) k0 hk0 ε hε
    refine ⟨δ, hδ, fun k hk hd => ?_⟩
    have h1 := hψ k hk hd
    rw [Real.dist_eq] at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    rcases le_total k k0 with hkk | hkk
    · obtain ⟨e1, e2⟩ := hh.Ts_mono i hk hk0 hkk
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm]
      have := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 hk.1) (mem_Ici.2 hk0.1) hkk
      rw [abs_of_nonneg (by linarith)]
      linarith
    · obtain ⟨e1, e2⟩ := hh.Ts_mono i hk0 hk hkk
      rw [abs_of_nonneg (by linarith)]
      have := (S.tech i).psi_strictMonoOn.monotoneOn (mem_Ici.2 hk0.1) (mem_Ici.2 hk.1) hkk
      rw [abs_of_nonneg (by linarith)]
      linarith
  nonneg i k hk := (Ts_mem_Icc h i hk).1
  le_psi i k hk := (Ts_mem_Icc h i hk).2
  mono i a ha b hb hab := (hh.Ts_mono i ha hb hab).1
  mono_sub i a ha b hb hab := by
    have := (hh.Ts_mono i ha hb hab).2
    simp only
    linarith

/-- **`T` is monotone on `F`** in the stochastic case (the analogue of Exercise 18.7). -/
theorem ex_18_8_mono {h h' : ι → ℝ → ℝ}
    (hle : ∀ j, ∀ k ∈ Icc 0 S.B, h j k ≤ h' j k) (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.Ts h i k ≤ S.Ts h' i k := by
  have hPB := S.psi_le_B i hk
  refine eulerCross_mono_rhs' (fun y hy0 hyP hz => ?_) (fun y hy0 hyP hz hz' => ?_)
  · obtain ⟨j, hj, hc⟩ := hz
    exact ⟨j, hj, by linarith [hle j y ⟨hy0, hyP.le.trans hPB⟩]⟩
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) S.coef_pos.le
    rcases (S.π_nonneg i j).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hc' : 0 < (S.tech j).psi y - h' j y := lt_of_not_ge fun hl => hz' ⟨j, hpos, hl⟩
      have hcc : (S.tech j).psi y - h' j y ≤ (S.tech j).psi y - h j y := by
        linarith [hle j y ⟨hy0, hyP.le.trans hPB⟩]
      have hU := S.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU
        ((S.tech j).f'_pos hy0).le) hpos.le

variable (S)

/-- The least element of `F` in the stochastic case: `h ≡ 0`. -/
theorem isInFs_zero : S.IsInFs fun _ _ => 0 where
  cont _ := continuousOn_const
  nonneg _ _ _ := le_rfl
  le_psi j k hk := ((S.tech j).psi_pos hk.1).le
  mono _ := fun _ _ _ _ _ => le_rfl
  mono_sub j := fun a ha b hb hab => by
    simp only [sub_zero]
    exact (S.tech j).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab

/-- The greatest element of `F` in the stochastic case: `h = ψ` (it is in `F` since
`ψ − h ≡ 0`). -/
theorem isInFs_psi : S.IsInFs fun j k => (S.tech j).psi k where
  cont j := (S.tech j).psi_continuousOn.mono Icc_subset_Ici_self
  nonneg j k hk := ((S.tech j).psi_pos hk.1).le
  le_psi _ _ _ := le_rfl
  mono j := fun a ha b hb hab =>
    (S.tech j).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
  mono_sub _ := fun _ _ _ _ _ => by simp

/-- Some state is reachable from `i`. -/
theorem exists_pi_pos (i : ι) : ∃ j, 0 < S.π i j := by
  by_contra hcon
  push Not at hcon
  have : ∑ j, S.π i j ≤ 0 := Finset.sum_nonpos fun j _ => hcon j
  linarith [S.π_sum i]

/-- **Correction (NOTE 18.3-J(ii)).** For `h = ψ ∈ F` every next-period consumption is zero,
so (9) has no solution with positive consumptions at any `(k, ξ_i)`. -/
theorem no_solution_at_psi (i : ι) (y : ℝ) : S.Zs (fun j k => (S.tech j).psi k) i y := by
  obtain ⟨j, hj⟩ := S.exists_pi_pos i
  exact ⟨j, hj, by simp⟩

/-- **Correction (NOTE 18.3-J(ii)).** With the extended-real convention, `Tψ = ψ`: the greatest
element of `F` is a fixed point of `T` with zero consumption forever, at which (9) holds nowhere
(`no_solution_at_psi`). So Schauder's Theorem (or Theorem 17.7 from the greatest element) yields
this degenerate fixed point, and existence of an equilibrium does not follow as claimed on
p. 560. -/
theorem Ts_psi (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.Ts (fun j k => (S.tech j).psi k) i k = (S.tech i).psi k := by
  refine le_antisymm (Ts_mem_Icc _ i hk).2 (le_eulerCross_of_forall fun y hy0 hy =>
    ⟨hy0, hy, Or.inl (S.no_solution_at_psi i y)⟩)

/-- **Correction (NOTE 18.3-J(i)), the mechanism.** If the cross-state condition fails strictly
in state `i` — `β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0)) < U′(ψ_i(0))` — then for `h ≡ 0 ∈ F`
equation (9) at `(0, ξ_i)` has no solution `y ∈ [0, ψ_i(0))` with positive consumptions: the left
side exceeds the right side everywhere (the agent wants a corner with zero saving). -/
theorem no_solution_of_crossState_fails (i : ι)
    (hfail : S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0)) <
      S.U' ((S.tech i).psi 0)) :
    ¬ ∃ y, 0 ≤ y ∧ y < (S.tech i).psi 0 ∧ ¬ S.Zs (fun _ _ => 0) i y ∧
      S.U' ((S.tech i).psi 0 - y) = S.Rs (fun _ _ => 0) i y := by
  rintro ⟨y, hy0, hyP, hz, heq⟩
  have hB : y ≤ S.B := hyP.le.trans (S.psi_le_B i ⟨le_rfl, S.B_pos.le⟩)
  have h1 : S.Rs (fun _ _ => 0) i y ≤ S.Rs (fun _ _ => 0) i 0 :=
    ((S.isInFs_zero).isEulerRHS i).anti y 0 le_rfl hy0 hB fun ⟨j, _, hc⟩ => by
      simp only [sub_zero] at hc
      linarith [(S.tech j).psi_pos (le_refl (0 : ℝ))]
  have h2 : S.U' ((S.tech i).psi 0) ≤ S.U' ((S.tech i).psi 0 - y) :=
    S.isMarginalUtility.strictAnti.antitoneOn (mem_Ioi.2 (by linarith))
      ((S.tech i).psi_pos le_rfl) (by linarith)
  simp only [Rs, sub_zero] at h1 heq
  linarith

end StochModel

/-! ### A two-shock model in which Exercise 18.8 fails -/

/-- The high-productivity technology `f(k) = 10 + (441/41) k/(1 + k)` (`θ = 1/2`, `β = 9/10`,
`k̄ = 20`, `ψ(k) − k = (20 − k)(k² + (51/41) k + 1/2)/(1 + k)²`). -/
noncomputable def modelHigh : GlobalModel :=
  ratModel (9 / 10) (1 / 2) (441 / 41) 10 20 (51 / 41) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The two-shock model of NOTE 18.3-J(i): state `0` has technology `modelHigh` (`ψ(0) = 10`),
state `1` has `modelE` (`ψ(0) = 1/50`), and the economy moves to state `0` for sure. Every
per-shock assumption holds, since both technologies are `GlobalModel`s. -/
noncomputable def stochJ : StochModel (Fin 2) where
  tech := ![modelHigh, modelE]
  β := 9 / 10
  θ := 1 / 2
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  B := 20
  π := fun _ j => if j = 0 then 1 else 0
  tech_β j := by fin_cases j <;> rfl
  tech_θ j := by fin_cases j <;> rfl
  tech_U j := by fin_cases j <;> rfl
  tech_U' j := by fin_cases j <;> rfl
  kbar_le j := by
    fin_cases j
    · exact le_refl (20 : ℝ)
    · change (2 : ℝ) ≤ 20; norm_num
  B_eq := ⟨0, rfl⟩
  π_nonneg _ j := by split_ifs <;> norm_num
  π_sum _ := by simp

/-- In `stochJ` the cross-state condition fails in state `1`:
`β(1 − θ) f′_0(0) U′(ψ_0(0)) = (9/20)(441/41)/(2√10) < 1/(2√(1/50)) = U′(ψ_1(0))`. -/
theorem stochJ_crossState_fails :
    stochJ.β * (1 - stochJ.θ) * ∑ j, stochJ.π 1 j *
        ((stochJ.tech j).f' 0 * stochJ.U' ((stochJ.tech j).psi 0)) <
      stochJ.U' ((stochJ.tech 1).psi 0) := by
  have e0 : (stochJ.tech 0).psi 0 = 10 := by
    change (10 + 441 / 41 * 0 / (1 + 0)) - 1 / 2 * 0 * (441 / 41 / (1 + 0) ^ 2) = 10
    norm_num
  have e1 : (stochJ.tech 1).psi 0 = 1 / 50 := by
    change (1 / 50 + 891 / 250 * 0 / (1 + 0)) - 1 / 2 * 0 * (891 / 250 / (1 + 0) ^ 2) = 1 / 50
    norm_num
  have f0 : (stochJ.tech 0).f' 0 = 441 / 41 := by
    change 441 / 41 / (1 + 0) ^ 2 = (441 / 41 : ℝ)
    norm_num
  have hβ : stochJ.β = 9 / 10 := rfl
  have hθ : stochJ.θ = 1 / 2 := rfl
  have hU : ∀ c, stochJ.U' c = 1 / (2 * √c) := fun _ => rfl
  have hπ0 : stochJ.π 1 0 = 1 := by simp [stochJ]
  have hπ1 : stochJ.π 1 1 = 0 := by simp [stochJ]
  rw [Fin.sum_univ_two, e0, e1, f0, hβ, hθ, hπ0, hπ1, hU, hU]
  simp only [zero_mul, add_zero, one_mul]
  have h10 : (3 : ℝ) < √10 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h50 : √(1 / 50 : ℝ) < 1 / 7 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs : 0 < √(1 / 50 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hA : 1 / (2 * √10) < 1 / (2 * 3) :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have hB : 1 / (2 * (1 / 7)) < 1 / (2 * √(1 / 50 : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  norm_num at hA hB ⊢
  nlinarith

/-- **Correction: Exercise 18.8 is false as posed** (NOTE 18.3-J(i)). The claim that (9) has a
solution with positive consumptions for every `h ∈ F` and every `(k, ξ_i)` fails in `stochJ`,
for `h ≡ 0` at `(0, ξ_1)`, although each technology satisfies Assumptions 18.1 and 18.2. -/
theorem ex_18_8_counterexample :
    ¬ ∀ (ι : Type) [Fintype ι] (S : StochModel ι) (h : ι → ℝ → ℝ), S.IsInFs h →
      ∀ (i : ι) (k : ℝ), k ∈ Icc 0 S.B → ∃ y, 0 ≤ y ∧ y < (S.tech i).psi k ∧
        ¬ S.Zs h i y ∧ S.U' ((S.tech i).psi k - y) = S.Rs h i y := by
  intro hall
  exact stochJ.no_solution_of_crossState_fails 1 stochJ_crossState_fails
    (hall (Fin 2) stochJ _ stochJ.isInFs_zero 1 0 ⟨le_rfl, stochJ.B_pos.le⟩)

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibria of the stochastic model: continuity, equicontinuity, least and greatest fixed
points (SLP p. 560)

The remainder of p. 560 asserts, for the stochastic operator (9): equicontinuity of `F`
"parallels exactly the proof of Proposition 6 [5]", continuity of `T` parallels Exercise 18.6,
existence follows from Schauder's Theorem, monotonicity parallels Exercise 18.7, and minimal and
maximal elements of `F` can be constructed as there.

* `IsInFs.abs_Ts_sub_le`, `Ts_equicontinuous`: `T(F)` is equicontinuous, with the modulus of
  continuity of `ψ_i` (Proposition 18.5).
* `Ts_tendsto` and `Ts_tendsto_uniform` (Exercise 18.6): if `hₐ → h` **pointwise** on `K` within
  `F`, then `T hₐ → T h` **uniformly** on `K`. In particular `T` is continuous for the sup norm.
* The least fixed point (Theorem 17.7 from the least element `0`): `lfp`, the pointwise limit of
  `Tⁿ0`. `tendsto_Tsit` gives convergence and `tendstoUniformly_Tsit` uniform convergence;
  `isInFs_lfp`, `Ts_lfp` and `lfp_le_of_super` say `lfp ∈ F` is a fixed point lying below every
  supersolution, in particular below every fixed point.
* `stoch_least_greatest`: the fixed points of `T` in `F` all lie between the least fixed point
  `lfp` and the **greatest fixed point `ψ`**, which is the degenerate fixed point with zero
  consumption forever (`Ts_psi`).
* `lfp_equilibrium_of_super` (existence of a non-degenerate equilibrium): if some `h̄ ∈ F` with
  positive consumption `ψ − h̄ > 0` on `K` is a supersolution (`T h̄ ≤ h̄`), and the cross-state
  condition holds, then `lfp` has positive consumption everywhere and solves (9) as an
  equation at every `(k, ξ_i)`; it is then the least equilibrium.
* `identical_tech_fixed`, `exists_nondegenerate_equilibrium_identical`: the hypothesis holds
  when all states share one technology (from the deterministic equilibrium of
  `GlobalModel.exists_equilibrium`), so `lfp_equilibrium_of_super` is not vacuous.

**Not proved.** Existence of a non-degenerate equilibrium for heterogeneous technologies under
the cross-state condition alone. The deterministic proof anchors consumption at `k*` through
(4)–(6), and the stochastic `F` has no such anchor; `Ts_psi` shows the book's Schauder argument
gives only the degenerate fixed point `ψ`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

namespace StochModel

variable {ι : Type} [Fintype ι] {S : StochModel ι}

/-- Members of the stochastic `F` change by at most the change in `ψ_j`. -/
theorem IsInFs.abs_sub_le {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (j : ι) {a b : ℝ}
    (ha : a ∈ Icc 0 S.B) (hb : b ∈ Icc 0 S.B) :
    |h j a - h j b| ≤ |(S.tech j).psi a - (S.tech j).psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hh.mono j ha hb hab
    have h2 : (S.tech j).psi a - h j a ≤ (S.tech j).psi b - h j b := hh.mono_sub j ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hh.mono j hb ha hab
    have h2 : (S.tech j).psi b - h j b ≤ (S.tech j).psi a - h j a := hh.mono_sub j hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `|(Th)_i(a) − (Th)_i(b)| ≤ |ψ_i(a) − ψ_i(b)|` for `h ∈ F`. -/
theorem IsInFs.abs_Ts_sub_le {h : ι → ℝ → ℝ} (hh : S.IsInFs h) (i : ι) {a b : ℝ}
    (ha : a ∈ Icc 0 S.B) (hb : b ∈ Icc 0 S.B) :
    |S.Ts h i a - S.Ts h i b| ≤ |(S.tech i).psi a - (S.tech i).psi b| :=
  (ex_18_8 hh).abs_sub_le i ha hb

variable (S) in
/-- **Equicontinuity of `T(F)`** in the stochastic case (the analogue of Proposition 18.5):
one `δ` for all `h ∈ F`, for each state. -/
theorem Ts_equicontinuous (i : ι) : ∀ ε > 0, ∃ δ > 0, ∀ h, S.IsInFs h →
    ∀ a ∈ Icc 0 S.B, ∀ b ∈ Icc 0 S.B, dist a b < δ → |S.Ts h i a - S.Ts h i b| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hψ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := S.B)).uniformContinuousOn_of_continuous
      ((S.tech i).psi_continuousOn.mono Icc_subset_Ici_self)) ε hε
  refine ⟨δ, hδ, fun h hh a ha b hb hab => ?_⟩
  have := hψ a ha b hb hab
  rw [Real.dist_eq] at this
  exact (hh.abs_Ts_sub_le i ha hb).trans_lt this

/-- Pointwise convergence of the right sides of (9) when `hₐ → h` pointwise on `K`. -/
theorem rhsConvergesAt_of_tendsto {α : Type*} {l : Filter α} {hs : α → ι → ℝ → ℝ}
    {h : ι → ℝ → ℝ}
    (hconv : ∀ j, ∀ y ∈ Icc 0 S.B, Tendsto (fun a => hs a j y) l (𝓝 (h j y))) (i : ι) {y : ℝ}
    (hyK : y ∈ Icc 0 S.B) :
    RHSConvergesAt l (fun a => S.Zs (hs a) i) (fun a => S.Rs (hs a) i) (S.Zs h i) (S.Rs h i)
      y := by
  have hcv : ∀ j, Tendsto (fun a => (S.tech j).psi y - hs a j y) l
      (𝓝 ((S.tech j).psi y - h j y)) := fun j => tendsto_const_nhds.sub (hconv j y hyK)
  constructor
  · rintro ⟨j0, hj0, hc0⟩ M0
    set m := S.β * (1 - S.θ) * S.π i j0 * (S.tech j0).f' y
    have hm : 0 < m := mul_pos (mul_pos S.coef_pos hj0) ((S.tech j0).f'_pos hyK.1)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (S.isMarginalUtility.inada.eventually_gt_atTop (|M0| / m))
    filter_upwards [(hcv j0).eventually_lt_const (lt_of_le_of_lt hc0 hε)] with a ha
    by_cases hZ : S.Zs (hs a) i y
    · exact Or.inl hZ
    · right
      have hc : 0 < (S.tech j0).psi y - hs a j0 y :=
        lt_of_not_ge fun hle => hZ ⟨j0, hj0, hle⟩
      have hU : |M0| / m < S.U' ((S.tech j0).psi y - hs a j0 y) := hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact ha, hc⟩
      rw [div_lt_iff₀ hm] at hU
      have hsingle := Finset.single_le_sum (f := fun j => S.π i j * ((S.tech j).f' y *
        S.U' ((S.tech j).psi y - hs a j y))) (fun j _ => IsInFs.term_nonneg i j hyK.1 hZ)
        (Finset.mem_univ j0)
      have h2 := mul_le_mul_of_nonneg_left hsingle S.coef_pos.le
      have h1 : m * S.U' ((S.tech j0).psi y - hs a j0 y) = S.β * (1 - S.θ) *
          (S.π i j0 * ((S.tech j0).f' y * S.U' ((S.tech j0).psi y - hs a j0 y))) := by
        simp only [m]; ring
      simp only [Rs]
      linarith [le_abs_self M0]
  · intro hz
    have hpos : ∀ j, 0 < S.π i j → 0 < (S.tech j).psi y - h j y :=
      fun j hj => lt_of_not_ge fun hle => hz ⟨j, hj, hle⟩
    refine ⟨?_, ?_⟩
    · have : ∀ᶠ a in l, ∀ j, 0 < S.π i j → 0 < (S.tech j).psi y - hs a j y := by
        refine eventually_all.2 fun j => ?_
        by_cases hj : 0 < S.π i j
        · exact ((hcv j).eventually_const_lt (hpos j hj)).mono fun a ha _ => ha
        · exact Eventually.of_forall fun a hj' => absurd hj' hj
      exact this.mono fun a ha ⟨j, hj, hle⟩ => absurd (ha j hj) (not_lt.2 hle)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => ?_)
      rcases (S.π_nonneg i j).eq_or_lt with h0 | hj
      · rw [← h0]; simpa using tendsto_const_nhds
      · exact tendsto_const_nhds.mul (tendsto_const_nhds.mul
          ((S.isMarginalUtility.cont.continuousAt (Ioi_mem_nhds (hpos j hj))).tendsto.comp
            (hcv j)))

/-- **Exercise 18.6, stochastic case, pointwise step**: if `hₐ → h` pointwise on `K` within
`F`, then `(T hₐ)_i(k) → (T h)_i(k)`. -/
theorem Ts_tendsto {α : Type*} {l : Filter α} {hs : α → ι → ℝ → ℝ} {h : ι → ℝ → ℝ}
    (hhs : ∀ a, S.IsInFs (hs a)) (hh : S.IsInFs h)
    (hconv : ∀ j, ∀ y ∈ Icc 0 S.B, Tendsto (fun a => hs a j y) l (𝓝 (h j y))) (i : ι)
    {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    Tendsto (fun a => S.Ts (hs a) i k) l (𝓝 (S.Ts h i k)) := by
  have hP := (S.tech i).psi_pos hk.1
  have hPB := S.psi_le_B i hk
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := eventually_abs_eulerCross_sub_le (u := S.U') (Zs := fun a => S.Zs (hs a) i)
    (Rs := fun a => S.Rs (hs a) i) S.isMarginalUtility (hh.isEulerRHS i)
    (fun a => (hhs a).isEulerRHS i) hP hPB
    (fun y hy0 hyP => rhsConvergesAt_of_tendsto hconv i ⟨hy0, hyP.le.trans hPB⟩)
    (half_pos hε)
  filter_upwards [hev] with a ha
  rw [Real.dist_eq]
  exact ha.trans_lt (half_lt_self hε)

/-- **Exercise 18.6, stochastic case**: pointwise convergence `hₐ → h` on `K` within `F` gives
uniform convergence `T hₐ → T h` on `K`, in every state (equicontinuity of `T(F)` and a finite
net of `K`). In particular `T` is continuous on `F` for the sup norm. -/
theorem Ts_tendsto_uniform {α : Type*} {l : Filter α} {hs : α → ι → ℝ → ℝ} {h : ι → ℝ → ℝ}
    (hhs : ∀ a, S.IsInFs (hs a)) (hh : S.IsInFs h)
    (hconv : ∀ j, ∀ y ∈ Icc 0 S.B, Tendsto (fun a => hs a j y) l (𝓝 (h j y))) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ i, ∀ k ∈ Icc 0 S.B, |S.Ts (hs a) i k - S.Ts h i k| < ε := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨δ, hδ, hψ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := S.B)).uniformContinuousOn_of_continuous
      ((S.tech i).psi_continuousOn.mono Icc_subset_Ici_self)) (ε / 4) (by linarith)
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := S.B)) hδ
  have hev : ∀ᶠ a in l, ∀ x ∈ t, |S.Ts (hs a) i x - S.Ts h i x| < ε / 4 := by
    refine (htfin.eventually_all).2 fun x hx => ?_
    have := Metric.tendsto_nhds.1 (Ts_tendsto hhs hh hconv i (htK hx)) (ε / 4) (by linarith)
    exact this.mono fun a ha => by rwa [Real.dist_eq] at ha
  filter_upwards [hev] with a ha k hk
  obtain ⟨x, hx, hkx⟩ := mem_iUnion₂.1 (hcover hk)
  have hxK := htK hx
  have hd := hψ k hk x hxK hkx
  rw [Real.dist_eq] at hd
  have e1 := (hhs a).abs_Ts_sub_le i hk hxK
  have e2 := hh.abs_Ts_sub_le i hxK hk
  have e3 := ha x hx
  rw [abs_sub_comm ((S.tech i).psi x)] at e2
  calc |S.Ts (hs a) i k - S.Ts h i k|
      ≤ |S.Ts (hs a) i k - S.Ts (hs a) i x| + |S.Ts (hs a) i x - S.Ts h i x| +
          |S.Ts h i x - S.Ts h i k| := by
        have := abs_sub_le (S.Ts (hs a) i k) (S.Ts (hs a) i x) (S.Ts h i k)
        have := abs_sub_le (S.Ts (hs a) i x) (S.Ts h i x) (S.Ts h i k)
        linarith
    _ < ε := by linarith

/-! ### The least fixed point -/

variable (S)

/-- The operator `T` of (9) on functions `ι → ℝ → ℝ`. -/
noncomputable def TsOp (h : ι → ℝ → ℝ) : ι → ℝ → ℝ := fun i k => S.Ts h i k

/-- The iterates `Tⁿ0` from the least element `0` of `F`. -/
noncomputable def Tsit (n : ℕ) : ι → ℝ → ℝ := (S.TsOp)^[n] (fun _ _ => 0)

/-- `Tⁿ⁺¹0 = T(Tⁿ0)`. -/
theorem Tsit_succ (n : ℕ) : S.Tsit (n + 1) = S.TsOp (S.Tsit n) :=
  Function.iterate_succ_apply' _ _ _

/-- Every iterate lies in `F`. -/
theorem isInFs_Tsit (n : ℕ) : S.IsInFs (S.Tsit n) := by
  induction n with
  | zero => exact S.isInFs_zero
  | succ n ih => rw [Tsit_succ]; exact ex_18_8 ih

/-- The iterates increase: `Tⁿ0 ≤ Tⁿ⁺¹0` on `K`. -/
theorem Tsit_le_succ (n : ℕ) : ∀ j, ∀ k ∈ Icc 0 S.B, S.Tsit n j k ≤ S.Tsit (n + 1) j k := by
  induction n with
  | zero =>
    intro j k hk
    rw [Tsit_succ]
    exact (Ts_mem_Icc _ j hk).1
  | succ n ih =>
    intro j k hk
    have e1 : S.Tsit (n + 1) j k = S.Ts (S.Tsit n) j k := by rw [Tsit_succ]; rfl
    have e2 : S.Tsit (n + 1 + 1) j k = S.Ts (S.Tsit (n + 1)) j k := by
      rw [Tsit_succ S (n + 1)]; rfl
    rw [e2, e1]
    exact ex_18_8_mono ih j hk

/-- A supersolution `h ∈ F` (`T h ≤ h` on `K`) lies above every iterate `Tⁿ0`. -/
theorem Tsit_le_of_super {h : ι → ℝ → ℝ} (hh : S.IsInFs h)
    (hsup : ∀ j, ∀ k ∈ Icc 0 S.B, S.Ts h j k ≤ h j k) (n : ℕ) :
    ∀ j, ∀ k ∈ Icc 0 S.B, S.Tsit n j k ≤ h j k := by
  induction n with
  | zero => exact fun j k hk => hh.nonneg j k hk
  | succ n ih =>
    intro j k hk
    rw [Tsit_succ]
    exact (ex_18_8_mono ih j hk).trans (hsup j k hk)

/-- The least fixed point: `lfp_j(k) = sup_n (Tⁿ0)_j(k)`. -/
noncomputable def lfp (j : ι) (k : ℝ) : ℝ := ⨆ n, S.Tsit n j k

/-- `Tⁿ0 → lfp` pointwise on `K` (monotone and bounded by `ψ`). -/
theorem tendsto_Tsit (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    Tendsto (fun n => S.Tsit n j k) atTop (𝓝 (S.lfp j k)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => S.Tsit_le_succ n j k hk)
    ⟨(S.tech j).psi k, forall_mem_range.2 fun n => (S.isInFs_Tsit n).le_psi j k hk⟩

/-- `lfp ∈ F`. -/
theorem isInFs_lfp : S.IsInFs S.lfp where
  cont j := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1 ((S.tech j).psi_continuousOn.mono
      (Icc_subset_Ici_self : Icc (0 : ℝ) S.B ⊆ Ici 0)) b hb ε hε
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    have h1 := hψ a ha hab
    rw [Real.dist_eq] at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    exact le_of_tendsto' (((S.tendsto_Tsit j ha).sub (S.tendsto_Tsit j hb)).abs)
      fun n => (S.isInFs_Tsit n).abs_sub_le j ha hb
  nonneg j k hk := ge_of_tendsto' (S.tendsto_Tsit j hk) fun n => (S.isInFs_Tsit n).nonneg j k hk
  le_psi j k hk := le_of_tendsto' (S.tendsto_Tsit j hk) fun n => (S.isInFs_Tsit n).le_psi j k hk
  mono j a ha b hb hab := le_of_tendsto_of_tendsto' (S.tendsto_Tsit j ha) (S.tendsto_Tsit j hb)
    fun n => (S.isInFs_Tsit n).mono j ha hb hab
  mono_sub j a ha b hb hab := le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.sub (S.tendsto_Tsit j ha)) (tendsto_const_nhds.sub (S.tendsto_Tsit j hb))
    fun n => (S.isInFs_Tsit n).mono_sub j ha hb hab

/-- `lfp` is a fixed point of `T` on `K`. -/
theorem Ts_lfp (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : S.Ts S.lfp i k = S.lfp i k := by
  have h1 : Tendsto (fun n => S.Ts (S.Tsit n) i k) atTop (𝓝 (S.Ts S.lfp i k)) :=
    Ts_tendsto S.isInFs_Tsit S.isInFs_lfp (fun j y hy => S.tendsto_Tsit j hy) i hk
  have h2 : Tendsto (fun n => S.Ts (S.Tsit n) i k) atTop (𝓝 (S.lfp i k)) := by
    have := (tendsto_add_atTop_iff_nat 1).2 (S.tendsto_Tsit i hk)
    refine this.congr fun n => ?_
    rw [Tsit_succ]; rfl
  exact tendsto_nhds_unique h1 h2

/-- `Tⁿ0 → lfp` **uniformly** on `K`. -/
theorem tendstoUniformly_Tsit {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i, ∀ k ∈ Icc 0 S.B, |S.Tsit (n + 1) i k - S.lfp i k| < ε := by
  have := Ts_tendsto_uniform S.isInFs_Tsit S.isInFs_lfp (fun j y hy => S.tendsto_Tsit j hy) hε
  filter_upwards [this] with n hn i k hk
  rw [Tsit_succ, ← S.Ts_lfp i hk]
  exact hn i k hk

/-- `lfp` lies below every supersolution in `F`, in particular below every fixed point. -/
theorem lfp_le_of_super {h : ι → ℝ → ℝ} (hh : S.IsInFs h)
    (hsup : ∀ j, ∀ k ∈ Icc 0 S.B, S.Ts h j k ≤ h j k) (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.lfp j k ≤ h j k :=
  le_of_tendsto' (S.tendsto_Tsit j hk) fun n => S.Tsit_le_of_super hh hsup n j k hk

/-- **Least and greatest fixed points** in the stochastic case (corrected p. 560): `lfp` (the
limit of `Tⁿ0`) and `ψ` are fixed points of `T` in `F`, and every fixed point `h ∈ F` satisfies
`lfp ≤ h ≤ ψ` on `K`. The greatest fixed point `ψ` is degenerate: consumption is zero and (9)
holds nowhere (`no_solution_at_psi`). -/
theorem stoch_least_greatest :
    S.IsInFs S.lfp ∧ (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts S.lfp i k = S.lfp i k) ∧
      S.IsInFs (fun j k => (S.tech j).psi k) ∧
      (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts (fun j k => (S.tech j).psi k) i k = (S.tech i).psi k) ∧
      ∀ h, S.IsInFs h → (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts h i k = h i k) →
        ∀ j, ∀ k ∈ Icc 0 S.B, S.lfp j k ≤ h j k ∧ h j k ≤ (S.tech j).psi k :=
  ⟨S.isInFs_lfp, fun i _ hk => S.Ts_lfp i hk, S.isInFs_psi, fun i _ hk => S.Ts_psi i hk,
    fun _ hh hfix j k hk => ⟨S.lfp_le_of_super hh (fun j k hk => (hfix j k hk).le) j hk,
      hh.le_psi j k hk⟩⟩

/-- **A non-degenerate equilibrium** (corrected p. 560). Under the cross-state condition, if
some supersolution `h̄ ∈ F` (`T h̄ ≤ h̄`) has positive consumption `h̄_j < ψ_j` on `K`, then the
least fixed point `lfp` has positive consumption everywhere and solves (9) as an equation at every
`(k, ξ_i)`, with positive consumption today and in every reachable state tomorrow. -/
theorem lfp_equilibrium_of_super (hCS : S.CrossState) {hbar : ι → ℝ → ℝ} (hhb : S.IsInFs hbar)
    (hsup : ∀ j, ∀ k ∈ Icc 0 S.B, S.Ts hbar j k ≤ hbar j k)
    (hpos : ∀ j, ∀ k ∈ Icc 0 S.B, hbar j k < (S.tech j).psi k) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    S.lfp i k < (S.tech i).psi k ∧ ¬ S.Zs S.lfp i (S.lfp i k) ∧
      S.U' ((S.tech i).psi k - S.lfp i k) = S.Rs S.lfp i (S.lfp i k) := by
  have hlt : S.lfp i k < (S.tech i).psi k :=
    (S.lfp_le_of_super hhb hsup i hk).trans_lt (hpos i k hk)
  rcases ex_18_8_spec hCS S.isInFs_lfp i hk with ⟨-, h2, h3, -⟩ | ⟨h1, -⟩
  · rw [S.Ts_lfp i hk] at h2 h3
    exact ⟨hlt, h2, h3⟩
  · rw [S.Ts_lfp i hk] at h1
    exact absurd h1 hlt.ne

/-! ### The hypothesis of `lfp_equilibrium_of_super` holds with identical technologies -/

/-- With one technology `M` in every state, a deterministic equilibrium `g` (a fixed point of
`M.T` in `M.F`) is a fixed point of (9) with positive consumption. -/
theorem identical_tech_fixed (M : GlobalModel) (hM : ∀ j, S.tech j = M)
    {g : Icc 0 M.kbar →ᵇ ℝ} (hg : g ∈ M.F) (hfix : M.T g = g) :
    S.IsInFs (fun _ k => M.ext g k) ∧
      (∀ i, ∀ k ∈ Icc 0 S.B, S.Ts (fun _ k => M.ext g k) i k = M.ext g k) ∧
      ∀ j, ∀ k ∈ Icc 0 S.B, M.ext g k < (S.tech j).psi k := by
  have hB : M.kbar = S.B := by
    obtain ⟨j, hj⟩ := S.B_eq
    rw [← hj, hM j]
  have hgF : M.IsInF (M.ext g) := hg
  have hβ : M.β = S.β := by
    obtain ⟨j, -⟩ := S.B_eq
    rw [← hM j, S.tech_β j]
  have hθ : M.θ = S.θ := by
    obtain ⟨j, -⟩ := S.B_eq
    rw [← hM j, S.tech_θ j]
  have hU : M.U' = S.U' := by
    obtain ⟨j, -⟩ := S.B_eq
    rw [← hM j, S.tech_U' j]
  have heuler := (M.isFixedPt_iff_euler hg).1 hfix
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ => hB ▸ hgF.cont, fun j k hk => hgF.nonneg k (hB ▸ hk),
      fun j k hk => by rw [hM j]; exact hgF.le_psi k (hB ▸ hk),
      fun _ => hB ▸ hgF.mono, fun j => ?_⟩
    rw [hM j]
    exact hB ▸ hgF.mono_sub
  · intro i k hk
    have hZ : S.Zs (fun _ k => M.ext g k) i = M.Zd (M.ext g) := by
      funext y
      apply propext
      constructor
      · rintro ⟨j, -, hj⟩
        rw [hM j] at hj
        exact hj
      · intro hy
        obtain ⟨j, hj⟩ := S.exists_pi_pos i
        exact ⟨j, hj, by rw [hM j]; exact hy⟩
    have hR : S.Rs (fun _ k => M.ext g k) i = M.Rd (M.ext g) := by
      funext y
      simp only [Rs, GlobalModel.Rd, hM, ← Finset.sum_mul, S.π_sum, one_mul, hβ, hθ, hU]
      ring
    have hTv : S.Ts (fun _ k => M.ext g k) i k = M.Tval (M.ext g) k := by
      simp only [Ts, GlobalModel.Tval, hZ, hR, hM i, hU]
    rw [hTv, ← GlobalModel.ext_T hg (hB ▸ hk), hfix]
  · intro j k hk
    rw [hM j]
    have := (heuler k (hB ▸ hk)).1
    linarith

/-- With one technology in every state the cross-state condition holds (it is Assumption
18.1d). -/
theorem crossState_of_identical (M : GlobalModel) (hM : ∀ j, S.tech j = M) : S.CrossState := by
  intro i
  have hβ : M.β = S.β := by rw [← hM i, S.tech_β i]
  have hθ : M.θ = S.θ := by rw [← hM i, S.tech_θ i]
  have hU : M.U' = S.U' := by rw [← hM i, S.tech_U' i]
  simp only [hM, ← Finset.sum_mul, S.π_sum, one_mul]
  have h1 := M.one_lt_euler_zero
  have h2 := M.U'_pos (M.psi_pos le_rfl)
  rw [hβ, hθ, hU] at *
  nlinarith

/-- **Existence of a non-degenerate stochastic equilibrium** when every state has the same
technology: the least fixed point `lfp` solves (9) with positive consumptions everywhere. -/
theorem exists_nondegenerate_equilibrium_identical (M : GlobalModel) (hM : ∀ j, S.tech j = M)
    (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.lfp i k < (S.tech i).psi k ∧ ¬ S.Zs S.lfp i (S.lfp i k) ∧
      S.U' ((S.tech i).psi k - S.lfp i k) = S.Rs S.lfp i (S.lfp i k) := by
  obtain ⟨g, hg, hfix⟩ := M.exists_equilibrium
  obtain ⟨h1, h2, h3⟩ := S.identical_tech_fixed M hM hg hfix
  exact S.lfp_equilibrium_of_super (S.crossState_of_identical M hM) h1
    (fun j k hk => (h2 j k hk).le) h3 i hk

end StochModel

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An indirect approach to equilibria with distortions

SLP §18.1, pp. 543–547. An individual with own capital `x` facing a given aggregate capital path
`k_t` consumes `c_t = a_t + b_t x_t − x_{t+1}`, where the intercept `a_t` (wages, rebates) and the
slope `b_t` (after-tax return on own capital) are determined by `k_t`:

* untaxed economy (§18.1 (2)): `a_t = f(k_t) − k_t f′(k_t)`, `b_t = f′(k_t)`;
* capital-income tax `θ` with lump-sum rebate (§18.1 (3)): `a_t = f(k_t) − (1 − θ) k_t f′(k_t)`,
  `b_t = (1 − θ) f′(k_t)`;
* Exercise 18.2 (tax `α` on all income thrown away, tax `θ` on capital income rebated):
  `a_t = (1 − α) f(k_t) − (1 − α − θ) k_t f′(k_t)`, `b_t = (1 − α − θ) f′(k_t)`.

The individual's problem is a concave sequence problem whose return depends on time through the
given path. The book's and the manual's arguments rest on the sufficiency of the Euler equation and
the transversality condition for such a problem (a non-stationary version of Theorem 4.15), which
is proved here first:

* `euler_telescope`: the telescoping identity behind Theorem 4.15.
* `euler_partial_sum_le`: the finite-horizon bound.
* `euler_tvc_optimal`, `euler_tvc_strict`, `euler_tvc_unique`, `euler_tvc_isGreatest`:
  Euler + transversality ⇒ optimal; with strict concavity, the unique optimum.
* `tvc_of_bounded`: the transversality condition holds along bounded paths (`0 ≤ β < 1`).

Results of §18.1.

* **Exercise 18.1** (`ex_18_1`, p. 544): the planner's path `k_{t+1} = g(k_t)`, satisfying the
  planner's Euler equation and transversality condition, is the unique optimum of the individual
  who starts with `x_0 = k_0` and expects aggregate capital to follow `g`. So
  `G(k, k; g) = g(k)` (`x_1 = g(k_0)`) and `V(k, k; g) = v(k)` (the individual's maximal value
  is the planner's value).
* `budget_rebate` (p. 545): wages + after-tax capital income + rebate
  `= f(k) + (1 − θ)(x − k) f′(k)`.
* `pseudo_economy_solves_6_7` (p. 546): if `w`, `ĥ` satisfy §18.1 (9)–(10) with
  `β̂ = (1 − θ)β`, then `φ = (1 − θ) w′`, `h = ĥ` satisfy §18.1 (6)–(7).
* `indirect_equilibrium` (p. 546): the pseudo-planner's path is the unique optimum of an
  individual of the taxed economy, provided the individual's transversality condition holds.
* **Exercise 18.2** (`ex_18_2_budget`, `ex_18_2_foc`, `ex_18_2`, p. 547): the economy with
  both taxes behaves like an untaxed economy with production function `(1 − α) f` and discount
  factor `β̂ = β(1 − α − θ)/(1 − α)`.

**Corrections.**
* (NOTE 18.1-A, p. 544.) The domain of the individual's problem is not stated. Here: `x_t ≥ 0`
  (no borrowing) and `c_t ≥ 0`, with `x_0` given (`IndivFeasible`); values are infinite sums
  assumed to exist (`HasSum`). The problem is posed as a sequence problem, not through the
  functional equation (2), whose unique solvability on the non-compact state space would need
  further hypotheses.
* (NOTE 18.1-B, manual Ex. 18.1.) The manual's argument uses the *sufficiency* of Euler +
  transversality for the individual's time-varying problem and the *uniqueness* of his optimum.
  Both are proved here (`euler_tvc_optimal`, `euler_tvc_unique`); they need `b_t ≥ 0`
  (i.e. `f′(k_t) ≥ 0`), `U′ ≥ 0` and, for uniqueness, strict concavity of `U`. Verified.
* (NOTE 18.1-C, p. 546.) A solution of (6)–(7) is only a candidate: the identification
  `h = ĥ` needs the individual's transversality condition, with his own discount factor `β`,
  `β^t (1 − θ) f′(k_t) U′(c_t) k_t → 0`. The pseudo-planner's condition uses `β̂^t`. The
  individual's condition implies the pseudo-planner's (`tvc_indiv_imp_pseudo`) but not
  conversely (`tvc_pseudo_not_imp_indiv_counterexample`). The individual's condition holds
  along bounded paths (`tvc_of_bounded`), e.g. paths converging to an interior steady state.
  Verified; `indirect_equilibrium` assumes the individual's condition.
* (NOTE 18.1-D, manual Ex. 18.2.) The manual's `β̂ = (1 − α − θ)/(1 − α)` omits the factor
  `β`. With it the first-order condition fails whenever `β < 1`
  (`ex_18_2_manual_counterexample`); the correct value is `β(1 − α − θ)/(1 − α)`. Verified.
* (NOTE 18.1-E, p. 547.) (i) Exercise 18.2 needs `α + θ < 1`: otherwise `β̂ ≤ 0`
  (`ex_18_2_requires_sum_lt_one`). (ii) The stated answer is for the additive reading (capital
  income taxed at `α + θ`). Under the sequential reading (the `θ`-tax levied on capital income
  net of the `α`-tax) the budget is `(1 − α) f(k) + (1 − α)(1 − θ)(x − k) f′(k)`
  (`ex_18_2_sequential_budget`) and the Euler equation is that of the pseudo-economy with
  discount factor `β(1 − θ)` (`ex_18_2_sequential_euler`), which differs from the book's value
  when `α, θ > 0` (`ex_18_2_sequential_ne`). Verified.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- Consumption at date `t` of an individual with capital path `x`, budget intercepts `a` and
after-tax returns `b`: `c_t = a_t + b_t x_t − x_{t+1}`. -/
def consPath (a b x : ℕ → ℝ) (t : ℕ) : ℝ := a t + b t * x t - x (t + 1)

/-- A capital path `x` is feasible for the individual starting from `x₀`: `x_0 = x₀`, capital
and consumption nonnegative at every date. -/
def IndivFeasible (a b : ℕ → ℝ) (x₀ : ℝ) (x : ℕ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∀ t, 0 ≤ x t ∧ 0 ≤ consPath a b x t

/-- The set of attainable lifetime utilities `∑ β^t U(c_t)` of feasible paths from `x₀`. -/
def indivValues (U : ℝ → ℝ) (β : ℝ) (a b : ℕ → ℝ) (x₀ : ℝ) : Set ℝ :=
  {S | ∃ x, IndivFeasible a b x₀ x ∧ HasSum (fun t => β ^ t * U (consPath a b x t)) S}

/-! ### Sufficiency of Euler + transversality for the individual's problem -/

/-- Tangent-line inequality for a concave function on `[0, ∞)` differentiable at `d`. -/
theorem concave_le_tangent {U : ℝ → ℝ} (hU : ConcaveOn ℝ (Ici 0) U) {c d : ℝ} (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hUd : DifferentiableAt ℝ U d) : U c ≤ U d + deriv U d * (c - d) := by
  rcases lt_trichotomy c d with h | rfl | h
  · have h1 := hU.deriv_le_slope (mem_Ici.2 hc) (mem_Ici.2 hd) h hUd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    nlinarith
  · simp
  · have h1 := hU.slope_le_deriv (mem_Ici.2 hd) (mem_Ici.2 hc) h hUd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
    linarith

/-- Strict tangent-line inequality for a strictly concave function at `c ≠ d`. -/
theorem strictConcave_lt_tangent {U : ℝ → ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ≠ d) (hUd : DifferentiableAt ℝ U d) :
    U c < U d + deriv U d * (c - d) := by
  rcases lt_or_gt_of_ne hcd with h | h
  · have h1 := hU.deriv_lt_slope (mem_Ici.2 hc) (mem_Ici.2 hd) h hUd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h1
    nlinarith
  · have h1 := hU.slope_lt_deriv (mem_Ici.2 hd) (mem_Ici.2 hc) h hUd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h1
    linarith

/-- **Telescoping identity** (proof of Theorem 4.15). If the path `xs` satisfies the Euler
equation `U′(c*_t) = β b_{t+1} U′(c*_{t+1})` and `x_0 = xs_0`, then
`∑_{t<T} β^t U′(c*_t)(c_t − c*_t) = β^T b_T U′(c*_T)(xs_T − x_T)`. -/
theorem euler_telescope (U : ℝ → ℝ) (β : ℝ) (a b xs x : ℕ → ℝ)
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (h0 : x 0 = xs 0) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * (deriv U (consPath a b xs t) *
        (consPath a b x t - consPath a b xs t)) =
      β ^ T * b T * deriv U (consPath a b xs T) * (xs T - x T) := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [sum_range_succ, ih, heul T]
    generalize deriv U (consPath a b xs (T + 1)) = D
    simp only [consPath]
    ring

/-- **Finite-horizon bound.** Along a path `xs` with nonnegative consumption satisfying the Euler
equation, every feasible path `x` from `xs_0` has
`∑_{t<T} β^t U(c_t) ≤ ∑_{t<T} β^t U(c*_t) + β^T b_T U′(c*_T)(xs_T − x_T)`. -/
theorem euler_partial_sum_le {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (hx : IndivFeasible a b (xs 0) x) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * (xs T - x T) := by
  rw [← euler_telescope U β a b xs x heul hx.1 T, ← sum_add_distrib]
  refine sum_le_sum fun t _ => ?_
  have h := concave_le_tangent hU (hx.2 t).2 (hxs t) (hUd t)
  have hb : 0 ≤ β ^ t := pow_nonneg hβ t
  nlinarith

/-- **Euler + transversality are sufficient** (non-stationary Theorem 4.15). Let `U` be concave
on `[0, ∞)`, `0 ≤ β`, and let the path `xs` have nonnegative consumption, satisfy the Euler
equation and the transversality condition `β^T b_T U′(c*_T) xs_T → 0`, with
`b_t U′(c*_t) ≥ 0`. Then no feasible path from `xs_0` has a larger value. -/
theorem euler_tvc_optimal {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') : S ≤ S' := by
  have key : ∀ T, ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * xs T := by
    intro T
    refine (euler_partial_sum_le hU hβ hUd hxs heul hx T).trans ?_
    have h1 : 0 ≤ β ^ T * (b T * deriv U (consPath a b xs T)) :=
      mul_nonneg (pow_nonneg hβ T) (hp T)
    have h2 := (hx.2 T).1
    nlinarith
  have hlim := hS'.tendsto_sum_nat.add htvc
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' hS.tendsto_sum_nat hlim key

/-- **Strict version.** If moreover `U` is strictly concave, `β > 0`, and the feasible path `x`
has a different consumption from `xs` at some date, then its value is strictly smaller. -/
theorem euler_tvc_strict {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S')
    {t₀ : ℕ} (ht₀ : consPath a b x t₀ ≠ consPath a b xs t₀) : S < S' := by
  set r : ℕ → ℝ := fun t => β ^ t * (U (consPath a b xs t) + deriv U (consPath a b xs t) *
    (consPath a b x t - consPath a b xs t) - U (consPath a b x t)) with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => by
    have h := concave_le_tangent hU.concaveOn (hx.2 t).2 (hxs t) (hUd t)
    exact mul_nonneg (pow_nonneg hβ.le t) (by linarith)
  have hrt₀ : 0 < r t₀ := by
    have h := strictConcave_lt_tangent hU (hx.2 t₀).2 (hxs t₀) ht₀ (hUd t₀)
    exact mul_pos (pow_pos hβ t₀) (by linarith)
  have key : ∀ T, t₀ < T → ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * xs T - r t₀ := by
    intro T hT
    have htel := euler_telescope U β a b xs x heul hx.1 T
    have hsum : ∑ t ∈ range T, β ^ t * U (consPath a b x t) =
        ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
          ∑ t ∈ range T, β ^ t * (deriv U (consPath a b xs t) *
            (consPath a b x t - consPath a b xs t)) - ∑ t ∈ range T, r t := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      simp only [hr]
      ring
    have hle : r t₀ ≤ ∑ t ∈ range T, r t :=
      single_le_sum (fun t _ => hr0 t) (mem_range.2 hT)
    have h1 : 0 ≤ β ^ T * (b T * deriv U (consPath a b xs T)) :=
      mul_nonneg (pow_nonneg hβ.le T) (hp T)
    have h2 := (hx.2 T).1
    rw [hsum, htel]
    nlinarith
  have hlim := (hS'.tendsto_sum_nat.add htvc).sub_const (r t₀)
  rw [add_zero] at hlim
  have hle : S ≤ S' - r t₀ :=
    le_of_tendsto_of_tendsto hS.tendsto_sum_nat hlim
      (eventually_atTop.2 ⟨t₀ + 1, fun T hT => key T (by omega)⟩)
  linarith

/-- **Uniqueness of the optimum.** Under the hypotheses of `euler_tvc_strict`, a feasible path
from `xs_0` whose value is at least that of `xs` coincides with `xs`. -/
theorem euler_tvc_unique {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') (hge : S' ≤ S) : x = xs := by
  have hc : ∀ t, consPath a b x t = consPath a b xs t := fun t => by
    by_contra h
    have := euler_tvc_strict hU hβ hUd hxs hp heul htvc hx hS hS' h
    linarith
  funext t
  induction t with
  | zero => exact hx.1
  | succ t ih =>
    have h := hc t
    simp only [consPath] at h
    rw [ih] at h
    linarith

/-- **The optimal value.** Under the hypotheses of `euler_tvc_optimal`, if `xs` is feasible from
`xs_0` with value `S'`, then `S'` is the greatest attainable value. -/
theorem euler_tvc_isGreatest {U : ℝ → ℝ} {β : ℝ} {a b xs : ℕ → ℝ} {S' : ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hfeas : IndivFeasible a b (xs 0) xs)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') :
    IsGreatest (indivValues U β a b (xs 0)) S' :=
  ⟨⟨xs, hfeas, hS'⟩, fun _ ⟨_, hx, hS⟩ =>
    euler_tvc_optimal hU hβ hUd (fun t => (hfeas.2 t).2) hp heul htvc hx hS hS'⟩

/-- **Transversality along bounded paths.** If `0 ≤ β < 1` and `z` is bounded, `β^t z_t → 0`;
e.g. `z_t = b_t U′(c_t) x_t` along a path converging to an interior steady state. -/
theorem tvc_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {z : ℕ → ℝ} {M : ℝ}
    (hz : ∀ t, |z t| ≤ M) : Tendsto (fun t => β ^ t * z t) atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  refine squeeze_zero_norm (fun t => ?_) (by simpa using hpow.mul_const M)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  exact mul_le_mul_of_nonneg_left (hz t) (pow_nonneg hβ0 t)

/-! ### Exercise 18.1 -/

/-- **Exercise 18.1** (p. 544). Let `U` be strictly concave on `[0, ∞)`, differentiable with
`U′ ≥ 0` there, `β > 0`, and let `k_{t+1} = g(k_t)` be a path with nonnegative capital and
consumption, `f′(k_t) ≥ 0`, satisfying the planner's Euler equation
`U′[f(k_t) − k_{t+1}] = β U′[f(k_{t+1}) − k_{t+2}] f′(k_{t+1})` and transversality condition
`β^t U′[f(k_t) − k_{t+1}] f′(k_t) k_t → 0`, with value `v = ∑ β^t U[f(k_t) − k_{t+1}]`.
For the individual with budget (2) given the aggregate path `k` (`a_t = f(k_t) − k_t f′(k_t)`,
`b_t = f′(k_t)`) starting from `x_0 = k_0`:
(i) the path `x = k` is feasible and its consumption is `f(k_t) − k_{t+1}`;
(ii) `v` is the greatest attainable value (`V(k_0, k_0; g) = v(k_0)`);
(iii) every optimal path equals `k`, so its first choice is `x_1 = g(k_0)`
(`G(k_0, k_0; g) = g(k_0)`). -/
theorem ex_18_1 {U f g : ℝ → ℝ} {β v : ℝ} {k : ℕ → ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hg : ∀ t, k (t + 1) = g (k t)) (hk : ∀ t, 0 ≤ k t) (hc : ∀ t, 0 ≤ f (k t) - k (t + 1))
    (hf' : ∀ t, 0 ≤ deriv f (k t))
    (heul : ∀ t, deriv U (f (k t) - k (t + 1)) =
      β * deriv U (f (k (t + 1)) - k (t + 2)) * deriv f (k (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * deriv U (f (k t) - k (t + 1)) * deriv f (k t) * k t)
      atTop (𝓝 0))
    (hv : HasSum (fun t => β ^ t * U (f (k t) - k (t + 1))) v) :
    (∀ t, consPath (fun t => f (k t) - k t * deriv f (k t)) (fun t => deriv f (k t)) k t =
        f (k t) - k (t + 1)) ∧
      IsGreatest (indivValues U β (fun t => f (k t) - k t * deriv f (k t))
        (fun t => deriv f (k t)) (k 0)) v ∧
      ∀ x S, IndivFeasible (fun t => f (k t) - k t * deriv f (k t)) (fun t => deriv f (k t))
          (k 0) x →
        HasSum (fun t => β ^ t * U (consPath (fun t => f (k t) - k t * deriv f (k t))
          (fun t => deriv f (k t)) x t)) S → v ≤ S → x = k ∧ x 1 = g (k 0) := by
  set a : ℕ → ℝ := fun t => f (k t) - k t * deriv f (k t) with ha
  set b : ℕ → ℝ := fun t => deriv f (k t) with hb
  have hcons : ∀ t, consPath a b k t = f (k t) - k (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have hfeas : IndivFeasible a b (k 0) k := ⟨rfl, fun t => ⟨hk t, (hcons t).symm ▸ hc t⟩⟩
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b k t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b k t) := fun t =>
    mul_nonneg (hf' t) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b k t) =
      β * b (t + 1) * deriv U (consPath a b k (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b k T) * k T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
    ring
  have hv' : HasSum (fun t => β ^ t * U (consPath a b k t)) v := by
    simpa only [hcons] using hv
  refine ⟨hcons, euler_tvc_isGreatest hU.concaveOn hβ.le hUd' hp heul' htvc' hfeas hv',
    fun x S hx hS hge => ?_⟩
  have hxk := euler_tvc_unique hU hβ hUd' (fun t => (hfeas.2 t).2) hp heul' htvc' hx hS hv' hge
  exact ⟨hxk, by rw [hxk, hg 0]⟩

/-! ### Capital-income tax with rebate: the pseudo-economy -/

/-- **Budget with rebate** (p. 545): wages `f(k) − k f′(k)`, after-tax capital income
`(1 − θ) x f′(k)` and the lump-sum rebate `θ k f′(k)` add up to
`f(k) + (1 − θ)(x − k) f′(k)`. -/
theorem budget_rebate (θ fk f'k x k : ℝ) :
    (fk - k * f'k) + (1 - θ) * x * f'k + θ * k * f'k = fk + (1 - θ) * (x - k) * f'k := by
  ring

/-- **Pseudo-economy** (p. 546). If `w′`, `ĥ` satisfy §18.1 (9)–(10),
`U′[f(k) − ĥ(k)] = β̂ w′[ĥ(k)]` and `w′(k) = f′(k) U′[f(k) − ĥ(k)]` with `β̂ = (1 − θ)β`, then
`φ = (1 − θ) w′` and `h = ĥ` satisfy §18.1 (6)–(7):
`U′[f(k) − h(k)] = β φ[h(k)]` and `φ(k) = (1 − θ) f′(k) U′[f(k) − h(k)]`. -/
theorem pseudo_economy_solves_6_7 {U' f f' w' hhat : ℝ → ℝ} {β θ : ℝ}
    (h9 : ∀ k, U' (f k - hhat k) = (1 - θ) * β * w' (hhat k))
    (h10 : ∀ k, w' k = f' k * U' (f k - hhat k)) :
    (∀ k, U' (f k - hhat k) = β * ((1 - θ) * w' (hhat k))) ∧
      ∀ k, (1 - θ) * w' k = (1 - θ) * f' k * U' (f k - hhat k) := by
  refine ⟨fun k => by rw [h9]; ring, fun k => by rw [h10]; ring⟩

/-- **The indirect method gives an equilibrium** (p. 546, with NOTE 18.1-C). Let the path `k`
(nonnegative capital and consumption, `f′(k_t) ≥ 0`) satisfy the Euler equation of the
pseudo-economy with discount factor `β̂ = (1 − θ)β`,
`U′[f(k_t) − k_{t+1}] = β̂ U′[f(k_{t+1}) − k_{t+2}] f′(k_{t+1})`, and the *individual's*
transversality condition `β^t (1 − θ) f′(k_t) U′[f(k_t) − k_{t+1}] k_t → 0`. Then for an
individual of the taxed economy (3) facing the aggregate path `k`, with `x_0 = k_0`, the path
`x = k` is the unique optimum (so `H(k, k; ĥ) = ĥ(k)`), with value `v`. -/
theorem indirect_equilibrium {U f : ℝ → ℝ} {β θ v : ℝ} {k : ℕ → ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β) (hθ : θ < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hk : ∀ t, 0 ≤ k t) (hc : ∀ t, 0 ≤ f (k t) - k (t + 1)) (hf' : ∀ t, 0 ≤ deriv f (k t))
    (heul : ∀ t, deriv U (f (k t) - k (t + 1)) =
      (1 - θ) * β * deriv U (f (k (t + 1)) - k (t + 2)) * deriv f (k (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (k t)) *
      deriv U (f (k t) - k (t + 1)) * k t) atTop (𝓝 0))
    (hv : HasSum (fun t => β ^ t * U (f (k t) - k (t + 1))) v) :
    IsGreatest (indivValues U β (fun t => f (k t) - (1 - θ) * k t * deriv f (k t))
        (fun t => (1 - θ) * deriv f (k t)) (k 0)) v ∧
      ∀ x S, IndivFeasible (fun t => f (k t) - (1 - θ) * k t * deriv f (k t))
          (fun t => (1 - θ) * deriv f (k t)) (k 0) x →
        HasSum (fun t => β ^ t * U (consPath (fun t => f (k t) - (1 - θ) * k t * deriv f (k t))
          (fun t => (1 - θ) * deriv f (k t)) x t)) S → v ≤ S → x = k := by
  set a : ℕ → ℝ := fun t => f (k t) - (1 - θ) * k t * deriv f (k t) with ha
  set b : ℕ → ℝ := fun t => (1 - θ) * deriv f (k t) with hb
  have hcons : ∀ t, consPath a b k t = f (k t) - k (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have hfeas : IndivFeasible a b (k 0) k := ⟨rfl, fun t => ⟨hk t, (hcons t).symm ▸ hc t⟩⟩
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b k t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b k t) := fun t =>
    mul_nonneg (mul_nonneg (by linarith) (hf' t)) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b k t) =
      β * b (t + 1) * deriv U (consPath a b k (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b k T) * k T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
  have hv' : HasSum (fun t => β ^ t * U (consPath a b k t)) v := by
    simpa only [hcons] using hv
  exact ⟨euler_tvc_isGreatest hU.concaveOn hβ.le hUd' hp heul' htvc' hfeas hv',
    fun x S hx hS hge => euler_tvc_unique hU hβ hUd' (fun t => (hfeas.2 t).2) hp heul' htvc' hx
      hS hv' hge⟩

/-- **The individual's transversality condition implies the pseudo-planner's** (NOTE 18.1-C):
if `β^t (1 − θ) z_t → 0` with `0 ≤ θ < 1` then `((1 − θ)β)^t z_t → 0`. -/
theorem tvc_indiv_imp_pseudo {β θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {z : ℕ → ℝ}
    (h : Tendsto (fun t => β ^ t * ((1 - θ) * z t)) atTop (𝓝 0)) :
    Tendsto (fun t => ((1 - θ) * β) ^ t * z t) atTop (𝓝 0) := by
  have hpos : 0 < 1 - θ := by linarith
  have hb : ∀ t, |(1 - θ) ^ t / (1 - θ)| ≤ 1 / (1 - θ) := fun t => by
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hpos.le t) hpos.le)]
    exact div_le_div_of_nonneg_right (pow_le_one₀ hpos.le (by linarith)) hpos.le
  refine squeeze_zero_norm (a := fun t => 1 / (1 - θ) * |β ^ t * ((1 - θ) * z t)|)
    (fun t => ?_) ?_
  · have e : ((1 - θ) * β) ^ t * z t = (1 - θ) ^ t / (1 - θ) * (β ^ t * ((1 - θ) * z t)) := by
      rw [mul_pow]
      field_simp
    rw [e, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
  · simpa using (h.abs).const_mul (1 / (1 - θ))

/-- **The converse fails** (NOTE 18.1-C): for `β ∈ (0, 1)`, `θ ∈ (0, 1)` the nonnegative
sequence `z_t = β^{−t}` has `((1 − θ)β)^t z_t → 0` but `β^t (1 − θ) z_t ↛ 0`; so the
pseudo-planner's transversality condition does not imply the individual's. -/
theorem tvc_pseudo_not_imp_indiv_counterexample {β θ : ℝ} (hβ : 0 < β) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ z : ℕ → ℝ, (∀ t, 0 ≤ z t) ∧ Tendsto (fun t => ((1 - θ) * β) ^ t * z t) atTop (𝓝 0) ∧
      ¬ Tendsto (fun t => β ^ t * ((1 - θ) * z t)) atTop (𝓝 0) := by
  refine ⟨fun t => (β ^ t)⁻¹, fun t => inv_nonneg.2 (pow_nonneg hβ.le t), ?_, ?_⟩
  · have e : (fun t : ℕ => ((1 - θ) * β) ^ t * (β ^ t)⁻¹) = fun t => (1 - θ) ^ t := by
      funext t
      rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero t hβ.ne'), mul_one]
    rw [e]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  · have e : (fun t : ℕ => β ^ t * ((1 - θ) * (β ^ t)⁻¹)) = fun _ => 1 - θ := by
      funext t
      field_simp
    rw [e]
    intro h
    have := tendsto_nhds_unique h tendsto_const_nhds
    linarith

/-! ### Exercise 18.2 -/

/-- **Exercise 18.2, budget** (manual p. 285). Wages taxed at `α`, capital income taxed at
`α + θ` (additive reading), rebate `θ k f′(k)`:
`(1 − α)[f(k) − k f′(k)] + (1 − α − θ) x f′(k) + θ k f′(k)
  = (1 − α) f(k) + (1 − α − θ)(x − k) f′(k)`. -/
theorem ex_18_2_budget (α θ fk f'k x k : ℝ) :
    (1 - α) * (fk - k * f'k) + (1 - α - θ) * x * f'k + θ * k * f'k =
      (1 - α) * fk + (1 - α - θ) * (x - k) * f'k := by
  ring

/-- **Exercise 18.2, first-order conditions.** Let `α < 1` and let `w′`, `ĥ` satisfy (9)–(10)
for the pseudo-economy with production function `F = (1 − α) f` and discount factor
`β̂ = β(1 − α − θ)/(1 − α)`. Then `h = ĥ` and `φ = [(1 − α − θ)/(1 − α)] w′` satisfy the
equilibrium conditions `U′[(1 − α) f(k) − h(k)] = β φ(h(k))` and
`φ(k) = (1 − α − θ) f′(k) U′[(1 − α) f(k) − h(k)]`. -/
theorem ex_18_2_foc {U' f f' w' hhat : ℝ → ℝ} {α β θ : ℝ} (hα : α < 1)
    (h9 : ∀ k, U' ((1 - α) * f k - hhat k) = β * (1 - α - θ) / (1 - α) * w' (hhat k))
    (h10 : ∀ k, w' k = (1 - α) * f' k * U' ((1 - α) * f k - hhat k)) :
    (∀ k, U' ((1 - α) * f k - hhat k) = β * ((1 - α - θ) / (1 - α) * w' (hhat k))) ∧
      ∀ k, (1 - α - θ) / (1 - α) * w' k = (1 - α - θ) * f' k * U' ((1 - α) * f k - hhat k) := by
  have hne : (1 - α) ≠ 0 := by linarith
  refine ⟨fun k => by rw [h9]; ring, fun k => ?_⟩
  rw [h10]
  field_simp

/-- **Exercise 18.2** (p. 547). Let `α < 1`, `α + θ ≤ 1`, and let the path `k` (nonnegative
capital and consumption, `f′(k_t) ≥ 0`) satisfy the Euler equation of the untaxed economy with
production function `F = (1 − α) f` and discount factor `β̂ = β(1 − α − θ)/(1 − α)`,
`U′[F(k_t) − k_{t+1}] = β̂ U′[F(k_{t+1}) − k_{t+2}] F′(k_{t+1})`, and the individual's
transversality condition. Then for an individual of the doubly taxed economy facing `k`, with
`x_0 = k_0`, the path `x = k` is the unique optimum, with value `v`. -/
theorem ex_18_2 {U f : ℝ → ℝ} {α β θ v : ℝ} {k : ℕ → ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ : 0 < β) (hα : α < 1) (hαθ : α + θ ≤ 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hk : ∀ t, 0 ≤ k t) (hc : ∀ t, 0 ≤ (1 - α) * f (k t) - k (t + 1))
    (hf' : ∀ t, 0 ≤ deriv f (k t))
    (heul : ∀ t, deriv U ((1 - α) * f (k t) - k (t + 1)) =
      β * (1 - α - θ) / (1 - α) * deriv U ((1 - α) * f (k (t + 1)) - k (t + 2)) *
        deriv (fun y => (1 - α) * f y) (k (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * ((1 - α - θ) * deriv f (k t)) *
      deriv U ((1 - α) * f (k t) - k (t + 1)) * k t) atTop (𝓝 0))
    (hv : HasSum (fun t => β ^ t * U ((1 - α) * f (k t) - k (t + 1))) v) :
    IsGreatest (indivValues U β (fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t))
        (fun t => (1 - α - θ) * deriv f (k t)) (k 0)) v ∧
      ∀ x S, IndivFeasible (fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t))
          (fun t => (1 - α - θ) * deriv f (k t)) (k 0) x →
        HasSum (fun t => β ^ t * U (consPath
          (fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t))
          (fun t => (1 - α - θ) * deriv f (k t)) x t)) S → v ≤ S → x = k := by
  set a : ℕ → ℝ := fun t => (1 - α) * f (k t) - (1 - α - θ) * k t * deriv f (k t) with ha
  set b : ℕ → ℝ := fun t => (1 - α - θ) * deriv f (k t) with hb
  have hne : (1 - α) ≠ 0 := by linarith
  have hcons : ∀ t, consPath a b k t = (1 - α) * f (k t) - k (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have hfeas : IndivFeasible a b (k 0) k := ⟨rfl, fun t => ⟨hk t, (hcons t).symm ▸ hc t⟩⟩
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b k t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b k t) := fun t =>
    mul_nonneg (mul_nonneg (by linarith) (hf' t)) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b k t) =
      β * b (t + 1) * deriv U (consPath a b k (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb, deriv_const_mul_field']
    field_simp
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b k T) * k T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
  have hv' : HasSum (fun t => β ^ t * U (consPath a b k t)) v := by
    simpa only [hcons] using hv
  exact ⟨euler_tvc_isGreatest hU.concaveOn hβ.le hUd' hp heul' htvc' hfeas hv',
    fun x S hx hS hge => euler_tvc_unique hU hβ hUd' (fun t => (hfeas.2 t).2) hp heul' htvc' hx
      hS hv' hge⟩

/-- **The manual's `β̂` is wrong** (NOTE 18.1-D). With the manual's value
`β̂ₘ = (1 − α − θ)/(1 − α)` in (9), the equilibrium condition `U′ = β φ(h)` with
`φ = [(1 − α − θ)/(1 − α)] w′` fails whenever `β < 1`, `α + θ < 1` and `w′(ĥ(k)) > 0`. -/
theorem ex_18_2_manual_counterexample {α β θ U'c w'h : ℝ} (hβ : β < 1) (hα : α < 1)
    (hαθ : α + θ < 1) (hw : 0 < w'h) (h9 : U'c = (1 - α - θ) / (1 - α) * w'h) :
    U'c ≠ β * ((1 - α - θ) / (1 - α) * w'h) := by
  have hc : 0 < (1 - α - θ) / (1 - α) := div_pos (by linarith) (by linarith)
  rw [h9]
  intro h
  have h1 : (1 - β) * ((1 - α - θ) / (1 - α) * w'h) = 0 := by linarith
  rcases mul_eq_zero.1 h1 with h2 | h2
  · linarith
  · exact (mul_pos hc hw).ne' h2

/-- **Exercise 18.2 needs `α + θ < 1`** (NOTE 18.1-E (i)): if `β > 0`, `α < 1` and
`α + θ ≥ 1`, then `β̂ = β(1 − α − θ)/(1 − α) ≤ 0`, not a discount factor. -/
theorem ex_18_2_requires_sum_lt_one {α β θ : ℝ} (hβ : 0 < β) (hα : α < 1) (hαθ : 1 ≤ α + θ) :
    β * (1 - α - θ) / (1 - α) ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
    (by linarith)

/-- **Sequential reading, budget** (NOTE 18.1-E (ii)): if the `θ`-tax is levied on capital
income net of the `α`-tax and its proceeds `θ(1 − α) k f′(k)` are rebated, the budget is
`(1 − α) f(k) + (1 − α)(1 − θ)(x − k) f′(k)`. -/
theorem ex_18_2_sequential_budget (α θ fk f'k x k : ℝ) :
    (1 - α) * (fk - k * f'k) + (1 - θ) * ((1 - α) * x * f'k) + θ * (1 - α) * k * f'k =
      (1 - α) * fk + (1 - α) * (1 - θ) * (x - k) * f'k := by
  ring

/-- **Sequential reading, Euler equation.** With after-tax return `(1 − α)(1 − θ) f′`, the
individual's Euler equation `U′(c_t) = β (1 − α)(1 − θ) f′(k_{t+1}) U′(c_{t+1})` is that of the
pseudo-economy with production function `F = (1 − α) f` and discount factor `β(1 − θ)`. -/
theorem ex_18_2_sequential_euler {α β θ U't U't1 f'k1 : ℝ} :
    U't = β * ((1 - α) * (1 - θ) * f'k1) * U't1 ↔
      U't = β * (1 - θ) * U't1 * ((1 - α) * f'k1) := by
  constructor <;> intro h <;> rw [h] <;> ring

/-- **The two readings differ** (NOTE 18.1-E (ii)): for `β > 0`, `0 < α < 1`, `θ > 0`,
`β(1 − θ) ≠ β(1 − α − θ)/(1 − α)`. -/
theorem ex_18_2_sequential_ne {α β θ : ℝ} (hβ : 0 < β) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : 0 < θ) : β * (1 - θ) ≠ β * (1 - α - θ) / (1 - α) := by
  have hne : (1 - α) ≠ 0 := by linarith
  intro h
  field_simp at h
  nlinarith [mul_pos hβ (mul_pos hα0 hθ)]

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The individual's functional equation and Exercise 18.1 stated literally

SLP §18.1, pp. 544–546, the bounded case. The individual with own capital `x`, facing
aggregate capital `k` that moves by `k′ = g(k)`, solves the functional equation
`W(x, k) = sup_{y ∈ Γ(x, k)} {U[A(k) + B(k) x − y] + β W(y, g(k))}`
(`SolvesBellman`) with `Γ(x, k) = {y : y ≥ 0, A(k) + B(k) x − y ≥ 0}` (`feasY`). The book's (2)
is `A(k) = f(k) − k f′(k)`, `B(k) = f′(k)`; its (3) (tax `θ`, rebate) is
`A(k) = f(k) − (1 − θ) k f′(k)`, `B(k) = (1 − θ) f′(k)`.

* `bellman_isLUB` (the dynamic-programming step, cf. Theorems 4.2–4.3): if `U` is bounded on
  `[0, ∞)` and `W` is a bounded solution of the functional equation, then `W(x₀, k₀)` is the
  supremum of the sequence-problem values `∑ β^t U(c_t)` over feasible paths from `x₀` with prices
  from `k_t = g^t(k₀)`. In particular the bounded solution is unique.
* `policyValue_hasSum`: a bounded `v` with `v(k) = U[F(k) − g(k)] + β v(g(k))` (the planner's
  value under its optimal policy `g`, from (1)) is the value of the path `k_{t+1} = g(k_t)`.
* `euler_tvc_gap`: the quantitative form of `euler_tvc_strict`.
* `dp_diagonal`: if the path `k_{t+1} = g(k_t)` from every `k ∈ K` satisfies the individual's
  Euler equation and transversality condition, then for the bounded solution `W`:
  `W(k, k) = v(k)`, and `g(k)` is the **unique** maximiser in the functional equation at `(k, k)`.
* **Exercise 18.1, literally** (`ex_18_1_dp`): `V(k, k; g) = v(k)` and `G(k, k; g) = g(k)` for the
  bounded solution `V` of (2).
* **The taxed economy, literally** (`indirect_equilibrium_dp`, p. 546): for the bounded solution
  `W` of (3) with `h = ĥ` the pseudo-planner's policy, `H(k, k; ĥ) = ĥ(k)` (the definition of a
  recursive competitive equilibrium, p. 545).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- The constraint set `Γ(x, k) = {y : y ≥ 0, A(k) + B(k) x − y ≥ 0}`. -/
def feasY (A B : ℝ → ℝ) (x k : ℝ) : Set ℝ := {y | 0 ≤ y ∧ 0 ≤ A k + B k * x - y}

/-- `W` solves the individual's functional equation on `[0, ∞) × K`:
`W(x, k) = sup_{y ∈ Γ(x, k)} {U[A(k) + B(k) x − y] + β W(y, g(k))}`. -/
def SolvesBellman (U A B g : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (β : ℝ) (K : Set ℝ) : Prop :=
  ∀ x, 0 ≤ x → ∀ k ∈ K,
    W x k = sSup ((fun y => U (A k + B k * x - y) + β * W y (g k)) '' feasY A B x k)

/-- A path defined by a selection: `x_0 = x₀`, `x_{t+1} = sel(x_t, g^t(k₀))`. -/
noncomputable def selPath (sel : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x₀ k₀ : ℝ) (t : ℕ) : ℝ :=
  Nat.rec (motive := fun _ => ℝ) x₀ (fun t xt => sel xt (g^[t] k₀)) t

/-- `g^t(k₀) ∈ K` when `K` is invariant. -/
theorem iterate_mem {g : ℝ → ℝ} {K : Set ℝ} (hK : ∀ k ∈ K, g k ∈ K) {k₀ : ℝ} (hk₀ : k₀ ∈ K) :
    ∀ t : ℕ, g^[t] k₀ ∈ K := by
  intro t
  induction t with
  | zero => exact hk₀
  | succ t ih => rw [Function.iterate_succ_apply']; exact hK _ ih

/-- **The bounded solution of the functional equation is the sequence-problem value.** Let
`0 ≤ β < 1`, `|U| ≤ B₀` on `[0, ∞)`, `K` invariant under `g`, `A, B ≥ 0` on `K`, and let `W`,
with `|W| ≤ M` on `[0, ∞) × K`, solve the functional equation. Then for `x₀ ≥ 0`, `k₀ ∈ K`,
`W(x₀, k₀)` is the least upper bound of the values `∑ β^t U(c_t)` of the feasible paths from
`x₀` with prices from `k_t = g^t(k₀)`. -/
theorem bellman_isLUB {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hsol : SolvesBellman U A B g W β K)
    {x₀ k₀ : ℝ} (hx₀ : 0 ≤ x₀) (hk₀ : k₀ ∈ K) :
    IsLUB (indivValues U β (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) x₀) (W x₀ k₀) := by
  have hkt := iterate_mem hK hk₀
  have hgk : ∀ t : ℕ, g^[t + 1] k₀ = g (g^[t] k₀) := fun t => Function.iterate_succ_apply' _ _ _
  have hne : ∀ x, 0 ≤ x → ∀ k ∈ K, (0 : ℝ) ∈ feasY A B x k := fun x hx k hk =>
    ⟨le_rfl, by have := mul_nonneg (hB k hk) hx; linarith [hA k hk]⟩
  have hbdd : ∀ x, 0 ≤ x → ∀ k ∈ K, BddAbove
      ((fun y => U (A k + B k * x - y) + β * W y (g k)) '' feasY A B x k) := by
    intro x hx k hk
    refine ⟨B₀ + β * M, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := (abs_le.1 (hU _ hy.2)).2
    have h2 := (abs_le.1 (hW y hy.1 _ (hK k hk))).2
    have := mul_le_mul_of_nonneg_left h2 hβ0
    simp only
    linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  constructor
  · -- every value is at most `W(x₀, k₀)`
    rintro S ⟨x, hx, hS⟩
    have key : ∀ T, ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) x t) + β ^ T * W (x T) (g^[T] k₀) ≤ W x₀ k₀ := by
      intro T
      induction T with
      | zero => simp [hx.1]
      | succ T ih =>
        rw [sum_range_succ]
        have hstep : U (consPath (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) x T) +
            β * W (x (T + 1)) (g^[T + 1] k₀) ≤ W (x T) (g^[T] k₀) := by
          rw [hsol _ (hx.2 T).1 _ (hkt T), hgk T]
          exact le_csSup (hbdd _ (hx.2 T).1 _ (hkt T))
            ⟨x (T + 1), ⟨(hx.2 (T + 1)).1, (hx.2 T).2⟩, rfl⟩
        have := mul_le_mul_of_nonneg_left hstep (pow_nonneg hβ0 T)
        rw [pow_succ]
        nlinarith
    have hle : ∀ T, ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) x t) ≤ W x₀ k₀ + β ^ T * M := by
      intro T
      have h1 := key T
      have h2 := (abs_le.1 (hW _ (hx.2 T).1 _ (hkt T))).1
      have := mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ0 T)
      linarith
    have hlim : Tendsto (fun T : ℕ => W x₀ k₀ + β ^ T * M) atTop (𝓝 (W x₀ k₀)) := by
      simpa using (hpow.mul_const M).const_add (W x₀ k₀)
    exact le_of_tendsto_of_tendsto' hS.tendsto_sum_nat hlim hle
  · -- `W(x₀, k₀)` is the least upper bound
    intro b hb
    by_contra hlt
    push Not at hlt
    set η := W x₀ k₀ - b with hη
    have hηp : 0 < η := by linarith
    set δ := η * (1 - β) / 2 with hδ
    have hδp : 0 < δ := by have : 0 < 1 - β := by linarith
                           positivity
    have hsel : ∀ x k, ∃ y, 0 ≤ x → k ∈ K → y ∈ feasY A B x k ∧
        W x k - δ < U (A k + B k * x - y) + β * W y (g k) := by
      intro x k
      by_cases h : 0 ≤ x ∧ k ∈ K
      · have hlt' : W x k - δ < sSup ((fun y => U (A k + B k * x - y) + β * W y (g k)) ''
            feasY A B x k) := by
          rw [← hsol x h.1 k h.2]
          linarith
        obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ :=
          exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨0, hne x h.1 k h.2⟩) hlt'
        exact ⟨y, fun _ _ => ⟨hy, hy'⟩⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose sel hsel using hsel
    set xp := selPath sel g x₀ k₀ with hxp
    have hxp0 : xp 0 = x₀ := rfl
    have hxps : ∀ t, xp (t + 1) = sel (xp t) (g^[t] k₀) := fun t => rfl
    have hnn : ∀ t, 0 ≤ xp t := by
      intro t
      induction t with
      | zero => exact hx₀
      | succ t ih => rw [hxps]; exact ((hsel _ _ ih (hkt t)).1).1
    have hfeas : IndivFeasible (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) x₀ xp := by
      refine ⟨hxp0, fun t => ⟨hnn t, ?_⟩⟩
      have := ((hsel _ _ (hnn t) (hkt t)).1).2
      simp only [consPath]
      rw [hxps]
      exact this
    have hcons : ∀ t, consPath (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) xp t =
        A (g^[t] k₀) + B (g^[t] k₀) * xp t - sel (xp t) (g^[t] k₀) := fun t => by
      simp only [consPath, hxps]
    have hsum : Summable fun t => β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) xp t) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
        fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (hU _ (hfeas.2 t).2) (pow_nonneg hβ0 t)
    have hval := hb ⟨xp, hfeas, hsum.hasSum⟩
    have key : ∀ T, W x₀ k₀ ≤ ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) xp t) + β ^ T * W (xp T) (g^[T] k₀) +
          δ * ∑ t ∈ range T, β ^ t := by
      intro T
      induction T with
      | zero => simp [hxp0]
      | succ T ih =>
        rw [sum_range_succ, sum_range_succ, hcons T, ← hxps T]
        have hstep := ((hsel _ _ (hnn T) (hkt T)).2)
        rw [← hxps, ← hgk T] at hstep
        have := mul_le_mul_of_nonneg_left hstep.le (pow_nonneg hβ0 T)
        rw [pow_succ]
        linarith
    have hgeo : ∀ T, ∑ t ∈ range T, β ^ t ≤ (1 - β)⁻¹ := fun T => by
      rw [← tsum_geometric_of_lt_one hβ0 hβ1]
      exact (summable_geometric_of_lt_one hβ0 hβ1).sum_le_tsum _
        (fun i _ => pow_nonneg hβ0 i)
    have hle : ∀ T, W x₀ k₀ - δ * (1 - β)⁻¹ - β ^ T * M ≤
        ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
          (fun t => B (g^[t] k₀)) xp t) := by
      intro T
      have h1 := key T
      have h2 := (abs_le.1 (hW _ (hnn T) _ (hkt T))).2
      have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ0 T)
      have h4 := mul_le_mul_of_nonneg_left (hgeo T) hδp.le
      linarith
    have hlim : Tendsto (fun T : ℕ => W x₀ k₀ - δ * (1 - β)⁻¹ - β ^ T * M) atTop
        (𝓝 (W x₀ k₀ - δ * (1 - β)⁻¹)) := by
      simpa using (hpow.mul_const M).const_sub (W x₀ k₀ - δ * (1 - β)⁻¹)
    have hS := le_of_tendsto_of_tendsto' hlim hsum.hasSum.tendsto_sum_nat hle
    have e : δ * (1 - β)⁻¹ = η / 2 := by
      rw [hδ]
      have : (1 - β) ≠ 0 := by linarith
      field_simp
    linarith

/-- **Uniqueness of the bounded solution** of the functional equation (the book's "the unique
solution of (2)"): two bounded solutions agree on `[0, ∞) × K`. -/
theorem bellman_unique {U A B g : ℝ → ℝ} {W W' : ℝ → ℝ → ℝ} {β B₀ M M' : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hW' : ∀ x, 0 ≤ x → ∀ k ∈ K, |W' x k| ≤ M')
    (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k)
    (hsol : SolvesBellman U A B g W β K) (hsol' : SolvesBellman U A B g W' β K) :
    ∀ x, 0 ≤ x → ∀ k ∈ K, W x k = W' x k := fun _ hx _ hk =>
  (bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hx hk).unique
    (bellman_isLUB hβ0 hβ1 hU hW' hK hA hB hsol' hx hk)

/-- **The value of the policy `g`.** If `0 ≤ β < 1`, `K` is invariant under `g`, `v` is bounded on
`K` and `v(k) = U[F(k) − g(k)] + β v(g(k))` on `K` (the planner's functional equation (1) at its
optimal policy), then `v(k₀) = ∑ β^t U[F(k_t) − k_{t+1}]` along `k_t = g^t(k₀)`, provided the terms
are bounded. -/
theorem policyValue_hasSum {U Fk g v : ℝ → ℝ} {β Mv B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hK : ∀ k ∈ K, g k ∈ K) (hv : ∀ k ∈ K, |v k| ≤ Mv)
    (hU : ∀ k ∈ K, |U (Fk k - g k)| ≤ B₀)
    (hpol : ∀ k ∈ K, v k = U (Fk k - g k) + β * v (g k)) {k₀ : ℝ} (hk₀ : k₀ ∈ K) :
    HasSum (fun t => β ^ t * U (Fk (g^[t] k₀) - g (g^[t] k₀))) (v k₀) := by
  have hkt := iterate_mem hK hk₀
  have hsum : Summable fun t => β ^ t * U (Fk (g^[t] k₀) - g (g^[t] k₀)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hU _ (hkt t)) (pow_nonneg hβ0 t)
  refine hsum.hasSum_iff_tendsto_nat.2 ?_
  have key : ∀ T, v k₀ = ∑ t ∈ range T, β ^ t * U (Fk (g^[t] k₀) - g (g^[t] k₀)) +
      β ^ T * v (g^[T] k₀) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_range_succ, Function.iterate_succ_apply', ih, hpol _ (hkt T), pow_succ]
      ring
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  have hrem : Tendsto (fun T : ℕ => β ^ T * v (g^[T] k₀)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun T => ?_) (by simpa using hpow.mul_const Mv)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hv _ (hkt T)) (pow_nonneg hβ0 T)
  have h := (tendsto_const_nhds (x := v k₀)).sub hrem
  rw [sub_zero] at h
  refine h.congr fun T => ?_
  rw [key T]
  ring

/-- **Quantitative strict optimality.** Under the hypotheses of `euler_tvc_optimal`, every
feasible path `x` from `xs_0` has value at most
`S′ − β^{t₀}(U(c*_{t₀}) + U′(c*_{t₀})(c_{t₀} − c*_{t₀}) − U(c_{t₀}))`, for any date `t₀`. -/
theorem euler_tvc_gap {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') (t₀ : ℕ) :
    S ≤ S' - β ^ t₀ * (U (consPath a b xs t₀) + deriv U (consPath a b xs t₀) *
      (consPath a b x t₀ - consPath a b xs t₀) - U (consPath a b x t₀)) := by
  set r : ℕ → ℝ := fun t => β ^ t * (U (consPath a b xs t) + deriv U (consPath a b xs t) *
    (consPath a b x t - consPath a b xs t) - U (consPath a b x t)) with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => by
    have h := concave_le_tangent hU (hx.2 t).2 (hxs t) (hUd t)
    exact mul_nonneg (pow_nonneg hβ t) (by linarith)
  have key : ∀ T, t₀ < T → ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * xs T - r t₀ := by
    intro T hT
    have htel := euler_telescope U β a b xs x heul hx.1 T
    have hsum : ∑ t ∈ range T, β ^ t * U (consPath a b x t) =
        ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
          ∑ t ∈ range T, β ^ t * (deriv U (consPath a b xs t) *
            (consPath a b x t - consPath a b xs t)) - ∑ t ∈ range T, r t := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      simp only [hr]
      ring
    have hle : r t₀ ≤ ∑ t ∈ range T, r t :=
      single_le_sum (fun t _ => hr0 t) (mem_range.2 hT)
    have h1 : 0 ≤ β ^ T * (b T * deriv U (consPath a b xs T)) :=
      mul_nonneg (pow_nonneg hβ T) (hp T)
    have h2 := (hx.2 T).1
    rw [hsum, htel]
    nlinarith
  have hlim := (hS'.tendsto_sum_nat.add htvc).sub_const (r t₀)
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto hS.tendsto_sum_nat hlim
    (eventually_atTop.2 ⟨t₀ + 1, fun T hT => key T (by omega)⟩)

/-- **The diagonal of the functional equation.** Let `U` be strictly concave on `[0, ∞)`,
differentiable with `U′ ≥ 0` there, `|U| ≤ B₀` on `[0, ∞)`, `0 < β < 1`, `K ⊆ [0, ∞)` invariant
under `g`, and on `K`: `A, B ≥ 0`, `A(k) + B(k) k = F(k)`, `F(k) − g(k) ≥ 0`, and the Euler
equation `U′[F(k) − g(k)] = β B(g(k)) U′[F(g(k)) − g(g(k))]`; let the transversality condition
`β^t B(k_t) U′(c_t) k_t → 0` hold along `k_t = g^t(k)` for every `k ∈ K`. Let `v` be bounded on
`K` with `v(k) = U[F(k) − g(k)] + β v(g(k))`, and `W` a bounded solution of the functional
equation. Then for every `k ∈ K`: `W(k, k) = v(k)`; `g(k) ∈ Γ(k, k)` attains the supremum at
`(k, k)`; and it is the only `y ∈ Γ(k, k)` that does. -/
theorem dp_diagonal {U A B Fk g v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hAB : ∀ k ∈ K, A k + B k * k = Fk k)
    (hc : ∀ k ∈ K, 0 ≤ Fk k - g k)
    (heul : ∀ k ∈ K, deriv U (Fk k - g k) =
      β * B (g k) * deriv U (Fk (g k) - g (g k)))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * B (g^[t] k) *
      deriv U (Fk (g^[t] k) - g (g^[t] k)) * g^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (Fk k - g k) + β * v (g k))
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hsol : SolvesBellman U A B g W β K) :
    ∀ k ∈ K, W k k = v k ∧ g k ∈ feasY A B k k ∧
      U (A k + B k * k - g k) + β * W (g k) (g k) = W k k ∧
      ∀ y ∈ feasY A B k k, U (A k + B k * k - y) + β * W y (g k) = W k k → y = g k := by
  -- the diagonal value
  have hdiag : ∀ k ∈ K, W k k = v k ∧
      IsGreatest (indivValues U β (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k) (v k) ∧
      ∀ x S, IndivFeasible (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k x →
        HasSum (fun t => β ^ t * U (consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k))
          x t)) S → ∀ t₀ : ℕ, S ≤ v k - β ^ t₀ * (U (Fk (g^[t₀] k) - g (g^[t₀] k)) +
            deriv U (Fk (g^[t₀] k) - g (g^[t₀] k)) * (consPath (fun t => A (g^[t] k))
              (fun t => B (g^[t] k)) x t₀ - (Fk (g^[t₀] k) - g (g^[t₀] k))) -
            U (consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x t₀)) := by
    intro k hk
    have hkt := iterate_mem hK hk
    set a : ℕ → ℝ := fun t => A (g^[t] k) with ha
    set b : ℕ → ℝ := fun t => B (g^[t] k) with hb
    set xs : ℕ → ℝ := fun t => g^[t] k with hxs
    have hcons : ∀ t, consPath a b xs t = Fk (g^[t] k) - g (g^[t] k) := fun t => by
      simp only [consPath, ha, hb, hxs, Function.iterate_succ_apply']
      rw [← hAB _ (hkt t)]
    have hcs : ∀ t, 0 ≤ consPath a b xs t := fun t => (hcons t).symm ▸ hc _ (hkt t)
    have hfeas : IndivFeasible a b (xs 0) xs := ⟨rfl, fun t => ⟨hK0 _ (hkt t), hcs t⟩⟩
    have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b xs t) := fun t => hUd _ (hcs t)
    have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t) := fun t =>
      mul_nonneg (hB _ (hkt t)) (hU' _ (hcs t))
    have heul' : ∀ t, deriv U (consPath a b xs t) =
        β * b (t + 1) * deriv U (consPath a b xs (t + 1)) := fun t => by
      rw [hcons, hcons, heul _ (hkt t)]
      simp only [hb, Function.iterate_succ_apply']
    have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop
        (𝓝 0) := by
      refine (htvc k hk).congr fun t => ?_
      rw [hcons]
    have hv' : HasSum (fun t => β ^ t * U (consPath a b xs t)) (v k) := by
      have := policyValue_hasSum hβ0.le hβ1 hK hv (fun k hk => hUb _ (hc k hk)) hpol hk
      simpa only [hcons] using this
    have hG := euler_tvc_isGreatest hU.concaveOn hβ0.le hUd' hp heul' htvc' hfeas hv'
    have hL := bellman_isLUB hβ0.le hβ1 hUb hW hK hA hB hsol (hK0 k hk) hk
    refine ⟨hL.unique hG.isLUB, hG, fun x S hx hS t₀ => ?_⟩
    have := euler_tvc_gap hU.concaveOn hβ0.le hUd' hcs hp heul' htvc' hx hS hv' t₀
    rwa [hcons t₀] at this
  intro k hk
  obtain ⟨hWk, -, hgap⟩ := hdiag k hk
  have hgk := hK k hk
  have hAk : A k + B k * k - g k = Fk k - g k := by rw [hAB k hk]
  refine ⟨hWk, ⟨hK0 _ hgk, by rw [hAk]; exact hc k hk⟩, ?_, fun y hy hyW => ?_⟩
  · rw [hAk, (hdiag _ hgk).1, hWk, hpol k hk]
  · by_contra hne
    set cy := A k + B k * k - y with hcy
    set cs := Fk k - g k with hcs
    have hcne : cy ≠ cs := by
      intro h
      apply hne
      rw [hcy, hcs, ← hAB k hk] at h
      linarith
    set r0 := U cs + deriv U cs * (cy - cs) - U cy with hr0
    have hr0p : 0 < r0 := by
      have := strictConcave_lt_tangent hU hy.2 (hc k hk) hcne (hUd _ (hc k hk))
      rw [hr0]
      linarith
    -- every continuation from `(y, g(k))` gives at most `v(k) − r₀`
    have hub : W y (g k) ≤ (v k - r0 - U cy) / β := by
      refine (bellman_isLUB hβ0.le hβ1 hUb hW hK hA hB hsol hy.1 hgk).2 ?_
      rintro S' ⟨x', hx', hS'⟩
      rw [le_div_iff₀ hβ0]
      set x : ℕ → ℝ := fun t => Nat.casesOn t k fun t => x' t with hxdef
      have hx0 : x 0 = k := rfl
      have hxs : ∀ t, x (t + 1) = x' t := fun t => rfl
      have hit : ∀ t : ℕ, g^[t + 1] k = g^[t] (g k) := fun t => Function.iterate_succ_apply _ _ _
      have hc0 : consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x 0 = cy := by
        simp only [consPath, hx0, hxs, hx'.1, Function.iterate_zero, id, hcy]
      have hcsucc : ∀ t, consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x (t + 1) =
          consPath (fun t => A (g^[t] (g k))) (fun t => B (g^[t] (g k))) x' t := fun t => by
        simp only [consPath, hxs, hit]
      have hfeas : IndivFeasible (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k x := by
        refine ⟨hx0, fun t => ?_⟩
        rcases t with _ | t
        · exact ⟨hK0 k hk, hc0 ▸ hy.2⟩
        · rw [hcsucc t]
          exact ⟨(hx'.2 t).1, (hx'.2 t).2⟩
      have hsum : HasSum (fun t => β ^ t * U (consPath (fun t => A (g^[t] k))
          (fun t => B (g^[t] k)) x t)) (U cy + β * S') := by
        refine (hasSum_nat_add_iff' 1).1 ?_
        have e : (U cy + β * S') - ∑ i ∈ range 1, β ^ i * U (consPath (fun t => A (g^[t] k))
            (fun t => B (g^[t] k)) x i) = β * S' := by
          simp [hc0]
        rw [e]
        refine (hS'.mul_left β).congr_fun fun t => ?_
        simp only [hcsucc t, pow_succ]
        ring
      have h := hgap x _ hfeas hsum 0
      simp only [pow_zero, one_mul, Function.iterate_zero, id, hc0] at h
      linarith
    have h1 : U cy + β * W y (g k) ≤ v k - r0 := by
      have := mul_le_mul_of_nonneg_left hub hβ0.le
      rw [mul_div_cancel₀ _ hβ0.ne'] at this
      linarith
    rw [hyW, hWk] at h1
    linarith

/-- **Exercise 18.1, stated literally** (p. 544). Let `0 < β < 1`, `U` strictly concave on
`[0, ∞)`, differentiable with `U′ ≥ 0` and bounded there; let `K ⊆ [0, ∞)` be invariant under the
planner's policy `g`, with `f′(k) ≥ 0`, `f(k) − k f′(k) ≥ 0` and `f(k) − g(k) ≥ 0` on `K`; let `g`
satisfy the planner's Euler equation and transversality condition, and let the planner's value
`v` (bounded on `K`) satisfy `v(k) = U[f(k) − g(k)] + β v(g(k))` (functional equation (1) at its
policy). If `V` is a bounded solution of the individual's functional equation (2) on
`[0, ∞) × K`, then `V(k, k; g) = v(k)` for all `k ∈ K`, and `g(k)` is the unique optimal choice
`G(k, k; g)` in (2) at `(k, k)`. -/
theorem ex_18_1_dp {U f g v : ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (f k - g k) + β * v (g k))
    (hV : ∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K) :
    ∀ k ∈ K, V k k = v k ∧
      (∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
        U (f k + (k - k) * deriv f k - y) + β * V y (g k) = V k k ↔ y = g k) := by
  have hD := dp_diagonal (A := fun k => f k - k * deriv f k) (B := deriv f) (Fk := f) hU hβ0
    hβ1 hUd hU' hUb hK hK0 hw hf' (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring)
    (fun k hk => (htvc k hk).congr fun t => by ring) hv hpol hV hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (k - k) * deriv f k - y = f k - k * deriv f k + deriv f k * k - y :=
    fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyV => h4 y hy (by rw [← e]; exact hyV), fun hyg => ?_⟩⟩
  rw [hyg, e]
  exact h3

/-- **The indirect method gives a recursive competitive equilibrium** (pp. 545–546). In the
economy with capital-income tax `θ ∈ [0, 1)` rebated lump sum, let `ĥ` be the policy of the
pseudo-economy with discount factor `(1 − θ)β` (Euler equation
`U′[f(k) − ĥ(k)] = (1 − θ)β U′[f(ĥ(k)) − ĥ(ĥ(k))] f′(ĥ(k))`) satisfying the individual's
transversality condition, with `v(k) = U[f(k) − ĥ(k)] + β v(ĥ(k))` bounded (the individual's
value of following `ĥ`). If `W` is a bounded solution of the individual's functional equation (3)
with `h = ĥ`, then `W(k, k; ĥ) = v(k)` and the unique optimal choice at `(k, k)` is
`H(k, k; ĥ) = ĥ(k)`: `ĥ` is a recursive competitive equilibrium. -/
theorem indirect_equilibrium_dp {U f h v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M Mv : ℝ}
    {K : Set ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (f k - h k) + β * v (h k))
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K) :
    ∀ k ∈ K, W k k = v k ∧
      ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
        (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (h k) = W k k ↔ y = h k) := by
  have hD := dp_diagonal (A := fun k => f k - (1 - θ) * k * deriv f k)
    (B := fun k => (1 - θ) * deriv f k) (Fk := f) hU hβ0 hβ1 hUd hU' hUb hK hK0 hw
    (fun k hk => mul_nonneg (by linarith) (hf' k hk)) (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring) htvc hv hpol hW hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (1 - θ) * (k - k) * deriv f k - y =
      f k - (1 - θ) * k * deriv f k + (1 - θ) * deriv f k * k - y := fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyW => h4 y hy (by rw [← e]; exact hyW), fun hyh => ?_⟩⟩
  rw [hyh, e]
  exact h3

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of the bounded solution of (2)/(3), and the planner's problem

SLP §18.1, pp. 543–546, the bounded case.

**Existence.** The Bellman operator of the individual's functional equation,
`(Tw)(x, k) = sup_{y ∈ Γ(x, k)} {U[A(k) + B(k) x − y] + β w(y, g(k))}` (`bellOp`), acts on the
Banach space `ℓ^∞` of bounded functions on the state set `{(x, k) : x ≥ 0, k ∈ K}`
(`DPState`, `lp (fun _ => ℝ) ⊤`; no continuity is needed). Only boundedness of `U` and
nonemptiness of `Γ` are used: `T` maps `ℓ^∞` into itself (`bellOp_abs_le`) and
`|Tw − Tw′| ≤ β ‖w − w′‖` (`bellOp_sub_le`), so it is a `β`-contraction (`bellLp_contracting`)
and has a fixed point (`exists_bellman_solution`), the unique bounded solution
(`bellman_unique`).

**The planner.** If the planner's path `k_{t+1} = g(k_t)` satisfies the planner's Euler equation
and transversality condition, it is optimal in the planner's sequence problem
(`planner_optimal`): with `a_t = f(k_t) − k_t f′(k_t)`, `b_t = f′(k_t)`, concavity of `f` gives
`f(k′_t) − k′_{t+1} ≤ a_t + b_t k′_t − k′_{t+1}`, so any planner-feasible path is feasible for the
individual facing the planner's prices and does no better there, where `euler_tvc_optimal`
applies. So the planner's value is the full maximum of `∑ β^t U(f(k_t) − k_{t+1})`
(`plannerValues`).

**Exercise 18.1 and the taxed economy, with existence** (`ex_18_1_full`,
`indirect_equilibrium_full`). The bounded solution `V` of (2) exists and is unique;
`V(k, k; g) = v(k)` where `v(k)` is the maximal value of the planner's sequence problem; and
`G(k, k; g) = g(k)` is the unique optimal choice. For (3) with `h = ĥ`: the bounded solution
exists and is unique, `ĥ` is optimal in the pseudo-economy (8) with discount factor `(1 − θ)β`,
and `H(k, k; ĥ) = ĥ(k)`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- The state set `{(x, k) : x ≥ 0, k ∈ K}`. -/
abbrev DPState (K : Set ℝ) : Type := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.2 ∈ K}

/-- Extension of a function on states to `ℝ × ℝ` by `0`. -/
noncomputable def wExt {K : Set ℝ} (w : DPState K → ℝ) (x k : ℝ) : ℝ :=
  @dite _ (0 ≤ x ∧ k ∈ K) (Classical.propDecidable _) (fun h => w ⟨(x, k), h⟩) fun _ => 0

/-- `wExt w = w` on states. -/
theorem wExt_of_mem {K : Set ℝ} (w : DPState K → ℝ) {x k : ℝ} (h : 0 ≤ x ∧ k ∈ K) :
    wExt w x k = w ⟨(x, k), h⟩ := by
  simp [wExt, h.1, h.2]

/-- The Bellman operator of the individual's functional equation (2)/(3). -/
noncomputable def bellOp (U A B g : ℝ → ℝ) (β : ℝ) {K : Set ℝ} (w : DPState K → ℝ)
    (s : DPState K) : ℝ :=
  sSup ((fun y => U (A s.1.2 + B s.1.2 * s.1.1 - y) + β * wExt w y (g s.1.2)) ''
    feasY A B s.1.1 s.1.2)

/-- `T` maps bounded functions to bounded functions: `|w| ≤ M ⇒ |Tw| ≤ B₀ + βM`. -/
theorem bellOp_abs_le {U A B g : ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k)
    (hB : ∀ k ∈ K, 0 ≤ B k) {w : DPState K → ℝ} (hw : ∀ s, |w s| ≤ M) (s : DPState K) :
    |bellOp U A B g β w s| ≤ B₀ + β * M := by
  obtain ⟨⟨x, k⟩, hx, hk⟩ := s
  have h0 : (0 : ℝ) ∈ feasY A B x k :=
    ⟨le_rfl, by have := mul_nonneg (hB k hk) hx; linarith [hA k hk]⟩
  have hel : ∀ y ∈ feasY A B x k,
      |U (A k + B k * x - y) + β * wExt w y (g k)| ≤ B₀ + β * M := by
    intro y hy
    rw [wExt_of_mem w ⟨hy.1, hK k hk⟩]
    have h1 := hU _ hy.2
    have h2 := mul_le_mul_of_nonneg_left (hw ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩) hβ0
    calc _ ≤ |U (A k + B k * x - y)| + |β * w ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩| := abs_add_le _ _
      _ ≤ B₀ + β * M := by rw [abs_mul, abs_of_nonneg hβ0]; linarith
  have hne : ((fun y => U (A k + B k * x - y) + β * wExt w y (g k)) '' feasY A B x k).Nonempty :=
    ⟨_, 0, h0, rfl⟩
  have hbdd : BddAbove ((fun y => U (A k + B k * x - y) + β * wExt w y (g k)) ''
      feasY A B x k) :=
    ⟨B₀ + β * M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.1 (hel y hy)).2⟩
  rw [abs_le]
  constructor
  · exact (abs_le.1 (hel 0 h0)).1.trans (le_csSup hbdd ⟨0, h0, rfl⟩)
  · exact csSup_le hne (by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.1 (hel y hy)).2)

/-- **The `β`-contraction estimate**: `|w − w′| ≤ D ⇒ |Tw − Tw′| ≤ βD`. -/
theorem bellOp_sub_le {U A B g : ℝ → ℝ} {β B₀ M M' D : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k)
    (hB : ∀ k ∈ K, 0 ≤ B k) {w w' : DPState K → ℝ} (hw : ∀ s, |w s| ≤ M)
    (hw' : ∀ s, |w' s| ≤ M') (hD : ∀ s, |w s - w' s| ≤ D) (s : DPState K) :
    |bellOp U A B g β w s - bellOp U A B g β w' s| ≤ β * D := by
  have key : ∀ (v v' : DPState K → ℝ) (N N' : ℝ), (∀ s, |v s| ≤ N) → (∀ s, |v' s| ≤ N') →
      (∀ s, v s - v' s ≤ D) → bellOp U A B g β v s ≤ bellOp U A B g β v' s + β * D := by
    intro v v' N N' hv hv' hvD
    obtain ⟨⟨x, k⟩, hx, hk⟩ := s
    have h0 : (0 : ℝ) ∈ feasY A B x k :=
      ⟨le_rfl, by have := mul_nonneg (hB k hk) hx; linarith [hA k hk]⟩
    have hbdd' : BddAbove ((fun y => U (A k + B k * x - y) + β * wExt v' y (g k)) ''
        feasY A B x k) := by
      refine ⟨B₀ + β * N', ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      beta_reduce
      rw [wExt_of_mem v' ⟨hy.1, hK k hk⟩]
      have h1 := (abs_le.1 (hU _ hy.2)).2
      have h2 := mul_le_mul_of_nonneg_left (abs_le.1 (hv' ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩)).2 hβ0
      linarith
    refine csSup_le ⟨_, 0, h0, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hmem := le_csSup hbdd' ⟨y, hy, rfl⟩
    beta_reduce at hmem ⊢
    rw [wExt_of_mem v ⟨hy.1, hK k hk⟩]
    rw [wExt_of_mem v' ⟨hy.1, hK k hk⟩] at hmem
    have h3 := mul_le_mul_of_nonneg_left (hvD ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩) hβ0
    change U (A k + B k * x - y) + β * v ⟨(y, g k), _⟩ ≤
      sSup ((fun y => U (A k + B k * x - y) + β * wExt v' y (g k)) '' feasY A B x k) + β * D
    nlinarith
  rw [abs_le]
  constructor
  · have := key w' w M' M hw' hw (fun s => by have := abs_le.1 (hD s); linarith)
    linarith
  · have := key w w' M M' hw hw' (fun s => (abs_le.1 (hD s)).2)
    linarith

/-- The Bellman operator on `ℓ^∞(DPState K)`. -/
noncomputable def bellLp (U A B g : ℝ → ℝ) (β B₀ : ℝ) {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k)
    (hB : ∀ k ∈ K, 0 ≤ B k) (w : lp (fun _ : DPState K => ℝ) ⊤) :
    lp (fun _ : DPState K => ℝ) ⊤ :=
  ⟨bellOp U A B g β (fun s => w s), memℓp_infty ⟨B₀ + β * ‖w‖, by
    rintro _ ⟨s, rfl⟩
    exact bellOp_abs_le hβ0 hU hK hA hB
      (fun s => lp.norm_apply_le_norm ENNReal.top_ne_zero w s) s⟩⟩

/-- **The Bellman operator is a `β`-contraction** of `ℓ^∞` (sup norm). -/
theorem bellLp_contracting {U A B g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) :
    ContractingWith (Real.toNNReal β) (bellLp U A B g β B₀ hβ0 hU hK hA hB) := by
  refine ⟨Real.toNNReal_lt_one.2 hβ1, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
  rw [Real.coe_toNNReal _ hβ0, dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (mul_nonneg hβ0 (norm_nonneg _)) fun s => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  refine bellOp_sub_le hβ0 hU hK hA hB (fun s => lp.norm_apply_le_norm ENNReal.top_ne_zero w s)
    (fun s => lp.norm_apply_le_norm ENNReal.top_ne_zero w' s) (fun s => ?_) s
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero (w - w') s
  rwa [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at this

/-- **Existence of the bounded solution** of the individual's functional equation (2)/(3):
for `0 ≤ β < 1`, `U` bounded on `[0, ∞)`, `K` invariant under `g`, and `A, B ≥ 0` on `K`
(so `Γ(x, k) ∋ 0` is nonempty), there is a bounded `W` solving the functional equation on
`[0, ∞) × K`: the fixed point of the contraction `bellLp`. -/
theorem exists_bellman_solution {U A B g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U A B g W β K := by
  have hT := bellLp_contracting hβ0 hβ1 hU hK hA hB
  set w := ContractingWith.fixedPoint _ hT with hw
  have hfix : bellLp U A B g β B₀ hβ0 hU hK hA hB w = w :=
    ContractingWith.fixedPoint_isFixedPt (f := bellLp U A B g β B₀ hβ0 hU hK hA hB) hT
  refine ⟨wExt fun s => w s, ‖w‖, fun x hx k hk => ?_, fun x hx k hk => ?_⟩
  · rw [wExt_of_mem _ ⟨hx, hk⟩]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero w _
  · rw [wExt_of_mem _ ⟨hx, hk⟩]
    have := congrArg (fun v : lp (fun _ : DPState K => ℝ) ⊤ => v ⟨(x, k), ⟨hx, hk⟩⟩) hfix
    simp only at this
    rw [← this]
    rfl

/-! ### The planner's problem -/

/-- The values `∑ β^t U(f(k_t) − k_{t+1})` of the planner's feasible paths from `k₀`
(`k_t ≥ 0`, `0 ≤ k_{t+1} ≤ f(k_t)`). -/
def plannerValues (U f : ℝ → ℝ) (β k₀ : ℝ) : Set ℝ :=
  {S | ∃ k : ℕ → ℝ, k 0 = k₀ ∧ (∀ t, 0 ≤ k t ∧ 0 ≤ f (k t) - k (t + 1)) ∧
    HasSum (fun t => β ^ t * U (f (k t) - k (t + 1))) S}

/-- **Sufficiency of Euler + transversality for the planner** (Theorem 4.15 for §18.1 (1)). Let
`U` be concave, nondecreasing, differentiable with `U′ ≥ 0` and bounded on `[0, ∞)`,
`0 ≤ β < 1`, `f` concave on `[0, ∞)`, and let the path `ks` (`ks_t ≥ 0`, `f(ks_t) − ks_{t+1} ≥ 0`,
`f` differentiable at `ks_t` with `f′(ks_t) ≥ 0`) satisfy the planner's Euler equation and
transversality condition. Then its value is the greatest value of the planner's problem. -/
theorem planner_optimal {U f : ℝ → ℝ} {β B₀ : ℝ} {ks : ℕ → ℝ} (hU : ConcaveOn ℝ (Ici 0) U)
    (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ t, DifferentiableAt ℝ f (ks t)) (hf' : ∀ t, 0 ≤ deriv f (ks t))
    (hks : ∀ t, 0 ≤ ks t) (hc : ∀ t, 0 ≤ f (ks t) - ks (t + 1))
    (heul : ∀ t, deriv U (f (ks t) - ks (t + 1)) =
      β * deriv U (f (ks (t + 1)) - ks (t + 2)) * deriv f (ks (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * deriv U (f (ks t) - ks (t + 1)) * deriv f (ks t) * ks t)
      atTop (𝓝 0)) :
    IsGreatest (plannerValues U f β (ks 0)) (∑' t, β ^ t * U (f (ks t) - ks (t + 1))) := by
  have hsumb : ∀ c : ℕ → ℝ, (∀ t, 0 ≤ c t) → Summable fun t => β ^ t * U (c t) := by
    intro c hc0
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hUb _ (hc0 t)) (pow_nonneg hβ0 t)
  have hS' := (hsumb _ hc).hasSum
  refine ⟨⟨ks, rfl, fun t => ⟨hks t, hc t⟩, hS'⟩, ?_⟩
  rintro S ⟨k, hk0, hk, hS⟩
  set a : ℕ → ℝ := fun t => f (ks t) - ks t * deriv f (ks t) with ha
  set b : ℕ → ℝ := fun t => deriv f (ks t) with hb
  have hcons : ∀ t, consPath a b ks t = f (ks t) - ks (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  -- the planner's feasible path does no better in the individual's problem at the planner's prices
  have htan : ∀ t, f (k t) - k (t + 1) ≤ consPath a b k t := fun t => by
    have := concave_le_tangent hf (hk t).1 (hks t) (hfd t)
    simp only [consPath, ha, hb]
    linarith
  have hfeas : IndivFeasible a b (ks 0) k :=
    ⟨hk0, fun t => ⟨(hk t).1, ((hk t).2).trans (htan t)⟩⟩
  have hS2 := (hsumb _ fun t => (hfeas.2 t).2).hasSum
  have hle1 : S ≤ ∑' t, β ^ t * U (consPath a b k t) :=
    hasSum_le (fun t => mul_le_mul_of_nonneg_left (hUm (mem_Ici.2 (hk t).2)
      (mem_Ici.2 (hfeas.2 t).2) (htan t)) (pow_nonneg hβ0 t)) hS hS2
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b ks t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b ks t) := fun t =>
    mul_nonneg (hf' t) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b ks t) =
      β * b (t + 1) * deriv U (consPath a b ks (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b ks T) * ks T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
    ring
  have hv' : HasSum (fun t => β ^ t * U (consPath a b ks t))
      (∑' t, β ^ t * U (f (ks t) - ks (t + 1))) := by
    simpa only [hcons] using hS'
  exact hle1.trans (euler_tvc_optimal hU hβ0 hUd' (fun t => (hcons t).symm ▸ hc t) hp heul'
    htvc' hfeas hS2 hv')

/-! ### The value of following a policy -/

/-- The value `∑ β^t U[F(k_t) − k_{t+1}]` of the path `k_t = g^t(k)`. -/
noncomputable def pathValue (U Fk g : ℝ → ℝ) (β k : ℝ) : ℝ :=
  ∑' t, β ^ t * U (Fk (g^[t] k) - g (g^[t] k))

/-- `pathValue` is bounded by `B₀/(1 − β)` and satisfies the policy equation
`v(k) = U[F(k) − g(k)] + β v(g(k))` on an invariant `K` with `F − g ≥ 0`. -/
theorem pathValue_spec {U Fk g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K)
    (hc : ∀ k ∈ K, 0 ≤ Fk k - g k) :
    (∀ k ∈ K, |pathValue U Fk g β k| ≤ (1 - β)⁻¹ * B₀) ∧
      ∀ k ∈ K, pathValue U Fk g β k = U (Fk k - g k) + β * pathValue U Fk g β (g k) := by
  have hgeo := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right B₀
  have hsum : ∀ k ∈ K, Summable fun t => β ^ t * U (Fk (g^[t] k) - g (g^[t] k)) := by
    intro k hk
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hUb _ (hc _ (iterate_mem hK hk t))) (pow_nonneg hβ0 t)
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hb : ∀ t, |β ^ t * U (Fk (g^[t] k) - g (g^[t] k))| ≤ β ^ t * B₀ := fun t => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (hUb _ (hc _ (iterate_mem hK hk t))) (pow_nonneg hβ0 t)
    rw [abs_le]
    constructor
    · have := hasSum_le (fun t => (abs_le.1 (hb t)).1) hgeo.neg (hsum k hk).hasSum
      simp only [pathValue]
      linarith
    · exact hasSum_le (fun t => (abs_le.1 (hb t)).2) (hsum k hk).hasSum hgeo
  · simp only [pathValue]
    rw [(hsum k hk).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, Function.iterate_zero, id]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [Function.iterate_succ_apply, pow_succ]
    ring

/-! ### Exercise 18.1 and the taxed economy, with existence -/

/-- **Exercise 18.1, complete** (p. 544). Let `0 < β < 1`; `U` strictly concave on `[0, ∞)`,
differentiable with `U′ ≥ 0` and bounded there; `f` concave on `[0, ∞)`; `K ⊆ [0, ∞)` invariant
under `g`, with `f` differentiable, `f′ ≥ 0`, `f(k) − k f′(k) ≥ 0`, `f(k) − g(k) ≥ 0` on `K`; and
let `g` satisfy the planner's Euler equation and transversality condition. Then:
(i) the individual's functional equation (2) has a bounded solution `V` on `[0, ∞) × K`, and any
two bounded solutions agree;
(ii) for `k ∈ K`, `V(k, k; g) = v(k)`, the maximal value of the planner's problem from `k`
(attained by the path of `g`);
(iii) `G(k, k; g) = g(k)`: `y` is optimal in (2) at `(k, k)` iff `y = g(k)`. -/
theorem ex_18_1_full {U f g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k) (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0)) :
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K ∧
      (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ K, |V' x k| ≤ M') →
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V' β K →
          ∀ x, 0 ≤ x → ∀ k ∈ K, V' x k = V x k) ∧
      ∀ k ∈ K, IsGreatest (plannerValues U f β k) (V k k) ∧
        ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
          (U (f k + (k - k) * deriv f k - y) + β * V y (g k) = V k k ↔ y = g k) := by
  obtain ⟨V, M, hVb, hsol⟩ := exists_bellman_solution (U := U) (g := g)
    (A := fun k => f k - k * deriv f k) (B := deriv f) hβ0.le hβ1 hUb hK hw hf'
  obtain ⟨hvb, hpol⟩ := pathValue_spec (Fk := f) hβ0.le hβ1 hUb hK hc
  have hUm : MonotoneOn U (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun c hc => (hUd c hc).continuousAt.continuousWithinAt)
      (fun c hc => (hUd c (interior_subset hc)).differentiableWithinAt) fun c hc => ?_
    exact hU' c (interior_subset hc)
  refine ⟨V, M, hVb, hsol, fun V' M' hV' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hV' hVb hK hw hf' hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := ex_18_1_dp hU hβ0 hβ1 hUd hU' hUb hK hK0 hf' hw hc heul htvc hvb hpol
    hVb hsol k hk
  refine ⟨?_, h4⟩
  have hkt := iterate_mem hK hk
  have hP := planner_optimal (ks := fun t => g^[t] k) hU.concaveOn hUm hβ0.le hβ1 hUb hUd hU'
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      exact heul _ (hkt t))
    (by simpa only [Function.iterate_succ_apply'] using htvc k hk)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  rw [h1]
  exact hP

/-- **The taxed economy (3), complete** (pp. 545–546). Tax `θ ∈ [0, 1)` on capital income,
rebated. Let `ĥ` satisfy the Euler equation of the pseudo-economy (8) with discount factor
`(1 − θ)β` and the individual's transversality condition (hypotheses as in `ex_18_1_full`).
Then: the functional equation (3) with `h = ĥ` has a bounded solution `W`, unique among bounded
solutions; the path of `ĥ` is optimal in the pseudo-economy (its value is the maximal value of
the pseudo-planner's problem with discount factor `(1 − θ)β`); `W(k, k; ĥ)` is the individual's
value of following `ĥ`; and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice at `(k, k)`, so `ĥ`
is a recursive competitive equilibrium. -/
theorem indirect_equilibrium_full {U f h : ℝ → ℝ} {β θ B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ K, 0 ≤ deriv f k)
    (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k) (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0)) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
        (fun k => (1 - θ) * deriv f k) h W β K ∧
      (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ K, |W' x k| ≤ M') →
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) h W' β K →
          ∀ x, 0 ≤ x → ∀ k ∈ K, W' x k = W x k) ∧
      ∀ k ∈ K, IsGreatest (plannerValues U f ((1 - θ) * β) k)
          (pathValue U f h ((1 - θ) * β) k) ∧
        W k k = pathValue U f h β k ∧
        ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
          (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (h k) = W k k ↔ y = h k) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  obtain ⟨W, M, hWb, hsol⟩ := exists_bellman_solution (U := U) (g := h)
    (A := fun k => f k - (1 - θ) * k * deriv f k) (B := fun k => (1 - θ) * deriv f k)
    hβ0.le hβ1 hUb hK hw hB
  obtain ⟨hvb, hpol⟩ := pathValue_spec (Fk := f) hβ0.le hβ1 hUb hK hc
  have hUm : MonotoneOn U (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun c hc => (hUd c hc).continuousAt.continuousWithinAt)
      (fun c hc => (hUd c (interior_subset hc)).differentiableWithinAt) fun c hc => ?_
    exact hU' c (interior_subset hc)
  refine ⟨W, M, hWb, hsol, fun W' M' hW' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hW' hWb hK hw hB hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := indirect_equilibrium_dp hU hβ0 hβ1 hθ hUd hU' hUb hK hK0 hf' hw hc heul
    htvc hvb hpol hWb hsol k hk
  refine ⟨?_, h1, h4⟩
  have hkt := iterate_mem hK hk
  have hβ' : 0 ≤ (1 - θ) * β := mul_nonneg (by linarith) hβ0.le
  have hβ'1 : (1 - θ) * β < 1 := by nlinarith
  -- the pseudo-planner's transversality condition follows from the individual's
  have htvc' := tvc_indiv_imp_pseudo hθ0 hθ (z := fun t => deriv U (f (h^[t] k) -
    h (h^[t] k)) * deriv f (h^[t] k) * h^[t] k) (by
      refine (htvc k hk).congr fun t => ?_
      ring)
  have hP := planner_optimal (ks := fun t => h^[t] k) hU.concaveOn hUm hβ' hβ'1 hUb hUd hU'
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      rw [heul _ (hkt t)])
    (by
      refine htvc'.congr fun t => ?_
      simp only [Function.iterate_succ_apply']
      ring)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  exact hP

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order and envelope conditions from the functional equation

SLP §18.1, pp. 545–546, (4)–(7). The book writes down the first-order condition (4) and the
envelope condition (5) for the bounded solution `W` of the individual's functional equation
(3), citing Chapter 4 (Theorems 4.10–4.11, Benveniste–Scheinkman), and evaluates them on the
diagonal to get (6)–(7). This module derives them.

* `hasDerivAt_of_concave_of_le` (**Benveniste–Scheinkman**, Theorem 4.10): a function `v`
  concave on a neighbourhood of `x₀`, minorised near `x₀` by a function `W` differentiable at
  `x₀` and touching it there, is differentiable at `x₀` with `v′(x₀) = W′(x₀)`. (Squeeze the
  slopes of `v` at `x₀` between those of `W` at `x₀` and at the reflected point `2x₀ − x`.)
* `bellman_concave`: for `U` concave and bounded on `[0, ∞)`, the bounded solution `W(·, k)`
  is concave in own capital `x` on `[0, ∞)`. (It is the supremum of the sequence-problem values
  (`bellman_isLUB`), the budget is linear in the path, and a convex combination of feasible
  paths is feasible.)
* `bellman_foc` (**§18.1 (4)**): at an optimal choice `y ∈ (0, A(k) + B(k)x)`, if `U` is
  differentiable at `c = A(k) + B(k)x − y` and `W(·, g(k))` at `y`, then
  `U′(c) = β W₁(y, g(k))`.
* `bellman_envelope` (**§18.1 (5)**): at `x > 0` with an optimal choice `y` and `c > 0`, `U`
  differentiable at `c` and concave: `W(·, k)` is differentiable at `x` with
  `W₁(x, k) = B(k) U′(c)`.
* `bellman_diagonal` (**§18.1 (6)–(7)**, generic budget): if `h(k)` is optimal at `(k, k)` and
  `h(h(k))` at `(h(k), h(k))`, with interior choices, then `φ(k) := W₁(k, k)` satisfies
  `φ(k) = B(k) U′(F(k) − h(k))` and `U′(F(k) − h(k)) = β φ(h(k))`; hence the Euler equation
  `U′(F(k) − h(k)) = β B(h(k)) U′(F(h(k)) − h(h(k)))`.
* `eq_18_1_4_5` and `eq_18_1_6_7`: the same for the taxed economy (3) literally, with
  `F = f`, `B = (1 − θ) f′`. `ex_18_1_foc_envelope`: the untaxed (2) (`θ = 0`).
* `eq_18_1_6_7_of_equilibrium`: combined with `indirect_equilibrium_full`: for the pseudo-planner's
  policy `ĥ` with interior choices, the bounded solution `W` of (3) satisfies (4)–(7), with
  `φ = W₁(k, k)`.

The hypotheses are those of SLP Theorem 4.11: interior state (`x > 0`), interior choice
(`0 < y`, `c > 0`), and differentiability of `U` at the optimal consumption. Differentiability of
`W(·, g(k))` at the optimal `y`, needed in (4), is itself supplied by (5) at the next date when
the next choice is interior (`bellman_diagonal`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- **Benveniste–Scheinkman** (SLP Theorem 4.10). Let `v` be concave on a set `S` that is a
neighbourhood of `x₀`, and let `W ≤ v` near `x₀` with `W(x₀) = v(x₀)` and `W` differentiable at
`x₀` with derivative `d`. Then `v` is differentiable at `x₀` with derivative `d`. -/
theorem hasDerivAt_of_concave_of_le {v W : ℝ → ℝ} {S : Set ℝ} {x₀ d : ℝ}
    (hv : ConcaveOn ℝ S v) (hS : S ∈ 𝓝 x₀) (hle : ∀ᶠ x in 𝓝 x₀, W x ≤ v x)
    (heq : W x₀ = v x₀) (hW : HasDerivAt W d x₀) : HasDerivAt v d x₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hW ⊢
  -- the reflection `x ↦ 2x₀ − x` maps `𝓝[≠] x₀` to itself
  have hr : Tendsto (fun x => 2 * x₀ - x) (𝓝[≠] x₀) (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x => 2 * x₀ - x) (𝓝 x₀) (𝓝 (2 * x₀ - x₀)) :=
        (continuous_const.sub continuous_id).tendsto x₀
      rw [show 2 * x₀ - x₀ = x₀ by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro h
      apply hx
      change x = x₀
      change 2 * x₀ - x = x₀ at h
      linarith
  have hL := hW.comp hr
  have hlo := hW.min hL
  have hhi := hW.max hL
  rw [min_self] at hlo
  rw [max_self] at hhi
  -- a symmetric neighbourhood on which everything holds
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hS hle)
  have hsq : ∀ᶠ x in 𝓝[≠] x₀, min (slope W x₀ x) ((slope W x₀ ∘ fun x => 2 * x₀ - x) x) ≤
      slope v x₀ x ∧ slope v x₀ x ≤
        max (slope W x₀ x) ((slope W x₀ ∘ fun x => 2 * x₀ - x) x) := by
    have hmem : Metric.ball x₀ δ ∈ 𝓝[≠] x₀ :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x₀ hδ)
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hne
    have hne' : x ≠ x₀ := hne
    set a := 2 * x₀ - x with ha
    have hxb : |x - x₀| < δ := by rwa [Metric.mem_ball, Real.dist_eq] at hx
    have hab : a ∈ Metric.ball x₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, ha]
      rw [show 2 * x₀ - x - x₀ = -(x - x₀) by ring, abs_neg]
      exact hxb
    have hx0b : x₀ ∈ Metric.ball x₀ δ := Metric.mem_ball_self hδ
    obtain ⟨hxS, hxW⟩ := hball hx
    obtain ⟨haS, haW⟩ := hball hab
    obtain ⟨hx0S, -⟩ := hball hx0b
    change W x ≤ v x at hxW
    change W a ≤ v a at haW
    simp only [Function.comp, slope_def_field]
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · -- `x < x₀ < a`
      have hxa : x₀ < a := by rw [ha]; linarith
      have h1 : (v x₀ - v x) / (x₀ - x) ≤ (W x₀ - W x) / (x₀ - x) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have h2 : (v a - v x₀) / (a - x₀) ≤ (v x₀ - v x) / (x₀ - x) :=
        hv.slope_anti_adjacent hxS haS hlt hxa
      have h3 : (W a - W x₀) / (a - x₀) ≤ (v a - v x₀) / (a - x₀) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e1 : (v x - v x₀) / (x - x₀) = (v x₀ - v x) / (x₀ - x) := by
        rw [← neg_sub (v x₀), ← neg_sub x₀, neg_div_neg_eq]
      have e2 : (W x - W x₀) / (x - x₀) = (W x₀ - W x) / (x₀ - x) := by
        rw [← neg_sub (W x₀), ← neg_sub x₀, neg_div_neg_eq]
      rw [e1, e2]
      exact ⟨(min_le_right _ _).trans (h3.trans h2), h1.trans (le_max_left _ _)⟩
    · -- `a < x₀ < x`
      have hxa : a < x₀ := by rw [ha]; linarith
      have h1 : (W x - W x₀) / (x - x₀) ≤ (v x - v x₀) / (x - x₀) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have h2 : (v x - v x₀) / (x - x₀) ≤ (v x₀ - v a) / (x₀ - a) :=
        hv.slope_anti_adjacent haS hxS hxa hgt
      have h3 : (v x₀ - v a) / (x₀ - a) ≤ (W x₀ - W a) / (x₀ - a) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e2 : (W a - W x₀) / (a - x₀) = (W x₀ - W a) / (x₀ - a) := by
        rw [← neg_sub (W x₀), ← neg_sub x₀, neg_div_neg_eq]
      rw [e2]
      exact ⟨(min_le_left _ _).trans h1, h2.trans (h3.trans (le_max_right _ _))⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hsq.mono fun _ h => h.1)
    (hsq.mono fun _ h => h.2)

/-- **Concavity of the bounded solution in own capital.** Under the hypotheses of
`bellman_isLUB` and with `U` concave on `[0, ∞)`, `x ↦ W(x, k)` is concave on `[0, ∞)` for every
`k ∈ K`. -/
theorem bellman_concave {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hUc : ConcaveOn ℝ (Ici 0) U) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hsol : SolvesBellman U A B g W β K)
    {k : ℝ} (hk : k ∈ K) : ConcaveOn ℝ (Ici 0) fun x => W x k := by
  refine ⟨convex_Ici 0, fun x hx x' hx' a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := hx
  have hx0' : (0 : ℝ) ≤ x' := hx'
  have hz : 0 ≤ a * x + b * x' := by positivity
  set at' : ℕ → ℝ := fun t => A (g^[t] k) with hat
  set bt : ℕ → ℝ := fun t => B (g^[t] k) with hbt
  have hL := bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hx0 hk
  have hL' := bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hx0' hk
  have hLz := bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hz hk
  -- any convex combination of attainable values is at most `W(a x + b x', k)`
  have key : ∀ S ∈ indivValues U β at' bt x, ∀ S' ∈ indivValues U β at' bt x',
      a * S + b * S' ≤ W (a * x + b * x') k := by
    rintro S ⟨p, hp, hS⟩ S' ⟨p', hp', hS'⟩
    set q : ℕ → ℝ := fun t => a * p t + b * p' t with hq
    have hcq : ∀ t, consPath at' bt q t = a * consPath at' bt p t + b * consPath at' bt p' t := by
      intro t
      simp only [consPath, hq]
      linear_combination (-at' t) * hab
    have hqf : IndivFeasible at' bt (a * x + b * x') q := by
      refine ⟨by simp only [hq, hp.1, hp'.1], fun t => ⟨?_, ?_⟩⟩
      · have := (hp.2 t).1
        have := (hp'.2 t).1
        simp only [hq]
        positivity
      · rw [hcq]
        have := (hp.2 t).2
        have := (hp'.2 t).2
        positivity
    have hsum : Summable fun t => β ^ t * U (consPath at' bt q t) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
        fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (hU _ (hqf.2 t).2) (pow_nonneg hβ0 t)
    have hle : a * S + b * S' ≤ ∑' t, β ^ t * U (consPath at' bt q t) := by
      refine hasSum_le (fun t => ?_) ((hS.mul_left a).add (hS'.mul_left b)) hsum.hasSum
      rw [hcq]
      have hcc := hUc.2 (mem_Ici.2 (hp.2 t).2) (mem_Ici.2 (hp'.2 t).2) ha hb hab
      simp only [smul_eq_mul] at hcc
      have := mul_le_mul_of_nonneg_left hcc (pow_nonneg hβ0 t)
      linarith
    exact hle.trans (hLz.1 ⟨q, hqf, hsum.hasSum⟩)
  -- pass to the suprema
  simp only [smul_eq_mul]
  by_contra hcon
  push Not at hcon
  set η := a * W x k + b * W x' k - W (a * x + b * x') k with hη
  have hηp : 0 < η := by linarith
  obtain ⟨S, hS, hS1, -⟩ := hL.exists_between (show W x k - η / 2 < W x k by linarith)
  obtain ⟨S', hS', hS1', -⟩ := hL'.exists_between (show W x' k - η / 2 < W x' k by linarith)
  have h := key S hS S' hS'
  have h1 := mul_le_mul_of_nonneg_left hS1.le ha
  have h2 := mul_le_mul_of_nonneg_left hS1'.le hb
  have : a * (W x k - η / 2) + b * (W x' k - η / 2) = a * W x k + b * W x' k - η / 2 := by
    have : a * (η / 2) + b * (η / 2) = η / 2 := by rw [← add_mul, hab, one_mul]
    linarith
  linarith

/-- The maximand of the functional equation is bounded above on `Γ(x, k)`. -/
theorem bellman_bddAbove {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hK : ∀ k ∈ K, g k ∈ K) (x : ℝ) {k : ℝ} (hk : k ∈ K) :
    BddAbove ((fun y => U (A k + B k * x - y) + β * W y (g k)) '' feasY A B x k) := by
  refine ⟨B₀ + β * M, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 := (abs_le.1 (hU _ hy.2)).2
  have h2 := (abs_le.1 (hW y hy.1 _ (hK k hk))).2
  have := mul_le_mul_of_nonneg_left h2 hβ0
  simp only
  linarith

/-- **The first-order condition §18.1 (4).** Let `W` be a bounded solution of the functional
equation, `x ≥ 0`, `k ∈ K`, and let `y` attain the supremum at `(x, k)` with
`0 < y < A(k) + B(k)x` (an interior choice). If `U` has derivative `u` at
`c = A(k) + B(k)x − y` and `W(·, g(k))` has derivative `w` at `y`, then `u = β w`:
`U′(c) = β W₁(y, g(k))`. -/
theorem bellman_foc {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hK : ∀ k ∈ K, g k ∈ K) (hsol : SolvesBellman U A B g W β K) {x k y u w : ℝ}
    (hx : 0 ≤ x) (hk : k ∈ K) (hy : 0 < y) (hc : y < A k + B k * x)
    (hopt : U (A k + B k * x - y) + β * W y (g k) = W x k)
    (hUd : HasDerivAt U u (A k + B k * x - y))
    (hWd : HasDerivAt (fun z => W z (g k)) w y) : u = β * w := by
  set φ : ℝ → ℝ := fun z => U (A k + B k * x - z) + β * W z (g k) with hφ
  have hmax : IsLocalMax φ y := by
    filter_upwards [Ioo_mem_nhds hy hc] with z hz
    have hzf : z ∈ feasY A B x k := ⟨hz.1.le, by linarith [hz.2]⟩
    change φ z ≤ φ y
    have h1 : φ y = W x k := hopt
    rw [h1, hsol x hx k hk]
    exact le_csSup (bellman_bddAbove hβ0 hU hW hK x hk) ⟨z, hzf, rfl⟩
  have hd1 : HasDerivAt (fun z => U (A k + B k * x - z)) (u * -1) y := by
    have hi : HasDerivAt (fun z => A k + B k * x - z) (-1) y :=
      (hasDerivAt_id y).const_sub (A k + B k * x)
    exact hUd.comp y hi
  have hd : HasDerivAt φ (u * -1 + β * w) y := hd1.add (hWd.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **The envelope condition §18.1 (5)** (Benveniste–Scheinkman). Let `U` be concave and
bounded on `[0, ∞)`, `W` a bounded solution of the functional equation, `k ∈ K`, `x > 0`, and
let `y ≥ 0` attain the supremum at `(x, k)` with positive consumption
`c = A(k) + B(k)x − y > 0`. If `U` has derivative `u` at `c`, then `W(·, k)` is differentiable
at `x` with `W₁(x, k) = B(k) u = B(k) U′(c)`. -/
theorem bellman_envelope {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hUc : ConcaveOn ℝ (Ici 0) U) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hsol : SolvesBellman U A B g W β K)
    {x k y u : ℝ} (hx : 0 < x) (hk : k ∈ K) (hy : 0 ≤ y) (hc : 0 < A k + B k * x - y)
    (hopt : U (A k + B k * x - y) + β * W y (g k) = W x k)
    (hUd : HasDerivAt U u (A k + B k * x - y)) :
    HasDerivAt (fun z => W z k) (B k * u) x := by
  set Wf : ℝ → ℝ := fun z => U (A k + B k * z - y) + β * W y (g k) with hWf
  have hi : HasDerivAt (fun z => A k + B k * z - y) (B k) x := by
    have := (((hasDerivAt_id x).const_mul (B k)).const_add (A k)).sub_const y
    simpa using this
  have hWfd : HasDerivAt Wf (B k * u) x := by
    have := (hUd.comp x hi).add_const (β * W y (g k))
    rw [mul_comm u] at this
    exact this
  have hcont : Continuous fun z => A k + B k * z - y := by fun_prop
  have hle : ∀ᶠ z in 𝓝 x, Wf z ≤ W z k := by
    filter_upwards [Ioi_mem_nhds hx, hcont.continuousAt.eventually (Ioi_mem_nhds hc)]
      with z hz hcz
    have hz0 : 0 ≤ z := le_of_lt hz
    have hyf : y ∈ feasY A B z k := ⟨hy, le_of_lt hcz⟩
    rw [hsol z hz0 k hk]
    exact le_csSup (bellman_bddAbove hβ0 hU hW hK z hk) ⟨y, hyf, rfl⟩
  exact hasDerivAt_of_concave_of_le (bellman_concave hβ0 hβ1 hUc hU hW hK hA hB hsol hk)
    (Ici_mem_nhds hx) hle hopt hWfd

/-- **§18.1 (6)–(7) on the diagonal, generic budget.** Let `U` be concave and bounded on
`[0, ∞)`, `W` a bounded solution of the functional equation with aggregate law `h`, and on `K`
let `A(k) + B(k) k = F(k)`. Let `k ∈ K` with `k > 0`, and suppose that `h(k)` is optimal at
`(k, k)` and `h(h(k))` at `(h(k), h(h(k)))` (`H(k, k; h) = h(k)`), with interior choices
`0 < h(k)`, `F(k) − h(k) > 0`, `h(h(k)) ≥ 0`, `F(h(k)) − h(h(k)) > 0`, and `U` differentiable
at both consumptions. Then, with `φ(k) = W₁(k, k)`:
(7) `W(·, k)` is differentiable at `k` and `φ(k) = B(k) U′(F(k) − h(k))`, and likewise at
`h(k)`; (6) `U′(F(k) − h(k)) = β φ(h(k))`; hence the Euler equation
`U′(F(k) − h(k)) = β B(h(k)) U′(F(h(k)) − h(h(k)))`. -/
theorem bellman_diagonal {U A B Fk h : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hUc : ConcaveOn ℝ (Ici 0) U) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, h k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hAB : ∀ k ∈ K, A k + B k * k = Fk k)
    (hsol : SolvesBellman U A B h W β K) {k : ℝ} (hk : k ∈ K) (hk0 : 0 < k)
    (hh0 : 0 < h k) (hc1 : 0 < Fk k - h k) (hhh0 : 0 ≤ h (h k))
    (hc2 : 0 < Fk (h k) - h (h k))
    (hopt1 : U (A k + B k * k - h k) + β * W (h k) (h k) = W k k)
    (hopt2 : U (A (h k) + B (h k) * h k - h (h k)) + β * W (h (h k)) (h (h k)) =
      W (h k) (h k))
    (hUd1 : DifferentiableAt ℝ U (Fk k - h k))
    (hUd2 : DifferentiableAt ℝ U (Fk (h k) - h (h k))) :
    HasDerivAt (fun x => W x k) (B k * deriv U (Fk k - h k)) k ∧
      HasDerivAt (fun x => W x (h k)) (B (h k) * deriv U (Fk (h k) - h (h k))) (h k) ∧
      deriv (fun x => W x k) k = B k * deriv U (Fk k - h k) ∧
      deriv U (Fk k - h k) = β * deriv (fun x => W x (h k)) (h k) ∧
      deriv U (Fk k - h k) = β * B (h k) * deriv U (Fk (h k) - h (h k)) := by
  have hhk := hK k hk
  have e1 : A k + B k * k - h k = Fk k - h k := by rw [hAB k hk]
  have e2 : A (h k) + B (h k) * h k - h (h k) = Fk (h k) - h (h k) := by rw [hAB _ hhk]
  have hd1 : HasDerivAt (fun x => W x k) (B k * deriv U (Fk k - h k)) k := by
    refine bellman_envelope hβ0 hβ1 hUc hU hW hK hA hB hsol hk0 hk hh0.le (by rwa [e1]) hopt1
      ?_
    rw [e1]
    exact hUd1.hasDerivAt
  have hd2 : HasDerivAt (fun x => W x (h k)) (B (h k) * deriv U (Fk (h k) - h (h k))) (h k) := by
    refine bellman_envelope hβ0 hβ1 hUc hU hW hK hA hB hsol hh0 hhk hhh0 (by rwa [e2]) hopt2 ?_
    rw [e2]
    exact hUd2.hasDerivAt
  have hfoc := bellman_foc hβ0 hU hW hK hsol hk0.le hk hh0 (by linarith [e1]) hopt1
    (by rw [e1]; exact hUd1.hasDerivAt) hd2
  refine ⟨hd1, hd2, hd1.deriv, ?_, ?_⟩
  · rw [hd2.deriv]
    exact hfoc
  · rw [hfoc]
    ring

/-- **§18.1 (4)–(5) for the taxed economy (3)**, literally. Tax `θ < 1` on capital income,
rebated; `U` concave and bounded on `[0, ∞)`; `f′ ≥ 0` and `f(k) − (1 − θ) k f′(k) ≥ 0` on `K`;
`W` a bounded solution of (3) with aggregate law `h`. Let `k ∈ K`, `x > 0`, and let `y = H(x, k)`
attain the supremum in (3) at `(x, k)`, with `0 < y` and consumption
`c = f(k) + (1 − θ)(x − k) f′(k) − y > 0`, `U` differentiable at `c`. Then
(5) `W₁(x, k) = (1 − θ) f′(k) U′(c)`; and (4) if `W(·, h(k))` is differentiable at `y`,
`U′(c) = β W₁(y, h(k))`. -/
theorem eq_18_1_4_5 {U f h : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : θ < 1) (hUc : ConcaveOn ℝ (Ici 0) U)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K)
    {x k y : ℝ} (hx : 0 < x) (hk : k ∈ K) (hy : 0 < y)
    (hc : 0 < f k + (1 - θ) * (x - k) * deriv f k - y)
    (hopt : U (f k + (1 - θ) * (x - k) * deriv f k - y) + β * W y (h k) = W x k)
    (hUd : DifferentiableAt ℝ U (f k + (1 - θ) * (x - k) * deriv f k - y)) :
    HasDerivAt (fun z => W z k)
        ((1 - θ) * deriv f k * deriv U (f k + (1 - θ) * (x - k) * deriv f k - y)) x ∧
      (DifferentiableAt ℝ (fun z => W z (h k)) y →
        deriv U (f k + (1 - θ) * (x - k) * deriv f k - y) =
          β * deriv (fun z => W z (h k)) y) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  have e : (fun k => f k - (1 - θ) * k * deriv f k) k + (fun k => (1 - θ) * deriv f k) k * x - y =
      f k + (1 - θ) * (x - k) * deriv f k - y := by simp only; ring
  refine ⟨?_, fun hWd => ?_⟩
  · refine bellman_envelope hβ0 hβ1 hUc hU hW hK hw hB hsol hx hk hy.le (by rwa [e])
      (by rwa [e]) ?_
    rw [e]
    exact hUd.hasDerivAt
  · refine bellman_foc hβ0 hU hW hK hsol hx.le hk hy (by linarith [e]) (by rwa [e]) ?_
      hWd.hasDerivAt
    rw [e]
    exact hUd.hasDerivAt

/-- **§18.1 (6)–(7) for the taxed economy (3)** (p. 546). Hypotheses of `eq_18_1_4_5`; let `h`
be an equilibrium at `k` and `h(k)` (`h(k)` optimal at `(k, k)`, `h(h(k))` optimal at
`(h(k), h(k))`) with `k > 0`, `h(k) > 0`, `h(h(k)) ≥ 0` and positive consumptions
`f(k) − h(k)`, `f(h(k)) − h(h(k))`, `U` differentiable there. Then `φ(k) := W₁(k, k; h)` satisfies
(7) `φ(k) = (1 − θ) f′(k) U′[f(k) − h(k)]` and (6) `U′[f(k) − h(k)] = β φ[h(k)]`; hence
`U′[f(k) − h(k)] = β (1 − θ) f′(h(k)) U′[f(h(k)) − h(h(k))]`. -/
theorem eq_18_1_6_7 {U f h : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : θ < 1) (hUc : ConcaveOn ℝ (Ici 0) U)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K)
    {k : ℝ} (hk : k ∈ K) (hk0 : 0 < k) (hh0 : 0 < h k) (hc1 : 0 < f k - h k)
    (hhh0 : 0 ≤ h (h k)) (hc2 : 0 < f (h k) - h (h k))
    (hopt1 : U (f k + (1 - θ) * (k - k) * deriv f k - h k) + β * W (h k) (h k) = W k k)
    (hopt2 : U (f (h k) + (1 - θ) * (h k - h k) * deriv f (h k) - h (h k)) +
      β * W (h (h k)) (h (h k)) = W (h k) (h k))
    (hUd1 : DifferentiableAt ℝ U (f k - h k))
    (hUd2 : DifferentiableAt ℝ U (f (h k) - h (h k))) :
    deriv (fun x => W x k) k = (1 - θ) * deriv f k * deriv U (f k - h k) ∧
      deriv U (f k - h k) = β * deriv (fun x => W x (h k)) (h k) ∧
      deriv U (f k - h k) = β * (1 - θ) * deriv f (h k) * deriv U (f (h k) - h (h k)) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  have e : ∀ k : ℝ, (fun k => f k - (1 - θ) * k * deriv f k) k +
      (fun k => (1 - θ) * deriv f k) k * k = f k := fun k => by simp only; ring
  have e' : ∀ k : ℝ, f k + (1 - θ) * (k - k) * deriv f k = f k := fun k => by ring
  rw [e'] at hopt1 hopt2
  obtain ⟨-, -, h3, h4, h5⟩ := bellman_diagonal (Fk := f) hβ0 hβ1 hUc hU hW hK hw hB
    (fun k _ => e k) hsol hk hk0 hh0 hc1 hhh0 hc2 (by rw [e]; exact hopt1)
    (by rw [e]; exact hopt2) hUd1 hUd2
  refine ⟨h3, h4, ?_⟩
  rw [h5]
  ring

/-- **(4)–(7) at the indirect equilibrium.** Under the hypotheses of `indirect_equilibrium_full`
(the pseudo-planner's policy `ĥ`, with the individual's transversality condition), let `W` be
the bounded solution of (3) with `h = ĥ`. At every `k ∈ K` with `k > 0`, `ĥ(k) > 0` and positive
consumptions `f(k) − ĥ(k)`, `f(ĥ(k)) − ĥ(ĥ(k))`, the function `φ(k) = W₁(k, k; ĥ)` exists and
satisfies (7) `φ(k) = (1 − θ) f′(k) U′[f(k) − ĥ(k)]` and (6) `U′[f(k) − ĥ(k)] = β φ[ĥ(k)]`.
So the solution of (6)–(7) produced by the pseudo-economy is the marginal value of the
individual's own capital, as the book asserts on p. 546. -/
theorem eq_18_1_6_7_of_equilibrium {U f h : ℝ → ℝ} {β θ B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ K, 0 ≤ deriv f k)
    (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k) (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0)) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
        (fun k => (1 - θ) * deriv f k) h W β K ∧
      ∀ k ∈ K, 0 < k → 0 < h k → 0 < f k - h k → 0 < f (h k) - h (h k) →
        deriv (fun x => W x k) k = (1 - θ) * deriv f k * deriv U (f k - h k) ∧
        deriv U (f k - h k) = β * deriv (fun x => W x (h k)) (h k) := by
  obtain ⟨W, M, hWb, hsol, -, hall⟩ := indirect_equilibrium_full hU hβ0 hβ1 hθ0 hθ hUd hU' hUb
    hf hK hK0 hfd hf' hw hc heul htvc
  refine ⟨W, M, hWb, hsol, fun k hk hk0 hh0 hc1 hc2 => ?_⟩
  have hhk := hK k hk
  have hfeas : ∀ k ∈ K, h k ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) k k := fun k hk => ⟨hK0 _ (hK k hk), by
        have := hc k hk
        simp only
        linarith⟩
  have hopt1 := ((hall k hk).2.2 (h k) (hfeas k hk)).2 rfl
  have hopt2 := ((hall (h k) hhk).2.2 (h (h k)) (hfeas _ hhk)).2 rfl
  obtain ⟨h1, h2, -⟩ := eq_18_1_6_7 hβ0.le hβ1 hθ hU.concaveOn hUb hK hf' hw hWb hsol hk hk0
    hh0 hc1 (hK0 _ (hK _ hhk)) hc2 hopt1 hopt2 (hUd _ hc1.le) (hUd _ hc2.le)
  exact ⟨h1, h2⟩

/-- **The first-order and envelope conditions for (2)** (Exercise 18.1 setting). Under the
hypotheses of `ex_18_1_full` (the planner's policy `g` with its Euler equation and transversality
condition), let `V` be the bounded solution of (2). At every `k ∈ K` with `k > 0`, `g(k) > 0` and
positive consumptions `f(k) − g(k)`, `f(g(k)) − g(g(k))`:
`V₁(k, k; g) = f′(k) U′[f(k) − g(k)]` and `U′[f(k) − g(k)] = β V₁(g(k), g(k); g)`. -/
theorem ex_18_1_foc_envelope {U f g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k) (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0)) :
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K ∧
      ∀ k ∈ K, 0 < k → 0 < g k → 0 < f k - g k → 0 < f (g k) - g (g k) →
        deriv (fun x => V x k) k = deriv f k * deriv U (f k - g k) ∧
        deriv U (f k - g k) = β * deriv (fun x => V x (g k)) (g k) := by
  obtain ⟨V, M, hVb, hsol, -, hall⟩ := ex_18_1_full hU hβ0 hβ1 hUd hU' hUb hf hK hK0 hfd hf' hw
    hc heul htvc
  refine ⟨V, M, hVb, hsol, fun k hk hk0 hg0 hc1 hc2 => ?_⟩
  have hgk := hK k hk
  have e : ∀ k : ℝ, (fun k => f k - k * deriv f k) k + deriv f k * k = f k := fun k => by
    simp only; ring
  have e' : ∀ k : ℝ, f k + (k - k) * deriv f k = f k := fun k => by ring
  have hfeas : ∀ k ∈ K, g k ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k :=
    fun k hk => ⟨hK0 _ (hK k hk), by have := hc k hk; simp only; linarith⟩
  have hopt1 := ((hall k hk).2 (g k) (hfeas k hk)).2 rfl
  have hopt2 := ((hall (g k) hgk).2 (g (g k)) (hfeas _ hgk)).2 rfl
  rw [e'] at hopt1 hopt2
  obtain ⟨-, -, h3, h4, -⟩ := bellman_diagonal (Fk := f) hβ0.le hβ1 hU.concaveOn hUb hVb hK hw
    hf' (fun k _ => e k) hsol hk hk0 hg0 hc1 (hK0 _ (hK _ hgk)) hc2 (by rw [e]; exact hopt1)
    (by rw [e]; exact hopt2) (hUd _ hc1.le) (hUd _ hc2.le)
  exact ⟨h3, h4⟩

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of the planner's value and policy, (1) and (8)

SLP §18.1, pp. 543 and 546. The planner's functional equation (1),
`v(k) = max_{0 ≤ y ≤ f(k)} {U[f(k) − y] + β v(y)}`, and that of the pseudo-economy (8) (the same
with discount factor `β̂ = (1 − θ)β`) are solved "by Chapter 4 methods" in the book. This module
carries out those methods for a generic discount factor `b ∈ [0, 1)` on `K = [0, k̄]`
(`PlannerHyp`: `U` continuous, nondecreasing and strictly concave on `[0, ∞)`; `f` continuous and
concave on `K` with `0 ≤ f ≤ k̄` there, so that `[0, f(k)] ⊆ K`).

* `plannerOp`, `plannerOp_contracting` (Theorem 4.6): the Bellman operator acts on the Banach
  space `ℝ →ᵇ ℝ` of bounded continuous functions and is a `b`-contraction. (A function on `ℝ`
  is used for convenience: `k` and `c` are clamped to `K`, and only values on `K` matter. The
  supremum over `y ∈ [0, f(k)]` is written as one over `s ∈ [0, 1]`, `y = s f(k)`, so that the
  Theorem of the Maximum reduces to `IsCompact.continuous_sSup`.)
* `plannerValue`, `plannerValue_solves`: its fixed point `v` is continuous and bounded and solves
  (1) on `K` (`SolvesPlanner`).
* `plannerValue_concave` (Theorem 4.8): `v` is concave on `K` (`T` preserves concavity, and the
  fixed point is the limit of `Tⁿ0`).
* `plannerPolicy`, `plannerPolicy_spec`, `plannerPolicy_unique` (Theorem 4.8): the maximum is
  attained at a unique `g(k) ∈ [0, f(k)]` (strict concavity of `U`), and
  `v(k) = U[f(k) − g(k)] + b v(g(k))`.
* `plannerPolicy_continuousOn` (Theorem 4.8, Theorem of the Maximum): `g` is continuous on `K`
  (its graph is closed and `K` is compact).
* `planner_envelope` (§18.1 (10), Theorem 4.11): at `k ∈ (0, k̄)` with `g(k) < f(k)`, `U`
  differentiable at `f(k) − g(k)` and `f` at `k`, `v′(k) = f′(k) U′[f(k) − g(k)]`.
* `planner_foc` (§18.1 (9)): at an interior choice `0 < g(k) < f(k)` with `v` differentiable at
  `g(k)`, `U′[f(k) − g(k)] = b v′(g(k))`.
* `planner_euler`: if `0 < g(k) < f(k)` and `g(g(k)) < f(g(k))`, the Euler equation
  `U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]` holds.

Interiority of the policy is a hypothesis here, as in SLP Theorem 4.11. With `U` differentiable
on `[0, ∞)` (which the book's Assumption 18.1 requires), `U′(0)` is finite, so the usual Inada
argument for interiority is not available. `PlannerHyp` asks only that `U` be continuous on
`[0, ∞)`, which allows `U′(0+) = ∞`; under that Inada condition, `b > 0`, `f(0) = 0` and `f > 0`
on `(0, k̄]` (`InteriorHyp`), `IndirectInterior` proves `0 < g(k) < f(k)` on `(0, k̄]`
(`InteriorHyp.policy_interior`), and `k = 0` is degenerate (`InteriorHyp.not_interior_zero`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set BoundedContinuousFunction

/-- **Hypotheses for the planner's problem** (1)/(8) on `K = [0, k̄]` with discount factor `b`. -/
structure PlannerHyp (U f : ℝ → ℝ) (b kbar : ℝ) : Prop where
  b_nonneg : 0 ≤ b
  b_lt_one : b < 1
  kbar_nonneg : 0 ≤ kbar
  U_cont : ContinuousOn U (Ici 0)
  U_mono : MonotoneOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  f_cont : ContinuousOn f (Icc 0 kbar)
  f_concave : ConcaveOn ℝ (Icc 0 kbar) f
  f_nonneg : ∀ k ∈ Icc 0 kbar, 0 ≤ f k
  f_le : ∀ k ∈ Icc 0 kbar, f k ≤ kbar

/-- `v` solves the planner's functional equation (1) (discount factor `b`) on `K = [0, k̄]`. -/
def SolvesPlanner (U f : ℝ → ℝ) (b kbar : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ k ∈ Icc 0 kbar, v k = sSup ((fun y => U (f k - y) + b * v y) '' Icc 0 (f k))

/-- The nearest point of `[0, k̄]`. -/
noncomputable def clampK (kbar x : ℝ) : ℝ := max 0 (min kbar x)

/-- `clampK` maps into `[0, k̄]`. -/
theorem clampK_mem {kbar : ℝ} (h : 0 ≤ kbar) (x : ℝ) : clampK kbar x ∈ Icc 0 kbar :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- `clampK` is the identity on `[0, k̄]`. -/
theorem clampK_of_mem {kbar x : ℝ} (hx : x ∈ Icc 0 kbar) : clampK kbar x = x := by
  simp only [clampK, min_eq_right hx.2, max_eq_right hx.1]

/-- `clampK` is continuous. -/
theorem continuous_clampK (kbar : ℝ) : Continuous (clampK kbar) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- `U ∘ clampK` is continuous. -/
theorem PlannerHyp.continuous_U {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    Continuous fun c => U (clampK kbar c) :=
  (P.U_cont.mono Icc_subset_Ici_self).comp_continuous (continuous_clampK kbar)
    (clampK_mem P.kbar_nonneg)

/-- `f ∘ clampK` is continuous. -/
theorem PlannerHyp.continuous_f {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    Continuous fun k => f (clampK kbar k) :=
  P.f_cont.comp_continuous (continuous_clampK kbar) (clampK_mem P.kbar_nonneg)

/-- `U` is bounded on `[0, k̄]`. -/
theorem PlannerHyp.exists_bound {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ∃ C, 0 ≤ C ∧ ∀ c, |U (clampK kbar c)| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (P.U_cont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) kbar ⊆ Ici 0))
  refine ⟨max C 0, le_max_right _ _, fun c => ?_⟩
  have := hC _ (clampK_mem P.kbar_nonneg c)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- A bound for `|U|` on `[0, k̄]`. -/
noncomputable def PlannerHyp.UB {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) : ℝ :=
  Classical.choose P.exists_bound

/-- The bound `PlannerHyp.UB`. -/
theorem PlannerHyp.UB_spec {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    0 ≤ P.UB ∧ ∀ c, |U (clampK kbar c)| ≤ P.UB :=
  Classical.choose_spec P.exists_bound

/-- The maximand of (1), written with `y = s f(k)`, `s ∈ [0, 1]`, and clamped to `K`. -/
noncomputable def plannerG (U f : ℝ → ℝ) (b kbar : ℝ) (v : ℝ → ℝ) (k s : ℝ) : ℝ :=
  U (clampK kbar (f (clampK kbar k) - s * f (clampK kbar k))) + b * v (s * f (clampK kbar k))

/-- The maximand is jointly continuous for continuous `v`. -/
theorem PlannerHyp.continuous_plannerG {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous fun p : ℝ × ℝ => plannerG U f b kbar v p.1 p.2 := by
  have hf : Continuous fun p : ℝ × ℝ => f (clampK kbar p.1) :=
    P.continuous_f.comp continuous_fst
  exact (P.continuous_U.comp (hf.sub (continuous_snd.mul hf))).add
    (continuous_const.mul (hv.comp (continuous_snd.mul hf)))

/-- The maximand is bounded by `UB + b ‖v‖`. -/
theorem PlannerHyp.abs_plannerG_le {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) (k s : ℝ) : |plannerG U f b kbar v k s| ≤ P.UB + b * ‖v‖ := by
  have h1 := P.UB_spec.2 (f (clampK kbar k) - s * f (clampK kbar k))
  have h2 : |v (s * f (clampK kbar k))| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact v.norm_coe_le_norm _
  have h3 := mul_le_mul_of_nonneg_left h2 P.b_nonneg
  calc |plannerG U f b kbar v k s|
      ≤ |U (clampK kbar (f (clampK kbar k) - s * f (clampK kbar k)))| +
          |b * v (s * f (clampK kbar k))| := abs_add_le _ _
    _ ≤ P.UB + b * ‖v‖ := by rw [abs_mul, abs_of_nonneg P.b_nonneg]; linarith

/-- The image of the maximand over `s ∈ [0, 1]` is bounded above. -/
theorem PlannerHyp.bddAbove_plannerG {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) (k : ℝ) : BddAbove (plannerG U f b kbar v k '' Icc 0 1) :=
  ⟨P.UB + b * ‖v‖, by rintro _ ⟨s, -, rfl⟩; exact (abs_le.1 (P.abs_plannerG_le v k s)).2⟩

/-- **The Bellman operator of (1)** on `ℝ →ᵇ ℝ`:
`(Tv)(k) = sup_{s ∈ [0, 1]} {U[f(k) − s f(k)] + b v(s f(k))}` (clamped to `K`). -/
noncomputable def plannerOp {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  ofNormedAddCommGroup (fun k => sSup (plannerG U f b kbar v k '' Icc 0 1))
    (isCompact_Icc.continuous_sSup (P.continuous_plannerG v.continuous)) (P.UB + b * ‖v‖)
    (fun k => by
      rw [Real.norm_eq_abs, abs_le]
      have hne : (plannerG U f b kbar v k '' Icc 0 1).Nonempty :=
        ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      constructor
      · exact (abs_le.1 (P.abs_plannerG_le v k 0)).1.trans
          (le_csSup (P.bddAbove_plannerG v k) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
      · exact csSup_le hne (by
          rintro _ ⟨s, -, rfl⟩
          exact (abs_le.1 (P.abs_plannerG_le v k s)).2))

/-- On `K`, the maximand over `s ∈ [0, 1]` has the same values as the maximand of (1) over
`y ∈ [0, f(k)]`. -/
theorem PlannerHyp.image_plannerG {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ → ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerG U f b kbar v k '' Icc 0 1 = (fun y => U (f k - y) + b * v y) '' Icc 0 (f k) := by
  have hf0 := P.f_nonneg k hk
  calc plannerG U f b kbar v k '' Icc 0 1
      = ((fun y => U (f k - y) + b * v y) ∘ fun s => s * f k) '' Icc 0 1 := by
        refine image_congr fun s hs => ?_
        have hc : f k - s * f k ∈ Icc 0 kbar := by
          constructor
          · nlinarith [hs.2]
          · nlinarith [hs.1, P.f_le k hk]
        simp only [plannerG, Function.comp, clampK_of_mem hk, clampK_of_mem hc]
    _ = (fun y => U (f k - y) + b * v y) '' ((fun s => s * f k) '' Icc 0 1) := image_comp _ _ _
    _ = (fun y => U (f k - y) + b * v y) '' Icc 0 (f k) := by
        rw [image_mul_right_Icc zero_le_one hf0, zero_mul, one_mul]

/-- On `K`, `(Tv)(k) = sup_{0 ≤ y ≤ f(k)} {U[f(k) − y] + b v(y)}`. -/
theorem PlannerHyp.plannerOp_apply {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerOp P v k = sSup ((fun y => U (f k - y) + b * v y) '' Icc 0 (f k)) := by
  rw [← P.image_plannerG v hk]
  rfl

/-- **`T` is a `b`-contraction** of `ℝ →ᵇ ℝ` (Theorem 4.6, with Blackwell's conditions replaced by
the direct estimate). -/
theorem PlannerHyp.plannerOp_contracting {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ContractingWith (Real.toNNReal b) (plannerOp P) := by
  refine ⟨Real.toNNReal_lt_one.2 P.b_lt_one, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [Real.coe_toNNReal _ P.b_nonneg]
  have hD : 0 ≤ b * dist v w := mul_nonneg P.b_nonneg dist_nonneg
  have key : ∀ (v w : ℝ →ᵇ ℝ) (k : ℝ), plannerOp P v k ≤ plannerOp P w k + b * dist v w := by
    intro v w k
    have hne : (plannerG U f b kbar v k '' Icc 0 1).Nonempty :=
      ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    change sSup (plannerG U f b kbar v k '' Icc 0 1) ≤
      sSup (plannerG U f b kbar w k '' Icc 0 1) + b * dist v w
    refine csSup_le hne ?_
    rintro _ ⟨s, hs, rfl⟩
    have h1 := le_csSup (P.bddAbove_plannerG w k) ⟨s, hs, rfl⟩
    have h2 : v (s * f (clampK kbar k)) ≤ w (s * f (clampK kbar k)) + dist v w := by
      have := (abs_le.1 (Real.dist_eq _ _ ▸ dist_coe_le_dist (f := v) (g := w)
        (s * f (clampK kbar k)))).2
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 P.b_nonneg
    have e : plannerG U f b kbar v k s = plannerG U f b kbar w k s +
        b * (v (s * f (clampK kbar k)) - w (s * f (clampK kbar k))) := by
      simp only [plannerG]
      ring
    rw [e]
    linarith
  refine (dist_le hD).2 fun k => ?_
  rw [Real.dist_eq, abs_le]
  constructor
  · have := key w v k
    rw [dist_comm] at this
    linarith
  · have := key v w k
    linarith

/-- **The planner's value function**: the fixed point of `T`. -/
noncomputable def plannerValue {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ℝ →ᵇ ℝ :=
  ContractingWith.fixedPoint (plannerOp P) P.plannerOp_contracting

/-- `Tv = v` for the planner's value function. -/
theorem PlannerHyp.plannerValue_fixed {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    plannerOp P (plannerValue P) = plannerValue P :=
  ContractingWith.fixedPoint_isFixedPt (f := plannerOp P) P.plannerOp_contracting

/-- **Existence for (1)** (Theorem 4.6): the planner's value function is continuous and bounded
and solves the functional equation (1) on `K`. -/
theorem PlannerHyp.plannerValue_solves {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    SolvesPlanner U f b kbar (plannerValue P) := by
  intro k hk
  rw [← P.plannerOp_apply _ hk, P.plannerValue_fixed]

/-- The maximand of (1) is continuous on `[0, f(k)]`. -/
theorem PlannerHyp.continuousOn_maximand {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hv : Continuous v) (k : ℝ) :
    ContinuousOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) := by
  refine ContinuousOn.add ?_ (continuous_const.mul hv).continuousOn
  refine P.U_cont.comp (continuous_const.sub continuous_id).continuousOn fun y hy => ?_
  exact mem_Ici.2 (sub_nonneg.2 hy.2)

/-- **The maximum is attained** on `[0, f(k)]` and equals `(Tv)(k)`. -/
theorem PlannerHyp.exists_max {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    ∃ y ∈ Icc 0 (f k), IsMaxOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) y ∧
      plannerOp P v k = U (f k - y) + b * v y := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, P.f_nonneg k hk⟩
    (P.continuousOn_maximand v.continuous k)
  refine ⟨y, hy, hmax, ?_⟩
  rw [P.plannerOp_apply v hk]
  exact IsGreatest.csSup_eq ⟨mem_image_of_mem _ hy, by rintro _ ⟨z, hz, rfl⟩; exact hmax hz⟩

/-- **`T` preserves concavity on `K`** (proof of Theorem 4.8). -/
theorem PlannerHyp.plannerOp_concave {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ →ᵇ ℝ} (hv : ConcaveOn ℝ (Icc 0 kbar) v) :
    ConcaveOn ℝ (Icc 0 kbar) (plannerOp P v) := by
  refine ⟨convex_Icc 0 kbar, fun k hk k' hk' a a' ha ha' haa => ?_⟩
  obtain ⟨y, hy, -, hTy⟩ := P.exists_max v hk
  obtain ⟨y', hy', -, hTy'⟩ := P.exists_max v hk'
  have hkθ : a • k + a' • k' ∈ Icc 0 kbar := (convex_Icc 0 kbar) hk hk' ha ha' haa
  have hfθ := P.f_concave.2 hk hk' ha ha' haa
  simp only [smul_eq_mul] at hfθ hkθ ⊢
  set kθ := a * k + a' * k' with hkθdef
  set yθ := a * y + a' * y' with hyθ
  have hyK : y ∈ Icc 0 kbar := ⟨hy.1, hy.2.trans (P.f_le k hk)⟩
  have hyK' : y' ∈ Icc 0 kbar := ⟨hy'.1, hy'.2.trans (P.f_le k' hk')⟩
  have hyθf : yθ ∈ Icc 0 (f kθ) := by
    constructor
    · have := hy.1
      have := hy'.1
      positivity
    · have h1 := mul_le_mul_of_nonneg_left hy.2 ha
      have h2 := mul_le_mul_of_nonneg_left hy'.2 ha'
      linarith
  have hc : 0 ≤ f k - y := by linarith [hy.2]
  have hc' : 0 ≤ f k' - y' := by linarith [hy'.2]
  have hcθ : a * (f k - y) + a' * (f k' - y') ≤ f kθ - yθ := by linarith
  have hcθ0 : 0 ≤ a * (f k - y) + a' * (f k' - y') := by positivity
  have hU1 : U (a * (f k - y) + a' * (f k' - y')) ≤ U (f kθ - yθ) :=
    P.U_mono (mem_Ici.2 hcθ0) (mem_Ici.2 (hcθ0.trans hcθ)) hcθ
  have hU2 := P.U_strictConcave.concaveOn.2 (mem_Ici.2 hc) (mem_Ici.2 hc') ha ha' haa
  have hv2 := hv.2 hyK hyK' ha ha' haa
  simp only [smul_eq_mul] at hU2 hv2
  have hv3 := mul_le_mul_of_nonneg_left hv2 P.b_nonneg
  have hle : U (f kθ - yθ) + b * v yθ ≤ plannerOp P v kθ := by
    rw [P.plannerOp_apply v hkθ]
    refine le_csSup ?_ ⟨yθ, hyθf, rfl⟩
    rw [← P.image_plannerG v hkθ]
    exact P.bddAbove_plannerG v kθ
  rw [hTy, hTy']
  nlinarith

/-- **The value function is concave on `K`** (Theorem 4.8). -/
theorem PlannerHyp.plannerValue_concave {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ConcaveOn ℝ (Icc 0 kbar) (plannerValue P) := by
  have hit : ∀ n : ℕ, ConcaveOn ℝ (Icc 0 kbar) ((plannerOp P)^[n] 0) := by
    intro n
    induction n with
    | zero => exact concaveOn_const 0 (convex_Icc 0 kbar)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact P.plannerOp_concave ih
  have hlim := P.plannerOp_contracting.tendsto_iterate_fixedPoint 0
  have hpt : ∀ x, Tendsto (fun n => ((plannerOp P)^[n] 0 : ℝ →ᵇ ℝ) x) atTop
      (𝓝 (plannerValue P x)) := fun x =>
    ((continuous_eval_const x).tendsto _).comp hlim
  refine ⟨convex_Icc 0 kbar, fun x hx y hy a a' ha ha' haa => ?_⟩
  exact le_of_tendsto_of_tendsto' (((hpt x).const_smul a).add ((hpt y).const_smul a'))
    (hpt (a • x + a' • y)) fun n => (hit n).2 hx hy ha ha' haa

/-- **Uniqueness of the maximiser** (Theorem 4.8): for `v` concave on `K`, two maximisers of
`U[f(k) − y] + b v(y)` on `[0, f(k)]` coincide (strict concavity of `U`). -/
theorem PlannerHyp.max_unique {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hv : ConcaveOn ℝ (Icc 0 kbar) v) {k : ℝ} (hk : k ∈ Icc 0 kbar) {y y' : ℝ}
    (hy : y ∈ Icc 0 (f k)) (hy' : y' ∈ Icc 0 (f k))
    (hmax : IsMaxOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) y)
    (hmax' : IsMaxOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) y') : y = y' := by
  by_contra hne
  have hm : (1 / 2 : ℝ) * y + (1 / 2) * y' ∈ Icc 0 (f k) :=
    ⟨by linarith [hy.1, hy'.1], by linarith [hy.2, hy'.2]⟩
  have hc : 0 ≤ f k - y := by linarith [hy.2]
  have hc' : 0 ≤ f k - y' := by linarith [hy'.2]
  have hcne : f k - y ≠ f k - y' := fun h => hne (by linarith)
  have hU := P.U_strictConcave.2 (mem_Ici.2 hc) (mem_Ici.2 hc') hcne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hyK : y ∈ Icc 0 kbar := ⟨hy.1, hy.2.trans (P.f_le k hk)⟩
  have hyK' : y' ∈ Icc 0 kbar := ⟨hy'.1, hy'.2.trans (P.f_le k hk)⟩
  have hv2 := hv.2 hyK hyK' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hU hv2
  have e : (1 / 2 : ℝ) * (f k - y) + 1 / 2 * (f k - y') = f k - (1 / 2 * y + 1 / 2 * y') := by
    ring
  rw [e] at hU
  have h1 : U (f k - y') + b * v y' ≤ U (f k - y) + b * v y := hmax hy'
  have h2 : U (f k - (1 / 2 * y + 1 / 2 * y')) + b * v (1 / 2 * y + 1 / 2 * y') ≤
      U (f k - y) + b * v y := hmax hm
  have h3 := mul_le_mul_of_nonneg_left hv2 P.b_nonneg
  have h4 : U (f k - y) + b * v y ≤ U (f k - y') + b * v y' := hmax' hy
  linarith

/-- **The planner's policy** `g(k)`: a maximiser in (1) (unique by `PlannerHyp.max_unique`). -/
noncomputable def plannerPolicy {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) (k : ℝ) :
    ℝ :=
  Classical.epsilon fun y => y ∈ Icc 0 (f k) ∧
    IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) y

/-- **The policy attains the maximum in (1)**: for `k ∈ K`, `g(k) ∈ [0, f(k)]` maximises
`U[f(k) − y] + b v(y)` there, and `v(k) = U[f(k) − g(k)] + b v(g(k))`. -/
theorem PlannerHyp.plannerPolicy_spec {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerPolicy P k ∈ Icc 0 (f k) ∧
      IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) (plannerPolicy P k) ∧
      plannerValue P k = U (f k - plannerPolicy P k) + b * plannerValue P (plannerPolicy P k) := by
  obtain ⟨y, hy, hmax, -⟩ := P.exists_max (plannerValue P) hk
  have hspec : plannerPolicy P k ∈ Icc 0 (f k) ∧
      IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) (plannerPolicy P k) :=
    Classical.epsilon_spec (p := fun y => y ∈ Icc 0 (f k) ∧
      IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) y) ⟨y, hy, hmax⟩
  refine ⟨hspec.1, hspec.2, ?_⟩
  obtain ⟨y₁, hy₁, hmax₁, hT⟩ := P.exists_max (plannerValue P) hk
  rw [P.plannerValue_fixed] at hT
  rw [hT, P.max_unique P.plannerValue_concave hk hy₁ hspec.1 hmax₁ hspec.2]

/-- **The policy is the unique maximiser** in (1): `y ∈ [0, f(k)]` attains the value `v(k)` iff
`y = g(k)`. -/
theorem PlannerHyp.plannerPolicy_unique {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) {y : ℝ} (hy : y ∈ Icc 0 (f k)) :
    U (f k - y) + b * plannerValue P y = plannerValue P k ↔ y = plannerPolicy P k := by
  obtain ⟨hg, hgmax, hgv⟩ := P.plannerPolicy_spec hk
  constructor
  · intro hyv
    refine P.max_unique P.plannerValue_concave hk hy hg (fun z hz => ?_) hgmax
    change U (f k - z) + b * plannerValue P z ≤ U (f k - y) + b * plannerValue P y
    rw [hyv, hgv]
    exact hgmax hz
  · rintro rfl
    exact hgv.symm

/-- The policy maps `K` into `K` with nonnegative consumption. -/
theorem PlannerHyp.plannerPolicy_mem {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerPolicy P k ∈ Icc 0 kbar ∧ 0 ≤ f k - plannerPolicy P k := by
  have h := (P.plannerPolicy_spec hk).1
  exact ⟨⟨h.1, h.2.trans (P.f_le k hk)⟩, by linarith [h.2]⟩

/-- **The policy is continuous on `K`** (Theorem 4.8; Theorem of the Maximum for a
single-valued policy). The graph of `g` on `K × K` is
`{(k, y) : y ≤ f(k), U[f(k) − y] + b v(y) = v(k)}` (by uniqueness of the maximiser), which is
closed; a map into the compact space `K` with closed graph is continuous. -/
theorem PlannerHyp.plannerPolicy_continuousOn {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) : ContinuousOn (plannerPolicy P) (Icc 0 kbar) := by
  set gK : Icc 0 kbar → Icc 0 kbar := fun k => ⟨plannerPolicy P k, (P.plannerPolicy_mem k.2).1⟩
    with hgK
  have hfK : Continuous fun k : Icc 0 kbar => f k :=
    P.f_cont.comp_continuous continuous_subtype_val fun k => k.2
  set S : Set (Icc 0 kbar × Icc 0 kbar) := {p | (p.2 : ℝ) ≤ f p.1 ∧
    U (clampK kbar (f p.1 - p.2)) + b * plannerValue P p.2 = plannerValue P p.1} with hS
  have hSc : IsClosed S := by
    refine IsClosed.inter (isClosed_le (continuous_subtype_val.comp continuous_snd)
      (hfK.comp continuous_fst)) (isClosed_eq ?_ ?_)
    · exact (P.continuous_U.comp ((hfK.comp continuous_fst).sub
        (continuous_subtype_val.comp continuous_snd))).add (continuous_const.mul
        ((plannerValue P).continuous.comp (continuous_subtype_val.comp continuous_snd)))
    · exact (plannerValue P).continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hgraph : Function.graph gK = S := by
    ext ⟨k, y⟩
    change gK k = y ↔ (y : ℝ) ≤ f k ∧
      U (clampK kbar (f k - y)) + b * plannerValue P y = plannerValue P k
    have hyc : ∀ hy : (y : ℝ) ≤ f k, clampK kbar (f k - y) = f k - y := fun hy =>
      clampK_of_mem ⟨by linarith, by linarith [y.2.1, P.f_le k k.2]⟩
    constructor
    · intro h
      have hy : (y : ℝ) = plannerPolicy P k := by rw [← h]
      obtain ⟨hg, -, hgv⟩ := P.plannerPolicy_spec k.2
      refine ⟨hy ▸ hg.2, ?_⟩
      rw [hyc (hy ▸ hg.2), hy, hgv]
    · rintro ⟨hy, hv⟩
      rw [hyc hy] at hv
      exact Subtype.ext ((P.plannerPolicy_unique k.2 ⟨y.2.1, hy⟩).1 hv).symm
  have hc : Continuous gK := continuous_of_isClosed_graph (hgraph ▸ hSc)
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hc

/-- **The envelope condition §18.1 (10)** (Benveniste–Scheinkman, Theorem 4.11). At
`k ∈ (0, k̄)` with positive consumption `f(k) − g(k) > 0`, `U` differentiable at `f(k) − g(k)`
and `f` differentiable at `k`, the planner's value function is differentiable at `k` with
`v′(k) = f′(k) U′[f(k) − g(k)]`. -/
theorem PlannerHyp.planner_envelope {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioo 0 kbar) (hc : plannerPolicy P k < f k)
    (hUd : DifferentiableAt ℝ U (f k - plannerPolicy P k)) (hfd : DifferentiableAt ℝ f k) :
    HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - plannerPolicy P k)) k := by
  have hkK : k ∈ Icc 0 kbar := Ioo_subset_Icc_self hk
  set y := plannerPolicy P k with hy
  obtain ⟨hyf, -, hv⟩ := P.plannerPolicy_spec hkK
  set Wf : ℝ → ℝ := fun z => U (f z - y) + b * plannerValue P y with hWf
  have hWd : HasDerivAt Wf (deriv f k * deriv U (f k - y)) k := by
    have := (hUd.hasDerivAt.comp k (hfd.hasDerivAt.sub_const y)).add_const
      (b * plannerValue P y)
    rw [mul_comm (deriv U _)] at this
    exact this
  have hle : ∀ᶠ z in 𝓝 k, Wf z ≤ plannerValue P z := by
    have hfc : ContinuousAt (fun z => f z - y) k := hfd.continuousAt.sub continuousAt_const
    filter_upwards [Ioo_mem_nhds hk.1 hk.2, hfc.eventually (Ioi_mem_nhds (sub_pos.2 hc))]
      with z hz hfz
    have hzK : z ∈ Icc 0 kbar := Ioo_subset_Icc_self hz
    have hyz : y ∈ Icc 0 (f z) := ⟨hyf.1, by have : 0 < f z - y := hfz; linarith⟩
    obtain ⟨y', hy', hmax, hT⟩ := P.exists_max (plannerValue P) hzK
    rw [P.plannerValue_fixed] at hT
    rw [hT]
    exact hmax hyz
  exact hasDerivAt_of_concave_of_le P.plannerValue_concave (Icc_mem_nhds hk.1 hk.2) hle hv.symm
    hWd

/-- **The first-order condition §18.1 (9).** At `k ∈ K` with an interior choice
`0 < g(k) < f(k)`, `U` differentiable at `f(k) − g(k)` and `v` differentiable at `g(k)`:
`U′[f(k) − g(k)] = b v′(g(k))`. -/
theorem PlannerHyp.planner_foc {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) (h0 : 0 < plannerPolicy P k) (h1 : plannerPolicy P k < f k)
    (hUd : DifferentiableAt ℝ U (f k - plannerPolicy P k))
    (hvd : DifferentiableAt ℝ (plannerValue P) (plannerPolicy P k)) :
    deriv U (f k - plannerPolicy P k) = b * deriv (plannerValue P) (plannerPolicy P k) := by
  set y := plannerPolicy P k with hy
  obtain ⟨-, hmax, -⟩ := P.plannerPolicy_spec hk
  have hloc : IsLocalMax (fun z => U (f k - z) + b * plannerValue P z) y := by
    filter_upwards [Ioo_mem_nhds h0 h1] with z hz
    exact hmax ⟨hz.1.le, hz.2.le⟩
  have hd1 : HasDerivAt (fun z => U (f k - z)) (deriv U (f k - y) * -1) y :=
    hUd.hasDerivAt.comp y ((hasDerivAt_id y).const_sub (f k))
  have hd := hd1.add (hvd.hasDerivAt.const_mul b)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **The planner's Euler equation**, from (9) and (10). Let `k ∈ K` with an interior choice
`0 < g(k) < f(k)` and positive consumption next period, `g(g(k)) < f(g(k))`; let `U` be
differentiable at both consumptions and `f` at `g(k)`. Then
`U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]`. -/
theorem PlannerHyp.planner_euler {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) (h0 : 0 < plannerPolicy P k) (h1 : plannerPolicy P k < f k)
    (h2 : plannerPolicy P (plannerPolicy P k) < f (plannerPolicy P k))
    (hUd1 : DifferentiableAt ℝ U (f k - plannerPolicy P k))
    (hUd2 : DifferentiableAt ℝ U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)))
    (hfd : DifferentiableAt ℝ f (plannerPolicy P k)) :
    deriv U (f k - plannerPolicy P k) = b * deriv f (plannerPolicy P k) *
      deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)) := by
  have hgI : plannerPolicy P k ∈ Ioo 0 kbar := ⟨h0, h1.trans_le (P.f_le k hk)⟩
  have henv := P.planner_envelope hgI h2 hUd2 hfd
  rw [P.planner_foc hk h0 h1 hUd1 henv.differentiableAt, henv.deriv]
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 18.1 and the indirect equilibrium with the planner constructed

SLP §18.1, pp. 543–546. `ex_18_1_full` and `indirect_equilibrium_full` (in `IndirectBellman`)
take the planner's policy `g` (resp. the pseudo-planner's `ĥ`) as an input satisfying the Euler
equation and the transversality condition. Here `g` and `ĥ` are the policies constructed in
`IndirectExistence` from the functional equations (1) and (8), and those hypotheses are
discharged, on `K = [0, k̄]`, for `U` bounded and `C¹`, `f` concave and `C¹` with `0 ≤ f ≤ k̄`
on `K`, and an interior policy (`0 < g(k) < f(k)` on `K`, as in SLP Theorem 4.11).

These assumptions are removed in `IndirectInterior`: under `InteriorHyp` (`U′(0+) = ∞` with `U`
bounded, `f(0) = 0`), `ex_18_1_interior` and `indirect_equilibrium_interior` prove interiority on
`(0, k̄]`, need `U` differentiable only on `(0, ∞)`, and need no continuity of `U′` or `f′`; the
example `U(c) = 1 − e^{−√c}`, `f(k) = √k` is in `IndirectInteriorExample`.

* `plannerHyp_of_differentiable`: the hypotheses `PlannerHyp` from differentiability of `U` with
  `U′ ≥ 0` and of `f`.
* `planner_euler_tvc`: the constructed policy satisfies the Euler equation everywhere on `K` and
  the transversality condition `bᵗ U′(c_t) f′(k_t) k_t → 0` (bounded paths), and also the
  individual's transversality condition with any discount factor in `[0, 1)`.
* **Exercise 18.1 with the planner constructed** (`ex_18_1_constructed`): the planner's value `v`
  solves (1), its policy `g` is continuous and the unique maximiser, `g` satisfies the Euler
  equation; the bounded solution `V` of (2) exists and is unique, `V(k, k; g) = v(k)`, which is
  the maximal value of the planner's sequence problem; `G(k, k; g) = g(k)`; and
  `V₁(k, k; g) = v′(k)` on `(0, k̄)`.
* **The indirect equilibrium with the pseudo-planner constructed**
  (`indirect_equilibrium_constructed`, p. 546): `w` solves (8) and is the value of `ĥ` in the
  pseudo-economy, (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `K` and (10)
  `w′(k) = f′(k) U′[f(k) − ĥ(k)]` on `(0, k̄)` hold, the bounded solution `W` of (3) exists and is
  unique, `H(k, k; ĥ) = ĥ(k)` (a recursive competitive equilibrium), and the book's identification
  `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` holds on `(0, k̄)`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set

/-- **`PlannerHyp` from differentiability.** If `0 ≤ b < 1`, `0 ≤ k̄`, `U` is strictly concave and
differentiable on `[0, ∞)` with `U′ ≥ 0`, and `f` is concave on `[0, ∞)`, differentiable on
`K = [0, k̄]` with `0 ≤ f ≤ k̄` there, then `PlannerHyp U f b k̄` holds. -/
theorem plannerHyp_of_differentiable {U f : ℝ → ℝ} {b kbar : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hkbar : 0 ≤ kbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k)
    (hf0 : ∀ k ∈ Icc 0 kbar, 0 ≤ f k) (hfle : ∀ k ∈ Icc 0 kbar, f k ≤ kbar) :
    PlannerHyp U f b kbar where
  b_nonneg := hb0
  b_lt_one := hb1
  kbar_nonneg := hkbar
  U_cont := fun c hc => (hUd c hc).continuousAt.continuousWithinAt
  U_mono := monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun c hc => (hUd c hc).continuousAt.continuousWithinAt)
      (fun c hc => (hUd c (interior_subset hc)).differentiableWithinAt)
      fun c hc => hU' c (interior_subset hc)
  U_strictConcave := hU
  f_cont := fun k hk => (hfd k hk).continuousAt.continuousWithinAt
  f_concave := hf.subset Icc_subset_Ici_self (convex_Icc 0 kbar)
  f_nonneg := hf0
  f_le := hfle

/-- **Euler equation and transversality for the constructed policy.** Let `P : PlannerHyp U f b k̄`,
`U` differentiable on `[0, ∞)` with `U′` continuous on `[0, k̄]`, `f` differentiable on `K` with
`f′` continuous on `K`, and let the policy `g` be interior on `K` (`0 < g(k) < f(k)`). Then for
every `k ∈ K`: the Euler equation `U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]` holds, and
for every `β' ∈ [0, 1)` and constant `a`, `β'ᵗ (a f′(k_t)) U′(c_t) k_t → 0` along `k_t = gᵗ(k)`.
Without interiority or continuity of `U′`, `f′`: `InteriorHyp.planner_euler_interior` and
`InteriorHyp.planner_tvc` on `(0, k̄]`. -/
theorem PlannerHyp.planner_euler_tvc {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hUc' : ContinuousOn (deriv U) (Icc 0 kbar))
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hfc' : ContinuousOn (deriv f) (Icc 0 kbar))
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k) :
    (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) = b * deriv f (plannerPolicy P k) *
      deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k))) ∧
    ∀ β' a : ℝ, 0 ≤ β' → β' < 1 → ∀ k ∈ Icc 0 kbar,
      Tendsto (fun t => β' ^ t * (a * deriv f ((plannerPolicy P)^[t] k)) *
        deriv U (f ((plannerPolicy P)^[t] k) - plannerPolicy P ((plannerPolicy P)^[t] k)) *
          (plannerPolicy P)^[t] k) atTop (𝓝 0) := by
  set g := plannerPolicy P with hg
  have hgK : ∀ k ∈ Icc 0 kbar, g k ∈ Icc 0 kbar := fun k hk => (P.plannerPolicy_mem hk).1
  refine ⟨fun k hk => ?_, fun β' a hβ0 hβ1 k hk => ?_⟩
  · have hgk := hgK k hk
    exact P.planner_euler hk (hint k hk).1 (hint k hk).2 (hint _ hgk).2
      (hUd _ (sub_pos.2 (hint k hk).2).le) (hUd _ (sub_pos.2 (hint _ hgk).2).le) (hfd _ hgk)
  · obtain ⟨MU, hMU⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc'
    obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc'
    have hkt := iterate_mem hgK hk
    refine (tvc_of_bounded (M := |a| * Mf * MU * kbar) hβ0 hβ1 (z := fun t =>
      a * deriv f (g^[t] k) * deriv U (f (g^[t] k) - g (g^[t] k)) * g^[t] k)
      fun t => ?_).congr fun t => by ring
    have hk' := hkt t
    have hc : f (g^[t] k) - g (g^[t] k) ∈ Icc 0 kbar :=
      ⟨(P.plannerPolicy_mem hk').2, by linarith [(hgK _ hk').1, P.f_le _ hk']⟩
    have h1 := hMf _ hk'
    have h2 := hMU _ hc
    rw [Real.norm_eq_abs] at h1 h2
    have h3 : |g^[t] k| ≤ kbar := by rw [abs_of_nonneg hk'.1]; exact hk'.2
    simp only [abs_mul]
    have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans h1
    have hMU0 : 0 ≤ MU := (abs_nonneg _).trans h2
    gcongr

/-- **Exercise 18.1 with the planner constructed** (pp. 543–544). Let `0 < β < 1`, `0 ≤ k̄`;
`U` strictly concave, differentiable with `U′ ≥ 0` and bounded by `B₀` on `[0, ∞)`, with `U′`
continuous on `[0, k̄]`; `f` concave on `[0, ∞)`, differentiable on `K = [0, k̄]` with `f′ ≥ 0`
and `f′` continuous there, and `0 ≤ f ≤ k̄` on `K`. Let `v = plannerValue P` and
`g = plannerPolicy P` be the solution of the planner's functional equation (1) constructed in
`IndirectExistence`, and suppose `g` is interior on `K`. Then:
(i) `v` solves (1) on `K`, `g` is continuous on `K` and is the unique maximiser in (1);
(ii) `g` satisfies the planner's Euler equation on `K`;
(iii) the individual's functional equation (2) has a bounded solution `V`, unique among bounded
solutions, with `V(k, k; g) = v(k)`, the maximal value of the planner's sequence problem, and
`G(k, k; g) = g(k)` the unique optimal choice at `(k, k)`;
(iv) on `(0, k̄)`, `V₁(k, k; g) = v′(k) = f′(k) U′[f(k) − g(k)]`.
Interiority is proved, on `(0, k̄]`, under `InteriorHyp` in `ex_18_1_interior`. -/
theorem ex_18_1_constructed {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (P : PlannerHyp U f β kbar)
    (hβ0 : 0 < β) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hUc' : ContinuousOn (deriv U) (Icc 0 kbar)) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k)
    (hfc' : ContinuousOn (deriv f) (Icc 0 kbar))
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k) :
    SolvesPlanner U f β kbar (plannerValue P) ∧
      ContinuousOn (plannerPolicy P) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy P k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue P y = plannerValue P k ↔ y = plannerPolicy P k) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) =
        β * deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)) *
          deriv f (plannerPolicy P k)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy P) V β
          (Icc 0 kbar) ∧
        (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V' x k| ≤ M') →
          SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy P) V' β
            (Icc 0 kbar) → ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, V' x k = V x k) ∧
        (∀ k ∈ Icc 0 kbar, V k k = plannerValue P k ∧
          IsGreatest (plannerValues U f β k) (V k k) ∧
          ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
            (U (f k + (k - k) * deriv f k - y) + β * V y (plannerPolicy P k) = V k k ↔
              y = plannerPolicy P k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => V x k) (deriv (plannerValue P) k) k ∧
          HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - plannerPolicy P k)) k := by
  set g := plannerPolicy P with hg
  set K := Icc 0 kbar with hKdef
  have hgK : ∀ k ∈ K, g k ∈ K := fun k hk => (P.plannerPolicy_mem hk).1
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1
  have hc : ∀ k ∈ K, 0 ≤ f k - g k := fun k hk => (P.plannerPolicy_mem hk).2
  have hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k := by
    intro k hk
    have h0K : (0 : ℝ) ∈ K := ⟨le_rfl, P.kbar_nonneg⟩
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1 (hfd k hk)
    have := P.f_nonneg 0 h0K
    nlinarith
  obtain ⟨heul, htvc⟩ := P.planner_euler_tvc hUd hUc' hfd hfc' hint
  have heul' : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k) := fun k hk => by
    rw [heul k hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0) := fun k hk =>
    (htvc β 1 hβ0.le P.b_lt_one k hk).congr fun t => by ring
  obtain ⟨V, M, hVb, hsol, huniq, hall⟩ := ex_18_1_full P.U_strictConcave hβ0 P.b_lt_one hUd hU'
    hUb hf hgK hK0 hfd hf' hw hc heul' htvc'
  have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
    rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
  have hpol : ∀ k ∈ K, plannerValue P k = U (f k - g k) + β * plannerValue P (g k) :=
    fun k hk => (P.plannerPolicy_spec hk).2.2
  have hdp := ex_18_1_dp P.U_strictConcave hβ0 P.b_lt_one hUd hU' hUb hgK hK0 hf' hw hc heul'
    htvc' hvb hpol hVb hsol
  refine ⟨P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨(P.plannerPolicy_spec hk).1, fun y hy => P.plannerPolicy_unique hk hy⟩, heul',
    V, M, hVb, hsol, huniq, fun k hk => ⟨(hdp k hk).1, (hall k hk).1, (hall k hk).2⟩,
    fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Icc_self hk
  have hv' := P.planner_envelope hk (hint k hkK).2 (hUd _ (hc k hkK)) (hfd k hkK)
  refine ⟨?_, hv'⟩
  rw [hv'.deriv]
  have hopt := ((hall k hkK).2 (g k) ⟨(hgK k hkK).1, by have := hc k hkK; simp only; linarith⟩).2
    rfl
  have e : (fun k => f k - k * deriv f k) k + deriv f k * k - g k = f k - g k := by
    simp only; ring
  have e' : f k + (k - k) * deriv f k - g k = f k - g k := by ring
  rw [e'] at hopt
  have := bellman_envelope hβ0.le P.b_lt_one P.U_strictConcave.concaveOn hUb hVb hgK hw hf' hsol
    hk.1 hkK (hgK k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) (by rw [e]; exact hopt)
    (by rw [e]; exact (hUd _ (hc k hkK)).hasDerivAt)
  exact this

/-- **The indirect equilibrium with the pseudo-planner constructed** (p. 546). Tax `θ ∈ [0, 1)`
on capital income, rebated; `0 < β < 1`. With the hypotheses of `ex_18_1_constructed` on `U`
and `f`, let `w = plannerValue P` and `ĥ = plannerPolicy P` solve the pseudo-economy's functional
equation (8) with discount factor `β̂ = (1 − θ)β`, and let `ĥ` be interior on `K`. Then:
(i) `w` solves (8) on `K`, `ĥ` is continuous on `K`, and `w(k)` is the value of the path of `ĥ`
in the pseudo-economy, which is the maximal value of the pseudo-planner's sequence problem;
(ii) (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `K` and (10) `w′(k) = f′(k) U′[f(k) − ĥ(k)]` on
`(0, k̄)`;
(iii) the functional equation (3) with `h = ĥ` has a bounded solution `W`, unique among bounded
solutions, `W(k, k; ĥ)` is the individual's value of following `ĥ`, and `H(k, k; ĥ) = ĥ(k)` is
the unique optimal choice at `(k, k)` (a recursive competitive equilibrium);
(iv) `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` on `(0, k̄)`, the book's identification.
Interiority is proved, on `(0, k̄]`, under `InteriorHyp` in `indirect_equilibrium_interior`. -/
theorem indirect_equilibrium_constructed {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (P : PlannerHyp U f ((1 - θ) * β) kbar) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hUc' : ContinuousOn (deriv U) (Icc 0 kbar)) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k)
    (hfc' : ContinuousOn (deriv f) (Icc 0 kbar))
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k) :
    SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue P) ∧
      ContinuousOn (plannerPolicy P) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerValue P k = pathValue U f (plannerPolicy P) ((1 - θ) * β) k ∧
        IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue P k)) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) =
        (1 - θ) * β * deriv (plannerValue P) (plannerPolicy P k)) ∧
      (∀ k ∈ Ioo 0 kbar,
        HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - plannerPolicy P k)) k) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy P) W β (Icc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy P) W' β (Icc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Icc 0 kbar, W k k = pathValue U f (plannerPolicy P) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy P k) = W k k ↔
              y = plannerPolicy P k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue P) k) k := by
  set h := plannerPolicy P with hh
  set K := Icc 0 kbar with hKdef
  have hhK : ∀ k ∈ K, h k ∈ K := fun k hk => (P.plannerPolicy_mem hk).1
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1
  have hc : ∀ k ∈ K, 0 ≤ f k - h k := fun k hk => (P.plannerPolicy_mem hk).2
  have hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k := by
    intro k hk
    have h0K : (0 : ℝ) ∈ K := ⟨le_rfl, P.kbar_nonneg⟩
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1 (hfd k hk)
    have := P.f_nonneg 0 h0K
    have := mul_nonneg (mul_nonneg hθ0 hk.1) (hf' k hk)
    nlinarith
  obtain ⟨heul, htvc⟩ := P.planner_euler_tvc hUd hUc' hfd hfc' hint
  have heul' : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k) := fun k hk => by
    rw [heul k hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0) := fun k hk =>
    htvc β (1 - θ) hβ0.le hβ1 k hk
  obtain ⟨W, M, hWb, hsol, huniq, hall⟩ := indirect_equilibrium_full P.U_strictConcave hβ0 hβ1
    hθ0 hθ hUd hU' hUb hf hhK hK0 hfd hf' hw hc heul' htvc'
  -- the envelope condition (10) for `w`
  have h10 : ∀ k ∈ Ioo 0 kbar,
      HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - h k)) k := fun k hk =>
    P.planner_envelope hk (hint k (Ioo_subset_Icc_self hk)).2
      (hUd _ (hc k (Ioo_subset_Icc_self hk))) (hfd k (Ioo_subset_Icc_self hk))
  -- the first-order condition (9)
  have h9 : ∀ k ∈ K, deriv U (f k - h k) = (1 - θ) * β * deriv (plannerValue P) (h k) := by
    intro k hk
    have hhI : h k ∈ Ioo 0 kbar := ⟨(hint k hk).1, (hint k hk).2.trans_le (P.f_le k hk)⟩
    exact P.planner_foc hk (hint k hk).1 (hint k hk).2 (hUd _ (hc k hk))
      (h10 _ hhI).differentiableAt
  -- `w` is the value of the path of `ĥ`
  have hval : ∀ k ∈ K, plannerValue P k = pathValue U f h ((1 - θ) * β) k := by
    intro k hk
    have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
      rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
    have hs := policyValue_hasSum P.b_nonneg P.b_lt_one hhK hvb (fun k hk => hUb _ (hc k hk))
      (fun k hk => (P.plannerPolicy_spec hk).2.2) hk
    exact hs.tsum_eq.symm
  refine ⟨P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨hval k hk, (hval k hk) ▸ (hall k hk).1⟩, h9, h10, W, M, hWb, hsol, huniq,
    fun k hk => ⟨(hall k hk).2.1, (hall k hk).2.2⟩, fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Icc_self hk
  have hopt := ((hall k hkK).2.2 (h k) ⟨(hhK k hkK).1, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : f k + (1 - θ) * (k - k) * deriv f k - h k = f k - h k := by ring
  obtain ⟨h5, -⟩ := eq_18_1_4_5 hβ0.le hβ1 hθ P.U_strictConcave.concaveOn hUb hhK hf' hw hWb hsol
    hk.1 hkK (hint k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) hopt
    (by rw [e]; exact hUd _ (hc k hkK))
  rw [(h10 k hk).deriv]
  rw [e] at h5
  convert h5 using 1
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 18.1 and the taxed economy with `U` differentiable only along the path

SLP §18.1, pp. 543–546. `dp_diagonal`, `ex_18_1_dp`, `indirect_equilibrium_dp`,
`planner_optimal`, `ex_18_1_full` and `indirect_equilibrium_full` assume that `U` is
differentiable with `U′ ≥ 0` at every `c ≥ 0`. Their proofs use the derivative only at the
consumptions `F(k) − g(k)`, `k ∈ K`, of the aggregate path. Here the same results are proved under
that pointwise hypothesis, with monotonicity of `U` assumed directly. This admits utilities with
`U′(0+) = ∞`, such as `U(c) = 1 − e^{−√c}`, which are not differentiable at `0`; these are the
utilities for which `IndirectInterior` proves the planner's policy interior.

* `dp_diagonal_pathwise`: `dp_diagonal` with `U` differentiable, `U′ ≥ 0`, at `F(k) − g(k)`,
  `k ∈ K`, only.
* `ex_18_1_dp_pathwise`, `indirect_equilibrium_dp_pathwise`: likewise for `ex_18_1_dp` and
  `indirect_equilibrium_dp` (pp. 544, 546).
* `planner_optimal_pathwise`: `planner_optimal` with `U` monotone, and differentiable with
  `U′ ≥ 0` along the planner's path only (Theorem 4.15 for (1)).
* `ex_18_1_full_pathwise`, `indirect_equilibrium_full_pathwise`: `ex_18_1_full` and
  `indirect_equilibrium_full` under the same weakening.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- **The diagonal of the functional equation, `U` differentiable along the path only.** As
`dp_diagonal`, with `U` differentiable and `U′ ≥ 0` only at the consumptions `F(k) − g(k)`,
`k ∈ K`: then `W(k, k) = v(k)`, `g(k) ∈ Γ(k, k)` attains the supremum at `(k, k)`, and it is the
only `y ∈ Γ(k, k)` that does. -/
theorem dp_diagonal_pathwise {U A B Fk g v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ}
    {K : Set ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (Fk k - g k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (Fk k - g k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hAB : ∀ k ∈ K, A k + B k * k = Fk k)
    (hc : ∀ k ∈ K, 0 ≤ Fk k - g k)
    (heul : ∀ k ∈ K, deriv U (Fk k - g k) =
      β * B (g k) * deriv U (Fk (g k) - g (g k)))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * B (g^[t] k) *
      deriv U (Fk (g^[t] k) - g (g^[t] k)) * g^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (Fk k - g k) + β * v (g k))
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hsol : SolvesBellman U A B g W β K) :
    ∀ k ∈ K, W k k = v k ∧ g k ∈ feasY A B k k ∧
      U (A k + B k * k - g k) + β * W (g k) (g k) = W k k ∧
      ∀ y ∈ feasY A B k k, U (A k + B k * k - y) + β * W y (g k) = W k k → y = g k := by
  -- the diagonal value
  have hdiag : ∀ k ∈ K, W k k = v k ∧
      IsGreatest (indivValues U β (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k) (v k) ∧
      ∀ x S, IndivFeasible (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k x →
        HasSum (fun t => β ^ t * U (consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k))
          x t)) S → ∀ t₀ : ℕ, S ≤ v k - β ^ t₀ * (U (Fk (g^[t₀] k) - g (g^[t₀] k)) +
            deriv U (Fk (g^[t₀] k) - g (g^[t₀] k)) * (consPath (fun t => A (g^[t] k))
              (fun t => B (g^[t] k)) x t₀ - (Fk (g^[t₀] k) - g (g^[t₀] k))) -
            U (consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x t₀)) := by
    intro k hk
    have hkt := iterate_mem hK hk
    set a : ℕ → ℝ := fun t => A (g^[t] k) with ha
    set b : ℕ → ℝ := fun t => B (g^[t] k) with hb
    set xs : ℕ → ℝ := fun t => g^[t] k with hxs
    have hcons : ∀ t, consPath a b xs t = Fk (g^[t] k) - g (g^[t] k) := fun t => by
      simp only [consPath, ha, hb, hxs, Function.iterate_succ_apply']
      rw [← hAB _ (hkt t)]
    have hcs : ∀ t, 0 ≤ consPath a b xs t := fun t => (hcons t).symm ▸ hc _ (hkt t)
    have hfeas : IndivFeasible a b (xs 0) xs := ⟨rfl, fun t => ⟨hK0 _ (hkt t), hcs t⟩⟩
    have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b xs t) := fun t => by
      rw [hcons]; exact hUd _ (hkt t)
    have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t) := fun t => by
      rw [hcons]; exact mul_nonneg (hB _ (hkt t)) (hU' _ (hkt t))
    have heul' : ∀ t, deriv U (consPath a b xs t) =
        β * b (t + 1) * deriv U (consPath a b xs (t + 1)) := fun t => by
      rw [hcons, hcons, heul _ (hkt t)]
      simp only [hb, Function.iterate_succ_apply']
    have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop
        (𝓝 0) := by
      refine (htvc k hk).congr fun t => ?_
      rw [hcons]
    have hv' : HasSum (fun t => β ^ t * U (consPath a b xs t)) (v k) := by
      have := policyValue_hasSum hβ0.le hβ1 hK hv (fun k hk => hUb _ (hc k hk)) hpol hk
      simpa only [hcons] using this
    have hG := euler_tvc_isGreatest hU.concaveOn hβ0.le hUd' hp heul' htvc' hfeas hv'
    have hL := bellman_isLUB hβ0.le hβ1 hUb hW hK hA hB hsol (hK0 k hk) hk
    refine ⟨hL.unique hG.isLUB, hG, fun x S hx hS t₀ => ?_⟩
    have := euler_tvc_gap hU.concaveOn hβ0.le hUd' hcs hp heul' htvc' hx hS hv' t₀
    rwa [hcons t₀] at this
  intro k hk
  obtain ⟨hWk, -, hgap⟩ := hdiag k hk
  have hgk := hK k hk
  have hAk : A k + B k * k - g k = Fk k - g k := by rw [hAB k hk]
  refine ⟨hWk, ⟨hK0 _ hgk, by rw [hAk]; exact hc k hk⟩, ?_, fun y hy hyW => ?_⟩
  · rw [hAk, (hdiag _ hgk).1, hWk, hpol k hk]
  · by_contra hne
    set cy := A k + B k * k - y with hcy
    set cs := Fk k - g k with hcs
    have hcne : cy ≠ cs := by
      intro h
      apply hne
      rw [hcy, hcs, ← hAB k hk] at h
      linarith
    set r0 := U cs + deriv U cs * (cy - cs) - U cy with hr0
    have hr0p : 0 < r0 := by
      have := strictConcave_lt_tangent hU hy.2 (hc k hk) hcne (hUd k hk)
      rw [hr0]
      linarith
    -- every continuation from `(y, g(k))` gives at most `v(k) − r₀`
    have hub : W y (g k) ≤ (v k - r0 - U cy) / β := by
      refine (bellman_isLUB hβ0.le hβ1 hUb hW hK hA hB hsol hy.1 hgk).2 ?_
      rintro S' ⟨x', hx', hS'⟩
      rw [le_div_iff₀ hβ0]
      set x : ℕ → ℝ := fun t => Nat.casesOn t k fun t => x' t with hxdef
      have hx0 : x 0 = k := rfl
      have hxs : ∀ t, x (t + 1) = x' t := fun t => rfl
      have hit : ∀ t : ℕ, g^[t + 1] k = g^[t] (g k) := fun t => Function.iterate_succ_apply _ _ _
      have hc0 : consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x 0 = cy := by
        simp only [consPath, hx0, hxs, hx'.1, Function.iterate_zero, id, hcy]
      have hcsucc : ∀ t, consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x (t + 1) =
          consPath (fun t => A (g^[t] (g k))) (fun t => B (g^[t] (g k))) x' t := fun t => by
        simp only [consPath, hxs, hit]
      have hfeas : IndivFeasible (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k x := by
        refine ⟨hx0, fun t => ?_⟩
        rcases t with _ | t
        · exact ⟨hK0 k hk, hc0 ▸ hy.2⟩
        · rw [hcsucc t]
          exact ⟨(hx'.2 t).1, (hx'.2 t).2⟩
      have hsum : HasSum (fun t => β ^ t * U (consPath (fun t => A (g^[t] k))
          (fun t => B (g^[t] k)) x t)) (U cy + β * S') := by
        refine (hasSum_nat_add_iff' 1).1 ?_
        have e : (U cy + β * S') - ∑ i ∈ range 1, β ^ i * U (consPath (fun t => A (g^[t] k))
            (fun t => B (g^[t] k)) x i) = β * S' := by
          simp [hc0]
        rw [e]
        refine (hS'.mul_left β).congr_fun fun t => ?_
        simp only [hcsucc t, pow_succ]
        ring
      have h := hgap x _ hfeas hsum 0
      simp only [pow_zero, one_mul, Function.iterate_zero, id, hc0] at h
      linarith
    have h1 : U cy + β * W y (g k) ≤ v k - r0 := by
      have := mul_le_mul_of_nonneg_left hub hβ0.le
      rw [mul_div_cancel₀ _ hβ0.ne'] at this
      linarith
    rw [hyW, hWk] at h1
    linarith

/-- **Exercise 18.1, literally, `U` differentiable along the path only** (p. 544). As
`ex_18_1_dp`, with `U` differentiable and `U′ ≥ 0` only at `f(k) − g(k)`, `k ∈ K`: for a bounded
solution `V` of (2), `V(k, k; g) = v(k)` and `g(k)` is the unique optimal choice at `(k, k)`. -/
theorem ex_18_1_dp_pathwise {U f g v : ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - g k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (f k - g k) + β * v (g k))
    (hV : ∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K) :
    ∀ k ∈ K, V k k = v k ∧
      (∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
        U (f k + (k - k) * deriv f k - y) + β * V y (g k) = V k k ↔ y = g k) := by
  have hD := dp_diagonal_pathwise (A := fun k => f k - k * deriv f k) (B := deriv f) (Fk := f)
    hU hβ0 hβ1 hUd hU' hUb hK hK0 hw hf' (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring)
    (fun k hk => (htvc k hk).congr fun t => by ring) hv hpol hV hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (k - k) * deriv f k - y = f k - k * deriv f k + deriv f k * k - y :=
    fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyV => h4 y hy (by rw [← e]; exact hyV), fun hyg => ?_⟩⟩
  rw [hyg, e]
  exact h3

/-- **The indirect method gives a recursive competitive equilibrium, `U` differentiable along
the path only** (pp. 545–546). As `indirect_equilibrium_dp`, with `U` differentiable and
`U′ ≥ 0` only at `f(k) − ĥ(k)`, `k ∈ K`: for a bounded solution `W` of (3) with `h = ĥ`,
`W(k, k; ĥ) = v(k)` and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice at `(k, k)`. -/
theorem indirect_equilibrium_dp_pathwise {U f h v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M Mv : ℝ}
    {K : Set ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ < 1)
    (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - h k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (f k - h k) + β * v (h k))
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K) :
    ∀ k ∈ K, W k k = v k ∧
      ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
        (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (h k) = W k k ↔ y = h k) := by
  have hD := dp_diagonal_pathwise (A := fun k => f k - (1 - θ) * k * deriv f k)
    (B := fun k => (1 - θ) * deriv f k) (Fk := f) hU hβ0 hβ1 hUd hU' hUb hK hK0 hw
    (fun k hk => mul_nonneg (by linarith) (hf' k hk)) (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring) htvc hv hpol hW hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (1 - θ) * (k - k) * deriv f k - y =
      f k - (1 - θ) * k * deriv f k + (1 - θ) * deriv f k * k - y := fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyW => h4 y hy (by rw [← e]; exact hyW), fun hyh => ?_⟩⟩
  rw [hyh, e]
  exact h3

/-- **Sufficiency of Euler + transversality for the planner, `U` differentiable along the path
only** (Theorem 4.15 for §18.1 (1)). As `planner_optimal`, with `U` concave, nondecreasing and
bounded on `[0, ∞)`, and differentiable with `U′ ≥ 0` only at the path's consumptions
`f(ks_t) − ks_{t+1}`. Then the path's value is the greatest value of the planner's problem. -/
theorem planner_optimal_pathwise {U f : ℝ → ℝ} {β B₀ : ℝ} {ks : ℕ → ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hUd : ∀ t, DifferentiableAt ℝ U (f (ks t) - ks (t + 1)))
    (hU' : ∀ t, 0 ≤ deriv U (f (ks t) - ks (t + 1))) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ t, DifferentiableAt ℝ f (ks t)) (hf' : ∀ t, 0 ≤ deriv f (ks t))
    (hks : ∀ t, 0 ≤ ks t) (hc : ∀ t, 0 ≤ f (ks t) - ks (t + 1))
    (heul : ∀ t, deriv U (f (ks t) - ks (t + 1)) =
      β * deriv U (f (ks (t + 1)) - ks (t + 2)) * deriv f (ks (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * deriv U (f (ks t) - ks (t + 1)) * deriv f (ks t) * ks t)
      atTop (𝓝 0)) :
    IsGreatest (plannerValues U f β (ks 0)) (∑' t, β ^ t * U (f (ks t) - ks (t + 1))) := by
  have hsumb : ∀ c : ℕ → ℝ, (∀ t, 0 ≤ c t) → Summable fun t => β ^ t * U (c t) := by
    intro c hc0
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hUb _ (hc0 t)) (pow_nonneg hβ0 t)
  have hS' := (hsumb _ hc).hasSum
  refine ⟨⟨ks, rfl, fun t => ⟨hks t, hc t⟩, hS'⟩, ?_⟩
  rintro S ⟨k, hk0, hk, hS⟩
  set a : ℕ → ℝ := fun t => f (ks t) - ks t * deriv f (ks t) with ha
  set b : ℕ → ℝ := fun t => deriv f (ks t) with hb
  have hcons : ∀ t, consPath a b ks t = f (ks t) - ks (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  have htan : ∀ t, f (k t) - k (t + 1) ≤ consPath a b k t := fun t => by
    have := concave_le_tangent hf (hk t).1 (hks t) (hfd t)
    simp only [consPath, ha, hb]
    linarith
  have hfeas : IndivFeasible a b (ks 0) k :=
    ⟨hk0, fun t => ⟨(hk t).1, ((hk t).2).trans (htan t)⟩⟩
  have hS2 := (hsumb _ fun t => (hfeas.2 t).2).hasSum
  have hle1 : S ≤ ∑' t, β ^ t * U (consPath a b k t) :=
    hasSum_le (fun t => mul_le_mul_of_nonneg_left (hUm (mem_Ici.2 (hk t).2)
      (mem_Ici.2 (hfeas.2 t).2) (htan t)) (pow_nonneg hβ0 t)) hS hS2
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b ks t) := fun t => by
    rw [hcons]; exact hUd t
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b ks t) := fun t => by
    rw [hcons]; exact mul_nonneg (hf' t) (hU' t)
  have heul' : ∀ t, deriv U (consPath a b ks t) =
      β * b (t + 1) * deriv U (consPath a b ks (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b ks T) * ks T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
    ring
  have hv' : HasSum (fun t => β ^ t * U (consPath a b ks t))
      (∑' t, β ^ t * U (f (ks t) - ks (t + 1))) := by
    simpa only [hcons] using hS'
  exact hle1.trans (euler_tvc_optimal hU hβ0 hUd' (fun t => (hcons t).symm ▸ hc t) hp heul'
    htvc' hfeas hS2 hv')

/-- **Exercise 18.1, complete, `U` differentiable along the path only** (p. 544). As
`ex_18_1_full`, with `U` strictly concave, nondecreasing and bounded on `[0, ∞)`, and
differentiable with `U′ ≥ 0` only at the consumptions `f(k) − g(k)`, `k ∈ K`. Then (2) has a
bounded solution `V` on `[0, ∞) × K`, unique among bounded solutions; `V(k, k; g)` is the maximal
value of the planner's problem from `k ∈ K`; and `G(k, k; g) = g(k)`. -/
theorem ex_18_1_full_pathwise {U f g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - g k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k) (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0)) :
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K ∧
      (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ K, |V' x k| ≤ M') →
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V' β K →
          ∀ x, 0 ≤ x → ∀ k ∈ K, V' x k = V x k) ∧
      ∀ k ∈ K, IsGreatest (plannerValues U f β k) (V k k) ∧
        ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
          (U (f k + (k - k) * deriv f k - y) + β * V y (g k) = V k k ↔ y = g k) := by
  obtain ⟨V, M, hVb, hsol⟩ := exists_bellman_solution (U := U) (g := g)
    (A := fun k => f k - k * deriv f k) (B := deriv f) hβ0.le hβ1 hUb hK hw hf'
  obtain ⟨hvb, hpol⟩ := pathValue_spec (Fk := f) hβ0.le hβ1 hUb hK hc
  refine ⟨V, M, hVb, hsol, fun V' M' hV' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hV' hVb hK hw hf' hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := ex_18_1_dp_pathwise hU hβ0 hβ1 hUd hU' hUb hK hK0 hf' hw hc heul htvc hvb
    hpol hVb hsol k hk
  refine ⟨?_, h4⟩
  have hkt := iterate_mem hK hk
  have hP := planner_optimal_pathwise (ks := fun t => g^[t] k) hU.concaveOn hUm hβ0.le hβ1 hUb
    (fun t => by simp only [Function.iterate_succ_apply']; exact hUd _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hU' _ (hkt t))
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      exact heul _ (hkt t))
    (by simpa only [Function.iterate_succ_apply'] using htvc k hk)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  rw [h1]
  exact hP

/-- **The taxed economy (3), complete, `U` differentiable along the path only** (pp. 545–546).
As `indirect_equilibrium_full`, with `U` strictly concave, nondecreasing and bounded on
`[0, ∞)`, and differentiable with `U′ ≥ 0` only at the consumptions `f(k) − ĥ(k)`, `k ∈ K`.
Then (3) with `h = ĥ` has a bounded solution `W`, unique among bounded solutions; the path of
`ĥ` is optimal in the pseudo-economy with discount factor `(1 − θ)β`; `W(k, k; ĥ)` is the
individual's value of following `ĥ`; and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice. -/
theorem indirect_equilibrium_full_pathwise {U f h : ℝ → ℝ} {β θ B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - h k)) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ K, 0 ≤ deriv f k)
    (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k) (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0)) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
        (fun k => (1 - θ) * deriv f k) h W β K ∧
      (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ K, |W' x k| ≤ M') →
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) h W' β K →
          ∀ x, 0 ≤ x → ∀ k ∈ K, W' x k = W x k) ∧
      ∀ k ∈ K, IsGreatest (plannerValues U f ((1 - θ) * β) k)
          (pathValue U f h ((1 - θ) * β) k) ∧
        W k k = pathValue U f h β k ∧
        ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
          (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (h k) = W k k ↔ y = h k) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  obtain ⟨W, M, hWb, hsol⟩ := exists_bellman_solution (U := U) (g := h)
    (A := fun k => f k - (1 - θ) * k * deriv f k) (B := fun k => (1 - θ) * deriv f k)
    hβ0.le hβ1 hUb hK hw hB
  obtain ⟨hvb, hpol⟩ := pathValue_spec (Fk := f) hβ0.le hβ1 hUb hK hc
  refine ⟨W, M, hWb, hsol, fun W' M' hW' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hW' hWb hK hw hB hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := indirect_equilibrium_dp_pathwise hU hβ0 hβ1 hθ hUd hU' hUb hK hK0 hf' hw
    hc heul htvc hvb hpol hWb hsol k hk
  refine ⟨?_, h1, h4⟩
  have hkt := iterate_mem hK hk
  have hβ' : 0 ≤ (1 - θ) * β := mul_nonneg (by linarith) hβ0.le
  have hβ'1 : (1 - θ) * β < 1 := by nlinarith
  -- the pseudo-planner's transversality condition follows from the individual's
  have htvc' := tvc_indiv_imp_pseudo hθ0 hθ (z := fun t => deriv U (f (h^[t] k) -
    h (h^[t] k)) * deriv f (h^[t] k) * h^[t] k) (by
      refine (htvc k hk).congr fun t => ?_
      ring)
  have hP := planner_optimal_pathwise (ks := fun t => h^[t] k) hU.concaveOn hUm hβ' hβ'1 hUb
    (fun t => by simp only [Function.iterate_succ_apply']; exact hUd _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hU' _ (hkt t))
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      rw [heul _ (hkt t)])
    (by
      refine htvc'.congr fun t => ?_
      simp only [Function.iterate_succ_apply']
      ring)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  exact hP

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interiority of the constructed planner's policy, §18.1

SLP §18.1, pp. 543–546. `ex_18_1_constructed` and `indirect_equilibrium_constructed` assume that
the policy `g` constructed in `IndirectExistence` is interior, `0 < g(k) < f(k)` on `K = [0, k̄]`,
and that `U′` and `f′` are continuous on `[0, k̄]`. With `U` differentiable on `[0, ∞)`, `U′(0)`
is finite and the Inada argument is unavailable. Here `U` is only continuous on `[0, ∞)`
(`PlannerHyp` asks no more), which allows `U′(0+) = ∞` with `U` bounded, e.g.
`U(c) = 1 − e^{−√c}` (`IndirectInteriorExample`).

* `InteriorHyp`: `PlannerHyp`, `b > 0`, the Inada condition `(U(c) − U(0))/c → ∞` as `c → 0+`,
  `f(0) = 0` and `f > 0` on `(0, k̄]`.
* `PlannerHyp.plannerPolicy_lt_of_inada` (route (i)): `g(k) < f(k)` wherever `f(k) > 0`.
* `PlannerHyp.plannerPolicy_pos_of_inada` (route (ii)): `g(k) > 0` on `(0, k̄]`. Only
  `U′(0+) = ∞`, `f(0) = 0` and concavity are used; no condition on `f′(0)` is needed, because a
  zero saving leaves zero consumption from the next period on.
* `InteriorHyp.policy_interior`, `InteriorHyp.policy_mapsTo`: `0 < g(k) < f(k)` on `(0, k̄]`,
  which `g` maps into itself. `InteriorHyp.not_interior_zero` (route (iii)): `g(0) = 0`, so
  interiority on all of `K` is impossible; the statements are made on `(0, k̄]`.
* `InteriorHyp.planner_euler_interior`: the Euler equation on `(0, k̄]`.
* `InteriorHyp.tvc_bound`, `InteriorHyp.planner_tvc`: the transversality condition
  `β′ᵗ a f′(k_t) U′(c_t) k_t → 0` for every `β′ ∈ [0, 1)`, from `v′(k) k ≤ v(k) − v(0)` (concavity
  and the envelope condition). This replaces the bound on `U′` from its continuity on `[0, k̄]`.
* `ex_18_1_interior`, `indirect_equilibrium_interior`: Exercise 18.1 and the indirect equilibrium
  of the pseudo-economy (`β̂ = (1 − θ)β`) with the planner constructed, interiority proved rather
  than assumed, `U` differentiable on `(0, ∞)` only, and no continuity of `U′` or `f′`; the
  aggregate state space is `(0, k̄]`.

The dynamic-programming steps are `ex_18_1_full_pathwise` and
`indirect_equilibrium_full_pathwise` (`IndirectInteriorDP`), which need `U` differentiable only
along the path.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set

/-- **The Inada condition in `ε`–`δ` form.** If `(U(c) − U(0))/c → ∞` as `c → 0+`, then for
every `L` there is `δ > 0` with `L c < U(c) − U(0)` for `0 < c < δ`. -/
theorem inada_exists_delta {U : ℝ → ℝ} (hI : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop)
    (L : ℝ) : ∃ δ > 0, ∀ c, 0 < c → c < δ → L * c < U c - U 0 := by
  have h := tendsto_atTop.1 hI (L + 1)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hδc⟩ := h
  refine ⟨δ, hδ, fun c hc hcδ => ?_⟩
  have h1 := hδc (by rw [Real.dist_eq, sub_zero, abs_of_pos hc]; exact hcδ) (mem_Ioi.2 hc)
  rw [le_div_iff₀ hc] at h1
  nlinarith

/-- **Positive consumption** (route (i)). Under `PlannerHyp`, if `U′(0+) = ∞` in the form
`(U(c) − U(0))/c → ∞` as `c → 0+`, then at every `k ∈ K` with `f(k) > 0` the planner consumes a
positive amount: `g(k) < f(k)`. (Saving everything loses `U(ε) − U(0)` against a gain in `b v` of
at most `4 b ‖v‖ ε / f(k)`, by concavity of `v`.) -/
theorem PlannerHyp.plannerPolicy_lt_of_inada {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) (hI : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) (hfk : 0 < f k) : plannerPolicy P k < f k := by
  set v := plannerValue P with hvdef
  set y₀ := f k with hy₀
  obtain ⟨hg, hmax, -⟩ := P.plannerPolicy_spec hk
  by_contra hge
  push Not at hge
  have heq : plannerPolicy P k = y₀ := le_antisymm hg.2 hge
  set Mv := ‖v‖ with hMvdef
  have hMv : ∀ x, |v x| ≤ Mv := fun x => by
    rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm x
  have hMv0 : 0 ≤ Mv := norm_nonneg _
  have hy₀K : y₀ ≤ kbar := P.f_le k hk
  obtain ⟨δ, hδ, hδc⟩ := inada_exists_delta hI (b * (4 * Mv / y₀))
  set ε := min (y₀ / 2) (δ / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ y₀ / 2 := min_le_left _ _
  have hε2 : ε < δ := (min_le_right _ _).trans_lt (by linarith)
  have hU := hδc ε hε0 hε2
  have hm := isMaxOn_iff.1 hmax (y₀ - ε) ⟨by linarith, by linarith⟩
  rw [heq] at hm
  simp only [hy₀, sub_sub_cancel, sub_self] at hm
  -- concavity of `v` between `0` and `y₀`
  change U ε + b * v (y₀ - ε) ≤ U 0 + b * v y₀ at hm
  have hcv := P.plannerValue_concave.2 (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar)
    (⟨hfk.le, hy₀K⟩ : y₀ ∈ Icc 0 kbar) (by positivity : 0 ≤ ε / y₀)
    (div_nonneg (by linarith) hfk.le : 0 ≤ (y₀ - ε) / y₀) (by field_simp; ring)
  have hpt : (ε / y₀) • (0 : ℝ) + ((y₀ - ε) / y₀) • y₀ = y₀ - ε := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hpt] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : ε * v 0 + (y₀ - ε) * v y₀ ≤ y₀ * v (y₀ - ε) := by
    have := mul_le_mul_of_nonneg_left hcv hfk.le
    have e : y₀ * (ε / y₀ * v 0 + (y₀ - ε) / y₀ * v y₀) = ε * v 0 + (y₀ - ε) * v y₀ := by
      field_simp
    linarith
  have hb1 := abs_le.1 (hMv 0)
  have hb2 := abs_le.1 (hMv (y₀ - ε))
  have hD : y₀ * (v y₀ - v (y₀ - ε)) ≤ 4 * ε * Mv := by
    rcases le_or_gt (v y₀ - v (y₀ - ε)) 0 with h | h
    · nlinarith
    · nlinarith
  have hbD := mul_le_mul_of_nonneg_left hD P.b_nonneg
  have e2 : b * (4 * Mv / y₀) * ε * y₀ = b * (4 * ε * Mv) := by field_simp
  have h3 : b * (4 * Mv / y₀) * ε * y₀ < (U ε - U 0) * y₀ := mul_lt_mul_of_pos_right hU hfk
  nlinarith

/-- **`k = 0` is degenerate when `f(0) = 0`**: `g(0) = 0`, and `v(0) = U(0) + b v(0)`. -/
theorem PlannerHyp.plannerPolicy_zero {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hf0 : f 0 = 0) : plannerPolicy P 0 = 0 ∧
      plannerValue P 0 = U 0 + b * plannerValue P 0 := by
  obtain ⟨hg, -, hv⟩ := P.plannerPolicy_spec (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar)
  rw [hf0] at hg hv
  have h0 : plannerPolicy P 0 = 0 := le_antisymm hg.2 hg.1
  rw [h0, sub_zero] at hv
  exact ⟨h0, hv⟩

/-- **Positive saving** (route (ii)). Under `PlannerHyp`, with `b > 0`, `U′(0+) = ∞`
(`(U(c) − U(0))/c → ∞` as `c → 0+`), `f(0) = 0` and `f > 0` on `(0, k̄]`, the planner saves a
positive amount at every `k ∈ (0, k̄]`: `g(k) > 0`. (Saving nothing leaves zero capital, hence
zero consumption, from the next period on; saving `y` gains at least `b [U(f(y)) − U(0)]`, which
is of larger order than `y` since `f(y) ≥ (f(k)/k) y` by concavity, while the loss today is
`O(y)` by concavity of `U`.) No condition on `f′(0)` is needed. -/
theorem PlannerHyp.plannerPolicy_pos_of_inada {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) (hb : 0 < b)
    (hI : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop) (hf0 : f 0 = 0)
    (hfpos : ∀ k ∈ Ioc 0 kbar, 0 < f k) {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    0 < plannerPolicy P k := by
  have hkK : k ∈ Icc 0 kbar := Ioc_subset_Icc_self hk
  set v := plannerValue P with hvdef
  set c := f k with hcdef
  have hc : 0 < c := hfpos k hk
  obtain ⟨hg, hmax, -⟩ := P.plannerPolicy_spec hkK
  by_contra hle
  push Not at hle
  have heq : plannerPolicy P k = 0 := le_antisymm hle hg.1
  have hv0 : v 0 = U 0 + b * v 0 := (P.plannerPolicy_zero hf0).2
  -- `v(y) ≥ U(f(y)) + b v(0)`: consume everything at `y`
  have hvy : ∀ y ∈ Icc 0 kbar, U (f y) + b * v 0 ≤ v y := by
    intro y hy
    obtain ⟨-, hmy, hvy⟩ := P.plannerPolicy_spec hy
    have := isMaxOn_iff.1 hmy 0 ⟨le_rfl, P.f_nonneg y hy⟩
    simp only [sub_zero] at this
    change U (f y) + b * v 0 ≤ U (f y - plannerPolicy P y) + b * v (plannerPolicy P y) at this
    change v y = U (f y - plannerPolicy P y) + b * v (plannerPolicy P y) at hvy
    linarith
  -- the bound on `U(c) − U(c − y)` from concavity
  set D := 2 * (U c - U 0) / c with hDdef
  have hU0c : U 0 ≤ U c := P.U_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hc.le) hc.le
  have hD0 : 0 ≤ D := by positivity
  have hUc : ∀ y, 0 < y → y ≤ c / 2 → U c - U (c - y) ≤ D * y := by
    intro y hy hyc
    have hcv := P.U_strictConcave.concaveOn.2 (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0)
      (mem_Ici.2 hc.le) (div_nonneg hy.le hc.le : 0 ≤ y / c)
      (div_nonneg (by linarith) hc.le : 0 ≤ (c - y) / c) (by field_simp; ring)
    have hpt : (y / c) • (0 : ℝ) + ((c - y) / c) • c = c - y := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt] at hcv
    simp only [smul_eq_mul] at hcv
    have hcv' : y * U 0 + (c - y) * U c ≤ c * U (c - y) := by
      have := mul_le_mul_of_nonneg_left hcv hc.le
      have e : c * (y / c * U 0 + (c - y) / c * U c) = y * U 0 + (c - y) * U c := by
        field_simp
      linarith
    have hmono : U (c - y) ≤ U c :=
      P.U_mono (mem_Ici.2 (by linarith)) (mem_Ici.2 hc.le) (by linarith)
    have e2 : D * y * c = 2 * y * (U c - U 0) := by rw [hDdef]; field_simp
    nlinarith
  -- `f(y) ≥ m y` on `[0, k]`, `m = f(k)/k`
  set m := c / k with hmdef
  have hm0 : 0 < m := div_pos hc hk.1
  have hfy : ∀ y, 0 ≤ y → y ≤ k → m * y ≤ f y := by
    intro y hy hyk
    have hk0 : k ≠ 0 := hk.1.ne'
    have hcv := P.f_concave.2 (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar) hkK
      (div_nonneg (by linarith) hk.1.le : 0 ≤ (k - y) / k) (div_nonneg hy hk.1.le : 0 ≤ y / k)
      (by field_simp; ring)
    have hpt : ((k - y) / k) • (0 : ℝ) + (y / k) • k = y := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt, hf0] at hcv
    simp only [smul_eq_mul, mul_zero, zero_add] at hcv
    have e : m * y = y / k * f k := by rw [hmdef, hcdef]; field_simp
    linarith
  -- the Inada condition at `f(y)` for small `y`
  set L := (D + 1) / (b * m) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hLm : b * L * m = D + 1 := by rw [hLdef]; field_simp
  obtain ⟨δ, hδ, hδc⟩ := inada_exists_delta hI L
  obtain ⟨δ', hδ', hδ'c⟩ := Metric.continuousWithinAt_iff.1
    (P.f_cont 0 ⟨le_rfl, P.kbar_nonneg⟩) δ hδ
  set y := min (min (c / 2) k) (δ' / 2) with hydef
  have hy0 : 0 < y := lt_min (lt_min (by linarith) hk.1) (by linarith)
  have hyc : y ≤ c / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hyk : y ≤ k := (min_le_left _ _).trans (min_le_right _ _)
  have hyδ : y < δ' := (min_le_right _ _).trans_lt (by linarith)
  have hyK : y ∈ Icc 0 kbar := ⟨hy0.le, hyk.trans hk.2⟩
  have hfy0 : 0 < f y := hfpos y ⟨hy0, hyk.trans hk.2⟩
  have hfyδ : f y < δ := by
    have := hδ'c hyK (by rw [Real.dist_eq, sub_zero, abs_of_pos hy0]; exact hyδ)
    rw [Real.dist_eq, hf0, sub_zero, abs_of_pos hfy0] at this
    exact this
  have hIn := hδc (f y) hfy0 hfyδ
  -- optimality of `g(k) = 0` against saving `y`
  have hopt := isMaxOn_iff.1 hmax y ⟨hy0.le, by linarith⟩
  rw [heq] at hopt
  change U (c - y) + b * v y ≤ U (c - 0) + b * v 0 at hopt
  rw [sub_zero] at hopt
  have h1 := hvy y hyK
  have h2 := hUc y hy0 hyc
  have h3 : L * (m * y) ≤ L * f y := mul_le_mul_of_nonneg_left (hfy y hy0.le hyk) hL0
  -- `b (U(f y) − U 0) ≤ D y` but `b (U(f y) − U 0) > (D + 1) y`
  have h4 : b * (U (f y) - U 0) ≤ D * y := by nlinarith
  have h5 : (D + 1) * y < b * (U (f y) - U 0) := by
    have := mul_lt_mul_of_pos_left hIn hb
    nlinarith
  linarith

/-- Under `PlannerHyp`, `U′(c) ≥ 0` for every `c > 0` (`U` is nondecreasing on `[0, ∞)`). -/
theorem PlannerHyp.deriv_U_nonneg {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {c : ℝ} (hc : 0 < c) : 0 ≤ deriv U c := by
  rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hc)]
  exact P.U_mono.derivWithin_nonneg

/-- **Primitive hypotheses for an interior planner's policy**: `PlannerHyp` (with `U` only
continuous on `[0, ∞)`, so `U′(0+) = ∞` is allowed), a positive discount factor, the Inada
condition `(U(c) − U(0))/c → ∞` as `c → 0+`, `f(0) = 0`, and `f > 0` on `(0, k̄]`. -/
structure InteriorHyp (U f : ℝ → ℝ) (b kbar : ℝ) : Prop where
  planner : PlannerHyp U f b kbar
  b_pos : 0 < b
  U_inada : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop
  f_zero : f 0 = 0
  f_pos : ∀ k ∈ Ioc 0 kbar, 0 < f k

/-- **Interiority of the constructed policy on `(0, k̄]`**: `0 < g(k) < f(k)`. -/
theorem InteriorHyp.policy_interior {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k :=
  ⟨I.planner.plannerPolicy_pos_of_inada I.b_pos I.U_inada I.f_zero I.f_pos hk,
    I.planner.plannerPolicy_lt_of_inada I.U_inada (Ioc_subset_Icc_self hk) (I.f_pos k hk)⟩

/-- The policy maps `(0, k̄]` into `(0, k̄)`. -/
theorem InteriorHyp.policy_mem_Ioo {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    plannerPolicy I.planner k ∈ Ioo 0 kbar :=
  ⟨(I.policy_interior hk).1,
    (I.policy_interior hk).2.trans_le (I.planner.f_le k (Ioc_subset_Icc_self hk))⟩

/-- The policy maps `(0, k̄]` into itself. -/
theorem InteriorHyp.policy_mapsTo {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    plannerPolicy I.planner k ∈ Ioc 0 kbar :=
  Ioo_subset_Ioc_self (I.policy_mem_Ioo hk)

/-- **Interiority on all of `K` is impossible** under `InteriorHyp`: `g(0) = 0` and consumption
at `k = 0` is `0` (route (iii): the interior statements are made on `(0, k̄]`). -/
theorem InteriorHyp.not_interior_zero {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar) :
    plannerPolicy I.planner 0 = 0 ∧ f 0 - plannerPolicy I.planner 0 = 0 ∧
      ¬ ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy I.planner k := by
  have h0 := (I.planner.plannerPolicy_zero I.f_zero).1
  refine ⟨h0, by rw [h0, I.f_zero, sub_zero], fun h => ?_⟩
  have := h 0 ⟨le_rfl, I.planner.kbar_nonneg⟩
  rw [h0] at this
  exact lt_irrefl _ this

/-- **The planner's Euler equation on `(0, k̄]`** under `InteriorHyp`, with `U` differentiable on
`(0, ∞)` and `f` on `(0, k̄]`:
`U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]`. -/
theorem InteriorHyp.planner_euler_interior {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k) {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    deriv U (f k - plannerPolicy I.planner k) = b * deriv f (plannerPolicy I.planner k) *
      deriv U (f (plannerPolicy I.planner k) -
        plannerPolicy I.planner (plannerPolicy I.planner k)) := by
  have hi := I.policy_interior hk
  have hgk := I.policy_mapsTo hk
  have hi2 := I.policy_interior hgk
  exact I.planner.planner_euler (Ioc_subset_Icc_self hk) hi.1 hi.2 hi2.2
    (hUd _ (sub_pos.2 hi.2)) (hUd _ (sub_pos.2 hi2.2)) (hfd _ hgk)

/-- **The bound behind the transversality condition.** For `k ∈ (0, k̄]`,
`f′(k) U′[f(k) − g(k)] k ≥ 0`, and for `k < k̄` it is at most `2 ‖v‖`: by the envelope
condition it is `v′(k) k`, and `v′(k) k ≤ v(k) − v(0)` by concavity of `v`. No bound on `U′`
near `0` is used. -/
theorem InteriorHyp.tvc_bound {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    0 ≤ deriv f k * deriv U (f k - plannerPolicy I.planner k) * k ∧
      (k < kbar → deriv f k * deriv U (f k - plannerPolicy I.planner k) * k ≤
        2 * ‖plannerValue I.planner‖) := by
  set P := I.planner with hP
  have hi := I.policy_interior hk
  refine ⟨mul_nonneg (mul_nonneg (hf' k hk) (P.deriv_U_nonneg (sub_pos.2 hi.2))) hk.1.le,
    fun hkb => ?_⟩
  have hkI : k ∈ Ioo 0 kbar := ⟨hk.1, hkb⟩
  have henv := P.planner_envelope hkI hi.2 (hUd _ (sub_pos.2 hi.2)) (hfd k hk)
  have hsl := P.plannerValue_concave.le_slope_of_hasDerivAt
    (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar) (Ioc_subset_Icc_self hk) hk.1 henv
  rw [slope_def_field, sub_zero, le_div_iff₀ hk.1] at hsl
  have h1 := abs_le.1 (by rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k :
    |plannerValue P k| ≤ ‖plannerValue P‖)
  have h2 := abs_le.1 (by rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm 0 :
    |plannerValue P 0| ≤ ‖plannerValue P‖)
  linarith

/-- **Transversality for the constructed policy** under `InteriorHyp`: for every `β′ ∈ [0, 1)`,
constant `a` and `k ∈ (0, k̄]`, `β′ᵗ (a f′(k_t)) U′(c_t) k_t → 0` along `k_t = gᵗ(k)`. This
replaces the continuity of `U′` on `[0, k̄]` used by `PlannerHyp.planner_euler_tvc`, which fails
when `U′(0+) = ∞`. -/
theorem InteriorHyp.planner_tvc {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k)
    (β' a : ℝ) (hβ0 : 0 ≤ β') (hβ1 : β' < 1) {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    Tendsto (fun t => β' ^ t * (a * deriv f ((plannerPolicy I.planner)^[t] k)) *
      deriv U (f ((plannerPolicy I.planner)^[t] k) -
        plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          (plannerPolicy I.planner)^[t] k) atTop (𝓝 0) := by
  set g := plannerPolicy I.planner with hg
  set Z : ℝ → ℝ := fun k => deriv f k * deriv U (f k - g k) * k with hZ
  set Mv := ‖plannerValue I.planner‖ with hMv
  have hMv0 : 0 ≤ Mv := norm_nonneg _
  have hkt := iterate_mem (fun k hk => I.policy_mapsTo hk) hk
  have hZb : ∀ k ∈ Ioc 0 kbar, |Z k| ≤ 2 * Mv + |Z kbar| := by
    intro k hk
    obtain ⟨h0, h1⟩ := I.tvc_bound hUd hfd hf' hk
    rcases lt_or_eq_of_le hk.2 with hlt | heq
    · rw [abs_of_nonneg h0]
      have := h1 hlt
      have := abs_nonneg (Z kbar)
      linarith
    · rw [heq]
      linarith
  refine (tvc_of_bounded (M := |a| * (2 * Mv + |Z kbar|)) hβ0 hβ1
    (z := fun t => a * Z (g^[t] k)) fun t => ?_).congr fun t => by simp only [hZ]; ring
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hZb _ (hkt t)) (abs_nonneg a)

/-- **Exercise 18.1 with the planner constructed and interior** (pp. 543–544). Let
`I : InteriorHyp U f β k̄`, `U` differentiable on `(0, ∞)` and bounded by `B₀` on `[0, ∞)`, `f`
concave on `[0, ∞)`, differentiable with `f′ ≥ 0` on `(0, k̄]`. Then:
(0) the constructed policy `g` is interior on `(0, k̄]`;
(i) `v` solves (1) on `K`, `g` is continuous on `K` and the unique maximiser in (1);
(ii) `g` satisfies the Euler equation on `(0, k̄]`;
(iii) (2) has a bounded solution `V` on `[0, ∞) × (0, k̄]`, unique among bounded solutions, with
`V(k, k; g) = v(k)`, the maximal value of the planner's problem, and `G(k, k; g) = g(k)`;
(iv) on `(0, k̄)`, `V₁(k, k; g) = v′(k) = f′(k) U′[f(k) − g(k)]`.
Compared with `ex_18_1_constructed`, interiority is proved, and `U` need not be differentiable at
`0` and `U′`, `f′` need not be continuous; the aggregate state space is `(0, k̄]`, since `k = 0` is
degenerate (`InteriorHyp.not_interior_zero`). -/
theorem ex_18_1_interior {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (I : InteriorHyp U f β kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Ioc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f β kbar (plannerValue I.planner) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy I.planner k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue I.planner y = plannerValue I.planner k ↔
          y = plannerPolicy I.planner k) ∧
      (∀ k ∈ Ioc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        β * deriv U (f (plannerPolicy I.planner k) -
          plannerPolicy I.planner (plannerPolicy I.planner k)) *
            deriv f (plannerPolicy I.planner k)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |V x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V β
          (Ioc 0 kbar) ∧
        (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |V' x k| ≤ M') →
          SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V'
            β (Ioc 0 kbar) → ∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, V' x k = V x k) ∧
        (∀ k ∈ Ioc 0 kbar, V k k = plannerValue I.planner k ∧
          IsGreatest (plannerValues U f β k) (V k k) ∧
          ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
            (U (f k + (k - k) * deriv f k - y) + β * V y (plannerPolicy I.planner k) = V k k ↔
              y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => V x k) (deriv (plannerValue I.planner) k) k ∧
          HasDerivAt (plannerValue I.planner)
            (deriv f k * deriv U (f k - plannerPolicy I.planner k)) k := by
  set P := I.planner with hP
  set g := plannerPolicy P with hg
  set K := Ioc 0 kbar with hKdef
  have hβ0 := I.b_pos
  have hint : ∀ k ∈ K, 0 < g k ∧ g k < f k := fun k hk => I.policy_interior hk
  have hgK : ∀ k ∈ K, g k ∈ K := fun k hk => I.policy_mapsTo hk
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1.le
  have hc : ∀ k ∈ K, 0 ≤ f k - g k := fun k hk => (sub_pos.2 (hint k hk).2).le
  have hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k := by
    intro k hk
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1.le (hfd k hk)
    rw [I.f_zero] at this
    linarith
  have hUdK : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k) := fun k hk =>
    hUd _ (sub_pos.2 (hint k hk).2)
  have hU'K : ∀ k ∈ K, 0 ≤ deriv U (f k - g k) := fun k hk =>
    P.deriv_U_nonneg (sub_pos.2 (hint k hk).2)
  have heul' : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k) := fun k hk => by
    rw [I.planner_euler_interior hUd hfd hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0) := fun k hk =>
    (I.planner_tvc hUd hfd hf' β 1 hβ0.le P.b_lt_one hk).congr fun t => by ring
  obtain ⟨V, M, hVb, hsol, huniq, hall⟩ := ex_18_1_full_pathwise P.U_strictConcave P.U_mono hβ0
    P.b_lt_one hUdK hU'K hUb hf hgK hK0 hfd hf' hw hc heul' htvc'
  have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
    rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
  have hpol : ∀ k ∈ K, plannerValue P k = U (f k - g k) + β * plannerValue P (g k) :=
    fun k hk => (P.plannerPolicy_spec (Ioc_subset_Icc_self hk)).2.2
  have hdp := ex_18_1_dp_pathwise P.U_strictConcave hβ0 P.b_lt_one hUdK hU'K hUb hgK hK0 hf' hw
    hc heul' htvc' hvb hpol hVb hsol
  refine ⟨hint, P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨(P.plannerPolicy_spec hk).1, fun y hy => P.plannerPolicy_unique hk hy⟩, heul',
    V, M, hVb, hsol, huniq, fun k hk => ⟨(hdp k hk).1, (hall k hk).1, (hall k hk).2⟩,
    fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Ioc_self hk
  have hv' := P.planner_envelope hk (hint k hkK).2 (hUdK k hkK) (hfd k hkK)
  refine ⟨?_, hv'⟩
  rw [hv'.deriv]
  have hopt := ((hall k hkK).2 (g k) ⟨(hgK k hkK).1.le, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : (fun k => f k - k * deriv f k) k + deriv f k * k - g k = f k - g k := by
    simp only; ring
  have e' : f k + (k - k) * deriv f k - g k = f k - g k := by ring
  rw [e'] at hopt
  exact bellman_envelope hβ0.le P.b_lt_one P.U_strictConcave.concaveOn hUb hVb hgK hw hf' hsol
    hk.1 hkK (hgK k hkK).1.le (by rw [e]; exact sub_pos.2 (hint k hkK).2) (by rw [e]; exact hopt)
    (by rw [e]; exact (hUdK k hkK).hasDerivAt)

/-- **The indirect equilibrium with the pseudo-planner constructed and interior** (p. 546). Tax
`θ ∈ [0, 1)` on capital income, rebated; `β < 1`; `I : InteriorHyp U f ((1 − θ)β) k̄`; `U`, `f`
as in `ex_18_1_interior`. Then: (0) `ĥ` is interior on `(0, k̄]`; (i) `w` solves (8) on `K`, `ĥ` is
continuous, and on `(0, k̄]` `w(k)` is the value of the path of `ĥ` in the pseudo-economy, the
maximal value of its sequence problem; (ii) (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `(0, k̄]` and
(10) `w′(k) = f′(k) U′[f(k) − ĥ(k)]` on `(0, k̄)`; (iii) (3) with `h = ĥ` has a bounded solution
`W` on `[0, ∞) × (0, k̄]`, unique among bounded solutions, `W(k, k; ĥ)` is the value of following
`ĥ`, and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice (a recursive competitive equilibrium);
(iv) `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` on `(0, k̄)`. Interiority is not assumed, unlike
`indirect_equilibrium_constructed`. -/
theorem indirect_equilibrium_interior {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (I : InteriorHyp U f ((1 - θ) * β) kbar) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Ioc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue I.planner) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Ioc 0 kbar,
        plannerValue I.planner k = pathValue U f (plannerPolicy I.planner) ((1 - θ) * β) k ∧
          IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue I.planner k)) ∧
      (∀ k ∈ Ioc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        (1 - θ) * β * deriv (plannerValue I.planner) (plannerPolicy I.planner k)) ∧
      (∀ k ∈ Ioo 0 kbar, HasDerivAt (plannerValue I.planner)
        (deriv f k * deriv U (f k - plannerPolicy I.planner k)) k) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W β (Ioc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W' β (Ioc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Ioc 0 kbar, W k k = pathValue U f (plannerPolicy I.planner) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy I.planner k) =
              W k k ↔ y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar,
          HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue I.planner) k) k := by
  set P := I.planner with hP
  set h := plannerPolicy P with hh
  set K := Ioc 0 kbar with hKdef
  have hβ0 : 0 < β := by
    have := I.b_pos
    by_contra hb
    push Not at hb
    have : (1 - θ) * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hb
    linarith
  have hint : ∀ k ∈ K, 0 < h k ∧ h k < f k := fun k hk => I.policy_interior hk
  have hhK : ∀ k ∈ K, h k ∈ K := fun k hk => I.policy_mapsTo hk
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1.le
  have hc : ∀ k ∈ K, 0 ≤ f k - h k := fun k hk => (sub_pos.2 (hint k hk).2).le
  have hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k := by
    intro k hk
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1.le (hfd k hk)
    rw [I.f_zero] at this
    have := mul_nonneg (mul_nonneg hθ0 hk.1.le) (hf' k hk)
    nlinarith
  have hUdK : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k) := fun k hk =>
    hUd _ (sub_pos.2 (hint k hk).2)
  have hU'K : ∀ k ∈ K, 0 ≤ deriv U (f k - h k) := fun k hk =>
    P.deriv_U_nonneg (sub_pos.2 (hint k hk).2)
  have heul' : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k) := fun k hk => by
    rw [I.planner_euler_interior hUd hfd hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0) := fun k hk =>
    I.planner_tvc hUd hfd hf' β (1 - θ) hβ0.le hβ1 hk
  obtain ⟨W, M, hWb, hsol, huniq, hall⟩ := indirect_equilibrium_full_pathwise P.U_strictConcave
    P.U_mono hβ0 hβ1 hθ0 hθ hUdK hU'K hUb hf hhK hK0 hfd hf' hw hc heul' htvc'
  -- the envelope condition (10) for `w`
  have h10 : ∀ k ∈ Ioo 0 kbar,
      HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - h k)) k := fun k hk =>
    P.planner_envelope hk (hint k (Ioo_subset_Ioc_self hk)).2 (hUdK k (Ioo_subset_Ioc_self hk))
      (hfd k (Ioo_subset_Ioc_self hk))
  -- the first-order condition (9)
  have h9 : ∀ k ∈ K, deriv U (f k - h k) = (1 - θ) * β * deriv (plannerValue P) (h k) := by
    intro k hk
    exact P.planner_foc (Ioc_subset_Icc_self hk) (hint k hk).1 (hint k hk).2 (hUdK k hk)
      (h10 _ (I.policy_mem_Ioo hk)).differentiableAt
  -- `w` is the value of the path of `ĥ`
  have hval : ∀ k ∈ K, plannerValue P k = pathValue U f h ((1 - θ) * β) k := by
    intro k hk
    have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
      rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
    have hs := policyValue_hasSum P.b_nonneg P.b_lt_one hhK hvb (fun k hk => hUb _ (hc k hk))
      (fun k hk => (P.plannerPolicy_spec (Ioc_subset_Icc_self hk)).2.2) hk
    exact hs.tsum_eq.symm
  refine ⟨hint, P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨hval k hk, (hval k hk) ▸ (hall k hk).1⟩, h9, h10, W, M, hWb, hsol, huniq,
    fun k hk => ⟨(hall k hk).2.1, (hall k hk).2.2⟩, fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Ioc_self hk
  have hopt := ((hall k hkK).2.2 (h k) ⟨(hhK k hkK).1.le, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : f k + (1 - θ) * (k - k) * deriv f k - h k = f k - h k := by ring
  obtain ⟨h5, -⟩ := eq_18_1_4_5 hβ0.le hβ1 hθ P.U_strictConcave.concaveOn hUb hhK hf' hw hWb hsol
    hk.1 hkK (hint k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) hopt
    (by rw [e]; exact hUdK k hkK)
  rw [(h10 k hk).deriv]
  rw [e] at h5
  convert h5 using 1
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An economy satisfying `InteriorHyp`

SLP §18.1, pp. 543–546 (the economy is not in the book). `U(c) = 1 − e^{−√c}` (`inadaU`) and
`f(k) = √k` on `K = [0, 1]` satisfy every hypothesis of `ex_18_1_interior` and
`indirect_equilibrium_interior`, so those hypotheses are consistent.

* `inadaU_strictConcaveOn`, `inadaU_monotoneOn`, `abs_inadaU_le`, `differentiableAt_inadaU`:
  `U` is strictly concave, nondecreasing and bounded on `[0, ∞)`, and differentiable on `(0, ∞)`.
* `inadaU_inada`: `(U(c) − U(0))/c → ∞` as `c → 0+`.
* `inadaU_not_differentiableAt_zero`: `U` is not differentiable at `0`, so the economy is outside
  `plannerHyp_of_differentiable`, `ex_18_1_constructed` and `indirect_equilibrium_constructed`.
* `inada_interiorHyp`: `InteriorHyp inadaU √ b 1` for every `b ∈ (0, 1)`.
* `inada_example_interior`, `inada_example_ex_18_1`, `inada_example_equilibrium`: the constructed
  policies are interior on `(0, 1]`; Exercise 18.1 and the recursive competitive equilibrium of
  the taxed economy hold there.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set

/-- The utility `U(c) = 1 − e^{−√c}`: bounded, strictly concave, with `U′(0+) = ∞`. -/
noncomputable def inadaU (c : ℝ) : ℝ := 1 - Real.exp (-Real.sqrt c)

/-- `U(0) = 0`. -/
theorem inadaU_zero : inadaU 0 = 0 := by
  simp [inadaU]

/-- `U` is continuous. -/
theorem continuous_inadaU : Continuous inadaU := by
  unfold inadaU
  fun_prop

/-- `U` is nondecreasing on `[0, ∞)`. -/
theorem inadaU_monotoneOn : MonotoneOn inadaU (Ici 0) := fun c _ d _ h => by
  have h1 := Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt h))
  simp only [inadaU]
  linarith

/-- `U` is strictly concave on `[0, ∞)`: `s ↦ 1 − e^{−s}` is concave and strictly increasing, and
`√` is strictly concave. -/
theorem inadaU_strictConcaveOn : StrictConcaveOn ℝ (Ici 0) inadaU := by
  have himg : Real.sqrt '' Ici 0 = Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg x
    · intro hy
      exact ⟨y ^ 2, sq_nonneg y, Real.sqrt_sq hy⟩
  have hg : ConcaveOn ℝ (Real.sqrt '' Ici 0) (fun s : ℝ => 1 - Real.exp (-s)) := by
    rw [himg]
    refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    have h := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have e : -(a * x + b * y) = a * -x + b * -y := by ring
    rw [e]
    nlinarith
  have hg' : StrictMonoOn (fun s : ℝ => 1 - Real.exp (-s)) (Real.sqrt '' Ici 0) :=
    fun x _ y _ h => by
      have := Real.exp_lt_exp.2 (neg_lt_neg h)
      simp only
      linarith
  exact hg.comp_strictConcaveOn Real.strictConcaveOn_sqrt hg'

/-- `0 ≤ U < 1` (on all of `ℝ`, since `√c = 0` for `c < 0`), so `|U| ≤ 1`. -/
theorem abs_inadaU_le (c : ℝ) : |inadaU c| ≤ 1 := by
  have h1 : Real.exp (-Real.sqrt c) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg c))
  have h2 := Real.exp_pos (-Real.sqrt c)
  have h0 : 0 ≤ inadaU c := by simp only [inadaU]; linarith
  rw [abs_of_nonneg h0]
  simp only [inadaU]
  linarith

/-- `U` is differentiable on `(0, ∞)`. -/
theorem differentiableAt_inadaU {c : ℝ} (hc : 0 < c) : DifferentiableAt ℝ inadaU c :=
  ((Real.hasDerivAt_sqrt hc.ne').differentiableAt.neg.exp).const_sub 1

/-- **The Inada condition** `(U(c) − U(0))/c → ∞` as `c → 0+`: with `s = √c ≤ 1`,
`1 − e^{−s} ≥ s/(1 + s) ≥ s/2`, so the quotient is at least `1/(2s)`. -/
theorem inadaU_inada : Tendsto (fun c => (inadaU c - inadaU 0) / c) (𝓝[>] 0) atTop := by
  rw [inadaU_zero]
  refine tendsto_atTop.2 fun L => ?_
  set L' := max L 1 with hL'
  have hL'0 : 0 < L' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ : (0 : ℝ) < min 1 ((1 / (2 * L')) ^ 2) := lt_min zero_lt_one (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with c hc
  have hc0 : 0 < c := hc.1
  set s := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hc0
  have hs1 : s < 1 := (Real.sqrt_lt' zero_lt_one).2 (by
    have := hc.2.trans_le (min_le_left _ _); linarith)
  have hs2 : s < 1 / (2 * L') := (Real.sqrt_lt' (by positivity)).2
    (hc.2.trans_le (min_le_right _ _))
  have hsc : s ^ 2 = c := Real.sq_sqrt hc0.le
  have hexp : Real.exp (-s) * (1 + s) ≤ 1 := by
    have h1 := Real.add_one_le_exp s
    have h2 := Real.exp_pos (-s)
    have h3 : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith
  have hE1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hhalf : s / 2 ≤ 1 - Real.exp (-s) := by nlinarith
  have h2Ls : 2 * L' * s < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hs2
    linarith
  rw [sub_zero, le_div_iff₀ hc0]
  have hLL : L * c ≤ L' * c := mul_le_mul_of_nonneg_right (le_max_left _ _) hc0.le
  simp only [inadaU]
  rw [← hs]
  nlinarith

/-- **`U` is not differentiable at `0`**: a derivative there would be the finite limit of the
quotients of `inadaU_inada`. So `U` violates the hypotheses of `plannerHyp_of_differentiable`,
`ex_18_1_constructed` and `indirect_equilibrium_constructed`. -/
theorem inadaU_not_differentiableAt_zero : ¬ DifferentiableAt ℝ inadaU 0 := by
  intro hd
  have h := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
  have h' : Tendsto (slope inadaU 0) (𝓝[>] 0) (𝓝 (deriv inadaU 0)) :=
    h.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt (mem_Ioi.1 hx))
  have hI : Tendsto (slope inadaU 0) (𝓝[>] 0) atTop := by
    refine inadaU_inada.congr fun c => ?_
    rw [slope_def_field, sub_zero]
  exact not_tendsto_nhds_of_tendsto_atTop hI _ h'

/-- **The example satisfies `InteriorHyp`**: for `b ∈ (0, 1)`, `U(c) = 1 − e^{−√c}`,
`f(k) = √k` and `k̄ = 1`. -/
theorem inada_interiorHyp {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    InteriorHyp inadaU Real.sqrt b 1 where
  planner :=
    { b_nonneg := hb0.le
      b_lt_one := hb1
      kbar_nonneg := zero_le_one
      U_cont := continuous_inadaU.continuousOn
      U_mono := inadaU_monotoneOn
      U_strictConcave := inadaU_strictConcaveOn
      f_cont := Real.continuous_sqrt.continuousOn
      f_concave := Real.strictConcaveOn_sqrt.concaveOn.subset Icc_subset_Ici_self (convex_Icc 0 1)
      f_nonneg := fun k _ => Real.sqrt_nonneg k
      f_le := fun _ hk => Real.sqrt_le_one.2 hk.2 }
  b_pos := hb0
  U_inada := inadaU_inada
  f_zero := Real.sqrt_zero
  f_pos := fun _ hk => Real.sqrt_pos.2 hk.1

/-- `f(k) = √k` is differentiable on `(0, 1]` with `f′ ≥ 0` there. -/
theorem sqrt_deriv_facts : (∀ k ∈ Ioc (0 : ℝ) 1, DifferentiableAt ℝ Real.sqrt k) ∧
    ∀ k ∈ Ioc (0 : ℝ) 1, 0 ≤ deriv Real.sqrt k :=
  ⟨fun k hk => (Real.hasDerivAt_sqrt hk.1.ne').differentiableAt, fun k hk => by
    rw [(Real.hasDerivAt_sqrt hk.1.ne').deriv]
    positivity⟩

/-- **The constructed policy of the example is interior** on `(0, 1]`:
`0 < g(k) < √k`. -/
theorem inada_example_interior {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ k ∈ Ioc (0 : ℝ) 1, 0 < plannerPolicy (inada_interiorHyp hb0 hb1).planner k ∧
      plannerPolicy (inada_interiorHyp hb0 hb1).planner k < Real.sqrt k :=
  fun _ hk => (inada_interiorHyp hb0 hb1).policy_interior hk

/-- **Exercise 18.1 in the example** (p. 544): for `β ∈ (0, 1)`, the bounded solution `V` of (2)
on `[0, ∞) × (0, 1]` exists, `V(k, k; g) = v(k)` and `G(k, k; g) = g(k)` for the constructed `g`,
which is interior. -/
theorem inada_example_ex_18_1 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ k ∈ Ioc (0 : ℝ) 1, 0 < plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k ∧
      plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k < Real.sqrt k) ∧
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc (0 : ℝ) 1, |V x k| ≤ M) ∧
      SolvesBellman inadaU (fun k => Real.sqrt k - k * deriv Real.sqrt k) (deriv Real.sqrt)
        (plannerPolicy (inada_interiorHyp hβ0 hβ1).planner) V β (Ioc 0 1) ∧
      ∀ k ∈ Ioc (0 : ℝ) 1, V k k = plannerValue (inada_interiorHyp hβ0 hβ1).planner k ∧
        ∀ y ∈ feasY (fun k => Real.sqrt k - k * deriv Real.sqrt k) (deriv Real.sqrt) k k,
          (inadaU (Real.sqrt k + (k - k) * deriv Real.sqrt k - y) +
            β * V y (plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k) = V k k ↔
              y = plannerPolicy (inada_interiorHyp hβ0 hβ1).planner k) := by
  obtain ⟨hint, -, -, -, -, V, M, hVb, hsol, -, hall, -⟩ := ex_18_1_interior
    (inada_interiorHyp hβ0 hβ1) (fun c hc => differentiableAt_inadaU hc)
    (fun c _ => abs_inadaU_le c) Real.strictConcaveOn_sqrt.concaveOn sqrt_deriv_facts.1
    sqrt_deriv_facts.2
  exact ⟨hint, V, M, hVb, hsol, fun k hk => ⟨(hall k hk).1, (hall k hk).2.2⟩⟩

/-- **The indirect equilibrium in the example** (p. 546): for `β ∈ (0, 1)` and `θ ∈ [0, 1)`, the
pseudo-planner's policy `ĥ` (discount factor `(1 − θ)β`) is interior on `(0, 1]`, and it is a
recursive competitive equilibrium of the taxed economy: the bounded solution `W` of (3) with
`h = ĥ` has `H(k, k; ĥ) = ĥ(k)` for `k ∈ (0, 1]`. -/
theorem inada_example_equilibrium {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    ∃ I : InteriorHyp inadaU Real.sqrt ((1 - θ) * β) 1,
      (∀ k ∈ Ioc (0 : ℝ) 1, 0 < plannerPolicy I.planner k ∧
        plannerPolicy I.planner k < Real.sqrt k) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc (0 : ℝ) 1, |W x k| ≤ M) ∧
        SolvesBellman inadaU (fun k => Real.sqrt k - (1 - θ) * k * deriv Real.sqrt k)
          (fun k => (1 - θ) * deriv Real.sqrt k) (plannerPolicy I.planner) W β (Ioc 0 1) ∧
        ∀ k ∈ Ioc (0 : ℝ) 1, ∀ y ∈ feasY (fun k => Real.sqrt k - (1 - θ) * k * deriv Real.sqrt k)
            (fun k => (1 - θ) * deriv Real.sqrt k) k k,
          (inadaU (Real.sqrt k + (1 - θ) * (k - k) * deriv Real.sqrt k - y) +
            β * W y (plannerPolicy I.planner k) = W k k ↔ y = plannerPolicy I.planner k) := by
  have hb0 : 0 < (1 - θ) * β := mul_pos (by linarith) hβ0
  have hb1 : (1 - θ) * β < 1 := by nlinarith
  have I := inada_interiorHyp hb0 hb1
  obtain ⟨hint, -, -, -, -, -, W, M, hWb, hsol, -, hall, -⟩ := indirect_equilibrium_interior I
    hβ1 hθ0 hθ1 (fun c hc => differentiableAt_inadaU hc) (fun c _ => abs_inadaU_le c)
    Real.strictConcaveOn_sqrt.concaveOn sqrt_deriv_facts.1 sqrt_deriv_facts.2
  exact ⟨I, hint, W, M, hWb, hsol, fun k hk => (hall k hk).2⟩

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A local approach based on first-order conditions: the setting

SLP §18.2, pp. 547–549. One-sector growth with a flat tax `θ` on capital income whose proceeds
are thrown away. After-tax income is `ψ(k) = f(k) − θ k f′(k)` (`psi`), and an equilibrium is a
savings function `g` with `F[k, g(k), g²(k)] = 0` (§18.2 (4)), where (§18.2 (3), `Feq`)
`F(x, y, z) = U′[ψ(x) − y] − β(1 − θ) f′(y) U′[ψ(y) − z]`.

* `Assumption18_1` (**Assumption 18.1**, pp. 547–548). `U` and `f` are functions `ℝ → ℝ` that
  are `C²` on all of `ℝ`; the book's properties on `[0, ∞)` are imposed on `Ici 0`. (A `C²`
  function on `[0, ∞)` extends to a `C²` function on `ℝ`, so nothing is lost.) Part (d)'s
  `lim_{k→0} f′(k)` equals `f′(0)` by continuity (`tendsto_deriv_f_zero`).
* Derived facts (F1)–(F4): `U′ > 0` and `f′ > 0` on `[0, ∞)` (`deriv_U_pos`, `deriv_f_pos`),
  `f′` strictly decreasing (`deriv_f_strictAnti`), `ψ(k̄) = k̄` (`psi_kbar`),
  `ψ(k) ≥ k` on `K = [0, k̄]` (`le_psi`), `β(1 − θ) f′(k̄) < 1` (`euler_kbar_lt`), and a unique
  `k* ∈ (0, k̄)` with `β(1 − θ) f′(k*) = 1` (`exists_unique_kstar`).
* **Proposition 18.1** (`prop_18_1`, p. 548): a continuous `g : K → K` solving (4) has exactly
  one fixed point, namely `k*`. Existence of a fixed point is Brouwer's theorem
  (`brouwer`, Theorem 17.3).
* The partial derivatives `F₁, F₂, F₃` (`F1f`, `F2f`, `F3f`, with `hasDerivAt_Feq_x`, `_y`, `_z`)
  and their values `F₁*, F₂*, F₃*` at `(k*, k*, k*)` (§18.2 (6a)–(6c), `F1s`, `F2s`, `F3s`,
  `F1f_star`, `F2f_star`, `F3f_star`).
* `LocalHyp`: the hypotheses used by the local analysis, including the added `U″(c*) < 0`,
  `f″(k*) < 0`; `Assumption18_1.localHyp`.
* The characteristic polynomial `P(λ) = F₁* + F₂* λ + F₃* λ²` (`charPoly`), its roots
  `λ* ∈ (0, 1)` (`lamStar`) and `λ₂ > 1` (`lamTwo`), with `P > 0` on `(λ*, λ₂)` (`charPoly_roots`,
  p. 549), `F₂* > 0`, `H₁* = −F₁*/F₂* > 0`, `H₂* = −F₃*/F₂* > 0`, `H₁* + H₂* < 1`, and
  `H₁* + H₂* λ² < λ` for `λ ∈ (λ*, 1)`.

**Corrections.**
* (Assumption 18.1 vs. Assumption 18.2, NOTE 18.3-A.) Assumption 18.1(b) makes `U` `C²` on
  `[0, ∞)`, so `U′(0)` is finite and the Inada condition `U′(0⁺) = ∞` of Assumption 18.2 fails
  (`Assumption18_1.not_inada`); §18.3 must read `U` as `C²` on `(0, ∞)` only.
* (NOTE 18.2-A, p. 549.) Existence of `k*` uses Assumption 18.1(e) as well as (d)
  (`euler_kbar_lt`); and dividing by `U′` uses `U′ > 0` (`deriv_U_pos`). Verified;
  `exists_unique_kstar` and `prop_18_1` use both.
* (NOTE 18.2-B, p. 549.) The sign claims `P(0) < 0`, `P(1) > 0`, `lim P = −∞` need
  `U″(c*) < 0` and `f″(k*) < 0`, which strict concavity does not give:
  `strictConcave_deriv2_zero_counterexample` is a `C²`, strictly increasing, strictly concave
  `U` with `U″(c₀) = 0` at any prescribed `c₀`. If `U″(c*) = 0` then `F₁* = F₃* = 0` and
  `P(0) = 0` (`charPoly_degenerate_U`); if `f″(k*) = 0` then `P(1) = 0`
  (`charPoly_degenerate_f`). The hypotheses `U″(c*) < 0` and `f″(k*) < 0` are added
  (`LocalHyp`).
* (NOTE 18.2-C, p. 549.) `P(F₁*/F₃*) = (F₁*/F₃*) P(1) > 0` (`charPoly_F1_div_F3`), so
  `F₁*/F₃*` lies strictly between the roots: `λ* < F₁*/F₃* < λ₂`; since `F₁*/F₃* > 1`, the
  inequality `λ* < F₁*/F₃*` is the trivial part. Verified (`charPoly_roots`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- After-tax income `ψ(k) = f(k) − θ k f′(k)`. -/
noncomputable def psi (θ : ℝ) (f : ℝ → ℝ) (k : ℝ) : ℝ := f k - θ * k * deriv f k

/-- The function `F(x, y, z) = U′[ψ(x) − y] − β(1 − θ) f′(y) U′[ψ(y) − z]` of §18.2 (3). -/
noncomputable def Feq (β θ : ℝ) (U f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv U (psi θ f x - y) - β * (1 - θ) * deriv f y * deriv U (psi θ f y - z)

/-- **Assumption 18.1** (pp. 547–548), with `K = [0, k̄]`.
a. `0 < β < 1`; b. `U` is `C²`, strictly increasing and strictly concave on `[0, ∞)`;
c. `0 < θ < 1`; d. `f` is `C²`, nonnegative, strictly increasing and strictly concave on
`[0, ∞)`, `f(0) > 0` and `f′(0) > 1/[β(1 − θ)]`; e. `ψ(k) − k > 0` on `(0, k̄)` and `< 0` on
`(k̄, ∞)`. -/
structure Assumption18_1 (β θ : ℝ) (U f : ℝ → ℝ) (kbar : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  U_contDiff : ContDiff ℝ 2 U
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  f_contDiff : ContDiff ℝ 2 f
  f_nonneg : ∀ k, 0 ≤ k → 0 ≤ f k
  f_strictMono : StrictMonoOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_zero_pos : 0 < f 0
  deriv_f_zero : 1 / (β * (1 - θ)) < deriv f 0
  kbar_pos : 0 < kbar
  psi_gt : ∀ k ∈ Ioo 0 kbar, k < psi θ f k
  psi_lt : ∀ k, kbar < k → psi θ f k < k

/-! ### Smoothness consequences of `C²` -/

/-- A `C²` function is differentiable. -/
theorem differentiable_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) : Differentiable ℝ u :=
  h.differentiable (by norm_num)

/-- The derivative of a `C²` function is differentiable. -/
theorem differentiable_deriv_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) :
    Differentiable ℝ (deriv u) :=
  h.differentiable_deriv_two

/-- The derivative of a `C²` function is continuous. -/
theorem continuous_deriv_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) : Continuous (deriv u) :=
  (differentiable_deriv_of_C2 h).continuous

/-- The second derivative of a `C²` function is continuous. -/
theorem continuous_deriv2_of_C2 {u : ℝ → ℝ} (h : ContDiff ℝ 2 u) :
    Continuous (deriv (deriv u)) :=
  ((contDiff_succ_iff_deriv (n := 1)).1 h).2.2.continuous_deriv_one

/-- `ψ′(x) = (1 − θ) f′(x) − θ x f″(x)`. -/
noncomputable def dpsi (θ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - θ) * deriv f x - θ * x * deriv (deriv f) x

/-- `ψ` has derivative `ψ′ = dpsi`. -/
theorem hasDerivAt_psi {θ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (psi θ f) (dpsi θ f x) x := by
  have h1 := (differentiable_of_C2 hf x).hasDerivAt
  have h2 := (differentiable_deriv_of_C2 hf x).hasDerivAt
  have h3 := ((hasDerivAt_id' x).const_mul θ).mul h2
  exact (h1.sub h3).congr_deriv (by simp only [dpsi]; ring)

/-- `ψ` is continuous. -/
theorem continuous_psi {θ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (psi θ f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_psi hf x).continuousAt

/-! ### Derived facts (F1)–(F4) -/

/-- A strictly increasing function, concave and differentiable on `[0, ∞)`, has a positive
derivative on `[0, ∞)` (fact (F1)). -/
theorem deriv_pos_of_strictMono_concave {u : ℝ → ℝ} (hm : StrictMonoOn u (Ici 0))
    (hc : ConcaveOn ℝ (Ici 0) u) (hd : Differentiable ℝ u) {c : ℝ} (h0 : 0 ≤ c) :
    0 < deriv u c := by
  by_contra hneg
  push Not at hneg
  have h1 := concave_le_tangent hc (by linarith : (0 : ℝ) ≤ c + 1) h0 (hd c)
  have h2 := hm (mem_Ici.2 h0) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c < c + 1)
  have e : c + 1 - c = 1 := by ring
  rw [e, mul_one] at h1
  linarith

/-- (F1) `U′ > 0` on `[0, ∞)`. -/
theorem Assumption18_1.deriv_U_pos {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {c : ℝ} (hc : 0 ≤ c) : 0 < deriv U c :=
  deriv_pos_of_strictMono_concave A.U_strictMono A.U_strictConcave.concaveOn
    (differentiable_of_C2 A.U_contDiff) hc

/-- (F1) `f′ > 0` on `[0, ∞)`. -/
theorem Assumption18_1.deriv_f_pos {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {k : ℝ} (hk : 0 ≤ k) : 0 < deriv f k :=
  deriv_pos_of_strictMono_concave A.f_strictMono A.f_strictConcave.concaveOn
    (differentiable_of_C2 A.f_contDiff) hk

/-- (F1) `f′` is strictly decreasing on `[0, ∞)`. -/
theorem Assumption18_1.deriv_f_strictAnti {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : StrictAntiOn (deriv f) (Ici 0) :=
  A.f_strictConcave.strictAntiOn_deriv fun x _ => differentiable_of_C2 A.f_contDiff x

/-- (F1) `U′` is strictly decreasing on `[0, ∞)`. -/
theorem Assumption18_1.deriv_U_strictAnti {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : StrictAntiOn (deriv U) (Ici 0) :=
  A.U_strictConcave.strictAntiOn_deriv fun x _ => differentiable_of_C2 A.U_contDiff x

/-- Part (d)'s `lim_{k→0} f′(k)` is `f′(0)`: `f′` is continuous. -/
theorem Assumption18_1.tendsto_deriv_f_zero {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) :
    Tendsto (deriv f) (𝓝[>] 0) (𝓝 (deriv f 0)) :=
  ((continuous_deriv_of_C2 A.f_contDiff).tendsto 0).mono_left nhdsWithin_le_nhds

/-- **Assumption 18.1 excludes the Inada condition of Assumption 18.2** (NOTE 18.3-A): since `U`
is `C²` up to `0`, `U′(c) → U′(0) < ∞` as `c → 0⁺`, so `U′(0⁺) = ∞` fails. (Relevant for §18.3,
which assumes both.) -/
theorem Assumption18_1.not_inada {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : ¬ Tendsto (deriv U) (𝓝[>] 0) atTop := by
  have hlim : Tendsto (deriv U) (𝓝[>] 0) (𝓝 (deriv U 0)) :=
    ((continuous_deriv_of_C2 A.U_contDiff).tendsto 0).mono_left nhdsWithin_le_nhds
  exact hlim.not_tendsto (disjoint_nhds_atTop _)

/-- (F2) `ψ(k̄) = k̄`. -/
theorem Assumption18_1.psi_kbar {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : psi θ f kbar = kbar := by
  have hc : Continuous fun k => psi θ f k - k := (continuous_psi A.f_contDiff).sub continuous_id
  have hle : psi θ f kbar - kbar ≤ 0 := by
    have hlim : Tendsto (fun k => psi θ f k - k) (𝓝[>] kbar) (𝓝 (psi θ f kbar - kbar)) :=
      (hc.tendsto kbar).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with k hk
    linarith [A.psi_lt k hk]
  have hge : 0 ≤ psi θ f kbar - kbar := by
    have hlim : Tendsto (fun k => psi θ f k - k) (𝓝[<] kbar) (𝓝 (psi θ f kbar - kbar)) :=
      (hc.tendsto kbar).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT A.kbar_pos] with k hk
    linarith [A.psi_gt k hk]
  linarith

/-- (F2) `k ≤ ψ(k)` on `K = [0, k̄]`: stationary consumption is nonnegative on `K`. -/
theorem Assumption18_1.le_psi {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {k : ℝ} (hk : k ∈ Icc 0 kbar) : k ≤ psi θ f k := by
  rcases eq_or_lt_of_le hk.1 with h | h
  · subst h
    simp only [psi, mul_zero, zero_mul, sub_zero]
    exact A.f_zero_pos.le
  rcases eq_or_lt_of_le hk.2 with h' | h'
  · rw [h', A.psi_kbar]
  · exact (A.psi_gt k ⟨h, h'⟩).le

/-- (F3) `f(k) ≥ f(0) + k f′(k)` on `[0, ∞)`, hence `ψ(k) > (1 − θ) k f′(k)`. -/
theorem Assumption18_1.psi_gt_mul {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) {k : ℝ} (hk : 0 ≤ k) :
    (1 - θ) * k * deriv f k < psi θ f k := by
  have h := concave_le_tangent A.f_strictConcave.concaveOn le_rfl hk
    (differentiable_of_C2 A.f_contDiff k)
  have := A.f_zero_pos
  simp only [psi]
  nlinarith

/-- (F3) `β(1 − θ) f′(k̄) < 1`. -/
theorem Assumption18_1.euler_kbar_lt {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) : β * (1 - θ) * deriv f kbar < 1 := by
  have h := A.psi_gt_mul A.kbar_pos.le
  rw [A.psi_kbar] at h
  have h1 : (1 - θ) * deriv f kbar < 1 := by
    by_contra hc
    push Not at hc
    nlinarith [A.kbar_pos]
  have := A.beta_pos
  have := A.beta_lt_one
  have h2 : 0 < (1 - θ) * deriv f kbar :=
    mul_pos (by linarith [A.theta_lt_one]) (A.deriv_f_pos A.kbar_pos.le)
  nlinarith

/-- (F4) There is a unique `k* ∈ (0, k̄)` with `β(1 − θ) f′(k*) = 1` (§18.2 (5)); it is also the
unique solution in `[0, ∞)`. -/
theorem Assumption18_1.exists_unique_kstar {β θ kbar : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) :
    ∃ ks ∈ Ioo 0 kbar, β * (1 - θ) * deriv f ks = 1 ∧
      ∀ k, 0 ≤ k → β * (1 - θ) * deriv f k = 1 → k = ks := by
  have hb : 0 < β * (1 - θ) := mul_pos A.beta_pos (by linarith [A.theta_lt_one])
  have h0 : 1 < β * (1 - θ) * deriv f 0 := by
    have := A.deriv_f_zero
    rw [div_lt_iff₀ hb] at this
    linarith
  have hcont : ContinuousOn (fun k => β * (1 - θ) * deriv f k) (Icc 0 kbar) :=
    (continuous_const.mul (continuous_deriv_of_C2 A.f_contDiff)).continuousOn
  obtain ⟨ks, hks, hval⟩ := intermediate_value_Icc' A.kbar_pos.le hcont
    ⟨A.euler_kbar_lt.le, h0.le⟩
  have hmono : StrictAntiOn (fun k => β * (1 - θ) * deriv f k) (Ici 0) :=
    fun x hx y hy hxy => mul_lt_mul_of_pos_left (A.deriv_f_strictAnti hx hy hxy) hb
  have hne0 : ks ≠ 0 := by
    rintro rfl
    simp only at hval
    linarith
  have hnek : ks ≠ kbar := by
    rintro rfl
    simp only at hval
    linarith [A.euler_kbar_lt]
  refine ⟨ks, ⟨lt_of_le_of_ne hks.1 (Ne.symm hne0), lt_of_le_of_ne hks.2 hnek⟩, hval,
    fun k hk hk1 => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono (mem_Ici.2 hk) (mem_Ici.2 hks.1) h
    simp only at this
    linarith
  · have := hmono (mem_Ici.2 hks.1) (mem_Ici.2 hk) h
    simp only at this
    linarith

/-- On the diagonal, `F(k, k, k) = U′[ψ(k) − k] (1 − β(1 − θ) f′(k))`. -/
theorem Feq_diag (β θ : ℝ) (U f : ℝ → ℝ) (k : ℝ) :
    Feq β θ U f k k k = deriv U (psi θ f k - k) * (1 - β * (1 - θ) * deriv f k) := by
  simp only [Feq]
  ring

/-! ### Proposition 18.1 -/

/-- **Proposition 18.1** (p. 548). Under Assumption 18.1, if `g` is continuous on
`K = [0, k̄]`, maps `K` into itself, and satisfies (4), `F[k, g(k), g²(k)] = 0` on `K`, then `g`
has exactly one fixed point in `K`, and it is the `k*` of (5): `β(1 − θ) f′(k*) = 1`.
The existence of a fixed point is Brouwer's theorem (Theorem 17.3). -/
theorem prop_18_1 {β θ kbar : ℝ} {U f g : ℝ → ℝ} (A : Assumption18_1 β θ U f kbar)
    (hgc : ContinuousOn g (Icc 0 kbar)) (hgm : MapsTo g (Icc 0 kbar) (Icc 0 kbar))
    (h4 : ∀ k ∈ Icc 0 kbar, Feq β θ U f k (g k) (g (g k)) = 0) :
    ∃ ks ∈ Ioo 0 kbar, β * (1 - θ) * deriv f ks = 1 ∧ g ks = ks ∧
      ∀ k ∈ Icc 0 kbar, g k = k → k = ks := by
  obtain ⟨ks, hks, hks1, hu⟩ := A.exists_unique_kstar
  have hfix : ∀ k ∈ Icc 0 kbar, g k = k → k = ks := by
    intro k hk hgk
    have h := h4 k hk
    rw [hgk, hgk, Feq_diag] at h
    have hpos : 0 < deriv U (psi θ f k - k) := A.deriv_U_pos (by linarith [A.le_psi hk])
    have h1 : 1 - β * (1 - θ) * deriv f k = 0 := by
      rcases mul_eq_zero.1 h with h2 | h2
      · exact absurd h2 hpos.ne'
      · exact h2
    exact hu k hk.1 (by linarith)
  obtain ⟨k, hk, hgk⟩ := brouwer isCompact_Icc (convex_Icc 0 kbar)
    ⟨0, ⟨le_rfl, A.kbar_pos.le⟩⟩ hgc hgm
  have hkks := hfix k hk hgk
  subst hkks
  exact ⟨k, hks, hks1, hgk, hfix⟩

/-! ### Partial derivatives of `F` and §18.2 (6a)–(6c) -/

/-- `F₁(x, y, z) = U″[ψ(x) − y] ψ′(x)`. -/
noncomputable def F1f (θ : ℝ) (U f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (deriv U) (psi θ f x - y) * dpsi θ f x

/-- `F₂(x, y, z) = −U″[ψ(x) − y] − β(1 − θ)(f″(y) U′[ψ(y) − z] + f′(y) U″[ψ(y) − z] ψ′(y))`. -/
noncomputable def F2f (β θ : ℝ) (U f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  -deriv (deriv U) (psi θ f x - y) - β * (1 - θ) * (deriv (deriv f) y * deriv U (psi θ f y - z) +
    deriv f y * (deriv (deriv U) (psi θ f y - z) * dpsi θ f y))

/-- `F₃(x, y, z) = β(1 − θ) f′(y) U″[ψ(y) − z]`. -/
noncomputable def F3f (β θ : ℝ) (U f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  β * (1 - θ) * deriv f y * deriv (deriv U) (psi θ f y - z)

/-- `∂F/∂x = F₁`. -/
theorem hasDerivAt_Feq_x {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x y z : ℝ) : HasDerivAt (fun x => Feq β θ U f x y z) (F1f θ U f x y) x := by
  have h1 := (differentiable_deriv_of_C2 hU (psi θ f x - y)).hasDerivAt
  have h2 := (hasDerivAt_psi (θ := θ) hf x).sub_const y
  exact (h1.comp x h2).sub_const (β * (1 - θ) * deriv f y * deriv U (psi θ f y - z))

/-- `∂F/∂y = F₂`. -/
theorem hasDerivAt_Feq_y {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x y z : ℝ) : HasDerivAt (fun y => Feq β θ U f x y z) (F2f β θ U f x y z) y := by
  have h1 := (differentiable_deriv_of_C2 hU (psi θ f x - y)).hasDerivAt
  have h2 : HasDerivAt (fun y => psi θ f x - y) (-1) y := by
    simpa using (hasDerivAt_id' y).const_sub (psi θ f x)
  have h3 := h1.comp y h2
  have h4 := ((differentiable_deriv_of_C2 hf y).hasDerivAt).const_mul (β * (1 - θ))
  have h5 := (differentiable_deriv_of_C2 hU (psi θ f y - z)).hasDerivAt
  have h6 := h5.comp y ((hasDerivAt_psi (θ := θ) hf y).sub_const z)
  exact (h3.sub (h4.mul h6)).congr_deriv (by simp only [F2f, Function.comp_apply]; ring)

/-- `∂F/∂z = F₃`. -/
theorem hasDerivAt_Feq_z {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (x y z : ℝ) :
    HasDerivAt (fun z => Feq β θ U f x y z) (F3f β θ U f y z) z := by
  have h5 := (differentiable_deriv_of_C2 hU (psi θ f y - z)).hasDerivAt
  have h2 : HasDerivAt (fun z => psi θ f y - z) (-1) z := by
    simpa using (hasDerivAt_id' z).const_sub (psi θ f y)
  have h6 := h5.comp z h2
  have h7 := (h6.const_mul (β * (1 - θ) * deriv f y)).const_sub (deriv U (psi θ f x - y))
  exact h7.congr_deriv (by simp only [F3f]; ring)

/-- Stationary consumption `c* = ψ(k*) − k*`. -/
noncomputable def cstar (θ : ℝ) (f : ℝ → ℝ) (ks : ℝ) : ℝ := psi θ f ks - ks

/-- §18.2 (6a): `F₁* = U″(c*)[β⁻¹ − θ k* f″(k*)]`. -/
noncomputable def F1s (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  deriv (deriv U) (cstar θ f ks) * (β⁻¹ - θ * ks * deriv (deriv f) ks)

/-- §18.2 (6b): `F₂* = −U″(c*)[1 + β⁻¹ − θ k* f″(k*)] − β(1 − θ) f″(k*) U′(c*)`. -/
noncomputable def F2s (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  -deriv (deriv U) (cstar θ f ks) * (1 + β⁻¹ - θ * ks * deriv (deriv f) ks) -
    β * (1 - θ) * deriv (deriv f) ks * deriv U (cstar θ f ks)

/-- §18.2 (6c): `F₃* = U″(c*)`. -/
noncomputable def F3s (U : ℝ → ℝ) (θ : ℝ) (f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  deriv (deriv U) (cstar θ f ks)

/-- `ψ′(k*) = β⁻¹ − θ k* f″(k*)` when `β(1 − θ) f′(k*) = 1`. -/
theorem dpsi_star {β θ ks : ℝ} {f : ℝ → ℝ} (hβ : 0 < β) (heul : β * (1 - θ) * deriv f ks = 1) :
    dpsi θ f ks = β⁻¹ - θ * ks * deriv (deriv f) ks := by
  have h : (1 - θ) * deriv f ks = β⁻¹ := by
    field_simp
    linarith
  simp only [dpsi, h]

/-- (6a) verified: `F₁(k*, k*, k*) = F₁*`. -/
theorem F1f_star {β θ ks : ℝ} {U f : ℝ → ℝ} (hβ : 0 < β)
    (heul : β * (1 - θ) * deriv f ks = 1) : F1f θ U f ks ks = F1s β θ U f ks := by
  simp only [F1f, F1s, cstar, dpsi_star hβ heul]

/-- (6b) verified: `F₂(k*, k*, k*) = F₂*`. -/
theorem F2f_star {β θ ks : ℝ} {U f : ℝ → ℝ} (hβ : 0 < β)
    (heul : β * (1 - θ) * deriv f ks = 1) : F2f β θ U f ks ks ks = F2s β θ U f ks := by
  simp only [F2f, F2s, cstar, dpsi_star hβ heul]
  linear_combination (-(deriv (deriv U) (psi θ f ks - ks) *
    (β⁻¹ - θ * ks * deriv (deriv f) ks))) * heul

/-- (6c) verified: `F₃(k*, k*, k*) = F₃*`. -/
theorem F3f_star {β θ ks : ℝ} {U f : ℝ → ℝ} (heul : β * (1 - θ) * deriv f ks = 1) :
    F3f β θ U f ks ks = F3s U θ f ks := by
  simp only [F3f, F3s, cstar, heul, one_mul]

/-! ### The hypotheses of the local analysis -/

/-- **Hypotheses of the local analysis.** Assumption 18.1 as used near the steady state, with
`k* > 0` solving (5), `U′(c*) > 0`, and the added hypotheses (NOTE 18.2-B) `U″(c*) < 0`,
`f″(k*) < 0`. -/
structure LocalHyp (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  U_contDiff : ContDiff ℝ 2 U
  f_contDiff : ContDiff ℝ 2 f
  ks_pos : 0 < ks
  euler : β * (1 - θ) * deriv f ks = 1
  deriv_U_pos : 0 < deriv U (cstar θ f ks)
  deriv2_U_neg : deriv (deriv U) (cstar θ f ks) < 0
  deriv2_f_neg : deriv (deriv f) ks < 0

/-- Assumption 18.1, the steady state `k* ∈ (0, k̄)` of (5) and the added hypotheses
`U″(c*) < 0`, `f″(k*) < 0` give `LocalHyp`. -/
theorem Assumption18_1.localHyp {β θ kbar ks : ℝ} {U f : ℝ → ℝ}
    (A : Assumption18_1 β θ U f kbar) (hks : ks ∈ Ioo 0 kbar)
    (heul : β * (1 - θ) * deriv f ks = 1) (hU2 : deriv (deriv U) (cstar θ f ks) < 0)
    (hf2 : deriv (deriv f) ks < 0) : LocalHyp β θ U f ks where
  beta_pos := A.beta_pos
  beta_lt_one := A.beta_lt_one
  theta_pos := A.theta_pos
  theta_lt_one := A.theta_lt_one
  U_contDiff := A.U_contDiff
  f_contDiff := A.f_contDiff
  ks_pos := hks.1
  euler := heul
  deriv_U_pos := A.deriv_U_pos (by
    have := A.le_psi ⟨hks.1.le, hks.2.le⟩
    simp only [cstar]
    linarith)
  deriv2_U_neg := hU2
  deriv2_f_neg := hf2

/-- `F₁* < 0`. -/
theorem LocalHyp.F1s_neg {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    F1s β θ U f ks < 0 := by
  have h1 : 0 < β⁻¹ - θ * ks * deriv (deriv f) ks := by
    have := inv_pos.2 L.beta_pos
    have := mul_pos L.theta_pos L.ks_pos
    nlinarith [L.deriv2_f_neg]
  exact mul_neg_of_neg_of_pos L.deriv2_U_neg h1

/-- `F₃* < 0`. -/
theorem LocalHyp.F3s_neg {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    F3s U θ f ks < 0 :=
  L.deriv2_U_neg

/-- `F₂* > 0`. -/
theorem LocalHyp.F2s_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < F2s β θ U f ks := by
  have h1 : 0 < 1 + β⁻¹ - θ * ks * deriv (deriv f) ks := by
    have := inv_pos.2 L.beta_pos
    have := mul_pos L.theta_pos L.ks_pos
    nlinarith [L.deriv2_f_neg]
  have h2 : 0 < -deriv (deriv U) (cstar θ f ks) * (1 + β⁻¹ - θ * ks * deriv (deriv f) ks) :=
    mul_pos (by linarith [L.deriv2_U_neg]) h1
  have h3 : 0 < β * (1 - θ) := mul_pos L.beta_pos (by linarith [L.theta_lt_one])
  have h4 : β * (1 - θ) * deriv (deriv f) ks * deriv U (cstar θ f ks) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h3 L.deriv2_f_neg) L.deriv_U_pos
  simp only [F2s]
  linarith

/-! ### The characteristic polynomial -/

/-- The characteristic polynomial `P(λ) = F₁* + F₂* λ + F₃* λ²` (p. 549). -/
noncomputable def charPoly (β θ : ℝ) (U f : ℝ → ℝ) (ks l : ℝ) : ℝ :=
  F1s β θ U f ks + F2s β θ U f ks * l + F3s U θ f ks * l ^ 2

/-- The discriminant `F₂*² − 4 F₁* F₃*`. -/
noncomputable def charDisc (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  F2s β θ U f ks ^ 2 - 4 * F1s β θ U f ks * F3s U θ f ks

/-- The smaller root `λ* = (−F₂* + √D)/(2F₃*)` (`F₃* < 0`). -/
noncomputable def lamStar (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  (-F2s β θ U f ks + Real.sqrt (charDisc β θ U f ks)) / (2 * F3s U θ f ks)

/-- The larger root `λ₂ = (−F₂* − √D)/(2F₃*)`. -/
noncomputable def lamTwo (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) : ℝ :=
  (-F2s β θ U f ks - Real.sqrt (charDisc β θ U f ks)) / (2 * F3s U θ f ks)

/-- `P(1) = −β(1 − θ) f″(k*) U′(c*)` (p. 549). -/
theorem charPoly_one (β θ : ℝ) (U f : ℝ → ℝ) (ks : ℝ) :
    charPoly β θ U f ks 1 = -(β * (1 - θ) * deriv (deriv f) ks * deriv U (cstar θ f ks)) := by
  simp only [charPoly, F1s, F2s, F3s]
  ring

/-- `P(1) > 0`. -/
theorem LocalHyp.charPoly_one_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < charPoly β θ U f ks 1 := by
  rw [charPoly_one]
  have h3 : 0 < β * (1 - θ) := mul_pos L.beta_pos (by linarith [L.theta_lt_one])
  have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h3 L.deriv2_f_neg) L.deriv_U_pos
  linarith

/-- `P(0) = F₁* < 0`. -/
theorem LocalHyp.charPoly_zero_neg {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    charPoly β θ U f ks 0 < 0 := by
  simpa [charPoly] using L.F1s_neg

/-- `F₁*/F₃* = β⁻¹ − θ k* f″(k*) > 1`. -/
theorem LocalHyp.one_lt_F1s_div_F3s {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    1 < F1s β θ U f ks / F3s U θ f ks := by
  have hne : F3s U θ f ks ≠ 0 := L.F3s_neg.ne
  have e : F1s β θ U f ks / F3s U θ f ks = β⁻¹ - θ * ks * deriv (deriv f) ks := by
    simp only [F1s, F3s]
    exact mul_div_cancel_left₀ _ hne
  rw [e]
  have h1 : 1 < β⁻¹ := one_lt_inv₀ L.beta_pos |>.2 L.beta_lt_one
  have := mul_pos L.theta_pos L.ks_pos
  nlinarith [L.deriv2_f_neg]

/-- `P(F₁*/F₃*) = (F₁*/F₃*) P(1)` (NOTE 18.2-C). -/
theorem charPoly_F1_div_F3 {β θ ks : ℝ} {U f : ℝ → ℝ} (hne : F3s U θ f ks ≠ 0) :
    charPoly β θ U f ks (F1s β θ U f ks / F3s U θ f ks) =
      F1s β θ U f ks / F3s U θ f ks * charPoly β θ U f ks 1 := by
  simp only [charPoly]
  field_simp
  ring

/-- **Roots of the characteristic polynomial** (p. 549). Under `LocalHyp`: `D > 0`,
`P(λ) = F₃*(λ − λ*)(λ − λ₂)`, `0 < λ* < 1 < λ₂`, `P(λ*) = P(λ₂) = 0`, `P > 0` on `(λ*, λ₂)`,
and `λ* < F₁*/F₃* < λ₂`. -/
theorem LocalHyp.charPoly_roots {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < charDisc β θ U f ks ∧
      (∀ l, charPoly β θ U f ks l =
        F3s U θ f ks * (l - lamStar β θ U f ks) * (l - lamTwo β θ U f ks)) ∧
      0 < lamStar β θ U f ks ∧ lamStar β θ U f ks < 1 ∧ 1 < lamTwo β θ U f ks ∧
      (∀ l, lamStar β θ U f ks < l → l < lamTwo β θ U f ks → 0 < charPoly β θ U f ks l) ∧
      lamStar β θ U f ks < F1s β θ U f ks / F3s U θ f ks ∧
      F1s β θ U f ks / F3s U θ f ks < lamTwo β θ U f ks := by
  set F1 := F1s β θ U f ks with hF1
  set F2 := F2s β θ U f ks with hF2
  set F3 := F3s U θ f ks with hF3
  set D := charDisc β θ U f ks with hD
  have hF3n : F3 < 0 := L.F3s_neg
  have hF3ne : F3 ≠ 0 := hF3n.ne
  have hP1 := L.charPoly_one_pos
  have hP0 := L.charPoly_zero_neg
  simp only [charPoly] at hP1 hP0
  rw [← hF1, ← hF2, ← hF3] at hP1 hP0
  have hDpos : 0 < D := by
    have e : D = (2 * F3 + F2) ^ 2 - 4 * F3 * (F1 + F2 * 1 + F3 * 1 ^ 2) := by
      simp only [hD, charDisc, ← hF1, ← hF2, ← hF3]
      ring
    rw [e]
    nlinarith [sq_nonneg (2 * F3 + F2)]
  have hs : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
  have hsq : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  set r1 := lamStar β θ U f ks with hr1
  set r2 := lamTwo β θ U f ks with hr2
  have hr1e : r1 = (-F2 + Real.sqrt D) / (2 * F3) := rfl
  have hr2e : r2 = (-F2 - Real.sqrt D) / (2 * F3) := rfl
  have hD' : D = F2 ^ 2 - 4 * F1 * F3 := rfl
  have hnum : (-F2 + Real.sqrt D) * (-F2 - Real.sqrt D) = 4 * F1 * F3 := by
    linear_combination (-1) * hs - hD'
  have hsum : F3 * (r1 + r2) = -F2 := by
    rw [hr1e, hr2e]
    field_simp
    ring
  have hprod : F3 * (r1 * r2) = F1 := by
    rw [hr1e, hr2e, div_mul_div_comm, hnum]
    field_simp
    ring
  have hfac : ∀ l, F1 + F2 * l + F3 * l ^ 2 = F3 * (l - r1) * (l - r2) := by
    intro l
    calc F1 + F2 * l + F3 * l ^ 2 = F3 * l ^ 2 - (-F2) * l + F1 := by ring
      _ = F3 * l ^ 2 - F3 * (r1 + r2) * l + F3 * (r1 * r2) := by rw [hsum, hprod]
      _ = F3 * (l - r1) * (l - r2) := by ring
  have hr12 : r1 < r2 := by
    have e : r2 - r1 = -Real.sqrt D / F3 := by
      rw [hr1e, hr2e]
      field_simp
      ring
    have : 0 < -Real.sqrt D / F3 := div_pos_iff.2 (Or.inr ⟨by linarith, hF3n⟩)
    linarith
  have h1 := hfac 1
  have h0 := hfac 0
  have hprod1 : (1 - r1) * (1 - r2) < 0 := by
    have e : F3 * (1 - r1) * (1 - r2) = F3 * ((1 - r1) * (1 - r2)) := by ring
    rw [e] at h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (neg_nonneg.2 hF3n.le) hc]
  have hr1lt : r1 < 1 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (1 - r1) * (1 - r2) := mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith)
    linarith
  have hr2gt : 1 < r2 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (1 - r1) * (1 - r2) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hprod0 : 0 < r1 * r2 := by
    have e : F3 * (0 - r1) * (0 - r2) = F3 * (r1 * r2) := by ring
    rw [e] at h0
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (neg_nonneg.2 hF3n.le) (neg_nonneg.2 hc)]
  have hr1pos : 0 < r1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hpos : ∀ l, r1 < l → l < r2 → 0 < F1 + F2 * l + F3 * l ^ 2 := by
    intro l hl1 hl2
    rw [hfac l]
    have : (l - r1) * (l - r2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have e : F3 * (l - r1) * (l - r2) = F3 * ((l - r1) * (l - r2)) := by ring
    rw [e]
    exact mul_pos_of_neg_of_neg hF3n this
  have hq1 : 1 < F1 / F3 := L.one_lt_F1s_div_F3s
  have hq : 0 < F1 / F3 * (F1 + F2 * 1 + F3 * 1 ^ 2) := mul_pos (by linarith) hP1
  have hPq := charPoly_F1_div_F3 (β := β) (U := U) hF3ne
  simp only [charPoly] at hPq
  rw [← hF1, ← hF2, ← hF3] at hPq
  have hqlt : F1 / F3 < r2 := by
    by_contra hc
    push Not at hc
    have hX : 0 ≤ (F1 / F3 - r1) * (F1 / F3 - r2) := mul_nonneg (by linarith) (by linarith)
    have e := hfac (F1 / F3)
    have e2 : F3 * (F1 / F3 - r1) * (F1 / F3 - r2) =
        F3 * ((F1 / F3 - r1) * (F1 / F3 - r2)) := by ring
    rw [e2] at e
    nlinarith [mul_nonneg (neg_nonneg.2 hF3n.le) hX]
  refine ⟨hDpos, fun l => hfac l, hr1pos, hr1lt, hr2gt, hpos, by linarith, hqlt⟩

/-- For `λ ∈ (λ*, 1]`, `P(λ) > 0`. -/
theorem LocalHyp.charPoly_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {l : ℝ}
    (hl : lamStar β θ U f ks < l) (hl1 : l ≤ 1) : 0 < charPoly β θ U f ks l := by
  obtain ⟨-, -, -, -, h2, hpos, -⟩ := L.charPoly_roots
  exact hpos l hl (by linarith)

/-- `H₁* = −F₁*/F₂* > 0` (p. 549). -/
theorem LocalHyp.H1s_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < -F1s β θ U f ks / F2s β θ U f ks :=
  div_pos (by linarith [L.F1s_neg]) L.F2s_pos

/-- `H₂* = −F₃*/F₂* > 0` (p. 549). -/
theorem LocalHyp.H2s_pos {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    0 < -F3s U θ f ks / F2s β θ U f ks :=
  div_pos (by linarith [L.F3s_neg]) L.F2s_pos

/-- `H₁* + H₂* λ² < λ ⇔ P(λ) > 0` (proof of Proposition 18.2); in particular for
`λ ∈ (λ*, 1]`. -/
theorem LocalHyp.H_lt_lam {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {l : ℝ}
    (hl : lamStar β θ U f ks < l) (hl1 : l ≤ 1) :
    -F1s β θ U f ks / F2s β θ U f ks + -F3s U θ f ks / F2s β θ U f ks * l ^ 2 < l := by
  have hP := L.charPoly_pos hl hl1
  have hF2 := L.F2s_pos
  simp only [charPoly] at hP
  have e : -F1s β θ U f ks / F2s β θ U f ks + -F3s U θ f ks / F2s β θ U f ks * l ^ 2 =
      (-F1s β θ U f ks - F3s U θ f ks * l ^ 2) / F2s β θ U f ks := by ring
  rw [e, div_lt_iff₀ hF2]
  linarith

/-- `H₁* + H₂* < 1 ⇔ P(1) > 0` (NOTE 18.2-H). -/
theorem LocalHyp.H_sum_lt_one {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    -F1s β θ U f ks / F2s β θ U f ks + -F3s U θ f ks / F2s β θ U f ks < 1 := by
  have h := L.H_lt_lam (l := 1) (L.charPoly_roots.2.2.2.1) le_rfl
  rwa [one_pow, mul_one] at h

/-- **The corrected step of Proposition 18.3** (NOTE 18.2-E): `H₂*(1 + λ) < 1` for every
`λ ≤ 1`; indeed `H₂*(1 + λ) < H₁* + H₂* < 1` for `λ < 1 < F₁*/F₃*`. -/
theorem LocalHyp.H2s_mul_lt_one {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {l : ℝ}
    (hl1 : l ≤ 1) : -F3s U θ f ks / F2s β θ U f ks * (1 + l) < 1 := by
  have hF2 := L.F2s_pos
  have hq := L.one_lt_F1s_div_F3s
  have hF3 := L.F3s_neg
  have hP1 := L.charPoly_one_pos
  simp only [charPoly] at hP1
  have hF1F3 : F1s β θ U f ks < F3s U θ f ks * l := by
    rw [lt_div_iff_of_neg hF3] at hq
    nlinarith
  have e : -F3s U θ f ks / F2s β θ U f ks * (1 + l) =
      (-F3s U θ f ks * (1 + l)) / F2s β θ U f ks := by ring
  rw [e, div_lt_iff₀ hF2]
  linarith

/-! ### NOTE 18.2-B: strict concavity does not give a negative second derivative -/

/-- The function `U_{c₀}(c) = −e^{−c}((c − c₀)² + 4(c − c₀) + 6)`. -/
noncomputable def flatU (c₀ c : ℝ) : ℝ := -Real.exp (-c) * ((c - c₀) ^ 2 + 4 * (c - c₀) + 6)

/-- `U_{c₀}′(c) = e^{−c}((c − c₀)² + 2(c − c₀) + 2)`. -/
theorem hasDerivAt_flatU (c₀ c : ℝ) :
    HasDerivAt (flatU c₀) (Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2)) c := by
  have h1 : HasDerivAt (fun c => -Real.exp (-c)) (Real.exp (-c)) c := by
    simpa using ((hasDerivAt_neg c).exp).fun_neg
  have h2 : HasDerivAt (fun c => (c - c₀) ^ 2 + 4 * (c - c₀) + 6) (2 * (c - c₀) + 4) c := by
    have := ((((hasDerivAt_id' c).sub_const c₀).pow 2).add
      (((hasDerivAt_id' c).sub_const c₀).const_mul 4)).add_const 6
    exact this.congr_deriv (by simp)
  exact (h1.mul h2).congr_deriv (by ring)

/-- `U_{c₀}″(c) = −(c − c₀)² e^{−c}`. -/
theorem hasDerivAt_deriv_flatU (c₀ c : ℝ) :
    HasDerivAt (deriv (flatU c₀)) (-(c - c₀) ^ 2 * Real.exp (-c)) c := by
  have e : deriv (flatU c₀) = fun c => Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2) :=
    funext fun c => (hasDerivAt_flatU c₀ c).deriv
  rw [e]
  have h1 : HasDerivAt (fun c => Real.exp (-c)) (Real.exp (-c) * (-1)) c :=
    (hasDerivAt_neg c).exp
  have h2 : HasDerivAt (fun c => (c - c₀) ^ 2 + 2 * (c - c₀) + 2) (2 * (c - c₀) + 2) c := by
    have := ((((hasDerivAt_id' c).sub_const c₀).pow 2).add
      (((hasDerivAt_id' c).sub_const c₀).const_mul 2)).add_const 2
    exact this.congr_deriv (by simp)
  exact (h1.mul h2).congr_deriv (by ring)

/-- **Strict concavity does not give `U″ < 0`** (NOTE 18.2-B). For every `c₀`, the function
`U_{c₀}` is `C²` (indeed `C^∞`), strictly increasing and strictly concave on `ℝ` (so it
satisfies Assumption 18.1(b)), and `U_{c₀}″(c₀) = 0`. -/
theorem strictConcave_deriv2_zero_counterexample (c₀ : ℝ) :
    ContDiff ℝ 2 (flatU c₀) ∧ StrictMono (flatU c₀) ∧ StrictConcaveOn ℝ univ (flatU c₀) ∧
      deriv (deriv (flatU c₀)) c₀ = 0 := by
  have hd : ∀ c, deriv (flatU c₀) c = Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2) :=
    fun c => (hasDerivAt_flatU c₀ c).deriv
  have hpos : ∀ c, 0 < deriv (flatU c₀) c := fun c => by
    rw [hd]
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg (c - c₀ + 1)])
  have hcont : Continuous (flatU c₀) := by
    unfold flatU
    fun_prop
  have hd2 : ∀ c, deriv (deriv (flatU c₀)) c = -(c - c₀) ^ 2 * Real.exp (-c) :=
    fun c => (hasDerivAt_deriv_flatU c₀ c).deriv
  have hdc : Continuous (deriv (flatU c₀)) := by
    rw [show deriv (flatU c₀) = fun c => Real.exp (-c) * ((c - c₀) ^ 2 + 2 * (c - c₀) + 2)
      from funext hd]
    fun_prop
  -- `U′` is strictly decreasing: on `(-∞, c₀]` and on `[c₀, ∞)` separately.
  have hanti1 : StrictAntiOn (deriv (flatU c₀)) (Iic c₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic c₀) hdc.continuousOn fun c hc => ?_
    rw [interior_Iic] at hc
    rw [hd2]
    have : 0 < (c - c₀) ^ 2 := by nlinarith [mem_Iio.1 hc]
    nlinarith [Real.exp_pos (-c)]
  have hanti2 : StrictAntiOn (deriv (flatU c₀)) (Ici c₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici c₀) hdc.continuousOn fun c hc => ?_
    rw [interior_Ici] at hc
    rw [hd2]
    have : 0 < (c - c₀) ^ 2 := by nlinarith [mem_Ioi.1 hc]
    nlinarith [Real.exp_pos (-c)]
  have hanti : StrictAnti (deriv (flatU c₀)) := by
    intro x y hxy
    rcases le_or_gt y c₀ with hy | hy
    · exact hanti1 (mem_Iic.2 (by linarith)) (mem_Iic.2 hy) hxy
    rcases le_or_gt c₀ x with hx | hx
    · exact hanti2 (mem_Ici.2 hx) (mem_Ici.2 (by linarith)) hxy
    exact (hanti2 (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy).trans
      (hanti1 (mem_Iic.2 hx.le) (mem_Iic.2 le_rfl) hx)
  refine ⟨?_, strictMono_of_deriv_pos hpos, hanti.strictConcaveOn_univ_of_deriv hcont,
    by rw [hd2]; ring⟩
  unfold flatU
  fun_prop

/-- **Degenerate case `U″(c*) = 0`** (NOTE 18.2-B): then `F₁* = F₃* = 0`, `P(0) = 0` (so the
book's `P(0) < 0` fails) and `P(λ) = F₂* λ` is linear with root `0`. -/
theorem charPoly_degenerate_U {β θ ks : ℝ} {U f : ℝ → ℝ}
    (h : deriv (deriv U) (cstar θ f ks) = 0) :
    F1s β θ U f ks = 0 ∧ F3s U θ f ks = 0 ∧ charPoly β θ U f ks 0 = 0 ∧
      ∀ l, charPoly β θ U f ks l = F2s β θ U f ks * l := by
  have h1 : F1s β θ U f ks = 0 := by simp [F1s, h]
  have h3 : F3s U θ f ks = 0 := h
  exact ⟨h1, h3, by simp [charPoly, h1, h3], fun l => by simp [charPoly, h1, h3]⟩

/-- **Degenerate case `f″(k*) = 0`** (NOTE 18.2-B): then `P(1) = 0`, so the book's `P(1) > 0`
fails and `λ = 1` is a root. -/
theorem charPoly_degenerate_f {β θ ks : ℝ} {U f : ℝ → ℝ} (h : deriv (deriv f) ks = 0) :
    charPoly β θ U f ks 1 = 0 := by
  rw [charPoly_one, h]
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The local implicit function `H` of §18.2 (7)

SLP §18.2, p. 549. Since `F₂* > 0`, the book applies the Implicit Function Theorem to get an open
interval `I ∋ k*` and a `C¹` function `H : I × I → ℝ` with `F[x, H(x, z), z] = 0` (§18.2 (7)),
`H(k*, k*) = k*`, and partial derivatives `H₁* = −F₁*/F₂* > 0`, `H₂* = −F₃*/F₂* > 0` at
`(k*, k*)`. The later proofs use `H` only through: (7); the uniqueness of the root near `k*`;
continuity; monotonicity in each argument; and, for every `m₁ > H₁*`, `m₂ > H₂*`, the bound
`|H(x, z) − H(x′, z′)| ≤ m₁|x − x′| + m₂|z − z′|` on a small square `I_ε × I_ε` (which the book
gets from the continuity of `H₁, H₂` and the mean value theorem). These properties are collected
in `LocalSolution`, and `exists_localSolution` constructs such an `H` directly: the middle
argument of `F` is solved by the intermediate value theorem, and the Lipschitz bounds come from
bounds on the partial derivatives of `F` near `(k*, k*, k*)`.

* `Jint p ρ = [p − ρ, p + ρ]`; `clampI` is the nearest-point map onto it.
* `abs_sub_le_of_hasDerivAt`, `mul_sub_le_of_hasDerivAt`: mean value inequalities.
* `root_sep`: if `∂_y G ≥ a > 0`, `|∂_x G| ≤ b₁`, `|∂_z G| ≤ b₃` on a cube and
  `G(x, y, z) = G(x′, y′, z′) = 0` there, then `a|y − y′| ≤ b₁|x − x′| + b₃|z − z′|`.
* `root_exists`: solvability of `G(x, ·, z) = 0` near `(p, p, p)`.
* `implicitRoot`: the root, chosen by `Classical.epsilon`, of `G(clamp x, ·, clamp z) = 0`.
* `LocalHyp.exists_cube`: bounds on `F₁, F₂, F₃` near `(k*, k*, k*)`.
* `LocalSolution`, `exists_localSolution` (**§18.2 (7)**).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- The closed interval `[p − ρ, p + ρ]`. -/
abbrev Jint (p ρ : ℝ) : Set ℝ := Icc (p - ρ) (p + ρ)

/-- Nearest-point map onto `[p − δ, p + δ]`. -/
noncomputable def clampI (p δ x : ℝ) : ℝ := max (p - δ) (min (p + δ) x)

/-- `clampI` maps into `[p − δ, p + δ]` when `δ ≥ 0`. -/
theorem clampI_mem {p δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : clampI p δ x ∈ Jint p δ :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- `clampI` is the identity on `[p − δ, p + δ]`. -/
theorem clampI_of_mem {p δ x : ℝ} (hx : x ∈ Jint p δ) : clampI p δ x = x := by
  simp only [clampI, min_eq_right hx.2, max_eq_right hx.1]

/-- `clampI` is `1`-Lipschitz. -/
theorem abs_clampI_sub_le (p δ x x' : ℝ) : |clampI p δ x - clampI p δ x'| ≤ |x - x'| := by
  simp only [clampI]
  rw [max_comm (p - δ), max_comm (p - δ)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- Membership in a smaller interval. -/
theorem Jint_mono {p δ ρ x : ℝ} (h : δ ≤ ρ) (hx : x ∈ Jint p δ) : x ∈ Jint p ρ :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The centre lies in `[p − ρ, p + ρ]` for `ρ ≥ 0`. -/
theorem center_mem_Jint {p ρ : ℝ} (h : 0 ≤ ρ) : p ∈ Jint p ρ := ⟨by linarith, by linarith⟩

/-- `x ∈ [p − ρ, p + ρ] ↔ |x − p| ≤ ρ`. -/
theorem mem_Jint_iff {p ρ x : ℝ} : x ∈ Jint p ρ ↔ |x - p| ≤ ρ := by
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Mean value inequalities -/

/-- **Mean value inequality.** If `φ′ = φ'` with `|φ'| ≤ C` on an interval `s`, then
`|φ(v) − φ(u)| ≤ C |v − u|` for `u, v ∈ s`. -/
theorem abs_sub_le_of_hasDerivAt {φ φ' : ℝ → ℝ} {s : Set ℝ} {C u v : ℝ} (hs : Convex ℝ s)
    (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t) (hb : ∀ t ∈ s, |φ' t| ≤ C) (hu : u ∈ s)
    (hv : v ∈ s) : |φ v - φ u| ≤ C * |v - u| :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t ht => (hφ t ht).hasDerivWithinAt)
    hb hu hv

/-- **Lower mean value inequality.** If `φ′ = φ' ≥ a` on a closed interval `s`, then
`a (v − u) ≤ φ(v) − φ(u)` for `u ≤ v` in `s`. -/
theorem mul_sub_le_of_hasDerivAt {φ φ' : ℝ → ℝ} {c d a u v : ℝ}
    (hφ : ∀ t ∈ Icc c d, HasDerivAt φ (φ' t) t) (hb : ∀ t ∈ Icc c d, a ≤ φ' t)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u ≤ v) : a * (v - u) ≤ φ v - φ u := by
  refine (convex_Icc c d).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => ?_) u hu v hv huv
  rw [(hφ t (interior_subset ht)).deriv]
  exact hb t (interior_subset ht)

/-! ### Roots of `G(x, ·, z) = 0` -/

/-- **Separation of roots.** Let `G` have partial derivatives `G₁, G₂, G₃` everywhere, with
`G₂ ≥ a`, `|G₁| ≤ b₁`, `|G₃| ≤ b₃` on the cube `J³`, `J = [p − ρ, p + ρ]`. If `G(x, y, z) = 0` and
`G(x′, y′, z′) = 0` with all coordinates in `J`, then `a|y − y′| ≤ b₁|x − x′| + b₃|z − z′|`. -/
theorem root_sep {G G1 G2 G3 : ℝ → ℝ → ℝ → ℝ} {p ρ a b1 b3 : ℝ}
    (h1 : ∀ x y z, HasDerivAt (fun x => G x y z) (G1 x y z) x)
    (h2 : ∀ x y z, HasDerivAt (fun y => G x y z) (G2 x y z) y)
    (h3 : ∀ x y z, HasDerivAt (fun z => G x y z) (G3 x y z) z)
    (ha : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, a ≤ G2 x y z)
    (hb1 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G1 x y z| ≤ b1)
    (hb3 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G3 x y z| ≤ b3)
    {x x' y y' z z' : ℝ} (hx : x ∈ Jint p ρ) (hx' : x' ∈ Jint p ρ) (hy : y ∈ Jint p ρ)
    (hy' : y' ∈ Jint p ρ) (hz : z ∈ Jint p ρ) (hz' : z' ∈ Jint p ρ)
    (h0 : G x y z = 0) (h0' : G x' y' z' = 0) :
    a * |y - y'| ≤ b1 * |x - x'| + b3 * |z - z'| := by
  have e1 : |G x' y' z' - G x y' z'| ≤ b1 * |x' - x| :=
    abs_sub_le_of_hasDerivAt (φ := fun t => G t y' z') (convex_Icc _ _)
      (fun t _ => h1 t y' z') (fun t ht => hb1 t ht y' hy' z' hz') hx hx'
  have e3 : |G x y' z' - G x y' z| ≤ b3 * |z' - z| :=
    abs_sub_le_of_hasDerivAt (φ := fun t => G x y' t) (convex_Icc _ _)
      (fun t _ => h3 x y' t) (fun t ht => hb3 x hx y' hy' t ht) hz hz'
  rw [abs_sub_comm x' x] at e1
  rw [abs_sub_comm z' z] at e3
  have e1' := abs_le.1 e1
  have e3' := abs_le.1 e3
  rcases le_total y' y with hle | hle
  · have e2 := mul_sub_le_of_hasDerivAt (φ := fun t => G x t z) (fun t _ => h2 x t z)
      (fun t ht => ha x hx t ht z hz) hy' hy hle
    rw [abs_of_nonneg (by linarith : 0 ≤ y - y')]
    linarith
  · have e2 := mul_sub_le_of_hasDerivAt (φ := fun t => G x t z) (fun t _ => h2 x t z)
      (fun t ht => ha x hx t ht z hz) hy hy' hle
    rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ y' - y)]
    linarith

/-- **Existence of a root.** Under the hypotheses of `root_sep`, with `G(p, p, p) = 0`, `a > 0`,
`0 < r ≤ ρ`, `0 ≤ δ ≤ ρ` and `(b₁ + b₃)δ < a r`: for `x, z ∈ [p − δ, p + δ]` there is
`y ∈ [p − r, p + r]` with `G(x, y, z) = 0`. -/
theorem root_exists {G G1 G2 G3 : ℝ → ℝ → ℝ → ℝ} {p ρ a b1 b3 r δ : ℝ}
    (h1 : ∀ x y z, HasDerivAt (fun x => G x y z) (G1 x y z) x)
    (h2 : ∀ x y z, HasDerivAt (fun y => G x y z) (G2 x y z) y)
    (h3 : ∀ x y z, HasDerivAt (fun z => G x y z) (G3 x y z) z)
    (ha : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, a ≤ G2 x y z)
    (hb1 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G1 x y z| ≤ b1)
    (hb3 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G3 x y z| ≤ b3)
    (hG0 : G p p p = 0) (hr : 0 < r) (hrρ : r ≤ ρ) (hδρ : δ ≤ ρ)
    (hsmall : (b1 + b3) * δ < a * r) {x z : ℝ} (hx : x ∈ Jint p δ) (hz : z ∈ Jint p δ) :
    ∃ y ∈ Jint p r, G x y z = 0 := by
  have hρ : 0 ≤ ρ := by linarith
  have hp := center_mem_Jint (p := p) hρ
  have hpr : p + r ∈ Jint p ρ := ⟨by linarith, by linarith⟩
  have hmr : p - r ∈ Jint p ρ := ⟨by linarith, by linarith⟩
  have hxρ := Jint_mono hδρ hx
  have hzρ := Jint_mono hδρ hz
  have hb1n : 0 ≤ b1 := (abs_nonneg _).trans (hb1 p hp p hp p hp)
  have hb3n : 0 ≤ b3 := (abs_nonneg _).trans (hb3 p hp p hp p hp)
  have hxd : |x - p| ≤ δ := mem_Jint_iff.1 hx
  have hzd : |z - p| ≤ δ := mem_Jint_iff.1 hz
  -- bounds at `y = p ± r`
  have hup : a * r ≤ G p (p + r) p - G p p p := by
    have := mul_sub_le_of_hasDerivAt (φ := fun t => G p t p) (fun t _ => h2 p t p)
      (fun t ht => ha p hp t ht p hp) hp hpr (by linarith)
    simpa using this
  have hdn : a * r ≤ G p p p - G p (p - r) p := by
    have := mul_sub_le_of_hasDerivAt (φ := fun t => G p t p) (fun t _ => h2 p t p)
      (fun t ht => ha p hp t ht p hp) hmr hp (by linarith)
    simpa using this
  have hmove : ∀ w ∈ Jint p ρ, |G x w z - G p w p| ≤ (b1 + b3) * δ := by
    intro w hw
    have e1 : |G x w z - G p w z| ≤ b1 * |x - p| :=
      abs_sub_le_of_hasDerivAt (φ := fun t => G t w z) (convex_Icc _ _)
        (fun t _ => h1 t w z) (fun t ht => hb1 t ht w hw z hzρ) hp hxρ
    have e3 : |G p w z - G p w p| ≤ b3 * |z - p| :=
      abs_sub_le_of_hasDerivAt (φ := fun t => G p w t) (convex_Icc _ _)
        (fun t _ => h3 p w t) (fun t ht => hb3 p hp w hw t ht) hp hzρ
    calc |G x w z - G p w p| = |(G x w z - G p w z) + (G p w z - G p w p)| := by ring_nf
      _ ≤ |G x w z - G p w z| + |G p w z - G p w p| := abs_add_le _ _
      _ ≤ b1 * δ + b3 * δ := add_le_add ((e1.trans (mul_le_mul_of_nonneg_left hxd hb1n)))
          (e3.trans (mul_le_mul_of_nonneg_left hzd hb3n))
      _ = (b1 + b3) * δ := by ring
  have hpos : 0 < G x (p + r) z := by
    have := (abs_le.1 (hmove _ hpr)).1
    linarith
  have hneg : G x (p - r) z < 0 := by
    have := (abs_le.1 (hmove _ hmr)).2
    linarith
  have hcont : ContinuousOn (fun y => G x y z) (Icc (p - r) (p + r)) :=
    fun y _ => (h2 x y z).continuousAt.continuousWithinAt
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc (by linarith : p - r ≤ p + r) hcont
    ⟨hneg.le, hpos.le⟩
  exact ⟨y, hy, hy0⟩

/-- The implicit root: a `y ∈ [p − r, p + r]` with `G(clamp x, y, clamp z) = 0`, chosen by
`Classical.epsilon` (clamping to `[p − δ, p + δ]`). -/
noncomputable def implicitRoot (G : ℝ → ℝ → ℝ → ℝ) (p r δ x z : ℝ) : ℝ :=
  Classical.epsilon fun y => y ∈ Jint p r ∧ G (clampI p δ x) y (clampI p δ z) = 0

/-! ### Bounds on the partial derivatives of `F` near the steady state -/

/-- From an eventual property at `(p, p, p)` to a property on a cube `J³`. -/
theorem exists_cube_of_eventually {P : ℝ × ℝ × ℝ → Prop} {p : ℝ}
    (h : ∀ᶠ q in 𝓝 ((p, p, p) : ℝ × ℝ × ℝ), P q) :
    ∃ ρ > 0, ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, P (x, y, z) := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε / 2, by linarith, fun x hx y hy z hz => hP ?_⟩
  have hx' := mem_Jint_iff.1 hx
  have hy' := mem_Jint_iff.1 hy
  have hz' := mem_Jint_iff.1 hz
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

/-- **Bounds near `(k*, k*, k*)`.** For `a < F₂*`, `b₁ > −F₁*`, `b₃ > −F₃*` there is a cube on
which `F₂ > a`, `|F₁| < b₁`, `|F₃| < b₃`, `F₁ < 0` and `F₃ < 0`. -/
theorem LocalHyp.exists_cube {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {a b1 b3 : ℝ}
    (ha : a < F2s β θ U f ks) (hb1 : -F1s β θ U f ks < b1) (hb3 : -F3s U θ f ks < b3) :
    ∃ ρ > 0, ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ,
      a < F2f β θ U f x y z ∧ |F1f θ U f x y| < b1 ∧ |F3f β θ U f y z| < b3 ∧
        F1f θ U f x y < 0 ∧ F3f β θ U f y z < 0 := by
  have hU1 := continuous_deriv_of_C2 L.U_contDiff
  have hU2 := continuous_deriv2_of_C2 L.U_contDiff
  have hf0 := (differentiable_of_C2 L.f_contDiff).continuous
  have hf1 := continuous_deriv_of_C2 L.f_contDiff
  have hf2 := continuous_deriv2_of_C2 L.f_contDiff
  have c1 : Continuous fun q : ℝ × ℝ × ℝ => F1f θ U f q.1 q.2.1 := by
    simp only [F1f, psi, dpsi]
    fun_prop
  have c2 : Continuous fun q : ℝ × ℝ × ℝ => F2f β θ U f q.1 q.2.1 q.2.2 := by
    simp only [F2f, psi, dpsi]
    fun_prop
  have c3 : Continuous fun q : ℝ × ℝ × ℝ => F3f β θ U f q.2.1 q.2.2 := by
    simp only [F3f, psi]
    fun_prop
  have v1 : F1f θ U f ks ks = F1s β θ U f ks := F1f_star L.beta_pos L.euler
  have v2 : F2f β θ U f ks ks ks = F2s β θ U f ks := F2f_star L.beta_pos L.euler
  have v3 : F3f β θ U f ks ks = F3s U θ f ks := F3f_star L.euler
  have hF1 := L.F1s_neg
  have hF3 := L.F3s_neg
  have e2' : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), a < F2f β θ U f q.1 q.2.1 q.2.2 :=
    c2.continuousAt.eventually (lt_mem_nhds (by
      change a < F2f β θ U f ks ks ks
      rw [v2]
      exact ha))
  have e1 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), |F1f θ U f q.1 q.2.1| < b1 :=
    (continuous_abs.comp c1).continuousAt.eventually
      (gt_mem_nhds (by simp only [Function.comp_apply]; rw [v1, abs_of_neg hF1]; exact hb1))
  have e3 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), |F3f β θ U f q.2.1 q.2.2| < b3 :=
    (continuous_abs.comp c3).continuousAt.eventually
      (gt_mem_nhds (by simp only [Function.comp_apply]; rw [v3, abs_of_neg hF3]; exact hb3))
  have e4 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), F1f θ U f q.1 q.2.1 < 0 :=
    c1.continuousAt.eventually (gt_mem_nhds (by
      change F1f θ U f ks ks < 0
      rw [v1]
      exact hF1))
  have e5 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), F3f β θ U f q.2.1 q.2.2 < 0 :=
    c3.continuousAt.eventually (gt_mem_nhds (by
      change F3f β θ U f ks ks < 0
      rw [v3]
      exact hF3))
  obtain ⟨ρ, hρ, hP⟩ := exists_cube_of_eventually (e2'.and (e1.and (e3.and (e4.and e5))))
  exact ⟨ρ, hρ, fun x hx y hy z hz => hP x hx y hy z hz⟩

/-! ### The local solution `H` -/

/-- **The local solution `H` of §18.2 (7)** on `I = [k* − ε₀, k* + ε₀]`, with the properties the
book derives from the Implicit Function Theorem: (7), local uniqueness of the root,
`H(k*, k*) = k*`, continuity, a Lipschitz bound, strict monotonicity in each argument, and
Lipschitz constants arbitrarily close to `H₁* = −F₁*/F₂*` and `H₂* = −F₃*/F₂*` near `(k*, k*)`. -/
structure LocalSolution (β θ : ℝ) (U f : ℝ → ℝ) (ks ε₀ : ℝ) (H : ℝ → ℝ → ℝ) : Prop where
  eps_pos : 0 < ε₀
  eq7 : ∀ x ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, Feq β θ U f x (H x z) z = 0
  unique : ∀ x ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, ∀ y ∈ Jint ks ε₀, Feq β θ U f x y z = 0 →
    y = H x z
  center : H ks ks = ks
  continuous : Continuous fun q : ℝ × ℝ => H q.1 q.2
  lipschitz : ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧ ∀ x x' z z' : ℝ,
    |H x z - H x' z'| ≤ B₁ * |x - x'| + B₂ * |z - z'|
  strictMono_left : ∀ x ∈ Jint ks ε₀, ∀ x' ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, x < x' →
    H x z < H x' z
  strictMono_right : ∀ x ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, ∀ z' ∈ Jint ks ε₀, z < z' →
    H x z < H x z'
  lip_near : ∀ m₁ m₂ : ℝ, -F1s β θ U f ks / F2s β θ U f ks < m₁ →
    -F3s U θ f ks / F2s β θ U f ks < m₂ → ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ x ∈ Jint ks ε, ∀ x' ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
        |H x z - H x' z'| ≤ m₁ * |x - x'| + m₂ * |z - z'|

/-- **§18.2 (7): existence of the local solution `H`.** Under `LocalHyp` (Assumption 18.1 near
the steady state, with `U″(c*) < 0` and `f″(k*) < 0`) there are `ε₀ > 0` and `H` with all the
properties of `LocalSolution`. -/
theorem exists_localSolution {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    ∃ ε₀ H, LocalSolution β θ U f ks ε₀ H := by
  set F1 := F1s β θ U f ks with hF1
  set F2 := F2s β θ U f ks with hF2
  set F3 := F3s U θ f ks with hF3
  have hF1n : F1 < 0 := L.F1s_neg
  have hF2p : 0 < F2 := L.F2s_pos
  have hF3n : F3 < 0 := L.F3s_neg
  have hd1 := hasDerivAt_Feq_x (β := β) (θ := θ) L.U_contDiff L.f_contDiff
  have hd2 := hasDerivAt_Feq_y (β := β) (θ := θ) L.U_contDiff L.f_contDiff
  have hd3 := hasDerivAt_Feq_z (β := β) (θ := θ) (f := f) L.U_contDiff
  have hG0 : Feq β θ U f ks ks ks = 0 := by
    rw [Feq_diag, L.euler, sub_self, mul_zero]
  -- the big cube
  set a0 := F2 / 2 with ha0
  set b10 := -F1 + 1 with hb10
  set b30 := -F3 + 1 with hb30
  have ha0p : 0 < a0 := by linarith
  have hb10p : 0 < b10 := by linarith
  have hb30p : 0 < b30 := by linarith
  obtain ⟨ρ, hρ, hcube⟩ := L.exists_cube (a := a0) (b1 := b10) (b3 := b30) (by linarith)
    (by linarith) (by linarith)
  have hA : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ, a0 ≤ F2f β θ U f x y z :=
    fun x hx y hy z hz => (hcube x hx y hy z hz).1.le
  have hB1 : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ,
      |(fun x y (_ : ℝ) => F1f θ U f x y) x y z| ≤ b10 :=
    fun x hx y hy z hz => (hcube x hx y hy z hz).2.1.le
  have hB3 : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ,
      |(fun (_ : ℝ) y z => F3f β θ U f y z) x y z| ≤ b30 :=
    fun x hx y hy z hz => (hcube x hx y hy z hz).2.2.1.le
  set δ := min ρ (a0 * ρ / (2 * (b10 + b30))) with hδ
  have hδp : 0 < δ := lt_min hρ (div_pos (mul_pos ha0p hρ) (by linarith))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hsmall : (b10 + b30) * δ < a0 * ρ := by
    have h1 : δ ≤ a0 * ρ / (2 * (b10 + b30)) := min_le_right _ _
    have h2 : (b10 + b30) * δ ≤ a0 * ρ / 2 := by
      calc (b10 + b30) * δ ≤ (b10 + b30) * (a0 * ρ / (2 * (b10 + b30))) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = a0 * ρ / 2 := by field_simp
    linarith [mul_pos ha0p hρ]
  set H := implicitRoot (Feq β θ U f) ks ρ δ with hH
  have hspec : ∀ x z, H x z ∈ Jint ks ρ ∧
      Feq β θ U f (clampI ks δ x) (H x z) (clampI ks δ z) = 0 := fun x z =>
    Classical.epsilon_spec (root_exists (G := Feq β θ U f) hd1 hd2 hd3 hA hB1 hB3 hG0 hρ le_rfl
      hδρ hsmall (clampI_mem hδp.le x) (clampI_mem hδp.le z))
  have hmemρ : ∀ x, clampI ks δ x ∈ Jint ks ρ := fun x => Jint_mono hδρ (clampI_mem hδp.le x)
  -- global Lipschitz bound
  have hglob : ∀ x x' z z', a0 * |H x z - H x' z'| ≤
      b10 * |x - x'| + b30 * |z - z'| := by
    intro x x' z z'
    have := root_sep (G := Feq β θ U f) hd1 hd2 hd3 hA hB1 hB3 (hmemρ x) (hmemρ x')
      (hspec x z).1 (hspec x' z').1 (hmemρ z) (hmemρ z') (hspec x z).2 (hspec x' z').2
    refine this.trans (add_le_add (mul_le_mul_of_nonneg_left (abs_clampI_sub_le _ _ _ _)
      hb10p.le) (mul_le_mul_of_nonneg_left (abs_clampI_sub_le _ _ _ _) hb30p.le))
  have hglob' : ∀ x x' z z', |H x z - H x' z'| ≤
      b10 / a0 * |x - x'| + b30 / a0 * |z - z'| := by
    intro x x' z z'
    have := hglob x x' z z'
    rw [show b10 / a0 * |x - x'| + b30 / a0 * |z - z'| =
      (b10 * |x - x'| + b30 * |z - z'|) / a0 by ring, le_div_iff₀ ha0p]
    linarith
  have heq7 : ∀ x ∈ Jint ks δ, ∀ z ∈ Jint ks δ, Feq β θ U f x (H x z) z = 0 := by
    intro x hx z hz
    have := (hspec x z).2
    rwa [clampI_of_mem hx, clampI_of_mem hz] at this
  have huniq : ∀ x ∈ Jint ks δ, ∀ z ∈ Jint ks δ, ∀ y ∈ Jint ks ρ, Feq β θ U f x y z = 0 →
      y = H x z := by
    intro x hx z hz y hy hy0
    have hxρ := Jint_mono hδρ hx
    have hzρ := Jint_mono hδρ hz
    have := root_sep (G := Feq β θ U f) hd1 hd2 hd3 hA hB1 hB3 hxρ hxρ hy (hspec x z).1 hzρ
      hzρ hy0 (heq7 x hx z hz)
    simp only [sub_self, abs_zero, mul_zero, add_zero] at this
    have h0 : |y - H x z| ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos ha0p hc
      linarith
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)
  have hks := center_mem_Jint (p := ks) hδp.le
  have hcenter : H ks ks = ks :=
    (huniq ks hks ks hks ks (center_mem_Jint hρ.le) hG0).symm
  -- strict monotonicity of `F` on the big cube
  have hFy : ∀ x ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ, StrictMonoOn (fun y => Feq β θ U f x y z)
      (Jint ks ρ) := by
    intro x hx z hz
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun y _ => (hd2 x y z).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [(hd2 x y z).deriv]
    exact ha0p.trans (hcube x hx y (interior_subset hy) z hz).1
  have hFx : ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ, StrictAntiOn (fun x => Feq β θ U f x y z)
      (Jint ks ρ) := by
    intro y hy z hz
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun x _ => (hd1 x y z).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [(hd1 x y z).deriv]
    exact (hcube x (interior_subset hx) y hy z hz).2.2.2.1
  have hFz : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, StrictAntiOn (fun z => Feq β θ U f x y z)
      (Jint ks ρ) := by
    intro x hx y hy
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun z _ => (hd3 x y z).continuousAt.continuousWithinAt) fun z hz => ?_
    rw [(hd3 x y z).deriv]
    exact (hcube x hx y hy z (interior_subset hz)).2.2.2.2
  refine ⟨δ, H, ⟨hδp, heq7, fun x hx z hz y hy hy0 => huniq x hx z hz y (Jint_mono hδρ hy) hy0,
    hcenter, ?_, ⟨b10 / a0, b30 / a0, (div_pos hb10p ha0p).le, (div_pos hb30p ha0p).le, hglob'⟩,
    ?_, ?_, ?_⟩⟩
  · -- continuity
    have hB : 0 ≤ b10 / a0 + b30 / a0 := by positivity
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (b10 / a0 + b30 / a0))
      fun q q' => ?_).continuous
    rw [Real.coe_toNNReal _ hB, Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine (hglob' _ _ _ _).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (le_max_left |q.1 - q'.1| |q.2 - q'.2|)
      (div_pos hb10p ha0p).le
    have h2 := mul_le_mul_of_nonneg_left (le_max_right |q.1 - q'.1| |q.2 - q'.2|)
      (div_pos hb30p ha0p).le
    linarith
  · -- strictly increasing in `x`
    intro x hx x' hx' z hz hxx
    have hy := (hspec x z).1
    have hy' := (hspec x' z).1
    have h1 : Feq β θ U f x' (H x z) z < Feq β θ U f x (H x z) z :=
      hFx _ hy z (Jint_mono hδρ hz) (Jint_mono hδρ hx) (Jint_mono hδρ hx') hxx
    rw [heq7 x hx z hz, ← heq7 x' hx' z hz] at h1
    exact (hFy x' (Jint_mono hδρ hx') z (Jint_mono hδρ hz)).lt_iff_lt hy hy' |>.1 h1
  · -- strictly increasing in `z`
    intro x hx z hz z' hz' hzz
    have hy := (hspec x z).1
    have hy' := (hspec x z').1
    have h1 : Feq β θ U f x (H x z) z' < Feq β θ U f x (H x z) z :=
      hFz x (Jint_mono hδρ hx) _ hy (Jint_mono hδρ hz) (Jint_mono hδρ hz') hzz
    rw [heq7 x hx z hz, ← heq7 x hx z' hz'] at h1
    exact (hFy x (Jint_mono hδρ hx) z' (Jint_mono hδρ hz')).lt_iff_lt hy hy' |>.1 h1
  · -- Lipschitz constants close to `H₁*`, `H₂*`
    intro m₁ m₂ hm₁ hm₂
    have hH1 : 0 < -F1 / F2 := div_pos (by linarith) hF2p
    have hH2 : 0 < -F3 / F2 := div_pos (by linarith) hF2p
    have hm₁p : 0 < 1 + m₁ := by linarith
    have hm₂p : 0 < 1 + m₂ := by linarith
    have hg₁ : 0 < F2 * m₁ + F1 := by
      have := (div_lt_iff₀ hF2p).1 hm₁
      linarith
    have hg₂ : 0 < F2 * m₂ + F3 := by
      have := (div_lt_iff₀ hF2p).1 hm₂
      linarith
    set s := min (F2 / 2) (min ((F2 * m₁ + F1) / (1 + m₁)) ((F2 * m₂ + F3) / (1 + m₂)))
      with hs
    have hsp : 0 < s := lt_min (by linarith) (lt_min (div_pos hg₁ hm₁p) (div_pos hg₂ hm₂p))
    have hs1 : s ≤ F2 / 2 := min_le_left _ _
    have hs2 : s * (1 + m₁) ≤ F2 * m₁ + F1 :=
      (le_div_iff₀ hm₁p).1 ((min_le_right _ _).trans (min_le_left _ _))
    have hs3 : s * (1 + m₂) ≤ F2 * m₂ + F3 :=
      (le_div_iff₀ hm₂p).1 ((min_le_right _ _).trans (min_le_right _ _))
    set a := F2 - s with ha
    have hap : 0 < a := by linarith
    obtain ⟨ρ₁, hρ₁, hcube₁⟩ := L.exists_cube (a := a) (b1 := -F1 + s) (b3 := -F3 + s)
      (by linarith) (by linarith) (by linarith)
    have hb1m : -F1 + s ≤ m₁ * a := by
      rw [ha]
      linarith
    have hb3m : -F3 + s ≤ m₂ * a := by
      rw [ha]
      linarith
    set B := b10 / a0 + b30 / a0 with hBdef
    have hB : 0 ≤ B := by positivity
    set ε := min δ (min ρ₁ (ρ₁ / (B + 1))) with hε
    have hεp : 0 < ε := lt_min hδp (lt_min hρ₁ (div_pos hρ₁ (by linarith)))
    have hεδ : ε ≤ δ := min_le_left _ _
    have hερ₁ : ε ≤ ρ₁ := (min_le_right _ _).trans (min_le_left _ _)
    have hεB : ε ≤ ρ₁ / (B + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have hnear : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, H x z ∈ Jint ks ρ₁ := by
      intro x hx z hz
      rw [mem_Jint_iff]
      have h := hglob' x ks z ks
      rw [hcenter] at h
      have hx' := mem_Jint_iff.1 hx
      have hz' := mem_Jint_iff.1 hz
      have h2 : B * ε ≤ ρ₁ := by
        calc B * ε ≤ (B + 1) * ε := by linarith
          _ ≤ (B + 1) * (ρ₁ / (B + 1)) := mul_le_mul_of_nonneg_left hεB (by linarith)
          _ = ρ₁ := by field_simp
      have h3 : b10 / a0 * |x - ks| + b30 / a0 * |z - ks| ≤ B * ε := by
        have h4 := mul_le_mul_of_nonneg_left hx' (div_pos hb10p ha0p).le
        have h5 := mul_le_mul_of_nonneg_left hz' (div_pos hb30p ha0p).le
        rw [hBdef]
        linarith
      linarith
    refine ⟨ε, hεp, hεδ, fun x hx x' hx' z hz z' hz' => ?_⟩
    have hA₁ : ∀ x ∈ Jint ks ρ₁, ∀ y ∈ Jint ks ρ₁, ∀ z ∈ Jint ks ρ₁,
        a ≤ F2f β θ U f x y z := fun x hx y hy z hz => (hcube₁ x hx y hy z hz).1.le
    have hB1₁ : ∀ x ∈ Jint ks ρ₁, ∀ y ∈ Jint ks ρ₁, ∀ z ∈ Jint ks ρ₁,
        |(fun x y (_ : ℝ) => F1f θ U f x y) x y z| ≤ -F1 + s :=
      fun x hx y hy z hz => (hcube₁ x hx y hy z hz).2.1.le
    have hB3₁ : ∀ x ∈ Jint ks ρ₁, ∀ y ∈ Jint ks ρ₁, ∀ z ∈ Jint ks ρ₁,
        |(fun (_ : ℝ) y z => F3f β θ U f y z) x y z| ≤ -F3 + s :=
      fun x hx y hy z hz => (hcube₁ x hx y hy z hz).2.2.1.le
    have key := root_sep (G := Feq β θ U f) hd1 hd2 hd3 hA₁ hB1₁ hB3₁ (Jint_mono hερ₁ hx)
      (Jint_mono hερ₁ hx') (hnear x hx z hz) (hnear x' hx' z' hz') (Jint_mono hερ₁ hz)
      (Jint_mono hερ₁ hz') (heq7 x (Jint_mono hεδ hx) z (Jint_mono hεδ hz))
      (heq7 x' (Jint_mono hεδ hx') z' (Jint_mono hεδ hz'))
    have h1 : a * |H x z - H x' z'| ≤ a * (m₁ * |x - x'| + m₂ * |z - z'|) := by
      have h2 := mul_le_mul_of_nonneg_right hb1m (abs_nonneg (x - x'))
      have h3 := mul_le_mul_of_nonneg_right hb3m (abs_nonneg (z - z'))
      linarith
    exact le_of_mul_le_mul_left h1 hap

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The local contraction argument

SLP §18.2, pp. 550–554. With `H` the local solution of §18.2 (7) (`LocalSolution`), the operator
`(Th)(k) = H[k, h²(k)]` (§18.2 (8), `Top`) acts on
`D_λ(I_ε) = {h : h(k*) = k*, |h(k) − h(k′)| ≤ λ|k − k′| on I_ε}` (`Dlam`), `I_ε = [k* − ε, k* + ε]`.
A fixed point of `T` solves the Euler equation (4) on `I_ε`.

* `local_constants`: for `λ ∈ (λ*, 1)`, constants `m₁ > H₁*`, `m₂ > H₂*` and `ε` with
  `m₁ + m₂λ² ≤ λ`, `m₂(1 + λ) < 1`, `m₁ + m₂ ≤ 1` and `H` `(m₁, m₂)`-Lipschitz on `I_ε × I_ε`.
* **Proposition 18.2** (`prop_18_2`, p. 550): for every `λ ∈ (λ*, 1)` there is `ε > 0` with
  `I_ε ⊆ I` and `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`.
* **Exercise 18.3** (`ex_18_3`, p. 551): `T` is (Lipschitz) continuous in the sup norm on
  `D_λ(I_ε)`; `ex_18_3_continuous` for the packaged operator on `C(I_ε)`.
* **Exercise 18.4** (p. 552): (a) `ex_18_4a` (monotone on nondecreasing members) and
  `ex_18_4a_mapsTo`; (b) `ex_18_4b` (repaired).
* **Proposition 18.3** (`prop_18_3`, `prop_18_3_contractingWith`, p. 552): for every
  `λ ∈ (λ*, 1)` there is `ε > 0` such that `T` is a contraction of `D_λ(I_ε)` (as a
  `ContractingWith` self-map of the closed subset `DC ⊆ C(I_ε)`); `prop_18_3_fixedPoint` gives
  the consequences on p. 553: a unique fixed point `g ∈ D_λ(I_ε)`, which solves (4) on `I_ε`, and
  `|g^t(k) − k*| ≤ λ^t |k − k*|` (local stability).
* **Proposition 18.4** (`prop_18_4`, p. 553): the fixed point is strictly increasing on `I_ε`.

`C(I_ε)` is `C(Jint ks ε, ℝ)` with the sup metric; a function on `I_ε` is extended to `ℝ` by
`Set.IccExtend` (`extendC`), so `TC` (the operator on `C(I_ε)`) agrees with `Top` on `I_ε`.

**Corrections.**
* (NOTE 18.2-D, p. 550.) `T` is not defined on all of `C(I)`: (8) needs `h(I) ⊆ I`. Here `Top`
  is defined for all functions, and only its values on `I_ε` for `h` mapping `I_ε` into itself
  (`Dlam.mapsTo`) are used. Verified, harmless.
* (NOTE 18.2-F, manual Ex. 18.3.) The manual's inequality
  `|h_n²(k) − h²(k)| ≤ λ|h_n(k) − h(k)|` is false (`ex_18_3_manual_counterexample`: on
  `[−1, 1]`, `h(k) = −λk`, `h_c(k) = −λk + c·max(k, 0)`, `0 < c ≤ 2λ`, at `k = −1`). The correct
  bound is `|h_n²(k) − h²(k)| ≤ (1 + λ)‖h_n − h‖` (`Top_sub_le`), which gives Exercise 18.3.
* (NOTE 18.2-G, Ex. 18.4a.) **False as stated**: `T` is not monotone on `D_λ(I_ε)`
  (`ex_18_4a_counterexample`: for every `λ ∈ (0, 1]` and `ε ≤ ε₀`, two members `h′ ≤ h` with
  `(Th)(k* + ε) < (Th′)(k* + ε)`). It is monotone on the nondecreasing members (`ex_18_4a`).
* (NOTE 18.2-H, Ex. 18.4b.) The constants `k* ± ε` are not in `D_λ(I_ε)`
  (`ex_18_4b_const_not_mem`). Repaired version `ex_18_4b`: on
  `E = {h : I_ε → I_ε nondecreasing, λ-Lipschitz}` (`Elam`), with `ε` chosen so that also
  `m₁ + m₂ ≤ 1`, `T` maps `E` into itself and is monotone there, `h₋ ≡ k* − ε` and
  `h₊ ≡ k* + ε` lie in `E` with `h₋ ≤ Th₋`, `Th₊ ≤ h₊`, the iterates `Tⁿh₋` increase and `Tⁿh₊`
  decrease, and both converge uniformly on `I_ε` (at rate `Kⁿ`) to the fixed point `g` of
  Proposition 18.3, which is the unique fixed point in `E`. (Convergence is proved with the
  contraction estimate rather than Theorem 17.7.)
* (NOTE 18.2-E, proof of Prop. 18.3.) The printed choice `m̂₂(1 + λ*) < δ` does not give
  `M₂(1 + λ) ≤ δ` since `λ > λ*` (`prop_18_3_printed_step_counterexample`). The fix replaces `λ*`
  by `λ`: `H₂*(1 + λ) < 1` (`LocalHyp.H2s_mul_lt_one`), used in `local_constants`.
* (NOTE 18.2-I, p. 553.) Uniqueness is within `D_λ(I_ε)` for the given `(λ, ε)`
  (`prop_18_3_fixedPoint`). Verified.
* (NOTE 18.2-J, p. 548.) A solution of (4) is taken as the definition of equilibrium; for the
  local solutions here the transversality condition holds because the paths are bounded and
  converge to `k*` (`tvc_of_bounded` in `IndirectApproach`). Verified, recorded.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- `D_λ(I_ε)` (p. 550), as a set of functions `ℝ → ℝ` (only values on `I_ε` matter):
`h(k*) = k*` and `h` is `λ`-Lipschitz on `I_ε`. -/
def Dlam (ks ε lam : ℝ) : Set (ℝ → ℝ) :=
  {h | h ks = ks ∧ ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |h k - h k'| ≤ lam * |k - k'|}

/-- The operator `(Th)(k) = H[k, h(h(k))]` of §18.2 (8). -/
def Top (H : ℝ → ℝ → ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun k => H k (h (h k))

/-- `H` is `(m₁, m₂)`-Lipschitz on `I_ε × I_ε`. -/
def HBound (H : ℝ → ℝ → ℝ) (ks ε m₁ m₂ : ℝ) : Prop :=
  ∀ x ∈ Jint ks ε, ∀ x' ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
    |H x z - H x' z'| ≤ m₁ * |x - x'| + m₂ * |z - z'|

/-- Members of `D_λ(I_ε)` (`λ ≤ 1`) map `I_ε` into itself. -/
theorem Dlam_mapsTo {ks ε lam : ℝ} {h : ℝ → ℝ} (hh : h ∈ Dlam ks ε lam) (hl1 : lam ≤ 1) :
    ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε := by
  intro k hk
  have hε : 0 ≤ ε := by linarith [hk.1, hk.2]
  have h1 := hh.2 k hk ks (center_mem_Jint hε)
  rw [hh.1] at h1
  have h2 := mem_Jint_iff.1 hk
  rw [mem_Jint_iff]
  linarith [mul_le_of_le_one_left (abs_nonneg (k - ks)) hl1]

/-- Membership in `D_λ(I_ε)` depends only on the values on `I_ε`. -/
theorem Dlam_congr {ks ε lam : ℝ} {h h' : ℝ → ℝ} (hε : 0 ≤ ε)
    (he : ∀ k ∈ Jint ks ε, h k = h' k) (hh : h ∈ Dlam ks ε lam) : h' ∈ Dlam ks ε lam :=
  ⟨by rw [← he ks (center_mem_Jint hε)]; exact hh.1, fun k hk k' hk' => by
    rw [← he k hk, ← he k' hk']; exact hh.2 k hk k' hk'⟩

/-! ### Basic estimates for `T` -/

/-- **Lipschitz bound for `Th`** (proof of Proposition 18.2). If `h` maps `I_ε` into itself and
is `λ`-Lipschitz there, `λ ≥ 0`, and `H` is `(m₁, m₂)`-Lipschitz, then `Th` is
`(m₁ + m₂λ²)`-Lipschitz on `I_ε`. -/
theorem Top_lipschitz {H : ℝ → ℝ → ℝ} {ks ε lam m₁ m₂ : ℝ} (hB : HBound H ks ε m₁ m₂)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) {h : ℝ → ℝ} (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε)
    (hL : ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |h k - h k'| ≤ lam * |k - k'|) :
    ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε,
      |Top H h k - Top H h k'| ≤ (m₁ + m₂ * lam ^ 2) * |k - k'| := by
  intro k hk k' hk'
  have h1 := hB k hk k' hk' _ (hmaps _ (hmaps k hk)) _ (hmaps _ (hmaps k' hk'))
  have h4 : |h (h k) - h (h k')| ≤ lam ^ 2 * |k - k'| :=
    calc |h (h k) - h (h k')| ≤ lam * |h k - h k'| := hL _ (hmaps k hk) _ (hmaps k' hk')
      _ ≤ lam * (lam * |k - k'|) := mul_le_mul_of_nonneg_left (hL k hk k' hk') hl0
      _ = lam ^ 2 * |k - k'| := by ring
  calc |Top H h k - Top H h k'| ≤ m₁ * |k - k'| + m₂ * |h (h k) - h (h k')| := h1
    _ ≤ m₁ * |k - k'| + m₂ * (lam ^ 2 * |k - k'|) := by
        linarith [mul_le_mul_of_nonneg_left h4 hm₂]
    _ = (m₁ + m₂ * lam ^ 2) * |k - k'| := by ring

/-- **`T(D_λ(I_ε)) ⊆ D_λ(I_ε)`** under `m₁ + m₂λ² ≤ λ` (proof of Proposition 18.2). -/
theorem Top_mem_Dlam {H : ℝ → ℝ → ℝ} {ks ε lam m₁ m₂ : ℝ} (hB : HBound H ks ε m₁ m₂)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hsum : m₁ + m₂ * lam ^ 2 ≤ lam)
    (hc : H ks ks = ks) {h : ℝ → ℝ} (hh : h ∈ Dlam ks ε lam) : Top H h ∈ Dlam ks ε lam := by
  refine ⟨by simp only [Top, hh.1, hc], fun k hk k' hk' => ?_⟩
  exact (Top_lipschitz hB hm₂ hl0 (Dlam_mapsTo hh hl1) hh.2 k hk k' hk').trans
    (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))

/-- **The contraction estimate** (proof of Proposition 18.3, Exercise 18.3). If `h, ĥ` map
`I_ε` into itself, `ĥ` is `λ`-Lipschitz there (`λ ≥ 0`), `|h − ĥ| ≤ D` on `I_ε`, and
`|H(x, z) − H(x, z′)| ≤ m₂|z − z′|`, then
`|h(h(k)) − ĥ(ĥ(k))| ≤ (1 + λ) D` and `|(Th)(k) − (Tĥ)(k)| ≤ m₂(1 + λ) D` on `I_ε`. -/
theorem Top_sub_le {H : ℝ → ℝ → ℝ} {ks ε lam m₂ D : ℝ}
    (hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε, |H x z - H x z'| ≤ m₂ * |z - z'|)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) {h hh : ℝ → ℝ} (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε)
    (hmaps' : ∀ k ∈ Jint ks ε, hh k ∈ Jint ks ε)
    (hL : ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |hh k - hh k'| ≤ lam * |k - k'|)
    (hD : ∀ k ∈ Jint ks ε, |h k - hh k| ≤ D) :
    ∀ k ∈ Jint ks ε, |h (h k) - hh (hh k)| ≤ (1 + lam) * D ∧
      |Top H h k - Top H hh k| ≤ m₂ * (1 + lam) * D := by
  intro k hk
  have h2 : |h (h k) - hh (hh k)| ≤ (1 + lam) * D :=
    calc |h (h k) - hh (hh k)| = |(h (h k) - hh (h k)) + (hh (h k) - hh (hh k))| := by ring_nf
      _ ≤ |h (h k) - hh (h k)| + |hh (h k) - hh (hh k)| := abs_add_le _ _
      _ ≤ D + lam * |h k - hh k| := add_le_add (hD _ (hmaps k hk))
          (hL _ (hmaps k hk) _ (hmaps' k hk))
      _ ≤ D + lam * D := by linarith [mul_le_mul_of_nonneg_left (hD k hk) hl0]
      _ = (1 + lam) * D := by ring
  refine ⟨h2, ?_⟩
  calc |Top H h k - Top H hh k| ≤ m₂ * |h (h k) - hh (hh k)| :=
        hHz k hk _ (hmaps _ (hmaps k hk)) _ (hmaps' _ (hmaps' k hk))
    _ ≤ m₂ * ((1 + lam) * D) := mul_le_mul_of_nonneg_left h2 hm₂
    _ = m₂ * (1 + lam) * D := by ring

/-- `T` is strictly increasing on `I_ε` at nondecreasing `h` mapping `I_ε` into itself
(proof of Proposition 18.4; it uses that `F` is strictly decreasing in its first and third
arguments and strictly increasing in its second, through the monotonicity of `H`). -/
theorem Top_strictMonoOn {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε : ℝ} (hεε₀ : ε ≤ ε₀) {h : ℝ → ℝ}
    (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) (hmono : MonotoneOn h (Jint ks ε)) :
    StrictMonoOn (Top H h) (Jint ks ε) := by
  intro k hk k' hk' hkk
  have hz := hmaps _ (hmaps k hk)
  have hz' := hmaps _ (hmaps k' hk')
  have hle : h (h k) ≤ h (h k') :=
    hmono (hmaps k hk) (hmaps k' hk') (hmono hk hk' hkk.le)
  have h1 : H k (h (h k)) < H k' (h (h k)) :=
    hH.strictMono_left k (Jint_mono hεε₀ hk) k' (Jint_mono hεε₀ hk') _ (Jint_mono hεε₀ hz) hkk
  have h2 : H k' (h (h k)) ≤ H k' (h (h k')) := by
    rcases eq_or_lt_of_le hle with he | hlt
    · rw [he]
    · exact (hH.strictMono_right k' (Jint_mono hεε₀ hk') _ (Jint_mono hεε₀ hz) _
        (Jint_mono hεε₀ hz') hlt).le
  exact h1.trans_le h2

/-! ### The constants of Propositions 18.2–18.3 -/

/-- **Choice of constants.** For `λ ∈ (λ*, 1)` there are `m₁, m₂ ≥ 0` and `ε ∈ (0, ε₀]` with
`m₁ + m₂λ² ≤ λ`, `m₂(1 + λ) < 1`, `m₁ + m₂ ≤ 1` and `H` `(m₁, m₂)`-Lipschitz on
`I_ε × I_ε`. (The condition `m₂(1 + λ) < 1` uses the corrected step of NOTE 18.2-E;
`m₁ + m₂ ≤ 1` is the extra condition of NOTE 18.2-H.) -/
theorem local_constants {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ m₁ m₂ ε, 0 < ε ∧ ε ≤ ε₀ ∧ 0 ≤ m₁ ∧ 0 ≤ m₂ ∧ m₁ + m₂ * lam ^ 2 ≤ lam ∧
      m₂ * (1 + lam) < 1 ∧ m₁ + m₂ ≤ 1 ∧ HBound H ks ε m₁ m₂ := by
  set H1 := -F1s β θ U f ks / F2s β θ U f ks with hH1
  set H2 := -F3s U θ f ks / F2s β θ U f ks with hH2
  have hH1p : 0 < H1 := L.H1s_pos
  have hH2p : 0 < H2 := L.H2s_pos
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  have g1 : 0 < lam - H1 - H2 * lam ^ 2 := by
    have := L.H_lt_lam hl hl1.le
    linarith
  have g2 : 0 < 1 - H2 * (1 + lam) := by
    have := L.H2s_mul_lt_one hl1.le
    linarith
  have g3 : 0 < 1 - H1 - H2 := by
    have := L.H_sum_lt_one
    linarith
  have hp1 : 0 < 1 + lam ^ 2 := by positivity
  have hp2 : 0 < 2 * (1 + lam) := by linarith
  set s := min ((lam - H1 - H2 * lam ^ 2) / (1 + lam ^ 2))
    (min ((1 - H2 * (1 + lam)) / (2 * (1 + lam))) ((1 - H1 - H2) / 2)) with hs
  have hsp : 0 < s := lt_min (div_pos g1 hp1) (lt_min (div_pos g2 hp2) (by linarith))
  have hs1 : s * (1 + lam ^ 2) ≤ lam - H1 - H2 * lam ^ 2 :=
    (le_div_iff₀ hp1).1 (min_le_left _ _)
  have hs2 : s * (2 * (1 + lam)) ≤ 1 - H2 * (1 + lam) :=
    (le_div_iff₀ hp2).1 ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : s ≤ (1 - H1 - H2) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε, hε, hεε₀, hB⟩ := hH.lip_near (H1 + s) (H2 + s) (by linarith) (by linarith)
  refine ⟨H1 + s, H2 + s, ε, hε, hεε₀, by linarith, by linarith, by nlinarith, by nlinarith,
    by linarith, hB⟩

/-! ### Proposition 18.2 -/

/-- **Proposition 18.2** (p. 550). Under `LocalHyp` (Assumption 18.1 with `U″(c*) < 0`,
`f″(k*) < 0`) and with `H` the local solution of (7) on `I = I_{ε₀}`: for every
`λ ∈ (λ*, 1)` there is `ε > 0` with `I_ε ⊆ I` and `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`. -/
theorem prop_18_2 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, -, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  exact ⟨ε, hε, hεε₀, fun h hh => Top_mem_Dlam hB hm₂ hlpos.le hl1.le hsum hH.center hh⟩

/-! ### Exercise 18.3 -/

/-- **Exercise 18.3** (p. 551). `T` is continuous on `D_λ(I_ε)` in the sup norm: for any
`ε ≤ ε₀` and `λ ∈ [0, 1]` there is `C ≥ 0` with `‖Th − Tĥ‖ ≤ C ‖h − ĥ‖` (sup over `I_ε`);
`C = B₂(1 + λ)` where `B₂` is a Lipschitz constant of `H` in its second argument. (In particular
for the `ε` of Proposition 18.2.) -/
theorem ex_18_3 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ Dlam ks ε lam, ∀ hh ∈ Dlam ks ε lam, ∀ D : ℝ,
      (∀ k ∈ Jint ks ε, |h k - hh k| ≤ D) →
        ∀ k ∈ Jint ks ε, |Top H h k - Top H hh k| ≤ C * D := by
  obtain ⟨B₁, B₂, -, hB₂, hB⟩ := hH.lipschitz
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ B₂ * |z - z'| := fun x _ z _ z' _ => by
    simpa using hB x x z z'
  refine ⟨B₂ * (1 + lam), mul_nonneg hB₂ (by linarith), fun h hh hh' hh2 D hD k hk => ?_⟩
  exact (Top_sub_le hHz hB₂ hl0 (Dlam_mapsTo hh hl1) (Dlam_mapsTo hh2 hl1) hh2.2 hD k hk).2

/-- The functions of the counterexample to the manual's step in Exercise 18.3. -/
noncomputable def manualH (lam k : ℝ) : ℝ := -lam * k

/-- `h_c(k) = −λk + c·max(k, 0)`. -/
noncomputable def manualHc (lam c k : ℝ) : ℝ := -lam * k + c * max k 0

/-- **The manual's inequality in Exercise 18.3 is false** (NOTE 18.2-F). Let `0 < λ < 1`,
`0 < c ≤ 2λ` (e.g. `c = 2λ/n`), `k* = 0`, `ε = 1`. Then `h(k) = −λk` and
`h_c(k) = −λk + c·max(k, 0)` both lie in `D_λ([−1, 1])`, `‖h_c − h‖ ≤ c`, but at `k = −1`
`|h_c²(−1) − h²(−1)| ≤ λ|h_c(−1) − h(−1)|` fails (the left side is `cλ`, the right side `0`). -/
theorem ex_18_3_manual_counterexample {lam c : ℝ} (hl0 : 0 < lam) (hc0 : 0 < c)
    (hc : c ≤ 2 * lam) :
    manualH lam ∈ Dlam 0 1 lam ∧ manualHc lam c ∈ Dlam 0 1 lam ∧
      (∀ k ∈ Jint 0 1, |manualHc lam c k - manualH lam k| ≤ c) ∧
      ¬ (|manualHc lam c (manualHc lam c (-1)) - manualH lam (manualH lam (-1))| ≤
        lam * |manualHc lam c (-1) - manualH lam (-1)|) := by
  refine ⟨⟨by simp [manualH], fun k _ k' _ => ?_⟩, ⟨by simp [manualHc], fun k _ k' _ => ?_⟩,
    fun k hk => ?_, ?_⟩
  · simp only [manualH]
    rw [show -lam * k - -lam * k' = -lam * (k - k') by ring, abs_mul, abs_neg,
      abs_of_pos hl0]
  · simp only [manualHc]
    rw [abs_le]
    rcases le_total k' k with hkk | hkk
    · rw [abs_of_nonneg (by linarith : 0 ≤ k - k')]
      rcases le_total k 0 with hk0 | hk0 <;> rcases le_total k' 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
    · rw [abs_of_nonpos (by linarith : k - k' ≤ 0)]
      rcases le_total k 0 with hk0 | hk0 <;> rcases le_total k' 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
  · simp only [manualHc, manualH]
    have hk1 : k ≤ 1 := by have := hk.2; linarith
    rcases le_total k 0 with hk0 | hk0
    · rw [max_eq_right hk0]
      simp [hc0.le]
    · rw [max_eq_left hk0]
      rw [show -lam * k + c * k - -lam * k = c * k by ring, abs_of_nonneg (by positivity)]
      nlinarith
  · simp only [manualHc, manualH]
    have e1 : max (-1 : ℝ) 0 = 0 := by norm_num
    have e2 : max (-lam * -1 + c * 0) 0 = lam := by
      rw [show -lam * -1 + c * 0 = lam by ring, max_eq_left hl0.le]
    rw [e1, e2]
    rw [show -lam * (-lam * -1 + c * 0) + c * lam - -lam * (-lam * -1) = c * lam by ring,
      show -lam * -1 + c * 0 - -lam * -1 = 0 by ring, abs_zero, mul_zero,
      abs_of_pos (mul_pos hc0 hl0)]
    intro h
    linarith [mul_pos hc0 hl0]

/-! ### Exercise 18.4 (a) -/

/-- The first function of the counterexample to Exercise 18.4(a): `h(k) = k* − (λ/2)(k − k*)`. -/
noncomputable def ex184H (ks lam k : ℝ) : ℝ := ks - lam / 2 * (k - ks)

/-- The second function: slope `−λ/2` left of `k*`, `−λ` right of `k*`. -/
noncomputable def ex184H' (ks lam k : ℝ) : ℝ := ks - lam / 2 * (k - ks) - lam / 2 * max (k - ks) 0

/-- **Exercise 18.4(a) is false as stated** (NOTE 18.2-G). For every `λ ∈ (0, 1]` and every
`ε ∈ (0, ε₀]`, the functions `h = ex184H` and `h′ = ex184H'` lie in `D_λ(I_ε)` with `h′ ≤ h` on
`I_ε`, but `(Th)(k* + ε) < (Th′)(k* + ε)`: `h²(k* + ε) = k* + λ²ε/4 < k* + λ²ε/2 = h′²(k* + ε)`
and `H` is strictly increasing in its second argument. So `T` is not monotone on
`D_λ(I_ε)`. -/
theorem ex_18_4a_counterexample {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    ex184H ks lam ∈ Dlam ks ε lam ∧ ex184H' ks lam ∈ Dlam ks ε lam ∧
      (∀ k ∈ Jint ks ε, ex184H' ks lam k ≤ ex184H ks lam k) ∧
      Top H (ex184H ks lam) (ks + ε) < Top H (ex184H' ks lam) (ks + ε) := by
  refine ⟨⟨by simp [ex184H], fun k _ k' _ => ?_⟩, ⟨by simp [ex184H'], fun k _ k' _ => ?_⟩,
    fun k _ => ?_, ?_⟩
  · simp only [ex184H]
    rw [show ks - lam / 2 * (k - ks) - (ks - lam / 2 * (k' - ks)) = -(lam / 2) * (k - k') by
      ring, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < lam / 2)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  · simp only [ex184H']
    rw [abs_le]
    rcases le_total k' k with hkk | hkk
    · rw [abs_of_nonneg (by linarith : 0 ≤ k - k')]
      rcases le_total (k - ks) 0 with hk0 | hk0 <;>
        rcases le_total (k' - ks) 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
    · rw [abs_of_nonpos (by linarith : k - k' ≤ 0)]
      rcases le_total (k - ks) 0 with hk0 | hk0 <;>
        rcases le_total (k' - ks) 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
  · simp only [ex184H, ex184H']
    have := le_max_right (k - ks) 0
    nlinarith
  · simp only [Top, ex184H, ex184H']
    have e1 : ks - lam / 2 * (ks + ε - ks) = ks - lam * ε / 2 := by ring
    have e2 : ks - lam / 2 * (ks - lam * ε / 2 - ks) = ks + lam ^ 2 * ε / 4 := by ring
    have e3 : max (ks + ε - ks) 0 = ε := by rw [show ks + ε - ks = ε by ring, max_eq_left hε.le]
    have e4 : ks - lam / 2 * (ks + ε - ks) - lam / 2 * ε = ks - lam * ε := by ring
    have e5 : max (ks - lam * ε - ks) 0 = 0 := by
      rw [max_eq_right]
      nlinarith
    have e6 : ks - lam / 2 * (ks - lam * ε - ks) - lam / 2 * 0 = ks + lam ^ 2 * ε / 2 := by ring
    rw [e3, e4, e1, e2, e5, e6]
    have hl2 : lam ^ 2 ≤ 1 := by nlinarith
    have hmem : ∀ t, 0 ≤ t → t ≤ 1 → ks + t * ε ∈ Jint ks ε₀ := fun t ht0 ht1 =>
      ⟨by nlinarith, by nlinarith⟩
    have m1 : ks + ε ∈ Jint ks ε₀ := by simpa using hmem 1 zero_le_one le_rfl
    have m2 : ks + lam ^ 2 * ε / 4 ∈ Jint ks ε₀ := by
      have := hmem (lam ^ 2 / 4) (by positivity) (by linarith)
      rwa [show lam ^ 2 / 4 * ε = lam ^ 2 * ε / 4 by ring] at this
    have m3 : ks + lam ^ 2 * ε / 2 ∈ Jint ks ε₀ := by
      have := hmem (lam ^ 2 / 2) (by positivity) (by linarith)
      rwa [show lam ^ 2 / 2 * ε = lam ^ 2 * ε / 2 by ring] at this
    exact hH.strictMono_right _ m1 _ m2 _ m3 (by nlinarith [mul_pos (pow_pos hl0 2) hε])

/-- **Exercise 18.4(a), corrected** (the manual's version). On nondecreasing members of
`D_λ(I_ε)` (`ε ≤ ε₀`, `λ ≤ 1`) `T` is monotone: `h ≤ ĥ` on `I_ε` implies `Th ≤ Tĥ` on `I_ε`. -/
theorem ex_18_4a {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε : ℝ} (hεε₀ : ε ≤ ε₀) {h hh : ℝ → ℝ}
    (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) (hmaps' : ∀ k ∈ Jint ks ε, hh k ∈ Jint ks ε)
    (hmono : MonotoneOn h (Jint ks ε)) (hle : ∀ k ∈ Jint ks ε, h k ≤ hh k) :
    ∀ k ∈ Jint ks ε, Top H h k ≤ Top H hh k := by
  intro k hk
  have h1 : h (h k) ≤ hh (hh k) :=
    (hmono (hmaps k hk) (hmaps' k hk) (hle k hk)).trans (hle _ (hmaps' k hk))
  rcases eq_or_lt_of_le h1 with he | hlt
  · simp only [Top, he, le_refl]
  · exact (hH.strictMono_right k (Jint_mono hεε₀ hk) _ (Jint_mono hεε₀ (hmaps _ (hmaps k hk)))
      _ (Jint_mono hεε₀ (hmaps' _ (hmaps' k hk))) hlt).le

/-- **Exercise 18.4(a), second part** (manual). `T` maps nondecreasing functions mapping `I_ε`
into itself to (strictly) increasing functions on `I_ε`; with Proposition 18.2, `T` maps the
nondecreasing members of `D_λ(I_ε)` into themselves. -/
theorem ex_18_4a_mapsTo {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hεε₀ : ε ≤ ε₀) (hl1 : lam ≤ 1)
    (hT : ∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) {h : ℝ → ℝ}
    (hh : h ∈ Dlam ks ε lam) (hmono : MonotoneOn h (Jint ks ε)) :
    Top H h ∈ Dlam ks ε lam ∧ MonotoneOn (Top H h) (Jint ks ε) :=
  ⟨hT h hh, (Top_strictMonoOn hH hεε₀ (Dlam_mapsTo hh hl1) hmono).monotoneOn⟩

/-- **Exercise 18.4(b), the constants are not in `D_λ(I_ε)`** (NOTE 18.2-H): for `ε > 0`,
`h₋ ≡ k* − ε` and `h₊ ≡ k* + ε` violate `h(k*) = k*`. -/
theorem ex_18_4b_const_not_mem {ks ε lam : ℝ} (hε : 0 < ε) :
    (fun _ => ks - ε) ∉ Dlam ks ε lam ∧ (fun _ => ks + ε) ∉ Dlam ks ε lam :=
  ⟨fun h => by have := h.1; simp only at this; linarith,
    fun h => by have := h.1; simp only at this; linarith⟩

/-! ### Proposition 18.3 -/

/-- **The printed step of Proposition 18.3 is invalid** (NOTE 18.2-E): `m(1 + λ*) < δ < 1` with
`λ* < λ < 1` does not give `m(1 + λ) ≤ δ`; e.g. `λ* = 1/4`, `λ = 3/4`, `m = 1/2`, `δ = 3/4`. -/
theorem prop_18_3_printed_step_counterexample :
    ∃ ls l m δ : ℝ, 0 < ls ∧ ls < l ∧ l < 1 ∧ 0 < m ∧ m * (1 + ls) < δ ∧ δ < 1 ∧
      δ < m * (1 + l) :=
  ⟨1 / 4, 3 / 4, 1 / 2, 3 / 4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **Proposition 18.3** (p. 552), estimate form. Under `LocalHyp` with `H` the local solution:
for every `λ ∈ (λ*, 1)` there is `ε ∈ (0, ε₀]` such that `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` and, for some
`K ∈ [0, 1)`, `‖Th − Tĥ‖ ≤ K ‖h − ĥ‖` (sup over `I_ε`) for `h, ĥ ∈ D_λ(I_ε)`; `K = m₂(1 + λ)`
(the corrected constant, NOTE 18.2-E). -/
theorem prop_18_3 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ (∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) ∧
      ∃ K, 0 ≤ K ∧ K < 1 ∧ ∀ h ∈ Dlam ks ε lam, ∀ hh ∈ Dlam ks ε lam, ∀ D : ℝ,
        (∀ k ∈ Jint ks ε, |h k - hh k| ≤ D) →
          ∀ k ∈ Jint ks ε, |Top H h k - Top H hh k| ≤ K * D := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  refine ⟨ε, hε, hεε₀, fun h hh => Top_mem_Dlam hB hm₂ hlpos.le hl1.le hsum hH.center hh,
    m₂ * (1 + lam), mul_nonneg hm₂ (by linarith), hK, fun h hh hh' hh2 D hD k hk => ?_⟩
  exact (Top_sub_le hHz hm₂ hlpos.le (Dlam_mapsTo hh hl1.le) (Dlam_mapsTo hh2 hl1.le) hh2.2
    hD k hk).2

/-! ### Packaging on `C(I_ε)` -/

/-- Extension of `h ∈ C(I_ε)` to `ℝ` (constant beyond the endpoints). -/
noncomputable def extendC {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) : ℝ → ℝ :=
  Set.IccExtend (by linarith : ks - ε ≤ ks + ε) h

/-- `extendC h = h` on `I_ε`. -/
theorem extendC_of_mem {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) {x : ℝ}
    (hx : x ∈ Jint ks ε) : extendC hε h x = h ⟨x, hx⟩ :=
  Set.IccExtend_of_mem _ _ hx

/-- `extendC h` is continuous. -/
theorem continuous_extendC {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) :
    Continuous (extendC hε h) :=
  h.continuous.Icc_extend'

/-- The operator `T` on `C(I_ε)`: `(Th)(k) = H[k, h(h(k))]`, with `h` extended to `ℝ`. -/
noncomputable def TC (H : ℝ → ℝ → ℝ) (hHc : Continuous fun q : ℝ × ℝ => H q.1 q.2)
    {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) : C(Jint ks ε, ℝ) where
  toFun k := H (k : ℝ) (extendC hε h (extendC hε h k))
  continuous_toFun := hHc.comp (continuous_subtype_val.prodMk
    ((continuous_extendC hε h).comp ((continuous_extendC hε h).comp continuous_subtype_val)))

/-- On `I_ε`, `TC h` is `T` applied to the extension of `h`. -/
theorem extendC_TC (H : ℝ → ℝ → ℝ) (hHc : Continuous fun q : ℝ × ℝ => H q.1 q.2) {ks ε : ℝ}
    (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) {k : ℝ} (hk : k ∈ Jint ks ε) :
    extendC hε (TC H hHc hε h) k = Top H (extendC hε h) k := by
  rw [extendC_of_mem hε _ hk]
  rfl

/-- `D_λ(I_ε)` as a subset of `C(I_ε)`. -/
def DC (ks ε lam : ℝ) (hε : 0 < ε) : Set C(Jint ks ε, ℝ) :=
  {h | h ⟨ks, center_mem_Jint hε.le⟩ = ks ∧
    ∀ k k' : Jint ks ε, |h k - h k'| ≤ lam * |(k : ℝ) - k'|}

/-- `h ∈ DC ↔ extendC h ∈ D_λ(I_ε)`. -/
theorem mem_DC_iff {ks ε lam : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) :
    h ∈ DC ks ε lam hε ↔ extendC hε h ∈ Dlam ks ε lam := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [extendC_of_mem hε h (center_mem_Jint hε.le)]; exact h1,
      fun k hk k' hk' => ?_⟩
    rw [extendC_of_mem hε h hk, extendC_of_mem hε h hk']
    exact h2 ⟨k, hk⟩ ⟨k', hk'⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← extendC_of_mem hε h (center_mem_Jint hε.le)]; exact h1,
      fun k k' => ?_⟩
    have := h2 k k.2 k' k'.2
    rwa [extendC_of_mem hε h k.2, extendC_of_mem hε h k'.2] at this

/-- `DC` is closed in `C(I_ε)`, hence complete. -/
theorem isClosed_DC (ks ε lam : ℝ) (hε : 0 < ε) : IsClosed (DC ks ε lam hε) := by
  simp only [DC, ofPred_and, ofPred_forall]
  refine IsClosed.inter (isClosed_eq (continuous_eval_const _) continuous_const)
    (isClosed_iInter fun k => isClosed_iInter fun k' => ?_)
  exact isClosed_le ((continuous_eval_const k).sub (continuous_eval_const k')).abs
    continuous_const

/-- The constant `k*` lies in `DC` (for `λ ≥ 0`). -/
theorem const_mem_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) :
    ContinuousMap.const (Jint ks ε) ks ∈ DC ks ε lam hε :=
  ⟨rfl, fun _ _ => by simp only [ContinuousMap.const_apply, sub_self, abs_zero]; positivity⟩

/-- `TC` maps `DC` into itself (Proposition 18.2). -/
theorem TC_mapsTo {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hsum : m₁ + m₂ * lam ^ 2 ≤ lam)
    (hB : HBound H ks ε m₁ m₂) :
    MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε) := by
  intro h hh
  rw [mem_DC_iff] at hh ⊢
  exact Dlam_congr hε.le (fun k hk => (extendC_TC H hH.continuous hε h hk).symm)
    (Top_mem_Dlam hB hm₂ hl0 hl1 hsum hH.center hh)

/-- The contraction estimate on `C(I_ε)`: `dist (Th) (Tĥ) ≤ m₂(1 + λ) dist h ĥ`. -/
theorem TC_dist_le {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hB : HBound H ks ε m₁ m₂) {h hh : C(Jint ks ε, ℝ)}
    (h1 : h ∈ DC ks ε lam hε) (h2 : hh ∈ DC ks ε lam hε) :
    dist (TC H hH.continuous hε h) (TC H hH.continuous hε hh) ≤
      m₂ * (1 + lam) * dist h hh := by
  rw [mem_DC_iff] at h1 h2
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  have hD : ∀ k ∈ Jint ks ε, |extendC hε h k - extendC hε hh k| ≤ dist h hh := by
    intro k hk
    rw [extendC_of_mem hε h hk, extendC_of_mem hε hh hk, ← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  refine (ContinuousMap.dist_le (mul_nonneg (mul_nonneg hm₂ (by linarith)) dist_nonneg)).2
    fun k => ?_
  rw [Real.dist_eq]
  exact (Top_sub_le hHz hm₂ hl0 (Dlam_mapsTo h1 hl1) (Dlam_mapsTo h2 hl1) h2.2 hD k k.2).2

/-- **`T` is a contraction of `DC`** (`ContractingWith`), given `m₂(1 + λ) < 1`. -/
theorem TC_contractingWith {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hK : m₂ * (1 + lam) < 1) (hB : HBound H ks ε m₁ m₂)
    (hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε)) :
    ContractingWith (Real.toNNReal (m₂ * (1 + lam))) (hmaps.restrict _ _ _) := by
  have hK0 : 0 ≤ m₂ * (1 + lam) := mul_nonneg hm₂ (by linarith)
  refine ⟨Real.toNNReal_lt_one.2 hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal _ hK0, Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply,
    MapsTo.val_restrict_apply]
  exact TC_dist_le hH hε hl0 hl1 hm₂ hB x.2 y.2

/-- **Exercise 18.3, packaged**: the restriction of `T` to `DC` is continuous. -/
theorem ex_18_3_continuous {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hB : HBound H ks ε m₁ m₂)
    (hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε)) :
    Continuous (hmaps.restrict _ _ _) := by
  have hK0 : 0 ≤ m₂ * (1 + lam) := mul_nonneg hm₂ (by linarith)
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (m₂ * (1 + lam)))
    fun x y => ?_).continuous
  rw [Real.coe_toNNReal _ hK0, Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply,
    MapsTo.val_restrict_apply]
  exact TC_dist_le hH hε hl0 hl1 hm₂ hB x.2 y.2

/-- **Proposition 18.3** (p. 552), `ContractingWith` form: for every `λ ∈ (λ*, 1)` there is
`ε ∈ (0, ε₀]` such that `T` maps `DC = D_λ(I_ε) ⊆ C(I_ε)` into itself and is a contraction
there with modulus `K < 1`. -/
theorem prop_18_3_contractingWith {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ ε₀ ∧
      ∃ hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε),
        ∃ K : NNReal, K < 1 ∧ ContractingWith K (hmaps.restrict _ _ _) := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  have hmaps := TC_mapsTo hH hε hlpos.le hl1.le hm₂ hsum hB
  have hc := TC_contractingWith hH hε hlpos.le hl1.le hm₂ hK hB hmaps
  exact ⟨ε, hε, hεε₀, hmaps, _, hc.1, hc⟩

/-! ### Proposition 18.4 -/

/-- **Proposition 18.4** (p. 553). Let `(λ, I_ε)` (`0 ≤ λ ≤ 1`, `ε ≤ ε₀`) be such that `T` maps
`DC = D_λ(I_ε)` into itself and is a contraction there, and let `g ∈ DC` be its fixed point.
Then `g` is strictly increasing on `I_ε`. (Corollary 1 to Theorem 3.2: `T` maps the closed set
of nondecreasing members into the strictly increasing ones, so the limit of the iterates from
the constant `k*` is nondecreasing, and then `g = Tg` is strictly increasing.) -/
theorem prop_18_4 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε)) {K : NNReal}
    (hK : ContractingWith K (hmaps.restrict _ _ _)) {g : C(Jint ks ε, ℝ)}
    (hg : g ∈ DC ks ε lam hε) (hfix : TC H hH.continuous hε g = g) :
    StrictMonoOn (extendC hε g) (Jint ks ε) := by
  have : Nonempty (DC ks ε lam hε) := ⟨⟨g, hg⟩⟩
  have : CompleteSpace (DC ks ε lam hε) := (isClosed_DC ks ε lam hε).isComplete.completeSpace_coe
  set T := hmaps.restrict _ _ _ with hT
  -- the closed set of nondecreasing members
  set D' : Set (DC ks ε lam hε) :=
    {h | ∀ p : {q : Jint ks ε × Jint ks ε // q.1 ≤ q.2}, (h : C(Jint ks ε, ℝ)) p.1.1 ≤
      (h : C(Jint ks ε, ℝ)) p.1.2} with hD'
  have hD'c : IsClosed D' := by
    simp only [hD', ofPred_forall]
    exact isClosed_iInter fun p => isClosed_le
      ((continuous_eval_const p.1.1).comp continuous_subtype_val)
      ((continuous_eval_const p.1.2).comp continuous_subtype_val)
  -- `T` maps nondecreasing members to strictly increasing (hence nondecreasing) ones
  have hmonoT : ∀ h : DC ks ε lam hε, h ∈ D' → T h ∈ D' := by
    intro h hh p
    have hmem := (mem_DC_iff hε _).1 h.2
    have hmono : MonotoneOn (extendC hε h.1) (Jint ks ε) := by
      intro x hx y hy hxy
      rw [extendC_of_mem hε _ hx, extendC_of_mem hε _ hy]
      exact hh ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
    have hsm := Top_strictMonoOn hH hεε₀ (Dlam_mapsTo hmem hl1) hmono
    have e1 := extendC_TC H hH.continuous hε (h : C(Jint ks ε, ℝ)) p.1.1.2
    have e2 := extendC_TC H hH.continuous hε (h : C(Jint ks ε, ℝ)) p.1.2.2
    rw [extendC_of_mem hε _ p.1.1.2] at e1
    rw [extendC_of_mem hε _ p.1.2.2] at e2
    rw [hT, MapsTo.val_restrict_apply]
    change TC H hH.continuous hε h p.1.1 ≤ TC H hH.continuous hε h p.1.2
    rw [e1, e2]
    exact hsm.monotoneOn p.1.1.2 p.1.2.2 p.2
  have hc : (⟨ContinuousMap.const (Jint ks ε) ks, const_mem_DC hε hl0⟩ : DC ks ε lam hε) ∈ D' :=
    fun p => le_rfl
  have hiter : ∀ n, T^[n] ⟨ContinuousMap.const (Jint ks ε) ks, const_mem_DC hε hl0⟩ ∈ D' := by
    intro n
    induction n with
    | zero => exact hc
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hmonoT _ ih
  have hgfix : (⟨g, hg⟩ : DC ks ε lam hε) = ContractingWith.fixedPoint T hK :=
    hK.fixedPoint_unique (Subtype.ext (by rw [hT, MapsTo.val_restrict_apply]; exact hfix))
  have hgD' : (⟨g, hg⟩ : DC ks ε lam hε) ∈ D' := by
    rw [hgfix]
    exact hD'c.mem_of_tendsto (hK.tendsto_iterate_fixedPoint _) (Eventually.of_forall hiter)
  have hmono : MonotoneOn (extendC hε g) (Jint ks ε) := by
    intro x hx y hy hxy
    rw [extendC_of_mem hε _ hx, extendC_of_mem hε _ hy]
    exact hgD' ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
  have hmem := (mem_DC_iff hε _).1 hg
  have hsm := Top_strictMonoOn hH hεε₀ (Dlam_mapsTo hmem hl1) hmono
  intro x hx y hy hxy
  have hx' : extendC hε g x = Top H (extendC hε g) x := by
    rw [← extendC_TC H hH.continuous hε g hx, hfix]
  have hy' : extendC hε g y = Top H (extendC hε g) y := by
    rw [← extendC_TC H hH.continuous hε g hy, hfix]
  rw [hx', hy']
  exact hsm hx hy hxy

/-! ### The fixed point -/

/-- **Uniqueness of fixed points** under the contraction estimate. If `h, g` map `I_ε` into
itself, `g` is `λ`-Lipschitz on `I_ε`, `m₂(1 + λ) < 1`, and both are fixed by `T` on `I_ε`, then
`h = g` on `I_ε`. -/
theorem eq_of_fixed {H : ℝ → ℝ → ℝ} {ks ε lam m₁ m₂ : ℝ} (hB : HBound H ks ε m₁ m₂)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) (hK : m₂ * (1 + lam) < 1) {h g : ℝ → ℝ}
    (hh : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) (hg : ∀ k ∈ Jint ks ε, g k ∈ Jint ks ε)
    (hgL : ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |g k - g k'| ≤ lam * |k - k'|)
    (hhf : ∀ k ∈ Jint ks ε, Top H h k = h k) (hgf : ∀ k ∈ Jint ks ε, Top H g k = g k) :
    ∀ k ∈ Jint ks ε, h k = g k := by
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  set K := m₂ * (1 + lam) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hm₂ (by linarith)
  have hbound : ∀ n : ℕ, ∀ k ∈ Jint ks ε, |h k - g k| ≤ K ^ n * (2 * ε) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have h1 := mem_Jint_iff.1 (hh k hk)
      have h2 := mem_Jint_iff.1 (hg k hk)
      rw [pow_zero, one_mul]
      calc |h k - g k| = |(h k - ks) - (g k - ks)| := by ring_nf
        _ ≤ |h k - ks| + |g k - ks| := abs_sub _ _
        _ ≤ 2 * ε := by linarith
    | succ n ih =>
      intro k hk
      have := (Top_sub_le hHz hm₂ hl0 hh hg hgL ih k hk).2
      rw [hhf k hk, hgf k hk] at this
      calc |h k - g k| ≤ K * (K ^ n * (2 * ε)) := this
        _ = K ^ (n + 1) * (2 * ε) := by ring
  intro k hk
  have hlim : Tendsto (fun n : ℕ => K ^ n * (2 * ε)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const (2 * ε)
  have h0 : |h k - g k| ≤ 0 := ge_of_tendsto' hlim fun n => hbound n k hk
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **Existence of the fixed point** for given constants (Contraction Mapping Theorem on `DC`,
with Proposition 18.4): a `g ∈ D_λ(I_ε)` with `Tg = g` on `I_ε`, strictly increasing on
`I_ε`. -/
theorem exists_fixedPoint_of_bounds {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hsum : m₁ + m₂ * lam ^ 2 ≤ lam)
    (hK : m₂ * (1 + lam) < 1) (hB : HBound H ks ε m₁ m₂) :
    ∃ g : ℝ → ℝ, g ∈ Dlam ks ε lam ∧ (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      StrictMonoOn g (Jint ks ε) := by
  have hmaps := TC_mapsTo hH hε hl0 hl1 hm₂ hsum hB
  have hc := TC_contractingWith hH hε hl0 hl1 hm₂ hK hB hmaps
  have : Nonempty (DC ks ε lam hε) :=
    ⟨⟨ContinuousMap.const (Jint ks ε) ks, const_mem_DC hε hl0⟩⟩
  have : CompleteSpace (DC ks ε lam hε) := (isClosed_DC ks ε lam hε).isComplete.completeSpace_coe
  set g0 := ContractingWith.fixedPoint _ hc with hg0
  have hfix : TC H hH.continuous hε g0.1 = g0.1 := by
    have := ContractingWith.fixedPoint_isFixedPt (f := hmaps.restrict _ _ _) hc
    rw [← hg0] at this
    have := congrArg Subtype.val this
    rwa [MapsTo.val_restrict_apply] at this
  refine ⟨extendC hε g0.1, (mem_DC_iff hε _).1 g0.2, fun k hk => ?_,
    prop_18_4 hH hε hεε₀ hl0 hl1 hmaps hc g0.2 hfix⟩
  rw [← extendC_TC H hH.continuous hε g0.1 hk, hfix]

/-- **Consequences of Proposition 18.3** (p. 553). For every `λ ∈ (λ*, 1)` there are
`ε ∈ (0, ε₀]` and `g ∈ D_λ(I_ε)` such that: `g = Tg` on `I_ε`; `g` solves the Euler equation (4)
`F[k, g(k), g²(k)] = 0` on `I_ε`; `g` is the unique fixed point of `T` in `D_λ(I_ε)`; `g` is
strictly increasing on `I_ε` (Proposition 18.4); and `|g^t(k) − k*| ≤ λ^t |k − k*|`, so
`k_t → k*` from every `k₀ ∈ I_ε` (local stability). -/
theorem prop_18_3_fixedPoint {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∃ g : ℝ → ℝ, g ∈ Dlam ks ε lam ∧
      (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      (∀ k ∈ Jint ks ε, Feq β θ U f k (g k) (g (g k)) = 0) ∧
      (∀ g' ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g' k = g' k) →
        ∀ k ∈ Jint ks ε, g' k = g k) ∧
      StrictMonoOn g (Jint ks ε) ∧
      ∀ k ∈ Jint ks ε, ∀ t : ℕ, |g^[t] k - ks| ≤ lam ^ t * |k - ks| := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨g, hg, hfix, hsm⟩ :=
    exists_fixedPoint_of_bounds hH hε hεε₀ hlpos.le hl1.le hm₂ hsum hK hB
  have hgm := Dlam_mapsTo hg hl1.le
  refine ⟨ε, hε, hεε₀, g, hg, hfix, fun k hk => ?_, fun g' hg' hfix' k hk => ?_, hsm,
    fun k hk t => ?_⟩
  · have h7 := hH.eq7 k (Jint_mono hεε₀ hk) _ (Jint_mono hεε₀ (hgm _ (hgm k hk)))
    have e : H k (g (g k)) = g k := hfix k hk
    rwa [e] at h7
  · exact eq_of_fixed hB hm₂ hlpos.le hK (Dlam_mapsTo hg' hl1.le) hgm hg.2 hfix' hfix k hk
  · have hiter : ∀ t : ℕ, g^[t] k ∈ Jint ks ε := by
      intro t
      induction t with
      | zero => exact hk
      | succ t ih => rw [Function.iterate_succ_apply']; exact hgm _ ih
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      have h1 := hg.2 _ (hiter t) ks (center_mem_Jint hε.le)
      rw [hg.1] at h1
      calc |g (g^[t] k) - ks| ≤ lam * |g^[t] k - ks| := h1
        _ ≤ lam * (lam ^ t * |k - ks|) := mul_le_mul_of_nonneg_left ih hlpos.le
        _ = lam ^ (t + 1) * |k - ks| := by ring

/-! ### Exercise 18.4 (b), repaired -/

/-- The set `E` of NOTE 18.2-H: nondecreasing, `λ`-Lipschitz maps of `I_ε` into itself. -/
def Elam (ks ε lam : ℝ) : Set (ℝ → ℝ) :=
  {h | (∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) ∧ MonotoneOn h (Jint ks ε) ∧
    ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |h k - h k'| ≤ lam * |k - k'|}

/-- **Exercise 18.4(b), repaired** (NOTE 18.2-H). For every `λ ∈ (λ*, 1)` there are
`ε ∈ (0, ε₀]` and `g` (the fixed point of Proposition 18.3, in `D_λ(I_ε) ∩ E`) such that, with
`h₋ ≡ k* − ε`, `h₊ ≡ k* + ε`:
(i) `T(E) ⊆ E` and `T` is monotone on `E`; (ii) `h₋, h₊ ∈ E`, `h₋ ≤ Th₋`, `Th₊ ≤ h₊` on `I_ε`;
(iii) `Tⁿh₋` is nondecreasing and `Tⁿh₊` nonincreasing in `n`; (iv) for some `K ∈ [0, 1)`,
`|Tⁿh₋ − g| ≤ Kⁿ·2ε` and `|Tⁿh₊ − g| ≤ Kⁿ·2ε` on `I_ε`, so both limits exist (uniformly) and
equal `g`, a fixed point of `T`; (v) `g` is the unique fixed point of `T` in `E`. -/
theorem ex_18_4b {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∃ g : ℝ → ℝ, ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧
      (∀ h ∈ Elam ks ε lam, Top H h ∈ Elam ks ε lam) ∧
      (∀ h ∈ Elam ks ε lam, ∀ hh ∈ Elam ks ε lam, (∀ k ∈ Jint ks ε, h k ≤ hh k) →
        ∀ k ∈ Jint ks ε, Top H h k ≤ Top H hh k) ∧
      (fun _ => ks - ε) ∈ Elam ks ε lam ∧ (fun _ => ks + ε) ∈ Elam ks ε lam ∧
      (∀ k ∈ Jint ks ε, ks - ε ≤ Top H (fun _ => ks - ε) k) ∧
      (∀ k ∈ Jint ks ε, Top H (fun _ => ks + ε) k ≤ ks + ε) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, (Top H)^[n] (fun _ => ks - ε) k ≤
        (Top H)^[n + 1] (fun _ => ks - ε) k) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, (Top H)^[n + 1] (fun _ => ks + ε) k ≤
        (Top H)^[n] (fun _ => ks + ε) k) ∧
      g ∈ Dlam ks ε lam ∧ g ∈ Elam ks ε lam ∧ (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, |(Top H)^[n] (fun _ => ks - ε) k - g k| ≤ K ^ n * (2 * ε)) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, |(Top H)^[n] (fun _ => ks + ε) k - g k| ≤ K ^ n * (2 * ε)) ∧
      (∀ k ∈ Jint ks ε, Tendsto (fun n => (Top H)^[n] (fun _ => ks - ε) k) atTop (𝓝 (g k))) ∧
      (∀ k ∈ Jint ks ε, Tendsto (fun n => (Top H)^[n] (fun _ => ks + ε) k) atTop (𝓝 (g k))) ∧
      ∀ h ∈ Elam ks ε lam, (∀ k ∈ Jint ks ε, Top H h k = h k) → ∀ k ∈ Jint ks ε, h k = g k := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, hm₁, hm₂, hsum, hK, hm12, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨g, hg, hfix, hsm⟩ :=
    exists_fixedPoint_of_bounds hH hε hεε₀ hlpos.le hl1.le hm₂ hsum hK hB
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  set K := m₂ * (1 + lam) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hm₂ (by linarith)
  have hks := center_mem_Jint (p := ks) hε.le
  -- (i) `T(E) ⊆ E`
  have hTE : ∀ h ∈ Elam ks ε lam, Top H h ∈ Elam ks ε lam := by
    rintro h ⟨hmaps, hmono, hL⟩
    refine ⟨fun k hk => ?_, (Top_strictMonoOn hH hεε₀ hmaps hmono).monotoneOn,
      fun k hk k' hk' => (Top_lipschitz hB hm₂ hlpos.le hmaps hL k hk k' hk').trans
        (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))⟩
    have h1 := hB k hk ks hks _ (hmaps _ (hmaps k hk)) ks hks
    rw [hH.center] at h1
    have h2 := mem_Jint_iff.1 hk
    have h3 := mem_Jint_iff.1 (hmaps _ (hmaps k hk))
    rw [mem_Jint_iff]
    have h4 := mul_le_mul_of_nonneg_left h2 hm₁
    have h5 := mul_le_mul_of_nonneg_left h3 hm₂
    have h6 := mul_le_mul_of_nonneg_right hm12 hε.le
    change |H k (h (h k)) - ks| ≤ ε
    linarith
  have hTmono : ∀ h ∈ Elam ks ε lam, ∀ hh ∈ Elam ks ε lam, (∀ k ∈ Jint ks ε, h k ≤ hh k) →
      ∀ k ∈ Jint ks ε, Top H h k ≤ Top H hh k := fun h hh hh' hh2 hle =>
    ex_18_4a hH hεε₀ hh.1 hh2.1 hh.2.1 hle
  have hconst : ∀ c ∈ Jint ks ε, (fun _ => c) ∈ Elam ks ε lam := fun c hc =>
    ⟨fun _ _ => hc, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ => by
      simp only [sub_self, abs_zero]; positivity⟩
  have hlo : ks - ε ∈ Jint ks ε := ⟨le_rfl, by linarith⟩
  have hhi : ks + ε ∈ Jint ks ε := ⟨by linarith, le_rfl⟩
  have hEm : ∀ n : ℕ, ∀ c ∈ Jint ks ε, (Top H)^[n] (fun _ => c) ∈ Elam ks ε lam := by
    intro n c hc
    induction n with
    | zero => exact hconst c hc
    | succ n ih => rw [Function.iterate_succ_apply']; exact hTE _ ih
  have hgE : g ∈ Elam ks ε lam := ⟨Dlam_mapsTo hg hl1.le, hsm.monotoneOn, hg.2⟩
  -- convergence bound
  have hconv : ∀ h ∈ Elam ks ε lam, ∀ n : ℕ, ∀ k ∈ Jint ks ε,
      |(Top H)^[n] h k - g k| ≤ K ^ n * (2 * ε) := by
    intro h hh n
    induction n with
    | zero =>
      intro k hk
      have h1 := mem_Jint_iff.1 (hh.1 k hk)
      have h2 := mem_Jint_iff.1 (hgE.1 k hk)
      rw [pow_zero, one_mul, Function.iterate_zero_apply]
      calc |h k - g k| = |(h k - ks) - (g k - ks)| := by ring_nf
        _ ≤ |h k - ks| + |g k - ks| := abs_sub _ _
        _ ≤ 2 * ε := by linarith
    | succ n ih =>
      intro k hk
      have hmem : (Top H)^[n] h ∈ Elam ks ε lam := by
        clear ih
        induction n with
        | zero => exact hh
        | succ n ih' => rw [Function.iterate_succ_apply']; exact hTE _ ih'
      have := (Top_sub_le hHz hm₂ hlpos.le hmem.1 hgE.1 hg.2 ih k hk).2
      rw [hfix k hk] at this
      rw [Function.iterate_succ_apply']
      calc |Top H ((Top H)^[n] h) k - g k| ≤ K * (K ^ n * (2 * ε)) := this
        _ = K ^ (n + 1) * (2 * ε) := by ring
  have hlim : Tendsto (fun n : ℕ => K ^ n * (2 * ε)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const (2 * ε)
  have htend : ∀ h ∈ Elam ks ε lam, ∀ k ∈ Jint ks ε,
      Tendsto (fun n => (Top H)^[n] h k) atTop (𝓝 (g k)) := by
    intro h hh k hk
    have h1 : Tendsto (fun n => (Top H)^[n] h k - g k) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hconv h hh n k hk) hlim
    simpa using h1.add_const (g k)
  refine ⟨ε, hε, hεε₀, g, K, hK0, hK, hTE, hTmono, hconst _ hlo, hconst _ hhi,
    fun k hk => ((hTE _ (hconst _ hlo)).1 k hk).1, fun k hk => ((hTE _ (hconst _ hhi)).1 k hk).2,
    ?_, ?_, hg, hgE, hfix, hconv _ (hconst _ hlo), hconv _ (hconst _ hhi),
    htend _ (hconst _ hlo), htend _ (hconst _ hhi), fun h hh hhf k hk =>
      eq_of_fixed hB hm₂ hlpos.le hK hh.1 hgE.1 hg.2 hhf hfix k hk⟩
  · intro n
    induction n with
    | zero => exact fun k hk => ((hTE _ (hconst _ hlo)).1 k hk).1
    | succ n ih =>
      intro k hk
      have e1 : (Top H)^[n + 1] (fun _ => ks - ε) = Top H ((Top H)^[n] (fun _ => ks - ε)) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (Top H)^[n + 1 + 1] (fun _ => ks - ε) =
          Top H ((Top H)^[n + 1] (fun _ => ks - ε)) := Function.iterate_succ_apply' _ _ _
      rw [e2, e1]
      rw [e1] at ih
      exact hTmono _ (hEm n _ hlo) _ (hTE _ (hEm n _ hlo)) ih k hk
  · intro n
    induction n with
    | zero => exact fun k hk => ((hTE _ (hconst _ hhi)).1 k hk).2
    | succ n ih =>
      intro k hk
      have e1 : (Top H)^[n + 1] (fun _ => ks + ε) = Top H ((Top H)^[n] (fun _ => ks + ε)) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (Top H)^[n + 1 + 1] (fun _ => ks + ε) =
          Top H ((Top H)^[n + 1] (fun _ => ks + ε)) := Function.iterate_succ_apply' _ _ _
      rw [e2, e1]
      rw [e1] at ih
      exact hTmono _ (hTE _ (hEm n _ hhi)) _ (hEm n _ hhi) ih k hk

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A concrete economy satisfying Assumption 18.1

SLP §18.2. The economy `β = θ = 1/2`, `f(k) = 9 − 8e^{−k}` (`exF`) satisfies Assumption 18.1
for every admissible utility `U` (`exModel_assumption`), with `k* = log 2` and
`c* = 5 − 3 log 2`. This makes the local analysis non-vacuous and turns two corrections into
counterexamples about an actual economy.

* `exModel_assumption`: Assumption 18.1 holds (with some `k̄ ∈ (0, 9)`) for any `C²`, strictly
  increasing, strictly concave `U`; `k* = log 2 ∈ (0, k̄)` solves (5).
* `exModel_localHyp` (non-vacuity): with `U(c) = 1 − e^{−c}` (`exU`) all hypotheses of the local
  analysis hold, `U″(c*) < 0` and `f″(k*) < 0` included.
* `note_18_2B_model_counterexample` (NOTE 18.2-B): with `U = U_{c*}` (`flatU`, strictly
  concave with `U″(c*) = 0`), Assumption 18.1 holds but `P(0) = 0`, so the book's claim
  `P(0) < 0` fails for an economy satisfying Assumption 18.1.
* `ex_18_4a_model_counterexample` (NOTE 18.2-G): in the economy with `U = exU`, for every
  `λ ∈ (λ*, 1)` there is `ε` as in Proposition 18.2 (so `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`) for which `T` is
  not monotone on `D_λ(I_ε)`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- The production function `f(k) = 9 − 8e^{−k}`. -/
noncomputable def exF (k : ℝ) : ℝ := 9 - 8 * Real.exp (-k)

/-- The utility function `U(c) = 1 − e^{−c}`. -/
noncomputable def exU (c : ℝ) : ℝ := 1 - Real.exp (-c)

/-- `ψ(k) − k = 9 − 8e^{−k} − 4k e^{−k} − k` for `θ = 1/2`. -/
noncomputable def exG (k : ℝ) : ℝ := 9 - 8 * Real.exp (-k) - 4 * k * Real.exp (-k) - k

/-- `(e^{−x})′ = −e^{−x}`. -/
theorem hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-x)) x := by
  simpa using (hasDerivAt_neg x).exp

/-- `f′(k) = 8e^{−k}`. -/
theorem deriv_exF : deriv exF = fun k => 8 * Real.exp (-k) := by
  funext k
  have := ((hasDerivAt_exp_neg k).const_mul 8).const_sub 9
  exact this.deriv.trans (by ring)

/-- `f″(k) = −8e^{−k}`. -/
theorem deriv2_exF : deriv (deriv exF) = fun k => -8 * Real.exp (-k) := by
  rw [deriv_exF]
  funext k
  rw [((hasDerivAt_exp_neg k).const_mul 8).deriv]
  ring

/-- `U′(c) = e^{−c}`. -/
theorem deriv_exU : deriv exU = fun c => Real.exp (-c) := by
  funext c
  have := (hasDerivAt_exp_neg c).const_sub 1
  exact this.deriv.trans (by ring)

/-- `U″(c) = −e^{−c}`. -/
theorem deriv2_exU : deriv (deriv exU) = fun c => -Real.exp (-c) := by
  rw [deriv_exU]
  funext c
  rw [(hasDerivAt_exp_neg c).deriv]

/-- `ψ(k) − k = exG k`. -/
theorem psi_exF (k : ℝ) : psi (1 / 2) exF k - k = exG k := by
  simp only [psi, deriv_exF, exF, exG]
  ring

/-- `exG′(k) = 4e^{−k} + 4k e^{−k} − 1`. -/
theorem hasDerivAt_exG (k : ℝ) :
    HasDerivAt exG (4 * Real.exp (-k) + 4 * k * Real.exp (-k) - 1) k := by
  have h1 := (hasDerivAt_exp_neg k).const_mul 8
  have h2 := ((hasDerivAt_id' k).const_mul 4).mul (hasDerivAt_exp_neg k)
  have h3 := (((h1.const_sub 9).sub h2).sub (hasDerivAt_id' k))
  exact h3.congr_deriv (by ring)

/-- `exG″(k) = −4k e^{−k}`. -/
theorem deriv2_exG (k : ℝ) : deriv (deriv exG) k = -4 * k * Real.exp (-k) := by
  have e : deriv exG = fun k => 4 * Real.exp (-k) + 4 * k * Real.exp (-k) - 1 :=
    funext fun k => (hasDerivAt_exG k).deriv
  rw [e]
  have h1 := (hasDerivAt_exp_neg k).const_mul 4
  have h2 := ((hasDerivAt_id' k).const_mul 4).mul (hasDerivAt_exp_neg k)
  have h3 : HasDerivAt (fun k => 4 * Real.exp (-k) + 4 * k * Real.exp (-k) - 1)
      (4 * -Real.exp (-k) + (4 * 1 * Real.exp (-k) + 4 * k * -Real.exp (-k))) k :=
    (h1.add h2).sub_const 1
  rw [h3.deriv]
  ring

/-- `exG` is continuous. -/
theorem continuous_exG : Continuous exG := by
  unfold exG
  fun_prop

/-- **Assumption 18.1 for `f(k) = 9 − 8e^{−k}`, `β = θ = 1/2`**, and any `C²`, strictly
increasing, strictly concave `U`; moreover `k* = log 2 ∈ (0, k̄)` solves (5). -/
theorem exModel_assumption {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hUm : StrictMonoOn U (Ici 0))
    (hUc : StrictConcaveOn ℝ (Ici 0) U) :
    ∃ kbar, Assumption18_1 (1 / 2) (1 / 2) U exF kbar ∧ Real.log 2 ∈ Ioo 0 kbar ∧
      1 / 2 * (1 - 1 / 2) * deriv exF (Real.log 2) = 1 := by
  have hfC : ContDiff ℝ 2 exF := by
    unfold exF
    fun_prop
  have hfd : ∀ k, 0 < deriv exF k := fun k => by
    rw [deriv_exF]
    positivity
  have hfc : Continuous exF := by
    unfold exF
    fun_prop
  have hfconc : StrictConcaveOn ℝ univ exF := by
    refine strictConcaveOn_univ_of_deriv2_neg hfc fun x => ?_
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [deriv2_exF]
    have := Real.exp_pos (-x)
    linarith
  -- strict concavity of `ψ − id` on `[0, ∞)`
  have hGc : StrictConcaveOn ℝ (Ici 0) exG := by
    refine strictConcaveOn_of_deriv2_neg (convex_Ici 0) continuous_exG.continuousOn
      fun x hx => ?_
    rw [interior_Ici] at hx
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [deriv2_exG]
    have := Real.exp_pos (-x)
    have := mem_Ioi.1 hx
    nlinarith
  have hG0 : exG 0 = 1 := by norm_num [exG]
  have hG9 : exG 9 < 0 := by
    have : exG 9 = -44 * Real.exp (-9) := by simp only [exG]; ring
    rw [this]
    have := Real.exp_pos (-9)
    linarith
  obtain ⟨kbar, hk, hkv⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 9)
    continuous_exG.continuousOn ⟨hG9.le, by rw [hG0]; norm_num⟩
  have hk0 : 0 < kbar := by
    rcases eq_or_lt_of_le hk.1 with h | h
    · rw [← h, hG0] at hkv
      norm_num at hkv
    · exact h
  -- sign pattern of `ψ − id`
  have hpos : ∀ k ∈ Ioo 0 kbar, 0 < exG k := by
    intro k ⟨hk1, hk2⟩
    have h3' : 0 < 1 - k / kbar := by
      rw [sub_pos, div_lt_one hk0]
      exact hk2
    have := hGc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hk0.le) hk0.ne h3' (div_pos hk1 hk0) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hkv, mul_zero, add_zero, hG0, mul_one] at this
    rw [div_mul_cancel₀ k hk0.ne'] at this
    have h3 : 0 < 1 - k / kbar := by
      rw [sub_pos, div_lt_one hk0]
      exact hk2
    linarith
  have hneg : ∀ k, kbar < k → exG k < 0 := by
    intro k hk1
    have hkp : 0 < k := hk0.trans hk1
    have := hGc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hkp.le) hkp.ne
      (by rw [sub_pos, div_lt_one hkp]; exact hk1 : 0 < 1 - kbar / k) (div_pos hk0 hkp)
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hG0, mul_one] at this
    rw [div_mul_cancel₀ kbar hkp.ne', hkv] at this
    have h3 : 0 < 1 - kbar / k := by rw [sub_pos, div_lt_one hkp]; exact hk1
    have h4 : 0 < kbar / k := div_pos hk0 hkp
    nlinarith
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog1 := Real.log_two_lt_d9
  have hGlog : 0 < exG (Real.log 2) := by
    have e : exG (Real.log 2) = 5 - 3 * Real.log 2 := by
      simp only [exG, Real.exp_neg, Real.exp_log two_pos]
      ring
    rw [e]
    norm_num at hlog1
    linarith
  have hlogk : Real.log 2 < kbar := by
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hc with h | h
    · rw [h] at hkv
      linarith
    · linarith [hneg _ h]
  refine ⟨kbar, ⟨by norm_num, by norm_num, hU, hUm, hUc, by norm_num, by norm_num, hfC,
    fun k hk => ?_, (strictMono_of_deriv_pos hfd).strictMonoOn _,
    hfconc.subset (subset_univ _) (convex_Ici 0), by norm_num [exF], ?_, hk0,
    fun k hk => ?_, fun k hk => ?_⟩, ⟨hlog, hlogk⟩, ?_⟩
  · simp only [exF]
    have : Real.exp (-k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  · rw [deriv_exF]
    norm_num
  · have := hpos k hk
    rw [← psi_exF] at this
    linarith
  · have := hneg k hk
    rw [← psi_exF] at this
    linarith
  · rw [deriv_exF]
    simp only [Real.exp_neg, Real.exp_log two_pos]
    norm_num

/-- `exU` is admissible: `C²`, strictly increasing and strictly concave. -/
theorem exU_admissible :
    ContDiff ℝ 2 exU ∧ StrictMonoOn exU (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) exU := by
  have hc : Continuous exU := by
    unfold exU
    fun_prop
  refine ⟨by unfold exU; fun_prop, (strictMono_of_deriv_pos fun c => ?_).strictMonoOn _,
    (strictConcaveOn_univ_of_deriv2_neg hc fun x => ?_).subset (subset_univ _) (convex_Ici 0)⟩
  · rw [deriv_exU]
    positivity
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [deriv2_exU]
    have := Real.exp_pos (-x)
    linarith

/-- **Non-vacuity of the local analysis.** In the economy `β = θ = 1/2`, `f(k) = 9 − 8e^{−k}`,
`U(c) = 1 − e^{−c}`, Assumption 18.1 holds and so do the hypotheses `LocalHyp` at
`k* = log 2` (in particular `U″(c*) < 0`, `f″(k*) < 0`). -/
theorem exModel_localHyp :
    ∃ kbar, Assumption18_1 (1 / 2) (1 / 2) exU exF kbar ∧
      LocalHyp (1 / 2) (1 / 2) exU exF (Real.log 2) := by
  obtain ⟨hU, hUm, hUc⟩ := exU_admissible
  obtain ⟨kbar, A, hks, heul⟩ := exModel_assumption hU hUm hUc
  refine ⟨kbar, A, A.localHyp hks heul ?_ ?_⟩
  · rw [deriv2_exU]
    have := Real.exp_pos (-cstar (1 / 2) exF (Real.log 2))
    linarith
  · rw [deriv2_exF]
    have := Real.exp_pos (-Real.log 2)
    linarith

/-- **NOTE 18.2-B in an economy satisfying Assumption 18.1.** With `β = θ = 1/2`,
`f(k) = 9 − 8e^{−k}` and the strictly concave `U = U_{c*}` of
`strictConcave_deriv2_zero_counterexample` (`U″(c*) = 0`), Assumption 18.1 holds and `k* = log 2`
solves (5), but `P(0) = 0`: the book's claim `P(0) < 0` (p. 549) is false. -/
theorem note_18_2B_model_counterexample :
    ∃ kbar, Assumption18_1 (1 / 2) (1 / 2) (flatU (cstar (1 / 2) exF (Real.log 2))) exF kbar ∧
      Real.log 2 ∈ Ioo 0 kbar ∧ 1 / 2 * (1 - 1 / 2) * deriv exF (Real.log 2) = 1 ∧
      ¬ charPoly (1 / 2) (1 / 2) (flatU (cstar (1 / 2) exF (Real.log 2))) exF
        (Real.log 2) 0 < 0 := by
  obtain ⟨hC, hm, hc, h0⟩ := strictConcave_deriv2_zero_counterexample
    (cstar (1 / 2) exF (Real.log 2))
  obtain ⟨kbar, A, hks, heul⟩ := exModel_assumption hC (hm.strictMonoOn _)
    (hc.subset (subset_univ _) (convex_Ici 0))
  refine ⟨kbar, A, hks, heul, ?_⟩
  rw [(charPoly_degenerate_U h0).2.2.1]
  exact lt_irrefl 0

/-- **Exercise 18.4(a) is false in an economy satisfying Assumption 18.1** (NOTE 18.2-G). In the
economy of `exModel_localHyp` there is a local solution `H` of (7) such that for every
`λ ∈ (λ*, 1)` there is `ε` as in Proposition 18.2 (`T(D_λ(I_ε)) ⊆ D_λ(I_ε)`) but `T` is not
monotone on `D_λ(I_ε)`: some `h′ ≤ h` in `D_λ(I_ε)` have `(Th′)(k) > (Th)(k)` at some
`k ∈ I_ε`. -/
theorem ex_18_4a_model_counterexample :
    ∃ ε₀ H, LocalSolution (1 / 2) (1 / 2) exU exF (Real.log 2) ε₀ H ∧
      ∀ lam, lamStar (1 / 2) (1 / 2) exU exF (Real.log 2) < lam → lam < 1 →
        ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧
          (∀ h ∈ Dlam (Real.log 2) ε lam, Top H h ∈ Dlam (Real.log 2) ε lam) ∧
          ¬ ∀ h ∈ Dlam (Real.log 2) ε lam, ∀ h' ∈ Dlam (Real.log 2) ε lam,
            (∀ k ∈ Jint (Real.log 2) ε, h' k ≤ h k) →
              ∀ k ∈ Jint (Real.log 2) ε, Top H h' k ≤ Top H h k := by
  obtain ⟨kbar, -, L⟩ := exModel_localHyp
  obtain ⟨ε₀, H, hH⟩ := exists_localSolution L
  refine ⟨ε₀, H, hH, fun lam hl hl1 => ?_⟩
  obtain ⟨ε, hε, hεε₀, hT⟩ := prop_18_2 L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨h1, h2, hle, hlt⟩ := ex_18_4a_counterexample hH hε hεε₀ hlpos hl1.le
  refine ⟨ε, hε, hεε₀, hT, fun hmono => ?_⟩
  have := hmono _ h1 _ h2 hle _ ⟨by linarith, le_rfl⟩
  linarith

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Schauder route to the local equilibrium

SLP §18.2, p. 551. The book lists three routes to a fixed point of `(Th)(k) = H[k, h²(k)]` on
`D_λ(I_ε)`; the first is Schauder's theorem (Theorem 17.4): `I_ε` is bounded, `D_λ(I_ε)` is a
nonempty, closed, bounded and convex subset of `C(I_ε)` whose members are uniformly
`λ`-Lipschitz, hence equicontinuous; Proposition 18.2 gives `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`, and
Exercise 18.3 that `T` is continuous. This module carries the argument out.

* `convex_DC`: `D_λ(I_ε)` (`DC`, as a subset of `C(I_ε)`) is convex.
* `isBounded_DC`, `totallyBounded_DC`: it is bounded, and totally bounded, by the
  Arzelà–Ascoli lemma `totallyBounded_of_equicontinuous` (a uniformly `λ`-Lipschitz family is
  equicontinuous in the sense of p. 520), transported from `I_ε →ᵇ ℝ` to `C(I_ε)` by the
  isometry `ContinuousMap.isometryEquivBoundedOfCompact`.
* `continuousOn_TC`: `T` is continuous on `D_λ(I_ε)` (Exercise 18.3, from `TC_dist_le` with
  the global Lipschitz constants of `H`).
* `localSchauder_fixedPoint_of_mapsTo`: whenever `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` (`0 ≤ λ ≤ 1`,
  `ε ≤ ε₀`), `T` has a fixed point `g ∈ D_λ(I_ε)`, which solves the Euler equation (4) on `I_ε`
  (by `schauder_closed`, Schauder's theorem for a closed convex set with relatively compact
  image).
* **Proposition 18.2 + Schauder** (`prop_18_2_schauder`, p. 551): for every `λ ∈ (λ*, 1)` and
  the `ε` of Proposition 18.2, `T` has a fixed point in `D_λ(I_ε)` solving (4) on `I_ε`.
  No contraction estimate is used, so the book's first route works with the `ε` of
  Proposition 18.2 alone (Proposition 18.3 shrinks `ε` further to get a contraction).
* `prop_18_2_schauder_eq_contraction`: for an `ε` as in Proposition 18.3 (from
  `local_constants`), `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` and every fixed point of `T` in `D_λ(I_ε)`, in
  particular the one given by Schauder's theorem, equals the contraction fixed point
  (`exists_fixedPoint_of_bounds`, `eq_of_fixed`).

The book's statement of the route is correct; Exercise 18.3 supplies its continuity hypothesis
(with the manual's estimate corrected, `Top_sub_le`). Schauder's theorem gives existence only;
uniqueness needs the contraction route.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology Metric

/-- **`D_λ(I_ε)` is convex** in `C(I_ε)` (p. 551). -/
theorem convex_DC (ks ε lam : ℝ) (hε : 0 < ε) : Convex ℝ (DC ks ε lam hε) := by
  intro h hh h' hh' a b ha hb hab
  refine ⟨?_, fun k k' => ?_⟩
  · change a * h ⟨ks, center_mem_Jint hε.le⟩ + b * h' ⟨ks, center_mem_Jint hε.le⟩ = ks
    rw [hh.1, hh'.1, ← add_mul, hab, one_mul]
  · change |(a * h k + b * h' k) - (a * h k' + b * h' k')| ≤ lam * |(k : ℝ) - k'|
    have e : (a * h k + b * h' k) - (a * h k' + b * h' k') =
        a * (h k - h k') + b * (h' k - h' k') := by ring
    rw [e]
    calc |a * (h k - h k') + b * (h' k - h' k')|
        ≤ |a * (h k - h k')| + |b * (h' k - h' k')| := abs_add_le _ _
      _ = a * |h k - h k'| + b * |h' k - h' k'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (lam * |(k : ℝ) - k'|) + b * (lam * |(k : ℝ) - k'|) := by
          have := mul_le_mul_of_nonneg_left (hh.2 k k') ha
          have := mul_le_mul_of_nonneg_left (hh'.2 k k') hb
          linarith
      _ = lam * |(k : ℝ) - k'| := by rw [← add_mul, hab, one_mul]

/-- The members of `D_λ(I_ε)` are bounded by `|k*| + λε` (for `λ ≥ 0`). -/
theorem abs_le_of_mem_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) {h : C(Jint ks ε, ℝ)}
    (hh : h ∈ DC ks ε lam hε) (k : Jint ks ε) : |h k| ≤ |ks| + lam * ε := by
  have h1 := hh.2 k ⟨ks, center_mem_Jint hε.le⟩
  rw [hh.1] at h1
  have h2 : |(k : ℝ) - ks| ≤ ε := mem_Jint_iff.1 k.2
  have h3 := mul_le_mul_of_nonneg_left h2 hl0
  calc |h k| = |(h k - ks) + ks| := by ring_nf
    _ ≤ |h k - ks| + |ks| := abs_add_le _ _
    _ ≤ |ks| + lam * ε := by linarith

/-- **`D_λ(I_ε)` is bounded** in `C(I_ε)`. -/
theorem isBounded_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) :
    Bornology.IsBounded (DC ks ε lam hε) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨|ks| + lam * ε, fun h hh => ?_⟩
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun k => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_of_mem_DC hε hl0 hh k

/-- **`D_λ(I_ε)` is totally bounded** in `C(I_ε)` (Arzelà–Ascoli): its members are uniformly
`λ`-Lipschitz, so the family is equicontinuous in the sense of p. 520, and
`totallyBounded_of_equicontinuous` applies in `I_ε →ᵇ ℝ`, isometric to `C(I_ε)`. -/
theorem totallyBounded_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) :
    TotallyBounded (DC ks ε lam hε) := by
  set e := ContinuousMap.isometryEquivBoundedOfCompact (Jint ks ε) ℝ with he
  have hX : TotallyBounded (univ : Set (Jint ks ε)) := isCompact_univ.totallyBounded
  have hbS : Bornology.IsBounded (e '' DC ks ε lam hε) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨|ks| + lam * ε, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact abs_le_of_mem_DC hε hl0 hh k
  have heq : ∀ η > 0, ∃ δ > 0, ∀ x y : Jint ks ε, dist x y < δ →
      ∀ g ∈ e '' DC ks ε lam hε, |g x - g y| < η := by
    intro η hη
    refine ⟨η / (lam + 1), div_pos hη (by linarith), fun x y hxy => ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    change |h x - h y| < η
    have hxy' : |(x : ℝ) - y| < η / (lam + 1) := by
      rwa [Subtype.dist_eq, Real.dist_eq] at hxy
    have h1 := hh.2 x y
    have h2 : lam * |(x : ℝ) - y| ≤ (lam + 1) * |(x : ℝ) - y| := by
      nlinarith [abs_nonneg ((x : ℝ) - y)]
    have h3 : (lam + 1) * |(x : ℝ) - y| < η := by
      rwa [lt_div_iff₀ (by linarith), mul_comm] at hxy'
    linarith
  have htb := totallyBounded_of_equicontinuous hX hbS heq
  have hpre := totallyBounded_preimage e.isometry.isUniformInducing htb
  refine hpre.subset fun h hh => ?_
  change e h ∈ e '' DC ks ε lam hε
  exact mem_image_of_mem e hh

/-- **Exercise 18.3 (continuity on `D_λ(I_ε)`)**, in the form needed for Schauder's theorem: the
operator `T` on `C(I_ε)` is continuous on `D_λ(I_ε)` (indeed Lipschitz there, with constant
`B₂(1 + λ)`, `B₂` a Lipschitz constant of `H` in its second argument). -/
theorem continuousOn_TC {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) : ContinuousOn (TC H hH.continuous hε) (DC ks ε lam hε) := by
  obtain ⟨B₁, B₂, -, hB₂, hB⟩ := hH.lipschitz
  have hHB : HBound H ks ε B₁ B₂ := fun x _ x' _ z _ z' _ => hB x x' z z'
  have hK0 : 0 ≤ B₂ * (1 + lam) := mul_nonneg hB₂ (by linarith)
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (B₂ * (1 + lam)))
    fun h hh h' hh' => ?_).continuousOn
  rw [Real.coe_toNNReal _ hK0]
  exact TC_dist_le hH hε hl0 hl1 hB₂ hHB hh hh'

/-- **The Schauder route** (p. 551). Let `H` be a local solution of (7) on `I_{ε₀}`,
`0 < ε ≤ ε₀`, `0 ≤ λ ≤ 1`, and suppose `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`. Then `T` has a fixed point
`g ∈ D_λ(I_ε)`, and `g` solves the Euler equation (4), `F[k, g(k), g²(k)] = 0`, on `I_ε`.
(Schauder's theorem, `schauder_closed`, on the nonempty closed convex set `D_λ(I_ε)` of the
Banach space `C(I_ε)`; `T` is continuous there (Exercise 18.3) and `T(D_λ(I_ε))` is relatively
compact because `D_λ(I_ε)` is totally bounded.) -/
theorem localSchauder_fixedPoint_of_mapsTo {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hT : ∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) :
    ∃ g ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      ∀ k ∈ Jint ks ε, Feq β θ U f k (g k) (g (g k)) = 0 := by
  have hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε) := by
    intro h hh
    rw [mem_DC_iff] at hh ⊢
    exact Dlam_congr hε.le (fun k hk => (extendC_TC H hH.continuous hε h hk).symm) (hT _ hh)
  have hcpt : IsCompact (closure (TC H hH.continuous hε '' DC ks ε lam hε)) :=
    ((totallyBounded_DC hε hl0).subset (image_subset_iff.2 hmaps)).closure.isCompact_of_isClosed
      isClosed_closure
  obtain ⟨g0, hg0, hfix⟩ := schauder_closed (isClosed_DC ks ε lam hε) (convex_DC ks ε lam hε)
    ⟨_, const_mem_DC hε hl0⟩ (continuousOn_TC hH hε hl0 hl1) hmaps hcpt
  have hg := (mem_DC_iff hε _).1 hg0
  have hfix' : ∀ k ∈ Jint ks ε, Top H (extendC hε g0) k = extendC hε g0 k := fun k hk => by
    rw [← extendC_TC H hH.continuous hε g0 hk, hfix]
  refine ⟨extendC hε g0, hg, hfix', fun k hk => ?_⟩
  have hgm := Dlam_mapsTo hg hl1
  have h7 := hH.eq7 k (Jint_mono hεε₀ hk) _ (Jint_mono hεε₀ (hgm _ (hgm k hk)))
  have e : H k (extendC hε g0 (extendC hε g0 k)) = extendC hε g0 k := hfix' k hk
  rwa [e] at h7

/-- **Proposition 18.2 with Schauder's theorem** (p. 551, the first of the book's three routes).
Under `LocalHyp` and with `H` the local solution of (7) on `I_{ε₀}`: for every `λ ∈ (λ*, 1)`
there is `ε ∈ (0, ε₀]` (the one of Proposition 18.2) such that `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` and `T`
has a fixed point `g ∈ D_λ(I_ε)`, which solves the Euler equation (4) on `I_ε`. -/
theorem prop_18_2_schauder {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ (∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) ∧
      ∃ g ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
        ∀ k ∈ Jint ks ε, Feq β θ U f k (g k) (g (g k)) = 0 := by
  obtain ⟨ε, hε, hεε₀, hT⟩ := prop_18_2 L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  exact ⟨ε, hε, hεε₀, hT, localSchauder_fixedPoint_of_mapsTo hH hε hεε₀ hlpos.le hl1.le hT⟩

/-- **The two routes agree.** For every `λ ∈ (λ*, 1)` there are `ε ∈ (0, ε₀]` and `g ∈ D_λ(I_ε)`
such that `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`, `g` is the fixed point given by the Contraction Mapping
Theorem (Proposition 18.3), and every fixed point of `T` in `D_λ(I_ε)` (in particular the one
given by Schauder's theorem, `localSchauder_fixedPoint_of_mapsTo`) equals `g` on `I_ε`. -/
theorem prop_18_2_schauder_eq_contraction {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ (∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) ∧
      ∃ g ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
        ∀ g' ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g' k = g' k) →
          ∀ k ∈ Jint ks ε, g' k = g k := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨g, hg, hfix, -⟩ :=
    exists_fixedPoint_of_bounds hH hε hεε₀ hlpos.le hl1.le hm₂ hsum hK hB
  refine ⟨ε, hε, hεε₀, fun h hh => Top_mem_Dlam hB hm₂ hlpos.le hl1.le hsum hH.center hh, g,
    hg, hfix, fun g' hg' hfix' k hk => ?_⟩
  exact eq_of_fixed hB hm₂ hlpos.le hK (Dlam_mapsTo hg' hl1.le) (Dlam_mapsTo hg hl1.le) hg.2
    hfix' hfix k hk

end StokeyLucasPrescott.EquilibriaWithDistortions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Smoothness of `H` and the slope of the local equilibrium at `k*`

SLP §18.2, pp. 549 and 553.

**The implicit function `H` is `C¹`** (p. 549). Mathlib's implicit function theorem for a curried
bivariate function (`implicitFunctionOfBivariate`) is applied to `((x, z), y) ↦ F(x, y, z)` at
any point `((x₀, z₀), H(x₀, z₀))` where `F₂ ≠ 0` (`bivImplicit`). The resulting implicit
function agrees with the `H` of `LocalSolution` near `(x₀, z₀)` (`eventuallyEq_bivImplicit`),
so `H` is strictly differentiable there with derivative
`(a, b) ↦ −(F₁ a + F₃ b)/F₂` (`Hderiv`, `LocalSolution.hasStrictFDerivAt`). In particular
(`LocalSolution.hasStrictFDerivAt_center`, `hasDerivAt_H_left`, `hasDerivAt_H_right`)
`H₁(k*, k*) = −F₁*/F₂*` and `H₂(k*, k*) = −F₃*/F₂*` are genuine partial derivatives, and `H` is
`C¹` on a neighbourhood of `(k*, k*)` (`LocalSolution.contDiffAt`, `eventually_contDiffAt`).

**The slope of the equilibrium at `k*`** (derived remark after Proposition 18.3, p. 553). If
`g ∈ D_λ(I_ε)` is a strictly increasing fixed point of `T` (as given by `prop_18_3_fixedPoint`),
then `g` is differentiable at `k*` with `g′(k*) = λ*`, the stable root of the characteristic
polynomial (`hasDerivAt_fixedPoint_lamStar`, `prop_18_3_deriv`). Differentiability is not
assumed: writing `s(k) = (g(k) − k*)/(k − k*)` and `e = s − λ*`, the identity
`g(k) = H(k, g(g(k)))`, the derivative of `H` at `(k*, k*)` and `λ* = H₁* + H₂* λ*²` give
`|e(k)| ≤ c |e(g(k))| + τ'` near `k*` with `c = H₂*λ*/(1 − H₂*λ) < 1` and `τ'` arbitrarily
small, and iterating the bound squeezes `e` to `0`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-! ### Continuity of the partial derivatives of `F` -/

/-- `F₁` is continuous. -/
theorem continuous_F1f {θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun p : ℝ × ℝ => F1f θ U f p.1 p.2 := by
  have := continuous_deriv2_of_C2 hU
  have := (differentiable_of_C2 hf).continuous
  have := continuous_deriv_of_C2 hf
  have := continuous_deriv2_of_C2 hf
  simp only [F1f, psi, dpsi]
  fun_prop

/-- `F₂` is continuous. -/
theorem continuous_F2f {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun p : ℝ × ℝ × ℝ => F2f β θ U f p.1 p.2.1 p.2.2 := by
  have := continuous_deriv_of_C2 hU
  have := continuous_deriv2_of_C2 hU
  have := (differentiable_of_C2 hf).continuous
  have := continuous_deriv_of_C2 hf
  have := continuous_deriv2_of_C2 hf
  simp only [F2f, psi, dpsi]
  fun_prop

/-- `F₃` is continuous. -/
theorem continuous_F3f {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun p : ℝ × ℝ => F3f β θ U f p.1 p.2 := by
  have := continuous_deriv2_of_C2 hU
  have := (differentiable_of_C2 hf).continuous
  have := continuous_deriv_of_C2 hf
  simp only [F3f, psi]
  fun_prop

/-! ### The bivariate set-up `((x, z), y) ↦ F(x, y, z)` -/

/-- The partial derivative of `F` with respect to `(x, z)`:
`(a, b) ↦ F₁(x, y) a + F₃(y, z) b`. -/
noncomputable def Fxz (β θ : ℝ) (U f : ℝ → ℝ) (w : ℝ × ℝ) (y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  F1f θ U f w.1 y • ContinuousLinearMap.fst ℝ ℝ ℝ +
    F3f β θ U f y w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The partial derivative of `F` with respect to `y`, as a linear map: `b ↦ F₂ b`. -/
noncomputable def Fyy (β θ : ℝ) (U f : ℝ → ℝ) (w : ℝ × ℝ) (y : ℝ) : ℝ →L[ℝ] ℝ :=
  F2f β θ U f w.1 y w.2 • ContinuousLinearMap.id ℝ ℝ

/-- `∂F/∂(x, z) = Fxz`. -/
theorem hasFDerivAt_Feq_xz {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (v : (ℝ × ℝ) × ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => Feq β θ U f w.1 v.2 w.2) (Fxz β θ U f v.1 v.2) v.1 := by
  obtain ⟨⟨x0, z0⟩, y⟩ := v
  have h1 := (hasDerivAt_Feq_x (β := β) (θ := θ) hU hf x0 y z0).comp_hasFDerivAt (x0, z0)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((x0, z0) : ℝ × ℝ)))
  have h3 := (hasDerivAt_Feq_z (β := β) (θ := θ) (f := f) hU x0 y z0).comp_hasFDerivAt (x0, z0)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((x0, z0) : ℝ × ℝ)))
  have e : (fun w : ℝ × ℝ => Feq β θ U f w.1 y w.2) = fun w =>
      ((fun x => Feq β θ U f x y z0) ∘ Prod.fst) w +
        (((fun z => Feq β θ U f x0 y z) ∘ Prod.snd) w - Feq β θ U f x0 y z0) := by
    funext w
    simp only [Function.comp, Feq]
    ring
  rw [e]
  exact h1.add (h3.sub_const _)

/-- `∂F/∂y = Fyy`. -/
theorem hasFDerivAt_Feq_yy {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (v : (ℝ × ℝ) × ℝ) :
    HasFDerivAt (fun y => Feq β θ U f v.1.1 y v.1.2) (Fyy β θ U f v.1 v.2) v.2 := by
  refine (hasDerivAt_Feq_y (β := β) (θ := θ) hU hf v.1.1 v.2 v.1.2).hasFDerivAt.congr_fderiv ?_
  ext
  simp [Fyy]

/-- `Fxz` is continuous in `((x, z), y)`. -/
theorem continuous_Fxz {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun v : (ℝ × ℝ) × ℝ => Fxz β θ U f v.1 v.2 := by
  have c1 := continuous_F1f (θ := θ) hU hf
  have c3 := continuous_F3f (β := β) (θ := θ) hU hf
  refine ((c1.comp (continuous_fst.fst.prodMk continuous_snd)).smul continuous_const).add
    ((c3.comp (continuous_snd.prodMk continuous_fst.snd)).smul continuous_const)

/-- `Fyy` is continuous in `((x, z), y)`. -/
theorem continuous_Fyy {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f) :
    Continuous fun v : (ℝ × ℝ) × ℝ => Fyy β θ U f v.1 v.2 :=
  ((continuous_F2f (β := β) (θ := θ) hU hf).comp
    (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))).smul continuous_const

/-- The equivalence `b ↦ c b` of `ℝ` for `c ≠ 0`. -/
noncomputable def mulEquiv' (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)

/-- `Fyy` is the linear map `b ↦ F₂ b`, invertible when `F₂ ≠ 0`. -/
theorem Fyy_eq_mulEquiv' {β θ : ℝ} {U f : ℝ → ℝ} (w : ℝ × ℝ) (y : ℝ)
    (hc : F2f β θ U f w.1 y w.2 ≠ 0) :
    Fyy β θ U f w y = (mulEquiv' _ hc : ℝ →L[ℝ] ℝ) := by
  ext
  simp [Fyy, mulEquiv', ContinuousLinearEquiv.unitsEquivAut_apply]

/-- `Fyy` is invertible when `F₂ ≠ 0`. -/
theorem Fyy_isInvertible {β θ : ℝ} {U f : ℝ → ℝ} {w : ℝ × ℝ} {y : ℝ}
    (hc : F2f β θ U f w.1 y w.2 ≠ 0) : (Fyy β θ U f w y).IsInvertible :=
  ⟨mulEquiv' _ hc, (Fyy_eq_mulEquiv' w y hc).symm⟩

/-- **Mathlib's implicit function** for `F(x, y, z) = F(x₀, y₀, z₀)` near `((x₀, z₀), y₀)`,
solving for `y` as a function of `(x, z)`, when `F₂(x₀, y₀, z₀) ≠ 0`. -/
noncomputable def bivImplicit {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 2 f) (u : (ℝ × ℝ) × ℝ) (hc : F2f β θ U f u.1.1 u.2 u.1.2 ≠ 0) :
    ℝ × ℝ → ℝ :=
  implicitFunctionOfBivariate (f := fun w y => Feq β θ U f w.1 y w.2) (u := u)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_xz hU hf v)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_yy hU hf v)
    (continuous_Fxz hU hf).continuousAt (continuous_Fyy hU hf).continuousAt
    (Fyy_isInvertible hc)

/-- The derivative of `H`: `(a, b) ↦ −(F₁ a + F₃ b)/F₂` at `(x, H(x, z), z)`. -/
noncomputable def Hderiv (β θ : ℝ) (U f : ℝ → ℝ) (w : ℝ × ℝ) (y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (-F1f θ U f w.1 y / F2f β θ U f w.1 y w.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (-F3f β θ U f y w.2 / F2f β θ U f w.1 y w.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- **Implicit function theorem** (Mathlib) for `F`: `bivImplicit` is strictly differentiable at
`(x₀, z₀)` with derivative `Hderiv`, and near `((x₀, z₀), y₀)` the equation
`F(x, y, z) = F(x₀, y₀, z₀)` holds iff `y = bivImplicit (x, z)`. -/
theorem bivImplicit_spec {β θ : ℝ} {U f : ℝ → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (u : (ℝ × ℝ) × ℝ) (hc : F2f β θ U f u.1.1 u.2 u.1.2 ≠ 0) :
    HasStrictFDerivAt (bivImplicit hU hf u hc) (Hderiv β θ U f u.1 u.2) u.1 ∧
      ∀ᶠ v in 𝓝 u, (Feq β θ U f v.1.1 v.2 v.1.2 = Feq β θ U f u.1.1 u.2 u.1.2 ↔
        bivImplicit hU hf u hc v.1 = v.2) := by
  refine ⟨?_, eventually_apply_eq_iff_implicitFunctionOfBivariate
    (f := fun w y => Feq β θ U f w.1 y w.2) (u := u)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_xz hU hf v)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_yy hU hf v)
    (continuous_Fxz hU hf).continuousAt (continuous_Fyy hU hf).continuousAt
    (Fyy_isInvertible hc)⟩
  have h := hasStrictFDerivAt_implicitFunctionOfBivariate
    (f := fun w y => Feq β θ U f w.1 y w.2) (u := u)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_xz hU hf v)
    (Eventually.of_forall fun v => hasFDerivAt_Feq_yy hU hf v)
    (continuous_Fxz hU hf).continuousAt (continuous_Fyy hU hf).continuousAt
    (Fyy_isInvertible hc)
  refine h.congr_fderiv ?_
  rw [Fyy_eq_mulEquiv' u.1 u.2 hc, ContinuousLinearMap.inverse_equiv]
  ext
  · simp [Hderiv, Fxz, mulEquiv', ContinuousLinearEquiv.unitsEquivAut_apply_symm]
    ring
  · simp [Hderiv, Fxz, mulEquiv', ContinuousLinearEquiv.unitsEquivAut_apply_symm]
    ring

/-! ### `H` is `C¹` near `(k*, k*)` -/

/-- **`H` agrees with Mathlib's implicit function.** If `(x₀, z₀)` lies in the open square
`(k* − ε₀, k* + ε₀)²` and `F₂(x₀, H(x₀, z₀), z₀) ≠ 0`, then `H = bivImplicit` near `(x₀, z₀)`. -/
theorem eventuallyEq_bivImplicit {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {x₀ z₀ : ℝ}
    (hx : |x₀ - ks| < ε₀) (hz : |z₀ - ks| < ε₀)
    (hc : F2f β θ U f x₀ (H x₀ z₀) z₀ ≠ 0) :
    (fun q : ℝ × ℝ => H q.1 q.2) =ᶠ[𝓝 (x₀, z₀)]
      bivImplicit L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc := by
  obtain ⟨-, hiff⟩ := bivImplicit_spec L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc
  have hHc : Continuous fun q : ℝ × ℝ => ((q.1, q.2), H q.1 q.2) :=
    (continuous_fst.prodMk continuous_snd).prodMk hH.continuous
  have h1 : ∀ᶠ q in 𝓝 ((x₀, z₀) : ℝ × ℝ), (Feq β θ U f q.1 (H q.1 q.2) q.2 =
      Feq β θ U f x₀ (H x₀ z₀) z₀ ↔ bivImplicit L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc
        (q.1, q.2) = H q.1 q.2) :=
    have ht : Tendsto (fun q : ℝ × ℝ => ((q.1, q.2), H q.1 q.2)) (𝓝 (x₀, z₀))
        (𝓝 ((x₀, z₀), H x₀ z₀)) := hHc.tendsto (x₀, z₀)
    ht.eventually hiff
  have hbox : ∀ᶠ q in 𝓝 ((x₀, z₀) : ℝ × ℝ), |q.1 - ks| < ε₀ ∧ |q.2 - ks| < ε₀ := by
    have c1 : Continuous fun q : ℝ × ℝ => |q.1 - ks| := by fun_prop
    have c2 : Continuous fun q : ℝ × ℝ => |q.2 - ks| := by fun_prop
    exact (c1.continuousAt.eventually (gt_mem_nhds hx)).and
      (c2.continuousAt.eventually (gt_mem_nhds hz))
  have hx₀ : x₀ ∈ Jint ks ε₀ := mem_Jint_iff.2 hx.le
  have hz₀ : z₀ ∈ Jint ks ε₀ := mem_Jint_iff.2 hz.le
  filter_upwards [h1, hbox] with q hq hb
  have e1 := hH.eq7 q.1 (mem_Jint_iff.2 hb.1.le) q.2 (mem_Jint_iff.2 hb.2.le)
  have e0 := hH.eq7 x₀ hx₀ z₀ hz₀
  exact (hq.1 (by rw [e1, e0])).symm

/-- **`H` is strictly differentiable** at every `(x₀, z₀)` of the open square
`(k* − ε₀, k* + ε₀)²` with `F₂(x₀, H(x₀, z₀), z₀) ≠ 0`, with derivative
`(a, b) ↦ −(F₁ a + F₃ b)/F₂` (`Hderiv`). -/
theorem LocalSolution.hasStrictFDerivAt {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {x₀ z₀ : ℝ}
    (hx : |x₀ - ks| < ε₀) (hz : |z₀ - ks| < ε₀)
    (hc : F2f β θ U f x₀ (H x₀ z₀) z₀ ≠ 0) :
    HasStrictFDerivAt (fun q : ℝ × ℝ => H q.1 q.2) (Hderiv β θ U f (x₀, z₀) (H x₀ z₀))
      (x₀, z₀) :=
  ((bivImplicit_spec L.U_contDiff L.f_contDiff ((x₀, z₀), H x₀ z₀) hc).1).congr_of_eventuallyEq
    (eventuallyEq_bivImplicit L hH hx hz hc).symm

/-- At the steady state, `Hderiv` is `(a, b) ↦ H₁* a + H₂* b` with `H₁* = −F₁*/F₂*`,
`H₂* = −F₃*/F₂*`. -/
theorem Hderiv_center {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    Hderiv β θ U f (ks, ks) ks =
      (-F1s β θ U f ks / F2s β θ U f ks) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-F3s U θ f ks / F2s β θ U f ks) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp only [Hderiv, F1f_star L.beta_pos L.euler, F2f_star L.beta_pos L.euler,
    F3f_star L.euler]

/-- **`H` at the steady state** (p. 549): `H` is strictly differentiable at `(k*, k*)` with
derivative `(a, b) ↦ H₁* a + H₂* b`, `H₁* = −F₁*/F₂*`, `H₂* = −F₃*/F₂*`; and `H` coincides
near `(k*, k*)` with Mathlib's implicit function. -/
theorem LocalSolution.hasStrictFDerivAt_center {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ}
    {H : ℝ → ℝ → ℝ} (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    HasStrictFDerivAt (fun q : ℝ × ℝ => H q.1 q.2)
      ((-F1s β θ U f ks / F2s β θ U f ks) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-F3s U θ f ks / F2s β θ U f ks) • ContinuousLinearMap.snd ℝ ℝ ℝ) (ks, ks) := by
  have hc : F2f β θ U f ks (H ks ks) ks ≠ 0 := by
    rw [hH.center, F2f_star L.beta_pos L.euler]
    exact L.F2s_pos.ne'
  have h := hH.hasStrictFDerivAt L (x₀ := ks) (z₀ := ks) (by simpa using hH.eps_pos)
    (by simpa using hH.eps_pos) hc
  rw [hH.center, Hderiv_center L] at h
  exact h

/-- **`H₁(k*, k*) = −F₁*/F₂*`** as a genuine partial derivative. -/
theorem hasDerivAt_H_left {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    HasDerivAt (fun x => H x ks) (-F1s β θ U f ks / F2s β θ U f ks) ks := by
  have hg : HasFDerivAt (fun x : ℝ => ((x, ks) : ℝ × ℝ))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) ks :=
    (hasFDerivAt_id ks).prodMk (hasFDerivAt_const ks ks)
  have h := HasFDerivAt.comp (f := fun x : ℝ => ((x, ks) : ℝ × ℝ)) ks
    (hH.hasStrictFDerivAt_center L).hasFDerivAt hg
  exact h.hasDerivAt.congr_deriv (by simp)

/-- **`H₂(k*, k*) = −F₃*/F₂*`** as a genuine partial derivative. -/
theorem hasDerivAt_H_right {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    HasDerivAt (fun z => H ks z) (-F3s U θ f ks / F2s β θ U f ks) ks := by
  have hg : HasFDerivAt (fun z : ℝ => ((ks, z) : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) ks :=
    (hasFDerivAt_const ks ks).prodMk (hasFDerivAt_id ks)
  have h := (hH.hasStrictFDerivAt_center L).hasFDerivAt.comp ks hg
  exact h.hasDerivAt.congr_deriv (by simp)

/-- **`H` is `C¹` at `(k*, k*)`** (the book's "`C¹` function `H`", p. 549), with derivative
`Hderiv` on a neighbourhood. -/
theorem LocalSolution.contDiffAt {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => H q.1 q.2) (ks, ks) := by
  have cF2 := continuous_F2f (β := β) (θ := θ) L.U_contDiff L.f_contDiff
  have cG : Continuous fun q : ℝ × ℝ => F2f β θ U f q.1 (H q.1 q.2) q.2 :=
    cF2.comp (continuous_fst.prodMk (hH.continuous.prodMk continuous_snd))
  have hc0 : F2f β θ U f ks (H ks ks) ks ≠ 0 := by
    rw [hH.center, F2f_star L.beta_pos L.euler]
    exact L.F2s_pos.ne'
  set u : Set (ℝ × ℝ) := {q | |q.1 - ks| < ε₀ ∧ |q.2 - ks| < ε₀ ∧
    F2f β θ U f q.1 (H q.1 q.2) q.2 ≠ 0} with hu
  have huo : IsOpen u := by
    refine (isOpen_lt (f := fun q : ℝ × ℝ => |q.1 - ks|) (by fun_prop) continuous_const).inter
      ((isOpen_lt (f := fun q : ℝ × ℝ => |q.2 - ks|) (by fun_prop) continuous_const).inter
        (isOpen_ne_fun cG continuous_const))
  have hku : ((ks, ks) : ℝ × ℝ) ∈ u := ⟨by simpa using hH.eps_pos, by simpa using hH.eps_pos, hc0⟩
  refine contDiffAt_one_iff.2 ⟨fun q => Hderiv β θ U f q (H q.1 q.2), u, huo.mem_nhds hku,
    ?_, fun q hq => (hH.hasStrictFDerivAt L hq.1 hq.2.1 hq.2.2).hasFDerivAt⟩
  have c1 : Continuous fun q : ℝ × ℝ => F1f θ U f q.1 (H q.1 q.2) :=
    (continuous_F1f L.U_contDiff L.f_contDiff).comp (continuous_fst.prodMk hH.continuous)
  have c3 : Continuous fun q : ℝ × ℝ => F3f β θ U f (H q.1 q.2) q.2 :=
    (continuous_F3f L.U_contDiff L.f_contDiff).comp (hH.continuous.prodMk continuous_snd)
  refine (((c1.continuousOn.neg.div cG.continuousOn fun q hq => hq.2.2).smul
    continuousOn_const).add ((c3.continuousOn.neg.div cG.continuousOn fun q hq => hq.2.2).smul
    continuousOn_const))

/-- `H` is `C¹` on a neighbourhood of `(k*, k*)`. -/
theorem LocalSolution.eventually_contDiffAt {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) :
    ∀ᶠ q in 𝓝 ((ks, ks) : ℝ × ℝ), ContDiffAt ℝ 1 (fun q : ℝ × ℝ => H q.1 q.2) q :=
  (hH.contDiffAt L).eventually (by simp)

/-! ### The slope of the equilibrium at `k*` -/

/-- `λ*` solves `λ = H₁* + H₂* λ²` (equivalently `P(λ*) = 0`). -/
theorem LocalHyp.lamStar_eq {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    lamStar β θ U f ks = -F1s β θ U f ks / F2s β θ U f ks +
      -F3s U θ f ks / F2s β θ U f ks * lamStar β θ U f ks ^ 2 := by
  obtain ⟨-, hfac, -⟩ := L.charPoly_roots
  have h0 : charPoly β θ U f ks (lamStar β θ U f ks) = 0 := by rw [hfac]; ring
  simp only [charPoly] at h0
  have hF2 := L.F2s_pos.ne'
  field_simp
  linarith

/-- **The slope of the local equilibrium at `k*` is `λ*`** (derived remark, p. 553). Let
`λ ∈ (λ*, 1)`, `0 < ε ≤ ε₀`, and let `g ∈ D_λ(I_ε)` be strictly increasing on `I_ε` with
`g(k) = H(k, g(g(k)))` on `I_ε`. Then `g` is differentiable at `k*` and `g′(k*) = λ*`, the root of
`P` in `(0, 1)`. No differentiability of `g` is assumed. -/
theorem hasDerivAt_fixedPoint_lamStar {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε)
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) {g : ℝ → ℝ} (hg : g ∈ Dlam ks ε lam)
    (hfix : ∀ k ∈ Jint ks ε, Top H g k = g k) (hsm : StrictMonoOn g (Jint ks ε)) :
    HasDerivAt g (lamStar β θ U f ks) ks := by
  set ls := lamStar β θ U f ks with hls
  set H1 := -F1s β θ U f ks / F2s β θ U f ks with hH1
  set H2 := -F3s U θ f ks / F2s β θ U f ks with hH2
  obtain ⟨-, -, hls0, hls1, -⟩ := L.charPoly_roots
  have hH2p : 0 < H2 := L.H2s_pos
  have hlpos : 0 < lam := hls0.trans hl
  have hK : H2 * (1 + lam) < 1 := L.H2s_mul_lt_one hl1.le
  have hden : 0 < 1 - H2 * lam := by nlinarith
  have hroot : ls = H1 + H2 * ls ^ 2 := L.lamStar_eq
  set c := H2 * ls / (1 - H2 * lam) with hc
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hden.le
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hden]
    nlinarith
  have hksJ : ks ∈ Jint ks ε := center_mem_Jint hε.le
  have hmaps := Dlam_mapsTo hg hl1.le
  have hgks : g ks = ks := hg.1
  have hgne : ∀ k ∈ Jint ks ε, k ≠ ks → g k ≠ ks := fun k hk hne h =>
    hne (hsm.injOn hk hksJ (h.trans hgks.symm))
  set s : ℝ → ℝ := fun k => (g k - ks) / (k - ks) with hs
  have hsk : ∀ k, k ≠ ks → g k - ks = s k * (k - ks) := fun k hk => by
    simp only [hs]
    field_simp [sub_ne_zero.2 hk]
  have hspos : ∀ k ∈ Jint ks ε, k ≠ ks → 0 < s k := by
    intro k hk hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hsm hk hksJ h
      rw [hgks] at this
      exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · have := hsm hksJ hk h
      rw [hgks] at this
      exact div_pos (by linarith) (by linarith)
  have hsle : ∀ k ∈ Jint ks ε, k ≠ ks → s k ≤ lam := by
    intro k hk hne
    have h1 := hg.2 k hk ks hksJ
    rw [hgks, hsk k hne, abs_mul] at h1
    have hd : 0 < |k - ks| := abs_pos.2 (sub_ne_zero.2 hne)
    have := le_of_mul_le_mul_right h1 hd
    exact (le_abs_self _).trans this
  -- the derivative of `H` at `(k*, k*)`
  have hD := (hH.hasStrictFDerivAt_center L).hasFDerivAt
  -- the key estimate, for a given `τ > 0`
  have key : ∀ τ > 0, ∃ δ > 0, ∀ k ∈ Jint ks ε, k ≠ ks → |k - ks| < δ →
      |s k - ls| ≤ c * |s (g k) - ls| + τ / (1 - H2 * lam) := by
    intro τ hτ
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hD.isLittleO.def hτ)
    refine ⟨δ, hδ, fun k hk hne hkd => ?_⟩
    have hgk := hmaps k hk
    have hggk := hmaps _ hgk
    have hgkne := hgne k hk hne
    have hd : 0 < |k - ks| := abs_pos.2 (sub_ne_zero.2 hne)
    have hlip1 : |g k - ks| ≤ |k - ks| := by
      have := hg.2 k hk ks hksJ
      rw [hgks] at this
      nlinarith [abs_nonneg (k - ks)]
    have hlip2 : |g (g k) - ks| ≤ |k - ks| := by
      have := hg.2 _ hgk ks hksJ
      rw [hgks] at this
      nlinarith [abs_nonneg (g k - ks)]
    have hq : dist ((k, g (g k)) : ℝ × ℝ) (ks, ks) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt hkd (lt_of_le_of_lt hlip2 hkd)
    have hb := hball hq
    have hn : ‖((k, g (g k)) : ℝ × ℝ) - (ks, ks)‖ ≤ |k - ks| := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
      exact max_le le_rfl hlip2
    have hval : H (k, g (g k)).1 (k, g (g k)).2 = g k := hfix k hk
    simp only [hval, hH.center, Real.norm_eq_abs] at hb
    have hlin : ((-F1s β θ U f ks / F2s β θ U f ks) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-F3s U θ f ks / F2s β θ U f ks) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (((k, g (g k)) : ℝ × ℝ) - (ks, ks)) = H1 * (k - ks) + H2 * (g (g k) - ks) := by
      simp [hH1, hH2]
    rw [hlin] at hb
    have hb2 : |g k - ks - (H1 * (k - ks) + H2 * (g (g k) - ks))| ≤ τ * |k - ks| :=
      hb.trans (mul_le_mul_of_nonneg_left hn hτ.le)
    -- express in terms of slopes
    have e1 := hsk k hne
    have e2 : g (g k) - ks = s (g k) * (s k * (k - ks)) := by
      rw [hsk (g k) hgkne, e1]
    rw [e1, e2] at hb2
    have e3 : s k * (k - ks) - (H1 * (k - ks) + H2 * (s (g k) * (s k * (k - ks)))) =
        (s k - H1 - H2 * s (g k) * s k) * (k - ks) := by ring
    rw [e3, abs_mul] at hb2
    have hb3 : |s k - H1 - H2 * s (g k) * s k| ≤ τ := le_of_mul_le_mul_right hb2 hd
    have e4 : (1 - H2 * s (g k)) * (s k - ls) =
        (s k - H1 - H2 * s (g k) * s k) + H2 * ls * (s (g k) - ls) := by
      linear_combination (-1 : ℝ) * hroot
    have hs' := hsle _ hgk hgkne
    have hs'p := hspos _ hgk hgkne
    have h5 : 0 < 1 - H2 * s (g k) := by nlinarith
    have h6 : (1 - H2 * lam) * |s k - ls| ≤ (1 - H2 * s (g k)) * |s k - ls| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    have h7 : (1 - H2 * s (g k)) * |s k - ls| ≤ τ + H2 * ls * |s (g k) - ls| := by
      have e5 : |(1 - H2 * s (g k)) * (s k - ls)| = (1 - H2 * s (g k)) * |s k - ls| := by
        rw [abs_mul, abs_of_pos h5]
      rw [← e5, e4]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (by positivity : 0 < H2 * ls)]
      linarith
    rw [hc, show H2 * ls / (1 - H2 * lam) * |s (g k) - ls| + τ / (1 - H2 * lam) =
      (H2 * ls * |s (g k) - ls| + τ) / (1 - H2 * lam) by ring, le_div_iff₀ hden]
    linarith
  -- squeeze
  have hsmall : ∀ η > 0, ∃ δ > 0, ∀ k ∈ Jint ks ε, k ≠ ks → |k - ks| < δ → |s k - ls| ≤ η := by
    intro η hη
    set τ := η * (1 - H2 * lam) * (1 - c) with hτ
    have hτp : 0 < τ := by
      have : 0 < 1 - c := by linarith
      positivity
    obtain ⟨δ, hδ, hkey⟩ := key τ hτp
    set δ' := min δ ε with hδ'
    have hδ'p : 0 < δ' := lt_min hδ hε
    refine ⟨δ', hδ'p, fun k hk hne hkd => ?_⟩
    have hτ' : τ / (1 - H2 * lam) = η * (1 - c) := by
      rw [hτ]
      field_simp
    have hbound : ∀ n : ℕ, ∀ k ∈ Jint ks ε, k ≠ ks → |k - ks| < δ' →
        |s k - ls| ≤ c ^ n * 2 + η := by
      intro n
      induction n with
      | zero =>
        intro k hk hne _
        have h1 := hspos k hk hne
        have h2 := hsle k hk hne
        rw [pow_zero, one_mul, abs_le]
        constructor <;> linarith
      | succ n ih =>
        intro k hk hne hkd
        have hgk := hmaps k hk
        have hgkne := hgne k hk hne
        have hlip : |g k - ks| < δ' := by
          have := hg.2 k hk ks hksJ
          rw [hgks] at this
          nlinarith [abs_nonneg (k - ks)]
        have h1 := hkey k hk hne (lt_of_lt_of_le hkd (min_le_left _ _))
        have h2 := ih (g k) hgk hgkne hlip
        rw [hτ'] at h1
        have h3 := mul_le_mul_of_nonneg_left h2 hc0
        rw [pow_succ]
        nlinarith
    have hlim : Tendsto (fun n : ℕ => c ^ n * 2 + η) atTop (𝓝 η) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const 2).add_const η
    exact ge_of_tendsto' hlim fun n => hbound n k hk hne hkd
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ, hδ, hsm'⟩ := hsmall (η / 2) (by linarith)
  refine ⟨min δ ε, lt_min hδ hε, fun {k} hk hkd => ?_⟩
  have hne : k ≠ ks := hk
  rw [Real.dist_eq] at hkd ⊢
  have hkJ : k ∈ Jint ks ε := mem_Jint_iff.2 (lt_of_lt_of_le hkd (min_le_right _ _)).le
  have h := hsm' k hkJ hne (lt_of_lt_of_le hkd (min_le_left _ _))
  have e : slope g ks k = s k := by
    rw [slope_def_field, hgks]
  rw [e]
  linarith

/-- **Proposition 18.3 with the slope** (p. 553): for every `λ ∈ (λ*, 1)` the unique fixed point
`g ∈ D_λ(I_ε)` of Proposition 18.3 is differentiable at `k*` with `g′(k*) = λ*`. -/
theorem prop_18_3_deriv {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∃ g : ℝ → ℝ, g ∈ Dlam ks ε lam ∧
      (∀ k ∈ Jint ks ε, Top H g k = g k) ∧ HasDerivAt g (lamStar β θ U f ks) ks := by
  obtain ⟨ε, hε, hεε₀, g, hg, hfix, -, -, hsm, -⟩ := prop_18_3_fixedPoint L hH hl hl1
  exact ⟨ε, hε, hεε₀, g, hg, hfix, hasDerivAt_fixedPoint_lamStar L hH hε hl hl1 hg hfix hsm⟩

end StokeyLucasPrescott.EquilibriaWithDistortions

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_polynomial_det_id_add_smul
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.integral_eq_of_polynomial_of_eq_on_Ioc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.isUnit_id_add_smul
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.no_C1_retraction
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.C1Restrictions
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_C1_approx_real
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_C1_approx
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.brouwer_closedBall
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.brouwer_ball
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_lipschitz_retraction
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.brouwer_inner
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.brouwer
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.brouwer_subtype
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.theorem_17_3
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsMarginalUtility
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsMarginalUtility.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsMarginalUtility.pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsMarginalUtility.strictAnti
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsMarginalUtility.cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsMarginalUtility.inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsEulerRHS
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsEulerRHS.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsEulerRHS.zero_anti
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsEulerRHS.anti
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsEulerRHS.cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IsEulerRHS.blowup
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.EulerBelow
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerSet
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerBelow_of_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bddAbove_eulerSet
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.le_eulerCross_of_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.mem_eulerSet_of_lt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_le_of_not_below
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.le_eulerCross_of_forall
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_le_add_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_mono_rhs
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_eq_zero_of_not_below
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_spec_KT
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_mono'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_mono_rhs'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.abs_eulerCross_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eulerCross_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.RHSConvergesAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eventually_abs_eulerCross_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.assumption_18_2_contradiction
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.β
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.θ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.β_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.β_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U_cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U_contDiff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U_strictMono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U_strictConcave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U_deriv
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.θ_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.θ_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f_cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f_contDiff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f_strictMono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f_strictConcave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f_deriv
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f_zero_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kbar_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_gt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_lt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_contAt_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U'_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.deriv_f_eq
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.deriv_U_eq
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_strictAntiOn_Ioi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_continuousOn_Ioi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_strictAntiOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U'_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U'_strictAntiOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.U'_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isMarginalUtility
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.f'_mul_lt_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.mul_f'_lt_f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_sub_gt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_strictMonoOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.lt_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_kbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.psi_le_kbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.one_sub_mul_f'_kbar_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.euler_kbar_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.one_lt_euler_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.exists_kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kstar_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kstar_lt_kbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.euler_kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kstar_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.one_lt_euler
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.euler_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.kstar_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.sub_lt_psi_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.lt_psi_of_le_kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.le_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.mono_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.ge_self
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.at_kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.le_self
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ext
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ext_apply
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.F
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.toBCF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.toBCF_apply
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ext_toBCF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.congr
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.toBCF_mem_F
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.abs_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.le_kbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.mem_Icc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.convex_comb
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.low
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isInF_low
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.low_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.bnd
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.le_bnd
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.bnd_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.bnd_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.runSup
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.le_runSup
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.runSup_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.runSup_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.runSup_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.gap
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.gap_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.up
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.le_up
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.up_le_bnd
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isInF_up
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.up_eq_of_le_kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.up_eq_of_kstar_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.hbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.exists_gap_gt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.not_isInF_hbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.hbar_not_mem_F
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.F_nonempty
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.norm_le_of_mem_F
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.F_isBounded
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.F_convex
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.F_isClosed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.prop_18_5
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.prop_18_5'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isLeast_low
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isGreatest_up
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_approx_fixed_point
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.schauder
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.schauder_subtype
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.schauder_closed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.schauder_closed_subtype
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.totallyBounded_of_equicontinuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.theorem_17_4
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bcf_le_iff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.isMonotoneOperator
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.isMonotoneOperator_iff_monotoneOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.cauchySeq_of_uniformEquicontinuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.lemma_17_6
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.monotone_iterate_of_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.antitone_iterate_of_ge
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_abs_le_of_isBounded
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.theorem_17_7_of_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.theorem_17_7_of_ge
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.theorem_17_7
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.le_of_tendsto_bcf
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ge_of_tendsto_bcf
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.corollary_17_7_least
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.corollary_17_7_greatest
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.corollary_17_7
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.corollary_17_7_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.totallyBounded_univ_of_isBounded
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.theorem_17_7_of_isBounded
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.Zd
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.Rd
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.Tval
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.euler_coef_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.isEulerRHS
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.eulerBelow_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.manual_rhs_limit_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.Tval_mem_Icc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.Tval_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.Tval_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.Tval_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.abs_Tval_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.le_Tval
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.Tval_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.isInF_Tval
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.T
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.T_apply
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ext_T
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ex_18_5
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ex_18_5_wellDefined
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ex_18_7
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.eventually_abs_Tval_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ex_18_6
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.F_isCompact
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.exists_equilibrium
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.IsInF.Tval_lt_psi_of_fixed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isFixedPt_iff_euler
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.T_equicontinuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.least_greatest_equilibria
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.unique_equilibrium_of_tendsto
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.monotone_iterate_low
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.antitone_iterate_up
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.hE
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.isInF_hE
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.GlobalModel.ex_18_5_counterexample_of
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.tech
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.β
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.θ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.U'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.B
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.κ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.tech_β
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.tech_θ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.tech_U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.tech_U'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.kbar_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.κ_prob
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.κ_feller
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.psi_cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.f'_cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.B_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.isMarginalUtility
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.coef_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.psi_le_B
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.lt_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.mono_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.G
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.Rc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.Tc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.G_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.G_continuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.G_integrable
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.Rc_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.IsInFc.isEulerRHS
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.ex_18_9_spec_KT
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.CrossState
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.isInFc_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.ex_18_9_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.ex_18_9
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ContModel.ex_18_9_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.sqrt_contDiffOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.sqrt_strictMonoOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.sqrt_hasDerivAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.sqrt_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ratTech_hasDerivAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ratTech_psi_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ratModel
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelE
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelE_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelE_f'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelE_β
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelE_θ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelE_psi_psi_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_5_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.phiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PhiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.fL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.psiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.phiL_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.phiL_le_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_phiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.phiL_strictAntiOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_PhiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_fL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_phiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_psiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_psiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.mul_phiL_le_PhiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.three_le_psiL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.psiL_twenty_lt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.psiL_sub_strictAntiOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_kbarL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.kbarL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.kbarL_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.psiL_kbarL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.contDiff_fL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelL
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_5_bound_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tech
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.β
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.θ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.U'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.B
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.π
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tech_β
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tech_θ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tech_U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tech_U'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.kbar_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.B_eq
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.π_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.π_sum
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.B_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.isMarginalUtility
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.coef_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.psi_le_B
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.le_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.mono_sub
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Zs
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Rs
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.term_anti
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.term_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.isEulerRHS
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts_mem_Icc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.ex_18_8_spec_KT
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.CrossState
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.eulerBelow_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.ex_18_8_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.Ts_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.ex_18_8
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.ex_18_8_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.isInFs_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.isInFs_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.exists_pi_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.no_solution_at_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.no_solution_of_crossState_fails
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.modelHigh
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.stochJ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.stochJ_crossState_fails
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_8_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.abs_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.IsInFs.abs_Ts_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts_equicontinuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.rhsConvergesAt_of_tendsto
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts_tendsto
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts_tendsto_uniform
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.TsOp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Tsit
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Tsit_succ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.isInFs_Tsit
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Tsit_le_succ
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Tsit_le_of_super
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.lfp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tendsto_Tsit
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.isInFs_lfp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.Ts_lfp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.tendstoUniformly_Tsit
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.lfp_le_of_super
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.stoch_least_greatest
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.lfp_equilibrium_of_super
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.identical_tech_fixed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.crossState_of_identical
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.StochModel.exists_nondegenerate_equilibrium_identical
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.consPath
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.IndivFeasible
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indivValues
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.concave_le_tangent
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.strictConcave_lt_tangent
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_telescope
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_partial_sum_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_tvc_optimal
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_tvc_strict
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_tvc_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_tvc_isGreatest
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.tvc_of_bounded
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.budget_rebate
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.pseudo_economy_solves_6_7
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.tvc_indiv_imp_pseudo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.tvc_pseudo_not_imp_indiv_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_budget
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_foc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_manual_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_requires_sum_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_sequential_budget
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_sequential_euler
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_2_sequential_ne
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.feasY
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.SolvesBellman
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.selPath
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.iterate_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_isLUB
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.policyValue_hasSum
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.euler_tvc_gap
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.dp_diagonal
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_dp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium_dp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.DPState
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.wExt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.wExt_of_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellOp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellOp_abs_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellOp_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellLp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellLp_contracting
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_bellman_solution
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.plannerValues
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.planner_optimal
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.pathValue
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.pathValue_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_full
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium_full
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_of_concave_of_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_concave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_bddAbove
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_foc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_envelope
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bellman_diagonal
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eq_18_1_4_5
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eq_18_1_6_7
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eq_18_1_6_7_of_equilibrium
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_foc_envelope
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.b_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.b_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.kbar_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.U_cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.U_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.U_strictConcave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.f_cont
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.f_concave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.f_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.f_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.SolvesPlanner
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.clampK
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.clampK_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.clampK_of_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_clampK
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.continuous_U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.continuous_f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.exists_bound
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.UB
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.UB_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.plannerG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.continuous_plannerG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.abs_plannerG_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.bddAbove_plannerG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.plannerOp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.image_plannerG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerOp_apply
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerOp_contracting
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.plannerValue
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerValue_fixed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerValue_solves
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.continuousOn_maximand
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.exists_max
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerOp_concave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerValue_concave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.max_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.plannerPolicy
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_continuousOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.planner_envelope
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.planner_foc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.planner_euler
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.plannerHyp_of_differentiable
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.planner_euler_tvc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_constructed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium_constructed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.dp_diagonal_pathwise
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_dp_pathwise
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium_dp_pathwise
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.planner_optimal_pathwise
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_full_pathwise
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium_full_pathwise
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inada_exists_delta
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_lt_of_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.plannerPolicy_pos_of_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.PlannerHyp.deriv_U_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.planner
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.b_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.U_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.f_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.f_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.policy_interior
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.policy_mem_Ioo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.policy_mapsTo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.not_interior_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.planner_euler_interior
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.tvc_bound
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.InteriorHyp.planner_tvc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_1_interior
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.indirect_equilibrium_interior
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inadaU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inadaU_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_inadaU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inadaU_monotoneOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inadaU_strictConcaveOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.abs_inadaU_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.differentiableAt_inadaU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inadaU_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inadaU_not_differentiableAt_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inada_interiorHyp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.sqrt_deriv_facts
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inada_example_interior
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inada_example_ex_18_1
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.inada_example_equilibrium
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Feq
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.beta_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.beta_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.U_contDiff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.U_strictMono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.U_strictConcave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.theta_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.theta_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.f_contDiff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.f_nonneg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.f_strictMono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.f_strictConcave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.f_zero_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.deriv_f_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.kbar_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.psi_gt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.psi_lt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.differentiable_of_C2
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.differentiable_deriv_of_C2
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_deriv_of_C2
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_deriv2_of_C2
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.dpsi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.deriv_pos_of_strictMono_concave
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.deriv_U_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.deriv_f_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.deriv_f_strictAnti
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.deriv_U_strictAnti
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.tendsto_deriv_f_zero
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.not_inada
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.psi_kbar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.le_psi
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.psi_gt_mul
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.euler_kbar_lt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.exists_unique_kstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Feq_diag
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_1
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F1f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F2f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F3f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_Feq_x
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_Feq_y
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_Feq_z
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.cstar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F1s
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F2s
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F3s
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.dpsi_star
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F1f_star
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F2f_star
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.F3f_star
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.beta_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.beta_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.theta_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.theta_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.U_contDiff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.f_contDiff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.ks_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.euler
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.deriv_U_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.deriv2_U_neg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.deriv2_f_neg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Assumption18_1.localHyp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.F1s_neg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.F3s_neg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.F2s_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.charPoly
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.charDisc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.lamStar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.lamTwo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.charPoly_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.charPoly_one_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.charPoly_zero_neg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.one_lt_F1s_div_F3s
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.charPoly_F1_div_F3
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.charPoly_roots
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.charPoly_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.H1s_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.H2s_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.H_lt_lam
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.H_sum_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.H2s_mul_lt_one
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.flatU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_flatU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_deriv_flatU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.strictConcave_deriv2_zero_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.charPoly_degenerate_U
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.charPoly_degenerate_f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Jint
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.clampI
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.clampI_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.clampI_of_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.abs_clampI_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Jint_mono
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.center_mem_Jint
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.mem_Jint_iff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.abs_sub_le_of_hasDerivAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.mul_sub_le_of_hasDerivAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.root_sep
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.root_exists
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.implicitRoot
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_cube_of_eventually
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.exists_cube
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.mk
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.eps_pos
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.eq7
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.unique
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.center
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.continuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.lipschitz
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.strictMono_left
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.strictMono_right
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.lip_near
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_localSolution
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Dlam
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Top
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.HBound
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Dlam_mapsTo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Dlam_congr
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Top_lipschitz
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Top_mem_Dlam
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Top_sub_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Top_strictMonoOn
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.local_constants
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_2
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_3
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.manualH
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.manualHc
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_3_manual_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex184H
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex184H'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_4a_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_4a
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_4a_mapsTo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_4b_const_not_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_3_printed_step_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_3
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.extendC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.extendC_of_mem
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_extendC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.TC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.extendC_TC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.mem_DC_iff
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.isClosed_DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.const_mem_DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.TC_mapsTo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.TC_dist_le
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.TC_contractingWith
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_3_continuous
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_3_contractingWith
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_4
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eq_of_fixed
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exists_fixedPoint_of_bounds
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_3_fixedPoint
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Elam
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_4b
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_exp_neg
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.deriv_exF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.deriv2_exF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.deriv_exU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.deriv2_exU
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.psi_exF
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_exG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.deriv2_exG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_exG
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exModel_assumption
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exU_admissible
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.exModel_localHyp
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.note_18_2B_model_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.ex_18_4a_model_counterexample
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.convex_DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.abs_le_of_mem_DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.isBounded_DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.totallyBounded_DC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuousOn_TC
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.localSchauder_fixedPoint_of_mapsTo
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_2_schauder
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_2_schauder_eq_contraction
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_F1f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_F2f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_F3f
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Fxz
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Fyy
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasFDerivAt_Feq_xz
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasFDerivAt_Feq_yy
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_Fxz
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.continuous_Fyy
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.mulEquiv'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Fyy_eq_mulEquiv'
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Fyy_isInvertible
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bivImplicit
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Hderiv
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.bivImplicit_spec
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.eventuallyEq_bivImplicit
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.hasStrictFDerivAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.Hderiv_center
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.hasStrictFDerivAt_center
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_H_left
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_H_right
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.contDiffAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalSolution.eventually_contDiffAt
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.LocalHyp.lamStar_eq
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.hasDerivAt_fixedPoint_lamStar
#print axioms StokeyLucasPrescott.EquilibriaWithDistortions.prop_18_3_deriv
