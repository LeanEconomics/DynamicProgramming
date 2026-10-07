/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.JumpChains
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Valuation in continuous time

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.2.1 (pp. 329–334).

For a positive exponential semigroup `K_t = e^{tA}` and a reward `h`, lifetime value is
`v = ∫₀^∞ K_t h dt` (10.38).

* **Proposition 10.2.1**: if `s(A) < 0` then (i) the integral is finite and
  `v = ∫₀^t K_τ h dτ + K_t v` (10.39); (ii) `A` is invertible and `v = −A⁻¹h`; (iii) `A⁻¹ ≤ 0`; and
  (iv) `Uw = h + (I + A)w` is order stable with unique fixed point `v`. Here `Av = −h` comes from
  the improper fundamental theorem of calculus, `∫₀^∞ (d/dt) e^{tA}h dt = −h`.
* Exercise 10.2.1: the path discount `η(s, t) = exp(−∫_s^t δ(X_τ) dτ)` is positive, `η(s, s) = 1`
  and `η(0, s + t) = η(0, s)η(s, s + t)`.
* **Proposition 10.2.3**: for an intensity matrix `Q` and `δ > 0`, `s(Q − δI) = −δ`, so
  `δI − Q` is invertible with `(δI − Q)⁻¹ ≥ 0`, `v = (δI − Q)⁻¹h`, and
  `Uw = h + (Q + (1 − δ)I)w` is order stable with unique fixed point `v`.

Proposition 10.2.2 (the Feynman–Kac semigroup of a continuous-time Markov chain) and the
interchange of expectation and integration in (10.44) concern the law of the chain and are not
formalised; Proposition 10.2.3 takes the semigroup form `v = ∫₀^∞ e^{−δt}P_t h dt` as the
definition of lifetime value.
-/

open Finset Matrix Filter Topology Function Set MeasureTheory

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `t ↦ e^{tA}h` is continuous. -/
theorem continuous_exp_smul_mulVec (A : Matrix X X ℝ) (h : X → ℝ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h :=
  (continuous_exp_smul A).matrix_mulVec continuous_const

/-- `v ↦ Mv` as a continuous linear map. -/
noncomputable def mulVecLinCLM (M : Matrix X X ℝ) : (X → ℝ) →L[ℝ] (X → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)

/-- The coordinate map `f ↦ f(x)` as a continuous linear map. -/
noncomputable def projCLM (x : X) : (X → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.proj x)

/-- Lifetime value (10.38): `v = ∫₀^∞ e^{tA}h dt`. -/
noncomputable def lifetimeValue (A : Matrix X X ℝ) (h : X → ℝ) : X → ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), NormedSpace.exp (t • A) *ᵥ h

variable [Nonempty X]

/-- **Proposition 10.2.1 (i)** (p. 329): for `s(A) < 0`, `t ↦ e^{tA}h` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_mulVec {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ) :
    IntegrableOn (fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h) (Ioi 0) := by
  have h4' : ∀ p : ℝ, 1 ≤ p → ∀ u₀ : X → ℝ, IntegrableOn
      (fun t : ℝ => ‖NormedSpace.exp (t • A) *ᵥ u₀‖ ^ p) (Set.Ioi 0) :=
    ((stability_tfae A).out 1 4).1 hs
  have h4 := h4' 1 le_rfl h
  simp only [Real.rpow_one] at h4
  exact (integrable_norm_iff (continuous_exp_smul_mulVec A h).aestronglyMeasurable).1 h4

omit [Nonempty X] in
/-- A matrix with negative spectral bound is invertible: `0` is not an eigenvalue. -/
theorem isUnit_of_spectralBound_neg {A : Matrix X X ℝ} (hs : spectralBound A < 0) : IsUnit A := by
  have h0 : (0 : ℂ) ∉ spectrum ℂ (complexify A) := fun h0 => by
    have := re_le_spectralBound h0
    simp only [Complex.zero_re] at this
    linarith
  rw [spectrum.notMem_iff, map_zero, zero_sub, IsUnit.neg_iff] at h0
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 h0
  have e : (complexify A).det = ((A.det : ℝ) : ℂ) := (Complex.ofRealHom.map_det A).symm
  rw [e] at hdet
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun hz => ?_)
  rw [hz, Complex.ofReal_zero] at hdet
  exact not_isUnit_zero hdet

/-- **Proposition 10.2.1 (ii)** (p. 329): for `s(A) < 0`, `Av = −h`. -/
theorem mulVec_lifetimeValue {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ) :
    A *ᵥ lifetimeValue A h = -h := by
  have hcomm : ∀ t : ℝ, A *ᵥ (NormedSpace.exp (t • A) *ᵥ h) = NormedSpace.exp (t • A) *ᵥ (A *ᵥ h) :=
    fun t => by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_smul_mul_comm]
  have hlim : Tendsto (fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖) atTop (𝓝 0) :=
      ((stability_tfae A).out 1 2).1 hs
    refine squeeze_zero (fun _ => norm_nonneg _) (fun t => Matrix.linfty_opNorm_mulVec _ _) ?_
    simpa using h2.mul_const ‖h‖
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h)
    (f' := fun t => A *ᵥ (NormedSpace.exp (t • A) *ᵥ h))
    (continuous_exp_smul_mulVec A h).continuousWithinAt
    (fun t _ => hasDerivAt_exp_smul_mulVec A h t)
    (by simp_rw [hcomm]; exact integrableOn_exp_mulVec hs (A *ᵥ h)) hlim
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, zero_sub] at hftc
  rw [← hftc, lifetimeValue]
  exact ((mulVecLinCLM A).integral_comp_comm (integrableOn_exp_mulVec hs h)).symm

/-- **Proposition 10.2.1 (ii)** (p. 329): for `s(A) < 0`, `A` is invertible and `v = −A⁻¹h`. -/
theorem lifetimeValue_eq {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ) :
    IsUnit A ∧ lifetimeValue A h = -(A⁻¹ *ᵥ h) := by
  have hA := isUnit_of_spectralBound_neg hs
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hA
  refine ⟨hA, ?_⟩
  rw [← mulVec_neg, ← mulVec_lifetimeValue hs h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **Proposition 10.2.1 (i)** (p. 329), (10.39): `v = ∫₀^t K_τ h dτ + K_t v` for `t ≥ 0`. -/
theorem lifetimeValue_eq_integral_add {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ)
    (t : ℝ) :
    lifetimeValue A h = (∫ τ in (0 : ℝ)..t, NormedSpace.exp (τ • A) *ᵥ h) +
      NormedSpace.exp (t • A) *ᵥ lifetimeValue A h := by
  set v := lifetimeValue A h
  have hv : A *ᵥ v = -h := mulVec_lifetimeValue hs h
  have hint : ∀ τ : ℝ, NormedSpace.exp (τ • A) *ᵥ h =
      -(A *ᵥ (NormedSpace.exp (τ • A) *ᵥ v)) := fun τ => by
    rw [Matrix.mulVec_mulVec, ← exp_smul_mul_comm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_neg,
      neg_neg]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ => NormedSpace.exp (τ • A) *ᵥ v)
    (f' := fun τ => A *ᵥ (NormedSpace.exp (τ • A) *ᵥ v)) (a := 0) (b := t)
    (fun τ _ => hasDerivAt_exp_smul_mulVec A v τ)
    ((continuous_const.matrix_mulVec (continuous_exp_smul_mulVec A v)).intervalIntegrable _ _)
  simp_rw [hint]
  rw [intervalIntegral.integral_neg, hftc]
  simp

/-- **Proposition 10.2.1 (iii)** (p. 329): if moreover `e^{tA} ≥ 0` for `t ≥ 0`, then `A⁻¹ ≤ 0`
entrywise. -/
theorem inv_nonpos {A : Matrix X X ℝ} (hs : spectralBound A < 0)
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ x y, 0 ≤ NormedSpace.exp (t • A) x y) (x y : X) :
    A⁻¹ x y ≤ 0 := by
  have hval := (lifetimeValue_eq hs (Pi.single y 1)).2
  have hnn : 0 ≤ lifetimeValue A (Pi.single y 1) x := by
    rw [lifetimeValue, show (∫ t in Set.Ioi (0 : ℝ), NormedSpace.exp (t • A) *ᵥ Pi.single y 1) x =
      ∫ t in Set.Ioi (0 : ℝ), (NormedSpace.exp (t • A) *ᵥ Pi.single y 1) x from
      ((projCLM x).integral_comp_comm (integrableOn_exp_mulVec hs _)).symm]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact hpos t (le_of_lt ht) x y
  rw [hval] at hnn
  simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hnn
  linarith

omit [Nonempty X] in
/-- `−A⁻¹` is a positive operator when `A⁻¹ ≤ 0`. -/
theorem neg_inv_mulVec_nonneg {A : Matrix X X ℝ} (hA : ∀ x y, A⁻¹ x y ≤ 0) {f : X → ℝ}
    (hf : 0 ≤ f) : 0 ≤ -(A⁻¹ *ᵥ f) := fun x => by
  simp only [Pi.neg_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, neg_nonneg]
  exact Finset.sum_nonpos fun y _ => mul_nonpos_of_nonpos_of_nonneg (hA x y) (hf y)

/-- **Proposition 10.2.1 (iv)** (p. 330): `Uw = h + (I + A)w` is order stable on `ℝ^X`, with unique
fixed point `v`. -/
theorem orderStable_valuation {A : Matrix X X ℝ} (hs : spectralBound A < 0)
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ x y, 0 ≤ NormedSpace.exp (t • A) x y) (h : X → ℝ) :
    OrderStable (fun w => h + (1 + A) *ᵥ w) ∧ IsFixedPt (fun w => h + (1 + A) *ᵥ w)
      (lifetimeValue A h) := by
  obtain ⟨hA, hv⟩ := lifetimeValue_eq hs h
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hA
  have hneg := inv_nonpos hs hpos
  have hfix : IsFixedPt (fun w => h + (1 + A) *ᵥ w) (lifetimeValue A h) := by
    change h + (1 + A) *ᵥ lifetimeValue A h = lifetimeValue A h
    rw [Matrix.add_mulVec, Matrix.one_mulVec, mulVec_lifetimeValue hs h]
    abel
  -- `v − w = −A⁻¹(h + Aw)`
  have key : ∀ w, lifetimeValue A h - w = -(A⁻¹ *ᵥ (h + A *ᵥ w)) := fun w => by
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
    abel
  refine ⟨orderStable_of_up_down hfix (fun w hw => ?_) (fun w hw => ?_), hfix⟩
  · have hw' : 0 ≤ h + A *ᵥ w := fun x => by
      have := hw x
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply] at this
      simp only [Pi.add_apply, Pi.zero_apply]
      linarith
    have := neg_inv_mulVec_nonneg hneg hw'
    rw [← key] at this
    exact sub_nonneg.1 this
  · have hw' : 0 ≤ -(h + A *ᵥ w) := fun x => by
      have := hw x
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply] at this
      simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply]
      linarith
    have := neg_inv_mulVec_nonneg hneg hw'
    rw [Matrix.mulVec_neg, neg_neg, ← neg_neg (A⁻¹ *ᵥ (h + A *ᵥ w)), ← key] at this
    intro x
    have := this x
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.zero_apply] at this
    linarith

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- **Exercise 10.2.1** (p. 332): along a path `τ ↦ X_τ` with `τ ↦ δ(X_τ)` locally integrable,
`η(s, t) = exp(−∫_s^t δ(X_τ) dτ)` satisfies (i) `η > 0`, (ii) `η(s, s) = 1` and
(iii) `η(0, s + t) = η(0, s)η(s, s + t)`. -/
theorem pathDiscount_properties {S : Type*} (path : ℝ → S) (δ : S → ℝ)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun τ => δ (path τ)) volume a b) (s t : ℝ) :
    0 < Real.exp (-∫ τ in s..t, δ (path τ)) ∧ Real.exp (-∫ τ in s..s, δ (path τ)) = 1 ∧
      Real.exp (-∫ τ in (0 : ℝ)..s + t, δ (path τ)) =
        Real.exp (-∫ τ in (0 : ℝ)..s, δ (path τ)) * Real.exp (-∫ τ in s..s + t, δ (path τ)) := by
  refine ⟨Real.exp_pos _, by simp, ?_⟩
  rw [← Real.exp_add,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + t))]
  ring_nf

omit [Nonempty X] in
/-- `e^{t(Q − δI)} = e^{−tδ}e^{tQ}`. -/
theorem exp_smul_sub_smul_one (Q : Matrix X X ℝ) (δ t : ℝ) :
    NormedSpace.exp (t • (Q - δ • (1 : Matrix X X ℝ))) =
      Real.exp (-(t * δ)) • NormedSpace.exp (t • Q) := by
  have hsplit : t • (Q - δ • (1 : Matrix X X ℝ)) = t • Q + (-(t * δ)) • (1 : Matrix X X ℝ) := by
    module
  rw [hsplit, exp_add_eq (((Commute.one_right Q).smul_left t).smul_right _), exp_smul_one,
    Matrix.mul_smul, Matrix.mul_one]

/-- **Proposition 10.2.3** (p. 333): for an intensity matrix `Q` and `δ > 0`, `s(Q − δI) = −δ`;
`δI − Q` is invertible with `(δI − Q)⁻¹ ≥ 0`; lifetime value `v = ∫₀^∞ e^{−δt}P_t h dt` equals
`(δI − Q)⁻¹h`; and `Uw = h + (Q + (1 − δ)I)w` is order stable with unique fixed point `v`. -/
theorem constant_discounting {Q : Matrix X X ℝ} (hQ : IsIntensity Q) {δ : ℝ} (hδ : 0 < δ)
    (h : X → ℝ) :
    spectralBound (Q - δ • 1) = -δ ∧ IsUnit (δ • (1 : Matrix X X ℝ) - Q) ∧
      (∀ x y, 0 ≤ (δ • (1 : Matrix X X ℝ) - Q)⁻¹ x y) ∧
      lifetimeValue (Q - δ • 1) h = (δ • (1 : Matrix X X ℝ) - Q)⁻¹ *ᵥ h ∧
      OrderStable (fun w => h + (Q + (1 - δ) • (1 : Matrix X X ℝ)) *ᵥ w) ∧
      IsFixedPt (fun w => h + (Q + (1 - δ) • (1 : Matrix X X ℝ)) *ᵥ w)
        (lifetimeValue (Q - δ • 1) h) := by
  set A := Q - δ • (1 : Matrix X X ℝ)
  have hmarkov := ((intensity_tfae Q).out 1 2).1 hQ
  -- `s(A) = −δ`
  have hs : spectralBound A = -δ := by
    have h1 := specRad_exp A
    have hexpA : NormedSpace.exp A = Real.exp (-δ) • NormedSpace.exp Q := by
      have := exp_smul_sub_smul_one Q δ 1
      simpa only [one_smul, one_mul] using this
    have hm1 : IsMarkov (NormedSpace.exp Q) := by
      have := hmarkov 1 zero_le_one
      rwa [one_smul] at this
    rw [hexpA, specRad_smul_isMarkov hm1 (Real.exp_pos _).le] at h1
    exact (Real.exp_injective h1).symm
  have hsneg : spectralBound A < 0 := by rw [hs]; linarith
  have hpos : ∀ t : ℝ, 0 ≤ t → ∀ x y, 0 ≤ NormedSpace.exp (t • A) x y := fun t ht x y => by
    rw [exp_smul_sub_smul_one, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (Real.exp_pos _).le (exp_smul_nonneg hQ ht x y)
  obtain ⟨hA, hv⟩ := lifetimeValue_eq hsneg h
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hA
  have hnegA : δ • (1 : Matrix X X ℝ) - Q = -A := by simp [A]
  have hinv : (δ • (1 : Matrix X X ℝ) - Q)⁻¹ = -A⁻¹ := by
    rw [hnegA]
    exact Matrix.inv_eq_right_inv (by rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hdet])
  have hU : Q + (1 - δ) • (1 : Matrix X X ℝ) = 1 + A := by
    simp only [A]
    module
  obtain ⟨hos, hfix⟩ := orderStable_valuation hsneg hpos h
  refine ⟨hs, by rw [hnegA]; exact hA.neg, fun x y => ?_, ?_, by rw [hU]; exact hos,
    by rw [hU]; exact hfix⟩
  · rw [hinv, Matrix.neg_apply]
    exact neg_nonneg.2 (inv_nonpos hsneg hpos x y)
  · rw [hv, hinv, Matrix.neg_mulVec]

end SargentStachurski.ContinuousTime
