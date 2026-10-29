/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.DiscreteSpectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Riesz–Schauder theory and Proposition 20.1.5 (MT §20.1.4)

Meyn and Tweedie, p. 518. Proposition 20.1.5 rests on Theorem 3.5 of Kontoyiannis–Meyn [219]:
an operator that is a norm limit of finite-rank operators has a discrete spectrum. Mathlib has
compact operators, their closure under norm limits, and the Fredholm alternative
(`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`). This module proves the remaining
Riesz–Schauder facts on a complex Banach space.

* `compact_not_separated`: a compact operator maps a bounded sequence to one with no infinite
  `ε`-separated subsequence (total boundedness and pigeonhole).
* `finite_eigenvalues`: **finitely many eigenvalues with `|μ| ≥ ε`**. Eigenvectors are
  independent, and the Riesz lemma (`riesz_lemma_of_norm_lt`) along the spans gives a separated
  sequence. `finite_spectrum_compact`: the same for the spectrum, by the Fredholm alternative.
* `circleIntegral_clm_comm`, `continuousOn_resolvent`, `resolvent_eq_inv_add`,
  `resolvent_mul_resolvent` (the resolvent identity) and `inv_sub_inv_ring`.
* `rieszProj_eq_of_le`: the Riesz projection does not depend on the radius (Cauchy on an
  annulus).
* `isCompactOperator_rieszProj`: at `z₀ ≠ 0` it is `T ∘ ∮z⁻¹R(z)dz`, a compact operator.
* `rieszProj_mul_self`: it is idempotent, by the resolvent identity and the analyticity of the
  Cauchy integral of `R` (`hasFPowerSeriesOn_cauchy_integral`).
* `finiteDimensional_range_of_compact_idempotent`: a compact projection has finite rank.
* `isFinitePole_of_compact`: every nonzero spectral point of a compact operator is a pole of finite
  multiplicity. `hasDiscreteSpectrum_of_compact`: **a compact operator has a discrete spectrum**
  in the sense of MT p. 512 (iv).
* **Proposition 20.1.5** (`proposition_20_1_5`): on a countable space, (DV3) with coercive
  `f ≥ 1`, finite `C` and `V ≥ 0` gives a discrete spectrum for `P` in `L∞_v`, `v = e^V` (through
  `proposition_20_1_5_compact`).

**Hypotheses.** As in `DiscreteSpectrum`: `V` real-valued with `V ≥ 0`, and `f ≥ 1`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Compact operators: no separated sequences in the image of a ball -/

/-- A compact operator maps a bounded sequence to a sequence with no `ε`-separated infinite
subsequence. -/
theorem compact_not_separated {T : E →L[ℂ] E} (hT : IsCompactOperator T) {r ε : ℝ}
    (hε : 0 < ε) (y : ℕ → E) (hy : ∀ n, ‖y n‖ ≤ r) :
    ¬ ∀ m n, m < n → ε ≤ ‖T (y n) - T (y m)‖ := by
  intro hsep
  have hK := hT.isCompact_closure_image_closedBall r
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (ε / 2) (half_pos hε)
  have hmem : ∀ n, ∃ c ∈ t, T (y n) ∈ Metric.ball c (ε / 2) := fun n => by
    have : T (y n) ∈ closure (T '' Metric.closedBall 0 r) :=
      subset_closure ⟨y n, by rw [Metric.mem_closedBall, dist_zero_right]; exact hy n, rfl⟩
    simpa only [mem_iUnion, exists_prop] using hcov this
  choose c hct hcb using hmem
  have : Finite t := htf.to_subtype
  obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n => (⟨c n, hct n⟩ : t))
  have hc : c m = c n := congrArg Subtype.val heq
  have hd : dist (T (y m)) (T (y n)) < ε := by
    calc dist (T (y m)) (T (y n)) ≤ dist (T (y m)) (c m) + dist (c n) (T (y n)) := by
          rw [hc]; exact dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hcb m) (by rw [dist_comm]; exact hcb n)
      _ = ε := add_halves ε
  rcases lt_or_gt_of_ne hmn with h | h
  · have := hsep m n h
    rw [dist_eq_norm, norm_sub_rev] at hd
    linarith
  · have := hsep n m h
    rw [dist_eq_norm] at hd
    linarith

/-! ### Finitely many eigenvalues outside every disc -/

/-- **A compact operator has finitely many eigenvalues `μ` with `|μ| ≥ ε`**, for every `ε > 0`
(Riesz): eigenvectors for distinct eigenvalues are independent, and the Riesz lemma along the
increasing spans produces a bounded sequence whose images are `ε`-separated. -/
theorem finite_eigenvalues {T : E →L[ℂ] E} (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℂ | Module.End.HasEigenvalue (T : Module.End ℂ E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  by_contra hinf
  set S := {μ : ℂ | Module.End.HasEigenvalue (T : Module.End ℂ E) μ ∧ ε ≤ ‖μ‖}
  have hinf' : S.Infinite := hinf
  set μ : ℕ → ℂ := fun n => (hinf'.natEmbedding S n : ℂ) with hμ
  have hμinj : Function.Injective μ := fun a b h =>
    (hinf'.natEmbedding S).injective (Subtype.ext h)
  have hμS : ∀ n, μ n ∈ S := fun n => (hinf'.natEmbedding S n).2
  have hμne : ∀ n, μ n ≠ 0 := fun n h => by
    have := (hμS n).2; rw [h, norm_zero] at this; linarith
  choose v hv using fun n => (hμS n).1.exists_hasEigenvector
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End ℂ E) μ hμinj v hv
  have hTv : ∀ n, T (v n) = μ n • v n := fun n => (hv n).apply_eq_smul
  set M : ℕ → Submodule ℂ E := fun n => Submodule.span ℂ (v '' Iio n) with hM
  have hMmono : Monotone M := fun a b hab =>
    Submodule.span_mono (image_mono (Iio_subset_Iio hab))
  have hMfin : ∀ n, FiniteDimensional ℂ (M n) := fun n =>
    FiniteDimensional.span_of_finite ℂ ((finite_Iio n).image v)
  have hvM : ∀ k n, k < n → v k ∈ M n := fun k n h =>
    Submodule.subset_span ⟨k, h, rfl⟩
  -- `(T − μₙ) M_{n+1} ⊆ Mₙ` and `T Mₙ ⊆ Mₙ`
  have hshift : ∀ n, ∀ x ∈ M (n + 1), T x - μ n • x ∈ M n := fun n x hx => by
    have hle : M (n + 1) ≤ (M n).comap ((T : E →ₗ[ℂ] E) - μ n • LinearMap.id) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, hk, rfl⟩
      change T (v k) - μ n • v k ∈ M n
      rw [hTv, ← sub_smul]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hk) with h | h
      · exact (M n).smul_mem _ (hvM k n h)
      · rw [h, sub_self, zero_smul]; exact (M n).zero_mem
    exact hle hx
  have hinv : ∀ n, ∀ x ∈ M n, T x ∈ M n := fun n x hx => by
    have hle : M n ≤ (M n).comap (T : E →ₗ[ℂ] E) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, hk, rfl⟩
      change T (v k) ∈ M n
      rw [hTv]; exact (M n).smul_mem _ (hvM k n hk)
    exact hle hx
  -- the Riesz sequence
  have hriesz : ∀ n, ∃ y : E, y ∈ M (n + 1) ∧ ‖y‖ ≤ 3 ∧ ∀ z ∈ M n, 1 ≤ ‖y - z‖ := fun n => by
    set F : Submodule ℂ (M (n + 1)) := (M n).comap (M (n + 1)).subtype
    have : FiniteDimensional ℂ (M (n + 1)) := hMfin (n + 1)
    have hFc : IsClosed (F : Set (M (n + 1))) := F.closed_of_finiteDimensional
    have hvn : v n ∉ M n := hli.notMem_span_image (lt_irrefl n)
    have hF : ∃ x : M (n + 1), x ∉ F := ⟨⟨v n, hvM n (n + 1) (Nat.lt_succ_self n)⟩, hvn⟩
    obtain ⟨x₀, hx₀, hdist⟩ := riesz_lemma_of_norm_lt (c := (2 : ℂ)) (by norm_num)
      (R := 3) (by norm_num) hFc hF
    refine ⟨x₀, x₀.2, hx₀, fun z hz => ?_⟩
    have := hdist ⟨z, hMmono (Nat.le_succ n) hz⟩ hz
    exact this
  choose y hyM hyb hyd using hriesz
  refine compact_not_separated hT hε y hyb fun m n hmn => ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hw : (μ (k + 1))⁻¹ • ((μ (k + 1) • y (k + 1) - T (y (k + 1))) + T (y m)) ∈ M (k + 1) := by
    refine (M (k + 1)).smul_mem _ ((M (k + 1)).add_mem ?_ ?_)
    · have := hshift (k + 1) _ (hyM (k + 1))
      rw [← neg_sub]; exact (M (k + 1)).neg_mem this
    · exact hMmono (by omega) (hinv (m + 1) _ (hyM m))
  have hid : T (y (k + 1)) - T (y m) = μ (k + 1) •
      (y (k + 1) - (μ (k + 1))⁻¹ • ((μ (k + 1) • y (k + 1) - T (y (k + 1))) + T (y m))) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (hμne _), one_smul]
    abel
  rw [hid, norm_smul]
  have h1 := hyd (k + 1) _ hw
  have h2 := (hμS (k + 1)).2
  nlinarith [norm_nonneg (y (k + 1) - (μ (k + 1))⁻¹ • ((μ (k + 1) • y (k + 1) -
    T (y (k + 1))) + T (y m)))]

variable [CompleteSpace E] in
/-- **The spectrum of a compact operator outside every disc is finite** (Riesz–Schauder): by the
Fredholm alternative (Mathlib) its nonzero points are eigenvalues. -/
theorem finite_spectrum_compact {T : E →L[ℂ] E} (hT : IsCompactOperator T) {ε : ℝ}
    (hε : 0 < ε) : {z ∈ spectrum ℂ T | ε ≤ ‖z‖}.Finite :=
  (finite_eigenvalues hT hε).subset fun z hz => ⟨(hT.hasEigenvalue_iff_mem_spectrum
    (fun h => by have := hz.2; rw [h, norm_zero] at this; linarith)).2 hz.1, hz.2⟩


/-! ### Riesz projections of compact operators -/

variable [CompleteSpace E]

/-- Circle integrals commute with continuous linear maps. -/
theorem circleIntegral_clm_comm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : F →L[ℂ] G) {f : ℂ → F} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) :
    ∮ z in C(c, r), L (f z) = L (∮ z in C(c, r), f z) := by
  unfold circleIntegral
  refine (intervalIntegral.integral_congr fun θ _ => ?_).trans
    (L.intervalIntegral_comp_comm hf.out)
  exact (L.map_smul _ _).symm

/-- The resolvent is continuous on the resolvent set. -/
theorem continuousOn_resolvent (T : E →L[ℂ] E) {s : Set ℂ} (hs : s ⊆ resolventSet ℂ T) :
    ContinuousOn (fun z => _root_.resolvent T z) s := fun _z hz =>
  (spectrum.hasDerivAt_resolvent_const_left (hs hz)).continuousAt.continuousWithinAt

/-- **The Riesz projection does not depend on the radius** while the annulus avoids the spectrum
(Cauchy's theorem on an annulus). -/
theorem rieszProj_eq_of_le (T : E →L[ℂ] E) {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hres : ∀ z, r ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ R → z ∈ resolventSet ℂ T) :
    rieszProj T z₀ R = rieszProj T z₀ r := by
  unfold rieszProj
  congr 1
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    countable_empty (continuousOn_resolvent T fun z hz => ?_) fun z hz => ?_
  · rw [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, not_lt] at hz
    exact hres z (by rw [← dist_eq_norm]; exact hz.2) (by rw [← dist_eq_norm]; exact hz.1)
  · rw [Set.mem_sdiff, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (hres z (by rw [← dist_eq_norm]; exact hz.1.2.le)
        (by rw [← dist_eq_norm]; exact hz.1.1.le))).differentiableAt

omit [CompleteSpace E] in
/-- `R(z) = z⁻¹ + T(z⁻¹R(z))` from `(z − T)R(z) = 1`. -/
theorem resolvent_eq_inv_add (T : E →L[ℂ] E) {z : ℂ} (hz : z ∈ resolventSet ℂ T) (hz0 : z ≠ 0) :
    _root_.resolvent T z = z⁻¹ • (1 : E →L[ℂ] E) + T * (z⁻¹ • _root_.resolvent T z) := by
  have h := Ring.mul_inverse_cancel _ (spectrum.mem_resolventSet_iff.1 hz)
  rw [Algebra.algebraMap_eq_smul_one, sub_mul, smul_mul_assoc, one_mul] at h
  change z • _root_.resolvent T z - T * _root_.resolvent T z = 1 at h
  rw [mul_smul_comm, ← h, smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul, sub_add_cancel]

/-- **The Riesz projection of a compact operator at `z₀ ≠ 0` is compact**: on a circle not
enclosing `0`, `∮R(z) dz = T ∮ z⁻¹R(z) dz`. -/
theorem isCompactOperator_rieszProj {T : E →L[ℂ] E} (hT : IsCompactOperator T) {z₀ : ℂ}
    {r : ℝ} (hr : 0 < r) (hr0 : r < ‖z₀‖)
    (hres : ∀ z, ‖z - z₀‖ = r → z ∈ resolventSet ℂ T) :
    IsCompactOperator (rieszProj T z₀ r) := by
  have hsph : ∀ z ∈ Metric.sphere z₀ r, z ∈ resolventSet ℂ T := fun z hz => by
    rw [mem_sphere_iff_norm] at hz; exact hres z hz
  have hne0 : ∀ z ∈ Metric.closedBall z₀ r, z ≠ 0 := fun z hz h => by
    rw [h, Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hz; linarith
  have hinvc : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.closedBall z₀ r) :=
    continuousOn_inv₀.mono fun z hz => hne0 z hz
  have hcR := continuousOn_resolvent T (s := Metric.sphere z₀ r) hsph
  have hc2 : ContinuousOn (fun z => T * (z⁻¹ • _root_.resolvent T z)) (Metric.sphere z₀ r) :=
    (continuous_const.mul continuous_id).comp_continuousOn ((hinvc.mono
      Metric.sphere_subset_closedBall).smul hcR)
  have hc1 : ContinuousOn (fun z : ℂ => z⁻¹ • (1 : E →L[ℂ] E)) (Metric.sphere z₀ r) :=
    (hinvc.mono Metric.sphere_subset_closedBall).smul continuousOn_const
  have hz0 : (∮ z in C(z₀, r), z⁻¹) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      hinvc fun z hz => differentiableAt_inv (hne0 z (Metric.ball_subset_closedBall hz.1))
  have hK : CircleIntegrable (fun z => z⁻¹ • _root_.resolvent T z) z₀ r :=
    ((hinvc.mono Metric.sphere_subset_closedBall).smul hcR).circleIntegrable hr.le
  have heq : rieszProj T z₀ r = T * ((2 * Real.pi * Complex.I)⁻¹ •
      ∮ z in C(z₀, r), z⁻¹ • _root_.resolvent T z) := by
    unfold rieszProj
    rw [circleIntegral.integral_congr hr.le fun z hz => resolvent_eq_inv_add T (hsph z hz)
      (hne0 z (Metric.sphere_subset_closedBall hz)),
      circleIntegral.integral_add (hc1.circleIntegrable hr.le) (hc2.circleIntegrable hr.le),
      circleIntegral.integral_smul_const, hz0, zero_smul, zero_add,
      show (∮ z in C(z₀, r), T * (z⁻¹ • _root_.resolvent T z)) =
        T * ∮ z in C(z₀, r), z⁻¹ • _root_.resolvent T z from
        circleIntegral_clm_comm (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) T) hK, mul_smul_comm]
  rw [heq]
  exact hT.comp_clm _

omit [CompleteSpace E] in
/-- `b⁻¹ − a⁻¹ = a⁻¹(a − b)b⁻¹` for units. -/
theorem inv_sub_inv_ring {A : Type*} [Ring A] {a b : A} (hu : IsUnit a) (hv : IsUnit b) :
    Ring.inverse b - Ring.inverse a = Ring.inverse a * (a - b) * Ring.inverse b := by
  rw [mul_sub, sub_mul, Ring.inverse_mul_cancel _ hu, one_mul, mul_assoc,
    Ring.mul_inverse_cancel _ hv, mul_one]

omit [CompleteSpace E] in
/-- **The resolvent identity** `R(z)R(w) = (z − w)⁻¹(R(w) − R(z))`. -/
theorem resolvent_mul_resolvent (T : E →L[ℂ] E) {z w : ℂ} (hz : z ∈ resolventSet ℂ T)
    (hw : w ∈ resolventSet ℂ T) (hzw : z ≠ w) :
    _root_.resolvent T z * _root_.resolvent T w =
      (z - w)⁻¹ • (_root_.resolvent T w - _root_.resolvent T z) := by
  have hu := spectrum.mem_resolventSet_iff.1 hz
  have hv := spectrum.mem_resolventSet_iff.1 hw
  have hab : (algebraMap ℂ (E →L[ℂ] E) z - T) - (algebraMap ℂ (E →L[ℂ] E) w - T) =
      (z - w) • (1 : E →L[ℂ] E) := by
    rw [sub_sub_sub_cancel_right, ← map_sub, Algebra.algebraMap_eq_smul_one]
  have key := inv_sub_inv_ring hu hv
  rw [hab, mul_smul_comm, mul_one, smul_mul_assoc] at key
  unfold _root_.resolvent
  rw [key, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hzw), one_smul]


/-- **The Riesz projection is idempotent**: with two radii `r₁ < r₂` around an isolated point,
`P² = P`, by the resolvent identity and Cauchy's formula (the Cauchy integral of `R` over the
outer circle is holomorphic inside it). -/
theorem rieszProj_mul_self (T : E →L[ℂ] E) {z₀ : ℂ} {r₁ r₂ : ℝ≥0} (h1 : 0 < r₁) (h12 : r₁ < r₂)
    (hres : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ resolventSet ℂ T) :
    rieszProj T z₀ r₁ * rieszProj T z₀ r₁ = rieszProj T z₀ r₁ := by
  set c : ℂ := 2 * Real.pi * Complex.I with hc
  have hc0 : c ≠ 0 := Complex.two_pi_I_ne_zero
  have h1' : (0 : ℝ) < r₁ := h1
  have h12' : (r₁ : ℝ) < r₂ := h12
  have h2' : (0 : ℝ) < r₂ := h1'.trans h12'
  set f : ℂ → E →L[ℂ] E := fun z => _root_.resolvent T z with hf
  have hres1 : ∀ z ∈ Metric.sphere z₀ (r₁ : ℝ), z ∈ resolventSet ℂ T := fun z hz => by
    rw [mem_sphere_iff_norm] at hz; exact hres z (by rw [hz]; exact h1') (by rw [hz]; exact h12'.le)
  have hres2 : ∀ z ∈ Metric.sphere z₀ (r₂ : ℝ), z ∈ resolventSet ℂ T := fun z hz => by
    rw [mem_sphere_iff_norm] at hz; exact hres z (by rw [hz]; exact h2') hz.le
  have hcf1 : ContinuousOn f (Metric.sphere z₀ r₁) := continuousOn_resolvent T hres1
  have hcf2 : ContinuousOn f (Metric.sphere z₀ r₂) := continuousOn_resolvent T hres2
  have hi1 : CircleIntegrable f z₀ r₁ := hcf1.circleIntegrable h1'.le
  have hi2 : CircleIntegrable f z₀ r₂ := hcf2.circleIntegrable h2'.le
  -- radius independence
  have hP : rieszProj T z₀ r₂ = rieszProj T z₀ r₁ :=
    rieszProj_eq_of_le T h1' h12'.le fun z hz1 hz2 => hres z (h1'.trans_le hz1) hz2
  -- the Cauchy integral of `R` over the outer circle
  set G : ℂ → E →L[ℂ] E := fun w => c⁻¹ • ∮ z in C(z₀, (r₂ : ℝ)), (z - w)⁻¹ • f z with hG
  have hGan := hasFPowerSeriesOn_cauchy_integral hi2 (lt_trans h1 h12)
  have hGd : ∀ w ∈ Metric.ball z₀ (r₂ : ℝ), DifferentiableAt ℂ G w := fun w hw =>
    (hGan.analyticAt_of_mem (by rw [Metric.eball_coe]; exact hw)).differentiableAt
  have hball : Metric.closedBall z₀ (r₁ : ℝ) ⊆ Metric.ball z₀ (r₂ : ℝ) :=
    Metric.closedBall_subset_ball h12'
  have hG0 : (∮ z in C(z₀, (r₁ : ℝ)), G z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable h1'.le countable_empty
      (fun w hw => (hGd w (hball hw)).continuousAt.continuousWithinAt)
      fun w hw => hGd w (hball (Metric.ball_subset_closedBall hw.1))
  -- the inner integral
  have hinner : ∀ z ∈ Metric.sphere z₀ (r₁ : ℝ),
      f z * (∮ w in C(z₀, (r₂ : ℝ)), f w) = (-c) • G z + c • f z := fun z hz => by
    have hzb : z ∈ Metric.ball z₀ (r₂ : ℝ) := hball (Metric.sphere_subset_closedBall hz)
    have hzw : ∀ w ∈ Metric.sphere z₀ (r₂ : ℝ), z ≠ w := fun w hw h => by
      rw [h] at hzb; rw [Metric.mem_ball, Metric.mem_sphere.1 hw] at hzb
      exact lt_irrefl _ hzb
    have hcz : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (Metric.sphere z₀ (r₂ : ℝ)) :=
      ((continuous_id.sub continuous_const).continuousOn).inv₀ fun w hw =>
        sub_ne_zero.2 (hzw w hw).symm
    have hci : CircleIntegrable (fun w => (w - z)⁻¹ • f w) z₀ r₂ :=
      (hcz.smul hcf2).circleIntegrable h2'.le
    have hcl : CircleIntegrable (fun w => (w - z)⁻¹) z₀ r₂ := hcz.circleIntegrable h2'.le
    rw [← show (∮ w in C(z₀, (r₂ : ℝ)), f z * f w) = f z * ∮ w in C(z₀, (r₂ : ℝ)), f w from
      circleIntegral_clm_comm (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (f z)) hi2]
    rw [circleIntegral.integral_congr h2'.le (g := fun w => (w - z)⁻¹ • f z - (w - z)⁻¹ • f w)
      fun w hw => by
        change _root_.resolvent T z * _root_.resolvent T w = (w - z)⁻¹ • _root_.resolvent T z -
          (w - z)⁻¹ • _root_.resolvent T w
        rw [resolvent_mul_resolvent T (hres1 z hz) (hres2 w hw) (hzw w hw), smul_sub,
          show (z - w)⁻¹ = -(w - z)⁻¹ by rw [← neg_sub, inv_neg], neg_smul, neg_smul]
        abel]
    have hcc : CircleIntegrable (fun w => (w - z)⁻¹ • f z) z₀ r₂ :=
      (hcz.smul continuousOn_const).circleIntegrable h2'.le
    rw [circleIntegral.integral_sub hcc hci,
      circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hzb, hG,
      smul_smul, neg_mul, mul_inv_cancel₀ hc0, neg_smul, one_smul]
    abel
  have hGc : ContinuousOn G (Metric.sphere z₀ (r₁ : ℝ)) := fun w hw =>
    (hGd w (hball (Metric.sphere_subset_closedBall hw))).continuousAt.continuousWithinAt
  have hA : CircleIntegrable (fun z => (-c) • G z) z₀ r₁ :=
    (hGc.const_smul (-c)).circleIntegrable h1'.le
  have hB : CircleIntegrable (fun z => c • f z) z₀ r₁ :=
    (hcf1.const_smul c).circleIntegrable h1'.le
  rw [show rieszProj T z₀ r₁ * rieszProj T z₀ r₁ = rieszProj T z₀ r₁ * rieszProj T z₀ r₂ by
    rw [hP]]
  unfold rieszProj
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    ← show (∮ z in C(z₀, (r₁ : ℝ)), f z * ∮ w in C(z₀, (r₂ : ℝ)), f w) =
      (∮ z in C(z₀, (r₁ : ℝ)), f z) * ∮ w in C(z₀, (r₂ : ℝ)), f w from
      circleIntegral_clm_comm ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip
        (∮ w in C(z₀, (r₂ : ℝ)), f w)) hi1,
    circleIntegral.integral_congr h1'.le hinner,
    circleIntegral.integral_add hA hB,
    circleIntegral.integral_smul (-c) G z₀ r₁, circleIntegral.integral_smul c f z₀ r₁, hG0,
    smul_zero, zero_add,
    smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]


omit [CompleteSpace E] in
/-- **A compact idempotent operator has finite rank**: the identity of its (closed) range is
compact, so the range is finite-dimensional (Riesz). -/
theorem finiteDimensional_range_of_compact_idempotent {P : E →L[ℂ] E}
    (hP : IsCompactOperator P) (hPP : P * P = P) :
    FiniteDimensional ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) := by
  set W := LinearMap.range (P : E →ₗ[ℂ] E)
  have hfix : ∀ x ∈ W, P x = x := by
    rintro _ ⟨y, rfl⟩
    change (P * P) y = P y
    rw [hPP]
  have hWset : (W : Set E) = {x | P x = x} := by
    ext x
    exact ⟨hfix x, fun h => ⟨x, h⟩⟩
  have hWc : IsClosed (W : Set E) := by
    rw [hWset]; exact isClosed_eq P.continuous continuous_id
  have hK := hP.isCompact_closure_image_closedBall 1
  have himg : (Subtype.val : W → E) '' Metric.closedBall (0 : W) 1 =
      (W : Set E) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      exact hw
    · rintro ⟨hx, hb⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hb ⊢
      exact hb
  have hcomp : IsCompact ((Subtype.val : W → E) '' Metric.closedBall (0 : W) 1) := by
    rw [himg]
    refine hK.of_isClosed_subset (hWc.inter Metric.isClosed_closedBall) ?_
    rintro x ⟨hx, hb⟩
    exact subset_closure ⟨x, hb, hfix x hx⟩
  exact FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one
    ((Topology.IsInducing.subtypeVal).isCompact_iff.2 hcomp)

/-- A finite set of points different from `z₀` stays at a positive distance from `z₀`. -/
theorem exists_pos_dist_of_finite {S : Set ℂ} (hS : S.Finite) {z₀ : ℂ} (hz₀ : z₀ ∉ S) :
    ∃ δ > 0, ∀ z ∈ S, δ ≤ ‖z - z₀‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun z hz => absurd hz (notMem_empty z)⟩
  obtain ⟨z₁, hz₁, hmin⟩ := hS.toFinset.exists_min_image (fun z => ‖z - z₀‖)
    (by rwa [Set.Finite.toFinset_nonempty])
  rw [Set.Finite.mem_toFinset] at hz₁
  refine ⟨‖z₁ - z₀‖, norm_pos_iff.2 (sub_ne_zero.2 fun h => hz₀ (h ▸ hz₁)),
    fun z hz => hmin z ((Set.Finite.mem_toFinset hS).2 hz)⟩

/-- **Every nonzero spectral point of a compact operator is a pole of finite multiplicity**
(Riesz–Schauder): it is isolated (finitely many spectral points outside each disc), the Riesz
projections are eventually constant, and the projection is compact and idempotent, hence of finite
rank. -/
theorem isFinitePole_of_compact {T : E →L[ℂ] E} (hT : IsCompactOperator T) {z₀ : ℂ}
    (hz₀ : z₀ ∈ spectrum ℂ T) (hz0 : z₀ ≠ 0) : IsFinitePole T z₀ := by
  have hn : 0 < ‖z₀‖ := norm_pos_iff.2 hz0
  have hF := finite_spectrum_compact hT (half_pos hn)
  obtain ⟨δ, hδ, hδF⟩ := exists_pos_dist_of_finite
    (S := {z ∈ spectrum ℂ T | ‖z₀‖ / 2 ≤ ‖z‖} \ {z₀}) (hF.subset sdiff_subset)
    (z₀ := z₀) (fun h => h.2 rfl)
  set δ' := min δ (‖z₀‖ / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (half_pos hn)
  have hiso : ∀ z ∈ spectrum ℂ T, ‖z - z₀‖ < δ' → z = z₀ := fun z hz hlt => by
    by_contra hne
    have hzF : ‖z₀‖ / 2 ≤ ‖z‖ := by
      have := norm_sub_norm_le z₀ (z₀ - z)
      rw [sub_sub_cancel, norm_sub_rev] at this
      have := min_le_right δ (‖z₀‖ / 2)
      linarith
    have := hδF z ⟨⟨hz, hzF⟩, hne⟩
    have := min_le_left δ (‖z₀‖ / 2)
    linarith
  have hres : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ' → z ∈ resolventSet ℂ T := fun z h0 hlt => by
    by_contra h
    have := hiso z h hlt
    rw [this, sub_self, norm_zero] at h0
    exact lt_irrefl 0 h0
  -- the radii
  set r₂ : ℝ≥0 := ⟨δ' / 2, by positivity⟩
  set r₁ : ℝ≥0 := ⟨δ' / 4, by positivity⟩
  have hr₁ : (0 : ℝ) < r₁ := by change 0 < δ' / 4; positivity
  have hr₁₂ : (r₁ : ℝ) < r₂ := by change δ' / 4 < δ' / 2; linarith
  have hr₂ : (r₂ : ℝ) < δ' := by change δ' / 2 < δ'; linarith
  have hconst : ∀ ε : ℝ, 0 < ε → ε ≤ (r₁ : ℝ) → rieszProj T z₀ ε = rieszProj T z₀ r₁ :=
    fun ε hε hεr =>
    (rieszProj_eq_of_le T hε hεr fun z hz1 hz2 =>
      hres z (hε.trans_le hz1) (lt_of_le_of_lt hz2 (hr₁₂.trans hr₂))).symm
  have hcomp : IsCompactOperator (rieszProj T z₀ r₁) :=
    isCompactOperator_rieszProj hT hr₁ (by
      have := min_le_right δ (‖z₀‖ / 2); linarith [hr₁₂, hr₂])
      fun z hz => hres z (by rw [hz]; exact hr₁) (by rw [hz]; linarith)
  have hidem : rieszProj T z₀ r₁ * rieszProj T z₀ r₁ = rieszProj T z₀ r₁ :=
    rieszProj_mul_self T (by exact_mod_cast hr₁) (by exact_mod_cast hr₁₂)
      fun z h0 hle => hres z h0 (lt_of_le_of_lt hle hr₂)
  refine ⟨hz₀, ⟨δ', hδ'0, hiso⟩, rieszProj T z₀ r₁, ?_,
    finiteDimensional_range_of_compact_idempotent hcomp hidem⟩
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioc_mem_nhdsGT hr₁] with ε hε
  exact (hconst ε hε.1 hε.2).symm

/-- **Riesz–Schauder: a compact operator on a complex Banach space has a discrete spectrum**
(MT p. 512, (iv)): for every `ε > 0` the spectrum in `|z| ≥ ε` is finite and consists of poles of
finite multiplicity. -/
theorem hasDiscreteSpectrum_of_compact {T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    HasDiscreteSpectrum T := fun ε hε =>
  ⟨finite_spectrum_compact hT hε, fun z hz hzε => isFinitePole_of_compact hT hz fun h => by
    rw [h, norm_zero] at hzε; linarith⟩

/-! ### Proposition 20.1.5 -/

variable {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] in
/-- **Proposition 20.1.5** (MT p. 518): on a countable space, if (DV3) holds for a coercive
`f ≥ 1`, a finite set `C` and `V ≥ 0`, then `P` has a discrete spectrum in `L∞_v`, `v = e^V`
(`P` is a norm limit of the finite-rank truncations, hence compact, and compact operators have a
discrete spectrum). -/
theorem proposition_20_1_5 {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ} {δ b : ℝ}
    {C : Set X} (hδ : 0 < δ) (hV0 : ∀ x, 0 ≤ V x) (hf1 : ∀ x, 1 ≤ f x)
    (hcoer : ∀ n : ℝ, {x | f x ≤ n}.Finite) (hC : C.Finite) (h : DriftDV3 P V f δ b C) :
    HasDiscreteSpectrum (E := BM X) (kOp (fun x => Real.exp (V x)) P) := by
  have := completeSpace_BM (X := X)
  exact hasDiscreteSpectrum_of_compact (proposition_20_1_5_compact hδ hV0 hf1 hcoer hC h).2.2.1

end MeynTweedie.Epilogue
