/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.Flows
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Basic.Real.Pointwise

/-!
# The spectral bound and stability of exponential flows

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.2.3–§10.1.2.4 (pp. 314–317).

The spectral bound (10.16) is `s(A) = max_{λ ∈ σ(A)} Re λ`, over the complex eigenvalues of `A`.

* The spectral mapping theorem for the exponential: `σ(e^A) = e^{σ(A)}`. One inclusion is
  Mathlib's `spectrum.exp_mem_exp`; for the other, an eigenvalue `μ` of `e^A` has an eigenspace
  invariant under `A` (which commutes with `e^A`), and an eigenvector `w` of `A` in it gives
  `μw = e^A w = e^λ w`. With it, the converse of Lemma 10.1.2 (iv) fails for a real matrix:
  `e^0` is an eigenvalue of `e^A` for `A = (0, −2π; 2π, 0)`, while `0` is not an eigenvalue of `A`.
* **Lemma 10.1.4**: `τs(A) = s(τA)` for `τ > 0` (Exercise 10.1.9), `e^{s(A)} = ρ(e^A)`
  (Exercise 10.1.10), and `s(A) = lim_k (1/k) ln ‖e^{kA}‖` over `k ∈ ℕ` (Exercise 10.1.11).
* **Theorem 10.1.5**: (i) `s(A) < 0`, (ii) `‖e^{tA}‖ → 0`, (iii) `‖e^{tA}‖ ≤ Me^{−ωt}` and
  (iv) `∫₀^∞ ‖e^{tA}u₀‖^p dt < ∞` for all `p ≥ 1` and `u₀` are equivalent. The book cites Engel and
  Nagel for the proof and asks for (i) ⇒ (ii) and (iii) ⇒ (iv) (Exercise 10.1.12). For
  (iv) ⇒ (i), an eigenvalue `λ` with `Re λ ≥ 0` and eigenvector `a + ib` give
  `‖e^{tA}a‖ + ‖e^{tA}b‖ ≥ c > 0` for all `t ≥ 0`.
-/

open Finset Matrix Filter Topology Function Set MeasureTheory
open scoped Pointwise

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `complexify` commutes with the exponential. -/
theorem complexify_exp (A : Matrix X X ℝ) :
    complexify (NormedSpace.exp A) = NormedSpace.exp (complexify A) :=
  NormedSpace.map_exp (Complex.ofRealHom.mapMatrix (m := X))
    (Continuous.matrix_map continuous_id Complex.continuous_ofReal) A

omit [Fintype X] [DecidableEq X] in
/-- `complexify (tA) = t · complexify A`. -/
theorem complexify_smul (t : ℝ) (A : Matrix X X ℝ) :
    complexify (t • A) = (t : ℂ) • complexify A := by
  ext i j
  simp [complexify_apply]

/-- The spectral mapping theorem for the exponential: `σ(e^A) = e^{σ(A)}`. -/
theorem spectrum_complexify_exp (A : Matrix X X ℝ) :
    spectrum ℂ (complexify (NormedSpace.exp A)) = Complex.exp '' spectrum ℂ (complexify A) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  set B := complexify A
  rw [complexify_exp]
  ext μ
  constructor
  · intro hμ
    -- `μ` is an eigenvalue of `e^B`; its eigenspace is invariant under `B`
    have hμ' : μ ∈ spectrum ℂ (complexify (NormedSpace.exp A)) := by rwa [complexify_exp]
    obtain ⟨e, he, hee⟩ := (mem_spectrum_iff_eigenpair (NormedSpace.exp A) μ).1 hμ'
    rw [complexify_exp] at hee
    set E : Submodule ℂ (X → ℂ) :=
      LinearMap.ker (Matrix.toLin' (NormedSpace.exp B) - μ • LinearMap.id)
    have hmemE : ∀ v, v ∈ E ↔ NormedSpace.exp B *ᵥ v = μ • v := fun v => by
      simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hcomm : NormedSpace.exp B * B = B * NormedSpace.exp B :=
      ((Commute.refl B).exp_left).eq
    have hinv : ∀ v ∈ E, Matrix.toLin' B v ∈ E := fun v hv => by
      rw [hmemE] at hv ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_smul]
    let g : Module.End ℂ E := (Matrix.toLin' B).restrict hinv
    have hne : Nontrivial E := ⟨⟨⟨e, (hmemE e).2 hee⟩, 0, fun h => he (congrArg Subtype.val h)⟩⟩
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw0 : (w : X → ℂ) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hBw : B *ᵥ (w : X → ℂ) = c • (w : X → ℂ) := by
      have := congrArg Subtype.val hw.apply_eq_smul
      simpa [g, LinearMap.restrict_apply, Matrix.toLin'_apply] using this
    have hexp1 := exp_mulVec_of_eigen hBw
    have hexp2 := (hmemE w).1 w.2
    rw [hexp1] at hexp2
    have hμc : μ = NormedSpace.exp c := by
      by_contra hne'
      have h0 : (NormedSpace.exp c - μ) • (w : X → ℂ) = 0 := by rw [sub_smul, hexp2, sub_self]
      rcases smul_eq_zero.1 h0 with h | h
      · exact hne' (sub_eq_zero.1 h).symm
      · exact hw0 h
    refine ⟨c, (mem_spectrum_iff_eigenpair A c).2 ⟨w, hw0, hBw⟩, ?_⟩
    rw [hμc, Complex.exp_eq_exp_ℂ]
  · rintro ⟨c, hc, rfl⟩
    rw [Complex.exp_eq_exp_ℂ]
    exact spectrum.exp_mem_exp B hc

/-- The spectral bound (10.16): `s(A) = max_{λ ∈ σ(A)} Re λ`. -/
noncomputable def spectralBound (A : Matrix X X ℝ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ (complexify A))

/-- **Lemma 10.1.2 (iv)** (p. 311), converse refuted for a real matrix: for the rotation generator
`A = (0, −2π; 2π, 0)`, `e^0 = 1` is an eigenvalue of `e^A` (since `2πi` is an eigenvalue of `A`),
but `0` is not an eigenvalue of `A`. -/
theorem exp_eigenvalue_converse_false_real :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, Complex.exp 0 ∈ spectrum ℂ (complexify (NormedSpace.exp A)) ∧
      (0 : ℂ) ∉ spectrum ℂ (complexify A) := by
  refine ⟨!![0, -(2 * Real.pi); 2 * Real.pi, 0], ?_, ?_⟩
  · rw [spectrum_complexify_exp]
    refine ⟨2 * Real.pi * Complex.I, ?_, by rw [Complex.exp_zero, Complex.exp_two_pi_mul_I]⟩
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      Matrix.det_fin_two]
    simp [complexify_apply, Algebra.algebraMap_eq_smul_one]
    ring_nf
    simp [Complex.I_sq]
  · rw [spectrum.mem_iff, not_not, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_fin_two]
    simp [complexify_apply, Real.pi_ne_zero]

variable [Nonempty X]

theorem spectrum_nonempty (A : Matrix X X ℝ) : (spectrum ℂ (complexify A)).Nonempty := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  exact spectrum.nonempty _

omit [Nonempty X] in
theorem re_spectrum_finite (A : Matrix X X ℝ) : (Complex.re '' spectrum ℂ (complexify A)).Finite :=
  (Matrix.finite_spectrum _).image _

omit [Nonempty X] in
/-- `Re λ ≤ s(A)` for every eigenvalue `λ`. -/
theorem re_le_spectralBound {A : Matrix X X ℝ} {c : ℂ} (hc : c ∈ spectrum ℂ (complexify A)) :
    c.re ≤ spectralBound A :=
  le_csSup (re_spectrum_finite A).bddAbove ⟨c, hc, rfl⟩

/-- `s(A)` is attained. -/
theorem exists_re_eq_spectralBound (A : Matrix X X ℝ) :
    ∃ c ∈ spectrum ℂ (complexify A), c.re = spectralBound A :=
  ((spectrum_nonempty A).image _).csSup_mem (re_spectrum_finite A)

/-- **Lemma 10.1.4** and **Exercise 10.1.10** (p. 316): `e^{s(A)} = ρ(e^A)`. -/
theorem specRad_exp (A : Matrix X X ℝ) :
    specRad (NormedSpace.exp A) = Real.exp (spectralBound A) := by
  have hnn : ∀ z : ℂ, ((‖z‖₊ : NNReal) : ENNReal) = ENNReal.ofReal ‖z‖ := fun z => by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  have hsr : spectralRadius ℂ (complexify (NormedSpace.exp A)) =
      ENNReal.ofReal (Real.exp (spectralBound A)) := by
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
    · rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, spectrum_complexify_exp] at hμ
      rcases hμ with ⟨c, hc, rfl⟩ | hμ0
      swap
      · rw [Set.mem_singleton_iff] at hμ0
        rw [hμ0, nnnorm_zero, ENNReal.coe_zero]
        exact bot_le
      rw [hnn, Complex.norm_exp]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (re_le_spectralBound hc))
    · obtain ⟨c, hc, hre⟩ := exists_re_eq_spectralBound A
      have hmem : Complex.exp c ∈ spectrum ℂ (complexify (NormedSpace.exp A)) := by
        rw [spectrum_complexify_exp]
        exact ⟨c, hc, rfl⟩
      have := le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ (complexify (NormedSpace.exp A))) =>
        ((‖k‖₊ : NNReal) : ENNReal)) _ (spectrum_subset_quasispectrum ℂ _ hmem)
      rw [hnn, Complex.norm_exp, hre] at this
      exact this
  unfold specRad
  rw [hsr, ENNReal.toReal_ofReal (Real.exp_pos _).le]

omit [Nonempty X] in
/-- **Lemma 10.1.4** and **Exercise 10.1.9** (p. 316): `τs(A) = s(τA)` for `τ > 0`. -/
theorem spectralBound_smul [Nonempty X] {τ : ℝ} (hτ : 0 < τ) (A : Matrix X X ℝ) :
    τ * spectralBound A = spectralBound (τ • A) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  unfold spectralBound
  rw [complexify_smul, spectrum.smul_eq_smul _ _ (spectrum_nonempty A)]
  have himg : Complex.re '' ((τ : ℂ) • spectrum ℂ (complexify A)) =
      τ • (Complex.re '' spectrum ℂ (complexify A)) := by
    ext r
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c.re, ⟨c, hc, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨τ * c, ⟨c, hc, rfl⟩, by simp⟩
  rw [himg, Real.sSup_smul_of_nonneg hτ.le, smul_eq_mul]

/-- `e^{kA}` is invertible, so its norm is positive. -/
theorem norm_exp_pos (A : Matrix X X ℝ) : 0 < ‖NormedSpace.exp A‖ := by
  refine norm_pos_iff.2 fun h => ?_
  have h1 := (exp_mul_exp_neg A).2.1
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- **Lemma 10.1.4** and **Exercise 10.1.11** (p. 316): `s(A) = lim_{k → ∞} (1/k) ln ‖e^{kA}‖`,
the limit over `k ∈ ℕ`. -/
theorem tendsto_log_norm_exp (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ => (1 / (k : ℝ)) * Real.log ‖NormedSpace.exp ((k : ℝ) • A)‖) atTop
      (𝓝 (spectralBound A)) := by
  have h := tendsto_norm_pow_rpow (NormedSpace.exp A)
  rw [specRad_exp] at h
  have hlog := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp h
  rw [Real.log_exp] at hlog
  refine hlog.congr fun k => ?_
  simp only [Function.comp, exp_natCast_smul]
  have hpos : 0 < ‖NormedSpace.exp A ^ k‖ := by
    rw [← exp_natCast_smul]
    exact norm_exp_pos _
  rw [Real.log_rpow hpos]

omit [Nonempty X] in
/-- `e^{tA} = e^{sA}e^{tA}` for commuting multiples. -/
theorem exp_smul_add (A : Matrix X X ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s |>.smul_right t)

/-- Theorem 10.1.5 (i) ⇒ (iii): if `s(A) < 0` then `‖e^{tA}‖ ≤ Me^{−ωt}` for some `M, ω > 0`. -/
theorem exists_exp_bound {A : Matrix X X ℝ} (hs : spectralBound A < 0) :
    ∃ M ω : ℝ, 0 < M ∧ 0 < ω ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ M * Real.exp (-ω * t) := by
  have hρ : specRad (NormedSpace.exp A) < 1 := by
    rw [specRad_exp]
    exact Real.exp_lt_one_iff.2 hs
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 < r := (specRad_nonneg _).trans_lt hr1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_norm_pow_le (NormedSpace.exp A) hr1)
  set C : ℝ := ∑ k ∈ range K, ‖NormedSpace.exp A ^ k‖ / r ^ k + 1
  have hC1 : 1 ≤ C := le_add_of_nonneg_left (sum_nonneg fun k _ => by positivity)
  have hCk : ∀ k : ℕ, ‖NormedSpace.exp A ^ k‖ ≤ C * r ^ k := by
    intro k
    by_cases hk : k < K
    · have h1 : ‖NormedSpace.exp A ^ k‖ / r ^ k ≤ C :=
        (single_le_sum (f := fun k => ‖NormedSpace.exp A ^ k‖ / r ^ k)
          (fun k _ => by positivity) (mem_range.2 hk)).trans (le_add_of_nonneg_right zero_le_one)
      rwa [div_le_iff₀ (by positivity)] at h1
    · exact (hK k (not_lt.1 hk)).trans (le_mul_of_one_le_left (by positivity) hC1)
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr2
  refine ⟨C * Real.exp ‖A‖ / r, -Real.log r, by positivity, by linarith, fun t ht => ?_⟩
  set k := ⌊t⌋₊
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht
  have htk : t < k + 1 := Nat.lt_floor_add_one t
  have hsplit : NormedSpace.exp (t • A) =
      NormedSpace.exp ((k : ℝ) • A) * NormedSpace.exp ((t - k) • A) := by
    rw [← exp_smul_add]
    congr 2
    ring
  have hf : ‖NormedSpace.exp ((t - k) • A)‖ ≤ Real.exp ‖A‖ := by
    refine (norm_exp_le _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hrk : r ^ k ≤ Real.exp (-(-Real.log r) * t) / r := by
    rw [neg_neg, le_div_iff₀ hr0, ← pow_succ, ← Real.rpow_natCast,
      Real.rpow_def_of_pos hr0, Real.exp_le_exp, mul_comm (Real.log r) t]
    push_cast
    nlinarith
  calc ‖NormedSpace.exp (t • A)‖ ≤ ‖NormedSpace.exp ((k : ℝ) • A)‖ *
        ‖NormedSpace.exp ((t - k) • A)‖ := by rw [hsplit]; exact norm_mul_le _ _
    _ ≤ (C * r ^ k) * Real.exp ‖A‖ := by
        rw [exp_natCast_smul]
        exact mul_le_mul (hCk k) hf (norm_nonneg _) (by positivity)
    _ ≤ (C * (Real.exp (-(-Real.log r) * t) / r)) * Real.exp ‖A‖ := by
        gcongr
    _ = C * Real.exp ‖A‖ / r * Real.exp (-(-Real.log r) * t) := by ring

/-- **Theorem 10.1.5** (p. 316): for any square matrix `A`, the following are equivalent:
(i) `s(A) < 0`; (ii) `‖e^{tA}‖ → 0` as `t → ∞`; (iii) `‖e^{tA}‖ ≤ Me^{−ωt}` for some `M, ω > 0`;
(iv) `∫₀^∞ ‖e^{tA}u₀‖^p dt < ∞` for every `p ≥ 1` and `u₀`. -/
theorem stability_tfae (A : Matrix X X ℝ) :
    [spectralBound A < 0,
      Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖) atTop (𝓝 0),
      ∃ M ω : ℝ, 0 < M ∧ 0 < ω ∧ ∀ t : ℝ, 0 ≤ t →
        ‖NormedSpace.exp (t • A)‖ ≤ M * Real.exp (-ω * t),
      ∀ p : ℝ, 1 ≤ p → ∀ u₀ : X → ℝ,
        IntegrableOn (fun t : ℝ => ‖NormedSpace.exp (t • A) *ᵥ u₀‖ ^ p) (Ioi 0)].TFAE := by
  tfae_have 1 → 3 := exists_exp_bound
  tfae_have 3 → 2 := by
    rintro ⟨M, ω, hM, hω, hb⟩
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop 0).mono fun t ht => hb t ht) ?_
    have : Tendsto (fun t : ℝ => Real.exp (-ω * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using this.const_mul M
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨T, hT⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    set K : ℕ := ⌈T⌉₊ + 1
    have hK : (0 : ℝ) < K := by positivity
    have hKT : T ≤ K := (Nat.le_ceil T).trans (by simp [K])
    have h1 : Real.exp (spectralBound ((K : ℝ) • A)) < 1 := by
      rw [← specRad_exp]
      exact (specRad_le_norm _).trans_lt (hT K hKT)
    rw [← spectralBound_smul hK] at h1
    have := Real.exp_lt_one_iff.1 h1
    by_contra hge
    exact absurd this (not_lt.2 (mul_nonneg hK.le (not_lt.1 hge)))
  tfae_have 3 → 4 := by
    rintro ⟨M, ω, hM, hω, hb⟩ p hp u₀
    have hp0 : 0 ≤ p := by linarith
    have hint : IntegrableOn (fun t : ℝ => (M * ‖u₀‖) ^ p * Real.exp (-(p * ω) * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul _
    refine hint.mono' ?_ ?_
    · exact (((continuous_exp_smul A).matrix_mulVec continuous_const).norm.rpow_const
        fun _ => Or.inr hp0).aestronglyMeasurable.restrict
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖NormedSpace.exp (t • A) *ᵥ u₀‖ ^ p ≤ (M * Real.exp (-ω * t) * ‖u₀‖) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul_of_nonneg_right (hb t ht0) (norm_nonneg _))) hp0
        _ = (M * ‖u₀‖) ^ p * Real.exp (-(p * ω) * t) := by
            rw [show M * Real.exp (-ω * t) * ‖u₀‖ = (M * ‖u₀‖) * Real.exp (-ω * t) by ring,
              Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul]
            congr 2
            ring
  tfae_have 4 → 1 := by
    intro hint
    by_contra hge
    push Not at hge
    obtain ⟨c, hc, hre⟩ := exists_re_eq_spectralBound A
    obtain ⟨e, he, hee⟩ := (mem_spectrum_iff_eigenpair A c).1 hc
    obtain ⟨x0, hx0⟩ : ∃ x0, e x0 ≠ 0 := by
      by_contra h
      push Not at h
      exact he (funext h)
    set a : X → ℝ := fun x => (e x).re
    set b : X → ℝ := fun x => (e x).im
    -- `complexify M *ᵥ e = Ma + i Mb`
    have hsplit : ∀ M : Matrix X X ℝ, ∀ x, (complexify M *ᵥ e) x =
        ((M *ᵥ a) x : ℂ) + ((M *ᵥ b) x : ℂ) * Complex.I := by
      intro M x
      simp only [mulVec, dotProduct, complexify_apply, a, b]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← Complex.re_add_im (e j)]
      ring
    have hlow : ∀ t : ℝ, 0 ≤ t →
        ‖e x0‖ ≤ ‖NormedSpace.exp (t • A) *ᵥ a‖ + ‖NormedSpace.exp (t • A) *ᵥ b‖ := by
      intro t ht
      have he1 : complexify (t • A) *ᵥ e = ((t : ℂ) * c) • e := by
        rw [complexify_smul, Matrix.smul_mulVec, hee, smul_smul]
      have he2 := exp_mulVec_of_eigen he1
      rw [← complexify_exp] at he2
      have hx := congrFun he2 x0
      rw [hsplit, Pi.smul_apply, smul_eq_mul] at hx
      have hnorm : ‖NormedSpace.exp ((t : ℂ) * c) * e x0‖ = Real.exp (t * c.re) * ‖e x0‖ := by
        rw [norm_mul, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
        simp
      have h1 : ‖e x0‖ ≤ ‖NormedSpace.exp ((t : ℂ) * c) * e x0‖ := by
        rw [hnorm]
        exact le_mul_of_one_le_left (norm_nonneg _)
          (Real.one_le_exp (mul_nonneg ht (hre ▸ hge)))
      rw [← hx] at h1
      refine h1.trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      · rw [Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ x0
      · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ x0
    have ha := hint 1 le_rfl a
    have hb := hint 1 le_rfl b
    simp only [Real.rpow_one] at ha hb
    have hsum := ha.add hb
    have hconst : IntegrableOn (fun _ : ℝ => ‖e x0‖) (Ioi 0) := by
      refine hsum.mono' (by fun_prop) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hlow t (le_of_lt ht)
    rw [integrableOn_const_iff, Real.volume_Ioi] at hconst
    rcases hconst with h | h
    · exact hx0 (by simpa using h)
    · exact absurd h (lt_irrefl _)
  tfae_finish

end SargentStachurski.ContinuousTime
