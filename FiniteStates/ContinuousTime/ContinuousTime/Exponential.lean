/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.ADP
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponentials

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.1 (pp. 308–312).

* Example 10.1.1: `u_t = e^{rt}u₀` is the unique solution of `u̇ = ru` from `u₀`.
* Exercise 10.1.1 and **Lemma 10.1.1**: the exponential distribution is memoryless, and a counter
  CDF `G` with `0 < G < 1` on `(0, ∞)` is memoryless only if `G(t) = e^{−θt}` for some `θ > 0`.
* The matrix exponential (10.6): Exercise 10.1.2 (the partial sums are bounded by `e^{‖A‖}`) and
  **Lemma 10.1.2**: (i) conjugation (Exercise 10.1.3), (ii) commuting sums,
  (iii) `e^{mA} = (e^A)^m`, (iv) eigenvalues, (v) `d/dt e^{tA} = Ae^{tA} = e^{tA}A`
  (Exercise 10.1.4), (vi) transposes, (vii) the fundamental theorem of calculus
  (Exercise 10.1.6); Exercise 10.1.5 (`(e^A)⁻¹ = e^{−A}`).
* An eigenvector of `A` with eigenvalue `λ` is an eigenvector of `e^A` with eigenvalue `e^λ`.
  The converse in Lemma 10.1.2 (iv) is false: `e^{2πi} = 1`, so the `1 × 1` matrix `(2πi)` has
  `e^0 = 1` as an eigenvalue of its exponential while `0` is not one of its eigenvalues.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Scalar exponentials (§10.1.1.1) -/

/-- **Example 10.1.1** (p. 309), existence: `t ↦ e^{rt}u₀` solves `u̇ = ru`. -/
theorem hasDerivAt_exp_mul (r u₀ t : ℝ) :
    HasDerivAt (fun t => Real.exp (r * t) * u₀) (r * (Real.exp (r * t) * u₀)) t := by
  have h := ((hasDerivAt_id t).const_mul r).exp.mul_const u₀
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

/-- **Example 10.1.1** (p. 309), uniqueness: a solution of `ẏ = ry` on `[0, ∞)` with `y(0) = u₀`
is `y(t) = e^{rt}u₀`. -/
theorem eq_exp_of_hasDerivAt {r u₀ : ℝ} {y : ℝ → ℝ} (hy0 : y 0 = u₀)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (r * y t) t) {t : ℝ} (ht : 0 ≤ t) :
    y t = Real.exp (r * t) * u₀ := by
  set g : ℝ → ℝ := fun s => y s * Real.exp (-r * s)
  have hg : ∀ s, 0 ≤ s → HasDerivAt g 0 s := fun s hs => by
    have h1 := (hy s hs).mul (((hasDerivAt_id s).const_mul (-r)).exp)
    simp only [id, mul_one] at h1
    exact h1.congr_deriv (by ring)
  have hcont : ContinuousOn g (Icc 0 t) := fun s hs =>
    (hg s hs.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun s hs =>
    (hg s hs.1).hasDerivWithinAt
  have h := hconst t ⟨ht, le_rfl⟩
  simp only [g, mul_zero, Real.exp_zero, mul_one, hy0] at h
  have hpos : Real.exp (-r * t) * Real.exp (r * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc y t = y t * (Real.exp (-r * t) * Real.exp (r * t)) := by rw [hpos, mul_one]
    _ = (y t * Real.exp (-r * t)) * Real.exp (r * t) := by ring
    _ = Real.exp (r * t) * u₀ := by rw [h, mul_comm]

/-! ### The exponential distribution (§10.1.1.2) -/

/-- **Exercise 10.1.1** (p. 310): the counter CDF `G(t) = e^{−θt}` of `Exp(θ)` is memoryless:
`G(s + t) = G(s)G(t)`, so `P{W > s + t | W > s} = G(s + t)/G(s) = G(t)`. -/
theorem exp_memoryless (θ s t : ℝ) :
    Real.exp (-θ * (s + t)) = Real.exp (-θ * s) * Real.exp (-θ * t) ∧
      Real.exp (-θ * (s + t)) / Real.exp (-θ * s) = Real.exp (-θ * t) := by
  have h : Real.exp (-θ * (s + t)) = Real.exp (-θ * s) * Real.exp (-θ * t) := by
    rw [← Real.exp_add]
    ring_nf
  refine ⟨h, ?_⟩
  rw [h, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

/-- Additivity on `(0, ∞)` gives `g(ks) = kg(s)`. -/
theorem add_nsmul_of_additive {g : ℝ → ℝ} (hg : ∀ s > 0, ∀ t > 0, g (s + t) = g s + g t)
    {s : ℝ} (hs : 0 < s) : ∀ k : ℕ, 0 < k → g (k * s) = k * g s := by
  intro k hk
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp
    · have hks : 0 < (k : ℝ) * s := mul_pos (by exact_mod_cast hk') hs
      push_cast
      rw [add_mul, one_mul, hg _ hks _ hs, ih hk', add_mul, one_mul]

/-- **Lemma 10.1.1** (p. 310), (ii) ⇒ (i): if a counter CDF `G` is decreasing, `0 < G < 1` on
`(0, ∞)`, and memoryless (`G(s + t) = G(s)G(t)` for `s, t > 0`), then `G(t) = e^{−θt}` on `(0, ∞)`
for `θ = −ln G(1) > 0`. -/
theorem eq_exp_of_memoryless {G : ℝ → ℝ} (hanti : AntitoneOn G (Ioi 0))
    (hG : ∀ t > 0, 0 < G t ∧ G t < 1) (hmul : ∀ s > 0, ∀ t > 0, G (s + t) = G s * G t) :
    ∃ θ > 0, ∀ t > 0, G t = Real.exp (-θ * t) := by
  set g : ℝ → ℝ := fun t => -Real.log (G t)
  have hgpos : ∀ t > 0, 0 < g t := fun t ht =>
    neg_pos.2 (Real.log_neg (hG t ht).1 (hG t ht).2)
  have hgadd : ∀ s > 0, ∀ t > 0, g (s + t) = g s + g t := fun s hs t ht => by
    simp only [g, hmul s hs t ht, Real.log_mul (hG s hs).1.ne' (hG t ht).1.ne']
    ring
  have hgmono : MonotoneOn g (Ioi 0) := fun s hs t ht hst =>
    neg_le_neg (Real.log_le_log (hG t ht).1 (hanti hs ht hst))
  -- `g(q) = q g(1)` for positive rationals `q = m/n`
  have hrat : ∀ m n : ℕ, 0 < m → 0 < n → g ((m : ℝ) / n) = (m : ℝ) / n * g 1 := by
    intro m n hm hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hq : 0 < (m : ℝ) / n := div_pos (by exact_mod_cast hm) hn'
    have h1 := add_nsmul_of_additive hgadd hq n hn
    rw [mul_div_cancel₀ _ hn'.ne'] at h1
    have h2 := add_nsmul_of_additive hgadd one_pos m hm
    rw [mul_one] at h2
    rw [h2] at h1
    field_simp
    linarith
  have hrat' : ∀ q : ℚ, 0 < q → g q = q * g 1 := by
    intro q hq
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    have h := hrat q.num.toNat q.den (by omega) q.pos
    have hcast : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]]
      exact_mod_cast (Rat.num_div_den q)
    rw [hcast] at h
    exact h
  have g1 := hgpos 1 one_pos
  refine ⟨g 1, g1, fun t ht => ?_⟩
  have hgt : g t = t * g 1 := by
    rcases lt_trichotomy (g t) (t * g 1) with hlt | heq | hgt'
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show g t / g 1 < t by rwa [div_lt_iff₀ g1])
      have hq0 : (0 : ℝ) < q := lt_trans (div_pos (hgpos t ht) g1) hq1
      have := hgmono (show (q : ℝ) ∈ Set.Ioi 0 from hq0) ht hq2.le
      rw [hrat' q (by exact_mod_cast hq0)] at this
      rw [div_lt_iff₀ g1] at hq1
      linarith
    · exact heq
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < g t / g 1 by rwa [lt_div_iff₀ g1])
      have hq0 : (0 : ℝ) < q := ht.trans hq1
      have := hgmono ht (show (q : ℝ) ∈ Set.Ioi 0 from hq0) hq1.le
      rw [hrat' q (by exact_mod_cast hq0)] at this
      rw [lt_div_iff₀ g1] at hq2
      linarith
  have hG' : G t = Real.exp (-(g t)) := by
    simp only [g, neg_neg]
    exact (Real.exp_log (hG t ht).1).symm
  rw [hG', hgt]
  ring_nf

/-- **Lemma 10.1.1** (p. 310), (i) ⇒ (ii): for `θ > 0`, `G(t) = e^{−θt}` is decreasing, lies in
`(0, 1)` for `t > 0`, and is memoryless. -/
theorem exp_counter_properties {θ : ℝ} (hθ : 0 < θ) :
    Antitone (fun t => Real.exp (-θ * t)) ∧ (∀ t > 0, 0 < Real.exp (-θ * t) ∧
      Real.exp (-θ * t) < 1) ∧
      ∀ s t, Real.exp (-θ * (s + t)) = Real.exp (-θ * s) * Real.exp (-θ * t) :=
  ⟨fun s t hst => Real.exp_le_exp.2 (by nlinarith), fun t ht =>
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by nlinarith)⟩, fun s t => (exp_memoryless θ s t).1⟩

/-! ### The matrix exponential (§10.1.1.3) -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `‖I‖ ≤ 1` in the operator norm. -/
theorem norm_one_le : ‖(1 : Matrix X X ℝ)‖ ≤ 1 :=
  norm_le_of_rowsum_abs_le _ zero_le_one fun i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply_ne' hj]) (by simp)]
    simp

/-- `‖Aᵏ‖ ≤ ‖A‖ᵏ`. -/
theorem norm_pow_le_pow (A : Matrix X X ℝ) (k : ℕ) : ‖A ^ k‖ ≤ ‖A‖ ^ k := by
  induction k with
  | zero => simpa using norm_one_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- **Exercise 10.1.2** (p. 311): the partial sums of (10.6) are bounded:
`‖∑_{k<m} Aᵏ/k!‖ ≤ e^{‖A‖}`. -/
theorem norm_partialSum_exp_le (A : Matrix X X ℝ) (m : ℕ) :
    ‖∑ k ∈ range m, ((k.factorial : ℝ)⁻¹) • A ^ k‖ ≤ Real.exp ‖A‖ := by
  refine (norm_sum_le _ _).trans ((sum_le_sum fun k _ => ?_).trans
    (Real.sum_le_exp_of_nonneg (norm_nonneg A) m))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le_pow A k) (by positivity)

/-- **Lemma 10.1.2 (i)** and **Exercise 10.1.3** (pp. 311–312): if `A = PDP⁻¹` then
`e^A = Pe^DP⁻¹`. -/
theorem exp_conj_eq {P D : Matrix X X ℝ} (hP : IsUnit P) :
    NormedSpace.exp (P * D * P⁻¹) = P * NormedSpace.exp D * P⁻¹ :=
  Matrix.exp_conj P D hP

/-- **Lemma 10.1.2 (ii)** (p. 311): commuting matrices have `e^{A+B} = e^Ae^B`. -/
theorem exp_add_eq {A B : Matrix X X ℝ} (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B :=
  Matrix.exp_add_of_commute A B h

/-- **Lemma 10.1.2 (iii)** (p. 311): `e^{mA} = (e^A)^m`. -/
theorem exp_natCast_smul (m : ℕ) (A : Matrix X X ℝ) :
    NormedSpace.exp ((m : ℝ) • A) = NormedSpace.exp A ^ m := by
  rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]

/-- **Lemma 10.1.2 (v)** and **Exercise 10.1.4** (pp. 311–312): `d/dt e^{tA} = e^{tA}A`. -/
theorem hasDerivAt_exp_smul (A : Matrix X X ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (NormedSpace.exp (t • A) * A) t :=
  hasDerivAt_exp_smul_const A t

/-- **Lemma 10.1.2 (v)** (p. 311): `d/dt e^{tA} = Ae^{tA}`. -/
theorem hasDerivAt_exp_smul' (A : Matrix X X ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (A * NormedSpace.exp (t • A)) t :=
  hasDerivAt_exp_smul_const' A t

/-- `e^{tA}` commutes with `A`. -/
theorem exp_smul_mul_comm (A : Matrix X X ℝ) (t : ℝ) :
    NormedSpace.exp (t • A) * A = A * NormedSpace.exp (t • A) :=
  (hasDerivAt_exp_smul A t).unique (hasDerivAt_exp_smul' A t)

/-- **Lemma 10.1.2 (vi)** (p. 311): `e^{Aᵀ} = (e^A)ᵀ`. -/
theorem exp_transpose_eq (A : Matrix X X ℝ) :
    NormedSpace.exp Aᵀ = (NormedSpace.exp A)ᵀ :=
  Matrix.exp_transpose A

/-- `t ↦ e^{tA}` is continuous. -/
theorem continuous_exp_smul (A : Matrix X X ℝ) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul A t).continuousAt

/-- **Lemma 10.1.2 (vii)** and **Exercise 10.1.6** (pp. 311–312):
`e^{tA} − e^{sA} = ∫_s^t e^{τA}A dτ`. -/
theorem exp_smul_sub_eq_integral (A : Matrix X X ℝ) (s t : ℝ) :
    NormedSpace.exp (t • A) - NormedSpace.exp (s • A) =
      ∫ τ in s..t, NormedSpace.exp (τ • A) * A := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hasDerivAt_exp_smul A τ)
    ?_).symm
  exact ((continuous_exp_smul A).mul continuous_const).intervalIntegrable _ _

/-- **Exercise 10.1.5** (p. 312): `e^A` is invertible with inverse `e^{−A}`. -/
theorem exp_mul_exp_neg (A : Matrix X X ℝ) :
    IsUnit (NormedSpace.exp A) ∧ NormedSpace.exp A * NormedSpace.exp (-A) = 1 ∧
      NormedSpace.exp (-A) = (NormedSpace.exp A)⁻¹ := by
  refine ⟨Matrix.isUnit_exp A, ?_, Matrix.exp_neg A⟩
  rw [← Matrix.exp_add_of_commute A (-A) (Commute.neg_right (Commute.refl A)), add_neg_cancel,
    NormedSpace.exp_zero]

/-! ### Eigenvectors and the exponential -/

/-- If `Aw = cw` then `e^A w = e^c w`, over `ℝ` or `ℂ`. -/
theorem exp_mulVec_of_eigen {𝕂 : Type*} [RCLike 𝕂] {A : Matrix X X 𝕂} {w : X → 𝕂} {c : 𝕂}
    (h : A *ᵥ w = c • w) : NormedSpace.exp A *ᵥ w = NormedSpace.exp c • w := by
  have : CompleteSpace (Matrix X X 𝕂) := FiniteDimensional.complete 𝕂 _
  have hpow : ∀ n : ℕ, A ^ n *ᵥ w = c ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul,
        pow_succ]
  let L : Matrix X X 𝕂 →L[𝕂] (X → 𝕂) := LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ w
      map_add' := fun M N => Matrix.add_mulVec M N w
      map_smul' := fun a M => Matrix.smul_mulVec a M w }
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) A).mapL L
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) c).smul_const w
  refine h1.unique ?_
  convert h2 using 1
  funext n
  change ((n.factorial⁻¹ : 𝕂) • A ^ n) *ᵥ w = ((n.factorial⁻¹ : 𝕂) • c ^ n) • w
  rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]

/-- **Lemma 10.1.2 (iv)** (p. 311), forward direction for a real eigenpair: if `Aw = λw` then
`e^A w = e^λ w`. -/
theorem exp_mulVec_of_eigen_real {A : Matrix X X ℝ} {w : X → ℝ} {c : ℝ} (h : A *ᵥ w = c • w) :
    NormedSpace.exp A *ᵥ w = Real.exp c • w := by
  rw [Real.exp_eq_exp_ℝ]
  exact exp_mulVec_of_eigen h

omit [Fintype X] [DecidableEq X] in
/-- **Lemma 10.1.2 (iv)** (p. 311), converse refuted: for the `1 × 1` matrix `B = (2πi)`, `e^0 = 1`
is an eigenvalue of `e^B = I` but `0` is not an eigenvalue of `B`. -/
theorem exp_eigenvalue_converse_false :
    ∃ B : Matrix (Fin 1) (Fin 1) ℂ, Complex.exp 0 ∈ spectrum ℂ (NormedSpace.exp B) ∧
      (0 : ℂ) ∉ spectrum ℂ B := by
  have : CompleteSpace (Matrix (Fin 1) (Fin 1) ℂ) := FiniteDimensional.complete ℂ _
  refine ⟨algebraMap ℂ _ (2 * Real.pi * Complex.I), ?_, ?_⟩
  · rw [show NormedSpace.exp (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (2 * Real.pi * Complex.I)) =
        algebraMap ℂ _ (NormedSpace.exp (2 * Real.pi * Complex.I)) from
        (NormedSpace.algebraMap_exp_comm _).symm, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I,
      Complex.exp_zero, spectrum.scalar_eq]
    exact Set.mem_singleton 1
  · rw [spectrum.scalar_eq, Set.mem_singleton_iff]
    exact (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero).symm

end SargentStachurski.ContinuousTime
