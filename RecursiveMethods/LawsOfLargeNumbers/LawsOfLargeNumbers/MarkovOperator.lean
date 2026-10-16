/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LawsOfLargeNumbers.TransitionFunctions
import LawsOfLargeNumbers.NormsErgodic

/-!
# The Markov operator on `C(S)`: Exercise 14.4 and Lemma 14.9

SLP §14.2, pp. 425–437. `S` is a metric space with its Borel sets and `C(S) = S →ᵇ ℝ`.

* **Exercise 14.4** (`ex_14_4`, p. 435): under the Feller property (Assumption 14.2) the Markov
  operator `T` is a continuous linear operator on `C(S)` (`markovCLM`), with `‖T‖ = 1` (for
  nonempty `S`), and every constant function is a fixed point.
* `integral_markovCLM_pow`: `∫ Tᵏf dλ = ∫ f d(T*ᵏλ)` (Theorem 8.3, iterated).
* **Assumption 14.3** (`Assumption14_3`, p. 425): the Cesàro averages `(1/N) Σ_{n=1}^N T*ⁿλ₀`
  converge weakly to `λ*` for every `λ₀`. The limit is unique (`assumption14_3_unique`).
* **Lemma 14.9** (`lemma_14_9_of_repr`, p. 427): the averages `(1/M) Σ_{m=1}^M Tᵐf` converge
  uniformly on `S` to the constant `∫ f dλ*`. The proof is the book's, through the Norms Ergodic
  Lemma (`lemma_14_13`). It uses Assumptions 14.2 and 14.3 and that every element of `C(S)*` is
  represented by a signed measure. That is Theorem 14.14 for compact `S`, where Assumption 14.1
  enters; the hypothesis is discharged in `lemma_14_9`.

**Correction (index shift, pp. 436–437).** Assumption 14.3 and Lemma 14.9 use the powers
`1, …, N`, while `Hₙ` uses `0, …, n − 1`. The gaps are closed by
`(1/M) Σ_{m=1}^M Tᵐf = T(H_M f)` and `‖T(H_M f − f̄)‖ ≤ ‖H_M f − f̄‖`, and by an `O(1/n)` bound in
(10).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-! ### Exercise 14.4 -/

theorem abs_markovOpR_le (κ : Kernel S S) [IsMarkovKernel κ] (f : S →ᵇ ℝ) (s : S) :
    |markovOpR κ f s| ≤ ‖f‖ :=
  (theorem_8_1_cor κ f.continuous.measurable fun z => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z).2 s

/-- `Tf` as a bounded continuous function, for a Feller `P`. -/
noncomputable def markovBCF (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    (f : S →ᵇ ℝ) : S →ᵇ ℝ :=
  ofNormedAddCommGroup (markovOpR κ f)
    (hF f f.continuous ⟨‖f‖, fun z => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z⟩)
    ‖f‖ fun s => by rw [Real.norm_eq_abs]; exact abs_markovOpR_le κ f s

theorem markovBCF_apply (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : markovBCF κ hF f s = ∫ s', f s' ∂κ s := rfl

/-- The Markov operator `T` as a linear map on `C(S)`. -/
noncomputable def markovLin (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    (S →ᵇ ℝ) →ₗ[ℝ] (S →ᵇ ℝ) where
  toFun := markovBCF κ hF
  map_add' f g := by
    ext s
    simp only [markovBCF_apply, coe_add, Pi.add_apply]
    exact integral_add (f.integrable _) (g.integrable _)
  map_smul' c f := by
    ext s
    simp only [markovBCF_apply, coe_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

/-- The Markov operator `T` as a continuous linear operator on `C(S)`, `‖T‖ ≤ 1`. -/
noncomputable def markovCLM (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    (S →ᵇ ℝ) →L[ℝ] (S →ᵇ ℝ) :=
  (markovLin κ hF).mkContinuous 1 fun f => by
    rw [one_mul]
    exact norm_ofNormedAddCommGroup_le _ (norm_nonneg f) fun s => by
      rw [Real.norm_eq_abs]; exact abs_markovOpR_le κ f s

theorem markovCLM_apply (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : markovCLM κ hF f s = ∫ s', f s' ∂κ s := rfl

theorem markovCLM_const (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (c : ℝ) :
    markovCLM κ hF (const S c) = const S c := by
  ext s
  rw [markovCLM_apply]
  simp

theorem norm_markovCLM_le (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    ‖markovCLM κ hF‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Exercise 14.4.** Under the Feller property, `T : C(S) → C(S)` is a (continuous) linear
operator, `‖T‖ = 1` for nonempty `S`, and every constant function is a fixed point. -/
theorem ex_14_4 [Nonempty S] (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) :
    (∀ (a b : ℝ) (f g : S →ᵇ ℝ),
      markovCLM κ hF (a • f + b • g) = a • markovCLM κ hF f + b • markovCLM κ hF g) ∧
      ‖markovCLM κ hF‖ = 1 ∧ ∀ c : ℝ, markovCLM κ hF (const S c) = const S c := by
  refine ⟨fun a b f g => by rw [map_add, map_smul, map_smul], le_antisymm
    (norm_markovCLM_le κ hF) ?_, markovCLM_const κ hF⟩
  have h := (markovCLM κ hF).le_opNorm (const S 1)
  rw [markovCLM_const, norm_const_eq, norm_one, mul_one] at h
  exact h

/-! ### Iterates and the adjoint -/

theorem integral_markovCLM (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, markovCLM κ hF f s ∂lam = ∫ s, f s ∂adjointOp κ lam :=
  theorem_8_3_cor κ lam f.continuous.measurable fun z => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z

/-- `∫ Tᵏf dλ = ∫ f d(T*ᵏλ)`. -/
theorem integral_markovCLM_pow (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (k : ℕ)
    (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, (markovCLM κ hF ^ k) f s ∂lam = ∫ s, f s ∂(adjointOp κ)^[k] lam := by
  induction k generalizing lam with
  | zero => rfl
  | succ k ih =>
    have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
    rw [pow_succ', Function.iterate_succ_apply, ← ih (adjointOp κ lam)]
    exact integral_markovCLM κ hF lam _

/-! ### Assumption 14.3 -/

/-- **Assumption 14.3.** For every initial `λ₀`, the Cesàro averages `(1/N) Σ_{n=1}^N T*ⁿλ₀`
converge weakly to the probability measure `λ*`. -/
def Assumption14_3 (κ : Kernel S S) (lstar : Measure S) : Prop :=
  IsProbabilityMeasure lstar ∧ ∀ lam₀ : Measure S, IsProbabilityMeasure lam₀ → ∀ f : S →ᵇ ℝ,
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ∫ s, f s ∂(adjointOp κ)^[n + 1] lam₀)
      atTop (𝓝 (∫ s, f s ∂lstar))

/-- The limit in Assumption 14.3 is unique. -/
theorem assumption14_3_unique [Nonempty S] {κ : Kernel S S} {l₁ l₂ : Measure S}
    (h₁ : Assumption14_3 κ l₁) (h₂ : Assumption14_3 κ l₂) : l₁ = l₂ := by
  have := h₁.1
  have := h₂.1
  have hd : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary S)) := inferInstance
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f =>
    tendsto_nhds_unique (h₁.2 _ hd f) (h₂.2 _ hd f)

/-! ### Lemma 14.9 -/

/-- `∫ Hₙf dλ → ∫ f dλ*` for probability measures `λ` ((10), p. 436), with the index shift. -/
theorem integral_cesaroOp_tendsto (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    {lstar : Measure S} (hA : Assumption14_3 κ lstar) (lam : Measure S) [IsProbabilityMeasure lam]
    (f : S →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, cesaroOp (markovCLM κ hF) n f s ∂lam) atTop
      (𝓝 (∫ s, f s ∂lstar)) := by
  set a : ℕ → ℝ := fun k => ∫ s, f s ∂(adjointOp κ)^[k] lam
  have hprob : ∀ k, IsProbabilityMeasure ((adjointOp κ)^[k] lam) := fun k => by
    induction k with
    | zero => exact inferInstanceAs (IsProbabilityMeasure lam)
    | succ k ih => rw [Function.iterate_succ_apply']; exact (theorem_8_2 κ _).1
  have ha : ∀ k, |a k| ≤ ‖f‖ := fun k => by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_of_norm_le_const (Eventually.of_forall f.norm_coe_le_norm)).trans
      (by simp)
  have hH : ∀ n, ∫ s, cesaroOp (markovCLM κ hF) n f s ∂lam =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k := fun n => by
    rw [cesaroOp_apply]
    simp only [coe_smul, coe_sum, Finset.sum_apply, smul_eq_mul]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => (BoundedContinuousFunction.integrable
      lam _)]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => integral_markovCLM_pow κ hF k lam f)
  simp_rw [hH]
  -- compare with the shifted averages of Assumption 14.3
  have hshift : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a (k + 1) + (n : ℝ)⁻¹ * (a 0 - a n) := fun n => by
    have : ∑ k ∈ Finset.range n, a k = ∑ k ∈ Finset.range n, a (k + 1) + a 0 - a n := by
      have h1 := Finset.sum_range_succ a n
      have h2 := Finset.sum_range_succ' a n
      linarith
    rw [this]
    ring
  simp_rw [hshift]
  have herr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (a 0 - a n)) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, |(n : ℝ)⁻¹ * (a 0 - a n)| ≤ 2 * ‖f‖ * (n : ℝ)⁻¹ := fun n => by
      rw [abs_mul, abs_inv, Nat.abs_cast, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (Nat.cast_nonneg n))
      linarith [abs_sub (a 0) (a n), ha 0, ha n]
    have hlim : Tendsto (fun n : ℕ => 2 * ‖f‖ * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 * ‖f‖)
    exact squeeze_zero_norm (fun n => (Real.norm_eq_abs _).trans_le (hb n)) hlim
  have := (hA.2 lam inferInstance f).add herr
  rw [add_zero] at this
  exact this

/-- `∫ Hₙf dμ → μ(S) ∫ f dλ*` for finite measures `μ`. -/
theorem integral_cesaroOp_tendsto_finite (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    {lstar : Measure S} (hA : Assumption14_3 κ lstar) (μ : Measure S) [IsFiniteMeasure μ]
    (f : S →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, cesaroOp (markovCLM κ hF) n f s ∂μ) atTop
      (𝓝 (∫ s, const S (∫ s, f s ∂lstar) s ∂μ)) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · set c := μ Set.univ
    have hc0 : c ≠ 0 := (Measure.measure_univ_ne_zero).2 hμ.out
    have hct : c ≠ ⊤ := measure_ne_top μ _
    set lam := c⁻¹ • μ
    have : IsProbabilityMeasure lam := ⟨by
      simp [lam, c]⟩
    have hμlam : μ = c • lam := by
      simp only [lam, smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]
    rw [hμlam]
    simp only [integral_smul_measure, const_apply, integral_const, smul_eq_mul,
      measureReal_ennreal_smul_apply, probReal_univ, mul_one]
    exact (integral_cesaroOp_tendsto κ hF hA lam f).const_mul _

/-- **Lemma 14.9** (from the representation of `C(S)*`). Under Assumptions 14.2 and 14.3, if every
continuous linear functional on `C(S)` is `f ↦ ∫ f dμ₁ − ∫ f dμ₂` for finite measures `μ₁`, `μ₂`,
then `(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly on `S`. -/
theorem lemma_14_9_of_repr (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ)
    {lstar : Measure S} (hA : Assumption14_3 κ lstar)
    (hR : ∀ Λ : StrongDual ℝ (S →ᵇ ℝ), ∃ μ₁ μ₂ : Measure S, IsFiniteMeasure μ₁ ∧
      IsFiniteMeasure μ₂ ∧ ∀ f : S →ᵇ ℝ, Λ f = ∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂) (f : S →ᵇ ℝ) :
    Tendsto (fun M : ℕ => ‖(M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM κ hF ^ (m + 1)) f -
      const S (∫ s, f s ∂lstar)‖) atTop (𝓝 0) := by
  set T := markovCLM κ hF
  set fbar := const S (∫ s, f s ∂lstar)
  have hfix : T fbar = fbar := markovCLM_const κ hF _
  have hw : ∀ Λ : StrongDual ℝ (S →ᵇ ℝ),
      Tendsto (fun n => Λ (cesaroOp T n f)) atTop (𝓝 (Λ fbar)) := fun Λ => by
    obtain ⟨μ₁, μ₂, h₁, h₂, hΛ⟩ := hR Λ
    simp_rw [hΛ]
    exact (integral_cesaroOp_tendsto_finite κ hF hA μ₁ f).sub
      (integral_cesaroOp_tendsto_finite κ hF hA μ₂ f)
  have hlim := lemma_14_13 T (norm_markovCLM_le κ hF) hfix hw
  refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hlim
  have heq : (M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (T ^ (m + 1)) f - fbar =
      T (cesaroOp T M f - fbar) := by
    rw [map_sub, hfix, cesaroOp_apply, map_smul, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pow_succ']
    rfl
  rw [heq]
  exact (T.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_markovCLM_le κ hF))

end StokeyLucasPrescott.LawsOfLargeNumbers
