/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.ConditionM

/-!
# Cesàro averages of `T*ⁿλ`

The averages `(1/N) Σ_{n=1}^{N} T*ⁿλ` of Theorem 11.9b (`cesaroM κ n μ`, with `N = n + 1`), and the
property that they are uniformly Cauchy on sets (`CesaroCauchy`), which for probability measures
is Cauchy-ness in the total variation norm (`tvDist_cesaro_le`). The class of measures with this
property is closed under sums and scalar multiples, invariant under `T*` (`cesaroCauchy_adjoint`),
and closed under perturbations of small mass after any number of steps (`cesaroCauchy_of_approx`).
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-! ### Linearity of `T*` -/

theorem adjointOp_add (η : Kernel S S) (μ ν : Measure S) :
    adjointOp η (μ + ν) = adjointOp η μ + adjointOp η ν := by
  ext A hA
  simp [adjointOp_apply η _ hA, lintegral_add_measure]

theorem adjointOp_smul (η : Kernel S S) (c : ℝ≥0∞) (μ : Measure S) :
    adjointOp η (c • μ) = c • adjointOp η μ := by
  ext A hA
  simp [adjointOp_apply η _ hA, lintegral_smul_measure]

theorem adjointOp_zero (η : Kernel S S) : adjointOp η (0 : Measure S) = 0 := by
  ext A hA; simp [adjointOp_apply η _ hA]

theorem adjointOp_finsetSum (η : Kernel S S) {ι : Type*} (s : Finset ι) (μ : ι → Measure S) :
    adjointOp η (∑ i ∈ s, μ i) = ∑ i ∈ s, adjointOp η (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adjointOp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adjointOp_add, ih]

theorem adjointOp_mono (η : Kernel S S) {μ ν : Measure S} (h : μ ≤ ν) :
    adjointOp η μ ≤ adjointOp η ν := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [adjointOp_apply η _ hA, adjointOp_apply η _ hA]
  exact lintegral_mono' h le_rfl

variable {κ : Kernel S S} [IsMarkovKernel κ]

theorem adjointOp_kpow_univ (k : ℕ) (μ : Measure S) :
    adjointOp (kpow κ k) μ univ = μ univ := by
  have := isMarkov_kpow (κ := κ) k
  rw [adjointOp_apply _ _ MeasurableSet.univ]; simp

theorem isFinite_adjoint (k : ℕ) (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (adjointOp (kpow κ k) μ) :=
  ⟨by rw [adjointOp_kpow_univ]; exact measure_lt_top μ univ⟩

theorem adjoint_real_le (k : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    (adjointOp (kpow κ k) μ).real A ≤ μ.real univ := by
  have := isFinite_adjoint (κ := κ) k μ
  calc (adjointOp (kpow κ k) μ).real A ≤ (adjointOp (kpow κ k) μ).real univ :=
        measureReal_mono (subset_univ A)
    _ = μ.real univ := by rw [measureReal_def, adjointOp_kpow_univ]; rfl

/-! ### Cesàro averages -/

variable (κ) in
/-- The Cesàro average `(1/(n+1)) Σ_{k=1}^{n+1} T*ᵏλ` (Theorem 11.9b, with `N = n + 1`). -/
noncomputable def cesaroM (n : ℕ) (μ : Measure S) : Measure S :=
  ((n : ℝ≥0∞) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), adjointOp (kpow κ (k + 1)) μ

omit [IsMarkovKernel κ] in
theorem cesaroM_apply (n : ℕ) (μ : Measure S) (A : Set S) :
    cesaroM κ n μ A =
      ((n : ℝ≥0∞) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), adjointOp (kpow κ (k + 1)) μ A := by
  simp [cesaroM, Measure.coe_finsetSum, Finset.sum_apply]

theorem cesaroM_real (n : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    (cesaroM κ n μ).real A =
      ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A := by
  rw [measureReal_def, cesaroM_apply, ENNReal.toReal_mul, ENNReal.toReal_sum fun k _ => by
    have := isFinite_adjoint (κ := κ) (k + 1) μ; exact measure_ne_top _ _]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top]
  simp

theorem cesaroM_univ (n : ℕ) (μ : Measure S) : cesaroM κ n μ univ = μ univ := by
  rw [cesaroM_apply]
  simp only [adjointOp_kpow_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, Nat.cast_add, Nat.cast_one,
    ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]

theorem isFinite_cesaroM (n : ℕ) (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (cesaroM κ n μ) := ⟨by rw [cesaroM_univ]; exact measure_lt_top μ univ⟩

theorem isProb_cesaroM (n : ℕ) (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (cesaroM κ n μ) := ⟨by rw [cesaroM_univ]; exact measure_univ⟩

theorem cesaroM_real_nonneg_le (n : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    0 ≤ (cesaroM κ n μ).real A ∧ (cesaroM κ n μ).real A ≤ μ.real univ := by
  have := isFinite_cesaroM (κ := κ) n μ
  refine ⟨measureReal_nonneg, (measureReal_mono (subset_univ A)).trans ?_⟩
  rw [measureReal_def, cesaroM_univ]; rfl

omit [IsMarkovKernel κ] in
theorem cesaroM_add (n : ℕ) (μ ν : Measure S) :
    cesaroM κ n (μ + ν) = cesaroM κ n μ + cesaroM κ n ν := by
  simp only [cesaroM, adjointOp_add, Finset.sum_add_distrib, smul_add]

omit [IsMarkovKernel κ] in
theorem cesaroM_smul (n : ℕ) (c : ℝ≥0∞) (μ : Measure S) :
    cesaroM κ n (c • μ) = c • cesaroM κ n μ := by
  simp only [cesaroM, adjointOp_smul, ← Finset.smul_sum, smul_comm c]

/-- Shifting the starting measure by `r` steps moves the averages by at most `r λ(S)/(n+1)`. -/
theorem abs_cesaro_shift_le (n r : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    |(cesaroM κ n (adjointOp (kpow κ r) μ)).real A - (cesaroM κ n μ).real A| ≤
      r * μ.real univ / ((n : ℝ) + 1) := by
  have := isFinite_adjoint (κ := κ) r μ
  set a : ℕ → ℝ := fun k => (adjointOp (kpow κ k) μ).real A
  have ha : ∀ k, 0 ≤ a k ∧ a k ≤ μ.real univ := fun k => ⟨measureReal_nonneg,
    adjoint_real_le k μ A⟩
  have hshift : ∀ k, (adjointOp (kpow κ (k + 1)) (adjointOp (kpow κ r) μ)).real A =
      a (k + 1 + r) := fun k => by rw [← adjoint_add]
  rw [cesaroM_real, cesaroM_real, Finset.sum_congr rfl (fun k _ => hshift k)]
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity), ← Finset.sum_sub_distrib]
  -- `Σ_{k≤n} (a(k+1+r) − a(k+1)) = Σ_{k<r} (a(n+2+k) − a(k+1))`
  have hsum : ∑ k ∈ Finset.range (n + 1), (a (k + 1 + r) - a (k + 1)) =
      ∑ k ∈ Finset.range r, (a (n + 1 + k + 1) - a (k + 1)) := by
    have h1 := Finset.sum_range_add (fun k => a (k + 1)) (n + 1) r
    have h2 := Finset.sum_range_add (fun k => a (k + 1)) r (n + 1)
    have h3 : ∑ k ∈ Finset.range (n + 1), a (k + 1 + r) =
        ∑ k ∈ Finset.range (n + 1), a (r + k + 1) :=
      Finset.sum_congr rfl fun k _ => by rw [show k + 1 + r = r + k + 1 by ring]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h3]
    rw [show r + (n + 1) = n + 1 + r by ring] at h2
    linarith
  rw [hsum]
  have hb : |∑ k ∈ Finset.range r, (a (n + 1 + k + 1) - a (k + 1))| ≤ r * μ.real univ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range r, |a (n + 1 + k + 1) - a (k + 1)| ≤
          ∑ _k ∈ Finset.range r, μ.real univ := Finset.sum_le_sum fun k _ => by
            rw [abs_le]; constructor <;> linarith [ha (n + 1 + k + 1), ha (k + 1)]
      _ = r * μ.real univ := by simp
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ### Uniformly Cauchy averages -/

variable (κ) in
/-- The Cesàro averages of `μ` are uniformly Cauchy on sets. -/
def CesaroCauchy (μ : Measure S) : Prop :=
  ∀ η > 0, ∃ n₀, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ A, MeasurableSet A →
    |(cesaroM κ n μ).real A - (cesaroM κ m μ).real A| ≤ η

omit [IsMarkovKernel κ] in
theorem cesaroCauchy_zero : CesaroCauchy κ 0 := fun η hη => ⟨0, fun n _ m _ A _ => by
  simp [cesaroM, adjointOp_zero, hη.le]⟩

theorem CesaroCauchy.add {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : CesaroCauchy κ μ) (hν : CesaroCauchy κ ν) : CesaroCauchy κ (μ + ν) := by
  intro η hη
  obtain ⟨n₁, h₁⟩ := hμ (η / 2) (half_pos hη)
  obtain ⟨n₂, h₂⟩ := hν (η / 2) (half_pos hη)
  refine ⟨max n₁ n₂, fun n hn m hm A hA => ?_⟩
  have := isFinite_cesaroM (κ := κ) n μ; have := isFinite_cesaroM (κ := κ) n ν
  have := isFinite_cesaroM (κ := κ) m μ; have := isFinite_cesaroM (κ := κ) m ν
  rw [cesaroM_add, cesaroM_add, measureReal_add_apply, measureReal_add_apply]
  have := h₁ n (le_of_max_le_left hn) m (le_of_max_le_left hm) A hA
  have := h₂ n (le_of_max_le_right hn) m (le_of_max_le_right hm) A hA
  calc _ = |((cesaroM κ n μ).real A - (cesaroM κ m μ).real A) +
        ((cesaroM κ n ν).real A - (cesaroM κ m ν).real A)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

omit [IsMarkovKernel κ] in
theorem CesaroCauchy.smul {μ : Measure S} [IsFiniteMeasure μ] (hμ : CesaroCauchy κ μ)
    (c : ℝ≥0∞) : CesaroCauchy κ (c • μ) := by
  intro η hη
  obtain ⟨n₀, h⟩ := hμ (η / (c.toReal + 1)) (by positivity)
  refine ⟨n₀, fun n hn m hm A hA => ?_⟩
  rw [cesaroM_smul, cesaroM_smul, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply, ← mul_sub,
    abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have h' := h n hn m hm A hA
  calc c.toReal * |(cesaroM κ n μ).real A - (cesaroM κ m μ).real A| ≤
        (c.toReal + 1) * (η / (c.toReal + 1)) :=
        mul_le_mul (by linarith) h' (abs_nonneg _) (by positivity)
    _ = η := by field_simp

theorem cesaroCauchy_finsetSum {ι : Type*} (s : Finset ι) (μ : ι → Measure S)
    [∀ i, IsFiniteMeasure (μ i)] (h : ∀ i ∈ s, CesaroCauchy κ (μ i)) :
    CesaroCauchy κ (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cesaroCauchy_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Closure under small perturbations.** If for every `η > 0` some `T*ʳμ` is a measure with
uniformly Cauchy averages plus a measure of mass at most `η`, the averages of `μ` are uniformly
Cauchy. -/
theorem cesaroCauchy_of_approx {μ : Measure S} [IsFiniteMeasure μ]
    (h : ∀ η > 0, ∃ (r : ℕ) (μ' ρ : Measure S) (_ : IsFiniteMeasure μ') (_ : IsFiniteMeasure ρ),
      adjointOp (kpow κ r) μ = μ' + ρ ∧ CesaroCauchy κ μ' ∧ ρ.real univ ≤ η) :
    CesaroCauchy κ μ := by
  intro η hη
  obtain ⟨r, μ', ρ, _, _, hdec, hc, hρ⟩ := h (η / 4) (by positivity)
  obtain ⟨n₁, h₁⟩ := hc (η / 4) (by positivity)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (4 * r * μ.real univ / η)
  refine ⟨max n₁ n₂, fun n hn m hm A hA => ?_⟩
  have hsh : ∀ k ≥ n₂, |(cesaroM κ k (adjointOp (kpow κ r) μ)).real A - (cesaroM κ k μ).real A| ≤
      η / 4 := fun k hk => by
    refine (abs_cesaro_shift_le k r μ A).trans ?_
    have hk' : (n₂ : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity)]
    have := (div_lt_iff₀ hη).1 hn₂
    nlinarith [measureReal_nonneg (μ := μ) (s := univ)]
  have hmid : |(cesaroM κ n (adjointOp (kpow κ r) μ)).real A -
      (cesaroM κ m (adjointOp (kpow κ r) μ)).real A| ≤ η / 4 + η / 4 := by
    have := isFinite_cesaroM (κ := κ) n μ'; have := isFinite_cesaroM (κ := κ) n ρ
    have := isFinite_cesaroM (κ := κ) m μ'; have := isFinite_cesaroM (κ := κ) m ρ
    rw [hdec, cesaroM_add, cesaroM_add, measureReal_add_apply, measureReal_add_apply]
    have h1 := h₁ n (le_of_max_le_left hn) m (le_of_max_le_left hm) A hA
    have h2 := cesaroM_real_nonneg_le (κ := κ) n ρ A
    have h3 := cesaroM_real_nonneg_le (κ := κ) m ρ A
    calc _ = |((cesaroM κ n μ').real A - (cesaroM κ m μ').real A) +
          ((cesaroM κ n ρ).real A - (cesaroM κ m ρ).real A)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 (by rw [abs_le]; constructor <;> linarith))
  have e1 := hsh n (le_of_max_le_right hn)
  have e2 := hsh m (le_of_max_le_right hm)
  calc _ = |((cesaroM κ n μ).real A - (cesaroM κ n (adjointOp (kpow κ r) μ)).real A) +
        ((cesaroM κ n (adjointOp (kpow κ r) μ)).real A -
          (cesaroM κ m (adjointOp (kpow κ r) μ)).real A) +
        ((cesaroM κ m (adjointOp (kpow κ r) μ)).real A - (cesaroM κ m μ).real A)| := by ring_nf
    _ ≤ _ := by
      refine (abs_add_le _ _).trans ?_
      refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
      rw [abs_sub_comm] at e1
      linarith

/-- `T*` preserves uniformly Cauchy averages. -/
theorem cesaroCauchy_adjoint {μ : Measure S} [IsFiniteMeasure μ] (hμ : CesaroCauchy κ μ)
    (r : ℕ) : CesaroCauchy κ (adjointOp (kpow κ r) μ) := by
  have := isFinite_adjoint (κ := κ) r μ
  refine cesaroCauchy_of_approx fun η hη => ⟨0, adjointOp (kpow κ r) μ, 0, inferInstance,
    inferInstance, by rw [add_zero, ← adjoint_add, zero_add], ?_, by simp [hη.le]⟩
  -- `T*ʳμ` differs from `μ` by a shift
  intro η hη
  obtain ⟨n₁, h₁⟩ := hμ (η / 3) (by positivity)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (3 * r * μ.real univ / η)
  refine ⟨max n₁ n₂, fun n hn m hm A hA => ?_⟩
  have hsh : ∀ k ≥ n₂, |(cesaroM κ k (adjointOp (kpow κ r) μ)).real A - (cesaroM κ k μ).real A| ≤
      η / 3 := fun k hk => by
    refine (abs_cesaro_shift_le k r μ A).trans ?_
    have hk' : (n₂ : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity)]
    have := (div_lt_iff₀ hη).1 hn₂
    nlinarith [measureReal_nonneg (μ := μ) (s := univ)]
  have e1 := hsh n (le_of_max_le_right hn)
  have e2 := hsh m (le_of_max_le_right hm)
  have e3 := h₁ n (le_of_max_le_left hn) m (le_of_max_le_left hm) A hA
  rw [abs_le] at e1 e2 e3 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-- For probability measures, uniformly Cauchy averages are Cauchy in total variation. -/
theorem tvDist_cesaro_le {μ : Measure S} [IsProbabilityMeasure μ] (hμ : CesaroCauchy κ μ) :
    ∀ η > 0, ∃ n₀, ∀ n ≥ n₀, ∀ m ≥ n₀, tvDist (cesaroM κ n μ) (cesaroM κ m μ) < η := by
  intro η hη
  obtain ⟨n₀, h⟩ := hμ (η / 4) (by positivity)
  refine ⟨n₀, fun n hn m hm => ?_⟩
  have := isProb_cesaroM (κ := κ) n μ
  have := isProb_cesaroM (κ := κ) m μ
  have := tvDist_le_of_forall (cesaroM κ n μ) (cesaroM κ m μ) (h n hn m hm)
  linarith

end StokeyLucasPrescott.StrongConvergence
