/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.MLODMcCall
import StructuralEstimation.MLExercises
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The job search likelihood (Examples 12.2.1, 12.3.1; Exercises 12.3–12.4)

Miao, §12.2, Example 12.2.1, pp. 396–397; §12.3, Example 12.3.1, p. 400; Exercises 12.3 and
12.4, pp. 408–409. McCall's model (Miao §8.1) is copied in `MLODMcCall`: the worker accepts
the offer `w` iff `w ≥ w*`, the reservation wage.

* `ml_firstPassage_iid` (Example 12.3.1, the i.i.d. case, and Example 12.2.1): if the offers
  `w₁, w₂, …` are i.i.d. with law `F` and `A` is the acceptance set, the probability of
  rejecting `n` offers and accepting the `(n + 1)`-th is `F(Aᶜ)ⁿ F(A)`.
* `example_12_2_1_duration` (Example 12.2.1): with `A = [w*, ∞)`, the probability of accepting a
  job for the first time after `t` periods is `Lᵢ = (1 − q) qᵗ⁻¹`, `q = F((−∞, w*))`;
  `ml_reject_prob_eq_cdf`: `q = F(w*)` (the book's expression) when `F` has no atom at `w*`.
* `example_12_2_1` (Example 12.2.1): the sample likelihood `L = ∏ᵢ (1 − q) q^{tᵢ − 1}` equals
  `(1 − q)ᴺ q^{∑(tᵢ − 1)}`; it depends on the structural parameters `θ` only through the
  reservation wage `w*(θ)`; and as a function of `q` it is maximised at
  `q̂ = ∑(tᵢ − 1)/∑ tᵢ`.
* `ml_resWage_mono_beta` (the content of Exercise 12.3): the McCall reservation wage is
  nondecreasing in the discount factor `β`, and `ml_resWage_strictMono_beta` strictly increasing
  when offers above it have positive probability; so `β` moves the likelihood through `w*(β)`.
* `ex_12_4_moments` (the content of Exercise 12.4): the duration `D` with
  `P(D = n + 1) = qⁿ(1 − q)` has `P(D = 1) = 1 − q`, `P(D ≤ 2) = 1 − q²`,
  `E D = 1/(1 − q)`, `E D² = (1 + q)/(1 − q)²` and `Var D = q/(1 − q)²`: the moments used for
  SMM in Example 12.3.2.

Departures. The book writes the rejection probability as `F(w*)`; with acceptance iff
`w ≥ w*` it is `F((−∞, w*))`, equal to `F(w*)` when `F` has no atom at `w*`
(`ml_reject_prob_eq_cdf`). Example 12.3.1 writes `wₜ > w*` for acceptance, which agrees with
Example 12.2.1's `w ≥ w*` under the same condition; `ml_firstPassage_iid` covers both. The
lognormal offer distribution of Exercise 12.3 is not concentrated on a bounded interval, as the
copied McCall model requires; the monotonicity result is proved for offers on `[0, B]`.
Simulation and plotting in Exercises 12.3–12.4 are computational and not formalised.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

/-- The event that offers `0, …, n − 1` are rejected and offer `n` is accepted (offer `i` is the
offer of period `i + 1`), with acceptance set `A`. -/
def ml_firstPassage {Ω : Type*} (w : ℕ → Ω → ℝ) (A : Set ℝ) (n : ℕ) : Set Ω :=
  {ω | (∀ i < n, w i ω ∉ A) ∧ w n ω ∈ A}

/-- Miao, Example 12.3.1, p. 400 (i.i.d. case) and Example 12.2.1, p. 397: if the offers are
i.i.d. with law `F` and `A` is the (measurable) acceptance set, the probability of waiting
exactly `n + 1` periods is `F(Aᶜ)ⁿ F(A)`. -/
theorem ml_firstPassage_iid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → Ω → ℝ) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hindep : iIndepFun w P) (hlaw : ∀ i, HasLaw (w i) F P) {A : Set ℝ} (hA : MeasurableSet A)
    (n : ℕ) : P.real (ml_firstPassage w A n) = F.real Aᶜ ^ n * F.real A := by
  classical
  let sets : ℕ → Set ℝ := fun i => if i < n then Aᶜ else A
  have hsets : ∀ i, MeasurableSet (sets i) := fun i => by
    simp only [sets]; split_ifs
    · exact hA.compl
    · exact hA
  have hev : ml_firstPassage w A n = ⋂ i ∈ Finset.range (n + 1), w i ⁻¹' sets i := by
    ext ω
    simp only [ml_firstPassage, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage, sets]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      split_ifs with h
      · exact h1 i h
      · rw [show i = n by omega]; exact h2
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i (by omega)
        simp only [hi, ↓reduceIte] at this
        exact this
      · have := h n (by omega)
        simp only [lt_irrefl, ↓reduceIte] at this
        exact this
  have hprod := hindep.measure_inter_preimage_eq_mul (Finset.range (n + 1))
    (sets := sets) fun i _ => hsets i
  have hlawi : ∀ i, P (w i ⁻¹' sets i) = F (sets i) := fun i => by
    rw [← Measure.map_apply_of_aemeasurable (hlaw i).aemeasurable (hsets i), (hlaw i).map_eq]
  rw [hev, measureReal_def, hprod, Finset.prod_range_succ]
  simp only [hlawi]
  rw [Finset.prod_congr rfl fun i hi => (by
    simp only [sets, Finset.mem_range.1 hi, ↓reduceIte] : F (sets i) = F Aᶜ)]
  simp only [sets, lt_irrefl, ↓reduceIte, Finset.prod_const, Finset.card_range,
    ENNReal.toReal_mul, ENNReal.toReal_pow, measureReal_def]

/-- Miao, Example 12.2.1, p. 397: with acceptance iff `w ≥ w*`, the probability that a worker
accepts a job for the first time after `t = n + 1` periods is `(1 − q) qⁿ` with
`q = F((−∞, w*))`. -/
theorem example_12_2_1_duration {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : ℕ → Ω → ℝ) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hindep : iIndepFun w P) (hlaw : ∀ i, HasLaw (w i) F P) (wstar : ℝ) (n : ℕ) :
    P.real {ω | (∀ i < n, w i ω < wstar) ∧ wstar ≤ w n ω} =
      (1 - F.real (Set.Iio wstar)) * F.real (Set.Iio wstar) ^ n := by
  have h := ml_firstPassage_iid w F hindep hlaw (measurableSet_Ici (a := wstar)) n
  have hev : ml_firstPassage w (Set.Ici wstar) n =
      {ω | (∀ i < n, w i ω < wstar) ∧ wstar ≤ w n ω} := by
    ext ω; simp [ml_firstPassage]
  rw [hev, Set.compl_Ici, ← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio] at h
  rw [h]
  ring

/-- Miao, Example 12.2.1, p. 397: the rejection probability `F((−∞, w*))` equals the book's
`F(w*)` (the distribution function at `w*`) when `F` has no atom at `w*`. -/
theorem ml_reject_prob_eq_cdf (F : Measure ℝ) [IsProbabilityMeasure F] (wstar : ℝ)
    (hatom : F {wstar} = 0) : F.real (Set.Iio wstar) = cdf F wstar := by
  rw [cdf_eq_real, ← Set.Iio_union_right, measureReal_union (by simp) (measurableSet_singleton _),
    measureReal_def F {wstar}, hatom, ENNReal.toReal_zero, add_zero]

/-- The job search likelihood of Example 12.2.1 as a function of the rejection probability
`q`: `L(q) = ∏ᵢ (1 − q) q^{tᵢ − 1}` for the observed durations `t₁, …, t_N`. -/
def ml_durationLik {N : ℕ} (t : Fin N → ℕ) (q : ℝ) : ℝ := ∏ i, (1 - q) * q ^ (t i - 1)

/-- **Example 12.2.1** (Miao, pp. 396–397). Let `w*(θ)` be the reservation wage at the
structural parameter `θ` (e.g. `θ = (c, β)`) and `q(θ) = F((−∞, w*(θ)))`; the likelihood of
the durations `t₁, …, t_N ≥ 1` is `L(θ) = ∏ᵢ (1 − F(w*(θ))) F(w*(θ))^{tᵢ − 1}`. Then
1. `L(θ) = (1 − q)ᴺ q^{∑ᵢ (tᵢ − 1)}`;
2. `L` depends on `θ` only through `w*(θ)`: `w*(θ₁) = w*(θ₂) ⇒ L(θ₁) = L(θ₂)`;
3. as a function of `q ∈ [0, 1]` it is maximised at `q̂ = ∑ᵢ (tᵢ − 1)/∑ᵢ tᵢ`. -/
theorem example_12_2_1 {Θ : Type*} (F : Measure ℝ) (wstar : Θ → ℝ) {N : ℕ} (hN : 0 < N)
    (t : Fin N → ℕ) (ht : ∀ i, 1 ≤ t i) :
    (∀ θ, ml_durationLik t (F.real (Set.Iio (wstar θ))) =
      (1 - F.real (Set.Iio (wstar θ))) ^ N *
        F.real (Set.Iio (wstar θ)) ^ (∑ i, (t i - 1))) ∧
      (∀ θ₁ θ₂, wstar θ₁ = wstar θ₂ → ml_durationLik t (F.real (Set.Iio (wstar θ₁))) =
        ml_durationLik t (F.real (Set.Iio (wstar θ₂)))) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1, ml_durationLik t q ≤
        ml_durationLik t (((∑ i, (t i - 1) : ℕ) : ℝ) / ((∑ i, t i : ℕ) : ℝ)) := by
  have hform : ∀ q, ml_durationLik t q = (1 - q) ^ N * q ^ (∑ i, (t i - 1)) := fun q => by
    unfold ml_durationLik
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow_eq_pow_sum]
  refine ⟨fun θ => hform _, fun θ₁ θ₂ h => by rw [h], fun q hq => ?_⟩
  set k := ∑ i, (t i - 1)
  set n := ∑ i, t i
  have hkn : k + N = n := by
    simp only [k, n]
    have : ∀ i, t i - 1 + 1 = t i := fun i => Nat.sub_add_cancel (ht i)
    calc ∑ i, (t i - 1) + N = ∑ i, (t i - 1 + 1) := by
          rw [Finset.sum_add_distrib]; simp
      _ = ∑ i, t i := Finset.sum_congr rfl fun i _ => this i
  have hnpos : 0 < n := by omega
  have hb := ml_binomial_lik_le n k hnpos (by omega) q hq.1 hq.2
  rw [hform, hform, mul_comm, mul_comm ((1 - _) ^ N)]
  rw [show n - k = N by omega] at hb
  exact hb

/-- The function `ψ_β(x) = x − c − β/(1 − β) ∫_{w > x} (w − x) dF` whose root is the McCall
reservation wage (`ml_od_mccall_reservation`). -/
theorem ml_mccall_psi_root {F : Measure ℝ} [IsProbabilityMeasure F] {B c β : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) {V : ℝ → ℝ}
    (hV : ml_od_McCallBellman F B c β V) (x : ℝ) :
    ml_od_firingψ F c 0 β x = 0 ↔ x = (1 - β) * (c + β * ∫ w, V w ∂F) :=
  ml_ex_8_2_root_unique hF hβ0 hβ1 le_rfl ((ml_od_mccall_iff_firing hβ1 V).1 hV) x

/-- The content of **Exercise 12.3** (Miao, p. 408): the McCall reservation wage
`w*(β) = (1 − β)(c + β ∫ V dF)` is nondecreasing in the discount factor `β`, for offers on
`[0, B]`. So the likelihood of Example 12.2.1 varies with `β` only through `q(β) = F(w*(β))`. -/
theorem ml_resWage_mono_beta {F : Measure ℝ} [IsProbabilityMeasure F] {B c β₁ β₂ : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ₁0 : 0 < β₁) (h12 : β₁ ≤ β₂) (hβ₂1 : β₂ < 1)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ml_od_McCallBellman F B c β₁ V₁)
    (hV₂ : ml_od_McCallBellman F B c β₂ V₂) :
    (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F) ≤ (1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F) := by
  have hβ₁1 : β₁ < 1 := lt_of_le_of_lt h12 hβ₂1
  have hβ₂0 : 0 < β₂ := lt_of_lt_of_le hβ₁0 h12
  set x₁ := (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)
  have h1 : ml_od_firingψ F c 0 β₁ x₁ = 0 := (ml_mccall_psi_root hF hβ₁0 hβ₁1 hV₁ x₁).2 rfl
  have h3 := (ml_mccall_psi_root hF hβ₂0 hβ₂1 hV₂ ((1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F))).2 rfl
  have hcoef : β₁ / (1 - β₁ + 0 * β₁) ≤ β₂ / (1 - β₂ + 0 * β₂) := by
    simp only [zero_mul, add_zero]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hint : 0 ≤ ∫ w in Set.Ioi x₁, (w - x₁) ∂F := by
    rw [ml_od_setIntegral_Ioi_eq]; exact integral_nonneg fun _ => le_max_right _ _
  have h2 : ml_od_firingψ F c 0 β₂ x₁ ≤ 0 := by
    unfold ml_od_firingψ at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcoef hint]
  exact (ml_od_firingψ_strictMono hF hβ₂0 hβ₂1 le_rfl).le_iff_le.1 (by rw [h3]; exact h2)

/-- The content of **Exercise 12.3** (Miao, p. 408): if `β₁ < β₂` and offers above the
reservation wage `w*(β₁)` have positive expected surplus, `∫_{w > w*(β₁)} (w − w*(β₁)) dF > 0`,
then `w*(β₁) < w*(β₂)`. -/
theorem ml_resWage_strictMono_beta {F : Measure ℝ} [IsProbabilityMeasure F] {B c β₁ β₂ : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ₁0 : 0 < β₁) (h12 : β₁ < β₂) (hβ₂1 : β₂ < 1)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ml_od_McCallBellman F B c β₁ V₁)
    (hV₂ : ml_od_McCallBellman F B c β₂ V₂)
    (hpos : 0 < ∫ w in Set.Ioi ((1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)),
      (w - (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)) ∂F) :
    (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F) < (1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F) := by
  have hβ₁1 : β₁ < 1 := lt_trans h12 hβ₂1
  have hβ₂0 : 0 < β₂ := lt_trans hβ₁0 h12
  set x₁ := (1 - β₁) * (c + β₁ * ∫ w, V₁ w ∂F)
  have h1 : ml_od_firingψ F c 0 β₁ x₁ = 0 := (ml_mccall_psi_root hF hβ₁0 hβ₁1 hV₁ x₁).2 rfl
  have h3 := (ml_mccall_psi_root hF hβ₂0 hβ₂1 hV₂ ((1 - β₂) * (c + β₂ * ∫ w, V₂ w ∂F))).2 rfl
  have hcoef : β₁ / (1 - β₁ + 0 * β₁) < β₂ / (1 - β₂ + 0 * β₂) := by
    simp only [zero_mul, add_zero]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : ml_od_firingψ F c 0 β₂ x₁ < 0 := by
    unfold ml_od_firingψ at h1 ⊢
    nlinarith [mul_lt_mul_of_pos_right hcoef hpos]
  exact (ml_od_firingψ_strictMono hF hβ₂0 hβ₂1 le_rfl).lt_iff_lt.1 (by rw [h3]; exact h2)

/-- The content of **Exercise 12.4** (Miao, p. 409) and Example 12.3.2: for the duration `D`
with `P(D = n + 1) = qⁿ(1 − q)`, `0 ≤ q < 1`: the probabilities sum to one,
`P(D = 1) = 1 − q`, `P(D ≤ 2) = 1 − q²`, `E D = 1/(1 − q)`, `E D² = (1 + q)/(1 − q)²` and
`Var D = E D² − (E D)² = q/(1 − q)²`. -/
theorem ex_12_4_moments {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ n * (1 - q)) 1 ∧
      q ^ 0 * (1 - q) = 1 - q ∧ q ^ 0 * (1 - q) + q ^ 1 * (1 - q) = 1 - q ^ 2 ∧
      HasSum (fun n : ℕ => ((n : ℝ) + 1) * (q ^ n * (1 - q))) (1 / (1 - q)) ∧
      HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * (q ^ n * (1 - q))) ((1 + q) / (1 - q) ^ 2) ∧
      (1 + q) / (1 - q) ^ 2 - (1 / (1 - q)) ^ 2 = q / (1 - q) ^ 2 := by
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hne : 1 - q ≠ 0 := by linarith
  have h0 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 0 hnorm
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero] at h0
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] at h1
  simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat] at h2
  refine ⟨?_, by ring, by ring, ?_, ?_, ?_⟩
  · have := h0.mul_right (1 - q)
    convert this using 1
    simp only [zero_add, pow_one]
    field_simp
  · have := h1.mul_right (1 - q)
    convert this using 1
    · funext n; ring
    · field_simp
  · -- `(n + 1)² = 2 · C(n + 2, 2) − (n + 1)`
    have := ((h2.mul_left 2).sub h1).mul_right (1 - q)
    convert this using 1
    · funext n; ring
    · field_simp
      ring
  · field_simp
    ring

end Miao.StructuralEstimation
