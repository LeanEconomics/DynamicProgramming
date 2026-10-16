/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.LinearCurrency

/-!
# A pure credit economy with linear utility

SLP §13.7, Exercise 13.7, pp. 402–403. Endowment `y > 0`, constant asset price `q > 0`, gross
return `R = 1 + y/q`, shocks on `Z = [0, 1]` with distribution `μ`, `0 < β < 1`;
`H(ζ) = ∫ max{ζ, z′} μ(dz′)` (`maxInt`, from `LinearCurrency`), `δ = μ([ζ, 1])`.

* **Exercise 13.7(a)** (p. 403). `ex_13_7a_cutoff`: if `μ` charges every `(a, 1]` (`lt_maxInt`:
  then `H(ζ) > ζ` for `ζ < 1`), the cutoff equation `ζ = βR∫max{ζ, z′}μ(dz′)` has a solution
  `ζ ∈ (0, 1)` iff `βR < 1` (i.e. `q > βy/(1 − β)`), and then it is unique. `ex_13_7a`:
  `v(w, z) = (y + q) max{ζ, z} w` (`creditValue`) satisfies the functional equation (2)
  (`SatisfiesCreditBellman`), the maximum being attained at the policy (3) (`creditPolicy`):
  `w′ = Rw` if `z < ζ`, `w′ = 0` if `z ≥ ζ`.
* **Exercise 13.7(b)** (p. 403). The process (`creditKernel`, built by `cutoffKernel` from (3) and
  `μ`) is `P(w, ·) = μ([0, ζ))δ_{Rw} + δ·δ₀` (`creditKernel_apply`); `0` is absorbing
  (`creditKernel_zero`) and `δ₀` is invariant (`adjointOp_creditKernel_dirac`). `ex_13_7b`: for
  `δ > 0` Condition M holds, `δ₀` is the unique invariant probability measure, and for every
  `Ψ₀`, `‖T*ⁿΨ₀ − δ₀‖ ≤ 2(1 − δ)ⁿ`, `|∫ f dΨₙ − f(0)| ≤ 2‖f‖(1 − δ)ⁿ`
  (`abs_integral_sub_le_norm_mul_tvDist`) and `T*ⁿΨ₀ ⇒ δ₀`. `ex_13_7b_counterexample`: the book's
  claim is false. `ex_13_7b_corrected`: when `Rμ([0, ζ)) = 1` and `Ψ₀` satisfies (1), every `Ψₙ`
  satisfies (1) but the weak limit `δ₀` does not, and no invariant probability measure does.
  `ex_13_7b_feller`: `P` is Feller, although `w ↦ P(w, {0})` is discontinuous at `0`.
* **Exercise 13.7(c)** (p. 403). (1) is `MarketClears` (`∫ w Ψ(dw) = 1`, for the nonnegative
  part). `lintegral_creditKernel_mean`, `lintegral_creditKernel_mean_iterate`: under (3),
  `∫ w Ψ_{t+1}(dw) = Rμ([0, ζ)) ∫ w Ψ_t(dw)`; `marketClears_iterate_iff`: (1) holds at every date
  iff `Rμ([0, ζ)) = 1`. `CreditEqm`: an equilibrium `(q, ζ)` (cutoff equation and
  `Rμ([0, ζ)) = 1`). `maxInt_eq_split`: `H(ζ) = ζμ([0, ζ)) + ∫_{[ζ, 1]} z dμ`. `ex_13_7c`: in an
  equilibrium, (3) solves (2) at every date, every `Ψ₀` satisfying (1) gives `Ψₜ` satisfying (1)
  for all `t`, `(1 − β)ζμ([0, ζ)) = β∫_{[ζ, 1]} z μ(dz)`, and `q = yμ([0, ζ))/μ([ζ, 1])`, which
  does not involve `Ψ₀`. `ex_13_7c_betaR`: `βR < 1` follows when `μ` charges every `(a, 1]`.
  `ex_13_7c_exists`: an equilibrium exists when `a ↦ μ([0, a))` is continuous (no atoms; uses
  `measureReal_le_le_lt`). `ex_13_7c_unique`: all equilibria have the same `ζ` and the same
  `q/y`. `ex_13_7c_scaling`: `(q, ζ)` is an equilibrium for `y` iff `(cq, ζ)` is one for `cy`.

**Corrections.**
1. Ex. 13.7(b), p. 403: "`{T*ⁿΨ₀}` does not converge weakly to an invariant measure" is false:
   `T*ⁿΨ₀ ⇒ δ₀`, which is invariant (`ex_13_7b`, `ex_13_7b_counterexample` with `Ψ₀ = δ₁`). The
   true statement is that the limit does not satisfy (1) (`ex_13_7b_corrected`).
2. Solutions manual, Ex. 13.7(b): "P is not Feller" is false (`ex_13_7b_feller`); only the
   discontinuity of `w ↦ P(w, {0})` is true, and the Feller property does not involve it.
3. Ex. 13.7(c), p. 403: `q` cannot be characterised "in terms of `β` and `μ`": it is proportional
   to `y` (`ex_13_7c_scaling`, `ex_13_7c_counterexample`); what `β` and `μ` determine is `q/y`
   (`ex_13_7c_unique`).
4. The derived solution's "a root `ζ ∈ (0, 1)` exists iff `βR < 1`" needs `μ` to charge every
   `(a, 1]` (true under the density condition of §13.5): for `μ = δ_{1/2}` and `βR = 1` every
   `ζ ∈ [1/2, 1)` is a root (`ex_13_7a_counterexample`).
5. The derived solution's "`βR < 1` then holds automatically" needs the same kind of condition:
   for `μ₀ = ½δ_{1/2} + ½δ₀`, `β = 1/2`, `(q, ζ) = (y, 1/2)` is an equilibrium with `βR = 1`
   (`ex_13_7c_betaR_counterexample`).

Remark. The manual writes the market-clearing condition as `(1 + y/q)μ([0, ζ]) = 1`; under (3)
the savers are `{z < ζ}`, so it is `μ([0, ζ))` (the two agree unless `μ` has an atom at `ζ`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {μ : Measure unitInterval} [IsProbabilityMeasure μ]

/-! ### Exercise 13.7(a): the cutoff and the value function -/

/-- `H(ζ) > ζ` for `ζ < 1` when `μ` charges every `(a, 1]`, `a < 1`: the integrand
`max{ζ, z′} − ζ ≥ 0` is positive on `(ζ, 1]`. -/
theorem lt_maxInt (hsupp : ∀ a : ℝ, a < 1 → 0 < μ {z : unitInterval | a < (z : ℝ)}) {ζ : ℝ}
    (hζ : ζ < 1) : ζ < maxInt μ ζ := by
  have hint : Integrable (fun z : unitInterval => max ζ (z : ℝ) - ζ) μ :=
    (integrable_max_unit ζ).sub (integrable_const ζ)
  have hpos : 0 < ∫ z, (max ζ (z : ℝ) - ζ) ∂μ := by
    refine (integral_pos_iff_support_of_nonneg (fun z => sub_nonneg.2 (le_max_left _ _))
      hint).2 ?_
    have : Function.support (fun z : unitInterval => max ζ (z : ℝ) - ζ) =
        {z : unitInterval | ζ < (z : ℝ)} := by
      ext z
      simp only [Function.mem_support, mem_ofPred_eq, ne_eq, sub_eq_zero]
      constructor
      · intro h
        by_contra h'
        exact h (max_eq_left (not_lt.1 h'))
      · intro h h'
        rw [max_eq_right h.le] at h'
        linarith
    rw [this]
    exact hsupp ζ hζ
  rw [integral_sub (integrable_max_unit ζ) (integrable_const ζ)] at hpos
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hpos
  unfold maxInt
  linarith

/-- **Exercise 13.7(a), the cutoff.** With `R = 1 + y/q`, the cutoff equation
`ζ = βR ∫ max{ζ, z′} μ(dz′)` has a solution `ζ ∈ (0, 1)` iff `βR < 1`, and then the solution is
unique. The "only if" uses that `μ` charges every `(a, 1]` (true under the density condition of
§13.5); see `ex_13_7a_counterexample`. -/
theorem ex_13_7a_cutoff {β R : ℝ} (hβ0 : 0 < β) (hR : 0 < R) (hE : 0 < ∫ z, (z : ℝ) ∂μ)
    (hsupp : ∀ a : ℝ, a < 1 → 0 < μ {z : unitInterval | a < (z : ℝ)}) :
    ((∃ ζ : ℝ, ζ ∈ Ioo (0 : ℝ) 1 ∧ ζ = β * R * maxInt μ ζ) ↔ β * R < 1) ∧
      (β * R < 1 → ∃! ζ : ℝ, ζ ∈ Ioo (0 : ℝ) 1 ∧ ζ = β * R * maxInt μ ζ) := by
  have hb : 0 < β * R := mul_pos hβ0 hR
  refine ⟨⟨fun ⟨ζ, hζ, hcut⟩ => ?_, fun h => ?_⟩, fun h => exists_unique_cutoff hb h hE⟩
  · by_contra hge
    have h1 := lt_maxInt hsupp hζ.2
    have h2 : maxInt μ ζ ≤ β * R * maxInt μ ζ :=
      le_mul_of_one_le_left (hζ.1.le.trans h1.le) (not_lt.1 hge)
    linarith
  · obtain ⟨ζ, hζ, -⟩ := exists_unique_cutoff hb h hE
    exact ⟨ζ, hζ⟩

/-- The point `1/2` of `Z = [0, 1]`. -/
noncomputable def halfUnitInterval : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- **Exercise 13.7(a), missing hypothesis.** Without a support condition the "only if" fails at
`βR = 1`: for `μ = δ_{1/2}`, `β = 1/2`, `R = 2` (so `βR = 1`, e.g. `q = y`), `ζ = 3/4 ∈ (0, 1)`
solves `ζ = βR max{ζ, 1/2}` (indeed every `ζ ∈ [1/2, 1)` does). -/
theorem ex_13_7a_counterexample :
    0 < ∫ z, (z : ℝ) ∂(Measure.dirac halfUnitInterval) ∧ ¬ ((1 / 2 : ℝ) * 2 < 1) ∧
      (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
      (3 / 4 : ℝ) = 1 / 2 * 2 * maxInt (Measure.dirac halfUnitInterval) (3 / 4) := by
  refine ⟨?_, by norm_num, ⟨by norm_num, by norm_num⟩, ?_⟩
  · rw [integral_dirac]
    simp only [halfUnitInterval]
    norm_num
  · rw [maxInt, integral_dirac]
    simp only [halfUnitInterval]
    norm_num

/-- The value function of Exercise 13.7(a): `v(w, z) = (y + q) max{ζ, z} w`. -/
noncomputable def creditValue (y q ζ : ℝ) (w : ℝ) (z : unitInterval) : ℝ :=
  (y + q) * max ζ (z : ℝ) * w

/-- The policy (3) of Exercise 13.7(a): `w′ = (1 + y/q)w` if `z < ζ` and `w′ = 0` (sell
everything) if `z ≥ ζ`. -/
noncomputable def creditPolicy (y q ζ : ℝ) (w : ℝ) (z : unitInterval) : ℝ :=
  if (z : ℝ) < ζ then (1 + y / q) * w else 0

/-- `v` **satisfies the functional equation (2)** of §13.7 (p. 403): for `w ≥ 0`, `v(w, z)` is
the maximum over `0 ≤ w′ ≤ (1 + y/q)w` of `[(y + q)w − qw′]z + β ∫ v(w′, z′) μ(dz′)`. -/
def SatisfiesCreditBellman (β y q : ℝ) (μ : Measure unitInterval)
    (v : ℝ → unitInterval → ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ w → ∀ z : unitInterval,
    IsGreatest ((fun w' => ((y + q) * w - q * w') * (z : ℝ) + β * ∫ z', v w' z' ∂μ) ''
      Icc 0 ((1 + y / q) * w)) (v w z)

omit [IsProbabilityMeasure μ] in
/-- `∫ v(w′, z′) μ(dz′) = (y + q) H(ζ) w′`. -/
theorem integral_creditValue (y q ζ w' : ℝ) :
    ∫ z', creditValue y q ζ w' z' ∂μ = (y + q) * maxInt μ ζ * w' := by
  unfold creditValue
  rw [integral_mul_const, integral_const_mul]
  rfl

omit [IsProbabilityMeasure μ] in
/-- **Exercise 13.7(a).** If `y ≥ 0`, `q > 0` and `ζ = βR H(ζ)` with `R = 1 + y/q`, then
`v(w, z) = (y + q) max{ζ, z} w` satisfies (2), with maximiser (3): the objective is
`(y + q)wz + q(ζ − z)w′`, linear in `w′`, because `β(y + q)H(ζ) = qβRH(ζ) = qζ`. -/
theorem ex_13_7a {β y q ζ : ℝ} (hy : 0 ≤ y) (hq : 0 < q) (hcut : ζ = β * (1 + y / q) * maxInt μ ζ) :
    SatisfiesCreditBellman β y q μ (creditValue y q ζ) ∧
      ∀ w : ℝ, 0 ≤ w → ∀ z : unitInterval,
        creditPolicy y q ζ w z ∈ Icc 0 ((1 + y / q) * w) ∧
          ((y + q) * w - q * creditPolicy y q ζ w z) * (z : ℝ) +
              β * ∫ z', creditValue y q ζ (creditPolicy y q ζ w z) z' ∂μ =
            creditValue y q ζ w z := by
  have hqR : q * (1 + y / q) = y + q := by
    field_simp
    ring
  have hcut' : q * ζ = β * (y + q) * maxInt μ ζ := by
    rw [← hqR]
    nth_rewrite 1 [hcut]
    ring
  have hR0 : 0 ≤ 1 + y / q := by positivity
  have hobj : ∀ w w' : ℝ, ∀ z : unitInterval,
      ((y + q) * w - q * w') * (z : ℝ) + β * ∫ z', creditValue y q ζ w' z' ∂μ =
        (y + q) * w * z + q * (ζ - z) * w' := by
    intro w w' z
    rw [integral_creditValue]
    linear_combination (-w') * hcut'
  have hpol : ∀ w : ℝ, 0 ≤ w → ∀ z : unitInterval,
      creditPolicy y q ζ w z ∈ Icc 0 ((1 + y / q) * w) ∧
        ((y + q) * w - q * creditPolicy y q ζ w z) * (z : ℝ) +
            β * ∫ z', creditValue y q ζ (creditPolicy y q ζ w z) z' ∂μ =
          creditValue y q ζ w z := by
    intro w hw z
    rw [hobj]
    unfold creditPolicy creditValue
    by_cases hz : (z : ℝ) < ζ
    · simp only [hz, ↓reduceIte, max_eq_left hz.le]
      exact ⟨⟨mul_nonneg hR0 hw, le_rfl⟩, by linear_combination ((ζ - z) * w) * hqR⟩
    · simp only [hz, ↓reduceIte, max_eq_right (not_lt.1 hz)]
      exact ⟨⟨le_rfl, mul_nonneg hR0 hw⟩, by ring⟩
  refine ⟨fun w hw z => ⟨⟨_, (hpol w hw z).1, (hpol w hw z).2⟩, ?_⟩, hpol⟩
  rintro _ ⟨w', ⟨h1, h2⟩, rfl⟩
  simp only
  rw [hobj]
  unfold creditValue
  by_cases hz : (z : ℝ) < ζ
  · rw [max_eq_left hz.le]
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hq.le (sub_nonneg.2 hz.le))
    have e : q * (ζ - z) * ((1 + y / q) * w) = (y + q) * (ζ - z) * w := by
      rw [← hqR]
      ring
    linarith
  · rw [max_eq_right (not_lt.1 hz)]
    have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hq.le (sub_nonneg.2 (not_lt.1 hz)))
    nlinarith

/-! ### Exercise 13.7(b): the asset-holdings process -/

/-- The transition function of §13.7 defined by the policy (3) and `μ`: from `w`, the next
holding is `Rw` if `z′ < ζ` and `0` if `z′ ≥ ζ`, with `R = 1 + y/q`. -/
noncomputable def creditKernel (μ : Measure unitInterval) [IsFiniteMeasure μ] (ζ R : ℝ) :
    Kernel ℝ ℝ :=
  cutoffKernel μ ζ (measurable_const_mul R) 0

/-- The credit kernel is a Markov kernel. -/
theorem isMarkovKernel_creditKernel (ζ R : ℝ) : IsMarkovKernel (creditKernel μ ζ R) :=
  isMarkovKernel_cutoffKernel ζ _ 0

/-- `P(w, ·) = μ([0, ζ)) δ_{Rw} + μ([ζ, 1]) δ₀`. -/
theorem creditKernel_apply (ζ R w : ℝ) :
    creditKernel μ ζ R w =
      μ {z | (z : ℝ) < ζ} • Measure.dirac (R * w) + μ {z | ζ ≤ (z : ℝ)} • Measure.dirac 0 :=
  cutoffKernel_apply ζ _ 0 w

/-- `0` is absorbing: `P(0, ·) = δ₀`. -/
theorem creditKernel_zero (ζ R : ℝ) : creditKernel μ ζ R 0 = Measure.dirac 0 := by
  rw [creditKernel_apply, mul_zero, ← add_smul, measure_lt_add_measure_ge, one_smul]

/-- `δ₀` is invariant: `T*δ₀ = P(0, ·) = δ₀`. -/
theorem adjointOp_creditKernel_dirac (ζ R : ℝ) :
    adjointOp (creditKernel μ ζ R) (Measure.dirac 0) = Measure.dirac 0 := by
  rw [adjointOp_dirac, creditKernel_zero]

omit [IsProbabilityMeasure μ] in
/-- `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖f‖ ‖λ₁ − λ₂‖` for bounded continuous `f`. -/
theorem abs_integral_sub_le_norm_mul_tvDist (l₁ l₂ : Measure ℝ) [IsFiniteMeasure l₁]
    [IsFiniteMeasure l₂] (f : ℝ →ᵇ ℝ) :
    |∫ x, f x ∂l₁ - ∫ x, f x ∂l₂| ≤ ‖f‖ * tvDist l₁ l₂ := by
  rcases (norm_nonneg f).lt_or_eq with hf | hf
  · have hg : ∀ s, |f s / ‖f‖| ≤ 1 := fun s => by
      rw [abs_div, abs_of_pos hf, div_le_one hf]
      exact bcf_abs_le_norm f s
    have := abs_integral_sub_le_tvDist l₁ l₂ (f.continuous.measurable.div_const _) hg
    rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hf, div_le_iff₀ hf] at this
    linarith
  · have h0 : ∀ s, f s = 0 := fun s => abs_nonpos_iff.1 (hf ▸ bcf_abs_le_norm f s)
    simp [h0, ← hf]

/-- **Exercise 13.7(b), correction.** Let `δ = μ([ζ, 1]) > 0`. The kernel
`P(w, ·) = μ([0, ζ))δ_{Rw} + δ·δ₀` satisfies Condition M (`P(w, {0}) ≥ δ`), `δ₀` is invariant and is
the only invariant probability measure, and from **every** initial distribution `Ψ₀`:
`‖T*ⁿΨ₀ − δ₀‖ ≤ 2(1 − δ)ⁿ`, `|∫ f dΨₙ − f(0)| ≤ 2‖f‖(1 − δ)ⁿ`, and `T*ⁿΨ₀ ⇒ δ₀` weakly. So the
book's claim that `{T*ⁿΨ₀}` does not converge weakly to an invariant measure is false
(`ex_13_7b_counterexample`). -/
theorem ex_13_7b {ζ R : ℝ} (hδ : 0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)}) :
    let δ := μ.real {z : unitInterval | ζ ≤ (z : ℝ)}
    ConditionMFor (creditKernel μ ζ R) 1 δ ∧
      adjointOp (creditKernel μ ζ R) (Measure.dirac 0) = Measure.dirac 0 ∧
      (∀ l : Measure ℝ, IsProbabilityMeasure l → adjointOp (creditKernel μ ζ R) l = l →
        l = Measure.dirac 0) ∧
      (∀ (Ψ₀ : Measure ℝ) [IsProbabilityMeasure Ψ₀] (n : ℕ),
        tvDist (adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀) (Measure.dirac 0) ≤
          2 * (1 - δ) ^ n) ∧
      (∀ (Ψ₀ : Measure ℝ) [IsProbabilityMeasure Ψ₀] (f : ℝ →ᵇ ℝ) (n : ℕ),
        |∫ w, f w ∂adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀ - f 0| ≤
          2 * ‖f‖ * (1 - δ) ^ n) ∧
      ∀ (Ψ₀ : Measure ℝ) [IsProbabilityMeasure Ψ₀],
        ConvWeak (fun n => adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀) (Measure.dirac 0) := by
  intro δ
  have h1 : δ ≤ 1 := measureReal_le_one
  have hMk : IsMarkovKernel (creditKernel μ ζ R) := isMarkovKernel_creditKernel ζ R
  have hM : ConditionMFor (creditKernel μ ζ R) 1 δ := cutoffKernel_conditionM ζ _ 0 hδ
  obtain ⟨huniq, hconv⟩ :=
    invariant_unique_of_conditionM_one hM (Measure.dirac 0) (adjointOp_creditKernel_dirac ζ R)
  have hbound : ∀ (Ψ₀ : Measure ℝ) [IsProbabilityMeasure Ψ₀] (f : ℝ →ᵇ ℝ) (n : ℕ),
      |∫ w, f w ∂adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀ - f 0| ≤
        2 * ‖f‖ * (1 - δ) ^ n := by
    intro Ψ₀ _ f n
    have := isProb_adjoint (κ := creditKernel μ ζ R) n Ψ₀
    have h := abs_integral_sub_le_norm_mul_tvDist
      (adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀) (Measure.dirac 0) f
    rw [integral_dirac] at h
    calc _ ≤ ‖f‖ * tvDist (adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀) (Measure.dirac 0) := h
      _ ≤ ‖f‖ * (2 * (1 - δ) ^ n) := mul_le_mul_of_nonneg_left (hconv Ψ₀ n) (norm_nonneg f)
      _ = 2 * ‖f‖ * (1 - δ) ^ n := by ring
  refine ⟨hM, adjointOp_creditKernel_dirac ζ R, huniq, hconv, hbound, fun Ψ₀ _ f => ?_⟩
  rw [integral_dirac, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n => 2 * ‖f‖ * (1 - δ) ^ n) (fun n => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]
    exact hbound Ψ₀ f n) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - δ) (by linarith)
    (by linarith)).const_mul (2 * ‖f‖)

/-- **Exercise 13.7(b), the book's claim is false.** It is not true that for every `Ψ₀`
satisfying (1) the sequence `{T*ⁿΨ₀}` fails to converge weakly to an invariant measure: for
`Ψ₀ = δ₁` (`∫ w dΨ₀ = 1`) it converges weakly to the invariant `δ₀` (`ex_13_7b`). -/
theorem ex_13_7b_counterexample {ζ R : ℝ} (hδ : 0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)}) :
    ¬ ∀ Ψ₀ : Measure ℝ, IsProbabilityMeasure Ψ₀ → ∫ w, w ∂Ψ₀ = 1 →
      ¬ ∃ l : Measure ℝ, adjointOp (creditKernel μ ζ R) l = l ∧
        ConvWeak (fun n => adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀) l := by
  intro h
  obtain ⟨-, hinv, -, -, -, hweak⟩ := ex_13_7b (μ := μ) (R := R) hδ
  exact h (Measure.dirac 1) inferInstance (by rw [integral_dirac]) ⟨_, hinv, hweak _⟩

/-- **Exercise 13.7(b), the manual's "not Feller" claim is false.** `P` is Feller:
`Tf(w) = μ([0, ζ)) f(Rw) + μ([ζ, 1]) f(0)` is continuous for continuous bounded `f`. What fails
(when `μ([0, ζ)) > 0` and `R ≠ 0`) is only continuity of `w ↦ P(w, {0})` (it is `δ` off `0` and
`1` at `0`), which the Feller property does not require. -/
theorem ex_13_7b_feller (ζ R : ℝ) :
    IsFeller (creditKernel μ ζ R) ∧
      (0 < μ.real {z : unitInterval | (z : ℝ) < ζ} → R ≠ 0 →
        ¬ Continuous fun w => (creditKernel μ ζ R w).real {0}) := by
  refine ⟨fun f hf ⟨M, hM⟩ => ?_, fun hp hR hcont => ?_⟩
  · have hT : markovOpR (creditKernel μ ζ R) f = fun w =>
        (μ {z : unitInterval | (z : ℝ) < ζ}).toReal * f (R * w) +
          (μ {z : unitInterval | ζ ≤ (z : ℝ)}).toReal * f 0 := by
      funext w
      have hi : ∀ a : ℝ, ∀ c : ℝ≥0∞, c ≠ ⊤ → Integrable f (c • Measure.dirac a) :=
        fun a c hc => (integrable_of_bounded hf.measurable hM).smul_measure hc
      rw [markovOpR, creditKernel_apply, integral_add_measure (hi _ _ (measure_ne_top _ _))
        (hi _ _ (measure_ne_top _ _)), integral_smul_measure, integral_smul_measure,
        integral_dirac, integral_dirac, smul_eq_mul, smul_eq_mul]
    rw [hT]
    have hm : Continuous fun w : ℝ => R * w := continuous_const.mul continuous_id
    exact (continuous_const.mul (hf.comp hm)).add continuous_const
  · set g : ℝ → ℝ := fun w => (creditKernel μ ζ R w).real {0} with hg
    have hg0 : g 0 = 1 := by
      simp [hg, creditKernel_zero]
    have hgw : ∀ w : ℝ, w ≠ 0 → g w = μ.real {z : unitInterval | ζ ≤ (z : ℝ)} := by
      intro w hw
      have : R * w ∉ ({0} : Set ℝ) := by simpa using mul_ne_zero hR hw
      simp only [hg, measureReal_def, creditKernel_apply, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply, indicator_of_notMem this, smul_eq_mul]
      simp
    have ht : Tendsto (fun n : ℕ => g (1 / ((n : ℝ) + 1))) atTop (𝓝 (g 0)) :=
      (hcont.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : (fun n : ℕ => g (1 / ((n : ℝ) + 1))) =
        fun _ => μ.real {z : unitInterval | ζ ≤ (z : ℝ)} :=
      funext fun n => hgw _ (by positivity)
    rw [hc, hg0] at ht
    have h1 := tendsto_nhds_unique ht tendsto_const_nhds
    have h2 := measureReal_lt_eq (μ := μ) ζ
    linarith

/-! ### Exercise 13.7(c): equilibrium -/

/-- The **market-clearing condition** (1) of §13.7, `∫ w Ψ(dw) = 1`, written for the mean of the
nonnegative part (for `Ψ` on `ℝ₊` this is the mean). -/
def MarketClears (Ψ : Measure ℝ) : Prop := ∫⁻ w, ENNReal.ofReal w ∂Ψ = 1

/-- **The mean recursion.** Under (3), `∫ w Ψ_{t+1}(dw) = R μ([0, ζ)) ∫ w Ψ_t(dw)`: savers multiply
their holdings by `R`, sellers drop to `0`. -/
theorem lintegral_creditKernel_mean (ζ : ℝ) {R : ℝ} (hR : 0 ≤ R) (Ψ : Measure ℝ) :
    ∫⁻ w, ENNReal.ofReal w ∂adjointOp (creditKernel μ ζ R) Ψ =
      ENNReal.ofReal (R * μ.real {z : unitInterval | (z : ℝ) < ζ}) *
        ∫⁻ w, ENNReal.ofReal w ∂Ψ := by
  rw [adjointOp, Measure.lintegral_bind (Kernel.aemeasurable _)
    ENNReal.measurable_ofReal.aemeasurable, ← lintegral_const_mul _ ENNReal.measurable_ofReal]
  refine lintegral_congr fun w => ?_
  rw [creditKernel_apply, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, ENNReal.ofReal_zero, smul_eq_mul, smul_eq_mul, mul_zero,
    add_zero, ENNReal.ofReal_mul hR, ENNReal.ofReal_mul hR, ofReal_measureReal]
  ring

/-- Iterating: `∫ w Ψₜ(dw) = (R μ([0, ζ)))ᵗ ∫ w Ψ₀(dw)`. -/
theorem lintegral_creditKernel_mean_iterate (ζ : ℝ) {R : ℝ} (hR : 0 ≤ R) (Ψ₀ : Measure ℝ)
    (t : ℕ) :
    ∫⁻ w, ENNReal.ofReal w ∂adjointOp (kpow (creditKernel μ ζ R) t) Ψ₀ =
      ENNReal.ofReal (R * μ.real {z : unitInterval | (z : ℝ) < ζ}) ^ t *
        ∫⁻ w, ENNReal.ofReal w ∂Ψ₀ := by
  rw [← adjointOp_iterate]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', lintegral_creditKernel_mean ζ hR, ih, pow_succ]
    ring

/-- **(1) at every date.** If `Ψ₀` satisfies (1), then `Ψₜ = T*ᵗΨ₀` satisfies (1) for all `t` iff
`R μ([0, ζ)) = 1`. -/
theorem marketClears_iterate_iff (ζ : ℝ) {R : ℝ} (hR : 0 ≤ R) {Ψ₀ : Measure ℝ}
    (h0 : MarketClears Ψ₀) :
    (∀ t : ℕ, MarketClears (adjointOp (kpow (creditKernel μ ζ R) t) Ψ₀)) ↔
      R * μ.real {z : unitInterval | (z : ℝ) < ζ} = 1 := by
  unfold MarketClears at *
  simp only [lintegral_creditKernel_mean_iterate ζ hR, h0, mul_one]
  constructor
  · intro h
    have := h 1
    rwa [pow_one, ENNReal.ofReal_eq_one] at this
  · intro h t
    rw [h, ENNReal.ofReal_one, one_pow]

/-- **Exercise 13.7(b), the corrected statement.** Suppose `δ = μ([ζ, 1]) > 0` and
`R μ([0, ζ)) = 1` (as in an equilibrium, part (c)), and `Ψ₀` satisfies (1). Then every `Ψₙ = T*ⁿΨ₀`
satisfies (1), yet `Ψₙ ⇒ δ₀` weakly and `δ₀` does not satisfy (1); indeed no invariant probability
measure satisfies (1). So `{T*ⁿΨ₀}` does not converge weakly to an invariant measure **satisfying
(1)**: the mass that escapes to ever larger `w` is lost in the weak limit. -/
theorem ex_13_7b_corrected {ζ R : ℝ} (hδ : 0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)})
    (hR : 0 ≤ R) (hclear : R * μ.real {z : unitInterval | (z : ℝ) < ζ} = 1) (Ψ₀ : Measure ℝ)
    [IsProbabilityMeasure Ψ₀] (h0 : MarketClears Ψ₀) :
    (∀ n : ℕ, MarketClears (adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀)) ∧
      ConvWeak (fun n => adjointOp (kpow (creditKernel μ ζ R) n) Ψ₀) (Measure.dirac 0) ∧
      ¬ MarketClears (Measure.dirac 0) ∧
      ∀ l : Measure ℝ, IsProbabilityMeasure l → adjointOp (creditKernel μ ζ R) l = l →
        ¬ MarketClears l := by
  obtain ⟨-, -, huniq, -, -, hweak⟩ := ex_13_7b (μ := μ) (R := R) hδ
  have hd : ¬ MarketClears (Measure.dirac 0) := by
    simp [MarketClears, lintegral_dirac]
  refine ⟨(marketClears_iterate_iff ζ hR h0).2 hclear, hweak Ψ₀, hd, fun l hl hinv => ?_⟩
  rw [huniq l hl hinv]
  exact hd

/-- A **stationary equilibrium with a constant asset price** (Exercise 13.7(c)): `q > 0`, the
cutoff `ζ ∈ (0, 1)` of (3) solves `ζ = βR H(ζ)` with `R = 1 + y/q`, and (1) is preserved,
`R μ([0, ζ)) = 1`. -/
structure CreditEqm (β y : ℝ) (μ : Measure unitInterval) (q ζ : ℝ) : Prop where
  q_pos : 0 < q
  mem : ζ ∈ Ioo (0 : ℝ) 1
  cutoff : ζ = β * (1 + y / q) * maxInt μ ζ
  clearing : (1 + y / q) * μ.real {z : unitInterval | (z : ℝ) < ζ} = 1

/-- `H(ζ) = ζ μ([0, ζ)) + ∫_{[ζ, 1]} z μ(dz)`. -/
theorem maxInt_eq_split (ζ : ℝ) :
    maxInt μ ζ = ζ * μ.real {z : unitInterval | (z : ℝ) < ζ} +
      ∫ z in {z : unitInterval | ζ ≤ (z : ℝ)}, (z : ℝ) ∂μ := by
  have hs : MeasurableSet {z : unitInterval | (z : ℝ) < ζ} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have ht : MeasurableSet {z : unitInterval | ζ ≤ (z : ℝ)} :=
    measurableSet_le measurable_const measurable_subtype_coe
  have hfun : (fun z : unitInterval => max ζ (z : ℝ)) = fun z =>
      {z : unitInterval | (z : ℝ) < ζ}.indicator (fun _ => ζ) z +
        {z : unitInterval | ζ ≤ (z : ℝ)}.indicator (fun z => (z : ℝ)) z := by
    funext z
    by_cases hz : (z : ℝ) < ζ
    · have : z ∉ {z : unitInterval | ζ ≤ (z : ℝ)} := by simpa using hz
      rw [indicator_of_mem (show z ∈ {z : unitInterval | (z : ℝ) < ζ} from hz),
        indicator_of_notMem this, max_eq_left hz.le, add_zero]
    · have : z ∉ {z : unitInterval | (z : ℝ) < ζ} := hz
      rw [indicator_of_notMem this, indicator_of_mem (show z ∈ {z : unitInterval | ζ ≤ (z : ℝ)}
        from not_lt.1 hz), max_eq_right (not_lt.1 hz), zero_add]
  rw [maxInt, hfun, integral_add ((integrable_const ζ).indicator hs)
    (integrable_coe_unit.indicator ht), integral_indicator_const _ hs, integral_indicator ht,
    smul_eq_mul, mul_comm]

/-- **Exercise 13.7(c).** In an equilibrium `(q, ζ)` (with `y > 0`, `β < 1`): the policy (3) solves
(2) at every date; for every `Ψ₀` satisfying (1), (1) holds for `Ψₜ = T*ᵗΨ₀` at all `t`; the cutoff
satisfies `(1 − β) ζ μ([0, ζ)) = β ∫_{[ζ, 1]} z μ(dz)`; and `q = y μ([0, ζ))/μ([ζ, 1])`, which does
not involve `Ψ₀`. -/
theorem ex_13_7c {β y q ζ : ℝ} (hy : 0 < y) (h : CreditEqm β y μ q ζ) :
    SatisfiesCreditBellman β y q μ (creditValue y q ζ) ∧
      (∀ Ψ₀ : Measure ℝ, MarketClears Ψ₀ →
        ∀ t : ℕ, MarketClears (adjointOp (kpow (creditKernel μ ζ (1 + y / q)) t) Ψ₀)) ∧
      (1 - β) * ζ * μ.real {z : unitInterval | (z : ℝ) < ζ} =
        β * ∫ z in {z : unitInterval | ζ ≤ (z : ℝ)}, (z : ℝ) ∂μ ∧
      0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)} ∧
      q = y * μ.real {z : unitInterval | (z : ℝ) < ζ} /
        μ.real {z : unitInterval | ζ ≤ (z : ℝ)} := by
  obtain ⟨hq, hζ, hcut, hclear⟩ := h
  have hR0 : 0 ≤ 1 + y / q := by positivity
  have hp := measureReal_lt_eq (μ := μ) ζ
  set p := μ.real {z : unitInterval | (z : ℝ) < ζ}
  set δ := μ.real {z : unitInterval | ζ ≤ (z : ℝ)}
  have hδ : 0 < δ := by
    by_contra h0
    have : p = 1 := by
      linarith [measureReal_nonneg (μ := μ) (s := {z : unitInterval | ζ ≤ (z : ℝ)})]
    rw [this, mul_one] at hclear
    have : 0 < y / q := div_pos hy hq
    linarith
  refine ⟨(ex_13_7a hy.le hq hcut).1, fun Ψ₀ h0 => (marketClears_iterate_iff ζ hR0 h0).2 hclear,
    ?_, hδ, ?_⟩
  · have hs := maxInt_eq_split (μ := μ) ζ
    have e : ζ * p = β * maxInt μ ζ := by
      calc ζ * p = β * (1 + y / q) * maxInt μ ζ * p := by rw [← hcut]
        _ = β * maxInt μ ζ * ((1 + y / q) * p) := by ring
        _ = β * maxInt μ ζ := by rw [hclear, mul_one]
    rw [hs] at e
    linarith
  · have hpos : 0 < p := by
      by_contra h0
      have : p = 0 := le_antisymm (not_lt.1 h0) measureReal_nonneg
      rw [this, mul_zero] at hclear
      exact zero_ne_one hclear
    have hc2 : q * p + y * p = q := by
      have e : (1 + y / q) * p * q = q * p + y * p * (q / q) := by ring
      rw [div_self hq.ne', mul_one, hclear, one_mul] at e
      linarith
    have key : y * p = q * δ := by linear_combination hc2 - q * hp
    rw [key, mul_div_assoc, div_self hδ.ne', mul_one]

/-- **Exercise 13.7(c): `βR < 1` holds automatically** in an equilibrium, when `μ` charges every
`(a, 1]` (true under the density condition of §13.5): `ζ ∈ (0, 1)` solves the cutoff equation,
so `ex_13_7a_cutoff` applies. -/
theorem ex_13_7c_betaR {β y q ζ : ℝ} (hβ0 : 0 < β) (hy : 0 < y) (hE : 0 < ∫ z, (z : ℝ) ∂μ)
    (hsupp : ∀ a : ℝ, a < 1 → 0 < μ {z : unitInterval | a < (z : ℝ)}) (h : CreditEqm β y μ q ζ) :
    β * (1 + y / q) < 1 :=
  ((ex_13_7a_cutoff hβ0 (by have := h.q_pos; positivity) hE hsupp).1).1 ⟨ζ, h.mem, h.cutoff⟩

/-- The two-atom distribution `μ₀ = ½δ_{1/2} + ½δ₀` on `Z = [0, 1]`. -/
noncomputable def twoAtomMeasure : Measure unitInterval :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac halfUnitInterval + (1 / 2 : ℝ≥0∞) • Measure.dirac 0

/-- `∫ f dμ₀ = ½ f(1/2) + ½ f(0)`. -/
theorem integral_twoAtomMeasure (f : unitInterval → ℝ) :
    ∫ z, f z ∂twoAtomMeasure = 1 / 2 * f halfUnitInterval + 1 / 2 * f 0 := by
  rw [twoAtomMeasure, integral_add_measure ((integrable_dirac enorm_lt_top).smul_measure
    (by simp)) ((integrable_dirac enorm_lt_top).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp

/-- **Exercise 13.7(c): "`βR < 1` holds automatically" needs a condition on `μ`.** For
`μ₀ = ½δ_{1/2} + ½δ₀` (which violates the density condition), `β = 1/2` and any `y > 0`,
`(q, ζ) = (y, 1/2)` is an equilibrium in the sense of `CreditEqm`, but `βR = β(1 + y/q) = 1`. -/
theorem ex_13_7c_betaR_counterexample {y : ℝ} (hy : 0 < y) :
    IsProbabilityMeasure twoAtomMeasure ∧ 0 < ∫ z, (z : ℝ) ∂twoAtomMeasure ∧
      CreditEqm (1 / 2) y twoAtomMeasure y (1 / 2) ∧ ¬ (1 / 2 * (1 + y / y) < 1) := by
  have hyy : y / y = 1 := div_self hy.ne'
  have hhalf : ((halfUnitInterval : unitInterval) : ℝ) = 1 / 2 := rfl
  have hH : maxInt twoAtomMeasure (1 / 2) = 1 / 2 := by
    rw [maxInt, integral_twoAtomMeasure, hhalf]
    norm_num
  have hP : twoAtomMeasure.real {z : unitInterval | (z : ℝ) < 1 / 2} = 1 / 2 := by
    have h1 : halfUnitInterval ∉ {z : unitInterval | (z : ℝ) < 1 / 2} := by
      simp [hhalf]
    have h2 : (0 : unitInterval) ∈ {z : unitInterval | (z : ℝ) < 1 / 2} := by
      simp
    rw [measureReal_def, twoAtomMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.dirac_apply, Measure.dirac_apply, indicator_of_notMem h1,
      indicator_of_mem h2]
    simp
  refine ⟨⟨?_⟩, ?_, ⟨hy, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩, ?_⟩
  · simp [twoAtomMeasure, ENNReal.inv_two_add_inv_two]
  · rw [integral_twoAtomMeasure, hhalf]
    norm_num
  · rw [hH, hyy]
    norm_num
  · rw [hP, hyy]
    norm_num
  · rw [hyy]
    norm_num

/-- With a continuous distribution function `a ↦ μ([0, a))`, `μ([0, a]) ≤ μ([0, a))`: take right
limits. -/
theorem measureReal_le_le_lt
    (hcont : Continuous fun a : ℝ => μ.real {z : unitInterval | (z : ℝ) < a}) (a : ℝ) :
    μ.real {z : unitInterval | (z : ℝ) ≤ a} ≤ μ.real {z : unitInterval | (z : ℝ) < a} :=
  ge_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun b : ℝ => μ.real {z : unitInterval | (z : ℝ) < b}) (𝓝[>] a) _)
    (eventually_nhdsWithin_of_forall fun b hb =>
      measureReal_mono fun z (hz : (z : ℝ) ≤ a) => show (z : ℝ) < b from hz.trans_lt hb)

/-- **Exercise 13.7(c), existence.** Suppose `0 < β < 1`, `y > 0`, `∫ z dμ > 0`, and the
distribution function `a ↦ μ([0, a))` is continuous (`μ` has no atoms). Then an equilibrium
`(q, ζ)` exists: `F(ζ) = ζ μ([0, ζ)) − βH(ζ)` is continuous with `F(0) = −β∫z dμ < 0` and
`F(1) = 1 − β > 0`, so it has a root `ζ ∈ (0, 1)`; then `0 < μ([0, ζ)) < 1` and
`q = y μ([0, ζ))/μ([ζ, 1])`. -/
theorem ex_13_7c_exists {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hE : 0 < ∫ z, (z : ℝ) ∂μ)
    (hcont : Continuous fun a : ℝ => μ.real {z : unitInterval | (z : ℝ) < a}) :
    ∃ q ζ : ℝ, CreditEqm β y μ q ζ := by
  set P : ℝ → ℝ := fun a => μ.real {z : unitInterval | (z : ℝ) < a} with hP
  set F : ℝ → ℝ := fun a => a * P a - β * maxInt μ a with hF
  have hFc : Continuous F := (continuous_id.mul hcont).sub (continuous_const.mul continuous_maxInt)
  have hP0 : P 0 = 0 := by
    have : {z : unitInterval | (z : ℝ) < 0} = ∅ := by
      ext z
      simpa using z.2.1
    simp [hP, this]
  have hP1 : P 1 = 1 := by
    have h1 := measureReal_le_le_lt hcont 1
    have : {z : unitInterval | (z : ℝ) ≤ 1} = univ := by
      ext z
      simpa using z.2.2
    rw [this, probReal_univ] at h1
    exact le_antisymm measureReal_le_one h1
  have hF0 : F 0 < 0 := by
    simp only [hF, hP0, mul_zero, zero_sub, maxInt_zero, neg_lt_zero]
    positivity
  have hF1 : 0 < F 1 := by
    simp only [hF, hP1, mul_one, maxInt_of_one_le le_rfl]
    linarith
  obtain ⟨ζ, hζ, hFζ⟩ := intermediate_value_Ioo zero_le_one hFc.continuousOn ⟨hF0, hF1⟩
  simp only [hF] at hFζ
  have hpos : 0 < P ζ := by
    by_contra h0
    have : P ζ = 0 := le_antisymm (not_lt.1 h0) measureReal_nonneg
    rw [this, mul_zero, zero_sub, neg_eq_zero] at hFζ
    have := le_maxInt (μ := μ) ζ
    nlinarith [hζ.1]
  have hlt : P ζ < 1 := by
    rcases (measureReal_le_one (μ := μ) (s := {z : unitInterval | (z : ℝ) < ζ})).lt_or_eq
      with h1 | h1
    · exact h1
    · exfalso
      have hcut : ζ = β * maxInt μ ζ := by
        change ζ * μ.real {z : unitInterval | (z : ℝ) < ζ} - β * maxInt μ ζ = 0 at hFζ
        rw [h1, mul_one] at hFζ
        linarith
      have := delta_pos_of_cutoff hβ1 hζ.1 hcut
      have h2 := measureReal_lt_eq (μ := μ) ζ
      change P ζ = 1 at h1
      simp only [hP] at h1
      linarith
  have h1p : 0 < 1 - P ζ := by linarith
  refine ⟨y * P ζ / (1 - P ζ), ζ, ⟨by positivity, hζ, ?_, ?_⟩⟩
  · have hR : 1 + y / (y * P ζ / (1 - P ζ)) = 1 / P ζ := by
      field_simp
      ring
    rw [hR]
    field_simp
    linarith
  · have hR : 1 + y / (y * P ζ / (1 - P ζ)) = 1 / P ζ := by
      field_simp
      ring
    change (1 + y / (y * P ζ / (1 - P ζ))) * P ζ = 1
    rw [hR]
    field_simp

/-- **Exercise 13.7(c), uniqueness.** All equilibria (for any endowments `y, y′ > 0`) have the
same cutoff `ζ` and the same price–endowment ratio `q/y = μ([0, ζ))/μ([ζ, 1])`:
`G(ζ) = (1 − β)ζμ([0, ζ)) − β∫_{[ζ, 1]} z dμ` is strictly increasing on `{μ([0, ζ)) > 0}`. -/
theorem ex_13_7c_unique {β y y' q q' ζ ζ' : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hy : 0 < y)
    (hy' : 0 < y') (h : CreditEqm β y μ q ζ) (h' : CreditEqm β y' μ q' ζ') :
    ζ = ζ' ∧ q / y = q' / y' := by
  obtain ⟨-, -, G, hδ, hq⟩ := ex_13_7c hy h
  obtain ⟨-, -, G', hδ', hq'⟩ := ex_13_7c hy' h'
  have hppos : ∀ {y q ζ : ℝ}, CreditEqm β y μ q ζ → 0 < μ.real {z : unitInterval | (z : ℝ) < ζ} :=
    fun {y q ζ} h => by
      have := h.clearing
      by_contra h0
      have h00 : μ.real {z : unitInterval | (z : ℝ) < ζ} = 0 :=
        le_antisymm (not_lt.1 h0) measureReal_nonneg
      rw [h00, mul_zero] at this
      exact zero_ne_one this
  have hmono : ∀ {a b : ℝ}, a ≤ b →
      μ.real {z : unitInterval | (z : ℝ) < a} ≤ μ.real {z : unitInterval | (z : ℝ) < b} ∧
        ∫ z in {z : unitInterval | b ≤ (z : ℝ)}, (z : ℝ) ∂μ ≤
          ∫ z in {z : unitInterval | a ≤ (z : ℝ)}, (z : ℝ) ∂μ := fun {a b} hab =>
    ⟨measureReal_mono fun z (hz : (z : ℝ) < a) => show (z : ℝ) < b from hz.trans_le hab,
      setIntegral_mono_set integrable_coe_unit.integrableOn
        (Eventually.of_forall fun z => z.2.1)
        (Eventually.of_forall fun z (hz : b ≤ (z : ℝ)) => (hab.trans hz : a ≤ (z : ℝ)))⟩
  have hζeq : ζ = ζ' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨hp, hI⟩ := hmono hlt.le
      have := hppos h
      nlinarith [mul_pos (sub_pos.2 hβ1) (mul_pos (sub_pos.2 hlt) this),
        mul_le_mul_of_nonneg_left hp (mul_nonneg (sub_pos.2 hβ1).le h'.mem.1.le)]
    · obtain ⟨hp, hI⟩ := hmono hlt.le
      have := hppos h'
      nlinarith [mul_pos (sub_pos.2 hβ1) (mul_pos (sub_pos.2 hlt) this),
        mul_le_mul_of_nonneg_left hp (mul_nonneg (sub_pos.2 hβ1).le h.mem.1.le)]
  subst hζeq
  refine ⟨rfl, ?_⟩
  rw [hq, hq']
  field_simp

omit [IsProbabilityMeasure μ] in
/-- **Exercise 13.7(c), the price is proportional to `y`.** `(q, ζ)` is an equilibrium for the
endowment `y` iff `(cq, ζ)` is one for `cy` (`c > 0`): only `y/q` enters. -/
theorem ex_13_7c_scaling {β y q ζ c : ℝ} (hc : 0 < c) :
    CreditEqm β y μ q ζ ↔ CreditEqm β (c * y) μ (c * q) ζ := by
  have e : c * y / (c * q) = y / q := mul_div_mul_left y q hc.ne'
  constructor
  · rintro ⟨hq, hζ, hcut, hcl⟩
    exact ⟨mul_pos hc hq, hζ, by rwa [e], by rwa [e]⟩
  · rintro ⟨hq, hζ, hcut, hcl⟩
    exact ⟨pos_of_mul_pos_right hq hc.le, hζ, by rwa [e] at hcut, by rwa [e] at hcl⟩

omit [IsProbabilityMeasure μ] in
/-- **Exercise 13.7(c), correction: `q` is not determined by `β` and `μ` alone.** If an
equilibrium exists for some endowment, no single price `Q` is the equilibrium price for every
`y > 0`: doubling `y` doubles `q`. (What `β` and `μ` determine is `q/y`, `ex_13_7c_unique`.) -/
theorem ex_13_7c_counterexample {β : ℝ} (hex : ∃ y : ℝ, 0 < y ∧ ∃ q ζ, CreditEqm β y μ q ζ) :
    ¬ ∃ Q : ℝ, ∀ y : ℝ, 0 < y → ∀ q ζ : ℝ, CreditEqm β y μ q ζ → q = Q := by
  rintro ⟨Q, hQ⟩
  obtain ⟨y, hy, q, ζ, h⟩ := hex
  have h2 := (ex_13_7c_scaling (c := 2) (by norm_num)).1 h
  have e1 := hQ y hy q ζ h
  have e2 := hQ (2 * y) (by positivity) (2 * q) ζ h2
  have := h.q_pos
  linarith

end StokeyLucasPrescott.ConvergenceApplications
