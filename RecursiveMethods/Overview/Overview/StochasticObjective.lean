/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.StochasticLog

/-!
# The objective (2) along policy (5)

SLP §2.2, (2), p. 17, and Exercise 2.6, p. 19.

Exercise 2.6 asks for "the value of the objective function (2)", `E[∑ βᵗ U(c_t)]`, along policy
(5) from `k₀ = k`, `z₀ = z`, and calls it `v(k, z)`. `hasSum_expected_utility` computes
`∑ βᵗ E[ln c_t] = v(k, z)`; here the expectation is taken outside the sum, as in (2).

The bound is `E|ln c_t| ≤ D` uniformly in `t` (with `α < 1`, `E|ln k_t|` stays bounded), so
`∑ βᵗ E|ln c_t| < ∞` and expectation and sum can be exchanged (Fubini–Tonelli for series).

* `ae_summable_norm_of_summable_integral_norm`, `integrable_tsum_of_summable_integral_norm`:
  if `∑ₙ E|fₙ| < ∞` then `∑ₙ |fₙ|` is a.e. finite and `∑ₙ fₙ` is integrable.
* `integral_abs_log_shock_le`, `integral_abs_log_path_le`, `integral_abs_log_cons_le`:
  `E|ln z_t| ≤ Z`, `E|ln k_t| ≤ K`, `E|ln c_t| ≤ D` for all `t`.
* `ae_summable_utility`: almost surely `∑ βᵗ ln c_t(ω)` converges absolutely.
* `integrable_utility`: `ω ↦ ∑ βᵗ ln c_t(ω)` is integrable.
* `hasSum_integral_utility`, `integral_tsum_utility`: `E[∑ βᵗ ln c_t] = ∑ βᵗ E[ln c_t]`.
* `integral_utility_eq_stochValue` (Ex 2.6): `E[∑ βᵗ ln c_t] = v(k, z) = A + B ln k + C ln z`,
  the function of `StochasticLog` that satisfies (3).
-/

namespace StokeyLucasPrescott.Overview

open Finset Set Filter Topology Real MeasureTheory ProbabilityTheory

/-- If the integrable `fₙ` have `∑ₙ E|fₙ| < ∞`, then `∫⁻ ∑ₙ ‖fₙ‖ₑ < ∞` and almost surely
`∑ₙ |fₙ(ω)|` converges. -/
theorem ae_summable_norm_of_summable_integral_norm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} (hf : ∀ n, Integrable (f n) P)
    (hs : Summable fun n => ∫ ω, ‖f n ω‖ ∂P) :
    (∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂P ≠ ⊤) ∧ ∀ᵐ ω ∂P, Summable fun n => ‖f n ω‖ := by
  have htop : ∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hf n).1.enorm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun ω => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨htop, ?_⟩
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun n => (hf n).1.enorm) htop] with ω hω
  exact tsum_enorm_ne_top_iff_summable_norm.1 hω.ne

/-- If the integrable `fₙ` have `∑ₙ E|fₙ| < ∞`, then `ω ↦ ∑ₙ fₙ(ω)` is integrable. -/
theorem integrable_tsum_of_summable_integral_norm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} (hf : ∀ n, Integrable (f n) P)
    (hs : Summable fun n => ∫ ω, ‖f n ω‖ ∂P) :
    Integrable (fun ω => ∑' n, f n ω) P := by
  obtain ⟨htop, hae⟩ := ae_summable_norm_of_summable_integral_norm hf hs
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ n ∈ range N, f n ω)
    (fun N => (integrable_finsetSum (range N) fun n _ => hf n).1) ?_, ?_⟩
  · filter_upwards [hae] with ω hω
    exact hω.of_norm.hasSum.tendsto_sum_nat
  · rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono fun ω => enorm_tsum_le_tsum_enorm).trans_lt htop.lt_top

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- `|ln z_t|` is integrable and `E|ln z_t| ≤ |ln z| + E_μ|ln z′|` for every `t`. -/
theorem integral_abs_log_shock_le (hint : Integrable log μ) (z : ℝ) (t : ℕ) :
    Integrable (fun ω => |log (shock z ω t)|) (shockMeasure μ) ∧
      ∫ ω, |log (shock z ω t)| ∂shockMeasure μ ≤ |log z| + ∫ x, |log x| ∂μ := by
  refine ⟨(integrable_log_shock hint z t).abs, ?_⟩
  have h0 : 0 ≤ ∫ x, |log x| ∂μ := integral_nonneg fun x => abs_nonneg _
  rcases t with _ | t
  · simp [shock, h0]
  · have e : ∫ ω, |log (ω (t + 1))| ∂shockMeasure μ = ∫ x, |log x| ∂μ := by
      rw [← integral_map (φ := fun ω : ℕ → ℝ => ω (t + 1)) (f := fun x => |log x|)
        (measurable_pi_apply (t + 1)).aemeasurable
        (continuous_abs.measurable.comp measurable_log).aestronglyMeasurable,
        Measure.infinitePi_map_eval]
    simp only [shock, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [e]
    linarith [abs_nonneg (log z)]

/-- Along policy (5), `E|ln k_t| ≤ K = |ln k| + (|ln(αβ)| + Z)/(1 − α)` for every `t`, where
`Z = |ln z| + E_μ|ln z′|`: `E|ln k_{t+1}| ≤ |ln(αβ)| + Z + αE|ln k_t|` and `K` is a fixed point
bound for this recursion. -/
theorem integral_abs_log_path_le (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    ∫ ω, |log (stochPath α β k z ω t)| ∂shockMeasure μ ≤
      |log k| + (|log (α * β)| + (|log z| + ∫ x, |log x| ∂μ)) / (1 - α) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  set Z := |log z| + ∫ x, |log x| ∂μ
  set K := |log k| + (|log (α * β)| + Z) / (1 - α)
  have hK : |log (α * β)| + Z + α * K ≤ K := by
    have : (1 - α) * K = (1 - α) * |log k| + (|log (α * β)| + Z) := by
      simp only [K]; field_simp
    nlinarith [abs_nonneg (log k)]
  induction t with
  | zero =>
    simp only [stochPath, integral_const, probReal_univ, smul_eq_mul, one_mul, K]
    have : 0 ≤ (|log (α * β)| + Z) / (1 - α) := by
      apply div_nonneg _ h1α.le
      have : 0 ≤ ∫ x, |log x| ∂μ := integral_nonneg fun x => abs_nonneg _
      positivity
    linarith
  | succ t ih =>
    have hi := (integral_log_path hpos hint h0 hk hz t).1
    have hi' := (integral_log_path hpos hint h0 hk hz (t + 1)).1
    have hs := integral_abs_log_shock_le hint z t
    have hle : (fun ω => |log (stochPath α β k z ω (t + 1))|) ≤ᵐ[shockMeasure μ]
        fun ω => |log (α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)| := by
      filter_upwards [ae_log_path hpos h0 hk hz] with ω hω
      rw [(hω t).2.2]
      calc |log (α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t)|
          ≤ |log (α * β) + log (shock z ω t)| + |α * log (stochPath α β k z ω t)| :=
            abs_add_le _ _
        _ ≤ _ := by
            rw [abs_mul, abs_of_pos hα]
            linarith [abs_add_le (log (α * β)) (log (shock z ω t))]
    have hA : Integrable (fun ω => |log (α * β)| + |log (shock z ω t)|) (shockMeasure μ) :=
      (integrable_const _).add hs.1
    have hB := hi.abs.const_mul α
    calc ∫ ω, |log (stochPath α β k z ω (t + 1))| ∂shockMeasure μ
        ≤ ∫ ω, |log (α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)|
            ∂shockMeasure μ := integral_mono_ae hi'.abs (hA.add hB) hle
      _ = |log (α * β)| + ∫ ω, |log (shock z ω t)| ∂shockMeasure μ +
            α * ∫ ω, |log (stochPath α β k z ω t)| ∂shockMeasure μ := by
          rw [integral_add hA hB, integral_add (integrable_const _) hs.1, integral_const,
            integral_const_mul]
          simp
      _ ≤ |log (α * β)| + Z + α * K := by
          have := mul_le_mul_of_nonneg_left ih hα.le
          linarith [hs.2]
      _ ≤ K := hK


/-- Almost surely `ln c_t = ln(1 − αβ) + ln z_t + α ln k_t` along policy (5). -/
theorem ae_log_cons (hpos : ∀ᵐ z ∂μ, 0 < z) {α β k z : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1)
    (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    (fun ω => log (stochCons α β k z ω t)) =ᵐ[shockMeasure μ]
      fun ω => log (1 - α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  filter_upwards [ae_log_path hpos h0 hk hz] with ω hω
  obtain ⟨hs, hp, -⟩ := hω t
  unfold stochCons
  rw [show shock z ω t * stochPath α β k z ω t ^ α - stochPath α β k z ω (t + 1) =
    (1 - α * β) * shock z ω t * stochPath α β k z ω t ^ α by simp only [stochPath]; ring,
    log_mul (mul_pos h1ab hs).ne' (rpow_pos_of_pos hp α).ne', log_mul h1ab.ne' hs.ne',
    log_rpow hp]

/-- Along policy (5), `ln c_t` is integrable and `E|ln c_t| ≤ |ln(1 − αβ)| + Z + αK` for every
`t`. -/
theorem integral_abs_log_cons_le (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) (t : ℕ) :
    Integrable (fun ω => log (stochCons α β k z ω t)) (shockMeasure μ) ∧
      ∫ ω, |log (stochCons α β k z ω t)| ∂shockMeasure μ ≤
        |log (1 - α * β)| + (|log z| + ∫ x, |log x| ∂μ) +
          α * (|log k| + (|log (α * β)| + (|log z| + ∫ x, |log x| ∂μ)) / (1 - α)) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1 : α * β < 1 := by nlinarith
  have heq := ae_log_cons hpos h0 h1 hk hz t (μ := μ)
  have hi := (integral_log_path hpos hint h0 hk hz t).1
  have hs := integral_abs_log_shock_le hint z t
  have hc : Integrable (fun ω => log (stochCons α β k z ω t)) (shockMeasure μ) :=
    (((integrable_const _).add (integrable_log_shock hint z t)).add (hi.const_mul α)).congr
      heq.symm
  refine ⟨hc, ?_⟩
  have hle : (fun ω => |log (stochCons α β k z ω t)|) ≤ᵐ[shockMeasure μ]
      fun ω => |log (1 - α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)| := by
    filter_upwards [heq] with ω hω
    rw [hω]
    calc |log (1 - α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t)|
        ≤ |log (1 - α * β) + log (shock z ω t)| + |α * log (stochPath α β k z ω t)| :=
          abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos hα]
          linarith [abs_add_le (log (1 - α * β)) (log (shock z ω t))]
  have hA : Integrable (fun ω => |log (1 - α * β)| + |log (shock z ω t)|) (shockMeasure μ) :=
    (integrable_const _).add hs.1
  have hB := hi.abs.const_mul α
  calc ∫ ω, |log (stochCons α β k z ω t)| ∂shockMeasure μ
      ≤ ∫ ω, |log (1 - α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)|
          ∂shockMeasure μ := integral_mono_ae hc.abs (hA.add hB) hle
    _ = |log (1 - α * β)| + ∫ ω, |log (shock z ω t)| ∂shockMeasure μ +
          α * ∫ ω, |log (stochPath α β k z ω t)| ∂shockMeasure μ := by
        rw [integral_add hA hB, integral_add (integrable_const _) hs.1, integral_const,
          integral_const_mul]
        simp
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left
          (integral_abs_log_path_le hpos hint hα hα1 hβ hk hz t) hα.le
        linarith [hs.2]

/-- Each `βᵗ ln c_t` is integrable and `∑ₜ E|βᵗ ln c_t| < ∞`. -/
theorem summable_integral_norm_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    (∀ t, Integrable (fun ω => β ^ t * log (stochCons α β k z ω t)) (shockMeasure μ)) ∧
      Summable fun t => ∫ ω, ‖β ^ t * log (stochCons α β k z ω t)‖ ∂shockMeasure μ := by
  set Dc := |log (1 - α * β)| + (|log z| + ∫ x, |log x| ∂μ) +
    α * (|log k| + (|log (α * β)| + (|log z| + ∫ x, |log x| ∂μ)) / (1 - α))
  have hb := fun t => integral_abs_log_cons_le hpos hint hα hα1 hβ hβ1 hk hz t (μ := μ)
  refine ⟨fun t => (hb t).1.const_mul _, ?_⟩
  refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _)
    (fun t => ?_) ((summable_geometric_of_lt_one hβ.le hβ1).mul_right Dc)
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hβ]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hb t).2 (pow_nonneg hβ.le t)


/-- **Ex 2.6.** Almost surely the discounted utility series `∑ βᵗ ln c_t(ω)` along policy (5)
converges absolutely. -/
theorem ae_summable_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    ∀ᵐ ω ∂shockMeasure μ, Summable fun t => |β ^ t * log (stochCons α β k z ω t)| := by
  obtain ⟨hi, hs⟩ := summable_integral_norm_utility hpos hint hα hα1 hβ hβ1 hk hz (μ := μ)
  simpa only [Real.norm_eq_abs] using (ae_summable_norm_of_summable_integral_norm hi hs).2

/-- **Ex 2.6.** The realized discounted utility `ω ↦ ∑ βᵗ ln c_t(ω)` along policy (5) is
integrable, so the objective (2) is a well-defined real number. -/
theorem integrable_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    Integrable (fun ω => ∑' t, β ^ t * log (stochCons α β k z ω t)) (shockMeasure μ) := by
  obtain ⟨hi, hs⟩ := summable_integral_norm_utility hpos hint hα hα1 hβ hβ1 hk hz (μ := μ)
  exact integrable_tsum_of_summable_integral_norm hi hs

/-- **Ex 2.6.** `∑ βᵗ E[ln c_t]` converges to `E[∑ βᵗ ln c_t]` along policy (5). -/
theorem hasSum_integral_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    HasSum (fun t => β ^ t * ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ)
      (∫ ω, ∑' t, β ^ t * log (stochCons α β k z ω t) ∂shockMeasure μ) := by
  obtain ⟨hi, hs⟩ := summable_integral_norm_utility hpos hint hα hα1 hβ hβ1 hk hz (μ := μ)
  simpa only [integral_const_mul] using hasSum_integral_of_summable_integral_norm hi hs

/-- **Ex 2.6.** `E[∑ βᵗ ln c_t] = ∑ βᵗ E[ln c_t]` along policy (5). -/
theorem integral_tsum_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    ∫ ω, ∑' t, β ^ t * log (stochCons α β k z ω t) ∂shockMeasure μ =
      ∑' t, β ^ t * ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ :=
  (hasSum_integral_utility hpos hint hα hα1 hβ hβ1 hk hz).tsum_eq.symm

/-- **Ex 2.6.** The objective (2), `E[∑ βᵗ ln c_t]`, under policy (5) from `(k, z)` is
`v(k, z) = A + B ln k + C ln z`. -/
theorem integral_utility_eq_stochValue (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    ∫ ω, ∑' t, β ^ t * log (stochCons α β k z ω t) ∂shockMeasure μ =
      stochValue α β (∫ z, log z ∂μ) k z :=
  (hasSum_integral_utility hpos hint hα hα1 hβ hβ1 hk hz).unique
    (hasSum_expected_utility hpos hint hα hα1 hβ hβ1 hk hz)

end StokeyLucasPrescott.Overview
