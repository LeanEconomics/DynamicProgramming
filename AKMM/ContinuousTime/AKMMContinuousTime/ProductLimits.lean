/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.GrowthRates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Products of one-period discount factors and their continuous limit

AKMM, Appendix 9.A.3 (pp. 844–845): dividing one period into subperiods of length `Δ` and
discounting each by `1 + r(tΔ)Δ`, `t = 1, …, T/Δ`, the book takes logs and argues
`−log ∏(1 + r(tΔ)Δ) = −Σ log(1 + r(tΔ)Δ) ≈ −Σ r(tΔ)Δ → −∫_0^T r`. Here, with `Δ = T/n`:

* the Riemann sums `Σ_{t=1}^n r(tΔ)Δ` converge to `∫_0^T r` for continuous `r`
  (`productLimits_riemann`), by uniform continuity on `[0, T]`;
* `|Σ log(1 + r(tΔ)Δ) − Σ r(tΔ)Δ| ≤ 2M²T²/n` (`M` a bound of `|r|`), using
  `|log(1 + x) − x| ≤ x²/(1 − |x|)` from `GrowthRates`, so
  `∏_{t=1}^n (1 + r(tΔ)Δ) → e^{∫_0^T r}` (`productLimits_product`);
* hence the continuous-time nPg discount `1/∏(1 + r(tΔ)Δ) → e^{−∫_0^T r}`
  (`appendix_9A3_product_limit`), and, for §9.4, the probability of no success in `n`
  independent trials with probabilities `λ(tΔ)Δ` tends to `e^{−∫_0^T λ}`
  (`productLimits_survival`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, Appendix 9.A.3, p. 845: for continuous `r` and `T > 0`, the Riemann sums with
right endpoints, `Σ_{i<n} r((i + 1)T/n)·T/n`, converge to `∫_0^T r`. -/
theorem productLimits_riemann {r : ℝ → ℝ} (hr : Continuous r) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, r ((i + 1) * (T / n)) * (T / n)) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, r s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn r (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hr.continuousOn
  obtain ⟨δ, hδ, hδr⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / (2 * T)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith
  set Δ := T / n with hΔdef
  have hΔ0 : 0 < Δ := div_pos hT hn0
  have hΔ : Δ < δ := by
    rw [hΔdef, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hnΔ : (n : ℝ) * Δ = T := by rw [hΔdef]; field_simp
  have hsplit : ∑ i ∈ Finset.range n, ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s =
      ∫ s in (0 : ℝ)..T, r s := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * Δ)
      (n := n) (f := r) (μ := MeasureTheory.volume) fun i _ => hr.intervalIntegrable _ _
    simpa [hnΔ] using this
  have hterm : ∀ i ∈ Finset.range n, |r ((i + 1) * Δ) * Δ -
      ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s| ≤ ε / (2 * T) * Δ := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.mp hi
      exact_mod_cast this
    have hlen : ((i + 1 : ℕ) : ℝ) * Δ - i * Δ = Δ := by push_cast; ring
    have hconst : ∫ _ in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r ((i + 1) * Δ) = r ((i + 1) * Δ) * Δ := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul, mul_comm]
    have hdiff : r ((i + 1) * Δ) * Δ - ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s =
        ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), (r ((i + 1) * Δ) - r s) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hr.intervalIntegrable _ _),
        hconst]
    rw [hdiff]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (i : ℝ) * Δ) (b := ((i + 1 : ℕ) : ℝ) * Δ) (C := ε / (2 * T))
      (f := fun s => r ((i + 1) * Δ) - r s) (fun s hs => ?_)
    · rw [Real.norm_eq_abs] at hb
      rw [abs_of_pos (by linarith : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) * Δ - i * Δ), hlen] at hb
      exact hb
    · rw [Set.uIoc_of_le (by push_cast; nlinarith)] at hs
      push_cast at hs
      have hs0 : 0 ≤ s := le_trans (by positivity) hs.1.le
      have hsT : s ≤ T := by rw [← hnΔ]; nlinarith [hs.2]
      have hiT : ((i : ℝ) + 1) * Δ ≤ T := by rw [← hnΔ]; nlinarith
      have hd : dist ((i + 1) * Δ) s < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> nlinarith [hs.1, hs.2]
      have := hδr ((i + 1) * Δ) ⟨by positivity, hiT⟩ s ⟨hs0, hsT⟩ hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
  rw [Real.dist_eq, ← hsplit, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range n, (r ((i + 1) * Δ) * Δ -
        ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s)|
      ≤ ∑ i ∈ Finset.range n, |r ((i + 1) * Δ) * Δ -
        ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε / (2 * T) * Δ := Finset.sum_le_sum hterm
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, mul_comm (n : ℝ),
          mul_assoc, hnΔ]
        field_simp
    _ < ε := half_lt_self hε

/-- AKMM, Appendix 9.A.3, pp. 844–845: for continuous `r` and `T > 0`, with `Δ = T/n`,
`∏_{t=1}^n (1 + r(tΔ)Δ) → e^{∫_0^T r}` as `n → ∞`. -/
theorem productLimits_product {r : ℝ → ℝ} (hr : Continuous r) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 + r ((i + 1) * (T / n)) * (T / n))) atTop
      (𝓝 (Real.exp (∫ s in (0 : ℝ)..T, r s))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hr.continuousOn (s := Set.Icc 0 T))
  set B := |M| + 1
  have hB : 0 < B := by positivity
  set x : ℕ → ℕ → ℝ := fun n i => r ((i + 1) * (T / n)) * (T / n)
  have hxb : ∀ n : ℕ, 0 < n → ∀ i ∈ Finset.range n, |x n i| ≤ B * (T / n) := by
    intro n hn i hi
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hi
    have hmem : (i + 1) * (T / n) ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [mul_div_assoc', div_le_iff₀ hn']
      nlinarith
    have h := hM _ hmem
    rw [Real.norm_eq_abs] at h
    simp only [x, abs_mul, abs_of_pos (div_pos hT hn')]
    exact mul_le_mul_of_nonneg_right (h.trans (by simp [B]; linarith [le_abs_self M]))
      (div_pos hT hn').le
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, x n i
  set L : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, Real.log (1 + x n i)
  have hsmall : ∀ᶠ n : ℕ in atTop, 0 < n ∧ B * (T / n) ≤ 1 / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * B * T)
    filter_upwards [eventually_gt_atTop N] with n hn
    have hn' : (N : ℝ) < n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt N.cast_nonneg hn'
    refine ⟨by exact_mod_cast hn0, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ hn0]
    nlinarith
  have hLS : ∀ᶠ n : ℕ in atTop, |L n - S n| ≤ 2 * (B * T) ^ 2 / n := by
    filter_upwards [hsmall] with n ⟨hn, hsm⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hterm : ∀ i ∈ Finset.range n, |Real.log (1 + x n i) - x n i| ≤ 2 * (B * (T / n)) ^ 2 := by
      intro i hi
      have hx := hxb n hn i hi
      have hx1 : |x n i| ≤ 1 / 2 := hx.trans hsm
      have hgt : -1 < x n i := by linarith [neg_abs_le (x n i)]
      have h := (growthRates_log_one_add_approx hgt).2.2 (by linarith)
      have hden : 1 / 2 ≤ 1 - |x n i| := by linarith
      have hsq : x n i ^ 2 ≤ (B * (T / n)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      calc |Real.log (1 + x n i) - x n i| ≤ x n i ^ 2 / (1 - |x n i|) := h
        _ ≤ x n i ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
        _ = 2 * x n i ^ 2 := by ring
        _ ≤ 2 * (B * (T / n)) ^ 2 := by linarith
    calc |L n - S n| = |∑ i ∈ Finset.range n, (Real.log (1 + x n i) - x n i)| := by
          simp only [L, S, Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ Finset.range n, |Real.log (1 + x n i) - x n i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, 2 * (B * (T / n)) ^ 2 := Finset.sum_le_sum hterm
      _ = 2 * (B * T) ^ 2 / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hdiff : Tendsto (fun n : ℕ => L n - S n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 2 * (B * T) ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hLS] with n hn
    rwa [Real.norm_eq_abs]
  have hL : Tendsto L atTop (𝓝 (∫ s in (0 : ℝ)..T, r s)) := by
    have := (productLimits_riemann hr hT).add hdiff
    rw [add_zero] at this
    refine this.congr fun n => ?_
    simp only [S, x]
    ring
  refine ((Real.continuous_exp.tendsto _).comp hL).congr' ?_
  filter_upwards [hsmall] with n ⟨hn, hsm⟩
  simp only [Function.comp, L, Real.exp_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hx1 : |x n i| ≤ 1 / 2 := (hxb n hn i hi).trans hsm
  have hpos : 0 < 1 + x n i := by linarith [neg_abs_le (x n i)]
  exact Real.exp_log hpos

/-- AKMM, Appendix 9.A.3, p. 845: the continuous-time limit of the nPg discount factor,
`1/∏_{t=1}^{T/Δ}(1 + r(tΔ)Δ) → e^{−∫_0^T r(t)dt}` as `Δ = T/n → 0`. -/
theorem appendix_9A3_product_limit {r : ℝ → ℝ} (hr : Continuous r) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (∏ i ∈ Finset.range n, (1 + r ((i + 1) * (T / n)) * (T / n)))⁻¹)
      atTop (𝓝 (Real.exp (-∫ s in (0 : ℝ)..T, r s))) := by
  rw [Real.exp_neg]
  exact (productLimits_product hr hT).inv₀ (Real.exp_pos _).ne'

/-- AKMM, p. 259: with independent trials in subintervals of length `Δ = T/n` with success
probabilities `λ(tΔ)Δ`, the probability of no success, `∏_{t=1}^n (1 − λ(tΔ)Δ)`, tends to
`e^{−∫_0^T λ}`. -/
theorem productLimits_survival {lam : ℝ → ℝ} (hlam : Continuous lam) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 - lam ((i + 1) * (T / n)) * (T / n))) atTop
      (𝓝 (Real.exp (-∫ s in (0 : ℝ)..T, lam s))) := by
  have h := productLimits_product (r := fun s => -lam s) hlam.neg hT
  rw [intervalIntegral.integral_neg] at h
  refine h.congr fun n => Finset.prod_congr rfl fun i _ => ?_
  ring

end AKMM.ContinuousTime
