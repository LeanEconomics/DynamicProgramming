/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.ContinuousBudget
import ContinuousTime.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Uncertainty: the Poisson distribution and exponential waiting times

AKMM, §9.4 (pp. 257–259): (9.40)–(9.43), the Poisson distribution, survival probabilities and
the expected duration of a job.

Mathlib has no Poisson *process* (independent increments, counting paths). What follows from
the binomial approximation, the exponential distribution and memorylessness is proved:

* (9.40)–(9.42): the binomial probabilities `b(k, n)` of `k` successes in `n` trials with
  success probability `λ/n`; they sum to `1`, the expected number of successes is `λ`, and
  (9.41)–(9.42) hold (`poisson_binomial_sum`, `poisson_expected_successes`, `eq_9_41`,
  `eq_9_42`).
* (9.43): `b(0, n) → e^{−λ}`; the ratio `b(k, n)/b(k − 1, n) → λ/k`; hence the law of small
  numbers `b(k, n) → e^{−λ}λ^k/k!` (`eq_9_43`, `poisson_ratio_limit`, `poisson_limit`).
* The Poisson probabilities sum to `1` with mean `λ` (`poisson_sum_mean`); with rate `λ` on an
  interval of length `T` they are those of parameter `λT` (`poisson_limit_interval`).
* The probability of no success in `(t, t + T]` is `e^{−λT}`, memoryless; and a decreasing
  survival function with values in `(0, 1)` that is memoryless is exponential
  (`poisson_survival_memoryless`, `poisson_memoryless_iff_exponential`, from Sargent–Stachurski's
  Lemma 10.1.1). With a time-varying rate the survival probability `S`, defined by
  `Ṡ = −λ(s)S`, `S(t) = 1`, is `e^{−∫_t^{t+T} λ}` (`poisson_survival_time_varying`).
* The expected remaining job duration `∫_0^∞ tσe^{−σt}dt = 1/σ`, and the density integrates to
  `1` (`poisson_expected_duration`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.40), p. 258: the binomial probability of `k` successes in `n` trials with success
probability `λ/n` each. -/
noncomputable def binomialProb (lam : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (lam / n) ^ k * (1 - lam / n) ^ (n - k)

/-- AKMM, p. 258: the binomial probabilities `b(0, n), …, b(n, n)` sum to `1`. -/
theorem poisson_binomial_sum (lam : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), binomialProb lam n k = 1 := by
  have h := (add_pow (lam / n) (1 - lam / n) n).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [binomialProb]
  ring

/-- AKMM, p. 258: with `n` trials of success probability `λ/n`, the expected number of successes
is `λ/n + ⋯ + λ/n = λ` (`n` times). -/
theorem poisson_expected_successes (lam : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ _i ∈ Finset.range n, lam / n = lam := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- AKMM, (9.41), p. 258: `b(0, n) = (1 − λ/n)^n`. -/
theorem eq_9_41 (lam : ℝ) (n : ℕ) : binomialProb lam n 0 = (1 - lam / n) ^ n := by
  simp [binomialProb]

/-- AKMM, (9.42), p. 258: for `1 ≤ k ≤ n` and `λ ≠ n`,
`b(k, n) = b(k − 1, n) · ((n − (k − 1))/k) · ((λ/n)/(1 − λ/n))`, and
`((n − (k − 1))/k)((λ/n)/(1 − λ/n)) = (λ − (k − 1)λ/n)/(k − λk/n)`. -/
theorem eq_9_42 (lam : ℝ) {n k : ℕ} (hk : k + 1 ≤ n) (hn : (n : ℝ) ≠ lam) :
    binomialProb lam n (k + 1) =
        binomialProb lam n k * (((n : ℝ) - k) / (k + 1) * ((lam / n) / (1 - lam / n))) ∧
      ((n : ℝ) - k) / (k + 1) * ((lam / n) / (1 - lam / n)) =
        (lam - k * lam / n) / ((k + 1) - lam * (k + 1) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have h1 : 1 - lam / n ≠ 0 := by
    intro h
    have h' : lam / n = 1 := by linarith
    rw [div_eq_one_iff_eq hn0] at h'
    exact hn h'.symm
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hchoose : ((n.choose (k + 1) : ℕ) : ℝ) * (k + 1) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
    have := Nat.choose_succ_right_eq n k
    rw [show ((n : ℝ) - k) = ((n - k : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]]
    exact_mod_cast this
  have hpow : (1 - lam / n) ^ (n - k) = (1 - lam / n) ^ (n - (k + 1)) * (1 - lam / n) := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨?_, ?_⟩
  · simp only [binomialProb]
    rw [hpow]
    have hc : ((n.choose (k + 1) : ℕ) : ℝ) = (n.choose k : ℝ) * ((n : ℝ) - k) / (k + 1) := by
      rw [eq_div_iff hk1, hchoose]
    rw [hc]
    set p := lam / (n : ℝ)
    field_simp
    ring
  · field_simp

/-- AKMM, (9.43), p. 258: `p(0) = lim_{n→∞} b(0, n) = e^{−λ}`. -/
theorem eq_9_43 (lam : ℝ) :
    Tendsto (fun n : ℕ => binomialProb lam n 0) atTop (𝓝 (Real.exp (-lam))) := by
  simp only [eq_9_41]
  have h := Real.tendsto_one_add_div_pow_exp (-lam)
  simpa [neg_div, sub_eq_add_neg] using h

/-- AKMM, p. 258: `lim_{n→∞} b(k + 1, n)/b(k, n) = λ/(k + 1)`, in the form of the limit of the
ratio `(λ − kλ/n)/((k + 1) − λ(k + 1)/n)` of (9.42). -/
theorem poisson_ratio_limit (lam : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (lam - k * lam / n) / ((k + 1) - lam * (k + 1) / n)) atTop
      (𝓝 (lam / (k + 1))) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun n : ℕ => lam - k * lam / n) atTop (𝓝 (lam - k * lam * 0)) := by
    refine tendsto_const_nhds.sub ((h0.const_mul (k * lam)).congr fun n => ?_)
    ring
  have hden : Tendsto (fun n : ℕ => ((k : ℝ) + 1) - lam * (k + 1) / n) atTop
      (𝓝 ((k + 1) - lam * (k + 1) * 0)) := by
    refine tendsto_const_nhds.sub ((h0.const_mul (lam * (k + 1))).congr fun n => ?_)
    ring
  simp only [mul_zero, sub_zero] at hnum hden
  exact hnum.div hden (by positivity)

/-- AKMM, p. 259: **the Poisson limit** (law of small numbers). For every `k`,
`b(k, n) → p(k) = e^{−λ}λ^k/k!` as `n → ∞`, by applying the ratio limit for `k = 1, 2, …`. -/
theorem poisson_limit (lam : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => binomialProb lam n k) atTop
      (𝓝 (Real.exp (-lam) * lam ^ k / k.factorial)) := by
  induction k with
  | zero => simpa using eq_9_43 lam
  | succ k ih =>
    have hprod := ih.mul (poisson_ratio_limit lam k)
    have hlim : Real.exp (-lam) * lam ^ k / k.factorial * (lam / (k + 1)) =
        Real.exp (-lam) * lam ^ (k + 1) / (k + 1).factorial := by
      push_cast [Nat.factorial_succ]
      field_simp
      ring
    rw [hlim] at hprod
    refine hprod.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt |lam|
    filter_upwards [eventually_ge_atTop (k + 1), eventually_gt_atTop N] with n hn hnN
    have hne : (n : ℝ) ≠ lam := by
      intro h
      have : (N : ℝ) < n := by exact_mod_cast hnN
      have := le_abs_self lam
      linarith
    have e := eq_9_42 lam hn hne
    rw [e.1, e.2]

/-- AKMM, p. 259: the Poisson probabilities `p(k) = e^{−λ}λ^k/k!` sum to `1` and have mean `λ`. -/
theorem poisson_sum_mean (lam : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-lam) * lam ^ k / k.factorial) 1 ∧
      HasSum (fun k : ℕ => (k : ℝ) * (Real.exp (-lam) * lam ^ k / k.factorial)) lam := by
  have hexp : HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℝ)) (Real.exp lam) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) lam
    rwa [← Real.exp_eq_exp_ℝ] at this
  have h1 : HasSum (fun k : ℕ => Real.exp (-lam) * lam ^ k / k.factorial) 1 := by
    have := hexp.mul_left (Real.exp (-lam))
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    refine this.congr_fun fun k => ?_
    ring
  refine ⟨h1, ?_⟩
  have h2 := (h1.mul_left lam)
  rw [mul_one] at h2
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  refine h2.congr_fun fun k => ?_
  push_cast [Nat.factorial_succ, pow_succ]
  field_simp

/-- AKMM, p. 259: on an interval of length `T` with trials of length `Δ = T/n` and success
probability `λΔ = λT/n`, the number of successes converges in distribution to the Poisson
distribution with parameter `λT`, whose mean is `λT`. -/
theorem poisson_limit_interval (lam T : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => binomialProb (lam * T) n k) atTop
      (𝓝 (Real.exp (-(lam * T)) * (lam * T) ^ k / k.factorial)) ∧
      HasSum (fun k : ℕ => (k : ℝ) * (Real.exp (-(lam * T)) * (lam * T) ^ k / k.factorial))
        (lam * T) :=
  ⟨poisson_limit (lam * T) k, (poisson_sum_mean (lam * T)).2⟩

/-- AKMM, p. 259: the probability of no success during `(t, t + T]` is `p(0) = e^{−λT}`, and it
is memoryless: `e^{−λ(s + T)}/e^{−λs} = e^{−λT}` (Sargent–Stachurski, Exercise 10.1.1). -/
theorem poisson_survival_memoryless (lam s T : ℝ) :
    Real.exp (-(lam * T)) * (lam * T) ^ 0 / (Nat.factorial 0) = Real.exp (-lam * T) ∧
      Real.exp (-lam * (s + T)) / Real.exp (-lam * s) = Real.exp (-lam * T) := by
  refine ⟨by simp [neg_mul], (SargentStachurski.ContinuousTime.exp_memoryless lam s T).2⟩

/-- AKMM, p. 259, "the Poisson process is a memoryless process": a decreasing survival function
`G` with `0 < G < 1` on `(0, ∞)` is memoryless, `G(s + t) = G(s)G(t)`, if and only if it is
exponential, `G(t) = e^{−λt}` with `λ > 0` (Sargent–Stachurski, Lemma 10.1.1, imported). -/
theorem poisson_memoryless_iff_exponential {G : ℝ → ℝ} (hanti : AntitoneOn G (Set.Ioi 0))
    (hG : ∀ t > 0, 0 < G t ∧ G t < 1) :
    (∀ s > 0, ∀ t > 0, G (s + t) = G s * G t) ↔ ∃ lam > 0, ∀ t > 0, G t = Real.exp (-lam * t) := by
  refine ⟨SargentStachurski.ContinuousTime.eq_exp_of_memoryless hanti hG, ?_⟩
  rintro ⟨lam, -, hlam⟩ s hs t ht
  rw [hlam s hs, hlam t ht, hlam (s + t) (by linarith)]
  exact (SargentStachurski.ContinuousTime.exp_memoryless lam s t).1

/-- AKMM, p. 259: with a time-varying rate `λ(s)` (continuous), the survival probability `S`
from `t` — defined by the hazard equation `Ṡ(s) = −λ(s)S(s)`, `S(t) = 1` — is
`S(t + T) = e^{−∫_t^{t+T} λ(s)ds}`. -/
theorem poisson_survival_time_varying {lam S : ℝ → ℝ} (hlam : Continuous lam) {t T : ℝ}
    (hT : 0 ≤ T) (hS : ∀ s, t ≤ s → HasDerivAt S (-lam s * S s) s) (hS0 : S t = 1) :
    S (t + T) = Real.exp (-∫ s in t..t + T, lam s) := by
  set a : ℝ → ℝ := fun x => S (t + x)
  have ha : ∀ x, 0 ≤ x → HasDerivAt a (0 + (fun y => -lam (t + y)) x * a x - 0) x := by
    intro x hx
    have h := (hS (t + x) (by linarith)).comp x ((hasDerivAt_id x).const_add t)
    simp only [mul_one] at h
    convert h using 1
    · rfl
    · simp only [a]
      ring
  have hcont : Continuous fun y => -lam (t + y) :=
    (hlam.comp (continuous_const.add continuous_id)).neg
  have h := appendix_9A3_continuous_budget hcont continuous_const continuous_const ha hT
  simp only [sub_self, mul_zero, intervalIntegral.integral_zero, add_zero, a, add_zero,
    hS0] at h
  have hsub : ∫ y in (0 : ℝ)..T, -lam (t + y) = -∫ s in t..t + T, lam s := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_add_left (fun s => lam s) t]
    simp
  rw [hsub, neg_neg] at h
  have hE := Real.exp_pos (∫ s in t..t + T, lam s)
  calc S (t + T) = Real.exp (-∫ s in t..t + T, lam s) *
        (Real.exp (∫ s in t..t + T, lam s) * S (t + T)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-∫ s in t..t + T, lam s) := by rw [h, mul_one]

/-- AKMM, p. 259: the expected remaining duration of a job with separation rate `σ > 0` is
`∫_0^∞ tσe^{−σt}dt = 1/σ`, and the density `σe^{−σt}` integrates to `1`. -/
theorem poisson_expected_duration {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-σ * t) * σ = 1 / σ ∧
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-σ * t) * σ = 1 := by
  have h2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := σ) two_pos hσ
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := σ) one_pos hσ
  have hG2 : Real.Gamma 2 = 1 := Real.Gamma_two
  have hG1 : Real.Gamma 1 = 1 := Real.Gamma_one
  constructor
  · have e : ∀ t : ℝ, t * Real.exp (-σ * t) * σ = σ * (t ^ ((2 : ℝ) - 1) * Real.exp (-(σ * t))) :=
      fun t => by norm_num; ring_nf
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul, h2, hG2, Real.rpow_two]
    field_simp
  · have e : ∀ t : ℝ, Real.exp (-σ * t) * σ = σ * (t ^ ((1 : ℝ) - 1) * Real.exp (-(σ * t))) :=
      fun t => by norm_num; ring_nf
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul, h1, hG1, Real.rpow_one]
    field_simp

end AKMM.ContinuousTime
