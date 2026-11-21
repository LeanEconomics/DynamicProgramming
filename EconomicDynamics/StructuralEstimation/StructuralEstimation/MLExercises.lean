/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.MLLikelihood
import StructuralEstimation.MLExponential
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exercises 12.1 and 12.2: coin tossing and exponential maximum likelihood

Miao, §12.4, p. 408, Exercises 12.1 and 12.2, and the asymptotic properties of ML listed on
pp. 397–398 for these two models.

* `ml_binomial_lik_le`: `pᵏ(1 − p)ⁿ⁻ᵏ ≤ (k/n)ᵏ(1 − k/n)ⁿ⁻ᵏ` for `p ∈ [0, 1]`.
* **Exercise 12.1** (coin tossing): `ex_12_1_likelihood` (`L(p) = pᵏ(1 − p)ᴺ⁻ᵏ` with `k` the number
  of heads), `ex_12_1` (the ML estimate is `p̂ = k/N`, the frequency of heads),
  `ex_12_1_consistent` (`p̂_N → p` almost surely, by the strong law), `ex_12_1_asymptotic`
  (`√N(p̂_N − p) ⇒ N(0, p(1 − p))`, by the central limit theorem; `p(1 − p) = I(p)⁻¹` by
  `ml_cramer_rao_bernoulli`).
* **Exercise 12.2** (exponential sampling, `f(x) = θe^{−xθ}`): `ex_12_2_likelihood`
  (`L(θ) = θᴺ e^{−θ ∑ xₜ}`), `ex_12_2_logLikelihood`, `ex_12_2` (the ML estimator is
  `θ̂ = N/∑ xₜ = 1/x̄`), `ex_12_2_fisher` (`−∂² ln f/∂θ² = 1/θ²`, so `I(θ) = 1/θ²`),
  `ex_12_2_consistent` (`θ̂_N → θ` almost surely) and `ex_12_2_asymptotic` (the asymptotic
  distribution: `√N(θ̂_N − θ) ⇒ N(0, θ²) = N(0, I(θ)⁻¹)`, by the central limit theorem and the
  delta method through Slutsky's theorem).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology Real

/-- The Bernoulli likelihood is maximised at the frequency: for `k ≤ n`, `0 < n` and
`p ∈ [0, 1]`, `pᵏ(1 − p)ⁿ⁻ᵏ ≤ (k/n)ᵏ(1 − k/n)ⁿ⁻ᵏ`. -/
theorem ml_binomial_lik_le (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    p ^ k * (1 - p) ^ (n - k) ≤ ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, sub_zero, one_pow, Nat.sub_zero]
    exact pow_le_one₀ (by linarith) (by linarith)
  rcases hk.lt_or_eq with hkn | rfl
  · set q : ℝ := (k : ℝ) / n with hq
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hknR : (k : ℝ) < n := by exact_mod_cast hkn
    have hq0 : 0 < q := div_pos hkR hn'
    have hq1 : q < 1 := (div_lt_one hn').2 hknR
    have hm0 : 0 < n - k := Nat.sub_pos_of_lt hkn
    have hmR : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hk
    rcases hp0.lt_or_eq with hp0' | rfl
    · rcases hp1.lt_or_eq with hp1' | rfl
      · -- interior: compare the logarithms
        have hL : 0 < p ^ k * (1 - p) ^ (n - k) := by
          have : 0 < 1 - p := by linarith
          positivity
        have hR : 0 < q ^ k * (1 - q) ^ (n - k) := by
          have : 0 < 1 - q := by linarith
          positivity
        rw [← Real.log_le_log_iff hL hR, Real.log_mul (by positivity) (by
          have : 0 < 1 - p := by linarith
          positivity), Real.log_mul (by positivity) (by
          have : 0 < 1 - q := by linarith
          positivity), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, hmR]
        have h1 : Real.log p - Real.log q ≤ p / q - 1 := by
          rw [← Real.log_div hp0'.ne' hq0.ne']
          exact Real.log_le_sub_one_of_pos (div_pos hp0' hq0)
        have h2 : Real.log (1 - p) - Real.log (1 - q) ≤ (1 - p) / (1 - q) - 1 := by
          rw [← Real.log_div (by linarith) (by linarith)]
          exact Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
        have hnkne : (n : ℝ) - k ≠ 0 := by linarith
        have hkne : (k : ℝ) ≠ 0 := hkR.ne'
        have e1 : (k : ℝ) * (p / q - 1) = n * p - k := by
          rw [hq]; field_simp
        have h1q : 1 - q = (n - k) / n := by rw [hq]; field_simp
        have e2 : ((n : ℝ) - k) * ((1 - p) / (1 - q) - 1) = k - n * p := by
          rw [h1q]; field_simp; ring
        have hsum : (k : ℝ) * (p / q - 1) + (n - k) * ((1 - p) / (1 - q) - 1) = 0 := by
          rw [e1, e2]; ring
        have hnk : (0 : ℝ) ≤ n - k := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hkR.le, mul_le_mul_of_nonneg_left h2 hnk]
      · rw [sub_self, zero_pow hm0.ne', mul_zero]
        have : 0 ≤ 1 - q := by linarith
        positivity
    · rw [zero_pow hk0.ne', zero_mul]
      have : 0 ≤ 1 - q := by linarith
      positivity
  · simp only [Nat.sub_self, pow_zero, mul_one, div_self hn'.ne', one_pow]
    exact pow_le_one₀ hp0 hp1

/-- The density of one coin toss, `Pr(x | p) = p` for heads and `1 − p` for tails. -/
def ml_coinDensity (b : Bool) (p : ℝ) : ℝ := if b then p else 1 - p

/-- The number of heads in `x₁, …, x_N`. -/
def ml_heads {N : ℕ} (x : Fin N → Bool) : ℕ := (Finset.univ.filter fun t => x t = true).card

/-- **Exercise 12.1** (Miao, p. 408): the likelihood of the tosses `x₁, …, x_N` is
`L(p) = ∏ₜ p^{xₜ}(1 − p)^{1 − xₜ} = pᵏ(1 − p)ᴺ⁻ᵏ`, `k` the number of heads. -/
theorem ex_12_1_likelihood {N : ℕ} (x : Fin N → Bool) (p : ℝ) :
    ml_likelihood ml_coinDensity x p = p ^ ml_heads x * (1 - p) ^ (N - ml_heads x) := by
  unfold ml_likelihood ml_coinDensity ml_heads
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun t : Fin N => x t = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **Exercise 12.1** (Miao, p. 408): the ML estimate of `p` is the frequency of heads
`p̂ = k/N`: it lies in `[0, 1]` and maximises the likelihood over `[0, 1]`. -/
theorem ex_12_1 {N : ℕ} (hN : 0 < N) (x : Fin N → Bool) :
    ((ml_heads x : ℝ) / N ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        ml_likelihood ml_coinDensity x p ≤
          ml_likelihood ml_coinDensity x ((ml_heads x : ℝ) / N) := by
  have hk : ml_heads x ≤ N := by
    unfold ml_heads
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨by positivity, (div_le_one hN').2 (by exact_mod_cast hk)⟩, fun p hp => ?_⟩
  rw [ex_12_1_likelihood, ex_12_1_likelihood]
  exact ml_binomial_lik_le N _ hN hk p hp.1 hp.2

/-- The mean of a `{0, 1}`-valued random variable is the probability of `1`. -/
theorem ml_integral_of_zero_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ01 : ∀ ω, Z ω = 0 ∨ Z ω = 1) (hmeas : Measurable Z) :
    ∫ ω, Z ω ∂P = P.real {ω | Z ω = 1} ∧ ∫ ω, Z ω ^ 2 ∂P = P.real {ω | Z ω = 1} := by
  have hset : MeasurableSet {ω | Z ω = 1} := hmeas (measurableSet_singleton 1)
  have hZ : Z = Set.indicator {ω | Z ω = 1} 1 := by
    funext ω
    rcases hZ01 ω with h | h
    · rw [Set.indicator_of_notMem (by simp [h]), h]
    · rw [Set.indicator_of_mem (by simp [h]), h]; rfl
  have hZ2 : (fun ω => Z ω ^ 2) = Z := by
    funext ω
    rcases hZ01 ω with h | h <;> simp [h]
  rw [hZ2]
  have : ∫ ω, Z ω ∂P = P.real {ω | Z ω = 1} := by
    conv_lhs => rw [hZ]
    exact integral_indicator_one hset
  exact ⟨this, this⟩

/-- **Exercise 12.1**, consistency (Miao, p. 397, "Consistency"): for i.i.d. tosses `Xᵢ ∈ {0, 1}`
with `P(Xᵢ = 1) = p`, the ML estimates `p̂_N = (1/N) ∑_{i<N} Xᵢ` converge to `p` almost surely
(Mathlib's strong law of large numbers). -/
theorem ex_12_1_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (p : ℝ) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmeas : Measurable (X 0)) (hp : P.real {ω | X 0 ω = 1} = p)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 p) := by
  have hint : Integrable (X 0) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rcases hX01 0 ω with h | h <;> simp [h])
  have hmean : ∫ ω, X 0 ω ∂P = p :=
    (ml_integral_of_zero_one (P := P) (X 0) (hX01 0) hmeas).1.trans hp
  have := strong_law_ae_real X hint hindep hident
  rw [hmean] at this
  exact this

/-- `√n (S/n − m) = (√n)⁻¹ (S − n m)` (both sides vanish at `n = 0`). -/
theorem ml_sqrt_mul_mean_sub (n : ℕ) (S m : ℝ) :
    Real.sqrt n * (S / n - m) = (Real.sqrt n)⁻¹ * (S - n * m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  set s := Real.sqrt (n : ℝ)
  rw [← hsq]
  field_simp

/-- **Exercise 12.1**, asymptotic normality (Miao, p. 397): for i.i.d. tosses with
`P(Xᵢ = 1) = p`, `√N(p̂_N − p) ⇒ N(0, p(1 − p))`; here `p(1 − p) = I(p)⁻¹`, the inverse Fisher
information of one toss (`ml_cramer_rao_bernoulli`). Mathlib's central limit theorem. -/
theorem ex_12_1_asymptotic {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (p : ℝ) (Y : Ω' → ℝ) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmeas : Measurable (X 0)) (hp : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY : HasLaw Y (gaussianReal 0 (p * (1 - p)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
      ((∑ i ∈ Finset.range n, X i ω) / n - p)) atTop Y (fun _ => P) P' := by
  obtain ⟨h1, h2⟩ := ml_integral_of_zero_one (P := P) (X 0) (hX01 0) hmeas
  have hL2 : MemLp (X 0) 2 P :=
    MemLp.of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rcases hX01 0 ω with h | h <;> simp [h])
  have hvar : Var[X 0; P] = p * (1 - p) := by
    rw [variance_eq_sub hL2]
    simp only [Pi.pow_apply]
    rw [h1, h2, hp]
    ring
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (P' := P') (X := X) (Y := Y)
    (by rw [hvar]; exact hY) hL2 hindep hident
  rw [h1, hp] at hclt
  have hfun : (fun (n : ℕ) ω => Real.sqrt n * ((∑ i ∈ Finset.range n, X i ω) / n - p)) =
      fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * (∑ i ∈ Finset.range n, X i ω - n * p) := by
    funext n ω
    exact ml_sqrt_mul_mean_sub n _ p
  rw [hfun]
  exact hclt

/-- The exponential density of Exercise 12.2, `f(x, θ) = θ exp(−xθ)`. -/
noncomputable def ml_expDensity (x θ : ℝ) : ℝ := θ * Real.exp (-(x * θ))

/-- **Exercise 12.2** (Miao, p. 408): the likelihood of a sample from `f(x) = θe^{−xθ}` is
`L(θ) = θᴺ exp(−θ ∑ₜ xₜ)`. -/
theorem ex_12_2_likelihood {N : ℕ} (x : Fin N → ℝ) (θ : ℝ) :
    ml_likelihood ml_expDensity x θ = θ ^ N * Real.exp (-(θ * ∑ t, x t)) := by
  unfold ml_likelihood ml_expDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **Exercise 12.2** (Miao, p. 408): the log-likelihood is `N ln θ − θ ∑ₜ xₜ` for `θ > 0`. -/
theorem ex_12_2_logLikelihood {N : ℕ} (x : Fin N → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ml_logLikelihood ml_expDensity x θ = N * Real.log θ - θ * ∑ t, x t := by
  rw [← eq_ml_log_likelihood _ _ _ (fun t => by unfold ml_expDensity; positivity),
    ex_12_2_likelihood, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp]
  ring

/-- **Exercise 12.2** (Miao, p. 408): for a sample with `∑ₜ xₜ > 0`, the ML estimator of `θ` is
`θ̂ = N/∑ₜ xₜ = 1/x̄`: it is positive and maximises the likelihood over `θ > 0`. -/
theorem ex_12_2 {N : ℕ} (x : Fin N → ℝ) (hS : 0 < ∑ t, x t) :
    let θhat := (N : ℝ) / ∑ t, x t
    0 < θhat ∧ θhat = 1 / ((∑ t, x t) / N) ∧
      IsMaxOn (ml_likelihood ml_expDensity x) (Set.Ioi 0) θhat := by
  intro θhat
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hS
    · exact h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < θhat := div_pos hN' hS
  refine ⟨hpos, by simp only [θhat]; field_simp, ?_⟩
  intro θ hθ
  have hθ' : 0 < θ := hθ
  change ml_likelihood ml_expDensity x θ ≤ ml_likelihood ml_expDensity x θhat
  have hLpos : ∀ η, 0 < η → 0 < ml_likelihood ml_expDensity x η := fun η hη => by
    rw [ex_12_2_likelihood]; positivity
  rw [← Real.log_le_log_iff (hLpos θ hθ') (hLpos θhat hpos),
    eq_ml_log_likelihood _ _ _ (fun t => by unfold ml_expDensity; positivity),
    eq_ml_log_likelihood _ _ _ (fun t => by unfold ml_expDensity; positivity),
    ex_12_2_logLikelihood x hθ', ex_12_2_logLikelihood x hpos]
  have hlog : Real.log θ - Real.log θhat ≤ θ / θhat - 1 := by
    rw [← Real.log_div hθ'.ne' hpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hθ' hpos)
  have key : (N : ℝ) * (θ / θhat - 1) = θ * ∑ t, x t - θhat * ∑ t, x t := by
    simp only [θhat]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hN'.le]

/-- **Exercise 12.2**, Fisher information (Miao, p. 398): for `θ > 0` the score of one
observation is `∂ ln f(x, θ)/∂θ = 1/θ − x` and `∂² ln f(x, θ)/∂θ² = −1/θ²`, so
`I(θ) = −E[∂² ln f/∂θ²] = 1/θ²`. -/
theorem ex_12_2_fisher (x : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun η => Real.log (ml_expDensity x η)) (1 / θ - x) θ ∧
      HasDerivAt (fun η => 1 / η - x) (-(1 / θ ^ 2)) θ := by
  constructor
  · have h1 : HasDerivAt (fun η => η * Real.exp (-(x * η)))
        (1 * Real.exp (-(x * θ)) + θ * (Real.exp (-(x * θ)) * (-(x * 1)))) θ :=
      (hasDerivAt_id θ).mul (((hasDerivAt_id θ).const_mul x).neg.exp)
    have h2 := h1.log (by positivity)
    unfold ml_expDensity
    convert h2 using 1
    field_simp
    ring
  · have := ((hasDerivAt_id θ).inv hθ.ne').sub_const x
    convert this using 1
    · funext η; simp [one_div]
    · simp only [id]; ring

/-- Convergence in distribution is unchanged by changing each random variable on a null set. -/
theorem ml_tendstoInDistribution_congr_ae {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X X' : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => P) P') (hae : ∀ n, X n =ᵐ[P] X' n) :
    TendstoInDistribution X' atTop Z (fun _ => P) P' where
  forall_aemeasurable n := (h.forall_aemeasurable n).congr (hae n)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine h.tendsto.congr' (Eventually.of_forall fun n => ?_)
    exact Subtype.ext (Measure.map_congr (hae n))

/-- **Exercise 12.2**, consistency (Miao, p. 397): for i.i.d. `Xᵢ ~ θe^{−θx}`, the ML estimates
`θ̂_N = N/∑_{i<N} Xᵢ` converge to `θ` almost surely (strong law and continuity of `x ↦ 1/x` at
`1/θ`). -/
theorem ex_12_2_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure θ) P)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ) / ∑ i ∈ Finset.range n, X i ω) atTop (𝓝 θ) := by
  have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  have hint : Integrable (X 0) P := (hlaw 0).integrable (by
    have := ml_integrable_expMeasure_pow hθ 1
    simp only [pow_one] at this
    exact this)
  have hmean : ∫ ω, X 0 ω ∂P = 1 / θ := by
    rw [(hlaw 0).integral_eq, ml_mean_expMeasure hθ]
  filter_upwards [strong_law_ae_real X hint hindep hident] with ω hω
  rw [hmean] at hω
  have := hω.inv₀ (by positivity)
  simp only [one_div, inv_inv] at this
  convert this using 2 with n
  rw [inv_div]

/-- **Exercise 12.2**, the asymptotic distribution (Miao, p. 408; p. 397 for the general claim):
for i.i.d. `Xᵢ ~ θe^{−θx}`, the ML estimator `θ̂_N = N/∑_{i<N} Xᵢ` satisfies
`√N(θ̂_N − θ) ⇒ N(0, θ²)`, and `θ² = I(θ)⁻¹` (`ex_12_2_fisher`). Proof: the central limit
theorem gives `√N(x̄_N − 1/θ) ⇒ N(0, 1/θ²)`; `θ̂_N → θ` in probability; and
`√N(θ̂_N − θ) = −θ · √N(x̄_N − 1/θ) · θ̂_N` whenever `x̄_N > 0`, so Slutsky's theorem
(the delta method) gives the limit `−θ² · N(0, 1/θ²) = N(0, θ²)`. -/
theorem ex_12_2_asymptotic {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) {θ : ℝ} (hθ : 0 < θ) (Y : Ω' → ℝ)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure θ) P) (hindep : iIndepFun X P)
    (hY : HasLaw Y (gaussianReal 0 (θ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
      ((n : ℝ) / (∑ i ∈ Finset.range n, X i ω) - θ)) atTop Y (fun _ => P) P' := by
  have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  have hL2 : MemLp (X 0) 2 P := (hlaw 0).memLp (ml_memLp_two_expMeasure hθ)
  have hmean : P[X 0] = 1 / θ := by rw [(hlaw 0).integral_eq, ml_mean_expMeasure hθ]
  have hvar : Var[X 0; P] = 1 / θ ^ 2 := by
    rw [(hlaw 0).variance_eq]; exact ml_variance_expMeasure hθ
  -- the limit of the CLT: `Z = −Y/θ² ~ N(0, 1/θ²)`
  set c : ℝ := -(θ ^ 2)⁻¹ with hc
  have hZ : HasLaw (fun ω => c * Y ω) (gaussianReal 0 Var[X 0; P].toNNReal) P' := by
    have hmul : HasLaw (fun x : ℝ => c * x) (gaussianReal 0 Var[X 0; P].toNNReal)
        (gaussianReal 0 (θ ^ 2).toNNReal) := by
      refine ⟨(measurable_const_mul c).aemeasurable, ?_⟩
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      rw [hvar]
      ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal', hc]
      rw [max_eq_left (by positivity), max_eq_left (by positivity)]
      field_simp
    exact hmul.comp hY
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (P' := P') (X := X)
    (Y := fun ω => c * Y ω) hZ hL2 hindep hident
  rw [hmean] at hclt
  -- `θ̂_N → θ` in probability
  have hcons := ex_12_2_consistent X hθ hlaw fun i j hij => hindep.indepFun hij
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hlaw i).aemeasurable
  have hYm : ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ) / ∑ i ∈ Finset.range n, X i ω) P :=
    fun n => aemeasurable_const.div (Finset.aemeasurable_fun_sum _ fun i _ => hXm i)
  have hprob : TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ) / ∑ i ∈ Finset.range n, X i ω)
      atTop (fun _ => θ) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hYm n).aestronglyMeasurable) hcons
  -- Slutsky with `g(z, y) = −θ z y`
  have hsl := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun q : ℝ × ℝ => -θ * q.1 * q.2) (by fun_prop) hprob hYm
  have hlim : (fun ω => -θ * (c * Y ω) * θ) = Y := by
    funext ω
    simp only [hc]
    field_simp
  dsimp only at hsl
  rw [hlim] at hsl
  refine ml_tendstoInDistribution_congr_ae hsl fun n => ?_
  -- equality off the null set where some `Xᵢ ≤ 0`
  have hpos : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω := by
    rw [ae_all_iff]
    intro i
    have h0 : P (X i ⁻¹' Set.Iic 0) = 0 := by
      rw [← Measure.map_apply_of_aemeasurable (hXm i) measurableSet_Iic, (hlaw i).map_eq]
      have hcdf := cdf_expMeasure_eq hθ 0
      rw [cdf_eq_real] at hcdf
      simp only [le_refl, ↓reduceIte, mul_zero, neg_zero, Real.exp_zero, sub_self] at hcdf
      exact (measureReal_eq_zero_iff).1 hcdf
    have := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with ω hω
    simpa using hω
  filter_upwards [hpos] with ω hω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hS : 0 < ∑ i ∈ Finset.range n, X i ω :=
    Finset.sum_pos (fun i _ => hω i) (Finset.nonempty_range_iff.2 hn.ne')
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  set s := Real.sqrt (n : ℝ)
  rw [← hsq]
  field_simp
  ring

end Miao.StructuralEstimation
