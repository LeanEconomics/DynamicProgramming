/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.StochasticComparison
import Mathlib.Analysis.PSeries

/-!
# The `c/x` chain after Theorem 9.5.6 (MT §9.5.3)

Meyn and Tweedie, pp. 227. On `ℤ₊`, with `0 < c ≤ 1`,
`P(x, x + 1) = 1 − c/x`, `P(x, 0) = c/x` for `x ≥ 1`, and `P(0, 1) = 1` (`cxKernel c`).

* `cx_tailProb`, `cx_tail_zero`: `P_0(τ₀ > n) = ∏_{x=1}^{n−1} (1 − c/x)`.
* `cx_recurrent`: `L(0, 0) = 1` and `U(0, 0) = ∞`: the chain is recurrent, since
  `∏ (1 − c/x) ≤ exp(−c Σ 1/x) → 0`.
* `cx_mean`, `cx_var`: for `x ≥ 1`, `m(x) = 1 − c − c/x` and `v(x) = cx + 1 − c/x`.
* `cx_identity`: `x(2x m(x) − v(x)) = (2 − 3c)x² − (2c + 1)x + c`.
* `cx_drift_condition`: for `c < 2/3` there are `θ > 1` and `x₀` with `m(x) ≥ θ v(x)/2x` for
  `x ≥ x₀`, which is (9.69); yet the chain is recurrent, so Theorem 9.5.6 (ii) needs its moment
  hypothesis.
* `cx_moment`: `E_x|Φ₁ − x|^{2+ε} = 1 − c/x + c x^{1+ε}`, unbounded in `x`.

**Corrections.**
* The book prints `P_0(τ₀ > n) = ∏_{x=1}^{n} [1 − c/x]`; the product stops at `n − 1`
  (`cx_tail_book_counterexample`, at `c = ½`, `n = 2`: `½` against `3/8`).
* The book prints `2xm(x) − v(x) = (2 − 3c)x² − (c + 1)x + c`. The left side must be
  `x(2xm(x) − v(x))`, and the linear coefficient is `2c + 1` (`cx_identity`);
  `cx_identity_book_counterexample` refutes the printed identity, with either left side, at
  `c = ½`, `x = 1`. The conclusion drawn from it (positive for large `x` when `c < 2/3`) is right.
* The book prints `E_x|W_x|^{2+ε} > x^{1+ε}`. The exact value is `1 − c/x + c x^{1+ε}`, which is
  smaller than `x^{1+ε}` for large `x` when `c < 1` (`cx_moment_book_counterexample`). What the
  argument needs, that `sup_x E_x|W_x|^{2+ε} = ∞`, is true (`cx_moment_unbounded`).
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-- The transition law of the `c/x` chain. -/
noncomputable def cxLaw (c : ℝ) : ℕ → Measure ℕ
  | 0 => Measure.dirac 1
  | x + 1 => ENNReal.ofReal (1 - c / (x + 1)) • Measure.dirac (x + 2) +
      ENNReal.ofReal (c / (x + 1)) • Measure.dirac 0

/-- The `c/x` chain. -/
noncomputable def cxKernel (c : ℝ) : Kernel ℕ ℕ where
  toFun := cxLaw c
  measurable' := measurable_of_countable _

/-- The `c/x` chain is Markov for `0 ≤ c ≤ 1`. -/
theorem isMarkovKernel_cxKernel {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsMarkovKernel (cxKernel c) := by
  refine ⟨fun x => ⟨?_⟩⟩
  change cxLaw c x univ = 1
  rcases x with _ | x
  · simp [cxLaw]
  · have hx : (1 : ℝ) ≤ x + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x]
    have h1 : 0 ≤ c / (x + 1) := div_nonneg hc0 (by linarith)
    have h2 : c / (x + 1) ≤ 1 := (div_le_one (by linarith)).2 (hc1.trans hx)
    simp only [cxLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) h1, sub_add_cancel, ENNReal.ofReal_one]

/-- `∫ f dP(x + 1) = (1 − c/(x+1)) f(x + 2) + (c/(x+1)) f(0)` for `f ≥ 0`. -/
theorem cx_lintegral_succ (c : ℝ) (x : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ y, f y ∂cxKernel c (x + 1) =
      ENNReal.ofReal (1 - c / (x + 1)) * f (x + 2) + ENNReal.ofReal (c / (x + 1)) * f 0 := by
  change ∫⁻ y, f y ∂cxLaw c (x + 1) = _
  simp only [cxLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- `∫ f dP(x + 1)` for real `f`. -/
theorem cx_integral_succ (c : ℝ) (x : ℕ) (f : ℕ → ℝ) :
    ∫ y, f y ∂cxKernel c (x + 1) =
      (ENNReal.ofReal (1 - c / (x + 1))).toReal * f (x + 2) +
        (ENNReal.ofReal (c / (x + 1))).toReal * f 0 := by
  change ∫ y, f y ∂cxLaw c (x + 1) = _
  simp only [cxLaw]
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, smul_eq_mul,
    smul_eq_mul]

/-! ### Tail probabilities and recurrence -/

/-- `P_{x+1}(τ₀ ≥ k + 1) = ∏_{j<k} (1 − c/(x + 1 + j))`. -/
theorem cx_tailProb {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k x : ℕ) :
    haveI := isMarkovKernel_cxKernel hc0 hc1
    tailProb (cxKernel c) {0} (k + 1) (x + 1) =
      ENNReal.ofReal (∏ j ∈ Finset.range k, (1 - c / ((x : ℝ) + 1 + j))) := by
  have := isMarkovKernel_cxKernel hc0 hc1
  induction k generalizing x with
  | zero => simp [tailProb_one]
  | succ k ih =>
    rw [tailProb_succ _ (measurableSet_singleton 0), ← lintegral_indicator
      (measurableSet_singleton (0 : ℕ)).compl, cx_lintegral_succ,
      indicator_of_mem (show (x + 2 : ℕ) ∈ ({0} : Set ℕ)ᶜ by simp),
      indicator_of_notMem (show (0 : ℕ) ∉ ({0} : Set ℕ)ᶜ by simp), mul_zero, add_zero,
      show x + 2 = (x + 1) + 1 from rfl, ih (x + 1), Finset.prod_range_succ',
      ← ENNReal.ofReal_mul (by
        have : c / ((x : ℝ) + 1) ≤ 1 :=
          (div_le_one (by positivity)).2 (hc1.trans (by linarith [Nat.cast_nonneg (α := ℝ) x]))
        linarith)]
    congr 1
    rw [mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      push_cast; ring_nf
    · push_cast; ring_nf

/-- **(Corrected)** `P_0(τ₀ ≥ k + 2) = ∏_{x=1}^{k} (1 − c/x)`, i.e.
`P_0(τ₀ > n) = ∏_{x=1}^{n−1} (1 − c/x)`. -/
theorem cx_tail_zero {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ) :
    haveI := isMarkovKernel_cxKernel hc0 hc1
    tailProb (cxKernel c) {0} (k + 2) 0 =
      ENNReal.ofReal (∏ j ∈ Finset.range k, (1 - c / ((j : ℝ) + 1))) := by
  have := isMarkovKernel_cxKernel hc0 hc1
  rw [tailProb_succ _ (measurableSet_singleton 0), ← lintegral_indicator
    (measurableSet_singleton (0 : ℕ)).compl]
  change ∫⁻ y, _ ∂cxLaw c 0 = _
  simp only [cxLaw]
  rw [lintegral_dirac, indicator_of_mem (show (1 : ℕ) ∈ ({0} : Set ℕ)ᶜ by simp),
    cx_tailProb hc0 hc1 k 0]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring_nf

/-- **Correction**: the printed `P_0(τ₀ > n) = ∏_{x=1}^{n} (1 − c/x)` fails at `c = ½`,
`n = 2`: the true value is `½`, the printed one `3/8`. -/
theorem cx_tail_book_counterexample :
    haveI := isMarkovKernel_cxKernel (c := 1 / 2) (by norm_num) (by norm_num)
    tailProb (cxKernel (1 / 2)) {0} 3 0 = ENNReal.ofReal (1 / 2) ∧
      ENNReal.ofReal (1 / 2) ≠
        ENNReal.ofReal (∏ j ∈ Finset.range 2, (1 - (1 / 2) / ((j : ℝ) + 1))) := by
  refine ⟨?_, ?_⟩
  · rw [cx_tail_zero (by norm_num) (by norm_num) 1]
    norm_num
  · rw [Ne, ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by simp [Finset.prod_range_succ]; norm_num)]
    simp [Finset.prod_range_succ]
    norm_num

/-- `∏_{j<k} (1 − c/(j+1)) → 0` for `0 < c ≤ 1`. -/
theorem cx_prod_tendsto_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun k => ∏ j ∈ Finset.range k, (1 - c / ((j : ℝ) + 1))) atTop (𝓝 0) := by
  have hnn : ∀ j : ℕ, 0 ≤ 1 - c / ((j : ℝ) + 1) := fun j => by
    have : c / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (hc1.trans (by linarith [Nat.cast_nonneg (α := ℝ) j]))
    linarith
  have hup : ∀ k, ∏ j ∈ Finset.range k, (1 - c / ((j : ℝ) + 1)) ≤
      Real.exp (-(c * ∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 1)))) := fun k => by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun j _ => hnn j) fun j _ => ?_
    have := Real.add_one_le_exp (-(c * (1 / ((j : ℝ) + 1))))
    rw [mul_one_div] at this ⊢
    linarith
  have hexp : Tendsto (fun k => Real.exp (-(c * ∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 1)))))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop hc0 Real.tendsto_sum_range_one_div_nat_succ_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
    (fun k => Finset.prod_nonneg fun j _ => hnn j) hup

/-- **The `c/x` chain is recurrent** (MT p. 227): `L(0, 0) = 1` and `U(0, 0) = ∞`. -/
theorem cx_recurrent {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    haveI := isMarkovKernel_cxKernel hc0.le hc1
    hitProb (cxKernel c) {0} 0 = 1 ∧ potKernel (cxKernel c) 0 {0} = ∞ := by
  have := isMarkovKernel_cxKernel hc0.le hc1
  have := isMarkovKernel_pathKernel (cxKernel c)
  have hT := measurableSet_firstReturn_ne_top (X := ℕ) (measurableSet_singleton (0 : ℕ))
  have htop : pathKernel (cxKernel c) 0 {ω | firstReturn {0} ω = ⊤} = 0 := by
    rw [pathKernel_firstReturn_top_eq_iInf _ (measurableSet_singleton 0)]
    have hlim : Tendsto (fun k => tailProb (cxKernel c) {0} (k + 2) 0) atTop (𝓝 0) := by
      simp_rw [cx_tail_zero hc0.le hc1]
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (cx_prod_tendsto_zero hc0 hc1)
    exact le_antisymm (ge_of_tendsto' hlim fun k => iInf_le _ (k + 2)) zero_le
  have hL : hitProb (cxKernel c) {0} 0 = 1 := by
    have e : {ω : ℕ → ℕ | firstReturn {0} ω = ⊤} = {ω | firstReturn {0} ω ≠ ⊤}ᶜ := by
      ext; simp
    rw [e, prob_compl_eq_zero_iff hT] at htop
    exact htop
  exact ⟨hL, (proposition_8_1_3 (cxKernel c) 0).2 hL⟩

/-! ### The increments -/

/-- `m(x) = 1 − c − c/x` for `x ≥ 1`. -/
theorem cx_mean {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℕ) :
    ∫ y, ((y : ℝ) - (x + 1 : ℕ)) ∂cxKernel c (x + 1) = 1 - c - c / ((x : ℝ) + 1) := by
  have hx : (1 : ℝ) ≤ x + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x]
  have h1 : 0 ≤ c / ((x : ℝ) + 1) := div_nonneg hc0 (by linarith)
  have h2 : c / ((x : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).2 (hc1.trans hx)
  rw [cx_integral_succ, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal h1]
  push_cast
  field_simp
  ring

/-- `v(x) = cx + 1 − c/x` for `x ≥ 1`. -/
theorem cx_var {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℕ) :
    ∫ y, ((y : ℝ) - (x + 1 : ℕ)) ^ 2 ∂cxKernel c (x + 1) =
      c * ((x : ℝ) + 1) + 1 - c / ((x : ℝ) + 1) := by
  have hx : (1 : ℝ) ≤ x + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x]
  have h1 : 0 ≤ c / ((x : ℝ) + 1) := div_nonneg hc0 (by linarith)
  have h2 : c / ((x : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).2 (hc1.trans hx)
  rw [cx_integral_succ, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal h1]
  push_cast
  field_simp
  ring

/-- **The corrected identity** `x(2x m(x) − v(x)) = (2 − 3c)x² − (2c + 1)x + c`. -/
theorem cx_identity (c X : ℝ) (hX : X ≠ 0) :
    X * (2 * X * (1 - c - c / X) - (c * X + 1 - c / X)) = (2 - 3 * c) * X ^ 2 -
      (2 * c + 1) * X + c := by
  field_simp
  ring

/-- **Correction**: the printed identity fails at `c = ½`, `x = 1`, whether its left side is
read as `2xm(x) − v(x)` or as `x(2xm(x) − v(x))`. -/
theorem cx_identity_book_counterexample :
    let c : ℝ := 1 / 2
    let X : ℝ := 1
    (2 * X * (1 - c - c / X) - (c * X + 1 - c / X)) ≠ (2 - 3 * c) * X ^ 2 - (c + 1) * X + c ∧
      X * (2 * X * (1 - c - c / X) - (c * X + 1 - c / X)) ≠
        (2 - 3 * c) * X ^ 2 - (c + 1) * X + c := by
  norm_num

/-- **(9.69) holds for `c < 2/3`**: with `θ = (2 − c)/(2c) > 1`, `m(x) ≥ θ v(x)/2x` for all
`x ≥ x₀`; the chain is nonetheless recurrent (`cx_recurrent`). -/
theorem cx_drift_condition {c : ℝ} (hc0 : 0 < c) (hc23 : c < 2 / 3) :
    ∃ θ : ℝ, 1 < θ ∧ ∃ x₀ : ℝ, ∀ X : ℝ, x₀ ≤ X →
      θ * (c * X + 1 - c / X) / (2 * X) ≤ 1 - c - c / X := by
  refine ⟨(2 - c) / (2 * c), by rw [lt_div_iff₀ (by positivity)]; linarith,
    max 1 ((2 * c + (2 - c) / (2 * c)) / ((2 - 3 * c) / 2)), fun X hX => ?_⟩
  set θ := (2 - c) / (2 * c)
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) (by positivity)
  have hk : 0 < (2 - 3 * c) / 2 := by linarith
  have hX2 : (2 * c + θ) / ((2 - 3 * c) / 2) ≤ X := (le_max_right _ _).trans hX
  rw [div_le_iff₀ hk] at hX2
  have hθc : θ * c = (2 - c) / 2 := by simp only [θ]; field_simp
  rw [div_le_iff₀ (by positivity)]
  have key : θ * (c * X + 1 - c / X) ≤ (1 - c - c / X) * (2 * X) := by
    have e1 : θ * (c * X + 1 - c / X) = (θ * c) * X + θ - θ * c / X := by ring
    have e2 : (1 - c - c / X) * (2 * X) = 2 * X - 2 * c * X - 2 * c := by field_simp
    rw [e1, e2, hθc]
    have : 0 ≤ (2 - c) / 2 / X := div_nonneg (by linarith) hX0.le
    nlinarith
  linarith

/-- `E_x|Φ₁ − x|^{2+ε} = (1 − c/x) + (c/x) x^{2+ε}` for `x ≥ 1`. -/
theorem cx_moment {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ε : ℝ) (x : ℕ) :
    ∫ y, |(y : ℝ) - (x + 1 : ℕ)| ^ (2 + ε) ∂cxKernel c (x + 1) =
      (1 - c / ((x : ℝ) + 1)) + c / ((x : ℝ) + 1) * ((x : ℝ) + 1) ^ (2 + ε) := by
  have hx : (1 : ℝ) ≤ x + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x]
  have h1 : 0 ≤ c / ((x : ℝ) + 1) := div_nonneg hc0 (by linarith)
  have h2 : c / ((x : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).2 (hc1.trans hx)
  rw [cx_integral_succ, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal h1]
  push_cast
  have e1 : |(x : ℝ) + 2 - (x + 1)| = 1 := by norm_num [show (x : ℝ) + 2 - (x + 1) = 1 by ring]
  have e2 : |(0 : ℝ) - (x + 1)| = (x : ℝ) + 1 := by
    rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
  rw [e1, e2, Real.one_rpow, mul_one]

/-- **`sup_x E_x|W_x|^{2+ε} = ∞`**: the moment hypothesis of Theorem 9.5.6 fails. -/
theorem cx_moment_unbounded {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ x : ℕ, B < ∫ y, |(y : ℝ) - (x + 1 : ℕ)| ^ (2 + ε) ∂cxKernel c (x + 1) := by
  obtain ⟨x, hx⟩ := exists_nat_ge ((|B| + 1) / c)
  refine ⟨x, ?_⟩
  rw [cx_moment hc0.le hc1]
  have hX : (1 : ℝ) ≤ x + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x]
  have hX0 : (0 : ℝ) < x + 1 := by linarith
  have h2 : c / ((x : ℝ) + 1) ≤ 1 := (div_le_one hX0).2 (hc1.trans hX)
  have hpow : ((x : ℝ) + 1) ^ (2 : ℝ) ≤ ((x : ℝ) + 1) ^ (2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hsq : ((x : ℝ) + 1) ^ (2 : ℝ) = ((x : ℝ) + 1) ^ 2 := by norm_cast
  have hcx : c / ((x : ℝ) + 1) * ((x : ℝ) + 1) ^ (2 + ε) ≥ c * ((x : ℝ) + 1) := by
    calc c / ((x : ℝ) + 1) * ((x : ℝ) + 1) ^ (2 + ε)
        ≥ c / ((x : ℝ) + 1) * ((x : ℝ) + 1) ^ 2 := by
          rw [← hsq]; exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = c * ((x : ℝ) + 1) := by field_simp
  rw [div_le_iff₀ hc0] at hx
  linarith [le_abs_self B]

/-- **Correction**: the printed bound `E_x|W_x|^{2+ε} > x^{1+ε}` fails: at `c = ½`, `ε = 1`,
`x = 4` the moment is `71/8 < 16`. -/
theorem cx_moment_book_counterexample :
    ∫ y, |(y : ℝ) - ((3 : ℕ) + 1 : ℕ)| ^ ((2 : ℝ) + 1) ∂cxKernel (1 / 2) (3 + 1) <
      ((3 : ℝ) + 1) ^ ((1 : ℝ) + 1) := by
  rw [cx_moment (by norm_num) (by norm_num)]
  norm_num

end MeynTweedie.HarrisRecurrence
