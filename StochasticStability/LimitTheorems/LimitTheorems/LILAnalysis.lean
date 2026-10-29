/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Real analysis for the law of the iterated logarithm

Deterministic tools for the Hartman–Wintner LIL (`IIDLIL`), used in the LIL parts of
MT Theorems 17.2.2 and 17.3.6 (pp. 430, 441) and Theorem 17.0.1 (iv) (p. 422).

* `lilScale n = √(2 n log log n)`, the normaliser of the LIL (MT p. 422), with
  `lilScale_mono`, `lilScale_sq`, `sqrt_le_lilScale`, `tendsto_lilScale`, and the ratio limit
  `tendsto_lilScale_div` (`mₙ/n → c > 0` gives `lilScale mₙ / lilScale n → √c`).
* `loglog_increment`, `lilPhi_increment`, `sqrt_lilPhi_increment`: increments of `log log x` and
  of `φ(x) = x / log log x`.
* **Kronecker's lemma** for non-negative terms (`tendsto_sum_div_of_summable`).
* Geometric index sequences: `eventually_floor_pow_succ_le`,
  `summable_exp_neg_mul_loglog_floor_pow` (`Σₖ (log ⌊θᵏ⌋)^{−p} < ∞` for `p > 1`) and
  `not_summable_exp_neg_mul_loglog_pow` (`Σₖ (log mᵏ)^{−p} = ∞` for `p ≤ 1`).
* The truncation levels `lilTruncLevel δ j₀ j = δ √φ(max j j₀)` and weights
  `lilWeight j₀ j = √(J log log J)`, `J = max j j₀`, with the counting estimate
  `sum_inv_lilWeight_le`: `Σ_{j : τⱼ < y} 1/wⱼ ≤ j₀/w_{j₀} + 8 (y/δ + 1)`.
-/

namespace MeynTweedie.LimitTheorems

open Filter Topology

/-- The LIL normaliser `√(2 n log log n)`. -/
noncomputable def lilScale (n : ℕ) : ℝ := √(2 * n * Real.log (Real.log n))

/-- `log log x ≥ 1` once `log x ≥ 3`. -/
theorem one_le_loglog {x : ℝ} (hx : 3 ≤ Real.log x) : 1 ≤ Real.log (Real.log x) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- Eventually `log n ≥ c`. -/
theorem eventually_le_log (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- `log (x + 1) − log x ≤ 1/x` for `x > 0`. -/
theorem log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [← Real.log_div (by linarith) hx.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- The increment of `log log`: for `log x ≥ 3`,
`0 ≤ log log (x + 1) − log log x ≤ 1/(x log x)`. -/
theorem loglog_increment {x : ℝ} (hx : 1 ≤ x) (hl : 3 ≤ Real.log x) :
    0 ≤ Real.log (Real.log (x + 1)) - Real.log (Real.log x) ∧
      Real.log (Real.log (x + 1)) - Real.log (Real.log x) ≤ 1 / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := by linarith
  have hle : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hlx1 : 0 < Real.log (x + 1) := by linarith
  constructor
  · have := Real.log_le_log hlx hle
    linarith
  · rw [← Real.log_div hlx1.ne' hlx.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log (x + 1) / Real.log x by positivity)
    have h2 := log_add_one_sub_log_le hx0
    have e : Real.log (x + 1) / Real.log x - 1 = (Real.log (x + 1) - Real.log x) / Real.log x := by
      field_simp
    have h3 : (Real.log (x + 1) - Real.log x) / Real.log x ≤ (1 / x) / Real.log x :=
      div_le_div_of_nonneg_right h2 hlx.le
    have e2 : (1 / x) / Real.log x = 1 / (x * Real.log x) := by field_simp
    linarith

/-- `φ(x) = x / log log x`, the square of the truncation level of the LIL (up to a constant). -/
noncomputable def lilPhi (x : ℝ) : ℝ := x / Real.log (Real.log x)

/-- The increments of `φ(x) = x / log log x` for `log x ≥ 3`:
`φ(x) + 1/(2 log log (x+1)) ≤ φ(x + 1) ≤ φ(x) + 1`. -/
theorem lilPhi_increment {x : ℝ} (hx : 1 ≤ x) (hl : 3 ≤ Real.log x) :
    lilPhi x + 1 / (2 * Real.log (Real.log (x + 1))) ≤ lilPhi (x + 1) ∧
      lilPhi (x + 1) ≤ lilPhi x + 1 := by
  obtain ⟨hd0, hd1⟩ := loglog_increment hx hl
  set A := Real.log (Real.log x) with hA
  set A' := Real.log (Real.log (x + 1)) with hA'
  have hA1 : 1 ≤ A := one_le_loglog hl
  have hA'1 : A ≤ A' := by linarith
  have hx0 : 0 < x := by linarith
  have hjd : x * (A' - A) ≤ 1 / 3 := by
    have h1 : x * (A' - A) ≤ x * (1 / (x * Real.log x)) :=
      mul_le_mul_of_nonneg_left hd1 hx0.le
    have h2 : x * (1 / (x * Real.log x)) = 1 / Real.log x := by
      field_simp
    have h3 : 1 / Real.log x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hl
    linarith
  have hA0 : 0 < A := by linarith
  have hA'0 : 0 < A' := by linarith
  simp only [lilPhi]
  rw [← hA, ← hA']
  constructor
  · rw [div_add_div _ _ hA0.ne' (by positivity), div_le_div_iff₀ (by positivity) hA'0]
    nlinarith
  · rw [div_add_one hA0.ne', div_le_div_iff₀ hA'0 hA0]
    nlinarith

/-- The increments of `√φ`: for `log x ≥ 3`, `1/(8 √(x log log x)) ≤ √φ(x + 1) − √φ(x)`. -/
theorem sqrt_lilPhi_increment {x : ℝ} (hx : 1 ≤ x) (hl : 3 ≤ Real.log x) :
    1 / (8 * √(x * Real.log (Real.log x))) ≤ √(lilPhi (x + 1)) - √(lilPhi x) := by
  obtain ⟨h1, -⟩ := lilPhi_increment hx hl
  obtain ⟨hd0, hd1⟩ := loglog_increment hx hl
  set A := Real.log (Real.log x) with hA
  set A' := Real.log (Real.log (x + 1)) with hA'
  have hA1 : 1 ≤ A := one_le_loglog hl
  have hx0 : 0 < x := by linarith
  have hA0 : 0 < A := by linarith
  have hA'0 : 0 < A' := by linarith
  have hlx : 0 < Real.log x := by linarith
  -- `A' ≤ 2 A`
  have hA'2 : A' ≤ 2 * A := by
    have : 1 / (x * Real.log x) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  set u := √(lilPhi (x + 1)) with hu
  set v := √(lilPhi x) with hv
  have hφ0 : 0 ≤ lilPhi x := div_nonneg hx0.le hA0.le
  have hφ1 : 0 < lilPhi (x + 1) := div_pos (by linarith) hA'0
  have hu0 : 0 < u := Real.sqrt_pos.2 hφ1
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hpos' : 0 < 1 / (2 * A') := by positivity
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  have hu2 : u ^ 2 = lilPhi (x + 1) := Real.sq_sqrt hφ1.le
  have hv2 : v ^ 2 = lilPhi x := Real.sq_sqrt hφ0
  -- `u − v ≥ (u² − v²)/(2u) ≥ 1/(4 A' u)`
  have hdiff : 1 / (2 * A') ≤ u ^ 2 - v ^ 2 := by rw [hu2, hv2]; linarith
  have huv : 1 / (4 * A' * u) ≤ u - v := by
    have e : u - v = (u ^ 2 - v ^ 2) / (u + v) := by
      field_simp [show u + v ≠ 0 by linarith]
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by linarith)]
    have h4 := mul_le_mul_of_nonneg_right hdiff (show 0 ≤ 4 * A' * u by positivity)
    have h5 : 1 / (2 * A') * (4 * A' * u) = 2 * u := by field_simp; ring
    linarith
  -- `A' u = √(A' (x + 1))` and `A' (x + 1) ≤ 4 x A`
  have hAu : A' * u = √(A' * (x + 1)) := by
    have e1 : A' * u = √(A' ^ 2 * lilPhi (x + 1)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA'0.le]
    rw [e1, lilPhi, ← hA']
    congr 1
    field_simp
  have hsq : √(A' * (x + 1)) ≤ 2 * √(x * A) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hpos : 0 < √(x * A) := Real.sqrt_pos.2 (by positivity)
  calc 1 / (8 * √(x * A)) ≤ 1 / (4 * √(A' * (x + 1))) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
    _ = 1 / (4 * A' * u) := by rw [mul_assoc, hAu]
    _ ≤ u - v := huv

/-! ### Kronecker's lemma for non-negative terms -/

/-- **Kronecker's lemma** for non-negative terms: if `aⱼ ≥ 0`, `0 < wⱼ` increases to `∞` and
`Σ aⱼ/wⱼ < ∞`, then `(Σ_{j<n} aⱼ)/wₙ → 0`. -/
theorem tendsto_sum_div_of_summable {a w : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hw : ∀ j, 0 < w j)
    (hmono : Monotone w) (hwt : Tendsto w atTop atTop) (hs : Summable fun j => a j / w j) :
    Tendsto (fun n => (∑ j ∈ Finset.range n, a j) / w n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail := tendsto_sum_nat_add fun j => a j / w j
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 htail) (ε / 2) (by positivity)
  have hK' := hK K le_rfl
  have hT0 : 0 ≤ ∑' i, a (i + K) / w (i + K) :=
    tsum_nonneg fun i => div_nonneg (ha _) (hw _).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hT0] at hK'
  set C := ∑ j ∈ Finset.range K, a j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => ha j
  have hCw : Tendsto (fun n => C / w n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hwt
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hCw) (ε / 2) (by positivity)
  refine ⟨max K N, fun n hn => ?_⟩
  have hKn : K ≤ n := le_of_max_le_left hn
  have hNn : N ≤ n := le_of_max_le_right hn
  have hCn := hN n hNn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hC0 (hw n).le)] at hCn
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, a j := Finset.sum_nonneg fun j _ => ha j
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsum0 (hw n).le)]
  -- the sum over `[K, n)`
  have hIco : ∑ j ∈ Finset.Ico K n, a j ≤ w n * ∑' i, a (i + K) / w (i + K) := by
    have h1 : ∑ j ∈ Finset.Ico K n, a j ≤ ∑ j ∈ Finset.Ico K n, w n * (a j / w j) :=
      Finset.sum_le_sum fun j hj => by
        have hjn : j ≤ n := (Finset.mem_Ico.1 hj).2.le
        rw [mul_div_assoc', le_div_iff₀ (hw j)]
        rw [mul_comm (w n)]
        exact mul_le_mul_of_nonneg_left (hmono hjn) (ha j)
    have h2 : ∑ j ∈ Finset.Ico K n, a j / w j ≤ ∑' i, a (i + K) / w (i + K) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hsK : Summable fun i => a (i + K) / w (i + K) := (summable_nat_add_iff K).2 hs
      calc ∑ i ∈ Finset.range (n - K), a (K + i) / w (K + i)
          = ∑ i ∈ Finset.range (n - K), a (i + K) / w (i + K) := by
            simp_rw [add_comm K]
        _ ≤ _ := hsK.sum_le_tsum _ fun i _ => div_nonneg (ha _) (hw _).le
    rw [← Finset.mul_sum] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (hw n).le)
  have hsplit : ∑ j ∈ Finset.range n, a j = C + ∑ j ∈ Finset.Ico K n, a j :=
    (Finset.sum_range_add_sum_Ico _ hKn).symm
  rw [hsplit, add_div]
  have h3 : (∑ j ∈ Finset.Ico K n, a j) / w n ≤ ∑' i, a (i + K) / w (i + K) := by
    rw [div_le_iff₀ (hw n)]; linarith
  linarith

/-! ### The LIL normaliser -/

/-- `lilScale n ≥ 0`. -/
theorem lilScale_nonneg (n : ℕ) : 0 ≤ lilScale n := Real.sqrt_nonneg _

/-- `lilScale n² = 2 n log log n` when `log n ≥ 3`. -/
theorem lilScale_sq {n : ℕ} (h : 3 ≤ Real.log n) :
    lilScale n ^ 2 = 2 * n * Real.log (Real.log n) := by
  have := one_le_loglog h
  rw [lilScale, Real.sq_sqrt (by positivity)]

/-- `lilScale` is monotone beyond `log n ≥ 3`. -/
theorem lilScale_mono {m n : ℕ} (hm : 3 ≤ Real.log m) (hmn : m ≤ n) :
    lilScale m ≤ lilScale n := by
  have h1 := one_le_loglog hm
  have hm0 : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hm; linarith
    · exact_mod_cast h
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hl : Real.log m ≤ Real.log n := Real.log_le_log hm0 hmn'
  have hll : Real.log (Real.log m) ≤ Real.log (Real.log n) :=
    Real.log_le_log (by linarith) hl
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ m := hm0.le
  nlinarith

/-- `√n ≤ lilScale n` when `log n ≥ 3`. -/
theorem sqrt_le_lilScale {n : ℕ} (h : 3 ≤ Real.log n) : √(n : ℝ) ≤ lilScale n := by
  have := one_le_loglog h
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `lilScale n → ∞`. -/
theorem tendsto_lilScale : Tendsto lilScale atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_le_log 3] with n hn
  exact sqrt_le_lilScale hn

/-- `lilScale n > 0` when `log n ≥ 3`. -/
theorem lilScale_pos {n : ℕ} (h : 3 ≤ Real.log n) : 0 < lilScale n := by
  have := one_le_loglog h
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at h; linarith
    · exact_mod_cast h0
  exact Real.sqrt_pos.2 (by positivity)

/-! ### Geometric index sequences -/

/-- For `θ > 1`, eventually `⌊θ^(k+1)⌋ ≤ θ² ⌊θ^k⌋`. -/
theorem eventually_floor_pow_succ_le {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ k : ℕ in atTop, (⌊θ ^ (k + 1)⌋₊ : ℝ) ≤ θ ^ 2 * ⌊θ ^ k⌋₊ := by
  have ht : Tendsto (fun k : ℕ => θ ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hθ
  filter_upwards [ht.eventually_ge_atTop (θ ^ 2 / (θ - 1))] with k hk
  have hθ1 : 0 < θ - 1 := by linarith
  have hθ0 : 0 < θ := by linarith
  have hpk : 0 < θ ^ k := by positivity
  have h1 : (⌊θ ^ (k + 1)⌋₊ : ℝ) ≤ θ ^ (k + 1) := Nat.floor_le (by positivity)
  have h2 : θ ^ k - 1 ≤ (⌊θ ^ k⌋₊ : ℝ) := by have := Nat.lt_floor_add_one (θ ^ k); linarith
  have h3 : θ ^ 2 ≤ θ ^ k * (θ - 1) := by rwa [div_le_iff₀ hθ1] at hk
  have h4 : θ ^ (k + 1) ≤ θ ^ 2 * (θ ^ k - 1) := by
    have e : θ ^ (k + 1) = θ ^ k * θ := pow_succ θ k
    have h5 : 0 ≤ θ ^ k * (θ - 1) ^ 2 := by positivity
    nlinarith
  have h6 : θ ^ 2 * (θ ^ k - 1) ≤ θ ^ 2 * ⌊θ ^ k⌋₊ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- For `θ > 1` and `p > 1`, `Σₖ exp(−p log log ⌊θ^k⌋) < ∞`. -/
theorem summable_exp_neg_mul_loglog_floor_pow {θ p : ℝ} (hθ : 1 < θ) (hp : 1 < p) :
    Summable fun k : ℕ => Real.exp (-(p * Real.log (Real.log (⌊θ ^ k⌋₊ : ℝ)))) := by
  have hlθ : 0 < Real.log θ := Real.log_pos hθ
  set c := Real.log θ / 2 with hc
  have hc0 : 0 < c := by positivity
  have hg : Summable fun k : ℕ => c ^ (-p) * (k : ℝ) ^ (-p) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left _
  refine hg.of_norm_bounded_eventually_nat ?_
  have ht : Tendsto (fun k : ℕ => θ ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hθ
  have ht2 : Tendsto (fun k : ℕ => (k : ℝ) * Real.log θ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlθ
  filter_upwards [ht.eventually_ge_atTop 2, ht2.eventually_ge_atTop (2 * Real.log 2),
    eventually_ge_atTop 1] with k hk1 hk2 hk3
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk3
  have hfl : θ ^ k / 2 ≤ (⌊θ ^ k⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (θ ^ k); linarith
  have hlog : c * k ≤ Real.log (⌊θ ^ k⌋₊ : ℝ) := by
    have h1 : Real.log (θ ^ k / 2) ≤ Real.log (⌊θ ^ k⌋₊ : ℝ) :=
      Real.log_le_log (by positivity) hfl
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h1
    have : c * k = k * Real.log θ / 2 := by rw [hc]; ring
    linarith
  have hll : Real.log (c * k) ≤ Real.log (Real.log (⌊θ ^ k⌋₊ : ℝ)) :=
    Real.log_le_log (by positivity) hlog
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(p * Real.log (Real.log (⌊θ ^ k⌋₊ : ℝ))))
      ≤ Real.exp (Real.log (c * k) * (-p)) := by
        apply Real.exp_le_exp.2; nlinarith
    _ = (c * k) ^ (-p) := (Real.rpow_def_of_pos (by positivity) _).symm
    _ = c ^ (-p) * (k : ℝ) ^ (-p) := Real.mul_rpow hc0.le (by positivity)

/-- For an integer `m ≥ 2`, `C > 0` and `p ≤ 1`, `Σₖ C exp(−p log log mᵏ) = ∞`. -/
theorem not_summable_exp_neg_mul_loglog_pow {m : ℕ} (hm : 2 ≤ m) {p : ℝ} (hp : p ≤ 1)
    {C : ℝ} (hC : 0 < C) :
    ¬ Summable fun k : ℕ => C * Real.exp (-(p * Real.log (Real.log ((m : ℝ) ^ k)))) := by
  intro h
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hlm : 0 < Real.log m := Real.log_pos hm1
  have h2 := (summable_nat_add_iff 1).2 h
  have h3 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-p) := by
    refine (h2.mul_left (C⁻¹ * Real.log m ^ p)).congr fun k => ?_
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
    have hK0 : 0 < K := by positivity
    have e1 : Real.log (Real.log ((m : ℝ) ^ (k + 1))) = Real.log K + Real.log (Real.log m) := by
      rw [Real.log_pow, Real.log_mul hK0.ne' hlm.ne']
    have e2 : Real.exp (-(p * (Real.log K + Real.log (Real.log m)))) =
        K ^ (-p) * Real.log m ^ (-p) := by
      rw [Real.rpow_def_of_pos hK0, Real.rpow_def_of_pos hlm, ← Real.exp_add]
      ring_nf
    have e3 : Real.log m ^ p * Real.log m ^ (-p) = 1 := by
      rw [← Real.rpow_add hlm, add_neg_cancel, Real.rpow_zero]
    rw [e1, e2]
    calc C⁻¹ * Real.log m ^ p * (C * (K ^ (-p) * Real.log m ^ (-p)))
        = (C⁻¹ * C) * (Real.log m ^ p * Real.log m ^ (-p)) * K ^ (-p) := by ring
      _ = K ^ (-p) := by rw [inv_mul_cancel₀ hC.ne', e3]; ring
  exact absurd (Real.summable_nat_rpow.1 ((summable_nat_add_iff 1).1 h3)) (by linarith)

/-! ### Ratios of the normaliser -/

/-- If `mₙ/n → c > 0` then `log log mₙ / log log n → 1`. -/
theorem tendsto_loglog_div {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n => Real.log (Real.log (m n)) / Real.log (Real.log n)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `mₙ → ∞`
  have hmt : Tendsto (fun n => (m n : ℝ)) atTop atTop := by
    refine (hm.pos_mul_atTop hc hn).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hlog := Real.tendsto_log_atTop.comp hn
  have hlogm := Real.tendsto_log_atTop.comp hmt
  -- `log mₙ − log n → log c`
  have h1 : Tendsto (fun n => Real.log (m n) - Real.log n) atTop (𝓝 (Real.log c)) := by
    refine ((Real.continuousAt_log hc.ne').tendsto.comp hm).congr' ?_
    filter_upwards [eventually_ge_atTop 1, hmt.eventually_gt_atTop 0] with n hn1 hm0
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Function.comp_apply]
    rw [Real.log_div hm0.ne' this]
  -- `log mₙ / log n → 1`
  have h2 : Tendsto (fun n => Real.log (m n) / Real.log n) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)).add (h1.div_atTop hlog)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn0
    simp only [Function.comp_apply] at hn0 ⊢
    field_simp
    ring
  -- `log log mₙ − log log n → 0`
  have h3 : Tendsto (fun n => Real.log (Real.log (m n)) - Real.log (Real.log n)) atTop
      (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h2
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0, hlogm.eventually_gt_atTop 0] with n hn0 hm0
    simp only [Function.comp_apply] at hn0 hm0 ⊢
    rw [Real.log_div hm0.ne' hn0.ne']
  have hll := Real.tendsto_log_atTop.comp hlog
  have := tendsto_const_nhds (x := (1 : ℝ)).add (h3.div_atTop hll)
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hll.eventually_gt_atTop 0] with n hn0
  simp only [Function.comp_apply] at hn0 ⊢
  field_simp
  ring

/-- If `mₙ/n → c > 0` then `lilScale mₙ / lilScale n → √c`. -/
theorem tendsto_lilScale_div {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n => lilScale (m n) / lilScale n) atTop (𝓝 √c) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmt : Tendsto (fun n => (m n : ℝ)) atTop atTop := by
    refine (hm.pos_mul_atTop hc hn).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hl := tendsto_loglog_div hc hm
  have hprod := hm.mul hl
  rw [mul_one] at hprod
  have hs := (Real.continuous_sqrt.tendsto c).comp hprod
  refine hs.congr' ?_
  have hm3 : ∀ᶠ n in atTop, 3 ≤ Real.log (m n) :=
    (Real.tendsto_log_atTop.comp hmt).eventually_ge_atTop 3
  filter_upwards [hm3, eventually_le_log 3] with n hm3 hn3
  have h1 := one_le_loglog hm3
  have h2 := one_le_loglog hn3
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at hn3; linarith
    · exact_mod_cast h0
  simp only [Function.comp_apply, lilScale]
  rw [← Real.sqrt_div' _ (by positivity)]
  congr 1
  field_simp

/-! ### Truncation levels and weights for the upper half -/

/-- The truncation level `δ √φ(max j j₀)` of the upper half of the LIL. -/
noncomputable def lilTruncLevel (δ : ℝ) (j₀ j : ℕ) : ℝ := δ * √(lilPhi (max j j₀ : ℕ))

/-- The Kronecker weight `√(J log log J)`, `J = max j j₀`. -/
noncomputable def lilWeight (j₀ j : ℕ) : ℝ :=
  √((max j j₀ : ℕ) * Real.log (Real.log (max j j₀ : ℕ)))

/-- `log j ≥ 3` for every `j ≥ j₀` once `log j₀ ≥ 3`. -/
theorem three_le_log_of_le {j₀ j : ℕ} (hj₀ : 3 ≤ Real.log j₀) (hj : j₀ ≤ j) :
    3 ≤ Real.log j := by
  have h0 : (0 : ℝ) < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · simp [h] at hj₀; linarith
    · exact_mod_cast h
  exact hj₀.trans (Real.log_le_log h0 (by exact_mod_cast hj))

/-- `1 ≤ x` when `3 ≤ log x` and `0 ≤ x`. -/
theorem one_le_of_three_le_log {x : ℝ} (hx0 : 0 ≤ x) (h : 3 ≤ Real.log x) : 1 ≤ x := by
  by_contra hx
  push Not at hx
  have := Real.log_nonpos hx0 hx.le
  linarith

/-- The weights are positive when `log j₀ ≥ 3`. -/
theorem lilWeight_pos {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) (j : ℕ) : 0 < lilWeight j₀ j := by
  have h3 := three_le_log_of_le hj₀ (le_max_right j j₀)
  have := one_le_loglog h3
  have := one_le_of_three_le_log (Nat.cast_nonneg _) h3
  exact Real.sqrt_pos.2 (by positivity)

/-- The weights are monotone. -/
theorem lilWeight_mono {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) : Monotone (lilWeight j₀) := by
  intro i j hij
  have hi := three_le_log_of_le hj₀ (le_max_right i j₀)
  have hj := three_le_log_of_le hj₀ (le_max_right j j₀)
  have h1 := one_le_loglog hi
  have hi1 := one_le_of_three_le_log (Nat.cast_nonneg _) hi
  have hmax : ((max i j₀ : ℕ) : ℝ) ≤ (max j j₀ : ℕ) := by
    exact_mod_cast max_le_max hij le_rfl
  have hl : Real.log (max i j₀ : ℕ) ≤ Real.log (max j j₀ : ℕ) :=
    Real.log_le_log (by linarith) hmax
  have hll : Real.log (Real.log (max i j₀ : ℕ)) ≤ Real.log (Real.log (max j j₀ : ℕ)) :=
    Real.log_le_log (by linarith) hl
  apply Real.sqrt_le_sqrt
  nlinarith

/-- The weights tend to infinity. -/
theorem tendsto_lilWeight {j₀ : ℕ} : Tendsto (lilWeight j₀) atTop atTop := by
  refine (tendsto_lilScale.const_mul_atTop (show (0 : ℝ) < (√2)⁻¹ by positivity)).congr' ?_
  filter_upwards [eventually_ge_atTop j₀] with j hj
  rw [lilWeight, lilScale, max_eq_left hj, mul_assoc, Real.sqrt_mul (by norm_num),
    ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `lilScale j = √2 · lilWeight j₀ j` for `j ≥ j₀`. -/
theorem lilScale_eq_lilWeight {j₀ j : ℕ} (hj : j₀ ≤ j) :
    lilScale j = √2 * lilWeight j₀ j := by
  rw [lilWeight, lilScale, max_eq_left hj, mul_assoc, Real.sqrt_mul (by norm_num)]

/-- `√(a + 1) ≤ √a + 1` for `a ≥ 0`. -/
theorem sqrt_add_one_le (a : ℝ) (ha : 0 ≤ a) : √(a + 1) ≤ √a + 1 := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha
  have := Real.sqrt_nonneg a
  nlinarith

/-- **The counting estimate for the truncated tails**: for `δ > 0` and `y ≥ 0`,
`Σ_{j<n, τⱼ < y} 1/wⱼ ≤ j₀/w_{j₀} + 8 (y/δ + 1)`, where `τⱼ = lilTruncLevel δ j₀ j` and
`wⱼ = lilWeight j₀ j`. -/
theorem sum_inv_lilWeight_le {δ : ℝ} (hδ : 0 < δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀)
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    ∑ j ∈ Finset.range n, (if lilTruncLevel δ j₀ j < y then 1 / lilWeight j₀ j else 0) ≤
      j₀ / lilWeight j₀ j₀ + 8 * (y / δ + 1) := by
  set f : ℕ → ℝ := fun j => if lilTruncLevel δ j₀ j < y then 1 / lilWeight j₀ j else 0
    with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    simp only [hf]
    split_ifs
    · exact (one_div_pos.2 (lilWeight_pos hj₀ j)).le
    · exact le_rfl
  have hfle : ∀ j, f j ≤ 1 / lilWeight j₀ j := fun j => by
    simp only [hf]
    split_ifs
    · exact le_rfl
    · exact (one_div_pos.2 (lilWeight_pos hj₀ j)).le
  -- the values of `φ` beyond `j₀`
  set g : ℕ → ℝ := fun N => √(lilPhi (N : ℝ)) with hg
  have hstep : ∀ N, j₀ ≤ N → 1 / lilWeight j₀ N ≤ 8 * (g (N + 1) - g N) ∧ g N ≤ g (N + 1) ∧
      g (N + 1) ≤ g N + 1 := by
    intro N hN
    have h3 := three_le_log_of_le hj₀ hN
    have h1 := one_le_of_three_le_log (Nat.cast_nonneg _) h3
    obtain ⟨hi1, hi2⟩ := lilPhi_increment h1 h3
    have hinc := sqrt_lilPhi_increment h1 h3
    have hA := one_le_loglog h3
    have hA' : 0 < Real.log (Real.log ((N : ℝ) + 1)) := by
      have := (loglog_increment h1 h3).1; linarith
    have hφ0 : 0 ≤ lilPhi N := div_nonneg (by linarith) (by linarith)
    have hw : lilWeight j₀ N = √((N : ℝ) * Real.log (Real.log N)) := by
      rw [lilWeight, max_eq_left hN]
    simp only [hg]
    push_cast
    have hpos : 0 < 1 / (2 * Real.log (Real.log ((N : ℝ) + 1))) := by positivity
    have hmono : √(lilPhi N) ≤ √(lilPhi ((N : ℝ) + 1)) := Real.sqrt_le_sqrt (by linarith)
    refine ⟨?_, hmono, (Real.sqrt_le_sqrt hi2).trans (sqrt_add_one_le _ hφ0)⟩
    rw [hw]
    have : 1 / √((N : ℝ) * Real.log (Real.log N)) =
        8 * (1 / (8 * √((N : ℝ) * Real.log (Real.log N)))) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hinc (by norm_num)
  -- induction beyond `j₀`
  have hind : ∀ N, j₀ ≤ N → ∑ j ∈ Finset.Ico j₀ N, f j ≤ 8 * min (g N) (y / δ + 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Finset.Ico_self, Finset.sum_empty]
      have : 0 ≤ g j₀ := Real.sqrt_nonneg _
      have : 0 ≤ y / δ + 1 := by positivity
      positivity
    | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN]
      obtain ⟨hs1, hs2, hs3⟩ := hstep N hN
      by_cases hlt : lilTruncLevel δ j₀ N < y
      · have hfN : f N = 1 / lilWeight j₀ N := by simp only [hf, hlt, ite_true]
        have hgN : g N < y / δ := by
          rw [lilTruncLevel, max_eq_left hN] at hlt
          rw [lt_div_iff₀ hδ]
          simp only [hg]
          linarith
        have hmin1 : min (g N) (y / δ + 1) ≤ g N := min_le_left _ _
        have hmin2 : min (g (N + 1)) (y / δ + 1) = g (N + 1) :=
          min_eq_left (by linarith)
        rw [hfN, hmin2]
        linarith
      · have hfN : f N = 0 := by simp only [hf, hlt, ite_false]
        rw [hfN, add_zero]
        exact ih.trans (mul_le_mul_of_nonneg_left (min_le_min hs2 le_rfl) (by norm_num))
  -- the first `j₀` terms
  have hfirst : ∑ j ∈ Finset.range j₀, f j ≤ j₀ / lilWeight j₀ j₀ := by
    calc ∑ j ∈ Finset.range j₀, f j ≤ ∑ _j ∈ Finset.range j₀, 1 / lilWeight j₀ j₀ :=
          Finset.sum_le_sum fun j hj => by
            have : lilWeight j₀ j = lilWeight j₀ j₀ := by
              rw [lilWeight, lilWeight, max_eq_right (Finset.mem_range.1 hj).le, max_self]
            rw [← this]; exact hfle j
      _ = j₀ / lilWeight j₀ j₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
  calc ∑ j ∈ Finset.range n, f j ≤ ∑ j ∈ Finset.range (max n j₀), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left _ _))
          fun j _ _ => hf0 j
    _ = ∑ j ∈ Finset.range j₀, f j + ∑ j ∈ Finset.Ico j₀ (max n j₀), f j :=
        (Finset.sum_range_add_sum_Ico _ (le_max_right _ _)).symm
    _ ≤ j₀ / lilWeight j₀ j₀ + 8 * min (g (max n j₀)) (y / δ + 1) :=
        add_le_add hfirst (hind _ (le_max_right _ _))
    _ ≤ j₀ / lilWeight j₀ j₀ + 8 * (y / δ + 1) := by
        have := min_le_right (g (max n j₀)) (y / δ + 1)
        linarith

end MeynTweedie.LimitTheorems
