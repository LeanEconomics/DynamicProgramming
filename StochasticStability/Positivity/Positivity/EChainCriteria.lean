/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.EChainInvariant
import Positivity.PositiveNull
import Positivity.Accessibility

/-!
# Hitting times and drift criteria for e-chains (MT §12.4.2, (12.24))

Meyn and Tweedie, §12.4, pp. 300–305. `X` is a locally compact, second-countable, metrizable
Hausdorff space with its Borel σ-algebra; `Π = eChainLimit he` is the limit kernel of the e-chain
(`EChainInvariant`), and `u(x) = Π(x, X)` (`eChainMass`).

**Abel means and (12.24).**
* `tsum_pow_succ_mul_eq` (summation by parts) and `tendsto_abel_of_cesaro`: Cesàro convergence of
  a bounded sequence implies Abel convergence to the same limit.
* **Theorem 12.4.1 (i)**, (12.24) (`theorem_12_4_1_resolvent`, p. 300): `K_ε(x, ·) → Π(x, ·)`
  vaguely as `ε ↑ 1`.

**Proposition 12.4.2** (p. 302).
* `proposition_12_4_2`: `K_ε(x, C) ≥ (sup_{y ∈ C} E_y[τ_C])⁻¹` for every `x ∈ C` and every
  `ε < 1`; `proposition_12_4_2_liminf` is the book's `liminf` form. Tools: `discOcc` (the
  discounted occupation `Σ εᵐ 1_C(Φₘ)`), `discOcc_ge`, `lintegral_discOcc`, `discAt` (`ε^{τ}`,
  `𝓕_τ`-measurable), and `one_le_pow_add_mul_one_sub` (Bernoulli's inequality).

**Theorem 12.4.3** (p. 303), with `regular_eChainLimit`, `lintegral_eChainMass` (`Pu = u`),
`lowerSemicontinuous_eChainMass`, `eChainLimit_open_le` ((D.6) for open sets),
`eChainLimit_comp_measure` (`π = πΠ` for invariant probabilities `π`) and
`eChainLimit_lt_one_null` ((12.29)).
* (i) `theorem_12_4_3_i`: `max_x Π(x, X)` exists and is `0` or `1`.
* (ii) `theorem_12_4_3_ii`: if `min_x Π(x, X)` exists it is `0` or `1`.
* (iii) `theorem_12_4_3_iii`: if a compact `C` is reached from everywhere, the minimum exists and
  is attained on `C` (martingale convergence of `u(Φₖ)` and Fatou's lemma).
* (iv) `theorem_12_4_3_iv`: `inf_{x ∈ C} Π(x, X) ≥ (sup_{x ∈ C} E_x[τ_C])⁻¹`.

**Proposition 12.4.4** (`proposition_12_4_4`, p. 304) and **Theorem 12.4.5**
(`theorem_12_4_5`, p. 304): reaching a compact set with bounded mean return times, or (V2) with
an everywhere finite `V`, makes an e-chain bounded in probability on average.
`meanReturnTime_le_of_V2` is the case of Theorem 11.3.4 used there: (V2) gives
`E_x[τ_C] ≤ V(x) + b 1_C(x)`.

**Hypotheses and method.**
* Proposition 12.4.2 holds for every measurable `C` and every `ε < 1`, not only in the limit. The
  book uses Jensen's inequality `E[ε^τ] ≥ ε^{E[τ]}`; Bernoulli's inequality
  `E[ε^τ] ≥ 1 − (1 − ε) E[τ]` suffices.
* Theorem 12.4.3 (iii) assumes `C` nonempty (an empty `C` is not reached).
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported

/-- `Σ_{i=1}^{m} aᵢ = Σ_{i<m} a_{i+1}`. -/
theorem sum_Icc_one_eq_sum_range (a : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, a i = ∑ i ∈ Finset.range m, a (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- **Summation by parts for power series**: for `0 ≤ t < 1` and bounded `a`, with
`Sₙ = Σ_{i ≤ n} a_{i+1}`, `Σₙ tⁿ⁺¹ aₙ₊₁ = (1 − t) Σₙ tⁿ⁺¹ Sₙ`. -/
theorem tsum_pow_succ_mul_eq (a : ℕ → ℝ) {B : ℝ} (hB : ∀ n, |a n| ≤ B) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    ∑' n, t ^ (n + 1) * a (n + 1) =
      (1 - t) * ∑' n, t ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), a (i + 1) := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), a (i + 1)
  have hS : ∀ n, |S n| ≤ (n + 1) * B := fun n => by
    calc |S n| ≤ ∑ i ∈ Finset.range (n + 1), |a (i + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (n + 1), B := Finset.sum_le_sum fun i _ => hB _
      _ = (n + 1) * B := by simp
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have htn : ‖t‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg ht0]
  have hgeo : Summable fun n : ℕ => t ^ n := summable_geometric_of_lt_one ht0 ht1
  have hngeo : Summable fun n : ℕ => (n : ℝ) * t ^ n := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 htn
    simpa using this
  have hsumS : ∀ k, Summable fun n => t ^ (n + k) * S n := fun k => by
    refine Summable.of_norm_bounded (g := fun n => B * ((n : ℝ) * t ^ n + t ^ n))
      ((hngeo.add hgeo).mul_left B) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
    calc t ^ (n + k) * |S n| ≤ t ^ n * ((n + 1) * B) :=
          mul_le_mul (pow_le_pow_of_le_one ht0 ht1.le (by omega)) (hS n) (abs_nonneg _)
            (pow_nonneg ht0 _)
      _ = B * ((n : ℝ) * t ^ n + t ^ n) := by ring
  have hsuma : ∀ k, Summable fun n => t ^ (n + k) * a (n + k) := fun k =>
    Summable.of_norm_bounded (g := fun n => B * t ^ n) (hgeo.mul_left B) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 _), mul_comm]
      exact mul_le_mul (hB _) (pow_le_pow_of_le_one ht0 ht1.le (by omega)) (pow_nonneg ht0 _)
        hB0
  set T := ∑' n, t ^ (n + 1) * S n
  have h1 : T = t * S 0 + ∑' n, t ^ (n + 2) * S (n + 1) := by
    change ∑' n, t ^ (n + 1) * S n = _
    rw [(hsumS 1).tsum_eq_zero_add]; simp [pow_succ]
  have hS1 : ∀ n, S (n + 1) = S n + a (n + 2) := fun n => by
    simp only [S]; rw [Finset.sum_range_succ]
  have h2 : ∑' n, t ^ (n + 2) * S (n + 1) = t * T + ∑' n, t ^ (n + 2) * a (n + 2) := by
    simp_rw [hS1, mul_add]
    rw [Summable.tsum_add ?_ (hsuma 2)]
    · congr 1
      change _ = t * ∑' n, t ^ (n + 1) * S n
      rw [← tsum_mul_left]; exact tsum_congr fun n => by ring
    · exact ((hsumS 1).mul_left t).congr fun n => by ring
  have h3 : ∑' n, t ^ (n + 1) * a (n + 1) = t * a 1 + ∑' n, t ^ (n + 2) * a (n + 2) := by
    rw [(hsuma 1).tsum_eq_zero_add]; simp
  have hS0 : S 0 = a 1 := by simp [S]
  rw [h3]
  rw [h2, hS0] at h1
  linarith


/-- **Cesàro convergence implies Abel convergence** (an Abelian theorem): if the Cesàro means
`n⁻¹ Σ_{i=1}^{n} aᵢ` of a bounded sequence tend to `L`, then `(1 − t) Σₙ tⁿ aₙ → L` as `t ↑ 1`. -/
theorem tendsto_abel_of_cesaro {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => (1 - t) * ∑' n, t ^ n * a n) (𝓝[<] 1) (𝓝 L) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.range (n + 1), a (i + 1)
  have hc : Tendsto c atTop (𝓝 L) := by
    have := h.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp, c, sum_Icc_one_eq_sum_range]
    push_cast; ring_nf
  have hcB : ∀ n, |c n - L| ≤ B + |L| := fun n => by
    have : |c n| ≤ B := by
      simp only [c]
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
      calc ((n : ℝ) + 1)⁻¹ * |∑ i ∈ Finset.range (n + 1), a (i + 1)|
          ≤ ((n : ℝ) + 1)⁻¹ * ∑ _i ∈ Finset.range (n + 1), B := by
            gcongr
            exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB _)
        _ = B := by simp; field_simp
    calc |c n - L| ≤ |c n| + |L| := abs_sub _ _
      _ ≤ B + |L| := by linarith
  -- the representation for `0 ≤ t < 1`
  have hrep : ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t) * ∑' n, t ^ n * a n - L =
      (1 - t) * (a 0 - L) + (1 - t) ^ 2 * ∑' n : ℕ, ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L) := by
    intro t ht0 ht1
    have htn : ‖t‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg ht0]
    have hsa : Summable fun n => t ^ n * a n :=
      Summable.of_norm_bounded (g := fun n => B * t ^ n)
        ((summable_geometric_of_lt_one ht0 ht1).mul_left B) fun n => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hB n) (pow_nonneg ht0 _)
    have hw : HasSum (fun n : ℕ => ((n : ℝ) + 1) * t ^ (n + 1)) (t / (1 - t) ^ 2) := by
      have := hasSum_coe_mul_geometric_of_norm_lt_one htn
      rw [← hasSum_nat_add_iff' 1] at this
      simpa using this
    have hwc : Summable fun n : ℕ => ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L) :=
      Summable.of_norm_bounded (g := fun n : ℕ => (B + |L|) * (((n : ℝ) + 1) * t ^ (n + 1)))
        (hw.summable.mul_left _) fun n => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), mul_comm]
          exact mul_le_mul_of_nonneg_right (hcB n) (by positivity)
    have hsplit : ∑' n, t ^ n * a n = a 0 + ∑' n, t ^ (n + 1) * a (n + 1) := by
      rw [hsa.tsum_eq_zero_add]; simp
    have hS : ∀ n, t ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), a (i + 1) =
        ((n : ℝ) + 1) * t ^ (n + 1) * c n := fun n => by
      simp only [c]; field_simp
    rw [hsplit, tsum_pow_succ_mul_eq a hB ht0 ht1]
    simp_rw [hS]
    have e1 : ∑' n : ℕ, ((n : ℝ) + 1) * t ^ (n + 1) * c n =
        ∑' n : ℕ, ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L) + L * (t / (1 - t) ^ 2) := by
      rw [← hw.tsum_eq, ← tsum_mul_left, ← Summable.tsum_add hwc (hw.summable.mul_left L)]
      exact tsum_congr fun n => by ring
    rw [e1]
    have h1t : (1 - t) ≠ 0 := by linarith
    field_simp
    ring
  -- the estimate
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hc) (δ / 2) (by positivity))
  set K : ℝ := |a 0 - L| + (B + |L|) * ((N : ℝ) + 1) ^ 2
  have hK : 0 ≤ K := by positivity
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ t ∧ (1 - t) * K < δ / 2 := by
    have hlim : Tendsto (fun t : ℝ => (1 - t) * K) (𝓝[<] 1) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
        (continuous_id.tendsto 1).mono_left nhdsWithin_le_nhds
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const K
      simpa using this
    filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hδ)),
      Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t h1 h2
    exact ⟨h2.1.le, h1⟩
  filter_upwards [hev, self_mem_nhdsWithin] with t ⟨ht0, htK⟩ ht1
  have ht1' : t < 1 := ht1
  rw [Real.dist_eq, hrep t ht0 ht1']
  have htn : ‖t‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg ht0]
  have hw : HasSum (fun n : ℕ => ((n : ℝ) + 1) * t ^ (n + 1)) (t / (1 - t) ^ 2) := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one htn
    rw [← hasSum_nat_add_iff' 1] at this
    simpa using this
  set Kc : ℝ := B + |L|
  have hKc : 0 ≤ Kc := by positivity
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1) * t ^ (n + 1) * (δ / 2) +
    (if n < N then Kc * ((N : ℝ) + 1) else 0)
  have hgs : Summable g := (hw.summable.mul_right _).add
    (summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn; simp [Nat.not_lt.2 hn])
  have hwc : Summable fun n : ℕ => ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L) :=
    Summable.of_norm_bounded (g := fun n : ℕ => (B + |L|) * (((n : ℝ) + 1) * t ^ (n + 1)))
      (hw.summable.mul_left _) fun n => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), mul_comm]
        exact mul_le_mul_of_nonneg_right (hcB n) (by positivity)
  have hpt : ∀ n : ℕ, |((n : ℝ) + 1) * t ^ (n + 1) * (c n - L)| ≤ g n := fun n => by
    have hw0 : 0 ≤ ((n : ℝ) + 1) * t ^ (n + 1) := by positivity
    rw [abs_mul, abs_of_nonneg hw0]
    by_cases hn : n < N
    · have hw1 : ((n : ℝ) + 1) * t ^ (n + 1) ≤ (N : ℝ) + 1 := by
        have : t ^ (n + 1) ≤ 1 := pow_le_one₀ (n := n + 1) ht0 ht1'.le
        have : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn.le
        nlinarith
      simp only [g, hn, ↓reduceIte]
      have := mul_le_mul hw1 (hcB n) (abs_nonneg _) (by positivity)
      nlinarith [mul_nonneg hw0 (half_pos hδ).le]
    · have hlt := hN n (not_lt.1 hn)
      rw [Real.dist_eq] at hlt
      simp only [g, hn, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_left hlt.le hw0
  have hsum_g : ∑' n, g n = (δ / 2) * (t / (1 - t) ^ 2) + N * (Kc * ((N : ℝ) + 1)) := by
    rw [Summable.tsum_add (hw.summable.mul_right _) (summable_of_ne_finset_zero
      (s := Finset.range N) fun n hn => by
        simp only [Finset.mem_range, not_lt] at hn; simp [Nat.not_lt.2 hn]),
      tsum_mul_right, hw.tsum_eq, tsum_eq_sum (s := Finset.range N) fun n hn => by
        simp only [Finset.mem_range, not_lt] at hn; simp [Nat.not_lt.2 hn]]
    rw [Finset.sum_congr rfl fun n hn =>
      (ite_eq_left_iff.2 fun h => absurd (Finset.mem_range.1 hn) h :
      (if n < N then Kc * ((N : ℝ) + 1) else 0) = Kc * ((N : ℝ) + 1))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hbound : |∑' n : ℕ, ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L)| ≤
      (δ / 2) * (t / (1 - t) ^ 2) + N * (Kc * ((N : ℝ) + 1)) := by
    rw [← hsum_g]
    calc |∑' n : ℕ, ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L)|
        ≤ ∑' n : ℕ, |((n : ℝ) + 1) * t ^ (n + 1) * (c n - L)| := by
          have := norm_tsum_le_tsum_norm hwc.norm
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' n, g n := hwc.abs.tsum_le_tsum hpt hgs
  have h1t : 0 < 1 - t := by linarith
  have hsq : (1 - t) ^ 2 * ((δ / 2) * (t / (1 - t) ^ 2)) = (δ / 2) * t := by
    field_simp
  have hsq2 : (1 - t) ^ 2 ≤ 1 - t := by nlinarith
  calc |(1 - t) * (a 0 - L) + (1 - t) ^ 2 * ∑' n : ℕ, ((n : ℝ) + 1) * t ^ (n + 1) * (c n - L)|
      ≤ (1 - t) * |a 0 - L| + (1 - t) ^ 2 *
          ((δ / 2) * (t / (1 - t) ^ 2) + N * (Kc * ((N : ℝ) + 1))) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos h1t]
        · rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (1 - t) * |a 0 - L| + (δ / 2) * t + (1 - t) ^ 2 * (N * (Kc * ((N : ℝ) + 1))) := by
        rw [mul_add, hsq]; ring
    _ ≤ (1 - t) * K + δ / 2 := by
        have hNN : (N : ℝ) * (Kc * ((N : ℝ) + 1)) ≤ Kc * ((N : ℝ) + 1) ^ 2 := by
          have : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
          nlinarith [hKc]
        have : (1 - t) ^ 2 * (N * (Kc * ((N : ℝ) + 1))) ≤ (1 - t) * (Kc * ((N : ℝ) + 1) ^ 2) :=
          mul_le_mul hsq2 hNN (by positivity) h1t.le
        have ht1'' : (δ / 2) * t ≤ δ / 2 := by nlinarith
        simp only [K]
        nlinarith
    _ < δ := by linarith


/-- `ε ↦ ε.toReal` maps `ε ↑ 1` in `[0, ∞]` to `t ↑ 1` in `ℝ`. -/
theorem tendsto_toReal_nhdsLT_one :
    Tendsto (fun ε : ℝ≥0∞ => ε.toReal) (𝓝[<] 1) (𝓝[<] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ≥0∞)))
    rwa [ENNReal.toReal_one] at this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hε
    rwa [ENNReal.toReal_one] at this

variable {X : Type*} [MeasurableSpace X]

/-! ### Proposition 12.4.2 -/

/-- Bernoulli's inequality in `[0, ∞]`: `εⁿ + n(1 − ε) ≥ 1` for `ε ≤ 1`. -/
theorem one_le_pow_add_mul_one_sub {ε : ℝ≥0∞} (hε : ε ≤ 1) (n : ℕ) :
    1 ≤ ε ^ n + n * (1 - ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (1 : ℝ≥0∞) = ε * 1 + (1 - ε) := by rw [mul_one, add_tsub_cancel_of_le hε]
      _ ≤ ε * (ε ^ n + n * (1 - ε)) + (1 - ε) := by gcongr
      _ = ε ^ (n + 1) + ε * (n * (1 - ε)) + (1 - ε) := by rw [mul_add, ← pow_succ']
      _ ≤ ε ^ (n + 1) + n * (1 - ε) + (1 - ε) :=
          add_le_add (add_le_add le_rfl (mul_le_of_le_one_left' hε)) le_rfl
      _ = ε ^ (n + 1) + ((n + 1 : ℕ) : ℝ≥0∞) * (1 - ε) := by push_cast; ring

/-- The discounted occupation `Hε(ω) = Σₘ εᵐ 1_C(Φₘ)`. -/
noncomputable def discOcc (ε : ℝ≥0∞) (C : Set X) (ω : ℕ → X) : ℝ≥0∞ :=
  ∑' m, ε ^ m * C.indicator 1 (ω m)

/-- `Hε` is measurable. -/
theorem measurable_discOcc (ε : ℝ≥0∞) {C : Set X} (hC : MeasurableSet C) :
    Measurable (discOcc ε C) :=
  Measurable.tsum fun m => measurable_const.mul
    ((measurable_one.indicator hC).comp (measurable_pi_apply m))

/-- `E_y[Hε] = Σₘ εᵐ Pᵐ(y, C) = K_ε(y, C)/(1 − ε)`. -/
theorem lintegral_discOcc (P : Kernel X X) [IsMarkovKernel P] (ε : ℝ≥0∞) {C : Set X}
    (hC : MeasurableSet C) (y : X) :
    ∫⁻ ω, discOcc ε C ω ∂pathKernel P y = ∑' m, ε ^ m * (P ^ m) y C := by
  unfold discOcc
  rw [lintegral_tsum (f := fun m (ω : ℕ → X) => ε ^ m * C.indicator 1 (ω m)) fun m =>
    (measurable_const.mul
      ((measurable_one.indicator hC).comp (measurable_pi_apply m))).aemeasurable]
  refine tsum_congr fun m => ?_
  rw [lintegral_const_mul (f := fun ω : ℕ → X => C.indicator 1 (ω m))
      _ ((measurable_one.indicator hC).comp (measurable_pi_apply m)),
    ← pathKernel_coord_mem P y m hC]
  congr 1
  rw [← lintegral_indicator_one (s := {ω : ℕ → X | ω m ∈ C}) (measurable_pi_apply m hC)]
  rfl

omit [MeasurableSpace X] in
/-- On `{τ_C = n}`: `Hε(ω) ≥ 1_C(Φ₀) + εⁿ Hε(θⁿω)` (the visits at times `0` and `n, n + 1, …`). -/
theorem discOcc_ge (ε : ℝ≥0∞) (C : Set X) {ω : ℕ → X} {n : ℕ} (hn : 1 ≤ n) :
    C.indicator 1 (ω 0) + ε ^ n * discOcc ε C (shift n ω) ≤ discOcc ε C ω := by
  have hR : discOcc ε C ω =
      C.indicator 1 (ω 0) + ∑' m, ε ^ (m + 1) * C.indicator 1 (ω (m + 1)) := by
    unfold discOcc; rw [tsum_eq_zero_add' ENNReal.summable]; simp
  have hL : ε ^ n * discOcc ε C (shift n ω) =
      ∑' k, ε ^ (n - 1 + k + 1) * C.indicator 1 (ω (n - 1 + k + 1)) := by
    unfold discOcc
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [shift_apply]
    rw [show n - 1 + k + 1 = n + k by omega, pow_add, mul_assoc]
  have hinj : Function.Injective fun k : ℕ => n - 1 + k := fun a b h => by simpa using h
  rw [hR, hL]
  exact add_le_add le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun m => ε ^ (m + 1) * C.indicator 1 (ω (m + 1))))

/-- `K_ε(y, C) = (1 − ε) Σₘ εᵐ Pᵐ(y, C)`. -/
theorem resolvent_apply_eq_mul (P : Kernel X X) (ε : ℝ≥0∞) {C : Set X} (hC : MeasurableSet C)
    (y : X) : resolvent P ε y C = (1 - ε) * ∑' m, ε ^ m * (P ^ m) y C :=
  resolvent_apply P ε y hC

/-- The discount `ε^{τ}` as an `𝓕_τ`-measurable function: `Σₙ εⁿ 1{τ = n}`. -/
noncomputable def discAt (ε : ℝ≥0∞) (τ : (ℕ → X) → WithTop ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  ∑' n : ℕ, {ω' | τ ω' = n}.indicator (fun _ => ε ^ n) ω

omit [MeasurableSpace X] in
/-- `discAt ε τ ω = εⁿ` when `τ(ω) = n`. -/
theorem discAt_of_eq (ε : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ} {ω : ℕ → X} {n : ℕ}
    (h : τ ω = n) : discAt ε τ ω = ε ^ n := by
  rw [discAt, tsum_eq_single n fun k hk => indicator_of_notMem (by
    simp only [mem_ofPred_eq, h]; exact fun h' => hk (WithTop.coe_injective h').symm) _]
  exact indicator_of_mem (by simp [h]) _

/-- `discAt ε τ` is `𝓕_τ`-measurable. -/
theorem measurable_discAt (ε : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : Measurable[hτ.measurableSpace] (discAt ε τ) := by
  let := hτ.measurableSpace
  exact Measurable.tsum fun n => measurable_const.indicator (hτ.measurableSet_eq_of_countable' n)

/-- **Proposition 12.4.2** (MT p. 302), in the stronger form proved by the same argument: for
every measurable `C`, every `x ∈ C` and every `ε < 1`,
`K_ε(x, C) ≥ (sup_{y ∈ C} E_y[τ_C])⁻¹`. With `G(y) = Σₘ εᵐ Pᵐ(y, C)`, the strong Markov property
at `τ_C` gives `G(y) ≥ 1 + (inf_C G) E_y[ε^{τ_C}]` on `C` (12.27); Bernoulli's inequality
`εⁿ ≥ 1 − n(1 − ε)` replaces the book's use of Jensen's inequality. -/
theorem proposition_12_4_2 (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {ε : ℝ≥0∞} (hε : ε < 1) {x : X} (hx : x ∈ C) :
    (⨆ y ∈ C, meanReturnTime P C y)⁻¹ ≤ resolvent P ε x C := by
  have := isMarkovKernel_pathKernel P
  set M := ⨆ y ∈ C, meanReturnTime P C y
  by_cases hM : M = ∞
  · rw [hM, ENNReal.inv_top]; exact zero_le
  set G : X → ℝ≥0∞ := fun y => ∑' m, ε ^ m * (P ^ m) y C
  have hG1 : ∀ y ∈ C, 1 ≤ G y := fun y hy => by
    refine le_trans ?_ (ENNReal.le_tsum 0)
    rw [pow_zero, one_mul, pow_zero_apply, Measure.dirac_apply' _ hC, indicator_of_mem hy]
    rfl
  have hGfin : ∀ y, G y ≤ (1 - ε)⁻¹ := fun y => by
    rw [← ENNReal.tsum_geometric]
    refine ENNReal.tsum_le_tsum fun m => ?_
    have := isMarkovKernel_pow P m
    exact mul_le_of_le_one_right' prob_le_one
  set g := ⨅ y ∈ C, G y
  have hg1 : 1 ≤ g := le_iInf₂ hG1
  have hgx : g ≤ G x := iInf₂_le x hx
  have hgfin : g ≠ ∞ := ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hε).ne')
    (hgx.trans (hGfin x))
  set τ := firstReturn C
  have hτ : IsStoppingTime (natFilt (X := X)) τ := (proposition_3_4_4 hC).1
  set S := {ω : ℕ → X | τ ω ≠ ⊤}
  have hS : MeasurableSet S := measurableSet_firstReturn_ne_top hC
  -- the renewal inequality on `C`
  have hkey : ∀ y ∈ C, 1 + g * (1 - (1 - ε) * M) ≤ G y := by
    intro y hy
    have hEy : meanReturnTime P C y ≤ M := le_iSup₂ (f := fun y _ => meanReturnTime P C y) y hy
    have hSy : pathKernel P y S = 1 :=
      hitProb_eq_one_of_meanReturnTime_ne_top hC (ne_top_of_le_ne_top hM hEy)
    have hSc : pathKernel P y Sᶜ = 0 := by rw [prob_compl_eq_one_sub hS, hSy, tsub_self]
    have h0 : ∀ᵐ ω ∂pathKernel P y, C.indicator (1 : X → ℝ≥0∞) (ω 0) = 1 := by
      have hm0 : MeasurableSet {ω : ℕ → X | ω 0 ∈ C} := measurable_pi_apply 0 hC
      have : pathKernel P y {ω : ℕ → X | ω 0 ∈ C}ᶜ = 0 := by
        rw [prob_compl_eq_one_sub hm0, pathKernel_zero_mem P y hC,
          indicator_of_mem hy, Pi.one_apply, tsub_self]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with ω hω
      simp only [mem_compl_iff, not_not, mem_ofPred_eq] at hω
      rw [indicator_of_mem hω, Pi.one_apply]
    set e := ∫⁻ ω in S, discAt ε τ ω ∂pathKernel P y
    -- (12.27)
    have hrenew : 1 + g * e ≤ G y := by
      have hSM := strong_markov_lintegral_mul P (Measure.dirac y) hτ (measurable_discAt ε hτ)
        (measurable_discOcc ε hC)
      rw [pathMeasure_dirac] at hSM
      calc 1 + g * e = ∫⁻ ω in S, 1 ∂pathKernel P y +
            ∫⁻ ω in S, discAt ε τ ω * g ∂pathKernel P y := by
            rw [setLIntegral_const, one_mul, hSy, lintegral_mul_const' _ _ (by exact hgfin),
              mul_comm]
        _ ≤ ∫⁻ ω in S, C.indicator 1 (ω 0) ∂pathKernel P y + ∫⁻ ω in S, discAt ε τ ω *
              ∫⁻ ω', discOcc ε C ω' ∂pathKernel P (stoppedState τ ω) ∂pathKernel P y := by
            refine add_le_add (setLIntegral_congr_fun_ae hS (h0.mono fun ω h _ => h.symm)).le
              (setLIntegral_mono (((measurable_discAt ε hτ).mono hτ.measurableSpace_le le_rfl).mul
                ((measurable_discOcc ε hC).lintegral_kernel.comp (measurable_stoppedState hτ)))
                fun ω hω => mul_le_mul_of_nonneg_left ?_ zero_le)
            rw [lintegral_discOcc P ε hC]
            exact iInf₂_le _ (stoppedState_firstReturn_mem C hω)
        _ = ∫⁻ ω in S, (C.indicator 1 (ω 0) + discAt ε τ ω * discOcc ε C (shiftAt τ ω))
              ∂pathKernel P y := by
            rw [← hSM, lintegral_add_left (f := fun ω : ℕ → X => C.indicator 1 (ω 0))
              ((measurable_one.indicator hC).comp (measurable_pi_apply 0))]
        _ ≤ ∫⁻ ω in S, discOcc ε C ω ∂pathKernel P y := by
            refine setLIntegral_mono (measurable_discOcc ε hC) fun ω hω => ?_
            obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hω
            rw [discAt_of_eq ε hn.symm, shiftAt_of_eq hn.symm]
            have h1 := one_le_firstReturn C ω
            change _ ≤ τ ω at h1
            rw [← hn] at h1
            exact discOcc_ge ε C (WithTop.coe_le_coe.1 h1)
        _ ≤ ∫⁻ ω, discOcc ε C ω ∂pathKernel P y := setLIntegral_le_lintegral _ _
        _ = G y := lintegral_discOcc P ε hC y
    have hbern : 1 ≤ e + (1 - ε) * meanReturnTime P C y := by
      calc (1 : ℝ≥0∞) = ∫⁻ _ in S, 1 ∂pathKernel P y := by rw [setLIntegral_const, one_mul, hSy]
        _ ≤ ∫⁻ ω in S, (discAt ε τ ω + (1 - ε) * ENat.toENNReal (τ ω)) ∂pathKernel P y := by
            refine setLIntegral_mono' hS fun ω hω => ?_
            obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hω
            rw [discAt_of_eq ε hn.symm, ← hn]
            change 1 ≤ ε ^ n + (1 - ε) * ENat.toENNReal ((n : ℕ) : ℕ∞)
            rw [ENat.toENNReal_coe, mul_comm]
            exact one_le_pow_add_mul_one_sub hε.le n
        _ = e + (1 - ε) * ∫⁻ ω in S, ENat.toENNReal (τ ω) ∂pathKernel P y := by
            rw [lintegral_add_left ((measurable_discAt ε hτ).mono hτ.measurableSpace_le le_rfl),
              lintegral_const_mul' _ _ (by finiteness)]
        _ ≤ e + (1 - ε) * meanReturnTime P C y := by
            gcongr
            exact setLIntegral_le_lintegral _ _
    calc 1 + g * (1 - (1 - ε) * M) ≤ 1 + g * e := by
          gcongr
          rw [tsub_le_iff_right]
          exact hbern.trans (by gcongr)
      _ ≤ G y := hrenew
  -- solving `g ≥ 1 + g (1 − b)`
  set b := (1 - ε) * M
  have hg : 1 + g * (1 - b) ≤ g := le_iInf₂ fun y hy => hkey y hy
  have hgb : 1 ≤ g * b := by
    by_cases hb : 1 ≤ b
    · calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ g * b := mul_le_mul' hg1 hb
    · push Not at hb
      have hsplit : g = g * (1 - b) + g * b := by
        rw [← mul_add, tsub_add_cancel_of_le hb.le, mul_one]
      have hfin : g * (1 - b) ≠ ∞ := ENNReal.mul_ne_top hgfin (by finiteness)
      have h2 : 1 + g * (1 - b) ≤ g * b + g * (1 - b) := by
        calc 1 + g * (1 - b) ≤ g := hg
          _ = g * (1 - b) + g * b := hsplit
          _ = g * b + g * (1 - b) := add_comm _ _
      exact (ENNReal.add_le_add_iff_right hfin).1 h2
  have hbfin : (1 - ε) * g ≠ ∞ := ENNReal.mul_ne_top (by finiteness) hgfin
  calc M⁻¹ ≤ (1 - ε) * g := by
        rw [ENNReal.inv_le_iff_le_mul (fun h => absurd h hbfin) (fun h => absurd h hM)]
        calc (1 : ℝ≥0∞) ≤ g * b := hgb
          _ = M * ((1 - ε) * g) := by simp only [b]; ring
    _ ≤ (1 - ε) * G x := by gcongr
    _ = resolvent P ε x C := (resolvent_apply_eq_mul P ε hC x).symm

/-- **Proposition 12.4.2** in the book's form (MT p. 302):
`liminf_{ε↑1} K_ε(x, C) ≥ (sup_{y ∈ C} E_y[τ_C])⁻¹` for `x ∈ C`. -/
theorem proposition_12_4_2_liminf (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {x : X} (hx : x ∈ C) :
    (⨆ y ∈ C, meanReturnTime P C y)⁻¹ ≤ (𝓝[<] (1 : ℝ≥0∞)).liminf fun ε => resolvent P ε x C :=
  le_liminf_of_le (by isBoundedDefault)
    (eventually_nhdsWithin_of_forall fun _ hε => proposition_12_4_2 P hC hε hx)

variable [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]

/-- **Theorem 12.4.1 (i)**, (12.24) (MT p. 300): for an e-chain, `K_ε(x, ·) → Π(x, ·)` vaguely as
`ε ↑ 1`. The Abel means of `Pⁿ f(x)` have the same limit as its Cesàro means
(`tendsto_abel_of_cesaro`). -/
theorem theorem_12_4_1_resolvent {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (f : C_c(X, ℝ)) (x : X) :
    Tendsto (fun ε : ℝ≥0∞ => ∫ y, f y ∂resolvent P ε x) (𝓝[<] 1)
      (𝓝 (∫ y, f y ∂eChainLimit he x)) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  set a : ℕ → ℝ := fun n => ∫ y, f y ∂(P ^ n) x
  have ha : ∀ n, |a n| ≤ B := fun n => by
    have := isMarkovKernel_pow P n
    exact abs_integral_le_of_univ_le (by simp) hB0 hB
  have hces : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i) atTop
      (𝓝 (∫ y, f y ∂eChainLimit he x)) := by
    refine ((theorem_12_4_1_i he).2 f x).congr fun n => ?_
    exact integral_cesaroKernel P n x (map_continuous f).measurable hB
  have habel := (tendsto_abel_of_cesaro ha hces).comp tendsto_toReal_nhdsLT_one
  refine habel.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp]
  rw [integral_resolvent P hε x (map_continuous f).measurable hB, ← tsum_mul_left]
  exact tsum_congr fun n => by ring


/-- `Π(x, ·)` is a regular measure (it is a Riesz–Markov–Kakutani measure). -/
theorem regular_eChainLimit {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (x : X) :
    (eChainLimit he x).Regular := by
  change (RealRMK.rieszMeasure _).Regular
  infer_instance

/-- `u(x) = Π(x, X)`. -/
noncomputable abbrev eChainMass {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (x : X) :
    ℝ≥0∞ :=
  eChainLimit he x univ

/-- `u ≤ 1`. -/
theorem eChainMass_le_one {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (x : X) :
    eChainMass he x ≤ 1 :=
  (theorem_12_4_1_i he).1 x

/-- `u` is measurable. -/
theorem measurable_eChainMass {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    Measurable (eChainMass he) :=
  Kernel.measurable_coe _ MeasurableSet.univ

/-- `Pu = u` (MT p. 303). -/
theorem lintegral_eChainMass {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (x : X) :
    ∫⁻ y, eChainMass he y ∂P x = eChainMass he x := by
  have h : (eChainLimit he ∘ₖ P) x univ = eChainLimit he x univ := by
    rw [eChainLimit_comp_kernel he]
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ] at h
  exact h

/-- `Pᵏu = u`. -/
theorem lintegral_pow_eChainMass {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (k : ℕ)
    (x : X) : ∫⁻ y, eChainMass he y ∂(P ^ k) x = eChainMass he x := by
  induction k generalizing x with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ (measurable_eChainMass he)]
  | succ k ih =>
    rw [Kernel.pow_add, pow_one, Kernel.lintegral_comp _ _ _ (measurable_eChainMass he)]
    simp_rw [ih]
    exact lintegral_eChainMass he x


/-- `u = Π(·, X)` is lower semicontinuous (MT p. 303): it is the supremum of the continuous
functions `Π φₘ`. -/
theorem lowerSemicontinuous_eChainMass {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    LowerSemicontinuous (eChainMass he) := by
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  have hfin := isFiniteKernel_eChainLimit he
  have heq : eChainMass he = fun x => ⨆ m, ENNReal.ofReal (∫ y, φ m y ∂eChainLimit he x) := by
    ext x
    have ht : Tendsto (fun m => ∫ y, φ m y ∂eChainLimit he x) atTop
        (𝓝 ((eChainLimit he x).real univ)) := by
      have := integral_cutoff_tendsto (μ := eChainLimit he x) hφ01 hφ1
        (BoundedContinuousFunction.const X 1)
      simpa using this
    have ht' := (ENNReal.tendsto_ofReal ht)
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at ht'
    refine le_antisymm (le_of_tendsto' ht' fun m => le_iSup (fun m =>
      ENNReal.ofReal (∫ y, φ m y ∂eChainLimit he x)) m) (iSup_le fun m => ?_)
    exact ofReal_integral_le_univ (φ m).continuous.measurable (hφ01 m)
  rw [heq]
  exact lowerSemicontinuous_iSup fun m => (ENNReal.continuous_ofReal.comp
    (continuous_integral_limMeasure he (cesaroConverges_eChainSubseq he) (φ m))).lowerSemicontinuous

/-- **(D.6) for open sets**: `Π(x, O) ≤ liminf_n P̄ⁿ(x, O)` for open `O`, by inner regularity of
`Π(x, ·)` and Urysohn functions. -/
theorem eChainLimit_open_le {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {O : Set X}
    (hO : IsOpen O) (x : X) :
    eChainLimit he x O ≤ atTop.liminf fun n => cesaroKernel P n x O := by
  have := regular_eChainLimit he x
  have hfin := isFiniteKernel_eChainLimit he
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  obtain ⟨K, hKO, hK, hrK⟩ := hO.exists_lt_isCompact hr
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK hO.isClosed_compl
      (disjoint_compl_right_iff_subset.2 hKO)
  set fc : C_c(X, ℝ) := ⟨f, hfc⟩
  have hlim := (theorem_12_4_1_i he).2 fc x
  have hKf : eChainLimit he x K ≤ ENNReal.ofReal (∫ y, fc y ∂eChainLimit he x) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ K), ← measureReal_def]
    exact ENNReal.ofReal_le_ofReal (measureReal_le_integral_of_indicator_le hK.measurableSet
      fc.integrable fun y => by
        by_cases hy : y ∈ K
        · rw [indicator_of_mem hy, Pi.one_apply]; exact (hf1 hy).ge
        · rw [indicator_of_notMem hy]; exact (hf01 y).1)
  refine hrK.le.trans (hKf.trans ?_)
  have ht := ENNReal.tendsto_ofReal hlim
  have hab : ∀ n, ENNReal.ofReal (cesaroFun P n fc x) ≤ cesaroKernel P n x O := fun n => by
    have := isFiniteKernel_cesaroKernel P n
    rw [← ENNReal.ofReal_toReal (measure_ne_top (cesaroKernel P n x) O), ← measureReal_def]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_indicator_one hO.measurableSet]
    refine integral_mono fc.integrable ((integrable_const 1).indicator hO.measurableSet)
      fun y => ?_
    by_cases hy : y ∈ O
    · rw [indicator_of_mem hy, Pi.one_apply]; exact (hf01 y).2
    · rw [indicator_of_notMem hy]; exact (hf0 hy).le
  calc ENNReal.ofReal (∫ y, fc y ∂eChainLimit he x)
      = atTop.liminf fun n => ENNReal.ofReal (cesaroFun P n fc x) := ht.liminf_eq.symm
    _ ≤ atTop.liminf fun n => cesaroKernel P n x O := liminf_le_liminf (Eventually.of_forall hab)


omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `∫ f d(μK) = ∫∫ f dK(x) μ(dx)` for a finite kernel `K` and integrable `f`. -/
theorem integral_comp_measure_finite (K : Kernel X X) [IsFiniteKernel K] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f (K ∘ₘ μ)) :
    ∫ y, f y ∂(K ∘ₘ μ) = ∫ x, ∫ y, f y ∂K x ∂μ := by
  have h : K ∘ₘ μ = (K ∘ₖ Kernel.const Unit μ) () := by
    rw [Kernel.comp_apply, Kernel.const_apply]
  rw [h] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- **Every invariant probability is `Π`-invariant** (MT p. 303, `π = πΠ`), by dominated
convergence: `π(f) = πP̄ⁿ(f) → πΠ(f)`. -/
theorem eChainLimit_comp_measure {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    eChainLimit he ∘ₘ π = π := by
  have hfin := isFiniteKernel_eChainLimit he
  have : IsFiniteMeasure (eChainLimit he ∘ₘ π) := inferInstance
  refine ext_of_integral_cc fun f => ?_
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  rw [integral_comp_measure_finite _ _ f.integrable]
  have hlim : Tendsto (fun n => ∫ y, cesaroFun P n f y ∂π) atTop
      (𝓝 (∫ y, (∫ z, f z ∂eChainLimit he y) ∂π)) :=
    tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (measurable_cesaroFun P n (map_continuous f).measurable).aestronglyMeasurable)
      (integrable_const B)
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_cesaroFun_le P n hB0 hB y)
      (Eventually.of_forall fun y => (theorem_12_4_1_i he).2 f y)
  refine tendsto_nhds_unique hlim (tendsto_nhds_of_eventually_eq ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hM := isMarkovKernel_cesaroKernel P hn
  have hK := hπ.sampledKernel (isSamplingDist_uniformDist hn)
  unfold IsInvariant at hK
  simp only [cesaroFun]
  rw [← integral_comp_measure _ _ f.integrable]
  exact congrArg (fun m : Measure X => ∫ z, f z ∂m) hK

/-- `Π(x, {u < 1}) = 0` (12.29): `Π(x, ·)/Π(x, X)` is an invariant probability, under which
`u = 1` almost everywhere. -/
theorem eChainLimit_lt_one_null {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) (x : X) :
    eChainLimit he x {y | eChainMass he y < 1} = 0 := by
  have hfin := isFiniteKernel_eChainLimit he
  by_cases hx0 : eChainMass he x = 0
  · exact measure_mono_null (subset_univ _) hx0
  have hxt : eChainMass he x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (eChainMass_le_one he x)
  set π := (eChainMass he x)⁻¹ • eChainLimit he x
  have hπ : IsProbabilityMeasure π := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.inv_mul_cancel hx0 hxt⟩
  have hinv : IsInvariant P π := (isInvariant_eChainLimit he x).smul _
  have h1 : ∫⁻ y, eChainMass he y ∂π = 1 := by
    have h0 : (eChainLimit he ∘ₘ π) univ = π univ := by rw [eChainLimit_comp_measure he hinv]
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _), measure_univ] at h0
    exact h0
  have h2 : ∫⁻ y, (1 - eChainMass he y) ∂π = 0 := by
    rw [lintegral_sub (measurable_eChainMass he) (by rw [h1]; exact ENNReal.one_ne_top)
      (Eventually.of_forall fun y => eChainMass_le_one he y), lintegral_one, measure_univ, h1,
      tsub_self]
  have h3 := (lintegral_eq_zero_iff (measurable_const.sub (measurable_eChainMass he))).1 h2
  have hnull : π {y | eChainMass he y < 1} = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [h3] with y hy
    simp only [Pi.sub_apply, Pi.zero_apply, tsub_eq_zero_iff_le] at hy
    simp only [not_lt]
    exact hy
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hnull
  exact hnull.resolve_left (ENNReal.inv_ne_zero.2 hxt)


/-! ### Theorem 12.4.3 -/

/-- **Theorem 12.4.3 (i)** (MT p. 303): `max_x Π(x, X)` exists and is `0` or `1`. If some
`Π(x, X) > 0`, `Π(x, ·)/Π(x, X)` is an invariant probability under which `Π(·, X) = 1` almost
everywhere, so the value `1` is attained. -/
theorem theorem_12_4_3_i [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    ∃ x₀, (∀ x, eChainMass he x ≤ eChainMass he x₀) ∧
      (eChainMass he x₀ = 0 ∨ eChainMass he x₀ = 1) := by
  by_cases h : ∃ x, eChainMass he x ≠ 0
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ : ∃ y, eChainMass he y = 1 := by
      by_contra hne
      push Not at hne
      have hall : {y | eChainMass he y < 1} = univ :=
        eq_univ_of_forall fun y => lt_of_le_of_ne (eChainMass_le_one he y) (hne y)
      have := eChainLimit_lt_one_null he x
      rw [hall] at this
      exact hx this
    exact ⟨y, fun z => (eChainMass_le_one he z).trans hy.ge, Or.inr hy⟩
  · push Not at h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact ⟨x₀, fun x => (h x).le.trans (h x₀).ge, Or.inl (h x₀)⟩

/-- **Theorem 12.4.3 (ii)** (MT p. 303): if `min_x Π(x, X)` exists, it is `0` or `1`. The set
`S_ρ = {Π(·, X) = ρ}` is closed (lower semicontinuity) and absorbing (`Pu = u`), so
`Π(x, S_ρᶜ) = 0` on `S_ρ` by (D.6), while `Π(x, {u < 1}) = 0` (12.29). -/
theorem theorem_12_4_3_ii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {x₀ : X}
    (hmin : ∀ x, eChainMass he x₀ ≤ eChainMass he x) :
    eChainMass he x₀ = 0 ∨ eChainMass he x₀ = 1 := by
  set ρ := eChainMass he x₀
  by_cases hρ1 : ρ = 1
  · exact Or.inr hρ1
  left
  have hρ : ρ < 1 := lt_of_le_of_ne (eChainMass_le_one he x₀) hρ1
  set S := {x | eChainMass he x ≤ ρ}
  have hSc : IsClosed S := (lowerSemicontinuous_eChainMass he).isClosed_preimage ρ
  have hSm : MeasurableSet S := hSc.measurableSet
  -- `S` is absorbing
  have habs : ∀ x ∈ S, P x Sᶜ = 0 := by
    intro x hx
    have hxρ : eChainMass he x = ρ := le_antisymm hx (hmin x)
    have hint : ∫⁻ y, (eChainMass he y - ρ) ∂P x = 0 := by
      rw [lintegral_sub (measurable_const) (by
          rw [lintegral_const, measure_univ, mul_one]; exact ne_top_of_lt hρ)
          (Eventually.of_forall fun y => hmin y),
        lintegral_eChainMass he x, hxρ, lintegral_const, measure_univ, mul_one, tsub_self]
    have hae := (lintegral_eq_zero_iff ((measurable_eChainMass he).sub measurable_const)).1 hint
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hae] with y hy
    simp only [Pi.sub_apply, Pi.zero_apply, tsub_eq_zero_iff_le] at hy
    simp only [mem_compl_iff, not_not]
    exact hy
  have hpow : ∀ n, ∀ x ∈ S, (P ^ n) x Sᶜ = 0 := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero_apply, Measure.dirac_apply' _ hSm.compl, indicator_of_notMem (by simpa)]
    | succ n ih =>
      intro x hx
      rw [pow_succ_apply P n x hSm.compl]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      have : ∀ᵐ y ∂P x, y ∈ S := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (habs x hx)] with y hy
        simpa using hy
      filter_upwards [this] with y hy
      exact ih y hy
  have hces : ∀ n, cesaroKernel P n x₀ Sᶜ = 0 := fun n => by
    rw [cesaroKernel_apply P n x₀ hSm.compl,
      Finset.sum_eq_zero fun i _ => hpow i x₀ (show ρ ≤ ρ from le_rfl), mul_zero]
  have h1 : eChainLimit he x₀ Sᶜ = 0 := by
    refine le_antisymm ((eChainLimit_open_le he hSc.isOpen_compl x₀).trans ?_) zero_le
    simp [hces]
  have h2 : eChainLimit he x₀ S = 0 :=
    measure_mono_null (fun y hy => lt_of_le_of_lt hy hρ) (eChainLimit_lt_one_null he x₀)
  calc ρ = eChainLimit he x₀ S + eChainLimit he x₀ Sᶜ := (measure_add_measure_compl hSm).symm
    _ = 0 := by rw [h1, h2, add_zero]


/-- **Theorem 12.4.3 (iii)** (MT p. 303): if a compact nonempty `C` is reached from every state,
`P_x(τ_C < ∞) ≡ 1`, then `min_x Π(x, X)` exists and is attained on `C`. The bounded martingale
`Π(Φₖ, X)` converges, `Φ` visits `C` infinitely often, so the limit is at least `min_C Π(·, X)`,
and Fatou's lemma gives `Π(y, X) ≥ min_C Π(·, X)`. -/
theorem theorem_12_4_3_iii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {C : Set X}
    (hC : IsCompact C) (hCne : C.Nonempty) (hL : ∀ x, hitProb P C x = 1) :
    ∃ x₀ ∈ C, ∀ x, eChainMass he x₀ ≤ eChainMass he x := by
  have := isMarkovKernel_pathKernel P
  have hCm := hC.measurableSet
  obtain ⟨x₀, hx₀C, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hCne hC
    ((lowerSemicontinuous_eChainMass he).lowerSemicontinuousOn C)
  rw [isMinOn_iff] at hmin
  refine ⟨x₀, hx₀C, fun y => ?_⟩
  set m := eChainMass he x₀
  set u := eChainMass he
  have hu1 : ∀ z, u z ≠ ∞ := fun z =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (eChainMass_le_one he z)
  -- infinitely many visits to `C`
  have hQ : harrisQ P C y = 1 := by
    rw [(proposition_9_1_1 P hCm fun x _ => hL x).1 y, hL y]
  have hio : ∀ᵐ ω ∂pathKernel P y, ω ∈ ioSet C := by
    refine ae_iff.2 ?_
    have h := prob_compl_eq_one_sub (μ := pathKernel P y) (measurableSet_ioSet hCm)
    rw [show harrisQ P C y = pathKernel P y (ioSet C) from rfl] at hQ
    rw [hQ, tsub_self] at h
    simpa [compl_def] using h
  -- the martingale `u(Φₖ)` converges
  set uN : X → ℝ≥0 := fun z => (u z).toNNReal
  have huN : ∀ z, (uN z : ℝ≥0∞) = u z := fun z => ENNReal.coe_toNNReal (hu1 z)
  have huNm : Measurable uN := (measurable_eChainMass he).ennreal_toNNReal
  have hconv := ae_tendsto_killedV P (Measure.dirac y) huNm MeasurableSet.empty
    (fun z _ => by simp_rw [huN]; exact (lintegral_eChainMass he z).le)
    (by rw [lintegral_dirac' _ huNm.coe_nnreal_ennreal]; exact ENNReal.coe_ne_top)
  rw [pathMeasure_dirac] at hconv
  -- the limit is at least `m`
  have hlim : ∀ᵐ ω ∂pathKernel P y, m ≤ atTop.liminf fun k => u (ω k) := by
    filter_upwards [hio, hconv] with ω hωC ⟨c, hc⟩
    have hk : ∀ k, killedV uN ∅ k ω = (uN (ω k) : ℝ) := fun k => by
      simp [killedV, avoidSet]
    simp_rw [hk] at hc
    have hcm : m.toReal ≤ c := by
      by_contra hlt
      push Not at hlt
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hc.eventually (gt_mem_nhds hlt))
      obtain ⟨k, hkN, hkC⟩ := hωC N
      have h1 := hN k hkN
      have h2 : m ≤ u (ω k) := hmin _ hkC
      have h3 : m.toReal ≤ (uN (ω k) : ℝ) := by
        rw [ENNReal.coe_toNNReal_eq_toReal]
        exact ENNReal.toReal_mono (hu1 _) h2
      linarith
    have hcl : Tendsto (fun k => u (ω k)) atTop (𝓝 (ENNReal.ofReal c)) := by
      have := ENNReal.tendsto_ofReal hc
      refine this.congr fun k => ?_
      rw [ENNReal.ofReal_coe_nnreal, huN]
    rw [hcl.liminf_eq]
    calc m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal (hu1 x₀)).symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hcm
  -- Fatou
  have hk : ∀ k, ∫⁻ ω, u (ω k) ∂pathKernel P y = u y := fun k => by
    rw [← lintegral_map (measurable_eChainMass he) (measurable_pi_apply k),
      pathKernel_map_coord, lintegral_pow_eChainMass he k y]
  calc m = ∫⁻ _, m ∂pathKernel P y := by rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ ω, atTop.liminf (fun k => u (ω k)) ∂pathKernel P y := lintegral_mono_ae hlim
    _ ≤ atTop.liminf fun k => ∫⁻ ω, u (ω k) ∂pathKernel P y :=
        lintegral_liminf_le fun k => (measurable_eChainMass he).comp (measurable_pi_apply k)
    _ = u y := by simp_rw [hk]; exact liminf_const (u y)


/-- **Theorem 12.4.3 (iv)** (MT p. 303): for compact `C`,
`inf_{x ∈ C} Π(x, X) ≥ (sup_{x ∈ C} E_x[τ_C])⁻¹`, from Proposition 12.4.2 and (12.24). -/
theorem theorem_12_4_3_iv {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {C : Set X}
    (hC : IsCompact C) :
    (⨆ y ∈ C, meanReturnTime P C y)⁻¹ ≤ ⨅ x ∈ C, eChainMass he x := by
  have hfin := isFiniteKernel_eChainLimit he
  refine le_iInf₂ fun x hx => ?_
  set M := ⨆ y ∈ C, meanReturnTime P C y
  have hM1 : 1 ≤ M := (one_le_meanReturnTime hC.measurableSet x).trans
    (le_iSup₂ (f := fun y _ => meanReturnTime P C y) x hx)
  have hMinv : M⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (ne_of_gt (lt_of_lt_of_le one_pos hM1))
  obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hC
  have hlim := theorem_12_4_1_resolvent he f x
  have hNe : (𝓝[<] (1 : ℝ≥0∞)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  have hle : M⁻¹.toReal ≤ ∫ y, f y ∂eChainLimit he x := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have := isFiniteMeasure_of_univ_le (resolvent_univ_le P ε x)
    calc M⁻¹.toReal ≤ (resolvent P ε x).real C := by
          rw [measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top _ _)
            (proposition_12_4_2 P hC.measurableSet hε hx)
      _ ≤ ∫ y, f y ∂resolvent P ε x :=
          measureReal_le_integral_of_indicator_le hC.measurableSet f.integrable hfC
  calc M⁻¹ = ENNReal.ofReal M⁻¹.toReal := (ENNReal.ofReal_toReal hMinv).symm
    _ ≤ ENNReal.ofReal (∫ y, f y ∂eChainLimit he x) := ENNReal.ofReal_le_ofReal hle
    _ ≤ eChainMass he x := ofReal_integral_le_univ (map_continuous f).measurable hf01

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `C` is nonempty if it is reached from some state. -/
theorem nonempty_of_hitProb {P : Kernel X X} [IsMarkovKernel P]
    {C : Set X} {x : X} (h : hitProb P C x = 1) : C.Nonempty := by
  by_contra hC
  rw [not_nonempty_iff_eq_empty] at hC
  have : {ω : ℕ → X | firstReturn C ω ≠ ⊤} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, firstReturn_ne_top_iff, hC, mem_empty_iff_false, and_false,
      exists_false]
  rw [hitProb, this, measure_empty] at h
  exact zero_ne_one h

/-- **Proposition 12.4.4** (MT p. 304): an e-chain that reaches a compact `C` from every state,
with `sup_{x ∈ C} E_x[τ_C] < ∞`, is bounded in probability on average. -/
theorem proposition_12_4_4 {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {C : Set X}
    (hC : IsCompact C) (hL : ∀ x, hitProb P C x = 1)
    (hM : (⨆ y ∈ C, meanReturnTime P C y) ≠ ∞) : IsBoundedInProbabilityOnAverage P := by
  rw [theorem_12_4_1_iii he]
  intro x
  obtain ⟨x₀, hx₀C, hmin⟩ := theorem_12_4_3_iii he hC (nonempty_of_hitProb (hL x)) hL
  have hpos : 0 < eChainMass he x₀ := lt_of_lt_of_le (ENNReal.inv_pos.2 hM)
    ((theorem_12_4_3_iv he hC).trans (iInf₂_le x₀ hx₀C))
  have h1 : eChainMass he x₀ = 1 := (theorem_12_4_3_ii he hmin).resolve_left hpos.ne'
  exact le_antisymm (eChainMass_le_one he x) (h1 ▸ hmin x)


omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Mean return times under (V2)** (the case of Theorem 11.3.4 used on p. 305): if
`∫ V dP(x) + 1 ≤ V(x) + b 1_C(x)`, then `E_x[τ_C] ≤ V(x) + b 1_C(x)` for every `x`. Here
`E_x[τ_C] = U_C(x, X) = Σₖ (P I_{Cᶜ})ᵏ 1 (x)`, and `G = V + b 1_C` satisfies
`1 + P I_{Cᶜ} G ≤ G`, so the minimality of the series applies. -/
theorem meanReturnTime_le_of_V2 (P : Kernel X X) [IsMarkovKernel P] {V : X → ℝ≥0∞}
    {C : Set X} (hC : MeasurableSet C) {b : ℝ≥0∞}
    (hV2 : ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + b * C.indicator 1 x) (x : X) :
    meanReturnTime P C x ≤ V x + b * C.indicator 1 x := by
  have hh : Measurable (C.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hC
  rw [meanReturnTime_eq_tabooPotKernel P hC x, ← genPotKernel_indicator P hC, ← lintegral_one,
    lintegral_genPotKernel P hh x (f := fun _ => 1) measurable_const]
  change geomOp P (1 - C.indicator 1) (kfun P 1) x ≤ _
  rw [kfun_one]
  refine geomOp_le (P := P) (w := 1 - C.indicator 1)
    (G := fun y => V y + b * C.indicator 1 y) (measurable_one.sub hh) measurable_one
    (fun y => ?_) x
  simp only [Pi.add_apply, Pi.one_apply]
  calc 1 + killOp P (1 - C.indicator 1) (fun z => V z + b * C.indicator 1 z) y
      ≤ 1 + ∫⁻ z, V z ∂P y := by
        gcongr
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ C
        · simp [hz]
        · simp [hz]
    _ ≤ V y + b * C.indicator 1 y := by rw [add_comm]; exact hV2 y

/-- **Theorem 12.4.5** (MT p. 304): an e-chain satisfying (V2) for a compact `C` and an
everywhere finite `V` is bounded in probability on average. `E_x[τ_C] < ∞` gives `L(·, C) ≡ 1`,
(12.21) gives `Π(x, X) ≥ 1/(2b) > 0` for every `x`, and Theorem 12.4.3 (iii), (ii) force
`Π(·, X) ≡ 1`. -/
theorem theorem_12_4_5 {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) {V : X → ℝ≥0∞}
    (hVm : Measurable V) (hVfin : ∀ x, V x ≠ ∞) {C : Set X} (hC : IsCompact C) {b : ℝ≥0}
    (hV2 : ∀ x, ∫⁻ y, V y ∂P x + 1 ≤ V x + b * C.indicator 1 x) :
    IsBoundedInProbabilityOnAverage P := by
  have hCm := hC.measurableSet
  rw [theorem_12_4_1_iii he]
  intro x
  have hb := V2_coe_ne_zero hVm hCm hV2 (hVfin x)
  have hL : ∀ y, hitProb P C y = 1 := fun y =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨hVfin y, ENNReal.mul_ne_top ENNReal.coe_ne_top
        (by by_cases hy : y ∈ C <;> simp [hy])⟩) (meanReturnTime_le_of_V2 P hCm hV2 y))
  obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hC
  have hfin := isFiniteKernel_eChainLimit he
  have hpos : ∀ y, 0 < eChainMass he y := fun y => by
    set δ : ℝ≥0∞ := (2 * (b : ℝ≥0∞))⁻¹
    have hδ : δ ≠ ∞ := ENNReal.inv_ne_top.2 (by simpa using hb)
    have hδ0 : 0 < δ.toReal :=
      ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 (ENNReal.mul_ne_top (by simp) (by simp))) hδ
    have hle : δ.toReal ≤ ∫ z, f z ∂eChainLimit he y := by
      refine ge_of_tendsto ((theorem_12_4_1_i he).2 f y) ?_
      filter_upwards [eventually_le_cesaroKernel_of_V2 hVm hCm hb hV2 (hVfin y)] with n hn
      have := isFiniteKernel_cesaroKernel P n
      calc δ.toReal ≤ (cesaroKernel P n y).real C := by
            rw [measureReal_def]; exact ENNReal.toReal_mono (measure_ne_top _ _) hn
        _ ≤ cesaroFun P n f y :=
            measureReal_le_integral_of_indicator_le hCm f.integrable hfC
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (hδ0.trans_le hle))
      (ofReal_integral_le_univ (map_continuous f).measurable hf01)
  obtain ⟨x₀, -, hmin⟩ := theorem_12_4_3_iii he hC (nonempty_of_hitProb (hL x)) hL
  have h1 : eChainMass he x₀ = 1 := (theorem_12_4_3_ii he hmin).resolve_left (hpos x₀).ne'
  exact le_antisymm (eChainMass_le_one he x) (h1 ▸ hmin x)

end MeynTweedie.Positivity
