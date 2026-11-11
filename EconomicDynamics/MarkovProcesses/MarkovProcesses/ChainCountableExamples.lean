/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainCountableStationary
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countable-state Markov chains: Examples 3.1.4–3.1.5 and counterexamples

Miao, §3.1, pp. 88–89, and §3.1.3, pp. 97–99.

* **Example 3.1.4** (the birth–death chain `Xₜ = max {0, bₜ + Xₜ₋₁}`, `ex314 p`, p. 88, with
  `Pr(bₜ = 1) = p`): `example_3_1_4_irreducible` (irreducible and aperiodic, p. 97);
  `example_3_1_4_transient` (for `p > 1/2` every state is transient and `p⁽ˡ⁾₀ⱼ → 0`, p. 97–99);
  `example_3_1_4_stationary` (for `p < 1/2`, `πᵢ = (1 − ρ)ρⁱ`, `ρ = p/q`, is the stationary
  distribution of the untruncated chain, which is positive recurrent, p. 98);
  `example_3_1_4_half` (for `p = 1/2` there is no stationary distribution, so the chain is not
  positive recurrent).
* **Example 3.1.5** (the unrestricted random walk on `ℤ`, `ex315`, p. 89):
  `example_3_1_5` (irreducible, every state has period `2`, no stationary distribution, p. 97).
* `theorem_3_1_4_countable_counterexample`: the uniform `k₀` of Theorem 3.1.4 fails for
  countable chains (Example 3.1.4 moves at most one step per period).
* `theorem_3_1_1b_countable_counterexample`: Theorem 3.1.1(b) fails for countable chains: the
  shift `i ↦ i + 1` on `ℕ` has no recurrent state.

**Corrections.**
* p. 98 says that Parts (a)–(b) of Theorem 3.1.1 remain true for countable chains. Part (b)
  (there is at least one recurrent class) is false (`theorem_3_1_1b_countable_counterexample`).
* p. 99 says that Theorem 3.1.4 also applies to countable chains. As stated (one `k₀` for all
  `i, j`) it is false (`theorem_3_1_4_countable_counterexample`); the pairwise version is
  `theorem_3_1_4_countable`.

**Not formalised.** Null recurrence for `p = 1/2` in Example 3.1.4: only the absence of a
stationary distribution (hence of positive recurrence) is proved, not recurrence. For Example
3.1.5, `p⁽ⁿ⁾ᵢⱼ → 0` is not proved (the absence of a stationary distribution is).
-/

namespace Miao.MarkovProcesses

open Filter Topology
open scoped ENNReal

/-! ### Two-point sums -/

/-- A sum with two nonzero terms. -/
theorem mc_tsum_pair {T : Type*} (f : T → ℝ≥0∞) {a b : T} (hab : a ≠ b)
    (hf : ∀ x, x ≠ a → x ≠ b → f x = 0) : ∑' x, f x = f a + f b := by
  classical
  rw [tsum_eq_sum (s := {a, b}) fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hf x hx.1 hx.2]
  exact Finset.sum_pair hab

/-! ### Example 3.1.4: the birth–death chain -/

/-- **Example 3.1.4** (Miao, p. 88): `Xₜ = max {0, bₜ + Xₜ₋₁}` with `Pr(bₜ = 1) = p`,
`Pr(bₜ = −1) = q = 1 − p`; from `i` the chain moves to `i + 1` with probability `p` and to
`max {0, i − 1}` with probability `q`. -/
noncomputable def ex314 (p : ℝ) (i j : ℕ) : ℝ≥0∞ :=
  if j = i + 1 then ENNReal.ofReal p else if j = i - 1 then ENNReal.ofReal (1 - p) else 0

/-- The rows of `ex314 p` sum to one. -/
theorem ex314_stochastic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : mc_IsStochasticE (ex314 p) := by
  intro i
  rw [mc_tsum_pair _ (show i + 1 ≠ i - 1 by omega) fun x h1 h2 => by simp [ex314, h1, h2]]
  simp only [ex314, ite_true, show i - 1 ≠ i + 1 by omega, ite_false]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- Column `0` of `ex314 p`: `Σᵢ μᵢ pᵢ₀ = q(μ₀ + μ₁)`. -/
theorem ex314_col_zero (p : ℝ) (μ : ℕ → ℝ≥0∞) :
    ∑' i, μ i * ex314 p i 0 = μ 0 * ENNReal.ofReal (1 - p) + μ 1 * ENNReal.ofReal (1 - p) := by
  rw [mc_tsum_pair _ (show (0 : ℕ) ≠ 1 by omega) fun x h1 h2 => by
    simp only [ex314]
    split_ifs <;> first | (exfalso; omega) | simp]
  simp [ex314]

/-- Column `j + 1` of `ex314 p`: `Σᵢ μᵢ pᵢ,ⱼ₊₁ = pμⱼ + qμⱼ₊₂`. -/
theorem ex314_col_succ (p : ℝ) (μ : ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' i, μ i * ex314 p i (j + 1) =
      μ j * ENNReal.ofReal p + μ (j + 2) * ENNReal.ofReal (1 - p) := by
  rw [mc_tsum_pair _ (show j ≠ j + 2 by omega) fun x h1 h2 => by
    simp only [ex314]
    split_ifs <;> first | (exfalso; omega) | simp]
  simp only [ex314, ite_true, show j + 1 = j + 2 - 1 by omega,
    show j + 2 - 1 ≠ j + 2 + 1 by omega, ite_false]

/-- The birth–death chain moves at most one step per period: `p⁽ⁿ⁾ᵢⱼ ≠ 0 ⇒ j ≤ i + n`. -/
theorem ex314_pow_ne_zero (p : ℝ) (n i j : ℕ) (h : mc_powE (ex314 p) n i j ≠ 0) : j ≤ i + n := by
  induction n generalizing i with
  | zero =>
    by_contra hne
    simp [mc_powE, mc_idE, show i ≠ j by omega] at h
  | succ n ih =>
    simp only [mc_powE, mc_mulE] at h
    obtain ⟨k, hk⟩ : ∃ k, ex314 p i k * mc_powE (ex314 p) n k j ≠ 0 := by
      by_contra hne
      push Not at hne
      exact h (ENNReal.tsum_eq_zero.2 hne)
    have h1 := left_ne_zero_of_mul hk
    have h2 := ih k (right_ne_zero_of_mul hk)
    have hk' : k ≤ i + 1 := by
      by_contra hki
      simp [ex314, show k ≠ i + 1 by omega, show k ≠ i - 1 by omega] at h1
    omega

/-- **Example 3.1.4** (Miao, p. 97): for `0 < p < 1` the birth–death chain is irreducible and
aperiodic. -/
theorem example_3_1_4_irreducible {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mc_IsIrreducibleE (ex314 p) ∧ ∀ i, mc_periodE (ex314 p) i = 1 := by
  have hP := ex314_stochastic hp0.le hp1.le
  have hup : ∀ i, mc_AccessibleE (ex314 p) i (i + 1) := fun i =>
    mc_accessibleE_of_pos (by simp [ex314, hp0])
  have hdown : ∀ i, mc_AccessibleE (ex314 p) (i + 1) i := fun i =>
    mc_accessibleE_of_pos (by simp [ex314, show i ≠ i + 1 + 1 by omega]; linarith)
  have hupk : ∀ k i, mc_AccessibleE (ex314 p) i (i + k + 1) := by
    intro k
    induction k with
    | zero => exact hup
    | succ k ih => exact fun i => (ih i).trans (hup _)
  have hdownk : ∀ k i, mc_AccessibleE (ex314 p) (i + k + 1) i := by
    intro k
    induction k with
    | zero => exact hdown
    | succ k ih => exact fun i => (hdown _).trans (ih i)
  have hacc : ∀ i j, mc_AccessibleE (ex314 p) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · obtain ⟨k, rfl⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
      exact hupk k i
    · exact (hup i).trans (hdown i)
    · obtain ⟨k, rfl⟩ : ∃ k, i = j + k + 1 := ⟨i - j - 1, by omega⟩
      exact hdownk k j
  have hirr := (mc_isIrreducibleE_iff hP).2 hacc
  refine ⟨hirr, fun i => ?_⟩
  have h0 : mc_periodE (ex314 p) 0 = 1 := by
    have h1 : 1 ∈ mc_returnSetE (ex314 p) 0 :=
      ⟨le_rfl, by rw [mc_powE_one]; simp [ex314]; linarith⟩
    exact Nat.dvd_one.1 (mc_setGcd_dvd (mc_returnSetE_isAddClosed _ 0) h1 one_pos h1)
  rw [← theorem_3_1_2_countable (ex314 p) (hirr 0 i), h0]

/-- **Theorem 3.1.4** (Miao, p. 99: "Theorem 3.1.4 also applies"), **counterexample**: the
birth–death chain is irreducible and aperiodic, but there is no `k₀` with `p⁽ᵏ⁾ᵢⱼ > 0` for all
`i, j` and all `k ≥ k₀`. -/
theorem theorem_3_1_4_countable_counterexample {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mc_IsIrreducibleE (ex314 p) ∧ (∀ i, mc_periodE (ex314 p) i = 1) ∧
      ¬ ∃ k₀, 0 < k₀ ∧ ∀ k ≥ k₀, ∀ i j, 0 < mc_powE (ex314 p) k i j := by
  refine ⟨(example_3_1_4_irreducible hp0 hp1).1, (example_3_1_4_irreducible hp0 hp1).2, ?_⟩
  rintro ⟨k₀, -, h⟩
  have := ex314_pow_ne_zero p k₀ 0 (k₀ + 1) (h k₀ le_rfl 0 (k₀ + 1)).ne'
  omega

/-- The sum `Σ_{b ≠ 0} p_{kb} x_b` for the birth–death chain. -/
theorem ex314_taboo_sum (p : ℝ) (k : ℕ) (x : ℕ → ℝ≥0∞) :
    ∑' b, (if b = 0 then 0 else ex314 p k b * x b) =
      ENNReal.ofReal p * x (k + 1) +
        (if k - 1 = 0 then 0 else ENNReal.ofReal (1 - p) * x (k - 1)) := by
  rw [mc_tsum_pair _ (show k + 1 ≠ k - 1 by omega) fun b h1 h2 => by simp [ex314, h1, h2]]
  simp only [ex314, ite_true, show k - 1 ≠ k + 1 by omega, ite_false,
    show k + 1 ≠ 0 by omega]

/-- **Example 3.1.4** (Miao, pp. 97–99): for `1/2 < p < 1` the birth–death chain is transient:
`Pr(τ₀ < ∞ | X₀ = 0) ≤ 2q < 1`; hence every state is transient and `p⁽ˡ⁾₀ⱼ → 0` for every `j`.
-/
theorem example_3_1_4_transient {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) :
    mc_hitE (ex314 p) 0 0 ≤ ENNReal.ofReal (2 * (1 - p)) ∧ (∀ j, mc_IsTransientE (ex314 p) j) ∧
      ∀ j, Tendsto (fun l => mc_powE (ex314 p) l 0 j) atTop (𝓝 0) := by
  have hP := ex314_stochastic (by linarith) hp1.le
  set q := 1 - p
  set r := q / p with hr
  have hp : 0 < p := by linarith
  have hq : 0 < q := by simp only [q]; linarith
  have hr0 : 0 ≤ r := div_nonneg hq.le hp.le
  have hrp : r * p = q := div_mul_cancel₀ q hp.ne'
  -- the minimal-solution bound `Σ_{n<N} f⁽ⁿ⁺¹⁾ₖ₀ ≤ rᵏ` for `k ≥ 1`
  have key : ∀ N k, 1 ≤ k → ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n k ≤
      ENNReal.ofReal (r ^ k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro k hk
      rw [Finset.sum_range_succ', mc_fpE_zero]
      simp only [mc_fpE_succ]
      rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
      have h1 : ∑' b, ∑ n ∈ Finset.range N,
          (if b = 0 then 0 else ex314 p k b * mc_fpE (ex314 p) 0 n b) =
          ∑' b, (if b = 0 then 0 else ex314 p k b *
            ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n b) := tsum_congr fun b => by
        by_cases hb : b = 0 <;> simp [hb, Finset.mul_sum]
      rw [h1, ex314_taboo_sum]
      by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.sub_self, ite_true, add_zero]
        have hval : ex314 p 1 0 = ENNReal.ofReal q := by simp [ex314, q]
        rw [hval]
        calc ENNReal.ofReal p * ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n (1 + 1) +
              ENNReal.ofReal q ≤ ENNReal.ofReal p * ENNReal.ofReal (r ^ 2) + ENNReal.ofReal q := by
              gcongr; exact ih 2 (by norm_num)
          _ = ENNReal.ofReal (r ^ 1) := by
              rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_add (by positivity) hq.le]
              congr 1
              have : r * (p * r) = r * q := by rw [mul_comm p r, hrp]
              nlinarith [this]
      · have hk2 : k - 1 ≠ 0 := by omega
        simp only [hk2, ite_false]
        have hval : ex314 p k 0 = 0 := by simp [ex314]; omega
        rw [hval, add_zero]
        calc ENNReal.ofReal p * ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n (k + 1) +
              ENNReal.ofReal q * ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n (k - 1)
            ≤ ENNReal.ofReal p * ENNReal.ofReal (r ^ (k + 1)) +
                ENNReal.ofReal q * ENNReal.ofReal (r ^ (k - 1)) := by
              gcongr
              · exact ih _ (by omega)
              · exact ih _ (by omega)
          _ = ENNReal.ofReal (r ^ k) := by
              rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hq.le,
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
              simp only [Nat.add_sub_cancel, pow_succ]
              have : r * (p * r) = r * q := by rw [mul_comm p r, hrp]
              nlinarith [this, pow_nonneg hr0 m]
  have hF1 : mc_hitE (ex314 p) 1 0 ≤ ENNReal.ofReal r := by
    have := ENNReal.tsum_le_of_sum_range_le fun N => key N 1 le_rfl
    rw [pow_one] at this
    exact this
  have hF0 : mc_hitE (ex314 p) 0 0 =
      ENNReal.ofReal q + ENNReal.ofReal p * mc_hitE (ex314 p) 1 0 := by
    rw [mc_hitE, tsum_eq_zero_add' ENNReal.summable, mc_fpE_zero]
    simp only [mc_fpE_succ]
    rw [ENNReal.tsum_comm]
    have h1 : ∀ b, ∑' n, (if b = 0 then 0 else ex314 p 0 b * mc_fpE (ex314 p) 0 n b) =
        if b = 0 then 0 else ex314 p 0 b * mc_hitE (ex314 p) b 0 := fun b => by
      by_cases hb : b = 0 <;> simp [hb, mc_hitE, ENNReal.tsum_mul_left]
    simp only [h1, ex314_taboo_sum, Nat.zero_sub, ite_true, add_zero]
    simp [ex314, q]
  have hbound : mc_hitE (ex314 p) 0 0 ≤ ENNReal.ofReal (2 * q) := by
    rw [hF0]
    calc ENNReal.ofReal q + ENNReal.ofReal p * mc_hitE (ex314 p) 1 0 ≤
          ENNReal.ofReal q + ENNReal.ofReal p * ENNReal.ofReal r := by gcongr
      _ = ENNReal.ofReal (2 * q) := by
          rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_add hq.le (by positivity)]
          congr 1
          rw [mul_comm p r, hrp]; ring
  have htr0 : mc_IsTransientE (ex314 p) 0 := by
    refine lt_of_le_of_lt hbound ?_
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by simp only [q]; linarith)
  obtain ⟨htr, -, hlim, -⟩ :=
    theorem_3_1_5a hP (example_3_1_4_irreducible hp (by linarith)).1 htr0
  exact ⟨hbound, htr, fun j => hlim 0 j⟩

/-- **Example 3.1.4** (Miao, p. 98): for `0 < p < 1/2`, `πᵢ = (1 − ρ)ρⁱ` with `ρ = p/q` is the
stationary distribution of the (untruncated) birth–death chain; hence the chain is positive
recurrent, `π` is its unique stationary distribution, and `πⱼ = 1/E[τⱼ | X₀ = j]`. -/
theorem example_3_1_4_stationary {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    mc_IsStationaryE (ex314 p) (fun i => ENNReal.ofReal ((1 - p / (1 - p)) * (p / (1 - p)) ^ i)) ∧
      (∀ j, mc_IsPositiveRecurrentE (ex314 p) j) ∧
      ∀ j, ENNReal.ofReal ((1 - p / (1 - p)) * (p / (1 - p)) ^ j) =
        (mc_meanRetE (ex314 p) j)⁻¹ := by
  have hP := ex314_stochastic hp0.le (by linarith)
  have hirr := (example_3_1_4_irreducible hp0 (by linarith)).1
  set q := 1 - p with hq
  set ρ := p / q with hρ
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ ρ := div_nonneg hp0.le hq0.le
  have hρ1 : ρ < 1 := (div_lt_one hq0).2 (by linarith)
  have hρq : ρ * q = p := div_mul_cancel₀ p hq0.ne'
  set π : ℕ → ℝ := fun i => (1 - ρ) * ρ ^ i
  have hπ0 : ∀ i, 0 ≤ π i := fun i => mul_nonneg (by linarith) (pow_nonneg hρ0 i)
  have hstat : mc_IsStationaryE (ex314 p) (fun i => ENNReal.ofReal (π i)) := by
    refine ⟨fun j => ?_, ?_⟩
    · rcases j with _ | j
      · rw [ex314_col_zero, ← ENNReal.ofReal_mul (hπ0 0), ← ENNReal.ofReal_mul (hπ0 1),
          ← ENNReal.ofReal_add (mul_nonneg (hπ0 0) hq0.le) (mul_nonneg (hπ0 1) hq0.le)]
        congr 1
        simp only [π, pow_zero, pow_one]
        have : (1 - ρ) * ρ * q = (1 - ρ) * p := by rw [mul_assoc, hρq]
        nlinarith [this]
      · rw [ex314_col_succ, ← ENNReal.ofReal_mul (hπ0 j), ← ENNReal.ofReal_mul (hπ0 (j + 2)),
          ← ENNReal.ofReal_add (mul_nonneg (hπ0 j) hp0.le) (mul_nonneg (hπ0 (j + 2)) hq0.le)]
        congr 1
        simp only [π, pow_succ]
        have : ρ * ρ * q = ρ * p := by rw [mul_assoc, hρq]
        have h2 : (1 - ρ) * ρ ^ j * ρ * ρ * q = (1 - ρ) * ρ ^ j * ρ * p := by
          rw [mul_assoc ((1 - ρ) * ρ ^ j * ρ), hρq]
        nlinarith [h2, pow_nonneg hρ0 j]
    · rw [← ENNReal.ofReal_tsum_of_nonneg hπ0
        ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (1 - ρ))]
      simp only [π]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1,
        mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]
  exact ⟨hstat, fun j => (mc_stationary_eq_inv hP hirr hstat j).2,
    fun j => (mc_stationary_eq_inv hP hirr hstat j).1⟩

/-- **Example 3.1.4** (Miao, p. 99), `p = 1/2`: the birth–death chain has no stationary
distribution, so it is not positive recurrent (Theorem 3.1.5(c)). -/
theorem example_3_1_4_half :
    (¬ ∃ μ, mc_IsStationaryE (ex314 (1 / 2)) μ) ∧
      ∀ j, ¬ mc_IsPositiveRecurrentE (ex314 (1 / 2)) j := by
  have hP := ex314_stochastic (p := 1 / 2) (by norm_num) (by norm_num)
  have hirr := (example_3_1_4_irreducible (p := 1 / 2) (by norm_num) (by norm_num)).1
  have hnost : ¬ ∃ μ, mc_IsStationaryE (ex314 (1 / 2)) μ := by
    rintro ⟨μ, hμ⟩
    have hfin : ∀ i, μ i ≠ ∞ := fun i =>
      ((mc_stationaryE_le_one hμ i).trans_lt ENNReal.one_lt_top).ne
    have hh' : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    have hh : ENNReal.ofReal (1 - 1 / 2) = 2⁻¹ := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hh']
    -- invariance forces `μ` to be constant
    have hconst : ∀ i, μ (i + 1) = μ i := by
      intro i
      induction i with
      | zero =>
        have h := hμ.1 0
        rw [ex314_col_zero, hh, ← add_mul] at h
        have h2 : (μ 0 + μ 1) * 2⁻¹ * 2 = μ 0 * 2 := by rw [h]
        rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one, mul_two] at h2
        exact ((ENNReal.add_right_inj (hfin 0)).1 h2)
      | succ i ih =>
        have h := hμ.1 (i + 1)
        rw [ex314_col_succ, hh, hh', ← add_mul, ih] at h
        have h2 : (μ i + μ (i + 1 + 1)) * 2⁻¹ * 2 = μ i * 2 := by rw [h]
        rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one, mul_two] at h2
        rw [ih]
        exact (ENNReal.add_right_inj (hfin i)).1 h2
    have hall : ∀ i, μ i = μ 0 := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [hconst, ih]
    have hsum := hμ.2
    simp only [hall] at hsum
    by_cases h0 : μ 0 = 0
    · simp [h0] at hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hsum
      exact ENNReal.top_ne_one hsum
  refine ⟨hnost, fun j hj => hnost ?_⟩
  obtain ⟨μ, hμ, -⟩ := theorem_3_1_5c hP hirr hj
  exact ⟨μ, hμ⟩

/-! ### Example 3.1.5: the unrestricted random walk -/

/-- **Example 3.1.5** (Miao, p. 89): the unrestricted random walk on `ℤ`, moving `±1` with
probability `1/2` each. -/
noncomputable def ex315 (i j : ℤ) : ℝ≥0∞ := if j = i + 1 ∨ j = i - 1 then 2⁻¹ else 0

/-- The rows of `ex315` sum to one. -/
theorem ex315_stochastic : mc_IsStochasticE ex315 := by
  intro i
  rw [mc_tsum_pair _ (show i + 1 ≠ i - 1 by omega) fun x h1 h2 => by simp [ex315, h1, h2]]
  simp only [ex315, true_or, or_true, ite_true]
  exact ENNReal.inv_two_add_inv_two

/-- Column sums of `ex315`: `Σᵢ μᵢ pᵢⱼ = (μⱼ₋₁ + μⱼ₊₁)/2`. -/
theorem ex315_col (μ : ℤ → ℝ≥0∞) (j : ℤ) :
    ∑' i, μ i * ex315 i j = μ (j - 1) * 2⁻¹ + μ (j + 1) * 2⁻¹ := by
  rw [mc_tsum_pair _ (show j - 1 ≠ j + 1 by omega) fun x h1 h2 => by
    simp only [ex315]
    split_ifs <;> first | (exfalso; omega) | simp]
  simp only [ex315, show j = j - 1 + 1 ∨ j = j - 1 - 1 from Or.inl (by ring),
    show j = j + 1 + 1 ∨ j = j + 1 - 1 from Or.inr (by ring), ite_true]

/-- Parity: `p⁽ⁿ⁾ᵢⱼ ≠ 0 ⇒ j − i + n` is even. -/
theorem ex315_pow_parity (n : ℕ) (i j : ℤ) (h : mc_powE ex315 n i j ≠ 0) :
    Even (j - i + n) := by
  induction n generalizing i with
  | zero =>
    by_contra hne
    have hij : i ≠ j := fun h' => hne (by subst h'; simp)
    simp [mc_powE, mc_idE, hij] at h
  | succ n ih =>
    simp only [mc_powE, mc_mulE] at h
    obtain ⟨k, hk⟩ : ∃ k, ex315 i k * mc_powE ex315 n k j ≠ 0 := by
      by_contra hne
      push Not at hne
      exact h (ENNReal.tsum_eq_zero.2 hne)
    have h1 := left_ne_zero_of_mul hk
    have h2 := ih k (right_ne_zero_of_mul hk)
    have hk' : k = i + 1 ∨ k = i - 1 := by
      by_contra hki
      simp [ex315, hki] at h1
    push_cast
    rcases hk' with rfl | rfl
    · have e : j - i + ((n : ℤ) + 1) = (j - (i + 1) + n) + 2 := by ring
      rw [e]
      exact h2.add even_two
    · convert h2 using 1
      ring

/-- **Example 3.1.5** (Miao, p. 97): the unrestricted random walk is irreducible, every state has
period `2`, and there is no stationary distribution. -/
theorem example_3_1_5 :
    mc_IsIrreducibleE ex315 ∧ (∀ i, mc_periodE ex315 i = 2) ∧
      ¬ ∃ μ, mc_IsStationaryE ex315 μ := by
  have hP := ex315_stochastic
  have hup : ∀ i, mc_AccessibleE ex315 i (i + 1) := fun i =>
    mc_accessibleE_of_pos (by simp [ex315])
  have hdown : ∀ i, mc_AccessibleE ex315 i (i - 1) := fun i =>
    mc_accessibleE_of_pos (by simp [ex315])
  have hupk : ∀ (k : ℕ) i, mc_AccessibleE ex315 i (i + k + 1) := by
    intro k
    induction k with
    | zero => simpa using hup
    | succ k ih => exact fun i => (ih i).trans (by simpa [add_assoc] using hup (i + k + 1))
  have hdownk : ∀ (k : ℕ) i, mc_AccessibleE ex315 i (i - k - 1) := by
    intro k
    induction k with
    | zero => simpa using hdown
    | succ k ih => exact fun i => (ih i).trans (by
        have := hdown (i - k - 1); push_cast; convert this using 1; ring)
  have hacc : ∀ i j, mc_AccessibleE ex315 i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = i + k + 1 := ⟨(j - i - 1).toNat, by omega⟩
      rw [hk]; exact hupk k i
    · exact (hup i).trans (by simpa using hdown (i + 1))
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = i - k - 1 := ⟨(i - j - 1).toNat, by omega⟩
      rw [hk]; exact hdownk k i
  have hirr := (mc_isIrreducibleE_iff hP).2 hacc
  refine ⟨hirr, fun i => ?_, ?_⟩
  · have hS := mc_returnSetE_isAddClosed ex315 i
    have h2 : 2 ∈ mc_returnSetE ex315 i := by
      refine ⟨by norm_num, ?_⟩
      have h := mc_powE_add_pos ex315 (m := 1) (n := 1) (i := i) (j := i + 1) (k := i)
        (by rw [mc_powE_one]; simp [ex315]) (by rw [mc_powE_one]; simp [ex315])
      simpa using h
    have heven : ∀ n ∈ mc_returnSetE ex315 i, 2 ∣ n := by
      rintro n ⟨-, hn⟩
      have := ex315_pow_parity n i i hn.ne'
      simp only [sub_self, zero_add] at this
      exact (Int.natCast_dvd_natCast.1 (even_iff_two_dvd.1 this))
    exact Nat.dvd_antisymm (mc_setGcd_dvd hS h2 (by norm_num) h2)
      (dvd_mc_setGcd hS h2 (by norm_num) heven)
  · rintro ⟨μ, hμ⟩
    have hfin : ∀ i, μ i ≠ ∞ := fun i =>
      ((mc_stationaryE_le_one hμ i).trans_lt ENNReal.one_lt_top).ne
    set a : ℤ → ℝ := fun i => (μ i).toReal
    have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
    -- `a` is affine: its increments are constant
    have hrec : ∀ j, a (j + 1) - a j = a j - a (j - 1) := by
      intro j
      have h := hμ.1 j
      rw [ex315_col] at h
      have h' := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top (hfin _) (by norm_num))
        (ENNReal.mul_ne_top (hfin _) (by norm_num)), ENNReal.toReal_mul, ENNReal.toReal_mul]
        at h'
      simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
      simp only [a]
      linarith
    set d := a 1 - a 0
    have hd : ∀ j, a (j + 1) - a j = d := by
      intro j
      induction j using Int.induction_on with
      | zero => simp [d]
      | succ k ih => rw [hrec, show (k : ℤ) + 1 - 1 = k by ring, ih]
      | pred k ih =>
        have := hrec (-(k : ℤ))
        rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
        linarith
    have hpos : ∀ n : ℕ, a n = a 0 + n * d := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => push_cast; linarith [hd n]
    have hneg : ∀ n : ℕ, a (-(n : ℤ)) = a 0 - n * d := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hd (-((n : ℤ) + 1))
        push_cast
        rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] at this
        linarith
    have hd0 : d = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · obtain ⟨n, hn⟩ := exists_nat_gt (a 0 / -d)
        have := ha0 n
        rw [hpos n] at this
        rw [div_lt_iff₀ (by linarith)] at hn
        nlinarith
      · obtain ⟨n, hn⟩ := exists_nat_gt (a 0 / d)
        have := ha0 (-(n : ℤ))
        rw [hneg n] at this
        rw [div_lt_iff₀ h] at hn
        nlinarith
    have hconst : ∀ i, μ i = μ 0 := by
      intro i
      have hi : a i = a 0 := by
        rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
        · rw [hpos, hd0]; ring
        · rw [hneg, hd0]; ring
      exact (ENNReal.toReal_eq_toReal_iff' (hfin i) (hfin 0)).1 hi
    have hsum := hμ.2
    simp only [hconst] at hsum
    by_cases h0 : μ 0 = 0
    · simp [h0] at hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hsum
      exact ENNReal.top_ne_one hsum

/-! ### The shift: a countable chain without recurrent states -/

/-- The deterministic shift `i ↦ i + 1` on `ℕ`. -/
noncomputable def mc_shift (i j : ℕ) : ℝ≥0∞ := if j = i + 1 then 1 else 0

/-- Miao, p. 98, **counterexample** to "Parts (a)–(b) of Theorem 3.1.1 are still true" for
countable chains: the shift on `ℕ` is a transition matrix with no recurrent state (every state
is transient, `Pr(τᵢ < ∞ | X₀ = i) = 0`), so the state space contains no recurrent class. -/
theorem theorem_3_1_1b_countable_counterexample :
    mc_IsStochasticE mc_shift ∧ ∀ i, mc_hitE mc_shift i i = 0 ∧ mc_IsTransientE mc_shift i := by
  have hP : mc_IsStochasticE mc_shift := fun i => by
    simp only [mc_shift]
    exact tsum_ite_eq (i + 1) 1
  have hpow : ∀ n i j, mc_powE mc_shift n i j = if j = i + n then 1 else 0 := by
    intro n
    induction n with
    | zero => intro i j; simp [mc_powE, mc_idE, eq_comm]
    | succ n ih =>
      intro i j
      simp only [mc_powE, mc_mulE, mc_shift, ih, ite_mul, one_mul, zero_mul]
      rw [tsum_eq_single (i + 1) fun k hk => by simp [hk]]
      simp only [ite_true]
      congr 1
      simp only [eq_iff_iff]
      omega
  refine ⟨hP, fun i => ?_⟩
  have h0 : mc_hitE mc_shift i i = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun n => le_antisymm ?_ bot_le
    calc mc_fpE mc_shift i n i ≤ mc_powE mc_shift (n + 1) i i := mc_fpE_le_powE _ _ _ _
      _ = 0 := by rw [hpow]; simp
  exact ⟨h0, by rw [mc_IsTransientE, h0]; exact one_pos⟩

end Miao.MarkovProcesses
