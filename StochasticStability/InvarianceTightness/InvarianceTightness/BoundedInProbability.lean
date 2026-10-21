/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.EChainsStability
import InvarianceTightness.NonEvanescence
import InvarianceTightness.Invariance
import InvarianceTightness.DriftHarris
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Chains bounded in probability (MT §12.0–12.1)

Meyn and Tweedie, Chapter 12 introduction and §12.1, pp. 288–292. `X` is a locally compact,
σ-compact, metrizable Hausdorff space with its Borel σ-algebra (each result states what it uses);
the book's standing assumption, a locally compact separable metric space, implies all of these.

**Cesàro and resolvent averages.**
* `cesaroKernel P n = P̄ⁿ = n⁻¹ Σ_{i=1}^{n} Pⁱ` (12.2), the sampled kernel of the uniform
  distribution on `{1, …, n}`; `cesaroKernel_apply_eq`, `cesaroKernel_apply`,
  `integral_cesaroKernel`, `lintegral_cesaroKernel`.
* `abs_integral_kfunR_cesaro_sub_le`: `|∫ Pg dP̄ⁿ(x) − ∫ g dP̄ⁿ(x)| ≤ 2‖g‖/n`, the telescoping step
  of (12.7); `abs_integral_kfunR_resolvent_sub_le`: `|∫ Pg dK_ε(x) − ∫ g dK_ε(x)| ≤
  2‖g‖(1 − ε)/ε` for the resolvent.
* `liminf_cesaro_le`, `le_liminf_cesaro`: Cesàro means of `[0, 1]`-sequences.

**Boundedness in probability on average** (p. 288).
* `IsBoundedInProbabilityOnAverage P`: (12.1)–(12.2); `IsBoundedInProbability.onAverage`: it is
  implied by boundedness in probability (Chapter 6).
* **Proposition 12.1.1** (`proposition_12_1_1`, p. 289): it implies non-evanescence; (12.3)
  (`inequality_12_3`): `P_x{Φⱼ ∈ C for some j ≥ n} ≥ Pⁿ(x, C)`.

**Vague limits** (Proposition D.5.6, as used on pp. 290–291). For measures `μᵢ` of mass at most
one and an ultrafilter `U`, `vagueLimit μs hμ U` is the Riesz–Markov–Kakutani measure of the
positive functional `f ↦ lim_U ∫ f dμᵢ` on `C_c(X)` (`vagueFunctional`), with
`tendsto_integral_vagueLimit` (vague convergence along `U`), `vagueLimit_univ_le` (a
sub-probability) and `integral_vagueLimit_le`, the lower bound (D.6) for bounded continuous
`g ≥ 0`. `exists_cutoff_seq` gives compactly supported cut-offs `φₙ ↑ 1`.

**Feller chains and invariant probabilities** (§12.1.2).
* `isInvariant_of_integral_le`: a finite `ν` with `∫ Pg dν ≤ ∫ g dν` for all `g ∈ C_c(X)`, `g ≥ 0`,
  is invariant (the step "`λ∞ ≥ λ∞P` forces `λ∞ = λ∞P`", p. 291).
* `exists_isInvariant_of_vague`: Foguel's argument (12.6)–(12.7).
* **Theorem 12.1.2** (p. 290): (i) `theorem_12_1_2_i`, (12.4), and `theorem_12_1_2_i_resolvent`,
  (12.5): without an invariant probability, `P̄ⁿ(x, C) → 0` and `K_ε(x, C) → 0` uniformly in `x`
  for compact `C`; (ii) `theorem_12_1_2_ii`: boundedness in probability on average gives an
  invariant probability; `exists_isInvariant_of_frequently` is the form of (i) used later.
* **Theorem 12.0.1 (i)** (`theorem_12_0_1_i`, p. 289), the same statement.
* **Proposition 12.1.3** (p. 291): `proposition_12_1_3` (a coercive `V` whose Cesàro means
  `n⁻¹ Σ_{k=1}^{n} E_x[V(Φₖ)]` have finite `liminf`) and `proposition_12_1_3_of_eventually_le`
  (`E_x[V(Φₖ)]` eventually bounded, the condition of Lemma D.5.3).
* **Proposition 12.1.4** (`proposition_12_1_4`, p. 292): with a unique invariant probability `π`,
  `P̄ⁿ(x, ·) → π` weakly; `isTightMeasureSet_range_of_liminf` (tightness in the sense (12.1) is
  tightness), `cesaroPM`, `kfunBCF`.

`succKernel` is the deterministic successor chain on `ℕ` (`succKernel_pow_apply`), used for the
counterexamples of §12.2–12.3.

**Hypotheses.**
* Proposition 12.1.3 is stated with `liminf_k E_x[V(Φₖ)] < ∞`. Theorem 12.1.2, which the book
  invokes, controls Cesàro averages, and a bound along a sparse subsequence of times does not
  bound `P̄ⁿ(x, C)` from below. The proposition is proved for Cesàro means (`proposition_12_1_3`)
  and for `E_x[V(Φₖ)]` bounded for all large `k` (`proposition_12_1_3_of_eventually_le`). The
  `liminf` version for `Pᵏ` is false: `proposition_12_1_3_counterexample` in
  `LiminfCounterexample`.
* Theorem 12.1.2 (ii) assumes `X` nonempty (on the empty space every chain is bounded in
  probability on average and no probability exists).
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported

variable {X : Type*} [MeasurableSpace X]

/-- The Cesàro kernel `P̄ⁿ = n⁻¹ Σ_{i=1}^{n} Pⁱ` (12.2), MT p. 288; it is the sampled kernel of the
uniform distribution on `{1, …, n}`. -/
noncomputable abbrev cesaroKernel (P : Kernel X X) (n : ℕ) : Kernel X X :=
  sampledKernel P (uniformDist n)

/-- `P̄ⁿ(x, ·) = n⁻¹ Σ_{i=1}^{n} Pⁱ(x, ·)` as measures. -/
theorem cesaroKernel_apply_eq (P : Kernel X X) (n : ℕ) (x : X) :
    cesaroKernel P n x = (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.Icc 1 n, (P ^ i) x := by
  ext A hA
  rw [sampledKernel_uniformDist_apply P n x hA, Measure.smul_apply, Measure.finsetSum_apply,
    smul_eq_mul]

/-- `P̄ⁿ` is a transition kernel for `n ≥ 1`. -/
theorem isMarkovKernel_cesaroKernel (P : Kernel X X) [IsMarkovKernel P] {n : ℕ} (hn : 1 ≤ n) :
    IsMarkovKernel (cesaroKernel P n) :=
  isMarkovKernel_sampledKernel P (isSamplingDist_uniformDist hn)

/-- `P̄ⁿ(x, X) ≤ 1` for every `n` (it is `0` for `n = 0`). -/
theorem cesaroKernel_univ_le (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) (x : X) :
    cesaroKernel P n x univ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cesaroKernel_apply_eq]; simp
  · have := isMarkovKernel_cesaroKernel P hn
    exact prob_le_one

/-- `P̄ⁿ` is a finite kernel. -/
theorem isFiniteKernel_cesaroKernel (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsFiniteKernel (cesaroKernel P n) :=
  ⟨⟨1, ENNReal.one_lt_top, cesaroKernel_univ_le P n⟩⟩

/-- `∫ g dP̄ⁿ(x) = n⁻¹ Σ_{i=1}^{n} ∫ g dPⁱ(x)` for bounded measurable `g`. -/
theorem integral_cesaroKernel (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) (x : X) {g : X → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    ∫ y, g y ∂cesaroKernel P n x = (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 n, ∫ y, g y ∂(P ^ i) x := by
  rw [cesaroKernel_apply_eq, integral_smul_measure, integral_finsetSum_measure]
  · simp [smul_eq_mul]
  · intro i _
    have := isMarkovKernel_pow P i
    exact Integrable.of_bound hg.aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)

/-- `∫ Pg dPⁱ(x) = ∫ g dPⁱ⁺¹(x)` for bounded measurable `g`. -/
theorem integral_kfunR_pow (P : Kernel X X) [IsMarkovKernel P] (i : ℕ) (x : X) {g : X → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    ∫ y, kfunR P g y ∂(P ^ i) x = ∫ y, g y ∂(P ^ (i + 1)) x := by
  have := isMarkovKernel_pow P i
  have := isMarkovKernel_pow P (i + 1)
  have hint : Integrable g ((P ^ (i + 1)) x) := Integrable.of_bound hg.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  rw [pow_succ'] at hint ⊢
  exact (Kernel.integral_comp hint).symm

/-- Telescoping over `{1, …, n}`: `Σ a(i + 1) − Σ a(i) = a(n + 1) − a(1)`. -/
theorem sum_Icc_succ_sub_sum_Icc (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, a (i + 1) - ∑ i ∈ Finset.Icc 1 n, a i = a (n + 1) - a 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

/-- The Cesàro telescoping bound: `|∫ Pg dP̄ⁿ(x) − ∫ g dP̄ⁿ(x)| ≤ 2B/n` for `|g| ≤ B`. -/
theorem abs_integral_kfunR_cesaro_sub_le (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) (x : X)
    {g : X → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    |∫ y, kfunR P g y ∂cesaroKernel P n x - ∫ y, g y ∂cesaroKernel P n x| ≤ 2 * B / n := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  have hPg : ∀ y, |kfunR P g y| ≤ B := abs_kfunR_le P hB
  rw [integral_cesaroKernel P n x (measurable_kfunR P hg) hPg,
    integral_cesaroKernel P n x hg hB, ← mul_sub]
  simp_rw [integral_kfunR_pow P _ x hg hB]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have htel := sum_Icc_succ_sub_sum_Icc (fun i => ∫ y, g y ∂(P ^ i) x) n
  rw [htel]
  have hb : ∀ j, |∫ y, g y ∂(P ^ j) x| ≤ B := fun j => by
    have := isMarkovKernel_pow P j
    calc |∫ y, g y ∂(P ^ j) x| ≤ ∫ y, |g y| ∂(P ^ j) x := abs_integral_le_integral_abs
      _ ≤ ∫ _, B ∂(P ^ j) x := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (integrable_const B) (ae_of_all _ hB)
      _ = B := by simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_inv, Nat.abs_cast, div_eq_mul_inv, mul_comm (2 * B)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hn'.le)
  calc |∫ y, g y ∂(P ^ (n + 1)) x - ∫ y, g y ∂(P ^ 1) x|
      ≤ |∫ y, g y ∂(P ^ (n + 1)) x| + |∫ y, g y ∂(P ^ 1) x| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hb (n + 1), hb 1]

/-! ### The resolvent -/

/-- The resolvent has mass at most one (it is `0` for `ε ≥ 1`). -/
theorem resolvent_univ_le (P : Kernel X X) [IsMarkovKernel P] (ε : ℝ≥0∞) (x : X) :
    resolvent P ε x univ ≤ 1 := by
  rcases lt_or_ge ε 1 with h | h
  · have := isMarkovKernel_resolvent P h; exact prob_le_one
  · rw [resolvent_apply P ε x MeasurableSet.univ, tsub_eq_zero_of_le h, zero_mul]
    exact zero_le_one

/-- `∫ g dK_ε(x) = Σₙ (1 − ε) εⁿ ∫ g dPⁿ(x)` for bounded measurable `g` and `ε < 1`. -/
theorem integral_resolvent (P : Kernel X X) [IsMarkovKernel P] {ε : ℝ≥0∞} (hε : ε < 1) (x : X)
    {g : X → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    ∫ y, g y ∂resolvent P ε x =
      ∑' n, (1 - ε.toReal) * ε.toReal ^ n * ∫ y, g y ∂(P ^ n) x := by
  have := isMarkovKernel_resolvent P hε
  have hint : Integrable g (resolvent P ε x) := Integrable.of_bound hg.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  change ∫ y, g y ∂(Measure.sum fun n => ((1 - ε) * ε ^ n) • (P ^ n) x) = _
  rw [integral_sum_measure hint]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hε.le
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_pow]

/-- The resolvent telescoping bound: `|∫ Pg dK_ε(x) − ∫ g dK_ε(x)| ≤ 2B(1 − ε)/ε` for
`|g| ≤ B` and `0 < ε < 1`. -/
theorem abs_integral_kfunR_resolvent_sub_le (P : Kernel X X) [IsMarkovKernel P] {ε : ℝ≥0∞}
    (hε0 : 0 < ε) (hε : ε < 1) (x : X) {g : X → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) :
    |∫ y, kfunR P g y ∂resolvent P ε x - ∫ y, g y ∂resolvent P ε x| ≤
      2 * B * (1 - ε.toReal) / ε.toReal := by
  set t := ε.toReal
  have ht0 : 0 < t := ENNReal.toReal_pos hε0.ne' (ne_top_of_lt hε)
  have ht1 : t < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hε
    rwa [ENNReal.toReal_one] at this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  have hPg : ∀ y, |kfunR P g y| ≤ B := abs_kfunR_le P hB
  set G : ℕ → ℝ := fun n => ∫ y, g y ∂(P ^ n) x
  have hG : ∀ n, |G n| ≤ B := fun n => by
    have := isMarkovKernel_pow P n
    calc |G n| ≤ ∫ y, |g y| ∂(P ^ n) x := abs_integral_le_integral_abs
      _ ≤ ∫ _, B ∂(P ^ n) x := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (integrable_const B) (ae_of_all _ hB)
      _ = B := by simp
  rw [integral_resolvent P hε x (measurable_kfunR P hg) hPg, integral_resolvent P hε x hg hB]
  simp_rw [integral_kfunR_pow P _ x hg hB]
  have hsum : ∀ k : ℕ, Summable fun n => t ^ n * G (n + k) := fun k =>
    Summable.of_norm_bounded (g := fun n => B * t ^ n)
      ((summable_geometric_of_lt_one ht0.le ht1).mul_left B) fun n => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ht0 n), mul_comm]
        exact mul_le_mul_of_nonneg_right (hG _) (pow_pos ht0 n).le
  set S := ∑' n, t ^ n * G n
  have hS : |(1 - t) * S| ≤ B := by
    have h1 : |S| ≤ B * (1 - t)⁻¹ := by
      calc |S| ≤ ∑' n, |t ^ n * G n| := by
            have := (hsum 0).norm.of_nonneg_of_le (fun n => norm_nonneg _) fun n => le_rfl
            simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hsum 0).norm
        _ ≤ ∑' n, B * t ^ n := by
            refine (hsum 0).abs.tsum_le_tsum (fun n => ?_)
              ((summable_geometric_of_lt_one ht0.le ht1).mul_left B)
            rw [abs_mul, abs_of_pos (pow_pos ht0 n), mul_comm]
            exact mul_le_mul_of_nonneg_right (hG _) (pow_pos ht0 n).le
        _ = B * (1 - t)⁻¹ := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one ht0.le ht1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    calc (1 - t) * |S| ≤ (1 - t) * (B * (1 - t)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = B := by
          rw [mul_comm B, ← mul_assoc, mul_inv_cancel₀ (by linarith : (1 : ℝ) - t ≠ 0), one_mul]
  have hshift : ∑' n, t ^ n * G (n + 1) = (S - G 0) / t := by
    have h0 := (hsum 0).tsum_eq_zero_add
    simp only [add_zero, pow_zero, one_mul] at h0
    rw [eq_div_iff ht0.ne', show S = _ from h0, ← tsum_mul_right]
    have : ∀ n, t ^ (n + 1) * G (n + 1) = t ^ n * G (n + 1) * t := fun n => by ring
    simp_rw [this]
    ring
  have e1 : ∑' n, (1 - t) * t ^ n * G (n + 1) = (1 - t) * ((S - G 0) / t) := by
    rw [← hshift, ← tsum_mul_left]; simp_rw [mul_assoc]
  have e2 : ∑' n, (1 - t) * t ^ n * G n = (1 - t) * S := by
    rw [← tsum_mul_left]; simp_rw [mul_assoc]
  rw [e1, e2]
  have : (1 - t) * ((S - G 0) / t) - (1 - t) * S = (1 - t) / t * ((1 - t) * S - G 0) := by
    field_simp; ring
  rw [this, abs_mul, abs_of_pos (div_pos (by linarith) ht0)]
  calc (1 - t) / t * |(1 - t) * S - G 0| ≤ (1 - t) / t * (B + B) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_pos (by linarith) ht0).le
        exact (abs_sub _ _).trans (add_le_add hS (hG 0))
    _ = 2 * B * (1 - t) / t := by ring

/-! ### Cesàro means of sequences -/

/-- Upper bound for partial sums: if `a ≤ 1` and `a(i) ≤ q` for `i ≥ N`, then
`Σ_{i=1}^{n} a(i) ≤ n q + min(n, N)`. -/
theorem sum_Icc_le_of_eventually_le (a : ℕ → ℝ≥0∞) (ha : ∀ i, a i ≤ 1) {N : ℕ} {q : ℝ≥0∞}
    (hq : ∀ i, N ≤ i → a i ≤ q) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, a i ≤ n * q + (min n N : ℕ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    by_cases hm : N ≤ m + 1
    · calc ∑ i ∈ Finset.Icc 1 m, a i + a (m + 1) ≤ (m * q + (min m N : ℕ)) + q :=
            add_le_add ih (hq _ hm)
        _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * q + (min (m + 1) N : ℕ) := by
            rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_right_comm]
            gcongr
            omega
    · have h1 : min m N = m := by omega
      have h2 : min (m + 1) N = m + 1 := by omega
      calc ∑ i ∈ Finset.Icc 1 m, a i + a (m + 1) ≤ (m * q + (min m N : ℕ)) + 1 :=
            add_le_add ih (ha _)
        _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * q + (min (m + 1) N : ℕ) := by
            rw [h1, h2, add_assoc]
            push_cast
            gcongr
            exact le_self_add

/-- Lower bound for partial sums: if `b ≤ 1` and `b ≤ a(i)` for `i ≥ N`, then
`n b ≤ Σ_{i=1}^{n} a(i) + min(n, N)`. -/
theorem le_sum_Icc_of_eventually_le (a : ℕ → ℝ≥0∞) {N : ℕ} {b : ℝ≥0∞} (hb : b ≤ 1)
    (hq : ∀ i, N ≤ i → b ≤ a i) (n : ℕ) :
    n * b ≤ ∑ i ∈ Finset.Icc 1 n, a i + (min n N : ℕ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    by_cases hm : N ≤ m + 1
    · calc ((m + 1 : ℕ) : ℝ≥0∞) * b = m * b + b := by push_cast; rw [add_mul, one_mul]
        _ ≤ (∑ i ∈ Finset.Icc 1 m, a i + (min m N : ℕ)) + a (m + 1) := add_le_add ih (hq _ hm)
        _ ≤ ∑ i ∈ Finset.Icc 1 m, a i + a (m + 1) + (min (m + 1) N : ℕ) := by
            rw [add_right_comm]
            gcongr
            omega
    · have h1 : min m N = m := by omega
      have h2 : min (m + 1) N = m + 1 := by omega
      calc ((m + 1 : ℕ) : ℝ≥0∞) * b = m * b + b := by push_cast; rw [add_mul, one_mul]
        _ ≤ (∑ i ∈ Finset.Icc 1 m, a i + (min m N : ℕ)) + 1 := add_le_add ih hb
        _ ≤ ∑ i ∈ Finset.Icc 1 m, a i + a (m + 1) + (min (m + 1) N : ℕ) := by
            rw [h1, h2, add_assoc]
            push_cast
            gcongr
            exact le_self_add

/-- The Cesàro means of a `[0, 1]`-sequence that is eventually at most `q` have `liminf ≤ q`. -/
theorem liminf_cesaro_le (a : ℕ → ℝ≥0∞) (ha : ∀ i, a i ≤ 1) {N : ℕ} {q : ℝ≥0∞}
    (hq : ∀ i, N ≤ i → a i ≤ q) :
    atTop.liminf (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i) ≤ q := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have ht : Tendsto (fun n : ℕ => (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top N)) (a := (N : ℝ≥0∞))
    rwa [mul_zero] at this
  have hev : ∀ᶠ n : ℕ in atTop, (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ η :=
    ht.eventually (Iic_mem_nhds (by exact_mod_cast hη))
  have hb : ∀ n : ℕ, (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i ≤ q + N * (n : ℝ≥0∞)⁻¹ := by
    intro n
    calc (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i
        ≤ (n : ℝ≥0∞)⁻¹ * (n * q + (min n N : ℕ)) := by
          gcongr; exact sum_Icc_le_of_eventually_le a ha hq n
      _ ≤ q + N * (n : ℝ≥0∞)⁻¹ := by
          rw [mul_add, ← mul_assoc, mul_comm _ ((min n N : ℕ) : ℝ≥0∞)]
          gcongr
          · exact mul_le_of_le_one_left' (ENNReal.inv_mul_le_one _)
          · exact_mod_cast min_le_right n N
  exact liminf_le_of_frequently_le'
    (hev.mono fun n hn => (hb n).trans (add_le_add_right hn q)).frequently

/-- The Cesàro means of a `[0, 1]`-sequence have `liminf` at least that of the sequence. -/
theorem le_liminf_cesaro (a : ℕ → ℝ≥0∞) (ha : ∀ i, a i ≤ 1) :
    atTop.liminf a ≤ atTop.liminf (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i) := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf hc)
  have hc1 : c ≤ 1 := (hN N le_rfl).le.trans (ha N)
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have ht : Tendsto (fun n : ℕ => (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top N)) (a := (N : ℝ≥0∞))
    rwa [mul_zero] at this
  have hev : ∀ᶠ n : ℕ in atTop, (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ η :=
    ht.eventually (Iic_mem_nhds (by exact_mod_cast hη))
  have hb : ∀ n : ℕ, 1 ≤ n →
      c ≤ (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i + N * (n : ℝ≥0∞)⁻¹ := by
    intro n hn
    have h1 := le_sum_Icc_of_eventually_le a hc1 (fun i hi => (hN i hi).le) n
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h2 : c * n ≤ ∑ i ∈ Finset.Icc 1 n, a i + N := by
      rw [mul_comm]
      exact h1.trans (by gcongr; exact_mod_cast min_le_right n N)
    have h3 := (ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))).2 h2
    rwa [div_eq_mul_inv, add_mul, mul_comm] at h3
  have hfin : ∀ᶠ n : ℕ in atTop, c - η ≤ (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    rw [tsub_le_iff_right]
    exact (hb n hn1).trans (add_le_add_right hn _)
  have := le_liminf_of_le (by isBoundedDefault) hfin
  rwa [tsub_le_iff_right] at this


/-! ### Cut-off functions -/

omit [MeasurableSpace X] in
variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X] in
/-- On a σ-compact locally compact Hausdorff space there are compactly supported continuous
`0 ≤ φₙ ≤ 1`, increasing in `n`, with `φₙ = 1` on any given compact set for all large `n`. -/
theorem exists_cutoff_seq : ∃ φ : ℕ → C_c(X, ℝ), Monotone (fun n => ⇑(φ n)) ∧
    (∀ n x, φ n x ∈ Icc (0 : ℝ) 1) ∧
    ∀ K : Set X, IsCompact K → ∃ N, ∀ n, N ≤ n → ∀ x ∈ K, φ n x = 1 := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have hψ : ∀ n, ∃ f : C(X, ℝ), EqOn f 1 (K n) ∧ EqOn f 0 (interior (K (n + 1)))ᶜ ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun n =>
    exists_continuous_one_zero_of_isCompact (K.isCompact n) isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.2 (K.subset_interior_succ n))
  choose ψ hψ1 hψ0 hψc hψ01 using hψ
  refine ⟨fun n => ⟨ψ n, hψc n⟩, monotone_nat_of_le_succ fun n x => ?_, fun n x => hψ01 n x,
    fun C hC => ?_⟩
  · change ψ n x ≤ ψ (n + 1) x
    by_cases hx : x ∈ interior (K (n + 1))
    · rw [hψ1 (n + 1) (interior_subset hx)]; exact (hψ01 n x).2
    · rw [hψ0 n hx]; exact (hψ01 (n + 1) x).1
  · obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hC
    exact ⟨N, fun n hn x hx => hψ1 n (K.subset hn (hN hx))⟩

omit [MeasurableSpace X] in
variable [TopologicalSpace X] in
/-- Cut-offs converge to `1` pointwise. -/
theorem cutoff_eventually_eq_one {φ : ℕ → C_c(X, ℝ)}
    (hφ : ∀ K : Set X, IsCompact K → ∃ N, ∀ n, N ≤ n → ∀ x ∈ K, φ n x = 1) (x : X) :
    ∀ᶠ n in atTop, φ n x = 1 := by
  obtain ⟨N, hN⟩ := hφ {x} isCompact_singleton
  exact eventually_atTop.2 ⟨N, fun n hn => hN n hn x rfl⟩

/-! ### Limits of integrals along an ultrafilter -/

/-- A family of measures with total mass at most one. -/
theorem isFiniteMeasure_of_univ_le {μ : Measure X} (h : μ univ ≤ 1) : IsFiniteMeasure μ :=
  ⟨h.trans_lt ENNReal.one_lt_top⟩

/-- `|∫ g dμ| ≤ B` for `|g| ≤ B` and `μ(X) ≤ 1`. -/
theorem abs_integral_le_of_univ_le {μ : Measure X} (h : μ univ ≤ 1) {g : X → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |g x| ≤ B) : |∫ x, g x ∂μ| ≤ B := by
  have := isFiniteMeasure_of_univ_le h
  calc |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, B ∂μ := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
        (integrable_const B) (ae_of_all _ hB)
    _ = μ.real univ * B := by rw [integral_const, smul_eq_mul]
    _ ≤ 1 * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact h)
    _ = B := one_mul B

/-- Along an ultrafilter, integrals of a bounded function against measures of mass at most one
converge. -/
theorem exists_tendsto_integral {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1)
    (U : Ultrafilter ι) {g : X → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, |g x| ≤ B) :
    ∃ c, Tendsto (fun i => ∫ x, g x ∂μs i) (U : Filter ι) (𝓝 c) := by
  obtain ⟨c, -, hc⟩ := (isCompact_Icc (a := -B) (b := B)).ultrafilter_le_nhds
    (U.map fun i => ∫ x, g x ∂μs i) (le_principal_iff.2 (Filter.mem_map.2 (univ_mem' fun i =>
      abs_le.1 (abs_integral_le_of_univ_le (hμ i) hB0 hB))))
  exact ⟨c, hc⟩


/-! ### Vague limits -/

omit [MeasurableSpace X] in
/-- A compactly supported continuous function is bounded by some `B ≥ 0`. -/
theorem exists_abs_le_cc [TopologicalSpace X] (f : C_c(X, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- The limit along `U` of `∫ f dμᵢ`, a positive linear functional on `C_c(X)` (the functional of a
vague limit point, MT Proposition D.5.6). -/
noncomputable def vagueFunctional [TopologicalSpace X] [OpensMeasurableSpace X] {ι : Type*}
    (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1) (U : Ultrafilter ι) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => limUnder (U : Filter ι) fun i => ∫ x, f x ∂μs i
      map_add' := fun f g => by
        have := fun i => isFiniteMeasure_of_univ_le (hμ i)
        obtain ⟨Bf, hBf0, hBf⟩ := exists_abs_le_cc f
        obtain ⟨Bg, hBg0, hBg⟩ := exists_abs_le_cc g
        have hf := tendsto_nhds_limUnder (exists_tendsto_integral μs hμ U hBf0 hBf)
        have hg := tendsto_nhds_limUnder (exists_tendsto_integral μs hμ U hBg0 hBg)
        have hfg : Tendsto (fun i => ∫ x, (f + g) x ∂μs i) (U : Filter ι)
            (𝓝 ((limUnder (U : Filter ι) fun i => ∫ x, f x ∂μs i) +
              limUnder (U : Filter ι) fun i => ∫ x, g x ∂μs i)) :=
          (hf.add hg).congr fun i => (integral_add f.integrable g.integrable).symm
        exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, hfg⟩) hfg
      map_smul' := fun c f => by
        have := fun i => isFiniteMeasure_of_univ_le (hμ i)
        obtain ⟨Bf, hBf0, hBf⟩ := exists_abs_le_cc f
        have hf := tendsto_nhds_limUnder (exists_tendsto_integral μs hμ U hBf0 hBf)
        have hcf : Tendsto (fun i => ∫ x, (c • f) x ∂μs i) (U : Filter ι)
            (𝓝 (c * limUnder (U : Filter ι) fun i => ∫ x, f x ∂μs i)) :=
          (hf.const_mul c).congr fun i => (integral_const_mul c _).symm
        exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, hcf⟩) hcf }
    fun f hf => by
      have := fun i => isFiniteMeasure_of_univ_le (hμ i)
      obtain ⟨Bf, hBf0, hBf⟩ := exists_abs_le_cc f
      have h := tendsto_nhds_limUnder (exists_tendsto_integral μs hμ U hBf0 hBf)
      exact ge_of_tendsto h (Eventually.of_forall fun i => integral_nonneg fun x => hf x)

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

/-- A **vague limit point** along the ultrafilter `U` of measures `μᵢ` of mass at most one (MT
Proposition D.5.6): the Riesz–Markov–Kakutani measure of `vagueFunctional`. -/
noncomputable def vagueLimit {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1)
    (U : Ultrafilter ι) : Measure X :=
  RealRMK.rieszMeasure (vagueFunctional μs hμ U)

/-- Vague convergence along `U`: `∫ f dμᵢ → ∫ f dμ∞` for every `f ∈ C_c(X)`. -/
theorem tendsto_integral_vagueLimit {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1)
    (U : Ultrafilter ι) (f : C_c(X, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂μs i) (U : Filter ι) (𝓝 (∫ x, f x ∂vagueLimit μs hμ U)) := by
  rw [vagueLimit, RealRMK.integral_rieszMeasure]
  obtain ⟨Bf, hBf0, hBf⟩ := exists_abs_le_cc f
  exact tendsto_nhds_limUnder (exists_tendsto_integral μs hμ U hBf0 hBf)

variable [SigmaCompactSpace X]

/-- A vague limit point has mass at most one. -/
theorem vagueLimit_univ_le {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1)
    (U : Ultrafilter ι) : vagueLimit μs hμ U univ ≤ 1 := by
  have := fun i => isFiniteMeasure_of_univ_le (hμ i)
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have hK : ∀ n, vagueLimit μs hμ U (K n) ≤ 1 := fun n => by
    obtain ⟨N, hN⟩ := hφ1 (K n) (K.isCompact n)
    have h1 := RealRMK.rieszMeasure_le_of_eq_one (vagueFunctional μs hμ U)
      (fun x => (hφ01 N x).1) (K.isCompact n) (fun x hx => hN N le_rfl x hx)
    refine h1.trans (ENNReal.ofReal_le_one.2 ?_)
    have ht := tendsto_integral_vagueLimit μs hμ U (φ N)
    rw [vagueLimit, RealRMK.integral_rieszMeasure] at ht
    refine le_of_tendsto ht (Eventually.of_forall fun i => ?_)
    have h2 := abs_integral_le_of_univ_le (hμ i) zero_le_one (g := fun x => φ N x)
      (fun x => by rw [abs_of_nonneg (hφ01 N x).1]; exact (hφ01 N x).2)
    exact (le_abs_self _).trans h2
  rw [← K.iUnion_eq, Monotone.measure_iUnion fun m n hmn => K.subset hmn]
  exact iSup_le hK

/-- A vague limit point is a finite measure. -/
theorem isFiniteMeasure_vagueLimit {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1)
    (U : Ultrafilter ι) : IsFiniteMeasure (vagueLimit μs hμ U) :=
  isFiniteMeasure_of_univ_le (vagueLimit_univ_le μs hμ U)

/-- **The lower bound (D.6) for a vague limit** (MT p. 291): for a bounded continuous `g ≥ 0`,
`∫ g dμ∞ ≤ lim_U ∫ g dμᵢ`. -/
theorem integral_vagueLimit_le {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1)
    (U : Ultrafilter ι) {g : X → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {B : ℝ}
    (hB : ∀ x, g x ≤ B) {c : ℝ} (hc : Tendsto (fun i => ∫ x, g x ∂μs i) (U : Filter ι) (𝓝 c)) :
    ∫ x, g x ∂vagueLimit μs hμ U ≤ c := by
  have := fun i => isFiniteMeasure_of_univ_le (hμ i)
  have := isFiniteMeasure_vagueLimit μs hμ U
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  set gφ : ℕ → C_c(X, ℝ) := fun n =>
    ⟨⟨fun x => g x * φ n x, hg.mul (φ n).continuous⟩, (φ n).hasCompactSupport.mul_left⟩
  have hgφ : ∀ n x, gφ n x = g x * φ n x := fun n x => rfl
  have hle : ∀ n, ∫ x, gφ n x ∂vagueLimit μs hμ U ≤ c := fun n => by
    refine le_of_tendsto_of_tendsto' (tendsto_integral_vagueLimit μs hμ U (gφ n)) hc fun i => ?_
    refine integral_mono (gφ n).integrable
      (Integrable.of_bound hg.aestronglyMeasurable B (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hB x)) fun x => ?_
    rw [hgφ]
    exact mul_le_of_le_one_right (hg0 x) (hφ01 n x).2
  have ht : Tendsto (fun n => ∫ x, gφ n x ∂vagueLimit μs hμ U) atTop
      (𝓝 (∫ x, g x ∂vagueLimit μs hμ U)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (gφ n).continuous.aestronglyMeasurable) (integrable_const B)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [hgφ, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x), abs_of_nonneg (hφ01 n x).1]
      exact (mul_le_of_le_one_right (hg0 x) (hφ01 n x).2).trans (hB x)
    · refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [cutoff_eventually_eq_one hφ1 x] with n hn
      rw [hgφ, hn, mul_one]
  exact le_of_tendsto' ht hle

/-! ### Invariance from a functional inequality -/

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [SigmaCompactSpace X] in
/-- `P(f + c) = Pf + c` for a Markov kernel and bounded measurable `f`. -/
theorem kfunR_add_const (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (c : ℝ) (x : X) :
    kfunR P (fun y => f y + c) x = kfunR P f x + c := by
  simp only [kfunR]
  rw [integral_add (Integrable.of_bound hf.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)) (integrable_const c)]
  simp

variable [TopologicalSpace.PseudoMetrizableSpace X]

/-- **Invariance from the test-function inequality** (the step "`λ∞ ≥ λ∞P`, which is only
possible if `λ∞ = λ∞P`", MT p. 291): a finite measure `ν` with `∫ Pg dν ≤ ∫ g dν` for every
nonnegative `g ∈ C_c(X)` is invariant. The inequality extends to bounded continuous `g ≥ 0`
with cut-offs, then, applied to `‖f‖ ± f`, gives `∫ Pf dν = ∫ f dν` for every bounded continuous
`f`, and finite measures agreeing on bounded continuous functions are equal. -/
theorem isInvariant_of_integral_le {P : Kernel X X} [IsMarkovKernel P] {ν : Measure X}
    [IsFiniteMeasure ν]
    (h : ∀ g : C_c(X, ℝ), (∀ x, 0 ≤ g x) → ∫ x, kfunR P g x ∂ν ≤ ∫ x, g x ∂ν) :
    IsInvariant P ν := by
  obtain ⟨φ, -, hφ01, hφ1⟩ := exists_cutoff_seq (X := X)
  -- the inequality for bounded continuous `g ≥ 0`
  have hA : ∀ g : X →ᵇ ℝ, (∀ x, 0 ≤ g x) → ∫ x, kfunR P g x ∂ν ≤ ∫ x, g x ∂ν := by
    intro g hg0
    set B := ‖g‖
    have hgB : ∀ x, |g x| ≤ B := fun x => by
      rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm x
    set gφ : ℕ → C_c(X, ℝ) := fun n =>
      ⟨⟨fun x => g x * φ n x, g.continuous.mul (φ n).continuous⟩,
        (φ n).hasCompactSupport.mul_left⟩
    have hgφ : ∀ n x, gφ n x = g x * φ n x := fun n x => rfl
    have hgφB : ∀ n x, |gφ n x| ≤ B := fun n x => by
      rw [hgφ, abs_mul, abs_of_nonneg (hφ01 n x).1]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hφ01 n x).2).trans (hgB x)
    have hlim : ∀ μ : Measure X, IsFiniteMeasure μ →
        Tendsto (fun n => ∫ x, gφ n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := fun μ _ => by
      refine tendsto_integral_of_dominated_convergence (fun _ => B)
        (fun n => (gφ n).continuous.aestronglyMeasurable) (integrable_const B)
        (fun n => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgφB n x)
        (Eventually.of_forall fun x => tendsto_nhds_of_eventually_eq ?_)
      filter_upwards [cutoff_eventually_eq_one hφ1 x] with n hn
      rw [hgφ, hn, mul_one]
    have hPlim : Tendsto (fun n => ∫ x, kfunR P (gφ n) x ∂ν) atTop
        (𝓝 (∫ x, kfunR P g x ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => B)
        (fun n => (measurable_kfunR P (gφ n).continuous.measurable).aestronglyMeasurable)
        (integrable_const B)
        (fun n => Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact abs_kfunR_le P (hgφB n) x)
        (Eventually.of_forall fun x => hlim (P x) inferInstance)
    exact le_of_tendsto_of_tendsto' hPlim (hlim ν inferInstance) fun n =>
      h (gφ n) fun x => by rw [hgφ]; exact mul_nonneg (hg0 x) (hφ01 n x).1
  -- equality for bounded continuous `f`
  have hB : ∀ f : X →ᵇ ℝ, ∫ x, kfunR P f x ∂ν = ∫ x, f x ∂ν := by
    intro f
    set c := ‖f‖
    have hfc : ∀ x, |f x| ≤ c := fun x => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
    have hint : Integrable (fun x => f x) ν := f.integrable ν
    have hPint : Integrable (fun x => kfunR P f x) ν :=
      Integrable.of_bound (measurable_kfunR P f.continuous.measurable).aestronglyMeasurable c
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_kfunR_le P hfc x)
    have h1 := hA (f + BoundedContinuousFunction.const X c) fun x => by
      simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_apply',
        Pi.add_apply]
      linarith [neg_abs_le (f x), hfc x]
    have h2 := hA (BoundedContinuousFunction.const X c - f) fun x => by
      simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.const_apply',
        Pi.sub_apply]
      linarith [le_abs_self (f x), hfc x]
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_apply',
      BoundedContinuousFunction.coe_sub, Pi.add_apply, Pi.sub_apply] at h1 h2
    have e1 : ∀ x, kfunR P (⇑f + ⇑(BoundedContinuousFunction.const X c)) x =
        kfunR P f x + c := fun x => kfunR_add_const P f.continuous.measurable hfc c x
    have e2 : ∀ x, kfunR P (⇑(BoundedContinuousFunction.const X c) - ⇑f) x =
        c - kfunR P f x := fun x => by
      have := kfunR_add_const P (f := fun y => -f y) f.continuous.measurable.neg
        (fun y => by rw [abs_neg]; exact hfc y) c x
      simp only [kfunR] at this ⊢
      rw [show (⇑(BoundedContinuousFunction.const X c) - ⇑f) = fun y => -f y + c from
        funext fun y => by simp; ring, this,
        integral_neg]
      ring
    simp_rw [e1, e2] at h1 h2
    rw [integral_add hPint (integrable_const c), integral_add hint (integrable_const c)] at h1
    rw [integral_sub (integrable_const c) hPint, integral_sub (integrable_const c) hint] at h2
    linarith
  -- conclude
  unfold IsInvariant
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_comp_measure P ν (f.integrable _)]
  exact hB f

/-- **Foguel's argument** (proof of Theorem 12.1.2, MT pp. 290–291). Let `P` be weak Feller and
`μᵢ` measures of mass at most one with `∫ Pg dμᵢ − ∫ g dμᵢ → 0` along an ultrafilter `U` for
every `g ∈ C_c(X)`, and `∫ f dμᵢ ≥ δ > 0` eventually for some `f ∈ C_c(X)`. Then the vague limit
point `λ∞` is a nonzero invariant measure, and its normalisation is an invariant probability. -/
theorem exists_isInvariant_of_vague {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {ι : Type*} (μs : ι → Measure X) (hμ : ∀ i, μs i univ ≤ 1) (U : Ultrafilter ι)
    (hdiff : ∀ g : C_c(X, ℝ),
      Tendsto (fun i => ∫ x, kfunR P g x ∂μs i - ∫ x, g x ∂μs i) (U : Filter ι) (𝓝 0))
    {f : C_c(X, ℝ)} {δ : ℝ} (hδ : 0 < δ) (hf : ∀ᶠ i in (U : Filter ι), δ ≤ ∫ x, f x ∂μs i) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π := by
  set ν := vagueLimit μs hμ U
  have := isFiniteMeasure_vagueLimit μs hμ U
  have hinv : IsInvariant P ν := by
    refine isInvariant_of_integral_le fun g hg0 => ?_
    obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc g
    have hPc : Continuous (kfunR P g) :=
      (proposition_6_1_1_i_weak P).1 hP g.toBoundedContinuousFunction
    have hPB : ∀ x, |kfunR P g x| ≤ B := abs_kfunR_le P hB
    obtain ⟨c, hc⟩ := exists_tendsto_integral μs hμ U hB0 hPB
    have hgc : Tendsto (fun i => ∫ x, g x ∂μs i) (U : Filter ι) (𝓝 c) := by
      have := hc.sub (hdiff g)
      simp only [sub_sub_cancel, sub_zero] at this
      exact this
    rw [tendsto_nhds_unique (tendsto_integral_vagueLimit μs hμ U g) hgc]
    exact integral_vagueLimit_le μs hμ U hPc (fun x => integral_nonneg fun y => hg0 y)
      (fun x => (le_abs_self _).trans (hPB x)) hc
  have hpos : δ ≤ ∫ x, f x ∂ν := ge_of_tendsto (tendsto_integral_vagueLimit μs hμ U f) hf
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, integral_zero_measure] at hpos
    linarith
  refine ⟨(ν univ)⁻¹ • ν, ⟨?_⟩, hinv.smul _⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.2 hν0) (measure_ne_top _ _)

/-! ### Theorem 12.1.2 -/

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] in
/-- `μ(C) ≤ ∫ f dμ` when `f ≥ 1_C`. -/
theorem measureReal_le_integral_of_indicator_le {μ : Measure X} [IsFiniteMeasure μ] {C : Set X}
    (hC : MeasurableSet C) {f : X → ℝ} (hf : Integrable f μ)
    (hfC : ∀ x, C.indicator 1 x ≤ f x) : μ.real C ≤ ∫ x, f x ∂μ := by
  rw [← integral_indicator_one hC]
  exact integral_mono ((integrable_const 1).indicator hC) hf hfC

omit [MeasurableSpace X] [SigmaCompactSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [BorelSpace X] in
/-- Urysohn: a compact set `C` has a compactly supported continuous `f` with `1_C ≤ f ≤ 1`. -/
theorem exists_cc_indicator_le {C : Set X} (hC : IsCompact C) :
    ∃ f : C_c(X, ℝ), (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ ∀ x, C.indicator 1 x ≤ f x := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty C)
  refine ⟨⟨f, hfc⟩, hf01, fun x => ?_⟩
  by_cases hx : x ∈ C
  · rw [indicator_of_mem hx, Pi.one_apply]; exact (hf1 hx).ge
  · rw [indicator_of_notMem hx]; exact (hf01 x).1

/-- **Theorem 12.1.2 (i)**, (12.4) (MT p. 290): for a weak Feller chain without an invariant
probability, `P̄ⁿ(x, C) → 0` uniformly in `x` for every compact `C`. -/
theorem theorem_12_1_2_i {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (hno : ¬ ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π) {C : Set X}
    (hC : IsCompact C) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x, cesaroKernel P n x C ≤ ε := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_forall, not_le] at h
  set S := {n : ℕ | ∃ x, ε < cesaroKernel P n x C}
  have hS : ∃ᶠ n in atTop, n ∈ S := h
  have hF : (atTop ⊓ 𝓟 S).NeBot := frequently_iff_neBot.1 hS
  obtain ⟨n₀, x₀, hx₀⟩ := hS.exists
  have hx : ∀ n, ∃ x, n ∈ S → ε < cesaroKernel P n x C := fun n => by
    by_cases hn : n ∈ S
    · obtain ⟨x, hx⟩ := hn; exact ⟨x, fun _ => hx⟩
    · exact ⟨x₀, fun h => absurd h hn⟩
  choose xs hxs using hx
  set U := Ultrafilter.of (atTop ⊓ 𝓟 S)
  have hUle : (U : Filter ℕ) ≤ atTop ⊓ 𝓟 S := Ultrafilter.of_le _
  set μs : ℕ → Measure X := fun n => cesaroKernel P n (xs n)
  have hμ : ∀ n, μs n univ ≤ 1 := fun n => cesaroKernel_univ_le P n (xs n)
  obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hC
  have hε1 : ε < 1 :=
    hx₀.trans_le ((measure_mono (subset_univ C)).trans (cesaroKernel_univ_le P n₀ x₀))
  refine hno (exists_isInvariant_of_vague hP μs hμ U (fun g => ?_)
    (f := f) (δ := ε.toReal) (ENNReal.toReal_pos hε.ne' (ne_top_of_lt hε1)) ?_)
  · obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc g
    refine (squeeze_zero_norm (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (2 * B))).mono_left (hUle.trans inf_le_left)
    rw [Real.norm_eq_abs]
    exact abs_integral_kfunR_cesaro_sub_le P n (xs n) g.continuous.measurable hB
  · filter_upwards [hUle (mem_inf_of_right (mem_principal_self S))] with n hn
    have := isFiniteMeasure_of_univ_le (hμ n)
    refine le_trans ?_ (measureReal_le_integral_of_indicator_le hC.measurableSet
      (f.integrable) hfC)
    rw [measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hxs n hn).le

/-! ### Boundedness in probability on average -/

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [SigmaCompactSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `P̄ⁿ(x, A) = n⁻¹ Σ_{i=1}^{n} Pⁱ(x, A)`. -/
theorem cesaroKernel_apply (P : Kernel X X) (n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    cesaroKernel P n x A = (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, (P ^ i) x A :=
  sampledKernel_uniformDist_apply P n x hA

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] [SigmaCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- The chain is **bounded in probability on average** (MT p. 288): for every `x` the Cesàro
averages `{P̄ᵏ(x, ·)}` are tight in the sense (12.1), `liminf_k P̄ᵏ(x, C) ≥ 1 − ε` for some
compact `C`. -/
def IsBoundedInProbabilityOnAverage (P : Kernel X X) : Prop :=
  ∀ x : X, ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set X, IsCompact C ∧
    1 - ε ≤ atTop.liminf fun k : ℕ => cesaroKernel P k x C

omit [LocallyCompactSpace X] [SigmaCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Boundedness in probability (Chapter 6) implies boundedness in probability on average: the
Cesàro means of `Pᵏ(x, C)` have `liminf` at least `liminf_k Pᵏ(x, C)` (the "slightly extended
form" of MT p. 288). -/
theorem IsBoundedInProbability.onAverage {P : Kernel X X} [IsMarkovKernel P]
    (h : IsBoundedInProbability P) : IsBoundedInProbabilityOnAverage P := by
  intro x ε hε
  obtain ⟨C, hC, hlim⟩ := h x ε hε
  refine ⟨C, hC, hlim.trans ?_⟩
  have := isMarkovKernel_pow P
  have h1 := le_liminf_cesaro (fun i => (P ^ i) x C) fun i => prob_le_one
  simp_rw [cesaroKernel_apply P _ x hC.measurableSet]
  exact h1

omit [LocallyCompactSpace X] [SigmaCompactSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [BorelSpace X] in
/-- **Proposition 12.1.1** (MT p. 289): a chain bounded in probability on average is
non-evanescent. For a compact `C` with `liminf_n P̄ⁿ(x, C) ≥ 1 − ε`, the events
`{Φₖ ∈ C for some k ≥ N}` have probability at least `liminf_n P̄ⁿ(x, C)` (the Cesàro means are
eventually at most this probability), so `P_x{Φ ∈ C i.o.} ≥ 1 − ε` and `P_x{Φ → ∞} ≤ ε`. -/
theorem proposition_12_1_1 [OpensMeasurableSpace X] {P : Kernel X X} [IsMarkovKernel P]
    (hb : IsBoundedInProbabilityOnAverage P) : IsNonEvanescent P := by
  have := isMarkovKernel_pathKernel P
  have := isMarkovKernel_pow P
  intro x
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  obtain ⟨C, hC, hlim⟩ := hb x ε (by exact_mod_cast hε)
  have hCm := hC.measurableSet
  set S : ℕ → Set (ℕ → X) := fun N => ⋃ k, ⋃ (_ : N ≤ k), {ω | ω k ∈ C}
  have hSm : ∀ N, MeasurableSet (S N) := fun N =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => measurable_pi_apply k hCm
  have hq : ∀ N, 1 - (ε : ℝ≥0∞) ≤ pathKernel P x (S N) := fun N => by
    refine hlim.trans ?_
    simp_rw [cesaroKernel_apply P _ x hCm]
    refine liminf_cesaro_le (fun i => (P ^ i) x C) (fun i => prob_le_one) (N := N) fun i hi => ?_
    rw [← pathKernel_coord_mem P x i hCm]
    exact measure_mono (subset_iUnion₂_of_subset i hi subset_rfl)
  have hio : pathKernel P x (ioSet C) = ⨅ N, pathKernel P x (S N) := by
    rw [ioSet_eq_iInter]
    exact Antitone.measure_iInter (fun M N hMN => iUnion₂_mono' fun k hk =>
        ⟨k, hMN.trans hk, subset_rfl⟩) (fun N => (hSm N).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have h1 : 1 - (ε : ℝ≥0∞) ≤ pathKernel P x (ioSet C) := by rw [hio]; exact le_iInf hq
  have hsub : tendsToInfty (X := X) ⊆ (ioSet C)ᶜ := fun ω hω => hω C hC
  calc pathKernel P x tendsToInfty ≤ pathKernel P x (ioSet C)ᶜ := measure_mono hsub
    _ = 1 - pathKernel P x (ioSet C) := prob_compl_eq_one_sub (measurableSet_ioSet hCm)
    _ ≤ 1 - (1 - (ε : ℝ≥0∞)) := tsub_le_tsub_left h1 1
    _ ≤ ε := by
        rw [tsub_le_iff_right]
        exact le_tsub_add.trans (by rw [add_comm])

/-- `2B(1 − ε)/ε → 0` as `ε ↑ 1`. -/
theorem tendsto_resolvent_bound (B : ℝ) :
    Tendsto (fun ε : ℝ≥0∞ => 2 * B * (1 - ε.toReal) / ε.toReal) (𝓝[<] 1) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ≥0∞ => ε.toReal) (𝓝[<] 1) (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ≥0∞)))
    rwa [ENNReal.toReal_one] at this
  have := ((tendsto_const_nhds (x := 2 * B)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub h1)).div h1 one_ne_zero
  simp only [sub_self, mul_zero, zero_div] at this
  exact this

/-- **Theorem 12.1.2 (i)**, (12.5) (MT p. 290): for a weak Feller chain without an invariant
probability, `K_ε(x, C) → 0` as `ε ↑ 1`, uniformly in `x`, for every compact `C`. -/
theorem theorem_12_1_2_i_resolvent {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (hno : ¬ ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π) {C : Set X}
    (hC : IsCompact C) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ e in 𝓝[<] 1, ∀ x, resolvent P e x C ≤ ε := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_forall, not_le] at h
  set S := {e : ℝ≥0∞ | ∃ x, ε < resolvent P e x C}
  have hS : ∃ᶠ e in 𝓝[<] (1 : ℝ≥0∞), e ∈ S := h
  have hF : (𝓝[<] (1 : ℝ≥0∞) ⊓ 𝓟 S).NeBot := frequently_iff_neBot.1 hS
  obtain ⟨e₀, x₀, hx₀⟩ := hS.exists
  have hx : ∀ e, ∃ x, e ∈ S → ε < resolvent P e x C := fun e => by
    by_cases he : e ∈ S
    · obtain ⟨x, hx⟩ := he; exact ⟨x, fun _ => hx⟩
    · exact ⟨x₀, fun h => absurd h he⟩
  choose xs hxs using hx
  set U := Ultrafilter.of (𝓝[<] (1 : ℝ≥0∞) ⊓ 𝓟 S)
  have hUle : (U : Filter ℝ≥0∞) ≤ 𝓝[<] 1 ⊓ 𝓟 S := Ultrafilter.of_le _
  set μs : ℝ≥0∞ → Measure X := fun e => resolvent P e (xs e)
  have hμ : ∀ e, μs e univ ≤ 1 := fun e => resolvent_univ_le P e (xs e)
  obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hC
  have hε1 : ε < 1 :=
    hx₀.trans_le ((measure_mono (subset_univ C)).trans (resolvent_univ_le P e₀ x₀))
  have hpos : ∀ᶠ e in 𝓝[<] (1 : ℝ≥0∞), 0 < e ∧ e < 1 := by
    filter_upwards [self_mem_nhdsWithin, inter_mem_nhdsWithin (Iio 1)
      (Ioi_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))] with e he1 he0
    exact ⟨he0.2, he1⟩
  refine hno (exists_isInvariant_of_vague hP μs hμ U (fun g => ?_)
    (f := f) (δ := ε.toReal) (ENNReal.toReal_pos hε.ne' (ne_top_of_lt hε1)) ?_)
  · obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc g
    refine (squeeze_zero_norm' ?_ (tendsto_resolvent_bound B)).mono_left
      (hUle.trans inf_le_left)
    filter_upwards [hpos] with e he
    rw [Real.norm_eq_abs]
    exact abs_integral_kfunR_resolvent_sub_le P he.1 he.2 (xs e) g.continuous.measurable hB
  · filter_upwards [hUle (mem_inf_of_right (mem_principal_self S))] with e he
    have := isFiniteMeasure_of_univ_le (hμ e)
    refine le_trans ?_ (measureReal_le_integral_of_indicator_le hC.measurableSet
      (f.integrable) hfC)
    rw [measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hxs e he).le

/-- **Theorem 12.1.2 (ii)** (MT p. 290): a weak Feller chain that is bounded in probability on
average admits an invariant probability. -/
theorem theorem_12_1_2_ii [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (hb : IsBoundedInProbabilityOnAverage P) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π := by
  by_contra hno
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨C, hC, hlim⟩ := hb x 2⁻¹ (by simp)
  have hev := theorem_12_1_2_i hP hno hC (ε := 4⁻¹) (by simp)
  have h1 : atTop.liminf (fun k : ℕ => cesaroKernel P k x C) ≤ 4⁻¹ :=
    liminf_le_of_frequently_le' (hev.mono fun n hn => hn x).frequently
  rw [ENNReal.one_sub_inv_two] at hlim
  have h2 := hlim.trans h1
  rw [ENNReal.inv_le_inv] at h2
  norm_num at h2

/-- **Theorem 12.0.1 (i)** (MT p. 289): a weak Feller chain bounded in probability on average has
an invariant probability (this is Theorem 12.1.2 (ii)). -/
theorem theorem_12_0_1_i [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (hb : IsBoundedInProbabilityOnAverage P) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π :=
  theorem_12_1_2_ii hP hb

/-- The contrapositive form of Theorem 12.1.2 (i) used repeatedly in the chapter: if
`P̄ⁿ(x, C) ≥ δ > 0` for infinitely many `n`, for one `x` and one compact `C`, then an invariant
probability exists. -/
theorem exists_isInvariant_of_frequently {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsWeakFeller P) {C : Set X} (hC : IsCompact C) {x : X} {δ : ℝ≥0∞} (hδ : 0 < δ)
    (h : ∃ᶠ n in atTop, δ ≤ cesaroKernel P n x C) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π := by
  by_contra hno
  have hev := theorem_12_1_2_i hP hno hC (ε := δ / 2) (ENNReal.half_pos hδ.ne')
  obtain ⟨n, hn1, hn2⟩ := (h.and_eventually hev).exists
  have hδ1 : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (hn1.trans ((measure_mono (subset_univ C)).trans (cesaroKernel_univ_le P n x)))
  exact absurd (hn1.trans (hn2 x)) (not_le.2 (ENNReal.half_lt_self hδ.ne' hδ1))

/-! ### Proposition 12.1.3 -/

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [SigmaCompactSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `∫ V dP̄ⁿ(x) = n⁻¹ Σ_{k=1}^{n} E_x[V(Φₖ)]`. -/
theorem lintegral_cesaroKernel (P : Kernel X X) (n : ℕ) (x : X) (V : X → ℝ≥0∞) :
    ∫⁻ y, V y ∂cesaroKernel P n x = (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, ∫⁻ y, V y ∂(P ^ i) x := by
  rw [cesaroKernel_apply_eq, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] [SigmaCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Markov's inequality for a coercive `V`: if `∫ V dμ ≤ M` for a probability `μ`, then the
compact set `closure {V ≤ 2M + 1}` has `μ`-measure at least `1/2`. -/
theorem half_le_measure_closure_sublevel {μ : Measure X} [IsProbabilityMeasure μ] {V : X → ℝ≥0}
    (hVm : Measurable V) {M : ℝ≥0} (hM : ∫⁻ y, (V y : ℝ≥0∞) ∂μ ≤ M) :
    2⁻¹ ≤ μ (closure {y | V y ≤ 2 * M + 1}) := by
  set r : ℝ≥0 := 2 * M + 1
  have hr : (0 : ℝ≥0∞) < r := by positivity
  have hmk : μ {y | (r : ℝ≥0∞) ≤ V y} ≤ (∫⁻ y, (V y : ℝ≥0∞) ∂μ) / r :=
    meas_ge_le_lintegral_div hVm.coe_nnreal_ennreal.aemeasurable hr.ne' ENNReal.coe_ne_top
  have hbig : μ {y | (r : ℝ≥0∞) ≤ V y} ≤ 2⁻¹ := by
    refine hmk.trans ?_
    rw [ENNReal.div_le_iff hr.ne' ENNReal.coe_ne_top]
    calc ∫⁻ y, (V y : ℝ≥0∞) ∂μ ≤ M := hM
      _ ≤ 2⁻¹ * r := by
          rw [show (r : ℝ≥0∞) = 2 * M + 1 by simp [r]]
          rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
          exact le_self_add
  have hsub : {y | (r : ℝ≥0∞) ≤ V y}ᶜ ⊆ closure {y | V y ≤ r} := fun y hy => by
    simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hy
    exact subset_closure (show V y ≤ r from by exact_mod_cast hy.le)
  have hm : MeasurableSet {y | (r : ℝ≥0∞) ≤ V y} :=
    measurableSet_le measurable_const hVm.coe_nnreal_ennreal
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - μ {y | (r : ℝ≥0∞) ≤ V y} := tsub_le_tsub_left hbig 1
    _ = μ {y | (r : ℝ≥0∞) ≤ V y}ᶜ := (prob_compl_eq_one_sub hm).symm
    _ ≤ μ (closure {y | V y ≤ r}) := measure_mono hsub

/-- **Proposition 12.1.3** (MT p. 291), in the Cesàro form that Theorem 12.1.2 supports: for a
weak Feller chain and a coercive `V`, if the Cesàro means of `E_x[V(Φₖ)]` have finite `liminf` for
one `x`, `liminf_n n⁻¹ Σ_{k=1}^{n} E_x[V(Φₖ)] < ∞`, then an invariant probability exists. -/
theorem proposition_12_1_3 {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    {V : X → ℝ≥0} (hVm : Measurable V) (hV : IsCoercive V) {x : X}
    (hx : atTop.liminf (fun n : ℕ => ∫⁻ y, (V y : ℝ≥0∞) ∂cesaroKernel P n x) < ∞) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, atTop.liminf
      (fun n : ℕ => ∫⁻ y, (V y : ℝ≥0∞) ∂cesaroKernel P n x) < M := by
    obtain ⟨M, hM, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hx
    exact ⟨M, hM⟩
  have hfr := frequently_lt_of_liminf_lt (by isBoundedDefault) hM
  refine exists_isInvariant_of_frequently hP (hV (2 * M + 1)) (x := x) (δ := 2⁻¹) (by simp) ?_
  refine (hfr.and_eventually (eventually_ge_atTop 1)).mono fun n hn => ?_
  have := isMarkovKernel_cesaroKernel P hn.2
  exact half_le_measure_closure_sublevel hVm hn.1.le

/-- **Proposition 12.1.3** with the condition of Lemma D.5.3 (MT p. 291): for a weak Feller chain
and a coercive `V` with `E_x[V(Φₖ)] ≤ M` for all large `k`, an invariant probability exists. -/
theorem proposition_12_1_3_of_eventually_le {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsWeakFeller P) {V : X → ℝ≥0} (hVm : Measurable V) (hV : IsCoercive V) {x : X}
    {M : ℝ≥0} (hx : ∀ᶠ k in atTop, ∫⁻ y, (V y : ℝ≥0∞) ∂(P ^ k) x ≤ M) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π := by
  have := isMarkovKernel_pow P
  set C := closure {y | V y ≤ 2 * M + 1}
  have hCm : MeasurableSet C := isClosed_closure.measurableSet
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx
  have hk : ∀ k, N ≤ k → 2⁻¹ ≤ (P ^ k) x C := fun k hk =>
    half_le_measure_closure_sublevel hVm (hN k hk)
  have hlim : (2⁻¹ : ℝ≥0∞) ≤ atTop.liminf fun n : ℕ => cesaroKernel P n x C := by
    have h1 := le_liminf_cesaro (fun i => (P ^ i) x C) fun i => prob_le_one
    simp_rw [cesaroKernel_apply P _ x hCm]
    refine le_trans ?_ h1
    exact le_liminf_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨N, hk⟩)
  have hfr : ∃ᶠ n in atTop, 4⁻¹ ≤ cesaroKernel P n x C := by
    have h4 : (4⁻¹ : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_lt_inv.2 (by norm_num)
    exact (eventually_lt_of_lt_liminf (h4.trans_le hlim)).frequently.mono fun n hn => hn.le
  exact exists_isInvariant_of_frequently hP (hV (2 * M + 1)) (by simp) hfr

/-! ### Proposition 12.1.4 -/

omit [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] in
/-- A sequence of probability measures that is tight in the sense (12.1),
`liminf_n μₙ(C) ≥ 1 − ε` for some compact `C`, is tight: the finitely many measures before the
`liminf` takes effect are each tight on a σ-compact space. -/
theorem isTightMeasureSet_range_of_liminf [OpensMeasurableSpace X] (μ : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set X, IsCompact C ∧ 1 - ε ≤ atTop.liminf fun n => μ n C) :
    IsTightMeasureSet (range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases le_or_gt 1 ε with h1 | h1
  · exact ⟨∅, isCompact_empty, by rintro _ ⟨n, rfl⟩; exact prob_le_one.trans h1⟩
  obtain ⟨C, hC, hlim⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  have hlt : 1 - ε < 1 - ε / 2 :=
    (ENNReal.cancel_of_ne (by finiteness)).tsub_lt_tsub_left_of_le h1.le
      (ENNReal.half_lt_self hε.ne' (ne_top_of_lt h1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf (hlt.trans_le hlim))
  have hsmall : ∀ n : ℕ, ∃ K : Set X, IsCompact K ∧ μ n Kᶜ ≤ ε := fun n => by
    let Kx : CompactExhaustion X := CompactExhaustion.choice X
    have ht := tendsto_measure_iInter_atTop (μ := μ n) (s := fun m => (Kx m)ᶜ)
      (fun m => (Kx.isCompact m).measurableSet.compl.nullMeasurableSet)
      (fun a b hab => compl_subset_compl.2 (Kx.subset hab)) ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ m, (Kx m)ᶜ) = ∅ := by rw [← compl_iUnion, Kx.iUnion_eq, compl_univ]
    rw [hempty, measure_empty] at ht
    obtain ⟨m, hm⟩ := (ht.eventually (Iic_mem_nhds hε)).exists
    exact ⟨Kx m, Kx.isCompact m, hm⟩
  choose K hK hKε using hsmall
  refine ⟨C ∪ ⋃ n ∈ Finset.range N, K n,
    hC.union ((Finset.range N).isCompact_biUnion fun n _ => hK n), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · calc μ n (C ∪ ⋃ n ∈ Finset.range N, K n)ᶜ ≤ μ n Cᶜ :=
          measure_mono (compl_subset_compl.2 subset_union_left)
      _ = 1 - μ n C := prob_compl_eq_one_sub hC.measurableSet
      _ ≤ ε := by
          rw [tsub_le_iff_right, add_comm]
          exact (tsub_le_iff_right.1 (hN n hn).le)
  · calc μ n (C ∪ ⋃ n ∈ Finset.range N, K n)ᶜ ≤ μ n (K n)ᶜ :=
          measure_mono (compl_subset_compl.2 (subset_union_of_subset_right
            (subset_biUnion_of_mem (u := K) (Finset.mem_coe.2 (Finset.mem_range.2
              (not_le.1 hn)))) _))
      _ ≤ ε := hKε n

/-- `Pf` as a bounded continuous function, for a weak Feller `P`. -/
noncomputable def kfunBCF {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨kfunR P f, (proposition_6_1_1_i_weak P).1 hP f⟩
    (2 * ‖f‖) fun x y => by
      have hb : ∀ z, |kfunR P f z| ≤ ‖f‖ := abs_kfunR_le P fun z => by
        rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z
      simp only [Real.dist_eq]
      calc |kfunR P f x - kfunR P f y| ≤ |kfunR P f x| + |kfunR P f y| := abs_sub _ _
        _ ≤ 2 * ‖f‖ := by linarith [hb x, hb y]

omit [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X] in
/-- `kfunBCF hP f = Pf`. -/
theorem kfunBCF_apply {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P) (f : X →ᵇ ℝ)
    (x : X) : kfunBCF hP f x = kfunR P f x := rfl

/-- The Cesàro averages `P̄ⁿ⁺¹(x, ·)` as probability measures. -/
noncomputable def cesaroPM (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) :
    ProbabilityMeasure X :=
  ⟨cesaroKernel P (n + 1) x, by
    have := isMarkovKernel_cesaroKernel P (n := n + 1) (by omega); infer_instance⟩

/-- **Proposition 12.1.4** (MT p. 292): for a weak Feller chain bounded in probability on average
with a unique invariant probability `π`, `P̄ⁿ(x, ·) → π` weakly for every `x`. By Prokhorov's
theorem the averages lie in a compact set; every cluster point is invariant (the Cesàro
telescoping bound and the Feller property), hence equal to `π`. -/
theorem proposition_12_1_4 {P : Kernel X X} [IsMarkovKernel P] (hP : IsWeakFeller P)
    (hb : IsBoundedInProbabilityOnAverage P) {π : ProbabilityMeasure X}
    (huniq : ∀ μ : Measure X, IsProbabilityMeasure μ → IsInvariant P μ → μ = π) (x : X) :
    Tendsto (cesaroPM P x) atTop (𝓝 π) := by
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ range (cesaroPM P x)} := by
    have : {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ range (cesaroPM P x)} =
        range fun n => cesaroKernel P (n + 1) x := by
      ext ν
      simp only [mem_ofPred_eq, mem_range, exists_exists_eq_and]
      rfl
    rw [this]
    have := fun n => isMarkovKernel_cesaroKernel P (n := n + 1) (by omega)
    refine isTightMeasureSet_range_of_liminf _ fun ε hε => ?_
    obtain ⟨C, hC, hlim⟩ := hb x ε hε
    refine ⟨C, hC, hlim.trans_eq ?_⟩
    exact (Filter.liminf_nat_add (fun k => cesaroKernel P k x C) 1).symm
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure (mem_range_self n)) fun ν _ hν => ?_
  obtain ⟨U, hU, hUt⟩ := mapClusterPt_iff_ultrafilter.1 hν
  have hw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hUt
  refine Subtype.ext (huniq ν inferInstance ?_)
  unfold IsInvariant
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_comp_measure P _ (f.integrable _)]
  have h1 := hw (kfunBCF hP f)
  have h2 := hw f
  have hdiff : Tendsto (fun n => ∫ y, kfunBCF hP f y ∂(cesaroPM P x n : Measure X) -
      ∫ y, f y ∂(cesaroPM P x n : Measure X)) (U : Filter ℕ) (𝓝 0) := by
    refine (squeeze_zero_norm (fun n => ?_) ((tendsto_const_div_atTop_nhds_zero_nat
      (2 * ‖f‖)).comp (tendsto_add_atTop_nat 1))).mono_left hU
    rw [Real.norm_eq_abs]
    have := abs_integral_kfunR_cesaro_sub_le P (n + 1) x f.continuous.measurable
      (B := ‖f‖) fun y => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y
    refine (le_of_eq rfl).trans (this.trans (le_of_eq ?_))
    simp [Function.comp]
  have h3 := h2.add hdiff
  simp only [add_sub_cancel, add_zero] at h3
  exact tendsto_nhds_unique h1 h3

/-! ### The inequality (12.3) and the successor chain -/

/-- The deterministic successor chain `n ↦ n + 1` on `ℕ` (a counterexample chain). -/
noncomputable def succKernel : Kernel ℕ ℕ := Kernel.deterministic (· + 1) (measurable_from_top)

/-- The successor chain is a transition kernel. -/
theorem isMarkovKernel_succKernel : IsMarkovKernel succKernel := by
  unfold succKernel; infer_instance

/-- `Pʲ(x, ·) = δ_{x + j}` for the successor chain. -/
theorem succKernel_pow_apply (j x : ℕ) : (succKernel ^ j) x = Measure.dirac (x + j) := by
  induction j generalizing x with
  | zero => rw [pow_zero_apply, add_zero]
  | succ j ih =>
    have h1 : succKernel x = Measure.dirac (x + 1) := Kernel.deterministic_apply _ _
    rw [Kernel.pow_add, pow_one, Kernel.comp_apply, h1, Measure.dirac_bind (Kernel.measurable _),
      ih, add_comm j 1, add_assoc]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] [SigmaCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **The inequality (12.3)** (MT p. 289): `P_x{Φⱼ ∈ C for some j ≥ n} ≥ Pⁿ(x, C)`. -/
theorem inequality_12_3 (P : Kernel X X) [IsMarkovKernel P] {C : Set X} (hC : MeasurableSet C)
    (x : X) (n : ℕ) :
    (P ^ n) x C ≤ pathKernel P x (⋃ j, ⋃ (_ : n ≤ j), {ω : ℕ → X | ω j ∈ C}) := by
  rw [← pathKernel_coord_mem P x n hC]
  exact measure_mono (subset_iUnion₂_of_subset n le_rfl subset_rfl)

end MeynTweedie.InvarianceTightness
