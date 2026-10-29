/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleLILTools

/-!
# The upper half of the LIL for martingale differences

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLILUpper.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

For martingale differences `Dⱼ` (`𝓕ⱼ₊₁`-measurable, `E[Dⱼ | 𝓕ⱼ] = 0`) that are identically
distributed and square integrable, with `(1/n) Σ_{j<n} E[Dⱼ² | 𝓕ⱼ] → σ² = E[D₀²]` almost surely,
almost surely `Σ_{j<n} Dⱼ ≤ (σ + ε) √(2 n log log n)` eventually, for every `ε > 0`
(`martingale_lil_upper`). This is the upper half of the Hartman–Wintner LIL for martingales
(Stout, *Ann. Math. Statist.* 41 (1970); Stout, *Almost Sure Convergence* (1974), §5.4). Its
hypotheses hold for the Poisson martingale `Mₙ(g)` (17.43) under `P_π` (MT p. 448), which gives
the LIL of MT Theorems 17.0.1 (iv), 17.5.3 and 17.5.4 without a minorization
(`MartingaleLILChains`).

The proof follows the i.i.d. upper half (`LILUpper`). The differences are truncated at
`τⱼ = δ √(j / log log j)` and recentred by their conditional means (`truncMD`). For the bounded
part, `exp(λ S'ₙ − λ²(1 + 2λτ_N) Wₙ/2)` with `Wₙ = Σ_{j<n} E[Dⱼ² | 𝓕ⱼ]` is a supermartingale up
to the time `W` passes the level `s² N`; Ville's inequality bounds
`P(W_N ≤ s² N, max_{n ≤ N} S'ₙ ≥ t)` (`measureReal_upper_block_le`), and the bound is summable
along `N = ⌊θ^{k+1}⌋`. The event `W_N > s² N`, `s > σ`, happens only finitely often by the
hypothesis on the conditional variances. The truncated tails and the conditional means are
`o(√(n log log n))` by Kronecker's lemma, as in the i.i.d. case.

* `sum_condVarMD_mono`, `measurable_sum_condVarMD`: the running conditional variance.
* `ae_tendsto_sum_sub_truncMD`: the truncation error is `o(√(n log log n))` almost surely.
* `martingale_lil_hyps_neg`, `martingale_lil_upper_neg`: the same for `−Dⱼ`, that is,
  `−Σ_{j<n} Dⱼ ≤ (σ + ε) √(2 n log log n)` eventually.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The running conditional variance `Wₙ = Σ_{j<n} E[Dⱼ² | 𝓕ⱼ]` is monotone in `n`. -/
theorem sum_condVarMD_mono (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {m n : ℕ}
    (hmn : m ≤ n) (ω : Ω) :
    ∑ j ∈ Finset.range m, condVarMD Q ℱ D j ω ≤ ∑ j ∈ Finset.range n, condVarMD Q ℱ D j ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn)
    fun j _ _ => condVarMD_nonneg Q ℱ D j ω

/-- `W_{j+1} = Σ_{i ≤ j} E[Dᵢ² | 𝓕ᵢ]` is `𝓕ⱼ`-measurable. -/
theorem measurable_sum_condVarMD (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (j : ℕ) : Measurable[ℱ j] fun ω => ∑ i ∈ Finset.range (j + 1), condVarMD Q ℱ D i ω :=
  Finset.measurable_sum _ fun i hi =>
    (measurable_condVarMD Q ℱ D i).mono (ℱ.mono (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))
      le_rfl

/-- **The block estimate of the upper half** (the exponential supermartingale and Ville's
inequality): for truncation levels `0 ≤ βⱼ` increasing, `b ≥ 0`, `0 ≤ λ` and `2λβ_N ≤ 1`,
`P(W_N ≤ b, max_{n ≤ N} S'ₙ ≥ t) ≤ exp(−λt + λ²(1 + 2λβ_N) b/2)`, where `S'ₙ` are the partial
sums of the truncated differences `truncMD` and `W_N = Σ_{j<N} E[Dⱼ² | 𝓕ⱼ]`. -/
theorem measureReal_upper_block_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) {β : ℕ → ℝ} (hβ0 : ∀ j, 0 ≤ β j) (hβm : Monotone β) (N : ℕ)
    {b l t : ℝ} (hb : 0 ≤ b) (hl : 0 ≤ l) (hlc : l * (2 * β N) ≤ 1) :
    Q.real {ω | ∑ j ∈ Finset.range N, condVarMD Q ℱ D j ω ≤ b ∧
        ∃ n ≤ N, t ≤ ∑ j ∈ Finset.range n, truncMD Q ℱ D β j ω} ≤
      Real.exp (-(l * t) + l ^ 2 * (1 + l * (2 * β N)) / 2 * b) := by
  set v := condVarMD Q ℱ D with hv
  set c := 2 * β N with hc
  have hc0 : 0 ≤ c := by have := hβ0 N; positivity
  set A : ℕ → Set Ω := fun j => {_ω | j < N} ∩ {ω | ∑ i ∈ Finset.range (j + 1), v i ω ≤ b}
    with hA
  have hAm : ∀ j, MeasurableSet[ℱ j] (A j) := fun j =>
    (MeasurableSet.const _).inter (measurable_sum_condVarMD Q ℱ D j measurableSet_Iic)
  set X : ℕ → Ω → ℝ := fun j => (A j).indicator (truncMD Q ℱ D β j) with hX
  set u : ℕ → Ω → ℝ := fun j => (A j).indicator (v j) with hu
  have hbmd : IsBddMartDiff Q ℱ X u c b := {
    meas_X := fun j => (measurable_truncMD Q hD β j).indicator
      (ℱ.mono (Nat.le_succ j) _ (hAm j))
    meas_u := fun j => (measurable_condVarMD Q ℱ D j).indicator (hAm j)
    abs_X_le := fun j ω => by
      by_cases hω : ω ∈ A j
      · simp only [hX]; rw [indicator_of_mem hω]
        exact (abs_truncMD_le Q ℱ D hβ0 j ω).trans (by
          have := hβm hω.1.le; rw [hc]; linarith)
      · simp only [hX]; rw [indicator_of_notMem hω, abs_zero]; exact hc0
    u_nonneg := fun j ω => by
      by_cases hω : ω ∈ A j
      · simp only [hu]; rw [indicator_of_mem hω]; exact condVarMD_nonneg Q ℱ D j ω
      · simp only [hu]; rw [indicator_of_notMem hω]
    u_le := fun j ω => by
      by_cases hω : ω ∈ A j
      · simp only [hu]; rw [indicator_of_mem hω]
        refine le_trans ?_ hω.2
        rw [Finset.sum_range_succ]
        have : 0 ≤ ∑ i ∈ Finset.range j, v i ω :=
          Finset.sum_nonneg fun i _ => condVarMD_nonneg Q ℱ D i ω
        linarith
      · simp only [hu]; rw [indicator_of_notMem hω]; exact hb
    orth := fun j F C hFm hFb => by
      have e : (fun ω => F ω * X j ω) = fun ω => (A j).indicator F ω * truncMD Q ℱ D β j ω := by
        ext ω
        by_cases hω : ω ∈ A j
        · simp only [hX]; rw [indicator_of_mem hω, indicator_of_mem hω]
        · simp only [hX]; rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero, zero_mul]
      rw [e]
      refine integral_mul_truncMD hD hβ0 j (hFm.indicator (hAm j)) (C := C) fun ω => ?_
      by_cases hω : ω ∈ A j
      · rw [indicator_of_mem hω]; exact hFb ω
      · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hFb ω) }
  have hvar : IsVarLe Q ℱ X u := by
    intro j F C hFm hF0 hFb
    have e1 : (fun ω => F ω * X j ω ^ 2) =
        fun ω => (A j).indicator F ω * truncMD Q ℱ D β j ω ^ 2 := by
      ext ω
      by_cases hω : ω ∈ A j
      · simp only [hX]; rw [indicator_of_mem hω, indicator_of_mem hω]
      · simp only [hX]; rw [indicator_of_notMem hω, indicator_of_notMem hω]; ring
    have e2 : (fun ω => F ω * u j ω) = fun ω => (A j).indicator F ω * v j ω := by
      ext ω
      by_cases hω : ω ∈ A j
      · simp only [hu]; rw [indicator_of_mem hω, indicator_of_mem hω]
      · simp only [hu]; rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero, zero_mul]
    rw [e1, e2]
    refine integral_mul_truncMD_sq_le hD hL2 hβ0 j (hFm.indicator (hAm j)) (C := C)
      (fun ω => ?_) fun ω => ?_
    · by_cases hω : ω ∈ A j
      · rw [indicator_of_mem hω]; exact hF0 ω
      · rw [indicator_of_notMem hω]
    · by_cases hω : ω ∈ A j
      · rw [indicator_of_mem hω]; exact hFb ω
      · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hFb ω)
  -- the supermartingale
  set κ := l ^ 2 * (1 + l * c) / 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set M : ℕ → Ω → ℝ := fun n ω => Real.exp (l * ∑ j ∈ Finset.Ico 0 n, X j ω -
    κ * ∑ j ∈ Finset.Ico 0 n, u j ω) with hM
  have hMm : ∀ n, Measurable[ℱ n] (M n) := fun n =>
    Real.continuous_exp.measurable.comp (((measurable_sum_Ico hbmd.meas_X 0 n).const_mul l).sub
      ((measurable_sum_Ico (fun j => (hbmd.meas_u j).mono (ℱ.mono (Nat.le_succ j)) le_rfl) 0
        n).const_mul κ))
  have hM0 : ∀ n ω, 0 ≤ M n ω := fun n ω => (Real.exp_pos _).le
  have hMb : ∀ n ω, |M n ω| ≤ Real.exp (l * ((n - 0 : ℕ) * c)) := fun n ω => by
    rw [hM, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h1 := (abs_le.1 (abs_sum_Ico_le hbmd.abs_X_le 0 n ω)).2
    have h2 : 0 ≤ ∑ j ∈ Finset.Ico 0 n, u j ω := Finset.sum_nonneg fun j _ => hbmd.u_nonneg j ω
    nlinarith [mul_nonneg hκ0 h2]
  have hMi : ∀ n, Integrable (M n) Q := fun n =>
    integrable_of_abs_le ((hMm n).mono (ℱ.le n) le_rfl) (hMb n)
  have hsup : ∀ n (B : Set Ω), MeasurableSet[ℱ n] B →
      ∫ ω in B, M (n + 1) ω ∂Q ≤ ∫ ω in B, M n ω ∂Q := fun n B hB => by
    have h := hbmd.integral_exp_succ_le (Q := Q) hvar hc0 hl hlc le_rfl (Nat.zero_le n)
      (F := B.indicator fun _ => (1 : ℝ)) (C := 1) (measurable_const.indicator hB)
      (fun ω => by
        by_cases hω : ω ∈ B
        · rw [indicator_of_mem hω]; exact zero_le_one
        · rw [indicator_of_notMem hω])
      (fun ω => by
        by_cases hω : ω ∈ B
        · rw [indicator_of_mem hω, abs_one]
        · rw [indicator_of_notMem hω, abs_zero]; exact zero_le_one)
    rw [integral_indicator_one_mul (ℱ.le n _ hB), integral_indicator_one_mul (ℱ.le n _ hB)] at h
    exact h
  have hville := measureReal_exists_ge_le hMm hM0 hMi hsup (Real.exp (l * t - κ * b)) N
  have hM00 : ∫ ω, M 0 ω ∂Q = 1 := by
    simp only [hM, Finset.Ico_self, Finset.sum_empty, mul_zero, sub_zero, Real.exp_zero,
      integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [hM00] at hville
  -- the event of the block lies in the Ville event
  have hsub : {ω | ∑ j ∈ Finset.range N, v j ω ≤ b ∧
      ∃ n ≤ N, t ≤ ∑ j ∈ Finset.range n, truncMD Q ℱ D β j ω} ⊆
      {ω | ∃ n ≤ N, Real.exp (l * t - κ * b) ≤ M n ω} := by
    rintro ω ⟨hW, n, hnN, htn⟩
    refine ⟨n, hnN, Real.exp_le_exp.2 ?_⟩
    have hAj : ∀ j < N, ω ∈ A j := fun j hj => ⟨hj, (sum_condVarMD_mono Q ℱ D
      (show j + 1 ≤ N by omega) ω).trans hW⟩
    have e1 : ∑ j ∈ Finset.Ico 0 n, X j ω = ∑ j ∈ Finset.range n, truncMD Q ℱ D β j ω := by
      rw [← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hX]; rw [indicator_of_mem (hAj j (by have := Finset.mem_range.1 hj; omega))]
    have e2 : ∑ j ∈ Finset.Ico 0 n, u j ω = ∑ j ∈ Finset.range n, v j ω := by
      rw [← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hu]; rw [indicator_of_mem (hAj j (by have := Finset.mem_range.1 hj; omega))]
    rw [e1, e2]
    have h3 : ∑ j ∈ Finset.range n, v j ω ≤ b := (sum_condVarMD_mono Q ℱ D hnN ω).trans hW
    have h4 := mul_le_mul_of_nonneg_left htn hl
    have h5 := mul_le_mul_of_nonneg_left h3 hκ0
    linarith
  have h6 := measureReal_mono (μ := Q) hsub
  have h7 : 0 < Real.exp (l * t - κ * b) := Real.exp_pos _
  have h8 : Q.real {ω | ∃ n ≤ N, Real.exp (l * t - κ * b) ≤ M n ω} ≤
      Real.exp (-(l * t) + κ * b) := by
    rw [show -(l * t) + κ * b = -(l * t - κ * b) by ring, Real.exp_neg,
      inv_eq_one_div, le_div_iff₀' h7]
    exact hville
  exact h6.trans h8

/-- **The truncated tails are negligible**: for martingale differences that are identically
distributed and square integrable, and the truncation levels `τⱼ = lilTruncLevel δ j₀ j`,
almost surely `(Σ_{j<n} Dⱼ − Σ_{j<n} truncMDⱼ) / √(2 n log log n) → 0` (Kronecker's lemma, as in
the i.i.d. case). -/
theorem ae_tendsto_sum_sub_truncMD {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q) {δ : ℝ} (hδ0 : 0 < δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => (∑ j ∈ Finset.range n, D j ω -
      ∑ j ∈ Finset.range n, truncMD Q ℱ D (lilTruncLevel δ j₀) j ω) / lilScale n) atTop
        (𝓝 0) := by
  set β : ℕ → ℝ := lilTruncLevel δ j₀ with hβ
  have hβ0 : ∀ j, 0 ≤ β j := lilTruncLevel_nonneg hδ0.le j₀
  have hDm : ∀ j, Measurable (D j) := fun j => (hD j).measurable.mono (ℱ.le _) le_rfl
  have hDL2 : ∀ j, MemLp (D j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  have hDi : ∀ j, Integrable (D j) Q := fun j => (hDL2 j).integrable one_le_two
  have hTi : ∀ j i, Integrable (fun ω => lilTrunc (β j) (D i ω)) Q := fun j i =>
    integrable_of_abs_le ((measurable_lilTrunc _).comp (hDm i)) fun ω =>
      abs_lilTrunc_le (hβ0 j) _
  set Y : ℕ → Ω → ℝ := truncMD Q ℱ D β with hY
  -- the tails and Kronecker's lemma
  set w : ℕ → ℝ := lilWeight j₀ with hw
  set e : ℕ → ℝ := fun j => ∫ ω, |D 0 ω - lilTrunc (β j) (D 0 ω)| ∂Q with he
  set A : ℕ → Ω → ℝ := fun j ω => |D j ω - lilTrunc (β j) (D j ω)| +
    |truncMean Q ℱ D β j ω| with hA
  have hDti : ∀ j i, Integrable (fun ω => |D i ω - lilTrunc (β j) (D i ω)|) Q := fun j i =>
    ((hDi i).sub (hTi j i)).abs
  have hDeq : ∀ j, ∫ ω, |D j ω - lilTrunc (β j) (D j ω)| ∂Q = e j := fun j =>
    ((hident j).comp (u := fun x => |x - lilTrunc (β j) x|)
      (continuous_abs.measurable.comp (measurable_id.sub (measurable_lilTrunc _)))).integral_eq
  have he0 : ∀ j, 0 ≤ e j := fun j => integral_nonneg fun ω => abs_nonneg _
  have hmi : ∀ j, Integrable (fun ω => |truncMean Q ℱ D β j ω|) Q := fun j =>
    integrable_of_abs_le (continuous_abs.measurable.comp
      ((measurable_truncMean Q ℱ D β j).mono (ℱ.le j) le_rfl)) (C := β j) fun ω => by
        rw [abs_abs]; exact abs_truncMean_le Q ℱ D hβ0 j ω
  have hAi : ∀ j, Integrable (A j) Q := fun j => (hDti j j).add (hmi j)
  have hAint : ∀ j, ∫ ω, A j ω ∂Q ≤ 2 * e j := fun j => by
    have h1 := integral_abs_truncMean_le (Q := Q) hD hDi h0 hβ0 j
    rw [hDeq] at h1
    have e3 : ∫ ω, A j ω ∂Q = e j + ∫ ω, |truncMean Q ℱ D β j ω| ∂Q := by
      simp only [hA]
      rw [integral_add (hDti j j) (hmi j), hDeq]
    rw [e3]
    linarith
  have hA0 : ∀ j ω, 0 ≤ A j ω := fun j ω => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsumA : Summable fun j => ∫ ω, A j ω / w j ∂Q := by
    have h2 := (summable_tail_div_lilWeight (hDm 0) hL2 hδ0 hj₀).mul_left 2
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω =>
      div_nonneg (hA0 j ω) (lilWeight_pos hj₀ j).le) (fun j => ?_) h2
    rw [integral_div]
    have := hAint j
    have hwj := lilWeight_pos hj₀ j
    rw [div_le_iff₀ hwj]
    have e2 : 2 * ((∫ ω, |D 0 ω - lilTrunc (lilTruncLevel δ j₀ j) (D 0 ω)| ∂Q) /
        lilWeight j₀ j) * w j = 2 * e j := by
      rw [hw, he]; field_simp; rfl
    rw [e2]
    exact this
  have hAm : ∀ j, Measurable fun ω => A j ω / w j := fun j =>
    ((continuous_abs.measurable.comp ((hDm j).sub ((measurable_lilTrunc _).comp
      (hDm j)))).add (continuous_abs.measurable.comp
        ((measurable_truncMean Q ℱ D β j).mono (ℱ.le j) le_rfl))).div_const _
  have hKr := ae_summable_of_summable_integral hAm
    (fun j ω => div_nonneg (hA0 j ω) (lilWeight_pos hj₀ j).le)
    (fun j => (hAi j).div_const _) hsumA
  filter_upwards [hKr] with ω hωK
  have hW := tendsto_sum_div_of_summable (a := fun j => A j ω) (w := w)
    (fun j => hA0 j ω) (lilWeight_pos hj₀) (lilWeight_mono hj₀) tendsto_lilWeight hωK
  refine squeeze_zero_norm' ?_ hW
  filter_upwards [eventually_ge_atTop j₀] with n hnj
  have hdiff : |∑ j ∈ Finset.range n, D j ω - ∑ j ∈ Finset.range n, Y j ω| ≤
      ∑ j ∈ Finset.range n, A j ω := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have e1 : D j ω - Y j ω = (D j ω - lilTrunc (β j) (D j ω)) + truncMean Q ℱ D β j ω := by
      simp only [hY, truncMD]; ring
    rw [e1]
    exact abs_add_le _ _
  have hwl : w n ≤ lilScale n := by
    rw [lilScale_eq_lilWeight hnj]
    have h1 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h2 := (lilWeight_pos hj₀ n).le
    nlinarith
  have hwn := lilWeight_pos hj₀ n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hwn.trans_le hwl)]
  calc |∑ j ∈ Finset.range n, D j ω - ∑ j ∈ Finset.range n, Y j ω| / lilScale n
      ≤ (∑ j ∈ Finset.range n, A j ω) / lilScale n :=
        div_le_div_of_nonneg_right hdiff (hwn.trans_le hwl).le
    _ ≤ (∑ j ∈ Finset.range n, A j ω) / w n :=
        div_le_div_of_nonneg_left (Finset.sum_nonneg fun j _ => hA0 j ω) hwn hwl

/-- **The upper half of the martingale LIL** (Stout 1970): let `Dⱼ` be martingale differences
(`𝓕ⱼ₊₁`-measurable, `E[Dⱼ | 𝓕ⱼ] = 0`), identically distributed and square integrable, with
`(1/n) Σ_{j<n} E[Dⱼ² | 𝓕ⱼ] → σ² = E[D₀²]` almost surely. Then for every `ε > 0`, almost surely
`Σ_{j<n} Dⱼ ≤ (σ + ε) √(2 n log log n)` eventually. -/
theorem martingale_lil_upper {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Q, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, D j ω ≤ (√(∫ ω, D 0 ω ^ 2 ∂Q) + ε) * lilScale n := by
  set σ := √(∫ ω, D 0 ω ^ 2 ∂Q) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∫ ω, D 0 ω ^ 2 ∂Q :=
    Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)
  -- the constants
  set s := σ + ε / 2 with hs
  set a := σ + 3 * ε / 4 with ha
  have hs0 : 0 < s := by positivity
  have ha0 : 0 < a := by positivity
  set ρ := a / s with hρ
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div hs0]; linarith
  have has : a = ρ * s := by rw [hρ]; field_simp
  set θ := √ρ with hθ
  have hθ1 : 1 < θ := by
    rw [hθ, show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one hρ1
  have hθ0 : 0 < θ := by linarith
  have hθ2 : θ ^ 2 = ρ := Real.sq_sqrt (by linarith)
  set η := (1 - 1 / ρ) / 2 with hη
  have hρinv : 1 / ρ < 1 := by rw [div_lt_one (by linarith)]; exact hρ1
  have hρinv0 : 0 < 1 / ρ := by positivity
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 1 := by rw [hη]; linarith
  set p := ρ * (1 - η) with hp
  have hp1 : 1 < p := by
    have e : p = (ρ + 1) / 2 := by rw [hp, hη]; field_simp; ring
    rw [e]; linarith
  set δ := η * s ^ 2 / (2 * √2 * a) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδη : 2 * √2 * a * δ / s ^ 2 = η := by rw [hδ]; field_simp
  have hpeq : a ^ 2 / (θ ^ 2 * s ^ 2) * (1 - η) = p := by
    rw [hθ2, has, hp]; field_simp
  -- the truncation
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, 3 ≤ Real.log j₀ := (eventually_le_log 3).exists
  set β : ℕ → ℝ := lilTruncLevel δ j₀ with hβ
  have hβ0 : ∀ j, 0 ≤ β j := lilTruncLevel_nonneg hδ0.le j₀
  have hβm : Monotone β := lilTruncLevel_mono hδ0.le hj₀
  have hDm : ∀ j, Measurable (D j) := fun j => (hD j).measurable.mono (ℱ.le _) le_rfl
  have hDL2 : ∀ j, MemLp (D j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  have hDi : ∀ j, Integrable (D j) Q := fun j => (hDL2 j).integrable one_le_two
  have hTi : ∀ j i, Integrable (fun ω => lilTrunc (β j) (D i ω)) Q := fun j i =>
    integrable_of_abs_le ((measurable_lilTrunc _).comp (hDm i)) fun ω =>
      abs_lilTrunc_le (hβ0 j) _
  set Y : ℕ → Ω → ℝ := truncMD Q ℱ D β with hY
  set v : ℕ → Ω → ℝ := condVarMD Q ℱ D with hv
  -- the conditional variances grow like `σ² n`
  have hWev : ∀ᵐ ω ∂Q, ∀ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range n, v k ω ≤ s ^ 2 * n := by
    filter_upwards [hV, ae_all_iff.2 fun k => condVarMD_ae_eq Q ℱ D k] with ω hω hk
    have hω' : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, v k ω) / n) atTop (𝓝 (σ ^ 2)) := by
      rw [hσ2]
      refine hω.congr fun n => ?_
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hk k).symm
    have hlt : σ ^ 2 < s ^ 2 := pow_lt_pow_left₀ (by linarith) hσ0 two_ne_zero
    filter_upwards [hω'.eventually (eventually_lt_nhds hlt), eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hn'] at hn
    exact hn.le
  -- the geometric blocks
  set nk : ℕ → ℕ := fun k => ⌊θ ^ k⌋₊ with hnk
  have hnk_mono : Monotone nk := fun i j hij =>
    Nat.floor_mono (pow_le_pow_right₀ hθ1.le hij)
  have hnk_t : Tendsto nk atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hθ1)
  set B : ℕ → Set Ω := fun k =>
    {ω | ∑ j ∈ Finset.range (nk (k + 1)), v j ω ≤ s ^ 2 * nk (k + 1) ∧
      ∃ n ≤ nk (k + 1), a * lilScale (nk k) ≤ ∑ j ∈ Finset.range n, Y j ω} with hB
  have hBbound : ∀ᶠ k in atTop, Q.real (B k) ≤
      Real.exp (-(p * Real.log (Real.log (nk k : ℝ)))) := by
    filter_upwards [hnk_t.eventually (eventually_le_log 3), eventually_floor_pow_succ_le hθ1,
      hnk_t.eventually_ge_atTop j₀] with k hk3 hkθ hkj
    set M := nk k with hM
    set N := nk (k + 1) with hN
    have hMN : M ≤ N := hnk_mono (Nat.le_succ k)
    have hM0 : (0 : ℝ) < M := by
      have := one_le_of_three_le_log (Nat.cast_nonneg _) hk3; linarith
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hLM := one_le_loglog hk3
    have hLN : Real.log (Real.log M) ≤ Real.log (Real.log N) :=
      Real.log_le_log (by linarith) (Real.log_le_log hM0 hMN')
    obtain ⟨hlC, hexp⟩ := lil_exponent_bound (a := a) (s := s) (δ := δ) (θ := θ)
      (M := M) (N := N) (LM := Real.log (Real.log M)) (LN := Real.log (Real.log N))
      ha0 hs0 hδ0 hθ0 hM0 hMN' (by rw [hθ2] at hkθ ⊢; exact hkθ) hLM hLN
    rw [hδη] at hlC hexp
    have hexp' := hexp hη1
    rw [hpeq] at hexp'
    set t := a * √(2 * M * Real.log (Real.log M)) with ht
    set l := t / (N * s ^ 2) with hl
    have hl0 : 0 ≤ l := by positivity
    have htl : a * lilScale M = t := rfl
    have hβN : 2 * β N = 2 * (δ * √(N / Real.log (Real.log N))) := by
      rw [hβ, lilTruncLevel, max_eq_left (hkj.trans hMN), lilPhi]
    have hblock := measureReal_upper_block_le (Q := Q) hD hDL2 hβ0 hβm N
      (b := s ^ 2 * N) (l := l) (t := t) (by positivity) hl0 (by rw [hβN]; linarith)
    have e : -(l * t) + l ^ 2 * (1 + l * (2 * β N)) / 2 * (s ^ 2 * N) =
        -(l * t) + N * (l ^ 2 * s ^ 2 * (1 + l * (2 * (δ * √(N / Real.log (Real.log N))))) /
          2) := by
      rw [hβN]; ring
    rw [e] at hblock
    exact hblock.trans (Real.exp_le_exp.2 hexp')
  -- Borel–Cantelli
  have hsumB : Summable fun k => Q.real (B k) :=
    (summable_exp_neg_mul_loglog_floor_pow hθ1 hp1).of_norm_bounded_eventually_nat (by
      filter_upwards [hBbound] with k hk
      rwa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg])
  have hBC : ∀ᵐ ω ∂Q, ∀ᶠ k in atTop, ω ∉ B k :=
    ae_eventually_notMem (tsum_measure_ne_top_of_summable hsumB)
  have hTail := ae_tendsto_sum_sub_truncMD hD h0 hident hL2 hδ0 hj₀
  filter_upwards [hBC, hTail, hWev] with ω hωB hωT hωW
  have hWk : ∀ᶠ k in atTop, ∑ j ∈ Finset.range (nk (k + 1)), v j ω ≤ s ^ 2 * nk (k + 1) :=
    (hnk_t.comp (tendsto_add_atTop_nat 1)).eventually hωW
  have hW' : ∀ᶠ n in atTop, ∑ j ∈ Finset.range n, D j ω - ∑ j ∈ Finset.range n, Y j ω ≤
      ε / 4 * lilScale n := by
    filter_upwards [(Metric.tendsto_nhds.1 hωT) (ε / 4) (by positivity),
      eventually_le_log 3] with n hn hp3
    have hp := lilScale_pos hp3
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at hn
    exact (le_abs_self _).trans hn.le
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 (hωB.and hWk)
  obtain ⟨K2, hK2⟩ := eventually_atTop.1 ((hnk_t.eventually (eventually_le_log 3)).and
    (eventually_ge_atTop (K1 + 1)))
  filter_upwards [hW', eventually_gt_atTop (nk K2)] with n hnW hnK
  classical
  have hex : ∃ k, n ≤ nk (k + 1) := by
    obtain ⟨k, hk⟩ := (hnk_t.eventually_ge_atTop n).exists
    exact ⟨k, hk.trans (hnk_mono (Nat.le_succ k))⟩
  set k := Nat.find hex with hkdef
  have hkn : n ≤ nk (k + 1) := Nat.find_spec hex
  have hkK : K2 ≤ k := by
    by_contra h
    push Not at h
    have := hnk_mono (show k + 1 ≤ K2 by omega)
    omega
  have hK1k : K1 + 1 ≤ k := (hK2 K2 le_rfl).2.trans hkK
  have hnk_lt : nk k < n := by
    have h := Nat.find_min hex (show k - 1 < k by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
    omega
  have h3 : 3 ≤ Real.log (nk k : ℝ) := (hK2 k hkK).1
  -- the truncated part
  have hYbound : ∑ j ∈ Finset.range n, Y j ω < a * lilScale (nk k) := by
    obtain ⟨h1, h2⟩ := hK1 k (by omega)
    simp only [hB, mem_ofPred_eq, not_and, not_exists, not_le] at h1
    exact h1 h2 n hkn
  have hlil : lilScale (nk k) ≤ lilScale n := lilScale_mono h3 hnk_lt.le
  have hfin : a * lilScale n + ε / 4 * lilScale n = (σ + ε) * lilScale n := by
    rw [ha]; ring
  have h5 : a * lilScale (nk k) ≤ a * lilScale n := mul_le_mul_of_nonneg_left hlil ha0.le
  linarith

/-- The hypotheses of the martingale LIL pass from `Dⱼ` to `−Dⱼ`. -/
theorem martingale_lil_hyps_neg {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q))) :
    (∀ k, StronglyMeasurable[ℱ (k + 1)] (fun ω => -D k ω)) ∧
      (∀ k, Q[fun ω => -D k ω | ℱ k] =ᵐ[Q] 0) ∧
      (∀ k, IdentDistrib (fun ω => -D k ω) (fun ω => -D 0 ω) Q Q) ∧
      MemLp (fun ω => -D 0 ω) 2 Q ∧
      (∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
        Q[fun ω => (-D k ω) ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, (-D 0 ω) ^ 2 ∂Q))) := by
  refine ⟨fun k => (hD k).neg, fun k => ?_, fun k => (hident k).comp measurable_neg, hL2.neg,
    ?_⟩
  · filter_upwards [condExp_neg (μ := Q) (D k) (ℱ k), h0 k] with ω h1 h2
    change Q[-D k | ℱ k] ω = 0
    rw [h1, Pi.neg_apply, h2, Pi.zero_apply, neg_zero]
  · have e1 : ∀ k, (fun ω => (-D k ω) ^ 2) = fun ω => D k ω ^ 2 := fun k => by
      funext ω; exact neg_sq _
    simp_rw [e1]
    exact hV

/-- **The upper half of the martingale LIL for `−Sₙ`**: under the hypotheses of
`martingale_lil_upper`, almost surely `−Σ_{j<n} Dⱼ ≤ (σ + ε) √(2 n log log n)` eventually. -/
theorem martingale_lil_upper_neg {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Q, ∀ᶠ n in atTop,
      -∑ j ∈ Finset.range n, D j ω ≤ (√(∫ ω, D 0 ω ^ 2 ∂Q) + ε) * lilScale n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := martingale_lil_hyps_neg hD h0 hident hL2 hV
  have h := martingale_lil_upper h1 h2 h3 h4 h5 hε
  have e : ∫ ω, (-D 0 ω) ^ 2 ∂Q = ∫ ω, D 0 ω ^ 2 ∂Q := by simp_rw [neg_sq]
  rw [e] at h
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  rwa [Finset.sum_neg_distrib] at hn

end MeynTweedie.GeneralizedDrift
