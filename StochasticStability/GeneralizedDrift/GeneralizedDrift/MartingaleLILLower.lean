/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleLILBlock
import GeneralizedDrift.MartingaleLILUpper

/-!
# The lower half of the LIL for martingale differences

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLILLower.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

For martingale differences `Dⱼ` (`𝓕ⱼ₊₁`-measurable, `E[Dⱼ | 𝓕ⱼ] = 0`), identically distributed
and square integrable, whose conditional variances and conditional truncated second moments obey
the ergodic theorem, `(1/n) Σ_{j<n} E[Dⱼ² | 𝓕ⱼ] → σ² = E[D₀²]` and
`(1/n) Σ_{j<n} E[Dⱼ² 1{Dⱼ² ≥ K} | 𝓕ⱼ] → E[D₀² 1{D₀² ≥ K}]` almost surely, almost surely
`Σ_{j<n} Dⱼ ≥ (σ − ε) √(2 n log log n)` for infinitely many `n`, for every `ε > 0`
(`martingale_lil_lower`). With `martingale_lil_upper` this is the Hartman–Wintner LIL for
martingales (Stout, *Ann. Math. Statist.* 41 (1970); `MartingaleLIL`). The hypotheses hold for the
Poisson martingale `Mₙ(g)` (17.43) under `P_π` (`MartingaleLILChains`).

The proof is Stout's: along `nₖ = mᵏ`, the truncated martingale is run from `nₖ` until its
conditional variance reaches `Bₖ = (1 − h')σ²(n_{k+1} − nₖ)` (the blocks of `MartingaleLILBlock`).
Conditionally on `𝓕_{nₖ}`, Kolmogorov's lower exponential bound gives
`P(block sum > xₖ√Bₖ | 𝓕_{nₖ}) ≥ pₖ = ½ exp(−(1 − h')²(1 + 12h) log log n_{k+1})`, whose sum
diverges, so by the conditional Borel–Cantelli lemma the block sums exceed `xₖ√Bₖ`,
`xₖ = (1 − h')√(2 log log n_{k+1})`, infinitely often. By the ergodic hypotheses each block uses
up its budget before `n_{k+1}` for large `k`, so a block sum is `S'_T − S'_{nₖ}` with
`nₖ ≤ T ≤ n_{k+1}`; the upper half controls `S_{nₖ}` and the truncation error is
`o(√(n log log n))` (`ae_tendsto_sum_sub_truncMD`). The case `σ = 0` is the upper half for `−Dⱼ`.

* `sqrt_div_two_le_lilPhi`, `tendsto_lilTruncLevel`, `tendsto_block_avg`,
  `lilScale_mul_sqrt_le`, `tendsto_integral_sq_indicator`: deterministic and measure-theoretic
  facts.
* `lower_target_ge`, `lower_param_le`, `exists_sum_Ico_ge`, `eventually_block_budget`,
  `lower_combine`: the arithmetic of the blocks.
* `martingale_lil_lower_aux`: the case `0 < ε ≤ σ`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Deterministic facts -/

/-- `φ(x) = x / log log x ≥ √x / 2` for `x ≥ 0` with `log x ≥ 3`. -/
theorem sqrt_div_two_le_lilPhi {x : ℝ} (hx0' : 0 ≤ x) (hx : 3 ≤ Real.log x) :
    √x / 2 ≤ lilPhi x := by
  have hx1 : 1 ≤ x := one_le_of_three_le_log hx0' hx
  have hx0 : 0 < x := by linarith
  have hL1 := one_le_loglog hx
  have hsx : 0 < √x := Real.sqrt_pos.2 hx0
  -- `log log x ≤ log x ≤ 2 √x`
  have h1 : Real.log (Real.log x) ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log x by linarith); linarith
  have h2 : Real.log x ≤ 2 * √x := by
    have h3 := Real.log_le_sub_one_of_pos hsx
    have h4 : Real.log x = 2 * Real.log √x := by
      rw [← Real.log_rpow hsx, Real.rpow_two, Real.sq_sqrt hx0.le]
    linarith
  rw [lilPhi, le_div_iff₀ (by linarith)]
  have h5 : √x * √x = x := Real.mul_self_sqrt hx0.le
  nlinarith

/-- The truncation levels tend to infinity. -/
theorem tendsto_lilTruncLevel {δ : ℝ} (hδ : 0 < δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) :
    Tendsto (lilTruncLevel δ j₀) atTop atTop := by
  have h1 : Tendsto (fun j : ℕ => δ * √(√(j : ℝ) / 2)) atTop atTop :=
    ((Real.tendsto_sqrt_atTop.comp ((Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num))).const_mul_atTop hδ)
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop j₀] with j hj
  rw [lilTruncLevel, max_eq_left hj]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hδ.le
  exact sqrt_div_two_le_lilPhi (Nat.cast_nonneg _) (three_le_log_of_le hj₀ hj)

/-- **Block averages**: if `aₙ/n → A` then `(a_{m^{k+1}} − a_{m^k}) / (m^{k+1} − m^k) → A`. -/
theorem tendsto_block_avg {a : ℕ → ℝ} {A : ℝ} (ha : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 A))
    {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun k : ℕ => (a (m ^ (k + 1)) - a (m ^ k)) /
      (((m ^ (k + 1) : ℕ) : ℝ) - ((m ^ k : ℕ) : ℝ))) atTop (𝓝 A) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hpow : Tendsto (fun k : ℕ => m ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have h1 := ha.comp (hpow.comp (tendsto_add_atTop_nat 1))
  have h2 := ha.comp hpow
  have h3 := (h1.const_mul ((m : ℝ) / (m - 1))).sub (h2.const_mul (1 / ((m : ℝ) - 1)))
  have hm0 : (m : ℝ) - 1 ≠ 0 := by linarith
  have e : (m : ℝ) / (m - 1) * A - 1 / ((m : ℝ) - 1) * A = A := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, div_eq_iff hm0]; ring
  rw [e] at h3
  refine h3.congr fun k => ?_
  simp only [Function.comp_apply]
  have hk0 : (0 : ℝ) < ((m ^ k : ℕ) : ℝ) := by positivity
  have hsucc : ((m ^ (k + 1) : ℕ) : ℝ) = m * ((m ^ k : ℕ) : ℝ) := by push_cast; ring
  rw [hsucc]
  field_simp

/-- `lilScale(N) √m ≤ lilScale(mN)` once `log N ≥ 3`. -/
theorem lilScale_mul_sqrt_le {N m : ℕ} (hN : 3 ≤ Real.log N) (hm : 1 ≤ m) :
    lilScale N * √(m : ℝ) ≤ lilScale (m * N) := by
  have hN0 : (0 : ℝ) < N := by
    have := one_le_of_three_le_log (Nat.cast_nonneg _) hN; linarith
  have hmN : N ≤ m * N := Nat.le_mul_of_pos_left N (by omega)
  have hmN3 : 3 ≤ Real.log ((m * N : ℕ) : ℝ) := three_le_log_of_le hN hmN
  have hL := one_le_loglog hN
  have hLL : Real.log (Real.log N) ≤ Real.log (Real.log ((m * N : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith) (Real.log_le_log hN0 (by exact_mod_cast hmN))
  have h1 := lilScale_sq hN
  have h2 := lilScale_sq hmN3
  have h3 : (lilScale N * √(m : ℝ)) ^ 2 ≤ lilScale (m * N) ^ 2 := by
    rw [mul_pow, h1, h2, Real.sq_sqrt (Nat.cast_nonneg _)]
    have : (0 : ℝ) ≤ 2 * ((m * N : ℕ) : ℝ) := by positivity
    have h4 := mul_le_mul_of_nonneg_left hLL this
    have e : 2 * (N : ℝ) * Real.log (Real.log N) * m =
        2 * ((m * N : ℕ) : ℝ) * Real.log (Real.log N) := by push_cast; ring
    rw [e]
    linarith
  exact (pow_le_pow_iff_left₀ (mul_nonneg (lilScale_nonneg _) (Real.sqrt_nonneg _))
    (lilScale_nonneg _) two_ne_zero).1 h3

/-- The truncated second moments of an `L²` variable vanish:
`E[Z² 1{Z² ≥ K}] → 0` as `K → ∞`. -/
theorem tendsto_integral_sq_indicator {Q : Measure Ω} {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ2 : MemLp Z 2 Q) :
    Tendsto (fun K : ℕ => ∫ ω, {ω | (K : ℝ) ≤ Z ω ^ 2}.indicator (fun ω => Z ω ^ 2) ω ∂Q)
      atTop (𝓝 0) := by
  have h1 := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun K : ℕ => {ω | (K : ℝ) ≤ Z ω ^ 2}.indicator (fun ω => Z ω ^ 2))
    (f := fun _ => (0 : ℝ)) (fun ω => Z ω ^ 2)
    (fun K => ((hZm.pow_const 2).indicator (measurableSet_le measurable_const
      (hZm.pow_const 2))).aestronglyMeasurable) hZ2.integrable_sq
    (fun K => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)]
      exact Set.indicator_le_self' (fun _ _ => sq_nonneg _) ω)
    (Eventually.of_forall fun ω => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (Z ω ^ 2)
      filter_upwards [eventually_ge_atTop N] with K hK
      have : Z ω ^ 2 < K := hN.trans_le (by exact_mod_cast hK)
      rw [Set.indicator_of_notMem (show ω ∉ {ω | (K : ℝ) ≤ Z ω ^ 2} by
        simp only [mem_ofPred_eq, not_le]; exact this)])
  rw [integral_zero] at h1
  exact h1

/-- The size of the block target: with `N₁ = mN₀`,
`(1 − h')√(2 log log N₁) · √((1 − h')σ²(N₁ − N₀)) ≥ σ(1 − 3h' − 1/m) √(2 N₁ log log N₁)`. -/
theorem lower_target_ge {σ h' : ℝ} (hσ : 0 ≤ σ) (h0 : 0 ≤ h') (h1 : h' ≤ 1 / 16) {m N₀ : ℕ}
    (hm : 2 ≤ m) (hN : 3 ≤ Real.log ((m * N₀ : ℕ) : ℝ)) :
    σ * (1 - 3 * h' - 1 / m) * lilScale (m * N₀) ≤
      (1 - h') * √(2 * Real.log (Real.log ((m * N₀ : ℕ) : ℝ))) *
        √((1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀)) := by
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hL := one_le_loglog hN
  have hinvm : 1 / (m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm1
  have hinvm0 : 0 < 1 / (m : ℝ) := by positivity
  have hc0 : 0 ≤ 1 - 3 * h' - 1 / m := by linarith
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hcm : ((m * N₀ : ℕ) : ℝ) = m * N₀ := Nat.cast_mul m N₀
  have hcast : ((m * N₀ : ℕ) : ℝ) - N₀ = (m - 1) * N₀ := by rw [hcm]; ring
  have hA : 0 ≤ (1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀) := by
    rw [hcast]; have : 0 ≤ (m : ℝ) - 1 := by linarith
    have : 0 ≤ 1 - h' := by linarith
    positivity
  have hlhs0 : 0 ≤ σ * (1 - 3 * h' - 1 / m) * lilScale (m * N₀) :=
    mul_nonneg (mul_nonneg hσ hc0) (lilScale_nonneg _)
  have hrhs0 : 0 ≤ (1 - h') * √(2 * Real.log (Real.log ((m * N₀ : ℕ) : ℝ))) *
      √((1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀)) := by
    have : 0 ≤ 1 - h' := by linarith
    positivity
  refine (pow_le_pow_iff_left₀ hlhs0 hrhs0 two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, lilScale_sq hN, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt hA, hcast]
  set LL := Real.log (Real.log ((m * N₀ : ℕ) : ℝ)) with hLL
  rw [hcm]
  -- `(1 − 3h' − 1/m)² m ≤ (1 − h')³ (m − 1)`
  have hb1 : 1 - 3 * h' ≤ (1 - h') ^ 3 := by nlinarith [sq_nonneg h', mul_nonneg h0 (sq_nonneg h')]
  have hb2 : (1 - 3 * h' - 1 / m) ^ 2 ≤ 1 - 3 * h' - 1 / m := by nlinarith
  have hb3 : (1 - 3 * h') * (1 - 1 / m) ≤ (1 - h') ^ 3 * (1 - 1 / m) :=
    mul_le_mul_of_nonneg_right hb1 (by linarith)
  have hb4 : 1 - 3 * h' - 1 / m ≤ (1 - 3 * h') * (1 - 1 / m) := by nlinarith
  have hkey : (1 - 3 * h' - 1 / m) ^ 2 * m ≤ (1 - h') ^ 3 * (m - 1) := by
    have h5 : (1 - 3 * h' - 1 / m) ^ 2 ≤ (1 - h') ^ 3 * (1 - 1 / m) := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 (show (0 : ℝ) ≤ m by linarith)
    have e : (1 - h') ^ 3 * (1 - 1 / m) * m = (1 - h') ^ 3 * (m - 1) := by
      field_simp
    linarith
  have h7 : 0 ≤ σ ^ 2 * (2 * N₀ * LL) := by positivity
  have h8 := mul_le_mul_of_nonneg_right hkey h7
  have e1 : σ ^ 2 * (1 - 3 * h' - 1 / ↑m) ^ 2 * (2 * (↑m * ↑N₀) * LL) =
      (1 - 3 * h' - 1 / m) ^ 2 * m * (σ ^ 2 * (2 * N₀ * LL)) := by ring
  have e2 : (1 - h') ^ 2 * (2 * LL) * ((1 - h') * σ ^ 2 * ((↑m - 1) * ↑N₀)) =
      (1 - h') ^ 3 * (m - 1) * (σ ^ 2 * (2 * N₀ * LL)) := by ring
  rw [e1, e2]
  exact h8

/-- The truncation is small on the block scale: with `N₁ = mN₀ ≥ j₀`,
`4 x · 2τ_{N₁}/√B ≤ 16δ/σ` for `x = (1 − h')√(2 log log N₁)`, `τ_{N₁} = lilTruncLevel δ j₀ N₁`
and `B = (1 − h')σ²(N₁ − N₀)`. -/
theorem lower_param_le {σ h' δ : ℝ} (hσ : 0 < σ) (h0 : 0 ≤ h') (h1 : h' ≤ 1 / 2) (hδ : 0 ≤ δ)
    {m N₀ j₀ : ℕ} (hm : 2 ≤ m) (hN₀ : 0 < N₀) (hj : j₀ ≤ m * N₀)
    (hN : 3 ≤ Real.log ((m * N₀ : ℕ) : ℝ)) :
    4 * ((1 - h') * √(2 * Real.log (Real.log ((m * N₀ : ℕ) : ℝ))) *
      (2 * lilTruncLevel δ j₀ (m * N₀) / √((1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀)))) ≤
        16 * δ / σ := by
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hL := one_le_loglog hN
  set LL := Real.log (Real.log ((m * N₀ : ℕ) : ℝ)) with hLL
  have hN₀' : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hcast : ((m * N₀ : ℕ) : ℝ) - N₀ = (m - 1) * N₀ := by push_cast; ring
  have hh : 0 < 1 - h' := by linarith
  have hB : 0 < (1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀) := by
    rw [hcast]; have : 0 < (m : ℝ) - 1 := by linarith
    positivity
  have hφ : lilPhi ((max (m * N₀) j₀ : ℕ) : ℝ) = ((m * N₀ : ℕ) : ℝ) / LL := by
    rw [max_eq_left hj, lilPhi]
  have hφ0 : 0 ≤ ((m * N₀ : ℕ) : ℝ) / LL := by positivity
  have hlhs0 : 0 ≤ 4 * ((1 - h') * √(2 * LL) *
      (2 * lilTruncLevel δ j₀ (m * N₀) / √((1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀)))) := by
    have := lilTruncLevel_nonneg hδ j₀ (m * N₀)
    positivity
  refine (pow_le_pow_iff_left₀ hlhs0 (by positivity) two_ne_zero).1 ?_
  have hτ2 : lilTruncLevel δ j₀ (m * N₀) ^ 2 = δ ^ 2 * (((m * N₀ : ℕ) : ℝ) / LL) := by
    rw [lilTruncLevel, hφ, mul_pow, Real.sq_sqrt hφ0]
  have eL : (4 * ((1 - h') * √(2 * LL) * (2 * lilTruncLevel δ j₀ (m * N₀) /
      √((1 - h') * σ ^ 2 * (((m * N₀ : ℕ) : ℝ) - N₀))))) ^ 2 =
      4 ^ 2 * ((1 - h') ^ 2 * (2 * LL) * (2 ^ 2 * (δ ^ 2 * (((m * N₀ : ℕ) : ℝ) / LL)) /
        ((1 - h') * σ ^ 2 * ((m - 1) * N₀)))) := by
    rw [mul_pow, mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity), hτ2,
      Real.sq_sqrt hB.le, hcast]
  rw [eL]
  push_cast
  have hmm : (m : ℝ) / (m - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have e : (4 : ℝ) ^ 2 * ((1 - h') ^ 2 * (2 * LL) * (2 ^ 2 * (δ ^ 2 * (↑m * ↑N₀ / LL)) /
      ((1 - h') * σ ^ 2 * ((↑m - 1) * ↑N₀)))) = 128 * (1 - h') * δ ^ 2 / σ ^ 2 * (m / (m - 1)) := by
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  have h2 : 128 * (1 - h') * δ ^ 2 / σ ^ 2 * (m / (m - 1)) ≤ 128 * (1 - h') * δ ^ 2 / σ ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hmm (by positivity)
  have h3 : 128 * (1 - h') * δ ^ 2 / σ ^ 2 * 2 ≤ (16 * δ / σ) ^ 2 := by
    rw [div_pow, mul_pow]
    have : 128 * (1 - h') * δ ^ 2 / σ ^ 2 * 2 = 256 * (1 - h') * δ ^ 2 / σ ^ 2 := by ring
    rw [this, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [sq_nonneg δ]
  linarith

omit mΩ in
/-- If `(1/H) Σ_{j<H} (vⱼ − 2wⱼ) → c > 0` and `vⱼ − 2wⱼ ≤ uⱼ` with `uⱼ ≥ 0` for `j ≥ N₁ ≥ N₀`, then
`Σ_{j ∈ [N₀, H)} uⱼ ≥ B` for some `H`. -/
theorem exists_sum_Ico_ge {v w u : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun H : ℕ => (∑ j ∈ Finset.range H, (v j - 2 * w j)) / H) atTop (𝓝 c))
    {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (hvu : ∀ j, N₁ ≤ j → v j - 2 * w j ≤ u j) (hu0 : ∀ j, 0 ≤ u j)
    (B : ℝ) : ∃ H, B ≤ ∑ j ∈ Finset.Ico N₀ H, u j := by
  have hinfty : Tendsto (fun H : ℕ => ∑ j ∈ Finset.range H, (v j - 2 * w j)) atTop atTop := by
    refine (hlim.pos_mul_atTop hc tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with H hH
    have : (H : ℝ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
    field_simp
  obtain ⟨H, hH1, hH2⟩ := ((hinfty.eventually_ge_atTop (B + ∑ j ∈ Finset.range N₁,
    (v j - 2 * w j))).and (eventually_ge_atTop N₁)).exists
  refine ⟨H, ?_⟩
  have h7 : B ≤ ∑ j ∈ Finset.Ico N₁ H, (v j - 2 * w j) := by
    rw [Finset.sum_Ico_eq_sub _ hH2]; linarith
  have h8 : ∑ j ∈ Finset.Ico N₁ H, (v j - 2 * w j) ≤ ∑ j ∈ Finset.Ico N₁ H, u j :=
    Finset.sum_le_sum fun j hj => hvu j (Finset.mem_Ico.1 hj).1
  have h9 : ∑ j ∈ Finset.Ico N₁ H, u j ≤ ∑ j ∈ Finset.Ico N₀ H, u j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico hN le_rfl)
      fun j _ _ => hu0 j
  linarith

omit mΩ in
/-- **The blocks use up their budget**: if `(1/n) Σ_{j<n} vⱼ → s`, `(1/n) Σ_{j<n} wⱼ → τ` and
`c < s − 2τ`, and eventually `vⱼ − 2wⱼ ≤ u_{k,j}` on `[m^k, m^{k+1})`, then eventually
`c (m^{k+1} − m^k) < Σ_{j ∈ [m^k, m^{k+1})} u_{k,j}`. -/
theorem eventually_block_budget {v w : ℕ → ℝ} {s τ c : ℝ}
    (hv : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, v j) / n) atTop (𝓝 s))
    (hw : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, w j) / n) atTop (𝓝 τ))
    (hgt : c < s - 2 * τ) {m : ℕ} (hm : 2 ≤ m) {u : ℕ → ℕ → ℝ}
    (hu : ∀ᶠ k in atTop, ∀ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), v j - 2 * w j ≤ u k j) :
    ∀ᶠ k in atTop, c * (((m ^ (k + 1) : ℕ) : ℝ) - ((m ^ k : ℕ) : ℝ)) <
      ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), u k j := by
  have hlim := (tendsto_block_avg hv hm).sub ((tendsto_block_avg hw hm).const_mul 2)
  filter_upwards [hlim.eventually (lt_mem_nhds hgt), hu] with k hk hku
  have hle : m ^ k ≤ m ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  have hpos : (0 : ℝ) < ((m ^ (k + 1) : ℕ) : ℝ) - ((m ^ k : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) < m := by exact_mod_cast hm
    have h2 : (0 : ℝ) < (m : ℝ) ^ k := by positivity
    push_cast
    rw [pow_succ]
    nlinarith
  set d := ((m ^ (k + 1) : ℕ) : ℝ) - ((m ^ k : ℕ) : ℝ) with hd
  set A1 := ∑ j ∈ Finset.range (m ^ (k + 1)), v j - ∑ j ∈ Finset.range (m ^ k), v j with hA1
  set A2 := ∑ j ∈ Finset.range (m ^ (k + 1)), w j - ∑ j ∈ Finset.range (m ^ k), w j with hA2
  have hk' : c < A1 / d - 2 * (A2 / d) := hk
  have e1 : (A1 / d - 2 * (A2 / d)) * d = A1 - 2 * A2 := by field_simp
  have h3 := mul_lt_mul_of_pos_right hk' hpos
  rw [e1] at h3
  have e : ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), (v j - 2 * w j) = A1 - 2 * A2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hle,
      Finset.sum_Ico_eq_sub _ hle]
  have h4 : ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), (v j - 2 * w j) ≤
      ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), u k j := Finset.sum_le_sum hku
  linarith

/-- **The final inequality of the lower half**: if the block `[N₀, T)`, `N₀ ≤ T ≤ mN₀`, carries
`S'_T − S'_{N₀} > σ(1 − 3h' − 1/m) √(2 mN₀ log log mN₀)`, the truncation error is at most
`(ε/8) √(2 n log log n)` at `N₀` and `T`, and `−S_{N₀} ≤ (σ + ε/8) √(2 N₀ log log N₀)`, then
`S_T ≥ (σ − ε) √(2 T log log T)` (with `h' = ε/(16σ)`, `0 < ε ≤ σ`, `σ/√m ≤ ε/16`). -/
theorem lower_combine {σ ε : ℝ} (hε : 0 < ε) (hεσ : ε ≤ σ) {m : ℕ} (hm : 2 ≤ m)
    (hsm : σ / √(m : ℝ) ≤ ε / 16) {SD SX : ℕ → ℝ} {N₀ T : ℕ} (hN₀ : 3 ≤ Real.log N₀)
    (hT1 : N₀ ≤ T) (hT2 : T ≤ m * N₀)
    (hY : σ * (1 - 3 * (ε / (16 * σ)) - 1 / m) * lilScale (m * N₀) < SX T - SX N₀)
    (hb : |SD T - SX T| ≤ ε / 8 * lilScale T) (hc : |SD N₀ - SX N₀| ≤ ε / 8 * lilScale N₀)
    (hd : -SD N₀ ≤ (σ + ε / 8) * lilScale N₀) :
    (σ - ε) * lilScale T ≤ SD T := by
  have hσpos : 0 < σ := hε.trans_le hεσ
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set Λ := lilScale (m * N₀) with hΛ
  have hΛ0 : 0 ≤ Λ := lilScale_nonneg _
  have hf : lilScale N₀ * √(m : ℝ) ≤ Λ := lilScale_mul_sqrt_le hN₀ (by omega)
  have hT3 : 3 ≤ Real.log (T : ℝ) := three_le_log_of_le hN₀ hT1
  have hg : lilScale T ≤ Λ := lilScale_mono hT3 hT2
  have hsm0 : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hmle : √(m : ℝ) ≤ m := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hσm : σ * (1 / m) ≤ ε / 16 := by
    have : σ * (1 / m) ≤ σ / √(m : ℝ) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left hσpos.le hsm0 hmle
    linarith
  have i1 : (σ + ε / 4) * lilScale N₀ ≤ 5 / 64 * ε * Λ := by
    have h1 : (σ + ε / 4) * lilScale N₀ =
        (σ + ε / 4) / √(m : ℝ) * (lilScale N₀ * √(m : ℝ)) := by field_simp
    rw [h1]
    have h2 : (σ + ε / 4) / √(m : ℝ) ≤ 5 / 64 * ε := by
      have : (σ + ε / 4) / √(m : ℝ) ≤ 5 / 4 * (σ / √(m : ℝ)) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hsm0]; linarith
      linarith
    calc (σ + ε / 4) / √(m : ℝ) * (lilScale N₀ * √(m : ℝ))
        ≤ (σ + ε / 4) / √(m : ℝ) * Λ := mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ 5 / 64 * ε * Λ := mul_le_mul_of_nonneg_right h2 hΛ0
  have i2 : (σ - 3 * ε / 16 - ε / 16) * Λ ≤ σ * (1 - 3 * (ε / (16 * σ)) - 1 / m) * Λ := by
    refine mul_le_mul_of_nonneg_right ?_ hΛ0
    have e : σ * (3 * (ε / (16 * σ))) = 3 * ε / 16 := by field_simp
    nlinarith
  have i3 : ε / 8 * lilScale T ≤ ε / 8 * Λ := mul_le_mul_of_nonneg_left hg (by positivity)
  have i4 : (σ - ε) * lilScale T ≤ (σ - ε) * Λ := mul_le_mul_of_nonneg_left hg (by linarith)
  have i5 : 0 ≤ ε * Λ := mul_nonneg hε.le hΛ0
  have hb' := (abs_le.1 hb).1
  have hc' := (abs_le.1 hc).2
  linarith only [hY, hb', hc', hd, i1, i2, i3, i4, i5]

/-! ### The lower half -/

/-- **The lower half of the martingale LIL** (Stout 1970), in the case `0 < ε ≤ σ`. -/
theorem martingale_lil_lower_aux {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q)))
    (hT : ∀ K : ℕ, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | (K : ℝ) ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω | ℱ k] ω) / n)
      atTop (𝓝 (∫ ω, {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω ∂Q)))
    {ε : ℝ} (hε : 0 < ε) (hεσ : ε ≤ √(∫ ω, D 0 ω ^ 2 ∂Q)) :
    ∀ᵐ ω ∂Q, ∃ᶠ n in atTop,
      (√(∫ ω, D 0 ω ^ 2 ∂Q) - ε) * lilScale n ≤ ∑ j ∈ Finset.range n, D j ω := by
  set σ := √(∫ ω, D 0 ω ^ 2 ∂Q) with hσ
  have hσpos : 0 < σ := hε.trans_le hεσ
  have hσ2 : σ ^ 2 = ∫ ω, D 0 ω ^ 2 ∂Q := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)
  have hDm : ∀ j, Measurable (D j) := fun j => (hD j).measurable.mono (ℱ.le _) le_rfl
  have hDL2 : ∀ j, MemLp (D j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  -- the constants
  set h' := ε / (16 * σ) with hh'
  have hh'0 : 0 < h' := by positivity
  have hh'1 : h' ≤ 1 / 16 := by
    rw [hh', div_le_iff₀ (by positivity)]; linarith
  set h := h' / 12 with hhdef
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 / 4 := by rw [hhdef]; linarith
  set α := h ^ 2 / 4 with hα
  have hα0 : 0 < α := by positivity
  set m : ℕ := ⌈(16 * σ / ε) ^ 2⌉₊ + 2 with hm
  have hm2 : 2 ≤ m := by omega
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmsq : 16 * σ / ε ≤ √(m : ℝ) := by
    rw [show 16 * σ / ε = √((16 * σ / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ((Nat.le_ceil _).trans ?_)
    rw [hm]; push_cast; linarith
  have hsm : σ / √(m : ℝ) ≤ ε / 16 := by
    have hsm0 : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hsm0]
    have := mul_le_mul_of_nonneg_left hmsq (show 0 ≤ ε / 16 by positivity)
    have e : ε / 16 * (16 * σ / ε) = σ := by field_simp
    linarith
  set δ := α * σ / 32 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, 3 ≤ Real.log j₀ := (eventually_le_log 3).exists
  set β : ℕ → ℝ := lilTruncLevel δ j₀ with hβ
  have hβ0 : ∀ j, 0 ≤ β j := lilTruncLevel_nonneg hδ0.le j₀
  have hβm : Monotone β := lilTruncLevel_mono hδ0.le hj₀
  have hβt : Tendsto β atTop atTop := tendsto_lilTruncLevel hδ0 hj₀
  -- the tail level `K₀`
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, ∫ ω, {ω | (K₀ : ℝ) ≤ D 0 ω ^ 2}.indicator
      (fun ω => D 0 ω ^ 2) ω ∂Q ≤ h' * σ ^ 2 / 16 :=
    ((tendsto_integral_sq_indicator (hDm 0) hL2).eventually
      (eventually_le_nhds (show (0 : ℝ) < h' * σ ^ 2 / 16 by positivity))).exists
  set τ₀ := ∫ ω, {ω | (K₀ : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω ∂Q with hτ₀
  have hτ₀0 : 0 ≤ τ₀ := integral_nonneg fun ω =>
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hβK : ∀ᶠ j in atTop, (K₀ : ℝ) ≤ β j ^ 2 := by
    filter_upwards [hβt.eventually_ge_atTop (√(K₀ : ℝ))] with j hj
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hj 2
    rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hβK
  -- the blocks
  set nk : ℕ → ℕ := fun k => m ^ k with hnk
  have hnk_succ : ∀ k, nk (k + 1) = m * nk k := fun k => by simp only [hnk, pow_succ']
  have hnk_pos : ∀ k, 0 < nk k := fun k => by simp only [hnk]; positivity
  have hnk_mono : Monotone nk := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have hnk_t : Tendsto nk atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by omega)
  set Bk : ℕ → ℝ := fun k => (1 - h') * σ ^ 2 * (((nk (k + 1) : ℕ) : ℝ) - (nk k : ℝ)) with hBk
  set xk : ℕ → ℝ := fun k => (1 - h') * √(2 * Real.log (Real.log (nk (k + 1) : ℝ))) with hxk
  set bk : ℕ → ℕ → ℝ := fun k j => β (min j (nk (k + 1))) with hbk
  set Ak : ℕ → Set Ω := fun k =>
    {ω | xk k * √(Bk k) < blockSum Q ℱ D (bk k) (nk k) (Bk k) (nk (k + 1)) ω} ∪
      {ω | ∑ j ∈ Finset.Ico (nk k) (nk (k + 1)), truncVar Q ℱ D (bk k) j ω ≤ Bk k} with hAk
  set pk : ℕ → ℝ := fun k => 1 / 2 * Real.exp (-(xk k ^ 2 / 2 * (1 + 12 * h))) with hpk
  -- the almost sure ingredients
  set v : ℕ → Ω → ℝ := condVarMD Q ℱ D with hv
  set w : ℕ → Ω → ℝ := fun j => Q[fun ω => {ω | (K₀ : ℝ) ≤ D j ω ^ 2}.indicator
    (fun ω => D j ω ^ 2) ω | ℱ j] with hw
  have hVω : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, v j ω) / n) atTop
      (𝓝 (σ ^ 2)) := by
    filter_upwards [hV, ae_all_iff.2 fun k => condVarMD_ae_eq Q ℱ D k] with ω hω hk
    rw [hσ2]
    refine hω.congr fun n => ?_
    congr 1
    exact Finset.sum_congr rfl fun k _ => (hk k).symm
  have hWω : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, w j ω) / n) atTop
      (𝓝 τ₀) := hT K₀
  have hge1 : ∀ᵐ ω ∂Q, ∀ k j, (K₀ : ℝ) ≤ bk k j ^ 2 →
      v j ω - 2 * w j ω ≤ truncVar Q ℱ D (bk k) j ω := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun j => ?_
    by_cases hc : (K₀ : ℝ) ≤ bk k j ^ 2
    · filter_upwards [truncVar_ge hD hDL2 h0 (b := bk k) (fun j => hβ0 _) j hc] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hc
  have hge2 : ∀ᵐ ω ∂Q, ∀ j, (K₀ : ℝ) ≤ β j ^ 2 →
      v j ω - 2 * w j ω ≤ truncVar Q ℱ D β j ω := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hc : (K₀ : ℝ) ≤ β j ^ 2
    · filter_upwards [truncVar_ge hD hDL2 h0 hβ0 j hc] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hc
  have hτσ : 2 * τ₀ < h' * σ ^ 2 := by
    have : 0 < h' * σ ^ 2 := by positivity
    linarith
  -- the conditional Borel–Cantelli lemma along the blocks
  have hAm : ∀ k, MeasurableSet[ℱ (nk (k + 1))] (Ak k) := fun k => by
    refine MeasurableSet.union ?_ ?_
    · exact (measurable_sum_Ico (fun j => (measurable_truncMD Q hD (bk k) j).indicator
        (ℱ.mono (Nat.le_succ j) _ (measurableSet_blockSet Q ℱ D (bk k) (nk k) (Bk k) j)))
        (nk k) (nk (k + 1))) measurableSet_Ioi
    · exact (measurable_sum_Ico (fun j => (measurable_truncVar Q ℱ D (bk k) j).mono
        (ℱ.mono (Nat.le_succ j)) le_rfl) (nk k) (nk (k + 1))) measurableSet_Iic
  have hp0 : ∀ k, 0 ≤ pk k := fun k => by simp only [hpk]; positivity
  have hLLt : Tendsto (fun k => Real.log (Real.log (nk (k + 1) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp
      (hnk_t.comp (tendsto_add_atTop_nat 1))))
  have hps : ¬ Summable pk := by
    set q := (1 - h') ^ 2 * (1 + 12 * h) with hq
    have hq1 : q ≤ 1 := by
      have e : 1 + 12 * h = 1 + h' := by rw [hhdef]; ring
      rw [hq, e]
      nlinarith [sq_nonneg h']
    have hnot := not_summable_exp_neg_mul_loglog_pow hm2 hq1 (show (0 : ℝ) < 1 / 2 by norm_num)
    intro hs
    refine hnot ((summable_nat_add_iff 1).1 (hs.congr_atTop ?_))
    filter_upwards [hLLt.eventually_ge_atTop 0] with k hk
    simp only [hpk, hxk]
    rw [mul_pow, Real.sq_sqrt (by linarith), hnk]
    push_cast
    congr 2
    ring
  -- the conditional lower bound for large `k`
  have hxt : Tendsto xk atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (hLLt.const_mul_atTop two_pos)).const_mul_atTop
      (by linarith)
  have hlog4 : Real.log 4 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hN1t : Tendsto (fun k => nk (k + 1)) atTop atTop := hnk_t.comp (tendsto_add_atTop_nat 1)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((hxt.eventually_ge_atTop (max 1 (2 / h))).and
    ((hN1t.eventually_ge_atTop j₀).and ((hN1t.eventually (eventually_le_log 3)).and
      (hN1t.eventually (eventually_atTop.2 ⟨J₀, hJ₀⟩)))))
  have hlow : ∀ k ≥ k₁, ∀ G : Set Ω, MeasurableSet[ℱ (nk k)] G →
      pk k * Q.real G ≤ Q.real (G ∩ Ak k) := by
    intro k hk G hG
    obtain ⟨hx, hj, h3, hK⟩ := hk₁ k hk
    have hx1 : 1 ≤ xk k := (le_max_left _ _).trans hx
    have hx2 : 2 / h ≤ xk k := (le_max_right _ _).trans hx
    have hxh : Real.log 4 ≤ h ^ 2 * xk k ^ 2 := by
      have h4 : (2 / h) ^ 2 ≤ xk k ^ 2 := pow_le_pow_left₀ (by positivity) hx2 2
      have h5 : h ^ 2 * (2 / h) ^ 2 = 4 := by field_simp; norm_num
      have := mul_le_mul_of_nonneg_left h4 (sq_nonneg h)
      linarith
    have hN1 : nk (k + 1) = m * nk k := hnk_succ k
    have hB : 0 < Bk k := by
      simp only [hBk]
      rw [hN1]
      have : ((m * nk k : ℕ) : ℝ) - (nk k : ℝ) = ((m : ℝ) - 1) * nk k := by push_cast; ring
      rw [this]
      have : (0 : ℝ) < nk k := by exact_mod_cast hnk_pos k
      have : 0 < 1 - h' := by linarith
      have : (0 : ℝ) < m - 1 := by linarith
      positivity
    have hc : 4 * (xk k * (2 * β (nk (k + 1)) / √(Bk k))) ≤ α := by
      have h6 := lower_param_le hσpos hh'0.le (by linarith) hδ0.le (m := m) (N₀ := nk k)
        (j₀ := j₀) hm2 (hnk_pos k) (by rw [← hN1]; exact hj) (by rw [← hN1]; exact h3)
      rw [← hN1] at h6
      have e : 16 * δ / σ = α / 2 := by rw [hδ]; field_simp; ring
      rw [e] at h6
      have : 4 * (xk k * (2 * β (nk (k + 1)) / √(Bk k))) ≤ α / 2 := h6
      linarith
    have hinf : ∀ᵐ ω ∂Q, ∃ H, Bk k ≤
        ∑ j ∈ Finset.Ico (nk k) H, truncVar Q ℱ D (bk k) j ω := by
      filter_upwards [hVω, hWω, hge1] with ω hωV hωW hωg
      have hlim : Tendsto (fun H : ℕ => (∑ j ∈ Finset.range H, (v j ω - 2 * w j ω)) / H)
          atTop (𝓝 (σ ^ 2 - 2 * τ₀)) := by
        refine (hωV.sub (hωW.const_mul 2)).congr fun H => ?_
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
      have hpos : 0 < σ ^ 2 - 2 * τ₀ := by nlinarith
      exact exists_sum_Ico_ge hpos hlim (hnk_mono (Nat.le_succ k)) (fun j hj => hωg k j (by
        simp only [hbk, min_eq_right hj]; exact hK)) (fun j => truncVar_nonneg Q ℱ D (bk k) j ω)
        (Bk k)
    have hblock := mdBlock_lower_bound hD (b := bk k) (L := β (nk (k + 1))) (fun j => hβ0 _)
      (fun j => hβm (min_le_right _ _)) (hnk_mono (Nat.le_succ k)) hB hx1 hh0 hh1 hα0.le le_rfl
      hxh hc hinf hG
    have e : pk k * Q.real G = Q.real G / 2 * Real.exp (-(xk k ^ 2 / 2 * (1 + 12 * h))) := by
      simp only [hpk]; ring
    rw [e]
    exact hblock
  have hfreq := ae_frequently_of_cond_lower hnk_mono hAm hp0 hps hlow
  -- the upper half for `−S`, and the truncation tails
  have hup := martingale_lil_upper_neg hD h0 hident hL2 hV (show 0 < ε / 8 by positivity)
  have htail := ae_tendsto_sum_sub_truncMD hD h0 hident hL2 hδ0 hj₀
  filter_upwards [hfreq, hup, htail, hVω, hWω, hge2] with ω hωA hωU hωT hωV hωW hωg
  set SD : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, D j ω with hSD
  set SX : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, truncMD Q ℱ D β j ω with hSX
  -- eventually the budget is used up inside the block
  have hGood : ∀ᶠ k in atTop,
      Bk k < ∑ j ∈ Finset.Ico (nk k) (nk (k + 1)), truncVar Q ℱ D (bk k) j ω := by
    have hgt : (1 - h') * σ ^ 2 < σ ^ 2 - 2 * τ₀ := by linarith
    have hb := eventually_block_budget hωV hωW hgt hm2 (u := fun k j => truncVar Q ℱ D (bk k) j ω)
      (by
        filter_upwards [hnk_t.eventually_ge_atTop J₀] with k hkJ j hj
        have hj' := Finset.mem_Ico.1 hj
        have hj2 : j < nk (k + 1) := hj'.2
        have hbj : bk k j = β j := by simp only [hbk, min_eq_left hj2.le]
        rw [truncVar_congr Q ℱ D hbj]
        exact hωg j (hJ₀ j (hkJ.trans hj'.1)))
    filter_upwards [hb] with k hk
    have e : Bk k = (1 - h') * σ ^ 2 * (((m ^ (k + 1) : ℕ) : ℝ) - ((m ^ k : ℕ) : ℝ)) := rfl
    rw [e]
    exact hk
  -- the thresholds
  have hT' : ∀ᶠ n in atTop, |SD n - SX n| ≤ ε / 8 * lilScale n := by
    filter_upwards [(Metric.tendsto_nhds.1 hωT) (ε / 8) (by positivity),
      eventually_le_log 3] with n hn hn3
    have hp := lilScale_pos hn3
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at hn
    exact hn.le
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨NU, hNU⟩ := eventually_atTop.1 hωU
  obtain ⟨NT, hNT⟩ := eventually_atTop.1 hT'
  obtain ⟨K2, hK2⟩ := eventually_atTop.1 (hGood.and ((hnk_t.eventually_ge_atTop
    (max (max NU NT) N)).and (hnk_t.eventually (eventually_le_log 3))))
  obtain ⟨k, hkK, hkA⟩ := Filter.frequently_atTop.1 hωA K2
  obtain ⟨hG, hkN, hk3⟩ := hK2 k hkK
  -- the block sum is large
  have hY : xk k * √(Bk k) < blockSum Q ℱ D (bk k) (nk k) (Bk k) (nk (k + 1)) ω := by
    rcases hkA with h | h
    · exact h
    · exact absurd h (not_le.2 hG)
  -- the block is a partial sum
  obtain ⟨T, hT1, hT2, hTe⟩ := exists_sum_indicator_eq
    (S := blockSet Q ℱ D (bk k) (nk k) (Bk k))
    (fun i j hi hij hj => mem_blockSet_of_le Q ℱ D (bk k) hi hij hj) (truncMD Q ℱ D (bk k))
    (hnk_mono (Nat.le_succ k))
  have hYT : blockSum Q ℱ D (bk k) (nk k) (Bk k) (nk (k + 1)) ω = SX T - SX (nk k) := by
    change ∑ j ∈ Finset.Ico (nk k) (nk (k + 1)),
      (blockSet Q ℱ D (bk k) (nk k) (Bk k) j).indicator (truncMD Q ℱ D (bk k) j) ω = _
    rw [hTe, ← Finset.sum_Ico_eq_sub _ hT1]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Ico.1 hj
    have hbj : bk k j = β j := by simp only [hbk, min_eq_left (hj'.2.trans_le hT2).le]
    rw [truncMD_congr Q ℱ D hbj]
  refine ⟨T, (le_max_right _ _).trans (hkN.trans hT1), ?_⟩
  have hN1 : nk (k + 1) = m * nk k := hnk_succ k
  have ha := lower_target_ge hσpos.le hh'0.le hh'1 (m := m) (N₀ := nk k) hm2
    (by rw [← hN1]; exact three_le_log_of_le hk3 (hnk_mono (Nat.le_succ k)))
  rw [← hN1] at ha
  have hNTk : NT ≤ nk k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hkN
  exact lower_combine hε hεσ hm2 hsm hk3 hT1 (by rw [← hN1]; exact hT2)
    (by rw [← hN1, ← hYT]; exact lt_of_le_of_lt ha hY) (hNT T (hNTk.trans hT1)) (hNT (nk k) hNTk)
    (hNU (nk k) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hkN))

/-- **The lower half of the martingale LIL** (Stout 1970): let `Dⱼ` be martingale differences
(`𝓕ⱼ₊₁`-measurable, `E[Dⱼ | 𝓕ⱼ] = 0`), identically distributed and square integrable, such that
almost surely `(1/n) Σ_{j<n} E[Dⱼ² | 𝓕ⱼ] → σ² = E[D₀²]` and, for every `K ∈ ℕ`,
`(1/n) Σ_{j<n} E[Dⱼ² 1{Dⱼ² ≥ K} | 𝓕ⱼ] → E[D₀² 1{D₀² ≥ K}]`. Then for every `ε > 0`, almost
surely `Σ_{j<n} Dⱼ ≥ (σ − ε) √(2 n log log n)` for infinitely many `n`. -/
theorem martingale_lil_lower {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q)))
    (hT : ∀ K : ℕ, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | (K : ℝ) ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω | ℱ k] ω) / n)
      atTop (𝓝 (∫ ω, {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω ∂Q)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Q, ∃ᶠ n in atTop,
      (√(∫ ω, D 0 ω ^ 2 ∂Q) - ε) * lilScale n ≤ ∑ j ∈ Finset.range n, D j ω := by
  rcases le_or_gt ε (√(∫ ω, D 0 ω ^ 2 ∂Q)) with hεσ | hσε
  · exact martingale_lil_lower_aux hD h0 hident hL2 hV hT hε hεσ
  · rcases eq_or_lt_of_le (Real.sqrt_nonneg (∫ ω, D 0 ω ^ 2 ∂Q)) with hσ0 | hσpos
    · filter_upwards [martingale_lil_upper_neg hD h0 hident hL2 hV hε] with ω hω
      refine (hω.mono fun n hn => ?_).frequently
      rw [← hσ0] at hn ⊢
      linarith
    · filter_upwards [martingale_lil_lower_aux hD h0 hident hL2 hV hT hσpos le_rfl] with ω hω
      refine hω.mono fun n hn => le_trans ?_ hn
      exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)

end MeynTweedie.GeneralizedDrift
