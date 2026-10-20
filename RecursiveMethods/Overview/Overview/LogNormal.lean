/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.StochasticLog
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi

/-!
# Log-normal capital

SLP Exercise 2.7, p. 20.

Under policy (5), `k_{t+1} = αβ z_t k_t^α`, so `ln k_{t+1} = ln(αβ) + α ln k_t + ln z_t`. If the
`ln z_t` are i.i.d. `N(m, σ²)`, each `ln k_t` is normal.

* `capPath`, `log_capPath`: the capital path in levels has logarithm `logPath`.
* `logPath_eq`: `ln k_t = c_t + ∑_{s<t} α^{t−1−s} ln z_s`, a function of past shocks only.
* `indepFun_logPath`: `ln k_t` is independent of the current shock `ln z_t`.
* `hasLaw_logPath` (Ex 2.7): `ln k_t ∼ N(μ_t, σ_t²)` with `μ_{t+1} = αμ_t + ln(αβ) + m`,
  `σ²_{t+1} = α²σ_t² + σ²`; `meanN_eq`, `varN_eq`: `μ_t = αᵗ ln k₀ + (ln(αβ) + m)(1 − αᵗ)/(1 − α)`,
  `σ_t² = σ²(1 − α^{2t})/(1 − α²)`.
* `meanN_tendsto`, `varN_tendsto` (Ex 2.7): `μ_t → (ln(αβ) + m)/(1 − α)`,
  `σ_t² → σ²/(1 − α²)`.
-/

open Finset Filter Topology Real MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StokeyLucasPrescott.Overview

/-- The capital path `k_{t+1} = αβ e^{ω_t} k_t^α`, with `ω_t = ln z_t`. -/
noncomputable def capPath (α β k₀ : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => α * β * exp (ω t) * capPath α β k₀ ω t ^ α

/-- `ln k_t`: `ℓ₀` given, `ℓ_{t+1} = ln(αβ) + αℓ_t + ω_t`. -/
noncomputable def logPath (α β ℓ₀ : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => ℓ₀
  | t + 1 => log (α * β) + α * logPath α β ℓ₀ ω t + ω t

/-- The capital path in levels has logarithm `logPath`, and stays positive. -/
theorem log_capPath {α β k₀ : ℝ} (h0 : 0 < α * β) (hk₀ : 0 < k₀) (ω : ℕ → ℝ) (t : ℕ) :
    0 < capPath α β k₀ ω t ∧ log (capPath α β k₀ ω t) = logPath α β (log k₀) ω t := by
  induction t with
  | zero => exact ⟨hk₀, rfl⟩
  | succ t ih =>
    obtain ⟨hp, hl⟩ := ih
    refine ⟨mul_pos (mul_pos h0 (exp_pos _)) (rpow_pos_of_pos hp α), ?_⟩
    simp only [capPath, logPath]
    rw [log_mul (mul_pos h0 (exp_pos _)).ne' (rpow_pos_of_pos hp α).ne',
      log_mul h0.ne' (exp_pos _).ne', log_exp, log_rpow hp, hl]
    ring

/-- The deterministic part of `ln k_t`: `c₀ = ℓ₀`, `c_{t+1} = ln(αβ) + αc_t`. -/
noncomputable def constPath (α β ℓ₀ : ℝ) : ℕ → ℝ
  | 0 => ℓ₀
  | t + 1 => log (α * β) + α * constPath α β ℓ₀ t

/-- `ln k_t = c_t + ∑_{s<t} α^{t−1−s} ω_s`. -/
theorem logPath_eq (α β ℓ₀ : ℝ) (ω : ℕ → ℝ) (t : ℕ) :
    logPath α β ℓ₀ ω t = constPath α β ℓ₀ t + ∑ s ∈ range t, α ^ (t - 1 - s) * ω s := by
  induction t with
  | zero => simp [logPath, constPath]
  | succ t ih =>
    simp only [logPath, constPath, ih, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self,
      pow_zero, one_mul, mul_add, mul_sum]
    have : ∀ s ∈ range t, α * (α ^ (t - 1 - s) * ω s) = α ^ (t - s) * ω s := fun s hs => by
      have hs := mem_range.1 hs
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [sum_congr rfl this]
    ring

theorem measurable_logPath (α β ℓ₀ : ℝ) (t : ℕ) :
    Measurable fun ω : ℕ → ℝ => logPath α β ℓ₀ ω t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (measurable_const.add (ih.const_mul α)).add (measurable_pi_apply t)

/-- **`ln k_t` is independent of the current shock** under any product probability measure. -/
theorem indepFun_logPath {ν : Measure ℝ} [IsProbabilityMeasure ν] (α β ℓ₀ : ℝ) (t : ℕ) :
    IndepFun (fun ω => logPath α β ℓ₀ ω t) (fun ω => ω t)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  set c : ℕ → ℝ := fun s => if s < t then α ^ (t - 1 - s) else 1
  have hind : iIndepFun (fun s (ω : ℕ → ℝ) => c s * ω s) (Measure.infinitePi fun _ : ℕ => ν) :=
    iIndepFun_infinitePi (X := fun s x => c s * x) fun s => measurable_const.mul measurable_id
  have hmeas : ∀ s, Measurable fun ω : ℕ → ℝ => c s * ω s :=
    fun s => measurable_const.mul (measurable_pi_apply s)
  have hsum := hind.indepFun_finsetSum_of_notMem hmeas (s := range t) (i := t) (by simp)
  have h := hsum.comp (measurable_const_add (constPath α β ℓ₀ t)) measurable_id
  convert h using 1
  · funext ω
    simp only [Function.comp_apply, Finset.sum_apply, logPath_eq]
    congr 1
    refine sum_congr rfl fun s hs => ?_
    simp [c, mem_range.1 hs]
  · funext ω
    simp [c]

/-- The means `μ₀ = ℓ₀`, `μ_{t+1} = αμ_t + ln(αβ) + m`. -/
noncomputable def meanN (α β ℓ₀ m : ℝ) : ℕ → ℝ
  | 0 => ℓ₀
  | t + 1 => α * meanN α β ℓ₀ m t + log (α * β) + m

/-- `α²` as a nonnegative real. -/
noncomputable def sqNN (α : ℝ) : ℝ≥0 := ⟨α ^ 2, sq_nonneg α⟩

theorem coe_sqNN (α : ℝ) : (sqNN α : ℝ) = α ^ 2 := rfl

/-- The variances `σ₀² = 0`, `σ²_{t+1} = α²σ_t² + σ²`. -/
noncomputable def varN (α : ℝ) (v : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | t + 1 => sqNN α * varN α v t + v

/-- **Ex 2.7.** If the log shocks are i.i.d. `N(m, σ²)`, then `ln k_t ∼ N(μ_t, σ_t²)`. -/
theorem hasLaw_logPath (α β ℓ₀ m : ℝ) (v : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω => logPath α β ℓ₀ ω t) (gaussianReal (meanN α β ℓ₀ m t) (varN α v t))
      (Measure.infinitePi fun _ : ℕ => gaussianReal m v) := by
  set P := Measure.infinitePi fun _ : ℕ => gaussianReal m v
  induction t with
  | zero =>
    refine ⟨measurable_const.aemeasurable, ?_⟩
    simp only [logPath, meanN, varN, gaussianReal_zero_var]
    rw [Measure.map_const, measure_univ, one_smul]
  | succ t ih =>
    -- the two summands and their laws
    set X : (ℕ → ℝ) → ℝ := fun ω => log (α * β) + α * logPath α β ℓ₀ ω t
    set Y : (ℕ → ℝ) → ℝ := fun ω => ω t
    have hφ : Measurable fun x : ℝ => log (α * β) + α * x := measurable_const.add
      (measurable_const.mul measurable_id)
    have hX : HasLaw X (gaussianReal (α * meanN α β ℓ₀ m t + log (α * β))
        (sqNN α * varN α v t)) P := by
      refine ⟨(hφ.comp (measurable_logPath α β ℓ₀ t)).aemeasurable, ?_⟩
      have hmul : (P.map fun ω => logPath α β ℓ₀ ω t).map (fun x => α * x) =
          gaussianReal (α * meanN α β ℓ₀ m t) (sqNN α * varN α v t) := by
        rw [ih.map_eq, gaussianReal_map_const_mul]
        rfl
      have hmap' : P.map X = ((P.map fun ω => logPath α β ℓ₀ ω t).map (fun x => α * x)).map
          (fun x => x + log (α * β)) := by
        rw [Measure.map_map (measurable_add_const _) (measurable_const_mul α),
          Measure.map_map ((measurable_add_const _).comp (measurable_const_mul α))
            (measurable_logPath α β ℓ₀ t)]
        congr 1
        funext ω
        simp [X, add_comm]
      rw [hmap', hmul, gaussianReal_map_add_const]
    have hY : HasLaw Y (gaussianReal m v) P :=
      ⟨(measurable_pi_apply t).aemeasurable, Measure.infinitePi_map_eval _ t⟩
    have hXY : IndepFun X Y P := (indepFun_logPath (ν := gaussianReal m v) α β ℓ₀ t).comp hφ
      measurable_id
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
    have hfun : (fun ω => logPath α β ℓ₀ ω (t + 1)) = X + Y := by
      funext ω
      simp [X, Y, logPath]
    refine ⟨(measurable_logPath α β ℓ₀ (t + 1)).aemeasurable, ?_⟩
    rw [hfun, hsum]
    rfl

/-- **Ex 2.7.** `μ_t = αᵗ ln k₀ + (ln(αβ) + m)(1 − αᵗ)/(1 − α)`. -/
theorem meanN_eq {α β ℓ₀ m : ℝ} (hα1 : α < 1) (t : ℕ) :
    meanN α β ℓ₀ m t = α ^ t * ℓ₀ + (log (α * β) + m) * (1 - α ^ t) / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  induction t with
  | zero => simp [meanN]
  | succ t ih =>
    simp only [meanN, ih]
    field_simp
    ring

/-- **Ex 2.7.** `σ_t² = σ²(1 − α^{2t})/(1 − α²)`. -/
theorem varN_eq {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (v : ℝ≥0) (t : ℕ) :
    (varN α v t : ℝ) = v * (1 - (α ^ 2) ^ t) / (1 - α ^ 2) := by
  have h2 : (1 - α ^ 2) ≠ 0 := by nlinarith
  induction t with
  | zero => simp [varN]
  | succ t ih =>
    rw [varN, NNReal.coe_add, NNReal.coe_mul, coe_sqNN, ih]
    field_simp
    ring

/-- **Ex 2.7.** `μ_t → (ln(αβ) + m)/(1 − α)`. -/
theorem meanN_tendsto {α β ℓ₀ m : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (meanN α β ℓ₀ m) atTop (𝓝 ((log (α * β) + m) / (1 - α))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
  have := ((hp.mul_const ℓ₀).add (((tendsto_const_nhds (x := log (α * β) + m)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).div_const (1 - α)))
  simp only [zero_mul, zero_add, sub_zero, mul_one] at this
  refine this.congr fun t => ?_
  rw [meanN_eq hα1]

/-- **Ex 2.7.** `σ_t² → σ²/(1 − α²)`. -/
theorem varN_tendsto {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (v : ℝ≥0) :
    Tendsto (fun t => (varN α v t : ℝ)) atTop (𝓝 (v / (1 - α ^ 2))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg α) (by nlinarith : α ^ 2 < 1)
  have := ((tendsto_const_nhds (x := (v : ℝ))).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).div_const (1 - α ^ 2)
  simp only [sub_zero, mul_one] at this
  refine this.congr fun t => ?_
  rw [varN_eq hα0 hα1]

end StokeyLucasPrescott.Overview
