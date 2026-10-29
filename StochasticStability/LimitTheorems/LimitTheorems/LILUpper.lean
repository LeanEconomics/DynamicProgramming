/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.LILAnalysis
import LimitTheorems.LILExponential


/-!
# The upper half of the Hartman–Wintner LIL

For i.i.d. centred `Xⱼ ∈ L²` with `σ² = E[X₀²]`, almost surely `Sₙ ≤ (σ + ε) √(2 n log log n)`
eventually, for every `ε > 0` (`lil_upper`). This is the upper half of the i.i.d. LIL used for the
LIL parts of MT Theorems 17.2.2 and 17.3.6 (pp. 430, 441).

The proof is the classical truncation argument. The summands are truncated at
`τⱼ = δ √(j / log log j)` (`lilTrunc`, `lilTruncLevel`): the centred truncated parts are bounded,
and along the geometric blocks `n_k = ⌊θᵏ⌋` the exponential maximal inequality
(`exp_maximal_ineq`, `integral_exp_sum_le`) gives
`P(max_{n ≤ n_{k+1}} S'ₙ ≥ a √(2 n_k log log n_k)) ≤ (log n_k)^{−p}` with `p > 1`
(`lil_exponent_bound`), which is summable (Borel–Cantelli). The tails `X 1{|X| > τⱼ}` are
`o(√(n log log n))` a.s. by Kronecker's lemma, since
`Σⱼ E[|X| 1{|X| > τⱼ}]/√(j log log j) ≤ C E[X²] < ∞` (`summable_tail_div_lilWeight`).

* `lilTrunc`, `measurable_lilTrunc`, `abs_lilTrunc_le`, `lilTrunc_sq_le`, `abs_sub_lilTrunc`.
* `lilPhi_mono_nat`, `lilTruncLevel_nonneg`, `lilTruncLevel_mono`.
* `ae_summable_of_summable_integral`: non-negative series with summable means converge a.s.
* `tsum_measure_ne_top_of_summable`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Truncation -/

/-- The truncation `x ↦ x 1{|x| ≤ b}`. -/
noncomputable def lilTrunc (b x : ℝ) : ℝ := if |x| ≤ b then x else 0

/-- The truncation is measurable. -/
theorem measurable_lilTrunc (b : ℝ) : Measurable (lilTrunc b) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
    measurable_const

/-- `|x 1{|x| ≤ b}| ≤ b` for `b ≥ 0`. -/
theorem abs_lilTrunc_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |lilTrunc b x| ≤ b := by
  unfold lilTrunc
  split_ifs with h
  · exact h
  · rw [abs_zero]; exact hb

/-- `(x 1{|x| ≤ b})² ≤ x²`. -/
theorem lilTrunc_sq_le (b x : ℝ) : lilTrunc b x ^ 2 ≤ x ^ 2 := by
  unfold lilTrunc
  split_ifs
  · exact le_rfl
  · rw [sq (0 : ℝ), mul_zero]; exact sq_nonneg x

/-- `|x − x 1{|x| ≤ b}| = |x| 1{|x| > b}`. -/
theorem abs_sub_lilTrunc (b x : ℝ) :
    |x - lilTrunc b x| = if b < |x| then |x| else 0 := by
  unfold lilTrunc
  by_cases h : |x| ≤ b
  · simp only [h, ite_true, not_lt.2 h, ite_false, sub_self, abs_zero]
  · simp only [h, ite_false, not_le.1 h, ite_true, sub_zero]

/-! ### Monotonicity of the truncation levels -/

/-- `φ` is monotone on the integers beyond `j₀` when `log j₀ ≥ 3`. -/
theorem lilPhi_mono_nat {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) {i j : ℕ} (hi : j₀ ≤ i)
    (hij : i ≤ j) : lilPhi i ≤ lilPhi j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h3 := three_le_log_of_le hj₀ (hi.trans hij)
    have h1 := one_le_of_three_le_log (Nat.cast_nonneg _) h3
    obtain ⟨h4, -⟩ := lilPhi_increment h1 h3
    have h5 : 0 < Real.log (Real.log ((j : ℝ) + 1)) := by
      have := (loglog_increment h1 h3).1
      have := one_le_loglog h3
      linarith
    have h6 : 0 < 1 / (2 * Real.log (Real.log ((j : ℝ) + 1))) := by positivity
    push_cast
    linarith

/-- The truncation levels are non-negative. -/
theorem lilTruncLevel_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j₀ j : ℕ) : 0 ≤ lilTruncLevel δ j₀ j :=
  mul_nonneg hδ (Real.sqrt_nonneg _)

/-- The truncation levels are monotone. -/
theorem lilTruncLevel_mono {δ : ℝ} (hδ : 0 ≤ δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) :
    Monotone (lilTruncLevel δ j₀) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (lilPhi_mono_nat hj₀ (le_max_right i j₀)
    (max_le_max hij le_rfl))) hδ

/-! ### The exponent of the block estimate -/

/-- The exponent in the block estimate of the upper half: with `t = a √(2 M L_M)`,
`λ = t/(N s²)` and `C = 2 δ √(N/L_N)`, `λ C ≤ 2√2 a δ/s²`, and when this is at most `1`,
`−λt + N λ² s² (1 + λC)/2 ≤ −(a²/(θ²s²)) (1 − 2√2 aδ/s²) L_M` for `M ≤ N ≤ θ² M` and
`1 ≤ L_M ≤ L_N`. -/
theorem lil_exponent_bound {a s δ θ M N LM LN : ℝ} (ha : 0 < a) (hs : 0 < s) (hδ : 0 < δ)
    (hθ : 0 < θ) (hM : 0 < M) (hMN : M ≤ N) (hNM : N ≤ θ ^ 2 * M) (hLM : 1 ≤ LM)
    (hLN : LM ≤ LN) :
    (a * √(2 * M * LM) / (N * s ^ 2)) * (2 * (δ * √(N / LN))) ≤ 2 * √2 * a * δ / s ^ 2 ∧
      (2 * √2 * a * δ / s ^ 2 ≤ 1 →
        -((a * √(2 * M * LM) / (N * s ^ 2)) * (a * √(2 * M * LM))) +
          N * ((a * √(2 * M * LM) / (N * s ^ 2)) ^ 2 * s ^ 2 *
            (1 + (a * √(2 * M * LM) / (N * s ^ 2)) * (2 * (δ * √(N / LN)))) / 2) ≤
          -((a ^ 2 / (θ ^ 2 * s ^ 2)) * (1 - 2 * √2 * a * δ / s ^ 2) * LM)) := by
  have hN : 0 < N := hM.trans_le hMN
  have hLN0 : 0 < LN := by linarith
  set t := a * √(2 * M * LM) with ht
  set l := t / (N * s ^ 2) with hl
  set C := 2 * (δ * √(N / LN)) with hC
  set η := 2 * √2 * a * δ / s ^ 2 with hη
  have ht0 : 0 ≤ t := by positivity
  have hl0 : 0 ≤ l := by positivity
  -- `λC ≤ η`
  have hlC : l * C ≤ η := by
    have hsq : √(2 * M * LM) * √(N / LN) ≤ √2 * N := by
      rw [← Real.sqrt_mul (by positivity)]
      have h1 : 2 * M * LM * (N / LN) ≤ 2 * N ^ 2 := by
        have h2 : LM / LN ≤ 1 := (div_le_one hLN0).2 hLN
        have h3 : M * (LM / LN) ≤ N := by
          calc M * (LM / LN) ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM.le
            _ ≤ N := by linarith
        have e : 2 * M * LM * (N / LN) = 2 * N * (M * (LM / LN)) := by ring
        rw [e]
        nlinarith
      calc √(2 * M * LM * (N / LN)) ≤ √(2 * N ^ 2) := Real.sqrt_le_sqrt h1
        _ = √2 * N := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hN.le]
    have e : l * C = 2 * a * δ / (N * s ^ 2) * (√(2 * M * LM) * √(N / LN)) := by
      rw [hl, hC, ht]; ring
    rw [e, hη]
    calc 2 * a * δ / (N * s ^ 2) * (√(2 * M * LM) * √(N / LN))
        ≤ 2 * a * δ / (N * s ^ 2) * (√2 * N) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * √2 * a * δ / s ^ 2 := by field_simp
  refine ⟨hlC, fun hη1 => ?_⟩
  -- `λ t = N λ² s² = q`
  set q := t ^ 2 / (N * s ^ 2) with hq
  have e1 : l * t = q := by rw [hl, hq]; ring
  have e2 : N * (l ^ 2 * s ^ 2) = q := by rw [hl, hq]; field_simp
  have e3 : -(l * t) + N * (l ^ 2 * s ^ 2 * (1 + l * C) / 2) = -(q * (1 - l * C) / 2) := by
    have : N * (l ^ 2 * s ^ 2 * (1 + l * C) / 2) = N * (l ^ 2 * s ^ 2) * (1 + l * C) / 2 := by
      ring
    rw [this, e1, e2]; ring
  rw [e3]
  have ht2 : t ^ 2 = a ^ 2 * (2 * M * LM) := by
    rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
  have hq2 : a ^ 2 * LM / (θ ^ 2 * s ^ 2) ≤ q / 2 := by
    have e4 : q / 2 = a ^ 2 * M * LM / (N * s ^ 2) := by rw [hq, ht2]; ring
    rw [e4, div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : 0 ≤ a ^ 2 * LM * s ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hNM h5
    nlinarith
  have h6 : 0 ≤ 1 - η := by linarith
  have h7 : 1 - η ≤ 1 - l * C := by linarith
  have h8 : 0 ≤ a ^ 2 * LM / (θ ^ 2 * s ^ 2) := by positivity
  have h9 := mul_le_mul hq2 h7 h6 (h8.trans hq2)
  have e5 : a ^ 2 / (θ ^ 2 * s ^ 2) * (1 - η) * LM = a ^ 2 * LM / (θ ^ 2 * s ^ 2) * (1 - η) := by
    ring
  rw [e5]
  linarith

/-! ### Summability of the truncated tails -/

/-- The truncated tails are summable against the weights: for `X ∈ L²`,
`Σⱼ E[|X| 1{|X| > τⱼ}]/wⱼ < ∞`. -/
theorem summable_tail_div_lilWeight {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Z : Ω → ℝ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 Q) {δ : ℝ}
    (hδ : 0 < δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) :
    Summable fun j => (∫ ω, |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| ∂Q) / lilWeight j₀ j := by
  set K := (j₀ : ℝ) / lilWeight j₀ j₀ with hK
  have hZi : Integrable Z Q := hZ2.integrable one_le_two
  have hZ2i : Integrable (fun ω => Z ω ^ 2) Q := hZ2.integrable_sq
  have hbdi : Integrable (fun ω => |Z ω| * (K + 8 * (|Z ω| / δ + 1))) Q := by
    have e : (fun ω => |Z ω| * (K + 8 * (|Z ω| / δ + 1))) =
        fun ω => (K + 8) * |Z ω| + (8 / δ) * Z ω ^ 2 := by
      ext ω; rw [← sq_abs (Z ω)]; field_simp; ring
    rw [e]
    exact (hZi.abs.const_mul _).add (hZ2i.const_mul _)
  have hti : ∀ j, Integrable (fun ω => |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)|) Q :=
    fun j => (hZi.sub (Integrable.of_bound ((measurable_lilTrunc _).comp hZm).aestronglyMeasurable
      (lilTruncLevel δ j₀ j) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_lilTrunc_le (lilTruncLevel_nonneg hδ.le j₀ j) _))).abs
  refine summable_of_sum_range_le (c := ∫ ω, |Z ω| * (K + 8 * (|Z ω| / δ + 1)) ∂Q)
    (fun j => div_nonneg (integral_nonneg fun ω => abs_nonneg _) (lilWeight_pos hj₀ j).le)
    fun n => ?_
  have e1 : ∑ j ∈ Finset.range n,
      (∫ ω, |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| ∂Q) / lilWeight j₀ j =
      ∫ ω, ∑ j ∈ Finset.range n,
        |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| / lilWeight j₀ j ∂Q := by
    rw [integral_finsetSum _ fun j _ => (hti j).div_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_div]
  rw [e1]
  refine integral_mono (integrable_finsetSum _ fun j _ => (hti j).div_const _) hbdi
    fun ω => ?_
  have hpt : ∀ j, |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| / lilWeight j₀ j =
      |Z ω| * (if lilTruncLevel δ j₀ j < |Z ω| then 1 / lilWeight j₀ j else 0) := fun j => by
    rw [abs_sub_lilTrunc]
    split_ifs
    · ring
    · rw [zero_div, mul_zero]
  simp only
  simp_rw [hpt]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_inv_lilWeight_le hδ hj₀ (abs_nonneg _) n)
    (abs_nonneg _)

/-- Non-negative random series with summable means converge almost surely. -/
theorem ae_summable_of_summable_integral {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {f : ℕ → Ω → ℝ} (hm : ∀ j, Measurable (f j)) (h0 : ∀ j ω, 0 ≤ f j ω)
    (hi : ∀ j, Integrable (f j) Q) (hs : Summable fun j => ∫ ω, f j ω ∂Q) :
    ∀ᵐ ω ∂Q, Summable fun j => f j ω := by
  have h1 : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂Q = ∑' j, ENNReal.ofReal (∫ ω, f j ω ∂Q) := by
    rw [lintegral_tsum fun j => (hm j).ennreal_ofReal.aemeasurable]
    congr 1
    ext j
    rw [ofReal_integral_eq_lintegral_ofReal (hi j) (ae_of_all _ (h0 j))]
  have h2 : ∑' j, ENNReal.ofReal (∫ ω, f j ω ∂Q) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (h0 j)) hs]
    exact ENNReal.ofReal_ne_top
  have h3 := ae_lt_top' (AEMeasurable.tsum fun j => (hm j).ennreal_ofReal.aemeasurable)
    (h1 ▸ h2)
  filter_upwards [h3] with ω hω
  exact (ENNReal.summable_toReal hω.ne).congr fun j => ENNReal.toReal_ofReal (h0 j ω)

/-- For a finite measure, summable real measures have finite `ENNReal` sum. -/
theorem tsum_measure_ne_top_of_summable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {B : ℕ → Set Ω} (h : Summable fun k => Q.real (B k)) :
    ∑' k, Q (B k) ≠ ∞ := by
  have e : ∀ k, Q (B k) = ENNReal.ofReal (Q.real (B k)) := fun k =>
    (ofReal_measureReal (μ := Q) (s := B k)).symm
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg) h]
  exact ENNReal.ofReal_ne_top

/-! ### The upper half of the LIL -/

/-- **The upper half of the Hartman–Wintner LIL**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ² = E[X₀²]` and every `ε > 0`, almost surely `Sₙ ≤ (σ + ε) √(2 n log log n)` eventually. -/
theorem lil_upper {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Q, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, X j ω ≤ (√(∫ ω, X 0 ω ^ 2 ∂Q) + ε) * lilScale n := by
  set σ := √(∫ ω, X 0 ω ^ 2 ∂Q) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∫ ω, X 0 ω ^ 2 ∂Q :=
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
  have hXL2 : ∀ j, MemLp (X j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  have hXi : ∀ j, Integrable (X j) Q := fun j => (hXL2 j).integrable one_le_two
  have hTi : ∀ j i, Integrable (fun ω => lilTrunc (β j) (X i ω)) Q := fun j i =>
    Integrable.of_bound ((measurable_lilTrunc _).comp (hm i)).aestronglyMeasurable (β j)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_lilTrunc_le (hβ0 j) _)
  have hTeq : ∀ j, ∫ ω, lilTrunc (β j) (X j ω) ∂Q = ∫ ω, lilTrunc (β j) (X 0 ω) ∂Q := fun j =>
    ((hident j).comp (measurable_lilTrunc (β j))).integral_eq
  set μt : ℕ → ℝ := fun j => ∫ ω, lilTrunc (β j) (X 0 ω) ∂Q with hμt
  set Y : ℕ → Ω → ℝ := fun j ω => lilTrunc (β j) (X j ω) - μt j with hY
  have hYm : ∀ j, Measurable (Y j) := fun j => ((measurable_lilTrunc _).comp (hm j)).sub_const _
  have hYind : iIndepFun Y Q :=
    hind.comp (fun j x => lilTrunc (β j) x - μt j) fun j => (measurable_lilTrunc _).sub_const _
  have hμb : ∀ j, |μt j| ≤ β j := fun j => by
    calc |μt j| ≤ ∫ ω, |lilTrunc (β j) (X 0 ω)| ∂Q := abs_integral_le_integral_abs
      _ ≤ ∫ _ω, β j ∂Q := integral_mono (hTi j 0).abs (integrable_const _) fun ω =>
          abs_lilTrunc_le (hβ0 j) _
      _ = β j := by simp
  have hYb : ∀ j ω, |Y j ω| ≤ 2 * β j := fun j ω => by
    have h1 := abs_lilTrunc_le (hβ0 j) (X j ω)
    have h2 := hμb j
    calc |Y j ω| ≤ |lilTrunc (β j) (X j ω)| + |μt j| := abs_sub _ _
      _ ≤ 2 * β j := by linarith
  have hY0 : ∀ j, ∫ ω, Y j ω ∂Q = 0 := fun j => by
    simp only [hY]
    rw [integral_sub (hTi j j) (integrable_const _), integral_const, probReal_univ, one_smul,
      hTeq j, sub_self]
  have hY2 : ∀ j, ∫ ω, Y j ω ^ 2 ∂Q ≤ s ^ 2 := fun j => by
    have hT2i : Integrable (fun ω => lilTrunc (β j) (X j ω) ^ 2) Q :=
      Integrable.of_bound (((measurable_lilTrunc _).comp (hm j)).pow_const 2).aestronglyMeasurable
        (β j ^ 2) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_lilTrunc_le (hβ0 j) _) 2)
    have hexp : ∫ ω, Y j ω ^ 2 ∂Q = ∫ ω, lilTrunc (β j) (X j ω) ^ 2 ∂Q - μt j ^ 2 := by
      have e : (fun ω => Y j ω ^ 2) = fun ω => lilTrunc (β j) (X j ω) ^ 2 +
          (-(2 * μt j) * lilTrunc (β j) (X j ω) + μt j ^ 2) := by
        ext ω; simp only [hY]; ring
      have hA : Integrable (fun ω => -(2 * μt j) * lilTrunc (β j) (X j ω) + μt j ^ 2) Q :=
        ((hTi j j).const_mul _).add (integrable_const _)
      rw [e, integral_add hT2i hA,
        integral_add ((hTi j j).const_mul _) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul, hTeq j]
      ring
    have h1 : ∫ ω, lilTrunc (β j) (X j ω) ^ 2 ∂Q ≤ ∫ ω, X j ω ^ 2 ∂Q :=
      integral_mono hT2i (hXL2 j).integrable_sq fun ω => lilTrunc_sq_le _ _
    have h2 : ∫ ω, X j ω ^ 2 ∂Q = σ ^ 2 := by
      rw [hσ2]; exact ((hident j).comp (measurable_id.pow_const 2)).integral_eq
    have h3 : σ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hσ0 (by linarith) 2
    nlinarith [sq_nonneg (μt j)]
  -- the geometric blocks
  set nk : ℕ → ℕ := fun k => ⌊θ ^ k⌋₊ with hnk
  have hnk_mono : Monotone nk := fun i j hij =>
    Nat.floor_mono (pow_le_pow_right₀ hθ1.le hij)
  have hnk_t : Tendsto nk atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hθ1)
  set B : ℕ → Set Ω := fun k =>
    {ω | ∃ n ≤ nk (k + 1), a * lilScale (nk k) ≤ ∑ j ∈ Finset.range n, Y j ω} with hB
  have hBbound : ∀ᶠ k in atTop, Q.real (B k) ≤
      Real.exp (-(p * Real.log (Real.log (nk k : ℝ)))) := by
    filter_upwards [hnk_t.eventually (eventually_le_log 3), eventually_floor_pow_succ_le hθ1,
      hnk_t.eventually_ge_atTop j₀] with k hk3 hkθ hkj
    set M := nk k with hM
    set N := nk (k + 1) with hN
    have hMN : M ≤ N := hnk_mono (Nat.le_succ k)
    have hN3 : 3 ≤ Real.log N := three_le_log_of_le hk3 hMN
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
    have hmax := exp_maximal_ineq hYind hYm hYb hY0 N (l := l) (t := t) hl0
    have hsum := integral_exp_sum_le hYind hYm hYb hY0 N (l := l) (C := 2 * β N)
      (s2 := s ^ 2) hl0 (fun j hj => by have := hβm hj.le; linarith)
      (by rw [hβN]; linarith) (fun j _ => hY2 j)
    have h1 : Real.exp (l * t) * Q.real (B k) ≤
        Real.exp (N * (l ^ 2 * s ^ 2 * (1 + l * (2 * β N)) / 2)) := by
      refine le_trans (le_of_eq ?_) (hmax.trans hsum)
      rfl
    rw [hβN] at h1
    have h2 : Q.real (B k) ≤ Real.exp (-(l * t) + N * (l ^ 2 * s ^ 2 *
        (1 + l * (2 * (δ * √(N / Real.log (Real.log N))))) / 2)) := by
      rw [Real.exp_add, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _),
        mul_comm]
      exact h1
    exact h2.trans (Real.exp_le_exp.2 hexp')
  -- Borel–Cantelli
  have hsumB : Summable fun k => Q.real (B k) :=
    (summable_exp_neg_mul_loglog_floor_pow hθ1 hp1).of_norm_bounded_eventually_nat (by
      filter_upwards [hBbound] with k hk
      rwa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg])
  have hBC : ∀ᵐ ω ∂Q, ∀ᶠ k in atTop, ω ∉ B k :=
    ae_eventually_notMem (tsum_measure_ne_top_of_summable hsumB)
  -- the tails and Kronecker's lemma
  set w : ℕ → ℝ := lilWeight j₀ with hw
  set e : ℕ → ℝ := fun j => ∫ ω, |X 0 ω - lilTrunc (β j) (X 0 ω)| ∂Q with he
  set A : ℕ → Ω → ℝ := fun j ω => |X j ω - lilTrunc (β j) (X j ω)| + e j with hA
  have hDi : ∀ j i, Integrable (fun ω => |X i ω - lilTrunc (β j) (X i ω)|) Q := fun j i =>
    ((hXi i).sub (hTi j i)).abs
  have hDeq : ∀ j, ∫ ω, |X j ω - lilTrunc (β j) (X j ω)| ∂Q = e j := fun j =>
    ((hident j).comp (u := fun x => |x - lilTrunc (β j) x|)
      (continuous_abs.measurable.comp (measurable_id.sub (measurable_lilTrunc _)))).integral_eq
  have he0 : ∀ j, 0 ≤ e j := fun j => integral_nonneg fun ω => abs_nonneg _
  have hsumA : Summable fun j => ∫ ω, A j ω / w j ∂Q := by
    have := (summable_tail_div_lilWeight (hm 0) hL2 hδ0 hj₀).mul_left 2
    refine this.congr fun j => ?_
    rw [integral_div, hA]
    simp only
    rw [integral_add (hDi j j) (integrable_const _), hDeq, integral_const, probReal_univ,
      one_smul]
    ring
  have hAm : ∀ j, Measurable fun ω => A j ω / w j := fun j =>
    ((continuous_abs.measurable.comp ((hm j).sub ((measurable_lilTrunc _).comp
      (hm j)))).add_const _).div_const _
  have hA0 : ∀ j ω, 0 ≤ A j ω / w j := fun j ω =>
    div_nonneg (add_nonneg (abs_nonneg _) (he0 j)) (lilWeight_pos hj₀ j).le
  have hAi : ∀ j, Integrable (fun ω => A j ω / w j) Q := fun j =>
    ((hDi j j).add (integrable_const _)).div_const _
  have hKr := ae_summable_of_summable_integral hAm hA0 hAi hsumA
  have hμe : ∀ j, |μt j| ≤ e j := fun j => by
    have e1 : μt j = -∫ ω, (X 0 ω - lilTrunc (β j) (X 0 ω)) ∂Q := by
      rw [integral_sub (hXi 0) (hTi j 0), h0]; simp [hμt]
    rw [e1, abs_neg]
    exact abs_integral_le_integral_abs
  filter_upwards [hBC, hKr] with ω hωB hωK
  have hW := tendsto_sum_div_of_summable (a := fun j => A j ω) (w := w)
    (fun j => add_nonneg (abs_nonneg _) (he0 j)) (lilWeight_pos hj₀) (lilWeight_mono hj₀)
    tendsto_lilWeight hωK
  have hW' : ∀ᶠ n in atTop, ∑ j ∈ Finset.range n, A j ω ≤ ε / 4 * w n := by
    filter_upwards [hW.eventually (eventually_le_nhds (show (0 : ℝ) < ε / 4 by positivity))]
      with n hn
    rwa [div_le_iff₀ (lilWeight_pos hj₀ n)] at hn
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 hωB
  obtain ⟨K2, hK2⟩ := eventually_atTop.1 ((hnk_t.eventually (eventually_le_log 3)).and
    (eventually_ge_atTop (K1 + 1)))
  filter_upwards [hW', eventually_gt_atTop (nk K2), eventually_ge_atTop j₀] with n hnW hnK hnj
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
    have h := hK1 k (by omega)
    simp only [hB, mem_ofPred_eq, not_exists, not_and, not_le] at h
    exact h n hkn
  have hlil : lilScale (nk k) ≤ lilScale n := lilScale_mono h3 hnk_lt.le
  -- the tails
  have hdiff : ∑ j ∈ Finset.range n, X j ω - ∑ j ∈ Finset.range n, Y j ω ≤
      ∑ j ∈ Finset.range n, A j ω := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have e1 : X j ω - Y j ω = (X j ω - lilTrunc (β j) (X j ω)) + μt j := by
      simp only [hY]; ring
    rw [e1]
    have := le_abs_self (X j ω - lilTrunc (β j) (X j ω))
    have := (abs_le.1 (hμe j)).2
    simp only [hA]
    linarith
  have hwl : w n ≤ lilScale n := by
    rw [lilScale_eq_lilWeight hnj]
    have h1 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h2 := (lilWeight_pos hj₀ n).le
    nlinarith
  have hfin : a * lilScale n + ε / 4 * lilScale n = (σ + ε) * lilScale n := by
    rw [ha]; ring
  have h4 : ε / 4 * w n ≤ ε / 4 * lilScale n :=
    mul_le_mul_of_nonneg_left hwl (by positivity)
  have h5 : a * lilScale (nk k) ≤ a * lilScale n := mul_le_mul_of_nonneg_left hlil ha0.le
  linarith

end MeynTweedie.LimitTheorems
