/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.FNormErgodicTheorem
import GeometricErgodicity.StochasticComparison
import GeometricErgodicity.ModelNonlinearModels

/-!
# `f`-ergodicity of specific models (MT §14.4) and the drift (V4′) (MT §14.6)

Meyn and Tweedie, §14.4, pp. 352–354, and Proposition 14.6.1, p. 361.

**Random walk on a half line** (§14.4.1). `halfLineWalkKernel Γ` is `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺`, and
`f_i(x) = xⁱ + 1`.
* `max_add_pow_le`, `max_add_pow_le_two_pow`, `integral_add_pow`, `integral_max_add_pow_le`,
  `lintegral_halfLine_pow`: the moment calculations (14.28) behind the drift.
* `halfLine_drift_pow`: for one power `j ≥ 1`, `P V_j ≤ V_j − c f_{j−1} + d 1_{[0, X₀]}` when
  `E[W] < 0` and `E|W|ʲ < ∞`.
* `halfLine_drift_14_29`: **(14.29)**, simultaneously for all `i ≤ k`.
* **Proposition 14.4.1** (`proposition_14_4_1`, p. 352): with `E[W] < 0` and
  `E|W|^{k+1} < ∞`, the walk is `ψ`-irreducible, aperiodic, positive Harris and `f_k`-regular;
  every invariant probability has a finite `k`-th moment; (i) `‖Pⁿ(x, ·) − π‖_{f_k} → 0` for every
  `x`, and `‖λPⁿ − π‖_{f_k} → 0` for every initial law with `∫ x^{k+1} dλ < ∞`; (ii) for `k ≥ 1`,
  `Σₙ ∫ λ(dx) ‖Pⁿ(x, ·) − π‖_{f_{k−1}} ≤ B (1 + ∫ xᵏ dλ)` for every initial law `λ`.

**The bilinear model** (§14.4.2). `bilinearKernel Γ θ b` is `Xₙ₊₁ = θXₙ + bXₙWₙ₊₁ + Wₙ₊₁`.
* `bilinear_lintegral_pow_le`: Minkowski's inequality
  `E|θx + bxW + W|ᵏ ≤ (‖θ + bW‖_k |x| + ‖W‖_k)ᵏ` for `k ≥ 1`.
* `bilinear_real_drift`, `bilinear_driftV3`: (V3) with `V = a|x|ᵏ`, `f = |x|ᵏ + 1` and a compact
  `C = [−R, R]`, when `E|W|ᵏ < ∞` and `E|θ + bW|ᵏ < 1`.
* `bilinear_moment_two` ((14.31), with equality): `E|θ + bW|² = θ² + b² E W²` for centred `W`;
  `bilinear_condition_14_32`: under (14.32), `θ² + b² E W² < 1`, the hypotheses of
  Proposition 14.4.2 hold with `k = 2`, so (V3) holds with `f = 1 + δV`, `V(x) = x²`.
* **Proposition 14.4.2**, corrected (`proposition_14_4_2`, p. 354): with `E|W|ᵏ < ∞` (14.33)
  and `E|θ + bW|ᵏ < 1`, for a `ψ`-irreducible aperiodic chain whose compact sets are petite:
  positive Harris, `∫ |x|ᵏ dπ < ∞` and `‖Pⁿ(x, ·) − π‖_{|x|ᵏ+1} → 0` for every `x`.

**The Jarner–Roberts drift (V4′) with `ε = ½`** (§14.6, commentary for the second edition).
* `lintegral_sqrt_le`: Jensen's inequality `∫ √V dρ ≤ √(∫ V dρ)` for a probability `ρ` (Hölder
  with `p = q = 2`).
* `sqrt_add_half_le`: the scalar step `√w + β/2 ≤ √v + b/2` when `w + β√v ≤ v + b` and `v ≥ 1`
  (concavity of the square root, `√y ≤ √v + (y − v)/(2√v)`).
* **Proposition 14.6.1** (`proposition_14_6_1`, p. 361): for a `ψ`-irreducible aperiodic chain,
  if `PV ≤ V − β V^{1/2} + b 1_C` with `V ≥ 1`, `C` petite and `V` finite at some `x₀`, then
  `U = 2β⁻¹ V^{1/2}` satisfies Foster's criterion, `π(V^{1/2}) ≤ β⁻¹ b π(C)`, and
  `Σₙ ‖Pⁿ(x, ·) − π‖ ≤ B₁ V(x)^{1/2}` for every `x` (14.52).

**Corrections.**
* Proposition 14.4.2 as printed assumes only (SBL1), (SBL2) and `E[Wᵏ] < ∞`, with no stability
  condition, and is false: `proposition_14_4_2_counterexample` takes `W` uniform on `(−1, 1)`
  (`uniformPM1`: a lower semicontinuous density, mean `0`, all moments finite) and `θ = 2`,
  `b = 0`, the AR(1) model `Xₙ₊₁ = 2Xₙ + Wₙ₊₁`, which is not positive Harris for any `ψ`
  (Proposition 9.5.2). The corrected statement adds `E|θ + bW|ᵏ < 1`, which is (14.32) for
  `k = 2` and centred `W` (`bilinear_condition_14_32`).

**Hypotheses.** In Proposition 14.4.2, `ψ`-irreducibility, aperiodicity and the petiteness of
compact sets are assumed: the book obtains them from (SBL2) through the T-chain property
(Proposition 7.1.3, Theorem 6.2.5), which is not formalised for the bilinear model here. The
moment condition is `E|W|ᵏ < ∞`, as `E[Wᵏ]` in (14.33) must mean.
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal

/-! ### Proposition 14.6.1 -/

variable {X : Type*} [MeasurableSpace X]

/-- **Jensen's inequality for the square root**: `∫ V^{1/2} dρ ≤ (∫ V dρ)^{1/2}` for a
probability `ρ`. -/
theorem lintegral_sqrt_le (ρ : Measure X) [IsProbabilityMeasure ρ] {V : X → ℝ≥0∞}
    (hV : Measurable V) : ∫⁻ x, V x ^ (2⁻¹ : ℝ) ∂ρ ≤ (∫⁻ x, V x ∂ρ) ^ (2⁻¹ : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two
    (f := fun x => V x ^ (2⁻¹ : ℝ)) (g := 1) (hV.pow_const _).aemeasurable
    measurable_const.aemeasurable
  have e1 : ∀ x, (V x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = V x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  simp only [Pi.mul_apply, Pi.one_apply, mul_one, e1, ENNReal.one_rpow, lintegral_one,
    measure_univ] at h
  convert h using 1
  norm_num

/-- The scalar step of Proposition 14.6.1: if `0 ≤ w`, `1 ≤ v` and `w + β √v ≤ v + c` with
`β, c ≥ 0`, then `√w + β/2 ≤ √v + c/2` (concavity of the square root). -/
theorem sqrt_add_half_le {v w β c : ℝ} (hw : 0 ≤ w) (hv : 1 ≤ v) (hc : 0 ≤ c)
    (h : w + β * Real.sqrt v ≤ v + c) : Real.sqrt w + β / 2 ≤ Real.sqrt v + c / 2 := by
  set s := Real.sqrt v with hs
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact hv
  have hss : s * s = v := Real.mul_self_sqrt (by linarith)
  have hww : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw
  have key : Real.sqrt w * (2 * s) ≤ w + v := by
    nlinarith [sq_nonneg (Real.sqrt w - s)]
  have hconc : Real.sqrt w ≤ (w + v) / (2 * s) := (le_div_iff₀ (by positivity)).2 key
  have hcs : c ≤ c * s := by nlinarith
  have h4 : (w + v) / (2 * s) ≤ s + c / 2 - β / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `x^{1/2} = ofReal √(x.toReal)` for a finite `x`. -/
theorem rpow_half_eq_ofReal_sqrt {x : ℝ≥0∞} (hx : x ≠ ∞) :
    x ^ (2⁻¹ : ℝ) = ENNReal.ofReal (Real.sqrt x.toReal) := by
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hx]
  norm_num

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 14.6.1** (MT p. 361): let the chain be `ψ`-irreducible and aperiodic and let
`V ≥ 1` satisfy the Jarner–Roberts drift (V4′) with `ε = ½`, `PV ≤ V − β V^{1/2} + b 1_C`, for a
petite `C`, `0 < β < ∞`, `b < ∞`, with `V(x₀) < ∞` for some `x₀`. Then
(i) `U = 2β⁻¹ V^{1/2}` satisfies Foster's criterion `PU ≤ U − 1 + β⁻¹ b 1_C`;
(ii) every invariant probability has `π(V^{1/2}) ≤ β⁻¹ b π(C)`;
(iii) (14.52): there is `B₁ < ∞` with `Σₙ ‖Pⁿ(x, ·) − π‖ ≤ B₁ V(x)^{1/2}` for every `x`. -/
theorem proposition_14_6_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {β b : ℝ≥0∞} (hβ0 : β ≠ 0) (hβ : β ≠ ∞)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C)
    (hdrift : ∀ x, ∫⁻ y, V y ∂P x + β * V x ^ (2⁻¹ : ℝ) ≤ V x + C.indicator (fun _ => b) x)
    {x₀ : X} (hx₀ : V x₀ ≠ ∞) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    DriftV2 P (fun x => 2 * β⁻¹ * V x ^ (2⁻¹ : ℝ)) (β⁻¹ * b) C ∧
      ∫⁻ x, V x ^ (2⁻¹ : ℝ) ∂π ≤ β⁻¹ * b * π C ∧
      ∃ B₁ : ℝ≥0∞, B₁ ≠ ∞ ∧ ∀ x,
        ∑' n, ENNReal.ofReal (tvNorm ((P ^ n : Kernel X X) x) π) ≤ B₁ * V x ^ (2⁻¹ : ℝ) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  set U : X → ℝ≥0∞ := fun x => 2 * β⁻¹ * V x ^ (2⁻¹ : ℝ) with hU
  have hUm : Measurable U := measurable_const.mul (hV.pow_const _)
  have hβi : β⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hβ0
  have hβi0 : β⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hβ
  -- (i) Foster's criterion for `U`
  have hfoster : DriftV2 P U (β⁻¹ * b) C := fun x => by
    by_cases hVx : V x = ∞
    · have : U x = ∞ := by
        simp only [hU, hVx, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
        exact ENNReal.mul_top (mul_ne_zero two_ne_zero hβi0)
      rw [this, top_add]; exact le_top
    set I := C.indicator (fun _ => b) x with hI
    have hIne : I ≠ ∞ := by rw [hI]; by_cases hx : x ∈ C <;> simp [hx, hb]
    have hPV : ∫⁻ y, V y ∂P x ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hVx, hIne⟩)
      (le_self_add.trans (hdrift x))
    -- the real inequality
    have hreal : (∫⁻ y, V y ∂P x).toReal + β.toReal * Real.sqrt (V x).toReal ≤
        (V x).toReal + I.toReal := by
      have h1 := hdrift x
      rw [rpow_half_eq_ofReal_sqrt hVx] at h1
      have h2 := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hPV, ENNReal.mul_ne_top hβ
        ENNReal.ofReal_ne_top⟩) (ENNReal.add_ne_top.2 ⟨hVx, hIne⟩)).2 h1
      rwa [ENNReal.toReal_add hPV (ENNReal.mul_ne_top hβ ENNReal.ofReal_ne_top),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
        ENNReal.toReal_add hVx hIne] at h2
    have hv1 : 1 ≤ (V x).toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hVx).2 (hV1 x)
      rwa [ENNReal.toReal_one] at this
    have hstep := sqrt_add_half_le ENNReal.toReal_nonneg hv1 ENNReal.toReal_nonneg hreal
    -- back to `[0, ∞]`
    have hE : (∫⁻ y, V y ∂P x) ^ (2⁻¹ : ℝ) + β / 2 ≤ V x ^ (2⁻¹ : ℝ) + I / 2 := by
      rw [rpow_half_eq_ofReal_sqrt hPV, rpow_half_eq_ofReal_sqrt hVx]
      have h3 := ENNReal.ofReal_le_ofReal hstep
      rwa [ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity),
        ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity),
        ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_toReal hβ, ENNReal.ofReal_toReal hIne, ENNReal.ofReal_ofNat] at h3
    have hjen := lintegral_sqrt_le (P x) hV
    have hscale : ∀ a : ℝ≥0∞, 2 * β⁻¹ * (a + β / 2) = 2 * β⁻¹ * a + 1 := fun a => by
      rw [mul_add, show 2 * β⁻¹ * (β / 2) = 1 by
        rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm (2 * β⁻¹), ← mul_assoc,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul,
          ENNReal.inv_mul_cancel hβ0 hβ]]
    have hscale' : 2 * β⁻¹ * (V x ^ (2⁻¹ : ℝ) + I / 2) =
        U x + C.indicator (fun _ => β⁻¹ * b) x := by
      rw [mul_add, hU]
      congr 1
      rw [hI]
      by_cases hx : x ∈ C
      · rw [indicator_of_mem hx, indicator_of_mem hx, ENNReal.div_eq_inv_mul]
        calc 2 * β⁻¹ * (2⁻¹ * b) = (2 * 2⁻¹) * (β⁻¹ * b) := by ring
          _ = β⁻¹ * b := by
              rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
    calc ∫⁻ y, U y ∂P x + 1 = 2 * β⁻¹ * ∫⁻ y, V y ^ (2⁻¹ : ℝ) ∂P x + 1 := by
          rw [hU, lintegral_const_mul _ (hV.pow_const _)]
      _ ≤ 2 * β⁻¹ * (∫⁻ y, V y ∂P x) ^ (2⁻¹ : ℝ) + 1 :=
          add_le_add (mul_le_mul' le_rfl hjen) le_rfl
      _ = 2 * β⁻¹ * ((∫⁻ y, V y ∂P x) ^ (2⁻¹ : ℝ) + β / 2) := (hscale _).symm
      _ ≤ 2 * β⁻¹ * (V x ^ (2⁻¹ : ℝ) + I / 2) := mul_le_mul' le_rfl hE
      _ = U x + C.indicator (fun _ => β⁻¹ * b) x := hscale'
  have hU1 : ∀ x, 1 ≤ (fun _ : X => (1 : ℝ≥0∞)) x := fun _ => le_rfl
  have hUx₀ : U x₀ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hβi)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hx₀)
  have hbU : β⁻¹ * b ≠ ∞ := ENNReal.mul_ne_top hβi hb
  -- the chain is positive
  obtain ⟨hpos, -⟩ := isPositive_of_driftV3 (f := fun _ => 1) hψ measurable_const hU1 hC hUm
    hbU hUx₀ hfoster
  -- (ii) `π(V^{1/2}) ≤ β⁻¹ b π(C)` by Theorem 14.3.7
  have hd3 : DriftV3 P V (fun x => β * V x ^ (2⁻¹ : ℝ)) b C := hdrift
  have hπV : ∫⁻ x, β * V x ^ (2⁻¹ : ℝ) ∂π ≤ b * π C :=
    lintegral_le_of_driftV3 hpos hπ hV (measurable_const.mul (hV.pow_const _)) hb hCm hd3 hx₀
  have hπs : ∫⁻ x, V x ^ (2⁻¹ : ℝ) ∂π ≤ β⁻¹ * b * π C := by
    rw [lintegral_const_mul _ (hV.pow_const _)] at hπV
    calc ∫⁻ x, V x ^ (2⁻¹ : ℝ) ∂π = β⁻¹ * (β * ∫⁻ x, V x ^ (2⁻¹ : ℝ) ∂π) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hβ0 hβ, one_mul]
      _ ≤ β⁻¹ * (b * π C) := mul_le_mul' le_rfl hπV
      _ = β⁻¹ * b * π C := by ring
  refine ⟨hfoster, hπs, ?_⟩
  -- (iii) the `f`-Norm Ergodic Theorem with `f ≡ 1` and `V = U`
  have hπU : ∫⁻ x, U x ∂π ≠ ∞ := by
    rw [hU, lintegral_const_mul _ (hV.pow_const _)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hβi) (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hbU (measure_ne_top π C)) hπs)
  obtain ⟨-, -, -, -, hsum⟩ := theorem_14_0_1_consequences (f := fun _ => 1) hψ hap
    measurable_const hU1 hC hUm hbU hUx₀ hfoster hπ
  obtain ⟨B, hB, hBle⟩ := hsum hπU
  refine ⟨B * (2 * β⁻¹ + 1), ENNReal.mul_ne_top hB (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by simp) hβi, ENNReal.one_ne_top⟩), fun x => ?_⟩
  have hs1 : 1 ≤ V x ^ (2⁻¹ : ℝ) := ENNReal.one_le_rpow (hV1 x) (by norm_num)
  have : ∀ n, IsFiniteMeasure ((P ^ n : Kernel X X) x) := fun n => by
    have := isMarkovKernel_pow P n; infer_instance
  calc ∑' n, ENNReal.ofReal (tvNorm ((P ^ n : Kernel X X) x) π)
      = ∑' n, fNorm (fun _ => 1) ((P ^ n : Kernel X X) x) π :=
        tsum_congr fun n => (fNorm_one _ _).symm
    _ ≤ B * (U x + 1) := hBle x
    _ ≤ B * (2 * β⁻¹ * V x ^ (2⁻¹ : ℝ) + V x ^ (2⁻¹ : ℝ)) :=
        mul_le_mul' le_rfl (add_le_add le_rfl hs1)
    _ = B * (2 * β⁻¹ + 1) * V x ^ (2⁻¹ : ℝ) := by ring

/-! ### Random walk on a half line: Proposition 14.4.1 -/

/-- `((x + w)⁺)ʲ ≤ (x + w)ʲ + 2|w|ʲ` for `x ≥ 0`: if `x + w < 0` then `|x + w| ≤ |w|`. -/
theorem max_add_pow_le {x w : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    (max (x + w) 0) ^ j ≤ (x + w) ^ j + 2 * |w| ^ j := by
  rcases le_or_gt 0 (x + w) with h | h
  · rw [max_eq_left h]
    have : 0 ≤ |w| ^ j := pow_nonneg (abs_nonneg w) j
    linarith
  · rw [max_eq_right h.le]
    have hle : |x + w| ≤ |w| := by
      rw [abs_of_neg h, abs_of_neg (by linarith : w < 0)]; linarith
    have h1 : -(|w| ^ j) ≤ (x + w) ^ j := by
      have := neg_abs_le ((x + w) ^ j)
      rw [abs_pow] at this
      linarith [pow_le_pow_left₀ (abs_nonneg _) hle j]
    rcases j with _ | j
    · norm_num
    · simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow]
      linarith [pow_nonneg (abs_nonneg w) (j + 1)]

/-- `((x + w)⁺)ʲ ≤ 2ʲ (xʲ + |w|ʲ)` for `x ≥ 0`. -/
theorem max_add_pow_le_two_pow {x w : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    (max (x + w) 0) ^ j ≤ 2 ^ j * (x ^ j + |w| ^ j) := by
  have h1 : max (x + w) 0 ≤ 2 * max x |w| := by
    refine max_le ?_ (by positivity)
    have := le_abs_self w
    linarith [le_max_left x |w|, le_max_right x |w|]
  have h2 : (max x |w|) ^ j ≤ x ^ j + |w| ^ j := by
    rcases le_total x |w| with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hx j]
    · rw [max_eq_left h]; linarith [pow_nonneg (abs_nonneg w) j]
  calc (max (x + w) 0) ^ j ≤ (2 * max x |w|) ^ j :=
        pow_le_pow_left₀ (le_max_right _ _) h1 j
    _ = 2 ^ j * (max x |w|) ^ j := mul_pow _ _ _
    _ ≤ 2 ^ j * (x ^ j + |w| ^ j) := by gcongr

/-- `∫ (x + w)ʲ Γ(dw) = Σ_{m ≤ j} xᵐ E[W^{j−m}] C(j, m)` (the binomial theorem). -/
theorem integral_add_pow (Γ : Measure ℝ) (x : ℝ) (j : ℕ)
    (hint : ∀ l ≤ j, Integrable (fun w => w ^ l) Γ) :
    ∫ w, (x + w) ^ j ∂Γ = ∑ m ∈ range (j + 1), x ^ m * (∫ w, w ^ (j - m) ∂Γ) * j.choose m := by
  simp_rw [add_pow]
  rw [integral_finsetSum _ fun m hm => ((hint (j - m) (Nat.sub_le j m)).const_mul (x ^ m)).mul_const
    _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, integral_const_mul]

/-- `|E[Wˡ]| ≤ E|W|ˡ`. -/
theorem abs_integral_pow_le (Γ : Measure ℝ) (l : ℕ) :
    |∫ w, w ^ l ∂Γ| ≤ ∫ w, |w| ^ l ∂Γ := by
  refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
  congr 1; funext w; rw [abs_pow]

/-- `w ↦ wˡ` is integrable when `|w|ˡ` is. -/
theorem integrable_pow_of_abs {Γ : Measure ℝ} {l : ℕ} (h : Integrable (fun w => |w| ^ l) Γ) :
    Integrable (fun w => w ^ l) Γ :=
  h.mono' (measurable_id.pow_const l).aestronglyMeasurable
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs, abs_pow])

/-- `((x + w)⁺)ʲ` is integrable when `|w|ʲ` is (`x ≥ 0`). -/
theorem integrable_max_add_pow {Γ : Measure ℝ} [IsFiniteMeasure Γ] {x : ℝ} (hx : 0 ≤ x) {j : ℕ}
    (h : Integrable (fun w => |w| ^ j) Γ) : Integrable (fun w => (max (x + w) 0) ^ j) Γ :=
  ((integrable_const (x ^ j)).add h).const_mul (2 ^ j) |>.mono'
    (((measurable_const.add measurable_id).max measurable_const).pow_const j).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) j)]
      exact max_add_pow_le_two_pow hx j)

/-- The second-order bound behind (14.28): for `x ≥ 1` and `j = n + 2`,
`∫ ((x + w)⁺)ʲ Γ(dw) ≤ xʲ + j β x^{j−1} + K xⁿ`, `β = E[W]`, with `K` depending only on the
moments of `Γ` up to order `j`. -/
theorem integral_max_add_pow_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (n : ℕ)
    (hint : ∀ l ≤ n + 2, Integrable (fun w => |w| ^ l) Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      ∫ w, (max (x + w) 0) ^ (n + 2) ∂Γ ≤
        x ^ (n + 2) + (n + 2) * (∫ w, w ∂Γ) * x ^ (n + 1) + K * x ^ n := by
  set K : ℝ := ∑ m ∈ range (n + 1), (∫ w, |w| ^ (n + 2 - m) ∂Γ) * (n + 2).choose m +
    2 * ∫ w, |w| ^ (n + 2) ∂Γ with hK
  have hmom : ∀ l, 0 ≤ ∫ w, |w| ^ l ∂Γ := fun l => integral_nonneg fun w => by positivity
  refine ⟨K, add_nonneg (Finset.sum_nonneg fun m _ => mul_nonneg (hmom _) (by positivity))
    (mul_nonneg (by norm_num) (hmom _)), fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hintp : ∀ l ≤ n + 2, Integrable (fun w => w ^ l) Γ := fun l hl =>
    integrable_pow_of_abs (hint l hl)
  have hbin := integral_add_pow Γ x (n + 2) hintp
  have hintsum : Integrable (fun w => (x + w) ^ (n + 2)) Γ := by
    simp_rw [add_pow]
    exact integrable_finsetSum _ fun m hm =>
      ((hintp (n + 2 - m) (Nat.sub_le _ _)).const_mul (x ^ m)).mul_const _
  -- `∫ ((x + w)⁺)ʲ ≤ ∫ (x + w)ʲ + 2 E|W|ʲ`
  have h1 : ∫ w, (max (x + w) 0) ^ (n + 2) ∂Γ ≤
      ∫ w, (x + w) ^ (n + 2) ∂Γ + 2 * ∫ w, |w| ^ (n + 2) ∂Γ := by
    rw [← integral_const_mul, ← integral_add hintsum ((hint _ le_rfl).const_mul 2)]
    exact integral_mono (integrable_max_add_pow hx0 (hint _ le_rfl))
      (hintsum.add ((hint _ le_rfl).const_mul 2)) fun w => max_add_pow_le hx0 _
  -- split the binomial sum
  rw [hbin, Finset.sum_range_succ, Finset.sum_range_succ] at h1
  have hlast : x ^ (n + 2) * (∫ w, w ^ (n + 2 - (n + 2)) ∂Γ) * ((n + 2).choose (n + 2) : ℝ) =
      x ^ (n + 2) := by simp
  have hmid : x ^ (n + 1) * (∫ w, w ^ (n + 2 - (n + 1)) ∂Γ) * ((n + 2).choose (n + 1) : ℝ) =
      (n + 2) * (∫ w, w ∂Γ) * x ^ (n + 1) := by
    rw [show n + 2 - (n + 1) = 1 by omega, show (n + 2).choose (n + 1) = n + 2 by
      rw [show n + 2 = (n + 1) + 1 by ring, Nat.choose_succ_self_right]]
    simp only [pow_one]; push_cast; ring
  have hhead : ∑ m ∈ range (n + 1), x ^ m * (∫ w, w ^ (n + 2 - m) ∂Γ) * ((n + 2).choose m : ℝ)
      ≤ (∑ m ∈ range (n + 1), (∫ w, |w| ^ (n + 2 - m) ∂Γ) * (n + 2).choose m) * x ^ n := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm' : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hxm : x ^ m ≤ x ^ n := pow_le_pow_right₀ hx hm'
    have habs := abs_integral_pow_le Γ (n + 2 - m)
    calc x ^ m * (∫ w, w ^ (n + 2 - m) ∂Γ) * ((n + 2).choose m : ℝ)
        ≤ x ^ m * (∫ w, |w| ^ (n + 2 - m) ∂Γ) * ((n + 2).choose m : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((le_abs_self _).trans habs)
            (pow_nonneg hx0 m)) (Nat.cast_nonneg _)
      _ ≤ x ^ n * (∫ w, |w| ^ (n + 2 - m) ∂Γ) * ((n + 2).choose m : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxm (hmom _))
            (Nat.cast_nonneg _)
      _ = (∫ w, |w| ^ (n + 2 - m) ∂Γ) * ((n + 2).choose m : ℝ) * x ^ n := by ring
  have hxn : 1 ≤ x ^ n := one_le_pow₀ hx
  rw [hlast, hmid] at h1
  have h2 : 2 * ∫ w, |w| ^ (n + 2) ∂Γ ≤ 2 * (∫ w, |w| ^ (n + 2) ∂Γ) * x ^ n := by
    nlinarith [hmom (n + 2)]
  rw [hK]
  nlinarith

/-- `∫ P(x, dy) yʲ = ∫ ((x + w)⁺)ʲ Γ(dw)` for random walk on a half line. -/
theorem lintegral_halfLine_pow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (x : ℝ≥0) (j : ℕ)
    (hint : Integrable (fun w => |w| ^ j) Γ) :
    ∫⁻ y, (y : ℝ≥0∞) ^ j ∂halfLineWalkKernel Γ x =
      ENNReal.ofReal (∫ w, (max ((x : ℝ) + w) 0) ^ j ∂Γ) := by
  rw [lintegral_halfLine Γ x ((measurable_coe_nnreal_ennreal).pow_const j),
    ofReal_integral_eq_lintegral_ofReal (integrable_max_add_pow (NNReal.coe_nonneg x) hint)
      (Eventually.of_forall fun w => pow_nonneg (le_max_right _ _) j)]
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (le_max_right _ _), ← Real.coe_toNNReal', ENNReal.ofReal_coe_nnreal]

/-- The drift (14.28)–(14.29) for one power `j ≥ 1`: if `β = E[W] < 0` and `E|W|ʲ < ∞`, there
are `c > 0`, `X₀` and `D < ∞` with `∫ P(x, dy) yʲ + c (x^{j−1} + 1) ≤ xʲ + D 1_{[0, X₀]}(x)`. -/
theorem halfLine_drift_pow (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) {j : ℕ} (hj : 1 ≤ j)
    (hint : ∀ l ≤ j, Integrable (fun w => |w| ^ l) Γ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧ ∃ X₀ : ℝ≥0, ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ x : ℝ≥0,
      ∫⁻ y, (y : ℝ≥0∞) ^ j ∂halfLineWalkKernel Γ x + c * ((x : ℝ≥0∞) ^ (j - 1) + 1) ≤
        (x : ℝ≥0∞) ^ j + (Iic X₀).indicator (fun _ => D) x := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  -- the bound far out
  obtain ⟨c, hc0, hct, X₀, hfar⟩ : ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧ ∃ X₀ : ℝ≥0, ∀ x : ℝ≥0, X₀ < x →
      ∫⁻ y, (y : ℝ≥0∞) ^ j ∂halfLineWalkKernel Γ x + c * ((x : ℝ≥0∞) ^ (j - 1) + 1) ≤
        (x : ℝ≥0∞) ^ j := by
    obtain ⟨n, rfl⟩ | rfl : (∃ n, j = n + 2) ∨ j = 1 := by
      rcases j with _ | _ | n
      · omega
      · exact Or.inr rfl
      · exact Or.inl ⟨n, rfl⟩
    · -- `j = n + 2`: the second-order bound
      obtain ⟨K, hK0, hK⟩ := integral_max_add_pow_le Γ n hint
      set β := ∫ w, w ∂Γ with hβdef
      set cR : ℝ := -((n + 2) * β) / 4 with hcR
      have hcR0 : 0 < cR := by
        have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have := mul_neg_of_pos_of_neg h2 hβ
        rw [hcR]; linarith
      set X : ℝ := max 1 ((K + cR) / (3 * cR)) with hX
      refine ⟨ENNReal.ofReal cR, ENNReal.ofReal_pos.2 hcR0, ENNReal.ofReal_ne_top,
        X.toNNReal, fun x hx => ?_⟩
      have hxX : X < x := by
        have := (Real.toNNReal_lt_iff_lt_coe (by positivity)).1 hx
        exact this
      have hx1 : 1 ≤ (x : ℝ) := le_trans (le_max_left _ _) hxX.le
      have hxK : (K + cR) / (3 * cR) ≤ (x : ℝ) := le_trans (le_max_right _ _) hxX.le
      have hxK' : K + cR ≤ 3 * cR * x := by
        rwa [div_le_iff₀ (by positivity), mul_comm] at hxK
      have hbound := hK x hx1
      have hxn : 0 ≤ (x : ℝ) ^ n := pow_nonneg (NNReal.coe_nonneg x) n
      have hxn1 : (x : ℝ) ^ (n + 1) = (x : ℝ) ^ n * x := pow_succ _ _
      have hreal : ∫ w, (max ((x : ℝ) + w) 0) ^ (n + 2) ∂Γ + cR * ((x : ℝ) ^ (n + 1) + 1) ≤
          (x : ℝ) ^ (n + 2) := by
        have h4 : (K + cR) * (x : ℝ) ^ n ≤ 3 * cR * x * (x : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hxK' hxn
        have h5 : cR ≤ cR * (x : ℝ) ^ n := le_mul_of_one_le_right hcR0.le (one_le_pow₀ hx1)
        have h6 : (n + 2 : ℝ) * β = -(4 * cR) := by rw [hcR]; ring
        rw [hxn1] at hbound ⊢
        have h7 : (n + 2 : ℝ) * β * ((x : ℝ) ^ n * x) = -(4 * cR) * ((x : ℝ) ^ n * x) := by
          rw [h6]
        have h8 : (K + cR) * (x : ℝ) ^ n ≤ 3 * cR * ((x : ℝ) ^ n * x) := by
          have : 3 * cR * x * (x : ℝ) ^ n = 3 * cR * ((x : ℝ) ^ n * x) := by ring
          linarith
        nlinarith [hbound, h7, h8, h5]
      rw [lintegral_halfLine_pow Γ x _ (hint _ le_rfl), show n + 2 - 1 = n + 1 by omega,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (NNReal.coe_nonneg x),
        ← ENNReal.ofReal_pow (NNReal.coe_nonneg x), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (pow_nonneg (NNReal.coe_nonneg x) _) zero_le_one,
        ← ENNReal.ofReal_mul hcR0.le, ← ENNReal.ofReal_add (integral_nonneg fun w =>
          pow_nonneg (le_max_right _ _) _) (mul_nonneg hcR0.le (by positivity))]
      exact ENNReal.ofReal_le_ofReal hreal
    · -- `j = 1`: Proposition 8.5.1's drift (8.54)
      obtain ⟨x₀, ε, hε, hdrift⟩ := halfLine_drift_neg Γ hW hβ
      refine ⟨ENNReal.ofReal (ε / 2), ENNReal.ofReal_pos.2 (by linarith), ENNReal.ofReal_ne_top,
        x₀, fun x hx => ?_⟩
      have h1 := hdrift x hx
      rw [integral_halfLine Γ x measurable_coe_nnreal_real] at h1
      have hc : ∫ w, (max ((x : ℝ) + w) 0) ^ 1 ∂Γ = ∫ w, ((Real.toNNReal ((x : ℝ) + w) : ℝ)) ∂Γ :=
        integral_congr_ae (Eventually.of_forall fun w => by
          simp only [pow_one, Real.coe_toNNReal'])
      rw [lintegral_halfLine_pow Γ x 1 (hint 1 le_rfl), Nat.sub_self, pow_zero, one_add_one_eq_two,
        hc, pow_one]
      have hnn : 0 ≤ ∫ w, ((Real.toNNReal ((x : ℝ) + w) : ℝ)) ∂Γ :=
        integral_nonneg fun w => NNReal.coe_nonneg _
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add hnn (by linarith), ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the bound near `0`
  set m : ℝ := ∫ w, |w| ^ j ∂Γ with hm
  set D : ℝ≥0∞ := ENNReal.ofReal (2 ^ j * ((X₀ : ℝ) ^ j + m)) +
    c * ((X₀ : ℝ≥0∞) ^ (j - 1) + 1) with hD
  refine ⟨c, hc0, hct, X₀, D, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top hct (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top ENNReal.coe_ne_top,
      ENNReal.one_ne_top⟩)⟩, fun x => ?_⟩
  by_cases hx : x ∈ Iic X₀
  · rw [indicator_of_mem hx]
    refine le_trans ?_ le_add_self
    have hxX : (x : ℝ) ≤ X₀ := by exact_mod_cast hx
    refine add_le_add ?_ (mul_le_mul' le_rfl (add_le_add (pow_le_pow_left₀ zero_le
      (by exact_mod_cast hx) _) le_rfl))
    rw [lintegral_halfLine_pow Γ x j (hint j le_rfl)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∫ w, (max ((x : ℝ) + w) 0) ^ j ∂Γ ≤ ∫ w, 2 ^ j * ((x : ℝ) ^ j + |w| ^ j) ∂Γ :=
          integral_mono (integrable_max_add_pow (NNReal.coe_nonneg x) (hint j le_rfl))
            (((integrable_const _).add (hint j le_rfl)).const_mul _)
            fun w => max_add_pow_le_two_pow (NNReal.coe_nonneg x) j
      _ = 2 ^ j * ((x : ℝ) ^ j + m) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hint j le_rfl),
            integral_const, probReal_univ, one_smul]
      _ ≤ 2 ^ j * ((X₀ : ℝ) ^ j + m) := by
          gcongr
  · rw [indicator_of_notMem hx, add_zero]
    exact hfar x (not_le.1 hx)

/-- **The drift (14.29)** (MT p. 353): if `β = E[W] < 0` and `E|W|^{k+1} < ∞`, there are `c₀ > 0`,
`X₀` and `d₀ < ∞` with `P V_{i+1} ≤ V_{i+1} − c₀ f_i + d₀ 1_{[0, X₀]}` for every `i ≤ k`, where
`V_j(x) = xʲ` and `f_i(x) = xⁱ + 1`. -/
theorem halfLine_drift_14_29 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) (k : ℕ)
    (hint : ∀ l ≤ k + 1, Integrable (fun w => |w| ^ l) Γ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧ ∃ X₀ : ℝ≥0, ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ i ≤ k, ∀ x : ℝ≥0,
      ∫⁻ y, (y : ℝ≥0∞) ^ (i + 1) ∂halfLineWalkKernel Γ x + c * ((x : ℝ≥0∞) ^ i + 1) ≤
        (x : ℝ≥0∞) ^ (i + 1) + (Iic X₀).indicator (fun _ => D) x := by
  induction k with
  | zero =>
    obtain ⟨c, hc0, hct, X₀, D, hD, h⟩ := halfLine_drift_pow Γ hW hβ le_rfl hint
    exact ⟨c, hc0, hct, X₀, D, hD, fun i hi x => by
      obtain rfl : i = 0 := by omega
      exact h x⟩
  | succ k ih =>
    obtain ⟨c, hc0, hct, X₀, D, hD, h⟩ := ih fun l hl => hint l (by omega)
    obtain ⟨c', hc0', hct', X', D', hD', h'⟩ := halfLine_drift_pow Γ hW hβ (j := k + 2)
      (by omega) hint
    refine ⟨min c c', lt_min hc0 hc0', ne_top_of_le_ne_top hct (min_le_left _ _), max X₀ X',
      max D D', max_ne_top hD hD', fun i hi x => ?_⟩
    have hind : ∀ (Y : ℝ≥0) (E : ℝ≥0∞), Y ≤ max X₀ X' → E ≤ max D D' →
        (Iic Y).indicator (fun _ => E) x ≤ (Iic (max X₀ X')).indicator (fun _ => max D D') x :=
      fun Y E hY hE => (indicator_le_indicator_of_subset (Set.Iic_subset_Iic.2 hY)
        (fun _ => zero_le) x).trans (indicator_le_indicator hE)
    rcases Nat.lt_or_ge i (k + 1) with hik | hik
    · refine le_trans (add_le_add le_rfl (mul_le_mul' (min_le_left _ _) le_rfl)) ((h i (by omega)
        x).trans (add_le_add le_rfl (hind X₀ D (le_max_left _ _) (le_max_left _ _))))
    · obtain rfl : i = k + 1 := by omega
      have h2 := h' x
      rw [show k + 2 - 1 = k + 1 by omega] at h2
      refine le_trans (add_le_add le_rfl (mul_le_mul' (min_le_right _ _) le_rfl)) (h2.trans
        (add_le_add le_rfl (hind X' D' (le_max_right _ _) (le_max_right _ _))))

/-- **Proposition 14.4.1** (MT p. 352): let random walk on a half line have increments with mean
`β < 0` and finite `(k + 1)`-st moment, and put `f_i(x) = xⁱ + 1`. Then the walk is
`ψ`-irreducible and aperiodic, positive Harris and `f_k`-regular; every invariant probability has
finite `k`-th moment; and
(i) `‖Pⁿ(x, ·) − π‖_{f_k} → 0` for every `x`, and `‖λPⁿ − π‖_{f_k} → 0` for every initial law
with `∫ λ(dx) x^{k+1} < ∞`;
(ii) for `k ≥ 1` there is `B_f < ∞` with
`Σₙ ∫ λ(dx) ‖Pⁿ(x, ·) − π‖_{f_{k−1}} ≤ B_f (1 + ∫ λ(dx) xᵏ)` for every initial law `λ`. -/
theorem proposition_14_4_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) (k : ℕ)
    (hint : ∀ l ≤ k + 1, Integrable (fun w => |w| ^ l) Γ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    ∃ ψ : Measure ℝ≥0, IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ ∧
      IsAperiodic (halfLineWalkKernel Γ) ψ ∧ IsPositiveHarris (halfLineWalkKernel Γ) ψ ∧
      IsFRegularChain (halfLineWalkKernel Γ) ψ (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ k + 1) ∧
      ∀ π : Measure ℝ≥0, IsProbabilityMeasure π → IsInvariant (halfLineWalkKernel Γ) π →
        ∫⁻ x, (x : ℝ≥0∞) ^ k ∂π ≠ ∞ ∧
        (∀ x, Tendsto (fun n => fNorm (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ k + 1)
          ((halfLineWalkKernel Γ ^ n : Kernel ℝ≥0 ℝ≥0) x) π) atTop (𝓝 0)) ∧
        (∀ (μ : Measure ℝ≥0) [IsProbabilityMeasure μ], ∫⁻ x, (x : ℝ≥0∞) ^ (k + 1) ∂μ ≠ ∞ →
          Tendsto (fun n => fNorm (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ k + 1)
            ((halfLineWalkKernel Γ ^ n : Kernel ℝ≥0 ℝ≥0) ∘ₘ μ) π) atTop (𝓝 0)) ∧
        (1 ≤ k → ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ (μ : Measure ℝ≥0) [IsProbabilityMeasure μ],
          ∑' n, ∫⁻ x, fNorm (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ (k - 1) + 1)
            ((halfLineWalkKernel Γ ^ n : Kernel ℝ≥0 ℝ≥0) x) π ∂μ ≤
            B * (1 + ∫⁻ x, (x : ℝ≥0∞) ^ k ∂μ)) := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  set P := halfLineWalkKernel Γ with hP
  obtain ⟨c, hc0, hct, X₀, D, hD, hdrift⟩ := halfLine_drift_14_29 Γ hW hβ k hint
  have hneg := halfLine_neg_pos_of_mean_neg Γ hβ
  obtain ⟨_, hψ, -⟩ := halfLine_maximal Γ hneg
  set ψ := (2 : ℝ≥0∞) • resolventHalf (halfLineWalkKernel Γ) 0 with hψdef
  have hpet := halfLine_isPetite_Iic Γ hneg X₀
  have hCm : MeasurableSet (Iic X₀) := measurableSet_Iic
  -- aperiodicity through the atom `{0}`
  have hatom := halfLine_isAccessibleAtom_zero Γ hneg hψ
  have hP0 : 0 < P 0 {0} := by
    rw [hP, halfLineWalkKernel_apply_zero]
    refine lt_of_lt_of_le hneg (measure_mono ?_)
    rw [NNReal.coe_zero, neg_zero]
    exact Set.Iio_subset_Iic_self
  obtain ⟨M, hMC, hMν, -⟩ := exists_minorization_of_le (P := P) (measurableSet_singleton 0)
    ⟨0, rfl⟩ (ν' := P 0) (fun x hx => by rw [mem_singleton_iff.1 hx]) hP0
  have hap : IsAperiodic P ψ := isAperiodic_of_minorization hψ M (by rw [hMC]; exact hatom.2.2)
    (by rw [hMν]; exact one_pos)
  -- (V3) for `V = c⁻¹ x^{i+1}` and `f_i`
  have hci : c⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hc0.ne'
  have hV3 : ∀ i ≤ k, DriftV3 P (fun x => c⁻¹ * (x : ℝ≥0∞) ^ (i + 1))
      (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ i + 1) (c⁻¹ * D) (Iic X₀) := fun i hi x => by
    have h := hdrift i hi x
    rw [lintegral_const_mul _ ((measurable_coe_nnreal_ennreal).pow_const _)]
    have hmul := mul_le_mul' (le_refl c⁻¹) h
    rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hc0.ne' hct, one_mul] at hmul
    refine hmul.trans ?_
    rw [mul_add]
    refine add_le_add le_rfl ?_
    by_cases hx : x ∈ Iic X₀
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  have hVm : ∀ i, Measurable fun x : ℝ≥0 => c⁻¹ * (x : ℝ≥0∞) ^ (i + 1) := fun i =>
    measurable_const.mul ((measurable_coe_nnreal_ennreal).pow_const _)
  have hfm : ∀ i, Measurable fun x : ℝ≥0 => (x : ℝ≥0∞) ^ i + 1 := fun i =>
    ((measurable_coe_nnreal_ennreal).pow_const _).add measurable_const
  have hf1 : ∀ i (x : ℝ≥0), 1 ≤ (x : ℝ≥0∞) ^ i + 1 := fun i x => le_add_self
  have hVfin : ∀ i (x : ℝ≥0), c⁻¹ * (x : ℝ≥0∞) ^ (i + 1) ≠ ∞ := fun i x =>
    ENNReal.mul_ne_top hci (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hb : c⁻¹ * D ≠ ∞ := ENNReal.mul_ne_top hci hD
  -- positive Harris recurrence
  have hph : IsPositiveHarris P ψ := theorem_11_3_4_positiveHarris hψ (hVm k) hb hpet
    ((hV3 k le_rfl).driftV2 (hf1 k)) (hVfin k) (ENNReal.mul_ne_top hci
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) : c⁻¹ * (X₀ : ℝ≥0∞) ^ (k + 1) ≠ ∞)
    fun x hx => mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le (by exact_mod_cast hx) _)
  have hreg : IsFRegularChain P ψ (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ k + 1) :=
    (theorem_14_2_6 hψ (hfm k) (hf1 k)).2 ⟨Iic X₀, _, _, hpet, hVm k, hb, hVfin k, hV3 k le_rfl⟩
  refine ⟨ψ, hψ, hap, hph, hreg, fun π hπp hπ => ?_⟩
  have hπf : ∫⁻ x, (x : ℝ≥0∞) ^ k + 1 ∂π ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hb (measure_ne_top π _))
    (lintegral_le_of_driftV3 hph.2 hπ (hVm k) (hfm k) hb hCm (hV3 k le_rfl) (hVfin k 0))
  have hπk : ∫⁻ x, (x : ℝ≥0∞) ^ k ∂π ≠ ∞ :=
    ne_top_of_le_ne_top hπf (lintegral_mono fun x => le_self_add)
  obtain ⟨-, -, -, hconv, -⟩ := theorem_14_0_1_consequences hψ hap (hfm k) (hf1 k) hpet (hVm k)
    hb (hVfin k 0) (hV3 k le_rfl) hπ
  refine ⟨hπk, fun x => hconv x (hVfin k x), fun μ _ hμ => ?_, fun hk => ?_⟩
  · refine tendsto_fNorm_of_driftV3 hph.2 hap hπ (hVm k) (hfm k) (hf1 k) hb hpet (hV3 k le_rfl)
      hπf μ ?_
    rw [lintegral_const_mul _ ((measurable_coe_nnreal_ennreal).pow_const _)]
    exact ENNReal.mul_ne_top hci hμ
  · -- (ii) with `V = c⁻¹ xᵏ` and `f_{k−1}`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨-, -, -, -, hsum⟩ := theorem_14_0_1_consequences hψ hap (hfm j) (hf1 j) hpet
      (hVm j) hb (hVfin j 0) (hV3 j (by omega)) hπ
    have hπV : ∫⁻ x, c⁻¹ * (x : ℝ≥0∞) ^ (j + 1) ∂π ≠ ∞ := by
      rw [lintegral_const_mul _ ((measurable_coe_nnreal_ennreal).pow_const _)]
      exact ENNReal.mul_ne_top hci hπk
    obtain ⟨B, hB, hBle⟩ := hsum hπV
    refine ⟨B * max c⁻¹ 1, ENNReal.mul_ne_top hB (max_ne_top hci ENNReal.one_ne_top),
      fun μ _ => ?_⟩
    calc ∑' n, ∫⁻ x, fNorm (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ j + 1)
          ((halfLineWalkKernel Γ ^ n : Kernel ℝ≥0 ℝ≥0) x) π ∂μ
        ≤ ∫⁻ x, ∑' n, fNorm (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ j + 1)
            ((halfLineWalkKernel Γ ^ n : Kernel ℝ≥0 ℝ≥0) x) π ∂μ :=
          tsum_lintegral_le_lintegral_tsum μ _
      _ ≤ ∫⁻ x, B * (c⁻¹ * (x : ℝ≥0∞) ^ (j + 1) + 1) ∂μ := lintegral_mono hBle
      _ = B * (c⁻¹ * ∫⁻ x, (x : ℝ≥0∞) ^ (j + 1) ∂μ + 1) := by
          rw [lintegral_const_mul' _ _ hB, lintegral_add_right _ measurable_const,
            lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ ((measurable_coe_nnreal_ennreal).pow_const _)]
      _ ≤ B * (max c⁻¹ 1 * ∫⁻ x, (x : ℝ≥0∞) ^ (j + 1) ∂μ + max c⁻¹ 1 * 1) :=
          mul_le_mul' le_rfl (add_le_add (mul_le_mul' (le_max_left _ _) le_rfl)
            (by rw [mul_one]; exact le_max_right _ _))
      _ = B * max c⁻¹ 1 * (1 + ∫⁻ x, (x : ℝ≥0∞) ^ (j + 1) ∂μ) := by ring

/-! ### Proposition 14.4.2: the bilinear model -/

/-- **Minkowski's inequality for the bilinear step**: for `k ≥ 1`,
`E|θx + bxW + W|ᵏ ≤ (‖θ + bW‖_k |x| + ‖W‖_k)ᵏ`, with `‖Y‖_k = (E|Y|ᵏ)^{1/k}`. -/
theorem bilinear_lintegral_pow_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b x : ℝ) {k : ℕ}
    (hk : 1 ≤ k) :
    ∫⁻ y, ‖y‖ₑ ^ k ∂(bilinearKernel Γ θ b x) ≤
      ((∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹ * ‖x‖ₑ +
        (∫⁻ w, ‖w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹) ^ k := by
  have hF := (contDiff_bilinearStep θ b).continuous.measurable
  have hp : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos hp
  have hk0 : (k : ℝ) ≠ 0 := hp0.ne'
  rw [bilinearKernel, recursionKernel_apply Γ hF x,
    lintegral_map (f := fun y : ℝ => ‖y‖ₑ ^ k) (g := fun w => bilinearStep θ b (x, w))
      (measurable_enorm.pow_const k) (hF.comp measurable_prodMk_left)]
  have hpt : ∀ w, ‖bilinearStep θ b (x, w)‖ₑ ^ k ≤ (‖θ + b * w‖ₑ * ‖x‖ₑ + ‖w‖ₑ) ^ k := by
    intro w
    refine pow_le_pow_left₀ zero_le ?_ k
    rw [bilinearStep_eq, ← enorm_mul]
    exact enorm_add_le _ _
  refine (lintegral_mono hpt).trans ?_
  have hmk := ENNReal.lintegral_Lp_add_le (μ := Γ) (p := (k : ℝ))
    (f := fun w => ‖θ + b * w‖ₑ * ‖x‖ₑ) (g := fun w => ‖w‖ₑ) (by fun_prop) (by fun_prop) hp
  have e0 : ∀ w, (((fun w : ℝ => ‖θ + b * w‖ₑ * ‖x‖ₑ) + fun w : ℝ => ‖w‖ₑ : ℝ → ℝ≥0∞) w) ^
      (k : ℝ) =
      (‖θ + b * w‖ₑ * ‖x‖ₑ + ‖w‖ₑ) ^ k := fun w =>
    ENNReal.rpow_natCast (‖θ + b * w‖ₑ * ‖x‖ₑ + ‖w‖ₑ) k
  have e1 : ∀ w, (‖θ + b * w‖ₑ * ‖x‖ₑ) ^ (k : ℝ) = ‖θ + b * w‖ₑ ^ k * ‖x‖ₑ ^ (k : ℝ) :=
    fun w => by rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_natCast]
  have e2 : ∀ w : ℝ, ‖w‖ₑ ^ (k : ℝ) = ‖w‖ₑ ^ k := fun w => ENNReal.rpow_natCast _ k
  rw [lintegral_congr e0, lintegral_congr e1, lintegral_congr e2,
    lintegral_mul_const (f := fun w => ‖θ + b * w‖ₑ ^ k) _ (by fun_prop),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hk0] at hmk
  calc ∫⁻ w, (‖θ + b * w‖ₑ * ‖x‖ₑ + ‖w‖ₑ) ^ k ∂Γ
      = ((∫⁻ w, (‖θ + b * w‖ₑ * ‖x‖ₑ + ‖w‖ₑ) ^ k ∂Γ) ^ (k : ℝ)⁻¹) ^ (k : ℝ) :=
        (ENNReal.rpow_inv_rpow hk0 _).symm
    _ ≤ ((∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹ * ‖x‖ₑ +
          (∫⁻ w, ‖w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹) ^ (k : ℝ) := ENNReal.rpow_le_rpow hmk hp0.le
    _ = _ := ENNReal.rpow_natCast _ k

/-- The real inequality behind the bilinear drift. With `0 ≤ r < 1`, `m ≥ 0`, `r' = (1 + r)/2`,
`a = 2/(1 − r'ᵏ)` and `R = max 1 (2m/(1 − r))`: for `t > R`,
`a (rt + m)ᵏ + tᵏ + 1 ≤ a tᵏ`. -/
theorem bilinear_real_drift {r m t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hm : 0 ≤ m) {k : ℕ}
    (hk : 1 ≤ k) (ht : max 1 (2 * m / (1 - r)) < t) :
    2 / (1 - ((1 + r) / 2) ^ k) * (r * t + m) ^ k + (t ^ k + 1) ≤
      2 / (1 - ((1 + r) / 2) ^ k) * t ^ k := by
  have h1r : 0 < 1 - r := by linarith
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht.le
  have ht2 : 2 * m / (1 - r) ≤ t := (le_max_right _ _).trans ht.le
  have hq0 : 0 ≤ (1 + r) / 2 := by linarith
  have hq1 : (1 + r) / 2 < 1 := by linarith
  have hqk : ((1 + r) / 2) ^ k < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  have hden : 0 < 1 - ((1 + r) / 2) ^ k := by linarith
  set q := ((1 + r) / 2) ^ k with hq
  set a := 2 / (1 - q) with ha
  have ha0 : 0 < a := div_pos two_pos hden
  have haq : a * (1 - q) = 2 := div_mul_cancel₀ 2 hden.ne'
  have hlin : r * t + m ≤ (1 + r) / 2 * t := by
    have := (div_le_iff₀ h1r).1 ht2
    nlinarith
  have hpow : (r * t + m) ^ k ≤ q * t ^ k := by
    rw [hq, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlin k
  have htk : 1 ≤ t ^ k := one_le_pow₀ ht1
  have e : a * t ^ k - a * q * t ^ k = 2 * t ^ k := by rw [← haq]; ring
  have := mul_le_mul_of_nonneg_left hpow ha0.le
  nlinarith

/-- **The bilinear drift** (MT §14.4.2, extending (14.31)–(14.32) to `k`-th moments): if
`E|W|ᵏ < ∞` and `E|θ + bW|ᵏ < 1`, then for some `a < ∞`, `R` and `B < ∞`, (V3) holds with
`V(x) = a|x|ᵏ`, `f(x) = |x|ᵏ + 1` and the compact set `C = [−R, R]`. -/
theorem bilinear_driftV3 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ) {k : ℕ}
    (hW : ∫⁻ w, ‖w‖ₑ ^ k ∂Γ ≠ ∞) (hρ : ∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ < 1) :
    ∃ a : ℝ≥0∞, a ≠ ∞ ∧ ∃ R : ℝ, ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      DriftV3 (bilinearKernel Γ θ b) (fun x => a * ‖x‖ₑ ^ k) (fun x => ‖x‖ₑ ^ k + 1) B
        (Icc (-R) R) := by
  -- `k ≥ 1`, since `E|θ + bW|⁰ = 1`
  have hk : 1 ≤ k := by
    by_contra h
    obtain rfl : k = 0 := by omega
    simp only [pow_zero, lintegral_const, measure_univ, mul_one] at hρ
    exact lt_irrefl _ hρ
  have hp0 : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hk)
  set ρ := (∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹ with hρdef
  set M := (∫⁻ w, ‖w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹ with hMdef
  have hρ1 : ρ < 1 := ENNReal.rpow_lt_one hρ hp0
  have hρt : ρ ≠ ∞ := ne_top_of_lt hρ1
  have hMt : M ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0.le hW
  set r := ρ.toReal
  set m := M.toReal
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal hρt ENNReal.one_ne_top).2 hρ1
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set R := max 1 (2 * m / (1 - r))
  set a := 2 / (1 - ((1 + r) / 2) ^ k)
  have hden : 0 < 1 - ((1 + r) / 2) ^ k := by
    have : ((1 + r) / 2) ^ k < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
    linarith
  have ha0 : 0 ≤ a := (div_pos two_pos hden).le
  have hR0 : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  refine ⟨ENNReal.ofReal a, ENNReal.ofReal_ne_top, R,
    ENNReal.ofReal (a * (r * R + m) ^ k + (R ^ k + 1)), ENNReal.ofReal_ne_top, fun x => ?_⟩
  set t := |x|
  have ht0 : 0 ≤ t := abs_nonneg x
  have hxe : ‖x‖ₑ = ENNReal.ofReal t := Real.enorm_eq_ofReal_abs x
  -- the one-step moment bound
  have hstep : ∫⁻ y, ENNReal.ofReal a * ‖y‖ₑ ^ k ∂(bilinearKernel Γ θ b x) ≤
      ENNReal.ofReal (a * (r * t + m) ^ k) := by
    rw [lintegral_const_mul _ (measurable_enorm.pow_const k)]
    refine (mul_le_mul' le_rfl (bilinear_lintegral_pow_le Γ θ b x hk)).trans (le_of_eq ?_)
    rw [← hρdef, ← hMdef, hxe, ← ENNReal.ofReal_toReal hρt, ← ENNReal.ofReal_toReal hMt,
      ← ENNReal.ofReal_mul hr0, ← ENNReal.ofReal_add (mul_nonneg hr0 ht0) hm0,
      ← ENNReal.ofReal_pow (add_nonneg (mul_nonneg hr0 ht0) hm0), ← ENNReal.ofReal_mul ha0]
  have hf : ‖x‖ₑ ^ k + 1 = ENNReal.ofReal (t ^ k + 1) := by
    rw [hxe, ← ENNReal.ofReal_pow ht0, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (pow_nonneg ht0 k) zero_le_one]
  have hV : ENNReal.ofReal a * ‖x‖ₑ ^ k = ENNReal.ofReal (a * t ^ k) := by
    rw [hxe, ← ENNReal.ofReal_pow ht0, ← ENNReal.ofReal_mul ha0]
  refine (add_le_add hstep (le_of_eq hf)).trans ?_
  change _ ≤ ENNReal.ofReal a * ‖x‖ₑ ^ k + _
  rw [← ENNReal.ofReal_add (mul_nonneg ha0 (pow_nonneg (add_nonneg (mul_nonneg hr0 ht0) hm0) k))
    (by positivity), hV]
  by_cases hx : x ∈ Icc (-R) R
  · rw [indicator_of_mem hx]
    have htR : t ≤ R := abs_le.2 hx
    rw [← ENNReal.ofReal_add (mul_nonneg ha0 (pow_nonneg ht0 k)) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (r * t + m) ^ k ≤ (r * R + m) ^ k :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) k
    have h2 : t ^ k ≤ R ^ k := pow_le_pow_left₀ ht0 htR k
    have h3 := mul_le_mul_of_nonneg_left h1 ha0
    have h4 : 0 ≤ a * t ^ k := mul_nonneg ha0 (pow_nonneg ht0 k)
    linarith
  · rw [indicator_of_notMem hx, add_zero]
    refine ENNReal.ofReal_le_ofReal (bilinear_real_drift hr0 hr1 hm0 hk ?_)
    by_contra h
    exact hx (abs_le.1 (not_lt.1 h))

/-- **Proposition 14.4.2**, corrected (MT p. 354). For the bilinear model
`Xₙ₊₁ = θXₙ + bXₙWₙ₊₁ + Wₙ₊₁` with `E|W|ᵏ < ∞` (14.33) and the added stability condition
`E|θ + bW|ᵏ < 1` (for `k = 2` and `E W = 0` this is (14.32)), if the chain is
`ψ`-irreducible and aperiodic and compact sets are petite (consequences of (SBL1)–(SBL2) via
Proposition 7.1.3 and Theorem 6.2.5), then it is positive Harris, every invariant probability
has a finite `k`-th moment, and `‖Pⁿ(x, ·) − π‖_{|x|ᵏ+1} → 0` for every `x`. -/
theorem proposition_14_4_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ) {k : ℕ}
    (hW : ∫⁻ w, ‖w‖ₑ ^ k ∂Γ ≠ ∞) (hρ : ∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ < 1) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_bilinearKernel Γ θ b
      IsMaximalIrreducibility (bilinearKernel Γ θ b) ψ)
    (hap : IsAperiodic (bilinearKernel Γ θ b) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (bilinearKernel Γ θ b) K) :
    haveI := isMarkovKernel_bilinearKernel Γ θ b
    IsPositiveHarris (bilinearKernel Γ θ b) ψ ∧
      ∀ π : Measure ℝ, IsProbabilityMeasure π → IsInvariant (bilinearKernel Γ θ b) π →
        ∫⁻ x, ‖x‖ₑ ^ k ∂π ≠ ∞ ∧
        ∀ x, Tendsto (fun n => fNorm (fun x : ℝ => ‖x‖ₑ ^ k + 1)
          ((bilinearKernel Γ θ b ^ n : Kernel ℝ ℝ) x) π) atTop (𝓝 0) := by
  have := isMarkovKernel_bilinearKernel Γ θ b
  obtain ⟨a, ha, R, B, hB, hdrift⟩ := bilinear_driftV3 Γ θ b hW hρ
  have hpet := hcpt (Icc (-R) R) isCompact_Icc
  have hVm : Measurable fun x : ℝ => a * ‖x‖ₑ ^ k :=
    measurable_const.mul (measurable_enorm.pow_const k)
  have hfm : Measurable fun x : ℝ => ‖x‖ₑ ^ k + 1 :=
    (measurable_enorm.pow_const k).add measurable_const
  have hf1 : ∀ x : ℝ, 1 ≤ ‖x‖ₑ ^ k + 1 := fun x => le_add_self
  have hVfin : ∀ x : ℝ, a * ‖x‖ₑ ^ k ≠ ∞ := fun x =>
    ENNReal.mul_ne_top ha (ENNReal.pow_ne_top enorm_ne_top)
  have hph : IsPositiveHarris (bilinearKernel Γ θ b) ψ :=
    theorem_11_3_4_positiveHarris hψ hVm hB hpet (hdrift.driftV2 hf1) hVfin
      (ENNReal.mul_ne_top ha (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
        a * ENNReal.ofReal R ^ k ≠ ∞)
      fun x hx => by
        refine mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le ?_ k)
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_le.2 hx)
  refine ⟨hph, fun π hπp hπ => ⟨?_, ?_⟩⟩
  · obtain ⟨-, hfin⟩ := isPositive_of_driftV3 hψ hfm hf1 hpet hVm hB (hVfin 0) hdrift
    exact ne_top_of_le_ne_top (hfin π hπp hπ) (lintegral_mono fun x => le_self_add)
  · obtain ⟨-, -, -, hconv, -⟩ := theorem_14_0_1_consequences hψ hap hfm hf1 hpet hVm hB
      (hVfin 0) hdrift hπ
    exact fun x => hconv x (hVfin x)

/-- The second moment of `θ + bW` for a centred `W` with finite variance (MT (14.31)–(14.32)):
`E|θ + bW|² = θ² + b² E W²`. -/
theorem bilinear_moment_two (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) :
    ∫⁻ w, ‖θ + b * w‖ₑ ^ 2 ∂Γ = ENNReal.ofReal (θ ^ 2 + b ^ 2 * ∫ w, w ^ 2 ∂Γ) := by
  have e : ∀ y : ℝ, ‖y‖ₑ ^ 2 = ENNReal.ofReal (y ^ 2) := fun y => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg y), sq_abs]
  have hsq : (fun w : ℝ => (θ + b * w) ^ 2) =
      fun w => (θ ^ 2 + 2 * θ * b * w) + b ^ 2 * w ^ 2 := by
    funext w
    ring
  have hi1 : Integrable (fun w : ℝ => θ ^ 2 + 2 * θ * b * w) Γ :=
    (integrable_const _).add (hW1.const_mul _)
  have hi2 : Integrable (fun w : ℝ => b ^ 2 * w ^ 2) Γ := hW2.const_mul _
  have hint : Integrable (fun w : ℝ => (θ + b * w) ^ 2) Γ := by
    rw [hsq]
    exact hi1.add hi2
  rw [lintegral_congr fun w => e (θ + b * w),
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => sq_nonneg _),
    hsq, integral_add hi1 hi2, integral_add (integrable_const _) (hW1.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, h0, probReal_univ, one_smul, mul_zero,
    add_zero]

/-- **(14.32)** (MT p. 354): for a centred `W` with finite variance, `θ² + b² E W² < 1` is the
case `k = 2` of the stability condition of `proposition_14_4_2`, and then (V3) holds with
`f = 1 + δV` for `V(x) = x²` (here `f(x) = x² + 1`), so the conclusions of Proposition 14.4.2
hold with second moments. -/
theorem bilinear_condition_14_32 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) (h : θ ^ 2 + b ^ 2 * ∫ w, w ^ 2 ∂Γ < 1) :
    ∫⁻ w, ‖w‖ₑ ^ 2 ∂Γ ≠ ∞ ∧ ∫⁻ w, ‖θ + b * w‖ₑ ^ 2 ∂Γ < 1 := by
  refine ⟨?_, ?_⟩
  · have e := bilinear_moment_two Γ 0 1 hW1 hW2 h0
    have e2 : ∀ w : ℝ, (0 : ℝ) + 1 * w = w := fun w => by ring
    rw [lintegral_congr fun w => by rw [e2 w]] at e
    rw [e]
    exact ENNReal.ofReal_ne_top
  · rw [bilinear_moment_two Γ θ b hW1 hW2 h0, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 h

/-- The uniform law on `(−1, 1)`, with the lower semicontinuous density `½ 1_{(−1,1)}`. -/
noncomputable def uniformPM1 : Measure ℝ :=
  volume.withDensity ((Ioo (-1 : ℝ) 1).indicator fun _ => 2⁻¹)

/-- The uniform law on `(−1, 1)` is `½` Lebesgue measure restricted to `(−1, 1)`. -/
theorem uniformPM1_eq : uniformPM1 = (2⁻¹ : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1) := by
  rw [uniformPM1, withDensity_indicator measurableSet_Ioo, withDensity_const]

/-- The uniform law on `(−1, 1)` is a probability measure. -/
theorem isProbabilityMeasure_uniformPM1 : IsProbabilityMeasure uniformPM1 := by
  refine ⟨?_⟩
  rw [uniformPM1_eq, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioo,
    show (1 : ℝ) - -1 = 2 by norm_num, ENNReal.ofReal_ofNat, smul_eq_mul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- The uniform law on `(−1, 1)` lives on `(−1, 1)`. -/
theorem ae_uniformPM1_mem : ∀ᵐ w ∂uniformPM1, w ∈ Ioo (-1 : ℝ) 1 := by
  rw [uniformPM1_eq]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _

/-- **Proposition 14.4.2 as printed is false** (MT p. 354): `W` uniform on `(−1, 1)` satisfies
(SBL2) (a lower semicontinuous density and finite variance), `E W = 0` and `E|W|ᵏ < ∞` for every
`k` (14.33), yet the bilinear model with `θ = 2`, `b = 0` (the AR(1) model `Xₙ₊₁ = 2Xₙ + Wₙ₊₁`)
is not positive Harris for any `ψ`: by Proposition 9.5.2 it is not even Harris. Some stability
condition such as `E|θ + bW|ᵏ < 1` must be added. -/
theorem proposition_14_4_2_counterexample :
    (∃ γ : ℝ → ℝ≥0∞, LowerSemicontinuous γ ∧ uniformPM1 = volume.withDensity γ) ∧
      (∀ k : ℕ, ∫⁻ w, ‖w‖ₑ ^ k ∂uniformPM1 ≠ ∞) ∧ ∫ w, w ∂uniformPM1 = 0 ∧
      ∀ ψ : Measure ℝ, haveI := isProbabilityMeasure_uniformPM1
        haveI := isMarkovKernel_bilinearKernel uniformPM1 2 0
        ¬ IsPositiveHarris (bilinearKernel uniformPM1 2 0) ψ := by
  have := isProbabilityMeasure_uniformPM1
  refine ⟨⟨_, isOpen_Ioo.lowerSemicontinuous_indicator zero_le, rfl⟩, fun k => ?_, ?_,
    fun ψ h => ?_⟩
  · refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂uniformPM1) ?_ (lintegral_mono_ae ?_)
    · rw [lintegral_one, measure_univ]
      exact ENNReal.one_ne_top
    · refine ae_uniformPM1_mem.mono fun w hw => pow_le_one₀ zero_le ?_
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.2 (abs_le.2 ⟨hw.1.le, hw.2.le⟩)
  · rw [uniformPM1_eq, integral_smul_measure, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num), integral_id]
    norm_num
  · have hk : bilinearKernel uniformPM1 2 0 = ar1Kernel uniformPM1 2 := by
      unfold bilinearKernel ar1Kernel
      congr 1
      funext p
      simp only [bilinearStep]
      ring
    have hR : uniformPM1 (Icc (-1 : ℝ) 1)ᶜ = 0 :=
      measure_mono_null (fun w hw h => hw (Ioo_subset_Icc_self h)) (ae_iff.1 ae_uniformPM1_mem)
    have hα := proposition_9_5_2_necessity uniformPM1 hR (ψ := ψ) (α := 2)
      (by convert h.1 using 1; exact hk.symm)
    rw [abs_of_pos two_pos] at hα
    linarith

end MeynTweedie.GeometricErgodicity
