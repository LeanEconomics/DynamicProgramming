/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.ShocksMonotone
import FixedPointArguments.MonotoneOLGExamples

/-!
# Partially observed shocks: Proposition 8 is false without Assumption 17.6

SLP §17.6, p. 540. Proposition 8 claims that under Assumptions 17.1, 17.4 and 17.5 every solution
`η` of (3) has a strictly increasing price function `ρ(z) = z/η(z)`. The corrected
`proposition_8` (`FixedPointArguments.ShocksMonotone`) adds Assumption 17.6 (uniform `Ψ`, `G`);
`proposition_8_general_counterexample` there shows only that the book's proof step (Exercise
17.14d) fails under Assumption 17.5. Here the proposition itself is refuted: an economy satisfying
all its hypotheses has a strictly positive continuous fixed point of (4) whose price function is
not invertible.

**The economy.** `x ~ U[1, 2]`, `θ` with the bimodal density `shocksExBimodal` on
`Θ = [1, 3/2]` (bumps on `[1, 11/10]` and `[7/5, 3/2]`), so `Z = [2/3, 2]`;
`H(l) = −l − log(1 − l)` on `[0, 1)`; `V(y) = A y^{1−σ}/(1 − σ)` with `A = 1/60000`, `σ = 1/20`
(`shocksP8V`).

* `monoCexH_assumption17_1H'`, `shocksP8V_assumptions`: Assumption 17.1 for `H`; the repaired
  Assumption 17.1, the repaired Assumption 17.2 (`β = 1 − σ`) and Assumption 17.4 for `V`
  (`Assumption17_1VR.const_mul`, `Assumption17_2R.const_mul`, `MonoAssumption17_4Pos.const_mul`,
  `crra_monoAssumption17_4Pos`).
* `shocksExBimodal_pi_pos`: `π > 0` on `int Z` (although `g` vanishes on `(11/10, 7/5)`), so
  Exercise 17.8b applies; `shocksP8_existsUnique_fixedPoint`: by Proposition 6, `T` has exactly
  one strictly positive continuous fixed point.
* `shocksP8_opT_eq`: with CRRA utility (4) separates, `Tf(z) = A M(f) K(z)` with
  `K(z) = E[θ^{σ−1} | z]`, since `φ(θ′η/θ̃) = A θ̃^{σ−1} (θ′η)^{1−σ}`.
* `shocksExBimodal_integral_inv_values`: `E[θ⁻¹ | z = 4/3] = 4/5`, `E[θ⁻¹ | z = 10/7] = 30/31`;
  `shocksP8_clamp_bounds`: `θ⁻¹ ≤ θ^{σ−1} ≤ (103/100) θ⁻¹` on `Θ`;
  `shocksExBimodal_condLaw_eq`: `G(·|z)` is the same for all `z ∈ [1, 4/3]`.
* `shocksP8_rho_ineq`: for **every** strictly positive fixed point, `ρ(10/7) < ρ(4/3)` and
  `ρ(1) < ρ(4/3)`. The a priori bound `η ≤ 1/200` (from `M ≤ 3/2`, `K ≤ 1` and the small `A`)
  makes `ζ(l) = l²/(1 − l)` nearly quadratic, and `K(10/7)/K(4/3) ≥ (30/31)/((103/100)(4/5))`
  exceeds `(15/14)²/(1 − 15/2800)`, the most that `ρ(4/3) ≤ ρ(10/7)` would allow.
* `shocksP8_not_injective`, **`proposition_8_counterexample`**: `ρ` is neither strictly
  increasing nor injective (intermediate value theorem on `[1, 4/3]` and `[4/3, 10/7]`).
  `proposition_8_assumption17_5_false`: the statement of `proposition_8` without
  Assumption 17.6 is false.
* **The book's Assumption 17.1.** The CRRA `V` has `V'(0) = ∞`, so it satisfies only the repaired
  Assumption 17.1. `shocksP8W y₀` agrees with it on `[y₀, ∞)` and is quadratic below `y₀`
  (`shocks_hasDerivAt_ite` glues the branches); `shocksP8W_assumptions`: it satisfies the book's
  Assumption 17.1 (`C²` on `ℝ₊`) and Assumption 17.4; `shocksP8W_opT_eq`: on fixed points with
  `η ≥ (3/2) y₀` the two operators (4) coincide. **`proposition_8_counterexample_book`**,
  **`proposition_8_false`**: Proposition 8 is false under its own hypotheses.

**Correction (Proposition 8, p. 540, is false).** Under Assumptions 17.1, 17.4 and 17.5 a solution
of (3) need not have an increasing (or even invertible) price function: in the economy above the
unique strictly positive solution under CRRA utility, and a strictly positive solution under a
utility satisfying the book's Assumption 17.1, has `ρ` rising on `[1, 4/3]` and falling from `4/3`
to `10/7`. As `z` rises past `x̄/θ = 10/7`, the conditional law of `θ` given `z` loses the upper
bump of `g`, so `E[θ^{σ−1} | z]` (hence `η`) jumps up faster than `z`. The proposition needs
Assumption 17.6 (`proposition_8`) or a monotone-likelihood condition on `G(·|z)`. Since the
operator also satisfies the hypotheses of Proposition 6, the economy has no equilibrium of the
form `p = ρ(x/θ)` with `ρ` continuous, positive and invertible.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

variable {V V' V'' : ℝ → ℝ}

/-- The repaired Assumption 17.1 is preserved by scaling `V` by `A > 0`. -/
theorem Assumption17_1VR.const_mul (hV : Assumption17_1VR V V' V'') {A : ℝ} (hA : 0 < A) :
    Assumption17_1VR (fun y => A * V y) (fun y => A * V' y) (fun y => A * V'' y) := by
  refine ⟨fun y hy => mul_nonneg hA.le (hV.V_nonneg y hy), continuousOn_const.mul hV.V_cont,
    fun y hy => (hV.V_deriv y hy).const_mul A, fun y hy => (hV.V'_deriv y hy).const_mul A,
    continuousOn_const.mul hV.V''_cont, fun x hx y hy hxy => mul_lt_mul_of_pos_left
    (hV.V_mono hx hy hxy) hA, ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩⟩
  have := hV.V_conc.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  nlinarith

/-- The repaired Assumption 17.2 is preserved by scaling `V` by `A > 0` (relative risk aversion
is unchanged). -/
theorem Assumption17_2R.const_mul {β : ℝ} (h : Assumption17_2R β V' V'') {A : ℝ} (hA : 0 < A) :
    Assumption17_2R β (fun y => A * V' y) (fun y => A * V'' y) := by
  have e : ∀ y, -(y * (A * V'' y)) / (A * V' y) = -(y * V'' y) / V' y := fun y => by
    rw [show -(y * (A * V'' y)) = A * -(y * V'' y) by ring, mul_div_mul_left _ _ hA.ne']
  exact ⟨h.β_nonneg, h.β_lt_one, fun y hy => by rw [e]; exact h.lower y hy,
    fun y hy => by rw [e]; exact h.upper y hy⟩

/-- Assumption 17.4 (on `ℝ₊₊`) is preserved by scaling `V` by `A > 0`. -/
theorem MonoAssumption17_4Pos.const_mul (h : MonoAssumption17_4Pos V' V'') {A : ℝ} (hA : 0 < A) :
    MonoAssumption17_4Pos (fun y => A * V' y) (fun y => A * V'' y) := by
  intro y hy
  have := h y hy
  simp only [monoRRA] at this ⊢
  rwa [show -y * (A * V'' y) = A * (-y * V'' y) by ring, mul_div_mul_left _ _ hA.ne']

/-- CRRA utility with `0 < σ < 1` satisfies Assumption 17.4 (relative risk aversion `σ ≤ 1`). -/
theorem crra_monoAssumption17_4Pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    MonoAssumption17_4Pos (fun y => y ^ (-σ)) (fun y => -σ * y ^ (-σ - 1)) := by
  intro y hy
  have h := (crra_assumption17_2R hσ0 hσ1).upper y hy
  simp only [monoRRA]
  have e : -y * (-σ * y ^ (-σ - 1)) / y ^ (-σ) = -(y * (-σ * y ^ (-σ - 1))) / y ^ (-σ) := by ring
  rw [e]
  have h1 : y * y ^ (-σ - 1) = y ^ (-σ) := by
    rw [Real.rpow_sub_one hy.ne', mul_div_cancel₀ _ hy.ne']
  have h2 : 0 < y ^ (-σ) := Real.rpow_pos_of_pos hy _
  rw [show -(y * (-σ * y ^ (-σ - 1))) = σ * (y * y ^ (-σ - 1)) by ring, h1,
    mul_div_assoc, div_self h2.ne', mul_one]
  linarith

/-- `H(l) = −l − log(1 − l)` satisfies Assumption 17.1 for `H` with `L = 1`. -/
theorem monoCexH_assumption17_1H' : Assumption17_1H 1 monoCexH monoCexH' monoCexH'' := by
  have h := monoCexH_assumption17_1H
  exact ⟨h.L_pos, h.nonneg, fun l hl => (h.hasDeriv_H l hl).mono Ico_subset_Ici_self,
    fun l hl => (h.hasDeriv_H' l hl).mono Ico_subset_Ici_self, h.continuousOn_H'',
    h.strictMonoOn, h.strictConvexOn, h.deriv_zero, h.tendsto_deriv⟩

/-- In the bimodal example `π(z) > 0` on `int Z = (2/3, 2)`: near `θ = 3/2` (upper bump) for
`z < 10/7`, near `θ = 1` (lower bump) for `z ≥ 10/7`. -/
theorem shocksExBimodal_pi_pos {z : ℝ} (hz : 1 / (3 / 2) < z ∧ z < 2 / 1) :
    0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := by
  have hA := shocksExBimodal_assumption
  have hz0 : 0 < z := lt_trans (by norm_num) hz.1
  have hψ1 : ∀ x ∈ Icc (1 : ℝ) 2, shocksUnif 1 2 x = 1 := fun x hx => by
    rw [shocksUnif, indicator_of_mem hx]; norm_num
  have hb1 : ∀ θ, 0 ≤ shocksExBump1 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have hb2 : ∀ θ, 0 ≤ shocksExBump2 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have key : ∀ a b : ℝ, a < b → (∀ θ ∈ Ioo a b,
      0 < shocksExBimodal θ * θ * shocksUnif 1 2 (z * θ)) →
      0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := fun a b hab hpos => by
    refine (integral_pos_iff_support_of_nonneg (fun θ => hA.joint_nonneg z θ)
      (hA.integrable_joint_slice z)).2 ?_
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo a b) fun θ hθ => (hpos θ hθ).ne')
    simp [hab]
  rcases lt_or_ge z (10 / 7) with h | h
  · refine key (max (7 / 5) (1 / z)) (min (3 / 2) (2 / z)) ?_ fun θ hθ => ?_
    · refine max_lt (lt_min (by norm_num) ?_) (lt_min ?_ ?_)
      · rw [lt_div_iff₀ hz0]; linarith
      · rw [div_lt_iff₀ hz0]; linarith [hz.1]
      · exact div_lt_div_of_pos_right (by norm_num) hz0
    · obtain ⟨h1, h2⟩ := hθ
      rw [max_lt_iff] at h1
      rw [lt_min_iff] at h2
      have hθ0 : 0 < θ := lt_trans (by norm_num) h1.1
      have e1 : 1 < z * θ := by rw [div_lt_iff₀ hz0] at h1; linarith [h1.2]
      have e2 : z * θ < 2 := by rw [lt_div_iff₀ hz0] at h2; linarith [h2.2]
      rw [hψ1 _ ⟨e1.le, e2.le⟩, mul_one]
      refine mul_pos ?_ hθ0
      have : shocksExBump2 θ = θ - 7 / 5 := by
        rw [shocksExBump2, indicator_of_mem
          (show θ ∈ Icc (7 / 5 : ℝ) (3 / 2) from ⟨h1.1.le, h2.1.le⟩)]
      simp only [shocksExBimodal]
      linarith [hb1 θ, h1.1]
  · refine key 1 (min (11 / 10) (2 / z)) (lt_min (by norm_num) ?_) fun θ hθ => ?_
    · rw [lt_div_iff₀ hz0]; linarith [hz.2]
    · obtain ⟨h1, h2⟩ := hθ
      rw [lt_min_iff] at h2
      have hθ0 : 0 < θ := lt_trans one_pos h1
      have e1 : 1 < z * θ := by nlinarith
      have e2 : z * θ < 2 := by rw [lt_div_iff₀ hz0] at h2; linarith [h2.2]
      rw [hψ1 _ ⟨e1.le, e2.le⟩, mul_one]
      refine mul_pos ?_ hθ0
      have : shocksExBump1 θ = 11 / 10 - θ := by
        rw [shocksExBump1, indicator_of_mem (show θ ∈ Icc (1 : ℝ) (11 / 10) from ⟨h1.le, h2.1.le⟩)]
      simp only [shocksExBimodal]
      linarith [hb2 θ, h2.1]

/-- In the bimodal example, `E[θ⁻¹ | z = 4/3] = 4/5` and `E[θ⁻¹ | z = 10/7] = 30/31`
(the computation of `proposition_8_general_counterexample`). -/
theorem shocksExBimodal_integral_inv_values :
    (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (4 / 3)) = 4 / 5 ∧
      (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (10 / 7)) =
        30 / 31 := by
  have hA := shocksExBimodal_assumption
  obtain ⟨j1, j2, j3, j4⟩ := shocksExBump_integrals
  have i3 : Integrable fun θ => shocksExBump1 θ * θ := by
    have : (fun θ => shocksExBump1 θ * θ) =
        (Icc (1 : ℝ) (11 / 10)).indicator fun θ => (11 / 10 - θ) * θ := by
      ext θ; simp only [shocksExBump1]
      by_cases h : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i4 : Integrable fun θ => shocksExBump2 θ * θ := by
    have : (fun θ => shocksExBump2 θ * θ) =
        (Icc (7 / 5 : ℝ) (3 / 2)).indicator fun θ => (θ - 7 / 5) * θ := by
      ext θ; simp only [shocksExBump2]
      by_cases h : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hψ1 : ∀ x ∈ Icc (1 : ℝ) 2, shocksUnif 1 2 x = 1 := fun x hx => by
    rw [shocksUnif, indicator_of_mem hx]; norm_num
  have hψ0 : ∀ x, 2 < x → shocksUnif 1 2 x = 0 := fun x hx => by
    rw [shocksUnif, indicator_of_notMem fun h => by linarith [h.2]]
  have hgΘ : ∀ θ, θ ∉ Icc (1 : ℝ) (3 / 2) → shocksExBimodal θ = 0 := hA.g_zero
  have a1 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = shocksExBimodal θ := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one]
    · rw [hgΘ θ h, zero_mul]
  have b1 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (4 / 3 * θ) =
      100 * (shocksExBump1 θ * θ + shocksExBump2 θ * θ) := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one, shocksExBimodal]; ring
    · have h1 : θ ∉ Icc (1 : ℝ) (11 / 10) := fun h' => h ⟨h'.1, by linarith [h'.2]⟩
      have h2 : θ ∉ Icc (7 / 5 : ℝ) (3 / 2) := fun h' => h ⟨by linarith [h'.1], h'.2⟩
      simp [hgΘ θ h, shocksExBump1, shocksExBump2, indicator_of_notMem h1,
        indicator_of_notMem h2]
  have a2 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 100 * shocksExBump1 θ :=
    fun θ => by
      simp only [shocksExBimodal, shocksExBump1, shocksExBump2]
      by_cases h1 : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h => by linarith [h.1, h1.2]),
          hψ1 _ ⟨by linarith [h1.1], by linarith [h1.2]⟩]
        ring
      · rw [indicator_of_notMem h1]
        by_cases h2 : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
        · rw [indicator_of_mem h2]
          rcases h2.1.eq_or_lt with h3 | h3
          · rw [← h3]; ring
          · rw [hψ0 _ (by linarith)]; ring
        · rw [indicator_of_notMem h2]; ring
  have b2 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
      100 * (shocksExBump1 θ * θ) := fun θ => by
    have := a2 θ
    calc shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
        shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) * θ := by ring
      _ = 100 * (shocksExBump1 θ * θ) := by rw [this]; ring
  have π1 : shocksPi (shocksUnif 1 2) shocksExBimodal (4 / 3) = 5 / 4 := by
    simp only [shocksPi]
    simp_rw [b1]
    rw [integral_const_mul, integral_add i3 i4, j3, j4]; norm_num
  have π2 : shocksPi (shocksUnif 1 2) shocksExBimodal (10 / 7) = 31 / 60 := by
    simp only [shocksPi]
    simp_rw [b2]
    rw [integral_const_mul, j3]; norm_num
  have N1 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = 1 := by
    simp_rw [a1]; exact hA.g_int
  have N2 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 1 / 2 := by
    simp_rw [a2]; rw [integral_const_mul, j1]; norm_num
  rw [shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π1]; norm_num),
    shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π2]; norm_num), π1, π2,
    N1, N2]
  norm_num

/-- Against `G(·|z)`, the clamp is invisible. -/
theorem shocksExBimodal_integral_clamp {z : ℝ} (hz : 1 / (3 / 2) < z ∧ z < 2 / 1)
    (k : ℝ → ℝ) :
    ∫ θ, k (shocksClamp 1 (3 / 2) θ) ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2)
      shocksExBimodal z =
      ∫ θ, k θ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z := by
  have hA := shocksExBimodal_assumption
  rw [hA.integral_condLaw hz (shocksExBimodal_pi_pos hz),
    hA.integral_condLaw hz (shocksExBimodal_pi_pos hz)]
  congr 1
  ext θ
  by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
  · rw [shocksClamp_of_mem h]
  · simp [shocksCondDens, hA.g_zero θ h]

/-- The utility `V(y) = A y^{1−σ}/(1 − σ)` with `A = 1/60000`, `σ = 1/20`. -/
noncomputable def shocksP8V (y : ℝ) : ℝ := 1 / 60000 * (y ^ (1 - 1 / 20 : ℝ) / (1 - 1 / 20))

/-- `V'(y) = A y^{−σ}`. -/
noncomputable def shocksP8V' (y : ℝ) : ℝ := 1 / 60000 * y ^ (-(1 / 20) : ℝ)

/-- `V''(y) = −A σ y^{−σ−1}`. -/
noncomputable def shocksP8V'' (y : ℝ) : ℝ := 1 / 60000 * (-(1 / 20) * y ^ (-(1 / 20) - 1 : ℝ))

/-- `shocksP8V` satisfies the repaired Assumption 17.1, the repaired Assumption 17.2 with
`β = 1 − σ`, and Assumption 17.4. -/
theorem shocksP8V_assumptions : Assumption17_1VR shocksP8V shocksP8V' shocksP8V'' ∧
    Assumption17_2R (1 - 1 / 20) shocksP8V' shocksP8V'' ∧
    MonoAssumption17_4Pos shocksP8V' shocksP8V'' :=
  ⟨(crra_assumption17_1VR (σ := 1 / 20) (by norm_num) (by norm_num)).const_mul (by norm_num),
    (crra_assumption17_2R (σ := 1 / 20) (by norm_num) (by norm_num)).const_mul (by norm_num),
    (crra_monoAssumption17_4Pos (σ := 1 / 20) (by norm_num) (by norm_num)).const_mul
      (by norm_num)⟩

/-- `φ(y) = A y^{1−σ}`, split at `y = (c′/c̃) e`. -/
theorem shocksP8_phi_eq {c' ct e : ℝ} (hc' : 0 < c') (hct : 0 < ct) (he : 0 < e) :
    olgPhi shocksP8V' (c' / ct * e) =
      1 / 60000 * (ct ^ (1 - 1 / 20 : ℝ))⁻¹ * (c' * e) ^ (1 - 1 / 20 : ℝ) := by
  have hy : 0 < c' / ct * e := mul_pos (div_pos hc' hct) he
  simp only [olgPhi, shocksP8V']
  have h1 : c' / ct * e * (c' / ct * e) ^ (-(1 / 20) : ℝ) = (c' / ct * e) ^ (1 - 1 / 20 : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add hy, Real.rpow_one]
  rw [show c' / ct * e * (1 / 60000 * (c' / ct * e) ^ (-(1 / 20) : ℝ)) =
    1 / 60000 * (c' / ct * e * (c' / ct * e) ^ (-(1 / 20) : ℝ)) by ring, h1,
    show c' / ct * e = c' * e / ct by ring, Real.div_rpow (mul_pos hc' he).le hct.le]
  ring

variable {Z : Type*} [MeasurableSpace Z] {L : ℝ} {H H' H'' : ℝ → ℝ}

/-- With this utility, (4) separates: `Tf(z) = A M(f) K(z)`. -/
theorem shocksP8_opT_eq (hH : Assumption17_1H L H H' H'') (μ : Measure (ℝ × Z))
    (ν : Z → Measure ℝ) (f : Z → ℝ) (hf : ∀ z, 0 < f z) (z : Z) :
    shocksOpT L H' shocksP8V' 1 (3 / 2) μ ν f z =
      1 / 60000 * (∫ ω, (shocksClamp 1 (3 / 2) ω.1 * olgZetaInv L H' (f ω.2)) ^
        (1 - 1 / 20 : ℝ) ∂μ) * ∫ θ, (shocksClamp 1 (3 / 2) θ ^ (1 - 1 / 20 : ℝ))⁻¹ ∂ν z := by
  have hc : ∀ t, 0 < shocksClamp 1 (3 / 2) t := fun t =>
    one_pos.trans_le (shocksClamp_mem (by norm_num) t).1
  have hphi : ∀ θt, shocksPhiF L H' shocksP8V' 1 (3 / 2) μ f θt =
      (1 / 60000 * (shocksClamp 1 (3 / 2) θt ^ (1 - 1 / 20 : ℝ))⁻¹) *
        ∫ ω, (shocksClamp 1 (3 / 2) ω.1 * olgZetaInv L H' (f ω.2)) ^ (1 - 1 / 20 : ℝ) ∂μ := by
    intro θt
    rw [← integral_const_mul]
    simp only [shocksPhiF, shocksIntegrand, shocksRatio]
    congr 1
    ext ω
    exact shocksP8_phi_eq (hc _) (hc _) (hH.zetaInv_pos (hf ω.2))
  simp only [shocksOpT]
  simp_rw [hphi]
  rw [integral_mul_const, integral_const_mul]
  ring

/-- `Z = [x̲/θ̄, x̄/θ̲] = [2/3, 2]` is nonempty. -/
theorem shocksP8_hZ : (1 : ℝ) / (3 / 2) ≤ 2 / 1 := by norm_num

/-- For `z ∈ [1, 4/3]` the conditional law of `θ` does not depend on `z`. -/
theorem shocksExBimodal_condLaw_eq {z : ℝ} (hz : z ∈ Icc (1 : ℝ) (4 / 3)) :
    shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z =
      shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal 1 := by
  have hA := shocksExBimodal_assumption
  have e : ∀ w ∈ Icc (1 : ℝ) (4 / 3), ∀ θ,
      shocksExBimodal θ * θ * shocksUnif 1 2 (w * θ) = shocksExBimodal θ * θ := by
    intro w hw θ
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [shocksUnif, indicator_of_mem (show w * θ ∈ Icc (1 : ℝ) 2 from
        ⟨by nlinarith [hw.1, h.1], by nlinarith [hw.2, h.2, hw.1, h.1]⟩)]
      norm_num
    · rw [hA.g_zero θ h]; ring
  have hd : ∀ w ∈ Icc (1 : ℝ) (4 / 3), shocksCondDens (shocksUnif 1 2) shocksExBimodal w =
      fun θ => shocksExBimodal θ * θ / ∫ t, shocksExBimodal t * t := by
    intro w hw
    ext θ
    simp only [shocksCondDens, shocksPi]
    rw [e w hw θ]
    simp_rw [e w hw]
  have hz' : 1 / (3 / 2) < z ∧ z < 2 / 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have h1 : (1 : ℝ) / (3 / 2) < 1 ∧ (1 : ℝ) < 2 / 1 := ⟨by norm_num, by norm_num⟩
  simp only [shocksCondLaw, hz', h1, and_self, ↓reduceIte]
  rw [hd z hz, hd 1 ⟨le_rfl, by norm_num⟩]

/-- Bounds on the clamp's power: `c⁻¹ ≤ (c^{1−σ})⁻¹ ≤ min(1, (103/100) c⁻¹)`. -/
theorem shocksP8_clamp_bounds (t : ℝ) :
    0 ≤ (shocksClamp 1 (3 / 2) t)⁻¹ ∧
    (shocksClamp 1 (3 / 2) t)⁻¹ ≤ (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹ ∧
    (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹ ≤ 1 ∧
    (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹ ≤ 103 / 100 * (shocksClamp 1 (3 / 2) t)⁻¹ := by
  obtain ⟨h1, h2⟩ := shocksClamp_mem (θlo := (1 : ℝ)) (θhi := 3 / 2) (by norm_num) t
  set c := shocksClamp 1 (3 / 2) t
  have hc : 0 < c := one_pos.trans_le h1
  have hp : 0 < c ^ (1 - 1 / 20 : ℝ) := Real.rpow_pos_of_pos hc _
  have hσ : c ^ (1 / 20 : ℝ) ≤ 103 / 100 := by
    have h3 : c ^ (1 / 20 : ℝ) ≤ (3 / 2 : ℝ) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow hc.le h2 (by norm_num)
    have h4 : (3 / 2 : ℝ) ^ (1 / 20 : ℝ) ≤ ((103 / 100 : ℝ) ^ (20 : ℕ)) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h4
    norm_num at h4
    exact h3.trans h4
  have hσ0 : 0 < c ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hc _
  have e : c ^ (1 - 1 / 20 : ℝ) = c / c ^ (1 / 20 : ℝ) := by
    rw [Real.rpow_sub hc, Real.rpow_one]
  refine ⟨inv_nonneg.2 hc.le, inv_anti₀ hp ?_, inv_le_one_of_one_le₀ ?_, ?_⟩
  · calc c ^ (1 - 1 / 20 : ℝ) ≤ c ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = c := Real.rpow_one c
  · exact Real.one_le_rpow h1 (by norm_num)
  · rw [e, inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hσ (inv_nonneg.2 hc.le)

/-- The functions `c(t)⁻¹` and `(c(t)^{1−σ})⁻¹` are continuous. -/
theorem shocksP8_continuous :
    Continuous (fun t => (shocksClamp 1 (3 / 2) t)⁻¹) ∧
      Continuous (fun t => (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹) := by
  have hc : ∀ t, 0 < shocksClamp 1 (3 / 2) t := fun t =>
    one_pos.trans_le (shocksClamp_mem (by norm_num) t).1
  exact ⟨continuous_shocksClamp.inv₀ fun t => (hc t).ne',
    (continuous_shocksClamp.rpow_const fun _ => Or.inr (by norm_num)).inv₀
      fun t => (Real.rpow_pos_of_pos (hc t) _).ne'⟩

/-- `ζ(y) = y²/(1 − y)` for `H'(l) = l/(1 − l)`. -/
theorem shocksP8_zeta_eq {y F : ℝ} (hy : y < 1) (h : olgZeta monoCexH' y = F) :
    F * (1 - y) = y ^ 2 := by
  have h1 : 1 - y ≠ 0 := (sub_pos.2 hy).ne'
  rw [← h]
  simp only [olgZeta, monoCexH']
  field_simp

/-- **The key estimate.** For every strictly positive fixed point `f` of `T` in the bimodal economy,
with `η = ζ⁻¹ ∘ f` and `ρ(z) = z/η(z)`: `ρ(10/7) < ρ(4/3)` and `ρ(1) < ρ(4/3)`. -/
theorem shocksP8_rho_ineq (f : Icc (1 / (3 / 2) : ℝ) (2 / 1) → ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) :
    (10 / 7 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨10 / 7, by norm_num, by norm_num⟩) <
        (4 / 3 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨4 / 3, by norm_num, by norm_num⟩) ∧
      (1 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨1, by norm_num, by norm_num⟩) <
        (4 / 3 : ℝ) / olgZetaInv 1 monoCexH' (f ⟨4 / 3, by norm_num, by norm_num⟩) := by
  have hH := monoCexH_assumption17_1H'
  have hA := shocksExBimodal_assumption
  have hπ : ∀ z : ℝ, 1 / (3 / 2) < z ∧ z < 2 / 1 →
      0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := fun z hz => shocksExBimodal_pi_pos hz
  have := isProbabilityMeasure_shocksJointLaw hA shocksP8_hZ
  have hν : ∀ z : ℝ, IsProbabilityMeasure
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) :=
    hA.isProbabilityMeasure_condLaw' hπ
  obtain ⟨hcon1, hcon2⟩ := shocksP8_continuous
  set μ := shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal
  set η := fun z => olgZetaInv 1 monoCexH' (f z) with hηdef
  set M := ∫ ω, (shocksClamp 1 (3 / 2) ω.1 * η ω.2) ^ (1 - 1 / 20 : ℝ) ∂μ with hMdef
  set K := fun z : ℝ => ∫ θ, (shocksClamp 1 (3 / 2) θ ^ (1 - 1 / 20 : ℝ))⁻¹
    ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z with hKdef
  have hfK : ∀ z, f z = 1 / 60000 * M * K z := fun z => by
    rw [hfix z, shocksP8_opT_eq hH μ _ f hfpos z]
  have hηmem : ∀ z, η z ∈ Ioo 0 1 := fun z =>
    ⟨hH.zetaInv_pos (hfpos z), (hH.zetaInv_mem (hfpos z).le).2⟩
  have hζ : ∀ z, f z * (1 - η z) = η z ^ 2 := fun z =>
    shocksP8_zeta_eq (hηmem z).2 (hH.zeta_zetaInv (hfpos z).le)
  -- bounds on `M` and `K`
  have hc : ∀ t, shocksClamp 1 (3 / 2) t ∈ Icc (1 : ℝ) (3 / 2) := shocksClamp_mem (by norm_num)
  have hM0 : 0 ≤ M := integral_nonneg fun ω => Real.rpow_nonneg
    (mul_nonneg (one_pos.trans_le (hc ω.1).1).le (hηmem ω.2).1.le) _
  have hM1 : M ≤ 3 / 2 := by
    have : M ≤ ∫ _ω, (3 / 2 : ℝ) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun ω => Real.rpow_nonneg
        (mul_nonneg (one_pos.trans_le (hc ω.1).1).le (hηmem ω.2).1.le) _) (integrable_const _)
        (ae_of_all _ fun ω => ?_)
      have h1 := hc ω.1
      have h2 := hηmem ω.2
      have h3 : shocksClamp 1 (3 / 2) ω.1 * η ω.2 ≤ 3 / 2 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
      calc (shocksClamp 1 (3 / 2) ω.1 * η ω.2) ^ (1 - 1 / 20 : ℝ)
          ≤ (3 / 2 : ℝ) ^ (1 - 1 / 20 : ℝ) :=
            Real.rpow_le_rpow (mul_nonneg (by linarith [h1.1]) h2.1.le) h3 (by norm_num)
        _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 / 2 := Real.rpow_one _
    rwa [integral_const, probReal_univ, one_smul] at this
  have hK0 : ∀ z, 0 ≤ K z := fun z => integral_nonneg fun θ =>
    le_trans (shocksP8_clamp_bounds θ).1 (shocksP8_clamp_bounds θ).2.1
  have hK1 : ∀ z, K z ≤ 1 := fun z => by
    have : K z ≤ ∫ _θ, (1 : ℝ) ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z :=
      integral_mono_of_nonneg (ae_of_all _ fun θ =>
        le_trans (shocksP8_clamp_bounds θ).1 (shocksP8_clamp_bounds θ).2.1) (integrable_const _)
        (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).2.2.1)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hint : ∀ z, Integrable (fun t => (shocksClamp 1 (3 / 2) t)⁻¹)
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) := fun z =>
    Integrable.of_bound hcon1.aestronglyMeasurable 1 (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (shocksP8_clamp_bounds t).1]
      exact (shocksP8_clamp_bounds t).2.1.trans (shocksP8_clamp_bounds t).2.2.1)
  have hint' : ∀ z, Integrable (fun t => (shocksClamp 1 (3 / 2) t ^ (1 - 1 / 20 : ℝ))⁻¹)
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) := fun z =>
    Integrable.of_bound hcon2.aestronglyMeasurable 1 (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((shocksP8_clamp_bounds t).1.trans
        (shocksP8_clamp_bounds t).2.1)]
      exact (shocksP8_clamp_bounds t).2.2.1)
  obtain ⟨v1, v2⟩ := shocksExBimodal_integral_inv_values
  have hK2 : 30 / 31 ≤ K (10 / 7) := by
    rw [← v2, ← shocksExBimodal_integral_clamp ⟨by norm_num, by norm_num⟩ fun t => t⁻¹]
    exact integral_mono_of_nonneg (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).1) (hint' _)
      (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).2.1)
  have hK43 : K (4 / 3) ≤ 103 / 100 * (4 / 5) := by
    rw [← v1, ← shocksExBimodal_integral_clamp ⟨by norm_num, by norm_num⟩ fun t => t⁻¹,
      ← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun θ =>
      (shocksP8_clamp_bounds θ).1.trans (shocksP8_clamp_bounds θ).2.1) ((hint _).const_mul _)
      (ae_of_all _ fun θ => (shocksP8_clamp_bounds θ).2.2.2)
  have hKeq : K 1 = K (4 / 3) := by
    simp only [hKdef]
    rw [shocksExBimodal_condLaw_eq (z := 4 / 3) ⟨by norm_num, by norm_num⟩]
  -- `η ≤ 1/200`
  have hηle : ∀ z, η z ≤ 1 / 200 := fun z => by
    have h1 : f z ≤ 1 / 40000 := by
      rw [hfK z]
      have := mul_le_mul hM1 (hK1 z) (hK0 z) (by norm_num)
      nlinarith
    have h2 := hζ z
    have h3 := hηmem z
    nlinarith [h3.1, h3.2, hfpos z]
  -- the comparison
  set z₁ : Icc (1 / (3 / 2) : ℝ) (2 / 1) := ⟨4 / 3, by norm_num, by norm_num⟩
  set z₂ : Icc (1 / (3 / 2) : ℝ) (2 / 1) := ⟨10 / 7, by norm_num, by norm_num⟩
  set z₀ : Icc (1 / (3 / 2) : ℝ) (2 / 1) := ⟨1, by norm_num, by norm_num⟩
  have hP : 0 < 1 / 60000 * M := by
    by_contra h
    push Not at h
    have := hfpos z₁
    rw [hfK z₁] at this
    nlinarith [hK0 (4 / 3)]
  have hη1 := hηmem z₁
  have hη2 := hηmem z₂
  refine ⟨?_, ?_⟩
  · rw [div_lt_div_iff₀ hη2.1 hη1.1]
    by_contra hcon
    push Not at hcon
    -- `η₂ ≤ s = (15/14) η₁`
    set s := 15 / 14 * η z₁
    have hs : η z₂ ≤ s := by simp only [s]; linarith
    have hs1 : s ≤ 15 / 2800 := by simp only [s]; linarith [hηle z₁]
    have e1 := hζ z₁
    have e2 := hζ z₂
    have hf2 := hfpos z₂
    have hf1 := hfpos z₁
    have step1 : f z₂ * (1 - 15 / 2800) ≤ f z₂ * (1 - η z₂) :=
      mul_le_mul_of_nonneg_left (by linarith) hf2.le
    have step2 : η z₂ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hη2.1.le hs 2
    have step3 : s ^ 2 = 225 / 196 * (f z₁ * (1 - η z₁)) := by rw [e1]; simp only [s]; ring
    have step4 : f z₁ * (1 - η z₁) ≤ f z₁ := by nlinarith [hη1.1]
    have key : f z₂ * (1 - 15 / 2800) ≤ 225 / 196 * f z₁ := by nlinarith
    rw [hfK z₁, hfK z₂] at key
    have key' : (1 / 60000 * M) * (K (10 / 7) * (1 - 15 / 2800)) ≤
        (1 / 60000 * M) * (225 / 196 * K (4 / 3)) := by
      have : (1 / 60000 * M) * (K (10 / 7) * (1 - 15 / 2800)) =
          1 / 60000 * M * K (10 / 7) * (1 - 15 / 2800) := by ring
      rw [this]
      linarith
    have := le_of_mul_le_mul_left key' hP
    linarith
  · have hf : f z₀ = f z₁ := by
      rw [hfK z₀, hfK z₁]
      change 1 / 60000 * M * K 1 = 1 / 60000 * M * K (4 / 3)
      rw [hKeq]
    have he : η z₀ = η z₁ := by simp only [hηdef, hf]
    change (1 : ℝ) / η z₀ < (4 / 3 : ℝ) / η z₁
    rw [he]
    exact div_lt_div_of_pos_right (by norm_num) hη1.1

/-- The bimodal economy has exactly one strictly positive continuous fixed point of `T`
(Proposition 6 applies: the CRRA utility satisfies the repaired Assumption 17.2). -/
theorem shocksP8_existsUnique_fixedPoint :
    ∃! f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) ∧
      ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
        (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
        (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z := by
  have hA := shocksExBimodal_assumption
  have hπ : ∀ z : ℝ, 1 / (3 / 2) < z ∧ z < 2 / 1 →
      0 < shocksPi (shocksUnif 1 2) shocksExBimodal z := fun z hz => shocksExBimodal_pi_pos hz
  have := isProbabilityMeasure_shocksJointLaw hA shocksP8_hZ
  have : ∀ z : Icc (1 / (3 / 2) : ℝ) (2 / 1),
      IsProbabilityMeasure (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) :=
    fun z => hA.isProbabilityMeasure_condLaw' hπ z.1
  have : Nonempty (Icc (1 / (3 / 2) : ℝ) (2 / 1)) := ⟨⟨_, left_mem_Icc.2 shocksP8_hZ⟩⟩
  exact proposition_6 hA.θlo_pos hA.θlo_lt.le monoCexH_assumption17_1H' shocksP8V_assumptions.1
    shocksP8V_assumptions.2.1 _ _ fun h => (hA.ex_17_8b hπ h).domRestrict

/-- For every strictly positive continuous fixed point of `T` in the bimodal economy, the price
function `ρ(z) = z/ζ⁻¹(f(z))` is not invertible (it rises on `[1, 4/3]` and falls between `4/3`
and `10/7`), and in particular not strictly increasing. -/
theorem shocksP8_not_injective (f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) :
    ¬ Function.Injective (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
        (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) ∧
      ¬ StrictMono (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
        (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) := by
  have hH := monoCexH_assumption17_1H'
  obtain ⟨h1, h2⟩ := shocksP8_rho_ineq f hfpos hfix
  set r := fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) => (z : ℝ) / olgZetaInv 1 monoCexH' (f z)
    with hrdef
  refine ⟨fun hinj => ?_, fun hmono => ?_⟩
  · have hr : Continuous r := continuous_subtype_val.div
      (hH.zetaInv_continuousOn.comp_continuous f.continuous fun z => (hfpos z).le)
      fun z => (hH.zetaInv_pos (hfpos z)).ne'
    set R : ℝ → ℝ := fun t => r (projIcc _ _ shocksP8_hZ t) with hRdef
    have hR : Continuous R := hr.comp continuous_projIcc
    have hRv : ∀ t (ht : t ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1)), R t = r ⟨t, ht⟩ := fun t ht => by
      simp only [hRdef, projIcc_of_mem _ ht]
    have e0 := hRv 1 ⟨by norm_num, by norm_num⟩
    have e1 := hRv (4 / 3) ⟨by norm_num, by norm_num⟩
    have e2 := hRv (10 / 7) ⟨by norm_num, by norm_num⟩
    have h1' : R (10 / 7) < R (4 / 3) := by rw [e1, e2]; exact h1
    have h2' : R 1 < R (4 / 3) := by rw [e0, e1]; exact h2
    obtain ⟨v, hvdef⟩ : ∃ v, v = (max (R 1) (R (10 / 7)) + R (4 / 3)) / 2 := ⟨_, rfl⟩
    have hv : max (R 1) (R (10 / 7)) < R (4 / 3) := max_lt h2' h1'
    have hv1 : v ∈ Icc (R 1) (R (4 / 3)) :=
      ⟨by linarith [le_max_left (R 1) (R (10 / 7))], by linarith⟩
    have hv2 : v ∈ Icc (R (10 / 7)) (R (4 / 3)) :=
      ⟨by linarith [le_max_right (R 1) (R (10 / 7))], by linarith⟩
    obtain ⟨t1, ht1, hRt1⟩ :=
      intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 4 / 3) hR.continuousOn hv1
    obtain ⟨t2, ht2, hRt2⟩ :=
      intermediate_value_Icc' (by norm_num : (4 / 3 : ℝ) ≤ 10 / 7) hR.continuousOn hv2
    have hne : t1 ≠ 4 / 3 := fun h => by rw [h] at hRt1; linarith
    have hlt : t1 < t2 := lt_of_lt_of_le (lt_of_le_of_ne ht1.2 hne) ht2.1
    have heq := hinj (a₁ := projIcc _ _ shocksP8_hZ t1) (a₂ := projIcc _ _ shocksP8_hZ t2)
      (by change R t1 = R t2; rw [hRt1, hRt2])
    have hm1 : t1 ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1) := by
      constructor <;> norm_num <;> linarith [ht1.1, ht1.2]
    have hm2 : t2 ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1) := by
      constructor <;> norm_num <;> linarith [ht2.1, ht2.2]
    rw [projIcc_of_mem _ hm1, projIcc_of_mem _ hm2] at heq
    exact hlt.ne (Subtype.mk.inj heq)
  · have := hmono (a := ⟨4 / 3, by norm_num, by norm_num⟩) (b := ⟨10 / 7, by norm_num, by norm_num⟩)
      (by change (4 / 3 : ℝ) < 10 / 7; norm_num)
    exact absurd this (not_lt.2 h1.le)

/-- **Proposition 8 under Assumption 17.5 alone: counterexample.** In the economy
`x ~ U[1, 2]`, `θ` with the bimodal density `shocksExBimodal` on `Θ = [1, 3/2]` (Assumption 17.5),
`H(l) = −l − log(1 − l)` on `[0, 1)` (Assumption 17.1) and
`V(y) = A y^{1−σ}/(1 − σ)`, `A = 1/60000`, `σ = 1/20` (the repaired Assumption 17.1, the repaired
Assumption 17.2 with `β = 1 − σ`, and Assumption 17.4), the operator (4) has exactly one strictly
positive continuous fixed point (Proposition 6), and for it, as for every strictly positive fixed
point, the price function `ρ(z) = z/ζ⁻¹(f(z))` is neither strictly increasing nor even
invertible. So the fixed point does not describe an equilibrium. -/
theorem proposition_8_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal ∧
      Assumption17_1H 1 monoCexH monoCexH' monoCexH'' ∧
      Assumption17_1VR shocksP8V shocksP8V' shocksP8V'' ∧
      Assumption17_2R (1 - 1 / 20) shocksP8V' shocksP8V'' ∧
      MonoAssumption17_4Pos shocksP8V' shocksP8V'' ∧
      (∃! f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) ∧
        ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
          (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) ∧
      ∀ f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) →
        (∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
          (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) →
        ¬ Function.Injective (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
          (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) :=
  ⟨shocksExBimodal_assumption, monoCexH_assumption17_1H', shocksP8V_assumptions.1,
    shocksP8V_assumptions.2.1, shocksP8V_assumptions.2.2, shocksP8_existsUnique_fixedPoint,
    fun f hfpos hfix => (shocksP8_not_injective f hfpos hfix).1⟩

/-- **Correction (Proposition 8 is false under Assumption 17.5 alone).** The statement of
`proposition_8` without Assumption 17.6 (uniform `Ψ`, `G`) fails: see
`proposition_8_counterexample`. -/
theorem proposition_8_assumption17_5_false :
    ¬ ∀ (xlo xhi θlo θhi : ℝ) (hZ : xlo / θhi ≤ xhi / θlo) (ψ g : ℝ → ℝ) (L : ℝ)
      (H H' H'' V V' V'' : ℝ → ℝ), ShocksAssumption17_5 xlo xhi θlo θhi ψ g →
      Assumption17_1H L H H' H'' → Assumption17_1VR V V' V'' → MonoAssumption17_4Pos V' V'' →
      ∀ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) →
      (∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z) →
      StrictMono fun z : Icc (xlo / θhi) (xhi / θlo) => (z : ℝ) / olgZetaInv L H' (f z) := by
  intro h
  obtain ⟨f, ⟨hfpos, hfix⟩, -⟩ := shocksP8_existsUnique_fixedPoint
  exact (shocksP8_not_injective f hfpos hfix).2 (h 1 2 1 (3 / 2) shocksP8_hZ _ _ 1 _ _ _ _ _ _
    shocksExBimodal_assumption monoCexH_assumption17_1H' shocksP8V_assumptions.1
    shocksP8V_assumptions.2.2 f hfpos hfix)

/-! ### The book's Assumption 17.1: a utility with `V'(0) < ∞` -/

/-- Gluing two differentiable branches at `y₀` with matching values and derivatives. -/
theorem shocks_hasDerivAt_ite {g h : ℝ → ℝ} {y₀ y d : ℝ} (hg : y₀ ≤ y → HasDerivAt g d y)
    (hh : y ≤ y₀ → HasDerivAt h d y) (heq : g y₀ = h y₀) :
    HasDerivAt (fun t => if y₀ ≤ t then g t else h t) d y := by
  rcases lt_trichotomy y y₀ with hy | hy | hy
  · refine (hh hy.le).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hy] with t ht
    simp [not_le.2 (mem_Iio.1 ht)]
  · subst hy
    have h1 : HasDerivWithinAt (fun t => if y ≤ t then g t else h t) d (Ici y) y :=
      (hg le_rfl).hasDerivWithinAt.congr (fun t ht => by simp [mem_Ici.1 ht]) (by simp)
    have h2 : HasDerivWithinAt (fun t => if y ≤ t then g t else h t) d (Iic y) y := by
      refine (hh le_rfl).hasDerivWithinAt.congr (fun t ht => ?_) (by simp [heq])
      rcases (mem_Iic.1 ht).eq_or_lt with h' | h'
      · subst h'; simp [heq]
      · simp [not_le.2 h']
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · refine (hg hy.le).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with t ht
    simp [(mem_Ioi.1 ht).le]

/-- The utility `W = V` on `[y₀, ∞)` (the CRRA utility `shocksP8V`, shifted to be continuous),
and below `y₀` the quadratic with `W(0) = 0` whose derivative continues `V'` linearly. -/
noncomputable def shocksP8W (y₀ y : ℝ) : ℝ :=
  if y₀ ≤ y then shocksP8V y - shocksP8V y₀ +
    1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * ((1 + 1 / 20) * y₀ - 1 / 20 * y₀ ^ 2 / (2 * y₀))
  else 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * ((1 + 1 / 20) * y - 1 / 20 * y ^ 2 / (2 * y₀))

/-- `W' = V'` on `[y₀, ∞)`, linear below `y₀`. -/
noncomputable def shocksP8W' (y₀ y : ℝ) : ℝ :=
  if y₀ ≤ y then shocksP8V' y else 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * y / y₀)

/-- `W'' = V''` on `[y₀, ∞)`, constant below `y₀`. -/
noncomputable def shocksP8W'' (y₀ y : ℝ) : ℝ :=
  1 / 60000 * (-(1 / 20) * max y y₀ ^ (-(1 / 20) - 1 : ℝ))

variable {y₀ : ℝ}

/-- `W' = dW/dy`. -/
theorem shocksP8W_hasDerivAt (hy₀ : 0 < y₀) (y : ℝ) :
    HasDerivAt (shocksP8W y₀) (shocksP8W' y₀ y) y := by
  have hV := shocksP8V_assumptions.1
  have hl : ∀ t, HasDerivAt (fun t => 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) *
      ((1 + 1 / 20) * t - 1 / 20 * t ^ 2 / (2 * y₀)))
      (1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * t / y₀)) t := fun t => by
    have := (((hasDerivAt_id t).const_mul (1 + 1 / 20 : ℝ)).sub
      (((hasDerivAt_pow 2 t).const_mul (1 / 20 : ℝ)).div_const (2 * y₀))).const_mul
      (1 / 60000 * y₀ ^ (-(1 / 20) : ℝ))
    refine this.congr_deriv ?_
    field_simp
    ring
  refine shocks_hasDerivAt_ite (fun h => ?_) (fun h => ?_) ?_
  · simp only [shocksP8W', h, ↓reduceIte]
    exact ((hV.V_deriv y (hy₀.trans_le h)).sub_const _).add_const _
  · rcases h.eq_or_lt with h' | h'
    · subst h'
      simp only [shocksP8W', le_refl, ↓reduceIte]
      convert hl y using 1
      simp only [shocksP8V']
      field_simp
      ring
    · simp only [shocksP8W', not_le.2 h', ↓reduceIte]
      exact hl y
  · ring

/-- `W'' = dW'/dy`. -/
theorem shocksP8W'_hasDerivAt (hy₀ : 0 < y₀) (y : ℝ) :
    HasDerivAt (shocksP8W' y₀) (shocksP8W'' y₀ y) y := by
  have hV := shocksP8V_assumptions.1
  have e : y₀ ^ (-(1 / 20) - 1 : ℝ) = y₀ ^ (-(1 / 20) : ℝ) / y₀ := Real.rpow_sub_one hy₀.ne' _
  refine shocks_hasDerivAt_ite (fun h => ?_) (fun h => ?_) ?_
  · rw [shocksP8W'', max_eq_left h]
    exact hV.V'_deriv y (hy₀.trans_le h)
  · rw [shocksP8W'', max_eq_right h, e]
    have := ((((hasDerivAt_id y).const_mul (1 / 20 : ℝ)).div_const y₀).const_sub
      (1 + 1 / 20 : ℝ)).const_mul (1 / 60000 * y₀ ^ (-(1 / 20) : ℝ))
    refine this.congr_deriv ?_
    field_simp
  · simp only [shocksP8V']
    field_simp
    ring

/-- `W' > 0`. -/
theorem shocksP8W'_pos (hy₀ : 0 < y₀) (y : ℝ) : 0 < shocksP8W' y₀ y := by
  simp only [shocksP8W']
  split_ifs with h
  · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (hy₀.trans_le h) _)
  · have h1 : y / y₀ < 1 := (div_lt_one hy₀).2 (not_le.1 h)
    have h2 : 1 / 20 * y / y₀ = 1 / 20 * (y / y₀) := by ring
    refine mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hy₀ _)) ?_
    rw [h2]
    linarith

/-- `W'' < 0`. -/
theorem shocksP8W''_neg (hy₀ : 0 < y₀) (y : ℝ) : shocksP8W'' y₀ y < 0 := by
  have := Real.rpow_pos_of_pos (hy₀.trans_le (le_max_right y y₀)) (-(1 / 20) - 1 : ℝ)
  simp only [shocksP8W'']
  nlinarith

/-- **`W` satisfies the book's Assumption 17.1** (`V` twice continuously differentiable on
`ℝ₊ = [0, ∞)`, `V'(0) < ∞`, strictly increasing and strictly concave) **and Assumption 17.4**
(relative risk aversion `≤ 1` on `ℝ₊`). -/
theorem shocksP8W_assumptions (hy₀ : 0 < y₀) :
    Assumption17_1V (shocksP8W y₀) (shocksP8W' y₀) (shocksP8W'' y₀) ∧
      MonoAssumption17_4 (shocksP8W' y₀) (shocksP8W'' y₀) := by
  have hd := shocksP8W_hasDerivAt hy₀
  have hd' := shocksP8W'_hasDerivAt hy₀
  have hc : Continuous (shocksP8W y₀) := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hc' : Continuous (shocksP8W' y₀) :=
    continuous_iff_continuousAt.2 fun y => (hd' y).continuousAt
  have hmono : StrictMonoOn (shocksP8W y₀) (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn fun x hx => by
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact shocksP8W'_pos hy₀ x
  have hanti : StrictAnti (shocksP8W' y₀) := by
    have := strictAntiOn_of_deriv_neg convex_univ hc'.continuousOn fun x _ => by
      rw [(hd' x).deriv]
      exact shocksP8W''_neg hy₀ x
    exact fun a b hab => this (mem_univ a) (mem_univ b) hab
  have hderiv : deriv (shocksP8W y₀) = shocksP8W' y₀ := funext fun y => (hd y).deriv
  have h0 : shocksP8W y₀ 0 = 0 := by simp [shocksP8W, not_le.2 hy₀]
  refine ⟨⟨fun y hy => ?_, fun y _ => (hd y).hasDerivWithinAt,
    fun y _ => (hd' y).hasDerivWithinAt, ?_, hmono, ?_⟩, fun y hy => ?_⟩
  · rw [← h0]
    exact hmono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
  · refine Continuous.continuousOn (continuous_const.mul (continuous_const.mul ?_))
    exact (continuous_id.max continuous_const).rpow_const fun y =>
      Or.inl (hy₀.trans_le (le_max_right y y₀)).ne'
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hc.continuousOn ?_
    rw [hderiv]
    exact fun a _ b _ hab => hanti hab
  · -- relative risk aversion
    have hW := shocksP8W'_pos hy₀ y
    simp only [monoRRA]
    rw [div_le_one hW]
    simp only [shocksP8W'', shocksP8W']
    split_ifs with h
    · rw [max_eq_left h]
      have hy0 : 0 < y := hy₀.trans_le h
      have e : y * y ^ (-(1 / 20) - 1 : ℝ) = y ^ (-(1 / 20) : ℝ) := by
        rw [Real.rpow_sub_one hy0.ne', mul_div_cancel₀ _ hy0.ne']
      have hp := Real.rpow_pos_of_pos hy0 (-(1 / 20) : ℝ)
      simp only [shocksP8V']
      have : -y * (1 / 60000 * (-(1 / 20) * y ^ (-(1 / 20) - 1 : ℝ))) =
          1 / 60000 * (1 / 20) * (y * y ^ (-(1 / 20) - 1 : ℝ)) := by ring
      rw [this, e]
      nlinarith
    · have hlt : y < y₀ := not_le.1 h
      rw [max_eq_right hlt.le, Real.rpow_sub_one hy₀.ne']
      have hp := Real.rpow_pos_of_pos hy₀ (-(1 / 20) : ℝ)
      have hq : y / y₀ < 1 := (div_lt_one hy₀).2 hlt
      have hq0 : 0 ≤ y / y₀ := div_nonneg hy hy₀.le
      have e1 : -y * (1 / 60000 * (-(1 / 20) * (y₀ ^ (-(1 / 20) : ℝ) / y₀))) =
          1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 / 20 * (y / y₀)) := by
        field_simp
      have e2 : 1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * y / y₀) =
          1 / 60000 * y₀ ^ (-(1 / 20) : ℝ) * (1 + 1 / 20 - 1 / 20 * (y / y₀)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- On functions whose `η = ζ⁻¹ ∘ f` stays above `(3/2) y₀`, the operators (4) built from `W`
and from the CRRA utility coincide: all arguments of `φ` are `≥ (θ̲/θ̄)(3/2) y₀ = y₀`. -/
theorem shocksP8W_opT_eq {Z : Type*} [MeasurableSpace Z] {L : ℝ} {H' : ℝ → ℝ} (hy₀ : 0 < y₀)
    (μ : Measure (ℝ × Z)) (ν : Z → Measure ℝ) (f : Z → ℝ)
    (hη : ∀ z, 3 / 2 * y₀ ≤ olgZetaInv L H' (f z)) (z : Z) :
    shocksOpT L H' (shocksP8W' y₀) 1 (3 / 2) μ ν f z =
      shocksOpT L H' shocksP8V' 1 (3 / 2) μ ν f z := by
  have e : ∀ θt (ω : ℝ × Z), shocksIntegrand L H' (shocksP8W' y₀) 1 (3 / 2) f θt ω =
      shocksIntegrand L H' shocksP8V' 1 (3 / 2) f θt ω := fun θt ω => by
    have h1 := (shocksRatio_mem (θlo := (1 : ℝ)) (θhi := 3 / 2) one_pos (by norm_num) ω.1 θt).1
    have h2 := hη ω.2
    have hle : y₀ ≤ shocksRatio 1 (3 / 2) ω.1 θt * olgZetaInv L H' (f ω.2) := by
      nlinarith [h1, h2, hy₀]
    simp only [shocksIntegrand, olgPhi, shocksP8W', hle, ↓reduceIte]
  simp only [shocksOpT, shocksPhiF, e]

/-- **Proposition 8 under Assumption 17.5 alone: counterexample satisfying the book's
Assumption 17.1.** In the bimodal economy of `proposition_8_counterexample`, replace the CRRA
utility below a small `y₀ > 0` by `shocksP8W y₀` (so that `V'(0) < ∞`): `H` and `V` satisfy the
book's Assumption 17.1 (with `V` twice continuously differentiable on all of `ℝ₊`) and
Assumption 17.4, the strictly positive fixed point of `T` for the CRRA utility is still a fixed
point (all arguments of `φ` exceed `y₀`), and its price function `ρ(z) = z/ζ⁻¹(f(z))` is not
invertible. -/
theorem proposition_8_counterexample_book :
    ∃ y₀ : ℝ, 0 < y₀ ∧
      Assumption17_1 1 monoCexH monoCexH' monoCexH'' (shocksP8W y₀) (shocksP8W' y₀)
        (shocksP8W'' y₀) ∧ MonoAssumption17_4 (shocksP8W' y₀) (shocksP8W'' y₀) ∧
      ∃ f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ, (∀ z, 0 < f z) ∧
        (∀ z, f z = shocksOpT 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2)
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
          (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) ∧
        ¬ Function.Injective (fun z : Icc (1 / (3 / 2) : ℝ) (2 / 1) =>
          (z : ℝ) / olgZetaInv 1 monoCexH' (f z)) := by
  have hH := monoCexH_assumption17_1H'
  obtain ⟨f, ⟨hfpos, hfix⟩, -⟩ := shocksP8_existsUnique_fixedPoint
  have hne : (univ : Set (Icc (1 / (3 / 2) : ℝ) (2 / 1))).Nonempty :=
    ⟨⟨_, left_mem_Icc.2 shocksP8_hZ⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne f.continuous.continuousOn
  have hy₀ : 0 < 2 / 3 * olgZetaInv 1 monoCexH' (f m) :=
    mul_pos (by norm_num) (hH.zetaInv_pos (hfpos m))
  have hη : ∀ z, 3 / 2 * (2 / 3 * olgZetaInv 1 monoCexH' (f m)) ≤
      olgZetaInv 1 monoCexH' (f z) := fun z => by
    rw [← mul_assoc, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, one_mul]
    exact hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hfpos m).le) (mem_Ici.2 (hfpos z).le)
      (isMinOn_iff.1 hm z (mem_univ z))
  exact ⟨_, hy₀, ⟨hH, (shocksP8W_assumptions hy₀).1⟩, (shocksP8W_assumptions hy₀).2, f, hfpos,
    fun z => by rw [shocksP8W_opT_eq hy₀ _ _ f hη z]; exact hfix z,
    (shocksP8_not_injective f hfpos hfix).1⟩

/-- **Correction (Proposition 8, p. 540, is false as stated).** Under the book's hypotheses
(Assumptions 17.1 and 17.4 for `H`, `V`; Assumption 17.5 for the shocks), a strictly positive
continuous solution of (3) (a fixed point of (4)) can have a price function `ρ(z) = z/η(z)` that is
not strictly increasing: `proposition_8_counterexample_book`. -/
theorem proposition_8_false :
    ¬ ∀ (xlo xhi θlo θhi : ℝ) (hZ : xlo / θhi ≤ xhi / θlo) (ψ g : ℝ → ℝ) (L : ℝ)
      (H H' H'' V V' V'' : ℝ → ℝ), ShocksAssumption17_5 xlo xhi θlo θhi ψ g →
      Assumption17_1 L H H' H'' V V' V'' → MonoAssumption17_4 V' V'' →
      ∀ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) →
      (∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z) →
      StrictMono fun z : Icc (xlo / θhi) (xhi / θlo) => (z : ℝ) / olgZetaInv L H' (f z) := by
  intro h
  obtain ⟨y₀, -, h1, h4, f, hfpos, hfix, hinj⟩ := proposition_8_counterexample_book
  exact hinj (h 1 2 1 (3 / 2) shocksP8_hZ _ _ 1 _ _ _ _ _ _ shocksExBimodal_assumption h1 h4 f
    hfpos hfix).injective

end StokeyLucasPrescott.FixedPointArguments
