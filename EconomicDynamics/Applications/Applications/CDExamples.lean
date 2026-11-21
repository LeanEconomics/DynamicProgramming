/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CDEuler
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Examples 8.3.1 and 8.3.2 (Ljungqvist and Sargent)

Miao, §8.3.1, pp. 248–249: `βR = 1`, `a₀ = 0`, `b = 0`, income alternating between
`y_h > y_l > 0`.

* `example_8_3_1_pv`: the present value of `{y_h, y_l, y_h, …}` is `(y_h + y_l/R)/(1 − R^{−2})`;
  `example_8_3_1_annuity`: the annuity value `c̄` with `Rc̄/r` equal to it is
  `c̄ = (y_h + y_l/R)/(1 + 1/R)`.
* `example_8_3_1_savings`: consuming `c̄` gives `a_{t+1} = (y_h − y_l)/(1 + R)` for even `t` and
  `0` for odd `t`. The book prints `a_{t+1} = (y_h − y_l)R/(1 + R)` for even `t`, which violates
  the budget constraint (`example_8_3_1_savings_misprint`).
* `example_8_3_1`: the plan is optimal (Euler equation and transversality condition); the Euler
  equation holds with equality at every date although `a_{t+1} = 0` at odd `t` (footnote 1: zero
  assets need not mean a binding constraint).
* `example_8_3_2`: for `{y_l, y_h, y_l, …}` the solution is `c_0 = y_l`, `a_1 = 0`, then `c̄`;
  the Euler inequality is strict only at `t = 0` (constrained in the first period only).
-/

namespace Miao.Applications

open Filter Topology

/-- Miao, Example 8.3.1, p. 248: the annuity value `c̄ = (y_h + y_l/R)/(1 + 1/R)`. -/
noncomputable def cd_cbar (R yh yl : ℝ) : ℝ := (yh + yl / R) / (1 + 1 / R)

theorem cd_cbar_eq {R yh yl : ℝ} (hR : 0 < R) : cd_cbar R yh yl = (R * yh + yl) / (R + 1) := by
  unfold cd_cbar
  field_simp

theorem cd_cbar_bounds {R yh yl : ℝ} (hR : 0 < R) (hl : yl < yh) :
    yl < cd_cbar R yh yl ∧ cd_cbar R yh yl < yh := by
  rw [cd_cbar_eq hR]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- Example 8.3.1's income stream `{y_h, y_l, y_h, y_l, …}`. -/
noncomputable def cd_y1 (yh yl : ℝ) (t : ℕ) : ℝ := if Even t then yh else yl

/-- Miao, Example 8.3.1, p. 248: `∑ y_t/(1 + r)ᵗ = (y_h + y_l/R)/(1 − R^{−2})`. -/
theorem example_8_3_1_pv {R yh yl : ℝ} (hR : 1 < R) :
    HasSum (fun t => cd_y1 yh yl t / R ^ t) ((yh + yl / R) / (1 - (R ^ 2)⁻¹)) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hq0 : 0 ≤ (R ^ 2)⁻¹ := by positivity
  have hR2 : 1 < R ^ 2 := one_lt_pow₀ hR (by norm_num)
  have hq1 : (R ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR2
  have hg := hasSum_geometric_of_lt_one hq0 hq1
  have he : HasSum (fun k => cd_y1 yh yl (2 * k) / R ^ (2 * k)) (yh * (1 - (R ^ 2)⁻¹)⁻¹) := by
    refine (hg.mul_left yh).congr_fun fun k => ?_
    have e1 : cd_y1 yh yl (2 * k) = yh := by simp only [cd_y1, even_two_mul k, ↓reduceIte]
    rw [e1, pow_mul, div_eq_mul_inv, inv_pow]
  have ho : HasSum (fun k => cd_y1 yh yl (2 * k + 1) / R ^ (2 * k + 1))
      (yl / R * (1 - (R ^ 2)⁻¹)⁻¹) := by
    refine (hg.mul_left (yl / R)).congr_fun fun k => ?_
    have e1 : cd_y1 yh yl (2 * k + 1) = yl := by
      simp only [cd_y1, Nat.not_even_iff_odd.2 (odd_two_mul_add_one k), ↓reduceIte]
    rw [e1, pow_succ, pow_mul, inv_pow]
    field_simp
  have hsum := HasSum.even_add_odd (f := fun t => cd_y1 yh yl t / R ^ t) he ho
  have e : yh * (1 - (R ^ 2)⁻¹)⁻¹ + yl / R * (1 - (R ^ 2)⁻¹)⁻¹ =
      (yh + yl / R) / (1 - (R ^ 2)⁻¹) := by ring
  rwa [e] at hsum

/-- Miao, Example 8.3.1, p. 248: `Rc̄/r = (y_h + y_l/R)/(1 − R^{−2})`. -/
theorem example_8_3_1_annuity {R yh yl : ℝ} (hR : 1 < R) :
    R * cd_cbar R yh yl / (R - 1) = (yh + yl / R) / (1 - (R ^ 2)⁻¹) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have h1 : R - 1 ≠ 0 := by linarith
  have h2 : 1 - (R ^ 2)⁻¹ ≠ 0 := (sub_pos.2 (inv_lt_one_of_one_lt₀ (by nlinarith))).ne'
  have h3 : R ^ 2 - 1 ≠ 0 := by nlinarith
  rw [cd_cbar_eq hR0, inv_eq_one_div]
  field_simp
  ring

/-- Example 8.3.1's asset path: `a_t = 0` for even `t`, `(y_h − y_l)/(1 + R)` for odd `t`. -/
noncomputable def cd_a1 (R yh yl : ℝ) (t : ℕ) : ℝ := if Even t then 0 else (yh - yl) / (1 + R)

/-- Miao, Example 8.3.1, p. 248, corrected: consuming `c̄` each period with `a₀ = 0` gives
`a_{t+1} = (y_h − y_l)/(1 + R)` for even `t` and `a_{t+1} = 0` for odd `t`. -/
theorem example_8_3_1_savings {R yh yl : ℝ} (hR : 0 < R) :
    cd_Budget R (cd_y1 yh yl) (fun _ => cd_cbar R yh yl) (cd_a1 R yh yl) ∧
      cd_a1 R yh yl 0 = 0 := by
  refine ⟨fun t => ?_, by simp [cd_a1]⟩
  rw [cd_cbar_eq hR]
  have h1 : R + 1 ≠ 0 := by linarith
  have h2 : 1 + R ≠ 0 := by linarith
  rcases Nat.even_or_odd t with ht | ht
  · simp only [cd_a1, cd_y1, ht, Nat.even_add_one, not_true_eq_false, ↓reduceIte]
    field_simp
    ring
  · have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
    simp only [cd_a1, cd_y1, ht', Nat.even_add_one, not_false_eq_true, ↓reduceIte]
    field_simp
    ring

/-- Miao, Example 8.3.1, p. 248: the printed saving `a_1 = (y_h − y_l)R/(1 + R)` violates the
budget constraint `c̄ + a_1 = Ra_0 + y_0 = y_h` (for `R ≠ 1`, `y_h ≠ y_l`). -/
theorem example_8_3_1_savings_misprint {R yh yl : ℝ} (hR : 0 < R) (hR1 : R ≠ 1)
    (hl : yl ≠ yh) : cd_cbar R yh yl + (yh - yl) * R / (1 + R) ≠ R * 0 + yh := by
  rw [cd_cbar_eq hR]
  intro h
  have h1 : R + 1 ≠ 0 := by linarith
  have h2 : 1 + R ≠ 0 := by linarith
  field_simp at h
  have : (R - 1) * ((R + 1) * (yh - yl)) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact hR1 (by linarith)
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h1 h4
    · exact hl (by linarith)

/-- Example 8.3.1's cash on hand `x_t = Ra_t + y_t`: `y_h` at even `t`, `c̄` at odd `t`. -/
noncomputable def cd_x1 (R yh yl : ℝ) (t : ℕ) : ℝ := if Even t then yh else cd_cbar R yh yl

/-- Miao, **Example 8.3.1**, p. 248: with `βR = 1`, consuming `c̄` each period is optimal (it
satisfies the Euler equation and the transversality condition); the cash on hand is
`x_t = Ra_t + y_t`. The Euler equation holds with equality at every date, although
`a_{t+1} = x_t − c̄ = 0` at odd `t` (footnote 1). -/
theorem example_8_3_1 (U : cd_Utility) {β R yh yl : ℝ} (hβ : 0 < β) (hR : 1 < R)
    (hβR : β * R = 1) (hl0 : 0 < yl) (hl : yl < yh) :
    cd_Optimal U β R 0 (cd_y1 yh yl) yh (fun _ => cd_cbar R yh yl) (cd_x1 R yh yl) ∧
      (∀ t, cd_x1 R yh yl t = R * cd_a1 R yh yl t + cd_y1 yh yl t) ∧
      U.du (cd_cbar R yh yl) = β * R * U.du (cd_cbar R yh yl) ∧
      ∀ t, ¬ Even t → cd_x1 R yh yl t - cd_cbar R yh yl = 0 := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hb := cd_cbar_bounds hR0 hl
  have hβ1 : β < 1 := by nlinarith
  have hx : ∀ t, cd_x1 R yh yl t = R * cd_a1 R yh yl t + cd_y1 yh yl t := fun t => by
    rcases Nat.even_or_odd t with ht | ht
    · simp [cd_x1, cd_a1, cd_y1, ht]
    · have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
      simp only [cd_x1, cd_a1, cd_y1, ht', ↓reduceIte]
      rw [cd_cbar_eq hR0]
      have h1 : R + 1 ≠ 0 := by linarith
      have h2 : 1 + R ≠ 0 := by linarith
      field_simp
      ring
  have hfe : cd_Feasible R 0 (cd_y1 yh yl) yh (fun _ => cd_cbar R yh yl) (cd_x1 R yh yl) := by
    refine ⟨⟨by simp [cd_x1], fun t => ?_⟩, fun t => ⟨by linarith, ?_⟩⟩
    · rcases Nat.even_or_odd t with ht | ht
      · simp only [cd_x1, cd_y1, ht, Nat.even_add_one, not_true_eq_false, ↓reduceIte]
        rw [cd_cbar_eq hR0]
        have h1 : R + 1 ≠ 0 := by linarith
        field_simp
        ring
      · have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
        simp only [cd_x1, cd_y1, ht', Nat.even_add_one, not_false_eq_true, ↓reduceIte]
        ring
    · simp only [cd_x1]; split_ifs <;> linarith
  have hE : cd_Euler U β R (fun _ => cd_cbar R yh yl) (cd_x1 R yh yl) :=
    fun t => ⟨by rw [hβR, one_mul], fun _ => by rw [hβR, one_mul]⟩
  have hT : cd_TVCs U β (fun _ => cd_cbar R yh yl) (cd_x1 R yh yl) := by
    have hK := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
      (U.du (cd_cbar R yh yl) * (yh - cd_cbar R yh yl))
    rw [zero_mul] at hK
    have hdu := U.du_pos _ (lt_trans hl0 hb.1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK (fun t => ?_)
      (fun t => ?_)
    · refine mul_nonneg (mul_nonneg (pow_nonneg hβ.le t) hdu.le) ?_
      simp only [cd_x1]; split_ifs <;> linarith
    · have h1 : cd_x1 R yh yl t - cd_cbar R yh yl ≤ yh - cd_cbar R yh yl := by
        simp only [cd_x1]; split_ifs <;> linarith
      have h2 : 0 ≤ β ^ t * U.du (cd_cbar R yh yl) := mul_nonneg (pow_nonneg hβ.le t) hdu.le
      calc β ^ t * U.du (cd_cbar R yh yl) * (cd_x1 R yh yl t - cd_cbar R yh yl)
          ≤ β ^ t * U.du (cd_cbar R yh yl) * (yh - cd_cbar R yh yl) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = β ^ t * (U.du (cd_cbar R yh yl) * (yh - cd_cbar R yh yl)) := by ring
  refine ⟨cd_sufficient U hβ.le hfe hE hT, hx, by rw [hβR, one_mul], fun t ht => ?_⟩
  simp [cd_x1, ht]

/-- Example 8.3.2's income stream `{y_l, y_h, y_l, y_h, …}`. -/
noncomputable def cd_y2 (yh yl : ℝ) (t : ℕ) : ℝ := if Even t then yl else yh

/-- Example 8.3.2's consumption: `c_0 = y_l`, then `c̄`. -/
noncomputable def cd_c2 (R yh yl : ℝ) (t : ℕ) : ℝ := if t = 0 then yl else cd_cbar R yh yl

/-- Example 8.3.2's cash on hand: `y_l` at `0`, then `y_h` at odd and `c̄` at even dates. -/
noncomputable def cd_x2 (R yh yl : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then yl else if Even t then cd_cbar R yh yl else yh

/-- Miao, **Example 8.3.2**, p. 249: with income `{y_l, y_h, y_l, …}`, `a₀ = b = 0`, `βR = 1`,
the solution is `c_0 = y_l`, `a_1 = 0` and then the plan of Example 8.3.1: it is optimal, and
the consumer is borrowing constrained in the first period only (the Euler inequality is strict
at `t = 0` and an equality at every `t ≥ 1`). -/
theorem example_8_3_2 (U : cd_Utility) {β R yh yl : ℝ} (hβ : 0 < β) (hR : 1 < R)
    (hβR : β * R = 1) (hl0 : 0 < yl) (hl : yl < yh) :
    cd_Optimal U β R 0 (cd_y2 yh yl) yl (cd_c2 R yh yl) (cd_x2 R yh yl) ∧
      cd_x2 R yh yl 0 - cd_c2 R yh yl 0 = 0 ∧
      β * R * U.du (cd_c2 R yh yl 1) < U.du (cd_c2 R yh yl 0) ∧
      ∀ t, 1 ≤ t → U.du (cd_c2 R yh yl t) = β * R * U.du (cd_c2 R yh yl (t + 1)) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hb := cd_cbar_bounds hR0 hl
  have hβ1 : β < 1 := by nlinarith
  have hlt : U.du (cd_cbar R yh yl) < U.du yl :=
    U.du_anti (Set.mem_Ioi.2 hl0) (Set.mem_Ioi.2 (lt_trans hl0 hb.1)) hb.1
  have hfe : cd_Feasible R 0 (cd_y2 yh yl) yl (cd_c2 R yh yl) (cd_x2 R yh yl) := by
    refine ⟨⟨by simp [cd_x2], fun t => ?_⟩, fun t => ⟨?_, ?_⟩⟩
    · cases t with
      | zero => simp [cd_x2, cd_c2, cd_y2]
      | succ t =>
        rcases Nat.even_or_odd (t + 1) with ht | ht
        · have ht2 : ¬ Even (t + 1 + 1) := by rw [Nat.even_add_one]; simpa using ht
          simp only [cd_x2, cd_c2, cd_y2, Nat.succ_ne_zero, ↓reduceIte, ht, ht2]
          ring
        · have ht' : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 ht
          have ht2 : Even (t + 1 + 1) := by rw [Nat.even_add_one]; exact ht'
          simp only [cd_x2, cd_c2, cd_y2, Nat.succ_ne_zero, ↓reduceIte, ht', ht2]
          rw [cd_cbar_eq hR0]
          have h1 : R + 1 ≠ 0 := by linarith
          field_simp
          ring
    · simp only [cd_c2]; split_ifs <;> linarith
    · simp only [cd_c2, cd_x2]; split_ifs <;> linarith
  have hE : cd_Euler U β R (cd_c2 R yh yl) (cd_x2 R yh yl) := by
    intro t
    cases t with
    | zero =>
      refine ⟨?_, fun h => ?_⟩
      · simp only [cd_c2, ↓reduceIte, hβR, one_mul]; exact hlt.le
      · simp [cd_c2, cd_x2] at h
    | succ t =>
      constructor <;> intros <;> simp [cd_c2, hβR]
  have hT : cd_TVCs U β (cd_c2 R yh yl) (cd_x2 R yh yl) := by
    have hK := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
      (U.du yl * (yh - cd_cbar R yh yl))
    rw [zero_mul] at hK
    have hs : ∀ t, 0 ≤ cd_x2 R yh yl t - cd_c2 R yh yl t ∧
        cd_x2 R yh yl t - cd_c2 R yh yl t ≤ yh - cd_cbar R yh yl := fun t => by
      simp only [cd_x2, cd_c2]; split_ifs <;> constructor <;> linarith
    have hd : ∀ t, 0 < U.du (cd_c2 R yh yl t) ∧ U.du (cd_c2 R yh yl t) ≤ U.du yl := fun t => by
      simp only [cd_c2]
      split_ifs
      · exact ⟨U.du_pos _ hl0, le_rfl⟩
      · exact ⟨U.du_pos _ (lt_trans hl0 hb.1), hlt.le⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK (fun t => ?_)
      (fun t => ?_)
    · exact mul_nonneg (mul_nonneg (pow_nonneg hβ.le t) (hd t).1.le) (hs t).1
    · have h1 := mul_le_mul (hd t).2 (hs t).2 (hs t).1 (U.du_pos _ hl0).le
      have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ.le t)
      calc β ^ t * U.du (cd_c2 R yh yl t) * (cd_x2 R yh yl t - cd_c2 R yh yl t)
          = β ^ t * (U.du (cd_c2 R yh yl t) * (cd_x2 R yh yl t - cd_c2 R yh yl t)) := by ring
        _ ≤ β ^ t * (U.du yl * (yh - cd_cbar R yh yl)) := h2
  refine ⟨cd_sufficient U hβ.le hfe hE hT, by simp [cd_x2, cd_c2], ?_, fun t ht => ?_⟩
  · simp only [cd_c2, ↓reduceIte, hβR, one_mul]
    exact hlt
  · simp only [cd_c2, show t ≠ 0 by omega, Nat.succ_ne_zero, ↓reduceIte, hβR, one_mul]

end Miao.Applications
