/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.CRRA
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Infinite horizon: boundedness, Ponzi schemes and the budget constraint

AKMM, §4.3.1, pp. 106–109.

* Unbounded utility: a constant stream has finite utility iff `β < 1`
  (`infinite_constant_summable_iff`); a stream growing at rate `γ` with CRRA utility has finite
  utility iff `β(1 + γ)^{1−σ} < 1` (`infinite_growth_summable_iff`), which holds for every
  `γ > 0` when `σ > 1` (`infinite_growth_sigma_gt_one`), is an upper bound on `γ` when `σ < 1`
  (`infinite_growth_sigma_lt_one`), and fails for fast enough negative growth when `σ > 1`
  (`infinite_growth_negative_fails`).
* The Ponzi scheme: with only the flow budget constraint every plan can be strictly improved
  (`ponzi_improvement`), so no plan is optimal (`ponzi_no_maximum`); the improvement lowers the
  discounted terminal assets by `ε`, so it violates the no-Ponzi-game condition (4.12) whenever
  the original plan satisfies the transversality condition.
* The consolidated budget: `eq_4_13_finite`, (4.13) under (4.12) (`eq_4_13`) and (4.14) when the
  TVC (4.15) holds too (`eq_4_14`).
* Example 4.3: `c_t = [β(1 + r)]ᵗc₀` and `c₀ = (1 − β)(1 + r)a₀` (`example_4_3_path`,
  `example_4_3_c0`), and this plan is optimal (`example_4_3`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real

/-- AKMM, p. 106: a constant stream `c̄` with `u(c̄) ≠ 0` has finite lifetime utility
`Σ βᵗu(c̄)` iff `β < 1` (for `β ≥ 0`). -/
theorem infinite_constant_summable_iff {β v : ℝ} (hβ : 0 ≤ β) (hv : v ≠ 0) :
    (Summable fun t : ℕ => β ^ t * v) ↔ β < 1 := by
  rw [summable_mul_right_iff hv, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_nonneg hβ]

/-- CRRA utility along a growing stream: `β^t u(c₀(1 + γ)^t)` in geometric form. -/
theorem infinite_growth_term {σ β c0 g : ℝ} (hc0 : 0 < c0) (hg : 0 < g) (t : ℕ) :
    β ^ t * crra σ (c0 * g ^ t) =
      (c0 ^ (1 - σ) * (β * g ^ (1 - σ)) ^ t - β ^ t) / (1 - σ) := by
  unfold crra
  have e : (g ^ t) ^ (1 - σ) = (g ^ (1 - σ)) ^ t := by
    rw [← rpow_natCast, ← rpow_mul hg.le, mul_comm, rpow_mul hg.le, rpow_natCast]
  rw [mul_rpow hc0.le (pow_nonneg hg.le t), e, mul_pow]
  ring

/-- **AKMM, p. 107: boundedness of CRRA utility along a growing path.** With `σ ≠ 1`, `c₀ > 0`,
`1 + γ > 0` and `0 < β < 1`, `Σ βᵗu(c₀(1 + γ)ᵗ)` is finite iff `β(1 + γ)^{1−σ} < 1`. -/
theorem infinite_growth_summable_iff {σ β c0 γ : ℝ} (hσ : σ ≠ 1) (hc0 : 0 < c0)
    (hγ : 0 < 1 + γ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (Summable fun t : ℕ => β ^ t * crra σ (c0 * (1 + γ) ^ t)) ↔ β * (1 + γ) ^ (1 - σ) < 1 := by
  have h1σ : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  simp_rw [infinite_growth_term (σ := σ) (β := β) hc0 hγ]
  have hgeo : Summable fun t : ℕ => β ^ t := summable_geometric_of_lt_one hβ0.le hβ1
  have hq : 0 < β * (1 + γ) ^ (1 - σ) := mul_pos hβ0 (rpow_pos_of_pos hγ _)
  have hc : c0 ^ (1 - σ) ≠ 0 := (rpow_pos_of_pos hc0 _).ne'
  constructor
  · intro hs
    have h2 : Summable fun t : ℕ => c0 ^ (1 - σ) * (β * (1 + γ) ^ (1 - σ)) ^ t := by
      have := (hs.mul_right (1 - σ)).add hgeo
      refine this.congr fun t => ?_
      field_simp
      ring
    rw [summable_mul_left_iff hc, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
      abs_of_pos hq] at h2
    exact h2
  · intro h
    have h2 : Summable fun t : ℕ => (β * (1 + γ) ^ (1 - σ)) ^ t :=
      summable_geometric_of_lt_one hq.le h
    exact ((h2.mul_left (c0 ^ (1 - σ))).sub hgeo).div_const _

/-- AKMM, p. 107: if `σ > 1` and `0 < β < 1`, positive growth `γ > 0` meets the boundedness
condition. -/
theorem infinite_growth_sigma_gt_one {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) : β * (1 + γ) ^ (1 - σ) < 1 := by
  have : (1 + γ) ^ (1 - σ) < 1 := rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  nlinarith [rpow_pos_of_pos (show (0 : ℝ) < 1 + γ by linarith) (1 - σ)]

/-- AKMM, p. 107: if `σ < 1` the boundedness condition is an upper bound on the growth factor,
`1 + γ < β^{−1/(1−σ)}`. -/
theorem infinite_growth_sigma_lt_one {σ β γ : ℝ} (hσ : σ < 1) (hβ0 : 0 < β) (hγ : 0 < 1 + γ) :
    β * (1 + γ) ^ (1 - σ) < 1 ↔ 1 + γ < β ^ (-(1 / (1 - σ))) := by
  have hp : 0 < 1 - σ := by linarith
  have hb : 0 < β ^ (-(1 / (1 - σ))) := rpow_pos_of_pos hβ0 _
  have key : (β ^ (-(1 / (1 - σ)))) ^ (1 - σ) = β⁻¹ := by
    rw [← rpow_mul hβ0.le, show -(1 / (1 - σ)) * (1 - σ) = -1 by field_simp, rpow_neg_one]
  rw [← rpow_lt_rpow_iff hγ.le hb.le hp, key]
  have hx := rpow_pos_of_pos hγ (1 - σ)
  constructor <;> intro h
  · calc (1 + γ) ^ (1 - σ) = β⁻¹ * (β * (1 + γ) ^ (1 - σ)) := by field_simp
      _ < β⁻¹ * 1 := mul_lt_mul_of_pos_left h (inv_pos.2 hβ0)
      _ = β⁻¹ := mul_one _
  · calc β * (1 + γ) ^ (1 - σ) < β * β⁻¹ := mul_lt_mul_of_pos_left h hβ0
      _ = 1 := mul_inv_cancel₀ hβ0.ne'

/-- AKMM, p. 107: if `σ > 1`, negative growth at a high enough rate violates the boundedness
condition: `γ = β^{1/(σ−1)} − 1 ∈ (−1, 0)` gives `β(1 + γ)^{1−σ} = 1`. -/
theorem infinite_growth_negative_fails {σ β : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ γ, -1 < γ ∧ γ < 0 ∧ 1 ≤ β * (1 + γ) ^ (1 - σ) := by
  have hp : 0 < 1 / (σ - 1) := by apply div_pos one_pos; linarith
  refine ⟨β ^ (1 / (σ - 1)) - 1, by linarith [rpow_pos_of_pos hβ0 (1 / (σ - 1))],
    by linarith [rpow_lt_one hβ0.le hβ1 hp], ?_⟩
  rw [show 1 + (β ^ (1 / (σ - 1)) - 1) = β ^ (1 / (σ - 1)) by ring, ← rpow_mul hβ0.le,
    show 1 / (σ - 1) * (1 - σ) = -1 by field_simp [show σ - 1 ≠ 0 by linarith]; ring,
    rpow_neg_one, mul_inv_cancel₀ hβ0.ne']

/-- AKMM, p. 107: the Ponzi perturbation of an asset path: `ã₀ = a₀` and
`ã_{t+1} = a_{t+1} − ε(1 + r)ᵗ`. -/
noncomputable def ponziAssets (a : ℕ → ℝ) (r ε : ℝ) : ℕ → ℝ
  | 0 => a 0
  | s + 1 => a (s + 1) - ε * (1 + r) ^ s

/-- **AKMM, p. 107: the Ponzi scheme.** Given any plan satisfying `c_t + a_{t+1} = (1 + r)a_t`,
consuming `ε > 0` more at `t = 0` and rolling the debt over, `ã_{t+1} = a_{t+1} − ε(1 + r)ᵗ`,
satisfies the budget constraint, raises every partial sum of utility, and lowers the discounted
terminal assets `a_{t+1}/(1 + r)ᵗ` by `ε`. -/
theorem ponzi_improvement {u : ℝ → ℝ} (hu : StrictMono u) {β r ε : ℝ} (hr : -1 < r)
    (hε : 0 < ε) {c a : ℕ → ℝ} (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) :
    (∀ t, Function.update c 0 (c 0 + ε) t + ponziAssets a r ε (t + 1) =
      (1 + r) * ponziAssets a r ε t) ∧
    (∀ T, ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) <
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (Function.update c 0 (c 0 + ε) t)) ∧
    ∀ t, ponziAssets a r ε (t + 1) / (1 + r) ^ t = a (t + 1) / (1 + r) ^ t - ε := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  refine ⟨fun t => ?_, fun T => ?_, fun t => ?_⟩
  · rcases t with _ | s
    · simp only [Function.update_self, ponziAssets, pow_zero, mul_one]
      linarith [hbudget 0]
    · rw [Function.update_of_ne (by omega)]
      simp only [ponziAssets]
      have := hbudget (s + 1)
      rw [pow_succ]
      linarith
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ∑ t ∈ Finset.range T, β ^ (t + 1) * u (Function.update c 0 (c 0 + ε) (t + 1)) =
        ∑ t ∈ Finset.range T, β ^ (t + 1) * u (c (t + 1)) :=
      Finset.sum_congr rfl fun t _ => by rw [Function.update_of_ne (by omega)]
    rw [hrest, Function.update_self, pow_zero, one_mul, one_mul]
    have := hu (show c 0 < c 0 + ε by linarith)
    linarith
  · simp only [ponziAssets]
    have : (1 + r) ^ t ≠ 0 := (pow_pos hr' t).ne'
    field_simp

/-- **AKMM, pp. 107–108: without a no-Ponzi condition there is no maximum.** If `u` is strictly
increasing, `β ≥ 0` and `r > −1`, no plan satisfying only the flow budget constraint, with finite
utility, is at least as good as every other such plan. -/
theorem ponzi_no_maximum {u : ℝ → ℝ} (hu : StrictMono u) {β r a0 : ℝ} (hr : -1 < r) :
    ¬ ∃ c a : ℕ → ℝ, a 0 = a0 ∧ (∀ t, c t + a (t + 1) = (1 + r) * a t) ∧
      (Summable fun t => β ^ t * u (c t)) ∧
      ∀ c' a' : ℕ → ℝ, a' 0 = a0 → (∀ t, c' t + a' (t + 1) = (1 + r) * a' t) →
        (Summable fun t => β ^ t * u (c' t)) →
        ∑' t, β ^ t * u (c' t) ≤ ∑' t, β ^ t * u (c t) := by
  rintro ⟨c, a, ha0, hbud, hsum, hmax⟩
  obtain ⟨hbud', -, -⟩ := ponzi_improvement (β := β) hu hr one_pos hbud
  set c' := Function.update c 0 (c 0 + 1)
  have hsucc : ∀ t, β ^ (t + 1) * u (c' (t + 1)) = β ^ (t + 1) * u (c (t + 1)) := fun t => by
    change β ^ (t + 1) * u (Function.update c 0 (c 0 + 1) (t + 1)) = _
    rw [Function.update_of_ne (by omega)]
  have hsum' : Summable fun t => β ^ t * u (c' t) := by
    rw [← summable_nat_add_iff 1]
    simp only [hsucc]
    exact (summable_nat_add_iff 1).2 hsum
  have h := hmax c' (ponziAssets a r 1) (by simp [ponziAssets, ha0]) hbud' hsum'
  rw [hsum'.tsum_eq_zero_add, hsum.tsum_eq_zero_add] at h
  simp only [hsucc, c', Function.update_self, pow_zero, one_mul] at h
  have := hu (show c 0 < c 0 + 1 by linarith)
  linarith

/-- AKMM, p. 108: consolidating `T + 1` flow budget constraints `c_t + a_{t+1} = (1 + r)a_t`
gives `Σ_{t≤T} c_t/(1 + r)ᵗ = a₀(1 + r) − a_{T+1}/(1 + r)ᵀ`. -/
theorem eq_4_13_finite {r : ℝ} (hr : -1 < r) {c a : ℕ → ℝ}
    (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t = a 0 * (1 + r) - a (T + 1) / (1 + r) ^ T := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  induction T with
  | zero => simp only [zero_add, Finset.sum_range_one, pow_zero, div_one]; linarith [hbudget 0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have := hbudget (T + 1)
    have h1 : (1 + r) ^ T ≠ 0 := (pow_pos hr' T).ne'
    have h2 : (1 + r) ^ (T + 1) ≠ 0 := (pow_pos hr' (T + 1)).ne'
    rw [eq_sub_of_add_eq this]
    field_simp
    ring

/-- **AKMM, (4.13), p. 108.** If consumption is nonnegative and the no-Ponzi-game condition
(4.12) holds, `a_{T+1}/(1 + r)ᵀ → L ≥ 0`, then `Σ c_t/(1 + r)ᵗ = a₀(1 + r) − L ≤ a₀(1 + r)`. -/
theorem eq_4_13 {r : ℝ} (hr : -1 < r) {c a : ℕ → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) {L : ℝ}
    (hlim : Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 L)) (hL : 0 ≤ L) :
    HasSum (fun t => c t / (1 + r) ^ t) (a 0 * (1 + r) - L) ∧
      a 0 * (1 + r) - L ≤ a 0 * (1 + r) := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  refine ⟨(hasSum_iff_tendsto_nat_of_nonneg (fun t => div_nonneg (hc t)
    (pow_pos hr' t).le) _).2 ?_, by linarith⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [eq_4_13_finite hr hbudget]
  exact tendsto_const_nhds.sub hlim

/-- **AKMM, (4.14)–(4.15), p. 109.** With the transversality condition (4.15) `L ≤ 0` as well,
the lifetime budget constraint holds with equality: `Σ c_t/(1 + r)ᵗ = a₀(1 + r)`. -/
theorem eq_4_14 {r : ℝ} (hr : -1 < r) {c a : ℕ → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hbudget : ∀ t, c t + a (t + 1) = (1 + r) * a t) {L : ℝ}
    (hlim : Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 L)) (hnpg : 0 ≤ L)
    (htvc : L ≤ 0) : HasSum (fun t => c t / (1 + r) ^ t) (a 0 * (1 + r)) := by
  have := (eq_4_13 hr hc hbudget hlim hnpg).1
  rwa [le_antisymm htvc hnpg, sub_zero] at this

/-- AKMM, Example 4.3, p. 109: the first-order conditions `βᵗ/c_t = λ(1/(1 + r))ᵗ` give
`c_t = [β(1 + r)]ᵗc₀`. -/
theorem example_4_3_path {β r lam : ℝ} (hr : -1 < r) {c : ℕ → ℝ} (hc : ∀ t, c t ≠ 0)
    (hfoc : ∀ t, β ^ t * (1 / c t) = lam * (1 / (1 + r)) ^ t) (t : ℕ) :
    c t = (β * (1 + r)) ^ t * c 0 := by
  have hr' : (1 + r) ≠ 0 := by linarith
  have h0 := hfoc 0
  simp only [pow_zero, one_mul, mul_one] at h0
  have ht := hfoc t
  rw [← h0] at ht
  have hc0 := hc 0
  have hct := hc t
  have h2 : c t = β ^ t * c 0 * (1 + r) ^ t := by
    simp only [one_div, inv_pow] at ht
    field_simp at ht
    linarith
  rw [h2, mul_pow]
  ring

/-- AKMM, Example 4.3, p. 109: substituting `c_t = [β(1 + r)]ᵗc₀` into the consolidated budget
`Σ c_t/(1 + r)ᵗ = a₀(1 + r)` gives `c₀ = (1 − β)(1 + r)a₀`. -/
theorem example_4_3_c0 {β r a0 c0 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hr : -1 < r)
    (h : HasSum (fun t : ℕ => (β * (1 + r)) ^ t * c0 / (1 + r) ^ t) (a0 * (1 + r))) :
    c0 = (1 - β) * (1 + r) * a0 := by
  have hr' : (1 + r) ≠ 0 := by linarith
  have e : (fun t : ℕ => (β * (1 + r)) ^ t * c0 / (1 + r) ^ t) = fun t => c0 * β ^ t := by
    funext t; rw [mul_pow]; field_simp
  rw [e] at h
  have h2 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left c0
  have := h.unique h2
  have h1β : (1 - β) ≠ 0 := by linarith
  field_simp at this
  linarith

/-- **AKMM, Example 4.3, p. 109: the solution is optimal.** With `u = log`, `0 < β < 1`,
`r > −1` and `a₀ > 0`, the plan `c*_t = [β(1 + r)]ᵗ(1 − β)(1 + r)a₀` exhausts the lifetime budget
(4.14), and every positive plan with `Σ c_t/(1 + r)ᵗ ≤ a₀(1 + r)` and finite utility has
`Σ βᵗ log c_t ≤ Σ βᵗ log c*_t`. -/
theorem example_4_3 {β r a0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hr : -1 < r) (ha0 : 0 < a0) :
    HasSum (fun t : ℕ => (β * (1 + r)) ^ t * ((1 - β) * (1 + r) * a0) / (1 + r) ^ t)
      (a0 * (1 + r)) ∧
    ∀ c : ℕ → ℝ, (∀ t, 0 < c t) → (Summable fun t => c t / (1 + r) ^ t) →
      ∑' t, c t / (1 + r) ^ t ≤ a0 * (1 + r) → (Summable fun t => β ^ t * Real.log (c t)) →
      ∑' t, β ^ t * Real.log (c t) ≤
        ∑' t : ℕ, β ^ t * Real.log ((β * (1 + r)) ^ t * ((1 - β) * (1 + r) * a0)) := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  set K := (1 - β) * (1 + r) * a0
  have hK : 0 < K := mul_pos (mul_pos (by linarith) hr') ha0
  have e : ∀ t : ℕ, (β * (1 + r)) ^ t * K / (1 + r) ^ t = K * β ^ t := fun t => by
    rw [mul_pow]; field_simp
  have hgeo := hasSum_geometric_of_lt_one hβ0.le hβ1
  refine ⟨?_, fun c hc hcs hbud hu => ?_⟩
  · simp only [e]
    have := hgeo.mul_left K
    convert this using 1
    simp only [K]; field_simp [show (1 - β) ≠ 0 by linarith]
  set cs : ℕ → ℝ := fun t => (β * (1 + r)) ^ t * K
  have hcs0 : ∀ t, 0 < cs t := fun t => mul_pos (pow_pos (mul_pos hβ0 hr') t) hK
  have hlogcs : ∀ t, β ^ t * Real.log (cs t) =
      Real.log (β * (1 + r)) * ((t : ℝ) ^ 1 * β ^ t) + Real.log K * β ^ t := fun t => by
    simp only [cs]
    rw [Real.log_mul (pow_pos (mul_pos hβ0 hr') t).ne' hK.ne', Real.log_pow]
    ring
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hsumcs : Summable fun t => β ^ t * Real.log (cs t) := by
    simp only [hlogcs]
    exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left _).add
      (hgeo.summable.mul_left _)
  -- the tangent inequality `log x ≤ log y + x/y − 1`, weighted by `βᵗ`
  have hle : ∀ t, β ^ t * Real.log (c t) ≤ β ^ t * Real.log (cs t) +
      (c t / (1 + r) ^ t) / K - β ^ t := fun t => by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hc t) (hcs0 t))
    rw [Real.log_div (hc t).ne' (hcs0 t).ne'] at h1
    have hb := pow_pos hβ0 t
    have h2 : β ^ t * (c t / cs t) = (c t / (1 + r) ^ t) / K := by
      simp only [cs]; rw [mul_pow]; field_simp
    nlinarith
  have hsumR : Summable fun t => β ^ t * Real.log (cs t) + (c t / (1 + r) ^ t) / K - β ^ t :=
    (hsumcs.add (hcs.div_const K)).sub hgeo.summable
  have := hu.tsum_le_tsum hle hsumR
  rw [Summable.tsum_sub (hsumcs.add (hcs.div_const K)) hgeo.summable,
    Summable.tsum_add hsumcs (hcs.div_const K), tsum_div_const, hgeo.tsum_eq] at this
  have hbudK : (∑' t, c t / (1 + r) ^ t) / K ≤ (1 - β)⁻¹ := by
    rw [div_le_iff₀ hK]
    calc ∑' t, c t / (1 + r) ^ t ≤ a0 * (1 + r) := hbud
      _ = (1 - β)⁻¹ * K := by simp only [K]; field_simp [show (1 - β) ≠ 0 by linarith]
  linarith

end AKMM.DynamicOptimization
