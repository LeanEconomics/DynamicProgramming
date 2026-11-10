/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §17.2.4: seigniorage

Miao, §17.2.4, pp. 577–579. No taxes, no borrowing (`φ = b = 0`); the government finances real
purchases `G` by printing money, `M_{t+1}/p_t = M_t/p_t + G`.

* `bw_seign_budget`: the budget in the form `M_{t+1}/p_t = (M_t/p_{t−1})(p_{t−1}/p_t) + G`.
* `bw_seign_mbar`: in a stationary equilibrium with `p_{t−1}/p_t = 1 + r` and `M_{t+1}/p_t = m̄`,
  `m̄ = −G/r`; `bw_seign_neg_rate`: with `G > 0` and valued money `m̄ > 0`, `r < 0` (the inflation
  tax `−r`), and the curve `m̄ = −G/r` lies in the south-east quadrant.
* `bw_seign_initial_price`, `bw_seign_quantity_theory`: `m̄ = M₀/p₀ + G` determines
  `p₀ = M₀/(m̄ − G)`; scaling `M₀` scales `p₀` and all later prices `p_t = p₀(1 + r)^{−t}`.
* `bw_seign_comparative_statics`: the selection by the highest return on currency gives the
  standard comparative statics. If `Ea` is continuous on `[r₂, 0]` and `r₂ < 0` is an equilibrium
  for the deficit `G₂`, then for every smaller deficit `0 < G₁ < G₂` there is an equilibrium
  `r₁ ∈ (r₂, 0)`; so raising `G` lowers the highest equilibrium return and raises inflation.

Multiplicity of stationary equilibria (Figure 17.4) and the effects of `b > 0` (the `Ea` curve
shifting left, possibly eliminating all equilibria) are read from figures and not formalised.
-/

namespace Miao.IncompleteMarkets

/-- Miao, p. 577: the government budget `M_{t+1}/p_t = M_t/p_t + G` written as
`M_{t+1}/p_t = (M_t/p_{t−1})(p_{t−1}/p_t) + G`. -/
theorem bw_seign_budget {M M' p p₀ G : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) :
    M' / p = M / p + G ↔ M' / p = M / p₀ * (p₀ / p) + G := by
  have : M / p₀ * (p₀ / p) = M / p := by field_simp
  rw [this]

/-- Miao, p. 577: in a stationary equilibrium with `p_{t−1}/p_t = 1 + r` and constant real
balances `M_{t+1}/p_t = m̄`, the budget `m̄ = m̄(1 + r) + G` gives `m̄ = −G/r` (`r ≠ 0`). -/
theorem bw_seign_mbar {mbar r G : ℝ} (hst : mbar = mbar * (1 + r) + G) (hr : r ≠ 0) :
    mbar = -G / r := by
  field_simp
  linarith

/-- Miao, p. 577: for `G > 0` a stationary equilibrium with valued money `m̄ > 0` has `r ≠ 0` and
`r < 0` ("`−r` can be regarded as an inflation tax"); conversely each `r < 0` gives a point
`(m̄, r) = (−G/r, r)` in the south-east quadrant. -/
theorem bw_seign_neg_rate {mbar r G : ℝ} (hG : 0 < G) (hst : mbar = mbar * (1 + r) + G)
    (hm : 0 < mbar) : r < 0 ∧ mbar = -G / r := by
  have hmr : mbar * r = -G := by linarith
  have hr : r < 0 := by
    by_contra h
    have := mul_nonneg hm.le (not_lt.1 h)
    linarith
  exact ⟨hr, bw_seign_mbar hst hr.ne⟩

/-- Miao, p. 577: the curve `m̄ = −G/r` lies in the south-east quadrant for `G > 0`, `r < 0`. -/
theorem bw_seign_hyperbola {r G : ℝ} (hG : 0 < G) (hr : r < 0) : 0 < -G / r :=
  div_pos_of_neg_of_neg (by linarith) hr

/-- Miao, pp. 577–578: the initial government budget `m̄ = M₀/p₀ + G` (with `m̄ > G`) determines
`p₀ = M₀/(m̄ − G)`. -/
theorem bw_seign_initial_price {mbar M₀ p₀ G : ℝ} (hp₀ : 0 < p₀) (hm : G < mbar) :
    mbar = M₀ / p₀ + G ↔ p₀ = M₀ / (mbar - G) := by
  have h : mbar - G ≠ 0 := by linarith
  constructor
  · intro h1
    have h2 : M₀ / p₀ = mbar - G := by linarith
    rw [eq_div_iff h, ← h2]
    field_simp
  · intro h1
    have hM : M₀ ≠ 0 := by
      rintro rfl
      rw [zero_div] at h1
      linarith
    rw [h1]
    field_simp
    ring

/-- Miao, p. 578 (a version of the quantity theory): with `p_{t−1}/p_t = 1 + r`,
`p_t = p₀(1 + r)^{−t}`; an increase of `M₀` by the factor `k` increases `p₀` and all subsequent
prices proportionately. -/
theorem bw_seign_quantity_theory (mbar M₀ G k r : ℝ) (t : ℕ) :
    k * M₀ / (mbar - G) / (1 + r) ^ t = k * (M₀ / (mbar - G) / (1 + r) ^ t) := by
  ring

/-- Miao, p. 578: **the comparative statics of the highest-return selection**. Let `Ea` be
continuous on `[r₂, 0]` and `r₂ < 0` a stationary equilibrium for the deficit `G₂`,
`Ea(r₂) = −G₂/r₂`. Then for every deficit `0 < G₁ < G₂` there is an equilibrium `r₁ ∈ (r₂, 0)`,
`Ea(r₁) = −G₁/r₁`. Hence the highest equilibrium return falls when `G` rises. -/
theorem bw_seign_comparative_statics {Ea : ℝ → ℝ} {r₂ G₁ G₂ : ℝ} (hr₂ : r₂ < 0)
    (hEa : ContinuousOn Ea (Set.Icc r₂ 0)) (heq : Ea r₂ = -G₂ / r₂) (hG₁ : 0 < G₁)
    (hG : G₁ < G₂) : ∃ r₁, r₂ < r₁ ∧ r₁ < 0 ∧ Ea r₁ = -G₁ / r₁ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := r₂) (b := 0)).exists_bound_of_continuousOn hEa
  set B' := max B 0
  set c := max (r₂ / 2) (-G₁ / (2 * (B' + 1)))
  have hB' : 0 ≤ B' := le_max_right _ _
  have hc0 : c < 0 := max_lt (by linarith) (div_neg_of_neg_of_pos (by linarith) (by linarith))
  have hrc : r₂ < c := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set f : ℝ → ℝ := fun r => Ea r + G₁ / r
  have hfc : ContinuousOn f (Set.Icc r₂ c) := by
    refine (hEa.mono (Set.Icc_subset_Icc le_rfl hc0.le)).add ?_
    exact continuousOn_const.div continuousOn_id fun r hr => (hr.2.trans_lt hc0).ne
  have hf2 : 0 < f r₂ := by
    simp only [f, heq]
    rw [← add_div]
    exact div_pos_of_neg_of_neg (by linarith) hr₂
  have hfcneg : f c < 0 := by
    have hEc : Ea c ≤ B' := by
      have := hB c ⟨hrc.le, hc0.le⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hge : -G₁ / (2 * (B' + 1)) ≤ c := le_max_right _ _
    have hdiv : G₁ / c ≤ -(2 * (B' + 1)) := by
      rw [div_le_iff_of_neg hc0]
      have h1 : -G₁ ≤ c * (2 * (B' + 1)) := by
        rwa [div_le_iff₀ (by linarith)] at hge
      linarith
    simp only [f]
    linarith
  obtain ⟨r₁, hr₁, hf1⟩ :=
    intermediate_value_Icc' hrc.le hfc ⟨hfcneg.le, hf2.le⟩
  have hne : r₁ ≠ r₂ := by rintro rfl; linarith
  refine ⟨r₁, lt_of_le_of_ne hr₁.1 hne.symm, hr₁.2.trans_lt hc0, ?_⟩
  simp only [f] at hf1
  have hr0 : r₁ ≠ 0 := (hr₁.2.trans_lt hc0).ne
  rw [neg_div]
  linarith

end Miao.IncompleteMarkets
