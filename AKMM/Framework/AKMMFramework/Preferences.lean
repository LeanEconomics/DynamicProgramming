/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Saving: the Euler equation and CRRA utility

AKMM, §2.1.8, "Consumption vs. saving", pp. 62–63, with footnote 19.

* **The Euler equation** `u′(c_t) = βu′(c_{t+1})R_{t+1}`, equivalently
  `u′(c_t)/(βu′(c_{t+1})) = R_{t+1}`: the first-order condition of
  `max u(c_t) + βu(c_{t+1})` subject to `c_{t+1} = R_{t+1}(W − c_t)` at an interior optimum
  (`pref_euler_equation`).
* **CRRA utility (2.5)** `u(c) = (c^{1−σ} − 1)/(1 − σ)` (`prefCrra`), with `u′(c) = c^{−σ}`
  (`eq_2_5_hasDerivAt`). The "if" part on p. 63: `u′(c)/u′((1 + γ)c) = (1 + γ)^σ` does not depend
  on `c` (`pref_crra_mu_ratio`); at a constant gross rate `R` the Euler equation holds exactly
  when `c_{t+1} = (βR)^{1/σ}c_t` (`pref_crra_euler_iff`), so the consumer chooses a constant growth
  rate that depends on `R`, `β` and `σ` but not on wealth (`pref_crra_constant_growth`).
* **The log limit** (footnote 19): `(c^{1−σ} − 1)/(1 − σ) → log c` as `σ → 1`
  (`pref_crra_log_limit`), with the l'Hôpital derivatives `−c^{1−σ}log c` and `−1`
  (`pref_footnote_19_derivatives`).

The "only if" part (power utility is the only class consistent with balanced growth) is proved
in the book's Appendix 4.A.2, not here.
-/

namespace AKMM.Framework

open Filter Topology

/-- AKMM, p. 62: the Euler equation. A consumer with wealth `W` chooses `c₀` and consumes
`c₁ = R(W − c₀)` next period. If `c₀` is a local maximum of `u(c) + βu(R(W − c))` and `u` is
differentiable at `c₀` and at `c₁ = R(W − c₀)`, then `u′(c₀) = βu′(c₁)R`, and, when
`βu′(c₁) ≠ 0`, `u′(c₀)/(βu′(c₁)) = R`. -/
theorem pref_euler_equation {u : ℝ → ℝ} {β R W c₀ u0 u1 : ℝ}
    (hu0 : HasDerivAt u u0 c₀) (hu1 : HasDerivAt u u1 (R * (W - c₀)))
    (hmax : IsLocalMax (fun c => u c + β * u (R * (W - c))) c₀) :
    u0 = β * u1 * R ∧ (β * u1 ≠ 0 → u0 / (β * u1) = R) := by
  have hc : HasDerivAt (fun c => R * (W - c)) (-R) c₀ := by
    simpa using ((hasDerivAt_id c₀).const_sub W).const_mul R
  have hd : HasDerivAt (fun c => u c + β * u (R * (W - c))) (u0 + β * (u1 * -R)) c₀ :=
    hu0.add ((hu1.comp c₀ hc).const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hd
  have he : u0 = β * u1 * R := by linarith
  refine ⟨he, fun hne => ?_⟩
  rw [he]
  exact mul_div_cancel_left₀ R hne

/-- AKMM, (2.5), p. 63: CRRA utility `u(c) = (c^{1−σ} − 1)/(1 − σ)`. -/
noncomputable def prefCrra (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, (2.5), p. 63: for `σ ≠ 1` and `c > 0`, `u′(c) = c^{−σ}`. -/
theorem eq_2_5_hasDerivAt {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (prefCrra σ) (c ^ (-σ)) c := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
    (1 - σ)
  have h1 : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have h3 : (1 - σ) * c ^ (1 - σ - 1) / (1 - σ) = c ^ (-σ) := by
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  exact h.congr_deriv h3

/-- AKMM, p. 63: for power utility `u′(c)/u′((1 + γ)c) = (1 + γ)^σ` for every `c > 0`: the ratio
is constant in `c` and contains the growth rate. -/
theorem pref_crra_mu_ratio {σ γ c : ℝ} (hγ : 0 < 1 + γ) (hc : 0 < c) :
    c ^ (-σ) / ((1 + γ) * c) ^ (-σ) = (1 + γ) ^ σ := by
  rw [Real.mul_rpow hγ.le hc.le, Real.rpow_neg hγ.le]
  have h1 : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have h2 : 0 < (1 + γ) ^ σ := Real.rpow_pos_of_pos hγ _
  field_simp

/-- AKMM, p. 63: with power marginal utility `u′(c) = c^{−σ}`, `σ > 0`, and `β, R > 0`, the
Euler equation `u′(c) = βRu′(c′)` holds if and only if `c′ = (βR)^{1/σ}c`. -/
theorem pref_crra_euler_iff {σ β R c c' : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hc : 0 < c) (hc' : 0 < c') :
    c ^ (-σ) = β * R * c' ^ (-σ) ↔ c' = (β * R) ^ (1 / σ) * c := by
  have hbR : 0 < β * R := mul_pos hβ hR
  have hσ' : σ ≠ 0 := hσ.ne'
  -- both sides are equivalent to `c'^σ = βR c^σ`
  have key : c ^ (-σ) = β * R * c' ^ (-σ) ↔ c' ^ σ = β * R * c ^ σ := by
    rw [Real.rpow_neg hc.le, Real.rpow_neg hc'.le]
    have h1 : 0 < c ^ σ := Real.rpow_pos_of_pos hc σ
    have h2 : 0 < c' ^ σ := Real.rpow_pos_of_pos hc' σ
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      field_simp
      linarith
  rw [key]
  constructor
  · intro h
    have : c' = (c' ^ σ) ^ (1 / σ) := by
      rw [← Real.rpow_mul hc'.le, mul_one_div_cancel hσ', Real.rpow_one]
    rw [this, h, Real.mul_rpow hbR.le (Real.rpow_nonneg hc.le σ), ← Real.rpow_mul hc.le,
      mul_one_div_cancel hσ', Real.rpow_one]
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hbR.le _) hc.le, ← Real.rpow_mul hbR.le,
      one_div_mul_cancel hσ', Real.rpow_one]

/-- AKMM, p. 63: under power utility and a constant gross interest rate `R`, the path
`c_t = ((βR)^{1/σ})^t c_0` satisfies the Euler equation `u′(c_t) = βRu′(c_{t+1})` in every
period, and it is the only positive path from `c_0` that does: consumption grows at the constant
gross rate `(βR)^{1/σ}`, which depends on `R`, `β`, `σ` but not on `c_0`. -/
theorem pref_crra_constant_growth {σ β R c₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hc₀ : 0 < c₀) :
    (∀ t : ℕ, ((β * R) ^ (1 / σ)) ^ t * c₀ > 0 ∧
      (((β * R) ^ (1 / σ)) ^ t * c₀) ^ (-σ) =
        β * R * (((β * R) ^ (1 / σ)) ^ (t + 1) * c₀) ^ (-σ)) ∧
      ∀ c : ℕ → ℝ, c 0 = c₀ → (∀ t, 0 < c t) →
        (∀ t, c t ^ (-σ) = β * R * c (t + 1) ^ (-σ)) →
          ∀ t, c t = ((β * R) ^ (1 / σ)) ^ t * c₀ := by
  have hg : 0 < (β * R) ^ (1 / σ) := Real.rpow_pos_of_pos (mul_pos hβ hR) _
  refine ⟨fun t => ⟨mul_pos (pow_pos hg t) hc₀, ?_⟩, fun c h0 hpos he t => ?_⟩
  · rw [pref_crra_euler_iff hσ hβ hR (mul_pos (pow_pos hg t) hc₀)
      (mul_pos (pow_pos hg (t + 1)) hc₀), pow_succ]
    ring
  · induction t with
    | zero => simp [h0]
    | succ t ih =>
      rw [(pref_crra_euler_iff hσ hβ hR (hpos t) (hpos (t + 1))).1 (he t), ih, pow_succ]
      ring

/-- AKMM, footnote 19, p. 63: the l'Hôpital derivatives in `σ`: `d(c^{1−σ} − 1)/dσ =
−c^{1−σ}log c` and `d(1 − σ)/dσ = −1`, for `c > 0`. -/
theorem pref_footnote_19_derivatives {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    HasDerivAt (fun s => c ^ (1 - s) - 1) (-(c ^ (1 - σ) * Real.log c)) σ ∧
      HasDerivAt (fun s : ℝ => 1 - s) (-1) σ := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) σ := by
    simpa using (hasDerivAt_id σ).const_sub 1
  refine ⟨?_, h1⟩
  have h2 := ((Real.hasStrictDerivAt_const_rpow hc (1 - σ)).hasDerivAt.comp σ h1).sub_const 1
  exact h2.congr_deriv (by ring)

/-- AKMM, p. 63 and footnote 19: as `σ → 1`, CRRA utility (2.5) tends to `log c`, for `c > 0`. -/
theorem pref_crra_log_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ => prefCrra σ c) (𝓝[≠] 1) (𝓝 (Real.log c)) := by
  -- the slope of `x ↦ c^x` at `0`
  have hd : HasDerivAt (fun x : ℝ => c ^ x) (c ^ (0 : ℝ) * Real.log c) 0 :=
    (Real.hasStrictDerivAt_const_rpow hc 0).hasDerivAt
  rw [Real.rpow_zero, one_mul, hasDerivAt_iff_tendsto_slope] at hd
  -- `σ ↦ 1 − σ` maps a punctured neighbourhood of `1` into one of `0`
  have hm : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_ne_zero.2 (Ne.symm hσ)
  refine (hd.comp hm).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ _
  simp only [Function.comp_apply, slope_def_field, prefCrra, Real.rpow_zero, sub_zero]

end AKMM.Framework
