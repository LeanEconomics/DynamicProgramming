/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.ExcessCost
import Mathlib.Analysis.MeanInequalities

/-!
# The Laffer curve

AKMM, §15.3.4, pp. 453–454, footnote 6.

Steady-state revenue in the GHH economy with `τ_c = 0` is
`R(τ_ℓ, τ_k) = τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y`, with `y` from (15.13) (`lafRevenue`).
Writing `z = (1 − τ_ℓ)(1 − α)` and `K = 1 − (ρ + δ)s`, `R = (K − z)z^φ(s^{α/(1−α)})^{1+φ}`
(`laf_revenue_eq`).

* `(K − z)z^φ ≤ φ^φ(K/(1 + φ))^{1+φ}` for `z ≥ 0`, with equality at `z = φK/(1 + φ)` (weighted
  AM–GM; `laf_amgm`, `laf_amgm_eq`).
* Footnote 6: for each `τ_k`, revenue is maximised over `τ_ℓ ≤ 1` at
  `τ_ℓ = (1 − τ_kρφα/((1 − α)(ρ + (1 − τ_k)δ)))/(1 + φ)` (`footnote_6`).
* **The revenue-maximising pair** over `τ_ℓ ∈ [0, 1]`, `τ_k ∈ [0, 1)` is `(1/(1 + φ), 0)`
  (`laf_isMaxOn`), and any positive `τ_k` raises strictly less (`laf_lt_of_pos`); this is the
  global form of footnote 6's "tax revenue is declining in `τ_k` at `τ_k = 0`". The proof uses
  the wage bound `inc_wage_le`.
* The revenue-maximising labour tax `1/(1 + φ)` falls as the Frisch elasticity `φ` rises
  (`laf_rate_strictAntiOn`).
* The Laffer curve at `τ_k = 0` is hump-shaped: zero at `τ_ℓ = 0` and `τ_ℓ = 1`, positive in
  between (`laf_hump`); at `τ_ℓ = 1` hours are zero (`laf_hours_zero`).

Departures: none. (The book asks for "positive" tax rates; we use `τ_ℓ, τ_k ≥ 0`.)
-/

namespace AKMM.FiscalPolicy

open Real

/-- Steady-state tax revenue `τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y` (AKMM, fn. 6, p. 454),
with `y` from (15.13) at `τ_c = 0`. -/
noncomputable def lafRevenue (α β δ φ τl τk : ℝ) : ℝ :=
  (τl * (1 - α) + incBud α β δ τk) * incOutput α φ ((1 - τl) * (1 - α)) (lrS α β δ τk)

/-- `τ_kρα/(ρ + (1 − τ_k)δ) = α − (ρ + δ)s` (for `τ_k < 1`, `ρ > 0`, `δ ≥ 0`). -/
theorem laf_bud_eq {α β δ τk : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hτk : τk < 1) :
    incBud α β δ τk = α - (lrRho β + δ) * lrS α β δ τk := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hd : 0 < lrRho β + (1 - τk) * δ := by
    have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
    linarith
  unfold incBud lrS
  rw [mul_comm δ (1 - τk)]
  field_simp
  ring

/-- AKMM, fn. 6: `R = (K − z)z^φ(s^{α/(1−α)})^{1+φ}` with `z = (1 − τ_ℓ)(1 − α)`,
`K = 1 − (ρ + δ)s`. -/
theorem laf_revenue_eq {α β δ φ τl τk : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hτk : τk < 1) (hs : 0 < lrS α β δ τk) :
    lafRevenue α β δ φ τl τk =
      ((1 - (lrRho β + δ) * lrS α β δ τk) - (1 - τl) * (1 - α)) *
        ((1 - τl) * (1 - α)) ^ φ * (lrS α β δ τk ^ (α / (1 - α))) ^ (1 + φ) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  unfold lafRevenue incOutput
  rw [laf_bud_eq hβ0 hβ1 hδ hτk, ← Real.rpow_mul hs.le,
    show α / (1 - α) * (1 + φ) = α * (1 + φ) / (1 - α) by ring]
  ring

/-- Weighted AM–GM: for `φ > 0`, `K ≥ 0`, `z ≥ 0`, `(K − z)z^φ ≤ φ^φ(K/(1 + φ))^{1+φ}`. -/
theorem laf_amgm {φ K z : ℝ} (hφ : 0 < φ) (hK : 0 ≤ K) (hz : 0 ≤ z) :
    (K - z) * z ^ φ ≤ φ ^ φ * (K / (1 + φ)) ^ (1 + φ) := by
  have hφ1 : 0 < 1 + φ := by linarith
  have hR : 0 ≤ φ ^ φ * (K / (1 + φ)) ^ (1 + φ) := by positivity
  by_cases hKz : K ≤ z
  · have : (K - z) * z ^ φ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hz φ)
    linarith
  push Not at hKz
  have hw1 : 0 ≤ 1 / (1 + φ) := by positivity
  have hw2 : 0 ≤ φ / (1 + φ) := by positivity
  have hw : 1 / (1 + φ) + φ / (1 + φ) = 1 := by field_simp
  have hp1 : 0 ≤ K - z := by linarith
  have hp2 : 0 ≤ z / φ := by positivity
  have hG := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hp1 hp2 hw
  have harith : 1 / (1 + φ) * (K - z) + φ / (1 + φ) * (z / φ) = K / (1 + φ) := by
    field_simp
    ring
  rw [harith] at hG
  have hlhs : 0 ≤ (K - z) ^ (1 / (1 + φ)) * (z / φ) ^ (φ / (1 + φ)) := by positivity
  have hpow := Real.rpow_le_rpow hlhs hG hφ1.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hp1,
    ← Real.rpow_mul hp2, one_div_mul_cancel hφ1.ne', div_mul_cancel₀ _ hφ1.ne',
    Real.rpow_one, Real.div_rpow hz hφ.le] at hpow
  have hφφ : 0 < φ ^ φ := Real.rpow_pos_of_pos hφ φ
  have : (K - z) * z ^ φ = φ ^ φ * ((K - z) * (z ^ φ / φ ^ φ)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hpow hφφ.le

/-- The AM–GM bound is attained at `z = φK/(1 + φ)`. -/
theorem laf_amgm_eq {φ K : ℝ} (hφ : 0 < φ) (hK : 0 ≤ K) :
    (K - φ * K / (1 + φ)) * (φ * K / (1 + φ)) ^ φ = φ ^ φ * (K / (1 + φ)) ^ (1 + φ) := by
  have hφ1 : 0 < 1 + φ := by linarith
  have hKφ : 0 ≤ K / (1 + φ) := by positivity
  rw [show φ * K / (1 + φ) = φ * (K / (1 + φ)) by ring, Real.mul_rpow hφ.le hKφ,
    Real.rpow_add' hKφ (by linarith), Real.rpow_one,
    show K - φ * (K / (1 + φ)) = K / (1 + φ) by field_simp; ring]
  ring

/-- **Footnote 6** (AKMM, p. 454): for given `τ_k ∈ [0, 1)` the revenue-maximising labour tax
(over `τ_ℓ ≤ 1`) is `τ_ℓ = (1 − τ_kρφα/((1 − α)(ρ + (1 − τ_k)δ)))/(1 + φ)`. -/
theorem footnote_6 {α β δ φ τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) (hτ0 : 0 ≤ τk) (hτk : τk < 1) :
    IsMaxOn (fun τl => lafRevenue α β δ φ τl τk) (Set.Iic 1)
      ((1 - τk * lrRho β / (1 - α) * φ * (α / (lrRho β + (1 - τk) * δ))) / (1 + φ)) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have h1α : 0 < 1 - α := by linarith
  have hφ1 : 0 < 1 + φ := by linarith
  have hs : 0 < lrS α β δ τk := by
    have : 0 < 1 - τk := by linarith
    unfold lrS
    positivity
  set K := 1 - (lrRho β + δ) * lrS α β δ τk with hK
  have hKpos : 0 ≤ K := by
    have hb : 0 ≤ incBud α β δ τk := by
      have : 0 < lrRho β + (1 - τk) * δ := by
        have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
        linarith
      unfold incBud
      positivity
    have := laf_bud_eq hβ0 hβ1 hδ hτk (α := α)
    linarith
  have hA : 0 ≤ (lrS α β δ τk ^ (α / (1 - α))) ^ (1 + φ) := by positivity
  set τs := (1 - τk * lrRho β / (1 - α) * φ * (α / (lrRho β + (1 - τk) * δ))) / (1 + φ)
  have hzs : (1 - τs) * (1 - α) = φ * K / (1 + φ) := by
    have hb := laf_bud_eq hβ0 hβ1 hδ hτk (α := α)
    unfold incBud at hb
    have hd : 0 < lrRho β + (1 - τk) * δ := by
      have : 0 ≤ (1 - τk) * δ := mul_nonneg (by linarith) hδ
      linarith
    rw [hK]
    have : (lrRho β + δ) * lrS α β δ τk = α - τk * lrRho β * α / (lrRho β + (1 - τk) * δ) := by
      linarith
    rw [this]
    simp only [τs]
    field_simp
    ring
  intro τl hτl
  simp only [Set.mem_ofPred_eq]
  have hz : 0 ≤ (1 - τl) * (1 - α) := mul_nonneg (by linarith [Set.mem_Iic.mp hτl]) h1α.le
  rw [laf_revenue_eq hα1 hβ0 hβ1 hδ hτk hs, laf_revenue_eq hα1 hβ0 hβ1 hδ hτk hs, ← hK, hzs,
    laf_amgm_eq hφ hKpos]
  exact mul_le_mul_of_nonneg_right (laf_amgm hφ hKpos hz) hA

/-- The no-tax value `s₀ = α/(ρ + δ)` of `s`. -/
theorem laf_s0 {α β δ : ℝ} : lrS α β δ 0 = α / (lrRho β + δ) := by
  unfold lrS
  simp

/-- AKMM, fn. 6 (global form): for `τ_ℓ ∈ [0, 1]` and `τ_k ∈ [0, 1)`,
`R(τ_ℓ, τ_k) ≤ φ^φ((1 − α)s₀^{α/(1−α)}/(1 + φ))^{1+φ}`, strictly if `τ_k > 0`. -/
theorem laf_bound {α β δ φ τl τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) (hτl : τl ≤ 1) (hτ0 : 0 ≤ τk) (hτk : τk < 1) :
    lafRevenue α β δ φ τl τk ≤
      φ ^ φ * ((1 - α) * lrS α β δ 0 ^ (α / (1 - α)) / (1 + φ)) ^ (1 + φ) ∧
    (0 < τk → lafRevenue α β δ φ τl τk <
      φ ^ φ * ((1 - α) * lrS α β δ 0 ^ (α / (1 - α)) / (1 + φ)) ^ (1 + φ)) := by
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have h1α : 0 < 1 - α := by linarith
  have hφ1 : 0 < 1 + φ := by linarith
  have hc : 0 < lrRho β + δ := by linarith
  set s := lrS α β δ τk with hsdef
  have hs : 0 < s := by
    have : 0 < 1 - τk := by linarith
    rw [hsdef]
    unfold lrS
    positivity
  have hss : s ≤ α / (lrRho β + δ) := by
    rw [← laf_s0]
    exact (lr_s_strictAntiOn hα0 hβ0 hβ1 hδ).antitoneOn (Set.mem_Iio.mpr one_pos)
      (Set.mem_Iio.mpr hτk) hτ0
  set K := 1 - (lrRho β + δ) * s with hK
  set A := s ^ (α / (1 - α)) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos hs _
  have hKpos : 0 ≤ K := by
    have : (lrRho β + δ) * s ≤ α := by
      have := mul_le_mul_of_nonneg_left hss hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    linarith
  obtain ⟨hW, hWs⟩ := inc_wage_le hα0 hα1 hc hs hss
  rw [← hK, ← hA, ← laf_s0] at hW hWs
  have hz : 0 ≤ (1 - τl) * (1 - α) := mul_nonneg (by linarith) h1α.le
  have hR : lafRevenue α β δ φ τl τk ≤ φ ^ φ * (K * A / (1 + φ)) ^ (1 + φ) := by
    rw [laf_revenue_eq hα1 hβ0 hβ1 hδ hτk hs, ← hsdef, ← hK, ← hA]
    have := mul_le_mul_of_nonneg_right (laf_amgm hφ hKpos hz)
      (Real.rpow_nonneg hApos.le (1 + φ))
    calc (K - (1 - τl) * (1 - α)) * ((1 - τl) * (1 - α)) ^ φ * A ^ (1 + φ)
        ≤ φ ^ φ * (K / (1 + φ)) ^ (1 + φ) * A ^ (1 + φ) := this
      _ = φ ^ φ * (K * A / (1 + φ)) ^ (1 + φ) := by
          rw [mul_assoc, ← Real.mul_rpow (by positivity) hApos.le]
          ring_nf
  have hφφ : 0 < φ ^ φ := Real.rpow_pos_of_pos hφ φ
  constructor
  · refine hR.trans (mul_le_mul_of_nonneg_left ?_ hφφ.le)
    exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hW hφ1.le) hφ1.le
  · intro hpos
    have hlt : s < lrS α β δ 0 := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ (Set.mem_Iio.mpr one_pos)
        (Set.mem_Iio.mpr hτk) hpos
    refine hR.trans_lt (mul_lt_mul_of_pos_left ?_ hφφ)
    exact Real.rpow_lt_rpow (by positivity) (div_lt_div_of_pos_right (hWs hlt) hφ1) hφ1

/-- The bound of `laf_bound` is attained at `(τ_ℓ, τ_k) = (1/(1 + φ), 0)`. -/
theorem laf_value_at_max {α β δ φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    lafRevenue α β δ φ (1 / (1 + φ)) 0 =
      φ ^ φ * ((1 - α) * lrS α β δ 0 ^ (α / (1 - α)) / (1 + φ)) ^ (1 + φ) := by
  have h1α : 0 < 1 - α := by linarith
  have hφ1 : 0 < 1 + φ := by linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs : 0 < lrS α β δ 0 := by
    rw [laf_s0]
    exact div_pos hα0 (by linarith)
  rw [laf_revenue_eq hα1 hβ0 hβ1 hδ (by norm_num) hs]
  have hK : 1 - (lrRho β + δ) * lrS α β δ 0 = 1 - α := by
    rw [laf_s0]
    field_simp
  have hz : (1 - 1 / (1 + φ)) * (1 - α) = φ * (1 - α) / (1 + φ) := by
    field_simp
    ring
  rw [hK, hz, laf_amgm_eq hφ h1α.le, mul_assoc,
    ← Real.mul_rpow (by positivity) (Real.rpow_nonneg hs.le _)]
  ring_nf

/-- **The revenue-maximising tax rates** (AKMM, p. 453): over `τ_ℓ ∈ [0, 1]`, `τ_k ∈ [0, 1)`,
steady-state revenue is maximised at `τ_ℓ = 1/(1 + φ)`, `τ_k = 0`. -/
theorem laf_isMaxOn {α β δ φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    IsMaxOn (fun p : ℝ × ℝ => lafRevenue α β δ φ p.1 p.2) (Set.Icc 0 1 ×ˢ Set.Ico 0 1)
      (1 / (1 + φ), 0) := by
  intro p hp
  simp only [Set.mem_ofPred_eq]
  obtain ⟨⟨_, h1⟩, ⟨h2, h3⟩⟩ := hp
  rw [laf_value_at_max hα0 hα1 hβ0 hβ1 hδ hφ]
  exact (laf_bound hα0 hα1 hβ0 hβ1 hδ hφ h1 h2 h3).1

/-- AKMM, fn. 6: any positive capital tax raises strictly less than the maximum. -/
theorem laf_lt_of_pos {α β δ φ τl τk : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hτl : τl ≤ 1) (hτ0 : 0 < τk) (hτk : τk < 1) :
    lafRevenue α β δ φ τl τk < lafRevenue α β δ φ (1 / (1 + φ)) 0 := by
  rw [laf_value_at_max hα0 hα1 hβ0 hβ1 hδ hφ]
  exact (laf_bound hα0 hα1 hβ0 hβ1 hδ hφ hτl hτ0.le hτk).2 hτ0

/-- AKMM, p. 454: "the higher is the Frisch elasticity of labor supply, `φ`, the lower is the
revenue-maximizing labor tax rate". -/
theorem laf_rate_strictAntiOn : StrictAntiOn (fun φ : ℝ => 1 / (1 + φ)) (Set.Ioi 0) := by
  intro a ha b _ hab
  have ha' : 0 < a := ha
  simp only
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- AKMM, p. 454: at `τ_ℓ = 1` hours `((1 − τ_ℓ)w)^φ` are zero. -/
theorem laf_hours_zero {φ w : ℝ} (hφ : 0 < φ) : ghhHours φ 1 0 w = 0 := by
  simp [ghhHours, Real.zero_rpow hφ.ne']

/-- AKMM, p. 454: "Revenue is hump-shaped in the tax rate": at `τ_k = 0`, revenue is zero at
`τ_ℓ = 0` and at `τ_ℓ = 1`, and positive for `0 < τ_ℓ < 1`. -/
theorem laf_hump {α β δ φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hφ : 0 < φ) :
    lafRevenue α β δ φ 0 0 = 0 ∧ lafRevenue α β δ φ 1 0 = 0 ∧
      ∀ τl, 0 < τl → τl < 1 → 0 < lafRevenue α β δ φ τl 0 := by
  have h1α : 0 < 1 - α := by linarith
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hs : 0 < lrS α β δ 0 := by
    rw [laf_s0]
    exact div_pos hα0 (by linarith)
  have hb : incBud α β δ 0 = 0 := by simp [incBud]
  refine ⟨?_, ?_, ?_⟩
  · simp [lafRevenue, hb]
  · simp [lafRevenue, hb, incOutput, Real.zero_rpow hφ.ne']
  · intro τl h0 h1
    unfold lafRevenue incOutput
    rw [hb, add_zero]
    have : 0 < (1 - τl) * (1 - α) := mul_pos (by linarith) h1α
    positivity

end AKMM.FiscalPolicy
