/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.FSDNK
import NewKeynesian.NewKeynesian
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fiscal stimulus at the zero lower bound

Miao, §19.3, pp. 648–654, (19.53)–(19.60), and Exercise 19.3 (p. 669), following Eggertsson
(2009) and Woodford (2011).

The two-state setting: the crisis state `L` (with `r^net_t = r_L`, `Ĝ_t = Ĝ_L`) persists each
period with probability `μ`; the normal state is absorbing, with `π = Ŷ = Ĝ = 0` and `i = r̄`.
For a variable equal to `x_L` in the crisis and `0` in the normal state, the expectation in the
crisis is `E_t x_{t+1} = μx_L`, and `E_t x_{t+j} = μʲx_L`. A path in the crisis state is a
sequence `(Ŷ_t, π_t)` of crisis values (the only history in which the crisis lasts until `t`).

* (19.53): it reduces to (19.50) when `Δ_t = 0` (`eq_19_53`); with `r^net < 0` the zero bound
  rules out the zero-inflation steady state (`fs_zlb_no_steady_state`).
* (19.55): `h(μ) = (1 − μ)(1 − βμ) − κσμ` is strictly decreasing on `[0, 1]`, `h(0) = 1`,
  `h(1) = −κσ`; there is a unique `μ̄ ∈ (0, 1)` with `h(μ̄) = 0`, and (19.55) holds on `[0, 1]` iff
  `μ < μ̄` (`fs_h_strictAntiOn`, `fs_mubar_exists`, `eq_19_55_iff`). The book's "for all
  `0 ≤ μ ≤ μ̄`" must exclude `μ̄` (`eq_19_55_fails_at_mubar`).
* **Exercise 19.3** (`ex_19_3`): with `i_t = 0`, the crisis system obtained from (19.48) and
  (19.53) has a unique bounded solution for every `(r_L, Ĝ_L)` iff (19.55); the solution is then
  the constant one of (19.56) and (19.60) (`ex_19_3_solution`). The recursive form of (19.48)
  is equivalent to the summed one for bounded paths (`fs_zlb_sum_form`). The proof uses the
  jump-only `2 × 2` Blanchard–Kahn results of Chapter 2 (`nk_jump2_unique`,
  `nk_jump2_nonunique`) with the trivial conditional expectation `fs_trivE`.
* (19.56)–(19.60): `eq_19_56`, `eq_19_57`, `eq_19_58` (an equivalence), `eq_19_60`; `ϑ_r > 0`,
  `ϑ_G > 1` for `μ > 0` (`eq_19_59`), and `ϑ_G = 1` at `μ = 0` (`fs_thetaG_zero`).
* The branches of (19.54): for every `Ĝ_L` there is exactly one constant crisis equilibrium, and
  `i_L = 0` iff `Ĝ_L ≤ Ĝ_c` (`eq_19_54_branches`; the book says `Ĝ_L < Ĝ_c`, but at `Ĝ_c` both
  branches give `i_L = 0`). `Ĝ_c > 0` iff `r_L` is negative enough (`fs_Gc_pos_iff`; the book
  prints `Ĝ_c > 0` as if unconditional). Above `Ĝ_c`, the solution "left as an exercise":
  `Ŷ_L = γ_yĜ_L + σ(r_L − r̄)/(1 − μ + ψ)` with `γ_y` of (19.52) at `ρ = μ` (`fs_taylor_branch`).
* Figure 19.4: `Ĝ_c ∈ (0.135, 0.137)` at the book's parameters (`fs_fig_19_4_Gc`).
* Figure 19.5: `ϑ_G` and `ϑ_r` are strictly increasing in `μ` on `[0, μ̄)` and tend to `+∞` as
  `μ ↑ μ̄` (`fs_thetaG_strictMonoOn`, `fs_thetaR_strictMonoOn`, `fs_thetaG_tendsto_atTop`,
  `fs_thetaR_tendsto_atTop`).
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- Miao, (19.53), p. 648: with `r^net_t = −ln β − Δ_t`, (19.53) is (19.50) when `Δ_t = 0`. -/
theorem eq_19_53 {β σ Yt Gt Y1 G1 it π1 Δ : ℝ} (hΔ : Δ = 0) :
    (Yt - Gt = Y1 - G1 - σ * (it - π1 - (-Real.log β - Δ))) ↔
      (Yt - Gt = Y1 - G1 - σ * (it - π1 - (-Real.log β))) := by
  rw [hΔ, sub_zero]

/-- Miao, p. 648: if `r^net < 0` the zero lower bound `i ≥ 0` is incompatible with the
zero-inflation steady state `Ŷ = π = Ĝ = 0` in (19.53) (`σ > 0`). -/
theorem fs_zlb_no_steady_state {σ i rnet : ℝ} (hσ : 0 < σ) (hr : rnet < 0) (hi : 0 ≤ i) :
    ¬ ((0 : ℝ) - 0 = 0 - 0 - σ * (i - 0 - rnet)) := by
  intro h
  have : σ * (i - rnet) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- `h(μ) = (1 − μ)(1 − βμ) − κσμ`, positive iff (19.55) (Miao, p. 650). -/
def fs_h (β κ σ μ : ℝ) : ℝ := (1 - μ) * (1 - β * μ) - κ * σ * μ

/-- `ϑ_r = σ(1 − βμ)/h(μ)` (Miao, (19.59), p. 650). -/
noncomputable def fs_thetaR (β κ σ μ : ℝ) : ℝ := σ * (1 - β * μ) / fs_h β κ σ μ

/-- `ϑ_G = ((1 − μ)(1 − βμ) − κσμΓ)/h(μ)` (Miao, (19.59), p. 650). -/
noncomputable def fs_thetaG (β κ σ μ Γ : ℝ) : ℝ :=
  ((1 - μ) * (1 - β * μ) - κ * σ * μ * Γ) / fs_h β κ σ μ

/-- Miao, p. 650: `h` is strictly decreasing on `[0, 1]` (for `0 < β < 1`, `κσ > 0`). -/
theorem fs_h_strictAntiOn {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    StrictAntiOn (fs_h β κ σ) (Set.Icc 0 1) := by
  intro a ha b hb hab
  unfold fs_h
  have : 0 < 1 + β + κ * σ - β * (a + b) := by nlinarith [ha.1, hb.2]
  nlinarith [mul_pos (sub_pos.2 hab) this]

/-- Miao, p. 650: there is a unique `μ̄ ∈ (0, 1)` with `h(μ̄) = 0`. -/
theorem fs_mubar_exists {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    ∃! μb, μb ∈ Set.Ioo (0 : ℝ) 1 ∧ fs_h β κ σ μb = 0 := by
  have hcont : ContinuousOn (fs_h β κ σ) (Set.Icc 0 1) := by
    unfold fs_h
    fun_prop
  have h0 : fs_h β κ σ 0 = 1 := by simp [fs_h]
  have h1 : fs_h β κ σ 1 = -(κ * σ) := by simp [fs_h]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont
    (show (0 : ℝ) ∈ Set.Icc (fs_h β κ σ 1) (fs_h β κ σ 0) by
      rw [h0, h1]
      constructor <;> linarith)
  have hc0' : c ≠ 0 := by
    rintro rfl
    rw [h0] at hc0
    norm_num at hc0
  have hc1' : c ≠ 1 := by
    rintro rfl
    rw [h1] at hc0
    linarith
  refine ⟨c, ⟨⟨lt_of_le_of_ne hc.1 (Ne.symm hc0'), lt_of_le_of_ne hc.2 hc1'⟩, hc0⟩, ?_⟩
  rintro d ⟨hd, hd0⟩
  exact (fs_h_strictAntiOn hβ0 hβ1 hκσ).injOn ⟨hd.1.le, hd.2.le⟩ hc (hd0.trans hc0.symm)

/-- Miao, p. 650: for `μ ∈ [0, 1]`, condition (19.55) `κσμ < (1 − μ)(1 − βμ)` holds iff
`μ < μ̄`. -/
theorem eq_19_55_iff {β κ σ μb μ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ)
    (hμb : μb ∈ Set.Ioo (0 : ℝ) 1) (hμb0 : fs_h β κ σ μb = 0) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    κ * σ * μ < (1 - μ) * (1 - β * μ) ↔ μ < μb := by
  have hanti := fs_h_strictAntiOn hβ0 hβ1 hκσ
  have hμb' : μb ∈ Set.Icc (0 : ℝ) 1 := ⟨hμb.1.le, hμb.2.le⟩
  have e : κ * σ * μ < (1 - μ) * (1 - β * μ) ↔ 0 < fs_h β κ σ μ := by
    unfold fs_h
    constructor <;> intro h <;> linarith
  rw [e, ← hμb0]
  exact hanti.lt_iff_gt hμb' hμ

/-- **Correction** (Miao, p. 650): (19.55) fails at `μ = μ̄`, so it holds for `0 ≤ μ < μ̄`, not
for all `0 ≤ μ ≤ μ̄`. -/
theorem eq_19_55_fails_at_mubar {β κ σ μb : ℝ} (hμb0 : fs_h β κ σ μb = 0) :
    ¬ κ * σ * μb < (1 - μb) * (1 - β * μb) := by
  unfold fs_h at hμb0
  intro h
  linarith

/-- Miao, (19.56), p. 650: in the crisis state (19.48) reads
`π_L = κΣⱼβʲ E(Ŷ_{t+j} − ΓĜ_{t+j})` with `E(x_{t+j}) = μʲx_L + (1 − μʲ)·0`, i.e.
`π_L = κ(Ŷ_L − ΓĜ_L)/(1 − βμ)`. -/
theorem eq_19_56 {β κ μ Γ YL gL πL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1)
    (h : πL = κ * ∑' j : ℕ, β ^ j * (μ ^ j * (YL - Γ * gL) + (1 - μ ^ j) * (0 - Γ * 0))) :
    πL = κ / (1 - β * μ) * (YL - Γ * gL) := by
  have hβμ0 : 0 ≤ β * μ := by positivity
  have hβμ1 : β * μ < 1 := by nlinarith
  have : ∀ j : ℕ, β ^ j * (μ ^ j * (YL - Γ * gL) + (1 - μ ^ j) * (0 - Γ * 0)) =
      (YL - Γ * gL) * (β * μ) ^ j := fun j => by
    rw [mul_pow]
    ring
  simp_rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβμ0 hβμ1] at h
  rw [h]
  ring

/-- Miao, (19.57), p. 650: in the crisis state (19.53) reads
`Ŷ_L − Ĝ_L = μ(Ŷ_L − Ĝ_L) + (1 − μ)(0 − 0) − σ(i_L − (μπ_L + (1 − μ)·0) − r_L)`, i.e.
`(1 − μ)(Ŷ_L − Ĝ_L) = σ(−i_L + μπ_L + r_L)`. -/
theorem eq_19_57 {μ σ YL gL iL πL rL : ℝ} :
    YL - gL = μ * (YL - gL) + (1 - μ) * (0 - 0) - σ * (iL - (μ * πL + (1 - μ) * 0) - rL) ↔
      (1 - μ) * (YL - gL) = σ * (-iL + μ * πL + rL) := by
  constructor <;> intro h <;> linarith

/-- Miao, (19.58), p. 650: when `h(μ) ≠ 0` and `βμ ≠ 1`, (19.56) and (19.57) hold iff
`Ŷ_L = ϑ_r(r_L − i_L) + ϑ_GĜ_L` and `π_L = κ(Ŷ_L − ΓĜ_L)/(1 − βμ)`. -/
theorem eq_19_58 {β κ σ μ Γ YL gL iL πL rL : ℝ} (hh : fs_h β κ σ μ ≠ 0)
    (hD : 1 - β * μ ≠ 0) :
    (πL = κ / (1 - β * μ) * (YL - Γ * gL) ∧ (1 - μ) * (YL - gL) = σ * (-iL + μ * πL + rL)) ↔
      (YL = fs_thetaR β κ σ μ * (rL - iL) + fs_thetaG β κ σ μ Γ * gL ∧
        πL = κ / (1 - β * μ) * (YL - Γ * gL)) := by
  have hc : κ / (1 - β * μ) * (1 - β * μ) = κ := div_mul_cancel₀ κ hD
  have e : ∀ Y, (Y = fs_thetaR β κ σ μ * (rL - iL) + fs_thetaG β κ σ μ Γ * gL ↔
      Y * fs_h β κ σ μ = σ * (1 - β * μ) * (rL - iL) +
        ((1 - μ) * (1 - β * μ) - κ * σ * μ * Γ) * gL) := by
    intro Y
    unfold fs_thetaR fs_thetaG
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hh]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(e YL).2 ?_, h1⟩
    rw [h1] at h2
    unfold fs_h
    linear_combination (1 - β * μ) * h2 + σ * μ * (YL - Γ * gL) * hc
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have k := (e YL).1 h1
    rw [h2]
    apply mul_left_cancel₀ hD
    unfold fs_h at k
    linear_combination k - σ * μ * (YL - Γ * gL) * hc

/-- Miao, (19.59), p. 650: under (19.55), `ϑ_r > 0`, and `ϑ_G > 1` when `μ > 0` and `Γ < 1`. -/
theorem eq_19_59 {β κ σ μ Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hΓ : Γ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    0 < fs_thetaR β κ σ μ ∧ 1 < fs_thetaG β κ σ μ Γ := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  refine ⟨div_pos (mul_pos hσ hD) hh, ?_⟩
  unfold fs_thetaG
  rw [one_lt_div hh]
  unfold fs_h
  nlinarith [mul_pos (mul_pos (mul_pos hκ hσ) hμ0) (sub_pos.2 hΓ)]

/-- Miao, p. 652: with `μ = 0` the multiplier `ϑ_G` is one. -/
theorem fs_thetaG_zero {β κ σ Γ : ℝ} : fs_thetaG β κ σ 0 Γ = 1 := by
  simp [fs_thetaG, fs_h]

/-- Miao, (19.60), p. 650: at the zero bound (`i_L = 0`), `Ŷ_L = ϑ_r r_L + ϑ_GĜ_L`. -/
theorem eq_19_60 {β κ σ μ Γ YL gL πL rL : ℝ} (hh : fs_h β κ σ μ ≠ 0) (hD : 1 - β * μ ≠ 0)
    (h56 : πL = κ / (1 - β * μ) * (YL - Γ * gL))
    (h57 : (1 - μ) * (YL - gL) = σ * (-0 + μ * πL + rL)) :
    YL = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL := by
  have := ((eq_19_58 hh hD).1 ⟨h56, h57⟩).1
  rw [this, sub_zero]

/-- The critical level `Ĝ_c` (Miao, p. 650). -/
noncomputable def fs_Gc (β κ σ μ Γ φπ φy rL rb : ℝ) : ℝ :=
  (-(κ * φπ / (1 - β * μ) + φy) * fs_thetaR β κ σ μ * rL - rb) /
    (κ * φπ / (1 - β * μ) * (fs_thetaG β κ σ μ Γ - Γ) + φy * fs_thetaG β κ σ μ Γ)

/-- The two branches of (19.54) (Miao, pp. 649–651). Under (19.55) (with `0 ≤ μ < 1`,
`Γ < 1`, `φ_π > 0`, `φ_y ≥ 0`), for every `Ĝ_L` there is exactly one constant crisis
equilibrium `(i_L, Ŷ_L, π_L)` of (19.56), (19.57) and `i_L = max(r̄ + φ_ππ_L + φ_yŶ_L, 0)`; and
the zero bound binds, `i_L = 0`, iff `Ĝ_L ≤ Ĝ_c`. -/
theorem eq_19_54_branches {β κ σ μ Γ φπ φy rL rb gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hΓ : Γ < 1)
    (hφπ : 0 < φπ) (hφy : 0 ≤ φy) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    (∃! x : ℝ × ℝ × ℝ, x.2.2 = κ / (1 - β * μ) * (x.2.1 - Γ * gL) ∧
        (1 - μ) * (x.2.1 - gL) = σ * (-x.1 + μ * x.2.2 + rL) ∧
        x.1 = max (rb + φπ * x.2.2 + φy * x.2.1) 0) ∧
      ∀ x : ℝ × ℝ × ℝ, x.2.2 = κ / (1 - β * μ) * (x.2.1 - Γ * gL) →
        (1 - μ) * (x.2.1 - gL) = σ * (-x.1 + μ * x.2.2 + rL) →
        x.1 = max (rb + φπ * x.2.2 + φy * x.2.1) 0 →
        (x.1 = 0 ↔ gL ≤ fs_Gc β κ σ μ Γ φπ φy rL rb) := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  set tr := fs_thetaR β κ σ μ
  set tg := fs_thetaG β κ σ μ Γ
  have htr : 0 < tr := div_pos (mul_pos hσ hD) hh
  have htg : 1 ≤ tg := by
    unfold tg fs_thetaG
    rw [one_le_div hh]
    unfold fs_h
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hκ hσ).le hμ0) (sub_pos.2 hΓ).le]
  set b := κ * φπ / (1 - β * μ)
  have hb : 0 < b := div_pos (mul_pos hκ hφπ) hD
  set a := b + φy
  have ha : 0 < a := by positivity
  set Dc := b * (tg - Γ) + φy * tg
  have hDc : 0 < Dc := by nlinarith [mul_nonneg hφy (by linarith : (0 : ℝ) ≤ tg)]
  -- the Taylor value as a function of `i`, given (19.56)–(19.58)
  set sh := rb + a * tr * rL + Dc * gL
  have hred : ∀ x : ℝ × ℝ × ℝ, x.2.2 = κ / (1 - β * μ) * (x.2.1 - Γ * gL) →
      (1 - μ) * (x.2.1 - gL) = σ * (-x.1 + μ * x.2.2 + rL) →
      x.2.1 = tr * (rL - x.1) + tg * gL ∧
        rb + φπ * x.2.2 + φy * x.2.1 = sh - a * tr * x.1 := by
    intro x h1 h2
    have hY := ((eq_19_58 hh.ne' hD.ne').1 ⟨h1, h2⟩).1
    refine ⟨hY, ?_⟩
    rw [h1, hY]
    unfold sh Dc a b
    field_simp
    ring
  have hGc : gL ≤ fs_Gc β κ σ μ Γ φπ φy rL rb ↔ sh ≤ 0 := by
    unfold fs_Gc
    change gL ≤ (-(b + φy) * tr * rL - rb) / Dc ↔ sh ≤ 0
    rw [le_div_iff₀ hDc]
    unfold sh
    constructor <;> intro h <;> nlinarith
  -- the candidate
  set i0 := max (sh / (1 + a * tr)) 0
  have hden : 0 < 1 + a * tr := by positivity
  have hi0 : i0 = max (sh - a * tr * i0) 0 := by
    unfold i0
    rcases le_or_gt sh 0 with hs | hs
    · have : sh / (1 + a * tr) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs hden.le
      rw [max_eq_right this]
      simp [hs]
    · have hpos : 0 < sh / (1 + a * tr) := div_pos hs hden
      rw [max_eq_left hpos.le]
      have : sh - a * tr * (sh / (1 + a * tr)) = sh / (1 + a * tr) := by
        field_simp
        ring
      rw [this, max_eq_left hpos.le]
  have huniq_i : ∀ i, i = max (sh - a * tr * i) 0 → i = i0 := by
    intro i hi
    have hi0' := hi0
    rcases le_or_gt sh 0 with hs | hs
    · have hin : 0 ≤ i := hi ▸ le_max_right _ _
      have : sh - a * tr * i ≤ 0 := by nlinarith [mul_nonneg (mul_pos ha htr).le hin]
      rw [max_eq_right this] at hi
      have : sh - a * tr * i0 ≤ 0 := by
        have hin0 : 0 ≤ i0 := le_max_right _ _
        nlinarith [mul_nonneg (mul_pos ha htr).le hin0]
      rw [max_eq_right this] at hi0'
      rw [hi, hi0']
    · rcases le_or_gt (sh - a * tr * i) 0 with h1 | h1
      · rw [max_eq_right h1] at hi
        rw [hi] at h1
        linarith
      · rw [max_eq_left h1.le] at hi
        unfold i0
        have hpos : 0 < sh / (1 + a * tr) := div_pos hs hden
        rw [max_eq_left hpos.le, eq_div_iff hden.ne']
        linarith
  have hshz : i0 = 0 ↔ sh ≤ 0 := by
    unfold i0
    constructor
    · intro h
      by_contra hs
      push Not at hs
      have hpos : 0 < sh / (1 + a * tr) := div_pos hs hden
      rw [max_eq_left hpos.le] at h
      linarith
    · intro hs
      exact max_eq_right (div_nonpos_of_nonpos_of_nonneg hs hden.le)
  refine ⟨⟨(i0, tr * (rL - i0) + tg * gL,
      κ / (1 - β * μ) * (tr * (rL - i0) + tg * gL - Γ * gL)), ?_, ?_⟩, ?_⟩
  · have hpair := (eq_19_58 (Γ := Γ) (gL := gL) (rL := rL) (iL := i0)
      (YL := tr * (rL - i0) + tg * gL)
      (πL := κ / (1 - β * μ) * (tr * (rL - i0) + tg * gL - Γ * gL)) hh.ne' hD.ne').2
      ⟨rfl, rfl⟩
    refine ⟨hpair.1, hpair.2, ?_⟩
    have := (hred (i0, tr * (rL - i0) + tg * gL,
      κ / (1 - β * μ) * (tr * (rL - i0) + tg * gL - Γ * gL)) hpair.1 hpair.2).2
    simp only at this ⊢
    rw [this]
    exact hi0
  · rintro ⟨i, Y, p⟩ ⟨h1, h2, h3⟩
    obtain ⟨hY, hT⟩ := hred (i, Y, p) h1 h2
    simp only at hY hT h1 h3 ⊢
    rw [hT] at h3
    have hi := huniq_i i h3
    subst hi
    rw [h1, hY]
  · rintro ⟨i, Y, p⟩ h1 h2 h3
    obtain ⟨-, hT⟩ := hred (i, Y, p) h1 h2
    simp only at hT h3 ⊢
    rw [hT] at h3
    rw [huniq_i i h3, hshz, hGc]

/-- Miao, p. 650: `Ĝ_c > 0` iff `r_L < −r̄/((κφ_π/(1 − βμ) + φ_y)ϑ_r)`: the zero bound binds at
`Ĝ_L = 0` only if the shock `r_L` is negative enough (the book prints `Ĝ_c > 0` as if it held
always). -/
theorem fs_Gc_pos_iff {β κ σ μ Γ φπ φy rL rb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hΓ : Γ < 1)
    (hφπ : 0 < φπ) (hφy : 0 ≤ φy) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    0 < fs_Gc β κ σ μ Γ φπ φy rL rb ↔
      rL < -rb / ((κ * φπ / (1 - β * μ) + φy) * fs_thetaR β κ σ μ) := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  have htr : 0 < fs_thetaR β κ σ μ := div_pos (mul_pos hσ hD) hh
  have htg : 1 ≤ fs_thetaG β κ σ μ Γ := by
    unfold fs_thetaG
    rw [one_le_div hh]
    unfold fs_h
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hκ hσ).le hμ0) (sub_pos.2 hΓ).le]
  have hb : 0 < κ * φπ / (1 - β * μ) := div_pos (mul_pos hκ hφπ) hD
  have hDc : 0 < κ * φπ / (1 - β * μ) * (fs_thetaG β κ σ μ Γ - Γ) +
      φy * fs_thetaG β κ σ μ Γ := by
    nlinarith [mul_nonneg hφy (by linarith : (0 : ℝ) ≤ fs_thetaG β κ σ μ Γ)]
  have hA : 0 < (κ * φπ / (1 - β * μ) + φy) * fs_thetaR β κ σ μ := by positivity
  unfold fs_Gc
  rw [div_pos_iff_of_pos_right hDc, lt_div_iff₀ hA]
  constructor <;> intro h <;> linarith

/-- Miao, p. 651, the branch "left as an exercise": if the zero bound does not bind,
(19.56), (19.57) and `i_L = r̄ + φ_ππ_L + φ_yŶ_L` give
`Ŷ_L = γ_yĜ_L + σ(r_L − r̄)/(1 − μ + ψ)`, with `γ_y` and `ψ` of (19.52) at `ρ = μ`: the
multiplier above `Ĝ_c` is `γ_y` (p. 652). -/
theorem fs_taylor_branch {β κ σ μ Γ φπ φy rL rb YL gL πL iL : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hμ1 : μ < 1) (hφπ : 1 < φπ) (hφy : 0 ≤ φy)
    (h56 : πL = κ / (1 - β * μ) * (YL - Γ * gL))
    (h57 : (1 - μ) * (YL - gL) = σ * (-iL + μ * πL + rL))
    (hT : iL = rb + φπ * πL + φy * YL) :
    YL = fs_gammaY σ φy κ φπ β μ Γ * gL + σ * (rL - rb) / (1 - μ + fs_psi σ φy κ φπ β μ) := by
  obtain ⟨-, hψ⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hμ1 hφπ
  have hψd : 0 < 1 - μ + fs_psi σ φy κ φπ β μ := by linarith
  have key : YL * (1 - μ + fs_psi σ φy κ φπ β μ) =
      (1 - μ + (fs_psi σ φy κ φπ β μ - σ * φy) * Γ) * gL + σ * (rL - rb) := by
    rw [hT, h56] at h57
    unfold fs_psi
    linear_combination h57
  unfold fs_gammaY
  field_simp
  linear_combination key

/-- Miao, Figure 19.5, p. 653: `ϑ_G` is strictly increasing in `μ` on `[0, μ̄)` (where
`h > 0`), for `Γ < 1`. -/
theorem fs_thetaG_strictMonoOn {β κ σ Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ)
    (hΓ : Γ < 1) :
    StrictMonoOn (fun μ => fs_thetaG β κ σ μ Γ) {μ | 0 ≤ μ ∧ μ ≤ 1 ∧ 0 < fs_h β κ σ μ} := by
  intro a ⟨ha0, ha1, hha⟩ b ⟨hb0, hb1, hhb⟩ hab
  have hanti := fs_h_strictAntiOn hβ0 hβ1 hκσ ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hab
  have e : ∀ μ, 0 < fs_h β κ σ μ →
      fs_thetaG β κ σ μ Γ = 1 + κ * σ * (1 - Γ) * μ / fs_h β κ σ μ := fun μ hμ => by
    unfold fs_thetaG
    field_simp
    unfold fs_h
    ring
  simp only
  rw [e a hha, e b hhb]
  have hc : 0 < κ * σ * (1 - Γ) := mul_pos hκσ (by linarith)
  rw [add_lt_add_iff_left, div_lt_div_iff₀ hha hhb]
  nlinarith [mul_le_mul_of_nonneg_left hanti.le ha0, mul_lt_mul_of_pos_right hab hha]

/-- Miao, Figure 19.5, p. 653: `ϑ_r` is strictly increasing in `μ` on `[0, μ̄)`. -/
theorem fs_thetaR_strictMonoOn {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) :
    StrictMonoOn (fun μ => fs_thetaR β κ σ μ) {μ | 0 ≤ μ ∧ μ ≤ 1 ∧ 0 < fs_h β κ σ μ} := by
  intro a ⟨ha0, ha1, hha⟩ b ⟨hb0, hb1, hhb⟩ hab
  simp only
  unfold fs_thetaR
  rw [div_lt_div_iff₀ hha hhb]
  have hDa : 0 < 1 - β * a := by nlinarith
  have hDb : 0 < 1 - β * b := by nlinarith
  have e : σ * (1 - β * a) * fs_h β κ σ b - σ * (1 - β * b) * fs_h β κ σ a =
      -σ * (b - a) * ((1 - β * a) * (1 - β * b) + κ * σ) := by
    unfold fs_h
    ring
  have : 0 < σ * (b - a) * ((1 - β * a) * (1 - β * b) + κ * σ) := by
    have := mul_pos hDa hDb
    have := mul_pos hκ hσ
    have := sub_pos.2 hab
    positivity
  linarith

/-- Miao, p. 654: the multiplier `ϑ_G` "increases without bound as `μ` approaches `μ̄`". -/
theorem fs_thetaG_tendsto_atTop {β κ σ Γ μb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκσ : 0 < κ * σ) (hΓ : Γ < 1) (hμb : μb ∈ Set.Ioo (0 : ℝ) 1)
    (hμb0 : fs_h β κ σ μb = 0) :
    Tendsto (fun μ => fs_thetaG β κ σ μ Γ) (𝓝[<] μb) atTop := by
  have hcont : Continuous (fs_h β κ σ) := by unfold fs_h; fun_prop
  have hpos : ∀ᶠ μ in 𝓝[<] μb, 0 < fs_h β κ σ μ := by
    have hI : Set.Ioo (0 : ℝ) μb ∈ 𝓝[<] μb := Ioo_mem_nhdsLT hμb.1
    filter_upwards [hI] with μ hμ
    rw [← hμb0]
    exact fs_h_strictAntiOn hβ0 hβ1 hκσ ⟨hμ.1.le, (hμ.2.trans hμb.2).le⟩
      ⟨hμb.1.le, hμb.2.le⟩ hμ.2
  have hh : Tendsto (fs_h β κ σ) (𝓝[<] μb) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hpos⟩
    have := hcont.tendsto μb
    rw [hμb0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinv := tendsto_inv_nhdsGT_zero.comp hh
  have hnum : Tendsto (fun μ => κ * σ * (1 - Γ) * μ) (𝓝[<] μb) (𝓝 (κ * σ * (1 - Γ) * μb)) :=
    ((continuous_const.mul continuous_id).tendsto μb).mono_left nhdsWithin_le_nhds
  have hc : 0 < κ * σ * (1 - Γ) * μb := mul_pos (mul_pos hκσ (by linarith)) hμb.1
  have hprod := hnum.pos_mul_atTop hc hinv
  have hsum := tendsto_atTop_add_const_left (𝓝[<] μb) 1 hprod
  refine hsum.congr' ?_
  filter_upwards [hpos] with μ hμ
  simp only [Function.comp_apply]
  unfold fs_thetaG
  field_simp
  unfold fs_h
  ring

/-- Miao, p. 654 and Figure 19.5: `ϑ_r = dY_L/dr_L` also tends to `+∞` as `μ ↑ μ̄`. -/
theorem fs_thetaR_tendsto_atTop {β κ σ μb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hμb : μb ∈ Set.Ioo (0 : ℝ) 1) (hμb0 : fs_h β κ σ μb = 0) :
    Tendsto (fun μ => fs_thetaR β κ σ μ) (𝓝[<] μb) atTop := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hcont : Continuous (fs_h β κ σ) := by unfold fs_h; fun_prop
  have hpos : ∀ᶠ μ in 𝓝[<] μb, 0 < fs_h β κ σ μ := by
    have hI : Set.Ioo (0 : ℝ) μb ∈ 𝓝[<] μb := Ioo_mem_nhdsLT hμb.1
    filter_upwards [hI] with μ hμ
    rw [← hμb0]
    exact fs_h_strictAntiOn hβ0 hβ1 hκσ ⟨hμ.1.le, (hμ.2.trans hμb.2).le⟩
      ⟨hμb.1.le, hμb.2.le⟩ hμ.2
  have hh : Tendsto (fs_h β κ σ) (𝓝[<] μb) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hpos⟩
    have := hcont.tendsto μb
    rw [hμb0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinv := tendsto_inv_nhdsGT_zero.comp hh
  have hnum : Tendsto (fun μ => σ * (1 - β * μ)) (𝓝[<] μb) (𝓝 (σ * (1 - β * μb))) := by
    have : Continuous (fun μ : ℝ => σ * (1 - β * μ)) := by fun_prop
    exact (this.tendsto μb).mono_left nhdsWithin_le_nhds
  have hc : 0 < σ * (1 - β * μb) := mul_pos hσ (by nlinarith [hμb.2])
  refine (hnum.pos_mul_atTop hc hinv).congr' ?_
  filter_upwards [hpos] with μ _
  simp only [Function.comp_apply]
  unfold fs_thetaR
  rw [div_eq_mul_inv]

/-- Miao, p. 652 (Figure 19.4): at `β = 0.997` (`r̄ = −ln β`), `κ = 0.00859`, `σ = 0.862`,
`Γ = 0.425`, `φ_π = 1.5`, `φ_y = 0.25`, `r_L = −0.0104`, `μ = 0.903`, the kink is at
`Ĝ_c ∈ (0.135, 0.137)` (the book: `0.136`). -/
theorem fs_fig_19_4_Gc :
    (0.135 : ℝ) < fs_Gc 0.997 0.00859 0.862 0.903 0.425 1.5 0.25 (-0.0104) (-Real.log 0.997) ∧
      fs_Gc 0.997 0.00859 0.862 0.903 0.425 1.5 0.25 (-0.0104) (-Real.log 0.997) < 0.137 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 0.997 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.997 by norm_num)
  set r := -Real.log 0.997
  have hr1 : 0.003 ≤ r := by unfold r; norm_num at h1 ⊢; linarith
  have hr2 : r ≤ 0.00301 := by unfold r; norm_num at h2 ⊢; linarith
  unfold fs_Gc fs_thetaR fs_thetaG fs_h
  norm_num
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-- The crisis system of Exercise 19.3 with `i_t = 0` (Miao, p. 669): the recursive form of
(19.48), `π_t = κ(Ŷ_t − ΓĜ_L) + βμπ_{t+1}`, and (19.53),
`Ŷ_t − Ĝ_L = μ(Ŷ_{t+1} − Ĝ_L) − σ(0 − μπ_{t+1} − r_L)` (next-period normal-state values are
zero). -/
def fs_zlbSys (β κ σ μ Γ rL gL : ℝ) (Y p : ℕ → ℝ) : Prop :=
  ∀ t, p t = κ * (Y t - Γ * gL) + β * μ * p (t + 1) ∧
    Y t - gL = μ * (Y (t + 1) - gL) - σ * (0 - μ * p (t + 1) - rL)

/-- Miao, (19.48) in the crisis state: for bounded `Ŷ`, a bounded `π` satisfies the recursive
Phillips curve iff `π_t = κΣⱼ(βμ)ʲ(Ŷ_{t+j} − ΓĜ_L)`. -/
theorem fs_zlb_sum_form {β κ μ Γ gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1) {Y p : ℕ → ℝ} (hY : fs_Bdd Y) :
    (fs_Bdd p ∧ ∀ t, p t = κ * (Y t - Γ * gL) + β * μ * p (t + 1)) ↔
      ∀ t, p t = ∑' j, (β * μ) ^ j * (κ * (Y (t + j) - Γ * gL)) := by
  have ha : |β * μ| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  obtain ⟨B, hB⟩ := hY
  have hx : fs_Bdd (fun t => κ * (Y t - Γ * gL)) := by
    refine ⟨|κ| * (B + |Γ * gL|), fun t => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hB t) le_rfl))
      (abs_nonneg _)
  constructor
  · rintro ⟨hp, hrec⟩ t
    exact (fs_forward_hasSum ha hp hx (fun t => by rw [hrec t]; ring) t).tsum_eq.symm
  · intro h
    obtain ⟨hb, hr⟩ := fs_forward_exists ha hx
    have hpe : p = fun t => ∑' j, (β * μ) ^ j * (κ * (Y (t + j) - Γ * gL)) := funext h
    rw [hpe]
    refine ⟨hb, fun t => ?_⟩
    beta_reduce
    rw [hr t]
    ring

/-- The trivial (deterministic) conditional expectation `E_t = id` on `ℝ`. -/
def fs_trivE : CondExpSystem ℝ ℝ where
  E _ := ContinuousLinearMap.id ℝ ℝ
  norm_le _ := ContinuousLinearMap.norm_id_le
  tower_le _ _ _ := ContinuousLinearMap.id_comp _
  tower_ge _ _ _ := ContinuousLinearMap.id_comp _

/-- The forward matrix `A⁻¹` of the homogeneous crisis system: `X_{t+1} = A⁻¹X_t` with
`X = (Ŷ, π)`. -/
noncomputable def fs_zlbM (β κ σ μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(κ * σ + β) / (μ * β), -σ / (μ * β); -κ / (μ * β), 1 / (μ * β)]

/-- The homogeneous crisis system is the forward system `X_{t+1} = A⁻¹X_t` (`μ, β > 0`). -/
theorem fs_zlb_hom_iff {β κ σ μ : ℝ} (hβ : 0 < β) (hμ : 0 < μ) (Y p : ℕ → ℝ) (t : ℕ) :
    (p t = κ * Y t + β * μ * p (t + 1) ∧ Y t = μ * Y (t + 1) + σ * μ * p (t + 1)) ↔
      Evec fs_trivE t (![Y (t + 1), p (t + 1)]) =
        matAct (fs_zlbM β κ σ μ) ![Y t, p t] + 0 := by
  have hev : Evec fs_trivE t (![Y (t + 1), p (t + 1)]) = ![Y (t + 1), p (t + 1)] := rfl
  rw [hev, add_zero]
  have hμβ : μ * β ≠ 0 := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · simp [matAct, fs_zlbM, Fin.sum_univ_two]
      field_simp
      linear_combination -(β * h2) + σ * h1
    · simp [matAct, fs_zlbM, Fin.sum_univ_two]
      field_simp
      linear_combination -h1
  · intro h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp [matAct, fs_zlbM, Fin.sum_univ_two] at e0 e1
    field_simp at e0 e1
    constructor
    · linear_combination -e1
    · have hb : β * (Y t - (μ * Y (t + 1) + σ * μ * p (t + 1))) = β * 0 := by
        linear_combination -e0 - σ * e1
      exact sub_eq_zero.1 (mul_left_cancel₀ hβ.ne' hb)

/-- The trace and determinant of `fs_zlbM`: `(κσ + β + 1)/(μβ)` and `1/(μ²β)`; and
`1 − tr + det = h(μ)/(μ²β)`. -/
theorem fs_zlbM_tr_det {β κ σ μ : ℝ} (hβ : 0 < β) (hμ : 0 < μ) :
    fs_zlbM β κ σ μ 0 0 + fs_zlbM β κ σ μ 1 1 = (κ * σ + β + 1) / (μ * β) ∧
      fs_zlbM β κ σ μ 0 0 * fs_zlbM β κ σ μ 1 1 - fs_zlbM β κ σ μ 0 1 * fs_zlbM β κ σ μ 1 0 =
        1 / (μ ^ 2 * β) ∧
      1 - (κ * σ + β + 1) / (μ * β) + 1 / (μ ^ 2 * β) = fs_h β κ σ μ / (μ ^ 2 * β) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [fs_zlbM]
    field_simp
  · simp [fs_zlbM]
    field_simp
    ring
  · unfold fs_h
    field_simp
    ring

/-- **Exercise 19.3** (Miao, p. 669), (19.55) (p. 650). With `i_t = 0`, the crisis-state
equilibrium conditions (19.48) and (19.53) (`fs_zlbSys`) have a unique bounded solution
`(Ŷ_t, π_t)` for every `(r_L, Ĝ_L)` iff `κσμ < (1 − μ)(1 − βμ)`
(for `0 < β < 1`, `κ, σ > 0`, `0 ≤ μ < 1`). -/
theorem ex_19_3 {β κ σ μ Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    (∀ rL gL : ℝ, ∃! YP : (ℕ → ℝ) × (ℕ → ℝ),
        fs_Bdd YP.1 ∧ fs_Bdd YP.2 ∧ fs_zlbSys β κ σ μ Γ rL gL YP.1 YP.2) ↔
      κ * σ * μ < (1 - μ) * (1 - β * μ) := by
  -- bounded homogeneous solutions
  have hhom : ∀ rL gL (Y p Y' p' : ℕ → ℝ), fs_zlbSys β κ σ μ Γ rL gL Y p →
      fs_zlbSys β κ σ μ Γ rL gL Y' p' → ∀ t,
        (p t - p' t = κ * (Y t - Y' t) + β * μ * (p (t + 1) - p' (t + 1)) ∧
          Y t - Y' t = μ * (Y (t + 1) - Y' (t + 1)) + σ * μ * (p (t + 1) - p' (t + 1))) := by
    intro rL gL Y p Y' p' h h' t
    obtain ⟨a1, a2⟩ := h t
    obtain ⟨b1, b2⟩ := h' t
    constructor
    · linear_combination a1 - b1
    · linear_combination a2 - b2
  have hstab : ∀ x : ℕ → ℝ, fs_Bdd x → ∃ B, 0 < B ∧ ∀ t, |x t| < B := by
    rintro x ⟨B, hB⟩
    exact ⟨|B| + 1, by positivity, fun t => (hB t).trans_lt (by linarith [le_abs_self B])⟩
  have hsubB : ∀ x y : ℕ → ℝ, fs_Bdd x → fs_Bdd y → fs_Bdd (fun t => x t - y t) := by
    rintro x y ⟨B, hB⟩ ⟨C, hC⟩
    exact ⟨B + C, fun t => (abs_sub _ _).trans (add_le_add (hB t) (hC t))⟩
  constructor
  · intro h
    by_contra hc
    push Not at hc
    -- `μ > 0`, since (19.55) holds at `μ = 0`
    have hμ : 0 < μ := by
      rcases hμ0.lt_or_eq with h0 | h0
      · exact h0
      · subst h0
        norm_num at hc
    have hμβ : 0 < μ * β := by positivity
    set M := fs_zlbM β κ σ μ
    have hM10 : M 1 0 ≠ 0 := by
      have e : M 1 0 = -κ / (μ * β) := rfl
      rw [e]
      exact div_ne_zero (neg_ne_zero.2 hκ.ne') hμβ.ne'
    obtain ⟨eT, eD, e1⟩ := fs_zlbM_tr_det (κ := κ) (σ := σ) hβ0 hμ
    have hT : 4 ≤ (M 0 0 + M 1 1) ^ 2 := by
      rw [eT]
      have h2 : 2 ≤ (κ * σ + β + 1) / (μ * β) := by
        rw [le_div_iff₀ hμβ]
        nlinarith [mul_pos hκ hσ, mul_le_mul_of_nonneg_right hμ1.le hβ0.le]
      nlinarith
    have hnb : ¬ nkBothOut (M 0 0 + M 1 1) (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
      rw [eT, eD]
      have hD0 : 0 < 1 / (μ ^ 2 * β) := by positivity
      rintro (⟨-, h2, -⟩ | ⟨h1, -, -⟩)
      · rw [e1] at h2
        have hhn : fs_h β κ σ μ ≤ 0 := by unfold fs_h; linarith
        have : fs_h β κ σ μ / (μ ^ 2 * β) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hhn (by positivity)
        linarith
      · linarith
    obtain ⟨X, hX0, hXe, -, ⟨B, -, hXB⟩⟩ := nk_jump2_nonunique fs_trivE M hM10 hT hnb
      (w := (1 : ℝ)) one_ne_zero rfl
    obtain ⟨YP, -, hYP⟩ := h 0 0
    have hsol : ∀ Y p : ℕ → ℝ, (∀ t, p t = κ * Y t + β * μ * p (t + 1) ∧
        Y t = μ * Y (t + 1) + σ * μ * p (t + 1)) → fs_zlbSys β κ σ μ Γ 0 0 Y p := by
      intro Y p hYp t
      obtain ⟨a, b⟩ := hYp t
      constructor
      · linear_combination a
      · linear_combination b
    have hXsol : ∀ t, X t 1 = κ * X t 0 + β * μ * X (t + 1) 1 ∧
        X t 0 = μ * X (t + 1) 0 + σ * μ * X (t + 1) 1 := by
      intro t
      have hx : ∀ s, X s = ![X s 0, X s 1] := fun s => by
        funext i
        fin_cases i <;> rfl
      have := hXe t
      rw [hx t, hx (t + 1), ← add_zero (matAct M _)] at this
      exact (fs_zlb_hom_iff hβ0 hμ (fun s => X s 0) (fun s => X s 1) t).2 this
    have hXbdd : ∀ i, fs_Bdd (fun t => X t i) := fun i => ⟨B, fun t => (hXB t i).le⟩
    have e1 := hYP (fun t => X t 0, fun t => X t 1) ⟨hXbdd 0, hXbdd 1, hsol _ _ hXsol⟩
    have e2 := hYP (fun _ => 0, fun _ => 0) ⟨⟨0, fun _ => by simp⟩, ⟨0, fun _ => by simp⟩,
      hsol _ _ (fun _ => by simp)⟩
    apply hX0
    funext t i
    have := congrArg (fun q => (q.1 t, q.2 t)) (e1.trans e2.symm)
    simp only [Prod.mk.injEq] at this
    fin_cases i
    · exact this.1
    · exact this.2
  · intro h55 rL gL
    have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
    have hD : 0 < 1 - β * μ := by nlinarith
    set YL := fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL
    set πL := κ / (1 - β * μ) * (YL - Γ * gL)
    have hpair := (eq_19_58 (Γ := Γ) (gL := gL) (rL := rL) (iL := 0) (YL := YL) (πL := πL)
      hh.ne' hD.ne').2 ⟨by rw [sub_zero], rfl⟩
    refine ⟨(fun _ => YL, fun _ => πL), ⟨⟨|YL|, fun _ => le_rfl⟩, ⟨|πL|, fun _ => le_rfl⟩,
      fun t => ⟨?_, ?_⟩⟩, ?_⟩
    · simp only
      rw [hpair.1]
      field_simp
      ring
    · simp only
      linear_combination hpair.2
    · rintro ⟨Y, p⟩ ⟨hYb, hpb, hsys⟩
      have hsys0 : fs_zlbSys β κ σ μ Γ rL gL (fun _ => YL) (fun _ => πL) := fun t => by
        constructor
        · rw [hpair.1]
          field_simp
          ring
        · linear_combination hpair.2
      have hdiff := hhom rL gL Y p _ _ hsys hsys0
      -- the difference is a bounded homogeneous solution, hence zero
      have hzero : ∀ t, Y t - YL = 0 ∧ p t - πL = 0 := by
        rcases hμ0.lt_or_eq with hμ | hμ
        · set X : ℕ → Fin 2 → ℝ := fun t => ![Y t - YL, p t - πL]
          have hXe : ∀ t, Evec fs_trivE t (X (t + 1)) = matAct (fs_zlbM β κ σ μ) (X t) + 0 :=
            fun t => (fs_zlb_hom_iff hβ0 hμ (fun s => Y s - YL) (fun s => p s - πL) t).1
              (hdiff t)
          have hM : nkBothOut (fs_zlbM β κ σ μ 0 0 + fs_zlbM β κ σ μ 1 1)
              (fs_zlbM β κ σ μ 0 0 * fs_zlbM β κ σ μ 1 1 -
                fs_zlbM β κ σ μ 0 1 * fs_zlbM β κ σ μ 1 0) := by
            obtain ⟨eT, eD, e1⟩ := fs_zlbM_tr_det (κ := κ) (σ := σ) hβ0 hμ
            rw [eT, eD]
            left
            refine ⟨?_, ?_, ?_⟩
            · rw [lt_div_iff₀ (by positivity)]
              nlinarith [mul_lt_mul_of_pos_left hμ1 hμ, mul_pos hμ hμ]
            · rw [e1]
              positivity
            · positivity
          obtain ⟨Z, -, hZu⟩ := nk_jump2_unique fs_trivE (fs_zlbM β κ σ μ) hM
            (c := fun _ => 0) ⟨1, one_pos, fun _ _ => by simp⟩ (fun _ _ => by simp)
          have hXs : IsStableProc X := by
            obtain ⟨B1, hB1, hB1'⟩ := hstab _ (hsubB Y (fun _ => YL) hYb ⟨|YL|, fun _ => le_rfl⟩)
            obtain ⟨B2, hB2, hB2'⟩ := hstab _ (hsubB p (fun _ => πL) hpb ⟨|πL|, fun _ => le_rfl⟩)
            refine ⟨B1 + B2, by positivity, fun t i => ?_⟩
            fin_cases i
            · simp only [X]
              simp
              linarith [hB1' t]
            · simp only [X]
              simp
              linarith [hB2' t]
          have hX := hZu X ⟨hXe, fun _ _ => rfl, hXs⟩
          have h0 := hZu (fun _ => 0) ⟨fun t => by
            funext i
            simp [Evec, matAct, fs_trivE], fun _ _ => rfl, ⟨1, one_pos, fun _ _ => by simp⟩⟩
          intro t
          have := congrFun (hX.trans h0.symm) t
          exact ⟨by simpa [X] using congrFun this 0, by simpa [X] using congrFun this 1⟩
        · subst hμ
          intro t
          obtain ⟨d1, d2⟩ := hdiff t
          simp only [mul_zero, zero_mul, add_zero] at d1 d2
          refine ⟨d2, ?_⟩
          rw [d1, d2, mul_zero]
      have hY : Y = fun _ => YL := funext fun t => by linarith [(hzero t).1]
      have hp : p = fun _ => πL := funext fun t => by linarith [(hzero t).2]
      rw [hY, hp]

/-- **Exercise 19.3**, the solution (Miao, pp. 650, 669): under (19.55) the unique bounded
solution is the constant one with `Ŷ_t = ϑ_r r_L + ϑ_GĜ_L` (19.60) and
`π_t = κ(Ŷ_t − ΓĜ_L)/(1 − βμ)` (19.56). -/
theorem ex_19_3_solution {β κ σ μ Γ rL gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ))
    {Y p : ℕ → ℝ} (hY : fs_Bdd Y) (hp : fs_Bdd p) (hsys : fs_zlbSys β κ σ μ Γ rL gL Y p)
    (t : ℕ) :
    Y t = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL ∧
      p t = κ / (1 - β * μ) * (Y t - Γ * gL) := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  set YL := fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL
  set πL := κ / (1 - β * μ) * (YL - Γ * gL)
  have hpair := (eq_19_58 (Γ := Γ) (gL := gL) (rL := rL) (iL := 0) (YL := YL) (πL := πL)
    hh.ne' hD.ne').2 ⟨by rw [sub_zero], rfl⟩
  have hsys0 : fs_zlbSys β κ σ μ Γ rL gL (fun _ => YL) (fun _ => πL) := fun t => by
    constructor
    · rw [hpair.1]
      field_simp
      ring
    · linear_combination hpair.2
  obtain ⟨_, -, hu⟩ := (ex_19_3 (Γ := Γ) hβ0 hβ1 hκ hσ hμ0 hμ1).2 h55 rL gL
  have e1 := hu (Y, p) ⟨hY, hp, hsys⟩
  have e2 := hu (fun _ => YL, fun _ => πL) ⟨⟨|YL|, fun _ => le_rfl⟩, ⟨|πL|, fun _ => le_rfl⟩,
    hsys0⟩
  have := e1.trans e2.symm
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]
  exact ⟨rfl, rfl⟩

end Miao.NewKeynesian
