/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The consolidated government budget

AKMM, §17.3.3, "Monetary-fiscal interactions", pp. 519–522. Real spending `g_t`, taxes `τ_t`,
nominal debt `B_t` (interest `i_{t−1}`), money `M_t`, price level `P_t`, real rate `r_t`,
`q_t = 1/(1 + r_t)` and the Fisher equation `1 + i_t = (1 + r_t)P_{t+1}/P_t`.

* `gb_flow_real`: (17.42) in real liabilities `b̂_t = (1 + i_{t−1})B_t/P_t`:
  `g_t + b̂_t = τ_t + q_tb̂_{t+1} + s_t`, `s_t = (M_{t+1} − M_t)/P_t`.
* `gb_iterate`: `b̂₀ = ∑_{t<T} Q_t(τ_t − g_t + s_t) + Q_Tb̂_T`, `Q_t = ∏_{s<t} q_s`.
* `eq_17_43`: if `Q_Tb̂_T → 0` (from the household's transversality condition and market
  clearing) and the sums converge, `∑ Q_t(g_t − τ_t) + b̂₀ = ∑ Q_ts_t`.
* `gb_printed_discount`: with the printed `q_{0,t} = ∏_{s=0}^{t} q_s` (17.43) fails.
* `eq_17_44`: in total liabilities `d_t = ((1 + i_{t−1})B_t + M_t)/P_t`,
  `d_t = τ_t − g_t + (M_{t+1}/P_t)i_t/(1 + i_t) + d_{t+1}/(1 + r_t)`.
* `gb_zero_rate`, `gb_zero_rate_printed`: with `i = 0` the discount factor is `1/(1 + r_t)`, not
  the printed `1/r_t`.
* `gb_stationary`: the stationary budget `ḡ + (r̄/(1 + r̄))d̄ = τ̄ + c̄f(ī)ī/(1 + ī)`.
* `gb_omo_irrelevance`: at `i = 0` any `(M̂, B̂)` with `M̂_t + B̂_t = M_t + B_t` satisfies the
  budget whenever `(M, B)` does (Wallace's irrelevance of open-market operations).
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, (17.42), p. 519: with the Fisher equation, `B_{t+1}/P_t = q_tb̂_{t+1}`, so (17.42) is
`g_t + b̂_t = τ_t + q_tb̂_{t+1} + s_t`, `b̂_t = (1 + i_{t−1})B_t/P_t`. -/
theorem gb_flow_real {g τ Bt Bt1 Mt Mt1 Pt Pt1 im1 i r : ℝ} (hPt : Pt ≠ 0) (hPt1 : Pt1 ≠ 0)
    (hr : 1 + r ≠ 0) (hF : 1 + i = (1 + r) * (Pt1 / Pt)) :
    g + (1 + im1) * Bt / Pt = τ + Bt1 / Pt + (Mt1 - Mt) / Pt ↔
      g + (1 + im1) * Bt / Pt =
        τ + 1 / (1 + r) * ((1 + i) * Bt1 / Pt1) + (Mt1 - Mt) / Pt := by
  have : 1 / (1 + r) * ((1 + i) * Bt1 / Pt1) = Bt1 / Pt := by rw [hF]; field_simp
  rw [this]

/-- AKMM, p. 520: iterating the real flow budget `b̂_t = τ_t − g_t + s_t + q_tb̂_{t+1}`
`T` times: `b̂₀ = ∑_{t<T} Q_t(τ_t − g_t + s_t) + Q_Tb̂_T`, `Q_t = ∏_{s<t} q_s`. -/
theorem gb_iterate {q x bh : ℕ → ℝ} (h : ∀ t, bh t = x t + q t * bh (t + 1)) (T : ℕ) :
    bh 0 = ∑ t ∈ Finset.range T, (∏ s ∈ Finset.range t, q s) * x t +
      (∏ s ∈ Finset.range T, q s) * bh T := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, Finset.prod_range_succ, h n]
    ring

/-- **AKMM, (17.43)**, p. 520: if the real flow budget holds at every date, the discounted
terminal liabilities vanish, `Q_Tb̂_T → 0`, and the present values converge,
`∑ Q_t(g_t − τ_t) = D` and `∑ Q_ts_t = S`, then `D + b̂₀ = S`. -/
theorem eq_17_43 {q g τ s bh : ℕ → ℝ} {D S : ℝ}
    (h : ∀ t, bh t = (τ t - g t + s t) + q t * bh (t + 1))
    (htvc : Tendsto (fun T => (∏ s ∈ Finset.range T, q s) * bh T) atTop (𝓝 0))
    (hD : HasSum (fun t => (∏ s ∈ Finset.range t, q s) * (g t - τ t)) D)
    (hS : HasSum (fun t => (∏ s ∈ Finset.range t, q s) * s t) S) : D + bh 0 = S := by
  have hsum := hS.sub hD
  have hlim : Tendsto (fun T => ∑ t ∈ Finset.range T, (∏ s ∈ Finset.range t, q s) *
      (τ t - g t + s t)) atTop (𝓝 (S - D)) := by
    refine hsum.tendsto_sum_nat.congr fun T => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have h2 : Tendsto (fun T => ∑ t ∈ Finset.range T, (∏ s ∈ Finset.range t, q s) *
      (τ t - g t + s t) + (∏ s ∈ Finset.range T, q s) * bh T) atTop (𝓝 (S - D + 0)) :=
    hlim.add htvc
  have h3 : Tendsto (fun _ : ℕ => bh 0) atTop (𝓝 (S - D + 0)) :=
    h2.congr fun T => (gb_iterate h T).symm
  have := tendsto_nhds_unique tendsto_const_nhds h3
  linarith

/-- AKMM, p. 520: the printed discount factor `q_{0,t} = ∏_{s=0}^{t} q_s` is wrong. With
`q ≡ 1/2`, `b̂₀ = 1`, `s₀ = 1` and all other terms zero the flow budget holds at every date and
(17.43) holds with `∏_{s<t}`, but the printed weights give `∑ q_{0,t}s_t = 1/2 ≠ b̂₀`. -/
theorem gb_printed_discount :
    let q : ℕ → ℝ := fun _ => 1 / 2
    let s : ℕ → ℝ := fun t => if t = 0 then 1 else 0
    let bh : ℕ → ℝ := fun t => if t = 0 then 1 else 0
    (∀ t, bh t = (0 - 0 + s t) + q t * bh (t + 1)) ∧
      HasSum (fun t => (∏ u ∈ Finset.range t, q u) * s t) 1 ∧
      HasSum (fun t => (∏ u ∈ Finset.range (t + 1), q u) * s t) (1 / 2) := by
  intro q s bh
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [bh, s]
    · simp [bh, s, ht.ne']
  · have := hasSum_ite_eq (0 : ℕ) (1 : ℝ)
    refine this.congr_fun fun t => ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [s]
    · simp [s, ht.ne']
  · have := hasSum_ite_eq (0 : ℕ) (1 / 2 : ℝ)
    refine this.congr_fun fun t => ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [s, q]
    · simp [s, ht.ne']

/-- **AKMM, (17.44)**, p. 520: with `D_t = (1 + i_{t−1})B_t + M_t`, `d_t = D_t/P_t` and the Fisher
equation, the flow budget (17.42) is
`d_t = τ_t − g_t + (M_{t+1}/P_t)(i_t/(1 + i_t)) + d_{t+1}/(1 + r_t)`. -/
theorem eq_17_44 {g τ Bt Bt1 Mt Mt1 Pt Pt1 im1 i r : ℝ} (hPt : Pt ≠ 0) (hPt1 : Pt1 ≠ 0)
    (hr : 1 + r ≠ 0) (hi : 1 + i ≠ 0) (hF : 1 + i = (1 + r) * (Pt1 / Pt)) :
    g + (1 + im1) * Bt / Pt = τ + Bt1 / Pt + (Mt1 - Mt) / Pt ↔
      ((1 + im1) * Bt + Mt) / Pt = τ - g + Mt1 / Pt * (i / (1 + i)) +
        1 / (1 + r) * (((1 + i) * Bt1 + Mt1) / Pt1) := by
  have e : 1 / (1 + r) * (((1 + i) * Bt1 + Mt1) / Pt1) + Mt1 / Pt * (i / (1 + i)) =
      Bt1 / Pt + Mt1 / Pt := by
    have hP : Pt1 / Pt = (1 + i) / (1 + r) := by rw [hF]; field_simp
    have hP' : Pt1 = Pt * ((1 + i) / (1 + r)) := by
      rw [← hP]; field_simp
    rw [hP']
    field_simp
    ring
  constructor
  · intro h
    have : ((1 + im1) * Bt + Mt) / Pt = (1 + im1) * Bt / Pt + Mt / Pt := by ring
    rw [this]
    have h' : (1 + im1) * Bt / Pt = τ - g + Bt1 / Pt + (Mt1 - Mt) / Pt := by linarith
    rw [h']
    have : (Mt1 - Mt) / Pt = Mt1 / Pt - Mt / Pt := by ring
    linarith
  · intro h
    have : ((1 + im1) * Bt + Mt) / Pt = (1 + im1) * Bt / Pt + Mt / Pt := by ring
    rw [this] at h
    have : (Mt1 - Mt) / Pt = Mt1 / Pt - Mt / Pt := by ring
    linarith

/-- AKMM, p. 522: with `i_t = i_{t−1} = 0` (17.44) reads
`(M_t + B_t)/P_t = τ_t − g_t + (1/(1 + r_t))(M_{t+1} + B_{t+1})/P_{t+1}`. -/
theorem gb_zero_rate {g τ Bt Bt1 Mt Mt1 Pt Pt1 r : ℝ} (hPt : Pt ≠ 0) (hPt1 : Pt1 ≠ 0)
    (hr : 1 + r ≠ 0) (hF : 1 + 0 = (1 + r) * (Pt1 / Pt)) :
    g + (1 + 0) * Bt / Pt = τ + Bt1 / Pt + (Mt1 - Mt) / Pt ↔
      (Mt + Bt) / Pt = τ - g + 1 / (1 + r) * ((Mt1 + Bt1) / Pt1) := by
  rw [eq_17_44 hPt hPt1 hr (by norm_num) hF]
  simp only [zero_div, mul_zero, add_zero, one_mul]
  rw [add_comm Bt Mt, add_comm Bt1 Mt1]

/-- AKMM, p. 522: the printed discount factor `1/r_t` is wrong: for `r_t > 0` and nonzero
next-period liabilities `X = (M_{t+1} + B_{t+1})/P_{t+1}`, `X/(1 + r_t) ≠ X/r_t`, so the printed
equation contradicts (17.44). -/
theorem gb_zero_rate_printed {r X : ℝ} (hr : 0 < r) (hX : X ≠ 0) :
    1 / (1 + r) * X ≠ 1 / r * X := by
  intro h
  have := mul_right_cancel₀ hX h
  rw [div_eq_div_iff (by linarith) hr.ne'] at this
  linarith

/-- AKMM, p. 521: the stationary budget. With constant `τ̄, ḡ, ī, r̄`, real liabilities `d̄` and
money demand `M_{t+1}/P_t = c̄f(ī)`, (17.44) reads `ḡ + (r̄/(1 + r̄))d̄ = τ̄ + c̄f(ī)ī/(1 + ī)`. -/
theorem gb_stationary {gb τb db rb ib cf : ℝ} (hr : 1 + rb ≠ 0) :
    db = τb - gb + cf * (ib / (1 + ib)) + 1 / (1 + rb) * db ↔
      gb + rb / (1 + rb) * db = τb + cf * (ib / (1 + ib)) := by
  have : db - 1 / (1 + rb) * db = rb / (1 + rb) * db := by field_simp; ring
  constructor <;> intro h <;> linarith

/-- AKMM, p. 522 (the irrelevance of open-market operations, Wallace 1981): at `i = 0` the
budget depends on money and bonds only through `M_t + B_t`; any sequences `(M̂, B̂)` with
`M̂_t + B̂_t = M_t + B_t` satisfy it iff `(M, B)` do. -/
theorem gb_omo_irrelevance {M B M' B' τ g r P : ℕ → ℝ} (hsum : ∀ t, M' t + B' t = M t + B t) :
    (∀ t, (M t + B t) / P t = τ t - g t + 1 / (1 + r t) * ((M (t + 1) + B (t + 1)) / P (t + 1)))
      ↔ ∀ t, (M' t + B' t) / P t =
        τ t - g t + 1 / (1 + r t) * ((M' (t + 1) + B' (t + 1)) / P (t + 1)) := by
  simp only [hsum]

end AKMM.Money
