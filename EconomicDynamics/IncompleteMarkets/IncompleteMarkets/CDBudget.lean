/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.CDUtility
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# The consumption–saving problem: budget, no-Ponzi condition, natural debt limit

Copied from `EconomicDynamics/Applications` (module `CDBudget`), namespace renamed.

Miao, §8.3, pp. 237–239.

* `cd_Budget` is the budget constraint (8.3) `c_t + a_{t+1} = Ra_t + y_t`; `cd_NoPonzi` is the
  no-Ponzi-game condition (8.5), read as `liminf_T a_{T+1}/R^T ≥ 0` (the limit need not exist).
* `eq_8_6`: the present-value budget identity (8.6). `cd_rollover`: rolling over the debt
  `a_{T+1} = R^T a_1 < 0` violates (8.5).
* `theorem_8_3_1`: with `R > 1`, labour income in `[0, y_max]`, `c ≥ 0` and `a_{t+1} ≥ −b`, the
  limit in (8.5) exists and is `≥ 0`; `theorem_8_3_1_pv`: the present value of consumption is at
  most `Ra_0` plus that of income. These are pathwise, so they hold almost surely for a
  stochastic income process.
* The converse (a.s. `a_t ≥ −y_min/r`). As printed, with only "support `[y_min, y_max]`", it is
  false: `theorem_8_3_1_converse_counterexample` (constant income `y_max`, `a_t ≡ −y_max/r`). The
  book's proof also has a gap: from "for each `n`, with positive probability `a_{t+n}/R^n <
  −ε/2`" it concludes "with positive probability `lim a_{t+n}/R^n < 0`", which needs one event for
  all `n` (for i.i.d. income the event that income stays low forever is null). We prove the
  converse, `theorem_8_3_1_converse`, under the hypothesis that from any event of positive
  probability `{a_t < −y_min/r − ε}` income stays below `y_min + δ` for `N` periods with positive
  probability (true for i.i.d. income with `y_min` in the support), by truncating at `N` and
  bounding the tail by `y_max/(rR^N)` (`cd_converse_path`).
* `cd_natural_debt_nonbinding`: if `b > y_min/r` the borrowing constraint never binds.
* `cd_IsPath`, `cd_change_of_variables` (p. 239): `â_t = a_t + b`, `x_t = Ra_t + y_t + b` give
  `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`, `c_t + â_{t+1} = x_t`, `â_{t+1} ≥ 0 ↔ a_{t+1} ≥ −b`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology MeasureTheory

/-- Miao, (8.3), p. 237: the budget constraint `c_t + a_{t+1} = Ra_t + y_t`. -/
def cd_Budget (R : ℝ) (y c a : ℕ → ℝ) : Prop := ∀ t, c t + a (t + 1) = R * a t + y t

/-- Miao, (8.5), p. 237: the no-Ponzi-game condition `lim_{T→∞} a_{T+1}/R^T ≥ 0`, read as
`liminf ≥ 0`: for every `ε > 0`, eventually `a_{T+1}/R^T ≥ −ε`. -/
def cd_NoPonzi (R : ℝ) (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ a (T + 1) / R ^ T

/-- Miao, (8.6), p. 238: `∑_{t≤T} c_t/R^t + a_{T+1}/R^T = Ra_0 + ∑_{t≤T} y_t/R^t`. -/
theorem eq_8_6 {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → ℝ} (h : cd_Budget R y c a) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), c t / R ^ t + a (T + 1) / R ^ T =
      R * a 0 + ∑ t ∈ Finset.range (T + 1), y t / R ^ t := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, div_one]
    linarith [h 0]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun t => c t / R ^ t) (n + 1),
      Finset.sum_range_succ (fun t => y t / R ^ t) (n + 1)]
    have hn := h (n + 1)
    have hp : R ^ (n + 1) ≠ 0 := pow_ne_zero _ hR
    have e : c (n + 1) / R ^ (n + 1) + a (n + 1 + 1) / R ^ (n + 1) - a (n + 1) / R ^ n =
        y (n + 1) / R ^ (n + 1) := by
      rw [pow_succ]
      field_simp
      linarith
    linarith

/-- Miao, p. 238: rolling over the initial debt, `a_{T+1} = R^T a_1` with `a_1 < 0`, gives
`a_{T+1}/R^T = a_1 → a_1 < 0`, so (8.5) fails. -/
theorem cd_rollover {R : ℝ} (hR : 0 < R) {a : ℕ → ℝ} (h : ∀ T, a (T + 1) = R ^ T * a 1)
    (ha : a 1 < 0) :
    (∀ T, a (T + 1) / R ^ T = a 1) ∧ Tendsto (fun T => a (T + 1) / R ^ T) atTop (𝓝 (a 1)) ∧
      ¬ cd_NoPonzi R a := by
  have e : ∀ T, a (T + 1) / R ^ T = a 1 := fun T => by
    rw [h T]; field_simp
  refine ⟨e, ?_, ?_⟩
  · simp only [e]; exact tendsto_const_nhds
  · intro hNP
    obtain ⟨T, hT⟩ := (hNP (-a 1 / 2) (by linarith)).exists
    rw [e T] at hT
    linarith

/-- `y_t/R^t ≤ y_max ρ^t` with `ρ = R⁻¹`: the present value of bounded income is summable. -/
theorem cd_summable_pv {R ymax : ℝ} (hR : 1 < R) {y : ℕ → ℝ} (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) :
    Summable fun t => y t / R ^ t := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  refine Summable.of_nonneg_of_le (fun t => div_nonneg (hy t).1 (pow_nonneg (by linarith) _))
    (fun t => ?_) ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ymax)
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul_of_nonneg_right (hy t).2 (pow_nonneg hρ0 _)

/-- `b/R^T → 0` for `R > 1`. -/
theorem cd_tendsto_div_pow {R : ℝ} (hR : 1 < R) (b : ℝ) :
    Tendsto (fun T : ℕ => b / R ^ T) atTop (𝓝 0) := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul b
  rw [mul_zero] at this
  refine this.congr fun T => ?_
  rw [div_eq_mul_inv, inv_pow]

/-- Miao, **Theorem 8.3.1** (first part), p. 238: if `R > 1`, income lies in `[0, y_max]`,
`c_t ≥ 0` and `a_{t+1} ≥ −b` for all `t`, then `lim a_{T+1}/R^T` exists and is `≥ 0`, so the
no-Ponzi-game condition (8.5) holds. The statement is pathwise, hence holds almost surely for a
stochastic income process with support in `[0, y_max]`. -/
theorem theorem_8_3_1 {R b ymax : ℝ} (hR : 1 < R) (hb : 0 ≤ b) {y c a : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t) (hbud : cd_Budget R y c a)
    (hbor : ∀ t, -b ≤ a (t + 1)) :
    ∃ L, 0 ≤ L ∧ Tendsto (fun T => a (T + 1) / R ^ T) atTop (𝓝 L) ∧
      HasSum (fun t => c t / R ^ t) (R * a 0 + ∑' t, y t / R ^ t - L) := by
  have hR0 : (0 : ℝ) < R := by linarith
  set Hy := ∑' t, y t / R ^ t
  have hsy := cd_summable_pv hR hy
  have hy0 : ∀ t, 0 ≤ y t / R ^ t := fun t => div_nonneg (hy t).1 (pow_nonneg hR0.le _)
  have hc0 : ∀ t, 0 ≤ c t / R ^ t := fun t => div_nonneg (hc t) (pow_nonneg hR0.le _)
  set Sc : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), c t / R ^ t
  set Sy : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), y t / R ^ t
  have hSy : Tendsto Sy atTop (𝓝 Hy) :=
    hsy.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSyle : ∀ T, Sy T ≤ Hy := fun T => hsy.sum_le_tsum _ (fun t _ => hy0 t)
  have hid : ∀ T, a (T + 1) / R ^ T = R * a 0 + Sy T - Sc T := fun T => by
    have := eq_8_6 hR0.ne' hbud T
    simp only [Sy, Sc]; linarith
  have hlow : ∀ T, -b / R ^ T ≤ a (T + 1) / R ^ T := fun T =>
    div_le_div_of_nonneg_right (hbor T) (pow_nonneg hR0.le _)
  have hScmono : Monotone Sc := monotone_nat_of_le_succ fun T => by
    simp only [Sc, Finset.sum_range_succ (n := T + 1)]
    linarith [hc0 (T + 1)]
  have hRT : ∀ T, b / R ^ T ≤ b := fun T =>
    div_le_self hb (one_le_pow₀ hR.le)
  have hScle : ∀ T, Sc T ≤ R * a 0 + Hy + b := fun T => by
    have h1 := hid T
    have h2 := hlow T
    have h3 := hSyle T
    have h4 := hRT T
    rw [neg_div] at h2
    linarith
  have hbdd : BddAbove (Set.range Sc) := ⟨_, Set.forall_mem_range.2 hScle⟩
  set Lc := ⨆ T, Sc T
  have hSc : Tendsto Sc atTop (𝓝 Lc) := tendsto_atTop_ciSup hScmono hbdd
  refine ⟨R * a 0 + Hy - Lc, ?_, ?_, ?_⟩
  · have hlim : Tendsto (fun T => a (T + 1) / R ^ T) atTop (𝓝 (R * a 0 + Hy - Lc)) := by
      simp only [hid]
      exact (hSy.const_add _).sub hSc |>.congr fun T => by ring
    exact le_of_tendsto_of_tendsto' (cd_tendsto_div_pow hR (-b)) hlim hlow
  · simp only [hid]
    exact (hSy.const_add _).sub hSc |>.congr fun T => by ring
  · have e : R * a 0 + Hy - (R * a 0 + Hy - Lc) = Lc := by ring
    rw [e]
    refine (hasSum_iff_tendsto_nat_of_nonneg hc0 Lc).2 ?_
    have := hSc.comp (tendsto_sub_atTop_nat 1)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    simp only [Function.comp_apply, Sc, Nat.sub_add_cancel hT]

/-- Miao, **Theorem 8.3.1**, p. 238: the inequality `Ra_0 + ∑ y_t/R^t ≥ ∑ c_t/R^t` derived in
the proof (present value of consumption at most initial wealth plus that of income). -/
theorem theorem_8_3_1_pv {R b ymax : ℝ} (hR : 1 < R) (hb : 0 ≤ b) {y c a : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t) (hbud : cd_Budget R y c a)
    (hbor : ∀ t, -b ≤ a (t + 1)) :
    Summable (fun t => c t / R ^ t) ∧ ∑' t, c t / R ^ t ≤ R * a 0 + ∑' t, y t / R ^ t := by
  obtain ⟨L, hL, -, hs⟩ := theorem_8_3_1 hR hb hy hc hbud hbor
  exact ⟨hs.summable, by rw [hs.tsum_eq]; linarith⟩

/-- Miao, **Theorem 8.3.1**: the first part gives the no-Ponzi-game condition (8.5). -/
theorem theorem_8_3_1_noPonzi {R b ymax : ℝ} (hR : 1 < R) (hb : 0 ≤ b) {y c a : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t) (hbud : cd_Budget R y c a)
    (hbor : ∀ t, -b ≤ a (t + 1)) : cd_NoPonzi R a := by
  obtain ⟨L, hL, hlim, -⟩ := theorem_8_3_1 hR hb hy hc hbud hbor
  intro ε hε
  exact (hlim.eventually (Ioi_mem_nhds (show -ε < L by linarith))).mono fun T hT => le_of_lt hT

/-- The telescoping bound used in the proof of Theorem 8.3.1: if
`B_{k+1} ≤ B_k + Yρ^{k+1}` for `n₀ ≤ k < n₀ + m`, `ρ = R⁻¹`, `r = R − 1`, then
`B_{n₀+m} + Yρ^{n₀+m}/r ≤ B_{n₀} + Yρ^{n₀}/r`. -/
theorem cd_telescope {R Y : ℝ} (hR : 1 < R) {B : ℕ → ℝ} (n₀ m : ℕ)
    (h : ∀ k < m, B (n₀ + k + 1) ≤ B (n₀ + k) + Y * R⁻¹ ^ (n₀ + k + 1)) :
    B (n₀ + m) + Y * R⁻¹ ^ (n₀ + m) / (R - 1) ≤ B n₀ + Y * R⁻¹ ^ n₀ / (R - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep := h m (Nat.lt_succ_self m)
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hr : (0 : ℝ) < R - 1 := by linarith
    have hR0 : R ≠ 0 := by linarith
    have e : Y * R⁻¹ ^ (n₀ + m + 1) + Y * R⁻¹ ^ (n₀ + m + 1) / (R - 1) =
        Y * R⁻¹ ^ (n₀ + m) / (R - 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [← add_assoc]
    linarith

/-- The pathwise step of the proof of Theorem 8.3.1 (converse), corrected. If `c ≥ 0`, income
lies in `[y_min, y_max]` with `y_min ≥ 0`, `a_t < −y_min/r − ε`, income stays below
`y_min + rε/4` for `N` periods from `t`, and `y_max/(rR^N) ≤ ε/4`, then (8.5) fails along the
path: `a_{t+n}/R^n < −ε/2` for every `n ≥ N`. -/
theorem cd_converse_path {R ymin ymax ε : ℝ} (hR : 1 < R) (hymin : 0 ≤ ymin) (hε : 0 < ε)
    {y c a : ℕ → ℝ} (hy : ∀ t, ymin ≤ y t ∧ y t ≤ ymax) (hc : ∀ t, 0 ≤ c t)
    (hbud : cd_Budget R y c a) {t N : ℕ} (hat : a t < -ymin / (R - 1) - ε)
    (hlow : ∀ k < N, y (t + k) ≤ ymin + (R - 1) * ε / 4)
    (hN : ymax * R⁻¹ ^ N / (R - 1) ≤ ε / 4) :
    (∀ n, N ≤ n → a (t + n) / R ^ n < -ε / 2) ∧ ¬ cd_NoPonzi R a := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hr : (0 : ℝ) < R - 1 := by linarith
  have hρ0 : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.2 hR0.le
  set B : ℕ → ℝ := fun n => a (t + n) / R ^ n
  have hymax : 0 ≤ ymax := le_trans hymin ((hy 0).1.trans (hy 0).2)
  have hstep : ∀ n, B (n + 1) ≤ B n + y (t + n) * R⁻¹ ^ (n + 1) := fun n => by
    simp only [B]
    have h1 := hbud (t + n)
    have h2 := hc (t + n)
    have e : t + (n + 1) = t + n + 1 := by omega
    rw [e]
    have hp : (0 : ℝ) < R ^ n := pow_pos hR0 n
    have key : a (t + n + 1) / R ^ (n + 1) =
        a (t + n) / R ^ n + y (t + n) / R ^ (n + 1) - c (t + n) / R ^ (n + 1) := by
      rw [show a (t + n + 1) = R * a (t + n) + y (t + n) - c (t + n) by linarith, pow_succ]
      field_simp
    rw [key, inv_pow, ← div_eq_mul_inv]
    have := div_nonneg h2 (pow_pos hR0 (n + 1)).le
    linarith
  -- first `N` periods: low income
  have h1 : B (0 + N) + (ymin + (R - 1) * ε / 4) * R⁻¹ ^ (0 + N) / (R - 1) ≤
      B 0 + (ymin + (R - 1) * ε / 4) * R⁻¹ ^ 0 / (R - 1) := by
    refine cd_telescope hR 0 N fun k hk => ?_
    have h3 := hstep k
    have hy' := hlow k hk
    have : y (t + k) * R⁻¹ ^ (k + 1) ≤ (ymin + (R - 1) * ε / 4) * R⁻¹ ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hy' (pow_nonneg hρ0 _)
    simp only [zero_add]
    linarith
  -- afterwards: income at most `y_max`
  have h2 : ∀ m, B (N + m) + ymax * R⁻¹ ^ (N + m) / (R - 1) ≤
      B N + ymax * R⁻¹ ^ N / (R - 1) := fun m => by
    refine cd_telescope hR N m fun k _ => ?_
    have h3 := hstep (N + k)
    have : y (t + (N + k)) * R⁻¹ ^ (N + k + 1) ≤ ymax * R⁻¹ ^ (N + k + 1) :=
      mul_le_mul_of_nonneg_right (hy _).2 (pow_nonneg hρ0 _)
    linarith
  have hB0 : B 0 = a t := by simp [B]
  simp only [zero_add, pow_zero, mul_one] at h1
  have hlowpos : 0 ≤ (ymin + (R - 1) * ε / 4) * R⁻¹ ^ N / (R - 1) :=
    div_nonneg (mul_nonneg (by positivity) (pow_nonneg hρ0 _)) hr.le
  have hmid : (ymin + (R - 1) * ε / 4) / (R - 1) = ymin / (R - 1) + ε / 4 := by
    field_simp
  have hbound : ∀ n, N ≤ n → B n < -ε / 2 := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h3 := h2 m
    have h4 : 0 ≤ ymax * R⁻¹ ^ (N + m) / (R - 1) :=
      div_nonneg (mul_nonneg hymax (pow_nonneg hρ0 _)) hr.le
    rw [hB0, hmid] at h1
    have : -ymin / (R - 1) = -(ymin / (R - 1)) := neg_div _ _
    linarith
  refine ⟨hbound, fun hNP => ?_⟩
  -- `a_{T+1}/R^T = B_n · R/R^t` with `T + 1 = t + n`
  set η : ℝ := ε / 2 * (R / R ^ t)
  have hη : 0 < η := by positivity
  obtain ⟨T, hT, hTN⟩ := ((hNP (η / 2) (by linarith)).and (eventually_ge_atTop (t + N))).exists
  obtain ⟨n, hn⟩ : ∃ n, T + 1 = t + n := ⟨T + 1 - t, by omega⟩
  have hnN : N ≤ n := by omega
  have hrel : a (T + 1) / R ^ T = B n * (R / R ^ t) := by
    simp only [B]
    rw [hn]
    have hpow : R ^ T * R = R ^ t * R ^ n := by rw [← pow_succ, ← pow_add, hn]
    have h5 : R ^ T ≠ 0 := pow_ne_zero _ hR0.ne'
    have h6 : R ^ t ≠ 0 := pow_ne_zero _ hR0.ne'
    have h7 : R ^ n ≠ 0 := pow_ne_zero _ hR0.ne'
    field_simp
    linear_combination (-a (t + n)) * hpow
  rw [hrel] at hT
  have h8 := hbound n hnN
  have h9 : 0 < R / R ^ t := by positivity
  have : B n * (R / R ^ t) < -ε / 2 * (R / R ^ t) := mul_lt_mul_of_pos_right h8 h9
  simp only [η] at hT
  nlinarith

/-- Miao, **Theorem 8.3.1** (converse), p. 238, corrected. Let income `y_t(ω) ∈ [y_min, y_max]`,
`y_min ≥ 0`, `c ≥ 0`, the budget (8.3) hold pathwise and (8.5) hold almost surely. Suppose the
income process can stay low after any event of positive probability: whenever
`{a_t < −y_min/r − ε}` has positive probability, so does its intersection with
`{y_{t+k} ≤ y_min + δ for k < N}` (`δ > 0`, any `N`). Then `a_t ≥ −y_min/r` almost surely. -/
theorem theorem_8_3_1_converse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {R ymin ymax : ℝ} (hR : 1 < R) (hymin : 0 ≤ ymin) {y c a : ℕ → Ω → ℝ}
    (hy : ∀ t ω, ymin ≤ y t ω ∧ y t ω ≤ ymax) (hc : ∀ t ω, 0 ≤ c t ω)
    (hbud : ∀ ω, cd_Budget R (fun t => y t ω) (fun t => c t ω) (fun t => a t ω))
    (hNP : ∀ᵐ ω ∂μ, cd_NoPonzi R (fun t => a t ω))
    (hsupp : ∀ t (ε δ : ℝ) (N : ℕ), 0 < ε → 0 < δ →
      0 < μ {ω | a t ω < -ymin / (R - 1) - ε} →
      0 < μ ({ω | a t ω < -ymin / (R - 1) - ε} ∩ {ω | ∀ k < N, y (t + k) ω ≤ ymin + δ})) :
    ∀ t, ∀ᵐ ω ∂μ, -ymin / (R - 1) ≤ a t ω := by
  intro t
  have hr : (0 : ℝ) < R - 1 := by linarith
  have hρ0 : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hnull : μ {ω | ¬ cd_NoPonzi R (fun t => a t ω)} = 0 := ae_iff.1 hNP
  have hE : ∀ ε : ℝ, 0 < ε → μ {ω | a t ω < -ymin / (R - 1) - ε} = 0 := by
    intro ε hε
    by_contra hne
    have hpos : 0 < μ {ω | a t ω < -ymin / (R - 1) - ε} := pos_iff_ne_zero.2 hne
    -- choose `N` with `y_max ρ^N / r ≤ ε/4`
    have hlim : Tendsto (fun N : ℕ => |ymax| * R⁻¹ ^ N / (R - 1)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul |ymax|).div_const
        (R - 1)
      simpa using this
    obtain ⟨N, hN⟩ := (hlim.eventually (ge_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))).exists
    have hN' : ymax * R⁻¹ ^ N / (R - 1) ≤ ε / 4 := by
      refine le_trans ?_ hN
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hρ0 _)) hr.le
    have hpos' := hsupp t ε ((R - 1) * ε / 4) N hε (by positivity) hpos
    have hsub : {ω | a t ω < -ymin / (R - 1) - ε} ∩
        {ω | ∀ k < N, y (t + k) ω ≤ ymin + (R - 1) * ε / 4} ⊆
        {ω | ¬ cd_NoPonzi R (fun t => a t ω)} := by
      rintro ω ⟨h1, h2⟩
      exact (cd_converse_path hR hymin hε (fun t => hy t ω) (fun t => hc t ω) (hbud ω) h1 h2
        hN').2
    exact (measure_mono_null hsub hnull ▸ hpos').false
  rw [ae_iff]
  have hcover : {ω | ¬ -ymin / (R - 1) ≤ a t ω} ⊆
      ⋃ n : ℕ, {ω | a t ω < -ymin / (R - 1) - 1 / ((n : ℝ) + 1)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_le] at hω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hω)
    exact Set.mem_iUnion.2 ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null fun n => hE _ Nat.one_div_pos_of_nat)

/-- Miao, **Theorem 8.3.1** (converse), p. 238: counterexample to the statement as printed.
With income in `[y_min, y_max]`, `y_min < y_max`, but constant at `y_max` (so the stated
support condition alone does not exclude it), the plan `c_t = 0`, `a_t = −y_max/r` satisfies the
budget (8.3) and (8.5), yet `a_t < −y_min/r`. (A Dirac measure turns it into a stochastic
counterexample.) -/
theorem theorem_8_3_1_converse_counterexample {R ymin ymax : ℝ} (hR : 1 < R)
    (hlt : ymin < ymax) :
    ∃ y c a : ℕ → ℝ, (∀ t, ymin ≤ y t ∧ y t ≤ ymax) ∧ (∀ t, 0 ≤ c t) ∧ cd_Budget R y c a ∧
      cd_NoPonzi R a ∧ ∀ t, a t < -ymin / (R - 1) := by
  have hr : (0 : ℝ) < R - 1 := by linarith
  refine ⟨fun _ => ymax, fun _ => 0, fun _ => -ymax / (R - 1), fun _ => ⟨hlt.le, le_rfl⟩,
    fun _ => le_rfl, fun t => ?_, fun ε hε => ?_, fun t => ?_⟩
  · field_simp; ring
  · have := cd_tendsto_div_pow hR (-ymax / (R - 1))
    exact (this.eventually (Ioi_mem_nhds (show -ε < 0 by linarith))).mono fun T hT => le_of_lt hT
  · exact div_lt_div_of_pos_right (neg_lt_neg hlt) hr

/-- Miao, p. 239: if `b > y_min/r` the borrowing constraint `a_{t+1} ≥ −b` never binds: under the
hypotheses of `theorem_8_3_1_converse`, `a_{t+1} > −b` almost surely. -/
theorem cd_natural_debt_nonbinding {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {R ymin ymax b : ℝ} (hR : 1 < R) (hymin : 0 ≤ ymin) {y c a : ℕ → Ω → ℝ}
    (hy : ∀ t ω, ymin ≤ y t ω ∧ y t ω ≤ ymax) (hc : ∀ t ω, 0 ≤ c t ω)
    (hbud : ∀ ω, cd_Budget R (fun t => y t ω) (fun t => c t ω) (fun t => a t ω))
    (hNP : ∀ᵐ ω ∂μ, cd_NoPonzi R (fun t => a t ω))
    (hsupp : ∀ t (ε δ : ℝ) (N : ℕ), 0 < ε → 0 < δ →
      0 < μ {ω | a t ω < -ymin / (R - 1) - ε} →
      0 < μ ({ω | a t ω < -ymin / (R - 1) - ε} ∩ {ω | ∀ k < N, y (t + k) ω ≤ ymin + δ}))
    (hb : ymin / (R - 1) < b) : ∀ t, ∀ᵐ ω ∂μ, -b < a (t + 1) ω := by
  intro t
  filter_upwards [theorem_8_3_1_converse μ hR hymin hy hc hbud hNP hsupp (t + 1)] with ω hω
  rw [neg_div] at hω
  linarith

/-- Miao, p. 239: a consumption plan `c` and a cash-on-hand path `x` from `x₀` in the
redefined variables: `x_0 = x₀`, `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb` with `r = R − 1`. The
saving `â_{t+1}` is `x_t − c_t`. -/
def cd_IsPath (R b : ℝ) (y : ℕ → ℝ) (x₀ : ℝ) (c x : ℕ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∀ t, x (t + 1) = R * (x t - c t) + y (t + 1) - (R - 1) * b

/-- Miao, p. 239: the change of variables `â_t = a_t + b`, `x_t = Ra_t + y_t + b` turns the
budget (8.3) and the borrowing constraint `a_{t+1} ≥ −b` into `x_{t+1} = R(x_t − c_t) + y_{t+1}
− rb`, `c_t + â_{t+1} = x_t`, `â_{t+1} ≥ 0`; and `x_t ≥ y_t − rb` whenever `a_t ≥ −b`. -/
theorem cd_change_of_variables {R b : ℝ} (hR : 0 ≤ R) {y c a : ℕ → ℝ}
    (h : cd_Budget R y c a) :
    cd_IsPath R b y (R * a 0 + y 0 + b) c (fun t => R * a t + y t + b) ∧
      (∀ t, c t + (a (t + 1) + b) = R * a t + y t + b) ∧
      (∀ t, 0 ≤ a (t + 1) + b ↔ -b ≤ a (t + 1)) ∧
      ∀ t, -b ≤ a t → y t - (R - 1) * b ≤ R * a t + y t + b := by
  refine ⟨⟨rfl, fun t => ?_⟩, fun t => by linarith [h t], fun t => ?_, fun t ht => ?_⟩
  · have := h t
    linear_combination R * this
  · constructor <;> intro h' <;> linarith
  · nlinarith

end Miao.IncompleteMarkets
