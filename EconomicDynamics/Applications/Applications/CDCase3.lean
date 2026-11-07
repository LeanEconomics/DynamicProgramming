/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CDEuler

/-!
# Deterministic income, Case 3 (`βR = 1`): Chamberlain and Wilson

Miao, §8.3.1, Case 3, pp. 246–248, and the last paragraph of §8.3.1 (p. 249). Income `y_t` is
deterministic, possibly time-varying, with `rb ≤ y_t ≤ M`; `ρ = R⁻¹`.

* `cd3_monotone`: along an optimal plan `c_t ≤ c_{t+1}`, with `c_t < c_{t+1}` only if
  `â_{t+1} = 0` (p. 246, from (8.7)).
* `cd3_A`: the annuity value of income from period `t` on,
  `A_t = (r/R)∑_{j≥0} R^{−j}(y_{t+j} − rb)`. The book prints `A_t = r∑_{j≥1}R^{−j}(y_{t+j} − rb)`
  (`cd3_Abook`), which omits `y_t` although the text says "starting from period `t`" and the proof
  uses `∑_{j≥t} R^{t−j}A_t = ∑_{j≥t}R^{t−j}(y_j − rb)`; `cd3_Abook_counterexample` shows the
  printed formula gives the wrong limit.
* `cd3_lower`: `lim c_t ≥ A_t` for every `t` (the book's second step, with the improving
  deviation made explicit; it holds for every `β`).
* `cd3_upper`: `c_j ≤ sup_t A_t` provided the consumer is borrowing constrained at some date
  (`x_t = y_t − rb`).
* `cd3_chamberlain_wilson`: with `a₀ = −b` (`x₀ = y_0 − rb`), `lim c_t = sup_t A_t`.
  As printed (`c* = A*` for every optimal plan) the claim is false:
  `cd3_chamberlain_wilson_counterexample` (constant income, `a₀ > −b`). The book's proof of
  `c* ≤ A*` assumes, without justification, a date at which the consumer is constrained.
* `cd3_constant_income`: the book's closing paragraph: with constant income, `c_t = y + ra₀`,
  `a_{t+1} = a₀` is optimal for every `a₀ ≥ −b`.
-/

namespace Miao.Applications

open Filter Topology

/-- Miao, p. 247: the annuity value of income (net of interest on the debt limit) from period
`t` on, `A_t = (r/R)∑_{j≥0} R^{−j}(y_{t+j} − rb) = (1 − R⁻¹)∑_{j≥0} R^{−j}(y_{t+j} − rb)`. -/
noncomputable def cd3_A (R b : ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 - R⁻¹) * ∑' n, R⁻¹ ^ n * (y (t + n) - (R - 1) * b)

/-- Miao, p. 247, the formula as printed: `A_t = r∑_{j≥1} R^{−j}(y_{t+j} − rb)`. -/
noncomputable def cd3_Abook (R b : ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  (R - 1) * ∑' j, R⁻¹ ^ (j + 1) * (y (t + j + 1) - (R - 1) * b)

theorem cd3_summable {R b M : ℝ} (hR : 1 < R) {y : ℕ → ℝ}
    (hy : ∀ t, (R - 1) * b ≤ y t ∧ y t ≤ M) (t : ℕ) :
    Summable fun n => R⁻¹ ^ n * (y (t + n) - (R - 1) * b) := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hρ0 n)
    (sub_nonneg.2 (hy _).1)) (fun n => ?_)
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_right (M - (R - 1) * b))
  exact mul_le_mul_of_nonneg_left (by linarith [(hy (t + n)).2]) (pow_nonneg hρ0 n)

theorem cd3_A_bdd {R b M : ℝ} (hR : 1 < R) {y : ℕ → ℝ}
    (hy : ∀ t, (R - 1) * b ≤ y t ∧ y t ≤ M) : BddAbove (Set.range (cd3_A R b y)) := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  refine ⟨M - (R - 1) * b, Set.forall_mem_range.2 fun t => ?_⟩
  have h1 : ∑' n, R⁻¹ ^ n * (y (t + n) - (R - 1) * b) ≤
      ∑' n, R⁻¹ ^ n * (M - (R - 1) * b) :=
    Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (by linarith [(hy (t + n)).2])
      (pow_nonneg hρ0 n)) (cd3_summable hR hy t)
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_right _)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1] at h1
  unfold cd3_A
  have h2 : 0 < 1 - R⁻¹ := sub_pos.2 hρ1
  calc (1 - R⁻¹) * ∑' n, R⁻¹ ^ n * (y (t + n) - (R - 1) * b)
      ≤ (1 - R⁻¹) * ((1 - R⁻¹)⁻¹ * (M - (R - 1) * b)) := mul_le_mul_of_nonneg_left h1 h2.le
    _ = M - (R - 1) * b := by rw [← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]

/-- Miao, pp. 246–247: with `βR = 1`, (8.7) reads `u′(c_t) ≥ u′(c_{t+1})`, with equality if
`â_{t+1} > 0`: consumption is nondecreasing and rises only when the consumer is constrained. -/
theorem cd3_monotone (U : cd_Utility) {β R b : ℝ} (hβ : 0 < β) (hR : 0 < R) (hβR : β * R = 1)
    {y : ℕ → ℝ} {x₀ : ℝ} {c x : ℕ → ℝ} (h : cd_Optimal U β R b y x₀ c x) :
    Monotone c ∧ ∀ t, c t < c (t + 1) → c t = x t := by
  have hE := eq_8_7 U hβ hR h
  have hf := h.1
  have hstep : ∀ t, c t ≤ c (t + 1) := fun t => by
    have h1 := (hE t).1
    rw [hβR, one_mul] at h1
    by_contra hlt
    push Not at hlt
    exact absurd h1 (not_le.2 (U.du_anti (Set.mem_Ioi.2 (hf.2 _).1)
      (Set.mem_Ioi.2 (hf.2 _).1) hlt))
  refine ⟨monotone_nat_of_le_succ hstep, fun t hlt => ?_⟩
  by_contra hne
  have hs : c t < x t := lt_of_le_of_ne (hf.2 t).2 hne
  have heq := (hE t).2 hs
  rw [hβR, one_mul] at heq
  exact (ne_of_lt hlt) (U.cd_du_inj (hf.2 _).1 (hf.2 _).1 heq)

/-- Partial geometric sums `∑_{n≤N} ρⁿ → 1/(1 − ρ)`. -/
theorem cd3_geom_tendsto {R : ℝ} (hR : 1 < R) :
    Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n) atTop (𝓝 (1 - R⁻¹)⁻¹) := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have := (hasSum_geometric_of_lt_one hρ0 hρ1).tendsto_sum_nat
  exact this.comp (tendsto_add_atTop_nat 1)

/-- The budget from a date `t` with `x_t ≥ y_t − rb`:
`∑_{n≤N} ρⁿc_{t+n} + ρᴺâ_{t+N+1} ≥ ∑_{n≤N} ρⁿ(y_{t+n} − rb)`, with equality if `x_t = y_t − rb`. -/
theorem cd3_budget_ge {R b : ℝ} (hR : R ≠ 0) {y : ℕ → ℝ} {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_IsPath R b y x₀ c x) (t N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * c (t + n) + R⁻¹ ^ N * (x (t + N) - c (t + N)) =
      (x t - (y t - (R - 1) * b)) +
        ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * (y (t + n) - (R - 1) * b) := by
  rw [cd_budget_iter hR h t N, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, add_zero]
  have e : ∀ n ∈ Finset.range N, R⁻¹ ^ (n + 1) * (y (t + n + 1) - (R - 1) * b) =
      R⁻¹ ^ (n + 1) * (y (t + (n + 1)) - (R - 1) * b) := fun n _ => by
    rw [show t + n + 1 = t + (n + 1) by omega]
  rw [Finset.sum_congr rfl e]
  ring

/-- Miao, pp. 247–248 (`c* ≥ A*`): along an optimal plan from `x₀ ≥ y_0 − rb`, for every `t`,
`lim c_j ≥ A_t`: if `c_j ≤ C < A_t` for all `j`, saving grows like `Rᴺ` and consuming `ε` more
at one date is feasible and strictly better. This part needs no condition on `βR`. -/
theorem cd3_lower (U : cd_Utility) {β R b M : ℝ} (hβ : 0 < β) (hR : 1 < R) {y : ℕ → ℝ}
    (hy : ∀ t, (R - 1) * b ≤ y t ∧ y t ≤ M) {x₀ : ℝ} (hx₀ : y 0 - (R - 1) * b ≤ x₀)
    {c x : ℕ → ℝ} (h : cd_Optimal U β R b y x₀ c x) (t : ℕ) (C : ℝ)
    (hC : C < cd3_A R b y t) : ∃ j, C < c j := by
  by_contra hall
  push Not at hall
  have hf := h.1
  have hR0 : (0 : ℝ) < R := by linarith
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have h1ρ : 0 < 1 - R⁻¹ := sub_pos.2 hρ1
  have hC0 : 0 ≤ C := le_trans (hf.2 0).1.le (hall 0)
  -- `x_t ≥ y_t − rb`
  have hxt : y t - (R - 1) * b ≤ x t := by
    cases t with
    | zero => rw [hf.1.1]; exact hx₀
    | succ t =>
      rw [hf.1.2 t]
      have := mul_nonneg hR0.le (sub_nonneg.2 (hf.2 t).2)
      linarith
  set S := ∑' n, R⁻¹ ^ n * (y (t + n) - (R - 1) * b)
  have hSA : cd3_A R b y t = (1 - R⁻¹) * S := rfl
  have hgap : C * (1 - R⁻¹)⁻¹ < S := by
    rw [hSA] at hC
    rw [← div_eq_mul_inv, div_lt_iff₀ h1ρ]
    linarith
  set ε := (S - C * (1 - R⁻¹)⁻¹) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  -- eventually `ρᴺ â_{t+N+1} ≥ ε`
  have hYlim : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * (y (t + n) - (R - 1) * b))
      atTop (𝓝 S) := (cd3_summable hR hy t).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hYlim.eventually (Ioi_mem_nhds
    (show C * (1 - R⁻¹)⁻¹ + ε < S by simp only [ε]; linarith)))
  have hsav : ∀ N, N₀ ≤ N → ε ≤ R⁻¹ ^ N * (x (t + N) - c (t + N)) := fun N hN => by
    have hb := cd3_budget_ge hR0.ne' hf.1 t N
    have hcs : ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * c (t + n) ≤ C * (1 - R⁻¹)⁻¹ := by
      calc ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * c (t + n)
          ≤ ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * C :=
            Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hall _) (pow_nonneg hρ0 n)
        _ = C * ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ C * (1 - R⁻¹)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            rw [← tsum_geometric_of_lt_one hρ0 hρ1]
            exact (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum _
              (fun n _ => pow_nonneg hρ0 n)
    have := hN₀ N hN
    linarith
  -- the improving deviation: consume `ε` more at `τ = t + N₀`
  set τ := t + N₀
  set c' : ℕ → ℝ := fun j => c j + if j = τ then ε else 0
  set x' : ℕ → ℝ := fun j => x j - if τ < j then R ^ (j - τ) * ε else 0
  have hfe : cd_Feasible R b y x₀ c' x' := by
    refine ⟨⟨?_, fun j => ?_⟩, fun j => ⟨?_, ?_⟩⟩
    · simp [x', hf.1.1]
    · have hp := hf.1.2 j
      simp only [c', x']
      by_cases hj : τ ≤ j
      · have hj1 : τ < j + 1 := by omega
        simp only [hj1, ↓reduceIte]
        rw [show j + 1 - τ = (j - τ) + 1 by omega, pow_succ, hp]
        by_cases hj' : j = τ
        · simp only [hj', lt_irrefl, ↓reduceIte, Nat.sub_self, pow_zero]; ring
        · have : τ < j := lt_of_le_of_ne hj (Ne.symm hj')
          simp only [this, hj', ↓reduceIte]; ring
      · have hj1 : ¬ τ < j + 1 := by omega
        have hj2 : ¬ τ < j := by omega
        have hj3 : j ≠ τ := by omega
        simp only [hj1, hj2, hj3, ↓reduceIte, sub_zero, add_zero]
        exact hp
    · simp only [c']; split_ifs <;> linarith [(hf.2 j).1]
    · simp only [c', x']
      by_cases hj : τ ≤ j
      · obtain ⟨N, hN⟩ : ∃ N, j = t + N := ⟨j - t, by omega⟩
        have hNN : N₀ ≤ N := by omega
        have h1 := hsav N hNN
        have hRN : R ^ (j - τ) * ε ≤ R ^ N * ε := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR.le (by omega)) hε.le
        have h2 : R ^ N * ε ≤ x j - c j := by
          rw [hN]
          have hRpos : (0 : ℝ) < R ^ N := pow_pos hR0 N
          rw [inv_pow] at h1
          rw [← le_div_iff₀' hRpos, div_eq_inv_mul] at *
          linarith
        by_cases hj' : j = τ
        · simp only [hj', lt_irrefl, ↓reduceIte, Nat.sub_self, pow_zero, one_mul] at hRN ⊢
          rw [hj'] at h2
          linarith
        · have : τ < j := lt_of_le_of_ne hj (Ne.symm hj')
          simp only [this, hj', ↓reduceIte, add_zero]
          linarith
      · have hj2 : ¬ τ < j := by omega
        have hj3 : j ≠ τ := by omega
        simp only [hj2, hj3, ↓reduceIte, sub_zero, add_zero]
        exact (hf.2 j).2
  -- the gain
  set G := β ^ τ * (U.u (c τ + ε) - U.u (c τ))
  have hG : 0 < G := by
    have := U.cd_u_strictMono (Set.mem_Ioi.2 (hf.2 τ).1)
      (Set.mem_Ioi.2 (by linarith [(hf.2 τ).1])) (show c τ < c τ + ε by linarith)
    exact mul_pos (pow_pos hβ _) (by linarith)
  obtain ⟨T, hT, hTτ⟩ := ((h.2 c' x' hfe (G / 2) (by linarith)).and
    (eventually_ge_atTop τ)).exists
  have hpart : cd_partial U β c' T = cd_partial U β c T + G := by
    unfold cd_partial
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib,
      Finset.sum_eq_single τ]
    · simp only [c', ↓reduceIte, G]; ring
    · intro j _ hj
      simp [c', hj]
    · intro hm
      exact absurd (Finset.mem_range.2 (by omega)) hm
  rw [hpart] at hT
  linarith

/-- The contradiction behind `c* ≤ A*` (p. 247): if the consumer is constrained at `t`
(`x_t = y_t − rb`) then `c_t ≤ A_t` when consumption is nondecreasing. -/
theorem cd3_le_A_of_constrained {R b M : ℝ} (hR : 1 < R) {y : ℕ → ℝ}
    (hy : ∀ t, (R - 1) * b ≤ y t ∧ y t ≤ M) {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_Feasible R b y x₀ c x) (hmono : Monotone c) {t : ℕ}
    (ht : x t = y t - (R - 1) * b) : c t ≤ cd3_A R b y t := by
  by_contra hlt
  push Not at hlt
  have hR0 : (0 : ℝ) < R := by linarith
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have h1ρ : 0 < 1 - R⁻¹ := sub_pos.2 hρ1
  set S := ∑' n, R⁻¹ ^ n * (y (t + n) - (R - 1) * b)
  have hSA : cd3_A R b y t = (1 - R⁻¹) * S := rfl
  have hgap : S < c t * (1 - R⁻¹)⁻¹ := by
    rw [hSA] at hlt
    rw [← div_eq_mul_inv, lt_div_iff₀ h1ρ]
    linarith
  have hct : 0 < c t := (h.2 t).1
  have hlim := (cd3_geom_tendsto hR).const_mul (c t)
  obtain ⟨N, hN⟩ := (hlim.eventually (Ioi_mem_nhds hgap)).exists
  have hb := cd3_budget_ge hR0.ne' h.1 t N
  rw [ht, sub_self, zero_add] at hb
  have h1 : c t * ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n ≤
      ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * c (t + n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hmono (Nat.le_add_right t n)) (pow_nonneg hρ0 n)
  have h2 : 0 ≤ R⁻¹ ^ N * (x (t + N) - c (t + N)) :=
    mul_nonneg (pow_nonneg hρ0 N) (sub_nonneg.2 (h.2 _).2)
  have h3 : ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * (y (t + n) - (R - 1) * b) ≤ S :=
    (cd3_summable hR hy t).sum_le_tsum _ fun n _ =>
      mul_nonneg (pow_nonneg hρ0 n) (sub_nonneg.2 (hy _).1)
  linarith

/-- Miao, p. 247 (`c* ≤ A*`), corrected: if the consumer is borrowing constrained at some date
`t₀` (`x_{t₀} = y_{t₀} − rb`; at `t₀ = 0` this is `a₀ = −b`), then `c_j ≤ sup_t A_t` for all `j`
along an optimal plan. Either the consumer is constrained again at a date `t ≥ j`, or after the
last constrained date consumption is constant (Euler equation); in both cases the book's
present-value contradiction applies at a constrained date. -/
theorem cd3_upper (U : cd_Utility) {β R b M : ℝ} (hβ : 0 < β) (hR : 1 < R) (hβR : β * R = 1)
    {y : ℕ → ℝ} (hy : ∀ t, (R - 1) * b ≤ y t ∧ y t ≤ M) {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b y x₀ c x) {t₀ : ℕ} (ht₀ : x t₀ = y t₀ - (R - 1) * b) (j : ℕ) :
    c j ≤ ⨆ t, cd3_A R b y t := by
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨hmono, hrise⟩ := cd3_monotone U hβ hR0 hβR h
  have hE := eq_8_7 U hβ hR0 h
  have hf := h.1
  have hbdd := cd3_A_bdd hR hy
  -- a constrained date `t` with `c_j ≤ c_t`
  obtain ⟨t, ht, hjt⟩ : ∃ t, x t = y t - (R - 1) * b ∧ c j ≤ c t := by
    by_cases hlate : ∃ t, j ≤ t ∧ x t = y t - (R - 1) * b
    · obtain ⟨t, hjt, ht⟩ := hlate
      exact ⟨t, ht, hmono hjt⟩
    · push Not at hlate
      classical
      set t := Nat.findGreatest (fun n => x n = y n - (R - 1) * b) j
      have ht0j : t₀ < j := by
        by_contra hle; push Not at hle; exact hlate t₀ hle ht₀
      have hts : x t = y t - (R - 1) * b :=
        Nat.findGreatest_spec (P := fun n => x n = y n - (R - 1) * b) ht0j.le ht₀
      have htj : t ≤ j := Nat.findGreatest_le j
      -- after `t` the constraint never binds, so consumption is constant
      have hfree : ∀ i, t ≤ i → c i < x i := fun i hi => by
        by_contra hb
        have heq : c i = x i := le_antisymm (hf.2 i).2 (not_lt.1 hb)
        have hx1 : x (i + 1) = y (i + 1) - (R - 1) * b := by rw [hf.1.2 i, heq]; ring
        by_cases hij : i + 1 ≤ j
        · exact absurd (Nat.le_findGreatest (P := fun n => x n = y n - (R - 1) * b) hij hx1)
            (by omega)
        · exact hlate (i + 1) (by omega) hx1
      have hconst : ∀ n, c (t + n) = c t := fun n => by
        induction n with
        | zero => rfl
        | succ n ih =>
          have := (hE (t + n)).2 (hfree _ (Nat.le_add_right _ _))
          rw [hβR, one_mul] at this
          rw [← ih, ← add_assoc]
          exact (U.cd_du_inj (hf.2 _).1 (hf.2 _).1 this).symm
      refine ⟨t, hts, ?_⟩
      obtain ⟨n, hn⟩ : ∃ n, j = t + n := ⟨j - t, by omega⟩
      rw [hn, hconst]
  exact (hjt.trans (cd3_le_A_of_constrained hR hy hf hmono ht)).trans (le_ciSup hbdd t)

/-- Miao, p. 247 (Chamberlain and Wilson), corrected: with `βR = 1` and `a₀ = −b`
(`x₀ = y_0 − rb`), consumption along an optimal plan converges to the highest annuity value of
the remaining income, `lim c_t = sup_t A_t`. -/
theorem cd3_chamberlain_wilson (U : cd_Utility) {β R b M : ℝ} (hβ : 0 < β) (hR : 1 < R)
    (hβR : β * R = 1) {y : ℕ → ℝ} (hy : ∀ t, (R - 1) * b ≤ y t ∧ y t ≤ M) {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b y (y 0 - (R - 1) * b) c x) :
    Tendsto c atTop (𝓝 (⨆ t, cd3_A R b y t)) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hmono := (cd3_monotone U hβ hR0 hβR h).1
  have hup : ∀ j, c j ≤ ⨆ t, cd3_A R b y t := cd3_upper U hβ hR hβR hy h h.1.1.1
  have hbddc : BddAbove (Set.range c) := ⟨_, Set.forall_mem_range.2 hup⟩
  have hlim := tendsto_atTop_ciSup hmono hbddc
  have heq : (⨆ j, c j) = ⨆ t, cd3_A R b y t := by
    refine le_antisymm (ciSup_le hup) (ciSup_le fun t => ?_)
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj⟩ := cd3_lower U hβ hR hy le_rfl h t _ hlt
    exact absurd (le_ciSup hbddc j) (not_le.2 hj)
  rwa [heq] at hlim

/-- Miao, p. 249: with constant income `y > rb` and `βR = 1`, the plan `c_t = y + ra₀`,
`a_{t+1} = a₀` (cash on hand `x_t = Ra₀ + y + b`) satisfies the Euler equation and the
transversality condition, hence is optimal, for every `a₀ ≥ −b`. -/
theorem cd3_constant_income (U : cd_Utility) {β R b y a₀ : ℝ} (hβ : 0 < β) (hR : 1 < R)
    (hβR : β * R = 1) (hy : (R - 1) * b < y) (ha₀ : -b ≤ a₀) :
    cd_Optimal U β R b (fun _ => y) (R * a₀ + y + b) (fun _ => y + (R - 1) * a₀)
      (fun _ => R * a₀ + y + b) := by
  have hβ1 : β < 1 := by nlinarith
  refine cd_sufficient U hβ.le ⟨⟨rfl, fun t => by ring⟩, fun t => ⟨by nlinarith, by linarith⟩⟩
    (fun t => ⟨by rw [hβR, one_mul], fun _ => by rw [hβR, one_mul]⟩) ?_
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
    (U.du (y + (R - 1) * a₀) * (R * a₀ + y + b - (y + (R - 1) * a₀)))
  rw [zero_mul] at this
  exact this.congr fun t => by ring

/-- Miao, p. 247: the claim `lim c_t = sup_t A_t` for every optimal plan is false. With
constant income `y > rb`, `βR = 1` and `a₀ > −b`, the optimal plan `c_t = y + ra₀` of
`cd3_constant_income` has `lim c_t = y + ra₀ > y − rb = sup_t A_t`. -/
theorem cd3_chamberlain_wilson_counterexample (U : cd_Utility) {β R b y a₀ : ℝ} (hβ : 0 < β)
    (hR : 1 < R) (hβR : β * R = 1) (hy : (R - 1) * b < y) (ha₀ : -b < a₀) :
    cd_Optimal U β R b (fun _ => y) (R * a₀ + y + b) (fun _ => y + (R - 1) * a₀)
        (fun _ => R * a₀ + y + b) ∧
      (⨆ t, cd3_A R b (fun _ => y) t) = y - (R - 1) * b ∧
      ¬ Tendsto (fun _ : ℕ => y + (R - 1) * a₀) atTop (𝓝 (⨆ t, cd3_A R b (fun _ => y) t)) := by
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hA : ∀ t, cd3_A R b (fun _ => y) t = y - (R - 1) * b := fun t => by
    unfold cd3_A
    rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1]
    rw [← mul_assoc, mul_inv_cancel₀ (sub_pos.2 hρ1).ne', one_mul]
  have hsup : (⨆ t, cd3_A R b (fun _ => y) t) = y - (R - 1) * b := by
    simp only [hA, ciSup_const]
  refine ⟨cd3_constant_income U hβ hR hβR hy ha₀.le, hsup, fun hlim => ?_⟩
  rw [hsup] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  have hr : 0 < R - 1 := by linarith
  nlinarith

/-- Miao, p. 247: the printed annuity formula `A_t = r∑_{j≥1}R^{−j}(y_{t+j} − rb)` omits the
income of period `t`. With `b = 0`, `y_0 = Y > 0` and `y_t = 0` afterwards, `βR = 1`, `a₀ = 0`,
the plan `c_t = (r/R)Y` (cash on hand `Y`) is optimal, `lim c_t = (r/R)Y = A_0 = sup_t A_t`
(as `cd3_chamberlain_wilson` says), but every printed `A_t` is `0`. -/
theorem cd3_Abook_counterexample (U : cd_Utility) {β R Y : ℝ} (hβ : 0 < β) (hR : 1 < R)
    (hβR : β * R = 1) (hY : 0 < Y) :
    cd_Optimal U β R 0 (fun t => if t = 0 then Y else 0) Y (fun _ => (1 - R⁻¹) * Y)
        (fun _ => Y) ∧
      (∀ t, cd3_Abook R 0 (fun t => if t = 0 then Y else 0) t = 0) ∧
      (⨆ t, cd3_A R 0 (fun t => if t = 0 then Y else 0) t) = (1 - R⁻¹) * Y ∧
      ¬ Tendsto (fun _ : ℕ => (1 - R⁻¹) * Y) atTop
        (𝓝 (⨆ t, cd3_Abook R 0 (fun t => if t = 0 then Y else 0) t)) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hρ0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hρ1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have h1ρ : 0 < 1 - R⁻¹ := sub_pos.2 hρ1
  have hβ1 : β < 1 := by nlinarith
  set y : ℕ → ℝ := fun t => if t = 0 then Y else 0
  have hopt : cd_Optimal U β R 0 y Y (fun _ => (1 - R⁻¹) * Y) (fun _ => Y) := by
    refine cd_sufficient U hβ.le ⟨⟨rfl, fun t => ?_⟩, fun t => ⟨by positivity, ?_⟩⟩
      (fun t => ⟨by rw [hβR, one_mul], fun _ => by rw [hβR, one_mul]⟩) ?_
    · simp only [y, Nat.succ_ne_zero, ↓reduceIte]
      field_simp
      ring
    · nlinarith
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
        (U.du ((1 - R⁻¹) * Y) * (Y - (1 - R⁻¹) * Y))
      rw [zero_mul] at this
      exact this.congr fun t => by ring
  have hbook : ∀ t, cd3_Abook R 0 y t = 0 := fun t => by
    unfold cd3_Abook
    simp [y]
  have hA0 : cd3_A R 0 y 0 = (1 - R⁻¹) * Y := by
    unfold cd3_A
    rw [tsum_eq_single 0 fun n hn => by simp [y, hn]]
    simp [y]
  have hA : ∀ t, 1 ≤ t → cd3_A R 0 y t = 0 := fun t ht => by
    unfold cd3_A
    have : ∀ n, y (t + n) = 0 := fun n => by simp only [y, show t + n ≠ 0 by omega, ↓reduceIte]
    simp [this]
  have hsup : (⨆ t, cd3_A R 0 y t) = (1 - R⁻¹) * Y := by
    refine le_antisymm (ciSup_le fun t => ?_) (hA0 ▸ le_ciSup (cd3_A_bdd (M := Y) hR
      (fun t => ⟨by simp only [y]; split_ifs <;> linarith, by
        simp only [y]; split_ifs <;> linarith⟩)) 0)
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, hA0]
    · rw [hA t h0]; positivity
  refine ⟨hopt, hbook, hsup, fun hlim => ?_⟩
  simp only [hbook, ciSup_const] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  have : 0 < (1 - R⁻¹) * Y := mul_pos h1ρ hY
  linarith

end Miao.Applications
