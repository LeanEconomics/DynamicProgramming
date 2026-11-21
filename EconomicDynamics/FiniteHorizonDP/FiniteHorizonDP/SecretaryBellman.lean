/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
# The secretary problem: the Bellman equations and the optimal threshold

Miao, §6.6.1, pp. 185–186. Candidates `t = 1, …, N` arrive in random order; the state is `1` if
the current candidate is the best so far and `0` otherwise; stopping at a best-so-far candidate
at date `t` wins with probability `t/N`; the next candidate is the best so far with probability
`1/(t + 1)`. (That these are the probabilities of the problem is `secretary_prob` in
`MDPSecretary`; that the recursion below gives the values of the Markov decision problem of
Chapter 5 is `SecretaryMDP`.)

* `sec_V N t z`: the solution of the book's Bellman equation, `V_N(1) = 1`, `V_N(0) = 0`,
  `V_t(1) = max{t/N, V_{t+1}(1)/(t+1) + tV_{t+1}(0)/(t+1)}`,
  `V_t(0) = max{0, V_{t+1}(1)/(t+1) + tV_{t+1}(0)/(t+1)}` (`sec_bellman`, `sec_V_terminal`).
* (6.41)–(6.42) (`eq_6_41_6_42`); `V_t ≥ 0`, `V_t(1) ≥ V_t(0)`, `V_t(0)` nonincreasing.
* `sec_H N t = 1/t + ⋯ + 1/(N − 1)`, `sec_tau N` = τ of (6.43).
* The closed form `V_t(0) = (t/N)(1/t + ⋯ + 1/(N − 1))` for `τ ≤ t ≤ N` (`sec_V0_closed`), and the
  threshold structure: `V_t(0) ≤ t/N` for `τ ≤ t ≤ N` (stop at a best-so-far candidate) and
  `V_t(0) ≥ t/N` for `1 ≤ t < τ` (continue) (`sec_threshold`).
* **Corrections.** (6.43) gives `τ(4) = 2`, not the printed `τ(4) = 1` (`sec_tau_four`). With τ as
  in (6.43), τ is the first date at which a best-so-far candidate is accepted: it is optimal to
  reject the first `τ − 1` candidates (one candidate for `N = 4`, as the book's prose says), not
  `τ` as Proposition 6.6.1 states (`prop_6_6_1_misprint` in `SecretaryMDP`). The proof's claim
  "`t/N ≤ V_t(0)` for all `t ≤ τ`" fails at `t = τ` (`sec_threshold_misprint`); it holds for
  `t < τ`.
-/

namespace Miao.FiniteHorizonDP

/-- The book's Bellman equation for the secretary problem, by time to go `n = N − t`:
`sec_val N n z = V_{N−n}(z)`. -/
noncomputable def sec_val (N : ℕ) : ℕ → Fin 2 → ℝ
  | 0 => fun z => if z = 1 then 1 else 0
  | n + 1 => fun z =>
    if z = 1 then
      max (((N - (n + 1) : ℕ) : ℝ) / N)
        (1 / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 1 +
          ((N - (n + 1) : ℕ) : ℝ) / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 0)
    else
      max 0 (1 / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 1 +
        ((N - (n + 1) : ℕ) : ℝ) / (((N - (n + 1) : ℕ) : ℝ) + 1) * sec_val N n 0)

/-- `V_t(z)`, the value at date `t` in state `z` (Miao, p. 185). -/
noncomputable def sec_V (N t : ℕ) (z : Fin 2) : ℝ := sec_val N (N - t) z

/-- The continuation value `V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)`. -/
noncomputable def sec_C (N t : ℕ) : ℝ :=
  1 / ((t : ℝ) + 1) * sec_V N (t + 1) 1 + (t : ℝ) / ((t : ℝ) + 1) * sec_V N (t + 1) 0

/-- Miao, p. 185: `V_N(1) = h(1) = 1`, `V_N(0) = h(0) = 0`. -/
theorem sec_V_terminal (N : ℕ) : sec_V N N 1 = 1 ∧ sec_V N N 0 = 0 := by
  simp [sec_V, sec_val]

/-- **The Bellman equation of the secretary problem** (Miao, p. 185): for `t < N`,
`V_t(1) = max{t/N, V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)}` and
`V_t(0) = max{0, V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)}`. -/
theorem sec_bellman (N : ℕ) {t : ℕ} (ht : t < N) :
    sec_V N t 1 = max ((t : ℝ) / N) (sec_C N t) ∧ sec_V N t 0 = max 0 (sec_C N t) := by
  have e1 : N - t = (N - (t + 1)) + 1 := by omega
  have e2 : N - (N - (t + 1) + 1) = t := by omega
  unfold sec_V sec_C
  rw [e1]
  simp only [sec_val, e2, ite_true]
  exact ⟨rfl, by simp [sec_V]⟩

theorem sec_V_nonneg (N : ℕ) : ∀ t z, 0 ≤ sec_V N t z := by
  have : ∀ n z, 0 ≤ sec_val N n z := by
    intro n
    induction n with
    | zero => intro z; simp only [sec_val]; split_ifs <;> norm_num
    | succ n ih =>
      intro z
      simp only [sec_val]
      split_ifs
      · exact le_max_of_le_left (by positivity)
      · exact le_max_left _ _
  exact fun t z => this _ z

theorem sec_C_nonneg (N t : ℕ) : 0 ≤ sec_C N t := by
  have := sec_V_nonneg N
  unfold sec_C
  have h1 := this (t + 1) 1
  have h0 := this (t + 1) 0
  positivity

/-- **(6.41)–(6.42)** (Miao, p. 185): for `t < N`, since `V_t ≥ 0`,
`V_t(0) = V_{t+1}(1)/(t + 1) + tV_{t+1}(0)/(t + 1)` and `V_t(1) = max{t/N, V_t(0)}`. -/
theorem eq_6_41_6_42 (N : ℕ) {t : ℕ} (ht : t < N) :
    sec_V N t 0 = 1 / ((t : ℝ) + 1) * sec_V N (t + 1) 1 +
        (t : ℝ) / ((t : ℝ) + 1) * sec_V N (t + 1) 0 ∧
      sec_V N t 1 = max ((t : ℝ) / N) (sec_V N t 0) := by
  obtain ⟨h1, h0⟩ := sec_bellman N ht
  rw [h0, max_eq_right (sec_C_nonneg N t)] at *
  exact ⟨rfl, h1⟩

/-- (6.42) at the terminal date too: `V_N(1) = max{N/N, V_N(0)}` (for `N ≥ 1`). -/
theorem eq_6_42_terminal {N : ℕ} (hN : 1 ≤ N) :
    sec_V N N 1 = max ((N : ℝ) / N) (sec_V N N 0) := by
  obtain ⟨h1, h0⟩ := sec_V_terminal N
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [h1, h0, div_self this]
  simp

/-- Miao, p. 186: `V_t(1) ≥ V_t(0)` (for `t ≤ N`). -/
theorem sec_V1_ge_V0 (N : ℕ) {t : ℕ} (ht : t ≤ N) : sec_V N t 0 ≤ sec_V N t 1 := by
  rcases Nat.lt_or_ge t N with h | h
  · obtain ⟨h1, h0⟩ := sec_bellman N h
    rw [h1, h0]
    exact max_le_max (by positivity) le_rfl
  · have : t = N := le_antisymm ht h
    subst this
    obtain ⟨h1, h0⟩ := sec_V_terminal t
    rw [h1, h0]
    norm_num

/-- Miao, p. 186: `V_t(0) ≥ V_{t+1}(0)` (from (6.41) and `V_{t+1}(1) ≥ V_{t+1}(0)`). -/
theorem sec_V0_succ_le (N : ℕ) {t : ℕ} (ht : t < N) : sec_V N (t + 1) 0 ≤ sec_V N t 0 := by
  rw [(eq_6_41_6_42 N ht).1]
  have h := sec_V1_ge_V0 N (show t + 1 ≤ N by omega)
  have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have key : 1 / ((t : ℝ) + 1) * sec_V N (t + 1) 0 +
      (t : ℝ) / ((t : ℝ) + 1) * sec_V N (t + 1) 0 = sec_V N (t + 1) 0 := by
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1))
  linarith

theorem sec_V0_antitone (N : ℕ) {t t' : ℕ} (htt : t ≤ t') (ht' : t' ≤ N) :
    sec_V N t' 0 ≤ sec_V N t 0 := by
  induction t' with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact le_rfl
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le htt with h | h
    · rw [h]
    · exact (sec_V0_succ_le N (by omega)).trans (ih (by omega) (by omega))

/-- `1/t + 1/(t + 1) + ⋯ + 1/(N − 1)` (Miao (6.43)). -/
noncomputable def sec_H (N t : ℕ) : ℝ := ∑ k ∈ Finset.Ico t N, (1 : ℝ) / k

/-- `τ = min{t ≥ 1 : 1/t + ⋯ + 1/(N − 1) < 1}` (Miao (6.43)). -/
noncomputable def sec_tau (N : ℕ) : ℕ := sInf {t : ℕ | 1 ≤ t ∧ sec_H N t < 1}

theorem sec_H_self (N : ℕ) : sec_H N N = 0 := by simp [sec_H]

theorem sec_H_succ {N t : ℕ} (ht : t < N) : sec_H N t = 1 / t + sec_H N (t + 1) := by
  unfold sec_H
  rw [Finset.sum_eq_sum_Ico_succ_bot ht]

theorem sec_H_nonneg (N t : ℕ) : 0 ≤ sec_H N t :=
  Finset.sum_nonneg fun k _ => by positivity

theorem sec_H_anti (N : ℕ) {t t' : ℕ} (h : t ≤ t') : sec_H N t' ≤ sec_H N t :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left h)
    fun k _ _ => by positivity

theorem sec_tau_spec {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ sec_tau N ∧ sec_H N (sec_tau N) < 1 ∧ sec_tau N ≤ N := by
  have hne : ({t : ℕ | 1 ≤ t ∧ sec_H N t < 1} : Set ℕ).Nonempty :=
    ⟨N, hN, by rw [sec_H_self]; norm_num⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨hmem.1, hmem.2, Nat.sInf_le ⟨hN, by rw [sec_H_self]; norm_num⟩⟩

theorem sec_tau_min {N t : ℕ} (h1 : 1 ≤ t) (ht : t < sec_tau N) : 1 ≤ sec_H N t := by
  by_contra h
  exact Nat.notMem_of_lt_sInf ht ⟨h1, lt_of_not_ge h⟩

theorem sec_H_lt_one {N t : ℕ} (hN : 1 ≤ N) (ht : sec_tau N ≤ t) : sec_H N t < 1 :=
  lt_of_le_of_lt (sec_H_anti N ht) (sec_tau_spec hN).2.1

/-- **The closed form** (Miao, p. 186): for `τ ≤ t ≤ N`,
`V_t(0) = (t/N)(1/t + 1/(t + 1) + ⋯ + 1/(N − 1))`. -/
theorem sec_V0_closed {N : ℕ} (hN : 1 ≤ N) :
    ∀ t, sec_tau N ≤ t → t ≤ N → sec_V N t 0 = (t : ℝ) / N * sec_H N t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ n t, N - t = n → sec_tau N ≤ t → t ≤ N →
      sec_V N t 0 = (t : ℝ) / N * sec_H N t := by
    intro n
    induction n with
    | zero =>
      intro t hn _ ht
      have : t = N := by omega
      subst this
      rw [(sec_V_terminal t).2, sec_H_self, mul_zero]
    | succ n ih =>
      intro t hn hτ ht
      have htN : t < N := by omega
      have ht1 : 1 ≤ t := le_trans (sec_tau_spec hN).1 hτ
      have hIH := ih (t + 1) (by omega) (by omega) (by omega)
      have hH1 := sec_H_lt_one hN (show sec_tau N ≤ t + 1 by omega)
      have hV1 : sec_V N (t + 1) 1 = ((t : ℝ) + 1) / N := by
        rcases Nat.lt_or_ge (t + 1) N with h | h
        · rw [(eq_6_41_6_42 N h).2, hIH]
          push_cast
          refine max_eq_left ?_
          have : 0 ≤ ((t : ℝ) + 1) / N := by positivity
          nlinarith [sec_H_nonneg N (t + 1)]
        · have : t + 1 = N := by omega
          rw [this, (sec_V_terminal N).1]
          rw [← this]
          push_cast
          field_simp
      rw [(eq_6_41_6_42 N htN).1, hV1, hIH, sec_H_succ htN]
      have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
      push_cast
      field_simp
  exact fun t hτ ht => key (N - t) t rfl hτ ht

/-- **The threshold structure** (Miao, p. 186), with τ as in (6.43): for `τ ≤ t ≤ N`,
`V_t(0) ≤ t/N`, so `V_t(1) = t/N` and accepting a best-so-far candidate is optimal; for
`1 ≤ t < τ`, `V_t(0) ≥ t/N`, so `V_t(1) = V_t(0)` and continuing is optimal. -/
theorem sec_threshold {N : ℕ} (hN : 1 ≤ N) :
    (∀ t, sec_tau N ≤ t → t ≤ N → sec_V N t 0 ≤ (t : ℝ) / N) ∧
      (∀ t, 1 ≤ t → t < sec_tau N → (t : ℝ) / N ≤ sec_V N t 0) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hstop : ∀ t, sec_tau N ≤ t → t ≤ N → sec_V N t 0 ≤ (t : ℝ) / N := by
    intro t hτ ht
    rw [sec_V0_closed hN t hτ ht]
    have := sec_H_lt_one hN hτ
    have : 0 ≤ (t : ℝ) / N := by positivity
    nlinarith
  refine ⟨hstop, fun t ht1 htτ => ?_⟩
  obtain ⟨hτ1, -, hτN⟩ := sec_tau_spec hN
  set m := sec_tau N - 1 with hm
  have hm1 : t ≤ m := by omega
  have hmN : m < N := by omega
  have hmτ : m + 1 = sec_tau N := by omega
  have hVm : sec_V N m 0 = (m : ℝ) / N * sec_H N m := by
    have hcl := sec_V0_closed hN (m + 1) (by omega) (by omega)
    have hV1 : sec_V N (m + 1) 1 = ((m : ℝ) + 1) / N := by
      rcases Nat.lt_or_ge (m + 1) N with h | h
      · rw [(eq_6_41_6_42 N h).2, hcl]
        push_cast
        refine max_eq_left ?_
        have := sec_H_lt_one hN (show sec_tau N ≤ m + 1 by omega)
        have : 0 ≤ ((m : ℝ) + 1) / N := by positivity
        nlinarith [sec_H_nonneg N (m + 1)]
      · have : m + 1 = N := by omega
        rw [this, (sec_V_terminal N).1, ← this]
        push_cast
        field_simp
    rw [(eq_6_41_6_42 N hmN).1, hV1, hcl, sec_H_succ hmN]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast
    field_simp
  have hHm : 1 ≤ sec_H N m := sec_tau_min (by omega) (by omega)
  have h1 : (m : ℝ) / N ≤ sec_V N m 0 := by
    rw [hVm]
    have : 0 ≤ (m : ℝ) / N := by positivity
    nlinarith
  have h2 : (t : ℝ) / N ≤ (m : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm1) hNpos.le
  exact h2.trans (h1.trans (sec_V0_antitone N hm1 hmN.le))

/-- **τ(4) = 2, not 1** (Miao, p. 186): by (6.43), `1 + 1/2 + 1/3 ≥ 1` and `1/2 + 1/3 < 1`, so
`τ(4) = 2`. The book's `τ(4) = 1` is the number of candidates rejected, `τ − 1`. -/
theorem sec_tau_four : sec_tau 4 = 2 ∧ sec_tau 4 ≠ 1 ∧ sec_tau 4 - 1 = 1 := by
  have h3 : sec_H 4 3 = 1 / 3 := by
    rw [sec_H_succ (by norm_num), sec_H_self]
    norm_num
  have h2 : sec_H 4 2 = 5 / 6 := by
    rw [sec_H_succ (by norm_num), h3]
    norm_num
  have h1 : sec_H 4 1 = 11 / 6 := by
    rw [sec_H_succ (by norm_num), h2]
    norm_num
  have hτ : sec_tau 4 = 2 := by
    refine le_antisymm (Nat.sInf_le ⟨by norm_num, by rw [h2]; norm_num⟩) ?_
    refine le_csInf ⟨2, by norm_num, by rw [h2]; norm_num⟩ fun t ht => ?_
    obtain ⟨ht1, htH⟩ := ht
    by_contra hlt
    have : t = 1 := by omega
    subst this
    rw [h1] at htH
    norm_num at htH
  exact ⟨hτ, by rw [hτ]; norm_num, by rw [hτ]⟩

/-- **The book's "`t/N ≤ V_t(0)` for all `t ≤ τ`" fails at `t = τ`** (Miao, p. 186): for `N = 4`,
`τ = 2` and `V_2(0) = (2/4)(1/2 + 1/3) = 5/12 < 2/4`. -/
theorem sec_threshold_misprint : sec_V 4 2 0 = 5 / 12 ∧ sec_V 4 2 0 < (2 : ℝ) / 4 := by
  have hτ := sec_tau_four.1
  have h2 : sec_H 4 2 = 5 / 6 := by
    rw [sec_H_succ (by norm_num), sec_H_succ (by norm_num), sec_H_self]
    norm_num
  have := sec_V0_closed (N := 4) (by norm_num) 2 (by rw [hτ]) (by norm_num)
  rw [this, h2]
  norm_num

end Miao.FiniteHorizonDP
