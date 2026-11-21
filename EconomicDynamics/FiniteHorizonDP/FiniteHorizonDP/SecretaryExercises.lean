/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exercises 6.3–6.4: two variants of the secretary problem

Miao, p. 189. Dates are the book's: the `k`-th candidate is seen at date `k = 1, …, N`.

**Exercise 6.3** (choose one of the two best). The state is the relative rank of the current
candidate among the first `k`: `1` (best so far), `2` (second best so far) or `0` (other); the
model is Chapter 5's `secretaryTwo` (Exercise 5.3), whose payoffs are the probabilities that a
candidate of relative rank `1` or `2` among the first `k` is among the two best of all,
`g_k(1) = k(2N − k − 1)/(N(N − 1))`, `g_k(2) = k(k − 1)/(N(N − 1))` (their counting derivation is
not formalised), and the next candidate has relative rank `1` or `2` with probability
`1/(k + 1)` each.
* The Bellman equation `V_k(r) = max{g_k(r), W_k}`,
  `W_k = (V_{k+1}(1) + V_{k+1}(2))/(k + 1) + (k − 1)V_{k+1}(0)/(k + 1)`, `V_N(1) = V_N(2) = 1`,
  `V_N(0) = 0` (`two_V`, `ex_6_3_bellman`).
* The threshold form (`ex_6_3_threshold`): `W_k` is nonincreasing and `g_k(r)` nondecreasing in
  `k`, so for each relative rank the dates at which stopping is optimal form a final segment
  `{τ_r, …, N}`; and stopping at relative rank `2` implies stopping at relative rank `1`, so
  `τ_1 ≤ τ_2`.
* The explicit part (`ex_6_3_rank2`): stopping at a second-best-so-far candidate at date
  `k ≤ N − 1` is optimal if and only if `3k ≥ 2N + 1`, i.e. `τ_2 = ⌈(2N + 1)/3⌉`; on those dates
  `W_k = 2k(N − k)/(N(N − 1))` and `V_k(r) = g_k(r)` for `r = 1, 2`. In general
  `W_k ≥ 2k(N − k)/(N(N − 1))` (`ex_6_3_lower`). The first threshold `τ_1` has no closed form; its
  asymptotics (`τ_1/N → 0.347`) are not formalised.
* `ex_6_3_mdp` (in `SecretaryTwoMDP`): by Theorem 6.3.2 the recursion gives the value functions of
  Chapter 5's Markov decision problem `(secretaryTwo N).toMDP`, and the threshold rule is optimal.

**Exercise 6.4** (minimise the expected rank; the book's "maximize the expected rank" means the
rank number is to be minimised, rank `1` being the best). The state is the relative rank
`r ∈ {1, …, k}`; stopping at relative rank `r` at date `k` gives the expected absolute rank
`r(N + 1)/(k + 1)` (taken as the model's data; its derivation is not formalised); the next
relative rank is uniform on `{1, …, k + 1}`.
* The Bellman equation `V_k(r) = min{r(N + 1)/(k + 1), W_k}`,
  `W_k = (1/(k + 1)) ∑_{r'=1}^{k+1} V_{k+1}(r')`, `V_N(r) = r` (`rank_V`, `ex_6_4_bellman`).
* The threshold form (`ex_6_4_threshold`): stopping at date `k` is optimal exactly for the
  relative ranks `r ≤ s_k = (k + 1)W_k/(N + 1)`, and `s_k` is nondecreasing in `k` (since `W_k` is
  nondecreasing).
* Explicit values: `W_{N−1} = (N + 1)/2` (`ex_6_4_last`) and, for `N = 3`, the minimal expected
  rank is `5/3` (`ex_6_4_three`). The Chow–Moriguti–Robbins–Samuels limit `≈ 3.8695` as
  `N → ∞` is out of scope and not formalised.
-/

namespace Miao.FiniteHorizonDP

/-! ### Exercise 6.3 -/

/-- The payoff of stopping at relative rank `r` at date `k` (Exercise 6.3). -/
noncomputable def two_g (N k : ℕ) (r : Fin 3) : ℝ :=
  if r = 1 then (k : ℝ) * (2 * N - k - 1) / (N * (N - 1))
  else if r = 2 then (k : ℝ) * (k - 1) / (N * (N - 1)) else 0

/-- The Bellman equation of Exercise 6.3, by time to go `n = N − k`. -/
noncomputable def two_val (N : ℕ) : ℕ → Fin 3 → ℝ
  | 0 => fun r => if r = 0 then 0 else 1
  | n + 1 => fun r =>
    max (two_g N (N - (n + 1)) r)
      ((two_val N n 1 + two_val N n 2) / (((N - (n + 1) : ℕ) : ℝ) + 1) +
        (((N - (n + 1) : ℕ) : ℝ) - 1) / (((N - (n + 1) : ℕ) : ℝ) + 1) * two_val N n 0)

/-- `V_k(r)` of Exercise 6.3. -/
noncomputable def two_V (N k : ℕ) (r : Fin 3) : ℝ := two_val N (N - k) r

/-- The continuation value `W_k` of Exercise 6.3. -/
noncomputable def two_W (N k : ℕ) : ℝ :=
  (two_V N (k + 1) 1 + two_V N (k + 1) 2) / ((k : ℝ) + 1) +
    ((k : ℝ) - 1) / ((k : ℝ) + 1) * two_V N (k + 1) 0

/-- **Exercise 6.3: the Bellman equation** (Miao, p. 189): `V_N(0) = 0`, `V_N(1) = V_N(2) = 1`,
and `V_k(r) = max{g_k(r), W_k}` for `k < N`. -/
theorem ex_6_3_bellman (N : ℕ) :
    (two_V N N 0 = 0 ∧ two_V N N 1 = 1 ∧ two_V N N 2 = 1) ∧
      ∀ k < N, ∀ r, two_V N k r = max (two_g N k r) (two_W N k) := by
  refine ⟨by simp [two_V, two_val], fun k hk r => ?_⟩
  have e1 : N - k = (N - (k + 1)) + 1 := by omega
  have e2 : N - (N - (k + 1) + 1) = k := by omega
  unfold two_V two_W
  rw [e1]
  simp only [two_val, e2]
  rfl

theorem two_g_nonneg {N k : ℕ} (hk : k ≤ N) (r : Fin 3) : 0 ≤ two_g N k r := by
  unfold two_g
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hden : 0 ≤ (N : ℝ) * (N - 1) := by nlinarith
  split_ifs
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hden
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h0
      exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hden
  · exact le_rfl

theorem two_V_nonneg {N k : ℕ} (hk : k ≤ N) (r : Fin 3) : 0 ≤ two_V N k r := by
  rcases Nat.lt_or_ge k N with h | h
  · rw [(ex_6_3_bellman N).2 k h r]
    exact le_max_of_le_left (two_g_nonneg hk r)
  · have : k = N := le_antisymm hk h
    subst this
    obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman k).1
    fin_cases r
    · simp [h0]
    · simp [h1]
    · simp [h2]

theorem two_W_nonneg {N k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) : 0 ≤ two_W N k := by
  unfold two_W
  have h1 := two_V_nonneg (N := N) (k := k + 1) (by omega) 1
  have h2 := two_V_nonneg (N := N) (k := k + 1) (by omega) 2
  have h0 := two_V_nonneg (N := N) (k := k + 1) (by omega) 0
  have : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  positivity

theorem two_V0 {N k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) : two_V N k 0 = two_W N k := by
  rw [(ex_6_3_bellman N).2 k hk 0]
  simp only [two_g, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide, ite_false]
  exact max_eq_right (two_W_nonneg hk1 hk)

theorem two_V_ge_V0 {N k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N) (r : Fin 3) :
    two_V N k 0 ≤ two_V N k r := by
  rcases Nat.lt_or_ge k N with h | h
  · rw [two_V0 hk1 h, (ex_6_3_bellman N).2 k h r]
    exact le_max_right _ _
  · have : k = N := le_antisymm hk h
    subst this
    obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman k).1
    rw [h0]
    exact two_V_nonneg le_rfl r

/-- `W_k` is nonincreasing. -/
theorem two_W_anti {N k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 < N) : two_W N (k + 1) ≤ two_W N k := by
  rw [← two_V0 (by omega) hk]
  have h1 := two_V_ge_V0 (N := N) (k := k + 1) (by omega) hk.le 1
  have h2 := two_V_ge_V0 (N := N) (k := k + 1) (by omega) hk.le 2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  unfold two_W
  have e : (two_V N (k + 1) 1 + two_V N (k + 1) 2) / ((k : ℝ) + 1) +
      ((k : ℝ) - 1) / ((k : ℝ) + 1) * two_V N (k + 1) 0 - two_V N (k + 1) 0 =
      ((two_V N (k + 1) 1 - two_V N (k + 1) 0) + (two_V N (k + 1) 2 - two_V N (k + 1) 0)) /
        ((k : ℝ) + 1) := by
    field_simp
    ring
  have : 0 ≤ ((two_V N (k + 1) 1 - two_V N (k + 1) 0) +
      (two_V N (k + 1) 2 - two_V N (k + 1) 0)) / ((k : ℝ) + 1) :=
    div_nonneg (by linarith) hpos.le
  linarith

theorem two_W_anti' {N k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k') (hk' : k' < N) :
    two_W N k' ≤ two_W N k := by
  induction k' with
  | zero => omega
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with h | h
    · rw [h]
    · exact (two_W_anti (by omega) hk').trans (ih (by omega) (by omega))

/-- The payoffs are nondecreasing in the date, and `g_k(2) ≤ g_k(1)`. -/
theorem two_g_mono {N k : ℕ} (hk : k + 1 ≤ N) :
    two_g N k 1 ≤ two_g N (k + 1) 1 ∧ two_g N k 2 ≤ two_g N (k + 1) 2 ∧
      two_g N k 2 ≤ two_g N k 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hden : 0 ≤ (N : ℝ) * (N - 1) := by nlinarith
  simp only [two_g, ite_true, show (2 : Fin 3) ≠ 1 by decide, ite_false]
  push_cast
  refine ⟨div_le_div_of_nonneg_right (by nlinarith) hden,
    div_le_div_of_nonneg_right (by nlinarith) hden,
    div_le_div_of_nonneg_right (by nlinarith) hden⟩

theorem two_g_mono' {N k k' : ℕ} (hkk : k ≤ k') (hk' : k' ≤ N) (r : Fin 3) (hr : r ≠ 0) :
    two_g N k r ≤ two_g N k' r := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    rw [this]
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with h | h
    · rw [h]
    · have hm := two_g_mono (N := N) (k := k') hk'
      refine (ih (by omega) (by omega)).trans ?_
      fin_cases r
      · exact absurd rfl hr
      · exact hm.1
      · exact hm.2.1

/-- **Exercise 6.3: the threshold form** (Miao, p. 189). For a relative rank `r ∈ {1, 2}` and
`1 ≤ k ≤ k' ≤ N − 1`, if stopping is optimal at `(k, r)` (`g_k(r) ≥ W_k`) it is optimal at
`(k', r)`; and if stopping at relative rank `2` is optimal at `k`, so is stopping at relative
rank `1`. -/
theorem ex_6_3_threshold {N : ℕ} {k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k') (hk' : k' < N)
    (r : Fin 3) (hr : r ≠ 0) :
    (two_W N k ≤ two_g N k r → two_W N k' ≤ two_g N k' r) ∧
      (two_W N k ≤ two_g N k 2 → two_W N k ≤ two_g N k 1) := by
  refine ⟨fun h => (two_W_anti' hk1 hkk hk').trans (h.trans
    (two_g_mono' hkk hk'.le r hr)), fun h => h.trans ?_⟩
  rcases Nat.lt_or_ge k N with hlt | hge
  · exact (two_g_mono (N := N) (k := k) hlt).2.2
  · omega

/-- The value of "stop at the first candidate of relative rank `1` or `2` after date `k`":
`2k(N − k)/(N(N − 1))`. -/
noncomputable def two_L (N k : ℕ) : ℝ := 2 * k * (N - k) / (N * (N - 1))

theorem two_L_step {N k : ℕ} (hN : 2 ≤ N) (hk1 : 1 ≤ k) :
    (two_g N (k + 1) 1 + two_g N (k + 1) 2) / ((k : ℝ) + 1) +
      ((k : ℝ) - 1) / ((k : ℝ) + 1) * two_L N (k + 1) = two_L N k := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (N : ℝ) * (N - 1) ≠ 0 := by nlinarith
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  simp only [two_g, two_L, ite_true, show (2 : Fin 3) ≠ 1 by decide, ite_false]
  push_cast
  field_simp
  ring

theorem two_W_last {N : ℕ} (hN : 2 ≤ N) : two_W N (N - 1) = two_L N (N - 1) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman N).1
  unfold two_W two_L
  rw [Nat.sub_add_cancel (by omega), h0, h1, h2]
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [show 1 ≤ N by omega]; ring
  rw [hc, show (N : ℝ) - 1 + 1 = N by ring]
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Exercise 6.3: a lower bound** — `W_k ≥ 2k(N − k)/(N(N − 1))` for `1 ≤ k ≤ N − 1`, the value
of stopping at the first candidate of relative rank `1` or `2` after `k`. -/
theorem ex_6_3_lower {N : ℕ} (hN : 2 ≤ N) :
    ∀ k, 1 ≤ k → k ≤ N - 1 → two_L N k ≤ two_W N k := by
  have key : ∀ n k, N - 1 - k = n → 1 ≤ k → k ≤ N - 1 → two_L N k ≤ two_W N k := by
    intro n
    induction n with
    | zero =>
      intro k hn _ hk
      have : k = N - 1 := by omega
      subst this
      rw [two_W_last hN]
    | succ n ih =>
      intro k hn hk1 hk
      have hIH := ih (k + 1) (by omega) (by omega) (by omega)
      have hlt : k + 1 < N := by omega
      have hV1 := (ex_6_3_bellman N).2 (k + 1) hlt 1
      have hV2 := (ex_6_3_bellman N).2 (k + 1) hlt 2
      have hV0 := two_V0 (N := N) (k := k + 1) (by omega) hlt
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      rw [← two_L_step hN hk1]
      unfold two_W
      rw [hV0]
      have e1 : two_g N (k + 1) 1 ≤ two_V N (k + 1) 1 := by rw [hV1]; exact le_max_left _ _
      have e2 : two_g N (k + 1) 2 ≤ two_V N (k + 1) 2 := by rw [hV2]; exact le_max_left _ _
      have e3 : 0 ≤ ((k : ℝ) - 1) / ((k : ℝ) + 1) := div_nonneg (by linarith) hpos.le
      have := mul_le_mul_of_nonneg_left hIH e3
      have : (two_g N (k + 1) 1 + two_g N (k + 1) 2) / ((k : ℝ) + 1) ≤
          (two_V N (k + 1) 1 + two_V N (k + 1) 2) / ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
      linarith
  exact fun k hk1 hk => key (N - 1 - k) k rfl hk1 hk

theorem two_g2_sub_L {N k : ℕ} (hN : 2 ≤ N) :
    two_g N k 2 - two_L N k = (k : ℝ) * (3 * k - 2 * N - 1) / (N * (N - 1)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  simp only [two_g, two_L, show (2 : Fin 3) ≠ 1 by decide, ite_false, ite_true]
  field_simp
  ring

/-- **Exercise 6.3: the second threshold, explicitly** (Miao, p. 189). For `N ≥ 2` and
`1 ≤ k ≤ N − 1`: stopping at a candidate who is second best so far is optimal at date `k` if and
only if `3k ≥ 2N + 1`; on those dates `W_k = 2k(N − k)/(N(N − 1))` and `V_k(r) = g_k(r)` for
`r = 1, 2`. -/
theorem ex_6_3_rank2 {N : ℕ} (hN : 2 ≤ N) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N - 1) :
    (two_W N k ≤ two_g N k 2 ↔ 2 * N + 1 ≤ 3 * k) ∧
      (2 * N + 1 ≤ 3 * k → two_W N k = two_L N k ∧
        two_V N k 1 = two_g N k 1 ∧ two_V N k 2 = two_g N k 2) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (0 : ℝ) < N * (N - 1) := by nlinarith
  -- exactness on the final segment
  have exact : ∀ n k, N - 1 - k = n → 1 ≤ k → k ≤ N - 1 → 2 * N + 1 ≤ 3 * k →
      two_W N k = two_L N k := by
    intro n
    induction n with
    | zero =>
      intro k hn _ hk _
      have : k = N - 1 := by omega
      subst this
      exact two_W_last hN
    | succ n ih =>
      intro k hn hk1 hk h3
      have hIH := ih (k + 1) (by omega) (by omega) (by omega) (by omega)
      have hlt : k + 1 < N := by omega
      have hge2 : two_W N (k + 1) ≤ two_g N (k + 1) 2 := by
        rw [hIH, ← sub_nonneg, two_g2_sub_L hN]
        have : (2 * N + 1 : ℝ) ≤ 3 * ((k : ℝ) + 1) := by exact_mod_cast (by omega : _)
        push_cast
        exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hden.le
      have hge1 : two_W N (k + 1) ≤ two_g N (k + 1) 1 :=
        hge2.trans (two_g_mono (N := N) (k := k + 1) hlt).2.2
      have hV1 : two_V N (k + 1) 1 = two_g N (k + 1) 1 := by
        rw [(ex_6_3_bellman N).2 (k + 1) hlt 1, max_eq_left hge1]
      have hV2 : two_V N (k + 1) 2 = two_g N (k + 1) 2 := by
        rw [(ex_6_3_bellman N).2 (k + 1) hlt 2, max_eq_left hge2]
      have hV0 := two_V0 (N := N) (k := k + 1) (by omega) hlt
      unfold two_W
      rw [hV1, hV2, hV0, hIH, two_L_step hN hk1]
  have hL := ex_6_3_lower hN k hk1 hk
  have hdiff := two_g2_sub_L (N := N) (k := k) hN
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hfin : 2 * N + 1 ≤ 3 * k → two_W N k = two_L N k ∧
      two_V N k 1 = two_g N k 1 ∧ two_V N k 2 = two_g N k 2 := by
    intro h3
    have hW := exact (N - 1 - k) k rfl hk1 hk h3
    have hle2 : two_W N k ≤ two_g N k 2 := by
      rw [hW, ← sub_nonneg, hdiff]
      have : (2 * N + 1 : ℝ) ≤ 3 * k := by exact_mod_cast h3
      exact div_nonneg (mul_nonneg hkpos.le (by linarith)) hden.le
    have hlt : k < N := by omega
    refine ⟨hW, ?_, ?_⟩
    · rw [(ex_6_3_bellman N).2 k hlt 1,
        max_eq_left (hle2.trans (two_g_mono (N := N) (k := k) hlt).2.2)]
    · rw [(ex_6_3_bellman N).2 k hlt 2, max_eq_left hle2]
  refine ⟨⟨fun h => ?_, fun h3 => ?_⟩, hfin⟩
  · by_contra h3
    have h3' : (3 * k : ℝ) < 2 * N + 1 := by exact_mod_cast (lt_of_not_ge h3)
    have hneg : two_g N k 2 - two_L N k < 0 := by
      rw [hdiff]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hkpos (by linarith)) hden
    linarith
  · have := (hfin h3).1
    rw [this, ← sub_nonneg, hdiff]
    have : (2 * N + 1 : ℝ) ≤ 3 * k := by exact_mod_cast h3
    exact div_nonneg (mul_nonneg hkpos.le (by linarith)) hden.le

/-! ### Exercise 6.4 -/

/-- The Bellman equation of Exercise 6.4, by time to go `n = N − k`; the state is the relative
rank `r`. -/
noncomputable def rank_val (N : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun r => r
  | n + 1 => fun r =>
    min ((r : ℝ) * (N + 1) / (((N - (n + 1) : ℕ) : ℝ) + 1))
      (1 / (((N - (n + 1) : ℕ) : ℝ) + 1) *
        ∑ i ∈ Finset.range (N - (n + 1) + 1), rank_val N n (i + 1))

/-- `V_k(r)` of Exercise 6.4: the minimal expected rank at date `k` with relative rank `r`. -/
noncomputable def rank_V (N k r : ℕ) : ℝ := rank_val N (N - k) r

/-- The continuation value `W_k = (1/(k + 1)) ∑_{r=1}^{k+1} V_{k+1}(r)`. -/
noncomputable def rank_W (N k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1) * ∑ i ∈ Finset.range (k + 1), rank_V N (k + 1) (i + 1)

/-- **Exercise 6.4: the Bellman equation** (Miao, p. 189): `V_N(r) = r` and
`V_k(r) = min{r(N + 1)/(k + 1), W_k}` for `k < N`. -/
theorem ex_6_4_bellman (N : ℕ) :
    (∀ r, rank_V N N r = r) ∧
      ∀ k < N, ∀ r, rank_V N k r = min ((r : ℝ) * (N + 1) / ((k : ℝ) + 1)) (rank_W N k) := by
  refine ⟨fun r => by simp [rank_V, rank_val], fun k hk r => ?_⟩
  have e1 : N - k = (N - (k + 1)) + 1 := by omega
  have e2 : N - (N - (k + 1) + 1) = k := by omega
  unfold rank_V rank_W
  rw [e1]
  simp only [rank_val, e2]
  rfl

theorem rank_V_nonneg (N : ℕ) : ∀ k r, 0 ≤ rank_V N k r := by
  have : ∀ n r, 0 ≤ rank_val N n r := by
    intro n
    induction n with
    | zero => intro r; simp only [rank_val]; positivity
    | succ n ih =>
      intro r
      simp only [rank_val]
      exact le_min (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => ih _))
  exact fun k r => this _ r

theorem rank_W_nonneg (N k : ℕ) : 0 ≤ rank_W N k :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => rank_V_nonneg N _ _)

/-- `W_k ≤ W_{k+1}`: an earlier date offers more options. -/
theorem rank_W_mono {N k : ℕ} (hk : k + 1 < N) : rank_W N k ≤ rank_W N (k + 1) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold rank_W
  have : ∀ i ∈ Finset.range (k + 1), rank_V N (k + 1) (i + 1) ≤ rank_W N (k + 1) := by
    intro i _
    rw [(ex_6_4_bellman N).2 (k + 1) hk]
    exact min_le_right _ _
  have hs := Finset.sum_le_sum this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  push_cast at hs
  calc 1 / ((k : ℝ) + 1) * ∑ i ∈ Finset.range (k + 1), rank_V N (k + 1) (i + 1)
      ≤ 1 / ((k : ℝ) + 1) * (((k : ℝ) + 1) * rank_W N (k + 1)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = rank_W N (k + 1) := by field_simp
    _ = _ := rfl

/-- **Exercise 6.4: the threshold form** (Miao, p. 189). At a date `k < N`, stopping is optimal
(`r(N + 1)/(k + 1) ≤ W_k`) exactly for the relative ranks `r ≤ s_k = (k + 1)W_k/(N + 1)`, and the
threshold `s_k` is nondecreasing in `k` (for `k + 1 < N`). -/
theorem ex_6_4_threshold {N k : ℕ} (r : ℕ) :
    ((r : ℝ) * (N + 1) / ((k : ℝ) + 1) ≤ rank_W N k ↔
      (r : ℝ) ≤ ((k : ℝ) + 1) * rank_W N k / (N + 1)) ∧
    (k + 1 < N → ((k : ℝ) + 1) * rank_W N k / (N + 1) ≤
      ((k : ℝ) + 1 + 1) * rank_W N (k + 1) / (N + 1)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨?_, fun hk' => ?_⟩
  · rw [div_le_iff₀ hk, le_div_iff₀ hN]
    constructor <;> intro h <;> linarith
  · refine div_le_div_of_nonneg_right ?_ hN.le
    have h1 := rank_W_mono hk'
    have h2 := rank_W_nonneg N (k + 1)
    nlinarith

theorem rank_sum_range (n : ℕ) : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Exercise 6.4 at the last decision date: `W_{N−1} = (N + 1)/2`, the mean rank of the last
candidate. -/
theorem ex_6_4_last {N : ℕ} (hN : 1 ≤ N) : rank_W N (N - 1) = ((N : ℝ) + 1) / 2 := by
  unfold rank_W
  rw [Nat.sub_add_cancel hN]
  simp only [(ex_6_4_bellman N).1]
  push_cast
  rw [rank_sum_range]
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [hN]; ring
  rw [hc, show (N : ℝ) - 1 + 1 = N by ring]
  have hNne : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp

/-- **Exercise 6.4 for `N = 3`**: the minimal expected rank is `V_1(1) = 5/3` (reject the first
candidate; accept the second if it is better than the first; otherwise take the third). -/
theorem ex_6_4_three : rank_V 3 1 1 = 5 / 3 := by
  simp only [rank_V, rank_val, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end Miao.FiniteHorizonDP
