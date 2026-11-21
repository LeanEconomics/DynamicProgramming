/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.LCDeterministic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Zhang's minimum consumption function, deterministic case (Miao §22.1.3, pp. 780–781)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.3, pp. 780–781, and Exercise 22.1,
p. 797, for a deterministic bounded utility-of-endowment sequence `x_t = u(y_t)`. With
`B_τ = Σ_{j<τ} β^j`, `S_t(τ) = Σ_{j<τ} β^j x_{t+j}` and the average `A_t(τ) = S_t(τ)/B_τ`, the
minimum consumption level at `t` in utility units is `m_t = inf_{τ ≥ 1} A_t(τ)` (`lc_m`), so
that `h(y_t) = u⁻¹(m_t)`. `lc_run m k j = max_{k ≤ s ≤ k+j} m_s` is the running maximum.

Main result (`lc_zhang_identity`): for every `k`,
`Σ_j β^j max_{k ≤ s ≤ k+j} m_s = U_k = Σ_j β^j x_{k+j}`.
This is the identity behind Zhang's characterisation (22.11): the consumption path
`c_t = max{c_{t-1}, h(y_t)}`, `c_0 = h(y_0)`, delivers at least the autarky value at every date
and exactly the autarky value at every date at which consumption is reset to `h(y_t)`.

The proof decomposes time into blocks between successive strict increases of `m`: on a finite
block `[t, t+T)` the average of `x` equals `m_t` (`lc_block_eq`), and on an infinite final block
`(1 − β)U_t = m_t` (`lc_tail_eq`).
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- `B_τ = Σ_{j<τ} β^j`. -/
def lc_B (β : ℝ) (τ : ℕ) : ℝ := ∑ j ∈ Finset.range τ, β ^ j

/-- `S_t(τ) = Σ_{j<τ} β^j x_{t+j}`. -/
def lc_S (β : ℝ) (x : ℕ → ℝ) (t τ : ℕ) : ℝ := ∑ j ∈ Finset.range τ, β ^ j * x (t + j)

/-- The discounted average `A_t(τ) = S_t(τ)/B_τ` (Miao, Exercise 22.1(c), p. 798). -/
noncomputable def lc_A (β : ℝ) (x : ℕ → ℝ) (t τ : ℕ) : ℝ := lc_S β x t τ / lc_B β τ

/-- The minimum consumption level in utility units, `m_t = inf_{τ ≥ 1} A_t(τ)`
(Miao, p. 781 and Exercise 22.1(c), p. 798). -/
noncomputable def lc_m (β : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ := ⨅ τ : ℕ, lc_A β x t (τ + 1)

/-- The running maximum `max_{k ≤ s ≤ k+j} m_s`. -/
def lc_run (m : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => m k
  | j + 1 => max (lc_run m k j) (m (k + j + 1))

theorem lc_B_add (β : ℝ) (τ σ : ℕ) : lc_B β (τ + σ) = lc_B β τ + β ^ τ * lc_B β σ := by
  unfold lc_B
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp_rw [pow_add]

theorem lc_S_add (β : ℝ) (x : ℕ → ℝ) (t τ σ : ℕ) :
    lc_S β x t (τ + σ) = lc_S β x t τ + β ^ τ * lc_S β x (t + τ) σ := by
  unfold lc_S
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, add_assoc]
  ring

theorem lc_B_mul (β : ℝ) (τ : ℕ) : lc_B β τ * (1 - β) = 1 - β ^ τ := by
  unfold lc_B
  have := geom_sum_mul β τ
  linarith [show (∑ i ∈ Finset.range τ, β ^ i) * (1 - β) =
    -((∑ i ∈ Finset.range τ, β ^ i) * (β - 1)) by ring]

theorem lc_B_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (τ : ℕ) : 0 ≤ lc_B β τ :=
  Finset.sum_nonneg fun j _ => pow_nonneg hβ0 j

theorem lc_B_ge_one {β : ℝ} (hβ0 : 0 ≤ β) {τ : ℕ} (hτ : 1 ≤ τ) : 1 ≤ lc_B β τ := by
  have := Finset.single_le_sum (f := fun j => β ^ j) (fun j _ => pow_nonneg hβ0 j)
    (Finset.mem_range.mpr (by omega : 0 < τ))
  simpa [lc_B] using this

theorem lc_B_mul_le {β : ℝ} (hβ0 : 0 ≤ β) (τ : ℕ) : lc_B β τ * (1 - β) ≤ 1 := by
  rw [lc_B_mul]; linarith [pow_nonneg hβ0 τ]

theorem lc_S_abs_le {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t τ : ℕ) : |lc_S β x t τ| ≤ M * lc_B β τ := by
  unfold lc_S lc_B
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), mul_comm]
  exact mul_le_mul_of_nonneg_right (hx _) (pow_nonneg hβ0 j)

theorem lc_A_abs_le {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) {τ : ℕ} (hτ : 1 ≤ τ) : |lc_A β x t τ| ≤ M := by
  have hB := lc_B_ge_one hβ0 hτ
  unfold lc_A
  rw [abs_div, abs_of_pos (show 0 < lc_B β τ by linarith),
    div_le_iff₀ (show 0 < lc_B β τ by linarith)]
  exact lc_S_abs_le hβ0 hx t τ

theorem lc_A_bddBelow {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) : BddBelow (Set.range fun τ : ℕ => lc_A β x t (τ + 1)) :=
  ⟨-M, by rintro _ ⟨τ, rfl⟩; exact (abs_le.mp (lc_A_abs_le hβ0 hx t (by omega))).1⟩

theorem lc_m_le_A {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) {τ : ℕ} (hτ : 1 ≤ τ) : lc_m β x t ≤ lc_A β x t τ := by
  obtain ⟨σ, rfl⟩ : ∃ σ, τ = σ + 1 := ⟨τ - 1, by omega⟩
  exact ciInf_le (lc_A_bddBelow hβ0 hx t) σ

theorem lc_m_abs_le {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) : |lc_m β x t| ≤ M := by
  rw [abs_le]
  constructor
  · exact le_ciInf fun τ => (abs_le.mp (lc_A_abs_le hβ0 hx t (by omega))).1
  · exact (lc_m_le_A hβ0 hx t le_rfl).trans (abs_le.mp (lc_A_abs_le hβ0 hx t le_rfl)).2

/-- `m_t ≤ x_t` (take `τ = 1`). -/
theorem lc_m_le_x {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t : ℕ) : lc_m β x t ≤ x t := by
  have := lc_m_le_A hβ0 hx t le_rfl
  simpa [lc_A, lc_S, lc_B] using this

theorem lc_S_ge_m {β : ℝ} (hβ0 : 0 ≤ β) {x : ℕ → ℝ} {M : ℝ} (hx : ∀ t, |x t| ≤ M)
    (t τ : ℕ) : lc_m β x t * lc_B β τ ≤ lc_S β x t τ := by
  rcases Nat.eq_zero_or_pos τ with rfl | hτ
  · simp [lc_B, lc_S]
  · have h := lc_m_le_A hβ0 hx t hτ
    have hB := lc_B_ge_one hβ0 hτ
    unfold lc_A at h
    rwa [le_div_iff₀ (by linarith)] at h

/-- The averages converge to `(1 − β) U_t`. -/
theorem lc_A_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) :
    Tendsto (fun τ => lc_A β x t τ) atTop (𝓝 ((1 - β) * lc_detValue β x t)) := by
  have hS : Tendsto (fun τ => lc_S β x t τ) atTop (𝓝 (lc_detValue β x t)) :=
    (lc_summable_geom hβ0 hβ1 (x := fun j => x (t + j)) (fun j => hx _)).hasSum.tendsto_sum_nat
  have hB : Tendsto (fun τ => lc_B β τ) atTop (𝓝 (1 - β)⁻¹) :=
    (hasSum_geometric_of_lt_one hβ0 hβ1).tendsto_sum_nat
  have h1 : (1 - β)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have := hS.div hB h1
  rw [div_inv_eq_mul, mul_comm] at this
  exact this

/-- If `m_t ≤ m̄` and the averages from some horizon `T` on are at least `m̄ + δ`, then some
average before `T` is at most `m̄`. -/
theorem lc_exists_low {β : ℝ} {x : ℕ → ℝ} (T : ℕ) : ∀ t mb δ, lc_m β x t ≤ mb → 0 < δ →
      (∀ τ, 1 ≤ τ → T ≤ τ → mb + δ ≤ lc_A β x t τ) →
      ∃ τ0, 1 ≤ τ0 ∧ τ0 < T ∧ lc_A β x t τ0 ≤ mb := by
  have hall : ∀ t mb δ, lc_m β x t ≤ mb → 0 < δ →
      (∀ τ, 1 ≤ τ → mb + δ ≤ lc_A β x t τ) → False := by
    intro t mb δ hm hδ h
    have : mb + δ ≤ lc_m β x t := le_ciInf fun τ => h (τ + 1) (by omega)
    linarith
  induction T with
  | zero =>
    intro t mb δ hm hδ h
    exact (hall t mb δ hm hδ fun τ h1 => h τ h1 (Nat.zero_le τ)).elim
  | succ T ih =>
    intro t mb δ hm hδ h
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · exact (hall t mb δ hm hδ fun τ h1 => h τ h1 h1).elim
    by_cases hA : lc_A β x t T ≤ mb
    · exact ⟨T, hT, by omega, hA⟩
    push Not at hA
    obtain ⟨τ0, h1, h2, h3⟩ := ih t mb (min δ (lc_A β x t T - mb)) hm
      (lt_min hδ (by linarith)) (fun τ hτ1 hτT => by
        rcases hτT.lt_or_eq with h' | h'
        · exact (add_le_add_right (min_le_left _ _) _).trans (h τ hτ1 h')
        · rw [← h']; linarith [min_le_right δ (lc_A β x t T - mb)])
    exact ⟨τ0, h1, by omega, h3⟩

/-- On a block `[t, t+T)` on which `m ≤ m̄`, ending with `m_{t+T} > m̄`, the discounted sum of
`x` is at most `m̄ B_T`. -/
theorem lc_block_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (T : ℕ) : 1 ≤ T → ∀ t mb, lc_m β x t ≤ mb →
      (∀ s, 1 ≤ s → s < T → lc_m β x (t + s) ≤ mb) → mb < lc_m β x (t + T) →
      lc_S β x t T ≤ mb * lc_B β T := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  intro hT t mb hm hs hTm
  by_contra hgt
  push Not at hgt
  set ε := lc_S β x t T - mb * lc_B β T with hε
  have hε0 : 0 < ε := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hbig : ∀ τ, 1 ≤ τ → T ≤ τ → mb + ε * (1 - β) ≤ lc_A β x t τ := by
    intro τ hτ1 hτT
    obtain ⟨σ, rfl⟩ : ∃ σ, τ = T + σ := ⟨τ - T, by omega⟩
    have hBpos : 0 < lc_B β (T + σ) := by linarith [lc_B_ge_one hβ0 hτ1]
    unfold lc_A
    rw [le_div_iff₀ hBpos, lc_S_add, lc_B_add]
    have h2 := lc_S_ge_m hβ0 hx (t + T) σ
    have h3 : mb * lc_B β σ ≤ lc_m β x (t + T) * lc_B β σ :=
      mul_le_mul_of_nonneg_right hTm.le (lc_B_nonneg hβ0 σ)
    have h4 : β ^ T * (mb * lc_B β σ) ≤ β ^ T * lc_S β x (t + T) σ :=
      mul_le_mul_of_nonneg_left (h3.trans h2) (pow_nonneg hβ0 T)
    have h5 := lc_B_mul_le hβ0 (T + σ)
    rw [lc_B_add] at h5
    nlinarith
  obtain ⟨τ0, h1, h2, h3⟩ := lc_exists_low T t mb (ε * (1 - β)) hm
    (mul_pos hε0 h1β) hbig
  have hlow : lc_S β x t τ0 ≤ mb * lc_B β τ0 := by
    unfold lc_A at h3
    rwa [div_le_iff₀ (by linarith [lc_B_ge_one hβ0 h1])] at h3
  have hIH := ih (T - τ0) (by omega) (by omega) (t + τ0) mb (hs τ0 h1 h2)
    (fun s hs1 hs2 => by rw [add_assoc]; exact hs (τ0 + s) (by omega) (by omega))
    (by rw [show t + τ0 + (T - τ0) = t + T by omega]; exact hTm)
  have hsplitS := lc_S_add β x t τ0 (T - τ0)
  have hsplitB := lc_B_add β τ0 (T - τ0)
  rw [show τ0 + (T - τ0) = T by omega] at hsplitS hsplitB
  have := mul_le_mul_of_nonneg_left hIH (pow_nonneg hβ0 τ0)
  have e : mb * lc_B β T = mb * lc_B β τ0 + β ^ τ0 * (mb * lc_B β (T - τ0)) := by
    rw [hsplitB]; ring
  linarith

/-- On a finite block between strict increases of `m` the average of `x` equals `m_t`. -/
theorem lc_block_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (T : ℕ) (hT : 1 ≤ T) (t : ℕ)
    (hs : ∀ s, 1 ≤ s → s < T → lc_m β x (t + s) ≤ lc_m β x t)
    (hTm : lc_m β x t < lc_m β x (t + T)) :
    lc_S β x t T = lc_m β x t * lc_B β T :=
  le_antisymm (lc_block_le hβ0 hβ1 hx T hT t _ le_rfl hs hTm) (lc_S_ge_m hβ0 hx t T)

/-- If `m ≤ m̄` from `t` on, then `(1 − β) U_t − m̄ ≤ (M + |m̄|) β^k` for every `k`. -/
theorem lc_tail_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (mb : ℝ) (k : ℕ) : ∀ t, (∀ s, lc_m β x (t + s) ≤ mb) →
      (1 - β) * lc_detValue β x t - mb ≤ (M + |mb|) * β ^ k := by
  have h1β : 0 < 1 - β := by linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hx 0)
  induction k with
  | zero =>
    intro t _
    have hU := abs_le.mp (lc_detValue_abs_le hβ0 hβ1 hx t)
    have : (1 - β) * lc_detValue β x t ≤ M := by
      have := mul_le_mul_of_nonneg_left hU.2 h1β.le
      rwa [mul_div_cancel₀ _ h1β.ne'] at this
    simp only [pow_zero, mul_one]
    linarith [neg_abs_le mb]
  | succ k ih =>
    intro t hs
    set η := (1 - β) * lc_detValue β x t - mb
    have hC : 0 ≤ (M + |mb|) * β ^ (k + 1) :=
      mul_nonneg (add_nonneg hM (abs_nonneg _)) (pow_nonneg hβ0 _)
    by_cases hη : η ≤ 0
    · linarith
    push Not at hη
    have hev := (lc_A_tendsto hβ0 hβ1 hx t).eventually
      (Ioi_mem_nhds (show mb + η / 2 < (1 - β) * lc_detValue β x t by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨τ0, h1, -, h3⟩ := lc_exists_low N t mb (η / 2)
      (by simpa using hs 0) (by linarith) (fun τ _ hτ => (hN τ hτ).le)
    have hlow : lc_S β x t τ0 ≤ mb * lc_B β τ0 := by
      unfold lc_A at h3
      rwa [div_le_iff₀ (by linarith [lc_B_ge_one hβ0 h1])] at h3
    have hIH := ih (t + τ0) (fun s => by rw [add_assoc]; exact hs (τ0 + s))
    have hsplit := lc_detValue_split hβ0 hβ1 hx t τ0
    have hB := lc_B_mul β τ0
    have hpow : β ^ τ0 ≤ β := pow_le_of_le_one hβ0 hβ1.le (by omega)
    have hCk : 0 ≤ (M + |mb|) * β ^ k :=
      mul_nonneg (add_nonneg hM (abs_nonneg _)) (pow_nonneg hβ0 _)
    have key : η ≤ β ^ τ0 * ((1 - β) * lc_detValue β x (t + τ0) - mb) := by
      simp only [η]
      rw [hsplit]
      change (1 - β) * (lc_S β x t τ0 + β ^ τ0 * lc_detValue β x (t + τ0)) - mb ≤ _
      have e2 : (1 - β) * (mb * lc_B β τ0) = mb * (1 - β ^ τ0) := by rw [← hB]; ring
      have := mul_le_mul_of_nonneg_left hlow h1β.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hIH (pow_nonneg hβ0 τ0)
    have h3 := mul_le_mul_of_nonneg_right hpow hCk
    rw [pow_succ]
    nlinarith

/-- On an infinite final block (`m_{t+s} ≤ m_t` for all `s`), `(1 − β) U_t = m_t`. -/
theorem lc_tail_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) (hs : ∀ s, lc_m β x (t + s) ≤ lc_m β x t) :
    (1 - β) * lc_detValue β x t = lc_m β x t := by
  apply le_antisymm
  · have hlim : Tendsto (fun k : ℕ => (M + |lc_m β x t|) * β ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul (M + |lc_m β x t|)
    have := ge_of_tendsto' hlim fun k => lc_tail_le hβ0 hβ1 hx (lc_m β x t) k t hs
    linarith
  · exact ge_of_tendsto (lc_A_tendsto hβ0 hβ1 hx t)
      (eventually_atTop.mpr ⟨1, fun τ hτ => lc_m_le_A hβ0 hx t hτ⟩)

theorem lc_run_succ (m : ℕ → ℝ) (k j : ℕ) :
    lc_run m k (j + 1) = max (lc_run m k j) (m (k + j + 1)) := rfl

theorem lc_run_ge (m : ℕ → ℝ) (k j : ℕ) : m (k + j) ≤ lc_run m k j ∧ m k ≤ lc_run m k j := by
  induction j with
  | zero => simp [lc_run]
  | succ j ih =>
    rw [lc_run_succ]
    exact ⟨le_max_of_le_right le_rfl, le_max_of_le_left ih.2⟩

theorem lc_run_mono (m : ℕ → ℝ) (k : ℕ) : Monotone (lc_run m k) :=
  monotone_nat_of_le_succ fun j => by rw [lc_run_succ]; exact le_max_left _ _

theorem lc_run_add (m : ℕ → ℝ) (k i j : ℕ) :
    lc_run m k (i + j) = max (lc_run m k i) (lc_run m (k + i) j) := by
  induction j with
  | zero =>
    simp only [add_zero, lc_run]
    exact (max_eq_left (by simpa using (lc_run_ge m k i).1)).symm
  | succ j ih =>
    rw [← add_assoc, lc_run_succ, ih, lc_run_succ, max_assoc]
    congr 3
    ring

theorem lc_run_eq_first (m : ℕ → ℝ) (k j : ℕ) (h : ∀ s, 1 ≤ s → s ≤ j → m (k + s) ≤ m k) :
    lc_run m k j = m k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [lc_run_succ, ih (fun s h1 h2 => h s h1 (by omega))]
    exact max_eq_left (h (j + 1) (by omega) le_rfl)

theorem lc_run_abs_le (m : ℕ → ℝ) {M : ℝ} (hm : ∀ t, |m t| ≤ M) (k j : ℕ) :
    |lc_run m k j| ≤ M := by
  induction j with
  | zero => exact hm k
  | succ j ih =>
    rw [lc_run_succ]
    rcases max_choice (lc_run m k j) (m (k + j + 1)) with h | h <;> rw [h]
    · exact ih
    · exact hm _

/-- **Zhang's identity** (Miao, §22.1.3, pp. 780–781, and Exercise 22.1(c), p. 798, deterministic
case): for every date `k`, `Σ_j β^j max_{k ≤ s ≤ k+j} m_s = Σ_j β^j x_{k+j} = U_k`. -/
theorem lc_zhang_identity {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (k : ℕ) :
    lc_detValue β (lc_run (lc_m β x) k) 0 = lc_detValue β x k := by
  classical
  set m := lc_m β x
  have hm : ∀ t, |m t| ≤ M := lc_m_abs_le hβ0 hx
  have hrun := lc_run_abs_le m hm
  have h1β : 0 < 1 - β := by linarith
  set C := 2 * (M / (1 - β))
  have hbound : ∀ n k, |lc_detValue β x k - lc_detValue β (lc_run m k) 0| ≤ C * β ^ n := by
    intro n
    induction n with
    | zero =>
      intro k
      simp only [pow_zero, mul_one, C]
      refine (abs_sub _ _).trans ?_
      linarith [lc_detValue_abs_le hβ0 hβ1 hx k, lc_detValue_abs_le hβ0 hβ1 (hrun k) 0]
    | succ n ih =>
      intro k
      have hC : 0 ≤ C * β ^ (n + 1) := by
        have : 0 ≤ M := (abs_nonneg _).trans (hx 0)
        exact mul_nonneg (by positivity) (pow_nonneg hβ0 _)
      by_cases hex : ∃ s, 1 ≤ s ∧ m k < m (k + s)
      · set T := Nat.find hex
        have hT : 1 ≤ T ∧ m k < m (k + T) := Nat.find_spec hex
        have hbefore : ∀ s, 1 ≤ s → s < T → m (k + s) ≤ m k := by
          intro s h1 h2
          have := Nat.find_min hex h2
          push Not at this
          exact this h1
        have hS := lc_block_eq hβ0 hβ1 hx T hT.1 k hbefore hT.2
        have hrunT : ∀ j, lc_run m k (T + j) = lc_run m (k + T) j := by
          intro j
          rw [lc_run_add]
          have : lc_run m k T = m (k + T) := by
            obtain ⟨T', hT'⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
            have h2 : m k < m (k + (T' + 1)) := hT' ▸ hT.2
            rw [hT', lc_run_succ, lc_run_eq_first m k T' (fun s h1 h2 => hbefore s h1 (by omega)),
              show k + T' + 1 = k + (T' + 1) by ring]
            exact max_eq_right h2.le
          rw [this]
          exact max_eq_right (by simpa using (lc_run_ge m (k + T) j).2)
        have hW : lc_detValue β (lc_run m k) 0 =
            m k * lc_B β T + β ^ T * lc_detValue β (lc_run m (k + T)) 0 := by
          rw [lc_detValue_split hβ0 hβ1 (hrun k) 0 T]
          congr 1
          · unfold lc_B
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [zero_add, lc_run_eq_first m k j (fun s h1 h2 =>
              hbefore s h1 (by have := Finset.mem_range.mp hj; omega))]
            ring
          · congr 1
            unfold lc_detValue
            refine tsum_congr fun j => ?_
            rw [zero_add, zero_add, hrunT]
        have hU := lc_detValue_split hβ0 hβ1 hx k T
        change lc_detValue β x k = lc_S β x k T + _ at hU
        rw [hS] at hU
        rw [hU, hW]
        have hpow : β ^ T ≤ β := pow_le_of_le_one hβ0 hβ1.le (by omega)
        have := ih (k + T)
        rw [show m k * lc_B β T + β ^ T * lc_detValue β x (k + T) -
            (m k * lc_B β T + β ^ T * lc_detValue β (lc_run m (k + T)) 0) =
            β ^ T * (lc_detValue β x (k + T) - lc_detValue β (lc_run m (k + T)) 0) by ring,
          abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
        have hCn : 0 ≤ C * β ^ n := by
          have : 0 ≤ M := (abs_nonneg _).trans (hx 0)
          exact mul_nonneg (by positivity) (pow_nonneg hβ0 _)
        calc β ^ T * |lc_detValue β x (k + T) - lc_detValue β (lc_run m (k + T)) 0|
            ≤ β ^ T * (C * β ^ n) := mul_le_mul_of_nonneg_left this (pow_nonneg hβ0 T)
          _ ≤ β * (C * β ^ n) := mul_le_mul_of_nonneg_right hpow hCn
          _ = C * β ^ (n + 1) := by ring
      · push Not at hex
        have hconst : ∀ j, lc_run m k j = m k := fun j =>
          lc_run_eq_first m k j fun s h1 _ => hex s h1
        have hW : lc_detValue β (lc_run m k) 0 = m k / (1 - β) := by
          rw [← lc_detValue_const hβ0 hβ1 (m k) 0]
          unfold lc_detValue
          exact tsum_congr fun j => by rw [hconst]
        have hU : (1 - β) * lc_detValue β x k = m k := lc_tail_eq hβ0 hβ1 hx k (fun s => by
          rcases Nat.eq_zero_or_pos s with rfl | hs
          · simp
          · exact hex s hs)
        rw [hW, ← hU, mul_div_cancel_left₀ _ h1β.ne', sub_self, abs_zero]
        exact hC
  have hlim : Tendsto (fun n : ℕ => C * β ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul C
  have h0 := ge_of_tendsto' hlim fun n => hbound n k
  have := abs_nonneg (lc_detValue β x k - lc_detValue β (lc_run m k) 0)
  have he : |lc_detValue β x k - lc_detValue β (lc_run m k) 0| = 0 := le_antisymm h0 this
  rw [abs_eq_zero, sub_eq_zero] at he
  exact he.symm

end Miao.RecursiveContracts
