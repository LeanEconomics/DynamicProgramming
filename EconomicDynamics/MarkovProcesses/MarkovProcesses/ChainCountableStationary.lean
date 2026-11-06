/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainCountable
import MarkovProcesses.ChainStationary

/-!
# Countable-state Markov chains: stationary distributions and Theorem 3.1.5

Miao, §3.1.3, pp. 97–99. Setting and notation as in `ChainCountable`.

* **Definition 3.1.5** for countable chains: `mc_IsInvariantE` (`μ = μP` for a
  `[0, ∞]`-valued row vector), `mc_IsStationaryE` (an invariant probability vector).
* The cycle measure of a state `i`, `mc_cycleE P i k = Σₙ Pr(Xₙ₊₁ = k, τᵢ ≥ n + 1 | X₀ = i)`,
  the expected number of visits to `k` during an excursion from `i`: it is invariant when `i` is
  recurrent (`mc_cycleE_invariant`), it is the smallest invariant measure with mass `1` at `i`
  (`mc_cycleE_le`), and its total mass is the mean return time `E[τᵢ | X₀ = i]`
  (`mc_cycleE_mass`).
* `mc_recurrent_of_stationary`: an irreducible chain with a stationary distribution is
  recurrent; `mc_stationary_eq_inv`: then every stationary distribution satisfies
  `μⱼ = 1/E[τⱼ | X₀ = j]` and every state is positive recurrent.
* **Theorem 3.1.5** (p. 99), for an irreducible chain:
  (a) `theorem_3_1_5a`: if the chain is transient, `Σₖ p⁽ᵏ⁾ᵢⱼ < ∞` and `p⁽ᵏ⁾ᵢⱼ → 0` for all
  `i, j`, and there is no stationary distribution;
  (b) `theorem_3_1_5b`: if it is null recurrent, there is no stationary distribution,
  `Σₖ p⁽ᵏ⁾ᵢⱼ = ∞` and `E[τⱼ | X₀ = j] = ∞` for all `i, j`;
  (c) `theorem_3_1_5c`: if it is positive recurrent, there is a unique stationary distribution
  and `μⱼ = 1/E[τⱼ | X₀ = j] > 0` for all `j`;
  `theorem_3_1_5_trichotomy`: exactly one of these holds, for all states at once.
* Finite chains (p. 99: "for a finite state space, cases (a)–(b) cannot happen"):
  `theorem_3_1_5_finite`: an irreducible finite chain (a real transition matrix) is positive
  recurrent and its stationary distribution is `μⱼ = 1/E[τⱼ | X₀ = j]`; the bridge is
  `mc_toE` with `mc_powE_toE` (`p⁽ⁿ⁾` computed in `[0, ∞]` and in `ℝ` agree).

**Not formalised.** The limits `p⁽ᵏ⁾ᵢⱼ → 0` in case (b) and `p⁽ᵏ⁾ᵢⱼ → 1/E[τⱼ | X₀ = j]` in case
(c) (Billingsley's Theorem 8.8; they need aperiodicity and the renewal theorem or a coupling
argument). Aperiodicity is not needed for anything proved here. For finite chains the limit in
(c) is Theorem 3.1.3 together with Theorem 3.1.4.
-/

namespace Miao.MarkovProcesses

open Filter Topology Matrix
open scoped ENNReal

variable {S : Type*} [DecidableEq S] {P : S → S → ℝ≥0∞}

/-! ### Invariant measures -/

/-- An **invariant measure** of `P`: a `[0, ∞]`-valued row vector with `μ = μP`. -/
def mc_IsInvariantE (P : S → S → ℝ≥0∞) (μ : S → ℝ≥0∞) : Prop := ∀ j, ∑' i, μ i * P i j = μ j

/-- **Definition 3.1.5** (Miao, p. 94) for countable chains: a **stationary distribution** is an
invariant probability vector. -/
def mc_IsStationaryE (P : S → S → ℝ≥0∞) (μ : S → ℝ≥0∞) : Prop :=
  mc_IsInvariantE P μ ∧ ∑' i, μ i = 1

/-- An invariant measure is invariant under every power: `μ = μPⁿ`. -/
theorem mc_IsInvariantE.pow {μ : S → ℝ≥0∞} (hμ : mc_IsInvariantE P μ) (n : ℕ) (j : S) :
    ∑' i, μ i * mc_powE P n i j = μ j := by
  induction n generalizing j with
  | zero =>
    simp only [mc_powE, mc_idE, mul_ite, mul_one, mul_zero]
    rw [tsum_eq_single j fun i hi => by simp [hi]]
    simp
  | succ n ih =>
    rw [← hμ j]
    simp only [mc_powE_succ', mc_mulE, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => ?_
    rw [← ih l, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun i => by ring

/-- `μᵢ p⁽ⁿ⁾ᵢⱼ ≤ μⱼ`. -/
theorem mc_IsInvariantE.le {μ : S → ℝ≥0∞} (hμ : mc_IsInvariantE P μ) (n : ℕ) (i j : S) :
    μ i * mc_powE P n i j ≤ μ j := by
  rw [← hμ.pow n j]; exact ENNReal.le_tsum (f := fun i => μ i * mc_powE P n i j) i

/-- A stationary distribution of an irreducible chain charges every state. -/
theorem mc_stationaryE_pos {μ : S → ℝ≥0∞} (hirr : mc_IsIrreducibleE P)
    (hμ : mc_IsStationaryE P μ) (j : S) : 0 < μ j := by
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    have := hμ.2
    simp [h] at this
  rcases hirr i j with rfl | ⟨⟨m, -, hm⟩, -⟩
  · exact pos_iff_ne_zero.2 hi
  · exact lt_of_lt_of_le (ENNReal.mul_pos hi hm.ne') (hμ.1.le m i j)

omit [DecidableEq S] in
/-- The entries of a stationary distribution are at most one. -/
theorem mc_stationaryE_le_one {μ : S → ℝ≥0∞} (hμ : mc_IsStationaryE P μ) (j : S) : μ j ≤ 1 := by
  rw [← hμ.2]; exact ENNReal.le_tsum j

/-- If `i → j` then `Pr(τⱼ < ∞ | X₀ = i) > 0`. -/
theorem mc_hitE_pos {i j : S} (h : mc_AccessibleE P i j) : 0 < mc_hitE P i j := by
  obtain ⟨m, hm, hm'⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [mc_first_entrance] at hm'
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm'.ne'
  have hk' : 0 < mc_fpE P j k i := pos_iff_ne_zero.2 (left_ne_zero_of_mul hk)
  exact hk'.trans_le (ENNReal.le_tsum (f := fun n => mc_fpE P j n i) k)

/-- `Σₙ p⁽ⁿ⁺¹⁾ₐⱼ ≤ 1 + Σₙ p⁽ⁿ⁺¹⁾ⱼⱼ`. -/
theorem mc_visitsE_le (hP : mc_IsStochasticE P) (a j : S) :
    mc_visitsE P a j ≤ 1 + mc_visitsE P j j := by
  rw [mc_visits_eq]
  calc mc_hitE P a j * (1 + mc_visitsE P j j) ≤ 1 * (1 + mc_visitsE P j j) := by
        gcongr; exact mc_hitE_le_one hP a j
    _ = _ := one_mul _

/-- Miao, p. 98: an irreducible chain with a stationary distribution is recurrent (if `j` were
transient, `Σₙ μⱼ = Σᵢ μᵢ Σₙ p⁽ⁿ⁺¹⁾ᵢⱼ ≤ 1 + Σₙ p⁽ⁿ⁺¹⁾ⱼⱼ < ∞`). -/
theorem mc_recurrent_of_stationary (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P)
    {μ : S → ℝ≥0∞} (hμ : mc_IsStationaryE P μ) (j : S) : mc_IsRecurrentE P j := by
  by_contra hrec
  have htr : mc_IsTransientE P j := by
    simp only [mc_IsTransientE, mc_IsRecurrentE] at hrec ⊢
    exact lt_of_le_of_ne (mc_hitE_le_one hP j j) hrec
  have hU := (mc_isTransientE_iff hP j).1 htr
  have hsum : ∑' _ : ℕ, μ j = ∑' i, μ i * mc_visitsE P i j := by
    simp only [mc_visitsE, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun n => (hμ.1.pow (n + 1) j).symm
  have hle : ∑' i, μ i * mc_visitsE P i j ≤ 1 + mc_visitsE P j j := by
    calc ∑' i, μ i * mc_visitsE P i j ≤ ∑' i, μ i * (1 + mc_visitsE P j j) :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact mc_visitsE_le hP i j
      _ = 1 + mc_visitsE P j j := by rw [ENNReal.tsum_mul_right, hμ.2, one_mul]
  have htop : ∑' _ : ℕ, μ j = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (mc_stationaryE_pos hirr hμ j).ne'
  rw [hsum, ← top_le_iff] at htop
  exact absurd (htop.trans hle) (not_le.2 (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hU⟩))

/-! ### The cycle measure -/

/-- `Pr(Xₙ₊₁ = k, X₁, …, Xₙ ≠ i | X₀ = i) = ((PDᵢ)ⁿP)ᵢₖ`. -/
noncomputable def mc_cycleStepE (P : S → S → ℝ≥0∞) (i : S) (n : ℕ) (k : S) : ℝ≥0∞ :=
  mc_mulE (mc_powE (mc_tabooE P i) n) P i k

/-- The **cycle measure** of `i`: the expected number of visits to `k` at times
`1, …, τᵢ`. -/
noncomputable def mc_cycleE (P : S → S → ℝ≥0∞) (i : S) (k : S) : ℝ≥0∞ :=
  ∑' n, mc_cycleStepE P i n k

/-- The forward recursion `Gₙ₊₁(k) = Σ_{l ≠ i} Gₙ(l) pₗₖ`. -/
theorem mc_cycleStepE_succ (P : S → S → ℝ≥0∞) (i : S) (n : ℕ) (k : S) :
    mc_cycleStepE P i (n + 1) k =
      ∑' l, if l = i then 0 else mc_cycleStepE P i n l * P l k := by
  simp only [mc_cycleStepE]
  rw [mc_powE_succ', mc_mulE_assoc]
  simp only [mc_mulE]
  have h1 : ∀ l, (if l = i then 0 else (∑' m, mc_powE (mc_tabooE P i) n i m * P m l) * P l k) =
      ∑' m, mc_powE (mc_tabooE P i) n i m * (mc_tabooE P i m l * P l k) := fun l => by
    by_cases hl : l = i
    · simp [hl, mc_tabooE]
    · simp only [hl, ite_false, mc_tabooE, ← ENNReal.tsum_mul_right, mul_assoc]
  simp only [h1]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

/-- `G₀(k) = pᵢₖ`. -/
theorem mc_cycleStepE_zero (P : S → S → ℝ≥0∞) (i k : S) : mc_cycleStepE P i 0 k = P i k := by
  simp [mc_cycleStepE, mc_powE, mc_idE_mulE]

/-- The cycle measure at `i` is the return probability. -/
theorem mc_cycleE_self (P : S → S → ℝ≥0∞) (i : S) : mc_cycleE P i i = mc_hitE P i i := rfl

/-- For a recurrent state `i`, the cycle measure is invariant. -/
theorem mc_cycleE_invariant {i : S} (hi : mc_IsRecurrentE P i) :
    mc_IsInvariantE P (mc_cycleE P i) := by
  intro k
  have h1 : mc_cycleE P i k = P i k + ∑' n, mc_cycleStepE P i (n + 1) k := by
    rw [mc_cycleE, tsum_eq_zero_add' ENNReal.summable, mc_cycleStepE_zero]
  rw [h1]
  simp only [mc_cycleE, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mc_cycleStepE_succ]
  have h2 : ∀ n, ∑' l, mc_cycleStepE P i n l * P l k =
      mc_cycleStepE P i n i * P i k + ∑' l, if l = i then 0 else mc_cycleStepE P i n l * P l k :=
    fun n => mc_tsum_split (fun l => mc_cycleStepE P i n l * P l k) i
  simp only [h2]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  congr 1
  rw [← mc_cycleE, mc_cycleE_self, hi, one_mul]

/-- The cycle measure is the smallest invariant measure with mass `1` at `i`. -/
theorem mc_cycleE_le {i : S} {μ : S → ℝ≥0∞} (hμ : mc_IsInvariantE P μ) (hμi : μ i = 1)
    (k : S) : mc_cycleE P i k ≤ μ k := by
  have key : ∀ N k, ∑ n ∈ Finset.range N, mc_cycleStepE P i n k ≤ μ k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro k
      rw [Finset.sum_range_succ', mc_cycleStepE_zero]
      simp only [mc_cycleStepE_succ]
      rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable, ← hμ k,
        mc_tsum_split (fun l => μ l * P l k) i, hμi, one_mul, add_comm]
      gcongr with l
      by_cases hl : l = i
      · simp [hl]
      · simp only [hl, ite_false, ← Finset.sum_mul]
        exact mul_le_mul_left (ih l) _
  exact ENNReal.tsum_le_of_sum_range_le fun N => key N k

/-- `Σ'ₙ Σ'ₘ g(m + n) = Σ'ₖ (k + 1) g(k)`. -/
theorem mc_tsum_tsum_add (g : ℕ → ℝ≥0∞) :
    ∑' n, ∑' m, g (m + n) = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * g k := by
  rw [← ENNReal.tsum_prod (f := fun n m => g (m + n)),
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  rw [tsum_fintype]
  have : ∀ x : Finset.antidiagonal k, g ((x : ℕ × ℕ).2 + (x : ℕ × ℕ).1) = g k := fun x => by
    have := Finset.mem_antidiagonal.1 x.2
    rw [add_comm, this]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  push_cast; ring

/-- The total mass of the cycle measure of a recurrent state is the mean return time:
`Σₖ νₖ = E[τᵢ | X₀ = i]` (Kac). -/
theorem mc_cycleE_mass (hP : mc_IsStochasticE P) {i : S} (hi : mc_IsRecurrentE P i) :
    ∑' k, mc_cycleE P i k = mc_meanRetE P i := by
  have hP' : ∀ b, ∑' k, P b k = 1 := hP
  set s : ℕ → ℝ≥0∞ := fun n => ∑' l, mc_powE (mc_tabooE P i) n i l
  have hrow : ∀ n, ∑' k, mc_cycleStepE P i n k = s n := fun n => by
    simp only [mc_cycleStepE, mc_mulE, s]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left, hP', mul_one]
  have hstep : ∀ n, s (n + 1) + mc_fpE P i n i = s n := fun n => by
    simp only [s, mc_powE_succ', mc_mulE, mc_fpE]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
    simp only [ENNReal.tsum_mul_left]
    refine tsum_congr fun l => ?_
    have : ∑' k, mc_tabooE P i l k + P l i = 1 := by
      rw [add_comm, ← hP l, mc_tsum_split (P l) i]
      rfl
    rw [← mul_add, this, mul_one]
  have hs : ∀ n, s n + ∑ m ∈ Finset.range n, mc_fpE P i m i = 1 := by
    intro n
    induction n with
    | zero =>
      simp only [s, mc_powE, mc_idE, Finset.range_zero, Finset.sum_empty, add_zero]
      rw [tsum_eq_single i fun j hj => by simp [Ne.symm hj]]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_comm _ (mc_fpE P i n i), ← add_assoc, hstep, ih]
  have htail : ∀ n, s n = ∑' m, mc_fpE P i (m + n) i := by
    intro n
    have h1 := (ENNReal.summable (f := fun m => mc_fpE P i (m + n) i)).sum_add_tsum_nat_add'
      (f := fun m => mc_fpE P i m i)
    have hfin : ∑ m ∈ Finset.range n, mc_fpE P i m i ≠ ∞ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← hs n]; exact le_add_self
    have h2 : ∑ m ∈ Finset.range n, mc_fpE P i m i + s n =
        ∑ m ∈ Finset.range n, mc_fpE P i m i + ∑' m, mc_fpE P i (m + n) i := by
      rw [h1, add_comm, hs n]
      exact hi.symm
    exact (ENNReal.add_right_inj hfin).1 h2
  calc ∑' k, mc_cycleE P i k = ∑' n, s n := by
        simp only [mc_cycleE]
        rw [ENNReal.tsum_comm]
        exact tsum_congr hrow
    _ = ∑' n, ∑' m, mc_fpE P i (m + n) i := tsum_congr htail
    _ = mc_meanRetE P i := mc_tsum_tsum_add (fun m => mc_fpE P i m i)

/-- `E[τᵢ | X₀ = i] ≥ Pr(τᵢ < ∞ | X₀ = i)`. -/
theorem mc_hitE_le_meanRetE (i : S) : mc_hitE P i i ≤ mc_meanRetE P i :=
  ENNReal.tsum_le_tsum fun _ => le_mul_of_one_le_left bot_le le_add_self

/-! ### Stationary distributions and mean return times -/

/-- Miao, Theorem 3.1.5(c), existence: a positive recurrent state `i` gives the stationary
distribution `ν/E[τᵢ | X₀ = i]`, `ν` the cycle measure, with mass `1/E[τᵢ | X₀ = i]` at `i`. -/
theorem mc_stationary_of_posRec (hP : mc_IsStochasticE P) {i : S}
    (hi : mc_IsPositiveRecurrentE P i) :
    mc_IsStationaryE P (fun k => mc_cycleE P i k * (mc_meanRetE P i)⁻¹) := by
  have hm0 : mc_meanRetE P i ≠ 0 := by
    have := mc_hitE_le_meanRetE (P := P) i
    rw [hi.1] at this
    exact (lt_of_lt_of_le one_pos this).ne'
  refine ⟨fun k => ?_, ?_⟩
  · calc ∑' l, mc_cycleE P i l * (mc_meanRetE P i)⁻¹ * P l k
        = (∑' l, mc_cycleE P i l * P l k) * (mc_meanRetE P i)⁻¹ := by
          rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun l => by ring
      _ = mc_cycleE P i k * (mc_meanRetE P i)⁻¹ := by rw [mc_cycleE_invariant hi.1 k]
  · rw [ENNReal.tsum_mul_right, mc_cycleE_mass hP hi.1]
    exact ENNReal.mul_inv_cancel hm0 hi.2.ne

/-- Miao, Theorem 3.1.5(c), the formula `μⱼ = 1/E[τⱼ | X₀ = j]`: for an irreducible chain, every
stationary distribution satisfies `μⱼ = 1/E[τⱼ | X₀ = j]` and every state is positive recurrent.
-/
theorem mc_stationary_eq_inv (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P)
    {μ : S → ℝ≥0∞} (hμ : mc_IsStationaryE P μ) (j : S) :
    μ j = (mc_meanRetE P j)⁻¹ ∧ mc_IsPositiveRecurrentE P j := by
  have hrec := mc_recurrent_of_stationary hP hirr hμ j
  have hμj := mc_stationaryE_pos hirr hμ j
  have hμj' : μ j ≠ ∞ := ((mc_stationaryE_le_one hμ j).trans_lt ENNReal.one_lt_top).ne
  set c := (μ j)⁻¹
  have hc : c ≠ ∞ := ENNReal.inv_ne_top.2 hμj.ne'
  set μ' : S → ℝ≥0∞ := fun k => μ k * c
  have hμ'inv : mc_IsInvariantE P μ' := fun k => by
    simp only [μ', mul_comm (μ _) c, mul_assoc, ENNReal.tsum_mul_left, hμ.1 k]
  have hμ'j : μ' j = 1 := ENNReal.mul_inv_cancel hμj.ne' hμj'
  have hμ'fin : ∀ k, μ' k ≠ ∞ := fun k =>
    ENNReal.mul_ne_top ((mc_stationaryE_le_one hμ k).trans_lt ENNReal.one_lt_top).ne hc
  set ν := mc_cycleE P j
  have hνinv : ∀ k, ∑' l, ν l * P l k = ν k := mc_cycleE_invariant hrec
  have hνle : ∀ k, ν k ≤ μ' k := mc_cycleE_le hμ'inv hμ'j
  have hνfin : ∀ k, ν k ≠ ∞ := fun k => ne_top_of_le_ne_top (hμ'fin k) (hνle k)
  set w : S → ℝ≥0∞ := fun k => μ' k - ν k
  have hsplit : ∀ k, μ' k = ν k + w k := fun k => (add_tsub_cancel_of_le (hνle k)).symm
  have hwinv : mc_IsInvariantE P w := fun k => by
    have h1 : ν k + ∑' l, w l * P l k = ν k + w k := by
      rw [← hsplit, ← hμ'inv k, ← hνinv k, ← ENNReal.tsum_add]
      exact tsum_congr fun l => by rw [hsplit l, add_mul]
    exact (ENNReal.add_right_inj (hνfin k)).1 h1
  have hwj : w j = 0 := by
    simp only [w, hμ'j]
    rw [show ν j = 1 from hrec, tsub_self]
  have hw0 : ∀ l, w l = 0 := by
    intro l
    by_cases hl : l = j
    · rw [hl, hwj]
    · obtain ⟨m, -, hm⟩ := ((mc_isIrreducibleE_iff hP).1 hirr) l j
      have := hwinv.le m l j
      rw [hwj, nonpos_iff_eq_zero, mul_eq_zero] at this
      exact this.resolve_right hm.ne'
  have hμν : ∀ k, μ' k = ν k := fun k => by rw [hsplit k, hw0 k, add_zero]
  have hmass : mc_meanRetE P j = c := by
    rw [← mc_cycleE_mass hP hrec]
    calc ∑' k, ν k = ∑' k, μ' k := tsum_congr fun k => (hμν k).symm
      _ = c := by simp only [μ']; rw [ENNReal.tsum_mul_right, hμ.2, one_mul]
  refine ⟨by rw [hmass, inv_inv], hrec, ?_⟩
  rw [hmass]
  exact lt_top_iff_ne_top.2 hc

/-! ### Theorem 3.1.5 -/

/-- The chain is transient, null recurrent or positive recurrent (all states). -/
theorem mc_transient_or_recurrent (hP : mc_IsStochasticE P) (i : S) :
    mc_IsTransientE P i ∨ mc_IsRecurrentE P i := by
  rcases lt_or_eq_of_le (mc_hitE_le_one hP i i) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Theorem 3.1.5(a)** (Miao, p. 99): for an irreducible chain with a transient state, every
state is transient, `Σₖ p⁽ᵏ⁾ᵢⱼ < ∞` and `p⁽ᵏ⁾ᵢⱼ → 0` for all `i, j`, and there is no stationary
distribution. -/
theorem theorem_3_1_5a (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P) {i : S}
    (hi : mc_IsTransientE P i) :
    (∀ j, mc_IsTransientE P j) ∧ (∀ a j, ∑' k, mc_powE P k a j < ∞) ∧
      (∀ a j, Tendsto (fun k => mc_powE P k a j) atTop (𝓝 0)) ∧
      ¬ ∃ μ, mc_IsStationaryE P μ := by
  have htr : ∀ j, mc_IsTransientE P j := by
    intro j
    rcases mc_transient_or_recurrent hP j with h | h
    · exact h
    · have := theorem_3_1_1a_countable hP (hirr j i) h
      exact absurd this (ne_of_lt hi)
  have hsum : ∀ a j, ∑' k, mc_powE P k a j < ∞ := by
    intro a j
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_lt_top.2 ⟨(mc_powE_le_one hP 0 a j).trans_lt ENNReal.one_lt_top, ?_⟩
    exact (mc_visitsE_le hP a j).trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, (mc_isTransientE_iff hP j).1 (htr j)⟩)
  refine ⟨htr, hsum, fun a j => ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hsum a j).ne, ?_⟩
  rintro ⟨μ, hμ⟩
  exact absurd (mc_recurrent_of_stationary hP hirr hμ i) (ne_of_lt hi)

/-- **Theorem 3.1.5(b)** (Miao, p. 99): for an irreducible chain with a null recurrent state,
every state is null recurrent, there is no stationary distribution, and
`Σₖ p⁽ᵏ⁾ᵢⱼ = ∞`, `E[τⱼ | X₀ = j] = ∞` for all `i, j`. The limit `p⁽ᵏ⁾ᵢⱼ → 0` is not proved. -/
theorem theorem_3_1_5b (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P) {i : S}
    (hi : mc_IsNullRecurrentE P i) :
    (∀ j, mc_IsNullRecurrentE P j) ∧ (¬ ∃ μ, mc_IsStationaryE P μ) ∧
      ∀ a j, ∑' k, mc_powE P k a j = ∞ := by
  have hnost : ¬ ∃ μ, mc_IsStationaryE P μ := by
    rintro ⟨μ, hμ⟩
    exact absurd hi.2 (mc_stationary_eq_inv hP hirr hμ i).2.2.ne
  have hrec : ∀ j, mc_IsRecurrentE P j := fun j =>
    theorem_3_1_1a_countable hP (hirr i j) hi.1
  refine ⟨fun j => ⟨hrec j, ?_⟩, hnost, fun a j => ?_⟩
  · by_contra h
    exact hnost ⟨_, mc_stationary_of_posRec hP ⟨hrec j, lt_top_iff_ne_top.2 h⟩⟩
  · have hF : mc_hitE P a j ≠ 0 :=
      (mc_hitE_pos (((mc_isIrreducibleE_iff hP).1 hirr) a j)).ne'
    have hU : mc_visitsE P a j = ∞ := by
      rw [mc_visits_eq, (mc_isRecurrentE_iff hP j).1 (hrec j), add_top, ENNReal.mul_top hF]
    rw [tsum_eq_zero_add' ENNReal.summable]
    change _ + mc_visitsE P a j = ∞
    rw [hU, add_top]

/-- **Theorem 3.1.5(c)** (Miao, p. 99): for an irreducible chain with a positive recurrent
state, every state is positive recurrent and there is a unique stationary distribution `μ`, with
`μⱼ = 1/E[τⱼ | X₀ = j] > 0` for all `j`. The limit `p⁽ᵏ⁾ᵢⱼ → μⱼ` is not proved. -/
theorem theorem_3_1_5c (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P) {i : S}
    (hi : mc_IsPositiveRecurrentE P i) :
    ∃ μ, mc_IsStationaryE P μ ∧ (∀ j, μ j = (mc_meanRetE P j)⁻¹ ∧ 0 < μ j) ∧
      (∀ j, mc_IsPositiveRecurrentE P j) ∧ ∀ ν, mc_IsStationaryE P ν → ν = μ := by
  have hμ := mc_stationary_of_posRec hP hi
  refine ⟨_, hμ, fun j => ⟨(mc_stationary_eq_inv hP hirr hμ j).1, mc_stationaryE_pos hirr hμ j⟩,
    fun j => (mc_stationary_eq_inv hP hirr hμ j).2, fun ν hν => funext fun j => ?_⟩
  rw [(mc_stationary_eq_inv hP hirr hν j).1, (mc_stationary_eq_inv hP hirr hμ j).1]

/-- Miao, Theorem 3.1.5 (p. 99): an irreducible chain is transient, null recurrent or positive
recurrent, each property holding for all states at once. -/
theorem theorem_3_1_5_trichotomy (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P)
    [Nonempty S] :
    (∀ j, mc_IsTransientE P j) ∨ (∀ j, mc_IsNullRecurrentE P j) ∨
      ∀ j, mc_IsPositiveRecurrentE P j := by
  obtain ⟨i⟩ := ‹Nonempty S›
  rcases mc_transient_or_recurrent hP i with h | h
  · exact Or.inl (theorem_3_1_5a hP hirr h).1
  · by_cases hm : mc_meanRetE P i = ∞
    · exact Or.inr (Or.inl (theorem_3_1_5b hP hirr ⟨h, hm⟩).1)
    · obtain ⟨-, -, -, hpos, -⟩ := theorem_3_1_5c hP hirr ⟨h, lt_top_iff_ne_top.2 hm⟩
      exact Or.inr (Or.inr hpos)

/-! ### Finite chains -/

/-- A real transition matrix seen as a `[0, ∞]`-valued one. -/
noncomputable def mc_toE {T : Type*} (P : Matrix T T ℝ) : T → T → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (P i j)

/-- The `n`-step transitions computed in `[0, ∞]` are those of the real matrix. -/
theorem mc_powE_toE {T : Type*} [Fintype T] [DecidableEq T] {P : Matrix T T ℝ}
    (hP : P ∈ rowStochastic ℝ T) (n : ℕ) (i j : T) :
    mc_powE (mc_toE P) n i j = ENNReal.ofReal ((P ^ n) i j) := by
  induction n generalizing i with
  | zero => by_cases h : i = j <;> simp [mc_powE, mc_idE, h]
  | succ n ih =>
    simp only [mc_powE, mc_mulE, ih, mc_toE, tsum_fintype]
    rw [pow_succ', mul_apply, ENNReal.ofReal_sum_of_nonneg fun l _ =>
      mul_nonneg (nonneg_of_mem_rowStochastic hP) (mc_pow_nonneg hP n l j)]
    exact Finset.sum_congr rfl fun l _ =>
      (ENNReal.ofReal_mul (nonneg_of_mem_rowStochastic hP)).symm

/-- A real transition matrix is a transition matrix in `[0, ∞]`. -/
theorem mc_toE_stochastic {T : Type*} [Fintype T] [DecidableEq T] {P : Matrix T T ℝ}
    (hP : P ∈ rowStochastic ℝ T) : mc_IsStochasticE (mc_toE P) := fun i => by
  simp only [mc_toE, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => nonneg_of_mem_rowStochastic hP,
    sum_row_of_mem_rowStochastic hP, ENNReal.ofReal_one]

/-- **Theorem 3.1.5** for finite chains (Miao, p. 99: "for a finite state space, cases (a)–(b)
cannot happen"): an irreducible finite chain is positive recurrent, and its (unique) stationary
distribution is `μⱼ = 1/E[τⱼ | X₀ = j]`. -/
theorem theorem_3_1_5_finite {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    {P : Matrix T T ℝ} (hP : P ∈ rowStochastic ℝ T) (hirr : mc_IsIrreducible P) :
    (∀ j, mc_IsPositiveRecurrentE (mc_toE P) j) ∧
      ∃ μ, mc_IsStationary P μ ∧ ∀ j, ENNReal.ofReal (μ j) = (mc_meanRetE (mc_toE P) j)⁻¹ := by
  obtain ⟨μ, hμ, -, -⟩ := mc_irreducible_stationary hP hirr
  have hPE := mc_toE_stochastic hP
  have hirrE : mc_IsIrreducibleE (mc_toE P) := by
    refine (mc_isIrreducibleE_iff hPE).2 fun i j => ?_
    obtain ⟨m, hm, hm'⟩ := (mc_isIrreducible_iff hP).1 hirr i j
    exact ⟨m, hm, by rw [mc_powE_toE hP]; exact ENNReal.ofReal_pos.2 hm'⟩
  have hμE : mc_IsStationaryE (mc_toE P) (fun i => ENNReal.ofReal (μ i)) := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [mc_toE, tsum_fintype]
      conv_rhs => rw [hμ.apply_eq 1 j, pow_one]
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
        mul_nonneg (hμ.1 i) (nonneg_of_mem_rowStochastic hP)]
      exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hμ.1 i)).symm
    · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hμ.1 i, hμ.2.1,
        ENNReal.ofReal_one]
  exact ⟨fun j => (mc_stationary_eq_inv hPE hirrE hμE j).2,
    μ, hμ, fun j => (mc_stationary_eq_inv hPE hirrE hμE j).1⟩

end Miao.MarkovProcesses
