/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.ConditionalExpectations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Tauchen's discretisation

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.3 (pp. 89–91)
and Exercise 3.2.2 (p. 93).

The AR(1) process `Xₜ₊₁ = ρXₜ + νεₜ₊₁` is approximated on an equispaced grid
`x₁ < ⋯ < xₙ` with step `s` by the matrix whose rows are the probabilities
that `ρxᵢ + νε` lands in the cell around `xⱼ`: `P(xᵢ, x₁) = F(x₁ − ρxᵢ + s/2)`,
`P(xᵢ, xₙ) = 1 − F(xₙ − ρxᵢ − s/2)` and
`P(xᵢ, xⱼ) = F(xⱼ − ρxᵢ + s/2) − F(xⱼ − ρxᵢ − s/2)` otherwise, where `F` is the
CDF of `N(0, ν²)`. Only three properties of `F` are used: it is increasing
and takes values in `[0, 1]`, so `F` is kept abstract. Exercise 3.1.12: each
row sums to one, by telescoping. Exercise 3.2.2: `P` is monotone increasing
when `ρ ≥ 0`, because the counter-CDF of row `i`, `∑_{l ≥ j} P(xᵢ, xₗ) =
1 − F(xⱼ − ρxᵢ − s/2)`, is increasing in `xᵢ`, and dominance of counter-CDFs
on a totally ordered set gives stochastic dominance (Vol. 1, Lemma 2.2.5 (ii),
re-proved here by Abel summation).

Exercises 3.1.10–3.1.11 concern the Gaussian stationary distribution and
conditional probabilities of the continuous process and are not formalised.
-/

open Finset Matrix

namespace SargentStachurski.MarkovDynamics

/-- A Tauchen grid: `n ≥ 2` points `xⱼ = x₁ + j·s`, `j = 0, …, n − 1`, autocorrelation `ρ`, and a
distribution function `F` that is increasing with values in `[0, 1]`. -/
structure Tauchen where
  n : ℕ
  two_le_n : 2 ≤ n
  ρ : ℝ
  x₁ : ℝ
  s : ℝ
  s_pos : 0 < s
  F : ℝ → ℝ
  F_mono : Monotone F
  F_nonneg : ∀ t, 0 ≤ F t
  F_le_one : ∀ t, F t ≤ 1

namespace Tauchen

variable (m : Tauchen)

/-- The grid point with index `j` (zero-based): `xⱼ = x₁ + j·s`. -/
noncomputable def x (j : ℕ) : ℝ := m.x₁ + j * m.s

theorem x_mono {j k : ℕ} (hjk : j ≤ k) : m.x j ≤ m.x k := by
  unfold x
  have : (j : ℝ) ≤ k := Nat.cast_le.2 hjk
  nlinarith [m.s_pos]

/-- The counter-CDF of row `i` at `j`: the probability of landing at a grid point with index at
least `j`: `1` for `j = 0`, `1 − F(xⱼ − ρxᵢ − s/2)` for `0 < j < n`, and `0` for `j ≥ n`. -/
noncomputable def G (i j : ℕ) : ℝ :=
  if j = 0 then 1 else if j < m.n then 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2) else 0

/-- Tauchen's transition probabilities (p. 91), rules (i)–(iii), on zero-based indices. -/
noncomputable def Pnat (i j : ℕ) : ℝ :=
  if j = 0 then m.F (m.x 0 - m.ρ * m.x i + m.s / 2)
  else if j = m.n - 1 then 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2)
  else m.F (m.x j - m.ρ * m.x i + m.s / 2) - m.F (m.x j - m.ρ * m.x i - m.s / 2)

/-- The transition matrix on the state space `Fin n`. -/
noncomputable def P : Matrix (Fin m.n) (Fin m.n) ℝ := Matrix.of fun i j => m.Pnat i j

theorem P_apply (i j : Fin m.n) : m.P i j = m.Pnat i j := rfl

/-- Rule (i), p. 91. -/
theorem Pnat_zero (i : ℕ) : m.Pnat i 0 = m.F (m.x 0 - m.ρ * m.x i + m.s / 2) := by
  simp [Pnat]

/-- Rule (ii), p. 91. -/
theorem Pnat_last (i : ℕ) :
    m.Pnat i (m.n - 1) = 1 - m.F (m.x (m.n - 1) - m.ρ * m.x i - m.s / 2) := by
  have h := m.two_le_n
  have : m.n - 1 ≠ 0 := by omega
  simp [Pnat, this]

/-- Rule (iii), p. 91. -/
theorem Pnat_mid (i j : ℕ) (hj0 : j ≠ 0) (hjn : j ≠ m.n - 1) :
    m.Pnat i j = m.F (m.x j - m.ρ * m.x i + m.s / 2) - m.F (m.x j - m.ρ * m.x i - m.s / 2) := by
  simp [Pnat, hj0, hjn]

-- The counter-CDF at the two ends.
theorem G_zero (i : ℕ) : m.G i 0 = 1 := by simp [G]

theorem G_n (i : ℕ) : m.G i m.n = 0 := by
  have h := m.two_le_n
  have h1 : m.n ≠ 0 := by omega
  simp [G, h1]

/-- The cell probabilities are differences of the counter-CDF: `P(xᵢ, xⱼ) = G(i, j) − G(i, j+1)`
for `j < n`. -/
theorem Pnat_eq_G_sub (i j : ℕ) (hj : j < m.n) : m.Pnat i j = m.G i j - m.G i (j + 1) := by
  have h2 := m.two_le_n
  have hx : m.x (j + 1) - m.ρ * m.x i - m.s / 2 = m.x j - m.ρ * m.x i + m.s / 2 := by
    unfold x
    push_cast
    ring
  by_cases hj0 : j = 0
  · subst hj0
    have h1 : (1 : ℕ) < m.n := by omega
    have hG1 : m.G i 1 = 1 - m.F (m.x 1 - m.ρ * m.x i - m.s / 2) := by simp [G, h1]
    rw [zero_add] at hx
    rw [Pnat_zero, zero_add, G_zero, hG1, sub_sub_cancel, hx]
  · by_cases hjn : j = m.n - 1
    · subst hjn
      have hG : m.G i (m.n - 1) = 1 - m.F (m.x (m.n - 1) - m.ρ * m.x i - m.s / 2) := by
        simp [G, hj0, hj]
      rw [Pnat_last, hG, show m.n - 1 + 1 = m.n by omega, G_n, sub_zero]
    · have hj1 : j + 1 < m.n := by omega
      have hGj : m.G i j = 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2) := by simp [G, hj0, hj]
      have hGj1 : m.G i (j + 1) = 1 - m.F (m.x (j + 1) - m.ρ * m.x i - m.s / 2) := by
        simp [G, hj1]
      rw [Pnat_mid m i j hj0 hjn, hGj, hGj1, hx]
      ring

/-- `G(i, ·)` is nonincreasing. -/
theorem G_antitone (i : ℕ) {j k : ℕ} (hjk : j ≤ k) : m.G i k ≤ m.G i j := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hj : j = 0 := by omega
    subst hj
    subst hk
    exact le_rfl
  by_cases hkn : k < m.n
  · have hGk : m.G i k = 1 - m.F (m.x k - m.ρ * m.x i - m.s / 2) := by simp [G, hk.ne', hkn]
    rw [hGk]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [G_zero]
      linarith [m.F_nonneg (m.x k - m.ρ * m.x i - m.s / 2)]
    · have hjn : j < m.n := lt_of_le_of_lt hjk hkn
      have hGj : m.G i j = 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2) := by simp [G, hj.ne', hjn]
      rw [hGj]
      exact sub_le_sub_left (m.F_mono (by linarith [m.x_mono hjk])) 1
  · have hGk : m.G i k = 0 := by simp [G, hk.ne', hkn]
    rw [hGk]
    unfold G
    split_ifs
    · exact zero_le_one
    · linarith [m.F_le_one (m.x j - m.ρ * m.x i - m.s / 2)]
    · exact le_rfl

/-- Each entry is nonnegative. -/
theorem Pnat_nonneg (i j : ℕ) (hj : j < m.n) : 0 ≤ m.Pnat i j := by
  rw [Pnat_eq_G_sub m i j hj]
  exact sub_nonneg.2 (m.G_antitone i (Nat.le_succ j))

/-- The tail sums telescope: `∑_{j ≤ l < n} P(xᵢ, xₗ) = G(i, j)` for `j ≤ n`. -/
theorem sum_Ico_Pnat (i j : ℕ) (hj : j ≤ m.n) : ∑ l ∈ Ico j m.n, m.Pnat i l = m.G i j := by
  rw [sum_Ico_eq_sum_range]
  have : ∀ k ∈ range (m.n - j), m.Pnat i (j + k) = m.G i (j + k) - m.G i (j + (k + 1)) := by
    intro k hk
    rw [mem_range] at hk
    rw [← add_assoc]
    exact m.Pnat_eq_G_sub i (j + k) (by omega)
  rw [sum_congr rfl this, sum_range_sub' (fun k => m.G i (j + k))]
  simp only [add_zero]
  rw [show j + (m.n - j) = m.n by omega, G_n, sub_zero]

/-- Exercise 3.1.12 (p. 91): every row of the Tauchen matrix sums to one. -/
theorem sum_Pnat (i : ℕ) : ∑ j ∈ range m.n, m.Pnat i j = 1 := by
  rw [range_eq_Ico, sum_Ico_Pnat m i 0 (Nat.zero_le _), G_zero]

/-- The Tauchen matrix is a Markov matrix. -/
theorem isMarkov_P : IsMarkov m.P where
  nonneg i j := m.Pnat_nonneg i j j.2
  rowsum i := by
    simp only [P_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => m.Pnat i j) m.n]
    exact m.sum_Pnat i

/-- The tail sums of row `i` from index `j`, as a sum over the state space. -/
theorem sum_filter_P (i j : Fin m.n) :
    ∑ l ∈ univ.filter (fun l : Fin m.n => j ≤ l), m.P i l = m.G i j := by
  rw [sum_filter]
  have h1 : ∑ l : Fin m.n, (if j ≤ l then m.P i l else 0) =
      ∑ l ∈ range m.n, (if (j : ℕ) ≤ l then m.Pnat i l else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun l => if (j : ℕ) ≤ l then m.Pnat i l else 0) m.n]
    refine sum_congr rfl fun l _ => ?_
    by_cases h : j ≤ l
    · have h' : (j : ℕ) ≤ l := Fin.le_def.1 h
      simp [h, h', P_apply]
    · have h' : ¬ (j : ℕ) ≤ l := fun hh => h (Fin.le_def.2 hh)
      simp [h, h']
  rw [h1, ← sum_filter]
  have h2 : (range m.n).filter (fun l => (j : ℕ) ≤ l) = Ico (j : ℕ) m.n := by
    ext l
    simp only [mem_filter, mem_range, mem_Ico]
    exact and_comm
  rw [h2, sum_Ico_Pnat m i j j.2.le]

/-! ### Dominance from counter-CDFs on `Fin n` (Vol. 1, Lemma 2.2.5 (ii)) -/

/-- Abel summation on `Fin n`: if `u` is increasing and nonnegative and every tail sum of `d` is
nonnegative, then `∑ u d ≥ 0`. -/
theorem sum_mul_nonneg_of_tails_nonneg : ∀ (n : ℕ) (u d : Fin n → ℝ), Monotone u →
    (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ ∑ j ∈ univ.filter (fun j => i ≤ j), d j) →
    0 ≤ ∑ i, u i * d i := by
  intro n
  induction n with
  | zero => intro u d _ _ _; simp
  | succ n ih =>
    intro u d hu hu0 htail
    have hD0 : ∑ j, d j = ∑ j ∈ univ.filter (fun j => (0 : Fin (n + 1)) ≤ j), d j := by
      congr 1
      ext j
      simp
    have hsplit : ∑ i, u i * d i =
        u 0 * ∑ j, d j + ∑ i : Fin n, (u i.succ - u 0) * d i.succ := by
      simp only [Fin.sum_univ_succ, sub_mul, sum_sub_distrib, mul_sum, mul_add]
      ring
    rw [hsplit]
    refine add_nonneg (mul_nonneg (hu0 0) (hD0 ▸ htail 0)) ?_
    refine ih (fun i => u i.succ - u 0) (fun i => d i.succ) ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu (Fin.succ_le_succ_iff.2 hij)) _
    · intro i
      exact sub_nonneg.2 (hu (Fin.zero_le _))
    · intro i
      have := htail i.succ
      have hreindex : ∑ j ∈ univ.filter (fun j : Fin (n + 1) => i.succ ≤ j), d j =
          ∑ j ∈ univ.filter (fun j : Fin n => i ≤ j), d j.succ := by
        refine (Finset.sum_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_).symm
        · intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj ⊢
          exact Fin.succ_le_succ_iff.2 hj
        · intro a _ b _ hab
          exact Fin.succ_injective _ hab
        · intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj
          refine ⟨j.pred (Fin.pos_iff_ne_zero.1 (lt_of_lt_of_le (Fin.succ_pos i) hj)), ?_, ?_⟩
          · simp only [mem_filter, mem_univ, true_and]
            rw [← Fin.succ_le_succ_iff, Fin.succ_pred]
            exact hj
          · exact Fin.succ_pred _ _
        · intro j _
          rfl
      rwa [hreindex] at this

/-- Vol. 1, Lemma 2.2.5 (ii) on `Fin n`: if two distributions have ordered tail sums,
`∑_{l ≥ j} φ(l) ≤ ∑_{l ≥ j} ψ(l)` for all `j`, then `φ ≼_F ψ`. -/
theorem fosd_of_tails_le {n : ℕ} {φ ψ : Fin n → ℝ} (hφ : ∑ l, φ l = 1) (hψ : ∑ l, ψ l = 1)
    (h : ∀ j, ∑ l ∈ univ.filter (fun l => j ≤ l), φ l ≤ ∑ l ∈ univ.filter (fun l => j ≤ l), ψ l) :
    FOSD φ ψ := by
  intro u hu
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hsum : ∑ x, (ψ x - φ x) = 0 := by rw [sum_sub_distrib, hψ, hφ, sub_self]
  set m : Fin n := ⟨0, hn⟩ with hm
  have hmin : ∀ x, m ≤ x := fun x => Fin.mk_le_of_le_val (Nat.zero_le _)
  have key : 0 ≤ ∑ x, (u x - u m) * (ψ x - φ x) := by
    refine sum_mul_nonneg_of_tails_nonneg n (fun x => u x - u m) (fun x => ψ x - φ x) ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu hij) _
    · intro i
      exact sub_nonneg.2 (hu (hmin i))
    · intro i
      rw [sum_sub_distrib]
      exact sub_nonneg.2 (h i)
  have hexpand : ∑ x, (u x - u m) * (ψ x - φ x) = ∑ x, u x * ψ x - ∑ x, u x * φ x := by
    have h1 : ∑ x, (u x - u m) * (ψ x - φ x) =
        ∑ x, u x * (ψ x - φ x) - u m * ∑ x, (ψ x - φ x) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [h1, hsum, mul_zero, sub_zero, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  linarith

/-- Exercise 3.2.2 (p. 93): the Tauchen matrix is monotone increasing when `ρ ≥ 0`: a higher
current state shifts every tail probability `1 − F(xⱼ − ρxᵢ − s/2)` up. -/
theorem monotoneIncreasing_P (hρ : 0 ≤ m.ρ) : MonotoneIncreasing m.P := by
  intro i k hik
  have hM := m.isMarkov_P
  refine fosd_of_tails_le (hM.rowsum i) (hM.rowsum k) fun j => ?_
  rw [sum_filter_P, sum_filter_P]
  unfold G
  split_ifs with h0 hn
  · exact le_rfl
  · have hx : m.x j - m.ρ * m.x k - m.s / 2 ≤ m.x j - m.ρ * m.x i - m.s / 2 := by
      have := m.x_mono (Fin.le_def.1 hik)
      nlinarith
    exact sub_le_sub_left (m.F_mono hx) 1
  · exact le_rfl

end Tauchen

end SargentStachurski.MarkovDynamics
