/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainExamples
import Mathlib.Algebra.Field.GeomSum

/-!
# Exercises 3 and 6 of Chapter 3

Miao, §3.1.3, pp. 97–98, and §3.4, pp. 113–114 (Exercise 1 is `ex_3_1` in `ChainClasses`).

* **Exercise 3** (§3.1.3, pp. 97–98): the truncated birth–death chain `ex33 k p` on
  `{0, …, k − 1}` (up with probability `p`, down with probability `q = 1 − p`, `p₀₀ = q`,
  `p_{k−1,k−1} = p`) is irreducible for `0 < p < 1` and has the unique stationary distribution
  `πᵢ = (1 − ρ)ρⁱ/(1 − ρᵏ)`, `ρ = p/q ≠ 1` (`ex_3_3`), and `πᵢ = 1/k` when `ρ = 1`
  (`ex_3_3_half`). As `k → ∞`, `πᵢ → (1 − ρ)ρⁱ` when `ρ < 1` and `πᵢ → 0` when `ρ > 1`
  (`ex_3_3_limit_lt`, `ex_3_3_limit_gt`, p. 98).
* **Exercise 6** (p. 114): a doubly stochastic, irreducible and aperiodic chain on `N` states
  has the uniform stationary distribution `πᵢ = 1/N`, it is the unique one, and
  `p⁽ᵗ⁾ᵢⱼ → 1/N` (`ex_3_6`); aperiodicity is needed only for the convergence
  (`ex_3_6_irreducible`).

The stationarity proofs use detailed balance (`mc_isStationary_of_detailed_balance`).
-/

namespace Miao.MarkovProcesses

open Matrix Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- Detailed balance implies stationarity: if `μᵢpᵢⱼ = μⱼpⱼᵢ` for all `i, j`, then `μ = μP`. -/
theorem mc_isStationary_of_detailed_balance (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) (hdb : ∀ i j, μ i * P i j = μ j * P j i) :
    mc_IsStationary P μ := by
  refine ⟨hμ0, hμ1, funext fun j => ?_⟩
  rw [mc_vecMul_apply]
  simp only [hdb _ j, ← Finset.mul_sum, sum_row_of_mem_rowStochastic hP, mul_one]

/-! ### Exercise 3 -/

/-- The transition probabilities of the truncated birth–death chain on `{0, …, k − 1}`, as a
function of the values of the states. -/
def ex33Fn (k : ℕ) (p : ℝ) (a b : ℕ) : ℝ :=
  (if b = a + 1 then p else 0) + (if b + 1 = a then 1 - p else 0) +
    (if b = a then (if a = 0 then 1 - p else 0) + (if a + 1 = k then p else 0) else 0)

/-- **Exercise 3** (Miao, pp. 97–98): the truncated birth–death chain on `{0, …, k − 1}`. -/
def ex33 (k : ℕ) (p : ℝ) : Matrix (Fin k) (Fin k) ℝ := fun i j => ex33Fn k p i j

/-- The truncated birth–death chain is a transition matrix for `0 ≤ p ≤ 1`. -/
theorem ex33_mem {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ex33 k p ∈ rowStochastic ℝ (Fin k) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [ex33, ex33Fn]
    have : 0 ≤ 1 - p := by linarith
    split_ifs <;> linarith
  · simp only [ex33]
    rw [Fin.sum_univ_eq_sum_range (fun b => ex33Fn k p i b) k]
    have hi := i.2
    set a := (i : ℕ)
    simp only [ex33Fn, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    have h2 : ∑ x ∈ Finset.range k, (if x + 1 = a then 1 - p else 0) =
        if a = 0 then 0 else 1 - p := by
      rcases Nat.eq_zero_or_pos a with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
        rw [hm]
        simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq', Finset.mem_range]
        simp [show m < k by omega]
    rw [h2]
    split_ifs <;> first | (exfalso; omega) | ring

/-- The stationary distribution of Exercise 3 for `ρ ≠ 1`. -/
noncomputable def ex33Dist (k : ℕ) (ρ : ℝ) (i : Fin k) : ℝ := (1 - ρ) * ρ ^ (i : ℕ) / (1 - ρ ^ k)

/-- The truncated chain is irreducible for `0 < p < 1` (and `k ≥ 1`). -/
theorem ex33_irreducible {k : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mc_IsIrreducible (ex33 k p) := by
  have hP := ex33_mem (k := k) hp0.le hp1.le
  have hq : 0 < 1 - p := by linarith
  have hup : ∀ i j : Fin k, (j : ℕ) = i + 1 → mc_Accessible (ex33 k p) i j := fun i j h =>
    mc_accessible_of_pos (by
      simp only [ex33, ex33Fn, h, ite_true, show (i : ℕ) + 1 + 1 ≠ i by omega,
        show (i : ℕ) + 1 ≠ i by omega, ite_false]; linarith)
  have hdown : ∀ i j : Fin k, (i : ℕ) = j + 1 → mc_Accessible (ex33 k p) i j := fun i j h =>
    mc_accessible_of_pos (by
      simp only [ex33, ex33Fn, h, ite_true, show (j : ℕ) ≠ j + 1 + 1 by omega,
        show (j : ℕ) ≠ j + 1 by omega, ite_false]; linarith)
  -- states with larger value are reached by steps up, smaller by steps down
  have hupk : ∀ d (i j : Fin k), (j : ℕ) = i + d + 1 → mc_Accessible (ex33 k p) i j := by
    intro d
    induction d with
    | zero => exact fun i j h => hup i j (by omega)
    | succ d ih =>
      intro i j h
      exact (ih i ⟨i + d + 1, by omega⟩ rfl).trans hP (hup _ j (by simp; omega))
  have hdownk : ∀ d (i j : Fin k), (i : ℕ) = j + d + 1 → mc_Accessible (ex33 k p) i j := by
    intro d
    induction d with
    | zero => exact fun i j h => hdown i j (by omega)
    | succ d ih =>
      intro i j h
      exact (hdown i ⟨j + d + 1, by omega⟩ (by simp; omega)).trans hP (ih _ j rfl)
  intro i j
  by_cases hij : i = j
  · exact Or.inl hij
  refine Or.inr ⟨?_, ?_⟩
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hupk ((j : ℕ) - i - 1) i j (by omega)
    · exact hdownk ((i : ℕ) - j - 1) i j (by omega)
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hdownk ((j : ℕ) - i - 1) j i (by omega)
    · exact hupk ((i : ℕ) - j - 1) j i (by omega)

/-- Detailed balance for the truncated chain, for any `μ` with `μ_{a+1} q = μ_a p`. -/
theorem ex33_detailed_balance {k : ℕ} {p : ℝ} {μ : Fin k → ℝ}
    (h : ∀ i j : Fin k, (j : ℕ) = i + 1 → μ i * p = μ j * (1 - p)) (i j : Fin k) :
    μ i * ex33 k p i j = μ j * ex33 k p j i := by
  by_cases hij : i = j
  · rw [hij]
  have hv : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij
  simp only [ex33, ex33Fn, show (j : ℕ) ≠ i by omega, show (i : ℕ) ≠ j by omega, ite_false,
    add_zero]
  by_cases h1 : (j : ℕ) = i + 1
  · simp only [h1, ite_true, show (i : ℕ) + 1 + 1 ≠ i by omega, ite_false, add_zero,
      show (i : ℕ) ≠ i + 1 + 1 by omega, zero_add]
    exact h i j h1
  · by_cases h2 : (i : ℕ) = j + 1
    · simp only [h2, ite_true, show (j : ℕ) + 1 + 1 ≠ j by omega, ite_false, add_zero,
        show (j : ℕ) ≠ j + 1 + 1 by omega, zero_add]
      exact (h j i h2).symm
    · simp only [h1, h2, ite_false, add_zero, show ¬ ((j : ℕ) + 1 = i) by omega,
        show ¬ ((i : ℕ) + 1 = j) by omega, mul_zero]

/-- **Exercise 3** (Miao, pp. 97–98): for `0 < p < 1` with `ρ = p/q ≠ 1` and `k ≥ 1`, the
truncated birth–death chain has the unique stationary distribution
`πᵢ = (1 − ρ)ρⁱ/(1 − ρᵏ)`. -/
theorem ex_3_3 {k : ℕ} (hk : 0 < k) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hρ : p / (1 - p) ≠ 1) :
    mc_IsStationary (ex33 k p) (ex33Dist k (p / (1 - p))) ∧
      ∀ ν, mc_IsStationary (ex33 k p) ν → ν = ex33Dist k (p / (1 - p)) := by
  have hP := ex33_mem (k := k) hp0.le hp1.le
  have hq : 0 < 1 - p := by linarith
  set ρ := p / (1 - p) with hρdef
  have hρ0 : 0 < ρ := div_pos hp0 hq
  have hρq : ρ * (1 - p) = p := div_mul_cancel₀ p hq.ne'
  have hρk : 1 - ρ ^ k ≠ 0 := by
    intro h
    have : ρ ^ k = 1 := by linarith
    exact hρ ((pow_eq_one_iff_of_nonneg hρ0.le hk.ne').1 this)
  have hstat : mc_IsStationary (ex33 k p) (ex33Dist k ρ) := by
    refine mc_isStationary_of_detailed_balance hP (fun i => ?_) ?_ ?_
    · simp only [ex33Dist]
      rcases lt_or_gt_of_ne hρ with h | h
      · have h1 : 0 < 1 - ρ ^ k := by
          have := pow_lt_one₀ hρ0.le h hk.ne'
          linarith
        exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg hρ0.le _)) h1.le
      · have h1 : 1 - ρ ^ k < 0 := by
          have := one_lt_pow₀ h hk.ne'
          linarith
        exact div_nonneg_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith)
          (pow_nonneg hρ0.le _)) h1.le
    · simp only [ex33Dist, ← Finset.sum_div, ← Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun i => ρ ^ i) k, geom_sum_eq hρ]
      have h1 : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ
      field_simp
      ring
    · refine ex33_detailed_balance fun i j h => ?_
      simp only [ex33Dist, h, pow_succ]
      field_simp
      linarith [hρq]
  exact ⟨hstat, fun ν hν => mc_stationary_unique_of_irreducible hP (ex33_irreducible hp0 hp1)
    hν hstat⟩

/-- **Exercise 3** (Miao, p. 98), the case `ρ = 1` (`p = 1/2`): the stationary distribution is
`πᵢ = 1/k`. -/
theorem ex_3_3_half {k : ℕ} (hk : 0 < k) :
    mc_IsStationary (ex33 k (1 / 2)) (fun _ => (1 : ℝ) / k) ∧
      ∀ ν, mc_IsStationary (ex33 k (1 / 2)) ν → ν = fun _ => (1 : ℝ) / k := by
  have hP := ex33_mem (k := k) (p := 1 / 2) (by norm_num) (by norm_num)
  have hstat : mc_IsStationary (ex33 k (1 / 2)) (fun _ => (1 : ℝ) / k) := by
    refine mc_isStationary_of_detailed_balance hP (fun _ => by positivity) ?_
      (ex33_detailed_balance fun _ _ _ => by norm_num)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  exact ⟨hstat, fun ν hν => mc_stationary_unique_of_irreducible hP
    (ex33_irreducible (by norm_num) (by norm_num)) hν hstat⟩

/-- Miao, p. 98: for `ρ < 1`, `πᵢ → (1 − ρ)ρⁱ` as `k → ∞`. -/
theorem ex_3_3_limit_lt {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (i : ℕ) :
    Tendsto (fun k : ℕ => (1 - ρ) * ρ ^ i / (1 - ρ ^ k)) atTop (𝓝 ((1 - ρ) * ρ ^ i)) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_sub 1)
  simp only [sub_zero] at h
  have h3 : Tendsto (fun k : ℕ => (1 - ρ) * ρ ^ i / (1 - ρ ^ k)) atTop
      (𝓝 ((1 - ρ) * ρ ^ i / 1)) := tendsto_const_nhds.div h one_ne_zero
  rwa [div_one] at h3

/-- Miao, p. 98: for `ρ > 1`, `πᵢ → 0` as `k → ∞`. -/
theorem ex_3_3_limit_gt {ρ : ℝ} (hρ1 : 1 < ρ) (i : ℕ) :
    Tendsto (fun k : ℕ => (1 - ρ) * ρ ^ i / (1 - ρ ^ k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => 1 - ρ ^ k) atTop atBot :=
    tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp
      (tendsto_pow_atTop_atTop_of_one_lt hρ1))
  have h2 := (tendsto_inv_atBot_zero.comp h1).const_mul ((1 - ρ) * ρ ^ i)
  simpa [div_eq_mul_inv] using h2

/-! ### Exercise 6 -/

/-- **Exercise 6** (Miao, p. 114), without aperiodicity: an irreducible doubly stochastic chain
on `N` states has the unique stationary distribution `πᵢ = 1/N`. -/
theorem ex_3_6_irreducible [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hcol : ∀ j, ∑ i, P i j = 1) (hirr : mc_IsIrreducible P) :
    mc_IsStationary P (fun _ => (1 : ℝ) / Fintype.card S) ∧
      ∀ ν, mc_IsStationary P ν → ν = fun _ => (1 : ℝ) / Fintype.card S := by
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hstat : mc_IsStationary P (fun _ => (1 : ℝ) / Fintype.card S) := by
    refine ⟨fun _ => by positivity, ?_, funext fun j => ?_⟩
    · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · rw [mc_vecMul_apply, ← Finset.mul_sum, hcol, mul_one]
  exact ⟨hstat, fun ν hν => mc_stationary_unique_of_irreducible hP hirr hν hstat⟩

/-- **Exercise 6** (Miao, p. 114): a doubly stochastic, irreducible and aperiodic chain on `N`
states has the stationary distribution `πᵢ = 1/N`; it is the unique one, and
`p⁽ᵗ⁾ᵢⱼ → 1/N` for all `i, j` (Theorems 3.1.3 and 3.1.4). -/
theorem ex_3_6 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (hcol : ∀ j, ∑ i, P i j = 1)
    (hirr : mc_IsIrreducible P) (hap : mc_IsAperiodicChain P) :
    mc_IsStationary P (fun _ => (1 : ℝ) / Fintype.card S) ∧
      (∀ ν, mc_IsStationary P ν → ν = fun _ => (1 : ℝ) / Fintype.card S) ∧
      ∀ i j, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 ((1 : ℝ) / Fintype.card S)) := by
  obtain ⟨hstat, huniq⟩ := ex_3_6_irreducible hP hcol hirr
  obtain ⟨k₀, hk₀, hpos⟩ := (theorem_3_1_4 hP).1 ⟨hirr, hap⟩
  obtain ⟨μ, hμ, -, hlim, -⟩ := theorem_3_1_3 hP ⟨k₀, hk₀, hpos k₀ le_rfl⟩
  have hμeq := huniq μ hμ
  refine ⟨hstat, huniq, fun i j => ?_⟩
  have := hlim i j
  rwa [hμeq] at this

end Miao.MarkovProcesses
