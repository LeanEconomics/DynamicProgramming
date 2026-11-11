/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainClasses
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.Infinite

/-!
# Finite Markov chains: stationary distributions, Theorems 3.1.3–3.1.4

Miao, §3.1.2, pp. 94–97.

* **Definition 3.1.5** (p. 94): `mc_IsStationary P μ`: `μ` is a distribution (row vector) with
  `μ = μP`; `mc_IsStationary.pow`: then `μ = μPᵗ`, and `μₜ = μ₀Pᵗ` is the distribution at `t`.
* **Theorem 3.1.3** (p. 94): if `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and one `k > 0`, there is a unique
  stationary distribution `μ`, `p⁽ᵗ⁾ᵢⱼ → μⱼ > 0` for all `i, j` (`theorem_3_1_3`). The steps of
  the proof are `theorem_3_1_3_mono` (`mₜ` increases), `theorem_3_1_3_anti` (`Mₜ` decreases),
  `theorem_3_1_3_min_step`, `theorem_3_1_3_max_step` (the two displayed inequalities, for the
  `k`-step matrix with `δ = minᵢⱼ p⁽ᵏ⁾ᵢⱼ`) and `theorem_3_1_3_gap_step`
  (`Δ_{t+k} ≤ (1 − 2δ)Δₜ`).
* **Theorem 3.1.4** (p. 96, `theorem_3_1_4`): a finite chain is irreducible and aperiodic iff
  there is `k₀ > 0` with `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and all `k ≥ k₀`.
* The general case (p. 97): `mc_exists_stationary` (every finite chain has a stationary
  distribution, from a limit point of the Cesàro averages of a row of `Pᵗ`);
  `mc_stationary_unique_of_irreducible`, `mc_stationary_pos_of_irreducible` (uniqueness and
  positivity under irreducibility); `stationary_p97_transient` (stationary distributions vanish
  on transient states); `stationary_p97_class` (each recurrent class carries a unique stationary
  distribution `mc_classDist`, supported by the class); `stationary_p97_decomposition` (every
  stationary distribution is a convex combination of these); `stationary_p97_infinite` (with two
  recurrent classes there are infinitely many stationary distributions).

**Corrections.**
* Theorem 3.1.3 needs one `k` for all pairs `i, j` (as its proof uses). If `k` may depend on
  `i, j` the conclusion fails: `theorem_3_1_3_counterexample` (the two-state swap, which is
  Example 3.1.2 with `1 × 1` blocks, has `p⁽ᵏ⁾ᵢⱼ > 0` for some `k` for every pair, but `p⁽ᵗ⁾₀₀`
  does not converge).
* After Theorems 3.1.3 and 3.1.4 the book says that Example 3.1.2 has no stationary distribution.
  This is false: every finite chain has one (`mc_exists_stationary`), and the swap has
  `(1/2, 1/2)` (`theorem_3_1_3_counterexample`); what fails for Example 3.1.2 is the convergence
  of `Pᵗ` (`example_3_1_2_stationary`, `example_3_1_2_not_tendsto` in `ChainExamples`).
* Theorem 3.1.3 is stated for a nonempty state space (otherwise no distribution exists).
* The proof's bound `Δₜ ≤ (1 − 2δ)ᵗ` is used here in the form `Δ_{nk} ≤ (1 − δ)ⁿ`, which follows
  from the displayed step and needs no case distinction on `δ ≤ 1/2`.
-/

namespace Miao.MarkovProcesses

open Matrix Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-! ### Definition 3.1.5 -/

/-- **Definition 3.1.5** (Miao, p. 94): `μ` is an **invariant** (**stationary**) distribution of
the chain with transition matrix `P`: a distribution (row vector) with `μ = μP`. -/
def mc_IsStationary (P : Matrix S S ℝ) (μ : S → ℝ) : Prop :=
  (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ μ ᵥ* P = μ

omit [DecidableEq S] in
/-- The entries of `v ᵥ* M`. -/
theorem mc_vecMul_apply (v : S → ℝ) (M : Matrix S S ℝ) (j : S) :
    (v ᵥ* M) j = ∑ i, v i * M i j := rfl

/-- Miao, p. 94: the distribution in period `t` is `μₜ = μ₀Pᵗ`; it satisfies
`μₜ₊₁ = μₜP`. -/
theorem mc_dist_succ (μ₀ : S → ℝ) (t : ℕ) : μ₀ ᵥ* P ^ (t + 1) = (μ₀ ᵥ* P ^ t) ᵥ* P := by
  rw [vecMul_vecMul, pow_succ]

/-- A stationary distribution is invariant under every power: `μ = μPᵗ`. -/
theorem mc_IsStationary.pow {μ : S → ℝ} (hμ : mc_IsStationary P μ) (t : ℕ) :
    μ ᵥ* P ^ t = μ := by
  induction t with
  | zero => simp
  | succ t ih => rw [mc_dist_succ, ih, hμ.2.2]

/-- The entries of a stationary distribution: `μⱼ = Σᵢ μᵢ p⁽ᵗ⁾ᵢⱼ`. -/
theorem mc_IsStationary.apply_eq {μ : S → ℝ} (hμ : mc_IsStationary P μ) (t : ℕ) (j : S) :
    μ j = ∑ i, μ i * (P ^ t) i j := by
  rw [← mc_vecMul_apply, hμ.pow t]

/-- `μⱼ ≥ μᵢ p⁽ᵗ⁾ᵢⱼ` for a stationary distribution. -/
theorem mc_IsStationary.le_apply (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ : mc_IsStationary P μ) (t : ℕ) (i j : S) : μ i * (P ^ t) i j ≤ μ j := by
  rw [hμ.apply_eq t j]
  exact Finset.single_le_sum (f := fun l => μ l * (P ^ t) l j)
    (fun l _ => mul_nonneg (hμ.1 l) (mc_pow_nonneg hP t l j)) (Finset.mem_univ i)

omit [DecidableEq S] in
/-- A convex combination of stationary distributions is stationary. -/
theorem mc_IsStationary.convex {μ ν : S → ℝ} (hμ : mc_IsStationary P μ)
    (hν : mc_IsStationary P ν) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mc_IsStationary P (t • μ + (1 - t) • ν) := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ht0 (hμ.1 i)) (mul_nonneg (by linarith) (hν.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hμ.2.1, hν.2.1]
    ring
  · rw [add_vecMul, smul_vecMul, smul_vecMul, hμ.2.2, hν.2.2]

omit [DecidableEq S] in
/-- A distribution has a state of positive mass. -/
theorem mc_exists_pos_of_sum_eq_one {μ : S → ℝ} (h : ∑ i, μ i = 1) : ∃ i, 0 < μ i := by
  by_contra hne
  push Not at hne
  have : ∑ i, μ i ≤ 0 := Finset.sum_nonpos fun i _ => hne i
  linarith

/-! ### Theorem 3.1.3 -/

/-- `m_t = minᵢ p⁽ᵗ⁾ᵢⱼ`, the minimum of column `j` of `Pᵗ` (Miao, p. 94). -/
noncomputable def mc_colMin [Nonempty S] (P : Matrix S S ℝ) (j : S) (t : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => (P ^ t) i j

/-- `M_t = maxᵢ p⁽ᵗ⁾ᵢⱼ`, the maximum of column `j` of `Pᵗ` (Miao, p. 94). -/
noncomputable def mc_colMax [Nonempty S] (P : Matrix S S ℝ) (j : S) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (P ^ t) i j

omit [Fintype S] [DecidableEq S] in
/-- The minimum is attained. -/
theorem mc_colMin_le [Fintype S] [DecidableEq S] [Nonempty S] (j : S) (t : ℕ) (i : S) :
    mc_colMin P j t ≤ (P ^ t) i j :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- `p⁽ᵗ⁾ᵢⱼ ≤ M_t`. -/
theorem mc_le_colMax [Nonempty S] (j : S) (t : ℕ) (i : S) : (P ^ t) i j ≤ mc_colMax P j t :=
  Finset.le_sup' (fun i => (P ^ t) i j) (Finset.mem_univ i)

/-- `M_t ≤ 1`. -/
theorem mc_colMax_le_one [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    mc_colMax P j t ≤ 1 :=
  Finset.sup'_le _ _ fun i _ => mc_pow_le_one hP t i j

/-- `m_t ≥ 0`. -/
theorem mc_colMin_nonneg [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    0 ≤ mc_colMin P j t :=
  Finset.le_inf' _ _ fun i _ => mc_pow_nonneg hP t i j

/-- A weighted average with stochastic weights lies above a lower bound. -/
theorem mc_avg_ge {Q : Matrix S S ℝ} (hQ : Q ∈ rowStochastic ℝ S) (i : S) {x : S → ℝ} {a : ℝ}
    (h : ∀ v, a ≤ x v) : a ≤ ∑ v, Q i v * x v := by
  calc a = ∑ v, Q i v * a := by rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hQ, one_mul]
    _ ≤ ∑ v, Q i v * x v := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (h v) (nonneg_of_mem_rowStochastic hQ)

/-- A weighted average with stochastic weights lies below an upper bound. -/
theorem mc_avg_le {Q : Matrix S S ℝ} (hQ : Q ∈ rowStochastic ℝ S) (i : S) {x : S → ℝ} {a : ℝ}
    (h : ∀ v, x v ≤ a) : ∑ v, Q i v * x v ≤ a := by
  calc ∑ v, Q i v * x v ≤ ∑ v, Q i v * a := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (h v) (nonneg_of_mem_rowStochastic hQ)
    _ = a := by rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hQ, one_mul]

/-- Miao, proof of Theorem 3.1.3, step 1, p. 95: the column minima `mₜ` increase. -/
theorem theorem_3_1_3_mono [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    mc_colMin P j t ≤ mc_colMin P j (t + 1) := by
  refine Finset.le_inf' _ _ fun i _ => ?_
  rw [pow_succ', mul_apply]
  exact mc_avg_ge hP i fun v => mc_colMin_le j t v

/-- Miao, proof of Theorem 3.1.3, step 2, p. 95: the column maxima `Mₜ` decrease. -/
theorem theorem_3_1_3_anti [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    mc_colMax P j (t + 1) ≤ mc_colMax P j t := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [pow_succ', mul_apply]
  exact mc_avg_le hP i fun v => mc_le_colMax j t v

/-- Miao, proof of Theorem 3.1.3, p. 95, first display: if every entry of `Q = Pᵏ` is at least
`δ`, then `m_{t+k} ≥ δMₜ + (1 − δ)mₜ`. -/
theorem theorem_3_1_3_min_step [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) {k : ℕ}
    {δ : ℝ} (hδ : ∀ i v, δ ≤ (P ^ k) i v) (t : ℕ) :
    δ * mc_colMax P j t + (1 - δ) * mc_colMin P j t ≤ mc_colMin P j (k + t) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => (P ^ t) i j
  refine Finset.le_inf' _ _ fun i _ => ?_
  have hQ := mc_pow_mem hP k
  set m := mc_colMin P j t
  set x : S → ℝ := fun v => (P ^ t) v j
  have hx : ∀ v, m ≤ x v := fun v => mc_colMin_le j t v
  have hsum : ∑ v, (P ^ k) i v * x v = m + ∑ v, (P ^ k) i v * (x v - m) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_row_of_mem_rowStochastic hQ, one_mul]
    ring
  have hsingle : (P ^ k) i l * (x l - m) ≤ ∑ v, (P ^ k) i v * (x v - m) :=
    Finset.single_le_sum (f := fun v => (P ^ k) i v * (x v - m))
      (fun v _ => mul_nonneg (mc_pow_nonneg hP k i v) (sub_nonneg.2 (hx v)))
      (Finset.mem_univ l)
  have hxl : x l = mc_colMax P j t := hl.symm
  have hδl : δ * (x l - m) ≤ (P ^ k) i l * (x l - m) :=
    mul_le_mul_of_nonneg_right (hδ i l) (sub_nonneg.2 (hx l))
  rw [pow_add, mul_apply]
  change _ ≤ ∑ v, (P ^ k) i v * x v
  rw [hsum, ← hxl]
  nlinarith

/-- Miao, proof of Theorem 3.1.3, p. 95, second display: `M_{t+k} ≤ δmₜ + (1 − δ)Mₜ`. -/
theorem theorem_3_1_3_max_step [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) {k : ℕ}
    {δ : ℝ} (hδ : ∀ i v, δ ≤ (P ^ k) i v) (t : ℕ) :
    mc_colMax P j (k + t) ≤ δ * mc_colMin P j t + (1 - δ) * mc_colMax P j t := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun i => (P ^ t) i j
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hQ := mc_pow_mem hP k
  set M := mc_colMax P j t
  set x : S → ℝ := fun v => (P ^ t) v j
  have hx : ∀ v, x v ≤ M := fun v => mc_le_colMax j t v
  have hsum : ∑ v, (P ^ k) i v * x v = M - ∑ v, (P ^ k) i v * (M - x v) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_row_of_mem_rowStochastic hQ, one_mul]
    ring
  have hsingle : (P ^ k) i l * (M - x l) ≤ ∑ v, (P ^ k) i v * (M - x v) :=
    Finset.single_le_sum (f := fun v => (P ^ k) i v * (M - x v))
      (fun v _ => mul_nonneg (mc_pow_nonneg hP k i v) (sub_nonneg.2 (hx v)))
      (Finset.mem_univ l)
  have hxl : x l = mc_colMin P j t := hl.symm
  have hδl : δ * (M - x l) ≤ (P ^ k) i l * (M - x l) :=
    mul_le_mul_of_nonneg_right (hδ i l) (sub_nonneg.2 (hx l))
  rw [pow_add, mul_apply]
  change ∑ v, (P ^ k) i v * x v ≤ _
  rw [hsum, ← hxl]
  nlinarith

/-- Miao, proof of Theorem 3.1.3, p. 95: `Δ_{t+k} ≤ (1 − 2δ)Δₜ`, `Δₜ = Mₜ − mₜ`. -/
theorem theorem_3_1_3_gap_step [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) {k : ℕ}
    {δ : ℝ} (hδ : ∀ i v, δ ≤ (P ^ k) i v) (t : ℕ) :
    mc_colMax P j (k + t) - mc_colMin P j (k + t) ≤
      (1 - 2 * δ) * (mc_colMax P j t - mc_colMin P j t) := by
  have h1 := theorem_3_1_3_min_step hP j hδ t
  have h2 := theorem_3_1_3_max_step hP j hδ t
  nlinarith

/-- **Theorem 3.1.3** (Miao, p. 94): if `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and some (one) `k > 0`, the
chain has a unique stationary distribution `μ`, and `p⁽ᵗ⁾ᵢⱼ → μⱼ > 0` for all `i, j`. -/
theorem theorem_3_1_3 [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hk : ∃ k, 0 < k ∧ ∀ i j, 0 < (P ^ k) i j) :
    ∃ μ, mc_IsStationary P μ ∧ (∀ j, 0 < μ j) ∧
      (∀ i j, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 (μ j))) ∧
      ∀ ν, mc_IsStationary P ν → ν = μ := by
  obtain ⟨k, hk0, hkpos⟩ := hk
  set δ := (Finset.univ : Finset (S × S)).inf' Finset.univ_nonempty
    (fun p => (P ^ k) p.1 p.2) with hδdef
  have hδ : ∀ i v, δ ≤ (P ^ k) i v := fun i v =>
    Finset.inf'_le (fun p : S × S => (P ^ k) p.1 p.2) (Finset.mem_univ (i, v))
  have hδpos : 0 < δ := (Finset.lt_inf'_iff _).2 fun p _ => hkpos p.1 p.2
  have i₀ : S := Classical.arbitrary S
  have hδ1 : δ ≤ 1 := (hδ i₀ i₀).trans (mc_pow_le_one hP k i₀ i₀)
  -- the limit of each column
  have hlim : ∀ j, ∃ a, 0 < a ∧ ∀ i, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 a) := by
    intro j
    have hmono : Monotone (mc_colMin P j) := monotone_nat_of_le_succ (theorem_3_1_3_mono hP j)
    have hanti : Antitone (mc_colMax P j) := antitone_nat_of_succ_le (theorem_3_1_3_anti hP j)
    have hbdd : BddAbove (Set.range (mc_colMin P j)) :=
      ⟨1, by rintro _ ⟨t, rfl⟩; exact (mc_colMin_le j t i₀).trans (mc_pow_le_one hP t i₀ j)⟩
    have hbdd' : BddBelow (Set.range (mc_colMax P j)) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact (mc_pow_nonneg hP t i₀ j).trans (mc_le_colMax j t i₀)⟩
    set a := ⨆ t, mc_colMin P j t
    set b := ⨅ t, mc_colMax P j t
    have ha := tendsto_atTop_ciSup hmono hbdd
    have hb := tendsto_atTop_ciInf hanti hbdd'
    have hmM : ∀ t t', mc_colMin P j t ≤ mc_colMax P j t' := fun t t' =>
      (hmono (le_max_left t t')).trans (((mc_colMin_le j _ i₀).trans
        (mc_le_colMax j _ i₀)).trans (hanti (le_max_right t t')))
    have hab : a ≤ b := le_ciInf fun t' => ciSup_le fun t => hmM t t'
    have hgap : ∀ n, mc_colMax P j (n * k) - mc_colMin P j (n * k) ≤ (1 - δ) ^ n := by
      intro n
      induction n with
      | zero =>
        simp only [zero_mul, pow_zero]
        linarith [mc_colMax_le_one hP j 0, mc_colMin_nonneg hP j 0]
      | succ n ih =>
        have hstep := theorem_3_1_3_gap_step hP j hδ (n * k)
        have hΔ : 0 ≤ mc_colMax P j (n * k) - mc_colMin P j (n * k) :=
          sub_nonneg.2 (hmM _ _)
        rw [show (n + 1) * k = k + n * k by ring, pow_succ]
        calc _ ≤ (1 - 2 * δ) * (mc_colMax P j (n * k) - mc_colMin P j (n * k)) := hstep
          _ ≤ (1 - δ) * (mc_colMax P j (n * k) - mc_colMin P j (n * k)) := by nlinarith
          _ ≤ (1 - δ) * (1 - δ) ^ n := mul_le_mul_of_nonneg_left ih (by linarith)
          _ = (1 - δ) ^ n * (1 - δ) := mul_comm _ _
    have hba : b - a ≤ 0 := by
      refine le_of_tendsto_of_tendsto' tendsto_const_nhds
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - δ) (by linarith) (by linarith))
        fun n => ?_
      have h1 : b ≤ mc_colMax P j (n * k) := ciInf_le hbdd' (n * k)
      have h2 : mc_colMin P j (n * k) ≤ a := le_ciSup hbdd (n * k)
      linarith [hgap n]
    have hb' : Tendsto (mc_colMax P j) atTop (𝓝 a) := by
      rwa [show a = b by linarith]
    refine ⟨a, ?_, fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb'
      (fun t => mc_colMin_le j t i) (fun t => mc_le_colMax j t i)⟩
    have : δ ≤ mc_colMin P j k := Finset.le_inf' _ _ fun i _ => hδ i j
    exact hδpos.trans_le (this.trans (le_ciSup hbdd k))
  choose μ hμpos hμlim using hlim
  have hsum : ∑ j, μ j = 1 := by
    have h := tendsto_finsetSum Finset.univ fun j _ => hμlim j i₀
    simp only [mc_pow_row_sum hP] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hstat : mc_IsStationary P μ := by
    refine ⟨fun j => (hμpos j).le, hsum, funext fun j => ?_⟩
    rw [mc_vecMul_apply]
    have h1 : Tendsto (fun t => ∑ v, (P ^ t) i₀ v * P v j) atTop (𝓝 (∑ v, μ v * P v j)) :=
      tendsto_finsetSum _ fun v _ => (hμlim v i₀).mul_const _
    have h2 : Tendsto (fun t => (P ^ (t + 1)) i₀ j) atTop (𝓝 (μ j)) :=
      (hμlim j i₀).comp (tendsto_add_atTop_nat 1)
    simp only [pow_succ, mul_apply] at h2
    exact tendsto_nhds_unique h1 h2
  refine ⟨μ, hstat, hμpos, fun i j => hμlim j i, fun ν hν => funext fun j => ?_⟩
  have h1 : Tendsto (fun t => ∑ i, ν i * (P ^ t) i j) atTop (𝓝 (∑ i, ν i * μ j)) :=
    tendsto_finsetSum _ fun i _ => (hμlim j i).const_mul _
  rw [← Finset.sum_mul, hν.2.1, one_mul] at h1
  have h2 : (fun t => ∑ i, ν i * (P ^ t) i j) = fun _ => ν j :=
    funext fun t => (hν.apply_eq t j).symm
  rw [h2] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

/-! ### The two-state swap -/

/-- The two-state swap `[0 1; 1 0]` (Example 3.1.2 with `1 × 1` blocks). -/
def mc_swap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The swap is a transition matrix. -/
theorem mc_swap_mem : mc_swap ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals simp [mc_swap, Fin.sum_univ_succ]

/-- `swap² = 1`. -/
theorem mc_swap_sq : mc_swap ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mc_swap, sq, mul_apply, Fin.sum_univ_succ]

/-- Even powers of the swap are the identity. -/
theorem mc_swap_pow_even (n : ℕ) : mc_swap ^ (2 * n) = 1 := by
  rw [pow_mul, mc_swap_sq, one_pow]

/-- Odd powers of the swap are the swap. -/
theorem mc_swap_pow_odd (n : ℕ) : mc_swap ^ (2 * n + 1) = mc_swap := by
  rw [pow_succ, mc_swap_pow_even, one_mul]

/-- Miao, Theorem 3.1.3, p. 94, **counterexample** to the reading in which `k` may depend on
`i, j`: for the swap every pair has `p⁽ᵏ⁾ᵢⱼ > 0` for some `k > 0`, but `p⁽ᵗ⁾₀₀` alternates
`1, 0, 1, …` and does not converge. The swap still has the stationary distribution
`(1/2, 1/2)`, contradicting the remark after Theorem 3.1.3 that Example 3.1.2 has none. -/
theorem theorem_3_1_3_counterexample :
    (∀ i j, ∃ k, 0 < k ∧ 0 < (mc_swap ^ k) i j) ∧
      ¬ (∃ L, Tendsto (fun t => (mc_swap ^ t) 0 0) atTop (𝓝 L)) ∧
      mc_IsStationary mc_swap (fun _ => 1 / 2) := by
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · by_cases hij : i = j
    · refine ⟨2, by norm_num, ?_⟩
      rw [mc_swap_sq, hij]; simp
    · refine ⟨1, by norm_num, ?_⟩
      fin_cases i <;> fin_cases j <;> simp_all [mc_swap]
  · rintro ⟨L, hL⟩
    have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
    have h3 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
    have he := hL.comp h2
    have ho := hL.comp h3
    simp only [Function.comp_def, mc_swap_pow_even, mc_swap_pow_odd] at he ho
    have h1 : L = 1 := tendsto_nhds_unique he (by simp)
    have h0 : L = 0 := tendsto_nhds_unique ho (by simp [mc_swap])
    linarith
  · refine ⟨fun _ => by norm_num, by norm_num, funext fun j => ?_⟩
    fin_cases j <;> simp [mc_vecMul_apply, mc_swap, Fin.sum_univ_succ]

/-! ### Existence: every finite chain has a stationary distribution -/

/-- `(P⁰)ᵢⱼ = 0` and `(Pᵗ)ᵢⱼ = 0` for all `t ≥ 1` when `j ≠ i` is not accessible from `i`. -/
theorem mc_pow_eq_zero_of_not_accessible (hP : P ∈ rowStochastic ℝ S) {i j : S} (hij : j ≠ i)
    (hacc : ¬ mc_Accessible P i j) (t : ℕ) : (P ^ t) i j = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Ne.symm hij]
  · exact le_antisymm (not_lt.1 fun h => hacc ⟨t, ht, h⟩) (mc_pow_nonneg hP t i j)

/-- Miao, p. 97 (existence, used for every recurrent class): every finite chain has a stationary
distribution. More precisely, for each state `i` there is one charging only `i` and the states
accessible from `i`: a limit point of the Cesàro averages `(1/(n+1)) Σ_{t ≤ n} p⁽ᵗ⁾ᵢ·`. -/
theorem mc_exists_stationary [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ μ, mc_IsStationary P μ ∧ ∀ j, j ≠ i → ¬ mc_Accessible P i j → μ j = 0 := by
  set c : ℕ → S → ℝ := fun n j => (1 / ((n : ℝ) + 1)) * ∑ t ∈ Finset.range (n + 1), (P ^ t) i j
    with hc
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcnn : ∀ n j, 0 ≤ c n j := fun n j => mul_nonneg (by have := hn1 n; positivity)
    (Finset.sum_nonneg fun t _ => mc_pow_nonneg hP t i j)
  have hsumc : ∀ n, ∑ j, c n j = 1 := by
    intro n
    simp only [hc, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mc_pow_row_sum hP, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp [(hn1 n).ne']
    push_cast; ring
  have hcle : ∀ n j, c n j ≤ 1 := fun n j => by
    rw [← hsumc n]
    exact Finset.single_le_sum (fun l _ => hcnn n l) (Finset.mem_univ j)
  -- `c_n P − c_n = (p⁽ⁿ⁺¹⁾ᵢⱼ − p⁽⁰⁾ᵢⱼ)/(n+1)`
  have hdiff : ∀ n j, (c n ᵥ* P) j - c n j =
      (1 / ((n : ℝ) + 1)) * ((P ^ (n + 1)) i j - (P ^ 0) i j) := by
    intro n j
    have hshift : ∀ t, ∑ v, (P ^ t) i v * P v j = (P ^ (t + 1)) i j := fun t => by
      rw [pow_succ, mul_apply]
    change ∑ v, c n v * P v j - c n j = _
    simp only [hc, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hshift, ← mul_sub]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (P ^ t) i j)]
  have hdiff_le : ∀ n j, |(c n ᵥ* P) j - c n j| ≤ 1 / ((n : ℝ) + 1) := by
    intro n j
    rw [hdiff, abs_mul, abs_of_pos (by have := hn1 n; positivity)]
    have h1 := mc_pow_nonneg hP (n + 1) i j
    have h2 := mc_pow_le_one hP (n + 1) i j
    have h3 := mc_pow_nonneg hP 0 i j
    have h4 := mc_pow_le_one hP 0 i j
    have : |(P ^ (n + 1)) i j - (P ^ 0) i j| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    calc 1 / ((n : ℝ) + 1) * |(P ^ (n + 1)) i j - (P ^ 0) i j| ≤ 1 / ((n : ℝ) + 1) * 1 :=
          mul_le_mul_of_nonneg_left this (by have := hn1 n; positivity)
      _ = 1 / ((n : ℝ) + 1) := mul_one _
  have hK : IsCompact (Set.univ.pi fun _ : S => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := c)
    fun n => Set.mem_univ_pi.2 fun j => ⟨hcnn n j, hcle n j⟩
  have hcoord : ∀ j, Tendsto (fun n => c (φ n) j) atTop (𝓝 (μ j)) := fun j =>
    (continuous_apply j).continuousAt.tendsto.comp hlim
  refine ⟨μ, ⟨fun j => ge_of_tendsto' (hcoord j) fun n => hcnn _ j, ?_, funext fun j => ?_⟩, ?_⟩
  · exact tendsto_nhds_unique (tendsto_finsetSum _ fun j _ => hcoord j)
      (by simp only [hsumc]; exact tendsto_const_nhds)
  · have h1 : Tendsto (fun n => (c (φ n) ᵥ* P) j) atTop (𝓝 ((μ ᵥ* P) j)) := by
      simp only [mc_vecMul_apply]
      exact tendsto_finsetSum _ fun v _ => (hcoord v).mul_const _
    have hinv : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n => (c (φ n) ᵥ* P) j - c (φ n) j) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hdiff_le (φ n) j) hinv
    have h3 := h2.add (hcoord j)
    simp only [sub_add_cancel, zero_add] at h3
    exact tendsto_nhds_unique h1 h3
  · intro j hji hacc
    have h0 : ∀ n, c n j = 0 := fun n => by
      simp [hc, mc_pow_eq_zero_of_not_accessible hP hji hacc]
    exact tendsto_nhds_unique (hcoord j) (by simp only [h0]; exact tendsto_const_nhds)

/-! ### Positivity and uniqueness on a communicating class -/

/-- A stationary distribution carried by a set `C` of mutually communicating states charges
every state of `C`. -/
theorem mc_stationary_pos_of (hP : P ∈ rowStochastic ℝ S) {C : Finset S}
    (hC : ∀ i ∈ C, ∀ j ∈ C, mc_Communicate P i j) {μ : S → ℝ} (hμ : mc_IsStationary P μ)
    (hsupp : ∀ j ∉ C, μ j = 0) : ∀ j ∈ C, 0 < μ j := by
  obtain ⟨k, hk⟩ := mc_exists_pos_of_sum_eq_one hμ.2.1
  have hkC : k ∈ C := by
    by_contra h
    rw [hsupp k h] at hk
    exact lt_irrefl _ hk
  intro j hj
  rcases hC k hkC j hj with rfl | ⟨⟨m, -, hm⟩, -⟩
  · exact hk
  · exact (mul_pos hk hm).trans_le (hμ.le_apply hP m k j)

/-- Two stationary distributions carried by a set `C` of mutually communicating states are
equal (if `w = μ − cν ≥ 0` is invariant and vanishes somewhere in `C`, it vanishes on `C`). -/
theorem mc_stationary_unique_of (hP : P ∈ rowStochastic ℝ S) {C : Finset S}
    (hC : ∀ i ∈ C, ∀ j ∈ C, mc_Communicate P i j) {μ ν : S → ℝ} (hμ : mc_IsStationary P μ)
    (hν : mc_IsStationary P ν) (hμs : ∀ j ∉ C, μ j = 0) (hνs : ∀ j ∉ C, ν j = 0) : μ = ν := by
  have hνpos := mc_stationary_pos_of hP hC hν hνs
  have hμpos := mc_stationary_pos_of hP hC hμ hμs
  have hCne : C.Nonempty := by
    obtain ⟨k, hk⟩ := mc_exists_pos_of_sum_eq_one hμ.2.1
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hμs k (by simp [h])] at hk
    exact lt_irrefl _ hk
  set c := C.inf' hCne fun j => μ j / ν j
  obtain ⟨j₀, hj₀, hc⟩ := Finset.exists_mem_eq_inf' hCne fun j => μ j / ν j
  set w := μ - c • ν
  have hw_nn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j ∈ C
    · have h1 : c ≤ μ j / ν j := Finset.inf'_le _ hj
      rw [le_div_iff₀ (hνpos j hj)] at h1
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · simp [w, hμs j hj, hνs j hj]
  have hw_inv : ∀ t, w ᵥ* P ^ t = w := fun t => by
    rw [sub_vecMul, smul_vecMul, hμ.pow, hν.pow]
  have hc' : c = μ j₀ / ν j₀ := hc
  have hw0 : w j₀ = 0 := by
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc', div_mul_cancel₀ _ (hνpos j₀ hj₀).ne']
    ring
  have hwC : ∀ i, w i = 0 := by
    intro i
    by_cases hi : i ∈ C
    · rcases hC i hi j₀ hj₀ with rfl | ⟨⟨m, -, hm⟩, -⟩
      · exact hw0
      · have hle : w i * (P ^ m) i j₀ ≤ w j₀ := by
          calc w i * (P ^ m) i j₀ ≤ ∑ l, w l * (P ^ m) l j₀ :=
                Finset.single_le_sum (f := fun l => w l * (P ^ m) l j₀)
                  (fun l _ => mul_nonneg (hw_nn l) (mc_pow_nonneg hP m l j₀))
                  (Finset.mem_univ i)
            _ = w j₀ := by rw [← mc_vecMul_apply, hw_inv m]
        rw [hw0] at hle
        refine le_antisymm ?_ (hw_nn i)
        by_contra h
        push Not at h
        linarith [mul_pos h hm]
    · simp [w, hμs i hi, hνs i hi]
  have hμeq : ∀ j, μ j = c * ν j := fun j => by
    have := hwC j
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hc1 : c = 1 := by
    have := hμ.2.1
    simp only [hμeq, ← Finset.mul_sum, hν.2.1, mul_one] at this
    exact this
  funext j
  rw [hμeq, hc1, one_mul]

/-- Miao, p. 97: an irreducible finite chain has at most one stationary distribution. -/
theorem mc_stationary_unique_of_irreducible (hP : P ∈ rowStochastic ℝ S)
    (hirr : mc_IsIrreducible P) {μ ν : S → ℝ} (hμ : mc_IsStationary P μ)
    (hν : mc_IsStationary P ν) : μ = ν :=
  mc_stationary_unique_of hP (C := Finset.univ) (fun i _ j _ => hirr i j) hμ hν
    (fun j hj => absurd (Finset.mem_univ j) hj) (fun j hj => absurd (Finset.mem_univ j) hj)

/-- The stationary distribution of an irreducible finite chain charges every state. -/
theorem mc_stationary_pos_of_irreducible (hP : P ∈ rowStochastic ℝ S)
    (hirr : mc_IsIrreducible P) {μ : S → ℝ} (hμ : mc_IsStationary P μ) (j : S) : 0 < μ j :=
  mc_stationary_pos_of hP (C := Finset.univ) (fun i _ j _ => hirr i j) hμ
    (fun j hj => absurd (Finset.mem_univ j) hj) j (Finset.mem_univ j)

/-- Miao, p. 97: an irreducible finite chain has a unique stationary distribution, and it is
positive. -/
theorem mc_irreducible_stationary [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hirr : mc_IsIrreducible P) :
    ∃ μ, mc_IsStationary P μ ∧ (∀ j, 0 < μ j) ∧ ∀ ν, mc_IsStationary P ν → ν = μ := by
  obtain ⟨μ, hμ, -⟩ := mc_exists_stationary hP (Classical.arbitrary S)
  exact ⟨μ, hμ, mc_stationary_pos_of_irreducible hP hirr hμ,
    fun ν hν => mc_stationary_unique_of_irreducible hP hirr hν hμ⟩

/-! ### Stationary distributions of a general finite chain (Miao, p. 97) -/

/-- Miao, p. 97: a stationary distribution vanishes on transient states. -/
theorem stationary_p97_transient (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ : mc_IsStationary P μ) {i : S} (hi : mc_IsTransient P i) : μ i = 0 := by
  classical
  obtain ⟨j, hij, hji⟩ := (mc_isTransient_iff i).1 hi
  by_contra hne
  have hμi : 0 < μ i := lt_of_le_of_ne (hμ.1 i) (Ne.symm hne)
  -- `D`: the states from which `i` can be reached in `≥ 0` steps
  set D : Finset S := Finset.univ.filter fun k => k = i ∨ mc_Accessible P k i with hD
  have hmemD : ∀ k, k ∈ D ↔ k = i ∨ mc_Accessible P k i := fun k => by simp [hD]
  have hpos_acc : ∀ k l, P k l ≠ 0 → mc_Accessible P k l := fun k l h =>
    mc_accessible_of_pos (lt_of_le_of_ne (mc_entry_nonneg hP k l) (Ne.symm h))
  -- no arc enters `D` from outside
  have hout : ∀ v ∉ D, ∀ k ∈ D, P v k = 0 := by
    intro v hv k hk
    by_contra h
    apply hv
    rw [hmemD] at hk ⊢
    rcases hk with rfl | hk
    · exact Or.inr (hpos_acc v k h)
    · exact Or.inr ((hpos_acc v k h).trans hP hk)
  -- mass balance on `D`
  have hbal : ∑ v ∈ D, μ v * (1 - ∑ k ∈ D, P v k) = 0 := by
    have h1 : ∑ k ∈ D, μ k = ∑ v, μ v * ∑ k ∈ D, P v k := by
      calc ∑ k ∈ D, μ k = ∑ k ∈ D, ∑ v, μ v * P v k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mc_vecMul_apply, hμ.2.2]
        _ = ∑ v, μ v * ∑ k ∈ D, P v k := by
            rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    have h2 : ∑ v, μ v * ∑ k ∈ D, P v k = ∑ v ∈ D, μ v * ∑ k ∈ D, P v k := by
      rw [← Finset.sum_add_sum_compl D]
      have : ∑ v ∈ Dᶜ, μ v * ∑ k ∈ D, P v k = 0 := Finset.sum_eq_zero fun v hv => by
        rw [Finset.sum_eq_zero fun k hk => hout v (by simpa using hv) k hk, mul_zero]
      rw [this, add_zero]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  have hterm : ∀ v ∈ D, 0 < μ v → ∑ k ∈ D, P v k = 1 := by
    intro v hv hμv
    have hle : ∑ k ∈ D, P v k ≤ 1 := by
      rw [← sum_row_of_mem_rowStochastic hP v]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        fun k _ _ => mc_entry_nonneg hP v k
    have hnn : ∀ u ∈ D, 0 ≤ μ u * (1 - ∑ k ∈ D, P u k) := fun u _ => by
      refine mul_nonneg (hμ.1 u) (sub_nonneg.2 ?_)
      rw [← sum_row_of_mem_rowStochastic hP u]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        fun k _ _ => mc_entry_nonneg hP u k
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hbal v hv
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hμv.ne'
    · linarith
  -- `E = D ∩ {μ > 0}` is closed
  have hE : mc_IsClosed P {k | k ∈ D ∧ 0 < μ k} := by
    rintro k ⟨hkD, hμk⟩ l hl
    by_contra hkl
    have hμl : 0 < μ l := by
      have := hμ.le_apply hP 1 k l
      rw [pow_one] at this
      exact (mul_pos hμk (lt_of_le_of_ne (mc_entry_nonneg hP k l) (Ne.symm hkl))).trans_le this
    have hlD : l ∉ D := fun h => hl ⟨h, hμl⟩
    have hsplit : ∑ k' ∈ D, P k k' + ∑ k' ∈ Dᶜ, P k k' = 1 := by
      rw [Finset.sum_add_sum_compl, sum_row_of_mem_rowStochastic hP]
    have hc0 : ∑ k' ∈ Dᶜ, P k k' = 0 := by linarith [hterm k hkD hμk]
    exact hkl ((Finset.sum_eq_zero_iff_of_nonneg fun k' _ => mc_entry_nonneg hP k k').1 hc0 l
      (by simpa using hlD))
  have hjD : j ∉ D := by
    rw [hmemD]
    rintro (rfl | h)
    · exact hji hij
    · exact hji h
  obtain ⟨m, -, hm⟩ := hij
  rw [mc_pow_eq_zero_of_closed hE m ⟨(hmemD i).2 (Or.inl rfl), hμi⟩
    fun h => hjD h.1] at hm
  exact lt_irrefl _ hm

/-- Members of the class of a recurrent state communicate with each other. -/
theorem mc_classOf_communicate (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∀ k ∈ mc_classOf P i, ∀ l ∈ mc_classOf P i, mc_Communicate P k l := fun _ hk _ hl =>
  (mc_communicate_equivalence hP).trans
    ((mc_communicate_equivalence hP).symm (mc_mem_classOf.1 hk)) (mc_mem_classOf.1 hl)

/-- Communicating states have the same class. -/
theorem mc_classOf_eq (hP : P ∈ rowStochastic ℝ S) {i j : S} (hij : mc_Communicate P i j) :
    mc_classOf P i = mc_classOf P j := by
  ext k
  simp only [mc_mem_classOf]
  exact ⟨fun h => (mc_communicate_equivalence hP).trans
      ((mc_communicate_equivalence hP).symm hij) h,
    fun h => (mc_communicate_equivalence hP).trans hij h⟩

/-- The stationary distribution attached to a set of states `C`: some stationary distribution
carried by `C` (unique when `C` is a recurrent class, `stationary_p97_class`). -/
noncomputable def mc_classDist (P : Matrix S S ℝ) (C : Finset S) : S → ℝ :=
  Classical.epsilon fun ν => mc_IsStationary P ν ∧ ∀ j ∉ C, ν j = 0

/-- Miao, p. 97: each recurrent class `C` carries a unique stationary distribution
`mc_classDist P C`, and it charges every state of `C`. -/
theorem stationary_p97_class [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {i : S}
    (hi : mc_IsRecurrent P i) :
    mc_IsStationary P (mc_classDist P (mc_classOf P i)) ∧
      (∀ j ∉ mc_classOf P i, mc_classDist P (mc_classOf P i) j = 0) ∧
      (∀ j ∈ mc_classOf P i, 0 < mc_classDist P (mc_classOf P i) j) ∧
      ∀ ν, mc_IsStationary P ν → (∀ j ∉ mc_classOf P i, ν j = 0) →
        ν = mc_classDist P (mc_classOf P i) := by
  have hex : ∃ ν, mc_IsStationary P ν ∧ ∀ j ∉ mc_classOf P i, ν j = 0 := by
    obtain ⟨μ, hμ, hsupp⟩ := mc_exists_stationary hP i
    refine ⟨μ, hμ, fun j hj => hsupp j ?_ ?_⟩
    · rintro rfl; exact hj (mc_mem_classOf.2 (Or.inl rfl))
    · exact fun h => hj (mc_mem_classOf.2 (Or.inr ⟨h, hi j h⟩))
  have hspec := Classical.epsilon_spec hex
  have hC := mc_classOf_communicate hP i
  exact ⟨hspec.1, hspec.2, mc_stationary_pos_of hP hC hspec.1 hspec.2,
    fun ν hν hνs => mc_stationary_unique_of hP hC hν hspec.1 hνs hspec.2⟩

/-- The recurrent classes of the chain. -/
noncomputable def mc_recClasses (P : Matrix S S ℝ) : Finset (Finset S) := by
  classical exact (Finset.univ.filter (mc_IsRecurrent P)).image (mc_classOf P)

/-- Membership in `mc_recClasses`. -/
theorem mc_mem_recClasses {C : Finset S} :
    C ∈ mc_recClasses P ↔ ∃ i, mc_IsRecurrent P i ∧ mc_classOf P i = C := by
  classical simp [mc_recClasses]

/-- Miao, p. 97: every stationary distribution is a convex combination of the stationary
distributions of the recurrent classes. -/
theorem stationary_p97_decomposition [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ : mc_IsStationary P μ) :
    ∃ w : Finset S → ℝ, (∀ C ∈ mc_recClasses P, 0 ≤ w C) ∧ ∑ C ∈ mc_recClasses P, w C = 1 ∧
      μ = ∑ C ∈ mc_recClasses P, w C • mc_classDist P C := by
  classical
  set R : Finset S → S → ℝ := fun C j => if j ∈ C then μ j else 0 with hR
  -- the pieces of `μ` sum to `μ`
  have hpt : ∀ j, ∑ C ∈ mc_recClasses P, R C j = μ j := by
    intro j
    by_cases hj : mc_IsRecurrent P j
    · have hjC : mc_classOf P j ∈ mc_recClasses P := mc_mem_recClasses.2 ⟨j, hj, rfl⟩
      rw [Finset.sum_eq_single (mc_classOf P j)]
      · simp [hR, mc_mem_classOf.2 (Or.inl rfl)]
      · intro C hC hne
        obtain ⟨i, -, rfl⟩ := mc_mem_recClasses.1 hC
        have : j ∉ mc_classOf P i := fun h => hne (mc_classOf_eq hP (mc_mem_classOf.1 h))
        simp [hR, this]
      · exact fun h => absurd hjC h
    · rw [stationary_p97_transient hP hμ hj]
      refine Finset.sum_eq_zero fun C hC => ?_
      obtain ⟨i, hi, rfl⟩ := mc_mem_recClasses.1 hC
      by_cases h : j ∈ mc_classOf P i
      · exact absurd (hi.of_communicate hP (mc_mem_classOf.1 h)) hj
      · simp [hR, h]
  -- each piece is a multiple of the class distribution
  have hpiece : ∀ C ∈ mc_recClasses P, R C = (∑ j ∈ C, μ j) • mc_classDist P C := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := mc_mem_recClasses.1 hC
    obtain ⟨-, -, -, huniq⟩ := stationary_p97_class hP hi
    set C := mc_classOf P i
    have hclosed := mc_classOf_closed hP hi
    have hRinv : R C ᵥ* P = R C := by
      funext j
      rw [mc_vecMul_apply]
      by_cases hj : j ∈ C
      · simp only [hR, hj, ite_true]
        have hμj : μ j = ∑ k, μ k * P k j := by rw [← mc_vecMul_apply, hμ.2.2]
        rw [hμj]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k ∈ C
        · simp [hk]
        · simp only [hk, ite_false, zero_mul]
          by_cases hμk : μ k = 0
          · rw [hμk, zero_mul]
          by_cases hkj : P k j = 0
          · rw [hkj, mul_zero]
          exfalso
          have hrec : mc_IsRecurrent P k := by
            by_contra h
            exact hμk (stationary_p97_transient hP hμ h)
          have hacc : mc_Accessible P k j :=
            mc_accessible_of_pos (lt_of_le_of_ne (mc_entry_nonneg hP k j) (Ne.symm hkj))
          have hjk : mc_Communicate P j k := Or.inr ⟨hrec j hacc, hacc⟩
          exact hk (mc_mem_classOf.2 ((mc_communicate_equivalence hP).trans
            (mc_mem_classOf.1 hj) hjk))
      · simp only [hR, hj, ite_false]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k ∈ C
        · simp [hk, hclosed k hk j hj]
        · simp [hk]
    by_cases hw : ∑ j ∈ C, μ j = 0
    · have h0 : ∀ j ∈ C, μ j = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hμ.1 j).1 hw
      rw [hw, zero_smul]
      funext j
      by_cases hj : j ∈ C <;> simp [hR, hj, h0]
    · have hwpos : 0 < ∑ j ∈ C, μ j :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => hμ.1 j) (Ne.symm hw)
      have hstat : mc_IsStationary P ((∑ j ∈ C, μ j)⁻¹ • R C) := by
        refine ⟨fun j => ?_, ?_, ?_⟩
        · simp only [Pi.smul_apply, smul_eq_mul, hR]
          split_ifs
          · exact mul_nonneg (inv_nonneg.2 hwpos.le) (hμ.1 j)
          · simp
        · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hR]
          rw [Finset.sum_ite_mem, Finset.univ_inter, inv_mul_cancel₀ hw]
        · rw [smul_vecMul, hRinv]
      have heq := huniq _ hstat fun j hj => by simp [hR, hj]
      rw [← heq, smul_smul, mul_inv_cancel₀ hw, one_smul]
  refine ⟨fun C => ∑ j ∈ C, μ j, fun C _ => Finset.sum_nonneg fun j _ => hμ.1 j, ?_, ?_⟩
  · have : ∀ C ∈ mc_recClasses P, ∑ j ∈ C, μ j = ∑ j, R C j := fun C _ => by
      simp only [hR]; rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    simp only [hpt, hμ.2.1]
  · funext j
    rw [← hpt j, Finset.sum_apply]
    exact Finset.sum_congr rfl fun C hC => by rw [hpiece C hC]

/-- Miao, p. 97: if there are at least two recurrent classes, there are infinitely many
stationary distributions. -/
theorem stationary_p97_infinite [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {i j : S}
    (hi : mc_IsRecurrent P i) (hj : mc_IsRecurrent P j) (hij : ¬ mc_Communicate P i j) :
    {μ | mc_IsStationary P μ}.Infinite := by
  obtain ⟨h1, -, hpos1, -⟩ := stationary_p97_class hP hi
  obtain ⟨h2, hs2, -, -⟩ := stationary_p97_class hP hj
  set ρ₁ := mc_classDist P (mc_classOf P i)
  set ρ₂ := mc_classDist P (mc_classOf P j)
  have hiC : i ∉ mc_classOf P j := fun h =>
    hij ((mc_communicate_equivalence hP).symm (mc_mem_classOf.1 h))
  have hρ₂ : ρ₂ i = 0 := hs2 i hiC
  have hρ₁ : 0 < ρ₁ i := hpos1 i (mc_mem_classOf.2 (Or.inl rfl))
  have : Infinite (Set.Icc (0 : ℝ) 1) := Set.Icc.infinite zero_lt_one
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : Set.Icc (0 : ℝ) 1 => (t : ℝ) • ρ₁ + (1 - (t : ℝ)) • ρ₂) ?_
    fun t => h1.convex h2 t.2.1 t.2.2
  intro s t hst
  have := congrFun hst i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hρ₂, mul_zero, add_zero] at this
  exact Subtype.ext (mul_right_cancel₀ hρ₁.ne' this)

/-! ### Theorem 3.1.4 -/

/-- The chain is aperiodic: every state has period `1`. -/
def mc_IsAperiodicChain (P : Matrix S S ℝ) : Prop := ∀ i, mc_IsAperiodic P i

/-- **Theorem 3.1.4** (Miao, p. 96): a finite chain is irreducible and aperiodic iff there is
`k₀ > 0` with `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and all `k ≥ k₀`. -/
theorem theorem_3_1_4 (hP : P ∈ rowStochastic ℝ S) :
    (mc_IsIrreducible P ∧ mc_IsAperiodicChain P) ↔
      ∃ k₀, 0 < k₀ ∧ ∀ k ≥ k₀, ∀ i j, 0 < (P ^ k) i j := by
  constructor
  · rintro ⟨hirr, hap⟩
    have hacc := (mc_isIrreducible_iff hP).1 hirr
    -- all large times are return times of `j`
    have hN : ∀ j, ∃ N, ∀ n ≥ N, 0 < (P ^ n) j j := by
      intro j
      obtain ⟨m, hm, hm'⟩ := hacc j j
      obtain ⟨N, hN⟩ := mc_eventually_mem_of_setGcd_eq_one (mc_returnSet_isAddClosed hP j)
        ⟨hm, hm'⟩ hm (hap j)
      exact ⟨N, fun n hn => (hN n hn).2⟩
    choose N hN using hN
    choose r hr hr' using hacc
    refine ⟨Finset.univ.sup (fun p : S × S => N p.2 + r p.1 p.2) + 1, by omega,
      fun k hk i j => ?_⟩
    have hle : N j + r i j ≤ Finset.univ.sup (fun p : S × S => N p.2 + r p.1 p.2) :=
      Finset.le_sup (f := fun p : S × S => N p.2 + r p.1 p.2) (Finset.mem_univ (i, j))
    have := mc_pow_add_pos hP (hr' i j) (hN j (k - r i j) (by omega))
    rwa [show r i j + (k - r i j) = k by omega] at this
  · rintro ⟨k₀, hk₀, h⟩
    refine ⟨(mc_isIrreducible_iff hP).2 fun i j => ⟨k₀, hk₀, h k₀ le_rfl i j⟩, fun i => ?_⟩
    have hS := mc_returnSet_isAddClosed hP i
    have h1 : k₀ ∈ mc_returnSet P i := ⟨hk₀, h k₀ le_rfl i i⟩
    have h2 : k₀ + 1 ∈ mc_returnSet P i := ⟨by omega, h (k₀ + 1) (by omega) i i⟩
    have hd1 := mc_setGcd_dvd hS h1 hk₀ h1
    have hd2 := mc_setGcd_dvd hS h1 hk₀ h2
    exact Nat.dvd_one.1 ((Nat.dvd_add_right hd1).1 hd2)

end Miao.MarkovProcesses
