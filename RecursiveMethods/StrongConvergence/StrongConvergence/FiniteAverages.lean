/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.FiniteChains

/-!
# Finite Markov chains: long-run averages

SLP §11.1, Theorem 11.1b–c, pp. 326–328. The averages `A⁽ⁿ⁾ = (1/n) Σ_{k<n} Πᵏ` (`cesaro`) are
stochastic matrices. They lie in the compact set of matrices with entries in `[0, 1]`, so every
subsequence has a convergent subsequence. Each limit `Q` of a subsequence satisfies
`Q = QΠ = ΠQ` (`limit_mul`), since `A⁽ⁿ⁾Π − A⁽ⁿ⁾ = (Πⁿ − I)/n → 0`. Two such limits `Q`, `B`
satisfy `Q = QB = BQ = B`, so the whole sequence converges.

* **Theorem 11.1b** (`theorem_11_1b`): `A⁽ⁿ⁾ → Q`, a stochastic matrix with `Q = QΠ = ΠQ`; and
  `(1/n) Σ_{k<n} p₀Πᵏ → p₀Q` for every `p₀`.
* **Theorem 11.1c** (`theorem_11_1c`): each row of `Q` is an invariant distribution, so `p₀Q` is
  one for every `p₀ ∈ Δ`; and every invariant distribution `r` satisfies `r = rQ`, a convex
  combination of the rows of `Q`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- The average `A⁽ⁿ⁾ = (1/n) Σ_{k<n} Πᵏ`. -/
noncomputable def cesaro (P : Matrix S S ℝ) (n : ℕ) : Matrix S S ℝ :=
  (n : ℝ)⁻¹ • ∑ k ∈ range n, P ^ k

omit [Fintype S] [DecidableEq S] in
theorem tendsto_matrix_iff {ι : Type*} {l : Filter ι} {f : ι → Matrix S S ℝ}
    {M : Matrix S S ℝ} :
    Tendsto f l (𝓝 M) ↔ ∀ i j, Tendsto (fun x => f x i j) l (𝓝 (M i j)) := by
  constructor
  · intro h i j
    exact (((continuous_apply j).comp (continuous_apply i)).tendsto M).comp h
  · intro h
    exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j

theorem simplex_vecMul (hP : P ∈ rowStochastic ℝ S) {p : S → ℝ} (hp : p ∈ simplex S) :
    p ᵥ* P ∈ simplex S := by
  refine ⟨fun j => sum_nonneg fun i _ => mul_nonneg (hp.1 i) (nonneg_of_mem_rowStochastic hP),
    ?_⟩
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  simp [← mul_sum, sum_row_of_mem_rowStochastic hP, hp.2]

theorem cesaro_mem (hP : P ∈ rowStochastic ℝ S) {n : ℕ} (hn : 1 ≤ n) :
    cesaro P n ∈ rowStochastic ℝ S := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [cesaro, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    exact mul_nonneg (inv_nonneg.2 hn'.le) (sum_nonneg fun k _ => pow_nonneg' hP k i j)
  · simp only [cesaro, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    rw [← mul_sum, sum_comm]
    simp [pow_row_sum hP, hn'.ne']

theorem isClosed_rowStochastic : IsClosed (rowStochastic ℝ S : Set (Matrix S S ℝ)) := by
  have : (rowStochastic ℝ S : Set (Matrix S S ℝ)) =
      (⋂ i, ⋂ j, {M : Matrix S S ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M | ∑ j, M i j = 1} := by
    ext M
    simp [mem_rowStochastic_iff_sum]
  rw [this]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const ?_).inter
    (isClosed_iInter fun i => isClosed_eq (continuous_finsetSum _ fun j _ => ?_) continuous_const)
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact (continuous_apply j).comp (continuous_apply i)

/-- The matrices with entries in `[0, 1]`. -/
def unitBox (S : Type*) : Set (Matrix S S ℝ) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

omit [Fintype S] [DecidableEq S] in
theorem mem_unitBox {M : Matrix S S ℝ} : M ∈ unitBox S ↔ ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩

omit [Fintype S] [DecidableEq S] in
theorem isCompact_unitBox : IsCompact (unitBox S) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

theorem rowStochastic_subset_unitBox : (rowStochastic ℝ S : Set (Matrix S S ℝ)) ⊆ unitBox S :=
  fun _ hM => mem_unitBox.2 fun _ _ =>
    ⟨nonneg_of_mem_rowStochastic hM, le_one_of_mem_rowStochastic hM⟩

/-- Telescoping: `Σ_{k<n} Πᵏ⁺¹ − Σ_{k<n} Πᵏ = Πⁿ − I`. -/
theorem sum_pow_succ_sub (n : ℕ) :
    ∑ k ∈ range n, P ^ (k + 1) - ∑ k ∈ range n, P ^ k = P ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sub_eq_iff_eq_add] at ih
    rw [sum_range_succ, sum_range_succ, ih]
    abel

theorem cesaro_mul_sub (n : ℕ) : cesaro P n * P - cesaro P n = (n : ℝ)⁻¹ • (P ^ n - 1) := by
  rw [cesaro, smul_mul_assoc, sum_mul, ← smul_sub]
  simp_rw [← pow_succ]
  rw [sum_pow_succ_sub]

theorem mul_cesaro_sub (n : ℕ) : P * cesaro P n - cesaro P n = (n : ℝ)⁻¹ • (P ^ n - 1) := by
  rw [cesaro, mul_smul_comm, mul_sum, ← smul_sub]
  simp_rw [← pow_succ']
  rw [sum_pow_succ_sub]

/-- `(Πⁿ − I)/n → 0`. -/
theorem tendsto_pow_sub_div (hP : P ∈ rowStochastic ℝ S) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (P ^ n - 1)) atTop (𝓝 0) := by
  rw [tendsto_matrix_iff]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply]
  have hb : ∀ n : ℕ, |(P ^ n) i j - (1 : Matrix S S ℝ) i j| ≤ 1 := fun n => by
    have h0 := pow_nonneg' hP n i j
    have h1 := pow_le_one' hP n i j
    rw [one_apply]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  refine squeeze_zero_norm (a := fun n : ℕ => (n : ℝ)⁻¹) (fun n => ?_)
    tendsto_inv_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg n)) (hb n)

/-- A limit `B` of `A⁽ᵐᵏ⁾` along indices `mₖ → ∞` satisfies `BΠ = B = ΠB`. -/
theorem limit_mul (hP : P ∈ rowStochastic ℝ S) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {B : Matrix S S ℝ} (hB : Tendsto (fun k => cesaro P (m k)) atTop (𝓝 B)) :
    B * P = B ∧ P * B = B := by
  have h0 := (tendsto_pow_sub_div hP).comp hm
  constructor
  · have h1 : Tendsto (fun k => cesaro P (m k) * P - cesaro P (m k)) atTop (𝓝 (B * P - B)) :=
      ((hB.comp tendsto_id).mul_const P).sub hB
    simp_rw [cesaro_mul_sub] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 h0)
  · have h1 : Tendsto (fun k => P * cesaro P (m k) - cesaro P (m k)) atTop (𝓝 (P * B - B)) :=
      (hB.const_mul P).sub hB
    simp_rw [mul_cesaro_sub] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 h0)

theorem mul_pow_eq {B : Matrix S S ℝ} (h : B * P = B) (n : ℕ) : B * P ^ n = B := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]

theorem pow_mul_eq {B : Matrix S S ℝ} (h : P * B = B) (n : ℕ) : P ^ n * B = B := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, h]

theorem mul_cesaro_eq {B : Matrix S S ℝ} (h : B * P = B) {n : ℕ} (hn : 1 ≤ n) :
    B * cesaro P n = B := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [cesaro, mul_smul_comm, mul_sum]
  simp_rw [mul_pow_eq h]
  rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]

theorem cesaro_mul_eq {B : Matrix S S ℝ} (h : P * B = B) {n : ℕ} (hn : 1 ≤ n) :
    cesaro P n * B = B := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [cesaro, smul_mul_assoc, sum_mul]
  simp_rw [pow_mul_eq h]
  rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- **Theorem 11.1b.** The averages `A⁽ⁿ⁾ = (1/n) Σ_{k<n} Πᵏ` converge to a stochastic matrix
`Q` with `Q = QΠ = ΠQ`; hence `(1/n) Σ_{k<n} p₀Πᵏ = p₀A⁽ⁿ⁾ → p₀Q` for every `p₀`. -/
theorem theorem_11_1b (hP : P ∈ rowStochastic ℝ S) :
    ∃ Q ∈ rowStochastic ℝ S, Tendsto (cesaro P) atTop (𝓝 Q) ∧ Q * P = Q ∧ P * Q = Q ∧
      ∀ p₀ : S → ℝ, Tendsto (fun n => p₀ ᵥ* cesaro P n) atTop (𝓝 (p₀ ᵥ* Q)) := by
  have : FirstCountableTopology (Matrix S S ℝ) :=
    inferInstanceAs (FirstCountableTopology (S → S → ℝ))
  have hK := isCompact_unitBox (S := S)
  have hmem : ∀ n, cesaro P n ∈ unitBox S := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact mem_unitBox.2 fun i j => by simp [cesaro]
    · exact rowStochastic_subset_unitBox (cesaro_mem hP hn)
  obtain ⟨Q, -, φ, hφ, hQ⟩ := hK.tendsto_subseq hmem
  have hQm : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hQP, hPQ⟩ := limit_mul hP hQm hQ
  -- every limit point equals `Q`
  have huniq : ∀ {m : ℕ → ℕ}, Tendsto m atTop atTop → ∀ {B : Matrix S S ℝ},
      Tendsto (fun k => cesaro P (m k)) atTop (𝓝 B) → B = Q := by
    intro m hm B hB
    obtain ⟨hBP, hPB⟩ := limit_mul hP hm hB
    have e2 : B * Q = B := by
      have := hQ.const_mul B
      refine tendsto_nhds_unique this (tendsto_const_nhds.congr' ?_)
      filter_upwards [hQm.eventually_ge_atTop 1] with k hk
      exact (mul_cesaro_eq hBP hk).symm
    have e3 : B * Q = Q := by
      have := hB.mul_const Q
      refine tendsto_nhds_unique this (tendsto_const_nhds.congr' ?_)
      filter_upwards [hm.eventually_ge_atTop 1] with k hk
      exact (cesaro_mul_eq hPQ hk).symm
    rw [← e2, e3]
  have hconv : Tendsto (cesaro P) atTop (𝓝 Q) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨B, -, ψ, hψ, hB⟩ := hK.tendsto_subseq fun k => hmem (ns k)
    have hBQ := huniq (hns.comp hψ.tendsto_atTop) hB
    exact ⟨ψ, hBQ ▸ hB⟩
  have hQs : Q ∈ rowStochastic ℝ S :=
    isClosed_rowStochastic.mem_of_tendsto hconv
      (eventually_atTop.2 ⟨1, fun n hn => cesaro_mem hP hn⟩)
  refine ⟨Q, hQs, hconv, hQP, hPQ, fun p₀ => ?_⟩
  have hc : Continuous fun M : Matrix S S ℝ => p₀ ᵥ* M :=
    continuous_const.matrix_vecMul continuous_id
  exact (hc.tendsto Q).comp hconv

/-- **Theorem 11.1c.** Each row of `Q` is an invariant distribution, hence so is `p₀Q` for every
`p₀ ∈ Δ`; and every invariant distribution `r` satisfies `rQ = r`: it is the convex combination
`Σᵢ rᵢ Qᵢ` of the rows of `Q`. -/
theorem theorem_11_1c (hP : P ∈ rowStochastic ℝ S) {Q : Matrix S S ℝ}
    (hQ : Tendsto (cesaro P) atTop (𝓝 Q)) :
    (∀ i, IsInvariantDist P (Q i)) ∧ (∀ p₀ ∈ simplex S, IsInvariantDist P (p₀ ᵥ* Q)) ∧
      ∀ r, IsInvariantDist P r → r ᵥ* Q = r := by
  have hm : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id
  obtain ⟨hQP, -⟩ := limit_mul hP hm hQ
  have hQs : Q ∈ rowStochastic ℝ S :=
    isClosed_rowStochastic.mem_of_tendsto hQ
      (eventually_atTop.2 ⟨1, fun n hn => cesaro_mem hP hn⟩)
  have hrow : ∀ i, IsInvariantDist P (Q i) := fun i => by
    refine ⟨⟨fun j => nonneg_of_mem_rowStochastic hQs, sum_row_of_mem_rowStochastic hQs i⟩, ?_⟩
    funext j
    have := congrFun (congrFun hQP i) j
    simpa [mul_apply, vecMul, dotProduct] using this
  refine ⟨hrow, fun p₀ hp₀ => ⟨simplex_vecMul hQs hp₀, ?_⟩, fun r hr => ?_⟩
  · rw [vecMul_vecMul, hQP]
  · have hpow : ∀ k, r ᵥ* P ^ k = r := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, hr.2]
    have hc : ∀ n, 1 ≤ n → r ᵥ* cesaro P n = r := fun n hn => by
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [cesaro, vecMul_smul, vecMul_sum]
      simp_rw [hpow]
      rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn',
        one_smul]
    have hcont : Continuous fun M : Matrix S S ℝ => r ᵥ* M :=
      continuous_const.matrix_vecMul continuous_id
    have := (hcont.tendsto Q).comp hQ
    refine tendsto_nhds_unique this (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hc n hn).symm

end StokeyLucasPrescott.StrongConvergence
