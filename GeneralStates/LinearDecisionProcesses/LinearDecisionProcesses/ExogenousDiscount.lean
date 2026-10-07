/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearDecisionProcesses.OrderContraction
import LinearDecisionProcesses.Pospace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exogenous discount processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.4.1 (pp. 194–195).

`Z` is finite (as in §6.1.4.2), `Q` a stochastic matrix and `β ≥ 0` the discount function, and
`(K_Q h)(z) = β(z) ∑_{z'} h(z')Q(z, z')` (6.10) acts on `ℝ^Z` with the supremum norm.

* **Lemma 6.1.4**: `(K_Q^n h)(z) = 𝔼_z β₀ ⋯ β_{n−1} h(Z_n)`, the expectation being the sum over
  the paths `z = z₀, z₁, …, z_n` weighted by `∏ Q(z_t, z_{t+1})`.
* **Lemma 6.1.5**: `ρ(K) < 1` iff `‖Kⁿh‖ ≤ λ‖h‖` for some `n ≥ 1` and `λ ∈ [0, 1)`; this holds for
  every bounded linear operator on a Banach lattice.
* **Exercise 6.1.1**: if `ρ(K_Q) < 1`, the price `q = ∑_{t ≥ 0} K_Q^t h` of the cash flow
  `(h(Z_t))` exists and is the unique solution of `q = h + K_Q q`, i.e. `q = (I − K_Q)⁻¹h`.
-/

open Set Function Filter Topology

namespace SargentStachurski.LinearDecisionProcesses

/-- The supremum norm of `ℝ^ι` is a lattice norm. -/
theorem hasSolidNorm_pi {ι : Type*} [Fintype ι] : HasSolidNorm (ι → ℝ) :=
  ⟨fun f g h => (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact (show |f i| ≤ |g i| from h i).trans ((Real.norm_eq_abs (g i)).symm.trans_le
      (norm_le_pi_norm g i))⟩

attribute [local instance] hasSolidNorm_pi

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E]

omit [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] in
/-- **Lemma 6.1.5** (p. 195): `ρ(K) < 1` iff `‖Kⁿh‖ ≤ λ‖h‖` for all `h`, for some `n ≥ 1` and
`λ ∈ [0, 1)` (Gelfand's formula, as in Example 4.1.1). -/
theorem lemma_6_1_5 (K : E →L[ℝ] E) :
    specRad K < 1 ↔ ∃ n, 0 < n ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ h, ‖(K ^ n) h‖ ≤ lam * ‖h‖ := by
  constructor
  · intro hρ
    obtain ⟨k, hk, hlt⟩ := exercise_A_4_2 hρ
    exact ⟨k, hk, ‖K ^ k‖, norm_nonneg _, hlt, fun h => (K ^ k).le_opNorm h⟩
  · rintro ⟨n, hn, lam, hlam0, hlam1, hK⟩
    have hnorm : ‖K ^ n‖ ≤ lam := ContinuousLinearMap.opNorm_le_bound _ hlam0 hK
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hle : specRad K ≤ ‖K ^ (m + 1)‖ ^ (1 / ((m : ℝ) + 1)) :=
      ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ m
    refine hle.trans_lt ((Real.rpow_le_rpow (norm_nonneg _) hnorm (by positivity)).trans_lt ?_)
    exact Real.rpow_lt_one hlam0 hlam1 (by positivity)

omit [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] in
/-- Iterating `v ↦ h + Kv` from `0` gives the partial sums `∑_{t < n} Kᵗh`. -/
theorem iterate_affine_zero (K : E →L[ℝ] E) (h : E) (n : ℕ) :
    (fun v => h + K v)^[n] 0 = ∑ t ∈ Finset.range n, (K ^ t) h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ', map_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ']
    rfl

variable [CompleteSpace E]

/-- **Exercise 6.1.1** (p. 195), operator form: if `K` is positive and `ρ(K) < 1`, then the
partial sums `∑_{t < n} Kᵗh` converge to the unique `q` with `q = h + Kq`, i.e. `q = (I − K)⁻¹h`. -/
theorem exercise_6_1_1 {K : E →L[ℝ] E} (hK : IsPositiveOp K) (hρ : specRad K < 1) (h : E) :
    ∃ q, q = h + K q ∧ (∀ w, w = h + K w → w = q) ∧
      Tendsto (fun n => ∑ t ∈ Finset.range n, (K ^ t) h) atTop (𝓝 q) := by
  have : Nonempty E := ⟨0⟩
  have hι : IsIsoOrderEmbedding (id : E → E) :=
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩
  have hcon : IsOrderContraction id (fun v => h + K v) K := ⟨example_4_1_1 hK hρ, fun v w => by
    change |h + K v - (h + K w)| ≤ K |v - w|
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact hK.abs_le _⟩
  obtain ⟨q, hq, huniq, hlim⟩ := (theorem_4_1_4 hι hcon).1
  refine ⟨q, hq.symm, fun w hw => huniq w hw.symm, (hlim 0).congr fun n => ?_⟩
  exact iterate_affine_zero K h n

end BanachLattice

/-! ### The finite exogenous discount operator -/

namespace Exo

variable {Z : Type*} [Fintype Z]

/-- `(K_Q h)(z) = β(z) ∑_{z'} h(z')Q(z, z')` (6.10), linear. -/
def KLin (β : Z → ℝ) (Q : Z → Z → ℝ) : (Z → ℝ) →ₗ[ℝ] (Z → ℝ) where
  toFun h z := β z * ∑ z', h z' * Q z z'
  map_add' h g := funext fun z => by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c h := funext fun z => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z' _ => by ring

/-- `K_Q` as a bounded linear operator on `ℝ^Z`. -/
noncomputable def K (β : Z → ℝ) (Q : Z → Z → ℝ) : (Z → ℝ) →L[ℝ] (Z → ℝ) :=
  LinearMap.toContinuousLinearMap (KLin β Q)

theorem K_apply (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) (z : Z) :
    K β Q h z = β z * ∑ z', h z' * Q z z' := rfl

theorem K_isPositive {β : Z → ℝ} {Q : Z → Z → ℝ} (hβ : ∀ z, 0 ≤ β z)
    (hQ : ∀ z z', 0 ≤ Q z z') : BanachLattice.IsPositiveOp (K β Q) := fun h hh z => by
  rw [K_apply]
  exact mul_nonneg (hβ z) (Finset.sum_nonneg fun z' _ => mul_nonneg (hh z') (hQ z z'))

/-- `𝔼_z β₀ ⋯ β_{n−1} h(Z_n)`: the sum over paths `z₀ = z, z₁, …, z_n` of
`∏_{t < n} β(z_t)Q(z_t, z_{t+1}) · h(z_n)`. -/
noncomputable def pathExp (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) :
    (n : ℕ) → Z → ℝ
  | 0, z => h z
  | n + 1, z => ∑ p : Fin (n + 1) → Z,
      (∏ t : Fin (n + 1), β ((Fin.cons z p : Fin (n + 2) → Z) t.castSucc) *
        Q ((Fin.cons z p : Fin (n + 2) → Z) t.castSucc) (p t)) * h (p (Fin.last n))

/-- The path sum unfolds one step: `𝔼_z[β₀ ⋯ β_n h(Z_{n+1})] = β(z) ∑_{z₁} Q(z, z₁)
𝔼_{z₁}[β₀ ⋯ β_{n−1} h(Z_n)]` (Markov property and iterated expectations). -/
theorem pathExp_succ (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) (n : ℕ) (z : Z) :
    pathExp β Q h (n + 1) z = β z * ∑ z₁, pathExp β Q h n z₁ * Q z z₁ := by
  cases n with
  | zero =>
    rw [pathExp, Finset.mul_sum, ← (Equiv.funUnique (Fin 1) Z).symm.sum_comp]
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    simp only [pathExp, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.castSucc_zero,
      Fin.cons_zero, Equiv.funUnique_symm_apply, Fin.last_zero]
    simp
    ring
  | succ n =>
    rw [pathExp, Finset.mul_sum, ← (Fin.consEquiv fun _ : Fin (n + 2) => Z).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    rw [pathExp, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ (n := n + 1), Fin.castSucc_zero,
      Fin.cons_zero, Fin.cons_succ]
    have hcast : ∀ t : Fin (n + 1), (Fin.cons z (Fin.cons z₁ p : Fin (n + 2) → Z) :
        Fin (n + 3) → Z) t.succ.castSucc = (Fin.cons z₁ p : Fin (n + 2) → Z) t.castSucc :=
      fun t => by rw [← Fin.succ_castSucc, Fin.cons_succ]
    have hce : (Fin.consEquiv fun _ : Fin (n + 2) => Z) (z₁, p) = Fin.cons z₁ p := rfl
    have hlast : (Fin.cons z₁ p : Fin (n + 2) → Z) (Fin.last (n + 1)) = p (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    simp only [hce, hcast, hlast]
    ring

/-- **Lemma 6.1.4** (p. 194): `(K_Qⁿ h)(z) = 𝔼_z β₀ ⋯ β_{n−1} h(Z_n)`. -/
theorem lemma_6_1_4 (β : Z → ℝ) (Q : Z → Z → ℝ) (h : Z → ℝ) (n : ℕ) (z : Z) :
    (K β Q ^ n) h z = pathExp β Q h n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pathExp_succ, pow_succ']
    change K β Q ((K β Q ^ n) h) z = _
    rw [K_apply]
    congr 1
    exact Finset.sum_congr rfl fun z₁ _ => by rw [ih]

/-- **Exercise 6.1.1** (p. 195): if `ρ(K_Q) < 1`, the price of the cash flow `(h(Z_t))_{t ≥ 0}`,
`q(z) = 𝔼_z ∑_{t ≥ 0} ∏_{i < t} β(Z_i) h(Z_t) = lim_n ∑_{t < n} 𝔼_z β₀ ⋯ β_{t−1} h(Z_t)`, exists and
is the unique solution of `q = h + K_Q q`, i.e. `q = (I − K_Q)⁻¹h`. -/
theorem exercise_6_1_1 {β : Z → ℝ} {Q : Z → Z → ℝ} (hβ : ∀ z, 0 ≤ β z) (hQ : ∀ z z', 0 ≤ Q z z')
    (hρ : BanachLattice.specRad (K β Q) < 1) (h : Z → ℝ) :
    ∃ q, q = h + K β Q q ∧ (∀ w, w = h + K β Q w → w = q) ∧
      ∀ z, Tendsto (fun n => ∑ t ∈ Finset.range n, pathExp β Q h t z) atTop (𝓝 (q z)) := by
  obtain ⟨q, hq, huniq, hlim⟩ := BanachLattice.exercise_6_1_1 (K_isPositive hβ hQ) hρ h
  refine ⟨q, hq, huniq, fun z => ?_⟩
  have := (continuous_apply z).continuousAt.tendsto.comp hlim
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, Finset.sum_apply, lemma_6_1_4]

end Exo

end SargentStachurski.LinearDecisionProcesses
