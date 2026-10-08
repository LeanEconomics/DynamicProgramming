/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnBanachSpace.OrderContraction
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Structural estimation with state-dependent discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.3.2 (pp. 143–144).

`X` and `A` are finite and nonempty, `G = X × A`, and the Bellman equation is (4.23),
`g(x, a) = ∑_{x'} max_{a'} [r(x', a') + β(x')g(x', a')] P(x, a, x')`, with a state-dependent
discount factor `β(x) ≥ 0`.

* `ℝⁿ` with the supremum norm is a Banach lattice (its norm is a lattice norm).
* The policy operators `T̂_σ g = r̂_σ + K_σ g` with `K_σ` as in (4.25); the greedy policies (4.24),
  regularity, and the Bellman operator.
* **Proposition 4.2.5**: if `ρ(K_σ) < 1` for every `σ`, the fundamental optimality properties hold,
  VFI, OPI and HPI converge, and HPI converges in finitely many steps (Theorems 4.1.7 and 2.2.6).
* With a constant discount `β(x) ≤ b < 1`, `ρ(K_σ) ≤ b < 1` always holds.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnBanachSpace

/-- The supremum norm of `ℝ^ι` is a lattice norm. -/
theorem hasSolidNorm_pi {ι : Type*} [Fintype ι] : HasSolidNorm (ι → ℝ) :=
  ⟨fun f g h => (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact (show |f i| ≤ |g i| from h i).trans ((Real.norm_eq_abs (g i)).symm.trans_le
      (norm_le_pi_norm g i))⟩

attribute [local instance] hasSolidNorm_pi

/-- The finite structural estimation model of §4.2.3.2. -/
structure FiniteSE (X A : Type*) [Fintype X] [Fintype A] where
  /-- the reward -/
  r : X × A → ℝ
  /-- the state-dependent discount factor -/
  βf : X → ℝ
  βf_nonneg : ∀ x, 0 ≤ βf x
  /-- the transition probabilities from `G` to `X` -/
  P : X × A → X → ℝ
  P_nonneg : ∀ p x', 0 ≤ P p x'
  P_sum : ∀ p, ∑ x', P p x' = 1

namespace FiniteSE

variable {X A : Type*} [Fintype X] [Fintype A] (M : FiniteSE X A)

/-- `K_σ` (4.25): `(K_σ g)(x, a) = ∑_{x'} β(x')g(x', σ(x'))P(x, a, x')`, linear. -/
def Klin (σ : X → A) : (X × A → ℝ) →ₗ[ℝ] (X × A → ℝ) where
  toFun g p := ∑ x', M.βf x' * g (x', σ x') * M.P p x'
  map_add' g h := funext fun p => by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x' _ => by ring
  map_smul' c g := funext fun p => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring

/-- `K_σ` as a bounded linear operator. -/
noncomputable def K (σ : X → A) : (X × A → ℝ) →L[ℝ] (X × A → ℝ) :=
  LinearMap.toContinuousLinearMap (M.Klin σ)

theorem K_apply (σ : X → A) (g : X × A → ℝ) (p : X × A) :
    M.K σ g p = ∑ x', M.βf x' * g (x', σ x') * M.P p x' := rfl

theorem K_isPositive (σ : X → A) : BanachLattice.IsPositiveOp (M.K σ) := fun g hg p => by
  rw [M.K_apply]
  exact Finset.sum_nonneg fun x' _ =>
    mul_nonneg (mul_nonneg (M.βf_nonneg x') (hg _)) (M.P_nonneg p x')

/-- `r̂_σ(x, a) = ∑_{x'} r(x', σ(x'))P(x, a, x')`. -/
def rhat (σ : X → A) : X × A → ℝ := fun p => ∑ x', M.r (x', σ x') * M.P p x'

/-- The policy operators `T̂_σ g = r̂_σ + K_σ g`. -/
noncomputable def adp [Nonempty A] : ADP (X × A → ℝ) (X → A) where
  T σ g := M.rhat σ + M.K σ g
  mono σ _ _ h := add_le_add le_rfl ((M.K_isPositive σ).mono h)
  nonempty := ⟨fun _ => Classical.arbitrary A⟩

theorem adp_T_apply [Nonempty A] (σ : X → A) (g : X × A → ℝ) (p : X × A) :
    M.adp.T σ g p = ∑ x', (M.r (x', σ x') + M.βf x' * g (x', σ x')) * M.P p x' := by
  change M.rhat σ p + M.K σ g p = _
  rw [rhat, M.K_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- (4.24): a policy maximizing `r(x, ·) + β(x)g(x, ·)` at every state is `g`-greedy. -/
theorem isGreedy_of_argmax [Nonempty A] (g : X × A → ℝ) (σ : X → A)
    (hσ : ∀ x a, M.r (x, a) + M.βf x * g (x, a) ≤ M.r (x, σ x) + M.βf x * g (x, σ x)) :
    M.adp.IsGreedy g σ := fun τ p => by
  rw [M.adp_T_apply, M.adp_T_apply]
  exact Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (hσ x' (τ x')) (M.P_nonneg p x')

theorem exists_argmax [Nonempty A] (g : X × A → ℝ) :
    ∃ σ : X → A, ∀ x a, M.r (x, a) + M.βf x * g (x, a) ≤ M.r (x, σ x) + M.βf x * g (x, σ x) := by
  choose σ _ hσ using fun x => Finset.exists_max_image Finset.univ
    (fun a => M.r (x, a) + M.βf x * g (x, a)) Finset.univ_nonempty
  exact ⟨σ, fun x a => hσ x a (Finset.mem_univ a)⟩

/-- §4.2.3.2: the ADP `(ℝ^G, 𝕋̂_SE)` is regular. -/
theorem adp_regular [Nonempty A] : M.adp.Regular := fun g => by
  obtain ⟨σ, hσ⟩ := M.exists_argmax g
  exact ⟨σ, M.isGreedy_of_argmax g σ hσ⟩

/-- (4.23): the Bellman operator is
`(T̂g)(x, a) = ∑_{x'} max_{a'} [r(x', a') + β(x')g(x', a')] P(x, a, x')`. -/
theorem adp_bellman_apply [Nonempty A] (g : X × A → ℝ) (p : X × A) :
    M.adp.bellman g p = ∑ x', (Finset.univ.sup' Finset.univ_nonempty fun a' =>
      M.r (x', a') + M.βf x' * g (x', a')) * M.P p x' := by
  obtain ⟨σ, hσ⟩ := M.exists_argmax g
  have hg := M.adp.isGreedy_greedy (M.adp_regular g)
  have heq : M.adp.bellman g = M.adp.T σ g :=
    le_antisymm (M.isGreedy_of_argmax g σ hσ _) (hg σ)
  rw [heq, M.adp_T_apply]
  refine Finset.sum_congr rfl fun x' _ => ?_
  congr 1
  exact le_antisymm (Finset.le_sup' (fun a' => M.r (x', a') + M.βf x' * g (x', a'))
    (Finset.mem_univ _)) (Finset.sup'_le _ _ fun a' _ => hσ x' a')

theorem isIsoOrderEmbedding_id :
    BanachLattice.IsIsoOrderEmbedding (id : (X × A → ℝ) → (X × A → ℝ)) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

theorem isAdditive [Nonempty A] : BanachLattice.IsAdditive id M.adp M.rhat M.K :=
  ⟨M.K_isPositive, fun _ _ => rfl⟩

/-- **Proposition 4.2.5** (p. 144): if `ρ(K_σ) < 1` for every `σ`, the fundamental optimality
properties hold for `(ℝ^G, 𝕋̂_SE)`, OPI, VFI and HPI all converge, and HPI converges in finitely
many steps. -/
theorem proposition_4_2_5 [Nonempty A] (hρ : ∀ σ, BanachLattice.specRad (M.K σ) < 1) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      (∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar) ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard hw g)^[n] v) := by
  have hfin : M.adp.IsFinite := finite_range _
  obtain ⟨hw, h12⟩ := BanachLattice.theorem_4_1_7 isIsoOrderEmbedding_id M.adp M.adp_regular
    hfin M.isAdditive hρ
  have hgs : M.adp.IsGloballyStable := fun σ =>
    (BanachLattice.theorem_4_1_4 isIsoOrderEmbedding_id
      ⟨BanachLattice.example_4_1_1 (M.K_isPositive σ) (hρ σ), M.isAdditive.abs_sub σ⟩).1
  exact ⟨hw, h12.1, h12.2,
    (ADP.fundamentalOptimality_of_finite hgs.isOrderStable M.adp_regular hfin).2⟩

/-- With `β(x) ≤ b < 1` everywhere, `‖K_σ‖ ≤ b`, so `ρ(K_σ) ≤ b < 1`: the condition of
Proposition 4.2.5 generalizes a constant discount factor below one. -/
theorem specRad_lt_one_of_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hβ : ∀ x, M.βf x ≤ b)
    (σ : X → A) : BanachLattice.specRad (M.K σ) < 1 := by
  refine ((BanachLattice.specRad_le_norm _).trans ?_).trans_lt hb1
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun g => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hb0 (norm_nonneg g))).2 fun p => ?_
  rw [Real.norm_eq_abs, M.K_apply]
  calc |∑ x', M.βf x' * g (x', σ x') * M.P p x'|
      ≤ ∑ x', |M.βf x' * g (x', σ x') * M.P p x'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', b * ‖g‖ * M.P p x' := Finset.sum_le_sum fun x' _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (M.βf_nonneg x'), abs_of_nonneg (M.P_nonneg p x')]
        refine mul_le_mul_of_nonneg_right (mul_le_mul (hβ x') ?_ (abs_nonneg _) hb0)
          (M.P_nonneg p x')
        exact (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm g _)
    _ = b * ‖g‖ := by rw [← Finset.mul_sum, M.P_sum, mul_one]

end FiniteSE

end SargentStachurski.ADPsOnBanachSpace
