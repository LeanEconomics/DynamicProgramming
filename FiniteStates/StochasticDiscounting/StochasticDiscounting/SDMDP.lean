/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.EventualContraction

/-!
# MDPs with state-dependent discounting: the model and finite lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.1.1–§6.2.1.2
(pp. 192–194).

An MDP with state-dependent discounting replaces the constant `β` of a regular
MDP `(Γ, β, r, P)` by a function `β(x, a, x') ≥ 0` of the current state, the
action and the next state. The policy operator (6.16) is `T_σ v = r_σ + L_σ v`
with the discount operator (6.17) `L_σ(x, x') = β(x, σ(x), x')P(x, σ(x), x')`.
Under Assumption 6.2.1, `ρ(L_σ) < 1` for every feasible `σ`:

* Lemma 6.2.1: `I − L_σ` is invertible and `T_σ` has the unique fixed point
  `v_σ = (I − L_σ)⁻¹ r_σ`, (6.18).
* Exercise 6.2.1: `v_σ = ∑ₜ L_σᵗ r_σ`, the lifetime value (6.19) in operator
  form; `T_σᵏv` is the `k`-period value with terminal payoff `v`.
* Exercise 6.2.2: `T_σ` is globally stable on `ℝ^X` (Example 6.1.2).
* Exercise 6.2.3: Assumption 6.2.1 holds whenever `βP ≤ L` on the feasible pairs
  for some `L` with `ρ(L) < 1`; in particular whenever `sup β < 1` (p. 193).

As in Chapter 5, `r`, `β` and `P` are given on all of `X × A`, with `P(x, a, ·)`
a distribution for every `a`; values off the feasible set never enter.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- An MDP with state-dependent discounting (§6.2.1.1): `(Γ, β, r, P)` with
`β : G × X → ℝ₊`. -/
structure SDMDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  r : X → A → ℝ
  β : X → A → X → ℝ
  β_nonneg : ∀ x a x', 0 ≤ β x a x'
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_rowsum : ∀ x a, ∑ x', P x a x' = 1

namespace SDMDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : SDMDP X A)

/-- The feasible state–action pairs `G`. -/
def Feasible (x : X) (a : A) : Prop := a ∈ M.Γ x

/-- A feasible policy: `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ M.Γ x

/-- The set `Σ` of feasible policies, as a subtype. -/
abbrev Policy := {σ : X → A // M.IsFeasible σ}

/-- A feasible policy exists. -/
noncomputable def defaultPolicy : M.Policy :=
  ⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty M.Policy := ⟨M.defaultPolicy⟩

/-- The closed-loop transition matrix `P_σ(x, x') = P(x, σ(x), x')` (p. 194). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

theorem Pσ_apply (σ : X → A) (x x' : X) : M.Pσ σ x x' = M.P x (σ x) x' := rfl

theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The discount operator (6.17): `L_σ(x, x') = β(x, σ(x), x')P(x, σ(x), x')`. -/
def Lσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.β x (σ x) x' * M.P x (σ x) x'

theorem Lσ_apply (σ : X → A) (x x' : X) : M.Lσ σ x x' = M.β x (σ x) x' * M.P x (σ x) x' := rfl

theorem Lσ_nonneg (σ : X → A) (x x' : X) : 0 ≤ M.Lσ σ x x' :=
  mul_nonneg (M.β_nonneg _ _ _) (M.P_nonneg _ _ _)

/-- `L_σ` is the discount operator (6.4) for `b(x, x') = β(x, σ(x), x')` and `P_σ`. -/
theorem Lσ_eq_discountOp (σ : X → A) :
    M.Lσ σ = discountOp (fun x x' => M.β x (σ x) x') (M.Pσ σ) := rfl

/-- The reward under `σ`: `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- The action value, the expression maximised in (6.15):
`r(x, a) + ∑ v(x')β(x, a, x')P(x, a, x')`. -/
def B (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + ∑ x', v x' * M.β x a x' * M.P x a x'

/-- The policy operator (6.16). -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.B v x (σ x)

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    M.Tσ σ v x = M.r x (σ x) + ∑ x', v x' * M.β x (σ x) x' * M.P x (σ x) x' := rfl

/-- (6.16) in operator form: `T_σ v = r_σ + L_σ v`. -/
theorem Tσ_eq (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + M.Lσ σ *ᵥ v := by
  funext x
  simp only [Tσ, B, rσ, Pi.add_apply, mulVec, dotProduct, Lσ_apply]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- The action value is order preserving in `v`. -/
theorem B_mono {v v' : X → ℝ} (hvv' : v ≤ v') (x : X) (a : A) : M.B v x a ≤ M.B v' x a := by
  unfold B
  refine add_le_add le_rfl (sum_le_sum fun x' _ => ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hvv' x') (M.β_nonneg x a x')) (M.P_nonneg x a x')

/-- `T_σ` is order preserving, since `L_σ ≥ 0`. -/
theorem Tσ_monotone (σ : X → A) : Monotone (M.Tσ σ) := fun _ _ h x => M.B_mono h x (σ x)

/-- **Assumption 6.2.1** (p. 193): `ρ(L_σ) < 1` for every feasible policy. -/
def SpectralCondition : Prop := ∀ σ : X → A, M.IsFeasible σ → specRad (M.Lσ σ) < 1

/-- Exercise 6.2.3 (p. 194): Assumption 6.2.1 holds whenever `β(x, a, x')P(x, a, x') ≤ L(x, x')`
on the feasible pairs for some `L` with `ρ(L) < 1`, by monotonicity of the spectral radius
(Exercise 2.2.28). -/
theorem spectralCondition_of_dominated [Nonempty X] {L : Matrix X X ℝ} (hρ : specRad L < 1)
    (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x') : M.SpectralCondition :=
  fun σ hσ => (specRad_le_of_le (M.Lσ_nonneg σ) fun x x' => hdom x (σ x) x' (hσ x)).trans_lt hρ

/-- The sufficient condition of p. 193: if `β ≤ b < 1` on the feasible pairs then
Assumption 6.2.1 holds, since `L_σ ≤ bP_σ` and `ρ(bP_σ) = b`. -/
theorem spectralCondition_of_le [Nonempty X] {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hβ : ∀ x a x', a ∈ M.Γ x → M.β x a x' ≤ b) : M.SpectralCondition := by
  intro σ hσ
  have h1 : specRad (M.Lσ σ) ≤ specRad (b • M.Pσ σ) :=
    specRad_le_of_le (M.Lσ_nonneg σ) fun x x' => by
      rw [Lσ_apply, Matrix.smul_apply, smul_eq_mul, Pσ_apply]
      exact mul_le_mul_of_nonneg_right (hβ x (σ x) x' (hσ x)) (M.P_nonneg _ _ _)
  rw [specRad_smul_isMarkov (M.isMarkov_Pσ σ) hb0] at h1
  exact h1.trans_lt hb1

/-! ### Lifetime values (§6.2.1.2) -/

variable [DecidableEq X]

/-- The lifetime value of `σ`, (6.18): `v_σ = (I − L_σ)⁻¹ r_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := (1 - M.Lσ σ)⁻¹ *ᵥ M.rσ σ

theorem vσ_eq_inv (σ : X → A) : M.vσ σ = (1 - M.Lσ σ)⁻¹ *ᵥ M.rσ σ := rfl

/-- Exercise 6.2.1 in finite-horizon form: `T_σᵏv = ∑_{t<k} L_σᵗ r_σ + L_σᵏ v`, the `k`-period
discounted value of following `σ` with terminal payoff `v`. -/
theorem iterate_Tσ_eq (σ : X → A) (v : X → ℝ) (k : ℕ) :
    (M.Tσ σ)^[k] v = (∑ t ∈ range k, M.Lσ σ ^ t *ᵥ M.rσ σ) + M.Lσ σ ^ k *ᵥ v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, Tσ_eq, sum_range_succ', pow_zero, one_mulVec, mulVec_add,
      mulVec_sum]
    have h1 : ∀ (w : X → ℝ) (t : ℕ), M.Lσ σ *ᵥ (M.Lσ σ ^ t *ᵥ w) = M.Lσ σ ^ (t + 1) *ᵥ w :=
      fun w t => by rw [mulVec_mulVec, ← pow_succ']
    simp only [h1]
    abel

variable [Nonempty X]

/-- **Lemma 6.2.1** (p. 193), first part: `I − L_σ` is invertible when `ρ(L_σ) < 1`. -/
theorem isUnit_one_sub_Lσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) : IsUnit (1 - M.Lσ σ) :=
  (neumann_series _ hρ).1

/-- **Lemma 6.2.1** (p. 193): `v_σ = (I − L_σ)⁻¹ r_σ` is a fixed point of `T_σ`. -/
theorem isFixedPt_vσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) : IsFixedPt (M.Tσ σ) (M.vσ σ) := by
  change M.Tσ σ (M.vσ σ) = M.vσ σ
  rw [Tσ_eq, vσ]
  exact (inv_mulVec_eq_add hρ _).symm

/-- **Lemma 6.2.1** (p. 193): `v_σ` is the only fixed point of `T_σ` in `ℝ^X`. -/
theorem eq_vσ_of_isFixedPt {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) {v : X → ℝ}
    (hv : IsFixedPt (M.Tσ σ) v) : v = M.vσ σ := by
  have h := hv.eq
  rw [Tσ_eq] at h
  exact (eq_add_mulVec_iff hρ _ _).1 h.symm

omit [DecidableEq X] in
/-- Lemma 6.2.1 as a unique-existence statement. -/
theorem existsUnique_fixedPt_Tσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) :
    ∃! v : X → ℝ, IsFixedPt (M.Tσ σ) v := by
  classical
  exact
  ⟨M.vσ σ, M.isFixedPt_vσ hρ, fun _ hv => M.eq_vσ_of_isFixedPt hρ hv⟩

/-- Exercise 6.2.1 (p. 194), (6.19) in operator form: `v_σ = ∑ₜ L_σᵗ r_σ`, the expected discounted
sum of rewards along `P_σ` with the discount factors `β(Xₜ₋₁, σ(Xₜ₋₁), Xₜ)`, by Theorem 6.1.1. -/
theorem vσ_eq_tsum {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) :
    M.vσ σ = ∑' t : ℕ, M.Lσ σ ^ t *ᵥ M.rσ σ :=
  inv_mulVec_eq_tsum hρ _

omit [DecidableEq X] [Nonempty X] in
/-- `T_σ` is the affine map of Example 6.1.2. -/
theorem Tσ_eq_affineOp (σ : X → A) : M.Tσ σ = affineOp (M.Lσ σ) (M.rσ σ) := by
  classical
  funext v
  rw [Tσ_eq, affineOp, add_comm]

omit [DecidableEq X] in
/-- Exercise 6.2.2 (p. 194): under `ρ(L_σ) < 1`, `T_σ` is globally stable on `ℝ^X`. -/
theorem globallyStable_Tσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) : GloballyStable (M.Tσ σ) := by
  classical
  rw [Tσ_eq_affineOp]
  exact globallyStable_affineOp hρ _

/-- `T_σᵏ v → v_σ` for every `v`. -/
theorem tendsto_iterate_Tσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (M.Tσ σ)^[k] v) atTop (𝓝 (M.vσ σ)) := by
  obtain ⟨u', hu', -, hconv⟩ := M.globallyStable_Tσ hρ
  rw [M.eq_vσ_of_isFixedPt hρ hu'] at hconv
  exact hconv v

end SDMDP

end SargentStachurski.StochasticDiscounting
