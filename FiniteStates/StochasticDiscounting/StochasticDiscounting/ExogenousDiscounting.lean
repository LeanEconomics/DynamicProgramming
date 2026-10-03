/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.Optimality

/-!
# Exogenous discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.1.5 (pp. 195–196).

The state is `(y, z)` with `y` endogenous and `z` exogenous and `Q`-Markov; the
discount factor `β(z)` depends on the exogenous component only; `R(y, a, y')` is
a stochastic kernel for the endogenous component. The Bellman equation is (6.22),
greedy policies are (6.23), and the model is the MDP with state-dependent
discounting on `Y × Z` with `P((y, z), a, (y', z')) = Q(z, z')R(y, a, y')`.

* Proposition 6.2.3 (Exercise 6.2.4): if `ρ(L_Z) < 1` for
  `L_Z(z, z') = β(z)Q(z, z')`, then Assumption 6.2.1 holds and so do all the
  conclusions of Proposition 6.2.2. For each policy `L_σ` has the product form of
  Lemma 6.1.3 with a kernel on `Y` that depends on `z` through `σ(y, z)`, which is
  why that lemma is proved here in the general form.
* Value function iteration converges in this model: `|Tv − Tw|(y, z)` is bounded
  by `(L_Z g)(z)` where `g(z) = max_y |v − w|(y, z)`, so
  `‖Tᵏv − Tᵏw‖ ≤ ‖L_Zᵏ‖‖v − w‖` and `T` is eventually contracting. The book
  defers the convergence of VFI to Chapter 8.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The exogenous discount model (§6.2.1.5): primitives (i)–(v) of p. 195–196. -/
structure Exogenous (Y Z A : Type*) [Fintype Y] [Fintype Z] [Fintype A] where
  Γ : Y × Z → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : Z → ℝ
  β_nonneg : ∀ z, 0 ≤ β z
  r : Y → A → ℝ
  Q : Matrix Z Z ℝ
  Q_markov : IsMarkov Q
  R : Y → A → Y → ℝ
  R_nonneg : ∀ y a y', 0 ≤ R y a y'
  R_rowsum : ∀ y a, ∑ y', R y a y' = 1

namespace Exogenous

variable {Y Z A : Type*} [Fintype Y] [Fintype Z] [Fintype A] (E : Exogenous Y Z A)

/-- The exogenous discount model as an MDP with state-dependent discounting on `Y × Z`
(p. 196): `P(x, a, x') = Q(z, z')R(y, a, y')` and `β(x, a, x') = β(z)`. -/
def toSDMDP : SDMDP (Y × Z) A where
  Γ := E.Γ
  Γ_nonempty := E.Γ_nonempty
  r := fun x a => E.r x.1 a
  β := fun x _ _ => E.β x.2
  β_nonneg := fun x _ _ => E.β_nonneg x.2
  P := fun x a x' => E.Q x.2 x'.2 * E.R x.1 a x'.1
  P_nonneg := fun _ _ _ => mul_nonneg (E.Q_markov.nonneg _ _) (E.R_nonneg _ _ _)
  P_rowsum := fun x a => by
    rw [Fintype.sum_prod_type]
    simp only [← sum_mul, E.Q_markov.rowsum, one_mul, E.R_rowsum]

/-- The exogenous discount operator `L_Z(z, z') = β(z)Q(z, z')` of Proposition 6.2.3. -/
def LZ : Matrix Z Z ℝ := discountOp (fun z _ => E.β z) E.Q

theorem LZ_apply (z z' : Z) : E.LZ z z' = E.β z * E.Q z z' := rfl

theorem LZ_nonneg (z z' : Z) : 0 ≤ E.LZ z z' := mul_nonneg (E.β_nonneg z) (E.Q_markov.nonneg z z')

/-- `L_σ` has the product form of Lemma 6.1.3, with the kernel `R(y, σ(y, z), y')` on `Y`. -/
theorem Lσ_eq (σ : Y × Z → A) :
    E.toSDMDP.Lσ σ = productDiscountOp (fun z _ => E.β z) E.Q fun x y' => E.R x.1 (σ x) y' := by
  ext x x'
  change E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 (σ x) x'.1) = E.β x.2 * E.Q x.2 x'.2 * E.R x.1 (σ x) x'.1
  ring

/-- `ρ(L_σ) = ρ(L_Z)` for every policy, by Lemma 6.1.3. -/
theorem specRad_Lσ [Nonempty Y] [Nonempty Z] (σ : Y × Z → A) :
    specRad (E.toSDMDP.Lσ σ) = specRad E.LZ := by
  rw [Lσ_eq]
  exact specRad_productDiscountOp (fun z _ => E.β_nonneg z) E.Q_markov.nonneg
    (fun x y' => E.R_nonneg _ _ _) fun x => E.R_rowsum _ _

/-- **Proposition 6.2.3** (p. 196), Exercise 6.2.4: if `ρ(L_Z) < 1` then Assumption 6.2.1 holds
for the exogenous discount model. -/
theorem spectralCondition [Nonempty Y] [Nonempty Z] (hρ : specRad E.LZ < 1) :
    E.toSDMDP.SpectralCondition := fun σ _ => by
  rw [E.specRad_Lσ σ]
  exact hρ

variable [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Y] [Nonempty Z]

/-- Proposition 6.2.3: the Bellman equation (6.22),
`v*(y, z) = max_{a ∈ Γ(y, z)} {r(y, a) + β(z) ∑_{y', z'} v*(y', z')Q(z, z')R(y, a, y')}`. -/
theorem bellman_equation (hρ : specRad E.LZ < 1) (y : Y) (z : Z) :
    E.toSDMDP.vstar (y, z) = (E.Γ (y, z)).sup' (E.Γ_nonempty _) fun a =>
      E.r y a + E.β z * ∑ x' : Y × Z, E.toSDMDP.vstar x' * E.Q z x'.2 * E.R y a x'.1 := by
  rw [E.toSDMDP.bellman_equation (E.spectralCondition hρ)]
  refine Finset.sup'_congr _ rfl fun a _ => ?_
  change E.r y a + ∑ x', E.toSDMDP.vstar x' * E.β z * (E.Q z x'.2 * E.R y a x'.1) = _
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- Proposition 6.2.3: `v*` is the unique solution of (6.22). -/
theorem eq_vstar_of_isFixedPt (hρ : specRad E.LZ < 1) {v : Y × Z → ℝ}
    (hv : IsFixedPt E.toSDMDP.T v) : v = E.toSDMDP.vstar :=
  E.toSDMDP.eq_vstar_of_isFixedPt (E.spectralCondition hρ) hv

/-- Proposition 6.2.3: a policy is optimal iff it is `v*`-greedy in the sense of (6.23). -/
theorem isOptimal_iff_isGreedy (hρ : specRad E.LZ < 1) (σ : Y × Z → A) :
    E.toSDMDP.IsOptimal σ ↔ E.toSDMDP.IsGreedy E.toSDMDP.vstar σ :=
  E.toSDMDP.isOptimal_iff_isGreedy (E.spectralCondition hρ) σ

/-- Proposition 6.2.3: an optimal policy exists. -/
theorem exists_isOptimal (hρ : specRad E.LZ < 1) : ∃ σ : Y × Z → A, E.toSDMDP.IsOptimal σ :=
  E.toSDMDP.exists_isOptimal (E.spectralCondition hρ)

/-! ### Value function iteration -/

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] in
/-- `g(z) = max_y |u(y, z)|`. -/
noncomputable def colMax (u : Y × Z → ℝ) : Z → ℝ := fun z =>
  univ.sup' univ_nonempty fun y => |u (y, z)|

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] [Fintype Z] in
theorem abs_le_colMax (u : Y × Z → ℝ) (x : Y × Z) : |u x| ≤ colMax u x.2 := by
  classical
  exact
  Finset.le_sup' (fun y => |u (y, x.2)|) (mem_univ x.1)

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] [Fintype Z] in
theorem colMax_nonneg (u : Y × Z → ℝ) (z : Z) : 0 ≤ colMax u z := by
  classical
  exact
  (abs_nonneg _).trans (abs_le_colMax u (Classical.arbitrary Y, z))

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] in
/-- `‖u‖_∞ = ‖g‖_∞`. -/
theorem norm_eq_norm_colMax (u : Y × Z → ℝ) : ‖u‖ = ‖colMax u‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro x
    rw [Real.norm_eq_abs]
    refine (abs_le_colMax u x).trans ?_
    have := norm_le_pi_norm (colMax u) x.2
    rwa [Real.norm_eq_abs, abs_of_nonneg (colMax_nonneg u _)] at this
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (colMax_nonneg u z)]
    refine Finset.sup'_le _ _ fun y _ => ?_
    have := norm_le_pi_norm u (y, z)
    rwa [Real.norm_eq_abs] at this

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] in
/-- The one-step bound: `|Tv − Tw|(y, z) ≤ (L_Z g)(z)` with `g = max_y |v − w|`. -/
theorem abs_T_sub_le (v w : Y × Z → ℝ) (x : Y × Z) :
    |E.toSDMDP.T v x - E.toSDMDP.T w x| ≤ (E.LZ *ᵥ colMax (v - w)) x.2 := by
  rw [SDMDP.T_apply, SDMDP.T_apply]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
  change |E.r x.1 a + ∑ x', v x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) -
    (E.r x.1 a + ∑ x', w x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1))| ≤ _
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  have hQ := E.Q_markov.nonneg
  calc |∑ x' : Y × Z, (v x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) -
          w x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1))|
      ≤ ∑ x' : Y × Z, colMax (v - w) x'.2 * (E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
        rw [show v x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) -
            w x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) =
            (v - w) x' * (E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1)) by
              simp only [Pi.sub_apply]; ring, abs_mul,
          abs_of_nonneg (mul_nonneg (E.β_nonneg _) (mul_nonneg (hQ _ _) (E.R_nonneg _ _ _)))]
        exact mul_le_mul_of_nonneg_right (abs_le_colMax (v - w) x')
          (mul_nonneg (E.β_nonneg _) (mul_nonneg (hQ _ _) (E.R_nonneg _ _ _)))
    _ = (E.LZ *ᵥ colMax (v - w)) x.2 := by
        rw [Fintype.sum_prod_type, sum_comm]
        simp only [mulVec, dotProduct, LZ_apply]
        refine sum_congr rfl fun z' _ => ?_
        have h : ∀ y', colMax (v - w) z' * (E.β x.2 * (E.Q x.2 z' * E.R x.1 a y')) =
            E.β x.2 * E.Q x.2 z' * colMax (v - w) z' * E.R x.1 a y' := fun y' => by ring
        simp only [h]
        rw [← mul_sum, E.R_rowsum, mul_one]

omit [DecidableEq Y] [DecidableEq A] [Nonempty Z] in
/-- Iterating: `max_y |Tᵏv − Tᵏw|(y, z) ≤ (L_Zᵏ g)(z)`. -/
theorem colMax_iterate_sub_le (v w : Y × Z → ℝ) (k : ℕ) :
    colMax (E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w) ≤ E.LZ ^ k *ᵥ colMax (v - w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro z
    rw [iterate_succ_apply', iterate_succ_apply']
    refine Finset.sup'_le _ _ fun y _ => ?_
    refine (E.abs_T_sub_le _ _ (y, z)).trans ?_
    have := mulVec_le_mulVec_of_nonneg E.LZ_nonneg ih z
    rwa [mulVec_mulVec, ← pow_succ'] at this

omit [DecidableEq Y] [DecidableEq A] [Nonempty Z] in
/-- `‖Tᵏv − Tᵏw‖_∞ ≤ ‖L_Zᵏ‖‖v − w‖_∞`. -/
theorem norm_iterate_T_sub_le (v w : Y × Z → ℝ) (k : ℕ) :
    ‖E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w‖ ≤ ‖E.LZ ^ k‖ * ‖v - w‖ := by
  rw [norm_eq_norm_colMax (E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w), norm_eq_norm_colMax (v - w)]
  calc ‖colMax (E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w)‖ ≤ ‖E.LZ ^ k *ᵥ colMax (v - w)‖ :=
        norm_le_norm_of_abs_le_fun
          (fun z => sum_nonneg fun z' _ =>
            mul_nonneg (pow_nonneg_entries E.LZ_nonneg k z z') (colMax_nonneg _ _))
          (fun z => by
            rw [abs_of_nonneg (colMax_nonneg _ _)]
            exact E.colMax_iterate_sub_le v w k z)
    _ ≤ ‖E.LZ ^ k‖ * ‖colMax (v - w)‖ := Matrix.linfty_opNorm_mulVec _ _

omit [DecidableEq Y] [DecidableEq A] in
/-- Under `ρ(L_Z) < 1` the Bellman operator of the exogenous discount model is eventually
contracting under the supremum norm. -/
theorem exists_isContractionOn_iterate_T (hρ : specRad E.LZ < 1) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (E.toSDMDP.T^[k]) Set.univ ‖E.LZ ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero E.LZ hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  exact ⟨k, hk0, Set.mapsTo_univ _ _, norm_nonneg _, hk1, fun v _ w _ =>
    E.norm_iterate_T_sub_le v w k⟩

omit [DecidableEq Y] [DecidableEq A] [DecidableEq Z] in
/-- Value function iteration converges in the exogenous discount model: `T` is globally stable
on `ℝ^{Y × Z}` when `ρ(L_Z) < 1`, by Theorem 6.1.5. -/
theorem globallyStable_T (hρ : specRad E.LZ < 1) : GloballyStable E.toSDMDP.T := by
  classical
  obtain ⟨k, hk, hc⟩ := E.exists_isContractionOn_iterate_T hρ
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- `Tᵏv → v*` for every `v` when `ρ(L_Z) < 1`. -/
theorem tendsto_iterate_T (hρ : specRad E.LZ < 1) (v : Y × Z → ℝ) :
    Tendsto (fun k : ℕ => E.toSDMDP.T^[k] v) atTop (𝓝 E.toSDMDP.vstar) := by
  obtain ⟨u', hu', -, hconv⟩ := E.globallyStable_T hρ
  rw [E.eq_vstar_of_isFixedPt hρ hu'] at hconv
  exact hconv v

end Exogenous

end SargentStachurski.StochasticDiscounting
