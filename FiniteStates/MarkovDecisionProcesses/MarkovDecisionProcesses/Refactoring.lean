/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Bellman

/-!
# Operator factorisations: expected value functions and Q-factors

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.3.4–§5.3.5
(pp. 171–178).

The Bellman operator factors as `T = M D E` through three auxiliary operators:
`E` takes conditional expectations, `(Ev)(x, a) = ∑ v(x')P(x, a, x')`; `D`
discounts and adds rewards, `(Dg)(x, a) = r(x, a) + βg(x, a)`; `M` maximises
over feasible actions, `(Mq)(x) = max_{a ∈ Γ(x)} q(x, a)`. The other two
round trips `R = E M D` (expected value functions) and `S = D E M` (Q-factors)
are given explicitly (Exercise 5.3.5), satisfy the iterate relations of
Exercise 5.3.6, and are contractions of modulus `β` because `E` and `M` are
nonexpansive and `D` contracts (Exercise 5.3.7, Lemma 5.3.5). Their fixed
points are `g* = Ev*`, `q* = Dg*`, `v* = Mq*` (Proposition 5.3.6), and a policy
is optimal iff it is `v*`-greedy iff `g*`-greedy iff `q*`-greedy
(Corollary 5.3.7), which contains Proposition 5.3.4 on Q-factors
(Exercise 5.3.4). The policy versions `R_σ = E M_σ D`, `S_σ = D E M_σ`,
`T_σ = M_σ D E` satisfy `R_σᵏ = E T_σᵏ⁻¹ M_σ D` (Exercise 5.3.8), which gives the
equivalence of refactored and regular optimistic policy iteration (p. 178).

Functions on the feasible pairs `G` are represented as functions on `X × A`;
the maximisation `M` only ever looks at feasible actions.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- `E : ℝ^X → ℝ^G`, `(Ev)(x, a) = ∑ v(x')P(x, a, x')` (p. 172). -/
def E (v : X → ℝ) : X × A → ℝ := fun p => ∑ x', v x' * M.P p.1 p.2 x'

/-- `D : ℝ^G → ℝ^G`, `(Dg)(x, a) = r(x, a) + βg(x, a)` (p. 172). -/
def D (g : X × A → ℝ) : X × A → ℝ := fun p => M.r p.1 p.2 + M.β * g p

/-- `Mop : ℝ^G → ℝ^X`, `(Mq)(x) = max_{a ∈ Γ(x)} q(x, a)` (p. 172). -/
noncomputable def Mop (q : X × A → ℝ) : X → ℝ := fun x =>
  (M.Γ x).sup' (M.Γ_nonempty x) fun a => q (x, a)

/-- `D(Ev) = B(·, ·, v)`: discounting the expectation gives the action value. -/
theorem D_E (v : X → ℝ) (p : X × A) : M.D (M.E v) p = M.B v p.1 p.2 := rfl

/-- (5.40): `T = M D E`. -/
theorem T_eq_Mop_D_E (v : X → ℝ) : M.T v = M.Mop (M.D (M.E v)) := rfl

/-- The expected value Bellman operator `R = E M D` (5.40). -/
noncomputable def R (g : X × A → ℝ) : X × A → ℝ := M.E (M.Mop (M.D g))

/-- The Q-factor Bellman operator `S = D E M` (5.40), (5.39). -/
noncomputable def S (q : X × A → ℝ) : X × A → ℝ := M.D (M.E (M.Mop q))

/-- Exercise 5.3.5 (p. 173):
`(Rg)(x, a) = ∑ max_{a' ∈ Γ(x')} {r(x', a') + βg(x', a')} P(x, a, x')`. -/
theorem R_apply (g : X × A → ℝ) (p : X × A) :
    M.R g p = ∑ x', ((M.Γ x').sup' (M.Γ_nonempty x') fun a' => M.r x' a' + M.β * g (x', a')) *
      M.P p.1 p.2 x' := rfl

/-- Exercise 5.3.5 (p. 173), (5.39):
`(Sq)(x, a) = r(x, a) + β ∑ max_{a' ∈ Γ(x')} q(x', a') P(x, a, x')`. -/
theorem S_apply (q : X × A → ℝ) (p : X × A) :
    M.S q p = M.r p.1 p.2 + M.β * ∑ x', ((M.Γ x').sup' (M.Γ_nonempty x') fun a' => q (x', a')) *
      M.P p.1 p.2 x' := rfl

/-! ### Exercise 5.3.6: iterate relations -/

/-- `Rᵏ⁺¹ = E Tᵏ M D`. -/
theorem R_iterate_succ (k : ℕ) (g : X × A → ℝ) : M.R^[k + 1] g = M.E (M.T^[k] (M.Mop (M.D g))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Rᵏ⁺¹ = E M Sᵏ D`. -/
theorem R_iterate_succ' (k : ℕ) (g : X × A → ℝ) :
    M.R^[k + 1] g = M.E (M.Mop (M.S^[k] (M.D g))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Sᵏ⁺¹ = D Rᵏ E M`. -/
theorem S_iterate_succ (k : ℕ) (q : X × A → ℝ) : M.S^[k + 1] q = M.D (M.R^[k] (M.E (M.Mop q))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Sᵏ⁺¹ = D E Tᵏ M`. -/
theorem S_iterate_succ' (k : ℕ) (q : X × A → ℝ) :
    M.S^[k + 1] q = M.D (M.E (M.T^[k] (M.Mop q))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Tᵏ⁺¹ = M Sᵏ D E`. -/
theorem T_iterate_succ (k : ℕ) (v : X → ℝ) : M.T^[k + 1] v = M.Mop (M.S^[k] (M.D (M.E v))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `Tᵏ⁺¹ = M D Rᵏ E`. -/
theorem T_iterate_succ' (k : ℕ) (v : X → ℝ) : M.T^[k + 1] v = M.Mop (M.D (M.R^[k] (M.E v))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-! ### Exercise 5.3.7: `E` and `M` are nonexpansive, `D` is a contraction -/

/-- Exercise 5.3.7 (i): `‖Ev − Ev'‖ ≤ ‖v − v'‖`. -/
theorem norm_E_sub_le (v v' : X → ℝ) : ‖M.E v - M.E v'‖ ≤ ‖v - v'‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  rintro ⟨x, a⟩
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have := (M.isMarkov_Pσ fun _ => a).abs_mulVec_sub_le v v' x
  simp only [mulVec_apply_eq, Pσ_apply] at this
  exact this

/-- Exercise 5.3.7 (ii): `‖Mg − Mg'‖ ≤ ‖g − g'‖`. -/
theorem norm_Mop_sub_le (g g' : X × A → ℝ) : ‖M.Mop g - M.Mop g'‖ ≤ ‖g - g'‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, Mop, Mop]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
  have := norm_le_pi_norm (g - g') (x, a)
  simpa [Real.norm_eq_abs] using this

/-- Exercise 5.3.7 (iii): `‖Dq − Dq'‖ ≤ β‖q − q'‖`. -/
theorem norm_D_sub_le (q q' : X × A → ℝ) : ‖M.D q - M.D q'‖ ≤ M.β * ‖q - q'‖ := by
  have : M.D q - M.D q' = M.β • (q - q') := by
    funext p
    simp only [D, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg M.β_pos.le]

/-- Lemma 5.3.5 (p. 174): `R` is a contraction of modulus `β`. -/
theorem isContractionOn_R : IsContractionOn M.R Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le _ _ _ _ :=
    (M.norm_E_sub_le _ _).trans ((M.norm_Mop_sub_le _ _).trans (M.norm_D_sub_le _ _))

/-- Lemma 5.3.5 (p. 174), Exercise 5.3.4 (p. 171): `S` is a contraction of modulus `β`. -/
theorem isContractionOn_S : IsContractionOn M.S Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le _ _ _ _ :=
    (M.norm_D_sub_le _ _).trans (mul_le_mul_of_nonneg_left
      ((M.norm_E_sub_le _ _).trans (M.norm_Mop_sub_le _ _)) M.β_pos.le)

/-- Lemma 5.3.5 (p. 174): the factorisation proof that `T` is a contraction of modulus `β`. -/
theorem norm_T_sub_le (v v' : X → ℝ) : ‖M.T v - M.T v'‖ ≤ M.β * ‖v - v'‖ := by
  rw [T_eq_Mop_D_E, T_eq_Mop_D_E]
  exact (M.norm_Mop_sub_le _ _).trans ((M.norm_D_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left (M.norm_E_sub_le _ _) M.β_pos.le))

/-- `E`, `D` and `M` are order preserving. -/
theorem E_monotone : Monotone M.E := fun _ _ h _ =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (h x') (M.P_nonneg _ _ _)

theorem D_monotone : Monotone M.D := fun _ _ h p =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (h p) M.β_pos.le)

theorem Mop_monotone : Monotone M.Mop := fun _ _ h x =>
  Finset.sup'_mono_fun fun a _ => h (x, a)

/-- Exercise 5.3.4 (p. 171): `S` is order preserving. -/
theorem S_monotone : Monotone M.S := fun _ _ h =>
  M.D_monotone (M.E_monotone (M.Mop_monotone h))

theorem R_monotone : Monotone M.R := fun _ _ h =>
  M.E_monotone (M.Mop_monotone (M.D_monotone h))

/-! ### Fixed points (Proposition 5.3.6) and greedy policies (Corollary 5.3.7) -/

/-- `g`-greedy (p. 175): `σ(x)` maximises `r(x, a) + βg(x, a)` over `Γ(x)`. -/
def IsGGreedy (g : X × A → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.D g (x, a) ≤ M.D g (x, σ x)

/-- `q`-greedy (p. 175): `σ(x)` maximises `q(x, a)` over `Γ(x)`. -/
def IsQGreedy (q : X × A → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, q (x, a) ≤ q (x, σ x)

/-- `v`-greedy is `(Ev)`-greedy, since `D(Ev) = B(·, ·, v)`. -/
theorem isGreedy_iff_isGGreedy_E (v : X → ℝ) (σ : X → A) : M.IsGreedy v σ ↔ M.IsGGreedy (M.E v) σ :=
  Iff.rfl

/-- `g`-greedy is `(Dg)`-greedy. -/
theorem isGGreedy_iff_isQGreedy_D (g : X × A → ℝ) (σ : X → A) :
    M.IsGGreedy g σ ↔ M.IsQGreedy (M.D g) σ :=
  Iff.rfl

/-! ### Policy operators in the three spaces (§5.3.5.3) -/

/-- `(M_σ q)(x) = q(x, σ(x))` (p. 177). -/
def Mσ (σ : X → A) (q : X × A → ℝ) : X → ℝ := fun x => q (x, σ x)

/-- `T_σ = M_σ D E` (p. 177): the policy operator of (5.19). -/
theorem Tσ_eq_Mσ_D_E (σ : X → A) (v : X → ℝ) : M.Tσ σ v = Mσ σ (M.D (M.E v)) := rfl

/-- `R_σ = E M_σ D` (p. 177). -/
def Rσ (σ : X → A) (g : X × A → ℝ) : X × A → ℝ := M.E (Mσ σ (M.D g))

/-- `S_σ = D E M_σ` (p. 177). -/
def Sσ (σ : X → A) (q : X × A → ℝ) : X × A → ℝ := M.D (M.E (Mσ σ q))

/-- Exercise 5.3.8, (5.41): `R_σᵏ⁺¹ = E T_σᵏ M_σ D`. -/
theorem Rσ_iterate_succ (σ : X → A) (k : ℕ) (g : X × A → ℝ) :
    (M.Rσ σ)^[k + 1] g = M.E ((M.Tσ σ)^[k] (Mσ σ (M.D g))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- `S_σᵏ⁺¹ = D E T_σᵏ M_σ`. -/
theorem Sσ_iterate_succ (σ : X → A) (k : ℕ) (q : X × A → ℝ) :
    (M.Sσ σ)^[k + 1] q = M.D (M.E ((M.Tσ σ)^[k] (Mσ σ q))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    rfl

/-- Refactored OPI (p. 178): `R_σᵐ (Ev) = E (T_σᵐ v)`, so the expected value iterates of
Algorithm 5.5 started at `g₀ = Ev₀` are the images under `E` of the regular OPI iterates. -/
theorem Rσ_iterate_E (σ : X → A) (m : ℕ) (v : X → ℝ) :
    (M.Rσ σ)^[m] (M.E v) = M.E ((M.Tσ σ)^[m] v) := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [Rσ_iterate_succ, iterate_succ_apply]
    rfl

/-- Refactored OPI (p. 178): a policy is `(Ev)`-greedy iff it is `v`-greedy, so both algorithms
select the same policies. -/
theorem isGGreedy_E_iff (v : X → ℝ) (σ : X → A) : M.IsGGreedy (M.E v) σ ↔ M.IsGreedy v σ :=
  Iff.rfl

variable [DecidableEq X] [DecidableEq A]

/-- `g* = Ev*`: the expected value function of the optimal value. -/
noncomputable def gstar : X × A → ℝ := M.E M.vstar

/-- `q* = Dg*`: the optimal Q-factor. -/
noncomputable def qstar : X × A → ℝ := M.D M.gstar

/-- Proposition 5.3.6 (i), p. 175: `g* = Ev*` is a fixed point of `R`, since
`Ev* = ETv* = EMDEv*`. -/
theorem isFixedPt_R_gstar : IsFixedPt M.R M.gstar := by
  change M.E (M.Mop (M.D (M.E M.vstar))) = M.E M.vstar
  rw [← T_eq_Mop_D_E, M.isFixedPt_T_vstar.eq]

/-- Proposition 5.3.6: `g*` is the unique fixed point of `R` in `ℝ^G`. -/
theorem eq_gstar_of_isFixedPt {g : X × A → ℝ} (hg : IsFixedPt M.R g) : g = M.gstar :=
  M.isContractionOn_R.fixedPt_unique (Set.mem_univ g) (Set.mem_univ _) hg M.isFixedPt_R_gstar

/-- Proposition 5.3.6 (ii), p. 175: `q* = Dg*` is a fixed point of `S`. -/
theorem isFixedPt_S_qstar : IsFixedPt M.S M.qstar := by
  change M.D (M.E (M.Mop (M.D (M.E M.vstar)))) = M.D (M.E M.vstar)
  rw [← T_eq_Mop_D_E, M.isFixedPt_T_vstar.eq]

/-- Proposition 5.3.6: `q*` is the unique fixed point of `S` in `ℝ^G`. -/
theorem eq_qstar_of_isFixedPt {q : X × A → ℝ} (hq : IsFixedPt M.S q) : q = M.qstar :=
  M.isContractionOn_S.fixedPt_unique (Set.mem_univ q) (Set.mem_univ _) hq M.isFixedPt_S_qstar

/-- Proposition 5.3.6 (iii), p. 175: `v* = Mq*`. -/
theorem vstar_eq_Mop_qstar : M.vstar = M.Mop M.qstar :=
  M.isFixedPt_T_vstar.eq.symm

/-- The explicit forms (p. 175): `g*(x, a) = ∑ v*(x')P(x, a, x')`, `q*(x, a) = r(x, a) + βg*(x, a)`,
`v*(x) = max_{a ∈ Γ(x)} q*(x, a)`. -/
theorem gstar_apply (x : X) (a : A) : M.gstar (x, a) = ∑ x', M.vstar x' * M.P x a x' := rfl

theorem qstar_apply (x : X) (a : A) : M.qstar (x, a) = M.r x a + M.β * M.gstar (x, a) := rfl

theorem vstar_apply_eq_sup'_qstar (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a => M.qstar (x, a) :=
  congrFun M.vstar_eq_Mop_qstar x

/-- Successive approximation with `R` and `S` converges to `g*` and `q*` (p. 176). -/
theorem tendsto_iterate_R (g : X × A → ℝ) : Tendsto (fun k : ℕ => M.R^[k] g) atTop (𝓝 M.gstar) :=
  M.isContractionOn_R.tendsto_iterate_fixedPt (Set.mem_univ g) (Set.mem_univ _) M.isFixedPt_R_gstar

theorem tendsto_iterate_S (q : X × A → ℝ) : Tendsto (fun k : ℕ => M.S^[k] q) atTop (𝓝 M.qstar) :=
  M.isContractionOn_S.tendsto_iterate_fixedPt (Set.mem_univ q) (Set.mem_univ _) M.isFixedPt_S_qstar

/-- Corollary 5.3.7 (p. 176), (i) ⟺ (ii): `v*`-greedy iff `g*`-greedy. -/
theorem isGreedy_vstar_iff_isGGreedy_gstar (σ : X → A) :
    M.IsGreedy M.vstar σ ↔ M.IsGGreedy M.gstar σ :=
  Iff.rfl

/-- Corollary 5.3.7 (p. 176), (ii) ⟺ (iii): `g*`-greedy iff `q*`-greedy. -/
theorem isGGreedy_gstar_iff_isQGreedy_qstar (σ : X → A) :
    M.IsGGreedy M.gstar σ ↔ M.IsQGreedy M.qstar σ :=
  Iff.rfl

/-- Corollary 5.3.7 (p. 176): `σ` is optimal iff it is `g*`-greedy. -/
theorem isOptimal_iff_isGGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsGGreedy M.gstar σ :=
  M.isOptimal_iff_isGreedy σ

/-- **Proposition 5.3.4** (p. 172) and Corollary 5.3.7: `σ` is optimal iff it is `q*`-greedy,
`σ(x) ∈ argmax_{a ∈ Γ(x)} q*(x, a)`. -/
theorem isOptimal_iff_isQGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsQGreedy M.qstar σ :=
  M.isOptimal_iff_isGreedy σ

end MDP

end SargentStachurski.MarkovDecisionProcesses
