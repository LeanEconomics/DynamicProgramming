/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Refactoring
import MarkovDecisionProcesses.Applications

/-!
# Expected value functions: structural estimation and stochastic returns

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.3.1 and §5.3.3
(pp. 162–171).

The generic structural model (5.33) has an endogenous state `y`, a preference
shock `ε` drawn IID from `φ`, and a kernel `P₀(y, a, y')` for `y`; the state is
`(y, ε)`. The book allows a continuous shock space; here `E` is finite, the
discretised form in which "all the optimality theory for MDPs applies" (p. 165).
The expected value function (5.34) depends on `(y, a)` only; the expected value
Bellman operator `R` of (5.35) acts on `ℝ^{Y × A}`, is order preserving and a
contraction of modulus `β` (Exercise 5.3.1), and its fixed point `g*`
determines optimality (Proposition 5.3.1): `σ` is optimal iff
`σ(y, ε) ∈ argmax_{a ∈ Γ(y, ε)} {r(y, ε, a) + βg*(y, a)}`. The feasible set may
depend on the shock, as it does in §5.3.3.

Optimal savings with stochastic returns (§5.3.3) and the savings model with
transient and persistent income (Exercise 5.3.3) are instances: their expected
value functions (5.37) depend only on income and next period's wealth, and
their Bellman equations in expected value form are the fixed point equations of
the reduced operator; the modified `σ`-value operator `R_σ` of p. 169 is the
policy operator of §5.3.5.3 in reduced form.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- The generic structural model (5.33): endogenous states `Y`, shocks `E` with distribution `φ`,
actions `A`, feasible sets `Γ(y, ε)`, rewards `r(y, ε, a)`, a stochastic kernel `P₀` for `y`. -/
structure Structural (Y E A : Type*) [Fintype Y] [Fintype E] [Fintype A] where
  Γ : Y → E → Finset A
  Γ_nonempty : ∀ y ε, (Γ y ε).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : Y → E → A → ℝ
  P₀ : Y → A → Y → ℝ
  P₀_nonneg : ∀ y a y', 0 ≤ P₀ y a y'
  P₀_rowsum : ∀ y a, ∑ y', P₀ y a y' = 1
  φ : E → ℝ
  φ_dist : IsDistribution φ

/-- The lift of a function on `Y × A` to one on `(Y × E) × A`, constant in the shock. -/
def liftEV {Y A : Type*} (E : Type*) (g : Y × A → ℝ) : (Y × E) × A → ℝ := fun p => g (p.1.1, p.2)

/-- `‖lift g − lift g'‖ ≤ ‖g − g'‖`. -/
theorem norm_liftEV_sub_le {Y A : Type*} [Fintype Y] [Fintype A] (E : Type*) [Fintype E]
    (g g' : Y × A → ℝ) : ‖liftEV E g - liftEV E g'‖ ≤ ‖g - g'‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  rintro ⟨⟨y, ε⟩, a⟩
  have := norm_le_pi_norm (g - g') (y, a)
  simpa [liftEV] using this

/-- `‖g − g'‖ ≤ ‖lift g − lift g'‖` when the shock space is nonempty. -/
theorem norm_le_norm_liftEV {Y A : Type*} [Fintype Y] [Fintype A] (E : Type*) [Fintype E]
    [Nonempty E] (g g' : Y × A → ℝ) : ‖g - g'‖ ≤ ‖liftEV E g - liftEV E g'‖ := by
  obtain ⟨ε⟩ := ‹Nonempty E›
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  rintro ⟨y, a⟩
  have := norm_le_pi_norm (liftEV E g - liftEV E g') ((y, ε), a)
  simpa [liftEV] using this

namespace Structural

variable {Y E A : Type*} [Fintype Y] [Fintype E] [Fintype A] (S : Structural Y E A)

/-- The MDP on the state space `Y × E` (p. 165): `P((y, ε), a, (y', ε')) = P₀(y, a, y')φ(ε')`. -/
noncomputable def toMDP : MDP (Y × E) A where
  Γ := fun x => S.Γ x.1 x.2
  Γ_nonempty := fun x => S.Γ_nonempty x.1 x.2
  β := S.β
  β_pos := S.β_pos
  β_lt_one := S.β_lt_one
  r := fun x a => S.r x.1 x.2 a
  P := fun x a x' => S.P₀ x.1 a x'.1 * S.φ x'.2
  P_nonneg := fun x a x' => mul_nonneg (S.P₀_nonneg _ _ _) (S.φ_dist.nonneg _)
  P_rowsum := fun x a => by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, S.φ_dist.sum_eq_one, mul_one]
    exact S.P₀_rowsum x.1 a

/-- The expectation of `v` under `P((y, ε), a, ·)` is the expected value function (5.34):
`∑_{y', ε'} v(y', ε')P₀(y, a, y')φ(ε')`, independent of `ε`. -/
theorem E_toMDP (v : Y × E → ℝ) (y : Y) (ε : E) (a : A) :
    S.toMDP.E v ((y, ε), a) = ∑ y', (∑ ε', v (y', ε') * S.φ ε') * S.P₀ y a y' := by
  simp only [MDP.E, toMDP]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun ε' _ => by ring

/-- The expected value function on `Y × A`, (5.34):
`g(y, a) = ∑_{y', ε'} v(y', ε')P₀(y, a, y')φ(ε')`. -/
def Ered (v : Y × E → ℝ) : Y × A → ℝ := fun p =>
  ∑ y', (∑ ε', v (y', ε') * S.φ ε') * S.P₀ p.1 p.2 y'

theorem E_toMDP_eq_lift (v : Y × E → ℝ) : S.toMDP.E v = liftEV E (S.Ered v) := by
  funext ⟨⟨y, ε⟩, a⟩
  exact S.E_toMDP v y ε a

/-- The expected value Bellman operator (5.35) on `ℝ^{Y × A}`:
`(Rg)(y, a) = ∑_{y'} ∑_{ε'} max_{a' ∈ Γ(y', ε')} {r(y', ε', a') + βg(y', a')} φ(ε')P₀(y, a, y')`. -/
noncomputable def Rred (g : Y × A → ℝ) : Y × A → ℝ := fun p =>
  ∑ y', (∑ ε', ((S.Γ y' ε').sup' (S.Γ_nonempty y' ε') fun a' => S.r y' ε' a' + S.β * g (y', a')) *
    S.φ ε') * S.P₀ p.1 p.2 y'

/-- The MDP's operator `R = EMD` acts on lifted functions as the reduced operator. -/
theorem R_lift (g : Y × A → ℝ) : S.toMDP.R (liftEV E g) = liftEV E (S.Rred g) := by
  funext ⟨⟨y, ε⟩, a⟩
  simp only [MDP.R]
  rw [S.E_toMDP]
  rfl

/-- Exercise 5.3.1 (p. 166): `R` is order preserving. -/
theorem Rred_monotone : Monotone S.Rred := by
  intro g g' hgg' p
  unfold Rred
  refine sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right (sum_le_sum fun ε' _ =>
    mul_le_mul_of_nonneg_right (Finset.sup'_mono_fun fun a' _ => ?_) (S.φ_dist.nonneg ε'))
    (S.P₀_nonneg _ _ _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgg' (y', a')) S.β_pos.le)

/-- Exercise 5.3.1 (p. 166): `R` is a contraction of modulus `β` on `ℝ^{Y × A}` under the supremum
norm, through the lift to the MDP's operator (Lemma 5.3.5). -/
theorem isContractionOn_Rred [Nonempty E] : IsContractionOn S.Rred Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le g _ g' _ := by
    calc ‖S.Rred g - S.Rred g'‖ ≤ ‖liftEV E (S.Rred g) - liftEV E (S.Rred g')‖ :=
          norm_le_norm_liftEV E _ _
      _ = ‖S.toMDP.R (liftEV E g) - S.toMDP.R (liftEV E g')‖ := by rw [R_lift, R_lift]
      _ ≤ S.β * ‖liftEV E g - liftEV E g'‖ :=
          S.toMDP.isContractionOn_R.norm_sub_le _ (Set.mem_univ _) _ (Set.mem_univ _)
      _ ≤ S.β * ‖g - g'‖ := mul_le_mul_of_nonneg_left (norm_liftEV_sub_le E g g') S.β_pos.le

variable [DecidableEq Y] [DecidableEq E] [DecidableEq A]

/-- The reduced optimal expected value function `g* = Ered v*`, (5.34) at `v = v*`. -/
noncomputable def gred : Y × A → ℝ := S.Ered S.toMDP.vstar

/-- The MDP's `g*` is the lift of the reduced `g*`. -/
theorem gstar_eq_lift : S.toMDP.gstar = liftEV E S.gred := S.E_toMDP_eq_lift _

/-- `g*` solves the expected value Bellman equation (p. 165): it is a fixed point of `R`. -/
theorem isFixedPt_Rred_gred [Nonempty E] : IsFixedPt S.Rred S.gred := by
  have h := S.toMDP.isFixedPt_R_gstar
  rw [IsFixedPt, gstar_eq_lift, R_lift] at h
  funext p
  obtain ⟨ε⟩ := ‹Nonempty E›
  exact congrFun h ((p.1, ε), p.2)

/-- `g*` is the unique fixed point of `R` in `ℝ^{Y × A}`, computable by successive approximation
(p. 166). -/
theorem eq_gred_of_isFixedPt [Nonempty E] {g : Y × A → ℝ} (hg : IsFixedPt S.Rred g) :
    g = S.gred :=
  S.isContractionOn_Rred.fixedPt_unique (Set.mem_univ g) (Set.mem_univ _) hg S.isFixedPt_Rred_gred

theorem tendsto_iterate_Rred [Nonempty E] (g : Y × A → ℝ) :
    Tendsto (fun k : ℕ => S.Rred^[k] g) atTop (𝓝 S.gred) :=
  S.isContractionOn_Rred.tendsto_iterate_fixedPt (Set.mem_univ g) (Set.mem_univ _)
    S.isFixedPt_Rred_gred

/-- The Bellman equation in expected value form (p. 165):
`v*(y, ε) = max_{a ∈ Γ(y, ε)} {r(y, ε, a) + βg*(y, a)}`. -/
theorem vstar_eq (y : Y) (ε : E) :
    S.toMDP.vstar (y, ε) =
      (S.Γ y ε).sup' (S.Γ_nonempty y ε) fun a => S.r y ε a + S.β * S.gred (y, a) := by
  rw [S.toMDP.vstar_apply_eq_sup'_qstar]
  refine Finset.sup'_congr _ rfl fun a _ => ?_
  rw [MDP.qstar_apply, gstar_eq_lift]
  rfl

/-- **Proposition 5.3.1** (p. 166): a feasible policy is optimal iff
`σ(y, ε) ∈ argmax_{a ∈ Γ(y, ε)} {r(y, ε, a) + βg*(y, a)}` for all `(y, ε)`. -/
theorem isOptimal_iff (σ : Y × E → A) :
    S.toMDP.IsOptimal σ ↔
      S.toMDP.IsFeasible σ ∧ ∀ y ε, ∀ a ∈ S.Γ y ε,
        S.r y ε a + S.β * S.gred (y, a) ≤ S.r y ε (σ (y, ε)) + S.β * S.gred (y, σ (y, ε)) := by
  rw [S.toMDP.isOptimal_iff_isGGreedy, MDP.IsGGreedy, gstar_eq_lift]
  constructor
  · rintro ⟨hσ, h⟩
    exact ⟨hσ, fun y ε a ha => h (y, ε) a ha⟩
  · rintro ⟨hσ, h⟩
    exact ⟨hσ, fun x a ha => h x.1 x.2 a ha⟩

omit [DecidableEq Y] [DecidableEq E] [DecidableEq A] in
/-- The modified `σ`-value operator `R_σ = E M_σ D` of p. 169, in reduced form:
`(R_σ g)(y, a) = ∑_{y', ε'} [r(y', ε', σ(y', ε')) + βg(y', σ(y', ε'))] φ(ε') P₀(y, a, y')`. -/
theorem Rσ_lift (σ : Y × E → A) (g : Y × A → ℝ) (y : Y) (ε : E) (a : A) :
    S.toMDP.Rσ σ (liftEV E g) ((y, ε), a) =
      ∑ y', (∑ ε', (S.r y' ε' (σ (y', ε')) + S.β * g (y', σ (y', ε'))) * S.φ ε') * S.P₀ y a y' := by
  simp only [MDP.Rσ]
  rw [S.E_toMDP]
  rfl

end Structural

/-! ### Optimal savings with stochastic returns (§5.3.3) -/

variable {W Yi Et : Type*} [Fintype W] [Fintype Yi] [Fintype Et] [DecidableEq W]

/-- Optimal savings with IID gross returns `η ∼ φ` (§5.3.3): endogenous state `(w, y)` with wealth
values `wealth` and income values `inc`, shock `η` with return `ret η`, actions `w'` with
`w' ≤ η(w + y)`, reward `u(w + y − w'/η)`, income `Q`-Markov. -/
noncomputable def stochasticReturns (wealth : W → ℝ) (inc : Yi → ℝ) (ret : Et → ℝ)
    {Q : Matrix Yi Yi ℝ} (hQ : IsMarkov Q) {φ : Et → ℝ} (hφ : IsDistribution φ) (u : ℝ → ℝ)
    (hΓ : ∀ w y η, ∃ s, wealth s ≤ ret η * (wealth w + inc y)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Structural (W × Yi) Et W where
  Γ := fun x η => univ.filter fun s => wealth s ≤ ret η * (wealth x.1 + inc x.2)
  Γ_nonempty := fun x η => by
    obtain ⟨s, hs⟩ := hΓ x.1 x.2 η
    exact ⟨s, by simp [hs]⟩
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x η s => u (wealth x.1 + inc x.2 - wealth s / ret η)
  P₀ := choiceKernel Q
  P₀_nonneg := choiceKernel_nonneg hQ
  P₀_rowsum := choiceKernel_rowsum hQ
  φ := φ
  φ_dist := hφ

namespace stochasticReturns

variable (wealth : W → ℝ) (inc : Yi → ℝ) (ret : Et → ℝ) {Q : Matrix Yi Yi ℝ} (hQ : IsMarkov Q)
  {φ : Et → ℝ} (hφ : IsDistribution φ) (u : ℝ → ℝ)
  (hΓ : ∀ w y η, ∃ s, wealth s ≤ ret η * (wealth w + inc y)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

/-- (5.37): the expected value function `g(y, w') = ∑_{y', η'} v(w', y', η')Q(y, y')φ(η')`
depends on the current state only through income `y`, not current wealth `w`. -/
theorem Ered_apply (v : (W × Yi) × Et → ℝ) (w : W) (y : Yi) (w' : W) :
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).Ered v ((w, y), w') =
      ∑ y', (∑ η', v ((w', y'), η') * φ η') * Q y y' := by
  exact sum_mul_choiceKernel Q _ (w, y) w'

/-- The Bellman equation with stochastic returns (p. 168):
`v*(w, y, η) = max_{w' ≤ η(w + y)} {u(w + y − w'/η) + βg*(y, w')}`, with `g*` the expected value
function (5.37) of `v*`. -/
theorem bellman_equation [DecidableEq Yi] [DecidableEq Et] (w : W) (y : Yi) (η : Et) :
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).toMDP.vstar ((w, y), η) =
      (univ.filter fun s => wealth s ≤ ret η * (wealth w + inc y)).sup'
        ((stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).Γ_nonempty (w, y) η)
        fun w' => u (wealth w + inc y - wealth w' / ret η) +
          β * (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).gred ((w, y), w') :=
  Structural.vstar_eq _ (w, y) η

/-- The Bellman equation in expected value form (p. 169): `g*` satisfies
`g*(y, w') = ∑_{y', η'} max_{w'' ≤ η'(w' + y')} {u(w' + y' − w''/η') + βg*(y', w'')} Q(y, y')φ(η')`.
-/
theorem gred_eq [DecidableEq Yi] [DecidableEq Et] [Nonempty Et] (w : W) (y : Yi) (w' : W) :
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).gred ((w, y), w') =
      ∑ y', (∑ η', ((univ.filter fun s => wealth s ≤ ret η' * (wealth w' + inc y')).sup'
        ((stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).Γ_nonempty (w', y') η')
        fun w'' => u (wealth w' + inc y' - wealth w'' / ret η') +
          β * (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1).gred ((w', y'), w'')) * φ η') *
        Q y y' := by
  have h := congrFun (Structural.isFixedPt_Rred_gred
    (stochasticReturns wealth inc ret hQ hφ u hΓ hβ0 hβ1)).eq ((w, y), w')
  rw [← h]
  exact sum_mul_choiceKernel Q _ (w, y) w'

end stochasticReturns

/-! ### Exercise 5.3.3: transient and persistent income -/

variable {Zp : Type*} [Fintype Zp]

/-- Exercise 5.3.3 (p. 169): optimal savings with labour income `Y = Z + ε`, `Z` `Q`-Markov and `ε`
IID with distribution `φ`, constant gross return `R`; endogenous state `(w, z)`, shock `ε`, actions
`w' ≤ R(w + z + ε)`, reward `u(w + z + ε − w'/R)`. -/
noncomputable def transientIncome (wealth : W → ℝ) (zval : Zp → ℝ) (eps : Et → ℝ)
    {Q : Matrix Zp Zp ℝ} (hQ : IsMarkov Q) {φ : Et → ℝ} (hφ : IsDistribution φ) (R : ℝ) (u : ℝ → ℝ)
    (hΓ : ∀ w z ε, ∃ s, wealth s ≤ R * (wealth w + zval z + eps ε)) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) : Structural (W × Zp) Et W where
  Γ := fun x ε => univ.filter fun s => wealth s ≤ R * (wealth x.1 + zval x.2 + eps ε)
  Γ_nonempty := fun x ε => by
    obtain ⟨s, hs⟩ := hΓ x.1 x.2 ε
    exact ⟨s, by simp [hs]⟩
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x ε s => u (wealth x.1 + zval x.2 + eps ε - wealth s / R)
  P₀ := choiceKernel Q
  P₀_nonneg := choiceKernel_nonneg hQ
  P₀_rowsum := choiceKernel_rowsum hQ
  φ := φ
  φ_dist := hφ

namespace transientIncome

variable (wealth : W → ℝ) (zval : Zp → ℝ) (eps : Et → ℝ) {Q : Matrix Zp Zp ℝ} (hQ : IsMarkov Q)
  {φ : Et → ℝ} (hφ : IsDistribution φ) (R : ℝ) (u : ℝ → ℝ)
  (hΓ : ∀ w z ε, ∃ s, wealth s ≤ R * (wealth w + zval z + eps ε)) {β : ℝ} (hβ0 : 0 < β)
  (hβ1 : β < 1)

/-- Exercise 5.3.3, the Bellman equation: `v*(w, z, ε)` equals
`max_{w' ≤ R(w + z + ε)} {u(w + z + ε − w'/R) + β ∑_{z', ε'} v*(w', z', ε')Q(z, z')φ(ε')}`. -/
theorem bellman_equation [DecidableEq Zp] [DecidableEq Et] (w : W) (z : Zp) (ε : Et) :
    (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).toMDP.vstar ((w, z), ε) =
      (univ.filter fun s => wealth s ≤ R * (wealth w + zval z + eps ε)).sup'
        ((transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).Γ_nonempty (w, z) ε)
        fun w' => u (wealth w + zval z + eps ε - wealth w' / R) +
          β * ∑ z', (∑ ε', (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).toMDP.vstar
            ((w', z'), ε') * φ ε') * Q z z' := by
  rw [Structural.vstar_eq]
  refine Finset.sup'_congr _ rfl fun w' _ => ?_
  congr 2
  exact sum_mul_choiceKernel Q _ (w, z) w'

/-- Exercise 5.3.3, the Bellman equation in expected value form: with
`g*(z, w') = ∑_{z', ε'} v*(w', z', ε')Q(z, z')φ(ε')`, `g*(z, w')` equals
`∑_{z', ε'} max_{w'' ≤ R(w' + z' + ε')} {u(w' + z' + ε' − w''/R) + βg*(z', w'')} Q(z, z')φ(ε')`. -/
theorem gred_eq [DecidableEq Zp] [DecidableEq Et] [Nonempty Et] (w : W) (z : Zp) (w' : W) :
    (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).gred ((w, z), w') =
      ∑ z', (∑ ε', ((univ.filter fun s => wealth s ≤ R * (wealth w' + zval z' + eps ε')).sup'
        ((transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).Γ_nonempty (w', z') ε')
        fun w'' => u (wealth w' + zval z' + eps ε' - wealth w'' / R) +
          β * (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1).gred ((w', z'), w'')) * φ ε') *
        Q z z' := by
  have h := congrFun (Structural.isFixedPt_Rred_gred
    (transientIncome wealth zval eps hQ hφ R u hΓ hβ0 hβ1)).eq ((w, z), w')
  rw [← h]
  exact sum_mul_choiceKernel Q _ (w, z) w'

end transientIncome

end SargentStachurski.MarkovDecisionProcesses
