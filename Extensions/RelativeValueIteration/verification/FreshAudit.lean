import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.SingularValues
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The span seminorm and the Dobrushin coefficient

Seneta (1981); Puterman (2005).

The span `sp(v) = max v − min v` of a function on a finite set ignores constant shifts. The
Dobrushin bound (`dobrushin`) says that for probability vectors `p`, `q`,
`∑ p d − ∑ q d ≤ (1 − ∑_y min(p_y, q_y)) · sp(d)`: the more two distributions overlap, the less
they can disagree about a function's expectation. These are the tools behind the convergence of
relative value iteration.
-/

open Finset

namespace DPExtensions.RelativeValueIteration

variable {S : Type*} [Fintype S] [Nonempty S]

/-- The span seminorm `sp(v) = max v − min v`. -/
noncomputable def sp (v : S → ℝ) : ℝ := univ.sup' univ_nonempty v - univ.inf' univ_nonempty v

theorem sub_le_sp (v : S → ℝ) (x y : S) : v x - v y ≤ sp v := by
  have h1 := le_sup' v (mem_univ x)
  have h2 := inf'_le v (mem_univ y)
  simp only [sp]
  linarith

theorem abs_sub_le_sp (v : S → ℝ) (x y : S) : |v x - v y| ≤ sp v :=
  abs_le.2 ⟨by linarith [sub_le_sp v y x], sub_le_sp v x y⟩

theorem sp_nonneg (v : S → ℝ) : 0 ≤ sp v := by
  have := sub_le_sp v (Classical.arbitrary S) (Classical.arbitrary S)
  linarith

theorem sp_le {v : S → ℝ} {c : ℝ} (h : ∀ x y, v x - v y ≤ c) : sp v ≤ c := by
  have h1 : ∀ x, v x - c ≤ univ.inf' univ_nonempty v := fun x =>
    le_inf' _ _ fun y _ => by linarith [h x y]
  have h2 : univ.sup' univ_nonempty v ≤ univ.inf' univ_nonempty v + c :=
    sup'_le _ _ fun x _ => by linarith [h1 x]
  simp only [sp]
  linarith

theorem sp_add_const (v : S → ℝ) (c : ℝ) : sp (fun x => v x + c) = sp v :=
  le_antisymm (sp_le fun x y => by linarith [sub_le_sp v x y])
    (sp_le fun x y => by linarith [sub_le_sp (fun x => v x + c) x y])

theorem sp_neg (v : S → ℝ) : sp (fun x => -v x) = sp v :=
  le_antisymm (sp_le fun x y => by linarith [sub_le_sp v y x])
    (sp_le fun x y => by linarith [sub_le_sp (fun x => -v x) y x])

theorem le_sup'_sp (v : S → ℝ) (x : S) : v x ≤ univ.sup' univ_nonempty v :=
  le_sup' v (mem_univ x)

theorem inf'_le_sp (v : S → ℝ) (x : S) : univ.inf' univ_nonempty v ≤ v x :=
  inf'_le v (mem_univ x)

omit [Nonempty S] in
/-- **The Dobrushin bound**: for `p`, `q` summing to one (probability vectors) and any `d`,
`∑ p d − ∑ q d ≤ (1 − ∑ min(p, q)) · sp(d)`. -/
theorem dobrushin {Y : Type*} [Fintype Y] [Nonempty Y] {p q : Y → ℝ} (hp1 : ∑ y, p y = 1)
    (hq1 : ∑ y, q y = 1) (d : Y → ℝ) :
    ∑ y, p y * d y - ∑ y, q y * d y ≤ (1 - ∑ y, min (p y) (q y)) * sp d := by
  set hi := univ.sup' univ_nonempty d
  set lo := univ.inf' univ_nonempty d
  set m : Y → ℝ := fun y => min (p y) (q y)
  have hpm : ∀ y, 0 ≤ p y - m y := fun y => sub_nonneg.2 (min_le_left _ _)
  have hqm : ∀ y, 0 ≤ q y - m y := fun y => sub_nonneg.2 (min_le_right _ _)
  have h1 : ∑ y, (p y - m y) * d y ≤ ∑ y, (p y - m y) * hi :=
    sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (le_sup'_sp d y) (hpm y)
  have h2 : ∑ y, (q y - m y) * lo ≤ ∑ y, (q y - m y) * d y :=
    sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (inf'_le_sp d y) (hqm y)
  have e1 : ∑ y, (p y - m y) * hi = (1 - ∑ y, m y) * hi := by
    rw [← sum_mul, sum_sub_distrib, hp1]
  have e2 : ∑ y, (q y - m y) * lo = (1 - ∑ y, m y) * lo := by
    rw [← sum_mul, sum_sub_distrib, hq1]
  have e3 : ∑ y, p y * d y - ∑ y, q y * d y =
      ∑ y, (p y - m y) * d y - ∑ y, (q y - m y) * d y := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun y _ => by ring
  rw [e3]
  simp only [sp]
  nlinarith

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite MDPs, constant shifts and the span contraction

White (1963); Morton and Wecker (1977); Bray (2019, *Quantitative Economics*).

A finite MDP with feasible actions `Γ(s)`, reward `r`, transitions `P` and discount
`β ∈ [0, 1]` (`β = 1` is the average-reward case). With `Tv(s) = max_{a ∈ Γ(s)} Q_v(s, a)`:

* `T_add_const`, `T_iterate_add_const`: `T(v + c) = Tv + βc`.
* `isGreedy_add_const_iff` (**White**): greedy policies ignore constant shifts of `v`.
* `rel`, `relT_iterate` (**relative value iteration**): with `rel(v) = v − v(s₀)`, iterating
  `v ↦ rel(Tv)` gives `rel(Tⁿv)` (Bray's Lemma 4): relative value iteration tracks value
  iteration up to a constant, at no cost.
* `sp_T_sub_le` (**the span contraction**): if `α` bounds the Dobrushin coefficient
  `1 − ∑_t min(P(s, a, t), P(s', a', t))` over all feasible state–action pairs, then
  `sp(Tv − Tw) ≤ βα·sp(v − w)`.
* For `β < 1`: `T` and the policy operators are sup-norm contractions with fixed points `v*`
  and `v_σ`, ordered by monotonicity (`vstar_le_of_T_le`, `le_vσ_of_le`, `vσ_le_vstar`).
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

variable (S A : Type*) [Fintype S] in
/-- A finite Markov decision process with discount factor `β ∈ [0, 1]`. -/
structure MDP where
  /-- feasible actions -/
  Γ : S → Finset A
  Γ_nonempty : ∀ s, (Γ s).Nonempty
  /-- rewards -/
  r : S → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_le_one : β ≤ 1
  /-- transition probabilities -/
  P : S → A → S → ℝ
  P_nonneg : ∀ s a t, 0 ≤ P s a t
  P_sum : ∀ s a, ∑ t, P s a t = 1

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

/-- The action value `Q_v(s, a) = r(s, a) + β∑_t P(s, a, t)v(t)`. -/
def Q (v : S → ℝ) (s : S) (a : A) : ℝ := M.r s a + M.β * ∑ t, M.P s a t * v t

/-- The Bellman operator. -/
noncomputable def T (v : S → ℝ) (s : S) : ℝ := (M.Γ s).sup' (M.Γ_nonempty s) (M.Q v s)

/-- The policy operator of a decision rule `σ`. -/
def Tσ (σ : S → A) (v : S → ℝ) (s : S) : ℝ := M.Q v s (σ s)

/-- `σ` is greedy for `v`. -/
def IsGreedy (σ : S → A) (v : S → ℝ) : Prop :=
  ∀ s, σ s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, M.Q v s a ≤ M.Q v s (σ s)

/-- `σ` is feasible. -/
def IsPolicy (σ : S → A) : Prop := ∀ s, σ s ∈ M.Γ s

theorem exists_greedyAct (v : S → ℝ) (s : S) :
    ∃ a ∈ M.Γ s, M.T v s = M.Q v s a ∧ ∀ b ∈ M.Γ s, M.Q v s b ≤ M.Q v s a := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image (M.Γ s) (M.Q v s) (M.Γ_nonempty s)
  exact ⟨a, ha, le_antisymm (sup'_le _ _ hmax) (le_sup' (M.Q v s) ha), hmax⟩

theorem exists_greedy (v : S → ℝ) : ∃ σ, M.IsGreedy σ v := by
  choose σ hσ using M.exists_greedyAct v
  exact ⟨σ, fun s => ⟨(hσ s).1, (hσ s).2.2⟩⟩

theorem Q_le_T (v : S → ℝ) {s : S} {a : A} (ha : a ∈ M.Γ s) : M.Q v s a ≤ M.T v s :=
  le_sup' (M.Q v s) ha

theorem Tσ_eq_T_of_greedy {σ : S → A} {v : S → ℝ} (h : M.IsGreedy σ v) : M.Tσ σ v = M.T v :=
  funext fun s => le_antisymm (M.Q_le_T v (h s).1) (sup'_le _ _ (h s).2)

theorem Tσ_le_T {σ : S → A} (hσ : M.IsPolicy σ) (v : S → ℝ) : M.Tσ σ v ≤ M.T v := fun s =>
  M.Q_le_T v (hσ s)

theorem Q_add_const (v : S → ℝ) (c : ℝ) (s : S) (a : A) :
    M.Q (fun t => v t + c) s a = M.Q v s a + M.β * c := by
  simp only [Q, mul_add, sum_add_distrib, ← sum_mul, M.P_sum, one_mul]
  ring

theorem T_add_const (v : S → ℝ) (c : ℝ) : M.T (fun t => v t + c) = fun s => M.T v s + M.β * c := by
  funext s
  simp only [T, Q_add_const]
  exact (sup'_add _ _ _ _).symm

theorem Tσ_add_const (σ : S → A) (v : S → ℝ) (c : ℝ) :
    M.Tσ σ (fun t => v t + c) = fun s => M.Tσ σ v s + M.β * c :=
  funext fun s => M.Q_add_const v c s (σ s)

/-- **White (1963)**: greedy policies are invariant to constant shifts of the value function. -/
theorem isGreedy_add_const_iff (σ : S → A) (v : S → ℝ) (c : ℝ) :
    M.IsGreedy σ (fun t => v t + c) ↔ M.IsGreedy σ v := by
  simp only [IsGreedy, Q_add_const, add_le_add_iff_right]

theorem T_iterate_add_const (v : S → ℝ) (c : ℝ) (n : ℕ) :
    M.T^[n] (fun t => v t + c) = fun s => M.T^[n] v s + M.β ^ n * c := by
  induction n generalizing v c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_add_const, ih, pow_succ']
    funext s
    ring

/-- The relative value function, normalized to `0` at the reference state `s₀`. -/
def rel (s₀ : S) (v : S → ℝ) (s : S) : ℝ := v s - v s₀

omit [Fintype S] in
theorem rel_add_const (s₀ : S) (v : S → ℝ) (c : ℝ) : rel s₀ (fun t => v t + c) = rel s₀ v := by
  funext s
  simp only [rel]
  ring

/-- **Relative value iteration is value iteration up to a constant** (Bray, 2019, Lemma 4):
iterating `v ↦ rel(Tv)` from `rel(v)` gives `rel(Tⁿv)`. -/
theorem relT_iterate (s₀ : S) (v : S → ℝ) (n : ℕ) :
    (fun w => rel s₀ (M.T w))^[n] (rel s₀ v) = rel s₀ (M.T^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    have e : rel s₀ (M.T^[n] v) = fun t => M.T^[n] v t + -M.T^[n] v s₀ := by
      funext t
      simp only [rel]
      ring
    rw [e, T_add_const, rel_add_const]

theorem Q_sub_Q (v w : S → ℝ) (s : S) (a : A) :
    M.Q v s a - M.Q w s a = M.β * ∑ t, M.P s a t * (v t - w t) := by
  simp only [Q, mul_sub, sum_sub_distrib]
  ring

variable [Nonempty S]

/-- **The span contraction**: if `α` bounds `1 − ∑_t min(P(s, a, t), P(s', a', t))` over all
feasible pairs, then `sp(Tv − Tw) ≤ βα·sp(v − w)`. -/
theorem sp_T_sub_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (v w : S → ℝ) :
    sp (fun s => M.T v s - M.T w s) ≤ M.β * α * sp (fun s => v s - w s) := by
  refine sp_le fun s s' => ?_
  obtain ⟨a, ha, hva, -⟩ := M.exists_greedyAct v s
  obtain ⟨a', ha', hwa', -⟩ := M.exists_greedyAct w s'
  have h1 : M.Q w s a ≤ M.T w s := M.Q_le_T w ha
  have h2 : M.Q v s' a' ≤ M.T v s' := M.Q_le_T v ha'
  have hd := dobrushin (M.P_sum s a) (M.P_sum s' a') (fun t => v t - w t)
  have hsp := sp_nonneg (fun t => v t - w t)
  have hc : (1 - ∑ t, min (M.P s a t) (M.P s' a' t)) * sp (fun t => v t - w t) ≤
      α * sp (fun t => v t - w t) := mul_le_mul_of_nonneg_right (hα s a s' a' ha ha') hsp
  have e1 := M.Q_sub_Q v w s a
  have e2 := M.Q_sub_Q v w s' a'
  have h3 := mul_le_mul_of_nonneg_left (hd.trans hc) M.β_nonneg
  nlinarith

end MDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The discounted problem

For `β < 1` the Bellman operator `T` and the policy operators `T_σ` are `β`-contractions for the
supremum norm, with fixed points `v*` (`vstar`) and `v_σ` (`vσ`), and monotonicity orders them.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

theorem abs_Q_sub_le (v w : S → ℝ) (s : S) (a : A) :
    |M.Q v s a - M.Q w s a| ≤ M.β * ‖v - w‖ := by
  rw [M.Q_sub_Q, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans ?_) M.β_nonneg
  calc ∑ t, |M.P s a t * (v t - w t)| ≤ ∑ t, M.P s a t * ‖v - w‖ := sum_le_sum fun t _ => by
        rw [abs_mul, abs_of_nonneg (M.P_nonneg s a t)]
        refine mul_le_mul_of_nonneg_left ?_ (M.P_nonneg s a t)
        have := norm_le_pi_norm (v - w) t
        rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    _ = ‖v - w‖ := by rw [← sum_mul, M.P_sum, one_mul]

theorem norm_T_sub_le (v w : S → ℝ) : ‖M.T v - M.T w‖ ≤ M.β * ‖v - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun s => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  obtain ⟨a, ha, hva, -⟩ := M.exists_greedyAct v s
  obtain ⟨b, hb, hwb, -⟩ := M.exists_greedyAct w s
  have h1 := abs_le.1 (M.abs_Q_sub_le v w s a)
  have h2 := abs_le.1 (M.abs_Q_sub_le v w s b)
  have h3 := M.Q_le_T w ha
  have h4 := M.Q_le_T v hb
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem norm_Tσ_sub_le (σ : S → A) (v w : S → ℝ) : ‖M.Tσ σ v - M.Tσ σ w‖ ≤ M.β * ‖v - w‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun s => by
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact M.abs_Q_sub_le v w s (σ s)

theorem T_mono : Monotone M.T := fun _ w h s =>
  sup'_le _ _ fun a ha => le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (M.P_nonneg s a t)) M.β_nonneg))
    (M.Q_le_T w ha)

theorem Tσ_mono (σ : S → A) : Monotone (M.Tσ σ) := fun _ _ h s =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (M.P_nonneg s (σ s) t)) M.β_nonneg)

theorem contracting_T (hβ : M.β < 1) : ContractingWith ⟨M.β, M.β_nonneg⟩ M.T :=
  ⟨hβ, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_T_sub_le v w⟩

theorem contracting_Tσ (hβ : M.β < 1) (σ : S → A) :
    ContractingWith ⟨M.β, M.β_nonneg⟩ (M.Tσ σ) :=
  ⟨hβ, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_Tσ_sub_le σ v w⟩

/-- The value function. -/
noncomputable def vstar (hβ : M.β < 1) : S → ℝ :=
  ContractingWith.fixedPoint M.T (M.contracting_T hβ)

/-- The value of a decision rule. -/
noncomputable def vσ (hβ : M.β < 1) (σ : S → A) : S → ℝ :=
  ContractingWith.fixedPoint (M.Tσ σ) (M.contracting_Tσ hβ σ)

theorem T_vstar (hβ : M.β < 1) : M.T (M.vstar hβ) = M.vstar hβ :=
  ContractingWith.fixedPoint_isFixedPt _

theorem Tσ_vσ (hβ : M.β < 1) (σ : S → A) : M.Tσ σ (M.vσ hβ σ) = M.vσ hβ σ :=
  ContractingWith.fixedPoint_isFixedPt _

/-- `w ≤ T_σw` implies `w ≤ v_σ`. -/
theorem le_vσ_of_le (hβ : M.β < 1) (σ : S → A) {w : S → ℝ} (h : w ≤ M.Tσ σ w) :
    w ≤ M.vσ hβ σ := by
  have hit : ∀ n, w ≤ (M.Tσ σ)^[n] w := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact h.trans (M.Tσ_mono σ ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_Tσ hβ σ) w) hit

/-- `w ≤ Tw` implies `w ≤ v*`. -/
theorem le_vstar_of_le (hβ : M.β < 1) {w : S → ℝ} (h : w ≤ M.T w) : w ≤ M.vstar hβ := by
  have hit : ∀ n, w ≤ M.T^[n] w := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact h.trans (M.T_mono ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_T hβ) w) hit

/-- `Tu ≤ u` implies `v* ≤ u`. -/
theorem vstar_le_of_T_le (hβ : M.β < 1) {u : S → ℝ} (h : M.T u ≤ u) : M.vstar hβ ≤ u := by
  have hit : ∀ n, M.T^[n] u ≤ u := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (M.T_mono ih).trans h
  exact le_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_T hβ) u) hit

theorem vσ_le_vstar (hβ : M.β < 1) {σ : S → A} (hσ : M.IsPolicy σ) :
    M.vσ hβ σ ≤ M.vstar hβ :=
  M.le_vstar_of_le hβ (by
    have := M.Tσ_le_T hσ (M.vσ hβ σ)
    rwa [M.Tσ_vσ] at this)

end MDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Relative value iteration

Morton and Wecker (1977); MacQueen (1966); Porteus (1971); Bray (2019, *Quantitative
Economics*), Propositions 1–3.

Relative value iteration sets `V_{n+1} = rel(TV_n)`, normalizing the value at a reference state
to zero; by `relT_iterate`, `V_n = rel(TⁿV₀)`.

* `sp_iterate_sub_vstar`, `rel_converges` (**strong convergence**, non-asymptotic): with `α`
  bounding the Dobrushin coefficient, `sp(TⁿV − v*) ≤ (βα)ⁿ sp(V − v*)` and the relative values
  converge to `rel(v*)` at rate `βα`, while the levels converge only at rate `β`. When `β` is
  close to `1` and the chain mixes (`α < 1`), relative value iteration needs far fewer steps.
* `policy_error` (**MacQueen–Porteus**): a policy greedy for any `v` is within
  `β/(1 − β)·sp(Tv − v)` of optimal — a bound that ignores constant shifts.
* `stopping_rule`, `stopping_rule_sup` (**Bray's stopping rule**): the policy greedy for `V_n`
  is `ε`-optimal once `sp(V_{n+1} − V_n) ≤ ε(1 − β)/β`, in particular once
  `|V_{n+1} − V_n| ≤ ε(1 − β)/(2β)` everywhere.
* `sp_relIter_succ_sub_le`, `stopping_eventually`: the stopping criterion is met after finitely
  many steps, geometrically fast at rate `βα`.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] [Nonempty S] (M : MDP S A)

omit [Nonempty S] in
/-- The Dobrushin coefficient is at most `1`, so `α = 1` is always a valid bound. -/
theorem dobrushin_le_one (s : S) (a : A) (s' : S) (a' : A) :
    1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ 1 := by
  have : 0 ≤ ∑ t, min (M.P s a t) (M.P s' a' t) :=
    sum_nonneg fun t _ => le_min (M.P_nonneg s a t) (M.P_nonneg s' a' t)
  linarith

theorem alpha_nonneg {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α) :
    0 ≤ α := by
  obtain ⟨a, ha⟩ := M.Γ_nonempty (Classical.arbitrary S)
  set s := Classical.arbitrary S
  have h := hα s a s a ha ha
  have e : ∑ t, min (M.P s a t) (M.P s a t) = 1 := by simp [M.P_sum]
  linarith

theorem sp_T_iterate_sub_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (v w : S → ℝ) (n : ℕ) :
    sp (fun s => M.T^[n] v s - M.T^[n] w s) ≤ (M.β * α) ^ n * sp (fun s => v s - w s) := by
  have hc : 0 ≤ M.β * α := mul_nonneg M.β_nonneg (M.alpha_nonneg hα)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    calc sp (fun s => M.T (M.T^[n] v) s - M.T (M.T^[n] w) s)
        ≤ M.β * α * sp (fun s => M.T^[n] v s - M.T^[n] w s) := M.sp_T_sub_le hα _ _
      _ ≤ M.β * α * ((M.β * α) ^ n * sp (fun s => v s - w s)) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (M.β * α) ^ n * (M.β * α) * sp (fun s => v s - w s) := by ring

/-- **Strong convergence**: `sp(TⁿV − v*) ≤ (βα)ⁿ sp(V − v*)`. -/
theorem sp_iterate_sub_vstar (hβ : M.β < 1) {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (v : S → ℝ) (n : ℕ) :
    sp (fun s => M.T^[n] v s - M.vstar hβ s) ≤
      (M.β * α) ^ n * sp (fun s => v s - M.vstar hβ s) := by
  have h := M.sp_T_iterate_sub_le hα v (M.vstar hβ) n
  have e : M.T^[n] (M.vstar hβ) = M.vstar hβ :=
    Function.iterate_fixed (M.T_vstar hβ) n
  rwa [e] at h

/-- **Relative values converge at rate `βα`**: `|rel(TⁿV)(s) − rel(v*)(s)| ≤ (βα)ⁿ sp(V − v*)`. -/
theorem rel_converges (hβ : M.β < 1) {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (s₀ : S) (v : S → ℝ) (n : ℕ) (s : S) :
    |rel s₀ (M.T^[n] v) s - rel s₀ (M.vstar hβ) s| ≤
      (M.β * α) ^ n * sp (fun s => v s - M.vstar hβ s) := by
  refine le_trans ?_ (M.sp_iterate_sub_vstar hβ hα v n)
  have := abs_sub_le_sp (fun s => M.T^[n] v s - M.vstar hβ s) s s₀
  simp only [rel]
  convert this using 2
  ring

/-- **The MacQueen–Porteus bound**: a policy greedy for `v` is within `β/(1 − β)·sp(Tv − v)` of
optimal. -/
theorem policy_error (hβ : M.β < 1) {v : S → ℝ} {σ : S → A} (hσ : M.IsGreedy σ v) (s : S) :
    0 ≤ M.vstar hβ s - M.vσ hβ σ s ∧
      M.vstar hβ s - M.vσ hβ σ s ≤ M.β / (1 - M.β) * sp (fun s => M.T v s - v s) := by
  have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
  have hpol : M.IsPolicy σ := fun s => (hσ s).1
  refine ⟨sub_nonneg.2 (M.vσ_le_vstar hβ hpol s), ?_⟩
  set d : S → ℝ := fun s => M.T v s - v s
  set hi := univ.sup' univ_nonempty d
  set lo := univ.inf' univ_nonempty d
  have hhi : ∀ s, M.T v s ≤ v s + hi := fun s => by linarith [le_sup'_sp d s]
  have hlo : ∀ s, v s + lo ≤ M.T v s := fun s => by linarith [inf'_le_sp d s]
  set kh := M.β * hi / (1 - M.β)
  set kl := M.β * lo / (1 - M.β)
  have ekh : M.β * hi + M.β * kh = kh := by simp only [kh]; field_simp; ring
  have ekl : M.β * lo + M.β * kl = kl := by simp only [kl]; field_simp; ring
  -- `v* ≤ Tv + βhi/(1 − β)`
  have hup : M.vstar hβ ≤ fun s => M.T v s + kh := by
    refine M.vstar_le_of_T_le hβ fun s => ?_
    rw [T_add_const]
    have h1 := M.T_mono (fun s => hhi s) s
    rw [T_add_const] at h1
    simp only at h1 ⊢
    linarith
  -- `v_σ ≥ Tv + βlo/(1 − β)`
  have hdown : (fun s => M.T v s + kl) ≤ M.vσ hβ σ := by
    refine M.le_vσ_of_le hβ σ fun s => ?_
    rw [Tσ_add_const]
    have h1 := M.Tσ_mono σ (fun s => hlo s) s
    rw [Tσ_add_const, M.Tσ_eq_T_of_greedy hσ] at h1
    simp only at h1 ⊢
    have h2 : M.Tσ σ (M.T v) s = M.Tσ σ (M.T v) s := rfl
    linarith
  have h1 := hup s
  have h2 := hdown s
  simp only at h1 h2
  have e : M.β / (1 - M.β) * sp d = kh - kl := by
    simp only [sp, kh, kl, hi, lo]
    field_simp
  rw [e]
  linarith

/-- The relative value iterates `V_n = rel(TⁿV₀)`. -/
noncomputable def relIter (s₀ : S) (V₀ : S → ℝ) (n : ℕ) : S → ℝ := rel s₀ (M.T^[n] V₀)

omit [Nonempty S] in
theorem relIter_succ (s₀ : S) (V₀ : S → ℝ) (n : ℕ) :
    M.relIter s₀ V₀ (n + 1) = rel s₀ (M.T (M.relIter s₀ V₀ n)) := by
  simp only [relIter]
  rw [← M.relT_iterate s₀ V₀ (n + 1), ← M.relT_iterate s₀ V₀ n, Function.iterate_succ_apply']

theorem sp_T_relIter_sub (s₀ : S) (V₀ : S → ℝ) (n : ℕ) :
    sp (fun s => M.T (M.relIter s₀ V₀ n) s - M.relIter s₀ V₀ n s) =
      sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) := by
  rw [M.relIter_succ]
  have := sp_add_const (fun s => rel s₀ (M.T (M.relIter s₀ V₀ n)) s - M.relIter s₀ V₀ n s)
    (M.T (M.relIter s₀ V₀ n) s₀)
  rw [← this]
  congr 1
  funext s
  simp only [rel]
  ring

/-- **Bray's stopping rule**: the policy greedy for `V_n` is `ε`-optimal as soon as
`β/(1 − β)·sp(V_{n+1} − V_n) ≤ ε`. -/
theorem stopping_rule (hβ : M.β < 1) (s₀ : S) (V₀ : S → ℝ) (n : ℕ) {σ : S → A}
    (hσ : M.IsGreedy σ (M.relIter s₀ V₀ n)) (s : S) :
    M.vstar hβ s - M.vσ hβ σ s ≤
      M.β / (1 - M.β) * sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) := by
  have h := (M.policy_error hβ hσ s).2
  rwa [M.sp_T_relIter_sub] at h

/-- **Bray's stopping rule in the supremum norm**: if `|V_{n+1}(s) − V_n(s)| ≤ ε(1 − β)/(2β)`
for all `s`, the policy greedy for `V_n` is `ε`-optimal. -/
theorem stopping_rule_sup (hβ : M.β < 1) (hβ0 : 0 < M.β) {ε : ℝ} (s₀ : S) (V₀ : S → ℝ) (n : ℕ)
    (hstop : ∀ s, |M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s| ≤ ε * (1 - M.β) / (2 * M.β))
    {σ : S → A} (hσ : M.IsGreedy σ (M.relIter s₀ V₀ n)) (s : S) :
    M.vstar hβ s - M.vσ hβ σ s ≤ ε := by
  have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
  have hsp : sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) ≤
      ε * (1 - M.β) / M.β := by
    refine sp_le fun x y => ?_
    have h1 := abs_le.1 (hstop x)
    have h2 := abs_le.1 (hstop y)
    have e : ε * (1 - M.β) / M.β = 2 * (ε * (1 - M.β) / (2 * M.β)) := by field_simp
    rw [e]
    linarith [h1.2, h2.1]
  refine (M.stopping_rule hβ s₀ V₀ n hσ s).trans ?_
  calc M.β / (1 - M.β) * sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s)
      ≤ M.β / (1 - M.β) * (ε * (1 - M.β) / M.β) :=
        mul_le_mul_of_nonneg_left hsp (div_nonneg M.β_nonneg hβ1.le)
    _ = ε := by field_simp

/-- The stopping statistic decays geometrically at rate `βα`. -/
theorem sp_relIter_succ_sub_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (s₀ : S) (V₀ : S → ℝ) (n : ℕ) :
    sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) ≤
      (M.β * α) ^ n * sp (fun s => M.T V₀ s - V₀ s) := by
  have e : (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) =
      fun s => (M.T^[n] (M.T V₀) s - M.T^[n] V₀ s) +
        -(M.T^[n + 1] V₀ s₀ - M.T^[n] V₀ s₀) := by
    funext s
    simp only [relIter, rel, Function.iterate_succ_apply]
    ring
  rw [e, sp_add_const]
  exact M.sp_T_iterate_sub_le hα _ _ n

/-- **Relative value iteration stops**: for `β < 1` the stopping statistic tends to `0`, so any
positive tolerance is met after finitely many steps. -/
theorem stopping_eventually (hβ : M.β < 1) (s₀ : S) (V₀ : S → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) < δ := by
  have hlim : Tendsto (fun n : ℕ => (M.β * 1) ^ n * sp (fun s => M.T V₀ s - V₀ s)) atTop
      (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg hβ).mul_const
      (sp (fun s => M.T V₀ s - V₀ s))
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  exact lt_of_le_of_lt (M.sp_relIter_succ_sub_le (fun s a s' a' _ _ =>
    M.dobrushin_le_one s a s' a') s₀ V₀ n) hn

end MDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Average reward: White's relative value iteration

White (1963); Puterman (2005).

With `β = 1` value iteration diverges (values grow like `n·g`), but relative value iteration
still converges when the Dobrushin coefficient is below one.

* `white`: if `α < 1`, the relative iterates `V_n = rel(TⁿV₀)` converge to some `h` with
  `h(s₀) = 0` and `Th = h + g` — the **average-reward optimality equation**, with gain `g`.
* `avg_upper`, `avg_greedy`, `avg_tendsto`: every feasible policy earns at most `n·g + 2‖h‖` over
  `n` periods, and a policy greedy for `h` earns within `2‖h‖` of `n·g`; so `g` is the optimal
  long-run average reward and the greedy policy attains it.
* `gain_unique`: every solution of the optimality equation has the same gain.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

theorem Tσ_iterate_add_const (hβ : M.β = 1) (σ : S → A) (v : S → ℝ) (c : ℝ) (n : ℕ) :
    (M.Tσ σ)^[n] (fun t => v t + c) = fun s => (M.Tσ σ)^[n] v s + c := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Tσ_add_const, hβ, one_mul, ih]

theorem T_iterate_of_poisson (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    (n : ℕ) (s : S) : M.T^[n] h s = h s + n * g := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have e2 : M.T^[n] h = fun t => h t + n * g := funext ih
    rw [e2, T_add_const, hβ, one_mul]
    change M.T h s + n * g = _
    rw [hpe]
    push_cast
    ring

theorem Tσ_iterate_le_T_iterate {σ : S → A} (hσ : M.IsPolicy σ) (v : S → ℝ) (n : ℕ) :
    (M.Tσ σ)^[n] v ≤ M.T^[n] v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (M.Tσ_mono σ ih).trans (M.Tσ_le_T hσ _)

theorem norm_bound (h : S → ℝ) (s : S) : -‖h‖ ≤ h s ∧ h s ≤ ‖h‖ := by
  have := norm_le_pi_norm h s
  rw [Real.norm_eq_abs] at this
  exact abs_le.1 this

/-- **No policy beats the gain**: over `n` periods every feasible policy earns at most
`n·g + 2‖h‖` from every state. -/
theorem avg_upper (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    {σ : S → A} (hσ : M.IsPolicy σ) (n : ℕ) (s : S) :
    (M.Tσ σ)^[n] 0 s ≤ n * g + 2 * ‖h‖ := by
  have h0 : (0 : S → ℝ) ≤ fun t => h t + ‖h‖ := fun t => by
    have := (norm_bound h t).1
    change (0 : ℝ) ≤ h t + ‖h‖
    linarith
  have h1 := (Monotone.iterate (M.Tσ_mono σ) n) h0 s
  rw [M.Tσ_iterate_add_const hβ] at h1
  have h2 := M.Tσ_iterate_le_T_iterate hσ h n s
  rw [M.T_iterate_of_poisson hβ hpe] at h2
  have h3 := (norm_bound h s).2
  simp only at h1
  linarith

/-- **The greedy policy attains the gain**: a policy greedy for `h` earns within `2‖h‖` of `n·g`
over `n` periods. -/
theorem avg_greedy (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    {σ : S → A} (hσ : M.IsGreedy σ h) (n : ℕ) (s : S) :
    |(M.Tσ σ)^[n] 0 s - n * g| ≤ 2 * ‖h‖ := by
  have hpol : M.IsPolicy σ := fun s => (hσ s).1
  have hexact : ∀ n, ∀ s, (M.Tσ σ)^[n] h s = h s + n * g := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply']
      have e : (M.Tσ σ)^[n] h = fun t => h t + n * g := funext ih
      rw [e, Tσ_add_const, hβ, one_mul, M.Tσ_eq_T_of_greedy hσ]
      change M.T h s + n * g = _
      rw [hpe]
      push_cast
      ring
  have hle : (fun t => h t + -‖h‖) ≤ (0 : S → ℝ) := fun t => by
    have := (norm_bound h t).2
    change h t + -‖h‖ ≤ 0
    linarith
  have h1 := (Monotone.iterate (M.Tσ_mono σ) n) hle s
  rw [M.Tσ_iterate_add_const hβ] at h1
  simp only at h1
  rw [hexact n s] at h1
  have h2 := M.avg_upper hβ hpe hpol n s
  have h3 := (norm_bound h s).1
  rw [abs_le]
  constructor <;> linarith

/-- The greedy policy's average reward converges to the gain. -/
theorem avg_tendsto (hβ : M.β = 1) {h : S → ℝ} {g : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    {σ : S → A} (hσ : M.IsGreedy σ h) (s : S) :
    Tendsto (fun n : ℕ => (M.Tσ σ)^[n] 0 s / n) atTop (𝓝 g) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * ‖h‖ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => dist_nonneg) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Real.dist_eq, le_div_iff₀ hn']
  have e : ((M.Tσ σ)^[n] 0 s / n - g) * n = (M.Tσ σ)^[n] 0 s - n * g := by
    field_simp
  calc |(M.Tσ σ)^[n] 0 s / n - g| * n = |((M.Tσ σ)^[n] 0 s / n - g) * n| := by
        rw [abs_mul, abs_of_pos hn']
    _ = |(M.Tσ σ)^[n] 0 s - n * g| := by rw [e]
    _ ≤ 2 * ‖h‖ := M.avg_greedy hβ hpe hσ n s

variable [Nonempty S]

/-- **The gain is unique**: all solutions of the average-reward optimality equation share it. -/
theorem gain_unique (hβ : M.β = 1) {h h' : S → ℝ} {g g' : ℝ} (hpe : ∀ s, M.T h s = h s + g)
    (hpe' : ∀ s, M.T h' s = h' s + g') : g = g' := by
  have key : ∀ {h h' : S → ℝ} {g g' : ℝ}, (∀ s, M.T h s = h s + g) →
      (∀ s, M.T h' s = h' s + g') → g ≤ g' := by
    intro h h' g g' hpe hpe'
    obtain ⟨σ, hσ⟩ := M.exists_greedy h
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_gt ((2 * ‖h‖ + 2 * ‖h'‖) / (g - g'))
    set s := Classical.arbitrary S
    have h1 := abs_le.1 (M.avg_greedy hβ hpe hσ n s)
    have h2 := M.avg_upper hβ hpe' (fun s => (hσ s).1) n s
    rw [div_lt_iff₀ (sub_pos.2 hlt)] at hn
    nlinarith
  exact le_antisymm (key hpe hpe') (key hpe' hpe)

/-- **White's theorem**: with `β = 1` and Dobrushin coefficient `α < 1`, relative value iteration
converges to a solution `h` of the average-reward optimality equation `Th = h + g`, normalized by
`h(s₀) = 0`. -/
theorem white (hβ : M.β = 1) {α : ℝ} (hα1 : α < 1)
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (s₀ : S) (V₀ : S → ℝ) :
    ∃ h : S → ℝ, ∃ g : ℝ, (∀ s, M.T h s = h s + g) ∧ h s₀ = 0 ∧
      Tendsto (M.relIter s₀ V₀) atTop (𝓝 h) := by
  set u := M.relIter s₀ V₀
  set C := sp (fun s => M.T V₀ s - V₀ s)
  have hstep : ∀ n, dist (u n) (u (n + 1)) ≤ C * α ^ n := fun n => by
    rw [dist_comm, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (sp_nonneg _)
      (pow_nonneg (M.alpha_nonneg hα) n))).2 fun s => ?_
    have h1 := M.sp_relIter_succ_sub_le hα s₀ V₀ n
    rw [hβ, one_mul] at h1
    have h2 := abs_sub_le_sp (fun s => u (n + 1) s - u n s) s s₀
    have h3 : u (n + 1) s₀ - u n s₀ = 0 := by simp [u, relIter, rel]
    rw [Pi.sub_apply, Real.norm_eq_abs]
    simp only [h3, sub_zero] at h2
    linarith [mul_comm C (α ^ n)]
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric α C hα1 hstep)
  have hTc : Continuous M.T := (LipschitzWith.of_dist_le_mul (K := 1) fun v w => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact (M.norm_T_sub_le v w).trans (mul_le_of_le_one_left (norm_nonneg _) M.β_le_one)
    ).continuous
  have hrel : Continuous (rel s₀ : (S → ℝ) → S → ℝ) := by
    unfold rel
    fun_prop
  have hF : Tendsto (fun n => u (n + 1)) atTop (𝓝 (rel s₀ (M.T h))) := by
    have : (fun n => u (n + 1)) = fun n => rel s₀ (M.T (u n)) :=
      funext fun n => M.relIter_succ s₀ V₀ n
    rw [this]
    exact ((hrel.comp hTc).tendsto h).comp hh
  have hfix : h = rel s₀ (M.T h) := tendsto_nhds_unique (hh.comp (tendsto_add_atTop_nat 1)) hF
  refine ⟨h, M.T h s₀, fun s => ?_, ?_, hh⟩
  · have := congrFun hfix s
    simp only [rel] at this
    linarith
  · have := congrFun hfix s₀
    simpa [rel] using this

end MDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Endogenous value iteration

Bray (2019, *Management Science*), Propositions 1–4.

The state is `(x, y)`: the **exogenous** variable `x` evolves by `F_x(x, x')` whatever the agent
does, the **endogenous** variable `y` by `F_y(x, y, a, y')`. Endogenous value iteration iterates
`ΛT`, where `Λ` subtracts from `v(x, y)` its mean over `y` given `x` (`endo`).

* `T_add_lift`, `isGreedy_add_lift_iff`: adding any function of `x` alone to `v` shifts `Tv` by a
  function of `x` and leaves greedy policies unchanged (Bray, Prop 1.3): the policy depends only
  on the endogenous value function.
* `endo_decomp`, `isGreedy_endo_iff`, `endoT_iterate`: `v = Λv + (mean of v over y)`, greedy
  policies for `Λv` and `v` coincide, and iterating `ΛT` gives `ΛTⁿ`.
* `spy_T_sub_le`: with `spy(v) = max_x sp(v(x, ·))` and `α_y` bounding the **endogenous**
  Dobrushin coefficient `1 − ∑_{y''} min(F_y(x, y, a, y''), F_y(x, y', a', y''))`,
  `spy(Tv − Tw) ≤ βα_y·spy(v − w)`; `endo_converges`: endogenous values converge at rate
  `βα_y`.
* `endoCoeff_le` (Bray, Prop 4, non-asymptotic): any bound on the full Dobrushin coefficient
  bounds the endogenous one, so endogenous value iteration is never slower than relative value
  iteration; `relative_slow_endogenous_exact`: it can be infinitely faster.
* `vstar_recover` (Bray, Prop 2): `v*` is recovered from `Λv*` by solving a linear equation in
  `x` alone; `optimal_of_greedy_endo`, `endo_policy_error`: policies greedy for endogenous values
  are optimal in the limit and `2β/(1 − β)·spy(TⁿV₀ − v*)`-optimal along the way.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

variable (X Y A : Type*) [Fintype X] [Fintype Y] in
/-- An MDP whose state `(x, y)` has an exogenous component `x`. -/
structure ExoMDP where
  /-- feasible actions -/
  Γ : X × Y → Finset A
  Γ_nonempty : ∀ s, (Γ s).Nonempty
  /-- rewards -/
  r : X × Y → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_le_one : β ≤ 1
  /-- the exogenous transition matrix -/
  Fx : X → X → ℝ
  Fx_nonneg : ∀ x x', 0 ≤ Fx x x'
  Fx_sum : ∀ x, ∑ x', Fx x x' = 1
  /-- the endogenous transition probabilities -/
  Fy : X → Y → A → Y → ℝ
  Fy_nonneg : ∀ x y a y', 0 ≤ Fy x y a y'
  Fy_sum : ∀ x y a, ∑ y', Fy x y a y' = 1

namespace ExoMDP

variable {X Y A : Type*} [Fintype X] [Fintype Y] (E : ExoMDP X Y A)

/-- The underlying MDP on `X × Y`. -/
abbrev toMDP : MDP (X × Y) A where
  Γ := E.Γ
  Γ_nonempty := E.Γ_nonempty
  r := E.r
  β := E.β
  β_nonneg := E.β_nonneg
  β_le_one := E.β_le_one
  P s a s' := E.Fx s.1 s'.1 * E.Fy s.1 s.2 a s'.2
  P_nonneg s a s' := mul_nonneg (E.Fx_nonneg _ _) (E.Fy_nonneg _ _ _ _)
  P_sum s a := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, E.Fy_sum, mul_one, E.Fx_sum]

/-- A function of the exogenous state, lifted to `X × Y`. -/
def lift (c : X → ℝ) (s : X × Y) : ℝ := c s.1

/-- `(F_x c)(x) = ∑_{x'} F_x(x, x')c(x')`. -/
def Fxc (c : X → ℝ) (x : X) : ℝ := ∑ x', E.Fx x x' * c x'

theorem sum_P_mul (s : X × Y) (a : A) (v : X × Y → ℝ) :
    ∑ s', E.toMDP.P s a s' * v s' = ∑ x', E.Fx s.1 x' * ∑ y', E.Fy s.1 s.2 a y' * v (x', y') := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x' _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y' _ => by ring

theorem Q_add_lift (v : X × Y → ℝ) (c : X → ℝ) (s : X × Y) (a : A) :
    E.toMDP.Q (fun t => v t + lift c t) s a = E.toMDP.Q v s a + E.β * E.Fxc c s.1 := by
  simp only [MDP.Q, E.sum_P_mul, lift, mul_add, sum_add_distrib, ← sum_mul, E.Fy_sum, one_mul,
    Fxc]
  ring

theorem T_add_lift (v : X × Y → ℝ) (c : X → ℝ) :
    E.toMDP.T (fun t => v t + lift c t) = fun s => E.toMDP.T v s + E.β * E.Fxc c s.1 := by
  funext s
  simp only [MDP.T, Q_add_lift]
  exact (sup'_add _ _ _ _).symm

/-- **Policies ignore exogenous shifts** (Bray, Prop 1.3). -/
theorem isGreedy_add_lift_iff (σ : X × Y → A) (v : X × Y → ℝ) (c : X → ℝ) :
    E.toMDP.IsGreedy σ (fun t => v t + lift c t) ↔ E.toMDP.IsGreedy σ v := by
  simp only [MDP.IsGreedy, Q_add_lift, add_le_add_iff_right]

/-- The mean of `v` over the endogenous variable. -/
noncomputable def mean (v : X × Y → ℝ) (x : X) : ℝ := (∑ y, v (x, y)) / Fintype.card Y

/-- The endogenizing operator `Λ`: subtract the mean over `y` given `x`. -/
noncomputable def endo (v : X × Y → ℝ) (s : X × Y) : ℝ := v s - mean v s.1

omit [Fintype X] in
theorem endo_decomp (v : X × Y → ℝ) : v = fun s => endo v s + lift (mean v) s := by
  funext s
  simp only [endo, lift]
  ring

omit [Fintype X] in
theorem mean_add_lift [Nonempty Y] (v : X × Y → ℝ) (c : X → ℝ) (x : X) :
    mean (fun t => v t + lift c t) x = mean v x + c x := by
  have hY : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [mean, lift, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Fintype X] in
theorem endo_add_lift [Nonempty Y] (v : X × Y → ℝ) (c : X → ℝ) :
    endo (fun t => v t + lift c t) = endo v := by
  funext s
  simp only [endo]
  rw [mean_add_lift]
  simp only [lift]
  ring

/-- Greedy policies for `Λv` and for `v` coincide. -/
theorem isGreedy_endo_iff (σ : X × Y → A) (v : X × Y → ℝ) :
    E.toMDP.IsGreedy σ (endo v) ↔ E.toMDP.IsGreedy σ v := by
  conv_rhs => rw [endo_decomp v]
  exact (E.isGreedy_add_lift_iff σ (endo v) (mean v)).symm

/-- **Endogenous value iteration is value iteration up to an exogenous function**: iterating
`v ↦ Λ(Tv)` from `Λv` gives `Λ(Tⁿv)`. -/
theorem endoT_iterate [Nonempty Y] (v : X × Y → ℝ) (n : ℕ) :
    (fun w => endo (E.toMDP.T w))^[n] (endo v) = endo (E.toMDP.T^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    have e : endo (E.toMDP.T^[n] v) =
        fun t => E.toMDP.T^[n] v t + lift (fun x => -mean (E.toMDP.T^[n] v) x) t := by
      funext t
      simp only [endo, lift]
      ring
    have e2 : (fun s => E.toMDP.T (E.toMDP.T^[n] v) s +
        E.β * E.Fxc (fun x => -mean (E.toMDP.T^[n] v) x) s.1) =
        fun s => E.toMDP.T (E.toMDP.T^[n] v) s +
          lift (fun x => E.β * E.Fxc (fun x => -mean (E.toMDP.T^[n] v) x) x) s := rfl
    rw [e, T_add_lift, e2, endo_add_lift]

omit [Fintype X] in
theorem endo_sub (v w : X × Y → ℝ) :
    endo (fun s => v s - w s) = fun s => endo v s - endo w s := by
  funext s
  simp only [endo, mean, sum_sub_distrib, sub_div]
  ring

variable [Nonempty X] [Nonempty Y]

/-- The within-`x` span `spy(v) = max_x sp(v(x, ·))`. -/
noncomputable def spy (v : X × Y → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun x => sp fun y => v (x, y)

theorem sp_le_spy (v : X × Y → ℝ) (x : X) : sp (fun y => v (x, y)) ≤ spy v :=
  le_sup' (fun x => sp fun y => v (x, y)) (mem_univ x)

theorem spy_nonneg (v : X × Y → ℝ) : 0 ≤ spy v :=
  (sp_nonneg _).trans (sp_le_spy v (Classical.arbitrary X))

/-- `spy ≤ sp`. -/
theorem spy_le_sp (v : X × Y → ℝ) : spy v ≤ sp v :=
  sup'_le _ _ fun x _ => sp_le fun y y' => sub_le_sp v (x, y) (x, y')

omit [Fintype X] [Nonempty X] in
/-- `|Λd(x, y)| ≤ sp(d(x, ·))`: a value differs from its mean by at most the span. -/
theorem abs_endo_le_sp (d : X × Y → ℝ) (s : X × Y) : |endo d s| ≤ sp fun y => d (s.1, y) := by
  have hY : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  have e : endo d s = (∑ y, (d s - d (s.1, y))) / Fintype.card Y := by
    simp only [endo, mean, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  rw [e, abs_div, abs_of_pos hY, div_le_iff₀ hY]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y, |d s - d (s.1, y)| ≤ ∑ _y : Y, sp fun y => d (s.1, y) := sum_le_sum fun y _ =>
        abs_sub_le_sp (fun y => d (s.1, y)) s.2 y
    _ = (sp fun y => d (s.1, y)) * Fintype.card Y := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

theorem abs_endo_le (d : X × Y → ℝ) (s : X × Y) : |endo d s| ≤ spy d :=
  (abs_endo_le_sp d s).trans (sp_le_spy d s.1)

theorem alphaY_nonneg {α : ℝ}
    (hα : ∀ x y a y' a', a ∈ E.Γ (x, y) → a' ∈ E.Γ (x, y') →
      1 - ∑ y'', min (E.Fy x y a y'') (E.Fy x y' a' y'') ≤ α) : 0 ≤ α := by
  set x := Classical.arbitrary X
  set y := Classical.arbitrary Y
  obtain ⟨a, ha⟩ := E.Γ_nonempty (x, y)
  have h := hα x y a y a ha ha
  simp only [min_self, E.Fy_sum] at h
  linarith

/-- **The endogenous span contraction**: if `α` bounds the endogenous Dobrushin coefficient,
`spy(Tv − Tw) ≤ βα·spy(v − w)`. -/
theorem spy_T_sub_le {α : ℝ}
    (hα : ∀ x y a y' a', a ∈ E.Γ (x, y) → a' ∈ E.Γ (x, y') →
      1 - ∑ y'', min (E.Fy x y a y'') (E.Fy x y' a' y'') ≤ α)
    (v w : X × Y → ℝ) :
    spy (fun s => E.toMDP.T v s - E.toMDP.T w s) ≤ E.β * α * spy (fun s => v s - w s) := by
  have hα0 := E.alphaY_nonneg hα
  refine sup'_le _ _ fun x _ => sp_le fun y y' => ?_
  obtain ⟨a, ha, hva, -⟩ := E.toMDP.exists_greedyAct v (x, y)
  obtain ⟨a', ha', hwa', -⟩ := E.toMDP.exists_greedyAct w (x, y')
  have h1 : E.toMDP.Q w (x, y) a ≤ E.toMDP.T w (x, y) := E.toMDP.Q_le_T w ha
  have h2 : E.toMDP.Q v (x, y') a' ≤ E.toMDP.T v (x, y') := E.toMDP.Q_le_T v ha'
  set d : X × Y → ℝ := fun s => v s - w s
  have e1 := E.toMDP.Q_sub_Q v w (x, y) a
  have e2 := E.toMDP.Q_sub_Q v w (x, y') a'
  rw [E.sum_P_mul] at e1 e2
  have hkey : ∑ x', E.Fx x x' * ∑ y'', E.Fy x y a y'' * d (x', y'') -
      ∑ x', E.Fx x x' * ∑ y'', E.Fy x y' a' y'' * d (x', y'') ≤ α * spy d := by
    rw [← sum_sub_distrib]
    calc ∑ x', (E.Fx x x' * ∑ y'', E.Fy x y a y'' * d (x', y'') -
          E.Fx x x' * ∑ y'', E.Fy x y' a' y'' * d (x', y''))
        ≤ ∑ x', E.Fx x x' * (α * spy d) := sum_le_sum fun x' _ => by
          rw [← mul_sub]
          refine mul_le_mul_of_nonneg_left ?_ (E.Fx_nonneg x x')
          have hd := dobrushin (E.Fy_sum x y a) (E.Fy_sum x y' a') fun y'' => d (x', y'')
          have hs := sp_nonneg fun y'' => d (x', y'')
          have hc := mul_le_mul_of_nonneg_right (hα x y a y' a' ha ha') hs
          have hsy := mul_le_mul_of_nonneg_left (sp_le_spy d x') hα0
          linarith
      _ = α * spy d := by rw [← sum_mul, E.Fx_sum, one_mul]
  have hβ := mul_le_mul_of_nonneg_left hkey E.β_nonneg
  simp only [toMDP] at e1 e2 hva hwa' h1 h2 ⊢
  simp only [d] at hβ ⊢
  nlinarith

omit [Nonempty X] [Nonempty Y] in
/-- **Endogenous coefficients are no larger** (Bray, Prop 4, non-asymptotic): any bound on the
full Dobrushin coefficient bounds the endogenous one. -/
theorem endoCoeff_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ E.toMDP.Γ s → a' ∈ E.toMDP.Γ s' →
      1 - ∑ t, min (E.toMDP.P s a t) (E.toMDP.P s' a' t) ≤ α) :
    ∀ x y a y' a', a ∈ E.Γ (x, y) → a' ∈ E.Γ (x, y') →
      1 - ∑ y'', min (E.Fy x y a y'') (E.Fy x y' a' y'') ≤ α := by
  intro x y a y' a' ha ha'
  have h := hα (x, y) a (x, y') a' ha ha'
  have e : ∑ t, min (E.toMDP.P (x, y) a t) (E.toMDP.P (x, y') a' t) =
      ∑ y'', min (E.Fy x y a y'') (E.Fy x y' a' y'') := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_min_of_nonneg _ _ (E.Fx_nonneg _ _)]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun y'' _ => ?_
    rw [← sum_mul, E.Fx_sum, one_mul]
  rwa [e] at h

theorem spy_T_iterate_sub_le {α : ℝ}
    (hα : ∀ x y a y' a', a ∈ E.Γ (x, y) → a' ∈ E.Γ (x, y') →
      1 - ∑ y'', min (E.Fy x y a y'') (E.Fy x y' a' y'') ≤ α)
    (v w : X × Y → ℝ) (n : ℕ) :
    spy (fun s => E.toMDP.T^[n] v s - E.toMDP.T^[n] w s) ≤
      (E.β * α) ^ n * spy (fun s => v s - w s) := by
  have hc : 0 ≤ E.β * α := mul_nonneg E.β_nonneg (E.alphaY_nonneg hα)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    calc spy (fun s => E.toMDP.T (E.toMDP.T^[n] v) s - E.toMDP.T (E.toMDP.T^[n] w) s)
        ≤ E.β * α * spy (fun s => E.toMDP.T^[n] v s - E.toMDP.T^[n] w s) :=
          E.spy_T_sub_le hα _ _
      _ ≤ E.β * α * ((E.β * α) ^ n * spy (fun s => v s - w s)) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (E.β * α) ^ n * (E.β * α) * spy (fun s => v s - w s) := by ring

/-- **Endogenous value iteration converges at rate `βα_y`**. -/
theorem endo_converges (hβ : E.β < 1) {α : ℝ}
    (hα : ∀ x y a y' a', a ∈ E.Γ (x, y) → a' ∈ E.Γ (x, y') →
      1 - ∑ y'', min (E.Fy x y a y'') (E.Fy x y' a' y'') ≤ α)
    (v : X × Y → ℝ) (n : ℕ) (s : X × Y) :
    |endo (E.toMDP.T^[n] v) s - endo (E.toMDP.vstar hβ) s| ≤
      (E.β * α) ^ n * spy (fun s => v s - E.toMDP.vstar hβ s) := by
  have h := E.spy_T_iterate_sub_le hα v (E.toMDP.vstar hβ) n
  rw [Function.iterate_fixed (E.toMDP.T_vstar hβ) n] at h
  have e := congrFun (endo_sub (E.toMDP.T^[n] v) (E.toMDP.vstar hβ)) s
  rw [← e]
  exact (abs_endo_le _ s).trans h

omit [Nonempty X] in
/-- **Recovering `v*` from the endogenous value function** (Bray, Prop 2): `v* = Λv* + m`, where
the exogenous part `m(x) = mean_y v*(x, y)` solves `m = g + βF_x m` with `g = mean_y T(Λv*)`. -/
theorem vstar_recover (hβ : E.β < 1) (x : X) :
    mean (E.toMDP.vstar hβ) x =
      mean (E.toMDP.T (endo (E.toMDP.vstar hβ))) x + E.β * E.Fxc (mean (E.toMDP.vstar hβ)) x := by
  have h1 := E.toMDP.T_vstar hβ
  rw [endo_decomp (E.toMDP.vstar hβ)] at h1
  rw [E.T_add_lift] at h1
  have h2 := congrArg (fun v => mean v x) h1
  have e : (fun s => E.toMDP.T (endo (E.toMDP.vstar hβ)) s +
      E.β * E.Fxc (mean (E.toMDP.vstar hβ)) s.1) =
      fun s => E.toMDP.T (endo (E.toMDP.vstar hβ)) s +
        lift (fun x => E.β * E.Fxc (mean (E.toMDP.vstar hβ)) x) s := rfl
  rw [e, mean_add_lift, mean_add_lift] at h2
  have h3 : mean (endo (E.toMDP.vstar hβ)) x = 0 := by
    have hY : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [mean, endo, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring
  linarith

omit [Nonempty X] [Nonempty Y] in
/-- The exogenous part is the unique solution of `m = g + βF_x m`. -/
theorem mean_unique (hβ : E.β < 1) {g m m' : X → ℝ} (hm : ∀ x, m x = g x + E.β * E.Fxc m x)
    (hm' : ∀ x, m' x = g x + E.β * E.Fxc m' x) : m = m' := by
  have hb : ∀ x, |m x - m' x| ≤ E.β * ‖m - m'‖ := fun x => by
    rw [hm x, hm' x, show g x + E.β * E.Fxc m x - (g x + E.β * E.Fxc m' x) =
      E.β * ∑ x', E.Fx x x' * (m x' - m' x') by simp only [Fxc, mul_sub, sum_sub_distrib]; ring,
      abs_mul, abs_of_nonneg E.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans ?_) E.β_nonneg
    calc ∑ x', |E.Fx x x' * (m x' - m' x')| ≤ ∑ x', E.Fx x x' * ‖m - m'‖ :=
          sum_le_sum fun x' _ => by
            rw [abs_mul, abs_of_nonneg (E.Fx_nonneg x x')]
            refine mul_le_mul_of_nonneg_left ?_ (E.Fx_nonneg x x')
            have := norm_le_pi_norm (m - m') x'
            rwa [Pi.sub_apply, Real.norm_eq_abs] at this
      _ = ‖m - m'‖ := by rw [← sum_mul, E.Fx_sum, one_mul]
  have hn : ‖m - m'‖ ≤ E.β * ‖m - m'‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg E.β_nonneg (norm_nonneg _))).2 fun x => by
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact hb x
  have h0 : ‖m - m'‖ = 0 := by
    nlinarith [norm_nonneg (m - m'), sub_pos.2 hβ]
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

omit [Nonempty X] [Nonempty Y] in
/-- **A policy greedy for the endogenous value function is optimal** (Bray, Prop 2). -/
theorem optimal_of_greedy_endo (hβ : E.β < 1) {σ : X × Y → A}
    (hσ : E.toMDP.IsGreedy σ (endo (E.toMDP.vstar hβ))) :
    E.toMDP.vσ hβ σ = E.toMDP.vstar hβ := by
  rw [E.isGreedy_endo_iff] at hσ
  have hfix : Function.IsFixedPt (E.toMDP.Tσ σ) (E.toMDP.vstar hβ) := by
    unfold Function.IsFixedPt
    rw [E.toMDP.Tσ_eq_T_of_greedy hσ, E.toMDP.T_vstar]
  exact (ContractingWith.fixedPoint_unique (E.toMDP.contracting_Tσ hβ σ) hfix).symm

/-- **The policy greedy for the `n`-th endogenous iterate is
`2β/(1 − β)·spy(TⁿV₀ − v*)`-optimal.** -/
theorem endo_policy_error (hβ : E.β < 1) (V₀ : X × Y → ℝ) (n : ℕ) {σ : X × Y → A}
    (hσ : E.toMDP.IsGreedy σ (endo (E.toMDP.T^[n] V₀))) :
    (1 - E.β) * ‖E.toMDP.vstar hβ - E.toMDP.vσ hβ σ‖ ≤
      2 * E.β * spy (fun s => E.toMDP.T^[n] V₀ s - E.toMDP.vstar hβ s) := by
  set vs := E.toMDP.vstar hβ
  set d : X × Y → ℝ := fun s => E.toMDP.T^[n] V₀ s - vs s
  set w : X × Y → ℝ := fun s => vs s + endo d s
  have hw : E.toMDP.IsGreedy σ w := by
    have e : w = fun s => endo (E.toMDP.T^[n] V₀) s + lift (mean vs) s := by
      funext s
      have h3 := congrFun (endo_sub (E.toMDP.T^[n] V₀) vs) s
      have h2 := congrFun (endo_decomp vs) s
      simp only [lift] at h2 ⊢
      change vs s + endo (fun s => E.toMDP.T^[n] V₀ s - vs s) s = _
      linarith
    rw [e, E.isGreedy_add_lift_iff]
    exact hσ
  have hwn : ‖w - vs‖ ≤ spy d :=
    (pi_norm_le_iff_of_nonneg (spy_nonneg d)).2 fun s => by
      rw [Pi.sub_apply, Real.norm_eq_abs]
      simp only [w, add_sub_cancel_left]
      exact abs_endo_le d s
  -- the classical bound `(1 − β)‖v* − v_σ‖ ≤ 2β‖w − v*‖` for `σ` greedy for `w`
  have h1 : ‖vs - E.toMDP.vσ hβ σ‖ ≤ E.β * ‖vs - w‖ + E.β * ‖w - E.toMDP.vσ hβ σ‖ := by
    have e : vs - E.toMDP.vσ hβ σ = (E.toMDP.T vs - E.toMDP.T w) +
        (E.toMDP.Tσ σ w - E.toMDP.Tσ σ (E.toMDP.vσ hβ σ)) := by
      rw [E.toMDP.Tσ_eq_T_of_greedy hw, E.toMDP.Tσ_vσ, E.toMDP.T_vstar]
      abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (E.toMDP.norm_T_sub_le _ _)
      (E.toMDP.norm_Tσ_sub_le σ _ _))
  have h2 : ‖w - E.toMDP.vσ hβ σ‖ ≤ ‖w - vs‖ + ‖vs - E.toMDP.vσ hβ σ‖ := by
    have := norm_add_le (w - vs) (vs - E.toMDP.vσ hβ σ)
    rwa [sub_add_sub_cancel] at this
  have h3 : ‖vs - w‖ = ‖w - vs‖ := norm_sub_rev _ _
  have hβ0 := E.β_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h2 hβ0, mul_le_mul_of_nonneg_left hwn hβ0]

end ExoMDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# When relative value iteration does not help but endogenous value iteration does

Bray (2019, *Management Science*), Corollary 3: a non-ergodic exogenous variable voids the strong
convergence of relative value iteration but not that of endogenous value iteration.

The exogenous state `x ∈ {false, true}` alternates deterministically (a seasonal cycle), the
reward is `1` in state `true`, and there is no endogenous state or choice (`swapModel`).

* `swap_dobrushin_ge`: no Dobrushin bound below `1` holds — the chain does not mix.
* `swap_sp_iterate`, `swap_sp_vstar`: the span of the value-iteration error is exactly
  `βⁿ/(1 + β)` from `V₀ = 0`: relative value iteration converges at rate `β`, no faster.
* `swap_endo_exact`: endogenous value iteration is exact from the first step.
-/

open Finset

namespace DPExtensions.RelativeValueIteration

/-- The seasonal example. -/
noncomputable abbrev swapModel (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) : ExoMDP Bool Unit Unit where
  Γ _ := univ
  Γ_nonempty _ := univ_nonempty
  r s _ := if s.1 then 1 else 0
  β := β
  β_nonneg := h0
  β_le_one := h1
  Fx x x' := if x' = !x then 1 else 0
  Fx_nonneg x x' := by split_ifs <;> norm_num
  Fx_sum x := by cases x <;> simp
  Fy _ _ _ _ := 1
  Fy_nonneg _ _ _ _ := zero_le_one
  Fy_sum _ _ _ := by simp

variable {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)

theorem swap_T (v : Bool × Unit → ℝ) (x : Bool) :
    (swapModel β h0 h1).toMDP.T v (x, ()) = (if x then 1 else 0) + β * v (!x, ()) := by
  simp only [MDP.T, MDP.Q, univ_unique, sup'_singleton]
  rw [Fintype.sum_prod_type]
  cases x <;> simp

/-- The two states' next-state distributions are disjoint, so no Dobrushin bound below `1`
holds. -/
theorem swap_dobrushin_ge {α : ℝ}
    (hα : ∀ s a s' a', a ∈ (swapModel β h0 h1).toMDP.Γ s → a' ∈ (swapModel β h0 h1).toMDP.Γ s' →
      1 - ∑ t, min ((swapModel β h0 h1).toMDP.P s a t) ((swapModel β h0 h1).toMDP.P s' a' t) ≤ α) :
    1 ≤ α := by
  have h := hα (true, ()) () (false, ()) () (mem_univ _) (mem_univ _)
  rw [Fintype.sum_prod_type] at h
  simpa using h

theorem sp_bool_unit (f : Bool × Unit → ℝ) : sp f = |f (true, ()) - f (false, ())| := by
  refine le_antisymm (sp_le fun a b => ?_) (abs_sub_le_sp f _ _)
  obtain ⟨x, ⟨⟩⟩ := a
  obtain ⟨y, ⟨⟩⟩ := b
  have h1 := le_abs_self (f (true, ()) - f (false, ()))
  have h2 := neg_abs_le (f (true, ()) - f (false, ()))
  have h3 := abs_nonneg (f (true, ()) - f (false, ()))
  cases x <;> cases y <;> (try simp only [sub_self]) <;> linarith

/-- **Value iteration's error shrinks exactly at rate `β` in span.** -/
theorem swap_sp_iterate (hβ : β < 1) (v : Bool × Unit → ℝ) (n : ℕ) :
    sp (fun s => (swapModel β h0 h1).toMDP.T^[n] v s - (swapModel β h0 h1).toMDP.vstar hβ s) =
      β ^ n * sp (fun s => v s - (swapModel β h0 h1).toMDP.vstar hβ s) := by
  set M := (swapModel β h0 h1).toMDP
  have hstep : ∀ (w : Bool × Unit → ℝ) (x : Bool),
      M.T w (x, ()) - M.vstar hβ (x, ()) = β * (w (!x, ()) - M.vstar hβ (!x, ())) := by
    intro w x
    have h := congrFun (M.T_vstar hβ) (x, ())
    rw [swap_T] at h
    rw [swap_T]
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sp_bool_unit] at ih ⊢
    rw [Function.iterate_succ_apply', hstep, hstep]
    simp only [Bool.not_true, Bool.not_false]
    rw [← mul_sub, abs_mul, abs_of_nonneg h0, abs_sub_comm, ih, pow_succ]
    ring

/-- `sp(v*) = 1/(1 + β)`. -/
theorem swap_sp_vstar (hβ : β < 1) :
    sp ((swapModel β h0 h1).toMDP.vstar hβ) = 1 / (1 + β) := by
  set M := (swapModel β h0 h1).toMDP
  have hfix := M.T_vstar hβ
  have ht := congrFun hfix (true, ())
  have hf := congrFun hfix (false, ())
  rw [swap_T] at ht hf
  norm_num at ht hf
  have e : M.vstar hβ (true, ()) - M.vstar hβ (false, ()) = 1 / (1 + β) := by
    field_simp
    linarith
  rw [sp_bool_unit, e, abs_of_pos (by positivity)]

/-- **Endogenous value iteration is exact**: with no endogenous variation, `Λv = 0` for every
`v`, so every endogenous iterate equals `Λv*`. -/
theorem swap_endo_exact (v : Bool × Unit → ℝ) : ExoMDP.endo v = 0 := by
  funext s
  obtain ⟨x, ⟨⟩⟩ := s
  simp [ExoMDP.endo, ExoMDP.mean]

/-- **Relative value iteration does not speed up; endogenous value iteration is exact.** For
`0 < β < 1`: no Dobrushin bound below `1` holds, the span error of value iteration from `0` is
exactly `βⁿ/(1 + β)`, and the endogenous iterates equal `Λv*` from the start. -/
theorem relative_slow_endogenous_exact (hβ : β < 1) :
    (∀ α : ℝ, (∀ s a s' a', a ∈ (swapModel β h0 h1).toMDP.Γ s →
        a' ∈ (swapModel β h0 h1).toMDP.Γ s' →
        1 - ∑ t, min ((swapModel β h0 h1).toMDP.P s a t)
          ((swapModel β h0 h1).toMDP.P s' a' t) ≤ α) → 1 ≤ α) ∧
    (∀ n, sp (fun s => (swapModel β h0 h1).toMDP.T^[n] 0 s -
        (swapModel β h0 h1).toMDP.vstar hβ s) = β ^ n / (1 + β)) ∧
    ∀ v n, ExoMDP.endo ((swapModel β h0 h1).toMDP.T^[n] v) =
      ExoMDP.endo ((swapModel β h0 h1).toMDP.vstar hβ) := by
  refine ⟨fun α hα => swap_dobrushin_ge h0 h1 hα, fun n => ?_, fun v n => by
    rw [swap_endo_exact, swap_endo_exact]⟩
  rw [swap_sp_iterate h0 h1 hβ]
  have e : (fun s => (0 : Bool × Unit → ℝ) s - (swapModel β h0 h1).toMDP.vstar hβ s) =
      fun s => -(swapModel β h0 h1).toMDP.vstar hβ s := by
    funext s
    simp
  rw [e, sp_neg, swap_sp_vstar h0 h1 hβ]
  ring

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Relative and endogenous policy iteration

Bray (2019a, *Quantitative Economics*), §4.1 and Proposition 4; Bray (2019b, *Management
Science*), §5 and Proposition 3.

Policy iteration sets `σ_{n+1}` greedy for `v_{σ_n}`. Relative policy iteration makes `σ_{n+1}`
greedy for the relative values `Δv_{σ_n}`, and endogenous policy iteration for the endogenous
values `Λv_{σ_n}`. Greedy policies ignore constants and functions of the exogenous state, so all
three produce the same policies; only the policy evaluation step differs, and the relative and
endogenous evaluations converge faster (`sp_policy_eval_le`, `endo_policy_eval_le`).

* `pi_improve`, `pi_mono`, `pi_terminates`: policy iteration improves monotonically and reaches
  `v*` after finitely many steps.
* `isGreedy_rel_iff`, `relPI_terminates`: relative policy iteration is policy iteration.
* `pi_residual_le`, `relPI_stopping`, `relPI_bray` (**Bray, 2019a, Prop 4**): Bray's stopping
  rule `|V_n − V_{n−1}| ≤ ε(1 − β)/(2β)` is met after finitely many iterations, and the policy it
  returns is `ε`-optimal.
* `policy_error_endo`: a policy greedy for `w` is within `β/(1 − β)·sp(Λ(Tw − w))` of optimal —
  only the endogenous part of the Bellman residual matters.
* `endoPI_terminates`, `endoPI_stopping`, `endoPI_bray` (**Bray, 2019b, Prop 3**): the same for
  endogenous policy iteration, with stopping statistic `Λ(TΛv) − Λv`.
-/

open Finset

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

/-- **Policy improvement**: a policy greedy for `v_σ` is at least as good as `σ`. -/
theorem pi_improve (hβ : M.β < 1) {σ σ' : S → A} (hσ : M.IsPolicy σ)
    (hσ' : M.IsGreedy σ' (M.vσ hβ σ)) : M.vσ hβ σ ≤ M.vσ hβ σ' := by
  refine M.le_vσ_of_le hβ σ' ?_
  rw [M.Tσ_eq_T_of_greedy hσ']
  conv_lhs => rw [← M.Tσ_vσ hβ σ]
  exact M.Tσ_le_T hσ _

/-- A fixed point of `T` is `v*`. -/
theorem eq_vstar_of_T_eq (hβ : M.β < 1) {w : S → ℝ} (h : M.T w = w) : w = M.vstar hβ :=
  le_antisymm (M.le_vstar_of_le hβ h.ge) (M.vstar_le_of_T_le hβ h.le)

/-- If policy improvement stalls, the policy is optimal. -/
theorem vσ_eq_vstar_of_stall (hβ : M.β < 1) {σ σ' : S → A}
    (hσ' : M.IsGreedy σ' (M.vσ hβ σ)) (h : M.vσ hβ σ' = M.vσ hβ σ) :
    M.vσ hβ σ = M.vstar hβ := by
  refine M.eq_vstar_of_T_eq hβ ?_
  rw [← M.Tσ_eq_T_of_greedy hσ']
  conv_lhs => rw [← h, M.Tσ_vσ hβ σ']
  exact h

/-- Policy iteration produces a monotone sequence of values. -/
theorem pi_mono (hβ : M.β < 1) {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (M.vσ hβ (σ n))) :
    Monotone fun n => M.vσ hβ (σ n) := by
  have hpol : ∀ n, M.IsPolicy (σ n) := fun n => by
    rcases n with _ | n
    · exact h0
    · exact fun s => (hstep n s).1
  exact monotone_nat_of_le_succ fun n => M.pi_improve hβ (hpol n) (hstep n)

/-- **Policy iteration terminates**: after finitely many steps the policy is optimal. -/
theorem pi_terminates (hβ : M.β < 1) {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (M.vσ hβ (σ n))) :
    ∃ N, ∀ n, N ≤ n → M.vσ hβ (σ n) = M.vstar hβ := by
  have hpol : ∀ n, M.IsPolicy (σ n) := fun n => by
    rcases n with _ | n
    · exact h0
    · exact fun s => (hstep n s).1
  have hmono := M.pi_mono hβ h0 hstep
  -- once optimal, always optimal
  have hstay : ∀ n, M.vσ hβ (σ n) = M.vstar hβ → M.vσ hβ (σ (n + 1)) = M.vstar hβ := by
    intro n hn
    refine le_antisymm (M.vσ_le_vstar hβ (hpol (n + 1))) ?_
    rw [← hn]
    exact hmono (Nat.le_succ n)
  suffices hex : ∃ N, M.vσ hβ (σ N) = M.vstar hβ by
    obtain ⟨N, hN⟩ := hex
    refine ⟨N, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => exact hN
    | succ n _ ih => exact hstay n ih
  by_contra hne
  push Not at hne
  -- the policies are pairwise distinct ...
  have hinj : Function.Injective σ := by
    have hlt : ∀ n m, n < m → σ n ≠ σ m := by
      intro n m hnm heq
      have e : M.vσ hβ (σ (n + 1)) = M.vσ hβ (σ n) := le_antisymm
        ((hmono (Nat.succ_le_of_lt hnm)).trans (by rw [heq])) (hmono (Nat.le_succ n))
      exact hne n (M.vσ_eq_vstar_of_stall hβ (hstep n) e)
    intro n m heq
    rcases lt_trichotomy n m with h | h | h
    · exact absurd heq (hlt n m h)
    · exact h
    · exact absurd heq.symm (hlt m n h)
  -- ... but there are only finitely many policies
  have hfin : (Set.univ.pi fun s => (M.Γ s : Set A)).Finite :=
    Set.Finite.pi fun s => (M.Γ s).finite_toSet
  exact Set.infinite_of_injective_forall_mem hinj (fun n => Set.mem_univ_pi.2 (hpol n)) hfin

variable [Nonempty S]

omit [Nonempty S] in
/-- Greedy policies for the relative values are greedy for the values. -/
theorem isGreedy_rel_iff (s₀ : S) (σ : S → A) (v : S → ℝ) :
    M.IsGreedy σ (rel s₀ v) ↔ M.IsGreedy σ v := by
  rw [show rel s₀ v = fun t => v t + -v s₀ by funext t; simp [rel, sub_eq_add_neg]]
  exact M.isGreedy_add_const_iff σ v _

omit [Nonempty S] in
/-- **Relative policy iteration is policy iteration**, and so terminates. -/
theorem relPI_terminates (hβ : M.β < 1) (s₀ : S) {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (rel s₀ (M.vσ hβ (σ n)))) :
    ∃ N, ∀ n, N ≤ n → M.vσ hβ (σ n) = M.vstar hβ :=
  M.pi_terminates hβ h0 fun n => (M.isGreedy_rel_iff s₀ _ _).1 (hstep n)

/-- **The Bellman residual after a policy improvement step**: if `σ'` is greedy for `v_σ`, then
`0 ≤ Tv_{σ'} − v_{σ'} ≤ β·sp(v_{σ'} − v_σ)`. -/
theorem pi_residual_le (hβ : M.β < 1) {σ σ' : S → A} (hσ' : M.IsGreedy σ' (M.vσ hβ σ))
    (s : S) :
    0 ≤ M.T (M.vσ hβ σ') s - M.vσ hβ σ' s ∧
      M.T (M.vσ hβ σ') s - M.vσ hβ σ' s ≤ M.β * sp (fun t => M.vσ hβ σ' t - M.vσ hβ σ t) := by
  set v := M.vσ hβ σ'
  set w := M.vσ hβ σ
  have hv : v s = M.Q v s (σ' s) := (congrFun (M.Tσ_vσ hβ σ') s).symm
  refine ⟨?_, ?_⟩
  · rw [hv]
    exact sub_nonneg.2 (M.Q_le_T v (hσ' s).1)
  obtain ⟨a, ha, hTa, -⟩ := M.exists_greedyAct v s
  have hw : M.Q w s a ≤ M.Q w s (σ' s) := (hσ' s).2 a ha
  have e1 := M.Q_sub_Q v w s a
  have e2 := M.Q_sub_Q v w s (σ' s)
  have hd := dobrushin (M.P_sum s a) (M.P_sum s (σ' s)) fun t => v t - w t
  have hmin : 0 ≤ ∑ t, min (M.P s a t) (M.P s (σ' s) t) :=
    sum_nonneg fun t _ => le_min (M.P_nonneg s a t) (M.P_nonneg s (σ' s) t)
  have hsp := sp_nonneg fun t => v t - w t
  have hd' : ∑ t, M.P s a t * (v t - w t) - ∑ t, M.P s (σ' s) t * (v t - w t) ≤
      sp (fun t => v t - w t) := by nlinarith
  rw [hTa, hv]
  have := mul_le_mul_of_nonneg_left hd' M.β_nonneg
  nlinarith

/-- **Bray's stopping rule for relative policy iteration** (Bray, 2019a, Prop 4): if `σ'` is
greedy for `V_{n−1} = Δv_σ`, `V_n = Δv_{σ'}` and `|V_n − V_{n−1}| ≤ ε(1 − β)/(2β)`, then any
policy greedy for `V_n` is `ε`-optimal. -/
theorem relPI_stopping (hβ : M.β < 1) (hβ0 : 0 < M.β) {ε : ℝ} (s₀ : S) {σ σ' σ'' : S → A}
    (hσ' : M.IsGreedy σ' (rel s₀ (M.vσ hβ σ)))
    (hstop : ∀ s, |rel s₀ (M.vσ hβ σ') s - rel s₀ (M.vσ hβ σ) s| ≤ ε * (1 - M.β) / (2 * M.β))
    (hσ'' : M.IsGreedy σ'' (rel s₀ (M.vσ hβ σ'))) (s : S) :
    M.vstar hβ s - M.vσ hβ σ'' s ≤ ε := by
  have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
  have hε : 0 ≤ ε := by
    have h := (abs_nonneg _).trans (hstop s)
    have h2 : 0 < (1 - M.β) / (2 * M.β) := by positivity
    rw [mul_div_assoc] at h
    exact nonneg_of_mul_nonneg_left h h2
  have hσ'v := (M.isGreedy_rel_iff s₀ _ _).1 hσ'
  have hσ''v := (M.isGreedy_rel_iff s₀ _ _).1 hσ''
  -- span of the change in values, from the stopping statistic
  have hsp : sp (fun t => M.vσ hβ σ' t - M.vσ hβ σ t) ≤ ε * (1 - M.β) / M.β := by
    refine sp_le fun x y => ?_
    have h1 := abs_le.1 (hstop x)
    have h2 := abs_le.1 (hstop y)
    have e : ε * (1 - M.β) / M.β = 2 * (ε * (1 - M.β) / (2 * M.β)) := by field_simp
    simp only [rel] at h1 h2
    rw [e]
    linarith [h1.2, h2.1]
  -- the Bellman residual of `v_{σ'}`
  have hres : sp (fun t => M.T (M.vσ hβ σ') t - M.vσ hβ σ' t) ≤ M.β * (ε * (1 - M.β) / M.β) :=
    sp_le fun x y => by
      have hx := (M.pi_residual_le hβ hσ'v x).2
      have hy := (M.pi_residual_le hβ hσ'v y).1
      have := mul_le_mul_of_nonneg_left hsp M.β_nonneg
      linarith
  refine ((M.policy_error hβ hσ''v s).2).trans ?_
  calc M.β / (1 - M.β) * sp (fun t => M.T (M.vσ hβ σ') t - M.vσ hβ σ' t)
      ≤ M.β / (1 - M.β) * (M.β * (ε * (1 - M.β) / M.β)) :=
        mul_le_mul_of_nonneg_left hres (div_nonneg M.β_nonneg hβ1.le)
    _ = M.β * ε := by field_simp
    _ ≤ ε := mul_le_of_le_one_left hε M.β_le_one

/-- **Relative policy iteration returns an `ε`-optimal policy after finitely many iterations**
(Bray, 2019a, Prop 4). -/
theorem relPI_bray (hβ : M.β < 1) (hβ0 : 0 < M.β) {ε : ℝ} (hε : 0 ≤ ε) (s₀ : S)
    {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (rel s₀ (M.vσ hβ (σ n)))) :
    ∃ N, (∀ s, |rel s₀ (M.vσ hβ (σ (N + 1))) s - rel s₀ (M.vσ hβ (σ N)) s| ≤
        ε * (1 - M.β) / (2 * M.β)) ∧
      ∀ σ'' : S → A, M.IsGreedy σ'' (rel s₀ (M.vσ hβ (σ (N + 1)))) →
        ∀ s, M.vstar hβ s - M.vσ hβ σ'' s ≤ ε := by
  obtain ⟨N, hN⟩ := M.relPI_terminates hβ s₀ h0 hstep
  have hstop : ∀ s, |rel s₀ (M.vσ hβ (σ (N + 1))) s - rel s₀ (M.vσ hβ (σ N)) s| ≤
      ε * (1 - M.β) / (2 * M.β) := fun s => by
    rw [hN (N + 1) (Nat.le_succ N), hN N le_rfl, sub_self, abs_zero]
    have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
    positivity
  exact ⟨N, hstop, fun σ'' hσ'' s => M.relPI_stopping hβ hβ0 s₀ (hstep N) hstop hσ'' s⟩

end MDP

namespace ExoMDP

variable {X Y A : Type*} [Fintype X] [Fintype Y] (E : ExoMDP X Y A)

/-- The exogenous chain with reward `m`, an MDP on `X` with a single action. -/
abbrev exoMDP (m : X → ℝ) : MDP X Unit where
  Γ _ := {()}
  Γ_nonempty _ := singleton_nonempty _
  r x _ := m x
  β := E.β
  β_nonneg := E.β_nonneg
  β_le_one := E.β_le_one
  P x _ x' := E.Fx x x'
  P_nonneg x _ x' := E.Fx_nonneg x x'
  P_sum x _ := E.Fx_sum x

/-- `c = m + βF_x c` has a solution when `β < 1`. -/
theorem exists_exo_solution (hβ : E.β < 1) (m : X → ℝ) :
    ∃ c : X → ℝ, ∀ x, c x = m x + E.β * E.Fxc c x := by
  refine ⟨(E.exoMDP m).vσ hβ fun _ => (), fun x => ?_⟩
  have h := congrFun ((E.exoMDP m).Tσ_vσ hβ fun _ => ()) x
  exact h.symm

/-- **Only the endogenous part of the Bellman residual matters**: a policy greedy for `w` is
within `β/(1 − β)·sp(Λ(Tw − w))` of optimal. -/
theorem policy_error_endo [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {w : X × Y → ℝ}
    {σ : X × Y → A} (hσ : E.toMDP.IsGreedy σ w) (s : X × Y) :
    E.toMDP.vstar hβ s - E.toMDP.vσ hβ σ s ≤
      E.β / (1 - E.β) * sp (endo fun t => E.toMDP.T w t - w t) := by
  obtain ⟨c, hc⟩ := E.exists_exo_solution hβ (mean fun t => E.toMDP.T w t - w t)
  have hσ' : E.toMDP.IsGreedy σ (fun t => w t + lift c t) :=
    (E.isGreedy_add_lift_iff σ w c).2 hσ
  have hres : (fun t => E.toMDP.T (fun t => w t + lift c t) t - (w t + lift c t)) =
      endo fun t => E.toMDP.T w t - w t := by
    rw [E.T_add_lift]
    funext t
    simp only [endo, lift]
    have := hc t.1
    linarith
  have h := (E.toMDP.policy_error hβ hσ' s).2
  rwa [hres] at h

/-- **Endogenous policy iteration is policy iteration**, and so terminates. -/
theorem endoPI_terminates [Nonempty Y] (hβ : E.β < 1) {σ : ℕ → X × Y → A}
    (h0 : E.toMDP.IsPolicy (σ 0))
    (hstep : ∀ n, E.toMDP.IsGreedy (σ (n + 1)) (endo (E.toMDP.vσ hβ (σ n)))) :
    ∃ N, ∀ n, N ≤ n → E.toMDP.vσ hβ (σ n) = E.toMDP.vstar hβ :=
  E.toMDP.pi_terminates hβ h0 fun n => (E.isGreedy_endo_iff _ _).1 (hstep n)

/-- Bray's stopping statistic `Λ(TΛv) − Λv` is the endogenous Bellman residual `Λ(Tv − v)`. -/
theorem endo_T_endo_sub [Nonempty Y] (v : X × Y → ℝ) :
    (fun s => endo (E.toMDP.T (endo v)) s - endo v s) = endo fun t => E.toMDP.T v t - v t := by
  have h := E.endoT_iterate v 1
  simp only [Function.iterate_one] at h
  rw [h, ← endo_sub]

/-- **Bray's stopping rule for endogenous policy iteration** (Bray, 2019b, Prop 3): if
`|Λ(TΛv_σ) − Λv_σ| ≤ ε(1 − β)/(2β)`, any policy greedy for `Λv_σ` is `ε`-optimal. -/
theorem endoPI_stopping [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (hβ0 : 0 < E.β) {ε : ℝ}
    {σ σ' : X × Y → A}
    (hstop : ∀ s, |endo (E.toMDP.T (endo (E.toMDP.vσ hβ σ))) s - endo (E.toMDP.vσ hβ σ) s| ≤
      ε * (1 - E.β) / (2 * E.β))
    (hσ' : E.toMDP.IsGreedy σ' (endo (E.toMDP.vσ hβ σ))) (s : X × Y) :
    E.toMDP.vstar hβ s - E.toMDP.vσ hβ σ' s ≤ ε := by
  have hβ1 : 0 < 1 - E.β := sub_pos.2 hβ
  have hstop' : ∀ s, |(endo fun t => E.toMDP.T (E.toMDP.vσ hβ σ) t - E.toMDP.vσ hβ σ t) s| ≤
      ε * (1 - E.β) / (2 * E.β) := fun s => by
    rw [← E.endo_T_endo_sub]
    exact hstop s
  have hsp : sp (endo fun t => E.toMDP.T (E.toMDP.vσ hβ σ) t - E.toMDP.vσ hβ σ t) ≤
      ε * (1 - E.β) / E.β := by
    refine sp_le fun x y => ?_
    have h1 := abs_le.1 (hstop' x)
    have h2 := abs_le.1 (hstop' y)
    have e : ε * (1 - E.β) / E.β = 2 * (ε * (1 - E.β) / (2 * E.β)) := by field_simp
    rw [e]
    linarith [h1.2, h2.1]
  refine (E.policy_error_endo hβ ((E.isGreedy_endo_iff _ _).1 hσ') s).trans ?_
  calc E.β / (1 - E.β) * sp (endo fun t => E.toMDP.T (E.toMDP.vσ hβ σ) t - E.toMDP.vσ hβ σ t)
      ≤ E.β / (1 - E.β) * (ε * (1 - E.β) / E.β) :=
        mul_le_mul_of_nonneg_left hsp (div_nonneg E.β_nonneg hβ1.le)
    _ = ε := by field_simp

/-- **Endogenous policy iteration returns an `ε`-optimal policy after finitely many iterations**
(Bray, 2019b, Prop 3). -/
theorem endoPI_bray [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (hβ0 : 0 < E.β) {ε : ℝ}
    (hε : 0 ≤ ε) {σ : ℕ → X × Y → A} (h0 : E.toMDP.IsPolicy (σ 0))
    (hstep : ∀ n, E.toMDP.IsGreedy (σ (n + 1)) (endo (E.toMDP.vσ hβ (σ n)))) :
    ∃ N, (∀ s, |endo (E.toMDP.T (endo (E.toMDP.vσ hβ (σ N)))) s -
        endo (E.toMDP.vσ hβ (σ N)) s| ≤ ε * (1 - E.β) / (2 * E.β)) ∧
      ∀ σ' : X × Y → A, E.toMDP.IsGreedy σ' (endo (E.toMDP.vσ hβ (σ N))) →
        ∀ s, E.toMDP.vstar hβ s - E.toMDP.vσ hβ σ' s ≤ ε := by
  obtain ⟨N, hN⟩ := E.endoPI_terminates hβ h0 hstep
  have hβ1 : 0 < 1 - E.β := sub_pos.2 hβ
  have hstop : ∀ s, |endo (E.toMDP.T (endo (E.toMDP.vσ hβ (σ N)))) s -
      endo (E.toMDP.vσ hβ (σ N)) s| ≤ ε * (1 - E.β) / (2 * E.β) := fun s => by
    have h := congrFun (E.endo_T_endo_sub (E.toMDP.vσ hβ (σ N))) s
    rw [h, hN N le_rfl, E.toMDP.T_vstar hβ]
    simp only [sub_self, endo, mean, sum_const_zero, zero_div, abs_zero]
    positivity
  exact ⟨N, hstop, fun σ' hσ' s => E.endoPI_stopping hβ hβ0 hstop hσ' s⟩

end ExoMDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix

The spectral radius `ρ(A)` of a real square matrix is the largest modulus of a complex eigenvalue
(`specRad`, `mem_spectrum_iff_eigenpair`). Gelfand's formula `‖Aᵏ‖^{1/k} → ρ(A)` for the ℓ∞
operator norm (`tendsto_norm_pow_rpow`) gives, for every `γ > ρ(A)`, a constant `C` with
`‖Aᵏ‖ ≤ Cγᵏ` for all `k` (`exists_norm_pow_le`); conversely `‖Aᵏ‖ ≤ Kαᵏ` for all `k` forces
`ρ(A) ≤ α` (`specRad_le_of_norm_pow_le`). Adapted from the `FiniteStates/ContinuousTime` project.
-/

open Filter Topology Matrix Finset

namespace DPExtensions.RelativeValueIteration

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ := A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) : complexify A i j = (A i j : ℂ) := rfl

theorem complexify_pow (A : Matrix X X ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := X)) A k

omit [DecidableEq X] in
theorem complexify_mul (A B : Matrix X X ℝ) : complexify (A * B) = complexify A * complexify B := by
  classical
  exact map_mul (Complex.ofRealHom.mapMatrix (m := X)) A B

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius: the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ := (spectralRadius ℂ (complexify A)).toReal

omit [DecidableEq X] in
theorem spectralRadius_complexify_ne_top [Nonempty X] (A : Matrix X X ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ := by
  classical
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

omit [Fintype X] [DecidableEq X] in
theorem specRad_nonneg [Fintype X] (A : Matrix X X ℝ) : 0 ≤ specRad A := ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues. -/
theorem mem_spectrum_iff_eigenpair (A : Matrix X X ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ e : X → ℂ, e ≠ 0 ∧ A *ᵥ e = μ • e := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
    exact h.symm

/-- **Gelfand's formula** for real matrices: `‖Aᵏ‖^{1/k} → ρ(A)`. -/
theorem tendsto_norm_pow_rpow [Nonempty X] (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`. -/
theorem eventually_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- For every `γ > ρ(A)` there is `C` with `‖Aᵏ‖ ≤ Cγᵏ` for all `k`. -/
theorem exists_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {γ : ℝ} (hγ : specRad A < γ) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k := by
  have hγ0 : 0 < γ := (specRad_nonneg A).trans_lt hγ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_norm_pow_le A hγ)
  refine ⟨1 + ∑ k ∈ range N, ‖A ^ k‖ / γ ^ k, by positivity, fun k => ?_⟩
  rcases lt_or_ge k N with hk | hk
  · have h1 : ‖A ^ k‖ / γ ^ k ≤ ∑ j ∈ range N, ‖A ^ j‖ / γ ^ j :=
      single_le_sum (f := fun j => ‖A ^ j‖ / γ ^ j) (fun j _ => by positivity) (mem_range.2 hk)
    have h2 : ‖A ^ k‖ = ‖A ^ k‖ / γ ^ k * γ ^ k := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h3 := hN k hk
    have h4 : 0 ≤ ∑ j ∈ range N, ‖A ^ j‖ / γ ^ j := sum_nonneg fun j _ => by positivity
    nlinarith [pow_pos hγ0 k]

/-- If `‖Aᵏ‖ ≤ Kαᵏ` for all `k`, then `ρ(A) ≤ α`. -/
theorem specRad_le_of_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {K α : ℝ} (hK : 0 < K)
    (hα : 0 ≤ α) (h : ∀ k : ℕ, ‖A ^ k‖ ≤ K * α ^ k) : specRad A ≤ α := by
  have hK1 : Tendsto (fun k : ℕ => K ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ => 1 / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := K)).rpow h0 (Or.inl hK.ne')
    rwa [Real.rpow_zero] at this
  have hup : Tendsto (fun k : ℕ => K ^ (1 / (k : ℝ)) * α) atTop (𝓝 α) := by
    simpa using hK1.mul_const α
  refine le_of_tendsto_of_tendsto (tendsto_norm_pow_rpow A) hup ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  calc ‖A ^ k‖ ^ (1 / (k : ℝ)) ≤ (K * α ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) (h k) (by positivity)
    _ = K ^ (1 / (k : ℝ)) * α := by
        rw [Real.mul_rpow hK.le (pow_nonneg hα k), ← Real.rpow_natCast,
          ← Real.rpow_mul hα, mul_one_div_cancel hk'.ne', Real.rpow_one]

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral subradius of a stochastic matrix

Morton and Wecker (1977); Bray (2019a), the quantity `λ(Q)` ("second-largest eigenvalue
modulus") that governs the asymptotic speed of relative value iteration.

Let `Δ` subtract the value at a reference state, `(Δv)(s) = v(s) − v(s₀)` (`deltaMat`), and let
`Q` be a stochastic matrix. The **subradius** is `λ(Q) = ρ(ΔQ)` (`subradius`).

* `mem_spectrum_deltaQ_iff`: the nonzero eigenvalues of `ΔQ` are exactly the eigenvalues of `Q`
  other than `1`, together with `1` itself iff `Q` has a non-constant fixed vector. A stochastic
  matrix has no Jordan block at `1`, which the proof uses.
* `spectralRadius_deltaQ`: hence, when the only fixed vectors of `Q` are the constants (one
  closed class), `λ(Q) = max{|μ| : μ an eigenvalue of Q, μ ≠ 1}` — Bray's second-largest
  eigenvalue modulus.
* `sp_pow_mulVec_le`: for every `γ > λ(Q)` there is `C` with `sp(Qᵏd) ≤ Cγᵏ sp(d)`.
* `subradius_le_dobrushin`: `λ(Q)` is at most any bound on the Dobrushin coefficient.
-/

open Filter Topology Matrix Finset

namespace DPExtensions.RelativeValueIteration

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The differencing matrix `Δ`: `(Δv)(s) = v(s) − v(s₀)`. -/
def deltaMat (s₀ : S) : Matrix S S ℝ :=
  fun i j => (if i = j then 1 else 0) - (if j = s₀ then 1 else 0)

/-- A stochastic matrix. -/
def IsStochastic (Q : Matrix S S ℝ) : Prop := (∀ i j, 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j = 1

/-- The spectral subradius `λ(Q) = ρ(ΔQ)`. -/
noncomputable def subradius (Q : Matrix S S ℝ) (s₀ : S) : ℝ := specRad (deltaMat s₀ * Q)

theorem deltaMat_mulVec (s₀ : S) (v : S → ℝ) : deltaMat s₀ *ᵥ v = fun s => v s - v s₀ := by
  funext s
  simp [deltaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul]

theorem cdelta_mulVec (s₀ : S) (w : S → ℂ) :
    complexify (deltaMat s₀) *ᵥ w = fun s => w s - w s₀ := by
  funext s
  simp [complexify, deltaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul,
    apply_ite (Complex.ofReal)]

omit [DecidableEq S] in
theorem mulVec_const {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (c : ℝ) :
    Q *ᵥ (fun _ => c) = fun _ => c := by
  funext s
  simp only [mulVec, dotProduct, ← sum_mul, hQ.2 s, one_mul]

omit [DecidableEq S] in
theorem cmulVec_const {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (c : ℂ) :
    complexify Q *ᵥ (fun _ => c) = fun _ => c := by
  funext s
  have h : ∑ j, (Q s j : ℂ) = 1 := by exact_mod_cast hQ.2 s
  simp only [mulVec, dotProduct, complexify_apply, ← sum_mul, h, one_mul]

omit [DecidableEq S] in
theorem norm_cmulVec_le {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (w : S → ℂ) :
    ‖complexify Q *ᵥ w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun s => ?_
  simp only [mulVec, dotProduct, complexify_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖(Q s j : ℂ) * w j‖ ≤ ∑ j, Q s j * ‖w‖ := sum_le_sum fun j _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hQ.1 s j)]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (hQ.1 s j)
    _ = ‖w‖ := by rw [← sum_mul, hQ.2 s, one_mul]

omit [DecidableEq S] in
/-- A stochastic matrix has no Jordan block at `1`: `Qv = v + c` with `v(s₀) = 0` forces
`c = 0`. -/
theorem no_jordan_one {Q : Matrix S S ℝ} (hQ : IsStochastic Q) {v : S → ℂ} {c : ℂ} (s₀ : S)
    (hv0 : v s₀ = 0) (hv : complexify Q *ᵥ v = fun s => v s + c) : c = 0 := by
  classical
  have hconst : ∀ k : ℕ, (complexify Q ^ k) *ᵥ (fun _ => c) = fun _ => c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, cmulVec_const hQ, ih]
  have hpow : ∀ k : ℕ, (complexify Q ^ k) *ᵥ v = fun s => v s + k * c := by
    intro k
    induction k with
    | zero => funext s; simp
    | succ k ih =>
      rw [pow_succ, ← mulVec_mulVec, hv,
        show (fun s => v s + c) = v + fun _ => c from rfl, mulVec_add, ih, hconst]
      funext s
      simp only [Pi.add_apply]
      push_cast
      ring
  have hb : ∀ k : ℕ, ‖(k : ℂ) * c‖ ≤ ‖v‖ := by
    intro k
    have h1 : ‖(complexify Q ^ k) *ᵥ v‖ ≤ ‖v‖ := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← mulVec_mulVec]
        exact (norm_cmulVec_le hQ _).trans ih
    have h2 := (norm_le_pi_norm ((complexify Q ^ k) *ᵥ v) s₀).trans h1
    simp only [hpow, hv0, zero_add] at h2
    exact h2
  by_contra hc
  obtain ⟨k, hk⟩ := exists_nat_gt (‖v‖ / ‖c‖)
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  have := hb k
  rw [norm_mul, Complex.norm_natCast] at this
  rw [div_lt_iff₀ hc'] at hk
  linarith

theorem complexify_deltaQ_mulVec (Q : Matrix S S ℝ) (s₀ : S) (w : S → ℂ) :
    complexify (deltaMat s₀ * Q) *ᵥ w =
      fun s => (complexify Q *ᵥ w) s - (complexify Q *ᵥ w) s₀ := by
  rw [complexify_mul, ← mulVec_mulVec, cdelta_mulVec]

/-- **The eigenvalues of `ΔQ`**: for `μ ≠ 0`, `μ` is an eigenvalue of `ΔQ` iff it is an
eigenvalue of `Q` other than `1`, or `μ = 1` and `Q` has a non-constant fixed vector. -/
theorem mem_spectrum_deltaQ_iff {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S) {μ : ℂ}
    (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ (complexify (deltaMat s₀ * Q)) ↔
      (μ ∈ spectrum ℂ (complexify Q) ∧ μ ≠ 1) ∨
        (μ = 1 ∧ ∃ v : S → ℂ, complexify Q *ᵥ v = v ∧ ∃ i j, v i ≠ v j) := by
  rw [mem_spectrum_iff_eigenpair, mem_spectrum_iff_eigenpair]
  constructor
  · rintro ⟨e, he, h⟩
    rw [complexify_deltaQ_mulVec] at h
    set w := complexify Q *ᵥ e with hw
    have hs : ∀ s, w s - w s₀ = μ * e s := fun s => by
      have := congrFun h s
      simpa using this
    have he0 : e s₀ = 0 := by
      have := hs s₀
      rw [sub_self] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hμ
    set c := w s₀
    have hwe : w = fun s => μ * e s + c := funext fun s => by linear_combination hs s
    by_cases h1 : μ = 1
    · subst h1
      have hc : c = 0 := no_jordan_one hQ s₀ he0 (by rw [← hw, hwe]; funext s; simp)
      refine Or.inr ⟨rfl, e, ?_, ?_⟩
      · rw [← hw, hwe, hc]
        funext s
        simp
      · obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
          by_contra hall
          push Not at hall
          exact he (funext hall)
        exact ⟨s, s₀, by rw [he0]; exact hs'⟩
    · refine Or.inl ⟨⟨fun s => e s + c / (μ - 1), ?_, ?_⟩, h1⟩
      · intro hu
        have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.2 h1
        have h2 := congrFun hu s₀
        simp only [he0, zero_add, Pi.zero_apply, div_eq_zero_iff, hμ1, or_false] at h2
        apply he
        funext s
        have h3 := congrFun hu s
        simp only [h2, zero_div, add_zero, Pi.zero_apply] at h3
        exact h3
      · have e1 : (fun s => e s + c / (μ - 1)) = e + fun _ => c / (μ - 1) := rfl
        rw [e1, mulVec_add, cmulVec_const hQ, ← hw, hwe]
        funext s
        have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.2 h1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
  · rintro (⟨⟨u, hu, h⟩, h1⟩ | ⟨rfl, v, hv, i, j, hij⟩)
    · refine ⟨fun s => u s - u s₀, fun hz => hu ?_, ?_⟩
      · -- `u` would be constant, hence a fixed vector, forcing `μ = 1`
        have hc : u = fun _ => u s₀ := funext fun s => by
          have := congrFun hz s
          simpa [sub_eq_zero] using this
        have hfix := cmulVec_const hQ (u s₀)
        rw [← hc, h] at hfix
        by_contra hne
        have hu0 : u s₀ ≠ 0 := by
          intro h0
          apply hne
          rw [hc, h0]
          rfl
        have := congrFun hfix s₀
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact h1 (mul_right_cancel₀ hu0 (this.trans (one_mul _).symm))
      · rw [complexify_deltaQ_mulVec]
        have e1 : (fun s => u s - u s₀) = u + fun _ => -u s₀ := by
          funext s
          simp [sub_eq_add_neg]
        rw [e1, mulVec_add, cmulVec_const hQ, h]
        funext s
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · refine ⟨fun s => v s - v s₀, fun hz => hij ?_, ?_⟩
      · have hi := congrFun hz i
        have hj := congrFun hz j
        simp only [Pi.zero_apply, sub_eq_zero] at hi hj
        rw [hi, hj]
      · rw [complexify_deltaQ_mulVec]
        have e1 : (fun s => v s - v s₀) = v + fun _ => -v s₀ := by
          funext s
          simp [sub_eq_add_neg]
        rw [e1, mulVec_add, cmulVec_const hQ, hv]
        funext s
        simp only [Pi.add_apply, one_smul]
        ring

/-- **The subradius is the second-largest eigenvalue modulus**: when the only fixed vectors of
`Q` are the constants, `ρ(ΔQ) = sup{|μ| : μ an eigenvalue of Q, μ ≠ 1}`. -/
theorem spectralRadius_deltaQ {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    (hfix : ∀ v : S → ℂ, complexify Q *ᵥ v = v → ∀ i j, v i = v j) :
    spectralRadius ℂ (complexify (deltaMat s₀ * Q)) =
      ⨆ μ ∈ spectrum ℂ (complexify Q), ⨆ (_ : μ ≠ 1), (‖μ‖₊ : ENNReal) := by
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => iSup_le fun h1 => ?_)
  · rcases eq_or_ne μ 0 with h0 | h0
    · simp [h0]
    · rcases (mem_spectrum_deltaQ_iff hQ s₀ h0).1 hμ with ⟨hs, h1⟩ | ⟨rfl, v, hv, i, j, hij⟩
      · exact le_iSup₂_of_le μ hs (le_iSup_of_le h1 le_rfl)
      · exact absurd (hfix v hv i j) hij
  · rcases eq_or_ne μ 0 with h0 | h0
    · simp [h0]
    · exact le_iSup₂_of_le μ ((mem_spectrum_deltaQ_iff hQ s₀ h0).2 (Or.inl ⟨hμ, h1⟩)) le_rfl

theorem sp_deltaMat_mulVec [Nonempty S] (s₀ : S) (v : S → ℝ) :
    sp (deltaMat s₀ *ᵥ v) = sp v := by
  rw [deltaMat_mulVec]
  have := sp_add_const v (-v s₀)
  simpa [sub_eq_add_neg] using this

theorem norm_deltaMat_mulVec_le [Nonempty S] (s₀ : S) (v : S → ℝ) :
    ‖deltaMat s₀ *ᵥ v‖ ≤ sp v :=
  (pi_norm_le_iff_of_nonneg (sp_nonneg v)).2 fun s => by
    rw [deltaMat_mulVec, Real.norm_eq_abs]
    exact abs_sub_le_sp v s s₀

omit [DecidableEq S] in
theorem sp_le_two_norm [Nonempty S] (v : S → ℝ) : sp v ≤ 2 * ‖v‖ :=
  sp_le fun x y => by
    have h1 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm v x)
    have h2 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm v y)
    linarith [h1.2, h2.1]

theorem deltaQ_pow_mulVec {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S) (v : S → ℝ)
    (k : ℕ) : (deltaMat s₀ * Q) ^ k *ᵥ (deltaMat s₀ *ᵥ v) = deltaMat s₀ *ᵥ (Q ^ k *ᵥ v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec]
    have e : Q *ᵥ (deltaMat s₀ *ᵥ v) = Q *ᵥ v + fun _ => -v s₀ := by
      rw [deltaMat_mulVec, show (fun s => v s - v s₀) = v + fun _ => -v s₀ by
        funext s; simp [sub_eq_add_neg], mulVec_add, mulVec_const hQ]
    rw [e, mulVec_add, deltaMat_mulVec (s₀ := s₀) (fun _ => -v s₀)]
    have e2 : deltaMat s₀ *ᵥ (Q *ᵥ v) + (fun s => (fun _ : S => -v s₀) s - -v s₀) =
        deltaMat s₀ *ᵥ (Q *ᵥ v) := by
      funext s
      simp
    rw [e2, ih, pow_succ, ← mulVec_mulVec]

/-- **The subradius governs the span**: for every `γ > λ(Q)` there is `C` with
`sp(Qᵏd) ≤ Cγᵏ sp(d)` for all `k`. -/
theorem sp_pow_mulVec_le [Nonempty S] {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    {γ : ℝ} (hγ : subradius Q s₀ < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (d : S → ℝ), sp (Q ^ k *ᵥ d) ≤ C * γ ^ k * sp d := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le (deltaMat s₀ * Q) hγ
  have hγ0 : 0 < γ := (specRad_nonneg _).trans_lt hγ
  refine ⟨2 * C, by positivity, fun k d => ?_⟩
  calc sp (Q ^ k *ᵥ d) = sp (deltaMat s₀ *ᵥ (Q ^ k *ᵥ d)) := (sp_deltaMat_mulVec s₀ _).symm
    _ ≤ 2 * ‖deltaMat s₀ *ᵥ (Q ^ k *ᵥ d)‖ := sp_le_two_norm _
    _ = 2 * ‖(deltaMat s₀ * Q) ^ k *ᵥ (deltaMat s₀ *ᵥ d)‖ := by rw [deltaQ_pow_mulVec hQ]
    _ ≤ 2 * (‖(deltaMat s₀ * Q) ^ k‖ * ‖deltaMat s₀ *ᵥ d‖) :=
        mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) zero_le_two
    _ ≤ 2 * (C * γ ^ k * sp d) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul (hC k) (norm_deltaMat_mulVec_le s₀ d) (norm_nonneg _) (by positivity)
    _ = 2 * C * γ ^ k * sp d := by ring

/-- **The subradius is at most the Dobrushin coefficient.** -/
theorem subradius_le_dobrushin [Nonempty S] {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    {α : ℝ} (hα : ∀ i j, 1 - ∑ t, min (Q i t) (Q j t) ≤ α) : subradius Q s₀ ≤ α := by
  have hα0 : 0 ≤ α := by
    have h := hα s₀ s₀
    simp only [min_self, hQ.2 s₀, sub_self] at h
    exact h
  have hstep : ∀ d : S → ℝ, sp (Q *ᵥ d) ≤ α * sp d := fun d =>
    sp_le fun i j => by
      have h := dobrushin (hQ.2 i) (hQ.2 j) d
      have hs := mul_le_mul_of_nonneg_right (hα i j) (sp_nonneg d)
      simp only [mulVec, dotProduct]
      linarith
  have hpow : ∀ (k : ℕ) (d : S → ℝ), sp (Q ^ k *ᵥ d) ≤ α ^ k * sp d := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
      intro d
      rw [pow_succ', ← mulVec_mulVec, pow_succ']
      calc sp (Q *ᵥ (Q ^ k *ᵥ d)) ≤ α * sp (Q ^ k *ᵥ d) := hstep _
        _ ≤ α * (α ^ k * sp d) := mul_le_mul_of_nonneg_left (ih d) hα0
        _ = α * α ^ k * sp d := by ring
  refine specRad_le_of_norm_pow_le _ zero_lt_two hα0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(deltaMat s₀ * Q) ^ k *ᵥ w‖ ≤ 2 * α ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    linarith [norm_nonneg w]
  -- `(ΔQ)ᵏ⁺¹ w = (ΔQ)ᵏ⁺¹ Δw`, since `ΔQ` kills constants
  have hconst : (deltaMat s₀ * Q) *ᵥ (fun _ => w s₀) = 0 := by
    rw [← mulVec_mulVec, mulVec_const hQ, deltaMat_mulVec]
    funext s
    simp
  have e : (deltaMat s₀ * Q) ^ (k + 1) *ᵥ w =
      (deltaMat s₀ * Q) ^ (k + 1) *ᵥ (deltaMat s₀ *ᵥ w) := by
    have hw : w = deltaMat s₀ *ᵥ w + fun _ => w s₀ := by
      rw [deltaMat_mulVec]
      funext s
      simp
    have h2 : (deltaMat s₀ * Q) ^ (k + 1) *ᵥ (fun _ => w s₀) = 0 := by
      rw [pow_succ, ← mulVec_mulVec, hconst, mulVec_zero]
    conv_lhs => rw [hw]
    rw [mulVec_add, h2, add_zero]
  rw [e, deltaQ_pow_mulVec hQ]
  calc ‖deltaMat s₀ *ᵥ (Q ^ (k + 1) *ᵥ w)‖ ≤ sp (Q ^ (k + 1) *ᵥ w) :=
        norm_deltaMat_mulVec_le s₀ _
    _ ≤ α ^ (k + 1) * sp w := hpow _ w
    _ ≤ α ^ (k + 1) * (2 * ‖w‖) := mul_le_mul_of_nonneg_left (sp_le_two_norm w) (by positivity)
    _ = 2 * α ^ (k + 1) * ‖w‖ := by ring

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asymptotic rates: relative value iteration converges at rate `βλ(Q*)`

Morton (1971); Morton and Wecker (1977); Bray (2019a), Propositions 3 and 5.

Let `P_σ` be the transition matrix of a decision rule and `λ(P_σ)` its subradius (the
second-largest eigenvalue modulus, `spectralRadius_deltaQ`).

* `sp_policy_eval_le` (**Morton; Bray, Prop 5**): policy evaluation `T_σⁿv → v_σ` converges in
  span at rate `βγ` for every `γ > λ(P_σ)`: `sp(T_σⁿv − v_σ) ≤ C(βγ)ⁿ sp(v − v_σ)`.
* `eventually_T_eq_Tσ`: if the optimal decision rule `σ*` is unique and strict, the greedy policy
  freezes: after finitely many steps value iteration is `T_{σ*}`-iteration.
* `relative_asymptotic_rate` (**Morton–Wecker; Bray, Prop 3**): then for every `γ > λ(P_{σ*})`
  there are `C` and `N` with `sp(T^{N+k}v − v*) ≤ C(βγ)ᵏ`, so the relative values converge at
  rate `βλ(P_{σ*})` (`rel_asymptotic_rate`).
* `level_rate_lower` (**standard value iteration is no faster than `β`**): if `ψ` is a stationary
  distribution of `P_{σ*}`, `‖T^{N+k}v − v*‖ ≥ βᵏ|ψ·(T^Nv − v*)|`.
* `subradius_policy_le`: `λ(P_σ)` is at most any Dobrushin bound `α`, so the asymptotic rate is
  never worse than the non-asymptotic rate `βα` of `sp_iterate_sub_vstar`.
-/

open Filter Topology Matrix Finset

namespace DPExtensions.RelativeValueIteration

theorem sp_mul_le {S : Type*} [Fintype S] [Nonempty S] {c : ℝ} (hc : 0 ≤ c) (w : S → ℝ) :
    sp (fun s => c * w s) ≤ c * sp w :=
  sp_le fun x y => by
    have := mul_le_mul_of_nonneg_left (sub_le_sp w x y) hc
    linarith [mul_sub c (w x) (w y)]

namespace MDP

variable {S A : Type*} [Fintype S] [DecidableEq S] (M : MDP S A)

/-- The transition matrix of the decision rule `σ`. -/
def Pmat (σ : S → A) : Matrix S S ℝ := fun s t => M.P s (σ s) t

omit [DecidableEq S] in
theorem Pmat_isStochastic (σ : S → A) : IsStochastic (M.Pmat σ) :=
  ⟨fun s t => M.P_nonneg s (σ s) t, fun s => M.P_sum s (σ s)⟩

omit [DecidableEq S] in
theorem Tσ_sub (σ : S → A) (v w : S → ℝ) :
    (fun s => M.Tσ σ v s - M.Tσ σ w s) = fun s => M.β * (M.Pmat σ *ᵥ (v - w)) s := by
  funext s
  simp only [Tσ, M.Q_sub_Q, Pmat, mulVec, dotProduct, Pi.sub_apply]

theorem Tσ_iterate_sub (σ : S → A) (v w : S → ℝ) (n : ℕ) :
    (fun s => (M.Tσ σ)^[n] v s - (M.Tσ σ)^[n] w s) =
      fun s => M.β ^ n * (M.Pmat σ ^ n *ᵥ (v - w)) s := by
  induction n with
  | zero => funext s; simp
  | succ n ih =>
    funext s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := congrFun (M.Tσ_sub σ ((M.Tσ σ)^[n] v) ((M.Tσ σ)^[n] w)) s
    rw [h]
    have e : (M.Tσ σ)^[n] v - (M.Tσ σ)^[n] w = M.β ^ n • (M.Pmat σ ^ n *ᵥ (v - w)) := by
      funext t
      exact congrFun ih t
    rw [e, mulVec_smul, mulVec_mulVec, ← pow_succ']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- **Policy evaluation converges at rate `βλ(P_σ)`** (Morton, 1971; Bray, Prop 5). -/
theorem sp_policy_eval_le [Nonempty S] (hβ : M.β < 1) (σ : S → A) (s₀ : S) {γ : ℝ}
    (hγ : subradius (M.Pmat σ) s₀ < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (v : S → ℝ),
      sp (fun s => (M.Tσ σ)^[n] v s - M.vσ hβ σ s) ≤
        C * (M.β * γ) ^ n * sp (fun s => v s - M.vσ hβ σ s) := by
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le (M.Pmat_isStochastic σ) s₀ hγ
  refine ⟨C, hC0, fun n v => ?_⟩
  have hfix : (M.Tσ σ)^[n] (M.vσ hβ σ) = M.vσ hβ σ := Function.iterate_fixed (M.Tσ_vσ hβ σ) n
  have e := M.Tσ_iterate_sub σ v (M.vσ hβ σ) n
  rw [hfix] at e
  rw [e]
  calc sp (fun s => M.β ^ n * (M.Pmat σ ^ n *ᵥ (v - M.vσ hβ σ)) s)
      ≤ M.β ^ n * sp (M.Pmat σ ^ n *ᵥ (v - M.vσ hβ σ)) :=
        sp_mul_le (pow_nonneg M.β_nonneg n) _
    _ ≤ M.β ^ n * (C * γ ^ n * sp (v - M.vσ hβ σ)) :=
        mul_le_mul_of_nonneg_left (hC n _) (pow_nonneg M.β_nonneg n)
    _ = C * (M.β * γ) ^ n * sp (fun s => v s - M.vσ hβ σ s) := by
        rw [mul_pow]
        change _ = C * (M.β ^ n * γ ^ n) * sp (v - M.vσ hβ σ)
        ring

omit [DecidableEq S] in
/-- **The greedy policy freezes** at a unique, strict optimal decision rule `σ*`: near `v*`,
`T = T_{σ*}`. -/
theorem eventually_T_eq_Tσ (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s)) :
    ∃ ρ > 0, ∀ w : S → ℝ, ‖w - M.vstar hβ‖ < ρ → M.T w = M.Tσ σs w := by
  classical
  set vs := M.vstar hβ
  set G : Finset (S × A) := univ.biUnion fun s => ((M.Γ s).filter fun a => a ≠ σs s).image
    fun a => (s, a)
  have hG : ∀ s, ∀ a ∈ M.Γ s, a ≠ σs s → (s, a) ∈ G := fun s a ha hne => by
    simp only [G, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
    exact ⟨s, a, ⟨ha, hne⟩, rfl⟩
  have hGgap : ∀ p ∈ G, 0 < M.Q vs p.1 (σs p.1) - M.Q vs p.1 p.2 := fun p hp => by
    simp only [G, mem_biUnion, mem_univ, true_and, mem_image, mem_filter] at hp
    obtain ⟨s, a, ⟨ha, hne⟩, rfl⟩ := hp
    exact sub_pos.2 ((hstrict s).2 a ha hne)
  obtain ⟨g, hg, hgap⟩ : ∃ g > 0, ∀ p ∈ G, g ≤ M.Q vs p.1 (σs p.1) - M.Q vs p.1 p.2 := by
    rcases G.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, fun p hp => by rw [hE] at hp; exact absurd hp (notMem_empty p)⟩
    · obtain ⟨p0, hp0, hmin⟩ := exists_min_image G
        (fun p => M.Q vs p.1 (σs p.1) - M.Q vs p.1 p.2) hne
      exact ⟨_, hGgap p0 hp0, hmin⟩
  have hβ0 := M.β_nonneg
  refine ⟨g / (2 * M.β + 1), div_pos hg (by linarith), fun w hw => ?_⟩
  have h2β : 2 * M.β * ‖w - vs‖ < g := by
    rw [lt_div_iff₀ (by linarith)] at hw
    nlinarith [norm_nonneg (w - vs)]
  funext s
  refine le_antisymm (sup'_le _ _ fun a ha => ?_) (M.Q_le_T w (hstrict s).1)
  by_cases hne : a = σs s
  · rw [hne]
    rfl
  · have h1 := abs_le.1 (M.abs_Q_sub_le w vs s a)
    have h2 := abs_le.1 (M.abs_Q_sub_le w vs s (σs s))
    have h3 := hgap (s, a) (hG s a ha hne)
    simp only at h3
    change M.Q w s a ≤ M.Q w s (σs s)
    linarith

omit [DecidableEq S] in
theorem norm_iterate_sub_vstar_le (hβ : M.β < 1) (v : S → ℝ) (n : ℕ) :
    ‖M.T^[n] v - M.vstar hβ‖ ≤ M.β ^ n * ‖v - M.vstar hβ‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    conv_lhs => rw [← M.T_vstar hβ]
    refine (M.norm_T_sub_le _ _).trans ?_
    rw [pow_succ']
    nlinarith [M.β_nonneg]

/-- After the greedy policy has frozen at `σ*`, the value-iteration error evolves linearly:
`T^{N+k}v − v* = βᵏP_{σ*}ᵏ(T^Nv − v*)`. -/
theorem eventually_linear (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s)) (v : S → ℝ) :
    ∃ N, ∀ k, M.T^[N + k] v - M.vstar hβ =
      M.β ^ k • (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) := by
  obtain ⟨ρ, hρ, hfreeze⟩ := M.eventually_T_eq_Tσ hβ hstrict
  have hlim : Tendsto (fun n : ℕ => M.β ^ n * ‖v - M.vstar hβ‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg hβ).mul_const
      ‖v - M.vstar hβ‖
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hρ))
  have hnear : ∀ n, N ≤ n → ‖M.T^[n] v - M.vstar hβ‖ < ρ := fun n hn =>
    (M.norm_iterate_sub_vstar_le hβ v n).trans_lt (hN n hn)
  have hstar : M.T (M.vstar hβ) = M.Tσ σs (M.vstar hβ) :=
    hfreeze _ (by rw [sub_self, norm_zero]; exact hρ)
  refine ⟨N, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Function.iterate_succ_apply', hfreeze _ (hnear _ (by omega))]
    conv_lhs => rw [← M.T_vstar hβ, hstar]
    have e := M.Tσ_sub σs (M.T^[N + k] v) (M.vstar hβ)
    funext s
    have := congrFun e s
    simp only [Pi.sub_apply]
    rw [this, ih, mulVec_smul, mulVec_mulVec, ← pow_succ']
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- **Relative value iteration converges at rate `βλ(P_{σ*})`** (Morton and Wecker, 1977;
Bray, Prop 3): with a unique, strict optimal decision rule `σ*`, for every `γ > λ(P_{σ*})`
there are `C` and `N` with `sp(T^{N+k}v − v*) ≤ C(βγ)ᵏ`. -/
theorem relative_asymptotic_rate [Nonempty S] (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s))
    (s₀ : S) {γ : ℝ} (hγ : subradius (M.Pmat σs) s₀ < γ) (v : S → ℝ) :
    ∃ C N, ∀ k, sp (fun s => M.T^[N + k] v s - M.vstar hβ s) ≤ C * (M.β * γ) ^ k := by
  obtain ⟨N, hN⟩ := M.eventually_linear hβ hstrict v
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le (M.Pmat_isStochastic σs) s₀ hγ
  refine ⟨C * sp (M.T^[N] v - M.vstar hβ), N, fun k => ?_⟩
  have e : (fun s => M.T^[N + k] v s - M.vstar hβ s) =
      fun s => M.β ^ k * (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) s := by
    funext s
    have := congrFun (hN k) s
    simpa using this
  rw [e]
  calc sp (fun s => M.β ^ k * (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) s)
      ≤ M.β ^ k * sp (M.Pmat σs ^ k *ᵥ (M.T^[N] v - M.vstar hβ)) :=
        sp_mul_le (pow_nonneg M.β_nonneg k) _
    _ ≤ M.β ^ k * (C * γ ^ k * sp (M.T^[N] v - M.vstar hβ)) :=
        mul_le_mul_of_nonneg_left (hC k _) (pow_nonneg M.β_nonneg k)
    _ = C * sp (M.T^[N] v - M.vstar hβ) * (M.β * γ) ^ k := by rw [mul_pow]; ring

/-- The relative values converge at rate `βλ(P_{σ*})`. -/
theorem rel_asymptotic_rate [Nonempty S] (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s))
    (s₀ : S) {γ : ℝ} (hγ : subradius (M.Pmat σs) s₀ < γ) (v : S → ℝ) :
    ∃ C N, ∀ k s, |rel s₀ (M.T^[N + k] v) s - rel s₀ (M.vstar hβ) s| ≤ C * (M.β * γ) ^ k := by
  obtain ⟨C, N, h⟩ := M.relative_asymptotic_rate hβ hstrict s₀ hγ v
  refine ⟨C, N, fun k s => le_trans ?_ (h k)⟩
  have := abs_sub_le_sp (fun s => M.T^[N + k] v s - M.vstar hβ s) s s₀
  simp only [rel]
  convert this using 2
  ring

omit [DecidableEq S] in
/-- **Standard value iteration converges no faster than `β`**: for a stationary distribution `ψ`
of `P_{σ*}`, `‖T^{N+k}v − v*‖ ≥ βᵏ|ψ·(T^Nv − v*)|`. -/
theorem level_rate_lower (hβ : M.β < 1) {σs : S → A}
    (hstrict : ∀ s, σs s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, a ≠ σs s →
      M.Q (M.vstar hβ) s a < M.Q (M.vstar hβ) s (σs s))
    {ψ : S → ℝ} (hψ0 : ∀ s, 0 ≤ ψ s) (hψ1 : ∑ s, ψ s = 1)
    (hψs : ∀ t, ∑ s, ψ s * M.Pmat σs s t = ψ t) (v : S → ℝ) :
    ∃ N, ∀ k, M.β ^ k * |∑ s, ψ s * (M.T^[N] v - M.vstar hβ) s| ≤
      ‖M.T^[N + k] v - M.vstar hβ‖ := by
  classical
  obtain ⟨N, hN⟩ := M.eventually_linear hβ hstrict v
  refine ⟨N, fun k => ?_⟩
  set d := M.T^[N] v - M.vstar hβ
  have hstat : ∀ (j : ℕ) (w : S → ℝ), ∑ s, ψ s * (M.Pmat σs ^ j *ᵥ w) s = ∑ s, ψ s * w s := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', ← mulVec_mulVec]
      have : ∀ u : S → ℝ, ∑ s, ψ s * (M.Pmat σs *ᵥ u) s = ∑ t, ψ t * u t := fun u => by
        calc ∑ s, ψ s * (M.Pmat σs *ᵥ u) s = ∑ s, ∑ t, ψ s * M.Pmat σs s t * u t := by
              simp only [mulVec, dotProduct, mul_sum]
              exact sum_congr rfl fun s _ => sum_congr rfl fun t _ => by ring
          _ = ∑ t, (∑ s, ψ s * M.Pmat σs s t) * u t := by
              rw [sum_comm]
              exact sum_congr rfl fun t _ => by rw [sum_mul]
          _ = ∑ t, ψ t * u t := by simp only [hψs]
      rw [this, ih]
  have e : ∑ s, ψ s * (M.T^[N + k] v - M.vstar hβ) s = M.β ^ k * ∑ s, ψ s * d s := by
    rw [hN k]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ s, ψ s * (M.β ^ k * (M.Pmat σs ^ k *ᵥ d) s) =
      M.β ^ k * ∑ s, ψ s * (M.Pmat σs ^ k *ᵥ d) s by
        rw [mul_sum]; exact sum_congr rfl fun s _ => by ring, hstat]
  have hbound : |∑ s, ψ s * (M.T^[N + k] v - M.vstar hβ) s| ≤ ‖M.T^[N + k] v - M.vstar hβ‖ := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |ψ s * (M.T^[N + k] v - M.vstar hβ) s|
        ≤ ∑ s, ψ s * ‖M.T^[N + k] v - M.vstar hβ‖ := sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (hψ0 s)]
          refine mul_le_mul_of_nonneg_left ?_ (hψ0 s)
          have := norm_le_pi_norm (M.T^[N + k] v - M.vstar hβ) s
          rwa [Real.norm_eq_abs] at this
      _ = ‖M.T^[N + k] v - M.vstar hβ‖ := by rw [← sum_mul, hψ1, one_mul]
  rw [e, abs_mul, abs_of_nonneg (pow_nonneg M.β_nonneg k)] at hbound
  exact hbound

/-- **The asymptotic rate is never worse than the Dobrushin rate**: `λ(P_σ) ≤ α`. -/
theorem subradius_policy_le [Nonempty S] {σ : S → A} (hσ : M.IsPolicy σ) (s₀ : S) {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α) :
    subradius (M.Pmat σ) s₀ ≤ α :=
  subradius_le_dobrushin (M.Pmat_isStochastic σ) s₀ fun i j => hα i (σ i) j (σ j) (hσ i) (hσ j)

end MDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asymptotic rates: endogenous value iteration converges at rate `βρ(ΛP*)`

Bray (2019b, *Management Science*), Proposition 4.

`Λ` (`lamMat`) subtracts from `v(x, y)` its mean over `y` given `x`. When the transition matrix
`F` maps functions of the exogenous state `x` to functions of `x` (`PreservesLift`, true of every
policy matrix of an `ExoMDP`), `ΛFΛ = ΛF`, so `(ΛF)ᵏΛ = ΛFᵏ` (`lamF_pow_endo`) and the spectral
radius `ρ(ΛF)` (`endoRadius`) governs the within-`x` span (`spy_pow_mulVec_le`).

* `endo_asymptotic_rate`: with a unique, strict optimal decision rule `σ*`, for every
  `γ > ρ(ΛP_{σ*})` there are `C` and `N` with `spy(T^{N+k}v − v*) ≤ C(βγ)ᵏ`; the endogenous
  values `Λ(Tⁿv)` converge at rate `βρ(ΛP_{σ*})` (`endo_values_asymptotic_rate`) (Bray, Prop 4.1).
* `endo_policy_eval_le` (Bray, Prop 4.2): endogenous policy evaluation converges at rate
  `βρ(ΛP_σ)`.
* `endoRadius_le_subradius` (**Bray, Prop 4**): `ρ(ΛF) ≤ λ(F)`, so endogenous value iteration is
  asymptotically never slower than relative value iteration.
-/

open Filter Topology Matrix Finset

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace DPExtensions.RelativeValueIteration

namespace ExoMDP

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem endo_idem [Nonempty Y] (v : X × Y → ℝ) : endo (endo v) = endo v := by
  have e : endo v = fun t => v t + lift (fun x => -mean v x) t := by
    funext t
    simp only [endo, lift]
    ring
  conv_lhs => rw [e]
  rw [endo_add_lift]

omit [Fintype X] in
theorem endo_lift [Nonempty Y] (c : X → ℝ) : endo (lift c : X × Y → ℝ) = 0 := by
  rw [show (lift c : X × Y → ℝ) = fun t => (fun _ => (0 : ℝ)) t + lift c t by
    funext t; simp, endo_add_lift]
  funext s
  simp [endo, mean]

/-- `F` maps functions of the exogenous state to functions of the exogenous state. -/
def PreservesLift (F : Matrix (X × Y) (X × Y) ℝ) : Prop :=
  ∀ c : X → ℝ, ∃ c' : X → ℝ, F *ᵥ lift c = lift c'

theorem endo_mulVec_endo [Nonempty Y] {G : Matrix (X × Y) (X × Y) ℝ} (hG : PreservesLift G)
    (d : X × Y → ℝ) : endo (G *ᵥ endo d) = endo (G *ᵥ d) := by
  obtain ⟨c', hc'⟩ := hG fun x => -mean d x
  have e : endo d = d + lift fun x => -mean d x := by
    funext t
    simp only [endo, lift, Pi.add_apply]
    ring
  rw [e, mulVec_add, hc']
  exact endo_add_lift (G *ᵥ d) c'

theorem spy_le_two_norm_endo [Nonempty X] [Nonempty Y] (w : X × Y → ℝ) : spy w ≤ 2 * ‖endo w‖ :=
  sup'_le _ _ fun x _ => sp_le fun y y' => by
    have e : w (x, y) - w (x, y') = endo w (x, y) - endo w (x, y') := by
      simp only [endo]
      ring
    have h1 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm (endo w) (x, y))
    have h2 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm (endo w) (x, y'))
    linarith [h1.2, h2.1]

theorem norm_endo_le [Nonempty X] [Nonempty Y] (d : X × Y → ℝ) : ‖endo d‖ ≤ spy d :=
  (pi_norm_le_iff_of_nonneg (spy_nonneg d)).2 fun s => by
    rw [Real.norm_eq_abs]
    exact abs_endo_le d s

theorem spy_mul_le [Nonempty X] [Nonempty Y] {c : ℝ} (hc : 0 ≤ c) (w : X × Y → ℝ) :
    spy (fun s => c * w s) ≤ c * spy w :=
  sup'_le _ _ fun x _ =>
    (sp_mul_le hc fun y => w (x, y)).trans (mul_le_mul_of_nonneg_left (sp_le_spy w x) hc)

variable [DecidableEq X] [DecidableEq Y]

/-- The matrix of the endogenizing operator `Λ`. -/
noncomputable def lamMat : Matrix (X × Y) (X × Y) ℝ := fun s t =>
  (if s = t then 1 else 0) - (if s.1 = t.1 then (Fintype.card Y : ℝ)⁻¹ else 0)

theorem lamMat_mulVec (v : X × Y → ℝ) : lamMat *ᵥ v = endo v := by
  funext s
  simp only [mulVec, dotProduct, lamMat, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true, endo, mean]
  congr 1
  rw [Fintype.sum_prod_type, sum_eq_single s.1
    (fun x _ hx => sum_eq_zero fun y _ => by simp [Ne.symm hx]) (by simp)]
  simp only [ite_true, ← mul_sum]
  rw [div_eq_inv_mul]

/-- The spectral radius of `ΛF`, which governs endogenous value iteration. -/
noncomputable def endoRadius (F : Matrix (X × Y) (X × Y) ℝ) : ℝ := specRad (lamMat * F)

theorem PreservesLift.pow {F : Matrix (X × Y) (X × Y) ℝ} (hF : PreservesLift F) (k : ℕ) :
    PreservesLift (F ^ k) := by
  induction k with
  | zero => exact fun c => ⟨c, one_mulVec _⟩
  | succ k ih =>
    intro c
    obtain ⟨c', hc'⟩ := hF c
    obtain ⟨c'', hc''⟩ := ih c'
    exact ⟨c'', by rw [pow_succ, ← mulVec_mulVec, hc', hc'']⟩

/-- `(ΛF)ᵏΛ = ΛFᵏ`. -/
theorem lamF_pow_endo [Nonempty Y] {F : Matrix (X × Y) (X × Y) ℝ} (hF : PreservesLift F)
    (k : ℕ) (d : X × Y → ℝ) : (lamMat * F) ^ k *ᵥ endo d = endo (F ^ k *ᵥ d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec, endo_mulVec_endo hF, ih,
      mulVec_mulVec, ← pow_succ]

/-- **`ρ(ΛF)` governs the within-`x` span**: for every `γ > ρ(ΛF)` there is `C` with
`spy(Fᵏd) ≤ Cγᵏ spy(d)` for all `k`. -/
theorem spy_pow_mulVec_le [Nonempty X] [Nonempty Y] {F : Matrix (X × Y) (X × Y) ℝ}
    (hF : PreservesLift F) {γ : ℝ} (hγ : endoRadius F < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (d : X × Y → ℝ), spy (F ^ k *ᵥ d) ≤ C * γ ^ k * spy d := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le (lamMat * F) hγ
  have hγ0 : 0 < γ := (specRad_nonneg _).trans_lt hγ
  refine ⟨2 * C, by positivity, fun k d => ?_⟩
  calc spy (F ^ k *ᵥ d) ≤ 2 * ‖endo (F ^ k *ᵥ d)‖ := spy_le_two_norm_endo _
    _ = 2 * ‖(lamMat * F) ^ k *ᵥ endo d‖ := by rw [lamF_pow_endo hF]
    _ ≤ 2 * (‖(lamMat * F) ^ k‖ * ‖endo d‖) :=
        mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) zero_le_two
    _ ≤ 2 * (C * γ ^ k * spy d) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul (hC k) (norm_endo_le d) (norm_nonneg _) (by positivity)
    _ = 2 * C * γ ^ k * spy d := by ring

/-- **Endogenous value iteration is asymptotically no slower than relative value iteration**
(Bray, Prop 4): `ρ(ΛF) ≤ λ(F)`. -/
theorem endoRadius_le_subradius [Nonempty X] [Nonempty Y] {F : Matrix (X × Y) (X × Y) ℝ}
    (hQ : IsStochastic F) (hF : PreservesLift F) (s₀ : X × Y) :
    endoRadius F ≤ subradius F s₀ := by
  refine le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le hQ s₀ hγ
  have hγ0 : 0 ≤ γ := (specRad_nonneg _).trans hγ.le
  refine specRad_le_of_norm_pow_le _ (K := 1 + 2 * C) (by positivity) hγ0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(lamMat * F) ^ k *ᵥ w‖ ≤ (1 + 2 * C) * γ ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    nlinarith [norm_nonneg w]
  have e : (lamMat * F) ^ (k + 1) *ᵥ w = endo (F ^ (k + 1) *ᵥ w) := by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec, lamF_pow_endo hF,
      mulVec_mulVec, ← pow_succ]
  rw [e]
  calc ‖endo (F ^ (k + 1) *ᵥ w)‖ ≤ spy (F ^ (k + 1) *ᵥ w) := norm_endo_le _
    _ ≤ sp (F ^ (k + 1) *ᵥ w) := spy_le_sp _
    _ ≤ C * γ ^ (k + 1) * sp w := hC _ _
    _ ≤ C * γ ^ (k + 1) * (2 * ‖w‖) :=
        mul_le_mul_of_nonneg_left (sp_le_two_norm w) (by positivity)
    _ ≤ (1 + 2 * C) * γ ^ (k + 1) * ‖w‖ := by nlinarith [norm_nonneg w, pow_nonneg hγ0 (k + 1)]

variable {A : Type*} (E : ExoMDP X Y A)

omit [DecidableEq X] [DecidableEq Y] in
/-- Every policy matrix of an `ExoMDP` preserves functions of the exogenous state. -/
theorem Pmat_preservesLift (σ : X × Y → A) : PreservesLift (E.toMDP.Pmat σ) := fun c =>
  ⟨E.Fxc c, by
    funext s
    change ∑ t, E.toMDP.P s (σ s) t * lift c t = lift (E.Fxc c) s
    simp only [E.sum_P_mul, lift, ← sum_mul, E.Fy_sum, one_mul, Fxc]⟩

/-- **Endogenous policy evaluation converges at rate `βρ(ΛP_σ)`** (Bray, 2019b, Prop 4.2). -/
theorem endo_policy_eval_le [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (σ : X × Y → A) {γ : ℝ}
    (hγ : endoRadius (E.toMDP.Pmat σ) < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (v : X × Y → ℝ),
      spy (fun s => (E.toMDP.Tσ σ)^[n] v s - E.toMDP.vσ hβ σ s) ≤
        C * (E.β * γ) ^ n * spy (fun s => v s - E.toMDP.vσ hβ σ s) := by
  obtain ⟨C, hC0, hC⟩ := spy_pow_mulVec_le (E.Pmat_preservesLift σ) hγ
  refine ⟨C, hC0, fun n v => ?_⟩
  have hfix : (E.toMDP.Tσ σ)^[n] (E.toMDP.vσ hβ σ) = E.toMDP.vσ hβ σ :=
    Function.iterate_fixed (E.toMDP.Tσ_vσ hβ σ) n
  have e := E.toMDP.Tσ_iterate_sub σ v (E.toMDP.vσ hβ σ) n
  rw [hfix] at e
  rw [e]
  calc spy (fun s => E.β ^ n * (E.toMDP.Pmat σ ^ n *ᵥ (v - E.toMDP.vσ hβ σ)) s)
      ≤ E.β ^ n * spy (E.toMDP.Pmat σ ^ n *ᵥ (v - E.toMDP.vσ hβ σ)) :=
        spy_mul_le (pow_nonneg E.β_nonneg n) _
    _ ≤ E.β ^ n * (C * γ ^ n * spy (v - E.toMDP.vσ hβ σ)) :=
        mul_le_mul_of_nonneg_left (hC n _) (pow_nonneg E.β_nonneg n)
    _ = C * (E.β * γ) ^ n * spy (fun s => v s - E.toMDP.vσ hβ σ s) := by
        rw [mul_pow]
        change _ = C * (E.β ^ n * γ ^ n) * spy (v - E.toMDP.vσ hβ σ)
        ring

/-- **Endogenous value iteration converges at rate `βρ(ΛP_{σ*})`**: with a unique, strict optimal
decision rule `σ*`, for every `γ > ρ(ΛP_{σ*})` there are `C` and `N` with
`spy(T^{N+k}v − v*) ≤ C(βγ)ᵏ`. -/
theorem endo_asymptotic_rate [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {σs : X × Y → A}
    (hstrict : ∀ s, σs s ∈ E.Γ s ∧ ∀ a ∈ E.Γ s, a ≠ σs s →
      E.toMDP.Q (E.toMDP.vstar hβ) s a < E.toMDP.Q (E.toMDP.vstar hβ) s (σs s))
    {γ : ℝ} (hγ : endoRadius (E.toMDP.Pmat σs) < γ) (v : X × Y → ℝ) :
    ∃ C N, ∀ k, spy (fun s => E.toMDP.T^[N + k] v s - E.toMDP.vstar hβ s) ≤
      C * (E.β * γ) ^ k := by
  obtain ⟨N, hN⟩ := E.toMDP.eventually_linear hβ hstrict v
  obtain ⟨C, hC0, hC⟩ := spy_pow_mulVec_le (E.Pmat_preservesLift σs) hγ
  refine ⟨C * spy (E.toMDP.T^[N] v - E.toMDP.vstar hβ), N, fun k => ?_⟩
  have e : (fun s => E.toMDP.T^[N + k] v s - E.toMDP.vstar hβ s) =
      fun s => E.β ^ k *
        (E.toMDP.Pmat σs ^ k *ᵥ (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) s := by
    funext s
    have := congrFun (hN k) s
    simpa using this
  rw [e]
  calc spy (fun s => E.β ^ k *
        (E.toMDP.Pmat σs ^ k *ᵥ (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) s)
      ≤ E.β ^ k * spy (E.toMDP.Pmat σs ^ k *ᵥ (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) :=
        spy_mul_le (pow_nonneg E.β_nonneg k) _
    _ ≤ E.β ^ k * (C * γ ^ k * spy (E.toMDP.T^[N] v - E.toMDP.vstar hβ)) :=
        mul_le_mul_of_nonneg_left (hC k _) (pow_nonneg E.β_nonneg k)
    _ = C * spy (E.toMDP.T^[N] v - E.toMDP.vstar hβ) * (E.β * γ) ^ k := by rw [mul_pow]; ring

/-- The endogenous values `Λ(Tⁿv)` converge to `Λv*` at rate `βρ(ΛP_{σ*})`. -/
theorem endo_values_asymptotic_rate [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {σs : X × Y → A}
    (hstrict : ∀ s, σs s ∈ E.Γ s ∧ ∀ a ∈ E.Γ s, a ≠ σs s →
      E.toMDP.Q (E.toMDP.vstar hβ) s a < E.toMDP.Q (E.toMDP.vstar hβ) s (σs s))
    {γ : ℝ} (hγ : endoRadius (E.toMDP.Pmat σs) < γ) (v : X × Y → ℝ) :
    ∃ C N, ∀ k s, |endo (E.toMDP.T^[N + k] v) s - endo (E.toMDP.vstar hβ) s| ≤
      C * (E.β * γ) ^ k := by
  obtain ⟨C, N, h⟩ := E.endo_asymptotic_rate hβ hstrict hγ v
  refine ⟨C, N, fun k s => le_trans ?_ (h k)⟩
  rw [← congrFun (endo_sub _ _) s]
  exact abs_endo_le _ s

/-- For every decision rule, the endogenous asymptotic rate is at most the relative one. -/
theorem endoRadius_policy_le [Nonempty X] [Nonempty Y] (σ : X × Y → A) (s₀ : X × Y) :
    endoRadius (E.toMDP.Pmat σ) ≤ subradius (E.toMDP.Pmat σ) s₀ :=
  endoRadius_le_subradius (E.toMDP.Pmat_isStochastic σ) (E.Pmat_preservesLift σ) s₀

end ExoMDP

end DPExtensions.RelativeValueIteration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# When is endogenous value iteration strictly faster?

Bray (2019b, *Management Science*), Proposition 5, Lemmas 4 and 7 and Corollaries 2–4.

Write `F_x` for the exogenous transition matrix (`FxMat`), `F_y(σ, x)` for the endogenous
transition matrix within exogenous state `x` (`FyMat`) and `Ω` for the demeaning matrix on `Y`
(`omegaMat`).

* `spectrum_exo_subset` (**Bray, Lemma 4**): every eigenvalue of `Δ_X F_x` is an eigenvalue of
  `ΔP_σ`, so `σ(F_x) ≤ σ(P_σ)` (`subradius_FxMat_le`): the chain as a whole mixes no faster than
  its exogenous part.
* `endoRadius_le_of_vecNorm` (**Bray, Prop 5**): for any vector norm `N` on `ℂ^Y`, if `c` bounds
  the `N`-operator norm of `ΩF_y(σ, x)` for every `x`, then `ρ(ΛP_σ) ≤ c`. Hence if
  `σ(F_x) > c`, endogenous iteration is strictly faster (`endoRadius_lt_subradius_of_vecNorm`,
  `endo_strictly_faster`, `endo_eval_strictly_faster`).
* **Bray, Cor 2**: `c` may be (a) the Frobenius norm of `ΩF_y(σ, x)` (`endoRadius_le_frobenius`),
  (b) its largest singular value (`endoRadius_le_singularValue`; `norm_apply_le_singularValues_zero`
  shows the largest singular value is the `ℓ²` operator norm), (c) its largest absolute row sum
  (`endoRadius_le_rowSum`), (d) its largest absolute column sum (`endoRadius_le_colSum`), or
  (e) the Hajnal (Dobrushin) coefficient of `F_y(σ, x)` (`endoRadius_le_hajnal`).
* `endoRadius_lt_of_nonergodic_scrambling` (**Bray, Cor 3**): if `F_x` is not ergodic (it has a
  non-constant fixed vector or an eigenvalue `μ ≠ 1` with `|μ| = 1`) and every `F_y(σ, x)` is
  scrambling, endogenous iteration is strictly faster.
* `specRad_omega_eq_subradius` (**Bray, Lemma 7**): `ρ(ΩF) = σ(F)` for every stochastic `F`.
* `endoRadius_le_subradius_Fy` (**Bray, Cor 4**): if `F_y(σ, x) = G` for every `x`, then
  `ρ(ΛP_σ) ≤ σ(G)`, so endogenous iteration is strictly faster when `σ(F_x) > σ(G)`
  (`endoRadius_lt_of_Fy_const`).
-/

open Filter Topology Matrix Finset

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace DPExtensions.RelativeValueIteration

/-! ### Spectral radii from eigenvalue bounds -/

/-- If every eigenvalue of `B` has modulus at most `c`, then `ρ(B) ≤ c`. -/
theorem specRad_le_of_eigen {S : Type*} [Fintype S] (B : Matrix S S ℝ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ (μ : ℂ) (e : S → ℂ), e ≠ 0 → complexify B *ᵥ e = μ • e → ‖μ‖ ≤ c) :
    specRad B ≤ c := by
  classical
  have hle : spectralRadius ℂ (complexify B) ≤ ENNReal.ofReal c := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun μ hμ => ?_
    obtain ⟨e, he, hμe⟩ := (mem_spectrum_iff_eigenpair _ μ).1 hμ
    rw [ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top hc]
    simpa using h μ e he hμe
  exact ENNReal.toReal_le_of_le_ofReal hc hle

/-- Every eigenvalue of `B` has modulus at most `ρ(B)`. -/
theorem norm_le_specRad {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] (B : Matrix S S ℝ)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify B)) : ‖μ‖ ≤ specRad B := by
  have h : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (complexify B) := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun μ _ => (‖μ‖₊ : ENNReal)) μ hμ
  have := ENNReal.toReal_mono (spectralRadius_complexify_ne_top B) h
  simpa [specRad] using this

/-- Spectral radii are monotone under inclusion of spectra. -/
theorem specRad_mono_of_spectrum {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] [Nonempty T] (B : Matrix S S ℝ) (C : Matrix T T ℝ)
    (h : ∀ μ, μ ∈ spectrum ℂ (complexify B) → μ ∈ spectrum ℂ (complexify C)) :
    specRad B ≤ specRad C := by
  refine ENNReal.toReal_mono (spectralRadius_complexify_ne_top C) ?_
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  exact iSup₂_le fun μ hμ => le_iSup₂ (f := fun μ _ => (‖μ‖₊ : ENNReal)) μ (h μ hμ)

/-- The rows of a power of a stochastic matrix are probability vectors. -/
theorem IsStochastic.pow {S : Type*} [Fintype S] [DecidableEq S] {Q : Matrix S S ℝ}
    (hQ : IsStochastic Q) (k : ℕ) : IsStochastic (Q ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_zero, one_apply]
      split_ifs <;> norm_num
    · simp [one_apply]
  | succ k ih =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_succ, mul_apply]
      exact sum_nonneg fun t _ => mul_nonneg (ih.1 i t) (hQ.1 t j)
    · rw [pow_succ]
      simp only [mul_apply]
      rw [sum_comm]
      simp only [← mul_sum, hQ.2, mul_one]
      exact ih.2 i

/-- A stochastic matrix that is not
ergodic — with a non-constant fixed vector, or an eigenvalue `μ ≠ 1` of modulus one — has
subradius at least one. -/
theorem one_le_subradius_of_nonergodic {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    (h : (∃ μ ∈ spectrum ℂ (complexify Q), μ ≠ 1 ∧ ‖μ‖ = 1) ∨
      ∃ v : S → ℂ, complexify Q *ᵥ v = v ∧ ∃ i j, v i ≠ v j) :
    1 ≤ subradius Q s₀ := by
  rcases h with ⟨μ, hμ, h1, hn⟩ | hv
  · have h0 : μ ≠ 0 := by
      rintro rfl
      simp at hn
    rw [← hn]
    exact norm_le_specRad _ ((mem_spectrum_deltaQ_iff hQ s₀ h0).2 (Or.inl ⟨hμ, h1⟩))
  · have := norm_le_specRad _ ((mem_spectrum_deltaQ_iff hQ s₀ one_ne_zero).2 (Or.inr ⟨rfl, hv⟩))
    simpa [subradius] using this

/-! ### Vector norms on `ℂ^Y` -/

/-- `N` is a norm on `ℂ^Y`. -/
def IsVecNorm {Y : Type*} (N : (Y → ℂ) → ℝ) : Prop :=
  (∀ u v, N (u + v) ≤ N u + N v) ∧ (∀ (a : ℂ) u, N (a • u) = ‖a‖ * N u) ∧
    ∀ u, N u = 0 → u = 0

namespace IsVecNorm

variable {Y : Type*} {N : (Y → ℂ) → ℝ}

theorem zero (hN : IsVecNorm N) : N 0 = 0 := by
  have := hN.2.1 0 0
  simpa using this

theorem nonneg (hN : IsVecNorm N) (u : Y → ℂ) : 0 ≤ N u := by
  have h1 := hN.1 u ((-1 : ℂ) • u)
  rw [hN.2.1, show u + (-1 : ℂ) • u = 0 by simp, hN.zero] at h1
  simp only [norm_neg, norm_one, one_mul] at h1
  linarith

theorem pos (hN : IsVecNorm N) {u : Y → ℂ} (hu : u ≠ 0) : 0 < N u :=
  lt_of_le_of_ne (hN.nonneg u) fun h => hu (hN.2.2 u h.symm)

theorem sum_le (hN : IsVecNorm N) {ι : Type*} (s : Finset ι) (g : ι → Y → ℂ) :
    N (∑ i ∈ s, g i) ≤ ∑ i ∈ s, N (g i) :=
  Finset.le_sum_of_subadditive N hN.zero.le hN.1 s g

theorem smul_real (hN : IsVecNorm N) {r : ℝ} (hr : 0 ≤ r) (u : Y → ℂ) :
    N ((r : ℂ) • u) = r * N u := by
  rw [hN.2.1, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The sup norm. -/
theorem sup_norm [Fintype Y] : IsVecNorm fun u : Y → ℂ => ‖u‖ :=
  ⟨norm_add_le, fun a u => norm_smul a u, fun _ h => norm_eq_zero.1 h⟩

end IsVecNorm

/-! ### `ℓ¹` and `ℓ²` norms and the largest singular value -/

/-- The `ℓ¹` norm. -/
theorem IsVecNorm.l1_norm {Y : Type*} [Fintype Y] : IsVecNorm fun u : Y → ℂ => ∑ y, ‖u y‖ :=
  ⟨fun u v => (sum_le_sum fun y _ => norm_add_le (u y) (v y)).trans_eq sum_add_distrib,
    fun a u => by simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_sum],
    fun u h => funext fun y => norm_eq_zero.1
      ((sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).1 h y (mem_univ y))⟩

/-- The `ℓ²` (Euclidean) norm. -/
theorem IsVecNorm.l2_norm {Y : Type*} [Fintype Y] :
    IsVecNorm fun u : Y → ℂ => ‖(WithLp.toLp 2 u : EuclideanSpace ℂ Y)‖ :=
  ⟨fun u v => by
      dsimp only
      rw [WithLp.toLp_add]
      exact norm_add_le _ _,
    fun a u => by
      dsimp only
      rw [WithLp.toLp_smul]
      exact norm_smul a _,
    fun u h => WithLp.toLp_injective 2 (by rw [norm_eq_zero.1 h, WithLp.toLp_zero])⟩

/-- **The largest singular value is the `ℓ²` operator norm**: `‖Tv‖ ≤ σ₀(T)‖v‖`, from the
spectral decomposition of `TᵀT`. -/
theorem norm_apply_le_singularValues_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (v : E) :
    ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := by
  have hA := T.isSymmetric_adjoint_comp_self
  have hσ0 := T.singularValues_nonneg 0
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    rw [Subsingleton.elim v 0]
    simp
  have hn : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  have hsq : T.singularValues 0 ^ 2 = hA.eigenvalues hn ⟨0, hpos⟩ :=
    T.sq_singularValues_of_lt hn hpos
  have h1 : ‖T v‖ ^ 2 = inner ℝ ((LinearMap.adjoint T ∘ₗ T) v) v := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have h2 : inner ℝ ((LinearMap.adjoint T ∘ₗ T) v) v =
      ∑ i, hA.eigenvalues hn i * (hA.eigenvectorBasis hn).repr v i ^ 2 := by
    rw [← (hA.eigenvectorBasis hn).repr.inner_map_map, PiLp.inner_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [hA.eigenvectorBasis_apply_self_apply hn v i]
    simp only [RCLike.inner_apply, conj_trivial, RCLike.ofReal_real_eq_id, id_eq]
    ring
  have h3 : ‖v‖ ^ 2 = ∑ i, (hA.eigenvectorBasis hn).repr v i ^ 2 := by
    rw [← (hA.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_eq,
      Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Real.norm_eq_abs, sq_abs]
  have key : ‖T v‖ ^ 2 ≤ (T.singularValues 0 * ‖v‖) ^ 2 := by
    rw [h1, h2, mul_pow, hsq, h3, mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (hA.eigenvalues_antitone hn (Fin.le_def.2 (Nat.zero_le _))) (sq_nonneg _)
  nlinarith [norm_nonneg (T v), mul_nonneg hσ0 (norm_nonneg v)]

/-- `∑(Mu)² ≤ σ₀(M)²∑u²` for a real square matrix `M`. -/
theorem sum_sq_mulVec_le_singularValues {Y : Type*} [Fintype Y] [DecidableEq Y]
    (M : Matrix Y Y ℝ) (u : Y → ℝ) :
    ∑ y, (M *ᵥ u) y ^ 2 ≤ (Matrix.toEuclideanLin M).singularValues 0 ^ 2 * ∑ y, u y ^ 2 := by
  have h := norm_apply_le_singularValues_zero (Matrix.toEuclideanLin M) (WithLp.toLp 2 u)
  have e1 : ‖Matrix.toEuclideanLin M (WithLp.toLp 2 u)‖ ^ 2 = ∑ y, (M *ᵥ u) y ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs]
  have e2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ Y)‖ ^ 2 = ∑ y, u y ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs]
  rw [← e1, ← e2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- A real `ℓ²` bound on `M` extends to complex vectors, real and imaginary parts separately. -/
theorem sum_sq_norm_cmulVec_le {Y : Type*} [Fintype Y] (M : Matrix Y Y ℝ) {c : ℝ}
    (h : ∀ u : Y → ℝ, ∑ y, (M *ᵥ u) y ^ 2 ≤ c ^ 2 * ∑ y, u y ^ 2) (u : Y → ℂ) :
    ∑ y, ‖(complexify M *ᵥ u) y‖ ^ 2 ≤ c ^ 2 * ∑ y, ‖u y‖ ^ 2 := by
  have hre : ∀ y, ((complexify M *ᵥ u) y).re = (M *ᵥ fun t => (u t).re) y := fun y => by
    simp [mulVec, dotProduct, complexify_apply, Complex.re_sum]
  have him : ∀ y, ((complexify M *ᵥ u) y).im = (M *ᵥ fun t => (u t).im) y := fun y => by
    simp [mulVec, dotProduct, complexify_apply, Complex.im_sum]
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [hn, sum_add_distrib, hre, him, mul_add]
  exact add_le_add (h _) (h _)

namespace ExoMDP

variable {X Y A : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The demeaning matrix `Ω = I − ιι′/Y` on the endogenous state. -/
noncomputable def omegaMat : Matrix Y Y ℝ := fun y y' =>
  (if y = y' then 1 else 0) - (Fintype.card Y : ℝ)⁻¹

theorem comega_mulVec (u : Y → ℂ) :
    complexify (omegaMat : Matrix Y Y ℝ) *ᵥ u = fun y => u y - (∑ y', u y') / Fintype.card Y := by
  funext y
  simp [complexify, omegaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul,
    apply_ite Complex.ofReal, ← mul_sum, div_eq_inv_mul]

theorem omega_mulVec (v : Y → ℝ) :
    (omegaMat : Matrix Y Y ℝ) *ᵥ v = fun y => v y - (∑ y', v y') / Fintype.card Y := by
  funext y
  simp [omegaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul, ← mul_sum,
    div_eq_inv_mul]

theorem omega_mulVec_const [Nonempty Y] (c : ℝ) :
    (omegaMat : Matrix Y Y ℝ) *ᵥ (fun _ => c) = 0 := by
  have hY : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [omega_mulVec]
  funext y
  simp only [sum_const, card_univ, nsmul_eq_mul, Pi.zero_apply]
  rw [mul_div_cancel_left₀ c hY, sub_self]

theorem omega_mulVec_add_const [Nonempty Y] (v : Y → ℝ) (c : ℝ) :
    (omegaMat : Matrix Y Y ℝ) *ᵥ (v + fun _ => c) = omegaMat *ᵥ v := by
  rw [mulVec_add, omega_mulVec_const, add_zero]

/-- Demeaning moves no entry by more than the span. -/
theorem norm_omega_mulVec_le [Nonempty Y] (v : Y → ℝ) :
    ‖(omegaMat : Matrix Y Y ℝ) *ᵥ v‖ ≤ sp v :=
  (pi_norm_le_iff_of_nonneg (sp_nonneg v)).2 fun y => by
    have hY : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
    have e : v y - (∑ y', v y') / Fintype.card Y = (∑ y', (v y - v y')) / Fintype.card Y := by
      simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
      field_simp
    rw [omega_mulVec, Real.norm_eq_abs]
    dsimp only
    rw [e, abs_div, abs_of_pos hY, div_le_iff₀ hY]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ y', |v y - v y'| ≤ ∑ _y' : Y, sp v := sum_le_sum fun y' _ => abs_sub_le_sp v y y'
      _ = sp v * Fintype.card Y := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- Demeaning does not change the span. -/
theorem sp_omega_mulVec [Nonempty Y] (v : Y → ℝ) : sp ((omegaMat : Matrix Y Y ℝ) *ᵥ v) = sp v := by
  rw [omega_mulVec]
  have := sp_add_const v (-((∑ y', v y') / Fintype.card Y))
  simpa [sub_eq_add_neg] using this

/-- `(ΩF)ᵏΩ = ΩFᵏ`: `Ω` kills constants and `F` preserves them. -/
theorem omegaF_pow_mulVec_omega [Nonempty Y] {F : Matrix Y Y ℝ} (hF : IsStochastic F) (k : ℕ)
    (v : Y → ℝ) : (omegaMat * F) ^ k *ᵥ (omegaMat *ᵥ v) = omegaMat *ᵥ (F ^ k *ᵥ v) := by
  have hkill : ∀ (j : ℕ) (u : Y → ℝ),
      (omegaMat : Matrix Y Y ℝ) *ᵥ (F ^ j *ᵥ (omegaMat *ᵥ u)) = omegaMat *ᵥ (F ^ j *ᵥ u) := by
    intro j u
    have e : (omegaMat : Matrix Y Y ℝ) *ᵥ u = u + fun _ => -((∑ y', u y') / Fintype.card Y) := by
      rw [omega_mulVec]
      funext y
      simp [sub_eq_add_neg]
    rw [e, mulVec_add, mulVec_const (hF.pow j), omega_mulVec_add_const]
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, ih, mulVec_mulVec _ (F ^ k) F, ← pow_succ,
      hkill]

/-- **Bray, Lemma 7**: `σ(F) = ρ(ΩF)` for every stochastic `F`: demeaning and differencing
against a reference state give the same spectral radius. -/
theorem specRad_omega_eq_subradius [Nonempty Y] {F : Matrix Y Y ℝ} (hF : IsStochastic F)
    (y₀ : Y) : specRad (omegaMat * F) = subradius F y₀ := by
  have hpow : ∀ (k : ℕ) (w : Y → ℝ),
      (omegaMat * F) ^ (k + 1) *ᵥ w = omegaMat *ᵥ (F ^ (k + 1) *ᵥ w) := fun k w => by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, omegaF_pow_mulVec_omega hF,
      mulVec_mulVec w (F ^ k) F, ← pow_succ]
  have hpowΔ : ∀ (k : ℕ) (w : Y → ℝ),
      (deltaMat y₀ * F) ^ (k + 1) *ᵥ w = deltaMat y₀ *ᵥ (F ^ (k + 1) *ᵥ w) := fun k w => by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, deltaQ_pow_mulVec hF,
      mulVec_mulVec w (F ^ k) F, ← pow_succ]
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_)
    (le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_)
  · obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le hF y₀ hγ
    have hγ0 : 0 ≤ γ := (specRad_nonneg _).trans hγ.le
    refine specRad_le_of_norm_pow_le _ (K := 1 + 2 * C) (by positivity) hγ0 fun k => ?_
    rw [Matrix.linfty_opNorm_eq_opNorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    change ‖(omegaMat * F) ^ k *ᵥ w‖ ≤ (1 + 2 * C) * γ ^ k * ‖w‖
    rcases k with _ | k
    · simp only [pow_zero, one_mulVec, mul_one]
      nlinarith [norm_nonneg w]
    rw [hpow]
    calc ‖(omegaMat : Matrix Y Y ℝ) *ᵥ (F ^ (k + 1) *ᵥ w)‖ ≤ sp (F ^ (k + 1) *ᵥ w) :=
          norm_omega_mulVec_le _
      _ ≤ C * γ ^ (k + 1) * sp w := hC _ _
      _ ≤ C * γ ^ (k + 1) * (2 * ‖w‖) :=
          mul_le_mul_of_nonneg_left (sp_le_two_norm w) (by positivity)
      _ ≤ (1 + 2 * C) * γ ^ (k + 1) * ‖w‖ := by
          nlinarith [mul_nonneg (pow_nonneg hγ0 (k + 1)) (norm_nonneg w)]
  · obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le (omegaMat * F) hγ
    have hγ0 : 0 ≤ γ := (specRad_nonneg _).trans hγ.le
    unfold subradius
    refine specRad_le_of_norm_pow_le _ (K := 1 + 2 * C) (by positivity) hγ0 fun k => ?_
    rw [Matrix.linfty_opNorm_eq_opNorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    change ‖(deltaMat y₀ * F) ^ k *ᵥ w‖ ≤ (1 + 2 * C) * γ ^ k * ‖w‖
    rcases k with _ | k
    · simp only [pow_zero, one_mulVec, mul_one]
      nlinarith [norm_nonneg w]
    rw [hpowΔ]
    calc ‖deltaMat y₀ *ᵥ (F ^ (k + 1) *ᵥ w)‖ ≤ sp (F ^ (k + 1) *ᵥ w) :=
          norm_deltaMat_mulVec_le _ _
      _ = sp ((omegaMat : Matrix Y Y ℝ) *ᵥ (F ^ (k + 1) *ᵥ w)) := (sp_omega_mulVec _).symm
      _ ≤ 2 * ‖(omegaMat : Matrix Y Y ℝ) *ᵥ (F ^ (k + 1) *ᵥ w)‖ := sp_le_two_norm _
      _ = 2 * ‖(omegaMat * F) ^ (k + 1) *ᵥ w‖ := by rw [hpow]
      _ ≤ 2 * (‖(omegaMat * F) ^ (k + 1)‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) zero_le_two
      _ ≤ 2 * (C * γ ^ (k + 1) * ‖w‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg w))
            zero_le_two
      _ ≤ (1 + 2 * C) * γ ^ (k + 1) * ‖w‖ := by
          nlinarith [mul_nonneg (pow_nonneg hγ0 (k + 1)) (norm_nonneg w)]

theorem clamMat_mulVec (w : X × Y → ℂ) :
    complexify (lamMat : Matrix (X × Y) (X × Y) ℝ) *ᵥ w =
      fun s => w s - (∑ y, w (s.1, y)) / Fintype.card Y := by
  funext s
  simp only [mulVec, dotProduct, complexify_apply, lamMat, Complex.ofReal_sub, sub_mul,
    sum_sub_distrib, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  congr 1
  rw [Fintype.sum_prod_type, sum_eq_single s.1
    (fun x _ hx => sum_eq_zero fun y _ => by simp [Ne.symm hx]) (by simp)]
  simp only [ite_true, ← mul_sum]
  push_cast
  rw [div_eq_inv_mul]

variable (E : ExoMDP X Y A)

/-- The exogenous transition matrix `F_x`. -/
def FxMat : Matrix X X ℝ := E.Fx

omit [DecidableEq X] [DecidableEq Y] in
theorem FxMat_isStochastic : IsStochastic E.FxMat := ⟨E.Fx_nonneg, E.Fx_sum⟩

/-- The endogenous transition matrix `F_y(σ, x)` within exogenous state `x`. -/
def FyMat (σ : X × Y → A) (x : X) : Matrix Y Y ℝ := fun y y' => E.Fy x y (σ (x, y)) y'

omit [DecidableEq X] [DecidableEq Y] in
theorem FyMat_isStochastic (σ : X × Y → A) (x : X) : IsStochastic (E.FyMat σ x) :=
  ⟨fun _ _ => E.Fy_nonneg _ _ _ _, fun _ => E.Fy_sum _ _ _⟩

omit [DecidableEq X] [DecidableEq Y] in
theorem Pmat_apply (σ : X × Y → A) (s t : X × Y) :
    E.toMDP.Pmat σ s t = E.FxMat s.1 t.1 * E.FyMat σ s.1 s.2 t.2 := rfl

omit [DecidableEq X] [DecidableEq Y] in
theorem cPmat_mulVec_lift (σ : X × Y → A) (v : X → ℂ) :
    complexify (E.toMDP.Pmat σ) *ᵥ (fun s => v s.1) =
      fun s => (complexify E.FxMat *ᵥ v) s.1 := by
  funext s
  simp only [mulVec, dotProduct, complexify_apply, Pmat_apply, Fintype.sum_prod_type]
  refine sum_congr rfl fun x' _ => ?_
  have h : ∑ y', ((E.FyMat σ s.1 s.2 y' : ℝ) : ℂ) = 1 := by
    exact_mod_cast (E.FyMat_isStochastic σ s.1).2 s.2
  push_cast
  rw [← sum_mul, ← mul_sum, h, mul_one]

/-- **Bray, Lemma 4**: every eigenvalue of `Δ_X F_x` is an eigenvalue of `ΔP_σ`. -/
theorem spectrum_exo_subset [Nonempty Y] (σ : X × Y → A) (s₀ : X × Y) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify (deltaMat s₀.1 * E.FxMat))) :
    μ ∈ spectrum ℂ (complexify (deltaMat s₀ * E.toMDP.Pmat σ)) := by
  obtain ⟨v, hv, hμv⟩ := (mem_spectrum_iff_eigenpair _ μ).1 hμ
  refine (mem_spectrum_iff_eigenpair _ μ).2 ⟨fun s => v s.1, fun h => hv ?_, ?_⟩
  · funext x
    exact congrFun h (x, Classical.arbitrary Y)
  · rw [complexify_deltaQ_mulVec, E.cPmat_mulVec_lift]
    funext s
    have := congrFun hμv s.1
    rw [complexify_deltaQ_mulVec] at this
    simpa using this

/-- **The chain mixes no faster than its exogenous part**: `σ(F_x) ≤ σ(P_σ)`. -/
theorem subradius_FxMat_le [Nonempty X] [Nonempty Y] (σ : X × Y → A) (s₀ : X × Y) :
    subradius E.FxMat s₀.1 ≤ subradius (E.toMDP.Pmat σ) s₀ :=
  specRad_mono_of_spectrum _ _ fun _ hμ => E.spectrum_exo_subset σ s₀ hμ

/-- `ΛP_σ` acts on each exogenous slice through `ΩF_y(σ, x)`. -/
theorem clamP_mulVec (σ : X × Y → A) (v : X × Y → ℂ) (s : X × Y) :
    (complexify (lamMat * E.toMDP.Pmat σ) *ᵥ v) s =
      ∑ x', (E.FxMat s.1 x' : ℂ) *
        (complexify (omegaMat * E.FyMat σ s.1) *ᵥ fun y => v (x', y)) s.2 := by
  have hP : ∀ x y, (complexify (E.toMDP.Pmat σ) *ᵥ v) (x, y) =
      ∑ x', (E.FxMat x x' : ℂ) * (complexify (E.FyMat σ x) *ᵥ fun y' => v (x', y')) y := by
    intro x y
    simp only [mulVec, dotProduct, complexify_apply, Pmat_apply, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun x' _ => sum_congr rfl fun y' _ => ?_
    push_cast
    ring
  obtain ⟨x, y⟩ := s
  rw [complexify_mul, ← mulVec_mulVec, clamMat_mulVec, complexify_mul]
  simp only [← mulVec_mulVec, comega_mulVec, hP, mul_sub, sum_sub_distrib]
  congr 1
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun x' _ => ?_
  rw [← mul_sum, mul_div_assoc]

/-- **Bray, Prop 5**: for any vector norm `N` on `ℂ^Y`, if `c` bounds the `N`-operator norm of
`ΩF_y(σ, x)` for every exogenous state `x`, then `ρ(ΛP_σ) ≤ c`. -/
theorem endoRadius_le_of_vecNorm [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    {N : (Y → ℂ) → ℝ} (hN : IsVecNorm N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x u, N (complexify (omegaMat * E.FyMat σ x) *ᵥ u) ≤ c * N u) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  unfold endoRadius
  refine specRad_le_of_eigen _ hc0 fun μ e he heig => ?_
  obtain ⟨x₀, -, hmax⟩ := exists_max_image univ (fun x => N fun y => e (x, y)) univ_nonempty
  have hpos : 0 < N fun y => e (x₀, y) := by
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      exact he (funext fun s => by
        by_contra hs
        exact h ⟨s, hs⟩)
    have h1 : 0 < N fun y => e (s.1, y) := hN.pos fun h => hs (by simpa using congrFun h s.2)
    exact h1.trans_le (hmax s.1 (mem_univ _))
  have hrow : (μ • fun y => e (x₀, y)) = ∑ x', (E.FxMat x₀ x' : ℂ) •
      (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y)) := by
    funext y
    have := congrFun heig (x₀, y)
    rw [E.clamP_mulVec] at this
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this ⊢
    exact this.symm
  have hst := E.FxMat_isStochastic
  have key : ‖μ‖ * N (fun y => e (x₀, y)) ≤ c * N (fun y => e (x₀, y)) := by
    rw [← hN.2.1, hrow]
    calc N (∑ x', (E.FxMat x₀ x' : ℂ) •
          (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y)))
        ≤ ∑ x', N ((E.FxMat x₀ x' : ℂ) •
          (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y))) := hN.sum_le _ _
      _ = ∑ x', E.FxMat x₀ x' *
          N (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y)) :=
          sum_congr rfl fun x' _ => hN.smul_real (hst.1 x₀ x') _
      _ ≤ ∑ x', E.FxMat x₀ x' * (c * N fun y => e (x₀, y)) := sum_le_sum fun x' _ =>
          mul_le_mul_of_nonneg_left ((hc x₀ _).trans
            (mul_le_mul_of_nonneg_left (hmax x' (mem_univ _)) hc0)) (hst.1 x₀ x')
      _ = c * N (fun y => e (x₀, y)) := by rw [← sum_mul, hst.2 x₀, one_mul]
  exact le_of_mul_le_mul_right key hpos

/-- **Bray, Prop 5 (strict form)**: if `σ(F_x)` exceeds a bound `c` on the `N`-operator norms of
`ΩF_y(σ, x)`, then `ρ(ΛP_σ) < σ(P_σ)`. -/
theorem endoRadius_lt_subradius_of_vecNorm [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    (s₀ : X × Y) {N : (Y → ℂ) → ℝ} (hN : IsVecNorm N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x u, N (complexify (omegaMat * E.FyMat σ x) *ᵥ u) ≤ c * N u)
    (hlt : c < subradius E.FxMat s₀.1) :
    endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀ :=
  (E.endoRadius_le_of_vecNorm σ hN hc0 hc).trans_lt (hlt.trans_le (E.subradius_FxMat_le σ s₀))

/-- **Endogenous value iteration is strictly faster** (Bray, Prop 5.1): if `ρ(ΛP_{σ*}) <
σ(P_{σ*})`, endogenous values converge at rate `βγ` for some `γ` strictly below `σ(P_{σ*})`. -/
theorem endo_strictly_faster [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {σs : X × Y → A}
    (hstrict : ∀ s, σs s ∈ E.Γ s ∧ ∀ a ∈ E.Γ s, a ≠ σs s →
      E.toMDP.Q (E.toMDP.vstar hβ) s a < E.toMDP.Q (E.toMDP.vstar hβ) s (σs s))
    (s₀ : X × Y) (hlt : endoRadius (E.toMDP.Pmat σs) < subradius (E.toMDP.Pmat σs) s₀)
    (v : X × Y → ℝ) :
    ∃ γ < subradius (E.toMDP.Pmat σs) s₀, ∃ C N, ∀ k,
      spy (fun s => E.toMDP.T^[N + k] v s - E.toMDP.vstar hβ s) ≤ C * (E.β * γ) ^ k := by
  obtain ⟨γ, h1, h2⟩ := exists_between hlt
  exact ⟨γ, h2, E.endo_asymptotic_rate hβ hstrict h1 v⟩

/-- **Endogenous policy evaluation is strictly faster** (Bray, Prop 5.2). -/
theorem endo_eval_strictly_faster [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (σ : X × Y → A)
    (s₀ : X × Y) (hlt : endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀) :
    ∃ γ < subradius (E.toMDP.Pmat σ) s₀, ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (v : X × Y → ℝ),
      spy (fun s => (E.toMDP.Tσ σ)^[n] v s - E.toMDP.vσ hβ σ s) ≤
        C * (E.β * γ) ^ n * spy (fun s => v s - E.toMDP.vσ hβ σ s) := by
  obtain ⟨γ, h1, h2⟩ := exists_between hlt
  exact ⟨γ, h2, E.endo_policy_eval_le hβ σ h1⟩

/-- **Bray, Cor 2(c)**: the largest absolute row sum of `ΩF_y(σ, x)` bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_rowSum [Nonempty X] [Nonempty Y] (σ : X × Y → A) {c : ℝ}
    (hc : ∀ x y, ∑ y', |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'| ≤ c) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  have hc0 : 0 ≤ c := (sum_nonneg fun _ _ => abs_nonneg _).trans
    (hc (Classical.arbitrary X) (Classical.arbitrary Y))
  refine E.endoRadius_le_of_vecNorm σ IsVecNorm.sup_norm hc0 fun x u => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc0 (norm_nonneg u))).2 fun y => ?_
  simp only [mulVec, dotProduct, complexify_apply]
  calc ‖∑ y', ((omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' : ℂ) * u y'‖
      ≤ ∑ y', |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'| * ‖u‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun y' _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u y') (abs_nonneg _))
    _ ≤ c * ‖u‖ := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right (hc x y) (norm_nonneg u)

/-- **Bray, Prop 5 under the `ℓ²` norm**: a bound `∑((ΩF_y(σ, x))u)² ≤ c²∑u²` on real vectors
bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_l2 [Nonempty X] [Nonempty Y] (σ : X × Y → A) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x (u : Y → ℝ),
      ∑ y, ((omegaMat * E.FyMat σ x : Matrix Y Y ℝ) *ᵥ u) y ^ 2 ≤ c ^ 2 * ∑ y, u y ^ 2) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  refine E.endoRadius_le_of_vecNorm σ IsVecNorm.l2_norm hc0 fun x u => ?_
  have h := sum_sq_norm_cmulVec_le _ (hc x) u
  have hN : ∀ w : Y → ℂ, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ Y)‖ = √(∑ y, ‖w y‖ ^ 2) :=
    fun w => by
      rw [EuclideanSpace.norm_eq]
  simp only [hN]
  rw [← Real.sqrt_sq hc0, ← Real.sqrt_mul (sq_nonneg c)]
  exact Real.sqrt_le_sqrt h

/-- **Bray, Cor 2(a)**: the Frobenius norm (the Euclidean norm of `vec(ΩF_y(σ, x))`) bounds
`ρ(ΛP_σ)`. -/
theorem endoRadius_le_frobenius [Nonempty X] [Nonempty Y] (σ : X × Y → A) {c : ℝ}
    (hc : ∀ x, √(∑ y, ∑ y', (omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' ^ 2) ≤ c) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  have hc0 : 0 ≤ c := (Real.sqrt_nonneg _).trans (hc (Classical.arbitrary X))
  refine E.endoRadius_le_l2 σ hc0 fun x u => ?_
  have hF : ∑ y, ∑ y', (omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' ^ 2 ≤ c ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hc x) 2
    rwa [Real.sq_sqrt (by positivity)] at this
  calc ∑ y, ((omegaMat * E.FyMat σ x : Matrix Y Y ℝ) *ᵥ u) y ^ 2
      ≤ ∑ y, (∑ y', (omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' ^ 2) * ∑ y', u y' ^ 2 :=
        sum_le_sum fun y _ => sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ y, ∑ y', (omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' ^ 2) * ∑ y', u y' ^ 2 :=
        (sum_mul _ _ _).symm
    _ ≤ c ^ 2 * ∑ y, u y ^ 2 := mul_le_mul_of_nonneg_right hF (sum_nonneg fun _ _ => sq_nonneg _)

/-- **Bray, Cor 2(b)**: the largest singular value of `ΩF_y(σ, x)` bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_singularValue [Nonempty X] [Nonempty Y] (σ : X × Y → A) {c : ℝ}
    (hc : ∀ x, (Matrix.toEuclideanLin (omegaMat * E.FyMat σ x : Matrix Y Y ℝ)).singularValues 0 ≤
      c) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  have hc0 : 0 ≤ c := (LinearMap.singularValues_nonneg _ 0).trans (hc (Classical.arbitrary X))
  refine E.endoRadius_le_l2 σ hc0 fun x u => (sum_sq_mulVec_le_singularValues _ u).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (LinearMap.singularValues_nonneg _ 0) (hc x) 2)
    (sum_nonneg fun _ _ => sq_nonneg _)

/-- **Bray, Cor 2(d)**: the largest absolute column sum of `ΩF_y(σ, x)` (the `ℓ¹` operator norm)
bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_colSum [Nonempty X] [Nonempty Y] (σ : X × Y → A) {c : ℝ}
    (hc : ∀ x y', ∑ y, |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'| ≤ c) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  have hc0 : 0 ≤ c := (sum_nonneg fun _ _ => abs_nonneg _).trans
    (hc (Classical.arbitrary X) (Classical.arbitrary Y))
  refine E.endoRadius_le_of_vecNorm σ IsVecNorm.l1_norm hc0 fun x u => ?_
  simp only [mulVec, dotProduct, complexify_apply]
  calc ∑ y, ‖∑ y', ((omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' : ℂ) * u y'‖
      ≤ ∑ y, ∑ y', |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'| * ‖u y'‖ :=
        sum_le_sum fun y _ => (norm_sum_le _ _).trans_eq (sum_congr rfl fun y' _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs])
    _ = ∑ y', (∑ y, |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'|) * ‖u y'‖ := by
        rw [sum_comm]
        simp only [sum_mul]
    _ ≤ ∑ y', c * ‖u y'‖ :=
        sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right (hc x y') (norm_nonneg _)
    _ = c * ∑ y', ‖u y'‖ := (mul_sum _ _ _).symm

omit [DecidableEq X] [DecidableEq Y] in
/-- One step of `P_σ` contracts the within-`x` span by the Hajnal coefficient of `F_y(σ, ·)`. -/
theorem spy_Pmat_mulVec_le [Nonempty X] [Nonempty Y] (σ : X × Y → A) {α : ℝ}
    (hα : ∀ x y y', 1 - ∑ y'', min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤ α)
    (d : X × Y → ℝ) : spy (E.toMDP.Pmat σ *ᵥ d) ≤ α * spy d := by
  have hα0 : 0 ≤ α := by
    have h := hα (Classical.arbitrary X) (Classical.arbitrary Y) (Classical.arbitrary Y)
    simp only [min_self, (E.FyMat_isStochastic σ _).2, sub_self] at h
    exact h
  have hst := E.FxMat_isStochastic
  refine sup'_le _ _ fun x _ => sp_le fun y y' => ?_
  have hP : ∀ y, (E.toMDP.Pmat σ *ᵥ d) (x, y) =
      ∑ x', E.FxMat x x' * ∑ y'', E.FyMat σ x y y'' * d (x', y'') := fun y => by
    simp only [mulVec, dotProduct, Pmat_apply, Fintype.sum_prod_type, mul_sum]
    exact sum_congr rfl fun x' _ => sum_congr rfl fun y'' _ => by ring
  rw [hP, hP, ← sum_sub_distrib]
  calc ∑ x', (E.FxMat x x' * ∑ y'', E.FyMat σ x y y'' * d (x', y'') -
        E.FxMat x x' * ∑ y'', E.FyMat σ x y' y'' * d (x', y''))
      ≤ ∑ x', E.FxMat x x' * (α * spy d) := sum_le_sum fun x' _ => by
        rw [← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (hst.1 x x')
        have hd := dobrushin ((E.FyMat_isStochastic σ x).2 y) ((E.FyMat_isStochastic σ x).2 y')
          fun y'' => d (x', y'')
        have hs := sp_nonneg fun y'' => d (x', y'')
        have hc := mul_le_mul_of_nonneg_right (hα x y y') hs
        have hsy := mul_le_mul_of_nonneg_left (sp_le_spy d x') hα0
        linarith
    _ = α * spy d := by rw [← sum_mul, hst.2 x, one_mul]

/-- **Bray, Cor 2(e)**: the Hajnal (Dobrushin) coefficient of `F_y(σ, ·)` bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_hajnal [Nonempty X] [Nonempty Y] (σ : X × Y → A) {α : ℝ}
    (hα : ∀ x y y', 1 - ∑ y'', min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤ α) :
    endoRadius (E.toMDP.Pmat σ) ≤ α := by
  have hα0 : 0 ≤ α := by
    have h := hα (Classical.arbitrary X) (Classical.arbitrary Y) (Classical.arbitrary Y)
    simp only [min_self, (E.FyMat_isStochastic σ _).2, sub_self] at h
    exact h
  have hpow : ∀ (k : ℕ) (d : X × Y → ℝ), spy (E.toMDP.Pmat σ ^ k *ᵥ d) ≤ α ^ k * spy d := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
      intro d
      rw [pow_succ', ← mulVec_mulVec, pow_succ']
      calc spy (E.toMDP.Pmat σ *ᵥ (E.toMDP.Pmat σ ^ k *ᵥ d))
          ≤ α * spy (E.toMDP.Pmat σ ^ k *ᵥ d) := E.spy_Pmat_mulVec_le σ hα _
        _ ≤ α * (α ^ k * spy d) := mul_le_mul_of_nonneg_left (ih d) hα0
        _ = α * α ^ k * spy d := by ring
  unfold endoRadius
  refine specRad_le_of_norm_pow_le _ zero_lt_two hα0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(lamMat * E.toMDP.Pmat σ) ^ k *ᵥ w‖ ≤ 2 * α ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    linarith [norm_nonneg w]
  have e : (lamMat * E.toMDP.Pmat σ) ^ (k + 1) *ᵥ w = endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) := by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec,
      lamF_pow_endo (E.Pmat_preservesLift σ), mulVec_mulVec, ← pow_succ]
  rw [e]
  calc ‖endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w)‖ ≤ spy (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) :=
        norm_endo_le _
    _ ≤ α ^ (k + 1) * spy w := hpow _ _
    _ ≤ α ^ (k + 1) * (2 * ‖w‖) :=
        mul_le_mul_of_nonneg_left ((spy_le_sp w).trans (sp_le_two_norm w)) (pow_nonneg hα0 _)
    _ = 2 * α ^ (k + 1) * ‖w‖ := by ring

omit [DecidableEq X] [DecidableEq Y] in
/-- **Scrambling matrices have Hajnal coefficient below one** (Hajnal, 1958): if any two rows of
each `F_y(σ, x)` overlap, a single `α < 1` bounds every endogenous Dobrushin coefficient. -/
theorem exists_hajnal_lt_one [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    (hs : ∀ x y y', ∃ y'', 0 < min (E.FyMat σ x y y'') (E.FyMat σ x y' y'')) :
    ∃ α < 1, ∀ x y y', 1 - ∑ y'', min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤ α := by
  set f : X × Y × Y → ℝ := fun p =>
    1 - ∑ y'', min (E.FyMat σ p.1 p.2.1 y'') (E.FyMat σ p.1 p.2.2 y'')
  refine ⟨univ.sup' univ_nonempty f, ?_, fun x y y' => le_sup' f (mem_univ (x, y, y'))⟩
  rw [sup'_lt_iff]
  rintro ⟨x, y, y'⟩ -
  obtain ⟨y'', hy''⟩ := hs x y y'
  have hst := E.FyMat_isStochastic σ x
  have : min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤
      ∑ t, min (E.FyMat σ x y t) (E.FyMat σ x y' t) :=
    single_le_sum (f := fun t => min (E.FyMat σ x y t) (E.FyMat σ x y' t))
      (fun t _ => le_min (hst.1 _ _) (hst.1 _ _)) (mem_univ y'')
  simp only [f]
  linarith

/-- **Bray, Cor 3**: if `F_x` is not ergodic and every `F_y(σ, x)` is scrambling, then
`ρ(ΛP_σ) < σ(P_σ)`: endogenous iteration is strictly faster. -/
theorem endoRadius_lt_of_nonergodic_scrambling [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    (s₀ : X × Y)
    (hx : (∃ μ ∈ spectrum ℂ (complexify E.FxMat), μ ≠ 1 ∧ ‖μ‖ = 1) ∨
      ∃ v : X → ℂ, complexify E.FxMat *ᵥ v = v ∧ ∃ i j, v i ≠ v j)
    (hs : ∀ x y y', ∃ y'', 0 < min (E.FyMat σ x y y'') (E.FyMat σ x y' y'')) :
    endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀ := by
  obtain ⟨α, hα1, hα⟩ := E.exists_hajnal_lt_one σ hs
  calc endoRadius (E.toMDP.Pmat σ) ≤ α := E.endoRadius_le_hajnal σ hα
    _ < 1 := hα1
    _ ≤ subradius E.FxMat s₀.1 := one_le_subradius_of_nonergodic E.FxMat_isStochastic s₀.1 hx
    _ ≤ subradius (E.toMDP.Pmat σ) s₀ := E.subradius_FxMat_le σ s₀

/-- When `F_y(σ, x) = G` for every `x`, `P_σ = F_x ⊗ G`, so `P_σᵏ = F_xᵏ ⊗ Gᵏ`. -/
theorem Pmat_pow_mulVec_of_Fy_const (σ : X × Y → A) {G : Matrix Y Y ℝ}
    (hG : ∀ x, E.FyMat σ x = G) (j : ℕ) (w : X × Y → ℝ) (x : X) (y : Y) :
    (E.toMDP.Pmat σ ^ j *ᵥ w) (x, y) =
      ∑ x', (E.FxMat ^ j) x x' * (G ^ j *ᵥ fun y' => w (x', y')) y := by
  have hexp : ∀ (M : Matrix (X × Y) (X × Y) ℝ) (u : X × Y → ℝ) (s : X × Y),
      (M *ᵥ u) s = ∑ t, M s t * u t := fun _ _ _ => rfl
  have hexpY : ∀ (M : Matrix Y Y ℝ) (u : Y → ℝ) (y : Y), (M *ᵥ u) y = ∑ t, M y t * u t :=
    fun _ _ _ => rfl
  induction j generalizing x y with
  | zero => simp [one_apply]
  | succ j ih =>
    rw [pow_succ' (E.toMDP.Pmat σ), ← mulVec_mulVec, hexp, Fintype.sum_prod_type,
      pow_succ' E.FxMat, pow_succ' G]
    simp only [← mulVec_mulVec]
    simp only [Pmat_apply, hG, ih, mul_apply, hexpY G, mul_sum, sum_mul]
    calc _ = ∑ x1, ∑ x', ∑ y1, E.FxMat x x1 * G y y1 *
            ((E.FxMat ^ j) x1 x' * (G ^ j *ᵥ fun y' => w (x', y')) y1) :=
          sum_congr rfl fun x1 _ => sum_comm
      _ = ∑ x', ∑ x1, ∑ y1, E.FxMat x x1 * G y y1 *
            ((E.FxMat ^ j) x1 x' * (G ^ j *ᵥ fun y' => w (x', y')) y1) := sum_comm
      _ = ∑ x', ∑ y1, ∑ x1, E.FxMat x x1 * G y y1 *
            ((E.FxMat ^ j) x1 x' * (G ^ j *ᵥ fun y' => w (x', y')) y1) :=
          sum_congr rfl fun x' _ => sum_comm
      _ = _ := sum_congr rfl fun x' _ => sum_congr rfl fun y1 _ =>
          sum_congr rfl fun x1 _ => by ring

/-- **Bray, Cor 4**: if `F_y(σ, x) = G` for every `x`, then `ρ(ΛP_σ) ≤ σ(G)`. -/
theorem endoRadius_le_subradius_Fy [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    {G : Matrix Y Y ℝ} (hG : ∀ x, E.FyMat σ x = G) (y₀ : Y) :
    endoRadius (E.toMDP.Pmat σ) ≤ subradius G y₀ := by
  have hGs : IsStochastic G := by
    rw [← hG (Classical.arbitrary X)]
    exact E.FyMat_isStochastic σ _
  refine le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le hGs y₀ hγ
  have hγ0 : 0 ≤ γ := (specRad_nonneg _).trans hγ.le
  unfold endoRadius
  refine specRad_le_of_norm_pow_le _ (K := 1 + 2 * C) (by positivity) hγ0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(lamMat * E.toMDP.Pmat σ) ^ k *ᵥ w‖ ≤ (1 + 2 * C) * γ ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    nlinarith [norm_nonneg w]
  have e : (lamMat * E.toMDP.Pmat σ) ^ (k + 1) *ᵥ w = endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) := by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec,
      lamF_pow_endo (E.Pmat_preservesLift σ), mulVec_mulVec, ← pow_succ]
  rw [e]
  have hst := E.FxMat_isStochastic.pow (k + 1)
  have hspy : spy (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) ≤ C * γ ^ (k + 1) * (2 * ‖w‖) := by
    refine sup'_le _ _ fun x _ => sp_le fun y y' => ?_
    rw [E.Pmat_pow_mulVec_of_Fy_const σ hG, E.Pmat_pow_mulVec_of_Fy_const σ hG,
      ← sum_sub_distrib]
    calc ∑ x', ((E.FxMat ^ (k + 1)) x x' * (G ^ (k + 1) *ᵥ fun y' => w (x', y')) y -
          (E.FxMat ^ (k + 1)) x x' * (G ^ (k + 1) *ᵥ fun y' => w (x', y')) y')
        ≤ ∑ x', (E.FxMat ^ (k + 1)) x x' * (C * γ ^ (k + 1) * (2 * ‖w‖)) :=
          sum_le_sum fun x' _ => by
            rw [← mul_sub]
            refine mul_le_mul_of_nonneg_left ?_ (hst.1 x x')
            refine (sub_le_sp _ y y').trans ((hC _ _).trans ?_)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (sp_le_two_norm _).trans ?_
            have : ‖fun y' => w (x', y')‖ ≤ ‖w‖ :=
              (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun y' => norm_le_pi_norm w (x', y')
            linarith
      _ = C * γ ^ (k + 1) * (2 * ‖w‖) := by rw [← sum_mul, hst.2 x, one_mul]
  calc ‖endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w)‖ ≤ spy (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) :=
        norm_endo_le _
    _ ≤ C * γ ^ (k + 1) * (2 * ‖w‖) := hspy
    _ ≤ (1 + 2 * C) * γ ^ (k + 1) * ‖w‖ := by
        nlinarith [mul_nonneg (pow_nonneg hγ0 (k + 1)) (norm_nonneg w)]

/-- **Bray, Cor 4 (strict form)**: if `F_y(σ, x) = G` for every `x` and `σ(F_x) > σ(G)`, then
`ρ(ΛP_σ) < σ(P_σ)`. -/
theorem endoRadius_lt_of_Fy_const [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    {G : Matrix Y Y ℝ} (hG : ∀ x, E.FyMat σ x = G) (s₀ : X × Y)
    (hlt : subradius G s₀.2 < subradius E.FxMat s₀.1) :
    endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀ :=
  (E.endoRadius_le_subradius_Fy σ hG s₀.2).trans_lt (hlt.trans_le (E.subradius_FxMat_le σ s₀))

end ExoMDP

end DPExtensions.RelativeValueIteration

set_option linter.style.longLine false
#print axioms DPExtensions.RelativeValueIteration.sp
#print axioms DPExtensions.RelativeValueIteration.sub_le_sp
#print axioms DPExtensions.RelativeValueIteration.abs_sub_le_sp
#print axioms DPExtensions.RelativeValueIteration.sp_nonneg
#print axioms DPExtensions.RelativeValueIteration.sp_le
#print axioms DPExtensions.RelativeValueIteration.sp_add_const
#print axioms DPExtensions.RelativeValueIteration.sp_neg
#print axioms DPExtensions.RelativeValueIteration.le_sup'_sp
#print axioms DPExtensions.RelativeValueIteration.inf'_le_sp
#print axioms DPExtensions.RelativeValueIteration.dobrushin
#print axioms DPExtensions.RelativeValueIteration.MDP
#print axioms DPExtensions.RelativeValueIteration.MDP.mk
#print axioms DPExtensions.RelativeValueIteration.MDP.Γ
#print axioms DPExtensions.RelativeValueIteration.MDP.Γ_nonempty
#print axioms DPExtensions.RelativeValueIteration.MDP.r
#print axioms DPExtensions.RelativeValueIteration.MDP.β
#print axioms DPExtensions.RelativeValueIteration.MDP.β_nonneg
#print axioms DPExtensions.RelativeValueIteration.MDP.β_le_one
#print axioms DPExtensions.RelativeValueIteration.MDP.P
#print axioms DPExtensions.RelativeValueIteration.MDP.P_nonneg
#print axioms DPExtensions.RelativeValueIteration.MDP.P_sum
#print axioms DPExtensions.RelativeValueIteration.MDP.Q
#print axioms DPExtensions.RelativeValueIteration.MDP.T
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ
#print axioms DPExtensions.RelativeValueIteration.MDP.IsGreedy
#print axioms DPExtensions.RelativeValueIteration.MDP.IsPolicy
#print axioms DPExtensions.RelativeValueIteration.MDP.exists_greedyAct
#print axioms DPExtensions.RelativeValueIteration.MDP.exists_greedy
#print axioms DPExtensions.RelativeValueIteration.MDP.Q_le_T
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_eq_T_of_greedy
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_le_T
#print axioms DPExtensions.RelativeValueIteration.MDP.Q_add_const
#print axioms DPExtensions.RelativeValueIteration.MDP.T_add_const
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_add_const
#print axioms DPExtensions.RelativeValueIteration.MDP.isGreedy_add_const_iff
#print axioms DPExtensions.RelativeValueIteration.MDP.T_iterate_add_const
#print axioms DPExtensions.RelativeValueIteration.MDP.rel
#print axioms DPExtensions.RelativeValueIteration.MDP.rel_add_const
#print axioms DPExtensions.RelativeValueIteration.MDP.relT_iterate
#print axioms DPExtensions.RelativeValueIteration.MDP.Q_sub_Q
#print axioms DPExtensions.RelativeValueIteration.MDP.sp_T_sub_le
#print axioms DPExtensions.RelativeValueIteration.MDP.abs_Q_sub_le
#print axioms DPExtensions.RelativeValueIteration.MDP.norm_T_sub_le
#print axioms DPExtensions.RelativeValueIteration.MDP.norm_Tσ_sub_le
#print axioms DPExtensions.RelativeValueIteration.MDP.T_mono
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_mono
#print axioms DPExtensions.RelativeValueIteration.MDP.contracting_T
#print axioms DPExtensions.RelativeValueIteration.MDP.contracting_Tσ
#print axioms DPExtensions.RelativeValueIteration.MDP.vstar
#print axioms DPExtensions.RelativeValueIteration.MDP.vσ
#print axioms DPExtensions.RelativeValueIteration.MDP.T_vstar
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_vσ
#print axioms DPExtensions.RelativeValueIteration.MDP.le_vσ_of_le
#print axioms DPExtensions.RelativeValueIteration.MDP.le_vstar_of_le
#print axioms DPExtensions.RelativeValueIteration.MDP.vstar_le_of_T_le
#print axioms DPExtensions.RelativeValueIteration.MDP.vσ_le_vstar
#print axioms DPExtensions.RelativeValueIteration.MDP.dobrushin_le_one
#print axioms DPExtensions.RelativeValueIteration.MDP.alpha_nonneg
#print axioms DPExtensions.RelativeValueIteration.MDP.sp_T_iterate_sub_le
#print axioms DPExtensions.RelativeValueIteration.MDP.sp_iterate_sub_vstar
#print axioms DPExtensions.RelativeValueIteration.MDP.rel_converges
#print axioms DPExtensions.RelativeValueIteration.MDP.policy_error
#print axioms DPExtensions.RelativeValueIteration.MDP.relIter
#print axioms DPExtensions.RelativeValueIteration.MDP.relIter_succ
#print axioms DPExtensions.RelativeValueIteration.MDP.sp_T_relIter_sub
#print axioms DPExtensions.RelativeValueIteration.MDP.stopping_rule
#print axioms DPExtensions.RelativeValueIteration.MDP.stopping_rule_sup
#print axioms DPExtensions.RelativeValueIteration.MDP.sp_relIter_succ_sub_le
#print axioms DPExtensions.RelativeValueIteration.MDP.stopping_eventually
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_iterate_add_const
#print axioms DPExtensions.RelativeValueIteration.MDP.T_iterate_of_poisson
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_iterate_le_T_iterate
#print axioms DPExtensions.RelativeValueIteration.MDP.norm_bound
#print axioms DPExtensions.RelativeValueIteration.MDP.avg_upper
#print axioms DPExtensions.RelativeValueIteration.MDP.avg_greedy
#print axioms DPExtensions.RelativeValueIteration.MDP.avg_tendsto
#print axioms DPExtensions.RelativeValueIteration.MDP.gain_unique
#print axioms DPExtensions.RelativeValueIteration.MDP.white
#print axioms DPExtensions.RelativeValueIteration.ExoMDP
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.mk
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Γ
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Γ_nonempty
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.r
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.β
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.β_nonneg
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.β_le_one
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fx
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fx_nonneg
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fx_sum
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fy
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fy_nonneg
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fy_sum
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.toMDP
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Fxc
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.sum_P_mul
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Q_add_lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.T_add_lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.isGreedy_add_lift_iff
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.mean
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_decomp
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.mean_add_lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_add_lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.isGreedy_endo_iff
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoT_iterate
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_sub
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.sp_le_spy
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_nonneg
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_le_sp
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.abs_endo_le_sp
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.abs_endo_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.alphaY_nonneg
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_T_sub_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoCoeff_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_T_iterate_sub_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_converges
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.vstar_recover
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.mean_unique
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.optimal_of_greedy_endo
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_policy_error
#print axioms DPExtensions.RelativeValueIteration.swapModel
#print axioms DPExtensions.RelativeValueIteration.swap_T
#print axioms DPExtensions.RelativeValueIteration.swap_dobrushin_ge
#print axioms DPExtensions.RelativeValueIteration.sp_bool_unit
#print axioms DPExtensions.RelativeValueIteration.swap_sp_iterate
#print axioms DPExtensions.RelativeValueIteration.swap_sp_vstar
#print axioms DPExtensions.RelativeValueIteration.swap_endo_exact
#print axioms DPExtensions.RelativeValueIteration.relative_slow_endogenous_exact
#print axioms DPExtensions.RelativeValueIteration.MDP.pi_improve
#print axioms DPExtensions.RelativeValueIteration.MDP.eq_vstar_of_T_eq
#print axioms DPExtensions.RelativeValueIteration.MDP.vσ_eq_vstar_of_stall
#print axioms DPExtensions.RelativeValueIteration.MDP.pi_mono
#print axioms DPExtensions.RelativeValueIteration.MDP.pi_terminates
#print axioms DPExtensions.RelativeValueIteration.MDP.isGreedy_rel_iff
#print axioms DPExtensions.RelativeValueIteration.MDP.relPI_terminates
#print axioms DPExtensions.RelativeValueIteration.MDP.pi_residual_le
#print axioms DPExtensions.RelativeValueIteration.MDP.relPI_stopping
#print axioms DPExtensions.RelativeValueIteration.MDP.relPI_bray
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.exoMDP
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.exists_exo_solution
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.policy_error_endo
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoPI_terminates
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_T_endo_sub
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoPI_stopping
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoPI_bray
#print axioms DPExtensions.RelativeValueIteration.complexify
#print axioms DPExtensions.RelativeValueIteration.complexify_apply
#print axioms DPExtensions.RelativeValueIteration.complexify_pow
#print axioms DPExtensions.RelativeValueIteration.complexify_mul
#print axioms DPExtensions.RelativeValueIteration.nnnorm_complexify
#print axioms DPExtensions.RelativeValueIteration.norm_complexify
#print axioms DPExtensions.RelativeValueIteration.specRad
#print axioms DPExtensions.RelativeValueIteration.spectralRadius_complexify_ne_top
#print axioms DPExtensions.RelativeValueIteration.specRad_nonneg
#print axioms DPExtensions.RelativeValueIteration.mem_spectrum_iff_eigenpair
#print axioms DPExtensions.RelativeValueIteration.tendsto_norm_pow_rpow
#print axioms DPExtensions.RelativeValueIteration.eventually_norm_pow_le
#print axioms DPExtensions.RelativeValueIteration.exists_norm_pow_le
#print axioms DPExtensions.RelativeValueIteration.specRad_le_of_norm_pow_le
#print axioms DPExtensions.RelativeValueIteration.deltaMat
#print axioms DPExtensions.RelativeValueIteration.IsStochastic
#print axioms DPExtensions.RelativeValueIteration.subradius
#print axioms DPExtensions.RelativeValueIteration.deltaMat_mulVec
#print axioms DPExtensions.RelativeValueIteration.cdelta_mulVec
#print axioms DPExtensions.RelativeValueIteration.mulVec_const
#print axioms DPExtensions.RelativeValueIteration.cmulVec_const
#print axioms DPExtensions.RelativeValueIteration.norm_cmulVec_le
#print axioms DPExtensions.RelativeValueIteration.no_jordan_one
#print axioms DPExtensions.RelativeValueIteration.complexify_deltaQ_mulVec
#print axioms DPExtensions.RelativeValueIteration.mem_spectrum_deltaQ_iff
#print axioms DPExtensions.RelativeValueIteration.spectralRadius_deltaQ
#print axioms DPExtensions.RelativeValueIteration.sp_deltaMat_mulVec
#print axioms DPExtensions.RelativeValueIteration.norm_deltaMat_mulVec_le
#print axioms DPExtensions.RelativeValueIteration.sp_le_two_norm
#print axioms DPExtensions.RelativeValueIteration.deltaQ_pow_mulVec
#print axioms DPExtensions.RelativeValueIteration.sp_pow_mulVec_le
#print axioms DPExtensions.RelativeValueIteration.subradius_le_dobrushin
#print axioms DPExtensions.RelativeValueIteration.sp_mul_le
#print axioms DPExtensions.RelativeValueIteration.MDP.Pmat
#print axioms DPExtensions.RelativeValueIteration.MDP.Pmat_isStochastic
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_sub
#print axioms DPExtensions.RelativeValueIteration.MDP.Tσ_iterate_sub
#print axioms DPExtensions.RelativeValueIteration.MDP.sp_policy_eval_le
#print axioms DPExtensions.RelativeValueIteration.MDP.eventually_T_eq_Tσ
#print axioms DPExtensions.RelativeValueIteration.MDP.norm_iterate_sub_vstar_le
#print axioms DPExtensions.RelativeValueIteration.MDP.eventually_linear
#print axioms DPExtensions.RelativeValueIteration.MDP.relative_asymptotic_rate
#print axioms DPExtensions.RelativeValueIteration.MDP.rel_asymptotic_rate
#print axioms DPExtensions.RelativeValueIteration.MDP.level_rate_lower
#print axioms DPExtensions.RelativeValueIteration.MDP.subradius_policy_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_idem
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.PreservesLift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_mulVec_endo
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_le_two_norm_endo
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.norm_endo_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_mul_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.lamMat
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.lamMat_mulVec
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.PreservesLift.pow
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.lamF_pow_endo
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_pow_mulVec_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_subradius
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Pmat_preservesLift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_policy_eval_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_asymptotic_rate
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_values_asymptotic_rate
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_policy_le
#print axioms DPExtensions.RelativeValueIteration.specRad_le_of_eigen
#print axioms DPExtensions.RelativeValueIteration.norm_le_specRad
#print axioms DPExtensions.RelativeValueIteration.specRad_mono_of_spectrum
#print axioms DPExtensions.RelativeValueIteration.IsStochastic.pow
#print axioms DPExtensions.RelativeValueIteration.one_le_subradius_of_nonergodic
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.zero
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.nonneg
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.pos
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.sum_le
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.smul_real
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.sup_norm
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.l1_norm
#print axioms DPExtensions.RelativeValueIteration.IsVecNorm.l2_norm
#print axioms DPExtensions.RelativeValueIteration.norm_apply_le_singularValues_zero
#print axioms DPExtensions.RelativeValueIteration.sum_sq_mulVec_le_singularValues
#print axioms DPExtensions.RelativeValueIteration.sum_sq_norm_cmulVec_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.omegaMat
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.comega_mulVec
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.omega_mulVec
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.omega_mulVec_const
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.omega_mulVec_add_const
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.norm_omega_mulVec_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.sp_omega_mulVec
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.omegaF_pow_mulVec_omega
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.specRad_omega_eq_subradius
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.clamMat_mulVec
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.FxMat
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.FxMat_isStochastic
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.FyMat
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.FyMat_isStochastic
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Pmat_apply
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.cPmat_mulVec_lift
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spectrum_exo_subset
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.subradius_FxMat_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.clamP_mulVec
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_of_vecNorm
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_lt_subradius_of_vecNorm
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_strictly_faster
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endo_eval_strictly_faster
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_rowSum
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_l2
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_frobenius
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_singularValue
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_colSum
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.spy_Pmat_mulVec_le
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_hajnal
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.exists_hajnal_lt_one
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_lt_of_nonergodic_scrambling
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.Pmat_pow_mulVec_of_Fy_const
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_le_subradius_Fy
#print axioms DPExtensions.RelativeValueIteration.ExoMDP.endoRadius_lt_of_Fy_const
