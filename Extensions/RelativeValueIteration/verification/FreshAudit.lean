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
