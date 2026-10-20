/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.AverageReward

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
