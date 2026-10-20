import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The value of information: Blackwell's sufficiency theorem

Blackwell (1951, 1953); Marschak and Miyasawa (1968).

A state `θ ∈ Θ` has prior `π`. An **experiment** `P(θ, y)` gives the probability of signal `y` in
state `θ`. A **garbling** is a Markov matrix `M(y, y')`, and `PM` is the experiment that reports
`y'` drawn from `M(y, ·)`. A decision problem is a finite set of actions `A` and a payoff
`u(a, θ)`; with signal `y` the agent maximizes `∑_θ π(θ)P(θ, y)u(a, θ)`, which is the posterior
expected payoff times the probability of `y`, so the value of the experiment is
`V_u(P) = ∑_y max_a ∑_θ π(θ)P(θ, y)u(a, θ)` — no division by signal probabilities is needed.

* `value_garble_le` (**Blackwell**): garbling never helps, `V_u(PM) ≤ V_u(P)`, in every decision
  problem.
* `sublinear_garble_le`: more generally, `∑_{y'} Φ(μ_{PM}(y')) ≤ ∑_y Φ(μ_P(y))` for every sublinear
  `Φ` of the unnormalized posteriors `μ_P(y) = π(·)P(·, y)`: the posterior distribution of `P` is a
  mean-preserving spread of that of `PM`. Decision values are the case
  `Φ(μ) = max_a ∑_θ μ(θ)u(a, θ)`.
* `value_noInfo_le`, `value_le_perfect`: information has nonnegative value, and no experiment beats
  observing the state.
-/

open Finset

namespace DPExtensions.ValueOfInformation

variable {Θ Y Y' A : Type*} [Fintype Θ] [Fintype Y] [Fintype Y'] [Fintype A] [Nonempty A]

/-- A Markov matrix. -/
def IsStochastic {Y Y' : Type*} [Fintype Y'] (M : Y → Y' → ℝ) : Prop :=
  (∀ y y', 0 ≤ M y y') ∧ ∀ y, ∑ y', M y y' = 1

/-- The garbled experiment `PM`. -/
def garble (P : Θ → Y → ℝ) (M : Y → Y' → ℝ) (θ : Θ) (y' : Y') : ℝ := ∑ y, P θ y * M y y'

/-- The unnormalized posterior after signal `y`, `μ_P(y)(θ) = π(θ)P(θ, y)`. -/
def joint (π : Θ → ℝ) (P : Θ → Y → ℝ) (y : Y) (θ : Θ) : ℝ := π θ * P θ y

/-- The expected payoff of action `a` jointly with signal `y`. -/
def payoff (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) (y : Y) (a : A) : ℝ :=
  ∑ θ, π θ * P θ y * u a θ

/-- The value of the experiment `P` in the decision problem `u`. -/
noncomputable def value (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) : ℝ :=
  ∑ y, univ.sup' univ_nonempty (payoff π u P y)

omit [Fintype Y'] [Fintype A] [Nonempty A] in
theorem payoff_garble (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) (M : Y → Y' → ℝ) (y' : Y')
    (a : A) : payoff π u (garble P M) y' a = ∑ y, M y y' * payoff π u P y a := by
  simp only [payoff, garble, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun θ _ => by ring

omit [Fintype Y'] in
/-- **Blackwell's theorem (sufficiency)**: garbling an experiment never raises its value. -/
theorem value_garble_le (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) {M : Y → Y' → ℝ}
    [Fintype Y'] (hM : IsStochastic M) : value π u (garble P M) ≤ value π u P := by
  simp only [value]
  calc ∑ y', univ.sup' univ_nonempty (payoff π u (garble P M) y')
      ≤ ∑ y', ∑ y, M y y' * univ.sup' univ_nonempty (payoff π u P y) := by
        refine sum_le_sum fun y' _ => sup'_le _ _ fun a _ => ?_
        rw [payoff_garble]
        exact sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (le_sup' (payoff π u P y) (mem_univ a)) (hM.1 y y')
    _ = ∑ y, univ.sup' univ_nonempty (payoff π u P y) := by
        rw [sum_comm]
        exact sum_congr rfl fun y _ => by rw [← sum_mul, hM.2 y, one_mul]

/-- A sublinear function: subadditive and positively homogeneous. -/
def IsSublinear (Φ : (Θ → ℝ) → ℝ) : Prop :=
  (∀ v w, Φ (v + w) ≤ Φ v + Φ w) ∧ ∀ (c : ℝ) v, 0 ≤ c → Φ (c • v) = c * Φ v

omit [Fintype Θ] in
theorem IsSublinear.sum_le {Φ : (Θ → ℝ) → ℝ} (hΦ : IsSublinear Φ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (v : ι → Θ → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    Φ (∑ i ∈ s, c i • v i) ≤ ∑ i ∈ s, c i * Φ (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hΦ.2 0 0 le_rfl
    rw [smul_zero, zero_mul] at h
    simp [h]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    refine (hΦ.1 _ _).trans ?_
    rw [hΦ.2 _ _ (hc i (mem_insert_self i s))]
    exact add_le_add le_rfl (ih fun j hj => hc j (mem_insert_of_mem hj))

omit [Fintype Θ] [Fintype Y'] in
theorem joint_garble (π : Θ → ℝ) (P : Θ → Y → ℝ) (M : Y → Y' → ℝ) (y' : Y') :
    joint π (garble P M) y' = ∑ y, M y y' • joint π P y := by
  funext θ
  simp only [joint, garble, mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_congr rfl fun y _ => by ring

omit [Fintype Θ] [Fintype Y'] in
/-- **Garbling contracts posteriors**: for every sublinear `Φ`,
`∑_{y'} Φ(μ_{PM}(y')) ≤ ∑_y Φ(μ_P(y))`. -/
theorem sublinear_garble_le (π : Θ → ℝ) (P : Θ → Y → ℝ) {M : Y → Y' → ℝ} [Fintype Y']
    (hM : IsStochastic M) {Φ : (Θ → ℝ) → ℝ} (hΦ : IsSublinear Φ) :
    ∑ y', Φ (joint π (garble P M) y') ≤ ∑ y, Φ (joint π P y) := by
  calc ∑ y', Φ (joint π (garble P M) y') ≤ ∑ y', ∑ y, M y y' * Φ (joint π P y) := by
        refine sum_le_sum fun y' _ => ?_
        rw [joint_garble]
        exact hΦ.sum_le _ _ _ fun y _ => hM.1 y y'
    _ = ∑ y, Φ (joint π P y) := by
        rw [sum_comm]
        exact sum_congr rfl fun y _ => by rw [← sum_mul, hM.2 y, one_mul]

/-- The decision value `Φ_u(μ) = max_a ∑_θ μ(θ)u(a, θ)` is sublinear, and `V_u(P)` is
`∑_y Φ_u(μ_P(y))`. -/
theorem decisionValue_sublinear (u : A → Θ → ℝ) :
    IsSublinear fun μ : Θ → ℝ => univ.sup' univ_nonempty fun a => ∑ θ, μ θ * u a θ := by
  refine ⟨fun v w => sup'_le _ _ fun a _ => ?_, fun c v hc => ?_⟩
  · simp only [Pi.add_apply, add_mul, sum_add_distrib]
    exact add_le_add (le_sup' (fun a => ∑ θ, v θ * u a θ) (mem_univ a))
      (le_sup' (fun a => ∑ θ, w θ * u a θ) (mem_univ a))
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
    exact (Finset.mul₀_sup' hc _ _ _).symm

/-- The uninformative experiment: a single signal. -/
def noInfo (_ : Θ) (_ : Unit) : ℝ := 1

omit [Fintype Y] in
/-- With a single signal, the value is `max_a ∑_θ π(θ)u(a, θ)`. -/
theorem value_noInfo (π : Θ → ℝ) (u : A → Θ → ℝ) :
    value π u (noInfo (Θ := Θ)) = univ.sup' univ_nonempty fun a => ∑ θ, π θ * u a θ := by
  simp only [value, Finset.univ_unique, Finset.sum_singleton]
  congr 1
  funext a
  simp [payoff, noInfo]

/-- **Information has nonnegative value.** -/
theorem value_noInfo_le (π : Θ → ℝ) (u : A → Θ → ℝ) {P : Θ → Y → ℝ}
    (hP : ∀ θ, ∑ y, P θ y = 1) : value π u (noInfo (Θ := Θ)) ≤ value π u P := by
  have e : (noInfo (Θ := Θ)) = garble P fun _ _ => 1 := by
    funext θ _
    simp [garble, noInfo, hP θ]
  rw [e]
  exact value_garble_le π u P ⟨fun _ _ => zero_le_one, fun _ => by simp⟩

/-- Observing the state. -/
def perfect [DecidableEq Θ] (θ θ' : Θ) : ℝ := if θ = θ' then 1 else 0

/-- **No experiment beats observing the state**: `V_u(P) ≤ ∑_θ π(θ) max_a u(a, θ)` for
`π ≥ 0`. -/
theorem value_le_perfect {π : Θ → ℝ} (hπ : ∀ θ, 0 ≤ π θ) (u : A → Θ → ℝ)
    {P : Θ → Y → ℝ} (hP : IsStochastic P) :
    value π u P ≤ ∑ θ, π θ * univ.sup' univ_nonempty fun a => u a θ := by
  classical
  have e : P = garble perfect P := by
    funext θ y
    simp [garble, perfect]
  rw [e]
  refine (value_garble_le π u perfect hP).trans (le_of_eq ?_)
  refine sum_congr rfl fun θ _ => ?_
  have e2 : payoff π u perfect θ = fun a => π θ * u a θ := by
    funext a
    simp [payoff, perfect]
  rw [e2]
  exact (Finset.mul₀_sup' (hπ θ) _ _ _).symm

end DPExtensions.ValueOfInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Blackwell's theorem: the converse

Blackwell (1951, 1953). If an experiment `P` is at least as valuable as `Q` in **every** decision
problem, then `Q` is a garbling of `P`.

* `blackwell_converse`: if `V_u(Q) ≤ V_u(P)` for every payoff `u` on the action set `Y'`, there is
  a Markov matrix `M` with `π(θ)Q(θ, y') = π(θ)(PM)(θ, y')`. The proof separates the unnormalized
  posteriors of `Q` from the compact convex set of those of garblings of `P`; the separating
  functional is a payoff `u`, and the best garbling for it is the decision rule optimal under `P`.
* `blackwell`: with a full-support prior, `P` is more valuable than `Q` in every decision problem
  iff `Q = PM` for a Markov matrix `M`.
-/

open Finset

namespace DPExtensions.ValueOfInformation

variable {Θ Y Y' : Type*} [Fintype Θ] [Fintype Y] [Fintype Y']

/-- The unnormalized posteriors of the garbling `PM`, as a linear function of `M`. -/
def garbleMap (π : Θ → ℝ) (P : Θ → Y → ℝ) : (Y × Y' → ℝ) →ₗ[ℝ] (Y' × Θ → ℝ) where
  toFun M p := ∑ y, M (y, p.1) * (π p.2 * P p.2 y)
  map_add' M N := by
    funext p
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c M := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

/-- Markov matrices `Y → Y'`, as functions on `Y × Y'`. -/
def stochSet : Set (Y × Y' → ℝ) := {M | (∀ p, 0 ≤ M p) ∧ ∀ y, ∑ y', M (y, y') = 1}

omit [Fintype Y] in
theorem convex_stochSet : Convex ℝ (stochSet : Set (Y × Y' → ℝ)) := by
  intro M hM N hN a b ha hb hab
  refine ⟨fun p => ?_, fun y => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hM.1 p)) (mul_nonneg hb (hN.1 p))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hM.2 y,
      hN.2 y, mul_one, hab]

omit [Fintype Y] in
theorem isCompact_stochSet [Finite Y] : IsCompact (stochSet : Set (Y × Y' → ℝ)) := by
  have := Fintype.ofFinite Y
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have e : (stochSet : Set (Y × Y' → ℝ)) =
        (⋂ p, {M : Y × Y' → ℝ | 0 ≤ M p}) ∩ ⋂ y, {M : Y × Y' → ℝ | ∑ y', M (y, y') = 1} := by
      ext M
      simp [stochSet]
    rw [e]
    exact (isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)).inter
      (isClosed_iInter fun y => isClosed_eq
        (continuous_finsetSum _ fun y' _ => continuous_apply (y, y')) continuous_const)
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun M hM => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hM.1 p), ← hM.2 p.1]
    exact single_le_sum (f := fun y' => M (p.1, y')) (fun y' _ => hM.1 _) (mem_univ p.2)

/-- **Blackwell's theorem (converse)**: if `P` is at least as valuable as `Q` in every decision
problem with action set `Y'`, then the unnormalized posteriors of `Q` are those of a garbling of
`P`. -/
theorem blackwell_converse [Nonempty Y'] (π : Θ → ℝ) (P : Θ → Y → ℝ)
    (Q : Θ → Y' → ℝ) (h : ∀ u : Y' → Θ → ℝ, value π u Q ≤ value π u P) :
    ∃ M : Y → Y' → ℝ, IsStochastic M ∧ ∀ y' θ, π θ * Q θ y' = π θ * garble P M θ y' := by
  classical
  set L := garbleMap (Y' := Y') π P
  set μQ : Y' × Θ → ℝ := fun p => π p.2 * Q p.2 p.1
  by_cases hmem : μQ ∈ L '' stochSet
  · obtain ⟨M, hM, hLM⟩ := hmem
    refine ⟨fun y y' => M (y, y'), ⟨fun y y' => hM.1 _, hM.2⟩, fun y' θ => ?_⟩
    have := congrFun hLM (y', θ)
    simp only [L, garbleMap, LinearMap.coe_mk, AddHom.coe_mk, μQ] at this
    rw [← this, garble, mul_sum]
    exact sum_congr rfl fun y _ => by ring
  exfalso
  have hconv : Convex ℝ (L '' stochSet) := convex_stochSet.linear_image L
  have hclosed : IsClosed (L '' stochSet) :=
    (isCompact_stochSet.image L.continuous_of_finiteDimensional).isClosed
  obtain ⟨f, c, hfC, hfQ⟩ := geometric_hahn_banach_closed_point hconv hclosed hmem
  -- the separating functional as a payoff
  set w : Y' → Θ → ℝ := fun a θ => f fun p => if (a, θ) = p then 1 else 0
  have hf : ∀ e : Y' × Θ → ℝ, f e = ∑ p, e p * w p.1 p.2 := fun e => by
    have h1 := (f : (Y' × Θ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ e
    simp only [ContinuousLinearMap.coe_coe] at h1
    rw [h1]
    exact sum_congr rfl fun p _ => by simp [w, smul_eq_mul]
  -- `f(μ_Q) ≤ V_w(Q)`
  have hQ : f μQ ≤ value π w Q := by
    rw [hf, Fintype.sum_prod_type, value]
    refine sum_le_sum fun y' _ => le_trans (le_of_eq ?_) (le_sup' (payoff π w Q y') (mem_univ y'))
    simp only [μQ, payoff]
  -- the decision rule optimal under `P` attains `V_w(P)` as a garbling
  have hbest : ∀ y, ∃ a, univ.sup' univ_nonempty (payoff π w P y) = payoff π w P y a := by
    intro y
    obtain ⟨a, -, ha⟩ := exists_max_image univ (payoff π w P y) univ_nonempty
    exact ⟨a, le_antisymm (sup'_le _ _ fun b _ => ha b (mem_univ b))
      (le_sup' (payoff π w P y) (mem_univ a))⟩
  choose act hact using hbest
  set Mstar : Y × Y' → ℝ := fun p => if p.2 = act p.1 then 1 else 0
  have hMstar : Mstar ∈ stochSet := ⟨fun p => by simp only [Mstar]; split_ifs <;> norm_num,
    fun y => by simp [Mstar]⟩
  have hP : f (L Mstar) = value π w P := by
    rw [hf, Fintype.sum_prod_type, value]
    have e1 : ∀ y' θ, L Mstar (y', θ) * w y' θ =
        ∑ y, if y' = act y then π θ * P θ y * w y' θ else 0 := by
      intro y' θ
      simp only [L, garbleMap, LinearMap.coe_mk, AddHom.coe_mk, Mstar, sum_mul]
      refine sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    simp only [e1]
    calc ∑ y', ∑ θ, ∑ y, (if y' = act y then π θ * P θ y * w y' θ else 0)
        = ∑ y', ∑ y, ∑ θ, (if y' = act y then π θ * P θ y * w y' θ else 0) :=
          sum_congr rfl fun y' _ => sum_comm
      _ = ∑ y, ∑ y', ∑ θ, (if y' = act y then π θ * P θ y * w y' θ else 0) := sum_comm
      _ = ∑ y, payoff π w P y (act y) := sum_congr rfl fun y _ => by
          have e2 : ∀ y', ∑ θ, (if y' = act y then π θ * P θ y * w y' θ else 0) =
              if y' = act y then ∑ θ, π θ * P θ y * w y' θ else 0 := fun y' => by
            split_ifs <;> simp
          simp only [e2, sum_ite_eq', mem_univ, ↓reduceIte, payoff]
      _ = ∑ y, univ.sup' univ_nonempty (payoff π w P y) := sum_congr rfl fun y _ => (hact y).symm
  have h1 := hfC (L Mstar) ⟨Mstar, hMstar, rfl⟩
  have h2 := h w
  linarith

/-- **Blackwell's theorem**: with a full-support prior, `P` is at least as valuable as `Q` in
every decision problem with action set `Y'` iff `Q` is a garbling of `P`. -/
theorem blackwell [Nonempty Y'] {π : Θ → ℝ} (hπ : ∀ θ, 0 < π θ)
    (P : Θ → Y → ℝ) (Q : Θ → Y' → ℝ) :
    (∀ u : Y' → Θ → ℝ, value π u Q ≤ value π u P) ↔
      ∃ M : Y → Y' → ℝ, IsStochastic M ∧ Q = garble P M := by
  constructor
  · intro h
    obtain ⟨M, hM, hQ⟩ := blackwell_converse π P Q h
    exact ⟨M, hM, funext fun θ => funext fun y' =>
      mul_left_cancel₀ (hπ θ).ne' (hQ y' θ)⟩
  · rintro ⟨M, hM, rfl⟩ u
    exact value_garble_le π u P hM

end DPExtensions.ValueOfInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Binary signals: more accurate is more valuable

A binary state `θ ∈ {false, true}` and a binary signal that matches the state with probability
`q` (`binExp q`), as in models of noisy information, expert advice or test accuracy.

* `binExp_garble`: for `1/2 < q` and `1/2 ≤ q' ≤ q`, the less accurate experiment is a garbling
  of the more accurate one: pass the signal through a binary channel of accuracy
  `(q + q' − 1)/(2q − 1)`.
* `value_mono_accuracy`: so the more accurate signal is at least as valuable in every decision
  problem, with every prior (Blackwell).
* `value_guess`, `value_strict`: in the problem of guessing the state with a uniform prior the
  value is `max(q, 1 − q)`, so a strictly more accurate signal is strictly more valuable.
-/

open Finset

namespace DPExtensions.ValueOfInformation

/-- The binary experiment that reports the state with probability `q`. -/
def binExp (q : ℝ) (θ y : Bool) : ℝ := if θ = y then q else 1 - q

theorem binExp_isStochastic {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsStochastic (binExp q) :=
  ⟨fun θ y => by simp only [binExp]; split_ifs <;> linarith, fun θ => by
    cases θ <;> simp [binExp]⟩

/-- **A less accurate binary signal is a garbling of a more accurate one.** -/
theorem binExp_garble {q q' : ℝ} (hq : 1 / 2 < q) (hq' : 1 / 2 ≤ q') (hle : q' ≤ q) :
    ∃ M, IsStochastic M ∧ binExp q' = garble (binExp q) M := by
  have hd : 0 < 2 * q - 1 := by linarith
  set m := (q + q' - 1) / (2 * q - 1)
  have hm0 : 0 ≤ m := div_nonneg (by linarith) hd.le
  have hm1 : m ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨binExp m, binExp_isStochastic hm0 hm1, ?_⟩
  have hd' : 2 * q - 1 ≠ 0 := hd.ne'
  have hmul : (2 * q - 1) * m = q + q' - 1 := mul_div_cancel₀ _ hd'
  have key : q * m + (1 - q) * (1 - m) = q' := by linear_combination hmul
  funext θ y'
  cases θ <;> cases y' <;> simp only [binExp, garble, Fintype.sum_bool] <;> norm_num <;>
    linarith

/-- **More accurate signals are more valuable** in every decision problem. -/
theorem value_mono_accuracy {A : Type*} [Fintype A] [Nonempty A] {q q' : ℝ} (hq : 1 / 2 < q)
    (hq' : 1 / 2 ≤ q') (hle : q' ≤ q) (π : Bool → ℝ) (u : A → Bool → ℝ) :
    value π u (binExp q') ≤ value π u (binExp q) := by
  obtain ⟨M, hM, e⟩ := binExp_garble hq hq' hle
  rw [e]
  exact value_garble_le π u _ hM

theorem sup'_bool (f : Bool → ℝ) : univ.sup' univ_nonempty f = max (f true) (f false) := by
  refine le_antisymm (sup'_le _ _ fun b _ => ?_) (max_le (le_sup' f (mem_univ _))
    (le_sup' f (mem_univ _)))
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Guessing a binary state with a uniform prior: the value of `binExp q` is `max(q, 1 − q)`. -/
theorem value_guess (q : ℝ) :
    value (fun _ => 1 / 2) (fun a θ : Bool => if a = θ then (1 : ℝ) else 0) (binExp q) =
      max q (1 - q) := by
  simp only [value, sup'_bool, payoff, Fintype.sum_bool, binExp]
  norm_num
  rw [max_comm (1 / 2 * (1 - q)) (1 / 2 * q),
    ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- **A strictly more accurate signal is strictly more valuable** (in the guessing problem). -/
theorem value_strict {q q' : ℝ} (hq' : 1 / 2 ≤ q') (hlt : q' < q) :
    value (fun _ => 1 / 2) (fun a θ : Bool => if a = θ then (1 : ℝ) else 0) (binExp q') <
      value (fun _ => 1 / 2) (fun a θ : Bool => if a = θ then (1 : ℝ) else 0) (binExp q) := by
  rw [value_guess, value_guess, max_eq_left (by linarith), max_eq_left (by linarith)]
  exact hlt

end DPExtensions.ValueOfInformation

set_option linter.style.longLine false
#print axioms DPExtensions.ValueOfInformation.IsStochastic
#print axioms DPExtensions.ValueOfInformation.garble
#print axioms DPExtensions.ValueOfInformation.joint
#print axioms DPExtensions.ValueOfInformation.payoff
#print axioms DPExtensions.ValueOfInformation.value
#print axioms DPExtensions.ValueOfInformation.payoff_garble
#print axioms DPExtensions.ValueOfInformation.value_garble_le
#print axioms DPExtensions.ValueOfInformation.IsSublinear
#print axioms DPExtensions.ValueOfInformation.IsSublinear.sum_le
#print axioms DPExtensions.ValueOfInformation.joint_garble
#print axioms DPExtensions.ValueOfInformation.sublinear_garble_le
#print axioms DPExtensions.ValueOfInformation.decisionValue_sublinear
#print axioms DPExtensions.ValueOfInformation.noInfo
#print axioms DPExtensions.ValueOfInformation.value_noInfo
#print axioms DPExtensions.ValueOfInformation.value_noInfo_le
#print axioms DPExtensions.ValueOfInformation.perfect
#print axioms DPExtensions.ValueOfInformation.value_le_perfect
#print axioms DPExtensions.ValueOfInformation.garbleMap
#print axioms DPExtensions.ValueOfInformation.stochSet
#print axioms DPExtensions.ValueOfInformation.convex_stochSet
#print axioms DPExtensions.ValueOfInformation.isCompact_stochSet
#print axioms DPExtensions.ValueOfInformation.blackwell_converse
#print axioms DPExtensions.ValueOfInformation.blackwell
#print axioms DPExtensions.ValueOfInformation.binExp
#print axioms DPExtensions.ValueOfInformation.binExp_isStochastic
#print axioms DPExtensions.ValueOfInformation.binExp_garble
#print axioms DPExtensions.ValueOfInformation.value_mono_accuracy
#print axioms DPExtensions.ValueOfInformation.sup'_bool
#print axioms DPExtensions.ValueOfInformation.value_guess
#print axioms DPExtensions.ValueOfInformation.value_strict
