/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.SmoothAmbiguity

/-!
# Minimization, shortest paths and negative discount rates

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.3.5 (pp. 286–289) and
Exercise 8.1.17 (p. 260).

Minimisation reduces to maximisation by reflection: `R⁻ = (Γ, −V, B⁻)` with
`B⁻(x, a, v) = −B(x, a, −v)` has policy operators `T⁻_σ v = −T_σ(−v)`, values `−v_σ`, value
function `−v_*` (`v_*` the min-value function), and its `v`-greedy policies are the
`(−v)`-min-greedy policies of `R`.

* Theorem 8.3.7 (min-optimality; the book defers its proof to §9.2.3): for globally stable `R`,
  (i) `v_*` is the unique solution of the min-Bellman equation in `V`, (ii) Bellman's principle of
  min-optimality, (iii) a min-optimal policy exists, (iv) min-HPI returns a min-optimal policy in
  finitely many steps; also min-VFI converges.
* Exercise 8.1.17: on a graph whose only cycle is the self-loop at `d` (stated with a rank function
  that strictly decreases along every edge out of `x ≠ d`), with `c ≥ 0` and `c(d, d) = 0`, the
  maximum cost-to-go `C`, the fixed point of `v ↦ max_{x'} {c(x, x') + v(x')}` reached in finitely
  many steps, gives the bounds `v₁ = 0`, `v₂ = C` of (8.20).
* Proposition 8.3.8: if moreover `c(x, x') > 0` for `x ≠ d`, the shortest path RDP on `[0, C]` is
  concave, hence globally stable, and Theorem 8.3.7 applies.
* Exercise 8.3.10 and Proposition 8.3.9: the same with `B(x, x', v) = c(x, x') + βv(x')`, `β > 1`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- The reflected RDP `R⁻ = (Γ, −V, B⁻)` with `B⁻(x, a, v) = −B(x, a, −v)`. -/
def neg : RDP X A where
  Γ := R.Γ
  Γ_nonempty := R.Γ_nonempty
  V := {v | -v ∈ R.V}
  B := fun x a v => -R.B x a (-v)
  mono := fun x a ha v hv w hw hvw => neg_le_neg (R.mono x a ha (-w) hw (-v) hv (neg_le_neg hvw))
  consistent := fun σ hσ v hv => by
    change -(fun x => -R.B x (σ x) (-v)) ∈ R.V
    have : -(fun x => -R.B x (σ x) (-v)) = fun x => R.B x (σ x) (-v) := by
      funext x
      simp
    rw [this]
    exact R.consistent σ hσ (-v) hv

theorem neg_Tσ (σ : X → A) (v : X → ℝ) : R.neg.Tσ σ v = -R.Tσ σ (-v) := rfl

theorem neg_isFeasible {σ : X → A} : R.neg.IsFeasible σ ↔ R.IsFeasible σ := Iff.rfl

theorem neg_mem {v : X → ℝ} : v ∈ R.neg.V ↔ -v ∈ R.V := Iff.rfl

/-- Global stability is invariant under reflection. -/
theorem isGloballyStable_neg_iff : R.IsGloballyStable ↔ R.neg.IsGloballyStable := by
  have key : ∀ σ, R.IsFeasible σ →
      (GloballyStableOn (R.Tσ σ) R.V ↔ GloballyStableOn (R.neg.Tσ σ) R.neg.V) := fun σ hσ =>
    globallyStableOn_iff_of_conj (fun v => -v) (fun v => -v)
      (fun v hv => by change -(-v) ∈ R.V; rwa [neg_neg])
      (fun v hv => hv) (fun v _ => neg_neg v) (fun v _ => neg_neg v)
      continuous_neg.continuousOn continuous_neg.continuousOn (R.Tσ_mapsTo hσ)
      fun v _ => by rw [neg_Tσ, neg_neg]
  exact ⟨fun h σ hσ => (key σ hσ).1 (h σ hσ), fun h σ hσ => (key σ hσ).2 (h σ hσ)⟩

/-- Well-posedness is invariant under reflection, with `v⁻_σ = −v_σ`. -/
theorem WellPosed.neg {R : RDP X A} (hw : R.WellPosed) : R.neg.WellPosed := by
  intro σ hσ
  refine ⟨-R.vσ σ, ⟨by change -(-R.vσ σ) ∈ R.V; rw [neg_neg]; exact vσ_mem hw hσ, ?_⟩,
    fun u ⟨hu, hfix⟩ => ?_⟩
  · change -R.Tσ σ (-(-R.vσ σ)) = -R.vσ σ
    rw [neg_neg, (isFixedPt_vσ hw hσ).eq]
  · have h1 : IsFixedPt (R.Tσ σ) (-u) := by
      have := hfix.eq
      change -R.Tσ σ (-u) = u at this
      change R.Tσ σ (-u) = -u
      exact neg_eq_iff_eq_neg.1 this
    rw [← eq_vσ_of_isFixedPt hw hσ hu h1, neg_neg]

theorem neg_vσ {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.neg.vσ σ = -R.vσ σ := by
  refine (eq_vσ_of_isFixedPt hw.neg hσ ?_ ?_).symm
  · change -(-R.vσ σ) ∈ R.V
    rw [neg_neg]
    exact vσ_mem hw hσ
  · change -R.Tσ σ (-(-R.vσ σ)) = -R.vσ σ
    rw [neg_neg, (isFixedPt_vσ hw hσ).eq]

/-- A `v`-min-greedy policy (§8.3.5): `σ(x)` minimises `B(x, ·, v)` over `Γ(x)`. -/
def IsMinGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  R.IsFeasible σ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x (σ x) v ≤ R.B x a v

theorem isMinGreedy_iff (v : X → ℝ) (σ : X → A) : R.IsMinGreedy v σ ↔ R.neg.IsGreedy (-v) σ := by
  refine and_congr Iff.rfl (forall_congr' fun x => forall₂_congr fun a _ => ?_)
  change _ ↔ -R.B x a (-(-v)) ≤ -R.B x (σ x) (-(-v))
  rw [neg_neg, neg_le_neg_iff]

/-- The Bellman min-operator `(Tv)(x) = min_{a ∈ Γ(x)} B(x, a, v)`. -/
noncomputable def Tmin (v : X → ℝ) : X → ℝ := fun x =>
  (R.Γ x).inf' (R.Γ_nonempty x) fun a => R.B x a v

theorem neg_T (v : X → ℝ) : R.neg.T v = -R.Tmin (-v) := by
  funext x
  change (R.Γ x).sup' (R.Γ_nonempty x) (fun a => -R.B x a (-v)) =
    -(R.Γ x).inf' (R.Γ_nonempty x) fun a => R.B x a (-v)
  refine le_antisymm (Finset.sup'_le _ _ fun a ha => neg_le_neg (Finset.inf'_le _ ha)) ?_
  rw [neg_le]
  exact Finset.le_inf' _ _ fun a ha => neg_le.1 (Finset.le_sup' (fun a => -R.B x a (-v)) ha)

theorem iterate_neg_T (v : X → ℝ) (k : ℕ) : R.neg.T^[k] v = -R.Tmin^[k] (-v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, neg_T, ih, neg_neg]

variable [DecidableEq X] [DecidableEq A]

/-- The min-value function `v_* = ⋀_σ v_σ` (§8.3.5). -/
noncomputable def vmin : X → ℝ := fun x =>
  univ.inf' (univ_nonempty_iff.2 R.policy_nonempty) fun σ : R.Policy => R.vσ σ.1 x

/-- A min-optimal policy: `v_σ = v_*`. -/
def IsMinOptimal (σ : X → A) : Prop := R.IsFeasible σ ∧ R.vσ σ = R.vmin

theorem neg_vstar {R : RDP X A} (hw : R.WellPosed) : R.neg.vstar = -R.vmin := by
  funext x
  refine le_antisymm (Finset.sup'_le _ _ fun τ _ => ?_) ?_
  · rw [neg_vσ hw τ.2, Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff]
    exact Finset.inf'_le (fun σ : R.Policy => R.vσ σ.1 x) (mem_univ (⟨τ.1, τ.2⟩ : R.Policy))
  · rw [Pi.neg_apply, neg_le]
    refine Finset.le_inf' _ _ fun σ _ => ?_
    rw [neg_le]
    have := Finset.le_sup' (fun τ : R.neg.Policy => R.neg.vσ τ.1 x)
      (mem_univ (⟨σ.1, σ.2⟩ : R.neg.Policy))
    simp only [neg_vσ hw σ.2, Pi.neg_apply] at this
    exact this

theorem isMinOptimal_iff {R : RDP X A} (hw : R.WellPosed) (σ : X → A) :
    R.IsMinOptimal σ ↔ R.neg.IsOptimal σ := by
  constructor
  · rintro ⟨hσ, h⟩
    exact ⟨hσ, by rw [neg_vσ hw hσ, neg_vstar hw, h]⟩
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, ?_⟩
    rw [neg_vσ hw hσ, neg_vstar hw] at h
    exact neg_injective h

omit [DecidableEq X] [DecidableEq A] in
/-- The min-HPI step: `σₖ₊₁` (HPI for `R⁻`) is `v_{σₖ}`-min-greedy for `R`, so the HPI sequence of
`R⁻` is min-HPI for `R`. -/
theorem minHpi_isMinGreedy {R : RDP X A} (hw : R.WellPosed) (σ : R.neg.Policy) (k : ℕ) :
    R.IsMinGreedy (R.vσ (R.neg.hpiPolicy σ k).1) (R.neg.hpiPolicy σ (k + 1)).1 := by
  rw [isMinGreedy_iff, ← neg_vσ hw (R.neg.hpiPolicy σ k).2]
  exact R.neg.isGreedy_greedy _

/-- **Theorem 8.3.7 (min-optimality)** (p. 286): for a globally stable RDP, (i) `v_*` is the unique
solution of the min-Bellman equation in `V`, (ii) Bellman's principle of min-optimality holds,
(iii) a min-optimal policy exists and (iv) min-HPI returns a min-optimal policy in finitely many
steps. -/
theorem minOptimality {R : RDP X A} (hR : R.IsGloballyStable) :
    (R.vmin ∈ R.V ∧ IsFixedPt R.Tmin R.vmin ∧ ∀ v ∈ R.V, IsFixedPt R.Tmin v → v = R.vmin) ∧
      (∀ σ, R.IsFeasible σ → (R.IsMinOptimal σ ↔ R.IsMinGreedy R.vmin σ)) ∧
      (∃ σ, R.IsMinOptimal σ) ∧
      ∀ σ : R.neg.Policy, ∃ k, R.vσ (R.neg.hpiPolicy σ (k + 1)).1 = R.vσ (R.neg.hpiPolicy σ k).1 ∧
        R.IsMinOptimal (R.neg.hpiPolicy σ (k + 1)).1 := by
  have hw := hR.wellPosed
  have hN := (isGloballyStable_neg_iff R).1 hR
  obtain ⟨⟨hmem, hfix, huniq⟩, hpo, ⟨σ0, hσ0⟩, hhpi, -⟩ := optimality_of_globallyStable hN
  rw [neg_vstar hw] at hmem hfix huniq
  refine ⟨⟨?_, ?_, fun v hv hv' => ?_⟩, fun σ hσ => ?_, ⟨σ0, (isMinOptimal_iff hw σ0).2 hσ0⟩,
    fun σ => ?_⟩
  · have : -(-R.vmin) ∈ R.V := hmem
    rwa [neg_neg] at this
  · have h := hfix.eq
    rw [neg_T, neg_neg] at h
    exact neg_injective h
  · have h1 : -v ∈ R.neg.V := by change -(-v) ∈ R.V; rwa [neg_neg]
    have h2 : IsFixedPt R.neg.T (-v) := by
      change R.neg.T (-v) = -v
      rw [neg_T, neg_neg, hv'.eq]
    exact neg_injective (huniq _ h1 h2)
  · rw [isMinOptimal_iff hw, hpo σ hσ, neg_vstar hw, isMinGreedy_iff]
  · obtain ⟨k, hk, hopt⟩ := hhpi σ
    refine ⟨k, ?_, (isMinOptimal_iff hw _).2 hopt⟩
    have e1 := neg_vσ hw (R.neg.hpiPolicy σ (k + 1)).2
    have e2 := neg_vσ hw (R.neg.hpiPolicy σ k).2
    simp only [hpiValue] at hk
    rw [e1, e2] at hk
    exact neg_injective hk

/-- Min-VFI converges from any `v_σ` (the `m = 1` case of the min-OPI result noted after
Theorem 8.3.7). -/
theorem tendsto_iterate_Tmin {R : RDP X A} (hR : R.IsGloballyStable) {σ : X → A}
    (hσ : R.IsFeasible σ) : Tendsto (fun k => R.Tmin^[k] (R.vσ σ)) atTop (𝓝 R.vmin) := by
  have hw := hR.wellPosed
  have h := (tendsto_iterate_T_vσ ((isGloballyStable_neg_iff R).1 hR) hσ).neg
  rw [neg_vstar hw, neg_neg, neg_vσ hw hσ] at h
  simpa only [iterate_neg_T, neg_neg] using h

end RDP

/-! ### Shortest paths and negative discount rates (§8.3.5.1–§8.3.5.2) -/

variable {X : Type*} [Fintype X] (O : X → Finset X) (hO : ∀ x, (O x).Nonempty) (c : X → X → ℝ)
  (β : ℝ)

/-- The maximum-cost Bellman operator `(Mv)(x) = max_{x' ∈ O(x)} {c(x, x') + βv(x')}`. -/
noncomputable def maxCost (v : X → ℝ) : X → ℝ := fun x =>
  (O x).sup' (hO x) fun x' => c x x' + β * v x'

/-- The maximum cost-to-go `C = M^N 0`, `N = max rank`: under the hypotheses of Exercise 8.1.17 the
iteration has stopped by then, and `C(x)` is the largest cost of any path from `x` to `d`. -/
noncomputable def maxCostToGo (rank : X → ℕ) : X → ℝ := (maxCost O hO c β)^[univ.sup rank] 0

variable {O hO c β} {d : X} (hOd : O d = {d}) (hcd : c d d = 0) (hc : ∀ x x', 0 ≤ c x x')
  (hβ : 0 ≤ β) {rank : X → ℕ} (hrank : ∀ x, x ≠ d → ∀ x' ∈ O x, rank x' < rank x)
include hOd hcd

omit [Fintype X] in
theorem maxCost_apply_d (v : X → ℝ) : maxCost O hO c β v d = β * v d := by
  have hd : d ∈ O d := by rw [hOd]; exact mem_singleton_self d
  refine le_antisymm (Finset.sup'_le _ _ fun x' hx' => ?_) ?_
  · rw [hOd, Finset.mem_singleton] at hx'
    rw [hx', hcd, zero_add]
  · have := Finset.le_sup' (fun x' => c d x' + β * v x') hd
    simp only [hcd, zero_add] at this
    exact this

omit [Fintype X] in
theorem iterate_maxCost_d (k : ℕ) : (maxCost O hO c β)^[k] 0 d = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', maxCost_apply_d hOd hcd, ih, mul_zero]

omit [Fintype X] in
include hrank in
/-- The iteration stabilises: `M^{k+1}0 = M^k 0` at `x` once `k ≥ rank x`. -/
theorem iterate_maxCost_stable :
    ∀ n, ∀ x, rank x ≤ n → ∀ k, n ≤ k →
      (maxCost O hO c β)^[k + 1] 0 x = (maxCost O hO c β)^[k] 0 x := by
  intro n
  induction n with
  | zero =>
    intro x hx k _
    by_cases hxd : x = d
    · subst hxd
      rw [iterate_maxCost_d hOd hcd, iterate_maxCost_d hOd hcd]
    · obtain ⟨x', hx'⟩ := hO x
      exact absurd (hrank x hxd x' hx') (by omega)
  | succ n ih =>
    intro x hx k hk
    by_cases hxd : x = d
    · subst hxd
      rw [iterate_maxCost_d hOd hcd, iterate_maxCost_d hOd hcd]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      conv_lhs => rw [iterate_succ_apply']
      conv_rhs => rw [iterate_succ_apply']
      refine Finset.sup'_congr (hO x) rfl fun x' hx' => ?_
      rw [ih x' (by have := hrank x hxd x' hx'; omega) j (by omega)]

include hrank in
/-- `C = MC`: the maximum cost-to-go solves the maximum-cost Bellman equation. -/
theorem maxCost_maxCostToGo : maxCost O hO c β (maxCostToGo O hO c β rank) =
    maxCostToGo O hO c β rank := by
  funext x
  have := iterate_maxCost_stable (hO := hO) (β := β) hOd hcd hrank _ x
    (Finset.le_sup (mem_univ x)) _ le_rfl
  rw [iterate_succ_apply'] at this
  exact this

omit hOd hcd in
include hc hβ in
theorem maxCostToGo_nonneg : 0 ≤ maxCostToGo O hO c β rank := by
  have hk : ∀ k, 0 ≤ (maxCost O hO c β)^[k] 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      rw [iterate_succ_apply']
      intro x
      obtain ⟨x', hx'⟩ := hO x
      exact (add_nonneg (hc x x') (mul_nonneg hβ (ih x'))).trans
        (Finset.le_sup' (fun x' => c x x' + β * (maxCost O hO c β)^[k] 0 x') hx')
  exact hk _

theorem maxCostToGo_d : maxCostToGo O hO c β rank d = 0 := iterate_maxCost_d hOd hcd _

include hc hβ hrank in
/-- **Exercise 8.1.17** (p. 260), and Exercise 8.3.10 for `β > 1`: the RDP `B(x, x', v) =
c(x, x') + βv(x')` satisfies (8.20) with `v₁ = 0` and `v₂ = C`, and `C` is finite. -/
theorem pathRDP_isBoundedBy :
    (pathRDP O hO c hβ).IsBoundedBy 0 (maxCostToGo O hO c β rank) := by
  refine ⟨maxCostToGo_nonneg hc hβ, fun _ _ => mem_univ _, fun x a ha => ⟨?_, ?_⟩⟩
  · change 0 ≤ c x a + β * 0
    rw [mul_zero, add_zero]
    exact hc x a
  · change c x a + β * maxCostToGo O hO c β rank a ≤ maxCostToGo O hO c β rank x
    rw [← maxCost_maxCostToGo hOd hcd hrank]
    nth_rewrite 2 [← maxCost_maxCostToGo hOd hcd hrank]
    exact Finset.le_sup' (fun x' => c x x' + β * maxCost O hO c β (maxCostToGo O hO c β rank) x')
      ha

include hc hβ hrank in
/-- **Propositions 8.3.8 and 8.3.9** (pp. 287–289): if also `c(x, x') > 0` for `x ≠ d`, the RDP
`(O, [0, C], B)` with `B(x, x', v) = c(x, x') + βv(x')` (shortest paths: `β = 1`; negative discount
rate: `β > 1`) is concave, hence globally stable; so its min-value function `v_*` is the unique
solution of `v(x) = min_{x' ∈ O(x)} {c(x, x') + βv(x')}` in `[0, C]`, and a policy is min-optimal
iff it is `v_*`-min-greedy. -/
theorem pathRDP_minOptimal [DecidableEq X] (hcpos : ∀ x, x ≠ d → ∀ x' ∈ O x, 0 < c x x') :
    let R := (pathRDP O hO c hβ).restrictIcc (pathRDP_isBoundedBy (hO := hO) hOd hcd hc hβ hrank)
    R.IsConcaveRDP 0 (maxCostToGo O hO c β rank) ∧ R.IsGloballyStable ∧
      (R.vmin ∈ R.V ∧ IsFixedPt R.Tmin R.vmin ∧ ∀ v ∈ R.V, IsFixedPt R.Tmin v → v = R.vmin) ∧
      ∀ σ, R.IsFeasible σ → (R.IsMinOptimal σ ↔ R.IsMinGreedy R.vmin σ) := by
  intro R
  have hb := pathRDP_isBoundedBy (hO := hO) hOd hcd hc hβ hrank
  set C := maxCostToGo O hO c β rank
  -- (8.56): `c(x, x') ≥ δC(x)`
  set w : X → ℝ := fun x => if x = d then 1 else (O x).inf' (hO x) (c x)
  have hw : ∀ x, (0 : X → ℝ) x < w x := fun x => by
    by_cases hxd : x = d
    · simp [w, hxd]
    · simp only [w, hxd, ↓reduceIte, Pi.zero_apply]
      obtain ⟨a, ha, hmin⟩ := (O x).exists_min_image (c x) (hO x)
      rw [show (O x).inf' (hO x) (c x) = c x a from
        le_antisymm (Finset.inf'_le _ ha) (Finset.le_inf' _ _ hmin)]
      exact hcpos x hxd a ha
  obtain ⟨δ, hδ, hδw⟩ := exists_delta_of_lt hb.1 hw
  have hconc : R.IsConcaveRDP 0 C := by
    refine ⟨hb.1, rfl, fun x a _ => ⟨convex_Icc _ _, fun v _ v' _ s t _ _ hst => le_of_eq ?_⟩,
      δ, hδ, fun x a ha => ?_⟩
    · change s * (c x a + β * v a) + t * (c x a + β * v' a) = c x a + β * (s * v a + t * v' a)
      obtain rfl : t = 1 - s := by linarith
      ring
    · change 0 + δ * (C x - 0) ≤ c x a + β * 0
      rw [mul_zero, add_zero, zero_add, sub_zero]
      by_cases hxd : x = d
      · subst hxd
        rw [show C x = 0 from maxCostToGo_d hOd hcd, mul_zero]
        exact hc _ a
      · have h1 := hδw x
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          zero_add, sub_zero, w, hxd, ↓reduceIte] at h1
        exact h1.trans (Finset.inf'_le _ ha)
  have hGS := hconc.isGloballyStable
  obtain ⟨h1, h2, -, -⟩ := RDP.minOptimality hGS
  exact ⟨hconc, hGS, h1, h2⟩

end SargentStachurski.RecursiveDecisionProcesses
