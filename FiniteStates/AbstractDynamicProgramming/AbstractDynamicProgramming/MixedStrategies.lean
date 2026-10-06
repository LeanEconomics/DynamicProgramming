/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDynamicProgramming.RDPOptimality

/-!
# Mixed strategies

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.2.1.6 (pp. 301–302).

A mixed strategy draws the action at `x` from a distribution `φ_x` on `Γ(x)`; its policy operator
is `(T̂_φ v)(x) = ∑_a B(x, a, v)φ_x(a)`. The set of mixed strategies is infinite, so
Proposition 9.2.5 (not Theorem 9.2.4) is the tool.

* Exercise 9.2.4: a mixed strategy supported on `argmax_a B(x, a, v)` is `v`-greedy among mixed
  strategies; Exercise 9.2.5: `max_φ (T̂_φ v)(x) = max_a B(x, a, v)`; the mixed strategies form
  an ADP `A_M` whose Bellman operator is `T` (9.6).
* Contracting RDPs (Proposition 8.2.1 and Corollary 8.2.2, restated) and Exercise 9.2.6: if `R`
  is contracting with modulus `β` and `V` is closed, every `T̂_φ` and `T̂ = T` are contractions.
* Conclusion: `A_M` is max-stable, and its value function equals `v*`: mixing does not raise
  the maximal lifetime value.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

/-- A contraction of a closed nonempty set is globally stable on it (Banach). -/
theorem globallyStableOn_of_isContractionOn {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {S : E → E} {U : Set E} {L : ℝ} (hc : IsContractionOn S U L) (hU : IsClosed U)
    (hne : U.Nonempty) : GloballyStableOn S U := by
  obtain ⟨u, hu, hfix⟩ := hc.exists_fixedPt hU hne
  exact ⟨u, hu, hfix, fun v hv hv' => hc.fixedPt_unique hv hu hv' hfix,
    fun v hv => hc.tendsto_iterate_fixedPt hv hu hfix⟩

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-! ### Contracting RDPs (restated from §8.2.1) -/

/-- `R` is contracting with modulus `β ∈ [0, 1)` (8.26). -/
def IsContracting (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧
    ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ w ∈ R.V, |R.B x a v - R.B x a w| ≤ β * ‖v - w‖

variable {R}

/-- Proposition 8.2.1: each `T_σ` is a contraction of modulus `β`. -/
theorem IsContracting.isContractionOn_Tσ {β : ℝ} (h : R.IsContracting β) {σ : X → A}
    (hσ : R.IsFeasible σ) : IsContractionOn (R.Tσ σ) R.V β :=
  ⟨R.Tσ_mapsTo hσ, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact h.2.2 x _ (hσ x) v hv w hw⟩

/-- Proposition 8.2.1: `T` is a contraction of modulus `β`. -/
theorem IsContracting.isContractionOn_T {β : ℝ} (h : R.IsContracting β) :
    IsContractionOn R.T R.V β :=
  ⟨R.T_mapsTo, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (abs_sup'_sub_sup'_le (R.Γ_nonempty x) _ _).trans
      (Finset.sup'_le _ _ fun a ha => h.2.2 x a ha v hv w hw)⟩

/-- Corollary 8.2.2: a contracting RDP with `V` closed and nonempty is globally stable. -/
theorem IsContracting.isGloballyStable {β : ℝ} (h : R.IsContracting β) (hV : IsClosed R.V)
    (hne : R.V.Nonempty) : R.IsGloballyStable := fun _ hσ =>
  globallyStableOn_of_isContractionOn (h.isContractionOn_Tσ hσ) hV hne

variable (R)

/-! ### Mixed strategies -/

/-- `φ` is a mixed strategy: each `φ_x` is a distribution on `A` supported on `Γ(x)`. -/
def IsMixed (φ : X → A → ℝ) : Prop :=
  ∀ x, (∀ a, 0 ≤ φ x a) ∧ (∀ a, a ∉ R.Γ x → φ x a = 0) ∧ ∑ a, φ x a = 1

/-- The set `Φ` of mixed strategies. -/
abbrev Mixed := {φ : X → A → ℝ // R.IsMixed φ}

/-- The mixed-strategy policy operator `(T̂_φ v)(x) = ∑_a B(x, a, v)φ_x(a)`. -/
def Tmix (φ : X → A → ℝ) (v : X → ℝ) : X → ℝ := fun x => ∑ a, R.B x a v * φ x a

/-- The pure strategy `σ` as a mixed strategy (a point mass at `σ(x)`). -/
def dirac [DecidableEq A] (σ : X → A) : X → A → ℝ := fun x a => if a = σ x then 1 else 0

theorem isMixed_dirac [DecidableEq A] {σ : X → A} (hσ : R.IsFeasible σ) :
    R.IsMixed (dirac σ) := fun x => by
  refine ⟨fun a => by unfold dirac; split_ifs <;> norm_num, fun a ha => ?_, ?_⟩
  · unfold dirac
    split_ifs with h
    · exact absurd (h ▸ hσ x) ha
    · rfl
  · simp [dirac]

theorem Tmix_dirac [DecidableEq A] (σ : X → A) (v : X → ℝ) :
    R.Tmix (dirac σ) v = R.Tσ σ v := by
  funext x
  simp [Tmix, dirac, Tσ_apply]

/-- A mixed operator lies between the minimising and the maximising actions. -/
theorem Tmix_le_T {φ : X → A → ℝ} (hφ : R.IsMixed φ) (v : X → ℝ) : R.Tmix φ v ≤ R.T v := by
  intro x
  obtain ⟨h0, hsupp, h1⟩ := hφ x
  calc R.Tmix φ v x = ∑ a, R.B x a v * φ x a := rfl
    _ ≤ ∑ a, R.T v x * φ x a := sum_le_sum fun a _ => by
        by_cases ha : a ∈ R.Γ x
        · exact mul_le_mul_of_nonneg_right (R.B_le_T v ha) (h0 a)
        · rw [hsupp a ha, mul_zero, mul_zero]
    _ = R.T v x := by rw [← Finset.mul_sum, h1, mul_one]

theorem Tmin_le_Tmix {φ : X → A → ℝ} (hφ : R.IsMixed φ) (v : X → ℝ) :
    R.Tσ (R.antiGreedy v) v ≤ R.Tmix φ v := by
  intro x
  obtain ⟨h0, hsupp, h1⟩ := hφ x
  have hmin := ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec
  calc R.Tσ (R.antiGreedy v) v x = ∑ a, R.Tσ (R.antiGreedy v) v x * φ x a := by
        rw [← Finset.mul_sum, h1, mul_one]
    _ ≤ ∑ a, R.B x a v * φ x a := sum_le_sum fun a _ => by
        by_cases ha : a ∈ R.Γ x
        · exact mul_le_mul_of_nonneg_right (hmin.2 a ha) (h0 a)
        · rw [hsupp a ha, mul_zero, mul_zero]

/-- **Exercise 9.2.4** (p. 301): if every `φ_x` is supported on `argmax_{a ∈ Γ(x)} B(x, a, v)`,
then `T̂_φ v ≥ T̂_ψ v` for every mixed `ψ`. -/
theorem Tmix_le_Tmix_of_supported {φ ψ : X → A → ℝ} (hφ : R.IsMixed φ) (hψ : R.IsMixed ψ)
    (v : X → ℝ) (hsupp : ∀ x a, φ x a ≠ 0 → R.B x a v = R.T v x) :
    R.Tmix ψ v ≤ R.Tmix φ v := by
  have heq : R.Tmix φ v = R.T v := by
    funext x
    calc R.Tmix φ v x = ∑ a, R.T v x * φ x a := sum_congr rfl fun a _ => by
          by_cases h : φ x a = 0
          · rw [h, mul_zero, mul_zero]
          · rw [hsupp x a h]
      _ = R.T v x := by rw [← Finset.mul_sum, (hφ x).2.2, mul_one]
  rw [heq]
  exact R.Tmix_le_T hψ v

/-- **Exercise 9.2.5** (p. 301): `max_{φ ∈ Φ} (T̂_φ v)(x) = max_{a ∈ Γ(x)} B(x, a, v)`. -/
theorem isGreatest_Tmix (v : X → ℝ) (x : X) :
    IsGreatest (range fun φ : R.Mixed => R.Tmix φ.1 v x) (R.T v x) := by
  classical
  exact ⟨⟨⟨dirac (R.greedy v), R.isMixed_dirac (R.isGreedy_greedy v).1⟩, by
      simp only
      rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]⟩,
    by rintro _ ⟨φ, rfl⟩; exact R.Tmix_le_T φ.2 v x⟩

/-- Mixed operators are order preserving on `V`. -/
theorem Tmix_monotoneOn {φ : X → A → ℝ} (hφ : R.IsMixed φ) : MonotoneOn (R.Tmix φ) R.V :=
  fun v hv w hw hvw x => sum_le_sum fun a _ => by
    by_cases ha : a ∈ R.Γ x
    · exact mul_le_mul_of_nonneg_right (R.mono x a ha v hv w hw hvw) ((hφ x).1 a)
    · rw [(hφ x).2.1 a ha, mul_zero, mul_zero]

/-- The ADP `A_M = (V, {T̂_φ}_{φ ∈ Φ})` of mixed strategies (p. 301), when each `T̂_φ` maps `V`
into itself. -/
noncomputable def mixedADP [DecidableEq A]
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) : ADP R.V R.Mixed where
  T φ v := ⟨R.Tmix φ.1 v, hmix φ.1 φ.2 v v.2⟩
  exists_greedy v := ⟨⟨dirac (R.greedy v), R.isMixed_dirac (R.isGreedy_greedy v).1⟩, fun ψ => by
    change R.Tmix ψ.1 v ≤ R.Tmix (dirac (R.greedy v)) v
    rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]
    exact R.Tmix_le_T ψ.2 v⟩
  exists_minGreedy v := ⟨⟨dirac (R.antiGreedy v), R.isMixed_dirac fun x =>
      ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.1⟩,
    fun ψ => by
      change R.Tmix (dirac (R.antiGreedy v)) v ≤ R.Tmix ψ.1 v
      rw [Tmix_dirac]
      exact R.Tmin_le_Tmix ψ.2 v⟩

/-- (9.6) (p. 301): the Bellman operator of `A_M` is the Bellman operator `T` of `R`. -/
theorem mixedADP_bellman [DecidableEq A]
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) (v : R.V) :
    ((R.mixedADP hmix).bellman v : X → ℝ) = R.T v := by
  have hg : (R.mixedADP hmix).IsGreedy v
      ⟨dirac (R.greedy v), R.isMixed_dirac (R.isGreedy_greedy v).1⟩ :=
    fun ψ => by
        change R.Tmix ψ.1 v ≤ R.Tmix (dirac (R.greedy v)) v
        rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]
        exact R.Tmix_le_T ψ.2 v
  rw [← ((R.mixedADP hmix).isGreedy_iff v _).1 hg]
  change R.Tmix (dirac (R.greedy v)) v = R.T v
  rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]

variable {R}

/-- **Exercise 9.2.6** (p. 301): if `R` is contracting with modulus `β`, each `T̂_φ` is a
contraction of modulus `β` on `V`. -/
theorem IsContracting.isContractionOn_Tmix {β : ℝ} (h : R.IsContracting β)
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) {φ : X → A → ℝ}
    (hφ : R.IsMixed φ) : IsContractionOn (R.Tmix φ) R.V β :=
  ⟨fun v hv => hmix φ hφ v hv, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    obtain ⟨h0, hsupp, h1⟩ := hφ x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    calc |R.Tmix φ v x - R.Tmix φ w x| = |∑ a, (R.B x a v - R.B x a w) * φ x a| := by
          simp only [Tmix, sub_mul, sum_sub_distrib]
      _ ≤ ∑ a, |(R.B x a v - R.B x a w) * φ x a| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, β * ‖v - w‖ * φ x a := sum_le_sum fun a _ => by
          rw [abs_mul, abs_of_nonneg (h0 a)]
          by_cases ha : a ∈ R.Γ x
          · exact mul_le_mul_of_nonneg_right (h.2.2 x a ha v hv w hw) (h0 a)
          · rw [hsupp a ha, mul_zero, mul_zero]
      _ = β * ‖v - w‖ := by rw [← Finset.mul_sum, h1, mul_one]⟩

/-- §9.2.1.6 (p. 302): for a contracting RDP with `V` closed and nonempty and mixed operators
mapping `V` into itself, the mixed-strategy ADP `A_M` is max-stable and its value function is
`v*`: mixing does not raise maximal lifetime value. -/
theorem mixed_value_eq_vstar [DecidableEq X] [DecidableEq A] {β : ℝ} (h : R.IsContracting β)
    (hV : IsClosed R.V) (hne : R.V.Nonempty)
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) :
    ∃ hs : (R.mixedADP hmix).IsMaxStable, ∃ vhat,
      IsGreatest (range ((R.mixedADP hmix).vσ hs.1.wellPosed)) vhat ∧ (vhat : X → ℝ) = R.vstar := by
  have hos : (R.mixedADP hmix).IsOrderStable := fun φ =>
    orderStable_restrict (fun v hv => hmix φ.1 φ.2 v hv) (R.Tmix_monotoneOn φ.2)
      (globallyStableOn_of_isContractionOn (h.isContractionOn_Tmix hmix φ.2) hV hne)
  obtain ⟨u, hu, hufix⟩ := h.isContractionOn_T.exists_fixedPt hV hne
  have hbfix : IsFixedPt (R.mixedADP hmix).bellman ⟨u, hu⟩ :=
    Subtype.ext ((R.mixedADP_bellman hmix ⟨u, hu⟩).trans hufix.eq)
  have hs : (R.mixedADP hmix).IsMaxStable := ⟨hos, _, hbfix⟩
  obtain ⟨vhat, hgr, hfixiff, -, -⟩ := hs.optimality
  refine ⟨hs, vhat, hgr, ?_⟩
  have hvfix : IsFixedPt R.T vhat := by
    have := congrArg Subtype.val ((hfixiff vhat).2 rfl).eq
    rwa [mixedADP_bellman] at this
  exact (optimality_of_globallyStable (h.isGloballyStable hV hne)).1.2.2 _ vhat.2 hvfix

end RDP

end SargentStachurski.AbstractDynamicProgramming
