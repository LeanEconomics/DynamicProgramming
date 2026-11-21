/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Objective

/-!
# Example 5.1.1: an infinite supremum and a supremum that is not attained

Miao, Example 5.1.1, p. 141. A static problem is the one-period problem (`T = 1`) with no
terminal reward; then `V₀(s) = sup_{a ∈ Γ(s)} u₀(s, a)` (`V0_one`).

* (a) `u₀(s, a) = 1/a + s` on `Γ(s) = {a ∈ [s, 2] : a ≠ 0}`: for `s ∈ (0, 2]`, `V₀(s) = 1/s + s`
  and `a* = s` is optimal (`example_5_1_1a_pos`); for `s ≤ 0`, `V₀(s) = +∞` and no plan attains
  it (`example_5_1_1a_nonpos`). The book states the first case for `s ∈ (0, 2)` and the second
  for `s < 0`; both hold on the larger sets. For `s > 2`, `Γ(s) = ∅` and `V₀(s) = −∞`
  (`example_5_1_1a_empty`; the book's `Γ` is not nonempty-valued there).
* (b) `u₀(s, a) = a` on `Γ(s) = (0, 1)`: `V₀ ≡ 1`, and no action attains it
  (`example_5_1_1b`).
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The one-period problem: `J₀¹(s, π) = u₀(s, π₀)` when there is no terminal reward. -/
theorem J0T_one (M : MDP S A) (huT : M.uT = 0) (s : S) (π : Plan S A) :
    J0T M 1 s π = M.u 0 (s, π 0 Fin.elim0) := by
  simp [J0T, huT, expRew_zero]

/-- The plans feasible for one period are those with `π₀ ∈ Γ(s)`. -/
theorem feasible_one_iff (M : MDP S A) (s : S) (π : Plan S A) :
    π ∈ feasiblePlans M 1 s ↔ π 0 Fin.elim0 ∈ M.Γ s := by
  constructor
  · intro h
    exact h.2 0 (by norm_num) Fin.elim0
  · intro h
    refine ⟨fun t ht => ?_, fun t ht g => ?_⟩
    · have : t = 0 := by exact_mod_cast Order.lt_one_iff.1 ht
      subst this
      exact Subsingleton.measurable
    · have : t = 0 := by exact_mod_cast Order.lt_one_iff.1 ht
      subst this
      have : g = Fin.elim0 := Subsingleton.elim _ _
      subst this
      exact h

/-- A static problem (Miao, Example 5.1.1): with `T = 1` and no terminal reward,
`V₀(s) = sup_{a ∈ Γ(s)} u₀(s, a)`. -/
theorem V0_one (M : MDP S A) (huT : M.uT = 0) (s : S) :
    V0 M 1 s = ⨆ a ∈ M.Γ s, (M.u 0 (s, a) : EReal) := by
  refine le_antisymm (iSup₂_le fun π hπ => ?_) (iSup₂_le fun a ha => ?_)
  · rw [J0T_one M huT]
    exact le_iSup₂ (f := fun a (_ : a ∈ M.Γ s) => (M.u 0 (s, a) : EReal)) _
      ((feasible_one_iff M s π).1 hπ)
  · have hπ : (fun _ _ => a : Plan S A) ∈ feasiblePlans M 1 s := (feasible_one_iff M s _).2 ha
    have := le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M 1 s) => (J0T M 1 s π : EReal)) _ hπ
    rwa [J0T_one M huT] at this

/-- The problem of Example 5.1.1(a): `sup_{a ∈ [s, 2], a ≠ 0} 1/a + s` (the kernel and the
discount factor play no role). -/
noncomputable def ex511a : MDP ℝ ℝ where
  Γ := fun s => {a | s ≤ a ∧ a ≤ 2 ∧ a ≠ 0}
  P := fun _ => Kernel.deterministic Prod.fst measurable_fst
  u := fun _ x => 1 / x.2 + x.1
  uT := fun _ => 0
  β := 1 / 2

/-- **Example 5.1.1(a)** (Miao, p. 141), `s ∈ (0, 2]`: `V₀(s) = 1/s + s`, attained by `a* = s`.
-/
theorem example_5_1_1a_pos {s : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 2) :
    V0 ex511a 1 s = ((1 / s + s : ℝ) : EReal) ∧
      IsOptimalPlan0 ex511a 1 s fun _ _ => s := by
  have hV : V0 ex511a 1 s = ((1 / s + s : ℝ) : EReal) := by
    rw [V0_one _ rfl]
    refine le_antisymm (iSup₂_le fun a ha => ?_) ?_
    · refine EReal.coe_le_coe_iff.2 ?_
      have : 1 / a ≤ 1 / s := one_div_le_one_div_of_le hs0 ha.1
      simp only [ex511a]
      linarith
    · exact le_iSup₂ (f := fun a (_ : a ∈ ex511a.Γ s) => (ex511a.u 0 (s, a) : EReal)) s
        ⟨le_rfl, hs2, hs0.ne'⟩
  refine ⟨hV, (feasible_one_iff _ s _).2 ⟨le_rfl, hs2, hs0.ne'⟩, ?_⟩
  rw [hV, J0T_one _ rfl]
  rfl

/-- **Example 5.1.1(a)** (Miao, p. 141), `s ≤ 0`: `V₀(s) = +∞` and no feasible plan attains the
supremum (the book states this for `s < 0`). -/
theorem example_5_1_1a_nonpos {s : ℝ} (hs : s ≤ 0) :
    V0 ex511a 1 s = ⊤ ∧ ∀ π, ¬ IsOptimalPlan0 ex511a 1 s π := by
  have hV : V0 ex511a 1 s = ⊤ := by
    rw [V0_one _ rfl]
    refine (EReal.eq_top_iff_forall_lt _).2 fun r => ?_
    set a : ℝ := 1 / (max (r - s) 0 + 1)
    have hpos : 0 < max (r - s) 0 + 1 := by positivity
    have ha0 : 0 < a := by positivity
    have ha1 : a ≤ 1 := by
      rw [div_le_one hpos]
      linarith [le_max_right (r - s) 0]
    refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun a (_ : a ∈ ex511a.Γ s) =>
      (ex511a.u 0 (s, a) : EReal)) a ⟨hs.trans ha0.le, by linarith, ha0.ne'⟩)
    refine EReal.coe_lt_coe_iff.2 ?_
    simp only [ex511a, a, one_div_one_div]
    linarith [le_max_left (r - s) 0]
  refine ⟨hV, fun π hπ => ?_⟩
  have h := hπ.2
  rw [hV] at h
  exact EReal.coe_ne_top _ h.symm

/-- Example 5.1.1(a) for `s > 2`: `Γ(s) = ∅` and `V₀(s) = −∞`. -/
theorem example_5_1_1a_empty {s : ℝ} (hs : 2 < s) : V0 ex511a 1 s = ⊥ := by
  rw [V0_one _ rfl]
  refine le_bot_iff.1 (iSup₂_le fun a ha => ?_)
  exact absurd (ha.1.trans ha.2.1) (not_le.2 hs)

/-- The problem of Example 5.1.1(b): `sup_{a ∈ (0, 1)} a`. -/
noncomputable def ex511b : MDP ℝ ℝ where
  Γ := fun _ => Set.Ioo 0 1
  P := fun _ => Kernel.deterministic Prod.fst measurable_fst
  u := fun _ x => x.2
  uT := fun _ => 0
  β := 1 / 2

/-- **Example 5.1.1(b)** (Miao, p. 141): `V₀(s) = 1` for every `s ∈ ℝ`, and no plan is
optimal. -/
theorem example_5_1_1b (s : ℝ) :
    V0 ex511b 1 s = 1 ∧ ∀ π, ¬ IsOptimalPlan0 ex511b 1 s π := by
  have hV : V0 ex511b 1 s = 1 := by
    rw [V0_one _ rfl]
    refine le_antisymm (iSup₂_le fun a ha => ?_) ?_
    · exact_mod_cast ha.2.le
    · refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
      by_contra hlt
      push Not at hlt
      have hz1 : z < 1 := by exact_mod_cast hlt
      have hm : max z 0 < 1 := max_lt hz1 one_pos
      set a := (max z 0 + 1) / 2
      have ha : a ∈ ex511b.Γ s := ⟨by positivity, by simp only [a]; linarith⟩
      have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (show z < a by
        simp only [a]; linarith [le_max_left z 0]))
        (le_iSup₂ (f := fun a (_ : a ∈ ex511b.Γ s) => (ex511b.u 0 (s, a) : EReal)) a ha)
      exact absurd hz (not_lt.2 this.le)
  refine ⟨hV, fun π hπ => ?_⟩
  have h := hπ.2
  rw [hV, J0T_one _ rfl] at h
  have h1 : (ex511b.u 0 (s, π 0 Fin.elim0)) = 1 := by exact_mod_cast h.symm
  have h2 := ((feasible_one_iff _ s π).1 hπ.1).2
  simp only [ex511b] at h1
  linarith

end Miao.MarkovDecisionProcesses
