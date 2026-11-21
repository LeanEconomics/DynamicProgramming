/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.RGPayoffSet
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Example 21.1.1: the repeated prisoner's dilemma

Miao, Example 21.1.1, p. 744. Two players, actions `C = true` and `D = false`, payoffs
`u(C, C) = (1, 1)`, `u(C, D) = (−1, 2)`, `u(D, C) = (2, −1)`, `u(D, D) = (0, 0)`.

* `example_21_1_1_DD`: `(D, D)` with `w ≡ (0, 0)` is admissible with respect to
  `W = {(1, 1), (0, 0)}` and gives `(0, 0)`, for every `δ ∈ [0, 1)`.
* `example_21_1_1_CC`: `(C, C)` with `w(C, C) = (1, 1)`, `w(y) = (0, 0)` otherwise, is admissible
  and gives `(1, 1)` when `δ ≥ 1/2`.
* `example_21_1_1`: for `1/2 ≤ δ < 1`, `W` is self-generating, hence `W ⊆ V`.
* `rg_pd_stageNash`: `(D, D)` is a stage-game Nash equilibrium, so `V ≠ ∅` for every `δ`
  (`rg_pd_V_nonempty`); this is the concrete instance used for the existence of a stage Nash
  equilibrium elsewhere in the chapter.
-/

namespace Miao.DynamicGames

/-- The prisoner's dilemma payoff of a player who plays `x` against `y` (`true = C`). -/
def rg_pdPay : Bool → Bool → ℝ
  | true, true => 1
  | true, false => -1
  | false, true => 2
  | false, false => 0

/-- The prisoner's dilemma payoffs `u(a)ᵢ = pdPay(aᵢ, a₋ᵢ)` (Miao, p. 744). -/
def rg_pdU (a : rg_Prof (fun _ : Fin 2 => Bool)) (i : Fin 2) : ℝ := rg_pdPay (a i) (a (1 - i))

/-- The candidate self-generating set `W = {(1, 1), (0, 0)}` of Example 21.1.1. -/
def rg_pdW : Set (Fin 2 → ℝ) := {fun _ => 1, fun _ => 0}

/-- Profile updates in the prisoner's dilemma, computed. -/
theorem rg_pd_upd (a : rg_Prof (fun _ : Fin 2 => Bool)) (i : Fin 2) (x : Bool) :
    rg_upd a i x = fun j => if j = i then x else a j := by
  rw [rg_upd_eq]
  funext j
  exact Function.update_apply a i x j

/-- `|u| ≤ 2` in the prisoner's dilemma. -/
theorem rg_pd_bound (a : rg_Prof (fun _ : Fin 2 => Bool)) (j : Fin 2) : |rg_pdU a j| ≤ 2 := by
  unfold rg_pdU
  cases a j <;> cases a (1 - j) <;> norm_num [rg_pdPay]

/-- **Example 21.1.1** (Miao, p. 744), `(0, 0)`: `(D, D)` and `w ≡ (0, 0)` are admissible with
respect to `W` for every `δ ∈ [0, 1)`: `0 = (1 − δ) uᵢ(D, D) + δ wᵢ(D, D)` and
`0 ≥ (1 − δ) uᵢ(aᵢ, D) + δ wᵢ(aᵢ, D)`. -/
theorem example_21_1_1_DD {δ : ℝ} (hδ1 : δ < 1) :
    rg_Admissible δ rg_pdU rg_pdW (fun _ => false) (fun _ => fun _ => 0) ∧
      (fun _ => (0 : ℝ)) = fun j => (1 - δ) * rg_pdU (fun _ => false) j + δ * 0 := by
  refine ⟨⟨fun _ => Or.inr rfl, fun i x => ?_⟩, ?_⟩
  · rw [rg_pd_upd]
    fin_cases i <;> cases x <;> simp [rg_pdU, rg_pdPay] <;> linarith
  · funext j
    simp [rg_pdU, rg_pdPay]

/-- The continuation values `w(C, C) = (1, 1)`, `w(y) = (0, 0)` otherwise. -/
def rg_pdWCC (a : rg_Prof (fun _ : Fin 2 => Bool)) : Fin 2 → ℝ :=
  if a = (fun _ => true) then fun _ => 1 else fun _ => 0

/-- **Example 21.1.1** (Miao, p. 744), `(1, 1)`: for `δ ≥ 1/2`, `(C, C)` with `w(C, C) = (1, 1)`
and `w(y) = (0, 0)` otherwise is admissible with respect to `W`:
`1 = (1 − δ) uᵢ(C, C) + δ wᵢ(C, C)` and `1 ≥ (1 − δ) uᵢ(aᵢ, C) + δ wᵢ(aᵢ, C)`. -/
theorem example_21_1_1_CC {δ : ℝ} (hδ : 1 / 2 ≤ δ) :
    rg_Admissible δ rg_pdU rg_pdW (fun _ => true) rg_pdWCC ∧
      (fun _ => (1 : ℝ)) =
        fun j => (1 - δ) * rg_pdU (fun _ => true) j + δ * rg_pdWCC (fun _ => true) j := by
  refine ⟨⟨fun a' => ?_, fun i x => ?_⟩, ?_⟩
  · unfold rg_pdWCC
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [rg_pd_upd]
    fin_cases i <;> cases x <;>
      simp [rg_pdU, rg_pdPay, rg_pdWCC, funext_iff] <;> linarith
  · funext j
    simp [rg_pdU, rg_pdPay, rg_pdWCC]

/-- **Example 21.1.1** (Miao, p. 744): if `1/2 ≤ δ < 1`, `W = {(1, 1), (0, 0)}` is
self-generating, hence `W ⊆ V` by Lemma 21.1.2. -/
theorem example_21_1_1 {δ : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) :
    rg_pdW ⊆ rg_B δ rg_pdU rg_pdW ∧ rg_pdW ⊆ rg_V δ rg_pdU := by
  have hself : rg_pdW ⊆ rg_B δ rg_pdU rg_pdW := by
    rintro v (rfl | rfl)
    · exact ⟨_, _, (example_21_1_1_CC hδ).1, (example_21_1_1_CC hδ).2⟩
    · exact ⟨_, _, (example_21_1_1_DD hδ1).1, by simpa using (example_21_1_1_DD hδ1).2⟩
  have hbd : rg_Bdd rg_pdW := ⟨1, by rintro x (rfl | rfl) j <;> simp⟩
  exact ⟨hself, hself.trans
    (lemma_21_1_2 rg_pd_bound (by linarith) hδ1 hbd hself)⟩

/-- `(D, D)` is a Nash equilibrium of the prisoner's dilemma stage game. -/
theorem rg_pd_stageNash : rg_IsStageNash rg_pdU (fun _ => false) := by
  intro i x
  rw [rg_pd_upd]
  fin_cases i <;> cases x <;> simp [rg_pdU, rg_pdPay]

/-- In the repeated prisoner's dilemma `(0, 0) ∈ V` for every `δ ∈ [0, 1)`. -/
theorem rg_pd_V_nonempty {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (fun _ => (0 : ℝ)) ∈ rg_V δ rg_pdU := by
  have := rg_stageNash_mem_V rg_pd_bound hδ0 hδ1 rg_pd_stageNash
  have h : rg_pdU (fun _ => false) = fun _ => 0 := by
    funext j
    simp [rg_pdU, rg_pdPay]
  rwa [h] at this

end Miao.DynamicGames
