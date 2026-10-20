/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
