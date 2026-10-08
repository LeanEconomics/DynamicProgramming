/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonotonePolicies.MonotoneDP

/-!
# Saving rises with wealth and income

A household with assets on a finite grid `ι` (asset level `level(a)`) and income state `z ∈ Z`
has cash on hand `m(a, z) = R·level(a) + y(z)`, chooses next-period assets `a'` with
`level(a') ≤ m(a, z)` and consumes `m(a, z) − level(a')`, with utility `u` concave. Income is
i.i.d. with distribution `π`. This is the household problem of Bewley–Huggett–Aiyagari models
on a grid.

* `SavingsModel.savings_monotone`: for any concave `u`, any `β ∈ [0, 1)`, `R ≥ 0`, increasing
  asset levels and income, the greatest optimal saving rule is increasing in assets and in
  income (in the product order) — no differentiability, interiority or monotonicity of the value
  function is needed, since next period's state depends on today's state only through the
  choice `a'`.
* `SavingsModel.chain_monotone`: under that rule the household's state `(a, z)` follows a
  monotone Markov chain, the input to the stationary-distribution theory of Hopenhayn and
  Prescott (1992).
-/

open Finset

namespace DPExtensions.MonotonePolicies

variable (ι Z : Type*) [Fintype ι] [Fintype Z] in
/-- A savings problem with i.i.d. income on an asset grid. -/
structure SavingsModel where
  /-- the asset level at each grid point -/
  level : ι → ℝ
  /-- the gross return -/
  R : ℝ
  R_nonneg : 0 ≤ R
  /-- income in each income state -/
  y : Z → ℝ
  /-- the period utility -/
  u : ℝ → ℝ
  u_concave : ConcaveOn ℝ Set.univ u
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the income distribution -/
  π : Z → ℝ
  π_nonneg : ∀ z, 0 ≤ π z
  π_sum : ∑ z, π z = 1
  /-- a grid point affordable in every state (the borrowing limit) -/
  a₀ : ι
  a₀_feasible : ∀ a z, level a₀ ≤ R * level a + y z

namespace SavingsModel

variable {ι Z : Type*} [Fintype ι] [Fintype Z] [DecidableEq ι] (S : SavingsModel ι Z)

/-- Cash on hand. -/
def cash (x : ι × Z) : ℝ := S.R * S.level x.1 + S.y x.2

/-- The next-state kernel given the choice `a'`: assets `a'`, income drawn from `π`. -/
def K (a : ι) (x' : ι × Z) : ℝ := if x'.1 = a then S.π x'.2 else 0

theorem K_sum (a : ι) : ∑ x', S.K a x' = 1 := by
  rw [Fintype.sum_prod_type]
  simp [K, S.π_sum]

/-- The savings problem as a finite dynamic program. -/
noncomputable def toFDP : FDP (ι × Z) ι where
  Γ x := univ.filter fun a => S.level a ≤ S.cash x
  Γ_nonempty x := ⟨S.a₀, mem_filter.2 ⟨mem_univ _, S.a₀_feasible x.1 x.2⟩⟩
  r x a := S.u (S.cash x - S.level a)
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  P _ a x' := S.K a x'
  P_nonneg _ a x' := by
    simp only [K]
    split_ifs
    · exact S.π_nonneg _
    · exact le_rfl
  P_sum _ a := S.K_sum a

theorem sum_mul_K (v : ι × Z → ℝ) (a : ι) : ∑ x', v x' * S.K a x' = ∑ z, v (a, z) * S.π z := by
  rw [Fintype.sum_prod_type]
  simp [K, mul_ite]

variable [LinearOrder ι] [Preorder Z]

omit [Fintype ι] [DecidableEq ι] in
theorem cash_monotone (hl : Monotone S.level) (hy : Monotone S.y) : Monotone S.cash :=
  fun _ _ hx => add_le_add (mul_le_mul_of_nonneg_left (hl hx.1) S.R_nonneg) (hy hx.2)

/-- The budget sets are ascending in the strong set order. -/
theorem ascending (hl : Monotone S.level) (hy : Monotone S.y) : Ascending S.toFDP.Γ := by
  intro x x' hx a ha a' ha'
  simp only [toFDP, mem_filter, mem_univ, true_and] at ha ha' ⊢
  refine ⟨(hl (min_le_left a a')).trans ha, ?_⟩
  rw [hl.map_max]
  exact max_le (ha.trans (S.cash_monotone hl hy hx)) ha'

/-- **Saving rises with wealth and income**: the greatest optimal saving rule is optimal and
increasing in `(a, z)`. -/
theorem savings_monotone (hl : Monotone S.level) (hy : Monotone S.y) :
    S.toFDP.IsOptimal (gmax S.toFDP.Γ_nonempty (S.toFDP.Q S.toFDP.vstar)) ∧
      Monotone (gmax S.toFDP.Γ_nonempty (S.toFDP.Q S.toFDP.vstar)) :=
  S.toFDP.optimal_monotone (S.ascending hl hy)
    (S.toFDP.id_Q_of_actionKernel
      (increasingDifferences_concave S.u_concave (S.cash_monotone hl hy) hl)
      (fun _ _ _ => rfl) _)

/-- The next-state kernel is FOSD-increasing in the saving choice. -/
theorem K_monotone : MonotoneKernel S.K := by
  intro v hv a a' ha
  simp only [S.sum_mul_K]
  exact Finset.sum_le_sum fun z _ =>
    mul_le_mul_of_nonneg_right (hv (Prod.mk_le_mk.2 ⟨ha, le_rfl⟩)) (S.π_nonneg z)

/-- **The household's state follows a monotone Markov chain** under the greatest optimal saving
rule. -/
theorem chain_monotone (hl : Monotone S.level) (hy : Monotone S.y) :
    MonotoneKernel fun x x' =>
      S.toFDP.P x (gmax S.toFDP.Γ_nonempty (S.toFDP.Q S.toFDP.vstar) x) x' :=
  monotoneKernel_comp S.K_monotone (S.savings_monotone hl hy).2

end SavingsModel

end DPExtensions.MonotonePolicies
