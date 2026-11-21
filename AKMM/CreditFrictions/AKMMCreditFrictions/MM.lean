/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.DebtCeiling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Modigliani–Miller principle and the collateral constraint

AKMM, §19.3.1, (19.1)–(19.2), pp. 566–567; §19.4, Assumption 19.4.2 and footnote 6, p. 572;
the box "More intuition for Modigliani–Miller principle", p. 587.

**Modigliani–Miller** (pp. 566–567). With Arrow–Debreu prices `pᵢ` for the states `i` of a
finite state space, the firm's problem (19.1) is
`max −k + Σᵢ pᵢ[F(zᵢ, k, ℓᵢ) − ℓᵢwᵢ + (1 − δ)k]` and the shareholders' problem (19.2), with
debt `b` and equity `e = k − b`, is `max −(k − b) + Σᵢ pᵢ[F(zᵢ, k, ℓᵢ) − ℓᵢwᵢ + (1 − δ)k − Rb]`.
The two objectives differ by `b(1 − Σᵢ pᵢR)` (`mm_obj_diff`). If `Σᵢ pᵢR = 1` the debt `b`
cancels (`eq_19_2`), the maximisers of (19.2) are exactly the maximisers of (19.1) paired with
any `b` (`mm_isMax_iff`), so the real decisions do not depend on the financing and `b` is
indeterminate (`mm_indeterminate`). Conversely, if `Σᵢ pᵢR ≠ 1`, (19.2) has no maximiser
(`mm_no_max`): the shareholders would take unbounded positive or negative debt.

**Footnote 6** (p. 572). If in default the lender confiscates the fraction `ξ` of the capital,
worth `ξpk′`, the borrower repays `min{D, ξpk′}` on a debt `D`; this is the repayment rule
`ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling.repayment` of Obstfeld–Rogoff (23),
with zero interest and the sanction base `pk′` (`fn6_repayment_eq`). The debt is repaid in full
iff `D ≤ ξpk′` (`fn6_full_iff`), and the lender's net payoff is nonnegative iff `D ≤ ξpk′`
(`fn6_lender_iff`); with `D = b′/R̃` this is the constraint of Assumption 19.4.2
(`assumption_19_4_2_of_fn6`).

**The box on p. 587.** Raising `∆` by debt and paying it out now, then repaying `∆R` next
period, changes the value of the firm by `∆(1 − E[m′R])` (`mm_box_gain`); the gain is zero for
every `∆` iff `E[m′R] = 1` (`mm_box_gain_zero_iff`).

Departure: footnote 6 compares the loan `b′/R̃` with the recovery `ξpk′`, as the book does; it
does not model the timing of the repayment.
-/

namespace AKMM.CreditFrictions

open Finset

variable {ι : Type*} [Fintype ι]

/-- The objective of (19.1), AKMM p. 567: `−k + Σᵢ pᵢ[F(zᵢ, k, ℓᵢ) − ℓᵢwᵢ + (1 − δ)k]`. -/
noncomputable def mmObj (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ k : ℝ) (ℓ : ι → ℝ) : ℝ :=
  -k + ∑ i, p i * (F (z i) k (ℓ i) - ℓ i * w i + (1 - δ) * k)

/-- The shareholders' objective of (19.2), AKMM p. 567:
`−(k − b) + Σᵢ pᵢ[F(zᵢ, k, ℓᵢ) − ℓᵢwᵢ + (1 − δ)k − Rb]`. -/
noncomputable def mmObjDebt (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ R k : ℝ) (ℓ : ι → ℝ)
    (b : ℝ) : ℝ :=
  -(k - b) + ∑ i, p i * (F (z i) k (ℓ i) - ℓ i * w i + (1 - δ) * k - R * b)

/-- AKMM, p. 567: the shareholders' objective (19.2) is the firm's objective (19.1) plus
`b(1 − Σᵢ pᵢR)`; the payoff is `−e + Σᵢ dᵢ` with `e = k − b` and
`dᵢ = pᵢ[F − ℓᵢwᵢ + (1 − δ)k − Rb]`. -/
theorem mm_obj_diff (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ R k : ℝ) (ℓ : ι → ℝ) (b : ℝ) :
    mmObjDebt F p z w δ R k ℓ b = mmObj F p z w δ k ℓ + b * (1 - ∑ i, p i * R) := by
  unfold mmObjDebt mmObj
  have h : ∑ i, p i * (F (z i) k (ℓ i) - ℓ i * w i + (1 - δ) * k - R * b) =
      ∑ i, p i * (F (z i) k (ℓ i) - ℓ i * w i + (1 - δ) * k) - b * ∑ i, p i * R := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [h]
  ring

/-- **(19.2)** (AKMM, p. 567): if `Σᵢ pᵢR = 1` (complete-markets pricing of the riskless bond),
the debt `b` cancels and (19.2) is (19.1), for every `b`. -/
theorem eq_19_2 (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ R : ℝ) (hR : ∑ i, p i * R = 1)
    (k : ℝ) (ℓ : ι → ℝ) (b : ℝ) :
    mmObjDebt F p z w δ R k ℓ b = mmObj F p z w δ k ℓ := by
  rw [mm_obj_diff, hR]
  ring

/-- **Modigliani–Miller** (AKMM, p. 567): if `Σᵢ pᵢR = 1`, `(k, ℓ, b)` maximises (19.2) iff
`(k, ℓ)` maximises (19.1): the financial structure does not affect real decisions. -/
theorem mm_isMax_iff (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ R : ℝ) (hR : ∑ i, p i * R = 1)
    (k : ℝ) (ℓ : ι → ℝ) (b : ℝ) :
    (∀ k' ℓ' b', mmObjDebt F p z w δ R k' ℓ' b' ≤ mmObjDebt F p z w δ R k ℓ b) ↔
      ∀ k' ℓ', mmObj F p z w δ k' ℓ' ≤ mmObj F p z w δ k ℓ := by
  simp only [eq_19_2 F p z w δ R hR]
  exact ⟨fun h k' ℓ' => h k' ℓ' 0, fun h k' ℓ' _ => h k' ℓ'⟩

/-- AKMM, p. 567: "the choice of the financial structure — `b` versus `e` — is indeterminate":
if `Σᵢ pᵢR = 1` and `(k, ℓ)` solves (19.1), then `(k, ℓ, b)` solves (19.2) for every `b`. -/
theorem mm_indeterminate (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ R : ℝ)
    (hR : ∑ i, p i * R = 1) (k : ℝ) (ℓ : ι → ℝ)
    (hopt : ∀ k' ℓ', mmObj F p z w δ k' ℓ' ≤ mmObj F p z w δ k ℓ) (b : ℝ) :
    ∀ k' ℓ' b', mmObjDebt F p z w δ R k' ℓ' b' ≤ mmObjDebt F p z w δ R k ℓ b :=
  (mm_isMax_iff F p z w δ R hR k ℓ b).2 hopt

/-- AKMM, p. 567 (converse): if `Σᵢ pᵢR ≠ 1`, the shareholders' problem (19.2) has no
maximiser, since the objective is affine and nonconstant in `b`. -/
theorem mm_no_max (F : ℝ → ℝ → ℝ → ℝ) (p z w : ι → ℝ) (δ R : ℝ) (hR : ∑ i, p i * R ≠ 1)
    (k : ℝ) (ℓ : ι → ℝ) (b : ℝ) :
    ∃ b', mmObjDebt F p z w δ R k ℓ b < mmObjDebt F p z w δ R k ℓ b' := by
  set s := 1 - ∑ i, p i * R with hs
  have hs0 : s ≠ 0 := fun h => hR (by linarith)
  refine ⟨b + s, ?_⟩
  rw [mm_obj_diff, mm_obj_diff]
  have : 0 < s * s := mul_self_pos.2 hs0
  nlinarith

/-! ### Footnote 6: the collateral constraint from limited enforcement -/

open ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling in
/-- AKMM, footnote 6, p. 572: when the lender can confiscate only the fraction `ξ` of the
capital, the repayment on a debt `D` is `min{D, ξpk′}`: the Obstfeld–Rogoff repayment rule (23)
with zero interest and sanction base `pk′`. -/
theorem fn6_repayment_eq (p ξ D k' : ℝ) :
    repayment (fun k => (p - 1) * k) 0 ξ D k' = min D (ξ * (p * k')) := by
  unfold repayment
  congr 1 <;> ring

open ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling in
/-- AKMM, footnote 6, p. 572: "the borrower could default whenever the debt exceeds this
value": the debt is repaid in full iff `D ≤ ξpk′` (from Obstfeld–Rogoff
`repayment_eq_full_iff`). -/
theorem fn6_full_iff (p ξ D k' : ℝ) :
    repayment (fun k => (p - 1) * k) 0 ξ D k' = D ↔ D ≤ ξ * (p * k') := by
  have h := repayment_eq_full_iff (fun k => (p - 1) * k) 0 ξ D k'
  have e1 : (1 + (0 : ℝ)) * D = D := by ring
  have e2 : ξ * ((fun k => (p - 1) * k) k' + k') = ξ * (p * k') := by ring
  rw [e1, e2] at h
  exact h

open ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling in
/-- AKMM, footnote 6, p. 572: "the lender will not be willing to lend an amount greater than
this value": the lender's net payoff `min{D, ξpk′} − D` is nonnegative iff `D ≤ ξpk′`. -/
theorem fn6_lender_iff (p ξ D k' : ℝ) :
    0 ≤ repayment (fun k => (p - 1) * k) 0 ξ D k' - D ↔ D ≤ ξ * (p * k') := by
  rw [fn6_repayment_eq]
  constructor
  · intro h
    have := min_le_right D (ξ * (p * k'))
    linarith
  · intro h
    rw [min_eq_left h]
    simp

open ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling in
/-- **Assumption 19.4.2** (AKMM, p. 572, via footnote 6): a loan `b′/R̃` is made (the lender's
net payoff is nonnegative) iff `b′/R̃ ≤ ξpk′`. -/
theorem assumption_19_4_2_of_fn6 (p ξ b' Rt k' : ℝ) :
    0 ≤ repayment (fun k => (p - 1) * k) 0 ξ (b' / Rt) k' - b' / Rt ↔
      b' / Rt ≤ ξ * p * k' := by
  rw [fn6_lender_iff, mul_assoc]

/-! ### The box on p. 587 -/

/-- AKMM, box, p. 587: raising `∆` with debt and paying it as dividends now, then cutting next
period's dividends by `∆R` in every state `s` (probability `πₛ`, discount `m′ₛ`), changes the
present value of dividends by `∆ − E[m′∆R] = ∆(1 − E[m′R])`. -/
theorem mm_box_gain (πs m : ι → ℝ) (R Δ : ℝ) :
    Δ - ∑ s, πs s * (m s * (Δ * R)) = Δ * (1 - ∑ s, πs s * (m s * R)) := by
  rw [mul_sub, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun s _ => by ring

/-- AKMM, box, p. 587: the gain from changing the sources of funding is zero for every `∆` iff
`E[m′R] = 1`. -/
theorem mm_box_gain_zero_iff (πs m : ι → ℝ) (R : ℝ) :
    (∀ Δ, Δ - ∑ s, πs s * (m s * (Δ * R)) = 0) ↔ ∑ s, πs s * (m s * R) = 1 := by
  simp only [mm_box_gain]
  constructor
  · intro h
    have := h 1
    linarith
  · intro h Δ
    rw [h]
    ring

end AKMM.CreditFrictions
