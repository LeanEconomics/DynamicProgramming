import CapitalMarketImperfections.DebtCeiling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import InfiniteHorizonDP.SLPEnvelope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NeoclassicalGrowth.RMDecentral
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dividend-adjustment cost

AKMM, §19.4, Assumption 19.4.3 and the firm's problem (19.3), pp. 573–574.

To pay the dividend `d` the firm uses `ϕ(d) = d + κ(d − φ)²` units of resources (`cfPhi`), with
derivative `ϕ′(d) = 1 + 2κ(d − φ)` (`cfPhiD`, `div_hasDerivAt_phi`). For `κ ≥ 0` the largest
dividend that resources `X` can pay is the larger root of `ϕ(d) = X`,
`cfDiv X = φ + 2(X − φ)/(1 + √(1 + 4κ(X − φ)))` (also valid at `κ = 0`, where it is `X`):
`ϕ(cfDiv X) = X` when `1 + 4κ(X − φ) ≥ 0` (`div_phi_div`), every root is at most `cfDiv X`
(`div_le_div_of_phi`), `cfDiv ∘ ϕ = id` where `ϕ′ ≥ 0` (`div_div_phi`), and
`ϕ′(cfDiv X) = √(1 + 4κ(X − φ))` (`div_phiD_div`). Its derivative is `1/ϕ′` (by the inverse
function rule, `div_hasDerivAt_div`). On the region `ϕ′ > 0`, `ϕ` and `ϕ′` are increasing:
`ϕ(d₁) − ϕ(d₀) = (d₁ − d₀)(ϕ′(d₀) + ϕ′(d₁))/2` (`div_phi_sub`, `div_lt_of_phi_lt`,
`div_phiD_le`).
-/

namespace AKMM.CreditFrictions

open Filter Topology

/-- AKMM, p. 574: `ϕ(d) = d + κ(d − φ)²`, the resources needed to pay the dividend `d`
(Assumption 19.4.3, p. 573). -/
def cfPhi (κ φ d : ℝ) : ℝ := d + κ * (d - φ) ^ 2

/-- The derivative `ϕ′(d) = 1 + 2κ(d − φ)`. -/
def cfPhiD (κ φ d : ℝ) : ℝ := 1 + 2 * κ * (d - φ)

/-- The largest dividend payable out of resources `X`: the larger root of `ϕ(d) = X`. -/
noncomputable def cfDiv (κ φ X : ℝ) : ℝ :=
  φ + 2 * (X - φ) / (1 + Real.sqrt (1 + 4 * κ * (X - φ)))

/-- AKMM, p. 574: `ϕ′(d) = 1 + 2κ(d − φ)`. -/
theorem div_hasDerivAt_phi (κ φ d : ℝ) : HasDerivAt (cfPhi κ φ) (cfPhiD κ φ d) d := by
  have h1 : HasDerivAt (fun x : ℝ => x - φ) 1 d := (hasDerivAt_id d).sub_const φ
  have h2 := (hasDerivAt_id d).add ((h1.fun_pow 2).const_mul κ)
  unfold cfPhi cfPhiD
  convert h2 using 1
  · funext x
    simp only [Pi.add_apply, id]
  · norm_num
    ring

/-- `ϕ(d₁) − ϕ(d₀) = (d₁ − d₀)(ϕ′(d₀) + ϕ′(d₁))/2`. -/
theorem div_phi_sub (κ φ d₀ d₁ : ℝ) :
    cfPhi κ φ d₁ - cfPhi κ φ d₀ = (d₁ - d₀) * (cfPhiD κ φ d₀ + cfPhiD κ φ d₁) / 2 := by
  unfold cfPhi cfPhiD
  ring

/-- `ϕ′(d₁) − ϕ′(d₀) = 2κ(d₁ − d₀)`. -/
theorem div_phiD_sub (κ φ d₀ d₁ : ℝ) :
    cfPhiD κ φ d₁ - cfPhiD κ φ d₀ = 2 * κ * (d₁ - d₀) := by
  unfold cfPhiD
  ring

/-- `ϕ′` is increasing for `κ ≥ 0`. -/
theorem div_phiD_le {κ φ d₀ d₁ : ℝ} (hκ : 0 ≤ κ) (h : d₀ ≤ d₁) :
    cfPhiD κ φ d₀ ≤ cfPhiD κ φ d₁ := by
  have := div_phiD_sub κ φ d₀ d₁
  nlinarith

/-- Where `ϕ′ > 0`, `ϕ` is strictly increasing: `ϕ(d₁) < ϕ(d₀)` forces `d₁ < d₀`. -/
theorem div_lt_of_phi_lt {κ φ d₀ d₁ : ℝ} (h₀ : 0 < cfPhiD κ φ d₀) (h₁ : 0 < cfPhiD κ φ d₁)
    (h : cfPhi κ φ d₁ < cfPhi κ φ d₀) : d₁ < d₀ := by
  have e := div_phi_sub κ φ d₀ d₁
  by_contra hc
  have : 0 ≤ (d₁ - d₀) * (cfPhiD κ φ d₀ + cfPhiD κ φ d₁) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- The radicand at `ϕ(d)` is a square: `1 + 4κ(ϕ(d) − φ) = ϕ′(d)²`. -/
theorem div_radicand_phi (κ φ d : ℝ) :
    1 + 4 * κ * (cfPhi κ φ d - φ) = cfPhiD κ φ d ^ 2 := by
  unfold cfPhi cfPhiD
  ring

/-- `ϕ(cfDiv X) = X` when `1 + 4κ(X − φ) ≥ 0`. -/
theorem div_phi_div {κ φ X : ℝ} (h : 0 ≤ 1 + 4 * κ * (X - φ)) :
    cfPhi κ φ (cfDiv κ φ X) = X := by
  set s := Real.sqrt (1 + 4 * κ * (X - φ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 1 + 4 * κ * (X - φ) := Real.sq_sqrt h
  have hd : (1 + s) ≠ 0 := by positivity
  unfold cfPhi cfDiv
  rw [← hs]
  field_simp
  linear_combination (-(X - φ)) * hss

/-- `ϕ′(cfDiv X) = √(1 + 4κ(X − φ))` when `1 + 4κ(X − φ) ≥ 0`. -/
theorem div_phiD_div {κ φ X : ℝ} (h : 0 ≤ 1 + 4 * κ * (X - φ)) :
    cfPhiD κ φ (cfDiv κ φ X) = Real.sqrt (1 + 4 * κ * (X - φ)) := by
  set s := Real.sqrt (1 + 4 * κ * (X - φ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 1 + 4 * κ * (X - φ) := Real.sq_sqrt h
  have hd : (1 + s) ≠ 0 := by positivity
  unfold cfPhiD cfDiv
  rw [← hs]
  field_simp
  linear_combination -hss

/-- `cfDiv (ϕ(d)) = d` where `ϕ′(d) ≥ 0`. -/
theorem div_div_phi {κ φ d : ℝ} (h : 0 ≤ cfPhiD κ φ d) : cfDiv κ φ (cfPhi κ φ d) = d := by
  have hr := div_radicand_phi κ φ d
  have hs : Real.sqrt (1 + 4 * κ * (cfPhi κ φ d - φ)) = cfPhiD κ φ d := by
    rw [hr, Real.sqrt_sq h]
  unfold cfDiv
  rw [hs]
  have hd : 1 + cfPhiD κ φ d ≠ 0 := by linarith
  field_simp
  unfold cfPhi cfPhiD
  ring

/-- Every `d` with `ϕ(d) = X` is at most `cfDiv X` (`κ ≥ 0`): the firm pays the larger root. -/
theorem div_le_div_of_phi {κ φ d X : ℝ} (hκ : 0 ≤ κ) (h : cfPhi κ φ d = X) :
    d ≤ cfDiv κ φ X := by
  have hrad : 0 ≤ 1 + 4 * κ * (X - φ) := by
    rw [← h, div_radicand_phi]
    positivity
  have h1 := div_phi_div hrad
  have h2 := div_phiD_div hrad
  have e := div_phi_sub κ φ (cfDiv κ φ X) d
  rw [h1, h] at e
  have es := div_phiD_sub κ φ (cfDiv κ φ X) d
  by_contra hc
  push Not at hc
  have hs0 : 0 ≤ Real.sqrt (1 + 4 * κ * (X - φ)) := Real.sqrt_nonneg _
  have hk : 0 ≤ κ * (d - cfDiv κ φ X) := mul_nonneg hκ (by linarith)
  have hsum : 0 < cfPhiD κ φ (cfDiv κ φ X) + cfPhiD κ φ d := by
    rcases hκ.lt_or_eq with hκ' | hκ'
    · have : 0 < κ * (d - cfDiv κ φ X) := mul_pos hκ' (by linarith)
      linarith
    · unfold cfPhiD
      rw [← hκ']
      norm_num
  have : (d - cfDiv κ φ X) * (cfPhiD κ φ (cfDiv κ φ X) + cfPhiD κ φ d) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · linarith

/-- `cfDiv` is continuous (the denominator is at least `1`). -/
theorem div_continuous (κ φ : ℝ) : Continuous (cfDiv κ φ) := by
  unfold cfDiv
  refine continuous_const.add (Continuous.div (by fun_prop) (by fun_prop) fun X => ?_)
  have := Real.sqrt_nonneg (1 + 4 * κ * (X - φ))
  positivity

/-- The derivative of the dividend in the resources is `1/ϕ′`: where `1 + 4κ(X − φ) > 0`,
`cfDiv′(X) = 1/√(1 + 4κ(X − φ)) = 1/ϕ′(cfDiv X)`. -/
theorem div_hasDerivAt_div {κ φ X : ℝ} (h : 0 < 1 + 4 * κ * (X - φ)) :
    HasDerivAt (cfDiv κ φ) (cfPhiD κ φ (cfDiv κ φ X))⁻¹ X := by
  refine HasDerivAt.of_local_left_inverse (div_continuous κ φ).continuousAt
    (div_hasDerivAt_phi κ φ _) ?_ ?_
  · rw [div_phiD_div h.le]
    exact (Real.sqrt_pos.2 h).ne'
  · have hc : Continuous fun y : ℝ => 1 + 4 * κ * (y - φ) := by fun_prop
    filter_upwards [hc.continuousAt.eventually_const_lt h] with y hy
    exact div_phi_div hy.le

end AKMM.CreditFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The firm's first-order conditions

AKMM, §19.4.1, the firm's problem (19.3) and its first-order conditions (19.4)–(19.6),
pp. 574–575, with Appendix 19.A.1, p. 877.

The firm at `(k, b)` chooses `(d, ℓ, k′, b′)` subject to the budget
`F(z, k, ℓ) − wℓ + b′/R̃ = b + p[k′ − (1 − δ)k] + ϕ(d)` and the borrowing limit `ξpk′ ≥ b′/R̃`,
to maximise `d + E[m′Ω(S′; k′, b′)]`.

**The envelope conditions** (p. 877). If `Ω(S; ·, ·)` is concave near `(k₀, b₀)` and
`(d₀, ℓ₀, k₀′, b₀′)` is optimal there with `ϕ′(d₀) > 0`, then `Ω` is differentiable at
`(k₀, b₀)` with `Ω_k = λ[(1 − δ)p + F_k]` and `Ω_b = −λ`, `λ = 1/ϕ′(d₀)` (`env_firm`,
`appendix_19_A_1_envelope`). The proof applies the Benveniste–Scheinkman lemma
(`Miao.InfiniteHorizonDP.theorem_4_10`) to the plan that keeps `(ℓ₀, k₀′, b₀′)` and pays out
the dividend `cfDiv` that the budget then allows.

**Kuhn–Tucker conditions** (p. 877). If the continuation `C(k′, b′) = E[m′Ω(S′; k′, b′)]` is
differentiable at the optimum, variations of the plan along feasible directions give
`F_ℓ = w` (19.4) and a multiplier `μ ≥ 0`, zero when the limit is slack, with
`C_k − λp + μλξp = 0` and `C_b + λ/R̃ − μλ/R̃ = 0` (`kkt_firm`): the four first-order
conditions of 19.A.1, derived rather than assumed.

**(19.5)–(19.6).** Substituting the envelope conditions, updated one period, and `λ = 1/ϕ′(d)`
gives `E[m′(ϕ′(d)/ϕ′(d′))((1 − δ)p′ + F_k′)] = (1 − μξ)p` (`eq_19_5`) and
`E[m′(ϕ′(d)/ϕ′(d′))]R̃ = 1 − μ` (`eq_19_6`); `firm_focs` chains everything. Expectations are
over a finite set of next-period states `s` with probabilities `πₛ`.
-/

namespace AKMM.CreditFrictions

open Filter Topology

/-! ### The envelope conditions -/

open Miao.InfiniteHorizonDP in
/-- AKMM, Appendix 19.A.1, p. 877 (envelope conditions). `Y` is output `F(z, ·, ℓ₀)` as a
function of capital, `wl = wℓ₀`, and `cont = E[m′Ω(S′; k′, b′)]` at the optimal `(k′, b′)`. If
`Ω` is concave on a neighbourhood of `(k₀, b₀)`, every plan keeping `(ℓ₀, k′, b′)` is worth at
most `Ω`, and the optimal plan pays `d₀` with `ϕ′(d₀) > 0`, then `Ω` is differentiable at
`(k₀, b₀)` with derivative `(1/ϕ′(d₀))((F_k + p(1 − δ))dk − db)`. -/
theorem env_firm {Y : ℝ → ℝ} {Yk : ℝ} {Ω : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {κ φ wl p δ Rt k' b' cont d₀ k₀ b₀ : ℝ}
    (hΩ : ConcaveOn ℝ U Ω) (hU : U ∈ 𝓝 (k₀, b₀)) (hY : HasDerivAt Y Yk k₀)
    (hle : ∀ (k b d : ℝ), cfPhi κ φ d = Y k - wl + b' / Rt - b - p * (k' - (1 - δ) * k) →
      d + cont ≤ Ω (k, b))
    (hbud : cfPhi κ φ d₀ = Y k₀ - wl + b' / Rt - b₀ - p * (k' - (1 - δ) * k₀))
    (hd₀ : 0 < cfPhiD κ φ d₀) (heq : Ω (k₀, b₀) = d₀ + cont) :
    HasFDerivAt Ω ((cfPhiD κ φ d₀)⁻¹ • ((Yk + p * (1 - δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ)) (k₀, b₀) := by
  set X : ℝ × ℝ → ℝ := fun x => Y x.1 - wl + b' / Rt - x.2 - p * (k' - (1 - δ) * x.1)
    with hXdef
  have hX : HasFDerivAt X ((Yk + p * (1 - δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) (k₀, b₀) := by
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => Y x.1) (Yk • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (k₀, b₀) := hY.comp_hasFDerivAt (k₀, b₀) hasFDerivAt_fst
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (k₀, b₀) :=
      hasFDerivAt_snd
    have h3 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (k₀, b₀) :=
      hasFDerivAt_fst
    have h4 := (((h1.sub_const wl).add_const (b' / Rt)).sub h2).add (h3.const_mul (p * (1 - δ)))
    convert h4.sub_const (p * k') using 1
    · funext x
      simp only [hXdef, Pi.add_apply, Pi.sub_apply]
      ring
    · ext
      · simp
      · simp
  have hX0 : X (k₀, b₀) = cfPhi κ φ d₀ := hbud.symm
  have hrad : 0 < 1 + 4 * κ * (X (k₀, b₀) - φ) := by
    rw [hX0, div_radicand_phi]
    positivity
  have hdiv0 : cfDiv κ φ (X (k₀, b₀)) = d₀ := by rw [hX0]; exact div_div_phi hd₀.le
  have hW : HasFDerivAt (fun x => cfDiv κ φ (X x) + cont)
      ((cfPhiD κ φ d₀)⁻¹ • ((Yk + p * (1 - δ)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        ContinuousLinearMap.snd ℝ ℝ ℝ)) (k₀, b₀) := by
    have h := (div_hasDerivAt_div hrad).comp_hasFDerivAt (k₀, b₀) hX
    rw [hdiv0] at h
    exact h.add_const cont
  refine theorem_4_10 hΩ hU hW (by rw [heq, hdiv0]) ?_
  have hc : ContinuousAt (fun x => 1 + 4 * κ * (X x - φ)) (k₀, b₀) :=
    continuousAt_const.add (continuousAt_const.mul (hX.continuousAt.sub continuousAt_const))
  filter_upwards [hc.eventually_const_lt hrad] with x hx
  exact hle x.1 x.2 _ (div_phi_div hx.le)

open Miao.InfiniteHorizonDP in
/-- **Appendix 19.A.1** (AKMM, p. 877): the envelope conditions
`Ω_k(S; k, b) = λ[(1 − δ)p + F_k(z, k, ℓ)]` and `Ω_b(S; k, b) = −λ`, with `λ = 1/ϕ′(d)` (the
first-order condition `1 = λϕ_d(d)`), under the hypotheses of `env_firm`. -/
theorem appendix_19_A_1_envelope {Y : ℝ → ℝ} {Yk : ℝ} {Ω : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {κ φ wl p δ Rt k' b' cont d₀ k₀ b₀ : ℝ}
    (hΩ : ConcaveOn ℝ U Ω) (hU : U ∈ 𝓝 (k₀, b₀)) (hY : HasDerivAt Y Yk k₀)
    (hle : ∀ (k b d : ℝ), cfPhi κ φ d = Y k - wl + b' / Rt - b - p * (k' - (1 - δ) * k) →
      d + cont ≤ Ω (k, b))
    (hbud : cfPhi κ φ d₀ = Y k₀ - wl + b' / Rt - b₀ - p * (k' - (1 - δ) * k₀))
    (hd₀ : 0 < cfPhiD κ φ d₀) (heq : Ω (k₀, b₀) = d₀ + cont) :
    1 = (cfPhiD κ φ d₀)⁻¹ * cfPhiD κ φ d₀ ∧
    HasDerivAt (fun k => Ω (k, b₀)) ((cfPhiD κ φ d₀)⁻¹ * ((1 - δ) * p + Yk)) k₀ ∧
    HasDerivAt (fun b => Ω (k₀, b)) (-(cfPhiD κ φ d₀)⁻¹) b₀ := by
  have h := env_firm hΩ hU hY hle hbud hd₀ heq
  refine ⟨(inv_mul_cancel₀ hd₀.ne').symm, ?_, ?_⟩
  · have hp : HasDerivAt (fun k : ℝ => (k, b₀)) ((1 : ℝ), (0 : ℝ)) k₀ :=
      (hasDerivAt_id k₀).prodMk (hasDerivAt_const k₀ b₀)
    refine (h.comp_hasDerivAt k₀ hp).congr_deriv ?_
    simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
      Pi.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  · have hp : HasDerivAt (fun b : ℝ => (k₀, b)) ((0 : ℝ), (1 : ℝ)) b₀ :=
      (hasDerivAt_const b₀ k₀).prodMk (hasDerivAt_id b₀)
    refine (h.comp_hasDerivAt b₀ hp).congr_deriv ?_
    simp

/-! ### The Kuhn–Tucker conditions from optimality -/

/-- A one-sided maximum: if `f` is differentiable at `0` and `f t ≤ f 0` for small `t ≥ 0`,
then `f′(0) ≤ 0`. -/
theorem kkt_deriv_nonpos {f : ℝ → ℝ} {D : ℝ} (hf : HasDerivAt f D 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t → f t ≤ f 0) : D ≤ 0 := by
  have hs := hf.tendsto_slope_zero_right
  refine le_of_tendsto hs ?_
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with t ht htpos
  have htp : (0 : ℝ) < t := htpos
  rw [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htp.le) (by linarith [ht htp.le])

/-- The firm's resources for dividends, `F(z, k, ℓ) − wℓ + b′/R̃ − b − p[k′ − (1 − δ)k]`
(the budget of (19.3), p. 574, solved for `ϕ(d)`). -/
noncomputable def kktRes (Yl : ℝ → ℝ) (w Rt b p δ k ℓ k' b' : ℝ) : ℝ :=
  Yl ℓ - w * ℓ + b' / Rt - b - p * (k' - (1 - δ) * k)

/-- AKMM, p. 877: the value of the plan moved from the optimum `(ℓ₀, k₀′, b₀′)` in the direction
`(aℓ, ak, ab)`, paying the largest dividend the budget allows, is differentiable at `0` with
derivative `(F_ℓaℓ − waℓ + ab/R̃ − pak)/ϕ′(d₀) + C′(ak, ab)`, and is at most the optimum
wherever the moved plan satisfies the borrowing limit. -/
theorem kkt_dir {Yl : ℝ → ℝ} {Fl : ℝ} {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ →L[ℝ] ℝ}
    {κ φ w Rt b p δ k ξ ℓ₀ k₀ b₀ d₀ : ℝ} (hY : HasDerivAt Yl Fl ℓ₀)
    (hC : HasFDerivAt C C' (k₀, b₀))
    (hopt : ∀ d ℓ k' b', cfPhi κ φ d = kktRes Yl w Rt b p δ k ℓ k' b' → b' / Rt ≤ ξ * p * k' →
      d + C (k', b') ≤ d₀ + C (k₀, b₀))
    (hbud : cfPhi κ φ d₀ = kktRes Yl w Rt b p δ k ℓ₀ k₀ b₀) (hq : 0 < cfPhiD κ φ d₀)
    (aℓ ak ab : ℝ) :
    ∃ f : ℝ → ℝ, HasDerivAt f ((cfPhiD κ φ d₀)⁻¹ * (Fl * aℓ - w * aℓ + ab / Rt - p * ak) +
      C' (ak, ab)) 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ),
        (b₀ + ab * t) / Rt ≤ ξ * p * (k₀ + ak * t) → f t ≤ f 0 := by
  set Xt : ℝ → ℝ := fun t => kktRes Yl w Rt b p δ k (ℓ₀ + aℓ * t) (k₀ + ak * t) (b₀ + ab * t)
    with hXt
  have hlin : ∀ (x a : ℝ), HasDerivAt (fun t : ℝ => x + a * t) a 0 := fun x a => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add x
  have hYt : HasDerivAt (fun t => Yl (ℓ₀ + aℓ * t)) (Fl * aℓ) 0 :=
    hY.comp_of_eq 0 (hlin ℓ₀ aℓ) (by ring)
  have hX : HasDerivAt Xt (Fl * aℓ - w * aℓ + ab / Rt - p * ak) 0 := by
    have h := ((((hYt.sub ((hlin ℓ₀ aℓ).const_mul w)).add ((hlin b₀ ab).div_const Rt)).sub_const
      b).sub ((hlin (k₀ - (1 - δ) * k) ak).const_mul p))
    convert h using 1
    funext t
    simp only [hXt, kktRes, Pi.add_apply, Pi.sub_apply]
    ring
  have hX0 : Xt 0 = cfPhi κ φ d₀ := by
    simp only [hXt, mul_zero, add_zero]
    exact hbud.symm
  have hrad : 0 < 1 + 4 * κ * (Xt 0 - φ) := by
    rw [hX0, div_radicand_phi]
    positivity
  have hdiv0 : cfDiv κ φ (Xt 0) = d₀ := by rw [hX0]; exact div_div_phi hq.le
  have hD := (div_hasDerivAt_div hrad).comp (0 : ℝ) hX
  rw [hdiv0] at hD
  have hp : HasDerivAt (fun t : ℝ => (k₀ + ak * t, b₀ + ab * t)) (ak, ab) 0 :=
    (hlin k₀ ak).prodMk (hlin b₀ ab)
  have hCt := hC.comp_hasDerivAt_of_eq 0 hp (by simp)
  refine ⟨fun t => cfDiv κ φ (Xt t) + C (k₀ + ak * t, b₀ + ab * t), hD.add hCt, ?_⟩
  have hc : ContinuousAt (fun t => 1 + 4 * κ * (Xt t - φ)) 0 :=
    continuousAt_const.add (continuousAt_const.mul (hX.continuousAt.sub continuousAt_const))
  filter_upwards [hc.eventually_const_lt hrad] with t ht hfeas
  have h0 : cfDiv κ φ (Xt 0) + C (k₀ + ak * 0, b₀ + ab * 0) = d₀ + C (k₀, b₀) := by
    rw [hdiv0]
    simp
  rw [h0]
  exact hopt _ _ _ _ (div_phi_div ht.le) hfeas

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on `(1, 0)` and
`(0, 1)`. -/
theorem kkt_clm_apply (L : ℝ × ℝ →L[ℝ] ℝ) (a c : ℝ) :
    L (a, c) = a * L (1, 0) + c * L (0, 1) := by
  have h : ((a, c) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The firm's first-order conditions of Appendix 19.A.1** (AKMM, p. 877), derived from
optimality. Let `(d₀, ℓ₀, k₀′, b₀′)` solve (19.3) at `(k, b)` (every feasible plan is worth at
most it), with `ϕ′(d₀) > 0`, `R̃ > 0`, output `F(z, k, ·)` differentiable at `ℓ₀` and the
continuation `C(k′, b′) = E[m′Ω(S′; k′, b′)]` differentiable at `(k₀′, b₀′)`, with partial
derivatives `C_k = C′(1, 0)`, `C_b = C′(0, 1)`. With `λ = 1/ϕ′(d₀)`: `F_ℓ = w` (19.4), and
there is `μ ≥ 0` with `μ(ξpk₀′ − b₀′/R̃) = 0` (zero when the limit is slack),
`C_k − λp + μλξp = 0` and `C_b + λ/R̃ − μλ/R̃ = 0`. -/
theorem kkt_firm {Yl : ℝ → ℝ} {Fl : ℝ} {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ →L[ℝ] ℝ}
    {κ φ w Rt b p δ k ξ ℓ₀ k₀ b₀ d₀ : ℝ} (hRt : 0 < Rt) (hY : HasDerivAt Yl Fl ℓ₀)
    (hC : HasFDerivAt C C' (k₀, b₀))
    (hopt : ∀ d ℓ k' b', cfPhi κ φ d = kktRes Yl w Rt b p δ k ℓ k' b' → b' / Rt ≤ ξ * p * k' →
      d + C (k', b') ≤ d₀ + C (k₀, b₀))
    (hbud : cfPhi κ φ d₀ = kktRes Yl w Rt b p δ k ℓ₀ k₀ b₀) (hq : 0 < cfPhiD κ φ d₀)
    (hfeas : b₀ / Rt ≤ ξ * p * k₀) :
    Fl = w ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ * (ξ * p * k₀ - b₀ / Rt) = 0 ∧
      C' (1, 0) - (cfPhiD κ φ d₀)⁻¹ * p + μ * (cfPhiD κ φ d₀)⁻¹ * ξ * p = 0 ∧
      C' (0, 1) + (cfPhiD κ φ d₀)⁻¹ / Rt - μ * (cfPhiD κ φ d₀)⁻¹ / Rt = 0 := by
  obtain ⟨f1, hf1, hle1⟩ := kkt_dir hY hC hopt hbud hq 1 0 0
  have h1 : IsLocalMax f1 0 := by
    filter_upwards [hle1] with t ht
    exact ht (by simpa using hfeas)
  have e1 := h1.hasDerivAt_eq_zero hf1
  obtain ⟨f2, hf2, hle2⟩ := kkt_dir hY hC hopt hbud hq 0 0 (-1)
  have e2 := kkt_deriv_nonpos hf2 (by
    filter_upwards [hle2] with t ht htpos
    refine ht ?_
    have : (b₀ + -1 * t) / Rt ≤ b₀ / Rt := div_le_div_of_nonneg_right (by linarith) hRt.le
    linarith)
  obtain ⟨f3, hf3, hle3⟩ := kkt_dir hY hC hopt hbud hq 0 1 (Rt * ξ * p)
  have h3 : IsLocalMax f3 0 := by
    filter_upwards [hle3] with t ht
    refine ht ?_
    have : (b₀ + Rt * ξ * p * t) / Rt = b₀ / Rt + ξ * p * t := by field_simp
    rw [this]
    nlinarith
  have e3 := h3.hasDerivAt_eq_zero hf3
  have e4 : b₀ / Rt < ξ * p * k₀ →
      (cfPhiD κ φ d₀)⁻¹ * (Fl * 0 - w * 0 + 1 / Rt - p * 0) + C' (0, 1) = 0 := by
    intro hs
    obtain ⟨f4, hf4, hle4⟩ := kkt_dir hY hC hopt hbud hq 0 0 1
    have hc : ContinuousAt (fun t : ℝ => ξ * p * (k₀ + 0 * t) - (b₀ + 1 * t) / Rt) 0 := by
      fun_prop
    have hpos : 0 < ξ * p * (k₀ + 0 * 0) - (b₀ + 1 * 0) / Rt := by simp; linarith
    have h4 : IsLocalMax f4 0 := by
      filter_upwards [hle4, hc.eventually_const_lt hpos] with t ht ht2
      exact ht (by linarith)
    have := h4.hasDerivAt_eq_zero hf4
    rw [kkt_clm_apply C' 0 1] at this
    linear_combination this
  rw [kkt_clm_apply] at e1 e2 e3
  have hRi : Rt * Rt⁻¹ = 1 := mul_inv_cancel₀ hRt.ne'
  have hRR : Rt * ξ * p / Rt = ξ * p := by field_simp
  rw [hRR] at e3
  generalize cfPhiD κ φ d₀ = q at hq e1 e2 e3 e4 ⊢
  generalize C' (1, 0) = Ck at e1 e2 e3 e4 ⊢
  generalize C' (0, 1) = Cb at e1 e2 e3 e4 ⊢
  have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
  have hμ : 1 + Rt * Cb * q = Rt * q * (q⁻¹ / Rt + Cb) := by
    linear_combination (-1 : ℝ) * hqq + (-(q * q⁻¹)) * hRi
  have hl : Fl = w := by
    have : q⁻¹ * (Fl - w) = 0 := by linear_combination e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (inv_pos.2 hq).ne'
    · linarith
  refine ⟨hl, 1 + Rt * Cb * q, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ q⁻¹ / Rt + Cb := by
      have : q⁻¹ * (Fl * 0 - w * 0 + -1 / Rt - p * 0) + (0 * Ck + -1 * Cb) =
          -(q⁻¹ / Rt + Cb) := by ring
      linarith
    rw [hμ]
    exact mul_nonneg (mul_nonneg hRt.le hq.le) this
  · rcases hfeas.lt_or_eq with hs | hs
    · have h2 : q⁻¹ / Rt + Cb = 0 := by linear_combination e4 hs
      rw [hμ, h2]
      ring
    · rw [hs]
      ring
  · linear_combination e3 + (Rt * Cb * ξ * p) * hqq
  · linear_combination (-Cb) * hqq + (-Cb * q * q⁻¹) * hRi

/-! ### (19.5)–(19.6) -/

variable {S : Type*} [Fintype S]

/-- **(19.5)** (AKMM, p. 575, via Appendix 19.A.1). From the first-order condition for `k′`,
`E[m′Ω_k′] − λp + μλξp = 0`, the updated envelope condition
`Ω_k(s) = λₛ[(1 − δ)p′ₛ + F_k(s)]`, `1 = λϕ′(d)` and `1 = λₛϕ′(d′ₛ)`:
`E[m′(ϕ′(d)/ϕ′(d′))((1 − δ)p′ + F_k′)] = (1 − μξ)p`. Here `q = ϕ′(d)`, `q′ₛ = ϕ′(d′ₛ)`. -/
theorem eq_19_5 (pr m lams Ωk p' Fk q' : S → ℝ) (lam q μ ξ p δ : ℝ) (hq : 1 = lam * q)
    (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωk s) - lam * p + μ * lam * ξ * p = 0)
    (henv : ∀ s, Ωk s = lams s * ((1 - δ) * p' s + Fk s)) :
    ∑ s, pr s * (m s * (q / q' s * ((1 - δ) * p' s + Fk s))) = (1 - μ * ξ) * p := by
  have hlam : lam ≠ 0 := by rintro h; rw [h] at hq; simp at hq
  have hrat : ∀ s, q / q' s = lams s / lam := by
    intro s
    have hq's : q' s ≠ 0 := by rintro h; have := hqs s; rw [h] at this; simp at this
    field_simp
    linear_combination (hqs s) - hq
  have e : ∑ s, pr s * (m s * (q / q' s * ((1 - δ) * p' s + Fk s))) =
      (∑ s, pr s * (m s * Ωk s)) / lam := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrat, henv]
    field_simp
  rw [e, div_eq_iff hlam]
  linear_combination hfoc

/-- **(19.6)** (AKMM, p. 575, via Appendix 19.A.1). From the first-order condition for `b′`,
`E[m′Ω_b′] + λ/R̃ − μλ/R̃ = 0`, the updated envelope condition `Ω_b(s) = −λₛ`, `1 = λϕ′(d)` and
`1 = λₛϕ′(d′ₛ)`: `E[m′(ϕ′(d)/ϕ′(d′))]R̃ = 1 − μ`. -/
theorem eq_19_6 (pr m lams Ωb q' : S → ℝ) (lam q μ Rt : ℝ) (hRt : Rt ≠ 0) (hq : 1 = lam * q)
    (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωb s) + lam / Rt - μ * lam / Rt = 0)
    (henv : ∀ s, Ωb s = -lams s) :
    (∑ s, pr s * (m s * (q / q' s))) * Rt = 1 - μ := by
  have hlam : lam ≠ 0 := by rintro h; rw [h] at hq; simp at hq
  have hrat : ∀ s, q / q' s = lams s / lam := by
    intro s
    have hq's : q' s ≠ 0 := by rintro h; have := hqs s; rw [h] at this; simp at this
    field_simp
    linear_combination (hqs s) - hq
  have e : ∑ s, pr s * (m s * (q / q' s)) = -(∑ s, pr s * (m s * Ωb s)) / lam := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrat, henv]
    ring
  have hRi : Rt * Rt⁻¹ = 1 := mul_inv_cancel₀ hRt
  rw [e, div_mul_eq_mul_div, div_eq_iff hlam]
  linear_combination (-Rt) * hfoc + (lam * (1 - μ)) * hRi

/-- **(19.4)–(19.6) from optimality** (AKMM, pp. 574–575 and 877). Let `(d₀, ℓ₀, k₀′, b₀′)`
solve (19.3) as in `kkt_firm`, and let the continuation be `C = Σₛ πₛm′ₛΩₛ` where each
next-period value `Ωₛ` is differentiable at `(k₀′, b₀′)` with the envelope derivative of
`env_firm`, `(1/ϕ′(d′ₛ))((F_k(s) + p′ₛ(1 − δ))dk − db)`. Then `F_ℓ = w` (19.4) and there is
`μ ≥ 0`, zero when the limit is slack, with (19.5) and (19.6). -/
theorem firm_focs {Yl : ℝ → ℝ} {Fl : ℝ} {Ω : S → ℝ × ℝ → ℝ} (pr m p' Fk q' : S → ℝ)
    {κ φ w Rt b p δ k ξ ℓ₀ k₀ b₀ d₀ : ℝ} (hRt : 0 < Rt) (hY : HasDerivAt Yl Fl ℓ₀)
    (hΩ : ∀ s, HasFDerivAt (Ω s) ((q' s)⁻¹ • ((Fk s + p' s * (1 - δ)) •
      ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)) (k₀, b₀))
    (hq' : ∀ s, q' s ≠ 0)
    (hopt : ∀ d ℓ k' b', cfPhi κ φ d = kktRes Yl w Rt b p δ k ℓ k' b' → b' / Rt ≤ ξ * p * k' →
      d + ∑ s, pr s * (m s * Ω s (k', b')) ≤ d₀ + ∑ s, pr s * (m s * Ω s (k₀, b₀)))
    (hbud : cfPhi κ φ d₀ = kktRes Yl w Rt b p δ k ℓ₀ k₀ b₀) (hq : 0 < cfPhiD κ φ d₀)
    (hfeas : b₀ / Rt ≤ ξ * p * k₀) :
    Fl = w ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ * (ξ * p * k₀ - b₀ / Rt) = 0 ∧
      ∑ s, pr s * (m s * (cfPhiD κ φ d₀ / q' s * ((1 - δ) * p' s + Fk s))) =
        (1 - μ * ξ) * p ∧
      (∑ s, pr s * (m s * (cfPhiD κ φ d₀ / q' s))) * Rt = 1 - μ := by
  set L : S → ℝ × ℝ →L[ℝ] ℝ := fun s => (q' s)⁻¹ • ((Fk s + p' s * (1 - δ)) •
      ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
  have hC : HasFDerivAt (fun x => ∑ s, pr s * (m s * Ω s x))
      (∑ s, (pr s * m s) • L s) (k₀, b₀) := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun s _ => (hΩ s).const_mul (pr s * m s))
    convert this using 1
    funext x
    exact Finset.sum_congr rfl fun s _ => by ring
  obtain ⟨hl, μ, hμ, hcs, hk, hb⟩ := kkt_firm hRt hY hC hopt hbud hq hfeas
  refine ⟨hl, μ, hμ, hcs, ?_, ?_⟩
  · refine eq_19_5 pr m (fun s => (q' s)⁻¹) (fun s => (q' s)⁻¹ * ((1 - δ) * p' s + Fk s)) p' Fk
      q' (cfPhiD κ φ d₀)⁻¹ (cfPhiD κ φ d₀) μ ξ p δ (inv_mul_cancel₀ hq.ne').symm
      (fun s => (inv_mul_cancel₀ (hq' s)).symm) ?_ (fun _ => rfl)
    rw [← hk]
    congr 1
    congr 1
    simp only [hL, sum_apply, smul_apply, sub_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
      mul_one, ContinuousLinearMap.coe_snd', sub_zero]
    exact Finset.sum_congr rfl fun s _ => by ring
  · refine eq_19_6 pr m (fun s => (q' s)⁻¹) (fun s => -(q' s)⁻¹) q' (cfPhiD κ φ d₀)⁻¹
      (cfPhiD κ φ d₀) μ Rt hRt.ne' (inv_mul_cancel₀ hq.ne').symm
      (fun s => (inv_mul_cancel₀ (hq' s)).symm) ?_ (fun _ => rfl)
    rw [← hb]
    congr 1
    congr 1
    simp only [mul_neg, Finset.sum_neg_distrib, hL, sum_apply, smul_apply, sub_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, mul_zero, ContinuousLinearMap.coe_snd', zero_sub,
      mul_one, neg_inj]
    exact Finset.sum_congr rfl fun s _ => by ring

end AKMM.CreditFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The household's first-order conditions

AKMM, §19.4.2, the household's problem (19.7) and its first-order conditions (19.8)–(19.10),
p. 576, with Appendix 19.A.2, pp. 877–878.

The household chooses `(c, ℓ, a′, b′)` subject to `(d + q)a + b + wℓ = c + qa′ + b′/R + T` to
maximise `u(c, ℓ) + βE[V(S′; a′, b′)]`.

* **Envelope conditions** (p. 877): `V_b = γ` and `V_a = γ(d + q)` with `γ = u_c(c, ℓ)`, from
  the Benveniste–Scheinkman lemma `Miao.InfiniteHorizonDP.theorem_4_10` when `V` is concave
  (`hh_envelope`).
* **First-order conditions** (p. 877), derived from optimality along budget-preserving
  directions (`hh_dir`): `u_ℓ + γw = 0`, `βE[V_b′] − γ/R = 0`, `βE[V_a′] − γq = 0`
  (`appendix_19_A_2_focs`).
* **(19.8)–(19.10)**: `u₁w = −u₂` (`eq_19_8`), `1/R = E[βu₁′/u₁]` (`eq_19_9`) and
  `q = E[(βu₁′/u₁)(d′ + q′)]` (`eq_19_10`), chained from optimality in `household_focs`.
* The lump-sum tax `T = B′/R̃ − B′/R = τB′/R` and `R > R̃` iff `τ > 0` (`hh_tax`,
  `hh_R_gt_Rt_iff`); the firm and household budgets with `A = A′ = 1` and this tax give the
  resource constraint `C + p[K′ − (1 − δ)K] + κ(D − φ)² = F` (`hh_resource`).
-/

namespace AKMM.CreditFrictions

open Filter Topology

/-! ### Envelope conditions -/

open Miao.InfiniteHorizonDP in
/-- **Appendix 19.A.2, envelope conditions** (AKMM, p. 877). Fix the optimal `(ℓ₀, a′, b′)`;
`cont = βE[V(S′; a′, b′)]`. If `V` is concave on a neighbourhood of `(a₀, b₀)`, every plan
keeping `(ℓ₀, a′, b′)` and consuming what the budget leaves is worth at most `V`, the optimum is
attained there, and `u(·, ℓ₀)` has derivative `γ` at the optimal consumption, then
`V` is differentiable at `(a₀, b₀)` with `V_a = γ(d + q)` and `V_b = γ`. -/
theorem hh_envelope {u : ℝ → ℝ} {γ : ℝ} {V : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {d q w ℓ₀ a' b' R T cont a₀ b₀ : ℝ} (hV : ConcaveOn ℝ U V) (hU : U ∈ 𝓝 (a₀, b₀))
    (hu : HasDerivAt u γ ((d + q) * a₀ + b₀ + w * ℓ₀ - q * a' - b' / R - T))
    (hle : ∀ a b, u ((d + q) * a + b + w * ℓ₀ - q * a' - b' / R - T) + cont ≤ V (a, b))
    (heq : V (a₀, b₀) = u ((d + q) * a₀ + b₀ + w * ℓ₀ - q * a' - b' / R - T) + cont) :
    HasFDerivAt V (γ • ((d + q) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ)) (a₀, b₀) := by
  set c : ℝ × ℝ → ℝ := fun x => (d + q) * x.1 + x.2 + w * ℓ₀ - q * a' - b' / R - T with hc
  have hcd : HasFDerivAt c ((d + q) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ) (a₀, b₀) := by
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (a₀, b₀) :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (a₀, b₀) :=
      hasFDerivAt_snd
    have h := ((h1.const_mul (d + q)).add h2).add_const (w * ℓ₀ - q * a' - b' / R - T)
    convert h using 1
    funext x
    simp only [hc, Pi.add_apply]
    ring
  have hW := (hu.comp_hasFDerivAt (a₀, b₀) hcd).add_const cont
  exact theorem_4_10 hV hU hW heq.symm (Eventually.of_forall fun x => hle x.1 x.2)

/-! ### First-order conditions from optimality -/

/-- AKMM, Appendix 19.A.2, p. 877: at an optimum of (19.7), moving `(c, ℓ, a′, b′)` in any
direction `(ac, aℓ, aa, ab)` that preserves the budget, `waℓ = ac + qaa + ab/R`, does not change
the objective to first order: `u′(ac, aℓ) + C′(aa, ab) = 0`, where `C = βE[V(S′; ·, ·)]`. -/
theorem hh_dir {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ →L[ℝ] ℝ}
    {d q w R T a b c₀ ℓ₀ a₀ b₀ : ℝ} (hu : HasFDerivAt u u' (c₀, ℓ₀))
    (hC : HasFDerivAt C C' (a₀, b₀))
    (hopt : ∀ c ℓ a' b', (d + q) * a + b + w * ℓ = c + q * a' + b' / R + T →
      u (c, ℓ) + C (a', b') ≤ u (c₀, ℓ₀) + C (a₀, b₀))
    (hbud : (d + q) * a + b + w * ℓ₀ = c₀ + q * a₀ + b₀ / R + T)
    (ac aℓ aa ab : ℝ) (hdir : w * aℓ = ac + q * aa + ab / R) :
    u' (ac, aℓ) + C' (aa, ab) = 0 := by
  have hlin : ∀ (x e : ℝ), HasDerivAt (fun t : ℝ => x + e * t) e 0 := fun x e => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul e).const_add x
  have hf := (hu.comp_hasDerivAt_of_eq 0 ((hlin c₀ ac).prodMk (hlin ℓ₀ aℓ)) (by simp)).add
    (hC.comp_hasDerivAt_of_eq 0 ((hlin a₀ aa).prodMk (hlin b₀ ab)) (by simp))
  refine IsLocalMax.hasDerivAt_eq_zero (Eventually.of_forall fun t => ?_) hf
  change u (c₀ + ac * t, ℓ₀ + aℓ * t) + C (a₀ + aa * t, b₀ + ab * t) ≤
    u (c₀ + ac * 0, ℓ₀ + aℓ * 0) + C (a₀ + aa * 0, b₀ + ab * 0)
  simp only [mul_zero, add_zero]
  refine hopt _ _ _ _ ?_
  have : (b₀ + ab * t) / R = b₀ / R + ab / R * t := by ring
  rw [this]
  linear_combination hbud + t * hdir

/-- **Appendix 19.A.2, first-order conditions** (AKMM, p. 877), from optimality. With
`γ = u_c(c, ℓ) = u′(1, 0)`, `u_ℓ = u′(0, 1)` and the continuation `C = βE[V(S′; ·, ·)]` with
partial derivatives `C_a = C′(1, 0)`, `C_b = C′(0, 1)`: `u_ℓ + γw = 0`, `C_b − γ/R = 0` and
`C_a − γq = 0`. -/
theorem appendix_19_A_2_focs {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {C : ℝ × ℝ → ℝ}
    {C' : ℝ × ℝ →L[ℝ] ℝ} {d q w R T a b c₀ ℓ₀ a₀ b₀ : ℝ} (hR : R ≠ 0)
    (hu : HasFDerivAt u u' (c₀, ℓ₀)) (hC : HasFDerivAt C C' (a₀, b₀))
    (hopt : ∀ c ℓ a' b', (d + q) * a + b + w * ℓ = c + q * a' + b' / R + T →
      u (c, ℓ) + C (a', b') ≤ u (c₀, ℓ₀) + C (a₀, b₀))
    (hbud : (d + q) * a + b + w * ℓ₀ = c₀ + q * a₀ + b₀ / R + T) :
    u' (0, 1) + u' (1, 0) * w = 0 ∧ C' (0, 1) - u' (1, 0) * (1 / R) = 0 ∧
      C' (1, 0) - u' (1, 0) * q = 0 := by
  have hl := hh_dir hu hC hopt hbud w 1 0 0 (by ring)
  have hb := hh_dir hu hC hopt hbud (-(1 / R)) 0 0 1 (by field_simp; ring)
  have ha := hh_dir hu hC hopt hbud (-q) 0 1 0 (by ring)
  rw [kkt_clm_apply u', kkt_clm_apply C'] at hl hb ha
  refine ⟨by linear_combination hl, by linear_combination hb, by linear_combination ha⟩

/-- **(19.8)** (AKMM, p. 576): from `u_c = γ` and `u_ℓ + γw = 0`, `u₁(c, ℓ)w = −u₂(c, ℓ)`. -/
theorem eq_19_8 {u1 u2 γ w : ℝ} (hc : u1 = γ) (hl : u2 + γ * w = 0) : u1 * w = -u2 := by
  rw [hc]
  linarith

variable {S : Type*} [Fintype S]

/-- **(19.9)** (AKMM, p. 576, via Appendix 19.A.2). From `βE[V_b′] − γ/R = 0` with the updated
envelope condition `V_b(s) = γₛ = u₁(c′ₛ, ℓ′ₛ)` and `γ = u₁(c, ℓ) ≠ 0`:
`1/R = E[βu₁(c′, ℓ′)/u₁(c, ℓ)]`. -/
theorem eq_19_9 (pr γs Vb : S → ℝ) (β γ R : ℝ) (hγ : γ ≠ 0)
    (hfoc : β * ∑ s, pr s * Vb s - γ * (1 / R) = 0) (henv : ∀ s, Vb s = γs s) :
    1 / R = ∑ s, pr s * (β * γs s / γ) := by
  have e : ∑ s, pr s * (β * γs s / γ) = β * (∑ s, pr s * Vb s) / γ := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by rw [henv]; ring
  rw [e, eq_div_iff hγ]
  linear_combination -hfoc

/-- **(19.10)** (AKMM, p. 576, via Appendix 19.A.2). From `βE[V_a′] − γq = 0` with the updated
envelope condition `V_a(s) = γₛ(d′ₛ + q′ₛ)` and `γ ≠ 0`:
`q = E[(βu₁(c′, ℓ′)/u₁(c, ℓ))(d′ + q′)]`. -/
theorem eq_19_10 (pr γs Va d' q' : S → ℝ) (β γ q : ℝ) (hγ : γ ≠ 0)
    (hfoc : β * ∑ s, pr s * Va s - γ * q = 0) (henv : ∀ s, Va s = γs s * (d' s + q' s)) :
    q = ∑ s, pr s * (β * γs s / γ * (d' s + q' s)) := by
  have e : ∑ s, pr s * (β * γs s / γ * (d' s + q' s)) = β * (∑ s, pr s * Va s) / γ := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by rw [henv]; field_simp
  rw [e, eq_div_iff hγ]
  linear_combination -hfoc

/-- **(19.8)–(19.10) from optimality** (AKMM, p. 576 and 877–878). Let `(c₀, ℓ₀, a₀′, b₀′)` solve
(19.7) (every budget-feasible plan is worth at most it), `u` be differentiable at `(c₀, ℓ₀)`
with `u₁ = u′(1, 0) ≠ 0`, `u₂ = u′(0, 1)`, and the continuation be `βΣₛπₛVₛ`, where each
next-period value `Vₛ` is differentiable at `(a₀′, b₀′)` with the envelope derivative of
`hh_envelope`, `γₛ((d′ₛ + q′ₛ)da + db)`. Then (19.8), (19.9) and (19.10) hold. -/
theorem household_focs {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {V : S → ℝ × ℝ → ℝ}
    (pr γs d' q' : S → ℝ) {β d q w R T a b c₀ ℓ₀ a₀ b₀ : ℝ} (hR : R ≠ 0)
    (hu : HasFDerivAt u u' (c₀, ℓ₀)) (hγ : u' (1, 0) ≠ 0)
    (hV : ∀ s, HasFDerivAt (V s) (γs s • ((d' s + q' s) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ)) (a₀, b₀))
    (hopt : ∀ c ℓ a' b', (d + q) * a + b + w * ℓ = c + q * a' + b' / R + T →
      u (c, ℓ) + β * ∑ s, pr s * V s (a', b') ≤ u (c₀, ℓ₀) + β * ∑ s, pr s * V s (a₀, b₀))
    (hbud : (d + q) * a + b + w * ℓ₀ = c₀ + q * a₀ + b₀ / R + T) :
    u' (1, 0) * w = -u' (0, 1) ∧ 1 / R = ∑ s, pr s * (β * γs s / u' (1, 0)) ∧
      q = ∑ s, pr s * (β * γs s / u' (1, 0) * (d' s + q' s)) := by
  set L : S → ℝ × ℝ →L[ℝ] ℝ := fun s => γs s • ((d' s + q' s) •
      ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
  have hC : HasFDerivAt (fun x => β * ∑ s, pr s * V s x) (β • ∑ s, pr s • L s) (a₀, b₀) := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun s _ => (hV s).const_mul (pr s))
    exact this.const_mul β
  obtain ⟨hl, hb, ha⟩ := appendix_19_A_2_focs hR hu hC hopt hbud
  have hLb : (β • ∑ s, pr s • L s) (0, 1) = β * ∑ s, pr s * γs s := by
    simp only [hL]
    simp
  have hLa : (β • ∑ s, pr s • L s) (1, 0) = β * ∑ s, pr s * (γs s * (d' s + q' s)) := by
    simp only [hL]
    simp
  rw [hLb] at hb
  rw [hLa] at ha
  refine ⟨eq_19_8 rfl hl, ?_, ?_⟩
  · exact eq_19_9 pr γs γs β (u' (1, 0)) R hγ hb (fun _ => rfl)
  · exact eq_19_10 pr γs (fun s => γs s * (d' s + q' s)) d' q' β (u' (1, 0)) q hγ ha
      (fun _ => rfl)

/-! ### Taxes and the resource constraint -/

/-- AKMM, p. 576: with `R̃ = R/(1 + τ)` (Assumption 19.4.1, p. 572), the lump-sum tax that
finances the interest subsidy is `T = B′/R̃ − B′/R = τB′/R`. -/
theorem hh_tax {R τ B' : ℝ} (hR : R ≠ 0) :
    B' / (R / (1 + τ)) - B' / R = τ * B' / R := by
  field_simp
  ring

/-- AKMM, p. 576: "Notice that `R > R̃` since `R̃ = R/(1 + τ)` and `τ` is positive": for
`R > 0`, `τ > −1`, `R > R̃` iff `τ > 0`. -/
theorem hh_R_gt_Rt_iff {R τ : ℝ} (hR : 0 < R) (hτ : -1 < τ) : R / (1 + τ) < R ↔ 0 < τ := by
  have h1 : 0 < 1 + τ := by linarith
  rw [div_lt_iff₀ h1]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- AKMM, pp. 574–576: the firm's budget `F − wL + B′/R̃ = B + p[K′ − (1 − δ)K] + ϕ(D)`, the
household's budget with `A = A′ = 1`, `(D + q) + B + wL = C + q + B′/R + T`, and the tax
`T = B′/R̃ − B′/R` give the resource constraint `C + p[K′ − (1 − δ)K] + κ(D − φ)² = F`. -/
theorem hh_resource {F w L B' Rt B p K' δ K D C q R T κ φ : ℝ}
    (hfirm : F - w * L + B' / Rt = B + p * (K' - (1 - δ) * K) + cfPhi κ φ D)
    (hhh : (D + q) * 1 + B + w * L = C + q * 1 + B' / R + T) (hT : T = B' / Rt - B' / R) :
    C + p * (K' - (1 - δ) * K) + κ * (D - φ) ^ 2 = F := by
  unfold cfPhi at hfirm
  rw [hT] at hhh
  linarith

end AKMM.CreditFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period model: closed forms

AKMM, §19.5, pp. 576–578, and the working-capital labour demand of §19.5.5, pp. 584–585.

Utility `u(c, ℓ) = ln(c − ℓ^ν)` and technology `F(z, k, ℓ) = zk^αℓ^{1−α}`. Write
`e = α + ν − 1`.

* Marginal utilities `u₁ = 1/(c − ℓ^ν)`, `u₂ = −νℓ^{ν−1}/(c − ℓ^ν)`, so `−u₂/u₁ = νℓ^{ν−1}`
  (`tp_hasDerivAt_u1`, `tp_hasDerivAt_u2`, `tp_mrs`); marginal products
  `F_k = αF/k` and `F_ℓ = (1 − α)zk^αℓ^{−α} = (1 − α)z(k/ℓ)^α = (1 − α)F/ℓ` (`tp_mpk`,
  `tp_mpl`, `tp_mpl_eq`, `tp_wage_bill`).
* **Labour** (p. 577): for `L > 0`, the condition `(1 − α)z(K/L)^α = ωνL^{ν−1}` holds iff
  `L = ((1 − α)/(ων))^{1/e} z^{1/e} K^{α/e}` (`tpL`, `tp_foc_iff`); `ω = 1` is the period-1
  condition from (19.4) and (19.8) (`tp_labour`), `ω = 1 + µ` the working-capital condition of
  p. 584. With `e > 0`, labour increases in `z` and `K` (`tp_L_strictMono_z`,
  `tp_L_strictMono_K`); with `e < 0` it decreases in `z` (`tp_L_strictAnti_z_of_neg`).
* **Output** (p. 577): `Y = zK^αL^{1−α} = ((1 − α)/ν)^{(1−α)/e} z^{ν/e} K^{να/e}` (`tpY`,
  `tp_Y_eq`), increasing in `z` and `K` (`tp_Y_strictMono_z`, `tp_Y_strictMono_K`).
* **The marginal product of capital** (p. 578): `F_k = α((1 − α)/ν)^{(1−α)/e} z^{ν/e}
  K^{να/e − 1} = αY/K` (`tpFk`, `tp_Fk_eq`), increasing in `z` and, for `ν > 1`, strictly
  decreasing in `K` (`tp_Fk_strictMono_z`, `tp_Fk_strictAnti_K`).
* **`g(z′, K′) = C′ − L′^ν`** (p. 577) with `C′ = (1 − δ)K′ + Y′`: `L^ν = (1 − α)Y/ν`
  (`tp_L_pow_nu`), so `g = (1 − δ)K′ + (e/ν)Y′` (`tp_g_eq`), increasing in `z′` and `K′` on
  the whole positive orthant when `e > 0` and `δ ≤ 1` (`tp_g_strictMono_z`,
  `tp_g_strictMono_K`): the book's "at least in the relevant range" is not needed.
* **Property 19.5.6** (p. 584): with working capital, labour
  `L = ((1 − α)/((1 + µ)ν))^{1/e} z^{1/e} K^{α/e}` (`tp_wc_labour`) is strictly decreasing in
  `µ` (`property_19_5_6`).

Departure: the book does not state a sign for `e = α + ν − 1`; its claims that labour and output
increase in `z` and `K` need `e > 0` (e.g. `ν > 1`), and fail for `e < 0`.
-/

namespace AKMM.CreditFrictions

open Set

/-- AKMM, p. 577 (with `ω = 1`) and p. 585 (with `ω = 1 + µ`): labour
`L = ((1 − α)/(ων))^{1/(α+ν−1)} z^{1/(α+ν−1)} K^{α/(α+ν−1)}`. -/
noncomputable def tpL (α ν ω z K : ℝ) : ℝ :=
  ((1 - α) / (ω * ν)) ^ (1 / (α + ν - 1)) * z ^ (1 / (α + ν - 1)) * K ^ (α / (α + ν - 1))

/-- AKMM, p. 577: output `Y = ((1 − α)/ν)^{(1−α)/(α+ν−1)} z^{ν/(α+ν−1)} K^{να/(α+ν−1)}`. -/
noncomputable def tpY (α ν z K : ℝ) : ℝ :=
  ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) * z ^ (ν / (α + ν - 1)) *
    K ^ (ν * α / (α + ν - 1))

/-- AKMM, p. 578: `F_k = α((1 − α)/ν)^{(1−α)/(α+ν−1)} z^{ν/(α+ν−1)} K^{να/(α+ν−1) − 1}`. -/
noncomputable def tpFk (α ν z K : ℝ) : ℝ :=
  α * ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) * z ^ (ν / (α + ν - 1)) *
    K ^ (ν * α / (α + ν - 1) - 1)

/-- AKMM, p. 577: `g(z, K) = C − L^ν` with `C = (1 − δ)K + Y`. -/
noncomputable def tpG (δ α ν z K : ℝ) : ℝ :=
  (1 - δ) * K + tpY α ν z K - tpL α ν 1 z K ^ ν

/-! ### Marginal utilities and marginal products -/

/-- AKMM, p. 577: `u₁(c, ℓ) = 1/(c − ℓ^ν)` for `u = ln(c − ℓ^ν)`, `c > ℓ^ν`. -/
theorem tp_hasDerivAt_u1 {c ℓ ν : ℝ} (h : ℓ ^ ν < c) :
    HasDerivAt (fun x => Real.log (x - ℓ ^ ν)) (1 / (c - ℓ ^ ν)) c := by
  have h1 : HasDerivAt (fun x : ℝ => x - ℓ ^ ν) 1 c := (hasDerivAt_id c).sub_const _
  convert h1.log (sub_ne_zero.2 (ne_of_gt h)) using 1

/-- AKMM, p. 577: `u₂(c, ℓ) = −νℓ^{ν−1}/(c − ℓ^ν)`, `ℓ > 0`, `c > ℓ^ν`. -/
theorem tp_hasDerivAt_u2 {c ℓ ν : ℝ} (hℓ : 0 < ℓ) (h : ℓ ^ ν < c) :
    HasDerivAt (fun x => Real.log (c - x ^ ν)) (-(ν * ℓ ^ (ν - 1)) / (c - ℓ ^ ν)) ℓ := by
  have h1 : HasDerivAt (fun x : ℝ => c - x ^ ν) (-(ν * ℓ ^ (ν - 1))) ℓ :=
    (Real.hasDerivAt_rpow_const (Or.inl hℓ.ne')).const_sub c
  exact h1.log (sub_ne_zero.2 (ne_of_gt h))

/-- AKMM, p. 577: the marginal rate of substitution `−u₂/u₁ = νℓ^{ν−1}`. -/
theorem tp_mrs {c ℓ ν : ℝ} (h : ℓ ^ ν < c) :
    -(-(ν * ℓ ^ (ν - 1)) / (c - ℓ ^ ν)) / (1 / (c - ℓ ^ ν)) = ν * ℓ ^ (ν - 1) := by
  have : c - ℓ ^ ν ≠ 0 := by linarith
  field_simp

/-- AKMM, p. 578: `F_k(z, K, L) = αzK^{α−1}L^{1−α} = αF/K`. -/
theorem tp_mpk {α z K L : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k => z * k ^ α * L ^ (1 - α)) (α * (z * K ^ α * L ^ (1 - α)) / K) K := by
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul z).mul_const
    (L ^ (1 - α))
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hK.ne']
  field_simp

/-- AKMM, p. 577: `F_ℓ(z, K, L) = (1 − α)zK^αL^{−α}`. -/
theorem tp_mpl {α z K L : ℝ} (hL : 0 < L) :
    HasDerivAt (fun l => z * K ^ α * l ^ (1 - α)) ((1 - α) * z * K ^ α * L ^ (-α)) L := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul (z * K ^ α)
  refine h.congr_deriv ?_
  rw [show 1 - α - 1 = -α by ring]
  ring

/-- AKMM, p. 577: `(1 − α)zK^αL^{−α} = (1 − α)z(K/L)^α`. -/
theorem tp_mpl_eq {α z K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) :
    (1 - α) * z * K ^ α * L ^ (-α) = (1 - α) * z * (K / L) ^ α := by
  rw [Real.div_rpow hK hL, Real.rpow_neg hL]
  ring

/-- AKMM, p. 578: the wage bill is labour's share, `F_ℓL = (1 − α)F` (used in (19.13)–(19.14)). -/
theorem tp_wage_bill {α z K L : ℝ} (hL : 0 < L) :
    (1 - α) * z * K ^ α * L ^ (-α) * L = (1 - α) * (z * K ^ α * L ^ (1 - α)) := by
  have : L ^ (1 - α) = L ^ (-α) * L := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add hL, Real.rpow_one]
  rw [this]
  ring

/-! ### Labour -/

/-- `tpL` is the `1/e`-th power of `((1 − α)/(ων))zK^α`. -/
theorem tp_L_eq {α ν ω z K : ℝ} (hc : 0 ≤ (1 - α) / (ω * ν)) (hz : 0 ≤ z) (hK : 0 ≤ K) :
    tpL α ν ω z K = ((1 - α) / (ω * ν) * z * K ^ α) ^ (1 / (α + ν - 1)) := by
  unfold tpL
  rw [Real.mul_rpow (mul_nonneg hc hz) (Real.rpow_nonneg hK α), Real.mul_rpow hc hz,
    ← Real.rpow_mul hK]
  congr 2
  ring

/-- **Labour** (AKMM, p. 577 for `ω = 1`, p. 585 for `ω = 1 + µ`): for `L > 0`,
`(1 − α)z(K/L)^α = ωνL^{ν−1}` iff `L = ((1 − α)/(ων))^{1/e} z^{1/e} K^{α/e}`,
`e = α + ν − 1 ≠ 0`. -/
theorem tp_foc_iff {α ν ω z K L : ℝ} (hα : α < 1) (hν : 0 < ν) (hω : 0 < ω) (hz : 0 < z)
    (hK : 0 < K) (hL : 0 < L) (he : α + ν - 1 ≠ 0) :
    (1 - α) * z * (K / L) ^ α = ω * ν * L ^ (ν - 1) ↔ L = tpL α ν ω z K := by
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hLa : 0 < L ^ α := Real.rpow_pos_of_pos hL α
  have hA : 0 < (1 - α) / (ω * ν) * z * K ^ α := by positivity
  rw [tp_L_eq hc.le hz.le hK.le, Real.div_rpow hK.le hL.le]
  have hLe : L ^ (α + ν - 1) = L ^ (ν - 1) * L ^ α := by
    rw [← Real.rpow_add hL]
    ring_nf
  have key : (1 - α) * z * (K ^ α / L ^ α) = ω * ν * L ^ (ν - 1) ↔
      L ^ (α + ν - 1) = (1 - α) / (ω * ν) * z * K ^ α := by
    rw [hLe]
    constructor
    · intro h
      field_simp at h ⊢
      linear_combination -h
    · intro h
      field_simp at h ⊢
      linear_combination -h
  rw [key, one_div]
  constructor
  · intro h
    rw [← h, Real.rpow_rpow_inv hL.le he]
  · intro h
    rw [h, Real.rpow_inv_rpow hA.le he]

/-- AKMM, p. 577: in period 1 the household's condition (19.8) with the wage from (19.4),
`u₁w = −u₂` with `w = (1 − α)z(K/L)^α`, `u₁ = 1/(C − L^ν)`, `u₂ = −νL^{ν−1}/(C − L^ν)`, is
`(1 − α)z(K/L)^α = νL^{ν−1}`, and so `L = ((1 − α)/ν)^{1/e} z^{1/e} K^{α/e}`. -/
theorem tp_labour {α ν z K L C : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (hL : 0 < L) (he : α + ν - 1 ≠ 0) (hC : L ^ ν < C)
    (h198 : 1 / (C - L ^ ν) * ((1 - α) * z * (K / L) ^ α) =
      -(-(ν * L ^ (ν - 1)) / (C - L ^ ν))) :
    L = tpL α ν 1 z K := by
  have hCL : C - L ^ ν ≠ 0 := by linarith
  refine (tp_foc_iff hα hν one_pos hz hK hL he).1 ?_
  field_simp at h198
  linear_combination h198

/-- AKMM, p. 577: "labor increases in TFP" (`e = α + ν − 1 > 0`). -/
theorem tp_L_strictMono_z {α ν ω K : ℝ} (hα : α < 1) (hν : 0 < ν) (hω : 0 < ω) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpL α ν ω z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ _ h
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have h1 := Real.rpow_lt_rpow (le_of_lt hz₁) h (one_div_pos.2 he)
  have h2 := Real.rpow_pos_of_pos hc (1 / (α + ν - 1))
  have h3 := Real.rpow_pos_of_pos hK (α / (α + ν - 1))
  simp only [tpL]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 h2) h3

/-- AKMM, p. 577: "labor increases in … capital" (`α > 0`, `e > 0`). -/
theorem tp_L_strictMono_K {α ν ω z : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hω : 0 < ω)
    (hz : 0 < z) (he : 0 < α + ν - 1) : StrictMonoOn (fun K => tpL α ν ω z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ _ h
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have h1 := Real.rpow_lt_rpow (le_of_lt hK₁) h (div_pos hα0 he)
  have h2 := mul_pos (Real.rpow_pos_of_pos hc (1 / (α + ν - 1)))
    (Real.rpow_pos_of_pos hz (1 / (α + ν - 1)))
  simp only [tpL]
  exact mul_lt_mul_of_pos_left h1 h2

/-- AKMM, p. 577 (the hypothesis `e > 0` is needed): if `α + ν < 1`, labour strictly
decreases in TFP. -/
theorem tp_L_strictAnti_z_of_neg {α ν ω K : ℝ} (hν : 0 < ν) (hω : 0 < ω)
    (hK : 0 < K) (he : α + ν - 1 < 0) : StrictAntiOn (fun z => tpL α ν ω z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ _ h
  have hc : 0 < (1 - α) / (ω * ν) := div_pos (by linarith) (mul_pos hω hν)
  have h1 := Real.rpow_lt_rpow_of_neg hz₁ h (one_div_neg.2 he)
  have h2 := Real.rpow_pos_of_pos hc (1 / (α + ν - 1))
  have h3 := Real.rpow_pos_of_pos hK (α / (α + ν - 1))
  simp only [tpL]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 h2) h3

/-- AKMM, pp. 584–585: in period 0 with working capital, (19.18) `F₃ = (1 + µ)w` with
`F₃ = (1 − α)zK^αL^{−α}` and the household's `w = νL^{ν−1}` give
`(1 − α)zK^αL^{−α} = (1 + µ)νL^{ν−1}`, so `L = ((1 − α)/((1 + µ)ν))^{1/e} z^{1/e} K^{α/e}`
(`µ > −1`). -/
theorem tp_wc_labour {α ν μ z K L w : ℝ} (hα : α < 1) (hν : 0 < ν) (hμ : -1 < μ) (hz : 0 < z)
    (hK : 0 < K) (hL : 0 < L) (he : α + ν - 1 ≠ 0)
    (h1918 : (1 - α) * z * K ^ α * L ^ (-α) = (1 + μ) * w) (h198 : w = ν * L ^ (ν - 1)) :
    L = tpL α ν (1 + μ) z K := by
  refine (tp_foc_iff hα hν (by linarith) hz hK hL he).1 ?_
  rw [← tp_mpl_eq hK.le hL.le, h1918, h198]
  ring

/-- **Property 19.5.6** (AKMM, pp. 584–585): with working capital, period-0 labour
`L = ((1 − α)/((1 + µ)ν))^{1/e} z^{1/e} K^{α/e}` is strictly decreasing in the multiplier `µ`
(`µ > −1`, `e > 0`). -/
theorem property_19_5_6 {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictAntiOn (fun μ => tpL α ν (1 + μ) z K) (Ioi (-1)) := by
  intro μ₁ hμ₁ μ₂ hμ₂ h
  have h1 : 0 < 1 + μ₁ := by simp only [mem_Ioi] at hμ₁; linarith
  have h2 : 0 < 1 + μ₂ := by simp only [mem_Ioi] at hμ₂; linarith
  have hb : (1 - α) / ((1 + μ₂) * ν) < (1 - α) / ((1 + μ₁) * ν) :=
    div_lt_div_of_pos_left (by linarith) (mul_pos h1 hν) (by nlinarith)
  have hc2 : 0 < (1 - α) / ((1 + μ₂) * ν) := div_pos (by linarith) (mul_pos h2 hν)
  have hr := Real.rpow_lt_rpow hc2.le hb (one_div_pos.2 he)
  have hz' := Real.rpow_pos_of_pos hz (1 / (α + ν - 1))
  have hK' := Real.rpow_pos_of_pos hK (α / (α + ν - 1))
  simp only [tpL]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hr hz') hK'

/-! ### Output, the marginal product of capital and `g` -/

/-- **Output** (AKMM, p. 577): `zK^αL^{1−α}` at the equilibrium labour is
`((1 − α)/ν)^{(1−α)/e} z^{ν/e} K^{να/e}`. -/
theorem tp_Y_eq {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) : z * K ^ α * tpL α ν 1 z K ^ (1 - α) = tpY α ν z K := by
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  unfold tpL tpY
  rw [one_mul, Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hz.le _))
    (Real.rpow_nonneg hK.le _), Real.mul_rpow (Real.rpow_nonneg hc.le _)
    (Real.rpow_nonneg hz.le _), ← Real.rpow_mul hc.le, ← Real.rpow_mul hz.le,
    ← Real.rpow_mul hK.le]
  have e1 : ν / (α + ν - 1) = 1 + 1 / (α + ν - 1) * (1 - α) := by field_simp; ring
  have e2 : ν * α / (α + ν - 1) = α + α / (α + ν - 1) * (1 - α) := by field_simp; ring
  have e3 : (1 - α) / (α + ν - 1) = 1 / (α + ν - 1) * (1 - α) := by ring
  rw [e1, e2, e3, Real.rpow_add hz, Real.rpow_add hK, Real.rpow_one]
  ring

/-- AKMM, p. 578: `F_k = αY/K` at the equilibrium labour, the printed closed form. -/
theorem tp_Fk_eq {α ν z K : ℝ} (hK : 0 < K) : α * tpY α ν z K / K = tpFk α ν z K := by
  unfold tpY tpFk
  rw [Real.rpow_sub_one hK.ne']
  ring

/-- AKMM, p. 578: the marginal product of capital at the equilibrium labour,
`∂/∂K [zK^αL^{1−α}]` at `L = L(z, K)`, is `tpFk`. -/
theorem tp_mpk_eq {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) :
    HasDerivAt (fun k => z * k ^ α * tpL α ν 1 z K ^ (1 - α)) (tpFk α ν z K) K := by
  refine (tp_mpk hK).congr_deriv ?_
  rw [tp_Y_eq hα hν hz hK he, tp_Fk_eq hK]

/-- AKMM, p. 577: output increases in `z` (`e > 0`). -/
theorem tp_Y_strictMono_z {α ν K : ℝ} (hα : α < 1) (hν : 0 < ν) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpY α ν z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ _ h
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  have h1 := Real.rpow_lt_rpow (le_of_lt hz₁) h (div_pos hν he)
  have h2 := Real.rpow_pos_of_pos hc ((1 - α) / (α + ν - 1))
  have h3 := Real.rpow_pos_of_pos hK (ν * α / (α + ν - 1))
  simp only [tpY]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 h2) h3

/-- AKMM, p. 577: output increases in `K` (`α > 0`, `e > 0`). -/
theorem tp_Y_strictMono_K {α ν z : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hz : 0 < z)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun K => tpY α ν z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ _ h
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  have h1 := Real.rpow_lt_rpow (le_of_lt hK₁) h (div_pos (mul_pos hν hα0) he)
  have h2 := mul_pos (Real.rpow_pos_of_pos hc ((1 - α) / (α + ν - 1)))
    (Real.rpow_pos_of_pos hz (ν / (α + ν - 1)))
  simp only [tpY]
  exact mul_lt_mul_of_pos_left h1 h2

/-- Output is positive. -/
theorem tp_Y_pos {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K) :
    0 < tpY α ν z K := by
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) hν
  unfold tpY
  have := Real.rpow_pos_of_pos hc ((1 - α) / (α + ν - 1))
  have := Real.rpow_pos_of_pos hz (ν / (α + ν - 1))
  have := Real.rpow_pos_of_pos hK (ν * α / (α + ν - 1))
  positivity

/-- AKMM, p. 579: "an increase in `z′` raises the marginal productivity of capital"
(`α > 0`, `e > 0`). -/
theorem tp_Fk_strictMono_z {α ν K : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpFk α ν z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ hz₂ h
  simp only
  rw [← tp_Fk_eq hK, ← tp_Fk_eq hK]
  have := tp_Y_strictMono_z hα hν hK he hz₁ hz₂ h
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left this hα0) hK

/-- AKMM, pp. 579, 582: the marginal product of capital is strictly decreasing in `K`
(`0 < α < 1`, `ν > 1`). -/
theorem tp_Fk_strictAnti_K {α ν z : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 1 < ν) (hz : 0 < z) :
    StrictAntiOn (fun K => tpFk α ν z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ _ h
  have he : 0 < α + ν - 1 := by linarith
  have hc : 0 < (1 - α) / ν := div_pos (by linarith) (by linarith)
  have hexp : ν * α / (α + ν - 1) - 1 < 0 := by
    rw [sub_neg, div_lt_one he]
    nlinarith
  have h1 := Real.rpow_lt_rpow_of_neg hK₁ h hexp
  have h2 : 0 < α * ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) * z ^ (ν / (α + ν - 1)) :=
    mul_pos (mul_pos hα0 (Real.rpow_pos_of_pos hc _)) (Real.rpow_pos_of_pos hz _)
  simp only [tpFk]
  exact mul_lt_mul_of_pos_left h1 h2

/-- The marginal product of capital is positive. -/
theorem tp_Fk_pos {α ν z K : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν) (hz : 0 < z)
    (hK : 0 < K) : 0 < tpFk α ν z K := by
  rw [← tp_Fk_eq hK]
  have := tp_Y_pos hα hν hz hK
  positivity

/-- AKMM, p. 577: at the equilibrium labour, `L^ν = (1 − α)Y/ν`. -/
theorem tp_L_pow_nu {α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) : tpL α ν 1 z K ^ ν = (1 - α) / ν * tpY α ν z K := by
  have hc : 0 < (1 - α) / (1 * ν) := div_pos (by linarith) (by linarith)
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hA : 0 < (1 - α) / (1 * ν) * z * K ^ α := by positivity
  have hL : tpL α ν 1 z K = ((1 - α) / (1 * ν) * z * K ^ α) ^ (1 / (α + ν - 1)) :=
    tp_L_eq hc.le hz.le hK.le
  have hLpos : 0 < tpL α ν 1 z K := by rw [hL]; exact Real.rpow_pos_of_pos hA _
  have hLe : tpL α ν 1 z K ^ (α + ν - 1) = (1 - α) / (1 * ν) * z * K ^ α := by
    rw [hL, one_div, Real.rpow_inv_rpow hA.le he]
  have hsplit : tpL α ν 1 z K ^ ν = tpL α ν 1 z K ^ (α + ν - 1) * tpL α ν 1 z K ^ (1 - α) := by
    rw [← Real.rpow_add hLpos]
    ring_nf
  rw [← tp_Y_eq hα hν hz hK he, hsplit, hLe, one_mul]
  ring

/-- AKMM, p. 577: `g(z, K) = C − L^ν = (1 − δ)K + ((α + ν − 1)/ν)Y`. -/
theorem tp_g_eq {δ α ν z K : ℝ} (hα : α < 1) (hν : 0 < ν) (hz : 0 < z) (hK : 0 < K)
    (he : α + ν - 1 ≠ 0) :
    tpG δ α ν z K = (1 - δ) * K + (α + ν - 1) / ν * tpY α ν z K := by
  unfold tpG
  rw [tp_L_pow_nu hα hν hz hK he]
  field_simp
  ring

/-- AKMM, p. 577: "`g(z′, K′)` is increasing in `z′`" (`e > 0`). -/
theorem tp_g_strictMono_z {δ α ν K : ℝ} (hα : α < 1) (hν : 0 < ν) (hK : 0 < K)
    (he : 0 < α + ν - 1) : StrictMonoOn (fun z => tpG δ α ν z K) (Ioi 0) := by
  intro z₁ hz₁ z₂ hz₂ h
  simp only
  rw [tp_g_eq hα hν hz₁ hK he.ne', tp_g_eq hα hν hz₂ hK he.ne']
  have := tp_Y_strictMono_z hα hν hK he hz₁ hz₂ h
  have hcoef : 0 < (α + ν - 1) / ν := div_pos he hν
  nlinarith

/-- AKMM, p. 577: "`g(z′, K′)` is increasing in `K′`" (`α > 0`, `e > 0`, `δ ≤ 1`), on the
whole positive half-line. -/
theorem tp_g_strictMono_K {δ α ν z : ℝ} (hδ : δ ≤ 1) (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν)
    (hz : 0 < z) (he : 0 < α + ν - 1) : StrictMonoOn (fun K => tpG δ α ν z K) (Ioi 0) := by
  intro K₁ hK₁ K₂ hK₂ h
  simp only
  rw [tp_g_eq hα hν hz hK₁ he.ne', tp_g_eq hα hν hz hK₂ he.ne']
  have := tp_Y_strictMono_K hα0 hα hν hz he hK₁ hK₂ h
  have hcoef : 0 < (α + ν - 1) / ν := div_pos he hν
  nlinarith

/-- `g` is positive (`e > 0`, `δ ≤ 1`). -/
theorem tp_g_pos {δ α ν z K : ℝ} (hδ : δ ≤ 1) (hα : α < 1) (hν : 0 < ν) (hz : 0 < z)
    (hK : 0 < K) (he : 0 < α + ν - 1) : 0 < tpG δ α ν z K := by
  rw [tp_g_eq hα hν hz hK he.ne']
  have := tp_Y_pos hα hν hz hK
  have : 0 ≤ (1 - δ) * K := mul_nonneg (by linarith) hK.le
  have : 0 < (α + ν - 1) / ν * tpY α ν z K := by positivity
  linarith

end AKMM.CreditFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period system, the price of capital, slack limits and working capital

AKMM, §19.5, (19.11)–(19.16), pp. 577–579; §19.5.2, Property 19.5.2, pp. 580–581; §19.5.4,
Property 19.5.4, p. 582; §19.5.5, (19.17)–(19.18), p. 584.

* **Period 1** (p. 577): with `k₂ = b₂ = 0`, no terminal dividend cost and `p′ = 1`, the
  budgets give `C′ = (1 − δ)K′ + Y′` (`sys_terminal_C`).
* **(19.11)–(19.16)** (pp. 578–579): the general conditions (19.5), (19.6), (19.9), the binding
  limit, the budgets of firm and household and `T = B′/R̃ − B′/R`, with `u = ln(c − ℓ^ν)`
  (so `βu₁′/u₁ = β(C − L^ν)/g(z′, K′)`), `wL = (1 − α)F`, `p′ = 1`, `ϕ′(D′) = 1`, give the six
  equations (`system_19_11_to_19_16`).
* **Property 19.5.2** (pp. 580–581): the elasticity of net worth `pK − B` in `p` is
  `pK/(pK − B)`, greater than one iff `B > 0` (`sys_networth_elasticity`,
  `property_19_5_2_networth`); the rearranged budget
  `K′ = [(1 − δ)K + (αF − B − D − κ(D − φ)²)/p]/(1 − ξ)` (`sys_Kprime_eq`); holding `D` fixed,
  `∂K′/∂p = −N/(p²(1 − ξ))` with `N = αF − B − D − κ(D − φ)²`, positive iff `N < 0`
  (`sys_hasDerivAt_Kprime`, `property_19_5_2`), and its size increases with `ξ`
  (`sys_multiplier_mono`). `B > 0` does not give `N < 0` (`sys_B_pos_not_sufficient`).
* **Property 19.5.4** (p. 582): with `µ = 0` the conditions (19.11), (19.13)–(19.16) do not
  involve `ξ` and the limit stays slack for `ξ′ ≥ ξ`, so an equilibrium with a slack limit
  remains one (`property_19_5_4`). For an abstract concave problem with a linear limit, a
  strictly slack optimum is a global unconstrained optimum and stays optimal for `ξ′ ≥ ξ`
  (`sys_slack_global`, `property_19_5_4_opt`).
* **Working capital** (p. 584): the Lagrangian conditions with the limit
  `wℓ + b′/R_c ≤ ξpk′` give (19.18) `F_ℓ = (1 + µ)w` (`eq_19_18`); (19.5) is unchanged
  (`sys_wc_19_5`); with `R_c = R̃` (19.6) is unchanged (`sys_wc_19_6_tilde`), but with the
  printed `R_c = R` it becomes `E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ/(1 + τ)`
  (`sys_wc_19_6_printed`), different from `1 − µ` when `µ ≠ 0`, `τ ≠ 0`
  (`sys_wc_19_6_printed_ne`).
-/

namespace AKMM.CreditFrictions

open Set

/-- AKMM, p. 577: "all resources are consumed": with `k₂ = b₂ = 0`, no dividend cost and
`p′ = 1`, the firm's period-1 budget `F′ − w′L′ = B′ + (0 − (1 − δ)K′) + D′` and the
household's `D′ + B′ + w′L′ = C′` give `C′ = (1 − δ)K′ + F′`. -/
theorem sys_terminal_C {F' w' L' B' K' δ D' C' : ℝ}
    (hfirm : F' - w' * L' = B' + 1 * (0 - (1 - δ) * K') + D')
    (hhh : D' + B' + w' * L' = C') : C' = (1 - δ) * K' + F' := by
  linarith

/-- **(19.11)–(19.16)** (AKMM, pp. 578–579). In period 0, with the firm's discount factor
`m = βu₁(C′, L′)/u₁(C, L)` for `u₁ = 1/(c − ℓ^ν)` and `C′ − L′^ν = g`, the conditions
(19.5) `m ϕ′(D)/1 · ((1 − δ)·1 + F_k′) = (1 − µξ)p` and (19.6) `m ϕ′(D)/1 · R̃ = 1 − µ`,
(19.9) `1/R = m`, the binding limit `B′/R̃ = ξpK′`, `R̃ = R/(1 + τ)`, the firm's budget, the
wage bill `wL = (1 − α)F`, the household's budget with `A = A′ = 1` and the tax
`T = B′/R̃ − B′/R` imply the six equations (19.11)–(19.16). -/
theorem system_19_11_to_19_16 {β C L ν g δ Fk μ ξ p κ φ D Rt R τ B' K' F w B K α T m : ℝ}
    (hg : g ≠ 0) (hCL : C - L ^ ν ≠ 0) (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (hm : m = β * (1 / g) / (1 / (C - L ^ ν)))
    (h195 : m * (cfPhiD κ φ D / 1) * ((1 - δ) * 1 + Fk) = (1 - μ * ξ) * p)
    (h196 : m * (cfPhiD κ φ D / 1) * Rt = 1 - μ) (h199 : 1 / R = m)
    (hbind : B' / Rt = ξ * p * K') (hRt : Rt = R / (1 + τ))
    (hfirm : F - w * L + B' / Rt = B + p * (K' - (1 - δ) * K) + cfPhi κ φ D)
    (hw : w * L = (1 - α) * F) (hhh : (D + 1) * 1 + B + w * L = C + 1 * 1 + B' / R + T)
    (hT : T = B' / Rt - B' / R) :
    (1 - μ * ξ) * p = β * ((C - L ^ ν) / g) * (1 - δ + Fk) * (1 + 2 * κ * (D - φ)) ∧
    (1 + τ) * B' / R = ξ * p * K' ∧
    α * F + (1 + τ) * B' / R = B + p * (K' - (1 - δ) * K) + D + κ * (D - φ) ^ 2 ∧
    (D + B + (1 - α) * F = C + B' / R + T ∧ T = τ * B' / R) ∧
    (1 - μ) * (1 + τ) / R = β * ((C - L ^ ν) / g) * (1 + 2 * κ * (D - φ)) ∧
    1 / R = β * ((C - L ^ ν) / g) := by
  have hmg : m = β * ((C - L ^ ν) / g) := by rw [hm]; field_simp
  have hB : B' / Rt = (1 + τ) * B' / R := by rw [hRt]; field_simp
  have hTt : T = τ * B' / R := by rw [hT, hRt, hh_tax hR]
  refine ⟨?_, ?_, ?_, ⟨?_, hTt⟩, ?_, ?_⟩
  · rw [← h195, hmg]
    unfold cfPhiD
    ring
  · rw [← hB, hbind]
  · rw [← hB]
    unfold cfPhi at hfirm
    linarith
  · linarith
  · have : (1 - μ) * (1 + τ) / R = m * cfPhiD κ φ D := by
      rw [← h196, hRt]
      field_simp
    rw [this, hmg]
    unfold cfPhiD
    ring
  · rw [h199, hmg]

/-! ### Property 19.5.2: the price of capital -/

/-- AKMM, p. 580: the elasticity of net worth `n(p) = pK − B` in `p`,
`n′(p)·p/n(p) = pK/(pK − B)`. -/
theorem sys_networth_elasticity {p K B : ℝ} :
    HasDerivAt (fun x => x * K - B) K p ∧ K * p / (p * K - B) = p * K / (p * K - B) := by
  refine ⟨?_, by ring⟩
  simpa using ((hasDerivAt_id p).mul_const K).sub_const B

/-- **Property 19.5.2, net worth** (AKMM, p. 580): "Provided that `B > 0`, a 1 percent increase in
`p` generates an increase in net worth larger than 1 percent": with positive net worth
`pK − B > 0` and `p, K > 0`, the elasticity `pK/(pK − B)` exceeds one iff `B > 0`; and for a
finite rise `p₀ < p₁`, `(p₁K − B)/(p₀K − B) > p₁/p₀` iff `B > 0`. -/
theorem property_19_5_2_networth {p K B : ℝ} (hn : 0 < p * K - B) :
    (1 < p * K / (p * K - B) ↔ 0 < B) ∧
    ∀ {p₀ p₁ : ℝ}, 0 < p₀ → p₀ < p₁ → 0 < p₀ * K - B → 0 < K →
      (p₁ / p₀ < (p₁ * K - B) / (p₀ * K - B) ↔ 0 < B) := by
  refine ⟨?_, ?_⟩
  · rw [one_lt_div hn]
    constructor <;> intro h <;> linarith
  · intro p₀ p₁ h0 h01 hn0 hK
    rw [div_lt_div_iff₀ h0 hn0]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith

/-- AKMM, p. 580: using (19.12) in (19.13), `αF + ξpK′ = B + p[K′ − (1 − δ)K] + D + κ(D − φ)²`,
the budget rearranges to `K′ = [(1 − δ)K + (αF − B − D − κ(D − φ)²)/p]/(1 − ξ)`. -/
theorem sys_Kprime_eq {α F ξ p K' B δ K D κ φ : ℝ} (hp : p ≠ 0) (hξ : ξ ≠ 1)
    (h : α * F + ξ * p * K' = B + p * (K' - (1 - δ) * K) + D + κ * (D - φ) ^ 2) :
    K' = 1 / (1 - ξ) * ((1 - δ) * K + (α * F - B - D - κ * (D - φ) ^ 2) / p) := by
  have h1 : 1 - ξ ≠ 0 := sub_ne_zero.2 (Ne.symm hξ)
  field_simp
  linear_combination -h

/-- AKMM, p. 580: holding the other terms fixed, the rearranged `K′` has derivative
`−N/(p²(1 − ξ))` in `p`, `N = αF − B − D − κ(D − φ)²`. -/
theorem sys_hasDerivAt_Kprime {ξ δ K N p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun x => 1 / (1 - ξ) * ((1 - δ) * K + N / x)) (-N / (p ^ 2 * (1 - ξ))) p := by
  have h := ((hasDerivAt_inv hp).const_mul N).const_add ((1 - δ) * K) |>.const_mul (1 / (1 - ξ))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · rw [div_eq_mul_inv (-N), mul_inv]
    ring
  · simp only [div_eq_mul_inv]

/-- **Property 19.5.2** (AKMM, pp. 580–581): with a binding limit and `ξ < 1`, holding dividends
and the period-0 terms fixed, a higher price of capital raises `K′` iff the profits net of
liabilities and dividends `N = αF − B − D − κ(D − φ)²` are negative. -/
theorem property_19_5_2 {ξ N p : ℝ} (hp : p ≠ 0) (hξ : ξ < 1) :
    0 < -N / (p ^ 2 * (1 - ξ)) ↔ N < 0 := by
  have hd : 0 < p ^ 2 * (1 - ξ) := mul_pos (by positivity) (by linarith)
  rw [div_pos_iff_of_pos_right hd]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 580: "The first term … acts as a multiplier, and depends positively on `ξ`": for
`N < 0` the response `−N/(p²(1 − ξ))` increases with `ξ < 1`. -/
theorem sys_multiplier_mono {N p ξ₁ ξ₂ : ℝ} (hN : N < 0) (hp : p ≠ 0) (h₁₂ : ξ₁ < ξ₂)
    (h₂ : ξ₂ < 1) : -N / (p ^ 2 * (1 - ξ₁)) < -N / (p ^ 2 * (1 - ξ₂)) := by
  have hp2 : 0 < p ^ 2 := by positivity
  exact div_lt_div_of_pos_left (by linarith) (mul_pos hp2 (by linarith))
    (mul_lt_mul_of_pos_left (by linarith) hp2)

/-- AKMM, p. 580 (correction): `B > 0`, the hypothesis of Property 19.5.2, does not give
`N = αF − B − D − κ(D − φ)² < 0`: with `αF = 2`, `B = 1`, `D = 0`, `κ = 0` the response of
`K′` to `p` is negative. -/
theorem sys_B_pos_not_sufficient :
    ∃ αF B D κ φ : ℝ, 0 < B ∧ 0 < αF - B - D - κ * (D - φ) ^ 2 :=
  ⟨2, 1, 0, 0, 0, by norm_num, by norm_num⟩

/-! ### Property 19.5.4: a slack constraint -/

/-- **Property 19.5.4** (AKMM, p. 582). If the limit is slack at an equilibrium for `ξ`
(`µ = 0`), then (19.11) holds at every `ξ′` (it involves `ξ` only through `µξ`), the other
conditions (19.13)–(19.16) do not involve `ξ`, and for `ξ′ ≥ ξ` (with `pK′ ≥ 0`) the limit
remains satisfied with `µ = 0` and complementary slackness: the same allocation is an
equilibrium, so an increase in `ξ` has no effect. -/
theorem property_19_5_4 {p rhs K' B' R τ ξ ξ' : ℝ} (hpK : 0 ≤ p * K')
    (h1911 : (1 - 0 * ξ) * p = rhs) (hlim : (1 + τ) * B' / R ≤ ξ * p * K') (hξ : ξ ≤ ξ') :
    (1 - 0 * ξ') * p = rhs ∧ (1 + τ) * B' / R ≤ ξ' * p * K' ∧
      (0 : ℝ) * (ξ' * p * K' - (1 + τ) * B' / R) = 0 := by
  refine ⟨by rw [← h1911]; ring, ?_, by ring⟩
  have : ξ * (p * K') ≤ ξ' * (p * K') := mul_le_mul_of_nonneg_right hξ hpK
  nlinarith

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A strictly slack optimum of a concave problem with a linear limit `b(x) ≤ ξa(x)` is a global
optimum on the convex set `X`. -/
theorem sys_slack_global {X : Set E} {J : E → ℝ} {a b : E →ₗ[ℝ] ℝ} {ξ : ℝ} {x : E}
    (hJ : ConcaveOn ℝ X J) (hx : x ∈ X) (hslack : b x < ξ * a x)
    (hopt : ∀ y ∈ X, b y ≤ ξ * a y → J y ≤ J x) : ∀ y ∈ X, J y ≤ J x := by
  intro y hy
  by_contra hc
  push Not at hc
  set s := ξ * a x - b x with hs
  set r := b y - ξ * a y with hr
  have hs0 : 0 < s := by rw [hs]; linarith
  rcases le_or_gt r 0 with hr0 | hr0
  · exact absurd (hopt y hy (by rw [hr] at hr0; linarith)) (not_le.2 hc)
  · set t := s / (s + r) with ht
    have hsr : 0 < s + r := by linarith
    have ht0 : 0 < t := div_pos hs0 hsr
    have ht1 : t < 1 := (div_lt_one hsr).2 (by linarith)
    have hz : (1 - t) • x + t • y ∈ X := hJ.1 hx hy (by linarith) ht0.le (by ring)
    have hfeas : b ((1 - t) • x + t • y) ≤ ξ * a ((1 - t) • x + t • y) := by
      simp only [map_add, map_smul, smul_eq_mul]
      have e : (1 - t) * b x + t * b y - ξ * ((1 - t) * a x + t * a y) = t * r - (1 - t) * s := by
        rw [hr, hs]; ring
      have e2 : t * r - (1 - t) * s = 0 := by
        rw [ht]; field_simp; ring
      linarith
    have h1 := hopt _ hz hfeas
    have h2 := hJ.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at h2
    nlinarith

/-- **Property 19.5.4, optimisation form** (AKMM, p. 582): "if they were not borrowing up to
the limit before … there is no reason for them to change that level of borrowing when the limit
expands". For a concave objective on a convex set with the limit `b(x) ≤ ξa(x)`, `a ≥ 0`, a
strictly slack optimum at `ξ` is feasible and optimal at every `ξ′ ≥ ξ`. -/
theorem property_19_5_4_opt {X : Set E} {J : E → ℝ} {a b : E →ₗ[ℝ] ℝ} {ξ ξ' : ℝ} {x : E}
    (hJ : ConcaveOn ℝ X J) (hx : x ∈ X) (ha : 0 ≤ a x) (hξ : ξ ≤ ξ')
    (hslack : b x < ξ * a x) (hopt : ∀ y ∈ X, b y ≤ ξ * a y → J y ≤ J x) :
    b x ≤ ξ' * a x ∧ ∀ y ∈ X, b y ≤ ξ' * a y → J y ≤ J x := by
  refine ⟨by nlinarith, fun y hy _ => sys_slack_global hJ hx hslack hopt y hy⟩

/-! ### Working capital -/

/-- **(19.18)** (AKMM, p. 584): with the working-capital limit `wℓ + b′/R_c ≤ ξpk′` (multiplier
`µλ`), the first-order condition for labour `λ(F_ℓ − w) − µλw = 0`, `λ ≠ 0`, gives
`F_ℓ = (1 + µ)w`. -/
theorem eq_19_18 {lam Fl w μ : ℝ} (hlam : lam ≠ 0) (h : lam * (Fl - w) - μ * lam * w = 0) :
    Fl = (1 + μ) * w := by
  have : lam * (Fl - (1 + μ) * w) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hlam
  · linarith

variable {S : Type*} [Fintype S]

/-- AKMM, p. 584: with working capital the first-order condition for `k′` is the same as
before, so (19.5) is unchanged. -/
theorem sys_wc_19_5 (pr m lams Ωk p' Fk q' : S → ℝ) (lam q μ ξ p δ : ℝ) (hq : 1 = lam * q)
    (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωk s) - lam * p + μ * lam * ξ * p = 0)
    (henv : ∀ s, Ωk s = lams s * ((1 - δ) * p' s + Fk s)) :
    ∑ s, pr s * (m s * (q / q' s * ((1 - δ) * p' s + Fk s))) = (1 - μ * ξ) * p :=
  eq_19_5 pr m lams Ωk p' Fk q' lam q μ ξ p δ hq hqs hfoc henv

/-- AKMM, p. 584: with the limit `wℓ + b′/R̃ ≤ ξpk′` the first-order condition for `b′` is
`E[m′Ω_b′] + λ/R̃ − µλ/R̃ = 0`, so (19.6) is unchanged. -/
theorem sys_wc_19_6_tilde (pr m lams Ωb q' : S → ℝ) (lam q μ Rt : ℝ) (hRt : Rt ≠ 0)
    (hq : 1 = lam * q) (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωb s) + lam / Rt - μ * lam / Rt = 0)
    (henv : ∀ s, Ωb s = -lams s) :
    (∑ s, pr s * (m s * (q / q' s))) * Rt = 1 - μ :=
  eq_19_6 pr m lams Ωb q' lam q μ Rt hRt hq hqs hfoc henv

/-- AKMM, (19.17), p. 584, as printed (`wℓ + b′/R ≤ ξpk′`, `R = (1 + τ)R̃`): the first-order
condition for `b′` is `E[m′Ω_b′] + λ/R̃ − µλ/R = 0`, and (19.6) becomes
`E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ/(1 + τ)`. -/
theorem sys_wc_19_6_printed (pr m lams Ωb q' : S → ℝ) (lam q μ Rt τ : ℝ) (hRt : Rt ≠ 0)
    (hτ : 1 + τ ≠ 0) (hq : 1 = lam * q) (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωb s) + lam / Rt - μ * lam / ((1 + τ) * Rt) = 0)
    (henv : ∀ s, Ωb s = -lams s) :
    (∑ s, pr s * (m s * (q / q' s))) * Rt = 1 - μ / (1 + τ) := by
  refine eq_19_6 pr m lams Ωb q' lam q (μ / (1 + τ)) Rt hRt hq hqs ?_ henv
  rw [← hfoc]
  field_simp

/-- AKMM, p. 584 (correction): under the printed (19.17), the condition of
`sys_wc_19_6_printed` is not (19.6) whenever `µ ≠ 0` and `τ ≠ 0`: `1 − µ/(1 + τ) ≠ 1 − µ`. -/
theorem sys_wc_19_6_printed_ne {μ τ : ℝ} (hμ : μ ≠ 0) (hτ : τ ≠ 0) (hτ1 : 1 + τ ≠ 0) :
    1 - μ / (1 + τ) ≠ 1 - μ := by
  intro h
  have : μ / (1 + τ) = μ := by linarith
  rw [div_eq_iff hτ1] at this
  have : μ * τ = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hμ h1
  · exact hτ h1

end AKMM.CreditFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Comparative statics of the two-period model: Properties 19.5.1, 19.5.3 and 19.5.5

AKMM, §19.5.1, Property 19.5.1, pp. 579–580; §19.5.3, Property 19.5.3, pp. 581–582; §19.5.4,
Property 19.5.5, pp. 582–583.

The book argues these properties from (19.11)–(19.13) and (19.15) "keeping other things
unchanged". We prove them for the firm's problem at given prices: the interest rate `R` and the
discount factor `Λ = β(C − L^ν)/g(z′, K′) = 1/R` are held fixed, as in the book's argument
(they are general-equilibrium objects the book does not sign). The equations are

* (19.11) `(1 − µξ)p = Λ(1 − δ + F_k(K′))ϕ′(D)`,
* (19.15) `(1 − µ)(1 + τ)/R = Λϕ′(D)`,
* the budget with the binding limit (19.12)–(19.13), `αF + ξpK′ = B + p[K′ − (1 − δ)K] + ϕ(D)`.

From (19.11) and (19.15), `Λ(1 − δ + F_k) = p[(1 − ξ)/ϕ′(D) + ξc]`, `c = RΛ/(1 + τ)`, and
`µ = 1 − cϕ′(D)` (`cs_return`, `cs_mu`): the effective cost of capital is a weighted average of
`1/ϕ′(D)` (equity) and `c` (debt), with `c < 1/ϕ′(D)` exactly when the limit binds.

* **Property 19.5.3** (`property_19_5_3`): with a binding limit (`µ₀ > 0`), a lower `ξ` lowers
  `K′`; hence next period's output and employment fall (`property_19_5_3_output`). No sign
  condition beyond `κ ≥ 0`, `ϕ′ > 0`, `ξ ≤ 1` and `F_k` decreasing is needed. In general
  equilibrium with `κ = 0` (so `µ = τ/(1 + τ)`), the same holds when `C − L^ν = W − pK′`,
  `F_k` decreases and `g` increases in `K′` (`property_19_5_3_ge`).
* **Property 19.5.1** (`property_19_5_1`): a rise in `z′` with current profits `αF` not falling
  raises `K′` with a binding limit, and also with a slack one (`property_19_5_1_slack`). With
  the closed-form `F_k` (`ν > 1`), if dividends fall (`D₁ < D₀`, which holds automatically when
  only `z′` changes, `cs_div_falls`) the proportional response of `K′` is strictly smaller with
  the binding limit than with a slack one (`property_19_5_1_dampening`).
* **Property 19.5.5** (`property_19_5_5`): starting from a slack solution, a fall in `ξ` large
  enough that the old plan violates the limit (`ξ₁pK₀′ < B₀′/R̃`) forces the limit to bind and
  strictly lowers `K′` (`κ > 0`, `ξ₁ < 1`); next period's output and employment fall
  (`property_19_5_5_output`).
-/

namespace AKMM.CreditFrictions

open Set

/-- AKMM, (19.11) and (19.15): the return to capital equals the effective cost,
`Λ(1 − δ + F_k) = p[(1 − ξ)/ϕ′(D) + ξRΛ/(1 + τ)]`. -/
theorem cs_return {Λ R τ p δ Fk ξ μ q : ℝ} (hq : 0 < q) (hτ : 0 < 1 + τ) (hR : 0 < R)
    (h1911 : (1 - μ * ξ) * p = Λ * (1 - δ + Fk) * q) (h1915 : (1 - μ) * (1 + τ) / R = Λ * q) :
    Λ * (1 - δ + Fk) = p * ((1 - ξ) / q + ξ * (R * Λ / (1 + τ))) := by
  have h' : (1 - μ) * (1 + τ) = R * Λ * q := by
    rw [div_eq_iff hR.ne'] at h1915
    linarith
  have hc : R * Λ / (1 + τ) * q = 1 - μ := by
    rw [div_mul_eq_mul_div, div_eq_iff hτ.ne']
    linarith
  have e : Λ * (1 - δ + Fk) * q = p * ((1 - ξ) / q + ξ * (R * Λ / (1 + τ))) * q := by
    rw [← h1911, mul_assoc p, add_mul, div_mul_cancel₀ _ hq.ne', mul_assoc ξ, hc]
    ring
  exact mul_right_cancel₀ hq.ne' e

/-- AKMM, (19.15): `µ = 1 − cϕ′(D)` with `c = RΛ/(1 + τ)`. -/
theorem cs_mu {Λ R τ μ q : ℝ} (hτ : 0 < 1 + τ) (hR : 0 < R)
    (h1915 : (1 - μ) * (1 + τ) / R = Λ * q) : μ = 1 - R * Λ / (1 + τ) * q := by
  have h' : (1 - μ) * (1 + τ) = R * Λ * q := by
    rw [div_eq_iff hR.ne'] at h1915
    linarith
  have hc : R * Λ / (1 + τ) * q = 1 - μ := by
    rw [div_mul_eq_mul_div, div_eq_iff hτ.ne']
    linarith
  linarith

/-- **Property 19.5.3** (AKMM, pp. 581–582). Let `(K₀, D₀, µ₀)` solve (19.11), (19.15) and the
budget with the binding limit at `ξ₀`, with `µ₀ > 0`, and `(K₁, D₁, µ₁)` solve them at
`ξ₁ < ξ₀ ≤ 1`, with `ϕ′(D₀), ϕ′(D₁) > 0`, `κ ≥ 0`, at the same prices `R, Λ > 0` and with
`F_k` strictly decreasing. Then `K₁ < K₀`: "a negative financial shock has a negative impact on
capital accumulation". -/
theorem property_19_5_3 {Fk : ℝ → ℝ} (hFk : StrictAntiOn Fk (Ioi 0))
    {Λ R τ p δ α F B K κ φ ξ₀ ξ₁ K₀ K₁ D₀ D₁ μ₀ μ₁ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hp : 0 < p) (hR : 0 < R) (hτ : 0 < 1 + τ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hξ : ξ₁ < ξ₀) (hξ1 : ξ₀ ≤ 1) (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - μ₀ * ξ₀) * p = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - μ₀) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h13₀ : α * F + ξ₀ * p * K₀ = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (h11₁ : (1 - μ₁ * ξ₁) * p = Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (h13₁ : α * F + ξ₁ * p * K₁ = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁)
    (hμ₀ : 0 < μ₀) : K₁ < K₀ := by
  by_contra hc
  push Not at hc
  set c := R * Λ / (1 + τ) with hcdef
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  have hm₀ := cs_mu hτ hR h15₀
  -- the binding limit: `c < 1/ϕ′(D₀)`
  have hc0 : c < 1 / cfPhiD κ φ D₀ := by
    rw [lt_div_iff₀ hq₀]
    linarith
  -- dividends fall
  have hphi : cfPhi κ φ D₁ < cfPhi κ φ D₀ := by
    have : (1 - ξ₀) * K₀ < (1 - ξ₁) * K₁ := by nlinarith
    nlinarith
  have hD := div_lt_of_phi_lt hq₀ hq₁ hphi
  have hqq : cfPhiD κ φ D₁ ≤ cfPhiD κ φ D₀ := div_phiD_le hκ hD.le
  have hinv : 1 / cfPhiD κ φ D₀ ≤ 1 / cfPhiD κ φ D₁ := one_div_le_one_div_of_le hq₁ hqq
  -- the effective cost rises
  have hcost : (1 - ξ₀) / cfPhiD κ φ D₀ + ξ₀ * c < (1 - ξ₁) / cfPhiD κ φ D₁ + ξ₁ * c := by
    have e₀ : (1 - ξ₀) / cfPhiD κ φ D₀ = (1 - ξ₀) * (1 / cfPhiD κ φ D₀) := by ring
    have e₁ : (1 - ξ₁) / cfPhiD κ φ D₁ = (1 - ξ₁) * (1 / cfPhiD κ φ D₁) := by ring
    rw [e₀, e₁]
    nlinarith
  have hFk1 : Fk K₀ < Fk K₁ := by
    have : Λ * (1 - δ + Fk K₀) < Λ * (1 - δ + Fk K₁) := by
      rw [hr₀, hr₁]
      exact mul_lt_mul_of_pos_left hcost hp
    nlinarith
  rcases hc.lt_or_eq with h | h
  · exact absurd (hFk hK₀ hK₁ h) (not_lt.2 hFk1.le)
  · rw [h] at hFk1
    exact lt_irrefl _ hFk1

/-- **Property 19.5.3, output and employment** (AKMM, p. 582): with the closed forms of the
two-period model (`e = α + ν − 1 > 0`, `0 < α < 1`), the lower `K′` lowers next period's
employment `L′` and output `Y′`. -/
theorem property_19_5_3_output {α ν z' K₀ K₁ : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν)
    (hz : 0 < z') (he : 0 < α + ν - 1) (hK₁ : 0 < K₁) (hK : K₁ < K₀) :
    tpL α ν 1 z' K₁ < tpL α ν 1 z' K₀ ∧ tpY α ν z' K₁ < tpY α ν z' K₀ :=
  ⟨tp_L_strictMono_K hα0 hα hν one_pos hz he hK₁ (hK₁.trans hK) hK,
    tp_Y_strictMono_K hα0 hα hν hz he hK₁ (hK₁.trans hK) hK⟩

/-- **Property 19.5.3 in general equilibrium with `κ = 0`** (AKMM, pp. 581–582). With `κ = 0`,
(19.15)–(19.16) give `µ = τ/(1 + τ)`, and with the resource constraint
`C − L^ν = W − pK′` (`W = F + p(1 − δ)K − L^ν`), (19.11) reads
`(1 − µξ)p = β(W − pK′)(1 − δ + F_k(K′))/g(K′)`. If `τ > 0`, `F_k` is strictly decreasing,
`g` increasing and positive, `1 − δ + F_k > 0` and `W − pK′ > 0`, then `ξ₁ < ξ₀` gives
`K₁ < K₀`. -/
theorem property_19_5_3_ge {Fk g : ℝ → ℝ} (hFk : StrictAntiOn Fk (Ioi 0))
    (hg : MonotoneOn g (Ioi 0)) {β W p δ τ R ξ₀ ξ₁ K₀ K₁ μ₀ μ₁ C₀ C₁ : ℝ} (hβ : 0 < β)
    (hp : 0 < p) (hτ : 0 < τ) (hR : 0 < R) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hg₀ : 0 < g K₀) (hret₁ : 0 < 1 - δ + Fk K₁)
    (hW₀ : 0 < W - p * K₀) (hW₁ : 0 < W - p * K₁) (hξ : ξ₁ < ξ₀)
    (h11₀ : (1 - μ₀ * ξ₀) * p = β * (C₀ / g K₀) * (1 - δ + Fk K₀) * (1 + 2 * 0 * (0 : ℝ)))
    (h15₀ : (1 - μ₀) * (1 + τ) / R = β * (C₀ / g K₀) * (1 + 2 * 0 * (0 : ℝ)))
    (h16₀ : 1 / R = β * (C₀ / g K₀)) (hC₀ : C₀ = W - p * K₀)
    (h11₁ : (1 - μ₁ * ξ₁) * p = β * (C₁ / g K₁) * (1 - δ + Fk K₁) * (1 + 2 * 0 * (0 : ℝ)))
    (h15₁ : (1 - μ₁) * (1 + τ) / R = β * (C₁ / g K₁) * (1 + 2 * 0 * (0 : ℝ)))
    (h16₁ : 1 / R = β * (C₁ / g K₁)) (hC₁ : C₁ = W - p * K₁) : K₁ < K₀ := by
  -- `µ = τ/(1 + τ)` at both
  have hμ : ∀ μ : ℝ, (1 - μ) * (1 + τ) / R = 1 / R → μ = τ / (1 + τ) := by
    intro μ h
    have h1 : (1 + τ) ≠ 0 := by linarith
    field_simp at h ⊢
    linarith
  have hμ₀ := hμ μ₀ (by rw [h15₀, h16₀]; ring)
  have hμ₁ := hμ μ₁ (by rw [h15₁, h16₁]; ring)
  have hμpos : 0 < τ / (1 + τ) := div_pos hτ (by linarith)
  have hlhs : (1 - μ₀ * ξ₀) * p < (1 - μ₁ * ξ₁) * p := by
    rw [hμ₀, hμ₁]
    exact mul_lt_mul_of_pos_right (by nlinarith) hp
  by_contra hc
  push Not at hc
  have hgle : g K₀ ≤ g K₁ := hg hK₀ hK₁ hc
  have hg₁ : 0 < g K₁ := lt_of_lt_of_le hg₀ hgle
  have hFle : Fk K₁ ≤ Fk K₀ := by
    rcases hc.lt_or_eq with h | h
    · exact (hFk hK₀ hK₁ h).le
    · rw [h]
  have hH : β * (C₁ / g K₁) * (1 - δ + Fk K₁) ≤ β * (C₀ / g K₀) * (1 - δ + Fk K₀) := by
    rw [hC₀, hC₁]
    have h1 : (W - p * K₁) / g K₁ ≤ (W - p * K₀) / g K₀ :=
      div_le_div₀ hW₀.le (by nlinarith) hg₀ hgle
    have h2 : 0 ≤ (W - p * K₁) / g K₁ := (div_pos hW₁ hg₁).le
    have h3 := mul_le_mul h1 (by linarith : 1 - δ + Fk K₁ ≤ 1 - δ + Fk K₀) hret₁.le
      (div_pos hW₀ hg₀).le
    nlinarith
  simp only [mul_zero, add_zero, mul_one] at h11₀ h11₁
  linarith

/-- **Property 19.5.1, binding limit** (AKMM, p. 579): "The response of investment to the
productivity shock is positive." At given prices, let `(K₀, D₀, µ₀)` and `(K₁, D₁, µ₁)` solve
(19.11), (19.15) and the budget with the binding limit for `(z₀′, F₀)` and `(z₁′, F₁)`, with
`z₀′ < z₁′`, current profits not falling (`αF₀ ≤ αF₁`), `ξ ≤ 1`, `κ ≥ 0`, `ϕ′ > 0`, and `F_k`
strictly increasing in `z′` and strictly decreasing in `K′`. Then `K₀ < K₁`. -/
theorem property_19_5_1 {Fk : ℝ → ℝ → ℝ} (hz : ∀ K, 0 < K → StrictMonoOn (Fk · K) (Ioi 0))
    (hK : ∀ z, 0 < z → StrictAntiOn (Fk z) (Ioi 0))
    {Λ R τ p δ α F₀ F₁ B K κ φ ξ z₀ z₁ K₀ K₁ D₀ D₁ μ₀ μ₁ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hp : 0 < p) (hR : 0 < R) (hτ : 0 < 1 + τ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hz₀ : 0 < z₀) (hz01 : z₀ < z₁) (hF : α * F₀ ≤ α * F₁) (hξ1 : ξ ≤ 1)
    (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - μ₀ * ξ) * p = Λ * (1 - δ + Fk z₀ K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - μ₀) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h13₀ : α * F₀ + ξ * p * K₀ = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (h11₁ : (1 - μ₁ * ξ) * p = Λ * (1 - δ + Fk z₁ K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (h13₁ : α * F₁ + ξ * p * K₁ = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁) : K₀ < K₁ := by
  by_contra hc
  push Not at hc
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  -- dividends do not fall
  have hD : D₀ ≤ D₁ := by
    by_contra hD
    push Not at hD
    have e := div_phi_sub κ φ D₀ D₁
    have : (D₁ - D₀) * (cfPhiD κ φ D₀ + cfPhiD κ φ D₁) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have h0 : 0 ≤ (1 - ξ) * p * (K₀ - K₁) :=
      mul_nonneg (mul_nonneg (by linarith) hp.le) (by linarith)
    have : cfPhi κ φ D₁ - cfPhi κ φ D₀ = α * F₁ - α * F₀ + (1 - ξ) * p * (K₀ - K₁) := by
      linear_combination h13₀ - h13₁
    linarith
  have hqq : cfPhiD κ φ D₀ ≤ cfPhiD κ φ D₁ := div_phiD_le hκ hD
  have hinv : 1 / cfPhiD κ φ D₁ ≤ 1 / cfPhiD κ φ D₀ := one_div_le_one_div_of_le hq₀ hqq
  have hcost : (1 - ξ) / cfPhiD κ φ D₁ ≤ (1 - ξ) / cfPhiD κ φ D₀ := by
    have e₀ : (1 - ξ) / cfPhiD κ φ D₀ = (1 - ξ) * (1 / cfPhiD κ φ D₀) := by ring
    have e₁ : (1 - ξ) / cfPhiD κ φ D₁ = (1 - ξ) * (1 / cfPhiD κ φ D₁) := by ring
    rw [e₀, e₁]
    exact mul_le_mul_of_nonneg_left hinv (by linarith)
  have hle : Fk z₁ K₁ ≤ Fk z₀ K₀ := by
    have : Λ * (1 - δ + Fk z₁ K₁) ≤ Λ * (1 - δ + Fk z₀ K₀) := by
      rw [hr₀, hr₁]
      exact mul_le_mul_of_nonneg_left (by linarith) hp.le
    nlinarith
  have hz₁ : 0 < z₁ := hz₀.trans hz01
  have h1 : Fk z₁ K₀ ≤ Fk z₁ K₁ := by
    rcases hc.lt_or_eq with h | h
    · exact (hK z₁ hz₁ hK₁ hK₀ h).le
    · rw [h]
  have h2 : Fk z₀ K₀ < Fk z₁ K₀ := hz K₀ hK₀ hz₀ hz₁ hz01
  linarith

/-- **Property 19.5.1, slack limit** (AKMM, p. 579): with `µ = 0`, (19.15) pins `ϕ′(D)` and
(19.11) pins `F_k(z′, K′)`, so a rise in `z′` raises `K′`. -/
theorem property_19_5_1_slack {Fk : ℝ → ℝ → ℝ} (hz : ∀ K, 0 < K → StrictMonoOn (Fk · K) (Ioi 0))
    (hK : ∀ z, 0 < z → StrictAntiOn (Fk z) (Ioi 0))
    {Λ R τ p δ κ φ z₀ z₁ K₀ K₁ D₀ D₁ : ℝ} (hΛ : 0 < Λ) (hR : 0 < R) (hτ : 0 < 1 + τ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hz₀ : 0 < z₀) (hz01 : z₀ < z₁)
    (h11₀ : (1 - 0 * 0) * p = Λ * (1 - δ + Fk z₀ K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h11₁ : (1 - 0 * 0) * p = Λ * (1 - δ + Fk z₁ K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ D₁) : K₀ < K₁ := by
  have hq : cfPhiD κ φ D₀ = cfPhiD κ φ D₁ := by
    have := h15₀.symm.trans h15₁
    exact mul_left_cancel₀ hΛ.ne' this
  have hqpos : 0 < cfPhiD κ φ D₀ := by
    have : 0 < (1 - 0) * (1 + τ) / R := by simp only [sub_zero, one_mul]; exact div_pos hτ hR
    rw [h15₀] at this
    exact pos_of_mul_pos_right this hΛ.le
  have heq : Fk z₀ K₀ = Fk z₁ K₁ := by
    rw [← hq] at h11₁
    have := h11₀.symm.trans h11₁
    have := mul_right_cancel₀ hqpos.ne' this
    have := mul_left_cancel₀ hΛ.ne' this
    linarith
  by_contra hc
  push Not at hc
  have hz₁ : 0 < z₁ := hz₀.trans hz01
  have h1 : Fk z₁ K₀ ≤ Fk z₁ K₁ := by
    rcases hc.lt_or_eq with h | h
    · exact (hK z₁ hz₁ hK₁ hK₀ h).le
    · rw [h]
  have h2 : Fk z₀ K₀ < Fk z₁ K₀ := hz K₀ hK₀ hz₀ hz₁ hz01
  linarith

/-- AKMM, p. 579: "in order for the firm to fund the higher investment, it has to reduce
dividends": with the binding limit, unchanged current profits and `ξ < 1`, a rise in `K′`
lowers `D` (`ϕ′ > 0`). -/
theorem cs_div_falls {p δ α F B K κ φ ξ K₀ K₁ D₀ D₁ : ℝ} (hp : 0 < p) (hξ : ξ < 1)
    (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁) (hK : K₀ < K₁)
    (h13₀ : α * F + ξ * p * K₀ = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (h13₁ : α * F + ξ * p * K₁ = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁) : D₁ < D₀ := by
  refine div_lt_of_phi_lt hq₀ hq₁ ?_
  have : 0 < (1 - ξ) * p * (K₁ - K₀) := by
    have := mul_pos (sub_pos.2 hξ) hp
    exact mul_pos this (by linarith)
  nlinarith

/-- Comparing proportional responses: if `z₀^a K₀^b < z₁^a K₁^b` and
`z₀^a S₀^b = z₁^a S₁^b` with `b < 0` and all variables positive, then `K₁/K₀ < S₁/S₀`. -/
theorem cs_ratio_lt {a b z₀ z₁ K₀ K₁ S₀ S₁ : ℝ} (hb : b < 0) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hS₀ : 0 < S₀) (hS₁ : 0 < S₁)
    (h1 : z₀ ^ a * K₀ ^ b < z₁ ^ a * K₁ ^ b) (h2 : z₀ ^ a * S₀ ^ b = z₁ ^ a * S₁ ^ b) :
    K₁ / K₀ < S₁ / S₀ := by
  have ha₀ := Real.rpow_pos_of_pos hz₀ a
  have ha₁ := Real.rpow_pos_of_pos hz₁ a
  have hk₀ := Real.rpow_pos_of_pos hK₀ b
  have hk₁ := Real.rpow_pos_of_pos hK₁ b
  have hs₀ := Real.rpow_pos_of_pos hS₀ b
  have hs₁ := Real.rpow_pos_of_pos hS₁ b
  -- `S₁^b K₀^b < K₁^b S₀^b`
  have key : S₁ ^ b * K₀ ^ b < K₁ ^ b * S₀ ^ b := by
    have e : z₀ ^ a * K₀ ^ b * S₀ ^ b < z₁ ^ a * K₁ ^ b * S₀ ^ b :=
      mul_lt_mul_of_pos_right h1 hs₀
    have e2 : z₀ ^ a * K₀ ^ b * S₀ ^ b = z₁ ^ a * S₁ ^ b * K₀ ^ b := by
      rw [mul_right_comm, h2]
    rw [e2] at e
    have : z₁ ^ a * (S₁ ^ b * K₀ ^ b) < z₁ ^ a * (K₁ ^ b * S₀ ^ b) := by
      calc z₁ ^ a * (S₁ ^ b * K₀ ^ b) = z₁ ^ a * S₁ ^ b * K₀ ^ b := by ring
        _ < z₁ ^ a * K₁ ^ b * S₀ ^ b := e
        _ = z₁ ^ a * (K₁ ^ b * S₀ ^ b) := by ring
    exact lt_of_mul_lt_mul_left this ha₁.le
  by_contra hc
  push Not at hc
  have hlt := (Real.rpow_le_rpow_of_nonpos (div_pos hS₁ hS₀) hc hb.le)
  rw [Real.div_rpow hK₁.le hK₀.le, Real.div_rpow hS₁.le hS₀.le, div_le_div_iff₀ hk₀ hs₀] at hlt
  linarith

/-- **Property 19.5.1, dampening** (AKMM, p. 579): "the responses of investment and output will
be smaller if the borrowing constraint is binding". With the closed-form `F_k` (`0 < α < 1`,
`ν > 1`) and fixed prices, compare a rise `z₀′ < z₁′`
* with a binding limit, solutions `(K₀, D₀)`, `(K₁, D₁)` of (19.11), (19.15) (the budget enters
  only through `D₁ < D₀`, which `cs_div_falls` provides when current profits are unchanged),
  `κ > 0`, `ξ < 1`;
* with a slack limit, solutions `S₀, S₁` of (19.11), (19.15) with `µ = 0`.
Then the proportional response of `K′` is strictly smaller with the binding limit:
`K₁/K₀ < S₁/S₀`. -/
theorem property_19_5_1_dampening {α ν Λ R τ p δ κ φ ξ z₀ z₁ K₀ K₁ S₀ S₁ D₀ D₁ E₀ E₁ μ₀ μ₁ : ℝ}
    (hα0 : 0 < α) (hα : α < 1) (hν : 1 < ν) (hκ : 0 < κ) (hΛ : 0 < Λ) (hp : 0 < p)
    (hR : 0 < R) (hτ : 0 < 1 + τ) (hξ : ξ < 1) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hS₀ : 0 < S₀) (hS₁ : 0 < S₁) (hD : D₁ < D₀)
    (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - μ₀ * ξ) * p = Λ * (1 - δ + tpFk α ν z₀ K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - μ₀) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h11₁ : (1 - μ₁ * ξ) * p = Λ * (1 - δ + tpFk α ν z₁ K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (s11₀ : (1 - 0 * ξ) * p = Λ * (1 - δ + tpFk α ν z₀ S₀) * cfPhiD κ φ E₀)
    (s15₀ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ E₀)
    (s11₁ : (1 - 0 * ξ) * p = Λ * (1 - δ + tpFk α ν z₁ S₁) * cfPhiD κ φ E₁)
    (s15₁ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ E₁) : K₁ / K₀ < S₁ / S₀ := by
  -- binding: the marginal product rises
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  have hqq : cfPhiD κ φ D₁ < cfPhiD κ φ D₀ := by
    have e := div_phiD_sub κ φ D₀ D₁
    have : 0 < κ * (D₀ - D₁) := mul_pos hκ (by linarith)
    linarith
  have hinv : 1 / cfPhiD κ φ D₀ < 1 / cfPhiD κ φ D₁ := one_div_lt_one_div_of_lt hq₁ hqq
  have hbind : tpFk α ν z₀ K₀ < tpFk α ν z₁ K₁ := by
    have : Λ * (1 - δ + tpFk α ν z₀ K₀) < Λ * (1 - δ + tpFk α ν z₁ K₁) := by
      rw [hr₀, hr₁]
      refine mul_lt_mul_of_pos_left ?_ hp
      have e₀ : (1 - ξ) / cfPhiD κ φ D₀ = (1 - ξ) * (1 / cfPhiD κ φ D₀) := by ring
      have e₁ : (1 - ξ) / cfPhiD κ φ D₁ = (1 - ξ) * (1 / cfPhiD κ φ D₁) := by ring
      rw [e₀, e₁]
      have := mul_lt_mul_of_pos_left hinv (sub_pos.2 hξ)
      linarith
    have := lt_of_mul_lt_mul_left this hΛ.le
    linarith
  -- slack: the marginal product is unchanged
  have hslack : tpFk α ν z₀ S₀ = tpFk α ν z₁ S₁ := by
    have hq : cfPhiD κ φ E₀ = cfPhiD κ φ E₁ := mul_left_cancel₀ hΛ.ne' (s15₀.symm.trans s15₁)
    have hqpos : 0 < cfPhiD κ φ E₀ := by
      have : 0 < (1 - 0) * (1 + τ) / R := by simp only [sub_zero, one_mul]; exact div_pos hτ hR
      rw [s15₀] at this
      exact pos_of_mul_pos_right this hΛ.le
    rw [← hq] at s11₁
    have := mul_right_cancel₀ hqpos.ne' (s11₀.symm.trans s11₁)
    have := mul_left_cancel₀ hΛ.ne' this
    linarith
  -- compare through the closed form
  have he : 0 < α + ν - 1 := by linarith
  set cK := α * ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) with hcK
  have hc : 0 < cK :=
    mul_pos hα0 (Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _)
  have hb : ν * α / (α + ν - 1) - 1 < 0 := by
    rw [sub_neg, div_lt_one he]
    nlinarith
  have hform : ∀ z K, tpFk α ν z K =
      cK * (z ^ (ν / (α + ν - 1)) * K ^ (ν * α / (α + ν - 1) - 1)) := by
    intro z K
    simp only [tpFk, hcK]
    ring
  rw [hform, hform] at hbind hslack
  exact cs_ratio_lt hb hz₀ hz₁ hK₀ hK₁ hS₀ hS₁ (lt_of_mul_lt_mul_left hbind hc.le)
    (mul_left_cancel₀ hc.ne' hslack)

/-- **Property 19.5.5** (AKMM, p. 583). At fixed prices with `κ > 0`, let `(K₀, D₀, B₀)` be a
solution with a slack limit at `ξ₀` (`µ₀ = 0`: (19.11), (19.15) and the budget
`αF + B′/R̃ = B + p[K′ − (1 − δ)K] + ϕ(D)`), and let `ξ₁ < 1` fall so far that the old plan
violates the limit, `ξ₁pK₀ < B₀/R̃`. Let `(K₁, D₁, B₁, µ₁)` satisfy the Kuhn–Tucker conditions
at `ξ₁`: (19.11), (19.15), the budget, `B₁/R̃ ≤ ξ₁pK₁`, `µ₁ ≥ 0`, `µ₁(ξ₁pK₁ − B₁/R̃) = 0`. Then
the limit binds and `K₁ < K₀`: "a sufficiently large decrease in `ξ` reduces investment". -/
theorem property_19_5_5 {Fk : ℝ → ℝ} (hFk : StrictAntiOn Fk (Ioi 0))
    {Λ R τ p δ α F B K κ φ Rt ξ₀ ξ₁ K₀ K₁ D₀ D₁ B₀ B₁ μ₁ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ)
    (hp : 0 < p) (hR : 0 < R) (hτ : 0 < 1 + τ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hξ1 : ξ₁ < 1) (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - 0 * ξ₀) * p = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h13₀ : α * F + B₀ / Rt = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (hbig : ξ₁ * p * K₀ < B₀ / Rt)
    (h11₁ : (1 - μ₁ * ξ₁) * p = Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (h13₁ : α * F + B₁ / Rt = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁)
    (hlim₁ : B₁ / Rt ≤ ξ₁ * p * K₁) (hμ₁ : 0 ≤ μ₁) (hcs₁ : μ₁ * (ξ₁ * p * K₁ - B₁ / Rt) = 0) :
    0 < μ₁ ∧ B₁ / Rt = ξ₁ * p * K₁ ∧ K₁ < K₀ := by
  set c := R * Λ / (1 + τ) with hcdef
  have hm₀ := cs_mu hτ hR h15₀
  have hm₁ := cs_mu hτ hR h15₁
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  -- the limit binds
  have hpos : 0 < μ₁ := by
    rcases hμ₁.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hm₁
      have hq : cfPhiD κ φ D₁ = cfPhiD κ φ D₀ := by
        have hc0 : c ≠ 0 := by rw [hcdef]; exact (div_pos (mul_pos hR hΛ) hτ).ne'
        have : c * cfPhiD κ φ D₁ = c * cfPhiD κ φ D₀ := by linarith
        exact mul_left_cancel₀ hc0 this
      have hDeq : D₁ = D₀ := by
        have := div_phiD_sub κ φ D₀ D₁
        rw [hq, sub_self] at this
        have : κ * (D₁ - D₀) = 0 := by linarith
        rcases mul_eq_zero.1 this with h1 | h1
        · exact absurd h1 hκ.ne'
        · linarith
      have hFeq : Fk K₁ = Fk K₀ := by
        have e1 : Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₀ = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀ :=
          calc Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₀ = Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₁ := by
                rw [hq]
            _ = (1 - μ₁ * ξ₁) * p := h11₁.symm
            _ = (1 - 0 * ξ₀) * p := by rw [← h]; ring
            _ = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀ := h11₀
        have := mul_left_cancel₀ hΛ.ne' (mul_right_cancel₀ hq₀.ne' e1)
        linarith
      have hKeq : K₁ = K₀ := hFk.injOn hK₁ hK₀ hFeq
      have hBeq : B₁ / Rt = B₀ / Rt := by rw [hKeq, hDeq] at h13₁; linarith
      rw [hBeq, hKeq] at hlim₁
      linarith
  have hbind : B₁ / Rt = ξ₁ * p * K₁ := by
    rcases mul_eq_zero.1 hcs₁ with h | h
    · exact absurd h hpos.ne'
    · linarith
  refine ⟨hpos, hbind, ?_⟩
  -- the effective cost rises above `c`
  have hc1 : c < 1 / cfPhiD κ φ D₁ := by
    rw [lt_div_iff₀ hq₁]
    linarith
  have hc0 : 1 / cfPhiD κ φ D₀ = c := by
    rw [div_eq_iff hq₀.ne']
    linarith
  have hFk1 : Fk K₀ < Fk K₁ := by
    have : Λ * (1 - δ + Fk K₀) < Λ * (1 - δ + Fk K₁) := by
      rw [hr₀, hr₁]
      have e₀ : (1 - ξ₀) / cfPhiD κ φ D₀ = (1 - ξ₀) * (1 / cfPhiD κ φ D₀) := by ring
      have e₁ : (1 - ξ₁) / cfPhiD κ φ D₁ = (1 - ξ₁) * (1 / cfPhiD κ φ D₁) := by ring
      rw [e₀, e₁, hc0]
      have := mul_lt_mul_of_pos_left hc1 (sub_pos.2 hξ1)
      nlinarith
    nlinarith
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with h | h
  · exact absurd (hFk hK₀ hK₁ h) (not_lt.2 hFk1.le)
  · rw [h] at hFk1
    exact lt_irrefl _ hFk1

/-- **Property 19.5.5, output and employment** (AKMM, p. 583): the lower `K′` reduces future
output and employment (closed forms, `e > 0`, `0 < α < 1`). -/
theorem property_19_5_5_output {α ν z' K₀ K₁ : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν)
    (hz : 0 < z') (he : 0 < α + ν - 1) (hK₁ : 0 < K₁) (hK : K₁ < K₀) :
    tpL α ν 1 z' K₁ < tpL α ν 1 z' K₀ ∧ tpY α ν z' K₁ < tpY α ν z' K₀ :=
  property_19_5_3_output hα0 hα hν hz he hK₁ hK

end AKMM.CreditFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The general model and the neoclassical growth model

AKMM, §19.6, (19.19)–(19.22), Proposition 19.1 and the box "More intuition for
Modigliani–Miller principle", pp. 585–587.

* **(19.19)–(19.22)**: (19.4) and (19.8) give `F₃ = −u₂/u₁` (`eq_19_19`); (19.5) with
  `m′ = βu₁′/u₁` is (19.20) (`eq_19_20`); (19.6) with `R̃ = R/(1 + τ)` is (19.21)
  (`eq_19_21`); (19.22) is the household's (19.9) (`eq_19_22`).
* **`κ = 0`** (p. 586): (19.21) and (19.22) give `(1 − µ)(1 + τ) = 1`, so `µ = τ/(1 + τ)` and
  `µ > 0` iff `τ > 0` (`gm_kappa_zero`, `gm_binding_iff`).
* **`κ > 0`** (p. 586): `µ > 0` iff `E[m′ϕ′(D)/ϕ′(D′)] < (1 + τ)E[m′]`, so if the
  `m′`-weighted mean of `ϕ′(D)/ϕ′(D′)` is at least `1 + τ`, (19.21) cannot hold with `µ > 0`
  (`gm_mu_pos_iff`, `gm_not_binding`). Scaling `m′` (a higher level of `u₁′/u₁`) with `R`
  adjusting through (19.22) leaves `µ` unchanged (`gm_mu_scale`); without uncertainty
  `µ = 1 − ϕ′(D)/((1 + τ)ϕ′(D′))` (`gm_mu_det`).
* **Proposition 19.1** (p. 586): with `τ = κ = 0` and `p ≡ 1`, a deterministic equilibrium of the
  economy with financial frictions has `µ ≡ 0` and its allocation satisfies the household,
  firm and market-clearing conditions of the neoclassical growth model as formalised in Miao
  Ch. 14 (`Miao.NeoclassicalGrowth.RMHHFOC`, `RMFirmFOC`, `RMClear`) (`proposition_19_1`),
  hence the planner's conditions (`proposition_19_1_planner`, via `rm_ce_planner`); debt is
  indeterminate: every debt path satisfying the limit, with dividends from the firm's budget,
  gives an equilibrium with the same allocation (`proposition_19_1_debt`), and there are
  distinct ones (`proposition_19_1_indeterminate`).
* **The box on p. 587**: when `τ = κ = 0`, (19.6) is `E[m′R] = 1`, so the gain
  `∆(1 − E[m′R])` from changing the financing is zero (`gm_box`).

Departure: Proposition 19.1 is proved for the deterministic model, by comparing the first-order
and market-clearing conditions as the book's proof does; transversality conditions are not
compared.
-/

namespace AKMM.CreditFrictions

open Miao.NeoclassicalGrowth

/-- **(19.19)** (AKMM, p. 585): (19.4) `F₃ = w` and (19.8) `u₁w = −u₂` with `u₁ ≠ 0` give
`F₃(z, K, L) = −u₂(C, L)/u₁(C, L)`. -/
theorem eq_19_19 {F3 w u1 u2 : ℝ} (hu1 : u1 ≠ 0) (h194 : F3 = w) (h198 : u1 * w = -u2) :
    F3 = -u2 / u1 := by
  rw [h194, eq_div_iff hu1]
  linarith

variable {S : Type*} [Fintype S]

/-- **(19.20)** (AKMM, p. 585): (19.5) with the stochastic discount factor
`m′ₛ = βu₁(C′ₛ, L′ₛ)/u₁(C, L)`. -/
theorem eq_19_20 (pr u1' q' p' F2 : S → ℝ) {β u1 q μ ξ p δ : ℝ}
    (h195 : ∑ s, pr s * (β * u1' s / u1 * (q / q' s * ((1 - δ) * p' s + F2 s))) =
      (1 - μ * ξ) * p) :
    (1 - μ * ξ) * p = ∑ s, pr s * (β * (u1' s / u1) * (q / q' s) * ((1 - δ) * p' s + F2 s)) := by
  rw [← h195]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **(19.21)** (AKMM, p. 586): (19.6) `E[m′ϕ′(D)/ϕ′(D′)]R̃ = 1 − µ` with `R̃ = R/(1 + τ)` is
`(1 − µ)(1 + τ)/R = E[β(u₁′/u₁)ϕ′(D)/ϕ′(D′)]`. -/
theorem eq_19_21 (pr m r : S → ℝ) {μ R τ : ℝ} (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (h196 : (∑ s, pr s * (m s * r s)) * (R / (1 + τ)) = 1 - μ) :
    (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s) := by
  rw [← h196]
  field_simp

/-- **(19.22)** (AKMM, p. 586): the household's bond condition, (19.9) (printed as "(19.6)"),
`1/R = E[βu₁(C′, L′)/u₁(C, L)]`. -/
theorem eq_19_22 (pr u1' : S → ℝ) {β u1 R : ℝ}
    (h199 : 1 / R = ∑ s, pr s * (β * u1' s / u1)) :
    1 / R = ∑ s, pr s * (β * (u1' s / u1)) := by
  rw [h199]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- AKMM, p. 586: "If we relax Assumption 19.4.3 by imposing `κ = 0` …, conditions (19.21) and
(19.22) imply `(1 − µ)(1 + τ) = 1`": with `ϕ′ ≡ 1`, `µ = τ/(1 + τ)`. -/
theorem gm_kappa_zero (pr m : S → ℝ) {μ R τ : ℝ} (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * 1))
    (h1922 : 1 / R = ∑ s, pr s * m s) :
    (1 - μ) * (1 + τ) = 1 ∧ μ = τ / (1 + τ) := by
  have e : ∑ s, pr s * (m s * 1) = ∑ s, pr s * m s := by simp
  rw [e, ← h1922] at h1921
  have h1 : (1 - μ) * (1 + τ) = 1 := by
    field_simp at h1921
    linarith
  refine ⟨h1, ?_⟩
  field_simp
  linarith

/-- AKMM, p. 586: "a sufficient condition to have a binding borrowing constraint (so that
`µ > 0`) is that `τ > 0`": with `κ = 0` and `1 + τ > 0`, `µ > 0` iff `τ > 0`. -/
theorem gm_binding_iff (pr m : S → ℝ) {μ R τ : ℝ} (hR : R ≠ 0) (hτ : 0 < 1 + τ)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * 1))
    (h1922 : 1 / R = ∑ s, pr s * m s) : 0 < μ ↔ 0 < τ := by
  rw [(gm_kappa_zero pr m hR hτ.ne' h1921 h1922).2, div_pos_iff_of_pos_right hτ]

/-- AKMM, p. 586: with `κ > 0`, (19.21) and (19.22) give
`(1 − µ)(1 + τ)E[m′] = E[m′ϕ′(D)/ϕ′(D′)]`, so (with `E[m′] = 1/R > 0`) `µ > 0` iff
`E[m′ϕ′(D)/ϕ′(D′)] < (1 + τ)E[m′]`. -/
theorem gm_mu_pos_iff (pr m r : S → ℝ) {μ R τ : ℝ} (hR : 0 < R) (hτ : 0 < 1 + τ)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s))
    (h1922 : 1 / R = ∑ s, pr s * m s) :
    0 < μ ↔ ∑ s, pr s * (m s * r s) < (1 + τ) * ∑ s, pr s * m s := by
  rw [← h1921, ← h1922]
  have : (1 - μ) * (1 + τ) / R = (1 + τ) * (1 / R) - μ * ((1 + τ) / R) := by ring
  rw [this]
  have hp : 0 < (1 + τ) / R := div_pos hτ hR
  constructor
  · intro h
    have := mul_pos h hp
    linarith
  · intro h
    have : 0 < μ * ((1 + τ) / R) := by linarith
    exact pos_of_mul_pos_left this hp.le

/-- AKMM, p. 586: "if in expectation `ϕ′(D)/ϕ′(D′)` is sufficiently larger than 1, then condition
(19.21) cannot be satisfied with `µ > 0`": precisely, if
`E[m′ϕ′(D)/ϕ′(D′)] ≥ (1 + τ)E[m′]`, then `µ ≤ 0`. -/
theorem gm_not_binding (pr m r : S → ℝ) {μ R τ : ℝ} (hR : 0 < R) (hτ : 0 < 1 + τ)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s))
    (h1922 : 1 / R = ∑ s, pr s * m s)
    (hbig : (1 + τ) * ∑ s, pr s * m s ≤ ∑ s, pr s * (m s * r s)) : μ ≤ 0 := by
  by_contra h
  push Not at h
  have := (gm_mu_pos_iff pr m r hR hτ h1921 h1922).1 h
  linarith

/-- AKMM, p. 586 (clarification): scaling the discount factor `m′` by `c > 0` (a higher level of
`u₁′/u₁`), with `R` adjusting through (19.22), leaves (19.21)–(19.22) satisfied with the same
`µ`: the level of `u₁′/u₁` alone does not decide whether the limit binds. -/
theorem gm_mu_scale (pr m r : S → ℝ) {μ R τ c : ℝ} (hc : 0 < c)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s))
    (h1922 : 1 / R = ∑ s, pr s * m s) :
    (1 - μ) * (1 + τ) / (R / c) = ∑ s, pr s * (c * m s * r s) ∧
      1 / (R / c) = ∑ s, pr s * (c * m s) := by
  have e1 : ∑ s, pr s * (c * m s * r s) = c * ∑ s, pr s * (m s * r s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : ∑ s, pr s * (c * m s) = c * ∑ s, pr s * m s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, e2, ← h1921, ← h1922]
  constructor <;> field_simp

/-- AKMM, p. 586: without uncertainty, (19.21)–(19.22) give `µ = 1 − ϕ′(D)/((1 + τ)ϕ′(D′))`,
independent of `u₁′/u₁`. -/
theorem gm_mu_det {μ R τ m r : ℝ} (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (h1921 : (1 - μ) * (1 + τ) / R = m * r) (h1922 : 1 / R = m) :
    μ = 1 - r / (1 + τ) := by
  rw [← h1922] at h1921
  field_simp at h1921 ⊢
  linarith

/-- **The box on p. 587** (AKMM): when `τ = κ = 0`, the firm's (19.6),
`E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ`, with `µ = 0` (from `gm_kappa_zero` at `τ = 0`) is
`E[m′R] = 1`, and the gain `∆ − E[m′∆R]` from raising `∆` by debt is zero for every `∆`. -/
theorem gm_box (pr m : S → ℝ) {μ R : ℝ} (hμ : μ = 0)
    (h196 : (∑ s, pr s * (m s * (cfPhiD 0 0 0 / cfPhiD 0 0 0))) * (R / (1 + 0)) = 1 - μ)
    (Δ : ℝ) : Δ - ∑ s, pr s * (m s * (Δ * R)) = 0 := by
  have h : ∑ s, pr s * (m s * R) = 1 := by
    have e : (∑ s, pr s * (m s * (cfPhiD 0 0 0 / cfPhiD 0 0 0))) * (R / (1 + 0)) =
        ∑ s, pr s * (m s * R) := by
      simp only [cfPhiD, mul_zero, zero_mul, add_zero, div_one, mul_one]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [← e, h196, hμ, sub_zero]
  exact (mm_box_gain_zero_iff pr m R).2 h Δ

/-! ### Proposition 19.1 -/

/-- **Proposition 19.1** (AKMM, p. 586). Consider a deterministic equilibrium of the economy with
financial frictions, `p ≡ 1`, `τ = 0`, `κ = 0`: (19.4) `F_L = w`, (19.8) `u₁w = −u₂`, (19.20),
(19.21), (19.22), the firm's budget with `R̃ = R/(1 + τ)`, the household's budget with
`A = A′ = 1` and the tax `T = B′/R̃ − B′/R`. Then the multiplier is zero, `µ ≡ 0`, and the
allocation `(C, L, K)`, with `R^k = F_K`, `w = F_L` and `I = K′ − (1 − δ)K`, satisfies the
neoclassical growth model's household conditions (14.7)–(14.8) `RMHHFOC`, the firm's
conditions (14.3) `RMFirmFOC` and market clearing (14.4) `RMClear` of Miao Ch. 14. -/
theorem proposition_19_1 {uc un F FK FN : ℝ → ℝ → ℝ} {β δ ξ τ κ φ : ℝ}
    {C L K D B R μ w T : ℕ → ℝ} (hτ : τ = 0) (hκ : κ = 0)
    (huc : ∀ t, uc (C t) (L t) ≠ 0) (hR : ∀ t, R t ≠ 0)
    (h194 : ∀ t, FN (K t) (L t) = w t)
    (h198 : ∀ t, uc (C t) (L t) * w t = -un (C t) (L t))
    (h1920 : ∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))) * ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1))))
    (h1921 : ∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))))
    (h1922 : ∀ t, 1 / R t = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)))
    (hfirm : ∀ t, F (K t) (L t) - w t * L t + B (t + 1) / (R t / (1 + τ)) =
      B t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (D t))
    (hhh : ∀ t, (D t + 1) * 1 + B t + w t * L t = C t + 1 * 1 + B (t + 1) / R t + T t)
    (hT : ∀ t, T t = B (t + 1) / (R t / (1 + τ)) - B (t + 1) / R t) :
    (∀ t, μ t = 0) ∧
    RMHHFOC uc un β δ C L (fun t => FK (K t) (L t)) w ∧
    RMFirmFOC FK FN 1 K L (fun t => FK (K t) (L t)) w ∧
    RMClear F 1 1 δ C (fun t => K (t + 1) - (1 - δ) * K t) L K C
      (fun t => K (t + 1) - (1 - δ) * K t) L K := by
  subst hτ hκ
  have hq : ∀ d, cfPhiD 0 φ d = 1 := fun d => by simp [cfPhiD]
  have hμ : ∀ t, μ t = 0 := by
    intro t
    have h := h1921 t
    rw [hq, hq, div_one, mul_one, ← h1922 t] at h
    have hR' := hR t
    field_simp at h
    linarith
  refine ⟨hμ, fun t => ⟨?_, ?_⟩, fun t => ⟨by simp, by simp [h194 t]⟩, fun t => ?_⟩
  · have h := h1920 t
    rw [hμ, hq, hq] at h
    have hu := huc t
    field_simp at h
    linarith
  · rw [← h194 t, div_eq_iff (huc t), ← h198 t, h194 t]
    ring
  · refine ⟨by simp, by simp, by simp, by simp, by ring, ?_⟩
    have := hh_resource (hfirm t) (hhh t) (hT t)
    simp only [one_pow, one_mul]
    linarith

/-- **Proposition 19.1, planner** (AKMM, p. 586–587): if moreover `F` has constant returns
(so `F_K`, `F_L` are homogeneous of degree zero) and `K, L > 0`, the allocation satisfies the
planner's first-order conditions of the neoclassical growth model (Miao, p. 465,
`rm_ce_planner`). -/
theorem proposition_19_1_planner {uc un F FK FN : ℝ → ℝ → ℝ} {β δ ξ τ κ φ : ℝ}
    {C L K D B R μ w T : ℕ → ℝ} (hτ : τ = 0) (hκ : κ = 0)
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (hK : ∀ t, 0 < K t) (hL : ∀ t, 0 < L t)
    (huc : ∀ t, uc (C t) (L t) ≠ 0) (hR : ∀ t, R t ≠ 0)
    (h194 : ∀ t, FN (K t) (L t) = w t)
    (h198 : ∀ t, uc (C t) (L t) * w t = -un (C t) (L t))
    (h1920 : ∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))) * ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1))))
    (h1921 : ∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))))
    (h1922 : ∀ t, 1 / R t = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)))
    (hfirm : ∀ t, F (K t) (L t) - w t * L t + B (t + 1) / (R t / (1 + τ)) =
      B t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (D t))
    (hhh : ∀ t, (D t + 1) * 1 + B t + w t * L t = C t + 1 * 1 + B (t + 1) / R t + T t)
    (hT : ∀ t, T t = B (t + 1) / (R t / (1 + τ)) - B (t + 1) / R t) :
    RMPlannerFOC uc un F FK FN β 1 1 δ C (fun t => K (t + 1) - (1 - δ) * K t) L K := by
  obtain ⟨-, h1, h2, h3⟩ := proposition_19_1 hτ hκ huc hR h194 h198 h1920 h1921 h1922 hfirm hhh hT
  exact rm_ce_planner hhom hFK hFN one_pos one_pos hK hL h1 h2 h3

/-- **Proposition 19.1, debt** (AKMM, pp. 586–587): "the equilibrium debt chosen by firms is
indeterminate". With `τ = κ = 0`, take an equilibrium as in `proposition_19_1` and any other
debt path `B̂` with the same initial debt. Paying the dividends `D̂` the firm's budget then
allows, `(C, L, K, D̂, B̂, R, µ)` satisfies every equilibrium condition: (19.20) and (19.21)
do not involve dividends when `κ = 0`, the firm's budget holds by construction and the
household's budget follows from the resource constraint. -/
theorem proposition_19_1_debt {uc F FK : ℝ → ℝ → ℝ} {β δ ξ τ κ φ : ℝ}
    {C L K D B Bh R μ w T : ℕ → ℝ} (hτ : τ = 0) (hκ : κ = 0) (hR : ∀ t, R t ≠ 0)
    (h1920 : ∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))) * ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1))))
    (h1921 : ∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))))
    (hfirm : ∀ t, F (K t) (L t) - w t * L t + B (t + 1) / (R t / (1 + τ)) =
      B t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (D t))
    (hhh : ∀ t, (D t + 1) * 1 + B t + w t * L t = C t + 1 * 1 + B (t + 1) / R t + T t)
    (hT : ∀ t, T t = B (t + 1) / (R t / (1 + τ)) - B (t + 1) / R t) :
    let Dh : ℕ → ℝ := fun t => F (K t) (L t) - w t * L t + Bh (t + 1) / (R t / (1 + τ)) -
      Bh t - 1 * (K (t + 1) - (1 - δ) * K t)
    let Th : ℕ → ℝ := fun t => Bh (t + 1) / (R t / (1 + τ)) - Bh (t + 1) / R t
    (∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (Dh t) / cfPhiD κ φ (Dh (t + 1))) *
        ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1)))) ∧
    (∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (Dh t) / cfPhiD κ φ (Dh (t + 1)))) ∧
    (∀ t, F (K t) (L t) - w t * L t + Bh (t + 1) / (R t / (1 + τ)) =
      Bh t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (Dh t)) ∧
    (∀ t, (Dh t + 1) * 1 + Bh t + w t * L t = C t + 1 * 1 + Bh (t + 1) / R t + Th t) := by
  intro Dh Th
  subst hτ hκ
  have hq : ∀ d, cfPhiD 0 φ d = 1 := fun d => by simp [cfPhiD]
  have hphi : ∀ d, cfPhi 0 φ d = d := fun d => by simp [cfPhi]
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · have e : cfPhiD 0 φ (Dh t) / cfPhiD 0 φ (Dh (t + 1)) =
        cfPhiD 0 φ (D t) / cfPhiD 0 φ (D (t + 1)) := by rw [hq, hq, hq, hq]
    rw [e]
    exact h1920 t
  · have e : cfPhiD 0 φ (Dh t) / cfPhiD 0 φ (Dh (t + 1)) =
        cfPhiD 0 φ (D t) / cfPhiD 0 φ (D (t + 1)) := by rw [hq, hq, hq, hq]
    rw [e]
    exact h1921 t
  · rw [hphi]
    simp only [Dh]
    ring
  · have hres := hh_resource (hfirm t) (hhh t) (hT t)
    have hR' := hR t
    simp only [Dh, Th, add_zero, div_one]
    simp only [add_zero, zero_mul] at hres
    linarith

/-- **Proposition 19.1, indeterminacy** (AKMM, p. 586): with `τ = κ = 0`, `R > 0` and an
equilibrium debt path `B` satisfying the limit `B(t + 1)/R̃ ≤ ξK(t + 1)`, the path that lowers
debt by one unit from date 1 on also satisfies the limit, has the same initial debt, and
differs from `B`: debt is not determined by the equilibrium conditions. -/
theorem proposition_19_1_indeterminate {ξ τ : ℝ} {K B R : ℕ → ℝ} (hτ : τ = 0)
    (hR : ∀ t, 0 < R t) (hlim : ∀ t, B (t + 1) / (R t / (1 + τ)) ≤ ξ * 1 * K (t + 1)) :
    ∃ Bh : ℕ → ℝ, Bh 0 = B 0 ∧ Bh ≠ B ∧
      ∀ t, Bh (t + 1) / (R t / (1 + τ)) ≤ ξ * 1 * K (t + 1) := by
  subst hτ
  refine ⟨fun t => if t = 0 then B 0 else B t - 1, by simp, fun h => ?_, fun t => ?_⟩
  · have := congrFun h 1
    simp at this
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, add_zero, div_one]
    have := hlim t
    simp only [add_zero, div_one] at this
    have hr := hR t
    have : (B (t + 1) - 1) / R t ≤ B (t + 1) / R t :=
      div_le_div_of_nonneg_right (by linarith) hr.le
    linarith

end AKMM.CreditFrictions

set_option linter.style.longLine false
#print axioms AKMM.CreditFrictions.mmObj
#print axioms AKMM.CreditFrictions.mmObjDebt
#print axioms AKMM.CreditFrictions.mm_obj_diff
#print axioms AKMM.CreditFrictions.eq_19_2
#print axioms AKMM.CreditFrictions.mm_isMax_iff
#print axioms AKMM.CreditFrictions.mm_indeterminate
#print axioms AKMM.CreditFrictions.mm_no_max
#print axioms AKMM.CreditFrictions.fn6_repayment_eq
#print axioms AKMM.CreditFrictions.fn6_full_iff
#print axioms AKMM.CreditFrictions.fn6_lender_iff
#print axioms AKMM.CreditFrictions.assumption_19_4_2_of_fn6
#print axioms AKMM.CreditFrictions.mm_box_gain
#print axioms AKMM.CreditFrictions.mm_box_gain_zero_iff
#print axioms AKMM.CreditFrictions.cfPhi
#print axioms AKMM.CreditFrictions.cfPhiD
#print axioms AKMM.CreditFrictions.cfDiv
#print axioms AKMM.CreditFrictions.div_hasDerivAt_phi
#print axioms AKMM.CreditFrictions.div_phi_sub
#print axioms AKMM.CreditFrictions.div_phiD_sub
#print axioms AKMM.CreditFrictions.div_phiD_le
#print axioms AKMM.CreditFrictions.div_lt_of_phi_lt
#print axioms AKMM.CreditFrictions.div_radicand_phi
#print axioms AKMM.CreditFrictions.div_phi_div
#print axioms AKMM.CreditFrictions.div_phiD_div
#print axioms AKMM.CreditFrictions.div_div_phi
#print axioms AKMM.CreditFrictions.div_le_div_of_phi
#print axioms AKMM.CreditFrictions.div_continuous
#print axioms AKMM.CreditFrictions.div_hasDerivAt_div
#print axioms AKMM.CreditFrictions.env_firm
#print axioms AKMM.CreditFrictions.appendix_19_A_1_envelope
#print axioms AKMM.CreditFrictions.kkt_deriv_nonpos
#print axioms AKMM.CreditFrictions.kktRes
#print axioms AKMM.CreditFrictions.kkt_dir
#print axioms AKMM.CreditFrictions.kkt_clm_apply
#print axioms AKMM.CreditFrictions.kkt_firm
#print axioms AKMM.CreditFrictions.eq_19_5
#print axioms AKMM.CreditFrictions.eq_19_6
#print axioms AKMM.CreditFrictions.firm_focs
#print axioms AKMM.CreditFrictions.hh_envelope
#print axioms AKMM.CreditFrictions.hh_dir
#print axioms AKMM.CreditFrictions.appendix_19_A_2_focs
#print axioms AKMM.CreditFrictions.eq_19_8
#print axioms AKMM.CreditFrictions.eq_19_9
#print axioms AKMM.CreditFrictions.eq_19_10
#print axioms AKMM.CreditFrictions.household_focs
#print axioms AKMM.CreditFrictions.hh_tax
#print axioms AKMM.CreditFrictions.hh_R_gt_Rt_iff
#print axioms AKMM.CreditFrictions.hh_resource
#print axioms AKMM.CreditFrictions.tpL
#print axioms AKMM.CreditFrictions.tpY
#print axioms AKMM.CreditFrictions.tpFk
#print axioms AKMM.CreditFrictions.tpG
#print axioms AKMM.CreditFrictions.tp_hasDerivAt_u1
#print axioms AKMM.CreditFrictions.tp_hasDerivAt_u2
#print axioms AKMM.CreditFrictions.tp_mrs
#print axioms AKMM.CreditFrictions.tp_mpk
#print axioms AKMM.CreditFrictions.tp_mpl
#print axioms AKMM.CreditFrictions.tp_mpl_eq
#print axioms AKMM.CreditFrictions.tp_wage_bill
#print axioms AKMM.CreditFrictions.tp_L_eq
#print axioms AKMM.CreditFrictions.tp_foc_iff
#print axioms AKMM.CreditFrictions.tp_labour
#print axioms AKMM.CreditFrictions.tp_L_strictMono_z
#print axioms AKMM.CreditFrictions.tp_L_strictMono_K
#print axioms AKMM.CreditFrictions.tp_L_strictAnti_z_of_neg
#print axioms AKMM.CreditFrictions.tp_wc_labour
#print axioms AKMM.CreditFrictions.property_19_5_6
#print axioms AKMM.CreditFrictions.tp_Y_eq
#print axioms AKMM.CreditFrictions.tp_Fk_eq
#print axioms AKMM.CreditFrictions.tp_mpk_eq
#print axioms AKMM.CreditFrictions.tp_Y_strictMono_z
#print axioms AKMM.CreditFrictions.tp_Y_strictMono_K
#print axioms AKMM.CreditFrictions.tp_Y_pos
#print axioms AKMM.CreditFrictions.tp_Fk_strictMono_z
#print axioms AKMM.CreditFrictions.tp_Fk_strictAnti_K
#print axioms AKMM.CreditFrictions.tp_Fk_pos
#print axioms AKMM.CreditFrictions.tp_L_pow_nu
#print axioms AKMM.CreditFrictions.tp_g_eq
#print axioms AKMM.CreditFrictions.tp_g_strictMono_z
#print axioms AKMM.CreditFrictions.tp_g_strictMono_K
#print axioms AKMM.CreditFrictions.tp_g_pos
#print axioms AKMM.CreditFrictions.sys_terminal_C
#print axioms AKMM.CreditFrictions.system_19_11_to_19_16
#print axioms AKMM.CreditFrictions.sys_networth_elasticity
#print axioms AKMM.CreditFrictions.property_19_5_2_networth
#print axioms AKMM.CreditFrictions.sys_Kprime_eq
#print axioms AKMM.CreditFrictions.sys_hasDerivAt_Kprime
#print axioms AKMM.CreditFrictions.property_19_5_2
#print axioms AKMM.CreditFrictions.sys_multiplier_mono
#print axioms AKMM.CreditFrictions.sys_B_pos_not_sufficient
#print axioms AKMM.CreditFrictions.property_19_5_4
#print axioms AKMM.CreditFrictions.sys_slack_global
#print axioms AKMM.CreditFrictions.property_19_5_4_opt
#print axioms AKMM.CreditFrictions.eq_19_18
#print axioms AKMM.CreditFrictions.sys_wc_19_5
#print axioms AKMM.CreditFrictions.sys_wc_19_6_tilde
#print axioms AKMM.CreditFrictions.sys_wc_19_6_printed
#print axioms AKMM.CreditFrictions.sys_wc_19_6_printed_ne
#print axioms AKMM.CreditFrictions.cs_return
#print axioms AKMM.CreditFrictions.cs_mu
#print axioms AKMM.CreditFrictions.property_19_5_3
#print axioms AKMM.CreditFrictions.property_19_5_3_output
#print axioms AKMM.CreditFrictions.property_19_5_3_ge
#print axioms AKMM.CreditFrictions.property_19_5_1
#print axioms AKMM.CreditFrictions.property_19_5_1_slack
#print axioms AKMM.CreditFrictions.cs_div_falls
#print axioms AKMM.CreditFrictions.cs_ratio_lt
#print axioms AKMM.CreditFrictions.property_19_5_1_dampening
#print axioms AKMM.CreditFrictions.property_19_5_5
#print axioms AKMM.CreditFrictions.property_19_5_5_output
#print axioms AKMM.CreditFrictions.eq_19_19
#print axioms AKMM.CreditFrictions.eq_19_20
#print axioms AKMM.CreditFrictions.eq_19_21
#print axioms AKMM.CreditFrictions.eq_19_22
#print axioms AKMM.CreditFrictions.gm_kappa_zero
#print axioms AKMM.CreditFrictions.gm_binding_iff
#print axioms AKMM.CreditFrictions.gm_mu_pos_iff
#print axioms AKMM.CreditFrictions.gm_not_binding
#print axioms AKMM.CreditFrictions.gm_mu_scale
#print axioms AKMM.CreditFrictions.gm_mu_det
#print axioms AKMM.CreditFrictions.gm_box
#print axioms AKMM.CreditFrictions.proposition_19_1
#print axioms AKMM.CreditFrictions.proposition_19_1_planner
#print axioms AKMM.CreditFrictions.proposition_19_1_debt
#print axioms AKMM.CreditFrictions.proposition_19_1_indeterminate
