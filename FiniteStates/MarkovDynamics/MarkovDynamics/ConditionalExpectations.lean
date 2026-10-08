/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.MarkovChains
import Mathlib.Data.Finset.Max
import Mathlib.Order.Monotone.Basic

/-!
# Conditional expectations and monotone Markov chains

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.2.1 (pp. 91–94).

`(Ph)(x) = ∑ h(x')P(x, x')` is the conditional expectation `E[h(Xₜ₊₁) | Xₜ = x]`,
(3.12)–(3.13), and `Pᵏh` the `k`-step version (3.14). Exercise 3.2.1: constants
are fixed points of `P` and `max |Ph| ≤ max |h|`. The law of iterated
expectations (3.15) is the identity `⟨ψ₀Pᵗ, Pᵏh⟩ = ⟨ψ₀Pᵗ⁺ᵏ, h⟩`.

A Markov operator on a partially ordered `X` is monotone increasing when
`x ≤ y` implies `P(x, ·) ≼_F P(y, ·)` in the stochastic dominance order of
Vol. 1, §2.2.4. Exercise 3.2.4: this holds iff `P` maps increasing functions to
increasing functions; Exercise 3.2.5: then every `Pᵗ` is monotone increasing.
Exercise 3.2.3 (the two-state matrix) is in `DayLaborer`, Exercise 3.2.2 (the
Tauchen discretisation) in `Tauchen`.
-/

open Finset Matrix Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- (3.12), p. 92: `(Ph)(x) = ∑_{x'} h(x') P(x, x')`, the conditional expectation of `h(Xₜ₊₁)`
given `Xₜ = x`, (3.13). -/
theorem mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (x : X) :
    (P *ᵥ h) x = ∑ x', h x' * P x x' := by
  simp only [mulVec, dotProduct, mul_comm]

/-- (3.14), p. 92: `(Pᵏh)(x) = ∑_{x'} h(x') Pᵏ(x, x')`, the conditional expectation of `h(Xₜ₊ₖ)`
given `Xₜ = x`. -/
theorem pow_mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (k : ℕ) (x : X) :
    (P ^ k *ᵥ h) x = ∑ x', h x' * (P ^ k) x x' :=
  mulVec_apply_eq (P ^ k) h x

omit [DecidableEq X] in
/-- Exercise 3.2.1 (i), p. 92: every constant function is a fixed point of `P`. -/
theorem IsMarkov.isFixedPt_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    IsFixedPt (fun h => P *ᵥ h) (fun _ => c) :=
  hP.mulVec_const c

omit [DecidableEq X] in
/-- Exercise 3.2.1 (ii), p. 92: `maxₓ |Ph(x)| ≤ maxₓ |h(x)|`. -/
theorem IsMarkov.sup'_abs_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ)
    (hX : (univ : Finset X).Nonempty) :
    univ.sup' hX (fun x => |(P *ᵥ h) x|) ≤ univ.sup' hX fun x => |h x| := by
  refine Finset.sup'_le hX _ fun x _ => ?_
  rw [mulVec_apply_eq]
  calc |∑ x', h x' * P x x'| ≤ ∑ x', |h x' * P x x'| := abs_sum_le_sum_abs _ _
    _ = ∑ x', |h x'| * P x x' := sum_congr rfl fun x' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
    _ ≤ ∑ x', (univ.sup' hX fun x => |h x|) * P x x' :=
        sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
          (Finset.le_sup' (fun x => |h x|) (mem_univ x')) (hP.nonneg x x')
    _ = univ.sup' hX fun x => |h x| := by rw [← mul_sum, hP.rowsum, mul_one]

omit [DecidableEq X] in
/-- Exercise 3.2.1 (ii) in the supremum norm: `‖Ph‖ ≤ ‖h‖`. -/
theorem IsMarkov.norm_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) :
    ‖P *ᵥ h‖ ≤ ‖h‖ := by
  have := hP.norm_mulVec_sub_le h 0
  simpa using this

/-- The law of iterated expectations (3.15), p. 92: `E[E_t[h(X_{t+k})]] = E[h(X_{t+k})]`, as
`∑ₓ (Pᵏh)(x)(ψ₀Pᵗ)(x) = ⟨ψ₀Pᵗ⁺ᵏ, h⟩`. -/
theorem iterated_expectations (P : Matrix X X ℝ) (ψ₀ h : X → ℝ) (t k : ℕ) :
    ∑ x, (P ^ k *ᵥ h) x * (ψ₀ ᵥ* P ^ t) x = (ψ₀ ᵥ* P ^ (t + k)) ⬝ᵥ h := by
  have h1 : ∑ x, (P ^ k *ᵥ h) x * (ψ₀ ᵥ* P ^ t) x = (ψ₀ ᵥ* P ^ t) ⬝ᵥ (P ^ k *ᵥ h) := by
    simp only [dotProduct, mul_comm]
  rw [h1, dotProduct_mulVec, vecMul_vecMul, ← pow_add]

/-! ### Monotone Markov chains (§3.2.1.3) -/

variable [PartialOrder X]

/-- First-order stochastic dominance (Vol. 1, (2.9)): `φ ≼_F ψ` iff `∑ u φ ≤ ∑ u ψ` for every
increasing `u`. -/
def FOSD (φ ψ : X → ℝ) : Prop := ∀ u : X → ℝ, Monotone u → ∑ x, u x * φ x ≤ ∑ x, u x * ψ x

/-- A monotone increasing Markov operator (p. 93): `x ≤ y` implies `P(x, ·) ≼_F P(y, ·)`. -/
def MonotoneIncreasing (P : Matrix X X ℝ) : Prop := ∀ x y, x ≤ y → FOSD (P x) (P y)

omit [DecidableEq X] in
/-- Exercise 3.2.4 (p. 94): `P` is monotone increasing iff `P` maps increasing functions to
increasing functions, `h ∈ iℝ^X ⇒ Ph ∈ iℝ^X`. -/
theorem monotoneIncreasing_iff (P : Matrix X X ℝ) :
    MonotoneIncreasing P ↔ ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h) := by
  constructor
  · intro hP h hh x y hxy
    rw [mulVec_apply_eq, mulVec_apply_eq]
    exact hP x y hxy h hh
  · intro hP x y hxy u hu
    have := hP u hu hxy
    rwa [mulVec_apply_eq, mulVec_apply_eq] at this

/-- Exercise 3.2.5 (p. 94): if `P` is monotone increasing then so is `Pᵗ` for every `t`. -/
theorem MonotoneIncreasing.pow {P : Matrix X X ℝ} (hP : MonotoneIncreasing P)
    (t : ℕ) : MonotoneIncreasing (P ^ t) := by
  rw [monotoneIncreasing_iff] at hP ⊢
  intro h hh
  induction t with
  | zero => simpa using hh
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact hP _ ih

end SargentStachurski.MarkovDynamics
