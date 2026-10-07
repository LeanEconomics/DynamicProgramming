/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PreludeExamples.FiniteMDP

/-!
# Cash management

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.1.5 (pp. 26–28).

Cash `x ∈ X = {0, …, w̄}`; a transfer `a ∈ Γ(x) = {a ∈ ℤ : −x ≤ a ≤ w̄ − x}`; iid shocks
`ξ ∈ Ξ = {−k, …, k}` with probabilities `φ`; next cash `F(x, a, ξ) = max{0, min{w̄, x + a + ξ}}`
(1.24); transition probabilities `P(x, a, x') = ∑_ξ 𝟙{F(x, a, ξ) = x'}φ(ξ)`; flow profit
`π(x, a, ξ) = ρ(w̄ − x) − (c + τ|a|)𝟙{a ≠ 0} − p𝟙{x + a + ξ < 0}` (1.25) and reward
`r(x, a) = ∑_ξ π(x, a, ξ)φ(ξ)` (1.26). This is a finite MDP, so Theorems 1.2.1 and 1.2.2 apply:
an optimal policy exists and HPI finds one in finitely many steps.
-/

namespace SargentStachurski.PreludeExamples

/-- The parameters of the cash management problem. -/
structure CashManagement where
  /-- total wealth `w̄` -/
  wbar : ℕ
  /-- the shock bound `k` -/
  k : ℕ
  /-- the shock probabilities on `Ξ = {−k, …, k}` -/
  φ : ℤ → ℝ
  φ_nonneg : ∀ ξ, 0 ≤ φ ξ
  φ_sum : ∑ ξ ∈ Finset.Icc (-(k : ℤ)) k, φ ξ = 1
  /-- the return on securities -/
  ρ : ℝ
  /-- the fixed transaction cost -/
  c : ℝ
  /-- the proportional transaction cost -/
  τ : ℝ
  /-- the penalty for insufficient cash -/
  p : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace CashManagement

variable (C : CashManagement)

/-- The shock set `Ξ = {−k, …, k}`. -/
def Ξ : Finset ℤ := Finset.Icc (-(C.k : ℤ)) C.k

/-- The next-period state (1.24), `F(x, a, ξ) = max{0, min{w̄, x + a + ξ}}`. -/
def next (x : Fin (C.wbar + 1)) (a ξ : ℤ) : Fin (C.wbar + 1) :=
  ⟨(max 0 (min (C.wbar : ℤ) (x + a + ξ))).toNat, by omega⟩

/-- The flow profit (1.25). -/
def profit (x : Fin (C.wbar + 1)) (a ξ : ℤ) : ℝ :=
  C.ρ * ((C.wbar : ℝ) - x) - (if a ≠ 0 then C.c + C.τ * |(a : ℝ)| else 0) -
    (if (x : ℤ) + a + ξ < 0 then C.p else 0)

/-- The cash management problem as a finite MDP (§1.2.1.5). -/
def toMDP : FiniteMDP (Fin (C.wbar + 1)) ℤ where
  Γ x := Finset.Icc (-(x : ℤ)) (C.wbar - x)
  Γ_nonempty x := ⟨0, by simp only [Finset.mem_Icc]; omega⟩
  r x a := ∑ ξ ∈ C.Ξ, C.profit x a ξ * C.φ ξ
  β := C.β
  β_nonneg := C.β_nonneg
  β_lt_one := C.β_lt_one
  P x a x' := ∑ ξ ∈ C.Ξ, if C.next x a ξ = x' then C.φ ξ else 0
  P_nonneg _ _ _ _ := Finset.sum_nonneg fun ξ _ => by
    split_ifs
    · exact C.φ_nonneg ξ
    · exact le_rfl
  P_sum x a _ := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact C.φ_sum

/-- §1.2.1.5: Theorems 1.2.1 and 1.2.2 apply to cash management. The value function uniquely
solves the Bellman equation, an optimal policy exists, VFI and OPI converge, and HPI reaches an
optimal policy in finitely many steps (five iterations in Figure 1.9). -/
theorem optimality :
    (∀ v : Fin (C.wbar + 1) → ℝ, (∀ x, v x = (C.toMDP.Γ x).sup' (C.toMDP.Γ_nonempty x)
      (C.toMDP.Q v x)) → v = C.toMDP.toDP.vstar) ∧ (∃ σ, C.toMDP.toDP.IsOptimal σ) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → C.toMDP.toDP.IsOptimal (C.toMDP.toDP.hpiPolicy σ₀ j) := by
  obtain ⟨-, -, huniq, -, hex⟩ := C.toMDP.theorem_1_2_1
  obtain ⟨-, -, hhpi⟩ := C.toMDP.theorem_1_2_2
  exact ⟨huniq, hex, fun σ₀ => by
    obtain ⟨k, hk⟩ := hhpi σ₀
    exact ⟨k, fun j hj => (hk j hj).2⟩⟩

end CashManagement

end SargentStachurski.PreludeExamples
