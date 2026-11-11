/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.Contractions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Value-function iteration on a grid

AKMM, §10.5, pp. 272–275. The algorithm of p. 272 fixes a grid, represents `V_i` by its values
on the grid, and computes `V_{i+1} = TV_i` with (10.7), `TV(k) = max_{k′} {F(k, k′) + βV(k′)}`,
the choice `k′` restricted to the grid (grid search, Examples 3–4). Here the state space is any
finite set `X` (a grid, or a grid times the exogenous states of §10.5.2), the feasible choices
from `x` a nonempty finite set, and the continuation value an expectation under a transition
`P(x, a, ·)` (`GridDP`, `GridDP.T`): the deterministic case has `P(x, a, ·)` a point mass, the
stochastic cake and growth problems a Markov chain on the shocks.

Proved: `T` is a contraction of modulus `β` in the sup norm (`GridDP.contraction`, through
Sargent–Stachurski's `IsContractionOn`), so (10.6) has a unique solution on the grid, and
`V_i = Tⁱ V₀` converges to it from every `V₀` with `‖V_i − V‖ ≤ βⁱ‖V₀ − V‖` (`GridDP.vfi`);
the stopping rule `max_j |V_{i+1}(a_j) − V_i(a_j)| < ε` bounds the error by `βε/(1 − β)`
(`GridDP.stopping_rule`). Concrete instances: the grid cake-eating problem of §10.5.1
(`cakeGrid`) and the two-state stochastic cake of §10.5.2 (`stochCakeGrid`).
-/

namespace AKMM.ComputationalTools

open Finset

/-- AKMM, §10.5, (10.6)–(10.7) on a finite state space: states `X`, choices `A`, feasible sets
`Γ(x)`, return `F(x, a)`, transition `P(x, a, x′)` to the next state, discount `β ∈ [0, 1)`. -/
structure GridDP (X A : Type*) [Fintype X] where
  /-- the feasible choices from each state -/
  feasible : X → Finset A
  feasible_nonempty : ∀ x, (feasible x).Nonempty
  /-- the current return `F(x, a)` -/
  ret : X → A → ℝ
  /-- the probability of moving to `x′` after choosing `a` in `x` -/
  trans : X → A → X → ℝ
  trans_nonneg : ∀ x a x', 0 ≤ trans x a x'
  trans_sum : ∀ x a, ∑ x', trans x a x' = 1
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace GridDP

variable {X A : Type*} [Fintype X] (M : GridDP X A)

/-- The expected continuation value `E[V(x′) | x, a]`. -/
def cont (V : X → ℝ) (x : X) (a : A) : ℝ := ∑ x', M.trans x a x' * V x'

/-- AKMM, (10.7), p. 272: the Bellman operator `TV(x) = max_{a ∈ Γ(x)} {F(x, a) + βE[V(x′)]}`. -/
def T (V : X → ℝ) (x : X) : ℝ :=
  (M.feasible x).sup' (M.feasible_nonempty x) fun a => M.ret x a + M.β * M.cont V x a

/-- The continuation value moves by at most the sup-distance of the value functions. -/
theorem cont_sub_le (V U : X → ℝ) (x : X) (a : A) : |M.cont V x a - M.cont U x a| ≤ ‖V - U‖ := by
  unfold cont
  rw [← sum_sub_distrib]
  calc |∑ x', (M.trans x a x' * V x' - M.trans x a x' * U x')|
      ≤ ∑ x', |M.trans x a x' * V x' - M.trans x a x' * U x'| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', M.trans x a x' * ‖V - U‖ := by
        refine sum_le_sum fun x' _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (M.trans_nonneg x a x')]
        refine mul_le_mul_of_nonneg_left ?_ (M.trans_nonneg x a x')
        have := norm_le_pi_norm (V - U) x'
        rwa [Real.norm_eq_abs] at this
    _ = ‖V - U‖ := by rw [← sum_mul, M.trans_sum, one_mul]

/-- The maximum over the same finite set moves by at most the largest change. -/
theorem sup'_sub_le {s : Finset A} (hs : s.Nonempty) (f g : A → ℝ) {c : ℝ}
    (h : ∀ a ∈ s, |f a - g a| ≤ c) : |s.sup' hs f - s.sup' hs g| ≤ c := by
  rw [abs_le]
  constructor
  · have : s.sup' hs g ≤ s.sup' hs f + c := by
      refine sup'_le hs _ fun a ha => ?_
      have h1 := (abs_le.1 (h a ha)).2
      have h2 := le_sup' f ha
      have h3 := (abs_le.1 (h a ha)).1
      linarith
    linarith
  · have : s.sup' hs f ≤ s.sup' hs g + c := by
      refine sup'_le hs _ fun a ha => ?_
      have h1 := (abs_le.1 (h a ha)).2
      have h2 := le_sup' g ha
      linarith
    linarith

/-- AKMM, p. 272: `T` is a contraction of modulus `β` in the sup norm (the contraction mapping
theorem of Chapter 4 applies). -/
theorem contraction : SargentStachurski.JobSearch.IsContractionOn M.T Set.univ M.β where
  mapsTo := fun _ _ => Set.mem_univ _
  nonneg := M.β_nonneg
  lt_one := M.β_lt_one
  norm_sub_le := fun V _ U _ => by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold T
    refine sup'_sub_le _ _ _ fun a _ => ?_
    have := M.cont_sub_le V U x a
    calc |M.ret x a + M.β * M.cont V x a - (M.ret x a + M.β * M.cont U x a)|
        = M.β * |M.cont V x a - M.cont U x a| := by
          rw [← abs_of_nonneg M.β_nonneg, ← abs_mul, abs_of_nonneg M.β_nonneg]; ring_nf
      _ ≤ M.β * ‖V - U‖ := mul_le_mul_of_nonneg_left this M.β_nonneg

/-- AKMM, p. 272: "The contraction mapping theorem guarantees `V_i(k)` approaches the true value
function `V(k)` for (10.6) as `i → ∞`, regardless of the starting value function `V₀(k)`": the
Bellman equation `V = TV` has a unique solution, and `‖TⁱV₀ − V‖ ≤ βⁱ‖V₀ − V‖`. -/
theorem vfi : ∃ V : X → ℝ, M.T V = V ∧ (∀ W, M.T W = W → W = V) ∧
    ∀ V₀ : X → ℝ, ∀ i : ℕ, ‖M.T^[i] V₀ - V‖ ≤ M.β ^ i * ‖V₀ - V‖ := by
  obtain ⟨V, -, hV, huniq, hrate⟩ :=
    M.contraction.banach_pi isClosed_univ Set.univ_nonempty
  exact ⟨V, hV, fun W hW => huniq W (Set.mem_univ _) hW,
    fun V₀ i => hrate V₀ (Set.mem_univ _) i⟩

/-- AKMM, p. 273, step 4: "stop when `max_j |V_{i+1}(a_j) − V_i(a_j)| < ε`": then `V_{i+1}` is
within `βε/(1 − β)` of the solution `V` of the Bellman equation. -/
theorem stopping_rule {V W : X → ℝ} (hV : M.T V = V) {ε : ℝ} (h : ‖M.T W - W‖ ≤ ε) :
    ‖M.T W - V‖ ≤ M.β * ε / (1 - M.β) := by
  have hc := M.contraction.norm_sub_le W (Set.mem_univ _) V (Set.mem_univ _)
  rw [hV] at hc
  have htri : ‖W - V‖ ≤ ‖M.T W - W‖ + ‖M.T W - V‖ := by
    calc ‖W - V‖ = ‖-(M.T W - W) + (M.T W - V)‖ := by congr 1; abel
      _ ≤ ‖-(M.T W - W)‖ + ‖M.T W - V‖ := norm_add_le _ _
      _ = ‖M.T W - W‖ + ‖M.T W - V‖ := by rw [norm_neg]
  have h1 := M.β_lt_one
  rw [le_div_iff₀ (by linarith)]
  nlinarith [M.β_nonneg, norm_nonneg (M.T W - V)]

end GridDP

/-- AKMM, §10.5.1, p. 273, steps 1 and 3 (grid search): the cake-eating problem on the grid
`a_j = j·a₀/n`, `j = 0, …, n`, with the choice `a′` restricted to grid points `a_k ≤ a_j` and
return `√(a_j − a_k)`; the next state is `a_k` for sure. -/
noncomputable def cakeGrid (n : ℕ) (a₀ β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GridDP (Fin (n + 1)) (Fin (n + 1)) where
  feasible j := univ.filter fun k => k ≤ j
  feasible_nonempty j := ⟨0, by simp⟩
  ret j k := √(j * a₀ / n - k * a₀ / n)
  trans _ k k' := if k' = k then 1 else 0
  trans_nonneg _ _ _ := by split_ifs <;> norm_num
  trans_sum _ k := by simp
  β := β
  β_nonneg := hβ0
  β_lt_one := hβ1

/-- AKMM, Example 3, p. 274 (grid search, `β = 0.98`, `a₀ = 10`): value-function iteration on the
cake grid converges to the unique solution of the grid Bellman equation. -/
theorem cakeGrid_vfi (n : ℕ) :
    ∃ V : Fin (n + 1) → ℝ, (cakeGrid n 10 0.98 (by norm_num) (by norm_num)).T V = V ∧
      ∀ V₀ : Fin (n + 1) → ℝ, ∀ i : ℕ,
        ‖(cakeGrid n 10 0.98 (by norm_num) (by norm_num)).T^[i] V₀ - V‖ ≤
          0.98 ^ i * ‖V₀ - V‖ := by
  obtain ⟨V, hV, -, hrate⟩ := (cakeGrid n 10 0.98 (by norm_num) (by norm_num)).vfi
  exact ⟨V, hV, hrate⟩

/-- AKMM, §10.5.2, pp. 273–274: the stochastic cake on the grid. States are pairs (grid point
`a_j`, shock `s ∈ {L, H}` with cake arrival `z_s ≥ 0`); the choice is a grid point `a_k` with
`a_k ≤ a_j + z_s`, the return `√(a_j − a_k + z_s)`, and the next state `(a_k, s′)` with
probability `π_{ss′}` (`Pz`). -/
noncomputable def stochCakeGrid (n : ℕ) (amax : ℝ) (z : Fin 2 → ℝ) (hz : ∀ s, 0 ≤ z s)
    (Pz : Fin 2 → Fin 2 → ℝ) (hP0 : ∀ s s', 0 ≤ Pz s s') (hP1 : ∀ s, ∑ s', Pz s s' = 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hamax : 0 ≤ amax) :
    GridDP (Fin (n + 1) × Fin 2) (Fin (n + 1)) where
  feasible x := univ.filter fun k => (k : ℝ) * amax / n ≤ x.1 * amax / n + z x.2
  feasible_nonempty x := ⟨0, by
    simp only [mem_filter, mem_univ, true_and, Fin.val_zero, Nat.cast_zero, zero_mul, zero_div]
    have : 0 ≤ (x.1 : ℝ) * amax / n := by positivity
    linarith [hz x.2]⟩
  ret x k := √(x.1 * amax / n - k * amax / n + z x.2)
  trans x k y := if y.1 = k then Pz x.2 y.2 else 0
  trans_nonneg x k y := by split_ifs <;> simp [hP0]
  trans_sum x k := by
    rw [Fintype.sum_prod_type]
    simp [hP1]
  β := β
  β_nonneg := hβ0
  β_lt_one := hβ1

end AKMM.ComputationalTools
