/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

/-!
# Hidden information: the model and the incentive constraints

Miao, §22.3, pp. 788–791: the Thomas–Worrall (1990) model. The agent's income `yₜ` is iid on
`Θ = {θ₁ < ⋯ < θₙ}` with `Pr(yₜ = θᵢ) = πᵢ` and is privately observed; the agent cannot save,
the principal is risk neutral, both discount with `β ∈ (0, 1)`. A one-period contract at
promised value `v` is a list `(cᵢ, wᵢ)` of transfers and continuation values.

* `HIModel`: the primitives. The index set is `Fin (N + 1)` (so `n = N + 1 ≥ 1`), `θ` is strictly
  increasing, the probabilities `prob` (the book's `πᵢ`; `π` is reserved) are positive and sum
  to one. The utility `u` is defined on all of `ℝ` (the book's `a = −∞`, as for the CARA utility
  of Exercise 22.4), continuous, strictly increasing, strictly concave, bounded above and
  unbounded below (the part of Assumption 22.3.1 used for the Bellman equation; the derivative
  conditions are in `HIAssumption`).
* `hi_C` is `Cᵢⱼ` of (22.24), `hi_IC` the incentive constraints, `hi_agentValue` the left side of
  the promise-keeping constraint (22.25), `hi_vmax = sup u / (1 − β)`, `hi_Feasible`.
* `lemma_22_3_1` (Lemma 22.3.1): incentive constraints imply `cᵢ₋₁ ≥ cᵢ`, `wᵢ₋₁ ≤ wᵢ`; it is
  proved from the two local constraints alone (`hi_local_mono`), as the book's proof does.
* `lemma_22_3_2` (Lemma 22.3.2): the local downward and upward constraints imply all constraints.
* `hi_upward_of_binding`: a binding local downward constraint with `cᵢ ≤ cᵢ₋₁` implies the local
  upward constraint (used in the proofs of Propositions 22.3.1 and 22.3.2).
* `hi_C_shift`, `hi_agentValue_shift`: shifting every `wᵢ` by `k` keeps every `Cᵢⱼ` and raises
  the agent's value by `βk` (the intuition for the martingale property, p. 796).
* `hi_cara`, `hi_caraModel`, `hi_exampleModel`: the CARA utility `−exp(−γc)` gives a model; a
  concrete two-state instance shows the hypotheses are satisfiable.
-/

namespace Miao.RecursiveContracts

open Finset

/-- The primitives of the hidden-information model of Miao, §22.3, pp. 788–789. The income
states are `Fin (N + 1)`; `prob i` is the book's `πᵢ`. -/
structure HIModel where
  /-- `n − 1`, so that there are `N + 1 ≥ 1` income states. -/
  N : ℕ
  /-- Income levels `θ₁ < ⋯ < θₙ`. -/
  θ : Fin (N + 1) → ℝ
  /-- The probabilities `πᵢ`. -/
  prob : Fin (N + 1) → ℝ
  /-- The common discount factor. -/
  β : ℝ
  /-- The agent's period utility. -/
  u : ℝ → ℝ
  θ_strictMono : StrictMono θ
  prob_pos : ∀ i, 0 < prob i
  prob_sum : ∑ i, prob i = 1
  β_pos : 0 < β
  β_lt_one : β < 1
  u_cont : Continuous u
  u_strictMono : StrictMono u
  u_strictConcave : StrictConcaveOn ℝ Set.univ u
  u_bddAbove : BddAbove (Set.range u)
  u_not_bddBelow : ¬ BddBelow (Set.range u)

/-- Miao, (22.24), p. 789: `Cᵢⱼ = u(θᵢ + cᵢ) + βwᵢ − [u(θᵢ + cⱼ) + βwⱼ]`, the gain of type `i`
from telling the truth rather than reporting `θⱼ`. -/
def hi_C (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (i j : Fin (M.N + 1)) : ℝ :=
  M.u (M.θ i + c i) + M.β * w i - (M.u (M.θ i + c j) + M.β * w j)

/-- Miao, (22.24), p. 789: all incentive constraints `Cᵢⱼ ≥ 0`. -/
def hi_IC (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  ∀ i j, 0 ≤ hi_C M c w i j

/-- The local downward (`Cᵢ,ᵢ₋₁ ≥ 0`) and upward (`Cᵢ₋₁,ᵢ ≥ 0`) constraints of Lemma 22.3.2. -/
def hi_LocalIC (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  ∀ i : Fin M.N, 0 ≤ hi_C M c w i.succ i.castSucc ∧ 0 ≤ hi_C M c w i.castSucc i.succ

/-- Miao, (22.25), p. 789: the agent's expected value `Σ πᵢ [u(θᵢ + cᵢ) + βwᵢ]`. -/
def hi_agentValue (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : ℝ :=
  ∑ i, M.prob i * (M.u (M.θ i + c i) + M.β * w i)

/-- The principal's value `Σ πᵢ [−cᵢ + β f(wᵢ)]` of a contract against a continuation `f`, the
objective of (22.23). -/
def hi_principalValue (M : HIModel) (f : ℝ → ℝ) (c w : Fin (M.N + 1) → ℝ) : ℝ :=
  ∑ i, M.prob i * (-c i + M.β * f (w i))

/-- `sup u`. -/
noncomputable def hi_ubar (M : HIModel) : ℝ := sSup (Set.range M.u)

/-- Miao, p. 789: `vmax = sup u(c) / (1 − β)`. -/
noncomputable def hi_vmax (M : HIModel) : ℝ := hi_ubar M / (1 - M.β)

/-- Miao, (22.23)–(22.25), p. 789: the contract `(c, w)` is feasible at `v`: incentive
compatible, promise keeping, and `wᵢ < vmax` (the book allows `wᵢ ∈ [−∞, vmax]`; real
continuation values below the supremum are used here). -/
def hi_Feasible (M : HIModel) (v : ℝ) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  hi_IC M c w ∧ hi_agentValue M c w = v ∧ ∀ i, w i < hi_vmax M

/-- A strictly concave function has strictly decreasing increments: for `x < y` and `d > 0`,
`f(y + d) − f(y) < f(x + d) − f(x)`. -/
theorem hi_strict_decreasing_increments {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ Set.univ f)
    {x y d : ℝ} (hxy : x < y) (hd : 0 < d) : f (y + d) - f y < f (x + d) - f x := by
  have h1 := hf.secant_strict_mono (a := x) (x := x + d) (y := y + d) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) (by linarith)
  have h2 := hf.secant_strict_mono (a := y + d) (x := x) (y := y) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) hxy
  have e1 : (f (x + d) - f x) / (x + d - x) = (f (x + d) - f x) / d := by ring_nf
  have e2 : (f y - f (y + d)) / (y - (y + d)) = (f (y + d) - f y) / d := by
    rw [show y - (y + d) = -d by ring, div_neg, ← neg_div]; ring
  have e3 : (f x - f (y + d)) / (x - (y + d)) = (f (y + d) - f x) / (y + d - x) := by
    rw [show x - (y + d) = -(y + d - x) by ring, div_neg, ← neg_div]; ring
  rw [e1] at h1
  rw [e2, e3] at h2
  exact (div_lt_div_iff_of_pos_right hd).1 (h2.trans h1)

/-- A concave function has decreasing increments: for `x ≤ y` and `d ≥ 0`,
`f(y + d) − f(y) ≤ f(x + d) − f(x)`. -/
theorem hi_decreasing_increments {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ Set.univ f)
    {x y d : ℝ} (hxy : x ≤ y) (hd : 0 ≤ d) : f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · exact (hi_strict_decreasing_increments hf hxy hd).le
    · simp
  · exact le_rfl

/-- Miao, p. 790 (proof of Lemma 22.3.1): `Cᵢ,ₖ + Cₖ,ᵢ = [u(θᵢ + cᵢ) − u(θₖ + cᵢ)] −
[u(θᵢ + cₖ) − u(θₖ + cₖ)]`. -/
theorem hi_C_add_C (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (i k : Fin (M.N + 1)) :
    hi_C M c w i k + hi_C M c w k i =
      (M.u (M.θ i + c i) - M.u (M.θ k + c i)) - (M.u (M.θ i + c k) - M.u (M.θ k + c k)) := by
  unfold hi_C; ring

/-- Miao, p. 790 (proof of Lemma 22.3.1): the pair of constraints `Cᵢₖ ≥ 0`, `Cₖᵢ ≥ 0` with
`θₖ < θᵢ` implies `cᵢ ≤ cₖ` and `wₖ ≤ wᵢ`. -/
theorem hi_pair_mono (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i k : Fin (M.N + 1)}
    (hki : k < i) (h1 : 0 ≤ hi_C M c w i k) (h2 : 0 ≤ hi_C M c w k i) :
    c i ≤ c k ∧ w k ≤ w i := by
  have hθ : M.θ k < M.θ i := M.θ_strictMono hki
  have hc : c i ≤ c k := by
    by_contra hlt
    push Not at hlt
    have key := hi_strict_decreasing_increments M.u_strictConcave
      (x := M.θ k + c k) (y := M.θ k + c i) (d := M.θ i - M.θ k) (by linarith) (by linarith)
    have hs := hi_C_add_C M c w i k
    rw [show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring,
      show M.θ k + c k + (M.θ i - M.θ k) = M.θ i + c k by ring] at key
    linarith
  refine ⟨hc, ?_⟩
  have hu : M.u (M.θ i + c i) ≤ M.u (M.θ i + c k) := M.u_strictMono.monotone (by linarith)
  unfold hi_C at h1
  nlinarith [M.β_pos]

/-- Miao, p. 790 (proof of Lemma 22.3.1, local form): the local constraints imply that `c` is
antitone and `w` is monotone. -/
theorem hi_local_mono (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (h : hi_LocalIC M c w) :
    Antitone c ∧ Monotone w := by
  refine ⟨Fin.antitone_iff_succ_le.2 fun i => ?_, Fin.monotone_iff_le_succ.2 fun i => ?_⟩
  · exact (hi_pair_mono M c w (Fin.castSucc_lt_succ) (h i).1 (h i).2).1
  · exact (hi_pair_mono M c w (Fin.castSucc_lt_succ) (h i).1 (h i).2).2

/-- **Lemma 22.3.1** (Miao, p. 790). Incentive constraints imply `cᵢ₋₁ ≥ cᵢ` and `wᵢ₋₁ ≤ wᵢ`
for all `i`: `c` is antitone and `w` is monotone in the income state. -/
theorem lemma_22_3_1 (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (h : hi_IC M c w) :
    Antitone c ∧ Monotone w :=
  hi_local_mono M c w fun _ => ⟨h _ _, h _ _⟩

/-- Miao, p. 791 (proof of Lemma 22.3.2, downward step): if `Cᵢₖ ≥ 0`, `cᵢ ≤ cₖ`, `θᵢ ≤ θⱼ`,
and `Cⱼᵢ ≥ 0`, then `Cⱼₖ ≥ 0`. -/
theorem hi_down_step (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i j k : Fin (M.N + 1)}
    (hij : i ≤ j) (hc : c i ≤ c k) (h1 : 0 ≤ hi_C M c w i k) (h2 : 0 ≤ hi_C M c w j i) :
    0 ≤ hi_C M c w j k := by
  have hθ : M.θ i ≤ M.θ j := M.θ_strictMono.monotone hij
  have key := hi_decreasing_increments M.u_strictConcave (x := M.θ i + c i)
    (y := M.θ i + c k) (d := M.θ j - M.θ i) (by linarith) (by linarith)
  rw [show M.θ i + c i + (M.θ j - M.θ i) = M.θ j + c i by ring,
    show M.θ i + c k + (M.θ j - M.θ i) = M.θ j + c k by ring] at key
  unfold hi_C at *
  linarith

/-- Miao, p. 791 (proof of Lemma 22.3.2, upward step): if `Cₖᵢ ≥ 0`, `cⱼ ≤ cᵢ`, `θₖ ≤ θᵢ`
and `Cᵢⱼ ≥ 0`, then `Cₖⱼ ≥ 0`. -/
theorem hi_up_step (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i j k : Fin (M.N + 1)}
    (hki : k ≤ i) (hc : c j ≤ c i) (h1 : 0 ≤ hi_C M c w k i) (h2 : 0 ≤ hi_C M c w i j) :
    0 ≤ hi_C M c w k j := by
  have hθ : M.θ k ≤ M.θ i := M.θ_strictMono.monotone hki
  have key := hi_decreasing_increments M.u_strictConcave (x := M.θ k + c j)
    (y := M.θ k + c i) (d := M.θ i - M.θ k) (by linarith) (by linarith)
  rw [show M.θ k + c j + (M.θ i - M.θ k) = M.θ i + c j by ring,
    show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring] at key
  unfold hi_C at *
  linarith

/-- **Lemma 22.3.2** (Miao, p. 791). If the local downward constraints `Cᵢ,ᵢ₋₁ ≥ 0` and the local
upward constraints `Cᵢ₋₁,ᵢ ≥ 0` hold for each `i`, then all the constraints `Cᵢⱼ ≥ 0` hold. -/
theorem lemma_22_3_2 (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (h : hi_LocalIC M c w) :
    hi_IC M c w := by
  obtain ⟨hc, -⟩ := hi_local_mono M c w h
  have hself : ∀ i, hi_C M c w i i = 0 := fun i => by unfold hi_C; ring
  -- downward: `C_{k+m, k} ≥ 0`, by induction on `m`
  have down : ∀ m : ℕ, ∀ k : Fin (M.N + 1), ∀ hm : k.val + m < M.N + 1,
      0 ≤ hi_C M c w ⟨k.val + m, hm⟩ k := by
    intro m
    induction m with
    | zero => intro k _; simp [hself]
    | succ m ih =>
      intro k hm
      have hm' : k.val + m < M.N := by omega
      have ih' := ih k (by omega)
      have hloc := (h ⟨k.val + m, hm'⟩).1
      have e1 : (⟨k.val + m, hm'⟩ : Fin M.N).succ = ⟨k.val + (m + 1), hm⟩ := by
        ext; simp; omega
      have e2 : (⟨k.val + m, hm'⟩ : Fin M.N).castSucc = ⟨k.val + m, by omega⟩ := rfl
      rw [e1, e2] at hloc
      exact hi_down_step M c w (Fin.mk_le_mk.2 (by omega))
        (hc (Fin.mk_le_mk.2 (by omega) : k ≤ ⟨k.val + m, by omega⟩)) ih' hloc
  -- upward: `C_{k, k+m} ≥ 0`, by induction on `m`
  have up : ∀ m : ℕ, ∀ k : Fin (M.N + 1), ∀ hm : k.val + m < M.N + 1,
      0 ≤ hi_C M c w k ⟨k.val + m, hm⟩ := by
    intro m
    induction m with
    | zero => intro k _; simp [hself]
    | succ m ih =>
      intro k hm
      have hm' : k.val + m < M.N := by omega
      have ih' := ih k (by omega)
      have hloc := (h ⟨k.val + m, hm'⟩).2
      have e1 : (⟨k.val + m, hm'⟩ : Fin M.N).succ = ⟨k.val + (m + 1), hm⟩ := by
        ext; simp; omega
      have e2 : (⟨k.val + m, hm'⟩ : Fin M.N).castSucc = ⟨k.val + m, by omega⟩ := rfl
      rw [e1, e2] at hloc
      exact hi_up_step M c w (Fin.mk_le_mk.2 (by omega))
        (hc (Fin.mk_le_mk.2 (by omega))) ih' hloc
  intro i j
  rcases le_total j i with hji | hij
  · have := down (i.val - j.val) j (by omega)
    have e : (⟨j.val + (i.val - j.val), by omega⟩ : Fin (M.N + 1)) = i := by
      ext; simp only; omega
    rwa [e] at this
  · have := up (j.val - i.val) i (by omega)
    have e : (⟨i.val + (j.val - i.val), by omega⟩ : Fin (M.N + 1)) = j := by
      ext; simp only; omega
    rwa [e] at this

/-- Miao, p. 793 and p. 794 (proofs of Propositions 22.3.1 and 22.3.2): a binding local
downward constraint `Cᵢ,ₖ = 0` (`θₖ < θᵢ`) together with `cᵢ ≤ cₖ` implies the upward
constraint `Cₖ,ᵢ ≥ 0`; it is slack (`Cₖ,ᵢ > 0`) when `cᵢ < cₖ`. -/
theorem hi_upward_of_binding (M : HIModel) (c w : Fin (M.N + 1) → ℝ) {i k : Fin (M.N + 1)}
    (hki : k < i) (hbind : hi_C M c w i k = 0) (hc : c i ≤ c k) :
    0 ≤ hi_C M c w k i ∧ (c i < c k → 0 < hi_C M c w k i) := by
  have hθ : M.θ k < M.θ i := M.θ_strictMono hki
  have hs := hi_C_add_C M c w i k
  refine ⟨?_, fun hlt => ?_⟩
  · have key := hi_decreasing_increments M.u_strictConcave (x := M.θ k + c i)
      (y := M.θ k + c k) (d := M.θ i - M.θ k) (by linarith) (by linarith)
    rw [show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring,
      show M.θ k + c k + (M.θ i - M.θ k) = M.θ i + c k by ring] at key
    linarith
  · have key := hi_strict_decreasing_increments M.u_strictConcave (x := M.θ k + c i)
      (y := M.θ k + c k) (d := M.θ i - M.θ k) (by linarith) (by linarith)
    rw [show M.θ k + c i + (M.θ i - M.θ k) = M.θ i + c i by ring,
      show M.θ k + c k + (M.θ i - M.θ k) = M.θ i + c k by ring] at key
    linarith

/-- Miao, p. 796: adding a constant `k` to every continuation value `wᵢ` leaves every
incentive constraint `Cᵢⱼ` unchanged. -/
theorem hi_C_shift (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (k : ℝ) (i j : Fin (M.N + 1)) :
    hi_C M c (fun l => w l + k) i j = hi_C M c w i j := by
  unfold hi_C; ring

/-- Miao, p. 796: adding `k` to every `wᵢ` raises the agent's value by `βk`. -/
theorem hi_agentValue_shift (M : HIModel) (c w : Fin (M.N + 1) → ℝ) (k : ℝ) :
    hi_agentValue M c (fun l => w l + k) = hi_agentValue M c w + M.β * k := by
  unfold hi_agentValue
  have : ∑ i, M.prob i * (M.u (M.θ i + c i) + M.β * (w i + k)) =
      ∑ i, M.prob i * (M.u (M.θ i + c i) + M.β * w i) + (∑ i, M.prob i) * (M.β * k) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, M.prob_sum, one_mul]

/-- The CARA utility `u(c) = −exp(−γc)` of Exercise 22.4. -/
noncomputable def hi_cara (γ : ℝ) (x : ℝ) : ℝ := -Real.exp (-γ * x)

/-- The CARA utility is strictly increasing. -/
theorem hi_cara_strictMono {γ : ℝ} (hγ : 0 < γ) : StrictMono (hi_cara γ) := by
  intro x y hxy
  unfold hi_cara
  have : -γ * y < -γ * x := by nlinarith
  linarith [Real.exp_lt_exp.2 this]

/-- The CARA utility is strictly concave. -/
theorem hi_cara_strictConcave {γ : ℝ} (hγ : 0 < γ) :
    StrictConcaveOn ℝ Set.univ (hi_cara γ) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hne : -γ * x ≠ -γ * y := by
    intro h; exact hxy (by have := mul_left_cancel₀ (neg_ne_zero.2 hγ.ne') h; exact this)
  have key := (strictConvexOn_exp).2 (Set.mem_univ (-γ * x)) (Set.mem_univ (-γ * y)) hne ha hb hab
  simp only [smul_eq_mul, hi_cara] at key ⊢
  have e : -γ * (a * x + b * y) = a * (-γ * x) + b * (-γ * y) := by ring
  rw [e]
  linarith

/-- The CARA utility is bounded above by `0`, with supremum `0`. -/
theorem hi_cara_sSup {γ : ℝ} (hγ : 0 < γ) : sSup (Set.range (hi_cara γ)) = 0 := by
  refine le_antisymm (csSup_le (Set.range_nonempty _) ?_) ?_
  · rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]
  · refine le_of_forall_lt fun ε hε => ?_
    have hbdd : BddAbove (Set.range (hi_cara γ)) := ⟨0, by
      rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]⟩
    -- choose `x` with `exp(−γx) < −ε`
    have hε' : 0 < -ε := by linarith
    refine lt_csSup_of_lt hbdd ⟨-Real.log (-ε) / γ + 1, rfl⟩ ?_
    unfold hi_cara
    have e : -γ * (-Real.log (-ε) / γ + 1) = Real.log (-ε) - γ := by field_simp; ring
    rw [e, Real.exp_sub, Real.exp_log hε']
    have h1 : 1 < Real.exp γ := Real.one_lt_exp_iff.2 hγ
    have : -ε / Real.exp γ < -ε := div_lt_self hε' h1
    linarith

/-- The CARA utility is unbounded below. -/
theorem hi_cara_not_bddBelow {γ : ℝ} (hγ : 0 < γ) : ¬ BddBelow (Set.range (hi_cara γ)) := by
  rintro ⟨m, hm⟩
  have h := hm ⟨-Real.log (|m| + 1) / γ, rfl⟩
  unfold hi_cara at h
  have e : -γ * (-Real.log (|m| + 1) / γ) = Real.log (|m| + 1) := by field_simp
  rw [e, Real.exp_log (by positivity)] at h
  have := neg_abs_le m
  linarith

/-- The hidden-information model with CARA utility `−exp(−γc)` (Exercise 22.4), for any income
distribution and discount factor. -/
noncomputable def hi_caraModel (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (θ prob : Fin (N + 1) → ℝ)
    (β : ℝ) (hθ : StrictMono θ) (hp : ∀ i, 0 < prob i) (hs : ∑ i, prob i = 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) : HIModel where
  N := N
  θ := θ
  prob := prob
  β := β
  u := hi_cara γ
  θ_strictMono := hθ
  prob_pos := hp
  prob_sum := hs
  β_pos := hβ0
  β_lt_one := hβ1
  u_cont := by unfold hi_cara; fun_prop
  u_strictMono := hi_cara_strictMono hγ
  u_strictConcave := hi_cara_strictConcave hγ
  u_bddAbove := ⟨0, by rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]⟩
  u_not_bddBelow := hi_cara_not_bddBelow hγ

/-- A concrete instance: two income states `θ = (0, 1)` with probabilities `(1/2, 1/2)`,
`β = 1/2`, CARA utility with `γ = 1`. -/
noncomputable def hi_exampleModel : HIModel :=
  hi_caraModel 1 one_pos 1 ![0, 1] ![1 / 2, 1 / 2] (1 / 2)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) (by norm_num) (by norm_num)

/-- The concrete instance has two income states. -/
theorem hi_exampleModel_N : hi_exampleModel.N = 1 := rfl

end Miao.RecursiveContracts
