/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXCopied
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The event tree of §14.3

Miao, §14.3, pp. 493–508: the stochastic models of §14.3 are written with conditional
expectations `E_t`. We write them on an event tree, as in Chapter 13: a node is a history
`h : List S` of shocks from a finite set `S`, most recent first; its successors are the lists
`s :: h`, and `cp h s` is the conditional probability of `s` given `h`. A process is a function
`List S → ℝ` (its value at a date-`t` node is its date-`t` value); a variable chosen at date
`t`, such as `K_{t+1}`, is a function of the date-`t` node at which it is chosen.

* `RXTree S`: conditional probabilities `cp h s ≥ 0`, `∑ₛ cp h s = 1`; concrete instances
  `rx_detTree` (deterministic, perfect foresight) and `rx_coinTree` (a fair coin each period).
* `rx_E T x h = E_t[x_{t+1}]` at the node `h` (`rx_Es T h f` for a successor-indexed
  `f`), its linearity, and "taking out what is known"
  (`rx_E_mul_left`).
* `rx_pv T m n x h = E_t[M_{t,t+n} x_{t+n}]`, the value at `h` of a payoff `n` periods ahead
  under the one-period stochastic discount factor `m` (`M_{t,t+n}` is the product of `m` along
  the path), and the forward iteration of a pricing recursion `y = E[m(d + y)]`
  (`rx_pv_iterate`, `rx_pv_limit`).
* `rx_node_foc`: the first-order condition of a node problem in which a variable chosen at `h`
  enters the objective at `h` and at all successors of `h`.
* `rx_homog_hasDerivAt`: a positively homogeneous function of one variable is linear on
  `(0, ∞)`, so its derivative equals its average (used for `∂P/∂K = P/K`).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- An event tree (Miao, §13.1, used in §14.3): conditional probabilities of the next shock
given the history. -/
structure RXTree (S : Type*) [Fintype S] where
  /-- `cp h s = Pr(s | h)`. -/
  cp : List S → S → ℝ
  cp_nonneg : ∀ h s, 0 ≤ cp h s
  cp_sum : ∀ h, ∑ s, cp h s = 1

/-- The deterministic tree: one shock, conditional probability one. -/
def rx_detTree : RXTree Unit where
  cp := fun _ _ => 1
  cp_nonneg := fun _ _ => zero_le_one
  cp_sum := fun _ => by simp

/-- The coin tree: two equally likely shocks each period. -/
noncomputable def rx_coinTree : RXTree Bool where
  cp := fun _ _ => 1 / 2
  cp_nonneg := fun _ _ => by norm_num
  cp_sum := fun _ => by simp

/-- The conditional expectation `E_t[x_{t+1}]` at the node `h`. -/
def rx_E {S : Type*} [Fintype S] (T : RXTree S) (x : List S → ℝ) (h : List S) : ℝ :=
  ∑ s, T.cp h s * x (s :: h)

/-- The conditional expectation `Eₜ[f]` of a successor-indexed date-`t+1` quantity `f s` at
the node `h`. -/
def rx_Es {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (f : S → ℝ) : ℝ :=
  ∑ s, T.cp h s * f s

/-- `rx_Es` is `rx_E` of the process whose value at `s :: h` is `f s`. -/
theorem rx_E_eq_Es {S : Type*} [Fintype S] (T : RXTree S) (x : List S → ℝ) (h : List S) :
    rx_E T x h = rx_Es T h (fun s => x (s :: h)) := rfl

theorem rx_Es_add {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (f g : S → ℝ) :
    rx_Es T h (fun s => f s + g s) = rx_Es T h f + rx_Es T h g := by
  simp only [rx_Es, mul_add, Finset.sum_add_distrib]

theorem rx_Es_mul_left {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (a : ℝ)
    (f : S → ℝ) : rx_Es T h (fun s => a * f s) = a * rx_Es T h f := by
  simp only [rx_Es, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem rx_Es_const {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (a : ℝ) :
    rx_Es T h (fun _ => a) = a := by
  simp only [rx_Es, ← Finset.sum_mul, T.cp_sum, one_mul]

/-- In the deterministic tree the expectation is the value at the unique successor. -/
theorem rx_E_det (x : List Unit → ℝ) (h : List Unit) : rx_E rx_detTree x h = x (() :: h) := by
  simp [rx_E, rx_detTree]

/-- In the coin tree the expectation is the average over the two successors. -/
theorem rx_E_coin (x : List Bool → ℝ) (h : List Bool) :
    rx_E rx_coinTree x h = (x (true :: h) + x (false :: h)) / 2 := by
  simp [rx_E, rx_coinTree]
  ring

theorem rx_E_add {S : Type*} [Fintype S] (T : RXTree S) (x y : List S → ℝ) (h : List S) :
    rx_E T (fun g => x g + y g) h = rx_E T x h + rx_E T y h := by
  simp only [rx_E, mul_add, Finset.sum_add_distrib]

/-- Expectation of a constant. -/
theorem rx_E_const {S : Type*} [Fintype S] (T : RXTree S) (a : ℝ) (h : List S) :
    rx_E T (fun _ => a) h = a := by
  simp only [rx_E, ← Finset.sum_mul, T.cp_sum, one_mul]

/-- Taking out what is known: a factor fixed at the date-`t` node leaves the expectation. -/
theorem rx_E_mul_left {S : Type*} [Fintype S] (T : RXTree S) (a : ℝ) (x : List S → ℝ)
    (h : List S) : rx_E T (fun g => a * x g) h = a * rx_E T x h := by
  simp only [rx_E, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `rx_pv T m n x h = E_t[M_{t,t+n} x_{t+n}]` at the node `h`, with `M` the product of the
one-period discount factors `m` along the path. -/
def rx_pv {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) :
    ℕ → (List S → ℝ) → List S → ℝ
  | 0, x, h => x h
  | n + 1, x, h => ∑ s, T.cp h s * (m (s :: h) * rx_pv T m n x (s :: h))

theorem rx_pv_one {S : Type*} [Fintype S] (T : RXTree S) (m x : List S → ℝ) (h : List S) :
    rx_pv T m 1 x h = rx_E T (fun g => m g * x g) h := rfl

theorem rx_pv_add {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (n : ℕ)
    (x y : List S → ℝ) (h : List S) :
    rx_pv T m n (fun g => x g + y g) h = rx_pv T m n x h + rx_pv T m n y h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [rx_pv, ih, mul_add, Finset.sum_add_distrib]

theorem rx_pv_sum {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (N : ℕ)
    (x : List S → ℝ) (h : List S) :
    ∑ j ∈ Finset.range N, rx_pv T m (j + 1 + 1) x h =
      ∑ s, T.cp h s * (m (s :: h) * ∑ j ∈ Finset.range N, rx_pv T m (j + 1) x (s :: h)) := by
  simp only [rx_pv, Finset.mul_sum]
  exact Finset.sum_comm

/-- Forward iteration of the pricing recursion `yₜ = Eₜ[m_{t+1}(d_{t+1} + y_{t+1})]`:
`yₜ = Σ_{j<n} Eₜ[M_{t,t+j+1} d_{t+j+1}] + Eₜ[M_{t,t+n} y_{t+n}]`. -/
theorem rx_pv_iterate {S : Type*} [Fintype S] (T : RXTree S) {m d y : List S → ℝ}
    (hy : ∀ h, y h = rx_E T (fun g => m g * (d g + y g)) h) (n : ℕ) (h : List S) :
    y h = ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d h + rx_pv T m n y h := by
  induction n generalizing h with
  | zero => simp [rx_pv]
  | succ n ih =>
    rw [Finset.sum_range_succ', rx_pv_sum, hy h]
    rw [show rx_pv T m (0 + 1) d h = ∑ s, T.cp h s * (m (s :: h) * d (s :: h)) from rfl,
      show rx_pv T m (n + 1) y h = ∑ s, T.cp h s * (m (s :: h) * rx_pv T m n y (s :: h))
        from rfl]
    simp only [rx_E]
    rw [add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih (s :: h)]
    ring

/-- The present-value formula: if the residual `Eₜ[M_{t,t+n} y_{t+n}]` vanishes as `n → ∞`
(transversality), then `yₜ = Σ_{j ≥ 1} Eₜ[M_{t,t+j} d_{t+j}]` (limit of partial sums). -/
theorem rx_pv_limit {S : Type*} [Fintype S] (T : RXTree S) {m d y : List S → ℝ}
    (hy : ∀ h, y h = rx_E T (fun g => m g * (d g + y g)) h) (h : List S)
    (htvc : Tendsto (fun n => rx_pv T m n y h) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d h) atTop (𝓝 (y h)) := by
  have h3 := (tendsto_const_nhds (x := y h)).sub htvc
  rw [sub_zero] at h3
  refine h3.congr fun n => ?_
  rw [rx_pv_iterate T hy n h]
  ring

/-- The first-order condition of a node problem. A variable `k` chosen at a node enters the
objective through `c₀(k)` at that node (felicity `U₀`) and through `c₁ₛ(k)` at each successor
`s` (felicity `U₁ₛ`, conditional probability `pₛ`, discount factor `β`). At a local maximum,
`U₀′ c₀′ + β Σₛ pₛ U₁ₛ′ c₁ₛ′ = 0`. -/
theorem rx_node_foc {S : Type*} [Fintype S] {U0 c0 : ℝ → ℝ} {U1 c1 : S → ℝ → ℝ} {p : S → ℝ}
    {β k l0 d0 : ℝ} {l1 d1 : S → ℝ} (hU0 : HasDerivAt U0 l0 (c0 k)) (hc0 : HasDerivAt c0 d0 k)
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (c1 s k)) (hc1 : ∀ s, HasDerivAt (c1 s) (d1 s) k)
    (hmax : IsLocalMax (fun x => U0 (c0 x) + β * ∑ s, p s * U1 s (c1 s x)) k) :
    l0 * d0 + β * ∑ s, p s * (l1 s * d1 s) = 0 := by
  have hs : HasDerivAt (fun x => ∑ s, p s * U1 s (c1 s x)) (∑ s, p s * (l1 s * d1 s)) k :=
    HasDerivAt.fun_sum fun s _ => ((hU1 s).comp k (hc1 s)).const_mul (p s)
  exact hmax.hasDerivAt_eq_zero (((hU0.comp k hc0).add (hs.const_mul β)))

/-- A function homogeneous of degree one on `(0, ∞)` (`P(λk) = λP(k)`) has derivative
`P(k)/k` at every `k > 0`: marginal equals average. -/
theorem rx_homog_hasDerivAt {P : ℝ → ℝ} (hP : ∀ l k : ℝ, 0 < l → 0 < k → P (l * k) = l * P k)
    {k : ℝ} (hk : 0 < k) : HasDerivAt P (P k / k) k := by
  have h0 : HasDerivAt (fun x => x * (P k / k)) (1 * (P k / k)) k :=
    (hasDerivAt_id k).mul_const _
  rw [one_mul] at h0
  refine h0.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hk] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have := hP (x / k) k (div_pos hx0 hk) hk
  rw [div_mul_cancel₀ x hk.ne'] at this
  rw [this]
  field_simp

end Miao.NeoclassicalGrowth
