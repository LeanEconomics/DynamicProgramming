/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPTree
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic

/-!
# Fundamental values and bubbles

Miao, §13.6, pp. 439–440. A stock with ex-dividend price `p` and dividends `d` on the event tree
of `BPTree`, priced by a state price deflator `δ > 0` (the book's `π`):
`p_t = (1/π_t) E_t[π_{t+1}(p_{t+1} + d_{t+1})]` (`bp_Prices`).

* `eq_13_6_forward` (p. 439): repeated substitution,
  `p_t = (1/π_t) ∑_{j=1}^T E_t[π_{t+j} d_{t+j}] + (1/π_t) E_t[π_{t+T} p_{t+T}]`.
* `bp_fundamental` (p. 440): the fundamental value `v_t(d) = (1/π_t) ∑_{j≥1} E_t[π_{t+j} d_{t+j}]`;
  `bp_bubble`: `b_t = p_t − v_t(d)`. For `p, d ≥ 0` the series converges
  (`bp_summable_dividends`), since its partial sums are at most `p_t`.
* `eq_13_6_bubble_limit`: `b_t = lim_T (1/π_t) E_t[π_{t+T} p_{t+T}]`.
* `eq_13_6_bubble_bounds`: `0 ≤ b_t ≤ p_t`.
* `bp_no_bubble_finite_maturity` (p. 439): an asset with finite maturity has no bubble.
* `eq_13_25`: the discounted martingale property `b_t = (1/π_t) E_t[π_{t+1} b_{t+1}]`, with its
  iterate `eq_13_25_iterate` and the consequence that a bubble vanishing at the root vanishes at
  every node (`bp_bubble_eq_zero_of_root`). The fundamental value itself solves the pricing
  equation (`bp_fundamental_prices`).

**Correction.** The book states `0 < b_t ≤ p_t`. The strict inequality is false: an asset priced
at its fundamental value has `b_t = 0` (`eq_13_6_bubble_pos_counterexample`). What is true is
`0 ≤ b_t ≤ p_t` (`eq_13_6_bubble_bounds`).
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- The no-arbitrage pricing equation of the stock (Miao, p. 439):
`π_t p_t = E_t[π_{t+1}(p_{t+1} + d_{t+1})]` at every node. -/
def bp_Prices {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ) : Prop :=
  ∀ h, δ h * p h = bp_condExp T 1 (fun g => δ g * (p g + d g)) h

/-- The fundamental value `v_t(d) = (1/π_t) ∑_{j ≥ 1} E_t[π_{t+j} d_{t+j}]` (Miao, p. 440). -/
noncomputable def bp_fundamental {S : Type*} [Fintype S] (T : BPTree S) (δ d : List S → ℝ)
    (h : List S) : ℝ :=
  1 / δ h * ∑' j, bp_condExp T (j + 1) (fun g => δ g * d g) h

/-- The bubble `b_t = p_t − v_t(d)` (Miao, p. 440). -/
noncomputable def bp_bubble {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (h : List S) : ℝ :=
  p h - bp_fundamental T δ d h

/-- The forward-iterated pricing equation, multiplied through by `π_t`. -/
theorem bp_forward_mul {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hP : bp_Prices T δ p d) (n : ℕ) (h : List S) :
    δ h * p h = ∑ j ∈ Finset.range n, bp_condExp T (j + 1) (fun g => δ g * d g) h +
      bp_condExp T n (fun g => δ g * p g) h := by
  induction n generalizing h with
  | zero => simp [bp_condExp_zero]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ]
    have h1 : bp_condExp T n (fun g => δ g * p g) h =
        bp_condExp T n (bp_condExp T 1 (fun g => δ g * (p g + d g))) h :=
      bp_condExp_congr T n _ _ (fun g => hP g) h
    rw [h1, ← bp_condExp_add]
    have h2 : bp_condExp T (n + 1) (fun g => δ g * (p g + d g)) h =
        bp_condExp T (n + 1) (fun g => δ g * d g) h +
          bp_condExp T (n + 1) (fun g => δ g * p g) h := by
      rw [← bp_condExp_add_fun]
      exact bp_condExp_congr T _ _ _ (fun g => by ring) h
    rw [h2]
    ring

/-- Miao, p. 439: solving the pricing equation forward by repeated substitution,
`p_t = (1/π_t) ∑_{j=1}^T E_t[π_{t+j} d_{t+j}] + (1/π_t) E_t[π_{t+T} p_{t+T}]`. -/
theorem eq_13_6_forward {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hP : bp_Prices T δ p d) (n : ℕ) (h : List S) :
    p h = 1 / δ h * ∑ j ∈ Finset.range n, bp_condExp T (j + 1) (fun g => δ g * d g) h +
      1 / δ h * bp_condExp T n (fun g => δ g * p g) h := by
  have := bp_forward_mul T δ p d hP n h
  have hne := (hδ h).ne'
  rw [← mul_add, ← this]
  field_simp

/-- For a nonnegative price and dividend, the series defining the fundamental value converges:
its partial sums are bounded by `π_t p_t`. -/
theorem bp_summable_dividends {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) : Summable (fun j => bp_condExp T (j + 1) (fun g => δ g * d g) h) := by
  refine summable_of_sum_range_le (c := δ h * p h)
    (fun j => bp_condExp_nonneg T _ _ (fun g => mul_nonneg (hδ g).le (hd g)) h) (fun n => ?_)
  rw [bp_forward_mul T δ p d hP n h]
  have := bp_condExp_nonneg T n (fun g => δ g * p g) (fun g => mul_nonneg (hδ g).le (hp g)) h
  linarith

/-- `π_t v_t(d)` is the sum of the discounted expected dividends. -/
theorem bp_mul_fundamental {S : Type*} [Fintype S] (T : BPTree S) (δ d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (h : List S) :
    δ h * bp_fundamental T δ d h = ∑' j, bp_condExp T (j + 1) (fun g => δ g * d g) h := by
  unfold bp_fundamental
  have := (hδ h).ne'
  field_simp

/-- Miao, p. 440: the bubble is the limit of the discounted expected resale value,
`b_t = lim_{T→∞} (1/π_t) E_t[π_{t+T} p_{t+T}]`. -/
theorem eq_13_6_bubble_limit {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) :
    Tendsto (fun n => 1 / δ h * bp_condExp T n (fun g => δ g * p g) h) atTop
      (𝓝 (bp_bubble T δ p d h)) := by
  have hs := (bp_summable_dividends T δ p d hδ hp hd hP h).hasSum.tendsto_sum_nat
  have hlim := (hs.const_mul (1 / δ h)).const_sub (p h)
  have heq : (fun n => 1 / δ h * bp_condExp T n (fun g => δ g * p g) h) =
      fun n => p h - 1 / δ h *
        ∑ j ∈ Finset.range n, bp_condExp T (j + 1) (fun g => δ g * d g) h := by
    funext n
    rw [eq_13_6_forward T δ p d hδ hP n h]
    ring
  rw [heq]
  exact hlim

/-- Miao, p. 440 (corrected): `0 ≤ b_t ≤ p_t`. The book's `0 < b_t` is false
(`eq_13_6_bubble_pos_counterexample`). -/
theorem eq_13_6_bubble_bounds {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) : 0 ≤ bp_bubble T δ p d h ∧ bp_bubble T δ p d h ≤ p h := by
  constructor
  · refine ge_of_tendsto' (eq_13_6_bubble_limit T δ p d hδ hp hd hP h) (fun n => ?_)
    exact mul_nonneg (one_div_nonneg.2 (hδ h).le)
      (bp_condExp_nonneg T n _ (fun g => mul_nonneg (hδ g).le (hp g)) h)
  · unfold bp_bubble
    have : 0 ≤ bp_fundamental T δ d h := by
      unfold bp_fundamental
      exact mul_nonneg (one_div_nonneg.2 (hδ h).le) (tsum_nonneg (fun j =>
        bp_condExp_nonneg T _ _ (fun g => mul_nonneg (hδ g).le (hd g)) h))
    linarith

/-- Counterexample to `0 < b_t` (Miao, p. 440): on the deterministic tree with `π = 1` the asset
with zero dividends and zero price satisfies the pricing equation and has no bubble. -/
theorem eq_13_6_bubble_pos_counterexample :
    bp_Prices bp_detTree (fun _ => 1) (fun _ => 0) (fun _ => 0) ∧
      ¬ 0 < bp_bubble bp_detTree (fun _ => 1) (fun _ => 0) (fun _ => 0) [] := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [add_zero, mul_zero]
    exact (bp_condExp_const bp_detTree 1 0 h).symm
  · have : bp_bubble bp_detTree (fun _ => (1 : ℝ)) (fun _ => 0) (fun _ => 0) [] = 0 := by
      unfold bp_bubble bp_fundamental
      simp only [mul_zero]
      simp [bp_condExp_const]
    rw [this]
    exact lt_irrefl 0

/-- The fundamental value solves the pricing equation:
`π_t v_t = E_t[π_{t+1}(v_{t+1} + d_{t+1})]`. -/
theorem bp_fundamental_prices {S : Type*} [Fintype S] (T : BPTree S) (δ d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h)
    (hsum : ∀ h, Summable (fun j => bp_condExp T (j + 1) (fun g => δ g * d g) h)) :
    bp_Prices T δ (bp_fundamental T δ d) d := by
  intro h
  set a : ℕ → List S → ℝ := fun j g => bp_condExp T (j + 1) (fun g => δ g * d g) g with ha
  rw [bp_mul_fundamental T δ d hδ h]
  have hrhs : bp_condExp T 1 (fun g => δ g * (bp_fundamental T δ d g + d g)) h =
      ∑ s, T.pr (s :: h) / T.pr h * (δ (s :: h) * d (s :: h)) +
        ∑ s, T.pr (s :: h) / T.pr h * ∑' j, a j (s :: h) := by
    rw [bp_condExp_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [bp_condExp_zero, mul_add, bp_mul_fundamental T δ d hδ (s :: h)]
    ring
  rw [hrhs]
  have hswap : ∑ s, T.pr (s :: h) / T.pr h * ∑' j, a j (s :: h) =
      ∑' j, a (j + 1) h := by
    have h1 : ∀ s, T.pr (s :: h) / T.pr h * ∑' j, a j (s :: h) =
        ∑' j, T.pr (s :: h) / T.pr h * a j (s :: h) :=
      fun s => ((hsum (s :: h)).tsum_mul_left _).symm
    simp only [h1]
    rw [← Summable.tsum_finsetSum (fun s _ => (hsum (s :: h)).mul_left _)]
    rfl
  rw [hswap, (hsum h).tsum_eq_zero_add]
  congr 1

/-- Miao, (13.25), p. 440: the bubble has the discounted martingale property
`b_t = (1/π_t) E_t[π_{t+1} b_{t+1}]`, stated multiplied through by `π_t`. -/
theorem eq_13_25 {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h : List S) :
    δ h * bp_bubble T δ p d h = bp_condExp T 1 (fun g => δ g * bp_bubble T δ p d g) h := by
  have hF := bp_fundamental_prices T δ d hδ (bp_summable_dividends T δ p d hδ hp hd hP) h
  have hb : (fun g => δ g * bp_bubble T δ p d g) =
      fun g => δ g * (p g + d g) - δ g * (bp_fundamental T δ d g + d g) := by
    funext g
    unfold bp_bubble
    ring
  rw [hb, bp_condExp_sub_fun, ← hP h, ← hF]
  unfold bp_bubble
  ring

/-- Iterating (13.25): `π_t b_t = E_t[π_{t+k} b_{t+k}]` for every `k`. -/
theorem eq_13_25_iterate {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (k : ℕ) (h : List S) :
    δ h * bp_bubble T δ p d h = bp_condExp T k (fun g => δ g * bp_bubble T δ p d g) h := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [show k + 1 = 1 + k by omega, bp_condExp_add, eq_13_25 T δ p d hδ hp hd hP h]
    exact bp_condExp_congr T 1 _ _ (fun g => ih g) h

/-- A bubble that vanishes at the root vanishes at every node (`b ≥ 0`, (13.25)). -/
theorem bp_bubble_eq_zero_of_root {S : Type*} [Fintype S] (T : BPTree S) (δ p d : List S → ℝ)
    (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h) (hP : bp_Prices T δ p d)
    (h0 : bp_bubble T δ p d [] = 0) (h : List S) : bp_bubble T δ p d h = 0 := by
  have hit := eq_13_25_iterate T δ p d hδ hp hd hP h.length []
  rw [h0, mul_zero, bp_condExp_root] at hit
  have hnn : ∀ g, 0 ≤ T.pr g * (δ g * bp_bubble T δ p d g) := fun g =>
    mul_nonneg (T.pr_pos g).le
      (mul_nonneg (hδ g).le (eq_13_6_bubble_bounds T δ p d hδ hp hd hP g).1)
  have := bp_nodeSum_eq_zero_iff h.length _ hnn hit.symm h rfl
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (T.pr_pos h).ne'
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (hδ h).ne'
    · exact h2

/-- `E_t[x_{t+n}]` at `h` only depends on `x` at the nodes of length `|h| + n`. -/
theorem bp_condExp_congr_length {S : Type*} [Fintype S] (T : BPTree S) (n : ℕ)
    (x y : List S → ℝ) (h : List S)
    (hxy : ∀ g : List S, g.length = h.length + n → x g = y g) :
    bp_condExp T n x h = bp_condExp T n y h := by
  induction n generalizing h with
  | zero => exact hxy h (by simp)
  | succ n ih =>
    simp only [bp_condExp_succ]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [ih (s :: h) (fun g hg => hxy g (by simp at hg; omega))]

/-- Miao, p. 439: "by backward induction, there is no bubble on assets with finite maturity".
If the asset has no value from date `N` on (`p_t = 0` for `t ≥ N`), its bubble is zero at every
node. -/
theorem bp_no_bubble_finite_maturity {S : Type*} [Fintype S] (T : BPTree S)
    (δ p d : List S → ℝ) (hδ : ∀ h, 0 < δ h) (hp : ∀ h, 0 ≤ p h) (hd : ∀ h, 0 ≤ d h)
    (hP : bp_Prices T δ p d) (N : ℕ) (hN : ∀ g : List S, N ≤ g.length → p g = 0)
    (h : List S) : bp_bubble T δ p d h = 0 := by
  have hlim := eq_13_6_bubble_limit T δ p d hδ hp hd hP h
  have hev : ∀ n, N ≤ n → 1 / δ h * bp_condExp T n (fun g => δ g * p g) h = 0 := by
    intro n hn
    rw [bp_condExp_congr_length T n _ (fun _ => 0) h (fun g hg => by
      rw [hN g (by omega), mul_zero]), bp_condExp_const, mul_zero]
  have h0 : Tendsto (fun n => 1 / δ h * bp_condExp T n (fun g => δ g * p g) h) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hev n hn).symm)
  exact tendsto_nhds_unique hlim h0

end Miao.CompleteMarkets
