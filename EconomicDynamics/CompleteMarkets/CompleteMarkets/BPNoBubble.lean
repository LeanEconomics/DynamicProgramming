/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPBubbles
import Mathlib.Topology.Algebra.Order.Group

/-!
# No bubbles on assets in positive supply (Theorem 13.6.1)

Miao, §13.6, pp. 440–441, Theorem 13.6.1 (Santos and Woodford 1997) and its proof, equations
(13.20), (13.26) and (13.27), on the event tree of `BPTree` with finitely many agents `ι` and
stocks `J`.

* `BPRadnerEqm` (Definition 13.4.1, p. 427, with the debt constraints (13.13)): budget
  constraints (13.11) at every node, debt constraints, and market clearing
  `∑ᵢ θⁱ_t = θ̄_{−1}`, `∑ᵢ cⁱ_t = ȳ_t + θ̄_{−1}·d_t`. A concrete instance is
  `theorem_13_6_1_instance`.
* `bp_eq_13_20`: multiplying the date-`t` budget constraints by `π_t`, taking expectations and
  summing, `E ∑_{t≤T} π_t cⁱ_t + E π_T p_T·θⁱ_T ≤ π_0 p_0·θⁱ_{−1} + E ∑_{t≤T} π_t yⁱ_t`.
* `eq_13_26`: summing over agents and letting `T → ∞`,
  `∑ᵢ E ∑ π_t cⁱ_t + θ̄_{−1}·π_0 b_0 ≤ π_0 p_0·θ̄_{−1} + E ∑ π_t ȳ_t`, where
  `lim E π_T p_T = π_0 b_0` (`eq_13_6_bubble_limit`).
* `eq_13_27`: a bubble on an asset in positive supply makes this strict, so some agent has
  `E ∑ π_t cⁱ_t < π_0 p_0·θⁱ_{−1} + E ∑ π_t yⁱ_t` (`bp_exists_agent_slack`).
* `theorem_13_6_1`: if the present value of the aggregate endowment is finite, no asset in
  positive supply has a bubble, at any node.

**Departure.** The last step of the book's proof, "this contradicts agent `i`'s optimality",
uses that with complete markets the Radner consumption is optimal among consumption plans
satisfying the Arrow–Debreu budget (13.22) (Definition 13.4.2(ii), Theorem 13.5.1, §13.5) and
that preferences are strictly increasing. We state these two properties as hypotheses
(`hopt`, `hmono`) rather than deriving them from Radner optimality; §13.5 is formalised
separately. The book's hypothesis `E ∑_{t=0}^T π_t ȳ_t < ∞` is read as the convergence of
`∑_t E[π_t ȳ_t]`. Prices and dividends are nonnegative and supplies `θ̄_{−1}` nonnegative.
-/

open Filter Topology

namespace Miao.CompleteMarkets

variable {S ι J : Type*} [Fintype S] [Fintype ι] [Fintype J]
  (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ) (θ0 : ι → J → ℝ)
  (D : ι → List S → ℝ) in
/-- A Radner equilibrium with debt constraints (Miao, Definition 13.4.1, p. 427): the budget
constraints (13.11) (date 0: `cⁱ_0 + p_0·θⁱ_0 ≤ p_0·θⁱ_{−1} + yⁱ_0`), the debt constraints
(13.13) `f_{t+1}·θⁱ_t ≥ −D̄ⁱ_{t+1}` and market clearing. Optimality is imposed separately. -/
structure BPRadnerEqm where
  cons_nonneg : ∀ i h, 0 ≤ c i h
  budget_root : ∀ i, c i [] + ∑ j, p j [] * θ i j [] ≤ ∑ j, p j [] * θ0 i j + y i []
  budget_succ : ∀ i s h, c i (s :: h) + ∑ j, p j (s :: h) * θ i j (s :: h) ≤
      ∑ j, (p j (s :: h) + d j (s :: h)) * θ i j h + y i (s :: h)
  debt : ∀ i s h, -D i (s :: h) ≤ ∑ j, (p j (s :: h) + d j (s :: h)) * θ i j h
  clear_assets : ∀ j h, ∑ i, θ i j h = ∑ i, θ0 i j
  clear_goods_root : ∑ i, c i [] = ∑ i, y i []
  clear_goods_succ : ∀ s h,
      ∑ i, c i (s :: h) = ∑ i, y i (s :: h) + ∑ j, (∑ i, θ0 i j) * d j (s :: h)

variable {S ι J : Type*} [Fintype S] [Fintype ι] [Fintype J]

/-- `Pr(s^t) E_t[x_{t+1}] = ∑ₛ Pr(s^t, s) x(s^t, s)`. -/
theorem bp_pr_mul_condExp_one (T : BPTree S) (x : List S → ℝ) (h : List S) :
    T.pr h * bp_condExp T 1 x h = ∑ s, T.pr (s :: h) * x (s :: h) := by
  rw [bp_condExp_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [bp_condExp_zero]
  field_simp [(T.pr_pos h).ne']

theorem bp_nodeSum_succ_mono (t : ℕ) (f g : List S → ℝ)
    (hfg : ∀ s h, f (s :: h) ≤ g (s :: h)) : bp_nodeSum (t + 1) f ≤ bp_nodeSum (t + 1) g := by
  rw [bp_nodeSum_succ, bp_nodeSum_succ]
  exact bp_nodeSum_mono t _ _ (fun h => Finset.sum_le_sum (fun s _ => hfg s h))

/-- The deflated value of the date-`t+1` payoff of a date-`t` portfolio equals the deflated value
of its date-`t` cost (the pricing equation, summed over the date-`t` nodes). -/
theorem bp_pv_payoff (T : BPTree S) (δ : List S → ℝ) (p d : J → List S → ℝ)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (φ : J → List S → ℝ) (t : ℕ) :
    bp_nodeSum t (fun h => ∑ s, T.pr (s :: h) * δ (s :: h) *
        ∑ j, (p j (s :: h) + d j (s :: h)) * φ j h) =
      ∑ j, bp_pv T δ t (fun h => p j h * φ j h) := by
  unfold bp_pv
  rw [← bp_nodeSum_finsetSum]
  congr 1
  funext h
  have key : ∀ j, T.pr h * δ h * (p j h * φ j h) =
      (∑ s, T.pr (s :: h) * (δ (s :: h) * (p j (s :: h) + d j (s :: h)))) * φ j h := by
    intro j
    have hc := bp_pr_mul_condExp_one T (fun g => δ g * (p j g + d j g)) h
    rw [← hc, ← hP j h]
    ring
  simp only [key, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun s _ => ?_))
  ring

/-- Miao, (13.20), p. 432 (used in the proof of Theorem 13.6.1): for each agent,
`E ∑_{t≤T} π_t cⁱ_t + E π_T p_T·θⁱ_T ≤ π_0 p_0·θⁱ_{−1} + E ∑_{t≤T} π_t yⁱ_t`. -/
theorem bp_eq_13_20 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (i : ι) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) +
        ∑ j, bp_pv T δ n (fun h => p j h * θ i j h) ≤
      δ [] * ∑ j, p j [] * θ0 i j + ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one]
    unfold bp_pv
    simp only [bp_nodeSum_zero, T.pr_nil, one_mul]
    have := mul_le_mul_of_nonneg_left (hE.budget_root i) (hδ []).le
    rw [mul_add, mul_add] at this
    simp only [Finset.mul_sum] at this ⊢
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => bp_pv T δ t (y i))]
    have hstep : bp_pv T δ (n + 1) (c i) + ∑ j, bp_pv T δ (n + 1) (fun h => p j h * θ i j h) ≤
        ∑ j, bp_pv T δ n (fun h => p j h * θ i j h) + bp_pv T δ (n + 1) (y i) := by
      rw [← bp_pv_payoff T δ p d hP (θ i) n]
      have h1 : bp_pv T δ (n + 1) (c i) + ∑ j, bp_pv T δ (n + 1) (fun h => p j h * θ i j h) =
          bp_nodeSum (n + 1) (fun g => T.pr g * δ g *
            (c i g + ∑ j, p j g * θ i j g)) := by
        unfold bp_pv
        rw [← bp_nodeSum_finsetSum, ← bp_nodeSum_add]
        congr 1
        funext g
        rw [mul_add, Finset.mul_sum]
      have h2 : bp_nodeSum n (fun h => ∑ s, T.pr (s :: h) * δ (s :: h) *
            ∑ j, (p j (s :: h) + d j (s :: h)) * θ i j h) + bp_pv T δ (n + 1) (y i) =
          bp_nodeSum (n + 1) (fun g => T.pr g * δ g *
            (∑ j, (p j g + d j g) * θ i j g.tail + y i g)) := by
        unfold bp_pv
        rw [bp_nodeSum_succ, bp_nodeSum_succ, ← bp_nodeSum_add]
        congr 1
        funext h
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [List.tail_cons]
        ring
      rw [h1, h2]
      refine bp_nodeSum_succ_mono n _ _ (fun s h => ?_)
      exact mul_le_mul_of_nonneg_left (hE.budget_succ i s h)
        (mul_nonneg (T.pr_pos _).le (hδ _).le)
    linarith

/-- `E[π_T p_T] = E_0[π_T p_T]`, the quantity whose limit is `π_0 b_0`. -/
theorem bp_pv_price_root (T : BPTree S) (δ q : List S → ℝ) (n : ℕ) :
    bp_pv T δ n q = bp_condExp T n (fun g => δ g * q g) [] := by
  rw [bp_condExp_root]
  unfold bp_pv
  congr 1
  funext h
  ring

/-- The present value of an endowment bounded by a summable aggregate converges. -/
theorem bp_summable_pv_of_le (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (x z : List S → ℝ) (hx : ∀ h, 0 ≤ x h) (hxz : ∀ h, x h ≤ z h)
    (hz : Summable (fun t => bp_pv T δ t z)) : Summable (fun t => bp_pv T δ t x) :=
  Summable.of_nonneg_of_le (fun t => bp_pv_nonneg T δ (fun h => (hδ h).le) t x hx)
    (fun t => bp_pv_mono T δ (fun h => (hδ h).le) t x z hxz) hz

/-- Miao, (13.26), p. 441: summing (13.20) over agents and letting `T → ∞`,
`∑ᵢ E ∑ π_t cⁱ_t + θ̄_{−1}·π_0 b_0 ≤ π_0 p_0·θ̄_{−1} + ∑ᵢ E ∑ π_t yⁱ_t`. Also returns the
convergence of each agent's present value of consumption. -/
theorem eq_13_26 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h))) :
    (∀ i, Summable (fun t => bp_pv T δ t (c i))) ∧
    ∑ i, ∑' t, bp_pv T δ t (c i) +
        δ [] * ∑ j, (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [] ≤
      δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) := by
  have hyi : ∀ i, Summable (fun t => bp_pv T δ t (y i)) := fun i =>
    bp_summable_pv_of_le T δ hδ (y i) _ (hy i)
      (fun h => Finset.single_le_sum (fun k _ => hy k h) (Finset.mem_univ i)) hY
  -- the aggregate of (13.20)
  have hagg : ∀ n, ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) +
      ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j) ≤
      δ [] * ∑ j, p j [] * (∑ i, θ0 i j) +
        ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i) := by
    intro n
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      bp_eq_13_20 T δ hδ p d y c θ θ0 D hE hP i n)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hV : ∑ i, ∑ j, bp_pv T δ n (fun h => p j h * θ i j h) =
        ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← bp_pv_finsetSum]
      have : (fun h => ∑ i, p j h * θ i j h) = fun h => p j h * (∑ i, θ0 i j) := by
        funext h
        rw [← Finset.mul_sum, hE.clear_assets j h]
      rw [this]
      unfold bp_pv
      rw [← bp_nodeSum_smul]
      congr 1
      funext h
      ring
    have hW : ∑ i, δ [] * ∑ j, p j [] * θ0 i j = δ [] * ∑ j, p j [] * (∑ i, θ0 i j) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    linarith
  have hVnn : ∀ n, 0 ≤ ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j) := fun n =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hsupp j)
      (bp_pv_nonneg T δ (fun h => (hδ h).le) n (p j) (hp j)))
  set R := δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) with hR
  have hYle : ∀ n, ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i) ≤
      ∑ i, ∑' t, bp_pv T δ t (y i) := fun n =>
    Finset.sum_le_sum (fun i _ => (hyi i).sum_le_tsum _
      (fun t _ => bp_pv_nonneg T δ (fun h => (hδ h).le) t (y i) (hy i)))
  have hcnn : ∀ i t, 0 ≤ bp_pv T δ t (c i) := fun i t =>
    bp_pv_nonneg T δ (fun h => (hδ h).le) t (c i) (hE.cons_nonneg i)
  have hci : ∀ i, Summable (fun t => bp_pv T δ t (c i)) := by
    intro i
    refine summable_of_sum_range_le (c := R) (hcnn i) (fun n => ?_)
    have h1 : ∑ t ∈ Finset.range n, bp_pv T δ t (c i) ≤
        ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) := by
      rw [Finset.sum_range_succ]
      linarith [hcnn i n]
    have h2 : ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i) ≤
        ∑ k, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c k) :=
      Finset.single_le_sum (f := fun k => ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c k))
        (fun k _ => Finset.sum_nonneg (fun t _ => hcnn k t)) (Finset.mem_univ i)
    linarith [hagg n, hVnn n, hYle n]
  refine ⟨hci, ?_⟩
  have hlimC : Tendsto (fun n => ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (c i)) atTop
      (𝓝 (∑ i, ∑' t, bp_pv T δ t (c i))) :=
    tendsto_finsetSum _ (fun i _ =>
      (tendsto_add_atTop_iff_nat 1).2 (hci i).hasSum.tendsto_sum_nat)
  have hlimY : Tendsto (fun n => ∑ i, ∑ t ∈ Finset.range (n + 1), bp_pv T δ t (y i)) atTop
      (𝓝 (∑ i, ∑' t, bp_pv T δ t (y i))) :=
    tendsto_finsetSum _ (fun i _ =>
      (tendsto_add_atTop_iff_nat 1).2 (hyi i).hasSum.tendsto_sum_nat)
  have hlimV : Tendsto (fun n => ∑ j, (∑ i, θ0 i j) * bp_pv T δ n (p j)) atTop
      (𝓝 (δ [] * ∑ j, (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [])) := by
    rw [Finset.mul_sum]
    refine tendsto_finsetSum _ (fun j _ => ?_)
    have hb := eq_13_6_bubble_limit T δ (p j) (d j) hδ (hp j) (hd j) (hP j) []
    have hb' := hb.const_mul (δ [])
    have heq : (fun n => δ [] * (1 / δ [] * bp_condExp T n (fun g => δ g * p j g) [])) =
        fun n => bp_pv T δ n (p j) := by
      funext n
      rw [bp_pv_price_root]
      field_simp [(hδ []).ne']
    rw [heq] at hb'
    have := hb'.const_mul (∑ i, θ0 i j)
    convert this using 2
    ring
  exact le_of_tendsto_of_tendsto' (hlimC.add hlimV) (tendsto_const_nhds.add hlimY) hagg

/-- Miao, (13.27), p. 441: if some asset in positive supply has a bubble, (13.26) is strict:
`∑ᵢ E ∑ π_t cⁱ_t < π_0 p_0·θ̄_{−1} + ∑ᵢ E ∑ π_t yⁱ_t`. -/
theorem eq_13_27 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h)))
    (j₀ : J) (hj₀ : 0 < ∑ i, θ0 i j₀) (hb : 0 < bp_bubble T δ (p j₀) (d j₀) []) :
    ∑ i, ∑' t, bp_pv T δ t (c i) <
      δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) := by
  have h26 := (eq_13_26 T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY).2
  have hpos : 0 < δ [] * ∑ j, (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [] := by
    refine mul_pos (hδ []) ?_
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (∑ i, θ0 i j) * bp_bubble T δ (p j) (d j) [] :=
      fun j _ => mul_nonneg (hsupp j)
        (eq_13_6_bubble_bounds T δ (p j) (d j) hδ (hp j) (hd j) (hP j) []).1
    exact lt_of_lt_of_le (mul_pos hj₀ hb) (Finset.single_le_sum hnn (Finset.mem_univ j₀))
  linarith

/-- Miao, p. 441: "this means that for at least one agent `i`,
`E ∑ π_t cⁱ_t < π_0 p_0·θⁱ_{−1} + E ∑ π_t yⁱ_t`". -/
theorem bp_exists_agent_slack (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h)))
    (j₀ : J) (hj₀ : 0 < ∑ i, θ0 i j₀) (hb : 0 < bp_bubble T δ (p j₀) (d j₀) []) :
    ∃ i, ∑' t, bp_pv T δ t (c i) <
      δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i) := by
  have h27 := eq_13_27 T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY j₀ hj₀ hb
  have hW : δ [] * ∑ j, p j [] * (∑ i, θ0 i j) + ∑ i, ∑' t, bp_pv T δ t (y i) =
      ∑ i, (δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hW] at h27
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt h27
  exact ⟨i, hi⟩

/-- **Theorem 13.6.1** (Santos–Woodford, Miao, p. 440). Let `p` be a Radner equilibrium price
system under debt constraints, with complete markets and state price deflator `π`. If the
present value of the aggregate endowment is finite, there is no bubble on any asset in positive
supply. Optimality is used through the Arrow–Debreu budget (13.22): each agent's consumption is
best among plans `x ≥ 0` with `E ∑ π_t x_t ≤ π_0 p_0·θⁱ_{−1} + E ∑ π_t yⁱ_t` (`hopt`), and
preferences strictly increase with date-0 consumption (`hmono`). -/
theorem theorem_13_6_1 (T : BPTree S) (δ : List S → ℝ) (hδ : ∀ h, 0 < δ h)
    (p d : J → List S → ℝ) (y c : ι → List S → ℝ) (θ : ι → J → List S → ℝ)
    (θ0 : ι → J → ℝ) (D : ι → List S → ℝ) (hE : BPRadnerEqm p d y c θ θ0 D)
    (hP : ∀ j, bp_Prices T δ (p j) (d j)) (hp : ∀ j h, 0 ≤ p j h) (hd : ∀ j h, 0 ≤ d j h)
    (hy : ∀ i h, 0 ≤ y i h) (hsupp : ∀ j, 0 ≤ ∑ i, θ0 i j)
    (hY : Summable (fun t => bp_pv T δ t (fun h => ∑ i, y i h)))
    (U : ι → (List S → ℝ) → ℝ)
    (hopt : ∀ i (x : List S → ℝ), (∀ h, 0 ≤ x h) → Summable (fun t => bp_pv T δ t x) →
      ∑' t, bp_pv T δ t x ≤ δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i) →
      U i x ≤ U i (c i))
    (hmono : ∀ i (x : List S → ℝ) (ε : ℝ), 0 < ε →
      U i x < U i (fun h => x h + if h = [] then ε else 0))
    (j : J) (hj : 0 < ∑ i, θ0 i j) (h : List S) : bp_bubble T δ (p j) (d j) h = 0 := by
  have hb0 := (eq_13_6_bubble_bounds T δ (p j) (d j) hδ (hp j) (hd j) (hP j) []).1
  refine bp_bubble_eq_zero_of_root T δ (p j) (d j) hδ (hp j) (hd j) (hP j) ?_ h
  by_contra hne
  have hb : 0 < bp_bubble T δ (p j) (d j) [] := lt_of_le_of_ne hb0 (Ne.symm hne)
  obtain ⟨i, hi⟩ := bp_exists_agent_slack T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY j hj hb
  have hci := (eq_13_26 T δ hδ p d y c θ θ0 D hE hP hp hd hy hsupp hY).1 i
  set W := δ [] * ∑ j, p j [] * θ0 i j + ∑' t, bp_pv T δ t (y i) with hW
  set C := ∑' t, bp_pv T δ t (c i) with hC
  set ε := (W - C) / δ [] with hε
  have hεpos : 0 < ε := div_pos (by linarith) (hδ [])
  set x : List S → ℝ := fun g => c i g + if g = [] then ε else 0 with hx
  have hpvx : ∀ t, bp_pv T δ t x = bp_pv T δ t (c i) + if t = 0 then W - C else 0 := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      unfold bp_pv
      simp only [bp_nodeSum_zero, T.pr_nil, one_mul, hx, ↓reduceIte, hε]
      field_simp [(hδ []).ne']
    · have hne : t ≠ 0 := ht.ne'
      simp only [hne, ↓reduceIte, add_zero]
      unfold bp_pv
      refine bp_nodeSum_congr t _ _ (fun g hg => ?_)
      have : g ≠ [] := by
        intro hg0
        rw [hg0] at hg
        exact hne hg.symm
      simp [hx, this]
  have hsx : HasSum (fun t => bp_pv T δ t x) (C + (W - C)) := by
    have h1 := (hci.hasSum).add (hasSum_ite_eq 0 (W - C))
    convert h1 using 1
    funext t
    rw [hpvx]
  have hxnn : ∀ g, 0 ≤ x g := by
    intro g
    have := hE.cons_nonneg i g
    by_cases hg : g = []
    · subst hg
      simp only [hx, ↓reduceIte]
      linarith
    · simp only [hx, hg, ↓reduceIte, add_zero]
      exact this
  have hle := hopt i x hxnn hsx.summable (by rw [hsx.tsum_eq]; linarith)
  have hlt := hmono i (c i) ε hεpos
  exact absurd hle (not_le.2 hlt)

/-- A concrete Radner equilibrium (`BPRadnerEqm`) in which every hypothesis of Theorem 13.6.1
holds, including `hopt` and `hmono`: one agent, one share of a stock in positive supply that pays
nothing and costs nothing, endowment `1` at the root and `0` afterwards, `π = 1` and the utility
`U(x) = x_0`. -/
theorem theorem_13_6_1_instance :
    BPRadnerEqm (S := Unit) (ι := Unit) (J := Unit) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ h => if h = [] then 1 else 0) (fun _ h => if h = [] then 1 else 0)
      (fun _ _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) ∧
    (∀ _j : Unit, bp_Prices bp_detTree (fun _ => 1) (fun _ => 0) (fun _ => 0)) ∧
    Summable (fun t => bp_pv bp_detTree (fun _ => 1) t
      (fun h => ∑ _i : Unit, if h = [] then (1 : ℝ) else 0)) ∧
    (∀ (_i : Unit) (x : List Unit → ℝ), (∀ h, 0 ≤ x h) →
      Summable (fun t => bp_pv bp_detTree (fun _ => 1) t x) →
      ∑' t, bp_pv bp_detTree (fun _ => 1) t x ≤
        1 * ∑ _j : Unit, (0 : ℝ) * 1 + ∑' t, bp_pv bp_detTree (fun _ => 1) t
          (fun h => if h = [] then 1 else 0) →
      x [] ≤ (fun h : List Unit => if h = [] then (1 : ℝ) else 0) []) ∧
    (∀ (_i : Unit) (x : List Unit → ℝ) (ε : ℝ), 0 < ε →
      x [] < (fun h => x h + if h = [] then ε else 0) []) := by
  have hpvY : ∀ t, bp_pv bp_detTree (fun _ => 1) t (fun h => if h = [] then (1 : ℝ) else 0) =
      if t = 0 then 1 else 0 := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      simp [bp_pv, bp_nodeSum_zero, bp_detTree]
    · have hne : t ≠ 0 := ht.ne'
      simp only [hne, ↓reduceIte]
      unfold bp_pv
      rw [bp_nodeSum_congr t _ (fun _ => 0) (fun g hg => by
        have : g ≠ [] := by
          intro hg0
          rw [hg0] at hg
          exact hne hg.symm
        simp [this])]
      simpa using bp_nodeSum_smul t 0 (fun _ : List Unit => (0 : ℝ))
  have hsY : HasSum (fun t => bp_pv bp_detTree (fun _ => 1) t
      (fun h => if h = [] then (1 : ℝ) else 0)) 1 := by
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
    funext t
    rw [hpvY]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i h
    split_ifs <;> norm_num
  · intro i
    simp
  · intro i s h
    simp
  · intro i s h
    simp
  · intro j h
    simp
  · simp
  · intro s h
    simp
  · intro j h
    simp only [add_zero, mul_zero]
    exact (bp_condExp_const bp_detTree 1 0 h).symm
  · simpa using hsY.summable
  · intro i x hx hsx hle
    rw [hsY.tsum_eq] at hle
    have h0 : bp_pv bp_detTree (fun _ => 1) 0 x ≤ ∑' t, bp_pv bp_detTree (fun _ => 1) t x :=
      hsx.le_tsum 0 (fun t _ => bp_pv_nonneg bp_detTree _ (fun _ => zero_le_one) t x hx)
    have hx0 : bp_pv bp_detTree (fun _ => 1) 0 x = x [] := by
      simp [bp_pv, bp_nodeSum_zero, bp_detTree]
    simp only [↓reduceIte]
    simp at hle
    linarith
  · intro i x ε hε
    simp only [↓reduceIte]
    linarith

end Miao.CompleteMarkets
