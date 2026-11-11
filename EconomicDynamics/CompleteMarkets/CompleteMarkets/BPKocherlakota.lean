/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPDeterministic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bubbles on assets in zero supply (Kocherlakota 1992)

Miao, §13.6, Example 13.6.1 (pp. 441–442), and §13.9, Exercises 13.5 and 13.6 (p. 453), in the
deterministic one-asset economy of `BPDeterministic`. `δ` is the state price deflator (the
book's `π`), `bp_natLimit δ y t = (1/π_t) ∑_{s>t} π_s y_s` the natural borrowing limit and
`bp_borrowCon B` the borrowing constraint `p_t θ_t ≥ −B_t` (13.14).

* `example_13_6_1`: if `(c, θ, p)` is an equilibrium with borrowing constraints, all initial
  holdings are zero and `π_t p_t = π_{t+1}(p_{t+1} + d_{t+1})`, then for every `η ≥ 0`,
  `(c, θ̂, p̂)` with `p̂_t = p_t + η/π_t`, `θ̂_t = θ_t p_t/p̂_t` is an equilibrium with the same
  borrowing limits. The text's derivations: `π_t/π_{t+1} = (p̂_{t+1} + d_{t+1})/p̂_t`, identical
  budget constraints (`bp_budget_transfer`), identical borrowing constraints, and identical
  transversality terms `π_t p̂_t θ̂_t = π_t p_t θ_t` (`example_13_6_1_tvc`). The bubble is `η/π_t`
  (`example_13_6_1_bubble`).
* `ex_13_5`: CRRA utilities, an asset in zero supply: for every admissible `η ≥ 0` the book's
  allocation, prices and portfolios form an equilibrium with natural borrowing constraints;
  `ex_13_5_continuum`: the prices differ for different `η`.
* `ex_13_6`: the special case `θ_{−1} = 0`, `d = 0`, `η > 0`, with the book's formulas
  `q_t = η/π_t`, `θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s)/(π_t q_t)` (`ex_13_6_formulas`);
  `ex_13_6_autarky`: the equilibrium with `q = 0`; `ex_13_6_pareto`: the allocation `sⁱ Y_t` is
  Pareto optimal.

**Corrections.**
* Example 13.6.1 needs `p_t > 0`. With `p_t = 0` (no dividends) the original economy has no
  trade while `p̂` permits trade, and the budget sets differ; the book's
  `p_t = (1/π_t)∑_{s>t} π_s d_s` is positive when dividends are positive.
* Exercise 13.5, initial wealth: the bracket `θⁱ_{−1}(q_0 + d_0 + η)` counts `η` twice when `q_0`
  is the equilibrium price (which already contains `η/π_0 = η`). The date-0 wealth is
  `θⁱ_{−1}(q_0 + d_0) = θⁱ_{−1}(∑_{s≥0} π_s d_s + η)`, which is what `bp_k5_wealth` uses.
* Exercise 13.5, "a continuum of equilibria indexed by `η ≥ 0`": false for large `η` when some
  agent has `θⁱ_{−1} < 0` (which zero supply and `θ_{−1} ≠ 0` force): `sⁱ(η)` falls below zero
  and the consumption `sⁱ(η) ȳ_t` is infeasible (`ex_13_5_share_counterexample`). The statement
  holds for the `η` with `sⁱ(η) > 0` for all `i` (`ex_13_5`).
* Exercise 13.5 also needs `q_t > 0` (true when `η > 0` or dividends are positive) for
  `θⁱ_t = …/(π_t q_t)` to be defined, and the present values `∑ π_t ȳ_t`, `∑ π_t d_t` finite.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- The natural borrowing limit `B_t = (1/π_t) ∑_{s>t} π_s y_s` (Miao, p. 434). -/
noncomputable def bp_natLimit (δ y : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 / δ t * bp_tail (fun s => δ s * y s) t

/-- The borrowing constraint `p_t θ_t ≥ −B_t` (Miao, (13.14)). -/
def bp_borrowCon (B : ℕ → ℝ) : ℕ → ℝ → ℝ → Prop := fun t z x => -B t ≤ z * x

/-- The CRRA utility `c^{1−γ}/(1−γ)`. -/
noncomputable def bp_crra (γ x : ℝ) : ℝ := x ^ (1 - γ) / (1 - γ)

/-- Two price systems priced by the same deflator, and two portfolios of equal value
`p_t a_t = q_t b_t`, give the same payoffs `(p_{t+1} + d_{t+1}) a_t = (q_{t+1} + d_{t+1}) b_t`. -/
theorem bp_payoff_eq (δ p q d a b : ℕ → ℝ) (hδ : ∀ t, 0 < δ t)
    (hp : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1)))
    (hq : ∀ t, δ t * q t = δ (t + 1) * (q (t + 1) + d (t + 1)))
    (hval : ∀ t, p t * a t = q t * b t) (t : ℕ) :
    (p (t + 1) + d (t + 1)) * a t = (q (t + 1) + d (t + 1)) * b t := by
  have h1 : δ (t + 1) * ((p (t + 1) + d (t + 1)) * a t) =
      δ (t + 1) * ((q (t + 1) + d (t + 1)) * b t) := by
    rw [← mul_assoc, ← hp t, ← mul_assoc, ← hq t, mul_assoc, hval t, mul_assoc]
  exact mul_left_cancel₀ (hδ (t + 1)).ne' h1

/-- Miao, p. 442: with zero initial holdings and portfolios of equal value, the budget
constraints and the borrowing constraints under `p` and under `q` coincide. -/
theorem bp_budget_transfer (δ p q d y B : ℕ → ℝ) (hδ : ∀ t, 0 < δ t)
    (hp : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1)))
    (hq : ∀ t, δ t * q t = δ (t + 1) * (q (t + 1) + d (t + 1)))
    (c a b : ℕ → ℝ) (hval : ∀ t, p t * a t = q t * b t) :
    bp_detBudget p d y 0 (bp_borrowCon B) c a ↔ bp_detBudget q d y 0 (bp_borrowCon B) c b := by
  have hpay := bp_payoff_eq δ p q d a b hδ hp hq hval
  unfold bp_detBudget bp_borrowCon
  simp only [mul_zero, hval, hpay]

/-- The bubbly price `p̂_t = p_t + η/π_t` of Example 13.6.1. -/
noncomputable def bp_ex1361_price (δ p : ℕ → ℝ) (η : ℝ) (t : ℕ) : ℝ := p t + η / δ t

/-- The rescaled portfolio `θ̂_t = θ_t p_t / p̂_t` of Example 13.6.1. -/
noncomputable def bp_ex1361_hold (δ p : ℕ → ℝ) (η : ℝ) (θ : ℕ → ℝ) (t : ℕ) : ℝ :=
  θ t * p t / bp_ex1361_price δ p η t

theorem bp_ex1361_price_pos (δ p : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hη : 0 ≤ η) (t : ℕ) : 0 < bp_ex1361_price δ p η t := by
  unfold bp_ex1361_price
  have := div_nonneg hη (hδ t).le
  linarith [hp t]

/-- Miao, p. 442: `p̂` is priced by the same deflator,
`π_t/π_{t+1} = (p̂_{t+1} + d_{t+1})/p̂_t`, in the form `π_t p̂_t = π_{t+1}(p̂_{t+1} + d_{t+1})`. -/
theorem example_13_6_1_prices (δ p d : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t)
    (hpr : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1))) (t : ℕ) :
    δ t * bp_ex1361_price δ p η t =
      δ (t + 1) * (bp_ex1361_price δ p η (t + 1) + d (t + 1)) := by
  unfold bp_ex1361_price
  have h1 := (hδ t).ne'
  have h2 := (hδ (t + 1)).ne'
  have e1 : δ t * (p t + η / δ t) = δ t * p t + η := by field_simp
  have e2 : δ (t + 1) * (p (t + 1) + η / δ (t + 1) + d (t + 1)) =
      δ (t + 1) * (p (t + 1) + d (t + 1)) + η := by field_simp; ring
  rw [e1, e2, hpr t]

/-- Value preservation `p̂_t θ̂_t = p_t θ_t`. -/
theorem bp_ex1361_value (δ p : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hη : 0 ≤ η) (θ : ℕ → ℝ) (t : ℕ) :
    p t * θ t = bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t := by
  unfold bp_ex1361_hold
  have := (bp_ex1361_price_pos δ p η hδ hp hη t).ne'
  field_simp

/-- **Example 13.6.1** (Kocherlakota 1992, Miao, pp. 441–442). If `(c, θ, p)` is an equilibrium
with borrowing constraints `p_tθⁱ_t ≥ −Bⁱ_t`, zero initial holdings, a positive price priced by
the deflator `π`, then for every `η ≥ 0` the consumption `c`, the portfolios `θ̂ = θp/p̂` and the
prices `p̂ = p + η/π` form an equilibrium with the same borrowing limits. -/
theorem example_13_6_1 {ι : Type*} [Fintype ι] (U : ι → (ℕ → ℝ) → ℝ)
    (adm : ι → (ℕ → ℝ) → Prop) (y : ι → ℕ → ℝ) (d : ℕ → ℝ) (B : ι → ℕ → ℝ)
    (c θ : ι → ℕ → ℝ) (p δ : ℕ → ℝ) (η : ℝ)
    (hE : BPDetEqm U adm y d (fun _ => 0) (fun i => bp_borrowCon (B i)) c θ p)
    (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hpr : ∀ t, δ t * p t = δ (t + 1) * (p (t + 1) + d (t + 1))) (hη : 0 ≤ η) :
    BPDetEqm U adm y d (fun _ => 0) (fun i => bp_borrowCon (B i)) c
      (fun i => bp_ex1361_hold δ p η (θ i)) (bp_ex1361_price δ p η) := by
  have hq := example_13_6_1_prices δ p d η hδ hpr
  have hqpos := bp_ex1361_price_pos δ p η hδ hp hη
  refine ⟨fun i => ?_, hE.adm_self, fun i c' θ' hb hadm => ?_, fun t => ?_, fun t => ?_⟩
  · exact (bp_budget_transfer δ p _ d (y i) (B i) hδ hpr hq (c i) (θ i) _
      (bp_ex1361_value δ p η hδ hp hη (θ i))).1 (hE.budget i)
  · -- pull the deviation back to the original prices
    set θo : ℕ → ℝ := fun t => θ' t * bp_ex1361_price δ p η t / p t with hθo
    have hval : ∀ t, p t * θo t = bp_ex1361_price δ p η t * θ' t := by
      intro t
      simp only [hθo]
      field_simp [(hp t).ne']
    exact hE.optimal i c' θo
      ((bp_budget_transfer δ p _ d (y i) (B i) hδ hpr hq c' θo θ' hval).2 hb) hadm
  · have h0 : ∑ i, θ i t = 0 := by rw [hE.clear_assets t]; simp
    simp only [Finset.sum_const_zero]
    unfold bp_ex1361_hold
    rw [← Finset.sum_div, ← Finset.sum_mul, h0]
    simp
  · exact hE.clear_goods t

/-- Miao, p. 442: the transversality terms agree, `π_t p̂_t θ̂_t = π_t p_t θ_t`, so
`lim π_t p̂_t θ̂_t = lim π_t p_t θ_t = 0` whenever the original condition holds. -/
theorem example_13_6_1_tvc (δ p θ : ℕ → ℝ) (η : ℝ) (hδ : ∀ t, 0 < δ t) (hp : ∀ t, 0 < p t)
    (hη : 0 ≤ η) (htvc : Tendsto (fun t => δ t * p t * θ t) atTop (𝓝 0)) :
    (∀ t, δ t * bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t = δ t * p t * θ t) ∧
      Tendsto (fun t => δ t * bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t) atTop
        (𝓝 0) := by
  have h : ∀ t, δ t * bp_ex1361_price δ p η t * bp_ex1361_hold δ p η θ t = δ t * p t * θ t :=
    fun t => by rw [mul_assoc, ← bp_ex1361_value δ p η hδ hp hη θ t, mul_assoc]
  refine ⟨h, ?_⟩
  simpa only [h] using htvc

/-- Miao, p. 442: when `p_t = (1/π_t) ∑_{s>t} π_s d_s` is the fundamental value, the bubble on
`p̂` is `b_t = η/π_t`. -/
theorem example_13_6_1_bubble (δ p d : ℕ → ℝ) (η : ℝ)
    (hfund : ∀ t, p t = 1 / δ t * bp_tail (fun s => δ s * d s) t) (t : ℕ) :
    bp_ex1361_price δ p η t - 1 / δ t * bp_tail (fun s => δ s * d s) t = η / δ t := by
  unfold bp_ex1361_price
  rw [hfund t]
  ring

/-! ### Exercises 13.5 and 13.6 -/

/-- Aggregate endowment `ȳ_t = ∑ᵢ yⁱ_t`. -/
def bp_k5_Y {ι : Type*} [Fintype ι] (y : ι → ℕ → ℝ) (t : ℕ) : ℝ := ∑ i, y i t

/-- The state price deflator `π_t = βᵗ (ȳ_t/ȳ_0)^{−γ}` of Exercise 13.5. -/
noncomputable def bp_k5_defl {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (bp_k5_Y y t / bp_k5_Y y 0) ^ (-γ)

/-- The stock price `q_t = (1/π_t) ∑_{s>t} π_s d_s + η/π_t` of Exercise 13.5. -/
noncomputable def bp_k5_price {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (η : ℝ) (t : ℕ) : ℝ :=
  (bp_tail (fun s => bp_k5_defl β γ y s * d s) t + η) / bp_k5_defl β γ y t

/-- Agent `i`'s wealth `∑ π_t yⁱ_t + θⁱ_{−1}(q_0 + d_0) = ∑ π_t yⁱ_t + θⁱ_{−1}(∑ π_t d_t + η)`. -/
noncomputable def bp_k5_wealth {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) : ℝ :=
  ∑' t, bp_k5_defl β γ y t * y i t + θ0 i * (∑' t, bp_k5_defl β γ y t * d t + η)

/-- The consumption share `sⁱ(η)`. -/
noncomputable def bp_k5_share {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) : ℝ :=
  bp_k5_wealth β γ y d θ0 η i / ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t

/-- Consumption `cⁱ_t = sⁱ(η) ȳ_t`. -/
noncomputable def bp_k5_cons {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) (t : ℕ) : ℝ :=
  bp_k5_share β γ y d θ0 η i * bp_k5_Y y t

/-- The numerator `π_t q_t θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s) + θⁱ_{−1}(∑ π_s d_s + η)`. -/
noncomputable def bp_k5_value {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (t + 1), bp_k5_defl β γ y s * (y i s - bp_k5_cons β γ y d θ0 η i s) +
    θ0 i * (∑' s, bp_k5_defl β γ y s * d s + η)

/-- The portfolio `θⁱ_t` of Exercise 13.5. -/
noncomputable def bp_k5_hold {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (d : ℕ → ℝ)
    (θ0 : ι → ℝ) (η : ℝ) (i : ι) (t : ℕ) : ℝ :=
  bp_k5_value β γ y d θ0 η i t / (bp_k5_defl β γ y t * bp_k5_price β γ y d η t)

theorem bp_k5_Y_pos {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → ℕ → ℝ)
    (hy : ∀ i t, 0 < y i t) (t : ℕ) : 0 < bp_k5_Y y t :=
  Finset.sum_pos (fun i _ => hy i t) Finset.univ_nonempty

theorem bp_k5_defl_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (t : ℕ) : 0 < bp_k5_defl β γ y t := by
  unfold bp_k5_defl
  have := bp_k5_Y_pos y hy t
  have := bp_k5_Y_pos y hy 0
  positivity

theorem bp_k5_defl_zero {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (y : ι → ℕ → ℝ)
    (hy : ∀ i t, 0 < y i t) : bp_k5_defl β γ y 0 = 1 := by
  unfold bp_k5_defl
  rw [div_self (bp_k5_Y_pos y hy 0).ne', Real.one_rpow, pow_zero, one_mul]

/-- The marginal utility identity `βᵗ (sȳ_t)^{−γ} = (sȳ_0)^{−γ} π_t`. -/
theorem bp_k5_marginal {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (y : ι → ℕ → ℝ)
    (hy : ∀ i t, 0 < y i t) (s : ℝ) (hs : 0 < s) (t : ℕ) :
    β ^ t * (s * bp_k5_Y y t) ^ (-γ) = (s * bp_k5_Y y 0) ^ (-γ) * bp_k5_defl β γ y t := by
  unfold bp_k5_defl
  have h0 := bp_k5_Y_pos y hy 0
  have ht := bp_k5_Y_pos y hy t
  rw [Real.mul_rpow hs.le ht.le, Real.mul_rpow hs.le h0.le, Real.div_rpow ht.le h0.le]
  have : 0 < bp_k5_Y y 0 ^ (-γ) := Real.rpow_pos_of_pos h0 _
  field_simp

/-- The pricing equation `π_t q_t = π_{t+1}(q_{t+1} + d_{t+1})`. -/
theorem bp_k5_prices {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ)
    (hD : Summable (fun t => bp_k5_defl β γ y t * d t)) (η : ℝ) (t : ℕ) :
    bp_k5_defl β γ y t * bp_k5_price β γ y d η t =
      bp_k5_defl β γ y (t + 1) * (bp_k5_price β γ y d η (t + 1) + d (t + 1)) := by
  unfold bp_k5_price
  have h1 := (bp_k5_defl_pos β γ hβ y hy t).ne'
  have h2 := (bp_k5_defl_pos β γ hβ y hy (t + 1)).ne'
  rw [bp_tail_succ _ hD t]
  field_simp
  ring

theorem bp_k5_summable_y {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (i : ι) :
    Summable (fun t => bp_k5_defl β γ y t * y i t) := by
  refine Summable.of_nonneg_of_le (fun t => (mul_pos (bp_k5_defl_pos β γ hβ y hy t)
    (hy i t)).le) (fun t => ?_) hY
  refine mul_le_mul_of_nonneg_left ?_ (bp_k5_defl_pos β γ hβ y hy t).le
  exact Finset.single_le_sum (f := fun k => y k t) (fun k _ => (hy k t).le) (Finset.mem_univ i)

theorem bp_k5_pv_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) :
    0 < ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t :=
  hY.tsum_pos (fun t => (mul_pos (bp_k5_defl_pos β γ hβ y hy t) (bp_k5_Y_pos y hy t)).le) 0
    (mul_pos (bp_k5_defl_pos β γ hβ y hy 0) (bp_k5_Y_pos y hy 0))

/-- With zero supply, the shares sum to one. -/
theorem bp_k5_share_sum {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ) (hθ0 : ∑ i, θ0 i = 0)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (η : ℝ) :
    ∑ i, bp_k5_share β γ y d θ0 η i = 1 := by
  unfold bp_k5_share bp_k5_wealth
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hθ0, zero_mul, add_zero]
  rw [← Summable.tsum_finsetSum (fun i _ => bp_k5_summable_y β γ hβ y hy hY i)]
  have : (fun t => ∑ i, bp_k5_defl β γ y t * y i t) =
      fun t => bp_k5_defl β γ y t * bp_k5_Y y t := by
    funext t
    rw [bp_k5_Y, Finset.mul_sum]
  rw [this, div_self (bp_k5_pv_pos β γ hβ y hy hY).ne']

/-- The present value of agent `i`'s consumption is his wealth. -/
theorem bp_k5_pv_cons {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (η : ℝ) (i : ι) :
    HasSum (fun t => bp_k5_defl β γ y t * bp_k5_cons β γ y d θ0 η i t)
      (bp_k5_wealth β γ y d θ0 η i) := by
  have h := hY.hasSum.mul_left (bp_k5_share β γ y d θ0 η i)
  have hw : bp_k5_share β γ y d θ0 η i * ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t =
      bp_k5_wealth β γ y d θ0 η i := by
    unfold bp_k5_share
    field_simp [(bp_k5_pv_pos β γ hβ y hy hY).ne']
  rw [hw] at h
  convert h using 1
  funext t
  unfold bp_k5_cons
  ring

/-- `π_t q_t θⁱ_t + ∑_{s>t} π_s yⁱ_s = ∑_{s>t} π_s cⁱ_s`: the value of the portfolio plus human
wealth is the value of future consumption. -/
theorem bp_k5_value_tail {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) (η : ℝ) (i : ι) (t : ℕ) :
    bp_k5_value β γ y d θ0 η i t + bp_tail (fun s => bp_k5_defl β γ y s * y i s) t =
      bp_tail (fun s => bp_k5_defl β γ y s * bp_k5_cons β γ y d θ0 η i s) t := by
  have hc := bp_k5_pv_cons β γ hβ y hy d θ0 hY η i
  have h1 := bp_sum_add_tail _ hc.summable t
  have h2 := bp_sum_add_tail _ (bp_k5_summable_y β γ hβ y hy hY i) t
  rw [hc.tsum_eq] at h1
  unfold bp_k5_wealth at h1
  unfold bp_k5_value
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- **Exercise 13.5** (Kocherlakota 1992, Miao, p. 453). CRRA utilities `c^{1−γ}/(1−γ)`, one
stock in zero supply. For every `η ≥ 0` such that all shares `sⁱ(η)` are positive and the prices
`q_t` are positive, the consumption `cⁱ_t = sⁱ(η)ȳ_t`, the deflator `π_t = βᵗ(ȳ_t/ȳ_0)^{−γ}`, the
price `q_t = (1/π_t)∑_{s>t} π_s d_s + η/π_t` and the portfolios `θⁱ_t` form an equilibrium with
natural borrowing constraints. -/
theorem ex_13_5 {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (θ0 : ι → ℝ)
    (hθ0 : ∑ i, θ0 i = 0) (η : ℝ)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t))
    (hD : Summable (fun t => bp_k5_defl β γ y t * d t))
    (hs : ∀ i, 0 < bp_k5_share β γ y d θ0 η i) (hq : ∀ t, 0 < bp_k5_price β γ y d η t) :
    BPDetEqm (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) y d θ0
      (fun i => bp_borrowCon (bp_natLimit (bp_k5_defl β γ y) (y i)))
      (bp_k5_cons β γ y d θ0 η) (bp_k5_hold β γ y d θ0 η) (bp_k5_price β γ y d η) := by
  set δ := bp_k5_defl β γ y with hδdef
  set q := bp_k5_price β γ y d η with hqdef
  set c := bp_k5_cons β γ y d θ0 η with hcdef
  set θ := bp_k5_hold β γ y d θ0 η with hθdef
  set V := bp_k5_value β γ y d θ0 η with hVdef
  have hδ : ∀ t, 0 < δ t := bp_k5_defl_pos β γ hβ y hy
  have hδ0 : δ 0 = 1 := bp_k5_defl_zero β γ y hy
  have hpr : ∀ t, δ t * q t = δ (t + 1) * (q (t + 1) + d (t + 1)) :=
    bp_k5_prices β γ hβ y hy d hD η
  have hcpos : ∀ i t, 0 < c i t := fun i t => mul_pos (hs i) (bp_k5_Y_pos y hy t)
  -- portfolio value
  have hqθ : ∀ i t, δ t * q t * θ i t = V i t := by
    intro i t
    have := (mul_pos (hδ t) (hq t)).ne'
    change δ t * q t * (V i t / (δ t * q t)) = V i t
    rw [mul_comm]
    exact div_mul_cancel₀ (V i t) this
  have hD0 : ∑' s, δ s * d s = d 0 + bp_tail (fun s => δ s * d s) 0 := by
    have := bp_sum_add_tail _ hD 0
    simp only [zero_add, Finset.sum_range_one] at this
    rw [hδ0, one_mul] at this
    linarith
  -- budget constraints hold with equality
  have hb0 : ∀ i, c i 0 + q 0 * θ i 0 = (q 0 + d 0) * θ0 i + y i 0 := by
    intro i
    have h := hqθ i 0
    rw [hδ0, one_mul] at h
    rw [h]
    simp only [hVdef, bp_k5_value, zero_add, Finset.sum_range_one]
    simp only [hqdef, bp_k5_price, ← hδdef, hδ0, div_one]
    rw [hD0]
    ring
  have hb : ∀ i t, c i (t + 1) + q (t + 1) * θ i (t + 1) =
      (q (t + 1) + d (t + 1)) * θ i t + y i (t + 1) := by
    intro i t
    have hne := (hδ (t + 1)).ne'
    have h1 : δ (t + 1) * (c i (t + 1) + q (t + 1) * θ i (t + 1)) =
        δ (t + 1) * ((q (t + 1) + d (t + 1)) * θ i t + y i (t + 1)) := by
      have e1 : δ (t + 1) * (q (t + 1) + d (t + 1)) * θ i t = V i t := by
        rw [← hpr t]
        exact hqθ i t
      have e2 : V i (t + 1) = V i t + δ (t + 1) * (y i (t + 1) - c i (t + 1)) := by
        simp only [hVdef, bp_k5_value, Finset.sum_range_succ]
        ring
      have e3 := hqθ i (t + 1)
      calc δ (t + 1) * (c i (t + 1) + q (t + 1) * θ i (t + 1))
          = δ (t + 1) * c i (t + 1) + δ (t + 1) * q (t + 1) * θ i (t + 1) := by ring
        _ = δ (t + 1) * c i (t + 1) + V i (t + 1) := by rw [e3]
        _ = V i t + δ (t + 1) * y i (t + 1) := by rw [e2]; ring
        _ = δ (t + 1) * ((q (t + 1) + d (t + 1)) * θ i t + y i (t + 1)) := by
          rw [← e1]; ring
    exact mul_left_cancel₀ hne h1
  -- the borrowing constraint, in deflated form
  have hcon_iff : ∀ i t (x : ℝ), bp_borrowCon (bp_natLimit δ (y i)) t (q t) x ↔
      -bp_tail (fun s => δ s * y i s) t ≤ δ t * q t * x := by
    intro i t x
    unfold bp_borrowCon bp_natLimit
    have hd := hδ t
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h hd.le
      have e : δ t * -(1 / δ t * bp_tail (fun s => δ s * y i s) t) =
          -bp_tail (fun s => δ s * y i s) t := by field_simp
      rw [e] at this
      linarith
    · intro h
      have e : -(1 / δ t * bp_tail (fun s => δ s * y i s) t) =
          (1 / δ t) * (-bp_tail (fun s => δ s * y i s) t) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h (one_div_nonneg.2 hd.le)
      have e2 : 1 / δ t * (δ t * q t * x) = q t * x := by field_simp
      linarith
  have hVtail : ∀ i t, V i t + bp_tail (fun s => δ s * y i s) t =
      bp_tail (fun s => δ s * c i s) t :=
    bp_k5_value_tail β γ hβ y hy d θ0 hY η
  have hbudget : ∀ i, bp_detBudget q d (y i) (θ0 i)
      (bp_borrowCon (bp_natLimit δ (y i))) (c i) (θ i) := by
    intro i
    refine ⟨hcpos i, (hb0 i).le, fun t => (hb i t).le, fun t => ?_⟩
    rw [hcon_iff, hqθ, ← sub_nonneg]
    have := hVtail i t
    have := bp_tail_nonneg (fun s => δ s * c i s) (fun s => (mul_pos (hδ s) (hcpos i s)).le) t
    linarith
  -- utility of `c` converges
  have hadm : ∀ i, bp_detAdm β (bp_crra γ) (c i) := by
    intro i
    unfold bp_detAdm bp_crra
    have hsi := hs i
    have hY0 := bp_k5_Y_pos y hy 0
    have key : ∀ t, β ^ t * (c i t ^ (1 - γ) / (1 - γ)) =
        (bp_k5_share β γ y d θ0 η i ^ (1 - γ) * bp_k5_Y y 0 ^ (-γ) / (1 - γ)) *
          (δ t * bp_k5_Y y t) := by
      intro t
      have hYt := bp_k5_Y_pos y hy t
      simp only [hcdef, bp_k5_cons, hδdef, bp_k5_defl]
      rw [Real.mul_rpow hsi.le hYt.le, Real.div_rpow hYt.le hY0.le,
        show 1 - γ = -γ + 1 by ring, Real.rpow_add hYt, Real.rpow_one]
      have : 0 < bp_k5_Y y 0 ^ (-γ) := Real.rpow_pos_of_pos hY0 _
      have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
      field_simp
    simp only [key]
    exact hY.mul_left _
  refine ⟨hbudget, hadm, fun i c' θ' hb' hadm' => ?_, fun t => ?_, fun t => ?_⟩
  · -- optimality via the sufficiency argument with `λ_t = κ π_t`
    obtain ⟨hc', hb0', hbs', hcon'⟩ := hb'
    set κ := (bp_k5_share β γ y d θ0 η i * bp_k5_Y y 0) ^ (-γ) with hκ
    have hκpos : 0 < κ := Real.rpow_pos_of_pos (mul_pos (hs i) (bp_k5_Y_pos y hy 0)) _
    have hlam : ∀ t, β ^ t * c i t ^ (-γ) = κ * δ t := fun t =>
      bp_k5_marginal β γ y hy _ (hs i) t
    refine bp_det_sufficiency β hβ.le (bp_crra γ) (fun x => x ^ (-γ))
      (fun x x' hx hx' => bp_crra_supergradient γ hγ hγ1 x x' hx hx') q d (y i) (θ0 i)
      (c i) (θ i) c' θ' (hcpos i) hc' (fun t => Real.rpow_nonneg (hcpos i t).le _) (hb0 i)
      (hb i) hb0' hbs' (fun t => ?_) (fun T => κ * bp_tail (fun s => δ s * c i s) T)
      (by simpa using (bp_tail_tendsto (fun s => δ s * c i s)).const_mul κ) (fun T => ?_)
      (hadm i) hadm'
    · simp only [hlam]
      rw [mul_assoc, ← hpr t]
      ring_nf
      exact le_rfl
    · simp only [hlam]
      have h1 := (hcon_iff i T (θ' T)).1 (hcon' T)
      have h2 := hqθ i T
      have h3 := hVtail i T
      have e : -(κ * δ T * q T * (θ' T - θ i T)) =
          κ * (δ T * q T * θ i T - δ T * q T * θ' T) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hκpos.le
      linarith
  · -- asset market clearing
    have hcsum : ∀ s, ∑ i, c i s = bp_k5_Y y s := by
      intro s
      simp only [hcdef, bp_k5_cons]
      rw [← Finset.sum_mul, bp_k5_share_sum β γ hβ y hy d θ0 hθ0 hY η, one_mul]
    have hVsum : ∑ i, V i t = 0 := by
      simp only [hVdef, bp_k5_value, Finset.sum_add_distrib]
      rw [Finset.sum_comm, ← Finset.sum_mul, hθ0, zero_mul, add_zero]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← hcdef, hcsum s]
      simp [bp_k5_Y]
    simp only [hθdef, bp_k5_hold]
    rw [← Finset.sum_div, ← hVdef, hVsum, hθ0, zero_div]
  · simp only [hcdef, bp_k5_cons]
    rw [← Finset.sum_mul, bp_k5_share_sum β γ hβ y hy d θ0 hθ0 hY η, one_mul, hθ0, zero_mul,
      add_zero]
    rfl

/-- Exercise 13.5: the equilibria are distinct, `q_t(η) ≠ q_t(η')` for `η ≠ η'`. -/
theorem ex_13_5_continuum {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β)
    (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (d : ℕ → ℝ) (η η' : ℝ) (hne : η ≠ η') (t : ℕ) :
    bp_k5_price β γ y d η t ≠ bp_k5_price β γ y d η' t := by
  unfold bp_k5_price
  intro h
  have hd := (bp_k5_defl_pos β γ hβ y hy t).ne'
  rw [div_left_inj' hd] at h
  exact hne (by linarith)

/-- Counterexample to Exercise 13.5 for all `η ≥ 0`: two agents with endowments `1`, `β = 1/2`,
`γ = 2`, no dividends and `θ_{−1} = (1, −1)`. At `η = 3` agent 2's share is negative, so his
consumption `s²(3) ȳ_t` is negative: no equilibrium. -/
theorem ex_13_5_share_counterexample :
    bp_k5_share (ι := Bool) (1 / 2) 2 (fun _ _ => 1) (fun _ => 0)
      (fun i => if i then 1 else -1) 3 false < 0 := by
  have hdefl : ∀ t, bp_k5_defl (ι := Bool) (1 / 2) 2 (fun _ _ => 1) t = (1 / 2) ^ t := by
    intro t
    simp [bp_k5_defl, bp_k5_Y]
  have hY : ∀ t, bp_k5_Y (ι := Bool) (fun _ _ => (1 : ℝ)) t = 2 := by
    intro t
    simp [bp_k5_Y]
  have hg : ∑' t : ℕ, ((1 : ℝ) / 2) ^ t = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  unfold bp_k5_share bp_k5_wealth
  simp only [hdefl, hY, mul_one, mul_zero, tsum_zero, zero_add]
  rw [tsum_mul_right, hg]
  norm_num

/-- **Exercise 13.6** (Kocherlakota 1992, Miao, p. 453). With `θⁱ_{−1} = 0` and `d = 0`, for
every `η > 0` the allocation `cⁱ_t = sⁱ Y_t`, the price `q_t = η/π_t` and the portfolios
`θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s)/(π_t q_t)` (`ex_13_6_formulas`) form an equilibrium. -/
theorem ex_13_6 {ι : Type*} [Fintype ι] [Nonempty ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (η : ℝ) (hη : 0 < η)
    (hY : Summable (fun t => bp_k5_defl β γ y t * bp_k5_Y y t)) :
    BPDetEqm (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) y
      (fun _ => 0) (fun _ => 0)
      (fun i => bp_borrowCon (bp_natLimit (bp_k5_defl β γ y) (y i)))
      (bp_k5_cons β γ y (fun _ => 0) (fun _ => 0) η)
      (bp_k5_hold β γ y (fun _ => 0) (fun _ => 0) η) (bp_k5_price β γ y (fun _ => 0) η) := by
  refine ex_13_5 β γ hβ hγ hγ1 y hy _ _ (by simp) η hY (by simp)
    (fun i => ?_) (fun t => ?_)
  · unfold bp_k5_share bp_k5_wealth
    simp only [zero_mul, add_zero]
    refine div_pos ?_ (bp_k5_pv_pos β γ hβ y hy hY)
    exact (bp_k5_summable_y β γ hβ y hy hY i).tsum_pos
      (fun t => (mul_pos (bp_k5_defl_pos β γ hβ y hy t) (hy i t)).le) 0
      (mul_pos (bp_k5_defl_pos β γ hβ y hy 0) (hy i 0))
  · unfold bp_k5_price bp_tail
    simp only [mul_zero, tsum_zero, zero_add]
    exact div_pos hη (bp_k5_defl_pos β γ hβ y hy t)

/-- Exercise 13.6: the objects of `ex_13_6` are the book's: `q_t = η/π_t`,
`sⁱ = ∑ π_t yⁱ_t / ∑ π_t Y_t` and `θⁱ_t = ∑_{s≤t} π_s(yⁱ_s − cⁱ_s)/(π_t q_t)`. -/
theorem ex_13_6_formulas {ι : Type*} [Fintype ι] (β γ : ℝ) (y : ι → ℕ → ℝ) (η : ℝ)
    (i : ι) (t : ℕ) :
    bp_k5_price β γ y (fun _ => 0) η t = η / bp_k5_defl β γ y t ∧
      bp_k5_share β γ y (fun _ => 0) (fun _ => 0) η i =
        (∑' t, bp_k5_defl β γ y t * y i t) / ∑' t, bp_k5_defl β γ y t * bp_k5_Y y t ∧
      bp_k5_hold β γ y (fun _ => 0) (fun _ => 0) η i t =
        (∑ s ∈ Finset.range (t + 1), bp_k5_defl β γ y s *
          (y i s - bp_k5_cons β γ y (fun _ => 0) (fun _ => 0) η i s)) /
          (bp_k5_defl β γ y t * bp_k5_price β γ y (fun _ => 0) η t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold bp_k5_price bp_tail
    simp
  · unfold bp_k5_share bp_k5_wealth
    simp
  · unfold bp_k5_hold bp_k5_value
    simp

/-- Exercise 13.6: "there is an equilibrium in which `q_t = 0`": autarky `cⁱ = yⁱ`, `θⁱ = 0`
(assuming each endowment has finite utility). -/
theorem ex_13_6_autarky {ι : Type*} [Fintype ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (y : ι → ℕ → ℝ) (hy : ∀ i t, 0 < y i t) (δ : ℕ → ℝ) (hδ : ∀ t, 0 < δ t)
    (hU : ∀ i, bp_detAdm β (bp_crra γ) (y i)) :
    BPDetEqm (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) y
      (fun _ => 0) (fun _ => 0) (fun i => bp_borrowCon (bp_natLimit δ (y i))) y
      (fun _ _ => 0) (fun _ => 0) := by
  have hB : ∀ i t, 0 ≤ bp_natLimit δ (y i) t := fun i t =>
    mul_nonneg (one_div_nonneg.2 (hδ t).le)
      (bp_tail_nonneg _ (fun s => (mul_pos (hδ s) (hy i s)).le) t)
  refine ⟨fun i => ⟨hy i, by simp, fun t => by simp, fun t => ?_⟩, hU,
    fun i c' θ' hb hadm => ?_, fun t => by simp, fun t => by simp⟩
  · unfold bp_borrowCon
    simp only [mul_zero, neg_nonpos]
    exact hB i t
  · obtain ⟨hc', hb0, hbs, -⟩ := hb
    have hle : ∀ t, c' t ≤ y i t := by
      intro t
      cases t with
      | zero => simpa using hb0
      | succ t => simpa using hbs t
    unfold bp_detU
    refine Summable.tsum_le_tsum (fun t => ?_) hadm (hU i)
    exact mul_le_mul_of_nonneg_left (bp_crra_mono γ hγ hγ1 _ _ (hc' t) (hle t))
      (pow_nonneg hβ.le t)

/-- Pareto optimality in the deterministic economy: no feasible allocation with positive,
admissible consumption makes everyone weakly better off and someone strictly better off. -/
def bp_detParetoOptimal {ι : Type*} [Fintype ι] (U : ι → (ℕ → ℝ) → ℝ)
    (adm : ι → (ℕ → ℝ) → Prop) (Y : ℕ → ℝ) (c : ι → ℕ → ℝ) : Prop :=
  ¬ ∃ x : ι → ℕ → ℝ, (∀ i t, 0 < x i t) ∧ (∀ t, ∑ i, x i t ≤ Y t) ∧ (∀ i, adm i (x i)) ∧
    (∀ i, U i (c i) ≤ U i (x i)) ∧ ∃ i, U i (c i) < U i (x i)

/-- Exercise 13.6: "the consumption allocation is Pareto optimal". With CRRA utilities, any
allocation `cⁱ_t = sⁱ Y_t` with positive shares summing to one (in particular that of `ex_13_6`)
is Pareto optimal; the Negishi weights are `(sⁱ)^γ`. -/
theorem ex_13_6_pareto {ι : Type*} [Fintype ι] (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ1 : γ ≠ 1) (Y : ℕ → ℝ) (hYpos : ∀ t, 0 < Y t) (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∑ i, s i = 1) (hadm : ∀ i, bp_detAdm β (bp_crra γ) (fun t => s i * Y t)) :
    bp_detParetoOptimal (fun _ => bp_detU β (bp_crra γ)) (fun _ => bp_detAdm β (bp_crra γ)) Y
      (fun i t => s i * Y t) := by
  rintro ⟨x, hx, hfeas, hxadm, hge, i₀, hgt⟩
  set w : ι → ℝ := fun i => s i ^ γ with hw
  have hwpos : ∀ i, 0 < w i := fun i => Real.rpow_pos_of_pos (hs i) _
  -- weighted per-period gain is nonpositive
  have hper : ∀ t, ∑ i, w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) ≤ 0 := by
    intro t
    have hYt := hYpos t
    have h1 : ∀ i, w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) ≤
        β ^ t * Y t ^ (-γ) * (x i t - s i * Y t) := by
      intro i
      have hsg := bp_crra_supergradient γ hγ hγ1 (s i * Y t) (x i t)
        (mul_pos (hs i) hYt) (hx i t)
      have hwm : w i * (s i * Y t) ^ (-γ) = Y t ^ (-γ) := by
        rw [hw, Real.mul_rpow (hs i).le hYt.le, ← mul_assoc, ← Real.rpow_add (hs i)]
        simp
      have e : w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) =
          w i * β ^ t * (bp_crra γ (x i t) - bp_crra γ (s i * Y t)) := by ring
      rw [e]
      have h2 : bp_crra γ (x i t) - bp_crra γ (s i * Y t) ≤
          (s i * Y t) ^ (-γ) * (x i t - s i * Y t) := by
        unfold bp_crra
        linarith
      have h3 := mul_le_mul_of_nonneg_left h2
        (mul_nonneg (hwpos i).le (pow_nonneg hβ.le t))
      calc w i * β ^ t * (bp_crra γ (x i t) - bp_crra γ (s i * Y t))
          ≤ w i * β ^ t * ((s i * Y t) ^ (-γ) * (x i t - s i * Y t)) := h3
        _ = β ^ t * (w i * (s i * Y t) ^ (-γ)) * (x i t - s i * Y t) := by ring
        _ = β ^ t * Y t ^ (-γ) * (x i t - s i * Y t) := by rw [hwm]
    have h4 : ∑ i, β ^ t * Y t ^ (-γ) * (x i t - s i * Y t) ≤ 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hs1, one_mul]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg hβ.le t) (Real.rpow_nonneg hYt.le _)) (by linarith [hfeas t])
    exact (Finset.sum_le_sum (fun i _ => h1 i)).trans h4
  have hsum : ∀ i, Summable (fun t => w i * (β ^ t * bp_crra γ (x i t) -
      β ^ t * bp_crra γ (s i * Y t))) := fun i => ((hxadm i).sub (hadm i)).mul_left _
  have htot : ∑ i, w i * (bp_detU β (bp_crra γ) (x i) -
      bp_detU β (bp_crra γ) (fun t => s i * Y t)) ≤ 0 := by
    have e : ∀ i, w i * (bp_detU β (bp_crra γ) (x i) -
        bp_detU β (bp_crra γ) (fun t => s i * Y t)) =
        ∑' t, w i * (β ^ t * bp_crra γ (x i t) - β ^ t * bp_crra γ (s i * Y t)) := by
      intro i
      unfold bp_detU
      rw [← (hxadm i).tsum_sub (hadm i), (((hxadm i).sub (hadm i))).tsum_mul_left]
    simp only [e]
    rw [← Summable.tsum_finsetSum (fun i _ => hsum i)]
    exact tsum_nonpos hper
  have hpos : 0 < ∑ i, w i * (bp_detU β (bp_crra γ) (x i) -
      bp_detU β (bp_crra γ) (fun t => s i * Y t)) := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ w i * (bp_detU β (bp_crra γ) (x i) -
        bp_detU β (bp_crra γ) (fun t => s i * Y t)) :=
      fun i _ => mul_nonneg (hwpos i).le (by linarith [hge i])
    exact lt_of_lt_of_le (mul_pos (hwpos i₀) (by linarith))
      (Finset.single_le_sum hnn (Finset.mem_univ i₀))
  linarith

end Miao.CompleteMarkets
