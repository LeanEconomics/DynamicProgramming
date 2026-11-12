/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.Endowment

/-!
# Sequential and Arrow–Debreu equilibrium, and the representative agent

AKMM, §16.3, pp. 471–472 ("Preview": the three results under complete markets) and §16.4,
p. 482 (representative agent), in the two-period economy of §16.4: a finite set `I` of agents with
endowments `yᵢ : Option S → ℝ` (`none` is date 0) and utilities `Uᵢ`, `N` assets with payoffs `D`.

* Sequential-markets equilibrium (`eqSeq`, p. 472: optimality on (16.10), goods and asset market
  clearing) and Arrow–Debreu equilibrium with date-0 numeraire and state prices `q`
  (`eqAD`).
* With complete markets the two coincide: a sequential equilibrium with strictly increasing
  utilities is an Arrow–Debreu equilibrium at the state prices of `p` (`eq_seq_to_ad`), and an
  Arrow–Debreu equilibrium is a sequential equilibrium at `p = Dᵀq` with portfolios that
  replicate the net trades and clear the asset markets (`eq_ad_to_seq`).
* **Representative agent** (p. 482): with complete markets, concave differentiable utilities and
  the first-order conditions `∂Uᵢ = αᵢ q̂`, the planner's value `U_λ`, `λᵢ = 1/αᵢ`, is bounded
  (`eq_planner_bound`); `c = y`, `θ = 0` solves the representative agent's problem at the same
  prices (`eq_repAgent`); and `q(ω) = (∂U_λ/∂y₁(ω))/(∂U_λ/∂y₀)` (`eq_repAgent_statePrice`).

Departure: the book states the three results for the infinite-horizon sequential economy; they
are proved here in its two-period version (where the budget sets are those of §16.4). On an
infinite tree the sequential budget (16.8) without a debt limit admits Ponzi schemes (Miao's
`rd_ponzi_arb`), and the equivalence is Miao's `theorem_13_5_1_if` under debt constraints and the
transversality condition. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix

variable {I S N : Type} [Fintype I] [Fintype S] [Fintype N]

/-- AKMM, p. 478: the Arrow–Debreu budget set with date-0 numeraire, state prices `q` and
`c ≥ 0`. -/
def eqBudgetAD (q : S → ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | (∀ k, 0 ≤ c k) ∧ c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0}

/-- AKMM, p. 472: a sequential-markets competitive equilibrium `(c, θ, p)` of the two-period
economy: optimality on the budget set (16.10) with `c ≥ 0`, goods-market clearing and
asset-market clearing (zero net supply). -/
def eqSeq (U : I → (Option S → ℝ) → ℝ) (y : I → Option S → ℝ) (D : Matrix S N ℝ)
    (c : I → Option S → ℝ) (θ : I → N → ℝ) (p : N → ℝ) : Prop :=
  (∀ i, (∀ k, 0 ≤ c i k) ∧ (∀ k, c i k ≤ y i k + (tpW p D *ᵥ θ i) k) ∧
    ∀ c' ∈ tpBudgetPos p D (y i), U i c' ≤ U i (c i)) ∧
  (∀ k, ∑ i, c i k = ∑ i, y i k) ∧ ∑ i, θ i = 0

/-- AKMM, p. 471: an Arrow–Debreu equilibrium `(c, q)` with date-0 numeraire and state prices
`q ≫ 0`. -/
def eqAD (U : I → (Option S → ℝ) → ℝ) (y : I → Option S → ℝ) (c : I → Option S → ℝ)
    (q : S → ℝ) : Prop :=
  (∀ s, 0 < q s) ∧ (∀ i, c i ∈ eqBudgetAD q (y i) ∧ ∀ c' ∈ eqBudgetAD q (y i), U i c' ≤ U i (c i)) ∧
  ∀ k, ∑ i, c i k = ∑ i, y i k

/-- With complete markets the budget set with `c ≥ 0` is the Arrow–Debreu one. -/
theorem eq_budgetPos_complete {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) (hD : Function.Surjective D.mulVec) (y : Option S → ℝ) :
    tpBudgetPos p D y = eqBudgetAD q y := by
  ext c
  simp only [tpBudgetPos, eqBudgetAD, tp_budget_complete hq hD y]
  rfl

/-- AKMM, p. 472, first result (sequential ⇒ Arrow–Debreu): with complete markets and strictly
increasing utilities, a sequential equilibrium `(c, θ, p)` is an Arrow–Debreu equilibrium at the
state prices `q` of `p` (which exist by `tp_ftap`, the agents' optima excluding arbitrage). -/
theorem eq_seq_to_ad [Nonempty I] {U : I → (Option S → ℝ) → ℝ} (hU : ∀ i, StrictMono (U i))
    {y : I → Option S → ℝ} {D : Matrix S N ℝ} (hD : Function.Surjective D.mulVec)
    {c : I → Option S → ℝ} {θ : I → N → ℝ} {p : N → ℝ} (hE : eqSeq U y D c θ p) :
    ∃ q, tpStatePrices p D q ∧ eqAD U y c q := by
  obtain ⟨hopt, hclear, -⟩ := hE
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hNA : tpNoArbitrage p D :=
    tp_noArbitrage_of_optimal (hU i₀) ⟨(hopt i₀).1, θ i₀, (hopt i₀).2.1⟩ (hopt i₀).2.2
  obtain ⟨q, hq⟩ := (tp_ftap p D).1 hNA
  refine ⟨q, hq, hq.1, fun i => ?_, hclear⟩
  rw [← eq_budgetPos_complete hq hD]
  exact ⟨⟨(hopt i).1, θ i, (hopt i).2.1⟩, (hopt i).2.2⟩

/-- AKMM, p. 472, first result (Arrow–Debreu ⇒ sequential): with complete markets an Arrow–Debreu
equilibrium `(c, q)` is a sequential equilibrium at the prices `p = Dᵀq`; every agent but `i₀`
holds a portfolio replicating its date-1 net trade and agent `i₀` holds minus their sum, which
replicates its own net trade by goods-market clearing. -/
theorem eq_ad_to_seq (i₀ : I) {U : I → (Option S → ℝ) → ℝ}
    {y : I → Option S → ℝ} {D : Matrix S N ℝ} (hD : Function.Surjective D.mulVec)
    {c : I → Option S → ℝ} {q : S → ℝ} (hE : eqAD U y c q) :
    ∃ θ : I → N → ℝ, eqSeq U y D c θ (fun n => ∑ s, D s n * q s) := by
  classical
  obtain ⟨hq0, hopt, hclear⟩ := hE
  set p : N → ℝ := fun n => ∑ s, D s n * q s with hp
  have hq : tpStatePrices p D q := ⟨hq0, fun n => rfl⟩
  set θ' : I → N → ℝ := fun i => Function.surjInv hD fun s => c i (some s) - y i (some s)
  have hθ' : ∀ i, D *ᵥ θ' i = fun s => c i (some s) - y i (some s) := fun i =>
    Function.surjInv_eq hD _
  set θ : I → N → ℝ := fun i => if i = i₀ then -∑ j ∈ Finset.univ.erase i₀, θ' j else θ' i
  have hθ : ∀ i, D *ᵥ θ i = fun s => c i (some s) - y i (some s) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp only [θ, ↓reduceIte, mulVec_neg, mulVec_sum, hθ']
      funext s
      have hs := hclear (some s)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _
        (Finset.mem_univ i)] at hs
      simp only [Pi.neg_apply, Finset.sum_apply]
      rw [Finset.sum_sub_distrib]
      linarith
    · simp only [θ, hi, ↓reduceIte, hθ']
  have hsum : ∑ i, θ i = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    simp only [θ, ↓reduceIte]
    rw [neg_add_eq_zero]
    exact Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  refine ⟨θ, fun i => ⟨(hopt i).1.1, fun k => ?_, ?_⟩, hclear, hsum⟩
  · have hbind : c i ∈ tpBudgetBind p D (y i) := by
      rw [eq_16_14 hq]
      exact ⟨(hopt i).1.2, θ i, hθ i⟩
    obtain ⟨θ₁, h0, h1⟩ := hbind
    have hpθ : p ⬝ᵥ θ₁ = p ⬝ᵥ θ i := by
      have e1 := tp_qhat_orth hq.2 θ₁
      have e2 := tp_qhat_orth hq.2 (θ i)
      rw [Fintype.sum_option] at e1 e2
      simp only [tpQhat, Option.elim, one_mul, tp_W_none, tp_W_some] at e1 e2
      have : D *ᵥ θ₁ = D *ᵥ θ i := funext fun s => by
        rw [hθ i]; simp only; linarith [h1 s]
      rw [this] at e1
      linarith
    cases k with
    | none => rw [tp_W_none]; linarith
    | some s => rw [tp_W_some, hθ i]; simp
  · rw [eq_budgetPos_complete hq hD]
    exact (hopt i).2

/-- AKMM, p. 482: under the hypotheses of the First Welfare Theorem (`en_fwt_planner`), every
allocation feasible for an aggregate bundle `y′` has weighted utility at most
`Σᵢ λᵢUᵢ(cᵢ) + Σ_h p(h)(y′(h) − y(h))`, `λᵢ = 1/αᵢ`. -/
theorem eq_planner_bound {H : Type} [Fintype H] {U : I → (H → ℝ) → ℝ}
    {DU : I → (H → ℝ) →L[ℝ] ℝ} {c : I → H → ℝ} {y : H → ℝ} {p : H → ℝ} {α : I → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i)) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hα0 : ∀ i, 0 < α i) (hα : ∀ i v, DU i v = α i * ∑ h, p h * v h) (hp : ∀ h, 0 ≤ p h)
    (hclear : ∀ h, ∑ i, c i h = y h) {y' : H → ℝ} {c' : I → H → ℝ} (hc' : enFeasible c' y') :
    ∑ i, 1 / α i * U i (c' i) ≤ ∑ i, 1 / α i * U i (c i) + ∑ h, p h * (y' h - y h) := by
  have hi : ∀ i, 1 / α i * U i (c' i) ≤ 1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h) :=
    fun i => by
      have := en_concave_le_fderiv (hconc i) (hU i) (c' i)
      rw [hα i] at this
      have ha := hα0 i
      have : 1 / α i * U i (c' i) ≤ 1 / α i * (U i (c i) + α i * ∑ h, p h * (c' i - c i) h) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      rw [mul_add, ← mul_assoc, one_div_mul_cancel ha.ne', one_mul] at this
      simpa using this
  have hsum : ∑ i, ∑ h, p h * (c' i h - c i h) ≤ ∑ h, p h * (y' h - y h) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun h _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hclear h]
    exact mul_le_mul_of_nonneg_left (by linarith [hc' h]) (hp h)
  calc ∑ i, 1 / α i * U i (c' i)
      ≤ ∑ i, (1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ∑ i, 1 / α i * U i (c i) + ∑ i, ∑ h, p h * (c' i h - c i h) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- **Representative agent** (AKMM, p. 482). With complete markets, concave differentiable
utilities whose derivatives at the equilibrium are `αᵢ q̂` (the first-order conditions (16.4) at
the consumption prices `q̂ = (1, q)`), `αᵢ > 0`, and goods-market clearing, the aggregate
endowment `c = y` with `θ = 0` solves the problem of the representative agent with utility
`U_λ = Σᵢ λᵢUᵢ` (the planner's value, `λᵢ = 1/αᵢ`) at the same asset prices. -/
theorem eq_repAgent [Nonempty I] {U : I → (Option S → ℝ) → ℝ}
    {DU : I → (Option S → ℝ) →L[ℝ] ℝ} {c : I → Option S → ℝ} {ybar : Option S → ℝ}
    {α : I → ℝ} {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i)) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hα0 : ∀ i, 0 < α i) (hα : ∀ i v, DU i v = α i * ∑ h, tpQhat q h * v h)
    (hclear : ∀ h, ∑ i, c i h = ybar h) :
    ybar ∈ tpBudget p D ybar ∧
      ∀ c' ∈ tpBudget p D ybar, en_plannerValue (fun i => 1 / α i) U c' ≤
        en_plannerValue (fun i => 1 / α i) U ybar := by
  classical
  have hp : ∀ h, 0 ≤ tpQhat q h := fun h => by
    cases h with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using (hq.1 s).le
  have hopt := en_fwt_planner hconc hU hα0 hα hp hclear
  refine ⟨⟨0, fun k => by simp⟩, fun c' hc' => ?_⟩
  rw [en_plannerValue_eq hopt]
  have hval : ∑ h, tpQhat q h * (c' h - ybar h) ≤ 0 := by
    have := tp_budget_single hq hc'
    rw [Fintype.sum_option]
    simpa [tpQhat] using this
  obtain ⟨i₀⟩ := ‹Nonempty I›
  refine csSup_le ⟨_, fun i => if i = i₀ then c' else 0, fun h => ?_, rfl⟩ ?_
  · simp [apply_ite (fun f : Option S → ℝ => f h)]
  · rintro v ⟨c'', hc'', rfl⟩
    have := eq_planner_bound hconc hU hα0 hα hp hclear hc''
    linarith

/-- AKMM, p. 482: with the weights `λᵢ = 1/αᵢ`, the state prices are the representative agent's
marginal rates of substitution, `q(ω) = (∂U_λ(y)/∂y₁(ω))/(∂U_λ(y)/∂y₀)`, whenever `U_λ` is
differentiable at the aggregate endowment (the boundedness needed by (16.2) is
`eq_planner_bound`). -/
theorem eq_repAgent_statePrice [Nonempty I] [DecidableEq S]
    {U : I → (Option S → ℝ) → ℝ} {DU : I → (Option S → ℝ) →L[ℝ] ℝ} {c : I → Option S → ℝ}
    {ybar : Option S → ℝ} {α : I → ℝ} {q : S → ℝ} (hq : ∀ s, 0 < q s)
    (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i)) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hα0 : ∀ i, 0 < α i) (hα : ∀ i v, DU i v = α i * ∑ h, tpQhat q h * v h)
    (hclear : ∀ h, ∑ i, c i h = ybar h) {DW : (Option S → ℝ) →L[ℝ] ℝ}
    (hW : HasFDerivAt (en_plannerValue (fun i => 1 / α i) U) DW ybar) (s : S) :
    q s = DW (Pi.single (some s) 1) / DW (Pi.single none 1) := by
  classical
  have hp : ∀ h, 0 ≤ tpQhat q h := fun h => by
    cases h with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using (hq s).le
  have hopt := en_fwt_planner hconc hU hα0 hα hp hclear
  have hb : ∀ y', BddAbove {v | ∃ c', enFeasible c' y' ∧
      v = ∑ i, 1 / α i * U i (c' i)} := fun y' =>
    ⟨_, by
      rintro v ⟨c', hc', rfl⟩
      exact eq_planner_bound hconc hU hα0 hα hp hclear hc'⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hMU : ∀ h, 1 / α i₀ * DU i₀ (Pi.single h 1) = tpQhat q h := fun h => by
    rw [hα i₀]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field_simp [(hα0 i₀).ne']
  rw [eq_16_2 hopt hU hb hW i₀, eq_16_2 hopt hU hb hW i₀, hMU, hMU]
  simp [tpQhat]

end AKMM.AssetPrices
