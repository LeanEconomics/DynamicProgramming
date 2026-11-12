/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.TwoPeriod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Optimal portfolios, the budget set in state prices and subjective state prices

AKMM, §16.4, pp. 473 and 477–480. A consumption plan is `c : Option S → ℝ` (`none` is date 0);
the budget set (16.10) is `{c : c ≤ y + Wθ for some θ}`, and `tpBudgetPos` adds `c ≥ 0`.

* (16.10) in the book's two-line form (`eq_16_10`).
* **Optimum ⇒ no arbitrage** (p. 477): with strictly increasing utility, an optimal plan rules
  out arbitrage (`tp_noArbitrage_of_optimal`).
* **No arbitrage ⇒ an optimum exists** (p. 477): with `y ≥ 0` and `c ≥ 0` the budget set is
  compact under no arbitrage (`tp_budgetPos_isCompact`: bounded by the state prices,
  `q̂ᵀc ≤ q̂ᵀy`, and closed as the projection of a compact set), so a continuous utility attains its
  maximum (`tp_exists_optimal`); together, `tp_exists_optimal_iff`. Without `c ≥ 0` the claim is
  false (`tp_no_optimal_without_nonneg`).
* **(16.14)**: every budget-feasible plan satisfies the single state-price budget constraint
  (`tp_budget_single`); the set (16.14) is the budget set with binding date-1 constraints
  (`eq_16_14`), and the printed claim that it equals (16.10) is false
  (`eq_16_14_counterexample`); with complete markets the budget set is the Arrow–Debreu budget set
  (`tp_budget_complete`).
* **First-order conditions and (16.15)**: at an interior optimum with differentiable `U`,
  `ψpⁿ = Σ_ω η(ω)dⁿ(ω)` (`tp_portfolio_foc`), so `qᵢ(ω) = (∂U/∂cᵢ,₁(ω))/(∂U/∂cᵢ,₀)` are state
  prices (`eq_16_15`); expected power utility gives `qᵢ(ω) = βπ(ω)(cᵢ,₁(ω)/cᵢ,₀)^{−γ}`
  (`tp_crra_marginal`, `tp_crra_statePrice`), `βπ(ω)` if `γ = 0` (`tp_riskNeutral_statePrice`).
* **Agreement** (p. 480): agents always agree on asset prices; with complete markets they agree on
  state prices (`tp_agreement_complete`).

Departures: the existence result needs `c ≥ 0` and `y ≥ 0` (the book's (16.10) has no consumption
constraint); the first-order conditions are derived at an interior optimum; (16.14) is corrected as
above. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix Filter Topology

variable {S N : Type} [Fintype S] [Fintype N]

/-- AKMM, (16.10), p. 473: the budget set `B(p, yᵢ) = {c : c ≤ y + Wθ for some θ ∈ ℝᴺ}`. -/
def tpBudget (p : N → ℝ) (D : Matrix S N ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | ∃ θ, ∀ k, c k ≤ y k + (tpW p D *ᵥ θ) k}

/-- The budget set with nonnegative consumption. -/
def tpBudgetPos (p : N → ℝ) (D : Matrix S N ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | (∀ k, 0 ≤ c k) ∧ c ∈ tpBudget p D y}

omit [Fintype S] in
/-- AKMM, (16.10), p. 473: the budget set in the book's form `cᵢ,₀ + pᵀθ ≤ yᵢ,₀`,
`cᵢ,₁(ω) ≤ yᵢ,₁(ω) + d(ω)ᵀθ`. -/
theorem eq_16_10 (p : N → ℝ) (D : Matrix S N ℝ) (y c : Option S → ℝ) :
    c ∈ tpBudget p D y ↔
      ∃ θ, c none + p ⬝ᵥ θ ≤ y none ∧ ∀ s, c (some s) ≤ y (some s) + (D *ᵥ θ) s := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, ?_, fun s => ?_⟩
    · have := hθ none
      rw [tp_W_none] at this
      linarith
    · simpa [tp_W_some] using hθ (some s)
  · rintro ⟨θ, h0, h1⟩
    refine ⟨θ, fun k => ?_⟩
    cases k with
    | none => rw [tp_W_none]; linarith
    | some s => rw [tp_W_some]; exact h1 s

omit [Fintype S] in
/-- AKMM, p. 477: if an optimal plan exists for a strictly increasing utility, there is no
arbitrage: an arbitrage added to the optimal portfolio would raise utility. -/
theorem tp_noArbitrage_of_optimal {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    {U : (Option S → ℝ) → ℝ} (hU : StrictMono U) {c : Option S → ℝ}
    (hc : c ∈ tpBudgetPos p D y) (hopt : ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) :
    tpNoArbitrage p D := by
  rintro θa ⟨hnn, hne⟩
  obtain ⟨hc0, θ, hθ⟩ := hc
  have hmem : c + tpW p D *ᵥ θa ∈ tpBudgetPos p D y := by
    refine ⟨fun k => add_nonneg (hc0 k) (hnn k), θ + θa, fun k => ?_⟩
    simp only [Pi.add_apply, mulVec_add]
    linarith [hθ k]
  have hlt : c < c + tpW p D *ᵥ θa := by
    refine lt_of_le_of_ne (fun k => le_add_of_nonneg_right (hnn k)) fun h => hne ?_
    have := congrArg (fun z => z - c) h
    simpa using this.symm
  exact absurd (hopt _ hmem) (not_le.2 (hU hlt))

omit [Fintype S] in
/-- AKMM, p. 477: under no arbitrage, with `y ≥ 0`, the budget set with `c ≥ 0` is compact. The
state prices `q̂ ≫ 0` (`tp_ftap`) bound every feasible plan: `q̂ₖcₖ ≤ q̂ᵀ(y + x) = q̂ᵀy` for the
attainable `x`, and the set is the projection of the compact set of pairs `(c, x)`. -/
theorem tp_budgetPos_isCompact [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} (h : tpNoArbitrage p D)
    {y : Option S → ℝ} (hy : ∀ k, 0 ≤ y k) : IsCompact (tpBudgetPos p D y) := by
  have := Fintype.ofFinite S
  obtain ⟨q, hq⟩ := (tp_ftap p D).1 h
  have hqh : ∀ k, 0 < tpQhat q k := fun k => by
    cases k with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using hq.1 s
  set V : ℝ := ∑ k, tpQhat q k * y k with hV
  set b : Option S → ℝ := fun k => V / tpQhat q k with hb
  set K : Set ((Option S → ℝ) × (Option S → ℝ)) :=
    {z | (∀ k, 0 ≤ z.1 k) ∧ (∀ k, z.1 k ≤ y k + z.2 k) ∧ z.2 ∈ tpAttainable p D} with hK
  have hbound : ∀ x ∈ tpAttainable p D, (∀ k, 0 ≤ y k + x k) → ∀ k, y k + x k ≤ b k := by
    intro x hx hnn k
    have horth := eq_16_13 hq.2 x hx
    have hsum : ∑ j, tpQhat q j * (y j + x j) = V := by
      simp only [mul_add, Finset.sum_add_distrib, horth, add_zero, hV]
    have hle : tpQhat q k * (y k + x k) ≤ V := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun j => tpQhat q j * (y j + x j))
        (fun j _ => mul_nonneg (hqh j).le (hnn j)) (Finset.mem_univ k)
    rw [hb, le_div_iff₀ (hqh k)]
    linarith
  have hKsub : K ⊆ Set.Icc 0 b ×ˢ Set.Icc (-y) b := by
    rintro ⟨c, x⟩ ⟨h0, h1, hx⟩
    have hnn : ∀ k, 0 ≤ y k + x k := fun k => (h0 k).trans (h1 k)
    have hb' := hbound x hx hnn
    refine ⟨⟨fun k => h0 k, fun k => (h1 k).trans (hb' k)⟩, fun k => ?_, fun k => ?_⟩
    · simp only [Pi.neg_apply]
      linarith [hnn k]
    · linarith [hb' k, hy k]
  have hKclosed : IsClosed K := by
    have e1 : IsClosed {z : (Option S → ℝ) × (Option S → ℝ) | ∀ k, 0 ≤ z.1 k} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le continuous_const (by fun_prop)
    have e2 : IsClosed {z : (Option S → ℝ) × (Option S → ℝ) | ∀ k, z.1 k ≤ y k + z.2 k} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le (by fun_prop) (by fun_prop)
    have e3 : IsClosed {z : (Option S → ℝ) × (Option S → ℝ) | z.2 ∈ tpAttainable p D} :=
      (Submodule.closed_of_finiteDimensional (tpAttainable p D)).preimage continuous_snd
    exact e1.inter (e2.inter e3)
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have heq : tpBudgetPos p D y = Prod.fst '' K := by
    ext c
    constructor
    · rintro ⟨h0, θ, hθ⟩
      exact ⟨(c, tpW p D *ᵥ θ), ⟨h0, hθ, θ, rfl⟩, rfl⟩
    · rintro ⟨⟨c', x⟩, ⟨h0, h1, θ, rfl⟩, rfl⟩
      exact ⟨h0, θ, h1⟩
  rw [heq]
  exact hKc.image continuous_fst

omit [Fintype S] in
/-- The endowment is budget feasible. -/
theorem tp_endowment_mem {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    (hy : ∀ k, 0 ≤ y k) : y ∈ tpBudgetPos p D y :=
  ⟨hy, 0, fun k => by simp⟩

omit [Fintype S] in
/-- AKMM, p. 477: if there is no arbitrage and the utility function is continuous, the agent's
problem has a solution (with `y ≥ 0` and `c ≥ 0`). -/
theorem tp_exists_optimal [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} (h : tpNoArbitrage p D)
    {y : Option S → ℝ} (hy : ∀ k, 0 ≤ y k) {U : (Option S → ℝ) → ℝ}
    (hU : ContinuousOn U (tpBudgetPos p D y)) :
    ∃ c ∈ tpBudgetPos p D y, ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c := by
  have := Fintype.ofFinite S
  obtain ⟨c, hc, hmax⟩ := (tp_budgetPos_isCompact h hy).exists_isMaxOn
    ⟨y, tp_endowment_mem hy⟩ hU
  exact ⟨c, hc, fun c' hc' => hmax hc'⟩

omit [Fintype S] in
/-- AKMM, p. 477: for a continuous, strictly increasing utility, an optimal plan exists iff there
is no arbitrage. -/
theorem tp_exists_optimal_iff [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    (hy : ∀ k, 0 ≤ y k) {U : (Option S → ℝ) → ℝ} (hUc : Continuous U) (hU : StrictMono U) :
    (∃ c ∈ tpBudgetPos p D y, ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) ↔ tpNoArbitrage p D := by
  have := Fintype.ofFinite S
  exact ⟨fun ⟨_, hc, hopt⟩ => tp_noArbitrage_of_optimal hU hc hopt,
    fun h => tp_exists_optimal h hy hUc.continuousOn⟩

/-- One state and one Arrow security. -/
def tpArrowOne : Matrix Unit Unit ℝ := Matrix.of fun _ _ => 1

/-- Two states and only a riskless bond. -/
def tpBondOnly : Matrix (Fin 2) Unit ℝ := Matrix.of fun _ _ => 1

/-- AKMM, p. 477, the need for `c ≥ 0`: one state, one Arrow security at price 1 (no arbitrage),
and the continuous, strictly increasing `U(c) = c₀ + 2c₁`; without a lower bound on consumption
the budget set (16.10) has no optimum. -/
theorem tp_no_optimal_without_nonneg :
    tpNoArbitrage (fun _ : Unit => (1 : ℝ)) tpArrowOne ∧
      ¬ ∃ c ∈ tpBudget (fun _ : Unit => (1 : ℝ)) tpArrowOne 0,
        ∀ c' ∈ tpBudget (fun _ : Unit => (1 : ℝ)) tpArrowOne 0,
          c' none + 2 * c' (some ()) ≤ c none + 2 * c (some ()) := by
  refine ⟨(tp_ftap _ _).2 ⟨fun _ => 1, fun _ => one_pos, fun _ => by simp [tpArrowOne]⟩, ?_⟩
  rintro ⟨c, ⟨θ, hθ⟩, hopt⟩
  have e0 : ∀ θ : Unit → ℝ,
      (tpW (fun _ : Unit => (1 : ℝ)) tpArrowOne *ᵥ θ) none = -θ () := by
    intro θ
    rw [tp_W_none]
    simp [dotProduct]
  have e1 : ∀ (θ : Unit → ℝ) (s : Unit),
      (tpW (fun _ : Unit => (1 : ℝ)) tpArrowOne *ᵥ θ) (some s) = θ () := by
    intro θ s
    rw [tp_W_some]
    simp [mulVec, dotProduct, tpArrowOne]
  have hmem : (fun k => c k + Option.elim k (-1) fun _ => 1) ∈
      tpBudget (fun _ : Unit => (1 : ℝ)) tpArrowOne 0 := by
    refine ⟨fun _ => θ () + 1, fun k => ?_⟩
    have := hθ k
    cases k with
    | none =>
      rw [e0] at this ⊢
      simp only [Pi.zero_apply, Option.elim] at this ⊢
      linarith
    | some s =>
      rw [e1] at this ⊢
      simp only [Pi.zero_apply, Option.elim] at this ⊢
      linarith
  have := hopt _ hmem
  simp only [Option.elim] at this
  linarith

/-- AKMM, p. 477: with state prices `q`, every budget-feasible plan satisfies the single budget
constraint `cᵢ,₀ − yᵢ,₀ + Σ_ω q(ω)(cᵢ,₁(ω) − yᵢ,₁(ω)) ≤ 0`. -/
theorem tp_budget_single {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    {y c : Option S → ℝ} (hc : c ∈ tpBudget p D y) :
    c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0 := by
  obtain ⟨θ, hθ⟩ := hc
  have horth := tp_qhat_orth hq.2 θ
  rw [Fintype.sum_option] at horth
  simp only [tpQhat, Option.elim, one_mul] at horth
  have h0 := hθ none
  have hle : ∑ s, q s * (c (some s) - y (some s)) ≤ ∑ s, q s * (tpW p D *ᵥ θ) (some s) :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (by linarith [hθ (some s)])
      (hq.1 s).le
  linarith

/-- AKMM, (16.14), p. 478, as a set: the plans with `c₀ − y₀ + Σ_ω q(ω)(c₁(ω) − y₁(ω)) ≤ 0` and
`c₁ − y₁ ∈ span(D)`. -/
def tpBudgetQ (D : Matrix S N ℝ) (q : S → ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0 ∧
    (fun s => c (some s) - y (some s)) ∈ LinearMap.range D.mulVecLin}

/-- AKMM, p. 473: the budget set with binding date-1 constraints, `c₁ = y₁ + Dθ` ("since the
utility function is strictly increasing, the budget equations will bind"). -/
def tpBudgetBind (p : N → ℝ) (D : Matrix S N ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | ∃ θ, c none + p ⬝ᵥ θ ≤ y none ∧ ∀ s, c (some s) = y (some s) + (D *ᵥ θ) s}

/-- AKMM, (16.14), p. 478, corrected: under no arbitrage, with state prices `q`, the budget set
with binding date-1 constraints is `{c : c₀ − y₀ + Σ_ω q(ω)(c₁(ω) − y₁(ω)) ≤ 0,
c₁ − y₁ ∈ span(D)}`. -/
theorem eq_16_14 {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    (y : Option S → ℝ) : tpBudgetBind p D y = tpBudgetQ D q y := by
  have key : ∀ θ : N → ℝ, ∑ s, q s * (D *ᵥ θ) s = p ⬝ᵥ θ := fun θ => by
    have := tp_qhat_orth hq.2 θ
    rw [Fintype.sum_option] at this
    simp only [tpQhat, Option.elim, one_mul, tp_W_none, tp_W_some] at this
    linarith
  ext c
  constructor
  · rintro ⟨θ, h0, h1⟩
    have hc1' : ∀ s, c (some s) - y (some s) = (D *ᵥ θ) s := fun s => by
      rw [h1 s]; ring
    refine ⟨?_, θ, (funext hc1').symm⟩
    simp only [hc1']
    rw [key]
    linarith
  · rintro ⟨h0, θ, hθ⟩
    have hc1 : ∀ s, c (some s) - y (some s) = (D *ᵥ θ) s := fun s => (congrFun hθ s).symm
    refine ⟨θ, ?_, fun s => by linarith [hc1 s]⟩
    rw [← key]
    simp only [← hc1] at h0 ⊢
    linarith

/-- AKMM, p. 478: the printed claim that (16.10) "can be rewritten as" (16.14) is false: with two
states and only a bond (`q = (1/2, 1/2)`), the plan that throws away one unit in state 1 is in
(16.10) but violates the span restriction of (16.14). -/
theorem eq_16_14_counterexample :
    tpStatePrices (fun _ : Unit => (1 : ℝ)) tpBondOnly (fun _ : Fin 2 => 1 / 2) ∧
      (fun k : Option (Fin 2) => Option.elim k 0 fun s => if s = 0 then -1 else 0) ∈
        tpBudget (fun _ : Unit => (1 : ℝ)) tpBondOnly 0 ∧
      (fun k : Option (Fin 2) => Option.elim k 0 fun s => if s = 0 then -1 else 0) ∉
        tpBudgetQ tpBondOnly (fun _ : Fin 2 => 1 / 2) 0 := by
  refine ⟨⟨fun _ => by norm_num, fun _ => by simp [tpBondOnly]⟩,
    ⟨0, fun k => ?_⟩, ?_⟩
  · cases k with
    | none => simp
    | some s =>
      simp only [Option.elim, Pi.zero_apply, mulVec_zero, zero_add]
      split_ifs <;> norm_num
  · rintro ⟨-, θ, hθ⟩
    have h0 := congrFun hθ 0
    have h1 := congrFun hθ 1
    simp [mulVec, dotProduct, tpBondOnly] at h0 h1
    linarith

/-- AKMM, p. 480: with complete markets (`D` onto `ℝˢ`), the span restriction does not bind and
the budget set (16.10) is the Arrow–Debreu budget set with date-0 numeraire and state prices
`q`. -/
theorem tp_budget_complete {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    (hD : Function.Surjective D.mulVec) (y : Option S → ℝ) :
    tpBudget p D y = {c | c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0} := by
  ext c
  refine ⟨fun hc => tp_budget_single hq hc, fun hc => ?_⟩
  obtain ⟨θ, hθ⟩ := hD fun s => c (some s) - y (some s)
  have hbind : c ∈ tpBudgetBind p D y := by
    rw [eq_16_14 hq]
    exact ⟨hc, θ, hθ⟩
  obtain ⟨θ', h0, h1⟩ := hbind
  exact (eq_16_10 p D y c).2 ⟨θ', h0, fun s => (h1 s).le⟩

/-- A continuous linear functional on `ℝᴷ` is `L v = Σₖ vₖ L(eₖ)`. -/
theorem tp_clm_apply {K : Type} [Fintype K] [DecidableEq K] (L : (K → ℝ) →L[ℝ] ℝ)
    (v : K → ℝ) : L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : Pi.single k (v k) = v k • (Pi.single k (1 : ℝ) : K → ℝ) := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- AKMM, p. 479: the first-order condition for the holdings of asset `n`,
`−ψᵢpⁿ + Σ_ω ηᵢ(ω)dⁿ(ω) = 0`, where `ψᵢ = ∂Uᵢ/∂cᵢ,₀` and `ηᵢ(ω) = ∂Uᵢ/∂cᵢ,₁(ω)`, at an interior
optimum `c ≫ 0` of a differentiable utility. -/
theorem tp_portfolio_foc [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    {U : (Option S → ℝ) → ℝ} {DU : (Option S → ℝ) →L[ℝ] ℝ} {c : Option S → ℝ}
    (hc : c ∈ tpBudget p D y) (hpos : ∀ k, 0 < c k)
    (hopt : ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) (hU : HasFDerivAt U DU c) (n : N) :
    DU (Pi.single none 1) * p n = ∑ s, DU (Pi.single (some s) 1) * D s n := by
  classical
  obtain ⟨θ, hθ⟩ := hc
  set v : Option S → ℝ := tpW p D *ᵥ Pi.single n 1 with hv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c + t • v ∈ tpBudgetPos p D y := by
    have hk : ∀ k, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c k + t * v k := fun k =>
      ((by fun_prop : Continuous fun t : ℝ => c k + t * v k).tendsto' 0 (c k)
        (by simp)).eventually (lt_mem_nhds (hpos k))
    filter_upwards [Filter.eventually_all.2 hk] with t ht
    refine ⟨fun k => by simpa using (ht k).le, θ + t • Pi.single n 1, fun k => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul, hv]
    linarith [hθ k]
  have hmax : IsLocalMax (fun t : ℝ => U (c + t • v)) 0 := by
    filter_upwards [hev] with t ht
    simpa using hopt _ ht
  have hU' : HasFDerivAt U DU (c + (0 : ℝ) • v) := by simpa using hU
  have hl : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  have h0 := hmax.hasDerivAt_eq_zero (hU'.comp_hasDerivAt (0 : ℝ) hl)
  rw [tp_clm_apply DU v, Fintype.sum_option] at h0
  simp only [hv, mulVec_single_one, Matrix.col_apply, tpW, Matrix.of_apply,
    Option.elim] at h0
  have hs : ∑ s, D s n * DU (Pi.single (some s) 1) = ∑ s, DU (Pi.single (some s) 1) * D s n :=
    Finset.sum_congr rfl fun s _ => mul_comm _ _
  linarith

/-- AKMM, (16.15), p. 479: at an interior optimum with positive marginal utilities, the subjective
state prices `qᵢ(ω) = (∂Uᵢ/∂cᵢ,₁(ω))/(∂Uᵢ/∂cᵢ,₀)` are state prices: `pⁿ = Σ_ω dⁿ(ω)qᵢ(ω)`. -/
theorem eq_16_15 [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    {U : (Option S → ℝ) → ℝ} {DU : (Option S → ℝ) →L[ℝ] ℝ} {c : Option S → ℝ}
    (hc : c ∈ tpBudget p D y) (hpos : ∀ k, 0 < c k)
    (hopt : ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) (hU : HasFDerivAt U DU c)
    (hMU : ∀ k, 0 < DU (Pi.single k 1)) :
    tpStatePrices p D fun s => DU (Pi.single (some s) 1) / DU (Pi.single none 1) := by
  refine ⟨fun s => div_pos (hMU _) (hMU _), fun n => ?_⟩
  have h := tp_portfolio_foc hc hpos hopt hU n
  have h0 := (hMU none).ne'
  change p n = ∑ s, D s n * (DU (Pi.single (some s) 1) / DU (Pi.single none 1))
  have e : ∑ s, D s n * (DU (Pi.single (some s) 1) / DU (Pi.single none 1)) =
      (∑ s, DU (Pi.single (some s) 1) * D s n) / DU (Pi.single none 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, ← h]
  field_simp

/-- AKMM, p. 479: the marginal utility of the power felicity `x^{1−γ}/(1−γ)` is `x^{−γ}`. -/
theorem tp_crra_marginal {γ x : ℝ} (hγ : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun z => z ^ (1 - γ) / (1 - γ)) (x ^ (-γ)) x := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hx.ne')).div_const (1 - γ)
  convert this using 1
  rw [show (1 - γ - 1 : ℝ) = -γ by ring]
  field_simp

/-- AKMM, p. 479: with expected power utility, marginal utilities `c₀^{−γ}` and
`βπ(ω)c₁(ω)^{−γ}` give the state prices `qᵢ(ω) = βπ(ω)(cᵢ,₁(ω)/cᵢ,₀)^{−γ}`. -/
theorem tp_crra_statePrice {β pr γ c0 c1 : ℝ} (hc0 : 0 < c0) (hc1 : 0 < c1) :
    β * pr * c1 ^ (-γ) / c0 ^ (-γ) = β * pr * (c1 / c0) ^ (-γ) := by
  rw [Real.div_rpow hc1.le hc0.le, mul_div_assoc]

/-- AKMM, p. 479: a risk-neutral agent (`γ = 0`) has state prices `βπ(ω)`. -/
theorem tp_riskNeutral_statePrice (β pr c0 c1 : ℝ) :
    β * pr * (c1 / c0) ^ (-(0 : ℝ)) = β * pr := by
  simp

/-- AKMM, p. 480: agents agree on asset prices (both sets of subjective state prices price every
asset at `p`); with complete markets, `rank D = S`, they also agree on state prices. -/
theorem tp_agreement_complete {p : N → ℝ} {D : Matrix S N ℝ} {qi qj : S → ℝ}
    (hi : ∀ n, p n = ∑ s, D s n * qi s) (hj : ∀ n, p n = ∑ s, D s n * qj s)
    (hD : D.rank = Fintype.card S) : qi = qj := by
  apply (tp_rank_iff_transpose_injective D).1 hD
  funext n
  simp only [mulVec, dotProduct, transpose_apply]
  rw [← hi n, ← hj n]

end AKMM.AssetPrices
