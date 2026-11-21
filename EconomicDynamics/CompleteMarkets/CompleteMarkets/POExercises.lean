/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.POTimeZero

/-!
# Exercises 13.1 and 13.2

Miao, §13.9, p. 452.

* **Exercise 13.1** (existence of a representative agent, `ex_13_1`). `po_Ulam E λ x` is
  (13.37), the supremum of `Σᵢ λⁱ Uⁱ(cⁱ)` over the allocations of `x`. Departure: the exercise
  starts from a Radner equilibrium with nonbinding debt constraints, zero asset supply and
  complete markets, whose allocation and prices are those of an Arrow–Debreu equilibrium (§13.5;
  not part of this module). The statement proved here starts from an interior Arrow–Debreu
  equilibrium with `q⁰₀(s₀) = 1` and concave, differentiable felicity functions: with
  `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹ > 0`, the equilibrium allocation solves (13.37) at `ȳ`, and `(ȳ, q⁰)` is a
  no-trade equilibrium for the representative agent with utility `U_λ` and endowment `ȳ`.
* **Exercise 13.2** (`ex_13_2`, `ex_13_2_converse`). With a constant aggregate endowment `Y`
  and Assumption 13.1.1, the interior Pareto optimal allocations are exactly the constant ones:
  `cⁱ_t(sᵗ) = κᵢ` at all nodes of positive probability, with `Σᵢ κᵢ = Y` and
  `λⁱ uⁱ'(κᵢ)` equal across agents.
* `po_example_ADEquilibrium`: an Arrow–Debreu equilibrium exists in `po_exampleEconomy`, so
  Definition 13.3.1 is not vacuous.
-/

namespace Miao.CompleteMarkets

/-- Miao, (13.37), p. 452: the values `Σᵢ λⁱ Uⁱ(cⁱ)` attained by allocations `c ∈ (L∞₊)ᴵ` of
`x`, `Σᵢ cⁱ = x`. -/
def po_repSet {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S) (lam : ι → ℝ)
    (x : List S → ℝ) : Set ℝ :=
  {v | ∃ d : ι → List S → ℝ, (∀ i, d i ∈ po_Lplus S) ∧ (∀ h, ∑ i, d i h = x h) ∧
    v = ∑ i, lam i * po_U E i (d i)}

/-- Miao, (13.37), p. 452: the representative agent's utility
`U_λ(x) = sup {Σᵢ λⁱ Uⁱ(cⁱ) : Σᵢ cⁱ = x}`. -/
noncomputable def po_Ulam {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (lam : ι → ℝ) (x : List S → ℝ) : ℝ :=
  sSup (po_repSet E lam x)

/-- **Exercise 13.1** (Existence of a representative agent, Miao, p. 452), for an interior
Arrow–Debreu equilibrium `(c, q⁰)` with `q⁰₀(s₀) = 1`: with `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹ > 0`, the
allocation `c` solves (13.37) at `ȳ = Σᵢ yⁱ`, `U_λ(ȳ) = Σᵢ λᵢ Uⁱ(cⁱ)`, and `ȳ` maximises `U_λ`
over the representative agent's budget set `{x ∈ L∞₊ : q⁰ · x ≤ q⁰ · ȳ}`, so `(ȳ, q⁰)` is a
no-trade equilibrium. -/
theorem ex_13_1 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y : ι → List S → ℝ} {q : List S → ℝ}
    {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c) (hq0 : q [] = 1)
    (hpos : ∀ i h, 0 < c i h) (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) :
    (∀ i, 0 < (deriv (E.u i) (c i []))⁻¹) ∧
      IsGreatest (po_repSet E (fun i => (deriv (E.u i) (c i []))⁻¹) (fun h => ∑ i, y i h))
        (∑ i, (deriv (E.u i) (c i []))⁻¹ * po_U E i (c i)) ∧
      po_Ulam E (fun i => (deriv (E.u i) (c i []))⁻¹) (fun h => ∑ i, y i h) =
        ∑ i, (deriv (E.u i) (c i []))⁻¹ * po_U E i (c i) ∧
      ∀ x ∈ po_Lplus S, po_cost q x ≤ po_cost q (fun h => ∑ i, y i h) →
        po_Ulam E (fun i => (deriv (E.u i) (c i []))⁻¹) x ≤
          po_Ulam E (fun i => (deriv (E.u i) (c i []))⁻¹) (fun h => ∑ i, y i h) := by
  set μ : ι → ℝ := fun i => deriv (E.u i) (c i []) with hμdef
  have hμ : ∀ i, 0 < μ i := fun i =>
    po_deriv_pos (hconc i) (E.u_mono i) (hpos i []) (hdiff i [])
  set ybar : List S → ℝ := fun h => ∑ i, y i h
  have hq := hE.1
  have hc := hE.2.1
  -- the key bound: any allocation `d` of `x` gives at most `Σ λU(c) + q·x − q·ȳ`
  have key : ∀ x, ∀ d : ι → List S → ℝ, (∀ i, d i ∈ po_Lplus S) → (∀ h, ∑ i, d i h = x h) →
      ∑ i, (μ i)⁻¹ * po_U E i (d i) ≤
        ∑ i, (μ i)⁻¹ * po_U E i (c i) + (po_cost q x - po_cost q ybar) := by
    intro x d hd hdx
    have hgain : ∀ i, (μ i)⁻¹ * po_U E i (d i) - (μ i)⁻¹ * po_U E i (c i) ≤
        po_cost q (d i) - po_cost q (c i) := by
      intro i
      have := po_utility_gain_le E i (hconc i) (hc.1 i) (hpos i) (hdiff i) hq (μ i)
        (eq_13_6 E hE hq0 i (hpos i) (hdiff i)) (hd i)
      have := mul_le_mul_of_nonneg_left this (inv_pos.mpr (hμ i)).le
      rw [← mul_assoc, inv_mul_cancel₀ (hμ i).ne', one_mul] at this
      linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hgain i
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      po_sum_cost hq fun i => po_Lplus_subset_Linfty (hd i),
      po_sum_cost hq fun i => po_Lplus_subset_Linfty (hc.1 i)] at hsum
    have e1 : (fun h => ∑ i, d i h) = x := funext hdx
    have e2 : (fun h => ∑ i, c i h) = ybar := funext hc.2
    rw [e1, e2] at hsum
    linarith
  have hgreat : IsGreatest (po_repSet E (fun i => (μ i)⁻¹) ybar)
      (∑ i, (μ i)⁻¹ * po_U E i (c i)) := by
    refine ⟨⟨c, hc.1, hc.2, rfl⟩, ?_⟩
    rintro v ⟨d, hd, hdx, rfl⟩
    have := key ybar d hd hdx
    linarith
  have hval := hgreat.csSup_eq
  refine ⟨fun i => inv_pos.mpr (hμ i), hgreat, hval, fun x hx hxb => ?_⟩
  unfold po_Ulam
  rw [hval]
  obtain i₀ : ι := Classical.arbitrary ι
  classical
  have hne : (po_repSet E (fun i => (μ i)⁻¹) x).Nonempty := by
    have h0 : (fun _ : List S => (0 : ℝ)) ∈ po_Lplus S :=
      ⟨fun _ => le_rfl, 0, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
    refine ⟨_, fun i => if i = i₀ then x else fun _ => 0, fun i => ?_, fun h => ?_, rfl⟩
    · by_cases hi : i = i₀
      · simp only [hi, ↓reduceIte]; exact hx
      · simp only [hi, ↓reduceIte]; exact h0
    · simp only [apply_ite (fun f : List S → ℝ => f h), Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
  refine csSup_le hne ?_
  rintro v ⟨d, hd, hdx, rfl⟩
  have := key x d hd hdx
  linarith

/-- **Exercise 13.2** (Miao, p. 452). If the aggregate endowment is constant, `Σᵢ yⁱ_t(sᵗ) = Y`,
and each `uⁱ` satisfies Assumption 13.1.1, then an interior Pareto optimal allocation is
constant over time and states: `cⁱ_t(sᵗ) = cⁱ₀(s₀) =: κᵢ` at every node of positive
probability, where `Σᵢ κᵢ = Y` and, for some weights `λ > 0`, `λⁱ uⁱ'(κᵢ) = λʲ uʲ'(κⱼ)`. -/
theorem ex_13_2 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hA : ∀ i, Assumption13_1_1 (E.u i)) {y c : ι → List S → ℝ} {Y : ℝ}
    (hY : ∀ h, ∑ i, y i h = Y) (hpo : po_ParetoOptimal E y c) (hpos : ∀ i h, 0 < c i h) :
    (∀ i h, 0 < po_w E h → c i h = c i []) ∧ ∑ i, c i [] = Y ∧
      ∃ lam : ι → ℝ, (∀ i, 0 < lam i) ∧
        ∀ i j, lam i * deriv (E.u i) (c i []) = lam j * deriv (E.u j) (c j []) := by
  have hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i) := fun i => (hA i).2.2.2.1.concaveOn
  have hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h) := fun i h =>
    po_differentiableAt (hA i) (hpos i h)
  obtain ⟨lam, hlam, -, hfoc⟩ := po_pareto_foc E hconc hpo hpos hdiff
  have hw0 : 0 < po_w E [] := by rw [po_w_root]; exact one_pos
  refine ⟨fun i h hw => po_risk_sharing E hpo.1 hlam (fun k => po_strictAntiOn_deriv (hA k))
      hpos hfoc hw hw0 (by rw [hY, hY]) i, by rw [hpo.1.2, hY], lam, hlam, hfoc [] hw0⟩

/-- **Exercise 13.2** (Miao, p. 452), converse. With a constant aggregate endowment `Y` and each
`uⁱ` satisfying Assumption 13.1.1, every constant allocation `cⁱ_t(sᵗ) = κᵢ > 0` with
`Σᵢ κᵢ = Y` is Pareto optimal (it solves the planner's problem with `λᵢ = uⁱ'(κᵢ)⁻¹`). -/
theorem ex_13_2_converse {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hA : ∀ i, Assumption13_1_1 (E.u i)) {y : ι → List S → ℝ} {Y : ℝ}
    (hY : ∀ h, ∑ i, y i h = Y) {κ : ι → ℝ} (hκ : ∀ i, 0 < κ i) (hsum : ∑ i, κ i = Y) :
    po_ParetoOptimal E y (fun i _ => κ i) := by
  have hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i) := fun i => (hA i).2.2.2.1.concaveOn
  have hd : ∀ i, 0 < deriv (E.u i) (κ i) := fun i =>
    po_deriv_pos (hconc i) (E.u_mono i) (hκ i) (po_differentiableAt (hA i) (hκ i))
  have hfeas : po_Feasible y (fun i _ => κ i) :=
    ⟨fun i => ⟨fun _ => (hκ i).le, κ i, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩,
      fun h => by rw [hsum, hY]⟩
  have hξ : po_w E ∈ po_L1 S := by
    change Summable fun h => |po_w E h|
    simp only [abs_of_nonneg (po_w_nonneg E _)]
    exact po_summable_w E
  refine po_pareto_of_planner_pos E (fun i => inv_pos.mpr (hd i))
    (po_planner_of_foc E hconc hfeas (fun i _ => hκ i)
      (fun i _ => po_differentiableAt (hA i) (hκ i)) (fun i => inv_pos.mpr (hd i)) hξ
      fun i h => ?_)
  field_simp [(hd i).ne']

/-- Miao, Definition 13.3.1 is not vacuous: in `po_exampleEconomy` with both agents endowed
with one unit at every node, autarky `cⁱ = yⁱ` is an Arrow–Debreu equilibrium at some prices
`q⁰ ∈ L¹` with `q⁰₀(s₀) = 1` (by `ex_13_2_converse` and `theorem_13_3_2`). -/
theorem po_example_ADEquilibrium :
    ∃ q : List Bool → ℝ, q [] = 1 ∧
      po_ADEquilibrium po_exampleEconomy (fun _ _ => 1) q (fun _ _ => 1) := by
  have hA := po_exampleEconomy_assumption
  have hpo : po_ParetoOptimal po_exampleEconomy (fun _ _ => (1 : ℝ)) (fun _ _ => 1) :=
    ex_13_2_converse po_exampleEconomy hA (Y := 2) (fun _ => by simp)
      (κ := fun _ => 1) (fun _ => one_pos) (by simp)
  exact theorem_13_3_2 po_exampleEconomy (fun i => (hA i).2.2.2.1.concaveOn)
    (fun i _ hx => po_differentiableAt (hA i) hx) hpo one_pos (fun _ _ => le_rfl)

end Miao.CompleteMarkets
