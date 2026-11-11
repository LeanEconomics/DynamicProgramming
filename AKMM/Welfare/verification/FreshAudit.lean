import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import AKMMCompetitiveEquilibrium.ADConsumer
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IntermediateValue
import AKMMCompetitiveEquilibrium.OGEconomies
import AKMMCompetitiveEquilibrium.Sequential
import OverlappingGenerations.OPEfficiency
import Mathlib.Topology.Order.MonotoneConvergence
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The First Welfare Theorem in the abstract economy

AKMM, §6.1, pp. 160–162, and §6.3.1, pp. 167–168. A finite set `I` of consumers and `J` of
firms, a finite set `G` of goods; bundles are vectors `G → ℝ` (negative entries allowed).
Consumer `i` has a consumption set `Xᵢ`, a weak preference `Rᵢ` (`Rᵢ x y`: `x` is at least as
good as `y`; `x ≻ y` is `Rᵢ x y ∧ ¬Rᵢ y x`), endowment `ωᵢ` and shares `θᵢⱼ` with
`Σᵢ θᵢⱼ = 1`; firm `j` has a production set `Yⱼ`.

* Feasibility (6.1) `Σ xᵢ ≤ Σ yⱼ + Σ ωᵢ` (`fwFeasible`), Pareto optimality (`fwParetoOptimal`),
  local nonsatiation (`fwLNS`) and the book's competitive equilibrium (`fwCompEq`), with
  lump-sum transfers `Tᵢ` added to incomes (`fwCompEqT`).
* **Theorem 6.1** (`theorem_6_1`) by the book's proof: a dominating feasible allocation costs
  weakly more for everyone and strictly more for someone (`fw_value_ge`, `fw_value_gt`), which
  contradicts the summed budgets, profit maximisation and feasibility.
* Lump-sum taxes summing to zero keep the equilibrium Pareto optimal (§6.3.1, fn. 3:
  `fwt_lump_sum`).
* Endowment economies, `Yⱼ = {0}`, are a special case; a concrete equilibrium satisfies every
  hypothesis (`theorem_6_1_instance`).
* §6.3.1, labour taxes: with inelastic labour a proportional tax does not change the labour
  choice and acts as a lump-sum tax (`tax_inelastic_labour`); with valued leisure it drives a
  wedge `(1 − τ)` between the marginal rate of substitution and the marginal product
  (`tax_labour_wedge`).

**Correction.** The last step of the proof multiplies the resource constraint (6.1), an
inequality, by `p`; this needs `p ≥ 0`, which the book does not state. Without it the theorem is
false (`theorem_6_1_counterexample`: a bad with a negative price). `p ≥ 0` holds automatically
when some consumer can always add a unit of any good and strictly prefers to
(`fw_price_nonneg`).
-/

namespace AKMM.Welfare

variable {G I J : Type*} [Fintype G] [Fintype I] [Fintype J]

/-- The value `p · x = Σ_g p_g x_g` of a bundle. -/
def fwValue (p x : G → ℝ) : ℝ := ∑ g, p g * x g

/-- Strict preference from a weak preference: `x ≻ y` iff `x ≿ y` and not `y ≿ x`. -/
def fwStrict (R : (G → ℝ) → (G → ℝ) → Prop) (x y : G → ℝ) : Prop := R x y ∧ ¬ R y x

/-- AKMM, (6.1), p. 160: an allocation is feasible if each `xᵢ ∈ Xᵢ`, each `yⱼ ∈ Yⱼ` and
`Σᵢ xᵢ ≤ Σⱼ yⱼ + Σᵢ ωᵢ` good by good. -/
def fwFeasible (X : I → Set (G → ℝ)) (Y : J → Set (G → ℝ)) (ω : I → G → ℝ)
    (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  (∀ i, x i ∈ X i) ∧ (∀ j, y j ∈ Y j) ∧ ∀ g, ∑ i, x i g ≤ ∑ j, y j g + ∑ i, ω i g

/-- AKMM, p. 161: a feasible allocation is Pareto optimal if no feasible allocation is weakly
preferred by every consumer and strictly preferred by one. -/
def fwParetoOptimal (X : I → Set (G → ℝ)) (R : I → (G → ℝ) → (G → ℝ) → Prop)
    (Y : J → Set (G → ℝ)) (ω : I → G → ℝ) (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  fwFeasible X Y ω x y ∧ ¬ ∃ x' y', fwFeasible X Y ω x' y' ∧ (∀ i, R i (x' i) (x i)) ∧
    ∃ i, fwStrict (R i) (x' i) (x i)

/-- AKMM, p. 160: local nonsatiation. For every `z ∈ Xᵢ` and `ε > 0` there is a strictly
preferred `z′ ∈ Xᵢ` within `ε` of `z` in every good. -/
def fwLNS (X : I → Set (G → ℝ)) (R : I → (G → ℝ) → (G → ℝ) → Prop) : Prop :=
  ∀ i, ∀ z ∈ X i, ∀ ε : ℝ, 0 < ε → ∃ z' ∈ X i, (∀ g, |z' g - z g| < ε) ∧ fwStrict (R i) z' z

/-- AKMM, pp. 160–161 and §6.3.1: a competitive equilibrium in which consumer `i` also receives
the lump-sum transfer `Tᵢ`. (1) `xᵢ ∈ Xᵢ`, `p·xᵢ = p·ωᵢ + Σⱼ θᵢⱼ p·yⱼ + Tᵢ` and no `z ∈ Xᵢ`
with `z ≻ xᵢ` and `p·z ≤ p·xᵢ`; (2) `yⱼ ∈ Yⱼ` maximises `p·y` on `Yⱼ`; (3) every market
clears with equality. -/
def fwCompEqT (X : I → Set (G → ℝ)) (R : I → (G → ℝ) → (G → ℝ) → Prop)
    (Y : J → Set (G → ℝ)) (ω : I → G → ℝ) (θ : I → J → ℝ) (T : I → ℝ) (x : I → G → ℝ)
    (y : J → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ i, x i ∈ X i ∧
      fwValue p (x i) = fwValue p (ω i) + ∑ j, θ i j * fwValue p (y j) + T i ∧
      ¬ ∃ z ∈ X i, fwStrict (R i) z (x i) ∧ fwValue p z ≤ fwValue p (x i)) ∧
    (∀ j, y j ∈ Y j ∧ ∀ w ∈ Y j, fwValue p w ≤ fwValue p (y j)) ∧
    ∀ g, ∑ i, x i g = ∑ j, y j g + ∑ i, ω i g

/-- **AKMM, p. 160: the competitive equilibrium** `({xᵢ⋆}, {yⱼ⋆}, p⋆)` (no transfers). -/
def fwCompEq (X : I → Set (G → ℝ)) (R : I → (G → ℝ) → (G → ℝ) → Prop)
    (Y : J → Set (G → ℝ)) (ω : I → G → ℝ) (θ : I → J → ℝ) (x : I → G → ℝ)
    (y : J → G → ℝ) (p : G → ℝ) : Prop :=
  fwCompEqT X R Y ω θ (fun _ => 0) x y p

omit [Fintype I] in
/-- AKMM, proof of Theorem 6.1, p. 161 ("the first property of a competitive equilibrium
combined with LNS"): under local nonsatiation and transitivity, a bundle weakly preferred to the
equilibrium bundle costs at least as much. -/
theorem fw_value_ge {X : I → Set (G → ℝ)} {R : I → (G → ℝ) → (G → ℝ) → Prop}
    (htrans : ∀ i a b c, R i a b → R i b c → R i a c) (hlns : fwLNS X R) {i : I}
    {xi z : G → ℝ} (hz : z ∈ X i) (hpref : R i z xi) {p : G → ℝ}
    (hopt : ¬ ∃ z ∈ X i, fwStrict (R i) z xi ∧ fwValue p z ≤ fwValue p xi) :
    fwValue p xi ≤ fwValue p z := by
  by_contra hlt
  push Not at hlt
  set S := ∑ g, |p g| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun g _ => abs_nonneg _
  set ε := (fwValue p xi - fwValue p z) / (S + 1) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨z', hz', hclose, hstr⟩ := hlns i z hz ε hεpos
  have hdiff : fwValue p z' - fwValue p z ≤ S * ε := by
    have e : fwValue p z' - fwValue p z = ∑ g, p g * (z' g - z g) := by
      simp only [fwValue, ← Finset.sum_sub_distrib, mul_sub]
    rw [e, hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun g _ => ?_
    calc p g * (z' g - z g) ≤ |p g * (z' g - z g)| := le_abs_self _
      _ = |p g| * |z' g - z g| := abs_mul _ _
      _ ≤ |p g| * ε := mul_le_mul_of_nonneg_left (hclose g).le (abs_nonneg _)
  have hSε : (S + 1) * ε = fwValue p xi - fwValue p z := by
    rw [hε]; field_simp
  have hcheap : fwValue p z' ≤ fwValue p xi := by nlinarith
  refine hopt ⟨z', hz', ⟨htrans i _ _ _ hstr.1 hpref, fun hback => hstr.2 ?_⟩, hcheap⟩
  exact htrans i _ _ _ hpref hback

/-- AKMM, proof of Theorem 6.1, p. 161: a bundle strictly preferred to the equilibrium bundle
costs strictly more. -/
theorem fw_value_gt {X : Set (G → ℝ)} {R : (G → ℝ) → (G → ℝ) → Prop} {xi z p : G → ℝ}
    (hz : z ∈ X) (hstr : fwStrict R z xi)
    (hopt : ¬ ∃ z ∈ X, fwStrict R z xi ∧ fwValue p z ≤ fwValue p xi) :
    fwValue p xi < fwValue p z := by
  by_contra hle
  push Not at hle
  exact hopt ⟨z, hz, hstr, hle⟩

/-- The value of a sum of bundles is the sum of the values. -/
theorem fw_value_sum {K : Type*} [Fintype K] (p : G → ℝ) (x : K → G → ℝ) :
    ∑ k, fwValue p (x k) = ∑ g, p g * ∑ k, x k g := by
  simp only [fwValue, Finset.mul_sum]
  exact Finset.sum_comm

/-- **AKMM, §6.3.1 and fn. 3, p. 167: lump-sum taxes.** If the transfers sum to zero
(`Σᵢ Tᵢ = 0`; the government is one more consumer), preferences are transitive and locally
nonsatiated, the shares sum to one and prices are nonnegative, a competitive equilibrium with
transfers is Pareto optimal. -/
theorem fwt_lump_sum {X : I → Set (G → ℝ)} {R : I → (G → ℝ) → (G → ℝ) → Prop}
    {Y : J → Set (G → ℝ)} {ω : I → G → ℝ} {θ : I → J → ℝ} {T : I → ℝ} {x : I → G → ℝ}
    {y : J → G → ℝ} {p : G → ℝ} (htrans : ∀ i a b c, R i a b → R i b c → R i a c)
    (hlns : fwLNS X R) (hθ : ∀ j, ∑ i, θ i j = 1) (hT : ∑ i, T i = 0) (hp : ∀ g, 0 ≤ p g)
    (he : fwCompEqT X R Y ω θ T x y p) : fwParetoOptimal X R Y ω x y := by
  obtain ⟨hcons, hfirm, hclear⟩ := he
  refine ⟨⟨fun i => (hcons i).1, fun j => (hfirm j).1, fun g => (hclear g).le⟩, ?_⟩
  rintro ⟨x', y', ⟨hx', hy', hres⟩, hpref, i₀, hstr⟩
  have hge : ∀ i, fwValue p (x i) ≤ fwValue p (x' i) := fun i =>
    fw_value_ge htrans hlns (hx' i) (hpref i) (hcons i).2.2
  have hgt : fwValue p (x i₀) < fwValue p (x' i₀) := fw_value_gt (hx' i₀) hstr (hcons i₀).2.2
  have hsum : ∑ i, fwValue p (x i) < ∑ i, fwValue p (x' i) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i₀, Finset.mem_univ _, hgt⟩
  -- summed budgets
  have hbud : ∑ i, fwValue p (x i) = ∑ i, fwValue p (ω i) + ∑ j, fwValue p (y j) := by
    rw [Finset.sum_congr rfl fun i _ => (hcons i).2.1, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hT, add_zero, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hθ j, one_mul]
  -- profit maximisation
  have hprof : ∑ j, fwValue p (y' j) ≤ ∑ j, fwValue p (y j) :=
    Finset.sum_le_sum fun j _ => (hfirm j).2 _ (hy' j)
  -- feasibility times `p ≥ 0`
  have hfeas : ∑ i, fwValue p (x' i) ≤ ∑ i, fwValue p (ω i) + ∑ j, fwValue p (y' j) := by
    rw [fw_value_sum, fw_value_sum, fw_value_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith [hres g]) (hp g)
  linarith

/-- **Theorem 6.1** (the First Welfare Theorem, AKMM, p. 161). An allocation that is part of a
competitive equilibrium is Pareto optimal, under local nonsatiation, with transitive
preferences, shares summing to one, and (a hypothesis the book's proof uses but does not state)
nonnegative prices. -/
theorem theorem_6_1 {X : I → Set (G → ℝ)} {R : I → (G → ℝ) → (G → ℝ) → Prop}
    {Y : J → Set (G → ℝ)} {ω : I → G → ℝ} {θ : I → J → ℝ} {x : I → G → ℝ} {y : J → G → ℝ}
    {p : G → ℝ} (htrans : ∀ i a b c, R i a b → R i b c → R i a c) (hlns : fwLNS X R)
    (hθ : ∀ j, ∑ i, θ i j = 1) (hp : ∀ g, 0 ≤ p g) (he : fwCompEq X R Y ω θ x y p) :
    fwParetoOptimal X R Y ω x y :=
  fwt_lump_sum htrans hlns hθ (by simp) hp he

/-- AKMM, p. 161 (correction): equilibrium prices are nonnegative when some consumer can add a
unit of any good to her equilibrium bundle and strictly prefers to (strict monotonicity). -/
theorem fw_price_nonneg {X : I → Set (G → ℝ)} {R : I → (G → ℝ) → (G → ℝ) → Prop}
    {Y : J → Set (G → ℝ)} {ω : I → G → ℝ} {θ : I → J → ℝ} {T : I → ℝ} {x : I → G → ℝ}
    {y : J → G → ℝ} {p : G → ℝ} [DecidableEq G] (he : fwCompEqT X R Y ω θ T x y p) (i : I)
    (hmono : ∀ g, x i + Pi.single g 1 ∈ X i ∧ fwStrict (R i) (x i + Pi.single g 1) (x i))
    (g : G) : 0 ≤ p g := by
  by_contra hneg
  push Not at hneg
  refine (he.1 i).2.2 ⟨_, (hmono g).1, (hmono g).2, ?_⟩
  have e : fwValue p (x i + Pi.single g 1) = fwValue p (x i) + p g := by
    simp only [fwValue, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single g (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [e]
  linarith

/-- The counterexample economy: one consumer, two goods, good 1 a bad
(`x ≿ y` iff `x₀ − x₁ ≥ y₀ − y₁`), consumption set `ℝ²₊`, endowment `(1, 1)`, one firm with
`Y = {0}`. -/
def fwBadPref (x y : Fin 2 → ℝ) : Prop := y 0 - y 1 ≤ x 0 - x 1

/-- **AKMM, Theorem 6.1, p. 161: the printed statement needs `p ≥ 0`.** In the economy
`fwBadPref`, the prices `p = (1, −1)` and the allocation `x = (1, 1)` form a competitive
equilibrium with transitive, locally nonsatiated preferences, but the feasible allocation
`(1, 0)` (dispose of the bad, allowed by the inequality (6.1)) is strictly preferred. -/
theorem theorem_6_1_counterexample :
    fwCompEq (I := Unit) (J := Unit) (fun _ => {z | ∀ g, 0 ≤ z g}) (fun _ => fwBadPref)
      (fun _ => {0}) (fun _ => fun _ => 1) (fun _ _ => 1) (fun _ => fun _ => 1) (fun _ => 0)
      ![1, -1] ∧
    fwLNS (I := Unit) (fun _ => {z | ∀ g, 0 ≤ z g}) (fun _ => fwBadPref) ∧
    (∀ i a b c, (fun _ => fwBadPref) i a b → (fun (_ : Unit) => fwBadPref) i b c →
      (fun (_ : Unit) => fwBadPref) i a c) ∧
    ¬ fwParetoOptimal (I := Unit) (J := Unit) (fun _ => {z | ∀ g, 0 ≤ z g})
      (fun _ => fwBadPref) (fun _ => {0}) (fun _ => fun _ => 1) (fun _ => fun _ => 1)
      (fun _ => 0) := by
  refine ⟨⟨fun _ => ⟨fun g => by fin_cases g <;> simp, ?_, ?_⟩, fun _ => ⟨rfl, ?_⟩,
    fun g => by simp⟩, ?_, ?_, ?_⟩
  · simp [fwValue, Fin.sum_univ_two]
  · rintro ⟨z, -, ⟨-, h1⟩, h2⟩
    simp only [fwBadPref, fwValue, Fin.sum_univ_two] at h1 h2
    simp at h1 h2
    linarith
  · rintro w hw
    simp only [Set.mem_singleton_iff] at hw
    simp [hw, fwValue]
  · intro _ z hz ε hε
    refine ⟨z + Pi.single 0 (ε / 2), fun g => ?_, fun g => ?_, ?_, ?_⟩
    · fin_cases g <;> simp <;> linarith [hz 0, hz 1]
    · fin_cases g <;> simp [abs_of_pos (half_pos hε)] <;> linarith
    · simp only [fwBadPref, Pi.add_apply]; simp; linarith
    · simp only [fwBadPref, Pi.add_apply]; simp; linarith
  · intro _ a b c h1 h2
    simp only [fwBadPref] at *
    linarith
  · rintro ⟨-, hno⟩
    refine hno ⟨fun _ => ![1, 0], fun _ => 0, ⟨fun _ g => ?_, fun _ => rfl, fun g => ?_⟩,
      fun _ => ?_, (), ?_, ?_⟩
    · fin_cases g <;> simp
    · fin_cases g <;> simp
    · simp [fwBadPref]
    · simp [fwBadPref]
    · simp [fwBadPref]

/-- **Theorem 6.1, a concrete instance** (AKMM, p. 161): in the one-consumer endowment economy
with two goods, `x ≿ y` iff `x₀ + x₁ ≥ y₀ + y₁` on `ℝ²₊`, endowment `(1, 1)`, `Y = {0}`
(an endowment economy), the prices `(1, 1)` and the allocation `(1, 1)` are an equilibrium,
every hypothesis of `theorem_6_1` holds, and the allocation is Pareto optimal. -/
theorem theorem_6_1_instance :
    fwParetoOptimal (I := Unit) (J := Unit) (fun _ => {z : Fin 2 → ℝ | ∀ g, 0 ≤ z g})
      (fun _ x y => y 0 + y 1 ≤ x 0 + x 1) (fun _ => {0}) (fun _ => fun _ => 1)
      (fun _ => fun _ => 1) (fun _ => 0) := by
  refine theorem_6_1 (θ := fun _ _ => 1) (p := fun _ => 1) (fun _ a b c h1 h2 => by linarith)
    ?_ (fun _ => by simp) (fun _ => zero_le_one) ⟨fun _ => ⟨fun g => zero_le_one, ?_, ?_⟩,
      fun _ => ⟨rfl, ?_⟩, fun g => by simp⟩
  · intro _ z hz ε hε
    refine ⟨z + Pi.single 0 (ε / 2), fun g => ?_, fun g => ?_, ?_, ?_⟩
    · fin_cases g <;> simp <;> linarith [hz 0, hz 1]
    · fin_cases g <;> simp [abs_of_pos (half_pos hε)] <;> linarith
    · simp; linarith
    · simp; linarith
  · simp [fwValue]
  · rintro ⟨z, -, ⟨-, h1⟩, h2⟩
    simp only [fwValue, Fin.sum_univ_two] at h1 h2
    simp at h1 h2
    linarith
  · rintro w hw
    simp only [Set.mem_singleton_iff] at hw
    simp [hw, fwValue]

/-- **AKMM, §6.3.1, p. 167: a proportional labour tax with inelastic labour.** If utility
depends only on consumption and is strictly increasing, the wage is positive and `τ < 1`, the
optimal choice of hours `ℓ ∈ [0, 1]` and consumption `c ≤ (1 − τ)wℓ + m` is `ℓ = 1`,
`c = (1 − τ)w + m`: hours do not depend on `τ`, and the allocation is the one under a lump-sum
tax `τw`. -/
theorem tax_inelastic_labour {u : ℝ → ℝ} (hu : StrictMono u) {w τ m c l : ℝ} (hw : 0 < w)
    (hτ : τ < 1) (hl : 0 ≤ l ∧ l ≤ 1) (hc : c ≤ (1 - τ) * w * l + m)
    (hopt : ∀ c' l', 0 ≤ l' → l' ≤ 1 → c' ≤ (1 - τ) * w * l' + m → u c' ≤ u c) :
    l = 1 ∧ c = (1 - τ) * w + m ∧ c = w + m - τ * w := by
  have hmax : (1 - τ) * w + m ≤ c := hu.le_iff_le.1 (hopt _ 1 zero_le_one le_rfl (by ring_nf; rfl))
  have hpos : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  have hl1 : l = 1 := by
    by_contra hne
    have : l < 1 := lt_of_le_of_ne hl.2 hne
    nlinarith
  subst hl1
  refine ⟨rfl, by linarith, by linarith⟩

/-- **AKMM, §6.3.1, pp. 167–168: the labour-tax wedge.** If the consumer's first-order condition
is `(1 − τ)w·u′(c) = v′(ℓ)` and the firm pays the marginal product, `w = MPL`, the marginal rate of
substitution `v′(ℓ)/u′(c)` equals `(1 − τ)·MPL`; it differs from the marginal rate of
transformation `MPL` whenever `τ ≠ 0` (and `MPL ≠ 0`). -/
theorem tax_labour_wedge {τ w mpl du dv : ℝ} (hdu : du ≠ 0) (hfoc : (1 - τ) * w * du = dv)
    (hfirm : w = mpl) : dv / du = (1 - τ) * mpl ∧ (τ ≠ 0 → mpl ≠ 0 → dv / du ≠ mpl) := by
  subst hfirm
  have e : dv / du = (1 - τ) * w := by rw [← hfoc]; field_simp
  refine ⟨e, fun hτ hm h => ?_⟩
  rw [e] at h
  have : τ * w = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hτ h1
  · exact hm h1

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinite horizons and the Pareto frontier

AKMM, §6.1 ("Infinite horizon models"), p. 162, and §6.2, pp. 164–167. Finitely many
infinitely lived consumers `i : I` in an exchange economy with one good per date, endowments
`ω_{i,t}`, common utility `Σ βᵗu(c_{i,t})`. The consumer's date-0 problem is Chapter 5's
`ADOptimal` (AKMM `CompetitiveEquilibrium`), with positive consumption and a convergent budget.

* The competitive equilibrium (`dyCompEq`), feasibility (`dyFeasible`) and Pareto optimality
  (`dyParetoOptimal`) among allocations whose utility series converge.
* **The First Welfare Theorem with infinitely many goods** (p. 162): when the value of each
  endowment `Σ pₜω_{i,t}` is finite, every equilibrium is Pareto optimal (`fwt_dynastic`). The
  values of feasible allocations are then finite as well (`dy_value_summable`), and local
  nonsatiation holds by adding consumption at date 0 (`dy_lns`).
* **§6.2.** (6.2) `c_{i,t} = (u′)⁻¹(β^{−t}λᵢpₜ)` (`eq_6_2`, from Chapter 5's `ad_foc_multiplier`);
  the planner's problem (`dyPlannerOptimal`) and its solutions are Pareto optimal
  (`negishi_planner_pareto`); the planner's first-order condition `µᵢβᵗu′(c_{i,t}) = ψₜ`
  (`dy_planner_foc`) and (6.3) `c_{i,t} = (u′)⁻¹(β^{−t}ψₜ/µᵢ)` (`eq_6_3`); with `µᵢ = 1/λᵢ` and
  `ψₜ = pₜ` the two give the same allocation (`negishi_coincide`), and market clearing forces
  `ψₜ = pₜ` (`negishi_psi_eq_p`); with concave `u` the equilibrium allocation solves the planner's
  problem with weights `µᵢ = 1/λᵢ` (`negishi_ce_solves_planner`) and is therefore Pareto optimal
  (`negishi_fwt`).

The Second Welfare Theorem is mentioned but not stated by the book (p. 166); it is not
formalised here.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium

variable {I : Type*} [Fintype I]

/-- AKMM, p. 164: a feasible allocation of the dynastic exchange economy: positive consumption
and `Σᵢ c_{i,t} ≤ Σᵢ ω_{i,t}` at every date. -/
def dyFeasible (ω c : I → ℕ → ℝ) : Prop :=
  (∀ i t, 0 < c i t) ∧ ∀ t, ∑ i, c i t ≤ ∑ i, ω i t

/-- Lifetime utility `Σ βᵗu(cₜ)`. -/
noncomputable def dyU (u : ℝ → ℝ) (β : ℝ) (c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * u (c t)

/-- AKMM, p. 164: Pareto optimality among feasible allocations with convergent utility
series. -/
def dyParetoOptimal (u : ℝ → ℝ) (β : ℝ) (ω c : I → ℕ → ℝ) : Prop :=
  dyFeasible ω c ∧ (∀ i, Summable fun t => β ^ t * u (c i t)) ∧
    ¬ ∃ d : I → ℕ → ℝ, dyFeasible ω d ∧ (∀ i, Summable fun t => β ^ t * u (d i t)) ∧
      (∀ i, dyU u β (c i) ≤ dyU u β (d i)) ∧ ∃ i, dyU u β (c i) < dyU u β (d i)

/-- AKMM, p. 165: a competitive equilibrium with date-0 trading and finitely many consumers:
each endowment has finite value, each `cᵢ` solves Chapter 5's date-0 problem with wealth
`Σ pₜω_{i,t}`, and markets clear. -/
def dyCompEq (u : ℝ → ℝ) (β : ℝ) (ω c : I → ℕ → ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ i, Summable fun t => p t * ω i t) ∧ (∀ i, ADOptimal u β p (∑' t, p t * ω i t) (c i)) ∧
    ∀ t, ∑ i, c i t = ∑ i, ω i t

/-- AKMM, p. 162: with positive prices and endowments of finite value, every feasible
allocation has finite value: `Σ pₜd_{i,t}` converges. -/
theorem dy_value_summable {ω d : I → ℕ → ℝ} {p : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hω : ∀ i, Summable fun t => p t * ω i t) (hd : dyFeasible ω d) (i : I) :
    Summable fun t => p t * d i t := by
  classical
  refine Summable.of_nonneg_of_le (fun t => (mul_pos (hp t) (hd.1 i t)).le) (fun t => ?_)
    (summable_sum fun k (_ : k ∈ Finset.univ) => hω k)
  have h1 : d i t ≤ ∑ k, d k t :=
    Finset.single_le_sum (f := fun k => d k t) (fun k _ => (hd.1 k t).le) (Finset.mem_univ i)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (h1.trans (hd.2 t)) (hp t).le

/-- AKMM, p. 160 (local nonsatiation in the dynastic economy): if `u` is strictly increasing,
a positive plan of finite value below `W` can be improved within the budget `Σ pₜcₜ = W` by
adding consumption at date 0. -/
theorem dy_lns {u : ℝ → ℝ} (hu : StrictMonoOn u (Set.Ioi 0)) {β : ℝ} {p x : ℕ → ℝ} {W : ℝ}
    (hp : ∀ t, 0 < p t) (hx : ∀ t, 0 < x t) (hxs : Summable fun t => p t * x t)
    (hxU : Summable fun t => β ^ t * u (x t)) (hlt : ∑' t, p t * x t < W) :
    ∃ x', ADBudget p W x' ∧ Summable (fun t => β ^ t * u (x' t)) ∧ dyU u β x < dyU u β x' := by
  set b := (W - ∑' t, p t * x t) / p 0 with hb
  have hbpos : 0 < b := div_pos (by linarith) (hp 0)
  set x' : ℕ → ℝ := fun t => if t = 0 then x 0 + b else x t with hx'
  have hout : ∀ n ∉ ({0} : Finset ℕ), x' n = x n := fun n hn => by
    simp only [Finset.mem_singleton] at hn
    simp [hx', hn]
  obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun t => p t * x t) (g := fun t => p t * x' t) {0}
    (fun n hn => by simp only [hout n hn]) hxs
  obtain ⟨hSU, hEU⟩ := ce_tsum_perturb (f := fun t => β ^ t * u (x t))
    (g := fun t => β ^ t * u (x' t)) {0} (fun n hn => by simp only [hout n hn]) hxU
  have hx'0 : x' 0 = x 0 + b := by simp [hx']
  refine ⟨x', ⟨fun t => ?_, hS, ?_⟩, hSU, ?_⟩
  · by_cases ht : t = 0
    · subst ht; rw [hx'0]; linarith [hx 0]
    · simp only [hx', ht, ↓reduceIte]; exact hx t
  · rw [hE, Finset.sum_singleton, hx'0, hb]
    have := (hp 0).ne'
    field_simp
    ring
  · unfold dyU
    rw [hEU, Finset.sum_singleton, hx'0, pow_zero, one_mul, one_mul]
    have := hu (Set.mem_Ioi.2 (hx 0)) (Set.mem_Ioi.2 (by linarith [hx 0] : 0 < x 0 + b))
      (by linarith)
    linarith

/-- **AKMM, p. 162: the First Welfare Theorem in the dynastic economy.** With finitely many
consumers, `u` strictly increasing, positive prices and endowments of finite value (the
condition the book stresses: the value `p · x` must be finite), a competitive equilibrium
allocation is Pareto optimal. -/
theorem fwt_dynastic {u : ℝ → ℝ} (hu : StrictMonoOn u (Set.Ioi 0)) {β : ℝ}
    {ω c : I → ℕ → ℝ} {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (he : dyCompEq u β ω c p) :
    dyParetoOptimal u β ω c := by
  classical
  obtain ⟨hω, hopt, hclear⟩ := he
  refine ⟨⟨fun i t => (hopt i).1.1 t, fun t => (hclear t).le⟩, fun i => (hopt i).2.1, ?_⟩
  rintro ⟨d, hd, hdU, hle, i₀, hlt⟩
  have hds := dy_value_summable hp hω hd
  have hge : ∀ i, ∑' t, p t * ω i t ≤ ∑' t, p t * d i t := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨x', hx', hx'U, hgain⟩ := dy_lns hu hp (hd.1 i) (hds i) (hdU i) hcon
    have := (hopt i).2.2 x' hx' hx'U
    have := hle i
    unfold dyU at *
    linarith
  have hgt : ∑' t, p t * ω i₀ t < ∑' t, p t * d i₀ t := by
    rcases (hge i₀).lt_or_eq with h | h
    · exact h
    exfalso
    have := (hopt i₀).2.2 (d i₀) ⟨hd.1 i₀, hds i₀, h.symm⟩ (hdU i₀)
    unfold dyU at hlt
    linarith
  have hsum : ∑ i, ∑' t, p t * ω i t < ∑ i, ∑' t, p t * d i t :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i₀, Finset.mem_univ _, hgt⟩
  rw [← Summable.tsum_finsetSum (fun i _ => hω i),
    ← Summable.tsum_finsetSum (fun i _ => hds i)] at hsum
  have hle' : ∀ t, ∑ i, p t * d i t ≤ ∑ i, p t * ω i t := by
    intro t
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hd.2 t) (hp t).le
  have := Summable.tsum_le_tsum hle' (summable_sum fun i _ => hds i)
    (summable_sum fun i _ => hω i)
  linarith

/-- AKMM, p. 165: the planner's problem with Negishi weights `µᵢ`: `c` is feasible with
convergent utility series and maximises `Σᵢ µᵢUᵢ` among such allocations. -/
def dyPlannerOptimal (u : ℝ → ℝ) (β : ℝ) (μ : I → ℝ) (ω c : I → ℕ → ℝ) : Prop :=
  dyFeasible ω c ∧ (∀ i, Summable fun t => β ^ t * u (c i t)) ∧
    ∀ d : I → ℕ → ℝ, dyFeasible ω d → (∀ i, Summable fun t => β ^ t * u (d i t)) →
      ∑ i, μ i * dyU u β (d i) ≤ ∑ i, μ i * dyU u β (c i)

/-- **AKMM, pp. 164–166: planner solutions are Pareto optimal.** "A solution to such a problem
must be Pareto optimal because if it were not, the Pareto dominating allocation would increase
the planner's objective" (strictly positive weights). -/
theorem negishi_planner_pareto {u : ℝ → ℝ} {β : ℝ} {μ : I → ℝ} {ω c : I → ℕ → ℝ}
    (hμ : ∀ i, 0 < μ i) (hc : dyPlannerOptimal u β μ ω c) : dyParetoOptimal u β ω c := by
  refine ⟨hc.1, hc.2.1, ?_⟩
  rintro ⟨d, hd, hdU, hle, i₀, hlt⟩
  have : ∑ i, μ i * dyU u β (c i) < ∑ i, μ i * dyU u β (d i) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hle i) (hμ i).le)
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hμ i₀)⟩
  exact absurd (hc.2.2 d hd hdU) (not_le.2 this)

/-- **AKMM, (6.2), p. 165.** At the date-0 optimum the first-order condition is
`βᵗu′(c_{i,t}) = λᵢpₜ` with the time-independent multiplier `λᵢ = u′(c_{i,0})/p₀` (Chapter 5's
`ad_foc_multiplier`); inverting `u′` (a left inverse `g` of `u′` on the consumption levels)
gives `c_{i,t} = (u′)⁻¹(β^{−t}λᵢpₜ)`. -/
theorem eq_6_2 {u du g : ℝ → ℝ} {β : ℝ} {p c : ℕ → ℝ} {W : ℝ} (hβ : 0 < β)
    (hopt : ADOptimal u β p W c) (hp : ∀ t, 0 < p t) (hd : ∀ t, HasDerivAt u (du (c t)) (c t))
    (hg : ∀ t, g (du (c t)) = c t) (t : ℕ) :
    β ^ t * du (c t) = du (c 0) / p 0 * p t ∧
      c t = g ((β ^ t)⁻¹ * (du (c 0) / p 0 * p t)) := by
  have h := ad_foc_multiplier (du := fun t => du (c t)) hopt hp hd t
  refine ⟨h, ?_⟩
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (pow_pos hβ t).ne', one_mul, hg t]

/-- **AKMM, p. 166: the planner's first-order condition.** At a solution of the planner's
problem, moving consumption between consumers `i` and `j` at date `t` cannot help, so
`µᵢβᵗu′(c_{i,t}) = µⱼβᵗu′(c_{j,t})`: there is one multiplier `ψₜ` for date `t`. -/
theorem dy_planner_foc {u du : ℝ → ℝ} {β : ℝ} {μ : I → ℝ} {ω c : I → ℕ → ℝ}
    (hc : dyPlannerOptimal u β μ ω c) (hd : ∀ i t, HasDerivAt u (du (c i t)) (c i t))
    (i j : I) (t : ℕ) : μ i * β ^ t * du (c i t) = μ j * β ^ t * du (c j t) := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rfl
  obtain ⟨⟨hpos, hfeas⟩, hU, hmax⟩ := hc
  -- the perturbed allocations
  let d : ℝ → I → ℕ → ℝ := fun ε k n =>
    if n = t then (if k = i then c i t + ε else if k = j then c j t - ε else c k n) else c k n
  have hdout : ∀ ε k, ∀ n ∉ ({t} : Finset ℕ), d ε k n = c k n := fun ε k n hn => by
    simp only [Finset.mem_singleton] at hn
    simp [d, hn]
  have hdi : ∀ ε, d ε i t = c i t + ε := fun ε => by simp [d]
  have hdj : ∀ ε, d ε j t = c j t - ε := fun ε => by simp [d, hij.symm]
  have hdk : ∀ ε k, k ≠ i → k ≠ j → d ε k t = c k t := fun ε k hki hkj => by simp [d, hki, hkj]
  -- utilities of the perturbed allocations
  have hUd : ∀ ε k, Summable (fun n => β ^ n * u (d ε k n)) ∧
      dyU u β (d ε k) = dyU u β (c k) + β ^ t * (u (d ε k t) - u (c k t)) := by
    intro ε k
    obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun n => β ^ n * u (c k n))
      (g := fun n => β ^ n * u (d ε k n)) {t} (fun n hn => by simp only [hdout ε k n hn])
      (hU k)
    refine ⟨hS, ?_⟩
    unfold dyU
    rw [hE, Finset.sum_singleton]
    ring
  have hobj : ∀ ε, ∑ k, μ k * dyU u β (d ε k) = ∑ k, μ k * dyU u β (c k) +
      (μ i * β ^ t * (u (c i t + ε) - u (c i t)) + μ j * β ^ t * (u (c j t - ε) - u (c j t))) := by
    intro ε
    have e : ∀ k, μ k * dyU u β (d ε k) = μ k * dyU u β (c k) +
        ((if k = i then μ i * β ^ t * (u (c i t + ε) - u (c i t)) else 0) +
          (if k = j then μ j * β ^ t * (u (c j t - ε) - u (c j t)) else 0)) := by
      intro k
      rw [(hUd ε k).2]
      by_cases hki : k = i
      · subst hki; simp [hij, hdi]; ring
      by_cases hkj : k = j
      · subst hkj; simp [hki, hdj]; ring
      simp [hki, hkj, hdk ε k hki hkj]
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  -- for small `ε` the perturbation is feasible
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c i t + ε ∧ 0 < c j t - ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c i t + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos i t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c j t - ε :=
      continuousAt_const.eventually_lt (continuous_const.sub continuous_id).continuousAt
        (by simpa using hpos j t)
    exact h1.and h2
  have hloc : IsLocalMax (fun ε => μ i * β ^ t * u (c i t + ε) + μ j * β ^ t * u (c j t - ε))
      0 := by
    filter_upwards [hev] with ε hε
    have hfe : dyFeasible ω (d ε) := by
      refine ⟨fun k n => ?_, fun n => ?_⟩
      · by_cases hn : n = t
        · subst hn
          by_cases hki : k = i
          · subst hki; rw [hdi]; exact hε.1
          by_cases hkj : k = j
          · subst hkj; rw [hdj]; exact hε.2
          rw [hdk ε k hki hkj]; exact hpos k n
        · rw [hdout ε k n (by simpa using hn)]; exact hpos k n
      · by_cases hn : n = t
        · subst hn
          have : ∑ k, d ε k n = ∑ k, c k n := by
            have e : ∀ k, d ε k n = c k n + ((if k = i then ε else 0) +
                (if k = j then -ε else 0)) := by
              intro k
              by_cases hki : k = i
              · subst hki; simp [hij, hdi]
              by_cases hkj : k = j
              · subst hkj; simp [hki, hdj]; ring
              simp [hki, hkj, hdk ε k hki hkj]
            rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib,
              Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
            simp
          rw [this]; exact hfeas n
        · simp only [hdout ε _ n (by simpa using hn)]; exact hfeas n
    have := hmax (d ε) hfe fun k => (hUd ε k).1
    rw [hobj ε] at this
    simp only [add_zero, sub_zero]
    linarith
  have hderiv : HasDerivAt (fun ε => μ i * β ^ t * u (c i t + ε) + μ j * β ^ t * u (c j t - ε))
      (μ i * β ^ t * du (c i t) + μ j * β ^ t * (du (c j t) * (-1))) 0 := by
    have h1 : HasDerivAt (fun ε => u (c i t + ε)) (du (c i t)) 0 := by
      have hu : HasDerivAt u (du (c i t)) (c i t + 0) := by simpa using hd i t
      simpa using hu.comp_const_add (c i t) 0
    have h2 : HasDerivAt (fun ε => u (c j t - ε)) (du (c j t) * (-1)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c j t - ε) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c j t)
      have hu : HasDerivAt u (du (c j t)) (c j t - 0) := by simpa using hd j t
      exact hu.comp 0 hin
    exact (h1.const_mul _).add (h2.const_mul _)
  have := hloc.hasDerivAt_eq_zero hderiv
  linarith

/-- **AKMM, (6.3), p. 166.** At a solution of the planner's problem the date-`t` multiplier
`ψₜ = µᵢβᵗu′(c_{i,t})` (the same for every `i`, `dy_planner_foc`) gives
`c_{i,t} = (u′)⁻¹(β^{−t}ψₜ/µᵢ)` for every consumer. -/
theorem eq_6_3 {u du g : ℝ → ℝ} {β : ℝ} {μ : I → ℝ} {ω c : I → ℕ → ℝ} (hβ : 0 < β)
    (hμ : ∀ i, 0 < μ i) (hc : dyPlannerOptimal u β μ ω c)
    (hd : ∀ i t, HasDerivAt u (du (c i t)) (c i t)) (hg : ∀ i t, g (du (c i t)) = c i t)
    (i₀ : I) (i : I) (t : ℕ) :
    c i t = g ((β ^ t)⁻¹ * ((μ i₀ * β ^ t * du (c i₀ t)) / μ i)) := by
  rw [← dy_planner_foc hc hd i i₀ t]
  have := (hμ i).ne'
  have := (pow_pos hβ t).ne'
  have e : (β ^ t)⁻¹ * (μ i * β ^ t * du (c i t) / μ i) = du (c i t) := by field_simp
  rw [e, hg i t]

/-- **AKMM, p. 166: the symmetry of (6.2) and (6.3).** With `µᵢ = 1/λᵢ` and `ψₜ = pₜ` the two
formulas give the same consumption. -/
theorem negishi_coincide (g : ℝ → ℝ) {β lam p : ℝ} (hlam : lam ≠ 0) (t : ℕ) :
    g ((β ^ t)⁻¹ * (lam * p)) = g ((β ^ t)⁻¹ * (p / (1 / lam))) := by
  congr 2
  field_simp

/-- **AKMM, p. 166: market clearing forces `ψₜ = pₜ`.** If `(u′)⁻¹` (`g`) is strictly
decreasing on the positive reals, `λᵢ > 0`, and the allocations `g(β^{−t}λᵢpₜ)` and
`g(β^{−t}λᵢψₜ)` have the same total (both equal the total endowment), then `ψₜ = pₜ`. -/
theorem negishi_psi_eq_p [Nonempty I] {g : ℝ → ℝ} (hg : StrictAntiOn g (Set.Ioi 0))
    {lam : I → ℝ} (hlam : ∀ i, 0 < lam i) {β p ψ : ℝ} (hβ : 0 < β) (hp : 0 < p) (hψ : 0 < ψ)
    (t : ℕ) (hclear : ∑ i, g ((β ^ t)⁻¹ * (lam i * p)) = ∑ i, g ((β ^ t)⁻¹ * (lam i * ψ))) :
    ψ = p := by
  have hb := inv_pos.2 (pow_pos hβ t)
  have key : ∀ a b : ℝ, 0 < a → a < b →
      ∑ i, g ((β ^ t)⁻¹ * (lam i * b)) < ∑ i, g ((β ^ t)⁻¹ * (lam i * a)) := by
    intro a b ha hab
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
    have hla := mul_pos hb (mul_pos (hlam i) ha)
    exact hg (Set.mem_Ioi.2 hla) (Set.mem_Ioi.2 (mul_pos hb (mul_pos (hlam i) (ha.trans hab))))
      (mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hab (hlam i)) hb)
  rcases lt_trichotomy ψ p with h | h | h
  · linarith [key ψ p hψ h]
  · exact h
  · linarith [key p ψ hp h]

/-- **AKMM, p. 166: the equilibrium allocation solves the planner's problem with Negishi
weights `µᵢ = 1/λᵢ`.** If `u` lies below its tangents (concavity) and the equilibrium satisfies
`βᵗu′(c_{i,t}) = λᵢpₜ` with `λᵢ > 0`, then `c` maximises `Σᵢ (1/λᵢ)Uᵢ` over feasible
allocations. -/
theorem negishi_ce_solves_planner {u du : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) {ω c : I → ℕ → ℝ}
    {p : ℕ → ℝ} {lam : I → ℝ} (hp : ∀ t, 0 < p t) (hlam : ∀ i, 0 < lam i)
    (he : dyCompEq u β ω c p)
    (htan : ∀ i t x, 0 < x → u x ≤ u (c i t) + du (c i t) * (x - c i t))
    (hfoc : ∀ i t, β ^ t * du (c i t) = lam i * p t) :
    dyPlannerOptimal u β (fun i => 1 / lam i) ω c := by
  classical
  obtain ⟨hω, hopt, hclear⟩ := he
  refine ⟨⟨fun i t => (hopt i).1.1 t, fun t => (hclear t).le⟩, fun i => (hopt i).2.1,
    fun d hd hdU => ?_⟩
  have hds := dy_value_summable hp hω hd
  have hcs : ∀ i, Summable fun t => p t * c i t := fun i => (hopt i).1.2.1
  have hgain : ∀ i, 1 / lam i * dyU u β (d i) ≤
      1 / lam i * dyU u β (c i) + ∑' t, (p t * d i t - p t * c i t) := by
    intro i
    have hb : ∀ t, β ^ t * u (d i t) ≤
        β ^ t * u (c i t) + lam i * (p t * d i t - p t * c i t) := by
      intro t
      have h1 := mul_le_mul_of_nonneg_left (htan i t (d i t) (hd.1 i t)) (pow_nonneg hβ t)
      have h2 : β ^ t * (u (c i t) + du (c i t) * (d i t - c i t)) =
          β ^ t * u (c i t) + (β ^ t * du (c i t)) * (d i t - c i t) := by ring
      rw [h2, hfoc i t] at h1
      linarith
    have hS : Summable (fun t => β ^ t * u (c i t) + lam i * (p t * d i t - p t * c i t)) :=
      ((hopt i).2.1).add (((hds i).sub (hcs i)).mul_left (lam i))
    have := Summable.tsum_le_tsum hb (hdU i) hS
    rw [((hopt i).2.1).tsum_add (((hds i).sub (hcs i)).mul_left (lam i)), tsum_mul_left]
      at this
    unfold dyU
    have hl := hlam i
    have e : 1 / lam i * (∑' t, β ^ t * u (c i t) +
        lam i * ∑' t, (p t * d i t - p t * c i t)) = 1 / lam i * ∑' t, β ^ t * u (c i t) +
        ∑' t, (p t * d i t - p t * c i t) := by field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hgain i
  rw [Finset.sum_add_distrib] at hsum
  have hnp : ∑ i, ∑' t, (p t * d i t - p t * c i t) ≤ 0 := by
    rw [← Summable.tsum_finsetSum (fun i _ => (hds i).sub (hcs i))]
    refine tsum_nonpos fun t => ?_
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hclear t, ← mul_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (hp t).le (by linarith [hd.2 t])
  linarith

/-- **AKMM, p. 166 ("there are some Negishi weights that make the competitive equilibrium
optimal for the planner, which implies the competitive equilibrium is Pareto optimal").** Under
the hypotheses of `negishi_ce_solves_planner` the equilibrium allocation is Pareto optimal. -/
theorem negishi_fwt {u du : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) {ω c : I → ℕ → ℝ}
    {p : ℕ → ℝ} {lam : I → ℝ} (hp : ∀ t, 0 < p t) (hlam : ∀ i, 0 < lam i)
    (he : dyCompEq u β ω c p)
    (htan : ∀ i t x, 0 < x → u x ≤ u (c i t) + du (c i t) * (x - c i t))
    (hfoc : ∀ i t, β ^ t * du (c i t) = lam i * p t) : dyParetoOptimal u β ω c :=
  negishi_planner_pareto (fun i => one_div_pos.2 (hlam i))
    (negishi_ce_solves_planner hβ hp hlam he htan hfoc)

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A production externality

AKMM, §6.3.2, pp. 168–169. The consumer maximises `log c − Bℓ^{1+1/θ}/(1 + 1/θ)` subject to
`c = rk + wℓ`; the representative firm produces `A(ȳ)k^αℓ^{1−α}` taking aggregate output `ȳ`
as given.

* The equilibrium condition `1 − α = Bℓ^{1+1/θ}` from the consumer's condition
  `w/(rk + wℓ) = Bℓ^{1/θ}` and the firm's `r/w = αℓ/((1 − α)k)` (`ext_equilibrium_hours`); its
  positive solution is unique and does not involve `A` (`ext_equilibrium_hours_unique`).
* The planner's first-order conditions give `(1 − α)/(1 − A′(y)k^αℓ^{1−α}) = Bℓ^{1+1/θ}`
  (`ext_planner_hours`); the equilibrium is optimal only if `A′(y) = 0` (`ext_not_optimal`); with
  a negative externality (`A′ < 0`) the planner's hours are strictly lower
  (`ext_overwork`).
* Fn. 7: at a zero-profit input choice, a rise in the firm's TFP makes profits positive and
  unbounded along a ray of input choices (`ext_fn7`).
-/

namespace AKMM.Welfare

/-- **AKMM, p. 169: equilibrium hours.** With `k, ℓ, w > 0`, `α < 1`, the consumer's condition
`w/(rk + wℓ) = Bℓ^{1/θ}` and the firm's `r/w = αℓ/((1 − α)k)` give `1 − α = Bℓ^{1+1/θ}`. -/
theorem ext_equilibrium_hours {α B θ k l r w : ℝ} (hα : α < 1) (hk : 0 < k) (hl : 0 < l)
    (hw : 0 < w) (hcons : w / (r * k + w * l) = B * l ^ (1 / θ))
    (hfirm : r / w = α * l / ((1 - α) * k)) : 1 - α = B * l ^ (1 + 1 / θ) := by
  have h1α : 0 < 1 - α := by linarith
  have hr : r * k = α * w * l / (1 - α) := by
    field_simp at hfirm ⊢
    linarith
  have hinc : r * k + w * l = w * l / (1 - α) := by
    rw [hr]; field_simp; ring
  rw [hinc] at hcons
  have e : w / (w * l / (1 - α)) = (1 - α) / l := by field_simp
  rw [e] at hcons
  rw [Real.rpow_add hl, Real.rpow_one]
  field_simp at hcons
  linarith

/-- **AKMM, p. 169: uniqueness.** For `B > 0`, `θ > 0`, `α < 1`, the positive solution of
`1 − α = Bℓ^{1+1/θ}` is `ℓ = ((1 − α)/B)^{1/(1+1/θ)}`, the same for every TFP function `A`. -/
theorem ext_equilibrium_hours_unique {α B θ l : ℝ} (hB : 0 < B) (hθ : 0 < θ) (hl : 0 < l)
    (h : 1 - α = B * l ^ (1 + 1 / θ)) : l = ((1 - α) / B) ^ (1 / (1 + 1 / θ)) := by
  have hpos : 0 < 1 + 1 / θ := by positivity
  rw [h, mul_div_cancel_left₀ _ hB.ne', ← Real.rpow_mul hl.le, mul_one_div_cancel hpos.ne',
    Real.rpow_one]

/-- **AKMM, p. 169: the planner's hours.** From the first-order conditions
`Bℓ^{1/θ} = λ(1 − α)A(y)k^αℓ^{−α}` and `1/y = λ(1 − A′(y)k^αℓ^{1−α})` and the constraint
`y = A(y)k^αℓ^{1−α}` (with `y, ℓ > 0`) follows `(1 − α)/(1 − A′(y)k^αℓ^{1−α}) = Bℓ^{1+1/θ}`. -/
theorem ext_planner_hours {α B θ k l y lam Ay dA : ℝ} (hl : 0 < l) (hy : 0 < y)
    (hfoc1 : B * l ^ (1 / θ) = lam * (1 - α) * Ay * k ^ α * l ^ (-α))
    (hfoc2 : 1 / y = lam * (1 - dA * k ^ α * l ^ (1 - α)))
    (hcon : y = Ay * k ^ α * l ^ (1 - α)) :
    1 - dA * k ^ α * l ^ (1 - α) ≠ 0 ∧
      (1 - α) / (1 - dA * k ^ α * l ^ (1 - α)) = B * l ^ (1 + 1 / θ) := by
  set D := dA * k ^ α * l ^ (1 - α) with hD
  have hD1 : 1 - D ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfoc2
    exact (one_div_pos.2 hy).ne' hfoc2
  refine ⟨hD1, ?_⟩
  have hlam : lam = 1 / (y * (1 - D)) := by
    field_simp at hfoc2 ⊢
    linarith
  have hsplit : l ^ (1 - α) = l * l ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hl, Real.rpow_one]
  have hyl : Ay * k ^ α * l ^ (-α) = y / l := by
    rw [hcon, hsplit]; field_simp
  rw [Real.rpow_add hl, Real.rpow_one, mul_comm l, ← mul_assoc, hfoc1, hlam]
  have e : 1 / (y * (1 - D)) * (1 - α) * Ay * k ^ α * l ^ (-α) * l =
      (1 - α) / (y * (1 - D)) * (Ay * k ^ α * l ^ (-α)) * l := by ring
  rw [e, hyl]
  field_simp

/-- **AKMM, p. 169: the equilibrium is not optimal unless `A′(y) = 0`.** If the same `ℓ` solves
the equilibrium condition `1 − α = Bℓ^{1+1/θ}` and the planner's condition (with `k, ℓ > 0` and
`α < 1`), then `A′(y) = 0`. -/
theorem ext_not_optimal {α B θ k l dA : ℝ} (hα : α < 1) (hk : 0 < k) (hl : 0 < l)
    (hD1 : 1 - dA * k ^ α * l ^ (1 - α) ≠ 0) (heq : 1 - α = B * l ^ (1 + 1 / θ))
    (hpl : (1 - α) / (1 - dA * k ^ α * l ^ (1 - α)) = B * l ^ (1 + 1 / θ)) : dA = 0 := by
  rw [← heq, div_eq_iff hD1] at hpl
  have h1α : (1 - α) ≠ 0 := by linarith
  have : (1 - α) * (dA * k ^ α * l ^ (1 - α)) = 0 := by linarith
  have hkl : k ^ α * l ^ (1 - α) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hl _).ne'
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h1α
  · rw [mul_assoc] at h
    exact (mul_eq_zero.1 h).resolve_right hkl

/-- **AKMM, p. 169: too much work under a negative externality.** If `A′ < 0` at the planner's
optimum `(ℓ_P, y_P)` and `ℓ_E` solves the equilibrium condition, then `ℓ_P < ℓ_E`. -/
theorem ext_overwork {α B θ k lP lE dA : ℝ} (hα : α < 1) (hB : 0 < B) (hθ : 0 < θ)
    (hk : 0 < k) (hlP : 0 < lP) (hlE : 0 < lE) (hdA : dA < 0)
    (heq : 1 - α = B * lE ^ (1 + 1 / θ))
    (hpl : (1 - α) / (1 - dA * k ^ α * lP ^ (1 - α)) = B * lP ^ (1 + 1 / θ)) : lP < lE := by
  have hD : dA * k ^ α * lP ^ (1 - α) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdA (Real.rpow_pos_of_pos hk _))
      (Real.rpow_pos_of_pos hlP _)
  have h1α : 0 < 1 - α := by linarith
  have hlt : (1 - α) / (1 - dA * k ^ α * lP ^ (1 - α)) < 1 - α := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hpow : lP ^ (1 + 1 / θ) < lE ^ (1 + 1 / θ) := by
    rw [hpl] at hlt
    rw [heq] at hlt
    exact lt_of_mul_lt_mul_left hlt hB.le
  have hpos : 0 < 1 + 1 / θ := by positivity
  exact (Real.rpow_lt_rpow_iff hlP.le hlE.le hpos).1 hpow

/-- **AKMM, fn. 7, p. 169.** If the input choice `(k, ℓ)` makes zero profit at TFP `A`,
`Ak^αℓ^{1−α} = rk + wℓ`, and the firm's TFP rises to `A′ > A` (other firms produce less), then
profits at `(sk, sℓ)` are `s(A′ − A)k^αℓ^{1−α}`: positive and unbounded in `s`. -/
theorem ext_fn7 {A A' α r w k l : ℝ} (hk : 0 < k) (hl : 0 < l) (hA : A < A')
    (hzero : A * k ^ α * l ^ (1 - α) = r * k + w * l) :
    (∀ s, 0 < s → A' * (s * k) ^ α * (s * l) ^ (1 - α) - r * (s * k) - w * (s * l) =
      s * ((A' - A) * k ^ α * l ^ (1 - α))) ∧
    ∀ M : ℝ, ∃ s, 0 < s ∧ M < A' * (s * k) ^ α * (s * l) ^ (1 - α) - r * (s * k) - w * (s * l) := by
  have hprof : ∀ s, 0 < s → A' * (s * k) ^ α * (s * l) ^ (1 - α) - r * (s * k) - w * (s * l) =
      s * ((A' - A) * k ^ α * l ^ (1 - α)) := by
    intro s hs
    rw [Real.mul_rpow hs.le hk.le, Real.mul_rpow hs.le hl.le]
    have hss : s ^ α * s ^ (1 - α) = s := by
      rw [← Real.rpow_add hs, add_sub_cancel, Real.rpow_one]
    have : A' * (s ^ α * k ^ α) * (s ^ (1 - α) * l ^ (1 - α)) =
        (s ^ α * s ^ (1 - α)) * (A' * k ^ α * l ^ (1 - α)) := by ring
    rw [this, hss]
    linear_combination s * hzero
  refine ⟨hprof, fun M => ?_⟩
  have hg : 0 < (A' - A) * k ^ α * l ^ (1 - α) :=
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hk _)) (Real.rpow_pos_of_pos hl _)
  refine ⟨(|M| + 1) / ((A' - A) * k ^ α * l ^ (1 - α)), by positivity, ?_⟩
  rw [hprof _ (by positivity), div_mul_cancel₀ _ hg.ne']
  linarith [le_abs_self M]

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Missing markets: a borrowing constraint

AKMM, §6.3.3, pp. 170–171, and §6.5.1, p. 184. Two log-utility consumers share a constant
endowment `ω`; consumer `i ∈ {0, 1}` (the book's agents 1 and 2) receives
`e_{i,t} = ω/2 − (ω/6)(−1)^{i+t}`: agent 1 has `ω/3` in even and `2ω/3` in odd periods, agent 2
the reverse.

* **Unrestricted markets** (p. 170): `pₜ = βᵗ` (gross interest rate `1/β`),
  `c₁ = (1/3 + 2β/3)ω/(1 + β)` and `c₂ = (2/3 + β/3)ω/(1 + β)` form an Arrow–Debreu equilibrium
  (`borrow_unrestricted`, with the endowment values `borrow_endow_value`).
* **The consumption possibility set** (p. 171): `c₀ ≤ a₀ + ω₀` and
  `q₀c₁ ≤ ω₀ + a₀ − c₀ + q₀ω₁` (`borrow_possibility_set`); the book prints `− q₀ω₁`
  (`borrow_possibility_set_printed_counterexample`).
* **No borrowing** (pp. 170–171): the sequential problem with `a_{t+1} ≥ 0` (`nbOptimal`) and its
  equilibrium (`nbEquilibrium`). Bond-market clearing with `a ≥ 0` forces autarky
  (`borrow_autarky`); at an optimum the Euler equation becomes the inequality
  `qₜu′(cₜ) ≥ βu′(c_{t+1})` (`borrow_euler_ineq`, proved by raising `a_{t+1}`); conversely the
  inequality at the endowment makes autarky optimal (`borrow_autarky_optimal`). Hence the
  equilibria are exactly autarky with `qₜ ≥ 2β` for all `t` (`borrow_equilibrium_iff`): `qₜ = 2β`
  is the case in which the lender's constraint does not bind, and fn. 9's `qₜ > 2β` are
  equilibria too. At `qₜ = 2β` the real rate `1/qₜ − 1` is below the unrestricted `1/β − 1`, and
  negative iff `β > 1/2` (`borrow_interest_rate`).
* The autarky allocation is not Pareto optimal: the unrestricted equilibrium allocation is
  feasible and strictly better for both consumers (`borrow_autarky_not_optimal`), so the transfer
  policy of §6.5.1 can make both better off.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium

/-- The endowments of §6.3.3: `e_{i,t} = ω/2 − (ω/6)(−1)^{i+t}`. -/
noncomputable def brEndow (ω : ℝ) (i : Fin 2) (t : ℕ) : ℝ := ω / 2 - ω / 6 * (-1) ^ ((i : ℕ) + t)

/-- The unrestricted equilibrium consumption `cᵢ = ω/2 − (ω/6)(−1)^i(1 − β)/(1 + β)`. -/
noncomputable def brCons (ω β : ℝ) (i : Fin 2) : ℝ :=
  ω / 2 - ω / 6 * (-1) ^ (i : ℕ) * ((1 - β) / (1 + β))

/-- AKMM, p. 170: agent 1 (`i = 0`) has `ω/3` in even and `2ω/3` in odd periods, agent 2 the
reverse, and the total is `ω`. -/
theorem brEndow_spec (ω : ℝ) (t : ℕ) :
    (Even t → brEndow ω 0 t = ω / 3 ∧ brEndow ω 1 t = 2 * ω / 3) ∧
    (Odd t → brEndow ω 0 t = 2 * ω / 3 ∧ brEndow ω 1 t = ω / 3) ∧
    brEndow ω 0 t + brEndow ω 1 t = ω := by
  simp only [brEndow, Fin.val_zero, Fin.val_one, zero_add]
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · rw [h.neg_one_pow, (h.one_add).neg_one_pow]; constructor <;> ring
  · rw [h.neg_one_pow, (h.one_add).neg_one_pow]; constructor <;> ring
  · rw [pow_add]; ring

/-- AKMM, p. 170: the book's formulas `c₁ = (1/3 + 2β/3)ω/(1 + β)`, `c₂ = (2/3 + β/3)ω/(1 + β)`. -/
theorem brCons_spec {ω β : ℝ} (hβ : 0 ≤ β) :
    brCons ω β 0 = (1 / 3 + 2 * β / 3) * ω / (1 + β) ∧
      brCons ω β 1 = (2 / 3 + β / 3) * ω / (1 + β) := by
  have : 1 + β ≠ 0 := by linarith
  simp only [brCons, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  constructor <;> field_simp <;> ring

/-- AKMM, p. 170: the values of the endowments at `pₜ = βᵗ`:
`Σ βᵗe_{i,t} = (ω/2)/(1 − β) − (ω/6)(−1)^i/(1 + β)`. -/
theorem borrow_endow_value {ω β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (i : Fin 2) :
    Summable (fun t => β ^ t * brEndow ω i t) ∧
      ∑' t, β ^ t * brEndow ω i t = ω / 2 / (1 - β) - ω / 6 * (-1) ^ (i : ℕ) / (1 + β) := by
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hn : ‖-β‖ < 1 := by rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hg' := summable_geometric_of_norm_lt_one hn
  have e : (fun t => β ^ t * brEndow ω i t) =
      fun t => ω / 2 * β ^ t - ω / 6 * (-1) ^ (i : ℕ) * (-β) ^ t := by
    funext t; simp only [brEndow, pow_add, neg_pow β]; ring
  rw [e]
  refine ⟨(hg.mul_left _).sub (hg'.mul_left _), ?_⟩
  rw [(hg.mul_left _).tsum_sub (hg'.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hβ0 hβ1, tsum_geometric_of_norm_lt_one hn]
  have : 1 - β ≠ 0 := by linarith
  have : 1 - -β ≠ 0 := by linarith
  field_simp
  ring

/-- **AKMM, p. 170: the unrestricted equilibrium.** For `ω > 0`, `0 < β < 1`, the prices
`pₜ = βᵗ` and the constant consumptions `brCons` form an Arrow–Debreu equilibrium of the
two-agent log economy; the gross interest rate is `pₜ/p_{t+1} = 1/β`. -/
theorem borrow_unrestricted {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 < β) (hβ1 : β < 1) :
    dyCompEq Real.log β (brEndow ω) (fun i _ => brCons ω β i) (fun t => β ^ t) ∧
      ∀ t, β ^ t / β ^ (t + 1) = 1 / β := by
  refine ⟨⟨fun i => (borrow_endow_value hβ0.le hβ1 i).1, fun i => ?_, fun t => ?_⟩, fun t => ?_⟩
  · have hr : 0 < (1 - β) / (1 + β) := div_pos (by linarith) (by linarith)
    have hr1 : (1 - β) / (1 + β) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hc : 0 < brCons ω β i := by
      fin_cases i <;> simp [brCons] <;> nlinarith
    have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
    refine ad_foc_sufficient (du := fun _ => (brCons ω β i)⁻¹) (lam := (brCons ω β i)⁻¹)
      hβ0.le (fun t x hx => ce_log_tangent hc hx) (fun t => by ring)
      ⟨fun _ => hc, hgeo.mul_right _, ?_⟩ (hgeo.mul_right _)
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, (borrow_endow_value hβ0.le hβ1 i).2]
    simp only [brCons]
    have : 1 - β ≠ 0 := by linarith
    have : 1 + β ≠ 0 := by linarith
    field_simp
  · rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have := (brEndow_spec ω t).2.2
    simp only [brCons, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    linarith
  · rw [pow_succ]; field_simp

/-- **AKMM, p. 171 (corrected).** In the sequential budgets `c₀ + q₀a₁ = ω₀ + a₀`,
`c₁ + q₁a₂ = ω₁ + a₁` with the borrowing constraints `a₁, a₂ ≥ 0` and `q₀ > 0`, `q₁ ≥ 0`:
`c₀ ≤ a₀ + ω₀` and `q₀c₁ ≤ ω₀ + a₀ − c₀ + q₀ω₁`. -/
theorem borrow_possibility_set {c₀ c₁ a₀ a₁ a₂ q₀ q₁ ω₀ ω₁ : ℝ} (hq₀ : 0 < q₀) (hq₁ : 0 ≤ q₁)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₀ : c₀ + q₀ * a₁ = ω₀ + a₀)
    (hb₁ : c₁ + q₁ * a₂ = ω₁ + a₁) :
    c₀ ≤ a₀ + ω₀ ∧ q₀ * c₁ ≤ ω₀ + a₀ - c₀ + q₀ * ω₁ := by
  constructor
  · nlinarith
  · have : c₁ ≤ ω₁ + a₁ := by nlinarith
    nlinarith

/-- **AKMM, p. 171: the printed constraint `q₀c₁ ≤ ω₀ + a₀ − c₀ − q₀ω₁` is wrong.** With
`a₀ = a₁ = a₂ = 0`, `ω₀ = ω₁ = 1`, `q₀ = q₁ = 1`, `c₀ = c₁ = 1` (autarky, which satisfies every
budget and borrowing constraint), the printed inequality reads `1 ≤ −1`. -/
theorem borrow_possibility_set_printed_counterexample :
    let c₀ : ℝ := 1; let c₁ : ℝ := 1; let q₀ : ℝ := 1; let ω₀ : ℝ := 1; let ω₁ : ℝ := 1
    let a₀ : ℝ := 0; let a₁ : ℝ := 0
    c₀ + q₀ * a₁ = ω₀ + a₀ ∧ c₁ + 1 * 0 = ω₁ + a₁ ∧ ¬ (q₀ * c₁ ≤ ω₀ + a₀ - c₀ - q₀ * ω₁) := by
  norm_num

/-- Consumption in the sequential budget `cₜ + qₜa_{t+1} = ωₜ + aₜ`. -/
def nbCons (q ω a : ℕ → ℝ) (t : ℕ) : ℝ := ω t + a t - q t * a (t + 1)

/-- AKMM, p. 170: a plan of bond holdings with `a₀ = 0`, the borrowing constraint
`a_{t+1} ≥ 0` and positive consumption. -/
def nbFeasible (q ω a : ℕ → ℝ) : Prop :=
  a 0 = 0 ∧ (∀ t, 0 ≤ a (t + 1)) ∧ ∀ t, 0 < nbCons q ω a t

/-- AKMM, p. 170: `a` solves `max Σ βᵗ log(ωₜ + aₜ − qₜa_{t+1})` subject to `a_{t+1} ≥ 0`, among
the plans whose utility series converges. -/
def nbOptimal (β : ℝ) (q ω a : ℕ → ℝ) : Prop :=
  nbFeasible q ω a ∧ Summable (fun t => β ^ t * Real.log (nbCons q ω a t)) ∧
    ∀ a', nbFeasible q ω a' → Summable (fun t => β ^ t * Real.log (nbCons q ω a' t)) →
      ∑' t, β ^ t * Real.log (nbCons q ω a' t) ≤ ∑' t, β ^ t * Real.log (nbCons q ω a t)

/-- AKMM, pp. 170–171: an equilibrium with the borrowing constraint: every consumer solves her
problem at the bond prices `q` and the bond market clears. -/
def nbEquilibrium {I : Type*} [Fintype I] (β : ℝ) (q : ℕ → ℝ) (ω a : I → ℕ → ℝ) : Prop :=
  (∀ i, nbOptimal β q (ω i) (a i)) ∧ ∀ t, ∑ i, a i t = 0

/-- **AKMM, p. 171: no borrowing means autarky.** In an equilibrium every `a_{i,t} = 0`, so
`c_{i,t} = ω_{i,t}`. -/
theorem borrow_autarky {I : Type*} [Fintype I] {β : ℝ} {q : ℕ → ℝ} {ω a : I → ℕ → ℝ}
    (he : nbEquilibrium β q ω a) : ∀ i t, a i t = 0 ∧ nbCons q (ω i) (a i) t = ω i t := by
  have ha : ∀ i t, a i t = 0 := by
    intro i t
    rcases t with _ | t
    · exact (he.1 i).1.1
    · exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (he.1 k).1.2.1 t).1 (he.2 (t + 1)) i
        (Finset.mem_univ _)
  intro i t
  refine ⟨ha i t, ?_⟩
  simp [nbCons, ha i t, ha i (t + 1)]

/-- **AKMM, pp. 170–171: the Euler inequality.** At an optimum of the problem with the
borrowing constraint, with `β, qₜ > 0`, `qₜu′(cₜ) ≥ βu′(c_{t+1})`, i.e.
`β/c_{t+1} ≤ qₜ/cₜ` (the multiplier `µₜ ≥ 0`). Proved by raising `a_{t+1}`. -/
theorem borrow_euler_ineq {β : ℝ} {q ω a : ℕ → ℝ} (hβ : 0 < β) (hopt : nbOptimal β q ω a)
    (t : ℕ) : β / nbCons q ω a (t + 1) ≤ q t / nbCons q ω a t := by
  obtain ⟨⟨ha0, hann, hpos⟩, hU, hmax⟩ := hopt
  set ct := nbCons q ω a t with hct
  set ct1 := nbCons q ω a (t + 1) with hct1
  have hct0 := hpos t
  have hct10 := hpos (t + 1)
  -- the perturbed plans
  let a' : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then a (t + 1) + ε else a n
  have hc't : ∀ ε, nbCons q ω (a' ε) t = ct - q t * ε := fun ε => by
    simp only [nbCons, a', hct, ↓reduceIte, show t ≠ t + 1 by omega]; ring
  have hc't1 : ∀ ε, nbCons q ω (a' ε) (t + 1) = ct1 + ε := fun ε => by
    simp only [nbCons, a', hct1, ↓reduceIte, show t + 1 + 1 ≠ t + 1 by omega]; ring
  have hc'o : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), nbCons q ω (a' ε) n = nbCons q ω a n := by
    intro ε n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [nbCons, a', hn.2, show n + 1 ≠ t + 1 by omega, ↓reduceIte]
  set φ : ℝ → ℝ := fun ε => β ^ t * Real.log (ct - q t * ε) + β ^ (t + 1) * Real.log (ct1 + ε)
    with hφ
  -- the optimum is not improved by small `ε > 0`
  have hle : ∀ ε, 0 ≤ ε → 0 < ct - q t * ε → φ ε ≤ φ 0 := by
    intro ε hε hεc
    have hfe : nbFeasible q ω (a' ε) := by
      refine ⟨by simp [a', ha0], fun n => ?_, fun n => ?_⟩
      · by_cases hn : n + 1 = t + 1
        · simp only [a', hn, ↓reduceIte]; linarith [hann t]
        · simp only [a', hn, ↓reduceIte]; exact hann n
      · by_cases hn1 : n = t
        · subst hn1; rw [hc't]; exact hεc
        by_cases hn2 : n = t + 1
        · subst hn2; rw [hc't1]; linarith
        rw [hc'o ε n (by simp [hn1, hn2])]; exact hpos n
    obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun n => β ^ n * Real.log (nbCons q ω a n))
      (g := fun n => β ^ n * Real.log (nbCons q ω (a' ε) n)) {t, t + 1}
      (fun n hn => by simp only [hc'o ε n hn]) hU
    have := hmax (a' ε) hfe hS
    rw [hE, Finset.sum_pair (by omega), hc't, hc't1] at this
    simp only [hφ, mul_zero, sub_zero, add_zero]
    linarith
  -- the derivative of `φ` at `0`
  have hd : HasDerivAt φ (β ^ t * (ct⁻¹ * (-q t)) + β ^ (t + 1) * ct1⁻¹) 0 := by
    have h1 : HasDerivAt (fun ε => Real.log (ct - q t * ε)) (ct⁻¹ * (-q t)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => ct - q t * ε) (-q t) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (q t)).const_sub ct
      have hl : HasDerivAt Real.log ct⁻¹ (ct - q t * 0) := by
        simpa using Real.hasDerivAt_log hct0.ne'
      exact hl.comp 0 hin
    have h2 : HasDerivAt (fun ε => Real.log (ct1 + ε)) ct1⁻¹ 0 := by
      have hl : HasDerivAt Real.log ct1⁻¹ (ct1 + 0) := by
        simpa using Real.hasDerivAt_log hct10.ne'
      simpa using hl.comp_const_add ct1 0
    exact (h1.const_mul _).add (h2.const_mul _)
  have hnonpos : β ^ t * (ct⁻¹ * (-q t)) + β ^ (t + 1) * ct1⁻¹ ≤ 0 := by
    by_contra hpos'
    push Not at hpos'
    have hsl := hd.tendsto_slope_zero_right
    have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε⁻¹ • (φ (0 + ε) - φ 0) :=
      hsl.eventually (lt_mem_nhds hpos')
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ct - q t * ε := by
      have : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ct - q t * ε :=
        continuousAt_const.eventually_lt
          (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
          (by simpa using hct0)
      exact nhdsWithin_le_nhds this
    have hev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
    have := hle ε h3.le h2
    rw [zero_add, smul_eq_mul] at h1
    have : ε⁻¹ * (φ ε - φ 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 h3.le) (by linarith)
    linarith
  have hbt := pow_pos hβ t
  rw [pow_succ] at hnonpos
  have key : β ^ t * (β * ct - q t * ct1) ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hnonpos (mul_pos hct0 hct10).le
    have e : ct * ct1 * (β ^ t * (ct⁻¹ * -q t) + β ^ t * β * ct1⁻¹) =
        β ^ t * (β * ct - q t * ct1) := by
      have h1 : ct ≠ 0 := hct0.ne'
      have h2 : ct1 ≠ 0 := hct10.ne'
      field_simp; ring
    rw [e, mul_zero] at h
    exact h
  rw [div_le_div_iff₀ hct10 hct0]
  by_contra hcon
  push Not at hcon
  have := mul_pos hbt (sub_pos.2 hcon)
  linarith

/-- **AKMM, pp. 170–171: autarky is optimal under the Euler inequality.** If `ωₜ > 0`,
`βωₜ ≤ qₜω_{t+1}` (that is, `qₜu′(ωₜ) ≥ βu′(ω_{t+1})`) for all `t`, `β ≥ 0`, and the autarky
utility series converges, then `a = 0` solves the problem with the borrowing constraint.
(No transversality condition is needed: every partial sum is compared.) -/
theorem borrow_autarky_optimal {β : ℝ} {q ω : ℕ → ℝ} (hβ : 0 ≤ β) (hω : ∀ t, 0 < ω t)
    (heul : ∀ t, β * ω t ≤ q t * ω (t + 1))
    (hU : Summable fun t => β ^ t * Real.log (ω t)) : nbOptimal β q ω (fun _ => 0) := by
  have hc0 : ∀ t, nbCons q ω (fun _ => 0) t = ω t := fun t => by simp [nbCons]
  refine ⟨⟨rfl, fun _ => le_rfl, fun t => by rw [hc0]; exact hω t⟩, by simpa [hc0] using hU,
    fun a' ha' hU' => ?_⟩
  simp only [hc0]
  obtain ⟨ha0, hann, hpos⟩ := ha'
  -- the tangent bound at each date
  have htan : ∀ n, β ^ n * Real.log (nbCons q ω a' n) ≤
      β ^ n * Real.log (ω n) + β ^ n * ((a' n - q n * a' (n + 1)) / ω n) := by
    intro n
    have h1 := ce_log_tangent (hω n) (hpos n)
    have h2 : nbCons q ω a' n - ω n = a' n - q n * a' (n + 1) := by simp [nbCons]; ring
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ n)
    calc β ^ n * Real.log (nbCons q ω a' n) ≤ β ^ n * (Real.log (ω n) + (ω n)⁻¹ *
          (a' n - q n * a' (n + 1))) := this
      _ = _ := by ring
  -- the telescoping bound
  have htel : ∀ N, ∑ n ∈ Finset.range N, β ^ n * ((a' n - q n * a' (n + 1)) / ω n) +
      β ^ N * a' N / ω N ≤ 0 := by
    intro N
    induction N with
    | zero => simp [ha0]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep : β ^ (N + 1) * a' (N + 1) / ω (N + 1) - β ^ N * q N * a' (N + 1) / ω N ≤ 0 := by
        have hωN := hω N
        have hωN1 := hω (N + 1)
        have e : β ^ (N + 1) * a' (N + 1) / ω (N + 1) - β ^ N * q N * a' (N + 1) / ω N =
            β ^ N * a' (N + 1) * (β * ω N - q N * ω (N + 1)) / (ω N * ω (N + 1)) := by
          field_simp; ring
        rw [e]
        refine div_nonpos_of_nonpos_of_nonneg ?_ (mul_pos hωN hωN1).le
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (pow_nonneg hβ N) (hann N)) (by linarith [heul N])
      have e2 : β ^ N * ((a' N - q N * a' (N + 1)) / ω N) =
          β ^ N * a' N / ω N - β ^ N * q N * a' (N + 1) / ω N := by ring
      linarith
  have hpart : ∀ N, ∑ n ∈ Finset.range N, β ^ n * Real.log (nbCons q ω a' n) ≤
      ∑ n ∈ Finset.range N, β ^ n * Real.log (ω n) := by
    intro N
    have h1 := Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) => htan n
    rw [Finset.sum_add_distrib] at h1
    have h2 : 0 ≤ β ^ N * a' N / ω N := by
      rcases N with _ | N
      · simp [ha0]
      · exact div_nonneg (mul_nonneg (pow_nonneg hβ _) (hann N)) (hω _).le
    linarith [htel N]
  exact le_of_tendsto_of_tendsto' hU'.hasSum.tendsto_sum_nat hU.hasSum.tendsto_sum_nat hpart

/-- The autarky utility series of the alternating economy converges. -/
theorem borrow_endow_log_summable {ω β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (i : Fin 2) :
    Summable fun t => β ^ t * Real.log (brEndow ω i t) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (|Real.log (ω / 3)| +
      |Real.log (2 * ω / 3)|)) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have hv : brEndow ω i t = ω / 3 ∨ brEndow ω i t = 2 * ω / 3 := by
    have := brEndow_spec ω t
    rcases Nat.even_or_odd t with h | h <;> fin_cases i <;> simp_all
  rcases hv with h | h <;> rw [h] <;> linarith [abs_nonneg (Real.log (ω / 3)),
    abs_nonneg (Real.log (2 * ω / 3))]

/-- **AKMM, p. 171 and fn. 9: the equilibria with the borrowing constraint.** In the alternating
economy (`ω > 0`, `0 < β < 1`), `(q, a)` is an equilibrium iff `a = 0` (autarky) and
`qₜ ≥ 2β` for every `t`. -/
theorem borrow_equilibrium_iff {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 < β) (hβ1 : β < 1)
    {q : ℕ → ℝ} {a : Fin 2 → ℕ → ℝ} :
    nbEquilibrium β q (brEndow ω) a ↔ (∀ i t, a i t = 0) ∧ ∀ t, 2 * β ≤ q t := by
  have hval : ∀ (i : Fin 2) t, (brEndow ω i t = ω / 3 ∧ brEndow ω i (t + 1) = 2 * ω / 3) ∨
      (brEndow ω i t = 2 * ω / 3 ∧ brEndow ω i (t + 1) = ω / 3) := by
    intro i t
    have h0 := brEndow_spec ω t
    have h1 := brEndow_spec ω (t + 1)
    rcases Nat.even_or_odd t with h | h
    · have h' : Odd (t + 1) := h.add_one
      fin_cases i <;> simp_all
    · have h' : Even (t + 1) := h.add_one
      fin_cases i <;> simp_all
  constructor
  · intro he
    have hz := borrow_autarky he
    refine ⟨fun i t => (hz i t).1, fun t => ?_⟩
    -- the consumer who is rich at `t`
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, brEndow ω i t = 2 * ω / 3 ∧ brEndow ω i (t + 1) = ω / 3 := by
      rcases hval 0 t with h | h
      · refine ⟨1, ?_⟩
        have := (brEndow_spec ω t).2.2
        have := (brEndow_spec ω (t + 1)).2.2
        constructor <;> linarith [h.1, h.2]
      · exact ⟨0, h⟩
    have := borrow_euler_ineq hβ0 (he.1 i) t
    rw [(hz i t).2, (hz i (t + 1)).2, hi.1, hi.2] at this
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
    nlinarith
  · rintro ⟨hz, hq2⟩
    have ha : a = fun _ _ => 0 := funext fun i => funext fun t => hz i t
    subst ha
    refine ⟨fun i => borrow_autarky_optimal hβ0.le (fun t => ?_) (fun t => ?_)
      (borrow_endow_log_summable hβ0.le hβ1 i), fun t => by simp⟩
    · rcases hval i t with h | h <;> rw [h.1] <;> positivity
    · have := hq2 t
      rcases hval i t with h | h <;> rw [h.1, h.2] <;> nlinarith

/-- **AKMM, p. 171: the interest rate at `qₜ = 2β`.** The real rate `1/(2β) − 1` is below the
unrestricted rate `1/β − 1`, and it is negative iff `β > 1/2`. -/
theorem borrow_interest_rate {β : ℝ} (hβ : 0 < β) :
    1 / (2 * β) - 1 < 1 / β - 1 ∧ (1 / (2 * β) - 1 < 0 ↔ 1 / 2 < β) := by
  constructor
  · have : 1 / (2 * β) < 1 / β := by
      rw [div_lt_div_iff₀ (by positivity) hβ]; linarith
    linarith
  · rw [sub_neg, div_lt_one (by positivity)]
    constructor <;> intro h <;> linarith

/-- **AKMM, p. 171: the no-borrowing allocation is not Pareto optimal** ("consumption is not
smoothed"). The unrestricted equilibrium allocation is feasible and gives both consumers strictly
higher utility than autarky. -/
theorem borrow_autarky_not_optimal {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ¬ dyParetoOptimal Real.log β (brEndow ω) (brEndow ω) ∧
      ∀ i, dyU Real.log β (brEndow ω i) < dyU Real.log β (fun _ => brCons ω β i) := by
  obtain ⟨he, -⟩ := borrow_unrestricted hω hβ0 hβ1
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hgain : ∀ i, dyU Real.log β (brEndow ω i) < dyU Real.log β (fun _ => brCons ω β i) := by
    intro i
    have hc := (he.2.1 i).1.1 0
    have hepos : ∀ t, 0 < brEndow ω i t := by
      intro t
      rcases (brEndow_spec ω t) with ⟨h1, h2, -⟩
      rcases Nat.even_or_odd t with h | h <;> fin_cases i <;> simp_all
    have hne : brEndow ω i 0 ≠ brCons ω β i := by
      simp only [brEndow, brCons, add_zero]
      intro h
      have h1 : (-1 : ℝ) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
      have : ω / 6 * (-1) ^ (i : ℕ) * (1 - (1 - β) / (1 + β)) = 0 := by linarith
      have hb : 1 - (1 - β) / (1 + β) = 2 * β / (1 + β) := by field_simp; ring
      rw [hb] at this
      have h2 : 2 * β / (1 + β) ≠ 0 := by positivity
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · exact h1 h
      · exact h2 h
    -- strict tangent inequality
    have htan : ∀ t, β ^ t * Real.log (brEndow ω i t) ≤ β ^ t * Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (β ^ t * brEndow ω i t - β ^ t * brCons ω β i) := by
      intro t
      have := mul_le_mul_of_nonneg_left (ce_log_tangent hc (hepos t)) (pow_nonneg hβ0.le t)
      linarith [show β ^ t * (Real.log (brCons ω β i) + (brCons ω β i)⁻¹ *
        (brEndow ω i t - brCons ω β i)) = β ^ t * Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (β ^ t * brEndow ω i t - β ^ t * brCons ω β i) by ring]
    have hstrict : Real.log (brEndow ω i 0) < Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (brEndow ω i 0 - brCons ω β i) := by
      have hx := Real.log_lt_sub_one_of_pos (div_pos (hepos 0) hc)
        (by rw [Ne, div_eq_one_iff_eq hc.ne']; exact hne)
      rw [Real.log_div (hepos 0).ne' hc.ne'] at hx
      have : brEndow ω i 0 / brCons ω β i - 1 =
          (brCons ω β i)⁻¹ * (brEndow ω i 0 - brCons ω β i) := by field_simp
      linarith
    have hS : Summable fun t => β ^ t * Real.log (brCons ω β i) +
        (brCons ω β i)⁻¹ * (β ^ t * brEndow ω i t - β ^ t * brCons ω β i) :=
      (hgeo.mul_right _).add (((borrow_endow_value hβ0.le hβ1 i).1.sub
        (hgeo.mul_right _)).mul_left _)
    have hlt := Summable.tsum_lt_tsum (i := 0) htan (by simpa using hstrict)
      (borrow_endow_log_summable hβ0.le hβ1 i) hS
    rw [(hgeo.mul_right _).tsum_add (((borrow_endow_value hβ0.le hβ1 i).1.sub
        (hgeo.mul_right _)).mul_left _), tsum_mul_left,
      (borrow_endow_value hβ0.le hβ1 i).1.tsum_sub (hgeo.mul_right _)] at hlt
    have hW : ∑' t, β ^ t * brCons ω β i = ∑' t, β ^ t * brEndow ω i t := (he.2.1 i).1.2.2
    rw [hW, sub_self, mul_zero, add_zero] at hlt
    exact hlt
  refine ⟨fun ⟨_, _, hno⟩ => hno ⟨fun i _ => brCons ω β i,
    ⟨fun i t => (he.2.1 i).1.1 t, fun t => (he.2.2 t).le⟩, fun i => (he.2.1 i).2.1,
    fun i => (hgain i).le, 0, hgain 0⟩, hgain⟩

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monopolistic competition

AKMM, §6.3.5, pp. 172–175 (Dixit and Stiglitz, 1977). A continuum of goods carrying a measure
`μ` (the book's `[0, 1]` with Lebesgue measure is one instance), the CES aggregate
`C = (∫ c(i)^{1−1/ε} di)^{ε/(ε−1)}`, `ε ≠ 1`, `ε > 0`.

* (6.4): the two forms of the first-order condition agree (`eq_6_4`); under it
  `∫ p(i)c(i) di = λC` (`ds_expenditure`), `λ = P ≡ (∫ p(i)^{1−ε} di)^{1/(1−ε)}`
  (`ds_price_index`), the demand function `c(i) = C(p(i)/P)^{−ε}` (`ds_demand`), and `P` is
  homogeneous of degree one (`ds_price_index_homogeneous`).
* The firm's problem `max_c PC^{1/ε}c^{1−1/ε} − (w/A)c` (`dsProfit`, with revenue
  `p(c)c`: `ds_revenue`): for `ε > 1` the solution is `c = C(w/(A(1 − 1/ε)P))^{−ε}` with the price
  `p = (ε/(ε − 1))w/A`, a markup `µ = ε/(ε − 1) > 1`, and profit `(µ − 1)(w/A)c`
  (`ds_firm_optimum`). Fn. 10: for `ε < 1` profits are unbounded (`ds_no_max_lt_one`); for
  `ε = 1` no maximum exists and the supremum is the revenue `PC` (`ds_no_max_eq_one`).
* The symmetric equilibrium: `c = C`, `P = 1` give `w = A(1 − 1/ε)` (`ds_symmetric_wage`); with
  log utility the labour condition is `A(1 − 1/ε) = Cv′(C/A)` (`ds_equilibrium_condition`),
  which has at most one solution when `v′` is positive and nondecreasing
  (`ds_rhs_strictMono`, `ds_unique`); the planner's condition is `A = Cv′(C/A)`
  (`ds_planner_foc`), and equilibrium output is too low (`ds_underproduction`).
-/

namespace AKMM.Welfare

open MeasureTheory

/-- The identity behind (6.4) and the revenue: for `x, C > 0`,
`(x/C)^{−1/ε}·x = C^{1/ε}x^{1−1/ε}`. -/
theorem ds_rpow_ratio {ε x C : ℝ} (hx : 0 < x) (hC : 0 < C) :
    (x / C) ^ (-1 / ε) * x = C ^ (1 / ε) * x ^ (1 - 1 / ε) := by
  rw [Real.div_rpow hx.le hC.le, sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one,
    show -1 / ε = -(1 / ε) by ring, Real.rpow_neg hx.le, Real.rpow_neg hC.le]
  field_simp

/-- **AKMM, (6.4), p. 173.** With `S = ∫ c^{1−1/ε} > 0`, `C = S^{ε/(ε−1)}` and `x = c(i) > 0`,
the derivative form of the first-order condition
`λ(ε/(ε − 1))S^{ε/(ε−1)−1}(1 − 1/ε)x^{−1/ε}` equals `λ(x/C)^{−1/ε}`. -/
theorem eq_6_4 {ε S x lam : ℝ} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1) (hS : 0 < S) (hx : 0 < x) :
    lam * (ε / (ε - 1)) * S ^ (ε / (ε - 1) - 1) * (1 - 1 / ε) * x ^ (-1 / ε) =
      lam * (x / S ^ (ε / (ε - 1))) ^ (-1 / ε) := by
  have hε1' : ε - 1 ≠ 0 := sub_ne_zero.2 hε1
  rw [Real.div_rpow hx.le (Real.rpow_nonneg hS.le _), ← Real.rpow_mul hS.le]
  have e1 : ε / (ε - 1) - 1 = 1 / (ε - 1) := by field_simp; ring
  have e2 : ε / (ε - 1) * (-1 / ε) = -(1 / (ε - 1)) := by field_simp
  have e3 : ε / (ε - 1) * (1 - 1 / ε) = 1 := by field_simp
  rw [e1, e2, Real.rpow_neg hS.le, div_inv_eq_mul]
  calc lam * (ε / (ε - 1)) * S ^ (1 / (ε - 1)) * (1 - 1 / ε) * x ^ (-1 / ε) =
      lam * (ε / (ε - 1) * (1 - 1 / ε)) * (x ^ (-1 / ε) * S ^ (1 / (ε - 1))) := by ring
    _ = _ := by rw [e3, mul_one]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **AKMM, p. 173: expenditure.** If `p(i) = λ(c(i)/C)^{−1/ε}` for all `i`, with `c > 0`,
`S = ∫ c^{1−1/ε} > 0` and `C = S^{ε/(ε−1)}`, then `∫ p(i)c(i) di = λC`: `λ` is the unit price of
the basket. -/
theorem ds_expenditure {μ : Measure Ω} {ε lam : ℝ} {c p : Ω → ℝ} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1)
    (hc : ∀ i, 0 < c i) (hS : 0 < ∫ i, c i ^ (1 - 1 / ε) ∂μ)
    (hfoc : ∀ i, p i = lam * (c i / (∫ i, c i ^ (1 - 1 / ε) ∂μ) ^ (ε / (ε - 1))) ^ (-1 / ε)) :
    ∫ i, p i * c i ∂μ = lam * (∫ i, c i ^ (1 - 1 / ε) ∂μ) ^ (ε / (ε - 1)) := by
  set S := ∫ i, c i ^ (1 - 1 / ε) ∂μ with hSdef
  have hC : 0 < S ^ (ε / (ε - 1)) := Real.rpow_pos_of_pos hS _
  have e : (fun i => p i * c i) = fun i => (lam * (S ^ (ε / (ε - 1))) ^ (1 / ε)) *
      c i ^ (1 - 1 / ε) := by
    funext i
    rw [hfoc i, mul_assoc, ds_rpow_ratio (hc i) hC]
    ring
  rw [e, integral_const_mul, ← hSdef, ← Real.rpow_mul hS.le, mul_assoc]
  congr 1
  have hε1' : ε - 1 ≠ 0 := sub_ne_zero.2 hε1
  rw [← Real.rpow_add_one hS.ne']
  congr 1
  field_simp
  ring

/-- **AKMM, p. 173: the price index.** Under the first-order condition of `ds_expenditure` with
`λ > 0`, `λ = P ≡ (∫ p(i)^{1−ε} di)^{1/(1−ε)}`. -/
theorem ds_price_index {μ : Measure Ω} {ε lam : ℝ} {c p : Ω → ℝ} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1)
    (hlam : 0 < lam) (hc : ∀ i, 0 < c i) (hS : 0 < ∫ i, c i ^ (1 - 1 / ε) ∂μ)
    (hfoc : ∀ i, p i = lam * (c i / (∫ i, c i ^ (1 - 1 / ε) ∂μ) ^ (ε / (ε - 1))) ^ (-1 / ε)) :
    (∫ i, p i ^ (1 - ε) ∂μ) ^ (1 / (1 - ε)) = lam := by
  set S := ∫ i, c i ^ (1 - 1 / ε) ∂μ with hSdef
  have hε1' : ε - 1 ≠ 0 := sub_ne_zero.2 hε1
  have hε1'' : 1 - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε1)
  have e : (fun i => p i ^ (1 - ε)) = fun i => (lam ^ (1 - ε) * S⁻¹) * c i ^ (1 - 1 / ε) := by
    funext i
    rw [hfoc i, Real.mul_rpow hlam.le (Real.rpow_nonneg (div_nonneg (hc i).le
      (Real.rpow_nonneg hS.le _)) _), ← Real.rpow_mul (div_nonneg (hc i).le
      (Real.rpow_nonneg hS.le _)), Real.div_rpow (hc i).le (Real.rpow_nonneg hS.le _),
      ← Real.rpow_mul hS.le]
    have e1 : -1 / ε * (1 - ε) = 1 - 1 / ε := by field_simp; ring
    have e2 : ε / (ε - 1) * (1 - 1 / ε) = 1 := by field_simp
    rw [e1, e2, Real.rpow_one]
    ring
  rw [e, integral_const_mul, ← hSdef, mul_assoc, inv_mul_cancel₀ hS.ne', mul_one,
    ← Real.rpow_mul hlam.le, mul_one_div_cancel hε1'', Real.rpow_one]

/-- **AKMM, p. 174: the demand function.** Under the first-order condition with `λ = P > 0`,
`c(i) = C(p(i)/P)^{−ε}`. -/
theorem ds_demand {ε lam C x px : ℝ} (hε0 : ε ≠ 0) (hlam : 0 < lam) (hC : 0 < C) (hx : 0 < x)
    (hfoc : px = lam * (x / C) ^ (-1 / ε)) : x = C * (px / lam) ^ (-ε) := by
  rw [hfoc, mul_div_cancel_left₀ _ hlam.ne', ← Real.rpow_mul (div_nonneg hx.le hC.le),
    show -1 / ε * -ε = 1 by field_simp, Real.rpow_one]
  field_simp

/-- **AKMM, p. 173: `P` is homogeneous of degree one** in the prices: scaling every price by
`s > 0` scales `P` by `s` (for `ε ≠ 1`, positive prices, `∫ p^{1−ε} ≥ 0`). -/
theorem ds_price_index_homogeneous {μ : Measure Ω} {ε s : ℝ} {p : Ω → ℝ} (hε1 : ε ≠ 1)
    (hs : 0 < s) (hp : ∀ i, 0 < p i) (hI : 0 ≤ ∫ i, p i ^ (1 - ε) ∂μ) :
    (∫ i, (s * p i) ^ (1 - ε) ∂μ) ^ (1 / (1 - ε)) =
      s * (∫ i, p i ^ (1 - ε) ∂μ) ^ (1 / (1 - ε)) := by
  have hε1'' : 1 - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε1)
  have e : (fun i => (s * p i) ^ (1 - ε)) = fun i => s ^ (1 - ε) * p i ^ (1 - ε) := by
    funext i; rw [Real.mul_rpow hs.le (hp i).le]
  rw [e, integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hs.le _) hI,
    ← Real.rpow_mul hs.le, mul_one_div_cancel hε1'', Real.rpow_one]

/-- The monopolist's profit as a function of output, with the inverse demand substituted:
`PC^{1/ε}c^{1−1/ε} − (w/A)c` (AKMM, p. 174). -/
noncomputable def dsProfit (ε P C w A c : ℝ) : ℝ := P * C ^ (1 / ε) * c ^ (1 - 1 / ε) - w / A * c

/-- AKMM, p. 174: with the inverse demand `p = P(c/C)^{−1/ε}`, revenue `pc` is
`PC^{1/ε}c^{1−1/ε}`, so `dsProfit` is the firm's objective `pc − w ℓ` with `c = Aℓ`. -/
theorem ds_revenue {ε P C w A c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    P * (c / C) ^ (-1 / ε) * c - w * (c / A) = dsProfit ε P C w A c := by
  rw [dsProfit, mul_assoc, ds_rpow_ratio hc hC]
  ring

/-- **AKMM, p. 175: the firm's optimum for `ε > 1`.** With `P, C, w, A > 0`, the output
`c⋆ = C(w/(A(1 − 1/ε)P))^{−ε}` maximises `dsProfit` over `c > 0`; its price is
`P(c⋆/C)^{−1/ε} = (ε/(ε − 1))w/A`, a markup `µ = ε/(ε − 1) > 1` over marginal cost `w/A`, and the
maximal profit is `(µ − 1)(w/A)c⋆`. -/
theorem ds_firm_optimum {ε P C w A : ℝ} (hε : 1 < ε) (hP : 0 < P) (hC : 0 < C) (hw : 0 < w)
    (hA : 0 < A) :
    let cs := C * (w / (A * (1 - 1 / ε) * P)) ^ (-ε)
    (∀ c, 0 < c → dsProfit ε P C w A c ≤ dsProfit ε P C w A cs) ∧
      P * (cs / C) ^ (-1 / ε) = ε / (ε - 1) * (w / A) ∧ 1 < ε / (ε - 1) ∧
      dsProfit ε P C w A cs = (ε / (ε - 1) - 1) * (w / A) * cs := by
  intro cs
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hθ0 : 0 < 1 - 1 / ε := by rw [sub_pos, div_lt_one (by linarith)]; exact hε
  have hθ1 : 1 - 1 / ε < 1 := sub_lt_self 1 (by positivity)
  set X := w / (A * (1 - 1 / ε) * P) with hX
  have hXpos : 0 < X := by positivity
  have hcs : 0 < cs := mul_pos hC (Real.rpow_pos_of_pos hXpos _)
  -- the price at `cs`
  have hprice : (cs / C) ^ (-1 / ε) = X := by
    rw [show cs / C = X ^ (-ε) from mul_div_cancel_left₀ _ hC.ne', ← Real.rpow_mul hXpos.le,
      show -ε * (-1 / ε) = 1 by field_simp, Real.rpow_one]
  -- the first-order condition `Kθc⋆^{θ−1} = w/A`
  have hfoc : P * C ^ (1 / ε) * (1 - 1 / ε) * cs ^ (-1 / ε) = w / A := by
    have : cs ^ (-1 / ε) = C ^ (-1 / ε) * X := by
      have hCp : C ^ (-1 / ε) ≠ 0 := (Real.rpow_pos_of_pos hC _).ne'
      rw [← hprice, Real.div_rpow hcs.le hC.le]
      field_simp
    rw [this, show -1 / ε = -(1 / ε) by ring, Real.rpow_neg hC.le, hX]
    have : C ^ (1 / ε) ≠ 0 := (Real.rpow_pos_of_pos hC _).ne'
    have : 1 - 1 / ε ≠ 0 := hθ0.ne'
    field_simp
  refine ⟨fun c hc => ?_, ?_, ?_, ?_⟩
  · -- Bernoulli: `c^θ ≤ c⋆^θ + θc⋆^{θ−1}(c − c⋆)`
    have hb := rpow_one_add_le_one_add_mul_self (s := c / cs - 1)
      (by have := div_pos hc hcs; linarith) hθ0.le hθ1.le
    rw [add_sub_cancel] at hb
    have hb2 : c ^ (1 - 1 / ε) ≤ cs ^ (1 - 1 / ε) +
        (1 - 1 / ε) * cs ^ (-1 / ε) * (c - cs) := by
      have h1 : c ^ (1 - 1 / ε) = cs ^ (1 - 1 / ε) * (c / cs) ^ (1 - 1 / ε) := by
        rw [Real.div_rpow hc.le hcs.le]; field_simp
      have h2 : cs ^ (-1 / ε) * cs = cs ^ (1 - 1 / ε) := by
        rw [sub_eq_add_neg, Real.rpow_add hcs, Real.rpow_one, show -1 / ε = -(1 / ε) by ring]
        ring
      rw [h1]
      have hpos := Real.rpow_pos_of_pos hcs (1 - 1 / ε)
      calc cs ^ (1 - 1 / ε) * (c / cs) ^ (1 - 1 / ε) ≤
          cs ^ (1 - 1 / ε) * (1 + (1 - 1 / ε) * (c / cs - 1)) :=
            mul_le_mul_of_nonneg_left hb hpos.le
        _ = cs ^ (1 - 1 / ε) + (1 - 1 / ε) * (cs ^ (-1 / ε) * cs) * (c / cs - 1) := by
            rw [h2]; ring
        _ = _ := by field_simp
    have hK : 0 < P * C ^ (1 / ε) := mul_pos hP (Real.rpow_pos_of_pos hC _)
    unfold dsProfit
    have := mul_le_mul_of_nonneg_left hb2 hK.le
    have e : P * C ^ (1 / ε) * ((1 - 1 / ε) * cs ^ (-1 / ε) * (c - cs)) = w / A * (c - cs) := by
      rw [← hfoc]; ring
    nlinarith
  · rw [hprice, hX]
    field_simp
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [dsProfit, mul_assoc P, ← ds_rpow_ratio hcs hC, ← mul_assoc, hprice, hX]
    field_simp

/-- **AKMM, fn. 10, p. 175: `ε < 1`.** For `0 < ε < 1` (and `P, C > 0`) profits are unbounded
above: they can be made arbitrarily large by producing little at a high price. -/
theorem ds_no_max_lt_one {ε P C w A : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hP : 0 < P)
    (hC : 0 < C) (hw : 0 ≤ w) (hA : 0 < A) :
    ∀ M : ℝ, ∃ c, 0 < c ∧ M < dsProfit ε P C w A c := by
  intro M
  have hθ : 1 - 1 / ε < 0 := by rw [sub_neg, lt_div_iff₀ hε0]; linarith
  have hK : 0 < P * C ^ (1 / ε) := mul_pos hP (Real.rpow_pos_of_pos hC _)
  set N := (|M| + w / A + 1) / (P * C ^ (1 / ε)) with hN
  have hNpos : 0 < N := by positivity
  set c0 := N ^ (1 / (1 - 1 / ε)) with hc0
  have hc0pos : 0 < c0 := Real.rpow_pos_of_pos hNpos _
  refine ⟨min 1 c0, lt_min one_pos hc0pos, ?_⟩
  have hm := lt_min one_pos hc0pos
  have hpow : N ≤ (min 1 c0) ^ (1 - 1 / ε) := by
    have h1 : c0 ^ (1 - 1 / ε) = N := by
      rw [hc0, ← Real.rpow_mul hNpos.le, one_div_mul_cancel hθ.ne, Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow_of_nonpos hm (min_le_right _ _) hθ.le
  unfold dsProfit
  have h1 : P * C ^ (1 / ε) * N ≤ P * C ^ (1 / ε) * (min 1 c0) ^ (1 - 1 / ε) :=
    mul_le_mul_of_nonneg_left hpow hK.le
  have h2 : P * C ^ (1 / ε) * N = |M| + w / A + 1 := by rw [hN]; field_simp
  have h3 : w / A * min 1 c0 ≤ w / A := by
    have := min_le_left 1 c0
    have : 0 ≤ w / A := div_nonneg hw hA.le
    nlinarith
  linarith [le_abs_self M]

/-- **AKMM, fn. 10, p. 175: `ε = 1`.** Revenue is `PC` whatever the output, so with `w, A > 0`
profit is below `PC` at every `c > 0`, but comes arbitrarily close: no maximum exists, and the
supremum is the revenue. -/
theorem ds_no_max_eq_one {P C w A : ℝ} (hw : 0 < w) (hA : 0 < A) :
    (∀ c, 0 < c → dsProfit 1 P C w A c < P * C) ∧
      ∀ η, 0 < η → ∃ c, 0 < c ∧ P * C - η < dsProfit 1 P C w A c := by
  have e : ∀ c, dsProfit 1 P C w A c = P * C - w / A * c := fun c => by
    simp [dsProfit]
  refine ⟨fun c hc => ?_, fun η hη => ⟨η / (2 * (w / A)), by positivity, ?_⟩⟩
  · rw [e]
    have : 0 < w / A * c := by positivity
    linarith
  rw [e]
  have : w / A * (η / (2 * (w / A))) = η / 2 := by field_simp
  linarith

/-- **AKMM, p. 175: the symmetric equilibrium wage.** With `c = C`, `P = 1`, the inverse demand
gives `p = 1`, and the markup `p = (ε/(ε − 1))w/A` gives `w = A(1 − 1/ε)`, below the marginal
product `A`. -/
theorem ds_symmetric_wage {ε C w A p : ℝ} (hε : 1 < ε) (hC : 0 < C) (hA : 0 < A)
    (hinv : p = 1 * (C / C) ^ (-1 / ε)) (hmark : p = ε / (ε - 1) * (w / A)) :
    p = 1 ∧ w = A * (1 - 1 / ε) ∧ w < A := by
  have hp : p = 1 := by rw [hinv, div_self hC.ne', Real.one_rpow, one_mul]
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  refine ⟨hp, ?_, ?_⟩
  · rw [hp] at hmark
    field_simp at hmark ⊢
    linarith
  · have hw : w = A * (1 - 1 / ε) := by
      rw [hp] at hmark; field_simp at hmark ⊢; linarith
    rw [hw]
    have : 0 < 1 / ε := by positivity
    nlinarith

/-- **AKMM, p. 175: the equilibrium condition.** With `u = log`, `L = C/A` and the labour
first-order condition `u′(C)w = v′(L)`, `w = A(1 − 1/ε)` gives `A(1 − 1/ε) = Cv′(C/A)`. -/
theorem ds_equilibrium_condition {ε C A w dvL : ℝ} (hC : 0 < C) (hw : w = A * (1 - 1 / ε))
    (hfoc : 1 / C * w = dvL) : A * (1 - 1 / ε) = C * dvL := by
  rw [← hfoc, ← hw]
  field_simp

/-- AKMM, p. 175: if `v′` is positive and nondecreasing on `(0, ∞)` (`v` convex and increasing)
and `A > 0`, then `C ↦ Cv′(C/A)` is strictly increasing on `(0, ∞)`. -/
theorem ds_rhs_strictMono {dv : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hpos : ∀ x, 0 < x → 0 < dv x) (hmono : MonotoneOn dv (Set.Ioi 0)) :
    StrictMonoOn (fun C => C * dv (C / A)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x / A := div_pos hx hA
  have hy' : 0 < y / A := div_pos hy hA
  have h1 : dv (x / A) ≤ dv (y / A) := hmono hx' hy' (div_le_div_of_nonneg_right hxy.le hA.le)
  have h2 := hpos _ hx'
  calc x * dv (x / A) < y * dv (x / A) := mul_lt_mul_of_pos_right hxy h2
    _ ≤ y * dv (y / A) := mul_le_mul_of_nonneg_left h1 (le_of_lt hy)

/-- **AKMM, p. 175: uniqueness.** When `C ↦ Cv′(C/A)` is strictly increasing, the equation
`A(1 − 1/ε) = Cv′(C/A)` has at most one positive solution. -/
theorem ds_unique {dv : ℝ → ℝ} {A ε C₁ C₂ : ℝ}
    (hsm : StrictMonoOn (fun C => C * dv (C / A)) (Set.Ioi 0)) (h1 : 0 < C₁) (h2 : 0 < C₂)
    (he1 : A * (1 - 1 / ε) = C₁ * dv (C₁ / A)) (he2 : A * (1 - 1 / ε) = C₂ * dv (C₂ / A)) :
    C₁ = C₂ :=
  hsm.injOn h1 h2 (show C₁ * dv (C₁ / A) = C₂ * dv (C₂ / A) by rw [← he1, ← he2])

/-- **AKMM, p. 175: the planner.** If `C > 0` maximises `log C − v(C/A)` over `(0, ∞)` and `v`
has derivative `v′(C/A)` at `C/A`, then `A = Cv′(C/A)`. -/
theorem ds_planner_foc {v : ℝ → ℝ} {A C dvL : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hd : HasDerivAt v dvL (C / A))
    (hmax : ∀ x, 0 < x → Real.log x - v (x / A) ≤ Real.log C - v (C / A)) : A = C * dvL := by
  have hloc : IsLocalMax (fun x => Real.log x - v (x / A)) C :=
    Filter.mem_of_superset (Ioi_mem_nhds hC) fun x hx => hmax x hx
  have hder : HasDerivAt (fun x => Real.log x - v (x / A)) (C⁻¹ - dvL * (1 / A)) C := by
    have hin : HasDerivAt (fun x : ℝ => x / A) (1 / A) C := by
      simpa using (hasDerivAt_id C).div_const A
    exact (Real.hasDerivAt_log hC.ne').sub (hd.comp C hin)
  have := hloc.hasDerivAt_eq_zero hder
  field_simp at this
  linarith

/-- **AKMM, p. 175: under-production.** If `C_M` solves `A(1 − 1/ε) = C_Mv′(C_M/A)`, `C_P` solves
`A = C_Pv′(C_P/A)`, `C ↦ Cv′(C/A)` is strictly increasing, `ε > 0` and `A > 0`, then
`C_M < C_P`: equilibrium output (and hours `C/A`) are too low. -/
theorem ds_underproduction {dv : ℝ → ℝ} {A ε CM CP : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hsm : StrictMonoOn (fun C => C * dv (C / A)) (Set.Ioi 0)) (hM : 0 < CM) (hP : 0 < CP)
    (heM : A * (1 - 1 / ε) = CM * dv (CM / A)) (heP : A = CP * dv (CP / A)) : CM < CP := by
  have hlt : CM * dv (CM / A) < CP * dv (CP / A) := by
    rw [← heM, ← heP]
    have : 0 < A * (1 / ε) := by positivity
    nlinarith
  exact (hsm.lt_iff_lt hM hP).1 hlt

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quantifying welfare losses, and the veil of ignorance

AKMM, §6.3.6, pp. 175–176, and §6.5.2, pp. 185–186.

* The consumption-equivalent `∆` (p. 176): if `u(·, ℓ_l)` is continuous and strictly increasing
  on `[0, c_l]` and `u(0, ℓ_l) < u(c_d, ℓ_d) < u(c_l, ℓ_l)`, there is exactly one `∆ ∈ (0, 1)` with
  `u(c_l(1 − ∆), ℓ_l) = u(c_d, ℓ_d)` (`welfare_cev_static`). In a dynamic model with log utility
  the uniform proportional cut `∆` is unique and given in closed form,
  `∆ = 1 − exp((1 − β)(U_d − U_l))` (`welfare_cev_dynamic_log`).
* Behind the veil of ignorance (p. 186): with strictly concave `u`, the problem
  `max πu(c_A) + (1 − π)u(c_B)` subject to `πc_A + (1 − π)c_B = πω_A + (1 − π)ω_B` is solved by
  `c_A = c_B` (`veil_equal_split`), and only by it (`veil_optimum_equal`).

The book's existence claim for general dynamic utilities ("a unique `∆` can still be defined")
is formalised for log utility only.
-/

namespace AKMM.Welfare

/-- **AKMM, p. 176: the consumption-equivalent welfare measure.** Let `g = u(·, ℓ_l)` be
continuous and strictly increasing on `[0, c_l]`, `c_l > 0`, and `g(0) < U_d < g(c_l)`, where
`U_d = u(c_d, ℓ_d)` and `g(c_l) = u(c_l, ℓ_l)`. Then there is exactly one `∆ ∈ (0, 1)` with
`u(c_l(1 − ∆), ℓ_l) = U_d`. -/
theorem welfare_cev_static {g : ℝ → ℝ} {cl Ud : ℝ} (hcl : 0 < cl)
    (hcont : ContinuousOn g (Set.Icc 0 cl)) (hmono : StrictMonoOn g (Set.Icc 0 cl))
    (h0 : g 0 < Ud) (h1 : Ud < g cl) :
    ∃! Δ : ℝ, Δ ∈ Set.Ioo 0 1 ∧ g (cl * (1 - Δ)) = Ud := by
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo hcl.le hcont ⟨h0, h1⟩
  have hx0 := hx.1
  have hx1 := hx.2
  refine ⟨1 - x / cl, ⟨⟨by rw [sub_pos, div_lt_one hcl]; exact hx1,
    by have := div_pos hx0 hcl; linarith⟩,
    by rw [sub_sub_cancel, mul_div_cancel₀ _ hcl.ne']; exact hgx⟩,
    fun Δ ⟨hΔ, hgΔ⟩ => ?_⟩
  have hm : cl * (1 - Δ) ∈ Set.Icc 0 cl :=
    ⟨by nlinarith [hΔ.1, hΔ.2], by nlinarith [hΔ.1, hΔ.2]⟩
  have hxm : x ∈ Set.Icc 0 cl := ⟨hx0.le, hx1.le⟩
  have : cl * (1 - Δ) = x := hmono.injOn hm hxm (by rw [hgΔ, hgx])
  field_simp
  linarith

/-- **AKMM, p. 176: the dynamic consumption equivalent with log utility.** For `0 ≤ β < 1`, a
positive consumption path `c` with a convergent utility series `U_l = Σ βᵗ log cₜ`, and `∆ < 1`,
cutting consumption by the fraction `∆` at every date gives utility
`Σ βᵗ log((1 − ∆)cₜ) = log(1 − ∆)/(1 − β) + U_l`; this equals `U_d` iff
`∆ = 1 − exp((1 − β)(U_d − U_l))`. So `∆` is unique, and positive iff `U_d < U_l`. -/
theorem welfare_cev_dynamic_log {β Ud Δ : ℝ} {c : ℕ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ t, 0 < c t) (hU : Summable fun t => β ^ t * Real.log (c t)) (hΔ : Δ < 1) :
    (∑' t, β ^ t * Real.log ((1 - Δ) * c t) =
        Real.log (1 - Δ) / (1 - β) + ∑' t, β ^ t * Real.log (c t)) ∧
      (∑' t, β ^ t * Real.log ((1 - Δ) * c t) = Ud ↔
        Δ = 1 - Real.exp ((1 - β) * (Ud - ∑' t, β ^ t * Real.log (c t)))) ∧
      (0 < 1 - Real.exp ((1 - β) * (Ud - ∑' t, β ^ t * Real.log (c t))) ↔
        Ud < ∑' t, β ^ t * Real.log (c t)) := by
  have h1Δ : 0 < 1 - Δ := by linarith
  have hgeo := summable_geometric_of_lt_one hβ0 hβ1
  have e : (fun t => β ^ t * Real.log ((1 - Δ) * c t)) =
      fun t => Real.log (1 - Δ) * β ^ t + β ^ t * Real.log (c t) := by
    funext t; rw [Real.log_mul h1Δ.ne' (hc t).ne']; ring
  have hsum : ∑' t, β ^ t * Real.log ((1 - Δ) * c t) =
      Real.log (1 - Δ) / (1 - β) + ∑' t, β ^ t * Real.log (c t) := by
    rw [e, (hgeo.mul_left _).tsum_add hU, tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1,
      div_eq_mul_inv]
  have hb : 0 < 1 - β := by linarith
  refine ⟨hsum, ?_, ?_⟩
  · rw [hsum]
    set Ul := ∑' t, β ^ t * Real.log (c t)
    constructor
    · intro h
      have : Real.log (1 - Δ) = (1 - β) * (Ud - Ul) := by
        field_simp at h ⊢; linarith
      rw [← this, Real.exp_log h1Δ]; ring
    · intro h
      have : 1 - Δ = Real.exp ((1 - β) * (Ud - Ul)) := by linarith
      rw [this, Real.log_exp]
      field_simp
      ring
  · rw [sub_pos, Real.exp_lt_one_iff, mul_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h; left; exact ⟨hb, by linarith⟩

/-- **AKMM, p. 186: behind the veil of ignorance.** If `u` is strictly concave on `(0, ∞)`,
`0 < π < 1`, and `(c_A, c_B)` is positive with `πc_A + (1 − π)c_B = m`, then
`πu(c_A) + (1 − π)u(c_B) ≤ u(m)`, strictly unless `c_A = c_B`: equal consumption `m` is the
unique optimum. -/
theorem veil_equal_split {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) {pr cA cB m : ℝ}
    (hpr0 : 0 < pr) (hpr1 : pr < 1) (hA : 0 < cA) (hB : 0 < cB)
    (hres : pr * cA + (1 - pr) * cB = m) :
    pr * u cA + (1 - pr) * u cB ≤ u m ∧ (cA ≠ cB → pr * u cA + (1 - pr) * u cB < u m) := by
  have hstrict : cA ≠ cB → pr * u cA + (1 - pr) * u cB < u m := by
    intro hne
    have := hu.2 (Set.mem_Ioi.2 hA) (Set.mem_Ioi.2 hB) hne hpr0 (by linarith : 0 < 1 - pr)
      (by ring)
    simpa [smul_eq_mul, hres] using this
  refine ⟨?_, hstrict⟩
  rcases eq_or_ne cA cB with h | h
  · subst h
    have : m = cA := by linarith
    subst this
    linarith
  · exact (hstrict h).le

/-- **AKMM, p. 186: "this optimization problem … delivers `c_A = c_B`".** Any solution of the
veil-of-ignorance problem (with strictly concave `u`, `0 < π < 1` and `m > 0`) has
`c_A = c_B = m`. -/
theorem veil_optimum_equal {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) {pr cA cB m : ℝ}
    (hpr0 : 0 < pr) (hpr1 : pr < 1) (hA : 0 < cA) (hB : 0 < cB) (hm : 0 < m)
    (hres : pr * cA + (1 - pr) * cB = m)
    (hopt : ∀ xA xB, 0 < xA → 0 < xB → pr * xA + (1 - pr) * xB = m →
      pr * u xA + (1 - pr) * u xB ≤ pr * u cA + (1 - pr) * u cB) : cA = m ∧ cB = m := by
  have heq : cA = cB := by
    by_contra hne
    have h1 := (veil_equal_split hu hpr0 hpr1 hA hB hres).2 hne
    have h2 := hopt m m hm hm (by ring)
    linarith
  subst heq
  constructor <;> linarith

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Overlapping generations: the endowment economy

AKMM, §6.4.1, pp. 176–180. Two-period lives, generation `t ≥ 0` with utility
`log c_y + log c_o`, the initial old with `log c`; endowments `ω_{y,t}`, `ω_{o,t}`. The sequential
equilibrium is Chapter 5's Definition 11 (`IsOGEndowEquilibrium 0 Real.log 1`).

* (6.5)–(6.6): the young's optimum (`eq_6_5_6_6`, `og_log_consumption`); the equilibrium is
  unique: autarky with `qₜ = ω_{y,t}/ω_{o,t+1}` (`og_log_equilibrium_iff`).
* Pareto optimality (`ogFeasible`, `ogDominates`, `ogParetoOptimal`); the equilibrium in
  Arrow–Debreu form (`ogADEquilibrium`, from the sequential one: `og_ad_of_seq`).
* **The First Welfare Theorem when the proof goes through** (p. 178): for any utilities strictly
  increasing in `c_y`, an equilibrium is Pareto optimal as soon as `pₜω_{y,t} → 0`, with
  `pₜ = q₀⋯q_{t−1}` (`og_fwt_value`); in particular when the present value `Σ pₜωₜ` is finite
  (`og_fwt_finite_value`). The proof sums the budgets over finitely many generations.
* The examples: `(3, 1)` (`q = 3`, net rate `−2/3`; `(2, 2)` Pareto dominates:
  `og_example_3_1`), `(1, 3)` (`q = 1/3`; Pareto optimal, and `(2, 2)` hurts the initial old:
  `og_example_1_3`), `(2, 2)` (Pareto optimal though `Σ pₜωₜ = ∞`: `og_example_2_2`, via the
  growing-transfer argument of Figure 6.3, `og_equal_endowments_optimal`).
* **Balasko–Shell for the stationary log economy**: the equilibrium is Pareto optimal iff
  `Σ 1/pₜ = ∞` iff `ω_y ≤ ω_o` (`og_balasko_shell_stationary_log`), with the book's sums
  (`og_balasko_shell_sums`).
* Transfers that stop hurt the last giver (`og_finite_transfers_hurt`).

**Correction (p. 179).** "Whenever the gross real interest rate `pₜ/p_{t+1}` converges … the
equilibrium is optimal if and only if the limit net real interest rate is equal to or above 0"
is false at 0. In the log economy with `ω_{y,t} = 1`, `ω_{o,t} = ((t+1)/(t+2))²`, the unique
equilibrium has gross rate `((t+2)/(t+3))² → 1` and is Pareto dominated
(`og_limit_rate_one_counterexample`), while the `(2, 2)` economy has gross rate `1` and is
optimal. What holds: a limit gross rate above one gives optimality (any monotone utilities,
bounded endowments: `og_limit_rate_gt_one`), and below one gives inefficiency (log utility,
young endowments bounded below: `og_limit_rate_lt_one_log`).

The general Balasko–Shell theorem (curvature and boundedness conditions the book does not
state) is not formalised.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium

/-- **AKMM, (6.5)–(6.6), p. 177.** With `q, ω_y, ω_o′ > 0`, saving `a` (in bonds paying one unit
next period) solves `max log(ω_y − qa) + log(ω_o′ + a)` iff `a = (ω_y − qω_o′)/(2q)`. -/
theorem eq_6_5_6_6 {q ωy ωo' a : ℝ} (hq : 0 < q) (hy : 0 < ωy) (ho : 0 < ωo') :
    OGSavingOpt Real.log 1 q ωy ωo' a ↔ a = (ωy - q * ωo') / (2 * q) := by
  set as := (ωy - q * ωo') / (2 * q) with has
  have h1 : ωy - q * as = (ωy + q * ωo') / 2 := by rw [has]; field_simp; ring
  have h2 : ωo' + as = (ωy / q + ωo') / 2 := by rw [has]; field_simp; ring
  have hp1 : 0 < ωy - q * as := by rw [h1]; positivity
  have hp2 : 0 < ωo' + as := by rw [h2]; positivity
  have hprod : ∀ x, (ωy - q * as) * (ωo' + as) - (ωy - q * x) * (ωo' + x) = q * (x - as) ^ 2 := by
    intro x; rw [has]; field_simp; ring
  have hval : ∀ x, 0 < ωy - q * x → 0 < ωo' + x →
      Real.log (ωy - q * x) + 1 * Real.log (ωo' + x) ≤
        Real.log (ωy - q * as) + 1 * Real.log (ωo' + as) := by
    intro x hx1 hx2
    rw [one_mul, one_mul, ← Real.log_mul hx1.ne' hx2.ne', ← Real.log_mul hp1.ne' hp2.ne']
    exact Real.log_le_log (mul_pos hx1 hx2) (by nlinarith [hprod x, sq_nonneg (x - as)])
  constructor
  · rintro ⟨ha1, ha2, hmax⟩
    have h3 := hmax as hp1 hp2
    have h4 := hval a ha1 ha2
    rw [one_mul, one_mul, ← Real.log_mul hp1.ne' hp2.ne', ← Real.log_mul ha1.ne' ha2.ne'] at h3 h4
    have heq := Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos hp1 hp2))
      (Set.mem_Ioi.2 (mul_pos ha1 ha2)) (le_antisymm h3 h4)
    have hz : q * (a - as) ^ 2 = 0 := by rw [← hprod a, heq, sub_self]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 hz).resolve_left hq.ne')
    linarith
  · rintro rfl
    exact ⟨hp1, hp2, hval⟩

/-- **AKMM, (6.5)–(6.6), p. 177: consumption and saving.** At the optimum
`c_{y,t} = (ω_y + qₜω_o)/2`, `c_{o,t+1} = (ω_y/qₜ + ω_o)/2`, and saving when young is
`ω_y − c_{y,t} = (ω_y − qₜω_o)/2`. -/
theorem og_log_consumption {q ωy ωo' : ℝ} (hq : 0 < q) :
    ωy - q * ((ωy - q * ωo') / (2 * q)) = (ωy + q * ωo') / 2 ∧
      ωo' + (ωy - q * ωo') / (2 * q) = (ωy / q + ωo') / 2 ∧
      ωy - (ωy + q * ωo') / 2 = (ωy - q * ωo') / 2 := by
  refine ⟨by field_simp; ring, by field_simp; ring, by ring⟩

/-- **AKMM, p. 177: the equilibrium is unique.** With positive endowments and bond prices, the
log economy is in equilibrium (Chapter 5's Definition 11, `t₀ = 0`) iff `a_{t+1} = 0`,
consumption is autarkic and `qₜ = ω_{y,t}/ω_{o,t+1}` at every date. -/
theorem og_log_equilibrium_iff {ωy ωo cy co a q : ℕ → ℝ} (hωy : ∀ t, 0 < ωy t)
    (hωo : ∀ t, 0 < ωo t) (hq : ∀ t, 0 < q t) :
    IsOGEndowEquilibrium 0 Real.log 1 ωy ωo cy co a q ↔
      (∀ t, q t = ωy t / ωo (t + 1)) ∧ ∀ t, a (t + 1) = 0 ∧ cy t = ωy t ∧ co t = ωo t := by
  constructor
  · intro he
    have hz := og_autarky he fun t => (hq t).ne'
    refine ⟨fun t => ?_, hz⟩
    have hopt := (he.1 t (Nat.zero_le _)).2.2
    rw [(hz t).1, eq_6_5_6_6 (hq t) (hωy t) (hωo (t + 1))] at hopt
    have := hωo (t + 1)
    have := hq t
    field_simp at hopt ⊢
    linarith
  · rintro ⟨hqt, hz⟩
    refine ⟨fun t _ => ⟨?_, ?_, ?_⟩, (hz 0).2.2, fun t => by rw [(hz t).2.1, (hz t).2.2]⟩
    · rw [(hz t).2.1, (hz t).1, mul_zero, sub_zero]
    · rw [(hz (t + 1)).2.2, (hz t).1, add_zero]
    · rw [(hz t).1, eq_6_5_6_6 (hq t) (hωy t) (hωo (t + 1)), hqt t]
      have := hωo (t + 1)
      field_simp
      ring

/-- A feasible allocation of the OG endowment economy (AKMM, p. 177): positive consumption and
`c_{y,t} + c_{o,t} ≤ ω_{y,t} + ω_{o,t}`; `co 0` is the initial old's consumption. -/
def ogFeasible (ωy ωo cy co : ℕ → ℝ) : Prop :=
  (∀ t, 0 < cy t ∧ 0 < co t) ∧ ∀ t, cy t + co t ≤ ωy t + ωo t

/-- `(cy', co')` Pareto dominates `(cy, co)`: the initial old (utility increasing in `c_{o,0}`)
and every generation `t` (utility `Uₜ(c_{y,t}, c_{o,t+1})`) are at least as well off, one
strictly. -/
def ogDominates (U : ℕ → ℝ → ℝ → ℝ) (cy co cy' co' : ℕ → ℝ) : Prop :=
  co 0 ≤ co' 0 ∧ (∀ t, U t (cy t) (co (t + 1)) ≤ U t (cy' t) (co' (t + 1))) ∧
    (co 0 < co' 0 ∨ ∃ t, U t (cy t) (co (t + 1)) < U t (cy' t) (co' (t + 1)))

/-- AKMM, p. 178: Pareto optimality in the OG endowment economy. -/
def ogParetoOptimal (U : ℕ → ℝ → ℝ → ℝ) (ωy ωo cy co : ℕ → ℝ) : Prop :=
  ogFeasible ωy ωo cy co ∧ ¬ ∃ cy' co', ogFeasible ωy ωo cy' co' ∧ ogDominates U cy co cy' co'

/-- The utility of every generation in §6.4.1: `log c_y + log c_o`. -/
noncomputable def ogLogU : ℕ → ℝ → ℝ → ℝ := fun _ x y => Real.log x + Real.log y

/-- AKMM, p. 178: the equilibrium in Arrow–Debreu form, budgets in date-`t` goods: positive
consumption, the initial old consume `ω_{o,0}`, markets clear, and each generation's bundle
satisfies `c_y + qₜc_o′ = ω_y + qₜω_o′` and maximises `Uₜ` on that budget. -/
def ogADEquilibrium (U : ℕ → ℝ → ℝ → ℝ) (ωy ωo q cy co : ℕ → ℝ) : Prop :=
  (∀ t, 0 < cy t ∧ 0 < co t) ∧ co 0 = ωo 0 ∧ (∀ t, cy t + co t = ωy t + ωo t) ∧
    ∀ t, cy t + q t * co (t + 1) = ωy t + q t * ωo (t + 1) ∧
      ∀ x y, 0 < x → 0 < y → x + q t * y ≤ ωy t + q t * ωo (t + 1) →
        U t x y ≤ U t (cy t) (co (t + 1))

/-- AKMM, p. 178: a sequential equilibrium of the log economy (Chapter 5's Definition 11) is an
equilibrium in Arrow–Debreu form. -/
theorem og_ad_of_seq {ωy ωo cy co a q : ℕ → ℝ} (hωo : ∀ t, 0 < ωo t)
    (he : IsOGEndowEquilibrium 0 Real.log 1 ωy ωo cy co a q) :
    ogADEquilibrium ogLogU ωy ωo q cy co := by
  obtain ⟨hopt, hco0, hclear⟩ := he
  have hco : ∀ t, 0 < co t := by
    intro t
    rcases t with _ | t
    · rw [hco0]; exact hωo 0
    · obtain ⟨_, h2, h3⟩ := hopt t (Nat.zero_le _)
      rw [h2]; exact h3.2.1
  refine ⟨fun t => ⟨?_, hco t⟩, hco0, hclear, fun t => ⟨?_, fun x y hx hy hb => ?_⟩⟩
  · obtain ⟨h1, _, h3⟩ := hopt t (Nat.zero_le _)
    rw [h1]; exact h3.1
  · obtain ⟨h1, h2, _⟩ := hopt t (Nat.zero_le _)
    rw [h1, h2]; ring
  · obtain ⟨h1, h2, ⟨_, _, hmax⟩⟩ := hopt t (Nat.zero_le _)
    have hs1 : x ≤ ωy t - q t * (y - ωo (t + 1)) := by linarith
    have := hmax (y - ωo (t + 1)) (by linarith) (by linarith)
    simp only [one_mul, add_sub_cancel] at this
    simp only [ogLogU, h1, h2]
    linarith [Real.log_le_log hx hs1]

/-- **AKMM, p. 178: the First Welfare Theorem in the OG economy when the proof goes through.**
If every `Uₜ` is strictly increasing in `c_y`, bond prices are positive, `(cy, co)` is an
equilibrium in Arrow–Debreu form and `pₜω_{y,t} → 0` with `pₜ = q₀⋯q_{t−1}`, the equilibrium is
Pareto optimal. -/
theorem og_fwt_value {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    (hq : ∀ t, 0 < q t) (he : ogADEquilibrium U ωy ωo q cy co)
    (hlim : Tendsto (fun t => seqPrice q t * ωy t) atTop (𝓝 0)) :
    ogParetoOptimal U ωy ωo cy co := by
  obtain ⟨hpos, hco0, hclear, hgen⟩ := he
  refine ⟨⟨hpos, fun t => (hclear t).le⟩, ?_⟩
  rintro ⟨cy', co', ⟨hpos', hfeas'⟩, hold, hle, hstrict⟩
  set P := seqPrice q with hP
  have hPpos : ∀ t, 0 < P t := seqPrice_pos hq
  have hP0 : P 0 = 1 := by simp [hP, seqPrice]
  -- each generation's alternative costs at least its wealth, strictly for a strict gain
  have hcost : ∀ t, ωy t + q t * ωo (t + 1) ≤ cy' t + q t * co' (t + 1) := by
    intro t
    by_contra hcon
    push Not at hcon
    set x' := ωy t + q t * ωo (t + 1) - q t * co' (t + 1)
    have hx' : cy' t < x' := by simp only [x']; linarith
    have := (hgen t).2 x' (co' (t + 1)) (by linarith [(hpos' t).1]) (hpos' (t + 1)).2
      (by simp only [x']; linarith)
    have := hU t _ _ _ (hpos' t).1 hx' (hpos' (t + 1)).2
    linarith [hle t]
  have hcost_strict : ∀ t, U t (cy t) (co (t + 1)) < U t (cy' t) (co' (t + 1)) →
      ωy t + q t * ωo (t + 1) < cy' t + q t * co' (t + 1) := by
    intro t ht
    by_contra hcon
    push Not at hcon
    have := (hgen t).2 _ _ (hpos' t).1 (hpos' (t + 1)).2 hcon
    linarith
  set g : ℕ → ℝ := fun t => P t * (cy' t + q t * co' (t + 1) - (ωy t + q t * ωo (t + 1)))
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (hPpos t).le (by linarith [hcost t])
  set gold := co' 0 - ωo 0
  have hgold : 0 ≤ gold := by simp only [gold]; linarith
  -- the summed budgets
  have hsum : ∀ N, ∑ t ∈ Finset.range N, g t + gold ≤ P N * (ωy N - cy' N) := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, hP0, one_mul, gold]
              linarith [hfeas' 0]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep : P N * (ωy N - cy' N) + g N ≤ P (N + 1) * (ωy (N + 1) - cy' (N + 1)) := by
        have e : P N * (ωy N - cy' N) + g N = P (N + 1) * (co' (N + 1) - ωo (N + 1)) := by
          simp only [g, hP, seqPrice_succ]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (by linarith [hfeas' (N + 1)]) (hPpos _).le
      linarith
  -- a strictly positive gap
  obtain ⟨G, T, hG, hGT⟩ : ∃ G T, 0 < G ∧ ∀ N, T < N → G ≤ ∑ t ∈ Finset.range N, g t + gold := by
    rcases hstrict with h | ⟨T, hT⟩
    · refine ⟨gold, 0, by simp only [gold]; linarith, fun N _ => ?_⟩
      linarith [Finset.sum_nonneg fun t (_ : t ∈ Finset.range N) => hg0 t]
    · refine ⟨g T, T, mul_pos (hPpos T) (by linarith [hcost_strict T hT]), fun N hN => ?_⟩
      have := Finset.single_le_sum (fun t _ => hg0 t) (Finset.mem_range.2 hN)
      linarith
  have hev : ∀ᶠ N in atTop, P N * ωy N < G := hlim.eventually (gt_mem_nhds hG)
  obtain ⟨N, hN⟩ := (hev.and (eventually_gt_atTop T)).exists
  have h1 := hGT N hN.2
  have h2 := hsum N
  have h3 : 0 < P N * cy' N := mul_pos (hPpos N) (hpos' N).1
  linarith [hN.1]

/-- **AKMM, p. 178: finite present value.** If `Σ pₜ(ω_{y,t} + ω_{o,t})` converges (positive
endowments), `pₜω_{y,t} → 0`, so `og_fwt_value` applies: the equilibrium is Pareto optimal. -/
theorem og_fwt_finite_value {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    (hq : ∀ t, 0 < q t) (hωy : ∀ t, 0 < ωy t) (hωo : ∀ t, 0 < ωo t)
    (he : ogADEquilibrium U ωy ωo q cy co)
    (hsum : Summable fun t => seqPrice q t * (ωy t + ωo t)) : ogParetoOptimal U ωy ωo cy co := by
  refine og_fwt_value hU hq he ?_
  have h0 := hsum.tendsto_atTop_zero
  refine squeeze_zero (fun t => (mul_pos (seqPrice_pos hq t) (hωy t)).le) (fun t => ?_) h0
  exact mul_le_mul_of_nonneg_left (by linarith [hωo t]) (seqPrice_pos hq t).le

/-- `log` is strictly increasing in `c_y`. -/
theorem og_logU_mono : ∀ t x x' y, 0 < x → x < x' → 0 < y → ogLogU t x y < ogLogU t x' y := by
  intro _ x x' y hx hxx' _
  simp only [ogLogU]
  linarith [Real.log_lt_log hx hxx']

/-- The stationary autarky equilibrium in Arrow–Debreu form at `q = ω_y/ω_o`. -/
theorem og_stationary_ad {ωy ωo : ℝ} (hy : 0 < ωy) (ho : 0 < ωo) :
    ogADEquilibrium ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy / ωo) (fun _ => ωy)
      (fun _ => ωo) := by
  refine og_ad_of_seq (a := fun _ => 0) (fun _ => ho) ?_
  exact (og_log_equilibrium_iff (fun _ => hy) (fun _ => ho) (fun _ => div_pos hy ho)).2
    ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- **AKMM, pp. 179–180 and Figure 6.3: the `(ω, ω)` economy.** With `ω_y = ω_o = ω > 0` and log
utility, autarky is Pareto optimal. A dominating allocation would need transfers to the old
`εₜ = c_{o,t} − ω ≥ 0`, positive at some date, with `ε_{t+1} − εₜ ≥ εₜ²/ω`; they would grow
without bound, but `εₜ < ω`. -/
theorem og_equal_endowments_optimal {ω : ℝ} (hω : 0 < ω) :
    ogParetoOptimal ogLogU (fun _ => ω) (fun _ => ω) (fun _ => ω) (fun _ => ω) := by
  refine ⟨⟨fun _ => ⟨hω, hω⟩, fun _ => le_rfl⟩, ?_⟩
  rintro ⟨cy', co', ⟨hpos, hfeas⟩, hold, hle, hstrict⟩
  set ε : ℕ → ℝ := fun t => co' t - ω with hε
  have hlt : ∀ t, ε t < ω := fun t => by
    simp only [hε]; linarith [hfeas t, (hpos t).1]
  have hy : ∀ t, cy' t ≤ ω - ε t := fun t => by simp only [hε]; linarith [hfeas t]
  -- each generation: `(ω − εₜ)(ω + ε_{t+1}) ≥ c_{y,t}c_{o,t+1} ≥ ω²`
  have hprod : ∀ t, ω * ω ≤ cy' t * co' (t + 1) := by
    intro t
    have := hle t
    simp only [ogLogU] at this
    rw [← Real.log_mul hω.ne' hω.ne', ← Real.log_mul (hpos t).1.ne' (hpos (t + 1)).2.ne'] at this
    exact (Real.log_le_log_iff (mul_pos hω hω) (mul_pos (hpos t).1 (hpos (t + 1)).2)).1 this
  have hkey : ∀ t, ω * ω ≤ (ω - ε t) * (ω + ε (t + 1)) := by
    intro t
    have h1 : cy' t * co' (t + 1) ≤ (ω - ε t) * co' (t + 1) :=
      mul_le_mul_of_nonneg_right (hy t) (hpos (t + 1)).2.le
    have h2 : co' (t + 1) = ω + ε (t + 1) := by simp only [hε]; ring
    rw [h2] at h1
    linarith [hprod t]
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp only [hε]; linarith
    | succ t ih =>
      have := hkey t
      have := hlt t
      by_contra hneg
      push Not at hneg
      nlinarith
  have hgrow : ∀ t, ε t * ε t ≤ ω * (ε (t + 1) - ε t) := by
    intro t
    have h1 := hkey t
    have h2 := hnn t
    have h3 := hlt t
    have h4 : ε t * ε t ≤ (ε (t + 1) - ε t) * (ω - ε t) := by nlinarith
    have h5 : 0 ≤ ε (t + 1) - ε t := by
      by_contra hneg
      push Not at hneg
      nlinarith
    nlinarith
  -- a strictly positive transfer
  obtain ⟨s, hs⟩ : ∃ s, 0 < ε s := by
    rcases hstrict with h | ⟨T, hT⟩
    · exact ⟨0, by simp only [hε]; linarith⟩
    · refine ⟨T + 1, ?_⟩
      have hT' : ω * ω < cy' T * co' (T + 1) := by
        simp only [ogLogU] at hT
        rw [← Real.log_mul hω.ne' hω.ne', ← Real.log_mul (hpos T).1.ne'
          (hpos (T + 1)).2.ne'] at hT
        exact (Real.log_lt_log_iff (mul_pos hω hω) (mul_pos (hpos T).1 (hpos (T + 1)).2)).1 hT
      have h1 : cy' T * co' (T + 1) ≤ (ω - ε T) * co' (T + 1) :=
        mul_le_mul_of_nonneg_right (hy T) (hpos (T + 1)).2.le
      have h2 : co' (T + 1) = ω + ε (T + 1) := by simp only [hε]; ring
      rw [h2] at h1
      have := hnn T
      have := hlt T
      by_contra hneg
      push Not at hneg
      nlinarith
  -- linear growth from date `s`
  have hlin : ∀ n : ℕ, ε s ≤ ε (s + n) ∧ ε s + n * (ε s * ε s / ω) ≤ ε (s + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hg := hgrow (s + n)
      have hsq : ε s * ε s ≤ ε (s + n) * ε (s + n) :=
        mul_le_mul ih.1 ih.1 hs.le (hs.le.trans ih.1)
      have : ε s * ε s / ω ≤ ε (s + n + 1) - ε (s + n) := by
        rw [div_le_iff₀ hω]; nlinarith
      push_cast
      rw [← add_assoc]
      constructor <;> nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (ω / (ε s * ε s / ω))
  have hq : 0 < ε s * ε s / ω := by positivity
  have h1 := (hlin n).2
  have h2 := hlt (s + n)
  have : ω < n * (ε s * ε s / ω) := by rwa [div_lt_iff₀ hq] at hn
  linarith

/-- **AKMM, p. 178: `ω_y > ω_o`.** The constant allocation `m = (ω_y + ω_o)/2` is feasible and
Pareto dominates autarky: the initial old gain, and every generation gains since
`2 log m > log ω_y + log ω_o`. -/
theorem og_stationary_improvement {ωy ωo : ℝ} (ho : 0 < ωo) (hlt : ωo < ωy) :
    ogFeasible (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2) (fun _ => (ωy + ωo) / 2) ∧
      ogDominates ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2)
        (fun _ => (ωy + ωo) / 2) ∧
      ¬ ogParetoOptimal ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy) (fun _ => ωo) := by
  have hm : 0 < (ωy + ωo) / 2 := by linarith
  have hgain : Real.log ωy + Real.log ωo < Real.log ((ωy + ωo) / 2) + Real.log ((ωy + ωo) / 2) := by
    rw [← Real.log_mul (by linarith) ho.ne', ← Real.log_mul hm.ne' hm.ne']
    exact Real.log_lt_log (by nlinarith) (by nlinarith [sq_pos_of_pos (sub_pos.2 hlt)])
  have hF : ogFeasible (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2)
      (fun _ => (ωy + ωo) / 2) := ⟨fun _ => ⟨hm, hm⟩, fun _ => by linarith⟩
  have hD : ogDominates ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => (ωy + ωo) / 2)
      (fun _ => (ωy + ωo) / 2) :=
    ⟨by linarith, fun _ => hgain.le, Or.inl (by linarith)⟩
  exact ⟨hF, hD, fun h => h.2 ⟨_, _, hF, hD⟩⟩

/-- The Arrow–Debreu prices of the stationary economy: `pₜ = qᵗ`. -/
theorem og_seqPrice_const (q : ℝ) (t : ℕ) : seqPrice (fun _ => q) t = q ^ t := by
  simp [seqPrice]

/-- **AKMM, pp. 178–179: Balasko–Shell in the stationary log economy.** With constant positive
endowments, the unique equilibrium (autarky at `q = ω_y/ω_o`, `pₜ = qᵗ`) is Pareto optimal iff
`Σ 1/pₜ = ∞` (the series does not converge), iff `ω_y ≤ ω_o`. -/
theorem og_balasko_shell_stationary_log {ωy ωo : ℝ} (hy : 0 < ωy) (ho : 0 < ωo) :
    (ogParetoOptimal ogLogU (fun _ => ωy) (fun _ => ωo) (fun _ => ωy) (fun _ => ωo) ↔
      ¬ Summable fun t => 1 / seqPrice (fun _ => ωy / ωo) t) ∧
    (¬ Summable (fun t => 1 / seqPrice (fun _ => ωy / ωo) t) ↔ ωy ≤ ωo) := by
  have hsum : (¬ Summable fun t => 1 / seqPrice (fun _ => ωy / ωo) t) ↔ ωy ≤ ωo := by
    have e : (fun t => 1 / seqPrice (fun _ => ωy / ωo) t) = fun t => (ωo / ωy) ^ t := by
      funext t; rw [og_seqPrice_const, one_div, ← inv_pow, inv_div]
    rw [e, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
      abs_of_pos (div_pos ho hy), div_lt_one hy, not_lt]
  refine ⟨?_, hsum⟩
  rw [hsum]
  constructor
  · intro hPO
    by_contra hlt
    push Not at hlt
    exact (og_stationary_improvement ho hlt).2.2 hPO
  · intro hle
    rcases hle.lt_or_eq with hlt | heq
    · refine og_fwt_value og_logU_mono (fun _ => div_pos hy ho) (og_stationary_ad hy ho) ?_
      simp only [og_seqPrice_const]
      have hr : ωy / ωo < 1 := (div_lt_one ho).2 hlt
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hy ho).le hr).mul_const ωy
      simpa using this
    · subst heq
      exact og_equal_endowments_optimal hy

/-- **AKMM, p. 179: the book's sums.** For `qₜ = 3`, `Σ 1/pₜ = Σ 3^{−t} = 3/2`; for `qₜ = 1/3`
and for `qₜ = 1` the series `Σ 1/pₜ` diverges. -/
theorem og_balasko_shell_sums :
    ∑' t, 1 / seqPrice (fun _ => (3 : ℝ)) t = 3 / 2 ∧
      ¬ Summable (fun t => 1 / seqPrice (fun _ => (1 / 3 : ℝ)) t) ∧
      ¬ Summable (fun t => 1 / seqPrice (fun _ => (1 : ℝ)) t) := by
  simp only [og_seqPrice_const]
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun t : ℕ => 1 / (3 : ℝ) ^ t) = fun t => (1 / 3 : ℝ) ^ t := by
      funext t; rw [one_div_pow]
    rw [e, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  · have e : (fun t : ℕ => 1 / (1 / 3 : ℝ) ^ t) = fun t => (3 : ℝ) ^ t := by
      funext t; rw [one_div_pow, one_div_one_div]
    rw [e, summable_geometric_iff_norm_lt_one]
    norm_num
  · simp only [one_pow, div_one]
    exact fun h => by simpa using h.tendsto_atTop_zero

/-- **AKMM, p. 178: the `(3, 1)` economy.** The unique equilibrium price is `q = 3`, the gross
real rate is `1/3` (net `−2/3`, "−67%"), and the allocation `(2, 2)` Pareto dominates autarky
`(3, 1)`: the initial old gain (`2 > 1`), every generation gains
(`log 2 + log 2 > log 3 + log 1`). -/
theorem og_example_3_1 :
    (3 : ℝ) / 1 = 3 ∧ 1 / (3 : ℝ) - 1 = -2 / 3 ∧
      ogDominates ogLogU (fun _ => 3) (fun _ => 1) (fun _ => 2) (fun _ => 2) ∧
      ¬ ogParetoOptimal ogLogU (fun _ => 3) (fun _ => 1) (fun _ => 3) (fun _ => 1) := by
  have h := og_stationary_improvement (ωy := 3) (ωo := 1) one_pos (by norm_num)
  norm_num at h ⊢
  exact h.2

/-- **AKMM, p. 178: the `(1, 3)` economy.** The price is `q = 1/3` (net rate `+2`); the
allocation `(2, 2)` hurts the initial old (`2 < 3`), and autarky is Pareto optimal: the present
value of the endowments is finite and the proof of the First Welfare Theorem goes through. -/
theorem og_example_1_3 :
    (2 : ℝ) < 3 ∧ 1 / (1 / 3 : ℝ) - 1 = 2 ∧
      ogParetoOptimal ogLogU (fun _ => 1) (fun _ => 3) (fun _ => 1) (fun _ => 3) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  refine og_fwt_finite_value og_logU_mono (fun _ => by norm_num) (fun _ => one_pos)
    (fun _ => by norm_num) (og_stationary_ad one_pos (by norm_num)) ?_
  simp only [og_seqPrice_const]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _

/-- **AKMM, p. 179: the `(2, 2)` economy.** The price is `q = 1`, the present value of the
endowments diverges (so the standard proof fails), yet autarky is Pareto optimal. -/
theorem og_example_2_2 :
    ¬ Summable (fun t => seqPrice (fun _ => (2 : ℝ) / 2) t * (2 + 2)) ∧
      ogParetoOptimal ogLogU (fun _ => 2) (fun _ => 2) (fun _ => 2) (fun _ => 2) := by
  refine ⟨?_, og_equal_endowments_optimal two_pos⟩
  simp only [og_seqPrice_const]
  rw [show (2 : ℝ) / 2 = 1 by norm_num]
  simp only [one_pow, one_mul]
  intro h
  have := h.tendsto_atTop_zero
  norm_num at this

/-- **AKMM, p. 179: transfers that stop.** In the `(3, 1)` economy, if the young give one unit
to the old until some date and the transfers then stop, the last generation that gave gets
`(2, 1)`, which is worse than autarky `(3, 1)`. -/
theorem og_finite_transfers_hurt : Real.log 2 + Real.log 1 < Real.log 3 + Real.log 1 := by
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
  linarith

/-- **AKMM, p. 179 (correction): a limit gross rate above one gives optimality.** If every `Uₜ`
is strictly increasing in `c_y`, `qₜ > 0` converges to `q∞ < 1` (gross rate `1/q∞ > 1`), the
young's endowments are bounded and `(cy, co)` is an equilibrium, it is Pareto optimal. -/
theorem og_limit_rate_gt_one {U : ℕ → ℝ → ℝ → ℝ}
    (hU : ∀ t x x' y, 0 < x → x < x' → 0 < y → U t x y < U t x' y) {ωy ωo q cy co : ℕ → ℝ}
    (hq : ∀ t, 0 < q t) {qinf B : ℝ} (hlim : Tendsto q atTop (𝓝 qinf)) (hqinf : qinf < 1)
    (hωy : ∀ t, 0 < ωy t) (hB : ∀ t, ωy t ≤ B) (he : ogADEquilibrium U ωy ωo q cy co) :
    ogParetoOptimal U ωy ωo cy co := by
  refine og_fwt_value hU hq he ?_
  set ρ := (qinf + 1) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : qinf < ρ)))
  have hρ0 : 0 < ρ := lt_of_lt_of_le (hq T) (hT T le_rfl).le
  have hbound : ∀ n, seqPrice q (T + n) ≤ seqPrice q T * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, seqPrice_succ, pow_succ, ← mul_assoc]
      exact mul_le_mul ih (hT _ (by omega)).le (hq _).le
        (mul_nonneg (seqPrice_pos hq T).le (pow_nonneg hρ0.le n))
  have hgeo : Tendsto (fun n => seqPrice q T * ρ ^ n * B) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul
      (seqPrice q T)).mul_const B
  have hshift : Tendsto (fun n => seqPrice q (T + n) * ωy (T + n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (mul_pos (seqPrice_pos hq _) (hωy _)).le) (fun n => ?_) hgeo
    exact mul_le_mul (hbound n) (hB _) (hωy _).le
      (mul_nonneg (seqPrice_pos hq T).le (pow_nonneg hρ0.le n))
  rw [← tendsto_add_atTop_iff_nat T]
  simpa [add_comm] using hshift

/-- **AKMM, p. 179 (correction): a limit gross rate below one gives inefficiency** (log
utility). In the log economy with `ω_{y,t} ≥ ω_min > 0`, `ω_{o,t} > 0` and gross rate at autarky
`ω_{o,t+1}/ω_{y,t} → R < 1`, the (unique) autarkic equilibrium is not Pareto optimal: constant
transfers `δ` from the young to the old from some date on improve everyone weakly and one
generation strictly. -/
theorem og_limit_rate_lt_one_log {ωy ωo : ℕ → ℝ} {R ωmin : ℝ} (hmin : 0 < ωmin)
    (hωy : ∀ t, ωmin ≤ ωy t) (hωo : ∀ t, 0 < ωo t)
    (hlim : Tendsto (fun t => ωo (t + 1) / ωy t) atTop (𝓝 R)) (hR : R < 1) :
    ¬ ogParetoOptimal ogLogU ωy ωo ωy ωo := by
  rintro ⟨-, hno⟩
  set R' := (R + 1) / 2 with hR'
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : R < R')))
  set δ := (1 - R') * ωmin with hδ
  have hδ0 : 0 < δ := mul_pos (by linarith) hmin
  have hωy0 : ∀ t, 0 < ωy t := fun t => hmin.trans_le (hωy t)
  have hgap : ∀ t, T ≤ t → δ ≤ ωy t - ωo (t + 1) := by
    intro t ht
    have h1 := hT t ht
    rw [div_lt_iff₀ (hωy0 t)] at h1
    have : δ ≤ (1 - R') * ωy t := mul_le_mul_of_nonneg_left (hωy t) (by linarith)
    linarith
  set d : ℕ → ℝ := fun t => if T + 1 ≤ t then δ else 0 with hd
  have hdle : ∀ t, d t ≤ δ := fun t => by simp only [hd]; split_ifs <;> linarith
  have hd0 : ∀ t, 0 ≤ d t := fun t => by simp only [hd]; split_ifs <;> linarith
  have hδy : ∀ t, T + 1 ≤ t → δ < ωy t := by
    intro t ht
    have := hgap t (by omega)
    linarith [hωo (t + 1)]
  refine hno ⟨fun t => ωy t - d t, fun t => ωo t + d t, ⟨fun t => ⟨?_, ?_⟩, fun t => by linarith⟩,
    ?_, fun t => ?_, Or.inr ⟨T, ?_⟩⟩
  · by_cases ht : T + 1 ≤ t
    · simp only [hd, ht, ↓reduceIte]; linarith [hδy t ht]
    · simp only [hd, ht, ↓reduceIte]; linarith [hωy0 t]
  · linarith [hωo t, hd0 t]
  · simp only [hd, show ¬ T + 1 ≤ 0 by omega, ↓reduceIte, add_zero, le_refl]
  · -- generation `t`
    simp only [ogLogU]
    have hy := hωy0 t
    have ho := hωo (t + 1)
    by_cases ht : T + 1 ≤ t
    · have ht1 : T + 1 ≤ t + 1 := by omega
      simp only [hd, ht, ht1, ↓reduceIte]
      have hpos : 0 < ωy t - δ := by linarith [hδy t ht]
      rw [← Real.log_mul hy.ne' ho.ne', ← Real.log_mul hpos.ne' (by linarith : ωo (t + 1) + δ ≠ 0)]
      refine Real.log_le_log (mul_pos hy ho) ?_
      have := hgap t (by omega)
      nlinarith
    · simp only [hd, ht, ↓reduceIte, sub_zero]
      by_cases ht1 : T + 1 ≤ t + 1
      · simp only [ht1, ↓reduceIte]
        linarith [Real.log_le_log ho (by linarith : ωo (t + 1) ≤ ωo (t + 1) + δ)]
      · simp only [ht1, ↓reduceIte, add_zero, le_refl]
  · -- generation `T` receives `δ` when old and gives nothing
    simp only [ogLogU, hd, show ¬ T + 1 ≤ T by omega, show T + 1 ≤ T + 1 from le_rfl,
      ↓reduceIte, sub_zero]
    linarith [Real.log_lt_log (hωo (T + 1)) (by linarith : ωo (T + 1) < ωo (T + 1) + δ)]

/-- The counterexample economy of the correction: `ω_{y,t} = 1`,
`ω_{o,t} = ((t + 1)/(t + 2))²`. -/
noncomputable def ogCexOld (t : ℕ) : ℝ := (((t : ℝ) + 1) / ((t : ℝ) + 2)) ^ 2

/-- **AKMM, p. 179: the printed criterion fails at a zero limit net rate.** In the log economy
with `ω_{y,t} = 1` and `ω_{o,t} = ((t + 1)/(t + 2))²`, autarky with
`qₜ = ω_{y,t}/ω_{o,t+1}` is the equilibrium; the gross real rate
`1/qₜ = ((t + 2)/(t + 3))²` converges to `1` (limit net rate `0`, "equal to or above 0"), yet the
equilibrium is Pareto dominated: transfers `δₜ = 1/(2(t + 2))` from the young to the old make the
initial old strictly and every generation weakly better off. -/
theorem og_limit_rate_one_counterexample :
    IsOGEndowEquilibrium 0 Real.log 1 (fun _ => 1) ogCexOld (fun _ => 1) ogCexOld (fun _ => 0)
        (fun t => 1 / ogCexOld (t + 1)) ∧
      Tendsto (fun t => 1 / (1 / ogCexOld (t + 1))) atTop (𝓝 1) ∧
      ¬ ogParetoOptimal ogLogU (fun _ => 1) ogCexOld (fun _ => 1) ogCexOld := by
  have hpos : ∀ t, 0 < ogCexOld t := fun t => by unfold ogCexOld; positivity
  refine ⟨(og_log_equilibrium_iff (fun _ => one_pos) hpos
      (fun t => one_div_pos.2 (hpos (t + 1)))).2 ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩,
    ?_, ?_⟩
  · simp only [one_div_one_div, ogCexOld]
    have h : Tendsto (fun t : ℕ => ((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) atTop (𝓝 1) := by
      have e : (fun t : ℕ => ((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) =
          fun t : ℕ => 1 - 1 / ((t : ℝ) + 3) := by
        funext t
        have : (t : ℝ) + 3 ≠ 0 := by positivity
        field_simp
        ring
      rw [e]
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
      have h3 : Tendsto (fun t : ℕ => 1 / ((t : ℝ) + 3)) atTop (𝓝 0) := by
        refine this.congr fun t => ?_
        simp only [Function.comp_apply]
        push_cast
        ring_nf
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
    simpa using h.pow 2
  · rintro ⟨-, hno⟩
    set d : ℕ → ℝ := fun t => 1 / (2 * ((t : ℝ) + 2)) with hd
    have hd0 : ∀ t, 0 < d t := fun t => by simp only [hd]; positivity
    have hd1 : ∀ t, d t < 1 := fun t => by
      simp only [hd]; rw [div_lt_one (by positivity)]; linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)]
    refine hno ⟨fun t => 1 - d t, fun t => ogCexOld t + d t,
      ⟨fun t => ⟨by linarith [hd1 t], by linarith [hpos t, hd0 t]⟩, fun t => by linarith⟩,
      by linarith [hd0 0], fun t => ?_, Or.inl (by linarith [hd0 0])⟩
    simp only [ogLogU, Real.log_one, zero_add]
    have h1 : 0 < 1 - d t := by linarith [hd1 t]
    rw [← Real.log_mul h1.ne' (by linarith [hpos (t + 1), hd0 (t + 1)])]
    refine Real.log_le_log (hpos (t + 1)) ?_
    simp only [hd, ogCexOld]
    have ht : (0 : ℝ) ≤ t := t.cast_nonneg
    push_cast
    have key : (1 - 1 / (2 * ((t : ℝ) + 2))) * ((((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) ^ 2 +
        1 / (2 * ((t : ℝ) + 1 + 2))) - (((t : ℝ) + 1 + 1) / ((t : ℝ) + 1 + 2)) ^ 2 =
        ((t : ℝ) + 1) / (4 * ((t : ℝ) + 2) * ((t : ℝ) + 3) ^ 2) := by
      field_simp; ring
    have : 0 ≤ ((t : ℝ) + 1) / (4 * ((t : ℝ) + 2) * ((t : ℝ) + 3) ^ 2) := by positivity
    linarith

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Overlapping generations: intertemporal production and dynamic efficiency

AKMM, §6.4.2, pp. 180–183, and Appendix 6.A, pp. 838–839.

* **Storage** (pp. 180–181). With a storage technology of gross return `χ`, the young's problem
  is the bond problem at `q = 1/χ` (`storage_saving`): saving `(ω_y − ω_o/χ)/2`, positive iff
  `χω_y > ω_o` (for `(3, 1)`, `χ > 1/3`). The equilibrium allocation (`stEqAlloc`) is Pareto
  optimal iff `χ > 1`: for `χ ≤ 1` a pay-as-you-go transfer of the stored amount dominates it
  (`storage_not_optimal`, at `χ = 1` the book's social-security argument), and for `χ > 1` the
  summed budgets at `pₜ = χ^{−t}` rule out improvements (`storage_optimal`); together
  `storage_optimal_iff`.
* **The Diamond economy** (pp. 181–182): the law of motion
  `k_{t+1} = h(F₂(kₜ), F₁(k_{t+1}), F₂(k_{t+1}))` (`diamond_law_of_motion`) and
  `∏_{s=1}^t R_s = 1/pₜ` (`theorem_6_2_prices`).
* **Theorem 6.2** (p. 182), dynamic efficiency of a feasible path `k_{t+1} = fₜ(kₜ) − cₜ`
  (`dePath`, `deEfficient`), with the assumptions of fn. 12 (returns `Rₜ` bounded above and away
  from zero, curvature bounded, stated as quadratic bounds on `fₜ` around `kₜ`): if
  `Σₜ ∏_{s=1}^t R_s = ∞` the path is efficient (`theorem_6_2_efficient`); if the sum is finite it
  is inefficient (`theorem_6_2_inefficient`, which also needs `kₜ` bounded away from zero);
  together `theorem_6_2`. Concrete instances satisfy all hypotheses
  (`theorem_6_2_instance_efficient`, `theorem_6_2_instance_inefficient`).
* **Theorem .5** (Appendix 6.A): a steady state `k⋆` is efficient iff `R⋆ = f′(k⋆) ≥ 1`
  (`theorem_A5`, from `theorem_A5_inefficient`, which needs only the derivative, and
  `theorem_A5_efficient`, by the book's growing-deficit argument made rigorous with strict
  concavity); at a steady state the criterion of Theorem 6.2 is `R⋆ ≥ 1` (`theorem_A5_cass`, from
  Miao's `op_cass_steady_state`).

**Corrections.** (i) p. 181: the storage problem is the bond problem at `qₜ = 1/χ`, not `qₜ = χ`
(`storage_printed_counterexample`). (ii) p. 838: `f(k)` must be `F(k, ω_y + ω_o) + (1 − δ)k`,
not `F(k, ω_y + ω_o) + 1 − δ`: with the printed `f` the criterion `f′(k⋆) ≥ 1` misclassifies
(`appendix_6A_printed_f`). (iii) p. 839: the book's limit `c_∞ = f(k⋆ − ε_∞) − (k⋆ − ε_∞)` has
the wrong sign (`ε₂ = k₂ − k⋆ < 0`) and the unbounded growth of the deficits is only sketched;
`theorem_A5_efficient` proves it. (iv) p. 838: part (i) needs no concavity, only `f′(k⋆) < 1`.
-/

namespace AKMM.Welfare

open Filter Topology AKMM.CompetitiveEquilibrium Miao.OverlappingGenerations

/-! ### Storage -/

/-- **AKMM, p. 181 (corrected): the storage problem.** Storing `s` when young gives
`(ω_y − s, ω_o + χs)`, which is the bond plan `a = χs` at the price `q = 1/χ`. With `χ, ω_y,
ω_o > 0`, the optimal plan is `s = (ω_y − ω_o/χ)/2` (equations (6.5)–(6.6) at `q = 1/χ`), with
`c_y = (ω_y + ω_o/χ)/2`, `c_o = (χω_y + ω_o)/2`; storage is positive iff `χω_y > ω_o`. -/
theorem storage_saving {χ ωy ωo s : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo) :
    (OGSavingOpt Real.log 1 (1 / χ) ωy ωo (χ * s) ↔ s = (ωy - ωo / χ) / 2) ∧
      ωy - (ωy - ωo / χ) / 2 = (ωy + ωo / χ) / 2 ∧
      ωo + χ * ((ωy - ωo / χ) / 2) = (χ * ωy + ωo) / 2 ∧
      (0 < (ωy - ωo / χ) / 2 ↔ ωo < χ * ωy) := by
  refine ⟨?_, by ring, by field_simp; ring, ?_⟩
  · rw [eq_6_5_6_6 (one_div_pos.2 hχ) hy ho]
    have e : (ωy - 1 / χ * ωo) / (2 * (1 / χ)) = χ * ((ωy - ωo / χ) / 2) := by
      field_simp
    rw [e]
    constructor
    · intro h; exact mul_left_cancel₀ hχ.ne' h
    · intro h; rw [h]
  · rw [div_pos_iff_of_pos_right two_pos, sub_pos, div_lt_iff₀ hχ, mul_comm]

/-- **AKMM, p. 181: the printed price `qₜ = χ` gives the wrong allocation.** In the `(3, 1)`
economy with `χ = 2`, (6.5)–(6.6) at the printed `q = 2` give `(c_y, c_o) = (5/2, 5/4)`, which is
not on the storage budget line (storing `1/2` returns `ω_o + 1 = 2`), while the correct optimum
at `q = 1/χ` is `(7/4, 7/2)`, with strictly higher utility. -/
theorem storage_printed_counterexample :
    (3 + 2 * 1) / 2 = (5 / 2 : ℝ) ∧ (3 / 2 + 1) / 2 = (5 / 4 : ℝ) ∧
      (1 : ℝ) + 2 * (3 - 5 / 2) ≠ 5 / 4 ∧
      OGSavingOpt Real.log 1 (1 / 2) 3 1 (2 * (5 / 4)) ∧
      Real.log (5 / 2) + Real.log (5 / 4) < Real.log (7 / 4) + Real.log (7 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [(storage_saving (by norm_num : (0 : ℝ) < 2) (by norm_num) one_pos).1]
    norm_num
  · rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)

/-- A feasible allocation of the storage economy (AKMM, p. 180): positive consumption,
nonnegative storage `sₜ` by the young at `t` (returning `χsₜ` at `t + 1`), and
`c_{y,t} + c_{o,t} + sₜ ≤ ω_y + ω_o + χs_{t−1}` (`s_{−1} = 0`). -/
def stFeasible (ωy ωo χ : ℝ) (cy co s : ℕ → ℝ) : Prop :=
  (∀ t, 0 < cy t ∧ 0 < co t ∧ 0 ≤ s t) ∧ cy 0 + co 0 + s 0 ≤ ωy + ωo ∧
    ∀ t, cy (t + 1) + co (t + 1) + s (t + 1) ≤ ωy + ωo + χ * s t

/-- Pareto optimality in the storage economy (log utility for every generation). -/
def stParetoOptimal (ωy ωo χ : ℝ) (cy co s : ℕ → ℝ) : Prop :=
  stFeasible ωy ωo χ cy co s ∧
    ¬ ∃ cy' co' s', stFeasible ωy ωo χ cy' co' s' ∧ ogDominates ogLogU cy co cy' co'

/-- The equilibrium allocation of the storage economy: every young stores
`s⋆ = (ω_y − ω_o/χ)/2` and consumes `(ω_y + ω_o/χ)/2`; the old consume `(χω_y + ω_o)/2`, except the
initial old, who consume `ω_o`. -/
noncomputable def stEqAlloc (ωy ωo χ : ℝ) : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun _ => (ωy + ωo / χ) / 2, fun t => if t = 0 then ωo else (χ * ωy + ωo) / 2,
    fun _ => (ωy - ωo / χ) / 2)

/-- The equilibrium allocation is feasible when storage is positive. -/
theorem stEqAlloc_feasible {ωy ωo χ : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) :
    stFeasible ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1 (stEqAlloc ωy ωo χ).2.2 := by
  have hs' := ((storage_saving hχ hy ho (s := 0)).2.2.2).2 hs
  refine ⟨fun t => ⟨by simp only [stEqAlloc]; positivity, ?_, hs'.le⟩, ?_, fun t => ?_⟩
  · simp only [stEqAlloc]; split_ifs <;> positivity
  · simp only [stEqAlloc, ↓reduceIte]; linarith
  · simp only [stEqAlloc, Nat.add_one_ne_zero, ↓reduceIte]
    field_simp
    linarith

/-- **AKMM, p. 181: storage with `χ ≤ 1` is inefficient.** When storage is positive and `χ ≤ 1`,
the young can instead give the amount `s⋆` to the current old (a pay-as-you-go scheme, no
storage): every generation's old-age consumption becomes `ω_o + s⋆ ≥ ω_o + χs⋆`, and the initial
old get `ω_o + s⋆ > ω_o`. At `χ = 1` and `(3, 1)` this is the social-security allocation
`(2, 2)` with the initial old at `2` instead of `1`. -/
theorem storage_not_optimal {ωy ωo χ : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) (hχ1 : χ ≤ 1) :
    ¬ stParetoOptimal ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1
      (stEqAlloc ωy ωo χ).2.2 := by
  rintro ⟨-, hno⟩
  set ss := (ωy - ωo / χ) / 2 with hss
  have hs' : 0 < ss := ((storage_saving hχ hy ho (s := 0)).2.2.2).2 hs
  have hcy : 0 < (ωy + ωo / χ) / 2 := by positivity
  have hco : (χ * ωy + ωo) / 2 ≤ ωo + ss := by
    have e : (χ * ωy + ωo) / 2 = ωo + χ * ss := by rw [hss]; field_simp; ring
    rw [e]; nlinarith
  refine hno ⟨fun _ => (ωy + ωo / χ) / 2, fun _ => ωo + ss, fun _ => 0,
    ⟨fun _ => ⟨hcy, by linarith, le_rfl⟩, ?_, fun _ => ?_⟩, ?_, fun t => ?_, Or.inl ?_⟩
  · rw [hss]; field_simp; linarith
  · rw [hss]; field_simp; linarith
  · simp only [stEqAlloc, ↓reduceIte]; linarith
  · simp only [stEqAlloc, ogLogU, Nat.add_one_ne_zero, ↓reduceIte]
    linarith [Real.log_le_log (by positivity) hco]
  · simp only [stEqAlloc, ↓reduceIte]; linarith

/-- **AKMM, p. 181: storage with `χ > 1` is efficient.** When `χ > 1` and storage is positive,
the equilibrium allocation is Pareto optimal: at the prices `pₜ = χ^{−t}` every generation's
alternative must cost at least its wealth, and the summed budgets leave a surplus of at most
`χ^{−N}ω_y → 0`. -/
theorem storage_optimal {ωy ωo χ : ℝ} (hχ : 1 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) :
    stParetoOptimal ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1
      (stEqAlloc ωy ωo χ).2.2 := by
  have hχ0 : 0 < χ := by linarith
  refine ⟨stEqAlloc_feasible hχ0 hy ho hs, ?_⟩
  rintro ⟨cy', co', s', ⟨hpos, h0, hres⟩, hold, hle, hstrict⟩
  set W := ωy + ωo / χ with hW
  set cs := (ωy + ωo / χ) / 2 with hcs
  set os := (χ * ωy + ωo) / 2 with hos
  have hcs0 : 0 < cs := by positivity
  have hos0 : 0 < os := by positivity
  -- the generation's optimum on the budget `x + y/χ ≤ W`
  have hopt : ∀ x y, 0 < x → 0 < y → x + y / χ ≤ W →
      Real.log x + Real.log y ≤ Real.log cs + Real.log os := by
    intro x y hx hy' hb
    have hsv := ((storage_saving hχ0 hy ho (s := (ωy - ωo / χ) / 2)).1).2 rfl
    obtain ⟨_, _, hmax⟩ := hsv
    have h1 : x ≤ ωy - 1 / χ * (y - ωo) := by
      have : 1 / χ * (y - ωo) = y / χ - ωo / χ := by ring
      rw [hW] at hb; linarith
    have := hmax (y - ωo) (by linarith) (by linarith)
    have e1 : ωy - 1 / χ * (χ * ((ωy - ωo / χ) / 2)) = cs := by rw [hcs]; field_simp; ring
    have e2 : ωo + χ * ((ωy - ωo / χ) / 2) = os := by rw [hos]; field_simp; ring
    rw [e1, e2, one_mul, one_mul, add_sub_cancel] at this
    linarith [Real.log_le_log hx h1]
  have hgenU : ∀ t, ogLogU t ((stEqAlloc ωy ωo χ).1 t) ((stEqAlloc ωy ωo χ).2.1 (t + 1)) =
      Real.log cs + Real.log os := by
    intro t; simp [stEqAlloc, ogLogU, hcs, hos]
  -- costs at the prices `χ^{−t}`
  have hcost : ∀ t, W ≤ cy' t + co' (t + 1) / χ := by
    intro t
    by_contra hcon
    push Not at hcon
    set x' := W - co' (t + 1) / χ
    have hx' : cy' t < x' := by simp only [x']; linarith
    have := hopt x' (co' (t + 1)) (by linarith [(hpos t).1]) (hpos (t + 1)).2.1
      (by simp only [x']; linarith)
    have h2 := hle t
    rw [hgenU] at h2
    simp only [ogLogU] at h2
    linarith [Real.log_lt_log (hpos t).1 hx']
  have hcost_strict : ∀ t, Real.log cs + Real.log os < ogLogU t (cy' t) (co' (t + 1)) →
      W < cy' t + co' (t + 1) / χ := by
    intro t ht
    by_contra hcon
    push Not at hcon
    have := hopt _ _ (hpos t).1 (hpos (t + 1)).2.1 hcon
    simp only [ogLogU] at ht
    linarith
  set ρ := χ⁻¹ with hρ
  have hρ0 : 0 < ρ := inv_pos.2 hχ0
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ hχ
  set g : ℕ → ℝ := fun t => ρ ^ t * (cy' t + co' (t + 1) / χ - W)
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (pow_nonneg hρ0.le t) (by linarith [hcost t])
  set gold := co' 0 - ωo
  have hco0 : (stEqAlloc ωy ωo χ).2.1 0 = ωo := by simp [stEqAlloc]
  have hgold : 0 ≤ gold := by simp only [gold]; rw [hco0] at hold; linarith
  have hsum : ∀ N, ∑ t ∈ Finset.range N, g t + gold ≤ ρ ^ N * (ωy - cy' N - s' N) := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, one_mul, gold]
              linarith
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep : ρ ^ N * (ωy - cy' N - s' N) + g N ≤
          ρ ^ (N + 1) * (ωy - cy' (N + 1) - s' (N + 1)) := by
        have e : ρ ^ N * (ωy - cy' N - s' N) + g N =
            ρ ^ (N + 1) * (co' (N + 1) - ωo) - ρ ^ N * s' N := by
          simp only [g, hW, hρ, pow_succ]; field_simp; ring
        have e2 : ρ ^ N * s' N = ρ ^ (N + 1) * (χ * s' N) := by
          rw [pow_succ, hρ]; field_simp
        rw [e, e2, ← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ0.le _)
        linarith [hres N]
      linarith
  obtain ⟨G, T, hG, hGT⟩ : ∃ G T, 0 < G ∧ ∀ N, T < N → G ≤ ∑ t ∈ Finset.range N, g t + gold := by
    rcases hstrict with h | ⟨T, hT⟩
    · refine ⟨gold, 0, by simp only [gold]; rw [hco0] at h; linarith, fun N _ => ?_⟩
      linarith [Finset.sum_nonneg fun t (_ : t ∈ Finset.range N) => hg0 t]
    · rw [hgenU] at hT
      refine ⟨g T, T, mul_pos (pow_pos hρ0 T) (by linarith [hcost_strict T hT]), fun N hN => ?_⟩
      have := Finset.single_le_sum (fun t _ => hg0 t) (Finset.mem_range.2 hN)
      linarith
  have hlim : Tendsto (fun N => ρ ^ N * ωy) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const ωy
  obtain ⟨N, hN⟩ := ((hlim.eventually (gt_mem_nhds hG)).and (eventually_gt_atTop T)).exists
  have h1 := hGT N hN.2
  have h2 := hsum N
  have h3 : 0 < ρ ^ N * (cy' N + s' N) :=
    mul_pos (pow_pos hρ0 N) (by linarith [(hpos N).1, (hpos N).2.2])
  nlinarith [hN.1]

/-- **AKMM, p. 181: "the equilibrium is actually optimal when `χ > 1` but not when `χ ≤ 1`".**
For positive storage (`χω_y > ω_o`), the storage equilibrium is Pareto optimal iff `χ > 1`. -/
theorem storage_optimal_iff {ωy ωo χ : ℝ} (hχ : 0 < χ) (hy : 0 < ωy) (ho : 0 < ωo)
    (hs : ωo < χ * ωy) :
    stParetoOptimal ωy ωo χ (stEqAlloc ωy ωo χ).1 (stEqAlloc ωy ωo χ).2.1
      (stEqAlloc ωy ωo χ).2.2 ↔ 1 < χ := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    exact storage_not_optimal hχ hy ho hs hle h
  · intro h
    exact storage_optimal h hy ho hs

/-! ### The Diamond economy -/

/-- **AKMM, p. 182: the equilibrium law of motion.** If saving is `sₜ = h(wₜ, r_{t+1}, w_{t+1})`,
the asset market clears (`sₜ = k_{t+1}`) and prices are marginal products `rₜ = F₁(kₜ)`,
`wₜ = F₂(kₜ)`, then `k_{t+1} = h(F₂(kₜ), F₁(k_{t+1}), F₂(k_{t+1}))`. -/
theorem diamond_law_of_motion {h : ℝ → ℝ → ℝ → ℝ} {F1 F2 : ℝ → ℝ} {s k r w : ℕ → ℝ}
    (hs : ∀ t, s t = h (w t) (r (t + 1)) (w (t + 1))) (hclear : ∀ t, s t = k (t + 1))
    (hr : ∀ t, r t = F1 (k t)) (hw : ∀ t, w t = F2 (k t)) (t : ℕ) :
    k (t + 1) = h (F2 (k t)) (F1 (k (t + 1))) (F2 (k (t + 1))) := by
  have := hs t
  rw [hclear t, hr, hw, hw] at this
  exact this

/-- **AKMM, p. 182: `∏_{s=1}^t R_s = 1/pₜ`.** With `p₀ = 1` and the no-arbitrage condition
`p_{s+1}R_{s+1} = p_s` (the gross return between `s` and `s + 1` is `p_s/p_{s+1}`), the product
of returns is the reciprocal of the Arrow–Debreu price. -/
theorem theorem_6_2_prices {p R : ℕ → ℝ} (hp : ∀ t, p t ≠ 0) (hp0 : p 0 = 1)
    (hR : ∀ s, p (s + 1) * R (s + 1) = p s) (t : ℕ) :
    ∏ s ∈ Finset.range t, R (s + 1) = 1 / p t := by
  induction t with
  | zero => simp [hp0]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have := hR t
    have := hp (t + 1)
    have := hp t
    field_simp
    linarith

/-! ### Theorem 6.2: dynamic efficiency -/

/-- A feasible capital path from `k₀` (AKMM, p. 182): `kₜ ≥ 0` and consumption
`cₜ = fₜ(kₜ) − k_{t+1} ≥ 0`, where `fₜ(k) = F(k, ωₜ) + (1 − δ)k` is the gross resource. -/
def dePath (f : ℕ → ℝ → ℝ) (k0 : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = k0 ∧ ∀ t, 0 ≤ k t ∧ 0 ≤ f t (k t) - k (t + 1)

/-- Consumption along a path. -/
def deCons (f : ℕ → ℝ → ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ := f t (k t) - k (t + 1)

/-- AKMM, p. 181: a feasible path is dynamically efficient if no feasible path from the same
`k₀` gives at least as much consumption at every date and more at some date. -/
def deEfficient (f : ℕ → ℝ → ℝ) (k : ℕ → ℝ) : Prop :=
  dePath f (k 0) k ∧ ¬ ∃ k', dePath f (k 0) k' ∧ (∀ t, deCons f k t ≤ deCons f k' t) ∧
    ∃ t, deCons f k t < deCons f k' t

/-- **Theorem 6.2, efficiency half** (AKMM, p. 182, with fn. 12). Let `k` be a feasible path,
bounded by `K̄`, with returns `0 < Rₜ ≤ R̄` that are supergradients of `fₜ` at `kₜ`, and with
curvature bounded below, `fₜ(y) ≤ fₜ(kₜ) + Rₜ(y − kₜ) − (a/2)(y − kₜ)²` for `0 ≤ y ≤ kₜ`
(`a > 0`; this is `−f″ ≥ a`). If `Σₜ ∏_{s=1}^t R_s = ∞`, the path is dynamically efficient. -/
theorem theorem_6_2_efficient {f : ℕ → ℝ → ℝ} {k R : ℕ → ℝ} {a Rbar Kbar : ℝ} (ha : 0 < a)
    (hR : ∀ t, 0 < R t) (hRbar : ∀ t, R t ≤ Rbar) (hK : ∀ t, k t ≤ Kbar)
    (hsup : ∀ t y, 0 ≤ y → f t y ≤ f t (k t) + R t * (y - k t))
    (hstrong : ∀ t y, 0 ≤ y → y ≤ k t →
      f t y ≤ f t (k t) + R t * (y - k t) - a / 2 * (y - k t) ^ 2)
    (hpath : dePath f (k 0) k)
    (hdiv : ¬ Summable fun t => ∏ s ∈ Finset.range t, R (s + 1)) : deEfficient f k := by
  refine ⟨hpath, ?_⟩
  rintro ⟨k', ⟨hk0, hk'⟩, hle, T, hT⟩
  set ε : ℕ → ℝ := fun t => k t - k' t with hε
  have hRbar0 : 0 < Rbar := (hR 0).trans_le (hRbar 0)
  -- `ε_{t+1} ≥ Rₜεₜ + dₜ`
  have hrec : ∀ t, R t * ε t + (deCons f k' t - deCons f k t) ≤ ε (t + 1) := by
    intro t
    have := hsup t (k' t) (hk' t).1
    simp only [deCons, hε]
    linarith
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp [hε, hk0]
    | succ t ih => nlinarith [hrec t, hle t, hR t]
  have hεK : ∀ t, ε t ≤ Kbar := fun t => by simp only [hε]; linarith [(hk' t).1, hK t]
  have hT1 : 0 < ε (T + 1) := by nlinarith [hrec T, hR T, hnn T]
  -- the quadratic recursion
  set b := a / (2 * Rbar) with hb
  have hb0 : 0 < b := by positivity
  have hquad : ∀ t, R t * ε t * (1 + b * ε t) ≤ ε (t + 1) := by
    intro t
    have h1 := hstrong t (k' t) (hk' t).1 (by linarith [hnn t])
    have h2 : ε (t + 1) ≥ R t * ε t + a / 2 * ε t ^ 2 := by
      have := hle t
      simp only [deCons, hε] at this ⊢
      nlinarith
    have h3 : R t * ε t * (1 + b * ε t) ≤ R t * ε t + a / 2 * ε t ^ 2 := by
      have hR' : R t * b ≤ a / 2 := by
        rw [hb, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
        nlinarith [hRbar t, hR t]
      nlinarith [sq_nonneg (ε t), hnn t]
    linarith
  have hpos : ∀ n, 0 < ε (T + 1 + n) := by
    intro n
    induction n with
    | zero => simpa using hT1
    | succ n ih =>
      have := hquad (T + 1 + n)
      rw [← add_assoc]
      have hp : 0 < R (T + 1 + n) * ε (T + 1 + n) * (1 + b * ε (T + 1 + n)) :=
        mul_pos (mul_pos (hR _) ih) (by positivity)
      linarith
  -- the weighted reciprocals decrease by at least `c·P_{T+n}`
  set P : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, R (s + 1) with hP
  have hPpos : ∀ t, 0 < P t := fun t => Finset.prod_pos fun s _ => hR (s + 1)
  set c := b / (1 + b * Kbar) with hc
  have hKbar0 : 0 ≤ Kbar := (hnn 0).trans (hεK 0)
  have hc0 : 0 < c := by positivity
  set v : ℕ → ℝ := fun n => P (T + n) / ε (T + 1 + n) with hv
  have hvstep : ∀ n, v (n + 1) + c * P (T + n) ≤ v n := by
    intro n
    have he := hpos n
    have he1 := hpos (n + 1)
    have hRn := hR (T + n + 1)
    have hq := hquad (T + 1 + n)
    rw [show T + 1 + n + 1 = T + 1 + (n + 1) by ring] at hq
    have hPs : P (T + (n + 1)) = P (T + n) * R (T + n + 1) := by
      simp only [hP, ← add_assoc, Finset.prod_range_succ]
    simp only [hv, hPs]
    have hKe : ε (T + 1 + n) ≤ Kbar := hεK _
    have hPn := hPpos (T + n)
    -- `P R / ε' ≤ P/(ε(1 + bε))`
    have h1 : P (T + n) * R (T + n + 1) / ε (T + 1 + (n + 1)) ≤
        P (T + n) / (ε (T + 1 + n) * (1 + b * ε (T + 1 + n))) := by
      rw [div_le_div_iff₀ he1 (by positivity)]
      have : R (T + n + 1) = R (T + 1 + n) := by ring_nf
      rw [this] at hRn ⊢
      nlinarith [mul_le_mul_of_nonneg_left hq hPn.le]
    -- `1/(ε(1 + bε)) ≤ 1/ε − c`
    have h2 : P (T + n) / (ε (T + 1 + n) * (1 + b * ε (T + 1 + n))) + c * P (T + n) ≤
        P (T + n) / ε (T + 1 + n) := by
      have hden : 0 < 1 + b * Kbar := by positivity
      rw [hc]
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) he]
      have : b / (1 + b * Kbar) * (1 + b * ε (T + 1 + n)) ≤ b := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        have := mul_le_mul_of_nonneg_left hKe (mul_pos hb0 hb0).le
        nlinarith
      have e : (P (T + n) + b / (1 + b * Kbar) * P (T + n) *
          (ε (T + 1 + n) * (1 + b * ε (T + 1 + n)))) * ε (T + 1 + n) =
          P (T + n) * ε (T + 1 + n) * (1 + b / (1 + b * Kbar) *
            (1 + b * ε (T + 1 + n)) * ε (T + 1 + n)) := by ring
      rw [e]
      have e2 : P (T + n) * (ε (T + 1 + n) * (1 + b * ε (T + 1 + n))) =
          P (T + n) * ε (T + 1 + n) * (1 + b * ε (T + 1 + n)) := by ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith
    linarith
  have hvsum : ∀ n, v n + c * ∑ j ∈ Finset.range n, P (T + j) ≤ v 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hvstep n]
  have hvpos : ∀ n, 0 < v n := fun n => div_pos (hPpos _) (hpos n)
  have hbdd : ∀ n, ∑ j ∈ Finset.range n, P (T + j) ≤ v 0 / c := by
    intro n
    rw [le_div_iff₀ hc0]
    linarith [hvsum n, hvpos n]
  have hsumm : Summable fun j => P (j + T) :=
    summable_of_sum_range_le (fun j => (hPpos _).le) fun n => by
      simpa [add_comm] using hbdd n
  exact hdiv ((summable_nat_add_iff T).1 hsumm)

/-- **Theorem 6.2, inefficiency half** (AKMM, p. 182, with fn. 12). Let `k` be a feasible path
with `kₜ ≥ k_low > 0`, returns `Rₜ ≥ R_low > 0`, and curvature bounded above,
`fₜ(y) ≥ fₜ(kₜ) + Rₜ(y − kₜ) − (M/2)(y − kₜ)²` for `0 ≤ y ≤ kₜ` (`−f″ ≤ M`). If
`Σₜ ∏_{s=1}^t R_s < ∞`, the path is dynamically inefficient: reducing capital by
`εₜ`, with `ε₀ = 0`, `ε₁ = e` small and `ε_{t+1} = Rₜεₜ + (M/2)εₜ²`, raises consumption at date
`0` and lowers it nowhere. -/
theorem theorem_6_2_inefficient {f : ℕ → ℝ → ℝ} {k R : ℕ → ℝ} {M Rlow klow : ℝ} (hM : 0 ≤ M)
    (hRlow : 0 < Rlow) (hR : ∀ t, Rlow ≤ R t) (hklow : 0 < klow) (hk : ∀ t, klow ≤ k t)
    (hlower : ∀ t y, 0 ≤ y → y ≤ k t →
      f t (k t) + R t * (y - k t) - M / 2 * (y - k t) ^ 2 ≤ f t y)
    (hpath : dePath f (k 0) k)
    (hsum : Summable fun t => ∏ s ∈ Finset.range t, R (s + 1)) : ¬ deEfficient f k := by
  rintro ⟨-, hno⟩
  set P : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, R (s + 1) with hP
  have hR0 : ∀ t, 0 < R t := fun t => hRlow.trans_le (hR t)
  have hPpos : ∀ t, 0 < P t := fun t => Finset.prod_pos fun s _ => hR0 (s + 1)
  set S := ∑' t, P t with hS
  have hPS : ∀ t, P t ≤ S := fun t =>
    hsum.le_tsum t fun j _ => (hPpos j).le
  have hS0 : 0 < S := (hPpos 0).trans_le (hPS 0)
  set c := M / (2 * Rlow) with hc
  have hc0 : 0 ≤ c := by positivity
  set e := 1 / (c * S + S / klow + 1) with he
  have he0 : 0 < e := by positivity
  -- the reductions `e_n = ε_{n+1}`
  let es : ℕ → ℝ := fun n => Nat.rec e (fun m x => R (m + 1) * x + M / 2 * x ^ 2) n
  have hes0 : es 0 = e := rfl
  have hes : ∀ n, es (n + 1) = R (n + 1) * es n + M / 2 * es n ^ 2 := fun n => rfl
  have hespos : ∀ n, 0 < es n := by
    intro n
    induction n with
    | zero => exact he0
    | succ n ih => rw [hes]; have := hR0 (n + 1); positivity
  -- `P_n/e_n ≥ 1/e − cΣ_{j<n} P_j`
  have hvstep : ∀ n, P n / es n - c * P n ≤ P (n + 1) / es (n + 1) := by
    intro n
    have hen := hespos n
    have hRn := hR0 (n + 1)
    have hPs : P (n + 1) = P n * R (n + 1) := by simp only [hP, Finset.prod_range_succ]
    rw [hPs, hes]
    have hcR : M / (2 * R (n + 1)) ≤ c := by
      rw [hc]; exact div_le_div_of_nonneg_left hM (by positivity) (by linarith [hR (n + 1)])
    have hPn := hPpos n
    have h1 : M / 2 ≤ c * R (n + 1) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R (n + 1))] at hcR
      linarith
    have hD : 0 < R (n + 1) * es n + M / 2 * es n ^ 2 := by positivity
    have key : (P n - c * P n * es n) * (R (n + 1) * es n + M / 2 * es n ^ 2) ≤
        P n * R (n + 1) * es n := by
      have e1 : (P n - c * P n * es n) * (R (n + 1) * es n + M / 2 * es n ^ 2) =
          P n * R (n + 1) * es n + P n * es n ^ 2 * (M / 2 - c * R (n + 1)) -
            c * P n * (M / 2) * es n ^ 3 := by ring
      rw [e1]
      have h2 : P n * es n ^ 2 * (M / 2 - c * R (n + 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      have h3 : 0 ≤ c * P n * (M / 2) * es n ^ 3 := by positivity
      linarith
    calc P n / es n - c * P n = (P n - c * P n * es n) / es n := by field_simp
      _ = (P n - c * P n * es n) * (R (n + 1) * es n + M / 2 * es n ^ 2) /
          (es n * (R (n + 1) * es n + M / 2 * es n ^ 2)) := by field_simp
      _ ≤ P n * R (n + 1) * es n / (es n * (R (n + 1) * es n + M / 2 * es n ^ 2)) :=
          div_le_div_of_nonneg_right key (by positivity)
      _ = P n * R (n + 1) / (R (n + 1) * es n + M / 2 * es n ^ 2) := by field_simp
  have hv : ∀ n, 1 / e - c * ∑ j ∈ Finset.range n, P j ≤ P n / es n := by
    intro n
    induction n with
    | zero => simp [hP, hes0]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hvstep n]
  have hsmall : ∀ n, es n ≤ klow := by
    intro n
    have h1 := hv n
    have h2 : c * ∑ j ∈ Finset.range n, P j ≤ c * S :=
      mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun j _ => (hPpos j).le) hc0
    have h3 : 1 / e = c * S + S / klow + 1 := by rw [he, one_div_one_div]
    have h4 : S / klow < P n / es n := by linarith
    rw [div_lt_div_iff₀ hklow (hespos n)] at h4
    nlinarith [hPS n, hespos n]
  -- the alternative path
  set ε : ℕ → ℝ := fun t => Nat.casesOn t 0 fun n => es n with hεdef
  have hε0 : ε 0 = 0 := rfl
  have hεs : ∀ n, ε (n + 1) = es n := fun n => rfl
  have hεnn : ∀ t, 0 ≤ ε t := fun t => by
    rcases t with _ | n
    · exact le_rfl
    · exact (hespos n).le
  have hεk : ∀ t, ε t ≤ k t := fun t => by
    rcases t with _ | n
    · exact (hpath.2 0).1
    · rw [hεs]; exact (hsmall n).trans (hk _)
  have hrec : ∀ t, R t * ε t + M / 2 * ε t ^ 2 ≤ ε (t + 1) := by
    intro t
    rcases t with _ | n
    · simp only [hε0, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact (hespos 0).le
    · exact (hes n).ge
  set k' : ℕ → ℝ := fun t => k t - ε t with hk'
  have hgain : ∀ t, deCons f k t ≤ deCons f k' t := by
    intro t
    have := hlower t (k' t) (by simp only [hk']; linarith [hεk t])
      (by simp only [hk']; linarith [hεnn t])
    simp only [deCons, hk'] at this ⊢
    have hsq : (k t - ε t - k t) ^ 2 = ε t ^ 2 := by ring
    rw [hsq] at this
    nlinarith [hrec t]
  refine hno ⟨k', ⟨by simp [hk', hε0], fun t => ⟨by simp only [hk']; linarith [hεk t],
    by have := hgain t; simp only [deCons] at this; linarith [(hpath.2 t).2]⟩⟩, hgain, 0, ?_⟩
  simp only [deCons, hk', hε0, sub_zero, hεs, hes0]
  linarith

/-- **Theorem 6.2** (AKMM, p. 182). Under the assumptions of fn. 12 (stated as in
`theorem_6_2_efficient` and `theorem_6_2_inefficient`, with the curvature bounds `a ≤ −f″ ≤ M`
as two-sided quadratic bounds), a feasible path is dynamically efficient iff
`Σₜ ∏_{s=1}^t R_s = ∞`. -/
theorem theorem_6_2 {f : ℕ → ℝ → ℝ} {k R : ℕ → ℝ} {a M Rlow Rbar klow Kbar : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hRlow : 0 < Rlow) (hR : ∀ t, Rlow ≤ R t) (hRbar : ∀ t, R t ≤ Rbar)
    (hklow : 0 < klow) (hk : ∀ t, klow ≤ k t) (hK : ∀ t, k t ≤ Kbar)
    (hsup : ∀ t y, 0 ≤ y → f t y ≤ f t (k t) + R t * (y - k t))
    (hstrong : ∀ t y, 0 ≤ y → y ≤ k t →
      f t y ≤ f t (k t) + R t * (y - k t) - a / 2 * (y - k t) ^ 2)
    (hlower : ∀ t y, 0 ≤ y → y ≤ k t →
      f t (k t) + R t * (y - k t) - M / 2 * (y - k t) ^ 2 ≤ f t y)
    (hpath : dePath f (k 0) k) :
    deEfficient f k ↔ ¬ Summable fun t => ∏ s ∈ Finset.range t, R (s + 1) := by
  constructor
  · intro he hs
    exact theorem_6_2_inefficient hM hRlow hR hklow hk hlower hpath hs he
  · intro hdiv
    exact theorem_6_2_efficient ha (fun t => hRlow.trans_le (hR t)) hRbar hK hsup hstrong hpath
      hdiv

/-- The quadratic technology `f(y) = 3y − y²/2` of the instances: around any `k` it equals its
second-order expansion with `f′(k) = 3 − k` and `f″ = −1`. -/
theorem de_quadratic_expansion (k y : ℝ) :
    3 * y - y ^ 2 / 2 = (3 * k - k ^ 2 / 2) + (3 - k) * (y - k) - 1 / 2 * (y - k) ^ 2 := by ring

/-- **Theorem 6.2, a concrete efficient instance.** With `f(y) = 3y − y²/2` and the steady path
`kₜ = 1` (`R = 2`, consumption `3/2`), every hypothesis of `theorem_6_2` holds and the path is
dynamically efficient. -/
theorem theorem_6_2_instance_efficient :
    deEfficient (fun _ y => 3 * y - y ^ 2 / 2) (fun _ => 1) := by
  refine theorem_6_2_efficient (a := 1) (R := fun _ => 2) (Rbar := 2) (Kbar := 1) one_pos
    (fun _ => two_pos) (fun _ => le_rfl) (fun _ => le_rfl) (fun t y _ => ?_)
    (fun t y _ _ => ?_) ⟨rfl, fun _ => ⟨zero_le_one, by norm_num⟩⟩ ?_
  · nlinarith [sq_nonneg (y - 1)]
  · nlinarith [sq_nonneg (y - 1)]
  · simp only [Finset.prod_const, Finset.card_range]
    rw [summable_geometric_iff_norm_lt_one]
    norm_num

/-- **Theorem 6.2, a concrete inefficient instance.** With `f(y) = 3y − y²/2` and the steady path
`kₜ = 5/2` (`R = 1/2`, consumption `15/8`), every hypothesis of `theorem_6_2_inefficient` holds
and the path is dynamically inefficient. -/
theorem theorem_6_2_instance_inefficient :
    ¬ deEfficient (fun _ y => 3 * y - y ^ 2 / 2) (fun _ => 5 / 2) := by
  refine theorem_6_2_inefficient (M := 1) (R := fun _ => 1 / 2) (Rlow := 1 / 2) (klow := 5 / 2)
    zero_le_one (by norm_num) (fun _ => le_rfl) (by norm_num) (fun _ => le_rfl)
    (fun t y _ _ => ?_) ⟨rfl, fun _ => ⟨by norm_num, by norm_num⟩⟩ ?_
  · nlinarith [sq_nonneg (y - 5 / 2)]
  · simp only [Finset.prod_const, Finset.card_range]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-! ### Appendix 6.A: Theorem .5 -/

/-- **Theorem .5 (i)** (AKMM, p. 838): a steady state `k⋆ > 0` with `f′(k⋆) = R⋆ < 1` is
inefficient. A permanent reduction of capital by a small `ε > 0` raises `c₀` by `ε` and every
later `cₜ` by `ε − (f(k⋆) − f(k⋆ − ε)) > 0`. Only the derivative at `k⋆` is used. -/
theorem theorem_A5_inefficient {f : ℝ → ℝ} {kstar Rstar : ℝ} (hk : 0 < kstar)
    (hc : 0 ≤ f kstar - kstar) (hd : HasDerivAt f Rstar kstar) (hR : Rstar < 1) :
    ¬ deEfficient (fun _ => f) (fun _ => kstar) := by
  rintro ⟨-, hno⟩
  have hsl := hd.tendsto_slope_zero_left
  have hev1 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t⁻¹ • (f (kstar + t) - f kstar) < 1 :=
    hsl.eventually (gt_mem_nhds hR)
  have hev2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), -kstar < t :=
    nhdsWithin_le_nhds (lt_mem_nhds (by linarith))
  have hev3 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  rw [smul_eq_mul] at h1
  set ε := -t with hε
  have hε0 : 0 < ε := by linarith
  have hgain : f kstar - f (kstar - ε) < ε := by
    have : t⁻¹ * (f (kstar + t) - f kstar) = (f kstar - f (kstar - ε)) / ε := by
      rw [hε]; field_simp; ring_nf
    rw [this, div_lt_one hε0] at h1
    exact h1
  set k' : ℕ → ℝ := fun n => if n = 0 then kstar else kstar - ε
  have hcons : ∀ n, deCons (fun _ => f) (fun _ => kstar) n ≤ deCons (fun _ => f) k' n := by
    intro n
    simp only [deCons, k']
    rcases n with _ | n
    · simp only [↓reduceIte, Nat.add_one_ne_zero]; linarith
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]; linarith
  refine hno ⟨k', ⟨rfl, fun n => ⟨?_, ?_⟩⟩, hcons, 0, ?_⟩
  · simp only [k']; split_ifs <;> linarith
  · have := hcons n
    simp only [deCons] at this
    linarith
  · simp only [deCons, k', ↓reduceIte, Nat.add_one_ne_zero]; linarith

/-- **Theorem .5 (ii)** (AKMM, p. 839): a steady state `k⋆ > 0` with `f′(k⋆) = R⋆ ≥ 1` is
efficient, for `f` strictly concave on `[0, ∞)`. With `εₜ = k⋆ − k′ₜ` the deficits of a
dominating path satisfy `εₜ ≥ 0`, become positive, and then grow by at least
`η = h(k⋆) − h(k⋆ − ε_{T+1}) > 0` per period, `h(k) = f(k) − k`; this contradicts `εₜ ≤ k⋆`. -/
theorem theorem_A5_efficient {f : ℝ → ℝ} {kstar Rstar : ℝ} (hk : 0 < kstar)
    (hc : 0 ≤ f kstar - kstar) (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hd : HasDerivAt f Rstar kstar) (hR : 1 ≤ Rstar) :
    deEfficient (fun _ => f) (fun _ => kstar) := by
  have hks : kstar ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 hk.le
  refine ⟨⟨rfl, fun _ => ⟨hk.le, by simpa using hc⟩⟩, ?_⟩
  rintro ⟨k', ⟨hk0, hk'⟩, hle, T, hT⟩
  set ε : ℕ → ℝ := fun t => kstar - k' t with hε
  have hrec : ∀ t, f kstar - f (kstar - ε t) ≤ ε (t + 1) ∧
      (deCons (fun _ => f) (fun _ => kstar) t < deCons (fun _ => f) k' t →
        f kstar - f (kstar - ε t) < ε (t + 1)) := by
    intro t
    have h1 := hle t
    simp only [deCons, hε, sub_sub_cancel] at h1 ⊢
    exact ⟨by linarith, fun h => by linarith⟩
  have hsup : ∀ y, 0 ≤ y → f y ≤ f kstar + Rstar * (y - kstar) := fun y hy =>
    op_concave_tangent hconc.concaveOn hks (Set.mem_Ici.2 hy) hd
  have hεk : ∀ t, ε t ≤ kstar := fun t => by simp only [hε]; linarith [(hk' t).1]
  have hnn : ∀ t, 0 ≤ ε t := by
    intro t
    induction t with
    | zero => simp [hε, hk0]
    | succ t ih =>
      have h1 := (hrec t).1
      have h2 := hsup (kstar - ε t) (by linarith [hεk t])
      nlinarith
  have hT1 : 0 < ε (T + 1) := by
    have h1 := (hrec T).2 hT
    have h2 := hsup (kstar - ε T) (by linarith [hεk T])
    nlinarith [hnn T]
  -- `h(y) = f(y) − y` is nondecreasing on `[0, k⋆]` and strictly below `h(k⋆)` there
  have hlt : ∀ y, 0 ≤ y → y < kstar → f y - y < f kstar - kstar := by
    intro y hy hyk
    have := op_strictConcave_tangent hconc hks (Set.mem_Ici.2 hy) hyk.ne hd
    nlinarith
  have hmono : ∀ y z, 0 ≤ y → y ≤ z → z ≤ kstar → f y - y ≤ f z - z := by
    intro y z hy hyz hzk
    rcases hzk.lt_or_eq with hzk | rfl
    · rcases hyz.lt_or_eq with hyz | rfl
      · -- `z` is a convex combination of `y` and `k⋆`
        set lam := (kstar - z) / (kstar - y) with hlam
        have hl0 : 0 < lam := div_pos (by linarith) (by linarith)
        have hl1 : lam < 1 := by rw [hlam, div_lt_one (by linarith)]; linarith
        have hne : kstar - y ≠ 0 := (sub_pos.2 (by linarith)).ne'
        have hz : lam * y + (1 - lam) * kstar = z := by rw [hlam]; field_simp; ring
        have hcc := hconc.concaveOn.2 (Set.mem_Ici.2 hy) hks hl0.le (by linarith : 0 ≤ 1 - lam)
          (by ring)
        simp only [smul_eq_mul, hz] at hcc
        have := hlt y hy (by linarith)
        nlinarith
      · exact le_rfl
    · rcases hyz.lt_or_eq with hyz | rfl
      · exact (hlt y hy hyz).le
      · exact le_rfl
  set η := (f kstar - kstar) - (f (kstar - ε (T + 1)) - (kstar - ε (T + 1))) with hη
  have hη0 : 0 < η := by
    have := hlt (kstar - ε (T + 1)) (by linarith [hεk (T + 1)]) (by linarith)
    rw [hη]; linarith
  have hgrow : ∀ n : ℕ, ε (T + 1) + n * η ≤ ε (T + 1 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := (hrec (T + 1 + n)).1
      have hge : ε (T + 1) ≤ ε (T + 1 + n) := by
        have : 0 ≤ (n : ℝ) * η := by positivity
        linarith
      have h2 := hmono (kstar - ε (T + 1 + n)) (kstar - ε (T + 1)) (by linarith [hεk (T + 1 + n)])
        (by linarith) (by linarith)
      rw [show T + 1 + (n + 1) = T + 1 + n + 1 by ring]
      push_cast
      rw [hη] at *
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (kstar / η)
  have h1 := hgrow n
  have h2 := hεk (T + 1 + n)
  rw [div_lt_iff₀ hη0] at hn
  linarith

/-- **Theorem .5** (AKMM, Appendix 6.A, p. 838). For `f` strictly concave on `[0, ∞)` with
derivative `R⋆ = f′(k⋆)` at a steady state `k⋆ > 0` with `c⋆ = f(k⋆) − k⋆ ≥ 0`, the steady state
is efficient iff `R⋆ ≥ 1`. -/
theorem theorem_A5 {f : ℝ → ℝ} {kstar Rstar : ℝ} (hk : 0 < kstar) (hc : 0 ≤ f kstar - kstar)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : HasDerivAt f Rstar kstar) :
    deEfficient (fun _ => f) (fun _ => kstar) ↔ 1 ≤ Rstar := by
  constructor
  · intro he
    by_contra hlt
    push Not at hlt
    exact theorem_A5_inefficient hk hc hd hlt he
  · exact theorem_A5_efficient hk hc hconc hd

/-- **AKMM, p. 182: the criterion of Theorem 6.2 at a steady state.** With `Rₜ = R⋆ > 0` for all
`t`, `Σₜ ∏_{s=1}^t R_s = ∞` iff `R⋆ ≥ 1` (Miao's `op_cass_steady_state` with `g_n = 1`), the
condition of Theorem .5. -/
theorem theorem_A5_cass {Rstar : ℝ} {R : ℕ → ℝ} (hR : 0 < Rstar) (hRs : ∀ s, R s = Rstar) :
    (¬ Summable fun t => ∏ s ∈ Finset.range t, R (s + 1)) ↔ 1 ≤ Rstar := by
  have := op_cass_steady_state (gn := 1) one_pos hR hRs
  simpa using this

/-- **AKMM, p. 838: the printed `f` misclassifies.** With `F(k) = 2√k` (labour fixed), `δ = 1/2`
and the steady state `k⋆ = 4`, the correct `f(k) = F(k) + (1 − δ)k` has `f′(4) = 1`, so the
steady state is efficient by Theorem .5, but the printed `f(k) = F(k) + 1 − δ` has
`f′(4) = 1/2 < 1`,
which would classify it as inefficient. -/
theorem appendix_6A_printed_f :
    HasDerivAt (fun k => 2 * √k + (1 - 1 / 2) * k) 1 4 ∧
      HasDerivAt (fun k => 2 * √k + (1 - 1 / 2)) (1 / 2) 4 ∧
      deEfficient (fun _ => fun k => 2 * √k + (1 - 1 / 2) * k) (fun _ => 4) := by
  have hs : HasDerivAt (fun k : ℝ => 2 * √k) (1 / 2) 4 := by
    have h := (Real.hasDerivAt_sqrt (by norm_num : (4 : ℝ) ≠ 0)).const_mul 2
    have e : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e] at h
    convert h using 1; norm_num
  have h1 : HasDerivAt (fun k => 2 * √k + (1 - 1 / 2) * k) 1 4 :=
    (hs.add ((hasDerivAt_id (4 : ℝ)).const_mul (1 - 1 / 2))).congr_deriv (by norm_num)
  refine ⟨h1, hs.add_const (1 - 1 / 2), ?_⟩
  have hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k + (1 - 1 / 2) * k) := by
    have hsq := Real.strictConcaveOn_sqrt
    have h2 : StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k) := by
      refine ⟨hsq.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
      have := hsq.2 hx hy hxy ha hb hab
      simp only [smul_eq_mul] at this ⊢
      linarith
    exact h2.add_concaveOn ((concaveOn_id (convex_Ici 0)).smul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2))
  have e : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact theorem_A5_efficient (by norm_num) (by simp only [e]; norm_num) hconc h1 le_rfl

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic inefficiency in the warm-glow model

AKMM, §6.4.3, p. 183. One-period lives, utility `u(cₜ) + Ab_{t+1}`, budget
`cₜ + b_{t+1} = (1 + rₜ − δ)bₜ + wₜ`, `b = k` in equilibrium.

* The consumption choice `u′(c̄) = A` is optimal (`warmglow_consumption`), and the law of motion
  is `k_{t+1} = (1 − δ)kₜ + F(kₜ, 1) − c̄` (`warmglow_law_of_motion`). Steady states solve
  `φ(k) = c̄` with `φ(k) = F(k, 1) − δk` (`warmglow_steady_iff`).
* With `φ` continuous and strictly concave on `[0, ∞)`, `φ(0) = 0`, `0 < c̄ < φ(k̂)` for some `k̂`
  and `φ < c̄` far out, there are exactly two positive steady states `k₁ < k₂`
  (`warmglow_two_steady_states`); `φ > c̄` between them and `φ < c̄` outside (`warmglow_sign`).
* At `k₂` the slope `1 + F₁ − δ = 1 + φ′(k₂)` is below `1`; at `k₁` it is above `1`
  (`warmglow_slopes`). The upper steady state is stable: every path from `k₀ > k₁` converges to
  `k₂` (`warmglow_stable`); paths from below `k₁` never approach it (`warmglow_lower_unstable`).
* The upper steady state is dynamically inefficient (`warmglow_inefficient`, by Theorem .5(i)).
* A concrete instance, `F(k, 1) = 2√k`, `δ = 1/2`, `c̄ = 3/2`, with steady states `1` and `9`
  (`warmglow_instance`).

**Correction (p. 183).** "There are two positive steady states" needs `c̄ < max_k φ(k)`, which the
book does not state; for `c̄` above the maximum there is no steady state
(`warmglow_no_steady_state`). Footnote 15 (welfare with warm glow) is not formalised.
-/

namespace AKMM.Welfare

open Filter Topology Miao.OverlappingGenerations

/-- **AKMM, p. 183: the consumption choice.** With `u` concave on `(0, ∞)`, `c̄ > 0` and
`u′(c̄) = A`, consumption `c̄` maximises `u(c) + A(W − c)` (bequest `b′ = W − c`). -/
theorem warmglow_consumption {u : ℝ → ℝ} {A W cbar : ℝ} (hu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hc : 0 < cbar) (hd : HasDerivAt u A cbar) :
    ∀ c, 0 < c → u c + A * (W - c) ≤ u cbar + A * (W - cbar) := by
  intro c hc'
  have := op_concave_tangent hu (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') hd
  linarith

/-- **AKMM, p. 183: the law of motion.** With `F(k, 1) = rk + w` (factor payments exhaust
output) and `b = k`, the bequest rule `b′ = (1 + r − δ)b + w − c̄` is
`k′ = (1 − δ)k + F(k, 1) − c̄`. -/
theorem warmglow_law_of_motion {r w δ k cbar Fk : ℝ} (hF : Fk = r * k + w) :
    (1 + r - δ) * k + w - cbar = (1 - δ) * k + Fk - cbar := by
  rw [hF]; ring

/-- AKMM, p. 183: `k` is a steady state of `k′ = (1 − δ)k + F(k, 1) − c̄` iff
`φ(k) = F(k, 1) − δk = c̄`. -/
theorem warmglow_steady_iff {δ k cbar Fk : ℝ} :
    (1 - δ) * k + Fk - cbar = k ↔ Fk - δ * k = cbar := by
  constructor <;> intro h <;> linarith

/-- The shape of `φ` around two roots `k₁ < k₂` of `φ = c̄` (strict concavity on `[0, ∞)`):
`φ > c̄` strictly between them, `φ < c̄` on `[0, k₁)` and on `(k₂, ∞)`. -/
theorem warmglow_sign {φ : ℝ → ℝ} {cbar k1 k2 : ℝ} (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ)
    (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hr1 : φ k1 = cbar) (hr2 : φ k2 = cbar) :
    (∀ x, k1 < x → x < k2 → cbar < φ x) ∧ (∀ x, 0 ≤ x → x < k1 → φ x < cbar) ∧
      (∀ x, k2 < x → φ x < cbar) := by
  have m1 : k1 ∈ Set.Ici (0 : ℝ) := hk1
  have m2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  refine ⟨fun x hx1 hx2 => ?_, fun x hx0 hx1 => ?_, fun x hx => ?_⟩
  · set a := (k2 - x) / (k2 - k1) with ha
    have ha0 : 0 < a := div_pos (by linarith) (by linarith)
    have ha1 : 0 < 1 - a := by rw [ha, sub_pos, div_lt_one (by linarith)]; linarith
    have hne : k2 - k1 ≠ 0 := by linarith
    have hx : a * k1 + (1 - a) * k2 = x := by rw [ha]; field_simp; ring
    have := hφ.2 m1 m2 h12.ne ha0 ha1 (by ring)
    simp only [smul_eq_mul, hx, hr1, hr2] at this
    linarith
  · set a := (k2 - k1) / (k2 - x) with ha
    have ha0 : 0 < a := div_pos (by linarith) (by linarith)
    have ha1 : 0 < 1 - a := by rw [ha, sub_pos, div_lt_one (by linarith)]; linarith
    have hne : k2 - x ≠ 0 := by linarith
    have hx : a * x + (1 - a) * k2 = k1 := by rw [ha]; field_simp; ring
    have := hφ.2 (Set.mem_Ici.2 hx0) m2 (by linarith : x ≠ k2) ha0 ha1 (by ring)
    simp only [smul_eq_mul, hx, hr1, hr2] at this
    nlinarith
  · set a := (k2 - k1) / (x - k1) with ha
    have ha0 : 0 < a := div_pos (by linarith) (by linarith)
    have ha1 : 0 < 1 - a := by rw [ha, sub_pos, div_lt_one (by linarith)]; linarith
    have hne : x - k1 ≠ 0 := by linarith
    have hx' : (1 - a) * k1 + a * x = k2 := by rw [ha]; field_simp; ring
    have := hφ.2 m1 (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x)) (by linarith : k1 ≠ x) ha1 ha0
      (by ring)
    simp only [smul_eq_mul, hx', hr1, hr2] at this
    nlinarith

/-- **AKMM, p. 183: exactly two positive steady states** (under the condition the book omits).
Let `φ` be continuous and strictly concave on `[0, ∞)` with `φ(0) = 0`, `c̄ > 0`, `φ(k̂) > c̄` for
some `k̂ > 0` (so `c̄ < max φ`) and `φ(K) < c̄` for some `K > k̂`. Then there are `0 < k₁ < k₂` with
`φ(k₁) = φ(k₂) = c̄`, and every `k ≥ 0` with `φ(k) = c̄` is `k₁` or `k₂`. -/
theorem warmglow_two_steady_states {φ : ℝ → ℝ} {cbar khat K : ℝ}
    (hcont : ContinuousOn φ (Set.Ici 0)) (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (h0 : φ 0 = 0)
    (hc : 0 < cbar) (hkhat : 0 < khat) (hhat : cbar < φ khat) (hK : khat < K) (hKc : φ K < cbar) :
    ∃ k1 k2, 0 < k1 ∧ k1 < k2 ∧ φ k1 = cbar ∧ φ k2 = cbar ∧
      ∀ k, 0 ≤ k → φ k = cbar → k = k1 ∨ k = k2 := by
  obtain ⟨k1, hk1, hr1⟩ := intermediate_value_Ioo hkhat.le
    (hcont.mono fun x hx => Set.mem_Ici.2 hx.1) ⟨by rw [h0]; exact hc, hhat⟩
  obtain ⟨k2, hk2, hr2⟩ := intermediate_value_Ioo' hK.le
    (hcont.mono fun x hx => Set.mem_Ici.2 (hkhat.le.trans hx.1)) ⟨hKc, hhat⟩
  have h12 : k1 < k2 := hk1.2.trans hk2.1
  refine ⟨k1, k2, hk1.1, h12, hr1, hr2, fun k hk hrk => ?_⟩
  obtain ⟨hmid, hlow, hhigh⟩ := warmglow_sign hφ hk1.1.le h12 hr1 hr2
  rcases lt_trichotomy k k1 with h | h | h
  · exact absurd hrk (hlow k hk h).ne
  · exact Or.inl h
  · rcases lt_trichotomy k k2 with h' | h' | h'
    · exact absurd hrk (hmid k h h').ne'
    · exact Or.inr h'
    · exact absurd hrk (hhigh k h').ne

/-- **AKMM, p. 183: the slopes at the steady states.** If `φ` has derivative `φ′(kᵢ)` at the
roots `k₁ < k₂`, then `g′(k₂) = 1 + φ′(k₂) < 1` and `g′(k₁) = 1 + φ′(k₁) > 1`, where
`g(k) = (1 − δ)k + F(k, 1) − c̄` and `1 + φ′ = 1 + F₁ − δ`. -/
theorem warmglow_slopes {φ : ℝ → ℝ} {cbar k1 k2 d1 d2 : ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hr1 : φ k1 = cbar)
    (hr2 : φ k2 = cbar) (hd1 : HasDerivAt φ d1 k1) (hd2 : HasDerivAt φ d2 k2) :
    1 + d2 < 1 ∧ 1 < 1 + d1 := by
  have m1 : k1 ∈ Set.Ici (0 : ℝ) := hk1
  have m2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  have t2 := op_strictConcave_tangent hφ m2 m1 h12.ne hd2
  have t1 := op_strictConcave_tangent hφ m1 m2 h12.ne' hd1
  rw [hr1, hr2] at t1 t2
  constructor <;> nlinarith

/-- **AKMM, p. 183: the upper steady state is stable.** Let `g(k) = k + φ(k) − c̄` be continuous
and monotone on `[0, ∞)`, with roots `k₁ < k₂` of `φ = c̄` as in `warmglow_sign`. Every path
`k_{t+1} = g(kₜ)` from `k₀ > k₁` converges to `k₂`. -/
theorem warmglow_stable {φ : ℝ → ℝ} {cbar k1 k2 : ℝ} {k : ℕ → ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ)
    (hgc : ContinuousOn (fun x => x + φ x - cbar) (Set.Ici 0))
    (hgm : MonotoneOn (fun x => x + φ x - cbar) (Set.Ici 0)) (hk1 : 0 ≤ k1) (h12 : k1 < k2)
    (hr1 : φ k1 = cbar) (hr2 : φ k2 = cbar) (hpath : ∀ t, k (t + 1) = k t + φ (k t) - cbar)
    (hk0 : k1 < k 0) : Tendsto k atTop (𝓝 k2) := by
  obtain ⟨hmid, -, hhigh⟩ := warmglow_sign hφ hk1 h12 hr1 hr2
  set g := fun x => x + φ x - cbar with hg
  have hg2 : g k2 = k2 := by simp [hg, hr2]
  have hm2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  -- the limit of a convergent path in `[k₁, ∞)` is a fixed point
  have hfix : ∀ L, k1 < L → Tendsto k atTop (𝓝 L) → L = k2 := by
    intro L hL hlim
    have hL0 : L ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
    have h1 : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hlim.comp (tendsto_add_atTop_nat 1)
    have hev : ∀ᶠ t in atTop, k t ∈ Set.Ici (0 : ℝ) :=
      hlim.eventually (Ici_mem_nhds (by linarith : (0 : ℝ) < L) |> fun h =>
        Filter.mem_of_superset (Ioi_mem_nhds (by linarith : (0 : ℝ) < L))
          fun x hx => Set.mem_Ici.2 (le_of_lt hx))
    have h2 : Tendsto (fun t => g (k t)) atTop (𝓝 (g L)) :=
      ((hgc L hL0).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨hlim, hev⟩)
    have h3 : (fun t => k (t + 1)) = fun t => g (k t) := funext hpath
    rw [h3] at h1
    have hgL : g L = L := tendsto_nhds_unique h2 h1
    simp only [hg] at hgL
    have hφL : φ L = cbar := by linarith
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · linarith [hmid L hL h]
    · linarith [hhigh L h]
  rcases le_or_gt (k 0) k2 with hlo | hhi
  · -- increasing and bounded by `k₂`
    have hin : ∀ t, k1 < k t ∧ k t ≤ k2 := by
      intro t
      induction t with
      | zero => exact ⟨hk0, hlo⟩
      | succ t ih =>
        have hm : k t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [ih.1])
        have hup : g (k t) ≤ g k2 := hgm hm hm2 ih.2
        have hφt : cbar ≤ φ (k t) := by
          rcases ih.2.lt_or_eq with h | h
          · exact (hmid _ ih.1 h).le
          · rw [h, hr2]
        rw [hpath t]
        refine ⟨by linarith [ih.1], ?_⟩
        simp only [hg] at hup
        linarith
    have hmono : Monotone k := monotone_nat_of_le_succ fun t => by
      have := hin t
      have hφt : cbar ≤ φ (k t) := by
        rcases this.2.lt_or_eq with h | h
        · exact (hmid _ this.1 h).le
        · rw [h, hr2]
      rw [hpath t]; linarith
    have hbdd : BddAbove (Set.range k) := ⟨k2, by rintro _ ⟨t, rfl⟩; exact (hin t).2⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hL : k1 < ⨆ t, k t := lt_of_lt_of_le hk0 (le_ciSup hbdd 0)
    rw [hfix _ hL hlim] at hlim
    exact hlim
  · -- decreasing and bounded below by `k₂`
    have hin : ∀ t, k2 ≤ k t := by
      intro t
      induction t with
      | zero => exact hhi.le
      | succ t ih =>
        have hm : k t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
        have := hgm hm2 hm ih
        rw [hpath t]
        simp only [hg] at this
        linarith
    have hanti : Antitone k := antitone_nat_of_succ_le fun t => by
      have hφt : φ (k t) ≤ cbar := by
        rcases (hin t).lt_or_eq with h | h
        · exact (hhigh _ h).le
        · rw [← h, hr2]
      rw [hpath t]; linarith
    have hbdd : BddBelow (Set.range k) := ⟨k2, by rintro _ ⟨t, rfl⟩; exact hin t⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hL : k1 < ⨅ t, k t := lt_of_lt_of_le h12 (le_ciInf hin)
    rw [hfix _ hL hlim] at hlim
    exact hlim

/-- **AKMM, p. 183: the lower steady state is unstable from below.** If `0 ≤ k₀ < k₁` and the
path stays in `[0, ∞)`, it decreases: `kₜ ≤ k₀ < k₁` for all `t`, so it never approaches `k₁`. -/
theorem warmglow_lower_unstable {φ : ℝ → ℝ} {cbar k1 k2 : ℝ} {k : ℕ → ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hr1 : φ k1 = cbar)
    (hr2 : φ k2 = cbar) (hpath : ∀ t, k (t + 1) = k t + φ (k t) - cbar)
    (hk0 : k 0 < k1) (hnn : ∀ t, 0 ≤ k t) : (∀ t, k t ≤ k 0) ∧ ¬ Tendsto k atTop (𝓝 k1) := by
  obtain ⟨-, hlow, -⟩ := warmglow_sign hφ hk1 h12 hr1 hr2
  have hdec : ∀ t, k t ≤ k 0 := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      rw [hpath t]
      linarith [hlow (k t) (hnn t) (by linarith)]
  refine ⟨hdec, fun hlim => ?_⟩
  have := le_of_tendsto' hlim hdec
  linarith

/-- **AKMM, p. 183: the upper steady state is dynamically inefficient.** With
`f(k) = F(k, 1) + (1 − δ)k = k + φ(k)` and `f′(k₂) = 1 + φ′(k₂) < 1` (`warmglow_slopes`), the
steady state `k₂` (consumption `c̄ ≥ 0`) is inefficient by Theorem .5(i). -/
theorem warmglow_inefficient {φ : ℝ → ℝ} {cbar k1 k2 d2 : ℝ}
    (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) (hk1 : 0 ≤ k1) (h12 : k1 < k2) (hc : 0 ≤ cbar)
    (hr1 : φ k1 = cbar) (hr2 : φ k2 = cbar) (hd2 : HasDerivAt φ d2 k2) :
    ¬ deEfficient (fun _ => fun x => x + φ x) (fun _ => k2) := by
  have m1 : k1 ∈ Set.Ici (0 : ℝ) := hk1
  have m2 : k2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  have t2 := op_strictConcave_tangent hφ m2 m1 h12.ne hd2
  rw [hr1, hr2] at t2
  have hneg : d2 < 0 := by nlinarith
  exact theorem_A5_inefficient (by linarith)
    (show 0 ≤ k2 + φ k2 - k2 by rw [hr2]; linarith) ((hasDerivAt_id k2).add hd2) (by linarith)

/-- **AKMM, p. 183: an instance.** With `F(k, 1) = 2√k`, `δ = 1/2` and `c̄ = 3/2`,
`φ(k) = 2√k − k/2` satisfies every hypothesis of `warmglow_two_steady_states` (with `k̂ = 4`,
`K = 16`), its steady states are `1` and `9`, and at `9` the slope is `1 + φ′(9) = 5/6 < 1`. -/
theorem warmglow_instance :
    ContinuousOn (fun k : ℝ => 2 * √k - k / 2) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k - k / 2) ∧
      (2 * √0 - 0 / 2 : ℝ) = 0 ∧ (3 / 2 : ℝ) < 2 * √4 - 4 / 2 ∧ 2 * √16 - 16 / 2 < (3 / 2 : ℝ) ∧
      (2 * √1 - 1 / 2 : ℝ) = 3 / 2 ∧ (2 * √9 - 9 / 2 : ℝ) = 3 / 2 ∧
      HasDerivAt (fun k : ℝ => 2 * √k - k / 2) (-1 / 6) 9 := by
  have e4 : √(4 : ℝ) = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e9 : √(9 : ℝ) = 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e16 : √(16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨(continuous_const.mul Real.continuous_sqrt).sub (continuous_id.div_const 2)
    |>.continuousOn, ?_, by simp, by rw [e4]; norm_num, by rw [e16]; norm_num,
    by simp; norm_num, by rw [e9]; norm_num, ?_⟩
  · have hsq := Real.strictConcaveOn_sqrt
    refine ⟨hsq.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := hsq.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
  · have h := ((Real.hasDerivAt_sqrt (by norm_num : (9 : ℝ) ≠ 0)).const_mul 2).sub
      ((hasDerivAt_id (9 : ℝ)).div_const 2)
    rw [e9] at h
    exact h.congr_deriv (by norm_num)

/-- **AKMM, p. 183 (correction): no steady state when `c̄` exceeds `max φ`.** In the instance,
`φ(k) = 2√k − k/2 ≤ 2` for all `k ≥ 0`, so with `c̄ = 3` there is no steady state. -/
theorem warmglow_no_steady_state : ∀ k : ℝ, 0 ≤ k → 2 * √k - k / 2 ≠ 3 := by
  intro k hk h
  have hs := Real.sq_sqrt hk
  nlinarith [sq_nonneg (√k - 2), Real.sqrt_nonneg k]

end AKMM.Welfare

set_option linter.style.longLine false
#print axioms AKMM.Welfare.fwValue
#print axioms AKMM.Welfare.fwStrict
#print axioms AKMM.Welfare.fwFeasible
#print axioms AKMM.Welfare.fwParetoOptimal
#print axioms AKMM.Welfare.fwLNS
#print axioms AKMM.Welfare.fwCompEqT
#print axioms AKMM.Welfare.fwCompEq
#print axioms AKMM.Welfare.fw_value_ge
#print axioms AKMM.Welfare.fw_value_gt
#print axioms AKMM.Welfare.fw_value_sum
#print axioms AKMM.Welfare.fwt_lump_sum
#print axioms AKMM.Welfare.theorem_6_1
#print axioms AKMM.Welfare.fw_price_nonneg
#print axioms AKMM.Welfare.fwBadPref
#print axioms AKMM.Welfare.theorem_6_1_counterexample
#print axioms AKMM.Welfare.theorem_6_1_instance
#print axioms AKMM.Welfare.tax_inelastic_labour
#print axioms AKMM.Welfare.tax_labour_wedge
#print axioms AKMM.Welfare.dyFeasible
#print axioms AKMM.Welfare.dyU
#print axioms AKMM.Welfare.dyParetoOptimal
#print axioms AKMM.Welfare.dyCompEq
#print axioms AKMM.Welfare.dy_value_summable
#print axioms AKMM.Welfare.dy_lns
#print axioms AKMM.Welfare.fwt_dynastic
#print axioms AKMM.Welfare.dyPlannerOptimal
#print axioms AKMM.Welfare.negishi_planner_pareto
#print axioms AKMM.Welfare.eq_6_2
#print axioms AKMM.Welfare.dy_planner_foc
#print axioms AKMM.Welfare.eq_6_3
#print axioms AKMM.Welfare.negishi_coincide
#print axioms AKMM.Welfare.negishi_psi_eq_p
#print axioms AKMM.Welfare.negishi_ce_solves_planner
#print axioms AKMM.Welfare.negishi_fwt
#print axioms AKMM.Welfare.ext_equilibrium_hours
#print axioms AKMM.Welfare.ext_equilibrium_hours_unique
#print axioms AKMM.Welfare.ext_planner_hours
#print axioms AKMM.Welfare.ext_not_optimal
#print axioms AKMM.Welfare.ext_overwork
#print axioms AKMM.Welfare.ext_fn7
#print axioms AKMM.Welfare.brEndow
#print axioms AKMM.Welfare.brCons
#print axioms AKMM.Welfare.brEndow_spec
#print axioms AKMM.Welfare.brCons_spec
#print axioms AKMM.Welfare.borrow_endow_value
#print axioms AKMM.Welfare.borrow_unrestricted
#print axioms AKMM.Welfare.borrow_possibility_set
#print axioms AKMM.Welfare.borrow_possibility_set_printed_counterexample
#print axioms AKMM.Welfare.nbCons
#print axioms AKMM.Welfare.nbFeasible
#print axioms AKMM.Welfare.nbOptimal
#print axioms AKMM.Welfare.nbEquilibrium
#print axioms AKMM.Welfare.borrow_autarky
#print axioms AKMM.Welfare.borrow_euler_ineq
#print axioms AKMM.Welfare.borrow_autarky_optimal
#print axioms AKMM.Welfare.borrow_endow_log_summable
#print axioms AKMM.Welfare.borrow_equilibrium_iff
#print axioms AKMM.Welfare.borrow_interest_rate
#print axioms AKMM.Welfare.borrow_autarky_not_optimal
#print axioms AKMM.Welfare.ds_rpow_ratio
#print axioms AKMM.Welfare.eq_6_4
#print axioms AKMM.Welfare.ds_expenditure
#print axioms AKMM.Welfare.ds_price_index
#print axioms AKMM.Welfare.ds_demand
#print axioms AKMM.Welfare.ds_price_index_homogeneous
#print axioms AKMM.Welfare.dsProfit
#print axioms AKMM.Welfare.ds_revenue
#print axioms AKMM.Welfare.ds_firm_optimum
#print axioms AKMM.Welfare.ds_no_max_lt_one
#print axioms AKMM.Welfare.ds_no_max_eq_one
#print axioms AKMM.Welfare.ds_symmetric_wage
#print axioms AKMM.Welfare.ds_equilibrium_condition
#print axioms AKMM.Welfare.ds_rhs_strictMono
#print axioms AKMM.Welfare.ds_unique
#print axioms AKMM.Welfare.ds_planner_foc
#print axioms AKMM.Welfare.ds_underproduction
#print axioms AKMM.Welfare.welfare_cev_static
#print axioms AKMM.Welfare.welfare_cev_dynamic_log
#print axioms AKMM.Welfare.veil_equal_split
#print axioms AKMM.Welfare.veil_optimum_equal
#print axioms AKMM.Welfare.eq_6_5_6_6
#print axioms AKMM.Welfare.og_log_consumption
#print axioms AKMM.Welfare.og_log_equilibrium_iff
#print axioms AKMM.Welfare.ogFeasible
#print axioms AKMM.Welfare.ogDominates
#print axioms AKMM.Welfare.ogParetoOptimal
#print axioms AKMM.Welfare.ogLogU
#print axioms AKMM.Welfare.ogADEquilibrium
#print axioms AKMM.Welfare.og_ad_of_seq
#print axioms AKMM.Welfare.og_fwt_value
#print axioms AKMM.Welfare.og_fwt_finite_value
#print axioms AKMM.Welfare.og_logU_mono
#print axioms AKMM.Welfare.og_stationary_ad
#print axioms AKMM.Welfare.og_equal_endowments_optimal
#print axioms AKMM.Welfare.og_stationary_improvement
#print axioms AKMM.Welfare.og_seqPrice_const
#print axioms AKMM.Welfare.og_balasko_shell_stationary_log
#print axioms AKMM.Welfare.og_balasko_shell_sums
#print axioms AKMM.Welfare.og_example_3_1
#print axioms AKMM.Welfare.og_example_1_3
#print axioms AKMM.Welfare.og_example_2_2
#print axioms AKMM.Welfare.og_finite_transfers_hurt
#print axioms AKMM.Welfare.og_limit_rate_gt_one
#print axioms AKMM.Welfare.og_limit_rate_lt_one_log
#print axioms AKMM.Welfare.ogCexOld
#print axioms AKMM.Welfare.og_limit_rate_one_counterexample
#print axioms AKMM.Welfare.storage_saving
#print axioms AKMM.Welfare.storage_printed_counterexample
#print axioms AKMM.Welfare.stFeasible
#print axioms AKMM.Welfare.stParetoOptimal
#print axioms AKMM.Welfare.stEqAlloc
#print axioms AKMM.Welfare.stEqAlloc_feasible
#print axioms AKMM.Welfare.storage_not_optimal
#print axioms AKMM.Welfare.storage_optimal
#print axioms AKMM.Welfare.storage_optimal_iff
#print axioms AKMM.Welfare.diamond_law_of_motion
#print axioms AKMM.Welfare.theorem_6_2_prices
#print axioms AKMM.Welfare.dePath
#print axioms AKMM.Welfare.deCons
#print axioms AKMM.Welfare.deEfficient
#print axioms AKMM.Welfare.theorem_6_2_efficient
#print axioms AKMM.Welfare.theorem_6_2_inefficient
#print axioms AKMM.Welfare.theorem_6_2
#print axioms AKMM.Welfare.de_quadratic_expansion
#print axioms AKMM.Welfare.theorem_6_2_instance_efficient
#print axioms AKMM.Welfare.theorem_6_2_instance_inefficient
#print axioms AKMM.Welfare.theorem_A5_inefficient
#print axioms AKMM.Welfare.theorem_A5_efficient
#print axioms AKMM.Welfare.theorem_A5
#print axioms AKMM.Welfare.theorem_A5_cass
#print axioms AKMM.Welfare.appendix_6A_printed_f
#print axioms AKMM.Welfare.warmglow_consumption
#print axioms AKMM.Welfare.warmglow_law_of_motion
#print axioms AKMM.Welfare.warmglow_steady_iff
#print axioms AKMM.Welfare.warmglow_sign
#print axioms AKMM.Welfare.warmglow_two_steady_states
#print axioms AKMM.Welfare.warmglow_slopes
#print axioms AKMM.Welfare.warmglow_stable
#print axioms AKMM.Welfare.warmglow_lower_unstable
#print axioms AKMM.Welfare.warmglow_inefficient
#print axioms AKMM.Welfare.warmglow_instance
#print axioms AKMM.Welfare.warmglow_no_steady_state
