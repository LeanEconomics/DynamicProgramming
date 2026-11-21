/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

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
