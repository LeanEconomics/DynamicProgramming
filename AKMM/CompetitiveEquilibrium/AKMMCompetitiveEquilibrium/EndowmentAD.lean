/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.ADConsumer
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Arrow–Debreu equilibrium of the endowment economy

AKMM, §5.2.1, pp. 132–135. Consumers `i` with endowments `y_{i,t}`, identical `u` and `β`,
trade all dated goods at date 0 at prices `pₜ` (`p₀ = 1`). The book's consumers form the
continuum `[0, 1]`; here they form any probability space `(I, μ)`, of which `[0, 1]` with
Lebesgue measure is an instance (`endow_unitInterval_probability`). Aggregates are integrals:
`Yₜ = ∫ y_{i,t} di`.

* Definition 1 (`IsADEquilibrium`) and Definition 2 (`IsADEquilibriumRep`).
* Log utility: `pₜ = βᵗY₀/Yₜ` (`endow_log_price`); identical consumption growth
  `c_{i,t+1}/c_{i,t} = Y_{t+1}/Yₜ = βpₜ/p_{t+1}` (`endow_log_growth`); perfect consumption
  smoothing when the aggregate endowment is constant (`endow_log_smoothing`);
  `c_{i,0} = (1 − β)Y₀ Σ βᵗy_{i,t}/Yₜ` and `c_{i,t} = θᵢYₜ` (`endow_log_shares`); the
  representative consumer (`endow_log_representative`).
* Existence: the log economy has the equilibrium `pₜ = βᵗY₀/Yₜ`, `c_{i,t} = θᵢYₜ`
  (`endow_log_existence`, with a concrete instance `endow_log_existence_instance`); with
  `endow_log_price` and `endow_log_shares` it is the only one.
* CRRA utility (`σ > 0`): every consumer's consumption grows with the aggregate
  (`endow_crra_common_growth`), the gross growth rate is `(βpₜ/p_{t+1})^{1/σ}`
  (`endow_crra_growth`) and `pₜ = βᵗ(Y₀/Yₜ)^σ` (`endow_crra_price`).
* Definition 2 as a special case: with strictly concave CRRA utility and identical endowments
  every consumer consumes the endowment (`definition_2_of_identical`).

Departures: consumers form a probability space rather than `[0, 1]`; the budget series and the
utility series are required to converge (fn. 2 of the book omits this on purpose).
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology StokeyLucasPrescott.EquilibriumApplications

variable {I : Type*} [MeasurableSpace I]

/-- The book's continuum of consumers `[0, 1]` with Lebesgue measure is a probability space, an
instance of the setting of this module. -/
theorem endow_unitInterval_probability :
    IsProbabilityMeasure (volume : Measure unitInterval) := inferInstance

/-- **AKMM, Definition 1, p. 132.** An Arrow–Debreu equilibrium of the endowment economy:
each `cᵢ` solves the date-0 problem at prices `p` with wealth `Σ pₜy_{i,t}` (a convergent
series), and `∫ c_{i,t} di = ∫ y_{i,t} di` for each `t`. -/
def IsADEquilibrium (μ : Measure I) (u : ℝ → ℝ) (β : ℝ) (y c : I → ℕ → ℝ) (p : ℕ → ℝ) :
    Prop :=
  (∀ i, Summable (fun t => p t * y i t)) ∧
    (∀ i, ADOptimal u β p (∑' t, p t * y i t) (c i)) ∧
    ∀ t, ∫ i, c i t ∂μ = ∫ i, y i t ∂μ

/-- **AKMM, Definition 2, p. 135.** The representative-consumer Arrow–Debreu equilibrium: `c`
solves the date-0 problem at prices `p` with wealth `Σ pₜyₜ`, and `cₜ = yₜ`. -/
def IsADEquilibriumRep (u : ℝ → ℝ) (β : ℝ) (y c p : ℕ → ℝ) : Prop :=
  Summable (fun t => p t * y t) ∧ ADOptimal u β p (∑' t, p t * y t) c ∧ ∀ t, c t = y t

/-- The log first-order condition: with `p₀ = 1`, `pₜc_{i,t} = βᵗc_{i,0}` at an optimum. -/
theorem endow_log_foc {β : ℝ} {p : ℕ → ℝ} {W : ℝ} {c : ℕ → ℝ}
    (hopt : ADOptimal Real.log β p W c) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1) (t : ℕ) :
    p t * c t = β ^ t * c 0 := by
  have hc := hopt.1.1
  have h := eq_5_3 hopt hp hp0 (du := fun t => (c t)⁻¹)
    (fun t => Real.hasDerivAt_log (hc t).ne') (inv_ne_zero (hc 0).ne') t
  rw [h]
  have := (hc t).ne'
  have := (hc 0).ne'
  field_simp

/-- **AKMM, p. 133: log prices.** In an equilibrium of the log economy with positive prices,
`p₀ = 1` and `Yₜ = ∫ y_{i,t} di > 0`, the price is `pₜ = βᵗY₀/Yₜ`. -/
theorem endow_log_price {μ : Measure I} {β : ℝ} {y c : I → ℕ → ℝ} {p Y : ℕ → ℝ}
    (he : IsADEquilibrium μ Real.log β y c p) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1)
    (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t) (t : ℕ) :
    p t = β ^ t * Y 0 / Y t := by
  obtain ⟨_, hopt, hclear⟩ := he
  have h : (fun i => p t * c i t) = fun i => β ^ t * c i 0 := by
    funext i; exact endow_log_foc (hopt i) hp hp0 t
  have hi := congrArg (fun f => ∫ i, f i ∂μ) h
  simp only [integral_const_mul, hclear, ← hYdef] at hi
  have := (hY t).ne'
  field_simp
  linarith

/-- **AKMM, p. 133: identical consumption growth.** In the log economy every consumer's
consumption grows at the rate of the aggregate endowment:
`c_{i,t+1}/c_{i,t} = Y_{t+1}/Yₜ = βpₜ/p_{t+1}`. -/
theorem endow_log_growth {μ : Measure I} {β : ℝ} {y c : I → ℕ → ℝ} {p Y : ℕ → ℝ}
    (he : IsADEquilibrium μ Real.log β y c p) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1)
    (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t) (i : I) (t : ℕ) :
    c i (t + 1) / c i t = Y (t + 1) / Y t ∧ c i (t + 1) / c i t = β * p t / p (t + 1) := by
  have hc := (he.2.1 i).1.1
  have h1 := endow_log_foc (he.2.1 i) hp hp0 t
  have h2 := endow_log_foc (he.2.1 i) hp hp0 (t + 1)
  have hpt := endow_log_price he hp hp0 hYdef hY t
  have hpt1 := endow_log_price he hp hp0 hYdef hY (t + 1)
  have := (hc t).ne'
  have := (hp t).ne'
  have := (hp (t + 1)).ne'
  have := (hY t).ne'
  have := (hY (t + 1)).ne'
  have := (hY 0).ne'
  have hc0 := (hc 0).ne'
  have hβ : β ≠ 0 := by
    intro hb; rw [hb, zero_pow (Nat.succ_ne_zero t), zero_mul] at h2
    exact (mul_pos (hp (t + 1)) (hc (t + 1))).ne' h2
  have hq : c i (t + 1) / c i t = β * p t / p (t + 1) := by
    rw [div_eq_div_iff (hc t).ne' (hp (t + 1)).ne']
    have e1 : c i (t + 1) = β ^ (t + 1) * c i 0 / p (t + 1) := by
      field_simp; linarith
    have e2 : c i t = β ^ t * c i 0 / p t := by field_simp; linarith
    rw [e1, e2]; field_simp; ring
  refine ⟨?_, hq⟩
  rw [hq, hpt, hpt1]
  field_simp
  ring

/-- **AKMM, p. 134: perfect consumption smoothing.** If the aggregate endowment is constant,
every consumer's consumption is constant, whatever the individual endowments. -/
theorem endow_log_smoothing {μ : Measure I} {β : ℝ} {y c : I → ℕ → ℝ} {p Y : ℕ → ℝ}
    (he : IsADEquilibrium μ Real.log β y c p) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1)
    (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t) (hconst : ∀ t, Y t = Y 0) (i : I)
    (t : ℕ) : c i t = c i 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h := (endow_log_growth he hp hp0 hYdef hY i t).1
    rw [hconst (t + 1), hconst t, div_self (hY 0).ne'] at h
    have := ((he.2.1 i).1.1 t).ne'
    rw [div_eq_one_iff_eq this] at h
    rw [h, ih]

/-- The consumption share of AKMM, p. 134: `θᵢ = (1 − β) Σ βᵗ y_{i,t}/Yₜ`. -/
noncomputable def endowShare (β : ℝ) (y : ℕ → ℝ) (Y : ℕ → ℝ) : ℝ :=
  (1 - β) * ∑' t, β ^ t * y t / Y t

/-- **AKMM, p. 134: consumption levels and shares.** In the log economy with `0 ≤ β < 1`,
`c_{i,0} = (1 − β)Y₀ Σ βᵗy_{i,t}/Yₜ`, and `c_{i,t} = θᵢYₜ` with
`θᵢ = (1 − β) Σ βᵗy_{i,t}/Yₜ`. -/
theorem endow_log_shares {μ : Measure I} {β : ℝ} {y c : I → ℕ → ℝ} {p Y : ℕ → ℝ}
    (he : IsADEquilibrium μ Real.log β y c p) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1)
    (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (i : I) :
    c i 0 = (1 - β) * Y 0 * ∑' t, β ^ t * y i t / Y t ∧
      ∀ t, c i t = endowShare β (y i) Y * Y t := by
  have hpr := endow_log_price he hp hp0 hYdef hY
  obtain ⟨_, hopt, _⟩ := he
  obtain ⟨⟨hc, _, hW⟩, _, _⟩ := hopt i
  have hfoc := endow_log_foc (hopt i) hp hp0
  have hLHS : ∑' t, p t * c i t = c i 0 * (1 - β)⁻¹ := by
    simp only [hfoc]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, mul_comm]
  have hRHS : ∑' t, p t * y i t = Y 0 * ∑' t, β ^ t * y i t / Y t := by
    rw [← tsum_mul_left]
    congr 1; funext t
    rw [hpr t]; ring
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hc0 : c i 0 = (1 - β) * Y 0 * ∑' t, β ^ t * y i t / Y t := by
    have := hLHS.symm.trans (hW.trans hRHS)
    field_simp at this
    linarith
  refine ⟨hc0, fun t => ?_⟩
  have hct : c i t = β ^ t * c i 0 / p t := by
    have := hfoc t; have := (hp t).ne'; field_simp; linarith
  rw [hct, hpr t, hc0]
  unfold endowShare
  have := (hY t).ne'
  have := (hY 0).ne'
  have hβt : β ^ t ≠ 0 ∨ β ^ t = 0 := (em _).symm.elim (fun h => Or.inr (not_not.1 h)) Or.inl
  rcases hβt with hb | hb
  · field_simp
  · have : p t = 0 := by rw [hpr t, hb]; ring
    exact absurd this (hp t).ne'

/-- **AKMM, p. 134: the representative consumer.** If every consumer's endowment equals the
aggregate, `y_{i,t} = Yₜ`, then `θᵢ = 1`: each consumes the own endowment. -/
theorem endow_log_representative {μ : Measure I} {β : ℝ} {y c : I → ℕ → ℝ} {p Y : ℕ → ℝ}
    (he : IsADEquilibrium μ Real.log β y c p) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1)
    (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hid : ∀ i t, y i t = Y t) (i : I) (t : ℕ) : c i t = y i t := by
  rw [(endow_log_shares he hp hp0 hYdef hY hβ0 hβ1 i).2 t, hid i t]
  unfold endowShare
  have h : ∀ s, β ^ s * y i s / Y s = β ^ s := fun s => by
    rw [hid i s, mul_div_assoc, div_self (hY s).ne', mul_one]
  simp only [h, tsum_geometric_of_lt_one hβ0 hβ1]
  have : (1 : ℝ) - β ≠ 0 := by linarith
  field_simp

/-- **AKMM, p. 134: existence in the log economy.** Let `0 < β < 1`, endowments be
nonnegative and integrable in `i` with `Yₜ = ∫ y_{i,t} di > 0`, each consumer have some
positive endowment, `Σ βᵗy_{i,t}/Yₜ` converge for each `i` and `Σ βᵗ log Yₜ` converge. Then
`pₜ = βᵗY₀/Yₜ` and `c_{i,t} = θᵢYₜ`, `θᵢ = (1 − β)Σ βᵗy_{i,t}/Yₜ`, form an Arrow–Debreu
equilibrium. With `endow_log_price` and `endow_log_shares` it is the only one. -/
theorem endow_log_existence {μ : Measure I} [IsProbabilityMeasure μ] {β : ℝ} {y : I → ℕ → ℝ}
    {Y : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy0 : ∀ i t, 0 ≤ y i t)
    (hyint : ∀ t, Integrable (y · t) μ) (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t)
    (hpos : ∀ i, ∃ t, 0 < y i t) (hsum : ∀ i, Summable (fun t => β ^ t * y i t / Y t))
    (hlog : Summable (fun t => β ^ t * Real.log (Y t))) :
    IsADEquilibrium μ Real.log β y (fun i t => endowShare β (y i) Y * Y t)
      (fun t => β ^ t * Y 0 / Y t) := by
  set θ : I → ℝ := fun i => endowShare β (y i) Y with hθ
  have hθpos : ∀ i, 0 < θ i := by
    intro i
    obtain ⟨t, ht⟩ := hpos i
    have : 0 < ∑' s, β ^ s * y i s / Y s :=
      (hsum i).tsum_pos (fun s => div_nonneg (mul_nonneg (pow_nonneg hβ0.le s) (hy0 i s))
        (hY s).le) t (div_pos (mul_pos (pow_pos hβ0 t) ht) (hY t))
    exact mul_pos (by linarith) this
  have hβ1' : (1 : ℝ) - β ≠ 0 := by linarith
  have hpy : ∀ i, (fun t => β ^ t * Y 0 / Y t * y i t) =
      fun t => Y 0 * (β ^ t * y i t / Y t) := fun i => by funext t; ring
  refine ⟨fun i => ?_, fun i => ?_, fun t => ?_⟩
  · rw [hpy i]; exact (hsum i).mul_left _
  · -- each consumer's plan satisfies the sufficient first-order conditions
    have hc : ∀ t, 0 < θ i * Y t := fun t => mul_pos (hθpos i) (hY t)
    refine ad_foc_sufficient (du := fun t => (θ i * Y t)⁻¹) (lam := (θ i * Y 0)⁻¹) hβ0.le
      (fun t x hx => ce_log_tangent (hc t) hx) (fun t => ?_) ⟨hc, ?_, ?_⟩ ?_
    · have := (hY t).ne'; have := (hY 0).ne'; have := (hθpos i).ne'
      field_simp
    · have e : (fun t => β ^ t * Y 0 / Y t * (θ i * Y t)) = fun t => θ i * Y 0 * β ^ t := by
        funext t; have := (hY t).ne'; field_simp
      rw [e]; exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_left _
    · have e : (fun t => β ^ t * Y 0 / Y t * (θ i * Y t)) = fun t => θ i * Y 0 * β ^ t := by
        funext t; have := (hY t).ne'; field_simp
      rw [e, hpy i, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hβ0.le hβ1]
      simp only [hθ, endowShare]
      field_simp
    · have e : (fun t => β ^ t * Real.log (θ i * Y t)) =
          fun t => Real.log (θ i) * β ^ t + β ^ t * Real.log (Y t) := by
        funext t; rw [Real.log_mul (hθpos i).ne' (hY t).ne']; ring
      rw [e]
      exact ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left _).add hlog
  · -- market clearing: `∫ θᵢ di = 1`
    have hint : ∫ i, θ i ∂μ = 1 := by
      have hF : ∀ s, Integrable (fun i => β ^ s * y i s / Y s) μ := fun s =>
        ((hyint s).const_mul (β ^ s)).div_const (Y s)
      have hnorm : ∀ s, ∫ i, ‖β ^ s * y i s / Y s‖ ∂μ = β ^ s := by
        intro s
        have : ∀ i, ‖β ^ s * y i s / Y s‖ = β ^ s * y i s / Y s := fun i =>
          Real.norm_of_nonneg (div_nonneg (mul_nonneg (pow_nonneg hβ0.le s) (hy0 i s))
            (hY s).le)
        simp only [this]
        rw [integral_div, integral_const_mul, ← hYdef]
        have := (hY s).ne'
        field_simp
      have hS : Summable fun s => ∫ i, ‖β ^ s * y i s / Y s‖ ∂μ := by
        simp only [hnorm]; exact summable_geometric_of_lt_one hβ0.le hβ1
      have key := integral_tsum_of_summable_integral_norm hF hS
      have hval : ∀ s, ∫ i, β ^ s * y i s / Y s ∂μ = β ^ s := by
        intro s
        rw [integral_div, integral_const_mul, ← hYdef]
        have := (hY s).ne'
        field_simp
      simp only [hval, tsum_geometric_of_lt_one hβ0.le hβ1] at key
      simp only [hθ, endowShare]
      rw [integral_const_mul, ← key]
      field_simp
    simp only
    rw [integral_mul_const, hint, one_mul, hYdef]

/-- **AKMM, p. 134: an instance.** On `[0, 1]` with Lebesgue measure, unit endowments and
`β = 1/2`, prices `pₜ = (1/2)ᵗ` and consumption `θᵢYₜ` form an equilibrium of the log economy. -/
theorem endow_log_existence_instance :
    IsADEquilibrium (volume : Measure unitInterval) Real.log (1 / 2) (fun _ _ => 1)
      (fun i _ => endowShare (1 / 2) ((fun (_ : unitInterval) (_ : ℕ) => (1 : ℝ)) i)
        (fun _ => 1) * 1) (fun t => (1 / 2 : ℝ) ^ t * 1 / 1) :=
  endow_log_existence (by norm_num) (by norm_num) (fun _ _ => zero_le_one)
    (fun _ => integrable_const _) (fun _ => by simp) (fun _ => one_pos) (fun _ => ⟨0, one_pos⟩)
    (fun _ => (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).congr fun t => by simp) (by simp)

/-- **AKMM, p. 134: CRRA consumption moves with the aggregate.** With `u = sgCRRA σ`
(`(c^{1−σ} − 1)/(1 − σ)`, log at `σ = 1`), `σ > 0`, positive prices and `p₀ = 1`, every
consumer's consumption satisfies `c_{i,t} = (pₜ/βᵗ)^{−1/σ} c_{i,0}`; the factor is common to all
consumers. -/
theorem endow_crra_common_growth {σ β : ℝ} {p : ℕ → ℝ} {W : ℝ} {c : ℕ → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hopt : ADOptimal (sgCRRA σ) β p W c) (hp : ∀ t, 0 < p t)
    (hp0 : p 0 = 1) (t : ℕ) : c t = (p t / β ^ t) ^ (-σ⁻¹) * c 0 := by
  have hc := hopt.1.1
  have h := eq_5_3 hopt hp hp0 (du := fun t => (c t) ^ (-σ)) (fun t => sgCRRA_hasDerivAt (hc t))
    (Real.rpow_pos_of_pos (hc 0) _).ne' t
  have hz : p t / β ^ t = c t ^ (-σ) / c 0 ^ (-σ) := by
    rw [h]; have := (pow_pos hβ t).ne'; field_simp
  rw [hz, Real.div_rpow (Real.rpow_nonneg (hc t).le _) (Real.rpow_nonneg (hc 0).le _),
    ← Real.rpow_mul (hc t).le, ← Real.rpow_mul (hc 0).le]
  have : -σ * -σ⁻¹ = 1 := by field_simp
  rw [this, Real.rpow_one, Real.rpow_one]
  have := (hc 0).ne'
  field_simp

/-- **AKMM, p. 134: CRRA prices.** In an equilibrium with `u = sgCRRA σ`, `σ > 0`, positive
prices, `p₀ = 1` and `Yₜ > 0`, the price is `pₜ = βᵗ(Y₀/Yₜ)^σ`. -/
theorem endow_crra_price {μ : Measure I} {σ β : ℝ} {y c : I → ℕ → ℝ} {p Y : ℕ → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (he : IsADEquilibrium μ (sgCRRA σ) β y c p) (hp : ∀ t, 0 < p t)
    (hp0 : p 0 = 1) (hYdef : ∀ t, Y t = ∫ i, y i t ∂μ) (hY : ∀ t, 0 < Y t) (t : ℕ) :
    p t = β ^ t * (Y 0 / Y t) ^ σ := by
  obtain ⟨_, hopt, hclear⟩ := he
  set z := p t / β ^ t with hz
  have hzpos : 0 < z := div_pos (hp t) (pow_pos hβ t)
  have h : (fun i => c i t) = fun i => z ^ (-σ⁻¹) * c i 0 := by
    funext i; exact endow_crra_common_growth hσ hβ (hopt i) hp hp0 t
  have hi := congrArg (fun f => ∫ i, f i ∂μ) h
  simp only [integral_const_mul, hclear, ← hYdef] at hi
  -- `Yₜ = z^{−1/σ} Y₀`, so `z = (Y₀/Yₜ)^σ`
  have hzr : z ^ (-σ⁻¹) = Y t / Y 0 := by
    rw [eq_div_iff (hY 0).ne', ← hi]
  have hzv : z = (Y 0 / Y t) ^ σ := by
    have e : z = (z ^ (-σ⁻¹)) ^ (-σ) := by
      rw [← Real.rpow_mul hzpos.le]
      have : -σ⁻¹ * -σ = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [e, hzr, Real.rpow_neg (div_pos (hY t) (hY 0)).le,
      ← Real.inv_rpow (div_pos (hY t) (hY 0)).le, inv_div]
  have : p t = β ^ t * z := by rw [hz]; have := (pow_pos hβ t).ne'; field_simp
  rw [this, hzv]

/-- **AKMM, p. 134: the CRRA growth rate.** Every consumer's gross consumption growth equals
`(βpₜ/p_{t+1})^{1/σ}`. -/
theorem endow_crra_growth {σ β : ℝ} {p : ℕ → ℝ} {W : ℝ} {c : ℕ → ℝ}
    (hσ : 0 < σ) (hβ : 0 < β) (hopt : ADOptimal (sgCRRA σ) β p W c) (hp : ∀ t, 0 < p t)
    (hp0 : p 0 = 1) (t : ℕ) : c (t + 1) / c t = (β * p t / p (t + 1)) ^ σ⁻¹ := by
  have h1 := endow_crra_common_growth hσ hβ hopt hp hp0 t
  have h2 := endow_crra_common_growth hσ hβ hopt hp hp0 (t + 1)
  have hc0 := hopt.1.1 0
  have ha : 0 < p t / β ^ t := div_pos (hp t) (pow_pos hβ t)
  have hb : 0 < p (t + 1) / β ^ (t + 1) := div_pos (hp (t + 1)) (pow_pos hβ (t + 1))
  rw [h1, h2, mul_div_mul_right _ _ hc0.ne', ← Real.div_rpow hb.le ha.le, Real.rpow_neg
    (div_pos hb ha).le, ← Real.inv_rpow (div_pos hb ha).le, inv_div]
  congr 1
  have := (hp (t + 1)).ne'
  have := (pow_pos hβ t).ne'
  field_simp
  ring

/-- **AKMM, p. 135: Definition 2 as a special case of Definition 1.** With CRRA utility
(`σ > 0`), positive prices, `p₀ = 1`, `β > 0` and identical endowments `y_{i,t} = yₜ > 0`, every
consumer consumes the endowment in an equilibrium, and each consumer's plan is a
representative-consumer equilibrium (Definition 2). -/
theorem definition_2_of_identical {μ : Measure I} [IsProbabilityMeasure μ] {σ β : ℝ}
    {y : ℕ → ℝ} {c : I → ℕ → ℝ} {p : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (he : IsADEquilibrium μ (sgCRRA σ) β (fun _ => y) c p) (hp : ∀ t, 0 < p t)
    (hp0 : p 0 = 1) (hy : ∀ t, 0 < y t) (i : I) :
    (∀ t, c i t = y t) ∧ IsADEquilibriumRep (sgCRRA σ) β y (c i) p := by
  have hpr := endow_crra_price hσ hβ he hp hp0 (Y := y) (fun t => by simp) hy
  have hct : ∀ t, c i t = y t / y 0 * c i 0 := by
    intro t
    rw [endow_crra_common_growth hσ hβ (he.2.1 i) hp hp0 t]
    congr 1
    have hz : p t / β ^ t = (y 0 / y t) ^ σ := by
      rw [hpr t]
      have := (pow_pos hβ t).ne'; field_simp
    rw [hz, ← Real.rpow_mul (div_pos (hy 0) (hy t)).le]
    have : σ * -σ⁻¹ = -1 := by field_simp
    rw [this, Real.rpow_neg_one, inv_div]
  -- the budget pins `c_{i,0} = y₀`
  obtain ⟨hsy, hopt, _⟩ := he
  obtain ⟨⟨hc, hcs, hW⟩, _, _⟩ := hopt i
  have hcs' : (fun t => p t * c i t) = fun t => c i 0 / y 0 * (p t * y t) := by
    funext t; rw [hct t]; ring
  have hPV : 0 < ∑' t, p t * y t :=
    (hsy i).tsum_pos (fun t => (mul_pos (hp t) (hy t)).le) 0 (mul_pos (hp 0) (hy 0))
  rw [hcs', tsum_mul_left] at hW
  have h0 : c i 0 = y 0 := by
    have h1 : c i 0 / y 0 = 1 := by
      have := hPV.ne'
      field_simp at hW ⊢
      linarith
    rwa [div_eq_one_iff_eq (hy 0).ne'] at h1
  have hall : ∀ t, c i t = y t := fun t => by
    rw [hct t, h0]; have := (hy 0).ne'; field_simp
  exact ⟨hall, hsy i, hopt i, hall⟩

end AKMM.CompetitiveEquilibrium
