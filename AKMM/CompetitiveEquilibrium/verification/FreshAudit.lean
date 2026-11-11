import EquilibriumApplications.SustainedGrowthPrices
import EquilibriumApplications.GrowthCertaintyDDGrowthStability
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import OverlappingGenerations.OPExercises
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The date-0 consumer problem

AKMM, §5.2.1, pp. 132–133. The consumer chooses a sequence `c` to maximize `Σ βᵗu(cₜ)` subject
to the lifetime budget `Σ pₜcₜ = W`. The book derives the first-order conditions
`βᵗu′(c_{i,t}) = λᵢpₜ` from the Lagrangian and the price formula (5.3).

* A sequence that differs from a summable one at finitely many dates is summable, and its sum
  differs by the finite sum of the differences (`ce_tsum_perturb`); a finite perturbation that
  cannot raise the objective has zero derivative (`ce_foc_of_perturb`). Every first-order
  condition of the chapter is proved from optimality this way.
* **Necessity**: at an optimum with positive prices and consumption,
  `βˢu′(c_s)pₜ = βᵗu′(cₜ)p_s` for all dates (`ad_foc`), so there is one multiplier
  `λ = u′(c₀)/p₀` with `βᵗu′(cₜ) = λpₜ` (`ad_foc_multiplier`), and with `p₀ = 1` the price is
  `pₜ = βᵗu′(cₜ)/u′(c₀)` (`eq_5_3`).
* **Sufficiency**: if `u` lies below its tangents, a budget-feasible plan with `βᵗu′(cₜ) = λpₜ`
  is optimal (`ad_foc_sufficient`). The tangent inequality holds for the CRRA family `sgCRRA σ`
  of SLP `EquilibriumApplications` (`(c^{1−σ} − 1)/(1 − σ)`, `log c` at `σ = 1`), which is
  used for the book's power and log utilities.

Departures (fn. 2 of the book omits them on purpose): consumption is required to be positive,
the budget series must converge, and the plans compared are those whose utility series converges.
-/

namespace AKMM.CompetitiveEquilibrium

open Filter Topology StokeyLucasPrescott.EquilibriumApplications

/-- A sequence that agrees with a summable `f` outside a finite set `s` is summable, and
`Σ g = Σ f + Σ_{n ∈ s} (gₙ − fₙ)`. -/
theorem ce_tsum_perturb {f g : ℕ → ℝ} (s : Finset ℕ) (hfg : ∀ n ∉ s, g n = f n)
    (hf : Summable f) : Summable g ∧ ∑' n, g n = ∑' n, f n + ∑ n ∈ s, (g n - f n) := by
  have hd : ∀ n ∉ s, g n - f n = 0 := fun n hn => by rw [hfg n hn]; ring
  have hs : Summable (fun n => g n - f n) := summable_of_ne_finset_zero hd
  have hg : g = fun n => f n + (g n - f n) := by funext n; ring
  refine ⟨by rw [hg]; exact hf.add hs, ?_⟩
  conv_lhs => rw [hg]
  rw [hf.tsum_add hs, tsum_eq_sum hd]

/-- A first-order condition from a finite perturbation. Let `g ε` agree with a summable `f`
outside a finite set `s`, with `g 0 = f`, and suppose that for `ε` near `0` the perturbed
series is no larger than `f` whenever it is summable. If `ε ↦ Σ_{n ∈ s} g ε n` has derivative
`d` at `0`, then `d = 0`. -/
theorem ce_foc_of_perturb {f : ℕ → ℝ} {g : ℝ → ℕ → ℝ} (s : Finset ℕ) (hf : Summable f)
    (hs : ∀ ε, ∀ n ∉ s, g ε n = f n) (h0 : ∀ n, g 0 n = f n)
    (hle : ∀ᶠ ε in 𝓝 0, Summable (g ε) → ∑' n, g ε n ≤ ∑' n, f n) {d : ℝ}
    (hd : HasDerivAt (fun ε => ∑ n ∈ s, g ε n) d 0) : d = 0 := by
  have hmax : IsLocalMax (fun ε => ∑ n ∈ s, g ε n) 0 := by
    filter_upwards [hle] with ε hε
    obtain ⟨hsum, heq⟩ := ce_tsum_perturb s (hs ε) hf
    have h := hε hsum
    rw [heq, Finset.sum_sub_distrib] at h
    have hz : ∑ n ∈ s, f n = ∑ n ∈ s, g 0 n := Finset.sum_congr rfl fun n _ => (h0 n).symm
    linarith
  exact hmax.hasDerivAt_eq_zero hd

/-- The date-0 budget set (AKMM, (5.2), p. 132): positive consumption with a convergent value
`Σ pₜcₜ = W`. -/
def ADBudget (p : ℕ → ℝ) (W : ℝ) (c : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ Summable (fun t => p t * c t) ∧ ∑' t, p t * c t = W

/-- AKMM, Definition 1, part 1, p. 132: `c` solves `max Σ βᵗu(cₜ)` subject to `Σ pₜcₜ = W`,
among the budget-feasible plans whose utility series converges. -/
def ADOptimal (u : ℝ → ℝ) (β : ℝ) (p : ℕ → ℝ) (W : ℝ) (c : ℕ → ℝ) : Prop :=
  ADBudget p W c ∧ Summable (fun t => β ^ t * u (c t)) ∧
    ∀ x, ADBudget p W x → Summable (fun t => β ^ t * u (x t)) →
      ∑' t, β ^ t * u (x t) ≤ ∑' t, β ^ t * u (c t)

/-- **AKMM, p. 133: the first-order conditions of the date-0 problem.** At an optimum with
positive prices, if `u` has derivative `u′(cₜ)` at each `cₜ`, then
`βˢu′(c_s)pₜ = βᵗu′(cₜ)p_s` for all dates `s, t`. Proved by moving `ε` units of value between
dates `s` and `t`. -/
theorem ad_foc {u : ℝ → ℝ} {β : ℝ} {p : ℕ → ℝ} {W : ℝ} {c du : ℕ → ℝ}
    (hopt : ADOptimal u β p W c) (hp : ∀ t, 0 < p t) (hd : ∀ t, HasDerivAt u (du t) (c t))
    (s t : ℕ) : β ^ s * du s * p t = β ^ t * du t * p s := by
  rcases eq_or_ne s t with rfl | hst
  · ring
  obtain ⟨⟨hpos, hsum, hW⟩, husum, hmax⟩ := hopt
  set r := p s / p t with hr
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = s then c s + ε else if n = t then c t - r * ε else c n
  have hxs : ∀ ε, x ε s = c s + ε := fun ε => by simp [x]
  have hxt : ∀ ε, x ε t = c t - r * ε := fun ε => by simp [x, hst.symm]
  have hxo : ∀ ε, ∀ n ∉ ({s, t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hpt := hp t
  -- for small `ε` the perturbed plan is budget-feasible
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε ∧ 0 < c t - r * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos s)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - r * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * u (x ε n))
      (β ^ s * du s + β ^ t * (du t * (-r))) 0 := by
    have e : (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * u (x ε n)) =
        fun ε => β ^ s * u (c s + ε) + β ^ t * u (c t - r * ε) := by
      funext ε; rw [Finset.sum_pair hst, hxs, hxt]
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c s + ε)) (du s) 0 := by
      have hu : HasDerivAt u (du s) (c s + 0) := by simpa using hd s
      simpa using hu.comp_const_add (c s) 0
    have h2 : HasDerivAt (fun ε => u (c t - r * ε)) (du t * (-r)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - r * ε) (-r) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul r).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - r * 0) := by simpa using hd t
      exact hu.comp 0 hin
    exact (h1.const_mul _).add (h2.const_mul _)
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * u (c n))
    (g := fun ε n => β ^ n * u (x ε n)) {s, t} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      refine hmax (x ε) ⟨fun n => ?_, ?_⟩ hU
      · by_cases h1 : n = s
        · subst h1; rw [hxs]; exact hε.1
        by_cases h2 : n = t
        · subst h2; rw [hxt]; exact hε.2
        simp only [x, h1, h2, ite_false]; exact hpos n
      · obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun n => p n * c n)
          (g := fun n => p n * x ε n) {s, t} (fun n hn => by simp only [hxo ε n hn]) hsum
        refine ⟨hS, ?_⟩
        rw [hE, Finset.sum_pair hst, hxs, hxt, hr, ← hW]
        field_simp
        ring) hd'
  rw [hr] at hzero
  field_simp at hzero
  linarith

/-- AKMM, p. 133: there is one multiplier `λ = u′(c₀)/p₀` with `βᵗu′(cₜ) = λpₜ` for every
`t`; it does not depend on time. -/
theorem ad_foc_multiplier {u : ℝ → ℝ} {β : ℝ} {p : ℕ → ℝ} {W : ℝ} {c du : ℕ → ℝ}
    (hopt : ADOptimal u β p W c) (hp : ∀ t, 0 < p t) (hd : ∀ t, HasDerivAt u (du t) (c t))
    (t : ℕ) : β ^ t * du t = du 0 / p 0 * p t := by
  have h := ad_foc hopt hp hd 0 t
  have := (hp 0).ne'
  field_simp
  simp only [pow_zero, one_mul] at h
  linarith

/-- **AKMM, (5.3), p. 133.** With `p₀ = 1` and `u′(c₀) ≠ 0`, the price at an optimum is
`pₜ = βᵗu′(cₜ)/u′(c₀)`. -/
theorem eq_5_3 {u : ℝ → ℝ} {β : ℝ} {p : ℕ → ℝ} {W : ℝ} {c du : ℕ → ℝ}
    (hopt : ADOptimal u β p W c) (hp : ∀ t, 0 < p t) (hp0 : p 0 = 1)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (hd0 : du 0 ≠ 0) (t : ℕ) :
    p t = β ^ t * du t / du 0 := by
  have h := ad_foc_multiplier hopt hp hd t
  rw [hp0, div_one] at h
  field_simp
  linarith

/-- **AKMM, p. 133: the first-order conditions are sufficient.** If `u` lies below its tangent
at every `cₜ` on the positive reals, `c` is budget-feasible with a convergent utility series and
`βᵗu′(cₜ) = λpₜ` for some `λ` and all `t` (with `β ≥ 0`), then `c` solves the date-0 problem. -/
theorem ad_foc_sufficient {u : ℝ → ℝ} {β lam : ℝ} {p : ℕ → ℝ} {W : ℝ} {c du : ℕ → ℝ}
    (hβ : 0 ≤ β) (htan : ∀ t x, 0 < x → u x ≤ u (c t) + du t * (x - c t))
    (hfoc : ∀ t, β ^ t * du t = lam * p t) (hc : ADBudget p W c)
    (hU : Summable (fun t => β ^ t * u (c t))) : ADOptimal u β p W c := by
  refine ⟨hc, hU, fun x hx hUx => ?_⟩
  obtain ⟨hcpos, hcs, hcW⟩ := hc
  obtain ⟨hxpos, hxs, hxW⟩ := hx
  have hb : ∀ t, β ^ t * u (x t) ≤ β ^ t * u (c t) + lam * (p t * x t - p t * c t) := by
    intro t
    have h1 := mul_le_mul_of_nonneg_left (htan t (x t) (hxpos t)) (pow_nonneg hβ t)
    have h2 : β ^ t * (u (c t) + du t * (x t - c t)) =
        β ^ t * u (c t) + (β ^ t * du t) * (x t - c t) := by ring
    rw [h2, hfoc t] at h1
    linarith
  have hS : Summable (fun t => β ^ t * u (c t) + lam * (p t * x t - p t * c t)) :=
    hU.add ((hxs.sub hcs).mul_left lam)
  have := hUx.tsum_le_tsum hb hS
  rw [hU.tsum_add ((hxs.sub hcs).mul_left lam), tsum_mul_left, hxs.tsum_sub hcs, hxW, hcW]
    at this
  linarith

/-- The tangent inequality for the CRRA family: `u(x) ≤ u(c) + c^{−σ}(x − c)` for `x, c > 0`
(from SLP `EquilibriumApplications`). -/
theorem ce_crra_tangent {σ c x : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hx : 0 < x) :
    sgCRRA σ x ≤ sgCRRA σ c + c ^ (-σ) * (x - c) :=
  sgCRRA_tangent hσ hc hx

/-- The tangent inequality for log utility: `log x ≤ log c + (x − c)/c` for `x, c > 0`. -/
theorem ce_log_tangent {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.log x ≤ Real.log c + c⁻¹ * (x - c) := by
  have := ce_crra_tangent one_pos hc hx
  rwa [sgCRRA_one, sgCRRA_one, Real.rpow_neg_one] at this

end AKMM.CompetitiveEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Arrow–Debreu equilibrium of the production economy with labour

AKMM, §5.2.2, pp. 135–138. Households `i` with skills `eᵢ` choose consumption and hours to
maximize `Σ βᵗ[u(c_{i,t}) − v(ℓ_{i,t})]` (5.4) subject to `Σ pₜc_{i,t} = Σ pₜwₜeᵢℓ_{i,t}` (5.7);
a representative firm with `Yₜ = AₜLₜ` (5.5) maximizes `Σ pₜ(AₜLₜ − wₜLₜ)` (5.6).

* The firm (fn. 3 and p. 137): the problem (5.6) is a sequence of static problems
  (`eq_5_6_static`); `w = A` makes every scale optimal, `A > w` leaves no optimum, `A < w` makes
  `L = 0` the unique optimum (`labour_firm_fn3`); so positive employment forces `wₜ = Aₜ`
  (`labour_wage_eq_productivity`).
* The household: the first-order conditions (5.8)–(5.10) are necessary (`eq_5_8`, `eq_5_9`,
  `eq_5_10`) and, with `u` concave and `v` convex, sufficient (`labour_foc_sufficient`).
* Definition 3 (`IsADEquilibriumLabour`). Log utility: consumption is a constant share of
  output (`labour_log_shares`), the hours condition `v′(ℓ_{i,t})θᵢYₜ = eᵢAₜ`
  (`labour_log_hours`), and with `θᵢ = eᵢ` all households work the same hours
  (`labour_log_equal_hours`). The guess `θᵢ = eᵢ`, `ℓ_{i,t} = L` with `v′(L)L = 1` is an
  equilibrium (`labour_log_equilibrium`, instance `labour_log_equilibrium_instance`).
* The static examples: with `c = wℓ` and utility `log c − v(ℓ)` the chosen hours do not depend
  on `w` (`labour_static_wage_independent`); with asset income `c = eAℓ + a` the first-order
  condition is `v′(ℓ) = eA/(eAℓ + a)` (`labour_static_asset_foc`), not `aA/(eAℓ + a)` as printed
  (`labour_static_asset_printed_counterexample`), and more assets mean fewer hours
  (`labour_assets_lower_hours`).

Departures: consumption positive, hours nonnegative, convergent budget and utility series; the
book's printed numerator `aᵢA` on p. 138 is corrected to `eᵢA`.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-! ### The firm -/

/-- The firm's time-`t` profit `AL − wL`. -/
def labourProfit (A w L : ℝ) : ℝ := A * L - w * L

/-- `L` maximizes the static profit `AL − wL` over `L ≥ 0`. -/
def LabourStaticOpt (A w L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ L', 0 ≤ L' → labourProfit A w L' ≤ labourProfit A w L

/-- AKMM, (5.6), p. 136: `L` solves the firm's date-0 problem: nonnegative labour with a
convergent profit series that no other such plan beats. -/
def LabourFirmOpt (p A w L : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ L t) ∧ Summable (fun t => p t * labourProfit (A t) (w t) (L t)) ∧
    ∀ L' : ℕ → ℝ, (∀ t, 0 ≤ L' t) → Summable (fun t => p t * labourProfit (A t) (w t) (L' t)) →
      ∑' t, p t * labourProfit (A t) (w t) (L' t) ≤ ∑' t, p t * labourProfit (A t) (w t) (L t)

/-- **AKMM, p. 136: the firm's problem is a sequence of static problems.** With positive prices
and a convergent profit series, `L` solves (5.6) iff each `Lₜ` maximizes `AₜLₜ − wₜLₜ`. -/
theorem eq_5_6_static {p A w L : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hs : Summable (fun t => p t * labourProfit (A t) (w t) (L t))) :
    LabourFirmOpt p A w L ↔ ∀ t, LabourStaticOpt (A t) (w t) (L t) := by
  constructor
  · rintro ⟨hL, -, hmax⟩ t
    refine ⟨hL t, fun L' hL' => ?_⟩
    let M : ℕ → ℝ := fun n => if n = t then L' else L n
    have hMo : ∀ n ∉ ({t} : Finset ℕ), M n = L n := fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [M, hn]
    obtain ⟨hS, hE⟩ := ce_tsum_perturb (f := fun n => p n * labourProfit (A n) (w n) (L n))
      (g := fun n => p n * labourProfit (A n) (w n) (M n)) {t}
      (fun n hn => by simp only [hMo n hn]) hs
    have h := hmax M (fun n => by by_cases h : n = t <;> simp [M, h, hL', hL n]) hS
    rw [hE, Finset.sum_singleton] at h
    simp only [M, ite_true] at h
    have : p t * (labourProfit (A t) (w t) L' - labourProfit (A t) (w t) (L t)) ≤ 0 := by
      rw [mul_sub]; linarith
    have := nonpos_of_mul_nonpos_right this (hp t)
    linarith
  · intro h
    refine ⟨fun t => (h t).1, hs, fun L' hL' hs' => hs'.tsum_le_tsum (fun t => ?_) hs⟩
    exact mul_le_mul_of_nonneg_left ((h t).2 (L' t) (hL' t)) (hp t).le

/-- **AKMM, fn. 3, p. 136.** (i) If `w = A`, every `L ≥ 0` maximizes `AL − wL`; (ii) if
`A > w`, nothing does (profits rise without bound with scale); (iii) if `A < w`, `L = 0` is the
unique maximizer. -/
theorem labour_firm_fn3 {A w : ℝ} :
    (w = A → ∀ L, 0 ≤ L → LabourStaticOpt A w L) ∧ (w < A → ∀ L, ¬ LabourStaticOpt A w L) ∧
      (A < w → ∀ L, LabourStaticOpt A w L ↔ L = 0) := by
  refine ⟨fun h L hL => ⟨hL, fun L' _ => by simp [labourProfit, h]⟩, fun h L hopt => ?_,
    fun h L => ⟨fun hopt => ?_, fun hL => ?_⟩⟩
  · obtain ⟨hL, hmax⟩ := hopt
    have := hmax (L + 1) (by linarith)
    simp only [labourProfit] at this
    nlinarith
  · obtain ⟨hL, hmax⟩ := hopt
    have := hmax 0 le_rfl
    simp only [labourProfit, mul_zero, sub_zero] at this
    nlinarith
  · subst hL
    refine ⟨le_rfl, fun L' hL' => ?_⟩
    simp only [labourProfit, mul_zero, sub_zero]
    nlinarith

/-- **AKMM, p. 137: in equilibrium `wₜ = Aₜ`.** If the firm's plan solves (5.6) at positive
prices with positive employment `Lₜ > 0`, then `wₜ = Aₜ`. -/
theorem labour_wage_eq_productivity {p A w L : ℕ → ℝ} (hp : ∀ t, 0 < p t)
    (hopt : LabourFirmOpt p A w L) {t : ℕ} (hLt : 0 < L t) : w t = A t := by
  have hs := (eq_5_6_static hp hopt.2.1).1 hopt t
  rcases lt_trichotomy (w t) (A t) with h | h | h
  · exact absurd hs ((labour_firm_fn3.2.1 h) _)
  · exact h
  · exact absurd (((labour_firm_fn3.2.2 h) _).1 hs) hLt.ne'

/-! ### The household -/

/-- AKMM, (5.7), p. 136: the household budget set: positive consumption, nonnegative hours and
`Σ pₜcₜ = Σ pₜwₜeℓₜ`, both series convergent. -/
def LabourBudget (p w : ℕ → ℝ) (e : ℝ) (c l : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ (∀ t, 0 ≤ l t) ∧ Summable (fun t => p t * c t) ∧
    Summable (fun t => p t * w t * e * l t) ∧ ∑' t, p t * c t = ∑' t, p t * w t * e * l t

/-- AKMM, Definition 3, part 1, p. 136: `(c, ℓ)` maximizes `Σ βᵗ[u(cₜ) − v(ℓₜ)]` (5.4) over the
budget set, among plans with a convergent utility series. -/
def LabourOptimal (u v : ℝ → ℝ) (β : ℝ) (p w : ℕ → ℝ) (e : ℝ) (c l : ℕ → ℝ) : Prop :=
  LabourBudget p w e c l ∧ Summable (fun t => β ^ t * (u (c t) - v (l t))) ∧
    ∀ x m, LabourBudget p w e x m → Summable (fun t => β ^ t * (u (x t) - v (m t))) →
      ∑' t, β ^ t * (u (x t) - v (m t)) ≤ ∑' t, β ^ t * (u (c t) - v (l t))

/-- **AKMM, (5.8), p. 137.** At an optimum with positive prices, `βˢu′(c_s)pₜ = βᵗu′(cₜ)p_s`,
i.e. `βᵗu′(cₜ) = λpₜ` with one multiplier. -/
theorem eq_5_8 {u v : ℝ → ℝ} {β e : ℝ} {p w c l du : ℕ → ℝ}
    (hopt : LabourOptimal u v β p w e c l) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (s t : ℕ) :
    β ^ s * du s * p t = β ^ t * du t * p s := by
  rcases eq_or_ne s t with rfl | hst
  · ring
  obtain ⟨⟨hpos, hl, hsum, hsumw, hW⟩, husum, hmax⟩ := hopt
  set r := p s / p t with hr
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = s then c s + ε else if n = t then c t - r * ε else c n
  have hxs : ∀ ε, x ε s = c s + ε := fun ε => by simp [x]
  have hxt : ∀ ε, x ε t = c t - r * ε := fun ε => by simp [x, hst.symm]
  have hxo : ∀ ε, ∀ n ∉ ({s, t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hpt := hp t
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε ∧ 0 < c t - r * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos s)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - r * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n)))
      (β ^ s * du s + β ^ t * (du t * (-r))) 0 := by
    have e : (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n))) =
        fun ε => β ^ s * u (c s + ε) + β ^ t * u (c t - r * ε) -
          (β ^ s * v (l s) + β ^ t * v (l t)) := by
      funext ε; rw [Finset.sum_pair hst, hxs, hxt]; ring
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c s + ε)) (du s) 0 := by
      have hu : HasDerivAt u (du s) (c s + 0) := by simpa using hd s
      simpa using hu.comp_const_add (c s) 0
    have h2 : HasDerivAt (fun ε => u (c t - r * ε)) (du t * (-r)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - r * ε) (-r) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul r).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - r * 0) := by simpa using hd t
      exact hu.comp 0 hin
    exact ((h1.const_mul _).add (h2.const_mul _)).sub_const _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (l n))) {s, t} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      refine hmax (x ε) l ⟨fun n => ?_, hl, ?_, hsumw, ?_⟩ hU
      · by_cases h1 : n = s
        · subst h1; rw [hxs]; exact hε.1
        by_cases h2 : n = t
        · subst h2; rw [hxt]; exact hε.2
        simp only [x, h1, h2, ite_false]; exact hpos n
      · exact (ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {s, t}
          (fun n hn => by simp only [hxo ε n hn]) hsum).1
      · obtain ⟨_, hE⟩ := ce_tsum_perturb (f := fun n => p n * c n)
          (g := fun n => p n * x ε n) {s, t} (fun n hn => by simp only [hxo ε n hn]) hsum
        have hz : p s * (c s + ε) - p s * c s + (p t * (c t - r * ε) - p t * c t) = 0 := by
          rw [hr]; field_simp; ring
        rw [hE, Finset.sum_pair hst, hxs, hxt, hz, add_zero, hW]) hd'
  rw [hr] at hzero
  field_simp at hzero
  linarith

/-- **AKMM, (5.9), p. 137.** At an optimum with `β > 0` and positive hours `ℓₜ > 0`,
`v′(ℓₜ) = ewₜu′(cₜ)`. Proved by working `ε` more hours at `t` and consuming the wage. -/
theorem eq_5_9 {u v : ℝ → ℝ} {β e : ℝ} {p w c l : ℕ → ℝ} {du dv : ℝ} {t : ℕ}
    (hopt : LabourOptimal u v β p w e c l) (hβ : 0 < β) (hlt : 0 < l t)
    (hdu : HasDerivAt u du (c t)) (hdv : HasDerivAt v dv (l t)) : dv = e * w t * du := by
  obtain ⟨⟨hpos, hl, hsum, hsumw, hW⟩, husum, hmax⟩ := hopt
  set k := e * w t with hk
  let x : ℝ → ℕ → ℝ := fun ε n => if n = t then c t + k * ε else c n
  let m : ℝ → ℕ → ℝ := fun ε n => if n = t then l t + ε else l n
  have hxo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [x, hn]
  have hmo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), m ε n = l n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [m, hn]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + k * ε ∧ 0 < l t + ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + k * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < l t + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hlt)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n)))
      (β ^ t * (du * k - dv)) 0 := by
    have e1 : (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n))) =
        fun ε => β ^ t * (u (c t + k * ε) - v (l t + ε)) := by
      funext ε; simp [x, m]
    rw [e1]
    have h1 : HasDerivAt (fun ε => u (c t + k * ε)) (du * k) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t + k * ε) k 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul k).const_add (c t)
      have hu : HasDerivAt u du (c t + k * 0) := by simpa using hdu
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => v (l t + ε)) dv 0 := by
      have hv : HasDerivAt v dv (l t + 0) := by simpa using hdv
      simpa using hv.comp_const_add (l t) 0
    exact (h1.sub h2).const_mul _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (m ε n))) {t} husum
    (fun ε n hn => by simp only [hxo ε n hn, hmo ε n hn])
    (fun n => by simp only [x, m]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      have hS1 := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {t}
        (fun n hn => by simp only [hxo ε n hn]) hsum
      have hS2 := ce_tsum_perturb (f := fun n => p n * w n * e * l n)
        (g := fun n => p n * w n * e * m ε n) {t} (fun n hn => by simp only [hmo ε n hn]) hsumw
      refine hmax (x ε) (m ε) ⟨fun n => ?_, fun n => ?_, hS1.1, hS2.1, ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; simp only [x, ite_true]; exact hε.1
        simp only [x, h1, ite_false]; exact hpos n
      · by_cases h1 : n = t
        · subst h1; simp only [m, ite_true]; exact hε.2.le
        simp only [m, h1, ite_false]; exact hl n
      · rw [hS1.2, hS2.2, hW, Finset.sum_singleton, Finset.sum_singleton]
        simp only [x, m, ite_true, hk]
        ring) hd'
  have := (pow_pos hβ t).ne'
  have h2 : du * k - dv = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h this
    · exact h
  rw [hk] at h2
  linarith

/-- **AKMM, (5.10), p. 137.** At an optimum with `β > 0`, positive prices and `u′(cₜ) ≠ 0`,
`p_{t+1}/pₜ = βu′(c_{t+1})/u′(cₜ)`. -/
theorem eq_5_10 {u v : ℝ → ℝ} {β e : ℝ} {p w c l du : ℕ → ℝ}
    (hopt : LabourOptimal u v β p w e c l) (hβ : 0 < β) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (t : ℕ) (hdt : du t ≠ 0) :
    p (t + 1) / p t = β * du (t + 1) / du t := by
  have h := eq_5_8 hopt hp hd t (t + 1)
  have := (hp t).ne'
  have hb := (pow_pos hβ t).ne'
  rw [div_eq_div_iff this hdt]
  rw [pow_succ] at h
  apply mul_left_cancel₀ hb
  linarith

/-- **AKMM, p. 137: the first-order conditions are sufficient.** If `u` lies below and `v` above
their tangents, `(c, ℓ)` is budget-feasible with a convergent utility series,
`βᵗu′(cₜ) = λpₜ` and `v′(ℓₜ) = ewₜu′(cₜ)`, and `β ≥ 0`, then `(c, ℓ)` is optimal. -/
theorem labour_foc_sufficient {u v : ℝ → ℝ} {β e lam : ℝ} {p w c l du dv : ℕ → ℝ}
    (hβ : 0 ≤ β) (hut : ∀ t x, 0 < x → u x ≤ u (c t) + du t * (x - c t))
    (hvt : ∀ t m, 0 ≤ m → v (l t) + dv t * (m - l t) ≤ v m)
    (h58 : ∀ t, β ^ t * du t = lam * p t) (h59 : ∀ t, dv t = e * w t * du t)
    (hb : LabourBudget p w e c l) (hU : Summable (fun t => β ^ t * (u (c t) - v (l t)))) :
    LabourOptimal u v β p w e c l := by
  refine ⟨hb, hU, fun x m hx hUx => ?_⟩
  obtain ⟨_, _, hcs, hcw, hcW⟩ := hb
  obtain ⟨hxp, hmp, hxs, hxw, hxW⟩ := hx
  have key : ∀ t, β ^ t * (u (x t) - v (m t)) ≤ β ^ t * (u (c t) - v (l t)) +
      lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
    intro t
    have h1 := hut t (x t) (hxp t)
    have h2 := hvt t (m t) (hmp t)
    have h3 : β ^ t * (u (x t) - v (m t)) ≤
        β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ t)
    have h4 : β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) =
        β ^ t * (u (c t) - v (l t)) +
          lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
      rw [h59 t]
      have : β ^ t * (du t * (x t - c t) - e * w t * du t * (m t - l t)) =
          (β ^ t * du t) * ((x t - c t) - e * w t * (m t - l t)) := by ring
      linear_combination this + (x t - c t - e * w t * (m t - l t)) * h58 t
    linarith
  have hS2 : Summable (fun t => lam * ((p t * x t - p t * c t) -
      (p t * w t * e * m t - p t * w t * e * l t))) :=
    ((hxs.sub hcs).sub (hxw.sub hcw)).mul_left lam
  have := hUx.tsum_le_tsum key (hU.add hS2)
  rw [hU.tsum_add hS2, tsum_mul_left, ((hxs.sub hcs)).tsum_sub (hxw.sub hcw),
    hxs.tsum_sub hcs, hxw.tsum_sub hcw, hxW, hcW] at this
  linarith

/-- **AKMM, Definition 3, p. 136.** An Arrow–Debreu equilibrium of the labour economy:
households optimize, the firm solves (5.6), and labour and goods markets clear,
`∫ eᵢℓ_{i,t} di = Lₜ` and `∫ c_{i,t} di = AₜLₜ`. -/
def IsADEquilibriumLabour (μ : Measure I) (u v : ℝ → ℝ) (β : ℝ) (e : I → ℝ)
    (A : ℕ → ℝ) (c l : I → ℕ → ℝ) (L p w : ℕ → ℝ) : Prop :=
  (∀ i, LabourOptimal u v β p w (e i) (c i) (l i)) ∧ LabourFirmOpt p A w L ∧
    ∀ t, ∫ i, e i * l i t ∂μ = L t ∧ ∫ i, c i t ∂μ = A t * L t

/-- **AKMM, p. 137: log consumption shares.** In an equilibrium with log utility, positive
prices, `p₀ = 1` and positive output `AₜLₜ`, `c_{i,t} = θᵢYₜ` with `Yₜ = AₜLₜ` and
`θᵢ = c_{i,0}/Y₀`. -/
theorem labour_log_shares {μ : Measure I} {v : ℝ → ℝ} {β : ℝ} {e : I → ℝ} {A : ℕ → ℝ}
    {c l : I → ℕ → ℝ} {L p w : ℕ → ℝ}
    (he : IsADEquilibriumLabour μ Real.log v β e A c l L p w) (hp : ∀ t, 0 < p t)
    (hp0 : p 0 = 1) (hY : ∀ t, 0 < A t * L t) (i : I) (t : ℕ) :
    c i t = c i 0 / (A 0 * L 0) * (A t * L t) := by
  obtain ⟨hopt, _, hclear⟩ := he
  have hfoc : ∀ i t, p t * c i t = β ^ t * c i 0 := by
    intro i t
    have hc := (hopt i).1.1
    have h := eq_5_8 (hopt i) hp (du := fun t => (c i t)⁻¹)
      (fun t => Real.hasDerivAt_log (hc t).ne') 0 t
    rw [hp0] at h
    have := (hc t).ne'
    have := (hc 0).ne'
    field_simp at h
    linarith
  have h : (fun i => p t * c i t) = fun i => β ^ t * c i 0 := funext fun i => hfoc i t
  have hi := congrArg (fun f => ∫ i, f i ∂μ) h
  simp only [integral_const_mul, (hclear _).2] at hi
  have hX := (hY 0).ne'
  have := (hp t).ne'
  have h1 := hfoc i t
  have e1 : c i t = β ^ t * c i 0 / p t := by field_simp; linarith
  have e2 : A t * L t = β ^ t * (A 0 * L 0) / p t := by field_simp; linarith
  rw [e1, e2, div_mul_div_comm,
    show c i 0 * (β ^ t * (A 0 * L 0)) = β ^ t * c i 0 * (A 0 * L 0) by ring,
    mul_comm (A 0 * L 0) (p t), mul_div_mul_right _ _ hX]

/-- **AKMM, p. 138: the log hours condition.** With log utility, `wₜ = Aₜ` and
`c_{i,t} = θᵢYₜ`, (5.9) reads `v′(ℓ_{i,t})θᵢYₜ = eᵢAₜ` at positive hours. -/
theorem labour_log_hours {v : ℝ → ℝ} {β e θ : ℝ} {p A c l : ℕ → ℝ} {Y : ℕ → ℝ} {dv : ℝ}
    {t : ℕ} (hopt : LabourOptimal Real.log v β p A e c l) (hβ : 0 < β) (hlt : 0 < l t)
    (hdv : HasDerivAt v dv (l t)) (hc : c t = θ * Y t) : dv * (θ * Y t) = e * A t := by
  have hct := hopt.1.1 t
  have h := eq_5_9 hopt hβ hlt (Real.hasDerivAt_log hct.ne') hdv
  rw [h, ← hc]
  field_simp

/-- **AKMM, p. 138: equal hours under `θᵢ = eᵢ`.** If `v′` is injective on the positive reals and
households `i, j` with `eᵢ, eⱼ > 0` have `v′(ℓ_{k,t})eₖYₜ = eₖAₜ`, they work the same hours. -/
theorem labour_log_equal_hours {dv : ℝ → ℝ} (hinj : Set.InjOn dv (Set.Ioi 0))
    {ei ej Yt At li lj : ℝ}
    (hei : 0 < ei) (hej : 0 < ej) (hY : 0 < Yt) (hli : 0 < li) (hlj : 0 < lj)
    (hi : dv li * (ei * Yt) = ei * At) (hj : dv lj * (ej * Yt) = ej * At) : li = lj := by
  apply hinj hli hlj
  have h1 : dv li = At / Yt := by field_simp; nlinarith
  have h2 : dv lj = At / Yt := by field_simp; nlinarith
  rw [h1, h2]

/-- **AKMM, pp. 137–138: the log equilibrium.** Let `0 < β < 1`, skills `eᵢ > 0` with
`∫ eᵢ di = 1`, productivity `Aₜ > 0` with `Σ βᵗ log Aₜ` convergent, and `v` convex with
`v′(L)L = 1` at some `L > 0`. Then `pₜ = βᵗA₀/Aₜ`, `wₜ = Aₜ`, `c_{i,t} = eᵢAₜL`,
`ℓ_{i,t} = L` and `Lₜ = L` form an equilibrium (Definition 3): `θᵢ = eᵢ` and equal hours. -/
theorem labour_log_equilibrium {μ : Measure I} [IsProbabilityMeasure μ] {v : ℝ → ℝ}
    {β Lbar dvL : ℝ} {e : I → ℝ} {A : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (he : ∀ i, 0 < e i) (he1 : ∫ i, e i ∂μ = 1)
    (hA : ∀ t, 0 < A t) (hlogA : Summable (fun t => β ^ t * Real.log (A t)))
    (hL : 0 < Lbar) (hvt : ∀ m, 0 ≤ m → v Lbar + dvL * (m - Lbar) ≤ v m)
    (hfoc : dvL * Lbar = 1) :
    IsADEquilibriumLabour μ Real.log v β e A (fun i t => e i * A t * Lbar) (fun _ _ => Lbar)
      (fun _ => Lbar) (fun t => β ^ t * A 0 / A t) A := by
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  refine ⟨fun i => ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · have hc : ∀ t, 0 < e i * A t * Lbar := fun t => mul_pos (mul_pos (he i) (hA t)) hL
    have hpc : (fun t => β ^ t * A 0 / A t * (e i * A t * Lbar)) =
        fun t => e i * A 0 * Lbar * β ^ t := by
      funext t; have := (hA t).ne'; field_simp
    have hpw : (fun t => β ^ t * A 0 / A t * A t * e i * Lbar) =
        fun t => e i * A 0 * Lbar * β ^ t := by
      funext t; have := (hA t).ne'; field_simp
    refine labour_foc_sufficient (du := fun t => (e i * A t * Lbar)⁻¹) (dv := fun _ => dvL)
      (lam := (e i * A 0 * Lbar)⁻¹) hβ0.le (fun t x hx => ce_log_tangent (hc t) hx)
      (fun t m hm => hvt m hm) (fun t => ?_) (fun t => ?_) ⟨hc, fun _ => hL.le, ?_, ?_, ?_⟩ ?_
    · have := (hA t).ne'; have := (hA 0).ne'; have := (he i).ne'; have := hL.ne'
      field_simp
    · have := (hA t).ne'; have := (he i).ne'; have := hL.ne'
      field_simp
      linarith
    · rw [hpc]; exact hgeo.mul_left _
    · rw [hpw]; exact hgeo.mul_left _
    · rw [hpc, hpw]
    · have e1 : (fun t => β ^ t * (Real.log (e i * A t * Lbar) - v Lbar)) =
          fun t => (Real.log (e i) + Real.log Lbar - v Lbar) * β ^ t + β ^ t * Real.log (A t) := by
        funext t
        rw [Real.log_mul (mul_pos (he i) (hA t)).ne' hL.ne', Real.log_mul (he i).ne' (hA t).ne']
        ring
      rw [e1]; exact (hgeo.mul_left _).add hlogA
  · have hpos : ∀ t, 0 < β ^ t * A 0 / A t := fun t =>
      div_pos (mul_pos (pow_pos hβ0 t) (hA 0)) (hA t)
    have hz : Summable (fun t => β ^ t * A 0 / A t * labourProfit (A t) (A t) Lbar) := by
      simp [labourProfit]
    exact (eq_5_6_static hpos hz).2 fun t => (labour_firm_fn3.1 rfl) Lbar hL.le
  · simp only
    rw [integral_mul_const, he1, one_mul]
  · simp only
    rw [integral_mul_const, integral_mul_const, he1, one_mul]

/-- **AKMM, pp. 137–138: an instance.** On `[0, 1]` with Lebesgue measure, unit skills,
`Aₜ = 1`, `v(ℓ) = ℓ²/2` (so `v′(1)·1 = 1`) and `β = 1/2`, the log equilibrium has `L = 1`. -/
theorem labour_log_equilibrium_instance :
    IsADEquilibriumLabour (volume : Measure unitInterval) Real.log (fun l => l ^ 2 / 2) (1 / 2)
      (fun _ => 1) (fun _ => 1) (fun i t => (fun _ => (1 : ℝ)) i * (fun _ => (1 : ℝ)) t * 1)
      (fun _ _ => 1) (fun _ => 1) (fun t => (1 / 2 : ℝ) ^ t * 1 / 1) (fun _ => 1) :=
  labour_log_equilibrium (dvL := 1) (by norm_num) (by norm_num) (fun _ => one_pos) (by simp)
    (fun _ => one_pos) (by simp) one_pos (fun m _ => by nlinarith [sq_nonneg (m - 1)])
    (by norm_num)

/-! ### The static examples -/

/-- **AKMM, p. 138: with labour income only, hours do not depend on the wage.** For `w, w' > 0`,
`ℓ > 0` maximizes `log(wℓ) − v(ℓ)` over `ℓ > 0` iff it maximizes `log(w'ℓ) − v(ℓ)`. -/
theorem labour_static_wage_independent {v : ℝ → ℝ} {w w' l : ℝ} (hw : 0 < w) (hw' : 0 < w') :
    (∀ m, 0 < m → Real.log (w * m) - v m ≤ Real.log (w * l) - v l) → 0 < l →
      ∀ m, 0 < m → Real.log (w' * m) - v m ≤ Real.log (w' * l) - v l := by
  intro h hl m hm
  have := h m hm
  rw [Real.log_mul hw.ne' hm.ne', Real.log_mul hw.ne' hl.ne'] at this
  rw [Real.log_mul hw'.ne' hm.ne', Real.log_mul hw'.ne' hl.ne']
  linarith

/-- **AKMM, p. 138, corrected: the first-order condition with asset income.** If `ℓ > 0`
maximizes `log(eAℓ + a) − v(ℓ)` over `ℓ ≥ 0` with `eAℓ + a > 0`, then
`v′(ℓ) = eA/(eAℓ + a)`. The book prints the numerator as `aᵢA`. -/
theorem labour_static_asset_foc {v : ℝ → ℝ} {e A a l dv : ℝ} (hl : 0 < l) (hc : 0 < e * A * l + a)
    (hmax : ∀ m, 0 ≤ m → 0 < e * A * m + a →
      Real.log (e * A * m + a) - v m ≤ Real.log (e * A * l + a) - v l)
    (hdv : HasDerivAt v dv l) : dv = e * A / (e * A * l + a) := by
  have hloc : IsLocalMax (fun m => Real.log (e * A * m + a) - v m) l := by
    have h1 : ∀ᶠ m in 𝓝 l, 0 < m := lt_mem_nhds hl
    have h2 : ∀ᶠ m in 𝓝 l, 0 < e * A * m + a :=
      continuousAt_const.eventually_lt
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt (by simpa using hc)
    filter_upwards [h1, h2] with m hm1 hm2
    exact hmax m hm1.le hm2
  have hd : HasDerivAt (fun m => Real.log (e * A * m + a) - v m)
      ((e * A) / (e * A * l + a) - dv) l := by
    have hin : HasDerivAt (fun m => e * A * m + a) (e * A) l := by
      simpa using ((hasDerivAt_id l).const_mul (e * A)).add_const a
    have := ((Real.hasDerivAt_log hc.ne').comp l hin).sub hdv
    rw [← div_eq_inv_mul] at this
    exact this
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, p. 138: the printed condition `v′(ℓ) = aA/(eAℓ + a)` is false.** With `e = A = 1`,
`a = 2` and `v(ℓ) = ℓ²/2`, hours `ℓ* = √2 − 1` maximize `log(ℓ + 2) − ℓ²/2` over `ℓ ≥ 0`, but
`v′(ℓ*) = ℓ*` while `aA/(eAℓ* + a) = 2ℓ*`. -/
theorem labour_static_asset_printed_counterexample :
    let l := Real.sqrt 2 - 1
    0 < l ∧ (∀ m, 0 ≤ m → Real.log (m + 2) - m ^ 2 / 2 ≤ Real.log (l + 2) - l ^ 2 / 2) ∧
      l ≠ 2 * 1 / (1 * 1 * l + 2) := by
  intro l
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hl : 0 < l := by simp only [l]; linarith
  have hfoc : l * (l + 2) = 1 := by simp only [l]; nlinarith
  refine ⟨hl, fun m hm => ?_, ?_⟩
  · have h1 := ce_log_tangent (show 0 < l + 2 by linarith) (show 0 < m + 2 by linarith)
    have h2 : (l + 2)⁻¹ = l := by
      have : l + 2 ≠ 0 := by linarith
      field_simp; linarith
    rw [h2] at h1
    nlinarith [sq_nonneg (m - l)]
  · intro h
    have h3 : l * (l + 2) = 2 := by
      field_simp at h
      nlinarith
    linarith

/-- **AKMM, p. 138: more assets, fewer hours.** If `v′` is increasing and hours `ℓ₁, ℓ₂ > 0`
satisfy the first-order condition `v′(ℓ)(eAℓ + a) = eA` at asset levels `a₁ < a₂` (with
`eA > 0`), then `ℓ₂ < ℓ₁`. -/
theorem labour_assets_lower_hours {dv : ℝ → ℝ} (hmono : Monotone dv) {e A a1 a2 l1 l2 : ℝ}
    (heA : 0 < e * A) (ha : a1 < a2) (hc1 : 0 < e * A * l1 + a1)
    (h1 : dv l1 * (e * A * l1 + a1) = e * A) (h2 : dv l2 * (e * A * l2 + a2) = e * A) :
    l2 < l1 := by
  by_contra hle'
  have hle := not_lt.1 hle'
  have hv1 : 0 < dv l1 := by
    by_contra h; have h' := not_lt.1 h; nlinarith
  have hv := hmono hle
  have : dv l1 * (e * A * l1 + a1) < dv l2 * (e * A * l2 + a2) := by
    have : e * A * l1 + a1 < e * A * l2 + a2 := by nlinarith
    calc dv l1 * (e * A * l1 + a1) < dv l1 * (e * A * l2 + a2) := by
          exact mul_lt_mul_of_pos_left this hv1
      _ ≤ dv l2 * (e * A * l2 + a2) := by
          exact mul_le_mul_of_nonneg_right hv (by linarith)
  linarith

end AKMM.CompetitiveEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Arrow–Debreu equilibrium of the neoclassical growth economy

AKMM, §5.2.3, pp. 139–142. Output `Yₜ = AₜKₜ^αLₜ^{1−α}` (5.11); households own capital,
`k_{i,t+1} = (1 − δ)k_{i,t} + ι_{i,t}` (5.13), and face the date-0 budget (5.14); the firm rents
capital and labour (5.12).

* The firm: the marginal-product conditions `rₜ = αAₜKₜ^{α−1}Lₜ^{1−α}`,
  `wₜ = (1 − α)AₜKₜ^αLₜ^{−α}` are necessary for an interior optimum (`growth_firm_foc`), and
  sufficient, with zero profit (`growth_firm_optimal`, by the weighted AM–GM inequality); the
  capital–labour ratio is pinned down (`growth_firm_ratio`).
* The household (Definition 4, `GrowthOptimal`): (5.15), (5.16) and the no-arbitrage condition
  (5.17) are necessary (`eq_5_15`, `eq_5_16`, `eq_5_17`).
* The consolidated budget `Σ pₜc_{i,t} = Σ pₜwₜeᵢℓ_{i,t} + (1 − δ + r₀)k_{i,0}` holds iff
  `p_Tk_{T+1} → 0` (`growth_consolidated_budget`); the book uses it without this condition. When
  the rental share of the gross return is bounded below, every budget-feasible plan has
  `p_Tk_{T+1} → 0` (`growth_capital_value_tendsto_zero`), and then (5.15)–(5.17) are sufficient
  (`growth_foc_sufficient`); a concrete optimal plan (`growth_optimal_instance`).
* Log utility with `k_{i,0} = eᵢK₀` and common hours: `c_{i,t} = eᵢβᵗ(1 − β)W/pₜ`
  (`growth_log_consumption`), so `θᵢ = eᵢ` (fn. 6, `growth_fn6`) and the hours condition does
  not depend on `i` (`growth_log_hours_common`).
* The aggregate system: the aggregate Euler equation (`growth_log_aggregate_euler`), (5.18),
  (5.19), (5.20) (`eq_5_18`, `eq_5_19`, `eq_5_20`); fn. 7, `δ = 1`: saving rate `αβ` and
  `v′(L)L = (1 − α)/(1 − αβ)` (`growth_fn7`).
* The planner (p. 142): the first-order conditions of `Σ βᵗ[log Cₜ − v(Lₜ)]` with respect to
  `K_{t+1}` and `Lₜ` are exactly (5.18) and (5.19) (`growth_planner_foc_K`,
  `growth_planner_foc_L`).

Departures: the household chooses the capital path `k` (with `k₀` given) rather than investment
`ι`, which (5.13) determines one-to-one; consumption positive, hours nonnegative; the values of
consumption, investment, capital income and labour income converge separately, and the utility
series converge.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-! ### The firm -/

/-- The Cobb–Douglas firm's profit `AK^αL^{1−α} − rK − wL` (AKMM, (5.12), p. 139). -/
noncomputable def cdProfit (A α r w K L : ℝ) : ℝ := A * K ^ α * L ^ (1 - α) - r * K - w * L

/-- **AKMM, p. 141: the firm's first-order conditions are necessary.** If `(K, L)` with
`K, L > 0` maximizes the profit over positive inputs, then `r = αAK^{α−1}L^{1−α}` and
`w = (1 − α)AK^αL^{−α}`. -/
theorem growth_firm_foc {A α r w K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hmax : ∀ K' L', 0 < K' → 0 < L' → cdProfit A α r w K' L' ≤ cdProfit A α r w K L) :
    r = α * A * K ^ (α - 1) * L ^ (1 - α) ∧ w = (1 - α) * A * K ^ α * L ^ (-α) := by
  constructor
  · have hloc : IsLocalMax (fun K' => cdProfit A α r w K' L) K := by
      filter_upwards [lt_mem_nhds hK] with K' hK' using hmax K' L hK' hL
    have hd : HasDerivAt (fun K' => cdProfit A α r w K' L)
        (A * (α * K ^ (α - 1)) * L ^ (1 - α) - r * 1) K := by
      have h := ((((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul A).mul_const
        (L ^ (1 - α))).sub ((hasDerivAt_id K).const_mul r)).sub_const (w * L)
      unfold cdProfit
      convert h using 1
      funext x; simp
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  · have hloc : IsLocalMax (fun L' => cdProfit A α r w K L') L := by
      filter_upwards [lt_mem_nhds hL] with L' hL' using hmax K L' hK hL'
    have hd : HasDerivAt (fun L' => cdProfit A α r w K L')
        (A * K ^ α * ((1 - α) * L ^ (1 - α - 1)) - w * 1) L := by
      have h := (((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul
        (A * K ^ α)).sub_const (r * K)).sub ((hasDerivAt_id L).const_mul w)
      unfold cdProfit
      convert h using 1
      funext x; simp
    have := hloc.hasDerivAt_eq_zero hd
    have e : (1 : ℝ) - α - 1 = -α := by ring
    rw [e] at this
    linarith

/-- **AKMM, p. 141: the marginal-product prices make `(K, L)` optimal with zero profit.** For
`0 ≤ α ≤ 1`, `A ≥ 0` and `K, L > 0`, at `r = αAK^{α−1}L^{1−α}`, `w = (1 − α)AK^αL^{−α}` every
`(K', L') ≥ 0` earns at most the profit `0` earned at `(K, L)`: the firm is indifferent to its
scale. -/
theorem growth_firm_optimal {A α K L : ℝ} (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hK : 0 < K)
    (hL : 0 < L) :
    cdProfit A α (α * A * K ^ (α - 1) * L ^ (1 - α)) ((1 - α) * A * K ^ α * L ^ (-α)) K L = 0 ∧
      ∀ K' L', 0 ≤ K' → 0 ≤ L' →
        cdProfit A α (α * A * K ^ (α - 1) * L ^ (1 - α)) ((1 - α) * A * K ^ α * L ^ (-α)) K' L'
          ≤ 0 := by
  have hKa : K ^ (α - 1) = K ^ α / K := Real.rpow_sub_one hK.ne' α
  have hLa : L ^ (-α) = L ^ (1 - α) / L := by
    rw [show -α = (1 - α) - 1 by ring, Real.rpow_sub_one hL.ne']
  have hKpos := Real.rpow_pos_of_pos hK α
  have hLpos := Real.rpow_pos_of_pos hL (1 - α)
  constructor
  · unfold cdProfit; rw [hKa, hLa]; field_simp; ring
  intro K' L' hK' hL'
  have amgm := Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith : 0 ≤ 1 - α)
    (div_nonneg hK' hK.le) (div_nonneg hL' hL.le) (by ring)
  rw [Real.div_rpow hK' hK.le, Real.div_rpow hL' hL.le] at amgm
  have key : K' ^ α * L' ^ (1 - α) ≤ K ^ α * L ^ (1 - α) * (α * (K' / K) + (1 - α) * (L' / L)) := by
    have h := mul_le_mul_of_nonneg_left amgm (mul_pos hKpos hLpos).le
    have e : K ^ α * L ^ (1 - α) * (K' ^ α / K ^ α * (L' ^ (1 - α) / L ^ (1 - α))) =
        K' ^ α * L' ^ (1 - α) := by field_simp
    linarith
  unfold cdProfit
  rw [hKa, hLa]
  have h2 := mul_le_mul_of_nonneg_left key hA
  have e : A * (K ^ α * L ^ (1 - α) * (α * (K' / K) + (1 - α) * (L' / L))) =
      α * A * (K ^ α / K) * L ^ (1 - α) * K' + (1 - α) * A * K ^ α * (L ^ (1 - α) / L) * L' := by
    field_simp
  nlinarith

/-- **AKMM, p. 141: the capital–labour ratio is pinned down.** For `0 < α < 1` and `A > 0`, any
two interior optima at the same rental rate have the same capital–labour ratio. -/
theorem growth_firm_ratio {A α r K₁ L₁ K₂ L₂ : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hK₁ : 0 < K₁) (hL₁ : 0 < L₁) (hK₂ : 0 < K₂) (hL₂ : 0 < L₂)
    (h₁ : r = α * A * K₁ ^ (α - 1) * L₁ ^ (1 - α)) (h₂ : r = α * A * K₂ ^ (α - 1) * L₂ ^ (1 - α)) :
    K₁ / L₁ = K₂ / L₂ := by
  have hr : ∀ K L : ℝ, 0 < K → 0 < L → K ^ (α - 1) * L ^ (1 - α) = (K / L) ^ (α - 1) := by
    intro K L hK hL
    rw [Real.div_rpow hK.le hL.le, show 1 - α = -(α - 1) by ring, Real.rpow_neg hL.le]
    field_simp
  have e : (K₁ / L₁) ^ (α - 1) = (K₂ / L₂) ^ (α - 1) := by
    rw [← hr K₁ L₁ hK₁ hL₁, ← hr K₂ L₂ hK₂ hL₂]
    have : α * A ≠ 0 := (mul_pos hα0 hA).ne'
    apply mul_left_cancel₀ this
    linarith
  have hne : α - 1 ≠ 0 := by linarith
  have := congrArg (fun x => x ^ (α - 1)⁻¹) e
  rwa [Real.rpow_rpow_inv (div_pos hK₁ hL₁).le hne,
    Real.rpow_rpow_inv (div_pos hK₂ hL₂).le hne] at this

/-! ### The household -/

/-- AKMM, (5.13)–(5.14), p. 139: the household budget set. The plan is consumption `c > 0`,
hours `ℓ ≥ 0` and capital `k` with `k₀` given; investment is `ιₜ = k_{t+1} − (1 − δ)kₜ`; the
values of consumption, investment, capital income and labour income converge, and
`Σ pₜ(cₜ + ιₜ) = Σ pₜ(rₜkₜ + wₜeℓₜ)`. -/
def GrowthBudget (p r w : ℕ → ℝ) (δ e k0 : ℝ) (c k l : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ (∀ t, 0 ≤ l t) ∧ k 0 = k0 ∧ Summable (fun t => p t * c t) ∧
    Summable (fun t => p t * (k (t + 1) - (1 - δ) * k t)) ∧
    Summable (fun t => p t * (r t * k t)) ∧ Summable (fun t => p t * w t * e * l t) ∧
    ∑' t, p t * (c t + (k (t + 1) - (1 - δ) * k t)) = ∑' t, p t * (r t * k t + w t * e * l t)

/-- **AKMM, Definition 4, part 1, p. 140.** The household's plan maximizes
`Σ βᵗ[u(cₜ) − v(ℓₜ)]` over the budget set, among plans with a convergent utility series. -/
def GrowthOptimal (u v : ℝ → ℝ) (β : ℝ) (p r w : ℕ → ℝ) (δ e k0 : ℝ) (c k l : ℕ → ℝ) : Prop :=
  GrowthBudget p r w δ e k0 c k l ∧ Summable (fun t => β ^ t * (u (c t) - v (l t))) ∧
    ∀ x kk m, GrowthBudget p r w δ e k0 x kk m →
      Summable (fun t => β ^ t * (u (x t) - v (m t))) →
        ∑' t, β ^ t * (u (x t) - v (m t)) ≤ ∑' t, β ^ t * (u (c t) - v (l t))

/-- **AKMM, (5.15), p. 140.** At an optimum with positive prices,
`βˢu′(c_s)pₜ = βᵗu′(cₜ)p_s`: one multiplier `λᵢ` with `βᵗu′(c_{i,t}) = λᵢpₜ`. -/
theorem eq_5_15 {u v : ℝ → ℝ} {β δ e k0 : ℝ} {p r w c k l du : ℕ → ℝ}
    (hopt : GrowthOptimal u v β p r w δ e k0 c k l) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (s t : ℕ) :
    β ^ s * du s * p t = β ^ t * du t * p s := by
  rcases eq_or_ne s t with rfl | hst
  · ring
  obtain ⟨⟨hpos, hl, hk0, hc, hι, hrk, hwl, hW⟩, husum, hmax⟩ := hopt
  have hsum : Summable (fun t => p t * (c t + (k (t + 1) - (1 - δ) * k t))) :=
    (hc.add hι).congr fun t => by ring
  set q := p s / p t with hq
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = s then c s + ε else if n = t then c t - q * ε else c n
  have hxs : ∀ ε, x ε s = c s + ε := fun ε => by simp [x]
  have hxt : ∀ ε, x ε t = c t - q * ε := fun ε => by simp [x, hst.symm]
  have hxo : ∀ ε, ∀ n ∉ ({s, t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hpt := hp t
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε ∧ 0 < c t - q * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c s + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos s)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - q * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n)))
      (β ^ s * du s + β ^ t * (du t * (-q))) 0 := by
    have e : (fun ε => ∑ n ∈ ({s, t} : Finset ℕ), β ^ n * (u (x ε n) - v (l n))) =
        fun ε => β ^ s * u (c s + ε) + β ^ t * u (c t - q * ε) -
          (β ^ s * v (l s) + β ^ t * v (l t)) := by
      funext ε; rw [Finset.sum_pair hst, hxs, hxt]; ring
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c s + ε)) (du s) 0 := by
      have hu : HasDerivAt u (du s) (c s + 0) := by simpa using hd s
      simpa using hu.comp_const_add (c s) 0
    have h2 : HasDerivAt (fun ε => u (c t - q * ε)) (du t * (-q)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - q * ε) (-q) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - q * 0) := by simpa using hd t
      exact hu.comp 0 hin
    exact ((h1.const_mul _).add (h2.const_mul _)).sub_const _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (l n))) {s, t} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      have hP := ce_tsum_perturb (f := fun n => p n * (c n + (k (n + 1) - (1 - δ) * k n)))
        (g := fun n => p n * (x ε n + (k (n + 1) - (1 - δ) * k n))) {s, t}
        (fun n hn => by simp only [hxo ε n hn]) hsum
      have hPc := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {s, t}
        (fun n hn => by simp only [hxo ε n hn]) hc
      refine hmax (x ε) k l ⟨fun n => ?_, hl, hk0, hPc.1, hι, hrk, hwl, ?_⟩ hU
      · by_cases h1 : n = s
        · subst h1; rw [hxs]; exact hε.1
        by_cases h2 : n = t
        · subst h2; rw [hxt]; exact hε.2
        simp only [x, h1, h2, ite_false]; exact hpos n
      · have hz : p s * (x ε s + (k (s + 1) - (1 - δ) * k s)) -
            p s * (c s + (k (s + 1) - (1 - δ) * k s)) +
            (p t * (x ε t + (k (t + 1) - (1 - δ) * k t)) -
              p t * (c t + (k (t + 1) - (1 - δ) * k t))) = 0 := by
          rw [hxs, hxt, hq]; field_simp; ring
        rw [hP.2, Finset.sum_pair hst, hz, add_zero, hW]) hd'
  rw [hq] at hzero
  field_simp at hzero
  linarith

/-- **AKMM, (5.16), p. 140.** At an optimum with `β > 0` and positive hours,
`v′(ℓₜ) = ewₜu′(cₜ)`. -/
theorem eq_5_16 {u v : ℝ → ℝ} {β δ e k0 : ℝ} {p r w c k l : ℕ → ℝ} {du dv : ℝ} {t : ℕ}
    (hopt : GrowthOptimal u v β p r w δ e k0 c k l) (hβ : 0 < β) (hlt : 0 < l t)
    (hdu : HasDerivAt u du (c t)) (hdv : HasDerivAt v dv (l t)) : dv = e * w t * du := by
  obtain ⟨⟨hpos, hl, hk0, hc, hι, hrk, hwl, hW⟩, husum, hmax⟩ := hopt
  have hsum : Summable (fun t => p t * (c t + (k (t + 1) - (1 - δ) * k t))) :=
    (hc.add hι).congr fun t => by ring
  have hsumR : Summable (fun t => p t * (r t * k t + w t * e * l t)) :=
    (hrk.add hwl).congr fun t => by ring
  set q := e * w t with hq
  let x : ℝ → ℕ → ℝ := fun ε n => if n = t then c t + q * ε else c n
  let m : ℝ → ℕ → ℝ := fun ε n => if n = t then l t + ε else l n
  have hxo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [x, hn]
  have hmo : ∀ ε, ∀ n ∉ ({t} : Finset ℕ), m ε n = l n := fun ε n hn => by
    simp only [Finset.mem_singleton] at hn; simp [m, hn]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + q * ε ∧ 0 < l t + ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t + q * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < l t + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hlt)
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n)))
      (β ^ t * (du * q - dv)) 0 := by
    have e1 : (fun ε => ∑ n ∈ ({t} : Finset ℕ), β ^ n * (u (x ε n) - v (m ε n))) =
        fun ε => β ^ t * (u (c t + q * ε) - v (l t + ε)) := by
      funext ε; simp [x, m]
    rw [e1]
    have h1 : HasDerivAt (fun ε => u (c t + q * ε)) (du * q) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t + q * ε) q 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_add (c t)
      have hu : HasDerivAt u du (c t + q * 0) := by simpa using hdu
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => v (l t + ε)) dv 0 := by
      have hv : HasDerivAt v dv (l t + 0) := by simpa using hdv
      simpa using hv.comp_const_add (l t) 0
    exact (h1.sub h2).const_mul _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (m ε n))) {t} husum
    (fun ε n hn => by simp only [hxo ε n hn, hmo ε n hn])
    (fun n => by simp only [x, m]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      have hS1 := ce_tsum_perturb (f := fun n => p n * (c n + (k (n + 1) - (1 - δ) * k n)))
        (g := fun n => p n * (x ε n + (k (n + 1) - (1 - δ) * k n))) {t}
        (fun n hn => by simp only [hxo ε n hn]) hsum
      have hS2 := ce_tsum_perturb (f := fun n => p n * (r n * k n + w n * e * l n))
        (g := fun n => p n * (r n * k n + w n * e * m ε n)) {t}
        (fun n hn => by simp only [hmo ε n hn]) hsumR
      have hPc := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n) {t}
        (fun n hn => by simp only [hxo ε n hn]) hc
      have hPw := ce_tsum_perturb (f := fun n => p n * w n * e * l n)
        (g := fun n => p n * w n * e * m ε n) {t} (fun n hn => by simp only [hmo ε n hn]) hwl
      refine hmax (x ε) k (m ε)
        ⟨fun n => ?_, fun n => ?_, hk0, hPc.1, hι, hrk, hPw.1, ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; simp only [x, ite_true]; exact hε.1
        simp only [x, h1, ite_false]; exact hpos n
      · by_cases h1 : n = t
        · subst h1; simp only [m, ite_true]; exact hε.2.le
        simp only [m, h1, ite_false]; exact hl n
      · rw [hS1.2, hS2.2, hW, Finset.sum_singleton, Finset.sum_singleton]
        simp only [x, m, ite_true, hq]
        ring) hd'
  have := (pow_pos hβ t).ne'
  have h2 : du * q - dv = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h this
    · exact h
  rw [hq] at h2
  linarith

/-- **AKMM, (5.17), p. 140: no arbitrage.** At an optimum with `β > 0`, positive prices and
`u′(cₜ) ≠ 0`, `pₜ = p_{t+1}r_{t+1} + (1 − δ)p_{t+1}`. Proved by investing `ε` more at `t` and
consuming its gross return `1 − δ + r_{t+1}` at `t + 1`. -/
theorem eq_5_17 {u v : ℝ → ℝ} {β δ e k0 : ℝ} {p r w c k l du : ℕ → ℝ}
    (hopt : GrowthOptimal u v β p r w δ e k0 c k l) (hβ : 0 < β) (hp : ∀ t, 0 < p t)
    (hd : ∀ t, HasDerivAt u (du t) (c t)) (t : ℕ) (hdt : du t ≠ 0) :
    p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1) := by
  have h515 := eq_5_15 hopt hp hd t (t + 1)
  obtain ⟨⟨hpos, hl, hk0, hc, hι, hrk, hwl, hW⟩, husum, hmax⟩ := hopt
  have hsum : Summable (fun t => p t * (c t + (k (t + 1) - (1 - δ) * k t))) :=
    (hc.add hι).congr fun t => by ring
  have hsumR : Summable (fun t => p t * (r t * k t + w t * e * l t)) :=
    (hrk.add hwl).congr fun t => by ring
  set R := 1 - δ + r (t + 1) with hR
  have htt : t + 1 ≠ t := by omega
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = t then c t - ε else if n = t + 1 then c (t + 1) + R * ε else c n
  let kk : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then k (t + 1) + ε else k n
  have hxt : ∀ ε, x ε t = c t - ε := fun ε => by simp [x]
  have hxt1 : ∀ ε, x ε (t + 1) = c (t + 1) + R * ε := fun ε => by simp [x]
  have hxo : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hkt1 : ∀ ε, kk ε (t + 1) = k (t + 1) + ε := fun ε => by simp [kk]
  have hko : ∀ ε n, n ≠ t + 1 → kk ε n = k n := fun ε n hn => by simp [kk, hn]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - ε ∧ 0 < c (t + 1) + R * ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - ε :=
      continuousAt_const.eventually_lt (continuous_const.sub continuous_id).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c (t + 1) + R * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos (t + 1))
    exact h1.and h2
  have hd' : HasDerivAt
      (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * (u (x ε n) - v (l n)))
      (β ^ t * (du t * (-1)) + β ^ (t + 1) * (du (t + 1) * R)) 0 := by
    have e : (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * (u (x ε n) - v (l n))) =
        fun ε => β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + R * ε) -
          (β ^ t * v (l t) + β ^ (t + 1) * v (l (t + 1))) := by
      funext ε; rw [Finset.sum_pair htt.symm, hxt, hxt1]; ring
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c t - ε)) (du t * (-1)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - ε) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - 0) := by simpa using hd t
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => u (c (t + 1) + R * ε)) (du (t + 1) * R) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c (t + 1) + R * ε) R 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add (c (t + 1))
      have hu : HasDerivAt u (du (t + 1)) (c (t + 1) + R * 0) := by simpa using hd (t + 1)
      exact hu.comp 0 hin
    exact ((h1.const_mul _).add (h2.const_mul _)).sub_const _
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * (u (c n) - v (l n)))
    (g := fun ε n => β ^ n * (u (x ε n) - v (l n))) {t, t + 1} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      -- the budget series change only at `t + 1`, by `p_{t+1}r_{t+1}ε` on each side
      have hLo : ∀ n ∉ ({t + 1} : Finset ℕ),
          p n * (x ε n + (kk ε (n + 1) - (1 - δ) * kk ε n)) =
            p n * (c n + (k (n + 1) - (1 - δ) * k n)) := by
        intro n hn
        simp only [Finset.mem_singleton] at hn
        by_cases hnt : n = t
        · subst hnt
          rw [hxt, hkt1, hko ε n hn]; ring
        · rw [hxo ε n (by simp [hnt, hn]), hko ε n hn, hko ε (n + 1) (by omega)]
      have hRo : ∀ n ∉ ({t + 1} : Finset ℕ),
          p n * (r n * kk ε n + w n * e * l n) = p n * (r n * k n + w n * e * l n) := by
        intro n hn
        simp only [Finset.mem_singleton] at hn
        rw [hko ε n hn]
      have hS1 := ce_tsum_perturb (f := fun n => p n * (c n + (k (n + 1) - (1 - δ) * k n)))
        (g := fun n => p n * (x ε n + (kk ε (n + 1) - (1 - δ) * kk ε n))) {t + 1} hLo hsum
      have hS2 := ce_tsum_perturb (f := fun n => p n * (r n * k n + w n * e * l n))
        (g := fun n => p n * (r n * kk ε n + w n * e * l n)) {t + 1} hRo hsumR
      have hPc := ce_tsum_perturb (f := fun n => p n * c n) (g := fun n => p n * x ε n)
        {t, t + 1} (fun n hn => by simp only [hxo ε n hn]) hc
      have hPι := ce_tsum_perturb (f := fun n => p n * (k (n + 1) - (1 - δ) * k n))
        (g := fun n => p n * (kk ε (n + 1) - (1 - δ) * kk ε n)) {t, t + 1}
        (fun n hn => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          rw [hko ε n hn.2, hko ε (n + 1) (by omega)]) hι
      have hPr := ce_tsum_perturb (f := fun n => p n * (r n * k n))
        (g := fun n => p n * (r n * kk ε n)) {t + 1}
        (fun n hn => by
          simp only [Finset.mem_singleton] at hn
          rw [hko ε n hn]) hrk
      refine hmax (x ε) (kk ε) l
        ⟨fun n => ?_, hl, by rw [hko ε 0 (by omega), hk0], hPc.1, hPι.1, hPr.1, hwl, ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; rw [hxt]; exact hε.1
        by_cases h2 : n = t + 1
        · subst h2; rw [hxt1]; exact hε.2
        rw [hxo ε n (by simp [h1, h2])]; exact hpos n
      · rw [hS1.2, hS2.2, hW, Finset.sum_singleton, Finset.sum_singleton, hxt1, hkt1,
          hko ε (t + 1 + 1) (by omega), hR]
        ring) hd'
  -- combine with (5.15)
  have hb := (pow_pos hβ t).ne'
  have hpt := (hp t).ne'
  have hpt1 := (hp (t + 1)).ne'
  rw [pow_succ] at hzero h515
  have h1 : β * du (t + 1) * R = du t := by
    apply mul_left_cancel₀ hb; linarith
  have h2 : β * du (t + 1) * p t = du t * p (t + 1) := by
    apply mul_left_cancel₀ hb; linarith
  have h3 : du t * p (t + 1) * R = du t * p t := by
    rw [← h2, ← h1]; ring
  have h4 : p (t + 1) * R = p t := by
    apply mul_left_cancel₀ hdt; linarith
  rw [hR] at h4
  linarith

/-- **AKMM, p. 141: the consolidated budget.** If the household's budget (5.14) holds and
(5.17) holds at every date, then `Σ pₜcₜ = Σ pₜwₜeℓₜ + (1 − δ + r₀)p₀k₀` iff `p_Tk_{T+1} → 0`.
The book substitutes (5.17) without stating this limit condition. -/
theorem growth_consolidated_budget {δ e k0 : ℝ} {p r w c k l : ℕ → ℝ}
    (hb : GrowthBudget p r w δ e k0 c k l)
    (h517 : ∀ t, p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1)) :
    ∑' t, p t * c t = ∑' t, p t * w t * e * l t + (1 - δ + r 0) * p 0 * k0 ↔
      Tendsto (fun T => p T * k (T + 1)) atTop (𝓝 0) := by
  obtain ⟨_, _, hk0, hc, hι, hrk, hwl, hW⟩ := hb
  set D : ℕ → ℝ := fun t => p t * (k (t + 1) - (1 - δ) * k t) - p t * (r t * k t) with hD
  have hDs : Summable D := hι.sub hrk
  have hW' : ∑' t, p t * c t + ∑' t, p t * (k (t + 1) - (1 - δ) * k t) =
      ∑' t, p t * (r t * k t) + ∑' t, p t * w t * e * l t := by
    rw [← hc.tsum_add hι, ← hrk.tsum_add hwl]
    convert hW using 2 <;> funext t <;> ring
  have hDv : ∑' t, D t = ∑' t, p t * w t * e * l t - ∑' t, p t * c t := by
    rw [hD, hι.tsum_sub hrk]
    linarith
  have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), D t =
      p T * k (T + 1) - (1 - δ + r 0) * p 0 * k 0 := by
    intro T
    induction T with
    | zero => simp [hD]; ring
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, hD]
      simp only
      rw [h517 T]
      ring
  have hlim : Tendsto (fun T => p T * k (T + 1)) atTop
      (𝓝 (∑' t, D t + (1 - δ + r 0) * p 0 * k 0)) := by
    have h := (hDs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have e : (fun T => p T * k (T + 1)) =
        fun T => (∑ t ∈ Finset.range (T + 1), D t) + (1 - δ + r 0) * p 0 * k 0 := by
      funext T; rw [hpart T]; ring
    rw [e]
    exact h.add_const _
  rw [hk0] at hlim
  constructor
  · intro h
    have : ∑' t, D t + (1 - δ + r 0) * p 0 * k0 = 0 := by rw [hDv, h]; ring
    rwa [this] at hlim
  · intro h
    have := tendsto_nhds_unique hlim h
    rw [hDv] at this
    linarith

/-- **AKMM, fn. 5, p. 140: no Ponzi scheme in the date-0 budget.** If (5.17) holds at every
date, prices are positive, gross returns `1 − δ + rₜ` are positive and the rental share of the
gross return is bounded below, `ε(1 − δ + rₜ) ≤ rₜ` with `ε > 0`, then every plan in the budget
set has `p_Tk_{T+1} → 0`: convergence of the value of capital income rules out Ponzi
schemes. -/
theorem growth_capital_value_tendsto_zero {δ e k0 ε : ℝ} {p r w c k l : ℕ → ℝ}
    (hb : GrowthBudget p r w δ e k0 c k l)
    (h517 : ∀ t, p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1))
    (hR : ∀ t, 0 < 1 - δ + r t) (hε : 0 < ε) (hrate : ∀ t, ε * (1 - δ + r t) ≤ r t) :
    Tendsto (fun T => p T * k (T + 1)) atTop (𝓝 0) := by
  obtain ⟨_, _, _, _, _, hrk, _, _⟩ := hb
  have hz : Tendsto (fun T => p (T + 1) * (r (T + 1) * k (T + 1))) atTop (𝓝 0) :=
    (hrk.tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
  have hrpos : ∀ t, 0 < r t := fun t => lt_of_lt_of_le (mul_pos hε (hR t)) (hrate t)
  have hbound : ∀ T, ‖p T * k (T + 1)‖ ≤ ε⁻¹ * ‖p (T + 1) * (r (T + 1) * k (T + 1))‖ := by
    intro T
    have e : p T * k (T + 1) =
        p (T + 1) * (r (T + 1) * k (T + 1)) * ((1 - δ + r (T + 1)) / r (T + 1)) := by
      rw [h517 T]; have := (hrpos (T + 1)).ne'; field_simp; ring
    rw [e, norm_mul]
    have h1 : ‖(1 - δ + r (T + 1)) / r (T + 1)‖ ≤ ε⁻¹ := by
      rw [Real.norm_of_nonneg (div_pos (hR _) (hrpos _)).le, div_le_iff₀ (hrpos _)]
      have := hrate (T + 1)
      rw [inv_mul_eq_div, le_div_iff₀ hε]
      linarith
    calc ‖p (T + 1) * (r (T + 1) * k (T + 1))‖ * ‖(1 - δ + r (T + 1)) / r (T + 1)‖
        ≤ ‖p (T + 1) * (r (T + 1) * k (T + 1))‖ * ε⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by ring
  refine squeeze_zero_norm hbound ?_
  have := (hz.norm).const_mul ε⁻¹
  simpa using this

/-- **AKMM, p. 140: the first-order conditions are sufficient.** Let `u` lie below and `v` above
their tangents, `β ≥ 0`, `βᵗu′(cₜ) = λpₜ` (5.15), `v′(ℓₜ) = ewₜu′(cₜ)` (5.16), (5.17)
at every date, positive prices and gross returns with `ε(1 − δ + rₜ) ≤ rₜ`, `ε > 0`. Then a
budget-feasible plan with a convergent utility series solves the household's problem. -/
theorem growth_foc_sufficient {u v : ℝ → ℝ} {β δ e k0 lam ε : ℝ} {p r w c k l du dv : ℕ → ℝ}
    (hβ : 0 ≤ β) (hut : ∀ t x, 0 < x → u x ≤ u (c t) + du t * (x - c t))
    (hvt : ∀ t m, 0 ≤ m → v (l t) + dv t * (m - l t) ≤ v m)
    (h515 : ∀ t, β ^ t * du t = lam * p t) (h516 : ∀ t, dv t = e * w t * du t)
    (h517 : ∀ t, p t = p (t + 1) * r (t + 1) + (1 - δ) * p (t + 1))
    (hR : ∀ t, 0 < 1 - δ + r t) (hε : 0 < ε) (hrate : ∀ t, ε * (1 - δ + r t) ≤ r t)
    (hb : GrowthBudget p r w δ e k0 c k l) (hU : Summable (fun t => β ^ t * (u (c t) - v (l t)))) :
    GrowthOptimal u v β p r w δ e k0 c k l := by
  refine ⟨hb, hU, fun x kk m hx hUx => ?_⟩
  have hcb := (growth_consolidated_budget hb h517).2
    (growth_capital_value_tendsto_zero hb h517 hR hε hrate)
  have hxb := (growth_consolidated_budget hx h517).2
    (growth_capital_value_tendsto_zero hx h517 hR hε hrate)
  obtain ⟨_, _, _, hcs, _, _, hcw, _⟩ := hb
  obtain ⟨hxp, hmp, _, hxs, _, _, hxw, _⟩ := hx
  have key : ∀ t, β ^ t * (u (x t) - v (m t)) ≤ β ^ t * (u (c t) - v (l t)) +
      lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
    intro t
    have h1 := hut t (x t) (hxp t)
    have h2 := hvt t (m t) (hmp t)
    have h3 : β ^ t * (u (x t) - v (m t)) ≤
        β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ t)
    have h4 : β ^ t * ((u (c t) + du t * (x t - c t)) - (v (l t) + dv t * (m t - l t))) =
        β ^ t * (u (c t) - v (l t)) +
          lam * ((p t * x t - p t * c t) - (p t * w t * e * m t - p t * w t * e * l t)) := by
      rw [h516 t]
      have : β ^ t * (du t * (x t - c t) - e * w t * du t * (m t - l t)) =
          (β ^ t * du t) * ((x t - c t) - e * w t * (m t - l t)) := by ring
      linear_combination this + (x t - c t - e * w t * (m t - l t)) * h515 t
    linarith
  have hS2 : Summable (fun t => lam * ((p t * x t - p t * c t) -
      (p t * w t * e * m t - p t * w t * e * l t))) :=
    ((hxs.sub hcs).sub (hxw.sub hcw)).mul_left lam
  have := hUx.tsum_le_tsum key (hU.add hS2)
  rw [hU.tsum_add hS2, tsum_mul_left, ((hxs.sub hcs)).tsum_sub (hxw.sub hcw),
    hxs.tsum_sub hcs, hxw.tsum_sub hcw, hxb, hcb] at this
  linarith

/-- **AKMM, Definition 4: an instance.** With `u = log`, `v(ℓ) = ℓ²/4`, `β = 1/2`, `δ = 1`,
`pₜ = (1/2)ᵗ`, `r = 2`, `w = e = 1` and `k₀ = 1`, the plan `cₜ = 2`, `kₜ = 1`, `ℓₜ = 1` solves
the household's problem. -/
theorem growth_optimal_instance :
    GrowthOptimal Real.log (fun l => l ^ 2 / 4) (1 / 2) (fun t => (1 / 2 : ℝ) ^ t) (fun _ => 2)
      (fun _ => 1) 1 1 1 (fun _ => 2) (fun _ => 1) (fun _ => 1) := by
  have hgeo := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  refine growth_foc_sufficient (du := fun _ => 1 / 2) (dv := fun _ => 1 / 2) (lam := 1 / 2)
    (ε := 1) (by norm_num) (fun t x hx => ?_) (fun t m _ => ?_)
    (fun t => by ring) (fun t => by ring) (fun t => by rw [pow_succ]; ring) (fun t => by norm_num)
    one_pos (fun t => by norm_num) ⟨fun _ => by norm_num, fun _ => by norm_num, rfl, ?_, ?_, ?_,
      ?_, ?_⟩ ?_
  · have := ce_log_tangent (show (0 : ℝ) < 2 by norm_num) hx
    norm_num at this ⊢
    linarith
  · nlinarith [sq_nonneg (m - 1)]
  · exact (hgeo.mul_right 2).congr fun t => by ring
  · exact (hgeo.mul_right 1).congr fun t => by ring
  · exact (hgeo.mul_right 2).congr fun t => by ring
  · exact (hgeo.mul_right 1).congr fun t => by ring
  · congr 1; funext t; ring
  · exact (hgeo.mul_right (Real.log 2 - 1 / 4)).congr fun t => by norm_num

/-- **AKMM, pp. 141–142: log consumption under `k_{i,0} = eᵢK₀` and common hours.** If
`pₜcₜ = βᵗc₀` (the log form of (5.15) with `p₀ = 1`), `0 ≤ β < 1` and the consolidated budget
`Σ pₜcₜ = Σ pₜwₜeℓₜ + (1 − δ + r₀)eK₀` holds with common hours `ℓ`, then
`cₜ = eβᵗ(1 − β)(Σ pₛwₛℓₛ + (1 − δ + r₀)K₀)/pₜ`. -/
theorem growth_log_consumption {β δ e K0 : ℝ} {p r w c l : ℕ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hp : ∀ t, 0 < p t) (hfoc : ∀ t, p t * c t = β ^ t * c 0)
    (hbud : ∑' t, p t * c t = ∑' t, p t * w t * e * l t + (1 - δ + r 0) * (e * K0)) (t : ℕ) :
    c t = e * (β ^ t * (1 - β) / p t * (∑' s, p s * w s * l s + (1 - δ + r 0) * K0)) := by
  have hL : ∑' t, p t * c t = c 0 * (1 - β)⁻¹ := by
    simp only [hfoc]; rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, mul_comm]
  have hR : ∑' t, p t * w t * e * l t = e * ∑' t, p t * w t * l t := by
    rw [← tsum_mul_left]; congr 1; funext s; ring
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hc0 : c 0 = e * ((1 - β) * (∑' s, p s * w s * l s + (1 - δ + r 0) * K0)) := by
    rw [hL, hR] at hbud
    field_simp at hbud
    linarith
  have hct : c t = β ^ t * c 0 / p t := by
    have := hfoc t; have := (hp t).ne'; field_simp; linarith
  rw [hct, hc0]
  have := (hp t).ne'
  field_simp

/-- **AKMM, fn. 6, p. 142.** If `c_{i,t} = eᵢXₜ` with `Xₜ` independent of `i` and
`∫ eᵢ di = 1`, then `Cₜ = ∫ c_{i,t} di = Xₜ`: the consumption share is `θᵢ = eᵢ`. -/
theorem growth_fn6 {μ : Measure I} {e : I → ℝ} {c : I → ℕ → ℝ} {X : ℕ → ℝ}
    (he1 : ∫ i, e i ∂μ = 1) (hc : ∀ i t, c i t = e i * X t) (t : ℕ) :
    ∫ i, c i t ∂μ = X t := by
  simp only [hc, integral_mul_const, he1, one_mul]

/-- **AKMM, p. 142: the hours condition does not depend on `i`.** With log utility, (5.16) reads
`v′(ℓ_{i,t}) = eᵢwₜ/c_{i,t}`; under `c_{i,t} = eᵢβᵗ(1 − β)W/pₜ` with `eᵢ, W > 0` the right
side is `wₜpₜ/(βᵗ(1 − β)W)`, the same for every household. -/
theorem growth_log_hours_common {β e W pt wt : ℝ} {t : ℕ} (he : 0 < e) (hβ : 0 < β)
    (hβ1 : β < 1) (hW : 0 < W) (hpt : 0 < pt) :
    e * wt / (e * (β ^ t * (1 - β) / pt * W)) = wt * pt / (β ^ t * (1 - β) * W) := by
  have : (1 : ℝ) - β ≠ 0 := by linarith
  have := (pow_pos hβ t).ne'
  field_simp

/-- **AKMM, p. 141: the aggregate Euler equation.** If every household satisfies the log
first-order condition `pₜc_{i,t} = βᵗc_{i,0}`, then `pₜCₜ = βᵗC₀` for `Cₜ = ∫ c_{i,t} di`, so
`C_{t+1} = βpₜ/p_{t+1}·Cₜ` when `β > 0`. -/
theorem growth_log_aggregate_euler {μ : Measure I} {β : ℝ} {p : ℕ → ℝ} {c : I → ℕ → ℝ}
    (hβ : 0 < β) (hp : ∀ t, 0 < p t) (hfoc : ∀ i t, p t * c i t = β ^ t * c i 0) (t : ℕ) :
    ∫ i, c i (t + 1) ∂μ = β * p t / p (t + 1) * ∫ i, c i t ∂μ := by
  have hagg : ∀ t, p t * ∫ i, c i t ∂μ = β ^ t * ∫ i, c i 0 ∂μ := by
    intro t
    rw [← integral_const_mul, ← integral_const_mul]
    exact congrArg (fun f => ∫ i, f i ∂μ) (funext fun i => hfoc i t)
  have h1 := hagg t
  have h2 := hagg (t + 1)
  have := (hp t).ne'
  have := (hp (t + 1)).ne'
  have := (pow_pos hβ t).ne'
  rw [pow_succ] at h2
  field_simp
  have e : p (t + 1) * ∫ i, c i (t + 1) ∂μ = β * (p t * ∫ i, c i t ∂μ) := by rw [h2, h1]; ring
  linarith

/-- **AKMM, (5.18), p. 142.** The aggregate Euler equation `C_{t+1} = βpₜ/p_{t+1}·Cₜ`, the
no-arbitrage condition (5.17) and the firm's condition
`r_{t+1} = αA_{t+1}K_{t+1}^{α−1}L_{t+1}^{1−α}` give
`C_{t+1}/Cₜ = β(1 − δ + αA_{t+1}K_{t+1}^{α−1}L_{t+1}^{1−α})`. -/
theorem eq_5_18 {β δ α Ct Ct1 pt pt1 rt1 At1 Kt1 Lt1 : ℝ} (hCt : Ct ≠ 0) (hpt1 : pt1 ≠ 0)
    (heul : Ct1 = β * pt / pt1 * Ct) (h517 : pt = pt1 * rt1 + (1 - δ) * pt1)
    (hr : rt1 = α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α)) :
    Ct1 / Ct = β * (1 - δ + α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α)) := by
  rw [heul, h517, ← hr]
  field_simp
  ring

/-- **AKMM, (5.19), p. 142.** If (5.16) holds with `c_{i,t} = eᵢCₜ` and `eᵢ > 0`,
`v′(Lₜ) = eᵢwₜ/c_{i,t}`, and `wₜ = (1 − α)AₜKₜ^αLₜ^{−α}`, then
`v′(Lₜ) = (1 − α)AₜKₜ^αLₜ^{−α}/Cₜ`. -/
theorem eq_5_19 {α e dv wt Ct At Kt Lt : ℝ} (he : 0 < e) (hC : Ct ≠ 0)
    (h516 : dv = e * wt * (e * Ct)⁻¹) (hw : wt = (1 - α) * At * Kt ^ α * Lt ^ (-α)) :
    dv = (1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct := by
  rw [h516, hw]
  have := he.ne'
  field_simp

/-- **AKMM, (5.20), p. 142.** If goods clear, `∫ (c_{i,t} + ι_{i,t}) di = Yₜ`, with
`ι_{i,t} = k_{i,t+1} − (1 − δ)k_{i,t}` and capital clearing `∫ k_{i,s} di = Kₛ` (integrable
consumption and capital), then `Cₜ = Yₜ + (1 − δ)Kₜ − K_{t+1}`. -/
theorem eq_5_20 {μ : Measure I} {δ Yt : ℝ} {c k : I → ℕ → ℝ} {K : ℕ → ℝ} {t : ℕ}
    (hcint : Integrable (c · t) μ) (hkint : ∀ s, Integrable (k · s) μ)
    (hK : ∀ s, ∫ i, k i s ∂μ = K s)
    (hgoods : ∫ i, (c i t + (k i (t + 1) - (1 - δ) * k i t)) ∂μ = Yt) :
    ∫ i, c i t ∂μ = Yt + (1 - δ) * K t - K (t + 1) := by
  have h1 : Integrable (fun i => k i (t + 1) - (1 - δ) * k i t) μ :=
    (hkint (t + 1)).sub ((hkint t).const_mul _)
  have h2 : Integrable (fun i => (1 - δ) * k i t) μ := (hkint t).const_mul _
  rw [integral_add hcint h1, integral_sub (hkint (t + 1)) h2, integral_const_mul, hK, hK]
    at hgoods
  linarith

/-- **AKMM, fn. 7, p. 142.** With `δ = 1`, constant hours `L` with `v′(L)L = (1 − α)/(1 − αβ)`,
saving `K_{t+1} = αβYₜ` and consumption `Cₜ = (1 − αβ)Yₜ`, where
`Yₜ = AₜKₜ^αL^{1−α}`, the path satisfies (5.18), (5.19) and (5.20): the saving rate is `αβ`
and hours do not depend on time. -/
theorem growth_fn7 {α β Lbar dvL : ℝ} {A K C : ℕ → ℝ} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hαβ : α * β < 1) (hA : ∀ t, 0 < A t) (hK0 : 0 < K 0) (hL : 0 < Lbar)
    (hv : dvL * Lbar = (1 - α) / (1 - α * β))
    (hsave : ∀ t, K (t + 1) = α * β * (A t * K t ^ α * Lbar ^ (1 - α)))
    (hcons : ∀ t, C t = (1 - α * β) * (A t * K t ^ α * Lbar ^ (1 - α))) :
    (∀ t, C (t + 1) / C t =
        β * (1 - 1 + α * A (t + 1) * K (t + 1) ^ (α - 1) * Lbar ^ (1 - α))) ∧
      (∀ t, dvL = (1 - α) * A t * K t ^ α * Lbar ^ (-α) / C t) ∧
      ∀ t, C t = A t * K t ^ α * Lbar ^ (1 - α) + (1 - 1) * K t - K (t + 1) := by
  have hKpos : ∀ t, 0 < K t := by
    intro t
    induction t with
    | zero => exact hK0
    | succ t ih =>
      rw [hsave]
      exact mul_pos (mul_pos hα0 hβ0) (mul_pos (mul_pos (hA t) (Real.rpow_pos_of_pos ih _))
        (Real.rpow_pos_of_pos hL _))
  have h1 : 0 < 1 - α * β := by linarith
  have hY : ∀ t, 0 < A t * K t ^ α * Lbar ^ (1 - α) := fun t =>
    mul_pos (mul_pos (hA t) (Real.rpow_pos_of_pos (hKpos t) _)) (Real.rpow_pos_of_pos hL _)
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · have hKa : K (t + 1) ^ (α - 1) = K (t + 1) ^ α / K (t + 1) :=
      Real.rpow_sub_one (hKpos (t + 1)).ne' α
    have hZ : C (t + 1) / C t =
        A (t + 1) * K (t + 1) ^ α * Lbar ^ (1 - α) / (A t * K t ^ α * Lbar ^ (1 - α)) := by
      rw [hcons, hcons]; have := h1.ne'; field_simp
    have e : β * (1 - 1 + α * A (t + 1) * K (t + 1) ^ (α - 1) * Lbar ^ (1 - α)) =
        A (t + 1) * K (t + 1) ^ α * Lbar ^ (1 - α) * (α * β / K (t + 1)) := by
      rw [hKa]; ring
    have hq : α * β / K (t + 1) = 1 / (A t * K t ^ α * Lbar ^ (1 - α)) := by
      rw [hsave t]; have := (hY t).ne'; have := hα0.ne'; have := hβ0.ne'; field_simp
    rw [e, hZ, hq]
    ring
  · rw [hcons]
    have hLa : Lbar ^ (-α) = Lbar ^ (1 - α) / Lbar := by
      rw [show -α = (1 - α) - 1 by ring, Real.rpow_sub_one hL.ne']
    rw [hLa]
    have hd : dvL = (1 - α) / (1 - α * β) / Lbar := by
      field_simp; field_simp at hv; linarith
    rw [hd]
    have := (Real.rpow_pos_of_pos (hKpos t) α).ne'
    have := (Real.rpow_pos_of_pos hL (1 - α)).ne'
    have := (hA t).ne'
    have := h1.ne'
    field_simp
  · rw [hcons, hsave]; ring

/-- The algebra of the planner's condition: for `a, b ≠ 0`,
`−1/a + β(x/b) = 0 ↔ b/a = βx`. -/
theorem ce_planner_iff {a b β x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    -1 / a + β * (x / b) = 0 ↔ b / a = β * x := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [div_eq_iff ha] at h
    field_simp
    linarith

/-- **AKMM, p. 142: the planner's first-order condition in `K_{t+1}`.** The terms of
`Σ βᵗ[log Cₜ − v(Lₜ)]` that depend on `K_{t+1} = k`, after substituting (5.20), are
`log(AₜKₜ^αLₜ^{1−α} + (1 − δ)Kₜ − k) + β log(A_{t+1}k^αL_{t+1}^{1−α} + (1 − δ)k − K_{t+2})`;
at `k = K_{t+1} > 0` with positive consumptions `Cₜ, C_{t+1}` their derivative is
`−1/Cₜ + β(αA_{t+1}K_{t+1}^{α−1}L_{t+1}^{1−α} + 1 − δ)/C_{t+1}`, and it vanishes iff (5.18). -/
theorem growth_planner_foc_K {α β δ At Kt Lt At1 Kt1 Lt1 Kt2 Ct Ct1 : ℝ} (hK1 : 0 < Kt1)
    (hCdef : Ct = At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - Kt1)
    (hC1def : Ct1 = At1 * Kt1 ^ α * Lt1 ^ (1 - α) + (1 - δ) * Kt1 - Kt2)
    (hCt : 0 < Ct) (hCt1 : 0 < Ct1) :
    HasDerivAt (fun k => Real.log (At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - k) +
        β * Real.log (At1 * k ^ α * Lt1 ^ (1 - α) + (1 - δ) * k - Kt2))
      (-1 / Ct + β * ((α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α) + (1 - δ)) / Ct1)) Kt1 ∧
    (-1 / Ct + β * ((α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α) + (1 - δ)) / Ct1) = 0 ↔
      Ct1 / Ct = β * (1 - δ + α * At1 * Kt1 ^ (α - 1) * Lt1 ^ (1 - α))) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun k => At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - k) (-1) Kt1 := by
      simpa using (hasDerivAt_id Kt1).const_sub (At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt)
    have h2 : HasDerivAt (fun k => At1 * k ^ α * Lt1 ^ (1 - α) + (1 - δ) * k - Kt2)
        (At1 * (α * Kt1 ^ (α - 1)) * Lt1 ^ (1 - α) + (1 - δ) * 1) Kt1 := by
      exact ((((Real.hasDerivAt_rpow_const (Or.inl hK1.ne')).const_mul At1).mul_const _).add
        ((hasDerivAt_id Kt1).const_mul (1 - δ))).sub_const Kt2
    rw [hCdef] at hCt
    rw [hC1def] at hCt1
    have := ((Real.hasDerivAt_log hCt.ne').comp Kt1 h1).add
      (((Real.hasDerivAt_log hCt1.ne').comp Kt1 h2).const_mul β)
    rw [hCdef, hC1def]
    convert this using 1 <;> first | rfl | ring
  · rw [ce_planner_iff hCt.ne' hCt1.ne']
    constructor <;> intro h <;> linear_combination h

/-- **AKMM, p. 142: the planner's first-order condition in `Lₜ`.** The terms of the planner's
objective that depend on `Lₜ = L` are `log(AₜKₜ^αL^{1−α} + (1 − δ)Kₜ − K_{t+1}) − v(L)`; at
`L = Lₜ > 0` with positive consumption `Cₜ` their derivative is
`(1 − α)AₜKₜ^αLₜ^{−α}/Cₜ − v′(Lₜ)`, and it vanishes iff (5.19). -/
theorem growth_planner_foc_L {v : ℝ → ℝ} {α δ At Kt Lt Kt1 dv Ct : ℝ} (hL : 0 < Lt)
    (hCdef : Ct = At * Kt ^ α * Lt ^ (1 - α) + (1 - δ) * Kt - Kt1) (hC : 0 < Ct)
    (hdv : HasDerivAt v dv Lt) :
    HasDerivAt (fun L => Real.log (At * Kt ^ α * L ^ (1 - α) + (1 - δ) * Kt - Kt1) - v L)
      ((1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct - dv) Lt ∧
    ((1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct - dv = 0 ↔
      dv = (1 - α) * At * Kt ^ α * Lt ^ (-α) / Ct) := by
  refine ⟨?_, sub_eq_zero.trans eq_comm⟩
  have h1 : HasDerivAt (fun L => At * Kt ^ α * L ^ (1 - α) + (1 - δ) * Kt - Kt1)
      (At * Kt ^ α * ((1 - α) * Lt ^ (1 - α - 1))) Lt :=
    (((Real.hasDerivAt_rpow_const (Or.inl hL.ne')).const_mul (At * Kt ^ α)).add_const
      _).sub_const _
  rw [hCdef] at hC
  have := ((Real.hasDerivAt_log hC.ne').comp Lt h1).sub hdv
  rw [show (1 : ℝ) - α - 1 = -α by ring] at this
  rw [hCdef]
  convert this using 1 <;> first | rfl | ring

end AKMM.CompetitiveEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequential equilibrium

AKMM, §5.3, pp. 143–146. Consumers trade one asset period by period: `c_{i,t} + qₜa_{i,t+1} =
a_{i,t} + y_{i,t}`, subject to the no-Ponzi-game condition
`lim (∏_{s ≤ t} q_s) a_{i,t+1} ≥ 0`.

* Definition 5 (`SeqBudget`, `SeqOptimal`, `IsSeqEquilibrium`). The nPg condition is stated as
  `liminf ≥ 0` (for every `ε > 0`, eventually `≥ −ε`), since the book's limit need not exist.
* Walras's law (p. 144 and fn. 10): with `∫ a_{i,0} di = 0`, goods clearing at every date is
  equivalent to asset clearing at every date (`seq_walras`).
* (5.21)–(5.22): `qₜu′(cₜ) = βu′(c_{t+1})` is necessary (`eq_5_21_5_22`), so
  `∏_{s<t} q_s = βᵗu′(cₜ)/u′(c₀)`, the Arrow–Debreu price (5.3) (`seq_price_product`), and
  `p_{t−1}/pₜ = 1/q_{t−1}` (`seq_gross_rate`).
* The budgets (p. 145): after `T` substitutions
  `Σ_{t≤T} pₜcₜ + p_{T+1}a_{T+1} = a₀ + Σ_{t≤T} pₜyₜ` (`seq_budget_iterate`); the book prints the
  factor of `a_{T+1}` as `∏_{s=0}^{T−1} q_s`, which is wrong
  (`seq_budget_iterate_printed_counterexample`). With nPg the lifetime budget
  `Σ pₜcₜ ≤ a₀ + Σ pₜyₜ` follows (`seq_lifetime_budget`), with equality iff
  `p_{T+1}a_{T+1} → 0` (`seq_lifetime_budget_eq_iff`); conversely every plan meeting the
  lifetime budget with equality is financed by a sequence of asset holdings satisfying nPg
  (`seq_of_lifetime_budget`).
* Equivalence (p. 145): with strictly increasing `u`, a plan solves the sequential problem iff it
  solves the date-0 problem at `pₜ = ∏_{s<t} q_s` with wealth `a₀ + Σ pₜyₜ`
  (`seq_optimal_iff_ad`); hence a sequential equilibrium with `a_{i,0} = 0` is an Arrow–Debreu
  equilibrium (`seq_equilibrium_is_ad`). An instance of Definition 5
  (`seq_equilibrium_instance`).
* Definition 6 and Walras's law in the growth economy (p. 146): for a constant-returns
  technology Euler's theorem `F(K, L) = F_K K + F_L L` holds (`euler_crs`), so the consumers'
  budgets and the firm's conditions imply the resource constraint (`seq_growth_walras`).

Departures: consumption positive; the utility series of the plans compared converge.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-- The Arrow–Debreu price implied by sequential prices: `pₜ = ∏_{s<t} q_s`. -/
noncomputable def seqPrice (q : ℕ → ℝ) (t : ℕ) : ℝ := ∏ s ∈ Finset.range t, q s

/-- `p_{t+1} = pₜqₜ`. -/
theorem seqPrice_succ (q : ℕ → ℝ) (t : ℕ) : seqPrice q (t + 1) = seqPrice q t * q t := by
  simp [seqPrice, Finset.prod_range_succ]

/-- Positive one-period prices give positive Arrow–Debreu prices. -/
theorem seqPrice_pos {q : ℕ → ℝ} (hq : ∀ t, 0 < q t) (t : ℕ) : 0 < seqPrice q t :=
  Finset.prod_pos fun s _ => hq s

/-- The no-Ponzi-game condition of Definition 5 (AKMM, p. 144), as `liminf ≥ 0`:
for every `ε > 0`, eventually `(∏_{s≤t} q_s)a_{t+1} ≥ −ε`. -/
def NoPonzi (q a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in atTop, -ε ≤ seqPrice q (t + 1) * a (t + 1)

/-- AKMM, Definition 5, p. 144: the sequential budget set: positive consumption, `a₀` given,
`cₜ + qₜa_{t+1} = aₜ + yₜ` for all `t`, and nPg. -/
def SeqBudget (q y : ℕ → ℝ) (a0 : ℝ) (c a : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ a 0 = a0 ∧ (∀ t, c t + q t * a (t + 1) = a t + y t) ∧ NoPonzi q a

/-- AKMM, Definition 5, part 1, p. 144: `(c, a)` solves the sequential problem, among plans
with a convergent utility series. -/
def SeqOptimal (u : ℝ → ℝ) (β : ℝ) (q y : ℕ → ℝ) (a0 : ℝ) (c a : ℕ → ℝ) : Prop :=
  SeqBudget q y a0 c a ∧ Summable (fun t => β ^ t * u (c t)) ∧
    ∀ x b, SeqBudget q y a0 x b → Summable (fun t => β ^ t * u (x t)) →
      ∑' t, β ^ t * u (x t) ≤ ∑' t, β ^ t * u (c t)

/-- **AKMM, Definition 5, p. 143.** A sequential competitive equilibrium: each consumer solves
the sequential problem from `a_{i,0}`, and goods and assets clear at every date. -/
def IsSeqEquilibrium (μ : Measure I) (u : ℝ → ℝ) (β : ℝ) (y : I → ℕ → ℝ) (a0 : I → ℝ)
    (c a : I → ℕ → ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ i, SeqOptimal u β q (y i) (a0 i) (c i) (a i)) ∧ (∀ t, ∫ i, c i t ∂μ = ∫ i, y i t ∂μ) ∧
    ∀ t, ∫ i, a i (t + 1) ∂μ = 0

/-- **AKMM, p. 144 and fn. 10: Walras's law.** Suppose every consumer's period budgets hold,
consumption, endowments and assets are integrable at every date, `∫ a_{i,0} di = 0` and
`qₜ ≠ 0`. Then goods clear at every date iff assets clear at every date. -/
theorem seq_walras {μ : Measure I} {q : ℕ → ℝ} {y c a : I → ℕ → ℝ}
    (hb : ∀ i t, c i t + q t * a i (t + 1) = a i t + y i t)
    (hc : ∀ t, Integrable (c · t) μ) (hy : ∀ t, Integrable (y · t) μ)
    (ha : ∀ t, Integrable (a · t) μ) (ha0 : ∫ i, a i 0 ∂μ = 0) (hq : ∀ t, q t ≠ 0) :
    (∀ t, ∫ i, c i t ∂μ = ∫ i, y i t ∂μ) ↔ ∀ t, ∫ i, a i (t + 1) ∂μ = 0 := by
  have hagg : ∀ t, ∫ i, c i t ∂μ + q t * ∫ i, a i (t + 1) ∂μ =
      ∫ i, a i t ∂μ + ∫ i, y i t ∂μ := by
    intro t
    rw [← integral_const_mul, ← integral_add (hc t) ((ha (t + 1)).const_mul _),
      ← integral_add (ha t) (hy t)]
    exact congrArg (fun f => ∫ i, f i ∂μ) (funext fun i => hb i t)
  constructor
  · intro hg t
    induction t with
    | zero =>
      have h := hagg 0
      rw [ha0, hg 0] at h
      have : q 0 * ∫ i, a i (0 + 1) ∂μ = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hq 0)
    | succ t ih =>
      have h := hagg (t + 1)
      rw [ih, hg (t + 1)] at h
      have : q (t + 1) * ∫ i, a i (t + 1 + 1) ∂μ = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hq (t + 1))
  · intro hA t
    have h := hagg t
    rw [hA t] at h
    rcases t with _ | t
    · rw [ha0] at h; linarith
    · rw [hA t] at h; linarith

/-- **AKMM, (5.21)–(5.22), p. 144.** At a sequential optimum with `β > 0`, positive prices and
derivatives `u′(cₜ)`, `qₜu′(cₜ) = βu′(c_{t+1})`. Proved by saving `ε` more at `t` and consuming
it at `t + 1`. -/
theorem eq_5_21_5_22 {u : ℝ → ℝ} {β a0 : ℝ} {q y c a du : ℕ → ℝ}
    (hopt : SeqOptimal u β q y a0 c a) (hβ : 0 < β) (hd : ∀ t, HasDerivAt u (du t) (c t))
    (t : ℕ) : q t * du t = β * du (t + 1) := by
  obtain ⟨⟨hpos, ha0, hb, hnpg⟩, husum, hmax⟩ := hopt
  have htt : t + 1 ≠ t := by omega
  let x : ℝ → ℕ → ℝ := fun ε n =>
    if n = t then c t - q t * ε else if n = t + 1 then c (t + 1) + ε else c n
  let b : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then a (t + 1) + ε else a n
  have hxt : ∀ ε, x ε t = c t - q t * ε := fun ε => by simp [x]
  have hxt1 : ∀ ε, x ε (t + 1) = c (t + 1) + ε := fun ε => by simp [x]
  have hxo : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), x ε n = c n := fun ε n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [x, hn.1, hn.2]
  have hbo : ∀ ε n, n ≠ t + 1 → b ε n = a n := fun ε n hn => by simp [b, hn]
  have hbt1 : ∀ ε, b ε (t + 1) = a (t + 1) + ε := fun ε => by simp [b]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - q t * ε ∧ 0 < c (t + 1) + ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - q t * ε :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (by simpa using hpos t)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c (t + 1) + ε :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using hpos (t + 1))
    exact h1.and h2
  have hd' : HasDerivAt (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * u (x ε n))
      (β ^ t * (du t * (-q t)) + β ^ (t + 1) * du (t + 1)) 0 := by
    have e : (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), β ^ n * u (x ε n)) =
        fun ε => β ^ t * u (c t - q t * ε) + β ^ (t + 1) * u (c (t + 1) + ε) := by
      funext ε; rw [Finset.sum_pair htt.symm, hxt, hxt1]
    rw [e]
    have h1 : HasDerivAt (fun ε => u (c t - q t * ε)) (du t * (-q t)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => c t - q t * ε) (-q t) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (q t)).const_sub (c t)
      have hu : HasDerivAt u (du t) (c t - q t * 0) := by simpa using hd t
      exact hu.comp 0 hin
    have h2 : HasDerivAt (fun ε => u (c (t + 1) + ε)) (du (t + 1)) 0 := by
      have hu : HasDerivAt u (du (t + 1)) (c (t + 1) + 0) := by simpa using hd (t + 1)
      simpa using hu.comp_const_add (c (t + 1)) 0
    exact (h1.const_mul _).add (h2.const_mul _)
  have hzero := ce_foc_of_perturb (f := fun n => β ^ n * u (c n))
    (g := fun ε n => β ^ n * u (x ε n)) {t, t + 1} husum
    (fun ε n hn => by simp only [hxo ε n hn]) (fun n => by simp [x]; split_ifs <;> simp_all)
    (by
      filter_upwards [hev] with ε hε
      intro hU
      refine hmax (x ε) (b ε) ⟨fun n => ?_, by rw [hbo ε 0 (by omega), ha0], fun n => ?_,
        fun η hη => ?_⟩ hU
      · by_cases h1 : n = t
        · subst h1; rw [hxt]; exact hε.1
        by_cases h2 : n = t + 1
        · subst h2; rw [hxt1]; exact hε.2
        rw [hxo ε n (by simp [h1, h2])]; exact hpos n
      · by_cases h1 : n = t
        · rw [h1, hxt, hbt1, hbo ε t (by omega)]
          have := hb t; linarith
        by_cases h2 : n = t + 1
        · rw [h2, hxt1, hbt1, hbo ε (t + 1 + 1) (by omega)]
          have := hb (t + 1); linarith
        rw [hxo ε n (by simp [h1, h2]), hbo ε (n + 1) (by omega), hbo ε n h2]
        exact hb n
      · filter_upwards [hnpg η hη, eventually_gt_atTop t] with s hs hst
        rw [hbo ε (s + 1) (by omega)]
        exact hs) hd'
  have hb' := (pow_pos hβ t).ne'
  rw [pow_succ] at hzero
  have : β ^ t * (β * du (t + 1) - q t * du t) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hb'
  · linarith

/-- **AKMM, p. 145: sequential prices compound to Arrow–Debreu prices.** If
`qₜu′(cₜ) = βu′(c_{t+1})` at every date and `u′(cₜ) ≠ 0`, then
`∏_{s<t} q_s = βᵗu′(cₜ)/u′(c₀)`, the price (5.3). -/
theorem seq_price_product {β : ℝ} {q du : ℕ → ℝ} (heul : ∀ t, q t * du t = β * du (t + 1))
    (hdu : ∀ t, du t ≠ 0) (t : ℕ) : seqPrice q t = β ^ t * du t / du 0 := by
  induction t with
  | zero => simp [seqPrice, hdu 0]
  | succ t ih =>
    rw [seqPrice_succ, ih]
    have h := heul t
    have := hdu t
    have := hdu 0
    field_simp
    rw [pow_succ]
    linear_combination β ^ t * h

/-- **AKMM, p. 145: the gross interest rate.** `pₜ/p_{t+1} = 1/qₜ`. -/
theorem seq_gross_rate {q : ℕ → ℝ} (hq : ∀ t, 0 < q t) (t : ℕ) :
    seqPrice q t / seqPrice q (t + 1) = 1 / q t := by
  rw [seqPrice_succ]
  have := (seqPrice_pos hq t).ne'
  have := (hq t).ne'
  field_simp

/-- **AKMM, p. 145: the iterated budget.** If `cₜ + qₜa_{t+1} = aₜ + yₜ` at every date then for
every `T`, `Σ_{t≤T} pₜcₜ + p_{T+1}a_{T+1} = a₀ + Σ_{t≤T} pₜyₜ`, with `pₜ = ∏_{s<t} q_s`; the
factor of `a_{T+1}` is `∏_{s≤T} q_s`. -/
theorem seq_budget_iterate {q y c a : ℕ → ℝ} (hb : ∀ t, c t + q t * a (t + 1) = a t + y t)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t + seqPrice q (T + 1) * a (T + 1) =
      a 0 + ∑ t ∈ Finset.range (T + 1), seqPrice q t * y t := by
  induction T with
  | zero => simp [seqPrice, hb 0]
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => seqPrice q t * c t) (T + 1),
      Finset.sum_range_succ (fun t => seqPrice q t * y t) (T + 1), seqPrice_succ q (T + 1)]
    have h := hb (T + 1)
    linear_combination ih + seqPrice q (T + 1) * h

/-- **AKMM, p. 145: the printed iterated budget is wrong.** The book's display multiplies
`a_{T+1}` by `∏_{s=0}^{T−1} q_s`. At `T = 0` it reads `c₀ + a₁ = a₀ + y₀`, which fails for the
budget-feasible `q₀ = 1/2`, `a₀ = 0`, `y₀ = 2`, `c₀ = 1`, `a₁ = 2`. -/
theorem seq_budget_iterate_printed_counterexample :
    let q : ℕ → ℝ := fun _ => 1 / 2
    let y : ℕ → ℝ := fun _ => 2
    let c : ℕ → ℝ := fun _ => 1
    let a : ℕ → ℝ := fun t => if t = 0 then 0 else 2
    c 0 + q 0 * a 1 = a 0 + y 0 ∧
      ∑ t ∈ Finset.range (0 + 1), seqPrice q t * c t + seqPrice q 0 * a (0 + 1) ≠
        a 0 + ∑ t ∈ Finset.range (0 + 1), seqPrice q t * y t := by
  intro q y c a
  refine ⟨by norm_num [q, y, c, a], ?_⟩
  norm_num [q, y, c, a, seqPrice]

/-- **AKMM, p. 145: the lifetime budget.** If the sequential budget (with nPg) holds, prices
`qₜ` are positive and `Σ pₜyₜ` converges, then `Σ pₜcₜ` converges and
`Σ pₜcₜ ≤ a₀ + Σ pₜyₜ`. -/
theorem seq_lifetime_budget {q y c a : ℕ → ℝ} {a0 : ℝ} (hb : SeqBudget q y a0 c a)
    (hq : ∀ t, 0 < q t) (hy : Summable (fun t => seqPrice q t * y t)) :
    Summable (fun t => seqPrice q t * c t) ∧
      ∑' t, seqPrice q t * c t ≤ a0 + ∑' t, seqPrice q t * y t := by
  obtain ⟨hpos, ha0, hbud, hnpg⟩ := hb
  have hit := seq_budget_iterate hbud
  have hnn : ∀ t, 0 ≤ seqPrice q t * c t := fun t =>
    (mul_pos (seqPrice_pos hq t) (hpos t)).le
  -- the partial sums of `pₜyₜ` converge, so the partial sums of `pₜcₜ` are bounded
  have hyT := (hy.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hbound : ∀ ε > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t ≤
      a0 + ∑' t, seqPrice q t * y t + 2 * ε := by
    intro ε hε
    have h1 := hyT.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [h1, hnpg ε hε] with T hT hP
    have h2 := hit T
    rw [ha0] at h2
    simp only [Function.comp_apply, Real.dist_eq] at hT
    have := (abs_lt.1 hT).2
    linarith
  -- a uniform bound on all partial sums
  obtain ⟨T0, hT0⟩ := (hbound 1 one_pos).exists_forall_of_atTop
  have hsum : Summable (fun t => seqPrice q t * c t) := by
    refine summable_of_sum_range_le hnn (c := a0 + ∑' t, seqPrice q t * y t + 2 * 1) ?_
    intro n
    calc ∑ t ∈ Finset.range n, seqPrice q t * c t
        ≤ ∑ t ∈ Finset.range (max n T0 + 1), seqPrice q t * c t :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (by omega)) (fun t _ _ => hnn t)
      _ ≤ _ := hT0 _ (le_max_right _ _)
  refine ⟨hsum, ?_⟩
  have hcT := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hle : ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t ≤
      a0 + ∑' t, seqPrice q t * y t + 2 * (ε / 2) := hbound (ε / 2) (by linarith)
  have := le_of_tendsto hcT hle
  linarith

/-- **AKMM, p. 145: equality in the lifetime budget.** Under the hypotheses of
`seq_lifetime_budget`, `Σ pₜcₜ = a₀ + Σ pₜyₜ` iff `p_{T+1}a_{T+1} → 0`. -/
theorem seq_lifetime_budget_eq_iff {q y c a : ℕ → ℝ} {a0 : ℝ} (hb : SeqBudget q y a0 c a)
    (hq : ∀ t, 0 < q t) (hy : Summable (fun t => seqPrice q t * y t)) :
    ∑' t, seqPrice q t * c t = a0 + ∑' t, seqPrice q t * y t ↔
      Tendsto (fun T => seqPrice q (T + 1) * a (T + 1)) atTop (𝓝 0) := by
  have hc := (seq_lifetime_budget hb hq hy).1
  obtain ⟨_, ha0, hbud, _⟩ := hb
  have hlim : Tendsto (fun T => seqPrice q (T + 1) * a (T + 1)) atTop
      (𝓝 (a0 + ∑' t, seqPrice q t * y t - ∑' t, seqPrice q t * c t)) := by
    have hyT := (hy.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hcT := (hc.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have e : (fun T => seqPrice q (T + 1) * a (T + 1)) = fun T =>
        a0 + (∑ t ∈ Finset.range (T + 1), seqPrice q t * y t) -
          ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t := by
      funext T; have := seq_budget_iterate hbud T; rw [ha0] at this; linarith
    rw [e]
    exact (hyT.const_add a0).sub hcT
  constructor
  · intro h; rw [h, sub_self] at hlim; exact hlim
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith

/-- The asset holdings that finance a consumption plan: `a₀` given and
`a_{t+1} = (aₜ + yₜ − cₜ)/qₜ`. -/
noncomputable def seqAssets (q y c : ℕ → ℝ) (a0 : ℝ) : ℕ → ℝ
  | 0 => a0
  | t + 1 => (seqAssets q y c a0 t + y t - c t) / q t

/-- **AKMM, p. 145: the converse.** If prices are positive, `Σ pₜyₜ` and `Σ pₜcₜ` converge,
`c > 0` and `Σ pₜcₜ = a₀ + Σ pₜyₜ`, then the assets `seqAssets` satisfy the period budgets and
`p_{T+1}a_{T+1} → 0`, so nPg: `c` is sequentially feasible. -/
theorem seq_of_lifetime_budget {q y c : ℕ → ℝ} {a0 : ℝ} (hq : ∀ t, 0 < q t) (hc0 : ∀ t, 0 < c t)
    (hy : Summable (fun t => seqPrice q t * y t)) (hc : Summable (fun t => seqPrice q t * c t))
    (hbud : ∑' t, seqPrice q t * c t = a0 + ∑' t, seqPrice q t * y t) :
    SeqBudget q y a0 c (seqAssets q y c a0) ∧
      Tendsto (fun T => seqPrice q (T + 1) * seqAssets q y c a0 (T + 1)) atTop (𝓝 0) := by
  have hb : ∀ t, c t + q t * seqAssets q y c a0 (t + 1) = seqAssets q y c a0 t + y t := by
    intro t
    simp only [seqAssets]
    have := (hq t).ne'
    field_simp
    ring
  have hlim : Tendsto (fun T => seqPrice q (T + 1) * seqAssets q y c a0 (T + 1)) atTop (𝓝 0) := by
    have hyT := (hy.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hcT := (hc.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have e : (fun T => seqPrice q (T + 1) * seqAssets q y c a0 (T + 1)) = fun T =>
        a0 + (∑ t ∈ Finset.range (T + 1), seqPrice q t * y t) -
          ∑ t ∈ Finset.range (T + 1), seqPrice q t * c t := by
      funext T
      have := seq_budget_iterate hb T
      simp only [seqAssets] at this ⊢
      linarith
    rw [e]
    have := (hyT.const_add a0).sub hcT
    rwa [← hbud, sub_self] at this
  refine ⟨⟨hc0, rfl, hb, fun ε hε => ?_⟩, hlim⟩
  filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : -ε < 0))] with T hT
  exact hT.le

/-- **AKMM, p. 145: the sequential and date-0 problems are equivalent.** Let `u` be strictly
increasing on `(0, ∞)`, prices `qₜ > 0`, `Σ pₜyₜ` convergent with `pₜ = ∏_{s<t} q_s`. Then a
consumption plan `c` solves the sequential problem (with some asset holdings) iff it solves the
date-0 problem with wealth `a₀ + Σ pₜyₜ`. -/
theorem seq_optimal_iff_ad {u : ℝ → ℝ} {β a0 : ℝ} {q y c : ℕ → ℝ}
    (hu : StrictMonoOn u (Set.Ioi 0)) (hq : ∀ t, 0 < q t)
    (hy : Summable (fun t => seqPrice q t * y t)) :
    (∃ a, SeqOptimal u β q y a0 c a) ↔
      ADOptimal u β (seqPrice q) (a0 + ∑' t, seqPrice q t * y t) c := by
  set W := a0 + ∑' t, seqPrice q t * y t with hW
  have hp := seqPrice_pos hq
  -- raising consumption at date 0 to exhaust a budget slack raises utility
  have hraise : ∀ x : ℕ → ℝ, (∀ t, 0 < x t) → Summable (fun t => seqPrice q t * x t) →
      Summable (fun t => β ^ t * u (x t)) → ∑' t, seqPrice q t * x t ≤ W →
      ∃ x' : ℕ → ℝ, ADBudget (seqPrice q) W x' ∧ Summable (fun t => β ^ t * u (x' t)) ∧
        ∑' t, β ^ t * u (x t) ≤ ∑' t, β ^ t * u (x' t) ∧
        (∑' t, seqPrice q t * x t < W → ∑' t, β ^ t * u (x t) < ∑' t, β ^ t * u (x' t)) := by
    intro x hx hxs hxu hle
    set sl := W - ∑' t, seqPrice q t * x t with hsl
    have hsl0 : 0 ≤ sl := by linarith
    let x' : ℕ → ℝ := fun n => if n = 0 then x 0 + sl else x n
    have hxo : ∀ n ∉ ({0} : Finset ℕ), x' n = x n := fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [x', hn]
    have hB := ce_tsum_perturb (f := fun n => seqPrice q n * x n)
      (g := fun n => seqPrice q n * x' n) {0} (fun n hn => by simp only [hxo n hn]) hxs
    have hU := ce_tsum_perturb (f := fun n => β ^ n * u (x n))
      (g := fun n => β ^ n * u (x' n)) {0} (fun n hn => by simp only [hxo n hn]) hxu
    have hx'0 : x' 0 = x 0 + sl := by simp [x']
    refine ⟨x', ⟨fun n => ?_, hB.1, ?_⟩, hU.1, ?_, fun hlt => ?_⟩
    · by_cases h : n = 0
      · subst h; rw [hx'0]; linarith [hx 0]
      · rw [hxo n (by simp [h])]; exact hx n
    · rw [hB.2, Finset.sum_singleton, hx'0]; simp [seqPrice, hsl]
    · rw [hU.2, Finset.sum_singleton, hx'0]
      have := hu.monotoneOn (hx 0) (show (0 : ℝ) < x 0 + sl by linarith [hx 0])
        (by linarith : x 0 ≤ x 0 + sl)
      simp only [pow_zero, one_mul]
      linarith
    · rw [hU.2, Finset.sum_singleton, hx'0]
      have hpos : 0 < sl := by linarith
      have := hu (hx 0) (show (0 : ℝ) < x 0 + sl by linarith [hx 0])
        (by linarith : x 0 < x 0 + sl)
      simp only [pow_zero, one_mul]
      linarith
  constructor
  · rintro ⟨a, hb, hU, hmax⟩
    obtain ⟨hcs, hcle⟩ := seq_lifetime_budget hb hq hy
    -- the budget binds
    have hbind : ∑' t, seqPrice q t * c t = W := by
      by_contra hne
      have hlt : ∑' t, seqPrice q t * c t < W := lt_of_le_of_ne hcle hne
      obtain ⟨x', hx'b, hx'u, -, hstrict⟩ := hraise c hb.1 hcs hU hcle
      obtain ⟨hsb, -⟩ := seq_of_lifetime_budget hq hx'b.1 hy hx'b.2.1 hx'b.2.2
      have := hmax x' _ hsb hx'u
      linarith [hstrict hlt]
    refine ⟨⟨hb.1, hcs, hbind⟩, hU, fun x hx hxu => ?_⟩
    exact hmax x _ (seq_of_lifetime_budget hq hx.1 hy hx.2.1 hx.2.2).1 hxu
  · rintro ⟨hb, hU, hmax⟩
    refine ⟨seqAssets q y c a0, (seq_of_lifetime_budget hq hb.1 hy hb.2.1 hb.2.2).1, hU,
      fun x b hxb hxu => ?_⟩
    obtain ⟨hxs, hxle⟩ := seq_lifetime_budget hxb hq hy
    obtain ⟨x', hx'b, hx'u, hle, -⟩ := hraise x hxb.1 hxs hxu hxle
    exact hle.trans (hmax x' hx'b hx'u)

/-- **AKMM, p. 145: a sequential equilibrium is an Arrow–Debreu equilibrium.** With `u`
strictly increasing on `(0, ∞)`, positive `qₜ`, no initial assets (`a_{i,0} = 0`) and
convergent `Σ pₜy_{i,t}`, the consumption of a sequential equilibrium is an Arrow–Debreu
equilibrium (Definition 1) at `pₜ = ∏_{s<t} q_s`. -/
theorem seq_equilibrium_is_ad {μ : Measure I} {u : ℝ → ℝ} {β : ℝ} {y c a : I → ℕ → ℝ}
    {q : ℕ → ℝ} (hu : StrictMonoOn u (Set.Ioi 0)) (hq : ∀ t, 0 < q t)
    (hy : ∀ i, Summable (fun t => seqPrice q t * y i t))
    (he : IsSeqEquilibrium μ u β y (fun _ => 0) c a q) :
    IsADEquilibrium μ u β y c (seqPrice q) := by
  refine ⟨hy, fun i => ?_, he.2.1⟩
  have := (seq_optimal_iff_ad (c := c i) (a0 := 0) hu hq (hy i)).1 ⟨a i, he.1 i⟩
  rwa [zero_add] at this

/-- **AKMM, Definition 5: an instance.** With log utility, `0 < β < 1`, unit endowments and no
initial assets, `qₜ = β`, `c_{i,t} = 1` and `a_{i,t} = 0` form a sequential equilibrium. -/
theorem seq_equilibrium_instance {μ : Measure I} [IsProbabilityMeasure μ] {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    IsSeqEquilibrium μ Real.log β (fun _ _ => 1) (fun _ => 0) (fun _ _ => 1) (fun _ _ => 0)
      (fun _ => β) := by
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hp : ∀ t, seqPrice (fun _ => β) t = β ^ t := fun t => by simp [seqPrice]
  have hy : Summable (fun t => seqPrice (fun _ => β) t * 1) := by simpa [hp] using hgeo
  have had : ADOptimal Real.log β (seqPrice fun _ => β)
      (0 + ∑' t, seqPrice (fun _ => β) t * 1) (fun _ => 1) := by
    refine ad_foc_sufficient (du := fun _ => 1) (lam := 1) hβ0.le
      (fun t x hx => by simpa using ce_log_tangent one_pos hx) (fun t => by simp [hp])
      ⟨fun _ => one_pos, hy, by simp⟩ (by simp)
  obtain ⟨a, _, hU, hmax⟩ := (seq_optimal_iff_ad (c := fun _ => 1)
    Real.strictMonoOn_log (fun _ => hβ0) hy).2 had
  refine ⟨fun _ => ⟨⟨fun _ => one_pos, rfl, fun t => by simp, fun ε hε => ?_⟩, hU, hmax⟩,
    fun _ => rfl, fun _ => by simp⟩
  exact Filter.Eventually.of_forall fun _ => by simp; linarith

/-- **AKMM, p. 146: Euler's theorem for constant returns.** If `F : ℝ × ℝ → ℝ` is homogeneous of
degree one, `F(λx) = λF(x)` for `λ > 0`, and differentiable at `x`, then `F′(x)x = F(x)`; with
`F_K = F′(1, 0)`, `F_L = F′(0, 1)`, `F(K, L) = F_K K + F_L L`. -/
theorem euler_crs {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ} {x : ℝ × ℝ}
    (hhom : ∀ l : ℝ, 0 < l → F (l • x) = l * F x) (hd : HasFDerivAt F F' x) :
    F x = F' (1, 0) * x.1 + F' (0, 1) * x.2 := by
  have hpath : HasDerivAt (fun l : ℝ => l • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hd1 : HasDerivAt (fun l : ℝ => F (l • x)) (F' x) 1 := by
    have hd' : HasFDerivAt F F' ((1 : ℝ) • x) := by simpa using hd
    exact hd'.comp_hasDerivAt 1 hpath
  have hd2 : HasDerivAt (fun l : ℝ => F (l • x)) (F x) 1 := by
    have h : HasDerivAt (fun l : ℝ => l * F x) (F x) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with l hl using hhom l hl
  have heq := hd1.unique hd2
  have hlin : F' x = F' (1, 0) * x.1 + F' (0, 1) * x.2 := by
    have : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [← heq, hlin]

/-- **AKMM, Definition 6 and p. 146: Walras's law in the growth economy.** If every consumer's
budget `c_{i,t} + k_{i,t+1} = (1 − δ + rₜ)k_{i,t} + wₜeᵢ` holds, consumption and capital are
integrable, `∫ eᵢ di = 1`, `∫ k_{i,s} di = K_s` and the firm's prices satisfy Euler's identity
`F(Kₜ, 1) = rₜKₜ + wₜ`, then `Cₜ + K_{t+1} = F(Kₜ, 1) + (1 − δ)Kₜ`: the resource constraint is
redundant. -/
theorem seq_growth_walras {μ : Measure I} {δ Ft : ℝ} {e : I → ℝ} {c k : I → ℕ → ℝ}
    {r w K : ℕ → ℝ} {t : ℕ} (hb : ∀ i, c i t + k i (t + 1) = (1 - δ + r t) * k i t + w t * e i)
    (hc : Integrable (c · t) μ) (hk : ∀ s, Integrable (k · s) μ) (he : Integrable e μ)
    (he1 : ∫ i, e i ∂μ = 1) (hK : ∀ s, ∫ i, k i s ∂μ = K s) (heuler : Ft = r t * K t + w t) :
    ∫ i, c i t ∂μ + K (t + 1) = Ft + (1 - δ) * K t := by
  have h := congrArg (fun f => ∫ i, f i ∂μ) (funext hb)
  simp only at h
  rw [integral_add hc (hk (t + 1)), integral_add ((hk t).const_mul _) (he.const_mul _),
    integral_const_mul, integral_const_mul, he1, hK, hK] at h
  rw [heuler]
  linarith

end AKMM.CompetitiveEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive steady-state equilibria

AKMM, §5.4.1, pp. 147–149. Both steady-state problems of the section have the form
`V(x) = max_{x′} u(mx + y − nx′) + βV(x′)`: the endowment economy with `m = 1`, `n = q`
(Definition 7) and the growth economy with `m = 1 − δ + r`, `n = 1`, `y = weᵢ` (Definition 8).
The Bellman equation is imposed on the natural domain `{x : (m − n)x + y ∈ S}` (consumption
when holdings are kept constant lies in the set `S` where `u` is defined, e.g. `(0, ∞)`); with
`m = 1` this is the natural borrowing limit.

* The general problem (`SSBellman`): with `βm = n` and `u` concave, `g(x) = x` and
  `V(x) = u((m − n)x + y)/(1 − β)` solve it (`ss_value`); conversely a stationary point of an
  optimal policy, with `u′ ≠ 0` there and `S` open, forces `βm = n` (`ss_rate`). The proof
  compares the optimum with saving `ε` once and then holding the new level forever, which the
  Bellman equation itself prices; no envelope theorem is needed.
* Definition 7 (`IsSSEquilibriumEndow`): `q = β` (`definition_7_q_eq_beta`); the functional Euler
  equation at a stationary point gives `q = β` (`ss_functional_euler_q`) and `g(a) = a` solves it
  (`ss_functional_euler_id`); every asset distribution with `∫ aᵢ di = 0` is an equilibrium,
  with `Vᵢ(a) = u(a(1 − q) + yᵢ)/(1 − β)` (`definition_7_any_distribution`).
* Definition 8 (`IsSSEquilibriumGrowth`): `β(1 − δ + r) = 1` (`definition_8_rate`), not
  `β = 1 − δ + r` as printed (`definition_8_printed_counterexample`); with Cobb–Douglas
  technology `K* = (αA/(1/β − 1 + δ))^{1/(1−α)}` (`definition_8_capital`); every capital
  distribution adding up to `K*` is an equilibrium, with `gᵢ(k) = k` and
  `Vᵢ(k) = u(k(r − δ) + weᵢ)/(1 − β)` (`definition_8_any_distribution`).
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-- The steady-state Bellman equation `V(x) = max_{x′} u(mx + y − nx′) + βV(x′)` on the domain
`{x : (m − n)x + y ∈ S}`, with `g` attaining the maximum and consumption in `S`. -/
def SSBellman (u : ℝ → ℝ) (S : Set ℝ) (β m n y : ℝ) (V g : ℝ → ℝ) : Prop :=
  ∀ x, (m - n) * x + y ∈ S →
    ((m - n) * g x + y ∈ S ∧ m * x + y - n * g x ∈ S ∧
        V x = u (m * x + y - n * g x) + β * V (g x)) ∧
      ∀ x', (m - n) * x' + y ∈ S → m * x + y - n * x' ∈ S →
        u (m * x + y - n * x') + β * V x' ≤ V x

/-- **AKMM, pp. 148–149: the steady-state value and policy.** If `0 ≤ β < 1`, `βm = n` and `u`
is concave on the convex set `S`, then `g(x) = x` and `V(x) = u((m − n)x + y)/(1 − β)` solve the
steady-state Bellman equation. -/
theorem ss_value {u : ℝ → ℝ} {S : Set ℝ} {β m n y : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hmn : β * m = n) (hu : ConcaveOn ℝ S u) :
    SSBellman u S β m n y (fun x => u ((m - n) * x + y) / (1 - β)) id := by
  have h1 : (0 : ℝ) < 1 - β := by linarith
  intro x hx
  have hc : m * x + y - n * x = (m - n) * x + y := by ring
  refine ⟨⟨hx, by rw [id, hc]; exact hx, ?_⟩, fun x' hx' hc1 => ?_⟩
  · simp only [id, hc]; field_simp; ring
  · have hcomb : (1 - β) • (m * x + y - n * x') + β • ((m - n) * x' + y) = (m - n) * x + y := by
      simp only [smul_eq_mul]; rw [← hmn]; ring
    have := hu.2 hc1 hx' h1.le hβ0 (by ring)
    rw [hcomb] at this
    simp only [smul_eq_mul] at this
    simp only
    rw [le_div_iff₀ h1]
    have e : (u (m * x + y - n * x') + β * (u ((m - n) * x' + y) / (1 - β))) * (1 - β) =
        (1 - β) * u (m * x + y - n * x') + β * u ((m - n) * x' + y) := by
      field_simp
    rw [e]
    exact this

/-- **AKMM, pp. 148–149: a stationary point forces `βm = n`.** Suppose `V, g` solve the
steady-state Bellman equation, `S` is open, `0 ≤ β < 1`, `x*` lies in the domain with
`g(x*) = x*`, and `u` is differentiable at `c* = (m − n)x* + y` with `u′(c*) ≠ 0`. Then
`βm = n`. -/
theorem ss_rate {u : ℝ → ℝ} {S : Set ℝ} {β m n y du xs : ℝ} {V g : ℝ → ℝ}
    (hb : SSBellman u S β m n y V g) (hS : IsOpen S) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hx : (m - n) * xs + y ∈ S) (hg : g xs = xs) (hd : HasDerivAt u du ((m - n) * xs + y))
    (hdu : du ≠ 0) : β * m = n := by
  have h1 : (0 : ℝ) < 1 - β := by linarith
  set cs := (m - n) * xs + y with hcs
  -- the value at `x*`
  have hV : V xs = u cs / (1 - β) := by
    have h := ((hb xs hx).1).2.2
    rw [hg, show m * xs + y - n * xs = cs by rw [hcs]; ring] at h
    field_simp; linarith
  -- keeping any holdings `x` forever gives `V(x) ≥ u((m − n)x + y)/(1 − β)`
  have hkeep : ∀ x, (m - n) * x + y ∈ S → u ((m - n) * x + y) / (1 - β) ≤ V x := by
    intro x hxS
    have e : m * x + y - n * x = (m - n) * x + y := by ring
    have := (hb x hxS).2 x hxS (by rw [e]; exact hxS)
    rw [e] at this
    rw [div_le_iff₀ h1]; linarith
  -- deviation: move to `x* + ε` once and stay
  let φ : ℝ → ℝ := fun ε => u (cs - n * ε) + β / (1 - β) * u (cs + (m - n) * ε)
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), cs - n * ε ∈ S ∧ cs + (m - n) * ε ∈ S := by
    have c1 : ContinuousAt (fun ε : ℝ => cs - n * ε) 0 :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
    have c2 : ContinuousAt (fun ε : ℝ => cs + (m - n) * ε) 0 :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
    exact (c1.eventually_mem (hS.mem_nhds (by simpa using hx))).and
      (c2.eventually_mem (hS.mem_nhds (by simpa using hx)))
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hev] with ε hε
    have ed : (m - n) * (xs + ε) + y = cs + (m - n) * ε := by rw [hcs]; ring
    have ec : m * xs + y - n * (xs + ε) = cs - n * ε := by rw [hcs]; ring
    have hB := (hb xs hx).2 (xs + ε) (by rw [ed]; exact hε.2) (by rw [ec]; exact hε.1)
    have hK := hkeep (xs + ε) (by rw [ed]; exact hε.2)
    rw [ed] at hK
    rw [ec] at hB
    have h0 : φ 0 = V xs := by
      rw [hV]; simp only [φ, mul_zero, sub_zero, add_zero]; field_simp; ring
    change φ ε ≤ φ 0
    rw [h0]
    have e : β / (1 - β) * u (cs + (m - n) * ε) = β * (u (cs + (m - n) * ε) / (1 - β)) := by
      ring
    simp only [φ]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hK hβ0]
  have hφ : HasDerivAt φ (du * (-n) + β / (1 - β) * (du * (m - n))) 0 := by
    have hA : HasDerivAt (fun ε => u (cs - n * ε)) (du * (-n)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => cs - n * ε) (-n) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul n).const_sub cs
      have hu : HasDerivAt u du (cs - n * 0) := by simpa using hd
      exact hu.comp 0 hin
    have hB : HasDerivAt (fun ε => u (cs + (m - n) * ε)) (du * (m - n)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => cs + (m - n) * ε) (m - n) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (m - n)).const_add cs
      have hu : HasDerivAt u du (cs + (m - n) * 0) := by simpa using hd
      exact hu.comp 0 hin
    exact hA.add (hB.const_mul _)
  have hz := hmax.hasDerivAt_eq_zero hφ
  have h2 : du * (β * m - n) = 0 := by
    field_simp at hz
    linear_combination hz
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hdu
  · linarith

/-! ### Definition 7: the endowment economy -/

/-- **AKMM, Definition 7, p. 147.** A recursive steady-state equilibrium of the endowment
economy: a price `q`, and for each consumer `Vᵢ, gᵢ` solving
`Vᵢ(a) = max_{a′} u(a + yᵢ − qa′) + βVᵢ(a′)` (on the natural domain), holdings `aᵢ*` in the
domain with `gᵢ(aᵢ*) = aᵢ*`, and `∫ gᵢ(aᵢ*) di = 0`. -/
def IsSSEquilibriumEndow (μ : Measure I) (u : ℝ → ℝ) (S : Set ℝ) (β : ℝ) (y : I → ℝ) (q : ℝ)
    (V g : I → ℝ → ℝ) (as : I → ℝ) : Prop :=
  (∀ i, SSBellman u S β 1 q (y i) (V i) (g i)) ∧ (∀ i, (1 - q) * as i + y i ∈ S) ∧
    (∀ i, g i (as i) = as i) ∧ ∫ i, g i (as i) ∂μ = 0

/-- **AKMM, p. 148: `q = β`.** In a steady-state equilibrium with `S` open, `0 ≤ β < 1` and
`u′ ≠ 0` at each consumer's steady consumption `(1 − q)aᵢ* + yᵢ`, the price is `q = β`. -/
theorem definition_7_q_eq_beta {μ : Measure I} {u du : ℝ → ℝ} {S : Set ℝ} {β q : ℝ}
    {y : I → ℝ} {V g : I → ℝ → ℝ} {as : I → ℝ}
    (he : IsSSEquilibriumEndow μ u S β y q V g as) (hS : IsOpen S) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hd : ∀ c ∈ S, HasDerivAt u (du c) c) (hdu : ∀ c ∈ S, du c ≠ 0) (i : I) : q = β := by
  obtain ⟨hb, hdom, hfix, _⟩ := he
  have h := ss_rate (hb i) hS hβ0 hβ1 (hdom i) (hfix i) (hd _ (hdom i)) (hdu _ (hdom i))
  linarith

/-- **AKMM, p. 148: the functional Euler equation at a stationary point.** If
`qu′(a + y − qg(a)) = βu′(g(a) + y − qg(g(a)))` holds at `a = a*` with `g(a*) = a*` and
`u′(a*(1 − q) + y) ≠ 0`, then `q = β`. -/
theorem ss_functional_euler_q {du g : ℝ → ℝ} {q β y as : ℝ} (hfix : g as = as)
    (heul : q * du (as + y - q * g as) = β * du (g as + y - q * g (g as)))
    (hdu : du (as * (1 - q) + y) ≠ 0) : q = β := by
  rw [hfix, hfix] at heul
  have e : as + y - q * as = as * (1 - q) + y := by ring
  rw [e] at heul
  exact mul_right_cancel₀ hdu heul

/-- **AKMM, p. 148: `g(a) = a` solves the functional Euler equation when `q = β`.** -/
theorem ss_functional_euler_id {du : ℝ → ℝ} {β y : ℝ} (a : ℝ) :
    β * du (a + y - β * id a) = β * du (id a + y - β * id (id a)) := by
  simp

/-- **AKMM, p. 148: the asset distribution is indeterminate.** For `0 ≤ β < 1`, `u` concave on
the convex set `S` and any holdings `aᵢ*` with `∫ aᵢ* di = 0` and `(1 − β)aᵢ* + yᵢ ∈ S`,
`q = β`, `gᵢ(a) = a` and `Vᵢ(a) = u(a(1 − q) + yᵢ)/(1 − β)` form a steady-state equilibrium. -/
theorem definition_7_any_distribution {μ : Measure I} {u : ℝ → ℝ} {S : Set ℝ} {β : ℝ}
    {y : I → ℝ} {as : I → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hu : ConcaveOn ℝ S u)
    (hdom : ∀ i, (1 - β) * as i + y i ∈ S) (hclear : ∫ i, as i ∂μ = 0) :
    IsSSEquilibriumEndow μ u S β y β
      (fun i a => u (a * (1 - β) + y i) / (1 - β)) (fun _ => id) as := by
  refine ⟨fun i => ?_, hdom, fun _ => rfl, hclear⟩
  have h := ss_value (y := y i) hβ0 hβ1 (by ring : β * 1 = β) hu
  have e : (fun x => u ((1 - β) * x + y i) / (1 - β)) = fun a => u (a * (1 - β) + y i) / (1 - β) :=
    by funext a; ring_nf
  rwa [e] at h

/-! ### Definition 8: the growth economy -/

/-- **AKMM, Definition 8, p. 149.** A recursive steady-state equilibrium of the growth economy
with labour `eᵢ`: prices `r, w`, for each consumer `Vᵢ, gᵢ` solving
`Vᵢ(k) = max_{k′} u((1 − δ + r)k + weᵢ − k′) + βVᵢ(k′)` (on the natural domain), `(K*, 1)`
maximizing `F(K, L) − rK − wL` over `K, L ≥ 0` with `∫ kᵢ* di = K*`, and `gᵢ(kᵢ*) = kᵢ*`
with `kᵢ*` in the domain. -/
def IsSSEquilibriumGrowth (μ : Measure I) (u : ℝ → ℝ) (S : Set ℝ) (β δ : ℝ)
    (F : ℝ → ℝ → ℝ) (e : I → ℝ) (r w : ℝ) (V g : I → ℝ → ℝ) (ks : I → ℝ) (Ks : ℝ) : Prop :=
  (∀ i, SSBellman u S β (1 - δ + r) 1 (w * e i) (V i) (g i)) ∧
    (∀ K L, 0 ≤ K → 0 ≤ L → F K L - r * K - w * L ≤ F Ks 1 - r * Ks - w * 1) ∧
    ∫ i, ks i ∂μ = Ks ∧ (∀ i, (1 - δ + r - 1) * ks i + w * e i ∈ S) ∧ ∀ i, g i (ks i) = ks i

/-- **AKMM, p. 149, corrected: `β(1 − δ + r) = 1`.** In a steady-state equilibrium with `S`
open, `0 ≤ β < 1` and `u′ ≠ 0` on `S`, the gross return satisfies `β(1 − δ + r) = 1`. The book
prints `β = 1 − δ + r`. -/
theorem definition_8_rate {μ : Measure I} {u du : ℝ → ℝ} {S : Set ℝ} {β δ r w Ks : ℝ}
    {F : ℝ → ℝ → ℝ} {e : I → ℝ} {V g : I → ℝ → ℝ} {ks : I → ℝ}
    (he : IsSSEquilibriumGrowth μ u S β δ F e r w V g ks Ks) (hS : IsOpen S) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hd : ∀ c ∈ S, HasDerivAt u (du c) c) (hdu : ∀ c ∈ S, du c ≠ 0) (i : I) :
    β * (1 - δ + r) = 1 := by
  obtain ⟨hb, _, _, hdom, hfix⟩ := he
  exact ss_rate (hb i) hS hβ0 hβ1 (hdom i) (hfix i) (hd _ (hdom i)) (hdu _ (hdom i))

/-- **AKMM, p. 149: the policy and value functions; the distribution is indeterminate.** If
`0 ≤ β < 1`, `β(1 − δ + r) = 1`, `u` is concave on the convex set `S`, `(K*, 1)` solves the
firm's problem and `kᵢ*` is any distribution with `∫ kᵢ* di = K*` and
`k(r − δ) + weᵢ ∈ S` at `kᵢ*`, then `gᵢ(k) = k` and `Vᵢ(k) = u(k(r − δ) + weᵢ)/(1 − β)` form a
steady-state equilibrium. -/
theorem definition_8_any_distribution {μ : Measure I} {u : ℝ → ℝ} {S : Set ℝ} {β δ r w Ks : ℝ}
    {F : ℝ → ℝ → ℝ} {e : I → ℝ} {ks : I → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrate : β * (1 - δ + r) = 1) (hu : ConcaveOn ℝ S u)
    (hfirm : ∀ K L, 0 ≤ K → 0 ≤ L → F K L - r * K - w * L ≤ F Ks 1 - r * Ks - w * 1)
    (hclear : ∫ i, ks i ∂μ = Ks) (hdom : ∀ i, (1 - δ + r - 1) * ks i + w * e i ∈ S) :
    IsSSEquilibriumGrowth μ u S β δ F e r w
      (fun i k => u (k * (r - δ) + w * e i) / (1 - β)) (fun _ => id) ks Ks := by
  refine ⟨fun i => ?_, hfirm, hclear, hdom, fun _ => rfl⟩
  have h := ss_value (y := w * e i) hβ0 hβ1 hrate hu
  have e1 : (fun x => u ((1 - δ + r - 1) * x + w * e i) / (1 - β)) =
      fun k => u (k * (r - δ) + w * e i) / (1 - β) := by funext k; ring_nf
  rwa [e1] at h

/-- **AKMM, p. 149: the steady-state capital stock.** With `F(K, 1) = AK^α`, `0 < α < 1`,
`A > 0`, `0 < β`, the conditions `β(1 − δ + r) = 1` and `r = αAK^{α−1}` with `K > 0` give
`K = (αA/(1/β − 1 + δ))^{1/(1−α)}`. -/
theorem definition_8_capital {A α β δ r K : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hK : 0 < K) (hrate : β * (1 - δ + r) = 1) (hr : r = α * A * K ^ (α - 1)) :
    K = (α * A / (1 / β - 1 + δ)) ^ (1 - α)⁻¹ := by
  have hr' : r = 1 / β - 1 + δ := by field_simp; linarith
  have hrpos : 0 < r := by rw [hr]; exact mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos hK _)
  rw [← hr']
  have e : α * A / r = K ^ (1 - α) := by
    rw [hr, show (1 : ℝ) - α = -(α - 1) by ring, Real.rpow_neg hK.le]
    have := (Real.rpow_pos_of_pos hK (α - 1)).ne'
    have := (mul_pos hα0 hA).ne'
    field_simp
  rw [e, Real.rpow_rpow_inv hK.le (by linarith)]

/-- **AKMM, p. 149: the printed condition `β = 1 − δ + r` is false.** With `u = log` on
`(0, ∞)`, `β = 1/2`, `δ = 1`, `F(K, L) = 4K^{1/2}L^{1/2}`, `r = w = 2`, `K* = 1` and every
consumer holding `kᵢ* = 1` with `eᵢ = 1`, `gᵢ(k) = k` and `Vᵢ(k) = 2 log(k + 2)` form a
steady-state equilibrium (Definition 8), and `1 − δ + r = 2 ≠ β`. -/
theorem definition_8_printed_counterexample {μ : Measure I} [IsProbabilityMeasure μ] :
    IsSSEquilibriumGrowth μ Real.log (Set.Ioi 0) (1 / 2) 1
      (fun K L => 4 * K ^ (1 / 2 : ℝ) * L ^ (1 - 1 / 2 : ℝ)) (fun _ => 1) 2 2
      (fun i k => Real.log (k * (2 - 1) + 2 * (fun _ : I => (1 : ℝ)) i) / (1 - 1 / 2))
      (fun _ => id) (fun _ => 1) 1 ∧ (1 - 1 + 2 : ℝ) ≠ 1 / 2 := by
  refine ⟨?_, by norm_num⟩
  have hfirm := (growth_firm_optimal (A := 4) (α := 1 / 2) (K := 1) (L := 1) (by norm_num)
    (by norm_num) (by norm_num) one_pos one_pos)
  simp only [Real.one_rpow, mul_one] at hfirm
  norm_num at hfirm
  refine definition_8_any_distribution (by norm_num) (by norm_num) (by norm_num)
    (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi) (fun K L hK hL => ?_) (by simp)
    (fun i => by norm_num)
  have := hfirm.2 K L hK hL
  simp only [cdProfit] at this
  norm_num
  linarith

end AKMM.CompetitiveEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive competitive equilibrium and aggregation

AKMM, §5.4.2, pp. 149–152, and Appendix 5.A, pp. 836–837. The household takes the price
functions `r(K)`, `w(K)` and the law of motion `K′ = G(K)` as given and solves (5.23); in a
recursive competitive equilibrium (Definition 9) `r(K) = F₁(K, 1)`, `w(K) = F₂(K, 1)` and
`G(K) = g(K, K)`.

* The resource constraint is implied (p. 150): consumption at `k = K` is
  `F(K, 1) + (1 − δ)K − G(K)` whenever `F(K, 1) = F₁K + F₂` (Euler's theorem, `euler_crs`)
  (`definition_9_resource`).
* The aggregate functional Euler equation (p. 151): evaluating the household's functional Euler
  equation at `k = K` gives the planner's equation (4.26),
  `u′((1 − δ)K + F(K, 1) − G(K)) = βu′((1 − δ)G(K) + F(G(K), 1) − G(G(K)))(1 − δ + F₁(G(K), 1))`
  (`definition_9_aggregate_euler`). The book prints `K(1 − δ)K` on the left; at a steady state
  with `δ ≠ 1`, `K ∉ {0, 1}` the printed equation fails
  (`definition_9_aggregate_euler_printed`, with the instance
  `definition_9_aggregate_euler_printed_instance`).
* Aggregation (p. 151, Appendix 5.A): with `u = c^{1−σ}/(1 − σ)` the Euler equation is
  equivalent to the linear equation `A + Bk + Cg(k, K) + Dg(g(k, K), G(K)) = 0`
  (`appendix_5A_power`, `appendix_5A_linear`); for `g = μ + λk` it splits into a constant term
  and a coefficient of `k` (`appendix_5A_split`), so the two functional equations make the
  Euler equation hold for all `k` (`appendix_5A_mu_lambda`). The book has the roles of the two
  equations reversed (`appendix_5A_printed_attribution_counterexample`).
* With linear policies `gᵢ(k, K) = μᵢ(K) + λ(K)k`, aggregate saving depends on the distribution
  only through `K` (`aggregation_linear`).
* Appendix 5.A closed form: log utility, `F = AK^α`, `δ = 1`: `G(K) = αβAK^α` and
  `g(k, K) = βr(K)k` satisfy the household's functional Euler equation for every `(k, K)` and
  consistency (`appendix_5A_closed_form`), with `μ = 0`, `λ = βr` solving the two functional
  equations (`appendix_5A_closed_form_mu_lambda`).
* Definition 10 (valued leisure, p. 152): at `k = K` the household's intratemporal condition is
  the planner's, and consumption is output plus undepreciated capital minus investment
  (`definition_10_planner`).

Not formalised: existence of `V` in (5.23) (the book does not construct it); condition 1 of
Definition 9 enters through its functional Euler equation, as in the book's characterisation.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-- **AKMM, p. 150: Definition 9 implies the resource constraint.** If `r(K) = F₁(K, 1)`,
`w(K) = F₂(K, 1)`, `G(K) = g(K, K)` and `F(K, 1) = F₁(K, 1)K + F₂(K, 1)`, then the
representative consumer's consumption `K(1 − δ + r(K)) + w(K) − G(K)` equals
`F(K, 1) + (1 − δ)K − G(K)`. -/
theorem definition_9_resource {F F1 F2 r w G : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {δ K : ℝ}
    (hr : r K = F1 K) (hw : w K = F2 K) (hG : G K = g K K) (heuler : F K = F1 K * K + F2 K) :
    K * (1 - δ + r K) + w K - g K K = F K + (1 - δ) * K - G K := by
  rw [hr, hw, hG, heuler]; ring

/-- **AKMM, p. 151, corrected: the aggregate functional Euler equation.** If the household's
functional Euler equation
`u′((1 − δ + r(K))k + w(K) − g(k, K)) =
  βu′(g(k, K)(1 − δ + r(G(K))) + w(G(K)) − g(g(k, K), G(K)))(1 − δ + r(G(K)))`
holds at `k = K` for all `K`, with `r = F₁`, `w = F₂`, `G(K) = g(K, K)` and Euler's identity
`F = F₁K + F₂`, then
`u′(K(1 − δ) + F(K) − G(K)) = βu′(G(K)(1 − δ) + F(G(K)) − G(G(K)))(1 − δ + F₁(G(K)))`, the
planner's (4.26). -/
theorem definition_9_aggregate_euler {du F F1 F2 r w G : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {β δ : ℝ}
    (heul : ∀ k K, du ((1 - δ + r K) * k + w K - g k K) =
      β * du (g k K * (1 - δ + r (G K)) + w (G K) - g (g k K) (G K)) * (1 - δ + r (G K)))
    (hr : ∀ K, r K = F1 K) (hw : ∀ K, w K = F2 K) (hG : ∀ K, G K = g K K)
    (heuler : ∀ K, F K = F1 K * K + F2 K) (K : ℝ) :
    du (K * (1 - δ) + F K - G K) =
      β * du (G K * (1 - δ) + F (G K) - G (G K)) * (1 - δ + F1 (G K)) := by
  have h := heul K K
  rw [← hG K, ← hG (G K), hr, hw, hr, hw] at h
  have e1 : (1 - δ + F1 K) * K + F2 K - G K = K * (1 - δ) + F K - G K := by
    rw [heuler]; ring
  have e2 : G K * (1 - δ + F1 (G K)) + F2 (G K) - G (G K) =
      G K * (1 - δ) + F (G K) - G (G K) := by rw [heuler]; ring
  rw [e1, e2] at h
  exact h

/-- **AKMM, p. 151: the printed aggregate equation is wrong.** The book prints the left side as
`u′(K(1 − δ)K + F(K, 1) − G(K))`. If `u′` is injective, `δ ≠ 1` and `K ∉ {0, 1}`, the printed
and the correct equations cannot both hold at `K`. -/
theorem definition_9_aggregate_euler_printed {du F F1 G : ℝ → ℝ} {β δ K : ℝ}
    (hinj : Function.Injective du) (hδ : δ ≠ 1) (hK0 : K ≠ 0) (hK1 : K ≠ 1)
    (hcorrect : du (K * (1 - δ) + F K - G K) =
      β * du (G K * (1 - δ) + F (G K) - G (G K)) * (1 - δ + F1 (G K))) :
    du (K * (1 - δ) * K + F K - G K) ≠
      β * du (G K * (1 - δ) + F (G K) - G (G K)) * (1 - δ + F1 (G K)) := by
  intro hprinted
  have := hinj (hprinted.trans hcorrect.symm)
  have h : (1 - δ) * K * (K - 1) = 0 := by linarith
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact hδ (by linarith)
    · exact hK0 h
  · exact hK1 (by linarith)

/-- **AKMM, p. 151: an instance.** With `u = log` (`u′(c) = 1/c`), `F(K) = 6K^{1/2}`,
`δ = β = 1/2`, the steady state is `K̄ = 4`: for any law of motion with `G(4) = 4` the correct
aggregate equation holds at `K = 4` and the printed one fails. -/
theorem definition_9_aggregate_euler_printed_instance {G : ℝ → ℝ} (hG : G 4 = 4) :
    let F : ℝ → ℝ := fun K => 6 * K ^ (1 / 2 : ℝ)
    let F1 : ℝ → ℝ := fun K => 1 / 2 * 6 * K ^ (1 / 2 - 1 : ℝ)
    (4 * (1 - 1 / 2) + F 4 - G 4)⁻¹ =
        1 / 2 * (G 4 * (1 - 1 / 2) + F (G 4) - G (G 4))⁻¹ * (1 - 1 / 2 + F1 (G 4)) ∧
      (4 * (1 - 1 / 2) * 4 + F 4 - G 4)⁻¹ ≠
        1 / 2 * (G 4 * (1 - 1 / 2) + F (G 4) - G (G 4))⁻¹ * (1 - 1 / 2 + F1 (G 4)) := by
  intro F F1
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have h4' : (4 : ℝ) ^ (1 / 2 - 1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_sub (by norm_num), h4, Real.rpow_one]; norm_num
  simp only [F, F1, hG, h4, h4']
  norm_num

/-- **AKMM, Appendix 5.A, p. 836: raising the power Euler equation to `−1/σ`.** For `σ > 0`,
consumptions `c, c′ > 0` and a gross return with `βR′ > 0`,
`c^{−σ} = βc′^{−σ}R′` iff `c = (βR′)^{−1/σ}c′`. -/
theorem appendix_5A_power {σ β R' c c' : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hc' : 0 < c')
    (hR : 0 < β * R') :
    c ^ (-σ) = β * c' ^ (-σ) * R' ↔ c = (β * R') ^ (-σ⁻¹) * c' := by
  have hσ' : σ ≠ 0 := hσ.ne'
  constructor
  · intro h
    have h1 : c ^ (-σ) = (β * R') * c' ^ (-σ) := by rw [h]; ring
    have h2 := congrArg (fun x => x ^ (-σ⁻¹)) h1
    rw [← Real.rpow_mul hc.le, Real.mul_rpow hR.le (Real.rpow_nonneg hc'.le _),
      ← Real.rpow_mul hc'.le] at h2
    have e : -σ * -σ⁻¹ = 1 := by field_simp
    rw [e, Real.rpow_one, Real.rpow_one] at h2
    exact h2
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hR.le _) hc'.le, ← Real.rpow_mul hR.le]
    have e : -σ⁻¹ * -σ = 1 := by field_simp
    rw [e, Real.rpow_one]
    ring

/-- **AKMM, Appendix 5.A, p. 836: the linear form.** With `R = 1 − δ + r(K)`,
`R′ = 1 − δ + r(G(K))`, `φ = (βR′)^{−1/σ}`, the equation
`Rk + w − g = φ(gR′ + w′ − g′)` is `A + Bk + Cg + Dg′ = 0` with `A = w − φw′`, `B = R`,
`C = −(1 + φR′)` and `D = φ`. -/
theorem appendix_5A_linear {R R' w w' φ k g g' : ℝ} :
    R * k + w - g = φ * (g * R' + w' - g') ↔
      (w - φ * w') + R * k + (-(1 + φ * R')) * g + φ * g' = 0 := by
  constructor <;> intro h <;> linarith

/-- **AKMM, Appendix 5.A, p. 836: the split.** For `g = μ + λk` and `g′ = μ′ + λ′g`,
`A + Bk + Cg + Dg′` equals `[A + Cμ + D(μ′ + λ′μ)] + k[B + Cλ + Dλ′λ]`: the first of the book's
two functional equations is the constant term, the second the coefficient of `k`. -/
theorem appendix_5A_split (A B C D μ lam μ' lam' k : ℝ) :
    A + B * k + C * (μ + lam * k) + D * (μ' + lam' * (μ + lam * k)) =
      (A + C * μ + D * (μ' + lam' * μ)) + k * (B + C * lam + D * lam' * lam) := by
  ring

/-- **AKMM, Appendix 5.A, p. 836: linear policies solve the Euler equation.** If `μ(K)` and
`λ(K)` satisfy `A(K) + C(K)μ(K) + D(K)(μ(G(K)) + λ(G(K))μ(K)) = 0` and
`B(K) + C(K)λ(K) + D(K)λ(G(K))λ(K) = 0` for all `K`, then `g(k, K) = μ(K) + λ(K)k` satisfies
`A(K) + B(K)k + C(K)g(k, K) + D(K)g(g(k, K), G(K)) = 0` for all `(k, K)`. -/
theorem appendix_5A_mu_lambda {A B C D μ lam G : ℝ → ℝ}
    (h1 : ∀ K, A K + C K * μ K + D K * (μ (G K) + lam (G K) * μ K) = 0)
    (h2 : ∀ K, B K + C K * lam K + D K * lam (G K) * lam K = 0) (k K : ℝ) :
    let g : ℝ → ℝ → ℝ := fun k K => μ K + lam K * k
    A K + B K * k + C K * g k K + D K * g (g k K) (G K) = 0 := by
  intro g
  simp only [g]
  rw [appendix_5A_split, h1, h2]
  ring

/-- **AKMM, Appendix 5.A, p. 836: the printed attribution is reversed.** The book says the first
equation makes the coefficient of `k` vanish. With `A = C = D = 0`, `B = 1`, `λ = 0`, the first
equation holds for every `μ` while the coefficient of `k`, `B + Cλ + Dλ′λ = 1`, does not
vanish. -/
theorem appendix_5A_printed_attribution_counterexample (μ μ' : ℝ) :
    (0 : ℝ) + 0 * μ + 0 * (μ' + 0 * μ) = 0 ∧ (1 : ℝ) + 0 * 0 + 0 * 0 * 0 ≠ 0 := by
  norm_num

/-- **AKMM, p. 151: aggregation with linear policies.** If `gᵢ(k, K) = μᵢ(K) + λ(K)k` with the
same slope for all consumers, `μᵢ(K)` and `kᵢ` are integrable and `∫ kᵢ di = K`, then aggregate
saving `∫ gᵢ(kᵢ, K) di = ∫ μᵢ(K) di + λ(K)K` depends on the distribution only through `K`. -/
theorem aggregation_linear {μm : Measure I} {μ : I → ℝ} {lam K : ℝ} {k : I → ℝ}
    (hμ : Integrable μ μm) (hk : Integrable k μm) (hK : ∫ i, k i ∂μm = K) :
    ∫ i, (μ i + lam * k i) ∂μm = ∫ i, μ i ∂μm + lam * K := by
  rw [integral_add hμ (hk.const_mul lam), integral_const_mul, hK]

/-- **AKMM, Appendix 5.A, pp. 836–837: the closed form.** With log utility (`u′(c) = 1/c`),
`F(K, 1) = AK^α`, `δ = 1`, `r(K) = αAK^{α−1}`, `w(K) = (1 − α)AK^α`, `G(K) = αβAK^α` and
`g(k, K) = βr(K)k`: consistency `G(K) = g(K, K)` holds, and for every `K > 0` and `k ≥ 0` the
household's functional Euler equation
`1/(r(K)k + w(K) − g(k, K)) = β r(G(K))/(r(G(K))g(k, K) + w(G(K)) − g(g(k, K), G(K)))` holds,
with positive consumption. -/
theorem appendix_5A_closed_form {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    let r : ℝ → ℝ := fun K => α * A * K ^ (α - 1)
    let w : ℝ → ℝ := fun K => (1 - α) * A * K ^ α
    let G : ℝ → ℝ := fun K => α * β * A * K ^ α
    let g : ℝ → ℝ → ℝ := fun k K => β * r K * k
    (∀ K, 0 < K → G K = g K K) ∧
      ∀ k K, 0 ≤ k → 0 < K →
        0 < r K * k + w K - g k K ∧
        0 < r (G K) * g k K + w (G K) - g (g k K) (G K) ∧
        (r K * k + w K - g k K)⁻¹ =
          β * (r (G K) * g k K + w (G K) - g (g k K) (G K))⁻¹ * r (G K) := by
  intro r w G g
  have hKa : ∀ K : ℝ, 0 < K → K ^ (α - 1) = K ^ α / K := fun K hK => Real.rpow_sub_one hK.ne' α
  refine ⟨fun K hK => ?_, fun k K hk hK => ?_⟩
  · simp only [G, g, r]; rw [hKa K hK]; field_simp
  have hGpos : 0 < G K := by
    simp only [G]; exact mul_pos (mul_pos (mul_pos hα0 hβ0) hA) (Real.rpow_pos_of_pos hK _)
  have hrpos : ∀ K : ℝ, 0 < K → 0 < r K := fun K hK =>
    mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos hK _)
  have hwpos : ∀ K : ℝ, 0 < K → 0 < w K := fun K hK =>
    mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos hK _)
  -- the key identity `w(G(K)) = βr(G(K))w(K)`
  have hwG : w (G K) = β * r (G K) * w K := by
    simp only [w, r]
    rw [hKa (G K) hGpos]
    have hG' : G K = α * β * A * K ^ α := rfl
    have := hGpos.ne'
    field_simp
    rw [hG']
    ring
  have hc : r K * k + w K - g k K = (1 - β) * r K * k + w K := by simp only [g]; ring
  have hc' : r (G K) * g k K + w (G K) - g (g k K) (G K) =
      β * r (G K) * ((1 - β) * r K * k + w K) := by
    simp only [g]; rw [hwG]; ring
  have hcpos : 0 < (1 - β) * r K * k + w K := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) (hrpos K hK).le) hk
    linarith [hwpos K hK]
  have hrG := hrpos (G K) hGpos
  refine ⟨by rw [hc]; exact hcpos, by rw [hc']; positivity, ?_⟩
  rw [hc, hc']
  have := hcpos.ne'
  have := hrG.ne'
  have := hβ0.ne'
  field_simp

/-- **AKMM, Appendix 5.A, p. 837: `μ(K) = 0`, `λ(K) = βr(K)`.** In the closed-form economy
(`σ = 1`, so `φ = 1/(βR′)` with `R′ = r(G(K))`; `A = w − φw′`, `B = r(K)`, `C = −(1 + φR′)`,
`D = φ`), `μ = 0` and `λ = βr` solve both functional equations. -/
theorem appendix_5A_closed_form_mu_lambda {A α β K : ℝ} (hA : 0 < A) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hK : 0 < K) :
    let r : ℝ → ℝ := fun K => α * A * K ^ (α - 1)
    let w : ℝ → ℝ := fun K => (1 - α) * A * K ^ α
    let G : ℝ → ℝ := fun K => α * β * A * K ^ α
    let φ := (β * r (G K))⁻¹
    (w K - φ * w (G K)) + (-(1 + φ * r (G K))) * 0 + φ * (0 + β * r (G K) * 0) = 0 ∧
      r K + (-(1 + φ * r (G K))) * (β * r K) + φ * (β * r (G K)) * (β * r K) = 0 := by
  intro r w G φ
  have hGpos : 0 < G K := by
    simp only [G]; exact mul_pos (mul_pos (mul_pos hα0 hβ0) hA) (Real.rpow_pos_of_pos hK _)
  have hrG : 0 < r (G K) := mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos hGpos _)
  have hwG : w (G K) = β * r (G K) * w K := by
    simp only [w, r]
    rw [Real.rpow_sub_one hGpos.ne']
    have hG' : G K = α * β * A * K ^ α := rfl
    have := hGpos.ne'
    field_simp
    rw [hG']
    ring
  have hφ : φ * (β * r (G K)) = 1 := inv_mul_cancel₀ (mul_pos hβ0 hrG).ne'
  constructor
  · rw [hwG]
    have : φ * (β * r (G K) * w K) = w K := by rw [← mul_assoc, hφ, one_mul]
    linarith
  · have e : φ * r (G K) * (β * r K) = r K := by
      rw [show φ * r (G K) * (β * r K) = φ * (β * r (G K)) * r K by ring, hφ, one_mul]
    have e2 : φ * (β * r (G K)) * (β * r K) = β * r K := by rw [hφ, one_mul]
    linear_combination (-1 : ℝ) * e + e2

/-- **AKMM, Definition 10, p. 152, and the remark after it.** With valued leisure, if
`r(K) = F₁(K, H(K))`, `w(K) = F₂(K, H(K))`, `G(K) = g(K, K)`, `H(K) = h(K, K)` and Euler's
identity `F(K, H) = F₁K + F₂H` holds, then at `k = K` (i) consumption is
`F(K, H(K)) + (1 − δ)K − G(K)` and (ii) the household's intratemporal condition
`v′(h) = w(K)u′(c)` is the planner's `v′(L) = F₂(K, L)u′(C)`. -/
theorem definition_10_planner {du dv : ℝ → ℝ} {F F1 F2 : ℝ → ℝ → ℝ} {r w G H : ℝ → ℝ}
    {g h : ℝ → ℝ → ℝ} {δ K : ℝ} (hr : r K = F1 K (H K)) (hw : w K = F2 K (H K))
    (hG : G K = g K K) (hH : H K = h K K)
    (heuler : F K (H K) = F1 K (H K) * K + F2 K (H K) * H K)
    (hintra : dv (h K K) = w K * du ((1 - δ + r K) * K + w K * h K K - g K K)) :
    (1 - δ + r K) * K + w K * h K K - g K K = F K (H K) + (1 - δ) * K - G K ∧
      dv (H K) = F2 K (H K) * du (F K (H K) + (1 - δ) * K - G K) := by
  have hc : (1 - δ + r K) * K + w K * h K K - g K K = F K (H K) + (1 - δ) * K - G K := by
    rw [hr, hw, ← hH, ← hG, heuler]; ring
  refine ⟨hc, ?_⟩
  calc dv (H K) = dv (h K K) := by rw [hH]
    _ = w K * du ((1 - δ + r K) * K + w K * h K K - g K K) := hintra
    _ = F2 K (H K) * du (F K (H K) + (1 - δ) * K - G K) := by rw [hc, hw]

end AKMM.CompetitiveEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Overlapping generations

AKMM, §5.5, pp. 152–157. Two-period lives, sequential trade, no population growth.

* The endowment economy (Definition 11, `IsOGEndowEquilibrium`): goods clearing forces
  `a_{t+1} = 0` and autarky (`og_autarky`); the Euler equation at autarky
  `qₜu′(ω_{y,t}) = βu′(ω_{o,t+1})` (`og_euler_autarky`) and, for CRRA utility, (5.24)
  `qₜ = β(ω_{y,t}/ω_{o,t+1})^σ` (`eq_5_24`); autarky at these prices is an equilibrium
  (`og_autarky_equilibrium`); `q > 1`, a negative interest rate, when `ω_y > ω_o`
  (`og_negative_rate_example`), which in the dynastic economy needs a falling aggregate
  endowment (`og_dynastic_rate`).
* The book's Definition 11 asks only cohorts `t > 0` to optimize; then `q₀` is undetermined and
  (5.24) fails at `t = 0` (`definition_11_printed_counterexample`). The definitions here take
  a starting cohort `t₀`; the corrected definition is `t₀ = 0`.
* The production economy (Definition 12, `IsOGGrowthEquilibrium`): the Euler equation is a
  first-order difference equation in `k` (`og_growth_euler`), with the steady-state version
  (`og_growth_steady`). The exercise (log, `e_y = 1`, `e_o = 0`, Cobb–Douglas, `δ = 1`):
  `k_{t+1} = β(1 − α)Ak_t^α/(1 + β)` (`og_growth_log_law`); this path is an equilibrium
  (`og_growth_log_equilibrium`); log-linear dynamics converging
  monotonically to the steady state (`og_growth_log_convergence`, using Miao's
  `op_cd_converge`), and the steady-state gross rate `α(1 + β)/(β(1 − α))`
  (`og_growth_log_rate`), not `α(1 + β)/(1 − α)` as printed
  (`og_growth_log_rate_printed_counterexample`); it is below one iff `α < β/(1 + 2β)`
  (`og_growth_log_rate_lt_one`), and `β(1 − δ + F₁) = 1` fails in general
  (`og_growth_not_smoothed`).
* Comparisons (§5.5.3): the dynastic long-run gross rate with growth `γ` is `(1 + γ)^σ/β`
  (`og_dynastic_long_run_rate`); with pure altruism the long-run rate is `1/β̃`
  (`og_altruism_rate`), proved from the parent's Bellman equation by two deviations.

Not formalised: the perpetual-youth and warm-glow discussions (verbal), and the remark that
uniqueness of `k_{t+1}` is not obvious (no claim).
-/

namespace AKMM.CompetitiveEquilibrium

open Filter Topology StokeyLucasPrescott.EquilibriumApplications

/-! ### The endowment economy -/

/-- The young's saving `a` is optimal: `max u(ω_y − qa) + βu(ω_o′ + a)` over saving with positive
consumptions (AKMM, Definition 11, p. 153). -/
def OGSavingOpt (u : ℝ → ℝ) (β q ωy ωo' a : ℝ) : Prop :=
  0 < ωy - q * a ∧ 0 < ωo' + a ∧
    ∀ x, 0 < ωy - q * x → 0 < ωo' + x → u (ωy - q * x) + β * u (ωo' + x) ≤
      u (ωy - q * a) + β * u (ωo' + a)

/-- **AKMM, Definition 11, p. 153.** A sequential equilibrium of the endowment OG economy in
which the cohorts `t ≥ t₀` optimize: for those cohorts `c_{y,t} = ω_{y,t} − qₜa_{t+1}`,
`c_{o,t+1} = ω_{o,t+1} + a_{t+1}` with `a_{t+1}` optimal; the initial old consume `ω_{o,0}`;
goods clear at every date. The book writes `t > 0` (`t₀ = 1`); the corrected definition is
`t₀ = 0`. -/
def IsOGEndowEquilibrium (t0 : ℕ) (u : ℝ → ℝ) (β : ℝ) (ωy ωo cy co a q : ℕ → ℝ) : Prop :=
  (∀ t, t0 ≤ t → cy t = ωy t - q t * a (t + 1) ∧ co (t + 1) = ωo (t + 1) + a (t + 1) ∧
      OGSavingOpt u β (q t) (ωy t) (ωo (t + 1)) (a (t + 1))) ∧
    co 0 = ωo 0 ∧ ∀ t, cy t + co t = ωy t + ωo t

/-- **AKMM, pp. 153–154: autarky.** In an equilibrium (`t₀ = 0`) with nonzero prices,
`a_{t+1} = 0` and `(c_{y,t}, c_{o,t}) = (ω_{y,t}, ω_{o,t})` at every date. -/
theorem og_autarky {u : ℝ → ℝ} {β : ℝ} {ωy ωo cy co a q : ℕ → ℝ}
    (he : IsOGEndowEquilibrium 0 u β ωy ωo cy co a q) (hq : ∀ t, q t ≠ 0) :
    ∀ t, a (t + 1) = 0 ∧ cy t = ωy t ∧ co t = ωo t := by
  obtain ⟨hopt, hco0, hclear⟩ := he
  have hco : ∀ t, co t = ωo t ∧ a (t + 1) = 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨hco0, ?_⟩
      obtain ⟨h1, _, _⟩ := hopt 0 le_rfl
      have := hclear 0
      rw [h1, hco0] at this
      exact (mul_eq_zero.1 (by linarith : q 0 * a (0 + 1) = 0)).resolve_left (hq 0)
    | succ t ih =>
      obtain ⟨_, h2, _⟩ := hopt t (Nat.zero_le _)
      have hc : co (t + 1) = ωo (t + 1) := by rw [h2, ih.2, add_zero]
      refine ⟨hc, ?_⟩
      obtain ⟨h1, _, _⟩ := hopt (t + 1) (Nat.zero_le _)
      have := hclear (t + 1)
      rw [h1, hc] at this
      exact (mul_eq_zero.1 (by linarith : q (t + 1) * a (t + 1 + 1) = 0)).resolve_left (hq _)
  intro t
  refine ⟨(hco t).2, ?_, (hco t).1⟩
  obtain ⟨h1, _, _⟩ := hopt t (Nat.zero_le _)
  rw [h1, (hco t).2, mul_zero, sub_zero]

/-- **AKMM, p. 154: the Euler equation at autarky.** If saving `0` is optimal and `u` has
derivatives at `ω_y` and `ω_o′`, then `qu′(ω_y) = βu′(ω_o′)`. -/
theorem og_euler_autarky {u : ℝ → ℝ} {β q ωy ωo' dy do' : ℝ} (hopt : OGSavingOpt u β q ωy ωo' 0)
    (hdy : HasDerivAt u dy ωy) (hdo : HasDerivAt u do' ωo') : q * dy = β * do' := by
  obtain ⟨hy, ho, hmax⟩ := hopt
  simp only [mul_zero, sub_zero, add_zero] at hy ho hmax
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < ωy - q * x ∧ 0 < ωo' + x := by
    have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < ωy - q * x :=
      continuousAt_const.eventually_lt
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt (by simpa using hy)
    have h2 : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < ωo' + x :=
      continuousAt_const.eventually_lt (continuous_const.add continuous_id).continuousAt
        (by simpa using ho)
    exact h1.and h2
  have hloc : IsLocalMax (fun x => u (ωy - q * x) + β * u (ωo' + x)) 0 := by
    filter_upwards [hev] with x hx
    have := hmax x hx.1 hx.2
    simpa using this
  have hd : HasDerivAt (fun x => u (ωy - q * x) + β * u (ωo' + x)) (dy * (-q) + β * do') 0 := by
    have hA : HasDerivAt (fun x => u (ωy - q * x)) (dy * (-q)) 0 := by
      have hin : HasDerivAt (fun x : ℝ => ωy - q * x) (-q) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub ωy
      have hu : HasDerivAt u dy (ωy - q * 0) := by simpa using hdy
      exact hu.comp 0 hin
    have hB : HasDerivAt (fun x => u (ωo' + x)) do' 0 := by
      have hu : HasDerivAt u do' (ωo' + 0) := by simpa using hdo
      simpa using hu.comp_const_add ωo' 0
    exact hA.add (hB.const_mul β)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, (5.24), p. 154.** With `u = sgCRRA σ` (`(c^{1−σ} − 1)/(1 − σ)`, log at `σ = 1`),
and positive endowments, an equilibrium (`t₀ = 0`) with positive prices has
`qₜ = β(ω_{y,t}/ω_{o,t+1})^σ`. -/
theorem eq_5_24 {σ β : ℝ} {ωy ωo cy co a q : ℕ → ℝ}
    (he : IsOGEndowEquilibrium 0 (sgCRRA σ) β ωy ωo cy co a q) (hq : ∀ t, 0 < q t)
    (hωy : ∀ t, 0 < ωy t) (hωo : ∀ t, 0 < ωo t) (t : ℕ) :
    q t = β * (ωy t / ωo (t + 1)) ^ σ := by
  have ha := (og_autarky he fun t => (hq t).ne') t
  have hopt := (he.1 t (Nat.zero_le _)).2.2
  rw [ha.1] at hopt
  have h := og_euler_autarky hopt (sgCRRA_hasDerivAt (hωy t)) (sgCRRA_hasDerivAt (hωo (t + 1)))
  have hy := Real.rpow_pos_of_pos (hωy t) (-σ)
  rw [Real.div_rpow (hωy t).le (hωo (t + 1)).le, Real.rpow_neg (hωy t).le,
    Real.rpow_neg (hωo (t + 1)).le] at *
  have := (Real.rpow_pos_of_pos (hωy t) σ).ne'
  have := (Real.rpow_pos_of_pos (hωo (t + 1)) σ).ne'
  field_simp at h ⊢
  linarith

/-- The CRRA cohort problem has autarky as its optimum at `q = β(ω_y/ω_o′)^σ`. -/
theorem og_saving_autarky_opt {σ β ωy ωo' : ℝ} (hσ : 0 < σ) (hβ : 0 ≤ β) (hy : 0 < ωy)
    (ho : 0 < ωo') : OGSavingOpt (sgCRRA σ) β (β * (ωy / ωo') ^ σ) ωy ωo' 0 := by
  refine ⟨by simpa using hy, by simpa using ho, fun x hx1 hx2 => ?_⟩
  simp only [mul_zero, sub_zero, add_zero]
  have t1 := sgCRRA_tangent hσ hy hx1
  have t2 := sgCRRA_tangent hσ ho hx2
  have key : ωy ^ (-σ) * (β * (ωy / ωo') ^ σ) = β * ωo' ^ (-σ) := by
    rw [Real.div_rpow hy.le ho.le, Real.rpow_neg hy.le, Real.rpow_neg ho.le]
    have := (Real.rpow_pos_of_pos hy σ).ne'
    have := (Real.rpow_pos_of_pos ho σ).ne'
    field_simp
  have h2 := mul_le_mul_of_nonneg_left t2 hβ
  nlinarith [key]

/-- **AKMM, p. 154: autarky is an equilibrium.** With CRRA utility, `β ≥ 0` and positive
endowments, `qₜ = β(ω_{y,t}/ω_{o,t+1})^σ`, `a_{t+1} = 0` and autarkic consumption form an
equilibrium (Definition 11, `t₀ = 0`). -/
theorem og_autarky_equilibrium {σ β : ℝ} {ωy ωo : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hωy : ∀ t, 0 < ωy t) (hωo : ∀ t, 0 < ωo t) :
    IsOGEndowEquilibrium 0 (sgCRRA σ) β ωy ωo ωy ωo (fun _ => 0)
      (fun t => β * (ωy t / ωo (t + 1)) ^ σ) := by
  refine ⟨fun t _ => ⟨by ring, by ring, og_saving_autarky_opt hσ hβ (hωy t) (hωo (t + 1))⟩,
    rfl, fun _ => rfl⟩

/-- **AKMM, p. 154: negative real interest rates.** With stationary endowments `ω_y = 2`,
`ω_o = 1`, log utility and `β = 9/10`, the equilibrium price is `q = 9/5 > 1`. -/
theorem og_negative_rate_example :
    IsOGEndowEquilibrium 0 (sgCRRA 1) (9 / 10) (fun _ => 2) (fun _ => 1) (fun _ => 2)
      (fun _ => 1) (fun _ => 0) (fun _ => 9 / 5) ∧ (1 : ℝ) < 9 / 5 := by
  refine ⟨?_, by norm_num⟩
  have h := og_autarky_equilibrium (σ := 1) (β := 9 / 10) (ωy := fun _ => 2) (ωo := fun _ => 1)
    one_pos (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
  have e : (fun _ : ℕ => (9 / 10 : ℝ) * (2 / 1) ^ (1 : ℝ)) = fun _ => 9 / 5 := by
    funext; norm_num
  rwa [e] at h

/-- **AKMM, p. 154: the dynastic comparison.** In the dynastic endowment economy with CRRA
prices `pₜ = βᵗ(Y₀/Yₜ)^σ` and aggregate endowment `Yₜ = Y₀γᵗ` (`Y₀, γ > 0`), the one-period
price is `p_{t+1}/pₜ = βγ^{−σ}`; with `β < 1` and `σ > 0` it exceeds one only if `γ < 1`, a
falling aggregate endowment. -/
theorem og_dynastic_rate {β σ γ Y0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hγ : 0 < γ)
    (hY0 : 0 < Y0) (t : ℕ) :
    let p : ℕ → ℝ := fun t => β ^ t * (Y0 / (Y0 * γ ^ t)) ^ σ
    p (t + 1) / p t = β * γ ^ (-σ) ∧ (1 < p (t + 1) / p t → γ < 1) := by
  intro p
  have hgt : ∀ t, Y0 / (Y0 * γ ^ t) = (γ ^ t)⁻¹ := fun t => by
    have := hY0.ne'; have := (pow_pos hγ t).ne'; field_simp
  have hratio : p (t + 1) / p t = β * γ ^ (-σ) := by
    simp only [p]
    rw [hgt, hgt, pow_succ γ t, mul_inv, Real.mul_rpow (inv_pos.2 (pow_pos hγ t)).le
      (inv_pos.2 hγ).le, Real.inv_rpow hγ.le, Real.rpow_neg hγ.le, pow_succ β t]
    have := (pow_pos hβ0 t).ne'
    have := (Real.rpow_pos_of_pos (inv_pos.2 (pow_pos hγ t)) σ).ne'
    field_simp
  refine ⟨hratio, fun h => ?_⟩
  rw [hratio] at h
  by_contra hγ1
  have hγ1' : 1 ≤ γ := not_lt.1 hγ1
  have : γ ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hγ1' (by linarith)
  nlinarith

/-- **AKMM, Definition 11 as printed is too weak.** If only cohorts `t > 0` optimize
(`t₀ = 1`), the price `q₀` is not determined: with log utility, `β = 1/2` and unit endowments,
autarky with `q₀ = 1` and `qₜ = 1/2` for `t ≥ 1` satisfies the printed definition, but (5.24)
requires `q₀ = β(ω_{y,0}/ω_{o,1}) = 1/2`. -/
theorem definition_11_printed_counterexample :
    let q : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
    IsOGEndowEquilibrium 1 (sgCRRA 1) (1 / 2) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 0) q ∧ q 0 ≠ 1 / 2 * (1 / 1) ^ (1 : ℝ) := by
  intro q
  refine ⟨⟨fun t ht => ⟨by ring, by ring, ?_⟩, rfl, fun _ => rfl⟩, by norm_num [q]⟩
  have hq : q t = 1 / 2 * (1 / 1) ^ (1 : ℝ) := by
    simp only [q, show t ≠ 0 by omega, ite_false]; norm_num
  rw [hq]
  exact og_saving_autarky_opt one_pos (by norm_num) one_pos one_pos

/-! ### The production economy -/

/-- The young's choice `k′` is optimal: `max u(w eᵧ − x) + βu(w′eₒ + R′x)` over `x` with positive
consumptions (AKMM, Definition 12, p. 155). -/
def OGCapitalOpt (u : ℝ → ℝ) (β ey eo w w' R' k' : ℝ) : Prop :=
  0 < w * ey - k' ∧ 0 < w' * eo + R' * k' ∧
    ∀ x, 0 < w * ey - x → 0 < w' * eo + R' * x →
      u (w * ey - x) + β * u (w' * eo + R' * x) ≤ u (w * ey - k') + β * u (w' * eo + R' * k')

/-- **AKMM, Definition 12, p. 155.** A sequential equilibrium of the OG growth economy in which
the cohorts `t ≥ t₀` optimize (the book writes `t > 0`): budgets and optimal saving for those
cohorts, the initial old consume `w₀eₒ + (1 − δ + r₀)k₀`, prices are marginal products
`rₜ = F₁(kₜ)`, `wₜ = F₂(kₜ)`, and `c_{y,t} + c_{o,t} + k_{t+1} = F(kₜ) + (1 − δ)kₜ`. -/
def IsOGGrowthEquilibrium (t0 : ℕ) (u : ℝ → ℝ) (β δ ey eo k0 : ℝ) (F F1 F2 : ℝ → ℝ)
    (cy co k r w : ℕ → ℝ) : Prop :=
  (∀ t, t0 ≤ t → cy t = w t * ey - k (t + 1) ∧
      co (t + 1) = w (t + 1) * eo + (1 - δ + r (t + 1)) * k (t + 1) ∧
      OGCapitalOpt u β ey eo (w t) (w (t + 1)) (1 - δ + r (t + 1)) (k (t + 1))) ∧
    co 0 = w 0 * eo + (1 - δ + r 0) * k0 ∧ k 0 = k0 ∧ (∀ t, r t = F1 (k t) ∧ w t = F2 (k t)) ∧
    ∀ t, cy t + co t + k (t + 1) = F (k t) + (1 - δ) * k t

/-- **AKMM, p. 155: the Euler equation as a first-order difference equation.** In an
equilibrium (`t₀ = 0`) with `u` differentiable,
`u′(e_yF₂(kₜ) − k_{t+1}) =
βu′(e_oF₂(k_{t+1}) + (1 − δ + F₁(k_{t+1}))k_{t+1})(1 − δ + F₁(k_{t+1}))`. -/
theorem og_growth_euler {u du : ℝ → ℝ} {β δ ey eo k0 : ℝ} {F F1 F2 : ℝ → ℝ}
    {cy co k r w : ℕ → ℝ} (he : IsOGGrowthEquilibrium 0 u β δ ey eo k0 F F1 F2 cy co k r w)
    (hd : ∀ c, 0 < c → HasDerivAt u (du c) c) (t : ℕ) :
    du (ey * F2 (k t) - k (t + 1)) =
      β * du (eo * F2 (k (t + 1)) + (1 - δ + F1 (k (t + 1))) * k (t + 1)) *
        (1 - δ + F1 (k (t + 1))) := by
  obtain ⟨hopt, _, _, hprice, _⟩ := he
  obtain ⟨_, _, hy, ho, hmax⟩ := hopt t (Nat.zero_le _)
  set R := 1 - δ + r (t + 1) with hR
  set cY := w t * ey - k (t + 1)
  set cO := w (t + 1) * eo + R * k (t + 1)
  have hev : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < w t * ey - x ∧ 0 < w (t + 1) * eo + R * x := by
    have h1 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < w t * ey - x :=
      continuousAt_const.eventually_lt (continuous_const.sub continuous_id).continuousAt hy
    have h2 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < w (t + 1) * eo + R * x :=
      continuousAt_const.eventually_lt
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt ho
    exact h1.and h2
  have hloc : IsLocalMax (fun x => u (w t * ey - x) + β * u (w (t + 1) * eo + R * x))
      (k (t + 1)) := by
    filter_upwards [hev] with x hx using hmax x hx.1 hx.2
  have hD : HasDerivAt (fun x => u (w t * ey - x) + β * u (w (t + 1) * eo + R * x))
      (du cY * (-1) + β * (du cO * R)) (k (t + 1)) := by
    have hA : HasDerivAt (fun x => u (w t * ey - x)) (du cY * (-1)) (k (t + 1)) := by
      have hin : HasDerivAt (fun x : ℝ => w t * ey - x) (-1) (k (t + 1)) := by
        simpa using (hasDerivAt_id (k (t + 1))).const_sub (w t * ey)
      exact (hd cY hy).comp (k (t + 1)) hin
    have hB : HasDerivAt (fun x => u (w (t + 1) * eo + R * x)) (du cO * R) (k (t + 1)) := by
      have hin : HasDerivAt (fun x : ℝ => w (t + 1) * eo + R * x) R (k (t + 1)) := by
        simpa using ((hasDerivAt_id (k (t + 1))).const_mul R).const_add (w (t + 1) * eo)
      exact (hd cO ho).comp (k (t + 1)) hin
    exact hA.add (hB.const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hD
  have e1 : cY = ey * F2 (k t) - k (t + 1) := by
    simp only [cY]; rw [(hprice t).2]; ring
  have e2 : cO = eo * F2 (k (t + 1)) + (1 - δ + F1 (k (t + 1))) * k (t + 1) := by
    simp only [cO, hR]; rw [(hprice (t + 1)).2, (hprice (t + 1)).1]; ring
  rw [← e1, ← e2, ← (hprice (t + 1)).1, ← hR]
  linarith

/-- **AKMM, p. 155: the steady state.** On a constant path `kₜ = k̄` the Euler equation reads
`u′(e_yF₂(k̄) − k̄) = βu′(e_oF₂(k̄) + (1 − δ + F₁(k̄))k̄)(1 − δ + F₁(k̄))`. -/
theorem og_growth_steady {u du : ℝ → ℝ} {β δ ey eo k0 kbar : ℝ} {F F1 F2 : ℝ → ℝ}
    {cy co r w : ℕ → ℝ}
    (he : IsOGGrowthEquilibrium 0 u β δ ey eo k0 F F1 F2 cy co (fun _ => kbar) r w)
    (hd : ∀ c, 0 < c → HasDerivAt u (du c) c) :
    du (ey * F2 kbar - kbar) =
      β * du (eo * F2 kbar + (1 - δ + F1 kbar) * kbar) * (1 - δ + F1 kbar) :=
  og_growth_euler he hd 0

/-- **AKMM, p. 156, the exercise: the law of motion.** With log utility, `e_y = 1`, `e_o = 0`,
`F₂(k) = (1 − α)Ak^α`, `δ = 1` and `F₁(k′) > 0`, the Euler equation
`1/(F₂(k) − k′) = β(1/(F₁(k′)k′))F₁(k′)` gives `k′ = β(1 − α)Ak^α/(1 + β)`. -/
theorem og_growth_log_law {α β A k k' R : ℝ} (hk' : 0 < k') (hR : 0 < R)
    (hc : 0 < (1 - α) * A * k ^ α - k')
    (heul : ((1 - α) * A * k ^ α - k')⁻¹ = β * (R * k')⁻¹ * R) :
    k' = β * (1 - α) * A * k ^ α / (1 + β) := by
  have hβ : 0 ≤ β ∨ β < 0 := le_or_gt 0 β
  have := hc.ne'
  have := hk'.ne'
  have := hR.ne'
  field_simp at heul
  have h1 : (1 : ℝ) + β ≠ 0 := by
    intro h
    have : β = -1 := by linarith
    rw [this] at heul
    nlinarith
  field_simp
  linarith

/-- **AKMM, p. 156, the exercise: log-linear dynamics and monotone convergence.** If
`k_{t+1} = ck_t^α` with `c > 0`, `0 < α < 1` and `k₀ > 0`, then `log k_{t+1} = log c + α log kₜ`,
`kₜ` converges to `k* = c^{1/(1−α)}` (Miao's `op_cd_converge`), and the path is monotone:
increasing if `k₀ ≤ k*`, decreasing if `k₀ ≥ k*`. -/
theorem og_growth_log_convergence {c α : ℝ} {k : ℕ → ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    (hk0 : 0 < k 0) (hlaw : ∀ t, k (t + 1) = c * k t ^ α) :
    (∀ t, Real.log (k (t + 1)) = Real.log c + α * Real.log (k t)) ∧
      Tendsto k atTop (𝓝 (Miao.OverlappingGenerations.opKstarCD c α)) ∧
      (k 0 ≤ Miao.OverlappingGenerations.opKstarCD c α → Monotone k) ∧
      (Miao.OverlappingGenerations.opKstarCD c α ≤ k 0 → Antitone k) := by
  obtain ⟨hpos, hlim⟩ := Miao.OverlappingGenerations.op_cd_converge hc hα0 hα1 hk0 hlaw
  have hloglin : ∀ t, Real.log (k (t + 1)) = Real.log c + α * Real.log (k t) := by
    intro t
    rw [hlaw, Real.log_mul hc.ne' (Real.rpow_pos_of_pos (hpos t) α).ne',
      Real.log_rpow (hpos t)]
  set ks := Miao.OverlappingGenerations.opKstarCD c α with hks
  have hkspos : 0 < ks := Miao.OverlappingGenerations.op_kstarCD_pos hc
  have hL : Real.log ks = Real.log c / (1 - α) := by
    rw [hks, Miao.OverlappingGenerations.opKstarCD, Real.log_rpow hc]; ring
  have h1 : (1 - α) ≠ 0 := by linarith
  -- `log k_{t+1} − log k* = α (log kₜ − log k*)`
  have hdev : ∀ t, Real.log (k (t + 1)) - Real.log ks = α * (Real.log (k t) - Real.log ks) := by
    intro t; rw [hloglin, hL]; field_simp; ring
  -- the deviation keeps its sign, and the step `log k_{t+1} − log kₜ = (1 − α)(log k* − log kₜ)`
  have hstep : ∀ t, Real.log (k (t + 1)) - Real.log (k t) =
      (1 - α) * (Real.log ks - Real.log (k t)) := by
    intro t; have := hdev t; linarith
  have hsign : ∀ t, (Real.log (k t) - Real.log ks) =
      α ^ t * (Real.log (k 0) - Real.log ks) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hdev, ih, pow_succ]; ring
  refine ⟨hloglin, hlim, fun hle => ?_, fun hge => ?_⟩
  · apply monotone_nat_of_le_succ
    intro t
    have h0 : Real.log (k 0) - Real.log ks ≤ 0 := by
      have := Real.log_le_log hk0 hle; linarith
    have ht : Real.log (k t) - Real.log ks ≤ 0 := by
      rw [hsign]; exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hα0.le t) h0
    have : Real.log (k t) ≤ Real.log (k (t + 1)) := by
      have := hstep t; nlinarith
    exact (Real.log_le_log_iff (hpos t) (hpos (t + 1))).1 this
  · apply antitone_nat_of_succ_le
    intro t
    have h0 : 0 ≤ Real.log (k 0) - Real.log ks := by
      have := Real.log_le_log hkspos hge; linarith
    have ht : 0 ≤ Real.log (k t) - Real.log ks := by
      rw [hsign]; exact mul_nonneg (pow_nonneg hα0.le t) h0
    have : Real.log (k (t + 1)) ≤ Real.log (k t) := by
      have := hstep t; nlinarith
    exact (Real.log_le_log_iff (hpos (t + 1)) (hpos t)).1 this

/-- **AKMM, p. 156, the exercise solved: an equilibrium.** With log utility, `β > 0`,
`e_y = 1`, `e_o = 0`, `F(k) = Ak^α` (`A > 0`, `0 < α < 1`), `δ = 1` and `k₀ > 0`, the path
`k_{t+1} = β(1 − α)Ak_t^α/(1 + β)` with marginal-product prices, `c_{y,t} = wₜ − k_{t+1}` and
`c_{o,t} = rₜkₜ` is an equilibrium (Definition 12, `t₀ = 0`). -/
theorem og_growth_log_equilibrium {A α β k0 : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hk0 : 0 < k0) :
    let F : ℝ → ℝ := fun k => A * k ^ α
    let F1 : ℝ → ℝ := fun k => α * A * k ^ (α - 1)
    let F2 : ℝ → ℝ := fun k => (1 - α) * A * k ^ α
    let k : ℕ → ℝ := fun t => Nat.rec k0 (fun _ kt => β * (1 - α) * A * kt ^ α / (1 + β)) t
    IsOGGrowthEquilibrium 0 Real.log β 1 1 0 k0 F F1 F2
      (fun t => F2 (k t) - k (t + 1)) (fun t => F1 (k t) * k t) k
      (fun t => F1 (k t)) (fun t => F2 (k t)) := by
  intro F F1 F2 k
  have hks : ∀ t, k (t + 1) = β * (1 - α) * A * k t ^ α / (1 + β) := fun _ => rfl
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      rw [hks]; have := Real.rpow_pos_of_pos ih α
      have : 0 < 1 - α := by linarith
      positivity
  have hwpos : ∀ t, 0 < F2 (k t) := fun t =>
    mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos (hkpos t) _)
  have hrpos : ∀ t, 0 < F1 (k t) := fun t =>
    mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos (hkpos t) _)
  -- `k_{t+1} = β(wₜ − k_{t+1})`
  have hsave : ∀ t, k (t + 1) = β * (F2 (k t) - k (t + 1)) := by
    intro t; rw [hks]; simp only [F2]; field_simp; ring
  have hcy : ∀ t, 0 < F2 (k t) - k (t + 1) := by
    intro t
    have h := hsave t
    have := hkpos (t + 1)
    by_contra hc
    have : β * (F2 (k t) - k (t + 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ.le (not_lt.1 hc)
    linarith
  refine ⟨fun t _ => ⟨by ring, by ring, ?_⟩, by simp only; rw [show k 0 = k0 from rfl]; ring, rfl,
    fun t => ⟨rfl, rfl⟩, fun t => ?_⟩
  · refine ⟨by simpa using hcy t, by simpa using mul_pos (hrpos (t + 1)) (hkpos (t + 1)),
      fun x hx1 hx2 => ?_⟩
    simp only [mul_one, mul_zero, zero_add, sub_self] at hx1 hx2 ⊢
    have hR := hrpos (t + 1)
    have hkn := hkpos (t + 1)
    have t1 := ce_log_tangent (hcy t) hx1
    have t2 := ce_log_tangent (mul_pos hR hkn) hx2
    have hsv := hsave t
    have hq : β / k (t + 1) = (F2 (k t) - k (t + 1))⁻¹ := by
      rw [div_eq_iff hkn.ne']
      have := (hcy t).ne'
      field_simp
      linarith
    have e : β * ((F1 (k (t + 1)) * k (t + 1))⁻¹ *
        (F1 (k (t + 1)) * x - F1 (k (t + 1)) * k (t + 1))) =
        β / k (t + 1) * (x - k (t + 1)) := by
      have := hR.ne'; have := hkn.ne'
      field_simp
    rw [hq] at e
    have e2 : (F2 (k t) - k (t + 1))⁻¹ * (F2 (k t) - x - (F2 (k t) - k (t + 1))) =
        -((F2 (k t) - k (t + 1))⁻¹ * (x - k (t + 1))) := by ring
    have h2 := mul_le_mul_of_nonneg_left t2 hβ.le
    rw [mul_add] at h2
    linarith
  · simp only [F, F1, F2]
    rw [Real.rpow_sub_one (hkpos t).ne']
    have := (hkpos t).ne'
    field_simp
    ring

/-- **AKMM, p. 156, corrected: the steady-state gross rate.** At the steady state
`k̄ = β(1 − α)Ak̄^α/(1 + β)` (`k̄ > 0`, `0 < β`, `α < 1`, `A > 0`), the gross rate is
`αAk̄^{α−1} = α(1 + β)/(β(1 − α))`. -/
theorem og_growth_log_rate {α β A kbar : ℝ} (hk : 0 < kbar) (hβ : 0 < β) (hα1 : α < 1)
    (hA : 0 < A) (hss : kbar = β * (1 - α) * A * kbar ^ α / (1 + β)) :
    α * A * kbar ^ (α - 1) = α * (1 + β) / (β * (1 - α)) := by
  rw [Real.rpow_sub_one hk.ne']
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h2 : kbar ^ α = kbar * (1 + β) / (β * (1 - α) * A) := by
    have := hA.ne'; have := hβ.ne'
    field_simp
    field_simp at hss
    linarith
  rw [h2]
  have := hk.ne'; have := hA.ne'; have := hβ.ne'
  have : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp

/-- **AKMM, p. 156: the printed rate `α(1 + β)/(1 − α)` is wrong.** For `0 < α < 1` and
`0 < β < 1` it differs from the correct `α(1 + β)/(β(1 − α))`; e.g. at `α = 3/10`, `β = 9/10`
the correct rate is `19/21` while the printed one is `57/70`. -/
theorem og_growth_log_rate_printed_counterexample {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    α * (1 + β) / (β * (1 - α)) ≠ α * (1 + β) / (1 - α) ∧
      (3 / 10 : ℝ) * (1 + 9 / 10) / (9 / 10 * (1 - 3 / 10)) = 19 / 21 ∧
      (3 / 10 : ℝ) * (1 + 9 / 10) / (1 - 3 / 10) = 57 / 70 := by
  refine ⟨fun h => ?_, by norm_num, by norm_num⟩
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hpos : 0 < α * (1 + β) := by positivity
  field_simp at h
  have : α * (1 + β) * (1 - β) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- **AKMM, p. 156: the rate is below one for low `α`.** For `0 < α < 1` and `β > 0`, the gross
rate `α(1 + β)/(β(1 − α))` is below one iff `α < β/(1 + 2β)`. -/
theorem og_growth_log_rate_lt_one {α β : ℝ} (hα1 : α < 1) (hβ : 0 < β) :
    α * (1 + β) / (β * (1 - α)) < 1 ↔ α < β / (1 + 2 * β) := by
  have h1 : 0 < β * (1 - α) := mul_pos hβ (by linarith)
  have h2 : 0 < 1 + 2 * β := by linarith
  rw [div_lt_one h1, lt_div_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 155: consumption is not fully smoothed.** In the exercise's steady state,
`β(1 − δ + F₁(k̄)) = α(1 + β)/(1 − α)` (with `δ = 1`), which equals one only if
`α(1 + β) = 1 − α`; at `α = 3/10`, `β = 9/10` it is `57/70 ≠ 1`. -/
theorem og_growth_not_smoothed {α β : ℝ} (hα1 : α < 1) (hβ : 0 < β) :
    (β * (α * (1 + β) / (β * (1 - α))) = 1 ↔ α * (1 + β) = 1 - α) ∧
      (9 / 10 : ℝ) * ((3 / 10) * (1 + 9 / 10) / (9 / 10 * (1 - 3 / 10))) ≠ 1 := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  refine ⟨?_, by norm_num⟩
  have e : β * (α * (1 + β) / (β * (1 - α))) = α * (1 + β) / (1 - α) := by
    have := hβ.ne'; field_simp
  rw [e, div_eq_one_iff_eq h1]

/-! ### Model comparisons -/

/-- **AKMM, p. 156: the dynastic long-run rate.** If `u′(c) = c^{−σ}`, consumption grows at gross
rate `1 + γ > 0` and the Euler equation `u′(cₜ) = βRu′(c_{t+1})` holds with `cₜ > 0`, `β > 0`,
then `R = (1 + γ)^σ/β`. -/
theorem og_dynastic_long_run_rate {σ β γ R c : ℝ} (hc : 0 < c) (hγ : 0 < 1 + γ) (hβ : 0 < β)
    (heul : c ^ (-σ) = β * R * ((1 + γ) * c) ^ (-σ)) : R = (1 + γ) ^ σ / β := by
  rw [Real.mul_rpow hγ.le hc.le, Real.rpow_neg hγ.le] at heul
  have hcs := (Real.rpow_pos_of_pos hc (-σ)).ne'
  have hgs := (Real.rpow_pos_of_pos hγ σ).ne'
  have := hβ.ne'
  field_simp at heul
  field_simp
  linarith

/-- **AKMM, p. 157: pure altruism gives the long-run rate `1/β̃`.** Let the parent's value
`φ` satisfy the Bellman inequality
`u(ω_y + b − qa′) + βu(ω_o + a′ − b′) + β̃φ(b′) ≤ φ(b)` for all choices with consumptions in the
open set `S`, and let a stationary choice `(a*, b*)` (bequest `b′ = b*`) attain it at `b*`.
If `β̃ ≥ 0` and `u` is differentiable at the stationary consumptions with `u′(c_y) ≠ 0`, then
`q = β̃`. -/
theorem og_altruism_rate {u : ℝ → ℝ} {S : Set ℝ} {β βt q ωy ωo as bs dy do' : ℝ}
    {φ : ℝ → ℝ} (hS : IsOpen S) (hβt : 0 ≤ βt)
    (hbell : ∀ b a' b', ωy + b - q * a' ∈ S → ωo + a' - b' ∈ S →
      u (ωy + b - q * a') + β * u (ωo + a' - b') + βt * φ b' ≤ φ b)
    (hatt : φ bs = u (ωy + bs - q * as) + β * u (ωo + as - bs) + βt * φ bs)
    (hy : ωy + bs - q * as ∈ S) (ho : ωo + as - bs ∈ S)
    (hdy : HasDerivAt u dy (ωy + bs - q * as)) (hdo : HasDerivAt u do' (ωo + as - bs))
    (hdy0 : dy ≠ 0) : q = βt := by
  set cy := ωy + bs - q * as with hcy
  set co := ωo + as - bs with hco
  -- deviation 1: save `ε` more
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), cy - q * ε ∈ S ∧ co + ε ∈ S := by
    have c1 : ContinuousAt (fun ε : ℝ => cy - q * ε) 0 :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
    have c2 : ContinuousAt (fun ε : ℝ => co + ε) 0 :=
      (continuous_const.add continuous_id).continuousAt
    exact (c1.eventually_mem (hS.mem_nhds (by simpa using hy))).and
      (c2.eventually_mem (hS.mem_nhds (by simpa using ho)))
  have hloc1 : IsLocalMax (fun ε => u (cy - q * ε) + β * u (co + ε)) 0 := by
    filter_upwards [hev1] with ε hε
    have h := hbell bs (as + ε) bs (by rw [hcy] at hε; convert hε.1 using 1; ring)
      (by rw [hco] at hε; convert hε.2 using 1; ring)
    have e1 : ωy + bs - q * (as + ε) = cy - q * ε := by rw [hcy]; ring
    have e2 : ωo + (as + ε) - bs = co + ε := by rw [hco]; ring
    rw [e1, e2] at h
    simp only [mul_zero, sub_zero, add_zero]
    linarith
  have hd1 : HasDerivAt (fun ε => u (cy - q * ε) + β * u (co + ε)) (dy * (-q) + β * do') 0 := by
    have hA : HasDerivAt (fun ε => u (cy - q * ε)) (dy * (-q)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => cy - q * ε) (-q) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub cy
      have hu : HasDerivAt u dy (cy - q * 0) := by simpa using hdy
      exact hu.comp 0 hin
    have hB : HasDerivAt (fun ε => u (co + ε)) do' 0 := by
      have hu : HasDerivAt u do' (co + 0) := by simpa using hdo
      simpa using hu.comp_const_add co 0
    exact hA.add (hB.const_mul β)
  have hz1 := hloc1.hasDerivAt_eq_zero hd1
  -- deviation 2: bequeath `ε` less for one generation
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), co + ε ∈ S ∧ cy - ε ∈ S := by
    have c1 : ContinuousAt (fun ε : ℝ => co + ε) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have c2 : ContinuousAt (fun ε : ℝ => cy - ε) 0 :=
      (continuous_const.sub continuous_id).continuousAt
    exact (c1.eventually_mem (hS.mem_nhds (by simpa using ho))).and
      (c2.eventually_mem (hS.mem_nhds (by simpa using hy)))
  have hloc2 : IsLocalMax (fun ε => β * u (co + ε) + βt * u (cy - ε)) 0 := by
    filter_upwards [hev2] with ε hε
    have hA := hbell bs as (bs - ε) hy (by rw [hco] at hε; convert hε.1 using 1; ring)
    have hB := hbell (bs - ε) as bs (by rw [hcy] at hε; convert hε.2 using 1; ring) ho
    have e1 : ωo + as - (bs - ε) = co + ε := by rw [hco]; ring
    have e2 : ωy + (bs - ε) - q * as = cy - ε := by rw [hcy]; ring
    rw [e1, ← hcy] at hA
    rw [e2, ← hco] at hB
    simp only [add_zero, sub_zero]
    have hB' := mul_le_mul_of_nonneg_left hB hβt
    have hatt2 : φ bs = u cy + β * u co + βt * (u cy + β * u co + βt * φ bs) := by
      rw [← hatt]; exact hatt
    linarith
  have hd2 : HasDerivAt (fun ε => β * u (co + ε) + βt * u (cy - ε)) (β * do' + βt * (dy * (-1)))
      0 := by
    have hA : HasDerivAt (fun ε => u (co + ε)) do' 0 := by
      have hu : HasDerivAt u do' (co + 0) := by simpa using hdo
      simpa using hu.comp_const_add co 0
    have hB : HasDerivAt (fun ε => u (cy - ε)) (dy * (-1)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => cy - ε) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub cy
      have hu : HasDerivAt u dy (cy - 0) := by simpa using hdy
      exact hu.comp 0 hin
    exact (hA.const_mul β).add (hB.const_mul βt)
  have hz2 := hloc2.hasDerivAt_eq_zero hd2
  have : (q - βt) * dy = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hdy0

end AKMM.CompetitiveEquilibrium

set_option linter.style.longLine false
#print axioms AKMM.CompetitiveEquilibrium.ce_tsum_perturb
#print axioms AKMM.CompetitiveEquilibrium.ce_foc_of_perturb
#print axioms AKMM.CompetitiveEquilibrium.ADBudget
#print axioms AKMM.CompetitiveEquilibrium.ADOptimal
#print axioms AKMM.CompetitiveEquilibrium.ad_foc
#print axioms AKMM.CompetitiveEquilibrium.ad_foc_multiplier
#print axioms AKMM.CompetitiveEquilibrium.eq_5_3
#print axioms AKMM.CompetitiveEquilibrium.ad_foc_sufficient
#print axioms AKMM.CompetitiveEquilibrium.ce_crra_tangent
#print axioms AKMM.CompetitiveEquilibrium.ce_log_tangent
#print axioms AKMM.CompetitiveEquilibrium.endow_unitInterval_probability
#print axioms AKMM.CompetitiveEquilibrium.IsADEquilibrium
#print axioms AKMM.CompetitiveEquilibrium.IsADEquilibriumRep
#print axioms AKMM.CompetitiveEquilibrium.endow_log_foc
#print axioms AKMM.CompetitiveEquilibrium.endow_log_price
#print axioms AKMM.CompetitiveEquilibrium.endow_log_growth
#print axioms AKMM.CompetitiveEquilibrium.endow_log_smoothing
#print axioms AKMM.CompetitiveEquilibrium.endowShare
#print axioms AKMM.CompetitiveEquilibrium.endow_log_shares
#print axioms AKMM.CompetitiveEquilibrium.endow_log_representative
#print axioms AKMM.CompetitiveEquilibrium.endow_log_existence
#print axioms AKMM.CompetitiveEquilibrium.endow_log_existence_instance
#print axioms AKMM.CompetitiveEquilibrium.endow_crra_common_growth
#print axioms AKMM.CompetitiveEquilibrium.endow_crra_price
#print axioms AKMM.CompetitiveEquilibrium.endow_crra_growth
#print axioms AKMM.CompetitiveEquilibrium.definition_2_of_identical
#print axioms AKMM.CompetitiveEquilibrium.labourProfit
#print axioms AKMM.CompetitiveEquilibrium.LabourStaticOpt
#print axioms AKMM.CompetitiveEquilibrium.LabourFirmOpt
#print axioms AKMM.CompetitiveEquilibrium.eq_5_6_static
#print axioms AKMM.CompetitiveEquilibrium.labour_firm_fn3
#print axioms AKMM.CompetitiveEquilibrium.labour_wage_eq_productivity
#print axioms AKMM.CompetitiveEquilibrium.LabourBudget
#print axioms AKMM.CompetitiveEquilibrium.LabourOptimal
#print axioms AKMM.CompetitiveEquilibrium.eq_5_8
#print axioms AKMM.CompetitiveEquilibrium.eq_5_9
#print axioms AKMM.CompetitiveEquilibrium.eq_5_10
#print axioms AKMM.CompetitiveEquilibrium.labour_foc_sufficient
#print axioms AKMM.CompetitiveEquilibrium.IsADEquilibriumLabour
#print axioms AKMM.CompetitiveEquilibrium.labour_log_shares
#print axioms AKMM.CompetitiveEquilibrium.labour_log_hours
#print axioms AKMM.CompetitiveEquilibrium.labour_log_equal_hours
#print axioms AKMM.CompetitiveEquilibrium.labour_log_equilibrium
#print axioms AKMM.CompetitiveEquilibrium.labour_log_equilibrium_instance
#print axioms AKMM.CompetitiveEquilibrium.labour_static_wage_independent
#print axioms AKMM.CompetitiveEquilibrium.labour_static_asset_foc
#print axioms AKMM.CompetitiveEquilibrium.labour_static_asset_printed_counterexample
#print axioms AKMM.CompetitiveEquilibrium.labour_assets_lower_hours
#print axioms AKMM.CompetitiveEquilibrium.cdProfit
#print axioms AKMM.CompetitiveEquilibrium.growth_firm_foc
#print axioms AKMM.CompetitiveEquilibrium.growth_firm_optimal
#print axioms AKMM.CompetitiveEquilibrium.growth_firm_ratio
#print axioms AKMM.CompetitiveEquilibrium.GrowthBudget
#print axioms AKMM.CompetitiveEquilibrium.GrowthOptimal
#print axioms AKMM.CompetitiveEquilibrium.eq_5_15
#print axioms AKMM.CompetitiveEquilibrium.eq_5_16
#print axioms AKMM.CompetitiveEquilibrium.eq_5_17
#print axioms AKMM.CompetitiveEquilibrium.growth_consolidated_budget
#print axioms AKMM.CompetitiveEquilibrium.growth_capital_value_tendsto_zero
#print axioms AKMM.CompetitiveEquilibrium.growth_foc_sufficient
#print axioms AKMM.CompetitiveEquilibrium.growth_optimal_instance
#print axioms AKMM.CompetitiveEquilibrium.growth_log_consumption
#print axioms AKMM.CompetitiveEquilibrium.growth_fn6
#print axioms AKMM.CompetitiveEquilibrium.growth_log_hours_common
#print axioms AKMM.CompetitiveEquilibrium.growth_log_aggregate_euler
#print axioms AKMM.CompetitiveEquilibrium.eq_5_18
#print axioms AKMM.CompetitiveEquilibrium.eq_5_19
#print axioms AKMM.CompetitiveEquilibrium.eq_5_20
#print axioms AKMM.CompetitiveEquilibrium.growth_fn7
#print axioms AKMM.CompetitiveEquilibrium.ce_planner_iff
#print axioms AKMM.CompetitiveEquilibrium.growth_planner_foc_K
#print axioms AKMM.CompetitiveEquilibrium.growth_planner_foc_L
#print axioms AKMM.CompetitiveEquilibrium.seqPrice
#print axioms AKMM.CompetitiveEquilibrium.seqPrice_succ
#print axioms AKMM.CompetitiveEquilibrium.seqPrice_pos
#print axioms AKMM.CompetitiveEquilibrium.NoPonzi
#print axioms AKMM.CompetitiveEquilibrium.SeqBudget
#print axioms AKMM.CompetitiveEquilibrium.SeqOptimal
#print axioms AKMM.CompetitiveEquilibrium.IsSeqEquilibrium
#print axioms AKMM.CompetitiveEquilibrium.seq_walras
#print axioms AKMM.CompetitiveEquilibrium.eq_5_21_5_22
#print axioms AKMM.CompetitiveEquilibrium.seq_price_product
#print axioms AKMM.CompetitiveEquilibrium.seq_gross_rate
#print axioms AKMM.CompetitiveEquilibrium.seq_budget_iterate
#print axioms AKMM.CompetitiveEquilibrium.seq_budget_iterate_printed_counterexample
#print axioms AKMM.CompetitiveEquilibrium.seq_lifetime_budget
#print axioms AKMM.CompetitiveEquilibrium.seq_lifetime_budget_eq_iff
#print axioms AKMM.CompetitiveEquilibrium.seqAssets
#print axioms AKMM.CompetitiveEquilibrium.seq_of_lifetime_budget
#print axioms AKMM.CompetitiveEquilibrium.seq_optimal_iff_ad
#print axioms AKMM.CompetitiveEquilibrium.seq_equilibrium_is_ad
#print axioms AKMM.CompetitiveEquilibrium.seq_equilibrium_instance
#print axioms AKMM.CompetitiveEquilibrium.euler_crs
#print axioms AKMM.CompetitiveEquilibrium.seq_growth_walras
#print axioms AKMM.CompetitiveEquilibrium.SSBellman
#print axioms AKMM.CompetitiveEquilibrium.ss_value
#print axioms AKMM.CompetitiveEquilibrium.ss_rate
#print axioms AKMM.CompetitiveEquilibrium.IsSSEquilibriumEndow
#print axioms AKMM.CompetitiveEquilibrium.definition_7_q_eq_beta
#print axioms AKMM.CompetitiveEquilibrium.ss_functional_euler_q
#print axioms AKMM.CompetitiveEquilibrium.ss_functional_euler_id
#print axioms AKMM.CompetitiveEquilibrium.definition_7_any_distribution
#print axioms AKMM.CompetitiveEquilibrium.IsSSEquilibriumGrowth
#print axioms AKMM.CompetitiveEquilibrium.definition_8_rate
#print axioms AKMM.CompetitiveEquilibrium.definition_8_any_distribution
#print axioms AKMM.CompetitiveEquilibrium.definition_8_capital
#print axioms AKMM.CompetitiveEquilibrium.definition_8_printed_counterexample
#print axioms AKMM.CompetitiveEquilibrium.definition_9_resource
#print axioms AKMM.CompetitiveEquilibrium.definition_9_aggregate_euler
#print axioms AKMM.CompetitiveEquilibrium.definition_9_aggregate_euler_printed
#print axioms AKMM.CompetitiveEquilibrium.definition_9_aggregate_euler_printed_instance
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_power
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_linear
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_split
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_mu_lambda
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_printed_attribution_counterexample
#print axioms AKMM.CompetitiveEquilibrium.aggregation_linear
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_closed_form
#print axioms AKMM.CompetitiveEquilibrium.appendix_5A_closed_form_mu_lambda
#print axioms AKMM.CompetitiveEquilibrium.definition_10_planner
#print axioms AKMM.CompetitiveEquilibrium.OGSavingOpt
#print axioms AKMM.CompetitiveEquilibrium.IsOGEndowEquilibrium
#print axioms AKMM.CompetitiveEquilibrium.og_autarky
#print axioms AKMM.CompetitiveEquilibrium.og_euler_autarky
#print axioms AKMM.CompetitiveEquilibrium.eq_5_24
#print axioms AKMM.CompetitiveEquilibrium.og_saving_autarky_opt
#print axioms AKMM.CompetitiveEquilibrium.og_autarky_equilibrium
#print axioms AKMM.CompetitiveEquilibrium.og_negative_rate_example
#print axioms AKMM.CompetitiveEquilibrium.og_dynastic_rate
#print axioms AKMM.CompetitiveEquilibrium.definition_11_printed_counterexample
#print axioms AKMM.CompetitiveEquilibrium.OGCapitalOpt
#print axioms AKMM.CompetitiveEquilibrium.IsOGGrowthEquilibrium
#print axioms AKMM.CompetitiveEquilibrium.og_growth_euler
#print axioms AKMM.CompetitiveEquilibrium.og_growth_steady
#print axioms AKMM.CompetitiveEquilibrium.og_growth_log_law
#print axioms AKMM.CompetitiveEquilibrium.og_growth_log_convergence
#print axioms AKMM.CompetitiveEquilibrium.og_growth_log_equilibrium
#print axioms AKMM.CompetitiveEquilibrium.og_growth_log_rate
#print axioms AKMM.CompetitiveEquilibrium.og_growth_log_rate_printed_counterexample
#print axioms AKMM.CompetitiveEquilibrium.og_growth_log_rate_lt_one
#print axioms AKMM.CompetitiveEquilibrium.og_growth_not_smoothed
#print axioms AKMM.CompetitiveEquilibrium.og_dynastic_long_run_rate
#print axioms AKMM.CompetitiveEquilibrium.og_altruism_rate
