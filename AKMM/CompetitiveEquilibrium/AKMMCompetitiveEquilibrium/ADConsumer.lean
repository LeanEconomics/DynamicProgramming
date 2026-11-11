/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SustainedGrowthPrices
import EquilibriumApplications.GrowthCertaintyDDGrowthStability
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

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
