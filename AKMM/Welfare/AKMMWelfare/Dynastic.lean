/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMWelfare.FirstWelfare
import AKMMCompetitiveEquilibrium.ADConsumer

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
