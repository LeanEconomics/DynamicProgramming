/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.RiskSharing
import AKMMCompetitiveEquilibrium.ADConsumer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The bond economy and the deterministic income fluctuation problem

AKMM, §11.2.3 (the bond economy, (11.8)–(11.11)) and §11.3.1, (11.12)–(11.16), footnotes 12–13
and 15, pp. 294–297.

* **(11.11)** from (11.8) with the constant bond price `q = 1/(1 + r)` (`eq_11_11`); **(11.10)**:
  the no-Ponzi condition and the transversality condition together give `lim = 0`
  (`eq_11_10`).
* The flow budget iterated `T` periods (`cd_budget_iter`) and, with (11.10), the intertemporal
  budget `Σⱼ R⁻ʲcₜ₊ⱼ = aₜ + Σⱼ R⁻ʲyₜ₊ⱼ` of p. 296 (`cd_intertemporal_budget`); the present value
  of a positive consumption plan converges automatically (`cd_summable_pv_cons`).
* The problem (11.12) (`cd_Plan`, `cd_Optimal`); **(11.13)** `u′(cₜ) = βRu′(cₜ₊₁)` at every
  optimum, from optimality by a two-period perturbation (`eq_11_13`); **(11.14)** for CRRA
  (`eq_11_14`); sufficiency of the Euler equation and (11.10) for concave `u`
  (`cd_optimal_of_euler`), with the log plan `cₜ = (1 − β)aₜ` as a concrete optimum
  (`cd_log_optimal`).
* **(11.15)** the linear consumption function (`eq_11_15`, from optimality
  `cd_optimal_eq_11_15`), **(11.16)** the MPC (`eq_11_16`); a transitory change in `yₜ` acts as
  a change in `aₜ` (`cd_transitory_eq_wealth`); `βR = 1` gives `MPC = 1 − β = ρ/(1 + ρ)` and
  `0 ≤ ρ − MPC ≤ ρ²` (`cd_mpc_betaR_one`, `cd_mpc_approx_rho`); the MPC out of a permanent change
  in income is `1` when `βR = 1` (`cd_mpc_permanent`); footnote 15, the annuity value keeps assets
  constant (`footnote_15`).
* **Correction** (p. 297, log utility "`MPC ≃ r`"): with `σ = 1`, `MPC = 1 − β` whatever `r`
  (`cd_mpc_log`), it equals `r/(1 + r)` only when `βR = 1` (`cd_mpc_log_eq_r_iff`), and with
  `β = 1/2`, `r = 1/100` it is `1/2` (`cd_mpc_log_printed_counterexample`).

Departures: (11.10) is imposed as `aₜ/Rᵗ → 0`, and the optimum is taken over positive consumption
plans with summable discounted utility.
-/

namespace AKMM.Consumption

open Filter Topology AKMM.CompetitiveEquilibrium

/-! ### The bond economy -/

/-- **AKMM, (11.11), p. 295.** With no aggregate risk the bond price is a constant `q`, and with
`r = 1/q − 1` the budget (11.8) `c + qa′ = y + a` is `a′ = (1 + r)(y + a − c)`. -/
theorem eq_11_11 {q r y a c a' : ℝ} (hq : 0 < q) (hr : r = 1 / q - 1) (h : c + q * a' = y + a) :
    a' = (1 + r) * (y + a - c) := by
  subst hr
  field_simp
  linarith

/-- **AKMM, (11.9)–(11.10), p. 294.** If the discounted debt satisfies the no-Ponzi condition
(eventually `≥ −ε` for every `ε > 0`) and the transversality condition (eventually `≤ ε`), then
it converges to `0`. -/
theorem eq_11_10 {x : ℕ → ℝ} (hnpg : ∀ ε > 0, ∀ᶠ t in atTop, -ε ≤ x t)
    (htvc : ∀ ε > 0, ∀ᶠ t in atTop, x t ≤ ε) : Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, h₁⟩ := eventually_atTop.1 (hnpg (ε / 2) (half_pos hε))
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (htvc (ε / 2) (half_pos hε))
  refine ⟨max N₁ N₂, fun t ht => ?_⟩
  have a := h₁ t (le_of_max_le_left ht)
  have b := h₂ t (le_of_max_le_right ht)
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-! ### Budgets -/

/-- AKMM, p. 296: the budget `aₜ₊₁ = R(yₜ + aₜ − cₜ)` iterated `T` periods:
`Σ_{j<T} R⁻ʲcₜ₊ⱼ = aₜ + Σ_{j<T} R⁻ʲyₜ₊ⱼ − R⁻ᵀaₜ₊ᵀ`. -/
theorem cd_budget_iter {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = R * (y t + a t - c t)) (t T : ℕ) :
    ∑ j ∈ Finset.range T, R⁻¹ ^ j * c (t + j) =
      a t + ∑ j ∈ Finset.range T, R⁻¹ ^ j * y (t + j) - R⁻¹ ^ T * a (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, show t + (T + 1) = t + T + 1 by ring,
      hb (t + T), pow_succ]
    field_simp
    ring

/-- AKMM, p. 296: the present value of a positive consumption plan converges whenever the
present value of income converges and `R⁻ᵀaₜ₊ᵀ → 0`: its partial sums are bounded. -/
theorem cd_summable_pv_cons {R : ℝ} (hR : 0 < R) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = R * (y t + a t - c t)) (hc : ∀ t, 0 ≤ c t) (t : ℕ)
    (htvc : Tendsto (fun T => R⁻¹ ^ T * a (t + T)) atTop (𝓝 0))
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    Summable fun j => R⁻¹ ^ j * c (t + j) := by
  have hnn : ∀ j, 0 ≤ R⁻¹ ^ j * c (t + j) := fun j =>
    mul_nonneg (pow_nonneg (inv_nonneg.2 hR.le) j) (hc _)
  have hlim : Tendsto (fun T => a t + ∑ j ∈ Finset.range T, R⁻¹ ^ j * y (t + j) -
      R⁻¹ ^ T * a (t + T)) atTop (𝓝 (a t + ∑' j, R⁻¹ ^ j * y (t + j) - 0)) :=
    (tendsto_const_nhds.add hy.hasSum.tendsto_sum_nat).sub htvc
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  refine summable_of_sum_range_le (c := B) hnn fun T => ?_
  rw [cd_budget_iter hR.ne' hb]
  exact hB ⟨T, rfl⟩

/-- AKMM, p. 296: iterating the budget and imposing (11.10) gives the intertemporal budget
`Σⱼ R⁻ʲcₜ₊ⱼ = aₜ + Σⱼ R⁻ʲyₜ₊ⱼ`. -/
theorem cd_intertemporal_budget {R : ℝ} (hR : 0 < R) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = R * (y t + a t - c t)) (t : ℕ)
    (htvc : Tendsto (fun T => R⁻¹ ^ T * a (t + T)) atTop (𝓝 0))
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j))
    (hc : Summable fun j => R⁻¹ ^ j * c (t + j)) :
    ∑' j, R⁻¹ ^ j * c (t + j) = a t + ∑' j, R⁻¹ ^ j * y (t + j) := by
  have hlim : Tendsto (fun T => a t + ∑ j ∈ Finset.range T, R⁻¹ ^ j * y (t + j) -
      R⁻¹ ^ T * a (t + T)) atTop (𝓝 (a t + ∑' j, R⁻¹ ^ j * y (t + j) - 0)) :=
    (tendsto_const_nhds.add hy.hasSum.tendsto_sum_nat).sub htvc
  have h2 := hc.hasSum.tendsto_sum_nat
  simp_rw [cd_budget_iter hR.ne' hb t] at h2
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique h2 hlim

/-- (11.10) for the plan, `aₜ/Rᵗ → 0`, gives `R⁻ᵀaₜ₊ᵀ → 0` from every date `t`. -/
theorem cd_tvc_shift {R : ℝ} (hR : 0 < R) {a : ℕ → ℝ}
    (htvc : Tendsto (fun t => a t / R ^ t) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => R⁻¹ ^ T * a (t + T)) atTop (𝓝 0) := by
  have h := (htvc.comp (tendsto_add_atTop_iff_nat t |>.2 tendsto_id)).const_mul (R ^ t)
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  simp only [Function.comp, id]
  rw [show T + t = t + T by ring, pow_add, inv_pow]
  field_simp

/-! ### The problem (11.12) and the Euler equation (11.13) -/

/-- AKMM, (11.12), p. 295: a feasible plan from `a₀`: the budget `aₜ₊₁ = R(yₜ + aₜ − cₜ)`,
positive consumption and condition (11.10), in the form `aₜ/Rᵗ → 0`. -/
def cd_Plan (R a₀ : ℝ) (y c a : ℕ → ℝ) : Prop :=
  a 0 = a₀ ∧ (∀ t, a (t + 1) = R * (y t + a t - c t)) ∧ (∀ t, 0 < c t) ∧
    Tendsto (fun t => a t / R ^ t) atTop (𝓝 0)

/-- AKMM, (11.12), p. 295: `(c, a)` solves the problem: it is feasible with summable discounted
utility, and no feasible plan with summable utility does better. -/
def cd_Optimal (β R a₀ : ℝ) (u : ℝ → ℝ) (y c a : ℕ → ℝ) : Prop :=
  cd_Plan R a₀ y c a ∧ Summable (fun t => β ^ t * u (c t)) ∧
    ∀ c' a', cd_Plan R a₀ y c' a' → Summable (fun t => β ^ t * u (c' t)) →
      ∑' t, β ^ t * u (c' t) ≤ ∑' t, β ^ t * u (c t)

/-- **AKMM, (11.13), p. 296.** At an optimum of (11.12) with `R > 0` and differentiable `u`,
`u′(cₜ) = βRu′(cₜ₊₁)`, i.e. `u′(cₜ)/(βu′(cₜ₊₁)) = 1 + r`. Proved from optimality: shifting `ε`
units of consumption from `t` to `t + 1` (as `Rε`) is feasible and changes only two terms. -/
theorem eq_11_13 {β R a₀ : ℝ} (hβ : 0 < β) (hR : 0 < R) {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) {y c a : ℕ → ℝ}
    (hopt : cd_Optimal β R a₀ u y c a) (t : ℕ) : du (c t) = β * R * du (c (t + 1)) := by
  obtain ⟨⟨ha0, hb, hc, htvc⟩, hsum, hle⟩ := hopt
  classical
  set c' : ℝ → ℕ → ℝ := fun ε n =>
    if n = t then c t - ε else if n = t + 1 then c (t + 1) + R * ε else c n with hc'
  set a' : ℝ → ℕ → ℝ := fun ε n => if n = t + 1 then a (t + 1) + R * ε else a n with ha'
  have hplan : ∀ ε, |ε| < min (c t) (c (t + 1) / R) → cd_Plan R a₀ y (c' ε) (a' ε) := by
    intro ε hε
    have h1 : ε < c t := (le_abs_self ε).trans_lt (hε.trans_le (min_le_left _ _))
    have h2 : -ε < c (t + 1) / R := (neg_le_abs ε).trans_lt (hε.trans_le (min_le_right _ _))
    have h2' : 0 < c (t + 1) + R * ε := by
      rw [lt_div_iff₀ hR] at h2; linarith
    refine ⟨?_, fun n => ?_, fun n => ?_, ?_⟩
    · simp only [ha', show (0 : ℕ) ≠ t + 1 by omega, ↓reduceIte, ha0]
    · by_cases hn : n = t
      · subst hn
        simp only [ha', hc', ↓reduceIte, show n ≠ n + 1 by omega]
        rw [hb n]; ring
      · by_cases hn1 : n = t + 1
        · subst hn1
          simp only [ha', hc', show t + 1 + 1 ≠ t + 1 by omega, show t + 1 ≠ t by omega,
            ↓reduceIte]
          rw [hb (t + 1)]; ring
        · simp only [ha', hc', show n + 1 ≠ t + 1 by omega, hn, hn1, ↓reduceIte]
          exact hb n
    · simp only [hc']
      split_ifs
      · linarith
      · exact h2'
      · exact hc n
    · refine htvc.congr' ?_
      filter_upwards [eventually_gt_atTop (t + 1)] with n hn
      simp only [ha', show n ≠ t + 1 by omega, ↓reduceIte]
  have hmin : 0 < min (c t) (c (t + 1) / R) := lt_min (hc t) (div_pos (hc _) hR)
  set f : ℕ → ℝ := fun n => β ^ n * u (c n)
  set g : ℝ → ℕ → ℝ := fun ε n => β ^ n * u (c' ε n)
  have hs : ∀ ε, ∀ n ∉ ({t, t + 1} : Finset ℕ), g ε n = f n := by
    intro ε n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [g, f, hc', hn.1, hn.2, ↓reduceIte]
  have h0 : ∀ n, g 0 n = f n := by
    intro n
    simp only [g, f, hc', sub_zero, mul_zero, add_zero]
    split_ifs <;> subst_vars <;> rfl
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), Summable (g ε) → ∑' n, g ε n ≤ ∑' n, f n := by
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < min (c t) (c (t + 1) / R) := by
      have hc0 : Continuous fun ε : ℝ => |ε| := continuous_abs
      exact hc0.continuousAt.eventually_lt continuousAt_const (by simpa using hmin)
    filter_upwards [this] with ε hε hsg
    exact hle _ _ (hplan ε hε) hsg
  have hd : HasDerivAt (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), g ε n)
      (β ^ t * (du (c t) * (-1)) + β ^ (t + 1) * (du (c (t + 1)) * (R * 1))) 0 := by
    have ht : t ∉ ({t + 1} : Finset ℕ) := by simp
    have hfun : (fun ε => ∑ n ∈ ({t, t + 1} : Finset ℕ), g ε n) =
        fun ε => β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + R * ε) := by
      funext ε
      rw [Finset.sum_insert ht, Finset.sum_singleton]
      simp only [g, hc', ↓reduceIte, show t + 1 ≠ t by omega]
    rw [hfun]
    have e1 : HasDerivAt (fun ε => c t - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c t)
    have e2 : HasDerivAt (fun ε => c (t + 1) + R * ε) (R * 1) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add _
    have u1 := hu (c t) (hc t)
    have u2 := hu (c (t + 1)) (hc _)
    have u1' : HasDerivAt u (du (c t)) (c t - 0) := by simpa using u1
    have u2' : HasDerivAt u (du (c (t + 1))) (c (t + 1) + R * 0) := by simpa using u2
    exact ((u1'.comp 0 e1).const_mul _).add ((u2'.comp 0 e2).const_mul _)
  have := ce_foc_of_perturb {t, t + 1} hsum hs h0 hev hd
  have hβt : β ^ t ≠ 0 := pow_ne_zero _ hβ.ne'
  rw [pow_succ] at this
  have : β ^ t * (β * R * du (c (t + 1)) - du (c t)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hβt
  · linarith

/-- **AKMM, (11.14), p. 296.** With CRRA marginal utility `u′(c) = c^{−σ}`, the Euler equation
(11.13) is `cₜ₊₁/cₜ = (βR)^{1/σ}`. -/
theorem eq_11_14 {β R σ ct ct1 : ℝ} (hσ : 0 < σ) (hβR : 0 < β * R) (hct : 0 < ct)
    (hct1 : 0 < ct1) (h : ct ^ (-σ) = β * R * ct1 ^ (-σ)) : ct1 / ct = (β * R) ^ (1 / σ) := by
  have hf : ct1 ^ (-σ) = (β * R)⁻¹ * ct ^ (-σ) := by
    rw [h, ← mul_assoc, inv_mul_cancel₀ hβR.ne', one_mul]
  have e := rs_crra_invert hσ hct1 (inv_pos.2 hβR) (Real.rpow_pos_of_pos hct _) hf
  have h1 : (ct ^ (-σ)) ^ (-1 / σ) = ct := by
    rw [← Real.rpow_mul hct.le, show -σ * (-1 / σ) = 1 by field_simp, Real.rpow_one]
  have h2 : ((β * R)⁻¹) ^ (-1 / σ) = (β * R) ^ (1 / σ) := by
    rw [Real.inv_rpow hβR.le, neg_div, Real.rpow_neg hβR.le, inv_inv]
  rw [e, h1, h2]
  field_simp

/-- With (11.14) at every date, `cₜ₊ⱼ = gʲcₜ` for `g = (βR)^{1/σ}`. -/
theorem cd_growth {g : ℝ} {c : ℕ → ℝ} (hg : ∀ t, c (t + 1) = g * c t) (t j : ℕ) :
    c (t + j) = g ^ j * c t := by
  induction j with
  | zero => simp
  | succ j ih => rw [← add_assoc, hg, ih, pow_succ]; ring

/-! ### Sufficiency and a concrete optimum -/

/-- AKMM, p. 296 (the Euler equation and (11.10) characterise the optimum). For `u` with the
tangent-line inequality `u(x) ≤ u(z) + u′(z)(x − z)` (concavity), a feasible plan satisfying the
Euler equation (11.13) at every date, with summable utility and a convergent present value of
income, solves (11.12). -/
theorem cd_optimal_of_euler {β R a₀ : ℝ} (hβ : 0 < β) (hR : 0 < R) {u du : ℝ → ℝ}
    (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z)) {y c a : ℕ → ℝ}
    (hplan : cd_Plan R a₀ y c a) (heuler : ∀ t, du (c t) = β * R * du (c (t + 1)))
    (hu : Summable fun t => β ^ t * u (c t)) (hy : Summable fun j => R⁻¹ ^ j * y j) :
    cd_Optimal β R a₀ u y c a := by
  refine ⟨hplan, hu, fun c' a' hplan' hu' => ?_⟩
  obtain ⟨ha0, hb, hc, htvc⟩ := hplan
  obtain ⟨ha0', hb', hc', htvc'⟩ := hplan'
  have hdisc : ∀ t, β ^ t * du (c t) = R⁻¹ ^ t * du (c 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e := heuler t
      rw [pow_succ, pow_succ, show β ^ t * β * du (c (t + 1)) = β ^ t * (β * du (c (t + 1)))
        by ring, show β * du (c (t + 1)) = R⁻¹ * du (c t) by rw [e]; field_simp]
      rw [show β ^ t * (R⁻¹ * du (c t)) = R⁻¹ * (β ^ t * du (c t)) by ring, ih]
      ring
  have hy0 : Summable fun j => R⁻¹ ^ j * y (0 + j) := by simpa using hy
  have hpv := cd_summable_pv_cons hR hb (fun t => (hc t).le) 0 (cd_tvc_shift hR htvc 0) hy0
  have hpv' := cd_summable_pv_cons hR hb' (fun t => (hc' t).le) 0 (cd_tvc_shift hR htvc' 0) hy0
  have hib := cd_intertemporal_budget hR hb 0 (cd_tvc_shift hR htvc 0) hy0 hpv
  have hib' := cd_intertemporal_budget hR hb' 0 (cd_tvc_shift hR htvc' 0) hy0 hpv'
  simp only [zero_add] at hpv hpv' hib hib'
  have hpt : ∀ t, β ^ t * u (c' t) ≤
      β ^ t * u (c t) + du (c 0) * (R⁻¹ ^ t * c' t - R⁻¹ ^ t * c t) := by
    intro t
    have h1 := htan (c' t) (c t) (hc' t) (hc t)
    have h2 : β ^ t * u (c' t) ≤ β ^ t * (u (c t) + du (c t) * (c' t - c t)) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ.le t)
    have h3 : β ^ t * (u (c t) + du (c t) * (c' t - c t)) =
        β ^ t * u (c t) + (β ^ t * du (c t)) * (c' t - c t) := by ring
    rw [h3, hdisc t] at h2
    linarith
  have hsr : Summable fun t => β ^ t * u (c t) + du (c 0) * (R⁻¹ ^ t * c' t - R⁻¹ ^ t * c t) :=
    hu.add ((hpv'.sub hpv).mul_left _)
  calc ∑' t, β ^ t * u (c' t)
      ≤ ∑' t, (β ^ t * u (c t) + du (c 0) * (R⁻¹ ^ t * c' t - R⁻¹ ^ t * c t)) :=
        Summable.tsum_le_tsum hpt hu' hsr
    _ = ∑' t, β ^ t * u (c t) + du (c 0) * (∑' t, R⁻¹ ^ t * c' t - ∑' t, R⁻¹ ^ t * c t) := by
        rw [hu.tsum_add ((hpv'.sub hpv).mul_left _), tsum_mul_left, hpv'.tsum_sub hpv]
    _ = ∑' t, β ^ t * u (c t) := by rw [hib, hib', ha0, ha0']; ring

/-- A concrete optimum of (11.12) (the problem's hypotheses are not vacuous): log utility, no
income, `0 < β < 1`, `R > 0`, `a₀ > 0`. The plan `aₜ = (βR)ᵗa₀`, `cₜ = (1 − β)aₜ` is optimal. -/
theorem cd_log_optimal {β R a₀ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (ha₀ : 0 < a₀) :
    cd_Optimal β R a₀ Real.log (fun _ => 0) (fun t => (1 - β) * ((β * R) ^ t * a₀))
      (fun t => (β * R) ^ t * a₀) := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hcpos : ∀ t, 0 < (1 - β) * ((β * R) ^ t * a₀) := fun t =>
    mul_pos (by linarith) (mul_pos (pow_pos hβR t) ha₀)
  refine cd_optimal_of_euler hβ hR (du := fun x => x⁻¹) (fun x z hx hz => ?_) ⟨by simp,
    fun t => by beta_reduce; ring, hcpos, ?_⟩ (fun t => ?_) ?_ (by simp)
  · have := Real.log_le_sub_one_of_pos (div_pos hx hz)
    rw [Real.log_div hx.ne' hz.ne'] at this
    have e : z⁻¹ * (x - z) = x / z - 1 := by field_simp
    linarith
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const a₀
    rw [zero_mul] at h
    refine h.congr fun t => ?_
    beta_reduce
    rw [mul_pow]
    field_simp
  · show ((1 - β) * ((β * R) ^ t * a₀))⁻¹ = β * R * ((1 - β) * ((β * R) ^ (t + 1) * a₀))⁻¹
    rw [pow_succ]
    have := pow_pos hβR t
    field_simp
  · have hlog : ∀ t : ℕ, β ^ t * Real.log ((1 - β) * ((β * R) ^ t * a₀)) =
        Real.log ((1 - β) * a₀) * β ^ t + Real.log (β * R) * ((t : ℝ) ^ 1 * β ^ t) := by
      intro t
      rw [show (1 - β) * ((β * R) ^ t * a₀) = (1 - β) * a₀ * (β * R) ^ t by ring,
        Real.log_mul (mul_pos (by linarith) ha₀).ne' (pow_pos hβR t).ne', Real.log_pow]
      ring
    simp_rw [hlog]
    have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ]; exact hβ1
    exact ((summable_geometric_of_lt_one hβ.le hβ1).mul_left _).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left _)

/-! ### The consumption function (11.15) and the MPC (11.16) -/

/-- The MPC of (11.16), `1 − R⁻¹(βR)^{1/σ}`. -/
noncomputable def cd_mpc (β R σ : ℝ) : ℝ := 1 - R⁻¹ * (β * R) ^ (1 / σ)

/-- AKMM, p. 297: consumption growing at the rate `g < R` and the intertemporal budget give
`cₜ = (1 − R⁻¹g)(aₜ + Σⱼ R⁻ʲyₜ₊ⱼ)`. -/
theorem cd_rule_of_growth {R g : ℝ} (hR : 0 < R) (hg0 : 0 ≤ g) (hgR : g < R) {y c a : ℕ → ℝ}
    (t : ℕ) (hgrow : ∀ j, c (t + j) = g ^ j * c t)
    (hbud : ∑' j, R⁻¹ ^ j * c (t + j) = a t + ∑' j, R⁻¹ ^ j * y (t + j)) :
    c t = (1 - R⁻¹ * g) * (a t + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have hq0 : 0 ≤ R⁻¹ * g := mul_nonneg (inv_nonneg.2 hR.le) hg0
  have hq1 : R⁻¹ * g < 1 := by rw [inv_mul_lt_iff₀ hR]; linarith
  have hsum : ∑' j, R⁻¹ ^ j * c (t + j) = c t * (1 - R⁻¹ * g)⁻¹ := by
    simp_rw [hgrow, show ∀ j : ℕ, R⁻¹ ^ j * (g ^ j * c t) = c t * (R⁻¹ * g) ^ j from
      fun j => by rw [mul_pow]; ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rw [← hbud, hsum]
  have : 0 < 1 - R⁻¹ * g := by linarith
  rw [mul_comm (c t), ← mul_assoc, mul_inv_cancel₀ this.ne', one_mul]

/-- **AKMM, (11.15), p. 297.** With CRRA utility, the Euler equation (11.14) at every date, the
intertemporal budget from `t`, and `(βR)^{1/σ} < R`: `cₜ = [1 − R⁻¹(βR)^{1/σ}](aₜ + Σⱼ R⁻ʲyₜ₊ⱼ)`,
consumption is a constant fraction of total (financial plus human) wealth. -/
theorem eq_11_15 {β R σ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hgR : (β * R) ^ (1 / σ) < R) {y c a : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    (heuler : ∀ t, c t ^ (-σ) = β * R * c (t + 1) ^ (-σ)) (t : ℕ)
    (hbud : ∑' j, R⁻¹ ^ j * c (t + j) = a t + ∑' j, R⁻¹ ^ j * y (t + j)) :
    c t = cd_mpc β R σ * (a t + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hg : ∀ s, c (s + 1) = (β * R) ^ (1 / σ) * c s := fun s => by
    have := eq_11_14 hσ hβR (hc s) (hc (s + 1)) (heuler s)
    rw [div_eq_iff (hc s).ne'] at this
    exact this
  exact cd_rule_of_growth hR (Real.rpow_nonneg hβR.le _) hgR t (cd_growth hg t) hbud

/-- **AKMM, (11.15), p. 297, from optimality.** At an optimum of (11.12) with CRRA marginal
utility `u′(c) = c^{−σ}` and `(βR)^{1/σ} < R`, if the present value of income from `t`
converges, `cₜ = MPC · (aₜ + Σⱼ R⁻ʲyₜ₊ⱼ)`. -/
theorem cd_optimal_eq_11_15 {β R σ a₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hgR : (β * R) ^ (1 / σ) < R) {u : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-σ)) c)
    {y c a : ℕ → ℝ} (hopt : cd_Optimal β R a₀ u y c a) (t : ℕ)
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    c t = cd_mpc β R σ * (a t + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have he := fun s => eq_11_13 (du := fun x => x ^ (-σ)) hβ hR hu hopt s
  obtain ⟨⟨-, hb, hc, htvc⟩, -⟩ := hopt
  have hpv := cd_summable_pv_cons hR hb (fun s => (hc s).le) t (cd_tvc_shift hR htvc t) hy
  exact eq_11_15 hσ hβ hR hgR hc he t
    (cd_intertemporal_budget hR hb t (cd_tvc_shift hR htvc t) hy hpv)

/-- **AKMM, (11.16), p. 297.** Differentiating (11.15): `∂cₜ/∂aₜ = MPC = 1 − R⁻¹(βR)^{1/σ}`. -/
theorem eq_11_16 (β R σ H a : ℝ) :
    HasDerivAt (fun x => cd_mpc β R σ * (x + H)) (cd_mpc β R σ) a := by
  simpa using ((hasDerivAt_id a).add_const H).const_mul (cd_mpc β R σ)

/-- AKMM, p. 297 and fn. 12: a transitory change `δ` in `yₜ` (leaving `yₜ₊ⱼ`, `j > 0`,
unchanged) moves consumption exactly as a change `δ` in `aₜ`. -/
theorem cd_transitory_eq_wealth {R : ℝ} (y : ℕ → ℝ) (m a δ : ℝ) (t : ℕ)
    (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    m * (a + ∑' j, R⁻¹ ^ j * (y (t + j) + if j = 0 then δ else 0)) =
      m * ((a + δ) + ∑' j, R⁻¹ ^ j * y (t + j)) := by
  have hδ : Summable fun j : ℕ => R⁻¹ ^ j * (if j = 0 then δ else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hsplit : ∑' j, R⁻¹ ^ j * (y (t + j) + if j = 0 then δ else 0) =
      ∑' j, R⁻¹ ^ j * y (t + j) + δ := by
    rw [show (fun j => R⁻¹ ^ j * (y (t + j) + if j = 0 then δ else 0)) =
      fun j => R⁻¹ ^ j * y (t + j) + R⁻¹ ^ j * (if j = 0 then δ else 0) from
      funext fun j => mul_add _ _ _, hy.tsum_add hδ,
      tsum_eq_single (f := fun j : ℕ => R⁻¹ ^ j * if j = 0 then δ else 0) 0
        (fun j hj => by simp [hj])]
    simp
  rw [hsplit]
  ring

/-- AKMM, p. 297: when `βR = 1`, `MPC = 1 − R⁻¹ = 1 − β`, and with `β = 1/(1 + ρ)` this is
`ρ/(1 + ρ)`. -/
theorem cd_mpc_betaR_one {β R σ ρ : ℝ} (hR : 0 < R) (hβR : β * R = 1)
    (hρ : β = 1 / (1 + ρ)) (hρ1 : 0 < 1 + ρ) :
    cd_mpc β R σ = 1 - R⁻¹ ∧ cd_mpc β R σ = 1 - β ∧ cd_mpc β R σ = ρ / (1 + ρ) := by
  have hβ : β = R⁻¹ := by field_simp; linarith
  have h1 : cd_mpc β R σ = 1 - R⁻¹ := by simp [cd_mpc, hβR]
  refine ⟨h1, by rw [h1, hβ], ?_⟩
  rw [h1, ← hβ, hρ]
  field_simp
  ring

/-- AKMM, p. 297 and fn. 13: "since `ρ` is small relative to 1, `MPC ≃ ρ`". Exactly:
`0 ≤ ρ − ρ/(1 + ρ) ≤ ρ²` for `ρ ≥ 0`. -/
theorem cd_mpc_approx_rho {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ ρ - ρ / (1 + ρ) ∧ ρ - ρ / (1 + ρ) ≤ ρ ^ 2 := by
  have h : ρ - ρ / (1 + ρ) = ρ ^ 2 / (1 + ρ) := by field_simp; ring
  rw [h]
  exact ⟨by positivity, div_le_self (sq_nonneg ρ) (by linarith)⟩

/-- AKMM, p. 297: with `βR = 1` a permanent change of one unit in income (`yₜ₊ⱼ + 1` for all
`j ≥ 0`) raises human wealth by `1/(1 − R⁻¹)` and consumption by exactly one unit: the MPC out of
permanent income is `1`. -/
theorem cd_mpc_permanent {β R σ : ℝ} (hR : 1 < R) (hβR : β * R = 1) (y : ℕ → ℝ) (a : ℝ)
    (t : ℕ) (hy : Summable fun j => R⁻¹ ^ j * y (t + j)) :
    ∑' j, R⁻¹ ^ j * (y (t + j) + 1) = ∑' j, R⁻¹ ^ j * y (t + j) + 1 / (1 - R⁻¹) ∧
    cd_mpc β R σ * (a + ∑' j, R⁻¹ ^ j * (y (t + j) + 1)) =
      cd_mpc β R σ * (a + ∑' j, R⁻¹ ^ j * y (t + j)) + 1 := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hq1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hg := summable_geometric_of_lt_one hq0 hq1
  have h1 : ∑' j, R⁻¹ ^ j * (y (t + j) + 1) = ∑' j, R⁻¹ ^ j * y (t + j) + 1 / (1 - R⁻¹) := by
    simp_rw [mul_add, mul_one]
    rw [hy.tsum_add hg, tsum_geometric_of_lt_one hq0 hq1, one_div]
  refine ⟨h1, ?_⟩
  rw [h1, (cd_mpc_betaR_one (σ := σ) (ρ := R - 1) hR0 hβR
    (by rw [show 1 + (R - 1) = R by ring, eq_div_iff hR0.ne']; exact hβR) (by linarith)).1]
  have : 0 < 1 - R⁻¹ := by linarith
  generalize ∑' j, R⁻¹ ^ j * y (t + j) = H
  have hR1 : R - 1 ≠ 0 := by linarith
  have e : 1 / (1 - R⁻¹) = R / (R - 1) := by field_simp
  rw [e]
  field_simp
  ring

/-- **AKMM, fn. 15, p. 298.** The annuity value: consuming `r/(1 + r)` of wealth (no income)
keeps assets constant, `(1 + r)(a − ra/(1 + r)) = a`. -/
theorem footnote_15 {r a : ℝ} (hr : 0 < 1 + r) : (1 + r) * (a - r / (1 + r) * a) = a := by
  field_simp
  ring

/-- **Correction to AKMM, p. 297** ("assuming log-utility (`σ = 1`) … without imposing `βR = 1`
… one obtains `MPC ≃ r`"). With `σ = 1`, (11.16) gives `MPC = 1 − β` for every `R > 0`: the MPC
does not depend on the interest rate. -/
theorem cd_mpc_log {β R : ℝ} (hR : 0 < R) : cd_mpc β R 1 = 1 - β := by
  simp only [cd_mpc, div_one, Real.rpow_one]
  field_simp

/-- With `σ = 1`, the MPC equals `r/(1 + r)` (the PIH value, `≃ r`) iff `βR = 1`. -/
theorem cd_mpc_log_eq_r_iff {β r : ℝ} (hr : 0 < 1 + r) :
    cd_mpc β (1 + r) 1 = r / (1 + r) ↔ β * (1 + r) = 1 := by
  rw [cd_mpc_log hr]
  constructor
  · intro h; field_simp at h; linarith
  · intro h
    have : β = 1 / (1 + r) := by field_simp; linarith
    rw [this]; field_simp; ring

/-- Counterexample to "`MPC ≃ r`" with log utility: `β = 1/2`, `r = 1/100` give `MPC = 1/2`,
fifty times `r`. -/
theorem cd_mpc_log_printed_counterexample :
    cd_mpc (1 / 2) (1 + 1 / 100) 1 = 1 / 2 ∧ cd_mpc (1 / 2) (1 + 1 / 100) 1 = 50 * (1 / 100) := by
  rw [cd_mpc_log (by norm_num)]
  constructor <;> norm_num

end AKMM.Consumption
