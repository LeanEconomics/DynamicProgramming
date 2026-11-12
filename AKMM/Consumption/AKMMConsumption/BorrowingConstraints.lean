/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.Deterministic

/-!
# Borrowing constraints and the natural borrowing limit

AKMM, §11.3.3, (11.31)–(11.32) and the natural borrowing limit, pp. 302–304, and the
borrowing-constraint part of §11.3.4, (11.33), pp. 304–305.

* **p. 302, the i.i.d. case.** Along the unconstrained PIH path of (11.30),
  `aₜ₊₁ = aₜ + yₜ − ȳ`: the book's example `yₜ < (1 − r)ȳ`, `aₜ < rȳ` gives `aₜ₊₁ < 0`
  (`bc_iid_example`); from any wealth, a run of `n` low incomes `y_lo < ȳ` (probability
  `pⁿ > 0`) takes wealth below zero in finite time (`bc_iid_hits`).
* **(11.32)** the modified Euler equation `u′(cₜ) = βREₜu′(cₜ₊₁) + λₜ`, `λₜ ≥ 0`, gives `≥`, strict
  iff the constraint binds (`eq_11_32`); at a binding constraint the household eats its cash in
  hand, with MPC `1` (`bc_binding_cons`).
* **The natural borrowing limit** (p. 303): nonnegative consumption and the no-Ponzi condition
  give `aₜ₊₁ ≥ −Σⱼ (1 + r)⁻ʲyₜ₊₁₊ⱼ` (`bc_natural_limit_det`); if income can stay at `y_min`
  forever, `aₜ₊₁ ≥ −(1 + r)y_min/r` (`bc_natural_limit`); borrowing up to the limit and drawing
  `y_min` forces `cₜ ≤ 0` (`bc_natural_limit_cons_nonpos`); with `y_min = 0` the limit is `0`
  (`bc_natural_limit_zero`).
* **(11.33)** with quadratic utility and `βR = 1`, `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}`
  (`eq_11_33`); below the kink the consumption function has slope `1` (`bc_slope_one`).

Departures: the "positive probability of hitting the limit" is proved for a run of identical low
draws whose probability is `pⁿ`; the stochastic natural limit is proved along the income path
that stays at `y_min` (the event the book uses).
-/

namespace AKMM.Consumption

open Filter Topology

/-- **AKMM, p. 302.** On the unconstrained i.i.d. path `aₜ₊₁ = aₜ + yₜ − ȳ`, if
`yₜ < (1 − r)ȳ` and `aₜ < rȳ` then `aₜ₊₁ < 0`: the no-borrowing limit would be violated. -/
theorem bc_iid_example {r ybar at' yt at1 : ℝ} (hdyn : at1 = at' + yt - ybar)
    (hy : yt < (1 - r) * ybar) (ha : at' < r * ybar) : at1 < 0 := by
  rw [hdyn]; nlinarith

/-- **AKMM, p. 302: "starting from any initial level of wealth there is always a positive
probability that … the household will hit the borrowing limit in finite time".** On the
unconstrained path `aₜ₊₁ = aₜ + yₜ − ȳ`, if income takes a value `y_lo < ȳ` with probability
`p > 0`, then from any `a₀` there is `n` such that `n` consecutive draws of `y_lo`, an event of
probability `pⁿ > 0`, give `aₙ < 0`. -/
theorem bc_iid_hits {ybar ylo p : ℝ} (hlo : ylo < ybar) (hp : 0 < p) (a₀ : ℝ) :
    ∃ n : ℕ, 0 < p ^ n ∧ ∀ a y : ℕ → ℝ, a 0 = a₀ → (∀ t, a (t + 1) = a t + y t - ybar) →
      (∀ t, t < n → y t = ylo) → a n < 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a₀ / (ybar - ylo))
  refine ⟨n, pow_pos hp n, fun a y ha0 hdyn hlow => ?_⟩
  have hk : ∀ k, k ≤ n → a k = a₀ - k * (ybar - ylo) := by
    intro k
    induction k with
    | zero => intro _; simp [ha0]
    | succ k ih =>
      intro hk
      rw [hdyn, ih (by omega), hlow k (by omega)]
      push_cast; ring
  rw [hk n le_rfl]
  have hd : 0 < ybar - ylo := by linarith
  rw [div_lt_iff₀ hd] at hn
  linarith

/-- **AKMM, (11.32), p. 303.** The first-order condition `u′(cₜ) = βREₜu′(cₜ₊₁) + λₜ` with
`λₜ ≥ 0` gives `u′(cₜ) ≥ βREₜu′(cₜ₊₁)`, with strict inequality exactly when `λₜ > 0` (the
constraint binds). -/
theorem eq_11_32 {mu emu βR lam : ℝ} (hfoc : mu = βR * emu + lam) (hlam : 0 ≤ lam) :
    βR * emu ≤ mu ∧ (βR * emu < mu ↔ 0 < lam) := by
  subst hfoc
  exact ⟨by linarith, ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- AKMM, p. 303: at a binding constraint `aₜ₊₁ = 0` the budget gives `cₜ = aₜ + yₜ`, so the
marginal propensity to consume out of current income (transitory or permanent) is `1`. -/
theorem bc_binding_cons {R a y c : ℝ} (hR : R ≠ 0) (hbud : 0 = R * (a + y - c)) :
    c = a + y ∧ HasDerivAt (fun y' : ℝ => a + y') 1 y := by
  refine ⟨?_, by simpa using (hasDerivAt_id y).const_add a⟩
  rcases mul_eq_zero.1 hbud.symm with h | h
  · exact absurd h hR
  · linarith

/-- **AKMM, p. 303: the natural borrowing limit, deterministic income.** With `r > 0`, the budget,
nonnegative consumption, a convergent present value of income from `t + 1` and the no-Ponzi
condition (`(1 + r)^{−T}aₜ₊₁₊ᵀ` eventually above `−ε` for every `ε > 0`),
`aₜ₊₁ ≥ −Σⱼ (1 + r)⁻ʲyₜ₊₁₊ⱼ`. -/
theorem bc_natural_limit_det {r : ℝ} (hr : 0 < r) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = (1 + r) * (y t + a t - c t)) (hc : ∀ t, 0 ≤ c t) (t : ℕ)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j * y (t + 1 + j))
    (hnpg : ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ ((1 + r)⁻¹) ^ T * a (t + 1 + T)) :
    -∑' j, ((1 + r)⁻¹) ^ j * y (t + 1 + j) ≤ a (t + 1) := by
  have hR : (1 + r) ≠ 0 := by linarith
  have hq0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.2 (by linarith)
  -- `Σ_{j<T} q^j y ≤ a + (stuff)`, from the iterated budget and `c ≥ 0`
  have hfin : ∀ T, ((1 + r)⁻¹) ^ T * a (t + 1 + T) - a (t + 1) ≤
      ∑ j ∈ Finset.range T, ((1 + r)⁻¹) ^ j * y (t + 1 + j) := by
    intro T
    have h := cd_budget_iter hR hb (t + 1) T
    have hnn : 0 ≤ ∑ j ∈ Finset.range T, ((1 + r)⁻¹) ^ j * c (t + 1 + j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hq0 j) (hc _)
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlim := hy.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ T in atTop, ∑ j ∈ Finset.range T, ((1 + r)⁻¹) ^ j * y (t + 1 + j) <
      ∑' j, ((1 + r)⁻¹) ^ j * y (t + 1 + j) + ε / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨T, h1, h2⟩ := (hev.and (hnpg (ε / 2) (half_pos hε))).exists
  have := hfin T
  linarith

/-- **AKMM, p. 303: the natural borrowing limit** `aₜ₊₁ ≥ −(1 + r)y_min/r`. If income stays at
its lowest value `y_min` from `t + 1` on (an event the household must survive with nonnegative
consumption), the deterministic limit is `−Σⱼ (1 + r)⁻ʲy_min = −(1 + r)y_min/r`. -/
theorem bc_natural_limit {r ymin : ℝ} (hr : 0 < r) {y c a : ℕ → ℝ}
    (hb : ∀ t, a (t + 1) = (1 + r) * (y t + a t - c t)) (hc : ∀ t, 0 ≤ c t) (t : ℕ)
    (hmin : ∀ j, y (t + 1 + j) = ymin)
    (hnpg : ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ ((1 + r)⁻¹) ^ T * a (t + 1 + T)) :
    -((1 + r) / r * ymin) ≤ a (t + 1) := by
  have hq0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.2 (by linarith)
  have hq1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hy : Summable fun j => ((1 + r)⁻¹) ^ j * y (t + 1 + j) := by
    simp_rw [hmin]; exact hg.mul_right _
  have h := bc_natural_limit_det hr hb hc t hy hnpg
  simp_rw [hmin] at h
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1] at h
  have e : (1 - (1 + r)⁻¹)⁻¹ * ymin = (1 + r) / r * ymin := by
    congr 1
    have : (1 + r) ≠ 0 := by linarith
    rw [show 1 - (1 + r)⁻¹ = r / (1 + r) by field_simp; ring, inv_div]
  linarith

/-- **AKMM, p. 304.** A household that has borrowed up to the natural limit,
`aₜ = −(1 + r)y_min/r`, and draws `yₜ = y_min` has `cₜ = aₜ + y_min − aₜ₊₁/(1 + r) ≤ 0` whenever
`aₜ₊₁` respects the limit. -/
theorem bc_natural_limit_cons_nonpos {r ymin at' at1 c : ℝ} (hr : 0 < r)
    (hat : at' = -((1 + r) / r * ymin)) (hlim : -((1 + r) / r * ymin) ≤ at1)
    (hbud : at1 = (1 + r) * (ymin + at' - c)) : c ≤ 0 := by
  have hR : 0 < 1 + r := by linarith
  have hc : c = at' + ymin - at1 / (1 + r) := by
    rw [hbud]; field_simp; ring
  have h1 : -((1 + r) / r * ymin) / (1 + r) ≤ at1 / (1 + r) := div_le_div_of_nonneg_right hlim hR.le
  have h2 : -((1 + r) / r * ymin) / (1 + r) = -(ymin / r) := by field_simp
  have h3 : -((1 + r) / r * ymin) + ymin = -(ymin / r) := by field_simp; ring
  rw [hc, hat]
  linarith

/-- AKMM, p. 304: if `y_min = 0` the natural borrowing limit is the no-borrowing constraint. -/
theorem bc_natural_limit_zero (r : ℝ) : -((1 + r) / r * 0) = 0 := by simp

/-- **AKMM, (11.33), p. 305.** Quadratic utility and `βR = 1` with the limit `aₜ₊₁ ≥ −a`: the
Euler inequality gives `cₜ ≤ Eₜcₜ₊₁`, with equality when the limit does not bind, and the budget
`aₜ₊₁ = R(yₜ + aₜ − cₜ)`. Then `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}`. -/
theorem eq_11_33 {R y a c a' abar ec : ℝ} (hR : 0 < R) (hbud : a' = R * (y + a - c))
    (hlim : -abar ≤ a') (heul : c ≤ ec) (hslack : -abar < a' → c = ec) :
    c = min (y + a + abar / R) ec := by
  have hc : c ≤ y + a + abar / R := by
    have h1 : -abar ≤ R * (y + a - c) := hbud ▸ hlim
    have h2 : c - y - a ≤ abar / R := by rw [le_div_iff₀ hR]; nlinarith
    linarith
  rcases hlim.lt_or_eq with h | h
  · rw [hslack h] at hc ⊢; exact (min_eq_right hc).symm
  · have hc' : c = y + a + abar / R := by
      rw [← h] at hbud
      field_simp
      linarith
    rw [← hc']
    exact (min_eq_left heul).symm

/-- AKMM, p. 305 and Figure 11.2: where the constraint binds, `c(a) = a + y + a/R`, so the
consumption function has slope `1` in wealth. -/
theorem bc_slope_one (y abar R a : ℝ) :
    HasDerivAt (fun x : ℝ => x + y + abar / R) 1 a := by
  simpa using ((hasDerivAt_id a).add_const y).add_const (abar / R)

end AKMM.Consumption
