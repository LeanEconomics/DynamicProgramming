/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.RecursiveEquilibrium
import OverlappingGenerations.OPExercises

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
