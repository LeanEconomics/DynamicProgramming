/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInequality.FactorShares
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# §21.2.2: wage inequality

AKMM, §21.2.2, pp. 638–641. Relative wages are ratios of marginal products.

* `fs_ces_symm`, `wi_ces_hasDerivAt`: the CES marginal product is `F₁ = α^{1/ρ}(F/X)^{1/ρ}`.
* **Katz–Murphy** (p. 639): `km_premium_eq`, `km_log_premium`: with `G` CES,
  `log(w_s/w_u) = −(1/ρ) log(s/u) + ((ρ − 1)/ρ) log(A_s/A_u) + (1/ρ) log((1 − α)/α)`;
  `km_premium_strictAnti_supply`, `km_sbtc_strictMono_iff`: the premium falls with `s/u` and
  rises with `A_s/A_u` iff `ρ > 1`; `km_cd_premium`: under Cobb–Douglas `A_s/A_u` drops out;
  `km_identify`: the regression coefficients identify `ρ` and `γ`.
* **Directed technical change** (pp. 640–641): `dt_term_le` (Bernoulli's inequality), `dt_optimal`
  (the first-order condition is sufficient and the optimum unique), `dt_foc_iff_ratio`,
  `dt_exists`, `dt_maximiser_ratio`: the optimum has
  `A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}`; the printed factor `λ/(1 − λ)` is right only
  for `λ = 1/2` (`dt_printed_ratio_iff`); `dt_ratio_strictMono`; `dt_wage_ratio`,
  `dt_premium_closed`, `dt_log_premium`: `log(w_s/w_u) = (σ/(σ − φ)) log(λ/(1 − λ))
  + ((σ − φ(1 − σ))/(φ − σ)) log(s/u)`; `dt_exponent_pos_iff`, `dt_rho_gt_two`.
* **Capital–skill complementarity** (p. 641): `cs_ex1_wages`, `cs_ex1_premium_strictMono`
  (`u + s^ν k^{1−ν}`); `cs_ex2_wu_strictAnti` (`s^ν (k + u)^{1−ν}`); `cs_nest_wu`,
  `cs_nest_wu_monotone` (under `F(u, G(k, s))` the unskilled wage cannot fall as `k` rises);
  `cs_ces_nest_premium`, `cs_ces_nest_strictMono` (both nests CES: the premium rises with `k`
  iff the elasticity in `F` exceeds the elasticity in `G`).
-/

namespace AKMM.Inequality

/-- The CES function is symmetric after swapping the weights. -/
theorem fs_ces_symm (α ρ X Y : ℝ) : fs_ces α ρ X Y = fs_ces (1 - α) ρ Y X := by
  unfold fs_ces
  rw [sub_sub_cancel, add_comm]

/-- AKMM, p. 639: the CES marginal product in closed form, `F₁(X, Y) = α^{1/ρ}(F/X)^{1/ρ}`. -/
theorem wi_ces_hasDerivAt {α ρ X Y : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun z => fs_ces α ρ z Y) (α ^ (1 / ρ) * (fs_ces α ρ X Y / X) ^ (1 / ρ)) X := by
  refine (fs_ces_hasDerivAt hα hα1 hρ hρ1 hX hY).congr_deriv ?_
  have hS : 0 < α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ) := by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hX ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hY ((ρ - 1) / ρ)
    positivity
  set S := α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ)
  have hF : fs_ces α ρ X Y = S ^ (ρ / (ρ - 1)) := rfl
  have hr : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  rw [hF, Real.div_rpow (Real.rpow_pos_of_pos hS _).le hX.le, ← Real.rpow_mul hS.le]
  have e1 : ρ / (ρ - 1) * (1 / ρ) = ρ / (ρ - 1) - 1 := by field_simp; ring
  have e2 : (ρ - 1) / ρ - 1 = -(1 / ρ) := by field_simp; ring
  rw [e1, e2, Real.rpow_neg hX.le]
  field_simp

/-! ### Katz–Murphy -/

/-- AKMM, p. 639: the Katz–Murphy skill premium with `G` CES,
`((1 − α)/α)^{1/ρ} (A_s/A_u)^{(ρ−1)/ρ} (s/u)^{−1/ρ}`. -/
noncomputable def km_premium (α ρ zA zS : ℝ) : ℝ :=
  ((1 - α) / α) ^ (1 / ρ) * zA ^ ((ρ - 1) / ρ) * zS ^ (-(1 / ρ))

/-- **AKMM, p. 639: the Katz–Murphy skill premium.** With `G(A_u u, A_s s)` CES (elasticity `ρ`,
weight `α` on unskilled labor), `w_s/w_u = A_s G_s/(A_u G_u) = km_premium α ρ (A_s/A_u) (s/u)`. -/
theorem km_premium_eq {α ρ Au u As s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hAu : 0 < Au) (hu : 0 < u) (hAs : 0 < As) (hs : 0 < s) :
    ∃ Gu Gs : ℝ, HasDerivAt (fun z => fs_ces α ρ z (As * s)) Gu (Au * u) ∧
      HasDerivAt (fun z => fs_ces α ρ (Au * u) z) Gs (As * s) ∧
      As * Gs / (Au * Gu) = km_premium α ρ (As / Au) (s / u) := by
  have hX : 0 < Au * u := mul_pos hAu hu
  have hY : 0 < As * s := mul_pos hAs hs
  have h1 := wi_ces_hasDerivAt hα hα1 hρ hρ1 hX hY
  have h2 := wi_ces_hasDerivAt (α := 1 - α) (by linarith) (by linarith) hρ hρ1 hY hX
  simp only [← fs_ces_symm] at h2
  refine ⟨_, _, h1, h2, ?_⟩
  set F := fs_ces α ρ (Au * u) (As * s)
  have hFpos : 0 < F := Real.rpow_pos_of_pos (by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hX ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hY ((ρ - 1) / ρ)
    positivity) _
  unfold km_premium
  rw [Real.div_rpow hFpos.le hY.le, Real.div_rpow hFpos.le hX.le,
    Real.div_rpow (sub_pos.2 hα1).le hα.le, Real.mul_rpow hAs.le hs.le,
    Real.mul_rpow hAu.le hu.le, Real.div_rpow hAs.le hAu.le, Real.div_rpow hs.le hu.le,
    Real.rpow_neg hs.le, Real.rpow_neg hu.le]
  have hρ' : (ρ - 1) / ρ = 1 - 1 / ρ := by field_simp
  rw [hρ', Real.rpow_sub hAs, Real.rpow_sub hAu, Real.rpow_one, Real.rpow_one]
  have := Real.rpow_pos_of_pos hAs (1 / ρ)
  have := Real.rpow_pos_of_pos hAu (1 / ρ)
  have := Real.rpow_pos_of_pos hs (1 / ρ)
  have := Real.rpow_pos_of_pos hu (1 / ρ)
  have := Real.rpow_pos_of_pos hFpos (1 / ρ)
  have := Real.rpow_pos_of_pos hα (1 / ρ)
  have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
  field_simp

/-- **AKMM, p. 639: the Katz–Murphy equation.**
`log(w_s/w_u) = −(1/ρ) log(s/u) + ((ρ − 1)/ρ) log(A_s/A_u) + constant`, the constant being
`(1/ρ) log((1 − α)/α)`. -/
theorem km_log_premium {α ρ zA zS : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < zA) (hS : 0 < zS) :
    Real.log (km_premium α ρ zA zS) =
      -(1 / ρ) * Real.log zS + (ρ - 1) / ρ * Real.log zA + 1 / ρ * Real.log ((1 - α) / α) := by
  have hc : 0 < (1 - α) / α := div_pos (sub_pos.2 hα1) hα
  unfold km_premium
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hS _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne' (Real.rpow_pos_of_pos hA _).ne',
    Real.log_rpow hc, Real.log_rpow hA, Real.log_rpow hS]
  ring

/-- **AKMM, p. 639:** "As the relative supply of skilled workers increases … the skill premium
falls": `km_premium` is strictly decreasing in `s/u` for `ρ > 0`. -/
theorem km_premium_strictAnti_supply {α ρ zA : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hA : 0 < zA) : StrictAntiOn (km_premium α ρ zA) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hc : 0 < ((1 - α) / α) ^ (1 / ρ) * zA ^ ((ρ - 1) / ρ) :=
    mul_pos (Real.rpow_pos_of_pos (div_pos (sub_pos.2 hα1) hα) _) (Real.rpow_pos_of_pos hA _)
  unfold km_premium
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx' hxy (by
    have := one_div_pos.2 hρ; linarith)) hc

/-- **AKMM, p. 639: "skill-biased technological change makes the skill premium rise if and only
if the substitution elasticity between the two skill types is above one."** For `ρ > 0`,
`km_premium` is strictly increasing in `A_s/A_u` iff `ρ > 1`. -/
theorem km_sbtc_strictMono_iff {α ρ zS : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hS : 0 < zS) :
    StrictMonoOn (fun zA => km_premium α ρ zA zS) (Set.Ioi 0) ↔ 1 < ρ := by
  have hc : 0 < ((1 - α) / α) ^ (1 / ρ) := Real.rpow_pos_of_pos (div_pos (sub_pos.2 hα1) hα) _
  have hs : 0 < zS ^ (-(1 / ρ)) := Real.rpow_pos_of_pos hS _
  constructor
  · intro h
    by_contra hle
    have hle := not_lt.1 hle
    have h12 := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos)
      one_lt_two
    simp only [km_premium, Real.one_rpow, mul_one] at h12
    have hθ : (ρ - 1) / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hρ.le
    have h2 : (2 : ℝ) ^ ((ρ - 1) / ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two hθ
    have : ((1 - α) / α) ^ (1 / ρ) * 2 ^ ((ρ - 1) / ρ) * zS ^ (-(1 / ρ)) ≤
        ((1 - α) / α) ^ (1 / ρ) * zS ^ (-(1 / ρ)) := by
      have := mul_le_mul_of_nonneg_left h2 hc.le
      nlinarith
    linarith
  · intro h1 x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hθ : 0 < (ρ - 1) / ρ := (fs_theta_pos_iff hρ).2 h1
    simp only [km_premium]
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow hx'.le hxy hθ) hc) hs

/-- **AKMM, p. 639: "with a Cobb–Douglas function, factor-augmenting technological change cannot
affect the relative input prices".** For `G = X^α Y^{1−α}`, `A_s G_Y/(A_u G_X) = ((1 − α)/α)(u/s)`
whatever `A_s, A_u`. -/
theorem km_cd_premium {α Au u As s : ℝ} (hα : 0 < α) (hAu : 0 < Au) (hu : 0 < u) (hAs : 0 < As)
    (hs : 0 < s) :
    HasDerivAt (fun z => z ^ α * (As * s) ^ (1 - α))
        (α * (Au * u) ^ (α - 1) * (As * s) ^ (1 - α)) (Au * u) ∧
      HasDerivAt (fun z => (Au * u) ^ α * z ^ (1 - α))
        ((Au * u) ^ α * ((1 - α) * (As * s) ^ (1 - α - 1))) (As * s) ∧
      As * ((Au * u) ^ α * ((1 - α) * (As * s) ^ (1 - α - 1))) /
        (Au * (α * (Au * u) ^ (α - 1) * (As * s) ^ (1 - α))) = (1 - α) / α * (u / s) := by
  have hX : 0 < Au * u := mul_pos hAu hu
  have hY : 0 < As * s := mul_pos hAs hs
  refine ⟨(Real.hasDerivAt_rpow_const (Or.inl hX.ne')).mul_const _,
    (Real.hasDerivAt_rpow_const (Or.inl hY.ne')).const_mul _, ?_⟩
  rw [Real.rpow_sub hX, Real.rpow_sub hY, Real.rpow_one, Real.rpow_one]
  have := Real.rpow_pos_of_pos hX α
  have := Real.rpow_pos_of_pos hY (1 - α)
  field_simp

/-- **AKMM, p. 639: the Katz–Murphy regression.** With `A_s/A_u = (1 + γ)ᵗ` the log premium is
`−β₁ log(s/u) + β₂ t + c` with `β₁ = 1/ρ`, `β₂ = ((ρ − 1)/ρ) log(1 + γ)`; conversely `β₁`
identifies `ρ = 1/β₁` and then `β₂` identifies `1 + γ = exp(β₂/(1 − β₁))` (for `ρ ≠ 1`). -/
theorem km_identify {α ρ γ zS : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hγ : 0 < 1 + γ) (hS : 0 < zS) (t : ℕ) :
    Real.log (km_premium α ρ ((1 + γ) ^ t) zS) =
        -(1 / ρ) * Real.log zS + ((ρ - 1) / ρ * Real.log (1 + γ)) * t +
          1 / ρ * Real.log ((1 - α) / α) ∧
      ρ = 1 / (1 / ρ) ∧ 1 + γ = Real.exp ((ρ - 1) / ρ * Real.log (1 + γ) / (1 - 1 / ρ)) := by
  refine ⟨?_, by field_simp, ?_⟩
  · rw [km_log_premium hα hα1 (pow_pos hγ t) hS, Real.log_pow]
    ring
  · have hr : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
    have e : (ρ - 1) / ρ * Real.log (1 + γ) / (1 - 1 / ρ) = Real.log (1 + γ) := by
      field_simp
    rw [e, Real.exp_log hγ]

/-! ### Directed technical change -/

/-- AKMM, p. 640: the objective `(A_s s)^σ + (A_u u)^σ` (a monotone transform of
`[(A_s s)^σ + (A_u u)^σ]^{1/σ}` for `σ > 0`). -/
noncomputable def dt_obj (σ s u As Au : ℝ) : ℝ := (As * s) ^ σ + (Au * u) ^ σ

/-- AKMM, p. 640: the technology frontier `λA_s^φ + (1 − λ)A_u^φ`. -/
noncomputable def dt_con (lam φ As Au : ℝ) : ℝ := lam * As ^ φ + (1 - lam) * Au ^ φ

/-- AKMM, p. 640: the tangent bound behind the first-order condition. For `0 < σ < φ`,
`B ≥ 0`, `A, s > 0`: `(Bs)^σ ≤ (As)^σ + (σ/φ) s^σ A^{σ−φ} (B^φ − A^φ)`, strictly if `B ≠ A`
(Bernoulli's inequality for the exponent `σ/φ ∈ (0, 1)`). -/
theorem dt_term_le {σ φ s A B : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hs : 0 < s) (hA : 0 < A)
    (hB : 0 ≤ B) :
    (B * s) ^ σ ≤ (A * s) ^ σ + σ / φ * s ^ σ * A ^ (σ - φ) * (B ^ φ - A ^ φ) ∧
      (B ≠ A → (B * s) ^ σ < (A * s) ^ σ + σ / φ * s ^ σ * A ^ (σ - φ) * (B ^ φ - A ^ φ)) := by
  have hφ : 0 < φ := hσ.trans hσφ
  set κ := σ / φ with hκ
  have hκ0 : 0 < κ := div_pos hσ hφ
  have hκ1 : κ < 1 := (div_lt_one hφ).2 hσφ
  set z0 := A ^ φ
  set z := B ^ φ
  have hz0 : 0 < z0 := Real.rpow_pos_of_pos hA φ
  have hz : 0 ≤ z := Real.rpow_nonneg hB φ
  have hBpow : B ^ σ = z ^ κ := by
    rw [← Real.rpow_mul hB]; congr 1; rw [hκ]; field_simp
  have hApow : A ^ σ = z0 ^ κ := by
    rw [← Real.rpow_mul hA.le]; congr 1; rw [hκ]; field_simp
  have hAm : A ^ (σ - φ) = z0 ^ κ / z0 := by
    rw [Real.rpow_sub hA, hApow]
  set t := z / z0 - 1 with ht
  have ht1 : -1 ≤ t := by rw [ht]; have := div_nonneg hz hz0.le; linarith
  have hzt : z = z0 * (1 + t) := by rw [ht]; field_simp; ring
  have hzk : z ^ κ = z0 ^ κ * (1 + t) ^ κ := by
    rw [hzt, Real.mul_rpow hz0.le (by linarith)]
  have hsσ : 0 < s ^ σ := Real.rpow_pos_of_pos hs σ
  have hz0k : 0 < z0 ^ κ := Real.rpow_pos_of_pos hz0 κ
  have key : ∀ q : ℝ, q ≤ 1 + κ * t →
      s ^ σ * (z0 ^ κ * q) ≤ (A * s) ^ σ + σ / φ * s ^ σ * A ^ (σ - φ) * (B ^ φ - A ^ φ) := by
    intro q hq
    rw [Real.mul_rpow hA.le hs.le, hApow, hAm, ← hκ]
    have e : κ * s ^ σ * (z0 ^ κ / z0) * (z - z0) = s ^ σ * z0 ^ κ * (κ * t) := by
      rw [ht]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hq (mul_pos hsσ hz0k).le
    nlinarith
  have hlhs : (B * s) ^ σ = s ^ σ * (z0 ^ κ * (1 + t) ^ κ) := by
    rw [Real.mul_rpow hB hs.le, hBpow, hzk]; ring
  refine ⟨?_, fun hne => ?_⟩
  · rw [hlhs]
    exact key _ (rpow_one_add_le_one_add_mul_self ht1 hκ0.le hκ1.le)
  · have htne : t ≠ 0 := by
      intro h0
      apply hne
      have hzz : z = z0 := by rw [hzt, h0]; ring
      have := congrArg (fun x => x ^ φ⁻¹) hzz
      simp only [z, z0] at this
      rwa [Real.rpow_rpow_inv hB hφ.ne', Real.rpow_rpow_inv hA.le hφ.ne'] at this
    have hlt := rpow_one_add_lt_one_add_mul_self ht1 htne hκ0 hκ1
    have hq := key (1 + κ * t) le_rfl
    rw [hlhs]
    have : s ^ σ * (z0 ^ κ * (1 + t) ^ κ) < s ^ σ * (z0 ^ κ * (1 + κ * t)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hlt hz0k) hsσ
    linarith

/-- **AKMM, p. 640: the first-order condition solves the directed-technology problem.** If
`(A_s, A_u) > 0` is on the frontier and satisfies `A_s^{σ−φ}s^σ/λ = A_u^{σ−φ}u^σ/(1 − λ)`, then
every `(B_s, B_u) ≥ 0` on the frontier gives a weakly lower objective, strictly lower unless it
equals `(A_s, A_u)`. -/
theorem dt_optimal {σ φ lam s u As Au : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hs : 0 < s) (hu : 0 < u) (hAs : 0 < As) (hAu : 0 < Au)
    (hcon : dt_con lam φ As Au = 1)
    (hfoc : As ^ (σ - φ) * s ^ σ / lam = Au ^ (σ - φ) * u ^ σ / (1 - lam)) {Bs Bu : ℝ}
    (hBs : 0 ≤ Bs) (hBu : 0 ≤ Bu) (hconB : dt_con lam φ Bs Bu = 1) :
    dt_obj σ s u Bs Bu ≤ dt_obj σ s u As Au ∧
      ((Bs, Bu) ≠ (As, Au) → dt_obj σ s u Bs Bu < dt_obj σ s u As Au) := by
  obtain ⟨h1, h1s⟩ := dt_term_le hσ hσφ hs hAs hBs
  obtain ⟨h2, h2s⟩ := dt_term_le hσ hσφ hu hAu hBu
  set μ := As ^ (σ - φ) * s ^ σ / lam with hμ
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have e1 : s ^ σ * As ^ (σ - φ) = μ * lam := by rw [hμ]; field_simp
  have e2 : u ^ σ * Au ^ (σ - φ) = μ * (1 - lam) := by rw [hfoc]; field_simp
  have hsum : σ / φ * s ^ σ * As ^ (σ - φ) * (Bs ^ φ - As ^ φ) +
      σ / φ * u ^ σ * Au ^ (σ - φ) * (Bu ^ φ - Au ^ φ) = 0 := by
    have : σ / φ * (μ * lam) * (Bs ^ φ - As ^ φ) + σ / φ * (μ * (1 - lam)) * (Bu ^ φ - Au ^ φ)
        = σ / φ * μ * (dt_con lam φ Bs Bu - dt_con lam φ As Au) := by
      unfold dt_con; ring
    rw [hconB, hcon, sub_self, mul_zero] at this
    rw [mul_assoc (σ / φ) (s ^ σ), e1, mul_assoc (σ / φ) (u ^ σ), e2]
    exact this
  unfold dt_obj
  refine ⟨by linarith, fun hne => ?_⟩
  by_cases hb : Bs = As
  · have hb' : Bu ≠ Au := fun h => hne (by rw [hb, h])
    have := h2s hb'
    linarith
  · have := h1s hb
    linarith

/-- AKMM, p. 640: the optimal direction `ζ = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}`. -/
noncomputable def dt_ratio (σ φ lam s u : ℝ) : ℝ :=
  (lam / (1 - lam)) ^ (1 / (σ - φ)) * (s / u) ^ (σ / (φ - σ))

/-- AKMM, p. 640: for positive technologies the first-order condition is equivalent to
`A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}`. -/
theorem dt_foc_iff_ratio {σ φ lam s u As Au : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hs : 0 < s) (hu : 0 < u) (hAs : 0 < As) (hAu : 0 < Au) :
    As ^ (σ - φ) * s ^ σ / lam = Au ^ (σ - φ) * u ^ σ / (1 - lam) ↔
      As / Au = dt_ratio σ φ lam s u := by
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have he : σ - φ ≠ 0 := by linarith
  have hc : 0 < lam / (1 - lam) := div_pos hl0 hl1'
  have hsu : 0 < s / u := div_pos hs hu
  have hζ : 0 < dt_ratio σ φ lam s u :=
    mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos hsu _)
  have hζe : dt_ratio σ φ lam s u ^ (σ - φ) = lam / (1 - lam) * (u ^ σ / s ^ σ) := by
    unfold dt_ratio
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hc _).le (Real.rpow_pos_of_pos hsu _).le,
      ← Real.rpow_mul hc.le, ← Real.rpow_mul hsu.le]
    have e1 : 1 / (σ - φ) * (σ - φ) = 1 := by field_simp
    have e2 : σ / (φ - σ) * (σ - φ) = -σ := by
      have : φ - σ ≠ 0 := by linarith
      field_simp; ring
    rw [e1, e2, Real.rpow_one, Real.rpow_neg hsu.le, Real.div_rpow hs.le hu.le]
    have := Real.rpow_pos_of_pos hs σ
    have := Real.rpow_pos_of_pos hu σ
    field_simp
  have hAA : 0 < As / Au := div_pos hAs hAu
  have hsσ := Real.rpow_pos_of_pos hs σ
  have huσ := Real.rpow_pos_of_pos hu σ
  have hAsσ := Real.rpow_pos_of_pos hAs (σ - φ)
  have hAuσ := Real.rpow_pos_of_pos hAu (σ - φ)
  constructor
  · intro hfoc
    have hpow : (As / Au) ^ (σ - φ) = dt_ratio σ φ lam s u ^ (σ - φ) := by
      rw [hζe, Real.div_rpow hAs.le hAu.le]
      field_simp at hfoc ⊢
      linarith
    have := congrArg (fun x => x ^ (σ - φ)⁻¹) hpow
    rwa [Real.rpow_rpow_inv hAA.le he, Real.rpow_rpow_inv hζ.le he] at this
  · intro hr
    have hpow : (As / Au) ^ (σ - φ) = lam / (1 - lam) * (u ^ σ / s ^ σ) := by rw [hr, hζe]
    rw [Real.div_rpow hAs.le hAu.le] at hpow
    field_simp at hpow ⊢
    linarith

/-- AKMM, p. 640: a point on the frontier with the optimal direction exists:
`A_u = (λζ^φ + 1 − λ)^{−1/φ}`, `A_s = ζA_u`. -/
theorem dt_exists {σ φ lam s u : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < s) (hu : 0 < u) :
    ∃ As Au : ℝ, 0 < As ∧ 0 < Au ∧ dt_con lam φ As Au = 1 ∧
      As / Au = dt_ratio σ φ lam s u := by
  have hφ : 0 < φ := hσ.trans hσφ
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have hζ : 0 < dt_ratio σ φ lam s u :=
    mul_pos (Real.rpow_pos_of_pos (div_pos hl0 hl1') _) (Real.rpow_pos_of_pos (div_pos hs hu) _)
  set ζ := dt_ratio σ φ lam s u
  set D := lam * ζ ^ φ + (1 - lam)
  have hD : 0 < D := by have := Real.rpow_pos_of_pos hζ φ; positivity
  set Au := D ^ (-(1 / φ))
  have hAu : 0 < Au := Real.rpow_pos_of_pos hD _
  have hAuφ : Au ^ φ = D⁻¹ := by
    rw [← Real.rpow_mul hD.le, show -(1 / φ) * φ = -1 by field_simp, Real.rpow_neg_one]
  refine ⟨ζ * Au, Au, mul_pos hζ hAu, hAu, ?_, by field_simp⟩
  unfold dt_con
  rw [Real.mul_rpow hζ.le hAu.le, hAuφ]
  field_simp
  rfl

/-- **AKMM, p. 640: "The first-order condition becomes `A_s/A_u = …`".** Every maximiser of the
objective on the frontier (over `A_s, A_u ≥ 0`) has
`A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}` (book: `σ ∈ (0, 1)`, `φ > 1`; `0 < σ < φ`
suffices). -/
theorem dt_maximiser_ratio {σ φ lam s u Bs Bu : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hs : 0 < s) (hu : 0 < u) (hBs : 0 ≤ Bs) (hBu : 0 ≤ Bu)
    (hcon : dt_con lam φ Bs Bu = 1)
    (hmax : ∀ Cs Cu : ℝ, 0 ≤ Cs → 0 ≤ Cu → dt_con lam φ Cs Cu = 1 →
      dt_obj σ s u Cs Cu ≤ dt_obj σ s u Bs Bu) :
    0 < Bu ∧ Bs / Bu = dt_ratio σ φ lam s u := by
  obtain ⟨As, Au, hAs, hAu, hc, hr⟩ := dt_exists hσ hσφ hl0 hl1 hs hu
  have hfoc := (dt_foc_iff_ratio hσφ hl0 hl1 hs hu hAs hAu).2 hr
  obtain ⟨-, hstrict⟩ := dt_optimal hσ hσφ hl0 hl1 hs hu hAs hAu hc hfoc hBs hBu hcon
  have heq : (Bs, Bu) = (As, Au) := by
    by_contra hne
    have h1 := hstrict hne
    have h2 := hmax As Au hAs.le hAu.le hc
    linarith
  simp only [Prod.mk.injEq] at heq
  rw [heq.1, heq.2]
  exact ⟨hAu, hr⟩

/-- **AKMM, p. 640, the printed first-order condition** `A_s/A_u = (λ/(1 − λ))(s/u)^{σ/(φ−σ)}`
agrees with the optimum only for `λ = 1/2`: for `σ < φ`,
`(λ/(1 − λ))^{1/(σ−φ)} = λ/(1 − λ)` iff `λ = 1/2`. -/
theorem dt_printed_ratio_iff {σ φ lam : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1) :
    (lam / (1 - lam)) ^ (1 / (σ - φ)) = lam / (1 - lam) ↔ lam = 1 / 2 := by
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have hx : 0 < lam / (1 - lam) := div_pos hl0 hl1'
  have he : 1 / (σ - φ) < 0 := one_div_neg.2 (by linarith)
  constructor
  · intro h
    have hlog := congrArg Real.log h
    rw [Real.log_rpow hx] at hlog
    have hl : Real.log (lam / (1 - lam)) = 0 := by
      have : (1 / (σ - φ) - 1) * Real.log (lam / (1 - lam)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exact h0
    have h1 := Real.eq_one_of_pos_of_log_eq_zero hx hl
    field_simp at h1
    linarith
  · intro h
    have h1 : lam / (1 - lam) = 1 := by rw [h]; norm_num
    rw [h1, Real.one_rpow]

/-- **AKMM, p. 640:** "a higher relative skill supply attracts more R&D": for `0 < σ < φ` the
optimal `A_s/A_u` is strictly increasing in `s/u` (here in `s` for fixed `u`). -/
theorem dt_ratio_strictMono {σ φ lam u : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hu : 0 < u) : StrictMonoOn (fun s => dt_ratio σ φ lam s u) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hc : 0 < (lam / (1 - lam)) ^ (1 / (σ - φ)) :=
    Real.rpow_pos_of_pos (div_pos hl0 (sub_pos.2 hl1)) _
  simp only [dt_ratio]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (div_pos hx' hu).le
    (div_lt_div_of_pos_right hxy hu) (div_pos hσ (by linarith))) hc

/-- **AKMM, p. 640: the relative wage.** With output `Y = [(A_s s)^σ + (A_u u)^σ]^{1/σ}`, the
marginal products give `w_s/w_u = (A_s/A_u)^σ (s/u)^{σ−1}`. -/
theorem dt_wage_ratio {σ s u As Au : ℝ} (hσ : σ ≠ 0) (hs : 0 < s) (hu : 0 < u) (hAs : 0 < As)
    (hAu : 0 < Au) :
    ∃ ws wu : ℝ, HasDerivAt (fun z => dt_obj σ z u As Au ^ (1 / σ)) ws s ∧
      HasDerivAt (fun z => dt_obj σ s z As Au ^ (1 / σ)) wu u ∧
      ws / wu = (As / Au) ^ σ * (s / u) ^ (σ - 1) := by
  have hO : 0 < dt_obj σ s u As Au := by
    unfold dt_obj
    have := Real.rpow_pos_of_pos (mul_pos hAs hs) σ
    have := Real.rpow_pos_of_pos (mul_pos hAu hu) σ
    positivity
  have h1 : HasDerivAt (fun z => dt_obj σ z u As Au)
      (As * (σ * (As * s) ^ (σ - 1))) s := by
    unfold dt_obj
    exact (((hasDerivAt_id s).const_mul As).rpow_const (p := σ)
      (Or.inl (mul_pos hAs hs).ne')).add_const _ |>.congr_deriv (by simp only [id]; ring)
  have h2 : HasDerivAt (fun z => dt_obj σ s z As Au)
      (Au * (σ * (Au * u) ^ (σ - 1))) u := by
    unfold dt_obj
    exact (((hasDerivAt_id u).const_mul Au).rpow_const (p := σ)
      (Or.inl (mul_pos hAu hu).ne')).const_add _ |>.congr_deriv (by simp only [id]; ring)
  refine ⟨_, _, h1.rpow_const (Or.inl hO.ne'), h2.rpow_const (Or.inl hO.ne'), ?_⟩
  have hP := Real.rpow_pos_of_pos hO (1 / σ - 1)
  rw [Real.mul_rpow hAs.le hs.le, Real.mul_rpow hAu.le hu.le, Real.div_rpow hAs.le hAu.le,
    Real.div_rpow hs.le hu.le, Real.rpow_sub hAs, Real.rpow_sub hAu, Real.rpow_sub hs,
    Real.rpow_sub hu, Real.rpow_one, Real.rpow_one, Real.rpow_one, Real.rpow_one]
  have := Real.rpow_pos_of_pos hAs σ
  have := Real.rpow_pos_of_pos hAu σ
  have := Real.rpow_pos_of_pos hs σ
  have := Real.rpow_pos_of_pos hu σ
  field_simp

/-- **AKMM, p. 640: the premium at the directed-technology optimum.** Substituting
`A_s/A_u = ζ` into `(A_s/A_u)^σ (s/u)^{σ−1}` gives
`(λ/(1 − λ))^{σ/(σ−φ)} (s/u)^{(σ − φ(1 − σ))/(φ − σ)}`. -/
theorem dt_premium_closed {σ φ lam s u : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < s) (hu : 0 < u) :
    dt_ratio σ φ lam s u ^ σ * (s / u) ^ (σ - 1) =
      (lam / (1 - lam)) ^ (σ / (σ - φ)) * (s / u) ^ ((σ - φ * (1 - σ)) / (φ - σ)) := by
  have hc : 0 < lam / (1 - lam) := div_pos hl0 (sub_pos.2 hl1)
  have hsu : 0 < s / u := div_pos hs hu
  have h1 : σ - φ ≠ 0 := by linarith
  have h2 : φ - σ ≠ 0 := by linarith
  unfold dt_ratio
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hc _).le (Real.rpow_pos_of_pos hsu _).le,
    ← Real.rpow_mul hc.le, ← Real.rpow_mul hsu.le, mul_assoc, ← Real.rpow_add hsu]
  congr 2
  · field_simp
  · field_simp; ring

/-- **AKMM, p. 640:** `log(w_s/w_u) = (σ/(σ − φ)) log(λ/(1 − λ))
+ ((σ − φ(1 − σ))/(φ − σ)) log(s/u)`, i.e. `log(w_s/w_u) ∝ ((σ − φ(1 − σ))/(φ − σ)) log(s/u)`. -/
theorem dt_log_premium {σ φ lam s u : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < s) (hu : 0 < u) :
    Real.log (dt_ratio σ φ lam s u ^ σ * (s / u) ^ (σ - 1)) =
      σ / (σ - φ) * Real.log (lam / (1 - lam)) +
        (σ - φ * (1 - σ)) / (φ - σ) * Real.log (s / u) := by
  have hc : 0 < lam / (1 - lam) := div_pos hl0 (sub_pos.2 hl1)
  have hsu : 0 < s / u := div_pos hs hu
  rw [dt_premium_closed hσφ hl0 hl1 hs hu, Real.log_mul (Real.rpow_pos_of_pos hc _).ne'
    (Real.rpow_pos_of_pos hsu _).ne', Real.log_rpow hc, Real.log_rpow hsu]

/-- **AKMM, p. 640: "the skill premium is increasing in `s/u` as long as
`ρ − 1 = σ/(1 − σ) > φ`".** For `0 < σ < 1` and `σ < φ` the exponent
`(σ − φ(1 − σ))/(φ − σ)` is positive iff `σ/(1 − σ) > φ`, and `ρ = 1/(1 − σ)` has
`ρ − 1 = σ/(1 − σ)`. -/
theorem dt_exponent_pos_iff {σ φ : ℝ} (hσ1 : σ < 1) (hσφ : σ < φ) :
    (0 < (σ - φ * (1 - σ)) / (φ - σ) ↔ φ < σ / (1 - σ)) ∧ 1 / (1 - σ) - 1 = σ / (1 - σ) := by
  have h1 : 0 < 1 - σ := sub_pos.2 hσ1
  refine ⟨?_, by field_simp; ring⟩
  rw [div_pos_iff_of_pos_right (sub_pos.2 hσφ), lt_div_iff₀ h1, sub_pos]

/-- **AKMM, p. 640:** "with a large enough elasticity of substitution … (at least above 2)":
`ρ − 1 > φ > 1` gives `ρ = 1/(1 − σ) > 2`. -/
theorem dt_rho_gt_two {σ φ : ℝ} (hσ1 : σ < 1) (hφ : 1 < φ) (h : φ < σ / (1 - σ)) :
    2 < 1 / (1 - σ) := by
  have h1 : 0 < 1 - σ := sub_pos.2 hσ1
  have e : 1 / (1 - σ) = σ / (1 - σ) + 1 := by field_simp; ring
  linarith

/-! ### Capital–skill complementarity -/

/-- **AKMM, p. 641: `F(k, u, s) = u + s^ν k^{1−ν}`.** The unskilled wage is `1` and the skilled
wage `ν s^{ν−1} k^{1−ν}`. -/
theorem cs_ex1_wages {ν k u s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z => z + s ^ ν * k ^ (1 - ν)) 1 u ∧
      HasDerivAt (fun z => u + z ^ ν * k ^ (1 - ν)) (ν * s ^ (ν - 1) * k ^ (1 - ν)) s :=
  ⟨(hasDerivAt_id u).add_const _,
    ((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).mul_const _).const_add _⟩

/-- **AKMM, p. 641:** "higher capital raises the marginal product of skilled labor, whereas the
unskilled marginal product is unaffected": for `0 < ν < 1`, `s > 0` the premium
`ν s^{ν−1}k^{1−ν}/1` is strictly increasing in `k ≥ 0`. -/
theorem cs_ex1_premium_strictMono {ν s : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hs : 0 < s) :
    StrictMonoOn (fun k => ν * s ^ (ν - 1) * k ^ (1 - ν) / 1) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  simp only [div_one]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx' hxy (by linarith))
    (mul_pos hν (Real.rpow_pos_of_pos hs _))

/-- **AKMM, p. 641: `F = s^ν (k + u)^{1−ν}`.** The unskilled wage
`w_u = (1 − ν) s^ν (k + u)^{−ν}` … -/
theorem cs_ex2_wu {ν k u s : ℝ} (hku : 0 < k + u) :
    HasDerivAt (fun z => s ^ ν * (k + z) ^ (1 - ν)) (s ^ ν * ((1 - ν) * (k + u) ^ (-ν))) u := by
  have h := ((hasDerivAt_id u).const_add k).rpow_const (p := 1 - ν) (Or.inl hku.ne')
  refine (h.const_mul (s ^ ν)).congr_deriv ?_
  simp only [id, sub_sub_cancel_left, one_mul]

/-- **AKMM, p. 641:** "a rise in the capital stock now allows the real wage of unskilled
workers, `w_u`, to fall": for `0 < ν < 1`, `s > 0`, `u > 0`,
`w_u = (1 − ν) s^ν (k + u)^{−ν}` is strictly decreasing in `k ≥ 0`. -/
theorem cs_ex2_wu_strictAnti {ν u s : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hs : 0 < s) (hu : 0 < u) :
    StrictAntiOn (fun k => s ^ ν * ((1 - ν) * (k + u) ^ (-ν))) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  have h := Real.rpow_lt_rpow_of_neg (by linarith : 0 < x + u) (by linarith : x + u < y + u)
    (by linarith : -ν < 0)
  have hc : 0 < s ^ ν * (1 - ν) := mul_pos (Real.rpow_pos_of_pos hs _) (by linarith)
  have := mul_lt_mul_of_pos_left h hc
  simp only
  linarith [this, show s ^ ν * ((1 - ν) * (y + u) ^ (-ν)) = s ^ ν * (1 - ν) * (y + u) ^ (-ν)
    by ring, show s ^ ν * ((1 - ν) * (x + u) ^ (-ν)) = s ^ ν * (1 - ν) * (x + u) ^ (-ν) by ring]

/-- AKMM, p. 641: under the nesting `F(u, G(k, s))` with `F` of constant returns,
`F(u, G) = u f(G/u)`, the unskilled wage is `w_u = f(x) − x f′(x)`, `x = G/u`. -/
theorem cs_nest_wu {f : ℝ → ℝ} {f' u G : ℝ} (hu : 0 < u)
    (hf : HasDerivAt f f' (G / u)) :
    HasDerivAt (fun z => z * f (G / z)) (f (G / u) - G / u * f') u := by
  have hq : HasDerivAt (fun z => G / z) (-(G / u ^ 2)) u :=
    ((hasDerivAt_const u G).div (hasDerivAt_id u) hu.ne').congr_deriv (by simp [neg_div])
  have h := (hasDerivAt_id u).mul (hf.comp u hq)
  refine h.congr_deriv ?_
  simp only [id, Function.comp]
  field_simp
  ring

/-- **AKMM, p. 641: "This feature … cannot be obtained under the previous nesting."** If `f`
is concave (tangent inequalities with derivative `f′`), then `w_u = f(x) − x f′(x)` is
nondecreasing in `x = G/u ≥ 0`; since `G` is increasing in `k`, `w_u` cannot fall as `k`
rises under `F(u, G(k, s))`. -/
theorem cs_nest_wu_monotone {f f' : ℝ → ℝ}
    (htan : ∀ x y, 0 ≤ x → 0 ≤ y → f x ≤ f y + f' y * (x - y)) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : f x - x * f' x ≤ f y - y * f' y := by
  have hy : 0 ≤ y := hx.trans hxy
  have h1 := htan x y hx hy
  have h2 := htan y x hy hx
  -- concavity: f' y ≤ f' x
  have hmono : (f' y - f' x) * (y - x) ≤ 0 := by nlinarith
  have hd : f' y ≤ f' x := by
    rcases hxy.eq_or_lt with h | h
    · rw [h]
    · nlinarith
  nlinarith

/-- **AKMM, p. 641: both nests CES.** With `F(u, G) = fs_ces α ρ u G` and
`G(k, s) = fs_ces β η k s`, the premium `w_s/w_u = F_G G_s/F_u` equals
`((1 − α)/α)^{1/ρ} (1 − β)^{1/η} u^{1/ρ} s^{−1/η} G^{1/η − 1/ρ}`. -/
theorem cs_ces_nest_premium {α ρ β η u k s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (hβ : 0 < β) (hβ1 : β < 1) (hη : 0 < η) (hη1 : η ≠ 1) (hu : 0 < u)
    (hk : 0 < k) (hs : 0 < s) :
    ∃ Fu FG Gs : ℝ,
      HasDerivAt (fun z => fs_ces α ρ z (fs_ces β η k s)) Fu u ∧
      HasDerivAt (fun z => fs_ces α ρ u z) FG (fs_ces β η k s) ∧
      HasDerivAt (fun z => fs_ces β η k z) Gs s ∧
      FG * Gs / Fu = ((1 - α) / α) ^ (1 / ρ) * (1 - β) ^ (1 / η) * u ^ (1 / ρ) *
        s ^ (-(1 / η)) * fs_ces β η k s ^ (1 / η - 1 / ρ) := by
  have hG : 0 < fs_ces β η k s := Real.rpow_pos_of_pos (by
    have := Real.rpow_pos_of_pos hβ (1 / η)
    have := Real.rpow_pos_of_pos hk ((η - 1) / η)
    have := Real.rpow_pos_of_pos (sub_pos.2 hβ1) (1 / η)
    have := Real.rpow_pos_of_pos hs ((η - 1) / η)
    positivity) _
  set G := fs_ces β η k s
  have h1 := wi_ces_hasDerivAt hα hα1 hρ hρ1 hu hG
  have h2 := wi_ces_hasDerivAt (α := 1 - α) (by linarith) (by linarith) hρ hρ1 hG hu
  simp only [← fs_ces_symm] at h2
  have h3 := wi_ces_hasDerivAt (α := 1 - β) (by linarith) (by linarith) hη hη1 hs hk
  simp only [← fs_ces_symm] at h3
  refine ⟨_, _, _, h1, h2, h3, ?_⟩
  set F := fs_ces α ρ u G
  have hF : 0 < F := Real.rpow_pos_of_pos (by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hu ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hG ((ρ - 1) / ρ)
    positivity) _
  rw [Real.div_rpow hF.le hG.le, Real.div_rpow hF.le hu.le, Real.div_rpow hG.le hs.le,
    Real.div_rpow (sub_pos.2 hα1).le hα.le, Real.rpow_neg hs.le, Real.rpow_sub hG]
  have := Real.rpow_pos_of_pos hF (1 / ρ)
  have := Real.rpow_pos_of_pos hG (1 / ρ)
  have := Real.rpow_pos_of_pos hG (1 / η)
  have := Real.rpow_pos_of_pos hu (1 / ρ)
  have := Real.rpow_pos_of_pos hs (1 / η)
  have := Real.rpow_pos_of_pos hα (1 / ρ)
  field_simp

/-- **AKMM, p. 641: "if the elasticity in `F` is greater than that in `G`, then the skill
premium rises as `k` goes up".** `G = fs_ces β η k s` is strictly increasing in `k > 0`, and the
premium `C·G^{1/η − 1/ρ}` (`C > 0`) is strictly increasing in `G > 0` iff `ρ > η`. -/
theorem cs_ces_nest_strictMono {β η ρ s C : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hη : 0 < η)
    (hη1 : η ≠ 1) (hρ : 0 < ρ) (hs : 0 < s) (hC : 0 < C) :
    StrictMonoOn (fun k => fs_ces β η k s) (Set.Ioi 0) ∧
      (StrictMonoOn (fun G => C * G ^ (1 / η - 1 / ρ)) (Set.Ioi 0) ↔ η < ρ) := by
  constructor
  · have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun k => fs_ces β η k s)
        (β ^ (1 / η) * (fs_ces β η x s / x) ^ (1 / η)) x :=
      fun x hx => wi_ces_hasDerivAt hβ hβ1 hη hη1 hx hs
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hx' : (0 : ℝ) < x := hx
      rw [(hd x hx).deriv]
      have hG : 0 < fs_ces β η x s := Real.rpow_pos_of_pos (by
        have := Real.rpow_pos_of_pos hβ (1 / η)
        have := Real.rpow_pos_of_pos hx' ((η - 1) / η)
        have := Real.rpow_pos_of_pos (sub_pos.2 hβ1) (1 / η)
        have := Real.rpow_pos_of_pos hs ((η - 1) / η)
        positivity) _
      exact mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos (div_pos hG hx') _)
  · constructor
    · intro h
      by_contra hle
      have hle := not_lt.1 hle
      have he : 1 / η - 1 / ρ ≤ 0 := by
        have := one_div_le_one_div_of_le hρ hle
        linarith
      have h12 := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos)
        one_lt_two
      simp only [Real.one_rpow, mul_one] at h12
      have h2 : (2 : ℝ) ^ (1 / η - 1 / ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two he
      nlinarith
    · intro hlt x hx y hy hxy
      have hx' : (0 : ℝ) < x := hx
      have he : 0 < 1 / η - 1 / ρ := by
        have := one_div_lt_one_div_of_lt hη hlt
        linarith
      exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx'.le hxy he) hC

end AKMM.Inequality
