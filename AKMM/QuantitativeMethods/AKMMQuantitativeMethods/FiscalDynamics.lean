/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMQuantitativeMethods.FiscalModel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The linearised fiscal model and the claims of Figure 8.4

AKMM, §8.6.1–8.6.2, pp. 229–231; §8.8 and Figure 8.4, pp. 234–236; §8.9, p. 238.

The model of §8.6 ((8.10)–(8.18), `FiscalModel`) is linearised around its steady state, as the
book does for Figure 8.4, and its impulse response to a spending shock `η̂ₜ = ρᵗ` is solved in
closed form. Spending follows (8.18), `G = γηc`, so `Ĝ = η̂ + ĉ`.

* **The linearisation**: the static equations are exactly log-linear (`fd_static_exact`); the
  resource constraint and the Euler equation are linearised by their derivatives at the steady
  state (`fd_resource_linear`, `fd_euler_linear`); the coefficients are the steady-state ratios
  (`fd_ratios`). The linearised impulse-response system is `fd_IsIRF`.
* **The saddle path**: the stable root `λ ∈ (0, 1/(1+κ))` (`fd_lam_props`, `fd_lam_lt_one`),
  the closed-form response `k̂ₜ₊₁ = λk̂ₜ − φρᵗ`, `ĉₜ = pk̂ₜ + qρᵗ` solves the system
  (`fd_irf_solves`), is bounded (`fd_k_bound`) and is the only bounded solution (`fd_irf_unique`).
* **The signs of Figure 8.4 (left)**: for `0 ≤ ρ < 1/(1+κ)`, on impact consumption falls, hours
  and output rise, spending rises by less than the shock, investment falls (`fd_impact_signs`);
  consumption stays below and capital below steady state at every date (`fd_c_k_neg`).
  **Correction**: investment falls on impact only when `ρ < 1/(1+κ)`, `κ = βr̄(1−α)/(ψ+α)`; it
  rises for `1/(1+κ) < ρ ≤ 1`, e.g. for a permanent shock (`fd_investment_correction`).
* **Multipliers**: output rises by less than spending over every horizon, so every cumulative
  multiplier is below one (`fd_cum_lt`, `fd_mult_lt_one`); the impact multiplier is in `(0, 1)`
  (`fd_impact_mult`, `fd_impact_mult_mem`).
* **Persistence (§8.6.2; Fig. 8.4, right)**: the impact multiplier is strictly increasing in `ρ`
  on `[0, 1/(1+κ)]` (`fd_impact_mult_strictMonoOn_rho`); the cumulative multiplier converges as
  the horizon grows (`fd_mult_tendsto`) and its limit, the whole-horizon multiplier, is strictly
  increasing in `ρ` wherever cumulative spending rises (`fd_multInf_strictMono`, with
  `fd_inf_closed`, `fd_key`, `fd_det`, `fd_GInf_pos_top`).
* **Labour supply (Fig. 8.4, right)**: for `δ ≤ 1` the stable root rises with `ψ`
  (`fd_pencil`, `fd_le_lam`, `fd_f0_nonneg`, `fd_lam_mono_psi`) and the impact multiplier is
  strictly larger for smaller `ψ` (`fd_impact_mult_Phi`, `fd_impact_mult_antitone_psi`).

Not formalised: the 12-quarter multiplier of the figure is monotone in `ρ` and `ψ` only
numerically (the proofs above cover the impact and whole-horizon multipliers); "close to zero",
"after 5 quarters, output falls below steady state" and the relative sizes of the responses are
calibrated numbers.
-/

namespace AKMM.QuantitativeMethods

open Filter Topology Finset

/-! ### The coefficients of the linearised model -/

/-- AKMM, p. 842: the steady-state output–capital ratio `ȳ/k̄ = r̄/α`. -/
noncomputable def fd_Y (α β δ : ℝ) : ℝ := fm_r β δ / α

/-- AKMM, p. 842: the steady-state consumption–capital ratio `c̄/k̄ = (ȳ/k̄ − δ)/(1+γ)`. -/
noncomputable def fd_C (α β δ γ : ℝ) : ℝ := (fd_Y α β δ - δ) / (1 + γ)

/-- The steady-state spending–capital ratio `Ḡ/k̄ = γc̄/k̄`. -/
noncomputable def fd_g (α β δ γ : ℝ) : ℝ := γ * fd_C α β δ γ

/-- `κ = βr̄(1−α)/(ψ+α)`, the coefficient of the reduced Euler equation. -/
noncomputable def fd_kap (α β δ ψ : ℝ) : ℝ := β * fm_r β δ * (1 - α) / (ψ + α)

/-- `m = 1 − δ + r̄(1+ψ)/(ψ+α)`, the coefficient on `k̂ₜ` in the reduced capital equation. -/
noncomputable def fd_m (α β δ ψ : ℝ) : ℝ := 1 - δ + fm_r β δ * (1 + ψ) / (ψ + α)

/-- `n = (ȳ/k̄)(1−α)/(ψ+α) + (1+γ)c̄/k̄`, the coefficient on `−ĉₜ` in the capital equation. -/
noncomputable def fd_n (α β δ ψ γ : ℝ) : ℝ :=
  fd_Y α β δ * (1 - α) / (ψ + α) + (1 + γ) * fd_C α β δ γ

/-- The middle coefficient `B = (1+κ)m + 1 + nκψ` of the characteristic polynomial
`(1+κ)λ² − Bλ + m`. -/
noncomputable def fd_B (α β δ ψ γ : ℝ) : ℝ :=
  (1 + fd_kap α β δ ψ) * fd_m α β δ ψ + 1 + fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ)

/-- **The stable root** `λ`: the smaller root of `(1+κ)λ² − Bλ + m`. -/
noncomputable def fd_lam (α β δ ψ γ : ℝ) : ℝ :=
  (fd_B α β δ ψ γ - Real.sqrt (fd_B α β δ ψ γ ^ 2 - 4 * (1 + fd_kap α β δ ψ) * fd_m α β δ ψ)) /
    (2 * (1 + fd_kap α β δ ψ))

/-- The saddle-path slope `p = (m − λ)/n` of consumption in capital. -/
noncomputable def fd_p (α β δ ψ γ : ℝ) : ℝ :=
  (fd_m α β δ ψ - fd_lam α β δ ψ γ) / fd_n α β δ ψ γ

/-- `D(ρ) = m − λ(1+κ)ρ`. -/
noncomputable def fd_D (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_m α β δ ψ - fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) * ρ

/-- The saddle-path coefficient `q = −pg/D(ρ)` of consumption on the spending shock. -/
noncomputable def fd_q (α β δ ψ γ ρ : ℝ) : ℝ :=
  -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ

/-- `φ = nq + g`: the fall in next period's capital per unit of the shock. -/
noncomputable def fd_phi (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_n α β δ ψ γ * fd_q α β δ ψ γ ρ + fd_g α β δ γ

/-- The impulse response of capital, `k̂₀ = 0`, `k̂ₜ₊₁ = λk̂ₜ − φρᵗ`. -/
noncomputable def fd_k (α β δ ψ γ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t

/-- The impulse response of consumption, `ĉₜ = pk̂ₜ + qρᵗ`. -/
noncomputable def fd_c (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ :=
  fd_p α β δ ψ γ * fd_k α β δ ψ γ ρ t + fd_q α β δ ψ γ ρ * ρ ^ t

/-- The impulse response of hours, `ℓ̂ₜ = (αk̂ₜ − ĉₜ)/(ψ+α)`. -/
noncomputable def fd_l (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ :=
  (α * fd_k α β δ ψ γ ρ t - fd_c α β δ ψ γ ρ t) / (ψ + α)

/-- The impulse response of output, `ŷₜ = αk̂ₜ + (1−α)ℓ̂ₜ`. -/
noncomputable def fd_y (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ :=
  α * fd_k α β δ ψ γ ρ t + (1 - α) * fd_l α β δ ψ γ ρ t

/-- The impulse response of spending, `Ĝₜ = η̂ₜ + ĉₜ` with `η̂ₜ = ρᵗ`. -/
noncomputable def fd_G (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ := ρ ^ t + fd_c α β δ ψ γ ρ t

/-! ### Signs of the coefficients -/

/-- The coefficients: `r̄ > 0`, `ȳ/k̄ > δ`, `c̄/k̄ > 0`, `Ḡ/k̄ > 0`, `κ > 0`, `m > 1`,
`0 < Ḡ/k̄ < n`,
`(1+γ)c̄/k̄ = ȳ/k̄ − δ` and `βr̄ = 1 − β + βδ`. -/
theorem fd_coef {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fm_r β δ ∧ δ < fd_Y α β δ ∧ 0 < fd_C α β δ γ ∧ 0 < fd_g α β δ γ ∧
      0 < fd_kap α β δ ψ ∧ 1 < fd_m α β δ ψ ∧ fd_g α β δ γ < fd_n α β δ ψ γ ∧
      (1 + γ) * fd_C α β δ γ = fd_Y α β δ - δ ∧ β * fm_r β δ = 1 - β + β * δ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  have hr := fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩
  have hr0 : 0 < fm_r β δ := by nlinarith
  have hY : δ < fd_Y α β δ := by unfold fd_Y; rw [lt_div_iff₀ ha0]; linarith
  have hC : 0 < fd_C α β δ γ := by unfold fd_C; apply div_pos <;> linarith
  have hg : 0 < fd_g α β δ γ := by unfold fd_g; positivity
  have hpa : 0 < ψ + α := by linarith
  have hbr : β * fm_r β δ = 1 - β + β * δ := by unfold fm_r; field_simp
  refine ⟨hr0, hY, hC, hg, ?_, ?_, ?_, ?_, hbr⟩
  · unfold fd_kap; apply div_pos _ hpa; have : 0 < 1 - α := by linarith
    positivity
  · unfold fd_m
    have h1 : fm_r β δ < fm_r β δ * (1 + ψ) / (ψ + α) := by
      rw [lt_div_iff₀ hpa]; nlinarith
    have h2 : 1 < 1 - δ + fm_r β δ := by
      unfold fm_r; have : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
      linarith
    linarith
  · unfold fd_n fd_g
    have : 0 < fd_Y α β δ * (1 - α) / (ψ + α) := by
      apply div_pos _ hpa; have : 0 < 1 - α := by linarith
      have : 0 < fd_Y α β δ := by linarith
      positivity
    nlinarith
  · unfold fd_C; field_simp

/-- The coefficients are the steady-state ratios (AKMM, Appendix 8.A.1, p. 842): at a steady
state, `ȳ/k̄ = fd_Y`, `c̄/k̄ = fd_C` and `Ḡ/k̄ = fd_g`. -/
theorem fd_ratios {α β δ ψ γ k c y ℓ G r w : ℝ} (hp : fm_Params α β δ ψ γ)
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    y / k = fd_Y α β δ ∧ c / k = fd_C α β δ γ ∧ G / k = fd_g α β δ γ := by
  obtain ⟨hr, -, -, -, -, -, hG⟩ := appendix_8A_1 hp hs
  obtain ⟨hyk, -, -, -⟩ := appendix_8A_1_ratios hp hs
  obtain ⟨hk, -, -, -, -, hR, -⟩ := hs
  have hγ := hp.2.2.2.2.2.2
  have hyk' : y / k = fd_Y α β δ := by rw [hyk, hr]; rfl
  have hck : c / k = fd_C α β δ γ := by
    unfold fd_C
    rw [← hyk', eq_div_iff (by linarith)]
    rw [hR, hG]
    field_simp
    ring
  refine ⟨hyk', hck, ?_⟩
  unfold fd_g
  rw [← hck, hG]
  ring

/-- **The stable root** (AKMM, §8.6.1, p. 231, "a linear approximation around the deterministic
steady state"): `0 < λ`, `(1+κ)λ < 1` and `(m − λ)(1 − (1+κ)λ) = nκψλ`. -/
theorem fd_lam_props {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fd_lam α β δ ψ γ ∧ (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ < 1 ∧
      (fd_m α β δ ψ - fd_lam α β δ ψ γ) * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) =
        fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * fd_lam α β δ ψ γ := by
  obtain ⟨-, -, -, -, hκ, hm, hgn, -, -⟩ := fd_coef hp
  have hg := (fd_coef hp).2.2.2.1
  have hψ : 0 < ψ := hp.2.2.2.2.2.1
  set κ := fd_kap α β δ ψ
  set m := fd_m α β δ ψ
  set n := fd_n α β δ ψ γ
  set B := fd_B α β δ ψ γ with hB
  have hBd : B = (1 + κ) * m + 1 + n * (κ * ψ) := rfl
  have hn : 0 < n := by linarith
  have hw : 0 < n * (κ * ψ) := by positivity
  have ha : 0 < 1 + κ := by linarith
  have ham : 1 < (1 + κ) * m := by nlinarith
  have hdisc : 0 ≤ B ^ 2 - 4 * (1 + κ) * m := by
    rw [hBd]; nlinarith [sq_nonneg ((1 + κ) * m - 1)]
  set s := Real.sqrt (B ^ 2 - 4 * (1 + κ) * m) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = B ^ 2 - 4 * (1 + κ) * m := Real.sq_sqrt hdisc
  have hlam : fd_lam α β δ ψ γ = (B - s) / (2 * (1 + κ)) := rfl
  have hBpos : 0 < B := by nlinarith
  have hsB : s < B := by nlinarith
  have hB2 : 2 < B := by rw [hBd]; linarith
  have hsB2 : B - 2 < s := by nlinarith
  rw [hlam]
  refine ⟨div_pos (by linarith) (by positivity), ?_, ?_⟩
  · rw [mul_div_assoc', div_lt_one (by positivity)]; nlinarith
  · field_simp
    nlinarith

/-- The relations among the coefficients used below: `(ψ+α)(m − 1 + δ) = (ȳ/k̄)α(1+ψ)`,
`(ψ+α)n = (ȳ/k̄)(1−α) + (ψ+α)(1+γ)c̄/k̄`, `κ(ψ+α) = βr̄(1−α)`, `(ȳ/k̄)α = r̄`, and for `ρ ≤ 1`:
`pn = m − λ`, `p(1 − (1+κ)λ) = λκψ`, `D > 0`, `qD = −pg`, `φD = gλ(1 − (1+κ)ρ)`, `p > 0`. -/
theorem fd_rel {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ ≤ 1) :
    (ψ + α) * (fd_m α β δ ψ - 1 + δ) = fd_Y α β δ * α * (1 + ψ) ∧
      (ψ + α) * fd_n α β δ ψ γ = fd_Y α β δ * (1 - α) + (ψ + α) * ((1 + γ) * fd_C α β δ γ) ∧
      fd_kap α β δ ψ * (ψ + α) = β * fm_r β δ * (1 - α) ∧ fd_Y α β δ * α = fm_r β δ ∧
      fd_p α β δ ψ γ * fd_n α β δ ψ γ = fd_m α β δ ψ - fd_lam α β δ ψ γ ∧
      fd_p α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) =
        fd_lam α β δ ψ γ * (fd_kap α β δ ψ * ψ) ∧
      0 < fd_D α β δ ψ γ ρ ∧
      fd_q α β δ ψ γ ρ * fd_D α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) ∧
      fd_phi α β δ ψ γ ρ * fd_D α β δ ψ γ ρ =
        fd_g α β δ γ * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ) ∧
      0 < fd_p α β δ ψ γ := by
  obtain ⟨hr0, hY, hC, hg, hκ, hm, hgn, hCY, hbr⟩ := fd_coef hp
  obtain ⟨hl0, hl1, hchar⟩ := fd_lam_props hp
  have ha0 : 0 < α := hp.1
  have hψ : 0 < ψ := hp.2.2.2.2.2.1
  have hpa : 0 < ψ + α := by linarith
  have hn : 0 < fd_n α β δ ψ γ := by linarith
  have hpn : fd_p α β δ ψ γ * fd_n α β δ ψ γ = fd_m α β δ ψ - fd_lam α β δ ψ γ := by
    unfold fd_p; field_simp
  have hD : 0 < fd_D α β δ ψ γ ρ := by
    unfold fd_D
    have hprod : 0 < fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) := by positivity
    have : fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) * ρ ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hρ hprod.le]
    linarith
  have hlm : fd_lam α β δ ψ γ < fd_m α β δ ψ := by nlinarith
  have hp0 : 0 < fd_p α β δ ψ γ := by unfold fd_p; exact div_pos (by linarith) hn
  have hq : fd_q α β δ ψ γ ρ * fd_D α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) := by
    unfold fd_q; field_simp
  refine ⟨?_, ?_, ?_, ?_, hpn, ?_, hD, hq, ?_, hp0⟩
  · unfold fd_m fd_Y; field_simp; ring
  · unfold fd_n; field_simp
  · unfold fd_kap; field_simp
  · unfold fd_Y; field_simp
  · have h2 : fd_p α β δ ψ γ * fd_n α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) =
        fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * fd_lam α β δ ψ γ := by rw [hpn]; exact hchar
    have : fd_n α β δ ψ γ * (fd_p α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) -
        fd_lam α β δ ψ γ * (fd_kap α β δ ψ * ψ)) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  · unfold fd_phi
    unfold fd_D at hq ⊢
    linear_combination fd_n α β δ ψ γ * hq - fd_g α β δ γ * hpn

/-- **The linearised equilibrium** (AKMM, (8.10)–(8.18) linearised around the steady state,
§8.6.1, p. 231), as the impulse response to a fiscal shock `η̂ₜ = ρᵗ` (AKMM, p. 236), in log
deviations `k̂, ĉ, ŷ, ℓ̂, Ĝ` with `k̂₀ = 0`: production (8.10) `ŷ = αk̂ + (1−α)ℓ̂`; the labour
condition (8.15) with (8.17), `ŷ = ĉ + (1+ψ)ℓ̂`; the spending rule (8.18), `Ĝ = η̂ + ĉ`; the
resource constraint (8.11) divided by `k̄`, `(ȳ/k̄)ŷ = (c̄/k̄)ĉ + k̂ₜ₊₁ − (1−δ)k̂ₜ + (Ḡ/k̄)Ĝ`; and
the Euler equation (8.14) with (8.16), `ĉₜ₊₁ − ĉₜ = βr̄(ŷₜ₊₁ − k̂ₜ₊₁)` (perfect foresight after
the shock, as in an impulse response). -/
def fd_IsIRF (α β δ ψ γ ρ : ℝ) (k c y l G : ℕ → ℝ) : Prop :=
  k 0 = 0 ∧ ∀ t, y t = α * k t + (1 - α) * l t ∧ y t = c t + (1 + ψ) * l t ∧
    G t = ρ ^ t + c t ∧
    fd_Y α β δ * y t = fd_C α β δ γ * c t + (k (t + 1) - (1 - δ) * k t) + fd_g α β δ γ * G t ∧
    c (t + 1) - c t = β * fm_r β δ * (y (t + 1) - k (t + 1))

/-- **The saddle-path impulse response solves the linearised model** (AKMM, §8.6.1, p. 231 and
Figure 8.4, p. 236): for `ρ ≤ 1`, the paths `k̂ₜ₊₁ = λk̂ₜ − φρᵗ`, `ĉₜ = pk̂ₜ + qρᵗ`,
`ℓ̂ₜ = (αk̂ₜ − ĉₜ)/(ψ+α)`, `ŷₜ = αk̂ₜ + (1−α)ℓ̂ₜ`, `Ĝₜ = ρᵗ + ĉₜ` satisfy `fd_IsIRF`. -/
theorem fd_irf_solves {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ ≤ 1) :
    fd_IsIRF α β δ ψ γ ρ (fd_k α β δ ψ γ ρ) (fd_c α β δ ψ γ ρ) (fd_y α β δ ψ γ ρ)
      (fd_l α β δ ψ γ ρ) (fd_G α β δ ψ γ ρ) := by
  obtain ⟨R1, R2, R4, R9, R5, R6, hD, R7, R8, -⟩ := fd_rel hp hρ
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  obtain ⟨hl0, -, -⟩ := fd_lam_props hp
  refine ⟨rfl, fun t => ⟨rfl, ?_, rfl, ?_, ?_⟩⟩
  · unfold fd_y fd_l; field_simp; ring
  · have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    have hy : (ψ + α) * fd_y α β δ ψ γ ρ t =
        α * (1 + ψ) * fd_k α β δ ψ γ ρ t - (1 - α) * fd_c α β δ ψ γ ρ t := by
      unfold fd_y fd_l; field_simp; ring
    have R3 : fd_g α β δ γ = γ * fd_C α β δ γ := rfl
    apply mul_left_cancel₀ hpa.ne'
    unfold fd_G
    rw [hk1]
    unfold fd_c at hy ⊢
    unfold fd_phi
    linear_combination fd_Y α β δ * hy - fd_k α β δ ψ γ ρ t * R1 +
      (fd_p α β δ ψ γ * fd_k α β δ ψ γ ρ t + fd_q α β δ ψ γ ρ * ρ ^ t) * R2 -
      (ψ + α) * fd_k α β δ ψ γ ρ t * R5 -
      (ψ + α) * (fd_p α β δ ψ γ * fd_k α β δ ψ γ ρ t + fd_q α β δ ψ γ ρ * ρ ^ t) * R3
  · have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    have hy : (ψ + α) * fd_y α β δ ψ γ ρ (t + 1) =
        α * (1 + ψ) * fd_k α β δ ψ γ ρ (t + 1) - (1 - α) * fd_c α β δ ψ γ ρ (t + 1) := by
      unfold fd_y fd_l; field_simp; ring
    have hpq : fd_p α β δ ψ γ * fd_phi α β δ ψ γ ρ =
        -(fd_q α β δ ψ γ ρ * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ)) :=
      mul_right_cancel₀ hD.ne' (by
        linear_combination fd_p α β δ ψ γ * R8 +
          fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ) * R7)
    have hE : fd_lam α β δ ψ γ * ((1 + fd_kap α β δ ψ) * fd_c α β δ ψ γ ρ (t + 1) -
        fd_c α β δ ψ γ ρ t + fd_kap α β δ ψ * ψ * fd_k α β δ ψ γ ρ (t + 1)) = 0 := by
      unfold fd_c
      rw [hk1]
      linear_combination (-(fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t -
        fd_phi α β δ ψ γ ρ * ρ ^ t)) * R6 - ρ ^ t * hpq
    have hE0 := (mul_eq_zero.1 hE).resolve_left hl0.ne'
    apply mul_left_cancel₀ hpa.ne'
    linear_combination (ψ + α) * hE0 - β * fm_r β δ * hy -
      (ψ * fd_k α β δ ψ γ ρ (t + 1) + fd_c α β δ ψ γ ρ (t + 1)) * R4

/-- The stable root is below one: `λ < 1`. -/
theorem fd_lam_lt_one {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) : fd_lam α β δ ψ γ < 1 := by
  obtain ⟨hl0, hl1, -⟩ := fd_lam_props hp
  have hκ := (fd_coef hp).2.2.2.2.1
  nlinarith

/-- **The impulse response is bounded** for `0 ≤ ρ ≤ 1`: `|k̂ₜ| ≤ |φ|/(1 − λ)`. -/
theorem fd_k_bound {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1)
    (t : ℕ) : |fd_k α β δ ψ γ ρ t| ≤ |fd_phi α β δ ψ γ ρ| / (1 - fd_lam α β δ ψ γ) := by
  have hl0 := (fd_lam_props hp).1
  have hl1 := fd_lam_lt_one hp
  have h1 : 0 < 1 - fd_lam α β δ ψ γ := by linarith
  induction t with
  | zero => simp only [fd_k, abs_zero]; positivity
  | succ t ih =>
    have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    have hpow : |ρ ^ t| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hρ0 t)]; exact pow_le_one₀ hρ0 hρ
    rw [hk1]
    calc |fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t|
        ≤ fd_lam α β δ ψ γ * |fd_k α β δ ψ γ ρ t| + |fd_phi α β δ ψ γ ρ| := by
          have := abs_sub (fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t)
            (fd_phi α β δ ψ γ ρ * ρ ^ t)
          rw [abs_mul, abs_mul, abs_of_pos hl0] at this
          nlinarith [abs_nonneg (fd_phi α β δ ψ γ ρ)]
      _ ≤ fd_lam α β δ ψ γ * (|fd_phi α β δ ψ γ ρ| / (1 - fd_lam α β δ ψ γ)) +
          |fd_phi α β δ ψ γ ρ| := by gcongr
      _ = |fd_phi α β δ ψ γ ρ| / (1 - fd_lam α β δ ψ γ) := by field_simp; ring

/-- **The saddle path is the unique bounded solution** (AKMM, §8.6.1, p. 231): for `0 ≤ ρ ≤ 1`,
every solution of the linearised model with `k̂` and `ĉ` bounded is the saddle-path impulse
response. The deviation `zₜ = ĉₜ − pk̂ₜ − qρᵗ` from the saddle path satisfies
`zₜ₊₁ = (m/((1+κ)λ))zₜ` with `m/((1+κ)λ) > 1`, so it is bounded only if it is zero. -/
theorem fd_irf_unique {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1)
    {k c y l G : ℕ → ℝ} (hirf : fd_IsIRF α β δ ψ γ ρ k c y l G)
    (hbdd : ∃ M, ∀ t, |k t| ≤ M ∧ |c t| ≤ M) :
    k = fd_k α β δ ψ γ ρ ∧ c = fd_c α β δ ψ γ ρ ∧ l = fd_l α β δ ψ γ ρ ∧
      y = fd_y α β δ ψ γ ρ ∧ G = fd_G α β δ ψ γ ρ := by
  obtain ⟨R1, R2, R4, -, R5, R6, hD, R7, R8, hp0⟩ := fd_rel hp hρ
  have R3 : fd_g α β δ γ = γ * fd_C α β δ γ := rfl
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  obtain ⟨hl0, hl1, -⟩ := fd_lam_props hp
  have hm := (fd_coef hp).2.2.2.2.2.1
  obtain ⟨hk0, hall⟩ := hirf
  unfold fd_D at R7 hD
  set lam := fd_lam α β δ ψ γ
  set a := 1 + fd_kap α β δ ψ
  set m := fd_m α β δ ψ
  set n := fd_n α β δ ψ γ
  set p := fd_p α β δ ψ γ
  set q := fd_q α β δ ψ γ ρ
  set g := fd_g α β δ γ
  set κ := fd_kap α β δ ψ
  -- the reduced system
  have hyl : ∀ t, (ψ + α) * y t = α * (1 + ψ) * k t - (1 - α) * c t := fun t => by
    obtain ⟨h1, h2, -⟩ := hall t
    linear_combination (1 + ψ) * h1 - (1 - α) * h2
  have hk : ∀ t, k (t + 1) = m * k t - n * c t - g * ρ ^ t := fun t => by
    obtain ⟨-, -, h3, h4, -⟩ := hall t
    apply mul_left_cancel₀ hpa.ne'
    rw [h3] at h4
    linear_combination -(ψ + α) * h4 + fd_Y α β δ * hyl t - k t * R1 + c t * R2 -
      (ψ + α) * c t * R3
  have hc : ∀ t, a * c (t + 1) = c t - κ * ψ * k (t + 1) := fun t => by
    obtain ⟨-, -, -, -, h5⟩ := hall t
    apply mul_left_cancel₀ hpa.ne'
    linear_combination (ψ + α) * h5 + β * fm_r β δ * hyl (t + 1) +
      (ψ * k (t + 1) + c (t + 1)) * R4
  -- the deviation from the saddle path
  set z : ℕ → ℝ := fun t => c t - p * k t - q * ρ ^ t with hzdef
  have hz : ∀ t, a * lam * z (t + 1) = m * z t := fun t => by
    simp only [hzdef]
    linear_combination lam * hc t + k (t + 1) * R6 - p * hk t + c t * R5 + ρ ^ t * R7
  have hκ := (fd_coef hp).2.2.2.2.1
  have hal : 0 < a * lam := by positivity
  set μ := m / (a * lam) with hμ
  have hμ1 : 1 < μ := by rw [hμ, lt_div_iff₀ hal]; linarith
  have hzt : ∀ t, z t = μ ^ t * z 0 := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      have : z (t + 1) = μ * z t := by
        rw [hμ, div_mul_eq_mul_div, eq_div_iff hal.ne']; linear_combination hz t
      rw [this, ih]; ring
  obtain ⟨M, hM⟩ := hbdd
  have hzb : ∀ t, |z t| ≤ M + p * M + |q| := fun t => by
    obtain ⟨h1, h2⟩ := hM t
    have hpow : |ρ ^ t| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hρ0 t)]; exact pow_le_one₀ hρ0 hρ
    have e1 : |z t| ≤ |c t| + |p * k t| + |q * ρ ^ t| := by
      simp only [hzdef]
      linarith [abs_sub (c t - p * k t) (q * ρ ^ t), abs_sub (c t) (p * k t)]
    rw [abs_mul, abs_mul, abs_of_pos hp0] at e1
    nlinarith [abs_nonneg q, abs_nonneg (k t), abs_nonneg (ρ ^ t)]
  have hz0 : z 0 = 0 := by
    by_contra hne
    have hpos : 0 < |z 0| := abs_pos.2 hne
    obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hμ1).eventually_gt_atTop
      ((M + p * M + |q|) / |z 0|)).exists
    have := hzb t
    rw [hzt t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
    rw [div_lt_iff₀ hpos] at ht
    linarith
  have hcz : ∀ t, c t = p * k t + q * ρ ^ t := fun t => by
    have := hzt t
    rw [hz0, mul_zero] at this
    simp only [hzdef] at this
    linarith
  have hkk : k = fd_k α β δ ψ γ ρ := by
    funext t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
          lam * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
      rw [hk1, ← ih, hk t, hcz t]
      unfold fd_phi
      linear_combination (-k t) * R5
  have hcc : c = fd_c α β δ ψ γ ρ := by
    funext t; rw [hcz t, hkk]; rfl
  have hll : l = fd_l α β δ ψ γ ρ := by
    funext t
    obtain ⟨h1, h2, -⟩ := hall t
    unfold fd_l
    rw [← hkk, ← hcc, eq_div_iff hpa.ne']
    linear_combination h1 - h2
  refine ⟨hkk, hcc, hll, ?_, ?_⟩
  · funext t
    rw [(hall t).1, hkk, hll]; rfl
  · funext t
    rw [(hall t).2.2.1, hcc]; rfl

/-! ### The signs of the impulse responses -/

/-- For `0 ≤ ρ` and `(1+κ)ρ ≤ 1`: `q < 0`, `φ ≥ 0`, and `D − pg ≥ p(n − g) > 0`. -/
theorem fd_q_phi {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) :
    fd_q α β δ ψ γ ρ < 0 ∧ 0 ≤ fd_phi α β δ ψ γ ρ ∧
      fd_p α β δ ψ γ * (fd_n α β δ ψ γ - fd_g α β δ γ) ≤
        fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ ∧
      0 < fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ := by
  have hκ := (fd_coef hp).2.2.2.2.1
  have hρ1 : ρ ≤ 1 := by nlinarith
  obtain ⟨-, -, -, -, R5, -, hD, R7, R8, hp0⟩ := fd_rel hp hρ1
  obtain ⟨-, -, -, hg, -, -, hgn, -, -⟩ := fd_coef hp
  have hl0 := (fd_lam_props hp).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    nlinarith [mul_pos hp0 hg]
  · by_contra h
    rw [not_le] at h
    have h1 : 0 ≤ 1 - (1 + fd_kap α β δ ψ) * ρ := by linarith
    nlinarith [mul_nonneg hg.le (mul_nonneg hl0.le h1)]
  · unfold fd_D
    nlinarith [mul_le_mul_of_nonneg_left hρ hl0.le]
  · unfold fd_D
    nlinarith [mul_le_mul_of_nonneg_left hρ hl0.le, mul_pos hp0 (sub_pos.2 hgn)]

/-- Capital never rises above its steady state: for `0 ≤ ρ`, `(1+κ)ρ ≤ 1`, `k̂ₜ ≤ 0`. -/
theorem fd_k_nonpos {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) (t : ℕ) : fd_k α β δ ψ γ ρ t ≤ 0 := by
  have hl0 := (fd_lam_props hp).1
  have hφ := (fd_q_phi hp hρ0 hρ).2.1
  induction t with
  | zero => exact le_refl _
  | succ t ih =>
    have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    rw [hk1]
    nlinarith [mul_nonneg hφ (pow_nonneg hρ0 t)]

/-- **Consumption falls and stays below steady state, and capital is run down** (AKMM, p. 236,
"consumes less, and invests less"; p. 238, "a persistent decrease in consumption"): for
`0 ≤ ρ` and `(1+κ)ρ < 1`, `ĉₜ < 0` for all `t` and `k̂ₜ₊₁ < 0` for all `t`. -/
theorem fd_c_k_neg {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ < 1) (t : ℕ) :
    fd_c α β δ ψ γ ρ t < 0 ∧ fd_k α β δ ψ γ ρ (t + 1) < 0 := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, hD, -, R8, hp0⟩ := fd_rel hp hρ1
  obtain ⟨hq, hφ0, -, -⟩ := fd_q_phi hp hρ0 hρ.le
  have hl0 := (fd_lam_props hp).1
  have hg := (fd_coef hp).2.2.2.1
  have hφ : 0 < fd_phi α β δ ψ γ ρ := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_pos hg (mul_pos hl0 (by linarith : 0 < 1 - (1 + fd_kap α β δ ψ) * ρ))]
  have hk : ∀ t, fd_k α β δ ψ γ ρ (t + 1) < 0 := fun t => by
    induction t with
    | zero =>
      change fd_lam α β δ ψ γ * 0 - fd_phi α β δ ψ γ ρ * ρ ^ 0 < 0
      simp only [mul_zero, pow_zero, mul_one, zero_sub, neg_neg_iff_pos]; exact hφ
    | succ t ih =>
      have hk1 : fd_k α β δ ψ γ ρ (t + 1 + 1) = fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ (t + 1) -
          fd_phi α β δ ψ γ ρ * ρ ^ (t + 1) := rfl
      rw [hk1]
      nlinarith [mul_nonneg hφ0 (pow_nonneg hρ0 (t + 1))]
  refine ⟨?_, hk t⟩
  unfold fd_c
  cases t with
  | zero => simp only [fd_k, mul_zero, pow_zero, mul_one, zero_add]; exact hq
  | succ t =>
    nlinarith [mul_pos hp0 (neg_pos.2 (hk t)), mul_nonpos_of_nonpos_of_nonneg hq.le
      (pow_nonneg hρ0 (t + 1))]

/-- **The impact responses** (AKMM, Figure 8.4, left, p. 236: "the economy works more, consumes
less, and invests less … the increase in labor supply raises output"): for `0 ≤ ρ` and
`(1+κ)ρ < 1`, on impact `ĉ₀ < 0`, `ℓ̂₀ > 0`, `ŷ₀ > 0`, `0 < Ĝ₀ < 1`, and investment
`Î₀ = k̂₁ − (1−δ)k̂₀ = k̂₁ < 0`. -/
theorem fd_impact_signs {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ < 1) :
    fd_c α β δ ψ γ ρ 0 < 0 ∧ 0 < fd_l α β δ ψ γ ρ 0 ∧ 0 < fd_y α β δ ψ γ ρ 0 ∧
      0 < fd_G α β δ ψ γ ρ 0 ∧ fd_G α β δ ψ γ ρ 0 < 1 ∧
      fd_k α β δ ψ γ ρ 1 - (1 - δ) * fd_k α β δ ψ γ ρ 0 < 0 := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, hD, R7, -, hp0⟩ := fd_rel hp hρ1
  obtain ⟨hq, -, -, hDp⟩ := fd_q_phi hp hρ0 hρ.le
  obtain ⟨hc0, hk1⟩ := fd_c_k_neg hp hρ0 hρ 0
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hc0' : fd_c α β δ ψ γ ρ 0 = fd_q α β δ ψ γ ρ := by
    simp only [fd_c, fd_k, mul_zero, pow_zero, mul_one, zero_add]
  have hl : 0 < fd_l α β δ ψ γ ρ 0 := by
    unfold fd_l; rw [hc0']; simp only [fd_k, mul_zero, zero_sub]
    exact div_pos (by linarith) hpa
  refine ⟨hc0, hl, ?_, ?_, ?_, ?_⟩
  · unfold fd_y; simp only [fd_k, mul_zero, zero_add]; positivity
  · unfold fd_G; rw [hc0', pow_zero]
    have hg := (fd_coef hp).2.2.2.1
    by_contra h
    rw [not_lt] at h
    nlinarith
  · unfold fd_G; rw [hc0', pow_zero]; linarith
  · simp only [fd_k, mul_zero, sub_zero] at hk1 ⊢; linarith

/-- **Correction: investment rises when the shock is persistent enough** (AKMM, p. 236, "invests
less"). The impact response of investment is `Î₀ = k̂₁ = −φ` with
`φD = gλ(1 − (1+κ)ρ)`: investment falls iff `(1+κ)ρ < 1`, is unchanged at `(1+κ)ρ = 1`, and
rises for `1/(1+κ) < ρ ≤ 1`. Since `κ > 0`, that interval is non-empty: it contains the
permanent shock `ρ = 1`. -/
theorem fd_investment_correction {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ1 : ρ ≤ 1) :
    (fd_k α β δ ψ γ ρ 1 < 0 ↔ (1 + fd_kap α β δ ψ) * ρ < 1) ∧
      (fd_k α β δ ψ γ ρ 1 = 0 ↔ (1 + fd_kap α β δ ψ) * ρ = 1) ∧
      (0 < fd_k α β δ ψ γ ρ 1 ↔ 1 < (1 + fd_kap α β δ ψ) * ρ) ∧
      1 < (1 + fd_kap α β δ ψ) * 1 := by
  obtain ⟨-, -, -, -, -, -, hD, -, R8, -⟩ := fd_rel hp hρ1
  have hl0 := (fd_lam_props hp).1
  have hg := (fd_coef hp).2.2.2.1
  have hκ := (fd_coef hp).2.2.2.2.1
  have hk1 : fd_k α β δ ψ γ ρ 1 = -fd_phi α β δ ψ γ ρ := by
    simp only [fd_k, mul_zero, pow_zero, mul_one, zero_sub]
  have hgl : 0 < fd_g α β δ γ * fd_lam α β δ ψ γ := mul_pos hg hl0
  have hφ : fd_phi α β δ ψ γ ρ = fd_g α β δ γ * fd_lam α β δ ψ γ *
      (1 - (1 + fd_kap α β δ ψ) * ρ) / fd_D α β δ ψ γ ρ := by
    rw [eq_div_iff hD.ne']; exact R8
  rw [hk1, hφ]
  refine ⟨?_, ?_, ?_, by linarith⟩
  · rw [neg_lt_zero, div_pos_iff_of_pos_right hD]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [neg_eq_zero, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · linarith
      · linarith
    · intro h; left; rw [h, sub_self, mul_zero]
  · rw [neg_pos, div_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · nlinarith
    · intro h; right; exact ⟨by nlinarith, hD⟩

/-! ### Fiscal multipliers -/

/-- **The cumulative fiscal multiplier over `H` periods** (AKMM, p. 236, "integrating the output
and spending responses over the first 12 quarters"): `Σₜ<H Δyₜ / Σₜ<H ΔGₜ`, with the level
responses per unit of capital `Δyₜ/k̄ = (ȳ/k̄)ŷₜ` and `ΔGₜ/k̄ = (Ḡ/k̄)Ĝₜ`. The figure plots
`H = 12`;
`H = 1` is the impact multiplier. -/
noncomputable def fd_mult (α β δ ψ γ ρ : ℝ) (H : ℕ) : ℝ :=
  (∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t) /
    ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t

/-- **Output rises by less than spending, over every horizon** (AKMM, §8.6.2, p. 231, and
p. 236): for `0 ≤ ρ`, `(1+κ)ρ ≤ 1` and `H ≥ 1`, `Σₜ<H Δyₜ < Σₜ<H ΔGₜ`. By the resource constraint
the gap is `Σₜ<H Δcₜ + Σₜ<H ΔIₜ`; consumption is below steady state and the cumulative investment
response is `k̄(k̂_H + δΣₜ<H k̂ₜ) ≤ 0`. -/
theorem fd_cum_lt {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) {H : ℕ} (hH : 1 ≤ H) :
    ∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t <
      ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, hall⟩ := fd_irf_solves hp hρ1
  obtain ⟨hq, -, -, -⟩ := fd_q_phi hp hρ0 hρ
  have hp0 := (fd_rel hp hρ1).2.2.2.2.2.2.2.2.2
  have hC := (fd_coef hp).2.2.1
  have hd := hp.2.2.2.2.1
  have hc : ∀ t, fd_c α β δ ψ γ ρ t ≤ 0 := fun t => by
    unfold fd_c
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp0.le (fd_k_nonpos hp hρ0 hρ t),
      mul_nonpos_of_nonpos_of_nonneg hq.le (pow_nonneg hρ0 t)]
  have hc0 : fd_c α β δ ψ γ ρ 0 < 0 := by
    simp only [fd_c, fd_k, mul_zero, pow_zero, mul_one, zero_add]; exact hq
  have hdiff : ∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t -
      ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t =
      fd_C α β δ γ * ∑ t ∈ range H, fd_c α β δ ψ γ ρ t +
        (fd_k α β δ ψ γ ρ H + δ * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t) := by
    have hk := Finset.sum_range_sub (fd_k α β δ ψ γ ρ) H
    have h0 : fd_k α β δ ψ γ ρ 0 = 0 := rfl
    rw [h0, sub_zero] at hk
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← hk, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hall t).2.2.2.1]
    ring
  have hsc : ∑ t ∈ range H, fd_c α β δ ψ γ ρ t < 0 := by
    obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have := Finset.sum_nonpos fun t (_ : t ∈ range H') => hc (t + 1)
    linarith
  have hsk : ∑ t ∈ range H, fd_k α β δ ψ γ ρ t ≤ 0 :=
    Finset.sum_nonpos fun t _ => fd_k_nonpos hp hρ0 hρ t
  have := fd_k_nonpos hp hρ0 hρ H
  nlinarith [mul_neg_of_pos_of_neg hC hsc, mul_nonpos_of_nonneg_of_nonpos hd hsk]

/-- **The cumulative multiplier is below one** whenever cumulative spending rises. -/
theorem fd_mult_lt_one {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) {H : ℕ} (hH : 1 ≤ H)
    (hG : 0 < ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t) :
    fd_mult α β δ ψ γ ρ H < 1 := by
  unfold fd_mult
  rw [div_lt_one hG]
  exact fd_cum_lt hp hρ0 hρ hH

/-- **The impact multiplier** (AKMM, Figure 8.4, p. 236): for `ρ ≤ 1`,
`Δy₀/ΔG₀ = (ȳ/k̄)(1−α)p/((ψ+α)(D(ρ) − pg))`, with `D(ρ) = m − λ(1+κ)ρ`. -/
theorem fd_impact_mult {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ ≤ 1) :
    fd_mult α β δ ψ γ ρ 1 = fd_Y α β δ * (1 - α) * fd_p α β δ ψ γ /
      ((ψ + α) * (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ)) := by
  obtain ⟨-, -, -, -, -, -, hD, R7, -, -⟩ := fd_rel hp hρ
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have hg := (fd_coef hp).2.2.2.1
  have hq : fd_q α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := rfl
  unfold fd_mult fd_y fd_l fd_G fd_c
  simp only [Finset.sum_range_one, fd_k, mul_zero, zero_add, pow_zero, mul_one, zero_sub]
  rw [hq]
  rcases eq_or_ne (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) 0 with h | h
  · have h' : fd_D α β δ ψ γ ρ = fd_p α β δ ψ γ * fd_g α β δ γ := by linarith
    rw [h, mul_zero, div_zero, h']
    have : 1 + -(fd_p α β δ ψ γ * fd_g α β δ γ) / (fd_p α β δ ψ γ * fd_g α β δ γ) = 0 := by
      rw [← h']; field_simp; ring
    rw [this, mul_zero, div_zero]
  · have e : 1 + -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ =
        (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := by
      field_simp; ring
    rw [e, div_eq_div_iff (by positivity) (mul_ne_zero hpa.ne' h)]
    field_simp

/-- **The impact multiplier is between zero and one** (AKMM, §8.6.2, p. 231): for `0 ≤ ρ` and
`(1+κ)ρ ≤ 1`, `0 < Δy₀/ΔG₀ < 1`. -/
theorem fd_impact_mult_mem {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) :
    0 < fd_mult α β δ ψ γ ρ 1 ∧ fd_mult α β δ ψ γ ρ 1 < 1 := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  have hp0 := (fd_rel hp hρ1).2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hDp⟩ := fd_q_phi hp hρ0 hρ
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hY : 0 < fd_Y α β δ := by linarith [(fd_coef hp).2.1, hp.2.2.2.2.1]
  have hpos : 0 < fd_mult α β δ ψ γ ρ 1 := by rw [fd_impact_mult hp hρ1]; positivity
  refine ⟨hpos, ?_⟩
  have hG : 0 < ∑ t ∈ range 1, fd_g α β δ γ * fd_G α β δ ψ γ ρ t := by
    obtain ⟨-, -, -, -, -, -, hD, -, -, -⟩ := fd_rel hp hρ1
    have hg := (fd_coef hp).2.2.2.1
    have hq : fd_q α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := rfl
    simp only [Finset.sum_range_one, fd_G, fd_c, fd_k, mul_zero, zero_add, pow_zero, mul_one]
    have : 1 + fd_q α β δ ψ γ ρ =
        (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := by
      rw [hq]; field_simp; ring
    rw [this]
    positivity
  exact fd_mult_lt_one hp hρ0 hρ (le_refl 1) hG

/-- **The impact multiplier increases with the persistence of the shock** (AKMM, §8.6.2,
p. 231, "the fiscal multiplier is increasing in the persistence of the shock to spending";
Figure 8.4, right): `ρ ↦ Δy₀/ΔG₀` is strictly increasing on `0 ≤ ρ ≤ 1/(1+κ)`. -/
theorem fd_impact_mult_strictMonoOn_rho {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    StrictMonoOn (fun ρ => fd_mult α β δ ψ γ ρ 1) {ρ | 0 ≤ ρ ∧ (1 + fd_kap α β δ ψ) * ρ ≤ 1} := by
  intro ρ1 h1 ρ2 h2 h12
  have hκ := (fd_coef hp).2.2.2.2.1
  have hr1 : ρ1 ≤ 1 := by nlinarith [h1.1, h1.2]
  have hr2 : ρ2 ≤ 1 := by nlinarith [h2.1, h2.2]
  simp only
  rw [fd_impact_mult hp hr1, fd_impact_mult hp hr2]
  have hp0 := (fd_rel hp hr1).2.2.2.2.2.2.2.2.2
  have hD1 := (fd_q_phi hp h1.1 h1.2).2.2.2
  have hD2 := (fd_q_phi hp h2.1 h2.2).2.2.2
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hY : 0 < fd_Y α β δ := by linarith [(fd_coef hp).2.1, hp.2.2.2.2.1]
  have hl0 := (fd_lam_props hp).1
  have hDD : fd_D α β δ ψ γ ρ2 < fd_D α β δ ψ γ ρ1 := by
    unfold fd_D
    have : 0 < fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) := by positivity
    nlinarith
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  exact mul_lt_mul_of_pos_left (by linarith) hpa

/-! ### The cumulative multiplier over the whole horizon -/

/-- `Σₜ k̂ₜ = −φ/((1−λ)(1−ρ))`, the cumulative capital response over the whole horizon. -/
noncomputable def fd_KInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  -fd_phi α β δ ψ γ ρ / ((1 - fd_lam α β δ ψ γ) * (1 - ρ))

/-- `Σₜ ŷₜ = A₁Σₜk̂ₜ + A₂Σₜρᵗ` with `A₁ = (α(1+ψ) − (1−α)p)/(ψ+α)`, `A₂ = −(1−α)q/(ψ+α)`. -/
noncomputable def fd_yInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  (α * (1 + ψ) - (1 - α) * fd_p α β δ ψ γ) / (ψ + α) * fd_KInf α β δ ψ γ ρ -
    (1 - α) * fd_q α β δ ψ γ ρ / (ψ + α) * (1 / (1 - ρ))

/-- `Σₜ Ĝₜ = pΣₜk̂ₜ + (1+q)Σₜρᵗ`. -/
noncomputable def fd_GInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_p α β δ ψ γ * fd_KInf α β δ ψ γ ρ + (1 + fd_q α β δ ψ γ ρ) * (1 / (1 - ρ))

/-- **The cumulative multiplier over the whole horizon**, `Σₜ Δyₜ / Σₜ ΔGₜ`. -/
noncomputable def fd_multInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_Y α β δ * fd_yInf α β δ ψ γ ρ / (fd_g α β δ γ * fd_GInf α β δ ψ γ ρ)

/-- The capital response dies out: for `0 ≤ ρ < 1`, `k̂ₜ → 0`. -/
theorem fd_k_tendsto {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Tendsto (fd_k α β δ ψ γ ρ) atTop (𝓝 0) := by
  have hl0 := (fd_lam_props hp).1
  have hl1 := fd_lam_lt_one hp
  set lam := fd_lam α β δ ψ γ
  set φ := fd_phi α β δ ψ γ ρ
  set ν := (1 + max lam ρ) / 2 with hν
  have hmx : max lam ρ < 1 := max_lt hl1 hρ
  have hνl : lam < ν := by have := le_max_left lam ρ; rw [hν]; linarith
  have hνρ : ρ ≤ ν := by have := le_max_right lam ρ; rw [hν]; linarith
  have hν1 : ν < 1 := by rw [hν]; linarith
  have hν0 : 0 ≤ ν := by linarith
  have hνl' : 0 ≤ ν - lam := by linarith
  have hb : ∀ t : ℕ, |fd_k α β δ ψ γ ρ t| ≤ |φ| / (ν - lam) * ν ^ t := by
    intro t
    induction t with
    | zero => simp only [fd_k, abs_zero, pow_zero, mul_one]; exact div_nonneg (abs_nonneg _) hνl'
    | succ t ih =>
      have hk1 : fd_k α β δ ψ γ ρ (t + 1) = lam * fd_k α β δ ψ γ ρ t - φ * ρ ^ t := rfl
      rw [hk1]
      have h1 : |lam * fd_k α β δ ψ γ ρ t - φ * ρ ^ t| ≤
          lam * |fd_k α β δ ψ γ ρ t| + |φ| * ρ ^ t := by
        have := abs_sub (lam * fd_k α β δ ψ γ ρ t) (φ * ρ ^ t)
        rwa [abs_mul, abs_mul, abs_of_pos hl0, abs_of_nonneg (pow_nonneg hρ0 t)] at this
      have h2 : ρ ^ t ≤ ν ^ t := pow_le_pow_left₀ hρ0 hνρ t
      have h3 : lam * |fd_k α β δ ψ γ ρ t| ≤ lam * (|φ| / (ν - lam) * ν ^ t) :=
        mul_le_mul_of_nonneg_left ih hl0.le
      have h4 : |φ| * ρ ^ t ≤ |φ| * ν ^ t := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have h5 : lam * (|φ| / (ν - lam) * ν ^ t) + |φ| * ν ^ t = |φ| / (ν - lam) * ν ^ (t + 1) := by
        have : ν - lam ≠ 0 := by linarith
        field_simp; ring
      linarith
  have hlim : Tendsto (fun t => |φ| / (ν - lam) * ν ^ t) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hν0 hν1).const_mul (|φ| / (ν - lam))
    rwa [mul_zero] at this
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hb t) hlim

/-- `(1 − λ)Σₜ<H k̂ₜ = −φΣₜ<H ρᵗ − k̂_H`. -/
theorem fd_sum_k {α β δ ψ γ ρ : ℝ} (H : ℕ) :
    (1 - fd_lam α β δ ψ γ) * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t =
      -fd_phi α β δ ψ γ ρ * ∑ t ∈ range H, ρ ^ t - fd_k α β δ ψ γ ρ H := by
  induction H with
  | zero => simp [fd_k]
  | succ H ih =>
    have hk1 : fd_k α β δ ψ γ ρ (H + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ H - fd_phi α β δ ψ γ ρ * ρ ^ H := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hk1]
    linear_combination ih

/-- **The cumulative multiplier converges as the horizon grows** (AKMM, p. 236): for
`0 ≤ ρ < 1` and `Σₜ Ĝₜ ≠ 0`, `Σₜ<H Δyₜ / Σₜ<H ΔGₜ → fd_multInf` as `H → ∞`. -/
theorem fd_mult_tendsto {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hG : fd_GInf α β δ ψ γ ρ ≠ 0) :
    Tendsto (fun H => fd_mult α β δ ψ γ ρ H) atTop (𝓝 (fd_multInf α β δ ψ γ ρ)) := by
  have hl1 := fd_lam_lt_one hp
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have hg := (fd_coef hp).2.2.2.1
  have hR : Tendsto (fun H => ∑ t ∈ range H, ρ ^ t) atTop (𝓝 (1 / (1 - ρ))) := by
    have := (hasSum_geometric_of_lt_one hρ0 hρ).tendsto_sum_nat
    rwa [one_div]
  have hK : Tendsto (fun H => ∑ t ∈ range H, fd_k α β δ ψ γ ρ t) atTop
      (𝓝 (fd_KInf α β δ ψ γ ρ)) := by
    have h1 : 1 - fd_lam α β δ ψ γ ≠ 0 := by linarith
    have e : ∀ H, ∑ t ∈ range H, fd_k α β δ ψ γ ρ t =
        (-fd_phi α β δ ψ γ ρ * ∑ t ∈ range H, ρ ^ t - fd_k α β δ ψ γ ρ H) /
          (1 - fd_lam α β δ ψ γ) :=
      fun H => by rw [eq_div_iff h1, mul_comm, fd_sum_k]
    simp_rw [e]
    have hlim := ((hR.const_mul (-fd_phi α β δ ψ γ ρ)).sub
      (fd_k_tendsto hp hρ0 hρ)).div_const (1 - fd_lam α β δ ψ γ)
    have hv : (-fd_phi α β δ ψ γ ρ * (1 / (1 - ρ)) - 0) / (1 - fd_lam α β δ ψ γ) =
        fd_KInf α β δ ψ γ ρ := by
      unfold fd_KInf
      have : 1 - ρ ≠ 0 := by linarith
      field_simp
      ring
    rwa [hv] at hlim
  have hy : ∀ H, ∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t = fd_Y α β δ *
      ((α * (1 + ψ) - (1 - α) * fd_p α β δ ψ γ) / (ψ + α) * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t -
        (1 - α) * fd_q α β δ ψ γ ρ / (ψ + α) * ∑ t ∈ range H, ρ ^ t) := fun H => by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold fd_y fd_l fd_c
    field_simp
    ring
  have hGs : ∀ H, ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t = fd_g α β δ γ *
      (fd_p α β δ ψ γ * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t +
        (1 + fd_q α β δ ψ γ ρ) * ∑ t ∈ range H, ρ ^ t) := fun H => by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold fd_G fd_c
    ring
  unfold fd_mult fd_multInf fd_yInf fd_GInf
  simp_rw [hy, hGs]
  refine Tendsto.div (tendsto_const_nhds.mul ((hK.const_mul _).sub (hR.const_mul _)))
    (tendsto_const_nhds.mul ((hK.const_mul _).add (hR.const_mul _))) ?_
  exact mul_ne_zero hg.ne' hG

/-- The numerator `N(ρ) = (1−α)p(1−λ) − A₀λ(1 − (1+κ)ρ)`, `A₀ = α(1+ψ) − (1−α)p`, of the
whole-horizon multiplier; affine in `ρ`. -/
noncomputable def fd_N (α β δ ψ γ ρ : ℝ) : ℝ :=
  (1 - α) * fd_p α β δ ψ γ * (1 - fd_lam α β δ ψ γ) -
    (α * (1 + ψ) - (1 - α) * fd_p α β δ ψ γ) * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ)

/-- The denominator `Q(ρ) = (D(ρ) − pg)(1−λ) − pgλ(1 − (1+κ)ρ)` of the whole-horizon
multiplier; affine in `ρ`. -/
noncomputable def fd_Q (α β δ ψ γ ρ : ℝ) : ℝ :=
  (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) * (1 - fd_lam α β δ ψ γ) -
    fd_p α β δ ψ γ * fd_g α β δ γ * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ)

/-- The closed forms: for `ρ < 1`, `Σₜ Ĝₜ = Q(ρ)/(D(1−λ)(1−ρ))` and
`Σₜ ŷₜ = gN(ρ)/((ψ+α)D(1−λ)(1−ρ))`. -/
theorem fd_inf_closed {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ < 1) :
    fd_GInf α β δ ψ γ ρ = fd_Q α β δ ψ γ ρ /
        (fd_D α β δ ψ γ ρ * (1 - fd_lam α β δ ψ γ) * (1 - ρ)) ∧
      fd_yInf α β δ ψ γ ρ = fd_g α β δ γ * fd_N α β δ ψ γ ρ /
        ((ψ + α) * fd_D α β δ ψ γ ρ * (1 - fd_lam α β δ ψ γ) * (1 - ρ)) := by
  obtain ⟨-, -, -, -, -, -, hD, -, R8, -⟩ := fd_rel hp hρ.le
  have hl1 := fd_lam_lt_one hp
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have h1 : 1 - fd_lam α β δ ψ γ ≠ 0 := by linarith
  have h2 : 1 - ρ ≠ 0 := by linarith
  have hφ : fd_phi α β δ ψ γ ρ = fd_g α β δ γ * fd_lam α β δ ψ γ *
      (1 - (1 + fd_kap α β δ ψ) * ρ) / fd_D α β δ ψ γ ρ := by
    rw [eq_div_iff hD.ne']; exact R8
  have hq : fd_q α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := rfl
  constructor
  · unfold fd_GInf fd_KInf fd_Q
    rw [hφ, hq]
    field_simp
    ring
  · unfold fd_yInf fd_KInf fd_N
    rw [hφ, hq]
    field_simp
    ring

/-- The identity behind the monotonicity: `α(1+ψ)(n − g) − (1−α)(m − 1) = α(1+ψ)c̄/k̄ + (1−α)δ`. -/
theorem fd_key {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    α * (1 + ψ) * (fd_n α β δ ψ γ - fd_g α β δ γ) - (1 - α) * (fd_m α β δ ψ - 1) =
      α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ := by
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha := hp.1
  unfold fd_n fd_g fd_m fd_Y
  field_simp
  ring

/-- The cross difference of the affine maps `N` and `Q`:
`N(ρ₂)Q(ρ₁) − N(ρ₁)Q(ρ₂) = (ρ₂ − ρ₁)(1+κ)λ(1−λ)p(α(1+ψ)c̄/k̄ + (1−α)δ)`. -/
theorem fd_det {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) (ρ₁ ρ₂ : ℝ) :
    fd_N α β δ ψ γ ρ₂ * fd_Q α β δ ψ γ ρ₁ - fd_N α β δ ψ γ ρ₁ * fd_Q α β δ ψ γ ρ₂ =
      (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ * (1 - fd_lam α β δ ψ γ) *
        fd_p α β δ ψ γ * (α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ) := by
  have R5 := (fd_rel (ρ := 0) hp zero_le_one).2.2.2.2.1
  have key := fd_key hp
  unfold fd_N fd_Q fd_D
  linear_combination (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ *
    (1 - fd_lam α β δ ψ γ) * (-(α * (1 + ψ))) * R5 + (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) *
    fd_lam α β δ ψ γ * (1 - fd_lam α β δ ψ γ) * fd_p α β δ ψ γ * key

/-- **The whole-horizon cumulative multiplier increases with persistence** (AKMM, §8.6.2,
p. 231; Figure 8.4, right, p. 236: "as `ρ_η` increases … a larger multiplier"). Let
`0 ≤ ρ₁ < ρ₂ ≤ 1/(1+κ)` and suppose cumulative spending rises at `ρ₁`, `Σₜ Ĝₜ > 0`. Then it rises
at `ρ₂` too, and `Σₜ Δyₜ/Σₜ ΔGₜ` is strictly larger at `ρ₂`. Both `N` and `Q` are affine in `ρ`,
and `N(ρ₂)Q(ρ₁) − N(ρ₁)Q(ρ₂) = (ρ₂ − ρ₁)(1+κ)λ(1−λ)p(α(1+ψ)c̄/k̄ + (1−α)δ) > 0`. -/
theorem fd_multInf_strictMono {α β δ ψ γ ρ₁ ρ₂ : ℝ} (hp : fm_Params α β δ ψ γ) (h0 : 0 ≤ ρ₁)
    (h12 : ρ₁ < ρ₂) (h2 : (1 + fd_kap α β δ ψ) * ρ₂ ≤ 1) (hG : 0 < fd_GInf α β δ ψ γ ρ₁) :
    0 < fd_GInf α β δ ψ γ ρ₂ ∧ fd_multInf α β δ ψ γ ρ₁ < fd_multInf α β δ ψ γ ρ₂ := by
  have hκ := (fd_coef hp).2.2.2.2.1
  have hr2 : ρ₂ < 1 := by nlinarith
  have hr1 : ρ₁ < 1 := by linarith
  obtain ⟨-, -, -, -, R5, -, hD1, -, -, hp0⟩ := fd_rel hp hr1.le
  have hD2 := (fd_rel hp hr2.le).2.2.2.2.2.2.1
  obtain ⟨-, -, -, hg, -, -, hgn, -, -⟩ := fd_coef hp
  have hl0 := (fd_lam_props hp).1
  have hl1 := fd_lam_lt_one hp
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have hY : 0 < fd_Y α β δ := by linarith [(fd_coef hp).2.1, hp.2.2.2.2.1]
  have hC := (fd_coef hp).2.2.1
  have hd := hp.2.2.2.2.1
  have ha0 := hp.1
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  obtain ⟨hG1, -⟩ := fd_inf_closed hp hr1
  obtain ⟨hG2, -⟩ := fd_inf_closed hp hr2
  have hpos1 : 0 < fd_D α β δ ψ γ ρ₁ * (1 - fd_lam α β δ ψ γ) * (1 - ρ₁) := by
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 - ρ₁ := by linarith
    positivity
  have hpos2 : 0 < fd_D α β δ ψ γ ρ₂ * (1 - fd_lam α β δ ψ γ) * (1 - ρ₂) := by
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 - ρ₂ := by linarith
    positivity
  have hQ1 : 0 < fd_Q α β δ ψ γ ρ₁ := by
    rw [hG1] at hG; exact (div_pos_iff_of_pos_right hpos1).1 hG
  -- `Q` is affine and positive at `1/(1+κ)`
  have hmlpg : 0 < fd_m α β δ ψ - fd_lam α β δ ψ γ - fd_p α β δ ψ γ * fd_g α β δ γ := by
    nlinarith [mul_pos hp0 (sub_pos.2 hgn)]
  have hQaff : (1 - (1 + fd_kap α β δ ψ) * ρ₁) * fd_Q α β δ ψ γ ρ₂ =
      (1 - (1 + fd_kap α β δ ψ) * ρ₂) * fd_Q α β δ ψ γ ρ₁ + (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) *
        (1 - fd_lam α β δ ψ γ) * (fd_m α β δ ψ - fd_lam α β δ ψ γ -
          fd_p α β δ ψ γ * fd_g α β δ γ) := by
    unfold fd_Q fd_D; ring
  have hQ2 : 0 < fd_Q α β δ ψ γ ρ₂ := by
    have e1 : 0 < 1 - (1 + fd_kap α β δ ψ) * ρ₁ := by nlinarith
    have e2 : 0 ≤ (1 - (1 + fd_kap α β δ ψ) * ρ₂) * fd_Q α β δ ψ γ ρ₁ :=
      mul_nonneg (by linarith) hQ1.le
    have e3 : 0 < (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * (1 - fd_lam α β δ ψ γ) *
        (fd_m α β δ ψ - fd_lam α β δ ψ γ - fd_p α β δ ψ γ * fd_g α β δ γ) := by
      have : 0 < ρ₂ - ρ₁ := by linarith
      have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
      have : 0 < 1 + fd_kap α β δ ψ := by linarith
      positivity
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos e1.le h]
  refine ⟨by rw [hG2]; positivity, ?_⟩
  have hdet := fd_det hp ρ₁ ρ₂
  have hdpos : 0 < (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ *
      (1 - fd_lam α β δ ψ γ) * fd_p α β δ ψ γ * (α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ) := by
    have : 0 < ρ₂ - ρ₁ := by linarith
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 + fd_kap α β δ ψ := by linarith
    have : 0 < α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ := by
      have : 0 < 1 + ψ := by linarith [hp.2.2.2.2.2.1]
      have := mul_nonneg ha1.le hd
      positivity
    positivity
  have hm : ∀ ρ, ρ < 1 → 0 < fd_Q α β δ ψ γ ρ →
      fd_multInf α β δ ψ γ ρ = fd_Y α β δ * fd_N α β δ ψ γ ρ / ((ψ + α) * fd_Q α β δ ψ γ ρ) := by
    intro ρ hρ hQ
    obtain ⟨e1, e2⟩ := fd_inf_closed hp hρ
    have hDρ := (fd_rel hp hρ.le).2.2.2.2.2.2.1
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 - ρ := by linarith
    unfold fd_multInf
    rw [e1, e2]
    field_simp
  rw [hm ρ₁ hr1 hQ1, hm ρ₂ hr2 hQ2, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hfin := mul_pos (mul_pos hY hpa) (hdet ▸ hdpos)
  linear_combination hfin

/-- The hypothesis of `fd_multInf_strictMono` holds near the top of the range: at
`ρ = 1/(1+κ)`, cumulative spending rises, `Σₜ Ĝₜ > 0` (and `Σₜ Ĝₜ` is affine in `ρ` up to a
positive factor). -/
theorem fd_GInf_pos_top {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fd_GInf α β δ ψ γ (1 / (1 + fd_kap α β δ ψ)) := by
  have hκ := (fd_coef hp).2.2.2.2.1
  have hr : 1 / (1 + fd_kap α β δ ψ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨-, -, -, -, R5, -, hD, -, -, hp0⟩ := fd_rel hp hr.le
  obtain ⟨-, -, -, hg, -, -, hgn, -, -⟩ := fd_coef hp
  have hl1 := fd_lam_lt_one hp
  rw [(fd_inf_closed hp hr).1]
  have : 0 < 1 - 1 / (1 + fd_kap α β δ ψ) := by linarith
  have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
  have hQ : fd_Q α β δ ψ γ (1 / (1 + fd_kap α β δ ψ)) = (1 - fd_lam α β δ ψ γ) *
      (fd_p α β δ ψ γ * (fd_n α β δ ψ γ - fd_g α β δ γ)) := by
    unfold fd_Q fd_D
    have : (1 + fd_kap α β δ ψ) * (1 / (1 + fd_kap α β δ ψ)) = 1 := by field_simp
    linear_combination -(1 - fd_lam α β δ ψ γ) * R5 -
      fd_lam α β δ ψ γ * (1 - fd_lam α β δ ψ γ - fd_p α β δ ψ γ * fd_g α β δ γ) * this
  rw [hQ]
  have : 0 < fd_p α β δ ψ γ * (fd_n α β δ ψ γ - fd_g α β δ γ) := mul_pos hp0 (by linarith)
  positivity

/-! ### The multiplier and the labour supply elasticity -/

/-- **The characteristic polynomial is a pencil in `ψ`**: with `θ = r̄(1−α)`,
`(ψ+α)[(m − x)(1 − (1+κ)x) − nκψx] = ψf₀(x) + αf₁(x)`, where
`f₀(x) = (1/β − x)(1 − x) − βθ(ȳ/k̄ − δ)x` (inelastic labour, `ψ → ∞`) and
`f₁(x) = (1/β + θ/α − x)(1 − (1 + βθ/α)x)` (`ψ = 0`) do not depend on `ψ`. -/
theorem fd_pencil {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) (x : ℝ) :
    (ψ + α) * ((fd_m α β δ ψ - x) * (1 - (1 + fd_kap α β δ ψ) * x) -
      fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * x) =
      ψ * ((1 / β - x) * (1 - x) - β * (fm_r β δ * (1 - α)) * (fd_Y α β δ - δ) * x) +
        α * ((1 / β + fm_r β δ * (1 - α) / α - x) *
          (1 - (1 + β * (fm_r β δ * (1 - α)) / α) * x)) := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  have hpa : 0 < ψ + α := by linarith
  unfold fd_m fd_kap fd_n fd_C fd_Y fm_r
  field_simp
  ring

/-- Below the stable root: if `0 ≤ x ≤ 1` and `(m − x)(1 − (1+κ)x) − nκψx ≥ 0`, then `x ≤ λ`. -/
theorem fd_le_lam {α β δ ψ γ x : ℝ} (hp : fm_Params α β δ ψ γ) (hx : x ≤ 1)
    (hF : 0 ≤ (fd_m α β δ ψ - x) * (1 - (1 + fd_kap α β δ ψ) * x) -
      fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * x) : x ≤ fd_lam α β δ ψ γ := by
  obtain ⟨hl0, -, hchar⟩ := fd_lam_props hp
  have hl1 := fd_lam_lt_one hp
  obtain ⟨-, -, -, hg, hκ, hm, hgn, -, -⟩ := fd_coef hp
  have hψ := hp.2.2.2.2.2.1
  have hw : 0 < fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) := by
    have : 0 < fd_n α β δ ψ γ := by linarith
    positivity
  set a := 1 + fd_kap α β δ ψ
  set m := fd_m α β δ ψ
  set w := fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ)
  set lam := fd_lam α β δ ψ γ
  -- `F(1) < 0` places `1` between the roots
  have h1 : (1 - lam) * (a * (1 + lam) - (a * m + 1 + w)) < 0 := by nlinarith
  have h2 : a * (1 + lam) - (a * m + 1 + w) < 0 := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam) h]
  by_contra hlt
  rw [not_le] at hlt
  have : (m - x) * (1 - a * x) - w * x = (x - lam) * (a * (x + lam) - (a * m + 1 + w)) := by
    linear_combination hchar
  have h3 : a * (x + lam) - (a * m + 1 + w) < 0 := by nlinarith
  nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < x - lam) h3]

/-- `f₀ ≥ 0` on `[0, 1/(1 + βθ/α)]` (for `δ ≤ 1`), where
`f₀(x) = (1/β − x)(1 − x) − βθ(ȳ/k̄ − δ)x` and `θ = r̄(1−α)`. At `x₁ = α/(α + βθ)`,
`(α + βθ)²f₀(x₁) = θβ(1−α)(1−δ)(1 − β(1 − δ + αδ)) ≥ 0`; `f₀(1) < 0` and convexity do the rest. -/
theorem fd_f0_nonneg {α β δ ψ γ x : ℝ} (hp : fm_Params α β δ ψ γ) (hδ : δ ≤ 1)
    (hx : x * (α + β * (fm_r β δ * (1 - α))) ≤ α) :
    0 ≤ (1 / β - x) * (1 - x) - β * (fm_r β δ * (1 - α)) * (fd_Y α β δ - δ) * x := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩ := hp
  obtain ⟨hr0, hY, -, -, -, -, -, -, hbr⟩ := fd_coef ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩
  set r := fm_r β δ
  set θ := r * (1 - α)
  have hθ : 0 < θ := by have : 0 < 1 - α := by linarith
                        positivity
  have hb1' : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
  set f0 : ℝ → ℝ := fun x => (1 / β - x) * (1 - x) - β * θ * (fd_Y α β δ - δ) * x
  change 0 ≤ f0 x
  have hden : 0 < α + β * θ := by positivity
  set x1 := α / (α + β * θ) with hx1def
  have hlx : x ≤ x1 := by rw [hx1def, le_div_iff₀ hden]; exact hx
  have hx1lt : x1 < 1 := by
    rw [hx1def, div_lt_one hden]
    have : 0 < β * θ := by positivity
    linarith
  have hfx1 : 0 ≤ f0 x1 := by
    have e : f0 x1 = θ * β * (1 - α) * (1 - δ) * (1 - β * (1 - δ + α * δ)) /
        (α + β * θ) ^ 2 := by
      have hYr : fd_Y α β δ = r / α := rfl
      have hE : α + β * θ - α * β - β * (r - α * δ) * (α + β * θ) =
          β * (1 - α) * (1 - δ) * (1 - β * (1 - δ + α * δ)) := by
        simp only [θ]
        linear_combination (1 - α - α - (β * r + (1 - β + β * δ)) * (1 - α) +
          α * β * δ * (1 - α)) * hbr
      have hf : f0 x1 = θ * (α + β * θ - α * β - β * (r - α * δ) * (α + β * θ)) /
          (α + β * θ) ^ 2 := by
        simp only [f0, hx1def]
        rw [hYr]
        field_simp
        ring
      rw [hf, hE]
      ring
    rw [e]
    have : 0 ≤ 1 - β * (1 - δ + α * δ) := by
      have : 1 - δ + α * δ ≤ 1 := by nlinarith
      have : β * (1 - δ + α * δ) ≤ β * 1 := by
        apply mul_le_mul_of_nonneg_left this hb0.le
      linarith
    have : 0 ≤ 1 - δ := by linarith
    have : 0 < 1 - α := by linarith
    positivity
  have hf01 : f0 1 < 0 := by
    have e : f0 1 = -(β * θ * (fd_Y α β δ - δ)) := by simp only [f0]; ring
    have : 0 < β * θ * (fd_Y α β δ - δ) := by
      have : 0 < fd_Y α β δ - δ := by linarith
      positivity
    linarith
  -- convexity of `f₀`
  have hb : 1 + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ)) < 0 := by
    have e1 : f0 1 - f0 x1 = (1 - x1) * (1 + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) := by
      simp only [f0]; ring
    have : (1 - x1) * (1 + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) < 0 := by linarith
    by_contra h
    rw [not_lt] at h
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x1) h
    linarith
  have e2 : f0 x - f0 x1 = (x - x1) * (x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) := by
    simp only [f0]; ring
  have h4 := mul_nonneg (by linarith : (0 : ℝ) ≤ x1 - x)
    (by linarith : (0 : ℝ) ≤ -(x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))))
  have h5 : (x - x1) * (x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) =
      (x1 - x) * -(x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) := by ring
  linarith

/-- **The stable root rises with `ψ`** (for `δ ≤ 1`): a less elastic labour supply makes capital
adjust more slowly. The proof uses the pencil `fd_pencil`: `f₀` is nonnegative at `λ(ψ₁)`, so
the characteristic polynomial for `ψ₂ > ψ₁` is nonnegative at `λ(ψ₁)`. The assumption `δ ≤ 1`
gives `f₀(1/(1 + βθ/α)) ≥ 0`. -/
theorem fd_lam_mono_psi {α β δ ψ₁ ψ₂ γ : ℝ} (hp : fm_Params α β δ ψ₁ γ) (hψ : ψ₁ ≤ ψ₂)
    (hδ : δ ≤ 1) : fd_lam α β δ ψ₁ γ ≤ fd_lam α β δ ψ₂ γ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩ := hp
  have hp2 : fm_Params α β δ ψ₂ γ := ⟨ha0, ha1, hb0, hb1, hd, by linarith, hγ⟩
  have hp1 : fm_Params α β δ ψ₁ γ := ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩
  obtain ⟨hl0, -, hchar⟩ := fd_lam_props hp1
  have hl1 := fd_lam_lt_one hp1
  obtain ⟨hr0, hY, -, -, -, -, -, -, hbr⟩ := fd_coef hp1
  set lam := fd_lam α β δ ψ₁ γ
  set r := fm_r β δ
  set θ := r * (1 - α)
  have hθ : 0 < θ := by have : 0 < 1 - α := by linarith
                        positivity
  set f0 : ℝ → ℝ := fun x => (1 / β - x) * (1 - x) - β * θ * (fd_Y α β δ - δ) * x
  set f1 : ℝ → ℝ := fun x => (1 / β + θ / α - x) * (1 - (1 + β * θ / α) * x)
  have hpen1 := fd_pencil hp1 lam
  have hpen2 := fd_pencil hp2 lam
  have hF1 : ψ₁ * f0 lam + α * f1 lam = 0 := by
    simp only [f0, f1]; rw [← hpen1]; rw [hchar]; ring
  -- `f₀(lam) ≥ 0`
  have hb1' : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
  have hf0 : 0 ≤ f0 lam := by
    by_contra hneg
    rw [not_le] at hneg
    have hf1 : 0 < f1 lam := by nlinarith
    have hm1 : 0 < 1 / β + θ / α - lam := by
      have : 0 < θ / α := div_pos hθ ha0
      linarith
    have hx1 : 0 < 1 - (1 + β * θ / α) * lam := by
      by_contra h
      rw [not_lt] at h
      have := mul_nonpos_of_nonneg_of_nonpos hm1.le h
      simp only [f1] at hf1
      linarith
    have hden : 0 < α + β * θ := by positivity
    have hlx : lam * (α + β * θ) ≤ α := by
      have e : (1 + β * θ / α) * lam = (α + β * θ) * lam / α := by field_simp
      rw [e] at hx1
      have : (α + β * θ) * lam / α < 1 := by linarith
      rw [div_lt_one ha0] at this
      linarith
    exact absurd (fd_f0_nonneg hp1 hδ hlx) (not_le.2 hneg)
  -- the characteristic polynomial at `ψ₂` is nonnegative at `lam`
  have hpa2 : 0 < ψ₂ + α := by linarith
  apply fd_le_lam hp2 hl1.le
  have : (ψ₂ + α) * ((fd_m α β δ ψ₂ - lam) * (1 - (1 + fd_kap α β δ ψ₂) * lam) -
      fd_n α β δ ψ₂ γ * (fd_kap α β δ ψ₂ * ψ₂) * lam) = (ψ₂ - ψ₁) * f0 lam := by
    rw [hpen2]; simp only [f0, f1] at hF1 ⊢; linear_combination hF1
  have h2 : 0 ≤ (ψ₂ + α) * ((fd_m α β δ ψ₂ - lam) * (1 - (1 + fd_kap α β δ ψ₂) * lam) -
      fd_n α β δ ψ₂ γ * (fd_kap α β δ ψ₂ * ψ₂) * lam) := by
    rw [this]; exact mul_nonneg (by linarith) hf0
  exact (mul_nonneg_iff_of_pos_left hpa2).1 h2

/-- The impact multiplier as `(ȳ/k̄)(1−α)/Φ` with
`Φ = (ȳ/k̄)(1−α) + (ψ+α)c̄/k̄ + (1 − (1+κ)ρ)·(ψ+α)n·λ/(m − λ)`, for `0 ≤ ρ ≤ 1/(1+κ)`. -/
theorem fd_impact_mult_Phi {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) :
    fd_mult α β δ ψ γ ρ 1 = fd_Y α β δ * (1 - α) /
      (fd_Y α β δ * (1 - α) + (ψ + α) * fd_C α β δ γ + (1 - (1 + fd_kap α β δ ψ) * ρ) *
        ((ψ + α) * fd_n α β δ ψ γ) * (fd_lam α β δ ψ γ / (fd_m α β δ ψ - fd_lam α β δ ψ γ))) := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, R2, -, -, R5, -, -, -, -, hp0⟩ := fd_rel hp hρ1
  obtain ⟨hl0, hl1, -⟩ := fd_lam_props hp
  obtain ⟨-, hY, hC, hg, hκ, hm, hgn, -, -⟩ := fd_coef hp
  have hlm : 0 < fd_m α β δ ψ - fd_lam α β δ ψ γ := by nlinarith
  have hn : 0 < fd_n α β δ ψ γ := by linarith
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hY0 : 0 < fd_Y α β δ := by linarith [hp.2.2.2.2.1]
  have hDp := (fd_q_phi hp hρ0 hρ).2.2.2
  have R3 : fd_g α β δ γ = γ * fd_C α β δ γ := rfl
  have hτ : 0 ≤ 1 - (1 + fd_kap α β δ ψ) * ρ := by linarith
  have hΦ : 0 < fd_Y α β δ * (1 - α) + (ψ + α) * fd_C α β δ γ + (1 - (1 + fd_kap α β δ ψ) * ρ) *
      ((ψ + α) * fd_n α β δ ψ γ) * (fd_lam α β δ ψ γ / (fd_m α β δ ψ - fd_lam α β δ ψ γ)) := by
    have : 0 ≤ (1 - (1 + fd_kap α β δ ψ) * ρ) * ((ψ + α) * fd_n α β δ ψ γ) *
        (fd_lam α β δ ψ γ / (fd_m α β δ ψ - fd_lam α β δ ψ γ)) := by positivity
    have : 0 < fd_Y α β δ * (1 - α) + (ψ + α) * fd_C α β δ γ := by positivity
    linarith
  rw [fd_impact_mult hp hρ1, div_eq_div_iff (by positivity) hΦ.ne']
  have hp' : fd_p α β δ ψ γ = (fd_m α β δ ψ - fd_lam α β δ ψ γ) / fd_n α β δ ψ γ := rfl
  unfold fd_D
  rw [hp']
  field_simp
  linear_combination -(fd_m α β δ ψ - fd_lam α β δ ψ γ) * R2 +
    (fd_m α β δ ψ - fd_lam α β δ ψ γ) * (ψ + α) * R3

/-- **The impact multiplier is larger when labour supply is more elastic** (AKMM, Figure 8.4,
right, p. 236: "if `ψ` is smaller, so labor supply is more elastic, … the fiscal multiplier is
larger"; §8.8, p. 234). For `δ ≤ 1`, `ψ₁ < ψ₂` and `0 ≤ ρ ≤ 1/(1+κ(ψ₁))`,
`Δy₀/ΔG₀` at `ψ₂` is strictly smaller than at `ψ₁`. In `fd_impact_mult_Phi`, every term of `Φ`
is nondecreasing in `ψ` and `(ψ+α)c̄/k̄` is strictly increasing: `κ` and `m` fall with `ψ` and the
stable root `λ` rises (`fd_lam_mono_psi`). -/
theorem fd_impact_mult_antitone_psi {α β δ ψ₁ ψ₂ γ ρ : ℝ} (hp : fm_Params α β δ ψ₁ γ)
    (hψ : ψ₁ < ψ₂) (hδ : δ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : (1 + fd_kap α β δ ψ₁) * ρ ≤ 1) :
    fd_mult α β δ ψ₂ γ ρ 1 < fd_mult α β δ ψ₁ γ ρ 1 := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩ := hp
  have hp1 : fm_Params α β δ ψ₁ γ := ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩
  have hp2 : fm_Params α β δ ψ₂ γ := ⟨ha0, ha1, hb0, hb1, hd, by linarith, hγ⟩
  have hpa1 : 0 < ψ₁ + α := by linarith
  have hpa2 : 0 < ψ₂ + α := by linarith
  obtain ⟨hr0, hY, hC, -, hκ1, hm1, hgn1, -, -⟩ := fd_coef hp1
  have hκ2 := (fd_coef hp2).2.2.2.2.1
  have hgn2 := (fd_coef hp2).2.2.2.2.2.2.1
  have hg := (fd_coef hp1).2.2.2.1
  -- `κ` and `m` fall with `ψ`
  have hκ : fd_kap α β δ ψ₂ ≤ fd_kap α β δ ψ₁ := by
    unfold fd_kap
    apply div_le_div_of_nonneg_left _ hpa1 (by linarith)
    have : 0 < 1 - α := by linarith
    positivity
  have hm : fd_m α β δ ψ₂ ≤ fd_m α β δ ψ₁ := by
    unfold fd_m
    have : fm_r β δ * (1 + ψ₂) / (ψ₂ + α) ≤ fm_r β δ * (1 + ψ₁) / (ψ₁ + α) := by
      rw [div_le_div_iff₀ hpa2 hpa1]
      nlinarith [mul_pos hr0 (by linarith : (0 : ℝ) < 1 - α)]
    linarith
  have hρ2 : (1 + fd_kap α β δ ψ₂) * ρ ≤ 1 := by nlinarith
  rw [fd_impact_mult_Phi hp2 hρ0 hρ2, fd_impact_mult_Phi hp1 hρ0 hρ]
  have hl := fd_lam_mono_psi hp1 hψ.le hδ
  have hl01 := (fd_lam_props hp1).1
  have hl11 := fd_lam_lt_one hp1
  have hl12 := fd_lam_lt_one hp2
  have hlm1 : 0 < fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ := by linarith
  have hlm2 : 0 < fd_m α β δ ψ₂ - fd_lam α β δ ψ₂ γ := by
    linarith [(fd_coef hp2).2.2.2.2.2.1]
  have hY0 : 0 < fd_Y α β δ := by linarith
  have ha1' : 0 < 1 - α := by linarith
  -- the four factors
  have hA : fd_Y α β δ * (1 - α) + (ψ₁ + α) * fd_C α β δ γ <
      fd_Y α β δ * (1 - α) + (ψ₂ + α) * fd_C α β δ γ := by nlinarith
  have hB0 : 0 ≤ 1 - (1 + fd_kap α β δ ψ₁) * ρ := by linarith
  have hB : 1 - (1 + fd_kap α β δ ψ₁) * ρ ≤ 1 - (1 + fd_kap α β δ ψ₂) * ρ := by nlinarith
  have hn1 : (ψ₁ + α) * fd_n α β δ ψ₁ γ = fd_Y α β δ * (1 - α) + (ψ₁ + α) * ((1 + γ) *
      fd_C α β δ γ) := (fd_rel (ρ := 0) hp1 zero_le_one).2.1
  have hn2 : (ψ₂ + α) * fd_n α β δ ψ₂ γ = fd_Y α β δ * (1 - α) + (ψ₂ + α) * ((1 + γ) *
      fd_C α β δ γ) := (fd_rel (ρ := 0) hp2 zero_le_one).2.1
  have hCc0 : 0 ≤ (ψ₁ + α) * fd_n α β δ ψ₁ γ := by rw [hn1]; positivity
  have hCc : (ψ₁ + α) * fd_n α β δ ψ₁ γ ≤ (ψ₂ + α) * fd_n α β δ ψ₂ γ := by
    rw [hn1, hn2]
    have : (ψ₁ + α) * ((1 + γ) * fd_C α β δ γ) ≤ (ψ₂ + α) * ((1 + γ) * fd_C α β δ γ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hE0 : 0 ≤ fd_lam α β δ ψ₁ γ / (fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ) := by positivity
  have hE : fd_lam α β δ ψ₁ γ / (fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ) ≤
      fd_lam α β δ ψ₂ γ / (fd_m α β δ ψ₂ - fd_lam α β δ ψ₂ γ) := by
    rw [div_le_div_iff₀ hlm1 hlm2]
    nlinarith [mul_le_mul hl hm (by linarith [(fd_coef hp2).2.2.2.2.2.1]) (by linarith)]
  have hprod := mul_le_mul (mul_le_mul hB hCc hCc0 (by linarith)) hE hE0
    (mul_nonneg (by linarith) (by linarith))
  have hΦ1 : 0 < fd_Y α β δ * (1 - α) + (ψ₁ + α) * fd_C α β δ γ +
      (1 - (1 + fd_kap α β δ ψ₁) * ρ) * ((ψ₁ + α) * fd_n α β δ ψ₁ γ) *
        (fd_lam α β δ ψ₁ γ / (fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ)) := by
    have := mul_nonneg (mul_nonneg hB0 hCc0) hE0
    have : 0 < fd_Y α β δ * (1 - α) + (ψ₁ + α) * fd_C α β δ γ := by positivity
    linarith
  apply div_lt_div_of_pos_left (by positivity) hΦ1
  linarith

/-! ### The linearisation -/

/-- **The static equations are exactly log-linear** (AKMM, (8.10), (8.15) with (8.17), and
(8.18), p. 230): if `y = kᵅℓ^{1−α}`, `w/c = ℓ^ψ` with `w = (1−α)y/ℓ`, and `G = γηc` hold at a
point and at the steady state (`η̄ = 1`), then in log deviations `ŷ = αk̂ + (1−α)ℓ̂`,
`ŷ = ĉ + (1+ψ)ℓ̂` and `Ĝ = η̂ + ĉ`, exactly. -/
theorem fd_static_exact {α ψ γ k ℓ c y G η kb ℓb cb yb Gb : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hη : 0 < η) (hkb : 0 < kb) (hℓb : 0 < ℓb) (hcb : 0 < cb) (hγ : 0 < γ)
    (hy : y = k ^ α * ℓ ^ (1 - α)) (hyb : yb = kb ^ α * ℓb ^ (1 - α))
    (hL : (1 - α) * y / ℓ / c = ℓ ^ ψ) (hLb : (1 - α) * yb / ℓb / cb = ℓb ^ ψ) (ha : α < 1)
    (hG : G = γ * η * c) (hGb : Gb = γ * 1 * cb) :
    Real.log (y / yb) = α * Real.log (k / kb) + (1 - α) * Real.log (ℓ / ℓb) ∧
      Real.log (y / yb) = Real.log (c / cb) + (1 + ψ) * Real.log (ℓ / ℓb) ∧
      Real.log (G / Gb) = Real.log η + Real.log (c / cb) := by
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyb0 : 0 < yb := by rw [hyb]; positivity
  have e1 : y / yb = (k / kb) ^ α * (ℓ / ℓb) ^ (1 - α) := by
    rw [hy, hyb, Real.div_rpow hk.le hkb.le, Real.div_rpow hℓ.le hℓb.le]
    have := Real.rpow_pos_of_pos hkb α
    have := Real.rpow_pos_of_pos hℓb (1 - α)
    field_simp
  have h1a : 0 < 1 - α := by linarith
  -- `(1−α)y = cℓ^{1+ψ}`
  have e2 : y / yb = (c / cb) * (ℓ / ℓb) ^ (1 + ψ) := by
    have h1 : (1 - α) * y = c * ℓ ^ (1 + ψ) := by
      rw [Real.rpow_add hℓ, Real.rpow_one]
      field_simp at hL
      linarith
    have h2 : (1 - α) * yb = cb * ℓb ^ (1 + ψ) := by
      rw [Real.rpow_add hℓb, Real.rpow_one]
      field_simp at hLb
      linarith
    rw [Real.div_rpow hℓ.le hℓb.le]
    have := Real.rpow_pos_of_pos hℓb (1 + ψ)
    have hy' : y = c * ℓ ^ (1 + ψ) / (1 - α) := by rw [← h1]; field_simp
    have hyb' : yb = cb * ℓb ^ (1 + ψ) / (1 - α) := by rw [← h2]; field_simp
    rw [hy', hyb']
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_rpow (by positivity)]
  · rw [e2, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
  · rw [hG, hGb, mul_one]
    have : γ * η * c / (γ * cb) = η * (c / cb) := by field_simp
    rw [this, Real.log_mul hη.ne' (by positivity)]

/-- **The linearised resource constraint** (AKMM, (8.11), p. 229): with the steady state
`ȳ = c̄ + δk̄ + Ḡ`, the map `s ↦ ȳe^{s ŷ} − c̄e^{s ĉ} − k̄e^{s k̂′} + (1−δ)k̄e^{s k̂} − Ḡe^{s Ĝ}`
(the resource constraint along the log deviation `s·(ŷ, ĉ, k̂′, k̂, Ĝ)`) vanishes at `s = 0` and
has derivative `ȳŷ − c̄ĉ − k̄k̂′ + (1−δ)k̄k̂ − ḠĜ` there; dividing by `k̄` gives the resource row
of `fd_IsIRF`. -/
theorem fd_resource_linear {yb cb kb Gb δ dy dc dk' dk dG : ℝ}
    (hs : yb = cb + δ * kb + Gb) :
    (fun s : ℝ => yb * Real.exp (s * dy) - cb * Real.exp (s * dc) - kb * Real.exp (s * dk') +
        (1 - δ) * kb * Real.exp (s * dk) - Gb * Real.exp (s * dG)) 0 = 0 ∧
      HasDerivAt (fun s : ℝ => yb * Real.exp (s * dy) - cb * Real.exp (s * dc) -
        kb * Real.exp (s * dk') + (1 - δ) * kb * Real.exp (s * dk) - Gb * Real.exp (s * dG))
        (yb * dy - cb * dc - kb * dk' + (1 - δ) * kb * dk - Gb * dG) 0 := by
  refine ⟨by simp only [zero_mul, Real.exp_zero, mul_one]; rw [hs]; ring, ?_⟩
  have hE : ∀ d : ℝ, HasDerivAt (fun s : ℝ => Real.exp (s * d)) d 0 := fun d => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const d).exp
    simpa using this
  have := (((((hE dy).const_mul yb).sub ((hE dc).const_mul cb)).sub
    ((hE dk').const_mul kb)).add ((hE dk).const_mul ((1 - δ) * kb))).sub ((hE dG).const_mul Gb)
  exact this

/-- **The linearised Euler equation** (AKMM, (8.14) with (8.16), p. 230): with
`β(1 + r̄ − δ) = 1`, the map `s ↦ β(1 + r̄e^{s(ŷ′−k̂′)} − δ)e^{s(ĉ−ĉ′)}` (the Euler equation
`1 = β(1 + r′ − δ)c/c′` with `r′ = r̄e^{ŷ′−k̂′}`, along the log deviation) equals `1` at `s = 0`
and has derivative `βr̄(ŷ′ − k̂′) + ĉ − ĉ′` there; setting it to zero gives the Euler row of
`fd_IsIRF`. -/
theorem fd_euler_linear {β δ rb dy' dk' dc dc' : ℝ} (hE : β * (1 + rb - δ) = 1) :
    (fun s : ℝ => β * (1 + rb * Real.exp (s * (dy' - dk')) - δ) * Real.exp (s * (dc - dc'))) 0 =
        1 ∧
      HasDerivAt (fun s : ℝ => β * (1 + rb * Real.exp (s * (dy' - dk')) - δ) *
        Real.exp (s * (dc - dc'))) (β * rb * (dy' - dk') + (dc - dc')) 0 := by
  refine ⟨by simp only [zero_mul, Real.exp_zero, mul_one]; exact hE, ?_⟩
  have hX : ∀ d : ℝ, HasDerivAt (fun s : ℝ => Real.exp (s * d)) d 0 := fun d => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const d).exp
    simpa using this
  have h1 := ((((hX (dy' - dk')).const_mul rb).const_add 1).sub_const δ).const_mul β
  have h2 := h1.mul (hX (dc - dc'))
  convert h2 using 1
  · simp only [zero_mul, Real.exp_zero, mul_one]
    linear_combination -(dc - dc') * hE

end AKMM.QuantitativeMethods
