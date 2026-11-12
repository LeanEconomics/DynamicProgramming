# Source map: AKMM Chapter 14

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 14, Real business cycles (Kurt Mitman), pp. 405–438, and Appendix 14.A,
pp. 863–867. Page references are the draft's running heads. Lean names are relative to
`AKMM.RealBusinessCycles` unless qualified. Departures from the book are in
[corrections](corrections.md).

## §14.1–14.2 Introduction and history

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 405–409 | Kitchin, Juglar, Kondratiev cycles; Wicksell, Keynes, Lucas, Kydland–Prescott; Figure 14.1 | not formalised: history and narrative |

## §14.3 First look at the data; §14.3.1 Filters (`HPFilter`, `HPLimit`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 409–410, Figures 14.2–14.3, NBER box | Recession dating; trend/cycle pictures | not formalised: narrative, figure |
| p. 410 | Trend-stationary and difference-stationary DGPs | not formalised: narrative (no claim derived) |
| p. 411, (14.1) | HP objective, second-difference constraint | `hpD`, `hpA`, `hpFit`, `hpPen`, `hpObj`, `hp_D_apply`, `hp_pen_eq` |
| p. 411 | "with µ = 0, τ_{t+1} − τ_t = τ_t − τ_{t−1}, which imposes a linear trend" | `hp_pen_zero_iff` |
| p. 411 | Constrained form ⇔ Lagrangian form when the constraint binds | `hp_constrained_of_lagrangian`, `hp_constrained_unique` |
| p. 412 | `1600 × (1/4)⁴ = 6.25` (Ravn–Uhlig) | `hp_ravn_uhlig` |
| p. 412 | FOC system `(I + λA)τ = Y`; the trend minimises the objective | `eq_14_1`, `hp_obj_expand`, `hp_quad_pos` |
| p. 412 | `I + λA` invertible (positive definite); unique trend `τ = (I + λA)⁻¹Y` | `hp_posDef`, `hp_unique`, `hp_trend_eq`, `hp_trend_exists` |
| p. 412 | The printed pentadiagonal `A` | `hp_A_apply`, `hp_A_interior`, `hp_A_row0`, `hp_A_row1`, `hp_A_rowLast`, `hp_A_rowLast1` |
| p. 412 | Interior FOC `τ_t − λ(…) = Y_t`, `2 ≤ t ≤ T − 2` | corrected: `hp_bracket_eq`, `hp_foc_interior`; printed false: `hp_foc_printed_iff`, `hp_foc_printed_false` |
| p. 411 | "In the limit as λ → ∞, the extracted trend converges to a linear function" | `hp_limit_ols` (the limit is the OLS linear trend `hpOLS`), with `hp_det_pos`, `hp_ols_normal`, `hp_pen_affine`, `hp_ols_pythagoras`, `hp_trend_bounds` |
| p. 412 | "the filter may produce spurious results towards the beginning and end of the sample"; choice of λ | not formalised: informal remarks |
| pp. 412–413 | Spectral representation `Yₜ = ∫A(ω)cos(ωt)dω + ∫B(ω)sin(ωt)dω` of any stationary process | beyond the text, proved in Hilbert-space form (correction 12): spectral measure `sden_spectral`, `sden_posDef`, `herg_herglotz`; the Kolmogorov isometry `cramIso`, `cram_iso_exp`, `cram_iso_range`, `cram_spectral_representation`; the orthogonal-increment measure `cramZ`, `cram_Z_inner`, `cram_Z_norm_sq`; real processes: `herg_symm_of_real`. The stochastic-integral notation and the real `A`, `B` form are a remark in `Cramer`, not formalised |
| p. 412, footnote 5 | `sin(2πtf)` completes a cycle at `t = 2π` | corrected in prose (correction 5); no theorem |

## §14.3.2 Stylised facts

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 413–417 | Pro-/countercyclical, leading/lagging (definitions); Facts 1–6; Tables 14.1–14.3; Figures 14.4–14.5 | not formalised: definitions used only for data; empirical facts |

## §14.3.3 Conditional moments (`SVAR`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 418 | Reduced-form VAR `Xₜ = BXₜ₋₁ + ηₜ`; structural `AXₜ = FXₜ₋₁ + εₜ` | `svar_reduced_form` (`B = A⁻¹F`, `η = A⁻¹ε`, `ε = Aη`) |
| p. 418 | Lower-triangular `A` (timing restrictions) | `svar_det`, `svar_isUnit_iff`, `svar_inv_lower` |
| p. 419 | First variable does not respond contemporaneously to the others | `svar_impact_recursive` |
| p. 419 | IRF `∂X_{t+s}/∂εₜ` | `svar_irf` (`(A⁻¹F)ˢA⁻¹`, via AKMM Ch 7 `AKMM.Uncertainty.sde_impulse_response`) |
| p. 419, Figures 14.6–14.7 | Estimated SVAR and LP IRFs | not formalised: empirical |

## §14.4.1 A simple business-cycle model (`SimpleModel`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 420, (14.2) | `E₀Σβᵗ(ln cₜ + φ ln(1 − ℓₜ))` | period utility is Miao's `Miao.NeoclassicalGrowth.rb_u φ` |
| p. 420, (14.3) | `Yₜ = zₜℓₜ`; `w = z` | `sm_wage` |
| p. 420 | `log zₜ = ρ log zₜ₋₁ + σε` | used in `sm_interest_rate` (finite-state shocks) |
| p. 421, (14.4)–(14.5) | Intratemporal condition `w/c = φ/(1 − ℓ)` | `eq_14_5`, `sm_static_deriv`; sufficiency `sm_static_suff` (Miao `rb_u_tangent`) |
| p. 421, (14.6) | Euler equation `1/cₜ = βEₜ[Rₜ₊₁/cₜ₊₁]` | `eq_14_6` |
| p. 421, (14.7) | `φ/(1 − ℓ) = 1/ℓ` with `B = 0` | `eq_14_7` |
| p. 421 | Hours constant, independent of the wage; output, consumption, TFP perfectly correlated | `sm_equilibrium` |
| p. 421 | "When TFP is high … the real interest rate falls" | `sm_interest_rate`, `sm_interest_rate_falls` (`ρ < 1`) |
| p. 421 | Log–log preferences: Frisch elasticity `(1 − ℓ)/ℓ`; `= 2` at `ℓ = 1/3` | `sm_frisch`, `sm_leisure_derivs`, `sm_frisch_two`, `sm_frisch_cd` (AKMM Ch 12 `AKMM.LaborSupply.frischF`, `dyn_frisch_cd`) |
| p. 421 | Frisch = response holding marginal utility constant | `sm_frisch_response` |
| pp. 421–422 | Income and substitution effects cancel; NK preview | consequence of `sm_equilibrium`; narrative otherwise |

## §14.4.2 The core RBC model (`CoreRBC`, `Impulse`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 422 | Preferences `E₀ΣβᵗU(cₜ, 1 − ℓₜ)`, `Yₜ = zₜF(kₜ, ℓₜ)`, `kₜ₊₁ = (1 − δ)kₜ + iₜ`, AR(1) log TFP | `rbcRes`, `rbc_Bellman` (finite-state Markov TFP) |
| p. 423 | Competitive equilibrium is efficient; CE allocations = planner's | Miao `Miao.NeoclassicalGrowth.rb_sce_iff`, `rb_sce_optimal` (log/Cobb–Douglas case, measure-theoretic), with `rbc_calib_utility` linking the calibrated utility; general `U, F` not formalised (asserted by the book) |
| p. 423 | Bellman `V(k, z) = max U(zF + (1 − δ)k − k′, 1 − ℓ) + E[V(k′, z′)∣z]` | `rbc_Bellman` (with `β`; correction 2), non-vacuity `rbc_example_bellman` |
| p. 423, (14.8) | `zF₂(k, ℓ) = U₂/U₁` | `eq_14_8` |
| p. 423, (14.9) | `U₁ = βE[V₁(k′, z′)∣z]` | `eq_14_9`; printed Bellman vs (14.9): `rbc_printed_bellman_beta` |
| p. 423, (14.10) | Envelope condition | `eq_14_10` |
| p. 423, (14.11) | Stochastic Euler equation | `eq_14_11` |
| pp. 423–424 | Interpretation of (14.8), (14.11) | narrative |
| p. 424 | Linear policies `y = G(k, z)`, `k′ = H(k, z)`; IRF sequence `y₀, y₁, y₂, …` | `irfK`, `irfY`, `irf_first_terms` (correction 3), `irf_closed` |
| p. 424 | Composition of linear functions is linear (IRF per unit shock) | `irf_K_linear`, `irf_linear` |
| p. 424 | IRF decays (model is stable) | `irf_bound`, `irf_decay` |
| p. 424, MIT-shock box | Sequence-space linearisation (Boppart–Krusell–Mitman) | not formalised: narrative |

## §14.4.3 Calibration (`Calibration`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 425–426 | Kydland–Prescott blueprint; limitations box | not formalised: methodology narrative |
| p. 426 | Perpetual inventory `kₜ = (1 − δ)kₜ₋₁ + iₜ` | `cal_perpetual_inventory`, `cal_perpetual_guess` |
| p. 426 | Solow residual `log zₜ = log yₜ − α log kₜ − (1 − α) log ℓₜ` | `cal_solow_residual` |
| p. 426 | `ρ_z = 0.95`, `σ_z = 0.007`, `δ = 0.025`, `α = 0.36`; "70%" | not formalised: estimates |
| pp. 426–427, box | Utilisation-adjusted capital `K* = uK` | `ext_util_solow` (in `Extensions`) |

## §14.4.4 The RBC model in action (`Calibration`, `Extensions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 427 | KPR preferences `(c v(1 − ℓ))^{1−σ}/(1 − σ)` consistent with balanced growth | `ext_kpr_form`, `ext_kpr_homog` (AKMM Ch 12 `AKMM.LaborSupply.kpr_homog`, `eq_12_37_if`) |
| p. 427 | Cobb–Douglas aggregator `c^{1−φ}(1 − ℓ)^φ` with `σ = 1` gives `(1 − φ)ln c + φ ln(1 − ℓ)` | `ext_cd_log` |
| p. 427 | Steady state: "real interest rate = growth rate of consumption times σ divided by β" | corrected `R = g^σ/β`: `ext_bgp_interest` (Miao `rb_u38_bgp` for `v = x^χ`); printed false: `ext_interest_printed_false` |
| p. 428 | `β = 0.99` is an annual 4% discount rate | `cal_discount_rate` |
| p. 428 | `ℓ = 1/3` from 8 of 24 hours | not formalised: arithmetic target |
| p. 428 | `φ/(1 − φ)·ℓ/(1 − ℓ) = (1 − α)y/c` | `cal_phi_identity`, `cal_mpl` |
| p. 428 | `φ = 0.6325` | `cal_steady_ratios`, `cal_phi_formula`, `calKY`, `calPhi`, `cal_phi_value` |
| pp. 428–431, Table 14.4, Figures 14.8–14.10 | Simulated moments; IRFs; sensitivity to `ρ`, Frisch, EIS | not formalised: simulations, figure claims (deferred) |
| p. 429, fn. 13 | Frisch elasticity 2 at `ℓ = 1/3` | `sm_frisch_two` |
| pp. 425, 431 | "roughly 70%" vs "nearly 80%" of output fluctuations | not formalised: quantitative claims from simulations (inconsistency noted, correction 6) |

## §14.5 Extensions (`Extensions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 432, §14.5.1 | Indivisible labour with lotteries: linear disutility of hours, infinite aggregate Frisch elasticity | Miao `Miao.NeoclassicalGrowth.rb_lottery` (log utility of (14.2): lottery utility `ln c − BN`); AKMM Ch 12 `AKMM.LaborSupply.il_lottery`, `il_frisch_infinite` |
| p. 432 | Micro vs macro Frisch estimates | not formalised: empirical |
| p. 433, §14.5.2 | `kₜ₊₁ = (1 − δ)kₜ + iₜ − Ψ(iₜ, kₜ)`, `Ψ = (ψ/2)(i/k − δ)²k` | `adjPsi` |
| p. 433 | Adjustment costs convex | `adj_convex_i`, `adj_jointly_convex` |
| p. 433 | Maintaining capital is costless | `adj_maintenance` |
| p. 433, fn. 15 | Homogeneous of degree 1 | `adj_homog`, `adj_Phi_homog` |
| p. 433 | Shadow price of installed capital `q = 1 + ψ(i/k − δ)` | corrected: `adj_dk_di`, `adj_shadow_price` (`q = 1/(1 − ψ(i/k − δ))`); printed false: `adj_q_printed_iff`, `adj_q_printed_false`; first-order agreement `adj_q_first_order`; printed exact with cost in the resource constraint `adj_shadow_price_resource` |
| p. 433 | Marginal `q` and investment (Hayashi) | `adj_hayashi` (Miao `proposition_14_3_1` with `Φ = i − Ψ`) |
| p. 433, §14.5.3 | `kₜ₊₁ = (1 − δ(uₜ))kₜ + iₜ`; amplification of TFP shocks | Miao `Miao.NeoclassicalGrowth.rx_cu_amplification` (with `δ(u) = δ₀u^{δ₁}`, `rx_dep_strictMonoOn`) |
| p. 433 | Solow residual must be adjusted for utilisation | `ext_util_solow` |
| p. 434, §14.5.4 | IST shocks `kₜ₊₁ = (1 − δ)kₜ + qₜiₜ` | `ext_ist_price` (shadow price `1/q`); Miao `rx_ist_price` |
| p. 434 | "IST shocks account for roughly 30%" | not formalised: empirical |
| p. 434 | `c + i + g = y`; CES `C = [θg^ϕ + (1 − θ)c^ϕ]^{1/ϕ}`: high elasticity: no effect; low: like a tax, raises hours | `ext_gov_perfect_subst`, `ext_gov_hours`, `ext_gov_hours_increasing` (static log–log economy; the CES limits are represented by perfect substitutes and by `g` outside utility) |

## §14.6 Business-cycle accounting (`BCA`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 435 | Efficiency wedge `Yₜ = zₜF(kₜ, ℓₜ)` | `bca_static_wedges`, `bca_static_unique` |
| p. 435 | Labour wedge: `(1 − τ^ℓ)zF₂ = U₂/U₁` | `bca_labour_foc` (from the household's problem), `bca_static_wedges`, `bca_static_unique` |
| p. 435 | Investment wedge Euler equation | `bca_investment_euler` (from the household's problem), `bca_investment_wedge` (backing out) |
| p. 435 | Government consumption wedge `c + i + g = Y` | `bca_static_wedges`, `bca_static_unique` |
| pp. 434–435 | Wedges are distortions from the planner's allocation | `bca_zero_wedges` |
| pp. 435–437, Figure 14.11, box | Interpretation; ML estimation; 70%/25% shares; jobless recoveries | not formalised: narrative, estimation, figure |
| p. 438, §14.6.1 | Frontiers | not formalised: narrative |

## Appendix 14.A (`Spectral`, `Gains`, `Herglotz`, `SpectralDensity`, `Cramer`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 863 | `s(ω) = (1/2π)Σγₖe^{−ikω}` | `specC` (on all of `ℝ`, needed on `[−π, π]`) |
| p. 863 | Inversion `∫_{−π}^{π}s(ω)e^{ikω}dω = γₖ` | `appx_inversion` (absolutely summable `γ`), `appx_orth`, `appx_spec_mul_exp`, `appx_norm_term`; proof errors corrected (correction 7) |
| p. 863, fn. 33 | Fourier transform `d_x(ω) = Σₖxₜe^{−ikω}` | typo (index `k` vs `t`), no theorem |
| p. 864 | `Var(Yₜ) = ∫_{−π}^{π}s(ω)dω` | `appx_variance` |
| p. 864 | Band variance `∫_{ω₁}^{ω₂}f(ω)dω` | corrected: `appx_spec_even`, `appx_band_variance` (correction 8) |
| p. 864 | Peaks of the spectrum and cycles; trends distort the spectrum | not formalised: informal remarks |
| p. 864 | Linear filter `Y^c = C(L)Y`; HP filter `C(L)` | `filtAutocov`, `transferFn`, `appx_filter_autocov` (finite filters) |
| p. 864 | `s_{Y^c} = G(ω)²s_Y(ω)` | `appx_filtered_spectrum`, `appx_transfer_normSq` (finite filters) |
| p. 864 | Gain `G(ω) = ∣C(e^{−iω})∣` | `appx_gain_diff`, `hpGain` |
| p. 865 | First difference: `G = √(2(1 − cos ω))`, attenuates frequency 0 | `appx_gain_diff_sq`, `appx_gain_diff`, `appx_gain_diff_mono`, `appx_exp_sub_exp`, `appx_diff_prod` |
| p. 865 | HP gain `4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)`; `≈ 0` near `ω = 0` | `appx_hp_gain_eq`, `appx_hp_gain_zero`, `appx_hp_gain_bounds`, `appx_hp_den_pos`, `appx_hp_gain_mono` |
| p. 865 | "As λ gets large there is less smoothing, and the spectrum of the filtered series converges to that of the original" | first half corrected: `appx_hp_trend_gain_anti` (correction 9); second half: `appx_hp_gain_limit`, `appx_cos_lt_one` |
| p. 865 | Ideal band-pass gain is 1 on the band, 0 otherwise | coefficients `appx_bandpass_coeff`, `appx_bandpass_coeff_zero` (not printed in the book) |
| p. 865 | HP and first difference remove low frequencies more than high | `appx_gain_diff_mono`, `appx_hp_gain_mono` |
| pp. 865–867, Figures 14.A.1–14.A.3, Tables 14.A.1–14.A.2 | Illustrations; Baxter–King and first-difference moments | not formalised: figures, data |
| pp. 412–413 (beyond the text) | Herglotz theorem: `γ` positive definite ⇔ `γ(h) = ∫e^{ihω}dF` for a finite measure `F`; `F` unique | `hergPosDef`, `herg_herglotz`, `herg_exists`, `herg_posDef_of_measure`, `herg_unique`, `herg_integral_eq_of_coeff`, `herg_conj`, `herg_symm_of_real`; Fejér construction `hergFejer`, `herg_fejer_eq`, `herg_fejer_nonneg`, `herg_fejer_coeff`, `herg_fejer_tendsto`, `herg_bound`, `herg_tendsto`, `hergLambda` (`Herglotz`) |
| pp. 412–413, p. 863 (beyond the text) | Weakly stationary processes have a spectral measure; with `Σ∣γ∣ < ∞` it has the continuous density `(1/2π)Σγₕe^{−ihω} ≥ 0` | `sdenStationary`, `sden_posDef`, `sden_spectral`, `sdenSeries`, `sdenMeasure`, `sden_coeff`, `sden_series_nonneg`, `sden_measure_coeff`, `sden_density` (`SpectralDensity`) |
| p. 863 (instance) | White noise and the AR(1): `γ(h) = ρ^{∣h∣}/(1 − ρ²)`, spectral density `1/(2π(1 − 2ρcos ω + ρ²))` | `sden_white_noise`, `sdenAR1`, `sden_ar1_summable`, `sden_ar1_series`, `sden_ar1_eq_normSq`, `sden_ar1_normSq_cos`, `sden_ar1_measure`, `sden_ar1_coeff`, `sden_ar1_posDef`; the process `sdenAR1Proc`, `sden_ar1_recursion`, `sden_ar1_stationary` |
| pp. 412–413 (beyond the text) | Spectral representation theorem (Cramér), Hilbert-space form: the isometry `L²(F) ≅ H_X`, `e^{itω} ↦ Xₜ`; `Z(A) = V(1_A)` with `⟪Z(A), Z(B)⟫ = F(A ∩ B)` | `cramExp`, `cram_inner_exp`, `cram_dense`, `cramIso`, `cram_iso_exp`, `cram_iso_inner`, `cram_iso_unique`, `cram_iso_range`, `cramZ`, `cram_Z_inner`, `cram_Z_norm_sq`, `cram_Z_orth`, `cram_Z_union`, `cram_Z_univ`, `cram_spectral_representation` (`Cramer`) |

## Shared lemmas

| Lean | Role |
| --- | --- |
| `hp_sum_ite_val`, `hpExt`, `hpSec`, `hp_ext_fin`, `hp_pen_nonneg`, `hp_fit_nonneg`, `hp_cross`, `hp_M_apply` | Index plumbing and identities for the HP matrices |
| `hpEx` | The vector `e₂` of the HP counterexample |
| `hpS1`, `hpS2`, `hpDet`, `hpOLSa`, `hpOLSb`, `hpOLS`, `hp_ols_affine`, `hp_continuous_pen`, `hp_continuous_fit`, `hp_cluster_le` | The OLS linear trend and the compactness argument |
