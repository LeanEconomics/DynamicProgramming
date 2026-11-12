# Source map: AKMM Chapter 24

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 24, Sovereign debt and default risk (J. C. Hatchondo and L. Martinez),
pp. 729–748, and Appendix 24.A, pp. 897–908. Lean names are relative to `AKMM.SovereignDefault`.
Departures are numbered in [corrections](corrections.md).

## §24.3 The two-period model (`TwoPeriod`)

| Source | Claim | Lean |
| --- | --- | --- |
| (24.3), p. 740 | Consumption under repayment and default | `cons2Of`, `eq_24_3` |
| (24.4), p. 740 | Default iff `Y₂ < B₂/φ`; optimal; ties repaid | `defaultRule`, `tp_defaultRule_eq`, `cons2`, `eq_24_4`, `tp_defaultRule_optimal`, `tp_repay_at_indifference`, `tp_defaultRule_mem` |
| p. 740 | `Ĉ₂ = Y₂ − min(φY₂, B₂) = max(Y₂ − B₂, Y₂ − φY₂)`; continuous, nonincreasing in `B₂`; bounds | `tp_cons2_eq`, `tp_cons2_eq_max`, `tp_cons2_continuous`, `tp_cons2_antitone`, `tp_cons2_bounds` |
| (24.5), p. 741 | `q₁ = E[1 − D̂₂] = Pr(Y₂ ≥ B₂/φ) = 1 − F(B₂/φ)` (corrected, item 1); zero profit | `price`, `eq_24_5`, `tp_zero_profit`, `tp_price_eq_measure`, `tp_measureReal_Ici`, `tp_one_sub_defaultRule`, `eq_24_5_printed_false`, `tp_uniform_admissible` |
| p. 741 | The price decreases with debt; `q₁ ∈ [0,1]`, `q₁(0) = 1`, `q₁ → 0`, continuous; `dq₁/dB₂ = −f/φ` | `tp_price_antitone`, `tp_price_strictAntiOn`, `tp_price_mem_Icc`, `tp_price_zero`, `tp_price_tendsto_zero`, `tp_price_continuous`, `tp_price_hasDerivAt` |
| fn 8, p. 741 | Income-contingent debt eliminates defaults and expands borrowing opportunities | `fn_8`, `tp_contingent_no_default`, `tp_contingent_revenue` |
| fn 14, p. 745 | FOSD in `Y₁` makes `q₁(B₂, Y₁)` increasing in `Y₁` | `fn_14` |

## §24.3 Optimal borrowing (`TwoPeriodOptimum`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 741 | The period-1 problem `max_{B₂≥0} u(C₁) + βE u(Ĉ₂)`, `C₁ = B₂q₁(B₂)` | `tp_objective` |
| p. 741 | An optimal `B̂₂` exists (bounded revenue `B₂q₁ → 0`, continuity) (item D1) | `tp_exists_optimal`, `tp_revenue_tendsto_zero`, `tp_cons2_continuous_Y` |
| p. 741 | Marginal revenue `q₁ + B₂dq₁/dB₂ ≥ 0` at the optimum (increasing side of the Laffer curve; imports Obstfeld–Rogoff's `writedown_raises_value`) | `tp_laffer_side` |
| p. 741 | `d/dB₂ E u(Ĉ₂) = −E[u′(Ĉ₂)(1 − D̂₂)]`: consumption in default does not depend on `B₂`, the boundary term vanishes | `tp_hasDerivAt_expectedUtility`, `tp_cons2_lipschitz` |
| (24.6), p. 741 | The Euler equation with default | `eq_24_6` |

## §24.4.1, App. 24.A.2: long-term debt (`LongTermDebt`)

| Source | Claim | Lean |
| --- | --- | --- |
| (24.2), p. 731 | The present-value haircut; in `[0, 1]` | `ltd_haircut`, `eq_24_2` |
| (24.7), p. 742 | `B_{t+1} = (1 − δ)B_t + I_t`, closed form | `ltd_stock`, `eq_24_7` |
| p. 742 | `B_t` suffices to predict future payments | `ltd_payment`, `ltd_coupon_due`, `ltd_payments_sufficient`, `ltd_same_stock_same_payments` |
| (24.8), p. 743 | Budget `C + δB = Y + Iq`, hence the constraint of (24.11) | `eq_24_8` |
| p. 903 | PV of debt `δB/(δ + r)` (timing note, departure D3) | `ltd_hasSum_coupons`, `ltd_pv_bond`, `ltd_pv_stock_timing` |
| p. 903 | Yield `q = Σ δ(1 − δ)^{j−1}/(1 + i)^j = δ/(δ + i)` | `ltd_yield`, `ltd_yield_iff` |
| p. 902 | Macaulay duration `(1 + i)/(δ + i)` | `ltd_coupon`, `ltd_duration` |
| p. 903 | Annualised spread `((1 + i)/(1 + r))⁴ − 1` | `ltd_spread`, `ltd_spread_pos_iff` |

## §24.4.2, App. 24.A.1: the bond price (`BondPrice`)

| Source | Claim | Lean |
| --- | --- | --- |
| (24.A.6), p. 900 | Price operator with default and borrowing probabilities; admissibility | `bp_op`, `BPAdmissible`, `bp_admissible_example` |
| (24.12), (24.A.2), (24.A.6) | The price map is a contraction of modulus `(1 − δ)/(1 + r)` | `bp_op_sub_le`, `bp_contracting`, `bp_op_mapsTo` |
| (24.A.6), p. 900 | Existence, uniqueness, `q ∈ [0, δ/(δ + r)]` | `eq_24_A_6` |
| (24.A.2), p. 897 | The price iteration converges from any initial guess (rules fixed) | `eq_24_A_2` |
| (24.12), p. 744 | Zero-profit price given `D̂`, `B̂`: exists, unique, bounded (finite grids, departure D4) | `bp_op12`, `bp_op12_eq`, `eq_24_12` |
| p. 903 | Without default the price is risk free, `δ/(δ + r)` | `bp_riskfree` |
| p. 748 | One-period debt: the price depends only on next-period default; no borrowing time inconsistency | `bp_one_period`, `bp_one_period_independent` |
| p. 748 | Long-term debt: future borrowing moves today's price | `bp_long_term_depends_on_borrowing` |

## §24.4.2, App. 24.A.1: the Bellman equations (`Bellman`)

| Source | Claim | Lean |
| --- | --- | --- |
| §24.4.1, pp. 742–743 | Environment on finite grids (departure D4); an example | `SDModel`, `sd_example`, `sd_example_solution` |
| (24.10), (24.11), p. 744 | Default value, repayment value, repayment consumption | `SDModel.defaultValue`, `SDModel.repayValue`, `SDModel.cons` |
| (24.9)–(24.11) | The problem as a Sargent–Stachurski RDP satisfying Blackwell's conditions | `SDModel.rdp`, `SDModel.sd_isContracting`, `SDModel.sd_T_good`, `SDModel.sd_T_excluded` |
| (24.9)–(24.11), pp. 743–744 | For every `q`, a unique solution `(V, V^D)`, `V^R` by (24.11) | `SDModel.eq_24_9_to_24_11` |
| (24.A.1), p. 897 | Value function iteration converges (given `q`) | `SDModel.eq_24_A_1` |
| p. 744 | `V^R` and `V` nonincreasing in debt, `V^D` independent of debt | `SDModel.sd_VR_antitone`, `SDModel.sd_V_antitone` |
| p. 744, App. 24.A.3 p. 904 | Default sets grow (repayment sets shrink) with debt | `SDModel.sd_default_set_mono`, `SDModel.sd_repay_set_antitone` |
| App. 24.A.3, p. 904 | "As is standard ... this threshold is unique": default iff `Y < Y*(B)` | not formalised: the text gives no argument and none follows from (24.9)–(24.12) without monotonicity of `V^R − V^D` in `Y` (cited) |

## §24.4.3–24.4.4, App. 24.A.1: equilibrium (`MarkovPerfect`)

| Source | Claim | Lean |
| --- | --- | --- |
| §24.4.3, pp. 744–745 | Markov perfect equilibrium (a)–(c); an instance | `IsMPE`, `mpe_example` |
| §24.4.3; (24.A.1)–(24.A.2) | The MPE as a fixed point of `q ↦ T_{D̂(q), B̂(q)} q` | `SDModel.bellmanSol`, `SDModel.inducedDefault`, `SDModel.inducedBorrow`, `SDModel.inducedBorrow_spec`, `SDModel.mpeMap`, `mpe_iff_fixedPt`, `mpe_values_eq` |
| (24.12) in equilibrium | `q ∈ [0, δ/(δ + r)]` | `mpe_price_mem` |
| p. 744, App. 24.A.3 | In equilibrium `V` falls and the default rule rises with debt | `mpe_V_antitone`, `mpe_default_mono` |
| p. 901 | Existence and uniqueness of the MPE for `δ = 1` (Auclert–Rognlie 2016; Aguiar–Amador 2019), Blackwell recast; multiplicity for `δ < 1` (Aguiar–Amador 2020) | proved beyond the text (decision 5) in a continuous-debt setting, departure D10: see the tables `UniqueEquilibrium` and `Multiplicity` below; on finite grids uniqueness fails even for `δ = 1` (correction 9) |
| §24.4.3 | Reuse check: Miao's `DGStochGame` MPE (fixed players, simultaneous actions, exogenous payoffs) does not match the book's equilibrium, whose price is set by lenders' zero profit given the sovereign's future rules | the MPE is defined directly (`IsMPE`); the declared `DynamicGames` dependency is unused |
| (24.13), p. 748 | Borrowing first-order condition (corrected sign, item 2); sign of marginal revenue | `eq_24_13`, `eq_24_13_printed_false`, `eq_24_13_printed_counterexample`, `eq_24_13_sign` |
| (24.A.3), p. 898 | Total derivative of the equilibrium price in income | `eq_24_A_3` |

## App. 24.A.1, Method 3: extreme-value shocks (`ExtremeValue`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 900 | Gumbel shocks; choice probability by conditioning on the chosen shock | `ev_gumbelCDF`, `ev_gumbelPDF`, `ev_choiceProb` |
| p. 900 | `∫ e^{−x} exp(−c e^{−x}) dx = 1/c` | `ev_hasDerivAt`, `ev_density_continuous`, `ev_integrable`, `ev_integral` |
| p. 900 | Choice probabilities are logit, positive, sum to one, continuous in values | `ev_logit`, `ev_logit_pos`, `ev_logit_sum`, `ev_logit_continuous` |
| p. 900 | Default probability `D` and borrowing probabilities `B(· \| ·)` given repayment | `ev_conditional_borrow` |
| (24.A.6), p. 900 | The price with logit probabilities exists, is unique, bounded | `eq_24_A_6_logit` |
| (24.A.5), p. 900 | The perturbed Bellman equations | not formalised separately: their choice probabilities are `ev_logit`; the perturbed fixed point is the extreme-value analogue of `eq_24_9_to_24_11` |

## App. 24.A.2–24.A.3: calibration formulas (`Calibration`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 901 | CRRA utility; `u′ = c^{−σ} > 0` decreasing (meets the hypotheses of `eq_24_6`) | `cal_crra`, `cal_crra_hasDerivAt`, `cal_crra_deriv_pos`, `cal_crra_deriv_antitone` |
| (24.A.7), p. 901 | `φ(Y) = max{Y[λ₀Y + λ₁(Y − E Y)], 0}` ≥ 0; loss fraction; `λ₀` the fraction at the mean | `cal_phi`, `cal_phi_nonneg`, `cal_phi_div`, `cal_phi_at_mean` |
| p. 743 | `φ(Y)/Y` increases in `Y` (needs `λ₀ + λ₁ ≥ 0`, departure D5) | `cal_phi_div_monotone` |
| pp. 904–905 | `λ₀` raises the cost everywhere; `λ₁` lowers it below mean income, raises it above | `cal_phi_mono_lam0`, `cal_phi_lam1` |
| p. 742 | AR(1) stationary mean and variance | `cal_ar1_variance` |
| p. 901, Table 24.A.1 | `μ` chosen so that `E Y = 1` (corrected, item 3) | `cal_lognormal_mean`, `cal_mean_one_iff`, `cal_table_mu_printed_false` |
| fn 44, p. 903 | Iso-moment curve by the implicit function theorem, slope `−X₀/X₁` (imports Obstfeld–Rogoff's `toSpanSingleton_eq_smul`, `smul_one_isInvertible`) | `fn_44`, `fn_44_exists` |
| Table 24.A.1, pp. 901–903 | Parameter values; `λ₀, λ₁` matched to debt and spread targets; uniqueness of the matching pair (Fig. 24.A.2) | not formalised: calibration and simulation (figure claim, deferred) |

## Not formalised

| Source | Item | Reason |
| --- | --- | --- |
| §24.1, pp. 729–730 | Introduction | narrative |
| (24.1), pp. 730–731 | The small-open-economy budget of the cited business-cycle models (timing corrected, item 4) | empirical sketch of cited models |
| §24.2, pp. 730–738 | Consumption volatility (Table 23.1), default facts, Figure 24.1, sovereign spreads (Table 24.1), panel regression (Table 24.2), COVID spreads (Figure 24.2), debt intolerance (Figures 24.3–24.4), original sin, remedies and fiscal rules (Figure 24.5), the low-income-country box | data, facts, figures and empirical discussion |
| fn 7, p. 740 | Costs of default; Bulow–Rogoff (1989) | cited |
| §24.4.4, pp. 745–747 | Table 24.3 (business-cycle moments), Figures 24.6–24.7, "the bond price increases with income" in the quantitative model | simulation; figure claim, deferred (the two-period analogue is `fn_14`) |
| pp. 747–748 | Welfare and commitment results (Mateos-Planas et al. 2025; Hatchondo et al. 2022; Bolton–Jeanne 2009), `β(1 + r) < 1` in calibrations | cited quantitative results |
| fn 11, p. 744 | No buybacks (Aguiar, Amador, Hopenhayn and Werning 2019) | cited |
| App. 24.A.1, pp. 898–900 | Grid pathologies, interpolation and quadrature (Method 1), the continuous i.i.d. shock of Chatterjee–Eyigungor (Method 2, (24.A.4)), Gordon–Qiu | computational methods beyond the logit result |
| App. 24.A.1, p. 901 | The limit of the finite-horizon game ("By using as initial guesses the equilibrium functions in the last period (T) of a finite-horizon economy, we are finding the equilibrium that is the limit of the finite horizon game as T → ∞") | beyond the text, not formalised: convergence of the finite-horizon equilibria needs a joint contraction on values and debt capacities (both the continuation values and the default value change with the horizon), which the capacity map of `ue_cutoff_le` (prices from a fixed capacity vector, values solved to infinite horizon) does not give |
| App. 24.A.1, p. 901 | Aguiar–Amador (2020) multiplicity with a continuum of debt levels (debt dilution) | beyond the text, not formalised; grid instances `mu_grid_long_term_two_mpe` |
| App. 24.A.2–24.A.3, pp. 901–908 | Parameter values, the matching of `(λ₀, λ₁)` to the debt and spread targets, Figures 24.A.1–24.A.4, uniqueness of the matching pair, the threshold `Y*(B)` (departure D9) | calibration, simulation; figure claims, deferred |
| fn 42–43, 46–47 | Duration data; Aiyagari (1994); the role of impatience | data, cited |

## App. 24.A.1, Method 3: the product of Gumbel laws (`GumbelProduct`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 900 | The standard Gumbel law: density, c.d.f., probability measure | `ev_gumbel`, `gp_pdf_continuous`, `gp_pdf_integrable`, `gp_pdf_nonneg`, `gp_hasDerivAt`, `gp_integral_Iic`, `gp_measure_Iic`, `gp_isProbabilityMeasure` |
| p. 900 | With i.i.d. shocks the probability of choosing alternative `i` is logit (departure D7) | `ev_logit_of_gumbel`, `ev_choiceProb_eq_gumbel` |

## App. 24.A.1, p. 901: existence and uniqueness with one-period debt (`UniqueEquilibrium`, beyond the text)

| Source | Claim | Lean |
| --- | --- | --- |
| §24.4.1–24.4.3 at `δ = 1`, `ψ = 0`, continuous debt (departure D10) | The economy and the Markov perfect equilibrium (a)–(c) with (24.9)–(24.12) | `UEModel`, `UEModel.price`, `UEModel.obj`, `UEModel.defaultRHS`, `IsOneMPE` |
| (24.10) at `ψ = 0` | The default value exists and is unique | `UEModel.ue_VD_exists`, `UEModel.ue_VD_unique` |
| (24.9), (24.11) given `q` | Blackwell's conditions on bounded functions of an arbitrary state space give a bounded solution | `ue_fixed_point`, `UEModel.ue_sol_exists`, `UEModel.VRsup`, `UEModel.bell`, `ue_sum_le`, `ue_le_sum`, `ue_sum_mono`, `ue_sum_add` |
| (24.12) at `δ = 1` | Price bounds, risk-free price, monotonicity in repayment | `UEModel.ue_price_mem`, `UEModel.ue_price_one`, `UEModel.ue_price_mono` |
| p. 901 (Auclert–Rognlie) | Revenue bound and the replication argument | `UEModel.ue_revenue`, `UEModel.ue_replication` |
| p. 901 | `V^R` nonincreasing and uniformly continuous in debt; debt `B ≤ 0` always repaid | `UEModel.ue_VR_antitone`, `UEModel.ue_modulus`, `UEModel.ue_repay_nonpos`, `UEModel.ue_mpe_sup` |
| p. 901 | **Uniqueness** of the MPE (values, default rule, prices) | `UEModel.ue_mpe_VR_le`, `UEModel.ue_mpe_unique` |
| p. 901 (Aguiar–Amador's Blackwell recast) | The debt-capacity map is a contraction of modulus `1/(1 + r)`; its fixed point | `ue_thr`, `UEModel.cutoff`, `UEModel.ue_thr_mem`, `UEModel.ue_thr_nonpos`, `UEModel.ue_cutoff_le`, `UEModel.ue_capacity_fixed` |
| p. 901 | Optimal borrowing exists (upper semicontinuity, satiation) | `UEModel.ue_attain`, `UEModel.ue_u_le`, `UEModel.ue_obj_le`, `UEModel.ue_VRsup_bdd`, `UEModel.ue_VRsup_le`, `UEModel.ue_VRsup_sup`, `UEModel.ue_VRsup_ub` |
| p. 901 | **Existence** of the MPE; existence and uniqueness | `UEModel.ue_mpe_exists`, `UEModel.ue_mpe_exists_unique` |
| p. 901 | A concrete economy meeting every hypothesis, with its unique MPE | `ue_example`, `ue_example_hyp`, `ue_example_exists_unique` |

## App. 24.A.1, p. 901: multiple equilibria on a finite grid (`Multiplicity`, beyond the text)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 901 (Aguiar–Amador 2020) | Multiple MPE with long-term debt: an explicit economy (`δ = 1/2`) with two MPE, both verified | `mu_econ`, `mu_sup_bool`, `mu_grid_long_term_two_mpe` |
| p. 901, correction 9 | On a finite grid there are two MPE even with one-period debt (`δ = 1`) | `mu_grid_one_period_two_mpe` |
