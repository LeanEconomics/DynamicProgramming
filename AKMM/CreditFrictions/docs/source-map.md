# Source map: AKMM Chapter 19

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 19, Credit market frictions (Vincenzo Quadrini), pp. 561–591, and
Appendix 19.A, pp. 877–878. Page references are the draft's running heads. Lean names are
relative to `AKMM.CreditFrictions` unless qualified. Departures from the book are in
[corrections](corrections.md).

## §19.1–19.2 Introduction; financial and real markets

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 561–565 | History; credit flows, credit standards, spreads and new debt over the cycle; three causal scenarios | not formalised: narrative and data |
| Figures 19.1–19.2 | Credit liabilities, credit standards, spreads, new debt | not formalised: figures (data) |

## §19.3 Modelling financial frictions (`MM`)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.1), p. 567 | The firm's problem `max −k + Σᵢpᵢ[F(zᵢ, k, ℓᵢ) − ℓᵢwᵢ + (1 − δ)k]` | `mmObj` |
| (19.2), p. 567 | The shareholders' problem with debt `b` and equity `e = k − b`; dividends `dᵢ` | `mmObjDebt`, `mm_obj_diff` |
| p. 567 | `Σᵢpᵢ R = 1` ⇒ `b` cancels and (19.2) reduces to (19.1) | `eq_19_2` |
| p. 567 | Financing does not affect real decisions; `b` versus `e` indeterminate | `mm_isMax_iff`, `mm_indeterminate`; converse (no maximiser when `ΣpᵢR ≠ 1`) `mm_no_max` |
| p. 567 | "The argument is very general …" (other instruments, incomplete markets) | not formalised: remark without derivation |
| pp. 567–569 | Exogenous and endogenous incompleteness; heterogeneity; the self-financing box | not formalised: verbal taxonomy |

## §19.4 The model (`MM`, `Dividend`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 571 | Stochastic discount factor `m_t = βᵗu₁(C_t, L_t)/u₁(C₀, L₀)` | used as `m′ = βu₁′/u₁` in `eq_19_20`, `eq_19_21`, `system_19_11_to_19_16` |
| p. 571 | Without further assumptions debt is indeterminate and the allocation is the NGM's | `proposition_19_1` (below) |
| Assumption 19.4.1, p. 572 | `R̃ = R/(1 + τ)` | used throughout; `hh_R_gt_Rt_iff` |
| Assumption 19.4.2, p. 572 | `b′/R̃ ≤ ξpk′` | constraint in `kkt_firm`, `firm_focs` |
| Footnote 6, p. 572 | Limited enforcement with recovery `ξpk′` gives the limit | `fn6_repayment_eq`, `fn6_full_iff`, `fn6_lender_iff`, `assumption_19_4_2_of_fn6` (via Obstfeld–Rogoff `DebtCeiling.repayment`, `repayment_eq_full_iff`) |
| pp. 573–574 | `p_t` exogenous; adjustment costs, Kiyotaki–Moore | not formalised: discussion |
| Assumption 19.4.3, p. 573–574 | `κ(d − φ)²`; `ϕ(d) = d + κ(d − φ)²` | `cfPhi`, `cfPhiD`, `div_hasDerivAt_phi`, `div_phi_sub`, `div_phiD_sub`, `div_phiD_le`, `div_lt_of_phi_lt` |
| p. 574 | "To pay `d` … the firm uses `ϕ(d)` units": the dividend that resources `X` pay | `cfDiv`, `div_radicand_phi`, `div_phi_div`, `div_phiD_div`, `div_div_phi`, `div_le_div_of_phi`, `div_continuous`, `div_hasDerivAt_div` |

## §19.4.1 Firms (`Firm`); Appendix 19.A.1

| Source | Claim | Lean |
| --- | --- | --- |
| (19.3), p. 574 | Firm's Bellman problem with budget and limit | `kktRes` (budget), optimality hypotheses of `kkt_firm`, `firm_focs` |
| App. 19.A.1, p. 877 | Lagrangian first-order conditions `1 = λϕ_d`, `F_ℓ = w`, `E m′Ω_k′ − λp + µλξp = 0`, `E m′Ω_b′ + λ/R̃ − µλ/R̃ = 0` (with `µ ≥ 0`, complementary slackness) | derived from optimality: `kkt_dir`, `kkt_deriv_nonpos`, `kkt_clm_apply`, `kkt_firm` |
| App. 19.A.1, p. 877 | Envelope conditions `Ω_k = λ[(1 − δ)p + F_k]`, `Ω_b = −λ` | `env_firm`, `appendix_19_A_1_envelope` (via Benveniste–Scheinkman `Miao.InfiniteHorizonDP.theorem_4_10`) |
| (19.4), p. 575 | `F₃ = w` | `kkt_firm`, `firm_focs` |
| (19.5), p. 575 | `E[m′(ϕ′(d)/ϕ′(d′))((1 − δ)p′ + F₂′)] = (1 − µξ)p` | `eq_19_5`, `firm_focs` |
| (19.6), p. 575 | `E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ` | `eq_19_6`, `firm_focs` |
| p. 575 | Interpretation (collateral premium, "more likely to bind") | not formalised: discussion (made precise in `gm_mu_pos_iff`) |

## §19.4.2 Households (`Household`); Appendix 19.A.2

| Source | Claim | Lean |
| --- | --- | --- |
| (19.7), p. 576 | Household's Bellman problem | optimality hypotheses of `hh_dir`, `household_focs` |
| p. 576 | `T = B′/R̃ − B′/R`; `R > R̃` since `τ > 0` | `hh_tax`, `hh_R_gt_Rt_iff` |
| App. 19.A.2, p. 877 | First-order conditions `u_c = γ`, `u_ℓ + γw = 0`, `βE V_b′ − γ/R = 0`, `βE V_a′ − γq = 0` | derived from optimality: `hh_dir`, `appendix_19_A_2_focs` |
| App. 19.A.2, p. 877 | Envelope `V_b = γ`, `V_a = γ(d + q)` | `hh_envelope` (via `theorem_4_10`) |
| (19.8)–(19.10), p. 576 | `u₁w = −u₂`; `1/R = E[βu₁′/u₁]`; `q = E[βu₁′/u₁(d′ + q′)]` | `eq_19_8`, `eq_19_9`, `eq_19_10`, `household_focs` |
| p. 576 | Households and firms share the discount factor | `household_focs` (with `m′ = βu₁′/u₁` in `firm_focs`) |
| pp. 574–576 | Budgets with `A = A′ = 1` give the resource constraint | `hh_resource` |

## §19.5 The two-period model (`TwoPeriod`, `System`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 576–577 | `u = ln(c − ℓ^ν)`, `F = zk^αℓ^{1−α}`; marginal utilities and products | `tp_hasDerivAt_u1`, `tp_hasDerivAt_u2`, `tp_mrs`, `tp_mpk`, `tp_mpl`, `tp_mpl_eq`, `tp_wage_bill` |
| p. 577 | Period-1 labour condition `(1 − α)z′(K′/L′)^α = νL′^{ν−1}` and closed form for `L′` | `tp_labour`, `tp_foc_iff`, `tpL`, `tp_L_eq` |
| p. 577 | Labour increases in `z′`, `K′` | `tp_L_strictMono_z`, `tp_L_strictMono_K` (need `α + ν > 1`; reversal `tp_L_strictAnti_z_of_neg`) |
| p. 577 | Closed form for `Y′`, increasing in `z′`, `K′` | `tpY`, `tp_Y_eq`, `tp_Y_strictMono_z`, `tp_Y_strictMono_K`, `tp_Y_pos` |
| p. 577 | `C′ = (1 − δ)K′ + Y′` (all resources consumed) | `sys_terminal_C` |
| p. 577 | `g(z′, K′) = C′ − L′^ν` increasing "at least in the relevant range" | `tpG`, `tp_L_pow_nu`, `tp_g_eq`, `tp_g_strictMono_z`, `tp_g_strictMono_K`, `tp_g_pos` |
| p. 578 | Closed form for `F_k(z′, K′, L′)` | `tpFk`, `tp_Fk_eq`, `tp_mpk_eq`, `tp_Fk_strictMono_z`, `tp_Fk_strictAnti_K`, `tp_Fk_pos` |
| (19.11)–(19.16), pp. 578–579 | The period-0 system | `system_19_11_to_19_16` |
| p. 578 | "This would be the case if initial debt `B` is sufficiently large" (binding) | not formalised: heuristic, no precise claim |
| p. 579 | With a slack limit replace (19.12) by `µ = 0` | `property_19_5_4`, `property_19_5_1_slack` |

## §19.5.1–19.5.4 Properties 19.5.1–19.5.5 (`System`, `Statics`)

| Source | Claim | Lean |
| --- | --- | --- |
| Property 19.5.1, p. 579 | Investment and output rise with a persistent productivity rise | `property_19_5_1` (binding), `property_19_5_1_slack`, `cs_return`, `cs_mu`; output via `tp_Y_strictMono_z`, `tp_Y_strictMono_K` |
| Property 19.5.1, pp. 579–580 | The responses are smaller when the limit binds; dividends must fall | `property_19_5_1_dampening`, `cs_ratio_lt`, `cs_div_falls` |
| p. 580 | Net worth `pK − B` rises more than proportionally in `p` iff `B > 0` | `sys_networth_elasticity`, `property_19_5_2_networth` |
| p. 580 | Rearranged budget `K′ = [(1 − δ)K + (αF − B − D − κ(D − φ)²)/p]/(1 − ξ)` | `sys_Kprime_eq` |
| Property 19.5.2, p. 580 | Higher `p` raises `K′` (binding limit, `B > 0`), hence `Y′`, `L′` | `sys_hasDerivAt_Kprime`, `property_19_5_2` (needs `αF − B − D − κ(D − φ)² < 0`; `sys_B_pos_not_sufficient`); `L′`, `Y′` via `tp_L_strictMono_K`, `tp_Y_strictMono_K` |
| p. 581 | The multiplier `1/(1 − ξ)` increases with `ξ` | `sys_multiplier_mono` |
| Property 19.5.3, pp. 581–582 | Lower `ξ` lowers `K′`, hence `Y′`, `L′` | `property_19_5_3`, `property_19_5_3_output`; general equilibrium with `κ = 0`: `property_19_5_3_ge` |
| p. 582 | `ξ` does not affect current employment | `tpL` depends only on `(z, K)` (definitional) |
| Property 19.5.4, p. 582 | Slack limit: a rise in `ξ` has no effect | `property_19_5_4` (equilibrium conditions), `sys_slack_global`, `property_19_5_4_opt` (optimisation form) |
| Property 19.5.5, p. 583 | Slack limit: a large fall in `ξ` reduces investment, output, employment | `property_19_5_5`, `property_19_5_5_output` |
| p. 583 | Asymmetry; which initial states are relevant | not formalised: discussion; the invariant distribution is a simulation result |

## §19.5.5 Working capital (`TwoPeriod`, `System`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 583–584 | 60% labour, < 10% capital contributions to output volatility (1950–2019) | not formalised: data |
| (19.17), p. 584 | `wℓ + b′/R ≤ ξpk′` | Lagrangian hypotheses of `eq_19_18`, `sys_wc_19_6_printed` |
| (19.18), p. 584 | `F₃ = (1 + µ)w` | `eq_19_18` |
| p. 584 | (19.5) and (19.6) "the same as before" | `sys_wc_19_5`; (19.6) only with `b′/R̃`: `sys_wc_19_6_tilde`, `sys_wc_19_6_printed`, `sys_wc_19_6_printed_ne` |
| pp. 584–585 | `(1 − α)zK^αL^{−α} = (1 + µ)νL^{ν−1}` and the closed form for `L` | `tp_wc_labour`, `tp_foc_iff` |
| Property 19.5.6, p. 584 | Employment declines with `µ` | `property_19_5_6` |
| p. 585 | Intermediate inputs | not formalised: remark |

## §19.6 General model (`General`)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.19), p. 585 | `F₃ = −u₂/u₁` | `eq_19_19` |
| (19.20), p. 585 | Capital condition with `m′ = βu₁′/u₁` | `eq_19_20` |
| (19.21), p. 586 | Firm's bond condition with `R̃ = R/(1 + τ)` | `eq_19_21` |
| (19.22), p. 586 | Household's bond condition | `eq_19_22` |
| p. 586 | `κ = 0` ⇒ `(1 − µ)(1 + τ) = 1`; `τ > 0` sufficient for `µ > 0` | `gm_kappa_zero`, `gm_binding_iff` |
| p. 586 | `κ > 0`: if `E[ϕ′(D)/ϕ′(D′)]` is large enough, `µ > 0` is impossible | `gm_mu_pos_iff`, `gm_not_binding` |
| p. 586 | "… when, in expectation, the term `u₁(C′, L′)/u₁(C, L)` is higher" | `gm_mu_scale`, `gm_mu_det` (the level alone does not matter; correction 9) |
| Footnote 7, p. 586 | Relaxing 19.4.2 requires relaxing 19.4.1 | not formalised: remark (`mm_no_max` is the unbounded-debt case of the static problem) |
| Proposition 19.1, p. 586 | `τ = κ = 0` ⇒ `µ = 0`, the NGM conditions, same allocation | `proposition_19_1` (Miao `RMHHFOC`, `RMFirmFOC`, `RMClear`), `proposition_19_1_planner` (Miao `rm_ce_planner`) |
| Proposition 19.1, p. 586 | Debt indeterminate | `proposition_19_1_debt`, `proposition_19_1_indeterminate` |
| Box, p. 587 | Gain `∆(1 − E m′R)`; zero when `τ = κ = 0` | `mm_box_gain`, `mm_box_gain_zero_iff`, `gm_box` |

## §19.7 Numerical analysis

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 587–588, Table 19.1 | Calibration (`β`, `ν`, `α`, `τ`, `κ`, Markov chains for `z` and `ξ`) | not formalised: calibrated numbers |
| p. 588 | Projection method on `(K, B/K)` | not formalised: numerical method |
| pp. 589–591, Figures 19.3–19.4 | Responses to TFP and credit shocks, asymmetric credit cycle, `µ` and spreads | not formalised: simulation, figure claims, deferred |
| p. 591 | Comparison with Reinhart–Rogoff and Schularick–Taylor | not formalised: empirical discussion |
