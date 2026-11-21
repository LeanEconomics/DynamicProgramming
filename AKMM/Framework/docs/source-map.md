# Source map: AKMM Chapter 2

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 2, A framework for macroeconomics, pp. 43–69. Page references are the
draft's running heads. Lean names are relative to `AKMM.Framework`. Departures from the book are
in [corrections](corrections.md).

Reused from dependencies: Miao's `NeoclassicalGrowth` (`rm_euler_homogeneous`,
`rm_partial2_homog_zero`, `rmKprU`, `rmKprUc`, `rmKprUn`, `rm_kpr_hasDerivAt_c`,
`rm_kpr_hasDerivAt_n`, `rm_kpr_uc_scale`, `rm_kpr_mrs_scale`) and EconomicGrowth's
`DiscreteTime` (`Solow1956.DiscreteTime.next`, `steady`, `Params`, `path`, `IsPath`,
`existsUnique_steadyState`, `steady_spec`, `steady_state_equilibrium`, `IsPath.orbit`,
`output_consumption_limit`; the technology class `Solow1956.Neoclassical.Technology`).

## Introduction and §2.1.1–2.1.3 (pp. 43–50)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 43 | Purpose of the chapter | not formalised: narrative |
| §2.1.1, p. 44, Fig. 2.1, fn. 2 | Output per capita grows steadily (1.86% a year) | not formalised: data, figure claim |
| §2.1.2, pp. 44–48, Figs. 2.2–2.6 | Capital–output ratio ≈ 3, wealth–output ratio, return on capital, hours, wages | not formalised: data, figure claims |
| §2.1.3, pp. 48–49 | Solow's neoclassical interpretation | not formalised: narrative |

## Box: the existence of an aggregate production function (pp. 49–50) — `Aggregation`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 50 | With a given relative price `p`, competitive allocation maximises the value of output; the mapping depends on `p` in general | not formalised: narrative (no precise general claim) |
| fn. a, p. 50 | Proportional isoquants (`x₂ = aG`): a concave CRS `G` is superadditive | `aggPosQuadrant`, `agg_superadditive` |
| fn. a, p. 50 | The production possibility frontier is linear, `x₁ + x₂/a ≤ G(K, L)`, every point attained | `agg_frontier_bound`, `agg_frontier_attained` |
| fn. a, p. 50 | "A relative price `p` is implied from the production technologies alone": `p = a` | `agg_price_implied` |
| fn. a, p. 50 | "It is possible to construct the mapping": output `x₁ + x₂/a = G(K, L)` at every value-maximising allocation, independent of prices | `agg_aggregate_production` |
| p. 50 | Cambridge capital controversy | not formalised: narrative |

## §2.1.4 Growth accounting (pp. 50–52) — `GrowthAccounting`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 50 | CRS implies zero pure profits under perfect competition | `eq_2_1` (second and third conjuncts), Miao's `rm_euler_homogeneous` |
| pp. 50–51 | With CRS, `y_t = F_t(k_t, ℓ_t)` in per-capita terms | `ga_per_capita` |
| p. 51 | `dy = F_t dt + F_k dk + F_ℓ dℓ` along differentiable paths | `gaPartials`, `ga_partials_apply`, `ga_hasFDerivAt_coords`, `eq_2_1` (first conjunct) |
| p. 51 | `r`, `w` equal the marginal products (first-order conditions of `max F − rk − wℓ`) | `ga_profit_foc` |
| p. 51 | Labour's share `1 − α = wℓ/y`, capital's share `α = rk/y` | `eq_2_1` (third conjunct) |
| (2.1), p. 51 | `dy/y = (∂F/∂t)dt/F + α dk/k + (1 − α) dℓ/ℓ` | `ga_growth_identity`, `eq_2_1` |
| (2.2), p. 52 | Hicks-neutral `F = zG(k, ℓ)`: `dy/y = dz/z + α dk/k + (1 − α) dℓ/ℓ` | `eq_2_2` |
| fn. 8, p. 52 | `z` multiplies both inputs, by homogeneity of degree 1 | `ga_hicks_neutral_common_factor` |
| p. 52 | Labour-augmenting `F = G(k, zℓ)`: `(∂F/∂t)dt = (∂F/∂ℓ)ℓ dz`, `∂F/∂ℓ = w/z`, `wℓ = (1 − α)F` | `ga_labour_augmenting_partials`, `ga_eq_2_3_partial_misreading` (see corrections, item 3) |
| (2.3), p. 52 | `dy/y = (1 − α)dz/z + α dk/k + (1 − α) dℓ/ℓ` | `eq_2_3` |
| fn. 9, p. 52 | One could define capital-augmenting technology similarly | not formalised: remark, no claim |
| p. 52 | Discrete-time shares (averages over `t`, `t + 1`) in practice | not formalised: measurement practice |
| pp. 52–53, Figs. 2.7–2.10, fn. 10 | Labour productivity and TFP growth ≈ 2% | not formalised: data, figure claims |

## §2.1.5 The dynamic system (pp. 52–57) — `DynamicSystem`

| Source | Claim | Lean |
| --- | --- | --- |
| (2.4), p. 53 | `k_{t+1} = (1 − δ)k_t + i_t`, rewritten as `(k_{t+1}/y_{t+1})(1 + γ_t) = (1 − δ)k_t/y_t + i_t/y_t` | `eq_2_4_ratio_form` |
| p. 53 | Capital, investment, output growing at a common `γ` with `i/y = s`: `k/y = s/(γ + δ)` | `DynBalancedPath`, `dyn_investment_growth`, `dyn_capital_output_ratio` |
| p. 53 | "This equation is consistent with a capital–output ratio that does not change over time" | `dyn_balanced_of_initial_ratio`, `dyn_balancedPath_example` |
| fn. 11, p. 53 | Human-capital accumulation | not formalised: deferred by the book to Ch. 13 |
| pp. 54–55, Fig. 2.11, fn. 12 | The investment rate is roughly constant; national accounts | not formalised: data, figure claim |
| p. 55, fn. 13 | `δ = 0.08`, `γ = 0.02`, `s = 0.3` give `K/Y ≈ 3` | not formalised: calibrated numbers |
| p. 55 | `k_{t+1} = sF(k_t, (1 + γ)^t ℓ) + (1 − δ)k_t` | hypothesis `hsys` of `dyn_detrend_step`, `dyn_detrended_path` |
| p. 56 | Uzawa (1961): balanced growth requires labour-augmenting technical change | not formalised: cited, proved in the book's Appendix 3.A |
| p. 56 | Detrended system `(1 + γ)k̃_{t+1} = sF(k̃_t, ℓ) + (1 − δ)k̃_t`, `k̃_t = k_t/(1 + γ)^t` | `dyn_detrend_step`, `dyn_detrended_path` (as EconomicGrowth's `next`, `path`) |
| p. 56 | A constant solution `k̄` exists and is unique ("under some minimal conditions") | `dyn_steady_iff`, `dyn_params`, `dyn_steady_existsUnique` |
| p. 56 | From `k̃_0 = k̄`: `k`, `i`, `y` grow at `γ`, `y_t = (1 + γ)^t F(k̄, ℓ)` | `dyn_balanced_growth_from_steady` |
| pp. 56–57 | Convergence from any initial capital (proved in Ch. 3); `K/Y` returns to its balanced value | `dyn_convergence` |
| p. 57 | Saving and hours are mechanical so far | not formalised: narrative |

## §2.1.6 Input shares (pp. 57–59) — `GrowthAccounting`, `LabourSupply`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 57 | On a balanced path `rk` and `wℓ` grow with output, so the shares are constant | `ls_bk_production` (with `ν = 0`: hours constant, labour share constant) |
| pp. 57–59, Figs. 2.12–2.14 | Factor shares roughly constant; recent decline of the labour share | not formalised: data, figure claims |
| p. 58 | Cobb–Douglas `F = Ak^α ℓ^{1−α}`: `F_k k/F = α` for all `(k, ℓ)` | `ga_cobbDouglas_hasDerivAt_k`, `ga_cobbDouglas_share`, `ga_cobbDouglas_crs` |

## §2.1.7 Summing up (p. 59)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 59 | Seven stylised facts and their neoclassical interpretation | not formalised: stylised facts |

## §2.1.8 Rationalising saving and labour-supply choices (pp. 59–65) — `Preferences`, `LabourSupply`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 60–61, fns. 15–17 | Time, people, dynasties, heterogeneous agents | not formalised: modelling discussion |
| p. 61 | Time-additive `u(c_t) + βu(c_{t+1})`, `u` increasing and strictly concave | assumptions, not formalised as claims |
| fn. 18, p. 61 | Exercise: both goods are normal | not formalised: exercise stated without a model of income |
| p. 62 | Euler equation `u′(c_t)/(βu′(c_{t+1})) = R_{t+1}`, `u′(c_t) = βu′(c_{t+1})R_{t+1}` | `pref_euler_equation` |
| p. 63 | "If" part: for power `u`, `u′(c)/u′((1 + γ)c)` is constant and contains the growth rate | `pref_crra_mu_ratio` |
| p. 63 | Constant `R` gives a constant consumption growth rate, depending on `R`, `β`, curvature but not wealth | `pref_crra_euler_iff`, `pref_crra_constant_growth` |
| (2.5), p. 63 | `u(c) = (c^{1−σ} − 1)/(1 − σ)`, `σ > 0`, `σ ≠ 1` | `prefCrra`, `eq_2_5_hasDerivAt` |
| p. 63, fn. 19 | `σ → 1` gives `log c` (l'Hôpital) | `pref_footnote_19_derivatives`, `pref_crra_log_limit` |
| p. 63 | "Only if": balanced growth requires power utility | not formalised: proved in the book's Appendix 4.A.2 |
| p. 63, fn. 20 | Asymptotically balanced growth (e.g. `u(c + 0.01)`) | not formalised: imprecise remark |
| p. 63 | Outside the class, saving rates drift to zero or one | not formalised: narrative, no proof |
| pp. 63–64, fn. 21 | Labour supply is a choice | not formalised: narrative |
| p. 64 | Hours condition `u₂(c, 1 − ℓ)/u₁(c, 1 − ℓ) = w` | `ls_kpr_mrs` (KPR), `ls_bk_mrs_scale` (Boppart–Krusell, as `−u_ℓ/u_c`) |
| p. 64 | KPR `u = ((c v(1 − ℓ))^{1−σ} − 1)/(1 − σ)` and its partials | `lsKpr`, `ls_kpr_eq_rm`, `ls_kpr_hasDerivAt_c`, `ls_kpr_hasDerivAt_l` |
| p. 64 | KPR "if" part: constant hours on a balanced path (hours condition and Euler equation) | `ls_kpr_balanced_growth` |
| p. 64 | KPR "only if" part, `v` increasing, `cv(l)` quasiconcave | not formalised: cited (King–Plosser–Rebelo), not proved in the book |
| p. 64 | Boppart–Krusell `u = (c^{1−σ}g(c^{ν/(1−ν)}ℓ) − 1)/(1 − σ)` and its partials | `lsBK`, `lsBKUc`, `lsBKUl`, `ls_bk_hasDerivAt_c`, `ls_bk_hasDerivAt_l`, `ls_bk_arg_invariant`, `ls_bk_uc_scale`, `ls_bk_ul_scale` |
| p. 64 | "If" part: hours fall at `(1 + γ)^{−ν}`, consumption grows at `(1 + γ)^{1−ν}` | `ls_bk_mrs_scale`, `ls_bk_balanced_growth` |
| p. 64 | "`g(·)` is a decreasing function" | `ls_bk_hours_marginal_sign`, `ls_bk_decreasing_g_counterexample` (corrections, item 2) |
| p. 64 | "Technology and output growth proceeding at a net rate γ"; wages grow faster than output; labour share constant | `ls_bk_production`, `ls_p64_output_growth_correction` (corrections, item 1) |
| p. 64, fn. 22 | Declining hours pose no problem on the production side | `ls_bk_production` |
| p. 64 | Boppart–Krusell "only if" part | not formalised: cited, not proved in the book |
| p. 65 | `ν = 0` collapses to the KPR case | `ls_bk_nu_zero` |
| p. 65 | Income and substitution effects cancel (`ν = 0`), income effect stronger (`ν > 0`) | not formalised: interpretation |
| p. 65 | Conclusion: the utility class consistent with the facts | not formalised: summary of the above |

## §2.2 The rest of the text (pp. 65–69)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 65–69 | Previews of Chapters 3–25 | not formalised: narrative |
