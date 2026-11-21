# Source map: AKMM Chapter 5

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 5, Dynamic competitive equilibrium, pp. 129–158, and Appendix 5.A,
pp. 836–837. Page references are the draft's running heads. Lean names are relative to
`AKMM.CompetitiveEquilibrium`. Departures from the book are in [corrections](corrections.md).

Reused from dependencies. SLP `EquilibriumApplications`
(`StokeyLucasPrescott.EquilibriumApplications`): the CRRA family `sgCRRA`
(`(c^{1−σ} − 1)/(1 − σ)`, `log c` at `σ = 1`) with `sgCRRA_one`, `sgCRRA_hasDerivAt`,
`sgCRRA_tangent`. Miao `OverlappingGenerations` (`Miao.OverlappingGenerations`): `opKstarCD`,
`op_kstarCD_pos` and `op_cd_converge` (global convergence of `k_{t+1} = ck_t^α`). Miao
`CompleteMarkets` is not used: its equilibria live on an event tree with finitely many consumers,
while the book's economies have a continuum of consumers and are deterministic, so the Arrow–Debreu
and sequential results are proved directly in the book's setting.

## Introduction and §5.1, equilibrium concepts (pp. 129–131)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 129–131 | Perfect competition, representative agents, three equilibrium concepts | not formalised: narrative |

## §5.2.1, the endowment economy (pp. 131–135) — `ADConsumer`, `EndowmentAD`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 132 | Consumers `i ∈ [0, 1]` | general probability space; `[0, 1]` is an instance: `endow_unitInterval_probability` |
| (5.1)–(5.2), p. 132 | Utility `Σ βᵗu(c_{i,t})`, lifetime budget `Σ pₜc_{i,t} = Σ pₜy_{i,t}` | `ADBudget`, `ADOptimal` |
| fn. 2, p. 132 | Nonnegativity and spaces omitted | added: `c > 0`, convergent series (corrections, item 9) |
| Definition 1, p. 132 | Arrow–Debreu equilibrium | `IsADEquilibrium` |
| p. 133 | First-order conditions `βᵗu′(c_{i,t}) = λᵢpₜ`, multiplier independent of time | `ad_foc`, `ad_foc_multiplier`; perturbation tools `ce_tsum_perturb`, `ce_foc_of_perturb` |
| p. 133 | Sufficiency of the first-order conditions (strictly concave `u`) | `ad_foc_sufficient`, `ce_crra_tangent`, `ce_log_tangent` |
| (5.3), p. 133 | `pₜ = βᵗu′(c_{i,t})/u′(c_{i,0})` | `eq_5_3`; log form `endow_log_foc` |
| p. 133 | Log: `pₜ = βᵗY₀/Yₜ` | `endow_log_price` |
| p. 133 | Identical consumption growth `c_{i,t+1}/c_{i,t} = Y_{t+1}/Yₜ = βpₜ/p_{t+1}` | `endow_log_growth` |
| p. 134 | Constant aggregate endowment ⇒ perfect smoothing | `endow_log_smoothing` |
| p. 134 | `c_{i,0} = (1 − β)Y₀ Σ βᵗy_{i,t}/Yₜ`; `c_{i,t} = θᵢYₜ` | `endowShare`, `endow_log_shares` |
| p. 134 | Identical endowments: `θᵢ = 1`, representative consumer | `endow_log_representative` |
| p. 134 | Existence (explicit construction) and uniqueness of the log equilibrium | `endow_log_existence`, `endow_log_existence_instance`; uniqueness from `endow_log_price`, `endow_log_shares` |
| p. 134 | CRRA: identical gross growth `(βpₜ/p_{t+1})^{1/σ}` | `endow_crra_common_growth`, `endow_crra_growth` |
| p. 134 | CRRA: `pₜ = βᵗ(Y₀/Yₜ)^σ` | `endow_crra_price` |
| pp. 134–135 | Asset pricing remark, uncertainty in Ch. 7 | not formalised: narrative |
| Definition 2, p. 135 | Representative-consumer equilibrium | `IsADEquilibriumRep` |
| p. 135 | Strictly concave `u`, equal endowments ⇒ equal consumption, Definition 2 | `definition_2_of_identical` (CRRA utility) |

## §5.2.2, the labour economy (pp. 135–138) — `LabourAD`

| Source | Claim | Lean |
| --- | --- | --- |
| (5.4)–(5.5), p. 135 | Utility `Σ βᵗ[u(c) − v(ℓ)]`; `Yₜ = AₜLₜ` | `LabourOptimal`, `labourProfit` |
| (5.6), p. 136 | Firm's problem; a sequence of static problems | `LabourFirmOpt`, `LabourStaticOpt`, `eq_5_6_static` |
| fn. 3, p. 136, p. 137 | `w = A`: any scale; `A > w`: no optimum; `A < w`: `L = 0` | `labour_firm_fn3` |
| p. 137 | Equilibrium requires `wₜ = Aₜ` | `labour_wage_eq_productivity` |
| (5.7), p. 136 | Household budget | `LabourBudget` |
| Definition 3, p. 136 | Arrow–Debreu equilibrium with labour | `IsADEquilibriumLabour` |
| fn. 4, p. 136 | Firms could operate at single dates | not formalised: remark (covered by `eq_5_6_static`) |
| (5.8), p. 137 | `βᵗu′(c_{i,t}) = λᵢpₜ` | `eq_5_8` |
| (5.9), p. 137 | `v′(ℓ_{i,t}) = eᵢwₜu′(c_{i,t})` | `eq_5_9` |
| (5.10), p. 137 | `p_{t+1}/pₜ = βu′(c_{i,t+1})/u′(c_{i,t})` | `eq_5_10` |
| p. 137 | Sufficiency of (5.8)–(5.9) | `labour_foc_sufficient` |
| p. 137 | Log: `c_{i,t} = θᵢYₜ` | `labour_log_shares` |
| p. 138 | `v′(ℓ_{i,t})θᵢYₜ = eᵢAₜ` | `labour_log_hours` |
| p. 138 | `θᵢ = eᵢ` ⇒ equal hours `ℓ_{i,t} = Lₜ` | `labour_log_equal_hours` |
| p. 138 | The guess `θᵢ = eᵢ` satisfies the budget: an equilibrium | `labour_log_equilibrium`, `labour_log_equilibrium_instance` |
| p. 138 | Income and substitution effects cancel (verbal) | not formalised: narrative (the result is `labour_static_wage_independent`) |
| p. 138 | Static problem `c = wℓ`: hours independent of `w` | `labour_static_wage_independent` |
| p. 138 | Asset income: `v′(ℓᵢ) = aᵢA/(eᵢAℓᵢ + aᵢ)` | corrected: `labour_static_asset_foc`, `labour_static_asset_printed_counterexample` (corrections, item 2) |
| p. 138 | Higher assets ⇒ lower labour effort | `labour_assets_lower_hours` |
| p. 138 | Labour supply depends on wealth inequality | not formalised: qualitative remark |

## §5.2.3, the neoclassical growth economy (pp. 139–142) — `GrowthAD`

| Source | Claim | Lean |
| --- | --- | --- |
| (5.11)–(5.12), p. 139 | Cobb–Douglas firm, rental of capital and labour | `cdProfit` |
| (5.13)–(5.14), p. 139 | Capital accumulation, household budget | `GrowthBudget` (capital path as choice; corrections, item 10) |
| Definition 4, pp. 139–140 | Arrow–Debreu equilibrium of the growth economy | `GrowthOptimal` (household part); instance `growth_optimal_instance` |
| p. 140 | Firms renting capital; owning capital alternative | not formalised: remark |
| (5.15)–(5.16), p. 140 | First-order conditions for consumption and labour | `eq_5_15`, `eq_5_16` |
| (5.17), p. 140 | No arbitrage `pₜ = p_{t+1}r_{t+1} + (1 − δ)p_{t+1}` | `eq_5_17` |
| fn. 5, p. 140 | Otherwise no maximum | `growth_capital_value_tendsto_zero`, `growth_foc_sufficient` |
| p. 141 | Firm: `r = αAK^{α−1}L^{1−α}`, `w = (1 − α)AK^αL^{−α}`; indifference to scale | `growth_firm_foc`, `growth_firm_optimal` |
| p. 141 | Capital–labour ratio pinned down | `growth_firm_ratio` |
| p. 141 | Log: `C_{t+1} = βpₜ/p_{t+1}·Cₜ` | `growth_log_aggregate_euler` |
| p. 141 | Consolidated budget `Σ pₜc = Σ pₜwₜeℓ + (1 − δ + r₀)k₀` | `growth_consolidated_budget` (needs `p_Tk_{T+1} → 0`; corrections, item 8) |
| p. 142 | `c_{i,t} = eᵢβᵗ(1 − β)(Σ pₜwₜℓₜ + (1 − δ + r₀)K₀)/pₜ` | `growth_log_consumption` |
| fn. 6, p. 142 | `θᵢ = eᵢ` | `growth_fn6` |
| p. 142 | Hours independent of `i` | `growth_log_hours_common` |
| (5.18), p. 142 | Aggregate Euler equation | `eq_5_18` |
| (5.19), p. 142 | Aggregate labour condition | `eq_5_19` |
| (5.20), p. 142 | Resource constraint | `eq_5_20` |
| p. 142 | No closed form in general | not formalised: negative remark |
| fn. 7, p. 142 | `δ = 1`: saving rate `αβ`, `v′(L)L = (1 − α)/(1 − αβ)` | `growth_fn7` |
| p. 142 | Planner's first-order conditions equal (5.18), (5.19) | `growth_planner_foc_K`, `growth_planner_foc_L` (with `ce_planner_iff`) |
| fn. 8, p. 142 | Heterogeneous skills: a weighted planner | not formalised: asserted without derivation |

## §5.3, sequential equilibrium (pp. 143–146) — `Sequential`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 143, fn. 9 | `1 + r_{t+1} = 1/qₜ`; `r₀` undetermined under the alternative convention | `seq_gross_rate`; fn. 9 not formalised: remark |
| Definition 5, pp. 143–144 | Sequential equilibrium with nPg | `SeqBudget`, `NoPonzi`, `SeqOptimal`, `IsSeqEquilibrium`; instance `seq_equilibrium_instance` |
| p. 144, fn. 10 | Walras's law: goods clearing ⇔ asset clearing | `seq_walras` |
| (5.21)–(5.22), p. 144 | `qₜ = βu′(c_{t+1})/u′(cₜ)` | `eq_5_21_5_22` |
| p. 145 | `∏_{s<t} q_s = βᵗu′(cₜ)/u′(c₀) = pₜ` | `seqPrice`, `seqPrice_succ`, `seqPrice_pos`, `seq_price_product` |
| p. 145 | `p_{t−1}/pₜ = 1/q_{t−1}` | `seq_gross_rate` |
| p. 145 | Budgets after `T` substitutions | corrected: `seq_budget_iterate`, `seq_budget_iterate_printed_counterexample` (corrections, item 7) |
| p. 145 | Lifetime budget `Σ pₜcₜ ≤ a₀ + Σ pₜyₜ` | `seq_lifetime_budget` |
| p. 145 | Equality iff the nPg limit is zero | `seq_lifetime_budget_eq_iff` |
| p. 145 | The two budget constraints are equivalent | `seqAssets`, `seq_of_lifetime_budget` |
| p. 145 | Same quantities and prices in both concepts | `seq_optimal_iff_ad`, `seq_equilibrium_is_ad` |
| Definition 6, p. 146 | Sequential equilibrium of the growth economy | conditions used in `seq_growth_walras`; the equivalence with Definition 4 is left to the reader by the book and not formalised |
| p. 146, fn. 11 | Walras's law makes the resource constraint redundant | `euler_crs`, `seq_growth_walras` |

## §5.4.1, steady state (pp. 147–149) — `SteadyState`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 146–147 | Recursive methods, steady states as a subset of equilibria | not formalised: narrative |
| Definition 7, p. 147 | Recursive steady-state equilibrium, endowment economy | `SSBellman`, `IsSSEquilibriumEndow` (natural domain; corrections, item 11) |
| p. 148 | Functional Euler equation; stationarity gives `q = β` | `ss_functional_euler_q`; from Definition 7 directly: `ss_rate`, `definition_7_q_eq_beta` |
| p. 148 | `gᵢ(a) = a` solves the functional Euler equation | `ss_functional_euler_id` |
| p. 148 | `Vᵢ(a) = u(a(1 − q) + yᵢ)/(1 − β)` | `ss_value` |
| p. 148 | Any distribution with market clearing is an equilibrium ("no predictions") | `definition_7_any_distribution` |
| p. 148 | Shape of `u` irrelevant; balanced growth | not formalised: remark (no hypothesis on `u` beyond concavity in `ss_value`) |
| Definition 8, p. 149 | Recursive steady-state equilibrium, growth economy | `IsSSEquilibriumGrowth` |
| p. 149 | `β = 1 − δ + r` | corrected: `definition_8_rate`, `definition_8_printed_counterexample` (corrections, item 1) |
| p. 149 | `r = F₁(K*, 1)` determines `K*`; `w = F₂` | `definition_8_capital` (Cobb–Douglas), `growth_firm_foc` |
| p. 149 | Distribution indeterminate; `gᵢ(k) = k`, `Vᵢ(k) = u(k(r − δ) + weᵢ)/(1 − β)` | `definition_8_any_distribution` |

## §5.4.2, dynamics (pp. 149–152) and Appendix 5.A (pp. 836–837) — `RecursiveEquilibrium`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 149–150 | `K` is the state; `r(K)`, `w(K)`, `G(K)` | not formalised: motivation |
| (5.23), Definition 9, p. 150 | Recursive competitive equilibrium | conditions 2–3 as hypotheses; condition 1 through its functional Euler equation; existence of `V` not formalised (corrections, item 12) |
| fn. 15, p. 150 | Firm's problem instead of first-order conditions | `growth_firm_optimal`, `growth_firm_foc` |
| p. 150 | The resource constraint is met | `definition_9_resource` |
| p. 150 | Individual functional Euler equation | hypothesis of `definition_9_aggregate_euler`; closed form `appendix_5A_closed_form` |
| p. 151 | Power utility ⇒ `g(k, K) = μ(K) + λ(K)k` | `appendix_5A_power`, `appendix_5A_linear`, `appendix_5A_split`, `appendix_5A_mu_lambda` (existence of `μ`, `λ` not formalised: the book does not prove it) |
| p. 151 | Aggregation; heterogeneous intercepts `μᵢ(K)` | `aggregation_linear` |
| p. 151 | Aggregate functional Euler equation = planner's (4.26) | corrected: `definition_9_aggregate_euler`, `definition_9_aggregate_euler_printed`, `definition_9_aggregate_euler_printed_instance` (corrections, item 4) |
| p. 151 | Closed form only for log, Cobb–Douglas, `δ = 1` | `appendix_5A_closed_form`; "only" not formalised (negative claim) |
| Definition 10, pp. 151–152 | Valued leisure | `definition_10_planner` (resource constraint and intratemporal condition at `k = K`) |
| p. 152 | Intertemporal conditions identical to the planner's | as `definition_9_aggregate_euler`; the labour condition `definition_10_planner` |
| p. 152, fn. 17 | No aggregation with leisure unless `kᵢ/eᵢ` is common | not formalised: asserted without derivation |
| App. 5.A, p. 836 | Raising to `−1/σ`; `A + Bk + Cg + Dg(g, G) = 0` | `appendix_5A_power`, `appendix_5A_linear` |
| App. 5.A, p. 836 | The two functional equations; which term each kills | corrected: `appendix_5A_split`, `appendix_5A_mu_lambda`, `appendix_5A_printed_attribution_counterexample` (corrections, item 5) |
| App. 5.A, p. 836 | Consistency `G(K) = μ(K) + λ(K)K` | `appendix_5A_closed_form` (consistency part) |
| App. 5.A, p. 836 | HARA: exponential and quadratic utility, affine arguments | not formalised: asserted without proof |
| App. 5.A, pp. 836–837 | Log/CD/`δ = 1`: `G(K) = αβAK^α`, `g(k, K) = βr(K)k`, `μ = 0`, `λ = βr` | `appendix_5A_closed_form`, `appendix_5A_closed_form_mu_lambda` |
| App. 5.A, p. 837 | Solving a 2-period economy to guess | not formalised: method advice |

## §5.5, overlapping generations (pp. 152–157) — `OGEconomies`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 152–153 | History and setting of OG models | not formalised: narrative |
| Definition 11, p. 153 | Sequential equilibrium of the endowment OG economy | `OGSavingOpt`, `IsOGEndowEquilibrium` (starting cohort `t₀`; corrections, item 6) |
| p. 153 | "for each `t > 0`" | corrected to `t ≥ 0`: `definition_11_printed_counterexample` |
| pp. 153–154 | Goods clearing ⇔ `a_{t+1} = 0`; autarky | `og_autarky` |
| p. 154 | Euler equation at autarky | `og_euler_autarky` |
| (5.24), p. 154 | `qₜ = β(ω_{y,t}/ω_{o,t+1})^σ` | `eq_5_24`; autarky is an equilibrium `og_saving_autarky_opt`, `og_autarky_equilibrium` |
| p. 154 | Stationary endowments; `q > 1` possible | `og_negative_rate_example` |
| p. 154 | Impossible in the dynastic model unless endowments fall | `og_dynastic_rate` |
| p. 154 | Three-period lives, PAYG pensions | not formalised: discussion (welfare in Ch. 6) |
| Definition 12, p. 155 | Sequential equilibrium of the OG growth economy | `OGCapitalOpt`, `IsOGGrowthEquilibrium` (`t > 0` corrected as in Definition 11) |
| p. 155 | Euler equation as a first-order difference equation | `og_growth_euler` |
| p. 155 | Steady-state condition | `og_growth_steady` |
| pp. 155–156 | `β(1 − δ + F₁(k̄)) = 1` fails in general | `og_growth_not_smoothed` |
| p. 156 | Exercise: log, `e_y = 1`, `e_o = 0`, CD, `δ = 1`: dynamics | `og_growth_log_law`, `og_growth_log_equilibrium` |
| p. 156 | (i) Log-linear, monotone convergence | `og_growth_log_convergence` |
| p. 156 | (ii) Gross rate `α(1 + β)/(1 − α)` | corrected: `og_growth_log_rate`, `og_growth_log_rate_printed_counterexample` (corrections, item 3) |
| p. 156 | Below one for low `α` | `og_growth_log_rate_lt_one` |
| p. 156, fn. 18 | Uniqueness of `k_{t+1}` not obvious; planner across cohorts | not formalised: no claim |
| p. 156 | Dynastic long-run rate `(1 + γ)^σ/β` | `og_dynastic_long_run_rate` |
| p. 156 | Perpetual youth, annuities | not formalised: verbal discussion |
| p. 157 | Warm glow; the initial old's problem | not formalised: setting only |
| p. 157 | Pure altruism: dynastic life-cycle model, long-run rate `1/β̃` | `og_altruism_rate` |
