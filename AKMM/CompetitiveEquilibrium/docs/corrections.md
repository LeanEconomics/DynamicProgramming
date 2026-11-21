# Corrections and departures: AKMM Chapter 5

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 5, Dynamic competitive equilibrium, pp. 129–158, and Appendix 5.A,
pp. 836–837. Lean names are relative to `AKMM.CompetitiveEquilibrium`. Every book item is located
in the [source map](source-map.md).

## Corrections

1. **p. 149, the steady-state interest rate of the growth economy.** The book: "For reasons
   identical to those used in the case of the endowment economy, we obtain `β = 1 − δ + r`." The
   endowment argument gives `q = β`, i.e. `1/(1 − δ + r) = β`, so the condition is
   `β(1 − δ + r) = 1` (`definition_8_rate`, through `ss_rate`). Counterexample to the printed
   condition: with `u = log`, `β = 1/2`, `δ = 1`, `F(K, L) = 4K^{1/2}L^{1/2}`, `r = w = 2`,
   `K* = 1`, `gᵢ(k) = k` and `Vᵢ(k) = 2 log(k + 2)` form a steady-state equilibrium while
   `1 − δ + r = 2 ≠ β` (`definition_8_printed_counterexample`).

2. **p. 138, the static labour choice with asset income.** With `cᵢ = eᵢAℓᵢ + aᵢ` and utility
   `log c − v(ℓ)` the book gives `v′(ℓᵢ) = aᵢA/(eᵢAℓᵢ + aᵢ)`. The first-order condition is
   `v′(ℓᵢ) = eᵢA/(eᵢAℓᵢ + aᵢ)` (`labour_static_asset_foc`). Counterexample: with `e = A = 1`,
   `a = 2`, `v(ℓ) = ℓ²/2`, the optimum is `ℓ* = √2 − 1`, where `v′(ℓ*) = ℓ*` but
   `aA/(eAℓ* + a) = 2ℓ*` (`labour_static_asset_printed_counterexample`). The qualitative claim
   (more assets, less work) holds (`labour_assets_lower_hours`).

3. **p. 156, the OG exercise.** The book: "the gross steady-state interest rate will be
   `α(1 + β)/(1 − α)`". With log utility, `e_y = 1`, `e_o = 0`, `F = AK^αL^{1−α}` and `δ = 1`,
   `k′ = β(1 − α)Ak^α/(1 + β)` (`og_growth_log_law`, `og_growth_log_equilibrium`) and the steady
   state gross rate is `αAk̄^{α−1} = α(1 + β)/(β(1 − α))` (`og_growth_log_rate`). The printed
   value differs for every `β ∈ (0, 1)`; at `α = 3/10`, `β = 9/10` it is `57/70` against the
   correct `19/21` (`og_growth_log_rate_printed_counterexample`). The remark that the rate is
   below one for low `α` holds, with threshold `α < β/(1 + 2β)` (`og_growth_log_rate_lt_one`).

4. **p. 151, the aggregate functional Euler equation.** The left side is printed
   `u′(K(1 − δ)K + F(K, 1) − G(K))`; it is `u′(K(1 − δ) + F(K, 1) − G(K))`, the planner's (4.26)
   (`definition_9_aggregate_euler`). With `u′` injective, `δ ≠ 1` and `K ∉ {0, 1}` the printed and
   correct equations cannot both hold (`definition_9_aggregate_euler_printed`); with `u = log`,
   `F(K) = 6K^{1/2}`, `δ = β = 1/2`, the correct equation holds at the steady state `K̄ = 4` and
   the printed one fails (`definition_9_aggregate_euler_printed_instance`).

5. **p. 836, Appendix 5.A.** "The first of these equations makes sure the object multiplying `k`
   is zero; the second makes sure the remainder is zero too." The roles are reversed: with
   `g = μ + λk`, `A + Bk + Cg + Dg(g, G) = [A + Cμ + D(μ(G) + λ(G)μ)] + k[B + Cλ + Dλ(G)λ]`
   (`appendix_5A_split`), so the first equation is the constant term and the second the
   coefficient of `k`. Counterexample to the printed attribution: with `A = C = D = 0`, `B = 1`,
   `λ = 0` the first equation holds for every `μ` and the coefficient of `k` is `1`
   (`appendix_5A_printed_attribution_counterexample`). The conclusion (the Euler equation holds
   for all `k`) is right (`appendix_5A_mu_lambda`).

6. **pp. 153, 155, Definitions 11 and 12.** "For each `t > 0`, `(c_{y,t}, c_{o,t+1}, …)` solves
   …". The cohort born at `t = 0` must optimize too; only the initial old are pinned down
   separately. With `t > 0` the price `q₀` is undetermined: with log utility, `β = 1/2` and unit
   endowments, autarky with `q₀ = 1` and `qₜ = 1/2` for `t ≥ 1` satisfies the printed definition,
   while (5.24) requires `q₀ = 1/2` (`definition_11_printed_counterexample`). The definitions take
   a starting cohort `t₀` (`IsOGEndowEquilibrium`, `IsOGGrowthEquilibrium`); every result uses
   `t₀ = 0`.

7. **p. 145, the iterated sequential budget.** After `T` substitutions the book's display
   multiplies `a_{i,T+1}` by `∏_{s=0}^{T−1} q_s`. The factor is `∏_{s=0}^{T} q_s`, as the book's own
   `T = 1` line (`q₁q₀a_{i,2}`) and the nPg condition of Definition 5 show (`seq_budget_iterate`).
   At `T = 0` the printed display reads `c₀ + a₁ = a₀ + y₀`, false for the budget-feasible
   `q₀ = 1/2`, `a₀ = 0`, `y₀ = 2`, `c₀ = 1`, `a₁ = 2`
   (`seq_budget_iterate_printed_counterexample`). The same factor appears in the sentence on the
   limit after the lifetime budget.

8. **p. 141, the consolidated budget.** The book substitutes `ι_{i,t} = k_{i,t+1} − (1 − δ)k_{i,t}`
   and (5.17) into (5.14) to obtain `Σ pₜc_{i,t} = Σ pₜwₜeᵢℓ_{i,t} + (1 − δ + r₀)k_{i,0}`. The
   substitution telescopes to `p_Tk_{i,T+1}`, and the consolidated budget holds iff
   `p_Tk_{i,T+1} → 0` (`growth_consolidated_budget`). When the rental share of the gross return is
   bounded below (`ε(1 − δ + rₜ) ≤ rₜ`), convergence of the value of capital income forces
   `p_Tk_{T+1} → 0` for every budget-feasible plan (`growth_capital_value_tendsto_zero`), and then
   (5.15)–(5.17) are sufficient (`growth_foc_sufficient`). `growth_log_consumption` takes the
   consolidated budget as a hypothesis.

## Departures

9. **The setting of the date-0 and sequential problems (fn. 2).** The book omits nonnegativity
   and the spaces of sequences on purpose. Here consumption is positive, the budget series must
   converge, and optimality compares plans whose utility series converges (`ADOptimal`,
   `LabourOptimal`, `GrowthOptimal`, `SeqOptimal`). Consumers form any probability space
   `(I, μ)`, of which `[0, 1]` with Lebesgue measure is an instance
   (`endow_unitInterval_probability`); aggregates are Bochner integrals and the existence
   theorems assume integrable endowments and convergent `Σ βᵗy_{i,t}/Yₜ`, `Σ βᵗ log Yₜ`
   (`endow_log_existence`). The book's nPg condition `lim (∏_{s≤t} q_s)a_{t+1} ≥ 0` is stated as
   `liminf ≥ 0` (`NoPonzi`), since the limit need not exist.

10. **The growth household (Definition 4).** The household chooses the capital path `k` with `k₀`
   given rather than investment `ι`; (5.13) makes the two one-to-one. The values of consumption,
   investment, capital income and labour income are required to converge separately
   (`GrowthBudget`); the book only writes the two sides of (5.14). The firm conditions of
   Definitions 4 and 8 are stated for Cobb–Douglas technology where the book uses it, and for a
   general `F` through Euler's identity `F(K, 1) = F₁K + F₂`, proved for any differentiable
   constant-returns `F` (`euler_crs`).

11. **The steady-state Bellman equations (Definitions 7 and 8).** The Bellman equation is imposed
   on the natural domain `{x : (m − n)x + y ∈ S}` (consumption at constant holdings lies in the set
   `S` where `u` is defined; for `S = (0, ∞)` and `m = 1` this is the natural borrowing limit),
   with choices restricted to that domain and to consumption in `S` (`SSBellman`). `q = β` and
   `β(1 − δ + r) = 1` are proved from the Bellman equation itself, by comparing the optimum with
   saving once and holding the new level forever (`ss_rate`), instead of through the envelope
   theorem; the book's functional-Euler argument is `ss_functional_euler_q`.

12. **Definition 9.** Condition 1 (the dynamic program (5.23)) enters only through its functional
   Euler equation, as in the book's characterisation; the existence of `V` is not formalised (the
   book does not construct it). The aggregation result of Appendix 5.A is the book's reduction to
   two functional equations in `μ` and `λ`; their solvability in general is not claimed by the
   book and not formalised. The closed form is proved in full (`appendix_5A_closed_form`).

13. **Definition 2 as a special case (p. 135).** The book says identical endowments and a
   strictly concave `u` give identical consumption. This is proved for the CRRA family
   (`definition_2_of_identical`), the utility the chapter uses; the general case would need
   uniqueness of the consumer's optimum on an infinite-dimensional budget set.

14. **(5.24).** The formula `qₜ = β(ω_{y,t}/ω_{o,t+1})^σ` holds for every `σ` with
   `u′(c) = c^{−σ}` (`eq_5_24`); `σ > 0` is used only for the existence of the autarkic
   equilibrium (`og_autarky_equilibrium`).
