# Source map: AKMM Chapter 3

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 3, The Solow model, pp. 71–92, and Appendix 3.A, pp. 825–826. Page
references are the draft's running heads. Lean names are relative to `AKMM.Solow`. Departures
from the book are in [corrections](corrections.md).

Reused from dependencies. EconomicGrowth's `DiscreteTime` (`Solow1956.DiscreteTime.next`,
`steady`, `Params`, `IsPath`, `IsPath.orbit`, `existsUnique_steadyState`, `steady_spec`,
`next_gt_self`, `next_strictMono`, `next_acemoglu`, `next_hasDerivAt`, `slope_at_steady`,
`steady_strictMono_saving`, `steady_strictAnti_depreciation`, `steady_strictAnti_growth`,
`capitalPerEffectiveWorker_succ`, `wage`, `Map.attracting_orbit`, `contraction_steady`,
`cobbDouglas_contraction`, `CobbDouglas.steady_eq`) and `Solow1956` (`Neoclassical.Technology`
with `average_strictAnti`, `marginal_strictAnti`, `output_pos`, `steadyCapital_spec`,
`technology_rpow`, `SolowSwan.CobbDouglas.steadyState`); `UzawaModern`
(`UzawaModern.Uzawa.rate_eq_of_weighted_moments`).

## Introduction and §3.1, the basic model (pp. 71–73) — `Production`, `BasicModel`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 71 | Purpose; Harrod–Domar; the two takeaways | not formalised: narrative |
| p. 72, Assumptions 1–6, fn. 1 | `F` strictly increasing, strictly quasiconcave, CRS, `F(0, L) = 0`, Inada; smooth | `StrictQuasiconcavePos`, `SolowAssumptions` |
| p. 72, Assumptions 1, 4 | As printed, strict monotonicity in `L` contradicts `F(0, L) = 0` | `solow_assumption1_conflicts_assumption4` |
| (3.1), p. 72 | `y_t = f(k_t)`, `f(k) = F(k, 1)` | `intensive`, `solow_intensive_form` |
| p. 73 | `f` strictly increasing and strictly concave, `f(0) = 0`, `f' > 0`, Inada | `solow_intensive_zero`, `solow_intensive_strictMono`, `solow_intensive_pos`, `solow_intensive_strictConcave`, `solow_intensive_deriv_pos`, `solow_technology` |
| (3.2)–(3.5), pp. 72–73 | The fundamental equation `k_{t+1} = (1 − δ)k_t + s f(k_t)`, `c = (1 − s)y` | `eq_3_5`, `solow_params_basic` |
| pp. 72–73 | Open economy, government, consumer optimisation in Ch. 4 | not formalised: narrative |

## §3.1.1, steady state and dynamics (pp. 73–75) — `BasicModel`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 73 | Steady state: `k̄ = (1 − δ)k̄ + s f(k̄)` iff `δk̄ = s f(k̄)` | `solow_fixed_iff` |
| p. 73 | A unique `k̄ > 0` exists | `solow_steady_existsUnique`, `solow_steady_spec` |
| p. 73 | The weak conditions `lim_{0} F₁ > δ/s`, `lim_{∞} F₁ < δ/s` suffice | `solow_steady_existsUnique_weak`, `solow_average_strictAnti_of_concave` |
| p. 73 | Cobb–Douglas satisfies all assumptions, including Inada | `solow_cobbDouglas_assumptions`, `solow_rpow_strictQuasiconcave`, `solow_deriv_rpow_mul_const`, `solow_intensive_cobbDouglas` |
| (3.6), p. 73 | `k̄ = (s/δ)^{1/(1−α)}` | `eq_3_6` |
| p. 74 | `k̄` and `ȳ` increase in `s`, decrease in `δ` | `solow_steady_strictMono_saving`, `solow_steady_strictAnti_depreciation`, `solow_cobbDouglas_output` |
| p. 74, Fig. 3.1 | Global monotone convergence to `k̄` from any `k₀ > 0` | `solow_global_convergence`; under the weak conditions `solow_global_convergence_weak` |
| p. 74 | The proof: `k_t < k̄` ⇒ `k_{t+1} > k_t` and `k_{t+1} < k̄`; monotone convergence; the limit is `k̄` | `solow_convergence_proof_steps`, `solow_global_convergence` |
| p. 74 | "decreasing returns to capital (Assumption 2)" | corrected: `solow_assumption2_alone_counterexample`, `solow_intensive_strictConcave` |
| p. 75 | Growth-rate form `(k_{t+1} − k_t)/k_t = s f(k_t)/k_t − δ` | `solow_growth_rate_form` |
| p. 75 | `f'' < 0`, `f(0) = 0` ⇒ `f(k)/k` decreasing | `solow_average_product_strictAnti` |
| p. 75 | Endogenous saving in Ch. 4 does not overturn convergence | not formalised: refers to Ch. 4 |
| p. 75 | `k̄/ȳ = s/δ` (Cobb–Douglas); larger when `s` larger, `δ` smaller | `solow_capital_output_ratio`, `solow_capital_output_ratio_mono` |

## Other kinds of dynamics (pp. 75–78) — `OtherDynamics`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 75, Fig. 3.2 | `F₁(k, 1)` above `δ/s`: no steady state `k̄ > 0`, `k_t` keeps growing | `solow_endogenous_no_steady_state`, `solow_endogenous_growth` |
| p. 75 | Constant `F₁`: `y = Ak` | covered by `solow_endogenous_growth` (`f' = A`) |
| fn. 2, p. 75 | `Y = AK + BL`: labour does not matter asymptotically if `A > δ/s` | `solow_ak_plus_labour` |
| p. 76 | AK: two countries keep a constant percentage gap | `solow_ak_constant_gap` |
| p. 75 | "hard to take this case very seriously"; labour share two thirds | not formalised: narrative, data |
| pp. 76–77, Fig. 3.3 | Multiple steady states: at least one is not stable | `SolowLocallyAttracting`, `solow_poverty_trap_unstable` |
| p. 77 | `k̄₁`, `k̄₃` stable; a big enough saving rise removes `k̄₁`, `k̄₂` | figure claim, deferred (qualitative; given one crossing see `solow_global_convergence_weak`) |
| p. 77 | Decreasing right side of (3.5): non-monotone convergence | `solow_decreasing_map_overshoots` |
| fn. a, p. 78 | Local stability if the slope at the steady state is below 1 in absolute value | `solow_local_stability` |
| p. 77, fn. b, Fig. 3.4 | Oscillating or chaotic dynamics | not formalised: narrative (no map given), figure claim |

## §3.2, the growing economy (pp. 78–80) — `GrowingEconomy`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 78 | Uzawa: labour-augmenting progress is the only one consistent with balanced growth | Appendix 3.A: `theorem_3A_1` |
| (3.7), p. 79 | `(1 + γ)(1 + n)k̃_{t+1} = (1 − δ)k̃_t + s f(k̃_t)` from the aggregates | `eq_3_7`, `solow_params_growth` |
| p. 79 | Balanced growth: unique `k̃̄` | `solow_fixed_iff_growth`, `solow_bgp_existsUnique` |
| (3.8), p. 79 | Cobb–Douglas `k̃̄ = (s/((1 + γ)(1 + n) + δ − 1))^{1/(1−α)}` | `eq_3_8` |
| p. 79 | `k̃_t` converges monotonically to `k̃̄` | `solow_detrended_convergence` |
| p. 79 | `γ`, `n` work like depreciation | `solow_bgp_strictAnti_growth` |
| pp. 79–80 | Untransforming: `Y/(AL) = f(k̃)`, `y = A f(k̃)` | `solow_untransform` |
| p. 80 | In the long run `y_t → f(k̃̄) A_t` | `solow_income_long_run`, `solow_aggregate_convergence` |
| p. 80 | On the BGP `y` grows at `γ`; `s` affects levels, not long-run growth | `solow_bgp_income_growth`, `solow_income_growth_tendsto` |
| p. 80 | Growth rate `(1 + γ)f(k̃_{t+1})/f(k̃_t) − 1`; above `γ` below the BGP, below `γ` above | `solow_income_growth_identity`, `solow_transition_growth` |

## §3.3, stylised facts (pp. 80–81) — `GrowingEconomy`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 80 | `K/Y = k̃/f(k̃)` constant on the BGP, and converging | `solow_untransform`, `solow_factor_prices_bgp`, `solow_aggregate_convergence` |
| p. 80 | GDP per capita grows at `γ` on the BGP | `solow_bgp_income_growth` |
| (3.9), p. 81 | `r = F₁(K, AL) = f'(k̃)` | `solow_rental_rate` |
| p. 81 | `r` constant on the BGP | `solow_factor_prices_bgp`, `solow_factor_prices_tendsto` |
| p. 81, fn. 5 | Euler: `Y = K F₁ + AL F₂` for H(1) functions | `solow_euler` |
| p. 81 | `w = F₂ = f(k̃) − k̃ f'(k̃)`; capital share, labour share = 1 − capital share, `AL/Y = 1/f(k̃)` | `solow_wage_rate`, `solow_factor_shares` |
| p. 81 | Shares constant on the BGP | `solow_factor_prices_bgp`, `solow_factor_prices_tendsto` |
| p. 81 | Cobb–Douglas shares `α`, `1 − α` everywhere | `solow_cobbDouglas_shares` |
| p. 80 | Return on capital "nearly constant" in the data | not formalised: data |

## §3.4, convergence (pp. 82–88) — `Convergence`

| Source | Claim | Lean |
| --- | --- | --- |
| (3.10), p. 82, fn. 6 | Slope `1 − δ + s f'(k̄)` at `k̄`; `λ = δ − s f'(k̄)` | `eq_3_10` |
| p. 82 | Relative-deviation form `(k_{t+1} − k̄)/k̄ = (1 − λ)(k_t − k̄)/k̄` | `solow_linearised_relative` |
| p. 82, (3.11) | Cobb–Douglas slope `1 − δ(1 − α)`, `λ = δ(1 − α)` | `eq_3_11` |
| p. 83 | `s` does not affect the speed; two forces offset | `solow_speed_independent_of_saving`, `solow_marginal_product_falls_with_saving`, `solow_cobbDouglas_forces_offset` |
| p. 82, Fig. 3.5 | Higher `λ`, faster convergence | figure claim, deferred (local rate: `solow_steady_locally_stable`) |
| (3.12), p. 83 | Slope `(1 − δ + s f'(k̃̄))/((1 + γ)(1 + n))`; `λ` with growth | `eq_3_12` |
| p. 83, (3.13) | Cobb–Douglas slope `α + (1 − α)(1 − δ)/((1 + γ)(1 + n))`, `λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))` | `eq_3_13` |
| fn. 7, p. 83 | Cobb–Douglas cancellations | not formalised: narrative |
| §3.4.1 | Local stability of the steady state | `solow_steady_locally_stable`, `solow_steady_locallyAttracting` |
| §3.4.2, pp. 83–85, Figs. 3.6–3.8 | Cross-country convergence in PWT data | not formalised: data, figure claims |
| p. 86 | Calibration method | not formalised: narrative |
| p. 86, fn. 9 | Cobb–Douglas substitution elasticity is one | not formalised: cited remark |
| p. 86 | `λ` in (3.13) does not depend on `s` | `eq_3_13` |
| p. 87 | BGP: `(1 + γ)(1 + n) = 1 − δ + I/K` | `solow_bgp_investment_rate` |
| p. 87, fn. 10 | `δ = 0.046`, `λ = 0.049`, `λ ≈ 0.02` at `α = 0.73`, `I/Y ≈ 0.23` | not formalised: calibrated numbers (checked: correct) |
| pp. 87–88 | Doubling `s` raises output by 17% | corrected (41%): `solow_saving_output_ratio`, `solow_p88_doubling_saving` |

## §3.5, business cycles (pp. 88–92) — `BusinessCycles`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 88 | Propagation, comovement | not formalised: narrative |
| p. 89 | RBC law `k_{t+1} = (1 − δ)k_t + s(k, A)A F(k, ℓ(k, A))`, a form of (3.5) | `solow_rbc_reduces` |
| p. 89 | Harrod = Hicks neutrality for Cobb–Douglas, `Ã = A^{1−α}` | `solow_harrod_hicks_cobbDouglas` |
| p. 89 | Constant `i/y`, `ℓ` at odds with business-cycle facts | not formalised: data |
| p. 89 | Investment-specific technology `k_{t+1} = sν_t F(k_t, ℓ) + (1 − δ)k_t` | `solow_investment_specific` |
| pp. 89–90 | Demand shocks: `c + i = c/(1 − s)`, `u(c, k)`, the law of motion | `solow_demand_shock`, `solow_demand_unemployment_unique` |
| p. 90, fn. 11 | Keynesian frictions | not formalised: narrative |
| (3.14), p. 90 | The impulse-response experiment | `solow_irf_log_form` (the map), `eq_3_17` |
| pp. 90–91, Fig. 3.9 | `k` rises from 9.066 to 9.089, hump shape, 0.25% | not formalised: numerical, figure claim (9.066 = `eq_3_17` at the calibration, checked) |
| (3.15)–(3.16), p. 91 | Log deviations and first-order approximations | definitions; used in `solow_irf_log_form` |
| (3.17), p. 92 | `k̄ = sĀk̄^α ℓ^{1−α} + (1 − δ)k̄` | `eq_3_17` |
| (3.18), p. 92 | `k̂_{t+1} = (1 − δ(1 − α))k̂_t + δÂ_t` | `eq_3_18`, `solow_irf_log_form` |
| p. 92 | Solution `k̂_{t+1} = Σ ρ^{t−τ}(1 − λ)^τ δε = ρ^t (1 − q^{t+1})/(1 − q) δε` | `solow_irf_capital_sum`, `solow_irf_capital_closed_form` |
| p. 92 | Log-linear approximation error about `10⁻⁵` | not formalised: numerical |
| p. 92 | `ŷ_t` closed form | corrected: `solow_irf_output`, `solow_irf_output_printed_false` |
| p. 92 | `g_k = 1 − δ(1 − α)`, `g_A = s^{1/(1−α)} δ^{−α/(1−α)} A^{α/(1−α)}` | `solow_level_linearisation` |

## Appendix 3.A, Uzawa's theorem (pp. 825–826) — `Uzawa`

| Source | Claim | Lean |
| --- | --- | --- |
| (3.A.1), p. 825 | `Y_t = F̃_t(K_t, L_t)`, `F̃_t` CRS, `L_t = L₀(1 + n)^t` | hypotheses of `theorem_3A_1` |
| Theorem .1, p. 825 | Balanced growth for all `(Y, K, L)` ⇒ `F̃_t(K, L) = F̃₀(K, A_t L)` | `theorem_3A_1` |
| Theorem .1, p. 825 | `A_t` grows at `(1 + γ)(1 + n) − 1` | corrected: `uzawa_technology_growth`, `uzawa_printed_rate_counterexample` |
| p. 825 | `F(K_t, A_t L_t)` completely characterises `F̃_t` | `theorem_3A_1`, `uzawa_technology_unique` |
| (3.A.2)–(3.A.3), p. 826 | Accumulation and resource constraint | hypotheses of `theorem_3A_2` |
| Theorem .2, p. 826 | `I > 0`, constant growth rates ⇒ `γ_Y = γ_K` | `theorem_3A_2`, `uzawa_part2_zero_output_counterexample`, `uzawa_part2_nonneg_consumption` |
| proof, p. 826 | `1 + γ_K = I_t/K_t − δ` | corrected: `uzawa_capital_growth` |
| proof, p. 826 | `I_t/K_t` constant ⇒ `γ_I = γ_K` | `uzawa_investment_growth` |
| (3.A.4), p. 826 | `γ_C C_t + γ_I I_t = γ_Y Y_t`, `(γ_C − γ_Y)C_t = (γ_Y − γ_I)I_t` | `eq_3A_4` |
| p. 826 | In the Solow model `γ_Y = γ_I` by constant saving | `uzawa_part2_solow` |
