# AKMM Chapter 21: Inequality, in Lean

This is the `AKMM/Inequality` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 21 (Inequality, by Per Krusell and José-Víctor Ríos-Rull) of Marina Azzimonti, Per
Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025),
pp. 627–662, cited by the draft's pages. The chapter has no appendix. Run the commands below from
this directory. [Return to the library index](../../README.md).

Chapter 21 surveys income, wage and wealth inequality and explains them with short derivations:
the labor share under factor-augmenting technical change, the capital–output ratio, the
Katz–Murphy relative-wage equation, directed technical change, capital–skill complementarity,
deterministic dynastic economies (indeterminacy of the wealth distribution, altruistic OLG,
heterogeneous discount factors, progressive capital taxes, borrowing limits with alternating
endowments, heterogeneous returns), Huggett's economy with a zero borrowing limit, random growth,
and the channels from inequality to aggregates. Every derivation and precise claim is proved in
the book's setting. The dynastic consumer's problem is Chapter 11's deterministic problem
(11.12), so its Euler equation and Euler sufficiency are reused from `AKMMConsumption`; the
altruistic recursion uses Obstfeld–Rogoff's dynasty utility; the Lorenz curve and Gini
coefficient, and the uniqueness of the stationary distribution, are Miao's Chapter 17 and
Proposition 8.3.1; the Solow steady state is Solow1956's. Not formalised: data, facts and
figures, calibrated and quantitative results, the empirical discussion, cited models without
derivations, and the Kesten–Goldie tail asymptotics `P(A > a) ~ C a^{−ζ}` (they need the
implicit renewal theorem). Beyond the text, Kesten's process is treated short of those
asymptotics: the stationary solution, the weak convergence of the law of `aₜ`, and the tail
index `ζ` in the moment sense. Three printed errors are corrected: the directed-technology first-order condition
(the factor `λ/(1 − λ)` needs the exponent `1/(σ − φ)`), the gross return under progressive
taxation in footnote 25 (`aτ′(a)`, not `τ′(a)/a`), and Kesten's convergence "in probability", as
recorded in [corrections](docs/corrections.md); every book item is located in the
[source map](docs/source-map.md). The library contains **151 theorems**.

* **Factor shares and `k/y`** (§21.2.1): the share depends only on `A_h h/(A_k k)`
  (`fs_partial_homog`, `fs_capital_share_homog`); the CES share and its monotonicity
  (`fs_ces_capital_share`, `fs_share_strictAntiOn`, `fs_share_strictMonoOn`,
  `fs_cd_capital_share`); `k/y = s/(δ + g)` and the rise of `k/y` toward it (`fs_bgp_ky`,
  `fs_steady_ky`, `fs_ky_strictMonoOn`, `fs_ky_below`, `fs_ky_above`).
* **Wage inequality** (§21.2.2): Katz–Murphy (`km_premium_eq`, `km_log_premium`,
  `km_sbtc_strictMono_iff`, `km_cd_premium`, `km_identify`); directed technical change, with the
  corrected first-order condition (`dt_optimal`, `dt_maximiser_ratio`, `dt_printed_ratio_iff`,
  `dt_log_premium`, `dt_exponent_pos_iff`, `dt_rho_gt_two`); capital–skill complementarity
  (`cs_ex1_premium_strictMono`, `cs_ex2_wu_strictAnti`, `cs_nest_wu_monotone`,
  `cs_ces_nest_premium`, `cs_ces_nest_strictMono`).
* **Deterministic dynastic models** (§21.2.3): indeterminacy (`dy_constant_optimal`,
  `dy_indeterminacy`, `dy_indeterminacy_example`); altruistic OLG (`ol_bellman_reduction`,
  `ol_dynastic_utility`, `ol_indeterminacy`); heterogeneous discount factors and returns
  (`hd_unique_beta`, `hd_tendsto_zero`, `hd_assets_limit`, `hd_strictMono`,
  `rh_lower_return_iff`).
* **Distortions and credit restrictions** (§21.2.3): progressive taxes (`pt_hasDerivAt`,
  `pt_printed_iff`, `pt_steady_euler`, `pt_equal_wealth`); two agents with alternating endowments
  (`ta_q_eq_beta`, `ta_footnote_26`, `ta_binding_kkt`, `ta_binding_unique`, `ta_binding_exists`).
* **Uninsurable shocks** (§21.2.3): Huggett with `a = 0` (`hu_autarky_clearing`, `hu_kkt_iff`,
  `hu_price_iff`, `hu_rate_below_discount`); determinacy (`ui_determinate`); Kesten's moment
  condition (`ke_moment_exists`, `ke_moment_unique`).
* **Kesten's random growth process, beyond the text** (§21.2.3, p. 651): on the i.i.d. space
  `infinitePi ν`, with `E|s|^κ < 1` and `E|ε|^κ < ∞`, the perpetuity `A = Σₖ s₀⋯s_{k−1} εₖ`
  converges a.s. and in `L^κ` (`kp_perp_hasSum_ae`, `kp_perp_tendsto_Lp`), `A = ε₀ + s₀A′` with
  `A′ =ᵈ A` independent of `(s₀, ε₀)` (`kp_fixed_point`), and the law of `aₜ` converges weakly to
  that of `A` from any `a₀` (`kp_iter_tendsto_law`); `E|A|^κ < ∞` and `P(|A| ≥ a) ≤ C_κ a^{−κ}`
  (`kp_lintegral_perp_lt_top`, `kp_tail_bound`), `E A^κ = ∞` when `E s^κ > 1`
  (`kp_lintegral_perp_eq_top`), so `sup {κ : E A^κ < ∞} = ζ` (`kp_tail_index`,
  `kp_moment_root`, `kp_finite_tail_index`, `kp_finite_tail_index_ke`); a two-point example with
  `ζ = 1` (`kp_two_point`, `kp_two_point_ke`). The Kesten–Goldie asymptotics are not formalised.
* **Distributions** (§21.1): `gi_gini_eq_ratio`, `gi_lorenz_convex`, `gi_gini_eq_zero_iff`,
  `gi_gini_concentrated_tendsto`, `pa_log_ccdf`.
* **Channels** (§21.3): education with a fixed cost (`ed_fraction`, `ed_wealth_matters`), the MPC
  at the borrowing limit (`mpc_binding`), TANK (`tank_mpc`), the consumption externality
  (`ext_log_output`).

All names are in the namespace `AKMM.Inequality`. The project imports
[AKMM/Consumption](../Consumption/README.md) (`cd_Optimal`, `eq_11_13`, `cd_optimal_of_euler`),
[EconomicDynamics/IncompleteMarkets](../../EconomicDynamics/IncompleteMarkets/README.md)
(Miao: `ay_lorenz`, `ay_gini`, `SIModel.Solution.proposition_8_3_1`), EconomicGrowth/SolowSwan
(`Solow1956.Neoclassical.Technology`, `existsUnique_steadyState`) and
InternationalEconomics/LifeCycleFiscalPolicy (Obstfeld–Rogoff:
`RicardianEquivalence.utility_eq_tsum_iff`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [FactorShares](AKMMInequality/FactorShares.lean) | 13 | Labor share, CES share, `k/y` (AKMM §21.2.1, pp. 636–638) |
| [WageInequality](AKMMInequality/WageInequality.lean) | 28 | Katz–Murphy, directed technical change, capital–skill complementarity (AKMM §21.2.2, pp. 638–641) |
| [Dynastic](AKMMInequality/Dynastic.lean) | 19 | Indeterminacy, altruistic OLG, heterogeneous discount factors and returns (AKMM §21.2.3, pp. 644–649) |
| [Distortions](AKMMInequality/Distortions.lean) | 17 | Progressive capital taxes, alternating endowments with borrowing limits (AKMM §21.2.3, pp. 647–648) |
| [Uninsurable](AKMMInequality/Uninsurable.lean) | 9 | Huggett with `a = 0`, determinacy, Kesten's moment condition (AKMM §21.2.3, pp. 650–651) |
| [Distribution](AKMMInequality/Distribution.lean) | 10 | Lorenz curve, Gini coefficient, Pareto tails (AKMM §21.1, pp. 630–631) |
| [Channels](AKMMInequality/Channels.lean) | 7 | Education with a fixed cost, MPCs, TANK, the consumption externality (AKMM §21.3, pp. 656–660) |
| [Kesten](AKMMInequality/Kesten.lean) | 48 | Kesten's process: stationary solution, weak convergence, tail index in the moment sense; beyond the text (AKMM §21.2.3, p. 651) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
