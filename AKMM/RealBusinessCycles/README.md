# AKMM Chapter 14: Real business cycles, in Lean

This is the `AKMM/RealBusinessCycles` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 14 (Real business cycles, by Kurt Mitman) of Marina Azzimonti, Per Krusell, Alisdair
McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 405–438, with
Appendix 14.A (pp. 863–867), cited by the draft's pages. Run the commands below from this
directory. [Return to the library index](../../README.md).

Chapter 14 measures business cycles (the Hodrick–Prescott filter, band-pass filters, recursive
SVARs), builds the simple labour-only model and the core RBC model, calibrates it, extends it
(indivisible labour, adjustment costs, utilisation, investment-specific and government-spending
shocks) and closes with business-cycle accounting; Appendix 14.A covers the spectrum and linear
filters. Every derivation the text carries out is proved in the book's setting: the HP filter as
a positive-definite least-squares problem with its pentadiagonal first-order system, its
constrained form, the linear trend at `µ = 0` and the OLS limit as `λ → ∞`; the SVAR reduced form
and impulse responses; (14.2)–(14.11) with the welfare theorems imported from Miao; impulse
responses from linear policies; the calibration of `φ` with a numeric certificate; KPR balanced
growth; the adjustment-cost algebra; the wedge conditions and backing out the wedges; and the
spectral inversion formula, the filtered spectrum and the gains of the first-difference, HP and
band-pass filters. Not formalised: history, data, stylised facts, tables, figures, simulations,
estimation, and the Cramér spectral representation theorem. Eleven printed errors are corrected,
among them the sign of the HP first-order condition, the missing `β` in the Bellman equation,
the steady-state interest rate (`g^σ/β`, not `gσ/β`), Tobin's `q` (`1/(1 − ψ(i/k − δ))`), the
inversion proof, the band variance and "less smoothing" for large `λ`, each with a Lean
counterexample or corrected statement, as recorded in [corrections](docs/corrections.md); every
book item is located in the [source map](docs/source-map.md). The library contains
**134 theorems**.

* **The HP filter** (§14.3.1): `I + λA` positive definite and the unique trend `(I + λA)⁻¹Y`
  (`hp_posDef`, `eq_14_1`, `hp_unique`, `hp_trend_eq`); the rows of `A` (`hp_A_interior`,
  `hp_A_row0`, `hp_A_row1`, `hp_A_rowLast`, `hp_A_rowLast1`); the corrected first-order condition
  (`hp_foc_interior`, `hp_foc_printed_false`); constrained form (`hp_constrained_of_lagrangian`,
  `hp_constrained_unique`); `µ = 0` (`hp_pen_zero_iff`); `λ → ∞` (`hp_limit_ols`); Ravn–Uhlig
  (`hp_ravn_uhlig`).
* **SVAR** (§14.3.3): reduced form and recursive identification (`svar_reduced_form`,
  `svar_inv_lower`, `svar_impact_recursive`), impulse responses (`svar_irf`, via AKMM Chapter 7).
* **The simple model** (§14.4.1): (14.5)–(14.7) (`eq_14_5`, `eq_14_6`, `eq_14_7`), constant hours
  (`sm_equilibrium`), the falling interest rate (`sm_interest_rate_falls`), the Frisch elasticity
  `(1 − ℓ)/ℓ = 2` (`sm_frisch`, `sm_frisch_two`, via AKMM Chapter 12).
* **The core RBC model** (§14.4.2): (14.8)–(14.11) (`eq_14_8`, `eq_14_9`, `eq_14_10`, `eq_14_11`)
  with a concrete Bellman solution (`rbc_example_bellman`); impulse responses (`irf_first_terms`,
  `irf_linear`, `irf_decay`).
* **Calibration** (§14.4.3–14.4.4): Solow residual and perpetual inventory
  (`cal_solow_residual`, `cal_perpetual_guess`); the `φ` identity and value (`cal_phi_identity`,
  `cal_phi_value`).
* **Extensions** (§14.4.4, §14.5): KPR (`ext_kpr_form`, `ext_kpr_homog`), `R = g^σ/β`
  (`ext_bgp_interest`, `ext_interest_printed_false`); adjustment costs (`adj_homog`,
  `adj_jointly_convex`, `adj_shadow_price`, `adj_q_printed_false`, `adj_hayashi`); utilisation,
  IST and government spending (`ext_util_solow`, `ext_ist_price`, `ext_gov_hours_increasing`).
* **Business-cycle accounting** (§14.6): the wedge conditions from the household's problem
  (`bca_labour_foc`, `bca_investment_euler`) and backing out the wedges (`bca_static_wedges`,
  `bca_static_unique`, `bca_investment_wedge`, `bca_zero_wedges`).
* **Appendix 14.A**: inversion and variance (`appx_inversion`, `appx_variance`), band variance
  (`appx_band_variance`), filtered spectrum (`appx_filter_autocov`, `appx_filtered_spectrum`),
  gains (`appx_gain_diff`, `appx_hp_gain_eq`, `appx_hp_gain_mono`, `appx_hp_gain_limit`,
  `appx_hp_trend_gain_anti`), band-pass coefficients (`appx_bandpass_coeff`).

All names are in the namespace `AKMM.RealBusinessCycles`. The project imports
[EconomicDynamics/NeoclassicalGrowth](../../EconomicDynamics/NeoclassicalGrowth/README.md)
(Miao Chapter 14: `rb_u`, `rb_u_tangent`, `rx_HasPartials`, `proposition_14_3_1`, the RBC welfare
theorems, `rx_cu_amplification`, `rx_ist_price`, `rb_lottery`, `rb_u38_bgp`),
[AKMM/LaborSupply](../LaborSupply/README.md) (Chapter 12: `frischF`, `dyn_frisch_cd`, `kprU`,
`kpr_homog`) and [AKMM/Uncertainty](../Uncertainty/README.md) (Chapter 7:
`sde_impulse_response`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [HPFilter](AKMMRealBusinessCycles/HPFilter.lean) | 29 | (14.1): the HP filter, `I + λA`, the first-order system, constrained form, `µ = 0` (AKMM §14.3.1, pp. 410–412) |
| [HPLimit](AKMMRealBusinessCycles/HPLimit.lean) | 10 | The HP trend tends to the OLS linear trend as `λ → ∞` (AKMM p. 411) |
| [SVAR](AKMMRealBusinessCycles/SVAR.lean) | 6 | The recursive structural VAR (AKMM §14.3.3, pp. 417–419) |
| [SimpleModel](AKMMRealBusinessCycles/SimpleModel.lean) | 14 | (14.2)–(14.7) and the Frisch elasticity (AKMM §14.4.1, pp. 420–422) |
| [CoreRBC](AKMMRealBusinessCycles/CoreRBC.lean) | 7 | (14.8)–(14.11): the planner's Bellman equation (AKMM §14.4.2, pp. 422–424) |
| [Impulse](AKMMRealBusinessCycles/Impulse.lean) | 6 | Impulse responses from linear policies (AKMM p. 424) |
| [Calibration](AKMMRealBusinessCycles/Calibration.lean) | 9 | Solow residual, perpetual inventory, `φ` (AKMM §14.4.3–14.4.4, pp. 425–428) |
| [Extensions](AKMMRealBusinessCycles/Extensions.lean) | 22 | KPR, adjustment costs, utilisation, IST, government spending (AKMM p. 427, §14.5, pp. 432–434) |
| [BCA](AKMMRealBusinessCycles/BCA.lean) | 6 | Business-cycle accounting (AKMM §14.6, pp. 434–437) |
| [Gains](AKMMRealBusinessCycles/Gains.lean) | 15 | Gains of the first-difference, HP and band-pass filters (AKMM App. 14.A, pp. 864–865) |
| [Spectral](AKMMRealBusinessCycles/Spectral.lean) | 10 | The spectrum, inversion, variance, filtered spectrum (AKMM App. 14.A, pp. 863–864) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
