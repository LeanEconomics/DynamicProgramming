# AKMM Chapter 8: Empirical Strategies and Quantitative Macroeconomics, in Lean

This is the `AKMM/QuantitativeMethods` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 8 and Appendix 8.A of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko
Mukoyama, *Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands
below from this directory. [Return to the library index](../../README.md).

Chapter 8 asks how large the fiscal multiplier is and uses the question to compare four empirical
strategies: natural experiments, structural VARs, structural estimation and calibration. Its
mathematical content is algebra, and that algebra is formalised: the static planner economy and its
multiplier, the identification problem and instruments, the reduced form of a structural VAR and its
rotation non-identification, the restriction count, Cholesky (recursive) identification, the
population estimands of local projections and VARs and the Plagborg-Møller–Wolf equivalence, the
dynamic fiscal model with its steady state, its linearisation and the closed-form saddle path of its
impulse response to a spending shock, the likelihood of the static model and the Kalman-filter
likelihood, and the calibration identities. The qualitative claims of Figure 8.4 are proved
analytically for the model's whole parameter class: the signs of the impulse responses, multipliers
below one, and the multiplier rising with persistence (impact and whole-horizon multipliers) and
with the elasticity of labour supply (impact multiplier, for `δ ≤ 1`); that the plotted 12-quarter
multiplier does the same is numerical. Data, estimates, calibrated numbers and the Monte Carlo study
are not formalised. The project depends on Miao's `PartialInformation` (second moments of random
vectors, the Kalman filter and its likelihood), `RationalExpectations` (VAR impulse responses),
`StructuralEstimation` (invariance of maximum likelihood) and `NeoclassicalGrowth` (the Frisch
elasticity). Six printed errors or imprecisions are corrected — the government rule of Appendix
8.A.1, the range of footnote 6's weights, a `K`/`k` slip, the missing Jacobian in the static
likelihood (with a Lean counterexample), the missing sign normalisation of Cholesky identification
(with a Lean counterexample) and the claim that investment falls after a spending shock, which fails
for very persistent shocks — as recorded in [corrections](docs/corrections.md); every book item is
located in the [source map](docs/source-map.md). The library contains **138 theorems**.

* **The static model and its multiplier** (§8.2, (8.5)–(8.6), Appendix 8.A.2): the planner's
  unique optimum and its first-order conditions (`sm_planner_optimal`, `sm_planner_unique`,
  `sm_foc_iff`); (8.2)–(8.3) and the equilibrium (`eq_8_2_8_3`, `sm_equilibrium_unique`); the
  multiplier from fiscal shocks and as the slope of the supply curve (`sm_multiplier_eta`,
  `sm_supply_slope`), equal to `1/(1 + ψ(1 − Ḡ/ȳ)) ∈ (0, 1)` (`sm_multiplier_formula`,
  `sm_multiplier_mem_Ioo`); Appendix 8.A.2 (`sm_supply_dA`, `appendix_8A_2_total_differential`,
  `appendix_8A_2_steady`); (8.5)–(8.6) and footnote 3 (`eq_8_5`, `eq_8_5_log`, `eq_8_6`, `fn_3`).
* **Identification and natural experiments** (§8.2–8.4): (8.8)–(8.9) (`eq_8_8_8_9`); the
  least-squares slope is biased unless `Var(Â) = 0` (`id_ols_slope`); an instrument uncorrelated
  with TFP recovers the effect (`id_iv`); the restriction identifies `χ` (`id_restriction_identifies`).
* **Structural VARs** (§8.4): the reduced form (8.7) (`eq_8_7`), `Var(u) = B₀⁻¹B₀⁻¹'`
  (`sv_var_u`), the normalisation (`sv_normalisation`), rotations (`sv_rotation`,
  `sv_rotation_converse`, `sv_not_identified`), the restriction count (`sv_finrank_symm`,
  `sv_restriction_count`).
* **Cholesky identification** (box, p. 224): existence and uniqueness of the Cholesky factor
  (`ch_exists`, `ch_unique`), recursive identification with its sign normalisation
  (`ch_recursive_identification`, `ch_sign_counterexample`), the fiscal example
  (`ch_fiscal_example`).
* **VARs and local projections** (§8.5): dynamic multipliers (`vl_cum_multiplier_prop`,
  `vl_peak_multiplier_prop`); VAR(1) and companion-form impulse responses (`vl_var1_irf`,
  `vl_companion_irf`); the LP and VAR estimands (`vl_lp_estimand`, `vl_var_estimand`,
  `vl_lp_differs`), footnote 6 (`fn_6`), the LP box (`vl_lp_exogenous`), the VAR(1) case
  (`vl_var1_estimands`).
* **The dynamic fiscal model** (§8.6, Appendix 8.A.1): (8.11), (8.15)–(8.18) (`eq_8_11`,
  `eq_8_15`, `eq_8_16_8_17`, `eq_8_18`); unit means (`eq_8_12_mean`); the equilibrium
  (`fm_IsEquilibrium`, `fm_steady_isEquilibrium`); the steady state, unique, with the printed
  government rule corrected (`appendix_8A_1`, `fm_steady_exists`, `appendix_8A_1_ratios`,
  `appendix_8A_1_printed_G`); the multiplier with investment fixed (`fm_fixed_investment_multiplier`).
* **The linearised model and Figure 8.4** (§8.6.1–8.6.2, §8.8, pp. 231–238): the static
  equations are exactly log-linear, the resource and Euler equations linearised
  (`fd_static_exact`, `fd_resource_linear`, `fd_euler_linear`, `fd_ratios`); the stable root and
  the saddle path, the unique bounded solution (`fd_lam_props`, `fd_irf_solves`, `fd_k_bound`,
  `fd_irf_unique`); on impact consumption falls, hours and output rise and, for
  `ρ < 1/(1+κ)`, investment falls, with consumption and capital below steady state throughout
  (`fd_impact_signs`, `fd_c_k_neg`), while investment rises for more persistent shocks
  (`fd_investment_correction`); cumulative multipliers below one (`fd_cum_lt`, `fd_mult_lt_one`,
  `fd_impact_mult_mem`); the impact multiplier rising in `ρ` and falling in `ψ` for `δ ≤ 1`
  (`fd_impact_mult_strictMonoOn_rho`, `fd_impact_mult_antitone_psi`, `fd_lam_mono_psi`); the
  whole-horizon multiplier as the limit of the cumulative ones and rising in `ρ` where
  cumulative spending rises (`fd_mult_tendsto`, `fd_multInf_strictMono`).
* **Structural estimation** (§8.7): (8.19)–(8.20) (`eq_8_19_8_20`, `sl_bijection`); the likelihood
  for discrete shocks and the Jacobian for densities (`sl_likelihood_discrete`, `sl_jacobian`,
  `sl_jacobian_depends_on_psi`); the implied multiplier (`sl_multiplier_mle`); the Kalman
  likelihood of (8.21)–(8.22) (`kl_innovations`, `kl_chain_rule`, `kl_likelihood`, `fn_9`).
* **Calibration** (§8.8): `β` (`fm_beta_calibration`), the Frisch elasticity (`fm_frisch`),
  `dℓ/dc` and the lottery formula (`fm_dl_dc`, `fm_lottery`), `γ = Ḡ/c̄` (`fm_gamma_calibration`),
  scale invariance (`fm_multiplier_scale`), the multiplier falling in `ψ`
  (`sm_multiplier_antitone_psi`).

All names are in the namespace `AKMM.QuantitativeMethods`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [StaticModel](AKMMQuantitativeMethods/StaticModel.lean) | 26 | (8.1)–(8.3), the planner, the multiplier, (8.5)–(8.6), Appendix 8.A.2 (AKMM §8.2, §8.4, pp. 218–223, 842) |
| [Identification](AKMMQuantitativeMethods/Identification.lean) | 8 | (8.8)–(8.9), endogeneity, least squares, instruments, the identifying restriction (AKMM §8.2–8.4, pp. 219–224) |
| [SVAR](AKMMQuantitativeMethods/SVAR.lean) | 12 | (8.4), (8.7), `Var(u)`, rotations, the restriction count (AKMM §8.4, pp. 222–223) |
| [Cholesky](AKMMQuantitativeMethods/Cholesky.lean) | 8 | The Cholesky factor, recursive identification, footnote 6's weights (AKMM §8.4–8.5, pp. 224, 227) |
| [VARLP](AKMMQuantitativeMethods/VARLP.lean) | 15 | Dynamic multipliers, VAR and companion IRFs, LP and VAR estimands, footnote 6 (AKMM pp. 220–221, §8.5, pp. 225–227) |
| [FiscalModel](AKMMQuantitativeMethods/FiscalModel.lean) | 21 | (8.10)–(8.18), the equilibrium, the steady state, §8.6.2, calibration (AKMM §8.6, §8.8, pp. 229–236, 842) |
| [FiscalDynamics](AKMMQuantitativeMethods/FiscalDynamics.lean) | 35 | The linearised model, its saddle path, the signs and multipliers of Figure 8.4 (AKMM §8.6, §8.8–8.9, pp. 231–238) |
| [StaticLikelihood](AKMMQuantitativeMethods/StaticLikelihood.lean) | 7 | (8.19)–(8.20), the likelihood and its Jacobian, the implied multiplier (AKMM §8.7, p. 232) |
| [KalmanLikelihood](AKMMQuantitativeMethods/KalmanLikelihood.lean) | 6 | (8.21)–(8.22), innovations, the prediction-error decomposition, footnote 9 (AKMM §8.7, pp. 232–233) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
