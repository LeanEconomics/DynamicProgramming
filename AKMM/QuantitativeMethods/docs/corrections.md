# Corrections and departures: AKMM Chapter 8

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 8, Empirical strategies and quantitative macroeconomics, pp. 217–238, and
Appendix 8.A, p. 842. Lean names are relative to `AKMM.QuantitativeMethods`. Every book item is
located in the [source map](source-map.md).

## Corrections

1. **Appendix 8.A.1, p. 842, the government rule.** The book's system for the steady state prints
   `Ḡ = (η̄c̄γ)^{−γ₁}`, with a stray exponent and an undefined `γ₁`. By (8.18) at `η̄ = 1` the rule
   is `Ḡ = γc̄`, as the main text itself uses (`γ = Ḡ/c̄`, p. 236). Proved: every steady state has
   `Ḡ = γc̄` (`appendix_8A_1`), the steady state exists with it (`fm_steady_exists`), and the
   printed rule agrees with `Ḡ = γc̄` for all `c̄ > 0` only if `γ₁ = −1`
   (`appendix_8A_1_printed_G`).

2. **Footnote 6, p. 227, the range of the weights.** "use these expected innovations in the other
   series as weights to combine the IRFs for `j = 1, ⋯, J`". The weights `L_{j1}/L₁₁` run over
   the `n` variables (reduced-form innovations), not over the `J` lags: `j = 1, ⋯, n` (`fn_6`,
   with `ch_first_column` for `Σ_{j1}/Σ₁₁ = L_{j1}/L₁₁`).

3. **§8.6.1, p. 229, the household budget.** `c_t + k_{t+1} = (1 + r_t − δ)K_t + w_tℓ_t − T_t`
   writes `K_t` for `k_t`. With `k_t`, the budget, `T = G` and zero profits give (8.11)
   (`fm_budget_resource`).

4. **§8.7, p. 232, the likelihood of the static model.** "The likelihood of these observations is
   then `Prob(G_t, Y_t | ψ, γ) = p_A(A_t) × p_η(η_t)`", where `p_A, p_η` are densities. The map
   `(y, G) ↦ (A, η)` of (8.19)–(8.20) is not measure preserving: the density of `(y, G)` is
   `p_A(A)p_η(η)|J|` with Jacobian determinant `J = (1 − s)^{1/(1+ψ)}/(γy(1 − s)²)`, `s = G/y`
   (`sl_jacobian`). `J` depends on `ψ` (`sl_jacobian_depends_on_psi`: `y = 1`, `G = 1/2`, `γ = 1`,
   `ψ = 1` versus `ψ = 3`), so the printed expression is not the likelihood of the data as a
   function of the parameters. The printed formula is exact for discretely distributed shocks
   (`sl_likelihood_discrete`). The measure-theoretic change-of-variables step is not formalised.

5. **§8.4, p. 224, box "Recursive identification" (imprecise).** "a Cholesky decomposition of the
   covariance matrix `Var(u_t)` gives `B₀⁻¹`" needs a sign normalisation: the triangular factor of
   `Var(u_t)` is unique only among lower-triangular matrices with positive diagonal (`ch_unique`).
   Without it, flipping the sign of any column gives another lower-triangular factor
   (`ch_sign_counterexample`). Proved: if `B₀⁻¹` is lower triangular with positive diagonal, the
   Cholesky factor of `Var(u_t)` is `B₀⁻¹` (`ch_recursive_identification`).

## Departures

6. **Conditional expectations as linear projections (§8.5, p. 226).** The book takes `{y_t}`
   Gaussian "so least squares equates with a conditional expectation". The local-projection and
   VAR estimands are proved as population least-squares (linear projection) coefficients in `L²`,
   using Miao's second-moment calculus (`vl_lp_estimand`, `vl_var_estimand`, `fn_6`); that they
   equal Gaussian conditional expectations is not formalised.

7. **The Kalman filter in second moments (§8.7, p. 233).** The statements `X_t ∼ N(X_{t|t−1},
   P_{t|t−1})` and that `Y_t` given the past is normal are not formalised; the innovation
   `Y_t − CX_{t|t−1}` is proved to have mean zero and covariance `CP_{t|t−1}C'`
   (`kl_innovations`, from Miao's filter), and the Gaussian likelihood formula is proved for the
   densities `N(Y_t | CX_{t|t−1}, CP_{t|t−1}C')` (`kl_likelihood`).

8. **Total differentials as local inverses (§8.2, p. 219; 8.A.2, p. 842).** The slope of the supply
   curve and `∂y/∂A` are strict derivatives of local inverses given by the inverse function
   theorem (`sm_supply_slope`, `sm_supply_dA`, `fm_fixed_investment_multiplier`), rather than
   formal total differentials of an implicit relation.

9. **The restriction count (footnote 4).** The count `n² − n(n+1)/2 = n(n−1)/2` is proved as a
   dimension count (`sv_finrank_symm`, `sv_restriction_count`, stated as `2·dim = n(n+1)` to avoid
   natural-number halving); like the book, it is a necessary count, not a sufficient condition.

10. **The Euler equation (8.14).** The book states (8.14) from Chapter 7 without derivation; it
    enters the equilibrium definition as stated (`fm_IsEquilibrium`), and the steady state is
    shown to be an equilibrium with zero shocks (`fm_steady_isEquilibrium`).

11. **§8.6.2, "the fiscal multiplier will be between zero and one".** Proved for the
    within-period equilibrium with capital and investment fixed and Cobb–Douglas production
    (`fm_fixed_investment_multiplier`), and in the static model of §8.2
    (`sm_multiplier_mem_Ioo`). "The multiplier is increasing in the persistence of the shock" and
    the claims of Figure 8.4 are treated in items 12–16 (module `FiscalDynamics`).

12. **§8.6.2 and p. 236, "invests less".** In the linearised model the impact response of
    investment is `Î₀ = k̄k̂₁ = −k̄φ` with `φD(ρ) = gλ(1 − (1+κ)ρ)`, `D(ρ) > 0`,
    `κ = βr̄(1−α)/(ψ+α)`. Investment falls on impact if and only if `ρ < 1/(1+κ)`; it is unchanged
    at `ρ = 1/(1+κ)` and rises for `1/(1+κ) < ρ ≤ 1`, a non-empty range that contains the permanent
    shock `ρ = 1` (`fd_investment_correction`). The book's statement holds for the persistence it
    uses (`ρ ≤ 0.95`, while `1/(1+κ)` is about 0.993 at `ψ = 2` and 0.980 at `ψ = 1/2`), but not for every persistence. With
    `ρ < 1/(1+κ)` the sign pattern of Figure 8.4 is proved for every parameter value
    (`fd_impact_signs`, `fd_c_k_neg`).

13. **"The fiscal multiplier is increasing in the persistence of the shock" (§8.6.2, p. 231;
    Fig. 8.4, right).** Proved analytically for two multipliers: the impact multiplier
    `Δy₀/ΔG₀`, strictly increasing on `0 ≤ ρ ≤ 1/(1+κ)` (`fd_impact_mult_strictMonoOn_rho`), and
    the whole-horizon cumulative multiplier `Σₜ Δyₜ/Σₜ ΔGₜ` (the limit of the `H`-period
    multipliers, `fd_mult_tendsto`), strictly increasing on `[ρ₁, 1/(1+κ)]` whenever cumulative
    spending rises at `ρ₁` (`fd_multInf_strictMono`). The extra hypothesis is needed: since
    `G = γηc` and consumption falls persistently, the cumulative spending response `Σₜ Ĝₜ` can be
    zero or negative for transitory shocks, and there the ratio has a pole; `Σₜ Ĝₜ > 0` at
    `ρ = 1/(1+κ)` (`fd_GInf_pos_top`). The 12-quarter multiplier plotted in the figure is not
    proved monotone for general parameters; that it rises over `ρ ∈ [0.8, 0.95]` at the
    calibration is a numerical statement.

14. **"If `ψ` is smaller … the fiscal multiplier is larger" (p. 237).** Proved for the impact
    multiplier under the extra assumption `δ ≤ 1` (`fd_impact_mult_antitone_psi`), which the book
    does not state (its calibration has `δ = 0.019`). The assumption gives that the stable root
    `λ` rises with `ψ` (`fd_lam_mono_psi`): the characteristic polynomial is a pencil
    `ψf₀ + αf₁` in `ψ` (`fd_pencil`) and `δ ≤ 1` makes `f₀ ≥ 0` up to the root of `f₁`
    (`fd_f0_nonneg`). The 12-quarter version is numerical.

15. **"The cumulative fiscal multiplier … is close to zero" (p. 236).** Its value is a calibrated
    number. What holds for every parameter value is that cumulative output rises by less than
    cumulative spending at every horizon, so the cumulative multiplier is below one whenever
    cumulative spending rises (`fd_cum_lt`, `fd_mult_lt_one`), and the impact multiplier is in
    `(0, 1)` (`fd_impact_mult_mem`).

16. **The linear approximation (§8.6.1, fn. 8).** The book computes the impulse responses with a
    numerical linear solution. Here the static equations (8.10), (8.15) with (8.17), and (8.18)
    are exactly log-linear (`fd_static_exact`), the resource constraint (8.11) and the Euler
    equation (8.14) with (8.16) are replaced by their derivatives at the steady state
    (`fd_resource_linear`, `fd_euler_linear`), the impulse response is the perfect-foresight path
    after the shock (`fd_IsIRF`), and its unique bounded solution is derived in closed form
    (`fd_irf_solves`, `fd_irf_unique`).
