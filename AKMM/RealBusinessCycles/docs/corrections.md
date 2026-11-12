# Corrections and departures: AKMM Chapter 14

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 14, Real business cycles (Kurt Mitman), pp. 405–438, and Appendix 14.A,
pp. 863–867. Lean names are relative to `AKMM.RealBusinessCycles`. Every book item is located in
the [source map](source-map.md).

## Corrections

1. **p. 412, the HP first-order condition.** Printed: for `2 ≤ t ≤ T − 2`,
   `τ_t − λ(Δτ_t − Δτ_{t−1} − 2(Δτ_{t+1} − Δτ_t) + Δτ_{t+2} − Δτ_{t+1}) = Y_t`. The bracket equals
   `τ_{t−2} − 4τ_{t−1} + 6τ_t − 4τ_{t+1} + τ_{t+2}` (`hp_bracket_eq`), the interior row of the
   printed `A`, so the condition is `τ_t + λ(…) = Y_t`, consistent with `(I + λA)τ = Y`
   (`hp_foc_interior`). At the trend the printed equation holds only where the bracket vanishes
   (`hp_foc_printed_iff`); counterexample `T = 5`, `λ = 1`, `Y = (I + A)e₂`
   (`hp_foc_printed_false`). The interior rows are `3 ≤ t ≤ T − 2` in the book's indexing; row
   `t = 2` is the boundary row `(−2, 5, −4, 1)` (`hp_A_row1`).

2. **p. 423, the Bellman equation.** Printed:
   `V(k, z) = max U(zF(k, ℓ) + (1 − δ)k − k′, 1 − ℓ) + E[V(k′, z′)∣z]`, without the discount factor,
   although (14.9) and (14.11) carry `β`. We formalise the discounted equation (`rbc_Bellman`);
   with the printed (undiscounted) equation the first-order condition is `U₁ = E[V₁]`, compatible
   with (14.9) only if `β = 1` or `U₁ = 0` (`rbc_printed_bellman_beta`). PDF page rendered.

3. **p. 424, the impulse-response sequence.** The third term is labelled `y₁` again; it is `y₂`
   (`irf_first_terms`).

4. **p. 427, the steady-state interest rate.** "the real interest rate is equal to the growth
   rate of consumption times σ divided by β". On a balanced growth path with gross consumption
   growth `g`, the Euler equation gives `R = g^σ/β` (`ext_bgp_interest`; Miao's `rb_u38_bgp` for
   `v = x^χ`), not `gσ/β`; counterexample `g = 1.02`, `σ = 2`, `β = 0.99`
   (`ext_interest_printed_false`).

5. **p. 412, footnote 5.** "the function `sin(2πtf)` is plotted … The first sine wave completes a
   full cycle at `t = 2π`". `sin(2πt)` completes a cycle at `t = 1`; Figure 14.A.1 (p. 863,
   rendered) plots `sin(ft)`, whose `f = 1` wave completes a cycle at `t = 2π`. No theorem
   (a statement about a figure).

6. **pp. 425 and 431, the share of output fluctuations.** TFP shocks explain "roughly 70%"
   (p. 425) and "nearly 80%" (p. 431) of output fluctuations. Internal inconsistency in
   quantitative claims; Table 14.4 gives `1.33/1.97 ≈ 0.68` in standard deviations. Not formalised
   (simulation results).

7. **p. 863, the proof of the inversion formula.** "For `j ≠ k`, `e^{−ikω}e^{ijω} = e^{iω(k−j)}`"
   has the exponent's sign reversed (it is `e^{iω(j−k)}`; the integrand of the display is
   `e^{−ijω}e^{ikω} = e^{iω(k−j)}`), and the integral is then rewritten as
   `e^{k−j}∫_{−π}^{π}(cos ω + i sin ω)dω`, which is wrong: it is
   `∫_{−π}^{π}(cos((k−j)ω) + i sin((k−j)ω))dω`, which vanishes because `k − j` is a nonzero integer
   (`appx_orth`). The proof also interchanges the infinite sum and the integral without comment;
   we justify it by dominated convergence for absolutely summable `γ` (`appx_inversion`). The
   result is correct. PDF page rendered.

8. **p. 864, the variance of a frequency band.** "`Var^{ω₂}_{ω₁}(Xₜ) = ∫_{ω₁}^{ω₂}f(ω)dω`": `f`
   is undefined (the spectrum `s` is meant), and since `Var = ∫_{−π}^{π}s`, the contribution of
   the frequencies `ω₁ ≤ |ω| ≤ ω₂` also includes the negative band; for symmetric autocovariances
   the spectrum is even and the band variance is `2∫_{ω₁}^{ω₂}s` (`appx_spec_even`,
   `appx_band_variance`).

9. **p. 865, the HP filter and λ.** "As λ gets large there is less smoothing". Backwards: the
   trend filter's gain `1/(1 + 4λ(1 − cos ω)²)` is strictly decreasing in `λ` at every
   `ω ∈ (0, π]` (`appx_hp_trend_gain_anti`), so a larger `λ` gives a smoother trend, as p. 411
   says. The rest of the sentence (the cyclical gain tends to `1`) is right
   (`appx_hp_gain_limit`).

10. **p. 433, Tobin's q.** "The quadratic formulation yields a shadow price of installed capital
   equal to `1 + ψ(iₜ/kₜ − δ)`". With the cost inside the accumulation equation,
   `∂kₜ₊₁/∂iₜ = 1 − ψ(i/k − δ)` (`adj_dk_di`), so the shadow price is
   `q = 1/(1 − ψ(i/k − δ))` (`adj_shadow_price`). The printed value agrees only at `i = δk`
   (`adj_q_printed_iff`; counterexample `ψ = 1`, `i/k − δ = 1/2`: `2 ≠ 3/2`,
   `adj_q_printed_false`); it is the first-order approximation, the error being
   `ψ²x²/(1 − ψx)` (`adj_q_first_order`), and it is exact if the cost is paid out of output
   (`adj_shadow_price_resource`).

11. **Minor misprints, no theorem.** p. 863, footnote 33: `d_x(ω) = Σₖxₜe^{−ikω}` mixes the
   indices (`Σₜxₜe^{−itω}`); p. 864: "`Y_c = C(L)`" omits `Y` (`Y_c = C(L)Y`); p. 863: the spectrum
   is "defined for each frequency ω in the interval `[0, π]`" but integrated over `[−π, π]`
   (`specC` is defined for all `ω`).

12. **pp. 412–413, the spectral representation.** "It is possible to represent any stationary
   process `Yₜ` as `Yₜ = ∫₀^π A(ω)cos(ωt)dω + ∫₀^π B(ω)sin(ωt)dω`, where for any `ω`, `A(ω)` and
   `B(ω)` are random variables". Imprecise, stated without proof. It holds for weakly
   (covariance-) stationary mean-zero processes with finite second moments, and the integrals are
   stochastic integrals against orthogonal-increment random measures `dU(ω)`, `dW(ω)`, not
   `dω`-integrals of random functions.
   Proved here in Hilbert-space form, a result beyond the text: the autocovariance is positive
   definite (`sden_posDef`); the Herglotz theorem gives a unique finite spectral measure `F`
   (`herg_herglotz`, `herg_unique`), with continuous density `(1/2π)Σγₕe^{−ihω} ≥ 0` when
   `Σ∣γₕ∣ < ∞` (`sden_density`); and the Kolmogorov isometry `V : L²(F) → H_X`, `e^{itω} ↦ Xₜ`, is
   onto the closed span of the process (`cramIso`, `cram_iso_exp`, `cram_iso_range`,
   `cram_iso_unique`), with `Z(A) = V(1_A)` of orthogonal increments, `⟪Z(A), Z(B)⟫ = F(A ∩ B)`
   (`cram_Z_inner`, `cram_Z_norm_sq`, `cram_Z_orth`, `cram_Z_union`, `cram_Z_univ`). For real
   processes `F` is symmetric (`herg_symm_of_real`) and folding `ω` onto `[0, π]` gives the book's
   real form with `A(ω)dω`, `B(ω)dω` read as `dU`, `dW` (a remark in the `Cramer` docstring; the
   stochastic-integral notation is not formalised).

## Departures

* **Finite-state TFP.** The core RBC Bellman equation (`rbc_Bellman`) and the BCA investment
  Euler equation use finitely many TFP states with transition probabilities in place of the
  AR(1) with normal shocks; the existence and differentiability of the value function are
  hypotheses (the book assumes them). Non-vacuity: `rbc_example_bellman`.
* **Welfare theorems.** The book asserts them for general `U`, `F`; they are imported from Miao
  (`rb_sce_iff`, `rb_sce_optimal`) for log utility and Cobb–Douglas technology, the calibrated
  case (`rbc_calib_utility`).
* **The HP limit `λ → ∞`** is made precise: the trend converges to the OLS linear trend
  (`hp_limit_ols`, `T ≥ 2`).
* **Constrained and Lagrangian HP forms**: we prove that the Lagrangian solution solves the
  constrained problem with `µ = ‖Dτ_λ‖²` and is its unique solution; the converse (every binding
  `µ` is attained by some `λ`) is not formalised.
* **Impulse responses** are in deviations from the steady state (`k_ss = 0`).
* **Linear filters** are finite in `appx_filter_autocov` and `appx_filtered_spectrum`; the
  HP and ideal band-pass filters are infinite, and for them only the gain functions and the
  band-pass coefficients are formalised.
* **Government spending** is analysed in the static log–log economy of §14.4.1 (labour supply
  response); the CES aggregate's two limits are represented by perfect substitutes
  (`ext_gov_perfect_subst`) and by `g` outside utility (`ext_gov_hours`).
* **Investment wedge**: backed out one period at a time with a successor wedge constant across
  next period's states (`bca_investment_wedge`); with several states other choices exist.
* **Spectral theory (beyond the text).** Processes take values in a complex Hilbert space `H`
  (for instance mean-zero `L²(Ω, ℂ)`) and autocovariances are complex (`γ(h) = ⟪Xₜ, Xₜ₊ₕ⟫`);
  the frequency domain is the circle `AddCircle T` with `T > 0` and characters
  `e^{2πihx/T}` (`T = 2π` gives `e^{ihω}` on `(−π, π]`). The limit of the Fejér measures is
  taken by Riesz–Markov–Kakutani (the Fejér functionals converge on all of `C(𝕋)`), not by
  Prokhorov.
