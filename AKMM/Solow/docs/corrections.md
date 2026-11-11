# Corrections and departures: AKMM Chapter 3

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 3, The Solow model, pp. 71–92, and Appendix 3.A, pp. 825–826. Lean names
are relative to `AKMM.Solow`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 88, §3.4.3, doubling the saving rate.** The book: with the calibrated parameters,
   `s = 0.1` gives `k̃̄ = 1.20`, `f(k̃̄) = 1.06`, and `s = 0.2` gives `k̃̄ = 1.90`, `f(k̃̄) = 1.24`, so
   "doubling the saving rate from 10% to 20% increases the normalized level of output by 17%".
   With (3.8) as printed (exponent `1/(1 − α)`), balanced-growth output is
   `f(k̃̄) = (s/((1 + γ)(1 + n) + δ − 1))^{α/(1−α)}`, so raising `s₁` to `s₂` multiplies it by
   `(s₂/s₁)^{α/(1−α)}` whatever `δ, γ, n` (`solow_saving_output_ratio`). At `α = 1/3` doubling `s`
   multiplies output by `√2 > 1.41`: a 41% increase, and `√2 ≠ 1.24/1.06`
   (`solow_p88_doubling_saving`). The correct values are `k̃̄ ≈ 1.50`, `f ≈ 1.15` and
   `k̃̄ ≈ 4.25`, `f ≈ 1.62`; the printed numbers are reproduced by the exponent `1 − α` in place of
   `1/(1 − α)`.

2. **p. 92, the output impulse response.** The book prints
   `ŷ_t = Â_t + αk̂_t = ρ^t δε + αρ^{t−1}(…)δε = ρ^t(1 + (α/ρ)(…))δε`. But `Â_t = ρ^t ε`, not
   `ρ^t δε`. The correct response is `ŷ₀ = ε` and, for `t ≥ 1`,
   `ŷ_t = ρ^t ε (1 + (αδ/ρ)(1 − q^t)/(1 − q))`, `q = (1 − λ)/ρ` (`solow_irf_output`, from the
   closed form `solow_irf_capital_closed_form`). The printed formula is false whenever `δ ≠ 1`,
   `ρ ≠ 0`, `ε ≠ 0`: at `t = 1` the true value is `ρε + αδε` and the printed one `ρδε + αδε`
   (`solow_irf_output_printed_false`).

3. **p. 825, Theorem .1 (Uzawa, Part I).** The statement says "the variable `A_t` grows at a
   constant rate `(1 + γ)(1 + n) − 1`". The proof (correctly) gives `A_t = ((1 + γ)/(1 + n))^t`
   (`theorem_3A_1`), whose growth rate is `(1 + γ)/(1 + n) − 1` (`uzawa_technology_growth`); in the
   appendix `γ` is the growth rate of output, not of technology. The factor is unique when `F̃₀` is
   increasing in labour (`uzawa_technology_unique`). Counterexample to the printed rate: with
   `γ = 0`, `n = 1`, `F̃_t(K, L) = K + (1/2)^t L` satisfies the hypotheses of Theorem .1, but
   `F̃₁(K, L) ≠ F̃₀(K, 2L)` (`uzawa_printed_rate_counterexample`).

4. **p. 826, proof of Theorem .2.** "From (3.A.2), `1 + γ_K = I_t/K_t − δ`". From
   `K_{t+1}/K_t = 1 + I_t/K_t − δ` the identity is `γ_K = I_t/K_t − δ` (`uzawa_capital_growth`, which
   also shows `K_t ≠ 0`). The conclusion of the theorem is unaffected (`uzawa_investment_growth`,
   `theorem_3A_2`).

5. **p. 826, Theorem .2, an implicit hypothesis.** The last step ("`γ_I = γ_C` implies
   `γ_I = γ_C = γ_Y`") divides by output. With constant growth stated multiplicatively,
   `X_{t+1} = (1 + γ_X)X_t`, the theorem fails when `Y ≡ 0`: `Y_t = 0`, `C_t = −(3/2)2^t`,
   `I_t = (3/2)2^t`, `K_t = 2^t`, `δ = 1/2`, `γ_Y = 0`, `γ_C = γ_I = γ_K = 1` satisfy (3.A.2),
   (3.A.3), constant growth and `I_t > 0`, but `γ_Y ≠ γ_K`
   (`uzawa_part2_zero_output_counterexample`). We assume `Y₀ ≠ 0` (`theorem_3A_2`), which the
   book's ratio definition of `γ_Y` presupposes. With nonnegative consumption (the
   Jones–Scrimgeour setting) no assumption on output is needed
   (`uzawa_part2_nonneg_consumption`).

6. **p. 74, cross-reference.** "the aggregate production function `f(k_t)` has decreasing returns
   to capital (Assumption 2 above)". Assumption 2 (strict quasiconcavity) alone does not give
   diminishing returns: `F(K, L) = K²L²` is strictly increasing, strictly quasiconcave on the
   positive orthant and has `F(0, L) = 0`, yet `f(k) = k²` is not concave
   (`solow_assumption2_alone_counterexample`). Assumptions 2 and 3 together (with 1 and 4) do give
   strict concavity of `f` (`solow_intensive_strictConcave`).

7. **p. 72, Assumptions 1 and 4.** Assumption 1 asks `F` to be strictly increasing in both
   arguments, which contradicts `F(0, L) = 0` (Assumption 4) at `K = 0`
   (`solow_assumption1_conflicts_assumption4`). `SolowAssumptions` asks for strict monotonicity in
   `L` at `K > 0` and in `K` on `[0, ∞)`, which is what the chapter uses.

## Departures (formalisation choices)

8. **Smoothness (footnote 1, p. 72).** The book assumes `F` twice continuously differentiable.
   `SolowAssumptions` asks only what the chapter uses: `K ↦ F(K, L)` continuous on `[0, ∞)` and
   `C¹` on `(0, ∞)`. Strict concavity of `f` is derived (`solow_intensive_strictConcave`), not
   assumed; `f' > 0` is derived from strict concavity and monotonicity
   (`solow_intensive_deriv_pos`). The result is EconomicGrowth's `Technology` (`solow_technology`),
   whose dynamics are then imported.

9. **Weak boundary conditions (p. 73).** "`lim_{k→0} F₁(k, 1) > δ/s` and `lim_{k→∞} F₁(k, 1) <
   δ/s`" are stated as `f' > δ/s` eventually near `0` and `f' < δ/s` eventually at infinity, which
   the limit conditions imply (the limits may be infinite). Existence and uniqueness need only
   continuity, `f(0) = 0` and strict concavity (`solow_steady_existsUnique_weak`); the global
   monotone convergence under these conditions adds that `f` is increasing
   (`solow_global_convergence_weak`).

10. **Growing economy (§3.2).** The detrended results assume `γ, n ≥ 0` (with `0 < δ < 1`), which
    makes `(1 + γ)(1 + n) − 1 + δ > 0` (`solow_params_growth`); the book leaves this implicit.

11. **Statements made for Cobb–Douglas but true in general.** The comparative statics of `k̄` and
    `ȳ` in `s` and `δ` (p. 74) and `k̄/ȳ = s/δ` (p. 75) are proved for every `F` satisfying
    Assumptions 1–6 (`solow_steady_strictMono_saving`, `solow_steady_strictAnti_depreciation`,
    `solow_capital_output_ratio`); Cobb–Douglas is an instance (`solow_cobbDouglas_assumptions`).

12. **Endogenous growth (p. 75).** "`F₁(k, 1)` uniformly above `δ/s`" is proved in two readings:
    pointwise (no positive steady state, capital strictly increasing,
    `solow_endogenous_no_steady_state`) and uniform, `f' ≥ c > δ/s` (geometric growth and
    divergence, `solow_endogenous_growth`).

13. **Poverty traps (p. 77).** "At least one of the steady states will then not be stable" is
    proved for two adjacent steady states of a continuous increasing map
    (`solow_poverty_trap_unstable`, with local attraction `SolowLocallyAttracting`). The claim that
    a sufficient rise in saving removes `k̄₁, k̄₂` is qualitative and not formalised; given a single
    crossing, global convergence is `solow_global_convergence_weak`.

14. **Linearisations.** (3.10), (3.12) and (3.18) are first-order approximations in the book; they
    are formalised as exact derivatives of the maps at the steady state (`eq_3_10`, `eq_3_12`,
    `eq_3_18`, `solow_level_linearisation`), and the impulse response is the exact solution of the
    linear recursion (3.18) (`solow_irf_capital_sum`, `solow_irf_capital_closed_form`). The
    closed form needs `ρ ≠ 0` and `ρ ≠ 1 − λ`, which the book leaves implicit.

15. **Uzawa Part I.** `F̃_t` is defined on the positive orthant as in the book, and `1 + γ > 0`,
    `1 + n > 0` are assumed. Part I needs only constant returns of `F̃₀`, not of every `F̃_t`.
