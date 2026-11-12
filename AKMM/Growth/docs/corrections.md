# Corrections and departures: AKMM Chapter 13

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 13, Growth (T. Boppart and P. J. Klenow), pp. 369–404, and Appendix 13.A,
pp. 850–862. Lean names are relative to `AKMM.Growth`. Every book item is located in the
[source map](source-map.md).

## Corrections

1. **p. 378, footnote 11, boundedness.** "condition (13.8) ensures that utility is bounded". With
   the normalisation `(c^{1−σ} − 1)/(1 − σ)` of (13.4), the integrand along the balanced growth
   path is `(c̄^{1−σ}e^{(13.8)t} − e^{−(ρ−n)t})/(1 − σ)` (`istc_bgp_utility_eq`). Utility is
   finite when (13.8) holds and also `ρ > n` (`istc_bgp_utility_integrable`). For `σ < 1`
   (13.8) implies `ρ > n` (when `g_c ≥ 0`), but for `σ > 1` it does not: with `σ = 2`,
   `γ_x = 0`, `γ_y = 0.03`, `n = 0.02`, `ρ = 0.01`, (13.8) holds and the integrand tends to
   `+∞`, so it is not integrable (`istc_bgp_utility_unbounded`). The `−1` does not affect
   choices, so only the boundedness claim is affected.

2. **p. 380, the GDP deflator.** "a reasonable definition of the growth rate of the GDP deflator
   is `(Ṗ_x/P_x)^{s*}(Ṗ_c/P_c)^{1−s*} = −(1 − s*)γ_x`". The share-weighted (Divisia) deflator
   growth is the weighted *sum* `s*(Ṗ_x/P_x) + (1 − s*)(Ṗ_c/P_c) = −s*γ_x` (`istc_deflator`);
   read literally the product of powers is `0`, since `Ṗ_c = 0`. With `−s*γ_x`, real output
   grows at `g_c + n + s*γ_x`, which is also the Divisia quantity index
   `s*g_K + (1 − s*)(g_c + n)`, and real `K/Y` grows at `(1 − s*)γ_x`, the book's conclusion
   (`istc_real_KY_growth`). With the printed `−(1 − s*)γ_x` real `K/Y` would grow at `s*γ_x`;
   the two agree only if `γ_x = 0` or `s* = 1/2` (`istc_deflator_printed_false`).

3. **p. 385, footnote 24, the capital equation.** Printed: "`K̇(t)/K(t) = A − δ −
   e^{(n+(A−δ−ρ)/σ)t}c(0)`". The resource constraint gives
   `K̇/K = A − δ − e^{(n+g)t}c(0)/K(t)`; the printed equation fails on the closed-form path
   whenever `n + g ≠ 0` (`ak_footnote_24_printed_false`). The footnote's closed form and its
   conclusion are correct (`ak_footnote_24_general`, `ak_footnote_24_unique`).

4. **p. 391, footnote 34, the corner firm value.** Printed:
   "`V = π/r* = φA(A(1−φ)/ψ)^{1/φ−1}L`". With `r* = ρ` the value is
   `V = φA(A(1−φ)/ψ)^{1/φ−1}L/ρ`; the printed right side equals `π/r*` only if `ρ = 1`
   (`romer_footnote_34_printed_false`). Only with the `/ρ` does "`V > w/(ηN)` under (13.32)"
   follow: `V > w/(ηN)` iff `ρ < (1−φ)ηL` (`romer_footnote_34`).

5. **p. 392, the machine under-use factor.** "for given production labor `L_y` the
   decentralized machine quantity is too low by a factor of `(1−φ)^φ < 1`". The ratio is
   `x^{DE}/x^{SP} = (1−φ)^{1/φ}` (`romer_machine_ratio`); `(1−φ)^φ ≠ (1−φ)^{1/φ}` for
   `0 < φ < 1` (`romer_machine_ratio_printed_false`).

6. **p. 392, the machine subsidy.** "subsidizing machines by a rate `τ` that fulfills
   `1 − τ = (1−φ)^{−1}`". That makes `1 − τ > 1`, a tax: users then pay `ψ/(1−φ)²` and machine
   use falls below `x^{DE}`. The user price `(1−τ)ψ/(1−φ)` equals marginal cost, and the
   quantity equals `x^{SP}`, iff `1 − τ = 1 − φ`, i.e. `τ = φ` (`romer_subsidy`). With it,
   growth is `(ηL − ρ)/(1 + σ) < g^{SP}`, confirming the text's claim that the subsidy alone does
   not restore efficiency (`romer_subsidy_not_efficient`).

7. **p. 855, App. 13.A.7, the constancy argument.** "Condition (13.A.25) then implies that this
   can only be the case if `N^{ε−1}Le^{nt}` is constant." (13.A.25) alone does not: with `n > 0`,
   `N ≡ N_0` and `c = MN_0Le^{nt}`, (13.A.25) holds and `Ṅ/N`, `ċ/c` are constant while
   `N^{ε−1}Le^{nt}` is not (`jones_planner_A25_alone_insufficient`). Constancy of `λ̇/λ` through
   (13.A.24) together with (13.A.25) does force it, and then `Ṅ/N = n/(1−ε)`
   (`jones_planner_bgp`).

8. **p. 862, App. 13.A.10, the Hamiltonian.** Printed `H = e^{ρt}(C^{1−σ} − 1)/(1−σ) + …`. With
   `e^{ρt}` the first-order conditions give `Ċ/C = ((λ−1)ηφκ + ρ)/σ`, which is not (13.A.28)
   unless `ρ = 0` (`quality_planner_hamiltonian_sign`). With `e^{−ρt}` the planner's problem is
   the AK problem of `eq_13_A_28`, whose growth rate is (13.A.28).

9. **p. 862, App. 13.A.10, reason 2.** "SP use intermediates more intensively `(1−φ)^{1/φ} > 1`".
   For `0 < φ < 1`, `(1−φ)^{1/φ} < 1`; the ratio is `x^{SP}/x^{DE} = (1−φ)^{−1/φ} > 1`
   (`romer_machine_ratio`, `quality_planner_static`). The direction of the force is right.

10. **p. 852, App. 13.A.3, the half-life.** "A simple calibration with `n = 0.01`, `γ_x = 0.013`,
    `γ_y = 0.014`, `α = 1/3`, `σ = 1`, and `ρ = 0.03` yields a half-life of about 5.5 years." The
    half-life also depends on `δ`, which is not stated: the formula of `istc_stable_root` and
    `istc_half_life` gives 9.97 years at `δ = 0`, 5.45 at `δ = 0.05` and 3.75 at `δ = 0.10`
    (numerical check outside Lean; calibrated numbers are not formalised). The book's figure
    corresponds to `δ ≈ 0.05`.

## Departures

1. **Optimality is proved by sufficiency only.** Mathlib has no Pontryagin maximum principle.
   For the ISTC planner (`istc_optimal`, `istc_bgp_optimal`), the AK planner and household
   (`ak_optimal`, `ak_decentralized`) and the Romer planner (`romer_planner_optimal`) the
   book's first-order conditions plus the TVC are shown sufficient (catching-up optimality),
   using the Mangasarian–Arrow theorem of AKMM Chapter 9 (`AKMMContinuousTime`). Their
   necessity is not formalised. The ISTC planner is written in per-capita wealth
   `a = Ke^{−γ_x t}/(A_x e^{nt})` (`istc_capital_to_wealth`); the ISTC household's own problem
   with time-varying prices is not separately verified (the planner and equilibrium systems
   coincide, `istc_planner_euler`, `eq_13_A_7`).

2. **Transitional dynamics of the ISTC model.** Global convergence and optimality from any
   `k̃(0)` are proved for `σ = α` in closed form (`istc_closed_form_path`,
   `istc_closed_form_converges`, `istc_closed_form_optimal`); for general `σ` only the local
   saddle (App. 13.A.3) is formalised.

3. **Symmetric allocations in the variety and quality models.** The continuum of varieties is
   handled through the symmetric allocation: the per-variety problems are solved pointwise
   (`eq_13_24`, `eq_13_33`, `eq_13_A_16`) and integrals over `[0, N]` are written as `N` times
   the common value.

4. **Quality ladders: the aggregate quality index.** Instead of a continuum law of large
   numbers (Uhlig 1996), the aggregate `Q` is defined by its mean-field law `Q̇ = (λ−1)zQ`; for a
   single ladder with Poisson arrivals at rate `z`, the expected quality is shown to be
   `q_0e^{(λ−1)zt}`, which obeys that law (`quality_single_ladder`). The claim that the
   quality-ladder equilibrium is unique with no transition (p. 402) is not formalised.

5. **Equilibrium dynamics of the Romer model in ODE form.** The discount factor `e^{−∫r}` and
   the stock of varieties enter footnote 33 as solutions of `Ṁ = −rM`, `Ṅ = η(L − L_y)N`.

## Checked and not errors

* **p. 402, the quality-ladder TVC.** `lim_{T→∞} a(T)exp(∫_0^T −r(s)ds) = 0` is printed with
  the integral; it is the standard condition.
* **(13.16), (13.A.14)–(13.A.15), (13.66), (13.A.26)–(13.A.28), (13.50)–(13.51)** were re-derived
  and hold as printed (`eq_13_16`, `eq_13_A_14`, `eq_13_A_15`, `istc_stable_root`, `eq_13_66`,
  `eq_13_A_26`, `eq_13_A_27`, `eq_13_A_28`, `eq_13_50`, `eq_13_51`).
